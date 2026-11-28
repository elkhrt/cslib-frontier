/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Foundations.Data.Matrix.RowTable
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Polynomial-Time Gauss–Jordan Linear Algebra over Finite Fields

Executable reduced row echelon form (`finElim`), row-space basis extraction (`finRowBasis`),
right-kernel basis extraction (`finKernelBasis`), and consistent linear-system solving (`finSolve`)
for `Cslib.RowTable F` over any finite field `F`, together with multi-tape Turing machine
`ComputableInPolyTime` certificates and complete algebraic specifications.

## Main definitions

* `Cslib.LinearAlgebra.FinRowTableCodec.enc`, `Cslib.LinearAlgebra.encFinTable`:
  structured `enc_structure` binary codec for `Cslib.RowTable F`.
* `Cslib.LinearAlgebra.finElim`: single-pass Gauss–Jordan sweep returning `(pivotCol, row)`
  pairs in reduced row echelon form.
* `Cslib.LinearAlgebra.finRowBasis`, `Cslib.LinearAlgebra.finKernelBasis`,
  `Cslib.LinearAlgebra.finSolve`: row-space basis, kernel basis, and `A x = b` solver.

## Main results

* `Cslib.LinearAlgebra.computableInPolyTime_finElim`,
  `Cslib.LinearAlgebra.computableInPolyTime_finRowBasis`,
  `Cslib.LinearAlgebra.computableInPolyTime_finKernelBasis`,
  `Cslib.LinearAlgebra.computableInPolyTime_finSolve`.
* `Cslib.LinearAlgebra.finElim_spec`, `Cslib.LinearAlgebra.finRowBasis_spec`,
  `Cslib.LinearAlgebra.finKernelBasis_spec`, `Cslib.LinearAlgebra.finSolve_spec`.
-/

public section

namespace Cslib.LinearAlgebra

open Cslib Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped BigOperators Matrix

/-! ### Structured Binary Encodings for `Cslib.RowTable F` -/

namespace FinRowTableCodec

/-- Binary encoding of a `Cslib.RowTable F` with unary dimension headers and framed row lists. -/
enc_structure enc (F : Type) (encF : F ↪ List Bool) : Cslib.RowTable F where
  numRows : encUnary,
  numCols : encUnary,
  rows : (encList (encList encF))

end FinRowTableCodec

open scoped FinRowTableCodec

/-- Canonical `Cslib.RowTable F` encoding over a finite type `F`. -/
noncomputable abbrev encFinTable (F : Type) [Finite F] : Cslib.RowTable F ↪ List Bool :=
  FinRowTableCodec.enc F (encFinite F)

/-- Convert a coordinate list `v : List F` into a vector `Fin n → F` (padding with `0`). -/
@[expose] def listToVec {F : Type*} [Zero F] (n : ℕ) (v : List F) : Fin n → F :=
  fun c => v.getD c.val 0

@[simp]
theorem listToVec_apply {F : Type*} [Zero F] (n : ℕ) (v : List F) (c : Fin n) :
    listToVec n v c = v.getD c.val 0 := rfl

/-! ### Executable Gauss–Jordan Sweep on `Cslib.RowTable F` -/

/-- Normalize `T : RowTable F` to `T.numRows` rows of exact length `T.numCols`. -/
@[expose] def normFinRows {F : Type*} [Zero F] (T : RowTable F) : List (List F) :=
  (List.range T.numRows).map fun i => (List.range T.numCols).map fun j => T.entry i j

/-- One column step of Gauss–Jordan elimination on `(pivots, todo)` of width `n`. -/
@[expose] def finElimStep {F : Type*} [DivisionRing F] [DecidableEq F]
    (n : ℕ) (s : List (ℕ × List F) × List (List F)) (j : ℕ) :
    List (ℕ × List F) × List (List F) :=
  match s.2.find? (fun w => decide (w.getD j 0 ≠ 0)) with
  | none => s
  | some v =>
    let inv := (v.getD j 0)⁻¹
    let p := (List.range n).map fun c => inv * v.getD c 0
    (s.1.map (fun q =>
        (q.1, (List.range n).map fun c => q.2.getD c 0 - q.2.getD j 0 * p.getD c 0)) ++ [(j, p)],
     s.2.map (fun w =>
        (List.range n).map fun c => w.getD c 0 - w.getD j 0 * p.getD c 0))

/-- Full Gauss–Jordan sweep returning `(pivotCol, reducedRow)` pairs in increasing column order. -/
@[expose] def finElim {F : Type*} [DivisionRing F] [DecidableEq F]
    (T : RowTable F) : List (ℕ × List F) :=
  ((List.range T.numCols).foldl (finElimStep T.numCols) ([], normFinRows T)).1

/-- Row-space basis extracted from `finElim T`. -/
@[expose] def finRowBasis {F : Type*} [DivisionRing F] [DecidableEq F]
    (T : RowTable F) : List (List F) :=
  (finElim T).map Prod.snd

/-- Build the `j`-th kernel basis vector from reduced `(pivotCol, row)` pairs. -/
@[expose] def buildFinKerVec {F : Type*} [Ring F]
    (n : ℕ) (pivs : List (ℕ × List F)) (j : ℕ) : List F :=
  (List.range n).map fun c =>
    if c == j then 1
    else match pivs.find? (fun q => q.1 == c) with
      | some q => -q.2.getD j 0
      | none => 0

/-- Right-kernel basis of `T.toMatrix.mulVecLin` over a division ring / field `F`. -/
@[expose] def finKernelBasis {F : Type*} [DivisionRing F] [DecidableEq F]
    (T : RowTable F) : List (List F) :=
  let pivs := finElim T
  let pivCols := pivs.map Prod.fst
  let freeCols := (List.range T.numCols).filter fun j => !pivCols.contains j
  freeCols.map (buildFinKerVec T.numCols pivs)

/-- Augmented table `[T | rhs]` of dimensions `T.numRows × (T.numCols + 1)`. -/
@[expose] def augmentFinTable {F : Type*} [Zero F] (T : RowTable F) (rhs : List F) : RowTable F :=
  ⟨T.numRows, T.numCols + 1,
    (List.range T.numRows).map fun i =>
      ((List.range T.numCols).map fun j => T.entry i j) ++ [rhs.getD i 0]⟩

/-- Solve `T.toMatrix *ᵥ x = rhs` via augmented Gauss–Jordan elimination. -/
@[expose] def finSolve {F : Type*} [DivisionRing F] [DecidableEq F]
    (T : RowTable F) (rhs : List F) : Option (List F) :=
  let pivs := finElim (augmentFinTable T rhs)
  if (pivs.map Prod.fst).contains T.numCols then
    none
  else
    some <| (List.range T.numCols).map fun c =>
      match pivs.find? (fun q => q.1 == c) with
      | some q => q.2.getD T.numCols 0
      | none => 0

/-! ### Algebraic Correctness of `finElim`, `finRowBasis`, `finKernelBasis`, and `finSolve` -/

section Correctness

private theorem getD_map_range_lt {α : Type*} (n : ℕ) (f : ℕ → α) (d : α) (c : ℕ) (hc : c < n) :
    ((List.range n).map f).getD c d = f c := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hc]

private theorem find?_pivs_eq_some {F : Type*} {pivs : List (ℕ × List F)}
    (hnodup : (pivs.map Prod.fst).Nodup) {a : Fin pivs.length} :
    pivs.find? (fun q => q.1 == pivs[a.val].1) = some pivs[a.val] := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, a.val, a.isLt, rfl, fun j hj => ?_⟩
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]
  intro heq
  have h1 : (pivs.map Prod.fst)[j]'(by simpa using hj.trans a.isLt) =
      (pivs.map Prod.fst)[a.val]'(by simp) := by
    simpa using heq
  exact hj.ne (hnodup.getElem_inj_iff.mp h1)

private theorem find?_pivs_eq_none {F : Type*} {pivs : List (ℕ × List F)} {c : ℕ}
    (hc : c ∉ pivs.map Prod.fst) :
    pivs.find? (fun q => q.1 == c) = none := by
  rw [List.find?_eq_none]
  intro q hq
  simp only [beq_iff_eq]
  rintro rfl
  exact hc (List.mem_map.mpr ⟨q, hq, rfl⟩)

variable {F : Type*} [Field F]

private structure FinSweepInv (T : RowTable F) (k : ℕ)
    (s : List (ℕ × List F) × List (List F)) : Prop where
  piv_len : s.1.length ≤ k
  piv_lt : ∀ q ∈ s.1, q.1 < k ∧ q.2.length = T.numCols
  todo_len : s.2.length = T.numRows
  todo_width : ∀ w ∈ s.2, w.length = T.numCols
  piv_pairwise : (s.1.map Prod.fst).Pairwise (· < ·)
  piv_self : ∀ q ∈ s.1, q.2.getD q.1 0 = 1
  piv_left_zero : ∀ q ∈ s.1, ∀ c < q.1, q.2.getD c 0 = 0
  piv_other_zero : ∀ q ∈ s.1, ∀ q' ∈ s.1, q'.1 ≠ q.1 → q.2.getD q'.1 0 = 0
  todo_zero : ∀ w ∈ s.2, ∀ c < k, w.getD c 0 = 0
  row_span : Submodule.span F
      ({u : Fin T.numCols → F | u ∈ s.1.map (listToVec T.numCols ∘ Prod.snd)} ∪
       {u : Fin T.numCols → F | u ∈ s.2.map (listToVec T.numCols)}) =
    Submodule.span F (Set.range T.toMatrix)

private theorem finSweepInv_init (T : RowTable F) :
    FinSweepInv T 0 ([], normFinRows T) where
  piv_len := le_rfl
  piv_lt := by simp
  todo_len := by simp [normFinRows]
  todo_width := by
    intro w hw
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
    simp
  piv_pairwise := List.Pairwise.nil
  piv_self := by simp
  piv_left_zero := by simp
  piv_other_zero := by simp
  todo_zero := by intro _ _ c hc; omega
  row_span := by
    have hset : ({u : Fin T.numCols → F | u ∈ ([] : List (ℕ × List F)).map
          (listToVec T.numCols ∘ Prod.snd)} ∪
        {u : Fin T.numCols → F | u ∈ (normFinRows T).map (listToVec T.numCols)}) =
        Set.range T.toMatrix := by
      ext u
      simp only [List.map_nil, List.not_mem_nil, Set.ofPred_false, Set.empty_union,
        Set.mem_ofPred_eq, List.mem_map, normFinRows, List.mem_range]
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        refine ⟨⟨i, hi⟩, ?_⟩
        ext c
        simp [listToVec]
      · rintro ⟨i, rfl⟩
        refine ⟨(List.range T.numCols).map fun j => T.entry i.val j, ⟨i.val, i.isLt, rfl⟩, ?_⟩
        ext c
        simp [listToVec]
    rw [hset]

variable [DecidableEq F]

private theorem finSweepInv_step {T : RowTable F} {j : ℕ} (hj : j < T.numCols)
    {s : List (ℕ × List F) × List (List F)} (hinv : FinSweepInv T j s) :
    FinSweepInv T (j + 1) (finElimStep T.numCols s j) := by
  dsimp only [finElimStep]
  cases hfind : s.2.find? (fun w => decide (w.getD j 0 ≠ 0)) with
  | none =>
    have hall_zero : ∀ w ∈ s.2, w.getD j 0 = 0 := by
      intro w hw
      have hnone := List.find?_eq_none.mp hfind w hw
      simpa using hnone
    exact
      { piv_len := hinv.piv_len.trans (Nat.le_succ j)
        piv_lt := fun q hq => ⟨(hinv.piv_lt q hq).1.trans (Nat.lt_succ_self j),
          (hinv.piv_lt q hq).2⟩
        todo_len := hinv.todo_len
        todo_width := hinv.todo_width
        piv_pairwise := hinv.piv_pairwise
        piv_self := hinv.piv_self
        piv_left_zero := hinv.piv_left_zero
        piv_other_zero := hinv.piv_other_zero
        todo_zero := fun w hw c hc => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | rfl
          · exact hinv.todo_zero w hw c hlt
          · exact hall_zero w hw
        row_span := hinv.row_span }
  | some v =>
    dsimp only
    have hv_mem : v ∈ s.2 := List.mem_of_find?_eq_some hfind
    have hvj_ne : v.getD j 0 ≠ 0 := by
      simpa using List.find?_some hfind
    let inv := (v.getD j 0)⁻¹
    let p : List F := (List.range T.numCols).map fun c => inv * v.getD c 0
    have hp_len : p.length = T.numCols := by simp [p]
    have hp_get : ∀ c < T.numCols, p.getD c 0 = inv * v.getD c 0 :=
      fun c hc => getD_map_range_lt T.numCols _ 0 c hc
    have hp_j : p.getD j 0 = 1 := by
      rw [hp_get j hj]
      exact inv_mul_cancel₀ hvj_ne
    have hp_lt : ∀ c < j, p.getD c 0 = 0 := fun c hc => by
      rw [hp_get c (hc.trans hj), hinv.todo_zero v hv_mem c hc, mul_zero]
    let updRow (r : List F) : List F :=
      (List.range T.numCols).map fun c => r.getD c 0 - r.getD j 0 * p.getD c 0
    have hupd_get : ∀ (r : List F) (c : ℕ), c < T.numCols →
        (updRow r).getD c 0 = r.getD c 0 - r.getD j 0 * p.getD c 0 :=
      fun r c hc => getD_map_range_lt T.numCols _ 0 c hc
    have hupd_vec : ∀ r : List F,
        listToVec T.numCols (updRow r) =
          listToVec T.numCols r - (r.getD j 0) • listToVec T.numCols p := fun r => by
      ext c
      simp only [listToVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hupd_get r c.val c.isLt]
    have hp_vec : listToVec T.numCols p = inv • listToVec T.numCols v := by
      ext c
      simp only [listToVec_apply, Pi.smul_apply, smul_eq_mul, hp_get c.val c.isLt]
    refine
      { piv_len := by
          simp only [List.length_append, List.length_map, List.length_singleton]
          exact Nat.succ_le_succ hinv.piv_len
        piv_lt := ?_
        todo_len := by simp [hinv.todo_len]
        todo_width := ?_
        piv_pairwise := ?_
        piv_self := ?_
        piv_left_zero := ?_
        piv_other_zero := ?_
        todo_zero := ?_
        row_span := ?_ }
    · intro q hq
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q₀, hq₀, rfl⟩ | rfl
      · exact ⟨(hinv.piv_lt q₀ hq₀).1.trans (Nat.lt_succ_self j), by simp⟩
      · exact ⟨Nat.lt_succ_self j, hp_len⟩
    · intro w' hw'
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hw'
      simp
    · have hmap_fst : ((s.1.map (fun q => (q.1, updRow q.2)) ++ [(j, p)]).map Prod.fst) =
          s.1.map Prod.fst ++ [j] := by
        simp [List.map_append, List.map_map, Function.comp_def]
      rw [hmap_fst, List.pairwise_append]
      refine ⟨hinv.piv_pairwise, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_singleton.mp hb]
      exact (hinv.piv_lt q₀ hq₀).1
    · intro q hq
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q₀, hq₀, rfl⟩ | rfl
      · have hq₀_lt := (hinv.piv_lt q₀ hq₀).1
        rw [hupd_get q₀.2 q₀.1 (hq₀_lt.trans hj), hp_lt q₀.1 hq₀_lt, mul_zero, sub_zero]
        exact hinv.piv_self q₀ hq₀
      · exact hp_j
    · intro q hq c hc
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q₀, hq₀, rfl⟩ | rfl
      · have hq₀_lt := (hinv.piv_lt q₀ hq₀).1
        rw [hupd_get q₀.2 c ((hc.trans hq₀_lt).trans hj),
          hinv.piv_left_zero q₀ hq₀ c hc, hp_lt c (hc.trans hq₀_lt), mul_zero, sub_zero]
      · exact hp_lt c hc
    · intro q hq q' hq' hne
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq hq'
      rcases hq with ⟨q₀, hq₀, rfl⟩ | rfl <;> rcases hq' with ⟨q₁, hq₁, rfl⟩ | rfl
      · have hq₁_lt := (hinv.piv_lt q₁ hq₁).1
        rw [hupd_get q₀.2 q₁.1 (hq₁_lt.trans hj), hinv.piv_other_zero q₀ hq₀ q₁ hq₁ hne,
          hp_lt q₁.1 hq₁_lt, mul_zero, sub_zero]
      · rw [hupd_get q₀.2 j hj, hp_j, mul_one, sub_self]
      · exact hp_lt q₁.1 (hinv.piv_lt q₁ hq₁).1
      · exact absurd rfl hne
    · intro w' hw' c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | hc_eq
      · rw [hupd_get w c (hlt.trans hj), hinv.todo_zero w hw c hlt, hp_lt c hlt, mul_zero, sub_zero]
      · rw [hc_eq, hupd_get w j hj, hp_j, mul_one, sub_self]
    · rw [← hinv.row_span]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro u (hu | hu)
        · simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append, List.mem_map,
            Function.comp_apply, List.map_singleton, List.mem_singleton] at hu
          rcases hu with ⟨_, ⟨q₀, hq₀, rfl⟩, rfl⟩ | rfl
          · change listToVec T.numCols (updRow q₀.2) ∈ _
            rw [hupd_vec, hp_vec]
            refine sub_mem (Submodule.subset_span (Or.inl ?_))
              (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ?_))))
            · exact List.mem_map.mpr ⟨q₀, hq₀, rfl⟩
            · exact List.mem_map.mpr ⟨v, hv_mem, rfl⟩
          · rw [hp_vec]
            exact Submodule.smul_mem _ _ (Submodule.subset_span
              (Or.inr (List.mem_map.mpr ⟨v, hv_mem, rfl⟩)))
        · simp only [Set.mem_ofPred_eq, List.mem_map] at hu
          obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hu
          rw [hupd_vec, hp_vec]
          refine sub_mem (Submodule.subset_span (Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩)))
            (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
              (Submodule.subset_span (Or.inr (List.mem_map.mpr ⟨v, hv_mem, rfl⟩)))))
      · rw [Submodule.span_le]
        let S_new : Set (Fin T.numCols → F) :=
          {u | u ∈ ((s.1.map (fun q => (q.1, updRow q.2)) ++ [(j, p)]).map
              (listToVec T.numCols ∘ Prod.snd))} ∪
            {u | u ∈ (s.2.map updRow).map (listToVec T.numCols)}
        have hp_in : listToVec T.numCols p ∈ Submodule.span F S_new := by
          refine Submodule.subset_span (Or.inl ?_)
          simp
        rintro u (hu | hu)
        · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hu
          have hmem : listToVec T.numCols (updRow q₀.2) ∈ Submodule.span F S_new := by
            refine Submodule.subset_span (Or.inl ?_)
            simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append, List.mem_map,
              Function.comp_apply]
            exact Or.inl ⟨_, ⟨q₀, hq₀, rfl⟩, rfl⟩
          have heq : listToVec T.numCols q₀.2 =
              listToVec T.numCols (updRow q₀.2) + (q₀.2.getD j 0) • listToVec T.numCols p := by
            rw [hupd_vec, sub_add_cancel]
          change listToVec T.numCols q₀.2 ∈ Submodule.span F S_new
          rw [heq]
          exact add_mem hmem (Submodule.smul_mem _ _ hp_in)
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
          have hmem : listToVec T.numCols (updRow w) ∈ Submodule.span F S_new := by
            refine Submodule.subset_span (Or.inr ?_)
            simp only [Set.mem_ofPred_eq, List.mem_map]
            exact ⟨updRow w, ⟨w, hw, rfl⟩, rfl⟩
          have heq : listToVec T.numCols w =
              listToVec T.numCols (updRow w) + (w.getD j 0) • listToVec T.numCols p := by
            rw [hupd_vec, sub_add_cancel]
          change listToVec T.numCols w ∈ Submodule.span F S_new
          rw [heq]
          exact add_mem hmem (Submodule.smul_mem _ _ hp_in)

private theorem finSweepInv_take (T : RowTable F) :
    ∀ k ≤ T.numCols,
      FinSweepInv T k
        (((List.range T.numCols).take k).foldl (finElimStep T.numCols) ([], normFinRows T))
  | 0, _ => by simpa using finSweepInv_init T
  | k + 1, hk => by
    have hk_lt : k < (List.range T.numCols).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hk_lt, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.getElem_range]
    exact finSweepInv_step (by omega) (finSweepInv_take T k (Nat.le_of_succ_le hk))

/-- Complete RREF and row-space specification of `finElim T`. -/
theorem finElim_spec (T : RowTable F) :
    let pivs := finElim T
    pivs.length ≤ T.numCols ∧
    (∀ q ∈ pivs, q.1 < T.numCols ∧ q.2.length = T.numCols) ∧
    (pivs.map Prod.fst).Pairwise (· < ·) ∧
    (∀ q ∈ pivs, q.2.getD q.1 0 = 1) ∧
    (∀ q ∈ pivs, ∀ c < q.1, q.2.getD c 0 = 0) ∧
    (∀ q ∈ pivs, ∀ q' ∈ pivs, q'.1 ≠ q.1 → q.2.getD q'.1 0 = 0) ∧
    Submodule.span F (Set.range fun a : Fin pivs.length => listToVec T.numCols pivs[a.val].2) =
      Submodule.span F (Set.range T.toMatrix) := by
  intro pivs
  have hfull : ((List.range T.numCols).take T.numCols) = List.range T.numCols := by simp
  have hinv := finSweepInv_take T T.numCols le_rfl
  rw [hfull] at hinv
  refine ⟨hinv.piv_len, hinv.piv_lt, hinv.piv_pairwise, hinv.piv_self, hinv.piv_left_zero,
    hinv.piv_other_zero, ?_⟩
  rw [← hinv.row_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span (Or.inl ?_)
    exact List.mem_map.mpr ⟨pivs[a.val], List.getElem_mem a.isLt, rfl⟩
  · rw [Submodule.span_le]
    rintro u (hu | hu)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
      have hw0 : listToVec T.numCols w = 0 := by
        ext c
        exact hinv.todo_zero w hw c.val c.isLt
      rw [hw0]
      exact zero_mem _

/-- Complete row-space basis specification of `finRowBasis T`. -/
theorem finRowBasis_spec (T : RowTable F) :
    let B := finRowBasis T
    B.length ≤ T.numCols ∧
    (∀ r ∈ B, r.length = T.numCols) ∧
    LinearIndependent F (fun a : Fin B.length => listToVec T.numCols B[a.val]) ∧
    Submodule.span F (Set.range fun a : Fin B.length => listToVec T.numCols B[a.val]) =
      Submodule.span F (Set.range T.toMatrix) := by
  intro B
  obtain ⟨hlen, hlt, hpair, hself, _, hother, hspan⟩ := finElim_spec T
  have hB_len : B.length = (finElim T).length := List.length_map _
  have hnodup : ((finElim T).map Prod.fst).Nodup := hpair.imp Nat.ne_of_lt
  refine ⟨hB_len ▸ hlen, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact (hlt q hq).2
  · rw [Fintype.linearIndependent_iff]
    intro g hg a
    have ha_lt : a.val < (finElim T).length := hB_len ▸ a.isLt
    let col : Fin T.numCols := ⟨(finElim T)[a.val].1, (hlt _ (List.getElem_mem ha_lt)).1⟩
    have heval := congrFun hg col
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
    rw [Finset.sum_eq_single a] at heval
    · have hget : B[a.val] = (finElim T)[a.val].2 := List.getElem_map _
      simp only [listToVec, hget, col, hself _ (List.getElem_mem ha_lt), mul_one] at heval
      exact heval
    · intro b _ hba
      have hb_lt : b.val < (finElim T).length := hB_len ▸ b.isLt
      have hget : B[b.val] = (finElim T)[b.val].2 := List.getElem_map _
      have hcol_ne : (finElim T)[a.val].1 ≠ (finElim T)[b.val].1 := by
        intro heq
        have h1 : ((finElim T).map Prod.fst)[a.val]'(by simpa using ha_lt) =
            ((finElim T).map Prod.fst)[b.val]'(by simpa using hb_lt) := by
          simpa using heq
        exact hba (Fin.ext ((hnodup.getElem_inj_iff.mp h1).symm))
      simp only [listToVec, hget, col,
        hother _ (List.getElem_mem hb_lt) _ (List.getElem_mem ha_lt) hcol_ne, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ a) hnot
  · rw [← hspan]
    congr 1
    ext u
    simp only [Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      have ha : a.val < (finElim T).length := hB_len ▸ a.isLt
      exact ⟨⟨a.val, ha⟩, congrArg (listToVec T.numCols) (List.getElem_map _).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, hB_len.symm ▸ a.isLt⟩, congrArg (listToVec T.numCols) (List.getElem_map _)⟩

private theorem mulVec_eq_zero_iff_pivs (T : RowTable F) (v : Fin T.numCols → F) :
    T.toMatrix *ᵥ v = 0 ↔
      ∀ a : Fin (finElim T).length,
        dotProduct (listToVec T.numCols (finElim T)[a.val].2) v = 0 := by
  obtain ⟨_, _, _, _, _, _, hspan⟩ := finElim_spec T
  let dotZero : Submodule F (Fin T.numCols → F) :=
    { carrier := {r | dotProduct r v = 0}
      add_mem' := fun {x y} hx hy => by
        change dotProduct x v = 0 at hx
        change dotProduct y v = 0 at hy
        change dotProduct (x + y) v = 0
        rw [add_dotProduct, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        change dotProduct x v = 0 at hx
        change dotProduct (c • x) v = 0
        rw [smul_dotProduct, hx, smul_eq_mul, mul_zero] }
  have h1 : (∀ i : Fin T.numRows, dotProduct (T.toMatrix i) v = 0) ↔
      Submodule.span F (Set.range T.toMatrix) ≤ dotZero := by
    rw [Submodule.span_le]
    exact ⟨by rintro h _ ⟨i, rfl⟩; exact h i, fun h i => h (Set.mem_range_self i)⟩
  have h2 : (∀ a : Fin (finElim T).length,
        dotProduct (listToVec T.numCols (finElim T)[a.val].2) v = 0) ↔
      Submodule.span F (Set.range fun a : Fin (finElim T).length =>
        listToVec T.numCols (finElim T)[a.val].2) ≤ dotZero := by
    rw [Submodule.span_le]
    exact ⟨by rintro h _ ⟨a, rfl⟩; exact h a, fun h a => h (Set.mem_range_self a)⟩
  have hm : T.toMatrix *ᵥ v = 0 ↔ ∀ i : Fin T.numRows, dotProduct (T.toMatrix i) v = 0 := by
    simp only [funext_iff, Matrix.mulVec, Pi.zero_apply]
  rw [hm, h1, ← hspan, ← h2]

/-- Complete right-kernel basis specification of `finKernelBasis T`. -/
theorem finKernelBasis_spec (T : RowTable F) :
    let K := finKernelBasis T
    K.length ≤ T.numCols ∧
    (∀ v ∈ K, v.length = T.numCols) ∧
    LinearIndependent F (fun idx : Fin K.length => listToVec T.numCols K[idx.val]) ∧
    Submodule.span F (Set.range fun idx : Fin K.length => listToVec T.numCols K[idx.val]) =
      LinearMap.ker T.toMatrix.mulVecLin := by
  intro K
  set pivs := finElim T
  set pivCols := pivs.map Prod.fst
  set freeCols := (List.range T.numCols).filter fun j => !pivCols.contains j
  obtain ⟨_, hlt, hpair, hself, _, hother, _⟩ := finElim_spec T
  have hnodup_piv : pivCols.Nodup := hpair.imp Nat.ne_of_lt
  have hnodup_free : freeCols.Nodup := List.nodup_range.filter _
  have hmem_free : ∀ c : ℕ, c ∈ freeCols ↔ c < T.numCols ∧ c ∉ pivCols := by
    intro c
    simp [freeCols]
  have hfree_len : freeCols.length ≤ T.numCols :=
    (List.filter_sublist.length_le).trans_eq List.length_range
  have hK_len : K.length = freeCols.length := List.length_map _
  have hkerVec_free : ∀ {j c : ℕ}, j < T.numCols → c < T.numCols → c ∉ pivCols →
      (buildFinKerVec T.numCols pivs j).getD c 0 = if c = j then 1 else 0 := by
    intro j c _ hc hnot
    rw [buildFinKerVec, getD_map_range_lt T.numCols _ 0 c hc, find?_pivs_eq_none hnot]
    by_cases hcj : c = j <;> simp [hcj]
  have hkerVec_piv : ∀ {j : ℕ} (hj_not : j ∉ pivCols) (a : Fin pivs.length),
      (buildFinKerVec T.numCols pivs j).getD pivs[a.val].1 0 = -pivs[a.val].2.getD j 0 := by
    intro j hj_not a
    have hca : pivs[a.val].1 < T.numCols := (hlt _ (List.getElem_mem a.isLt)).1
    have hne : pivs[a.val].1 ≠ j := fun heq =>
      hj_not (heq ▸ List.mem_map.mpr ⟨pivs[a.val], List.getElem_mem a.isLt, rfl⟩)
    rw [buildFinKerVec, getD_map_range_lt T.numCols _ 0 pivs[a.val].1 hca, beq_false_of_ne hne,
      ite_eq_right Bool.false_ne_true, find?_pivs_eq_some hnodup_piv]
  have hkerVec_mem_ker : ∀ j ∈ freeCols,
      T.toMatrix *ᵥ listToVec T.numCols (buildFinKerVec T.numCols pivs j) = 0 := by
    intro j hj_mem
    obtain ⟨hj_lt, hj_not⟩ := (hmem_free j).mp hj_mem
    rw [mulVec_eq_zero_iff_pivs]
    intro a
    let c_a : Fin T.numCols := ⟨pivs[a.val].1, (hlt _ (List.getElem_mem a.isLt)).1⟩
    let j_f : Fin T.numCols := ⟨j, hj_lt⟩
    have hc_ne_j : c_a ≠ j_f := by
      intro h
      have hv : pivs[a.val].1 = j := congrArg Fin.val h
      exact hj_not (hv ▸ List.mem_map.mpr ⟨pivs[a.val], List.getElem_mem a.isLt, rfl⟩)
    dsimp only [dotProduct]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c_a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hc_ne_j.symm, Finset.mem_univ j_f⟩)]
    have ht1 : listToVec T.numCols pivs[a.val].2 c_a *
        listToVec T.numCols (buildFinKerVec T.numCols pivs j) c_a = -pivs[a.val].2.getD j 0 := by
      change pivs[a.val].2.getD pivs[a.val].1 0 *
        (buildFinKerVec T.numCols pivs j).getD pivs[a.val].1 0 = -pivs[a.val].2.getD j 0
      rw [hself pivs[a.val] (List.getElem_mem a.isLt), hkerVec_piv hj_not a, one_mul]
    have ht2 : listToVec T.numCols pivs[a.val].2 j_f *
        listToVec T.numCols (buildFinKerVec T.numCols pivs j) j_f = pivs[a.val].2.getD j 0 := by
      change pivs[a.val].2.getD j 0 *
        (buildFinKerVec T.numCols pivs j).getD j 0 = pivs[a.val].2.getD j 0
      rw [hkerVec_free hj_lt hj_lt hj_not, ite_eq_left rfl, mul_one]
    have ht_rest : ∑ c ∈ (Finset.univ.erase c_a).erase j_f,
        listToVec T.numCols pivs[a.val].2 c *
          listToVec T.numCols (buildFinKerVec T.numCols pivs j) c = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hcj : c ≠ j_f := (Finset.mem_erase.mp hc).1
      have hca : c ≠ c_a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
      by_cases hc_piv : c.val ∈ pivCols
      · obtain ⟨q', hq', hq'_eq⟩ := List.mem_map.mp hc_piv
        have hne_col : q'.1 ≠ pivs[a.val].1 := by
          rw [hq'_eq]
          exact fun h => hca (Fin.ext h)
        have h0 : pivs[a.val].2.getD c.val 0 = 0 := by
          rw [← hq'_eq]
          exact hother _ (List.getElem_mem a.isLt) q' hq' hne_col
        rw [listToVec_apply, h0, zero_mul]
      · have h0 : (buildFinKerVec T.numCols pivs j).getD c.val 0 = 0 := by
          rw [hkerVec_free hj_lt c.isLt hc_piv, ite_eq_right (fun h => hcj (Fin.ext h))]
        rw [listToVec_apply, listToVec_apply, h0, mul_zero]
    rw [ht1, ht2, ht_rest, add_zero, neg_add_cancel]
  refine ⟨hK_len ▸ hfree_len, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    simp [buildFinKerVec]
  · rw [Fintype.linearIndependent_iff]
    intro g hg idx
    have hi_lt : idx.val < freeCols.length := hK_len ▸ idx.isLt
    have hj_mem : freeCols[idx.val] ∈ freeCols := List.getElem_mem hi_lt
    obtain ⟨hj_lt, hj_not⟩ := (hmem_free _).mp hj_mem
    let col : Fin T.numCols := ⟨freeCols[idx.val], hj_lt⟩
    have heval := congrFun hg col
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
    rw [Finset.sum_eq_single idx] at heval
    · have hget : K[idx.val] = buildFinKerVec T.numCols pivs freeCols[idx.val] :=
        List.getElem_map _
      simp only [listToVec_apply, hget, col, hkerVec_free hj_lt hj_lt hj_not, ↓reduceIte,
        mul_one] at heval
      exact heval
    · intro b _ hb
      have hb_lt : b.val < freeCols.length := hK_len ▸ b.isLt
      obtain ⟨hb_col_lt, _⟩ := (hmem_free _).mp (List.getElem_mem hb_lt)
      have hget : K[b.val] = buildFinKerVec T.numCols pivs freeCols[b.val] := List.getElem_map _
      have hne_col : freeCols[idx.val] ≠ freeCols[b.val] := fun heq =>
        hb (Fin.ext ((hnodup_free.getElem_inj_iff.mp heq).symm))
      simp only [listToVec_apply, hget, col, hkerVec_free hb_col_lt hj_lt hj_not,
        ite_eq_right hne_col, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ idx) hnot
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨idx, rfl⟩
      have hi_lt : idx.val < freeCols.length := hK_len ▸ idx.isLt
      have hget : K[idx.val] = buildFinKerVec T.numCols pivs freeCols[idx.val] :=
        List.getElem_map _
      change T.toMatrix *ᵥ listToVec T.numCols K[idx.val] = 0
      rw [hget]
      exact hkerVec_mem_ker _ (List.getElem_mem hi_lt)
    · intro x hx
      change T.toMatrix *ᵥ x = 0 at hx
      let w : Fin T.numCols → F :=
        ∑ idx : Fin K.length, x ⟨freeCols[idx.val]'(hK_len ▸ idx.isLt),
          ((hmem_free _).mp (List.getElem_mem (hK_len ▸ idx.isLt))).1⟩ •
          listToVec T.numCols K[idx.val]
      have hw_mem : w ∈ Submodule.span F
          (Set.range fun idx : Fin K.length => listToVec T.numCols K[idx.val]) :=
        Submodule.sum_mem _ fun idx _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨idx, rfl⟩)
      suffices hxw : x = w by exact hxw ▸ hw_mem
      have hw_ker : T.toMatrix *ᵥ w = 0 := by
        have hle : Submodule.span F
            (Set.range fun idx : Fin K.length => listToVec T.numCols K[idx.val]) ≤
            LinearMap.ker T.toMatrix.mulVecLin := by
          rw [Submodule.span_le]
          rintro _ ⟨idx, rfl⟩
          have hi_lt : idx.val < freeCols.length := hK_len ▸ idx.isLt
          change T.toMatrix *ᵥ listToVec T.numCols K[idx.val] = 0
          rw [show K[idx.val] = buildFinKerVec T.numCols pivs freeCols[idx.val] from
            List.getElem_map _]
          exact hkerVec_mem_ker _ (List.getElem_mem hi_lt)
        exact hle hw_mem
      have hdiff_ker : T.toMatrix *ᵥ (x - w) = 0 := by
        rw [Matrix.mulVec_sub, hx, hw_ker, sub_self]
      have hdiff_free : ∀ c : Fin T.numCols, c.val ∉ pivCols → (x - w) c = 0 := by
        intro c hc_not
        have hc_mem : c.val ∈ freeCols := (hmem_free c.val).mpr ⟨c.isLt, hc_not⟩
        obtain ⟨i₀, hi₀, hi₀_eq⟩ := List.mem_iff_getElem.mp hc_mem
        let idx₀ : Fin K.length := ⟨i₀, hK_len.symm ▸ hi₀⟩
        have hw_c : w c = x c := by
          simp only [w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_eq_single idx₀]
          · have hget : K[idx₀.val] = buildFinKerVec T.numCols pivs freeCols[i₀] :=
              List.getElem_map _
            have h1 : (buildFinKerVec T.numCols pivs freeCols[i₀]).getD c.val 0 = 1 := by
              rw [hkerVec_free ((hmem_free _).mp (List.getElem_mem hi₀)).1 c.isLt hc_not,
                ite_eq_left hi₀_eq.symm]
            have hxc : x ⟨freeCols[i₀], ((hmem_free _).mp (List.getElem_mem hi₀)).1⟩ = x c := by
              congr 1; exact Fin.ext hi₀_eq
            simp only [listToVec_apply, hget, h1, mul_one, idx₀, hxc]
          · intro b _ hb
            have hb_lt : b.val < freeCols.length := hK_len ▸ b.isLt
            have hget : K[b.val] = buildFinKerVec T.numCols pivs freeCols[b.val] :=
              List.getElem_map _
            have hne : c.val ≠ freeCols[b.val] := by
              rw [← hi₀_eq]
              exact fun heq => hb (Fin.ext ((hnodup_free.getElem_inj_iff.mp heq).symm))
            simp only [listToVec_apply, hget,
              hkerVec_free ((hmem_free _).mp (List.getElem_mem hb_lt)).1 c.isLt hc_not,
              ite_eq_right hne, mul_zero]
          · intro hnot; exact absurd (Finset.mem_univ idx₀) hnot
        simp [hw_c]
      have hdiff_piv := (mulVec_eq_zero_iff_pivs T (x - w)).mp hdiff_ker
      ext c
      by_cases hc_piv : c.val ∈ pivCols
      · obtain ⟨q, hq, hq_eq⟩ := List.mem_map.mp hc_piv
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
        have hdot := hdiff_piv ⟨i, hi⟩
        dsimp only [dotProduct] at hdot
        have hc_eq : (⟨pivs[i].1, (hlt _ (List.getElem_mem hi)).1⟩ : Fin T.numCols) = c :=
          Fin.ext hq_eq
        rw [Finset.sum_eq_single c] at hdot
        · rw [← hc_eq, listToVec_apply, hself pivs[i] (List.getElem_mem hi), one_mul, hc_eq]
            at hdot
          exact sub_eq_zero.mp hdot
        · intro b _ hbc
          by_cases hb_piv : b.val ∈ pivCols
          · obtain ⟨q', hq', hq'_eq⟩ := List.mem_map.mp hb_piv
            have hne : q'.1 ≠ pivs[i].1 := by
              rw [hq'_eq, hq_eq]
              exact Fin.val_ne_of_ne hbc
            have h0 : pivs[i].2.getD b.val 0 = 0 := by
              rw [← hq'_eq]
              exact hother _ (List.getElem_mem hi) q' hq' hne
            rw [listToVec_apply, h0, zero_mul]
          · rw [hdiff_free b hb_piv, mul_zero]
        · intro hnot; exact absurd (Finset.mem_univ c) hnot
      · exact sub_eq_zero.mp (hdiff_free c hc_piv)

/-- Soundness and completeness of `finSolve T rhs` with respect to `T.toMatrix *ᵥ x = rhs`. -/
theorem finSolve_spec (T : RowTable F) (rhs : List F) :
    let b : Fin T.numRows → F := fun i => rhs.getD i.val 0
    (∀ x, finSolve T rhs = some x →
      x.length = T.numCols ∧ T.toMatrix *ᵥ listToVec T.numCols x = b) ∧
    (finSolve T rhs = none ↔ ¬ ∃ x : Fin T.numCols → F, T.toMatrix *ᵥ x = b) := by
  intro b
  set aug := augmentFinTable T rhs
  set pivs := finElim aug
  obtain ⟨_, hlt, hpair, hself, _, hother, _⟩ := finElim_spec aug
  have hnodup : (pivs.map Prod.fst).Nodup := hpair.imp Nat.ne_of_lt
  have haug_entry : ∀ (i : Fin T.numRows) (j : Fin (T.numCols + 1)),
      aug.toMatrix i j =
        if hj : j.val < T.numCols then T.toMatrix i ⟨j.val, hj⟩ else b i := by
    intro i j
    simp only [RowTable.toMatrix_apply, RowTable.entry, aug, augmentFinTable]
    rw [getD_map_range_lt T.numRows _ [] i.val i.isLt]
    have hlen : ((List.range T.numCols).map fun c => T.entry i.val c).length = T.numCols := by
      simp
    by_cases hj : j.val < T.numCols
    · rw [dite_eq_left hj, List.getD_append _ _ _ _ (hlen.symm ▸ hj),
        getD_map_range_lt T.numCols _ 0 j.val hj]
    · have hjeq : j.val = T.numCols := by have := j.isLt; omega
      rw [dite_eq_right hj, hjeq, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp), List.length_map, List.length_range, Nat.sub_self]
      rfl
  have hext_orth : ∀ x : Fin T.numCols → F,
      (∀ i : Fin T.numRows,
          dotProduct (aug.toMatrix i) (Fin.snoc (α := fun _ => F) x (-1)) = 0) ↔
        T.toMatrix *ᵥ x = b := by
    intro x
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    change (∑ j : Fin (T.numCols + 1),
        aug.toMatrix i j * Fin.snoc (α := fun _ => F) x (-1) j = 0) ↔
      (∑ c : Fin T.numCols, T.toMatrix i c * x c = b i)
    rw [Fin.sum_univ_castSucc]
    have hsum : (∑ c : Fin T.numCols,
        aug.toMatrix i c.castSucc * Fin.snoc (α := fun _ => F) x (-1) c.castSucc) =
        ∑ c : Fin T.numCols, T.toMatrix i c * x c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [haug_entry, c.isLt]
    have hlast : aug.toMatrix i (Fin.last T.numCols) *
        Fin.snoc (α := fun _ => F) x (-1) (Fin.last T.numCols) = -b i := by
      simp [haug_entry]
    rw [hsum, hlast, ← sub_eq_add_neg, sub_eq_zero]
  by_cases hcont : (pivs.map Prod.fst).contains T.numCols = true
  · have hmem_last : T.numCols ∈ pivs.map Prod.fst := List.contains_iff_mem.mp hcont
    obtain ⟨q_last, hq_last, hq_col⟩ := List.mem_map.mp hmem_last
    obtain ⟨i_last, hi_last, rfl⟩ := List.mem_iff_getElem.mp hq_last
    have hnone : finSolve T rhs = none := by
      dsimp only [finSolve]; rw [ite_eq_left hcont]
    refine ⟨fun _ h => (by rw [hnone] at h; cases h), ⟨fun _ => ?_, fun _ => hnone⟩⟩
    rintro ⟨x, hx⟩
    let xExt : Fin aug.numCols → F := Fin.snoc (α := fun _ => F) x (-1)
    have hpiv_orth := (mulVec_eq_zero_iff_pivs aug xExt).mp (by
      ext i
      exact (hext_orth x).mpr hx i) ⟨i_last, hi_last⟩
    dsimp only [dotProduct] at hpiv_orth
    change (∑ j : Fin (T.numCols + 1),
      listToVec (T.numCols + 1) pivs[i_last].2 j * xExt j) = 0 at hpiv_orth
    rw [Fin.sum_univ_castSucc] at hpiv_orth
    have hzero_left : (∑ c : Fin T.numCols,
        listToVec (T.numCols + 1) pivs[i_last].2 c.castSucc * xExt c.castSucc) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      have hc_lt : c.val < pivs[i_last].1 := by rw [hq_col]; exact c.isLt
      have h0 := (finElim_spec aug).2.2.2.2.1 _ (List.getElem_mem hi_last) c.val hc_lt
      rw [listToVec_apply, Fin.val_castSucc, h0, zero_mul]
    have hlast_one : listToVec (T.numCols + 1) pivs[i_last].2 (Fin.last T.numCols) *
        xExt (Fin.last T.numCols) = -1 := by
      have h1 : pivs[i_last].2.getD T.numCols 0 = 1 := by
        rw [← hq_col]
        exact hself _ (List.getElem_mem hi_last)
      rw [listToVec_apply, Fin.val_last, h1, one_mul]
      simp [xExt]
    rw [hzero_left, zero_add, hlast_one] at hpiv_orth
    exact one_ne_zero (neg_eq_zero.mp hpiv_orth)
  · have hnot_mem : T.numCols ∉ pivs.map Prod.fst :=
      mt List.contains_iff_mem.mpr hcont
    let xList : List F := (List.range T.numCols).map fun c =>
      match pivs.find? (fun q => q.1 == c) with
      | some q => q.2.getD T.numCols 0
      | none => 0
    have hsome : finSolve T rhs = some xList := by
      dsimp only [finSolve]; rw [ite_eq_right hcont]
    have hx_sol : T.toMatrix *ᵥ listToVec T.numCols xList = b := by
      rw [← hext_orth]
      let xExt : Fin aug.numCols → F :=
        Fin.snoc (α := fun _ => F) (listToVec T.numCols xList) (-1)
      have hmul0 : aug.toMatrix *ᵥ xExt = 0 := by
        rw [mulVec_eq_zero_iff_pivs aug xExt]
        intro a
        have ha_lt_n : pivs[a.val].1 < T.numCols := by
          have ha1 := (hlt _ (List.getElem_mem a.isLt)).1
          have ha_ne : pivs[a.val].1 ≠ T.numCols := fun heq =>
            hnot_mem (heq ▸ List.mem_map.mpr ⟨pivs[a.val], List.getElem_mem a.isLt, rfl⟩)
          change pivs[a.val].1 < T.numCols + 1 at ha1
          omega
        dsimp only [dotProduct]
        change (∑ j : Fin (T.numCols + 1),
          listToVec (T.numCols + 1) pivs[a.val].2 j * xExt j) = 0
        rw [Fin.sum_univ_castSucc]
        let c_a : Fin T.numCols := ⟨pivs[a.val].1, ha_lt_n⟩
        rw [Finset.sum_eq_single c_a]
        · have hxa : listToVec T.numCols xList c_a = pivs[a.val].2.getD T.numCols 0 := by
            rw [listToVec_apply]
            change xList.getD pivs[a.val].1 0 = pivs[a.val].2.getD T.numCols 0
            rw [getD_map_range_lt T.numCols _ 0 pivs[a.val].1 ha_lt_n, find?_pivs_eq_some hnodup]
          have h1 : listToVec (T.numCols + 1) pivs[a.val].2 c_a.castSucc = 1 :=
            hself pivs[a.val] (List.getElem_mem a.isLt)
          have hlast : listToVec (T.numCols + 1) pivs[a.val].2 (Fin.last T.numCols) *
              xExt (Fin.last T.numCols) = -pivs[a.val].2.getD T.numCols 0 := by
            rw [listToVec_apply, Fin.val_last]
            simp [xExt]
          simp only [xExt, Fin.snoc_castSucc, h1, one_mul, hxa]
          rw [hlast, add_neg_cancel]
        · intro c _ hca
          by_cases hc_piv : c.val ∈ pivs.map Prod.fst
          · obtain ⟨q', hq', hq'_eq⟩ := List.mem_map.mp hc_piv
            have hne : q'.1 ≠ pivs[a.val].1 := by
              rw [hq'_eq]
              exact Fin.val_ne_of_ne hca
            have h0 : pivs[a.val].2.getD c.val 0 = 0 := by
              rw [← hq'_eq]
              exact hother _ (List.getElem_mem a.isLt) q' hq' hne
            rw [listToVec_apply, Fin.val_castSucc, h0, zero_mul]
          · have h0 : listToVec T.numCols xList c = 0 := by
              rw [listToVec_apply, getD_map_range_lt T.numCols _ 0 c.val c.isLt,
                find?_pivs_eq_none hc_piv]
            simp only [xExt, Fin.snoc_castSucc, h0, mul_zero]
        · intro hnot; exact absurd (Finset.mem_univ c_a) hnot
      exact fun i => congrFun hmul0 i
    refine ⟨fun x hx => ?_, ⟨fun h => (by rw [hsome] at h; cases h), fun hno =>
      False.elim (hno ⟨listToVec T.numCols xList, hx_sol⟩)⟩⟩
    rw [hsome, Option.some.injEq] at hx
    subst hx
    exact ⟨by simp [xList], hx_sol⟩

end Correctness

/-! ### Polynomial-Time Computability over Finite Fields -/

section PolyTime

private theorem length_encFinite_le (F : Type) [Finite F] :
    ∃ C : ℕ, ∀ x : F, (encFinite F x).length ≤ C := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  by_cases hne : (Finset.univ : Finset F).Nonempty
  · let lengths : Finset ℕ := (Finset.univ : Finset F).image (fun x => (encFinite F x).length)
    refine ⟨lengths.max' (hne.image (fun x => (encFinite F x).length)), fun x => ?_⟩
    exact Finset.le_max' lengths _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  · exact ⟨0, fun x => False.elim (hne ⟨x, Finset.mem_univ x⟩)⟩

variable (F : Type) [Field F] [Finite F] [DecidableEq F]

private noncomputable abbrev encSweepState : (List (ℕ × List F) × List (List F)) ↪ List Bool :=
  encPair (encList (encPair encUnary (encList (encFinite F))))
    (encList (encList (encFinite F)))

omit [DecidableEq F] in
private theorem poly_elimPivotRow :
    ComputableInPolyTime
      (fun u : (ℕ × ℕ) × List F =>
        let inv := (u.2.getD u.1.2 0)⁻¹
        (List.range u.1.1).map fun c => inv * u.2.getD c 0)
      (encPair (encPair encUnary encUnary) (encList (encFinite F)))
      (encList (encFinite F)) := by
  have hmul : ComputableInPolyTime (fun p : F × F => p.1 * p.2)
      (encPair (encFinite F) (encFinite F)) (encFinite F) := of_finite _
  have hinv : ComputableInPolyTime (fun x : F => x⁻¹) (encFinite F) (encFinite F) := of_finite _
  have hget : ComputableInPolyTime (fun q : List F × ℕ => q.1.getD q.2 0)
      (encPair (encList (encFinite F)) encUnary) (encFinite F) := by fun_prop
  let EU := encPair (encPair encUnary encUnary) (encList (encFinite F))
  have hn : ComputableInPolyTime (fun u : (ℕ × ℕ) × List F => u.1.1) EU encUnary := by fun_prop
  have hinv_u : ComputableInPolyTime (fun u : (ℕ × ℕ) × List F => (u.2.getD u.1.2 0)⁻¹)
      EU (encFinite F) := by
    have hvj : ComputableInPolyTime (fun u : (ℕ × ℕ) × List F => u.2.getD u.1.2 0)
        EU (encFinite F) := by fun_prop
    exact hinv.comp hvj
  refine mapWithInput (ComputableInPolyTime.range.comp hn) ?_
  let EC := encPair EU encUnary
  have h1 : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List F) × ℕ => (x.1.2.getD x.1.1.2 0)⁻¹)
      EC (encFinite F) := hinv_u.comp (fst EU encUnary)
  have h2 : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List F) × ℕ => x.1.2.getD x.2 0)
      EC (encFinite F) := by
    dsimp only [EC, EU]
    fun_prop
  exact hmul.comp (h1.prod h2)

omit [DecidableEq F] in
private theorem poly_elimUpdateRow :
    ComputableInPolyTime
      (fun u : (ℕ × ℕ) × (List F × List F) =>
        (List.range u.1.1).map fun c => u.2.2.getD c 0 - u.2.2.getD u.1.2 0 * u.2.1.getD c 0)
      (encPair (encPair encUnary encUnary)
        (encPair (encList (encFinite F)) (encList (encFinite F))))
      (encList (encFinite F)) := by
  have hmul : ComputableInPolyTime (fun p : F × F => p.1 * p.2)
      (encPair (encFinite F) (encFinite F)) (encFinite F) := of_finite _
  have hsub : ComputableInPolyTime (fun p : F × F => p.1 - p.2)
      (encPair (encFinite F) (encFinite F)) (encFinite F) := of_finite _
  let EU := encPair (encPair encUnary encUnary)
    (encPair (encList (encFinite F)) (encList (encFinite F)))
  have hn : ComputableInPolyTime (fun u : (ℕ × ℕ) × (List F × List F) => u.1.1) EU encUnary := by
    dsimp only [EU]; fun_prop
  refine mapWithInput (ComputableInPolyTime.range.comp hn) ?_
  let EC := encPair EU encUnary
  have hrc : ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × (List F × List F)) × ℕ => x.1.2.2.getD x.2 0) EC (encFinite F) := by
    dsimp only [EC, EU]; fun_prop
  have hrj : ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × (List F × List F)) × ℕ => x.1.2.2.getD x.1.1.2 0) EC (encFinite F) := by
    dsimp only [EC, EU]; fun_prop
  have hpc : ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × (List F × List F)) × ℕ => x.1.2.1.getD x.2 0) EC (encFinite F) := by
    dsimp only [EC, EU]; fun_prop
  exact hsub.comp (hrc.prod (hmul.comp (hrj.prod hpc)))

private theorem computableInPolyTime_finElimStep :
    ComputableInPolyTime
      (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ =>
        finElimStep (F := F) p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encSweepState F)) encUnary)
      (encSweepState F) := by
  have hnz : ComputableInPolyTime (fun x : F => decide (x ≠ 0)) (encFinite F) encBool :=
    of_finite _
  let Ein := encPair (encPair encUnary (encSweepState F)) encUnary
  have hn : ComputableInPolyTime (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ => p.1.1)
      Ein encUnary := (fst _ _).comp (fst _ _)
  have hs : ComputableInPolyTime (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ => p.1.2)
      Ein (encSweepState F) := (snd _ _).comp (fst _ _)
  have hj : ComputableInPolyTime (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ => p.2)
      Ein encUnary := snd _ _
  have hs1 : ComputableInPolyTime
      (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ => p.1.2.1)
      Ein (encList (encPair encUnary (encList (encFinite F)))) := (fst _ _).comp hs
  have hs2 : ComputableInPolyTime
      (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ => p.1.2.2)
      Ein (encList (encList (encFinite F))) := (snd _ _).comp hs
  have hget : ComputableInPolyTime (fun q : List F × ℕ => q.1.getD q.2 0)
      (encPair (encList (encFinite F)) encUnary) (encFinite F) := by fun_prop
  have hfind : ComputableInPolyTime
      (fun p : (ℕ × (List (ℕ × List F) × List (List F))) × ℕ =>
        p.1.2.2.find? fun w => decide (w.getD p.2 0 ≠ 0))
      Ein (encOption (encList (encFinite F))) := by
    refine findWithInput hs2 ?_
    let EF := encPair Ein (encList (encFinite F))
    exact hnz.comp (hget.comp
      ((snd Ein (encList (encFinite F))).prod (hj.comp (fst Ein (encList (encFinite F))))))
  let Esome := encPair Ein (encList (encFinite F))
  have hnj_some : ComputableInPolyTime
      (fun q : ((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F => (q.1.1.1, q.1.2))
      Esome (encPair encUnary encUnary) :=
    (hn.comp (fst Ein (encList (encFinite F)))).prod (hj.comp (fst Ein (encList (encFinite F))))
  have hp_row : ComputableInPolyTime
      (fun q : ((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F =>
        let inv := (q.2.getD q.1.2 0)⁻¹
        (List.range q.1.1.1).map fun c => inv * q.2.getD c 0)
      Esome (encList (encFinite F)) :=
    (poly_elimPivotRow F).comp (hnj_some.prod (snd Ein (encList (encFinite F))))
  let Epiv := encPair encUnary (encList (encFinite F))
  have hupd_pivs : ComputableInPolyTime
      (fun q : ((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F =>
        let inv := (q.2.getD q.1.2 0)⁻¹
        let p := (List.range q.1.1.1).map fun c => inv * q.2.getD c 0
        q.1.1.2.1.map (fun r =>
          (r.1, (List.range q.1.1.1).map fun c =>
            r.2.getD c 0 - r.2.getD q.1.2 0 * p.getD c 0)) ++ [(q.1.2, p)])
      Esome (encList Epiv) := by
    have hmapped : ComputableInPolyTime
        (fun q : ((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F =>
          let inv := (q.2.getD q.1.2 0)⁻¹
          let p := (List.range q.1.1.1).map fun c => inv * q.2.getD c 0
          q.1.1.2.1.map fun r =>
            (r.1, (List.range q.1.1.1).map fun c =>
              r.2.getD c 0 - r.2.getD q.1.2 0 * p.getD c 0))
        Esome (encList Epiv) := by
      refine mapWithInput (hs1.comp (fst Ein (encList (encFinite F)))) ?_
      let EM := encPair Esome Epiv
      have hr1 : ComputableInPolyTime
          (fun u : (((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F) × (ℕ × List F) =>
            u.2.1) EM encUnary :=
        (fst encUnary (encList (encFinite F))).comp (snd Esome Epiv)
      have hr2_upd : ComputableInPolyTime
          (fun u : (((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F) × (ℕ × List F) =>
            let inv := (u.1.2.getD u.1.1.2 0)⁻¹
            let p := (List.range u.1.1.1.1).map fun c => inv * u.1.2.getD c 0
            (List.range u.1.1.1.1).map fun c =>
              u.2.2.getD c 0 - u.2.2.getD u.1.1.2 0 * p.getD c 0)
          EM (encList (encFinite F)) :=
        (poly_elimUpdateRow F).comp
          ((hnj_some.comp (fst Esome Epiv)).prod
            ((hp_row.comp (fst Esome Epiv)).prod
              ((snd encUnary (encList (encFinite F))).comp (snd Esome Epiv))))
      exact hr1.prod hr2_upd
    have htail : ComputableInPolyTime
        (fun q : ((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F =>
          [(q.1.2,
            let inv := (q.2.getD q.1.2 0)⁻¹
            (List.range q.1.1.1).map fun c => inv * q.2.getD c 0)])
        Esome (encList Epiv) := by
      have hsing : ComputableInPolyTime (fun x : ℕ × List F => [x]) Epiv (encList Epiv) := by
        dsimp only [Epiv]; fun_prop
      exact hsing.comp ((hj.comp (fst Ein (encList (encFinite F)))).prod hp_row)
    have happ : ComputableInPolyTime
        (fun x : List (ℕ × List F) × List (ℕ × List F) => x.1 ++ x.2)
        (encPair (encList Epiv) (encList Epiv)) (encList Epiv) := by
      dsimp only [Epiv]; fun_prop
    exact happ.comp (hmapped.prod htail)
  have hupd_todo : ComputableInPolyTime
      (fun q : ((ℕ × (List (ℕ × List F) × List (List F))) × ℕ) × List F =>
        let inv := (q.2.getD q.1.2 0)⁻¹
        let p := (List.range q.1.1.1).map fun c => inv * q.2.getD c 0
        q.1.1.2.2.map fun w =>
          (List.range q.1.1.1).map fun c => w.getD c 0 - w.getD q.1.2 0 * p.getD c 0)
      Esome (encList (encList (encFinite F))) := by
    refine mapWithInput (hs2.comp (fst Ein (encList (encFinite F)))) ?_
    exact (poly_elimUpdateRow F).comp
      ((hnj_some.comp (fst Esome (encList (encFinite F)))).prod
        ((hp_row.comp (fst Esome (encList (encFinite F)))).prod
          (snd Esome (encList (encFinite F)))))
  exact (ComputableInPolyTime.optionElimWithInput hfind hs (hupd_pivs.prod hupd_todo)).of_enc_eq
    fun p => by
      dsimp only [finElimStep]
      cases p.1.2.2.find? (fun w => decide (w.getD p.2 0 ≠ 0)) <;> rfl

/-- `finElim` is computable in polynomial time over any finite field `F`. -/
theorem computableInPolyTime_finElim :
    ComputableInPolyTime (finElim (F := F)) (encFinTable F)
      (encList (encPair encUnary (encList (encFinite F)))) := by
  obtain ⟨C, hC⟩ := length_encFinite_le F
  have hrows : ComputableInPolyTime (fun T : RowTable F => T.numRows)
      (encFinTable F) encUnary := by unfold encFinTable; fun_prop
  have hcols : ComputableInPolyTime (fun T : RowTable F => T.numCols)
      (encFinTable F) encUnary := by unfold encFinTable; fun_prop
  have hnorm : ComputableInPolyTime (normFinRows (F := F))
      (encFinTable F) (encList (encList (encFinite F))) := by
    unfold normFinRows RowTable.entry encFinTable
    fun_prop
  have hinit : ComputableInPolyTime
      (fun T : RowTable F => (([] : List (ℕ × List F)), normFinRows T))
      (encFinTable F) (encSweepState F) :=
    (const (encOut := encList (encPair encUnary (encList (encFinite F)))) []).prod hnorm
  let rowBound (n : ℕ) : ℕ := n * (2 * C + 1)
  let B (T : RowTable F) : ℕ :=
    2 * (T.numCols * (2 * (2 * T.numCols + 1 + rowBound T.numCols) + 1)) + 1 +
      T.numRows * (2 * rowBound T.numCols + 1)
  have hB_poly : PolyBounded (fun T => (encFinTable F T).length) B := by
    dsimp only [B, rowBound]
    growth_poly
  have hfold : ComputableInPolyTime
      (fun T : RowTable F =>
        (List.range T.numCols).foldl (finElimStep T.numCols) ([], normFinRows T))
      (encFinTable F) (encSweepState F) := by
    refine foldlWith hcols (ComputableInPolyTime.range.comp hcols) hinit
      (computableInPolyTime_finElimStep F) hB_poly ?_
    intro T k hk
    have hk_le : k ≤ T.numCols := by simpa using hk
    have hinv := finSweepInv_take T k hk_le
    set st := ((List.range T.numCols).take k).foldl (finElimStep T.numCols) ([], normFinRows T)
    have hrow_len : ∀ r : List F, r.length = T.numCols →
        (encList (encFinite F) r).length ≤ rowBound T.numCols := by
      intro r hr
      have := length_encList_le (encFinite F) r (fun x _ => hC x)
      rwa [hr] at this
    have hpiv_elem : ∀ q ∈ st.1,
        (encPair encUnary (encList (encFinite F)) q).length ≤
          2 * T.numCols + 1 + rowBound T.numCols := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := hinv.piv_lt q hq
      have h1 : (encUnary q.1).length ≤ T.numCols := by simp; omega
      have h2 := hrow_len q.2 hq2
      rw [length_encPair]
      omega
    have hs1_len : (encList (encPair encUnary (encList (encFinite F))) st.1).length ≤
        T.numCols * (2 * (2 * T.numCols + 1 + rowBound T.numCols) + 1) := by
      have h1 := length_encList_le (encPair encUnary (encList (encFinite F))) st.1 hpiv_elem
      have h2 : st.1.length ≤ T.numCols := hinv.piv_len.trans hk_le
      exact h1.trans (Nat.mul_le_mul_right _ h2)
    have hs2_len : (encList (encList (encFinite F)) st.2).length ≤
        T.numRows * (2 * rowBound T.numCols + 1) := by
      have h1 := length_encList_le (encList (encFinite F)) st.2
        (fun w hw => hrow_len w (hinv.todo_width w hw))
      rwa [hinv.todo_len] at h1
    rw [encSweepState, length_encPair]
    dsimp only [B]
    omega
  exact ((fst _ _).comp hfold).of_enc_eq fun _ => rfl

/-- `finRowBasis` is computable in polynomial time over any finite field `F`. -/
theorem computableInPolyTime_finRowBasis :
    ComputableInPolyTime (finRowBasis (F := F)) (encFinTable F)
      (encList (encList (encFinite F))) := by
  have hp := computableInPolyTime_finElim F
  unfold finRowBasis
  fun_prop

/-- `finKernelBasis` is computable in polynomial time over any finite field `F`. -/
theorem computableInPolyTime_finKernelBasis :
    ComputableInPolyTime (finKernelBasis (F := F)) (encFinTable F)
      (encList (encList (encFinite F))) := by
  have hp := computableInPolyTime_finElim F
  have hneg : ComputableInPolyTime (fun x : F => -x) (encFinite F) (encFinite F) := of_finite _
  have hcols : ComputableInPolyTime (fun T : RowTable F => T.numCols)
      (encFinTable F) encUnary := by unfold encFinTable; fun_prop
  have hfree : ComputableInPolyTime
      (fun T : RowTable F =>
        let pivCols := (finElim T).map Prod.fst
        (List.range T.numCols).filter fun j => !pivCols.contains j)
      (encFinTable F) (encList encUnary) := by
    fun_prop
  refine (mapWithInput hfree ?_).of_enc_eq fun _ => rfl
  refine mapWithInput (ComputableInPolyTime.range.comp (hcols.comp (fst _ _))) ?_
  let E := encPair (encPair (encFinTable F) encUnary) encUnary
  have hc : ComputableInPolyTime (fun x : (RowTable F × ℕ) × ℕ => x.2) E encUnary := snd _ _
  have hj : ComputableInPolyTime (fun x : (RowTable F × ℕ) × ℕ => x.1.2) E encUnary :=
    (snd _ _).comp (fst _ _)
  have hpivs : ComputableInPolyTime (fun x : (RowTable F × ℕ) × ℕ => finElim x.1.1)
      E (encList (encPair encUnary (encList (encFinite F)))) :=
    hp.comp ((fst _ _).comp (fst _ _))
  have hfind : ComputableInPolyTime
      (fun x : (RowTable F × ℕ) × ℕ => (finElim x.1.1).find? fun q => q.1 == x.2)
      E (encOption (encPair encUnary (encList (encFinite F)))) := by
    refine findWithInput hpivs ?_
    let EF := encPair E (encPair encUnary (encList (encFinite F)))
    exact unary_beq
      ((fst encUnary (encList (encFinite F))).comp
        (snd E (encPair encUnary (encList (encFinite F)))))
      (hc.comp (fst E (encPair encUnary (encList (encFinite F)))))
  have hget : ComputableInPolyTime (fun q : List F × ℕ => q.1.getD q.2 0)
      (encPair (encList (encFinite F)) encUnary) (encFinite F) := by fun_prop
  have helse : ComputableInPolyTime
      (fun x : (RowTable F × ℕ) × ℕ =>
        match (finElim x.1.1).find? (fun q => q.1 == x.2) with
        | some q => -q.2.getD x.1.2 0
        | none => 0)
      E (encFinite F) := by
    refine (ComputableInPolyTime.optionElimWithInput hfind (const (encOut :=
      encFinite F) 0) ?_).of_enc_eq
      fun x => by cases (finElim x.1.1).find? (fun q => q.1 == x.2) <;> rfl
    let Epiv := encPair encUnary (encList (encFinite F))
    exact hneg.comp (hget.comp
      (((snd encUnary (encList (encFinite F))).comp (snd E Epiv)).prod (hj.comp (fst E Epiv))))
  exact (unary_beq hc hj).ite (const (encOut := encFinite F) 1) helse

/-- `finSolve` is computable in polynomial time over any finite field `F`. -/
theorem computableInPolyTime_finSolve :
    ComputableInPolyTime (fun p : RowTable F × List F => finSolve p.1 p.2)
      (encPair (encFinTable F) (encList (encFinite F)))
      (encOption (encList (encFinite F))) := by
  let Ein := encPair (encFinTable F) (encList (encFinite F))
  have haug : ComputableInPolyTime (fun p : RowTable F × List F => augmentFinTable p.1 p.2)
      Ein (encFinTable F) := by
    unfold augmentFinTable RowTable.entry encFinTable
    dsimp only [Ein]
    fun_prop
  have hpivs := (computableInPolyTime_finElim F).comp haug
  have hcols : ComputableInPolyTime (fun p : RowTable F × List F => p.1.numCols)
      Ein encUnary := by
    have h1 : ComputableInPolyTime (fun T : RowTable F => T.numCols)
        (encFinTable F) encUnary := by unfold encFinTable; fun_prop
    exact h1.comp (fst (encFinTable F) (encList (encFinite F)))
  have hcont : ComputableInPolyTime
      (fun p : RowTable F × List F =>
        ((finElim (augmentFinTable p.1 p.2)).map Prod.fst).contains p.1.numCols)
      Ein encBool := by
    fun_prop
  have hget : ComputableInPolyTime (fun q : List F × ℕ => q.1.getD q.2 0)
      (encPair (encList (encFinite F)) encUnary) (encFinite F) := by fun_prop
  have hsol : ComputableInPolyTime
      (fun p : RowTable F × List F =>
        (List.range p.1.numCols).map fun c =>
          match (finElim (augmentFinTable p.1 p.2)).find? (fun q => q.1 == c) with
          | some q => q.2.getD p.1.numCols 0
          | none => 0)
      Ein (encList (encFinite F)) := by
    refine mapWithInput (ComputableInPolyTime.range.comp hcols) ?_
    let E2 := encPair Ein encUnary
    let Epiv := encPair encUnary (encList (encFinite F))
    have hfind : ComputableInPolyTime
        (fun x : (RowTable F × List F) × ℕ =>
          (finElim (augmentFinTable x.1.1 x.1.2)).find? fun q => q.1 == x.2)
        E2 (encOption Epiv) := by
      refine findWithInput (hpivs.comp (fst Ein encUnary)) ?_
      exact unary_beq
        ((fst encUnary (encList (encFinite F))).comp (snd E2 Epiv))
        ((snd Ein encUnary).comp (fst E2 Epiv))
    refine (ComputableInPolyTime.optionElimWithInput hfind (const (encOut :=
      encFinite F) 0) ?_).of_enc_eq
      fun x => by
        cases (finElim (augmentFinTable x.1.1 x.1.2)).find? (fun q => q.1 == x.2) <;> rfl
    exact hget.comp
      (((snd encUnary (encList (encFinite F))).comp (snd E2 Epiv)).prod
        (hcols.comp ((fst Ein encUnary).comp (fst E2 Epiv))))
  have hsome : ComputableInPolyTime (fun l : List F => some l)
      (encList (encFinite F)) (encOption (encList (encFinite F))) := by fun_prop
  exact (hcont.ite (const (encOut := encOption (encList (encFinite F))) none)
    (hsome.comp hsol)).of_enc_eq fun _ => rfl

end PolyTime

end Cslib.LinearAlgebra
