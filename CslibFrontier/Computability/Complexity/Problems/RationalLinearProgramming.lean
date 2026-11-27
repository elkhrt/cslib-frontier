/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.LinearProgramming
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import Mathlib.Basic.Real.Basic

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational and Real Linear-Programming Feasibility

Extends `CslibFrontier.Computability.Complexity.Problems.LinearProgramming` with:

1. Equivalence of real (`ℝ`) and rational (`ℚ`) solvability for integer and rational linear
   inequality systems (`LPFeasibility.mem_iff_exists_real` and
   `realLPFeasibility_eq_rationalLPFeasibility`), proved from `Matrix.exists_int_mulVec_le` at
   `K = ℝ`.
2. Polynomial-time row-wise denominator clearing `clearRationalSystem` from rational linear
   inequality systems (`RationalLinearInequality`) to `LPFeasibility`, proving
   `RationalLPFeasibility ∈ NP ∩ coNP` and `RealLPFeasibility ∈ NP ∩ coNP`.
3. Unconditional polynomial-time decidability (`P`) of single-variable linear-programming
   feasibility (`singleVarLPFeasibility_mem_P`).

## Main definitions

* `Cslib.Complexity.RationalLinearInequality`, `Cslib.Complexity.encRationalLinearInequality`,
  `Cslib.Complexity.encRationalSystem`
* `Cslib.Complexity.RationalLPFeasibility`, `Cslib.Complexity.RealLPFeasibility`
* `Cslib.Complexity.clearRationalRow`, `Cslib.Complexity.clearRationalSystem`
* `Cslib.Complexity.SingleVarLPFeasibility`

## Main results

* `Cslib.Complexity.LPFeasibility.mem_iff_exists_real`
* `Cslib.Complexity.realLPFeasibility_eq_rationalLPFeasibility`
* `Cslib.Complexity.computableInPolyTime_clearRationalSystem`
* `Cslib.Complexity.polyTimeReducible_rationalLP_lpFeasibility`,
  `Cslib.Complexity.polyTimeReducible_realLP_lpFeasibility`
* `Cslib.Complexity.rationalLPFeasibility_mem_NP`,
  `Cslib.Complexity.rationalLPFeasibility_mem_coNP`,
  `Cslib.Complexity.realLPFeasibility_mem_NP`, `Cslib.Complexity.realLPFeasibility_mem_coNP`
* `Cslib.Complexity.singleVarLPFeasibility_mem_P`
-/

public section

namespace Cslib.Complexity

open Finset Matrix Turing.MultiTapeTM ComputableInPolyTime

private lemma maxCols_bound (C : List LinearInequality) :
    ∀ c ∈ C, c.coeffs.length ≤ (C.map (fun r => r.coeffs.length)).foldl max 0 := by
  have hfold_mono : ∀ (l : List ℕ) (a b : ℕ), a ≤ b → l.foldl max a ≤ l.foldl max b := by
    intro l
    induction l with
    | nil => intro _ _ h; exact h
    | cons x xs ih => intro a b h; exact ih _ _ (max_le_max_right x h)
  have hfold_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a := by
    intro l
    induction l with
    | nil => intro _; exact le_rfl
    | cons x xs ih => intro a; exact le_trans (le_max_left a x) (ih (max a x))
  induction C with
  | nil => intro _ h; cases h
  | cons r rs ih =>
    intro c hc
    simp only [List.map_cons, List.foldl_cons, Nat.zero_max]
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact hfold_init _ _
    · exact le_trans (ih c hmem) (hfold_mono _ 0 r.coeffs.length (Nat.zero_le _))

private lemma abs_entry_le_maxEntry (C : List LinearInequality) :
    ∃ B : ℕ, (∀ i : Fin C.length, ∀ j,
      |(C[i.1].coeffs.getD j 0 : ℤ)| ≤ (B : ℤ)) ∧
      ∀ i : Fin C.length, |C[i.1].bound| ≤ (B : ℤ) := by
  let rowMax (c : LinearInequality) : ℕ :=
    (c.coeffs.map Int.natAbs).foldl max c.bound.natAbs
  let B : ℕ := (C.map rowMax).foldl max 0
  have hfold_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a := by
    intro l
    induction l with
    | nil => intro _; exact le_rfl
    | cons x xs ih => intro a; exact le_trans (le_max_left a x) (ih (max a x))
  have hfold_mem : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → x ≤ l.foldl max a := by
    intro l
    induction l with
    | nil => intro _ _ h; cases h
    | cons y ys ih =>
      intro a x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact le_trans (le_max_right a x) (hfold_init ys (max a x))
      · exact ih (max a y) x hmem
  refine ⟨B, fun i j => ?_, fun i => ?_⟩
  · have hrow : rowMax C[i.1] ≤ B :=
      hfold_mem (C.map rowMax) 0 (rowMax C[i.1]) (List.mem_map_of_mem (List.getElem_mem i.2))
    rcases List.getD_mem_or C[i.1].coeffs j 0 with hj | hj
    · have hj_le : (C[i.1].coeffs.getD j 0).natAbs ≤ rowMax C[i.1] :=
        hfold_mem (C[i.1].coeffs.map Int.natAbs) C[i.1].bound.natAbs _
          (List.mem_map_of_mem hj)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hj_le.trans hrow
    · rw [hj, abs_zero]
      exact Nat.cast_nonneg B
  · have hrow : rowMax C[i.1] ≤ B :=
      hfold_mem (C.map rowMax) 0 (rowMax C[i.1]) (List.mem_map_of_mem (List.getElem_mem i.2))
    have hb_le : C[i.1].bound.natAbs ≤ rowMax C[i.1] :=
      hfold_init (C[i.1].coeffs.map Int.natAbs) C[i.1].bound.natAbs
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hb_le.trans hrow

/-- An integer-coefficient linear inequality system belongs to `Cslib.Complexity.LPFeasibility`
if and only if it admits a real solution `x : ℕ → ℝ`. -/
theorem LPFeasibility.mem_iff_exists_real {C : List LinearInequality} :
    C ∈ LPFeasibility ↔
      ∃ x : ℕ → ℝ, ∀ c ∈ C,
        ∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℝ) * x j ≤ (c.bound : ℝ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun j => (x j : ℝ), fun c hc => ?_⟩
    have hq := hx c hc
    have hcast : (∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℝ) * (x j : ℝ)) =
        ((∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℚ) * x j : ℚ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast hq
  · rintro ⟨x, hx⟩
    let n : ℕ := (C.map (fun r => r.coeffs.length)).foldl max 0
    have hn : ∀ c ∈ C, c.coeffs.length ≤ n := maxCols_bound C
    obtain ⟨B, hA_abs, hb_abs⟩ := abs_entry_le_maxEntry C
    have hmat_real :
        (LPFeasibility.matrix C n).map (Int.cast : ℤ → ℝ) *ᵥ (fun j : Fin n => x j.1) ≤
          fun i => (LPFeasibility.rhs C i : ℝ) := by
      intro i
      have hi := hx C[i.1] (List.getElem_mem i.2)
      simp only [mulVec, dotProduct, Matrix.map_apply, LPFeasibility.matrix, of_apply,
        LPFeasibility.rhs]
      rw [Fin.sum_eq_sum_range_of_eq_zero (hn C[i.1] (List.getElem_mem i.2))
        (fun j => ((C[i.1].coeffs.getD j 0 : ℤ) : ℝ) * x j)
        fun j hj => by rw [List.getD_eq_default _ _ hj, Int.cast_zero, zero_mul]]
      exact hi
    have hA_mat : ∀ (i : Fin C.length) (j : Fin n),
        |LPFeasibility.matrix C n i j| ≤ (B : ℤ) := fun i j => hA_abs i j.1
    have hb_mat : ∀ i : Fin C.length, |LPFeasibility.rhs C i| ≤ (B : ℤ) := hb_abs
    obtain ⟨d, p, hd, hAp, -, -⟩ :=
      Matrix.exists_int_mulVec_le (K := ℝ) hA_mat hb_mat hmat_real
    have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
    rw [LPFeasibility.mem_iff_exists_mulVec_le hn]
    refine ⟨fun j => (p j : ℚ) / d, fun i => ?_⟩
    have hrow := hAp i
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hrow ⊢
    have hmul : (∑ j : Fin n, ((LPFeasibility.matrix C n i j : ℤ) : ℚ) * ((p j : ℚ) / d)) * d =
        ((∑ j : Fin n, LPFeasibility.matrix C n i j * p j : ℤ) : ℚ) := by
      rw [Finset.sum_mul]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, div_mul_cancel₀ _ hdQ.ne']
    have hle : ((∑ j : Fin n, LPFeasibility.matrix C n i j * p j : ℤ) : ℚ) ≤
        (LPFeasibility.rhs C i : ℚ) * d := by
      rw [mul_comm]
      exact_mod_cast hrow
    exact le_of_mul_le_mul_right (hmul ▸ hle) hdQ

/-- A rational linear inequality `∑ j < coeffs.length, coeffs[j] * x j ≤ bound`. -/
@[ext]
structure RationalLinearInequality where
  /-- Rational coefficients `a[0], …, a[m - 1]`. -/
  coeffs : List ℚ
  /-- Rational upper bound. -/
  bound : ℚ
  deriving DecidableEq, Repr

/-- Binary encoding of `RationalLinearInequality`. -/
@[expose]
def encRationalLinearInequality : RationalLinearInequality ↪ List Bool where
  toFun c := encPair (encList encRat) encRat (c.coeffs, c.bound)
  inj' c₁ c₂ h := by
    have hp := (encPair (encList encRat) encRat).injective h
    exact RationalLinearInequality.ext (Prod.mk.inj hp).1 (Prod.mk.inj hp).2

/-- Binary encoding of a system of rational linear inequalities. -/
abbrev encRationalSystem : List RationalLinearInequality ↪ List Bool :=
  encList encRationalLinearInequality

private theorem computableInPolyTime_ratIneq_pair :
    ComputableInPolyTime (fun c : RationalLinearInequality => (c.coeffs, c.bound))
      encRationalLinearInequality (encPair (encList encRat) encRat) :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Extracting `coeffs` from `RationalLinearInequality` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ratIneq_coeffs {α : Type} {encIn : α ↪ List Bool}
    {f : α → RationalLinearInequality}
    (hf : ComputableInPolyTime f encIn encRationalLinearInequality) :
    ComputableInPolyTime (fun a => (f a).coeffs) encIn (encList encRat) :=
  computableInPolyTime_ratIneq_pair.fst'.comp hf

/-- Extracting `bound` from `RationalLinearInequality` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ratIneq_bound {α : Type} {encIn : α ↪ List Bool}
    {f : α → RationalLinearInequality}
    (hf : ComputableInPolyTime f encIn encRationalLinearInequality) :
    ComputableInPolyTime (fun a => (f a).bound) encIn encRat :=
  computableInPolyTime_ratIneq_pair.snd'.comp hf

/-- Rational linear-programming feasibility over `ℚ`. -/
def RationalLPFeasibility : Set (List RationalLinearInequality) :=
  {C | ∃ x : ℕ → ℚ, ∀ c ∈ C,
    ∑ j ∈ range c.coeffs.length, c.coeffs.getD j 0 * x j ≤ c.bound}

/-- Rational linear-programming feasibility over `ℝ`. -/
def RealLPFeasibility : Set (List RationalLinearInequality) :=
  {C | ∃ x : ℕ → ℝ, ∀ c ∈ C,
    ∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℝ) * x j ≤ (c.bound : ℝ)}

private def rowDenominator (c : RationalLinearInequality) : ℕ :=
  c.bound.den * (c.coeffs.map Rat.den).prod

private def clearRatEntry (d : ℕ) (q : ℚ) : ℤ :=
  q.num * ((d / q.den : ℕ) : ℤ)

/-- Multiply a rational linear inequality by the positive product of its denominators to obtain an
equivalent integer `LinearInequality`. -/
def clearRationalRow (c : RationalLinearInequality) : LinearInequality where
  coeffs := c.coeffs.map (clearRatEntry (rowDenominator c))
  bound := clearRatEntry (rowDenominator c) c.bound

/-- Clear denominators row-by-row across a system of rational linear inequalities. -/
def clearRationalSystem (C : List RationalLinearInequality) : List LinearInequality :=
  C.map clearRationalRow

private theorem rowDenominator_pos (c : RationalLinearInequality) : 0 < rowDenominator c :=
  Nat.mul_pos c.bound.pos (List.prod_pos (by simp [Rat.pos]))

private theorem clearRationalRow_entry_cast (c : RationalLinearInequality) (j : ℕ) :
    (((clearRationalRow c).coeffs.getD j 0 : ℤ) : ℚ) =
      (rowDenominator c : ℚ) * c.coeffs.getD j 0 := by
  have hdvd {q : ℚ} (hq : q ∈ c.coeffs) : q.den ∣ rowDenominator c :=
    dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)) _
  have hmap : (clearRationalRow c).coeffs.getD j 0 =
      clearRatEntry (rowDenominator c) (c.coeffs.getD j 0) := by
    simpa [clearRationalRow, clearRatEntry] using
      List.getD_map (l := c.coeffs) (d := 0) (n := j) (clearRatEntry (rowDenominator c))
  rw [hmap]
  exact (List.getD_mem_or c.coeffs j 0).elim
    (fun hj => (Rat.clearDenom_entry (hdvd hj)).symm)
    fun hj => by rw [hj]; simp [clearRatEntry]

private theorem clearRationalRow_bound_cast (c : RationalLinearInequality) :
    (((clearRationalRow c).bound : ℤ) : ℚ) = (rowDenominator c : ℚ) * c.bound :=
  (Rat.clearDenom_entry (dvd_mul_right c.bound.den _)).symm

private theorem satisfies_clearRationalRow_rat_iff (c : RationalLinearInequality) (x : ℕ → ℚ) :
    (∑ j ∈ range (clearRationalRow c).coeffs.length,
      ((clearRationalRow c).coeffs.getD j 0 : ℚ) * x j ≤ (clearRationalRow c).bound) ↔
      ∑ j ∈ range c.coeffs.length, c.coeffs.getD j 0 * x j ≤ c.bound := by
  have hlen : (clearRationalRow c).coeffs.length = c.coeffs.length := by simp [clearRationalRow]
  rw [hlen, clearRationalRow_bound_cast]
  simp only [clearRationalRow_entry_cast, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_iff_right₀ (by exact_mod_cast rowDenominator_pos c)

private theorem satisfies_clearRationalRow_real_iff (c : RationalLinearInequality) (x : ℕ → ℝ) :
    (∑ j ∈ range (clearRationalRow c).coeffs.length,
      ((clearRationalRow c).coeffs.getD j 0 : ℝ) * x j ≤ ((clearRationalRow c).bound : ℝ)) ↔
      ∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℝ) * x j ≤ (c.bound : ℝ) := by
  have hlen : (clearRationalRow c).coeffs.length = c.coeffs.length := by simp [clearRationalRow]
  have hentry (j : ℕ) : (((clearRationalRow c).coeffs.getD j 0 : ℤ) : ℝ) =
      (rowDenominator c : ℝ) * (c.coeffs.getD j 0 : ℝ) := by
    exact_mod_cast clearRationalRow_entry_cast c j
  have hbound : (((clearRationalRow c).bound : ℤ) : ℝ) =
      (rowDenominator c : ℝ) * (c.bound : ℝ) := by
    exact_mod_cast clearRationalRow_bound_cast c
  rw [hlen, hbound]
  simp only [hentry, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_iff_right₀ (by exact_mod_cast rowDenominator_pos c)

/-- Real and rational feasibility coincide on rational linear inequality systems. -/
theorem realLPFeasibility_eq_rationalLPFeasibility :
    RealLPFeasibility = RationalLPFeasibility := by
  ext C
  have hrat : clearRationalSystem C ∈ LPFeasibility ↔ C ∈ RationalLPFeasibility := by
    simp only [clearRationalSystem, LPFeasibility, RationalLPFeasibility, Set.mem_ofPred_eq,
      List.forall_mem_map, satisfies_clearRationalRow_rat_iff]
  have hreal : clearRationalSystem C ∈ LPFeasibility ↔ C ∈ RealLPFeasibility := by
    rw [LPFeasibility.mem_iff_exists_real]
    simp only [clearRationalSystem, RealLPFeasibility, Set.mem_ofPred_eq,
      List.forall_mem_map, satisfies_clearRationalRow_real_iff]
  rw [← hreal, hrat]

@[local fun_prop]
private theorem computableInPolyTime_rowDenominator :
    ComputableInPolyTime rowDenominator encRationalLinearInequality encNat := by
  unfold rowDenominator
  have hden : ComputableInPolyTime (fun c : RationalLinearInequality => c.bound.den)
      encRationalLinearInequality encNat := rat_den.comp (computableInPolyTime_ratIneq_bound id')
  have hprod :
      ComputableInPolyTime (fun c : RationalLinearInequality => (c.coeffs.map Rat.den).prod)
      encRationalLinearInequality encNat :=
    binary_prod.comp ((map rat_den).comp (computableInPolyTime_ratIneq_coeffs id'))
  exact binary_mul' hden hprod

/-- Clearing denominators across a rational linear inequality system is computable in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_clearRationalSystem :
    ComputableInPolyTime clearRationalSystem encRationalSystem LPFeasibility.encSystem := by
  have hrow : ComputableInPolyTime clearRationalRow encRationalLinearInequality
      encLinearInequality := by
    unfold clearRationalRow clearRatEntry
    have hcoeffs : ComputableInPolyTime
        (fun c : RationalLinearInequality =>
          c.coeffs.map fun q => q.num * ((rowDenominator c / q.den : ℕ) : ℤ))
        encRationalLinearInequality (encList encIntBin) := by
      apply mapWithInput (computableInPolyTime_ratIneq_coeffs id')
      have hnum := rat_num.comp (snd encRationalLinearInequality encRat)
      have hden := rat_den.comp (snd encRationalLinearInequality encRat)
      have hrden :=
        computableInPolyTime_rowDenominator.comp (fst encRationalLinearInequality encRat)
      exact intBin_mul' hnum (intBin_natCast.comp (binary_div' hrden hden))
    have hbound : ComputableInPolyTime
        (fun c : RationalLinearInequality =>
          c.bound.num * ((rowDenominator c / c.bound.den : ℕ) : ℤ))
        encRationalLinearInequality encIntBin := by
      have hnum := rat_num.comp (computableInPolyTime_ratIneq_bound id')
      have hden := rat_den.comp (computableInPolyTime_ratIneq_bound id')
      exact intBin_mul' hnum
        (intBin_natCast.comp (binary_div' computableInPolyTime_rowDenominator hden))
    exact (hcoeffs.prod hbound).of_enc_eq fun _ => rfl
  exact map hrow

/-- Polynomial-time many-one reduction from `RationalLPFeasibility` to `LPFeasibility`. -/
theorem polyTimeReducible_rationalLP_lpFeasibility :
    PolyTimeReducible encRationalSystem LPFeasibility.encSystem
      RationalLPFeasibility LPFeasibility :=
  ⟨clearRationalSystem, computableInPolyTime_clearRationalSystem, fun C => by
    simp only [clearRationalSystem, LPFeasibility, RationalLPFeasibility, Set.mem_ofPred_eq,
      List.forall_mem_map, satisfies_clearRationalRow_rat_iff]⟩

/-- Polynomial-time many-one reduction from `RealLPFeasibility` to `LPFeasibility`. -/
theorem polyTimeReducible_realLP_lpFeasibility :
    PolyTimeReducible encRationalSystem LPFeasibility.encSystem
      RealLPFeasibility LPFeasibility :=
  ⟨clearRationalSystem, computableInPolyTime_clearRationalSystem, fun C => by
    rw [LPFeasibility.mem_iff_exists_real]
    simp only [clearRationalSystem, RealLPFeasibility, Set.mem_ofPred_eq,
      List.forall_mem_map, satisfies_clearRationalRow_real_iff]⟩

/-- Rational linear-programming feasibility belongs to `NP`. -/
theorem rationalLPFeasibility_mem_NP : RationalLPFeasibility ∈ NP encRationalSystem :=
  polyTimeReducible_rationalLP_lpFeasibility.mem_NP LPFeasibility.mem_NP

/-- Rational linear-programming feasibility belongs to `coNP`. -/
theorem rationalLPFeasibility_mem_coNP : RationalLPFeasibility ∈ coNP encRationalSystem :=
  polyTimeReducible_rationalLP_lpFeasibility.mem_coNP LPFeasibility.mem_coNP

/-- Real linear-programming feasibility of rational systems belongs to `NP`. -/
theorem realLPFeasibility_mem_NP : RealLPFeasibility ∈ NP encRationalSystem :=
  polyTimeReducible_realLP_lpFeasibility.mem_NP LPFeasibility.mem_NP

/-- Real linear-programming feasibility of rational systems belongs to `coNP`. -/
theorem realLPFeasibility_mem_coNP : RealLPFeasibility ∈ coNP encRationalSystem :=
  polyTimeReducible_realLP_lpFeasibility.mem_coNP LPFeasibility.mem_coNP

/-- Single-variable slice of `Cslib.Complexity.LPFeasibility`. -/
def SingleVarLPFeasibility : Set (List LinearInequality) :=
  {C | (∀ c ∈ C, c.coeffs.length ≤ 1) ∧ C ∈ LPFeasibility}

private def decideSingleVarLP (C : List LinearInequality) : Bool :=
  (C.all fun c => decide (c.coeffs.length ≤ 1)) &&
  (C.all fun c => decide (c.coeffs.getD 0 0 ≠ 0 ∨ 0 ≤ c.bound)) &&
  (C.all fun c₁ => C.all fun c₂ =>
    decide (¬(c₁.coeffs.getD 0 0 < 0 ∧ 0 < c₂.coeffs.getD 0 0) ∨
      0 ≤ c₂.coeffs.getD 0 0 * c₁.bound - c₁.coeffs.getD 0 0 * c₂.bound))

private lemma sum_single_var (c : LinearInequality) (hl : c.coeffs.length ≤ 1) (x : ℕ → ℚ) :
    ∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℚ) * x j =
      (c.coeffs.getD 0 0 : ℚ) * x 0 := by
  rcases hc : c.coeffs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp
  · simp
  · simp [hc] at hl

private lemma decideSingleVarLP_eq_true_iff (C : List LinearInequality) :
    decideSingleVarLP C = true ↔ C ∈ SingleVarLPFeasibility := by
  simp only [decideSingleVarLP, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    SingleVarLPFeasibility, Set.mem_ofPred_eq, LPFeasibility]
  constructor
  · rintro ⟨⟨hlen, hzero⟩, hcross⟩
    refine ⟨hlen, ?_⟩
    let lowers : List ℚ := (C.filter fun c => decide (c.coeffs.getD 0 0 < 0)).map
      fun c => (c.bound : ℚ) / (c.coeffs.getD 0 0 : ℚ)
    let uppers : List ℚ := (C.filter fun c => decide (0 < c.coeffs.getD 0 0)).map
      fun c => (c.bound : ℚ) / (c.coeffs.getD 0 0 : ℚ)
    have hlu : ∀ l ∈ lowers, ∀ u ∈ uppers, l ≤ u := by
      intro l hl u hu
      obtain ⟨c₁, hc₁f, rfl⟩ := List.mem_map.mp hl
      obtain ⟨c₂, hc₂f, rfl⟩ := List.mem_map.mp hu
      have hc₁ := (List.mem_filter.mp hc₁f).1
      have ha₁ : c₁.coeffs.getD 0 0 < 0 := of_decide_eq_true (List.mem_filter.mp hc₁f).2
      have hc₂ := (List.mem_filter.mp hc₂f).1
      have ha₂ : 0 < c₂.coeffs.getD 0 0 := of_decide_eq_true (List.mem_filter.mp hc₂f).2
      have hcr := (hcross c₁ hc₁ c₂ hc₂).resolve_left (not_not.mpr ⟨ha₁, ha₂⟩)
      have ha₁Q : (c₁.coeffs.getD 0 0 : ℚ) < 0 := by exact_mod_cast ha₁
      have ha₂Q : (0 : ℚ) < (c₂.coeffs.getD 0 0 : ℚ) := by exact_mod_cast ha₂
      have hcrQ : (0 : ℚ) ≤
          (c₂.coeffs.getD 0 0 : ℚ) * c₁.bound - (c₁.coeffs.getD 0 0 : ℚ) * c₂.bound := by
        exact_mod_cast hcr
      rw [div_le_iff_of_neg ha₁Q]
      have hmul : (c₂.bound : ℚ) / (c₂.coeffs.getD 0 0 : ℚ) * (c₁.coeffs.getD 0 0 : ℚ) =
          ((c₁.coeffs.getD 0 0 : ℚ) * c₂.bound) / (c₂.coeffs.getD 0 0 : ℚ) := by ring
      rw [hmul, div_le_iff₀ ha₂Q]
      linarith
    obtain ⟨x₀, hxlo, hxhi⟩ : ∃ x₀ : ℚ, (∀ l ∈ lowers, l ≤ x₀) ∧ ∀ u ∈ uppers, x₀ ≤ u := by
      rcases lowers with _ | ⟨l₀, ls⟩
      · rcases uppers with _ | ⟨u₀, us⟩
        · exact ⟨0, by simp, by simp⟩
        · let U : Finset ℚ := (u₀ :: us).toFinset
          have hUne : U.Nonempty := ⟨u₀, by simp [U]⟩
          exact ⟨U.min' hUne, by simp, fun u hu => Finset.min'_le U u (List.mem_toFinset.mpr hu)⟩
      · let S : Finset ℚ := (l₀ :: ls).toFinset
        have hSne : S.Nonempty := ⟨l₀, by simp [S]⟩
        refine ⟨S.max' hSne, fun l hl => Finset.le_max' S l (List.mem_toFinset.mpr hl),
          fun u hu => ?_⟩
        exact hlu (S.max' hSne) (List.mem_toFinset.mp (Finset.max'_mem S hSne)) u hu
    refine ⟨fun _ => x₀, fun c hc => ?_⟩
    rw [sum_single_var c (hlen c hc)]
    rcases lt_trichotomy (c.coeffs.getD 0 0) 0 with ha | ha | ha
    · have hmem : ((c.bound : ℚ) / (c.coeffs.getD 0 0 : ℚ)) ∈ lowers :=
        List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, decide_eq_true ha⟩, rfl⟩
      have hle := hxlo _ hmem
      have haQ : (c.coeffs.getD 0 0 : ℚ) < 0 := by exact_mod_cast ha
      have hmul := mul_le_mul_of_nonpos_left hle haQ.le
      rwa [mul_div_cancel₀ _ haQ.ne] at hmul
    · rw [ha, Int.cast_zero, zero_mul]
      exact_mod_cast (hzero c hc).resolve_left (not_not.mpr ha)
    · have hmem : ((c.bound : ℚ) / (c.coeffs.getD 0 0 : ℚ)) ∈ uppers :=
        List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, decide_eq_true ha⟩, rfl⟩
      have hle := hxhi _ hmem
      have haQ : (0 : ℚ) < (c.coeffs.getD 0 0 : ℚ) := by exact_mod_cast ha
      have hmul := mul_le_mul_of_nonneg_left hle haQ.le
      rwa [mul_div_cancel₀ _ haQ.ne'] at hmul
  · rintro ⟨hlen, ⟨x, hx⟩⟩
    refine ⟨⟨hlen, fun c hc => ?_⟩, fun c₁ hc₁ c₂ hc₂ => ?_⟩
    · by_cases ha : c.coeffs.getD 0 0 = 0
      · right
        have hrow := hx c hc
        rw [sum_single_var c (hlen c hc), ha, Int.cast_zero, zero_mul] at hrow
        exact_mod_cast hrow
      · exact Or.inl ha
    · by_cases hpair : c₁.coeffs.getD 0 0 < 0 ∧ 0 < c₂.coeffs.getD 0 0
      · right
        obtain ⟨ha₁, ha₂⟩ := hpair
        have h₁ := hx c₁ hc₁
        have h₂ := hx c₂ hc₂
        rw [sum_single_var c₁ (hlen c₁ hc₁)] at h₁
        rw [sum_single_var c₂ (hlen c₂ hc₂)] at h₂
        have ha₁Q : (c₁.coeffs.getD 0 0 : ℚ) < 0 := by exact_mod_cast ha₁
        have ha₂Q : (0 : ℚ) < (c₂.coeffs.getD 0 0 : ℚ) := by exact_mod_cast ha₂
        have hcomb : (0 : ℚ) ≤
            (c₂.coeffs.getD 0 0 : ℚ) * c₁.bound - (c₁.coeffs.getD 0 0 : ℚ) * c₂.bound := by
          nlinarith
        exact_mod_cast hcomb
      · exact Or.inl hpair

/-- Single-variable linear-programming feasibility belongs to `Cslib.Complexity.P`. -/
theorem singleVarLPFeasibility_mem_P :
    SingleVarLPFeasibility ∈ P LPFeasibility.encSystem := by
  rw [mem_P]
  refine ⟨decideSingleVarLP, ?_, fun C => (decideSingleVarLP_eq_true_iff C).symm⟩
  have h : decideSingleVarLP = fun C : List LinearInequality =>
      (C.all fun c => decide (c.coeffs.length ≤ 1)) &&
      (C.all fun c => !decide (c.coeffs.getD 0 0 = 0) || decide (0 ≤ c.bound)) &&
      (C.all fun c₁ => C.all fun c₂ =>
        !(decide (c₁.coeffs.getD 0 0 < 0) && decide (0 < c₂.coeffs.getD 0 0)) ||
        decide (0 ≤ c₂.coeffs.getD 0 0 * c₁.bound - c₁.coeffs.getD 0 0 * c₂.bound)) := by
    funext C
    simp only [decideSingleVarLP]
    refine congrArg₂ (· && ·) (congrArg₂ (· && ·) rfl ?_) ?_
    · refine List.all_congr rfl fun c => by grind
    · refine List.all_congr rfl fun c₁ => List.all_congr rfl fun c₂ => by grind
  rw [h]
  open scoped LinearInequality in
  have hcoeffs_of : ∀ {α : Type} {encIn : α ↪ List Bool} {f : α → LinearInequality},
      ComputableInPolyTime f encIn encLinearInequality →
      ComputableInPolyTime (fun x => (f x).coeffs) encIn (encList encIntBin) := fun hf => by
    fun_prop
  have hbound_of : ∀ {α : Type} {encIn : α ↪ List Bool} {f : α → LinearInequality},
      ComputableInPolyTime f encIn encLinearInequality →
      ComputableInPolyTime (fun x => (f x).bound) encIn encIntBin := fun hf => by
    fun_prop
  have h1 : ComputableInPolyTime
      (fun C : List LinearInequality => C.all fun c => decide (c.coeffs.length ≤ 1))
      LPFeasibility.encSystem encBool := by
    apply allWithInput id'
    exact unary_le' ((length_list encIntBin).comp (hcoeffs_of (snd _ _))) (const 1)
  have h2 : ComputableInPolyTime
      (fun C : List LinearInequality =>
        C.all fun c => !decide (c.coeffs.getD 0 0 = 0) || decide (0 ≤ c.bound))
      LPFeasibility.encSystem encBool := by
    apply allWithInput id'
    have hc0 : ComputableInPolyTime
        (fun p : List LinearInequality × LinearInequality => p.2.coeffs.getD 0 0)
        (encPair LPFeasibility.encSystem encLinearInequality) encIntBin :=
      (listGetD (0 : ℤ)).comp ((hcoeffs_of (snd _ _)).prod (const 0))
    have hb : ComputableInPolyTime
        (fun p : List LinearInequality × LinearInequality => p.2.bound)
        (encPair LPFeasibility.encSystem encLinearInequality) encIntBin :=
      hbound_of (snd _ _)
    exact bool_or' (bool_not.comp (intBin_isZero.comp hc0)) (intBin_le' (const 0) hb)
  have h3 : ComputableInPolyTime
      (fun C : List LinearInequality =>
        C.all fun c₁ => C.all fun c₂ =>
          !(decide (c₁.coeffs.getD 0 0 < 0) && decide (0 < c₂.coeffs.getD 0 0)) ||
          decide (0 ≤ c₂.coeffs.getD 0 0 * c₁.bound - c₁.coeffs.getD 0 0 * c₂.bound))
      LPFeasibility.encSystem encBool := by
    apply allWithInput id'
    apply allWithInput (fst LPFeasibility.encSystem encLinearInequality)
    let encP := encPair LPFeasibility.encSystem encLinearInequality
    let encQ := encPair encP encLinearInequality
    have ha1 : ComputableInPolyTime
        (fun q : (List LinearInequality × LinearInequality) × LinearInequality =>
          q.1.2.coeffs.getD 0 0) encQ encIntBin :=
      (listGetD (0 : ℤ)).comp
        ((hcoeffs_of ((snd LPFeasibility.encSystem encLinearInequality).comp
          (fst encP encLinearInequality))).prod (const 0))
    have hb1 : ComputableInPolyTime
        (fun q : (List LinearInequality × LinearInequality) × LinearInequality => q.1.2.bound)
        encQ encIntBin :=
      hbound_of ((snd LPFeasibility.encSystem encLinearInequality).comp
        (fst encP encLinearInequality))
    have ha2 : ComputableInPolyTime
        (fun q : (List LinearInequality × LinearInequality) × LinearInequality =>
          q.2.coeffs.getD 0 0) encQ encIntBin :=
      (listGetD (0 : ℤ)).comp ((hcoeffs_of (snd encP encLinearInequality)).prod (const 0))
    have hb2 : ComputableInPolyTime
        (fun q : (List LinearInequality × LinearInequality) × LinearInequality => q.2.bound)
        encQ encIntBin :=
      hbound_of (snd encP encLinearInequality)
    exact bool_or'
      (bool_not.comp (bool_and' (intBin_lt' ha1 (const 0)) (intBin_lt' (const 0) ha2)))
      (intBin_le' (const 0) (intBin_sub' (intBin_mul' ha2 hb1) (intBin_mul' ha1 hb2)))
  exact bool_and' (bool_and' h1 h2) h3

end Cslib.Complexity
