/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ExistsReal
public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
public import CslibFrontier.Logics.RealArithmetic.Basic
public import CslibFrontier.Logics.RealArithmetic.Encoding
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.RankPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Membership of `ARM(k)` in `∃ℝ`

Polynomial-time many-one reductions proving `ARM(k) ∈ ∃ℝ` for every fixed rank bound `k : ℕ`
via rank-`k` factorization, plus an independent determinantal proof of `ARM(3) ∈ ∃ℝ` via
vanishing `4 × 4` minors.
-/

public section

namespace Cslib.Complexity

open Matrix Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Prefix-Token Builders for `Term` and `Formula` -/

/-- Conjunction of `eqZero t` over a list of terms (empty list maps to `0 = 0`). -/
@[expose] def andEqZeroFormula {n : ℕ} : List (Term n) → Formula n
  | [] => .eqZero (.const 0)
  | t :: ts => .and (.eqZero t) (andEqZeroFormula ts)

/-- A real vector lies in the solution set of `andEqZeroFormula ts` iff every term vanishes. -/
theorem mem_solutionSet_andEqZeroFormula {n : ℕ} (ts : List (Term n)) (x : Fin n → ℝ) :
    x ∈ (andEqZeroFormula ts).solutionSet ↔ ∀ t ∈ ts, t.eval x = 0 := by
  induction ts with
  | nil => simp [andEqZeroFormula, Formula.solutionSet, Term.eval]
  | cons t ts ih =>
    simp [andEqZeroFormula, Formula.solutionSet, ih]

/-- Sum of a list of terms (empty list maps to `0`). -/
@[expose] def sumTerms {n : ℕ} : List (Term n) → Term n
  | [] => .const 0
  | t :: ts => .add t (sumTerms ts)

/-- Evaluation of `sumTerms` equals the sum of term evaluations. -/
theorem eval_sumTerms {n : ℕ} (ts : List (Term n)) (x : Fin n → ℝ) :
    (sumTerms ts).eval x = (ts.map (Term.eval x)).sum := by
  induction ts with
  | nil => simp [sumTerms, Term.eval]
  | cons t ts ih => simp [sumTerms, Term.eval, ih]

/-- Prefix tokens of a constant term. -/
@[expose] def constTermTokens (z : ℤ) : List TermToken := [.inl z]

/-- Prefix tokens of a variable term. -/
@[expose] def varTermTokens (i : ℕ) : List TermToken := [.inr (.inl i)]

/-- Prefix tokens of an addition term. -/
@[expose] def addTermTokens (a b : List TermToken) : List TermToken :=
  .inr (.inr (.inl ())) :: (a ++ b)

/-- Prefix tokens of a multiplication term. -/
@[expose] def mulTermTokens (a b : List TermToken) : List TermToken :=
  .inr (.inr (.inr ())) :: (a ++ b)

/-- Prefix tokens of `sumTerms`. -/
@[expose] def sumTermTokens (ts : List (List TermToken)) : List TermToken :=
  (ts.map (fun tok ↦ .inr (.inr (.inl ())) :: tok)).flatten ++ [.inl 0]

/-- Prefix tokens of `andEqZeroFormula` given the encoded term words. -/
@[expose] def andEqZeroFormulaTokens (ws : List (List Bool)) : List FormulaToken :=
  (ws.map (fun w ↦ [.inr (.inr (.inr (.inr (.inl ())))), .inr (.inl w)])).flatten ++
    [.inr (.inl (encTerm 0 (.const 0)))]

private theorem encTerm_eq_encList {n : ℕ} (t : Term n) :
    encTerm n t = encList encTermToken ((encTerm_tokens n t).map TermToken.ofFin) := by
  rw [encTerm_apply]
  change (encTerm_tokens n t).flatMap (frame ∘ encTermTokenEncoding n) =
    ((encTerm_tokens n t).map TermToken.ofFin).flatMap (frame ∘ encTermToken)
  rw [List.flatMap_map]
  congr 1
  funext tok
  rcases tok with z | i | _ | _ <;>
    simp [TermToken.ofFin, encTermToken, encTermTokenEncoding,
      Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin.fin]

private theorem encTerm_sumTerms {n : ℕ} (ts : List (Term n)) :
    encTerm n (sumTerms ts) =
      encList encTermToken
        (sumTermTokens (ts.map fun t ↦ (encTerm_tokens n t).map TermToken.ofFin)) := by
  rw [encTerm_eq_encList]
  congr 1
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [sumTerms, encTerm_tokens, List.map_cons, List.map_append, sumTermTokens,
      List.flatten_cons, List.cons_append, List.append_assoc] at ih ⊢
    rw [ih]
    simp [TermToken.ofFin]

private theorem encFormula_andEqZeroFormula {n : ℕ} (ts : List (Term n)) :
    encFormula n (andEqZeroFormula ts) =
      encList encFormulaToken (andEqZeroFormulaTokens (ts.map (encTerm n))) := by
  rw [encFormula_apply]
  have hzero : encTerm n (.const 0) = encTerm 0 (.const 0) := by
    rw [encTerm_eq_encList, encTerm_eq_encList]; rfl
  change (encFormula_tokens n (andEqZeroFormula ts)).flatMap
      (frame ∘ encFormulaTokenEncoding n) =
    (andEqZeroFormulaTokens (ts.map (encTerm n))).flatMap (frame ∘ encFormulaToken)
  have htok : (encFormula_tokens n (andEqZeroFormula ts)).map FormulaToken.encodeTerms =
      andEqZeroFormulaTokens (ts.map (encTerm n)) := by
    induction ts with
    | nil =>
      simp [andEqZeroFormula, encFormula_tokens, FormulaToken.encodeTerms,
        andEqZeroFormulaTokens, hzero]
    | cons t ts ih =>
      simp only [andEqZeroFormula, encFormula_tokens, List.map_cons, List.map_append,
        FormulaToken.encodeTerms, Sum.map_inr, Sum.map_inl, id_eq, andEqZeroFormulaTokens,
        List.flatten_cons, List.cons_append] at ih ⊢
      rw [ih]
      simp
  rw [← htok, List.flatMap_map]
  congr 1
  funext tok
  rcases tok with _ | _ | _ | _ | _ | _ <;>
    simp [FormulaToken.encodeTerms, encFormulaToken, encFormulaTokenEncoding]

/-! ### Denominator Clearing for Rational Affine Constraints -/

/-- Product of all denominators in a rational affine constraint `(rows, b)`. -/
@[expose] def constraintDenomProd (c : List (List ℚ) × ℚ) : ℕ :=
  c.2.den * (c.1.map (fun row ↦ row.map Rat.den)).flatten.prod

/-- Denominator product is always strictly positive. -/
theorem constraintDenomProd_pos (c : List (List ℚ) × ℚ) : 0 < constraintDenomProd c := by
  unfold constraintDenomProd
  refine Nat.mul_pos c.2.pos (List.prod_pos fun d hd ↦ ?_)
  obtain ⟨r, hr, hdr⟩ := List.mem_flatten.mp hd
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hr
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hdr
  exact q.pos

/-- Every denominator in a constraint matrix divides `constraintDenomProd c`. -/
theorem den_dvd_constraintDenomProd {c : List (List ℚ) × ℚ} {row : List ℚ} {q : ℚ}
    (hrow : row ∈ c.1) (hq : q ∈ row) :
    q.den ∣ constraintDenomProd c := by
  unfold constraintDenomProd
  refine dvd_mul_of_dvd_right ?_ _
  refine List.dvd_prod ?_
  exact List.mem_flatten.mpr ⟨row.map Rat.den, List.mem_map.mpr ⟨row, hrow, rfl⟩,
    List.mem_map.mpr ⟨q, hq, rfl⟩⟩

/-- Scaling a rational `q` by a multiple `D` of `q.den` yields an exact integer cast. -/
theorem rat_mul_denom_div_eq (q : ℚ) {D : ℕ} (hdvd : q.den ∣ D) :
    ((q.num * ((D / q.den : ℕ) : ℤ) : ℤ) : ℝ) = (D : ℝ) * (q : ℝ) := by
  have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hD : (D : ℝ) = ((D / q.den : ℕ) : ℝ) * (q.den : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  rw [hq, hD, Int.cast_mul, Int.cast_natCast, mul_assoc, mul_div_cancel₀ _ hden, mul_comm]

/-- Exact integer numerator for entry `(i, j)` of constraint `c` after clearing denominators. -/
@[expose] def clearedCoeff (c : List (List ℚ) × ℚ) (i j : ℕ) : ℤ :=
  let D := constraintDenomProd c
  let a := (c.1.getD i []).getD j 0
  a.num * ((D / a.den : ℕ) : ℤ)

/-- Exact negated integer right-hand side of constraint `c` after clearing denominators. -/
@[expose] def clearedNegRhs (c : List (List ℚ) × ℚ) : ℤ :=
  let D := constraintDenomProd c;
  -(c.2.num * ((D / c.2.den : ℕ) : ℤ))

/-- Cleared entry coefficient cast to `ℝ` equals `D * A_{ij}` for in-bounds `(i, j)`. -/
theorem clearedCoeff_cast {inst : ARMInstance} {c : List (List ℚ) × ℚ} (hc : c ∈ inst.constraints)
    (i : Fin inst.rows) (j : Fin inst.cols) :
    ((clearedCoeff c i.1 j.1 : ℤ) : ℝ) =
      (constraintDenomProd c : ℝ) * ((inst.matrixAt c i j : ℚ) : ℝ) := by
  obtain ⟨hrows, hcols⟩ := inst.dims_ok c hc
  have hi : i.1 < c.1.length := hrows.symm ▸ i.2
  have hrow_mem : c.1[i.1] ∈ c.1 := List.getElem_mem hi
  have hj : j.1 < c.1[i.1].length := (hcols _ hrow_mem).symm ▸ j.2
  have hq_mem : c.1[i.1][j.1] ∈ c.1[i.1] := List.getElem_mem hj
  have hget : (c.1.getD i.1 []).getD j.1 0 = c.1[i.1][j.1] := by
    simp [List.getD_eq_getElem?_getD, hi, hj]
  have hmat : inst.matrixAt c i j = c.1[i.1][j.1] := by
    simpa using hget
  rw [hmat, clearedCoeff, hget]
  exact rat_mul_denom_div_eq _ (den_dvd_constraintDenomProd hrow_mem hq_mem)

/-- Cleared negated RHS cast to `ℝ` equals `-D * b`. -/
theorem clearedNegRhs_cast (c : List (List ℚ) × ℚ) :
    ((clearedNegRhs c : ℤ) : ℝ) = -((constraintDenomProd c : ℝ) * (c.2 : ℝ)) := by
  have hdvd : c.2.den ∣ constraintDenomProd c := dvd_mul_right c.2.den _
  simp only [clearedNegRhs, Int.cast_neg]
  rw [rat_mul_denom_div_eq c.2 hdvd]

/-! ### Polynomial-Time Reduction `ARM(k) ≤ₚ ETR` via Rank Factorization -/

/-- Exact `Term` encoding one cleared affine constraint `⟨A, U * V⟩ - b = 0` for `U ∈ ℝ^{m×k}`,
`V ∈ ℝ^{k×n}`. Variable `U_{it}` is at `i * k + t`, and `V_{tj}` is at `m * k + t * n + j`. -/
@[expose] def factorConstraintTerm (m n k : ℕ) (c : List (List ℚ) × ℚ) :
    Term (m * k + k * n) :=
  let entries : List (Term (m * k + k * n)) :=
    (List.range m).flatMap fun i ↦
      (List.range n).flatMap fun j ↦
        (List.range k).map fun t ↦
          if hU : i * k + t < m * k + k * n then
            if hV : m * k + t * n + j < m * k + k * n then
              .mul (.const (clearedCoeff c i j))
                (.mul (.var ⟨i * k + t, hU⟩) (.var ⟨m * k + t * n + j, hV⟩))
            else .const 0
          else .const 0
  .add (sumTerms entries) (.const (clearedNegRhs c))

/-- Token-level computation of `factorConstraintTerm` (identical encoding, directly `PolyTime`). -/
@[expose] def factorConstraintTermTokens (m n k : ℕ) (c : List (List ℚ) × ℚ) : List TermToken :=
  let entries : List (List TermToken) :=
    (List.range m).flatMap fun i ↦
      (List.range n).flatMap fun j ↦
        (List.range k).map fun t ↦
          mulTermTokens (constTermTokens (clearedCoeff c i j))
            (mulTermTokens (varTermTokens (i * k + t)) (varTermTokens (m * k + t * n + j)))
  addTermTokens (sumTermTokens entries) (constTermTokens (clearedNegRhs c))

private theorem list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).sum = (l.map fun x ↦ (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem list_sum_map_range {m : ℕ} (f : ℕ → ℝ) :
    ((List.range m).map f).sum = ∑ i : Fin m, f i.1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih, Fin.sum_univ_castSucc]
    rfl

private theorem encTerm_factorConstraintTerm (m n k : ℕ) (c : List (List ℚ) × ℚ) :
    encTerm (m * k + k * n) (factorConstraintTerm m n k c) =
      encList encTermToken (factorConstraintTermTokens m n k c) := by
  rw [encTerm_eq_encList]
  congr 1
  have h1 := encTerm_sumTerms (n := m * k + k * n)
    ((List.range m).flatMap fun i ↦ (List.range n).flatMap fun j ↦
      (List.range k).map fun t ↦
        if hU : i * k + t < m * k + k * n then
          if hV : m * k + t * n + j < m * k + k * n then
            .mul (.const (clearedCoeff c i j))
              (.mul (.var ⟨i * k + t, hU⟩) (.var ⟨m * k + t * n + j, hV⟩))
          else .const 0
        else .const 0)
  rw [encTerm_eq_encList] at h1
  have hsum := (encList encTermToken).injective h1
  simp only [factorConstraintTerm, encTerm_tokens, List.map_cons, List.map_append]
  rw [hsum]
  simp only [TermToken.ofFin, Sum.map_inl, Sum.map_inr, id_eq, factorConstraintTermTokens,
    addTermTokens, constTermTokens]
  congr 1
  congr 1
  congr 1
  simp only [List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun i hi ↦ ?_
  rw [List.mem_range] at hi
  refine List.flatMap_congr fun j hj ↦ ?_
  rw [List.mem_range] at hj
  refine List.map_congr_left fun t ht ↦ ?_
  rw [List.mem_range] at ht
  have hU : i * k + t < m * k + k * n := by
    have : i * k + t < m * k := by nlinarith
    omega
  have hV : m * k + t * n + j < m * k + k * n := by
    have : t * n + j < k * n := by nlinarith
    omega
  simp [hU, hV, encTerm_tokens, mulTermTokens, varTermTokens]

/-- Unpack a flat real vector `y : Fin (m * k + k * n) → ℝ` into `U ∈ ℝ^{m×k}` and `V ∈ ℝ^{k×n}`. -/
@[expose] def unpackU {m n k : ℕ} (y : Fin (m * k + k * n) → ℝ) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun i t ↦ y ⟨i.1 * k + t.1, by
    have : i.1 * k + t.1 < m * k := by nlinarith [i.2, t.2]
    omega⟩

/-- Unpack the second factor `V ∈ ℝ^{k×n}` from `y : Fin (m * k + k * n) → ℝ`. -/
@[expose] def unpackV {m n k : ℕ} (y : Fin (m * k + k * n) → ℝ) : Matrix (Fin k) (Fin n) ℝ :=
  Matrix.of fun t j ↦ y ⟨m * k + t.1 * n + j.1, by
    have : t.1 * n + j.1 < k * n := by nlinarith [t.2, j.2]
    omega⟩

/-- Pack `(U, V)` into a flat real vector `y : Fin (m * k + k * n) → ℝ`. -/
@[expose] def packUV {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ) :
    Fin (m * k + k * n) → ℝ := fun idx ↦
  if h : idx.1 < m * k then
    if hk : 0 < k then
      U ⟨idx.1 / k, Nat.div_lt_of_lt_mul (by nlinarith)⟩ ⟨idx.1 % k, Nat.mod_lt _ hk⟩
    else 0
  else
    if hn : 0 < n then
      V ⟨(idx.1 - m * k) / n, Nat.div_lt_of_lt_mul (by
          have h2 := idx.2; have h1 : idx.1 - m * k < k * n := by omega
          nlinarith)⟩
        ⟨(idx.1 - m * k) % n, Nat.mod_lt _ hn⟩
    else 0

private theorem unpackU_packUV {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin k) (Fin n) ℝ) : unpackU (packUV U V) = U := by
  ext i t
  have hk : 0 < k := Nat.zero_lt_of_lt t.2
  have hlt : i.1 * k + t.1 < m * k := by nlinarith [i.2, t.2]
  have hdiv : (i.1 * k + t.1) / k = i.1 := by
    rw [Nat.mul_comm i.1 k, Nat.mul_add_div hk, Nat.div_eq_of_lt t.2, Nat.add_zero]
  simp [unpackU, packUV, hlt, hk, hdiv, Nat.mod_eq_of_lt t.2]

private theorem unpackV_packUV {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin k) (Fin n) ℝ) : unpackV (packUV U V) = V := by
  ext t j
  have hn : 0 < n := Nat.zero_lt_of_lt j.2
  have hge : ¬ (m * k + t.1 * n + j.1 < m * k) := by omega
  have hsub : m * k + t.1 * n + j.1 - m * k = t.1 * n + j.1 := by omega
  have hdiv : (t.1 * n + j.1) / n = t.1 := by
    rw [Nat.mul_comm t.1 n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.2, Nat.add_zero]
  have hmod : (t.1 * n + j.1) % n = j.1 := by
    rw [Nat.mul_comm t.1 n, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
  simp [unpackV, packUV, hge, hn, hsub, hdiv, hmod]

private theorem eval_factorConstraintTerm {inst : ARMInstance} {c : List (List ℚ) × ℚ}
    (hc : c ∈ inst.constraints) (k : ℕ) (y : Fin (inst.rows * k + k * inst.cols) → ℝ) :
    (factorConstraintTerm inst.rows inst.cols k c).eval y =
      (constraintDenomProd c : ℝ) *
        (frobeniusInner ((inst.matrixAt c).map ((↑) : ℚ → ℝ)) (unpackU y * unpackV y) -
          (c.2 : ℝ)) := by
  let m := inst.rows
  let n := inst.cols
  simp only [factorConstraintTerm, Term.eval, eval_sumTerms, clearedNegRhs_cast]
  have hsum :
      (List.map (Term.eval y) ((List.range m).flatMap fun i ↦
        (List.range n).flatMap fun j ↦
          (List.range k).map fun t ↦
            if hU : i * k + t < m * k + k * n then
              if hV : m * k + t * n + j < m * k + k * n then
                .mul (.const (clearedCoeff c i j))
                  (.mul (.var ⟨i * k + t, hU⟩) (.var ⟨m * k + t * n + j, hV⟩))
              else .const 0
            else .const 0)).sum =
      (constraintDenomProd c : ℝ) *
        frobeniusInner ((inst.matrixAt c).map ((↑) : ℚ → ℝ)) (unpackU y * unpackV y) := by
    simp only [List.map_flatMap, list_sum_flatMap, List.map_map, frobeniusInner_eq_sum,
      Matrix.map_apply, Matrix.mul_apply, Finset.mul_sum]
    rw [list_sum_map_range]
    apply Finset.sum_congr rfl; intro i _
    rw [list_sum_map_range]
    apply Finset.sum_congr rfl; intro j _
    rw [list_sum_map_range]
    apply Finset.sum_congr rfl; intro t _
    have hU : i.1 * k + t.1 < m * k + k * n := by
      have : i.1 * k + t.1 < m * k := by nlinarith [i.2, t.2]
      omega
    have hV : m * k + t.1 * n + j.1 < m * k + k * n := by
      have : t.1 * n + j.1 < k * n := by nlinarith [t.2, j.2]
      omega
    simp only [Function.comp_apply, hU, hV, ↓reduceDIte, Term.eval, clearedCoeff_cast hc i j,
      unpackU, unpackV, Matrix.of_apply]
    ring
  rw [hsum]
  ring

/-- **Polynomial-time reduction `armToETR k`** from `ARM(k)` to `ETR` via rank-`k` factorization. -/
@[expose] def armToETR (k : ℕ) (inst : ARMInstance) : List Bool :=
  if inst.constraints.isEmpty then
    encFormula 0 (.eqZero (.const 0))
  else
    let firstMat := (inst.constraints.headD ([], 0)).1
    let m := firstMat.length
    let n := (firstMat.headD []).length
    if m == 0 || n == 0 then
      if inst.constraints.all (fun c ↦ decide (c.2 = 0)) then
        encFormula 0 (.eqZero (.const 0))
      else
        encFormula 0 .false
    else
      encList encFormulaToken
        (andEqZeroFormulaTokens
          (inst.constraints.map fun c ↦
            encList encTermToken (factorConstraintTermTokens m n k c)))

private theorem arm_zero_dim_iff {k : ℕ} {inst : ARMInstance}
    (hdim : inst.rows = 0 ∨ inst.cols = 0) :
    inst ∈ ARM k ↔ ∀ c ∈ inst.constraints, c.2 = 0 := by
  constructor
  · rintro ⟨X, hsat, _⟩ c hc
    have h := hsat c hc
    have h0 : frobeniusInner ((inst.matrixAt c).map ((↑) : ℚ → ℝ)) X = 0 := by
      rcases hdim with h0 | h0 <;> simp [frobeniusInner_eq_sum, h0]
    rw [h0] at h
    exact_mod_cast h.symm
  · intro hall
    refine ⟨0, fun c hc ↦ ?_, by simp⟩
    rcases hdim with h0 | h0 <;> simp [frobeniusInner_eq_sum, h0, hall c hc]

private theorem etr_zero_dim_iff (inst : ARMInstance) :
    (∀ c ∈ inst.constraints, c.2 = 0) ↔
      (if inst.constraints.all (fun c ↦ decide (c.2 = 0)) then
        encFormula 0 (.eqZero (.const 0)) else encFormula 0 .false) ∈ ETR := by
  by_cases hall : inst.constraints.all (fun c ↦ decide (c.2 = 0)) = true
  · simp only [hall, ↓reduceIte, encFormula_mem_ETR]
    exact iff_of_true (fun c hc ↦ of_decide_eq_true (List.all_eq_true.mp hall c hc))
      ⟨Fin.elim0, by simp [Formula.solutionSet, Term.eval]⟩
  · simp only [hall, Bool.false_eq_true, ↓reduceIte, encFormula_mem_ETR, Formula.solutionSet,
      Set.not_nonempty_empty]
    exact iff_of_false (fun h ↦ hall (List.all_eq_true.mpr fun c hc ↦ decide_eq_true (h c hc))) id

/-- Equisatisfiability of `armToETR k`: `inst ∈ ARM k ↔ armToETR k inst ∈ ETR`. -/
theorem armToETR_mem_iff (k : ℕ) (inst : ARMInstance) :
    inst ∈ ARM k ↔ armToETR k inst ∈ ETR := by
  by_cases hemp : inst.constraints.isEmpty = true
  · have hnil : inst.constraints = [] := List.isEmpty_iff.mp hemp
    have hfeas : inst ∈ ARM k := ⟨0, fun c hc ↦ by simp [hnil] at hc, by simp⟩
    have hetr : armToETR k inst ∈ ETR := by
      simp only [armToETR, hemp, ↓reduceIte, encFormula_mem_ETR]
      exact ⟨Fin.elim0, by simp [Formula.solutionSet, Term.eval]⟩
    exact iff_of_true hfeas hetr
  · have hne : inst.constraints ≠ [] := fun h ↦ hemp (by simp [h])
    have hhead_mem : inst.constraints.headD ([], 0) ∈ inst.constraints := by
      cases h : inst.constraints with
      | nil => exact absurd h hne
      | cons c cs => simp [List.headD]
    have hm_eq : (inst.constraints.headD ([], 0)).1.length = inst.rows :=
      (inst.dims_ok _ hhead_mem).1
    by_cases hm0 : inst.rows = 0
    · have hcond : ((inst.constraints.headD ([], 0)).1.length == 0 ||
          ((inst.constraints.headD ([], 0)).1.headD []).length == 0) = true := by
        rw [hm_eq, hm0]; simp
      rw [arm_zero_dim_iff (Or.inl hm0), etr_zero_dim_iff]
      simp only [armToETR, hemp, Bool.false_eq_true, ↓reduceIte, hcond]
    · have hrow_ne : (inst.constraints.headD ([], 0)).1 ≠ [] := fun h ↦
        hm0 (by rw [← hm_eq, h]; rfl)
      have hrow_mem : (inst.constraints.headD ([], 0)).1.headD [] ∈
          (inst.constraints.headD ([], 0)).1 := by
        cases h : (inst.constraints.headD ([], 0)).1 with
        | nil => exact absurd h hrow_ne
        | cons r rs => simp [List.headD]
      have hn_eq : ((inst.constraints.headD ([], 0)).1.headD []).length = inst.cols :=
        (inst.dims_ok _ hhead_mem).2 _ hrow_mem
      by_cases hn0 : inst.cols = 0
      · have hcond : ((inst.constraints.headD ([], 0)).1.length == 0 ||
            ((inst.constraints.headD ([], 0)).1.headD []).length == 0) = true := by
          rw [hn_eq, hn0]; simp
        rw [arm_zero_dim_iff (Or.inr hn0), etr_zero_dim_iff]
        simp only [armToETR, hemp, Bool.false_eq_true, ↓reduceIte, hcond]
      · have hform : armToETR k inst =
            encFormula (inst.rows * k + k * inst.cols)
              (andEqZeroFormula (inst.constraints.map
                (factorConstraintTerm inst.rows inst.cols k))) := by
          dsimp [armToETR]
          simp only [hemp, Bool.false_eq_true, ↓reduceIte, hm_eq, hn_eq]
          rw [show (inst.rows == 0 || inst.cols == 0) = false by simp [hm0, hn0]]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [encFormula_andEqZeroFormula, List.map_map]
          congr 1; congr 1
          exact List.map_congr_left fun c _ ↦ (encTerm_factorConstraintTerm _ _ k c).symm
        rw [hform, encFormula_mem_ETR]
        constructor
        · rintro ⟨X, hsat, hrank⟩
          obtain ⟨U, V, rfl⟩ := (rank_factorization_equiv X k).mp hrank
          refine ⟨packUV U V, (mem_solutionSet_andEqZeroFormula _ _).mpr ?_⟩
          intro t ht
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          rw [eval_factorConstraintTerm hc, unpackU_packUV, unpackV_packUV, hsat c hc, sub_self,
            mul_zero]
        · rintro ⟨y, hy⟩
          rw [mem_solutionSet_andEqZeroFormula] at hy
          refine ⟨unpackU y * unpackV y, fun c hc ↦ ?_,
            (rank_factorization_equiv _ k).mpr ⟨unpackU y, unpackV y, rfl⟩⟩
          have h0 := hy _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
          rw [eval_factorConstraintTerm hc] at h0
          have hD : (constraintDenomProd c : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (constraintDenomProd_pos c).ne'
          exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hD)

/-- `constraintDenomProd` is computable in polynomial time. -/
theorem constraintDenomProd_polyTime :
    ComputableInPolyTime constraintDenomProd
      (encPair (encList (encList encRat)) encRat) encNat := by
  have h1 : ComputableInPolyTime
      (fun p : List (List ℚ) × ℚ ↦ p.1.map (fun row ↦ row.map Rat.den))
      (encPair (encList (encList encRat)) encRat) (encList (encList encNat)) := by
    have hrow : ComputableInPolyTime (List.map Rat.den) (encList encRat) (encList encNat) :=
      map (encA := encRat) (encB := encNat) rat_den
    exact (map hrow).comp (fst _ _)
  have hprod : ComputableInPolyTime
      (fun p : List (List ℚ) × ℚ ↦ (p.1.map (fun row ↦ row.map Rat.den)).flatten.prod)
      (encPair (encList (encList encRat)) encRat) encNat :=
    binary_prod.comp ((flatten encNat).comp h1)
  have hden : ComputableInPolyTime (fun p : List (List ℚ) × ℚ ↦ p.2.den)
      (encPair (encList (encList encRat)) encRat) encNat :=
    rat_den.comp (snd _ _)
  exact binary_mul.comp (hden.prod hprod)

/-- `armToETR k` is computable in polynomial time for every fixed `k : ℕ`. -/
theorem armToETR_polyTime (k : ℕ) :
    ComputableInPolyTime (armToETR k) encARMInstance encBits := by
  let encC := encPair (encList (encList encRat)) encRat
  let encInst := encPair encNat (encPair encNat encARMConstraints)
  have htoPair : ComputableInPolyTime
      (fun inst : ARMInstance ↦ (inst.rows, inst.cols, inst.constraints))
      encARMInstance encInst :=
    (id' (encIn := encARMInstance)).of_enc_eq fun _ ↦ rfl
  have hcs : ComputableInPolyTime (fun inst : ARMInstance ↦ inst.constraints)
      encARMInstance (encList encC) :=
    (snd encNat encARMConstraints).comp ((snd encNat _).comp htoPair)
  have hemp : ComputableInPolyTime (fun inst : ARMInstance ↦ inst.constraints.isEmpty)
      encARMInstance encBool :=
    (listIsEmpty' encC).comp hcs
  have hfirst : ComputableInPolyTime
      (fun inst : ARMInstance ↦ (inst.constraints.headD ([], 0)).1)
      encARMInstance (encList (encList encRat)) :=
    (fst (encList (encList encRat)) encRat).comp ((headD (encA := encC) ([], 0)).comp hcs)
  have hm : ComputableInPolyTime
      (fun inst : ARMInstance ↦ (inst.constraints.headD ([], 0)).1.length)
      encARMInstance encUnary :=
    (length_list (encList encRat)).comp hfirst
  have hn : ComputableInPolyTime
      (fun inst : ARMInstance ↦ ((inst.constraints.headD ([], 0)).1.headD []).length)
      encARMInstance encUnary :=
    (length_list encRat).comp ((headD []).comp hfirst)
  have hzero : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        (inst.constraints.headD ([], 0)).1.length == 0 ||
          ((inst.constraints.headD ([], 0)).1.headD []).length == 0)
      encARMInstance encBool := by
    have hm0 : ComputableInPolyTime
        (fun inst : ARMInstance ↦ (inst.constraints.headD ([], 0)).1.length == 0)
        encARMInstance encBool :=
      (unary_beq hm (const 0)).of_enc_eq fun _ ↦ by simp
    have hn0 : ComputableInPolyTime
        (fun inst : ARMInstance ↦ ((inst.constraints.headD ([], 0)).1.headD []).length == 0)
        encARMInstance encBool :=
      (unary_beq hn (const 0)).of_enc_eq fun _ ↦ by simp
    exact bool_or' hm0 hn0
  have hall0 : ComputableInPolyTime
      (fun inst : ARMInstance ↦ inst.constraints.all (fun c ↦ decide (c.2 = 0)))
      encARMInstance encBool := by
    have htest : ComputableInPolyTime (fun c : List (List ℚ) × ℚ ↦ decide (c.2 = 0))
        encC encBool := by
      fun_prop
    exact allWith (htest.comp (snd encUnit encC)) (const ()) hcs
 -- Show the main branch computing the encoded formula word is `ComputableInPolyTime`.
  let encParam := encPair encUnary encUnary
  let encP := encPair encParam encC
  have hparam : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        ((inst.constraints.headD ([], 0)).1.length,
          ((inst.constraints.headD ([], 0)).1.headD []).length))
      encARMInstance encParam := hm.prod hn
 -- Compute one constraint's encoded term word from `((m, n), c)` in `PolyTime`.
  let encEntryPar := encPair encP encUnary
  let encEntryIJ := encPair encEntryPar encUnary
  have htermWord : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦
        encList encTermToken (factorConstraintTermTokens q.1.1 q.1.2 k q.2))
      encP encBits := by
    have hsingleEntry : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
          (List.range k).map fun t ↦
            mulTermTokens (constTermTokens (clearedCoeff s.1.1.2 s.1.2 s.2))
              (mulTermTokens (varTermTokens (s.1.2 * k + t))
                (varTermTokens (s.1.1.1.1 * k + t * s.1.1.1.2 + s.2))))
        encEntryIJ (encList (encList encTermToken)) := by
      refine mapConst (List.range k) fun t _ ↦ ?_
      have hc_at : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.1.2)
          encEntryIJ encC :=
        (snd encParam encC).comp ((fst encP encUnary).comp (fst encEntryPar encUnary))
      have hi_at : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.2)
          encEntryIJ encUnary :=
        (snd encP encUnary).comp (fst encEntryPar encUnary)
      have hj_at : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.2)
          encEntryIJ encUnary :=
        snd encEntryPar encUnary
      have hm_at : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.1.1.1)
          encEntryIJ encUnary :=
        (fst encUnary encUnary).comp
          ((fst encParam encC).comp ((fst encP encUnary).comp (fst encEntryPar encUnary)))
      have hn_at : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.1.1.2)
          encEntryIJ encUnary :=
        (snd encUnary encUnary).comp
          ((fst encParam encC).comp ((fst encP encUnary).comp (fst encEntryPar encUnary)))
      have hD : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ constraintDenomProd s.1.1.2)
          encEntryIJ encNat :=
        constraintDenomProd_polyTime.comp hc_at
      have ha : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            (s.1.1.2.1.getD s.1.2 []).getD s.2 0)
          encEntryIJ encRat :=
        listGetDWithInput (listGetDWithInput ((fst _ _).comp hc_at) hi_at []) hj_at 0
      have hcoeff : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            clearedCoeff s.1.1.2 s.1.2 s.2)
          encEntryIJ encIntBin := by
        have hq : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
              ((s.1.1.2.1.getD s.1.2 []).getD s.2 0).num *
                ((constraintDenomProd s.1.1.2 /
                  ((s.1.1.2.1.getD s.1.2 []).getD s.2 0).den : ℕ) : ℤ))
            encEntryIJ encIntBin :=
          intBin_mul' (rat_num.comp ha) (intBin_natCast.comp (binary_div' hD (rat_den.comp ha)))
        exact hq
      have hconstTok : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            constTermTokens (clearedCoeff s.1.1.2 s.1.2 s.2))
          encEntryIJ (encList encTermToken) :=
        (cons encTermToken).comp (((sumInl encIntBin _).comp hcoeff).prod (const []))
      have hvarU : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            varTermTokens (s.1.2 * k + t))
          encEntryIJ (encList encTermToken) := by
        have hidx : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.2 * k + t)
            encEntryIJ encUnary :=
          unary_add.comp ((unary_mul.comp (hi_at.prod (const k))).prod (const t))
        exact (cons encTermToken).comp
          (((sumInr encIntBin _).comp ((sumInl encUnary _).comp hidx)).prod (const []))
      have hvarV : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            varTermTokens (s.1.1.1.1 * k + t * s.1.1.1.2 + s.2))
          encEntryIJ (encList encTermToken) := by
        have hidx : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
              s.1.1.1.1 * k + t * s.1.1.1.2 + s.2)
            encEntryIJ encUnary :=
          unary_add.comp ((unary_add.comp
            ((unary_mul.comp (hm_at.prod (const k))).prod
              (unary_mul.comp ((const t).prod hn_at)))).prod hj_at)
        exact (cons encTermToken).comp
          (((sumInr encIntBin _).comp ((sumInl encUnary _).comp hidx)).prod (const []))
      have hmulUV : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            mulTermTokens (varTermTokens (s.1.2 * k + t))
              (varTermTokens (s.1.1.1.1 * k + t * s.1.1.1.2 + s.2)))
          encEntryIJ (encList encTermToken) :=
        (cons encTermToken).comp
          ((const (α := (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ)
            ((.inr (.inr (.inr ())) : TermToken))).prod
            ((listAppend encTermToken).comp (hvarU.prod hvarV)))
      exact (cons encTermToken).comp
        ((const (α := (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ)
          ((.inr (.inr (.inr ())) : TermToken))).prod
          ((listAppend encTermToken).comp (hconstTok.prod hmulUV)))
    have hrowEntries : ComputableInPolyTime
        (fun r : ((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ ↦
          (List.range r.1.1.2).flatMap fun j ↦
            (List.range k).map fun t ↦
              mulTermTokens (constTermTokens (clearedCoeff r.1.2 r.2 j))
                (mulTermTokens (varTermTokens (r.2 * k + t))
                  (varTermTokens (r.1.1.1 * k + t * r.1.1.2 + j))))
        encEntryPar (encList (encList encTermToken)) :=
      flatMapWith hsingleEntry id'
        (range.comp ((snd encUnary encUnary).comp ((fst encParam encC).comp (fst encP encUnary))))
    have hallEntries : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦
          (List.range q.1.1).flatMap fun i ↦
            (List.range q.1.2).flatMap fun j ↦
              (List.range k).map fun t ↦
                mulTermTokens (constTermTokens (clearedCoeff q.2 i j))
                  (mulTermTokens (varTermTokens (i * k + t))
                    (varTermTokens (q.1.1 * k + t * q.1.2 + j))))
        encP (encList (encList encTermToken)) :=
      flatMapWith hrowEntries id' (range.comp ((fst encUnary encUnary).comp (fst encParam encC)))
    have hsumTok : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦
          sumTermTokens ((List.range q.1.1).flatMap fun i ↦
            (List.range q.1.2).flatMap fun j ↦
              (List.range k).map fun t ↦
                mulTermTokens (constTermTokens (clearedCoeff q.2 i j))
                  (mulTermTokens (varTermTokens (i * k + t))
                    (varTermTokens (q.1.1 * k + t * q.1.2 + j)))))
        encP (encList encTermToken) := by
      have hmap : ComputableInPolyTime
          (fun l : List (List TermToken) ↦
            l.map (fun tok ↦ ((.inr (.inr (.inl ())) : TermToken) :: tok)))
          (encList (encList encTermToken)) (encList (encList encTermToken)) :=
        ComputableInPolyTime.map
          ((cons encTermToken).comp
            ((const (α := List TermToken) ((.inr (.inr (.inl ())) : TermToken))).prod id'))
      exact (listAppend encTermToken).comp
        (((flatten encTermToken).comp (hmap.comp hallEntries)).prod
          (const (α := (ℕ × ℕ) × (List (List ℚ) × ℚ)) ([.inl 0] : List TermToken)))
    have hrhsTok : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ constTermTokens (clearedNegRhs q.2))
        encP (encList encTermToken) := by
      have hc_q : ComputableInPolyTime (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ q.2) encP encC :=
        snd encParam encC
      have hD : ComputableInPolyTime
          (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ constraintDenomProd q.2) encP encNat :=
        constraintDenomProd_polyTime.comp hc_q
      have hb : ComputableInPolyTime
          (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ q.2.2) encP encRat :=
        (snd _ _).comp hc_q
      have hrhs : ComputableInPolyTime
          (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ clearedNegRhs q.2) encP encIntBin :=
        intBin_neg.comp (intBin_mul' (rat_num.comp hb)
          (intBin_natCast.comp (binary_div' hD (rat_den.comp hb))))
      exact (cons encTermToken).comp (((sumInl encIntBin _).comp hrhs).prod (const []))
    have hfullTok : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ factorConstraintTermTokens q.1.1 q.1.2 k q.2)
        encP (encList encTermToken) :=
      (cons encTermToken).comp
        ((const (α := (ℕ × ℕ) × (List (List ℚ) × ℚ)) ((.inr (.inr (.inl ())) : TermToken))).prod
          ((listAppend encTermToken).comp (hsumTok.prod hrhsTok)))
    exact hfullTok.of_enc_eq fun _ ↦ rfl
  have hmapped : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        inst.constraints.map fun c ↦
          encList encTermToken
            (factorConstraintTermTokens
              (inst.constraints.headD ([], 0)).1.length
              ((inst.constraints.headD ([], 0)).1.headD []).length k c))
      encARMInstance (encList encBits) :=
    (mapWith htermWord hparam hcs).of_enc_eq fun _ ↦ rfl
  have htoks : ComputableInPolyTime
      (fun ws : List (List Bool) ↦ andEqZeroFormulaTokens ws)
      (encList encBits) (encList encFormulaToken) := by
    have hpair : ComputableInPolyTime
        (fun w : List Bool ↦ ([.inr (.inr (.inr (.inr (.inl ())))),
          .inr (.inl w)] : List FormulaToken))
        encBits (encList encFormulaToken) :=
      (cons encFormulaToken).comp
        ((const (α := List Bool) ((.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken))).prod
          ((cons encFormulaToken).comp
            (((sumInr encUnit _).comp ((sumInl encBits _).comp id')).prod (const []))))
    exact (listAppend encFormulaToken).comp
      (((flatten encFormulaToken).comp ((ComputableInPolyTime.map hpair).comp id')).prod
        (const (α := List (List Bool)) ([.inr (.inl (encTerm 0 (.const 0)))] : List FormulaToken)))
  have hmain : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        encList encFormulaToken
          (andEqZeroFormulaTokens
            (inst.constraints.map fun c ↦
              encList encTermToken
                (factorConstraintTermTokens
                  (inst.constraints.headD ([], 0)).1.length
                  ((inst.constraints.headD ([], 0)).1.headD []).length k c))))
      encARMInstance encBits :=
    (htoks.comp hmapped).of_enc_eq fun _ ↦ rfl
  exact (hemp.ite' (const (encFormula 0 (.eqZero (.const 0))))
    (hzero.ite'
      (hall0.ite' (const (encFormula 0 (.eqZero (.const 0)))) (const (encFormula 0 .false)))
      hmain))

/-- and for every fixed `k : ℕ` (in particular every `k ≥
 1`), `ARM(k) ∈ ∃ℝ` (`Cslib.Complexity.ExistsReal`). -/
theorem arm_mem_existsReal (k : ℕ) :
    ARM k ∈ ExistsReal encARMInstance :=
  ⟨armToETR k, armToETR_polyTime k, armToETR_mem_iff k⟩

/-! ### Determinantal Proof of `ARM(3) ∈ ∃ℝ` via Vanishing `4 × 4` Minors -/

/-- The 24 permutations of `Fin 4` paired with their signs `(sgn, σ(0), σ(1), σ(2), σ(3))`
for the explicit Leibniz determinant formula (). -/
@[expose] noncomputable def perms4 : List (ℤ × Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
  (Finset.univ : Finset (Equiv.Perm (Fin 4))).toList.map fun σ ↦
    ((Equiv.Perm.sign σ : ℤ), σ 0, σ 1, σ 2, σ 3)

/-- Sum of `perms4` agrees with the `4 × 4` matrix determinant. -/
theorem sum_perms4_eq_det (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (perms4.map fun p ↦
      (p.1 : ℝ) * (M p.2.1 0 * (M p.2.2.1 1 * (M p.2.2.2.1 2 * M p.2.2.2.2 3)))).sum =
      M.det := by
  rw [Matrix.det_apply]
  unfold perms4
  rw [List.map_map]
  have hsum : (List.map (fun σ : Equiv.Perm (Fin 4) ↦
      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (M (σ 0) 0 * (M (σ 1) 1 * (M (σ 2) 2 * M (σ 3) 3))))
      (Finset.univ : Finset (Equiv.Perm (Fin 4))).toList).sum =
      ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (M (σ 0) 0 * (M (σ 1) 1 * (M (σ 2) 2 * M (σ 3) 3))) := by
    rw [Finset.sum_eq_multiset_sum]
    simp
  have hfn : (fun p : ℤ × Fin 4 × Fin 4 × Fin 4 × Fin 4 ↦
      (p.1 : ℝ) * (M p.2.1 0 * (M p.2.2.1 1 * (M p.2.2.2.1 2 * M p.2.2.2.2 3)))) ∘
      (fun σ : Equiv.Perm (Fin 4) ↦ ((Equiv.Perm.sign σ : ℤ), σ 0, σ 1, σ 2, σ 3)) =
      fun σ : Equiv.Perm (Fin 4) ↦ ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (M (σ 0) 0 * (M (σ 1) 1 * (M (σ 2) 2 * M (σ 3) 3))) := rfl
  rw [hfn, hsum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Fin.prod_univ_four, Units.smul_def, zsmul_eq_mul]
  ring

/-- `Term` encoding the `4 × 4` minor `det(X[r, c])` in `m * n` variables `X_{ij} = i * n + j`. -/
@[expose] noncomputable def minor4Term (m n : ℕ) (r₀ r₁ r₂ r₃ c₀ c₁ c₂ c₃ : ℕ) : Term (m * n) :=
  let r : Fin 4 → ℕ := ![r₀, r₁, r₂, r₃]
  let c : Fin 4 → ℕ := ![c₀, c₁, c₂, c₃]
  sumTerms (perms4.map fun p ↦
    if h0 : r p.2.1 * n + c 0 < m * n then
      if h1 : r p.2.2.1 * n + c 1 < m * n then
        if h2 : r p.2.2.2.1 * n + c 2 < m * n then
          if h3 : r p.2.2.2.2 * n + c 3 < m * n then
            .mul (.const p.1)
              (.mul (.var ⟨r p.2.1 * n + c 0, h0⟩)
                (.mul (.var ⟨r p.2.2.1 * n + c 1, h1⟩)
                  (.mul (.var ⟨r p.2.2.2.1 * n + c 2, h2⟩)
                    (.var ⟨r p.2.2.2.2 * n + c 3, h3⟩))))
          else .const 0
        else .const 0
      else .const 0
    else .const 0)

/-- Evaluation of `minor4Term` equals `det(X[r, c])` for `X_{ij} = y (i * n + j)`. -/
theorem eval_minor4Term {m n : ℕ} (r : Fin 4 → Fin m) (c : Fin 4 → Fin n)
    (y : Fin (m * n) → ℝ) :
    (minor4Term m n (r 0).1 (r 1).1 (r 2).1 (r 3).1 (c 0).1 (c 1).1 (c 2).1 (c 3).1).eval y =
      ((Matrix.of fun (i : Fin m) (j : Fin n) ↦
        y ⟨i.1 * n + j.1, by nlinarith [i.2, j.2]⟩).submatrix r c).det := by
  let X : Matrix (Fin m) (Fin n) ℝ :=
    Matrix.of fun i j ↦ y ⟨i.1 * n + j.1, by nlinarith [i.2, j.2]⟩
  rw [← sum_perms4_eq_det (X.submatrix r c), minor4Term, eval_sumTerms, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ ↦ ?_
  have hr : ∀ a : Fin 4, (![(r 0).1, (r 1).1, (r 2).1, (r 3).1] a) = (r a).1 := by
    intro a; fin_cases a <;> rfl
  have hc : ∀ a : Fin 4, (![(c 0).1, (c 1).1, (c 2).1, (c 3).1] a) = (c a).1 := by
    intro a; fin_cases a <;> rfl
  have hlt : ∀ a b : Fin 4, (r a).1 * n + (c b).1 < m * n := fun a b ↦ by
    nlinarith [(r a).2, (c b).2]
  simp only [Function.comp_apply, hr, hc, hlt, ↓reduceDIte, Term.eval, X, Matrix.submatrix_apply,
    Matrix.of_apply]

/-- `Term` encoding one cleared affine constraint `⟨A, X⟩ - b = 0` directly in `X_{ij}`. -/
@[expose] def directConstraintTerm (m n : ℕ) (c : List (List ℚ) × ℚ) : Term (m * n) :=
  let entries : List (Term (m * n)) :=
    (List.range m).flatMap fun i ↦
      (List.range n).map fun j ↦
        if h : i * n + j < m * n then
          .mul (.const (clearedCoeff c i j)) (.var ⟨i * n + j, h⟩)
        else .const 0
  .add (sumTerms entries) (.const (clearedNegRhs c))

/-- Token-level direct affine constraint term (identical encoding, directly `PolyTime`). -/
@[expose] def directConstraintTermTokens (m n : ℕ) (c : List (List ℚ) × ℚ) : List TermToken :=
  let entries : List (List TermToken) :=
    (List.range m).flatMap fun i ↦
      (List.range n).map fun j ↦
        mulTermTokens (constTermTokens (clearedCoeff c i j)) (varTermTokens (i * n + j))
  addTermTokens (sumTermTokens entries) (constTermTokens (clearedNegRhs c))

/-- Token-level `4 × 4` minor term (identical encoding, directly `PolyTime`). -/
@[expose] noncomputable def minor4TermTokens (n : ℕ) (r₀ r₁ r₂ r₃ c₀ c₁ c₂ c₃ : ℕ) :
    List TermToken :=
  let r : Fin 4 → ℕ := ![r₀, r₁, r₂, r₃]
  let c : Fin 4 → ℕ := ![c₀, c₁, c₂, c₃]
  sumTermTokens (perms4.map fun p ↦
    mulTermTokens (constTermTokens p.1)
      (mulTermTokens (varTermTokens (r p.2.1 * n + c 0))
        (mulTermTokens (varTermTokens (r p.2.2.1 * n + c 1))
          (mulTermTokens (varTermTokens (r p.2.2.2.1 * n + c 2))
            (varTermTokens (r p.2.2.2.2 * n + c 3))))))

private theorem encTerm_directConstraintTerm (m n : ℕ) (c : List (List ℚ) × ℚ) :
    encTerm (m * n) (directConstraintTerm m n c) =
      encList encTermToken (directConstraintTermTokens m n c) := by
  rw [encTerm_eq_encList]
  congr 1
  have h1 := encTerm_sumTerms (n := m * n)
    ((List.range m).flatMap fun i ↦ (List.range n).map fun j ↦
      if h : i * n + j < m * n then
        .mul (.const (clearedCoeff c i j)) (.var ⟨i * n + j, h⟩)
      else .const 0)
  rw [encTerm_eq_encList] at h1
  simp only [directConstraintTerm, encTerm_tokens, List.map_cons, List.map_append]
  rw [(encList encTermToken).injective h1]
  simp only [TermToken.ofFin, Sum.map_inl, Sum.map_inr, id_eq, directConstraintTermTokens,
    addTermTokens, constTermTokens]
  congr 1
  congr 1
  congr 1
  simp only [List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun i hi ↦ ?_
  rw [List.mem_range] at hi
  refine List.map_congr_left fun j hj ↦ ?_
  rw [List.mem_range] at hj
  have hlt : i * n + j < m * n := by nlinarith
  simp [hlt, encTerm_tokens, mulTermTokens, varTermTokens]

private theorem encTerm_minor4Term (m n : ℕ) (r : Fin 4 → Fin m) (c : Fin 4 → Fin n) :
    encTerm (m * n)
        (minor4Term m n (r 0).1 (r 1).1 (r 2).1 (r 3).1 (c 0).1 (c 1).1 (c 2).1 (c 3).1) =
      encList encTermToken
        (minor4TermTokens n (r 0).1 (r 1).1 (r 2).1 (r 3).1 (c 0).1 (c 1).1 (c 2).1 (c 3).1) := by
  rw [minor4Term, encTerm_sumTerms]
  congr 2
  rw [List.map_map]
  refine List.map_congr_left fun p _ ↦ ?_
  have hr : ∀ a : Fin 4, (![(r 0).1, (r 1).1, (r 2).1, (r 3).1] a) = (r a).1 := by
    intro a; fin_cases a <;> rfl
  have hc : ∀ a : Fin 4, (![(c 0).1, (c 1).1, (c 2).1, (c 3).1] a) = (c a).1 := by
    intro a; fin_cases a <;> rfl
  have hlt : ∀ a b : Fin 4, (r a).1 * n + (c b).1 < m * n := fun a b ↦ by
    nlinarith [(r a).2, (c b).2]
  simp [Function.comp_apply, hr, hc, hlt, encTerm_tokens, TermToken.ofFin, mulTermTokens,
    constTermTokens, varTermTokens]

/-- ** determinantal reduction `arm3ToETRDet`** from `ARM(3)` to `ETR` using
vanishing `4 × 4` minors (). -/
@[expose] noncomputable def arm3ToETRDet (inst : ARMInstance) : List Bool :=
  if inst.constraints.isEmpty then
    encFormula 0 (.eqZero (.const 0))
  else
    let firstMat := (inst.constraints.headD ([], 0)).1
    let m := firstMat.length
    let n := (firstMat.headD []).length
    if m == 0 || n == 0 then
      if inst.constraints.all (fun c ↦ decide (c.2 = 0)) then
        encFormula 0 (.eqZero (.const 0))
      else
        encFormula 0 .false
    else
      let affineWords := inst.constraints.map fun c ↦
        encList encTermToken (directConstraintTermTokens m n c)
      let minorWords :=
        (List.range m).flatMap fun r₀ ↦
          (List.range m).flatMap fun r₁ ↦
            (List.range m).flatMap fun r₂ ↦
              (List.range m).flatMap fun r₃ ↦
                (List.range n).flatMap fun c₀ ↦
                  (List.range n).flatMap fun c₁ ↦
                    (List.range n).flatMap fun c₂ ↦
                      (List.range n).map fun c₃ ↦
                        encList encTermToken (minor4TermTokens n r₀ r₁ r₂ r₃ c₀ c₁ c₂ c₃)
      encList encFormulaToken (andEqZeroFormulaTokens (affineWords ++ minorWords))

/-- Equisatisfiability of the determinantal encoding `arm3ToETRDet`. -/
theorem arm3ToETRDet_mem_iff (inst : ARMInstance) :
    inst ∈ ARM 3 ↔ arm3ToETRDet inst ∈ ETR := by
  by_cases hemp : inst.constraints.isEmpty = true
  · have hnil : inst.constraints = [] := List.isEmpty_iff.mp hemp
    exact iff_of_true ⟨0, fun c hc ↦ by simp [hnil] at hc, by simp⟩
      (by
        simp only [arm3ToETRDet, hemp, ↓reduceIte, encFormula_mem_ETR]
        exact ⟨Fin.elim0, by simp [Formula.solutionSet, Term.eval]⟩)
  · have hne : inst.constraints ≠ [] := fun h ↦ hemp (by simp [h])
    have hhead_mem : inst.constraints.headD ([], 0) ∈ inst.constraints := by
      cases h : inst.constraints with
      | nil => exact absurd h hne
      | cons c cs => simp [List.headD]
    have hm_eq : (inst.constraints.headD ([], 0)).1.length = inst.rows :=
      (inst.dims_ok _ hhead_mem).1
    by_cases hm0 : inst.rows = 0
    · have hcond : ((inst.constraints.headD ([], 0)).1.length == 0 ||
          ((inst.constraints.headD ([], 0)).1.headD []).length == 0) = true := by
        rw [hm_eq, hm0]; simp
      rw [arm_zero_dim_iff (Or.inl hm0), etr_zero_dim_iff]
      simp only [arm3ToETRDet, hemp, Bool.false_eq_true, ↓reduceIte, hcond]
    · have hrow_ne : (inst.constraints.headD ([], 0)).1 ≠ [] := fun h ↦
        hm0 (by rw [← hm_eq, h]; rfl)
      have hrow_mem : (inst.constraints.headD ([], 0)).1.headD [] ∈
          (inst.constraints.headD ([], 0)).1 := by
        cases h : (inst.constraints.headD ([], 0)).1 with
        | nil => exact absurd h hrow_ne
        | cons r rs => simp [List.headD]
      have hn_eq : ((inst.constraints.headD ([], 0)).1.headD []).length = inst.cols :=
        (inst.dims_ok _ hhead_mem).2 _ hrow_mem
      by_cases hn0 : inst.cols = 0
      · have hcond : ((inst.constraints.headD ([], 0)).1.length == 0 ||
            ((inst.constraints.headD ([], 0)).1.headD []).length == 0) = true := by
          rw [hn_eq, hn0]; simp
        rw [arm_zero_dim_iff (Or.inr hn0), etr_zero_dim_iff]
        simp only [arm3ToETRDet, hemp, Bool.false_eq_true, ↓reduceIte, hcond]
      · let m := inst.rows
        let n := inst.cols
        let affineTerms : List (Term (m * n)) :=
          inst.constraints.map (directConstraintTerm m n)
        let minorTerms : List (Term (m * n)) :=
          (List.range m).flatMap fun r₀ ↦
            (List.range m).flatMap fun r₁ ↦
              (List.range m).flatMap fun r₂ ↦
                (List.range m).flatMap fun r₃ ↦
                  (List.range n).flatMap fun c₀ ↦
                    (List.range n).flatMap fun c₁ ↦
                      (List.range n).flatMap fun c₂ ↦
                        (List.range n).map fun c₃ ↦
                          minor4Term m n r₀ r₁ r₂ r₃ c₀ c₁ c₂ c₃
        have hform : arm3ToETRDet inst =
            encFormula (m * n) (andEqZeroFormula (affineTerms ++ minorTerms)) := by
          dsimp [arm3ToETRDet]
          simp only [hemp, Bool.false_eq_true, ↓reduceIte, hm_eq, hn_eq]
          rw [show (inst.rows == 0 || inst.cols == 0) = false by simp [hm0, hn0]]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [encFormula_andEqZeroFormula, List.map_append]
          congr 1
          refine congrArg andEqZeroFormulaTokens (congrArg₂ (· ++ ·) ?_ ?_)
          · rw [List.map_map]
            exact List.map_congr_left fun c _ ↦ (encTerm_directConstraintTerm m n c).symm
          · simp only [minorTerms, List.map_flatMap, List.map_map]
            refine List.flatMap_congr fun r₀ hr₀ ↦ ?_
            refine List.flatMap_congr fun r₁ hr₁ ↦ ?_
            refine List.flatMap_congr fun r₂ hr₂ ↦ ?_
            refine List.flatMap_congr fun r₃ hr₃ ↦ ?_
            refine List.flatMap_congr fun c₀ hc₀ ↦ ?_
            refine List.flatMap_congr fun c₁ hc₁ ↦ ?_
            refine List.flatMap_congr fun c₂ hc₂ ↦ ?_
            refine List.map_congr_left fun c₃ hc₃ ↦ ?_
            rw [List.mem_range] at hr₀ hr₁ hr₂ hr₃ hc₀ hc₁ hc₂ hc₃
            exact (encTerm_minor4Term m n ![⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩, ⟨r₃, hr₃⟩]
              ![⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ⟨c₃, hc₃⟩]).symm
        rw [hform, encFormula_mem_ETR]
        have heval_direct : ∀ (c : List (List ℚ) × ℚ) (_ : c ∈ inst.constraints)
            (y : Fin (m * n) → ℝ),
            (directConstraintTerm m n c).eval y =
              (constraintDenomProd c : ℝ) *
                (frobeniusInner ((inst.matrixAt c).map ((↑) : ℚ → ℝ))
                  (Matrix.of fun (i : Fin m) (j : Fin n) ↦
                    y ⟨i.1 * n + j.1, by nlinarith [i.2, j.2]⟩) - (c.2 : ℝ)) := by
          intro c hc y
          simp only [directConstraintTerm, Term.eval, eval_sumTerms, clearedNegRhs_cast]
          have hsum :
              (List.map (Term.eval y) ((List.range m).flatMap fun i ↦
                (List.range n).map fun j ↦
                  if h : i * n + j < m * n then
                    .mul (.const (clearedCoeff c i j)) (.var ⟨i * n + j, h⟩)
                  else .const 0)).sum =
              (constraintDenomProd c : ℝ) *
                frobeniusInner ((inst.matrixAt c).map ((↑) : ℚ → ℝ))
                  (Matrix.of fun (i : Fin m) (j : Fin n) ↦
                    y ⟨i.1 * n + j.1, by nlinarith [i.2, j.2]⟩) := by
            simp only [List.map_flatMap, list_sum_flatMap, List.map_map, frobeniusInner_eq_sum,
              Matrix.map_apply, Finset.mul_sum]
            rw [list_sum_map_range]
            apply Finset.sum_congr rfl; intro i _
            rw [list_sum_map_range]
            apply Finset.sum_congr rfl; intro j _
            have hlt : i.1 * n + j.1 < m * n := by nlinarith [i.2, j.2]
            simp only [Function.comp_apply, hlt, ↓reduceDIte, Term.eval, clearedCoeff_cast hc i j,
              Matrix.of_apply]
            ring
          rw [hsum]; ring
        constructor
        · rintro ⟨X, hsat, hrank⟩
          have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
          let y : Fin (m * n) → ℝ := fun idx ↦
            X ⟨idx.1 / n, Nat.div_lt_of_lt_mul (by have := idx.2; nlinarith)⟩
              ⟨idx.1 % n, Nat.mod_lt _ hn_pos⟩
          have hXeq : (Matrix.of fun (i : Fin m) (j : Fin n) ↦
              y ⟨i.1 * n + j.1, by nlinarith [i.2, j.2]⟩) = X := by
            ext i j
            have hdiv : (i.1 * n + j.1) / n = i.1 := by
              rw [Nat.mul_comm i.1 n, Nat.mul_add_div hn_pos, Nat.div_eq_of_lt j.2, Nat.add_zero]
            simp [y, hdiv, Nat.mod_eq_of_lt j.2]
          refine ⟨y, (mem_solutionSet_andEqZeroFormula _ _).mpr ?_⟩
          intro t ht
          rw [List.mem_append] at ht
          rcases ht with ht | ht
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
            rw [heval_direct c hc y, hXeq, hsat c hc, sub_self, mul_zero]
          · simp only [minorTerms, List.mem_flatMap, List.mem_map, List.mem_range] at ht
            obtain ⟨r₀, hr₀, r₁, hr₁, r₂, hr₂, r₃, hr₃, c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, rfl⟩ :=
              ht
            have h := eval_minor4Term ![⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩, ⟨r₃, hr₃⟩]
              ![⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ⟨c₃, hc₃⟩] y
            rw [hXeq] at h
            exact h.trans (rank3_minors hrank _ _)
        · rintro ⟨y, hy⟩
          rw [mem_solutionSet_andEqZeroFormula] at hy
          let X : Matrix (Fin m) (Fin n) ℝ :=
            Matrix.of fun i j ↦ y ⟨i.1 * n + j.1, by nlinarith [i.2, j.2]⟩
          refine ⟨X, fun c hc ↦ ?_, (rank_via_minors X 3).mpr fun r c ↦ ?_⟩
          · have h0 := hy _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
            rw [heval_direct c hc y] at h0
            have hD : (constraintDenomProd c : ℝ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (constraintDenomProd_pos c).ne'
            exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hD)
          · have hmem : minor4Term m n (r 0).1 (r 1).1 (r 2).1 (r 3).1
                (c 0).1 (c 1).1 (c 2).1 (c 3).1 ∈ minorTerms := by
              simp only [minorTerms, List.mem_flatMap, List.mem_map, List.mem_range]
              exact ⟨(r 0).1, (r 0).2, (r 1).1, (r 1).2, (r 2).1, (r 2).2, (r 3).1, (r 3).2,
                (c 0).1, (c 0).2, (c 1).1, (c 1).2, (c 2).1, (c 2).2, (c 3).1, (c 3).2, rfl⟩
            have h0 := hy _ (List.mem_append_right _ hmem)
            rwa [eval_minor4Term r c y] at h0

/-- `arm3ToETRDet` is computable in polynomial time. -/
theorem arm3ToETRDet_polyTime :
    ComputableInPolyTime arm3ToETRDet encARMInstance encBits := by
  let encC := encPair (encList (encList encRat)) encRat
  let encInst := encPair encNat (encPair encNat encARMConstraints)
  have htoPair : ComputableInPolyTime
      (fun inst : ARMInstance ↦ (inst.rows, inst.cols, inst.constraints))
      encARMInstance encInst :=
    (id' (encIn := encARMInstance)).of_enc_eq fun _ ↦ rfl
  have hcs : ComputableInPolyTime (fun inst : ARMInstance ↦ inst.constraints)
      encARMInstance (encList encC) :=
    (snd encNat encARMConstraints).comp ((snd encNat _).comp htoPair)
  have hemp : ComputableInPolyTime (fun inst : ARMInstance ↦ inst.constraints.isEmpty)
      encARMInstance encBool :=
    (listIsEmpty' encC).comp hcs
  have hfirst : ComputableInPolyTime
      (fun inst : ARMInstance ↦ (inst.constraints.headD ([], 0)).1)
      encARMInstance (encList (encList encRat)) :=
    (fst (encList (encList encRat)) encRat).comp ((headD (encA := encC) ([], 0)).comp hcs)
  have hm : ComputableInPolyTime
      (fun inst : ARMInstance ↦ (inst.constraints.headD ([], 0)).1.length)
      encARMInstance encUnary :=
    (length_list (encList encRat)).comp hfirst
  have hn : ComputableInPolyTime
      (fun inst : ARMInstance ↦ ((inst.constraints.headD ([], 0)).1.headD []).length)
      encARMInstance encUnary :=
    (length_list encRat).comp ((headD []).comp hfirst)
  have hzero : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        (inst.constraints.headD ([], 0)).1.length == 0 ||
          ((inst.constraints.headD ([], 0)).1.headD []).length == 0)
      encARMInstance encBool := by
    have hm0 : ComputableInPolyTime
        (fun inst : ARMInstance ↦ (inst.constraints.headD ([], 0)).1.length == 0)
        encARMInstance encBool :=
      (unary_beq hm (const 0)).of_enc_eq fun _ ↦ by simp
    have hn0 : ComputableInPolyTime
        (fun inst : ARMInstance ↦ ((inst.constraints.headD ([], 0)).1.headD []).length == 0)
        encARMInstance encBool :=
      (unary_beq hn (const 0)).of_enc_eq fun _ ↦ by simp
    exact bool_or' hm0 hn0
  have hall0 : ComputableInPolyTime
      (fun inst : ARMInstance ↦ inst.constraints.all (fun c ↦ decide (c.2 = 0)))
      encARMInstance encBool := by
    have htest : ComputableInPolyTime (fun c : List (List ℚ) × ℚ ↦ decide (c.2 = 0))
        encC encBool := by fun_prop
    exact allWith (htest.comp (snd encUnit encC)) (const ()) hcs
  let encParam := encPair encUnary encUnary
  let encP := encPair encParam encC
  have hparam : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        ((inst.constraints.headD ([], 0)).1.length,
          ((inst.constraints.headD ([], 0)).1.headD []).length))
      encARMInstance encParam := hm.prod hn
 -- Affine constraint words in `PolyTime`.
  have hdirectWord : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦
        encList encTermToken (directConstraintTermTokens q.1.1 q.1.2 q.2))
      encP encBits := by
    let encEntryPar := encPair encP encUnary
    let encEntryIJ := encPair encEntryPar encUnary
    have hrow : ComputableInPolyTime
        (fun r : ((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ ↦
          (List.range r.1.1.2).map fun j ↦
            mulTermTokens (constTermTokens (clearedCoeff r.1.2 r.2 j))
              (varTermTokens (r.2 * r.1.1.2 + j)))
        encEntryPar (encList (encList encTermToken)) := by
      have hbody : ComputableInPolyTime
          (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
            mulTermTokens (constTermTokens (clearedCoeff s.1.1.2 s.1.2 s.2))
              (varTermTokens (s.1.2 * s.1.1.1.2 + s.2)))
          encEntryIJ (encList encTermToken) := by
        have hc_at : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.1.2)
            encEntryIJ encC :=
          (snd encParam encC).comp ((fst encP encUnary).comp (fst encEntryPar encUnary))
        have hi_at : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.2)
            encEntryIJ encUnary :=
          (snd encP encUnary).comp (fst encEntryPar encUnary)
        have hj_at : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.2)
            encEntryIJ encUnary :=
          snd encEntryPar encUnary
        have hn_at : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦ s.1.1.1.2)
            encEntryIJ encUnary :=
          (snd encUnary encUnary).comp
            ((fst encParam encC).comp ((fst encP encUnary).comp (fst encEntryPar encUnary)))
        have hD := constraintDenomProd_polyTime.comp hc_at
        have ha : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
              (s.1.1.2.1.getD s.1.2 []).getD s.2 0)
            encEntryIJ encRat :=
          listGetDWithInput (listGetDWithInput ((fst _ _).comp hc_at) hi_at []) hj_at 0
        have hcoeff : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
              clearedCoeff s.1.1.2 s.1.2 s.2)
            encEntryIJ encIntBin :=
          intBin_mul' (rat_num.comp ha) (intBin_natCast.comp (binary_div' hD (rat_den.comp ha)))
        have hconstTok : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
              constTermTokens (clearedCoeff s.1.1.2 s.1.2 s.2))
            encEntryIJ (encList encTermToken) :=
          (cons encTermToken).comp (((sumInl encIntBin _).comp hcoeff).prod (const []))
        have hvarTok : ComputableInPolyTime
            (fun s : (((ℕ × ℕ) × (List (List ℚ) × ℚ)) × ℕ) × ℕ ↦
              varTermTokens (s.1.2 * s.1.1.1.2 + s.2))
            encEntryIJ (encList encTermToken) :=
          (cons encTermToken).comp
            (((sumInr encIntBin _).comp ((sumInl encUnary _).comp
              (unary_add.comp ((unary_mul.comp (hi_at.prod hn_at)).prod hj_at)))).prod (const []))
        exact (cons encTermToken).comp
          ((const (.inr (.inr (.inr ())))).prod
            ((listAppend encTermToken).comp (hconstTok.prod hvarTok)))
      exact mapWith hbody id'
        (range.comp ((snd encUnary encUnary).comp ((fst encParam encC).comp (fst encP encUnary))))
    have hall : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦
          (List.range q.1.1).flatMap fun i ↦
            (List.range q.1.2).map fun j ↦
              mulTermTokens (constTermTokens (clearedCoeff q.2 i j)) (varTermTokens (i * q.1.2 +
                j)))
        encP (encList (encList encTermToken)) :=
      flatMapWith hrow id' (range.comp ((fst encUnary encUnary).comp (fst encParam encC)))
    have hsumTok : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦
          sumTermTokens ((List.range q.1.1).flatMap fun i ↦
            (List.range q.1.2).map fun j ↦
              mulTermTokens (constTermTokens (clearedCoeff q.2 i j)) (varTermTokens (i * q.1.2 +
                j))))
        encP (encList encTermToken) := by
      have hmap : ComputableInPolyTime
          (fun l : List (List TermToken) ↦
            l.map (fun tok ↦ ((.inr (.inr (.inl ())) : TermToken) :: tok)))
          (encList (encList encTermToken)) (encList (encList encTermToken)) :=
        ComputableInPolyTime.map
          ((cons encTermToken).comp
            ((const (α := List TermToken) ((.inr (.inr (.inl ())) : TermToken))).prod id'))
      exact (listAppend encTermToken).comp
        (((flatten encTermToken).comp (hmap.comp hall)).prod
          (const (α := (ℕ × ℕ) × (List (List ℚ) × ℚ)) ([.inl 0] : List TermToken)))
    have hrhsTok : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List (List ℚ) × ℚ) ↦ constTermTokens (clearedNegRhs q.2))
        encP (encList encTermToken) := by
      have hc_q := snd encParam encC
      have hD := constraintDenomProd_polyTime.comp hc_q
      have hb := (snd _ _).comp hc_q
      have hrhs := intBin_neg.comp (intBin_mul' (rat_num.comp hb)
        (intBin_natCast.comp (binary_div' hD (rat_den.comp hb))))
      exact (cons encTermToken).comp (((sumInl encIntBin _).comp hrhs).prod (const []))
    exact ((cons encTermToken).comp
      ((const (α := (ℕ × ℕ) × (List (List ℚ) × ℚ)) ((.inr (.inr (.inl ())) : TermToken))).prod
        ((listAppend encTermToken).comp (hsumTok.prod hrhsTok)))).of_enc_eq fun _ ↦ rfl
 -- Minor `4 × 4` words in `PolyTime`.
  let encM1 := encPair encParam encUnary
  let encM2 := encPair encM1 encUnary
  let encM3 := encPair encM2 encUnary
  let encM4 := encPair encM3 encUnary
  let encM5 := encPair encM4 encUnary
  let encM6 := encPair encM5 encUnary
  let encM7 := encPair encM6 encUnary
  let encM8 := encPair encM7 encUnary
  have hminorWord : ComputableInPolyTime
      (fun s : ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ ↦
        encList encTermToken
          (minor4TermTokens s.1.1.1.1.1.1.1.1.2
            s.1.1.1.1.1.1.1.2 s.1.1.1.1.1.1.2 s.1.1.1.1.1.2 s.1.1.1.1.2
            s.1.1.1.2 s.1.1.2 s.1.2 s.2))
      encM8 encBits := by
    have hn_s : ComputableInPolyTime
        (fun s : ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ ↦
          s.1.1.1.1.1.1.1.1.2) encM8 encUnary :=
      (snd encUnary encUnary).comp ((fst encParam encUnary).comp ((fst encM1 encUnary).comp
        ((fst encM2 encUnary).comp ((fst encM3 encUnary).comp ((fst encM4 encUnary).comp
          ((fst encM5 encUnary).comp ((fst encM6 encUnary).comp (fst encM7 encUnary))))))))
    have hr0 : ComputableInPolyTime (fun s : _ ↦ s.1.1.1.1.1.1.1.2) encM8 encUnary :=
      (snd encParam encUnary).comp ((fst encM1 encUnary).comp ((fst encM2 encUnary).comp
        ((fst encM3 encUnary).comp ((fst encM4 encUnary).comp ((fst encM5 encUnary).comp
          ((fst encM6 encUnary).comp (fst encM7 encUnary)))))))
    have hr1 : ComputableInPolyTime (fun s : _ ↦ s.1.1.1.1.1.1.2) encM8 encUnary :=
      (snd encM1 encUnary).comp ((fst encM2 encUnary).comp ((fst encM3 encUnary).comp
        ((fst encM4 encUnary).comp ((fst encM5 encUnary).comp ((fst encM6 encUnary).comp
          (fst encM7 encUnary))))))
    have hr2 : ComputableInPolyTime (fun s : _ ↦ s.1.1.1.1.1.2) encM8 encUnary :=
      (snd encM2 encUnary).comp ((fst encM3 encUnary).comp ((fst encM4 encUnary).comp
        ((fst encM5 encUnary).comp ((fst encM6 encUnary).comp (fst encM7 encUnary)))))
    have hr3 : ComputableInPolyTime (fun s : _ ↦ s.1.1.1.1.2) encM8 encUnary :=
      (snd encM3 encUnary).comp ((fst encM4 encUnary).comp ((fst encM5 encUnary).comp
        ((fst encM6 encUnary).comp (fst encM7 encUnary))))
    have hc0 : ComputableInPolyTime (fun s : _ ↦ s.1.1.1.2) encM8 encUnary :=
      (snd encM4 encUnary).comp ((fst encM5 encUnary).comp ((fst encM6 encUnary).comp
        (fst encM7 encUnary)))
    have hc1 : ComputableInPolyTime (fun s : _ ↦ s.1.1.2) encM8 encUnary :=
      (snd encM5 encUnary).comp ((fst encM6 encUnary).comp (fst encM7 encUnary))
    have hc2 : ComputableInPolyTime (fun s : _ ↦ s.1.2) encM8 encUnary :=
      (snd encM6 encUnary).comp (fst encM7 encUnary)
    have hc3 : ComputableInPolyTime (fun s : _ ↦ s.2) encM8 encUnary := snd encM7 encUnary
    have hpermList : ComputableInPolyTime
        (fun s : ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ ↦
          perms4.map fun p ↦
            mulTermTokens (constTermTokens p.1)
              (mulTermTokens
                (varTermTokens ((![s.1.1.1.1.1.1.1.2, s.1.1.1.1.1.1.2,
                  s.1.1.1.1.1.2, s.1.1.1.1.2] p.2.1) * s.1.1.1.1.1.1.1.1.2 + s.1.1.1.2))
                (mulTermTokens
                  (varTermTokens ((![s.1.1.1.1.1.1.1.2, s.1.1.1.1.1.1.2,
                    s.1.1.1.1.1.2, s.1.1.1.1.2] p.2.2.1) * s.1.1.1.1.1.1.1.1.2 + s.1.1.2))
                  (mulTermTokens
                    (varTermTokens ((![s.1.1.1.1.1.1.1.2, s.1.1.1.1.1.1.2,
                      s.1.1.1.1.1.2, s.1.1.1.1.2] p.2.2.2.1) * s.1.1.1.1.1.1.1.1.2 + s.1.2))
                    (varTermTokens ((![s.1.1.1.1.1.1.1.2, s.1.1.1.1.1.1.2,
                      s.1.1.1.1.1.2, s.1.1.1.1.2] p.2.2.2.2) * s.1.1.1.1.1.1.1.1.2 + s.2))))))
        encM8 (encList (encList encTermToken)) := by
      refine mapConst perms4 fun p _ ↦ ?_
      have hsel : ∀ a : Fin 4, ComputableInPolyTime
          (fun s : ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ ↦
            ![s.1.1.1.1.1.1.1.2, s.1.1.1.1.1.1.2, s.1.1.1.1.1.2, s.1.1.1.1.2] a)
          encM8 encUnary := fun a ↦ by
        fin_cases a
        · exact hr0
        · exact hr1
        · exact hr2
        · exact hr3
      have hvt : ∀ (a : Fin 4) {g : _ → ℕ},
          ComputableInPolyTime g encM8 encUnary →
          ComputableInPolyTime (fun s ↦ varTermTokens
            ((![s.1.1.1.1.1.1.1.2, s.1.1.1.1.1.1.2, s.1.1.1.1.1.2, s.1.1.1.1.2] a) *
              s.1.1.1.1.1.1.1.1.2 + g s)) encM8 (encList encTermToken) := fun a _ hg ↦
        (cons encTermToken).comp
          (((sumInr encIntBin _).comp ((sumInl encUnary _).comp
            (unary_add.comp ((unary_mul.comp ((hsel a).prod hn_s)).prod hg)))).prod (const []))
      have hmul : ∀ {f g : _ → List TermToken},
          ComputableInPolyTime f encM8 (encList encTermToken) →
          ComputableInPolyTime g encM8 (encList encTermToken) →
          ComputableInPolyTime (fun s ↦ mulTermTokens (f s) (g s)) encM8
            (encList encTermToken) := fun hf hg ↦
        (cons encTermToken).comp
          ((const (α := ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
              ((.inr (.inr (.inr ())) : TermToken))).prod
            ((listAppend encTermToken).comp (hf.prod hg)))
      exact hmul (const (constTermTokens p.1))
        (hmul (hvt p.2.1 hc0)
          (hmul (hvt p.2.2.1 hc1) (hmul (hvt p.2.2.2.1 hc2) (hvt p.2.2.2.2 hc3))))
    have hmap : ComputableInPolyTime
        (fun l : List (List TermToken) ↦
          l.map (fun tok ↦ ((.inr (.inr (.inl ())) : TermToken) :: tok)))
        (encList (encList encTermToken)) (encList (encList encTermToken)) :=
      ComputableInPolyTime.map
        ((cons encTermToken).comp
          ((const (α := List TermToken) ((.inr (.inr (.inl ())) : TermToken))).prod id'))
    exact ((listAppend encTermToken).comp
      (((flatten encTermToken).comp (hmap.comp hpermList)).prod
        (const (α := ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
          ([.inl 0] : List TermToken)))).of_enc_eq
      fun _ ↦ rfl
  have hminorWords : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        let m := (inst.constraints.headD ([], 0)).1.length
        let n := ((inst.constraints.headD ([], 0)).1.headD []).length
        (List.range m).flatMap fun r₀ ↦
          (List.range m).flatMap fun r₁ ↦
            (List.range m).flatMap fun r₂ ↦
              (List.range m).flatMap fun r₃ ↦
                (List.range n).flatMap fun c₀ ↦
                  (List.range n).flatMap fun c₁ ↦
                    (List.range n).flatMap fun c₂ ↦
                      (List.range n).map fun c₃ ↦
                        encList encTermToken (minor4TermTokens n r₀ r₁ r₂ r₃ c₀ c₁ c₂ c₃))
      encARMInstance (encList encBits) := by
    have h7 : ComputableInPolyTime _ encM7 (encList encBits) :=
      mapWith hminorWord id' (range.comp ((snd encUnary encUnary).comp
        ((fst encParam encUnary).comp ((fst encM1 encUnary).comp ((fst encM2 encUnary).comp
          ((fst encM3 encUnary).comp ((fst encM4 encUnary).comp ((fst encM5 encUnary).comp
            (fst encM6 encUnary)))))))))
    have h6 : ComputableInPolyTime _ encM6 (encList encBits) :=
      flatMapWith h7 id' (range.comp ((snd encUnary encUnary).comp
        ((fst encParam encUnary).comp ((fst encM1 encUnary).comp ((fst encM2 encUnary).comp
          ((fst encM3 encUnary).comp ((fst encM4 encUnary).comp (fst encM5 encUnary))))))))
    have h5 : ComputableInPolyTime _ encM5 (encList encBits) :=
      flatMapWith h6 id' (range.comp ((snd encUnary encUnary).comp
        ((fst encParam encUnary).comp ((fst encM1 encUnary).comp ((fst encM2 encUnary).comp
          ((fst encM3 encUnary).comp (fst encM4 encUnary)))))))
    have h4 : ComputableInPolyTime _ encM4 (encList encBits) :=
      flatMapWith h5 id' (range.comp ((snd encUnary encUnary).comp
        ((fst encParam encUnary).comp ((fst encM1 encUnary).comp ((fst encM2 encUnary).comp
          (fst encM3 encUnary))))))
    have h3 : ComputableInPolyTime _ encM3 (encList encBits) :=
      flatMapWith h4 id' (range.comp ((fst encUnary encUnary).comp
        ((fst encParam encUnary).comp ((fst encM1 encUnary).comp (fst encM2 encUnary)))))
    have h2 : ComputableInPolyTime _ encM2 (encList encBits) :=
      flatMapWith h3 id' (range.comp ((fst encUnary encUnary).comp
        ((fst encParam encUnary).comp (fst encM1 encUnary))))
    have h1 : ComputableInPolyTime _ encM1 (encList encBits) :=
      flatMapWith h2 id' (range.comp ((fst encUnary encUnary).comp (fst encParam encUnary)))
    exact (flatMapWith h1 hparam (range.comp hm)).of_enc_eq fun _ ↦ rfl
  have haffineWords : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        inst.constraints.map fun c ↦
          encList encTermToken
            (directConstraintTermTokens
              (inst.constraints.headD ([], 0)).1.length
              ((inst.constraints.headD ([], 0)).1.headD []).length c))
      encARMInstance (encList encBits) :=
    (mapWith hdirectWord hparam hcs).of_enc_eq fun _ ↦ rfl
  have htoks : ComputableInPolyTime
      (fun ws : List (List Bool) ↦ andEqZeroFormulaTokens ws)
      (encList encBits) (encList encFormulaToken) := by
    have hpair : ComputableInPolyTime
        (fun w : List Bool ↦ ([.inr (.inr (.inr (.inr (.inl ())))),
          .inr (.inl w)] : List FormulaToken))
        encBits (encList encFormulaToken) :=
      (cons encFormulaToken).comp
        ((const (α := List Bool) ((.inr (.inr (.inr (.inr (.inl ())))) : FormulaToken))).prod
          ((cons encFormulaToken).comp
            (((sumInr encUnit _).comp ((sumInl encBits _).comp id')).prod (const []))))
    exact (listAppend encFormulaToken).comp
      (((flatten encFormulaToken).comp ((ComputableInPolyTime.map hpair).comp id')).prod
        (const (α := List (List Bool)) ([.inr (.inl (encTerm 0 (.const 0)))] : List FormulaToken)))
  have hmain : ComputableInPolyTime
      (fun inst : ARMInstance ↦
        encList encFormulaToken
          (andEqZeroFormulaTokens
            ((inst.constraints.map fun c ↦
              encList encTermToken
                (directConstraintTermTokens
                  (inst.constraints.headD ([], 0)).1.length
                  ((inst.constraints.headD ([], 0)).1.headD []).length c)) ++
            ((List.range (inst.constraints.headD ([], 0)).1.length).flatMap fun r₀ ↦
              (List.range (inst.constraints.headD ([], 0)).1.length).flatMap fun r₁ ↦
                (List.range (inst.constraints.headD ([], 0)).1.length).flatMap fun r₂ ↦
                  (List.range (inst.constraints.headD ([], 0)).1.length).flatMap fun r₃ ↦
                    (List.range ((inst.constraints.headD ([],
                      0)).1.headD []).length).flatMap fun c₀ ↦
                      (List.range ((inst.constraints.headD ([],
                        0)).1.headD []).length).flatMap fun c₁ ↦
                        (List.range ((inst.constraints.headD ([],
                          0)).1.headD []).length).flatMap fun c₂ ↦
                          (List.range ((inst.constraints.headD ([],
                            0)).1.headD []).length).map fun c₃ ↦
                            encList encTermToken
                              (minor4TermTokens ((inst.constraints.headD ([], 0)).1.headD []).length
                                r₀ r₁ r₂ r₃ c₀ c₁ c₂ c₃)))))
      encARMInstance encBits :=
    (htoks.comp ((listAppend encBits).comp (haffineWords.prod hminorWords))).of_enc_eq fun _ ↦ rfl
  exact hemp.ite' (const (encFormula 0 (.eqZero (.const 0))))
    (hzero.ite'
      (hall0.ite' (const (encFormula 0 (.eqZero (.const 0)))) (const (encFormula 0 .false)))
      hmain)

/-- independent determinantal proof that
`ARM(3) ∈ ∃ℝ` via vanishing `4 × 4` minors. -/
theorem arm3_mem_existsReal_det :
    ARM 3 ∈ ExistsReal encARMInstance :=
  ⟨arm3ToETRDet, arm3ToETRDet_polyTime, arm3ToETRDet_mem_iff⟩

end Cslib.Complexity
