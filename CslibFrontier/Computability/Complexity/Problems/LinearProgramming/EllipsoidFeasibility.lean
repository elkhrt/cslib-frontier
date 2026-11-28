module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.LinearProgramming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.GetD
import Mathlib.Tactic.Matrix.ListMatrix
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Complexity.Problems.LinearProgramming.RoundedEllipsoidStep

/-!
# Khachiyan's Theorem: Polynomial-Time Linear Programming and Halfspace Consistency

This module combines the fixed-precision rounded ellipsoid step with Cramer basic-solution bounds
and integer Farkas certificates to prove Khachiyan's theorem on deterministic multi-tape
Turing machines under standard Lean axioms: rational linear-programming feasibility belongs to the
complexity class `P`, and exact consistent integer linear-threshold classifiers for realizable
Boolean samples are computable in deterministic polynomial time.

## Main definitions

* `CslibFrontier.Complexity.LinearProgramming.solvePerturbedLP`: polynomial-time dyadic ellipsoid
  solver producing a
  Farkas-safe perturbed rational solution iff an integer linear inequality system is feasible.
* `CslibFrontier.Complexity.LinearProgramming.decideLPFeasibility`: polynomial-time decision
  procedure for
  `Cslib.Complexity.LPFeasibility`.
* `CslibFrontier.Complexity.LinearProgramming.evalIntHalfspace`,
  `CslibFrontier.Complexity.LinearProgramming.solveBoolHalfspace`:
  evaluation and deterministic polynomial-time exact consistency solver for Boolean halfspaces.

## Main results

* `CslibFrontier.Complexity.LinearProgramming.solvePerturbedLP_sound`,
  `CslibFrontier.Complexity.LinearProgramming.solvePerturbedLP_isSome_iff`,
    `CslibFrontier.Complexity.LinearProgramming.computableInPolyTime_solvePerturbedLP`: soundness,
  completeness, and
  polynomial-time computability of the rounded dyadic ellipsoid solver.
* `CslibFrontier.Complexity.LinearProgramming.lpFeasibility_mem_P`: Khachiyan's theorem
  `LPFeasibility ∈ P LPFeasibility.encSystem`.
* `CslibFrontier.Complexity.LinearProgramming.solveBoolHalfspace_sound`,
  `CslibFrontier.Complexity.LinearProgramming.solveBoolHalfspace_complete`,
    `CslibFrontier.Complexity.LinearProgramming.computableInPolyTime_solveBoolHalfspace`: soundness,
  completeness, and
  deterministic polynomial-time computability of exact Boolean halfspace consistency.
-/

public section

open Cslib.Complexity Matrix Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

namespace CslibFrontier.Complexity.LinearProgramming

/-! ### Fixed-precision dyadic ellipsoid solver -/

private abbrev EllParTuple := ℕ × (ℕ × (ℤ × (ℤ × (ℤ × List (List ℤ × ℤ)))))
private abbrev EllState := Option (List ℤ) × (List ℤ × List (List ℤ))

private def ellDim (L : ℕ) : ℕ := L + 2
private def ellEQ (L : ℕ) : ℕ := (L + 2) * (6 * L + 8)
private def ellE1 (L : ℕ) : ℕ := (3 * L + 6) * (6 * L + 8)
private def ellRho (L : ℕ) : ℕ := ellE1 L + L + 3
private def ellTau (L : ℕ) : ℕ := ellEQ L + 2 * L + 4
private def ellIter (L : ℕ) : ℕ :=
  12 * (ellDim L) ^ 2 * (2 * ellDim L * (ellRho L + ellTau L) + 1)
private def ellPrec (L : ℕ) : ℕ := 3 * ellIter L + 8 * ellDim L + 16
private def ellKSqrt (L : ℕ) : ℕ :=
  2 * ellPrec L + ellIter L + ellRho L + ellEQ L + L + ellDim L + 4

private def mkPerturbedRows (n : ℕ) (Q : ℤ) (C : List LinearInequality) :
    List (List ℤ × ℤ) :=
  C.map fun c => ((List.range n).map (fun j => Q * c.coeffs.getD j 0), Q * c.bound + 1)

private def mkEllPar (C : List LinearInequality) : EllParTuple :=
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  let p := ellPrec L
  (n, (ellKSqrt L, ((2 : ℤ) ^ p, ((2 : ℤ) ^ (2 * p), ((2 : ℤ) ^ (3 * p),
    mkPerturbedRows n ((2 : ℤ) ^ ellEQ L) C)))))

private def mkEllInit (C : List LinearInequality) : EllState :=
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  let diagVal : ℤ := (2 : ℤ) ^ (ellPrec L + 2 * ellRho L)
  (none,
    (List.replicate n 0,
      (List.range n).map fun i =>
        (List.range n).map fun j => if decide (i = j) then diagVal else 0))

private def ellRowViolated (n : ℕ) (scale : ℤ) (cVec : List ℤ) (row : List ℤ × ℤ) : Bool :=
  decide (scale * row.2 < Mathlib.Tactic.Matrix.ListMatrix.dotProduct n row.1 cVec)

private def ellStep (par : EllParTuple) (st : EllState) : EllState :=
  st.1.elim
    (let n := par.1
     let kSqrt := par.2.1
     let scale := par.2.2.1
     let scale2 := par.2.2.2.1
     let scale3 := par.2.2.2.2.1
     let rows := par.2.2.2.2.2
     let cVec := st.2.1
     let mMat := st.2.2
     (rows.find? (ellRowViolated n scale cVec)).elim
       (some cVec, st.2)
       (fun row =>
         let a := row.1
         let bVec := mMat.map fun mRow => Mathlib.Tactic.Matrix.ListMatrix.dotProduct n mRow a
         let S := Mathlib.Tactic.Matrix.ListMatrix.dotProduct n a bVec
         if decide (S ≤ 0) then
           (none, st.2)
         else
           (none, (dyadicEllipsoidCenterUpdate n kSqrt scale2 scale3 S cVec bVec,
             dyadicEllipsoidMatUpdate n S bVec mMat))))
    (fun _ => st)

private def ellFinal (C : List LinearInequality) : Option (List ℤ) :=
  let par := mkEllPar C
  let out := (ellStep par)^[ellIter (LPFeasibility.encSystem C).length] (mkEllInit C)
  out.1.elim
    (if par.2.2.2.2.2.all (fun row => !ellRowViolated par.1 par.2.2.1 out.2.1 row) then
       some out.2.1
     else
       none)
    some

/-- **Rounded ellipsoid solver for integer linear inequality systems.** Runs the fixed-precision
dyadic ellipsoid algorithm on a Farkas-safe right-hand-side perturbation of `C`, returning
`some (denom, coords)` with `denom > 0` iff `C ∈ LPFeasibility`. -/
def solvePerturbedLP (C : List LinearInequality) : Option (ℤ × List ℤ) :=
  (ellFinal C).map fun cVec => ((2 : ℤ) ^ ellPrec (LPFeasibility.encSystem C).length, cVec)

/-- **Polynomial-time decision procedure for `LPFeasibility`.** -/
def decideLPFeasibility (C : List LinearInequality) : Bool :=
  (solvePerturbedLP C).isSome

/-! ### Farkas perturbation bounds and loop invariant -/

private theorem getD_map_range {α : Type*} (n : ℕ) (f : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  have hlen : i < ((List.range n).map f).length := by simp [hi]
  rw [List.getD_eq_getElem _ d hlen, List.getElem_map, List.getElem_range]

private theorem listDot_eq_fin_sum (n : ℕ) (u v : List ℤ) :
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct n u v =
      ∑ j : Fin n, u.getD j.1 0 * v.getD j.1 0 := by
  rw [Mathlib.Tactic.Matrix.ListMatrix.dotProduct_eq_sum_map_range,
    List.sum_map_range_eq_sum_range, ← Fin.sum_univ_eq_sum_range]

private theorem nat_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; rw [pow_succ]; omega

private theorem abs_coeff_le_two_pow {C : List LinearInequality} {c : LinearInequality}
    (hc : c ∈ C) (j : ℕ) :
    |c.coeffs.getD j 0| ≤ ((2 ^ (LPFeasibility.encSystem C).length : ℕ) : ℤ) := by
  by_cases hj : j < c.coeffs.length
  · have hlen : (encIntBin (c.coeffs.getD j 0)).length ≤ (LPFeasibility.encSystem C).length :=
      ((length_le_encList_of_mem _ (List.getD_mem 0 hj)).trans
        (encLinearInequality_coeffs_length_le c)).trans (length_le_encList_of_mem _ hc)
    rw [length_encIntBin] at hlen
    have hsz : (c.coeffs.getD j 0).natAbs.size ≤ (LPFeasibility.encSystem C).length := by omega
    have hlt := (Nat.lt_size_self (c.coeffs.getD j 0).natAbs).trans_le
      (Nat.pow_le_pow_right (by norm_num) hsz)
    rw [Int.abs_eq_natAbs]; exact_mod_cast hlt.le
  · rw [List.getD_eq_default _ _ (not_lt.mp hj), abs_zero]; positivity

private theorem abs_bound_le_two_pow {C : List LinearInequality} {c : LinearInequality}
    (hc : c ∈ C) : |c.bound| ≤ ((2 ^ (LPFeasibility.encSystem C).length : ℕ) : ℤ) := by
  have hlen : (encIntBin c.bound).length ≤ (LPFeasibility.encSystem C).length :=
    (encLinearInequality_bound_length_le c).trans (length_le_encList_of_mem _ hc)
  rw [length_encIntBin] at hlen
  have hsz : c.bound.natAbs.size ≤ (LPFeasibility.encSystem C).length := by omega
  have hlt := (Nat.lt_size_self c.bound.natAbs).trans_le (Nat.pow_le_pow_right (by norm_num) hsz)
  rw [Int.abs_eq_natAbs]; exact_mod_cast hlt.le

private theorem row_len_le_encSystem {C : List LinearInequality} {c : LinearInequality}
    (hc : c ∈ C) : c.coeffs.length ≤ (LPFeasibility.encSystem C).length :=
  (length_le_length_encList _ _).trans
    ((encLinearInequality_coeffs_length_le c).trans (length_le_encList_of_mem _ hc))

private theorem factorial_le_self_pow (k : ℕ) : k.factorial ≤ k ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul_left (k + 1) (ih.trans (Nat.pow_le_pow_left (Nat.le_succ k) k))

private theorem add_three_le_two_pow (L : ℕ) : L + 3 ≤ 2 ^ (L + 2) := by
  induction L with
  | zero => decide
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1 + 2) = 2 ^ (k + 2) * 2 := by rw [← pow_succ]
    omega

private theorem three_mul_add_four_le_two_pow (L : ℕ) : 3 * L + 4 ≤ 2 ^ (2 * L + 3) := by
  induction L with
  | zero => decide
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ (2 * k + 3) := Nat.one_le_two_pow
    have h2 : 2 ^ (2 * (k + 1) + 3) = 2 ^ (2 * k + 3) * 4 := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by omega, pow_add]; rfl
    omega

private theorem farkas_bound_lt_Q (L m : ℕ) (hm : m ≤ L) :
    m * (m.factorial * ((ellDim L + 1) * (2 ^ L + 1) ^ 2 + 1) ^ m) < 2 ^ ellEQ L := by
  set M := (ellDim L + 1) * (2 ^ L + 1) ^ 2 + 1
  have h2L1 : 2 ^ L + 1 ≤ 2 ^ (L + 1) := by
    have : 1 ≤ 2 ^ L := Nat.one_le_two_pow; rw [pow_succ]; omega
  have hM : M ≤ 2 ^ (3 * L + 5) := by
    have hp : (ellDim L + 1) * (2 ^ L + 1) ^ 2 ≤ 2 ^ (3 * L + 4) :=
      (Nat.mul_le_mul (add_three_le_two_pow L) (Nat.pow_le_pow_left h2L1 2)).trans_eq
        (by rw [← pow_mul, ← pow_add]; congr 1; omega)
    have : 1 ≤ 2 ^ (3 * L + 4) := Nat.one_le_two_pow
    rw [show 3 * L + 5 = (3 * L + 4) + 1 by omega, pow_succ]; dsimp [M]; omega
  have hmM : m * M ≤ 2 ^ (6 * L + 8) :=
    (Nat.mul_le_mul (hm.trans (nat_le_two_pow L)) hM).trans
      (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hm_lt : m < 2 ^ (L + 1) :=
    (hm.trans (nat_le_two_pow L)).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hpow_pos : 0 < (2 ^ (6 * L + 8)) ^ L := by positivity
  have hple : (m * M) ^ m ≤ (2 ^ (6 * L + 8)) ^ L :=
    (Nat.pow_le_pow_left hmM m).trans (Nat.pow_le_pow_right Nat.one_le_two_pow hm)
  calc m * (m.factorial * M ^ m)
      ≤ m * (m * M) ^ m := by
        rw [Nat.mul_pow]
        exact Nat.mul_le_mul_left m (Nat.mul_le_mul_right _ (factorial_le_self_pow m))
    _ ≤ m * (2 ^ (6 * L + 8)) ^ L := Nat.mul_le_mul_left m hple
    _ < 2 ^ (L + 1) * (2 ^ (6 * L + 8)) ^ L := Nat.mul_lt_mul_of_pos_right hm_lt hpow_pos
    _ ≤ 2 ^ ellEQ L := by
        rw [← pow_mul, ← pow_add]; dsimp [ellEQ]
        exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

private theorem witness_bound_le_E1 (L m : ℕ) (hm : m ≤ L) :
    (2 * ellDim L + m).factorial *
      (m * (2 ^ L + 1) ^ 2 + 1) ^ (2 * ellDim L + m) ≤ 2 ^ ellE1 L := by
  set K := 2 * ellDim L + m
  set M := m * (2 ^ L + 1) ^ 2 + 1
  have hK_pow : K ≤ 2 ^ (2 * L + 3) :=
    (show K ≤ 3 * L + 4 by dsimp [K, ellDim]; omega).trans (three_mul_add_four_le_two_pow L)
  have h2L1 : 2 ^ L + 1 ≤ 2 ^ (L + 1) := by
    have : 1 ≤ 2 ^ L := Nat.one_le_two_pow; rw [pow_succ]; omega
  have hM_pow : M ≤ 2 ^ (3 * L + 3) := by
    have hm2 : m * (2 ^ L + 1) ^ 2 ≤ 2 ^ (3 * L + 2) :=
      (Nat.mul_le_mul (hm.trans (nat_le_two_pow L)) (Nat.pow_le_pow_left h2L1 2)).trans_eq
        (by rw [← pow_mul, ← pow_add]; congr 1; omega)
    have : 1 ≤ 2 ^ (3 * L + 2) := Nat.one_le_two_pow
    rw [show 3 * L + 3 = (3 * L + 2) + 1 by omega, pow_succ]; dsimp [M]; omega
  have hKM : K * M ≤ 2 ^ (6 * L + 8) :=
    (Nat.mul_le_mul hK_pow hM_pow).trans
      (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
  calc K.factorial * M ^ K ≤ (K * M) ^ K := by
          rw [Nat.mul_pow]; exact Nat.mul_le_mul_right _ (factorial_le_self_pow K)
    _ ≤ (2 ^ (6 * L + 8)) ^ (3 * L + 6) :=
        (Nat.pow_le_pow_left hKM K).trans
          (Nat.pow_le_pow_right Nat.one_le_two_pow (by dsimp [K, ellDim]; omega))
    _ = 2 ^ ellE1 L := by dsimp [ellE1]; rw [← pow_mul, mul_comm]

private theorem real_mulVec_le_implies_rat {m n B : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ} (hA : ∀ i j, |A i j| ≤ B) (hb : ∀ i, |b i| ≤ B)
    {z : Fin n → ℝ} (hz : A.map (Int.cast : ℤ → ℝ) *ᵥ z ≤ fun i => (b i : ℝ)) :
    ∃ x : Fin n → ℚ, A.map (Int.cast : ℤ → ℚ) *ᵥ x ≤ fun i => (b i : ℚ) := by
  obtain ⟨d, p, hd, hAp, -, -⟩ := Matrix.exists_int_mulVec_le hA hb hz
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨fun j => (p j : ℚ) / d, fun i => ?_⟩
  have hi : ((A *ᵥ p) i : ℚ) ≤ (d : ℚ) * (b i : ℚ) := by exact_mod_cast hAp i
  rw [← mul_le_mul_iff_left₀ hdQ]
  refine le_trans (le_of_eq ?_) (hi.trans_eq (mul_comm _ _))
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Int.cast_sum,
    Int.cast_mul]
  exact Finset.sum_congr rfl fun _ _ => by rw [mul_assoc, div_mul_cancel₀ _ hdQ.ne']

private theorem perturbed_real_implies_lpFeasibility {C : List LinearInequality}
    {x : Fin (ellDim (LPFeasibility.encSystem C).length) → ℝ}
    (hx : ∀ c ∈ C,
      ((2 : ℝ) ^ ellEQ (LPFeasibility.encSystem C).length) *
        (∑ j : Fin (ellDim (LPFeasibility.encSystem C).length), (c.coeffs.getD j.1 0 : ℝ) * x j) ≤
      ((2 : ℝ) ^ ellEQ (LPFeasibility.encSystem C).length) * (c.bound : ℝ) + 1) :
    C ∈ LPFeasibility := by
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  have hrow : ∀ c ∈ C, c.coeffs.length ≤ n := fun c hc =>
    (row_len_le_encSystem hc).trans (by dsimp [n, ellDim]; omega)
  rw [LPFeasibility.mem_iff_exists_mulVec_le hrow]
  by_contra hnoQ
  have hA : ∀ i j, |LPFeasibility.matrix C n i j| ≤ (2 ^ L : ℕ) := fun i j =>
    abs_coeff_le_two_pow (List.getElem_mem i.2) j.1
  have hb : ∀ i, |LPFeasibility.rhs C i| ≤ (2 ^ L : ℕ) := fun i =>
    abs_bound_le_two_pow (List.getElem_mem i.2)
  have hnoR : ¬∃ z : Fin n → ℝ,
      (LPFeasibility.matrix C n).map (Int.cast : ℤ → ℝ) *ᵥ z ≤
        fun i => (LPFeasibility.rhs C i : ℝ) := fun ⟨z, hz⟩ =>
    hnoQ (real_mulVec_le_implies_rat hA hb hz)
  obtain ⟨y, hy0, hyA, hyb, hyB⟩ := Matrix.exists_int_farkas_certificate hA hb hnoR
  simp only [Fintype.card_fin] at hyB
  set Q : ℝ := (2 : ℝ) ^ ellEQ L
  have hQ_pos : 0 < Q := by positivity
  have hAx : ∀ i : Fin C.length,
      ∑ j : Fin n, (LPFeasibility.matrix C n i j : ℝ) * x j ≤
        (LPFeasibility.rhs C i : ℝ) + 1 / Q := fun i => by
    have hdiv : (Q * ∑ j : Fin n, (C[i.1].coeffs.getD j.1 0 : ℝ) * x j) / Q ≤
        (Q * (C[i.1].bound : ℝ) + 1) / Q :=
      (div_le_div_iff_of_pos_right hQ_pos).mpr (hx C[i.1] (List.getElem_mem i.2))
    have hl : (∑ j : Fin n, (LPFeasibility.matrix C n i j : ℝ) * x j) =
        Q * (∑ j : Fin n, (C[i.1].coeffs.getD j.1 0 : ℝ) * x j) / Q :=
      (mul_div_cancel_left₀ _ hQ_pos.ne').symm
    have hr : (LPFeasibility.rhs C i : ℝ) = C[i.1].bound := rfl
    rw [hl, hr]
    exact hdiv.trans_eq (by rw [add_div, mul_div_cancel_left₀ _ hQ_pos.ne'])
  have hsum_y_lt : (∑ i : Fin C.length, (y i : ℝ)) < Q := by
    have hm : C.length ≤ L := length_le_length_encList _ _
    set DF : ℕ := C.length.factorial * ((n + 1) * (2 ^ L + 1) ^ 2 + 1) ^ C.length
    have hsumZ : ∑ i : Fin C.length, y i ≤ ((C.length * DF : ℕ) : ℤ) :=
      (Finset.sum_le_sum fun i _ => hyB i).trans_eq (by simp)
    calc (∑ i : Fin C.length, (y i : ℝ)) = ((∑ i : Fin C.length, y i : ℤ) : ℝ) :=
            (Int.cast_sum _ _).symm
      _ ≤ ((C.length * DF : ℕ) : ℝ) := by exact_mod_cast hsumZ
      _ < ((2 ^ ellEQ L : ℕ) : ℝ) := by exact_mod_cast farkas_bound_lt_Q L C.length hm
      _ = Q := by simp [Q]
  have hyb_le : (∑ i : Fin C.length, (y i : ℝ) * (LPFeasibility.rhs C i : ℝ)) ≤ -1 := by
    have h1 : y ⬝ᵥ LPFeasibility.rhs C ≤ -1 := by omega
    simpa [dotProduct] using (show ((y ⬝ᵥ LPFeasibility.rhs C : ℤ) : ℝ) ≤ -1 by exact_mod_cast h1)
  have hlhs : ∑ i : Fin C.length,
      (y i : ℝ) * (∑ j : Fin n, (LPFeasibility.matrix C n i j : ℝ) * x j) = 0 := by
    calc ∑ i : Fin C.length, (y i : ℝ) * (∑ j : Fin n, (LPFeasibility.matrix C n i j : ℝ) * x j)
        = ∑ j : Fin n, (∑ i : Fin C.length, (y i : ℝ) * (LPFeasibility.matrix C n i j : ℝ)) *
            x j := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := Finset.sum_eq_zero fun j _ => by
          have hj : ((y ᵥ* LPFeasibility.matrix C n) j : ℝ) = 0 := by rw [congrFun hyA j]; simp
          rw [show ∑ i : Fin C.length, (y i : ℝ) * (LPFeasibility.matrix C n i j : ℝ) = 0 by
            simpa [Matrix.vecMul, dotProduct] using hj, zero_mul]
  have hrhs : ∑ i : Fin C.length,
      (y i : ℝ) * (∑ j : Fin n, (LPFeasibility.matrix C n i j : ℝ) * x j) < 0 := by
    calc ∑ i : Fin C.length, (y i : ℝ) * (∑ j : Fin n, (LPFeasibility.matrix C n i j : ℝ) * x j)
        ≤ ∑ i : Fin C.length, (y i : ℝ) * ((LPFeasibility.rhs C i : ℝ) + 1 / Q) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hAx i) (by exact_mod_cast hy0 i)
      _ = (∑ i : Fin C.length, (y i : ℝ) * (LPFeasibility.rhs C i : ℝ)) +
            (∑ i : Fin C.length, (y i : ℝ)) / Q := by
          simp_rw [mul_add, Finset.sum_add_distrib, mul_one_div, Finset.sum_div]
      _ < 0 := by linarith [(div_lt_one hQ_pos).mpr hsum_y_lt]
  linarith

private def ellLoopInv (C : List LinearInequality) (k : ℕ) (st : EllState) : Prop :=
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  let p := ellPrec L
  let N := ellIter L
  let ρ := ellRho L
  let par := mkEllPar C
  let cVec := st.2.1
  let mMat := st.2.2
  let E := dyadicListToMat n p mMat
  cVec.length = n ∧ mMat.length = n ∧ (∀ r ∈ mMat, r.length = n) ∧
    (∀ z ∈ cVec, |z| ≤ (N : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1)) ∧
    (∀ r ∈ mMat, ∀ z ∈ r, |z| ≤ (2 : ℤ) ^ (p + N + 2 * ρ)) ∧
    match st.1 with
    | some w =>
        w.length = n ∧
        (∀ z ∈ w, |z| ≤ (N : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1)) ∧
        par.2.2.2.2.2.all (fun row => !ellRowViolated par.1 par.2.2.1 w row) = true
    | none =>
        (∀ z ∈ cVec, |z| ≤ (k : ℤ) * (2 : ℤ) ^ (p + N + ρ + 1)) ∧
        (∀ r ∈ mMat, ∀ z ∈ r, |z| ≤ (2 : ℤ) ^ (p + k + 2 * ρ)) ∧
        E.PosDef ∧
        (∀ v, (2 : ℝ) ^ (2 * ρ) / (4 : ℝ) ^ k * (v ⬝ᵥ v) ≤ v ⬝ᵥ (E *ᵥ v)) ∧
        (∀ v, v ⬝ᵥ (E *ᵥ v) ≤ (2 : ℝ) ^ (k + 2 * ρ) * (v ⬝ᵥ v)) ∧
        (∀ u : Fin n → ℝ,
          (∀ x : Fin n → ℝ, (x - u) ⬝ᵥ (x - u) ≤ ((2 : ℝ) ^ ellTau L)⁻¹ ^ 2 →
            (x ⬝ᵥ x ≤ ((2 : ℝ) ^ ρ) ^ 2 ∧
              ∀ row ∈ par.2.2.2.2.2,
                ∑ j : Fin n, (row.1.getD j.1 0 : ℝ) * x j ≤ (row.2 : ℝ))) →
          E.det ≤ Real.exp (-(k : ℝ) / (12 * (n : ℝ) ^ 2)) * (2 : ℝ) ^ (2 * n * ρ) ∧
            ∀ x : Fin n → ℝ, (x - u) ⬝ᵥ (x - u) ≤ ((2 : ℝ) ^ ellTau L)⁻¹ ^ 2 →
              x ∈ ellipsoidSet (dyadicListToVec n p cVec) E)

private theorem ellLoopInv_init (C : List LinearInequality) :
    ellLoopInv C 0 (mkEllInit C) := by
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  set p := ellPrec L
  set ρ := ellRho L
  have hE0 : dyadicListToMat n p (mkEllInit C).2.2 =
      ((2 : ℝ) ^ (2 * ρ)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [dyadicListToMat_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.ext_iff]
    dsimp only [mkEllInit]
    rw [getD_map_range n _ [] i.2, getD_map_range n _ 0 j.2]
    by_cases hij : i.1 = j.1
    · simp only [hij, decide_true, ↓reduceIte, Int.cast_pow, Int.cast_ofNat, mul_one]
      rw [pow_add, mul_div_cancel_left₀ _ (by positivity)]
    · simp [hij]
  have hc0 : dyadicListToVec n p (mkEllInit C).2.1 = 0 := by
    funext i
    simp only [dyadicListToVec_apply, Pi.zero_apply]
    have hget : (mkEllInit C).2.1.getD i.1 0 = 0 := by
      have hi : i.1 < (List.replicate n (0 : ℤ)).length := by rw [List.length_replicate]; exact i.2
      change (List.replicate n (0 : ℤ)).getD i.1 0 = 0
      rw [List.getD_eq_getElem _ 0 hi, List.getElem_replicate]
    rw [hget, Int.cast_zero, zero_div]
  have hE0_pos : (dyadicListToMat n p (mkEllInit C).2.2).PosDef := by
    rw [hE0]
    exact posDef_of_quad_lower
      (by change (((2 : ℝ) ^ (2 * ρ)) • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ = _; simp)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * ρ))
      (fun v => by simp [Matrix.smul_mulVec, dotProduct_smul])
  have hE0_inv : (dyadicListToMat n p (mkEllInit C).2.2)⁻¹ =
      (((2 : ℝ) ^ (2 * ρ))⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hE0]
    exact Matrix.inv_eq_right_inv (by
      rw [smul_mul_assoc, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ (2 * ρ) ≠ 0), one_smul, Matrix.one_mul])
  refine ⟨by simp [mkEllInit], by simp [mkEllInit], ?_, ?_, ?_, ?_, ?_, hE0_pos, ?_, ?_, ?_⟩
  · intro r hr; simp only [mkEllInit, List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr; simp
  · intro z hz; simp only [mkEllInit, List.mem_replicate] at hz; rw [hz.2, abs_zero]; positivity
  · intro r hr z hz
    simp only [mkEllInit, List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr
    simp only [List.mem_map] at hz; obtain ⟨_, _, rfl⟩ := hz
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    · simp
  · intro z hz; simp only [mkEllInit, List.mem_replicate] at hz; simp [hz.2]
  · intro r hr z hz
    simp only [mkEllInit, List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr
    simp only [List.mem_map] at hz; obtain ⟨_, _, rfl⟩ := hz
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact le_rfl
    · simp
  · intro v; rw [hE0, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      pow_zero, div_one]
  · intro v; rw [hE0, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, zero_add]
  · intro u hu
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hE0, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul,
        Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, one_mul]
      refine le_of_eq ?_; congr 1; ring
    · rw [mem_ellipsoidSet_iff, hc0, sub_zero, hE0_inv, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul]
      refine (inv_mul_le_one₀ (by positivity)).mpr ?_
      have hx1 := (hu x hx).1
      rwa [← pow_mul, mul_comm ρ 2] at hx1

private theorem ellLoopInv_step (C : List LinearInequality) {k : ℕ}
    (hk : k < ellIter (LPFeasibility.encSystem C).length) {st : EllState}
    (hinv : ellLoopInv C k st) :
    ellLoopInv C (k + 1) (ellStep (mkEllPar C) st) := by
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  set p := ellPrec L
  set N := ellIter L
  set ρ := ellRho L
  set par := mkEllPar C
  obtain ⟨hcLen, hmLen, hmRow, hcAbsN, hmAbsN, hrest⟩ := hinv
  cases hfst : st.1 with
  | some w =>
    rw [hfst] at hrest
    rw [show ellStep par st = st by simp [ellStep, hfst]]
    exact ⟨hcLen, hmLen, hmRow, hcAbsN, hmAbsN, by simpa [hfst] using hrest⟩
  | none =>
    rw [hfst] at hrest
    obtain ⟨hcAbs, hmAbs, hE_pos, hE_low, hE_hi, hball⟩ := hrest
    cases hfind : par.2.2.2.2.2.find? (ellRowViolated par.1 par.2.2.1 st.2.1) with
    | none =>
      rw [show ellStep par st = (some st.2.1, st.2) by simp [ellStep, hfst, hfind]]
      have hall : par.2.2.2.2.2.all (fun row => !ellRowViolated par.1 par.2.2.1 st.2.1 row) =
          true :=
        List.all_eq_true.mpr fun row hrow => by simpa using List.find?_eq_none.mp hfind row hrow
      exact ⟨hcLen, hmLen, hmRow, hcAbsN, hmAbsN, hcLen, hcAbsN, hall⟩
    | some row =>
      let bVec := st.2.2.map fun mRow => Mathlib.Tactic.Matrix.ListMatrix.dotProduct n mRow row.1
      let S := Mathlib.Tactic.Matrix.ListMatrix.dotProduct n row.1 bVec
      have hrow_mem : row ∈ par.2.2.2.2.2 := List.mem_of_find?_eq_some hfind
      have hrow_viol : ellRowViolated par.1 par.2.2.1 st.2.1 row = true := List.find?_some hfind
      obtain ⟨c, hcC, hrow_eq⟩ : ∃ c ∈ C,
          row = ((List.range n).map (fun j => (2 : ℤ) ^ ellEQ L * c.coeffs.getD j 0),
                 (2 : ℤ) ^ ellEQ L * c.bound + 1) := by
        simpa [par, mkEllPar, mkPerturbedRows, n, L, eq_comm] using hrow_mem
      have haLen : row.1.length = n := by rw [hrow_eq]; simp
      have haAbs : ∀ z ∈ row.1, |z| ≤ (2 : ℤ) ^ (ellEQ L + L) := by
        intro z hz; rw [hrow_eq] at hz
        simp only [List.mem_map, List.mem_range] at hz; obtain ⟨j, _, rfl⟩ := hz
        rw [abs_mul, abs_of_pos (by positivity), pow_add]
        exact mul_le_mul_of_nonneg_left (by simpa using abs_coeff_le_two_pow hcC j) (by positivity)
      by_cases hSle : S ≤ 0
      · have hstep_eq : ellStep par st = (none, st.2) := by
          unfold ellStep; rw [hfst]; simp only [Option.elim_none]
          rw [hfind]; simp only [Option.elim_some]
          have hdec : decide (S ≤ 0) = true := decide_eq_true hSle
          change (if decide (S ≤ 0) = true then (none, st.2) else _) = (none, st.2)
          rw [hdec]; simp
        rw [hstep_eq]
        have ha0 : ∀ j : Fin n, row.1.getD j.1 0 = 0 := by
          by_contra hne; push Not at hne; obtain ⟨j, hj⟩ := hne
          let a : Fin n → ℝ := fun i => (row.1.getD i.1 0 : ℝ)
          have hσ : 0 < a ⬝ᵥ (dyadicListToMat n p st.2.2 *ᵥ a) :=
            hE_pos.dotProduct_mulVec_pos fun h => by
              have hj0 : (row.1.getD j.1 0 : ℝ) = 0 := congrFun h j
              exact hj (by exact_mod_cast hj0)
          have hSR : (S : ℝ) = (2 : ℝ) ^ p * (a ⬝ᵥ (dyadicListToMat n p st.2.2 *ᵥ a)) := by
            dsimp [S]; rw [listDot_eq_fin_sum, Int.cast_sum]
            simp only [Int.cast_mul, dotProduct, Matrix.mulVec, dyadicListToMat_apply, a,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have hi : i.1 < st.2.2.length := by rw [hmLen]; exact i.2
            have hbi : bVec.getD i.1 0 =
                Mathlib.Tactic.Matrix.ListMatrix.dotProduct n (st.2.2.getD i.1 []) row.1 := by
              rw [List.getD_eq_getElem bVec 0 (by simp [bVec, hi]), List.getElem_map,
                List.getD_eq_getElem st.2.2 [] hi]
            rw [hbi, listDot_eq_fin_sum, Int.cast_sum]
            simp only [Int.cast_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => ?_
            have hp0 : (2 : ℝ) ^ p ≠ 0 := by positivity
            field_simp
          linarith [show (0 : ℝ) < (S : ℝ) by rw [hSR]; positivity,
            show (S : ℝ) ≤ 0 by exact_mod_cast hSle]
        have hrow2_neg : (row.2 : ℝ) < 0 := by
          simp only [ellRowViolated, decide_eq_true_eq, listDot_eq_fin_sum, par, mkEllPar]
            at hrow_viol
          rw [Finset.sum_eq_zero fun j _ => by rw [ha0 j, zero_mul]] at hrow_viol
          have hZ : row.2 < 0 := by nlinarith [show (0 : ℤ) < 2 ^ p by positivity]
          exact_mod_cast hZ
        refine ⟨hcLen, hmLen, hmRow, hcAbsN, hmAbsN,
          fun z hz => (hcAbs z hz).trans
            (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity)),
          fun r hr z hz => (hmAbs r hr z hz).trans (pow_le_pow_right₀ (by norm_num) (by omega)),
          hE_pos,
          fun v => le_trans (mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by positivity) (by positivity)
              (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)))
            (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)) (hE_low v),
          fun v => (hE_hi v).trans (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (by omega))
            (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)),
          fun u hu => False.elim ?_⟩
        have hu0 : (u - u) ⬝ᵥ (u - u) ≤ ((2 : ℝ) ^ ellTau L)⁻¹ ^ 2 := by
          rw [sub_self, zero_dotProduct]; positivity
        have huu := (hu u hu0).2 row hrow_mem
        rw [Finset.sum_eq_zero fun j _ => by rw [ha0 j]; simp] at huu
        linarith
      · have haNe : ∃ j : Fin n, row.1.getD j.1 0 ≠ 0 := by
          by_contra h0; push Not at h0; apply hSle; dsimp [S]; rw [listDot_eq_fin_sum]
          exact (Finset.sum_eq_zero fun j _ => by rw [h0 j, zero_mul]).le
        have hstep_eq : ellStep par st =
            (none, (dyadicEllipsoidCenterUpdate n (ellKSqrt L) ((2 : ℤ) ^ (2 * p))
              ((2 : ℤ) ^ (3 * p)) S st.2.1 bVec, dyadicEllipsoidMatUpdate n S bVec st.2.2)) := by
          unfold ellStep; rw [hfst]; simp only [Option.elim_none]
          rw [hfind]; simp only [Option.elim_some]
          have hdec : decide (S ≤ 0) = false := decide_eq_false hSle
          change (if decide (S ≤ 0) = true then (none, st.2) else _) = _
          rw [hdec]; simp only [Bool.false_eq_true, ↓reduceIte]; rfl
        rw [hstep_eq]
        have hn2 : 2 ≤ n := by dsimp [n, ellDim]; omega
        have hk1 : ((k + 1 : ℕ) : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr hk
        have hkN : k + 1 ≤ N := hk
        have hkSqrt_le : 2 * p + N + ρ + (ellEQ L + L) + n + 2 ≤ ellKSqrt L := by
          dsimp [ellKSqrt, p, N, ρ, n, L]; omega
        obtain ⟨hc'Len, hm'Len, hm'Row, hE'_pos, hE'_low, hE'_hi, hc'Abs, hm'Abs,
          hdet_step, hcont⟩ :=
          dyadicEllipsoidStep_spec (eA := ellEQ L + L) hn2 hk rfl hkSqrt_le hcLen hmLen
            hE_pos hE_low hE_hi hcAbs haLen haAbs haNe
            (List.map_congr_left fun _ _ => listDot_eq_fin_sum n _ _)
            (listDot_eq_fin_sum n _ _)
        refine ⟨hc'Len, hm'Len, hm'Row,
          fun z hz => (hc'Abs z hz).trans (mul_le_mul_of_nonneg_right hk1 (by positivity)),
          fun r hr z hz => (hm'Abs r hr z hz).trans
            (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (Nat.add_le_add_left hkN p) _)),
          hc'Abs, hm'Abs, hE'_pos, hE'_low, hE'_hi, fun u hu => ?_⟩
        obtain ⟨hdet, hball_u⟩ := hball u hu
        refine ⟨?_, fun x hx => ?_⟩
        · refine (hdet_step.trans (mul_le_mul_of_nonneg_left hdet (Real.exp_pos _).le)).trans_eq ?_
          rw [← mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
        · apply hcont x (hball_u x hx)
          simp only [ellRowViolated, decide_eq_true_eq, listDot_eq_fin_sum, par, mkEllPar]
            at hrow_viol
          have hR : ((2 : ℝ) ^ p) * (row.2 : ℝ) <
              ∑ j : Fin n, (row.1.getD j.1 0 : ℝ) * (st.2.1.getD j.1 0 : ℝ) :=
            by exact_mod_cast hrow_viol
          have hdiv := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ p)).mpr hR
          have hac : (row.2 : ℝ) <
              ∑ j : Fin n, (row.1.getD j.1 0 : ℝ) * dyadicListToVec n p st.2.1 j :=
            lt_of_eq_of_lt (by field_simp)
              (hdiv.trans_eq (by simp [dyadicListToVec_apply, Finset.sum_div, mul_div_assoc]))
          exact ((hu x hx).2 row hrow_mem).trans hac.le

private theorem ellLoopInv_iterate (C : List LinearInequality) {t : ℕ}
    (ht : t ≤ ellIter (LPFeasibility.encSystem C).length) :
    ellLoopInv C t ((ellStep (mkEllPar C))^[t] (mkEllInit C)) := by
  induction t with
  | zero => exact ellLoopInv_init C
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hlt : t < ellIter (LPFeasibility.encSystem C).length := Nat.lt_of_succ_le ht
    exact ellLoopInv_step C hlt (ih hlt.le)

/-! ### Soundness and completeness of `solvePerturbedLP` -/

/-- **Soundness of `solvePerturbedLP`.** Whenever `solvePerturbedLP C = some (d, w)`, `0 < d`,
`C ∈ LPFeasibility`, and `3 * ∑ j < |a|, a[j] * w[j] ≤ 3 * d * t + d` for every `⟨a, t⟩ ∈ C`. -/
theorem solvePerturbedLP_sound {C : List LinearInequality} {d : ℤ} {w : List ℤ}
    (h : solvePerturbedLP C = some (d, w)) :
    0 < d ∧ C ∈ LPFeasibility ∧
      ∀ c ∈ C, 3 * (∑ j ∈ Finset.range c.coeffs.length, c.coeffs.getD j 0 * w.getD j 0) ≤
        3 * d * c.bound + d := by
  let L := (LPFeasibility.encSystem C).length
  let n := ellDim L
  set p := ellPrec L
  simp only [solvePerturbedLP, Option.map_eq_some_iff] at h
  obtain ⟨cVec, hfin, hpair⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  have hall : (mkEllPar C).2.2.2.2.2.all
      (fun row => !ellRowViolated (mkEllPar C).1 (mkEllPar C).2.2.1 cVec row) = true := by
    have hinv := ellLoopInv_iterate C le_rfl
    set out := (ellStep (mkEllPar C))^[ellIter L] (mkEllInit C)
    dsimp [ellFinal] at hfin
    cases hout : out.1 with
    | some u =>
      rw [hout] at hfin; simp only [Option.elim_some, Option.some.injEq] at hfin; subst hfin
      have hrest := hinv.2.2.2.2.2; rw [hout] at hrest; exact hrest.2.2
    | none =>
      change out.1.elim
        (if (mkEllPar C).2.2.2.2.2.all
            (fun row => !ellRowViolated (mkEllPar C).1 (mkEllPar C).2.2.1 out.2.1 row) then
          some out.2.1 else none) some = some cVec at hfin
      rw [hout] at hfin; simp only [Option.elim_none] at hfin
      cases hok : (mkEllPar C).2.2.2.2.2.all
        (fun row => !ellRowViolated (mkEllPar C).1 (mkEllPar C).2.2.1 out.2.1 row)
      · rw [hok] at hfin; simp at hfin
      · rw [hok] at hfin; simp only [↓reduceIte, Option.some.injEq] at hfin; rwa [← hfin]
  have hineq : ∀ c ∈ C,
      (2 : ℤ) ^ ellEQ L * (∑ j ∈ Finset.range c.coeffs.length, c.coeffs.getD j 0 * cVec.getD j 0) ≤
        (2 : ℤ) ^ p * ((2 : ℤ) ^ ellEQ L * c.bound + 1) := by
    intro c hc
    have hrow : !ellRowViolated n ((2 : ℤ) ^ p) cVec
        ((List.range n).map (fun j => (2 : ℤ) ^ ellEQ L * c.coeffs.getD j 0),
          (2 : ℤ) ^ ellEQ L * c.bound + 1) = true :=
      List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hrow' : Mathlib.Tactic.Matrix.ListMatrix.dotProduct n
        ((List.range n).map (fun j => (2 : ℤ) ^ ellEQ L * c.coeffs.getD j 0)) cVec ≤
        (2 : ℤ) ^ p * ((2 : ℤ) ^ ellEQ L * c.bound + 1) := by
      simp only [ellRowViolated, Bool.not_eq_true'] at hrow
      exact not_lt.mp (of_decide_eq_false hrow)
    rw [listDot_eq_fin_sum] at hrow'
    have hlen : c.coeffs.length ≤ n := (row_len_le_encSystem hc).trans (by dsimp [n, ellDim]; omega)
    have hsum : (∑ j : Fin n,
        ((List.range n).map (fun k => (2 : ℤ) ^ ellEQ L * c.coeffs.getD k 0)).getD j.1 0 *
          cVec.getD j.1 0) =
        (2 : ℤ) ^ ellEQ L *
          ∑ j ∈ Finset.range c.coeffs.length, c.coeffs.getD j 0 * cVec.getD j 0 := by
      rw [← Fin.sum_eq_sum_range_of_eq_zero hlen (fun j => c.coeffs.getD j 0 * cVec.getD j 0)
        (fun j hj => by rw [List.getD_eq_default _ _ hj, zero_mul]), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [getD_map_range n _ 0 j.2, mul_assoc]
    linarith [hrow', hsum]
  have hd_pos : (0 : ℤ) < (2 : ℤ) ^ p := by positivity
  refine ⟨hd_pos, ?_, ?_⟩
  · refine perturbed_real_implies_lpFeasibility (x := dyadicListToVec n p cVec) fun c hc => ?_
    have hR : (2 : ℝ) ^ ellEQ L * (∑ j ∈ Finset.range c.coeffs.length,
        (c.coeffs.getD j 0 : ℝ) * (cVec.getD j 0 : ℝ)) ≤
        (2 : ℝ) ^ p * ((2 : ℝ) ^ ellEQ L * (c.bound : ℝ) + 1) := by exact_mod_cast hineq c hc
    have hdiv := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ p)).mpr hR
    have hlen : c.coeffs.length ≤ n := (row_len_le_encSystem hc).trans (by dsimp [n, ellDim]; omega)
    simp only [dyadicListToVec_apply]
    rw [Fin.sum_eq_sum_range_of_eq_zero hlen
      (fun j => (c.coeffs.getD j 0 : ℝ) * ((cVec.getD j 0 : ℝ) / (2 : ℝ) ^ p))
      (fun j hj => by rw [List.getD_eq_default _ _ hj, Int.cast_zero, zero_mul])]
    have hlhs : (2 : ℝ) ^ ellEQ L *
        (∑ j ∈ Finset.range c.coeffs.length,
          (c.coeffs.getD j 0 : ℝ) * ((cVec.getD j 0 : ℝ) / (2 : ℝ) ^ p)) =
        (2 : ℝ) ^ ellEQ L *
          (∑ j ∈ Finset.range c.coeffs.length, (c.coeffs.getD j 0 : ℝ) * (cVec.getD j 0 : ℝ)) /
          (2 : ℝ) ^ p := by
      rw [Finset.sum_congr rfl fun j _ => (mul_div_assoc _ _ _).symm, ← Finset.sum_div,
        mul_div_assoc]
    rw [hlhs]
    exact hdiv.trans_eq (mul_div_cancel_left₀ _ (by positivity))
  · intro c hc
    have hZ := hineq c hc
    have h2 : 2 ≤ ellEQ L :=
      le_trans (show 2 ≤ L + 2 by omega) (Nat.le_mul_of_pos_right (L + 2) (by omega))
    have hQpos : (0 : ℤ) < (2 : ℤ) ^ ellEQ L := by positivity
    have hQ3 : (3 : ℤ) ≤ (2 : ℤ) ^ ellEQ L :=
      le_trans (by decide : (3 : ℤ) ≤ 2 ^ 2) (pow_le_pow_right₀ (by decide) h2)
    have hmul : (2 : ℤ) ^ ellEQ L *
        (3 * ∑ j ∈ Finset.range c.coeffs.length, c.coeffs.getD j 0 * cVec.getD j 0) ≤
        (2 : ℤ) ^ ellEQ L * (3 * (2 : ℤ) ^ p * c.bound + (2 : ℤ) ^ p) := by
      have hpQ : 3 * (2 : ℤ) ^ p ≤ (2 : ℤ) ^ ellEQ L * (2 : ℤ) ^ p :=
        mul_le_mul_of_nonneg_right hQ3 hd_pos.le
      have hZ3 : 3 * ((2 : ℤ) ^ ellEQ L *
          ∑ j ∈ Finset.range c.coeffs.length, c.coeffs.getD j 0 * cVec.getD j 0) ≤
          3 * ((2 : ℤ) ^ p * ((2 : ℤ) ^ ellEQ L * c.bound + 1)) := by linarith
      linarith
    exact le_of_mul_le_mul_left hmul hQpos

/-- **Exact characterization of `solvePerturbedLP`.** `(solvePerturbedLP C).isSome = true` iff
`C ∈ LPFeasibility`. -/
theorem solvePerturbedLP_isSome_iff (C : List LinearInequality) :
    (solvePerturbedLP C).isSome = true ↔ C ∈ LPFeasibility := by
  refine ⟨fun hs => ?_, fun hC => ?_⟩
  · obtain ⟨⟨d, w⟩, hdw⟩ := Option.isSome_iff_exists.mp hs
    exact (solvePerturbedLP_sound hdw).2.1
  · set L := (LPFeasibility.encSystem C).length
    set n := ellDim L
    set p := ellPrec L
    set N := ellIter L
    set ρ := ellRho L
    set τ := ellTau L
    have hrow : ∀ c ∈ C, c.coeffs.length ≤ n := fun c hc =>
      (row_len_le_encSystem hc).trans (by dsimp [n, ellDim]; omega)
    obtain ⟨xQ, hxQ⟩ := (LPFeasibility.mem_iff_exists_mulVec_le hrow).mp hC
    obtain ⟨d0, p0, hd0, hAp0, -, hp0B⟩ :=
      Matrix.exists_int_mulVec_le (A := LPFeasibility.matrix C n) (b := LPFeasibility.rhs C)
        (x := xQ) (B := (2 : ℕ) ^ L)
        (fun i j => abs_coeff_le_two_pow (List.getElem_mem i.2) j.1)
        (fun i => abs_bound_le_two_pow (List.getElem_mem i.2)) hxQ
    have hp0B' : ∀ j : Fin n,
        |p0 j| ≤
          (((2 * n + C.length).factorial *
            (C.length * (2 ^ L + 1) ^ 2 + 1) ^ (2 * n + C.length) : ℕ) : ℤ) :=
      fun j => by simpa only [Fintype.card_fin] using hp0B j
    let u : Fin n → ℝ := fun j => (p0 j : ℝ) / (d0 : ℝ)
    have hd0R : (1 : ℝ) ≤ (d0 : ℝ) := by exact_mod_cast (show 1 ≤ d0 from hd0)
    have hu_coord : ∀ j : Fin n, |u j| ≤ (2 : ℝ) ^ ellE1 L := fun j => by
      have hD1 : |p0 j| ≤ ((2 ^ ellE1 L : ℕ) : ℤ) :=
        (hp0B' j).trans
          (by exact_mod_cast witness_bound_le_E1 L C.length (length_le_length_encList _ _))
      dsimp [u]; rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < d0)]
      refine (div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hd0R).trans ?_
      rw [div_one, ← Int.cast_abs]; exact_mod_cast hD1
    set r : ℝ := ((2 : ℝ) ^ τ)⁻¹
    have hr_pos : 0 < r := by positivity
    have hball_ok : ∀ x : Fin n → ℝ, (x - u) ⬝ᵥ (x - u) ≤ r ^ 2 →
        (x ⬝ᵥ x ≤ ((2 : ℝ) ^ ρ) ^ 2 ∧
          ∀ row ∈ (mkEllPar C).2.2.2.2.2,
            ∑ j : Fin n, (row.1.getD j.1 0 : ℝ) * x j ≤ (row.2 : ℝ)) := by
      intro x hx
      have hcd : ∀ j : Fin n, |x j - u j| ≤ r := fun j => by
        have hsq : (x j - u j) ^ 2 ≤ r ^ 2 := by
          rw [sq]
          exact (Finset.single_le_sum (f := fun i : Fin n => (x i - u i) * (x i - u i))
            (fun _ _ => mul_self_nonneg _) (Finset.mem_univ j)).trans hx
        exact abs_le_of_sq_le_sq hsq hr_pos.le
      refine ⟨?_, ?_⟩
      · have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
        have hxj : ∀ j : Fin n, |x j| ≤ (2 : ℝ) ^ (ellE1 L + 1) := fun j => by
          have htri : |x j| ≤ |u j| + |x j - u j| := by simpa using abs_add_le (u j) (x j - u j)
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ellE1 L := one_le_pow₀ (by norm_num)
          rw [pow_succ]; linarith [hu_coord j, hcd j]
        calc ∑ j : Fin n, x j * x j
            ≤ ∑ _j : Fin n, ((2 : ℝ) ^ (ellE1 L + 1)) ^ 2 := Finset.sum_le_sum fun j _ => by
              rw [← sq]
              exact sq_le_sq.mpr
                (by rw [abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (ellE1 L +
                  1))]; exact hxj j)
          _ = (n : ℝ) * (2 : ℝ) ^ (2 * ellE1 L + 2) := by
              simp [← pow_mul, show (ellE1 L + 1) * 2 = 2 * ellE1 L + 2 by omega]
          _ ≤ (2 : ℝ) ^ (2 * (L + 2)) * (2 : ℝ) ^ (2 * ellE1 L + 2) := by
              have hn_le : n ≤ 2 ^ (2 * (L + 2)) :=
                (nat_le_two_pow n).trans
                  (Nat.pow_le_pow_right (by norm_num) (by dsimp [n, ellDim]; omega))
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn_le) (by positivity)
          _ = ((2 : ℝ) ^ ρ) ^ 2 := by
              rw [← pow_add, ← pow_mul]; congr 1; dsimp [ρ, ellRho]; omega
      · intro row hrm
        simp only [mkEllPar, mkPerturbedRows, List.mem_map] at hrm
        obtain ⟨c, hcC, rfl⟩ := hrm
        obtain ⟨i0, hi0, rfl⟩ := List.getElem_of_mem hcC
        have hau : ∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * u j ≤ (C[i0].bound : ℝ) := by
          have hiR : ((LPFeasibility.matrix C n *ᵥ p0) ⟨i0, hi0⟩ : ℝ) ≤
              (d0 : ℝ) * (C[i0].bound : ℝ) := by exact_mod_cast hAp0 ⟨i0, hi0⟩
          have hdiv := (div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < d0)).mpr hiR
          refine le_trans (le_of_eq ?_) (hdiv.trans_eq (by field_simp))
          simp [u, LPFeasibility.matrix, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
        have hsum_eq : (∑ j : Fin n,
            ((((List.range n).map
              (fun k => (2 : ℤ) ^ ellEQ L * C[i0].coeffs.getD k 0)).getD j.1 0 : ℤ) : ℝ) *
              x j) =
            (2 : ℝ) ^ ellEQ L * (∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * u j) +
            (2 : ℝ) ^ ellEQ L * (∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * (x j - u j)) := by
          rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [getD_map_range n _ 0 j.2]; push_cast; ring
        have hsum_err : ∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * (x j - u j) ≤
            (n : ℝ) * (2 : ℝ) ^ L * r := by
          calc ∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * (x j - u j)
              ≤ ∑ _j : Fin n, (2 : ℝ) ^ L * r := Finset.sum_le_sum fun j _ => by
                refine (le_abs_self _).trans ?_; rw [abs_mul]
                have hcabs : |(C[i0].coeffs.getD j.1 0 : ℝ)| ≤ (2 : ℝ) ^ L := by
                  have h := abs_coeff_le_two_pow hcC j.1; rw [← Int.cast_abs]; exact_mod_cast h
                exact mul_le_mul hcabs (hcd j) (abs_nonneg _) (by positivity)
            _ = (n : ℝ) * (2 : ℝ) ^ L * r := by simp [mul_assoc]
        have herr : (2 : ℝ) ^ ellEQ L *
            (∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * (x j - u j)) ≤ 1 := by
          calc (2 : ℝ) ^ ellEQ L * (∑ j : Fin n, (C[i0].coeffs.getD j.1 0 : ℝ) * (x j - u j))
              ≤ (2 : ℝ) ^ ellEQ L * ((2 : ℝ) ^ (L + 2) * (2 : ℝ) ^ L * ((2 : ℝ) ^ τ)⁻¹) :=
                mul_le_mul_of_nonneg_left (hsum_err.trans
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (by exact_mod_cast nat_le_two_pow n) (by positivity)) hr_pos.le))
                  (by positivity)
            _ = (2 : ℝ) ^ (ellEQ L + 2 * L + 2) / (2 : ℝ) ^ τ := by
                simp only [div_eq_mul_inv, pow_add]; ring
            _ ≤ 1 := (div_le_one (by positivity)).mpr
                (pow_le_pow_right₀ (by norm_num) (by dsimp [τ, ellTau]; omega))
        rw [hsum_eq]; push_cast
        linarith [mul_le_mul_of_nonneg_left hau (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ellEQ L)]
    have hinvN := ellLoopInv_iterate C le_rfl
    set out := (ellStep (mkEllPar C))^[N] (mkEllInit C)
    simp only [solvePerturbedLP, Option.isSome_map, ellFinal]
    cases hout : out.1 with
    | some _ => rfl
    | none =>
      exfalso
      have hrest := hinvN.2.2.2.2.2; rw [hout] at hrest
      obtain ⟨_, _, hEN_pos, _, _, hballN⟩ := hrest
      obtain ⟨hdet_le, hball_sub⟩ := hballN u hball_ok
      have hdet_ge := pow_le_det_of_ball_subset_ellipsoidSet hEN_pos hr_pos hball_sub
      have hexp_eq : -(N : ℝ) / (12 * (n : ℝ) ^ 2) = -((2 * n * (ρ + τ) + 1 : ℕ) : ℝ) := by
        dsimp [N, ellIter, n, ρ, τ]; push_cast
        have hn0 : (ellDim L : ℝ) ≠ 0 := by
          exact_mod_cast (show ellDim L ≠ 0 by dsimp [ellDim]; omega)
        field_simp
      rw [hexp_eq] at hdet_le
      have hexp_lt : Real.exp (-((2 * n * (ρ + τ) + 1 : ℕ) : ℝ)) <
          ((2 : ℝ) ^ (2 * n * (ρ + τ)))⁻¹ := by
        rw [Real.exp_neg, inv_lt_inv₀ (Real.exp_pos _) (by positivity)]
        calc (2 : ℝ) ^ (2 * n * (ρ + τ)) ≤ (Real.exp 1) ^ (2 * n * (ρ + τ)) :=
                pow_le_pow_left₀ zero_le_two (by linarith [Real.exp_one_gt_d9]) _
          _ < Real.exp ((2 * n * (ρ + τ) + 1 : ℕ) : ℝ) := by
                rw [← Real.exp_nat_mul, mul_one]; apply Real.exp_lt_exp.mpr; push_cast; linarith
      have hdet_lt : (dyadicListToMat n p out.2.2).det < r ^ (2 * n) :=
        hdet_le.trans_lt ((mul_lt_mul_of_pos_right hexp_lt (by positivity)).trans_eq (by
          dsimp [r]
          rw [inv_pow, ← pow_mul, mul_comm τ (2 * n), mul_add, pow_add, mul_inv,
            mul_comm ((2 : ℝ) ^ (2 * n * ρ))⁻¹, inv_mul_cancel_right₀ (by positivity)]))
      linarith

/-! ### Polynomial-time computability and Khachiyan's theorem `LPFeasibility ∈ P` -/

private abbrev encEllRow : List ℤ × ℤ ↪ List Bool :=
  encPair (encList encIntBin) encIntBin

private abbrev encEllPar : EllParTuple ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encIntBin
    (encPair encIntBin (encPair encIntBin (encList encEllRow)))))

private abbrev encEllState : EllState ↪ List Bool :=
  encPair (encOption (encList encIntBin))
    (encPair (encList encIntBin) (encList (encList encIntBin)))

private theorem length_encIntBin_of_abs_le {z : ℤ} {E : ℕ} (hz : |z| ≤ (2 : ℤ) ^ E) :
    (encIntBin z).length ≤ E + 2 := by
  rw [length_encIntBin]
  have h1 : z.natAbs ≤ 2 ^ E := by
    exact_mod_cast (show ((z.natAbs : ℕ) : ℤ) ≤ ((2 ^ E : ℕ) : ℤ) by
      simpa [Int.natCast_natAbs] using hz)
  have : z.natAbs.size ≤ E + 1 :=
    Nat.size_le.mpr (h1.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  omega

private theorem listDot_pt {α : Type} {encIn : α ↪ List Bool} {n : α → ℕ}
    {l w : α → List ℤ} (hn : ComputableInPolyTime n encIn encUnary)
    (hl : ComputableInPolyTime l encIn (encList encIntBin))
    (hw : ComputableInPolyTime w encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun a => Mathlib.Tactic.Matrix.ListMatrix.dotProduct (n a) (l a) (w a))
      encIn encIntBin :=
  listDotProduct.comp (hn.prod (hl.prod hw))

attribute [local fun_prop] listDot_pt

/-- **`solvePerturbedLP` runs in deterministic polynomial time** on a multi-tape Turing machine. -/
theorem computableInPolyTime_solvePerturbedLP :
    ComputableInPolyTime solvePerturbedLP LPFeasibility.encSystem
      (encOption (encPair encIntBin (encList encIntBin))) := by
  have hL : ComputableInPolyTime (fun C => (LPFeasibility.encSystem C).length)
      LPFeasibility.encSystem encUnary := encoding_length LPFeasibility.encSystem
  have hn := unary_add' hL (const 2)
  have heQ := unary_mul' (unary_add' hL (const 2)) (unary_add' (unary_mul' (const 6) hL) (const 8))
  have he1 := unary_mul' (unary_add' (unary_mul' (const 3) hL) (const 6))
    (unary_add' (unary_mul' (const 6) hL) (const 8))
  have hrho := unary_add' (unary_add' he1 hL) (const 3)
  have htau := unary_add' (unary_add' heQ (unary_mul' (const 2) hL)) (const 4)
  have hN : ComputableInPolyTime (fun C => ellIter (LPFeasibility.encSystem C).length)
      LPFeasibility.encSystem encUnary := by
    have heq : (fun C => ellIter (LPFeasibility.encSystem C).length) = fun C =>
        12 * (ellDim (LPFeasibility.encSystem C).length *
          ellDim (LPFeasibility.encSystem C).length) *
        (2 * ellDim (LPFeasibility.encSystem C).length *
          (ellRho (LPFeasibility.encSystem C).length +
            ellTau (LPFeasibility.encSystem C).length) + 1) := by funext C; dsimp [ellIter]; ring
    rw [heq]
    exact unary_mul' (unary_mul' (const 12) (unary_mul' hn hn))
      (unary_add' (unary_mul' (unary_mul' (const 2) hn) (unary_add' hrho htau)) (const 1))
  have hp := unary_add' (unary_add' (unary_mul' (const 3) hN) (unary_mul' (const 8) hn)) (const 16)
  have hkSqrt := unary_add' (unary_add' (unary_add' (unary_add' (unary_add'
    (unary_add' (unary_mul' (const 2) hp) hN) hrho) heQ) hL) hn) (const 4)
  have hQ := intBin_pow' (const 2) heQ
  have hrows : ComputableInPolyTime
      (fun C => mkPerturbedRows (ellDim (LPFeasibility.encSystem C).length)
        ((2 : ℤ) ^ ellEQ (LPFeasibility.encSystem C).length) C)
      LPFeasibility.encSystem (encList encEllRow) :=
    mapWithInput (by fun_prop)
      ((mapWithInput (unary_range' (hn.comp (fst _ _)))
        (intBin_mul' (hQ.comp ((fst _ _).comp (fst _ _))) (by fun_prop))).prod
        (intBin_add' (intBin_mul' (hQ.comp (fst _ _)) (by fun_prop)) (const 1)))
  have hscale := intBin_pow' (const 2) hp
  have hpar : ComputableInPolyTime mkEllPar LPFeasibility.encSystem encEllPar :=
    hn.prod (hkSqrt.prod (hscale.prod
      ((intBin_pow' (const 2) (unary_mul' (const 2) hp)).prod
        ((intBin_pow' (const 2) (unary_mul' (const 3) hp)).prod hrows))))
  have hinit : ComputableInPolyTime mkEllInit LPFeasibility.encSystem encEllState := by
    have hdiag := intBin_pow' (const 2) (unary_add' hp (unary_mul' (const 2) hrho))
    refine (const none).prod ((replicate hn (const 0)).prod ?_)
    refine mapWithInput (unary_range' hn) (mapWithInput (unary_range' (hn.comp (fst _ _))) ?_)
    exact ite (by fun_prop) (hdiag.comp ((fst _ _).comp (fst _ _))) (const 0)
  have hstep : ComputableInPolyTime (fun x : EllParTuple × EllState => ellStep x.1 x.2)
      (encPair encEllPar encEllState) encEllState := by
    dsimp only [ellStep]
    refine optionElimWithInput (by fun_prop) ?_ (by fun_prop)
    have hfind := findWithInput
      (test := fun (x : EllParTuple × EllState) (row : List ℤ × ℤ) =>
        ellRowViolated x.1.1 x.1.2.2.1 x.2.2.1 row)
      (by fun_prop : ComputableInPolyTime
        (fun x : EllParTuple × EllState => x.1.2.2.2.2.2)
        (encPair encEllPar encEllState) (encList encEllRow))
      (intBin_lt.comp ((intBin_mul' (by fun_prop) (by fun_prop)).prod
        (listDot_pt (by fun_prop) (by fun_prop) (by fun_prop))))
    refine optionElimWithInput hfind (((optionSome _).comp (by fun_prop)).prod (by fun_prop)) ?_
    let encDom := encPair (encPair encEllPar encEllState) encEllRow
    have hbVec : ComputableInPolyTime
        (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
          y.1.2.2.2.map fun mRow =>
            Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 mRow y.2.1)
        encDom (encList encIntBin) := mapWithInput (by fun_prop) (by fun_prop)
    have hS : ComputableInPolyTime
        (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 y.2.1
            (y.1.2.2.2.map fun mRow =>
              Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 mRow y.2.1))
        encDom encIntBin :=
      listDot_pt ((fst _ _).comp ((fst _ _).comp (fst _ _))) ((fst _ _).comp (snd _ _)) hbVec
    have hq := computableInPolyTime_isqrtBounded
      ((fst _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _))))
      (intBin_toNat.comp (intBin_mul'
        ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
          ((snd _ _).comp ((fst _ _).comp (fst _ _)))))))
        hS))
    have hdenC := intBin_mul'
      (intBin_natCast_unary.comp
        (unary_add' ((fst _ _).comp ((fst _ _).comp (fst _ _))) (const 1)))
      (intBin_natCast.comp (binary_add' hq (const 1)))
    have hcNext : ComputableInPolyTime
        (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
          dyadicEllipsoidCenterUpdate y.1.1.1 y.1.1.2.1 y.1.1.2.2.2.1 y.1.1.2.2.2.2.1
            (Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 y.2.1
              (y.1.2.2.2.map fun mRow =>
                Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 mRow y.2.1))
            y.1.2.2.1
            (y.1.2.2.2.map fun mRow =>
              Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 mRow y.2.1))
        encDom (encList encIntBin) :=
      mapWithInput (unary_range' (by fun_prop))
        (intBin_sub' (listGetDWithInput (by fun_prop) (by fun_prop) 0)
          (intBin_ediv'
            (intBin_mul' (by fun_prop)
              (listGetDWithInput (hbVec.comp (fst _ _)) (by fun_prop) 0))
            (hdenC.comp (fst _ _))))
    have hmNext : ComputableInPolyTime
        (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
          dyadicEllipsoidMatUpdate y.1.1.1
            (Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 y.2.1
              (y.1.2.2.2.map fun mRow =>
                Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 mRow y.2.1))
            (y.1.2.2.2.map fun mRow =>
              Mathlib.Tactic.Matrix.ListMatrix.dotProduct y.1.1.1 mRow y.2.1)
            y.1.2.2.2)
        encDom (encList (encList encIntBin)) := by
      have hnZ : ComputableInPolyTime (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
          (y.1.1.1 : ℤ)) encDom encIntBin := intBin_natCast_unary.comp (by fun_prop)
      have hnumFac : ComputableInPolyTime
          (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
            (16 * (y.1.1.1 : ℤ) * (y.1.1.1 : ℤ) * (y.1.1.1 : ℤ) + 1) *
              ((y.1.1.1 : ℤ) * (y.1.1.1 : ℤ))) encDom encIntBin := by fun_prop
      have hden := intBin_mul'
        (by fun_prop : ComputableInPolyTime
          (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) =>
            16 * (y.1.1.1 : ℤ) * (y.1.1.1 : ℤ) * (y.1.1.1 : ℤ) *
              ((y.1.1.1 : ℤ) * (y.1.1.1 : ℤ) - 1) * ((y.1.1.1 : ℤ) + 1)) encDom encIntBin) hS
      refine mapWithInput (unary_range' (by fun_prop))
        (mapWithInput (unary_range' (by fun_prop)) ?_)
      have hproj := (fst encDom encUnary).comp (fst (encPair encDom encUnary) encUnary)
      have hnZ'' := hnZ.comp hproj
      have hb'' := hbVec.comp hproj
      have hmProj : ComputableInPolyTime
          (fun y : (EllParTuple × EllState) × (List ℤ × ℤ) => y.1.2.2.2)
          encDom (encList (encList encIntBin)) := by fun_prop
      have hmij := listGetDWithInput
        (listGetDWithInput (hmProj.comp hproj) ((snd _ _).comp (fst _ _)) ([] : List ℤ))
        (snd _ _) (0 : ℤ)
      have hbi := listGetDWithInput hb'' ((snd _ _).comp (fst _ _)) (0 : ℤ)
      have hbj := listGetDWithInput hb'' (snd _ _) (0 : ℤ)
      have hnum := intBin_mul' (hnumFac.comp hproj)
        (intBin_sub'
          (intBin_mul' (intBin_mul' (intBin_add' hnZ'' (const 1)) (hS.comp hproj)) hmij)
          (intBin_mul' (intBin_mul' (const 2) hbi) hbj))
      exact intBin_add' (intBin_ediv' hnum (hden.comp hproj))
        (ite (by fun_prop) (intBin_add' hnZ'' (const 1)) (const 0))
    exact ite (intBin_le.comp (hS.prod (const 0)))
      ((const none).prod (by fun_prop)) ((const none).prod (hcNext.prod hmNext))
  let entryExp (C : List LinearInequality) : ℕ :=
    let L := (LPFeasibility.encSystem C).length
    ellPrec L + 2 * ellIter L + 2 * ellRho L + 2
  let sizeBound (C : List LinearInequality) : ℕ :=
    let n := ellDim (LPFeasibility.encSystem C).length
    16 * (n + 2) * (n + 2) * (entryExp C + 6)
  have hsize_pt : ComputableInPolyTime sizeBound LPFeasibility.encSystem encUnary :=
    unary_mul'
      (unary_mul' (unary_mul' (const 16) (unary_add' hn (const 2))) (unary_add' hn (const 2)))
      (unary_add' (unary_add' (unary_add' (unary_add' hp (unary_mul' (const 2) hN))
        (unary_mul' (const 2) hrho)) (const 2)) (const 6))
  have hout := (iterateWith_spec hpar hN hinit hstep ellLoopInv
    ellLoopInv_init (fun C _ _ hk hinv => ellLoopInv_step C hk hinv) hsize_pt.polyBounded
    (fun C _ st _ hinv => by
      obtain ⟨hcLen, hmLen, hmRow, hcAbs, hmAbs, hrest⟩ := hinv
      set L := (LPFeasibility.encSystem C).length
      set n := ellDim L
      set E := entryExp C
      have hEE : ellPrec L + 2 * ellIter L + 2 * ellRho L + 1 ≤ E := by
        dsimp [E, entryExp, L]; omega
      have hcap : (ellIter L : ℤ) * (2 : ℤ) ^ (ellPrec L + ellIter L + ellRho L + 1) ≤
          (2 : ℤ) ^ E := by
        calc (ellIter L : ℤ) * (2 : ℤ) ^ (ellPrec L + ellIter L + ellRho L + 1)
            ≤ (2 : ℤ) ^ ellIter L * (2 : ℤ) ^ (ellPrec L + ellIter L + ellRho L + 1) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast nat_le_two_pow (ellIter L))
                (by positivity)
          _ ≤ (2 : ℤ) ^ E := by
              rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hvec_len : ∀ v : List ℤ, v.length = n → (∀ z ∈ v, |z| ≤ (2 : ℤ) ^ E) →
          (encList encIntBin v).length ≤ n * (2 * (E + 2) + 1) := fun v hvl hva => by
        simpa [hvl] using length_encList_le encIntBin v (b := E + 2)
          fun z hz => length_encIntBin_of_abs_le (hva z hz)
      have hc_enc := hvec_len st.2.1 hcLen fun z hz => (hcAbs z hz).trans hcap
      have hm_enc : (encList (encList encIntBin) st.2.2).length ≤
          n * (2 * (n * (2 * (E + 2) + 1)) + 1) := by
        simpa [hmLen] using length_encList_le (encList encIntBin) st.2.2
          (b := n * (2 * (E + 2) + 1)) fun r hr => hvec_len r (hmRow r hr) fun z hz =>
            (hmAbs r hr z hz).trans (pow_le_pow_right₀ (by norm_num) (by omega))
      have hopt_enc : (encOption (encList encIntBin) st.1).length ≤
          2 * (n * (2 * (E + 2) + 1)) + 2 := by
        cases h1 : st.1 with
        | none => simp [encOption]
        | some w =>
          rw [h1] at hrest
          have hw_enc := hvec_len w hrest.1 fun z hz => (hrest.2.1 z hz).trans hcap
          have hlen_opt : (encOption (encList encIntBin) (some w)).length =
              (encList encIntBin w).length + 1 := by simp [encOption]
          rw [hlen_opt]; omega
      have htot : (encEllState st).length =
          2 * (encOption (encList encIntBin) st.1).length + 1 +
            (2 * (encList encIntBin st.2.1).length + 1 +
              (encList (encList encIntBin) st.2.2).length) := by
        dsimp only [encEllState]; rw [length_encPair, length_encPair]
      rw [htot]
      dsimp only [sizeBound]
      change _ ≤ 16 * (n + 2) * (n + 2) * (E + 6)
      nlinarith)).1
  have hcOut := (fst _ _).comp ((snd _ _).comp hout)
  have hfinal : ComputableInPolyTime ellFinal LPFeasibility.encSystem
      (encOption (encList encIntBin)) := by
    unfold ellFinal
    refine optionElimWithInput ((fst _ _).comp hout) ?_ ((optionSome _).comp (snd _ _))
    have hall := allWithInput
      (test := fun (C : List LinearInequality) (row : List ℤ × ℤ) =>
        !ellRowViolated (mkEllPar C).1 (mkEllPar C).2.2.1
          (((ellStep (mkEllPar C))^[ellIter (LPFeasibility.encSystem C).length]
            (mkEllInit C)).2.1) row)
      hrows (bool_not.comp (intBin_lt.comp
        ((intBin_mul' (hscale.comp (fst _ _)) ((snd _ _).comp (snd _ _))).prod
          (listDot_pt (hn.comp (fst _ _)) ((fst _ _).comp (snd _ _)) (hcOut.comp (fst _ _))))))
    exact ite hall ((optionSome _).comp hcOut) (const none)
  have hsolve_eq : solvePerturbedLP = fun C =>
      (ellFinal C).elim none
        (fun cVec => some ((2 : ℤ) ^ ellPrec (LPFeasibility.encSystem C).length, cVec)) := by
    funext C; unfold solvePerturbedLP; cases ellFinal C <;> rfl
  rw [hsolve_eq]
  exact optionElimWithInput hfinal (const none)
    ((optionSome _).comp ((hscale.comp (fst _ _)).prod (snd _ _)))

/-- `decideLPFeasibility C = true` iff `C ∈ LPFeasibility`. -/
@[simp] theorem decideLPFeasibility_eq_true_iff (C : List LinearInequality) :
    decideLPFeasibility C = true ↔ C ∈ LPFeasibility :=
  solvePerturbedLP_isSome_iff C

/-- `decideLPFeasibility` is computable in deterministic polynomial time on a multi-tape Turing
machine. -/
theorem computableInPolyTime_decideLPFeasibility :
    ComputableInPolyTime decideLPFeasibility LPFeasibility.encSystem encBool := by
  have heq : decideLPFeasibility = fun C => (solvePerturbedLP C).elim false (fun _ => true) := by
    funext C; dsimp [decideLPFeasibility]; cases solvePerturbedLP C <;> rfl
  rw [heq]
  exact optionElimWithInput computableInPolyTime_solvePerturbedLP (const false) (const true)

/-- **Khachiyan's theorem: rational linear-programming feasibility is in `P`.** -/
theorem lpFeasibility_mem_P : LPFeasibility ∈ P LPFeasibility.encSystem :=
  ⟨decideLPFeasibility, computableInPolyTime_decideLPFeasibility,
    fun C => (decideLPFeasibility_eq_true_iff C).symm⟩

/-! ### Exact polynomial-time consistency solver for Boolean linear-threshold classifiers -/

/-- Evaluate an integer halfspace `(w, b)` on a Boolean list `x` (missing coordinates read as
`false`), returning `true` iff `0 ≤ ∑ j < w.length, w[j] * x[j].toNat + b`. -/
@[expose] def evalIntHalfspace (w : List ℤ) (b : ℤ) (x : List Bool) : Bool :=
  decide (0 ≤ ∑ j ∈ Finset.range w.length, w.getD j 0 * ((x.getD j false).toNat : ℤ) + b)

private def boolSampleToLP (d : ℕ) (S : List (List Bool × Bool)) : List LinearInequality :=
  S.map fun ex =>
    if ex.2 then
      { coeffs := (List.range d).map (fun j => -((ex.1.getD j false).toNat : ℤ)) ++ [-1]
        bound := 0 }
    else
      { coeffs := (List.range d).map (fun j => ((ex.1.getD j false).toNat : ℤ)) ++ [1]
        bound := -1 }

/-- **Polynomial-time exact consistency solver for Boolean halfspaces.** Given dimension `d` and a
finite labeled sample `S`, returns exact integer weights `(w, b)` with `w.length = d` consistent
with every `(x, y) ∈ S` whenever `S` is realizable by any real affine halfspace on `{0, 1} ^ d`. -/
def solveBoolHalfspace (d : ℕ) (S : List (List Bool × Bool)) : Option (List ℤ × ℤ) :=
  (solvePerturbedLP (boolSampleToLP d S)).map fun dw =>
    ((List.range d).map fun j => 3 * dw.2.getD j 0, 3 * dw.2.getD d 0 + dw.1)

private theorem getD_append_map_range_left (d : ℕ) (f : ℕ → ℤ) (t : ℤ) {j : ℕ} (hj : j < d) :
    ((List.range d).map f ++ [t]).getD j 0 = f j := by
  have h1 : j < ((List.range d).map f).length := by simp [hj]
  have h2 : j < ((List.range d).map f ++ [t]).length := by simp; omega
  rw [List.getD_eq_getElem _ 0 h2, List.getElem_append_left h1, List.getElem_map,
    List.getElem_range]

private theorem getD_append_map_range_last (d : ℕ) (f : ℕ → ℤ) (t : ℤ) :
    ((List.range d).map f ++ [t]).getD d 0 = t := by
  have h2 : d < ((List.range d).map f ++ [t]).length := by simp
  rw [List.getD_eq_getElem _ 0 h2, List.getElem_append_right (by simp)]; simp

/-- **Soundness of `solveBoolHalfspace`.** Any returned `(w, b)` has length `d` and classifies
every labeled example `(x, y) ∈ S` consistently. -/
theorem solveBoolHalfspace_sound {d : ℕ} {S : List (List Bool × Bool)} {w : List ℤ} {b : ℤ}
    (h : solveBoolHalfspace d S = some (w, b)) :
    w.length = d ∧ ∀ ex ∈ S, evalIntHalfspace w b ex.1 = ex.2 := by
  simp only [solveBoolHalfspace, Option.map_eq_some_iff] at h
  obtain ⟨⟨den, coords⟩, hlp, hwb⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hwb
  obtain ⟨hden, _, hineq⟩ := solvePerturbedLP_sound hlp
  refine ⟨by simp, fun ex hex => ?_⟩
  have hsum_w : (∑ j ∈ Finset.range d,
      ((List.range d).map fun k => 3 * coords.getD k 0).getD j 0 *
        ((ex.1.getD j false).toNat : ℤ)) =
      3 * ∑ j ∈ Finset.range d, coords.getD j 0 * ((ex.1.getD j false).toNat : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [getD_map_range d _ 0 (Finset.mem_range.mp hj), mul_assoc]
  cases hy : ex.2
  · have hmem : ({ coeffs := (List.range d).map (fun j => ((ex.1.getD j false).toNat : ℤ)) ++ [1]
                   bound := -1 } : LinearInequality) ∈ boolSampleToLP d S :=
      List.mem_map.mpr ⟨ex, hex, by simp [hy]⟩
    have hrow := hineq _ hmem
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton,
      Finset.sum_range_succ, getD_append_map_range_last, one_mul] at hrow
    have hpre : (∑ j ∈ Finset.range d,
        ((List.range d).map (fun k => ((ex.1.getD k false).toNat : ℤ)) ++ [1]).getD j 0 *
          coords.getD j 0) =
        ∑ j ∈ Finset.range d, coords.getD j 0 * ((ex.1.getD j false).toNat : ℤ) :=
      Finset.sum_congr rfl fun j hj => by
        rw [getD_append_map_range_left d _ 1 (Finset.mem_range.mp hj), mul_comm]
    rw [hpre] at hrow
    simp only [evalIntHalfspace, List.length_map, List.length_range, hsum_w,
      decide_eq_false_iff_not, not_le]
    linarith
  · have hmem : ({ coeffs := (List.range d).map (fun j => -((ex.1.getD j false).toNat : ℤ)) ++ [-1]
                   bound := 0 } : LinearInequality) ∈ boolSampleToLP d S :=
      List.mem_map.mpr ⟨ex, hex, by simp [hy]⟩
    have hrow := hineq _ hmem
    simp only [List.length_append, List.length_map, List.length_range, List.length_singleton,
      Finset.sum_range_succ, getD_append_map_range_last] at hrow
    have hpre : (∑ j ∈ Finset.range d,
        ((List.range d).map (fun k => -((ex.1.getD k false).toNat : ℤ)) ++ [-1]).getD j 0 *
          coords.getD j 0) =
        -(∑ j ∈ Finset.range d, coords.getD j 0 * ((ex.1.getD j false).toNat : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j hj => by
        rw [getD_append_map_range_left d _ (-1) (Finset.mem_range.mp hj)]; ring
    rw [hpre] at hrow
    simp only [evalIntHalfspace, List.length_map, List.length_range, hsum_w, decide_eq_true_eq]
    linarith

/-- **Completeness of `solveBoolHalfspace`.** Whenever `S` is consistent with any real linear
threshold `(w : Fin d → ℝ, b : ℝ)`, `solveBoolHalfspace d S` returns `some (W, B)`. -/
theorem solveBoolHalfspace_complete {d : ℕ} {S : List (List Bool × Bool)}
    (w : Fin d → ℝ) (b : ℝ)
    (hcons : ∀ ex ∈ S,
      decide (0 ≤ ∑ j : Fin d, w j * ((ex.1.getD j.1 false).toNat : ℝ) + b) = ex.2) :
    ∃ W : List ℤ, ∃ B : ℤ, solveBoolHalfspace d S = some (W, B) := by
  classical
  suffices hfeas : boolSampleToLP d S ∈ LPFeasibility by
    obtain ⟨dw, hdw⟩ := Option.isSome_iff_exists.mp ((solvePerturbedLP_isSome_iff _).mpr hfeas)
    exact ⟨_, _, Option.map_eq_some_iff.mpr ⟨dw, hdw, rfl⟩⟩
  let score (ex : List Bool × Bool) : ℝ :=
    ∑ j : Fin d, w j * ((ex.1.getD j.1 false).toNat : ℝ) + b
  let negs : List (List Bool × Bool) := S.filter fun ex => !ex.2
  have hex_scale : ∃ γ : ℝ, 0 < γ ∧ ∀ ex ∈ S, ex.2 = false → γ * score ex ≤ -1 := by
    by_cases hne : negs = []
    · refine ⟨1, zero_lt_one, fun ex hex hy => ?_⟩
      have : ex ∈ negs := List.mem_filter.mpr ⟨hex, by simp [hy]⟩
      simp [hne] at this
    · have hfin_ne : (negs.toFinset.image fun ex => -score ex).Nonempty := by
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil negs hne
        exact ⟨-score a, Finset.mem_image_of_mem _ (List.mem_toFinset.mpr ha)⟩
      set μ := (negs.toFinset.image fun ex => -score ex).min' hfin_ne
      have hμ_pos : 0 < μ := by
        obtain ⟨a, ha, hμa⟩ := Finset.mem_image.mp (Finset.min'_mem _ hfin_ne)
        obtain ⟨hS, hy⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
        have hlt : score a < 0 := by
          have hc := hcons a hS
          rw [show a.2 = false by simpa using hy, decide_eq_false_iff_not, not_le] at hc
          exact hc
        linarith
      refine ⟨μ⁻¹, inv_pos.mpr hμ_pos, fun ex hex hy => ?_⟩
      have hμ_le : μ ≤ -score ex := Finset.min'_le _ _
        (Finset.mem_image_of_mem _
          (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hex, by simp [hy]⟩)))
      have h1 : 1 ≤ μ⁻¹ * (-score ex) := by
        rw [← inv_mul_cancel₀ hμ_pos.ne']
        exact mul_le_mul_of_nonneg_left hμ_le (inv_pos.mpr hμ_pos).le
      linarith
  obtain ⟨γ, hγ, hneg⟩ := hex_scale
  set C := boolSampleToLP d S
  have hrow : ∀ c ∈ C, c.coeffs.length ≤ d + 1 := by
    intro c hc; simp only [C, boolSampleToLP, List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc; split_ifs <;> simp
  rw [LPFeasibility.mem_iff_exists_mulVec_le hrow]
  let z : Fin (d + 1) → ℝ := fun j => if h : j.1 < d then γ * w ⟨j.1, h⟩ else γ * b
  refine real_mulVec_le_implies_rat
    (fun i j => abs_coeff_le_two_pow (List.getElem_mem i.2) j.1)
    (fun i => abs_bound_le_two_pow (List.getElem_mem i.2)) (z := z) fun i => ?_
  have hiS : i.1 < S.length := by simpa [C, boolSampleToLP] using i.2
  set ex := S[i.1]
  have hexS : ex ∈ S := List.getElem_mem hiS
  have hCi : C[i.1] = (if ex.2 then
      { coeffs := (List.range d).map (fun j => -((ex.1.getD j false).toNat : ℤ)) ++ [-1],
        bound := 0 }
    else
      { coeffs := (List.range d).map (fun j => ((ex.1.getD j false).toNat : ℤ)) ++ [1],
        bound := -1 }) := by simp [C, boolSampleToLP, ex]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, LPFeasibility.matrix, Matrix.of_apply,
    LPFeasibility.rhs, hCi]
  cases hy : ex.2
  · simp only [Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_castSucc, Fin.val_castSucc,
      Fin.val_last]
    rw [getD_append_map_range_last]
    have hpre : (∑ j : Fin d,
        ((((List.range d).map (fun k => ((ex.1.getD k false).toNat : ℤ)) ++ [1]).getD
          j.1 0 : ℤ) : ℝ) * z j.castSucc) =
        γ * ∑ j : Fin d, w j * ((ex.1.getD j.1 false).toNat : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [getD_append_map_range_left d _ 1 j.2]
      have hzj : z j.castSucc = γ * w j := by simp [z, j.2]
      rw [hzj]; push_cast; ring
    have hzlast : z (Fin.last d) = γ * b := by simp [z]
    rw [hpre, hzlast]; push_cast
    have := hneg ex hexS hy; dsimp [score] at this; linarith
  · simp only [↓reduceIte, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [getD_append_map_range_last]
    have hpre : (∑ j : Fin d,
        ((((List.range d).map (fun k => -((ex.1.getD k false).toNat : ℤ)) ++ [-1]).getD
          j.1 0 : ℤ) : ℝ) * z j.castSucc) =
        -(γ * ∑ j : Fin d, w j * ((ex.1.getD j.1 false).toNat : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [getD_append_map_range_left d _ (-1) j.2]
      have hzj : z j.castSucc = γ * w j := by simp [z, j.2]
      rw [hzj]; push_cast; ring
    have hzlast : z (Fin.last d) = γ * b := by simp [z]
    rw [hpre, hzlast]; push_cast
    have hge : 0 ≤ score ex := by have hc := hcons ex hexS; rwa [hy, decide_eq_true_eq] at hc
    have hmul := mul_nonneg hγ.le hge; dsimp [score] at hmul; linarith

/-- **`solveBoolHalfspace` is computable in deterministic polynomial time** on a multi-tape Turing
machine. -/
theorem computableInPolyTime_solveBoolHalfspace :
    ComputableInPolyTime (fun p : ℕ × List (List Bool × Bool) => solveBoolHalfspace p.1 p.2)
      (encPair encUnary (encList (encPair encBits encBool)))
      (encOption (encPair (encList encIntBin) encIntBin)) := by
  have hbit : ∀ {α : Type} {enc : α ↪ List Bool} {xs : α → List Bool} {idx : α → ℕ},
      ComputableInPolyTime xs enc encBits →
      ComputableInPolyTime idx enc encUnary →
      ComputableInPolyTime (fun a => (((xs a).getD (idx a) false).toNat : ℤ)) enc encIntBin := by
    intro α enc xs idx hxs hidx
    have hb := listGetDWithInput ((bits_encList_polyTime encBool).1.comp hxs) hidx false
    have heq : (fun a => (((xs a).getD (idx a) false).toNat : ℤ)) =
        fun a => if (xs a).getD (idx a) false then (1 : ℤ) else 0 := by
      funext a; cases (xs a).getD (idx a) false <;> rfl
    rw [heq]; exact ite hb (const 1) (const 0)
  have hmk : ComputableInPolyTime (fun p : List ℤ × ℤ => LinearInequality.mk p.1 p.2)
      (encPair (encList encIntBin) encIntBin) encLinearInequality := by fun_prop
  have htoLP : ComputableInPolyTime
      (fun p : ℕ × List (List Bool × Bool) => boolSampleToLP p.1 p.2)
      (encPair encUnary (encList (encPair encBits encBool))) LPFeasibility.encSystem := by
    refine mapWithInput (by fun_prop) (ite (by fun_prop) ?_ ?_)
    · exact hmk.comp ((listAppend'
        (mapWithInput (unary_range' (by fun_prop))
          (intBin_neg.comp (hbit (by fun_prop) (by fun_prop)))) (const [-1])).prod (const 0))
    · exact hmk.comp ((listAppend'
        (mapWithInput (unary_range' (by fun_prop))
          (hbit (by fun_prop) (by fun_prop))) (const [1])).prod (const (-1)))
  have hlp := computableInPolyTime_solvePerturbedLP.comp htoLP
  have heq : (fun p : ℕ × List (List Bool × Bool) => solveBoolHalfspace p.1 p.2) = fun p =>
      (solvePerturbedLP (boolSampleToLP p.1 p.2)).elim none
        (fun dw => some ((List.range p.1).map (fun j => 3 * dw.2.getD j 0),
          3 * dw.2.getD p.1 0 + dw.1)) := by
    funext p; dsimp [solveBoolHalfspace]; cases solvePerturbedLP (boolSampleToLP p.1 p.2) <;> rfl
  rw [heq]
  exact optionElimWithInput hlp (const none)
    ((optionSome _).comp
      ((mapWithInput (unary_range' (by fun_prop))
        (intBin_mul' (const 3) (listGetDWithInput (by fun_prop) (by fun_prop) 0))).prod
        (intBin_add' (intBin_mul' (const 3) (listGetDWithInput (by fun_prop) (by fun_prop) 0))
          (by fun_prop))))

-- Non-vacuity witness on the 2-input Boolean OR sample.
example : ∃ w b, solveBoolHalfspace 2
    [([false, false], false), ([true, false], true), ([false, true], true)] =
    some (w, b) ∧ w.length = 2 := by
  obtain ⟨w, b, h⟩ := solveBoolHalfspace_complete (fun _ : Fin 2 => (1 : ℝ)) (-1 / 2 : ℝ) (by
    intro ex hex
    have hcheck : ∀ a ∈ ([([false, false], false), ([true, false], true),
        ([false, true], true)] : List (List Bool × Bool)),
        decide (0 ≤ (1 : ℝ) * ((a.1.getD 0 false).toNat : ℝ) +
          (1 : ℝ) * ((a.1.getD 1 false).toNat : ℝ) + (-1 / 2 : ℝ)) = a.2 := by
      refine List.forall_mem_cons.mpr ⟨?_, List.forall_mem_cons.mpr
        ⟨?_, List.forall_mem_cons.mpr ⟨?_, List.forall_mem_nil _⟩⟩⟩
      · exact decide_eq_false (by change ¬ (0 : ℝ) ≤ 1 * (0 : ℕ) + 1 * (0 : ℕ) + (-1 / 2); norm_num)
      · exact decide_eq_true (by change (0 : ℝ) ≤ 1 * (1 : ℕ) + 1 * (0 : ℕ) + (-1 / 2); norm_num)
      · exact decide_eq_true (by change (0 : ℝ) ≤ 1 * (0 : ℕ) + 1 * (1 : ℕ) + (-1 / 2); norm_num)
    rw [Fin.sum_univ_two]
    exact hcheck ex hex)
  exact ⟨w, b, h, (solveBoolHalfspace_sound h).1⟩

end CslibFrontier.Complexity.LinearProgramming
