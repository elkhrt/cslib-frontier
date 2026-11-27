/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Gradient
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring

/-!
# The matrix transposition principle for arithmetic circuits

Given an arithmetic circuit `c : Circuit (arithSignature K) n m` of size `s` formally computing a
linear map `x ↦ A *ᵥ x` over a commutative semiring `K`, reverse-mode differentiation of the
bilinear form `(x, y) ↦ ∑ k, c_k(x) * y_k` followed by substituting `x = 0` yields an explicit
arithmetic circuit `Circuit.transpose c : Circuit (arithSignature K) m n` of size at most
`5 * s + 10 * m + 8` formally computing `y ↦ Aᵀ *ᵥ y`.

## Main definitions

* `CslibFrontier.Circuits.bilinearDotCircuit`: circuit on `m + m` inputs computing `∑ k, u_k * v_k`.
* `CslibFrontier.Circuits.zeroPadLeftCircuit`: one-gate substitution setting the first `n` inputs to
  `0`.
* `CslibFrontier.Circuits.transposeCircuit`: syntactic transposition of an arithmetic circuit.

## Main results

* `CslibFrontier.Circuits.size_transposeCircuit_le`:
  `(transposeCircuit c).size ≤ 5 * c.size + 10 * m + 8`.
* `CslibFrontier.Circuits.polynomial_transposeCircuit`: formal linear-form transposition.
* `CslibFrontier.Circuits.eval_transposeCircuit`: value-level matrix-vector product `Aᵀ *ᵥ y`.
* `CslibFrontier.Circuits.exists_transpose_mulVec`: existential transposition principle.
-/

public section

namespace CslibFrontier.Circuits

open Cslib.Circuits MvPolynomial
open scoped BigOperators Matrix

universe u

variable {K : Type u}

/-- Arithmetic circuit on `m + m` inputs computing `∑ k : Fin m, u_k * v_k` with `2 * m + 1`
gates. -/
def bilinearDotCircuit [Zero K] : (m : ℕ) → Circuit (arithSignature K) (m + m) 1
  | 0 => Circuit.oneGate (σ := arithSignature K) (.const 0) Fin.elim0
  | m + 1 =>
    let prev : Circuit (arithSignature K) ((m + 1) + (m + 1)) 1 :=
      (bilinearDotCircuit m).mapInputs fun idx =>
        Fin.addCases (fun i : Fin m => Fin.castAdd (m + 1) i.castSucc)
          (fun j : Fin m => Fin.natAdd (m + 1) j.castSucc) idx
    let prodLast : Circuit (arithSignature K) ((m + 1) + (m + 1)) 1 :=
      Circuit.oneGate (σ := arithSignature K) .mul
        ![Fin.castAdd (m + 1) (Fin.last m), Fin.natAdd (m + 1) (Fin.last m)]
    let addTwo : Circuit (arithSignature K) 2 1 :=
      Circuit.oneGate (σ := arithSignature K) .add ![0, 1]
    addTwo.comp (prev.append prodLast)

/-- Exact gate count `2 * m + 1` of `bilinearDotCircuit m`. -/
@[simp]
theorem size_bilinearDotCircuit [Zero K] (m : ℕ) :
    (bilinearDotCircuit (K := K) m).size = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [bilinearDotCircuit, Circuit.size_comp, Circuit.size_append, Circuit.mapInputs_size,
      Circuit.size_oneGate, ih]
    omega

/-- Evaluation of `bilinearDotCircuit m` under any commutative-semiring interpretation. -/
theorem eval_bilinearDotCircuit [Zero K] {R : Type*} [CommSemiring R] (constant : K → R)
    (h0 : constant 0 = 0) :
    ∀ (m : ℕ) (z : Fin (m + m) → R),
      (bilinearDotCircuit (K := K) m).eval (arithInterpretationWith K constant) z 0 =
        ∑ k : Fin m, z (Fin.castAdd m k) * z (Fin.natAdd m k)
  | 0, z => by
    simp [bilinearDotCircuit, arithInterpretationWith, h0]
  | m + 1, z => by
    let prevC : Circuit (arithSignature K) ((m + 1) + (m + 1)) 1 :=
      (bilinearDotCircuit (K := K) m).mapInputs fun idx =>
        Fin.addCases (fun i : Fin m => Fin.castAdd (m + 1) i.castSucc)
          (fun j : Fin m => Fin.natAdd (m + 1) j.castSucc) idx
    let prodC : Circuit (arithSignature K) ((m + 1) + (m + 1)) 1 :=
      Circuit.oneGate (σ := arithSignature K) .mul
        ![Fin.castAdd (m + 1) (Fin.last m), Fin.natAdd (m + 1) (Fin.last m)]
    simp only [bilinearDotCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_oneGate,
      arithInterpretationWith]
    have hprev : prevC.eval (arithInterpretationWith K constant) z 0 =
        ∑ k : Fin m,
          z (Fin.castAdd (m + 1) k.castSucc) * z (Fin.natAdd (m + 1) k.castSucc) := by
      dsimp only [prevC]
      rw [Circuit.eval_mapInputs, eval_bilinearDotCircuit constant h0 m]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, Fin.addCases_left, Fin.addCases_right]
    have hleft : Fin.append (prevC.eval (arithInterpretationWith K constant) z)
        (prodC.eval (arithInterpretationWith K constant) z) (0 : Fin 2) =
        ∑ k : Fin m,
          z (Fin.castAdd (m + 1) k.castSucc) * z (Fin.natAdd (m + 1) k.castSucc) := by
      change Fin.append _ _ (Fin.castAdd 1 (0 : Fin 1)) = _
      rw [Fin.append_left, hprev]
    have hright : Fin.append (prevC.eval (arithInterpretationWith K constant) z)
        (prodC.eval (arithInterpretationWith K constant) z) (1 : Fin 2) =
        z (Fin.castAdd (m + 1) (Fin.last m)) * z (Fin.natAdd (m + 1) (Fin.last m)) := by
      change Fin.append _ _ (Fin.natAdd 1 (0 : Fin 1)) = _
      rw [Fin.append_right]
      simp [prodC, arithInterpretationWith]
    change Fin.append (prevC.eval (arithInterpretationWith K constant) z)
        (prodC.eval (arithInterpretationWith K constant) z) (0 : Fin 2) +
      Fin.append (prevC.eval (arithInterpretationWith K constant) z)
        (prodC.eval (arithInterpretationWith K constant) z) (1 : Fin 2) = _
    rw [hleft, hright, Fin.sum_univ_castSucc]

/-- One-gate input-substitution circuit setting the first `n` wires to `0`. -/
@[expose] def zeroPadLeftCircuit [Zero K] (n m : ℕ) : Circuit (arithSignature K) m (n + m) where
  size := 1
  program := .gate .empty ⟨.const 0, Fin.elim0⟩
  outputs := Fin.addCases (fun _ : Fin n => .gate 0) (fun k : Fin m => .input k)

/-- Gate count of `zeroPadLeftCircuit n m` is `1`. -/
@[simp]
theorem size_zeroPadLeftCircuit [Zero K] (n m : ℕ) :
    (zeroPadLeftCircuit (K := K) n m).size = 1 :=
  rfl

/-- Evaluation of `zeroPadLeftCircuit n m`. -/
theorem eval_zeroPadLeftCircuit [Zero K] {R : Type*} [Add R] [Mul R] (constant : K → R)
    (n m : ℕ) (y : Fin m → R) :
    (zeroPadLeftCircuit (K := K) n m).eval (arithInterpretationWith K constant) y =
      Fin.append (fun _ : Fin n => constant 0) y := by
  funext idx
  induction idx using Fin.addCases with
  | left i =>
    dsimp only [Circuit.eval, zeroPadLeftCircuit, Function.comp_apply]
    rw [Fin.addCases_left, Fin.append_left]
    rfl
  | right k =>
    dsimp only [Circuit.eval, zeroPadLeftCircuit, Function.comp_apply]
    rw [Fin.addCases_right, Fin.append_right]
    rfl

/-- Syntactic transposition of an arithmetic circuit `c : Circuit (arithSignature K) n m` into
`Circuit (arithSignature K) m n`. -/
def transposeCircuit [Zero K] [One K] {n m : ℕ}
    (c : Circuit (arithSignature K) n m) : Circuit (arithSignature K) m n :=
  let cX : Circuit (arithSignature K) (n + m) m := c.mapInputs (Fin.castAdd m)
  let wY : Circuit (arithSignature K) (n + m) m :=
    Circuit.wiring (arithSignature K) (Fin.natAdd n)
  let bilinear : Circuit (arithSignature K) (n + m) 1 :=
    (bilinearDotCircuit (K := K) m).comp (cX.append wY)
  let grad : Circuit (arithSignature K) (n + m) n :=
    (bilinear.withGradient 0 1 0).comapOutputs fun i : Fin n =>
      Fin.natAdd 1 (Fin.castAdd m i)
  grad.comp (zeroPadLeftCircuit (K := K) n m)

/-- Size bound for `transposeCircuit c`: at most `5 * c.size + 10 * m + 8` gates. -/
theorem size_transposeCircuit_le [Zero K] [One K] {n m : ℕ}
    (c : Circuit (arithSignature K) n m) :
    (transposeCircuit c).size ≤ 5 * c.size + 10 * m + 8 := by
  dsimp only [transposeCircuit]
  rw [Circuit.size_comp, size_zeroPadLeftCircuit, Circuit.comapOutputs_size]
  have hbil : ((bilinearDotCircuit (K := K) m).comp
      ((c.mapInputs (Fin.castAdd m)).append
        (Circuit.wiring (arithSignature K) (Fin.natAdd n)))).size = c.size + 2 * m + 1 := by
    simp only [Circuit.size_comp, Circuit.size_append, Circuit.mapInputs_size,
      Circuit.size_wiring, size_bilinearDotCircuit]
    omega
  have hgrad := Circuit.size_withGradient_le
    ((bilinearDotCircuit (K := K) m).comp
      ((c.mapInputs (Fin.castAdd m)).append
        (Circuit.wiring (arithSignature K) (Fin.natAdd n)))) 0 (1 : K) (0 : K)
  rw [hbil] at hgrad
  omega

section CommSemiring

variable [CommSemiring K]

private theorem polynomial_bilinear_helper {n m : ℕ} (c : Circuit (arithSignature K) n m) :
    ((bilinearDotCircuit (K := K) m).comp
      ((c.mapInputs (Fin.castAdd m)).append
        (Circuit.wiring (arithSignature K) (Fin.natAdd n)))).polynomial 0 =
      ∑ k : Fin m,
        aeval (fun i : Fin n => (X (Fin.castAdd m i) : MvPolynomial (Fin (n + m)) K))
          (c.polynomial k) * X (Fin.natAdd n k) := by
  dsimp only [Circuit.polynomial]
  rw [Circuit.eval_comp, eval_bilinearDotCircuit C (map_zero C)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Circuit.eval_append, Fin.append_left, Fin.append_right, Circuit.eval_mapInputs,
    Circuit.eval_wiring]
  congr 1
  exact (c.aeval_polynomial_mvPolynomial (fun i => X (Fin.castAdd m i)) k).symm

private theorem pderiv_castAdd_linear {n m : ℕ} (row : Fin n → K) (i : Fin n) :
    pderiv (Fin.castAdd m i)
      (aeval (fun j : Fin n => (X (Fin.castAdd m j) : MvPolynomial (Fin (n + m)) K))
        (∑ j : Fin n, MvPolynomial.C (row j) * (X j : MvPolynomial (Fin n) K))) =
      MvPolynomial.C (row i) := by
  classical
  simp only [_root_.map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X]
  have hterm : ∀ j : Fin n,
      pderiv (Fin.castAdd m i)
        (MvPolynomial.C (row j) * (X (Fin.castAdd m j) : MvPolynomial (Fin (n + m)) K)) =
        if j = i then MvPolynomial.C (row j) else 0 := by
    intro j
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X, smul_eq_mul]
    by_cases hji : j = i
    · subst hji
      simp [Pi.single_eq_same]
    · simp [hji]
  simp_rw [hterm]
  simp

/-- **Formal Transposition Principle**: if `c` formally computes the linear forms of `A`, then
`transposeCircuit c` formally computes the linear forms of `Aᵀ`. -/
theorem polynomial_transposeCircuit {n m : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (c : Circuit (arithSignature K) n m)
    (hc : ∀ k : Fin m,
      c.polynomial k = ∑ i : Fin n, MvPolynomial.C (A k i) * MvPolynomial.X i)
    (i : Fin n) :
    (transposeCircuit c).polynomial i =
      ∑ k : Fin m, MvPolynomial.C (Aᵀ i k) * MvPolynomial.X k := by
  classical
  set bil : Circuit (arithSignature K) (n + m) 1 :=
    (bilinearDotCircuit (K := K) m).comp
      ((c.mapInputs (Fin.castAdd m)).append
        (Circuit.wiring (arithSignature K) (Fin.natAdd n)))
  set gradFull : Circuit (arithSignature K) (n + m) (1 + (n + m)) :=
    bil.withGradient 0 1 0
  have hgrad_poly : gradFull.polynomial (Fin.natAdd 1 (Fin.castAdd m i)) =
      ∑ k : Fin m, MvPolynomial.C (A k i) * X (Fin.natAdd n k) := by
    rw [Circuit.polynomial_withGradient_natAdd, map_one, one_mul, polynomial_bilinear_helper]
    simp_rw [hc]
    rw [_root_.map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz]
    have hne : Fin.natAdd n k ≠ Fin.castAdd m i := fun h => by
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    have hpX : pderiv (Fin.castAdd m i) (X (Fin.natAdd n k) : MvPolynomial (Fin (n + m)) K) =
        0 := by
      rw [pderiv_X, Pi.single_eq_of_ne hne]
    rw [hpX, smul_zero, zero_add, pderiv_castAdd_linear (A k) i, smul_eq_mul, mul_comm]
  have hcomp : (transposeCircuit c).polynomial i =
      aeval (Fin.append (fun _ : Fin n => (0 : MvPolynomial (Fin m) K)) X)
        (gradFull.polynomial (Fin.natAdd 1 (Fin.castAdd m i))) := by
    change ((gradFull.comapOutputs fun j : Fin n => Fin.natAdd 1 (Fin.castAdd m j)).comp
      (zeroPadLeftCircuit (K := K) n m)).eval (arithInterpretationWith K C) X i = _
    rw [Circuit.eval_comp, Circuit.eval_comapOutputs, Function.comp_apply,
      eval_zeroPadLeftCircuit C n m X]
    simpa only [map_zero] using
      (gradFull.aeval_polynomial_mvPolynomial
        (Fin.append (fun _ : Fin n => (0 : MvPolynomial (Fin m) K)) X)
        (Fin.natAdd 1 (Fin.castAdd m i))).symm
  rw [hcomp, hgrad_poly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, aeval_C, algebraMap_eq, aeval_X, Fin.append_right, Matrix.transpose_apply]

/-- Value-level matrix transposition corollary. -/
theorem eval_transposeCircuit {n m : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (c : Circuit (arithSignature K) n m)
    (hc : ∀ k : Fin m,
      c.polynomial k = ∑ i : Fin n, MvPolynomial.C (A k i) * MvPolynomial.X i)
    (y : Fin m → K) :
    (transposeCircuit c).eval (arithInterpretation K) y = Aᵀ *ᵥ y := by
  funext i
  rw [← Circuit.eval_polynomial, polynomial_transposeCircuit A c hc i]
  simp [Matrix.mulVec, dotProduct]

/-- **The Matrix Transposition Principle**: a circuit of size `s` formally computing `x ↦ A *ᵥ x`
yields a circuit of size at most `5 * s + 10 * m + 8` formally computing `y ↦ Aᵀ *ᵥ y`. -/
theorem exists_transpose_mulVec {n m : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (c : Circuit (arithSignature K) n m)
    (hc : ∀ k : Fin m,
      c.polynomial k = ∑ i : Fin n, MvPolynomial.C (A k i) * MvPolynomial.X i) :
    ∃ c' : Circuit (arithSignature K) m n,
      c'.size ≤ 5 * c.size + 10 * m + 8 ∧
      (∀ i : Fin n, c'.polynomial i = ∑ k : Fin m, MvPolynomial.C (Aᵀ i k) * MvPolynomial.X k) ∧
      (∀ y : Fin m → K, c'.eval (arithInterpretation K) y = Aᵀ *ᵥ y) :=
  ⟨transposeCircuit c, size_transposeCircuit_le c, polynomial_transposeCircuit A c hc,
    eval_transposeCircuit A c hc⟩

end CommSemiring

end CslibFrontier.Circuits
