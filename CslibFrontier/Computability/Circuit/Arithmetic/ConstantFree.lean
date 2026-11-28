/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Synthesis
public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.Permanent
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import CslibFrontier.Computability.Circuit.Pi
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Algebra.MvPolynomial.Degrees
import Cslib.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Constant-Free Arithmetic Circuits, Formal Degree, and Valiant Complexity Classes

Defines constant-free arithmetic circuits (`+`, `-`, `×`, `1`), their syntactic formal degree,
coefficient `ℓ¹`-norm bounds, the constant-free circuit size measure `τ`, and bounded- and
unbounded-degree Valiant algebraic complexity classes with and without arbitrary field constants
(`VP_nb`, `VNP_nb`, `VΠP`, `VP^0`, `VP^0_nb`, `VNP^0`, `VNP^0_nb`, `VΠP^0`, and `VPnbHalf`).

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.ConstFreeOp`, `constFreeSignature`, `constFreeInterp`:
  constant-free arithmetic circuits over an arbitrary ring.
* `CslibFrontier.Circuits.Arithmetic.formalDegreeInterp`, `formalDegree`: syntactic formal degree
  of a constant-free arithmetic circuit.
* `CslibFrontier.Circuits.Arithmetic.constFreePoly`: formal multivariate integer polynomial
  computed by a constant-free circuit.
* `CslibFrontier.Circuits.Arithmetic.tau`, `TauPolyBounded`: smallest constant-free circuit size
  and polynomially bounded `τ`-complexity families.
* `CslibFrontier.Circuits.Arithmetic.booleanProd`, `VPnb`, `VNPnb`, `VPiP`, `VP0`, `VP0nb`,
  `VNP0`, `VNP0nb`, `VPiP0`, `VPnbHalf`: algebraic circuit complexity classes.

## Main results

* `CslibFrontier.Circuits.Arithmetic.totalDegree_constFreePoly_le_formalDegree`: total degree is
  bounded by syntactic formal degree.
* `CslibFrontier.Circuits.Arithmetic.formalDegree_le_two_pow_size`,
  `l1Norm_constFreePoly_le`, `coeff_natAbs_constFreePoly_le`: exponential degree and
  doubly-exponential coefficient bounds from circuit size.
* `CslibFrontier.Circuits.Arithmetic.permFamily_mem_VNP0`: the generic permanent family lies in
  `VNP^0`.
* `CslibFrontier.Circuits.Arithmetic.tauPolyBounded_permFamily_of_VNP0_subset_VP0nb`,
  `tauPolyBounded_permFamily_of_VP0_eq_VNP0`: collapse implications for the `τ`-complexity of the
  permanent.
* `CslibFrontier.Circuits.Arithmetic.exists_constFreeCircuit_pow_two_pow`,
  `exists_constFreeCircuit_two_pow_two_pow`, `exists_halfCircuit_inv_two_pow`: repeated squaring
  constructions.
-/

public section

namespace CslibFrontier.Circuits.Arithmetic

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Constant-free arithmetic circuits and formal degree -/

/-- Operations of a constant-free arithmetic circuit: addition, subtraction, multiplication,
and the sole constant `1`. -/
inductive ConstFreeOp : Type
  /-- Binary addition gate `+`. -/
  | add
  /-- Binary subtraction gate `-`. -/
  | sub
  /-- Binary multiplication gate `×`. -/
  | mul
  /-- Nullary constant gate `1`. -/
  | one
  deriving DecidableEq

/-- Arity of each constant-free arithmetic gate. -/
abbrev ConstFreeOp.arity : ConstFreeOp → ℕ
  | .add => 2
  | .sub => 2
  | .mul => 2
  | .one => 0

/-- Signature of constant-free arithmetic circuits. -/
abbrev constFreeSignature : Signature.{0} where
  Op := ConstFreeOp
  Arity := ConstFreeOp.arity

/-- Standard interpretation of constant-free arithmetic gates in any ring `R`. -/
@[expose] def constFreeInterp (R : Type*) [Ring R] : Interpretation constFreeSignature R
  | .add, x => x 0 + x 1
  | .sub, x => x 0 - x 1
  | .mul, x => x 0 * x 1
  | .one, _ => 1

/-- Evaluation of `constFreeInterp` on `.add`. -/
@[simp] theorem constFreeInterp_add {R : Type*} [Ring R] (x : Fin 2 → R) :
    constFreeInterp R .add x = x 0 + x 1 := rfl

/-- Evaluation of `constFreeInterp` on `.sub`. -/
@[simp] theorem constFreeInterp_sub {R : Type*} [Ring R] (x : Fin 2 → R) :
    constFreeInterp R .sub x = x 0 - x 1 := rfl

/-- Evaluation of `constFreeInterp` on `.mul`. -/
@[simp] theorem constFreeInterp_mul {R : Type*} [Ring R] (x : Fin 2 → R) :
    constFreeInterp R .mul x = x 0 * x 1 := rfl

/-- Evaluation of `constFreeInterp` on `.one`. -/
@[simp] theorem constFreeInterp_one {R : Type*} [Ring R] (x : Fin 0 → R) :
    constFreeInterp R .one x = 1 := rfl

/-- Formal-degree interpretation on `ℕ`: inputs and `1` have
formal degree `1`, `+` and `-` take the maximum, and `×` takes the sum. -/
@[expose] def formalDegreeInterp : Interpretation constFreeSignature ℕ
  | .add, x => max (x 0) (x 1)
  | .sub, x => max (x 0) (x 1)
  | .mul, x => x 0 + x 1
  | .one, _ => 1

/-- Product interpretation tracking both the formal polynomial and its formal degree. -/
@[expose] noncomputable def constFreeWithDegInterp (n : ℕ) :
    Interpretation constFreeSignature (MvPolynomial (Fin n) ℤ × ℕ)
  | .add, x => ((x 0).1 + (x 1).1, max (x 0).2 (x 1).2)
  | .sub, x => ((x 0).1 - (x 1).1, max (x 0).2 (x 1).2)
  | .mul, x => ((x 0).1 * (x 1).1, (x 0).2 + (x 1).2)
  | .one, _ => (1, 1)

/-- Evaluation of `constFreeWithDegInterp` on `.add`. -/
@[simp] theorem constFreeWithDegInterp_add {n : ℕ}
    (x : Fin 2 → MvPolynomial (Fin n) ℤ × ℕ) :
    constFreeWithDegInterp n .add x = ((x 0).1 + (x 1).1, max (x 0).2 (x 1).2) := rfl

/-- Evaluation of `constFreeWithDegInterp` on `.sub`. -/
@[simp] theorem constFreeWithDegInterp_sub {n : ℕ}
    (x : Fin 2 → MvPolynomial (Fin n) ℤ × ℕ) :
    constFreeWithDegInterp n .sub x = ((x 0).1 - (x 1).1, max (x 0).2 (x 1).2) := rfl

/-- Evaluation of `constFreeWithDegInterp` on `.mul`. -/
@[simp] theorem constFreeWithDegInterp_mul {n : ℕ}
    (x : Fin 2 → MvPolynomial (Fin n) ℤ × ℕ) :
    constFreeWithDegInterp n .mul x = ((x 0).1 * (x 1).1, (x 0).2 + (x 1).2) := rfl

/-- Evaluation of `constFreeWithDegInterp` on `.one`. -/
@[simp] theorem constFreeWithDegInterp_one {n : ℕ}
    (x : Fin 0 → MvPolynomial (Fin n) ℤ × ℕ) :
    constFreeWithDegInterp n .one x = (1, 1) := rfl

/-- Formal degree of output `j` of a constant-free arithmetic circuit
defined inductively along the circuit DAG. -/
def formalDegree {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) : ℕ :=
  c.eval formalDegreeInterp (fun _ => 1) j

/-- Formal multivariate polynomial over `ℤ` computed at output `j` of a constant-free
arithmetic circuit. -/
noncomputable def constFreePoly {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) :
    MvPolynomial (Fin n) ℤ :=
  c.eval (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X j

/-- Evaluating the formal polynomial of a constant-free circuit at a point in any commutative ring
`R` agrees with evaluating the circuit directly in `R`. -/
theorem aeval_constFreePoly {R : Type*} [CommRing R] {n m : ℕ}
    (c : Circuit constFreeSignature n m) (x : Fin n → R) (j : Fin m) :
    MvPolynomial.aeval x (constFreePoly c j) = c.eval (constFreeInterp R) x j := by
  let h : Homomorphism (constFreeInterp (MvPolynomial (Fin n) ℤ)) (constFreeInterp R) :=
    ⟨MvPolynomial.aeval x, fun op args => by
      cases op <;> simp [constFreeInterp, map_add, map_sub, map_mul, map_one]⟩
  refine (congrFun (c.map_eval h MvPolynomial.X) j).trans ?_
  congr 1
  funext i
  exact MvPolynomial.aeval_X x i

/-- Evaluating the formal polynomial of a constant-free circuit over `ℤ` agrees with evaluating
the circuit in `ℤ`. -/
@[simp] theorem eval_constFreePoly {n m : ℕ} (c : Circuit constFreeSignature n m)
    (x : Fin n → ℤ) (j : Fin m) :
    MvPolynomial.eval x (constFreePoly c j) = c.eval (constFreeInterp ℤ) x j := by
  simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using aeval_constFreePoly c x j

/-- Composing constant-free circuits substitutes the formal polynomials of the inner circuit
into the formal polynomial of the outer circuit. -/
theorem constFreePoly_comp {n m p : ℕ} (d : Circuit constFreeSignature m p)
    (c : Circuit constFreeSignature n m) (j : Fin p) :
    constFreePoly (d.comp c) j =
      MvPolynomial.aeval (fun i => constFreePoly c i) (constFreePoly d j) := by
  rw [constFreePoly, Circuit.eval_comp]
  exact (aeval_constFreePoly d (fun i => constFreePoly c i) j).symm

/-- Mapping the input variables of a constant-free circuit renames the computed polynomial. -/
theorem constFreePoly_mapInputs {n n' m : ℕ} (f : Fin n → Fin n')
    (c : Circuit constFreeSignature n m) (j : Fin m) :
    constFreePoly (c.mapInputs f) j = MvPolynomial.rename f (constFreePoly c j) := by
  let h : Homomorphism (constFreeInterp (MvPolynomial (Fin n) ℤ))
      (constFreeInterp (MvPolynomial (Fin n') ℤ)) :=
    ⟨MvPolynomial.rename f, fun op args => by
      cases op <;> simp [constFreeInterp, map_add, map_sub, map_mul, map_one]⟩
  rw [constFreePoly, Circuit.eval_mapInputs, constFreePoly]
  have hX : (MvPolynomial.X ∘ f : Fin n → MvPolynomial (Fin n') ℤ) = h.map ∘ MvPolynomial.X :=
    funext fun i => (MvPolynomial.rename_X f i).symm
  rw [hX]
  exact (congrFun (c.map_eval h MvPolynomial.X) j).symm

/-- Mapping input variables leaves formal degree unchanged. -/
@[simp] theorem formalDegree_mapInputs {n n' m : ℕ} (f : Fin n → Fin n')
    (c : Circuit constFreeSignature n m) (j : Fin m) :
    formalDegree (c.mapInputs f) j = formalDegree c j := by
  simp [formalDegree, Circuit.eval_mapInputs, Function.comp_def]

/-- First projection from `constFreeWithDegInterp` recovers `constFreePoly`. -/
theorem fst_eval_constFreeWithDegInterp {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) :
    (c.eval (constFreeWithDegInterp n) (fun i => (MvPolynomial.X i, 1)) j).1 =
      constFreePoly c j := by
  let h : Homomorphism (constFreeWithDegInterp n)
      (constFreeInterp (MvPolynomial (Fin n) ℤ)) :=
    ⟨Prod.fst, fun op _ => by cases op <;> rfl⟩
  exact congrFun (c.map_eval h (fun i => (MvPolynomial.X i, 1))) j

/-- Second projection from `constFreeWithDegInterp` recovers `formalDegree`. -/
theorem snd_eval_constFreeWithDegInterp {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) :
    (c.eval (constFreeWithDegInterp n) (fun i => (MvPolynomial.X i, 1)) j).2 =
      formalDegree c j := by
  let h : Homomorphism (constFreeWithDegInterp n) formalDegreeInterp :=
    ⟨Prod.snd, fun op _ => by cases op <;> rfl⟩
  exact congrFun (c.map_eval h (fun i => (MvPolynomial.X i, 1))) j

/-! ### Degree and coefficient-norm bounds from circuit size -/

/-- Every wire of a constant-free circuit has formal degree at least `1`. -/
theorem one_le_formalDegree {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) :
    1 ≤ formalDegree c j := by
  refine Program.wire_induction c.program
    (P := fun w => 1 ≤ c.program.trace formalDegreeInterp (fun _ => 1) w)
    (fun _ => le_rfl) (fun k ih => ?_) (c.outputs j)
  rw [Program.trace_gate]
  generalize c.program.lines k = l at ih ⊢
  rcases l with ⟨op, wires⟩
  cases op with
  | add => exact le_max_of_le_left (ih 0)
  | sub => exact le_max_of_le_left (ih 0)
  | mul => exact Nat.le_add_right_of_le (ih 0)
  | one => exact le_rfl

/-- Total degree of the polynomial computed by a constant-free circuit is bounded by its formal
degree. -/
theorem totalDegree_constFreePoly_le_formalDegree {n m : ℕ}
    (c : Circuit constFreeSignature n m) (j : Fin m) :
    (constFreePoly c j).totalDegree ≤ formalDegree c j := by
  refine Program.wire_induction c.program
    (P := fun w =>
      (c.program.trace (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X w).totalDegree ≤
        c.program.trace formalDegreeInterp (fun _ => 1) w)
    (fun i => by
      simp only [Program.trace_input, MvPolynomial.totalDegree_X, le_refl])
    (fun k ih => ?_) (c.outputs j)
  rw [Program.trace_gate, Program.trace_gate]
  generalize c.program.lines k = l at ih ⊢
  rcases l with ⟨op, wires⟩
  cases op with
  | add =>
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max (ih 0) (ih 1))
  | sub =>
    rw [constFreeInterp, sub_eq_add_neg]
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    have hneg : (-c.program.trace (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X
        (wires 1)).totalDegree =
        (c.program.trace (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X
        (wires 1)).totalDegree := by
      classical
      simp only [MvPolynomial.totalDegree]
      congr 1
      ext m
      simp [MvPolynomial.mem_support_iff]
    rw [hneg]
    exact max_le_max (ih 0) (ih 1)
  | mul =>
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (ih 0) (ih 1))
  | one =>
    simp [constFreeInterp, formalDegreeInterp]

private theorem trace_formalDegree_le {n g : ℕ} (p : Program constFreeSignature n g)
    (w : Wire n g) :
    p.trace formalDegreeInterp (fun _ => 1) w ≤
      match w with
      | .input _ => 1
      | .gate k => 2 ^ (k.val + 1) := by
  refine Program.wire_induction p
    (P := fun w => p.trace formalDegreeInterp (fun _ => 1) w ≤
      match w with
      | .input _ => 1
      | .gate k => 2 ^ (k.val + 1))
    (fun i => le_rfl) (fun k ih => ?_) w
  rw [Program.trace_gate]
  have hlt (s : Fin (constFreeSignature.Arity (p.lines k).op)) :
      p.trace formalDegreeInterp (fun _ => 1) ((p.lines k).wires s) ≤ 2 ^ k.val := by
    have hs := ih s
    cases hw : (p.lines k).wires s with
    | input i =>
      rw [hw] at hs
      exact hs.trans Nat.one_le_two_pow
    | gate j =>
      rw [hw] at hs
      have hjk : j.val + 1 ≤ k.val := p.lt_of_lines_wires_eq_gate k s j hw
      exact hs.trans (Nat.pow_le_pow_right (by omega) hjk)
  generalize p.lines k = l at hlt ⊢
  rcases l with ⟨op, wires⟩
  cases op with
  | add =>
    exact (max_le (hlt 0) (hlt 1)).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
  | sub =>
    exact (max_le (hlt 0) (hlt 1)).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
  | mul =>
    change _ + _ ≤ 2 ^ (k.val + 1)
    rw [pow_succ, mul_two]
    exact Nat.add_le_add (hlt 0) (hlt 1)
  | one =>
    exact Nat.one_le_two_pow

/-- Formal degree of a constant-free circuit is at most `2 ^ c.size`. -/
theorem formalDegree_le_two_pow_size {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) :
    formalDegree c j ≤ 2 ^ c.size := by
  change c.program.trace formalDegreeInterp (fun _ => 1) (c.outputs j) ≤ 2 ^ c.size
  have h := trace_formalDegree_le c.program (c.outputs j)
  cases hw : c.outputs j with
  | input i =>
    rw [hw] at h
    exact h.trans Nat.one_le_two_pow
  | gate k =>
    rw [hw] at h
    exact h.trans (Nat.pow_le_pow_right (by omega) k.isLt)

/-- Total degree of a constant-free circuit's polynomial is at most `2 ^ c.size`. -/
theorem totalDegree_constFreePoly_le_two_pow_size {n m : ℕ}
    (c : Circuit constFreeSignature n m) (j : Fin m) :
    (constFreePoly c j).totalDegree ≤ 2 ^ c.size :=
  (totalDegree_constFreePoly_le_formalDegree c j).trans (formalDegree_le_two_pow_size c j)

/-- The `ℓ¹` coefficient norm `∑ m, |coeff m p|` of an integer multivariate polynomial. -/
noncomputable def l1Norm {σ : Type*} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

/-- Every coefficient has magnitude bounded by the `ℓ¹` norm. -/
theorem coeff_natAbs_le_l1Norm {σ : Type*} (p : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (p.coeff m).natAbs ≤ l1Norm p := by
  classical
  rw [l1Norm]
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun k => (p.coeff k).natAbs) (fun _ _ => Nat.zero_le _) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    simp

/-- `ℓ¹` norm of `0` is `0`. -/
@[simp] theorem l1Norm_zero {σ : Type*} : l1Norm (0 : MvPolynomial σ ℤ) = 0 := by
  simp [l1Norm]

/-- `ℓ¹` norm of `1` is `1`. -/
@[simp] theorem l1Norm_one {σ : Type*} : l1Norm (1 : MvPolynomial σ ℤ) = 1 := by
  classical
  rw [l1Norm, show (1 : MvPolynomial σ ℤ) = MvPolynomial.C 1 from (map_one MvPolynomial.C).symm,
    MvPolynomial.support_C]
  simp

/-- `ℓ¹` norm of a variable `X i` is `1`. -/
@[simp] theorem l1Norm_X {σ : Type*} (i : σ) :
    l1Norm (MvPolynomial.X i : MvPolynomial σ ℤ) = 1 := by
  classical
  rw [l1Norm, MvPolynomial.support_X]
  simp

/-- Subadditivity of `ℓ¹` norm under addition. -/
theorem l1Norm_add_le {σ : Type*} (p q : MvPolynomial σ ℤ) :
    l1Norm (p + q) ≤ l1Norm p + l1Norm q := by
  classical
  have hsub : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  calc
    l1Norm (p + q) ≤ ∑ m ∈ p.support ∪ q.support, ((p + q).coeff m).natAbs :=
      Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ m ∈ p.support ∪ q.support, ((p.coeff m).natAbs + (q.coeff m).natAbs) := by
      refine Finset.sum_le_sum fun m _ => ?_
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      exact Int.natAbs_add_le _ _
    _ = (∑ m ∈ p.support ∪ q.support, (p.coeff m).natAbs) +
        (∑ m ∈ p.support ∪ q.support, (q.coeff m).natAbs) := Finset.sum_add_distrib
    _ = l1Norm p + l1Norm q := by
      rw [l1Norm, l1Norm]
      congr 1
      · exact (Finset.sum_subset Finset.subset_union_left fun m _ hm => by
          rw [MvPolynomial.notMem_support_iff.mp hm]; rfl).symm
      · exact (Finset.sum_subset Finset.subset_union_right fun m _ hm => by
          rw [MvPolynomial.notMem_support_iff.mp hm]; rfl).symm

/-- Subadditivity of `ℓ¹` norm under finite sums. -/
theorem l1Norm_sum_le {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1Norm_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- `ℓ¹` norm is invariant under negation. -/
@[simp] theorem l1Norm_neg {σ : Type*} (p : MvPolynomial σ ℤ) : l1Norm (-p) = l1Norm p := by
  classical
  have hsupp : (-p).support = p.support := by
    ext m
    simp [MvPolynomial.mem_support_iff]
  simp [l1Norm, hsupp]

/-- Subadditivity of `ℓ¹` norm under subtraction. -/
theorem l1Norm_sub_le {σ : Type*} (p q : MvPolynomial σ ℤ) :
    l1Norm (p - q) ≤ l1Norm p + l1Norm q := by
  rw [sub_eq_add_neg]
  exact (l1Norm_add_le p (-q)).trans_eq (by rw [l1Norm_neg])

private theorem l1Norm_monomial_mul_le {σ : Type*} (m : σ →₀ ℕ) (a : ℤ) (q : MvPolynomial σ ℤ) :
    l1Norm (MvPolynomial.monomial m a * q) ≤ a.natAbs * l1Norm q := by
  classical
  have hmul : MvPolynomial.monomial m a * q =
      ∑ k ∈ q.support, MvPolynomial.monomial (m + k) (a * q.coeff k) := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MvPolynomial.monomial_mul_monomial]
  rw [hmul]
  refine (l1Norm_sum_le q.support _).trans ?_
  rw [l1Norm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h0 : a * q.coeff k = 0
  · simp [h0]
  · have hsupp : (MvPolynomial.monomial (m + k) (a * q.coeff k)).support = {m + k} := by
      ext u
      simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, Finset.mem_singleton]
      constructor
      · intro h
        split_ifs at h with hEq
        · exact hEq.symm
        · exact absurd rfl h
      · rintro rfl
        simp [h0]
    simp [l1Norm, hsupp, Int.natAbs_mul]

/-- Submultiplicativity of `ℓ¹` norm under multiplication. -/
theorem l1Norm_mul_le {σ : Type*} (p q : MvPolynomial σ ℤ) :
    l1Norm (p * q) ≤ l1Norm p * l1Norm q := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.sum_mul]
  refine (l1Norm_sum_le p.support _).trans ?_
  rw [l1Norm, Finset.sum_mul]
  exact Finset.sum_le_sum fun m _ => l1Norm_monomial_mul_le m (p.coeff m) q

private theorem trace_l1Norm_le {n g : ℕ} (p : Program constFreeSignature n g) (w : Wire n g) :
    l1Norm (p.trace (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X w) ≤
      match w with
      | .input _ => 1
      | .gate k => 2 ^ (2 ^ (k.val + 1)) := by
  refine Program.wire_induction p
    (P := fun w => l1Norm (p.trace (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X w) ≤
      match w with
      | .input _ => 1
      | .gate k => 2 ^ (2 ^ (k.val + 1)))
    (fun i => by simp only [Program.trace_input, l1Norm_X, le_refl]) (fun k ih => ?_) w
  rw [Program.trace_gate]
  have hlt (s : Fin (constFreeSignature.Arity (p.lines k).op)) :
      l1Norm (p.trace (constFreeInterp (MvPolynomial (Fin n) ℤ))
        MvPolynomial.X ((p.lines k).wires s)) ≤ 2 ^ (2 ^ k.val) := by
    have hs := ih s
    cases hw : (p.lines k).wires s with
    | input i =>
      rw [hw] at hs
      exact hs.trans Nat.one_le_two_pow
    | gate j =>
      rw [hw] at hs
      have hjk : j.val + 1 ≤ k.val := p.lt_of_lines_wires_eq_gate k s j hw
      exact hs.trans (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hjk))
  have h2pow : 2 ^ (2 ^ k.val) + 2 ^ (2 ^ k.val) ≤ 2 ^ (2 ^ (k.val + 1)) := by
    have hmul : 2 ^ (2 ^ k.val) * 2 ^ (2 ^ k.val) = 2 ^ (2 ^ (k.val + 1)) := by
      rw [← pow_add, pow_succ, mul_two]
    have hge2 : 2 ≤ 2 ^ (2 ^ k.val) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (2 ^ k.val) := Nat.pow_le_pow_right (by omega) Nat.one_le_two_pow
    rw [← hmul]
    nlinarith
  generalize p.lines k = l at hlt ⊢
  rcases l with ⟨op, wires⟩
  cases op with
  | add =>
    exact (l1Norm_add_le _ _).trans ((Nat.add_le_add (hlt 0) (hlt 1)).trans h2pow)
  | sub =>
    exact (l1Norm_sub_le _ _).trans ((Nat.add_le_add (hlt 0) (hlt 1)).trans h2pow)
  | mul =>
    refine (l1Norm_mul_le _ _).trans ((Nat.mul_le_mul (hlt 0) (hlt 1)).trans ?_)
    rw [← pow_add, ← two_mul, mul_comm 2, ← pow_succ]
  | one =>
    simpa only [constFreeInterp, l1Norm_one] using Nat.one_le_two_pow

/-- The `ℓ¹` coefficient norm of a constant-free circuit is at most `2 ^ (2 ^ c.size)`. -/
theorem l1Norm_constFreePoly_le {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m) :
    l1Norm (constFreePoly c j) ≤ 2 ^ (2 ^ c.size) := by
  change l1Norm (c.program.trace (constFreeInterp (MvPolynomial (Fin n) ℤ)) MvPolynomial.X
    (c.outputs j)) ≤ 2 ^ (2 ^ c.size)
  have h := trace_l1Norm_le c.program (c.outputs j)
  cases hw : c.outputs j with
  | input i =>
    rw [hw] at h
    exact h.trans Nat.one_le_two_pow
  | gate k =>
    rw [hw] at h
    exact h.trans (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) k.isLt))

/-- Every coefficient of a constant-free circuit's polynomial has magnitude at most
`2 ^ (2 ^ c.size)`. -/
theorem coeff_natAbs_constFreePoly_le {n m : ℕ} (c : Circuit constFreeSignature n m) (j : Fin m)
    (mon : Fin n →₀ ℕ) :
    ((constFreePoly c j).coeff mon).natAbs ≤ 2 ^ (2 ^ c.size) :=
  (coeff_natAbs_le_l1Norm _ mon).trans (l1Norm_constFreePoly_le c j)

/-- Evaluation magnitude bound from `ℓ¹` norm, degree, and input bound. -/
theorem eval_natAbs_le_l1Norm_mul_pow {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ)
    {B : ℕ} (hB : 1 ≤ B) (hx : ∀ i, (x i).natAbs ≤ B) :
    (MvPolynomial.eval x p).natAbs ≤ l1Norm p * B ^ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  have hsum : (∑ m ∈ p.support, MvPolynomial.eval x (MvPolynomial.monomial m (p.coeff m))).natAbs ≤
      ∑ m ∈ p.support, (MvPolynomial.eval x (MvPolynomial.monomial m (p.coeff m))).natAbs := by
    induction p.support using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
  refine hsum.trans ?_
  rw [l1Norm, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [MvPolynomial.eval_monomial, Int.natAbs_mul]
  refine Nat.mul_le_mul_left _ ?_
  have hprod : (m.prod fun i e => x i ^ e).natAbs ≤ B ^ (m.sum fun _ e => e) := by
    rw [Finsupp.prod, Finsupp.sum]
    have hnat : ∀ (s : Finset (Fin n)),
        (∏ i ∈ s, x i ^ m i).natAbs ≤ ∏ i ∈ s, B ^ m i := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, Int.natAbs_pow]
        exact Nat.mul_le_mul (Nat.pow_le_pow_left (hx a) _) ih
    exact (hnat m.support).trans_eq (Finset.prod_pow_eq_pow_sum m.support (fun i => m i) B)
  exact hprod.trans (Nat.pow_le_pow_right hB (MvPolynomial.le_totalDegree hm))

/-! ### Constant-free synthesis rules and `τ(f)` -/

section ConstFreeSynthesis

variable {n : ℕ} {R : Type*} [Ring R]

/-- Synthesize constant `1` in a constant-free circuit using 1 gate. -/
theorem synthesis_cf_one {s : Set ((Fin n → R) → R)} :
    Synthesis (constFreeInterp R) s {fun _ => 1} 1 :=
  Synthesis.gate (σ := constFreeSignature) .one (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- Synthesize addition in a constant-free circuit using 1 gate. -/
theorem synthesis_cf_add {s : Set ((Fin n → R) → R)} {f g : (Fin n → R) → R}
    (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (constFreeInterp R) s {fun x => f x + g x} 1 :=
  Synthesis.gate (σ := constFreeSignature) .add ![f, g] fun i => by fin_cases i <;> assumption

/-- Synthesize subtraction in a constant-free circuit using 1 gate. -/
theorem synthesis_cf_sub {s : Set ((Fin n → R) → R)} {f g : (Fin n → R) → R}
    (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (constFreeInterp R) s {fun x => f x - g x} 1 :=
  Synthesis.gate (σ := constFreeSignature) .sub ![f, g] fun i => by fin_cases i <;> assumption

/-- Synthesize multiplication in a constant-free circuit using 1 gate. -/
theorem synthesis_cf_mul {s : Set ((Fin n → R) → R)} {f g : (Fin n → R) → R}
    (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (constFreeInterp R) s {fun x => f x * g x} 1 :=
  Synthesis.gate (σ := constFreeSignature) .mul ![f, g] fun i => by fin_cases i <;> assumption

/-- Synthesize constant `0 = 1 - 1` in a constant-free circuit using 2 gates. -/
theorem synthesis_cf_zero {s : Set ((Fin n → R) → R)} :
    Synthesis (constFreeInterp R) s {fun _ => 0} 2 := by
  have h1 : Synthesis (constFreeInterp R) s {fun _ => (1 : R)} 1 := synthesis_cf_one
  have hsub := synthesis_cf_sub (s := s ∪ {fun _ => (1 : R)}) (f := fun _ => (1 : R))
    (g := fun _ => (1 : R)) (Set.mem_union_right _ rfl) (Set.mem_union_right _ rfl)
  simpa only [sub_self] using h1.trans hsub

/-- Every natural constant `k : ℕ` can be synthesized in a constant-free circuit. -/
theorem synthesis_cf_natCast {s : Set ((Fin n → R) → R)} (k : ℕ) :
    ∃ cost : ℕ, Synthesis (constFreeInterp R) s {fun _ => (k : R)} cost := by
  induction k with
  | zero => exact ⟨2, by simpa using synthesis_cf_zero⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + 2, ?_⟩
    have h1 : Synthesis (constFreeInterp R) (s ∪ {fun _ => (k : R)}) {fun _ => (1 : R)} 1 :=
      synthesis_cf_one
    have hadd : Synthesis (constFreeInterp R)
        (s ∪ ({fun _ => (k : R)} ∪ {fun _ => (1 : R)}))
        {fun _ => (k : R) + 1} 1 :=
      synthesis_cf_add (Set.mem_union_right _ (Set.mem_union_left _ rfl))
        (Set.mem_union_right _ (Set.mem_union_right _ rfl))
    have hcomp := (hc.comp h1).trans hadd
    simpa only [Nat.cast_succ, add_assoc] using hcomp

/-- Every integer constant `z : ℤ` can be synthesized in a constant-free circuit. -/
theorem synthesis_cf_intCast {s : Set ((Fin n → R) → R)} (z : ℤ) :
    ∃ cost : ℕ, Synthesis (constFreeInterp R) s {fun _ => (z : R)} cost := by
  cases z with
  | ofNat k =>
    obtain ⟨c, hc⟩ := synthesis_cf_natCast (R := R) (s := s) k
    exact ⟨c, by simpa using hc⟩
  | negSucc k =>
    obtain ⟨c, hc⟩ := synthesis_cf_natCast (R := R) (s := s) (k + 1)
    refine ⟨c + 3, ?_⟩
    have h0 : Synthesis (constFreeInterp R) (s ∪ {fun _ => ((k + 1 : ℕ) : R)})
        {fun _ => (0 : R)} 2 := synthesis_cf_zero
    have hsub : Synthesis (constFreeInterp R)
        (s ∪ ({fun _ => ((k + 1 : ℕ) : R)} ∪ {fun _ => (0 : R)}))
        {fun _ => (0 : R) - ((k + 1 : ℕ) : R)} 1 :=
      synthesis_cf_sub (Set.mem_union_right _ (Set.mem_union_right _ rfl))
        (Set.mem_union_right _ (Set.mem_union_left _ rfl))
    have hcomp := (hc.comp h0).trans hsub
    simpa [Int.negSucc_eq, add_assoc] using hcomp

/-- Every integer multivariate polynomial is computed by some constant-free arithmetic circuit. -/
theorem exists_constFreeCircuit_of_mvPolynomial (f : MvPolynomial (Fin n) ℤ) :
    ∃ c : Circuit constFreeSignature n 1, constFreePoly c 0 = f := by
  suffices ∃ cost, Synthesis (constFreeInterp (MvPolynomial (Fin n) ℤ)) (inputs n)
      {fun x => MvPolynomial.aeval x f} cost by
    obtain ⟨cost, hsyn⟩ := this
    obtain ⟨c, hc, -⟩ := hsyn.exists_circuit
    refine ⟨c, ?_⟩
    have h0 := congrFun (hc MvPolynomial.X) 0
    simpa [constFreePoly, MvPolynomial.aeval_X_left] using h0
  induction f using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨cost, hc⟩ := synthesis_cf_intCast (R := MvPolynomial (Fin n) ℤ) (s := inputs n) a
    refine ⟨cost, ?_⟩
    simpa [MvPolynomial.aeval_C] using hc
  | add p q ihp ihq =>
    obtain ⟨cp, hp⟩ := ihp
    obtain ⟨cq, hq⟩ := ihq
    refine ⟨cp + cq + 1, ?_⟩
    have hcomb := hp.combine hq (synthesis_cf_add (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ rfl))
    simpa [map_add] using hcomb
  | mul_X p i ihp =>
    obtain ⟨cp, hp⟩ := ihp
    refine ⟨cp + 1, ?_⟩
    have hmul : Synthesis (constFreeInterp (MvPolynomial (Fin n) ℤ))
        (inputs n ∪ {fun x => MvPolynomial.aeval x p})
        {fun x => MvPolynomial.aeval x p * x i} 1 :=
      synthesis_cf_mul (Set.mem_union_right _ rfl) (Set.mem_union_left _ ⟨i, rfl⟩)
    simpa [map_mul, MvPolynomial.aeval_X] using hp.trans hmul

end ConstFreeSynthesis

/-- The constant-free arithmetic circuit complexity `τ(f)` : the size of a
smallest constant-free circuit computing the integer polynomial `f`. -/
noncomputable def tau {n : ℕ} (f : MvPolynomial (Fin n) ℤ) : ℕ :=
  sInf {s : ℕ | ∃ c : Circuit constFreeSignature n 1, constFreePoly c 0 = f ∧ c.size = s}

/-- Upper bound on `τ(f)` from any constant-free circuit computing `f`. -/
theorem tau_le_of_circuit {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    (c : Circuit constFreeSignature n 1) (hc : constFreePoly c 0 = f) :
    tau f ≤ c.size :=
  Nat.sInf_le ⟨c, hc, rfl⟩

/-- Attainment of `τ(f)`: there exists a constant-free circuit of size exactly `τ(f)` computing
`f`. -/
theorem exists_circuit_of_tau {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    ∃ c : Circuit constFreeSignature n 1, constFreePoly c 0 = f ∧ c.size = tau f := by
  have hne : {s : ℕ | ∃ c : Circuit constFreeSignature n 1,
      constFreePoly c 0 = f ∧ c.size = s}.Nonempty := by
    obtain ⟨c, hc⟩ := exists_constFreeCircuit_of_mvPolynomial f
    exact ⟨c.size, c, hc, rfl⟩
  exact Nat.sInf_mem hne

/-- A family of integer polynomials has polynomially bounded `τ`-complexity
(`τ(f_n) = n^{O(1)}`). -/
def TauPolyBounded (f : PolynomialFamily ℤ) : Prop :=
  PolynomiallyBounded fun n => tau (f.poly n)

/-! ### Valiant's bounded- and unbounded-degree classes (with and without constants) -/

/-- The Boolean product `∏ e ∈ {0, 1}^m, P (X, e)` over the last `m` variables . -/
noncomputable def booleanProd {K : Type*} [CommSemiring K] {n : ℕ} (m : ℕ)
    (P : MvPolynomial (Fin (n + m)) K) : MvPolynomial (Fin n) K :=
  ∏ e : Fin m → Bool, projection (booleanAssignment e) P

/-- Unfolding equation for `booleanProd`. -/
theorem booleanProd_eq {K : Type*} [CommSemiring K] {n : ℕ} (m : ℕ)
    (P : MvPolynomial (Fin (n + m)) K) :
    booleanProd m P = ∏ e : Fin m → Bool, projection (booleanAssignment e) P := by
  unfold booleanProd; rfl

/-- A Boolean product over zero variables is the polynomial itself. -/
@[simp] theorem booleanProd_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (P : MvPolynomial (Fin (n + 0)) K) : booleanProd 0 P = P := by
  have h (e : Fin 0 → Bool) : (booleanAssignment e : Fin (n + 0) → Fin n ⊕ K) = Sum.inl :=
    (Fin.append_right_nil _ _ rfl).trans rfl
  rw [booleanProd, Fintype.prod_unique, h, projection_inl]
  rfl

/-- Unbounded-degree class `VP_nb` over `K` : families with polynomially many
variables computed by polynomial-size arithmetic circuits with constants from `K`. -/
def VPnb (K : Type*) [CommSemiring K] : Set (PolynomialFamily K) :=
  {f | PolynomiallyBounded f.vars ∧
    ∃ c : ∀ n, Circuit (arithSignature K) (f.vars n) 1,
      PolynomiallyBounded (fun n => (c n).size) ∧ ∀ n, (c n).polynomial 0 = f.poly n}

/-- Unbounded-degree `VNP_nb` over `K`: exponential Boolean sums of `VP_nb` families. -/
def VNPnb (K : Type*) [CommSemiring K] : Set (PolynomialFamily K) :=
  {f | ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) K),
    (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily K) ∈ VPnb K ∧
      ∀ n, f.poly n = booleanSum (m n) (g n)}

/-- Class `VΠP` over `K` : exponential Boolean products of `VP_nb` families. -/
def VPiP (K : Type*) [CommSemiring K] : Set (PolynomialFamily K) :=
  {f | ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) K),
    (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily K) ∈ VPnb K ∧
      ∀ n, f.poly n = booleanProd (m n) (g n)}

/-- Constant-free degree-bounded class `VP^0` : integer polynomial families
with polynomially many variables computed by constant-free circuits of polynomially bounded
size and formal degree. -/
def VP0 : Set (PolynomialFamily ℤ) :=
  {f | PolynomiallyBounded f.vars ∧
    ∃ c : ∀ n, Circuit constFreeSignature (f.vars n) 1,
      PolynomiallyBounded (fun n => (c n).size) ∧
      PolynomiallyBounded (fun n => formalDegree (c n) 0) ∧
      ∀ n, constFreePoly (c n) 0 = f.poly n}

/-- Constant-free unbounded-degree class `VP^0_nb` : integer polynomial families
with polynomially many variables computed by polynomial-size constant-free circuits. -/
def VP0nb : Set (PolynomialFamily ℤ) :=
  {f | PolynomiallyBounded f.vars ∧
    ∃ c : ∀ n, Circuit constFreeSignature (f.vars n) 1,
      PolynomiallyBounded (fun n => (c n).size) ∧
      ∀ n, constFreePoly (c n) 0 = f.poly n}

/-- Constant-free class `VNP^0` : exponential Boolean sums of `VP^0`
families. -/
def VNP0 : Set (PolynomialFamily ℤ) :=
  {f | ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) ℤ),
    (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily ℤ) ∈ VP0 ∧
      ∀ n, f.poly n = booleanSum (m n) (g n)}

/-- Constant-free unbounded-degree class `VNP^0_nb`: exponential Boolean sums of `VP^0_nb`
families. -/
def VNP0nb : Set (PolynomialFamily ℤ) :=
  {f | ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) ℤ),
    (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily ℤ) ∈ VP0nb ∧
      ∀ n, f.poly n = booleanSum (m n) (g n)}

/-- Constant-free class `VΠP^0` : exponential Boolean products of `VP^0_nb`
families. -/
def VPiP0 : Set (PolynomialFamily ℤ) :=
  {f | ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) ℤ),
    (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily ℤ) ∈ VP0nb ∧
      ∀ n, f.poly n = booleanProd (m n) (g n)}

/-- Characterization of `VP^0_nb` via `τ`-complexity. -/
theorem mem_VP0nb_iff_tauPolyBounded {f : PolynomialFamily ℤ} :
    f ∈ VP0nb ↔ PolynomiallyBounded f.vars ∧ TauPolyBounded f := by
  constructor
  · rintro ⟨hvars, c, hc, hcf⟩
    exact ⟨hvars, hc.mono_of_le fun n => tau_le_of_circuit (c n) (hcf n)⟩
  · rintro ⟨hvars, htau⟩
    choose c hcf hsz using fun n => exists_circuit_of_tau (f.poly n)
    exact ⟨hvars, c, htau.mono_of_le fun n => (hsz n).le, hcf⟩

/-- `VP^0 ⊆ VP^0_nb`. -/
theorem VP0_subset_VP0nb : VP0 ⊆ VP0nb :=
  fun _ ⟨hvars, c, hsize, _, hc⟩ => ⟨hvars, c, hsize, hc⟩

/-- `VP^0 ⊆ VNP^0`. -/
theorem VP0_subset_VNP0 : VP0 ⊆ VNP0 :=
  fun f hf => ⟨fun _ => 0, f.poly, hf, fun n => (booleanSum_zero (f.poly n)).symm⟩

/-- `VP^0_nb ⊆ VNP^0_nb`. -/
theorem VP0nb_subset_VNP0nb : VP0nb ⊆ VNP0nb :=
  fun f hf => ⟨fun _ => 0, f.poly, hf, fun n => (booleanSum_zero (f.poly n)).symm⟩

/-- `VP^0_nb ⊆ VΠP^0`. -/
theorem VP0nb_subset_VPiP0 : VP0nb ⊆ VPiP0 :=
  fun f hf => ⟨fun _ => 0, f.poly, hf, fun n => (booleanProd_zero (f.poly n)).symm⟩

/-! ### The generic permanent lies in `VNP^0` and `τ`-complexity implications -/

private theorem synthesis_deg_one {n : ℕ}
    {s : Set ((Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ)} :
    Synthesis (constFreeWithDegInterp n) s {fun _ => (1, 1)} 1 :=
  Synthesis.gate (σ := constFreeSignature) .one (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

private theorem synthesis_deg_add {n : ℕ}
    {s : Set ((Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ)}
    {f g : (Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ}
    (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (constFreeWithDegInterp n) s
      {fun x => ((f x).1 + (g x).1, max (f x).2 (g x).2)} 1 :=
  Synthesis.gate (σ := constFreeSignature) .add ![f, g] fun i => by fin_cases i <;> assumption

private theorem synthesis_deg_sub {n : ℕ}
    {s : Set ((Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ)}
    {f g : (Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ}
    (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (constFreeWithDegInterp n) s
      {fun x => ((f x).1 - (g x).1, max (f x).2 (g x).2)} 1 :=
  Synthesis.gate (σ := constFreeSignature) .sub ![f, g] fun i => by fin_cases i <;> assumption

private theorem synthesis_deg_mul {n : ℕ}
    {s : Set ((Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ)}
    {f g : (Fin n → MvPolynomial (Fin n) ℤ × ℕ) → MvPolynomial (Fin n) ℤ × ℕ}
    (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (constFreeWithDegInterp n) s
      {fun x => ((f x).1 * (g x).1, (f x).2 + (g x).2)} 1 :=
  Synthesis.gate (σ := constFreeSignature) .mul ![f, g] fun i => by fin_cases i <;> assumption

private theorem exists_constFreeCircuit_ryserPoly (n : ℕ) :
    ∃ c : Circuit constFreeSignature (n * n + n) 1,
      constFreePoly c 0 = ryserPoly ℤ n ∧
      c.size ≤ 2 * n ^ 2 + 4 * n + 4 ∧
      formalDegree c 0 ≤ 3 * n + 2 := by
  let N := n * n + n
  let I := constFreeWithDegInterp N
  let x0 : Fin N → MvPolynomial (Fin N) ℤ × ℕ := fun i => (MvPolynomial.X i, 1)
  have hfold_prod : ∀ {ι : Type} (l : List ι)
      (s : Set ((Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ))
      (F : ι → (Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ)
      (cost : ℕ) (hone : (fun _ => ((1 : MvPolynomial (Fin N) ℤ), 1)) ∈ s)
      (hF : ∀ a ∈ l, Synthesis I s {F a} cost),
      ∃ d : ℕ, d ≤ (l.map (fun a => (F a x0).2)).sum + 1 ∧
        ∃ G : (Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ,
          (G x0).1 = (l.map (fun a => (F a x0).1)).prod ∧
          (G x0).2 = d ∧
          Synthesis I s {G} (l.length * (cost + 1)) := by
    intro ι l s F cost hone hF
    induction l with
    | nil =>
      exact ⟨1, by simp, fun _ => (1, 1), by simp, rfl, by simpa using Synthesis.of_mem hone⟩
    | cons a t ih =>
      obtain ⟨dt, hdt, Gt, hGt1, hGt2, hsyn_t⟩ :=
        ih fun b hb => hF b (List.mem_cons_of_mem a hb)
      have ha : Synthesis I s {F a} cost := hF a (List.mem_cons_self ..)
      refine ⟨(F a x0).2 + dt, ?_, fun x => ((F a x).1 * (Gt x).1, (F a x).2 + (Gt x).2),
        ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]; omega
      · simp [hGt1]
      · simp [hGt2]
      · have hcomb := ha.combine hsyn_t (synthesis_deg_mul (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ rfl))
        refine hcomb.mono Set.Subset.rfl Set.Subset.rfl ?_
        simp only [List.length_cons]
        ring_nf
        omega
  have hfold_sum : ∀ {ι : Type} (l : List ι)
      (s : Set ((Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ))
      (F : ι → (Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ)
      (cost D : ℕ) (hzero : (fun _ => ((0 : MvPolynomial (Fin N) ℤ), 1)) ∈ s)
      (hF : ∀ a ∈ l, Synthesis I s {F a} cost) (hD : ∀ a ∈ l, (F a x0).2 ≤ D),
      ∃ d : ℕ, d ≤ max D 1 ∧
        ∃ G : (Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ,
          (G x0).1 = (l.map (fun a => (F a x0).1)).sum ∧
          (G x0).2 = d ∧
          Synthesis I s {G} (l.length * (cost + 1)) := by
    intro ι l s F cost D hzero hF hD
    induction l with
    | nil =>
      exact ⟨1, le_max_right D 1, fun _ => (0, 1), by simp, rfl,
        by simpa using Synthesis.of_mem hzero⟩
    | cons a t ih =>
      obtain ⟨dt, hdt, Gt, hGt1, hGt2, hsyn_t⟩ :=
        ih (fun b hb => hF b (List.mem_cons_of_mem a hb))
          (fun b hb => hD b (List.mem_cons_of_mem a hb))
      have ha : Synthesis I s {F a} cost := hF a (List.mem_cons_self ..)
      have haD : (F a x0).2 ≤ D := hD a (List.mem_cons_self ..)
      refine ⟨max (F a x0).2 dt, max_le (haD.trans (le_max_left D 1)) hdt,
        fun x => ((F a x).1 + (Gt x).1, max (F a x).2 (Gt x).2), ?_, ?_, ?_⟩
      · simp [hGt1]
      · simp [hGt2]
      · have hcomb := ha.combine hsyn_t (synthesis_deg_add (Set.mem_insert _ _)
          (Set.mem_insert_of_mem _ rfl))
        refine hcomb.mono Set.Subset.rfl Set.Subset.rfl ?_
        simp only [List.length_cons]
        ring_nf
        omega
  -- Build constants (1, 1) and (0, 1) first (cost 2).
  let consts : Set ((Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ) :=
    {fun _ => (1, 1), fun _ => (0, 1)}
  have hconsts : Synthesis I (inputs N) consts 2 := by
    have h1 : Synthesis I (inputs N) {fun _ => (1, 1)} 1 := synthesis_deg_one
    have h0 : Synthesis I (inputs N ∪ {fun _ => (1, 1)}) {fun _ => (0, 1)} 1 := by
      simpa [sub_self] using synthesis_deg_sub (n := N)
        (s := inputs N ∪ {fun _ => (1, 1)})
        (f := fun _ => (1, 1)) (g := fun _ => (1, 1))
        (Set.mem_union_right _ rfl) (Set.mem_union_right _ rfl)
    refine (h1.comp h0).mono Set.Subset.rfl ?_ le_rfl
    dsimp only [consts]
    rw [Set.insert_eq]
  let s := inputs N ∪ consts
  have h1s : (fun _ => ((1 : MvPolynomial (Fin N) ℤ), 1)) ∈ s :=
    Or.inr (Set.mem_insert _ _)
  have h0s : (fun _ => ((0 : MvPolynomial (Fin N) ℤ), 1)) ∈ s :=
    Or.inr (Set.mem_insert_of_mem _ rfl)
  have hxs (i : Fin N) : (fun x : Fin N → MvPolynomial (Fin N) ℤ × ℕ => x i) ∈ s :=
    Or.inl ⟨i, rfl⟩
  -- Sign factor list: for each j, `X (n*n + j) + X (n*n + j) - 1`, cost 2, deg 1.
  let signF (j : Fin n) (x : Fin N → MvPolynomial (Fin N) ℤ × ℕ) : MvPolynomial (Fin N) ℤ × ℕ :=
    ((x (Fin.natAdd (n * n) j)).1 + (x (Fin.natAdd (n * n) j)).1 - 1,
      max (max (x (Fin.natAdd (n * n) j)).2 (x (Fin.natAdd (n * n) j)).2) 1)
  have hsignF (j : Fin n) : Synthesis I s {signF j} 2 := by
    have hadd := synthesis_deg_add (hxs (Fin.natAdd (n * n) j)) (hxs (Fin.natAdd (n * n) j))
    exact hadd.trans (synthesis_deg_sub (Set.mem_union_right _ rfl) (Set.mem_union_left _ h1s))
  obtain ⟨d1, hd1, G1, hG1_val, hG1_deg, hsyn1⟩ :=
    hfold_prod (List.finRange n) s signF 2 h1s (fun j _ => hsignF j)
  -- Row factors: for each i, sum over j of `X (n*n + j) * X (i, j)`, cost 2 * n, deg ≤ 2.
  let termF (i j : Fin n) (x : Fin N → MvPolynomial (Fin N) ℤ × ℕ) :
      MvPolynomial (Fin N) ℤ × ℕ :=
    ((x (Fin.natAdd (n * n) j)).1 * (x (Fin.castAdd n (finProdFinEquiv (i, j)))).1,
      (x (Fin.natAdd (n * n) j)).2 + (x (Fin.castAdd n (finProdFinEquiv (i, j)))).2)
  have hrow_ex (i : Fin n) :
      ∃ d : ℕ, d ≤ 2 ∧
        ∃ R : (Fin N → MvPolynomial (Fin N) ℤ × ℕ) → MvPolynomial (Fin N) ℤ × ℕ,
          (R x0).1 = ∑ j : Fin n,
            (X (Fin.natAdd (n * n) j) : MvPolynomial (Fin N) ℤ) *
              X (Fin.castAdd n (finProdFinEquiv (i, j))) ∧
          (R x0).2 = d ∧
          Synthesis I s {R} (2 * n) := by
    obtain ⟨d, hd, R, hR1, hR2, hsynR⟩ :=
      hfold_sum (List.finRange n) s (termF i) 1 2 h0s
        (fun j _ => synthesis_deg_mul (hxs (Fin.natAdd (n * n) j))
          (hxs (Fin.castAdd n (finProdFinEquiv (i, j)))))
        (fun j _ => by simp [termF, x0])
    refine ⟨d, by omega, R, ?_, hR2, ?_⟩
    · rw [hR1, ← Fin.sum_univ_def]
    · simpa [List.length_finRange, mul_comm] using hsynR
  choose drow hdrow Rrow hRrow_val hRrow_deg hsyn_row using hrow_ex
  obtain ⟨d2, hd2, G2, hG2_val, hG2_deg, hsyn2⟩ :=
    hfold_prod (List.finRange n) s Rrow (2 * n) h1s (fun i _ => hsyn_row i)
  have hfull := hconsts.trans (hsyn1.combine hsyn2
    (synthesis_deg_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)))
  obtain ⟨c, hc, hsize⟩ := hfull.exists_circuit
  refine ⟨c, ?_, ?_, ?_⟩
  · have h0 := congrArg Prod.fst (congrFun (hc x0) 0)
    rw [fst_eval_constFreeWithDegInterp] at h0
    simp only [single_apply] at h0
    rw [h0, hG1_val, hG2_val, ryserPoly]
    congr 1
    · rw [← Fin.prod_univ_def]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [signF, x0, two_mul]
    · rw [← Fin.prod_univ_def]
      refine Finset.prod_congr rfl fun i _ => hRrow_val i
  · refine hsize.trans ?_
    simp only [List.length_finRange]
    nlinarith
  · have h0 := congrArg Prod.snd (congrFun (hc x0) 0)
    rw [snd_eval_constFreeWithDegInterp] at h0
    simp only [single_apply] at h0
    rw [h0, hG1_deg, hG2_deg]
    have hsum1 : (List.map (fun a => (signF a x0).2) (List.finRange n)).sum = n := by
      have : List.map (fun a => (signF a x0).2) (List.finRange n) = List.replicate n 1 := by
        apply List.ext_getElem (by simp)
        intro i hi _
        simp [signF, x0]
      rw [this, List.sum_replicate, smul_eq_mul, mul_one]
    have hsum2 : (List.map (fun a => (Rrow a x0).2) (List.finRange n)).sum ≤ 2 * n := by
      calc (List.map (fun a => (Rrow a x0).2) (List.finRange n)).sum
          ≤ (List.map (fun _ : Fin n => 2) (List.finRange n)).sum :=
            List.sum_le_sum fun i _ => by rw [hRrow_deg]; exact hdrow i
        _ = 2 * n := by simp [List.map_const', mul_comm]
    omega

/-- The generic permanent family belongs to `VNP^0`. -/
theorem permFamily_mem_VNP0 : permFamily ℤ ∈ VNP0 := by
  choose c hpoly hsize hdeg using exists_constFreeCircuit_ryserPoly
  refine ⟨fun n => n, ryserPoly ℤ, ⟨?_, c, ?_, ?_, hpoly⟩,
    fun n => (booleanSum_ryserPoly n).symm⟩
  · change PolynomiallyBounded fun n : ℕ => n * n + n
    fun_prop
  · exact (show PolynomiallyBounded fun n : ℕ => 2 * n ^ 2 + 4 * n + 4 by fun_prop).mono_of_le
      hsize
  · exact (show PolynomiallyBounded fun n : ℕ => 3 * n + 2 by fun_prop).mono_of_le hdeg

/-- `VNP^0 ⊆ VP^0_nb` implies
`τ(PER_n) = n^{O(1)}`. -/
theorem tauPolyBounded_permFamily_of_VNP0_subset_VP0nb (h : VNP0 ⊆ VP0nb) :
    TauPolyBounded (permFamily ℤ) :=
  (mem_VP0nb_iff_tauPolyBounded.mp (h permFamily_mem_VNP0)).2

/-- `VP^0 = VNP^0` implies
`τ(PER_n) = n^{O(1)}`. -/
theorem tauPolyBounded_permFamily_of_VP0_eq_VNP0 (h : VP0 = VNP0) :
    TauPolyBounded (permFamily ℤ) :=
  tauPolyBounded_permFamily_of_VNP0_subset_VP0nb (h ▸ VP0_subset_VP0nb)

/-! ### Repeated squaring circuits -/

/-- Repeated squaring computes `X 0 ^ (2 ^ t)` with a constant-free circuit of size `≤ t`. -/
theorem exists_constFreeCircuit_pow_two_pow (t : ℕ) :
    ∃ c : Circuit constFreeSignature 1 1,
      constFreePoly c 0 = (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℤ) ^ 2 ^ t ∧ c.size ≤ t := by
  suffices Synthesis (constFreeInterp (MvPolynomial (Fin 1) ℤ)) (inputs 1)
      {fun x : Fin 1 → MvPolynomial (Fin 1) ℤ => x 0 ^ 2 ^ t} t by
    obtain ⟨c, hc, hsz⟩ := this.exists_circuit
    exact ⟨c, congrFun (hc MvPolynomial.X) 0, hsz⟩
  induction t with
  | zero =>
    simpa using Synthesis.of_mem (I := constFreeInterp (MvPolynomial (Fin 1) ℤ))
      (⟨0, rfl⟩ : (fun x : Fin 1 → MvPolynomial (Fin 1) ℤ => x 0) ∈ inputs 1)
  | succ t ih =>
    have hsq : (fun x : Fin 1 → MvPolynomial (Fin 1) ℤ => x 0 ^ 2 ^ (t + 1)) =
        fun x => x 0 ^ 2 ^ t * x 0 ^ 2 ^ t :=
      funext fun x => by rw [pow_succ, pow_mul, sq]
    exact hsq ▸ ih.trans (synthesis_cf_mul (Set.mem_union_right _ rfl) (Set.mem_union_right _ rfl))

/-- Repeated squaring computes the integer constant `2 ^ (2 ^ t)` with a constant-free circuit
of size `≤ t + 2`. -/
theorem exists_constFreeCircuit_two_pow_two_pow (n t : ℕ) :
    ∃ c : Circuit constFreeSignature n 1,
      constFreePoly c 0 = MvPolynomial.C ((2 : ℤ) ^ 2 ^ t) ∧ c.size ≤ t + 2 := by
  suffices Synthesis (constFreeInterp (MvPolynomial (Fin n) ℤ)) (inputs n)
      {fun _ : Fin n → MvPolynomial (Fin n) ℤ => MvPolynomial.C ((2 : ℤ) ^ 2 ^ t)} (t + 2) by
    obtain ⟨c, hc, hsz⟩ := this.exists_circuit
    exact ⟨c, congrFun (hc MvPolynomial.X) 0, hsz⟩
  induction t with
  | zero =>
    have h1 : Synthesis (constFreeInterp (MvPolynomial (Fin n) ℤ)) (inputs n)
        {fun _ => (1 : MvPolynomial (Fin n) ℤ)} 1 := synthesis_cf_one
    have h2 : Synthesis (constFreeInterp (MvPolynomial (Fin n) ℤ))
        (inputs n ∪ {fun _ => (1 : MvPolynomial (Fin n) ℤ)})
        {fun _ => (1 : MvPolynomial (Fin n) ℤ) + 1} 1 :=
      synthesis_cf_add (Set.mem_union_right _ rfl) (Set.mem_union_right _ rfl)
    have hcomb := h1.trans h2
    have hC2 : ((1 : MvPolynomial (Fin n) ℤ) + 1) = MvPolynomial.C ((2 : ℤ) ^ 2 ^ 0) := by
      simp [one_add_one_eq_two]
    simpa only [hC2] using hcomb
  | succ t ih =>
    have hsq : (fun _ : Fin n → MvPolynomial (Fin n) ℤ =>
          (MvPolynomial.C ((2 : ℤ) ^ 2 ^ (t + 1)) : MvPolynomial (Fin n) ℤ)) =
        fun _ => (MvPolynomial.C ((2 : ℤ) ^ 2 ^ t) : MvPolynomial (Fin n) ℤ) *
          MvPolynomial.C ((2 : ℤ) ^ 2 ^ t) :=
      funext fun _ => by rw [← map_mul, pow_succ, pow_mul, sq]
    refine hsq ▸ (ih.trans (synthesis_cf_mul (Set.mem_union_right _ rfl)
      (Set.mem_union_right _ rfl))).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-! ### Arithmetic circuits over `ℚ` using only the constant `1/2` -/

/-- Operations of an arithmetic circuit over `ℚ` using only the constant `1/2`
over `ℚ`. -/
inductive HalfOp : Type
  /-- Binary addition gate `+`. -/
  | add
  /-- Binary subtraction gate `-`. -/
  | sub
  /-- Binary multiplication gate `×`. -/
  | mul
  /-- Nullary constant gate `1/2`. -/
  | half
  deriving DecidableEq

/-- Arity of each `HalfOp` gate. -/
abbrev HalfOp.arity : HalfOp → ℕ
  | .add => 2
  | .sub => 2
  | .mul => 2
  | .half => 0

/-- Signature of arithmetic circuits using only the constant `1/2`. -/
abbrev halfSignature : Signature.{0} where
  Op := HalfOp
  Arity := HalfOp.arity

/-- Interpretation of `halfSignature` in any `ℚ`-algebra `R` (in particular `ℚ` and
`MvPolynomial (Fin n) ℚ`). -/
@[expose] noncomputable def halfInterp (R : Type*) [Ring R] [Algebra ℚ R] :
    Interpretation halfSignature R
  | .add, x => x 0 + x 1
  | .sub, x => x 0 - x 1
  | .mul, x => x 0 * x 1
  | .half, _ => algebraMap ℚ R (1 / 2 : ℚ)

/-- Formal polynomial over `ℚ` computed by a `halfSignature` circuit. -/
noncomputable def halfPoly {n m : ℕ} (c : Circuit halfSignature n m) (j : Fin m) :
    MvPolynomial (Fin n) ℚ :=
  c.eval (halfInterp (MvPolynomial (Fin n) ℚ)) MvPolynomial.X j

/-- Families of integer polynomials computable (when viewed in `ℚ[X]`) by polynomial-size
arithmetic circuits using only the constant `1/2` over `ℚ`. -/
def VPnbHalf : Set (PolynomialFamily ℤ) :=
  {f | PolynomiallyBounded f.vars ∧
    ∃ c : ∀ n, Circuit halfSignature (f.vars n) 1,
      PolynomiallyBounded (fun n => (c n).size) ∧
      ∀ n, halfPoly (c n) 0 = MvPolynomial.map (Int.castRingHom ℚ) (f.poly n)}

/-- Every constant-free circuit compiles into a `halfSignature` circuit (using `1 = 1/2 + 1/2`)
with at most twice as many gates, computing the same polynomial mapped to `ℚ`. -/
theorem exists_halfCircuit_of_constFree {n m : ℕ} (c : Circuit constFreeSignature n m) :
    ∃ d : Circuit halfSignature n m,
      (∀ j, halfPoly d j = MvPolynomial.map (Int.castRingHom ℚ) (constFreePoly c j)) ∧
      d.size ≤ 2 * c.size := by
  let I := halfInterp (MvPolynomial (Fin n) ℚ)
  have hsim : I.SimulatesWithCost (constFreeInterp (MvPolynomial (Fin n) ℚ)) (fun _ => 2) := by
    intro op
    cases op with
    | add =>
      exact ⟨Circuit.oneGate (σ := halfSignature) .add id,
        fun x => funext fun j => by fin_cases j; rfl, by simp⟩
    | sub =>
      exact ⟨Circuit.oneGate (σ := halfSignature) .sub id,
        fun x => funext fun j => by fin_cases j; rfl, by simp⟩
    | mul =>
      exact ⟨Circuit.oneGate (σ := halfSignature) .mul id,
        fun x => funext fun j => by fin_cases j; rfl, by simp⟩
    | one =>
      have hhalf : Synthesis I (inputs 0)
          {fun _ => (algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ))} 1 :=
        Synthesis.gate (σ := halfSignature) .half (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      have hadd : Synthesis I (inputs 0 ∪
          {fun _ => (algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ))})
          {fun _ => algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ) +
            algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ)} 1 :=
        Synthesis.gate (σ := halfSignature) .add
          ![fun _ => algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ),
            fun _ => algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ)]
          (fun i => by fin_cases i <;> exact Set.mem_union_right _ rfl)
      have hone : algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ) +
          algebraMap ℚ (MvPolynomial (Fin n) ℚ) (1 / 2 : ℚ) = 1 := by
        rw [← map_add]
        norm_num
      obtain ⟨c1, hc1, hsz1⟩ := (hhalf.trans hadd).exists_circuit
      refine ⟨c1, fun x => funext fun j => ?_, hsz1⟩
      have h0 := congrFun (hc1 x) j
      simpa only [single_apply, constFreeInterp_one, hone] using h0
  obtain ⟨d, hd, hsz⟩ := c.exists_simulation_le hsim
  refine ⟨d, fun j => ?_, hsz⟩
  let hmap : Homomorphism (constFreeInterp (MvPolynomial (Fin n) ℤ))
      (constFreeInterp (MvPolynomial (Fin n) ℚ)) :=
    ⟨MvPolynomial.map (Int.castRingHom ℚ), fun op args => by
      cases op <;> simp [constFreeInterp, map_add, map_sub, map_mul, map_one]⟩
  have heq := congrFun (c.map_eval hmap MvPolynomial.X) j
  have hX : hmap.map ∘ MvPolynomial.X = MvPolynomial.X :=
    funext fun i => MvPolynomial.map_X _ i
  rw [hX] at heq
  rw [halfPoly, congrFun (congrFun hd MvPolynomial.X) j, ← heq]
  rfl

/-- Computing `(1/2) ^ k` in `halfSignature` takes at most `2 * k + 2` gates. -/
theorem exists_halfCircuit_inv_two_pow (n k : ℕ) :
    ∃ c : Circuit halfSignature n 1,
      halfPoly c 0 = MvPolynomial.C ((1 / 2 : ℚ) ^ k) ∧ c.size ≤ 2 * k + 2 := by
  let I := halfInterp (MvPolynomial (Fin n) ℚ)
  suffices Synthesis I (inputs n)
      {fun _ : Fin n → MvPolynomial (Fin n) ℚ => MvPolynomial.C ((1 / 2 : ℚ) ^ k)}
      (2 * k + 2) by
    obtain ⟨c, hc, hsz⟩ := this.exists_circuit
    exact ⟨c, congrFun (hc MvPolynomial.X) 0, hsz⟩
  induction k with
  | zero =>
    have hhalf : Synthesis I (inputs n)
        {fun _ => MvPolynomial.C (1 / 2 : ℚ)} 1 :=
      Synthesis.gate (σ := halfSignature) .half (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hadd : Synthesis I (inputs n ∪ {fun _ => MvPolynomial.C (1 / 2 : ℚ)})
        {fun _ => MvPolynomial.C (1 / 2 : ℚ) + MvPolynomial.C (1 / 2 : ℚ)} 1 :=
      Synthesis.gate (σ := halfSignature) .add
        ![fun _ => MvPolynomial.C (1 / 2 : ℚ), fun _ => MvPolynomial.C (1 / 2 : ℚ)]
        (fun i => by fin_cases i <;> exact Set.mem_union_right _ rfl)
    have hone : MvPolynomial.C (1 / 2 : ℚ) + MvPolynomial.C (1 / 2 : ℚ) =
        (MvPolynomial.C ((1 / 2 : ℚ) ^ 0) : MvPolynomial (Fin n) ℚ) := by
      rw [← map_add]
      norm_num
    simpa only [hone] using hhalf.trans hadd
  | succ k ih =>
    have hhalf : Synthesis I (inputs n ∪ {fun _ => MvPolynomial.C ((1 / 2 : ℚ) ^ k)})
        {fun _ => MvPolynomial.C (1 / 2 : ℚ)} 1 :=
      Synthesis.gate (σ := halfSignature) .half (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hmul : Synthesis I
        (inputs n ∪ ({fun _ => MvPolynomial.C ((1 / 2 : ℚ) ^ k)} ∪
          {fun _ => MvPolynomial.C (1 / 2 : ℚ)}))
        {fun _ => MvPolynomial.C ((1 / 2 : ℚ) ^ k) * MvPolynomial.C (1 / 2 : ℚ)} 1 :=
      Synthesis.gate (σ := halfSignature) .mul
        ![fun _ => MvPolynomial.C ((1 / 2 : ℚ) ^ k), fun _ => MvPolynomial.C (1 / 2 : ℚ)]
        (fun i => by
          fin_cases i
          · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
          · exact Set.mem_union_right _ (Set.mem_union_right _ rfl))
    have hpow : MvPolynomial.C ((1 / 2 : ℚ) ^ k) * MvPolynomial.C (1 / 2 : ℚ) =
        (MvPolynomial.C ((1 / 2 : ℚ) ^ (k + 1)) : MvPolynomial (Fin n) ℚ) := by
      rw [← map_mul, pow_succ]
    refine (ih.comp hhalf).trans hmul |>.mono Set.Subset.rfl ?_ (by omega)
    simp only [hpow, Set.Subset.rfl]

/-- Multiplying two `halfSignature` circuits of one output yields a `halfSignature` circuit
computing the product of their polynomials. -/
theorem exists_halfCircuit_mul {n : ℕ} (c₁ c₂ : Circuit halfSignature n 1) :
    ∃ c : Circuit halfSignature n 1,
      halfPoly c 0 = halfPoly c₁ 0 * halfPoly c₂ 0 ∧ c.size ≤ c₁.size + c₂.size + 1 := by
  let mulGate : Circuit halfSignature 2 1 :=
    Circuit.oneGate (σ := halfSignature) .mul id
  let pairC : Circuit halfSignature n 2 :=
    Circuit.pi fun i : Fin 2 => if i = 0 then c₁ else c₂
  refine ⟨mulGate.comp pairC, ?_, ?_⟩
  · simp only [halfPoly, Circuit.eval_comp, mulGate, pairC, Circuit.eval_oneGate,
      Circuit.eval_pi, halfInterp, id_eq]
    rfl
  · simp only [Circuit.size_comp, mulGate, pairC, Circuit.size_oneGate, Circuit.size_pi,
      Fin.sum_univ_two, ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
    omega

/-- If `τ(2 ^ p(n) * f_n)` is polynomially bounded for some polynomially bounded `p`, then `f`
can be computed by polynomial-size arithmetic circuits over `ℚ` using only the constant `1/2`
over `ℚ`. -/
theorem mem_VPnbHalf_of_tau_two_pow_mul {f : PolynomialFamily ℤ}
    (hvars : PolynomiallyBounded f.vars) {p : ℕ → ℕ} (hp : PolynomiallyBounded p)
    (htau : PolynomiallyBounded fun n => tau (MvPolynomial.C ((2 : ℤ) ^ p n) * f.poly n)) :
    f ∈ VPnbHalf := by
  choose c₀ hc₀ hsz₀ using fun n =>
    exists_circuit_of_tau (MvPolynomial.C ((2 : ℤ) ^ p n) * f.poly n)
  choose d₁ hd₁ hsz₁ using fun n => exists_halfCircuit_of_constFree (c₀ n)
  choose d₂ hd₂ hsz₂ using fun n => exists_halfCircuit_inv_two_pow (f.vars n) (p n)
  choose d hd hsz using fun n => exists_halfCircuit_mul (d₂ n) (d₁ n)
  refine ⟨hvars, d, ?_, fun n => ?_⟩
  · have hbound : PolynomiallyBounded fun n => (2 * p n + 2) + 2 * tau
        (MvPolynomial.C ((2 : ℤ) ^ p n) * f.poly n) + 1 := by fun_prop
    refine hbound.mono_of_le fun n => ?_
    calc (d n).size ≤ (d₂ n).size + (d₁ n).size + 1 := hsz n
      _ ≤ (2 * p n + 2) + 2 * (c₀ n).size + 1 :=
        Nat.add_le_add_right (Nat.add_le_add (hsz₂ n) (hsz₁ n)) 1
      _ = (2 * p n + 2) + 2 * tau (MvPolynomial.C ((2 : ℤ) ^ p n) * f.poly n) + 1 := by
        rw [hsz₀ n]
  · rw [hd n, hd₂ n, hd₁ n 0, hc₀ n, map_mul, MvPolynomial.map_C]
    simp only [Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat, ← mul_assoc, ← map_mul]
    have hcancel : (1 / 2 : ℚ) ^ p n * (2 : ℚ) ^ p n = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hcancel, map_one, one_mul]

/-- Characterization of `TauPolyBounded`. -/
theorem tauPolyBounded_iff {f : PolynomialFamily ℤ} :
    TauPolyBounded f ↔ PolynomiallyBounded fun n => tau (f.poly n) :=
  Iff.rfl

/-- Membership characterization for `VPnb`. -/
theorem mem_VPnb {K : Type*} [CommSemiring K] {f : PolynomialFamily K} :
    f ∈ VPnb K ↔
      PolynomiallyBounded f.vars ∧
      ∃ c : ∀ n, Circuit (arithSignature K) (f.vars n) 1,
        PolynomiallyBounded (fun n => (c n).size) ∧ ∀ n, (c n).polynomial 0 = f.poly n :=
  Iff.rfl

/-- Membership characterization for `VNPnb`. -/
theorem mem_VNPnb {K : Type*} [CommSemiring K] {f : PolynomialFamily K} :
    f ∈ VNPnb K ↔
      ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) K),
        (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily K) ∈ VPnb K ∧
          ∀ n, f.poly n = booleanSum (m n) (g n) :=
  Iff.rfl

/-- Membership characterization for `VP0`. -/
theorem mem_VP0 {f : PolynomialFamily ℤ} :
    f ∈ VP0 ↔
      PolynomiallyBounded f.vars ∧
      ∃ c : ∀ n, Circuit constFreeSignature (f.vars n) 1,
        PolynomiallyBounded (fun n => (c n).size) ∧
        PolynomiallyBounded (fun n => formalDegree (c n) 0) ∧
        ∀ n, constFreePoly (c n) 0 = f.poly n :=
  Iff.rfl

/-- Membership characterization for `VP0nb`. -/
theorem mem_VP0nb {f : PolynomialFamily ℤ} :
    f ∈ VP0nb ↔
      PolynomiallyBounded f.vars ∧
      ∃ c : ∀ n, Circuit constFreeSignature (f.vars n) 1,
        PolynomiallyBounded (fun n => (c n).size) ∧
        ∀ n, constFreePoly (c n) 0 = f.poly n :=
  Iff.rfl

/-- Membership characterization for `VNP0`. -/
theorem mem_VNP0 {f : PolynomialFamily ℤ} :
    f ∈ VNP0 ↔
      ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) ℤ),
        (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily ℤ) ∈ VP0 ∧
          ∀ n, f.poly n = booleanSum (m n) (g n) :=
  Iff.rfl

/-- Membership characterization for `VNP0nb`. -/
theorem mem_VNP0nb {f : PolynomialFamily ℤ} :
    f ∈ VNP0nb ↔
      ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) ℤ),
        (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily ℤ) ∈ VP0nb ∧
          ∀ n, f.poly n = booleanSum (m n) (g n) :=
  Iff.rfl

/-- Membership characterization for `VPiP0`. -/
theorem mem_VPiP0 {f : PolynomialFamily ℤ} :
    f ∈ VPiP0 ↔
      ∃ (m : ℕ → ℕ) (g : ∀ n, MvPolynomial (Fin (f.vars n + m n)) ℤ),
        (⟨fun n => f.vars n + m n, g⟩ : PolynomialFamily ℤ) ∈ VP0nb ∧
          ∀ n, f.poly n = booleanProd (m n) (g n) :=
  Iff.rfl

/-- Membership characterization for `VPnbHalf`. -/
theorem mem_VPnbHalf {f : PolynomialFamily ℤ} :
    f ∈ VPnbHalf ↔
      PolynomiallyBounded f.vars ∧
      ∃ c : ∀ n, Circuit halfSignature (f.vars n) 1,
        PolynomiallyBounded (fun n => (c n).size) ∧
        ∀ n, halfPoly (c n) 0 = MvPolynomial.map (Int.castRingHom ℚ) (f.poly n) :=
  Iff.rfl

end CslibFrontier.Circuits.Arithmetic
