/-
Copyright (c) 2026 Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cslib contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Depth
public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.Arithmetic.BitBlast
public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.Encoding
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LowerBound
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NWGenerator
public import CslibFrontier.Computability.Circuit.Arithmetic.Permanent
public import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis
public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PH
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicExponentialTime
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
public import CslibFrontier.Computability.Complexity.Classes.Toda
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Design
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import CslibFrontier.Foundations.Data.MvPolynomial.LastVariable
public import CslibFrontier.Foundations.Data.MvPolynomial.LowDegreeRoot
public import CslibFrontier.Foundations.Data.MvPolynomial.PartialEval
public import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel
public import CslibFrontier.Foundations.Data.Polynomial.InterpolationCoeff
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Fin

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.Data.MvPolynomial.Shift
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
import CslibFrontier.Foundations.Data.MvPolynomial.TruncateTotalDegree
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn

/-!
# Polynomial Identity Testing, Algebraic Nisan–Wigderson Designs, and Circuit Lower Bounds

This module develops the mathematical and complexity-theoretic connection between deterministic
Polynomial Identity Testing (PIT), algebraic Nisan–Wigderson designs evaluated on hard Boolean
truth tables, downward self-reducibility of the permanent, and circuit lower bounds.

## Contents

1. **Syntactic degree and bounded-degree arithmetic circuits.** We define syntactic degree for
   general fan-in-two arithmetic circuits over `Cslib.Circuits.arithSignature K` and prove that the
   formal polynomial degree is bounded by the syntactic degree and hence by `2 ^ depth`. We also
   define constant-free arithmetic circuits (with constants in `{-1, 0, 1}`) and provide
   polynomial-size circuit combinators for sparse polynomials, linear combinations, variable
   shifts, powers, univariate coefficient extraction, last-variable derivatives, and low-degree
   homogeneous truncation over characteristic-zero fields.

2. **White-box and black-box PIT, Schwartz–Zippel, range avoidance, and Heintz–Schnorr lower
   bounds.** We formalize white-box PIT (`WhiteBoxPIT`) on encoded rational arithmetic circuits,
   subexponential deterministic and nondeterministic time classes (`DSUBEXP`, `NSUBEXP`), and
   black-box hitting sets (`IsCircuitHittingSet`). We prove the Schwartz–Zippel density and
   grid-witness bounds for arithmetic circuits, probabilistic existence of small hitting sets for
   finite circuit classes, an equivalence between hitting sets and range avoidance over strictly
   ordered rings via explicit sum-of-squares circuits, a constructive binary-halving root decoder,
   and Heintz–Schnorr algebraic lower bounds from subexponential hitting sets.

3. **Algebraic Nisan–Wigderson designs on Boolean truth tables and general-circuit
   hardness-to-randomness.** Bridging combinatorial designs (`NisanWigderson.Design`) with
   multilinear extensions (`BitString.multilinearExtension`), we define the algebraic
   Nisan–Wigderson generator on Boolean truth tables and prove exact agreement with the Boolean
   generator on the hypercube. For general DAG arithmetic circuits, we prove the algebraic hybrid
   reconstruction lemma, low-degree root circuit extraction in characteristic zero via Lagrange
   inversion and interpolation, the general-circuit hardness-to-hitting-set theorem, and a
   bit-blasting bridge from modular arithmetic circuits to Boolean De Morgan circuits.

4. **Downward self-reducibility and PIT certification of the permanent.** We prove the row-zero
   Laplace expansion of the matrix permanent over arbitrary commutative semirings, build explicit
   Laplace-residual arithmetic circuits, and prove that a sequence of candidate arithmetic circuits
   computes the generic permanent polynomials up to dimension `n` if and only if all `n + 1`
   residual circuits vanish identically. Consequently, white-box PIT certifies exact permanent
   evaluation on all matrices (including 0/1 matrices).

5. **Hardness-vs-randomness dichotomies.** Combining the native nondeterministic exponential time
   hierarchy (`expLazyDiagonal`), the inclusion `MA ⊆ PH ⊆ P^#P`, Valiant's `#P`-completeness of
   the 0/1 permanent, and PIT certification of permanent circuits, we establish both an
   unconditional algebraic-vs-Boolean Nisan–Wigderson dichotomy, a native guess-and-certify `NTIME`
   simulation and diagonal lower-bound transfer, and the conditional complexity-class dichotomy
   from subexponential white-box PIT to `NEXP ⊄ P/poly` or permanent algebraic circuit lower
   bounds.

6. **Concrete non-vacuity and sharpness witnesses.** We provide explicit circuits, hitting sets,
   certified small permanent circuits, concrete algebraic design evaluations, and sharpness
   counterexamples over rings with zero divisors, finite fields, and undersized grids.
-/

@[expose] public section

namespace Cslib.Circuits

open Finset MvPolynomial

/-! ## : Syntactic Degree and General Arithmetic Circuit Combinators -/

section SyntacticDegree

universe u

variable {K : Type u} {n g m : ℕ}

/-- The syntactic-degree interpretation of `arithSignature K` in `ℕ`: addition takes the maximum
of its inputs' degrees, multiplication adds them, and constants have degree `0`. -/
def arithDegInterpretation (K : Type u) : Interpretation (arithSignature K) ℕ
  | .add, d => max (d 0) (d 1)
  | .mul, d => d 0 + d 1
  | .const _, _ => 0

@[simp] theorem arithDegInterpretation_add (d : Fin 2 → ℕ) :
    arithDegInterpretation K .add d = max (d 0) (d 1) := rfl

@[simp] theorem arithDegInterpretation_mul (d : Fin 2 → ℕ) :
    arithDegInterpretation K .mul d = d 0 + d 1 := rfl

@[simp] theorem arithDegInterpretation_const (c : K) (d : Fin 0 → ℕ) :
    arithDegInterpretation K (.const c) d = 0 := rfl

/-- The syntactic degree of every input or internal-gate wire in an arithmetic program, with each
input wire assigned syntactic degree `1`. -/
def Program.wireSyntacticDegree (p : Program (arithSignature K) n g) : Wire n g → ℕ :=
  p.trace (arithDegInterpretation K) (fun _ => 1)

/-- The syntactic degree of designated output `j` of an arithmetic circuit. -/
def Circuit.outputSyntacticDegree (c : Circuit (arithSignature K) n m) (j : Fin m) : ℕ :=
  c.eval (arithDegInterpretation K) (fun _ => 1) j

/-- The syntactic degree of an arithmetic circuit: the maximum syntactic degree of its outputs. -/
def Circuit.syntacticDegree (c : Circuit (arithSignature K) n m) : ℕ :=
  Fin.foldl m (fun acc j => max acc (c.outputSyntacticDegree j)) 0

private theorem foldl_max_le_iff_nat {k : ℕ} (f : Fin k → ℕ) (init bound : ℕ) :
    Fin.foldl k (fun acc j => max acc (f j)) init ≤ bound ↔
      init ≤ bound ∧ ∀ j, f j ≤ bound := by
  induction k generalizing init with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ, ih]
    simp [Fin.forall_fin_succ, and_assoc]

/-- The syntactic degree of a circuit is at most `d` iff every output has syntactic degree at most
`d`. -/
theorem Circuit.syntacticDegree_le_iff (c : Circuit (arithSignature K) n m) {d : ℕ} :
    c.syntacticDegree ≤ d ↔ ∀ j, c.outputSyntacticDegree j ≤ d := by
  simpa only [Circuit.syntacticDegree, Nat.zero_le, true_and] using
    foldl_max_le_iff_nat c.outputSyntacticDegree 0 d

/-- Every output's syntactic degree is at most the circuit's syntactic degree. -/
theorem Circuit.outputSyntacticDegree_le_syntacticDegree (c : Circuit (arithSignature K) n m)
    (j : Fin m) : c.outputSyntacticDegree j ≤ c.syntacticDegree :=
  c.syntacticDegree_le_iff.mp le_rfl j

/-- For a single-output arithmetic circuit, `syntacticDegree` equals `outputSyntacticDegree 0`. -/
@[simp] theorem Circuit.syntacticDegree_single (c : Circuit (arithSignature K) n 1) :
    c.syntacticDegree = c.outputSyntacticDegree 0 := by
  simp [Circuit.syntacticDegree, Fin.foldl_succ]

/-- Every wire of an arithmetic program computes a formal polynomial whose total degree is at most
its syntactic degree. -/
theorem Program.totalDegree_trace_le_wireSyntacticDegree [CommSemiring K]
    (p : Program (arithSignature K) n g) (w : Wire n g) :
    (p.trace (arithInterpretationWith K C) X w).totalDegree ≤ p.wireSyntacticDegree w := by
  induction p with
  | empty =>
    cases w with
    | input i => exact totalDegree_X_le i
    | gate j => exact j.elim0
  | @gate k p line ih =>
    induction w using Wire.lastCases with
    | castSucc w =>
      rw [Program.trace_gate_castSucc, Program.wireSyntacticDegree, Program.trace_gate_castSucc]
      exact ih w
    | last =>
      change ((p.gate line).eval (arithInterpretationWith K C) X (Fin.last k)).totalDegree ≤
        (p.gate line).eval (arithDegInterpretation K) (fun _ => 1) (Fin.last k)
      rw [Program.eval_gate_last, Program.eval_gate_last, Line.eval, Line.eval]
      rcases line with ⟨op, wires⟩
      cases op with
      | add =>
        simp only [arithInterpretationWith_add, arithDegInterpretation_add, Function.comp_apply]
        exact (totalDegree_add _ _).trans (max_le_max (ih (wires 0)) (ih (wires 1)))
      | mul =>
        simp only [arithInterpretationWith_mul, arithDegInterpretation_mul, Function.comp_apply]
        exact (totalDegree_mul _ _).trans (Nat.add_le_add (ih (wires 0)) (ih (wires 1)))
      | const a =>
        simp only [arithInterpretationWith_const, arithDegInterpretation_const, totalDegree_C,
          le_refl]

/-- The formal polynomial at output `j` has total degree at most `c.outputSyntacticDegree j`. -/
theorem Circuit.totalDegree_polynomial_le_outputSyntacticDegree [CommSemiring K]
    (c : Circuit (arithSignature K) n m) (j : Fin m) :
    (c.polynomial j).totalDegree ≤ c.outputSyntacticDegree j :=
  c.program.totalDegree_trace_le_wireSyntacticDegree (c.outputs j)

/-- The formal polynomial at every output of an arithmetic circuit has total degree at most its
syntactic degree. -/
theorem Circuit.totalDegree_polynomial_le_syntacticDegree [CommSemiring K]
    (c : Circuit (arithSignature K) n m) (j : Fin m) :
    (c.polynomial j).totalDegree ≤ c.syntacticDegree :=
  (c.totalDegree_polynomial_le_outputSyntacticDegree j).trans
    (c.outputSyntacticDegree_le_syntacticDegree j)

/-- Every wire of an arithmetic program has syntactic degree at most `2 ^ (wireDepth)`. -/
theorem Program.wireSyntacticDegree_le_two_pow_wireDepths (p : Program (arithSignature K) n g)
    (w : Wire n g) :
    p.wireSyntacticDegree w ≤ 2 ^ p.wireDepths w := by
  induction p with
  | empty =>
    cases w with
    | input i => simp [Program.wireSyntacticDegree]
    | gate j => exact j.elim0
  | @gate k p line ih =>
    induction w using Wire.lastCases with
    | castSucc w =>
      rw [Program.wireSyntacticDegree, Program.trace_gate_castSucc,
        Program.wireDepths_gate_castSucc]
      exact ih w
    | last =>
      change (p.gate line).eval (arithDegInterpretation K) (fun _ => 1) (Fin.last k) ≤
        2 ^ (p.gate line).depths (Fin.last k)
      rw [Program.eval_gate_last, Program.depths_gate_last, Line.eval]
      rcases line with ⟨op, wires⟩
      have harg (a : Fin ((arithSignature K).Arity op)) :
          p.wireDepths (wires a) + 1 ≤
            Line.depth (σ := arithSignature K) ⟨op, wires⟩ p.wireDepths := by
        have hle := (Line.depth_le_add_one_iff (σ := arithSignature K) ⟨op, wires⟩ p.wireDepths
          (d := Line.depth (σ := arithSignature K) ⟨op, wires⟩ p.wireDepths - 1)).mp
          (by have := Line.depth_pos (σ := arithSignature K) ⟨op, wires⟩ p.wireDepths; omega) a
        have hpos := Line.depth_pos (σ := arithSignature K) ⟨op, wires⟩ p.wireDepths
        dsimp only at hle
        omega
      cases op with
      | const a =>
        simp only [arithDegInterpretation_const, Nat.zero_le]
      | add =>
        simp only [arithDegInterpretation_add, Function.comp_apply]
        have h0 := (ih (wires 0)).trans
          (Nat.pow_le_pow_right two_pos (Nat.le_of_succ_le (harg 0)))
        have h1 := (ih (wires 1)).trans
          (Nat.pow_le_pow_right two_pos (Nat.le_of_succ_le (harg 1)))
        exact max_le h0 h1
      | mul =>
        simp only [arithDegInterpretation_mul, Function.comp_apply]
        set D := Line.depth (σ := arithSignature K) ⟨ArithOp.mul, wires⟩ p.wireDepths
        have hpos : 0 < D :=
          Line.depth_pos (σ := arithSignature K) ⟨ArithOp.mul, wires⟩ p.wireDepths
        have h0 : p.wireDepths (wires 0) ≤ D - 1 := by have := harg 0; omega
        have h1 : p.wireDepths (wires 1) ≤ D - 1 := by have := harg 1; omega
        calc p.wireSyntacticDegree (wires 0) + p.wireSyntacticDegree (wires 1)
            ≤ 2 ^ (D - 1) + 2 ^ (D - 1) :=
              Nat.add_le_add ((ih _).trans (Nat.pow_le_pow_right two_pos h0))
                ((ih _).trans (Nat.pow_le_pow_right two_pos h1))
          _ = 2 ^ D := by
              rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hpos]

/-- The syntactic degree of an arithmetic circuit is at most `2 ^ c.depth`. -/
theorem Circuit.syntacticDegree_le_two_pow_depth (c : Circuit (arithSignature K) n m) :
    c.syntacticDegree ≤ 2 ^ c.depth :=
  c.syntacticDegree_le_iff.mpr fun j =>
    (c.program.wireSyntacticDegree_le_two_pow_wireDepths (c.outputs j)).trans
      (Nat.pow_le_pow_right two_pos (c.outputDepths_le_depth j))

/-- The formal polynomial degree of an arithmetic circuit is at most `2 ^ c.depth` and
`2 ^ c.size`. -/
theorem Circuit.totalDegree_polynomial_le_two_pow_depth [CommSemiring K]
    (c : Circuit (arithSignature K) n m) (j : Fin m) :
    (c.polynomial j).totalDegree ≤ 2 ^ c.depth :=
  (c.totalDegree_polynomial_le_syntacticDegree j).trans c.syntacticDegree_le_two_pow_depth

/-- The formal polynomial degree of an arithmetic circuit is at most `2 ^ c.size`. -/
theorem Circuit.totalDegree_polynomial_le_two_pow_size [CommSemiring K]
    (c : Circuit (arithSignature K) n m) (j : Fin m) :
    (c.polynomial j).totalDegree ≤ 2 ^ c.size :=
  (c.totalDegree_polynomial_le_two_pow_depth j).trans
    (Nat.pow_le_pow_right two_pos c.depth_le_size)

/-- Relabeling the inputs of an arithmetic circuit renames the variables of its formal
polynomial. -/
theorem Circuit.polynomial_mapInputs [CommSemiring K] {n' : ℕ}
    (c : Circuit (arithSignature K) n m) (f : Fin n → Fin n') (j : Fin m) :
    (c.mapInputs f).polynomial j = rename f (c.polynomial j) := by
  rw [rename_eq_aeval, Circuit.aeval_polynomial_mvPolynomial, Circuit.polynomial]
  exact congrFun (c.eval_mapInputs f (arithInterpretationWith K C) X) j

/-- Relabeling the inputs of an arithmetic circuit preserves its syntactic degree. -/
theorem Circuit.syntacticDegree_mapInputs {n' : ℕ}
    (c : Circuit (arithSignature K) n m) (f : Fin n → Fin n') :
    (c.mapInputs f).syntacticDegree = c.syntacticDegree := by
  have hout : (c.mapInputs f).outputSyntacticDegree = c.outputSyntacticDegree := by
    funext j
    simp only [Circuit.outputSyntacticDegree, Circuit.eval_mapInputs]
    rfl
  simp [Circuit.syntacticDegree, hout]

/-- An arithmetic operation is *constant-free* (unit-constant) if every constant symbol lies in
`{-1, 0, 1}`. -/
def ArithOp.IsUnitConst [Zero K] [One K] [Neg K] : ArithOp K → Prop
  | .add => True
  | .mul => True
  | .const c => c = 0 ∨ c = 1 ∨ c = -1

/-- An arithmetic circuit is *constant-free* if every constant gate uses only `-1`, `0`, or `1`. -/
def Circuit.IsConstantFree [Zero K] [One K] [Neg K] (c : Circuit (arithSignature K) n m) : Prop :=
  ∀ j : Fin c.size, (c.program.lines j).op.IsUnitConst

end SyntacticDegree

namespace Arithmetic

section BoundedClasses

universe u

variable {K : Type u} {n : ℕ}

/-- The class of polynomials in `n` variables computed by arithmetic circuits of size at most `s`
and total degree at most `d`. -/
def boundedCircuitPolys (K : Type u) [CommSemiring K] (n s d : ℕ) :
    Set (MvPolynomial (Fin n) K) :=
  {p | ∃ c : Circuit (arithSignature K) n 1,
    c.polynomial 0 = p ∧ c.size ≤ s ∧ p.totalDegree ≤ d}

/-- The class of polynomials in `n` variables computed by arithmetic circuits of size at most `s`
and syntactic degree at most `d`. -/
def boundedSyntacticCircuitPolys (K : Type u) [CommSemiring K] (n s d : ℕ) :
    Set (MvPolynomial (Fin n) K) :=
  {p | ∃ c : Circuit (arithSignature K) n 1,
    c.polynomial 0 = p ∧ c.size ≤ s ∧ c.syntacticDegree ≤ d}

/-- Every polynomial with a bounded-syntactic-degree circuit also has bounded total degree. -/
theorem boundedSyntacticCircuitPolys_subset [CommSemiring K] (n s d : ℕ) :
    boundedSyntacticCircuitPolys K n s d ⊆ boundedCircuitPolys K n s d := by
  rintro p ⟨c, rfl, hs, hd⟩
  exact ⟨c, rfl, hs, (c.totalDegree_polynomial_le_syntacticDegree 0).trans hd⟩

/-- Constant-free `VP`: p-families computed by polynomial-size constant-free arithmetic circuits. -/
def ConstantFreeVP (K : Type u) [CommRing K] : Set (PolynomialFamily K) :=
  {f | f.IsPFamily ∧ ∃ c : ∀ n, Circuit (arithSignature K) (f.vars n) 1,
    PolynomiallyBounded (fun n => (c n).size) ∧
    (∀ n, (c n).IsConstantFree) ∧
    ∀ n, (c n).polynomial 0 = f.poly n}

/-- Every family in `ConstantFreeVP K` lies in `VP K`. -/
theorem ConstantFreeVP_subset_VP [CommRing K] : ConstantFreeVP K ⊆ VP K := by
  rintro f ⟨hpf, c, hsize, -, hpoly⟩
  exact ⟨hpf, c, hsize, hpoly⟩

end BoundedClasses

/-! ### General Arithmetic Circuit Combinators and Characteristic-Zero Interpolation -/

section CircuitCombinators

variable {K : Type*}

/-- Synthesis of a finite product of polynomials from a seed `1`. -/
private theorem synthesis_arith_prod [CommSemiring K] {N : ℕ}
    {s : Set ((Fin N → MvPolynomial (Fin N) K) → MvPolynomial (Fin N) K)}
    {ι : Type*} (indices : Finset ι)
    (factor : ι → (Fin N → MvPolynomial (Fin N) K) → MvPolynomial (Fin N) K)
    (cost : ι → ℕ) (hone : (fun _ => 1) ∈ s)
    (h : ∀ i ∈ indices, Synthesis (arithInterpretationWith K C) s {factor i} (cost i)) :
    Synthesis (arithInterpretationWith K C) s {fun x => ∏ i ∈ indices, factor i x}
      (∑ i ∈ indices, (cost i + 1)) := by
  have := Synthesis.finset_fold (· * ·) 1
    (fun f g => Synthesis.arith_mul (Set.mem_insert f {g}) (Set.mem_insert_of_mem f rfl))
    indices (Synthesis.of_mem hone) h
  simpa only [Finset.prod_eq_fold, Nat.add_zero] using this

/-- **Sparse polynomial circuit synthesis.** Any polynomial `p` in `N` variables has an arithmetic
circuit computing `p` with at most `#p.support * (p.totalDegree + 3) + 2` gates. -/
theorem exists_circuit_ofSparse [CommSemiring K] {N : ℕ} (p : MvPolynomial (Fin N) K) :
    ∃ c : Circuit (arithSignature K) N 1,
      c.polynomial 0 = p ∧ c.size ≤ #p.support * (p.totalDegree + 3) + 2 := by
  let s0 : Set ((Fin N → MvPolynomial (Fin N) K) → MvPolynomial (Fin N) K) :=
    inputs N ∪ ({fun _ => (0 : MvPolynomial (Fin N) K)} ∪ {fun _ => 1})
  have h01 : Synthesis (arithInterpretationWith K C) (inputs N)
      ({fun _ => (0 : MvPolynomial (Fin N) K)} ∪ {fun _ => 1}) 2 := by
    have h0 : Synthesis (arithInterpretationWith K C) (inputs N)
        {fun _ : Fin N → MvPolynomial (Fin N) K => 0} 1 := by
      simpa only [map_zero] using Synthesis.arith_const (constant := C) (0 : K)
    have h1 : Synthesis (arithInterpretationWith K C) (inputs N)
        {fun _ : Fin N → MvPolynomial (Fin N) K => 1} 1 := by
      simpa only [map_one] using Synthesis.arith_const (constant := C) (1 : K)
    exact h0.union h1
  let monoFn (d : Fin N →₀ ℕ) (x : Fin N → MvPolynomial (Fin N) K) : MvPolynomial (Fin N) K :=
    C (p.coeff d) * ∏ t ∈ d.support.sigma (fun i => range (d i)), x t.1
  have hmono (d : Fin N →₀ ℕ) (hd : d ∈ p.support) :
      Synthesis (arithInterpretationWith K C) s0 {monoFn d} (d.degree + 2) := by
    have hprod := synthesis_arith_prod (d.support.sigma fun i => range (d i))
      (fun t x => x t.1) (fun _ => 0) (by simp [s0])
      (fun t _ => Synthesis.of_mem (I := arithInterpretationWith K C) (s := s0) (Or.inl ⟨t.1, rfl⟩))
    have hcard : ∑ _t ∈ d.support.sigma (fun i => range (d i)), (0 + 1) = d.degree := by
      simp [Finsupp.degree_apply]
    rw [hcard] at hprod
    have hc : Synthesis (arithInterpretationWith K C) s0 {fun _ => C (p.coeff d)} 1 :=
      Synthesis.arith_const (constant := C) (p.coeff d)
    refine (hc.combine hprod
      (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)
  have hsum := Synthesis.arith_sum (constant := C) p.support monoFn
    (fun d => p.totalDegree + 2) (by simp [s0]) fun d hd =>
      (hmono d hd).mono Set.Subset.rfl Set.Subset.rfl (Nat.add_le_add_right (le_totalDegree hd) 2)
  have hfull : Synthesis (arithInterpretationWith K C) (inputs N)
      {fun x => ∑ d ∈ p.support, monoFn d x} (#p.support * (p.totalDegree + 3) + 2) :=
    (h01.trans hsum).mono Set.Subset.rfl Set.Subset.rfl (by
      rw [sum_const, smul_eq_mul, add_assoc]
      omega)
  obtain ⟨c, hc, hsize⟩ := hfull.exists_circuit_polynomial
  refine ⟨c, hc.trans ?_, hsize⟩
  refine (sum_congr rfl fun d _ => ?_).trans p.support_sum_monomial_coeff
  simp only [monoFn, prod_sigma, prod_const, card_range, prod_X_pow_eq_monomial, C_mul_monomial,
    mul_one]

/-- **Linear combination of circuits.** Given circuits `fs j` on `M` inputs and scalar weights
`w j`, there is a single circuit computing `∑ j ∈ s, C (w j) * (fs j).polynomial 0` with at most
`(∑ j ∈ s, (fs j).size) + 3 * #s + 1` gates. -/
theorem exists_linearComb_circuit [CommSemiring K] {M : ℕ} {ι : Type*} (s : Finset ι)
    (w : ι → K) (fs : ι → Circuit (arithSignature K) M 1) :
    ∃ c : Circuit (arithSignature K) M 1,
      c.polynomial 0 = ∑ j ∈ s, C (w j) * (fs j).polynomial 0 ∧
      c.size ≤ (∑ j ∈ s, (fs j).size) + 3 * #s + 1 := by
  classical
  let e : Fin #s ≃ s := (s.equivFin).symm
  let combFn (x : Fin #s → MvPolynomial (Fin #s) K) : MvPolynomial (Fin #s) K :=
    ∑ k : Fin #s, C (w (e k)) * x k
  let s1 : Set ((Fin #s → MvPolynomial (Fin #s) K) → MvPolynomial (Fin #s) K) :=
    inputs #s ∪ {fun _ => (0 : MvPolynomial (Fin #s) K)}
  have h0 : Synthesis (arithInterpretationWith K C) (inputs #s)
      {fun _ : Fin #s → MvPolynomial (Fin #s) K => 0} 1 := by
    simpa only [map_zero] using Synthesis.arith_const (constant := C) (0 : K)
  have hcomb : Synthesis (arithInterpretationWith K C) s1 {combFn} (3 * #s) := by
    have hsum := Synthesis.arith_sum (constant := C) (s := s1) (univ : Finset (Fin #s))
      (fun k x => C (w (e k)) * x k) (fun _ => 2) (Set.mem_union_right _ rfl) fun k _ =>
        (Synthesis.arith_const (constant := C) (w (e k))).combine
          (Synthesis.of_mem (I := arithInterpretationWith K C) (s := s1) (Or.inl ⟨k, rfl⟩))
          (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    refine hsum.mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  obtain ⟨linC, hlinC, hlinSize⟩ := (h0.trans hcomb).exists_circuit_polynomial
  let inputsC : Circuit (arithSignature K) M #s := Circuit.pi fun k => fs (e k)
  refine ⟨linC.comp inputsC, ?_, ?_⟩
  · rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial, hlinC]
    simp only [combFn, map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X, inputsC, Circuit.eval_pi]
    change ∑ k : Fin #s, C (w (e k)) * (fs (e k)).polynomial 0 = _
    rw [Fintype.sum_equiv e _ (fun a : s => C (w a) * (fs a).polynomial 0) (fun _ => rfl)]
    exact Finset.sum_coe_sort s (fun j => C (w j) * (fs j).polynomial 0)
  · rw [Circuit.size_comp, Circuit.size_pi]
    have hsum_eq : ∑ k : Fin #s, (fs (e k)).size = ∑ j ∈ s, (fs j).size := by
      rw [Fintype.sum_equiv e _ (fun a : s => (fs a).size) (fun _ => rfl)]
      exact Finset.sum_coe_sort s (fun j => (fs j).size)
    omega

/-- **Variable shift for arithmetic circuits.** Substituting `X k + C (a k)` for each input `k`
adds at most `2 * N` gates and does not increase total degree. -/
theorem exists_shift_circuit [CommSemiring K] {N : ℕ} (a : Fin N → K)
    (c : Circuit (arithSignature K) N 1) :
    ∃ c' : Circuit (arithSignature K) N 1,
      c'.polynomial 0 = shift a (c.polynomial 0) ∧
      c'.size ≤ c.size + 2 * N ∧
      (c'.polynomial 0).totalDegree ≤ (c.polynomial 0).totalDegree := by
  have h1 (k : Fin N) : ∃ g : Circuit (arithSignature K) N 1,
      g.polynomial 0 = X k + C (a k) ∧ g.size ≤ 2 := by
    have hs : Synthesis (arithInterpretationWith K C) (inputs N)
        {fun x : Fin N → MvPolynomial (Fin N) K => x k + C (a k)} 2 :=
      (Synthesis.of_mem (I := arithInterpretationWith K C) (s := inputs N) ⟨k, rfl⟩).combine
        (Synthesis.arith_const (constant := C) (a k))
        (Synthesis.arith_add (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    exact hs.exists_circuit_polynomial
  choose g hg hgs using h1
  refine ⟨c.comp (Circuit.pi g), ?_, ?_, ?_⟩
  · rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
    have hpi : (Circuit.pi g).eval (arithInterpretationWith K C) X = fun k => X k + C (a k) := by
      funext k
      rw [Circuit.eval_pi]
      exact hg k
    rw [hpi]
    rfl
  · rw [Circuit.size_comp, Circuit.size_pi]
    have hle : ∑ k : Fin N, (g k).size ≤ 2 * N := by
      calc ∑ k : Fin N, (g k).size ≤ ∑ _k : Fin N, 2 := sum_le_sum fun k _ => hgs k
        _ = 2 * N := by simp [mul_comm]
    omega
  · rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
    have hpi : (Circuit.pi g).eval (arithInterpretationWith K C) X = fun k => X k + C (a k) := by
      funext k
      rw [Circuit.eval_pi]
      exact hg k
    rw [hpi]
    exact totalDegree_aeval_le (fun k => (totalDegree_add _ _).trans
      (max_le (totalDegree_X_le k) (by simp))) _

/-- **Power circuit.** Computing `(c.polynomial 0) ^ (k + 1)` adds at most `k` multiplication gates
by reusing `c` in a DAG. -/
theorem exists_pow_circuit [CommSemiring K] {N : ℕ} (c : Circuit (arithSignature K) N 1) (k : ℕ) :
    ∃ p : Circuit (arithSignature K) N 1,
      p.polynomial 0 = (c.polynomial 0) ^ (k + 1) ∧ p.size ≤ c.size + k := by
  have hpow : ∃ q : Circuit (arithSignature K) 1 1,
      q.polynomial 0 = (X 0 : MvPolynomial (Fin 1) K) ^ (k + 1) ∧ q.size ≤ k := by
    suffices ∀ t : ℕ, Synthesis (arithInterpretationWith K C) (inputs 1)
        {fun x : Fin 1 → MvPolynomial (Fin 1) K => x 0 ^ (t + 1)} t from
      (this k).exists_circuit_polynomial
    intro t
    induction t with
    | zero =>
      simpa only [zero_add, pow_one] using Synthesis.of_mem (I := arithInterpretationWith K C)
        (⟨0, rfl⟩ : (fun x : Fin 1 → MvPolynomial (Fin 1) K => x 0) ∈ inputs 1)
    | succ t ih =>
      have heq : (fun x : Fin 1 → MvPolynomial (Fin 1) K => x 0 ^ (t + 1 + 1)) =
          fun x => x 0 ^ (t + 1) * x 0 := funext fun x => pow_succ (x 0) (t + 1)
      exact heq ▸ ih.trans
        (Synthesis.arith_mul (Set.mem_union_right _ rfl) (Set.mem_union_left _ ⟨0, rfl⟩))
  obtain ⟨q, hq, hqs⟩ := hpow
  refine ⟨q.comp c, ?_, ?_⟩
  · rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial, hq,
      map_pow, aeval_X]
    rfl
  · rw [Circuit.size_comp]; omega

/-- **Coefficient extraction in the last variable for arithmetic circuits.** Over a field of
characteristic zero, if `c` has total degree at most `r`, then the coefficient of `y ^ i` in
`c.polynomial 0` (viewed in `y = X (Fin.last N)`) has an arithmetic circuit of size at most
`(r + 1) * (c.size + N + 4) + 1` and total degree at most `r`. -/
theorem exists_coeffLast_circuit [Field K] [CharZero K] {N : ℕ} (i r : ℕ)
    (c : Circuit (arithSignature K) (N + 1) 1)
    (hdeg : (c.polynomial 0).totalDegree ≤ r) :
    ∃ c' : Circuit (arithSignature K) N 1,
      c'.polynomial 0 = (lastVariableEquiv K N (c.polynomial 0)).coeff i ∧
      c'.size ≤ (r + 1) * (c.size + N + 4) + 1 ∧
      (c'.polynomial 0).totalDegree ≤ r := by
  let ρ (j : ℕ) : Fin (N + 1) → Fin N ⊕ K := Fin.lastCases (.inr (j : K)) .inl
  let fs (j : ℕ) : Circuit (arithSignature K) N 1 := c.comp (projectionCircuit (ρ j))
  let w (j : ℕ) : K := (Lagrange.basis (range (r + 1)) (fun t : ℕ => (t : K)) j).coeff i
  obtain ⟨res, hres, hresSize⟩ := exists_linearComb_circuit (range (r + 1)) w fs
  have hfs_poly (j : ℕ) :
      (fs j).polynomial 0 = (lastVariableEquiv K N (c.polynomial 0)).eval (C (j : K)) := by
    rw [polynomial_comp_projectionCircuit, eval_lastVariableEquiv]
    unfold projection
    congr 1 with k
    refine Fin.lastCases ?_ (fun t => ?_) k <;> simp [ρ]
  have hres_eq : res.polynomial 0 = (lastVariableEquiv K N (c.polynomial 0)).coeff i := by
    rw [hres, Lagrange.coeff_eq_sum_coeff_basis_smul_eval (v := fun t : ℕ => (t : K))
      (s := range (r + 1)) Nat.cast_injective.injOn _ i]
    · refine sum_congr rfl fun j _ => ?_
      rw [hfs_poly j, smul_eq_C_mul, algebraMap_eq]
    · rw [card_range, natDegree_lastVariableEquiv]
      exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree _ _).trans hdeg)
  refine ⟨res, hres_eq, ?_, ?_⟩
  · have hsum_le : ∑ j ∈ range (r + 1), (fs j).size ≤ (r + 1) * (c.size + N + 1) := by
      calc ∑ j ∈ range (r + 1), (fs j).size
          ≤ ∑ _j ∈ range (r + 1), (c.size + N + 1) := sum_le_sum fun j _ => by
            rw [Circuit.size_comp]
            have := size_projectionCircuit_le (ρ j)
            omega
        _ = (r + 1) * (c.size + N + 1) := by rw [sum_const, card_range, smul_eq_mul]
    rw [card_range] at hresSize
    linarith
  · rw [hres]
    refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, polynomial_comp_projectionCircuit]
    exact (totalDegree_projection_le (ρ j) (c.polynomial 0)).trans hdeg

/-- **Iterated derivative in the last variable for arithmetic circuits.** Over a field of
characteristic zero, if `c` has total degree at most `r`, then the `j`-th derivative in the last
variable has an arithmetic circuit of size at most `(r + 1) * (c.size + N + 6) + 3` and total
degree at most `r`. -/
theorem exists_derivLast_circuit [Field K] [CharZero K] {N : ℕ} (j r : ℕ)
    (c : Circuit (arithSignature K) (N + 1) 1)
    (hdeg : (c.polynomial 0).totalDegree ≤ r) :
    ∃ d : Circuit (arithSignature K) (N + 1) 1,
      lastVariableEquiv K N (d.polynomial 0) =
        Polynomial.derivative^[j] (lastVariableEquiv K N (c.polynomial 0)) ∧
      d.size ≤ (r + 1) * (c.size + N + 6) + 3 ∧
      (d.polynomial 0).totalDegree ≤ r := by
  let addWire : Circuit (arithSignature K) (N + 2) 1 :=
    Circuit.oneGate .add ![(Fin.last N).castSucc, Fin.last (N + 1)]
  let subInputs : Fin (N + 1) → Circuit (arithSignature K) (N + 2) 1 :=
    Fin.lastCases addWire fun k => Circuit.wiring _ fun _ => k.castSucc.castSucc
  let cShift : Circuit (arithSignature K) (N + 2) 1 := c.comp (Circuit.pi subInputs)
  have hsub_poly (k : Fin (N + 1)) : (subInputs k).polynomial 0 =
      Fin.lastCases (X (Fin.last N).castSucc + X (Fin.last (N + 1)))
        (fun t => X t.castSucc.castSucc) k := by
    refine Fin.lastCases ?_ (fun t => ?_) k
    · simp [subInputs, addWire, Circuit.polynomial]
    · simp [subInputs, Circuit.polynomial]
  have hcShift_poly : cShift.polynomial 0 =
      aeval (fun k => (subInputs k).polynomial 0) (c.polynomial 0) := by
    rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
    congr 1 with k
    rw [Circuit.eval_pi]
    rfl
  have hcShift_deg : (cShift.polynomial 0).totalDegree ≤ r := by
    rw [hcShift_poly]
    refine (totalDegree_aeval_le (fun k => ?_) (c.polynomial 0)).trans hdeg
    rw [hsub_poly k]
    refine Fin.lastCases ?_ (fun t => ?_) k
    · simpa only [Fin.lastCases_last] using (totalDegree_add _ _).trans
        (max_le (totalDegree_X_le _) (totalDegree_X_le _))
    · simpa only [Fin.lastCases_castSucc] using totalDegree_X_le _
  have hcShift_size : cShift.size ≤ c.size + 1 := by
    rw [Circuit.size_comp, Circuit.size_pi, Fin.sum_univ_castSucc]
    simp [subInputs, addWire]
    omega
  obtain ⟨coeffC, hcoeffC, hcoeffSize, hcoeffDeg⟩ :=
    exists_coeffLast_circuit j r cShift hcShift_deg
  -- Scale `coeffC` by `j.factorial`.
  have hscale : ∃ sc : Circuit (arithSignature K) 1 1,
      sc.polynomial 0 = C (j.factorial : K) * X 0 ∧ sc.size ≤ 2 := by
    have hs : Synthesis (arithInterpretationWith K C) (inputs 1)
        {fun x : Fin 1 → MvPolynomial (Fin 1) K => C (j.factorial : K) * x 0} 2 :=
      (Synthesis.arith_const (constant := C) (j.factorial : K)).combine
        (Synthesis.of_mem (I := arithInterpretationWith K C) (s := inputs 1) ⟨0, rfl⟩)
        (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    exact hs.exists_circuit_polynomial
  obtain ⟨sc, hsc, hscSize⟩ := hscale
  refine ⟨sc.comp coeffC, ?_, ?_, ?_⟩
  · have hTaylor : (Polynomial.mapRingHom (lastVariableEquiv K N).toRingHom).comp
        ((lastVariableEquiv K (N + 1)).toRingHom.comp
          (aeval (fun k => (subInputs k).polynomial 0) :
            MvPolynomial (Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin (N + 2)) K).toRingHom) =
        (Polynomial.taylorAlgHom
          (Polynomial.X : Polynomial (MvPolynomial (Fin N) K))).toRingHom.comp
          ((Polynomial.mapRingHom Polynomial.C).comp (lastVariableEquiv K N).toRingHom) :=
      ringHom_ext (fun a => by simp) fun i => by
        rw [RingHom.coe_comp, RingHom.coe_comp, RingHom.coe_comp, RingHom.coe_comp,
          Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hsub_poly]
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simp [lastVariableEquiv_X_last, lastVariableEquiv_X_castSucc, add_comm]
        · simp [lastVariableEquiv_X_castSucc]
    have hj := congrArg (fun q => q.coeff j) (RingHom.congr_fun hTaylor (c.polynomial 0))
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.taylorAlgHom_apply,
      Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, Polynomial.eval_map,
      Polynomial.eval₂_C_X] at hj
    change lastVariableEquiv K N
        ((lastVariableEquiv K (N + 1)
          (aeval (fun k => (subInputs k).polynomial 0) (c.polynomial 0))).coeff j) =
      Polynomial.hasseDeriv j (lastVariableEquiv K N (c.polynomial 0)) at hj
    have hpoly : (sc.comp coeffC).polynomial 0 = C (j.factorial : K) * coeffC.polynomial 0 := by
      rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial, hsc,
        map_mul, aeval_C, algebraMap_eq, aeval_X]
      rfl
    rw [hpoly, map_mul, lastVariableEquiv_C, hcoeffC, hcShift_poly, hj,
      ← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul,
      map_natCast, map_natCast]
  · rw [Circuit.size_comp]
    have : (r + 1) * (cShift.size + (N + 1) + 4) ≤ (r + 1) * (c.size + N + 6) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have hpoly : (sc.comp coeffC).polynomial 0 = C (j.factorial : K) * coeffC.polynomial 0 := by
      rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial, hsc,
        map_mul, aeval_C, algebraMap_eq, aeval_X]
      rfl
    rw [hpoly]
    exact ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])).trans hcoeffDeg

/-- Scaling the variables by `c` multiplies the homogeneous component of degree `k` by `c ^ k`. -/
private theorem aeval_scale_eq_sum_homogeneous [CommSemiring K] {N : ℕ}
    {p : MvPolynomial (Fin N) K} {r : ℕ} (hr : p.totalDegree ≤ r) (c : K) :
    aeval (fun i => C c * X i) p = ∑ k ∈ range (r + 1), C c ^ k * homogeneousComponent k p := by
  calc aeval (fun i => C c * X i) p
      = ∑ s ∈ p.support, C c ^ s.degree * monomial s (p.coeff s) := by
        conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
        refine sum_congr rfl fun s _ => ?_
        rw [aeval_monomial, algebraMap_eq, monomial_eq, Finsupp.prod, Finsupp.prod]
        simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, Finsupp.degree_apply]
        ring
    _ = _ := by
        rw [← sum_fiberwise_of_maps_to
          (fun s hs => mem_range_succ_iff.2 ((le_totalDegree hs).trans hr))]
        refine sum_congr rfl fun k _ => ?_
        rw [homogeneousComponent_apply, mul_sum]
        exact sum_congr rfl fun s hs => by rw [(mem_filter.1 hs).2]

/-- The homogeneous components of degree at most `D` sum to `truncateTotalDegree D`. -/
private theorem sum_homogeneousComponent_eq_truncate [CommSemiring K] {σ : Type*} (D : ℕ)
    (p : MvPolynomial σ K) :
    ∑ k ∈ range (D + 1), homogeneousComponent k p = truncateTotalDegree D p := by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncateTotalDegree]

/-- **Low-degree truncation for arithmetic circuits.** Over a field of characteristic zero, if `c`
computes a polynomial of total degree at most `r`, then `truncateTotalDegree D (c.polynomial 0)` is
computed by an arithmetic circuit of size at most `(r + 1) * (c.size + 2 * N + 3) + 1`. -/
theorem exists_lowPart_circuit [Field K] [CharZero K] {N : ℕ} (D r : ℕ)
    (c : Circuit (arithSignature K) N 1) (hr : (c.polynomial 0).totalDegree ≤ r) :
    ∃ low : Circuit (arithSignature K) N 1,
      low.polynomial 0 = truncateTotalDegree D (c.polynomial 0) ∧
      low.size ≤ (r + 1) * (c.size + 2 * N + 3) + 1 := by
  have hscale (j : ℕ) : ∃ g : Circuit (arithSignature K) N N,
      (∀ k, g.polynomial k = C (j : K) * X k) ∧ g.size ≤ 2 * N := by
    have hone (k : Fin N) : ∃ h : Circuit (arithSignature K) N 1,
        h.polynomial 0 = C (j : K) * X k ∧ h.size ≤ 2 := by
      have hs : Synthesis (arithInterpretationWith K C) (inputs N)
          {fun x : Fin N → MvPolynomial (Fin N) K => C (j : K) * x k} 2 :=
        (Synthesis.arith_const (constant := C) (j : K)).combine
          (Synthesis.of_mem (I := arithInterpretationWith K C) (s := inputs N) ⟨k, rfl⟩)
          (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
      exact hs.exists_circuit_polynomial
    choose h hh hhs using hone
    refine ⟨Circuit.pi h, fun k => ?_, ?_⟩
    · simp only [Circuit.polynomial, Circuit.eval_pi]; exact hh k
    · rw [Circuit.size_pi]
      calc ∑ k : Fin N, (h k).size ≤ ∑ _k : Fin N, 2 := sum_le_sum fun k _ => hhs k
        _ = 2 * N := by simp [mul_comm]
  choose sc hsc hscSize using hscale
  let fs (j : ℕ) : Circuit (arithSignature K) N 1 := c.comp (sc j)
  let w (j : ℕ) : K := ∑ i ∈ range (D + 1),
    (Lagrange.basis (range (r + 1)) (fun t : ℕ => (t : K)) j).coeff i
  obtain ⟨res, hres, hresSize⟩ := exists_linearComb_circuit (range (r + 1)) w fs
  refine ⟨res, ?_, ?_⟩
  · let Q : Polynomial (MvPolynomial (Fin N) K) :=
      ∑ k ∈ range (r + 1), Polynomial.C (homogeneousComponent k (c.polynomial 0)) * Polynomial.X ^ k
    have hQdeg : Q.natDegree < #(range (r + 1)) :=
      (card_range (r + 1)).symm ▸ Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _
        fun _ hk => (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (mem_range_succ_iff.1 hk))
    have hQcoeff (k : ℕ) : Q.coeff k = homogeneousComponent k (c.polynomial 0) := by
      simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
      split_ifs with h
      exacts [rfl, (homogeneousComponent_eq_zero _ _ (by omega)).symm]
    have hQeval (a : K) : Q.eval (C a) = aeval (fun i => C a * X i) (c.polynomial 0) := by
      rw [aeval_scale_eq_sum_homogeneous hr, Polynomial.eval_finsetSum]
      exact sum_congr rfl fun k _ => by
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          mul_comm]
    have hfs (j : ℕ) : (fs j).polynomial 0 = aeval (fun i => C (j : K) * X i) (c.polynomial 0) := by
      rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
      have hsc_eq : (sc j).eval (arithInterpretationWith K C) X = fun k => C (j : K) * X k :=
        funext fun k => hsc j k
      rw [hsc_eq]
    rw [hres, ← sum_homogeneousComponent_eq_truncate]
    simp_rw [← hQcoeff, Lagrange.coeff_eq_sum_coeff_basis_smul_eval (v := fun t : ℕ => (t : K))
      Nat.cast_injective.injOn hQdeg, algebraMap_eq, hQeval, smul_eq_C_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [hfs j, map_sum, sum_mul]
  · have hsum_le : ∑ j ∈ range (r + 1), (fs j).size ≤ (r + 1) * (c.size + 2 * N) := by
      calc ∑ j ∈ range (r + 1), (fs j).size
          ≤ ∑ _j ∈ range (r + 1), (c.size + 2 * N) := sum_le_sum fun j _ => by
            rw [Circuit.size_comp]; have := hscSize j; omega
        _ = (r + 1) * (c.size + 2 * N) := by rw [sum_const, card_range, smul_eq_mul]
    rw [card_range] at hresSize
    linarith

/-- Explicit polynomial size bound for extracting a degree-`D` root of an `(N + 1)`-variate
arithmetic circuit of size `s` and total degree at most `r` in characteristic zero. -/
def circuitRootCost (s r N D : ℕ) : ℕ :=
  128 * (D + 1) ^ 3 * (r + 1) ^ 3 * (s + N + D + 10)

/-- `circuitRootCost` is monotone in all four arguments. -/
theorem circuitRootCost_mono {s s' r r' N N' D D' : ℕ}
    (hs : s ≤ s') (hr : r ≤ r') (hN : N ≤ N') (hD : D ≤ D') :
    circuitRootCost s r N D ≤ circuitRootCost s' r' N' D' := by
  unfold circuitRootCost
  gcongr

private theorem lastVariableEquiv_shift_aux [CommRing K] {N : ℕ} (x₀ : Fin N → K) (α : K)
    (p : MvPolynomial (Fin (N + 1)) K) :
    lastVariableEquiv K N (shift (Fin.lastCases α x₀) p) =
      Polynomial.taylor (C α) ((lastVariableEquiv K N p).map (shift x₀ : _ →ₐ[K] _).toRingHom) := by
  have h : (lastVariableEquiv K N).toRingHom.comp
      (shift (Fin.lastCases α x₀) : _ →ₐ[K] MvPolynomial (Fin (N + 1)) K).toRingHom =
      (Polynomial.taylorAlgHom (C α)).toRingHom.comp ((Polynomial.mapRingHom
        (shift x₀ : _ →ₐ[K] MvPolynomial (Fin N) K).toRingHom).comp
        (lastVariableEquiv K N).toRingHom) :=
    ringHom_ext (fun a => by simp) fun i => by
      refine Fin.lastCases ?_ (fun k => ?_) i <;>
        simp [lastVariableEquiv_X_last, lastVariableEquiv_X_castSucc, shift_X]
  exact RingHom.congr_fun h p

/-- **Low-degree root extraction for general arithmetic circuits in characteristic zero.**
If `F` is a fan-in-two arithmetic circuit in `N + 1` variables computing a nonzero polynomial
`P(x, y)` of total degree at most `r`, and `f(x)` is a polynomial of total degree `D` satisfying
`P(x, f(x)) = 0`, then `f` is computed by an arithmetic circuit of size at most
`circuitRootCost F.size r N f.totalDegree`. -/
theorem exists_circuit_of_root [Field K] [CharZero K] {N r : ℕ}
    {F : Circuit (arithSignature K) (N + 1) 1}
    (hF : F.polynomial 0 ≠ 0) (hdeg : (F.polynomial 0).totalDegree ≤ r)
    {f : MvPolynomial (Fin N) K}
    (hroot :
      aeval (Fin.lastCases f X : Fin (N + 1) → MvPolynomial (Fin N) K) (F.polynomial 0) = 0) :
    ∃ G : Circuit (arithSignature K) N 1,
      G.polynomial 0 = f ∧ G.size ≤ circuitRootCost F.size r N f.totalDegree := by
  classical
  set D := f.totalDegree
  have hP : lastVariableEquiv K N (F.polynomial 0) ≠ 0 := fun h =>
    hF ((lastVariableEquiv K N).injective (h.trans (map_zero _).symm))
  have hPf : (lastVariableEquiv K N (F.polynomial 0)).eval f = 0 := by rwa [eval_lastVariableEquiv]
  obtain ⟨j, x₀, -, hshift⟩ := exists_shift_eq_truncate_sum_of_root hP hPf
  set α := eval x₀ f
  set Q := Polynomial.taylor (C α)
    ((Polynomial.derivative^[j] (lastVariableEquiv K N (F.polynomial 0))).map
      (shift x₀ : _ →ₐ[K] _).toRingHom)
  set c := constantCoeff (Q.coeff 1)
  obtain ⟨derivC, hderivP, hderivS, hderivDeg⟩ := exists_derivLast_circuit j r F hdeg
  obtain ⟨QC, hQP, hQS, hQDeg⟩ := exists_shift_circuit (Fin.lastCases α x₀) derivC
  have hQeq : lastVariableEquiv K N (QC.polynomial 0) = Q := by
    rw [hQP, lastVariableEquiv_shift_aux, hderivP]
  -- Build `G₀ = y - c⁻¹ * QC`.
  have hG0_step : ∃ comb : Circuit (arithSignature K) 2 1,
      comb.polynomial 0 = X 0 + C (-c⁻¹) * X 1 ∧ comb.size ≤ 3 := by
    have hs : Synthesis (arithInterpretationWith K C) (inputs 2)
        {fun x : Fin 2 → MvPolynomial (Fin 2) K => x 0 + C (-c⁻¹) * x 1} 3 :=
      (Synthesis.of_mem (I := arithInterpretationWith K C) (s := inputs 2) ⟨0, rfl⟩).combine
        ((Synthesis.arith_const (constant := C) (-c⁻¹)).combine
          (Synthesis.of_mem (I := arithInterpretationWith K C) (s := inputs 2) ⟨1, rfl⟩)
          (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)))
        (Synthesis.arith_add (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    exact hs.exists_circuit_polynomial
  obtain ⟨combG0, hcombG0, hcombG0S⟩ := hG0_step
  let G0 : Circuit (arithSignature K) (N + 1) 1 :=
    combG0.comp (Circuit.pi ![Circuit.wiring _ (fun _ => Fin.last N), QC])
  have hG0_poly : G0.polynomial 0 = X (Fin.last N) + C (-c⁻¹) * QC.polynomial 0 := by
    rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial, hcombG0]
    simp only [map_add, map_mul, aeval_X, aeval_C, algebraMap_eq, Circuit.eval_pi,
      Matrix.cons_val_zero, Matrix.cons_val_one, Circuit.eval_wiring, Function.comp_apply]
    rfl
  have hG0_last :
      lastVariableEquiv K N (G0.polynomial 0) = Polynomial.X - Polynomial.C (C c⁻¹) * Q := by
    rw [hG0_poly, map_add, map_mul, lastVariableEquiv_X_last, lastVariableEquiv_C, hQeq,
      map_neg, Polynomial.C_neg]
    ring
  have hG0_deg : (G0.polynomial 0).totalDegree ≤ r + 1 := by
    rw [hG0_poly]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_X_le _).trans (by omega)) ?_)
    exact ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])).trans
      ((hQDeg.trans hderivDeg).trans (by omega))
  have hG0_size : G0.size ≤ QC.size + 3 := by
    simp only [G0, Circuit.size_comp, Circuit.size_pi, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Circuit.size_wiring, zero_add]
    omega
  -- Powers `Pm m = G0 ^ (m + 1)` and coefficients `Cm m = [y ^ m] Pm m`.
  set R := 2 * (D + 1) * (r + 1) with hRdef
  have hCm_ex (m : ℕ) (hm : m ∈ range (2 * (D + 1))) :
      ∃ cm : Circuit (arithSignature K) N 1,
        cm.polynomial 0 = ((Polynomial.X - Polynomial.C (C c⁻¹) * Q) ^ (m + 1)).coeff m ∧
        cm.size ≤ (R + 1) * (G0.size + 2 * (D + 1) + N + 4) + 1 ∧
        (cm.polynomial 0).totalDegree ≤ R := by
    obtain ⟨pm, hpmP, hpmS⟩ := exists_pow_circuit G0 m
    have hpmDeg : (pm.polynomial 0).totalDegree ≤ R := by
      rw [hpmP]
      refine (totalDegree_pow _ _).trans ?_
      have hm' : m + 1 ≤ 2 * (D + 1) := mem_range.mp hm
      exact Nat.mul_le_mul hm' hG0_deg
    obtain ⟨cm, hcmP, hcmS, hcmDeg⟩ := exists_coeffLast_circuit m R pm hpmDeg
    refine ⟨cm, ?_, ?_, hcmDeg⟩
    · rw [hcmP, hpmP, map_pow, hG0_last]
    · have hm' : m ≤ 2 * (D + 1) := (mem_range.mp hm).le
      have : pm.size + N + 4 ≤ G0.size + 2 * (D + 1) + N + 4 := by omega
      exact hcmS.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 1)
  have hCm_all (m : ℕ) : ∃ cm : Circuit (arithSignature K) N 1,
      (m ∈ range (2 * (D + 1)) →
        cm.polynomial 0 = ((Polynomial.X - Polynomial.C (C c⁻¹) * Q) ^ (m + 1)).coeff m ∧
        cm.size ≤ (R + 1) * (G0.size + 2 * (D + 1) + N + 4) + 1 ∧
        (cm.polynomial 0).totalDegree ≤ R) := by
    by_cases hm : m ∈ range (2 * (D + 1))
    · obtain ⟨cm, h1, h2, h3⟩ := hCm_ex m hm
      exact ⟨cm, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨Circuit.oneGate (.const 0) Fin.elim0, fun h => absurd h hm⟩
  choose Cm hCm using hCm_all
  obtain ⟨SC, hSP, hSS⟩ := exists_linearComb_circuit (range (2 * (D + 1)))
    (fun m => ((m : K) + 1)⁻¹) Cm
  have hS_eq : SC.polynomial 0 = ∑ m ∈ range (2 * (D + 1)),
      ((m : K) + 1)⁻¹ • ((Polynomial.X - Polynomial.C (C c⁻¹) * Q) ^ (m + 1)).coeff m := by
    rw [hSP]
    refine sum_congr rfl fun m hm => ?_
    rw [(hCm m hm).1, smul_eq_C_mul]
  have hSDeg : (SC.polynomial 0).totalDegree ≤ R := by
    rw [hSP]
    refine totalDegree_finsetSum_le fun m hm => ?_
    exact ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])).trans (hCm m hm).2.2
  obtain ⟨LC, hLP, hLS⟩ := exists_lowPart_circuit D R SC hSDeg
  -- Add constant `α` and shift by `-x₀`.
  have haddA : ∃ addA : Circuit (arithSignature K) 1 1,
      addA.polynomial 0 = C α + X 0 ∧ addA.size ≤ 2 := by
    have hs : Synthesis (arithInterpretationWith K C) (inputs 1)
        {fun x : Fin 1 → MvPolynomial (Fin 1) K => C α + x 0} 2 :=
      (Synthesis.arith_const (constant := C) α).combine
        (Synthesis.of_mem (I := arithInterpretationWith K C) (s := inputs 1) ⟨0, rfl⟩)
        (Synthesis.arith_add (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    exact hs.exists_circuit_polynomial
  obtain ⟨addA, haddAP, haddAS⟩ := haddA
  let TC : Circuit (arithSignature K) N 1 := addA.comp LC
  have hTP : TC.polynomial 0 = shift x₀ f := by
    rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial, haddAP,
      map_add, aeval_C, algebraMap_eq, aeval_X]
    change C α + LC.polynomial 0 = shift x₀ f
    rw [hLP, hS_eq, hshift D le_rfl]
  obtain ⟨finalC, hfinalP, hfinalS, -⟩ := exists_shift_circuit (fun i => -x₀ i) TC
  refine ⟨finalC, ?_, ?_⟩
  · rw [hfinalP, hTP, shift_neg_shift]
  · -- Explicit polynomial size arithmetic bound without heavy nonlinear search.
    set W := F.size + N + D + 10 with hWdef
    set A := D + 1 with hAdef
    set B := r + 1 with hBdef
    have hA1 : 1 ≤ A := Nat.succ_pos D
    have hB1 : 1 ≤ B := Nat.succ_pos r
    have hW1 : 10 ≤ W := by omega
    have hG0_bound : G0.size + 2 * A + N + 4 ≤ 4 * B * W := by
      have h1 : G0.size ≤ B * (F.size + N + 6) + 2 * N + 8 := by omega
      have h2 : B * (F.size + N + 6) ≤ B * W := Nat.mul_le_mul_left B (by omega)
      have h3 : 2 * N + 8 + 2 * A + N + 4 ≤ 3 * W := by omega
      have h4 : 3 * W ≤ 3 * (B * W) := Nat.mul_le_mul_left 3 (Nat.le_mul_of_pos_left W hB1)
      calc G0.size + 2 * A + N + 4
          ≤ B * (F.size + N + 6) + (2 * N + 8 + 2 * A + N + 4) := by omega
        _ ≤ B * W + 3 * (B * W) := Nat.add_le_add h2 (h3.trans h4)
        _ = 4 * B * W := by ring
    have hR1 : R + 1 ≤ 3 * A * B := by
      have hAB : 1 ≤ A * B := Nat.mul_pos hA1 hB1
      calc R + 1 = 2 * (A * B) + 1 := by rw [hRdef]; ring
        _ ≤ 2 * (A * B) + A * B := Nat.add_le_add_left hAB _
        _ = 3 * A * B := by ring
    have hCm_bound (m : ℕ) (hm : m ∈ range (2 * A)) :
        (Cm m).size ≤ 13 * A * B ^ 2 * W := by
      have hpos : 1 ≤ A * B ^ 2 * W := Nat.succ_le_of_lt (by positivity)
      calc (Cm m).size ≤ (R + 1) * (G0.size + 2 * A + N + 4) + 1 := (hCm m hm).2.1
        _ ≤ (3 * A * B) * (4 * B * W) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul hR1 hG0_bound) 1
        _ = 12 * (A * B ^ 2 * W) + 1 := by ring
        _ ≤ 12 * (A * B ^ 2 * W) + A * B ^ 2 * W := Nat.add_le_add_left hpos _
        _ = 13 * A * B ^ 2 * W := by ring
    have hS_bound : SC.size ≤ 28 * A ^ 2 * B ^ 2 * W := by
      have hsum : ∑ m ∈ range (2 * A), (Cm m).size ≤ 2 * A * (13 * A * B ^ 2 * W) := by
        calc ∑ m ∈ range (2 * A), (Cm m).size
            ≤ ∑ _m ∈ range (2 * A), (13 * A * B ^ 2 * W) := sum_le_sum hCm_bound
          _ = 2 * A * (13 * A * B ^ 2 * W) := by rw [sum_const, card_range, smul_eq_mul]
      rw [card_range] at hSS
      have htail : 3 * (2 * A) + 1 ≤ 2 * (A ^ 2 * B ^ 2 * W) := by
        have hAB2 : 1 ≤ A * B ^ 2 := Nat.succ_le_of_lt (by positivity)
        have hA_le : A ≤ A ^ 2 * B ^ 2 := by
          calc A = A * 1 := (mul_one A).symm
            _ ≤ A * (A * B ^ 2) := Nat.mul_le_mul_left A hAB2
            _ = A ^ 2 * B ^ 2 := by ring
        calc 3 * (2 * A) + 1 = 6 * A + 1 := by ring
          _ ≤ 7 * A := by omega
          _ ≤ 2 * W * A := Nat.mul_le_mul_right A (by omega)
          _ ≤ 2 * W * (A ^ 2 * B ^ 2) := Nat.mul_le_mul_left _ hA_le
          _ = 2 * (A ^ 2 * B ^ 2 * W) := by ring
      calc SC.size ≤ (∑ m ∈ range (2 * A), (Cm m).size) + 3 * (2 * A) + 1 := hSS
        _ ≤ 2 * A * (13 * A * B ^ 2 * W) + (3 * (2 * A) + 1) := by omega
        _ ≤ 26 * (A ^ 2 * B ^ 2 * W) + 2 * (A ^ 2 * B ^ 2 * W) := by
            have : 2 * A * (13 * A * B ^ 2 * W) = 26 * (A ^ 2 * B ^ 2 * W) := by ring
            rw [this]
            exact Nat.add_le_add_left htail _
        _ = 28 * A ^ 2 * B ^ 2 * W := by ring
    have hL_bound : LC.size ≤ 91 * A ^ 3 * B ^ 3 * W := by
      have hSC2 : SC.size + 2 * N + 3 ≤ 30 * A ^ 2 * B ^ 2 * W := by
        have h1 : 2 * N + 3 ≤ 2 * W := by omega
        have hAB2 : 1 ≤ A ^ 2 * B ^ 2 := Nat.succ_le_of_lt (by positivity)
        have h2 : 2 * W ≤ 2 * (A ^ 2 * B ^ 2 * W) :=
          Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left W hAB2)
        calc SC.size + 2 * N + 3 = SC.size + (2 * N + 3) := by omega
          _ ≤ 28 * A ^ 2 * B ^ 2 * W + 2 * (A ^ 2 * B ^ 2 * W) :=
              Nat.add_le_add hS_bound (h1.trans h2)
          _ = 30 * A ^ 2 * B ^ 2 * W := by ring
      have hpos : 1 ≤ A ^ 3 * B ^ 3 * W := Nat.succ_le_of_lt (by positivity)
      calc LC.size ≤ (R + 1) * (SC.size + 2 * N + 3) + 1 := hLS
        _ ≤ (3 * A * B) * (30 * A ^ 2 * B ^ 2 * W) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul hR1 hSC2) 1
        _ = 90 * A ^ 3 * B ^ 3 * W + 1 := by ring
        _ ≤ 90 * A ^ 3 * B ^ 3 * W + A ^ 3 * B ^ 3 * W := Nat.add_le_add_left hpos _
        _ = 91 * A ^ 3 * B ^ 3 * W := by ring
    have hTC_size : TC.size ≤ LC.size + 2 := by
      rw [Circuit.size_comp]; omega
    have hfinal_bound : finalC.size ≤ LC.size + 2 * N + 2 := by omega
    have htail : 2 * N + 2 ≤ 2 * (A ^ 3 * B ^ 3 * W) := by
      have h1 : 2 * N + 2 ≤ 2 * W := by omega
      have hAB3 : 1 ≤ A ^ 3 * B ^ 3 := Nat.succ_le_of_lt (by positivity)
      exact h1.trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left W hAB3))
    calc finalC.size ≤ LC.size + (2 * N + 2) := by omega
      _ ≤ 91 * A ^ 3 * B ^ 3 * W + 2 * (A ^ 3 * B ^ 3 * W) := Nat.add_le_add hL_bound htail
      _ = 93 * (A ^ 3 * B ^ 3 * W) := by ring
      _ ≤ 128 * (A ^ 3 * B ^ 3 * W) := Nat.mul_le_mul_right _ (by decide)
      _ = circuitRootCost F.size r N D := by simp only [circuitRootCost, A, B, W]; ring

end CircuitCombinators

/-! ## : White-Box and Black-Box PIT, Schwartz–Zippel, Range Avoidance, and Lower Bounds -/

section PITAndHittingSets

open Turing.MultiTapeTM Filter

/-- The set of `n`-variate arithmetic circuits over `K` computing a nonzero formal polynomial. -/
def ArithNonZero (K : Type*) [CommSemiring K] (n : ℕ) : Set (Circuit (arithSignature K) n 1) :=
  {c | c.polynomial 0 ≠ 0}

/-- White-box Polynomial Identity Testing (nonzeroness) for rational arithmetic circuits, encoded
via `encRatArithCircuit 1`. -/
def WhiteBoxPIT : Set (Σ n, Circuit (arithSignature ℚ) n 1) :=
  {p | p.2.polynomial 0 ≠ 0}

/-- White-box PIT restricted to rational arithmetic circuits of syntactic degree at most `d n`. -/
def WhiteBoxBoundedPIT (d : ℕ → ℕ) : Set (Σ n, Circuit (arithSignature ℚ) n 1) :=
  {p | p.2.syntacticDegree ≤ d p.1 ∧ p.2.polynomial 0 ≠ 0}

/-- Deterministic subexponential time `⋂ ε > 0, DTIME(2 ^ ⌈n ^ ε⌉₊)`. -/
noncomputable def DSUBEXP {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋂ (ε : ℝ) (_ : 0 < ε), Complexity.DTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊

/-- Nondeterministic subexponential time `⋂ ε > 0, NTIME(2 ^ ⌈n ^ ε⌉₊)`. -/
noncomputable def NSUBEXP {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  ⋂ (ε : ℝ) (_ : 0 < ε), Complexity.NTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊

/-- Membership characterization for `DSUBEXP`. -/
theorem mem_DSUBEXP_iff {α : Type*} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ DSUBEXP enc ↔
      ∀ ε : ℝ, 0 < ε → A ∈ Complexity.DTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  simp [DSUBEXP]

/-- Membership characterization for `NSUBEXP`. -/
theorem mem_NSUBEXP_iff {α : Type*} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NSUBEXP enc ↔
      ∀ ε : ℝ, 0 < ε → A ∈ Complexity.NTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  simp [NSUBEXP]

/-- Every polynomial `n ^ k` is eventually at most `2 ^ ⌈n ^ ε⌉₊` for every `ε > 0`. -/
theorem eventually_pow_le_two_pow_ceil_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, n ^ k ≤ 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  have hlim := (isLittleO_log_rpow_atTop hε).comp_tendsto tendsto_natCast_atTop_atTop
  have hpos : (0 : ℝ) < Real.log 2 / (k + 1 : ℝ) := by positivity
  have hbound := hlim.bound hpos
  filter_upwards [hbound, eventually_ge_atTop 2] with n hn hn2
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hrpow_nn : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hn_pos.le ε
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlog_nn,
    abs_of_nonneg hrpow_nn] at hn
  have h1 : (k : ℝ) * Real.log (n : ℝ) ≤ Real.log 2 * (n : ℝ) ^ ε := by
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hn hk1.le
    rw [← mul_assoc, mul_div_cancel₀ _ hk1.ne'] at hmul
    have hkle : (k : ℝ) * Real.log (n : ℝ) ≤ (k + 1 : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog_nn
    exact hkle.trans hmul
  have h2 : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (⌈(n : ℝ) ^ ε⌉₊ : ℕ) := by
    have hle_ceil : (n : ℝ) ^ ε ≤ (⌈(n : ℝ) ^ ε⌉₊ : ℝ) := Nat.le_ceil _
    have hlog2_pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog_ineq : Real.log ((n : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ (⌈(n : ℝ) ^ ε⌉₊ : ℕ)) := by
      rw [Real.log_pow, Real.log_pow]
      calc (k : ℝ) * Real.log (n : ℝ)
          ≤ Real.log 2 * (n : ℝ) ^ ε := h1
        _ ≤ Real.log 2 * (⌈(n : ℝ) ^ ε⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hle_ceil hlog2_pos
        _ = (⌈(n : ℝ) ^ ε⌉₊ : ℝ) * Real.log 2 := mul_comm _ _
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_ineq
  exact_mod_cast h2

/-- Polynomial time lies inside deterministic subexponential time. -/
theorem P_subset_DSUBEXP {α : Type*} {enc : α ↪ List Bool} :
    Complexity.P enc ⊆ DSUBEXP enc := by
  intro A hA
  rw [mem_DSUBEXP_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := Complexity.mem_P_iff_exists_mem_DTIME.mp hA
  exact Complexity.DTIME_mono_of_eventually_le (eventually_pow_le_two_pow_ceil_rpow k hε) hk

/-- Deterministic subexponential time lies inside nondeterministic subexponential time. -/
theorem DSUBEXP_subset_NSUBEXP {α : Type*} {enc : α ↪ List Bool} :
    DSUBEXP enc ⊆ NSUBEXP enc := by
  intro A hA
  rw [mem_NSUBEXP_iff]
  intro ε hε
  exact Complexity.DTIME_subset_NTIME ((mem_DSUBEXP_iff.mp hA) ε hε)

/-- For every `k ≥ 1`, `NSUBEXP` lies inside `NTIME(2 ^ (k * n))`. -/
theorem NSUBEXP_subset_NTIME_two_pow {α : Type*} {enc : α ↪ List Bool} {k : ℕ} (hk : 1 ≤ k) :
    NSUBEXP enc ⊆ Complexity.NTIME enc fun n => 2 ^ (k * n) := by
  intro A hA
  have hhalf := (mem_NSUBEXP_iff.mp hA) (1 / 2 : ℝ) (by norm_num)
  refine Complexity.NTIME_mono_of_eventually_le ?_ hhalf
  filter_upwards [eventually_ge_atTop 4] with n hn
  refine Nat.pow_le_pow_right two_pos ?_
  have hceil : ⌈(n : ℝ) ^ (1 / 2 : ℝ)⌉₊ ≤ n := by
    refine Nat.ceil_le.mpr ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = n := Real.rpow_one _
  exact hceil.trans (Nat.le_mul_of_pos_left n hk)

/-- **Nondeterministic linear exponential time is not contained in `NSUBEXP`**, witnessed
explicitly by `expLazyDiagonal 1`. -/
theorem NE_not_subset_NSUBEXP : ¬ (Complexity.NE encBits ⊆ NSUBEXP encBits) := by
  intro hsub
  have hmem : Complexity.expLazyDiagonal 1 ∈ Complexity.NE encBits :=
    Complexity.mem_NE_iff.mpr ⟨8 * 1 + 16, Complexity.expLazyDiagonal_mem_NTIME 1⟩
  have hnt : Complexity.expLazyDiagonal 1 ∈ Complexity.NTIME encBits fun n => 2 ^ (1 * n) :=
    NSUBEXP_subset_NTIME_two_pow le_rfl (hsub hmem)
  exact Complexity.expLazyDiagonal_notMem_NTIME 1 hnt

/-- **`NEXP` is not contained in `NSUBEXP`**. -/
theorem NEXP_not_subset_NSUBEXP : ¬ (Complexity.NEXP encBits ⊆ NSUBEXP encBits) :=
  fun hsub => NE_not_subset_NSUBEXP (Complexity.NE_subset_NEXP.trans hsub)

/-! ### Black-Box Hitting Sets and Schwartz–Zippel for Arithmetic Circuits -/

/-- A finite set of points `H` is a *circuit hitting set* for a set `𝒞` of `n`-variate arithmetic
circuits if every circuit in `𝒞` computing a nonzero formal polynomial evaluates to a nonzero value
at some point of `H`. -/
def IsCircuitHittingSet {K : Type*} [CommSemiring K] {n : ℕ}
    (H : Finset (Fin n → K)) (𝒞 : Set (Circuit (arithSignature K) n 1)) : Prop :=
  ∀ c ∈ 𝒞, c.polynomial 0 ≠ 0 → ∃ a ∈ H, c.eval (arithInterpretation K) a 0 ≠ 0

/-- Circuit hitting sets are precisely polynomial hitting sets for the image of `𝒞` under
`Circuit.polynomial`. -/
theorem isCircuitHittingSet_iff_isHittingSet {K : Type*} [CommSemiring K] {n : ℕ}
    (H : Finset (Fin n → K)) (𝒞 : Set (Circuit (arithSignature K) n 1)) :
    IsCircuitHittingSet H 𝒞 ↔ IsHittingSet H ((fun c : Circuit (arithSignature K) n 1 =>
      c.polynomial 0) '' 𝒞) := by
  constructor
  · rintro hH _ ⟨c, hc, rfl⟩ hc0
    obtain ⟨a, ha, hne⟩ := hH c hc hc0
    exact ⟨a, ha, by rwa [Circuit.eval_polynomial]⟩
  · intro hH c hc hc0
    obtain ⟨a, ha, hne⟩ := hH (c.polynomial 0) ⟨c, hc, rfl⟩ hc0
    exact ⟨a, ha, by rwa [← Circuit.eval_polynomial]⟩

/-- **Black-box hitting sets decide white-box PIT on the hit class**: a circuit `c ∈ 𝒞` computes a
nonzero formal polynomial if and only if it evaluates to a nonzero value at some point of `H`. -/
theorem IsCircuitHittingSet.nonzero_iff {K : Type*} [CommSemiring K] {n : ℕ}
    {H : Finset (Fin n → K)} {𝒞 : Set (Circuit (arithSignature K) n 1)}
    (hH : IsCircuitHittingSet H 𝒞) {c : Circuit (arithSignature K) n 1} (hc : c ∈ 𝒞) :
    c.polynomial 0 ≠ 0 ↔ ∃ a ∈ H, c.eval (arithInterpretation K) a 0 ≠ 0 := by
  refine ⟨hH c hc, ?_⟩
  rintro ⟨a, -, hne⟩ hzero
  apply hne
  rw [← Circuit.eval_polynomial, hzero, map_zero]

/-- **Schwartz–Zippel density bound for arithmetic circuits** over an integral domain `K`:
a nonzero circuit `c` vanishes on at most a `c.syntacticDegree / #S` fraction of `S ^ n`. -/
theorem circuit_schwartz_zippel_bound {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    {n : ℕ} {c : Circuit (arithSignature K) n 1} (hc : c.polynomial 0 ≠ 0) (S : Finset K) :
    #{a ∈ Fintype.piFinset (fun _ : Fin n => S) | c.eval (arithInterpretation K) a 0 = 0} /
        (#S ^ n : ℚ≥0) ≤
      (c.syntacticDegree : ℚ≥0) / #S := by
  have hfilter :
      {a ∈ Fintype.piFinset (fun _ : Fin n => S) | c.eval (arithInterpretation K) a 0 = 0} =
        {a ∈ Fintype.piFinset (fun _ : Fin n => S) | MvPolynomial.eval a (c.polynomial 0) = 0} := by
    ext a
    simp [Circuit.eval_polynomial]
  rw [hfilter]
  refine (MvPolynomial.schwartz_zippel_totalDegree hc S).trans ?_
  gcongr
  exact_mod_cast c.totalDegree_polynomial_le_syntacticDegree 0

/-- **Schwartz–Zippel counting bound for arithmetic circuits**: without division,
`#zeros * #S ≤ c.syntacticDegree * #S ^ n`. -/
theorem circuit_schwartz_zippel_counting {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    {n : ℕ} {c : Circuit (arithSignature K) n 1} (hc : c.polynomial 0 ≠ 0) (S : Finset K) :
    #{a ∈ Fintype.piFinset (fun _ : Fin n => S) | c.eval (arithInterpretation K) a 0 = 0} * #S ≤
      c.syntacticDegree * #S ^ n := by
  rcases Nat.eq_zero_or_pos #S with hS0 | hSpos
  · simp [hS0]
  · have hSpos' : (0 : ℚ≥0) < #S := by exact_mod_cast hSpos
    have hbound := circuit_schwartz_zippel_bound hc S
    rw [div_le_div_iff₀ (pow_pos hSpos' n) hSpos'] at hbound
    exact_mod_cast hbound

/-- **Grid witness for nonzero arithmetic circuits**: if `c.syntacticDegree < #S`, a nonzero
circuit evaluates to a nonzero value at some point of `S ^ n`. -/
theorem circuit_exists_nonvanishing_witness {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} {c : Circuit (arithSignature K) n 1} (hc : c.polynomial 0 ≠ 0) {S : Finset K}
    (hS : c.syntacticDegree < #S) :
    ∃ a : Fin n → K, (∀ i, a i ∈ S) ∧ c.eval (arithInterpretation K) a 0 ≠ 0 := by
  obtain ⟨a, ha, hne⟩ := MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card hc
    ((c.totalDegree_polynomial_le_syntacticDegree 0).trans_lt hS)
  exact ⟨a, ha, by rwa [← Circuit.eval_polynomial]⟩

/-- **Exact grid characterization of formal nonzeroness** when `c.syntacticDegree < #S`. -/
theorem circuit_nonzero_iff_grid_witness {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} {c : Circuit (arithSignature K) n 1} {S : Finset K}
    (hS : c.syntacticDegree < #S) :
    c.polynomial 0 ≠ 0 ↔
      ∃ a : Fin n → K, (∀ i, a i ∈ S) ∧ c.eval (arithInterpretation K) a 0 ≠ 0 := by
  refine ⟨fun hc => circuit_exists_nonvanishing_witness hc hS, ?_⟩
  rintro ⟨a, -, hne⟩ hzero
  apply hne
  rw [← Circuit.eval_polynomial, hzero, map_zero]

/-- **Bad-tuple counting bound (compression)**: for any nonzero circuit `c` of syntactic degree at
most `d` and any grid `S` with `2 * d ≤ #S`, at most `(#S ^ n) ^ r / 2 ^ r` of the `r`-tuples of
points in `S ^ n` vanish on `c` at every coordinate. -/
theorem badTuples_card_le {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    {n d r : ℕ} {c : Circuit (arithSignature K) n 1} (hc : c.polynomial 0 ≠ 0)
    (hd : c.syntacticDegree ≤ d) {S : Finset K} (hS : 2 * d ≤ #S) :
    2 ^ r * #{t ∈ Fintype.piFinset (fun _ : Fin r => Fintype.piFinset (fun _ : Fin n => S)) |
      ∀ j : Fin r, c.eval (arithInterpretation K) (t j) 0 = 0} ≤ (#S ^ n) ^ r := by
  let Z : Finset (Fin n → K) :=
    {a ∈ Fintype.piFinset (fun _ : Fin n => S) | c.eval (arithInterpretation K) a 0 = 0}
  have hZ : 2 * #Z ≤ #S ^ n := by
    rcases Nat.eq_zero_or_pos #S with hS0 | hSpos
    · have hd0 : d = 0 := by omega
      have hdeg0 : (c.polynomial 0).totalDegree = 0 :=
        Nat.eq_zero_of_le_zero
          ((c.totalDegree_polynomial_le_syntacticDegree 0).trans (hd.trans hd0.le))
      have hSempty : S = ∅ := card_eq_zero.mp hS0
      subst hSempty
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hconst : c.polynomial 0 = C (constantCoeff (c.polynomial 0)) :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
        have hne : constantCoeff (c.polynomial 0) ≠ 0 := fun h => by
          rw [h, map_zero] at hconst; exact hc hconst
        have hZ0 : Z = ∅ := by
          ext a
          simp only [Z, mem_filter, notMem_empty, iff_false, not_and]
          intro _ hev
          rw [← Circuit.eval_polynomial, hconst, eval_C] at hev
          exact hne hev
        simp [hZ0]
      · have hpi : Fintype.piFinset (fun _ : Fin n => (∅ : Finset K)) = ∅ := by
          ext a
          simp only [Fintype.mem_piFinset, notMem_empty, iff_false, not_forall]
          exact ⟨⟨0, hn⟩, id⟩
        simp [Z, hpi]
    · have hsz := (circuit_schwartz_zippel_counting hc S).trans
        (Nat.mul_le_mul_right _ hd)
      have hmul : 2 * #Z * #S ≤ #S ^ n * #S := by
        calc 2 * #Z * #S = 2 * (#Z * #S) := by ring
          _ ≤ 2 * (d * #S ^ n) := Nat.mul_le_mul_left 2 hsz
          _ = (2 * d) * #S ^ n := by ring
          _ ≤ #S * #S ^ n := Nat.mul_le_mul_right _ hS
          _ = #S ^ n * #S := mul_comm _ _
      exact Nat.le_of_mul_le_mul_right hmul hSpos
  have hbij :
      {t ∈ Fintype.piFinset (fun _ : Fin r => Fintype.piFinset (fun _ : Fin n => S)) |
        ∀ j : Fin r, c.eval (arithInterpretation K) (t j) 0 = 0} =
        Fintype.piFinset (fun _ : Fin r => Z) := by
    ext t
    simp [Z, Fintype.mem_piFinset, forall_and]
  rw [hbij, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, ← mul_pow]
  exact Nat.pow_le_pow_left hZ r

/-- **Probabilistic existence of small hitting sets for finite arithmetic circuit classes.**
If a finite family `𝒞` of nonzero `n`-variate circuits of syntactic degree at most `d` has
`#𝒞 < 2 ^ r` and `2 * d ≤ #S`, then there exists a hitting set `H ⊆ S ^ n` of size at most `r`. -/
theorem exists_small_hitting_set_of_finite_class {K : Type*} [CommRing K] [IsDomain K]
    {n d r : ℕ} {𝒞 : Finset (Circuit (arithSignature K) n 1)}
    (hnonzero : ∀ c ∈ 𝒞, c.polynomial 0 ≠ 0)
    (hdeg : ∀ c ∈ 𝒞, c.syntacticDegree ≤ d)
    {S : Finset K} (hS : 2 * d ≤ #S) (hSpos : 0 < #S)
    (hcard : #𝒞 < 2 ^ r) :
    ∃ H : Finset (Fin n → K), H ⊆ Fintype.piFinset (fun _ : Fin n => S) ∧
      #H ≤ r ∧ IsCircuitHittingSet H (𝒞 : Set (Circuit (arithSignature K) n 1)) := by
  classical
  let G : Finset (Fin n → K) := Fintype.piFinset (fun _ : Fin n => S)
  let Tuples : Finset (Fin r → Fin n → K) := Fintype.piFinset (fun _ : Fin r => G)
  let bad (c : Circuit (arithSignature K) n 1) : Finset (Fin r → Fin n → K) :=
    {t ∈ Tuples | ∀ j : Fin r, c.eval (arithInterpretation K) (t j) 0 = 0}
  have hTuples : #Tuples = (#S ^ n) ^ r := by
    simp [Tuples, G, Fintype.card_piFinset]
  have hbad_sum : 2 ^ r * #(𝒞.biUnion bad) ≤ #𝒞 * (#S ^ n) ^ r := by
    calc 2 ^ r * #(𝒞.biUnion bad)
        ≤ 2 ^ r * ∑ c ∈ 𝒞, #(bad c) := Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ c ∈ 𝒞, 2 ^ r * #(bad c) := mul_sum _ _ _
      _ ≤ ∑ _c ∈ 𝒞, (#S ^ n) ^ r :=
          sum_le_sum fun c hc => badTuples_card_le (hnonzero c hc) (hdeg c hc) hS
      _ = #𝒞 * (#S ^ n) ^ r := by rw [sum_const, smul_eq_mul]
  have hTuples_pos : 0 < (#S ^ n) ^ r := pow_pos (pow_pos hSpos n) r
  have hstrict : #(𝒞.biUnion bad) < #Tuples := by
    rw [hTuples]
    have hlt : 2 ^ r * #(𝒞.biUnion bad) < 2 ^ r * (#S ^ n) ^ r :=
      lt_of_le_of_lt hbad_sum (Nat.mul_lt_mul_of_pos_right hcard hTuples_pos)
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hne : (Tuples \ 𝒞.biUnion bad).Nonempty := by
    rw [← card_pos, card_sdiff]
    have hsub : 𝒞.biUnion bad ⊆ Tuples := biUnion_subset.mpr fun _ _ => filter_subset _ _
    rw [inter_eq_left.mpr hsub]
    omega
  obtain ⟨t, ht⟩ := hne
  rw [Finset.mem_sdiff] at ht
  refine ⟨univ.image t, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨j, -, rfl⟩ := mem_image.mp ha
    exact (Fintype.mem_piFinset.mp ht.1) j
  · exact card_image_le.trans (by simp)
  · intro c hc _
    have hnotbad : t ∉ bad c := fun h => ht.2 (mem_biUnion.mpr ⟨c, hc, h⟩)
    simp only [bad, mem_filter, ht.1, true_and, not_forall] at hnotbad
    obtain ⟨j, hj⟩ := hnotbad
    exact ⟨t j, mem_image_of_mem t (mem_univ j), hj⟩

/-! ### Range Avoidance (`HS ↔ dWPHP`) over Strictly Ordered Rings and Hybrid Root Decoder -/

/-- Over a ring `K`, there is an explicit arithmetic circuit computing the sum-of-squares target
avoidance polynomial `∏ t, ∑ j, (X j - target t j) ^ 2` with at most
`k * (4 * n + 2) + 2` gates and syntactic degree at most `2 * k`. -/
theorem exists_sumOfSquaresAvoidCircuit {K : Type*} [CommRing K] {n k : ℕ}
    (target : Fin k → Fin n → K) :
    ∃ c : Circuit (arithSignature K) n 1,
      c.polynomial 0 = ∏ t : Fin k, ∑ j : Fin n, (X j - C (target t j)) ^ 2 ∧
      c.size ≤ k * (4 * n + 2) + 2 := by
  let s0 : Set ((Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K) :=
    inputs n ∪ ({fun _ => (0 : MvPolynomial (Fin n) K)} ∪ {fun _ => 1})
  have h01 : Synthesis (arithInterpretationWith K C) (inputs n)
      ({fun _ => (0 : MvPolynomial (Fin n) K)} ∪ {fun _ => 1}) 2 := by
    have h0 : Synthesis (arithInterpretationWith K C) (inputs n)
        {fun _ : Fin n → MvPolynomial (Fin n) K => 0} 1 := by
      simpa only [map_zero] using Synthesis.arith_const (constant := C) (0 : K)
    have h1 : Synthesis (arithInterpretationWith K C) (inputs n)
        {fun _ : Fin n → MvPolynomial (Fin n) K => 1} 1 := by
      simpa only [map_one] using Synthesis.arith_const (constant := C) (1 : K)
    exact h0.union h1
  have hterm (t : Fin k) (j : Fin n) :
      Synthesis (arithInterpretationWith K C) s0
        {fun x : Fin n → MvPolynomial (Fin n) K => (x j - C (target t j)) ^ 2} 3 := by
    have hdiff : Synthesis (arithInterpretationWith K C) s0
        {fun x : Fin n → MvPolynomial (Fin n) K => x j + C (-target t j)} 2 :=
      (Synthesis.of_mem (I := arithInterpretationWith K C) (s := s0) (Or.inl ⟨j, rfl⟩)).combine
        (Synthesis.arith_const (constant := C) (-target t j))
        (Synthesis.arith_add (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    have hsq : (fun x : Fin n → MvPolynomial (Fin n) K => (x j - C (target t j)) ^ 2) =
        fun x => (x j + C (-target t j)) * (x j + C (-target t j)) := by
      funext x; rw [map_neg, ← sub_eq_add_neg, sq]
    exact hsq ▸ hdiff.trans
      (Synthesis.arith_mul (Set.mem_union_right _ rfl) (Set.mem_union_right _ rfl))
  have hfactor (t : Fin k) :
      Synthesis (arithInterpretationWith K C) s0
        {fun x : Fin n → MvPolynomial (Fin n) K => ∑ j : Fin n, (x j - C (target t j)) ^ 2}
        (4 * n) := by
    have hsum := Synthesis.arith_sum (constant := C) (univ : Finset (Fin n))
      (fun j x => (x j - C (target t j)) ^ 2) (fun _ => 3) (by simp [s0]) fun j _ => hterm t j
    simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm] using hsum
  have hprod := synthesis_arith_prod (univ : Finset (Fin k))
    (fun t x => ∑ j : Fin n, (x j - C (target t j)) ^ 2) (fun _ => 4 * n) (by simp [s0])
    fun t _ => hfactor t
  have hfull : Synthesis (arithInterpretationWith K C) (inputs n)
      {fun x => ∏ t : Fin k, ∑ j : Fin n, (x j - C (target t j)) ^ 2} (k * (4 * n + 2) + 2) :=
    (h01.trans hprod).mono Set.Subset.rfl Set.Subset.rfl (by
      rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      have : k * (4 * n + 1) ≤ k * (4 * n + 2) := Nat.mul_le_mul_left k (by omega)
      omega)
  exact hfull.exists_circuit_polynomial

/-- **Range avoidance equivalence over strictly ordered rings (`HS ↔ dWPHP`).**
Over a strictly ordered commutative ring `K` (such as `ℤ` or `ℚ`), for `n ≥ 1`, a finite set `H`
avoids the range of `target : Fin k → Fin n → K` (i.e., `∃ a ∈ H, ∀ t, a ≠ target t`) if and only
if `H` hits the sum-of-squares avoidance polynomial `∏ t, ∑ j, (X j - target t j) ^ 2`. -/
theorem hittingSet_iff_rangeAvoidance_orderedRing {K : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] {n k : ℕ} (target : Fin k → Fin n → K) (H : Finset (Fin n → K)) :
    (∃ a ∈ H, ∀ t : Fin k, a ≠ target t) ↔
      ∃ a ∈ H, eval a (∏ t : Fin k, ∑ j : Fin n, (X j - C (target t j)) ^ 2) ≠ 0 := by
  have heval (a : Fin n → K) :
      eval a (∏ t : Fin k, ∑ j : Fin n, (X j - C (target t j)) ^ 2) ≠ 0 ↔
        ∀ t : Fin k, a ≠ target t := by
    simp only [map_prod, map_sum, map_pow, map_sub, eval_X, eval_C, prod_ne_zero_iff, mem_univ,
      true_implies]
    refine forall_congr' fun t => ?_
    constructor
    · intro hne heq
      apply hne
      subst heq
      simp
    · intro hne hsum
      apply hne
      funext j
      have hsq : (a j - target t j) ^ 2 = 0 := by
        have hzero := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (a i - target t i)).mp hsum
        exact hzero j (mem_univ j)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  exact exists_congr fun a => and_congr_right fun _ => (heval a).symm

/-- **Constructive binary-halving hybrid root index.** Given a linearly ordered integral domain `K`
and a polynomial `p` in `n + 1` variables, records the sorted root index of `t` inside the
univariate restriction `evalPrefix u p`. -/
noncomputable def hybridRootIndex {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K]
    {n : ℕ} (p : MvPolynomial (Fin (n + 1)) K) (u : Fin n → K) (t : K) : ℕ :=
  ((MvPolynomial.evalPrefix u p).roots.toFinset.sort (· ≤ ·)).idxOf t

/-- For any prefix `u` where `evalPrefix u p ≠ 0`, every root `t` of `evalPrefix u p` lies in the
finite multiset `(evalPrefix u p).roots` of cardinality at most `p.degreeOf (Fin.last n)`. -/
theorem mem_roots_evalPrefix_of_eval_eq_zero {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} {p : MvPolynomial (Fin (n + 1)) K} {u : Fin n → K} {t : K}
    (hne : MvPolynomial.evalPrefix u p ≠ 0) (hzero : eval (Fin.snoc u t) p = 0) :
    t ∈ (MvPolynomial.evalPrefix u p).roots ∧
      Multiset.card (MvPolynomial.evalPrefix u p).roots ≤ p.degreeOf (Fin.last n) := by
  refine ⟨(Polynomial.mem_roots hne).mpr ?_,
    (Polynomial.card_roots' _).trans (MvPolynomial.natDegree_evalPrefix_le u p)⟩
  rw [Polynomial.IsRoot, MvPolynomial.eval_evalPrefix, MvPolynomial.eval_specializeLast]
  exact hzero

/-! ### Heintz–Schnorr: Black-Box PIT (Small Hitting Sets) Implies Algebraic Lower Bounds -/

/-- **Small hitting sets imply multilinear lower bounds.** If `H` is a hitting set for a class `𝒞`
of `n`-variate polynomials over a field `F` and `#H < 2 ^ n`, then there exists a nonzero
multilinear polynomial `f` (of individual degree at most `1` and total degree at most `n`) outside
`𝒞`. -/
theorem IsHittingSet.exists_multilinear_notMem {F : Type*} [Field F] {n : ℕ}
    {H : Finset (Fin n → F)} {𝒞 : Set (MvPolynomial (Fin n) F)}
    (hH : IsHittingSet H 𝒞) (hcard : #H < 2 ^ n) :
    ∃ f : MvPolynomial (Fin n) F,
      f ≠ 0 ∧ (∀ i, f.degreeOf i ≤ 1) ∧ f.totalDegree ≤ n ∧ f ∉ 𝒞 := by
  classical
  let toMono : (Fin n → Bool) → (Fin n →₀ ℕ) :=
    fun b => ∑ i : Fin n, Finsupp.single i (b i).toNat
  have htoMono_apply (b : Fin n → Bool) (i : Fin n) : toMono b i = (b i).toNat := by
    rw [show toMono b i = Finsupp.applyAddHom i (toMono b) from rfl, map_sum]
    simp only [Finsupp.applyAddHom_apply, Finsupp.single_apply, Finset.sum_ite_eq', mem_univ,
      ite_true]
  have hinj : Function.Injective toMono := by
    intro b₁ b₂ h
    funext i
    have hi : (b₁ i).toNat = (b₂ i).toNat := by
      simpa only [htoMono_apply] using congrArg (fun d : Fin n →₀ ℕ => d i) h
    cases hb1 : b₁ i <;> cases hb2 : b₂ i <;> simp_all
  let T : Finset (Fin n →₀ ℕ) := univ.image toMono
  have hTcard : #T = 2 ^ n := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  obtain ⟨f, hf0, hfT, hnot⟩ := hH.exists_notMem T (hTcard.symm ▸ hcard)
  refine ⟨f, hf0, ?_, ?_, hnot⟩
  · intro i
    rw [degreeOf_le_iff]
    intro d hd
    obtain ⟨b, -, rfl⟩ := mem_image.mp (hfT hd)
    rw [htoMono_apply]
    cases b i <;> simp
  · refine Finset.sup_le fun d hd => ?_
    obtain ⟨b, -, rfl⟩ := mem_image.mp (hfT hd)
    change Finsupp.degree _ ≤ n
    rw [map_sum]
    calc ∑ i : Fin n, (Finsupp.single i (b i).toNat).degree
        ≤ ∑ _i : Fin n, 1 := sum_le_sum fun i _ => by
          rw [Finsupp.degree_single]; cases b i <;> simp
      _ = n := by simp

/-- **Subexponential hitting sets imply superpolynomial algebraic circuit lower bounds.**
If a hitting-set family `H` for `boundedCircuitPolys F n (s n) (d n)` has `#(H n) < 2 ^ n`, then
there is a nonzero multilinear polynomial in `n` variables that cannot be computed by any
arithmetic circuit of size at most `s n` (and total degree at most `d n`). -/
theorem subexpHittingSet_implies_multilinear_circuit_lowerBound {F : Type*} [Field F]
    {n s d : ℕ} {H : Finset (Fin n → F)}
    (hH : IsHittingSet H (boundedCircuitPolys F n s d)) (hcard : #H < 2 ^ n) (hd : n ≤ d) :
    ∃ f : MvPolynomial (Fin n) F,
      f ≠ 0 ∧ (∀ i, f.degreeOf i ≤ 1) ∧ f.totalDegree ≤ n ∧
      ∀ c : Circuit (arithSignature F) n 1, c.polynomial 0 = f → s < c.size := by
  obtain ⟨f, hf0, hmul, hdeg, hnot⟩ := hH.exists_multilinear_notMem hcard
  refine ⟨f, hf0, hmul, hdeg, fun c hc => ?_⟩
  by_contra hle
  exact hnot ⟨c, hc, not_lt.mp hle, hdeg.trans hd⟩

end PITAndHittingSets

end Arithmetic
end Cslib.Circuits

/-! ## : Algebraic Nisan–Wigderson Designs on Boolean Truth Tables -/

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset

/-- The `i`-th block of a `NisanWigderson.Design ℓ m a n`, presented as an embedding
`Fin m ↪ Fin ℓ` in increasing order. -/
def Design.blockEmb {ℓ m a n : ℕ} (D : Design ℓ m a n) (i : Fin n) : Fin m ↪ Fin ℓ :=
  ((D.block i).orderEmbOfFin (D.card_block i)).toEmbedding

/-- The image of `D.blockEmb i` is `D.block i`. -/
@[simp] theorem Design.map_univ_blockEmb {ℓ m a n : ℕ} (D : Design ℓ m a n) (i : Fin n) :
    univ.map (D.blockEmb i) = D.block i := by
  ext x
  simp only [mem_map, mem_univ, true_and, Design.blockEmb, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨k, rfl⟩
    exact orderEmbOfFin_mem (D.block i) (D.card_block i) k
  · intro hx
    obtain ⟨k, hk⟩ : x ∈ Set.range ((D.block i).orderEmbOfFin (D.card_block i)) := by
      simpa using hx
    exact ⟨k, hk⟩

/-- Distinct blocks of `D.blockEmb` pairwise intersect in at most `a` coordinates. -/
theorem Design.card_map_blockEmb_inter_le {ℓ m a n : ℕ} (D : Design ℓ m a n)
    {i j : Fin n} (hij : i ≠ j) :
    #(univ.map (D.blockEmb i) ∩ univ.map (D.blockEmb j)) ≤ a := by
  rw [D.map_univ_blockEmb, D.map_univ_blockEmb]
  exact D.card_inter_le hij

end Cslib.Crypto.PRG.NisanWigderson

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

section AlgebraicNisanWigderson

open Cslib.Crypto.PRG.NisanWigderson Cslib.BitString

/-- The multilinear extension of a Boolean truth table `f : (Fin m → Bool) → Bool` over a
commutative ring `K`. -/
noncomputable def boolMultilinearExt (K : Type*) [CommRing K] {m : ℕ}
    (f : (Fin m → Bool) → Bool) : MvPolynomial (Fin m) K :=
  multilinearExtension fun x => bitVal K (f x)

/-- On every Boolean input `x`, `boolMultilinearExt K f` evaluates to `bitVal K (f x)`. -/
@[simp] theorem eval_bitPoint_boolMultilinearExt (K : Type*) [CommRing K] {m : ℕ}
    (f : (Fin m → Bool) → Bool) (x : Fin m → Bool) :
    eval (bitPoint x : Fin m → K) (boolMultilinearExt K f) = bitVal K (f x) :=
  eval_multilinearExtension (fun y => bitVal K (f y)) x

/-- `boolMultilinearExt K f` is multilinear: every variable has degree at most `1`. -/
theorem degreeOf_boolMultilinearExt_le_one (K : Type*) [CommRing K] {m : ℕ}
    (f : (Fin m → Bool) → Bool) (i : Fin m) :
    (boolMultilinearExt K f).degreeOf i ≤ 1 := by
  rw [degreeOf_le_iff, boolMultilinearExt]
  have h := multilinearExtension_mem_restrictDegree (R := K) (fun y => bitVal K (f y))
  rw [MvPolynomial.mem_restrictDegree] at h
  intro d hd
  exact h d hd i

/-- `boolMultilinearExt K f` has total degree at most `m`. -/
theorem totalDegree_boolMultilinearExt_le (K : Type*) [CommRing K] {m : ℕ}
    (f : (Fin m → Bool) → Bool) :
    (boolMultilinearExt K f).totalDegree ≤ m := by
  rw [boolMultilinearExt]
  simpa using totalDegree_multilinearExtension_le (R := K) (fun y => bitVal K (f y))

/-- The **algebraic Nisan–Wigderson generator** evaluating the multilinear extension of a Boolean
truth table `f` along the blocks of a combinatorial design `D`. -/
noncomputable def algNWGenerator (K : Type*) [CommRing K] {ℓ m a n : ℕ}
    (D : Design ℓ m a n) (f : (Fin m → Bool) → Bool) : Fin n → MvPolynomial (Fin ℓ) K :=
  nwGenerator (boolMultilinearExt K f) D.blockEmb

/-- **Exact agreement on the Boolean hypercube**: evaluating the algebraic Nisan–Wigderson
generator at a Boolean seed `z` yields the 0/1 embedding of the Boolean Nisan–Wigderson
generator `generator D f z`. -/
theorem eval_bitPoint_algNWGenerator (K : Type*) [CommRing K] {ℓ m a n : ℕ}
    (D : Design ℓ m a n) (f : (Fin m → Bool) → Bool) (z : Fin ℓ → Bool) (i : Fin n) :
    eval (bitPoint z : Fin ℓ → K) (algNWGenerator K D f i) =
      bitVal K (generator D f z i) := by
  rw [algNWGenerator, nwGenerator_apply, eval_rename]
  exact eval_bitPoint_boolMultilinearExt K f (D.restrict i z)

/-! ### General-Circuit Algebraic NW Hybrid Reconstruction and Hardness-to-Hitting-Sets -/

section GeneralCircuitNW

variable {K L : Type*} {m n : ℕ}

private noncomputable def circuitHybridInput [CommSemiring K] (f : MvPolynomial (Fin m) K)
    (S : Fin n → (Fin m ↪ L)) (k : ℕ) (j : Fin n) : MvPolynomial (L ⊕ Fin n) K :=
  if (j : ℕ) < k then rename Sum.inl (nwGenerator f S j) else X (Sum.inr j)

private noncomputable def circuitFreeVar (S : Fin n → (Fin m ↪ L)) (i : Fin n) :
    L ⊕ Fin n → (L ⊕ Fin n) ⊕ Fin (m + 1)
  | .inl l => Function.extend (S i) (fun k => .inr k.castSucc) (fun l => .inl (.inl l)) l
  | .inr j => if j = i then .inr (Fin.last m) else .inl (.inr j)

private theorem injective_circuitFreeVar (S : Fin n → (Fin m ↪ L)) (i : Fin n) :
    Function.Injective (circuitFreeVar S i) := by
  refine Function.LeftInverse.injective
    (g := Sum.elim id (Fin.lastCases (.inr i) fun k => .inl (S i k))) ?_
  rintro (l | j)
  · rcases Classical.em (∃ k, S i k = l) with ⟨k, rfl⟩ | hl
    · simp [circuitFreeVar, (S i).injective.extend_apply]
    · simp [circuitFreeVar, Function.extend_apply' _ _ _ hl]
  · by_cases hj : j = i <;> simp [circuitFreeVar, hj]

private noncomputable def circuitSpecialize [CommSemiring K] (S : Fin n → (Fin m ↪ L)) (i : Fin n)
    (v : L ⊕ Fin n → K) : L ⊕ Fin n → MvPolynomial (Fin (m + 1)) K :=
  Sum.elim (fun a => C (v a)) X ∘ circuitFreeVar S i

/-- **Algebraic Nisan–Wigderson hybrid argument for general arithmetic circuits.**
If `f` is multilinear in `m` variables, the blocks `S i` pairwise intersect in at most `a` seed
variables, and a general fan-in-two arithmetic circuit `F` computing a nonzero polynomial vanishes
on `nwGenerator f S`, then there exists an arithmetic circuit `Q` in `m + 1` variables such that:
* `Q.size ≤ F.size + n * (2 ^ a * (a + 3) + 2)`,
* `(Q.polynomial 0).totalDegree ≤ (F.polynomial 0).totalDegree * max a 1`,
* `Q.polynomial 0 ≠ 0`, and
* `aeval (Fin.lastCases f X) (Q.polynomial 0) = 0`. -/
theorem exists_root_circuit_of_nwGenerator_vanishing [Field K] [Infinite K] [DecidableEq L]
    {f : MvPolynomial (Fin m) K} (hmul : ∀ i, f.degreeOf i ≤ 1)
    {S : Fin n → (Fin m ↪ L)} {a : ℕ}
    (hS : ∀ i j, i ≠ j → #(univ.map (S i) ∩ univ.map (S j)) ≤ a)
    {F : Circuit (arithSignature K) n 1} (hF : F.polynomial 0 ≠ 0)
    (hvan : aeval (nwGenerator f S) (F.polynomial 0) = 0) :
    ∃ Q : Circuit (arithSignature K) (m + 1) 1,
      Q.size ≤ F.size + n * (2 ^ a * (a + 3) + 2) ∧
      (Q.polynomial 0).totalDegree ≤ (F.polynomial 0).totalDegree * max a 1 ∧
      Q.polynomial 0 ≠ 0 ∧
      aeval (Fin.lastCases f X : Fin (m + 1) → MvPolynomial (Fin m) K) (Q.polynomial 0) = 0 := by
  classical
  set H : ℕ → MvPolynomial (L ⊕ Fin n) K :=
    fun k => aeval (circuitHybridInput f S k) (F.polynomial 0) with hH
  have H0 : H 0 ≠ 0 := by
    have h0 : circuitHybridInput f S 0 = X ∘ Sum.inr := funext fun j => by
      simp [circuitHybridInput]
    simpa only [hH, h0, ← rename_eq_aeval] using
      (map_ne_zero_iff _ (rename_injective _ Sum.inr_injective)).2 hF
  have Hn : H n = 0 := by
    have hn : circuitHybridInput f S n = fun j => rename Sum.inl (nwGenerator f S j) :=
      funext fun j => by simp [circuitHybridInput]
    simp only [hH, hn, ← comp_aeval_apply, hvan, map_zero]
  obtain ⟨i, hi, hHi, hHi1⟩ : ∃ i < n, H i ≠ 0 ∧ H (i + 1) = 0 := by
    by_contra! h
    exact Nat.rec (motive := fun k => k ≤ n → H k ≠ 0) (fun _ => H0)
      (fun k ih hk => h k (by omega) (ih (by omega))) n le_rfl Hn
  set i' : Fin n := ⟨i, hi⟩ with hi'
  obtain ⟨v, hv⟩ := exists_aeval_sumElim_ne_zero
    ((map_ne_zero_iff _ (rename_injective _ (injective_circuitFreeVar S i'))).2 hHi)
  rw [aeval_rename] at hv
  change aeval (circuitSpecialize S i' v) (H i) ≠ 0 at hv
  set ψ := circuitSpecialize S i' v with hψ
  -- Build a small circuit for each specialized input `aeval ψ (circuitHybridInput f S i j)`.
  have hG_ex (j : Fin n) : ∃ g : Circuit (arithSignature K) (m + 1) 1,
      g.polynomial 0 = aeval ψ (circuitHybridInput f S i j) ∧
      g.size ≤ 2 ^ a * (a + 3) + 2 ∧
      (g.polynomial 0).totalDegree ≤ max a 1 := by
    by_cases hj : (j : ℕ) < i
    · have hji : j ≠ i' := fun h => by simp [h, hi'] at hj
      set A : Finset (Fin m) := univ.filter fun k => ∃ k', S i' k' = S j k with hA
      have hcard : #A ≤ a := by
        rw [← card_map (S j)]
        refine (card_le_card fun l hl => ?_).trans (hS i' j hji.symm)
        obtain ⟨k, hk, rfl⟩ := mem_map.1 hl
        obtain ⟨k', hk'⟩ := (mem_filter.1 hk).2
        exact mem_inter.2 ⟨mem_map.2 ⟨k', mem_univ _, hk'⟩, mem_map_of_mem _ (mem_univ _)⟩
      have hAX : ∀ k ∈ A, ∃ x, ψ (.inl (S j k)) = X x := fun k hk => by
        obtain ⟨k', hk'⟩ := (mem_filter.1 hk).2
        exact ⟨k'.castSucc, by
          simp [← hk', hψ, circuitSpecialize, circuitFreeVar, (S i').injective.extend_apply]⟩
      have hAC : ∀ k ∉ A, ∃ c, ψ (.inl (S j k)) = MvPolynomial.C c := fun k hk =>
        ⟨v (.inl (S j k)), by
          simp [hψ, circuitSpecialize, circuitFreeVar,
            Function.extend_apply' _ _ _ (by simpa [hA] using hk)]⟩
      have h1 := (card_support_aeval_le_of_degreeOf_le_one hmul hAX hAC).trans
        (Nat.pow_le_pow_right two_pos hcard)
      have h2 := (totalDegree_aeval_le_card_of_degreeOf_le_one hmul hAX hAC).trans hcard
      have hg : aeval ψ (circuitHybridInput f S i j) = aeval (fun k => ψ (.inl (S j k))) f := by
        simp [circuitHybridInput, hj, aeval_rename, Function.comp_def]
      obtain ⟨g, hgP, hgS⟩ := exists_circuit_ofSparse (aeval ψ (circuitHybridInput f S i j))
      refine ⟨g, hgP, ?_, ?_⟩
      · rw [hg] at hgS
        have := Nat.mul_le_mul h1 (Nat.add_le_add_right h2 3)
        omega
      · rw [hgP, hg]
        exact h2.trans (le_max_left a 1)
    · have hval : aeval ψ (circuitHybridInput f S i j) = ψ (.inr j) := by
        simp [circuitHybridInput, hj]
      by_cases hji : j = i'
      · refine ⟨Circuit.wiring _ (fun _ => Fin.last m), ?_, by simp, ?_⟩
        · rw [hval]; simp [hji, hψ, circuitSpecialize, circuitFreeVar, Circuit.polynomial]
        · exact (totalDegree_X_le _).trans (le_max_right a 1)
      · refine ⟨Circuit.oneGate (.const (v (.inr j))) Fin.elim0, ?_, by simp, ?_⟩
        · rw [hval]; simp [hψ, circuitSpecialize, circuitFreeVar, hji, Circuit.polynomial]
        · simp [Circuit.polynomial]
  choose G hGP hGS hGDeg using hG_ex
  let Q : Circuit (arithSignature K) (m + 1) 1 := F.comp (Circuit.pi G)
  have hQpoly : Q.polynomial 0 = aeval ψ (H i) := by
    rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
    have hpi : (Circuit.pi G).eval (arithInterpretationWith K C) X =
        fun j => aeval ψ (circuitHybridInput f S i j) := by
      funext j
      rw [Circuit.eval_pi]
      exact hGP j
    rw [hpi, hH, comp_aeval_apply]
  refine ⟨Q, ?_, ?_, hQpoly ▸ hv, ?_⟩
  · rw [Circuit.size_comp, Circuit.size_pi]
    have hsum : ∑ j : Fin n, (G j).size ≤ n * (2 ^ a * (a + 3) + 2) := by
      calc ∑ j : Fin n, (G j).size ≤ ∑ _j : Fin n, (2 ^ a * (a + 3) + 2) :=
            sum_le_sum fun j _ => hGS j
        _ = n * (2 ^ a * (a + 3) + 2) := by simp
    omega
  · rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
    refine totalDegree_aeval_le_mul (fun j => ?_) (F.polynomial 0)
    rw [Circuit.eval_pi]
    exact hGDeg j
  · have key (j : Fin n) :
        aeval (Fin.lastCases f X : Fin (m + 1) → MvPolynomial (Fin m) K)
          (aeval ψ (circuitHybridInput f S i j)) =
        aeval (Fin.lastCases f X : Fin (m + 1) → MvPolynomial (Fin m) K)
          (aeval ψ (circuitHybridInput f S (i + 1) j)) := by
      by_cases hji : j = i'
      · rw [hji]
        simp [circuitHybridInput, hi', aeval_rename, Function.comp_def, hψ, circuitSpecialize,
          circuitFreeVar, (S ⟨i, hi⟩).injective.extend_apply, comp_aeval_apply, aeval_X_left_apply]
      · have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
        simp only [circuitHybridInput, show (j : ℕ) < i ↔ (j : ℕ) < i + 1 by omega]
    have hsub (k : ℕ) :
        aeval (Fin.lastCases f X : Fin (m + 1) → MvPolynomial (Fin m) K) (aeval ψ (H k)) =
          aeval (fun j => aeval (Fin.lastCases f X : Fin (m + 1) → MvPolynomial (Fin m) K)
            (aeval ψ (circuitHybridInput f S k j))) (F.polynomial 0) := by
      simp only [hH, comp_aeval_apply]
    rw [hQpoly, hsub, funext key, ← hsub, hHi1, map_zero, map_zero]

/-- If the composition of a polynomial of degree at most `d_C` with `nwGenerator f S` is nonzero,
where `f.totalDegree ≤ d`, then `generatorHittingSet f S (d_C * d)` hits it. -/
theorem exists_mem_generatorHittingSet_eval_ne_zero_of_totalDegree [Field K] [CharZero K]
    [Fintype L] [DecidableEq L] {f : MvPolynomial (Fin m) K} {S : Fin n → (Fin m ↪ L)}
    {d d_C : ℕ} (hd : f.totalDegree ≤ d) {p : MvPolynomial (Fin n) K} (hp : p.totalDegree ≤ d_C)
    (hne : aeval (nwGenerator f S) p ≠ 0) :
    ∃ x ∈ generatorHittingSet f S (d_C * d), eval x p ≠ 0 := by
  classical
  set grid := (range (d_C * d + 1)).image (Nat.cast : ℕ → K)
  have hdeg : (aeval (nwGenerator f S) p).totalDegree < #grid := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range, Nat.lt_succ_iff]
    exact (totalDegree_aeval_le_mul (fun i => (totalDegree_rename_le _ f).trans hd) p).trans
      (Nat.mul_le_mul_right d hp)
  obtain ⟨z, hz, hz_ne⟩ := exists_eval_ne_zero_of_totalDegree_lt_card hne hdeg
  refine ⟨fun i => eval z (nwGenerator f S i),
    mem_image.2 ⟨z, Fintype.mem_piFinset.2 hz, rfl⟩, ?_⟩
  rwa [← aeval_eq_eval, comp_aeval_apply] at hz_ne

/-- **Algebraic Nisan–Wigderson hardness-to-hitting-sets for general arithmetic circuits.**
Over a field `K` of characteristic zero, if a multilinear polynomial `f` in `m` variables of total
degree at most `d` has no arithmetic circuit of size at most
`circuitRootCost (s + n * (2 ^ a * (a + 3) + 2)) (d_C * max a 1) m d`, and `S` is a family of `n`
blocks in `L` with pairwise intersections at most `a`, then `generatorHittingSet f S (d_C * d)`
(of size at most `(d_C * d + 1) ^ |L|`) is a hitting set for all `n`-variate arithmetic circuits of
size at most `s` and total degree at most `d_C`. -/
theorem isHittingSet_generatorHittingSet_of_circuitHard [Field K] [CharZero K]
    [Fintype L] [DecidableEq L]
    {f : MvPolynomial (Fin m) K} (hmul : ∀ i, f.degreeOf i ≤ 1)
    {d : ℕ} (hd : f.totalDegree ≤ d)
    {S : Fin n → (Fin m ↪ L)} {a : ℕ}
    (hS : ∀ i j, i ≠ j → #(univ.map (S i) ∩ univ.map (S j)) ≤ a)
    {s d_C : ℕ}
    (hhard : ∀ G : Circuit (arithSignature K) m 1, G.polynomial 0 = f →
      circuitRootCost (s + n * (2 ^ a * (a + 3) + 2)) (d_C * max a 1) m d < G.size) :
    IsHittingSet (generatorHittingSet f S (d_C * d)) (boundedCircuitPolys K n s d_C) := by
  classical
  rintro _ ⟨C, rfl, hCsize, hCdeg⟩ hC0
  by_cases hvan : aeval (nwGenerator f S) (C.polynomial 0) = 0
  · have : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
    obtain ⟨Q, hQsize, hQdeg, hQ0, hQroot⟩ :=
      exists_root_circuit_of_nwGenerator_vanishing hmul hS hC0 hvan
    obtain ⟨G, hGf, hGsize⟩ := exists_circuit_of_root hQ0
      (hQdeg.trans (Nat.mul_le_mul_right _ hCdeg)) hQroot
    have hle : G.size ≤ circuitRootCost (s + n * (2 ^ a * (a + 3) + 2)) (d_C * max a 1) m d :=
      hGsize.trans (circuitRootCost_mono (hQsize.trans (Nat.add_le_add_right hCsize _))
        le_rfl le_rfl hd)
    exact absurd hle (hhard G hGf).not_ge
  · exact exists_mem_generatorHittingSet_eval_ne_zero_of_totalDegree hd hCdeg hvan

/-- **Algebraic-vs-hitting-set dichotomy for Boolean truth tables.**
For any combinatorial design `D : Design ℓ m a n` and any Boolean truth table
`T : (Fin m → Bool) → Bool`, either the algebraic Nisan–Wigderson hitting set
`generatorHittingSet (boolMultilinearExt K T) D.blockEmb (d_C * m)` hits every nonzero circuit in
`boundedCircuitPolys K n s d_C` (with at most `(d_C * m + 1) ^ ℓ` points), or
`boolMultilinearExt K T` is computed by an arithmetic circuit of size at most
`circuitRootCost (s + n * (2 ^ a * (a + 3) + 2)) (d_C * max a 1) m m`. -/
theorem algNW_dichotomy_of_boolTable [Field K] [CharZero K] {ℓ m a n s d_C : ℕ}
    (D : Design ℓ m a n) (T : (Fin m → Bool) → Bool) :
    (IsHittingSet (generatorHittingSet (boolMultilinearExt K T) D.blockEmb (d_C * m))
        (boundedCircuitPolys K n s d_C) ∧
      #(generatorHittingSet (boolMultilinearExt K T) D.blockEmb (d_C * m)) ≤ (d_C * m + 1) ^ ℓ) ∨
    ∃ G : Circuit (arithSignature K) m 1,
      G.polynomial 0 = boolMultilinearExt K T ∧
      G.size ≤ circuitRootCost (s + n * (2 ^ a * (a + 3) + 2)) (d_C * max a 1) m m := by
  by_cases h : ∃ G : Circuit (arithSignature K) m 1,
      G.polynomial 0 = boolMultilinearExt K T ∧
      G.size ≤ circuitRootCost (s + n * (2 ^ a * (a + 3) + 2)) (d_C * max a 1) m m
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨isHittingSet_generatorHittingSet_of_circuitHard
      (degreeOf_boolMultilinearExt_le_one K T) (totalDegree_boolMultilinearExt_le K T)
      (fun _ _ hij => D.card_map_blockEmb_inter_le hij) h, ?_⟩
    simpa [Fintype.card_fin] using
      card_generatorHittingSet_le (boolMultilinearExt K T) D.blockEmb (d_C * m)

/-- **Unconditional design-instantiated algebraic Nisan–Wigderson dichotomy.**
Using the explicit `(4 * m ^ 2, m, k - 1)`-design with `(m + 1) ^ k` blocks
(`Design.nonempty_four_mul_sq`), for every Boolean truth table `T` on `m` bits and every circuit
size `s` and degree `d_C`, there exists a design `D` such that either the algebraic NW generator on
`T` produces a hitting set of size at most `(d_C * m + 1) ^ (4 * m ^ 2)` for all `((m + 1) ^ k)`-
variate circuits of size `≤ s` and degree `≤ d_C`, or `boolMultilinearExt K T` has an arithmetic
circuit of size at most
`circuitRootCost (s + (m + 1) ^ k * (2 ^ (k - 1) * (k - 1 + 3) + 2)) (d_C * max (k - 1) 1) m m`. -/
theorem exists_algNW_hittingSet_or_smallCircuit [Field K] [CharZero K] (m k s d_C : ℕ)
    (T : (Fin m → Bool) → Bool) :
    ∃ D : Design (4 * m ^ 2) m (k - 1) ((m + 1) ^ k),
      (IsHittingSet (generatorHittingSet (boolMultilinearExt K T) D.blockEmb (d_C * m))
          (boundedCircuitPolys K ((m + 1) ^ k) s d_C) ∧
        #(generatorHittingSet (boolMultilinearExt K T) D.blockEmb (d_C * m)) ≤
          (d_C * m + 1) ^ (4 * m ^ 2)) ∨
      ∃ G : Circuit (arithSignature K) m 1,
        G.polynomial 0 = boolMultilinearExt K T ∧
        G.size ≤ circuitRootCost
          (s + (m + 1) ^ k * (2 ^ (k - 1) * (k - 1 + 3) + 2)) (d_C * max (k - 1) 1) m m := by
  obtain ⟨D⟩ := Design.nonempty_four_mul_sq m k
  exact ⟨D, algNW_dichotomy_of_boolTable D T⟩

end GeneralCircuitNW

end AlgebraicNisanWigderson

/-! ### Bit-Blasting Bridge: Modular Arithmetic Circuits to Boolean Circuits -/

section BitBlastBridge

open Cslib.BitString

/-- **Bit-blasting modular arithmetic circuits to Boolean De Morgan circuits.**
If a Boolean function `T : (Fin m → Bool) → Bool` agrees on `{0, 1} ^ m` with an arithmetic circuit
`C` over a commutative ring `F` admitting an injective `w`-bit encoding whose least significant bit
recovers `bitVal F b`, then `T` has Boolean De Morgan circuit complexity at most
`C.size * bitBlastCost w + 1`. -/
theorem boolean_complexity_le_of_arithCircuit {F : Type*} [CommRing F] {m w : ℕ}
    (enc : F → BitString w) (decode : BitString w → F) (hdecode : Function.LeftInverse decode enc)
    (bit0 : Fin w)
    (h0 : enc 0 bit0 = false) (h1 : enc 1 bit0 = true)
    (hother : ∀ j : Fin w, j ≠ bit0 → enc 0 j = false ∧ enc 1 j = false)
    (T : (Fin m → Bool) → Bool) (C : Circuit (arithSignature F) m 1)
    (hC : ∀ x : Fin m → Bool,
      C.eval (arithInterpretation F) (fun i => bitVal F (x i)) 0 = bitVal F (T x)) :
    complexity Boolean.interpretation (single T) ≤ C.size * bitBlastCost w + 1 := by
  let s0 : Set (BooleanFunction m) := inputs m ∪ {fun _ => false}
  have hfalse : Synthesis Boolean.interpretation (inputs m) {fun _ : Fin m → Bool => false} 1 :=
    Synthesis.const false
  have hφ : ∀ (i : Fin m) (j : Fin w),
      bitsOf enc (fun x : Fin m → Bool => bitVal F (x i)) j ∈ s0 := by
    intro i j
    by_cases hj : j = bit0
    · subst hj
      refine Or.inl ⟨i, funext fun x => ?_⟩
      simp only [bitsOf]
      cases x i
      · simp [h0]
      · simp [h1]
    · refine Or.inr (Set.mem_singleton_iff.mpr (funext fun x => ?_))
      simp only [bitsOf]
      cases x i
      · simp [(hother j hj).1]
      · simp [(hother j hj).2]
  have hbb := Synthesis.bitBlast_arithmetic enc decode hdecode C
    (fun i x => bitVal F (x i)) hφ
  have hTmem : T ∈ Set.range (fun oj : Fin 1 × Fin w =>
      bitsOf enc (fun x => C.eval (arithInterpretation F)
        (fun i => bitVal F (x i)) oj.1) oj.2) := by
    refine ⟨(0, bit0), funext fun x => ?_⟩
    simp only [bitsOf, hC x]
    cases T x
    · simp [h0]
    · simp [h1]
  have hfull : Synthesis Boolean.interpretation (inputs m) {T}
      (C.size * bitBlastCost w + 1) :=
    (hfalse.trans hbb).mono Set.Subset.rfl (Set.singleton_subset_iff.mpr hTmem) (by omega)
  exact hfull.complexity_le

end BitBlastBridge

/-! ## : Downward Self-Reducibility and PIT Certification of the Permanent -/

section PermanentCertification

/-- Row-indexed form of the matrix permanent: `M.permanent = ∑ σ, ∏ i, M i (σ i)`. -/
private theorem matrix_permanent_eq_sum_row {K : Type*} [CommSemiring K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) :
    M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M i (σ i) := by
  rw [Matrix.permanent, ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  refine sum_congr rfl fun σ _ => ?_
  rw [← Equiv.prod_comp σ]
  simp

/-- **Row-zero Laplace expansion of the matrix permanent** over any commutative semiring `K`. -/
theorem matrix_permanent_succ_row_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    M.permanent = ∑ j : Fin (n + 1),
      M 0 j * (M.submatrix Fin.succ j.succAbove).permanent := by
  rw [matrix_permanent_eq_sum_row]
  let liftFun (p : Fin (n + 1) × Equiv.Perm (Fin n)) : Fin (n + 1) → Fin (n + 1) :=
    Fin.cases p.1 fun i => p.1.succAbove (p.2 i)
  have hliftFun_inj (p : Fin (n + 1) × Equiv.Perm (Fin n)) : Function.Injective (liftFun p) := by
    intro a b h
    refine Fin.cases (fun b => ?_) (fun i b => ?_) a b h
    · refine Fin.cases (fun _ => rfl) (fun k h => ?_) b
      exact absurd h.symm (Fin.succAbove_ne p.1 (p.2 k))
    · refine Fin.cases (fun h => ?_) (fun k h => ?_) b
      · exact absurd h (Fin.succAbove_ne p.1 (p.2 i))
      · exact congrArg Fin.succ (p.2.injective (Fin.succAbove_right_injective h))
  let lift (p : Fin (n + 1) × Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
    Equiv.ofBijective (liftFun p) (Finite.injective_iff_bijective.mp (hliftFun_inj p))
  have hlift_inj : Function.Injective lift := by
    rintro ⟨j₁, τ₁⟩ ⟨j₂, τ₂⟩ h
    have h0 : j₁ = j₂ := by
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ 0) h
      simpa [lift, liftFun] using this
    subst h0
    congr 1
    ext i
    have hi := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ i.succ) h
    simp only [lift, liftFun, Equiv.ofBijective_apply, Fin.cases_succ] at hi
    exact congrArg Fin.val (Fin.succAbove_right_injective hi)
  have hlift_bij : Function.Bijective lift :=
    (Fintype.bijective_iff_injective_and_card lift).mpr
      ⟨hlift_inj, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
  rw [← Equiv.sum_comp (Equiv.ofBijective lift hlift_bij), Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  rw [matrix_permanent_eq_sum_row, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_succ]
  simp [lift, liftFun, Matrix.submatrix]

/-- The generic `0 × 0` permanent is `1`. -/
@[simp] theorem permanent_genericMatrix_zero (K : Type*) [CommSemiring K] :
    (genericMatrix K 0).permanent = 1 := by
  simp [Matrix.permanent]

/-- Wire-renaming map embedding the `n × n` variables of the `(0, j)`-minor into the
`(n + 1) × (n + 1)` variables of `genericMatrix K (n + 1)`. -/
def minorMap (n : ℕ) (j : Fin (n + 1)) : Fin (n * n) → Fin ((n + 1) * (n + 1)) :=
  fun idx =>
    let rc := finProdFinEquiv.symm idx
    finProdFinEquiv (rc.1.succ, j.succAbove rc.2)

/-- Renaming the generic `n × n` permanent along `minorMap n j` yields the permanent of the
`(0, j)`-minor of `genericMatrix K (n + 1)`. -/
theorem rename_minorMap_permanent (K : Type*) [CommSemiring K] (n : ℕ) (j : Fin (n + 1)) :
    rename (minorMap n j) (genericMatrix K n).permanent =
      ((genericMatrix K (n + 1)).submatrix Fin.succ j.succAbove).permanent := by
  simp only [Matrix.permanent, map_sum, map_prod, genericMatrix, Matrix.submatrix_apply,
    Matrix.of_apply, rename_X, minorMap, Equiv.symm_apply_apply]

/-- Concrete 2-gate circuit subtracting `1` from its single input: `x ↦ x + (-1)`. -/
def subOneGateCircuit (K : Type*) [CommRing K] : Circuit (arithSignature K) 1 1 :=
  ⟨((Program.empty (σ := arithSignature K)).gate ⟨ArithOp.const (-1 : K), Fin.elim0⟩).gate
      ⟨ArithOp.add, ![Wire.input 0, Wire.gate 0]⟩,
    fun _ => Wire.gate 1⟩

@[simp] theorem subOneGateCircuit_polynomial (K : Type*) [CommRing K] :
    (subOneGateCircuit K).polynomial 0 = X 0 - 1 := by
  rw [sub_eq_add_neg]
  simp only [subOneGateCircuit, Circuit.polynomial, Circuit.eval, Program.trace, Program.eval,
    Line.eval, Function.comp_apply, Wire.elim, arithInterpretationWith_add,
    arithInterpretationWith_const, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one]
  rfl

@[simp] theorem subOneGateCircuit_size (K : Type*) [CommRing K] :
    (subOneGateCircuit K).size = 2 := rfl

/-- The constant-one residual circuit `C₀ - 1`, certifying the `0 × 0` permanent base case. -/
def constOneResidualCircuit {K : Type*} [CommRing K] (C₀ : Circuit (arithSignature K) 0 1) :
    Circuit (arithSignature K) 0 1 :=
  (subOneGateCircuit K).comp C₀

/-- `constOneResidualCircuit C₀` computes `C₀.polynomial 0 - 1`. -/
@[simp] theorem constOneResidualCircuit_polynomial {K : Type*} [CommRing K]
    (C₀ : Circuit (arithSignature K) 0 1) :
    (constOneResidualCircuit C₀).polynomial 0 = C₀.polynomial 0 - 1 := by
  rw [constOneResidualCircuit, Circuit.polynomial, Circuit.eval_comp,
    ← Circuit.aeval_polynomial_mvPolynomial, subOneGateCircuit_polynomial, map_sub, aeval_X,
    map_one]
  rfl

/-- `constOneResidualCircuit C₀` adds `2` gates. -/
@[simp] theorem constOneResidualCircuit_size {K : Type*} [CommRing K]
    (C₀ : Circuit (arithSignature K) 0 1) :
    (constOneResidualCircuit C₀).size = C₀.size + 2 := rfl

/-- `constOneResidualCircuit C₀` preserves syntactic degree. -/
@[simp] theorem constOneResidualCircuit_syntacticDegree {K : Type*} [CommRing K]
    (C₀ : Circuit (arithSignature K) 0 1) :
    (constOneResidualCircuit C₀).syntacticDegree = C₀.syntacticDegree := by
  rw [constOneResidualCircuit, Circuit.syntacticDegree_single, Circuit.syntacticDegree_single,
    Circuit.outputSyntacticDegree, Circuit.outputSyntacticDegree, Circuit.eval_comp]
  have hstep (d : Fin 1 → ℕ) :
      (subOneGateCircuit K).eval (arithDegInterpretation K) d 0 = d 0 := by
    change Fin.lastCases (max (d 0) (Fin.lastCases 0 Fin.elim0 (0 : Fin 1)))
      (fun i => Fin.lastCases 0 Fin.elim0 i) (1 : Fin 2) = d 0
    exact Nat.max_zero (d 0)
  exact hstep _

/-- **Laplace-residual circuit** for downward self-reducibility of the permanent: given candidate
circuits `C_prev` (on `n * n` inputs) and `C_curr` (on `(n + 1) * (n + 1)` inputs), constructs an
explicit arithmetic circuit computing
`C_curr(X) - ∑ j, X_{0, j} * C_prev(X^{(0, j)})`
with gate count at most `C_curr.size + (n + 1) * C_prev.size + 3 * (n + 1) + 5`. -/
theorem exists_laplaceResidualCircuit {K : Type*} [CommRing K] {n : ℕ}
    (C_prev : Circuit (arithSignature K) (n * n) 1)
    (C_curr : Circuit (arithSignature K) ((n + 1) * (n + 1)) 1) :
    ∃ R : Circuit (arithSignature K) ((n + 1) * (n + 1)) 1,
      R.polynomial 0 = C_curr.polynomial 0 -
        ∑ j : Fin (n + 1),
          X (finProdFinEquiv ((0 : Fin (n + 1)), j)) *
            rename (minorMap n j) (C_prev.polynomial 0) ∧
      R.size ≤ C_curr.size + (n + 1) * C_prev.size + 4 * (n + 1) + 5 := by
  let N := (n + 1) * (n + 1)
  let mulGate : Circuit (arithSignature K) 2 1 :=
    Circuit.oneGate .mul ![0, 1]
  let termCirc (j : Fin (n + 1)) : Circuit (arithSignature K) N 1 :=
    mulGate.comp (Circuit.pi
      ![Circuit.wiring _ (fun _ => finProdFinEquiv ((0 : Fin (n + 1)), j)),
        C_prev.mapInputs (minorMap n j)])
  have htermP (j : Fin (n + 1)) :
      (termCirc j).polynomial 0 =
        X (finProdFinEquiv ((0 : Fin (n + 1)), j)) *
          rename (minorMap n j) (C_prev.polynomial 0) := by
    rw [Circuit.polynomial, Circuit.eval_comp, ← Circuit.aeval_polynomial_mvPolynomial]
    have hmul : mulGate.polynomial 0 = X 0 * X 1 := by
      simp [mulGate, Circuit.polynomial]
    rw [hmul, map_mul, aeval_X, aeval_X]
    simp only [Circuit.eval_pi, Matrix.cons_val_zero, Matrix.cons_val_one, Circuit.eval_wiring,
      Function.comp_apply]
    change X (finProdFinEquiv (0, j)) * (C_prev.mapInputs (minorMap n j)).polynomial 0 = _
    rw [Circuit.polynomial_mapInputs]
  have htermS (j : Fin (n + 1)) : (termCirc j).size = C_prev.size + 1 := by
    simp [termCirc, mulGate, Circuit.size_comp, Circuit.size_pi, Fin.sum_univ_two]
  -- Sum the terms with weight `-1` and add `C_curr` with weight `1`.
  let allCircs : Option (Fin (n + 1)) → Circuit (arithSignature K) N 1
    | none => C_curr
    | some j => termCirc j
  let allWeights : Option (Fin (n + 1)) → K
    | none => 1
    | some _ => -1
  obtain ⟨R, hRP, hRS⟩ := exists_linearComb_circuit (univ : Finset (Option (Fin (n + 1))))
    allWeights allCircs
  refine ⟨R, ?_, ?_⟩
  · rw [hRP, Fintype.sum_option]
    simp only [allWeights, allCircs, map_one, one_mul, map_neg, neg_mul, sum_neg_distrib,
      ← sub_eq_add_neg]
    congr 1
    exact sum_congr rfl fun j _ => htermP j
  · rw [Fintype.sum_option, card_univ, Fintype.card_option, Fintype.card_fin] at hRS
    simp only [allCircs, htermS, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_add, Nat.mul_one] at hRS
    omega

/-- **Exact PIT certification of permanent circuits via downward self-reducibility.**
A sequence of arithmetic circuits `C k` (for `k ≤ n`) computes the generic permanent polynomials
`(genericMatrix K k).permanent` for every `k ≤ n` if and only if:
1. the base residual `constOneResidualCircuit (C 0)` computes the zero polynomial, and
2. for every `k < n`, the Laplace residual between `C k` and `C (k + 1)` computes the zero
   polynomial. -/
theorem permanent_certified_by_PIT_iff {K : Type*} [CommRing K] {n : ℕ}
    (C : ∀ k, Circuit (arithSignature K) (k * k) 1)
    (R : ∀ k, Circuit (arithSignature K) ((k + 1) * (k + 1)) 1)
    (hR : ∀ k, (R k).polynomial 0 = (C (k + 1)).polynomial 0 -
      ∑ j : Fin (k + 1),
        X (finProdFinEquiv ((0 : Fin (k + 1)), j)) *
          rename (minorMap k j) ((C k).polynomial 0)) :
    (∀ k ≤ n, (C k).polynomial 0 = (genericMatrix K k).permanent) ↔
      ((constOneResidualCircuit (C 0)).polynomial 0 = 0 ∧
        ∀ k < n, (R k).polynomial 0 = 0) := by
  constructor
  · intro hperm
    refine ⟨?_, fun k hk => ?_⟩
    · rw [constOneResidualCircuit_polynomial, hperm 0 (Nat.zero_le n), permanent_genericMatrix_zero,
        sub_self]
    · rw [hR k, hperm (k + 1) hk, hperm k (Nat.le_of_lt hk), matrix_permanent_succ_row_zero,
        sub_eq_zero]
      refine sum_congr rfl fun j _ => ?_
      rw [rename_minorMap_permanent]
      rfl
  · rintro ⟨h0, hstep⟩ k hk
    induction k with
    | zero =>
      rw [constOneResidualCircuit_polynomial, sub_eq_zero] at h0
      rw [h0, permanent_genericMatrix_zero]
    | succ k ih =>
      have hklt : k < n := hk
      have hres := hstep k hklt
      rw [hR k, sub_eq_zero] at hres
      rw [hres, matrix_permanent_succ_row_zero]
      refine sum_congr rfl fun j _ => ?_
      rw [ih (Nat.le_of_lt hklt), rename_minorMap_permanent]
      rfl

/-- **White-box PIT certification over `ℚ`**: a sequence of rational arithmetic circuits computes
the generic permanents up to dimension `n` if and only if all `n + 1` residual circuits are
rejected by `WhiteBoxPIT`. -/
theorem permanent_certified_by_whiteBoxPIT_iff {n : ℕ}
    (C : ∀ k, Circuit (arithSignature ℚ) (k * k) 1)
    (R : ∀ k, Circuit (arithSignature ℚ) ((k + 1) * (k + 1)) 1)
    (hR : ∀ k, (R k).polynomial 0 = (C (k + 1)).polynomial 0 -
      ∑ j : Fin (k + 1),
        X (finProdFinEquiv ((0 : Fin (k + 1)), j)) *
          rename (minorMap k j) ((C k).polynomial 0)) :
    (∀ k ≤ n, (C k).polynomial 0 = (genericMatrix ℚ k).permanent) ↔
      (⟨0, constOneResidualCircuit (C 0)⟩ ∉ WhiteBoxPIT ∧
        ∀ k < n, ⟨(k + 1) * (k + 1), R k⟩ ∉ WhiteBoxPIT) := by
  simp only [WhiteBoxPIT, Set.mem_ofPred_eq, not_not]
  exact permanent_certified_by_PIT_iff C R hR

/-- **Exact permanent evaluation from a certified circuit.** If
`C.polynomial 0 = (genericMatrix K n).permanent`, then evaluating `C` at the entries of any `n × n`
matrix `A` over `K` returns `A.permanent`. -/
theorem eval_eq_permanent_of_certified {K : Type*} [CommSemiring K] {n : ℕ}
    {C : Circuit (arithSignature K) (n * n) 1}
    (hC : C.polynomial 0 = (genericMatrix K n).permanent)
    (A : Matrix (Fin n) (Fin n) K) :
    C.eval (arithInterpretation K)
      (fun idx => A (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2) 0 =
      A.permanent := by
  rw [← Circuit.eval_polynomial, hC, Matrix.permanent, Matrix.permanent, map_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [map_prod]
  refine prod_congr rfl fun i _ => ?_
  simp only [genericMatrix, Matrix.of_apply, eval_X, Equiv.symm_apply_apply]

/-- **Exact 0/1 permanent evaluation from a certified rational circuit.** Evaluating a certified
rational permanent circuit on the 0/1 entries of a Boolean table `A` computes
`ZeroOnePermanent A`. -/
theorem eval_eq_zeroOnePermanent_of_certified {n : ℕ} {C : Circuit (arithSignature ℚ) (n * n) 1}
    (hC : C.polynomial 0 = (genericMatrix ℚ n).permanent)
    (A : List (List Bool)) (hA : A.length = n) :
    C.eval (arithInterpretation ℚ)
      (fun idx =>
        ((A[Fin.cast hA.symm (finProdFinEquiv.symm idx).1].getD
          (finProdFinEquiv.symm idx).2 false).toNat : ℚ)) 0 =
      (Complexity.ZeroOnePermanent A : ℚ) := by
  subst hA
  let M : Matrix (Fin A.length) (Fin A.length) ℚ :=
    Matrix.of fun i j => ((A[i].getD j false).toNat : ℚ)
  have h1 := eval_eq_permanent_of_certified hC M
  refine h1.trans ?_
  simp only [Complexity.ZeroOnePermanent, Complexity.boolTableMatrix, M, Matrix.permanent,
    Nat.cast_sum, Nat.cast_prod, Matrix.of_apply]

/-- **Modular permanent recovery.** Since the 0/1 permanent of an `n × n` Boolean table is at most
`n!`, knowing its value modulo any integer `Q > n!` determines `ZeroOnePermanent A` uniquely. -/
theorem zeroOnePermanent_le_factorial (A : List (List Bool)) :
    Complexity.ZeroOnePermanent A ≤ A.length.factorial := by
  rw [Complexity.zeroOnePermanent_eq_card]
  calc (univ.filter fun σ : Equiv.Perm (Fin A.length) =>
          ∀ i : Fin A.length, A[i].getD (σ i) false = true).card
      ≤ (univ : Finset (Equiv.Perm (Fin A.length))).card := card_le_card (filter_subset _ _)
    _ = A.length.factorial := by simp [Fintype.card_perm]

/-- Knowing `ZeroOnePermanent A` modulo `Q > A.length.factorial` recovers it uniquely. -/
theorem zeroOnePermanent_eq_of_mod_eq (A : List (List Bool)) {Q v : ℕ}
    (hQ : A.length.factorial < Q) (hv : v < Q)
    (hmod : v % Q = Complexity.ZeroOnePermanent A % Q) :
    v = Complexity.ZeroOnePermanent A := by
  have hlt : Complexity.ZeroOnePermanent A < Q :=
    lt_of_le_of_lt (zeroOnePermanent_le_factorial A) hQ
  rwa [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hlt] at hmod

end PermanentCertification

/-! ## : Hardness-vs-Randomness Dichotomies -/

section Dichotomy

open Turing.MultiTapeTM

/-- **Unconditional inclusion `MA ⊆ P^#P`**, composing `MA ⊆ AM ⊆ PH` with `PH ⊆ P^#P`. -/
theorem MA_subset_PWithSharpPOracle {α : Type} {enc : α ↪ List Bool} :
    Complexity.MA enc ⊆ Complexity.PWithSharpPOracle enc :=
  Complexity.MA_subset_AM.trans
    (Complexity.AM_subset_PH.trans Complexity.PH_subset_PWithSharpPOracle)

/-- **Every `#P` function reduces via a polynomial-time oracle computation to the 0/1 permanent**
(re-exported link to Valiant's theorem for the permanent dichotomy chain). -/
theorem sharpP_reduces_to_zeroOnePermanent {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} (hf : f ∈ Complexity.SharpP enc) :
    Complexity.ComputableInPolyTimeWithOracle
      (Complexity.bitGraph Complexity.encBoolTable Complexity.ZeroOnePermanent) f enc encNat :=
  Complexity.zeroOnePermanent_computableInPolyTimeWithOracle hf

/-- **Native guess-and-certify `NTIME` simulation using a deterministic white-box PIT algorithm.**
Given a certificate length `ℓ`, a query compiler producing a single PIT-checkable residual circuit
`query (x, w)` (or a combined residual), a Boolean evaluation predicate `evalPred (x, w)`, and a
deterministic white-box PIT decider `pit` in `ComputableInO`, the language of inputs possessing a
certificate `w` of length `ℓ x` that passes the PIT check (`query (x, w) ∉ WhiteBoxPIT`) and
satisfies `evalPred (x, w) = true` lies in `NTIME enc t` whenever the sum of input, length,
compilation, PIT, and evaluation costs is `O(t (enc x).length)`. -/
theorem pitCertifiedLanguage_mem_NTIME {α : Type} {enc : α ↪ List Bool}
    {ℓ : α → ℕ} {t : ℕ → ℕ}
    {query : α × List Bool → Σ n, Circuit (arithSignature ℚ) n 1}
    {evalPred : α × List Bool → Bool}
    {pit : (Σ n, Circuit (arithSignature ℚ) n 1) → Bool}
    {Tℓ Sℓ : α → ℕ} {TQ SQ TE SE : α × List Bool → ℕ}
    {TP SP : (Σ n, Circuit (arithSignature ℚ) n 1) → ℕ} {C : ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ)
    (hQ : ComputableInO query (encPair enc encBits) (encRatArithCircuit 1) TQ SQ)
    (hE : ComputableInO evalPred (encPair enc encBits) encBool TE SE)
    (hPIT : ComputableInO pit (encRatArithCircuit 1) encBool TP SP)
    (hspec : ∀ c, pit c = true ↔ c ∈ WhiteBoxPIT)
    (ht : ∀ x w, w.length = ℓ x →
      (enc x).length + Tℓ x +
        ((TQ (x, w) + TP (query (x, w))) + TE (x, w) + 1) ≤ C * t (enc x).length + C) :
    {x | ∃ w : List Bool, w.length = ℓ x ∧
      query (x, w) ∉ WhiteBoxPIT ∧ evalPred (x, w) = true} ∈ Complexity.NTIME enc t := by
  have hcert : ComputableInO (fun p : α × List Bool => !pit (query p) && evalPred p)
      (encPair enc encBits) encBool
      (fun p => (TQ p + TP (query p)) + TE p + 1)
      (fun p => (SQ p + SP (query p)) + SE p + 1) := by
    have hcomp : ComputableInO (fun p : α × List Bool => pit (query p))
        (encPair enc encBits) encBool
        (fun p => TQ p + TP (query p))
        (fun p => SQ p + SP (query p)) := hPIT.comp hQ
    obtain ⟨TA, SA, -, -, hAnd0⟩ :=
      (ComputableInPolyTime.of_finite (encIn := encPair encBool encBool) (encOut := encBool)
        (fun b : Bool × Bool => !b.1 && b.2)).exists_computableInO
    let MA := max (max (TA (false, false)) (TA (false, true)))
      (max (TA (true, false)) (TA (true, true)))
    let MS := max (max (SA (false, false)) (SA (false, true)))
      (max (SA (true, false)) (SA (true, true)))
    have hTA (b : Bool × Bool) : TA b ≤ MA := by
      rcases b with ⟨_ | _, _ | _⟩ <;> simp [MA]
    have hSA (b : Bool × Bool) : SA b ≤ MS := by
      rcases b with ⟨_ | _, _ | _⟩ <;> simp [MS]
    have hand := hAnd0.comp (hcomp.prod hE)
    refine hand.mono (MA + MS + 4) (fun p => ?_) (fun p => ?_)
    · have h1 := hTA (pit (query p), evalPred p)
      have h2 : (TQ p + TP (query p) + TE p + 1) + MA ≤
          (MA + MS + 4) * ((TQ p + TP (query p) + TE p + 1) + 1) := by nlinarith
      change TQ p + TP (query p) + TE p + TA (pit (query p), evalPred p) ≤ _
      omega
    · have h1 := hSA (pit (query p), evalPred p)
      have h2 : (SQ p + SP (query p) + SE p + 1) + MS ≤
          (MA + MS + 4) * ((SQ p + SP (query p) + SE p + 1) + 1) := by nlinarith
      change SQ p + SP (query p) + SE p + SA (pit (query p), evalPred p) ≤ _
      omega
  have hset : {x | ∃ w : List Bool, w.length = ℓ x ∧
        query (x, w) ∉ WhiteBoxPIT ∧ evalPred (x, w) = true} =
      {x | ∃ w : List Bool, w.length = ℓ x ∧ (!pit (query (x, w)) && evalPred (x, w)) = true} := by
    ext x
    refine exists_congr fun w => and_congr_right fun _ => ?_
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    exact and_congr_left fun _ => (not_congr (hspec _)).symm
  rw [hset]
  exact Complexity.setOf_exists_mem_NTIME hℓ hcert ht

/-- **Unconditional diagonal lower-bound transfer for PIT-certified verifiers.**
If a PIT-certified witness family agrees with the native exponential diagonal language
`expLazyDiagonal k` on all inputs where a small witness exists, and the combined witness
compilation, white-box PIT, and evaluation cost fits `O(2 ^ (k * |x|))`, then some word in
`expLazyDiagonal k` has no PIT-certified witness of length `ℓ x`. -/
theorem exists_unwitnessed_expLazyDiagonal_of_pitVerifier
    {k : ℕ} {ℓ : List Bool → ℕ}
    {query : List Bool × List Bool → Σ n, Circuit (arithSignature ℚ) n 1}
    {evalPred : List Bool × List Bool → Bool}
    {pit : (Σ n, Circuit (arithSignature ℚ) n 1) → Bool}
    {Tℓ Sℓ : List Bool → ℕ} {TQ SQ TE SE : List Bool × List Bool → ℕ}
    {TP SP : (Σ n, Circuit (arithSignature ℚ) n 1) → ℕ} {C : ℕ}
    (hsound : ∀ x w, w.length = ℓ x →
      query (x, w) ∉ WhiteBoxPIT → evalPred (x, w) = true →
      x ∈ Complexity.expLazyDiagonal k)
    (hℓ : ComputableInO ℓ encBits encUnary Tℓ Sℓ)
    (hQ : ComputableInO query (encPair encBits encBits) (encRatArithCircuit 1) TQ SQ)
    (hE : ComputableInO evalPred (encPair encBits encBits) encBool TE SE)
    (hPIT : ComputableInO pit (encRatArithCircuit 1) encBool TP SP)
    (hspec : ∀ c, pit c = true ↔ c ∈ WhiteBoxPIT)
    (ht : ∀ x w, w.length = ℓ x →
      x.length + Tℓ x + ((TQ (x, w) + TP (query (x, w))) + TE (x, w) + 1) ≤
        C * 2 ^ (k * x.length) + C) :
    ∃ x ∈ Complexity.expLazyDiagonal k,
      ∀ w : List Bool, w.length = ℓ x →
        query (x, w) ∉ WhiteBoxPIT → evalPred (x, w) = false := by
  by_contra! hall
  have heq : Complexity.expLazyDiagonal k =
      {x | ∃ w : List Bool, w.length = ℓ x ∧
        query (x, w) ∉ WhiteBoxPIT ∧ evalPred (x, w) = true} := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hq, hev⟩ := hall x hx
      exact ⟨w, hw, hq, Bool.eq_true_of_not_eq_false hev⟩
    · rintro ⟨w, hw, hq, hev⟩
      exact hsound x w hw hq hev
  have hmem : Complexity.expLazyDiagonal k ∈ Complexity.NTIME encBits fun n => 2 ^ (k * n) := by
    rw [heq]
    exact pitCertifiedLanguage_mem_NTIME hℓ hQ hE hPIT hspec
      (by simpa only [encBits_apply] using ht)
  exact Complexity.expLazyDiagonal_notMem_NTIME k hmem

/-- **Conditional hardness-vs-randomness transfer step from subexponential PIT to `NEXP ⊄ P/poly`
or permanent algebraic circuit lower bounds.**
This is the complexity-class composition step combining the unconditionally proved inclusions
`MA ⊆ P^#P` (`MA_subset_PWithSharpPOracle`) and `NEXP ⊄ NSUBEXP` (`NEXP_not_subset_NSUBEXP`) with
two explicit external hypotheses:
1. the collapse `NEXP ⊆ P/poly → NEXP ⊆ MA`, and
2. a PIT-certified simulation placing `P^#P` inside `NSUBEXP` whenever
   `permFamily ℚ ∈ ConstantFreeVP ℚ` and `WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1)`.

Under deterministic subexponential white-box PIT (`WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1)`)
and these two hypotheses, either `NEXP` does not have polynomial-size Boolean circuits
(`NEXP ⊄ P/poly`) or the permanent has no polynomial-size constant-free arithmetic circuits
(`permFamily ℚ ∉ ConstantFreeVP ℚ`). -/
theorem nexp_not_ppoly_or_perm_not_constantFreeVP_of_collapse_of_permSim
    (hPIT : WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1))
    (hCollapse : Complexity.NEXP encBits ⊆ Boolean.PPolyOn encBits →
      Complexity.NEXP encBits ⊆ Complexity.MA encBits)
    (hPermSim : WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1) →
      permFamily ℚ ∈ ConstantFreeVP ℚ →
      Complexity.PWithSharpPOracle encBits ⊆ NSUBEXP encBits) :
    ¬ (Complexity.NEXP encBits ⊆ Boolean.PPolyOn encBits) ∨
      permFamily ℚ ∉ ConstantFreeVP ℚ := by
  by_contra h
  push Not at h
  obtain ⟨hNEXP_ppoly, hPerm_vp⟩ := h
  have hNEXP_MA : Complexity.NEXP encBits ⊆ Complexity.MA encBits := hCollapse hNEXP_ppoly
  have hNEXP_sharpP : Complexity.NEXP encBits ⊆ Complexity.PWithSharpPOracle encBits :=
    hNEXP_MA.trans MA_subset_PWithSharpPOracle
  have hNEXP_nsubexp : Complexity.NEXP encBits ⊆ NSUBEXP encBits :=
    hNEXP_sharpP.trans (hPermSim hPIT hPerm_vp)
  exact NEXP_not_subset_NSUBEXP hNEXP_nsubexp

/-- Conditional transfer step specialized to deterministic polynomial-time white-box PIT
(`WhiteBoxPIT ∈ P`), using `P_subset_DSUBEXP`. -/
theorem nexp_not_ppoly_or_perm_not_constantFreeVP_of_polyPIT_of_collapse_of_permSim
    (hPIT : WhiteBoxPIT ∈ Complexity.P (encRatArithCircuit 1))
    (hCollapse : Complexity.NEXP encBits ⊆ Boolean.PPolyOn encBits →
      Complexity.NEXP encBits ⊆ Complexity.MA encBits)
    (hPermSim : WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1) →
      permFamily ℚ ∈ ConstantFreeVP ℚ →
      Complexity.PWithSharpPOracle encBits ⊆ NSUBEXP encBits) :
    ¬ (Complexity.NEXP encBits ⊆ Boolean.PPolyOn encBits) ∨
      permFamily ℚ ∉ ConstantFreeVP ℚ :=
  nexp_not_ppoly_or_perm_not_constantFreeVP_of_collapse_of_permSim
    (P_subset_DSUBEXP hPIT) hCollapse hPermSim

/-- Conditional hardness-vs-randomness transfer step stated for general `VP ℚ`. -/
theorem nexp_not_ppoly_or_perm_not_VP_of_collapse_of_permSim
    (hPIT : WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1))
    (hCollapse : Complexity.NEXP encBits ⊆ Boolean.PPolyOn encBits →
      Complexity.NEXP encBits ⊆ Complexity.MA encBits)
    (hPermSim : WhiteBoxPIT ∈ DSUBEXP (encRatArithCircuit 1) →
      permFamily ℚ ∈ VP ℚ →
      Complexity.PWithSharpPOracle encBits ⊆ NSUBEXP encBits) :
    ¬ (Complexity.NEXP encBits ⊆ Boolean.PPolyOn encBits) ∨
      permFamily ℚ ∉ VP ℚ := by
  by_contra h
  push Not at h
  exact NEXP_not_subset_NSUBEXP
    (((hCollapse h.1).trans MA_subset_PWithSharpPOracle).trans (hPermSim hPIT h.2))

end Dichotomy

/-! ## : Concrete Non-Vacuity and Sharpness Witnesses -/

section ConcreteWitnesses

open Cslib.Crypto.PRG.NisanWigderson Cslib.BitString

/-- Explicit 1-gate rational arithmetic circuit computing `X 0 * X 1`. -/
def mulTwoCircuit : Circuit (arithSignature ℚ) 2 1 :=
  Circuit.oneGate .mul ![0, 1]

/-- `mulTwoCircuit` computes `X 0 * X 1`, has syntactic degree `2`, is constant-free, and lies in
`WhiteBoxPIT`. -/
theorem mulTwoCircuit_mem_whiteBoxPIT :
    (⟨2, mulTwoCircuit⟩ : Σ n, Circuit (arithSignature ℚ) n 1) ∈ WhiteBoxPIT ∧
    mulTwoCircuit.syntacticDegree = 2 ∧
    mulTwoCircuit.IsConstantFree := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hev := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℚ))) h0
    simp [mulTwoCircuit, Circuit.polynomial] at hev
  · simp [mulTwoCircuit, Circuit.syntacticDegree_single, Circuit.outputSyntacticDegree,
      Circuit.eval_oneGate]
  · intro j
    fin_cases j
    trivial

/-- The singleton `{(1, 1)}` is a concrete hitting set for `{mulTwoCircuit}`. -/
theorem singleton_hits_mulTwoCircuit :
    IsCircuitHittingSet ({fun _ : Fin 2 => (1 : ℚ)} : Finset (Fin 2 → ℚ)) {mulTwoCircuit} := by
  intro c hc _
  rw [Set.mem_singleton_iff] at hc
  subst hc
  exact ⟨fun _ => 1, mem_singleton_self _, by simp [mulTwoCircuit, arithInterpretation]⟩

/-- Explicit 3-gate rational arithmetic circuit computing `X 0 + (-1) * X 0 = 0`, witnessing
membership in the complement of `WhiteBoxPIT`. -/
def cancelCircuit : Circuit (arithSignature ℚ) 1 1 :=
  ⟨(((Program.empty (σ := arithSignature ℚ)).gate ⟨ArithOp.const (-1 : ℚ), Fin.elim0⟩).gate
    ⟨ArithOp.mul, ![Wire.gate 0, Wire.input 0]⟩).gate
      ⟨ArithOp.add, ![Wire.input 0, Wire.gate 1]⟩,
    fun _ => Wire.gate 2⟩

/-- `cancelCircuit` computes the zero polynomial and is rejected by `WhiteBoxPIT`. -/
theorem cancelCircuit_notMem_whiteBoxPIT :
    (⟨1, cancelCircuit⟩ : Σ n, Circuit (arithSignature ℚ) n 1) ∉ WhiteBoxPIT := by
  simp only [WhiteBoxPIT, Set.mem_ofPred_eq, not_not]
  have hpoly : cancelCircuit.polynomial 0 = X 0 + (-1 : MvPolynomial (Fin 1) ℚ) * X 0 := by
    simp only [cancelCircuit, Circuit.polynomial, Circuit.eval, Program.trace, Program.eval,
      Line.eval, Function.comp_apply, Wire.elim, arithInterpretationWith_add,
      arithInterpretationWith_mul, arithInterpretationWith_const, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_neg, map_one]
    rfl
  rw [hpoly]
  ring

/-- Concrete non-vacuity of Laplace PIT certification for dimensions `0, 1, 2`:
explicit circuits `C₀ = 1`, `C₁ = X_{0,0}`, and `C₂ = X_{0,0} * X_{1,1} + X_{0,1} * X_{1,0}`
compute the generic permanents `per₀`, `per₁`, `per₂` and satisfy the Laplace identities. -/
theorem concrete_permanent_circuits_012 :
    ∃ (C0 : Circuit (arithSignature ℚ) (0 * 0) 1)
      (C1 : Circuit (arithSignature ℚ) (1 * 1) 1)
      (C2 : Circuit (arithSignature ℚ) (2 * 2) 1),
      C0.polynomial 0 = (genericMatrix ℚ 0).permanent ∧
      C1.polynomial 0 = (genericMatrix ℚ 1).permanent ∧
      C2.polynomial 0 = (genericMatrix ℚ 2).permanent ∧
      (constOneResidualCircuit C0).polynomial 0 = 0 := by
  let C0 : Circuit (arithSignature ℚ) 0 1 := Circuit.oneGate (.const 1) Fin.elim0
  let C1 : Circuit (arithSignature ℚ) 1 1 := Circuit.wiring _ fun _ => 0
  let C2 : Circuit (arithSignature ℚ) 4 1 :=
    ⟨(((Program.empty (σ := arithSignature ℚ)).gate
        ⟨ArithOp.mul, ![Wire.input 0, Wire.input 3]⟩).gate
      ⟨ArithOp.mul, ![Wire.input 1, Wire.input 2]⟩).gate
        ⟨ArithOp.add, ![Wire.gate 0, Wire.gate 1]⟩,
      fun _ => Wire.gate 2⟩
  refine ⟨C0, C1, C2, ?_, ?_, ?_, ?_⟩
  · rw [permanent_genericMatrix_zero]
    simp [C0, Circuit.polynomial]
  · simp [C1, Circuit.polynomial, Matrix.permanent, genericMatrix]
    rfl
  · have hC2 : C2.polynomial 0 = X 0 * X 3 + X 1 * X 2 := by
      simp only [C2, Circuit.polynomial, Circuit.eval, Program.trace, Program.eval, Line.eval,
        Function.comp_apply, Wire.elim, arithInterpretationWith_add, arithInterpretationWith_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    rw [hC2, matrix_permanent_succ_row_zero, Fin.sum_univ_two]
    simp [genericMatrix, finProdFinEquiv, Matrix.permanent]
  · rw [constOneResidualCircuit_polynomial]
    simp [C0, Circuit.polynomial]

/-- Concrete algebraic Nisan–Wigderson design witness: a `(3, 2, 1)`-design with `3` blocks
evaluated on the Boolean AND function agrees with `NisanWigderson.generator` on every Boolean
seed. -/
def concreteDesign321 : Design 3 2 1 3 where
  block
    | 0 => {0, 1}
    | 1 => {0, 2}
    | 2 => {1, 2}
  card_block i := by fin_cases i <;> decide
  card_inter_le {i j} hij := by fin_cases i <;> fin_cases j <;> simp_all

/-- Concrete evaluation witness for `algNWGenerator` on `concreteDesign321` and Boolean AND. -/
theorem concrete_algNWGenerator_and_eval (z : Fin 3 → Bool) (i : Fin 3) :
    eval (bitPoint z : Fin 3 → ℚ)
      (algNWGenerator ℚ concreteDesign321 (fun x => x 0 && x 1) i) =
      bitVal ℚ (generator concreteDesign321 (fun x => x 0 && x 1) z i) :=
  eval_bitPoint_algNWGenerator ℚ concreteDesign321 (fun x => x 0 && x 1) z i

/-! ### Sharpness Counterexamples for Schwartz–Zippel Hypotheses -/

/-- **Sharpness 1 (Zero divisors break Schwartz–Zippel)**: over `ZMod 6`, the degree-1 polynomial
`2 * X 0` is formally nonzero yet vanishes on the 2-element grid `{0, 3}`
(size `2 > 1 = degree`). -/
theorem sharpness_zeroDivisor_zmod6 :
    let p : MvPolynomial (Fin 1) (ZMod 6) := C 2 * X 0
    let S : Finset (ZMod 6) := {0, 3}
    p ≠ 0 ∧ p.totalDegree = 1 ∧ 1 < #S ∧ ∀ x : Fin 1 → ZMod 6, x 0 ∈ S → eval x p = 0 := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro h
    have hev := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (1 : ZMod 6))) h
    simp only [map_mul, eval_C, eval_X, map_zero, mul_one] at hev
    exact absurd hev (by decide)
  · have h1 : (C (2 : ZMod 6) * X 0 : MvPolynomial (Fin 1) (ZMod 6)) =
        monomial (Finsupp.single 0 1) 2 := by
      rw [X, C_mul_monomial, mul_one]
    rw [h1, totalDegree_monomial _ (by decide : (2 : ZMod 6) ≠ 0)]
    exact Finsupp.degree_single 0 1
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with h0 | h3
    · simp [h0]
    · simp only [map_mul, eval_C, eval_X, h3]; decide

/-- **Sharpness 2 (Small finite fields allow nonzero polynomials vanishing everywhere)**: over
`ZMod 5`, `X 0 ^ 5 - X 0` is formally nonzero yet vanishes on every point of `ZMod 5`. -/
theorem sharpness_finiteField_zmod5 :
    let p : MvPolynomial (Fin 1) (ZMod 5) := X 0 ^ 5 - X 0
    p ≠ 0 ∧ ∀ x : Fin 1 → ZMod 5, eval x p = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have hc := congrArg
      (fun q : MvPolynomial (Fin 1) (ZMod 5) => q.coeff (Finsupp.single (0 : Fin 1) 5)) h
    simp only [coeff_sub, X, monomial_pow, one_pow, coeff_monomial] at hc
    have h10 : (1 : ZMod 5) = 0 := by simpa using hc
    exact absurd h10 (by decide)
  · intro x
    simp only [map_sub, map_pow, eval_X]
    generalize x 0 = a
    fin_cases a <;> decide

/-- **Sharpness 3 (Grid size `≤` degree breaks grid-witness PIT)**: over `ℚ`, `(X 0) * (X 0 - 1)`
is formally nonzero of total degree `2` yet vanishes on the entire 2-element grid `{0, 1}`. -/
theorem sharpness_smallGrid_rat :
    let p : MvPolynomial (Fin 1) ℚ := X 0 * (X 0 - 1)
    let S : Finset ℚ := {0, 1}
    p ≠ 0 ∧ p.totalDegree ≤ 2 ∧ #S = 2 ∧
      ∀ x : Fin 1 → ℚ, x 0 ∈ S → eval x p = 0 := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro h
    have := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ))) h
    norm_num at this
  · refine (totalDegree_mul _ _).trans ?_
    have h1 : (X 0 : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1 := totalDegree_X_le 0
    have h2 : (X 0 - 1 : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le h1 (by simp))
    omega
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with h0 | h1
    · simp [h0]
    · simp [h1]

end ConcreteWitnesses

end Cslib.Circuits.Arithmetic
