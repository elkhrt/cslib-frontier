/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Depth
public import CslibFrontier.Computability.Circuit.Boolean.Barrington
public import CslibFrontier.Computability.Circuit.Depth
public import CslibFrontier.Computability.Circuit.Formula
public import Mathlib.Data.Matrix.PEquiv

/-!
# Formula Unrolling of Straight-Line Circuits and Barrington's Theorem for Circuits

Every wire of an acyclic straight-line `Cslib.Circuits.Program` (and hence every designated output
of a `Cslib.Circuits.Circuit`) unfolds along its input-and-gate DAG into an equivalent tree
`Cslib.Circuits.Formula` (`CslibFrontier.Circuits.wireToFormula`,
`CslibFrontier.Circuits.outputFormula`, `CslibFrontier.Circuits.toFormula`). While unrolling shared
fan-out gates may multiply gate count, every root-to-leaf path in the unrolled formula corresponds
to a directed path in the original circuit, so unrolling preserves both unit depth and arbitrary
operation-weighted depth (`depthWith`) with exact equality on each wire.

Combining formula unrolling with Barrington's theorem for De Morgan formulas
(`Cslib.Circuits.Formula.exists_monoidProgram_computes`) yields Barrington's theorem directly for
bounded-depth De Morgan Boolean circuits, both in `(1, σ)`-accepting monoid-program form and in the
two-five-cycle `(σ₀, σ₁)` and permutation-matrix `(A₀, A₁)` forms of length at most `4 ^ d`.

## Main definitions

* `CslibFrontier.Circuits.wireToFormula`: recursively unrolls a wire of a straight-line program into
  an equivalent formula over the same signature.
* `CslibFrontier.Circuits.outputFormula`: unrolls output `j` of a multi-output circuit into a
  formula.
* `CslibFrontier.Circuits.toFormula`: unrolls a single-output circuit into a formula.
* `CslibFrontier.Circuits.permMatrixCovariantHom`: covariant `{0, 1}`-permutation-matrix monoid
  homomorphism `Perm ι →* Matrix ι ι R` sending `σ ↦ σ⁻¹.toPEquiv.toMatrix`.

## Main results

* `CslibFrontier.Circuits.eval_wireToFormula`, `CslibFrontier.Circuits.eval_outputFormula`,
  `CslibFrontier.Circuits.eval_toFormula`, `CslibFrontier.Circuits.computes_toFormula`: exact
  semantic preservation under every interpretation.
* `CslibFrontier.Circuits.depthWith_wireToFormula`, `CslibFrontier.Circuits.depth_wireToFormula`,
  `CslibFrontier.Circuits.depthWith_outputFormula_le`,
  `CslibFrontier.Circuits.depth_outputFormula_le`, `CslibFrontier.Circuits.depthWith_toFormula`,
  `CslibFrontier.Circuits.depth_toFormula`: exact wire-depth preservation and circuit-depth bounds.
* `CslibFrontier.Circuits.fanInAtMost_wireToFormula`,
  `CslibFrontier.Circuits.fanInAtMost_outputFormula`,
  `CslibFrontier.Circuits.fanInAtMost_toFormula`,
  `CslibFrontier.Circuits.leafSize_toFormula_le_pow_depth`: fan-in preservation and `r ^ d`
  leaf-size bound for unrolled circuits.
* `CslibFrontier.Circuits.exists_monoidProgram_computes_of_circuit`,
  `CslibFrontier.Circuits.exists_distinct_fiveCycles_circuit_branchingProgram`,
  `CslibFrontier.Circuits.exists_distinct_fiveCycle_permMatrices_circuit`: Barrington's width-`5`,
  length-`4 ^ d` branching-program theorem for depth-`d` De Morgan Boolean circuits.
-/

public section

namespace CslibFrontier.Circuits

open Cslib.Circuits Cslib.BranchingPrograms Equiv

universe v u

section Unrolling

variable {σ : Signature.{v}} {n g m : ℕ} {U : Type u}

/-- Unroll a wire `w` of a straight-line program `p` into a tree `Formula` by expanding every
internal gate recursively into its argument wires. -/
def wireToFormula {g : ℕ} : Program σ n g → Wire n g → Formula σ n
  | .empty, .input i => .input i
  | .empty, .gate k => k.elim0
  | .gate _ _, .input i => .input i
  | .gate (gateCount := _) q line, .gate k =>
      Fin.lastCases
        (Formula.gate line.op fun a => wireToFormula q (line.wires a))
        (fun j => wireToFormula q (.gate j)) k

/-- Unrolling an original input wire yields the corresponding input leaf formula. -/
@[simp]
theorem wireToFormula_input (p : Program σ n g) (i : Fin n) :
    wireToFormula p (.input i) = .input i := by
  cases p <;> rfl

/-- Unrolling the newly appended gate of `q.gate line` builds an operation node from the unrolled
argument wires of `line`. -/
@[simp]
theorem wireToFormula_gate_last (q : Program σ n g) (line : Line σ n g) :
    wireToFormula (q.gate line) (.gate (Fin.last g)) =
      Formula.gate line.op fun a => wireToFormula q (line.wires a) := by
  simp [wireToFormula]

/-- Unrolling an earlier wire across an appended gate agrees with unrolling it in the prefix
program. -/
@[simp]
theorem wireToFormula_gate_castSucc (q : Program σ n g) (line : Line σ n g) (w : Wire n g) :
    wireToFormula (q.gate line) w.castSucc = wireToFormula q w := by
  cases w with
  | input i => simp
  | gate j => simp [wireToFormula]

/-- Evaluating the unrolled formula of a wire agrees with the program trace at that wire under
every interpretation. -/
@[simp]
theorem eval_wireToFormula (I : Interpretation σ U) (p : Program σ n g) (w : Wire n g)
    (x : Fin n → U) : (wireToFormula p w).eval I x = p.trace I x w := by
  induction p with
  | empty =>
    cases w with
    | input i => rfl
    | gate k => exact k.elim0
  | @gate g₀ q line ih =>
    induction w using Wire.lastCases with
    | last =>
      rw [wireToFormula_gate_last, Formula.eval_gate]
      change _ = (q.gate line).eval I x (Fin.last g₀)
      rw [Program.eval_gate_last, Line.eval]
      exact congrArg (I line.op) (funext fun a => ih (line.wires a))
    | castSucc w =>
      rw [wireToFormula_gate_castSucc, Program.trace_gate_castSucc]
      exact ih w

/-- Unrolling a wire preserves weighted depth `depthWith cost` for every operation cost function. -/
@[simp]
theorem depthWith_wireToFormula (cost : σ.Op → ℕ) (p : Program σ n g) (w : Wire n g) :
    (wireToFormula p w).depthWith cost = p.wireDepthsWith cost w := by
  induction p with
  | empty =>
    cases w with
    | input i => rfl
    | gate k => exact k.elim0
  | @gate g₀ q line ih =>
    induction w using Wire.lastCases with
    | last =>
      rw [wireToFormula_gate_last, Formula.depthWith_gate, Program.wireDepthsWith_gateWire,
        Program.depthsWith_gate_last, Line.depthWith_eq_sup]
      exact congrArg (· + cost line.op) (Finset.sup_congr rfl fun a _ => ih (line.wires a))
    | castSucc w =>
      rw [wireToFormula_gate_castSucc, Program.wireDepthsWith_gate_castSucc]
      exact ih w

/-- Unrolling a wire preserves unit gate depth exactly. -/
@[simp]
theorem depth_wireToFormula (p : Program σ n g) (w : Wire n g) :
    (wireToFormula p w).depth = p.wireDepths w := by
  rw [← Formula.depthWith_one, depthWith_wireToFormula, Program.wireDepthsWith_one]

/-- Unrolling any wire of a program with fan-in at most `r` produces a formula with fan-in at
most `r`. -/
theorem fanInAtMost_wireToFormula {r : ℕ} {p : Program σ n g} (hp : p.FanInAtMost r)
    (w : Wire n g) : (wireToFormula p w).FanInAtMost r := by
  induction p with
  | empty =>
    cases w with
    | input i => trivial
    | gate k => exact k.elim0
  | @gate g₀ q line ih =>
    obtain ⟨hq, hline⟩ := hp
    induction w using Wire.lastCases with
    | last =>
      rw [wireToFormula_gate_last]
      exact ⟨hline, fun a => ih hq (line.wires a)⟩
    | castSucc w =>
      rw [wireToFormula_gate_castSucc]
      exact ih hq w

/-- Unroll designated output `j` of a circuit `c` into a tree `Formula`. -/
def outputFormula (c : Circuit σ n m) (j : Fin m) : Formula σ n :=
  wireToFormula c.program (c.outputs j)

/-- Unroll a single-output circuit `c` into an equivalent tree `Formula`. -/
def toFormula (c : Circuit σ n 1) : Formula σ n :=
  outputFormula c 0

/-- Evaluating `outputFormula c j` computes output `j` of `c`. -/
@[simp]
theorem eval_outputFormula (I : Interpretation σ U) (c : Circuit σ n m) (j : Fin m)
    (x : Fin n → U) : (outputFormula c j).eval I x = c.eval I x j :=
  eval_wireToFormula I c.program (c.outputs j) x

/-- Evaluating `toFormula c` computes the unique output `0` of `c`. -/
@[simp]
theorem eval_toFormula (I : Interpretation σ U) (c : Circuit σ n 1) (x : Fin n → U) :
    (toFormula c).eval I x = c.eval I x 0 :=
  eval_outputFormula I c 0 x

/-- If a single-output circuit `c` computes `single f`, its unrolled formula `toFormula c`
computes `f`. -/
theorem computes_toFormula {I : Interpretation σ U} {c : Circuit σ n 1} {f : (Fin n → U) → U}
    (hc : c.Computes I (single f)) : (toFormula c).Computes I f := fun x => by
  rw [eval_toFormula, hc x, single_apply]

/-- The weighted depth of `outputFormula c j` is at most the weighted depth of `c`. -/
theorem depthWith_outputFormula_le (cost : σ.Op → ℕ) (c : Circuit σ n m) (j : Fin m) :
    (outputFormula c j).depthWith cost ≤ c.depthWith cost := by
  rw [outputFormula, depthWith_wireToFormula]
  exact c.wireDepthsWith_outputs_le_depthWith cost j

/-- The depth of `outputFormula c j` is at most the depth of `c`. -/
theorem depth_outputFormula_le (c : Circuit σ n m) (j : Fin m) :
    (outputFormula c j).depth ≤ c.depth := by
  simpa only [Formula.depthWith_one, Circuit.depthWith_one] using depthWith_outputFormula_le 1 c j

/-- For a single-output circuit `c`, unrolling to `toFormula c` preserves weighted depth `depthWith`
with exact equality. -/
@[simp]
theorem depthWith_toFormula (cost : σ.Op → ℕ) (c : Circuit σ n 1) :
    (toFormula c).depthWith cost = c.depthWith cost := by
  rw [toFormula, outputFormula, depthWith_wireToFormula, Circuit.depthWith_eq_sup, Fin.univ_succ]
  simp

/-- For a single-output circuit `c`, unrolling to `toFormula c` preserves unit depth with exact
equality. -/
@[simp]
theorem depth_toFormula (c : Circuit σ n 1) : (toFormula c).depth = c.depth := by
  rw [← Formula.depthWith_one, depthWith_toFormula, Circuit.depthWith_one]

/-- Output formulas of a bounded-fan-in circuit inherit the same fan-in bound. -/
theorem fanInAtMost_outputFormula {r : ℕ} {c : Circuit σ n m} (hc : c.FanInAtMost r) (j : Fin m) :
    (outputFormula c j).FanInAtMost r :=
  fanInAtMost_wireToFormula hc (c.outputs j)

/-- Unrolling a single-output circuit with fan-in at most `r` yields a formula with fan-in at
most `r`. -/
theorem fanInAtMost_toFormula {r : ℕ} {c : Circuit σ n 1} (hc : c.FanInAtMost r) :
    (toFormula c).FanInAtMost r :=
  fanInAtMost_outputFormula hc 0

/-- A single-output circuit of depth `d` and fan-in at most `r` unrolls to a formula with at most
`r ^ c.depth` input leaves. -/
theorem leafSize_toFormula_le_pow_depth {r : ℕ} {c : Circuit σ n 1} (hc : c.FanInAtMost r) :
    (toFormula c).leafSize ≤ r ^ c.depth := by
  simpa only [depth_toFormula] using Formula.leafSize_le_pow_depth (fanInAtMost_toFormula hc)

end Unrolling

section BarringtonCircuits

open Cslib.Circuits.Boolean

/-- **Barrington's theorem for De Morgan Boolean circuits**: for every five-cycle `σ` in `S₅` and
every single-output De Morgan circuit `c` on `n ≥ 1` inputs of depth at most `d`, there exists a
width-`5` permutation branching program of length at most `4 ^ d` that `σ`-computes `c`. -/
theorem exists_monoidProgram_computes_of_circuit {n d : ℕ} [NeZero n]
    (c : Circuit signature n 1) (hc : c.depth ≤ d) {σ : Perm (Fin 5)} (hσ : σ.IsFiveCycle) :
    ∃ P : MonoidProgram (Fin n) Bool (Perm (Fin 5)),
      P.toList.length ≤ 4 ^ d ∧ P.Computes σ (fun x => c.eval interpretation x 0) := by
  let F := toFormula c
  have hFdepth : F.depthWith binaryCost ≤ d := by
    have hbin : F.depthWith binaryCost ≤ F.depth :=
      F.depthWith_le_depth fun op => by cases op <;> simp [binaryCost]
    exact hbin.trans ((depth_toFormula c).trans_le hc)
  obtain ⟨P, hPlen, hPcomp⟩ := F.exists_monoidProgram_computes hσ
  refine ⟨P, hPlen.trans (Nat.pow_le_pow_right (by decide) hFdepth), fun x => ?_⟩
  simpa only [F, eval_toFormula] using hPcomp x

/-- **Two-five-cycle Barrington theorem for De Morgan Boolean circuits**: there exist two distinct
five-cycles `σ₀, σ₁ ∈ S₅` such that every single-output De Morgan circuit `c` on `n ≥ 1` inputs of
depth at most `d` is computed by a nonempty permutation branching program of length at most `4 ^ d`
evaluating to `σ₁` when `c` outputs `true` and `σ₀` when `c` outputs `false`. -/
theorem exists_distinct_fiveCycles_circuit_branchingProgram :
    ∃ σ₀ σ₁ : Perm (Fin 5), σ₀.IsFiveCycle ∧ σ₁.IsFiveCycle ∧ σ₀ ≠ σ₁ ∧
      ∀ {n d : ℕ} [NeZero n] (c : Circuit signature n 1), c.depth ≤ d →
        ∃ P : MonoidProgram (Fin n) Bool (Perm (Fin 5)),
          1 ≤ P.toList.length ∧ P.toList.length ≤ 4 ^ d ∧
            ∀ x, P.eval x = if c.eval interpretation x 0 then σ₁ else σ₀ := by
  let σ₀ : Perm (Fin 5) := ([0, 1, 2, 3, 4] : List (Fin 5)).formPerm
  let σ₁ : Perm (Fin 5) := ([0, 2, 4, 1, 3] : List (Fin 5)).formPerm
  have hσ₀ : σ₀.IsFiveCycle := Perm.isFiveCycle_formPerm (by decide) rfl
  have hσ₁ : σ₁.IsFiveCycle := Perm.isFiveCycle_formPerm (by decide) rfl
  have hne : σ₀ ≠ σ₁ := by decide
  have hmul : σ₀ * σ₀ = σ₁ := by decide
  refine ⟨σ₀, σ₁, hσ₀, hσ₁, hne, fun {n d} _ c hc => ?_⟩
  obtain ⟨Q, hQlen, hQcomp⟩ := exists_monoidProgram_computes_of_circuit c hc hσ₀
  refine ⟨MonoidProgram.mulLeft σ₀ Q, ?_, ?_, fun x => ?_⟩
  · rw [MonoidProgram.length_mulLeft]
    exact le_max_left 1 Q.toList.length
  · rw [MonoidProgram.length_mulLeft]
    exact max_le (Nat.one_le_pow d 4 (by decide)) hQlen
  · rw [MonoidProgram.eval_mulLeft, hQcomp x]
    cases h : c.eval interpretation x 0
    · simp [h]
    · simp [h, hmul]

/-- Covariant `{0, 1}`-valued permutation-matrix monoid homomorphism sending `σ : Perm ι` to the
matrix `σ⁻¹.toPEquiv.toMatrix` (whose `(i, j)` entry is `1` when `σ j = i` and `0` otherwise). -/
def permMatrixCovariantHom (ι R : Type*) [DecidableEq ι] [Fintype ι] [NonAssocSemiring R] :
    Perm ι →* Matrix ι ι R where
  toFun σ := σ⁻¹.toPEquiv.toMatrix
  map_one' := by
    ext i j
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.one_apply]
  map_mul' σ τ := by
    rw [mul_inv_rev, Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

/-- Entry formula for `permMatrixCovariantHom`: entry `(i, j)` equals `1` if `σ j = i` and `0`
otherwise. -/
@[simp]
theorem permMatrixCovariantHom_apply_entry {ι R : Type*} [DecidableEq ι] [Fintype ι]
    [NonAssocSemiring R] (σ : Perm ι) (i j : ι) :
    permMatrixCovariantHom ι R σ i j = if σ j = i then 1 else 0 := by
  change (if j ∈ σ⁻¹.toPEquiv i then (1 : R) else 0) = if σ j = i then 1 else 0
  by_cases h : σ j = i
  · subst h
    simp
  · simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Perm.inv_def, h,
      ↓reduceIte, ite_eq_right_iff]
    intro hs
    exact absurd (hs ▸ σ.apply_symm_apply i) h

/-- **Matrix Barrington theorem for De Morgan Boolean circuits**: over any nontrivial semiring `R`,
there exist two distinct `{0, 1}`-valued `5 × 5` five-cycle permutation matrices `A₀, A₁` such that
every single-output De Morgan circuit `c` on `n ≥ 1` inputs of depth at most `d` has a nonempty
matrix branching program of length at most `4 ^ d` whose step matrices are `{0, 1}`-valued `5 × 5`
permutation matrices and whose ordered product equals `A₁` when `c` outputs `true` and `A₀` when
`c` outputs `false`. -/
theorem exists_distinct_fiveCycle_permMatrices_circuit (R : Type*) [Semiring R] [Nontrivial R] :
    ∃ σ₀ σ₁ : Perm (Fin 5), σ₀.IsFiveCycle ∧ σ₁.IsFiveCycle ∧
      permMatrixCovariantHom (Fin 5) R σ₀ ≠ permMatrixCovariantHom (Fin 5) R σ₁ ∧
      ∀ {n d : ℕ} [NeZero n] (c : Circuit signature n 1), c.depth ≤ d →
        ∃ P : MonoidProgram (Fin n) Bool (Matrix (Fin 5) (Fin 5) R),
          1 ≤ P.toList.length ∧ P.toList.length ≤ 4 ^ d ∧
          (∀ I ∈ P.toList, ∀ b, ∃ τ : Perm (Fin 5),
            I.select b = permMatrixCovariantHom (Fin 5) R τ) ∧
          ∀ x, P.eval x =
            if c.eval interpretation x 0 then permMatrixCovariantHom (Fin 5) R σ₁
            else permMatrixCovariantHom (Fin 5) R σ₀ := by
  obtain ⟨σ₀, σ₁, hσ₀, hσ₁, hne, hprog⟩ := exists_distinct_fiveCycles_circuit_branchingProgram
  have hinj : Function.Injective (permMatrixCovariantHom (Fin 5) R) := fun τ₁ τ₂ h =>
    Equiv.ext fun j => by
      have hj := congrArg (fun M => M (τ₁ j) j) h
      simp only [permMatrixCovariantHom_apply_entry, ↓reduceIte] at hj
      split_ifs at hj with heq
      · exact heq.symm
      · exact absurd hj.symm zero_ne_one
  refine ⟨σ₀, σ₁, hσ₀, hσ₁, fun h => hne (hinj h), fun {n d} _ c hc => ?_⟩
  obtain ⟨Q, hQpos, hQlen, hQeval⟩ := hprog c hc
  refine ⟨Q.map (permMatrixCovariantHom (Fin 5) R), ?_, ?_, ?_, fun x => ?_⟩
  · simpa only [MonoidProgram.length_map] using hQpos
  · simpa only [MonoidProgram.length_map] using hQlen
  · intro I hI b
    rw [MonoidProgram.map, FreeMonoid.toList_map, List.mem_map] at hI
    obtain ⟨J, _, rfl⟩ := hI
    exact ⟨J.select b, rfl⟩
  · rw [MonoidProgram.eval_map, hQeval x]
    cases c.eval interpretation x 0 <;> rfl

example :
    let l₀ : Line signature 2 0 := ⟨.and, ![.input 0, .input 1]⟩
    let l₁ : Line signature 2 1 := ⟨.or, ![.gate 0, .gate 0]⟩
    let c : Circuit signature 2 1 := ⟨(Program.empty.gate l₀).gate l₁, fun _ => .gate 1⟩
    c.size = 2 ∧ (toFormula c).size = 3 ∧ (toFormula c).depth = 2 ∧ c.depth = 2 := by
  decide

end BarringtonCircuits

end CslibFrontier.Circuits
