module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic

/-!
# Algebraic Oracle Circuits, c-Reductions, Homogenization, and VP Closure

Defines arithmetic oracle circuits (`OracleInstr`, `OracleProgram`, `OracleCircuit`), oracle
complexity `oracleComplexity`, polynomial oracle reductions (`IsCReduction`), and
`VNP`-completeness under `c`-reductions (`IsVNPCompleteC`), and establishes:

* Projection embedding (`IsPProjection.isCReduction`), reflexivity, and transitivity of
  `c`-reductions.
* Constant-oracle collapse into `VP` (`mem_VP_of_isCReduction_const`).
* Lagrange homogenization (`oracleComputedWithin_homogeneousComponent`,
  `homogeneousComponentFamily_isCReduction`): over any infinite field, every homogeneous component
  of an `n`-variate polynomial `f` is computable with `≤ (n + 3) * (f.totalDegree + 1)` arithmetic
  and oracle operations.
* Downward closure of `VP` under `c`-reductions (`mem_VP_of_isCReduction`).
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial Finset

universe u

/-! ### Algebraic oracle complexity and $c$-reductions -/

/-- A single gate of an arithmetic oracle circuit with `w` previously available wires and an
`m`-ary polynomial oracle. -/
public inductive OracleInstr (K : Type u) (m w : ℕ) : Type u
  /-- Addition of two earlier wires. -/
  | add (i j : Fin w)
  /-- Multiplication of two earlier wires. -/
  | mul (i j : Fin w)
  /-- A scalar constant from `K`. -/
  | const (c : K)
  /-- Evaluation of the `m`-ary oracle polynomial on `m` earlier wires. -/
  | oracle (args : Fin m → Fin w)

/-- Whether an instruction counts as an arithmetic operation (`+`, `*`) or an oracle evaluation
(constants are free). -/
@[expose] public def OracleInstr.cost {K : Type u} {m w : ℕ} : OracleInstr K m w → ℕ
  | .add _ _ => 1
  | .mul _ _ => 1
  | .const _ => 0
  | .oracle _ => 1

/-- Cost of an addition gate is `1`. -/
@[simp] public theorem OracleInstr.cost_add {K : Type u} {m w : ℕ} (i j : Fin w) :
    (OracleInstr.add (K := K) (m := m) i j).cost = 1 := rfl
/-- Cost of a multiplication gate is `1`. -/
@[simp] public theorem OracleInstr.cost_mul {K : Type u} {m w : ℕ} (i j : Fin w) :
    (OracleInstr.mul (K := K) (m := m) i j).cost = 1 := rfl
/-- Cost of a constant gate is `0`. -/
@[simp] public theorem OracleInstr.cost_const {K : Type u} {m w : ℕ} (c : K) :
    (OracleInstr.const (m := m) (w := w) c).cost = 0 := rfl
/-- Cost of an oracle gate is `1`. -/
@[simp] public theorem OracleInstr.cost_oracle {K : Type u} {m w : ℕ} (args : Fin m → Fin w) :
    (OracleInstr.oracle (K := K) args).cost = 1 := rfl

/-- Straight-line arithmetic oracle program on `n` inputs with `s` instructions and an `m`-ary
oracle. -/
public inductive OracleProgram (K : Type u) (m n : ℕ) : ℕ → Type u
  /-- Empty program with `n` input wires. -/
  | nil : OracleProgram K m n 0
  /-- Append one instruction referencing the `n + s` existing wires. -/
  | snoc {s : ℕ} (p : OracleProgram K m n s) (instr : OracleInstr K m (n + s)) :
      OracleProgram K m n (s + 1)

namespace OracleProgram

variable {K : Type u} {m n s : ℕ}

/-- Total number of arithmetic (`+`, `*`) and oracle gates in a program. -/
@[expose] public def opCount : ∀ {s : ℕ}, OracleProgram K m n s → ℕ
  | _, .nil => 0
  | _, .snoc p instr => p.opCount + instr.cost

/-- Operation count of the empty oracle program is `0`. -/
@[simp] public theorem opCount_nil :
    (OracleProgram.nil (K := K) (m := m) (n := n)).opCount = 0 := rfl
/-- Operation count of a `snoc` oracle program adds the new instruction's cost. -/
@[simp] public theorem opCount_snoc (p : OracleProgram K m n s)
    (instr : OracleInstr K m (n + s)) :
    (p.snoc instr).opCount = p.opCount + instr.cost := rfl

/-- Evaluate every wire of an oracle program over a commutative semiring `K` with oracle
`g : MvPolynomial (Fin m) K`. -/
@[expose] public noncomputable def trace [CommSemiring K] (g : MvPolynomial (Fin m) K) :
    ∀ {s : ℕ}, OracleProgram K m n s → Fin (n + s) → MvPolynomial (Fin n) K
  | _, .nil => MvPolynomial.X
  | _, .snoc p instr =>
      let prev := p.trace g
      let val : MvPolynomial (Fin n) K :=
        match instr with
        | .add i j => prev i + prev j
        | .mul i j => prev i * prev j
        | .const c => MvPolynomial.C c
        | .oracle args => MvPolynomial.aeval (fun a => prev (args a)) g
      Fin.snoc prev val

/-- `trace` on the empty oracle program returns the input indeterminates. -/
@[simp] public theorem trace_nil [CommSemiring K] (g : MvPolynomial (Fin m) K) (i : Fin n) :
    (OracleProgram.nil (K := K) (m := m) (n := n)).trace g i = MvPolynomial.X i := rfl

/-- `trace` on an old wire is preserved when appending a new instruction. -/
@[simp] public theorem trace_snoc_castSucc [CommSemiring K] (g : MvPolynomial (Fin m) K)
    (p : OracleProgram K m n s) (instr : OracleInstr K m (n + s)) (i : Fin (n + s)) :
    (p.snoc instr).trace g i.castSucc = p.trace g i := by
  simp [trace]

/-- `trace` on the newest wire of a `snoc` program evaluates its instruction. -/
@[simp] public theorem trace_snoc_last [CommSemiring K] (g : MvPolynomial (Fin m) K)
    (p : OracleProgram K m n s) (instr : OracleInstr K m (n + s)) :
    (p.snoc instr).trace g (Fin.last (n + s)) =
      match instr with
      | .add i j => p.trace g i + p.trace g j
      | .mul i j => p.trace g i * p.trace g j
      | .const c => MvPolynomial.C c
      | .oracle args => MvPolynomial.aeval (fun a => p.trace g (args a)) g := by
  simp [trace]

/-- Input wire `v : Fin n` always evaluates to `MvPolynomial.X v`. -/
public theorem trace_input [CommSemiring K] (g : MvPolynomial (Fin m) K)
    (p : OracleProgram K m n s) (v : Fin n) :
    p.trace g (v.castLE (Nat.le_add_right n s)) = MvPolynomial.X v := by
  induction p with
  | nil => rfl
  | @snoc s' p' instr ih =>
      have hcast : (v.castLE (Nat.le_add_right n (s' + 1)) : Fin (n + (s' + 1))) =
          (v.castLE (Nat.le_add_right n s')).castSucc := by ext; rfl
      rw [hcast, trace_snoc_castSucc, ih]

/-- Map every wire reference in an instruction along `f : Fin w₁ → Fin w₂`. -/
@[expose] public def mapInstr {w₁ w₂ : ℕ} (f : Fin w₁ → Fin w₂) :
    OracleInstr K m w₁ → OracleInstr K m w₂
  | .add i j => .add (f i) (f j)
  | .mul i j => .mul (f i) (f j)
  | .const c => .const c
  | .oracle args => .oracle (f ∘ args)

/-- Cost is preserved by wire remapping. -/
@[simp] public theorem cost_mapInstr {w₁ w₂ : ℕ} (f : Fin w₁ → Fin w₂)
    (instr : OracleInstr K m w₁) : (mapInstr f instr).cost = instr.cost := by
  cases instr <;> rfl

/-- Shift an `m`-ary oracle program on `n` inputs so that its inputs are fed from `n₀` inputs
through wire indices `inWires : Fin n → Fin (n₀ + s₀)` inside an existing program `base`. -/
@[expose] public def append {n₀ s₀ : ℕ} (base : OracleProgram K m n₀ s₀)
    (inWires : Fin n → Fin (n₀ + s₀)) :
    ∀ {s : ℕ}, OracleProgram K m n s → OracleProgram K m n₀ (s₀ + s)
  | _, .nil => base
  | _, .snoc p instr =>
      let q := base.append inWires p
      let liftWire : Fin (n + _) → Fin (n₀ + (s₀ + _)) := fun w =>
        if h : w.1 < n then
          (inWires ⟨w.1, h⟩).castLE (by omega)
        else
          ⟨n₀ + s₀ + (w.1 - n), by omega⟩
      q.snoc (mapInstr liftWire instr)

/-- Operation count of `append` is the sum of operation counts. -/
public theorem opCount_append {n₀ s₀ s : ℕ} (base : OracleProgram K m n₀ s₀)
    (inWires : Fin n → Fin (n₀ + s₀)) (p : OracleProgram K m n s) :
    (base.append inWires p).opCount = base.opCount + p.opCount := by
  induction p with
  | nil => simp [append, opCount]
  | snoc p instr ih =>
      simp only [append, opCount, cost_mapInstr, ih, Nat.add_assoc]

/-- Trace of `append` on any wire from `base` agrees with `base.trace`. -/
public theorem trace_append_left [CommSemiring K] (g : MvPolynomial (Fin m) K)
    {n₀ s₀ s : ℕ} (base : OracleProgram K m n₀ s₀) (inWires : Fin n → Fin (n₀ + s₀))
    (p : OracleProgram K m n s) (w : Fin (n₀ + s₀)) :
    (base.append inWires p).trace g (w.castLE (by omega)) = base.trace g w := by
  induction p with
  | nil => rfl
  | @snoc s' p instr ih =>
      have hcast : (w.castLE (by omega) : Fin (n₀ + (s₀ + (s' + 1)))) =
          (w.castLE (by omega : n₀ + s₀ ≤ n₀ + (s₀ + s'))).castSucc := by
        ext; rfl
      rw [append, hcast, trace_snoc_castSucc, ih]

/-- Trace of `append` on a wire of `p` evaluates `p.trace g` with inputs substituted by
`base.trace g ∘ inWires`. -/
public theorem trace_append_right [CommSemiring K] (g : MvPolynomial (Fin m) K)
    {n₀ s₀ s : ℕ} (base : OracleProgram K m n₀ s₀) (inWires : Fin n → Fin (n₀ + s₀))
    (p : OracleProgram K m n s) (w : Fin (n + s)) :
    (base.append inWires p).trace g
        (if h : w.1 < n then (inWires ⟨w.1, h⟩).castLE (by omega)
         else ⟨n₀ + s₀ + (w.1 - n), by omega⟩) =
      MvPolynomial.aeval (fun i => base.trace g (inWires i)) (p.trace g w) := by
  induction p with
  | nil =>
      have hw : w.1 < n := w.2
      simp only [append, hw, ↓reduceDIte, Fin.castLE_rfl, trace, MvPolynomial.aeval_X]
      congr 1
  | @snoc s' p instr ih =>
      by_cases hlast : w.1 = n + s'
      · have hw_last : w = Fin.last (n + s') := Fin.ext hlast
        subst hw_last
        have hnotlt : ¬ (n + s' < n) := by omega
        have hidx : (⟨n₀ + s₀ + (n + s' - n), by omega⟩ : Fin (n₀ + (s₀ + (s' + 1)))) =
            Fin.last (n₀ + (s₀ + s')) := by
          ext; dsimp only [Fin.val_last]; omega
        simp only [append, Fin.val_last, hnotlt, ↓reduceDIte, hidx, trace_snoc_last]
        cases instr with
        | add i j =>
            simp only [mapInstr, map_add, ih i, ih j]
        | mul i j =>
            simp only [mapInstr, map_mul, ih i, ih j]
        | const c =>
            simp only [mapInstr, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
        | oracle args =>
            simp only [mapInstr, Function.comp_apply]
            have hcomp :
                MvPolynomial.aeval (fun i => base.trace g (inWires i))
                  (MvPolynomial.aeval (fun a => p.trace g (args a)) g) =
                MvPolynomial.aeval
                  (fun a => MvPolynomial.aeval (fun i => base.trace g (inWires i))
                    (p.trace g (args a))) g := by
              rw [← AlgHom.comp_apply]
              congr 1
              apply MvPolynomial.algHom_ext
              intro a
              simp
            rw [hcomp]
            exact congrArg (fun fn => MvPolynomial.aeval fn g) (funext fun a => ih (args a))
      · have hw_lt : w.1 < n + s' := by omega
        let w' : Fin (n + s') := ⟨w.1, hw_lt⟩
        have hw_eq : w = w'.castSucc := Fin.ext rfl
        rw [hw_eq, trace_snoc_castSucc]
        have hsub :
            (if h : w'.castSucc.1 < n then (inWires ⟨w'.castSucc.1, h⟩).castLE (by omega)
             else ⟨n₀ + s₀ + (w'.castSucc.1 - n), by omega⟩ : Fin (n₀ + (s₀ + (s' + 1)))) =
            (if h : w'.1 < n then (inWires ⟨w'.1, h⟩).castLE (by omega)
             else ⟨n₀ + s₀ + (w'.1 - n), by omega⟩ : Fin (n₀ + (s₀ + s'))).castSucc := by
          by_cases hw' : w'.1 < n
          · simp only [Fin.val_castSucc, hw', ↓reduceDIte]
            ext; rfl
          · simp only [Fin.val_castSucc, hw', ↓reduceDIte]
            ext; rfl
        rw [append, hsub, trace_snoc_castSucc, ih w']

end OracleProgram

/-- An arithmetic oracle circuit over `K` with `n` inputs and an `m`-ary oracle polynomial. -/
public structure OracleCircuit (K : Type u) (m n : ℕ) : Type u where
  /-- Number of instructions in the straight-line program. -/
  size : ℕ
  /-- The straight-line program. -/
  prog : OracleProgram K m n size
  /-- Output wire index. -/
  out : Fin (n + size)

/-- Number of arithmetic (`+`, `*`) and oracle gates in an `OracleCircuit`. -/
@[expose] public def OracleCircuit.opCount {K : Type u} {m n : ℕ}
    (c : OracleCircuit K m n) : ℕ :=
  c.prog.opCount

/-- Operation count of a constructed `OracleCircuit`. -/
@[simp] public theorem OracleCircuit.opCount_mk {K : Type u} {m n : ℕ} (s : ℕ)
    (p : OracleProgram K m n s) (o : Fin (n + s)) :
    (OracleCircuit.mk s p o).opCount = p.opCount := rfl

/-- Operation count of an `OracleCircuit` equals its program's operation count. -/
public theorem OracleCircuit.opCount_eq_prog {K : Type u} {m n : ℕ} (c : OracleCircuit K m n) :
    c.opCount = c.prog.opCount := rfl

/-- The formal polynomial computed by an `OracleCircuit` given oracle polynomial `g`. -/
@[expose] public noncomputable def OracleCircuit.eval {K : Type u} [CommSemiring K] {m n : ℕ}
    (g : MvPolynomial (Fin m) K) (c : OracleCircuit K m n) : MvPolynomial (Fin n) K :=
  c.prog.trace g c.out

/-- Evaluation of a constructed `OracleCircuit`. -/
@[simp] public theorem OracleCircuit.eval_mk {K : Type u} [CommSemiring K] {m n : ℕ} (s : ℕ)
    (p : OracleProgram K m n s) (o : Fin (n + s)) (g : MvPolynomial (Fin m) K) :
    (OracleCircuit.mk s p o).eval g = p.trace g o := rfl

/-- Evaluation of an `OracleCircuit` equals its program's trace at `c.out`. -/
public theorem OracleCircuit.eval_eq_trace {K : Type u} [CommSemiring K] {m n : ℕ}
    (g : MvPolynomial (Fin m) K) (c : OracleCircuit K m n) :
    c.eval g = c.prog.trace g c.out := rfl

/-- `f` is computed with oracle `g` using at most `s` arithmetic (`+`, `*`) and oracle gates. -/
@[expose] public def OracleComputedWithin {K : Type u} [CommSemiring K] {m n : ℕ}
    (g : MvPolynomial (Fin m) K) (f : MvPolynomial (Fin n) K) (s : ℕ) : Prop :=
  ∃ c : OracleCircuit K m n, c.opCount ≤ s ∧ c.eval g = f

/-- The *oracle complexity* $L^g(f)$: minimum
number of arithmetic operations (`+`, `*`) and oracle evaluations of `g` sufficient to compute
`f` from the indeterminates and constants in `K`. -/
@[expose] public noncomputable def oracleComplexity {K : Type u} [CommSemiring K] {m n : ℕ}
    (g : MvPolynomial (Fin m) K) (f : MvPolynomial (Fin n) K) : ℕ :=
  sInf {s | OracleComputedWithin g f s}

/-- `OracleComputedWithin` is monotone in the operation budget. -/
public theorem OracleComputedWithin.mono {K : Type u} [CommSemiring K] {m n : ℕ}
    {g : MvPolynomial (Fin m) K} {f : MvPolynomial (Fin n) K} {s t : ℕ}
    (h : OracleComputedWithin g f s) (hst : s ≤ t) : OracleComputedWithin g f t :=
  let ⟨c, hc, he⟩ := h
  ⟨c, hc.trans hst, he⟩

/-- If `OracleComputedWithin g f s`, then `oracleComplexity g f ≤ s`. -/
public theorem oracleComplexity_le_of_oracleComputedWithin {K : Type u} [CommSemiring K] {m n : ℕ}
    {g : MvPolynomial (Fin m) K} {f : MvPolynomial (Fin n) K} {s : ℕ}
    (h : OracleComputedWithin g f s) : oracleComplexity g f ≤ s :=
  Nat.sInf_le h

/-- If `OracleComputedWithin g f s`, then `OracleComputedWithin g f (oracleComplexity g f)`. -/
public theorem oracleComputedWithin_oracleComplexity {K : Type u} [CommSemiring K] {m n : ℕ}
    {g : MvPolynomial (Fin m) K} {f : MvPolynomial (Fin n) K} {s : ℕ}
    (h : OracleComputedWithin g f s) : OracleComputedWithin g f (oracleComplexity g f) :=
  Nat.sInf_mem (s := {t | OracleComputedWithin g f t}) ⟨s, h⟩

/-- Every projection `IsProjection f g` has oracle complexity at most `1` (one oracle gate plus
free constant wires). -/
public theorem oracleComputedWithin_of_isProjection {K : Type u} [CommSemiring K] {m n : ℕ}
    {f : MvPolynomial (Fin n) K} {g : MvPolynomial (Fin m) K} (h : IsProjection f g) :
    OracleComputedWithin g f 1 := by
  obtain ⟨ρ, rfl⟩ := h
  have hbuild : ∀ (k : ℕ) (ρ' : Fin k → Fin n ⊕ K),
      ∃ (s : ℕ) (p : OracleProgram K m n s) (wires : Fin k → Fin (n + s)),
        p.opCount = 0 ∧
        ∀ j, p.trace g (wires j) = Sum.elim MvPolynomial.X (fun a => MvPolynomial.C a) (ρ' j) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨0, .nil, Fin.elim0, rfl, fun j => Fin.elim0 j⟩
    | succ k ih =>
        intro ρ'
        obtain ⟨s, p, wires, hcnt, hwires⟩ := ih (ρ' ∘ Fin.castSucc)
        cases hlast : ρ' (Fin.last k) with
        | inl v =>
            refine ⟨s, p, Fin.snoc wires (v.castLE (Nat.le_add_right n s)), hcnt, fun j => ?_⟩
            refine Fin.lastCases ?_ ?_ j
            · simp only [Fin.snoc_last, hlast, Sum.elim_inl]
              exact p.trace_input g v
            · intro j'
              simpa [Fin.snoc_castSucc] using hwires j'
        | inr c =>
            refine ⟨s + 1, p.snoc (.const c),
              Fin.snoc (fun j => (wires j).castSucc) (Fin.last (n + s)),
              by simp [OracleProgram.opCount, OracleInstr.cost, hcnt], fun j => ?_⟩
            refine Fin.lastCases ?_ ?_ j
            · simp [Fin.snoc_last, hlast]
            · intro j'
              simpa [Fin.snoc_castSucc] using hwires j'
  obtain ⟨s, p, wires, hcnt, hwires⟩ := hbuild m ρ
  refine ⟨⟨s + 1, p.snoc (.oracle wires), Fin.last (n + s)⟩, ?_, ?_⟩
  · simp [OracleCircuit.opCount, OracleProgram.opCount, OracleInstr.cost, hcnt]
  · simp only [OracleCircuit.eval, OracleProgram.trace_snoc_last, projection]
    exact congrArg (fun fn => MvPolynomial.aeval fn g) (funext hwires)

/-- Helper: inline an `m₁`-ary oracle circuit `sub` (using `m₂`-ary oracle `h`) into an `m₁`-ary
oracle program `p` on `n` inputs, preserving all wire values with op-count multiplied by at most
`sub.opCount + 1`. -/
private theorem exists_inlineProgram {K : Type u} [CommSemiring K] {m₁ m₂ n : ℕ}
    {g : MvPolynomial (Fin m₁) K} {h : MvPolynomial (Fin m₂) K}
    (sub : OracleCircuit K m₂ m₁) (hsub : sub.eval h = g) :
    ∀ {s : ℕ} (p : OracleProgram K m₁ n s),
      ∃ (s' : ℕ) (q : OracleProgram K m₂ n s') (wireMap : Fin (n + s) → Fin (n + s')),
        q.opCount ≤ p.opCount * (sub.opCount + 1) ∧
        ∀ w, q.trace h (wireMap w) = p.trace g w := by
  intro s p
  induction p with
  | nil =>
      exact ⟨0, .nil, id, by simp [OracleProgram.opCount], fun _ => rfl⟩
  | @snoc s p instr ih =>
      obtain ⟨s', q, wireMap, hcnt, hval⟩ := ih
      cases instr with
      | add i j =>
          refine ⟨s' + 1, q.snoc (.add (wireMap i) (wireMap j)),
            Fin.snoc (fun w => (wireMap w).castSucc) (Fin.last (n + s')), ?_, ?_⟩
          · simp only [OracleProgram.opCount, OracleInstr.cost]
            nlinarith
          · intro w
            refine Fin.lastCases ?_ ?_ w
            · simp [Fin.snoc_last, hval]
            · intro w'; simp [Fin.snoc_castSucc, hval]
      | mul i j =>
          refine ⟨s' + 1, q.snoc (.mul (wireMap i) (wireMap j)),
            Fin.snoc (fun w => (wireMap w).castSucc) (Fin.last (n + s')), ?_, ?_⟩
          · simp only [OracleProgram.opCount, OracleInstr.cost]
            nlinarith
          · intro w
            refine Fin.lastCases ?_ ?_ w
            · simp [Fin.snoc_last, hval]
            · intro w'; simp [Fin.snoc_castSucc, hval]
      | const c =>
          refine ⟨s' + 1, q.snoc (.const c),
            Fin.snoc (fun w => (wireMap w).castSucc) (Fin.last (n + s')), ?_, ?_⟩
          · simp only [OracleProgram.opCount, OracleInstr.cost]
            omega
          · intro w
            refine Fin.lastCases ?_ ?_ w
            · simp [Fin.snoc_last]
            · intro w'; simp [Fin.snoc_castSucc, hval]
      | oracle args =>
          let inWires : Fin m₁ → Fin (n + s') := fun a => wireMap (args a)
          let q' : OracleProgram K m₂ n (s' + sub.size) := q.append inWires sub.prog
          let outWire : Fin (n + (s' + sub.size)) :=
            if hh : sub.out.1 < m₁ then
              (inWires ⟨sub.out.1, hh⟩).castLE (by omega)
            else
              ⟨n + s' + (sub.out.1 - m₁), by omega⟩
          refine ⟨s' + sub.size, q',
            Fin.snoc (fun w => (wireMap w).castLE (by omega)) outWire, ?_, ?_⟩
          · simp only [q', OracleProgram.opCount_append, OracleProgram.opCount, OracleInstr.cost]
            change q.opCount + sub.opCount ≤ (p.opCount + 1) * (sub.opCount + 1)
            nlinarith
          · intro w
            refine Fin.lastCases ?_ ?_ w
            · simp only [Fin.snoc_last, q', outWire]
              rw [OracleProgram.trace_append_right]
              change MvPolynomial.aeval (fun a => q.trace h (wireMap (args a))) (sub.eval h) =
                (p.snoc (.oracle args)).trace g (Fin.last (n + s))
              rw [hsub, OracleProgram.trace_snoc_last]
              exact congrArg (fun fn => MvPolynomial.aeval fn g) (funext fun a => hval (args a))
            · intro w'
              simp only [Fin.snoc_castSucc, OracleProgram.trace_snoc_castSucc, q']
              rw [OracleProgram.trace_append_left, hval w']

/-- Transitivity of `OracleComputedWithin`: composing oracle computations multiplies operation
counts by at most `s₁ * (s₂ + 1)`. -/
public theorem OracleComputedWithin.trans {K : Type u} [CommSemiring K] {m₁ m₂ n : ℕ}
    {f : MvPolynomial (Fin n) K} {g : MvPolynomial (Fin m₁) K} {h : MvPolynomial (Fin m₂) K}
    {s₁ s₂ : ℕ} (hfg : OracleComputedWithin g f s₁) (hgh : OracleComputedWithin h g s₂) :
    OracleComputedWithin h f (s₁ * (s₂ + 1)) := by
  obtain ⟨c₁, hc₁, he₁⟩ := hfg
  obtain ⟨c₂, hc₂, he₂⟩ := hgh
  obtain ⟨s', q, wireMap, hcnt, hval⟩ := exists_inlineProgram c₂ he₂ c₁.prog
  refine ⟨⟨s', q, wireMap c₁.out⟩, ?_, (hval c₁.out).trans he₁⟩
  exact hcnt.trans (Nat.mul_le_mul hc₁ (Nat.add_le_add_right hc₂ 1))

/-- A *$c$-reduction* (polynomial oracle reduction) $f \le_c g$ between polynomial families. -/
@[expose] public def IsCReduction {K : Type u} [CommSemiring K]
    (f g : PolynomialFamily K) : Prop :=
  ∃ (t b : ℕ → ℕ), PolynomiallyBounded t ∧ PolynomiallyBounded b ∧
    ∀ n, OracleComputedWithin (g.poly (t n)) (f.poly n) (b n)

/-- Reflexivity of $c$-reductions. -/
public theorem IsCReduction.refl {K : Type u} [CommSemiring K] (f : PolynomialFamily K) :
    IsCReduction f f :=
  ⟨id, fun _ => 1, PolynomiallyBounded.id, PolynomiallyBounded.const 1, fun n =>
    oracleComputedWithin_of_isProjection (IsProjection.refl (f.poly n))⟩

/-- Every $p$-projection is a $c$-reduction. -/
public theorem IsPProjection.isCReduction {K : Type u} [CommSemiring K]
    {f g : PolynomialFamily K} (h : f.IsPProjection g) : IsCReduction f g := by
  obtain ⟨t, ht, hproj⟩ := h
  exact ⟨t, fun _ => 1, ht, PolynomiallyBounded.const 1, fun n =>
    oracleComputedWithin_of_isProjection (hproj n)⟩

/-- Transitivity of $c$-reductions. -/
public theorem IsCReduction.trans {K : Type u} [CommSemiring K]
    {f g h : PolynomialFamily K} (hfg : IsCReduction f g) (hgh : IsCReduction g h) :
    IsCReduction f h := by
  obtain ⟨t₁, b₁, ht₁, hb₁, h₁⟩ := hfg
  obtain ⟨t₂, b₂, ht₂, hb₂, h₂⟩ := hgh
  refine ⟨fun n => t₂ (t₁ n), fun n => b₁ n * (b₂ (t₁ n) + 1),
    ht₂.comp ht₁, hb₁.mul ((hb₂.comp ht₁).add (PolynomiallyBounded.const 1)), fun n => ?_⟩
  exact (h₁ n).trans (h₂ (t₁ n))

/-- A polynomial family is $\mathrm{VNP}$-hard under $c$-reductions. -/
@[expose] public def IsVNPHardC {K : Type u} [CommSemiring K] (f : PolynomialFamily K) : Prop :=
  ∀ g ∈ VNP K, IsCReduction g f

/-- A polynomial family is $\mathrm{VNP}$-complete under $c$-reductions. -/
@[expose] public def IsVNPCompleteC {K : Type u} [CommSemiring K] (f : PolynomialFamily K) : Prop :=
  f ∈ VNP K ∧ IsVNPHardC f

/-- Every `VNP`-complete family under $p$-projections is `VNP`-complete under $c$-reductions. -/
public theorem IsVNPComplete.isVNPCompleteC {K : Type u} [CommSemiring K]
    {f : PolynomialFamily K} (hf : IsVNPComplete f) : IsVNPCompleteC f :=
  ⟨hf.1, fun g hg => IsPProjection.isCReduction (hf.2 g hg)⟩

/-- `VNP`-hardness under $c$-reductions transfers along $c$-reductions. -/
public theorem IsVNPHardC.trans {K : Type u} [CommSemiring K]
    {f g : PolynomialFamily K} (hf : IsVNPHardC f) (hfg : IsCReduction f g) : IsVNPHardC g :=
  fun h hh => (hf h hh).trans hfg

/-- `VNP`-completeness under $p$-projections transfers along $p$-projections. -/
public theorem IsVNPComplete.of_isPProjection {K : Type u} [CommSemiring K]
    {f g : PolynomialFamily K} (hf : IsVNPComplete f) (hg : g ∈ VNP K)
    (hfg : f.IsPProjection g) : IsVNPComplete g :=
  ⟨hg, fun h hh => (hf.2 h hh).trans hfg⟩

/-- An oracle program with a constant oracle and `opCount ≤ s` computes its output by a standard
arithmetic circuit of size `≤ 2 * s + 1`. -/
public theorem exists_circuit_of_oracleComputedWithin_const {K : Type u} [CommSemiring K]
    {m n : ℕ} {a : K} {f : MvPolynomial (Fin n) K} {s : ℕ}
    (h : OracleComputedWithin (MvPolynomial.C a : MvPolynomial (Fin m) K) f s) :
    ∃ c : Circuit (arithSignature K) n 1, c.polynomial 0 = f ∧ c.size ≤ 2 * s + 1 := by
  obtain ⟨oc, hcop, rfl⟩ := h
  have hsyn : ∀ {t : ℕ} (p : OracleProgram K m n t) (S : Finset (Fin (n + t))),
      Synthesis (arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K))
        (inputs n)
        ((fun w => fun x : Fin n → MvPolynomial (Fin n) K =>
          MvPolynomial.aeval x (p.trace (MvPolynomial.C a) w)) '' (S : Set (Fin (n + t))))
        (2 * p.opCount + S.card) := by
    intro t p
    induction p with
    | nil =>
        intro S
        refine (Synthesis.of_subset (s := inputs n) ?_).mono Set.Subset.rfl Set.Subset.rfl
          (Nat.zero_le _)
        rintro _ ⟨w, -, rfl⟩
        refine ⟨w, funext fun x => ?_⟩
        simp [OracleProgram.trace]
    | @snoc t p instr ih =>
        intro S
        let S0 : Finset (Fin (n + t)) := S.preimage Fin.castSucc (Fin.castSucc_injective _).injOn
        have hcard : S0.card ≤ S.card :=
          Finset.card_le_card_of_injOn Fin.castSucc (fun w hw => by simpa [S0] using hw)
            (Fin.castSucc_injective _).injOn
        by_cases hlast : Fin.last (n + t) ∈ S
        · have hcard_lt : S0.card + 1 = S.card := by
            have hdisj : Disjoint (S0.image Fin.castSucc) {Fin.last (n + t)} := by
              rw [Finset.disjoint_singleton_right, Finset.mem_image]
              rintro ⟨w, -, hw⟩
              exact Fin.castSucc_ne_last w hw
            have hunion : S0.image Fin.castSucc ∪ {Fin.last (n + t)} = S := by
              ext w
              simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, S0,
                Finset.mem_preimage]
              refine Fin.lastCases ?_ ?_ w
              · simp [hlast]
              · intro w'
                simp [Fin.castSucc_ne_last]
            rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
              Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
          cases instr with
          | add i j =>
              let S' := insert i (insert j S0)
              have hS' : S'.card ≤ S0.card + 2 :=
                (Finset.card_insert_le _ _).trans
                  (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
              have hbase := ih S'
              have hadd : Synthesis
                  (arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K))
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace (MvPolynomial.C a) w)) ''
                      (S' : Set (Fin (n + t)))))
                  {fun x => MvPolynomial.aeval x (p.trace (MvPolynomial.C a) i) +
                    MvPolynomial.aeval x (p.trace (MvPolynomial.C a) j)} 1 :=
                Synthesis.arith_add
                  (Or.inr ⟨i, by simp [S'], rfl⟩)
                  (Or.inr ⟨j, by simp [S'], rfl⟩)
              have hcomb := hbase.comp hadd
              refine hcomb.mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _
                  right
                  simp [OracleProgram.trace_snoc_last]
                · intro w' hw
                  left
                  refine ⟨w', ?_, by simp [OracleProgram.trace_snoc_castSucc]⟩
                  have hw' : w' ∈ S0 := by simpa [S0] using hw
                  simp [S', hw']
              · simp only [OracleProgram.opCount, OracleInstr.cost]
                omega
          | mul i j =>
              let S' := insert i (insert j S0)
              have hS' : S'.card ≤ S0.card + 2 :=
                (Finset.card_insert_le _ _).trans
                  (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
              have hbase := ih S'
              have hmul : Synthesis
                  (arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K))
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace (MvPolynomial.C a) w)) ''
                      (S' : Set (Fin (n + t)))))
                  {fun x => MvPolynomial.aeval x (p.trace (MvPolynomial.C a) i) *
                    MvPolynomial.aeval x (p.trace (MvPolynomial.C a) j)} 1 :=
                Synthesis.arith_mul
                  (Or.inr ⟨i, by simp [S'], rfl⟩)
                  (Or.inr ⟨j, by simp [S'], rfl⟩)
              have hcomb := hbase.comp hmul
              refine hcomb.mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _
                  right
                  simp [OracleProgram.trace_snoc_last]
                · intro w' hw
                  left
                  refine ⟨w', ?_, by simp [OracleProgram.trace_snoc_castSucc]⟩
                  have hw' : w' ∈ S0 := by simpa [S0] using hw
                  simp [S', hw']
              · simp only [OracleProgram.opCount, OracleInstr.cost]
                omega
          | const b =>
              have hbase := ih S0
              have hc : Synthesis
                  (arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K))
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace (MvPolynomial.C a) w)) ''
                      (S0 : Set (Fin (n + t)))))
                  {fun _ => MvPolynomial.C b} 1 :=
                Synthesis.arith_const b
              have hcomb := hbase.comp hc
              refine hcomb.mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _
                  right
                  simp [OracleProgram.trace_snoc_last]
                · intro w' hw
                  left
                  refine ⟨w', by simpa [S0] using hw, by simp [OracleProgram.trace_snoc_castSucc]⟩
              · simp only [OracleProgram.opCount, OracleInstr.cost]
                omega
          | oracle args =>
              have hbase := ih S0
              have hc : Synthesis
                  (arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K))
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace (MvPolynomial.C a) w)) ''
                      (S0 : Set (Fin (n + t)))))
                  {fun _ => MvPolynomial.C a} 1 :=
                Synthesis.arith_const a
              have hcomb := hbase.comp hc
              refine hcomb.mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _
                  right
                  simp [OracleProgram.trace_snoc_last]
                · intro w' hw
                  left
                  refine ⟨w', by simpa [S0] using hw, by simp [OracleProgram.trace_snoc_castSucc]⟩
              · simp only [OracleProgram.opCount, OracleInstr.cost]
                omega
        · refine (ih S0).mono Set.Subset.rfl ?_ ?_
          · rintro _ ⟨w, hw, rfl⟩
            revert hw
            refine Fin.lastCases ?_ ?_ w
            · intro hw
              exact absurd hw hlast
            · intro w' hw
              exact ⟨w', by simpa [S0] using hw, by simp [OracleProgram.trace_snoc_castSucc]⟩
          · simp only [OracleProgram.opCount]
            omega
  have h1 := hsyn oc.prog {oc.out}
  rw [Finset.coe_singleton, Set.image_singleton, Finset.card_singleton] at h1
  obtain ⟨c, hc, hsize⟩ := h1.exists_circuit_polynomial
  refine ⟨c, ?_, ?_⟩
  · rw [hc, MvPolynomial.aeval_X_left_apply]
    rfl
  · unfold OracleCircuit.opCount at hcop
    omega

/-- If a `p`-family `f` $c$-reduces to a family of constant polynomials, then `f ∈ VP K`. -/
public theorem mem_VP_of_isCReduction_const {K : Type u} [CommSemiring K]
    {f g : PolynomialFamily K} (hf : f.IsPFamily) (hg : ∀ n, ∃ a : K, g.poly n = MvPolynomial.C a)
    (hred : IsCReduction f g) : f ∈ VP K := by
  obtain ⟨t, b, -, hb, hcomp⟩ := hred
  have hcirc : ∀ n, ∃ c : Circuit (arithSignature K) (f.vars n) 1,
      c.polynomial 0 = f.poly n ∧ c.size ≤ 2 * b n + 1 := fun n => by
    obtain ⟨a, ha⟩ := hg (t n)
    have hn := hcomp n
    rw [ha] at hn
    exact exists_circuit_of_oracleComputedWithin_const hn
  choose c hc hsize using hcirc
  have hb' : PolynomiallyBounded (fun n => 2 * b n + 1) :=
    ((PolynomiallyBounded.const 2).mul hb).add (PolynomiallyBounded.const 1)
  exact ⟨hf, c, hb'.mono_of_le hsize, hc⟩

/-! ### Lagrange homogenization of homogeneous components -/

/-- The family of homogeneous components `(f_n^{(δ_n)})` extracted from a polynomial family `f`. -/
@[expose] public noncomputable def homogeneousComponentFamily {K : Type u} [CommSemiring K]
    (δ : ℕ → ℕ) (f : PolynomialFamily K) : PolynomialFamily K where
  vars n := f.vars n
  poly n := MvPolynomial.homogeneousComponent (δ n) (f.poly n)

private theorem aeval_C_mul_X_of_isHomogeneous {K : Type u} [CommSemiring K] {n k : ℕ}
    {h : MvPolynomial (Fin n) K} (hh : h.IsHomogeneous k) (t : K) :
    MvPolynomial.aeval (fun i => MvPolynomial.C t * MvPolynomial.X i) h =
      MvPolynomial.C (t ^ k) * h := by
  conv_lhs => rw [h.as_sum]
  rw [map_sum]
  conv_rhs => rw [h.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = k := by
    have := hh (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, mul_pow, ← map_pow]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Scaling every indeterminate by `t` expands as `∑_{k ≤ deg f} t^k f^{(k)}`. -/
public theorem aeval_C_mul_X_eq_sum_homogeneousComponent {K : Type u} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (t : K) :
    MvPolynomial.aeval (fun i => MvPolynomial.C t * MvPolynomial.X i) f =
      ∑ k ∈ Finset.range (f.totalDegree + 1),
        MvPolynomial.C (t ^ k) * MvPolynomial.homogeneousComponent k f := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact aeval_C_mul_X_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous k f) t

/-- Univariate Lagrange basis polynomial `L_j(T) = ∏_{r ≠ j} (T - a_r) / (a_j - a_r)`. -/
public noncomputable def lagrangeBasis {K : Type u} [Field K] {d : ℕ}
    (a : Fin (d + 1) → K) (j : Fin (d + 1)) : Polynomial K :=
  ∏ r ∈ Finset.univ.erase j,
    Polynomial.C ((a j - a r)⁻¹) * (Polynomial.X - Polynomial.C (a r))

private theorem lagrangeBasis_eval_self {K : Type u} [Field K] {d : ℕ}
    {a : Fin (d + 1) → K} (ha : Function.Injective a) (j : Fin (d + 1)) :
    (lagrangeBasis a j).eval (a j) = 1 := by
  rw [lagrangeBasis, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun r hr => ?_
  have hne : a j - a r ≠ 0 := sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hr) (ha h).symm
  simp [inv_mul_cancel₀ hne]

private theorem lagrangeBasis_eval_ne {K : Type u} [Field K] {d : ℕ}
    (a : Fin (d + 1) → K) {i j : Fin (d + 1)} (hij : i ≠ j) :
    (lagrangeBasis a j).eval (a i) = 0 := by
  rw [lagrangeBasis, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩) ?_
  simp

private theorem natDegree_lagrangeBasis_le {K : Type u} [Field K] {d : ℕ}
    (a : Fin (d + 1) → K) (j : Fin (d + 1)) :
    (lagrangeBasis a j).natDegree ≤ d := by
  rw [lagrangeBasis]
  have h1 : (∏ r ∈ Finset.univ.erase j,
      Polynomial.C ((a j - a r)⁻¹) * (Polynomial.X - Polynomial.C (a r))).natDegree ≤
      ∑ r ∈ Finset.univ.erase j,
        (Polynomial.C ((a j - a r)⁻¹) * (Polynomial.X - Polynomial.C (a r))).natDegree :=
    Polynomial.natDegree_prod_le (Finset.univ.erase j)
      (fun r => Polynomial.C ((a j - a r)⁻¹) * (Polynomial.X - Polynomial.C (a r)))
  have h2 : ∑ r ∈ Finset.univ.erase j,
      (Polynomial.C ((a j - a r)⁻¹) * (Polynomial.X - Polynomial.C (a r))).natDegree ≤
      ∑ _r ∈ Finset.univ.erase j, (1 : ℕ) :=
    Finset.sum_le_sum fun r _ =>
      (Polynomial.natDegree_C_mul_le ((a j - a r)⁻¹) (Polynomial.X - Polynomial.C (a r))).trans
        (Polynomial.natDegree_X_sub_C (a r)).le
  have h3 : ∑ _r ∈ Finset.univ.erase j, (1 : ℕ) = d := by
    rw [Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin, Nat.add_sub_cancel]
  exact h1.trans (h2.trans h3.le)

private theorem sum_pow_mul_lagrangeBasis {K : Type u} [Field K] {d : ℕ}
    {a : Fin (d + 1) → K} (ha : Function.Injective a) {k : ℕ} (hk : k ≤ d) :
    ∑ j : Fin (d + 1), Polynomial.C (a j ^ k) * lagrangeBasis a j = Polynomial.X ^ k := by
  classical
  let P : Polynomial K :=
    (∑ j : Fin (d + 1), Polynomial.C (a j ^ k) * lagrangeBasis a j) - Polynomial.X ^ k
  suffices hP : P = 0 from sub_eq_zero.1 hP
  by_contra hne
  have hdeg : P.natDegree ≤ d := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sum_le _ _).trans ?_
      refine Finset.sup_le fun j _ => ?_
      exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_lagrangeBasis_le a j)
    · rw [Polynomial.natDegree_X_pow]
      exact hk
  have hsub : Finset.univ.image a ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    have hev : P.eval (a i) =
        (∑ j : Fin (d + 1), a j ^ k * (lagrangeBasis a j).eval (a i)) - a i ^ k := by
      dsimp only [P]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        ← Polynomial.coe_evalRingHom, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by
        simp [Polynomial.coe_evalRingHom]
    rw [hev, Finset.sum_eq_single i]
    · rw [lagrangeBasis_eval_self ha i, mul_one, sub_self]
    · intro j _ hji; rw [lagrangeBasis_eval_ne a hji.symm, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hcard : d + 1 ≤ P.natDegree := by
    calc d + 1 = (Finset.univ : Finset (Fin (d + 1))).card := by simp
      _ = (Finset.univ.image a).card := (Finset.card_image_of_injective _ ha).symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
  omega

/-- Homogeneous component `f^{(δ)}` expressed as a `K`-linear combination of scaled evaluations
`f(a_j X)` at `deg f + 1` distinct points `a_0, ..., a_d`. -/
public theorem homogeneousComponent_eq_sum_aeval {K : Type u} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) {a : Fin (f.totalDegree + 1) → K}
    (ha : Function.Injective a) (δ : ℕ) :
    MvPolynomial.homogeneousComponent δ f =
      ∑ j : Fin (f.totalDegree + 1),
        MvPolynomial.C ((lagrangeBasis a j).coeff δ) *
          MvPolynomial.aeval (fun i => MvPolynomial.C (a j) * MvPolynomial.X i) f := by
  simp_rw [aeval_C_mul_X_eq_sum_homogeneousComponent, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ k ∈ Finset.range (f.totalDegree + 1),
      (∑ j : Fin (f.totalDegree + 1),
        MvPolynomial.C ((lagrangeBasis a j).coeff δ) *
          (MvPolynomial.C (a j ^ k) * MvPolynomial.homogeneousComponent k f)) =
      (if k = δ then MvPolynomial.homogeneousComponent k f else 0) := by
    intro k hk
    have hkle : k ≤ f.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hcoeff : ∑ j : Fin (f.totalDegree + 1),
        (lagrangeBasis a j).coeff δ * a j ^ k = if k = δ then 1 else 0 := by
      have h := congrArg (fun p : Polynomial K => Polynomial.lcoeff K δ p)
        (sum_pow_mul_lagrangeBasis ha hkle)
      simp only [map_sum, Polynomial.lcoeff_apply, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow] at h
      simpa [mul_comm, eq_comm] using h
    calc ∑ j : Fin (f.totalDegree + 1),
            MvPolynomial.C ((lagrangeBasis a j).coeff δ) *
              (MvPolynomial.C (a j ^ k) * MvPolynomial.homogeneousComponent k f)
        = (∑ j : Fin (f.totalDegree + 1),
            MvPolynomial.C ((lagrangeBasis a j).coeff δ * a j ^ k)) *
            MvPolynomial.homogeneousComponent k f := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, mul_assoc]
      _ = MvPolynomial.C (∑ j : Fin (f.totalDegree + 1),
            (lagrangeBasis a j).coeff δ * a j ^ k) *
            MvPolynomial.homogeneousComponent k f := by
          rw [map_sum]
      _ = if k = δ then MvPolynomial.homogeneousComponent k f else 0 := by
          rw [hcoeff]
          split_ifs <;> simp
  rw [Finset.sum_congr rfl hinner]
  by_cases hδ : δ ≤ f.totalDegree
  · rw [Finset.sum_eq_single δ]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hδ)) h
  · rw [Finset.sum_eq_zero]
    · exact MvPolynomial.homogeneousComponent_eq_zero δ f (by omega)
    · intro k hk
      have hkle : k ≤ f.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hne : k ≠ δ := by omega
      simp [hne]

/-- Helper: extend an oracle program with `n` wires holding `C a * X i` for `i : Fin n`. -/
private theorem build_scaled_wires {K : Type u} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (a : K) :
    ∀ {s₀ : ℕ} (base : OracleProgram K n n s₀) (k : ℕ) (hk : k ≤ n),
      ∃ (s' : ℕ) (q : OracleProgram K n n (s₀ + s')) (wires : Fin k → Fin (n + (s₀ + s'))),
        q.opCount ≤ base.opCount + k ∧
        (∀ w : Fin (n + s₀), q.trace f (w.castLE (by omega)) = base.trace f w) ∧
        (∀ i : Fin k, q.trace f (wires i) = MvPolynomial.C a * MvPolynomial.X ⟨i.1, by omega⟩) := by
  intro s₀ base k hk
  induction k with
  | zero =>
      exact ⟨0, base, Fin.elim0, by simp, fun _ => rfl, fun i => Fin.elim0 i⟩
  | succ k ih =>
      obtain ⟨s', q, wires, hcnt, hbase, hw⟩ := ih (by omega)
      let q1 := q.snoc (.const a)
      let wA : Fin (n + (s₀ + s' + 1)) := Fin.last (n + (s₀ + s'))
      let wX : Fin (n + (s₀ + s' + 1)) :=
        (⟨k, by omega⟩ : Fin n).castLE (Nat.le_add_right n (s₀ + s' + 1))
      let q2 := q1.snoc (.mul wA wX)
      let wires' : Fin (k + 1) → Fin (n + (s₀ + (s' + 2))) :=
        Fin.snoc (fun i => (wires i).castLE (by omega)) (Fin.last (n + (s₀ + s' + 1)))
      refine ⟨s' + 2, q2, wires', ?_, ?_, ?_⟩
      · simp only [q2, q1, OracleProgram.opCount_snoc, OracleInstr.cost_mul,
          OracleInstr.cost_const]
        omega
      · intro w
        have h1 : (w.castLE (by omega) : Fin (n + (s₀ + (s' + 2)))) =
            ((w.castLE (by omega : n + s₀ ≤ n + (s₀ + s'))).castSucc).castSucc := by ext; rfl
        rw [h1]
        simp only [q2, q1, OracleProgram.trace_snoc_castSucc, hbase w]
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp only [wires', Fin.snoc_last, q2, OracleProgram.trace_snoc_last]
          have hA : q1.trace f wA = MvPolynomial.C a := by simp [q1, wA]
          have hX : q1.trace f wX = MvPolynomial.X ⟨k, by omega⟩ := q1.trace_input f ⟨k, by omega⟩
          rw [hA, hX]
          rfl
        · intro i'
          have h1 : (wires' i'.castSucc : Fin (n + (s₀ + (s' + 2)))) =
              ((wires i').castSucc).castSucc := by
            simp only [wires', Fin.snoc_castSucc]; ext; rfl
          rw [h1]
          simp only [q2, q1, OracleProgram.trace_snoc_castSucc, hw i']
          rfl

/-- Helper: compute a finite linear combination `∑ j : Fin m, C (c j) * f(a j • X)` in at most
`m * (n + 3)` arithmetic and oracle gates. -/
private theorem build_scaled_oracle_sum {K : Type u} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (m : ℕ) (c a : Fin m → K) :
    OracleComputedWithin f
      (∑ j : Fin m, MvPolynomial.C (c j) *
        MvPolynomial.aeval (fun i => MvPolynomial.C (a j) * MvPolynomial.X i) f)
      (m * (n + 3)) := by
  induction m with
  | zero =>
      refine ⟨⟨1, OracleProgram.nil.snoc (.const 0), Fin.last n⟩, ?_, ?_⟩
      · simp
      · rw [OracleCircuit.eval_mk]
        exact (OracleProgram.trace_snoc_last f .nil (.const 0)).trans (by simp)
  | succ m ih =>
      obtain ⟨oc, hcop, hceval⟩ := ih (c ∘ Fin.castSucc) (a ∘ Fin.castSucc)
      obtain ⟨s', q, wires, hcnt, hbase, hw⟩ :=
        build_scaled_wires f (a (Fin.last m)) oc.prog n le_rfl
      let q1 := q.snoc (.oracle wires)
      let q2 := q1.snoc (.const (c (Fin.last m)))
      let wOrc : Fin (n + (oc.size + s' + 2)) := (Fin.last (n + (oc.size + s'))).castSucc
      let wC : Fin (n + (oc.size + s' + 2)) := Fin.last (n + (oc.size + s' + 1))
      let q3 := q2.snoc (.mul wC wOrc)
      let wOld : Fin (n + (oc.size + s' + 3)) := oc.out.castLE (by omega)
      let wNew : Fin (n + (oc.size + s' + 3)) := Fin.last (n + (oc.size + s' + 2))
      let q4 := q3.snoc (.add wOld wNew)
      refine ⟨⟨oc.size + s' + 4, q4, Fin.last (n + (oc.size + s' + 3))⟩, ?_, ?_⟩
      · simp only [OracleCircuit.opCount_mk, q4, q3, q2, q1, OracleProgram.opCount_snoc,
          OracleInstr.cost_add, OracleInstr.cost_mul, OracleInstr.cost_const,
          OracleInstr.cost_oracle]
        rw [OracleCircuit.opCount_eq_prog] at hcop
        have hmul : (m + 1) * (n + 3) = m * (n + 3) + (n + 3) := by ring
        omega
      · simp only [OracleCircuit.eval_mk, q4, OracleProgram.trace_snoc_last]
        have hOld : q3.trace f wOld =
            ∑ j : Fin m, MvPolynomial.C (c j.castSucc) *
              MvPolynomial.aeval (fun i => MvPolynomial.C (a j.castSucc) * MvPolynomial.X i) f := by
          have hcast : wOld =
              (((oc.out.castLE (by omega : n + oc.size ≤ n + (oc.size + s'))).castSucc).castSucc
                ).castSucc := by
            ext; rfl
          rw [hcast]
          simp only [q3, q2, q1, OracleProgram.trace_snoc_castSucc, hbase oc.out]
          exact hceval
        have hNew : q3.trace f wNew = MvPolynomial.C (c (Fin.last m)) *
            MvPolynomial.aeval (fun i => MvPolynomial.C (a (Fin.last m)) * MvPolynomial.X i) f := by
          simp only [wNew, q3, OracleProgram.trace_snoc_last]
          have hC : q2.trace f wC = MvPolynomial.C (c (Fin.last m)) := by simp [q2, wC]
          have hO : q2.trace f wOrc =
              MvPolynomial.aeval (fun i => MvPolynomial.C (a (Fin.last m)) *
                MvPolynomial.X i) f := by
            simp only [wOrc, q2, OracleProgram.trace_snoc_castSucc, q1,
              OracleProgram.trace_snoc_last]
            exact congrArg (fun fn => MvPolynomial.aeval fn f) (funext fun i => hw i)
          rw [hC, hO]
        rw [hOld, hNew, Fin.sum_univ_castSucc]

/-- Over any infinite field `K`, every homogeneous component `f^{(δ)}` of an `n`-variate
polynomial `f` is computed by an oracle circuit with oracle `f` using at most
`(n + 3) * (f.totalDegree + 1)` arithmetic and oracle operations. -/
public theorem oracleComputedWithin_homogeneousComponent {K : Type u} [Field K] [Infinite K]
    {n : ℕ} (f : MvPolynomial (Fin n) K) (δ : ℕ) :
    OracleComputedWithin f (MvPolynomial.homogeneousComponent δ f)
      ((f.totalDegree + 1) * (n + 3)) := by
  let emb : ℕ ↪ (Set.univ : Set K) := Set.infinite_univ.natEmbedding
  let a : Fin (f.totalDegree + 1) → K := fun j => (emb j.1).1
  have ha : Function.Injective a := fun i j hij => by
    have hsub : emb i.1 = emb j.1 := Subtype.ext hij
    exact Fin.ext (emb.injective hsub)
  rw [homogeneousComponent_eq_sum_aeval f ha δ]
  exact build_scaled_oracle_sum f (f.totalDegree + 1)
    (fun j => (lagrangeBasis a j).coeff δ) a

/-- Oracle complexity bound for homogeneous components over any infinite field `K`. -/
public theorem oracleComplexity_homogeneousComponent_le {K : Type u} [Field K] [Infinite K]
    {n : ℕ} (f : MvPolynomial (Fin n) K) (δ : ℕ) :
    oracleComplexity f (MvPolynomial.homogeneousComponent δ f) ≤
      (f.totalDegree + 1) * (n + 3) :=
  oracleComplexity_le_of_oracleComputedWithin (oracleComputedWithin_homogeneousComponent f δ)

/-- For any `p`-family `f` over an infinite field `K` and any sequence of target degrees `δ`,
the family of homogeneous components `(f_n^{(δ_n)})` `c`-reduces to `f`. -/
public theorem homogeneousComponentFamily_isCReduction {K : Type u} [Field K] [Infinite K]
    {f : PolynomialFamily K} (hf : f.IsPFamily) (δ : ℕ → ℕ) :
    IsCReduction (homogeneousComponentFamily δ f) f := by
  refine ⟨id, fun n => ((f.poly n).totalDegree + 1) * (f.vars n + 3),
    PolynomiallyBounded.id, ?_, fun n => oracleComputedWithin_homogeneousComponent (f.poly n) (δ n)⟩
  exact (hf.2.add (PolynomiallyBounded.const 1)).mul (hf.1.add (PolynomiallyBounded.const 3))

/-! ### Downward closure of `VP` under `c`-reductions -/

/-- Helper: any arithmetic `Program` on `m` inputs can be synthesized in `s_g` gates starting from
any set `base` containing the `m` input functions. -/
private theorem synthesis_program_of_inputs {K : Type u} [CommSemiring K] {m n : ℕ}
    (argFn : Fin m → (Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K)
    (base : Set ((Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K))
    (hbase : ∀ a : Fin m, argFn a ∈ base) :
    ∀ {s_g : ℕ} (prog : Program (arithSignature K) m s_g),
      Synthesis (arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K))
        base
        (Set.range fun w : Wire m s_g =>
          fun x => prog.trace (arithInterpretationWith K (MvPolynomial.C : K →
            MvPolynomial (Fin n) K))
            (fun a => argFn a x) w)
        s_g
  | _, .empty => by
      refine Synthesis.of_subset ?_
      rintro _ ⟨w, rfl⟩
      cases w with
      | input a => exact hbase a
      | gate g => exact Fin.elim0 g
  | _, .gate prog line => by
      let I := arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K)
      have ih := synthesis_program_of_inputs argFn base hbase prog
      let prevSet : Set ((Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K) :=
        Set.range fun w : Wire m _ =>
          fun x => prog.trace I (fun a => argFn a x) w
      have hstep : Synthesis I (base ∪ prevSet)
          {fun x => (prog.gate line).trace I (fun a => argFn a x) (.gate (Fin.last _))} 1 := by
        rcases line with ⟨op, wires⟩
        cases op with
        | add =>
            have h0 : (fun x => prog.trace I (fun a => argFn a x) (wires 0)) ∈
                base ∪ prevSet := Or.inr ⟨_, rfl⟩
            have h1 : (fun x => prog.trace I (fun a => argFn a x) (wires 1)) ∈
                base ∪ prevSet := Or.inr ⟨_, rfl⟩
            convert Synthesis.arith_add h0 h1 using 1
            ext f
            simp only [Set.mem_singleton_iff]
            constructor <;> rintro rfl <;> funext x <;>
              simp [Line.eval, I, arithInterpretationWith, Program.trace]
        | mul =>
            have h0 : (fun x => prog.trace I (fun a => argFn a x) (wires 0)) ∈
                base ∪ prevSet := Or.inr ⟨_, rfl⟩
            have h1 : (fun x => prog.trace I (fun a => argFn a x) (wires 1)) ∈
                base ∪ prevSet := Or.inr ⟨_, rfl⟩
            convert Synthesis.arith_mul h0 h1 using 1
            ext f
            simp only [Set.mem_singleton_iff]
            constructor <;> rintro rfl <;> funext x <;>
              simp [Line.eval, I, arithInterpretationWith, Program.trace]
        | const c =>
            convert Synthesis.arith_const (K := K) (R := MvPolynomial (Fin n) K) c using 1
            ext f
            simp only [Set.mem_singleton_iff]
            constructor <;> rintro rfl <;> funext x <;>
              simp [Line.eval, I, arithInterpretationWith]
      refine (ih.comp hstep).mono Set.Subset.rfl ?_ le_rfl
      rintro _ ⟨w, rfl⟩
      cases w with
      | input a =>
          left; refine ⟨.input a, funext fun x => ?_⟩; simp
      | gate g =>
          refine Fin.lastCases ?_ ?_ g
          · right; rfl
          · intro g'; left
            refine ⟨.gate g', funext fun x => ?_⟩
            simp

/-- Replacing oracle calls by a standard arithmetic circuit of size `cg.size` turns an oracle
program of opCount `≤ s` into a standard arithmetic circuit of size
`≤ s * (2 + m + cg.size) + 1`. -/
public theorem exists_circuit_of_oracleComputedWithin_circuit {K : Type u} [CommSemiring K]
    {m n : ℕ} {g : MvPolynomial (Fin m) K} {f : MvPolynomial (Fin n) K} {s : ℕ}
    (cg : Circuit (arithSignature K) m 1) (hcg : cg.polynomial 0 = g)
    (h : OracleComputedWithin g f s) :
    ∃ c : Circuit (arithSignature K) n 1,
      c.polynomial 0 = f ∧ c.size ≤ s * (2 + m + cg.size) + 1 := by
  obtain ⟨oc, hcop, rfl⟩ := h
  let I := arithInterpretationWith K (MvPolynomial.C : K → MvPolynomial (Fin n) K)
  have hsyn : ∀ {t : ℕ} (p : OracleProgram K m n t) (S : Finset (Fin (n + t))),
      Synthesis I (inputs n)
        ((fun w => fun x : Fin n → MvPolynomial (Fin n) K =>
          MvPolynomial.aeval x (p.trace g w)) '' (S : Set (Fin (n + t))))
        (p.opCount * (2 + m + cg.size) + S.card) := by
    intro t p
    induction p with
    | nil =>
        intro S
        refine (Synthesis.of_subset (s := inputs n) ?_).mono Set.Subset.rfl Set.Subset.rfl
          (Nat.zero_le _)
        rintro _ ⟨w, -, rfl⟩
        refine ⟨w, funext fun x => ?_⟩
        simp
    | @snoc t p instr ih =>
        intro S
        let S0 : Finset (Fin (n + t)) := S.preimage Fin.castSucc (Fin.castSucc_injective _).injOn
        have hcard : S0.card ≤ S.card :=
          Finset.card_le_card_of_injOn Fin.castSucc (fun w hw => by simpa [S0] using hw)
            (Fin.castSucc_injective _).injOn
        by_cases hlast : Fin.last (n + t) ∈ S
        · have hcard_lt : S0.card + 1 = S.card := by
            have hdisj : Disjoint (S0.image Fin.castSucc) {Fin.last (n + t)} := by
              rw [Finset.disjoint_singleton_right, Finset.mem_image]
              rintro ⟨w, -, hw⟩
              exact Fin.castSucc_ne_last w hw
            have hunion : S0.image Fin.castSucc ∪ {Fin.last (n + t)} = S := by
              ext w
              simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, S0,
                Finset.mem_preimage]
              refine Fin.lastCases ?_ ?_ w
              · simp [hlast]
              · intro w'; simp [Fin.castSucc_ne_last]
            rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
              Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
          cases instr with
          | add i j =>
              let S' := insert i (insert j S0)
              have hS' : S'.card ≤ S0.card + 2 :=
                (Finset.card_insert_le _ _).trans
                  (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
              have hbase := ih S'
              have hadd : Synthesis I
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace g w)) '' (S' : Set (Fin (n + t)))))
                  {fun x => MvPolynomial.aeval x (p.trace g i) +
                    MvPolynomial.aeval x (p.trace g j)} 1 :=
                Synthesis.arith_add
                  (Or.inr ⟨i, by simp [S'], rfl⟩)
                  (Or.inr ⟨j, by simp [S'], rfl⟩)
              refine (hbase.comp hadd).mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _; right; simp [OracleProgram.trace_snoc_last]
                · intro w' hw; left
                  exact ⟨w', by simp [S', show w' ∈ S0 by simpa [S0] using hw],
                    by simp [OracleProgram.trace_snoc_castSucc]⟩
              · simp only [OracleProgram.opCount_snoc, OracleInstr.cost_add]
                nlinarith
          | mul i j =>
              let S' := insert i (insert j S0)
              have hS' : S'.card ≤ S0.card + 2 :=
                (Finset.card_insert_le _ _).trans
                  (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
              have hbase := ih S'
              have hmul : Synthesis I
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace g w)) '' (S' : Set (Fin (n + t)))))
                  {fun x => MvPolynomial.aeval x (p.trace g i) *
                    MvPolynomial.aeval x (p.trace g j)} 1 :=
                Synthesis.arith_mul
                  (Or.inr ⟨i, by simp [S'], rfl⟩)
                  (Or.inr ⟨j, by simp [S'], rfl⟩)
              refine (hbase.comp hmul).mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _; right; simp [OracleProgram.trace_snoc_last]
                · intro w' hw; left
                  exact ⟨w', by simp [S', show w' ∈ S0 by simpa [S0] using hw],
                    by simp [OracleProgram.trace_snoc_castSucc]⟩
              · simp only [OracleProgram.opCount_snoc, OracleInstr.cost_mul]
                nlinarith
          | const b =>
              have hbase := ih S0
              have hc : Synthesis I
                  (inputs n ∪
                    ((fun w x => MvPolynomial.aeval x (p.trace g w)) '' (S0 : Set (Fin (n + t)))))
                  {fun _ => MvPolynomial.C b} 1 :=
                Synthesis.arith_const b
              refine (hbase.comp hc).mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _; right; simp [OracleProgram.trace_snoc_last]
                · intro w' hw; left
                  exact ⟨w', by simpa [S0] using hw, by simp [OracleProgram.trace_snoc_castSucc]⟩
              · simp only [OracleProgram.opCount_snoc, OracleInstr.cost_const, add_zero]
                omega
          | oracle args =>
              let S' : Finset (Fin (n + t)) := S0 ∪ Finset.univ.image args
              have hS' : S'.card ≤ S0.card + m := by
                refine (Finset.card_union_le _ _).trans ?_
                have : (Finset.univ.image args).card ≤ m :=
                  Finset.card_image_le.trans (by simp)
                omega
              have hbase := ih S'
              let argFn : Fin m → (Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K :=
                fun a x => MvPolynomial.aeval x (p.trace g (args a))
              have hprog := synthesis_program_of_inputs argFn
                (inputs n ∪
                  ((fun w x => MvPolynomial.aeval x (p.trace g w)) '' (S' : Set (Fin (n + t)))))
                (fun a => Or.inr ⟨args a, by simp [S'], rfl⟩)
                cg.program
              refine (hbase.comp hprog).mono Set.Subset.rfl ?_ ?_
              · rintro _ ⟨w, hw, rfl⟩
                revert hw
                refine Fin.lastCases ?_ ?_ w
                · intro _
                  right
                  refine ⟨cg.outputs 0, funext fun x => ?_⟩
                  change cg.program.trace I (fun a => argFn a x) (cg.outputs 0) =
                    MvPolynomial.aeval x ((p.snoc (.oracle args)).trace g (Fin.last (n + t)))
                  rw [OracleProgram.trace_snoc_last]
                  have hhom : (MvPolynomial.aeval x).comp
                      (MvPolynomial.aeval (fun a => p.trace g (args a))) =
                      MvPolynomial.aeval (fun a => argFn a x) := by
                    apply MvPolynomial.algHom_ext; intro a; simp [argFn]
                  have hval : MvPolynomial.aeval x
                      (MvPolynomial.aeval (fun a => p.trace g (args a)) g) =
                      MvPolynomial.aeval (fun a => argFn a x) g :=
                    AlgHom.congr_fun hhom g
                  rw [hval, ← hcg]
                  have hmap : cg.program.trace I (fun a => argFn a x) (cg.outputs 0) =
                      MvPolynomial.aeval (fun a => argFn a x) (cg.polynomial 0) := by
                    have hph := congrFun (Circuit.map_eval (c := cg)
                      (i₁ := arithInterpretationWith K (MvPolynomial.C : K →
                        MvPolynomial (Fin m) K))
                      (i₂ := I)
                      ⟨MvPolynomial.aeval (fun a => argFn a x),
                        fun op args' => by cases op <;> simp [I, arithInterpretationWith]⟩
                      MvPolynomial.X) 0
                    simpa [Circuit.polynomial, Circuit.eval, I, Function.comp_def] using hph.symm
                  exact hmap
                · intro w' hw
                  left
                  exact ⟨w', by simp [S', show w' ∈ S0 by simpa [S0] using hw],
                    by simp [OracleProgram.trace_snoc_castSucc]⟩
              · simp only [OracleProgram.opCount_snoc, OracleInstr.cost_oracle]
                nlinarith
        · refine (ih S0).mono Set.Subset.rfl ?_ ?_
          · rintro _ ⟨w, hw, rfl⟩
            revert hw
            refine Fin.lastCases ?_ ?_ w
            · intro hw; exact absurd hw hlast
            · intro w' hw
              exact ⟨w', by simpa [S0] using hw, by simp [OracleProgram.trace_snoc_castSucc]⟩
          · simp only [OracleProgram.opCount_snoc]
            nlinarith
  have h1 := hsyn oc.prog {oc.out}
  rw [Finset.coe_singleton, Set.image_singleton, Finset.card_singleton] at h1
  obtain ⟨c, hc, hsize⟩ := h1.exists_circuit_polynomial
  refine ⟨c, ?_, ?_⟩
  · rw [hc, MvPolynomial.aeval_X_left_apply]; rfl
  · rw [OracleCircuit.opCount_eq_prog] at hcop
    nlinarith

/-- **`VP K` is closed downward under `c`-reductions**: if `f` is a `p`-family, `g ∈ VP K`, and
`IsCReduction f g`, then `f ∈ VP K`. -/
public theorem mem_VP_of_isCReduction {K : Type u} [CommSemiring K]
    {f g : PolynomialFamily K} (hf : f.IsPFamily) (hg : g ∈ VP K) (hred : IsCReduction f g) :
    f ∈ VP K := by
  obtain ⟨t, b, ht, hb, hcomp⟩ := hred
  obtain ⟨hg_pf, cg, hcg_sz, hcg_poly⟩ := hg
  have hex : ∀ n, ∃ c : Circuit (arithSignature K) (f.vars n) 1,
      c.polynomial 0 = f.poly n ∧
      c.size ≤ b n * (2 + g.vars (t n) + (cg (t n)).size) + 1 := fun n =>
    exists_circuit_of_oracleComputedWithin_circuit (cg (t n)) (hcg_poly (t n)) (hcomp n)
  choose c hc hsize using hex
  refine ⟨hf, c, ?_, hc⟩
  have hpoly : PolynomiallyBounded (fun n => b n * (2 + g.vars (t n) + (cg (t n)).size) + 1) :=
    (hb.mul (((PolynomiallyBounded.const 2).add (hg_pf.1.comp ht)).add
      (hcg_sz.comp ht))).add (PolynomiallyBounded.const 1)
  exact hpoly.mono_of_le hsize

end CslibFrontier.Computability.Circuit.Arithmetic
