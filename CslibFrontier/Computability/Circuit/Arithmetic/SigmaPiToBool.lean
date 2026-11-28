module

public import CslibFrontier.Computability.Circuit.Arithmetic.SPCircuit
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Computability.Circuit.Pi

import CslibFrontier.Computability.Circuit.CompositionDepth
import Mathlib.Tactic.Linarith

/-!
# Unweighted Natural-Number Sigma-Pi to Unbounded Boolean Circuit Compilation

Compiles any unweighted natural-number arithmetic circuit of unbounded fan-in
(`Cslib.Circuits.Arithmetic.SPCircuit ℕ m`) into an unbounded fan-in Boolean `{AND, OR, NOT}`
circuit (`Cslib.Circuits.Circuit Cslib.Circuits.Boolean.Unbounded.signature m 1`) of size
`2 + addCount + mulCount` and `andOrCost` depth at most `arithDepth + 1` whose output is `true`
iff the computed polynomial evaluates to a positive natural number on `{0, 1}`-embedded Boolean
inputs. Also provides a zero-`andOrCost`-depth input-duplication and literal-negation layer.

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.sigmaPiArithCost`: unit cost for addition and
  multiplication gates, zero for constants.
* `CslibFrontier.Computability.Circuit.Arithmetic.spCircuitArithDepth`,
  `CslibFrontier.Computability.Circuit.Arithmetic.spCircuitAddCount`,
  `CslibFrontier.Computability.Circuit.Arithmetic.spCircuitMulCount`,
  `CslibFrontier.Computability.Circuit.Arithmetic.spCircuitUnweighted`: arithmetic depth, gate
  counts, and unit-weight predicate for unbounded fan-in arithmetic circuits.
* `CslibFrontier.Computability.Circuit.Arithmetic.boolToNat`,
  `CslibFrontier.Computability.Circuit.Arithmetic.boolInputs`: `{false, true} → {0, 1}` embedding
  and literal vector `(x₁, …, xₙ, ¬x₁, …, ¬xₙ)`.
* `CslibFrontier.Computability.Circuit.Arithmetic.spCircuitNatToBool`: compiler from unweighted
  `SPCircuit ℕ m` to unbounded fan-in Boolean circuits with constant deduplication.
* `CslibFrontier.Computability.Circuit.Arithmetic.dupAndNotCircuit`: zero-`andOrCost`-depth
  literal preparation circuit.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.spCircuitNatToBool_spec`: exact size,
  `andOrCost` depth bound, and positivity equivalence of `spCircuitNatToBool`.
* `CslibFrontier.Computability.Circuit.Arithmetic.dupAndNotCircuit_spec`: size, depth, and
  literal-evaluation specification of `dupAndNotCircuit`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.Unbounded MvPolynomial
open scoped BigOperators

universe u

section Metrics

variable {K : Type u} {n m : ℕ}

/-- Arithmetic depth cost of a `SigmaPiOp`: `+` and `×` cost `1`; constants cost `0`. -/
@[expose] def sigmaPiArithCost : SigmaPiOp K → ℕ
  | .add _ _ => 1
  | .mul _ => 1
  | .const _ => 0

/-- Boolean indicator of a `SigmaPiOp.add` gate. -/
@[expose] def sigmaPiOpIsAdd : SigmaPiOp K → Bool
  | .add _ _ => true
  | _ => false

/-- Boolean indicator of a `SigmaPiOp.mul` gate. -/
@[expose] def sigmaPiOpIsMul : SigmaPiOp K → Bool
  | .mul _ => true
  | _ => false

/-- Arithmetic depth of an unbounded fan-in arithmetic circuit
(inputs and constants have depth `0`). -/
@[expose] def spCircuitArithDepth (C : Circuit (sigmaPiSignature K) n m) : ℕ :=
  C.depthWith sigmaPiArithCost

/-- Number of addition gates in a `Circuit (sigmaPiSignature K) n m`. -/
@[expose] def spCircuitAddCount (C : Circuit (sigmaPiSignature K) n m) : ℕ :=
  (Finset.univ.filter fun k : Fin C.size => sigmaPiOpIsAdd (C.program.lines k).op).card

/-- Number of multiplication gates in a `Circuit (sigmaPiSignature K) n m`. -/
@[expose] def spCircuitMulCount (C : Circuit (sigmaPiSignature K) n m) : ℕ :=
  (Finset.univ.filter fun k : Fin C.size => sigmaPiOpIsMul (C.program.lines k).op).card

/-- Every addition gate of `C` is unweighted (all edge weights are `1`). -/
@[expose] def spCircuitUnweighted [One K] (C : Circuit (sigmaPiSignature K) n m) : Prop :=
  ∀ (k : Fin C.size) (r : ℕ) (c : Fin r → K),
    (C.program.lines k).op = .add r c → ∀ j, c j = 1

end Metrics

/-- Canonical embedding of `Bool` into `ℕ` (`false ↦ 0`, `true ↦ 1`). -/
@[expose] def boolToNat (b : Bool) : ℕ :=
  if b then 1 else 0

/-- Literal vector `(x₁, …, xₙ, ¬x₁, …, ¬xₙ)` embedded into `ℕ`. -/
@[expose] def boolInputs {n : ℕ} (x : Fin n → Bool) : Fin (2 * n) → ℕ :=
  fun j => if h : j.1 < n then boolToNat (x ⟨j.1, h⟩) else boolToNat (!(x ⟨j.1 - n, by omega⟩))

/-- Compiled unbounded Boolean program with constant-0/1 deduplication and wire translation. -/
private structure BoolCompiled (m g : ℕ) where
  gates : ℕ
  ge_two : 2 ≤ gates
  prog : Program Unbounded.signature m gates
  mapWire : Wire m g → Wire m gates

/-- Base 2-gate Boolean program holding `.or 0` (`false`, gate 0) and `.and 0` (`true`, gate 1). -/
private def baseBoolProg (m : ℕ) : Program Unbounded.signature m 2 :=
  ((Program.empty (σ := Unbounded.signature)).gate ⟨Unbounded.Op.or 0, Fin.elim0⟩).gate
    ⟨Unbounded.Op.and 0, Fin.elim0⟩

/-- Translate a `Program (sigmaPiSignature ℕ)` to an unbounded Boolean program, deduplicating all
`.const` gates onto the two base constant gates `0` (`false`) and `1` (`true`). -/
private def compileNatProg {m : ℕ} : {g : ℕ} → Program (sigmaPiSignature ℕ) m g → BoolCompiled m g
  | _, .empty =>
    { gates := 2
      ge_two := le_rfl
      prog := baseBoolProg m
      mapWire := fun
        | .input i => .input i
        | .gate k => k.elim0 }
  | _, .gate P ⟨op, wires⟩ =>
    let bc := compileNatProg P
    match op with
    | .const a =>
      let wNew : Wire m bc.gates :=
        if a = 0 then .gate ⟨0, lt_of_lt_of_le (by decide) bc.ge_two⟩
        else .gate ⟨1, lt_of_lt_of_le (by decide) bc.ge_two⟩
      { gates := bc.gates
        ge_two := bc.ge_two
        prog := bc.prog
        mapWire := fun
          | .input i => .input i
          | .gate k => Fin.lastCases wNew (fun j => bc.mapWire (.gate j)) k }
    | .add r _ =>
      let lineB : Line Unbounded.signature m bc.gates :=
        ⟨Unbounded.Op.or r, fun a => bc.mapWire (wires a)⟩
      { gates := bc.gates + 1
        ge_two := Nat.le_succ_of_le bc.ge_two
        prog := bc.prog.gate lineB
        mapWire := fun
          | .input i => .input i
          | .gate k => Fin.lastCases (.gate (Fin.last bc.gates))
              (fun j => (bc.mapWire (.gate j)).castSucc) k }
    | .mul r =>
      let lineB : Line Unbounded.signature m bc.gates :=
        ⟨Unbounded.Op.and r, fun a => bc.mapWire (wires a)⟩
      { gates := bc.gates + 1
        ge_two := Nat.le_succ_of_le bc.ge_two
        prog := bc.prog.gate lineB
        mapWire := fun
          | .input i => .input i
          | .gate k => Fin.lastCases (.gate (Fin.last bc.gates))
              (fun j => (bc.mapWire (.gate j)).castSucc) k }

/-- Helper counting addition and multiplication lines in a `Program (sigmaPiSignature ℕ)`. -/
private def progArithCount {m : ℕ} : {g : ℕ} → Program (sigmaPiSignature ℕ) m g → ℕ
  | _, .empty => 0
  | _, .gate P line =>
    progArithCount P + match line.op with | .const _ => 0 | .add _ _ => 1 | .mul _ => 1

private lemma progArithCount_eq_add_mul {m g : ℕ} (P : Program (sigmaPiSignature ℕ) m g) :
    progArithCount P =
      (Finset.univ.filter fun k : Fin g => sigmaPiOpIsAdd (P.lines k).op).card +
      (Finset.univ.filter fun k : Fin g => sigmaPiOpIsMul (P.lines k).op).card := by
  induction P with
  | empty => simp [progArithCount]
  | gate P line ih =>
    rename_i g'
    have hadd : (Finset.univ.filter fun k : Fin (g' + 1) =>
          sigmaPiOpIsAdd ((P.gate line).lines k).op).card =
        (Finset.univ.filter fun k : Fin g' => sigmaPiOpIsAdd (P.lines k).op).card +
          if sigmaPiOpIsAdd line.op then 1 else 0 := by
      have hsum : ∀ {n} (f : Fin n → Bool),
          (Finset.univ.filter fun k : Fin n => f k = true).card =
            ∑ k : Fin n, if f k then 1 else 0 := fun f => by
        rw [Finset.card_filter]
      rw [hsum, hsum, Fin.sum_univ_castSucc]
      simp only [Program.lines_gate_castSucc, Line.mapWires_op, Program.lines_gate_last]
    have hmul : (Finset.univ.filter fun k : Fin (g' + 1) =>
          sigmaPiOpIsMul ((P.gate line).lines k).op).card =
        (Finset.univ.filter fun k : Fin g' => sigmaPiOpIsMul (P.lines k).op).card +
          if sigmaPiOpIsMul line.op then 1 else 0 := by
      have hsum : ∀ {n} (f : Fin n → Bool),
          (Finset.univ.filter fun k : Fin n => f k = true).card =
            ∑ k : Fin n, if f k then 1 else 0 := fun f => by
        rw [Finset.card_filter]
      rw [hsum, hsum, Fin.sum_univ_castSucc]
      simp only [Program.lines_gate_castSucc, Line.mapWires_op, Program.lines_gate_last]
    rw [hadd, hmul, progArithCount, ih]
    cases line.op <;> simp [sigmaPiOpIsAdd, sigmaPiOpIsMul] <;> omega

private lemma compileNatProg_spec {m g : ℕ} (P : Program (sigmaPiSignature ℕ) m g) :
    let bc := compileNatProg P
    ∃ h2 : 2 ≤ bc.gates,
      bc.gates = 2 + progArithCount P ∧
      (∀ x : Fin m → Bool,
        bc.prog.trace Unbounded.interpretation x (.gate ⟨0, by omega⟩) = false ∧
        bc.prog.trace Unbounded.interpretation x (.gate ⟨1, by omega⟩) = true) ∧
      (bc.prog.trace (depthInterpretation Unbounded.andOrCost) (fun _ => 0)
          (.gate ⟨0, by omega⟩) ≤ 1 ∧
        bc.prog.trace (depthInterpretation Unbounded.andOrCost) (fun _ => 0)
          (.gate ⟨1, by omega⟩) ≤ 1) ∧
      (∀ w : Wire m g,
        bc.prog.trace (depthInterpretation Unbounded.andOrCost) (fun _ => 0) (bc.mapWire w) ≤
          P.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0) w + 1) ∧
      ((∀ (k : Fin g) (r : ℕ) (cs : Fin r → ℕ),
          (P.lines k).op = .add r cs → ∀ j, cs j = 1) →
        ∀ (x : Fin m → Bool) (w : Wire m g),
          bc.prog.trace Unbounded.interpretation x (bc.mapWire w) = true ↔
            0 < MvPolynomial.eval (fun i => boolToNat (x i))
              (P.trace (sigmaPiInterpretationWith ℕ MvPolynomial.C) X w)) := by
  induction P with
  | empty =>
    refine ⟨le_rfl, rfl, fun x => ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun w => ?_, fun _ x w => ?_⟩
    · change Unbounded.interpretation (.or 0) Fin.elim0 = false
      simp
    · change Unbounded.interpretation (.and 0) Fin.elim0 = true
      simp
    · change depthInterpretation (σ := Unbounded.signature) Unbounded.andOrCost
        (Unbounded.Op.or 0) Fin.elim0 ≤ 1
      simp [depthInterpretation]
    · change depthInterpretation (σ := Unbounded.signature) Unbounded.andOrCost
        (Unbounded.Op.and 0) Fin.elim0 ≤ 1
      simp [depthInterpretation]
    · cases w with
      | input i => simp [compileNatProg, Program.trace_input]
      | gate k => exact k.elim0
    · cases w with
      | input i =>
        simp only [compileNatProg, Program.trace_input, MvPolynomial.eval_X, boolToNat]
        cases x i <;> simp
      | gate k => exact k.elim0
  | gate P line ih =>
    rename_i g'
    rcases ih with ⟨h2, hsz, hcval, hcdep, hdep, heval⟩
    rcases line with ⟨op, wires⟩
    cases op with
    | const a =>
      dsimp only [compileNatProg, progArithCount]
      refine ⟨h2, by omega, hcval, hcdep, fun w => ?_, fun hunw x w => ?_⟩
      · cases w with
        | input i => simp [Program.trace_input]
        | gate k =>
          induction k using Fin.lastCases with
          | cast j =>
            simp only [Fin.lastCases_castSucc]
            rw [show Wire.gate j.castSucc = (Wire.gate j).castSucc from rfl,
              Program.trace_gate_castSucc]
            exact hdep (.gate j)
          | last =>
            simp only [Fin.lastCases_last]
            split_ifs
            · exact hcdep.1.trans (Nat.le_add_left 1 _)
            · exact hcdep.2.trans (Nat.le_add_left 1 _)
      · have hunw' : ∀ (k : Fin g') (r : ℕ) (cs : Fin r → ℕ),
            (P.lines k).op = .add r cs → ∀ j, cs j = 1 := fun k r cs hop =>
          hunw k.castSucc r cs (by rw [Program.lines_gate_castSucc, Line.mapWires_op]; exact hop)
        cases w with
        | input i =>
          simp only [Program.trace_input, MvPolynomial.eval_X, boolToNat]
          cases x i <;> simp
        | gate k =>
          induction k using Fin.lastCases with
          | cast j =>
            simp only [Fin.lastCases_castSucc]
            rw [show Wire.gate j.castSucc = (Wire.gate j).castSucc from rfl,
              Program.trace_gate_castSucc]
            exact heval hunw' x (.gate j)
          | last =>
            rw [Program.trace_gate_last]
            dsimp only [Line.eval]
            rw [sigmaPiInterpretationWith_const, MvPolynomial.eval_C]
            simp only [Fin.lastCases_last]
            split_ifs with ha0
            · subst ha0
              rw [(hcval x).1]; simp
            · rw [(hcval x).2]
              exact ⟨fun _ => Nat.pos_of_ne_zero ha0, fun _ => rfl⟩
    | add r cs =>
      dsimp only [compileNatProg, progArithCount]
      refine ⟨Nat.le_succ_of_le h2, by omega, fun x => ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun w => ?_,
        fun hunw x w => ?_⟩
      · rw [show (Wire.gate (⟨0, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨0, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact (hcval x).1
      · rw [show (Wire.gate (⟨1, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨1, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact (hcval x).2
      · rw [show (Wire.gate (⟨0, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨0, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact hcdep.1
      · rw [show (Wire.gate (⟨1, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨1, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact hcdep.2
      · cases w with
        | input i => simp [Program.trace_input]
        | gate k =>
          induction k using Fin.lastCases with
          | cast j =>
            simp only [Fin.lastCases_castSucc]
            rw [show Wire.gate j.castSucc = (Wire.gate j).castSucc from rfl,
              Program.trace_gate_castSucc, Program.trace_gate_castSucc]
            exact hdep (.gate j)
          | last =>
            simp only [Fin.lastCases_last]
            rw [Program.trace_gate_last, Program.trace_gate_last]
            dsimp only [Line.eval, depthInterpretation]
            simp only [Fin.foldl_max_eq_max_sup, Nat.zero_max, andOrCost_or, sigmaPiArithCost]
            have hsup : (Finset.univ.sup fun a : Fin r =>
                (compileNatProg P).prog.trace (depthInterpretation Unbounded.andOrCost) (fun _ => 0)
                  ((compileNatProg P).mapWire (wires a))) ≤
                (Finset.univ.sup fun a : Fin r =>
                  P.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0) (wires a)) + 1 :=
              Finset.sup_le fun a _ =>
                (hdep (wires a)).trans (Nat.add_le_add_right
                  (Finset.le_sup (f := fun a : Fin r =>
                    P.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0) (wires a))
                    (Finset.mem_univ a)) 1)
            exact Nat.add_le_add_right hsup 1
      · have hunw' : ∀ (k : Fin g') (r' : ℕ) (cs' : Fin r' → ℕ),
            (P.lines k).op = .add r' cs' → ∀ j, cs' j = 1 := fun k r' cs' hop =>
          hunw k.castSucc r' cs' (by rw [Program.lines_gate_castSucc, Line.mapWires_op]; exact hop)
        have hcs1 : ∀ j : Fin r, cs j = 1 :=
          hunw (Fin.last g') r cs (by simp [Program.lines_gate_last])
        cases w with
        | input i =>
          simp only [Program.trace_input, MvPolynomial.eval_X, boolToNat]
          cases x i <;> simp
        | gate k =>
          induction k using Fin.lastCases with
          | cast j =>
            simp only [Fin.lastCases_castSucc]
            rw [show Wire.gate j.castSucc = (Wire.gate j).castSucc from rfl,
              Program.trace_gate_castSucc, Program.trace_gate_castSucc]
            exact heval hunw' x (.gate j)
          | last =>
            simp only [Fin.lastCases_last]
            rw [Program.trace_gate_last, Program.trace_gate_last]
            dsimp only [Line.eval]
            rw [interpretation_or, decide_eq_true_iff, sigmaPiInterpretationWith_add, map_sum]
            simp only [map_mul, MvPolynomial.eval_C, hcs1, one_mul]
            rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
            constructor
            · rintro ⟨a, ha⟩
              exact ⟨a, Finset.mem_univ a, (heval hunw' x (wires a)).mp ha⟩
            · rintro ⟨a, _, ha⟩
              exact ⟨a, (heval hunw' x (wires a)).mpr ha⟩
    | mul r =>
      dsimp only [compileNatProg, progArithCount]
      refine ⟨Nat.le_succ_of_le h2, by omega, fun x => ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun w => ?_,
        fun hunw x w => ?_⟩
      · rw [show (Wire.gate (⟨0, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨0, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact (hcval x).1
      · rw [show (Wire.gate (⟨1, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨1, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact (hcval x).2
      · rw [show (Wire.gate (⟨0, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨0, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact hcdep.1
      · rw [show (Wire.gate (⟨1, by omega⟩ : Fin ((compileNatProg P).gates + 1)) :
              Wire m ((compileNatProg P).gates + 1)) =
            (Wire.gate ⟨1, by omega⟩).castSucc from rfl, Program.trace_gate_castSucc]
        exact hcdep.2
      · cases w with
        | input i => simp [Program.trace_input]
        | gate k =>
          induction k using Fin.lastCases with
          | cast j =>
            simp only [Fin.lastCases_castSucc]
            rw [show Wire.gate j.castSucc = (Wire.gate j).castSucc from rfl,
              Program.trace_gate_castSucc, Program.trace_gate_castSucc]
            exact hdep (.gate j)
          | last =>
            simp only [Fin.lastCases_last]
            rw [Program.trace_gate_last, Program.trace_gate_last]
            dsimp only [Line.eval, depthInterpretation]
            simp only [Fin.foldl_max_eq_max_sup, Nat.zero_max, andOrCost_and, sigmaPiArithCost]
            have hsup : (Finset.univ.sup fun a : Fin r =>
                (compileNatProg P).prog.trace (depthInterpretation Unbounded.andOrCost) (fun _ => 0)
                  ((compileNatProg P).mapWire (wires a))) ≤
                (Finset.univ.sup fun a : Fin r =>
                  P.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0) (wires a)) + 1 :=
              Finset.sup_le fun a _ =>
                (hdep (wires a)).trans (Nat.add_le_add_right
                  (Finset.le_sup (f := fun a : Fin r =>
                    P.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0) (wires a))
                    (Finset.mem_univ a)) 1)
            exact Nat.add_le_add_right hsup 1
      · have hunw' : ∀ (k : Fin g') (r' : ℕ) (cs' : Fin r' → ℕ),
            (P.lines k).op = .add r' cs' → ∀ j, cs' j = 1 := fun k r' cs' hop =>
          hunw k.castSucc r' cs' (by rw [Program.lines_gate_castSucc, Line.mapWires_op]; exact hop)
        cases w with
        | input i =>
          simp only [Program.trace_input, MvPolynomial.eval_X, boolToNat]
          cases x i <;> simp
        | gate k =>
          induction k using Fin.lastCases with
          | cast j =>
            simp only [Fin.lastCases_castSucc]
            rw [show Wire.gate j.castSucc = (Wire.gate j).castSucc from rfl,
              Program.trace_gate_castSucc, Program.trace_gate_castSucc]
            exact heval hunw' x (.gate j)
          | last =>
            simp only [Fin.lastCases_last]
            rw [Program.trace_gate_last, Program.trace_gate_last]
            dsimp only [Line.eval]
            rw [interpretation_and, decide_eq_true_iff, sigmaPiInterpretationWith_mul, map_prod]
            simp only [Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff]
            constructor
            · intro h a _
              exact Nat.pos_iff_ne_zero.mp ((heval hunw' x (wires a)).mp (h a))
            · intro h a
              exact (heval hunw' x (wires a)).mpr
                (Nat.pos_iff_ne_zero.mpr (h a (Finset.mem_univ a)))

/-- Convert an arithmetic `SPCircuit ℕ m` into an unbounded fan-in Boolean circuit by replacing
additions with unbounded `OR`, multiplications with unbounded `AND`, and deduplicating zero and
nonzero constants onto `false` and `true`. -/
def spCircuitNatToBool {m : ℕ} (Γ : SPCircuit ℕ m) :
    Circuit Unbounded.signature m 1 :=
  let bc := compileNatProg Γ.program
  ⟨bc.prog, fun _ => bc.mapWire (Γ.outputs 0)⟩

/-- For any unweighted `SPCircuit ℕ m`, `spCircuitNatToBool Γ` has size
`2 + spCircuitAddCount Γ + spCircuitMulCount Γ`, `andOrCost` depth at most
`spCircuitArithDepth Γ + 1`, and outputs `true` on `x` iff
`0 < MvPolynomial.eval (fun i => boolToNat (x i)) Γ.polynomial`. -/
theorem spCircuitNatToBool_spec {m : ℕ} (Γ : SPCircuit ℕ m) (hunw : spCircuitUnweighted Γ) :
    (spCircuitNatToBool Γ).size = 2 + spCircuitAddCount Γ + spCircuitMulCount Γ ∧
    (spCircuitNatToBool Γ).depthWith Unbounded.andOrCost ≤ spCircuitArithDepth Γ + 1 ∧
    ∀ x : Fin m → Bool,
      ((spCircuitNatToBool Γ).eval Unbounded.interpretation x 0 = true) ↔
        0 < MvPolynomial.eval (fun i => boolToNat (x i)) Γ.polynomial := by
  rcases compileNatProg_spec Γ.program with ⟨_, hsz, _, _, hdep, heval⟩
  refine ⟨?_, ?_, fun x => ?_⟩
  · change (compileNatProg Γ.program).gates = _
    rw [hsz, progArithCount_eq_add_mul]
    simp only [spCircuitAddCount, spCircuitMulCount]; omega
  · rw [Circuit.depthWith_le_iff, spCircuitArithDepth]
    intro _
    change (compileNatProg Γ.program).prog.trace (depthInterpretation Unbounded.andOrCost)
        (fun _ => 0) ((compileNatProg Γ.program).mapWire (Γ.outputs 0)) ≤
      Γ.depthWith sigmaPiArithCost + 1
    have hw : Γ.program.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0) (Γ.outputs 0) ≤
        Γ.depthWith sigmaPiArithCost := by
      have htr : Γ.program.trace (depthInterpretation sigmaPiArithCost) (fun _ => 0)
            (Γ.outputs 0) =
          Γ.program.wireDepthsWith sigmaPiArithCost (Γ.outputs 0) := by
        cases Γ.outputs 0 <;> rfl
      rw [htr]
      exact Circuit.wireDepthsWith_outputs_le_depthWith sigmaPiArithCost Γ 0
    exact (hdep (Γ.outputs 0)).trans (Nat.add_le_add_right hw 1)
  · exact heval hunw x (Γ.outputs 0)

/-- Input-duplication and negation layer: maps `x : Fin n → Bool` to `(x, ¬x)` with `n` `NOT`
gates and zero `andOrCost` depth. -/
def dupAndNotCircuit (n : ℕ) : Circuit Unbounded.signature n (2 * n) :=
  Circuit.pi fun j : Fin (2 * n) =>
    if h : j.1 < n then
      Circuit.wiring Unbounded.signature (fun _ => ⟨j.1, h⟩)
    else
      Circuit.oneGate (σ := Unbounded.signature) .not (fun _ => ⟨j.1 - n, by omega⟩)

/-- Size, depth, and literal semantics of `dupAndNotCircuit`. -/
theorem dupAndNotCircuit_spec (n : ℕ) :
    (dupAndNotCircuit n).size ≤ 2 * n ∧
    (dupAndNotCircuit n).depthWith Unbounded.andOrCost ≤ 0 ∧
    ∀ (x : Fin n → Bool) (j : Fin (2 * n)),
      boolToNat ((dupAndNotCircuit n).eval Unbounded.interpretation x j) = boolInputs x j := by
  dsimp only [dupAndNotCircuit]
  refine ⟨?_, ?_, fun x j => ?_⟩
  · rw [Circuit.size_pi]
    calc ∑ j : Fin (2 * n),
            (if h : j.1 < n then Circuit.wiring Unbounded.signature (fun _ : Fin 1 => ⟨j.1, h⟩)
              else Circuit.oneGate (σ := Unbounded.signature) .not
                (fun _ => ⟨j.1 - n, by omega⟩)).size
        ≤ ∑ _j : Fin (2 * n), 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs <;> simp
      _ = 2 * n := by simp
  · refine Circuit.depthWith_pi_le (σ := Unbounded.signature) Unbounded.andOrCost _ fun j => ?_
    split_ifs
    · rw [Circuit.depthWith_wiring]
    · rw [Circuit.depthWith_oneGate]; rfl
  · rw [Circuit.eval_pi]
    dsimp only [boolInputs]
    split_ifs with h
    · simp [Circuit.eval_wiring]
    · simp [Circuit.eval_oneGate]

end CslibFrontier.Computability.Circuit.Arithmetic
