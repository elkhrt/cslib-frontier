module

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import CslibFrontier.Computability.Circuit.Quantum.Classical
public import CslibFrontier.Computability.Circuit.Quantum.Code
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Computability.Circuit.Quantum.Parallel
public import CslibFrontier.Computability.Circuit.Quantum.Uniform
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantum Circuits with Classical Boolean Oracles and Relativized EQP and BQP

This module defines polynomial-time uniform families of quantum circuits with coherent XOR queries
to a classical Boolean oracle `O : List Bool → Bool`, over the finite exact-inverse gate set
consisting of the Hadamard, NOT, CNOT, and Toffoli gates (`Cslib.Quantum.GateCode`), together with
the relativized complexity classes `EQPWithOracle` and `BQPWithOracle`.

Every gate in `BooleanOracleGateCode` — both elementary `GateCode` gates and coherent XOR oracle
queries — is its own inverse, so reversing the instruction list produces the exact inverse circuit
of the same size and query count (`BooleanOracleCircuit.eval_reverse_eval`). A coherent query into
a `|−⟩` phase ancilla implements a phase query `|a⟩ ↦ (-1)^{O(a)} |a⟩`
(`BooleanOracleGateCode.eval_phaseQuery_ket`).

## Main definitions

* `CslibFrontier.Quantum.BooleanOracleGateCode`: elementary `GateCode` gates and variable-length
  coherent XOR oracle query instructions.
* `CslibFrontier.Quantum.BooleanOracleCircuit`: lists of `BooleanOracleGateCode` instructions, with
  `toCircuit`, `queryCount`, and `gateCount`.
* `CslibFrontier.Quantum.UniformBooleanOracleCircuitFamily`: polynomial-time uniform families of
  well-formed quantum oracle circuits.
* `CslibFrontier.Complexity.EQPWithOracle`, `CslibFrontier.Complexity.BQPWithOracle`: exact and
  bounded-error quantum polynomial time relative to a classical Boolean oracle.

## Main results

* `CslibFrontier.Quantum.BooleanOracleGateCode.eval_toPlacedGate?_query_ket`: semantics of a
  coherent XOR query on computational basis states.
* `CslibFrontier.Quantum.BooleanOracleGateCode.eval_phaseQuery_ket`: phase-kickback implementation
  of a phase query using one XOR query and a `|−⟩` ancilla.
* `CslibFrontier.Quantum.BooleanOracleCircuit.eval_reverse_eval`: reversing a well-formed circuit
  computes its exact inverse.
* `CslibFrontier.Complexity.EQPWithOracle_subset_BQPWithOracle`: `EQP^O ⊆ BQP^O`.
* `CslibFrontier.Complexity.compl_mem_EQPWithOracle` and
  `CslibFrontier.Complexity.compl_mem_BQPWithOracle`:
  closure of `EQP^O` and `BQP^O` under complement.

-/

public section

namespace CslibFrontier

namespace Quantum

open Cslib.Quantum Finset Turing.MultiTapeTM

/-- A quantum oracle-circuit instruction over the finite gate set `{H, NOT, CNOT, Toffoli}` and
coherent XOR queries to a classical Boolean oracle `O : List Bool → Bool`. -/
inductive BooleanOracleGateCode where
  /-- An elementary Hadamard, NOT, CNOT, or Toffoli gate code. -/
  | gate (code : GateCode)
  /-- A coherent XOR query reading `addrs` (in order) and XORing `O(a)` into `target`. -/
  | query (addrs : List ℕ) (target : ℕ)
  deriving DecidableEq

namespace BooleanOracleGateCode

/-- Validity of an instruction on an `m`-qubit register: elementary gates satisfy
`GateCode.WellFormed`, and oracle queries act on distinct wires below `m`. -/
@[expose] def WellFormed (m : ℕ) : BooleanOracleGateCode → Prop
  | .gate g => g.WellFormed m
  | .query addrs target => (target :: addrs).Nodup ∧ ∀ w ∈ target :: addrs, w < m

@[simp] theorem wellFormed_gate (m : ℕ) (g : GateCode) :
    WellFormed m (.gate g) ↔ g.WellFormed m := Iff.rfl

/-- Characterization of `WellFormed` for a coherent XOR query instruction. -/
theorem wellFormed_query_iff (m : ℕ) (addrs : List ℕ) (target : ℕ) :
    WellFormed m (.query addrs target) ↔
      (target :: addrs).Nodup ∧ ∀ w ∈ target :: addrs, w < m := Iff.rfl

instance (m : ℕ) : DecidablePred (WellFormed m)
  | .gate _ => inferInstanceAs (Decidable (GateCode.WellFormed m _))
  | .query _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Whether an instruction is an oracle query. -/
@[expose] def isQuery : BooleanOracleGateCode → Bool
  | .gate _ => false
  | .query _ _ => true

@[simp] theorem isQuery_gate (g : GateCode) : isQuery (.gate g) = false := rfl

@[simp] theorem isQuery_query (addrs : List ℕ) (target : ℕ) :
    isQuery (.query addrs target) = true := rfl

/-- Shift all wire indices of an instruction upward by `o`. -/
@[expose] def shift (o : ℕ) : BooleanOracleGateCode → BooleanOracleGateCode
  | .gate g => .gate (GateCode.shift o g)
  | .query addrs target => .query (addrs.map (· + o)) (target + o)

/-- Wire embedding for a well-formed query instruction `(addrs, target)` on `m` qubits:
wires `0, …, addrs.length - 1` carry the query address and wire `addrs.length` is the target. -/
@[expose] def queryEmb {m : ℕ} {addrs : List ℕ} {target : ℕ}
    (h : WellFormed m (.query addrs target)) : Fin (addrs.length + 1) ↪ Fin m where
  toFun i :=
    if hi : i.1 < addrs.length then
      ⟨addrs[i.1], h.2 _ (List.mem_cons_of_mem _ (List.getElem_mem hi))⟩
    else
      ⟨target, h.2 _ List.mem_cons_self⟩
  inj' i j hij := by
    have hnd := List.nodup_cons.mp h.1
    by_cases hi : i.1 < addrs.length <;> by_cases hj : j.1 < addrs.length
    · simp only [hi, hj, ↓reduceDIte, Fin.mk.injEq] at hij
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd.2).mp hij)
    · simp only [hi, hj, ↓reduceDIte, Fin.mk.injEq] at hij
      exact absurd (hij ▸ List.getElem_mem hi) hnd.1
    · simp only [hi, hj, ↓reduceDIte, Fin.mk.injEq] at hij
      exact absurd (hij.symm ▸ List.getElem_mem hj) hnd.1
    · exact Fin.ext (by omega)

/-- The placed gate denoted by a `BooleanOracleGateCode` on `m` qubits against oracle `O`, or
`none` if the instruction is not well formed. -/
@[expose] noncomputable def toPlacedGate? (m : ℕ) (O : List Bool → Bool) :
    BooleanOracleGateCode → Option (PlacedGate m)
  | .gate g => g.toPlacedGate? m
  | .query addrs target =>
    if h : WellFormed m (.query addrs target) then
      some (xorQuery (fun x _ => O (List.ofFn x)) (queryEmb h))
    else
      none

@[simp] theorem toPlacedGate?_gate (m : ℕ) (O : List Bool → Bool) (g : GateCode) :
    toPlacedGate? m O (.gate g) = g.toPlacedGate? m := rfl

/-- Exactly the well-formed instructions denote placed gates. -/
theorem isSome_toPlacedGate?_iff {m : ℕ} {O : List Bool → Bool} {g : BooleanOracleGateCode} :
    (g.toPlacedGate? m O).isSome ↔ g.WellFormed m := by
  cases g with
  | gate c => exact GateCode.isSome_toPlacedGate?_iff
  | query addrs target =>
    simp only [toPlacedGate?]
    split_ifs with h <;> simp [h]

/-- **Semantics of a coherent XOR query on a basis state**: the query reads the bits on `addrs` in
order and XORs `O(a)` into `target`, leaving every other qubit unchanged. -/
theorem eval_toPlacedGate?_query_ket {m : ℕ} {O : List Bool → Bool} {addrs : List ℕ}
    {target : ℕ} {g : PlacedGate m} (hg : toPlacedGate? m O (.query addrs target) = some g)
    (ht : target < m) (x : Fin m → Bool) :
    g.eval (ket x) =
      ket (Function.update x ⟨target, ht⟩ (x ⟨target, ht⟩ ^^ O (addrs.map (readBit x)))) := by
  simp only [toPlacedGate?] at hg
  split_ifs at hg with h
  · cases hg
    set A := queryEmb h
    have hA_lt : ∀ {i : Fin (addrs.length + 1)} (hi : i.1 < addrs.length),
        A i = ⟨addrs[i.1], h.2 _ (List.mem_cons_of_mem _ (List.getElem_mem hi))⟩ := by
      intro i hi
      apply Fin.ext
      change (if hi' : i.1 < addrs.length then
        (⟨addrs[i.1], _⟩ : Fin m) else ⟨target, _⟩).1 = addrs[i.1]
      rw [dite_eq_left hi]
    have hA_last : A (Fin.natAdd addrs.length 0) = ⟨target, ht⟩ := by
      apply Fin.ext
      change (if hi' : (Fin.natAdd addrs.length 0).1 < addrs.length then
        (⟨addrs[_], _⟩ : Fin m) else ⟨target, _⟩).1 = target
      rw [dite_eq_right (by simp)]
    have hsplit : (queryRegisters A).symm (queryRegisters A x) = x :=
      (queryRegisters A).symm_apply_apply x
    conv_lhs => rw [← hsplit]
    rw [xorQuery_eval_ket]
    congr 1
    funext j
    by_cases hj : ∃ i : Fin (addrs.length + 1), A i = j
    · obtain ⟨i, rfl⟩ := hj
      by_cases hi : i.1 < addrs.length
      · have hne : A i ≠ ⟨target, ht⟩ := by
          intro heq
          have hmem : addrs[i.1] ∈ addrs := List.getElem_mem hi
          have hval : addrs[i.1] = target := congrArg Fin.val ((hA_lt hi).symm.trans heq)
          exact (List.nodup_cons.mp h.1).1 (hval ▸ hmem)
        have hcast : i = Fin.castAdd 1 ⟨i.1, hi⟩ := Fin.ext rfl
        rw [hcast, queryRegisters_symm_query, Function.update_of_ne (hcast ▸ hne)]
        simp [queryRegisters_apply]
      · have hi_lt : i.1 < addrs.length + 1 := i.2
        have hlast : i = Fin.natAdd addrs.length 0 := Fin.ext (by dsimp; omega)
        rw [hlast, queryRegisters_symm_response, hA_last, Function.update_self]
        simp only [queryRegisters_apply, Pi.add_apply, Bool.add_eq_xor]
        have hlist : (List.ofFn fun k : Fin addrs.length =>
            x (A (Fin.castAdd 1 k))) = addrs.map (readBit x) := by
          apply List.ext_getElem
          · simp
          · intro k hk₁ hk₂
            have hk : k < addrs.length := by simpa using hk₁
            simp only [List.getElem_ofFn, List.getElem_map]
            rw [hA_lt (show (Fin.castAdd 1 (⟨k, hk⟩ : Fin addrs.length)).1 < addrs.length from hk),
              readBit_of_lt _ (h.2 _ (List.mem_cons_of_mem _ (List.getElem_mem hk)))]
            rfl
        rw [hlist, hA_last]
    · rw [queryRegisters_symm_workspace _ _ _ _ j hj]
      have hne : j ≠ ⟨target, ht⟩ :=
        fun heq => hj ⟨Fin.natAdd addrs.length 0, hA_last.trans heq.symm⟩
      rw [Function.update_of_ne hne]
      simp [queryRegisters_apply]

/-- **Every well-formed instruction is its own inverse** (`g² = I`). -/
theorem eval_toPlacedGate?_self_inv {m : ℕ} {O : List Bool → Bool} {c : BooleanOracleGateCode}
    {g : PlacedGate m} (hg : c.toPlacedGate? m O = some g) (ψ : Qubits m) :
    g.eval (g.eval ψ) = ψ := by
  cases c with
  | gate code =>
    simp only [toPlacedGate?] at hg
    match code with
    | (true, t, []) =>
      simp only [GateCode.toPlacedGate?] at hg
      split_ifs at hg with ht
      cases hg
      have hmul : (⟨1, Gate.hadamard,
            ⟨![⟨t, ht⟩], fun i j _ => Subsingleton.elim i j⟩⟩ : PlacedGate m).matrix *
          (⟨1, Gate.hadamard,
            ⟨![⟨t, ht⟩], fun i j _ => Subsingleton.elim i j⟩⟩ : PlacedGate m).matrix = 1 := by
        change place _ Gate.hadamard * place _ Gate.hadamard = 1
        rw [← map_mul, Gate.hadamard_mul_self, map_one]
      change unitaryEquiv _ (unitaryEquiv _ ψ) = ψ
      rw [← unitaryEquiv_mul, hmul, unitaryEquiv_one]
    | (true, _, _ :: _) => simp [GateCode.toPlacedGate?] at hg
    | (false, t, cs) =>
      have hwf : GateCode.WellFormed m (false, t, cs) :=
        GateCode.isSome_toPlacedGate?_iff.mp (by rw [hg]; rfl)
      have ht : t < m := hwf.2.2 _ List.mem_cons_self
      have hnot : t ∉ cs := GateCode.target_notMem_of_wellFormed rfl hwf
      have hket : ∀ x : Fin m → Bool, g.eval (g.eval (ket x)) = ket x := by
        intro x
        rw [GateCode.eval_toPlacedGate_ket hg ht x, GateCode.eval_toPlacedGate_ket hg ht]
        congr 1
        have hstep := GateCode.classicalStep_classicalStep (m := m) (g := (false, t, cs)) hnot x
        rw [GateCode.classicalStep, dite_eq_left ht, GateCode.classicalStep, dite_eq_left ht]
          at hstep
        exact hstep
      have hsum : ψ = ∑ x : Fin m → Bool, ψ.ofLp x • ket x := (sum_smul_ket ψ).symm
      conv_lhs => rw [hsum, map_sum, map_sum]
      simp_rw [map_smul, hket]
      rw [← hsum]
  | query addrs target =>
    simp only [toPlacedGate?] at hg
    split_ifs at hg with h
    cases hg
    exact xorQuery_eval_twice _ _ ψ

/-- **Phase kickback**: applying a coherent XOR query on `(addrs, target)` when qubit `target` is
in the `|−⟩` state multiplies `|x⟩` by `(-1)^{O(addrs)}` while keeping `target` in `|−⟩`. -/
theorem eval_phaseQuery_ket {m : ℕ} {O : List Bool → Bool} {addrs : List ℕ} {target : ℕ}
    {g : PlacedGate m} (hg : toPlacedGate? m O (.query addrs target) = some g)
    (ht : target < m) (x : Fin m → Bool) :
    g.eval
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (Function.update x ⟨target, ht⟩ false) -
       (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (Function.update x ⟨target, ht⟩ true)) =
    (if O (addrs.map (readBit x)) then (-1 : ℂ) else 1) •
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (Function.update x ⟨target, ht⟩ false) -
       (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (Function.update x ⟨target, ht⟩ true)) := by
  have hwf : WellFormed m (.query addrs target) :=
    isSome_toPlacedGate?_iff.mp (by rw [hg]; rfl)
  have hnot : target ∉ addrs := (List.nodup_cons.mp hwf.1).1
  have hmap (b : Bool) :
      addrs.map (readBit (Function.update x ⟨target, ht⟩ b)) = addrs.map (readBit x) := by
    apply List.map_congr_left
    intro w hw
    have hne : w ≠ target := fun heq => hnot (heq ▸ hw)
    by_cases hwm : w < m
    · rw [readBit_of_lt _ hwm, readBit_of_lt _ hwm,
        Function.update_of_ne (by simp [Fin.ext_iff, hne])]
    · rw [readBit_of_le _ (not_lt.mp hwm), readBit_of_le _ (not_lt.mp hwm)]
  rw [map_sub, map_smul, map_smul, eval_toPlacedGate?_query_ket hg ht,
    eval_toPlacedGate?_query_ket hg ht, hmap false, hmap true]
  simp only [Function.update_self, Function.update_idem, Bool.false_xor, Bool.true_xor]
  cases O (addrs.map (readBit x))
  · simp
  · simp [sub_eq_add_neg, add_comm]

/-- Binary encoding of a `BooleanOracleGateCode` using a tagged sum of `GateCode` and
`(List ℕ × ℕ)`. -/
@[expose] def encBooleanOracleGateCode : BooleanOracleGateCode ↪ List Bool :=
  ⟨fun c => match c with
    | .gate g => false :: encGateCode g
    | .query addrs target => true :: encPair (encList encUnary) encUnary (addrs, target), by
    rintro (g₁ | ⟨a₁, t₁⟩) (g₂ | ⟨a₂, t₂⟩) h
    · simp only [List.cons.injEq, true_and] at h
      exact congrArg BooleanOracleGateCode.gate (encGateCode.injective h)
    · simp at h
    · simp at h
    · simp only [List.cons.injEq, true_and] at h
      have hp := (encPair (encList encUnary) encUnary).injective h
      exact congrArg₂ BooleanOracleGateCode.query (congrArg Prod.fst hp) (congrArg Prod.snd hp)⟩

@[simp] theorem encBooleanOracleGateCode_gate (g : GateCode) :
    encBooleanOracleGateCode (.gate g) = false :: encGateCode g := rfl

@[simp] theorem encBooleanOracleGateCode_query (addrs : List ℕ) (target : ℕ) :
    encBooleanOracleGateCode (.query addrs target) =
      true :: encPair (encList encUnary) encUnary (addrs, target) := rfl

/-- Wrapping a polynomial-time `GateCode` into `BooleanOracleGateCode.gate` is polynomial-time. -/
@[fun_prop] theorem computableInPolyTime_gate {α : Type} {enc : α ↪ List Bool} {g : α → GateCode}
    (hg : ComputableInPolyTime g enc encGateCode) :
    ComputableInPolyTime (fun a => BooleanOracleGateCode.gate (g a)) enc
      encBooleanOracleGateCode := by
  have hraw : ComputableInPolyTime (fun a => encGateCode (g a)) enc encBits :=
    (ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl).comp hg
  have h := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false]) hraw
  exact h.of_enc_eq fun _ => rfl

/-- Constructing a `BooleanOracleGateCode.query` from polynomial-time wires is polynomial-time. -/
@[fun_prop] theorem computableInPolyTime_query {α : Type} {enc : α ↪ List Bool}
    {addrs : α → List ℕ} {target : α → ℕ}
    (haddrs : ComputableInPolyTime addrs enc (encList encUnary))
    (htarget : ComputableInPolyTime target enc encUnary) :
    ComputableInPolyTime (fun a => BooleanOracleGateCode.query (addrs a) (target a)) enc
      encBooleanOracleGateCode := by
  have hraw : ComputableInPolyTime
      (fun a => encPair (encList encUnary) encUnary (addrs a, target a)) enc encBits :=
    (ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl).comp (haddrs.prod htarget)
  have h := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [true]) hraw
  exact h.of_enc_eq fun _ => rfl

end BooleanOracleGateCode

/-- A finite quantum circuit with variable-length coherent XOR oracle queries. -/
abbrev BooleanOracleCircuit := List BooleanOracleGateCode

namespace BooleanOracleCircuit

/-- Interpret a `BooleanOracleCircuit` as a `Cslib.Quantum.Circuit` on `m` qubits against `O`. -/
@[expose] noncomputable def toCircuit (m : ℕ) (O : List Bool → Bool)
    (codes : BooleanOracleCircuit) : Circuit m :=
  codes.filterMap (BooleanOracleGateCode.toPlacedGate? m O)

/-- Number of oracle query instructions in a circuit. -/
@[expose] def queryCount (codes : BooleanOracleCircuit) : ℕ :=
  codes.countP BooleanOracleGateCode.isQuery

/-- Number of elementary gate instructions in a circuit. -/
@[expose] def gateCount (codes : BooleanOracleCircuit) : ℕ :=
  codes.countP fun g => !g.isQuery

@[simp] theorem toCircuit_nil (m : ℕ) (O : List Bool → Bool) :
    toCircuit m O [] = [] := rfl

theorem toCircuit_cons (m : ℕ) (O : List Bool → Bool) (c : BooleanOracleGateCode)
    (codes : BooleanOracleCircuit) {g : PlacedGate m} (hg : c.toPlacedGate? m O = some g) :
    toCircuit m O (c :: codes) = g :: toCircuit m O codes := by
  simp [toCircuit, hg]

@[simp] theorem toCircuit_append (m : ℕ) (O : List Bool → Bool)
    (codes₁ codes₂ : BooleanOracleCircuit) :
    toCircuit m O (codes₁ ++ codes₂) = toCircuit m O codes₁ ++ toCircuit m O codes₂ :=
  List.filterMap_append

theorem toCircuit_map_gate (m : ℕ) (O : List Bool → Bool) (gs : List GateCode) :
    toCircuit m O (gs.map BooleanOracleGateCode.gate) = Circuit.ofCodes m gs := by
  rw [toCircuit, List.filterMap_map, Circuit.ofCodes]
  rfl

@[simp] theorem queryCount_nil : queryCount [] = 0 := rfl

@[simp] theorem queryCount_cons_gate (g : GateCode) (codes : BooleanOracleCircuit) :
    queryCount (.gate g :: codes) = queryCount codes := rfl

@[simp] theorem queryCount_cons_query (addrs : List ℕ) (target : ℕ)
    (codes : BooleanOracleCircuit) :
    queryCount (.query addrs target :: codes) = queryCount codes + 1 := by
  rw [queryCount, List.countP_cons]
  simp [queryCount]

@[simp] theorem queryCount_append (codes₁ codes₂ : BooleanOracleCircuit) :
    queryCount (codes₁ ++ codes₂) = queryCount codes₁ + queryCount codes₂ :=
  List.countP_append

@[simp] theorem queryCount_reverse (codes : BooleanOracleCircuit) :
    queryCount codes.reverse = queryCount codes := by
  simp [queryCount, List.countP_reverse]

@[simp] theorem queryCount_map_gate (gs : List GateCode) :
    queryCount (gs.map BooleanOracleGateCode.gate) = 0 := by
  simp [queryCount, BooleanOracleGateCode.isQuery]

theorem gateCount_add_queryCount (codes : BooleanOracleCircuit) :
    gateCount codes + queryCount codes = codes.length := by
  simpa only [gateCount, queryCount, decide_not, Bool.decide_coe, Nat.add_comm] using
    (List.length_eq_countP_add_countP (l := codes) BooleanOracleGateCode.isQuery).symm

/-- **Exact circuit reversal**: reversing a well-formed `BooleanOracleCircuit` computes its exact
inverse on every quantum state `ψ`. -/
theorem eval_reverse_eval {m : ℕ} (O : List Bool → Bool) (codes : BooleanOracleCircuit)
    (hwf : ∀ c ∈ codes, c.WellFormed m) (ψ : Qubits m) :
    Circuit.eval (toCircuit m O codes.reverse)
      (Circuit.eval (toCircuit m O codes) ψ) = ψ := by
  induction codes generalizing ψ with
  | nil => simp [toCircuit]
  | cons c cs ih =>
    obtain ⟨g, hg⟩ :=
      Option.isSome_iff_exists.mp
        (BooleanOracleGateCode.isSome_toPlacedGate?_iff.mpr (hwf c List.mem_cons_self))
    rw [List.reverse_cons, toCircuit_append, toCircuit_cons m O c cs hg, Circuit.eval_cons,
      Circuit.eval_append, ih (fun c' hc' => hwf c' (List.mem_cons_of_mem _ hc')),
      toCircuit_cons m O c [] hg, toCircuit_nil, Circuit.eval_cons, Circuit.eval_nil]
    exact BooleanOracleGateCode.eval_toPlacedGate?_self_inv hg ψ

/-- Applying a circuit after its reverse also yields the identity. -/
theorem eval_eval_reverse {m : ℕ} (O : List Bool → Bool) (codes : BooleanOracleCircuit)
    (hwf : ∀ c ∈ codes, c.WellFormed m) (ψ : Qubits m) :
    Circuit.eval (toCircuit m O codes)
      (Circuit.eval (toCircuit m O codes.reverse) ψ) = ψ := by
  have hrev := eval_reverse_eval O codes.reverse (fun c hc => hwf c (List.mem_reverse.mp hc)) ψ
  simpa only [List.reverse_reverse] using hrev

end BooleanOracleCircuit

/-- A polynomial-time uniform family of quantum circuits with coherent XOR access to a classical
Boolean oracle `O : List Bool → Bool`, over `{H, NOT, CNOT, Toffoli}`. -/
structure UniformBooleanOracleCircuitFamily where
  /-- Register width on inputs of length `n`. -/
  width : ℕ → ℕ
  /-- Oracle circuit instructions on inputs of length `n`. -/
  gates : ℕ → BooleanOracleCircuit
  /-- Register width is computable in polynomial time from `n` in unary. -/
  computableInPolyTime_width : ComputableInPolyTime width encUnary encUnary
  /-- Gate list is computable in polynomial time from `n` in unary. -/
  computableInPolyTime_gates :
    ComputableInPolyTime gates encUnary (encList BooleanOracleGateCode.encBooleanOracleGateCode)
  /-- Input qubits `0, …, n - 1` fit in the register. -/
  le_width : ∀ n, n ≤ width n
  /-- Qubit `0` (the output qubit) is always present. -/
  width_pos : ∀ n, 0 < width n
  /-- Every instruction emitted at input length `n` is well formed. -/
  wellFormed : ∀ n, ∀ g ∈ gates n, g.WellFormed (width n)

namespace UniformBooleanOracleCircuitFamily

/-- Acceptance probability on classical input `x` relative to oracle `O`: probability that
measuring qubit `0` in the computational basis yields `1`. -/
@[expose] noncomputable def acceptProb (F : UniformBooleanOracleCircuitFamily)
    (O : List Bool → Bool) (x : List Bool) : ℝ :=
  let m := F.width x.length
  measureProb (Circuit.run (BooleanOracleCircuit.toCircuit m O (F.gates x.length))
    (inputState m x)) (accepting m)

/-- Express `acceptProb` directly in terms of `measureProb` on the circuit's output state. -/
theorem acceptProb_eq_measureProb (F : UniformBooleanOracleCircuitFamily)
    (O : List Bool → Bool) (x : List Bool) :
    F.acceptProb O x =
      measureProb
        (Circuit.run (BooleanOracleCircuit.toCircuit (F.width x.length) O (F.gates x.length))
          (inputState (F.width x.length) x))
        (accepting (F.width x.length)) := rfl

theorem acceptProb_nonneg (F : UniformBooleanOracleCircuitFamily) (O : List Bool → Bool)
    (x : List Bool) : 0 ≤ F.acceptProb O x :=
  measureProb_nonneg _ _

theorem acceptProb_le_one (F : UniformBooleanOracleCircuitFamily) (O : List Bool → Bool)
    (x : List Bool) : F.acceptProb O x ≤ 1 := by
  unfold acceptProb
  have hnorm := Circuit.norm_run
    (BooleanOracleCircuit.toCircuit (F.width x.length) O (F.gates x.length))
    (inputState (F.width x.length) x)
  exact (measureProb_le_measureProb_univ _ _).trans (by rw [measureProb_univ, hnorm, one_pow])

/-- Append a final NOT gate on qubit `0` to flip acceptance and rejection. -/
@[expose] def appendNot (F : UniformBooleanOracleCircuitFamily) :
    UniformBooleanOracleCircuitFamily where
  width := F.width
  gates n := F.gates n ++ [.gate (false, 0, [])]
  computableInPolyTime_width := F.computableInPolyTime_width
  computableInPolyTime_gates := by
    have hconst : ComputableInPolyTime
        (fun _ : ℕ => ([BooleanOracleGateCode.gate (false, 0, [])] : BooleanOracleCircuit))
        encUnary (encList BooleanOracleGateCode.encBooleanOracleGateCode) :=
      ComputableInPolyTime.const _
    exact F.computableInPolyTime_gates.listAppend' hconst
  le_width := F.le_width
  width_pos := F.width_pos
  wellFormed n g hg := by
    rcases List.mem_append.mp hg with hg | hg
    · exact F.wellFormed n g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨by simp, by simp, fun _ hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact F.width_pos n⟩

/-- Appending a final NOT gate on qubit `0` replaces acceptance probability `p` by `1 - p`. -/
theorem acceptProb_appendNot (F : UniformBooleanOracleCircuitFamily) (O : List Bool → Bool)
    (x : List Bool) : F.appendNot.acceptProb O x = 1 - F.acceptProb O x := by
  set m := F.width x.length
  set C := BooleanOracleCircuit.toCircuit m O (F.gates x.length)
  have hm : 0 < m := F.width_pos x.length
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp
    (GateCode.isSome_toPlacedGate?_iff.mpr
      (show GateCode.WellFormed m (false, 0, []) from
        ⟨by simp, by simp, fun _ hi => by
          simp only [List.mem_singleton] at hi; subst hi; exact hm⟩))
  have hnot : BooleanOracleCircuit.toCircuit m O [.gate (false, 0, [])] = [g] := by
    simp [BooleanOracleCircuit.toCircuit, BooleanOracleGateCode.toPlacedGate?, hg]
  have hstep : ∀ y : Fin m → Bool,
      g.eval (ket y) = ket (Function.update y ⟨0, hm⟩ (!y ⟨0, hm⟩)) := by
    intro y
    simpa using GateCode.eval_toPlacedGate_ket hg hm y
  have hnorm : ‖Circuit.run C (inputState m x)‖ = 1 := Circuit.norm_run C (inputState m x)
  unfold acceptProb appendNot
  dsimp only
  rw [BooleanOracleCircuit.toCircuit_append, hnot, Circuit.run, Circuit.eval_append,
    Circuit.eval_cons, Circuit.eval_nil]
  set ψ := Circuit.eval C (ket (inputState m x))
  have hnormψ : ‖ψ‖ = 1 := hnorm
  have hamp : ∀ z : Fin m → Bool,
      (g.eval ψ).ofLp z = ψ.ofLp (Function.update z ⟨0, hm⟩ (!z ⟨0, hm⟩)) :=
    PlacedGate.eval_apply_of_involutive g (fun z => by
      funext i; by_cases hi : i = ⟨0, hm⟩ <;> simp [hi]) hstep ψ
  have hpart : measureProb (g.eval ψ) (accepting m) = measureProb ψ (accepting m)ᶜ := by
    simp only [measureProb, hamp]
    refine Finset.sum_bij (fun z _ => Function.update z ⟨0, hm⟩ (!z ⟨0, hm⟩)) ?_ ?_ ?_ ?_
    · intro z hz
      rw [mem_compl, mem_accepting hm]
      rw [mem_accepting hm] at hz
      simp [hz]
    · intro z₁ _ z₂ _ h
      funext i
      by_cases hi : i = ⟨0, hm⟩
      · subst hi
        have := congrFun h ⟨0, hm⟩
        simp only [Function.update_self] at this
        cases h1 : z₁ ⟨0, hm⟩ <;> cases h2 : z₂ ⟨0, hm⟩ <;> simp_all
      · have := congrFun h i
        simpa [hi] using this
    · intro y hy
      rw [mem_compl, mem_accepting hm] at hy
      refine ⟨Function.update y ⟨0, hm⟩ (!y ⟨0, hm⟩), ?_, ?_⟩
      · rw [mem_accepting hm]
        simp [hy]
      · funext i
        by_cases hi : i = ⟨0, hm⟩
        · subst hi; simp
        · simp [hi]
    · intro _ _; rfl
  rw [hpart, measureProb_compl, hnormψ, one_pow]
  rfl

/-- Embed an oracle-free `UniformCircuitFamily` as a zero-query oracle circuit family. -/
@[expose] def ofUniformCircuitFamily (F : UniformCircuitFamily) :
    UniformBooleanOracleCircuitFamily where
  width := F.width
  gates n := (F.gates n).map BooleanOracleGateCode.gate
  computableInPolyTime_width := F.computableInPolyTime_width
  computableInPolyTime_gates :=
    ComputableInPolyTime.mapWith
      (BooleanOracleGateCode.computableInPolyTime_gate
        (ComputableInPolyTime.snd encBool encGateCode))
      (ComputableInPolyTime.const true) F.computableInPolyTime_gates
  le_width := F.le_width
  width_pos := F.width_pos
  wellFormed n g hg := by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    exact F.wellFormed n c hc

/-- A zero-query family has the exact same acceptance probability as its underlying circuit
family. -/
theorem acceptProb_ofUniformCircuitFamily (F : UniformCircuitFamily) (O : List Bool → Bool)
    (x : List Bool) :
    (ofUniformCircuitFamily F).acceptProb O x = F.acceptProb x := by
  simp [acceptProb, ofUniformCircuitFamily, UniformCircuitFamily.acceptProb,
    Cslib.Quantum.acceptProb, BooleanOracleCircuit.toCircuit_map_gate, Circuit.run]
  rfl

end UniformBooleanOracleCircuitFamily

end Quantum

namespace Complexity

open Quantum

variable {α : Type}

/-- **Exact quantum polynomial time relative to a classical Boolean oracle `O`**: languages
decided with probability `1` on members and `0` on non-members by a polynomial-time uniform family
of quantum oracle circuits over `{H, NOT, CNOT, Toffoli}`. -/
@[expose] def EQPWithOracle (O : List Bool → Bool) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformBooleanOracleCircuitFamily, ∀ a,
    (a ∈ A → F.acceptProb O (enc a) = 1) ∧ (a ∉ A → F.acceptProb O (enc a) = 0)}

/-- **Bounded-error quantum polynomial time relative to a classical Boolean oracle `O`**:
languages decided with error at most `1 / 3` by a polynomial-time uniform family of quantum oracle
circuits over `{H, NOT, CNOT, Toffoli}`. -/
@[expose] def BQPWithOracle (O : List Bool → Bool) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformBooleanOracleCircuitFamily, ∀ a,
    (a ∈ A → 2 / 3 ≤ F.acceptProb O (enc a)) ∧ (a ∉ A → F.acceptProb O (enc a) ≤ 1 / 3)}

/-- **`EQP^O ⊆ BQP^O`** for every classical Boolean oracle `O`. -/
theorem EQPWithOracle_subset_BQPWithOracle (O : List Bool → Bool) (enc : α ↪ List Bool) :
    EQPWithOracle O enc ⊆ BQPWithOracle O enc := by
  rintro A ⟨F, hF⟩
  exact ⟨F, fun a => ⟨fun ha => (hF a).1 ha ▸ by norm_num, fun ha => (hF a).2 ha ▸ by norm_num⟩⟩

/-- **`EQP^O` is closed under complement**: appending a NOT gate to qubit `0` flips `1` and `0`. -/
theorem compl_mem_EQPWithOracle {O : List Bool → Bool} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ EQPWithOracle O enc) : Aᶜ ∈ EQPWithOracle O enc := by
  obtain ⟨F, hF⟩ := hA
  refine ⟨F.appendNot, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · rw [F.acceptProb_appendNot, (hF a).2 ha, sub_zero]
  · rw [F.acceptProb_appendNot, (hF a).1 (Set.notMem_compl_iff.mp ha), sub_self]

/-- **`BQP^O` is closed under complement**. -/
theorem compl_mem_BQPWithOracle {O : List Bool → Bool} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ BQPWithOracle O enc) : Aᶜ ∈ BQPWithOracle O enc := by
  obtain ⟨F, hF⟩ := hA
  refine ⟨F.appendNot, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have := (hF a).2 ha
    rw [F.acceptProb_appendNot]; linarith
  · have := (hF a).1 (Set.notMem_compl_iff.mp ha)
    rw [F.acceptProb_appendNot]; linarith

end Complexity

end CslibFrontier
