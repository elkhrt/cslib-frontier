/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import CslibFrontier.Computability.Circuit.Boolean.Oracle.Selection
public import CslibFrontier.Computability.Circuit.FanIn
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relativized $\mathrm{NC}^1$ Reductions and Determinant Circuit Compilers

This module formalizes Cook--Wilson relativized logarithmic-depth Boolean circuit complexity
(`Cslib.Complexity.NC1Oracle`), the determinant complexity classes $\mathrm{DET}_k$
(`Cslib.Complexity.DETk`) and $\mathrm{DET}$ (`Cslib.Complexity.DET`)
over $\mathbb{Z}_k$ and $\mathbb{Z}$, and a single-query oracle circuit compiler for matrices whose
entries each depend on at most one input wire under standard Lean axioms.

## Main definitions

* `Cslib.Complexity.encodeBits`, `Cslib.Complexity.decodeBits`:
  fixed-width little-endian binary bit-tuple codecs.
* `Cslib.Complexity.nc1OracleDepthWeight`: Cook--Wilson logarithmic oracle gate depth
  weight (`1` for De Morgan base gates, `⌊log₂ q⌋ + 1` for an arity-`q` oracle gate).
* `Cslib.Complexity.NC1Oracle`: languages reducible to an oracle language `O` by
  polynomial-size, polynomial-fan-in oracle circuits of Cook--Wilson weighted depth `O(log n)`.
* `Cslib.Complexity.DetZModInstance`, `Cslib.Complexity.encDetZMod`,
  `Cslib.Complexity.detZModLanguage`: square matrix determinant verification over
  `ZMod k`.
* `Cslib.Complexity.DetIntInstance`, `Cslib.Complexity.encDetInt`,
  `Cslib.Complexity.detIntLanguage`: signed bit-graph of the integer matrix
  determinant over `ℤ`.
* `Cslib.Complexity.DETk`, `Cslib.Complexity.DET`,
  `Cslib.Complexity.DETkOn`, `Cslib.Complexity.DETOn`: the nonuniform
  determinant classes $\mathrm{DET}_k = \mathrm{NC}^1(\mathrm{det}_{\mathbb{Z}_k})$ and
  $\mathrm{DET} = \mathrm{NC}^1(\mathrm{det}_{\mathbb{Z}})$ on bitstrings and encoded decision
  problems.
* `Cslib.Complexity.SingleVarMatrixSpec`: specification of an `m × m` matrix over
  `ZMod k` whose entries each depend on at most one Boolean input wire.

## Main results

* `Cslib.Complexity.NC1_subset_NC1Oracle`,
  `Cslib.Complexity.self_mem_NC1Oracle`,
  `Cslib.Complexity.NC1Oracle.trans`: $\mathrm{NC}^1 \subseteq \mathrm{NC}^1(O)$,
  $O \in \mathrm{NC}^1(O)$, and transitivity of $\mathrm{NC}^1$-reducibility.
* `Cslib.Complexity.singleLiteralDetCircuit`,
  `Cslib.Complexity.eval_singleLiteralDetCircuit`,
  `Cslib.Complexity.size_singleLiteralDetCircuit_le`,
  `Cslib.Complexity.depthWith_singleLiteralDetCircuit_le`: every
  `SingleVarMatrixSpec` has its determinant-equality (or disequality) predicate computed by a
  single-query oracle circuit of linear gate size `n + 4` and logarithmic Cook--Wilson depth.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Binary fixed-width little-endian bit-tuple codecs -/

/-- Little-endian binary encoding of `u : ℕ` into `w` bits. -/
@[expose]
def encodeBits : ∀ (w : ℕ), ℕ → (Fin w → Bool)
  | 0, _ => Fin.elim0
  | w + 1, u => Fin.cons (decide (u % 2 = 1)) (encodeBits w (u / 2))

/-- Little-endian binary decoding of `b : Fin w → Bool` into a natural number `< 2 ^ w`. -/
@[expose]
def decodeBits : ∀ {w : ℕ}, (Fin w → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, b => (if b 0 then 1 else 0) + 2 * decodeBits (b ∘ Fin.succ)

theorem decodeBits_lt {w : ℕ} (b : Fin w → Bool) : decodeBits b < 2 ^ w := by
  induction w with
  | zero => simp [decodeBits]
  | succ w ih =>
    have h := ih (b ∘ Fin.succ)
    simp only [decodeBits, pow_succ']
    rcases Bool.eq_false_or_eq_true (b 0) with hb | hb <;> simp [hb] <;> omega

theorem decodeBits_encodeBits {w u : ℕ} (hu : u < 2 ^ w) :
    decodeBits (encodeBits w u) = u := by
  induction w generalizing u with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hu
    simp [decodeBits, hu]
  | succ w ih =>
    simp only [pow_succ'] at hu
    have hdiv : u / 2 < 2 ^ w := by omega
    simp only [encodeBits, decodeBits, Fin.cons_zero]
    rw [show Fin.cons (decide (u % 2 = 1)) (encodeBits w (u / 2)) ∘ Fin.succ =
        encodeBits w (u / 2) from funext fun _ ↦ rfl, ih hdiv]
    by_cases hmod : u % 2 = 1 <;> simp [hmod] <;> omega

theorem encodeBits_decodeBits {w : ℕ} (b : Fin w → Bool) :
    encodeBits w (decodeBits b) = b := by
  induction w with
  | zero => funext i; exact Fin.elim0 i
  | succ w ih =>
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [encodeBits, decodeBits, Fin.cons_zero]
      rcases Bool.eq_false_or_eq_true (b 0) with hb | hb <;> simp [hb]
    · simp only [encodeBits, decodeBits, Fin.cons_succ]
      have hdiv : ((if b 0 then 1 else 0) + 2 * decodeBits (b ∘ Fin.succ)) / 2 =
          decodeBits (b ∘ Fin.succ) := by
        rcases Bool.eq_false_or_eq_true (b 0) with hb | hb
        · simp [hb]; omega
        · simp [hb]
      rw [hdiv, ih (b ∘ Fin.succ)]
      rfl

theorem encodeBits_apply {w u : ℕ} (r : Fin w) :
    encodeBits w u r = decide ((u / 2 ^ r.val) % 2 = 1) := by
  induction w generalizing u with
  | zero => exact Fin.elim0 r
  | succ w ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) r
    · simp [encodeBits]
    · simp only [encodeBits, Fin.cons_succ, Fin.val_succ, ih, pow_succ', ← Nat.div_div_eq_div_mul]

theorem sum_two_pow_encodeBits {B u : ℕ} (hu : u < 2 ^ B) :
    (∑ r : Fin B, if decide ((u / 2 ^ r.val) % 2 = 1) then 2 ^ r.val else 0) = u := by
  induction B generalizing u with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hu
    simp [hu]
  | succ B ih =>
    simp only [pow_succ'] at hu
    rw [Fin.sum_univ_succ]
    have hdiv : u / 2 < 2 ^ B := by omega
    have htail :
        (∑ x : Fin B, if decide ((u / 2 ^ x.succ.val) % 2 = 1) then 2 ^ x.succ.val else 0) =
          2 * ∑ x : Fin B, if decide (((u / 2) / 2 ^ x.val) % 2 = 1) then 2 ^ x.val else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
      split_ifs <;> ring
    rw [htail, ih hdiv]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    by_cases hmod : u % 2 = 1 <;> simp [hmod] <;> omega

/-! ### Cook--Wilson relativized $\mathrm{NC}^1$ (`NC1Oracle`) -/

/-- Cook--Wilson logarithmic depth weight on the oracle Boolean basis: `1` for each De Morgan base
operation and `⌊log₂ q⌋ + 1` for an oracle query gate of fan-in `q`. -/
@[expose]
def nc1OracleDepthWeight : OracleOp → ℕ
  | .base _ => 1
  | .query q => Nat.log 2 q + 1

@[simp]
theorem nc1OracleDepthWeight_base (op : Op) :
    nc1OracleDepthWeight (.base op) = 1 := by
  rfl

@[simp]
theorem nc1OracleDepthWeight_query (q : ℕ) :
    nc1OracleDepthWeight (.query q) = Nat.log 2 q + 1 := by
  rfl

/-- **Relativized $\mathrm{NC}^1(O)$**: languages over `Bool` decided at
each input length `n` by an oracle circuit over `oracleSignature` of polynomially bounded gate count
`s n`, polynomially bounded gate fan-in `s n`, and Cook--Wilson weighted depth at most
`c * (⌊log₂ n⌋ + 1)`.
-/
@[expose]
def NC1Oracle (O : Language Bool) : Set (Language Bool) :=
  {L | ∃ (C : ∀ n, Circuit oracleSignature n 1) (c : ℕ) (s : ℕ → ℕ),
    PolynomiallyBounded s ∧
    ∀ n, (C n).size ≤ s n ∧
      (C n).FanInAtMost (s n) ∧
      (C n).depthWith nc1OracleDepthWeight ≤ c * (Nat.log 2 n + 1) ∧
      (C n).Computes (oracleInterpretation O) (single (L.slice n))}

theorem mem_NC1Oracle_iff {O L : Language Bool} :
    L ∈ NC1Oracle O ↔
      ∃ (C : ∀ n, Circuit oracleSignature n 1) (c : ℕ) (s : ℕ → ℕ),
        PolynomiallyBounded s ∧
        ∀ n, (C n).size ≤ s n ∧
          (C n).FanInAtMost (s n) ∧
          (C n).depthWith nc1OracleDepthWeight ≤ c * (Nat.log 2 n + 1) ∧
          (C n).Computes (oracleInterpretation O) (single (L.slice n)) := by
  rfl

/-- Every language in $\mathrm{NC}^1$ lies in $\mathrm{NC}^1(O)$ for every oracle `O`. -/
theorem NC1_subset_NC1Oracle (O : Language Bool) : NC 1 ⊆ NC1Oracle O := by
  rintro L ⟨c, s, hs, hC⟩
  choose C hCc hCd hCs using hC
  refine ⟨fun n ↦ (C n).mapOp toOracle, c, fun n ↦ s n + 2, by fun_prop, fun n ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [Circuit.size_mapOp]
    exact (hCs n).trans (Nat.le_add_right _ _)
  · exact fanInAtMost_mapOp_toOracle (C n).program (Nat.le_add_left 2 (s n))
  · have hdepth : ((C n).mapOp toOracle).depthWith nc1OracleDepthWeight = (C n).depth := by
      rw [Circuit.depthWith_mapOp]
      exact (C n).depthWith_one
    rw [hdepth]
    simpa only [pow_one] using hCd n
  · exact (hCc n).mapOp

/-- Every oracle language `O` lies in its own $\mathrm{NC}^1(O)$ class via a single query gate. -/
theorem self_mem_NC1Oracle (O : Language Bool) : O ∈ NC1Oracle O := by
  refine ⟨fun n ↦ Circuit.oneGate (.query n) id, 1, fun n ↦ n + 1, by fun_prop,
    fun n ↦ ⟨by simp, by simp, by simp, fun x ↦ funext fun i ↦ ?_⟩⟩
  obtain rfl : i = 0 := Subsingleton.elim i 0
  rfl

/-- Every language in $\mathrm{NC}^1(O)$ lies in $\mathrm{P/poly}^O$. -/
theorem NC1Oracle_subset_PPolyOracle (O : Language Bool) :
    NC1Oracle O ⊆ PPolyOracle O := by
  rintro L ⟨C, _, s, hs, hC⟩
  exact ⟨C, s, hs, fun n ↦ ⟨(hC n).1, (hC n).2.1, (hC n).2.2.2⟩⟩

section SimulationWeightedDepth

private theorem wireDepthsWith_scale_le {σ : Signature} {n g : ℕ}
    (p : Program σ n g) (w : σ.Op → ℕ) (K : ℕ) (wire : Wire n g) :
    p.wireDepthsWith (fun op ↦ K * w op) wire ≤ K * p.wireDepthsWith w wire := by
  induction p with
  | empty =>
    cases wire with
    | input _ => simp
    | gate j => exact j.elim0
  | gate q line ih =>
    refine Wire.lastCases ?_ (fun u ↦ ?_) wire
    · rw [Program.wireDepthsWith_gateWire, Program.wireDepthsWith_gateWire,
        Program.depthsWith_gate_last, Program.depthsWith_gate_last,
        Line.depthWith_eq_sup, Line.depthWith_eq_sup]
      have hsup :
          (Finset.univ.sup fun a ↦ (q.wireDepthsWith fun op ↦ K * w op) (line.wires a)) ≤
            K * (Finset.univ.sup fun a ↦ (q.wireDepthsWith w) (line.wires a)) := by
        refine Finset.sup_le fun a _ ↦ (ih (line.wires a)).trans (Nat.mul_le_mul_left K ?_)
        exact Finset.le_sup (f := fun a ↦ (q.wireDepthsWith w) (line.wires a)) (Finset.mem_univ a)
      nlinarith
    · rw [Program.wireDepthsWith_gate_castSucc, Program.wireDepthsWith_gate_castSucc]
      exact ih u

private theorem depthWith_scale_le {σ : Signature} {n m : ℕ}
    (c : Circuit σ n m) (w : σ.Op → ℕ) (K : ℕ) :
    c.depthWith (fun op ↦ K * w op) ≤ K * c.depthWith w :=
  (Circuit.depthWith_le_iff _ c).2 fun j ↦
    (wireDepthsWith_scale_le c.program w K (c.outputs j)).trans
      (Nat.mul_le_mul_left K (c.wireDepthsWith_outputs_le_depthWith w j))

private theorem wireDepthsWith_simulateRenaming_le {σ τ : Signature} {n g : ℕ}
    (p : Program σ n g) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (w : τ.Op → ℕ) (wire : Wire n g) :
    (p.simulateProgram impl).wireDepthsWith w (p.simulateRenaming impl wire) ≤
      p.wireDepthsWith (fun op ↦ (impl op).depthWith w) wire := by
  induction p with
  | empty =>
    cases wire with
    | input _ => exact le_rfl
    | gate j => exact j.elim0
  | gate q line ih =>
    dsimp only [Program.simulateProgram, Program.simulateRenaming, Program.simulate,
      Program.cost_gate] at ih ⊢
    set cost : σ.Op → ℕ := fun op ↦ (impl op).depthWith w
    refine Wire.lastCases ?_ (fun u ↦ ?_) wire
    · simp only [Wire.Renaming.apply_gate, Wire.Renaming.skipLast_gates_last]
      rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
      have hc := line.cost_le_depthWith cost (q.wireDepthsWith cost)
      have hD (a : Fin (σ.Arity line.op)) :
          (q.simulate impl).1.wireDepthsWith w (((q.simulate impl).2 ∘ line.wires) a) ≤
            line.depthWith cost (q.wireDepthsWith cost) - (impl line.op).depthWith w := by
        have h₁ := ih (line.wires a)
        have h₂ := line.wireDepth_add_le_depthWith cost (q.wireDepthsWith cost) a
        dsimp only [Function.comp_apply, cost] at *
        omega
      have h := Program.wireDepthsWith_append_appendedWire_le (q.simulate impl).1
        ((q.simulate impl).2 ∘ line.wires) w hD (impl line.op).program ((impl line.op).outputs 0)
      have ho := (impl line.op).wireDepthsWith_outputs_le_depthWith w 0
      dsimp only [Function.comp_apply, cost] at hc ho h ⊢
      omega
    · rw [Wire.Renaming.skipLast_castSucc, Program.wireDepthsWith_gate_castSucc]
      have hold :=
        (Program.wireDepthsWith_append_castAdd (q.simulate impl).1
            ((q.simulate impl).2 ∘ line.wires) w (impl line.op).program
            ((q.simulate impl).2 u)).trans_le
          (ih u)
      cases u <;> exact hold

private theorem depthWith_simulate_le {σ τ : Signature} {n m : ℕ}
    (c : Circuit σ n m) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (w : τ.Op → ℕ) :
    (c.simulate impl).depthWith w ≤ c.depthWith fun op ↦ (impl op).depthWith w :=
  (Circuit.depthWith_le_iff w _).2 fun j ↦
    (wireDepthsWith_simulateRenaming_le c.program impl w (c.outputs j)).trans
      (c.wireDepthsWith_outputs_le_depthWith _ j)

private theorem fanInAtMost_simulate {σ τ : Signature} {n m r s : ℕ}
    (c : Circuit σ n m) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (hc : c.FanInAtMost r) (himpl : ∀ op, σ.Arity op ≤ r → (impl op).FanInAtMost s) :
    (c.simulate impl).FanInAtMost s := by
  suffices ∀ {g : ℕ} (p : Program σ n g), p.FanInAtMost r →
      (p.simulateProgram impl).FanInAtMost s from this c.program hc
  intro g p hp
  induction p with
  | empty => trivial
  | gate q line ih =>
    exact (ih hp.1).append (himpl line.op hp.2)

/-- **Transitivity of $\mathrm{NC}^1$-reducibility**: if `A ∈ NC1Oracle B` and `B ∈ NC1Oracle C`,
then `A ∈ NC1Oracle C`. -/
theorem NC1Oracle.trans {A B C : Language Bool}
    (hAB : A ∈ NC1Oracle B) (hBC : B ∈ NC1Oracle C) : A ∈ NC1Oracle C := by
  obtain ⟨CA, c₁, s₁, hs₁, hCA⟩ := hAB
  obtain ⟨CB, c₂, s₂, hs₂, hCB⟩ := hBC
  obtain ⟨a₂, d₂, hcd₂⟩ := polynomiallyBounded_iff_le.1 hs₂
  let impl : ∀ op : oracleSignature.Op, Circuit oracleSignature (oracleSignature.Arity op) 1
    | .base op => Circuit.oneGate (.base op) id
    | .query q => CB q
  let K := max 1 c₂
  let bound (n : ℕ) : ℕ := (s₁ n + 1) * (2 + a₂ * (s₁ n + 1) ^ d₂)
  refine ⟨fun n ↦ (CA n).simulate impl, K * c₁, bound, by fun_prop,
    fun n ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · have hfan := Program.fanInAtMost_iff.1 (hCA n).2.1
    rw [Circuit.size_simulate, Program.cost_eq_sum]
    have hstep (idx : Fin (CA n).size) :
        (impl ((CA n).program.lines idx).op).size ≤ 2 + a₂ * (s₁ n + 1) ^ d₂ := by
      have hidx := hfan idx
      revert hidx
      cases ((CA n).program.lines idx).op with
      | base op => intro _; simp [impl]; omega
      | query q =>
        intro hq
        have hq' : (CB q).size ≤ a₂ * (s₁ n + 1) ^ d₂ :=
          (hCB q).1.trans ((hcd₂ q).trans
            (Nat.mul_le_mul_left a₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) d₂)))
        exact hq'.trans (Nat.le_add_left _ 2)
    calc ∑ idx : Fin (CA n).size, (impl ((CA n).program.lines idx).op).size
        ≤ ∑ _idx : Fin (CA n).size, (2 + a₂ * (s₁ n + 1) ^ d₂) :=
          Finset.sum_le_sum fun idx _ ↦ hstep idx
      _ = (CA n).size * (2 + a₂ * (s₁ n + 1) ^ d₂) := by simp
      _ ≤ bound n := Nat.mul_le_mul_right _ ((hCA n).1.trans (Nat.le_succ _))
  · refine (fanInAtMost_simulate (CA n) impl (hCA n).2.1 fun op hop ↦ ?_).mono
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    cases op with
    | base op =>
      rw [Circuit.fanInAtMost_oneGate]
      have h2 : signature.Arity op ≤ 2 := by cases op <;> simp
      exact h2.trans (Nat.le_add_right 2 _)
    | query q =>
      have hq : s₂ q ≤ a₂ * (s₁ n + 1) ^ d₂ :=
        (hcd₂ q).trans (Nat.mul_le_mul_left a₂
          (Nat.pow_le_pow_left (Nat.add_le_add_right hop 1) d₂))
      exact (hCB q).2.1.mono (hq.trans (Nat.le_add_left _ 2))
  · have himpl_depth (op : OracleOp) :
        (impl op).depthWith nc1OracleDepthWeight ≤ K * nc1OracleDepthWeight op := by
      cases op with
      | base op =>
        simp only [impl, Circuit.depthWith_oneGate, nc1OracleDepthWeight_base, mul_one]
        exact le_max_left 1 c₂
      | query q =>
        simp only [impl, nc1OracleDepthWeight_query]
        exact (hCB q).2.2.1.trans (Nat.mul_le_mul_right _ (le_max_right 1 c₂))
    calc ((CA n).simulate impl).depthWith nc1OracleDepthWeight
        ≤ (CA n).depthWith fun op ↦ (impl op).depthWith nc1OracleDepthWeight :=
          depthWith_simulate_le (CA n) impl nc1OracleDepthWeight
      _ ≤ (CA n).depthWith fun op ↦ K * nc1OracleDepthWeight op :=
          (CA n).depthWith_mono himpl_depth
      _ ≤ K * (CA n).depthWith nc1OracleDepthWeight :=
          depthWith_scale_le (CA n) nc1OracleDepthWeight K
      _ ≤ K * (c₁ * (Nat.log 2 n + 1)) := Nat.mul_le_mul_left K (hCA n).2.2.1
      _ = (K * c₁) * (Nat.log 2 n + 1) := (Nat.mul_assoc _ _ _).symm
  · intro x
    rw [(CA n).eval_simulate (I := oracleInterpretation B) (J := oracleInterpretation C) impl
      (fun op ↦ by
        cases op with
        | base op => exact fun y ↦ funext fun _ ↦ rfl
        | query q => exact (hCB q).2.2.2)]
    exact (hCA n).2.2.2 x

end SimulationWeightedDepth

/-! ### Determinant oracle languages and classes $\mathrm{DET}_k$ and $\mathrm{DET}$ -/

/-- Bit width `Nat.size k` used to represent residues in `ZMod k`. -/
@[expose]
def zmodBitWidth (k : ℕ) : ℕ :=
  Nat.size k

/-- An instance of the matrix determinant verification problem over `ZMod k`: a dimension `m`,
a target residue `target : ZMod k`, and an `m × m` matrix `mat` over `ZMod k`. -/
@[ext]
structure DetZModInstance (k : ℕ) where
  /-- Matrix dimension. -/
  m : ℕ
  /-- Target determinant residue in `ZMod k`. -/
  target : ZMod k
  /-- Square matrix over `ZMod k`. -/
  mat : Matrix (Fin m) (Fin m) (ZMod k)

namespace DetZModInstance

/-- Total bit length of an encoded `m × m` determinant instance over `ZMod k`. -/
@[expose]
def encodedLen (k m : ℕ) : ℕ :=
  (m + 1) + zmodBitWidth k + m * m * zmodBitWidth k

theorem encodedLen_eq (k m : ℕ) :
    encodedLen k m = (m + 1) + zmodBitWidth k + m * m * zmodBitWidth k :=
  rfl

/-- Binary encoding of `I : DetZModInstance k`: unary header `1^m 0`, `zmodBitWidth k`-bit target,
and `m^2` matrix entries in row-major order, each of width `zmodBitWidth k`. -/
@[expose]
def encode {k : ℕ} (I : DetZModInstance k) : List Bool :=
  List.replicate I.m true ++ [false] ++
    List.ofFn (encodeBits (zmodBitWidth k) I.target.val) ++
    (List.ofFn fun p : Fin (I.m * I.m) ↦
      List.ofFn (encodeBits (zmodBitWidth k)
        (I.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val)).flatten

theorem encode_eq {k : ℕ} (I : DetZModInstance k) :
    I.encode =
      List.replicate I.m true ++ [false] ++
        List.ofFn (encodeBits (zmodBitWidth k) I.target.val) ++
        (List.ofFn fun p : Fin (I.m * I.m) ↦
          List.ofFn (encodeBits (zmodBitWidth k)
            (I.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val)).flatten :=
  rfl

@[simp]
theorem length_encode {k : ℕ} (I : DetZModInstance k) :
    I.encode.length = encodedLen k I.m := by
  have hflat :
      (List.ofFn fun p : Fin (I.m * I.m) ↦
        List.ofFn (encodeBits (zmodBitWidth k)
          (I.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val)).flatten.length =
        I.m * I.m * zmodBitWidth k := by
    rw [List.length_flatten, List.map_ofFn]
    simp [Function.comp_def]
  simp only [encode, encodedLen, List.length_append, List.length_replicate, List.length_singleton,
    List.length_ofFn, hflat]

private theorem replicate_true_append_false_inj :
    ∀ {m₁ m₂ : ℕ} {r₁ r₂ : List Bool},
      List.replicate m₁ true ++ false :: r₁ = List.replicate m₂ true ++ false :: r₂ →
        m₁ = m₂ ∧ r₁ = r₂
  | 0, 0, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | m₁ + 1, m₂ + 1, r₁, r₂, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, hr⟩ := replicate_true_append_false_inj h
    exact ⟨rfl, hr⟩

private theorem ofFn_flatten_fixed_inj :
    ∀ {n w : ℕ} {f g : Fin n → Fin w → Bool},
      (List.ofFn fun i ↦ List.ofFn (f i)).flatten =
        (List.ofFn fun i ↦ List.ofFn (g i)).flatten → f = g
  | 0, _, _, _, _ => funext fun i ↦ Fin.elim0 i
  | _ + 1, _, f, g, h => by
    simp only [List.ofFn_succ, List.flatten_cons] at h
    have hl : (List.ofFn (f 0)).length = (List.ofFn (g 0)).length := by simp
    obtain ⟨h0, hrest⟩ := List.append_inj h hl
    have hf0 : f 0 = g 0 := funext fun j ↦ by
      have := congrArg (fun l : List Bool ↦ l[j.val]?) h0
      simpa using this
    have hfg := ofFn_flatten_fixed_inj hrest
    funext i
    refine Fin.cases hf0 (fun j ↦ congrFun hfg j) i

theorem encode_injective (k : ℕ) [NeZero k] :
    Function.Injective (encode (k := k)) := by
  intro I₁ I₂ h
  have h' : List.replicate I₁.m true ++ false ::
      (List.ofFn (encodeBits (zmodBitWidth k) I₁.target.val) ++
        (List.ofFn fun p : Fin (I₁.m * I₁.m) ↦
          List.ofFn (encodeBits (zmodBitWidth k)
            (I₁.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val)).flatten) =
      List.replicate I₂.m true ++ false ::
      (List.ofFn (encodeBits (zmodBitWidth k) I₂.target.val) ++
        (List.ofFn fun p : Fin (I₂.m * I₂.m) ↦
          List.ofFn (encodeBits (zmodBitWidth k)
            (I₂.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).val)).flatten) := by
    simpa [encode, List.append_assoc] using h
  obtain ⟨hm, hrest⟩ := replicate_true_append_false_inj h'
  rcases I₁ with ⟨m₁, t₁, M₁⟩
  rcases I₂ with ⟨m₂, t₂, M₂⟩
  dsimp only at hm hrest
  subst hm
  obtain ⟨ht_list, hM_list⟩ := List.append_inj hrest (by simp)
  have hlt_w (z : ZMod k) : z.val < 2 ^ zmodBitWidth k :=
    (ZMod.val_lt z).trans (Nat.lt_size_self k)
  have ht_bits : encodeBits (zmodBitWidth k) t₁.val = encodeBits (zmodBitWidth k) t₂.val :=
    funext fun j ↦ by
      have := congrArg (fun l : List Bool ↦ l[j.val]?) ht_list
      simpa using this
  have ht : t₁ = t₂ := ZMod.val_injective k <| by
    rw [← decodeBits_encodeBits (hlt_w t₁), ← decodeBits_encodeBits (hlt_w t₂), ht_bits]
  have hM_bits := ofFn_flatten_fixed_inj hM_list
  have hM : M₁ = M₂ := by
    ext i j
    have hp := congrFun hM_bits (finProdFinEquiv (i, j))
    simp only [Equiv.symm_apply_apply] at hp
    exact ZMod.val_injective k <| by
      rw [← decodeBits_encodeBits (hlt_w (M₁ i j)), ← decodeBits_encodeBits (hlt_w (M₂ i j)), hp]
  subst ht hM
  rfl

end DetZModInstance

/-- Injective encoding of `DetZModInstance k` as bitstrings (`k ≠ 0`). -/
def encDetZMod (k : ℕ) [NeZero k] : DetZModInstance k ↪ List Bool :=
  ⟨DetZModInstance.encode, DetZModInstance.encode_injective k⟩

/-- The determinant verification oracle language over `ZMod k`: encoded instances `(m, target, M)`
satisfying `M.det = target`. -/
@[expose]
def detZModLanguage (k : ℕ) : Language Bool :=
  {w : List Bool | ∃ I : DetZModInstance k, I.encode = w ∧ I.mat.det = I.target}

theorem mem_detZModLanguage_encode {k : ℕ} [NeZero k] (I : DetZModInstance k) :
    I.encode ∈ detZModLanguage k ↔ I.mat.det = I.target := by
  exact ⟨fun ⟨J, hJ, hdet⟩ ↦ DetZModInstance.encode_injective k hJ ▸ hdet, fun h ↦ ⟨I, rfl, h⟩⟩

/-- An instance of the signed bit-graph of the integer determinant: dimension `m`, per-entry
magnitude bit width `entryWidth`, queried output bit index `bitIndex` (`0` for `det < 0`,
`r + 1` for bit `r` of `|det|`), and an integer matrix `mat` with `|mat i j| < 2 ^ entryWidth`. -/
@[ext]
structure DetIntInstance where
  /-- Matrix dimension. -/
  m : ℕ
  /-- Magnitude bit width per matrix entry. -/
  entryWidth : ℕ
  /-- Queried determinant bit index (`0` = sign `det < 0`; `r + 1` = bit `r` of `det.natAbs`). -/
  bitIndex : ℕ
  /-- Square integer matrix. -/
  mat : Matrix (Fin m) (Fin m) ℤ
  /-- Magnitude bound ensuring lossless fixed-width encoding. -/
  entry_lt : ∀ i j, (mat i j).natAbs < 2 ^ entryWidth

namespace DetIntInstance

/-- Total bit length of an encoded `DetIntInstance`. -/
@[expose]
def encodedLen (m entryWidth bitIndex : ℕ) : ℕ :=
  (m + 1) + (entryWidth + 1) + (bitIndex + 1) + m * m * (entryWidth + 1)

theorem encodedLen_eq (m entryWidth bitIndex : ℕ) :
    encodedLen m entryWidth bitIndex =
      (m + 1) + (entryWidth + 1) + (bitIndex + 1) + m * m * (entryWidth + 1) :=
  rfl

/-- Binary encoding of `I : DetIntInstance`: unary headers `1^m 0 1^entryWidth 0 1^bitIndex 0`
followed by `m^2` signed-magnitude blocks of `1 + entryWidth` bits. -/
@[expose]
def encode (I : DetIntInstance) : List Bool :=
  List.replicate I.m true ++ [false] ++
    List.replicate I.entryWidth true ++ [false] ++
    List.replicate I.bitIndex true ++ [false] ++
    (List.ofFn fun p : Fin (I.m * I.m) ↦
      let e := I.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
      List.ofFn (Fin.cons (decide (e < 0)) (encodeBits I.entryWidth e.natAbs))).flatten

theorem encode_eq (I : DetIntInstance) :
    I.encode =
      List.replicate I.m true ++ [false] ++
        List.replicate I.entryWidth true ++ [false] ++
        List.replicate I.bitIndex true ++ [false] ++
        (List.ofFn fun p : Fin (I.m * I.m) ↦
          let e := I.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
          List.ofFn (Fin.cons (decide (e < 0)) (encodeBits I.entryWidth e.natAbs))).flatten :=
  rfl

@[simp]
theorem length_encode (I : DetIntInstance) :
    I.encode.length = encodedLen I.m I.entryWidth I.bitIndex := by
  have hflat :
      (List.ofFn fun p : Fin (I.m * I.m) ↦
        let e := I.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
        List.ofFn (Fin.cons (decide (e < 0)) (encodeBits I.entryWidth e.natAbs))).flatten.length =
        I.m * I.m * (I.entryWidth + 1) := by
    rw [List.length_flatten, List.map_ofFn]
    simp [Function.comp_def]
  simp only [encode, encodedLen, List.length_append, List.length_replicate, List.length_singleton,
    hflat]
  omega

private theorem int_eq_of_sign_natAbs {z₁ z₂ : ℤ}
    (hs : decide (z₁ < 0) = decide (z₂ < 0)) (ha : z₁.natAbs = z₂.natAbs) : z₁ = z₂ := by
  by_cases h₁ : z₁ < 0 <;> by_cases h₂ : z₂ < 0 <;> simp_all <;> omega

theorem encode_injective : Function.Injective encode := by
  intro I₁ I₂ h
  have h' :
      List.replicate I₁.m true ++ false ::
        (List.replicate I₁.entryWidth true ++ false ::
          (List.replicate I₁.bitIndex true ++ false ::
            (List.ofFn fun p : Fin (I₁.m * I₁.m) ↦
              let e := I₁.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
              List.ofFn (Fin.cons (decide (e < 0))
                (encodeBits I₁.entryWidth e.natAbs))).flatten)) =
      List.replicate I₂.m true ++ false ::
        (List.replicate I₂.entryWidth true ++ false ::
          (List.replicate I₂.bitIndex true ++ false ::
            (List.ofFn fun p : Fin (I₂.m * I₂.m) ↦
              let e := I₂.mat (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
              List.ofFn (Fin.cons (decide (e < 0))
                (encodeBits I₂.entryWidth e.natAbs))).flatten)) := by
    simpa [encode, List.append_assoc] using h
  obtain ⟨hm, hr₁⟩ := DetZModInstance.replicate_true_append_false_inj h'
  obtain ⟨hw, hr₂⟩ := DetZModInstance.replicate_true_append_false_inj hr₁
  obtain ⟨hb, hr₃⟩ := DetZModInstance.replicate_true_append_false_inj hr₂
  rcases I₁ with ⟨m₁, w₁, b₁, M₁, hlt₁⟩
  rcases I₂ with ⟨m₂, w₂, b₂, M₂, hlt₂⟩
  dsimp only at hm hw hb hr₃
  subst hm hw hb
  have hblocks := DetZModInstance.ofFn_flatten_fixed_inj hr₃
  have hM : M₁ = M₂ := by
    ext i j
    have hp := congrFun hblocks (finProdFinEquiv (i, j))
    simp only [Equiv.symm_apply_apply] at hp
    have hsign : decide (M₁ i j < 0) = decide (M₂ i j < 0) := by
      have := congrFun hp 0
      simpa using this
    have hmag_bits : encodeBits w₁ (M₁ i j).natAbs = encodeBits w₁ (M₂ i j).natAbs :=
      funext fun t ↦ by
        have := congrFun hp t.succ
        simpa using this
    have hmag : (M₁ i j).natAbs = (M₂ i j).natAbs := by
      rw [← decodeBits_encodeBits (hlt₁ i j), ← decodeBits_encodeBits (hlt₂ i j), hmag_bits]
    exact int_eq_of_sign_natAbs hsign hmag
  subst hM
  rfl

/-- Queried bit of `I.mat.det`: `0` tests `I.mat.det < 0`, `r + 1` tests bit `r` of
`I.mat.det.natAbs`. -/
@[expose]
def verdict (I : DetIntInstance) : Bool :=
  match I.bitIndex with
  | 0 => decide (I.mat.det < 0)
  | r + 1 => decide ((I.mat.det.natAbs / 2 ^ r) % 2 = 1)

@[simp]
theorem verdict_mk_zero (m entryWidth : ℕ) (mat : Matrix (Fin m) (Fin m) ℤ)
    (hlt : ∀ i j, (mat i j).natAbs < 2 ^ entryWidth) :
    (⟨m, entryWidth, 0, mat, hlt⟩ : DetIntInstance).verdict = decide (mat.det < 0) :=
  rfl

@[simp]
theorem verdict_mk_succ (m entryWidth r : ℕ) (mat : Matrix (Fin m) (Fin m) ℤ)
    (hlt : ∀ i j, (mat i j).natAbs < 2 ^ entryWidth) :
    (⟨m, entryWidth, r + 1, mat, hlt⟩ : DetIntInstance).verdict =
      decide ((mat.det.natAbs / 2 ^ r) % 2 = 1) :=
  rfl

end DetIntInstance

/-- Injective encoding of `DetIntInstance` as bitstrings. -/
def encDetInt : DetIntInstance ↪ List Bool :=
  ⟨DetIntInstance.encode, DetIntInstance.encode_injective⟩

/-- The integer matrix determinant bit-graph oracle language over `Bool`. -/
@[expose]
def detIntLanguage : Language Bool :=
  {w : List Bool | ∃ I : DetIntInstance, I.encode = w ∧ I.verdict = true}

theorem mem_detIntLanguage_encode (I : DetIntInstance) :
    I.encode ∈ detIntLanguage ↔ I.verdict = true := by
  exact ⟨fun ⟨J, hJ, hv⟩ ↦ DetIntInstance.encode_injective hJ ▸ hv, fun h ↦ ⟨I, rfl, h⟩⟩

/-- **$\mathrm{DET}_k$**: languages $\mathrm{NC}^1$-reducible to computing the determinant over
`ZMod k`.
-/
@[expose]
def DETk (k : ℕ) : Set (Language Bool) :=
  NC1Oracle (detZModLanguage k)

/-- **$\mathrm{DET}$**: languages $\mathrm{NC}^1$-reducible to computing the integer determinant
over `ℤ`.
-/
@[expose]
def DET : Set (Language Bool) :=
  NC1Oracle detIntLanguage

/-- Encoded decision problems `A : Set α` (with encoding `enc : α ↪ List Bool`) belonging to
$\mathrm{DET}_k$. -/
@[expose]
def DETkOn (k : ℕ) {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ L ∈ DETk k, ∀ a, a ∈ A ↔ enc a ∈ L}

/-- Encoded decision problems `A : Set α` (with encoding `enc : α ↪ List Bool`) belonging to
$\mathrm{DET}$. -/
@[expose]
def DETOn {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ L ∈ DET, ∀ a, a ∈ A ↔ enc a ∈ L}

@[simp]
theorem mem_DETkOn_encBits_iff {k : ℕ} {A : Language Bool} :
    (A : Set (List Bool)) ∈ DETkOn k Turing.MultiTapeTM.encBits ↔ A ∈ DETk k := by
  exact ⟨fun ⟨L, hL, h⟩ ↦ (Language.ext fun w ↦ h w : A = L) ▸ hL,
   fun hA ↦ ⟨A, hA, fun _ ↦ Iff.rfl⟩⟩

@[simp]
theorem mem_DETOn_encBits_iff {A : Language Bool} :
    (A : Set (List Bool)) ∈ DETOn Turing.MultiTapeTM.encBits ↔ A ∈ DET := by
  exact ⟨fun ⟨L, hL, h⟩ ↦ (Language.ext fun w ↦ h w : A = L) ▸ hL,
   fun hA ↦ ⟨A, hA, fun _ ↦ Iff.rfl⟩⟩

/-! ### List `ofFn` block-decomposition helpers and single-literal determinant compiler -/

theorem ofFn_comp_cast {α : Type*} {a b : ℕ} (h : a = b) (g : Fin b → α) :
    List.ofFn (fun i : Fin a ↦ g (Fin.cast h i)) = List.ofFn g := by
  subst h
  rfl

theorem ofFn_addCases {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
    List.ofFn (Fin.addCases f g) = List.ofFn f ++ List.ofFn g := by
  induction m with
  | zero =>
    rw [List.ofFn_zero, List.nil_append, ← ofFn_comp_cast (Nat.zero_add n).symm]
    congr 1
    funext j
    have hj : Fin.cast (Nat.zero_add n).symm j = Fin.natAdd 0 j := Fin.ext (by simp)
    rw [hj]
    exact Fin.addCases_right j
  | succ m ih =>
    have hlen : m + n + 1 = m + 1 + n := by omega
    rw [← ofFn_comp_cast hlen, List.ofFn_succ, List.ofFn_succ, List.cons_append,
      ← ih (fun i ↦ f i.succ)]
    refine congrArg₂ List.cons ?_ (congrArg List.ofFn (funext fun i ↦ ?_))
    · have h0 : Fin.cast hlen 0 = Fin.castAdd n (0 : Fin (m + 1)) := Fin.ext rfl
      rw [h0, Fin.addCases_left]
    · refine Fin.addCases ?_ ?_ i
      · intro i₀
        have h₁ : Fin.cast hlen (Fin.castAdd n i₀).succ = Fin.castAdd n i₀.succ := Fin.ext rfl
        rw [h₁, Fin.addCases_left, Fin.addCases_left]
      · intro j₀
        have h₂ : Fin.cast hlen (Fin.natAdd m j₀).succ = Fin.natAdd (m + 1) j₀ :=
          Fin.ext (by simp; omega)
        rw [h₂, Fin.addCases_right, Fin.addCases_right]

theorem ofFn_decide_lt (m : ℕ) :
    List.ofFn (fun i : Fin (m + 1) ↦ decide (i.val < m)) =
      List.replicate m true ++ [false] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ, List.replicate_succ, List.cons_append]
    simp only [Fin.val_zero, Nat.zero_lt_succ, decide_true, List.cons.injEq, true_and]
    rw [← ih]
    exact congrArg List.ofFn (funext fun i ↦ by simp [Fin.val_succ])

theorem ofFn_mul_eq_flatten {α : Type*} {K w : ℕ} (hw : 0 < w) (F : Fin K → Fin w → α) :
    List.ofFn (fun p : Fin (K * w) ↦
      F ⟨p.val / w, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
        ⟨p.val % w, Nat.mod_lt _ hw⟩) =
      (List.ofFn fun q : Fin K ↦ List.ofFn (F q)).flatten := by
  induction K with
  | zero =>
    have h0 : 0 * w = 0 := Nat.zero_mul w
    rw [← ofFn_comp_cast h0.symm]
    simp
  | succ K ih =>
    rw [List.ofFn_succ, List.flatten_cons, ← ih (fun i ↦ F i.succ)]
    have hlen : w + K * w = (K + 1) * w := by ring
    rw [← ofFn_comp_cast hlen]
    have hsplit :
        (fun x : Fin (w + K * w) ↦
          F ⟨(Fin.cast hlen x).val / w,
              Nat.div_lt_of_lt_mul (by have hx := (Fin.cast hlen x).isLt; nlinarith)⟩
            ⟨(Fin.cast hlen x).val % w, Nat.mod_lt _ hw⟩) =
        Fin.addCases (F 0) (fun r : Fin (K * w) ↦
          F (⟨r.val / w, Nat.div_lt_of_lt_mul (by have hr := r.isLt; nlinarith)⟩ : Fin K).succ
            ⟨r.val % w, Nat.mod_lt _ hw⟩) := by
      funext x
      refine Fin.addCases ?_ ?_ x
      · intro t
        rw [Fin.addCases_left]
        simp only [Fin.val_cast, Fin.val_castAdd]
        have hdiv : t.val / w = 0 := Nat.div_eq_of_lt t.isLt
        have hmod : t.val % w = t.val := Nat.mod_eq_of_lt t.isLt
        congr 1 <;> ext <;> simp [hdiv, hmod]
      · intro r
        rw [Fin.addCases_right]
        simp only [Fin.val_cast, Fin.val_natAdd]
        have hdiv : (w + r.val) / w = r.val / w + 1 := by
          rw [Nat.add_comm]
          exact Nat.add_div_right r.val hw
        have hmod : (w + r.val) % w = r.val % w := Nat.add_mod_left w r.val
        congr 1 <;> ext <;> simp [hdiv, hmod]
    rw [hsplit, ofFn_addCases]

/-- Specification of an `m × m` matrix over `ZMod k` on `n` Boolean inputs whose `(i, j)`-entry
depends on at most one input wire `readIdx i j : Option (Fin n)`. -/
@[ext]
structure SingleVarMatrixSpec (k n m : ℕ) where
  /-- Input coordinate (if any) read by entry `(i, j)`. -/
  readIdx : Fin m → Fin m → Option (Fin n)
  /-- Entry value when `readIdx i j = none` or when the read bit is `false`. -/
  valFalse : Fin m → Fin m → ZMod k
  /-- Entry value when `readIdx i j = some idx` and `x idx = true`. -/
  valTrue : Fin m → Fin m → ZMod k

namespace SingleVarMatrixSpec

/-- Evaluate a `SingleVarMatrixSpec` at input `x : Fin n → Bool`. -/
@[expose]
def eval {k n m : ℕ} (S : SingleVarMatrixSpec k n m) (x : Fin n → Bool) :
    Matrix (Fin m) (Fin m) (ZMod k) :=
  fun i j ↦
    match S.readIdx i j with
    | none => S.valFalse i j
    | some idx => if x idx then S.valTrue i j else S.valFalse i j

theorem eval_apply {k n m : ℕ} (S : SingleVarMatrixSpec k n m) (x : Fin n → Bool)
    (i j : Fin m) :
    S.eval x i j =
      match S.readIdx i j with
      | none => S.valFalse i j
      | some idx => if x idx then S.valTrue i j else S.valFalse i j :=
  rfl

@[simp]
theorem eval_of_readIdx_eq_none {k n m : ℕ} (S : SingleVarMatrixSpec k n m) (x : Fin n → Bool)
    {i j : Fin m} (h : S.readIdx i j = none) :
    S.eval x i j = S.valFalse i j := by
  simp [eval, h]

@[simp]
theorem eval_of_readIdx_eq_some {k n m : ℕ} (S : SingleVarMatrixSpec k n m) (x : Fin n → Bool)
    {i j : Fin m} {idx : Fin n} (h : S.readIdx i j = some idx) :
    S.eval x i j = if x idx then S.valTrue i j else S.valFalse i j := by
  simp [eval, h]

end SingleVarMatrixSpec

/-- Parallel layer of `n` negation gates producing `!x 0, …, !x (n - 1)`. -/
def notLayer (n : ℕ) : Circuit oracleSignature n n :=
  Circuit.pi fun i ↦ Circuit.oneGate (.base .not) (fun _ ↦ i)

@[simp]
theorem eval_notLayer (O : Language Bool) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (notLayer n).eval (oracleInterpretation O) x i = !x i := by
  simp [notLayer, interpretation]

@[simp]
theorem size_notLayer (n : ℕ) : (notLayer n).size = n := by
  simp [notLayer]

theorem fanInAtMost_notLayer (n : ℕ) {r : ℕ} (hr : 1 ≤ r) : (notLayer n).FanInAtMost r :=
  Circuit.fanInAtMost_pi fun _ ↦ (Circuit.fanInAtMost_oneGate _ _ _).2 hr

theorem depthWith_notLayer_le (n : ℕ) :
    (notLayer n).depthWith nc1OracleDepthWeight ≤ 1 :=
  Circuit.depthWith_pi_le _ _ fun _ ↦ by simp

/-- Inputs followed by constant `false` and `true` gates over `oracleSignature`. -/
def constBank (K : ℕ) : Circuit oracleSignature K (K + 2) :=
  (Circuit.id oracleSignature K).append
    ((Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const false)) Fin.elim0).append
      (Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const true)) Fin.elim0))

/-- Wire index in `constBank K` corresponding to `s : Source K`. -/
@[expose]
def sourceWire {K : ℕ} : Source K → Fin (K + 2)
  | .inl i => Fin.castAdd 2 i
  | .inr false => Fin.natAdd K (Fin.castAdd 1 (0 : Fin 1))
  | .inr true => Fin.natAdd K (Fin.natAdd 1 (0 : Fin 1))

@[simp]
theorem eval_constBank_sourceWire (O : Language Bool) {K : ℕ} (x : Fin K → Bool) (s : Source K) :
    (constBank K).eval (oracleInterpretation O) x (sourceWire s) = s.elim x id := by
  rcases s with i | b
  · simp [constBank, sourceWire, Circuit.eval_append, Fin.append_left]
  · cases b <;>
      simp only [constBank, sourceWire, Circuit.eval_append, Fin.append_right, Fin.append_left,
        Circuit.eval_oneGate, oracleInterpretation_base, interpretation, Sum.elim_inr, id_eq]

@[simp]
theorem size_constBank (K : ℕ) : (constBank K).size = 2 := by
  simp [constBank]

theorem fanInAtMost_constBank (K r : ℕ) : (constBank K).FanInAtMost r :=
  (Circuit.fanInAtMost_wiring _ _).append <|
    ((Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _)).append
      ((Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _))

theorem depthWith_constBank_nc1_le (K : ℕ) :
    (constBank K).depthWith nc1OracleDepthWeight ≤ 1 := by
  unfold constBank
  refine (Circuit.depthWith_append_le _ _ _).trans (max_le (by simp) ?_)
  exact (Circuit.depthWith_append_le _ _ _).trans (max_le (by simp) (by simp))

/-- Literal bank `(x, !x, false, true)` of width `n + n + 2` built from `constBank (n + n)` on
`id.append (notLayer n)`. -/
def literalBank (n : ℕ) : Circuit oracleSignature n (n + n + 2) :=
  (constBank (n + n)).comp ((Circuit.id oracleSignature n).append (notLayer n))

/-- Select the `Source (n + n)` realizing `if x idx then bTrue else bFalse` from `(x, !x)`. -/
def singleVarSource {n : ℕ} (optIdx : Option (Fin n)) (bFalse bTrue : Bool) : Source (n + n) :=
  match optIdx with
  | none => .inr bFalse
  | some idx =>
    match bFalse, bTrue with
    | false, false => .inr false
    | true, true => .inr true
    | false, true => .inl (Fin.castAdd n idx)
    | true, false => .inl (Fin.natAdd n idx)

theorem eval_literalBank_singleVarSource (O : Language Bool) {n : ℕ}
    (x : Fin n → Bool) (optIdx : Option (Fin n)) (bFalse bTrue : Bool) :
    (literalBank n).eval (oracleInterpretation O) x
        (sourceWire (singleVarSource optIdx bFalse bTrue)) =
      match optIdx with
      | none => bFalse
      | some idx => if x idx then bTrue else bFalse := by
  simp only [literalBank, Circuit.eval_comp, eval_constBank_sourceWire]
  cases optIdx with
  | none => rfl
  | some idx =>
    cases bFalse <;> cases bTrue <;> rcases Bool.eq_false_or_eq_true (x idx) with h | h
    · simp [singleVarSource, h]
    · simp [singleVarSource, h]
    · simp only [singleVarSource, Sum.elim_inl, Circuit.eval_append, Fin.append_left]
      simp [Circuit.id, h]
    · simp only [singleVarSource, Sum.elim_inl, Circuit.eval_append, Fin.append_left]
      simp [Circuit.id, h]
    · simp only [singleVarSource, Sum.elim_inl, Circuit.eval_append, Fin.append_right,
        eval_notLayer, h]
      rfl
    · simp only [singleVarSource, Sum.elim_inl, Circuit.eval_append, Fin.append_right,
        eval_notLayer, h]
      rfl
    · simp [singleVarSource, h]
    · simp [singleVarSource, h]

/-- Wire-source map of length `DetZModInstance.encodedLen k m` encoding `(m, target, S.eval x)` from
`literalBank n`. -/
def detZModQuerySources {k n m : ℕ} (S : SingleVarMatrixSpec k n m) (target : ZMod k) :
    Fin (DetZModInstance.encodedLen k m) → Source (n + n) :=
  let w := zmodBitWidth k
  Fin.addCases
    (Fin.addCases
      (fun i : Fin (m + 1) ↦ .inr (decide (i.val < m)))
      (fun t : Fin w ↦ .inr (encodeBits w target.val t)))
    (fun p : Fin (m * m * w) ↦
      let q : Fin (m * m) :=
        ⟨p.val / w, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
      let t : Fin w := ⟨p.val % w, Nat.mod_lt _ (Nat.pos_of_ne_zero fun hw ↦ by
        rw [hw, Nat.mul_zero] at p; exact Fin.elim0 p)⟩
      let ij := finProdFinEquiv.symm q
      singleVarSource (S.readIdx ij.1 ij.2)
        (encodeBits w (S.valFalse ij.1 ij.2).val t)
        (encodeBits w (S.valTrue ij.1 ij.2).val t))

private theorem list_ofFn_detZModQuerySources {k n m : ℕ} [NeZero k]
    (S : SingleVarMatrixSpec k n m) (target : ZMod k) (O : Language Bool) (x : Fin n → Bool) :
    List.ofFn (fun a ↦ (literalBank n).eval (oracleInterpretation O) x
      (sourceWire (detZModQuerySources S target a))) =
      (⟨m, target, S.eval x⟩ : DetZModInstance k).encode := by
  let w := zmodBitWidth k
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun hw0 ↦ by
    have := Nat.lt_size_self k
    rw [show Nat.size k = 0 from hw0] at this
    omega
  let evalSrc (s : Source (n + n)) : Bool :=
    (literalBank n).eval (oracleInterpretation O) x (sourceWire s)
  change List.ofFn (fun a : Fin ((m + 1) + w + m * m * w) ↦
    evalSrc (detZModQuerySources S target a)) = _
  have hcomp :
      (fun a : Fin ((m + 1) + w + m * m * w) ↦ evalSrc (detZModQuerySources S target a)) =
      Fin.addCases
        (Fin.addCases
          (fun i : Fin (m + 1) ↦ decide (i.val < m))
          (encodeBits w target.val))
        (fun p : Fin (m * m * w) ↦
          let q : Fin (m * m) :=
            ⟨p.val / w, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
          let t : Fin w := ⟨p.val % w, Nat.mod_lt _ hw_pos⟩
          encodeBits w ((S.eval x) (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).val t)
            := by
    funext a
    refine Fin.addCases ?_ ?_ a
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i₀
        change evalSrc (detZModQuerySources S target
          (Fin.castAdd (m * m * w) (Fin.castAdd w i₀))) = _
        unfold detZModQuerySources
        rw [Fin.addCases_left, Fin.addCases_left, Fin.addCases_left, Fin.addCases_left]
        exact eval_literalBank_singleVarSource O x none
          (decide (i₀.val < m)) (decide (i₀.val < m))
      · intro t₀
        change evalSrc (detZModQuerySources S target
          (Fin.castAdd (m * m * w) (Fin.natAdd (m + 1) t₀))) = _
        unfold detZModQuerySources
        rw [Fin.addCases_left, Fin.addCases_right, Fin.addCases_left, Fin.addCases_right]
        exact eval_literalBank_singleVarSource O x none
          (encodeBits w target.val t₀) (encodeBits w target.val t₀)
    · intro p
      change evalSrc (detZModQuerySources S target (Fin.natAdd ((m + 1) + w) p)) = _
      unfold detZModQuerySources
      rw [Fin.addCases_right, Fin.addCases_right]
      dsimp only [evalSrc, w]
      rw [eval_literalBank_singleVarSource]
      dsimp only [SingleVarMatrixSpec.eval]
      let q : Fin (m * m) :=
        ⟨p.val / zmodBitWidth k, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
      cases S.readIdx (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 with
      | none => rfl
      | some idx =>
        rcases Bool.eq_false_or_eq_true (x idx) with hx | hx <;> simp [hx]
  rw [hcomp, ofFn_addCases, ofFn_addCases, ofFn_decide_lt,
    ofFn_mul_eq_flatten hw_pos (fun q t ↦
      encodeBits w ((S.eval x) (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).val t)]
  rfl

/-- Single-query oracle circuit testing `(S.eval x).det = target` (when `negate = false`) or
`(S.eval x).det ≠ target` (when `negate = true`) over `ZMod k`. -/
def singleLiteralDetCircuit {k n m : ℕ} (S : SingleVarMatrixSpec k n m)
    (target : ZMod k) (negate : Bool) : Circuit oracleSignature n 1 :=
  let qGate : Circuit oracleSignature (n + n + 2) 1 :=
    Circuit.oneGate (σ := oracleSignature) (OracleOp.query (DetZModInstance.encodedLen k m))
      fun a ↦ sourceWire (detZModQuerySources S target a)
  let core : Circuit oracleSignature n 1 := qGate.comp (literalBank n)
  if negate then
    (Circuit.oneGate (σ := oracleSignature) (OracleOp.base .not) (fun _ ↦ 0)).comp core
  else core

theorem eval_singleLiteralDetCircuit {k n m : ℕ} [NeZero k]
    (S : SingleVarMatrixSpec k n m) (target : ZMod k) (negate : Bool)
    (x : Fin n → Bool) :
    (singleLiteralDetCircuit S target negate).eval
        (oracleInterpretation (detZModLanguage k)) x 0 =
      xor negate (decide ((S.eval x).det = target)) := by
  let qGate : Circuit oracleSignature (n + n + 2) 1 :=
    Circuit.oneGate (σ := oracleSignature) (OracleOp.query (DetZModInstance.encodedLen k m))
      fun a ↦ sourceWire (detZModQuerySources S target a)
  have hcore : (qGate.comp (literalBank n)).eval
      (oracleInterpretation (detZModLanguage k)) x 0 =
      decide ((S.eval x).det = target) := by
    simp only [qGate, Circuit.eval_comp, Circuit.eval_oneGate, oracleInterpretation_query]
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff,
      list_ofFn_detZModQuerySources S target (detZModLanguage k) x,
      mem_detZModLanguage_encode, decide_eq_true_eq]
  cases negate
  · simpa [singleLiteralDetCircuit, qGate] using hcore
  · rw [Bool.true_xor]
    change ((Circuit.oneGate (σ := oracleSignature) (OracleOp.base .not) (fun _ ↦ 0)).comp
        (qGate.comp (literalBank n))).eval (oracleInterpretation (detZModLanguage k)) x 0 =
      !(decide ((S.eval x).det = target))
    rw [Circuit.eval_comp, Circuit.eval_oneGate]
    exact congrArg Bool.not hcore

theorem size_singleLiteralDetCircuit_le {k n m : ℕ}
    (S : SingleVarMatrixSpec k n m) (target : ZMod k) (negate : Bool) :
    (singleLiteralDetCircuit S target negate).size ≤ n + 4 := by
  unfold singleLiteralDetCircuit literalBank
  cases negate <;> simp [Circuit.size_comp, Circuit.size_append]

theorem fanInAtMost_singleLiteralDetCircuit {k n m : ℕ}
    (S : SingleVarMatrixSpec k n m) (target : ZMod k) (negate : Bool) :
    (singleLiteralDetCircuit S target negate).FanInAtMost
      (max 2 (DetZModInstance.encodedLen k m)) := by
  have hlit : (literalBank n).FanInAtMost (max 2 (DetZModInstance.encodedLen k m)) :=
    (fanInAtMost_constBank _ _).comp
      ((Circuit.fanInAtMost_wiring _ _).append
        (fanInAtMost_notLayer n (le_trans (by decide : 1 ≤ 2) (le_max_left _ _))))
  have hq : (Circuit.oneGate (σ := oracleSignature)
      (OracleOp.query (DetZModInstance.encodedLen k m))
      fun a ↦ sourceWire (detZModQuerySources S target a)).FanInAtMost
      (max 2 (DetZModInstance.encodedLen k m)) :=
    (Circuit.fanInAtMost_oneGate _ _ _).2 (le_max_right _ _)
  unfold singleLiteralDetCircuit
  cases negate
  · exact hq.comp hlit
  · exact ((Circuit.fanInAtMost_oneGate _ _ _).2
      (le_trans (by decide : 1 ≤ 2) (le_max_left _ _))).comp (hq.comp hlit)

theorem depthWith_singleLiteralDetCircuit_le {k n m : ℕ}
    (S : SingleVarMatrixSpec k n m) (target : ZMod k) (negate : Bool) :
    (singleLiteralDetCircuit S target negate).depthWith nc1OracleDepthWeight ≤
      3 + (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
  have hconst := depthWith_constBank_nc1_le (n + n)
  have hlit : (literalBank n).depthWith nc1OracleDepthWeight ≤ 2 := by
    refine (Circuit.depthWith_comp_le _ _ _).trans ?_
    have happ : ((Circuit.id oracleSignature n).append (notLayer n)).depthWith
        nc1OracleDepthWeight ≤ 1 :=
      (Circuit.depthWith_append_le _ _ _).trans (max_le (by simp) (depthWith_notLayer_le n))
    omega
  let qGate : Circuit oracleSignature (n + n + 2) 1 :=
    Circuit.oneGate (σ := oracleSignature) (OracleOp.query (DetZModInstance.encodedLen k m))
      fun a ↦ sourceWire (detZModQuerySources S target a)
  have hcore : (qGate.comp (literalBank n)).depthWith nc1OracleDepthWeight ≤
      2 + (Nat.log 2 (DetZModInstance.encodedLen k m) + 1) := by
    refine (Circuit.depthWith_comp_le _ _ _).trans ?_
    simp only [qGate, Circuit.depthWith_oneGate, nc1OracleDepthWeight_query]
    omega
  cases negate
  · simpa [singleLiteralDetCircuit, qGate] using hcore.trans (by omega)
  · change ((Circuit.oneGate (σ := oracleSignature) (OracleOp.base .not) (fun _ ↦ 0)).comp
        (qGate.comp (literalBank n))).depthWith nc1OracleDepthWeight ≤ _
    have hcomp := Circuit.depthWith_comp_le nc1OracleDepthWeight
      (Circuit.oneGate (σ := oracleSignature) (OracleOp.base .not) (fun _ ↦ (0 : Fin 1)))
      (qGate.comp (literalBank n))
    have hnot : (Circuit.oneGate (σ := oracleSignature) (OracleOp.base .not)
        (fun _ ↦ (0 : Fin 1))).depthWith nc1OracleDepthWeight = 1 := by
      simp [Circuit.depthWith_oneGate]
    omega

/-! ### Private sanity check -/

section Sanity

private example : detIntLanguage ∈ DET ∧ detZModLanguage 2 ∈ DETk 2 :=
  ⟨self_mem_NC1Oracle detIntLanguage, self_mem_NC1Oracle (detZModLanguage 2)⟩

end Sanity

end Cslib.Complexity
