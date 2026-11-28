/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import CslibFrontier.Probability.PMF.Bool
public import CslibFrontier.Probability.Product

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Asymmetric Binary Readout Channels and Wire-Local Quantum Circuits

Independent single-qubit asymmetric binary readout channels for computational-basis quantum circuit
measurements, together with wire-locality invariants for `Cslib.Quantum.Circuit`:

1. **Asymmetric binary readout channels** (`BinaryReadoutError`, `BinaryReadoutError.channel`,
   `noisyReadout`, `measureCircuitNoisy`): models independent per-qubit classical readout bit-flips
   with distinct false-positive (`false → true`) and false-negative (`true → false`) probabilities
   on `PMF (Fin n → Bool)` via `Cslib.Probability.PMF.pi`.
2. **Marginal commutation and balanced-input bias identities** (`noisyReadout_marginal`,
   `toReal_channel_true_of_balanced`, `toReal_channel_false_sub_true_of_balanced`,
   `toReal_channel_bitflip_of_balanced`): proves that independent multi-qubit readout noise commutes
   with coordinate marginals and characterizes post-readout bit bias, zero-minus-one asymmetry, and
   average bit-flip rate on balanced pre-measurement marginals.
3. **Wire-support locality on quantum circuits** (`PlacedGate.wireSet`, `Circuit.TouchesOnly`,
   `PlacedGate.eval_of_touchesOnly_eq_zero`, `Circuit.run_of_touchesOnly_eq_zero`): proves that
   when all placed gates in a quantum circuit act within a wire subset `S`, computational-basis
   executions assign zero amplitude to any bitstring differing from the initial basis state outside
   `S`.

## Main definitions

* `CslibFrontier.Quantum.BinaryReadoutError`: asymmetric single-qubit binary readout error rates in
  `[0, 1]`.
* `CslibFrontier.Quantum.BinaryReadoutError.channel`: stochastic readout kernel `Bool → PMF Bool`.
* `CslibFrontier.Quantum.noisyReadout`: multi-qubit independent product readout channel on
  `PMF (Fin n → Bool)`.
* `CslibFrontier.Quantum.measureCircuitNoisy`: computational-basis circuit measurement composed with
  independent asymmetric readout noise.
* `CslibFrontier.Quantum.PlacedGate.wireSet`, `CslibFrontier.Quantum.Circuit.TouchesOnly`: finite
  set of wires acted on by a placed gate and wire-locality predicate for quantum circuits.

## Main results

* `CslibFrontier.Quantum.noisyReadout_marginal`: projecting `noisyReadout err p` to qubit `i`
  equals pushing the `i`-th marginal of `p` through `(err i).channel`.
* `CslibFrontier.Quantum.toReal_channel_true_of_balanced`,
  `CslibFrontier.Quantum.toReal_channel_false_sub_true_of_balanced`,
  `CslibFrontier.Quantum.toReal_channel_bitflip_of_balanced`: exact balanced-marginal readout bias,
  zero-minus-one asymmetry, and average bit-flip error formulas.
* `CslibFrontier.Quantum.Circuit.run_of_touchesOnly_eq_zero`: running a wire-local circuit `C` on
  `|x₀⟩` vanishes on every basis state disagreeing with `x₀` outside the active wire set.
-/

public section

noncomputable section

namespace CslibFrontier.Quantum

open Finset
open Cslib.Quantum
open scoped ENNReal

/-- Discrete Bernoulli distribution on `Bool` with `true`-mass `p ∈ [0, 1]`. -/
def bernoulliPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFinset (fun b ↦ if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) Finset.univ
    (by
      have h1 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      rw [Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add hp0 h1]
      ring_nf
      exact ENNReal.ofReal_one)
    (fun _ hx ↦ absurd (Finset.mem_univ _) hx)

/-- Real probability of `true` under `bernoulliPMF`. -/
@[simp]
theorem toReal_bernoulliPMF_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliPMF p hp0 hp1 true).toReal = p := by
  change (ENNReal.ofReal p).toReal = p
  exact ENNReal.toReal_ofReal hp0

/-- Real probability of `false` under `bernoulliPMF`. -/
@[simp]
theorem toReal_bernoulliPMF_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliPMF p hp0 hp1 false).toReal = 1 - p := by
  change (ENNReal.ofReal (1 - p)).toReal = 1 - p
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)

/-- Asymmetric binary readout error parameters `(falseToTrue, trueToFalse) ∈ [0, 1]^2` for a
two-outcome classical measurement channel. -/
@[ext]
structure BinaryReadoutError where
  /-- Probability of reporting `true` given pre-readout bit `false`. -/
  falseToTrue : ℝ
  /-- Probability of reporting `false` given pre-readout bit `true`. -/
  trueToFalse : ℝ
  /-- Nonnegativity of `falseToTrue`. -/
  falseToTrue_nonneg : 0 ≤ falseToTrue
  /-- Upper bound `falseToTrue ≤ 1`. -/
  falseToTrue_le_one : falseToTrue ≤ 1
  /-- Nonnegativity of `trueToFalse`. -/
  trueToFalse_nonneg : 0 ≤ trueToFalse
  /-- Upper bound `trueToFalse ≤ 1`. -/
  trueToFalse_le_one : trueToFalse ≤ 1

/-- Stochastic binary readout kernel `Bool → PMF Bool` induced by `e : BinaryReadoutError`. -/
def BinaryReadoutError.channel (e : BinaryReadoutError) (b : Bool) : PMF Bool :=
  if b then
    bernoulliPMF (1 - e.trueToFalse)
      (sub_nonneg.mpr e.trueToFalse_le_one) (sub_le_self 1 e.trueToFalse_nonneg)
  else
    bernoulliPMF e.falseToTrue e.falseToTrue_nonneg e.falseToTrue_le_one

/-- Conditional probability `Pr[out = true | in = false] = e.falseToTrue`. -/
@[simp]
theorem toReal_channel_false_true (e : BinaryReadoutError) :
    (e.channel false true).toReal = e.falseToTrue := by
  simp only [BinaryReadoutError.channel, Bool.false_eq_true, ite_false, toReal_bernoulliPMF_true]

/-- Conditional probability `Pr[out = true | in = true] = 1 - e.trueToFalse`. -/
@[simp]
theorem toReal_channel_true_true (e : BinaryReadoutError) :
    (e.channel true true).toReal = 1 - e.trueToFalse := by
  simp only [BinaryReadoutError.channel, ite_true, toReal_bernoulliPMF_true]

/-- Multi-qubit independent asymmetric readout noise channel applied to a bitstring distribution
`p : PMF (Fin n → Bool)`. -/
def noisyReadout {n : ℕ} (err : Fin n → BinaryReadoutError)
    (p : PMF (Fin n → Bool)) : PMF (Fin n → Bool) :=
  p.bind fun x ↦ Cslib.Probability.PMF.pi fun i ↦ (err i).channel (x i)

/-- Computational-basis measurement of an `n`-qubit quantum circuit `C` started in `|x₀⟩` followed
by independent per-qubit asymmetric readout noise `err`. -/
def measureCircuitNoisy {n : ℕ} (C : Circuit n) (x₀ : Fin n → Bool)
    (err : Fin n → BinaryReadoutError) : PMF (Fin n → Bool) :=
  noisyReadout err (C.measure x₀)

/-- Independent multi-qubit readout noise commutes with single-qubit coordinate projection: the
`i`-th marginal of `noisyReadout err p` equals the `i`-th marginal of `p` pushed through
`(err i).channel`. -/
theorem noisyReadout_marginal {n : ℕ} (err : Fin n → BinaryReadoutError)
    (p : PMF (Fin n → Bool)) (i : Fin n) :
    (noisyReadout err p).map (fun y ↦ y i) =
      (p.map fun x ↦ x i).bind (err i).channel := by
  unfold noisyReadout
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext x
  exact Cslib.Probability.PMF.pi_map_eval (fun j ↦ (err j).channel (x j)) i

/-- Under a balanced pre-readout marginal `(m true).toReal = 1 / 2`, the post-readout `true`-mass
equals `1 / 2 + (e.falseToTrue - e.trueToFalse) / 2`. -/
theorem toReal_channel_true_of_balanced (e : BinaryReadoutError) (m : PMF Bool)
    (hbal : (m true).toReal = 1 / 2) :
    ((m.bind e.channel) true).toReal =
      1 / 2 + (e.falseToTrue - e.trueToFalse) / 2 := by
  rw [Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool,
    Cslib.Probability.PMF.toReal_false_eq_one_sub, hbal, toReal_channel_true_true,
    toReal_channel_false_true]
  ring

/-- Under a balanced pre-readout marginal `(m true).toReal = 1 / 2`, the post-readout difference
between `false`-mass and `true`-mass equals `e.trueToFalse - e.falseToTrue`. -/
theorem toReal_channel_false_sub_true_of_balanced (e : BinaryReadoutError) (m : PMF Bool)
    (hbal : (m true).toReal = 1 / 2) :
    ((m.bind e.channel) false).toReal - ((m.bind e.channel) true).toReal =
      e.trueToFalse - e.falseToTrue := by
  rw [Cslib.Probability.PMF.toReal_false_eq_one_sub,
    toReal_channel_true_of_balanced e m hbal]
  ring

/-- Under a balanced pre-readout marginal `(m true).toReal = 1 / 2`, the probability that the
post-readout bit differs from the pre-readout bit equals `(e.falseToTrue + e.trueToFalse) / 2`. -/
theorem toReal_channel_bitflip_of_balanced (e : BinaryReadoutError) (m : PMF Bool)
    (hbal : (m true).toReal = 1 / 2) :
    ((m.bind fun b ↦ (e.channel b).map fun b' ↦ b != b') true).toReal =
      (e.falseToTrue + e.trueToFalse) / 2 := by
  rw [Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool,
    Cslib.Probability.PMF.toReal_false_eq_one_sub, hbal]
  have htrue : (((e.channel true).map fun b' ↦ (true != b')) true).toReal = e.trueToFalse := by
    have hfn : (fun b' : Bool ↦ (true != b')) = fun b' : Bool ↦ !b' := by
      funext b'
      cases b' <;> rfl
    have hid : ((e.channel true).map fun b' : Bool ↦ b') = e.channel true :=
      PMF.map_id (e.channel true)
    rw [hfn, Cslib.Probability.PMF.map_not_true, hid]
    have h1 : (1 - e.channel true true).toReal = 1 - (e.channel true true).toReal :=
      ENNReal.toReal_sub_of_le (PMF.coe_le_one _ _) ENNReal.one_ne_top
    rw [h1, toReal_channel_true_true]
    ring
  have hfalse : (((e.channel false).map fun b' ↦ (false != b')) true).toReal = e.falseToTrue := by
    have hfn : (fun b' : Bool ↦ (false != b')) = id := by
      funext b'
      cases b' <;> rfl
    rw [hfn, PMF.map_id, toReal_channel_false_true]
  rw [htrue, hfalse]
  ring

/-- Finite set of qubit wires acted on by a placed gate `g : PlacedGate n`. -/
def PlacedGate.wireSet {n : ℕ} (g : PlacedGate n) : Finset (Fin n) :=
  Finset.univ.map g.wires

/-- Predicate asserting that every placed gate in `C : Circuit n` acts only on wires in `S`. -/
def Circuit.TouchesOnly {n : ℕ} (S : Set (Fin n)) (C : Circuit n) : Prop :=
  ∀ g ∈ C, ∀ i : Fin g.arity, g.wires i ∈ S

/-- If a placed gate `g` acts only on wires in `S` and a state `ψ` vanishes on all bitstrings
disagreeing with `x₀` at wire `j ∉ S`, then `g.eval ψ` preserves that vanishing invariant. -/
theorem PlacedGate.eval_of_wires_mem_eq_zero {n : ℕ} (g : PlacedGate n) {S : Set (Fin n)}
    (hg : ∀ i : Fin g.arity, g.wires i ∈ S) {j : Fin n} (hj : j ∉ S)
    {x₀ : Fin n → Bool} {ψ : Qubits n}
    (hψ : ∀ z : Fin n → Bool, z j ≠ x₀ j → ψ.ofLp z = 0)
    (y : Fin n → Bool) (hy : y j ≠ x₀ j) :
    (g.eval ψ).ofLp y = 0 := by
  simp only [PlacedGate.eval, unitaryEquiv_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rw [PlacedGate.matrix_apply]
  split_ifs with hall
  · have hnot : ¬∃ i : Fin g.arity, g.wires i = j := by
      rintro ⟨i, rfl⟩
      exact hj (hg i)
    have hyz : y j = z j := hall j hnot
    rw [hψ z (hyz ▸ hy), mul_zero]
  · exact zero_mul _

/-- Running a wire-local circuit `C` (`C.TouchesOnly S`) from basis state `|x₀⟩` assigns zero
amplitude to every bitstring `y` differing from `x₀` at any wire `j ∉ S`. -/
theorem Circuit.run_of_touchesOnly_eq_zero {n : ℕ} {S : Set (Fin n)} {C : Circuit n}
    (hC : Circuit.TouchesOnly S C) {j : Fin n} (hj : j ∉ S)
    (x₀ y : Fin n → Bool) (hy : y j ≠ x₀ j) :
    (C.run x₀).ofLp y = 0 := by
  suffices ∀ ψ : Qubits n,
      (∀ z : Fin n → Bool, z j ≠ x₀ j → ψ.ofLp z = 0) →
        ∀ z : Fin n → Bool, z j ≠ x₀ j → (C.eval ψ).ofLp z = 0 by
    refine this (ket x₀) (fun z hz ↦ ?_) y hy
    rw [ket_apply]
    split_ifs with hzx
    · exact absurd (congrFun hzx j) hz
    · rfl
  intro ψ hψ
  induction C generalizing ψ with
  | nil =>
    intro z hz
    simpa only [Circuit.eval_nil] using hψ z hz
  | cons g D ih =>
    have hg : ∀ i : Fin g.arity, g.wires i ∈ S := fun i ↦ hC g List.mem_cons_self i
    have hD : Circuit.TouchesOnly S D := fun g' hg' i ↦
      hC g' (List.mem_cons_of_mem g hg') i
    intro z hz
    rw [Circuit.eval_cons]
    exact ih hD (g.eval ψ) (PlacedGate.eval_of_wires_mem_eq_zero g hg hj hψ) z hz

end CslibFrontier.Quantum
