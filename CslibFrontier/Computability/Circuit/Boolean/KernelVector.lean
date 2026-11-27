/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Full
public import CslibFrontier.Computability.Circuit.LinearSolve
public import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import Mathlib.Tactic.Linarith

/-!
# De Morgan Boolean circuit complexity of elimination over `ZMod 2`

`CslibFrontier.Computability.Circuit.KernelVector` and
`CslibFrontier.Computability.Circuit.LinearSolve` bound the straight-line gate complexity of
`Cslib.LinearAlgebra.kernelVec`, `Cslib.LinearAlgebra.kernelVecAt`, and
`Cslib.LinearAlgebra.vecMulSolve` over the full binary basis `fullInterpretation (k := 2)` of any
field `F`. Over `F = ZMod 2`, conjugating `fullInterpretation (k := 2)` by the ring equivalence
`Cslib.BitString.bitEquiv : ZMod 2 ≃+* Bool` yields a circuit homomorphism into `2`-input Boolean
operations, each of which is synthesized in the standard De Morgan basis
`Cslib.Circuits.Boolean.interpretation` with at most `25` gates via
`Cslib.Circuits.Synthesis.selected`.

This module packages that homomorphism-and-simulation bridge (`complexity_boolean_of_fullTwo_zmod2`)
and derives explicit polynomial multi-output De Morgan Boolean circuit complexity bounds
`O((r + 1) * (n + 1) ^ 2)` for extracting a nonzero right-kernel vector (`kernelVec`), a
prescribed-pivot kernel vector (`kernelVecAt`), and a linear system solution (`vecMulSolve`) from
bit-encoded binary matrices.

## Main definitions

* `Cslib.Circuits.zmod2FullOnBool`: conjugation of `fullInterpretation (k := 2)` on `ZMod 2` onto
  `Bool` along `Cslib.BitString.bitEquiv`.
* `Cslib.Circuits.bitEquivHomomorphism`: circuit homomorphism from `fullInterpretation (k := 2)` on
  `ZMod 2` to `zmod2FullOnBool`.

## Main results

* `Cslib.Circuits.boolean_simulatesWithCost_fullTwo`: `Boolean.interpretation` simulates
  `fullInterpretation (Carrier := Bool) (k := 2)` with cost `25` per gate.
* `Cslib.Circuits.complexity_boolean_of_fullTwo_zmod2`: any family over `ZMod 2` synthesized in
  `fullInterpretation (k := 2)` with `cost` gates has De Morgan Boolean circuit complexity at most
  `25 * cost`.
* `Cslib.Circuits.complexity_boolean_kernelVec_le`: De Morgan circuit complexity at most
  `25 * kernelVecCost r n` for `Cslib.LinearAlgebra.kernelVec` over `ZMod 2`.
* `Cslib.Circuits.complexity_boolean_kernelVecAt_le`: De Morgan circuit complexity at most
  `25 * kernelVecCost r n` for `Cslib.LinearAlgebra.kernelVecAt` over `ZMod 2`.
* `Cslib.Circuits.complexity_boolean_vecMulSolve_le`: De Morgan circuit complexity at most
  `25 * (kernelVecCost n (r + 1) + r)` for `Cslib.LinearAlgebra.vecMulSolve` over `ZMod 2`.
-/

public section

namespace Cslib.Circuits

open Cslib.LinearAlgebra

/-- Conjugation of `fullInterpretation (k := 2)` from `ZMod 2` onto `Bool` via
`Cslib.BitString.bitEquiv`. -/
def zmod2FullOnBool :
    Interpretation (fullSignature (Carrier := ZMod 2) 2) Bool :=
  fun op args =>
    Cslib.BitString.bitEquiv
      (fullInterpretation (k := 2) op (Cslib.BitString.bitEquiv.symm ∘ args))

/-- `Cslib.BitString.bitEquiv` is a circuit homomorphism from `fullInterpretation (k := 2)` on
`ZMod 2` to `zmod2FullOnBool` on `Bool`. -/
def bitEquivHomomorphism :
    Homomorphism (fullInterpretation (Carrier := ZMod 2) (k := 2)) zmod2FullOnBool where
  map := Cslib.BitString.bitEquiv
  homomorphic op input := by
    simp only [zmod2FullOnBool]
    congr 2
    funext i
    exact (Cslib.BitString.bitEquiv.symm_apply_apply (input i)).symm

/-- Every operation in `fullInterpretation (Carrier := Bool) (k := 2)` can be simulated in the
standard De Morgan basis `Boolean.interpretation` with at most `25` gates. -/
theorem boolean_simulatesWithCost_fullTwo :
    Boolean.interpretation.SimulatesWithCost
      (fullInterpretation (Carrier := Bool) (k := 2)) (fun _ => 25) := by
  intro op
  cases op with
  | con value =>
    obtain ⟨c, hc, hsize⟩ :=
      (Synthesis.of_forall_eq_const (s := inputs 0) value (fun _ => rfl)).exists_circuit
    exact ⟨c, hc, hsize.trans (by dsimp only; decide)⟩
  | fn g =>
    exact (Synthesis.selected id g).exists_circuit

/-- `Boolean.interpretation` simulates `zmod2FullOnBool` with at most `25` gates per operation. -/
theorem boolean_simulatesWithCost_zmod2FullOnBool :
    Boolean.interpretation.SimulatesWithCost zmod2FullOnBool (fun _ => 25) := by
  intro op
  cases op with
  | con value =>
    obtain ⟨c, hc, hsize⟩ :=
      (Synthesis.of_forall_eq_const (s := inputs 0) (Cslib.BitString.bitEquiv value)
        (fun _ => rfl)).exists_circuit
    exact ⟨c, hc, hsize.trans (by dsimp only; decide)⟩
  | fn g =>
    exact (Synthesis.selected id (zmod2FullOnBool (.fn g))).exists_circuit

/-- **Algebraic-to-Boolean circuit simulation over `ZMod 2`.** Any family
`F : Fin M → (Fin N → ZMod 2) → ZMod 2` synthesized in `fullInterpretation (k := 2)` with gate
budget `cost` has multi-output De Morgan Boolean circuit complexity at most `25 * cost`. -/
theorem complexity_boolean_of_fullTwo_zmod2 {N M cost : ℕ}
    {F : Fin M → (Fin N → ZMod 2) → ZMod 2}
    (h : Synthesis (fullInterpretation (Carrier := ZMod 2) (k := 2))
      (inputs N) (Set.range F) cost) :
    complexity Boolean.interpretation
      (fun (x : Fin N → Bool) (j : Fin M) =>
        Cslib.BitString.bitEquiv (F j (Cslib.BitString.bitEquiv.symm ∘ x))) ≤
      25 * cost := by
  obtain ⟨c, hc, hsize⟩ := h.exists_circuit_outputs
  obtain ⟨d, hd_eval, hd_size⟩ := c.exists_simulation_le boolean_simulatesWithCost_zmod2FullOnBool
  have hd_comp :
      d.Computes Boolean.interpretation
        (fun (x : Fin N → Bool) (j : Fin M) =>
          Cslib.BitString.bitEquiv (F j (Cslib.BitString.bitEquiv.symm ∘ x))) := by
    intro x
    rw [congrFun hd_eval x]
    have hhom := c.map_eval bitEquivHomomorphism (Cslib.BitString.bitEquiv.symm ∘ x)
    have hx : (bitEquivHomomorphism.map ∘ (Cslib.BitString.bitEquiv.symm ∘ x)) = x := by
      funext i
      exact Cslib.BitString.bitEquiv.apply_symm_apply (x i)
    rw [hx] at hhom
    rw [← hhom, hc (Cslib.BitString.bitEquiv.symm ∘ x)]
    rfl
  exact (complexity_le_of_computes d hd_comp).trans
    (hd_size.trans (Nat.mul_le_mul_left 25 hsize))

/-- **De Morgan Boolean circuit complexity of `kernelVec` over `ZMod 2`.** Given an `r × n` binary
matrix encoded row-major on `Fin (r * n) → Bool` via `finProdFinEquiv`, computing `kernelVec` takes
at most `25 * kernelVecCost r n` De Morgan gates. -/
theorem complexity_boolean_kernelVec_le (r n : ℕ) :
    complexity Boolean.interpretation
      (fun (aBits : Fin (r * n) → Bool) (j : Fin n) =>
        Cslib.BitString.bitEquiv
          (kernelVec (Matrix.of fun k l =>
            Cslib.BitString.bitEquiv.symm (aBits (finProdFinEquiv (k, l)))) j)) ≤
      25 * kernelVecCost r n := by
  have hsyn := Synthesis.full_kernelVec
    (F := ZMod 2) (N := r * n) (s := inputs (r * n))
    (fun k l x => x (finProdFinEquiv (k, l)))
    (fun k l => ⟨finProdFinEquiv (k, l), rfl⟩)
  exact complexity_boolean_of_fullTwo_zmod2 hsyn

/-- **De Morgan Boolean circuit complexity of `kernelVecAt` over `ZMod 2`.** Given an `r × n`
binary matrix encoded on `Fin (r * n) → Bool`, computing `kernelVecAt _ j₀` takes at most
`25 * kernelVecCost r n` De Morgan gates. -/
theorem complexity_boolean_kernelVecAt_le (r n : ℕ) (j₀ : Fin n) :
    complexity Boolean.interpretation
      (fun (aBits : Fin (r * n) → Bool) (j : Fin n) =>
        Cslib.BitString.bitEquiv
          (kernelVecAt (Matrix.of fun k l =>
            Cslib.BitString.bitEquiv.symm (aBits (finProdFinEquiv (k, l)))) j₀ j)) ≤
      25 * kernelVecCost r n := by
  have hsyn := Synthesis.full_kernelVecAt
    (F := ZMod 2) (N := r * n) (s := inputs (r * n))
    (fun k l x => x (finProdFinEquiv (k, l)))
    (fun k l => ⟨finProdFinEquiv (k, l), rfl⟩) j₀
  exact complexity_boolean_of_fullTwo_zmod2 hsyn

/-- **De Morgan Boolean circuit complexity of `vecMulSolve` over `ZMod 2`.** Given an `r × n`
binary matrix `M` and target vector `b` encoded on `Fin (r * n + n) → Bool` via `finSumFinEquiv`
and `finProdFinEquiv`, computing `vecMulSolve M b` takes at most
`25 * (kernelVecCost n (r + 1) + r)` De Morgan gates. -/
theorem complexity_boolean_vecMulSolve_le (r n : ℕ) :
    complexity Boolean.interpretation
      (fun (mbBits : Fin (r * n + n) → Bool) (k : Fin r) =>
        Cslib.BitString.bitEquiv
          (vecMulSolve
            (Matrix.of fun i l =>
              Cslib.BitString.bitEquiv.symm
                (mbBits (finSumFinEquiv (Sum.inl (finProdFinEquiv (i, l))))))
            (fun l =>
              Cslib.BitString.bitEquiv.symm (mbBits (finSumFinEquiv (Sum.inr l))))
            k)) ≤
      25 * (kernelVecCost n (r + 1) + r) := by
  have hsyn := Synthesis.full_vecMulSolve
    (F := ZMod 2) (N := r * n + n) (s := inputs (r * n + n))
    (fun i l x => x (finSumFinEquiv (Sum.inl (finProdFinEquiv (i, l)))))
    (fun l x => x (finSumFinEquiv (Sum.inr l)))
    (fun i l => ⟨finSumFinEquiv (Sum.inl (finProdFinEquiv (i, l))), rfl⟩)
    (fun l => ⟨finSumFinEquiv (Sum.inr l), rfl⟩)
  exact complexity_boolean_of_fullTwo_zmod2 hsyn

end Cslib.Circuits
