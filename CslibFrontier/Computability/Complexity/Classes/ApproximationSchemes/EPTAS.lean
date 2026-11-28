/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ApproximationSchemes
public import CslibFrontier.Computability.Complexity.FineGrained.FunctionRates
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Mathlib.Tactic.Positivity

/-!
# Efficient polynomial-time approximation schemes (EPTAS)

An *efficient polynomial-time approximation scheme* (`EPTAS`) for an `NPOptimizationProblem`
 strengthens `PTAS` by requiring an absolute polynomial degree `c`
independent of the accuracy parameter `k`: for every positive `k`, there is a `(1 + 1 / k)`-
(minimization) or `(1 - 1 / k)`- (maximization) approximation algorithm running in time
`O(f k * (|x| + 1) ^ c)` on native multi-tape Turing machines.

We prove the full approximation-scheme hierarchy `FPTAS → EPTAS → PTAS`.

## Main definitions

* `Cslib.Complexity.NPOptimizationProblem.EPTAS`: efficient polynomial-time approximation scheme
  with an absolute polynomial degree independent of the accuracy `1 / k`.

## Main results

* `Cslib.Complexity.NPOptimizationProblem.EPTAS.toPTAS`: every `EPTAS` is a `PTAS`.
* `Cslib.Complexity.NPOptimizationProblem.FPTAS.toEPTAS`: every `FPTAS` is an `EPTAS`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace NPOptimizationProblem

variable {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
  (problem : NPOptimizationProblem encI encS)

/-- An efficient polynomial-time approximation scheme (`EPTAS`): a single absolute polynomial
degree `c` and accuracy overhead `f : ℕ → ℕ` such that every positive accuracy `1 / k` has a
native multi-tape solver running in time `O(f k * (|x| + 1) ^ c)`. -/
@[expose] def EPTAS : Prop :=
  ∃ (c : ℕ) (f : ℕ → ℕ),
    ∀ k : ℕ, 0 < k →
      ∃ solve : α → β,
        ComputableInTimeO solve encI encS
          (fun a => (f k : ℝ) * ((encI a).length + 1) ^ c) ∧
        ∀ a, problem.IsApproximate k a (solve a)

/-- Every `EPTAS` is a `PTAS`. -/
theorem EPTAS.toPTAS (h : problem.EPTAS) : problem.PTAS := by
  obtain ⟨c, f, hsolve⟩ := h
  intro k hk
  obtain ⟨solve, htime, happrox⟩ := hsolve k hk
  obtain ⟨c₀, t, s, ht, hcomp⟩ := htime
  let polyClock (n : ℕ) : ℕ := c₀ * (f k * (n + 1) ^ c) + c₀
  have hpoly_t : Cslib.PolynomiallyBounded polyClock := by
    dsimp only [polyClock]
    fun_prop
  refine ⟨solve, ?_, happrox⟩
  refine (hcomp.mono (fun a => ?_) (fun _ => le_rfl)).computableInPolyTime hpoly_t
  have hta : (t a : ℝ) ≤ c₀ * ((f k : ℝ) * ((encI a).length + 1) ^ c) + c₀ := ht a
  exact_mod_cast hta

/-- Every `FPTAS` is an `EPTAS`. -/
theorem FPTAS.toEPTAS (h : problem.FPTAS) : problem.EPTAS := by
  obtain ⟨solve, hsolve, hcorrect⟩ := h
  obtain ⟨d, _, hdeg⟩ := hsolve.exists_degree
  refine ⟨max d 1, fun k => (2 * k + 3) ^ (max d 1) + 2, fun k hk => ?_⟩
  have hconst : ComputableInO (fun _ : α => k) encI encUnary
      (fun a => (encI a).length) (fun a => (encI a).length) :=
    ComputableInO.const k
  have hid : ComputableInO (fun a : α => a) encI encI
      (fun a => (encI a).length) (fun a => (encI a).length) :=
    ComputableInO.of_eq fun _ => rfl
  have hcomp := hdeg.inO.comp (hconst.prod hid)
  refine ⟨fun a => solve (k, a), ComputableInTimeO.of_computableInO hcomp fun a => ?_,
    hcorrect k hk⟩
  set L := (encI a).length
  have hL1 : 1 ≤ L + 1 := Nat.succ_pos L
  have hpair : (encPair encUnary encI (k, a)).length + 1 ≤ (2 * k + 3) * (L + 1) := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    nlinarith
  have hpow : ((encPair encUnary encI (k, a)).length + 1) ^ d ≤
      (2 * k + 3) ^ max d 1 * (L + 1) ^ max d 1 := by
    calc ((encPair encUnary encI (k, a)).length + 1) ^ d
        ≤ ((2 * k + 3) * (L + 1)) ^ d := Nat.pow_le_pow_left hpair d
      _ = (2 * k + 3) ^ d * (L + 1) ^ d := Nat.mul_pow _ _ _
      _ ≤ (2 * k + 3) ^ max d 1 * (L + 1) ^ max d 1 :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (le_max_left d 1))
          (Nat.pow_le_pow_right hL1 (le_max_left d 1))
  have hlin : L + L ≤ 2 * (L + 1) ^ max d 1 := by
    have : L + 1 ≤ (L + 1) ^ max d 1 :=
      Nat.le_self_pow (by have := le_max_right d 1; omega) _
    omega
  have hnat : L + L + ((encPair encUnary encI (k, a)).length + 1) ^ d ≤
      ((2 * k + 3) ^ max d 1 + 2) * (L + 1) ^ max d 1 := by
    rw [Nat.add_mul]
    omega
  dsimp only [Function.comp_apply]
  exact_mod_cast hnat

end NPOptimizationProblem

end Cslib.Complexity
