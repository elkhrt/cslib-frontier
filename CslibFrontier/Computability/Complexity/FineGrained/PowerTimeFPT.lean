/-
Copyright (c) 2026 The Cslib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
public import CslibFrontier.Computability.Complexity.Parameterized

import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Power-Exponential Time Implies Fixed-Parameter Tractability

Connects fine-grained power-exponential parameter bounds (`Cslib.Complexity.DecidableInPowerExpTime`
and `Cslib.Complexity.ComputableInPowerExpTime`) to uniform fixed-parameter tractability
(`Cslib.Complexity.FPT` and `Cslib.Complexity.ComputableInFPTTime`):

* Any problem decidable in time $2^{C (\kappa(a) + 1)^p} \cdot (|a| + 1)^e$ up to constant factors
  belongs to `Cslib.Complexity.FPT enc κ` with parameter factor
  $f(k) = \lceil 2^{C (k + 1)^p} \rceil_+$ (`Cslib.Complexity.DecidableInPowerExpTime.mem_FPT`).
* Any function computable within a power-exponential parameter time bound is computable in FPT time
  (`Cslib.Complexity.ComputableInPowerExpTime.computableInFPTTime`).

In particular, combining `Cslib.Complexity.DecidableInPowerExpTime.of_exhaustiveSearch` with
`Cslib.Complexity.DecidableInPowerExpTime.mem_FPT` certifies `FPT` membership for algorithms that
branch on $O((\kappa(a) + 1)^q)$ bits (for example, enumerating bijections on a kernel or bounded
remainder of size $O(\kappa(a))$ encoded in $O(\kappa(a)^2)$ unary-block bits).

## Main results

* `Cslib.Complexity.DecidableInPowerExpTime.mem_FPT`: power-exponential time in the parameter is
  fixed-parameter tractable.
* `Cslib.Complexity.ComputableInPowerExpTime.computableInFPTTime`: power-exponential time
  functions are computable in `ComputableInFPTTime`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

section PowerTimeToFPT

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {A : Set α} {κ : α → ℕ}

/-- **Power-exponential parameter time is fixed-parameter tractable**: any problem decidable in
time $2^{C (\kappa(a) + 1)^p} \cdot (|a| + 1)^e$ up to constant factors belongs to `FPT encA κ`. -/
theorem DecidableInPowerExpTime.mem_FPT {p : ℝ}
    (h : DecidableInPowerExpTime A encA κ p) :
    A ∈ FPT encA κ := by
  obtain ⟨C, e, h⟩ := h
  refine ⟨fun k => ⌈(2 : ℝ) ^ ((C : ℝ) * (k + 1 : ℝ) ^ p)⌉₊, e,
    h.mono 1 (fun a => ?_) fun _ => by positivity⟩
  have hceil : (2 : ℝ) ^ ((C : ℝ) * (κ a + 1 : ℝ) ^ p) ≤
      (⌈(2 : ℝ) ^ ((C : ℝ) * (κ a + 1 : ℝ) ^ p)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hceil
    (by positivity : (0 : ℝ) ≤ ((encA a).length + 1 : ℝ) ^ e)
  dsimp only
  push_cast
  linarith

/-- Any function computable in power-exponential parameter time (`ComputableInPowerExpTime`) is
computable in FPT time (`ComputableInFPTTime`). -/
theorem ComputableInPowerExpTime.computableInFPTTime {f : α → β} {p : ℝ}
    (hf : ComputableInPowerExpTime f encA encB κ p) :
    ComputableInFPTTime f encA encB κ := by
  obtain ⟨C, e, hf⟩ := hf
  obtain ⟨t, c, hfO, ht⟩ := hf.exists_computableInO
  let F : ℕ → ℕ := fun k => c * ⌈(2 : ℝ) ^ ((C : ℝ) * (k + 1 : ℝ) ^ p)⌉₊ + c
  have htle (a : α) : t a ≤ F (κ a) * ((encA a).length + 1) ^ e := by
    have hpow_pos : (1 : ℝ) ≤ ((encA a).length + 1 : ℝ) ^ e :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg (encA a).length : (0 : ℝ) ≤ _)])
    have hceil : (2 : ℝ) ^ ((C : ℝ) * (κ a + 1 : ℝ) ^ p) ≤
        (⌈(2 : ℝ) ^ ((C : ℝ) * (κ a + 1 : ℝ) ^ p)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h1 : (t a : ℝ) ≤
        (F (κ a) : ℝ) * ((encA a).length + 1 : ℝ) ^ e := by
      have hm1 := mul_le_mul_of_nonneg_right hceil
        (by positivity : (0 : ℝ) ≤ ((encA a).length + 1 : ℝ) ^ e)
      have hm2 := mul_le_mul_of_nonneg_left hm1 (Nat.cast_nonneg c)
      have hm3 := mul_le_mul_of_nonneg_left hpow_pos (Nat.cast_nonneg c)
      dsimp only [F]
      push_cast
      linarith [ht a]
    exact_mod_cast h1
  exact ComputableInO.computableInFPTTime (hfO.mono_le htle htle)

end PowerTimeToFPT

end Cslib.Complexity
