/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP.Padding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow

/-!
# Linear-exponent padding and closure rules for `E`

`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad` (`Classes/EXP.lean`) proves that a
polynomial-time test on `(y, 2 ^ |y|)` for raw bit words `y` belongs to linear exponential time
`Cslib.Complexity.E encBits`. This module generalizes linear-exponential padding to arbitrary
caller-supplied encodings `encB : β ↪ List Bool` and any polynomial-time unary exponent `L : β → ℕ`
bounded linearly by encoded input length (`L b ≤ c * |encB b| + c`), and establishes the linear
counterparts of `DTIME_two_pow_subset_EXP` and `NTIME_two_pow_subset_NEXP` for `E` and `NE`.

## Main results

* `Cslib.Complexity.DTIME_two_pow_linear_subset_E`: deterministic time `2 ^ h n` with
  `h n ≤ c * n + c` lies in `E`.
* `Cslib.Complexity.NTIME_two_pow_linear_subset_NE`: nondeterministic time `2 ^ h n` with
  `h n ≤ c * n + c` lies in `NE`.
* `Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad_linear`: polynomial time on
  `(b, 2 ^ L b)` with `L b ≤ c * |encB b| + c` gives `E encB`.
-/

public section

namespace Cslib.Complexity

open Filter Turing Turing.MultiTapeTM

/-- Deterministic time `2 ^ h n`, for an exponent `h n ≤ c * n + c`, lies in linear exponential
time `E`. -/
theorem DTIME_two_pow_linear_subset_E {α : Type*} {enc : α ↪ List Bool} {h : ℕ → ℕ} {c : ℕ}
    (hh : ∀ n, h n ≤ c * n + c) :
    DTIME enc (fun n => 2 ^ h n) ⊆ E enc := fun _ hA => by
  refine mem_E_iff.mpr ⟨2 * c, DTIME_mono_of_eventually_le ?_ hA⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply Nat.pow_le_pow_right (by decide)
  have := hh n
  nlinarith

/-- Nondeterministic time `2 ^ h n`, for an exponent `h n ≤ c * n + c`, lies in nondeterministic
linear exponential time `NE`. -/
theorem NTIME_two_pow_linear_subset_NE {α : Type*} {enc : α ↪ List Bool} {h : ℕ → ℕ} {c : ℕ}
    (hh : ∀ n, h n ≤ c * n + c) :
    NTIME enc (fun n => 2 ^ h n) ⊆ NE enc := fun _ hA => by
  refine mem_NE_iff.mpr ⟨2 * c, NTIME_mono_of_eventually_le ?_ hA⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply Nat.pow_le_pow_right (by decide)
  have := hh n
  nlinarith

/-- **Linear-exponential padding on arbitrary encodings.** If `Ψ` is computable in polynomial time
on pairs `(b, N)` with `N` in unary, and `L` is computable in unary in polynomial time with
`L b ≤ c * |encB b| + c`, then `{b | Ψ (b, 2 ^ L b) = true} ∈ E encB`. -/
theorem setOf_mem_E_of_computableInPolyTime_pad_linear {β : Type} {encB : β ↪ List Bool}
    {Ψ : β × ℕ → Bool} (hΨ : ComputableInPolyTime Ψ (encPair encB encUnary) encBool)
    {L : β → ℕ} (hL : ComputableInPolyTime L encB encUnary)
    {c : ℕ} (hLle : ∀ b, L b ≤ c * (encB b).length + c) :
    {b | Ψ (b, 2 ^ L b) = true} ∈ E encB := by
  obtain ⟨C, D, h⟩ := hΨ.exists_computableInO_pad hL
  let K := D * c + D
  let M := C * 2 ^ (D * c)
  refine mem_E_iff.mpr ⟨K, DTIME_mono_of_le_mul_add (C := M) (fun _ => le_rfl)
    (setOf_mem_DTIME_of_computableInO (t := fun n => M * 2 ^ (K * n) + M) h fun b => ?_)⟩
  set n := (encB b).length
  have h1 : 2 ^ (D * L b) ≤ 2 ^ (D * c) * 2 ^ (D * c * n) := by
    calc 2 ^ (D * L b) ≤ 2 ^ (D * (c * n + c)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left D (hLle b))
      _ = 2 ^ (D * c) * 2 ^ (D * c * n) := by
          rw [← Nat.pow_add]
          congr 1
          ring
  have h2 : (n + 1) ^ D ≤ 2 ^ (D * n) := by
    calc (n + 1) ^ D ≤ (2 ^ n) ^ D := Nat.pow_le_pow_left Nat.lt_two_pow_self D
      _ = 2 ^ (D * n) := by rw [← Nat.pow_mul, Nat.mul_comm]
  calc C * 2 ^ (D * L b) * (n + 1) ^ D
      ≤ C * (2 ^ (D * c) * 2 ^ (D * c * n)) * 2 ^ (D * n) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left C h1) h2
    _ = M * 2 ^ (K * n) := by
        dsimp [M, K]
        rw [← Nat.mul_assoc C, Nat.mul_assoc (C * 2 ^ (D * c)), ← Nat.pow_add]
        congr 2
        ring
    _ ≤ M * 2 ^ (K * n) + M := Nat.le_add_right _ _

end Cslib.Complexity
