module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Central Binomial Probability Bound

Proves the elementary central binomial bound `2^{-r} * C(r, r / 2) ≤ 1 / √(r + 1)`
for all `r : ℕ`, used in total-variation bounds for binomial shifts.

## Main results

* `CslibFrontier.Probability.central_binom_le_inv_sqrt`: exact `1 / √(r + 1)` bound on
  the largest mass of `Bin(r, 1/2)`.
-/

public section

namespace CslibFrontier.Probability

/-- Elementary central binomial bound `2^{-r} C(r, ⌊r/2⌋) ≤ 1 / √(r + 1)` for all `r : ℕ`. -/
theorem central_binom_le_inv_sqrt (r : ℕ) :
    (2 : ℝ)⁻¹ ^ r * (r.choose (r / 2) : ℝ) ≤ (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
  have hsq : ∀ m : ℕ, ((2 : ℝ)⁻¹ ^ m * (m.choose (m / 2) : ℝ)) ^ 2 * ((m + 1 : ℕ) : ℝ) ≤ 1 := by
    intro m
    have heven : ∀ j : ℕ,
        ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2 * ((2 * j + 1 : ℕ) : ℝ) ≤ 1 := by
      intro j
      induction j with
      | zero => norm_num
      | succ j ih =>
        have hstep : ((2 * (j + 1)).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
            2 * ((2 * j + 1 : ℕ) : ℝ) * ((2 * j).choose j : ℝ) := by
          have hnat : (2 * (j + 1)).choose (j + 1) * (j + 1) =
            2 * (2 * j + 1) * (2 * j).choose j := by
            have hf1 := Nat.choose_mul_factorial_mul_factorial (show j + 1 ≤ 2 * (j + 1) by omega)
            have hf2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
            rw [show 2 * (j + 1) - (j + 1) = j + 1 by omega] at hf1
            rw [show 2 * j - j = j by omega] at hf2
            have hpos : 0 < (j + 1) * j.factorial * j.factorial :=
              Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
            apply Nat.eq_of_mul_eq_mul_right hpos
            calc (2 * (j + 1)).choose (j + 1) * (j + 1) * ((j + 1) * j.factorial * j.factorial)
                = (2 * (j + 1)).choose (j + 1) * (j + 1).factorial * (j + 1).factorial := by
                    rw [Nat.factorial_succ]; ring
              _ = (2 * (j + 1)).factorial := hf1
              _ = (2 * j + 2) * (2 * j + 1) * (2 * j).factorial := by
                    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, Nat.factorial_succ,
                      Nat.factorial_succ]; ring
              _ = 2 * (j + 1) * (2 * j + 1) * ((2 * j).choose j * j.factorial * j.factorial) := by
                    rw [← hf2]; ring
              _ = 2 * (2 * j + 1) * (2 * j).choose j * ((j + 1) * j.factorial * j.factorial) := by
                ring
          exact_mod_cast hnat
        have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hratio : (2 : ℝ)⁻¹ ^ (2 * (j + 1)) * ((2 * (j + 1)).choose (j + 1) : ℝ) =
            (((2 * j + 1 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) *
              ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) := by
          have hch : ((2 * (j + 1)).choose (j + 1) : ℝ) =
              2 * ((2 * j + 1 : ℕ) : ℝ) * ((2 * j).choose j : ℝ) / ((j + 1 : ℕ) : ℝ) :=
            eq_div_of_mul_eq hj1 hstep
          rw [hch, show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
          field_simp [hj1]
        rw [hratio, mul_pow, mul_assoc,
          mul_comm (((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2),
          ← mul_assoc]
        have hfrac : ((((2 * j + 1 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) ^ 2 * ((2 * (j + 1) +
          1 : ℕ) : ℝ)) ≤
            ((2 * j + 1 : ℕ) : ℝ) := by
          rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          push_cast; nlinarith
        calc (((2 * j + 1 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) ^ 2 * ((2 * (j + 1) + 1 : ℕ) : ℝ) *
                ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2
            ≤ ((2 * j + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
          _ = ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2 * ((2 * j + 1 : ℕ) : ℝ) :=
            mul_comm _ _
          _ ≤ 1 := ih
    rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by omega, show (2 * j) / 2 = j by omega]
      exact heven j
    · rw [show (2 * j + 1) / 2 = j by omega]
      have hstep : ((2 * j + 1).choose j : ℝ) * ((j + 1 : ℕ) : ℝ) =
          ((2 * j + 1 : ℕ) : ℝ) * ((2 * j).choose j : ℝ) := by
        have hnat : (2 * j + 1).choose j * (j + 1) = (2 * j + 1) * (2 * j).choose j := by
          have hf1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j + 1 by omega)
          have hf2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
          rw [show 2 * j + 1 - j = j + 1 by omega] at hf1
          rw [show 2 * j - j = j by omega] at hf2
          have hpos : 0 < j.factorial * j.factorial :=
            Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
          apply Nat.eq_of_mul_eq_mul_right hpos
          calc (2 * j + 1).choose j * (j + 1) * (j.factorial * j.factorial)
              = (2 * j + 1).choose j * j.factorial * (j + 1).factorial := by
                rw [Nat.factorial_succ]; ring
            _ = (2 * j + 1).factorial := hf1
            _ = (2 * j + 1) * (2 * j).factorial := Nat.factorial_succ _
            _ = (2 * j + 1) * ((2 * j).choose j * j.factorial * j.factorial) := by rw [← hf2]
            _ = (2 * j + 1) * (2 * j).choose j * (j.factorial * j.factorial) := by ring
        exact_mod_cast hnat
      have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hratio : (2 : ℝ)⁻¹ ^ (2 * j + 1) * ((2 * j + 1).choose j : ℝ) =
          (((2 * j + 1 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) *
            ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) := by
        have hch : ((2 * j + 1).choose j : ℝ) =
            ((2 * j + 1 : ℕ) : ℝ) * ((2 * j).choose j : ℝ) / ((j + 1 : ℕ) : ℝ) :=
          eq_div_of_mul_eq hj1 hstep
        rw [hch, pow_succ]
        field_simp [hj1]
      rw [hratio, mul_pow, mul_assoc, mul_comm (((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2),
        ← mul_assoc]
      have hfrac : ((((2 * j + 1 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) ^ 2 * ((2 * j + 1 +
        1 : ℕ) : ℝ)) ≤
          ((2 * j + 1 : ℕ) : ℝ) := by
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        push_cast; nlinarith
      calc (((2 * j + 1 : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) ^ 2 * ((2 * j + 1 + 1 : ℕ) : ℝ) *
              ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2
          ≤ ((2 * j + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
        _ = ((2 : ℝ)⁻¹ ^ (2 * j) * ((2 * j).choose j : ℝ)) ^ 2 * ((2 * j + 1 : ℕ) : ℝ) :=
          mul_comm _ _
        _ ≤ 1 := heven j
  have h1 := hsq r
  have hpos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ r * (r.choose (r / 2) : ℝ))]
  have hsq_le : ((2 : ℝ)⁻¹ ^ r * (r.choose (r / 2) : ℝ)) ^ 2 ≤
    ((Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) ^ 2 := by
    rw [inv_pow (Real.sqrt _), Real.sq_sqrt hpos.le, inv_eq_one_div ((r + 1 : ℕ) : ℝ),
      le_div_iff₀ hpos]
    exact h1
  exact (Real.sqrt_le_sqrt hsq_le).trans_eq (Real.sqrt_sq (by positivity))

end CslibFrontier.Probability
