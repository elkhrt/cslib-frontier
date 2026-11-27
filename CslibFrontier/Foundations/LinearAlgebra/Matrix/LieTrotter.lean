module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# First-order Lie–Trotter product formula for complex matrices

This module establishes the quantitative and asymptotic first-order Lie–Trotter product formula
for finite lists of complex square matrices under the `ℓ²` operator norm:
`(∏_i exp ((t / K) A_i)) ^ K → exp (t ∑_i A_i)` as `K → ∞`.

## Main definitions

* `lieTrotterStep`: the single-step product `∏_i exp (δ A_i)`.
* `lieTrotterProd`: the `K`-step product `(∏_i exp ((t / K) A_i)) ^ K`.

## Main results

* `norm_lieTrotterProd_sub_exp_le`: quantitative error bound `‖(∏_i exp ((t / K) A_i)) ^ K - exp (t
  ∑_i A_i)‖ ≤ 2 (t L)^2 / K * exp (t L)`.
* `tendsto_lieTrotterProd`: asymptotic convergence to `exp (t ∑_i A_i)`.
-/

public section

namespace CslibFrontier.Foundations.LinearAlgebra.Matrix

open _root_.Matrix Filter Topology
open scoped Matrix.Norms.L2Operator

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Single first-order Lie–Trotter step `∏_i exp (δ A_i)` for a list of matrices `As`. -/
noncomputable def lieTrotterStep (As : List (Matrix m m ℂ)) (δ : ℝ) : Matrix m m ℂ :=
  (As.map fun A ↦ NormedSpace.exp ((δ : ℂ) • A)).prod

/-- `K`-step first-order Lie–Trotter product `(∏_i exp ((t / K) A_i)) ^ K`. -/
noncomputable def lieTrotterProd (As : List (Matrix m m ℂ)) (t : ℝ) (K : ℕ) : Matrix m m ℂ :=
  (lieTrotterStep As (t / (K : ℝ))) ^ K

/-- A single Lie–Trotter step on the empty list is the identity matrix. -/
@[simp]
theorem lieTrotterStep_nil (δ : ℝ) : lieTrotterStep ([] : List (Matrix m m ℂ)) δ = 1 := by
  simp [lieTrotterStep]

/-- At step size `δ = 0`, every Lie–Trotter step is the identity matrix. -/
@[simp]
theorem lieTrotterStep_zero (As : List (Matrix m m ℂ)) : lieTrotterStep As 0 = 1 := by
  induction As with
  | nil => simp
  | cons A As ih =>
    simp [lieTrotterStep] at ih ⊢

/-- At time `t = 0`, every `K`-step Lie–Trotter product is the identity matrix. -/
@[simp]
theorem lieTrotterProd_zero (As : List (Matrix m m ℂ)) (K : ℕ) :
    lieTrotterProd As 0 K = 1 := by
  simp [lieTrotterProd]

private lemma norm_one_le_matrix : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
  by_cases h : Nonempty m
  · have hnt : Nontrivial (Matrix m m ℂ) :=
      ⟨1, 0, fun heq ↦ (one_ne_zero : (1 : ℂ) ≠ 0) (by
        simpa using congrArg (fun M : Matrix m m ℂ ↦ M h.some h.some) heq)⟩
    exact le_of_eq norm_one
  · have hss : Subsingleton (Matrix m m ℂ) := by
      refine ⟨fun A B ↦ ?_⟩
      ext i j
      exact False.elim (h ⟨i⟩)
    rw [Subsingleton.elim (1 : Matrix m m ℂ) 0, norm_zero]
    exact zero_le_one

private lemma real_hasSum_exp (x : ℝ) :
    HasSum (fun k : ℕ ↦ x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

private lemma norm_exp_sub_one_sub_le (M : Matrix m m ℂ) :
    ‖NormedSpace.exp M - 1 - M‖ ≤ Real.exp ‖M‖ - 1 - ‖M‖ := by
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M
  have htail :
      HasSum (fun k : ℕ ↦ ((k + 2).factorial⁻¹ : ℂ) • M ^ (k + 2))
        (NormedSpace.exp M - 1 - M) := by
    have h1 := (hasSum_nat_add_iff' 2).mpr hsum
    simpa [Finset.sum_range_succ, sub_sub] using h1
  have hreal :
      HasSum (fun k : ℕ ↦ ((k + 2).factorial⁻¹ : ℝ) * ‖M‖ ^ (k + 2))
        (Real.exp ‖M‖ - 1 - ‖M‖) := by
    have h0 := (hasSum_nat_add_iff' 2).mpr (real_hasSum_exp ‖M‖)
    simpa [Finset.sum_range_succ, sub_sub, div_eq_inv_mul] using h0
  have hle : ∀ k : ℕ, ‖((k + 2).factorial⁻¹ : ℂ) • M ^ (k + 2)‖ ≤
      ((k + 2).factorial⁻¹ : ℝ) * ‖M‖ ^ (k + 2) := fun k ↦ by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' M (Nat.succ_pos _)) (by positivity)
  have hsumm : Summable fun k : ℕ ↦ ‖((k + 2).factorial⁻¹ : ℂ) • M ^ (k + 2)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hreal.summable
  rw [← htail.tsum_eq, ← hreal.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hle hreal.summable)

private lemma norm_exp_le_exp_norm (M : Matrix m m ℂ) :
    ‖NormedSpace.exp M‖ ≤ Real.exp ‖M‖ := by
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M
  have hreal := real_hasSum_exp ‖M‖
  have hle : ∀ k : ℕ, ‖(k.factorial⁻¹ : ℂ) • M ^ k‖ ≤ ‖M‖ ^ k / (k.factorial : ℝ) := by
    intro k
    rw [norm_smul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul]
    rcases k with _ | k
    · simpa using norm_one_le_matrix (m := m)
    · exact div_le_div_of_nonneg_right (norm_pow_le' M (Nat.succ_pos _)) (by positivity)
  have hsumm : Summable fun k : ℕ ↦ ‖(k.factorial⁻¹ : ℂ) • M ^ k‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hreal.summable
  rw [← hsum.tsum_eq, ← hreal.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hle hreal.summable)

private lemma real_exp_sub_one_sub_le {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x ^ 2 * Real.exp x := by
  have htail :
      HasSum (fun k : ℕ ↦ x ^ (k + 2) / ((k + 2).factorial : ℝ)) (Real.exp x - 1 - x) := by
    have h0 := (hasSum_nat_add_iff' 2).mpr (real_hasSum_exp x)
    simpa [Finset.sum_range_succ, sub_sub] using h0
  have hdom : HasSum (fun k : ℕ ↦ x ^ 2 * (x ^ k / (k.factorial : ℝ))) (x ^ 2 * Real.exp x) :=
    (real_hasSum_exp x).mul_left (x ^ 2)
  rw [← htail.tsum_eq, ← hdom.tsum_eq]
  refine htail.summable.tsum_le_tsum (fun k ↦ ?_) hdom.summable
  rw [pow_add, mul_comm (x ^ k) (x ^ 2), mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
  refine div_le_div_of_nonneg_left (pow_nonneg hx k) (Nat.cast_pos.mpr (Nat.factorial_pos k)) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_add_right k 2)

private lemma norm_list_sum_le (As : List (Matrix m m ℂ)) :
    ‖As.sum‖ ≤ (As.map fun A ↦ ‖A‖).sum := by
  induction As with
  | nil => simp
  | cons B Bs ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le B Bs.sum).trans (by linarith)

private lemma lieTrotterStep_first_order (As : List (Matrix m m ℂ)) {δ : ℝ} (hδ : 0 ≤ δ) :
    let L := (As.map fun A ↦ ‖A‖).sum
    ‖lieTrotterStep As δ‖ ≤ Real.exp (δ * L) ∧
      ‖lieTrotterStep As δ - (1 + (δ : ℂ) • As.sum)‖ ≤
        Real.exp (δ * L) - 1 - δ * L := by
  induction As with
  | nil =>
    simp only [lieTrotterStep_nil, List.map_nil, List.sum_nil, mul_zero, Real.exp_zero,
      smul_zero, add_zero, sub_self, norm_zero, le_refl, and_true]
    exact norm_one_le_matrix
  | cons A As ih =>
    rcases ih with ⟨hnorm_tail, herr_tail⟩
    set L := (As.map fun B ↦ ‖B‖).sum
    have hL_nn : 0 ≤ L := List.sum_nonneg fun x hx ↦ by
      obtain ⟨B, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg B
    have hnormA : ‖NormedSpace.exp ((δ : ℂ) • A)‖ ≤ Real.exp (δ * ‖A‖) := by
      refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
    have hnorm_cons : ‖lieTrotterStep (A :: As) δ‖ ≤ Real.exp (δ * (‖A‖ + L)) := by
      rw [lieTrotterStep, List.map_cons, List.prod_cons, ← lieTrotterStep]
      calc
        ‖NormedSpace.exp ((δ : ℂ) • A) * lieTrotterStep As δ‖
            ≤ ‖NormedSpace.exp ((δ : ℂ) • A)‖ * ‖lieTrotterStep As δ‖ := norm_mul_le _ _
        _ ≤ Real.exp (δ * ‖A‖) * Real.exp (δ * L) :=
          mul_le_mul hnormA hnorm_tail (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (δ * (‖A‖ + L)) := by rw [← Real.exp_add]; congr 1; ring
    have herrA : ‖NormedSpace.exp ((δ : ℂ) • A) - 1 - (δ : ℂ) • A‖ ≤
        Real.exp (δ * ‖A‖) - 1 - δ * ‖A‖ := by
      have h := norm_exp_sub_one_sub_le ((δ : ℂ) • A)
      rwa [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ] at h
    have hnormA_sub : ‖NormedSpace.exp ((δ : ℂ) • A) - 1‖ ≤ Real.exp (δ * ‖A‖) - 1 := by
      have htri := norm_add_le (NormedSpace.exp ((δ : ℂ) • A) - 1 - (δ : ℂ) • A) ((δ : ℂ) • A)
      rw [sub_add_cancel] at htri
      have hsmul : ‖(δ : ℂ) • A‖ = δ * ‖A‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
      linarith
    refine ⟨by simpa [List.map_cons, List.sum_cons, L] using hnorm_cons, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    change ‖NormedSpace.exp ((δ : ℂ) • A) * lieTrotterStep As δ -
        (1 + (δ : ℂ) • (A + As.sum))‖ ≤
      Real.exp (δ * (‖A‖ + L)) - 1 - δ * (‖A‖ + L)
    set E := NormedSpace.exp ((δ : ℂ) • A)
    set P := lieTrotterStep As δ
    set R₁ := E - 1 - (δ : ℂ) • A
    set R₂ := P - (1 + (δ : ℂ) • As.sum)
    have hdecomp :
        E * P - (1 + (δ : ℂ) • (A + As.sum)) =
          R₁ + E * R₂ + (E - 1) * ((δ : ℂ) • As.sum) := by
      simp only [R₁, R₂, smul_add, mul_sub, sub_mul, mul_add, mul_one, one_mul]
      abel
    have hsum_norm : ‖As.sum‖ ≤ L := norm_list_sum_le As
    have htri :
        ‖E * P - (1 + (δ : ℂ) • (A + As.sum))‖ ≤
          ‖R₁‖ + ‖E‖ * ‖R₂‖ + ‖E - 1‖ * (δ * L) := by
      rw [hdecomp]
      calc
        ‖R₁ + E * R₂ + (E - 1) * ((δ : ℂ) • As.sum)‖
            ≤ ‖R₁ + E * R₂‖ + ‖(E - 1) * ((δ : ℂ) • As.sum)‖ := norm_add_le _ _
        _ ≤ (‖R₁‖ + ‖E * R₂‖) + ‖(E - 1) * ((δ : ℂ) • As.sum)‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ ‖R₁‖ + ‖E‖ * ‖R₂‖ + ‖E - 1‖ * ‖(δ : ℂ) • As.sum‖ := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_mul_le _ _
        _ ≤ ‖R₁‖ + ‖E‖ * ‖R₂‖ + ‖E - 1‖ * (δ * L) := by
          gcongr
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
          exact mul_le_mul_of_nonneg_left hsum_norm hδ
    calc
      ‖E * P - (1 + (δ : ℂ) • (A + As.sum))‖
          ≤ ‖R₁‖ + ‖E‖ * ‖R₂‖ + ‖E - 1‖ * (δ * L) := htri
      _ ≤ (Real.exp (δ * ‖A‖) - 1 - δ * ‖A‖) +
            Real.exp (δ * ‖A‖) * (Real.exp (δ * L) - 1 - δ * L) +
            (Real.exp (δ * ‖A‖) - 1) * (δ * L) := by gcongr
      _ = Real.exp (δ * (‖A‖ + L)) - 1 - δ * (‖A‖ + L) := by
        rw [show δ * (‖A‖ + L) = δ * ‖A‖ + δ * L by ring, Real.exp_add]
        ring

/-- **Quantitative first-order Lie–Trotter error bound** for complex matrices:
`‖(∏_i exp((t/K) A_i))^K - exp(t ∑_i A_i)‖ ≤ 2 (t L)^2 / K * exp(t L)` for `t ≥ 0`, `K ≥ 1`,
where `L = ∑_i ‖A_i‖`. -/
theorem norm_lieTrotterProd_sub_exp_le (As : List (Matrix m m ℂ)) {t : ℝ} (ht : 0 ≤ t)
    {K : ℕ} (hK : 0 < K) :
    let L := (As.map fun A ↦ ‖A‖).sum
    ‖lieTrotterProd As t K - NormedSpace.exp ((t : ℂ) • As.sum)‖ ≤
      2 * (t * L) ^ 2 / (K : ℝ) * Real.exp (t * L) := by
  intro L
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  set δ : ℝ := t / (K : ℝ)
  have hδ : 0 ≤ δ := div_nonneg ht hKpos.le
  have hL_nn : 0 ≤ L := List.sum_nonneg fun x hx ↦ by
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg B
  have hP := lieTrotterStep_first_order As hδ
  have hsum_norm : ‖As.sum‖ ≤ L := norm_list_sum_le As
  set P := lieTrotterStep As δ
  set Q := NormedSpace.exp ((δ : ℂ) • As.sum)
  have hQ_norm : ‖Q‖ ≤ Real.exp (δ * L) := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hsum_norm hδ
  have hQ_err : ‖Q - (1 + (δ : ℂ) • As.sum)‖ ≤ Real.exp (δ * L) - 1 - δ * L := by
    have hsub : ‖(δ : ℂ) • As.sum‖ ≤ δ * L := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
      exact mul_le_mul_of_nonneg_left hsum_norm hδ
    have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
        Real.exp a - 1 - a ≤ Real.exp b - 1 - b := by
      intro a b ha hab
      have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ Real.exp y - 1 - y) (Real.exp x - 1) x :=
        fun x ↦ ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
      have hmono' : MonotoneOn (fun y : ℝ ↦ Real.exp y - 1 - y) (Set.Ici 0) :=
        monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
          (fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt)
          (fun x hx ↦ by
            rw [(hderiv x).deriv]
            have hx0 : 0 ≤ x := interior_subset hx
            linarith [Real.add_one_le_exp x, hx0])
      exact hmono' ha (ha.trans hab) hab
    have hstep := (norm_exp_sub_one_sub_le ((δ : ℂ) • As.sum)).trans
      (hmono _ _ (norm_nonneg _) hsub)
    simpa [Q, sub_sub] using hstep
  have hPQ : ‖P - Q‖ ≤ 2 * (δ * L) ^ 2 * Real.exp (δ * L) := by
    have htri : ‖P - Q‖ ≤ ‖P - (1 + (δ : ℂ) • As.sum)‖ + ‖Q - (1 + (δ : ℂ) • As.sum)‖ := by
      have heq : P - Q = (P - (1 + (δ : ℂ) • As.sum)) - (Q - (1 + (δ : ℂ) • As.sum)) := by abel
      rw [heq]
      exact norm_sub_le _ _
    have h1 := real_exp_sub_one_sub_le (mul_nonneg hδ hL_nn)
    linarith [hP.2, hQ_err]
  have hQK : Q ^ K = NormedSpace.exp ((t : ℂ) • As.sum) := by
    rw [← _root_.Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 2
    simp only [δ]
    push_cast
    exact mul_div_cancel₀ _ (by exact_mod_cast hKpos.ne')
  have htelesc : ∀ n : ℕ, ‖P ^ n - Q ^ n‖ ≤
      (n : ℝ) * Real.exp (((n : ℝ) - 1) * (δ * L)) * ‖P - Q‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hsplit : P ^ (n + 1) - Q ^ (n + 1) = P ^ n * (P - Q) + (P ^ n - Q ^ n) * Q := by
        rw [pow_succ, pow_succ]; noncomm_ring
      rcases n with _ | n
      · simp
      · have hPn : ‖P ^ (n + 1)‖ ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) := by
          calc
            ‖P ^ (n + 1)‖ ≤ ‖P‖ ^ (n + 1) := norm_pow_le' P (Nat.succ_pos n)
            _ ≤ (Real.exp (δ * L)) ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hP.1 (n + 1)
            _ = Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) := (Real.exp_nat_mul _ _).symm
        rw [hsplit]
        calc
          ‖P ^ (n + 1) * (P - Q) + (P ^ (n + 1) - Q ^ (n + 1)) * Q‖
              ≤ ‖P ^ (n + 1) * (P - Q)‖ + ‖(P ^ (n + 1) - Q ^ (n + 1)) * Q‖ := norm_add_le _ _
          _ ≤ ‖P ^ (n + 1)‖ * ‖P - Q‖ + ‖P ^ (n + 1) - Q ^ (n + 1)‖ * ‖Q‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) * ‖P - Q‖ +
                (((n + 1 : ℕ) : ℝ) * Real.exp ((((n + 1 : ℕ) : ℝ) - 1) * (δ * L)) * ‖P - Q‖) *
                  Real.exp (δ * L) := by gcongr
          _ = (((n + 1 + 1 : ℕ) : ℝ) * Real.exp ((((n + 1 + 1 : ℕ) : ℝ) - 1) * (δ * L))) *
                ‖P - Q‖ := by
            have h1 : Real.exp ((((n + 1 : ℕ) : ℝ) - 1) * (δ * L)) * Real.exp (δ * L) =
                Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) := by
              rw [← Real.exp_add]; congr 1; ring
            have h2 : ((((n + 1 + 1 : ℕ) : ℝ) - 1) * (δ * L)) =
                ((n + 1 : ℕ) : ℝ) * (δ * L) := by push_cast; ring
            rw [h2]
            calc
              Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) * ‖P - Q‖ +
                  ((n + 1 : ℕ) : ℝ) * Real.exp ((((n + 1 : ℕ) : ℝ) - 1) * (δ * L)) * ‖P - Q‖ *
                    Real.exp (δ * L)
                  = Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) * ‖P - Q‖ +
                      ((n + 1 : ℕ) : ℝ) *
                        (Real.exp ((((n + 1 : ℕ) : ℝ) - 1) * (δ * L)) * Real.exp (δ * L)) *
                        ‖P - Q‖ := by ring
              _ = (((n + 1 : ℕ) : ℝ) + 1) * Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L)) * ‖P - Q‖ := by
                rw [h1]; ring
              _ = (((n + 1 + 1 : ℕ) : ℝ) * Real.exp (((n + 1 : ℕ) : ℝ) * (δ * L))) * ‖P - Q‖ := by
                push_cast; ring
  rw [lieTrotterProd, ← hQK]
  have hKδ : (K : ℝ) * δ = t := mul_div_cancel₀ t hKpos.ne'
  calc
    ‖P ^ K - Q ^ K‖ ≤ (K : ℝ) * Real.exp (((K : ℝ) - 1) * (δ * L)) * ‖P - Q‖ := htelesc K
    _ ≤ (K : ℝ) * Real.exp (((K : ℝ) - 1) * (δ * L)) *
          (2 * (δ * L) ^ 2 * Real.exp (δ * L)) := by gcongr
    _ = 2 * (t * L) ^ 2 / (K : ℝ) * Real.exp (t * L) := by
      have hexp : Real.exp (((K : ℝ) - 1) * (δ * L)) * Real.exp (δ * L) = Real.exp (t * L) := by
        rw [← Real.exp_add]
        congr 1
        nlinarith [hKδ]
      calc
        (K : ℝ) * Real.exp (((K : ℝ) - 1) * (δ * L)) * (2 * (δ * L) ^ 2 * Real.exp (δ * L))
            = 2 * ((K : ℝ) * (δ * L) ^ 2) *
                (Real.exp (((K : ℝ) - 1) * (δ * L)) * Real.exp (δ * L)) := by ring
        _ = 2 * (t * L) ^ 2 / (K : ℝ) * Real.exp (t * L) := by
          rw [hexp]
          have hsq : (K : ℝ) * (δ * L) ^ 2 = (t * L) ^ 2 / (K : ℝ) := by
            rw [eq_div_iff hKpos.ne']
            calc
              (K : ℝ) * (δ * L) ^ 2 * (K : ℝ) = ((K : ℝ) * δ) ^ 2 * L ^ 2 := by ring
              _ = t ^ 2 * L ^ 2 := by rw [hKδ]
              _ = (t * L) ^ 2 := by ring
          rw [hsq]
          ring

/-- **First-order Lie–Trotter product formula**: for any finite list of complex matrices `As`
and `t ≥ 0`, `(∏_i exp ((t / K) A_i)) ^ K → exp (t ∑_i A_i)` as `K → ∞`. -/
theorem tendsto_lieTrotterProd (As : List (Matrix m m ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun K : ℕ ↦ lieTrotterProd As t K) atTop
      (𝓝 (NormedSpace.exp ((t : ℂ) • As.sum))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set L := (As.map fun A ↦ ‖A‖).sum
  have htend : Tendsto (fun K : ℕ ↦ 2 * (t * L) ^ 2 / (K : ℝ) * Real.exp (t * L)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun K : ℕ ↦ (2 * (t * L) ^ 2 * Real.exp (t * L)) / (K : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact hinv.congr fun K ↦ by ring
  refine squeeze_zero_norm' (eventually_atTop.mpr ⟨1, fun K hK ↦ ?_⟩) htend
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_lieTrotterProd_sub_exp_le As ht hK

end CslibFrontier.Foundations.LinearAlgebra.Matrix
