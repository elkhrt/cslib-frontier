module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zeroing Correlations by Change of Distribution via Matrix Inversion

Given a nonempty finite domain `X` and `{-1, +1}`-valued functions `f, χ_1, ..., χ_k : X → ℝ`
that are nearly pairwise orthogonal and nearly uncorrelated with `f` under the uniform measure,
this module constructs a strictly positive probability distribution `μ` on `X` under which
`f` has exact zero correlation with every `χ_i`. The construction inverts the strictly diagonally
dominant Gram matrix `M_{ij} = ⟨χ_i, χ_j⟩` using Gershgorin's nonsingularity criterion.

As an immediate obstruction corollary, no such probability distribution can exist when `f` is
sign-represented by a real linear combination of `χ_1, ..., χ_k`.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.uniformInnerProd`: normalized inner product
  `|X|⁻¹ ∑_{x ∈ X} f(x) g(x)` on a finite type `X`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.exists_zero_correlation_dist`: existence of a
  strictly positive probability distribution `μ` with `∑ x, μ x * (f x * χ_i x) = 0` for all `i`.
* `CslibFrontier.Foundations.BooleanAnalysis.not_exists_zero_correlation_dist_of_pos_mul`:
  sign-representation obstruction against correlation-zeroing distributions.
-/

public section

namespace CslibFrontier.Foundations.BooleanAnalysis

open Finset
open scoped Matrix

/-- Normalized inner product `⟨f, g⟩ = |X|⁻¹ ∑_{x ∈ X} f(x) g(x)` on a finite type `X`. -/
@[expose] noncomputable def uniformInnerProd {X : Type*} [Fintype X] (f g : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ x : X, f x * g x

/-- If `f, χ_1, ..., χ_k : X → {-1, +1}` on a nonempty finite type `X` satisfy
`∑_i |⟨f, χ_i⟩| < 1 / 2` and `∑_{j ≠ i} |⟨χ_i, χ_j⟩| ≤ 1 / 2` for every `i`, then there exists
a strictly positive probability distribution `μ` on `X` such that
`∑ x, μ x * (f x * χ_i x) = 0` for every `i`. -/
theorem exists_zero_correlation_dist {X : Type*} [Fintype X] [Nonempty X] {k : ℕ}
    (f : X → ℝ) (χ : Fin k → X → ℝ)
    (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hχ : ∀ i x, χ i x = 1 ∨ χ i x = -1)
    (hcorr : ∑ i : Fin k, |uniformInnerProd f (χ i)| < 1 / 2)
    (hpair : ∀ i : Fin k, ∑ j ∈ Finset.univ.erase i, |uniformInnerProd (χ i) (χ j)| ≤ 1 / 2) :
    ∃ μ : X → ℝ,
      (∀ x, 0 < μ x) ∧ (∑ x : X, μ x = 1) ∧
      ∀ i : Fin k, ∑ x : X, μ x * (f x * χ i x) = 0 := by
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => uniformInnerProd (χ i) (χ j)
  let γ : Fin k → ℝ := fun i => uniformInnerProd f (χ i)
  have hMdiag : ∀ i : Fin k, M i i = 1 := fun i => by
    have hsq : ∀ x : X, χ i x * χ i x = 1 := fun x => by rcases hχ i x with h | h <;> simp [h]
    simp only [M, Matrix.of_apply, uniformInnerProd, hsq, sum_const, card_univ, nsmul_eq_mul,
      mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hMsym : ∀ i j : Fin k, M i j = M j i := fun i j => by
    simp only [M, Matrix.of_apply, uniformInnerProd]
    congr 1
    exact sum_congr rfl fun x _ => mul_comm _ _
  have hMdet : M.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    simpa only [Real.norm_eq_abs, hMdiag i, abs_one, M, Matrix.of_apply] using
      (hpair i).trans_lt (by norm_num)
  let α : Fin k → ℝ := M⁻¹ *ᵥ γ
  have hMα : M *ᵥ α = γ := by
    dsimp only [α]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hMdet),
      Matrix.one_mulVec]
  have hrow_ineq : ∀ i : Fin k,
      2 * |α i| - ∑ j : Fin k, |M i j| * |α j| ≤ |γ i| := by
    intro i
    have hi : ∑ j : Fin k, M i j * α j = γ i := by
      simpa [Matrix.mulVec, dotProduct] using congr_fun hMα i
    have hsplit : α i + ∑ j ∈ Finset.univ.erase i, M i j * α j = γ i := by
      have := Finset.add_sum_erase Finset.univ (fun j => M i j * α j) (mem_univ i)
      rw [hMdiag i, one_mul] at this
      linarith
    have htri : |α i| ≤ |γ i| + ∑ j ∈ Finset.univ.erase i, |M i j| * |α j| := by
      calc |α i| = |γ i - ∑ j ∈ Finset.univ.erase i, M i j * α j| := by
            congr 1; linarith
        _ ≤ |γ i| + |∑ j ∈ Finset.univ.erase i, M i j * α j| := abs_sub _ _
        _ ≤ |γ i| + ∑ j ∈ Finset.univ.erase i, |M i j * α j| :=
            add_le_add le_rfl (abs_sum_le_sum_abs _ _)
        _ = |γ i| + ∑ j ∈ Finset.univ.erase i, |M i j| * |α j| := by
            congr 1; exact sum_congr rfl fun j _ => abs_mul _ _
    have hsum_full : ∑ j : Fin k, |M i j| * |α j| =
        |α i| + ∑ j ∈ Finset.univ.erase i, |M i j| * |α j| := by
      rw [← Finset.add_sum_erase Finset.univ (fun j => |M i j| * |α j|) (mem_univ i),
        hMdiag i, abs_one, one_mul]
    linarith
  have hα_l1 : ∑ i : Fin k, |α i| < 1 := by
    have hsum1 : 2 * ∑ i : Fin k, |α i| - ∑ j : Fin k, |α j| * ∑ i : Fin k, |M i j| ≤
        ∑ i : Fin k, |γ i| := by
      have hsum_rows := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow_ineq i
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum_rows
      have hswap : ∑ i : Fin k, ∑ j : Fin k, |M i j| * |α j| =
          ∑ j : Fin k, |α j| * ∑ i : Fin k, |M i j| := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun i _ => mul_comm _ _
      rwa [← hswap]
    have hcol : ∀ j : Fin k, ∑ i : Fin k, |M i j| ≤ 3 / 2 := by
      intro j
      rw [← Finset.add_sum_erase Finset.univ (fun i => |M i j|) (mem_univ j), hMdiag j, abs_one]
      have : ∑ i ∈ Finset.univ.erase j, |M i j| = ∑ i ∈ Finset.univ.erase j, |M j i| :=
        sum_congr rfl fun i _ => by rw [hMsym i j]
      rw [this]
      have hpair' : ∑ i ∈ Finset.univ.erase j, |M j i| ≤ 1 / 2 := by
        simpa [M] using hpair j
      linarith
    have hsum2 : ∑ j : Fin k, |α j| * ∑ i : Fin k, |M i j| ≤
        (3 / 2 : ℝ) * ∑ j : Fin k, |α j| := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun j _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hcol j) (abs_nonneg _)
    linarith
  let raw : X → ℝ := fun x => 1 - f x * ∑ j : Fin k, α j * χ j x
  have hraw_pos : ∀ x : X, 0 < raw x := by
    intro x
    have hfx : |f x| = 1 := by rcases hf x with h | h <;> simp [h]
    have hbound : |f x * ∑ j : Fin k, α j * χ j x| ≤ ∑ j : Fin k, |α j| := by
      rw [abs_mul, hfx, one_mul]
      calc |∑ j : Fin k, α j * χ j x|
          ≤ ∑ j : Fin k, |α j * χ j x| := abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin k, |α j| := by
            refine sum_congr rfl fun j _ => ?_
            have hχx : |χ j x| = 1 := by rcases hχ j x with h | h <;> simp [h]
            rw [abs_mul, hχx, mul_one]
    have hle := (abs_le.1 hbound).2
    dsimp only [raw]
    linarith
  set Z : ℝ := ∑ x : X, raw x
  have hZpos : 0 < Z := Finset.sum_pos (fun x _ => hraw_pos x) Finset.univ_nonempty
  refine ⟨fun x => raw x / Z, fun x => div_pos (hraw_pos x) hZpos, ?_, fun i => ?_⟩
  · rw [← Finset.sum_div, div_self hZpos.ne']
  · have hnum : ∑ x : X, raw x * (f x * χ i x) = 0 := by
      have hcard_ne : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have h1 : ∑ x : X, raw x * (f x * χ i x) =
          (∑ x : X, f x * χ i x) - ∑ j : Fin k, α j * ∑ x : X, χ i x * χ j x := by
        calc ∑ x : X, (1 - f x * ∑ j : Fin k, α j * χ j x) * (f x * χ i x)
            = ∑ x : X, (f x * χ i x - ∑ j : Fin k, α j * (χ i x * χ j x)) := by
              refine sum_congr rfl fun x _ => ?_
              have hf2 : f x * f x = 1 := by rcases hf x with h | h <;> simp [h]
              rw [sub_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
              congr 1
              refine sum_congr rfl fun j _ => ?_
              calc f x * (α j * χ j x) * (f x * χ i x)
                  = (f x * f x) * (α j * (χ i x * χ j x)) := by ring
                _ = α j * (χ i x * χ j x) := by rw [hf2, one_mul]
          _ = (∑ x : X, f x * χ i x) - ∑ x : X, ∑ j : Fin k, α j * (χ i x * χ j x) :=
              Finset.sum_sub_distrib _ _
          _ = (∑ x : X, f x * χ i x) - ∑ j : Fin k, α j * ∑ x : X, χ i x * χ j x := by
              congr 1; rw [Finset.sum_comm]
              exact sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      rw [h1]
      have hγi : ∑ x : X, f x * χ i x = (Fintype.card X : ℝ) * γ i := by
        dsimp only [γ, uniformInnerProd]; field_simp [hcard_ne]
      have hMij : ∀ j, ∑ x : X, χ i x * χ j x = (Fintype.card X : ℝ) * M i j := by
        intro j; simp only [M, Matrix.of_apply, uniformInnerProd]; field_simp [hcard_ne]
      simp_rw [hγi, hMij]
      have hlin : ∑ j : Fin k, M i j * α j = γ i := by
        simpa [Matrix.mulVec, dotProduct] using congr_fun hMα i
      have hfact : ∑ j : Fin k, α j * ((Fintype.card X : ℝ) * M i j) =
          (Fintype.card X : ℝ) * ∑ j : Fin k, M i j * α j := by
        rw [Finset.mul_sum]; exact sum_congr rfl fun j _ => by ring
      rw [hfact, hlin, sub_self]
    calc ∑ x : X, raw x / Z * (f x * χ i x)
        = (∑ x : X, raw x * (f x * χ i x)) / Z := by
          rw [Finset.sum_div]; exact sum_congr rfl fun x _ => div_mul_eq_mul_div _ _ _
      _ = 0 := by rw [hnum, zero_div]

/-- Obstruction against sign representation: if `0 < f x * ∑ i, α i * χ i x` holds everywhere on
a finite type `X`, then no probability distribution `μ` on `X` can make `f` uncorrelated with
every `χ i`. -/
theorem not_exists_zero_correlation_dist_of_pos_mul {X : Type*} [Fintype X] {k : ℕ}
    (f : X → ℝ) (χ : Fin k → X → ℝ) (α : Fin k → ℝ)
    (hrep : ∀ x, 0 < f x * ∑ i : Fin k, α i * χ i x) :
    ¬ ∃ μ : X → ℝ, (∀ x, 0 ≤ μ x) ∧ (∑ x : X, μ x = 1) ∧
      ∀ i : Fin k, ∑ x : X, μ x * (f x * χ i x) = 0 := by
  rintro ⟨μ, hμ0, hμ1, hzero⟩
  have hsum_pos : 0 < ∑ x : X, μ x * (f x * ∑ i : Fin k, α i * χ i x) := by
    have hex : ∃ x : X, 0 < μ x := by
      by_contra hall
      push Not at hall
      have h0 : ∑ x : X, μ x ≤ 0 := Finset.sum_nonpos fun x _ => hall x
      linarith
    obtain ⟨x₀, hx₀⟩ := hex
    exact Finset.sum_pos' (fun x _ => mul_nonneg (hμ0 x) (hrep x).le)
      ⟨x₀, mem_univ x₀, mul_pos hx₀ (hrep x₀)⟩
  have hsum_zero : ∑ x : X, μ x * (f x * ∑ i : Fin k, α i * χ i x) = 0 := by
    calc ∑ x : X, μ x * (f x * ∑ i : Fin k, α i * χ i x)
        = ∑ x : X, ∑ i : Fin k, α i * (μ x * (f x * χ i x)) := by
          refine sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin k, α i * ∑ x : X, μ x * (f x * χ i x) := by
          rw [Finset.sum_comm]
          exact sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = 0 := by simp [hzero]
  linarith

end CslibFrontier.Foundations.BooleanAnalysis
