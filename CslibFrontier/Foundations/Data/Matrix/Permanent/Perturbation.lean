module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Entrywise Perturbation and Scaling Identities for Matrix Permanents

Provides an entrywise Lipschitz perturbation bound for real matrix permanents on the hypercube
`[-1, 1]^{N × N}`, together with scalar homogeneity and integer-to-real cast preservation.

## Main results

* `CslibFrontier.Matrix.abs_permanent_sub_le`: if `A, B ∈ [-1, 1]^{N × N}` satisfy
  `|A i j - B i j| ≤ ε` for all `i, j`, then `|Per(A) - Per(B)| ≤ N! · N · ε`.
* `CslibFrontier.Matrix.permanent_smul_real`: scaling every entry of an `N × N` real matrix by `c`
  scales its permanent by `c ^ N`.
* `CslibFrontier.Matrix.permanent_map_intCast`: casting an integer matrix entrywise to `ℝ`
  commutes with `Matrix.permanent`.
-/

public section

namespace CslibFrontier.Matrix

private theorem abs_prod_le_one {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |∏ i : Fin N, a i| ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.prod_univ_castSucc, abs_mul]
    have h1 : |∏ i : Fin N, a i.castSucc| ≤ 1 := ih (fun i => a i.castSucc) (fun i => ha i.castSucc)
    have h2 : |a (Fin.last N)| ≤ 1 := ha (Fin.last N)
    calc |∏ i : Fin N, a i.castSucc| * |a (Fin.last N)|
        ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

private theorem abs_prod_sub_prod_le {N : ℕ} (a b : Fin N → ℝ) {ε : ℝ}
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (hd : ∀ i, |a i - b i| ≤ ε) :
    |∏ i : Fin N, a i - ∏ i : Fin N, b i| ≤ (N : ℝ) * ε := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    set pa := ∏ i : Fin N, a i.castSucc
    set pb := ∏ i : Fin N, b i.castSucc
    have hsplit : pa * a (Fin.last N) - pb * b (Fin.last N) =
        (pa - pb) * a (Fin.last N) + pb * (a (Fin.last N) - b (Fin.last N)) := by ring
    rw [hsplit]
    have hpa : |pa - pb| ≤ (N : ℝ) * ε :=
      ih (fun i => a i.castSucc) (fun i => b i.castSucc)
        (fun i => ha i.castSucc) (fun i => hb i.castSucc) (fun i => hd i.castSucc)
    have hpb : |pb| ≤ 1 := abs_prod_le_one (fun i => b i.castSucc) (fun i => hb i.castSucc)
    have h1 : |(pa - pb) * a (Fin.last N)| ≤ (N : ℝ) * ε := by
      rw [abs_mul]
      calc |pa - pb| * |a (Fin.last N)|
          ≤ ((N : ℝ) * ε) * 1 := by
            gcongr
            · exact (abs_nonneg _).trans hpa
            · exact ha (Fin.last N)
        _ = (N : ℝ) * ε := mul_one _
    have h2 : |pb * (a (Fin.last N) - b (Fin.last N))| ≤ ε := by
      rw [abs_mul]
      calc |pb| * |a (Fin.last N) - b (Fin.last N)|
          ≤ 1 * ε := mul_le_mul hpb (hd (Fin.last N)) (abs_nonneg _) zero_le_one
        _ = ε := one_mul _
    calc |(pa - pb) * a (Fin.last N) + pb * (a (Fin.last N) - b (Fin.last N))|
        ≤ |(pa - pb) * a (Fin.last N)| + |pb * (a (Fin.last N) - b (Fin.last N))| :=
          abs_add_le _ _
      _ ≤ (N : ℝ) * ε + ε := add_le_add h1 h2
      _ = ((N + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- Entrywise permanent perturbation bound: if `A, B ∈ [-1, 1]^{N × N}` satisfy
`|A i j - B i j| ≤ ε`, then `|Per(A) - Per(B)| ≤ N! · N · ε`. -/
theorem abs_permanent_sub_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) {ε : ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) (hB : ∀ i j, |B i j| ≤ 1) (hd : ∀ i j, |A i j - B i j| ≤ ε) :
    |A.permanent - B.permanent| ≤ (N.factorial : ℝ) * (N : ℝ) * ε := by
  rw [Matrix.permanent, Matrix.permanent, ← Finset.sum_sub_distrib]
  calc |∑ σ : Equiv.Perm (Fin N), (∏ i, A (σ i) i - ∏ i, B (σ i) i)|
      ≤ ∑ σ : Equiv.Perm (Fin N), |∏ i, A (σ i) i - ∏ i, B (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), ((N : ℝ) * ε) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact abs_prod_sub_prod_le (fun i => A (σ i) i) (fun i => B (σ i) i)
          (fun i => hA (σ i) i) (fun i => hB (σ i) i) (fun i => hd (σ i) i)
    _ = (N.factorial : ℝ) * (N : ℝ) * ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
          mul_assoc]

/-- Scaling every entry of an `N × N` real matrix by `c` scales its permanent by `c ^ N`. -/
theorem permanent_smul_real {N : ℕ} (c : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    (Matrix.of fun i j => c * A i j).permanent = c ^ N * A.permanent := by
  rw [Matrix.permanent, Matrix.permanent, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The permanent of a real-cast integer matrix equals the real cast of its integer permanent. -/
theorem permanent_map_intCast {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    (A.map (Int.cast : ℤ → ℝ)).permanent = (A.permanent : ℝ) := by
  simp only [Matrix.permanent, Matrix.map_apply, Int.cast_sum, Int.cast_prod]

end CslibFrontier.Matrix
