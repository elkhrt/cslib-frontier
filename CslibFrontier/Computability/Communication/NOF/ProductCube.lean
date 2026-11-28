/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Computability.Communication.NOF.Discrepancy
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Probability.Product
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Product-Measure Cube Cauchy-Schwarz and Fiberwise Fourier Bounds for NOF Cylinders

Product-measure correlation bounds for multiparty number-on-forehead (NOF) cylinder intersections
and multibit Boolean functions.

Given independent coordinate distributions `X : ∀ i : ι, PMF (α i)` and cylinder-like factors
`g : ι → (∀ j, α j) → ℝ` where each `g i` does not depend on coordinate `i` and takes values in
`[-1, 1]`, repeated application of Cauchy-Schwarz along each coordinate in `T : Finset ι` bounds
the `2 ^ |T|`-th power of `𝔼_{x ∼ ∏ X_j}[F(x) ∏_{i ∈ T} g_i(x)]` by the cube correlation
`𝔼_{a, b ∼ ∏ X_j}[∏_{S ⊆ T} F(S.piecewise b a)]` (`pow_sum_pi_mul_prod_le`). Specializing `g_i` to
the `[0, 1]` player indicators of `Cslib.Communication.NOF.cylinderIntersection φ` bounds the
signed correlation of any real-valued function on a cylinder intersection under an arbitrary
independent product distribution (`abs_sum_cylinderIntersection_le`).

For multibit outputs `f : α → BitString m` paired with an arbitrary transcript or side-information
map `g : α → β`, Parseval's identity on Boolean characters bounds the statistical distance between
the joint distribution `(f(X), g(X))` and the ideal product `(U_m, g(X))` in terms of the maximum
single-fiber character correlation (`dist_joint_uniform_le_of_fiber_corr`).

## Main results

* `CslibFrontier.Communication.NOF.pow_sum_pi_mul_prod_le`: product-measure cube Cauchy-Schwarz
  inequality over a subset `T` of coordinates.
* `CslibFrontier.Communication.NOF.abs_sum_cylinderIntersection_le`: `2 ^ |ι|`-th power cube bound
  for expectations restricted to `Cslib.Communication.NOF.cylinderIntersection φ`.
* `CslibFrontier.Communication.NOF.dist_joint_uniform_le_of_fiber_corr`: statistical distance from
  joint uniformity bounded by fiberwise Boolean character correlations.
-/

public section

namespace CslibFrontier.Communication.NOF

open Cslib Cslib.BitString Cslib.Probability Cslib.Probability.PMF Cslib.Communication Finset
open scoped BigOperators Cslib.Probability.PMF

/-! ### Product-measure cube Cauchy-Schwarz inequality -/

private theorem sum_toReal_pmf {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 :=
  Cslib.Probability.PMF.sum_toReal p

private theorem sum_pmf_mul_sq_le {α : Type*} [Fintype α] (p : PMF α) (u v : α → ℝ) :
    (∑ x, (p x).toReal * (u x * v x)) ^ 2 ≤
      (∑ x, (p x).toReal * u x ^ 2) * (∑ x, (p x).toReal * v x ^ 2) := by
  have hterm (x : α) :
      (p x).toReal * (u x * v x) =
        (Real.sqrt (p x).toReal * u x) * (Real.sqrt (p x).toReal * v x) := by
    have hsq : Real.sqrt (p x).toReal * Real.sqrt (p x).toReal = (p x).toReal :=
      Real.mul_self_sqrt ENNReal.toReal_nonneg
    calc (p x).toReal * (u x * v x)
        = (Real.sqrt (p x).toReal * Real.sqrt (p x).toReal) * (u x * v x) := by rw [hsq]
      _ = _ := by ring
  have hsq_u (x : α) : (Real.sqrt (p x).toReal * u x) ^ 2 = (p x).toReal * u x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hsq_v (x : α) : (Real.sqrt (p x).toReal * v x) ^ 2 = (p x).toReal * v x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  simp_rw [hterm, ← hsq_u, ← hsq_v]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

private theorem pow_two_pow_sum_pmf_le {α : Type*} [Fintype α] (p : PMF α) (z : α → ℝ) (k : ℕ) :
    (∑ x, (p x).toReal * z x) ^ (2 ^ k) ≤ ∑ x, (p x).toReal * z x ^ (2 ^ k) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_mul]
    have h1 : (∑ x, (p x).toReal * z x) ^ 2 ≤ ∑ x, (p x).toReal * z x ^ 2 := by
      have hcs := sum_pmf_mul_sq_le p z (fun _ => 1)
      simpa [sum_toReal_pmf p] using hcs
    calc ((∑ x, (p x).toReal * z x) ^ 2) ^ (2 ^ k)
        ≤ (∑ x, (p x).toReal * z x ^ 2) ^ (2 ^ k) := pow_le_pow_left₀ (sq_nonneg _) h1 _
      _ ≤ ∑ x, (p x).toReal * (z x ^ 2) ^ (2 ^ k) := ih (fun x => z x ^ 2)
      _ = ∑ x, (p x).toReal * z x ^ (2 * 2 ^ k) := by
          refine Finset.sum_congr rfl fun x _ => by rw [← pow_mul]

private theorem sum_pi_resample {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (X : ∀ i, PMF (α i)) (j : ι) (H : (∀ i, α i) → ℝ) :
    ∑ x, (PMF.pi X x).toReal * H x =
      ∑ x, (PMF.pi X x).toReal * ∑ c : α j, (X j c).toReal * H (Function.update x j c) := by
  have hbind := congrArg (fun q : PMF (∀ i, α i) => ∑ x, (q x).toReal * H x)
    (PMF.pi_bind_update X j).symm
  rw [hbind, sum_bind_mul]
  have hpush (c : α j) :
      PMF.pi (Function.update X j (PMF.pure c)) =
        (PMF.pi X).map (fun x => Function.update x j c) := by
    have hmap : ∀ i, Function.update X j (PMF.pure c) i =
        (X i).map (fun a => if h : i = j then h ▸ c else a) := by
      intro i
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self, ↓reduceDIte]
        exact (PMF.map_const (X i) c).symm
      · simp only [Function.update_of_ne hij, hij, ↓reduceDIte]
        exact (PMF.map_id (X i)).symm
    have hpi := PMF.pi_map X (fun i a => if h : i = j then h ▸ c else a)
    have hfun : (fun (x : ∀ i, α i) i => if h : i = j then h ▸ c else x i) =
        fun x => Function.update x j c := by
      funext x i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [funext hmap, hpi, hfun]
  simp_rw [hpush, sum_map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => by ring

private theorem piecewise_update_notMem {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    {S : Finset ι} {j : ι} (hj : j ∉ S) (a b : ∀ i, α i) (c d : α j) :
    S.piecewise (Function.update b j d) (Function.update a j c) =
      Function.update (S.piecewise b a) j c := by
  funext i
  by_cases hij : i = j
  · subst hij; simp [hj]
  · by_cases hi : i ∈ S <;> simp [hi, hij]

private theorem piecewise_insert_update {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    {S : Finset ι} {j : ι} (hj : j ∉ S) (a b : ∀ i, α i) (c d : α j) :
    (insert j S).piecewise (Function.update b j d) (Function.update a j c) =
      Function.update (S.piecewise b a) j d := by
  rw [Finset.piecewise_insert, piecewise_update_notMem hj, Function.update_idem,
    Function.update_self]

/-- **Product-measure cube Cauchy-Schwarz inequality**: for independent coordinate laws
`X : ∀ i : ι, PMF (α i)`, a subset `T : Finset ι`, a real-valued function `F`, and coordinatewise
invariant factors `g : ι → (∀ i, α i) → ℝ` bounded in `[-1, 1]`, the `2 ^ |T|`-th power of
`𝔼[F(x) ∏_{i ∈ T} g_i(x)]` is bounded above by the `T`-cube correlation of `F`. -/
theorem pow_sum_pi_mul_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (X : ∀ i, PMF (α i)) (T : Finset ι)
    (F : (∀ i, α i) → ℝ) (g : ι → (∀ i, α i) → ℝ)
    (hg : ∀ i ∈ T, ∀ x (e : α i), g i (Function.update x i e) = g i x)
    (hg1 : ∀ i ∈ T, ∀ x, |g i x| ≤ 1) :
    (∑ x, (PMF.pi X x).toReal * (F x * ∏ i ∈ T, g i x)) ^ (2 ^ T.card) ≤
      ∑ a, (PMF.pi X a).toReal * ∑ b, (PMF.pi X b).toReal *
        ∏ S ∈ T.powerset, F (S.piecewise b a) := by
  induction T using Finset.induction_on generalizing F g with
  | empty =>
    simp only [Finset.card_empty, pow_zero, pow_one, Finset.prod_empty, mul_one,
      Finset.powerset_empty, Finset.prod_singleton, Finset.piecewise_empty]
    have h1 : ∀ a : ∀ i, α i,
        ∑ b : ∀ i, α i, (PMF.pi X b).toReal * F a = F a := fun a => by
      rw [← Finset.sum_mul, sum_toReal_pmf (PMF.pi X), one_mul]
    simp_rw [h1]
    exact le_rfl
  | @insert j T hj ih =>
    rw [Finset.card_insert_of_notMem hj, pow_succ', pow_mul]
    have hres :
        ∑ x, (PMF.pi X x).toReal * (F x * ∏ i ∈ insert j T, g i x) =
          ∑ x, (PMF.pi X x).toReal * (g j x *
            ∑ c : α j, (X j c).toReal *
              (F (Function.update x j c) * ∏ i ∈ T, g i (Function.update x j c))) := by
      rw [sum_pi_resample X j]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.prod_insert hj, hg j (Finset.mem_insert_self j T) x c]
      ring
    have hcs :
        (∑ x, (PMF.pi X x).toReal * (F x * ∏ i ∈ insert j T, g i x)) ^ 2 ≤
          ∑ x, (PMF.pi X x).toReal *
            (∑ c : α j, (X j c).toReal *
              (F (Function.update x j c) * ∏ i ∈ T, g i (Function.update x j c))) ^ 2 := by
      rw [hres]
      refine (sum_pmf_mul_sq_le (PMF.pi X) _ _).trans ?_
      refine mul_le_of_le_one_left
        (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) ?_
      calc ∑ x, (PMF.pi X x).toReal * g j x ^ 2
          ≤ ∑ x, (PMF.pi X x).toReal * 1 := by
            refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            rw [← sq_abs]
            exact pow_le_one₀ (abs_nonneg _) (hg1 j (Finset.mem_insert_self j T) x)
        _ = 1 := by
          simp only [mul_one]
          exact sum_toReal_pmf (PMF.pi X)
    have hexp :
        (∑ x, (PMF.pi X x).toReal *
          (∑ c : α j, (X j c).toReal *
            (F (Function.update x j c) * ∏ i ∈ T, g i (Function.update x j c))) ^ 2) =
          ∑ c : α j, (X j c).toReal * ∑ d : α j, (X j d).toReal *
            ∑ x, (PMF.pi X x).toReal *
              ((F (Function.update x j c) * F (Function.update x j d)) *
                ∏ i ∈ T, (g i (Function.update x j c) * g i (Function.update x j d))) := by
      have hsq_expand (x : ∀ i, α i) :
          (∑ c : α j, (X j c).toReal *
            (F (Function.update x j c) * ∏ i ∈ T, g i (Function.update x j c))) ^ 2 =
            ∑ c : α j, (X j c).toReal * ∑ d : α j, (X j d).toReal *
              ((F (Function.update x j c) * F (Function.update x j d)) *
                ∏ i ∈ T, (g i (Function.update x j c) * g i (Function.update x j d))) := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
      simp_rw [hsq_expand, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      exact Finset.sum_congr rfl fun x _ => by ring
    have hih (c d : α j) :
        (∑ x, (PMF.pi X x).toReal *
          ((F (Function.update x j c) * F (Function.update x j d)) *
            ∏ i ∈ T, (g i (Function.update x j c) * g i (Function.update x j d)))) ^
          (2 ^ T.card) ≤
        ∑ a, (PMF.pi X a).toReal * ∑ b, (PMF.pi X b).toReal *
          ∏ S ∈ T.powerset,
            (F (Function.update (S.piecewise b a) j c) *
              F (Function.update (S.piecewise b a) j d)) := by
      refine ih
        (fun x => F (Function.update x j c) * F (Function.update x j d))
        (fun i x => g i (Function.update x j c) * g i (Function.update x j d))
        (fun i hi x e => ?_) (fun i hi x => ?_)
      · by_cases hij : i = j
        · subst hij; simp only [Function.update_idem]
        · rw [Function.update_comm hij e c x, Function.update_comm hij e d x,
            hg i (Finset.mem_insert_of_mem hi), hg i (Finset.mem_insert_of_mem hi)]
      · rw [abs_mul]
        exact (mul_le_mul (hg1 i (Finset.mem_insert_of_mem hi) _)
          (hg1 i (Finset.mem_insert_of_mem hi) _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hcube :
        (∑ c : α j, (X j c).toReal * ∑ d : α j, (X j d).toReal *
          ∑ a, (PMF.pi X a).toReal * ∑ b, (PMF.pi X b).toReal *
            ∏ S ∈ T.powerset,
              (F (Function.update (S.piecewise b a) j c) *
                F (Function.update (S.piecewise b a) j d))) =
        ∑ a, (PMF.pi X a).toReal * ∑ b, (PMF.pi X b).toReal *
          ∏ S ∈ (insert j T).powerset, F (S.piecewise b a) := by
      symm
      rw [sum_pi_resample X j]
      have hstep :
          (∑ a, (PMF.pi X a).toReal * ∑ c : α j, (X j c).toReal *
            ∑ b, (PMF.pi X b).toReal *
              ∏ S ∈ (insert j T).powerset, F (S.piecewise b (Function.update a j c))) =
          ∑ a, (PMF.pi X a).toReal * ∑ c : α j, (X j c).toReal *
            ∑ b, (PMF.pi X b).toReal * ∑ d : α j, (X j d).toReal *
              ∏ S ∈ (insert j T).powerset,
                F (S.piecewise (Function.update b j d) (Function.update a j c)) := by
        refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
        congr 1
        exact sum_pi_resample X j _
      rw [hstep]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hswap_ab :
          (∑ a, ∑ b, ∑ d,
            (PMF.pi X a).toReal * ((X j c).toReal *
              ((PMF.pi X b).toReal * ((X j d).toReal *
                ∏ S ∈ (insert j T).powerset,
                  F (S.piecewise (Function.update b j d) (Function.update a j c)))))) =
          ∑ d, ∑ a, ∑ b,
            (X j c).toReal * ((X j d).toReal *
              ((PMF.pi X a).toReal * ((PMF.pi X b).toReal *
                ∏ S ∈ T.powerset,
                  (F (Function.update (S.piecewise b a) j c) *
                    F (Function.update (S.piecewise b a) j d))))) := by
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_powerset_insert hj, ← Finset.prod_mul_distrib]
        have hprod :
            (∏ S ∈ T.powerset,
              (F (S.piecewise (Function.update b j d) (Function.update a j c)) *
                F ((insert j S).piecewise (Function.update b j d) (Function.update a j c)))) =
            ∏ S ∈ T.powerset,
              (F (Function.update (S.piecewise b a) j c) *
                F (Function.update (S.piecewise b a) j d)) := by
          refine Finset.prod_congr rfl fun S hS => ?_
          have hjS : j ∉ S := fun h => hj (Finset.mem_powerset.mp hS h)
          rw [piecewise_update_notMem hjS, piecewise_insert_update hjS]
        rw [hprod]
        ring
      rw [hswap_ab]
    calc ((∑ x, (PMF.pi X x).toReal * (F x * ∏ i ∈ insert j T, g i x)) ^ 2) ^ (2 ^ T.card)
        ≤ (∑ c : α j, (X j c).toReal * ∑ d : α j, (X j d).toReal *
            ∑ x, (PMF.pi X x).toReal *
              ((F (Function.update x j c) * F (Function.update x j d)) *
                ∏ i ∈ T, (g i (Function.update x j c) * g i (Function.update x j d)))) ^
          (2 ^ T.card) := hexp ▸ pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ ∑ c : α j, (X j c).toReal * ∑ d : α j, (X j d).toReal *
            (∑ x, (PMF.pi X x).toReal *
              ((F (Function.update x j c) * F (Function.update x j d)) *
                ∏ i ∈ T, (g i (Function.update x j c) * g i (Function.update x j d)))) ^
              (2 ^ T.card) := by
          refine (pow_two_pow_sum_pmf_le (X j) _ _).trans ?_
          exact Finset.sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_left (pow_two_pow_sum_pmf_le (X j) _ _) ENNReal.toReal_nonneg
      _ ≤ ∑ c : α j, (X j c).toReal * ∑ d : α j, (X j d).toReal *
            (∑ a, (PMF.pi X a).toReal * ∑ b, (PMF.pi X b).toReal *
              ∏ S ∈ T.powerset,
                (F (Function.update (S.piecewise b a) j c) *
                  F (Function.update (S.piecewise b a) j d))) := by
          refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          exact Finset.sum_le_sum fun d _ =>
            mul_le_mul_of_nonneg_left (hih c d) ENNReal.toReal_nonneg
      _ = _ := hcube

/-- **Product-measure cube bound for NOF cylinder intersections**: for nonempty index sets `ι`,
bounding the `2 ^ |ι|`-th power of `|𝔼_{x ∼ ∏ X_i}[1_{x ∈ cylinderIntersection φ} · F(x)]|` by the
full cube correlation of `F`. -/
theorem abs_sum_cylinderIntersection_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (X : ∀ i, PMF (α i))
    (φ : ∀ i, NOF.View α i → Bool)
    (F : (∀ i, α i) → ℝ) :
    |∑ x : ∀ i, α i,
        (PMF.pi X x).toReal *
          (if x ∈ NOF.cylinderIntersection φ then F x else 0)| ^ (2 ^ Fintype.card ι) ≤
      ∑ a : ∀ i, α i, (PMF.pi X a).toReal *
        ∑ b : ∀ i, α i, (PMF.pi X b).toReal *
          ∏ S : Finset ι, F (S.piecewise b a) := by
  let g (i : ι) (x : ∀ j, α j) : ℝ := if φ i (NOF.view i x) = true then 1 else 0
  have hrew (x : ∀ i, α i) :
      (if x ∈ NOF.cylinderIntersection φ then F x else 0) =
        F x * ∏ i : ι, g i x := by
    by_cases hx : x ∈ NOF.cylinderIntersection φ
    · have hall := NOF.mem_cylinderIntersection.mp hx
      have hp1 : ∏ i : ι, g i x = 1 := Finset.prod_eq_one fun i _ => by simp [g, hall i]
      simp [hx, hp1]
    · obtain ⟨i₀, hi₀⟩ := not_forall.mp (NOF.mem_cylinderIntersection.not.mp hx)
      have hp0 : ∏ i : ι, g i x = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [g, hi₀])
      simp [hx, hp0]
  simp_rw [hrew]
  have hcard_pos : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have heven : Even (2 ^ Fintype.card ι) := Nat.even_pow' hcard_pos |>.mpr even_two
  rw [heven.pow_abs]
  have hcube := pow_sum_pi_mul_prod_le X Finset.univ F g
    (fun i _ x v => by simp [g, NOF.view_update_self])
    (fun i _ _ => by dsimp only [g]; split_ifs <;> norm_num)
  rwa [Finset.card_univ, Finset.powerset_univ] at hcube

/-! ### Fiberwise Boolean Fourier joint-uniformity bound -/

private theorem sum_chi_mul_chi_bits {m : ℕ} (u v : BitString m) :
    ∑ S : Finset (Fin m), chi ℝ S u * chi ℝ S v = if u = v then (2 : ℝ) ^ m else 0 := by
  simpa using Cslib.BitString.sum_chi_mul_chi u v

/-- **Fiberwise Boolean Fourier joint-uniformity bound**: if every nonempty character `chi ℝ S` on
`BitString m` and every fiber `g⁻¹(π)` has correlation magnitude at most `α_corr` under `D`, then
the statistical distance between `D.map (fun x => (f x, g x))` and the independent product of
`PMF.uniformOfFintype (BitString m)` with `D.map g` is at most `2 ^ m * |β| * α_corr`. -/
theorem dist_joint_uniform_le_of_fiber_corr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] {m : ℕ} (D : PMF α) (f : α → BitString m) (g : α → β)
    {α_corr : ℝ} (hα : 0 ≤ α_corr)
    (hcorr : ∀ (S : Finset (Fin m)), S.Nonempty → ∀ π : β,
      |∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0)| ≤ α_corr) :
    dist (D.map fun x => (f x, g x))
      ((PMF.uniformOfFintype (BitString m)).bind fun u => D.map fun x => (u, g x)) ≤
      (2 : ℝ) ^ m * Fintype.card β * α_corr := by
  let P := D.map fun x => (f x, g x)
  let Q := (PMF.uniformOfFintype (BitString m)).bind fun u => D.map fun x => (u, g x)
  have hpt (z₀ : BitString m) (π : β) :
      ((P (z₀, π)).toReal - (Q (z₀, π)).toReal) * (2 : ℝ) ^ m =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.Nonempty),
          chi ℝ S z₀ * ∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0) := by
    have hP : (P (z₀, π)).toReal =
        ∑ x : α, (D x).toReal * if f x = z₀ ∧ g x = π then 1 else 0 := by
      simp only [P, map_apply_toReal, Prod.mk.injEq, eq_comm (a := z₀), eq_comm (a := π)]
      refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
    have hQ : (Q (z₀, π)).toReal =
        ((2 : ℝ) ^ m)⁻¹ * ∑ x : α, (D x).toReal * if g x = π then 1 else 0 := by
      simp only [Q, bind_apply_toReal, map_apply_toReal, PMF.uniformOfFintype_apply,
        ENNReal.toReal_inv, ENNReal.toReal_natCast]
      rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat]
      rw [← Finset.mul_sum, Finset.sum_eq_single z₀]
      · congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : g x = π
        · simp [hx]
        · have hx' : π ≠ g x := Ne.symm hx
          simp [hx, hx']
      · intro u _ huz
        exact Finset.sum_eq_zero fun x _ => by simp [huz.symm]
      · intro hz; exact absurd (Finset.mem_univ z₀) hz
    have hfull :
        ∑ S : Finset (Fin m),
          chi ℝ S z₀ * ∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0) =
          (P (z₀, π)).toReal * (2 : ℝ) ^ m := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner (x : α) :
          (∑ S : Finset (Fin m),
            chi ℝ S z₀ * ((D x).toReal * if g x = π then chi ℝ S (f x) else 0)) =
            (D x).toReal * ((if f x = z₀ ∧ g x = π then 1 else 0) * (2 : ℝ) ^ m) := by
        by_cases hg : g x = π
        · simp only [hg, ↓reduceIte, and_true]
          have : (∑ S : Finset (Fin m), chi ℝ S z₀ * ((D x).toReal * chi ℝ S (f x))) =
              (D x).toReal * ∑ S : Finset (Fin m), chi ℝ S (f x) * chi ℝ S z₀ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun S _ => by ring
          rw [this, sum_chi_mul_chi_bits]
          split_ifs <;> ring
        · simp [hg]
      simp_rw [hinner, ← mul_assoc]
      rw [← Finset.sum_mul, hP]
    have hempty :
        chi ℝ (∅ : Finset (Fin m)) z₀ *
          ∑ x : α, (D x).toReal * (if g x = π then chi ℝ ∅ (f x) else 0) =
          (Q (z₀, π)).toReal * (2 : ℝ) ^ m := by
      simp only [chi_empty, one_mul, hQ]
      field_simp
    have hsplit :
        (∑ S : Finset (Fin m),
          chi ℝ S z₀ * ∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0)) =
        (chi ℝ (∅ : Finset (Fin m)) z₀ *
          ∑ x : α, (D x).toReal * (if g x = π then chi ℝ ∅ (f x) else 0)) +
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.Nonempty),
          chi ℝ S z₀ * ∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin m)))]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext S
      simp [Finset.nonempty_iff_ne_empty]
    linarith
  have hpt_abs (z₀ : BitString m) (π : β) :
      |(P (z₀, π)).toReal - (Q (z₀, π)).toReal| ≤ α_corr := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have habs := congrArg abs (hpt z₀ π)
    rw [abs_mul, abs_of_pos hpow_pos] at habs
    have hsum_le :
        |∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.Nonempty),
          chi ℝ S z₀ * ∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0)| ≤
          (2 : ℝ) ^ m * α_corr := by
      calc _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.Nonempty),
              |chi ℝ S z₀ * ∑ x : α, (D x).toReal * (if g x = π then chi ℝ S (f x) else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.Nonempty), α_corr := by
            refine Finset.sum_le_sum fun S hS => ?_
            rw [abs_mul, abs_chi, one_mul]
            exact hcorr S (Finset.mem_filter.mp hS).2 π
        _ ≤ ∑ _S : Finset (Fin m), α_corr :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => hα
        _ = (2 : ℝ) ^ m * α_corr := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith
  rw [dist_eq]
  calc (∑ p : BitString m × β, |(P p).toReal - (Q p).toReal|) / 2
      ≤ (∑ _p : BitString m × β, α_corr) / 2 := by
        gcongr with p
        exact hpt_abs p.1 p.2
    _ = ((2 : ℝ) ^ m * Fintype.card β * α_corr) / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, BitString.card, nsmul_eq_mul,
          Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
    _ ≤ (2 : ℝ) ^ m * Fintype.card β * α_corr := by
        have : 0 ≤ (2 : ℝ) ^ m * Fintype.card β * α_corr := by positivity
        linarith

end CslibFrontier.Communication.NOF

end
