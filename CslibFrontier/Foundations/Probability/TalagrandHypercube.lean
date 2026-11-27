module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Self-Contained Talagrand Convex-Distance Concentration on the Hypercube

This module gives a self-contained, `Mathlib`-only proof of Talagrand's convex-distance
exponential-moment inequality on `{0, 1}^ι` and the resulting
two-sided median concentration inequality for convex Euclidean `L`-Lipschitz functions under
product Bernoulli(`1/2`) measures.

## Main results

* `talagrandDistSq`: squared Talagrand convex distance `d_T(x, A)²` on `ι → Bool`.
* `talagrand_hypercube_exp_moment`: `E_x[exp(d_T(x, A)² / 4)] ≤ 1 / P(A)` for any nonempty
  `A ⊆ (ι → Bool)`.
* `talagrand_convex_lipschitz_bernoulli01_median`: two-sided median concentration
  `P[|f(x) - M| ≥ s] ≤ 4 exp(-s² / (4 L²))` for convex Euclidean `L`-Lipschitz `f` on `[0, 1]^ι`
  under product Bernoulli(`1/2`).
-/

public section

namespace CslibFrontier.Foundations.Probability

open MeasureTheory
open scoped ENNReal

section TalagrandHypercube

/-- Elementary 1-variable inequality at the core of Talagrand's inductive proof:
for every `r ∈ (0, 1]`, there exists `λ ∈ [0, 1]` such that
`(1 + r) * (1 + exp(λ² / 4) * r^(λ - 1)) ≤ 4`. -/
private theorem talagrand_one_dim_aux {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ lam ∈ Set.Icc (0 : ℝ) 1,
      (1 + r) * (1 + Real.exp (lam ^ 2 / 4) * r ^ (lam - 1)) ≤ 4 := by
  let u : ℝ := -Real.log r
  have hu0 : 0 ≤ u := by
    dsimp only [u]; linarith [Real.log_nonpos hr0.le hr1]
  have hr_eq : r = Real.exp (-u) := by dsimp only [u]; rw [neg_neg, Real.exp_log hr0]
  have hrpow : ∀ lam : ℝ, Real.exp (lam ^ 2 / 4) * r ^ (lam - 1) =
      Real.exp (lam ^ 2 / 4 + (1 - lam) * u) := by
    intro lam
    rw [Real.rpow_def_of_pos hr0, ← Real.exp_add]
    congr 1; dsimp only [u]; ring
  by_cases hu : u ≤ 1 / 2
  · refine ⟨2 * u, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hrpow, show (2 * u) ^ 2 / 4 + (1 - 2 * u) * u = u - u ^ 2 by ring, hr_eq]
    have hexp_comb : Real.exp (-u) * Real.exp (u - u ^ 2) = Real.exp (-(u ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 + (2 / 9 : ℝ) * u ^ 3 := by
      have hb := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg hu0]; linarith)
        (n := 3) (by norm_num)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add] at hb
      simp only [Nat.factorial, Nat.succ_eq_add_one, abs_neg, abs_of_nonneg hu0] at hb
      have hle := (abs_le.mp hb).2
      norm_num at hle
      linarith
    have h2 : Real.exp (u - u ^ 2) ≤ 1 + (u - u ^ 2) + (5 / 9 : ℝ) * (u - u ^ 2) ^ 2 := by
      have ht0 : 0 ≤ u - u ^ 2 := by nlinarith
      have ht1 : u - u ^ 2 ≤ 1 / 4 := by nlinarith
      have hb := Real.exp_bound (x := u - u ^ 2) (by rw [abs_of_nonneg ht0]; linarith)
        (n := 3) (by norm_num)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add] at hb
      simp only [Nat.factorial, Nat.succ_eq_add_one, abs_of_nonneg ht0] at hb
      have hle := (abs_le.mp hb).2
      norm_num at hle
      have hcub : (u - u ^ 2) ^ 3 * (2 / 9 : ℝ) ≤ (1 / 18 : ℝ) * (u - u ^ 2) ^ 2 := by
        have := mul_le_mul_of_nonneg_right ht1 (sq_nonneg (u - u ^ 2))
        have h3 : (u - u ^ 2) ^ 3 = (u - u ^ 2) * (u - u ^ 2) ^ 2 := by ring
        linarith
      linarith
    have h3 : Real.exp (-(u ^ 2)) ≤ 1 - u ^ 2 + (3 / 4 : ℝ) * u ^ 4 := by
      have ht0 : 0 ≤ u ^ 2 := sq_nonneg u
      have ht1 : u ^ 2 ≤ 1 / 4 := by nlinarith
      have hb := Real.exp_bound (x := -(u ^ 2)) (by rw [abs_neg, abs_of_nonneg ht0]; linarith)
        (n := 2) (by norm_num)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hb
      simp only [Nat.factorial, Nat.succ_eq_add_one, abs_neg, abs_of_nonneg ht0] at hb
      have hle := (abs_le.mp hb).2
      norm_num at hle
      have h4 : (u ^ 2) ^ 2 = u ^ 4 := by ring
      linarith
    have hexp_sum : Real.exp (-u) + Real.exp (u - u ^ 2) + Real.exp (-(u ^ 2)) ≤ 3 := by
      have hu4 : u ^ 4 ≤ (1 / 4 : ℝ) * u ^ 2 := by
        calc u ^ 4 = u ^ 2 * u ^ 2 := by ring
          _ ≤ (1 / 4 : ℝ) * u ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg u)
      have hpoly : (1 - u + u ^ 2 / 2 + (2 / 9 : ℝ) * u ^ 3) +
          (1 + (u - u ^ 2) + (5 / 9 : ℝ) * (u - u ^ 2) ^ 2) +
          (1 - u ^ 2 + (3 / 4 : ℝ) * u ^ 4) ≤ 3 := by
        have hstep : (1 - u + u ^ 2 / 2 + (2 / 9 : ℝ) * u ^ 3) +
            (1 + (u - u ^ 2) + (5 / 9 : ℝ) * (u - u ^ 2) ^ 2) +
            (1 - u ^ 2 + (3 / 4 : ℝ) * u ^ 4) =
            3 - (17 / 18 : ℝ) * u ^ 2 - (8 / 9 : ℝ) * u ^ 3 + (47 / 36 : ℝ) * u ^ 4 := by ring
        rw [hstep]
        nlinarith [sq_nonneg u, show 0 ≤ u ^ 3 by positivity]
      linarith
    calc (1 + Real.exp (-u)) * (1 + Real.exp (u - u ^ 2))
        = 1 + Real.exp (-u) + Real.exp (u - u ^ 2) + Real.exp (-u) * Real.exp (u - u ^ 2) := by ring
      _ = 1 + (Real.exp (-u) + Real.exp (u - u ^ 2) + Real.exp (-(u ^ 2))) := by
          rw [hexp_comb]; ring
      _ ≤ 1 + 3 := by linarith
      _ = 4 := by norm_num
  · push Not at hu
    refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [hrpow, show (1 : ℝ) ^ 2 / 4 + (1 - 1) * u = 1 / 4 by ring, hr_eq]
    have h14 : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
      have hb := Real.exp_bound (x := (1 / 4 : ℝ)) (by norm_num) (n := 3) (by norm_num)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add] at hb
      simp only [Nat.factorial, Nat.succ_eq_add_one] at hb
      have hle := (abs_le.mp hb).2; norm_num at hle; linarith
    have hm12 : Real.exp (-u) ≤ 2 / 3 := by
      have hge : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
        linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
      have hle1 : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
        rw [Real.exp_neg, inv_eq_one_div]
        have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 2) hge
        simpa [one_div] using this
      exact (Real.exp_le_exp.mpr (by linarith)).trans hle1
    nlinarith [Real.exp_pos (-u), Real.exp_pos (1 / 4 : ℝ)]

/-- Squared Talagrand convex distance `d_T(x, A)²` for a subset `A` of the finite hypercube
`ι → Bool`. -/
noncomputable def talagrandDistSq {ι : Type*} [Fintype ι]
    (A : Finset (ι → Bool)) (x : ι → Bool) : ℝ :=
  sInf {r : ℝ | ∃ w : (ι → Bool) → ℝ,
    (∀ y, 0 ≤ w y) ∧ (∑ y ∈ A, w y = 1) ∧
      (∑ i : ι, (∑ y ∈ A, if x i ≠ y i then w y else 0) ^ 2) = r}

private theorem talagrandDistSq_nonneg {ι : Type*} [Fintype ι]
    (A : Finset (ι → Bool)) (x : ι → Bool) : 0 ≤ talagrandDistSq A x := by
  dsimp only [talagrandDistSq]
  by_cases hne : {r : ℝ | ∃ w : (ι → Bool) → ℝ, (∀ y, 0 ≤ w y) ∧ (∑ y ∈ A, w y = 1) ∧
      (∑ i : ι, (∑ y ∈ A, if x i ≠ y i then w y else 0) ^ 2) = r}.Nonempty
  · refine le_csInf hne ?_
    rintro r ⟨_, _, _, rfl⟩
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

private theorem talagrandDistSq_le {ι : Type*} [Fintype ι]
    (A : Finset (ι → Bool)) (x : ι → Bool) (w : (ι → Bool) → ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y ∈ A, w y = 1) :
    talagrandDistSq A x ≤ ∑ i : ι, (∑ y ∈ A, if x i ≠ y i then w y else 0) ^ 2 := by
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw0, hw1, rfl⟩
  rintro r ⟨_, _, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private theorem talagrandDistSq_equiv {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (e : ι₁ ≃ ι₂) (A : Finset (ι₁ → Bool)) (x : ι₁ → Bool) :
    talagrandDistSq (A.image fun y ↦ y ∘ e.symm) (x ∘ e.symm) = talagrandDistSq A x := by
  classical
  dsimp only [talagrandDistSq]
  congr 1; ext r
  constructor
  · rintro ⟨w, hw0, hw1, hr⟩
    refine ⟨fun y ↦ w (y ∘ e.symm), fun y ↦ hw0 _, ?_, ?_⟩
    · rw [Finset.sum_image (fun a _ b _ h ↦ funext fun i ↦ by
        have := congrFun h (e i); simpa using this)] at hw1
      exact hw1
    · rw [← hr, ← Fintype.sum_equiv e]
      intro i
      congr 1
      rw [Finset.sum_image (fun a _ b _ h ↦ funext fun j ↦ by
        have := congrFun h (e j); simpa using this)]
      refine Finset.sum_congr rfl fun y _ ↦ by simp
  · rintro ⟨w, hw0, hw1, hr⟩
    refine ⟨fun z ↦ w (z ∘ e), fun z ↦ hw0 _, ?_, ?_⟩
    · rw [Finset.sum_image (fun a _ b _ h ↦ funext fun i ↦ by
        have := congrFun h (e i); simpa using this)]
      refine (Finset.sum_congr rfl fun y _ ↦ ?_).trans hw1
      have : (y ∘ e.symm) ∘ e = y := by ext i; simp
      rw [this]
    · rw [← hr, ← Fintype.sum_equiv e]
      intro i
      congr 1
      rw [Finset.sum_image (fun a _ b _ h ↦ funext fun j ↦ by
        have := congrFun h (e j); simpa using this)]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      have : (y ∘ e.symm) ∘ e = y := by ext j; simp
      simp [this]

/-- Flipping coordinate `0` on `Fin (n + 1) → Bool`. -/
private def flipZero {n : ℕ} (y : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  Fin.cons (!y 0) (Fin.tail y)

private theorem flipZero_involutive (n : ℕ) : Function.Involutive (@flipZero n) := by
  intro y; ext i
  refine Fin.cases ?_ ?_ i <;> simp [flipZero, Fin.tail]

private theorem talagrandDistSq_flipZero {n : ℕ} (A : Finset (Fin (n + 1) → Bool))
    (x : Fin (n + 1) → Bool) :
    talagrandDistSq (A.image flipZero) (flipZero x) = talagrandDistSq A x := by
  classical
  dsimp only [talagrandDistSq]
  congr 1; ext r
  have hinj : Function.Injective (@flipZero n) := (flipZero_involutive n).injective
  have hne_iff : ∀ y (i : Fin (n + 1)), flipZero x i ≠ flipZero y i ↔ x i ≠ y i := by
    intro y i; refine Fin.cases ?_ ?_ i <;> simp [flipZero, Fin.tail]
  constructor
  · rintro ⟨w, hw0, hw1, hr⟩
    refine ⟨fun y ↦ w (flipZero y), fun y ↦ hw0 _, ?_, ?_⟩
    · rwa [Finset.sum_image (fun a _ b _ h ↦ hinj h)] at hw1
    · rw [← hr]; refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_image (fun a _ b _ h ↦ hinj h)]
      congr 1; refine Finset.sum_congr rfl fun y _ ↦ by simp [hne_iff]
  · rintro ⟨w, hw0, hw1, hr⟩
    refine ⟨fun z ↦ w (flipZero z), fun z ↦ hw0 _, ?_, ?_⟩
    · rw [Finset.sum_image (fun a _ b _ h ↦ hinj h)]
      simpa [flipZero_involutive n _] using hw1
    · rw [← hr]; refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_image (fun a _ b _ h ↦ hinj h)]
      congr 1; refine Finset.sum_congr rfl fun y _ ↦ by simp [hne_iff, flipZero_involutive n _]

/-- Weighted finite Hölder inequality via AM-GM for `λ ∈ [0, 1]`. -/
private theorem finset_sum_rpow_mul_rpow_le {α : Type*} (s : Finset α) {f g : α → ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∑ x ∈ s, f x ^ (1 - lam) * g x ^ lam ≤
      (∑ x ∈ s, f x) ^ (1 - lam) * (∑ x ∈ s, g x) ^ lam := by
  by_cases hl0 : lam = 0
  · subst hl0; simp
  · by_cases hl1 : lam = 1
    · subst hl1; simp
    · have hp : 0 < 1 - lam := by
        have : lam < 1 := lt_of_le_of_ne h1 hl1; linarith
      have hq : 0 < lam := lt_of_le_of_ne h0 (Ne.symm hl0)
      set F := ∑ x ∈ s, f x
      set G := ∑ x ∈ s, g x
      have hF : 0 ≤ F := Finset.sum_nonneg hf
      have hG : 0 ≤ G := Finset.sum_nonneg hg
      rcases eq_or_lt_of_le hF with hF0 | hFpos
      · have hfx0 : ∀ x ∈ s, f x = 0 := fun x hx ↦
          le_antisymm (by have := Finset.single_le_sum hf hx; linarith) (hf x hx)
        have hlhs0 : ∑ x ∈ s, f x ^ (1 - lam) * g x ^ lam = 0 :=
          Finset.sum_eq_zero fun x hx ↦ by rw [hfx0 x hx, Real.zero_rpow hp.ne', zero_mul]
        rw [hlhs0, ← hF0, Real.zero_rpow hp.ne', zero_mul]
      · rcases eq_or_lt_of_le hG with hG0 | hGpos
        · have hgx0 : ∀ x ∈ s, g x = 0 := fun x hx ↦
            le_antisymm (by have := Finset.single_le_sum hg hx; linarith) (hg x hx)
          have hlhs0 : ∑ x ∈ s, f x ^ (1 - lam) * g x ^ lam = 0 :=
            Finset.sum_eq_zero fun x hx ↦ by rw [hgx0 x hx, Real.zero_rpow hq.ne', mul_zero]
          rw [hlhs0, ← hG0, Real.zero_rpow hq.ne', mul_zero]
        · have hdenom : 0 < F ^ (1 - lam) * G ^ lam :=
            mul_pos (Real.rpow_pos_of_pos hFpos _) (Real.rpow_pos_of_pos hGpos _)
          rw [← div_le_one hdenom, Finset.sum_div]
          have hterm : ∀ x ∈ s,
              f x ^ (1 - lam) * g x ^ lam / (F ^ (1 - lam) * G ^ lam) ≤
              (1 - lam) * (f x / F) + lam * (g x / G) := fun x hx ↦ by
            rw [mul_div_mul_comm, ← Real.div_rpow (hf x hx) hFpos.le,
              ← Real.div_rpow (hg x hx) hGpos.le]
            exact Real.geom_mean_le_arith_mean2_weighted hp.le hq.le
              (div_nonneg (hf x hx) hFpos.le) (div_nonneg (hg x hx) hGpos.le) (by ring)
          calc ∑ x ∈ s, f x ^ (1 - lam) * g x ^ lam / (F ^ (1 - lam) * G ^ lam)
              ≤ ∑ x ∈ s, ((1 - lam) * (f x / F) + lam * (g x / G)) := Finset.sum_le_sum hterm
            _ = (1 - lam) * ((∑ x ∈ s, f x) / F) + lam * ((∑ x ∈ s, g x) / G) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
                  ← Finset.sum_div, ← Finset.sum_div]
            _ = (1 - lam) * 1 + lam * 1 := by
                rw [div_self hFpos.ne', div_self hGpos.ne']
            _ = 1 := by ring

/-- Talagrand's exponential-moment inequality on `Fin n → Bool` (by induction on `n`). -/
private theorem talagrand_fin_exp_moment : ∀ (n : ℕ) (A : Finset (Fin n → Bool)), A.Nonempty →
    (∑ x : Fin n → Bool, Real.exp (talagrandDistSq A x / 4)) / (2 : ℝ) ^ n ≤
      (2 : ℝ) ^ n / (A.card : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro A hA
    have hcard0 : Fintype.card (Fin 0 → Bool) = 1 := by simp
    have hA1 : A = Finset.univ := Finset.eq_univ_of_card A (by
      have h1 : 1 ≤ A.card := Finset.card_pos.mpr hA
      have h2 : A.card ≤ Fintype.card (Fin 0 → Bool) := Finset.card_le_univ A
      omega)
    subst hA1
    have h0 : ∀ x : Fin 0 → Bool, talagrandDistSq Finset.univ x = 0 := fun x ↦ by
      refine le_antisymm ?_ (talagrandDistSq_nonneg _ _)
      have h := talagrandDistSq_le Finset.univ x (fun _ ↦ 1) (fun _ ↦ by norm_num) (by simp)
      simpa using h
    rw [Finset.sum_congr rfl fun x _ ↦ by rw [h0 x]]
    simp
  | succ n ih =>
    intro A hA
    -- Helper proving the inductive step under `A₁.card ≤ A₀.card` (symmetry via `flipZero`).
    have hstep_wlog : ∀ (B : Finset (Fin (n + 1) → Bool)), B.Nonempty →
        ((B.filter fun y ↦ y 0 = true).image Fin.tail).card ≤
          ((B.filter fun y ↦ y 0 = false).image Fin.tail).card →
        (∑ x : Fin (n + 1) → Bool, Real.exp (talagrandDistSq B x / 4)) / (2 : ℝ) ^ (n + 1) ≤
          (2 : ℝ) ^ (n + 1) / (B.card : ℝ) := by
      intro B hB hle_card
      let B0f := B.filter fun y ↦ y 0 = false
      let B1f := B.filter fun y ↦ y 0 = true
      let B0 := B0f.image Fin.tail
      let B1 := B1f.image Fin.tail
      have htail_inj : ∀ b : Bool, Set.InjOn Fin.tail {y : Fin (n + 1) → Bool | y 0 = b} := by
        intro b y₁ hy₁ y₂ hy₂ h; ext i
        refine Fin.cases ?_ ?_ i
        · exact hy₁.trans hy₂.symm
        · intro j; exact congrFun h j
      have hB0c : B0.card = B0f.card :=
        Finset.card_image_of_injOn fun y₁ hy₁ y₂ hy₂ h ↦
          htail_inj false (Finset.mem_filter.mp hy₁).2 (Finset.mem_filter.mp hy₂).2 h
      have hB1c : B1.card = B1f.card :=
        Finset.card_image_of_injOn fun y₁ hy₁ y₂ hy₂ h ↦
          htail_inj true (Finset.mem_filter.mp hy₁).2 (Finset.mem_filter.mp hy₂).2 h
      have hB0_sum : ∀ g : (Fin n → Bool) → ℝ,
          ∑ y' ∈ B0, g y' = ∑ y ∈ B0f, g (Fin.tail y) := fun g ↦
        Finset.sum_image fun y₁ hy₁ y₂ hy₂ h ↦
          htail_inj false (Finset.mem_filter.mp hy₁).2 (Finset.mem_filter.mp hy₂).2 h
      have hB1_sum : ∀ g : (Fin n → Bool) → ℝ,
          ∑ y' ∈ B1, g y' = ∑ y ∈ B1f, g (Fin.tail y) := fun g ↦
        Finset.sum_image fun y₁ hy₁ y₂ hy₂ h ↦
          htail_inj true (Finset.mem_filter.mp hy₁).2 (Finset.mem_filter.mp hy₂).2 h
      have hBcard : B0.card + B1.card = B.card := by
        rw [hB0c, hB1c]
        have := Finset.card_filter_add_card_filter_not (s := B) (p := fun y ↦ y 0 = false)
        have hneg : B.filter (fun y ↦ ¬y 0 = false) = B1f := by
          ext y; simp [B1f]
        rwa [hneg] at this
      have hB0ne : B0.Nonempty := by
        rw [← Finset.card_pos]; have : 0 < B.card := Finset.card_pos.mpr hB
        change B1.card ≤ B0.card at hle_card; omega
      have hsum_split : (∑ x : Fin (n + 1) → Bool, Real.exp (talagrandDistSq B x / 4)) =
          (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons false x') / 4)) +
          (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons true x') / 4)) := by
        let e : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) :=
          { toFun := fun x ↦ (x 0, Fin.tail x)
            invFun := fun p ↦ Fin.cons p.1 p.2
            left_inv := fun x ↦ by ext i; refine Fin.cases rfl (fun _ ↦ rfl) i
            right_inv := fun ⟨b, x'⟩ ↦ by ext <;> simp }
        rw [Fintype.sum_equiv e _ (fun p ↦ Real.exp (talagrandDistSq B (Fin.cons p.1 p.2) / 4))
          (fun x ↦ by simp [e, Fin.cons_self_tail]), Fintype.sum_prod_type, Fintype.sum_bool,
          add_comm]
      -- Bound for `x 0 = false`: `talagrandDistSq B (Fin.cons false x') ≤ talagrandDistSq B0 x'`.
      have hd_false : ∀ x' : Fin n → Bool,
          talagrandDistSq B (Fin.cons false x') ≤ talagrandDistSq B0 x' := by
        intro x'
        refine le_csInf ?_ ?_
        · obtain ⟨y₀, hy₀⟩ := hB0ne
          exact ⟨_, Pi.single y₀ 1, fun y ↦ by by_cases h : y = y₀ <;> simp [Pi.single, h],
            by simp [hy₀], rfl⟩
        · rintro r ⟨w0, hw0, hw1, rfl⟩
          let w : (Fin (n + 1) → Bool) → ℝ := fun y ↦ if y 0 = false then w0 (Fin.tail y) else 0
          have hw_nn : ∀ y, 0 ≤ w y := fun y ↦ by
            dsimp only [w]; by_cases h : y 0 = false <;> simp [h, hw0]
          have hw_sum : ∑ y ∈ B, w y = 1 := by
            dsimp only [w]
            rw [← Finset.sum_filter]
            change ∑ y ∈ B0f, w0 (Fin.tail y) = 1
            rw [← hB0_sum w0, hw1]
          refine (talagrandDistSq_le B (Fin.cons false x') w hw_nn hw_sum).trans ?_
          rw [Fin.sum_univ_succ]
          have h0_zero :
              (∑ y ∈ B, if (Fin.cons false x' : Fin (n + 1) → Bool) 0 ≠ y 0 then w y else 0) =
                0 := by
            refine Finset.sum_eq_zero fun y _ ↦ ?_
            dsimp only [w]; split_ifs with h1 h2 <;> simp_all
          rw [h0_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
          refine le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
          congr 1
          have hfilt : (∑ y ∈ B, if (Fin.cons false x' : Fin (n + 1) → Bool) i.succ ≠ y i.succ then
                w y else 0) =
              ∑ y' ∈ B0, if x' i ≠ y' i then w0 y' else 0 := by
            have h1 : (∑ y ∈ B, if (Fin.cons false x' : Fin (n + 1) → Bool) i.succ ≠ y i.succ then
                  w y else 0) =
                ∑ y ∈ B0f, if x' i ≠ Fin.tail y i then w0 (Fin.tail y) else 0 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun y _ ↦ ?_
              dsimp only [w]; simp only [Fin.cons_succ]
              by_cases hy : y 0 = false
              · simp only [hy, ↓reduceIte, Fin.tail]; by_cases hxi : x' i = y i.succ <;> simp [hxi]
              · simp [hy]
            rw [h1, ← hB0_sum (fun y' ↦ if x' i ≠ y' i then w0 y' else 0)]
          exact hfilt
      by_cases hB1ne : B1.Nonempty
      · -- Both `B0` and `B1` are nonempty; `r = B1.card / B0.card ∈ (0, 1]`.
        have hr0 : (0 : ℝ) < (B1.card : ℝ) / (B0.card : ℝ) :=
          div_pos (by exact_mod_cast Finset.card_pos.mpr hB1ne)
            (by exact_mod_cast Finset.card_pos.mpr hB0ne)
        have hr1 : (B1.card : ℝ) / (B0.card : ℝ) ≤ 1 :=
          (div_le_one (by exact_mod_cast Finset.card_pos.mpr hB0ne)).mpr
            (by exact_mod_cast hle_card)
        obtain ⟨lam, ⟨hlam0, hlam1⟩, h1d⟩ := talagrand_one_dim_aux hr0 hr1
        -- Convex-combination inequality for `x 0 = true`:
        have hd_true : ∀ x' : Fin n → Bool,
            talagrandDistSq B (Fin.cons true x') ≤
              lam ^ 2 + (1 - lam) * talagrandDistSq B1 x' + lam * talagrandDistSq B0 x' := by
          intro x'
          have h1 : ∀ (w1 w0 : (Fin n → Bool) → ℝ),
              (∀ y, 0 ≤ w1 y) → (∑ y ∈ B1, w1 y = 1) →
              (∀ y, 0 ≤ w0 y) → (∑ y ∈ B0, w0 y = 1) →
              talagrandDistSq B (Fin.cons true x') ≤
                lam ^ 2 + (1 - lam) * (∑ i : Fin n, (∑ y ∈ B1, if x' i ≠
                  y i then w1 y else 0) ^ 2) +
                  lam * (∑ i : Fin n, (∑ y ∈ B0, if x' i ≠ y i then w0 y else 0) ^ 2) := by
            intro w1 w0 hw1_0 hw1_1 hw0_0 hw0_1
            let w : (Fin (n + 1) → Bool) → ℝ := fun y ↦
              if y 0 = true then (1 - lam) * w1 (Fin.tail y) else lam * w0 (Fin.tail y)
            have hw_nn : ∀ y, 0 ≤ w y := fun y ↦ by
              dsimp only [w]; split_ifs
              · exact mul_nonneg (by linarith) (hw1_0 _)
              · exact mul_nonneg hlam0 (hw0_0 _)
            have hw_sum : ∑ y ∈ B, w y = 1 := by
              have hsp := Finset.sum_filter_add_sum_filter_not B (fun y ↦ y 0 = true) w
              rw [← hsp]
              have hneg : B.filter (fun y ↦ ¬y 0 = true) = B0f := by ext y; simp [B0f]
              have h1' : ∑ y ∈ B1f, w y = (1 - lam) * ∑ y' ∈ B1, w1 y' := by
                rw [hB1_sum w1, Finset.mul_sum]
                refine Finset.sum_congr rfl fun y hy ↦ by simp [w, (Finset.mem_filter.mp hy).2]
              have h0' : ∑ y ∈ B0f, w y = lam * ∑ y' ∈ B0, w0 y' := by
                rw [hB0_sum w0, Finset.mul_sum]
                refine Finset.sum_congr rfl fun y hy ↦ by simp [w, (Finset.mem_filter.mp hy).2]
              rw [hneg]; change ∑ y ∈ B1f, w y + ∑ y ∈ B0f, w y = 1
              rw [h1', h0', hw1_1, hw0_1]; ring
            refine (talagrandDistSq_le B (Fin.cons true x') w hw_nn hw_sum).trans ?_
            rw [Fin.sum_univ_succ]
            have h0_eq :
                (∑ y ∈ B, if (Fin.cons true x' : Fin (n + 1) → Bool) 0 ≠ y 0 then w y else 0) =
                  lam := by
              have h1' : (∑ y ∈ B, if (Fin.cons true x' : Fin (n + 1) → Bool) 0 ≠ y 0 then
                    w y else 0) =
                  ∑ y ∈ B0f, w y := by
                rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun y _ ↦ ?_
                simp only [Fin.cons_zero]; by_cases hy : y 0 = false <;> simp [hy]
              rw [h1']
              have h0' : ∑ y ∈ B0f, w y = lam * ∑ y' ∈ B0, w0 y' := by
                rw [hB0_sum w0, Finset.mul_sum]
                refine Finset.sum_congr rfl fun y hy ↦ by simp [w, (Finset.mem_filter.mp hy).2]
              rw [h0', hw0_1, mul_one]
            rw [h0_eq, add_assoc (lam ^ 2), Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib]
            gcongr with i _
            have hsp_i : (∑ y ∈ B, if (Fin.cons true x' : Fin (n + 1) → Bool) i.succ ≠ y i.succ then
                  w y else 0) =
                (1 - lam) * (∑ y' ∈ B1, if x' i ≠ y' i then w1 y' else 0) +
                lam * (∑ y' ∈ B0, if x' i ≠ y' i then w0 y' else 0) := by
              rw [← Finset.sum_filter_add_sum_filter_not B (fun y ↦ y 0 = true)]
              have hneg : B.filter (fun y ↦ ¬y 0 = true) = B0f := by ext y; simp [B0f]
              rw [hneg]
              have ha : (∑ y ∈ B1f,
                    if (Fin.cons true x' : Fin (n + 1) → Bool) i.succ ≠ y i.succ then w y else 0) =
                  (1 - lam) * (∑ y' ∈ B1, if x' i ≠ y' i then w1 y' else 0) := by
                rw [hB1_sum (fun y' ↦ if x' i ≠ y' i then w1 y' else 0), Finset.mul_sum]
                refine Finset.sum_congr rfl fun y hy ↦ ?_
                simp only [Fin.cons_succ, w, (Finset.mem_filter.mp hy).2, ↓reduceIte, Fin.tail]
                by_cases hxi : x' i = y i.succ <;> simp [hxi]
              have hb : (∑ y ∈ B0f,
                    if (Fin.cons true x' : Fin (n + 1) → Bool) i.succ ≠ y i.succ then w y else 0) =
                  lam * (∑ y' ∈ B0, if x' i ≠ y' i then w0 y' else 0) := by
                rw [hB0_sum (fun y' ↦ if x' i ≠ y' i then w0 y' else 0), Finset.mul_sum]
                refine Finset.sum_congr rfl fun y hy ↦ ?_
                simp only [Fin.cons_succ, w, (Finset.mem_filter.mp hy).2, Bool.false_eq_true,
                  ↓reduceIte, Fin.tail]
                by_cases hxi : x' i = y i.succ <;> simp [hxi]
              exact congrArg₂ (· + ·) ha hb
            rw [hsp_i]
            set a := ∑ y' ∈ B1, if x' i ≠ y' i then w1 y' else 0
            set b := ∑ y' ∈ B0, if x' i ≠ y' i then w0 y' else 0
            have hconv : ((1 - lam) * a + lam * b) ^ 2 ≤ (1 - lam) * a ^ 2 + lam * b ^ 2 := by
              have hpos : 0 ≤ lam * (1 - lam) * (a - b) ^ 2 :=
                mul_nonneg (mul_nonneg hlam0 (by linarith)) (sq_nonneg _)
              linarith
            exact hconv
          -- Take `sInf` first over `w1`, then over `w0`!
          have h2 : ∀ w0 : (Fin n → Bool) → ℝ, (∀ y, 0 ≤ w0 y) → (∑ y ∈ B0, w0 y = 1) →
              talagrandDistSq B (Fin.cons true x') - lam ^ 2 -
                lam * (∑ i : Fin n, (∑ y ∈ B0, if x' i ≠ y i then w0 y else 0) ^ 2) ≤
                (1 - lam) * talagrandDistSq B1 x' := by
            intro w0 hw0_0 hw0_1
            by_cases hl1 : lam = 1
            · subst hl1; simp only [sub_self, zero_mul, one_mul]
              have h3 := h1 (Pi.single hB1ne.choose 1) w0
                (fun y ↦ by by_cases h : y = hB1ne.choose <;> simp [Pi.single, h])
                (by simp [hB1ne.choose_spec]) hw0_0 hw0_1
              linarith
            · have hpos1 : 0 < 1 - lam := by have : lam < 1 := lt_of_le_of_ne hlam1 hl1; linarith
              rw [← div_le_iff₀' hpos1]
              refine le_csInf ?_ ?_
              · exact ⟨_, Pi.single hB1ne.choose 1,
                  fun y ↦ by by_cases h : y = hB1ne.choose <;> simp [Pi.single, h],
                  by simp [hB1ne.choose_spec], rfl⟩
              · rintro r ⟨w1, hw1_0, hw1_1, rfl⟩
                rw [div_le_iff₀' hpos1]; linarith [h1 w1 w0 hw1_0 hw1_1 hw0_0 hw0_1]
          by_cases hl0 : lam = 0
          · subst hl0
            simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero, sub_zero, one_mul]
            have h3 := h2 (Pi.single hB0ne.choose 1)
              (fun y ↦ by by_cases h : y = hB0ne.choose <;> simp [Pi.single, h])
              (by simp [hB0ne.choose_spec])
            linarith
          · have hpos0 : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hl0)
            have h3 : (talagrandDistSq B (Fin.cons true x') - lam ^ 2 -
                (1 - lam) * talagrandDistSq B1 x') / lam ≤ talagrandDistSq B0 x' := by
              refine le_csInf ?_ ?_
              · exact ⟨_, Pi.single hB0ne.choose 1,
                  fun y ↦ by by_cases h : y = hB0ne.choose <;> simp [Pi.single, h],
                  by simp [hB0ne.choose_spec], rfl⟩
              · rintro r ⟨w0, hw0_0, hw0_1, rfl⟩
                rw [div_le_iff₀ hpos0]; linarith [h2 w0 hw0_0 hw0_1]
            have := (div_le_iff₀ hpos0).mp h3; linarith
        -- Apply finite Hölder + IH!
        have hS0 : (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B0 x' / 4)) ≤
            (2 : ℝ) ^ (2 * n) / (B0.card : ℝ) := by
          have h := ih B0 hB0ne
          rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast Finset.card_pos.mpr hB0ne)] at h
          rw [le_div_iff₀ (by exact_mod_cast Finset.card_pos.mpr hB0ne)]
          simpa [two_mul, pow_add] using h
        have hS1 : (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B1 x' / 4)) ≤
            (2 : ℝ) ^ (2 * n) / (B1.card : ℝ) := by
          have h := ih B1 hB1ne
          rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast Finset.card_pos.mpr hB1ne)] at h
          rw [le_div_iff₀ (by exact_mod_cast Finset.card_pos.mpr hB1ne)]
          simpa [two_mul, pow_add] using h
        have hsum_false : ∑ x' : Fin n → Bool,
            Real.exp (talagrandDistSq B (Fin.cons false x') / 4) ≤
            (2 : ℝ) ^ (2 * n) / (B0.card : ℝ) :=
          (Finset.sum_le_sum fun x' _ ↦ Real.exp_le_exp.mpr (by linarith [hd_false x'])).trans hS0
        have hsum_true : ∑ x' : Fin n → Bool,
            Real.exp (talagrandDistSq B (Fin.cons true x') / 4) ≤
            Real.exp (lam ^ 2 / 4) * ((B1.card : ℝ) / (B0.card : ℝ)) ^ (lam - 1) *
              ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by
          have hpt : ∀ x' : Fin n → Bool,
              Real.exp (talagrandDistSq B (Fin.cons true x') / 4) ≤
              Real.exp (lam ^ 2 / 4) *
                (Real.exp (talagrandDistSq B1 x' / 4) ^ (1 - lam) *
                 Real.exp (talagrandDistSq B0 x' / 4) ^ lam) := fun x' ↦ by
            rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            have := hd_true x'; linarith
          calc ∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons true x') / 4)
              ≤ ∑ x' : Fin n → Bool, Real.exp (lam ^ 2 / 4) *
                  (Real.exp (talagrandDistSq B1 x' / 4) ^ (1 - lam) *
                   Real.exp (talagrandDistSq B0 x' / 4) ^ lam) :=
                     Finset.sum_le_sum fun x' _ ↦ hpt x'
            _ = Real.exp (lam ^ 2 / 4) * ∑ x' : Fin n → Bool,
                  Real.exp (talagrandDistSq B1 x' / 4) ^ (1 - lam) *
                  Real.exp (talagrandDistSq B0 x' / 4) ^ lam := by rw [← Finset.mul_sum]
            _ ≤ Real.exp (lam ^ 2 / 4) *
                  ((∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B1 x' / 4)) ^ (1 - lam) *
                   (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B0 x' / 4)) ^ lam) :=
                mul_le_mul_of_nonneg_left
                  (finset_sum_rpow_mul_rpow_le _ (fun _ _ ↦ (Real.exp_pos _).le)
                    (fun _ _ ↦ (Real.exp_pos _).le) hlam0 hlam1) (Real.exp_pos _).le
            _ ≤ Real.exp (lam ^ 2 / 4) *
                  (((2 : ℝ) ^ (2 * n) / (B1.card : ℝ)) ^ (1 - lam) *
                   ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) ^ lam) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul
                  (Real.rpow_le_rpow
                    (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le) hS1 (by linarith))
                  (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le) hS0 hlam0)
                  (by positivity) (by positivity)) (Real.exp_pos _).le
            _ = Real.exp (lam ^ 2 / 4) * ((B1.card : ℝ) / (B0.card : ℝ)) ^ (lam - 1) *
                  ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by
                have hB0p : (0 : ℝ) < (B0.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB0ne
                have hB1p : (0 : ℝ) < (B1.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB1ne
                have h2p : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := by positivity
                have hA_id : ((2 : ℝ) ^ (2 * n) / (B1.card : ℝ)) ^ (1 - lam) *
                    ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) ^ lam =
                    ((B1.card : ℝ) / (B0.card : ℝ)) ^ (lam - 1) *
                      ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by
                  rw [Real.div_rpow h2p.le hB1p.le, Real.div_rpow h2p.le hB0p.le,
                    Real.div_rpow hB1p.le hB0p.le]
                  have h1 : ((2 : ℝ) ^ (2 * n)) ^ (1 - lam) * ((2 : ℝ) ^ (2 * n)) ^ lam =
                      (2 : ℝ) ^ (2 * n) := by
                    rw [← Real.rpow_add h2p]; simp
                  have h2 : (B0.card : ℝ) ^ (lam - 1) * (B0.card : ℝ) = (B0.card : ℝ) ^ lam := by
                    conv_rhs => rw [show lam = (lam - 1) + 1 by ring]
                    rw [Real.rpow_add hB0p, Real.rpow_one]
                  have h3 : (B1.card : ℝ) ^ (lam - 1) = ((B1.card : ℝ) ^ (1 - lam))⁻¹ := by
                    rw [← Real.rpow_neg hB1p.le]; congr 1; ring
                  rw [h3, div_mul_div_comm, h1]
                  have hB0_r : (B0.card : ℝ) ^ lam = (B0.card : ℝ) ^ (lam - 1) * (B0.card : ℝ) :=
                    h2.symm
                  simp only [div_eq_mul_inv, mul_inv, hB0_r]
                  ring
                rw [hA_id, mul_assoc]
        rw [hsum_split]
        have hB0p : (0 : ℝ) < (B0.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB0ne
        have hBp : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
        have hB_eq : (B.card : ℝ) = (B0.card : ℝ) * (1 + (B1.card : ℝ) / (B0.card : ℝ)) := by
          have : (B.card : ℝ) = (B0.card : ℝ) + (B1.card : ℝ) := by exact_mod_cast hBcard.symm
          rw [this]; field_simp [hB0p.ne']
        have hcomb : (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons false x') / 4)) +
            (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons true x') / 4)) ≤
            (4 / (1 + (B1.card : ℝ) / (B0.card : ℝ))) * ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by
          have h1 : (1 + Real.exp (lam ^ 2 / 4) * ((B1.card : ℝ) / (B0.card : ℝ)) ^ (lam - 1)) ≤
              4 / (1 + (B1.card : ℝ) / (B0.card : ℝ)) := by
            rw [le_div_iff₀ (by positivity)]; rw [mul_comm]; exact h1d
          have := add_le_add hsum_false hsum_true
          have h2 : (2 : ℝ) ^ (2 * n) / (B0.card : ℝ) +
              Real.exp (lam ^ 2 / 4) * ((B1.card : ℝ) / (B0.card : ℝ)) ^ (lam - 1) *
                ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) =
              (1 + Real.exp (lam ^ 2 / 4) * ((B1.card : ℝ) / (B0.card : ℝ)) ^ (lam - 1)) *
                ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by ring
          rw [h2] at this
          exact this.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
        rw [div_le_div_iff₀ (by positivity) hBp]
        have hrhs_eq : (4 / (1 + (B1.card : ℝ) / (B0.card : ℝ))) *
            ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) * (B.card : ℝ) =
            (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) := by
          rw [hB_eq, show (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n by rw [two_mul, pow_add],
            pow_succ]
          field_simp [hB0p.ne', (show (0 : ℝ) < 1 +
            (B1.card : ℝ) / (B0.card : ℝ) by positivity).ne']
          ring
        have := mul_le_mul_of_nonneg_right hcomb hBp.le
        linarith
      · -- `B1 = ∅`, so `B.card = B0.card`, `B1.card = 0`.
        have hB1_zero : B1.card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB1ne)
        have hB_eq : B.card = B0.card := by omega
        have hd_true1 : ∀ x' : Fin n → Bool,
            talagrandDistSq B (Fin.cons true x') ≤ 1 + talagrandDistSq B0 x' := by
          intro x'
          suffices hsub1 : talagrandDistSq B (Fin.cons true x') - 1 ≤ talagrandDistSq B0 x' by
            linarith
          refine le_csInf ?_ ?_
          · obtain ⟨y₀, hy₀⟩ := hB0ne
            exact ⟨_, Pi.single y₀ 1, fun y ↦ by by_cases h : y = y₀ <;> simp [Pi.single, h],
              by simp [hy₀], rfl⟩
          · rintro r ⟨w0, hw0, hw1, rfl⟩
            let w : (Fin (n + 1) → Bool) → ℝ := fun y ↦ if y 0 = false then w0 (Fin.tail y) else 0
            have hw_nn : ∀ y, 0 ≤ w y := fun y ↦ by
              dsimp only [w]; by_cases h : y 0 = false <;> simp [h, hw0]
            have hw_sum : ∑ y ∈ B, w y = 1 := by
              dsimp only [w]
              rw [← Finset.sum_filter]
              change ∑ y ∈ B0f, w0 (Fin.tail y) = 1
              rw [← hB0_sum w0, hw1]
            have hsub := talagrandDistSq_le B (Fin.cons true x') w hw_nn hw_sum
            have hstep_le : talagrandDistSq B (Fin.cons true x') ≤
                1 + ∑ i : Fin n, (∑ y ∈ B0, if x' i ≠ y i then w0 y else 0) ^ 2 := by
              refine hsub.trans ?_
              rw [Fin.sum_univ_succ]
              have h0_one :
                  (∑ y ∈ B, if (Fin.cons true x' : Fin (n + 1) → Bool) 0 ≠ y 0 then w y else 0) =
                    1 := by
                have h1' : (∑ y ∈ B, if (Fin.cons true x' : Fin (n + 1) → Bool) 0 ≠ y 0 then
                      w y else 0) =
                    ∑ y ∈ B0f, w y := by
                  rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun y _ ↦ ?_
                  simp only [Fin.cons_zero]; by_cases hy : y 0 = false <;> simp [hy]
                rw [h1']
                have h2' : ∑ y ∈ B0f, w y = ∑ y ∈ B0f, w0 (Fin.tail y) :=
                  Finset.sum_congr rfl fun y hy ↦ by simp [w, (Finset.mem_filter.mp hy).2]
                rw [h2', ← hB0_sum w0, hw1]
              rw [h0_one, one_pow]
              refine le_of_eq (congrArg (1 + ·) (Finset.sum_congr rfl fun i _ ↦ ?_))
              congr 1
              have h1' : (∑ y ∈ B, if (Fin.cons true x' : Fin (n + 1) → Bool) i.succ ≠ y i.succ then
                    w y else 0) =
                  ∑ y ∈ B0f, if x' i ≠ Fin.tail y i then w0 (Fin.tail y) else 0 := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun y _ ↦ ?_
                dsimp only [w]; simp only [Fin.cons_succ]
                by_cases hy : y 0 = false
                · simp only [hy, ↓reduceIte, Fin.tail]
                  by_cases hxi : x' i = y i.succ <;> simp [hxi]
                · simp [hy]
              rw [h1', ← hB0_sum (fun y' ↦ if x' i ≠ y' i then w0 y' else 0)]
            linarith
        have hS0 : (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B0 x' / 4)) ≤
            (2 : ℝ) ^ (2 * n) / (B0.card : ℝ) := by
          have h := ih B0 hB0ne
          rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast Finset.card_pos.mpr hB0ne)] at h
          rw [le_div_iff₀ (by exact_mod_cast Finset.card_pos.mpr hB0ne)]
          simpa [two_mul, pow_add] using h
        have h14 : Real.exp (1 / 4 : ℝ) ≤ 3 := by
          have hb := Real.exp_bound (x := (1 / 4 : ℝ)) (by norm_num) (n := 3) (by norm_num)
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_zero, zero_add] at hb
          simp only [Nat.factorial, Nat.succ_eq_add_one] at hb
          have hle := (abs_le.mp hb).2; norm_num at hle; linarith
        rw [hsum_split, hB_eq]
        have hsum1 : ∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons false x') / 4) ≤
            (2 : ℝ) ^ (2 * n) / (B0.card : ℝ) :=
          (Finset.sum_le_sum fun x' _ ↦ Real.exp_le_exp.mpr (by linarith [hd_false x'])).trans hS0
        have hsum2 : ∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons true x') / 4) ≤
            Real.exp (1 / 4 : ℝ) * ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by
          have h1 : ∀ x', Real.exp (talagrandDistSq B (Fin.cons true x') / 4) ≤
              Real.exp (1 / 4 : ℝ) * Real.exp (talagrandDistSq B0 x' / 4) := fun x' ↦ by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [hd_true1 x'])
          exact (Finset.sum_le_sum fun x' _ ↦ h1 x').trans
            (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hS0 (Real.exp_pos _).le)
        have htot : (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons false x') / 4)) +
            (∑ x' : Fin n → Bool, Real.exp (talagrandDistSq B (Fin.cons true x') / 4)) ≤
            4 * ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) := by
          have := add_le_add hsum1 hsum2
          nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (2 * n) / (B0.card : ℝ) by positivity]
        rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast Finset.card_pos.mpr hB0ne)]
        have hB0p : (0 : ℝ) < (B0.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB0ne
        have hrhs : 4 * ((2 : ℝ) ^ (2 * n) / (B0.card : ℝ)) * (B0.card : ℝ) =
            (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) := by
          rw [show (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n by rw [two_mul, pow_add],
            pow_succ]
          field_simp [hB0p.ne']; ring
        have := mul_le_mul_of_nonneg_right htot hB0p.le
        linarith
    by_cases hcard :
        ((A.filter fun y ↦ y 0 = true).image Fin.tail).card ≤
          ((A.filter fun y ↦ y 0 = false).image Fin.tail).card
    · exact hstep_wlog A hA hcard
    · -- Flip coordinate `0` to reduce to `A₁.card ≤ A₀.card`!
      let A' := A.image flipZero
      have hinj : Function.Injective (@flipZero n) := (flipZero_involutive n).injective
      have hA'ne : A'.Nonempty := hA.image _
      have hA'c : A'.card = A.card := Finset.card_image_of_injective A hinj
      have hswap1 : ((A'.filter fun y ↦ y 0 = true).image Fin.tail) =
          ((A.filter fun y ↦ y 0 = false).image Fin.tail) := by
        ext z; simp only [A', Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hy0⟩, rfl⟩
          exact ⟨y, ⟨hy, by simpa [flipZero] using hy0⟩, by ext i; simp [flipZero]⟩
        · rintro ⟨y, ⟨hy, hy0⟩, rfl⟩
          exact ⟨flipZero y, ⟨⟨y, hy, rfl⟩, by simp [flipZero, hy0]⟩, by ext i; simp [flipZero]⟩
      have hswap2 : ((A'.filter fun y ↦ y 0 = false).image Fin.tail) =
          ((A.filter fun y ↦ y 0 = true).image Fin.tail) := by
        ext z; simp only [A', Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hy0⟩, rfl⟩
          exact ⟨y, ⟨hy, by simpa [flipZero] using hy0⟩, by ext i; simp [flipZero]⟩
        · rintro ⟨y, ⟨hy, hy0⟩, rfl⟩
          exact ⟨flipZero y, ⟨⟨y, hy, rfl⟩, by simp [flipZero, hy0]⟩, by ext i; simp [flipZero]⟩
      have hcard' : ((A'.filter fun y ↦ y 0 = true).image Fin.tail).card ≤
          ((A'.filter fun y ↦ y 0 = false).image Fin.tail).card := by
        rw [hswap1, hswap2]; omega
      have hres := hstep_wlog A' hA'ne hcard'
      rw [hA'c] at hres
      have hsum_eq : ∑ x : Fin (n + 1) → Bool, Real.exp (talagrandDistSq A' x / 4) =
          ∑ x : Fin (n + 1) → Bool, Real.exp (talagrandDistSq A x / 4) := by
        refine Fintype.sum_equiv (Equiv.ofBijective flipZero ⟨hinj,
          (flipZero_involutive n).surjective⟩)
          _ _ fun x ↦ ?_
        change Real.exp (talagrandDistSq (A.image flipZero) x / 4) =
          Real.exp (talagrandDistSq A (flipZero x) / 4)
        rw [← talagrandDistSq_flipZero A (flipZero x), flipZero_involutive n x]
      rwa [hsum_eq] at hres

/-- **Talagrand's Exponential-Moment Inequality on the Hypercube**:
for any finite type `ι` and any nonempty `A ⊆ (ι → Bool)`,
`((∑ x, exp(d_T(x, A)² / 4)) / 2^|ι|) ≤ 2^|ι| / |A|`. -/
theorem talagrand_hypercube_exp_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Bool)) (hA : A.Nonempty) :
    (∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4)) / (2 : ℝ) ^ Fintype.card ι ≤
      (2 : ℝ) ^ Fintype.card ι / (A.card : ℝ) := by
  classical
  let e := Fintype.equivFin ι
  let A' : Finset (Fin (Fintype.card ι) → Bool) := A.image fun y ↦ y ∘ e.symm
  have hinj : Function.Injective (fun y : ι → Bool ↦ y ∘ e.symm) :=
    fun a b h ↦ funext fun i ↦ by have := congrFun h (e i); simpa using this
  have hres := talagrand_fin_exp_moment (Fintype.card ι) A' (hA.image _)
  rw [Finset.card_image_of_injective A hinj] at hres
  have hsum : ∑ x : Fin (Fintype.card ι) → Bool, Real.exp (talagrandDistSq A' x / 4) =
      ∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4) := by
    let eFun : (ι → Bool) ≃ (Fin (Fintype.card ι) → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
    refine (Fintype.sum_equiv eFun _ _ fun x ↦ ?_).symm
    change Real.exp (talagrandDistSq A x / 4) = Real.exp (talagrandDistSq A' (x ∘ e.symm) / 4)
    rw [talagrandDistSq_equiv e A x]
  rwa [hsum] at hres

/-- **Talagrand's Two-Sided Median Concentration Inequality on `[0, 1]^ι` under Product
Bernoulli(`1/2`)**: if `f : (ι → ℝ) → ℝ` is measurable, convex on `[0, 1]^ι`, and Euclidean
`L`-Lipschitz on `[0, 1]^ι` (`L > 0`), and `M` is a median of `f` under `Measure.pi μ` (where
`μ i = (1/2) δ_0 + (1/2) δ_1`), then for every `s ≥ 0`,
`(Measure.pi μ).real {x | s ≤ |f x - M|} ≤ 4 * exp(-s² / (4 L²))`. -/
theorem talagrand_convex_lipschitz_bernoulli01_median {ι : Type*} [Fintype ι]
    {μ : ι → Measure ℝ}
    (hμ : ∀ i, μ i = (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1)
    {M L : ℝ} {f : (ι → ℝ) → ℝ} (_hf_meas : Measurable f)
    (hf_conv : ConvexOn ℝ (Set.univ.pi fun _ : ι ↦ Set.Icc (0 : ℝ) 1) f)
    (hL : 0 < L)
    (hf_lip : ∀ x ∈ Set.univ.pi (fun _ : ι ↦ Set.Icc (0 : ℝ) 1),
      ∀ y ∈ Set.univ.pi (fun _ : ι ↦ Set.Icc (0 : ℝ) 1),
        |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hM_le : 1 / 2 ≤ (Measure.pi μ).real {x | f x ≤ M})
    (hM_ge : 1 / 2 ≤ (Measure.pi μ).real {x | M ≤ f x})
    (s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi μ).real {x | s ≤ |f x - M|} ≤ 4 * Real.exp (-(s ^ 2) / (4 * L ^ 2)) := by
  classical
  have : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦
    ⟨by simp [hμ i, ENNReal.inv_two_add_inv_two]⟩
  let toPoint : (ι → Bool) → (ι → ℝ) := fun b i ↦ if b i then 1 else 0
  have hto_inj : Function.Injective toPoint := fun a b h ↦ funext fun i ↦ by
    have := congrFun h i
    cases ha : a i <;> cases hb : b i <;> simp [toPoint, ha, hb] at this ⊢
  have hto_cube : ∀ b : ι → Bool, toPoint b ∈ Set.univ.pi fun _ : ι ↦ Set.Icc (0 : ℝ) 1 := by
    intro b i _; dsimp only [toPoint]; split_ifs <;> norm_num
  -- Exact counting bridge: `(Measure.pi μ).real S = |{b | toPoint b ∈ S}| / 2^|ι|`!
  have hbridge : ∀ S : Set (ι → ℝ),
      (Measure.pi μ).real S =
        ((Finset.univ.filter fun b : ι → Bool ↦ toPoint b ∈ S).card : ℝ) /
          (2 : ℝ) ^ Fintype.card ι := by
    intro S
    have hsupp : ∀ᵐ x : ι → ℝ ∂Measure.pi μ, x ∈ Set.range toPoint := by
      have hall : ∀ᵐ x : ι → ℝ ∂Measure.pi μ, ∀ i : ι, x i = 0 ∨ x i = 1 := by
        rw [ae_all_iff]; intro i
        have h1 : ∀ᵐ y : ℝ ∂μ i, y = 0 ∨ y = 1 := by rw [ae_iff]; simp [hμ i]
        exact (MeasureTheory.measurePreserving_eval μ i).quasiMeasurePreserving.ae h1
      filter_upwards [hall] with x hx
      refine ⟨fun i ↦ decide (x i = 1), funext fun i ↦ ?_⟩
      rcases hx i with h | h <;> simp [toPoint, h]
    have hsing : ∀ b : ι → Bool, Measure.pi μ {toPoint b} = (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
      intro b
      have hset : ({toPoint b} : Set (ι → ℝ)) = Set.univ.pi fun i ↦ {toPoint b i} := by
        ext x; simp [funext_iff]
      rw [hset, Measure.pi_pi]
      have h1 : ∀ i : ι, μ i {toPoint b i} = (1 / 2 : ℝ≥0∞) := fun i ↦ by
        cases hb : b i <;> simp [hμ i, toPoint, hb]
      simp [h1]
    have hmeas_S : Measure.pi μ S =
        ((Finset.univ.filter fun b : ι → Bool ↦ toPoint b ∈ S).card : ℝ≥0∞) *
          (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
      have h1 : Measure.pi μ S = Measure.pi μ (S ∩ Set.range toPoint) := by
        have hcompl : Measure.pi μ (Set.range toPoint)ᶜ = 0 := ae_iff.mp hsupp
        have hsub : S \ (S ∩ Set.range toPoint) ⊆ (Set.range toPoint)ᶜ := fun x hx hmem ↦
          hx.2 ⟨hx.1, hmem⟩
        have hzero : Measure.pi μ (S \ (S ∩ Set.range toPoint)) = 0 :=
          measure_mono_null hsub hcompl
        have hunion : S = (S ∩ Set.range toPoint) ∪ (S \ (S ∩ Set.range toPoint)) := by
          ext x; by_cases hx : x ∈ Set.range toPoint <;> simp
        conv_lhs => rw [hunion]
        exact le_antisymm
          ((measure_union_le _ _).trans (by rw [hzero, add_zero]))
          (measure_mono Set.subset_union_left)
      have h2 : S ∩ Set.range toPoint =
          ⋃ b ∈ Finset.univ.filter (fun b : ι → Bool ↦ toPoint b ∈ S), {toPoint b} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Finset.mem_filter,
          Finset.mem_univ, true_and, Set.mem_singleton_iff]
        exact ⟨fun ⟨hxS, b, hb⟩ ↦ ⟨b, hb ▸ hxS, hb.symm⟩, fun ⟨b, hbS, hbx⟩ ↦ ⟨hbx ▸ hbS, b,
          hbx.symm⟩⟩
      rw [h1, h2, measure_biUnion_finset
        (fun a _ b _ hab ↦ Set.disjoint_singleton.mpr (fun h ↦ hab (hto_inj h)))
        (fun b _ ↦ measurableSet_singleton _)]
      simp [hsing]
    rw [measureReal_def, hmeas_S, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
    simp [div_eq_mul_inv, inv_pow]
  -- Core Lipschitz + Convexity bound: if `∀ y ∈ A, f (toPoint y) ≤ t`, then
  -- `∀ x, f (toPoint x) ≤ t + L * √(talagrandDistSq A x)`.
  have hlip_dist : ∀ (A : Finset (ι → Bool)) (t : ℝ), A.Nonempty →
      (∀ y ∈ A, f (toPoint y) ≤ t) →
      ∀ x : ι → Bool, f (toPoint x) - t ≤ L * Real.sqrt (talagrandDistSq A x) := by
    intro A t hA hAt x
    have hfor_w : ∀ w : (ι → Bool) → ℝ, (∀ y, 0 ≤ w y) → (∑ y ∈ A, w y = 1) →
        ((f (toPoint x) - t) / L) ^ 2 ≤
          ∑ i : ι, (∑ y ∈ A, if x i ≠ y i then w y else 0) ^ 2 ∨ f (toPoint x) ≤ t := by
      intro w hw0 hw1
      by_cases hft : f (toPoint x) ≤ t
      · exact Or.inr hft
      · left; push Not at hft
        let z : ι → ℝ := ∑ y ∈ A, w y • toPoint y
        have hz_cube : z ∈ Set.univ.pi fun _ : ι ↦ Set.Icc (0 : ℝ) 1 := by
          intro i _
          have hzi : z i = ∑ y ∈ A, w y * toPoint y i := by simp [z, Finset.sum_apply]
          rw [hzi]
          refine ⟨Finset.sum_nonneg fun y _ ↦ mul_nonneg (hw0 y) (hto_cube y i trivial).1, ?_⟩
          calc ∑ y ∈ A, w y * toPoint y i
              ≤ ∑ y ∈ A, w y * 1 := Finset.sum_le_sum fun y _ ↦
                  mul_le_mul_of_nonneg_left (hto_cube y i trivial).2 (hw0 y)
            _ = 1 := by simp [hw1]
        have hfz : f z ≤ t := by
          have h1 := hf_conv.map_sum_le (t := A) (w := w) (p := toPoint)
            (fun y _ ↦ hw0 y) hw1 (fun y _ ↦ hto_cube y)
          calc f z ≤ ∑ y ∈ A, w y * f (toPoint y) := h1
            _ ≤ ∑ y ∈ A, w y * t := Finset.sum_le_sum fun y hy ↦
                mul_le_mul_of_nonneg_left (hAt y hy) (hw0 y)
            _ = t := by rw [← Finset.sum_mul, hw1, one_mul]
        have hlip := hf_lip (toPoint x) (hto_cube x) z hz_cube
        have hdiff : f (toPoint x) - t ≤ L * Real.sqrt (∑ i : ι, (toPoint x i - z i) ^ 2) := by
          have := (abs_le.mp hlip).2; linarith
        have hcoord : ∀ i : ι, (toPoint x i - z i) ^ 2 ≤
            (∑ y ∈ A, if x i ≠ y i then w y else 0) ^ 2 := by
          intro i
          have hzi : toPoint x i - z i = ∑ y ∈ A, w y * (toPoint x i - toPoint y i) := by
            have h1 : z i = ∑ y ∈ A, w y * toPoint y i := by simp [z, Finset.sum_apply]
            have h2 : toPoint x i = ∑ y ∈ A, w y * toPoint x i := by
              rw [← Finset.sum_mul, hw1, one_mul]
            conv_lhs => rw [h1, h2, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun y _ ↦ by ring
          have habs : |toPoint x i - z i| ≤ ∑ y ∈ A, if x i ≠ y i then w y else 0 := by
            rw [hzi]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
            rw [abs_mul, abs_of_nonneg (hw0 y)]
            cases hxi : x i <;> cases hyi : y i <;> simp [toPoint, hxi, hyi]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        have hsq_le : ((f (toPoint x) - t) / L) ^ 2 ≤
            ∑ i : ι, (toPoint x i - z i) ^ 2 := by
          have h1 : (f (toPoint x) - t) / L ≤ Real.sqrt (∑ i : ι, (toPoint x i - z i) ^ 2) :=
            (div_le_iff₀ hL).mpr (by linarith)
          have h2 := pow_le_pow_left₀ (div_nonneg (by linarith) hL.le) h1 2
          rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
        exact hsq_le.trans (Finset.sum_le_sum fun i _ ↦ hcoord i)
    by_cases hft : f (toPoint x) ≤ t
    · exact (by linarith : f (toPoint x) - t ≤ 0).trans (by positivity)
    · have hcs : ((f (toPoint x) - t) / L) ^ 2 ≤ talagrandDistSq A x := by
        refine le_csInf ?_ ?_
        · exact ⟨_, Pi.single hA.choose 1,
            fun y ↦ by by_cases h : y = hA.choose <;> simp [Pi.single, h],
            by simp [hA.choose_spec], rfl⟩
        · rintro r ⟨w, hw0, hw1, rfl⟩
          exact (hfor_w w hw0 hw1).resolve_right hft
      have hsq := Real.sqrt_le_sqrt hcs
      rw [Real.sqrt_sq (div_nonneg (by linarith) hL.le)] at hsq
      exact (div_le_iff₀ hL).mp hsq |>.trans_eq (mul_comm _ _)
  -- Upper tail: `P[f x ≥ M + s] ≤ 2 exp(-s² / (4 L²))`.
  have hupper : (Measure.pi μ).real {x | M + s ≤ f x} ≤ 2 * Real.exp (-(s ^ 2) / (4 * L ^ 2)) := by
    let A := Finset.univ.filter fun y : ι → Bool ↦ f (toPoint y) ≤ M
    have hA_prob : (1 / 2 : ℝ) ≤ (A.card : ℝ) / (2 : ℝ) ^ Fintype.card ι := by
      have := hbridge {x | f x ≤ M}; rwa [this] at hM_le
    have hA_ne : A.Nonempty := by
      rw [← Finset.card_pos]; by_contra h0; simp only [not_lt, Nat.le_zero] at h0
      rw [h0] at hA_prob; norm_num at hA_prob
    rw [hbridge]
    let B := Finset.univ.filter fun x : ι → Bool ↦ M + s ≤ f (toPoint x)
    have hmark : (B.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤
        ∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4) := by
      have hpt : ∀ x ∈ B, Real.exp (s ^ 2 / (4 * L ^ 2)) ≤ Real.exp (talagrandDistSq A x / 4) := by
        intro x hx
        have hfx : M + s ≤ f (toPoint x) := (Finset.mem_filter.mp hx).2
        have hd := hlip_dist A M hA_ne (fun y hy ↦ (Finset.mem_filter.mp hy).2) x
        have hs_le : s / L ≤ Real.sqrt (talagrandDistSq A x) :=
          (div_le_iff₀ hL).mpr (by linarith)
        have hsq := pow_le_pow_left₀ (div_nonneg hs hL.le) hs_le 2
        rw [Real.sq_sqrt (talagrandDistSq_nonneg _ _), div_pow] at hsq
        exact Real.exp_le_exp.mpr (by
          rw [show s ^ 2 / (4 * L ^ 2) = (s ^ 2 / L ^ 2) / 4 by ring]
          exact div_le_div_of_nonneg_right hsq (by norm_num))
      calc (B.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2))
          = ∑ _x ∈ B, Real.exp (s ^ 2 / (4 * L ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ B, Real.exp (talagrandDistSq A x / 4) := Finset.sum_le_sum hpt
        _ ≤ ∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ ↦ (Real.exp_pos _).le)
    have hexp := talagrand_hypercube_exp_moment A hA_ne
    have h1 : ((B.card : ℝ) / (2 : ℝ) ^ Fintype.card ι) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤
        ((A.card : ℝ) / (2 : ℝ) ^ Fintype.card ι)⁻¹ := by
      rw [inv_div]
      calc ((B.card : ℝ) / (2 : ℝ) ^ Fintype.card ι) * Real.exp (s ^ 2 / (4 * L ^ 2))
          = ((B.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2))) / (2 : ℝ) ^ Fintype.card ι := by ring
        _ ≤ (∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4)) / (2 : ℝ) ^ Fintype.card ι :=
            div_le_div_of_nonneg_right hmark (by positivity)
        _ ≤ (2 : ℝ) ^ Fintype.card ι / (A.card : ℝ) := hexp
    have h2 : ((A.card : ℝ) / (2 : ℝ) ^ Fintype.card ι)⁻¹ ≤ 2 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hA_prob
      simpa [one_div] using this
    have h3 : ((B.card : ℝ) / (2 : ℝ) ^ Fintype.card ι) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤ 2 :=
      h1.trans h2
    have h4 := (le_div_iff₀ (Real.exp_pos _)).mpr h3
    simpa [div_eq_mul_inv, Real.exp_neg, neg_div] using h4
  -- Lower tail: `P[f x ≤ M - s] ≤ 2 exp(-s² / (4 L²))`.
  have hlower : (Measure.pi μ).real {x | f x ≤ M - s} ≤ 2 * Real.exp (-(s ^ 2) / (4 * L ^ 2)) := by
    let A := Finset.univ.filter fun y : ι → Bool ↦ f (toPoint y) ≤ M - s
    rw [hbridge]
    by_cases hA_ne : A.Nonempty
    · let B := Finset.univ.filter fun x : ι → Bool ↦ M ≤ f (toPoint x)
      have hB_prob : (1 / 2 : ℝ) ≤ (B.card : ℝ) / (2 : ℝ) ^ Fintype.card ι := by
        have := hbridge {x | M ≤ f x}; rwa [this] at hM_ge
      have hmark : (B.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤
          ∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4) := by
        have hpt : ∀ x ∈ B, Real.exp (s ^ 2 / (4 * L ^ 2)) ≤
          Real.exp (talagrandDistSq A x / 4) := by
          intro x hx
          have hfx : M ≤ f (toPoint x) := (Finset.mem_filter.mp hx).2
          have hd := hlip_dist A (M - s) hA_ne (fun y hy ↦ (Finset.mem_filter.mp hy).2) x
          have hs_le : s / L ≤ Real.sqrt (talagrandDistSq A x) :=
            (div_le_iff₀ hL).mpr (by linarith)
          have hsq := pow_le_pow_left₀ (div_nonneg hs hL.le) hs_le 2
          rw [Real.sq_sqrt (talagrandDistSq_nonneg _ _), div_pow] at hsq
          exact Real.exp_le_exp.mpr (by
            rw [show s ^ 2 / (4 * L ^ 2) = (s ^ 2 / L ^ 2) / 4 by ring]
            exact div_le_div_of_nonneg_right hsq (by norm_num))
        calc (B.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2))
            = ∑ _x ∈ B, Real.exp (s ^ 2 / (4 * L ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ x ∈ B, Real.exp (talagrandDistSq A x / 4) := Finset.sum_le_sum hpt
          _ ≤ ∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun _ _ _ ↦ (Real.exp_pos _).le)
      have hexp := talagrand_hypercube_exp_moment A hA_ne
      have h1 : (1 / 2 : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤
          (2 : ℝ) ^ Fintype.card ι / (A.card : ℝ) := by
        calc (1 / 2 : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2))
            ≤ ((B.card : ℝ) / (2 : ℝ) ^ Fintype.card ι) * Real.exp (s ^ 2 / (4 * L ^ 2)) :=
              mul_le_mul_of_nonneg_right hB_prob (Real.exp_pos _).le
          _ = ((B.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2))) / (2 : ℝ) ^ Fintype.card ι := by ring
          _ ≤ (∑ x : ι → Bool, Real.exp (talagrandDistSq A x / 4)) / (2 : ℝ) ^ Fintype.card ι :=
              div_le_div_of_nonneg_right hmark (by positivity)
          _ ≤ (2 : ℝ) ^ Fintype.card ι / (A.card : ℝ) := hexp
      have hAp : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA_ne
      have h2 : ((A.card : ℝ) / (2 : ℝ) ^ Fintype.card ι) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤ 2 := by
        have h1' := (le_div_iff₀ hAp).mp h1
        have h3 := (div_le_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι by positivity)).mpr
          (by linarith : (A.card : ℝ) * Real.exp (s ^ 2 / (4 * L ^ 2)) ≤
            2 * (2 : ℝ) ^ Fintype.card ι)
        simpa [div_mul_eq_mul_div] using h3
      have h3 := (le_div_iff₀ (Real.exp_pos _)).mpr h2
      simpa [div_eq_mul_inv, Real.exp_neg, neg_div] using h3
    · have h0 : A.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hA_ne)
      have hAeq : (Finset.univ.filter fun b : ι → Bool ↦ toPoint b ∈ {x | f x ≤ M - s}) = A := rfl
      rw [hAeq, h0]; simp only [CharP.cast_eq_zero, zero_div]; positivity
  -- Combine upper and lower tails!
  have hsub : {x : ι → ℝ | s ≤ |f x - M|} ⊆ {x | M + s ≤ f x} ∪ {x | f x ≤ M - s} := by
    intro x hx
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hx ⊢
    rcases le_abs.mp hx with h | h
    · left; linarith
    · right; linarith
  calc (Measure.pi μ).real {x | s ≤ |f x - M|}
      ≤ (Measure.pi μ).real ({x | M + s ≤ f x} ∪ {x | f x ≤ M - s}) := measureReal_mono hsub
    _ ≤ (Measure.pi μ).real {x | M + s ≤ f x} + (Measure.pi μ).real {x | f x ≤ M - s} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(s ^ 2) / (4 * L ^ 2)) + 2 * Real.exp (-(s ^ 2) / (4 * L ^ 2)) :=
        add_le_add hupper hlower
    _ = 4 * Real.exp (-(s ^ 2) / (4 * L ^ 2)) := by ring

end TalagrandHypercube

end CslibFrontier.Foundations.Probability
