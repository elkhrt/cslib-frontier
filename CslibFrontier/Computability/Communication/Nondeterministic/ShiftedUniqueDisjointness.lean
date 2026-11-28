module

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank
public import CslibFrontier.Computability.Communication.Nondeterministic.RectangleCorruption

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonnegative Rank Lower Bounds for Shifted Unique Disjointness Matrices

A nonnegative matrix `M` indexed by `Finset (Fin n)` is a `ρ`-extension of unique disjointness if
`M a b = ρ` whenever `Disjoint a b` and `M a b = ρ - 1` whenever `(a ∩ b).card = 1`. Applying the
entropy-based rectangle corruption inequality to each rank-1 term of a nonnegative factorization
yields explicit finite-`n` and asymptotic lower bounds on `rank₊(M)`:
1. For fixed constant `ρ ≥ 1`, `rank₊(M) = 2 ^ Ω(n)`.
2. For `ρ ≤ C * n ^ β` with `β < 1 / 2`, `rank₊(M) = 2 ^ Ω(n ^ (1 - 2 * β))`.

## Main definitions

* `CslibFrontier.Communication.Nondeterministic.IsUDISJExtension`: `ρ`-extensions of unique
  disjointness.

## Main results

* `nonnegRank_udisjExtension_explicit`: explicit finite-`n` lower bound for all `n ≥ 3`.
* `nonnegRank_udisjExtension_const`: `2 ^ Ω(n)` lower bound for constant `ρ ≥ 1`.
* `nonnegRank_udisjExtension_poly`: `2 ^ Ω(n ^ (1 - 2 * β))` lower bound for `ρ ≤ C * n ^ β`
  with `β < 1 / 2`.
-/

public section

namespace CslibFrontier.Communication.Nondeterministic

open Matrix Finset

/-- A nonnegative matrix `M` indexed by `Finset (Fin n)` is a **`ρ`-extension of UDISJ**
 if `M a b ≥ 0` everywhere, `M a b = ρ` whenever
`Disjoint a b`, and `M a b = ρ - 1` whenever `(a ∩ b).card = 1`. -/
def IsUDISJExtension (n : ℕ) (ρ : ℝ) (M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ) : Prop :=
  (∀ a b, 0 ≤ M a b) ∧
    (∀ a b, Disjoint a b → M a b = ρ) ∧
    (∀ a b, (a ∩ b).card = 1 → M a b = ρ - 1)

/-- Characterization of `IsUDISJExtension` without unfolding across modules. -/
theorem isUDISJExtension_iff {n : ℕ} {ρ : ℝ}
    {M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ} :
    IsUDISJExtension n ρ M ↔
      (∀ a b, 0 ≤ M a b) ∧
        (∀ a b, Disjoint a b → M a b = ρ) ∧
        (∀ a b, (a ∩ b).card = 1 → M a b = ρ - 1) :=
  Iff.rfl

/-- For `n ≥ 1`, any `ρ`-extension of UDISJ necessarily has `1 ≤ ρ`. -/
theorem IsUDISJExtension.one_le_rho {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ}
    {M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ} (hM : IsUDISJExtension n ρ M) :
    1 ≤ ρ := by
  let a : Finset (Fin n) := {⟨0, hn⟩}
  have hinter : (a ∩ a).card = 1 := by simp [a]
  have h1 := hM.1 a a
  rw [hM.2.2 a a hinter] at h1
  linarith

/-- Extracting a principal submatrix along `Fin k ↪ Fin n` preserves `IsUDISJExtension`. -/
theorem IsUDISJExtension.submatrix_castLE {k n : ℕ} (hkn : k ≤ n) {ρ : ℝ}
    {M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ} (hM : IsUDISJExtension n ρ M) :
    IsUDISJExtension k ρ
      (M.submatrix (Finset.map (Fin.castLEEmb hkn)) (Finset.map (Fin.castLEEmb hkn))) := by
  refine ⟨fun a b => hM.1 _ _, fun a b hdisj => hM.2.1 _ _ (disjoint_map _ |>.2 hdisj),
    fun a b hinter => hM.2.2 _ _ ?_⟩
  rw [← map_inter, card_map]
  exact hinter

/-- **Explicit finite-`n` nonnegative rank lower bound for `ρ`-extensions of UDISJ**
: for any `n ≥ 3`, `ℓ = (n + 1) / 4`, `0 < ε < 1`,
and any nonnegative factorization of `M` of size `r`,
`((1 / ρ) - ε) * 2 ^ ((ε ^ 2 / (16 * log 2)) * ℓ) ≤ r * (2 * (2 * ℓ + 1))`. -/
theorem nonnegRank_udisjExtension_explicit {n : ℕ} (hn : 3 ≤ n) {ρ : ℝ}
    {M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ} (hM : IsUDISJExtension n ρ M)
    {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : M.HasNonnegFactorization (Fin r)) :
    (1 / ρ - ε) * (2 : ℝ) ^ ((ε ^ 2 / (16 * Real.log 2)) * ((n + 1) / 4 : ℕ)) ≤
      (r : ℝ) * (2 * (2 * (((n + 1) / 4 : ℕ) : ℝ) + 1)) := by
  set ℓ : ℕ := (n + 1) / 4
  have hℓ : 1 ≤ ℓ := by omega
  set n' : ℕ := 4 * ℓ - 1
  have hn'le : n' ≤ n := by omega
  have hn'4 : n' + 1 = 4 * ℓ := by omega
  have hρ1 : 1 ≤ ρ := hM.one_le_rho (by omega)
  have hρpos : 0 < ρ := by linarith
  let emb := Finset.map (Fin.castLEEmb hn'le)
  let M' : Matrix (Finset (Fin n')) (Finset (Fin n')) ℝ := M.submatrix emb emb
  have hM' : IsUDISJExtension n' ρ M' := hM.submatrix_castLE hn'le
  have hfac' : M'.HasNonnegFactorization (Fin r) := by
    obtain ⟨T, U, hT, hU, hTU⟩ := hr
    exact ⟨T.submatrix emb id, U.submatrix id emb, fun _ _ => hT _ _, fun _ _ => hU _ _,
      by dsimp only [M']; rw [← hTU, submatrix_mul _ _ _ _ _ Function.bijective_id]⟩
  obtain ⟨T, U, hT, hU, hTU⟩ := hfac'
  -- For each rank-1 term `k : Fin r`, apply `razborov_corruption_explicit`.
  have hterm : ∀ k : Fin r,
      (1 - ε) * avgOn (disjointPairs n' ℓ) (fun p => T p.1 k * U k p.2) -
          avgOn (uniqueInterPairs n' ℓ) (fun p => T p.1 k * U k p.2) ≤
        ρ * (2 * (2 * (ℓ : ℝ) + 1)) * (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := by
    intro k
    have hraz := razborov_corruption_explicit hℓ hn'4 (f := fun a => T a k) (g := fun b => U k b)
      (fun a => hT a k) (fun b => hU k b) hε
    have hmax_le : maxOn (disjointPairs n' ℓ ∪ uniqueInterPairs n' ℓ)
        (fun p => T p.1 k * U k p.2) ≤ ρ := by
      refine maxOn_le_of_forall_le hρpos.le fun p hp => ?_
      have hleM : T p.1 k * U k p.2 ≤ M' p.1 p.2 := by
        rw [← hTU, Matrix.mul_apply]
        exact single_le_sum (fun j _ => mul_nonneg (hT p.1 j) (hU j p.2)) (mem_univ k)
      rcases mem_union.1 hp with hA | hB
      · rw [hM'.2.1 p.1 p.2 (mem_disjointPairs_iff.1 hA).2.2] at hleM; exact hleM
      · rw [hM'.2.2 p.1 p.2 (mem_uniqueInterPairs_iff.1 hB).2.2] at hleM; linarith
    calc _ ≤ maxOn (disjointPairs n' ℓ ∪ uniqueInterPairs n' ℓ)
              (fun p => T p.1 k * U k p.2) * (2 * (2 * (ℓ : ℝ) + 1)) *
              (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := hraz
      _ ≤ ρ * (2 * (2 * (ℓ : ℝ) + 1)) * (2 : ℝ) ^ (-(ε ^ 2 / (16 * Real.log 2)) * ℓ) := by
          gcongr
  -- Sum over `k : Fin r` and evaluate the LHS on `A` and `B`.
  have hsum := sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin r))) => hterm k
  rw [sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hsumA : ∑ k : Fin r, avgOn (disjointPairs n' ℓ) (fun p => T p.1 k * U k p.2) = ρ := by
    rw [sum_avgOn]
    have hcongr := avgOn_congr (S := disjointPairs n' ℓ)
      (X := fun p => ∑ k : Fin r, T p.1 k * U k p.2) (Y := fun _ => ρ) fun p hp => by
        rw [← Matrix.mul_apply, hTU, hM'.2.1 p.1 p.2 (mem_disjointPairs_iff.1 hp).2.2]
    rw [hcongr, avgOn_const (disjointPairs_nonempty (by omega))]
  have hsumB : ∑ k : Fin r, avgOn (uniqueInterPairs n' ℓ) (fun p => T p.1 k * U k p.2) =
      ρ - 1 := by
    rw [sum_avgOn]
    have hcongr := avgOn_congr (S := uniqueInterPairs n' ℓ)
      (X := fun p => ∑ k : Fin r, T p.1 k * U k p.2) (Y := fun _ => ρ - 1) fun p hp => by
        rw [← Matrix.mul_apply, hTU, hM'.2.2 p.1 p.2 (mem_uniqueInterPairs_iff.1 hp).2.2]
    rw [hcongr, avgOn_const (uniqueInterPairs_nonempty hℓ (by omega))]
  rw [hsumA, hsumB] at hsum
  -- Rearrange `(1 - ε) * ρ - (ρ - 1) ≤ r * ρ * (2 * (2ℓ + 1)) * 2^(-E)`.
  set E : ℝ := (ε ^ 2 / (16 * Real.log 2)) * (ℓ : ℝ)
  have hmul := mul_le_mul_of_nonneg_right hsum
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) E).le
  have hcancel : (2 : ℝ) ^ (-E) * (2 : ℝ) ^ E = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hstep1 : (1 - ε * ρ) * (2 : ℝ) ^ E ≤ (r : ℝ) * ρ * (2 * (2 * (ℓ : ℝ) + 1)) := by
    calc (1 - ε * ρ) * (2 : ℝ) ^ E
        = ((1 - ε) * ρ - (ρ - 1)) * (2 : ℝ) ^ E := by ring
      _ ≤ ((r : ℝ) * (ρ * (2 * (2 * (ℓ : ℝ) + 1)) * (2 : ℝ) ^ (-E))) * (2 : ℝ) ^ E := by
          simpa only [E, neg_mul] using hmul
      _ = (r : ℝ) * ρ * (2 * (2 * (ℓ : ℝ) + 1)) * ((2 : ℝ) ^ (-E) * (2 : ℝ) ^ E) := by ring
      _ = (r : ℝ) * ρ * (2 * (2 * (ℓ : ℝ) + 1)) := by rw [hcancel, mul_one]
  have hdiv := div_le_div_of_nonneg_right hstep1 hρpos.le
  have hlhs : (1 - ε * ρ) * (2 : ℝ) ^ E / ρ = (1 / ρ - ε) * (2 : ℝ) ^ E := by
    field_simp
  have hrhs : (r : ℝ) * ρ * (2 * (2 * (ℓ : ℝ) + 1)) / ρ =
      (r : ℝ) * (2 * (2 * (ℓ : ℝ) + 1)) := by
    field_simp
  rwa [hlhs, hrhs] at hdiv

/-- Elementary polynomial-vs-stretched-exponential inequality: for `A > 0`, `c > 0`, `γ > 0`,
there exists `N₀` such that `A * n ^ 2 ≤ 2 ^ (c * n ^ γ)` for all `n ≥ N₀`. -/
private theorem exists_poly_le_two_rpow {A c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → A * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ (c * (n : ℝ) ^ γ) := by
  set m : ℕ := Nat.ceil (3 / γ)
  have hm_ge : (3 : ℝ) ≤ (m : ℝ) * γ := by
    have h1 := Nat.le_ceil (3 / γ)
    have h2 := mul_le_mul_of_nonneg_right h1 hγ.le
    rwa [div_mul_cancel₀ _ hγ.ne'] at h2
  set α : ℝ := c * Real.log 2
  have hα_pos : 0 < α := mul_pos hc (Real.log_pos (by norm_num))
  set B : ℝ := α ^ m / (m.factorial : ℝ)
  have hB_pos : 0 < B := div_pos (pow_pos hα_pos m) (by exact_mod_cast Nat.factorial_pos m)
  refine ⟨max 1 (Nat.ceil (A / B)), fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_left 1 _).trans hn
  have hAB : A / B ≤ n :=
    (Nat.le_ceil (A / B)).trans (by exact_mod_cast (le_max_right 1 _).trans hn)
  have hx_nn : 0 ≤ α * (n : ℝ) ^ γ := by positivity
  have hexp_term : (α * (n : ℝ) ^ γ) ^ m / (m.factorial : ℝ) ≤ Real.exp (α * (n : ℝ) ^ γ) := by
    have hsum := Real.sum_le_exp_of_nonneg hx_nn (m + 1)
    exact (single_le_sum (f := fun i => (α * (n : ℝ) ^ γ) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (mem_range.2 (Nat.lt_succ_self m))).trans hsum
  have h2pow : (2 : ℝ) ^ (c * (n : ℝ) ^ γ) = Real.exp (α * (n : ℝ) ^ γ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; simp only [α]; ring
  have hpow_ge : (n : ℝ) ^ 3 ≤ ((n : ℝ) ^ γ) ^ m := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ γ) m, ← Real.rpow_mul (by positivity), mul_comm]
    calc (n : ℝ) ^ 3 = (n : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast (n : ℝ) 3).symm
      _ ≤ (n : ℝ) ^ ((m : ℝ) * γ) := Real.rpow_le_rpow_of_exponent_le hn1 hm_ge
  rw [h2pow]
  calc A * (n : ℝ) ^ 2 ≤ (B * (n : ℝ)) * (n : ℝ) ^ 2 := by
        have hAn : A ≤ B * n := by rwa [div_le_iff₀ hB_pos, mul_comm] at hAB
        gcongr
    _ = B * (n : ℝ) ^ 3 := by ring
    _ ≤ B * ((n : ℝ) ^ γ) ^ m := mul_le_mul_of_nonneg_left hpow_ge hB_pos.le
    _ = (α * (n : ℝ) ^ γ) ^ m / (m.factorial : ℝ) := by simp only [B, mul_pow]; ring
    _ ≤ Real.exp (α * (n : ℝ) ^ γ) := hexp_term

/-- **Polynomial-shift nonnegative-rank lower bound**:
if `ρ ≤ C * n ^ β` for constants `C > 0` and `β < 1 / 2`, then every `ρ`-extension `M` of UDISJ
on `[n]` has nonnegative rank `2 ^ Ω(n ^ (1 - 2 * β))`. -/
theorem nonnegRank_udisjExtension_poly {C β : ℝ} (hC : 0 < C) (hβ : β < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (n : ℕ), N₀ ≤ n →
      ∀ (ρ : ℝ), ρ ≤ C * (n : ℝ) ^ β →
      ∀ (M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ), IsUDISJExtension n ρ M →
      ∀ (r : ℕ), M.HasNonnegFactorization (Fin r) →
        (2 : ℝ) ^ (c * (n : ℝ) ^ (1 - 2 * β)) ≤ r := by
  by_cases hβ0 : β < 0
  · -- When `β < 0`, `C * n ^ β < 1` for large `n`, contradicting `1 ≤ ρ` from `IsUDISJExtension`.
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → C * (n : ℝ) ^ β < 1 := by
      have hneg : 0 < -β := by linarith
      set K : ℕ := max 1 (Nat.ceil ((C + 1) ^ (1 / (-β))))
      refine ⟨K, fun n hn => ?_⟩
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_left 1 _).trans hn
      have hn_pos : (0 : ℝ) < n := by linarith
      have hceil : (C + 1) ^ (1 / (-β)) ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 _).trans hn)
      have hpow : C + 1 ≤ (n : ℝ) ^ (-β) := by
        calc C + 1 = ((C + 1) ^ (1 / (-β))) ^ (-β) := by
              rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hneg.ne', Real.rpow_one]
          _ ≤ (n : ℝ) ^ (-β) := Real.rpow_le_rpow (by positivity) hceil hneg.le
      rw [show β = -(-β) by ring, Real.rpow_neg hn_pos.le, ← div_eq_mul_inv,
        div_lt_one (by positivity)]
      linarith
    refine ⟨1, zero_lt_one, max 1 N₁, fun n hn ρ hρ M hM _ _ => ?_⟩
    have h1 := hM.one_le_rho ((le_max_left 1 N₁).trans hn)
    have h2 := hN₁ n ((le_max_right 1 N₁).trans hn)
    linarith
  · push Not at hβ0
    set γ : ℝ := 1 - 2 * β
    have hγ : 0 < γ := by linarith
    set c : ℝ := 1 / (1024 * C ^ 2 * Real.log 2)
    have hc : 0 < c := by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    obtain ⟨N₁, hN₁⟩ := exists_poly_le_two_rpow (A := 4 * C) (c := c) (γ := γ) hc hγ
    refine ⟨c, hc, max 4 N₁, fun n hn ρ hρ M hM r hr => ?_⟩
    have hn4 : 4 ≤ n := (le_max_left 4 N₁).trans hn
    have hn3 : 3 ≤ n := by omega
    have hρ1 : 1 ≤ ρ := hM.one_le_rho (by omega)
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hCnβ_pos : 0 < C * (n : ℝ) ^ β := by positivity
    set ε : ℝ := 1 / (2 * C * (n : ℝ) ^ β)
    have hε : 0 < ε := by positivity
    have hbound := nonnegRank_udisjExtension_explicit hn3 hM hε hr
    set ℓ : ℕ := (n + 1) / 4
    have hℓ_lb : (n : ℝ) / 8 ≤ (ℓ : ℝ) := by
      have : n ≤ 8 * ℓ := by omega
      have hreal : (n : ℝ) ≤ 8 * (ℓ : ℝ) := by exact_mod_cast this
      linarith
    have hℓ_ub : 2 * (ℓ : ℝ) + 1 ≤ n := by
      have : 2 * ℓ + 1 ≤ n := by omega
      exact_mod_cast this
    have hcoeff : 1 / (2 * C * (n : ℝ) ^ β) ≤ 1 / ρ - ε := by
      have h1 : 1 / (C * (n : ℝ) ^ β) ≤ 1 / ρ :=
        one_div_le_one_div_of_le (by linarith) hρ
      have h2 : 1 / (C * (n : ℝ) ^ β) = 2 * (1 / (2 * C * (n : ℝ) ^ β)) := by field_simp
      simp only [ε]; linarith
    have hexp_ge : 2 * c * (n : ℝ) ^ γ ≤ (ε ^ 2 / (16 * Real.log 2)) * (ℓ : ℝ) := by
      have h1 : (ε ^ 2 / (16 * Real.log 2)) * (n / 8) ≤
          (ε ^ 2 / (16 * Real.log 2)) * (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_left hℓ_lb (by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
      have heq : (ε ^ 2 / (16 * Real.log 2)) * (n / 8) = 2 * c * (n : ℝ) ^ γ := by
        simp only [ε, c, γ]
        have hrpow : (n : ℝ) ^ (1 - 2 * β) = (n : ℝ) / ((n : ℝ) ^ β) ^ 2 := by
          rw [Real.rpow_sub hn_pos, Real.rpow_one, mul_comm 2 β, Real.rpow_mul hn_pos.le,
            show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hrpow]
        field_simp
        ring
      linarith
    have hpoly : 4 * C * (n : ℝ) ^ β * (2 * (ℓ : ℝ) + 1) ≤ (2 : ℝ) ^ (c * (n : ℝ) ^ γ) := by
      have hβle1 : (n : ℝ) ^ β ≤ (n : ℝ) := by
        calc (n : ℝ) ^ β ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
          _ = n := Real.rpow_one _
      calc 4 * C * (n : ℝ) ^ β * (2 * (ℓ : ℝ) + 1)
          ≤ 4 * C * (n : ℝ) * (n : ℝ) := by gcongr
        _ = 4 * C * (n : ℝ) ^ 2 := by ring
        _ ≤ (2 : ℝ) ^ (c * (n : ℝ) ^ γ) := hN₁ n ((le_max_right 4 N₁).trans hn)
    -- Combine: `2^(c * n^γ) * (4 * C * n^β * (2ℓ + 1)) ≤ 2^(2 * c * n^γ) ≤ ...`
    have hstep1 : (2 : ℝ) ^ (c * (n : ℝ) ^ γ) * (2 * (2 * (ℓ : ℝ) + 1)) ≤
        (1 / ρ - ε) * (2 : ℝ) ^ (2 * c * (n : ℝ) ^ γ) := by
      rw [show 2 * c * (n : ℝ) ^ γ = c * (n : ℝ) ^ γ + c * (n : ℝ) ^ γ by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have hmul : 2 * (2 * (ℓ : ℝ) + 1) ≤ (1 / ρ - ε) * (2 : ℝ) ^ (c * (n : ℝ) ^ γ) := by
        calc 2 * (2 * (ℓ : ℝ) + 1)
            = (1 / (2 * C * (n : ℝ) ^ β)) * (4 * C * (n : ℝ) ^ β * (2 * (ℓ : ℝ) + 1)) := by
              field_simp; ring
          _ ≤ (1 / ρ - ε) * (2 : ℝ) ^ (c * (n : ℝ) ^ γ) :=
              mul_le_mul hcoeff hpoly (by positivity) (by linarith [hcoeff, hε])
      calc (2 : ℝ) ^ (c * (n : ℝ) ^ γ) * (2 * (2 * (ℓ : ℝ) + 1))
          ≤ (2 : ℝ) ^ (c * (n : ℝ) ^ γ) * ((1 / ρ - ε) * (2 : ℝ) ^ (c * (n : ℝ) ^ γ)) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = (1 / ρ - ε) * ((2 : ℝ) ^ (c * (n : ℝ) ^ γ) * (2 : ℝ) ^ (c * (n : ℝ) ^ γ)) := by ring
    have hstep2 : (1 / ρ - ε) * (2 : ℝ) ^ (2 * c * (n : ℝ) ^ γ) ≤
        (r : ℝ) * (2 * (2 * (ℓ : ℝ) + 1)) := by
      calc _ ≤ (1 / ρ - ε) * (2 : ℝ) ^ ((ε ^ 2 / (16 * Real.log 2)) * (ℓ : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge) (by linarith [hcoeff, hε])
        _ ≤ (r : ℝ) * (2 * (2 * (ℓ : ℝ) + 1)) := hbound
    exact le_of_mul_le_mul_right (hstep1.trans hstep2) (by positivity)

/-- **Constant-shift nonnegative-rank lower bound**:
for any fixed constant `ρ ≥ 1`, every `ρ`-extension `M` of UDISJ on `[n]` has nonnegative rank
`2 ^ Ω(n)`. -/
theorem nonnegRank_udisjExtension_const {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (n : ℕ), N₀ ≤ n →
      ∀ (M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℝ), IsUDISJExtension n ρ M →
      ∀ (r : ℕ), M.HasNonnegFactorization (Fin r) →
        (2 : ℝ) ^ (c * (n : ℝ)) ≤ r := by
  obtain ⟨c, hc, N₀, hbound⟩ :=
    nonnegRank_udisjExtension_poly (C := ρ) (β := 0) (by linarith) (by norm_num)
  refine ⟨c, hc, N₀, fun n hn M hM r hr => ?_⟩
  have h := hbound n hn ρ (by simp) M hM r hr
  simpa only [mul_zero, sub_zero, Real.rpow_one] using h

end CslibFrontier.Communication.Nondeterministic
