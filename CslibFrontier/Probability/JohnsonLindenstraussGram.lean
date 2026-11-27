/-
Copyright (c) 2026 The Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Probability.PMF
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Basic
import CslibFrontier.Probability.JohnsonLindenstrauss
import CslibFrontier.Probability.PMF.UniformBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Approximate-Identity Gram Matrices and Simultaneous Rademacher Sign Alignment

Two textbook randomized-linear-algebra and high-dimensional probability tools for metric embeddings
and sketching lower bounds
:

1. **Johnson–Lindenstrauss approximate-identity Gram factorization**
   (`CslibFrontier.Probability.exists_matrix_gram_sub_one_abs_le`): for any `n ≥ 1` and
   `ε ∈ (0, 1]`, embedding the `n` standard basis vectors together with `0` via
   `Cslib.Probability.exists_linearMap_forall_norm_sq_mem_Icc` produces a tall matrix
   `U : Matrix (Fin n) (Fin k) ℝ` of width `k = ⌈96 / ε² * log (n + 1)⌉₊` whose Gram matrix
   approximates the identity entrywise within `ε`: `∀ i j, |(U * Uᵀ - 1) i j| ≤ ε`.
2. **Simultaneous Rademacher sign-alignment bound**
   (`CslibFrontier.Probability.toOuterMeasure_boolean_matrix_sign_aligned_ge`): for `s` uniform
   random sign vectors in `{±1}^m`, with probability at least `1 - 2^s * exp(- m / (12 * 2^s))`
   under `Cslib.Probability.PMF.uniformOfFintype`, every real coefficient vector `α : Fin s → ℝ`
   simultaneously aligns at least `m / (2 * 2^s)` coordinates in the positive binary direction.
-/

public section

open Finset Matrix
open scoped BigOperators

namespace CslibFrontier.Probability

/-- **Approximate-identity Gram factorization via Johnson–Lindenstrauss**:
for any `n : ℕ` and `ε ∈ (0, 1]`, with `k = ⌈96 / ε² * log (n + 1)⌉₊`, there exists a matrix
`U : Matrix (Fin n) (Fin k) ℝ` such that every entry of `U * Uᵀ - 1` has absolute value at most
`ε`. -/
theorem exists_matrix_gram_sub_one_abs_le (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let k : ℕ := Nat.ceil (96 / ε ^ 2 * Real.log ((n + 1 : ℕ) : ℝ))
    ∃ U : Matrix (Fin n) (Fin k) ℝ,
      ∀ i j : Fin n, |((U * Uᵀ - 1 : Matrix (Fin n) (Fin n) ℝ) i j)| ≤ ε := by
  intro k
  let ε' : ℝ := ε / 2
  have hε'0 : 0 < ε' := half_pos hε0
  have hε'1 : ε' ≤ 1 := by dsimp [ε']; linarith
  have hk_ge : 24 / ε' ^ 2 * Real.log ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    have h96 : 24 / ε' ^ 2 = 96 / ε ^ 2 := by
      dsimp [ε']
      field_simp [hε0.ne']
      ring
    rw [h96]
    exact Nat.le_ceil _
  let basisPt (i : Fin n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  let pts : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := fun j ↦
    if hj : j.val < n then basisPt ⟨j.val, hj⟩ else 0
  obtain ⟨f, hf⟩ := Cslib.Probability.exists_linearMap_forall_norm_sq_mem_Icc pts hε'0 hε'1 hk_ge
  let U : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun i r ↦ f (basisPt i) r
  refine ⟨U, fun i j ↦ ?_⟩
  have hgram : (U * Uᵀ) i j = ∑ r : Fin k, f (basisPt i) r * f (basisPt j) r := by
    simp [U, Matrix.mul_apply]
  have hnorm_unit : ∀ a : Fin n, ‖basisPt a‖ ^ 2 = 1 := fun a ↦ by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [basisPt, Pi.single_apply]
  have hdiag_f : ∀ a : Fin n, ‖f (basisPt a)‖ ^ 2 ∈ Set.Icc (1 - ε') (1 + ε') := by
    intro a
    let ja : Fin (n + 1) := ⟨a.val, a.isLt.trans (Nat.lt_succ_self n)⟩
    let jz : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    have hfa := hf ja jz
    have hja : pts ja = basisPt a := by simp [pts, ja, a.isLt]
    have hjz : pts jz = 0 := by simp [pts, jz]
    rw [hja, hjz, map_zero, sub_zero, sub_zero, hnorm_unit a, mul_one, mul_one] at hfa
    exact hfa
  by_cases hij : i = j
  · subst hij
    have hdiag_eq : (U * Uᵀ) i i = ‖f (basisPt i)‖ ^ 2 := by
      rw [hgram, EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun r _ ↦ by ring
    obtain ⟨hlo, hhi⟩ := hdiag_f i
    have hsub : ((U * Uᵀ - 1 : Matrix (Fin n) (Fin n) ℝ) i i) = ‖f (basisPt i)‖ ^ 2 - 1 := by
      rw [Matrix.sub_apply, hdiag_eq, Matrix.one_apply_eq i]
    rw [hsub, abs_le]
    exact ⟨by dsimp [ε'] at hlo; linarith, by dsimp [ε'] at hhi; linarith⟩
  · have hsub_zero : ((U * Uᵀ - 1 : Matrix (Fin n) (Fin n) ℝ) i j) = (U * Uᵀ) i j := by
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]
    rw [hsub_zero]
    have hdist_two : ‖basisPt i - basisPt j‖ ^ 2 = 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hterm : ∀ r : Fin n,
          ((basisPt i - basisPt j) r) ^ 2 =
            (if r = i then (1 : ℝ) else 0) + (if r = j then (1 : ℝ) else 0) := fun r ↦ by
        change ((Pi.single i (1 : ℝ) : Fin n → ℝ) r -
          (Pi.single j (1 : ℝ) : Fin n → ℝ) r) ^ 2 = _
        by_cases hri : r = i
        · subst hri; simp [hij]
        · by_cases hrj : r = j
          · subst hrj; simp [hri]
          · simp [hri, hrj]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      norm_num
    let ji : Fin (n + 1) := ⟨i.val, i.isLt.trans (Nat.lt_succ_self n)⟩
    let jj : Fin (n + 1) := ⟨j.val, j.isLt.trans (Nat.lt_succ_self n)⟩
    have hfij := hf ji jj
    have hji : pts ji = basisPt i := by simp [pts, ji, i.isLt]
    have hjj : pts jj = basisPt j := by simp [pts, jj, j.isLt]
    rw [hji, hjj, hdist_two] at hfij
    have hpolar : ‖f (basisPt i) - f (basisPt j)‖ ^ 2 =
        ‖f (basisPt i)‖ ^ 2 + ‖f (basisPt j)‖ ^ 2 - 2 * ((U * Uᵀ) i j) := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        EuclideanSpace.real_norm_sq_eq, hgram, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      change (f (basisPt i) r - f (basisPt j) r) ^ 2 = _
      ring
    obtain ⟨hi_lo, hi_hi⟩ := hdiag_f i
    obtain ⟨hj_lo, hj_hi⟩ := hdiag_f j
    obtain ⟨hd_lo, hd_hi⟩ := hfij
    rw [abs_le]
    exact ⟨by dsimp [ε'] at *; linarith, by dsimp [ε'] at *; linarith⟩

/-- **Simultaneous Rademacher sign-alignment bound**:
under `Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin s → Bool)`, with probability at least
`1 - 2^s * exp(- m / (12 * 2^s))`, for **every** weight vector `α : Fin s → ℝ`, at least
`m / (2 * 2^s)` rows `t : Fin m` satisfy `0 ≤ α r * Cslib.BitString.signVal (Ω t r)` (i.e.,
`α r * x_{r, t} = |α r|`) for all `r : Fin s`. -/
theorem toOuterMeasure_boolean_matrix_sign_aligned_ge (m s : ℕ) :
    1 - (2 : ℝ) ^ s * Real.exp (-((m : ℝ) / (12 * (2 : ℝ) ^ s))) ≤
      (((Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin s → Bool)).toOuterMeasure
        {Ω : Fin m → Fin s → Bool |
          ∀ α : Fin s → ℝ,
            (m : ℝ) / (2 * (2 : ℝ) ^ s) ≤
              (#{t : Fin m | ∀ r : Fin s,
                0 ≤ α r * Cslib.BitString.signVal (Ω t r)} : ℝ)})).toReal := by
  classical
  have hexp_half : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    have h1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
      linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(1 / 2 : ℝ))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
    linarith
  -- Bound each fixed pattern `σ : Fin s → Bool`:
  have hpat : ∀ σ : Fin s → Bool,
      (#{Ω : Fin m → Fin s → Bool |
          (#{t : Fin m | Ω t = σ} : ℝ) ≤ (m : ℝ) / (2 * (2 : ℝ) ^ s)} : ℝ) ≤
        (((2 : ℝ) ^ s) ^ m) * Real.exp (-((m : ℝ) / (12 * (2 : ℝ) ^ s))) := by
    intro σ
    have hrow :
        (∑ v : Fin s → Bool, Real.exp (if v = σ then -(1 / 2 : ℝ) else 0)) ≤
          (2 : ℝ) ^ s * Real.exp (-(1 / (3 * (2 : ℝ) ^ s))) := by
      rw [← Finset.add_sum_erase Finset.univ _ (mem_univ σ)]
      simp only [↓reduceIte]
      have herase : (∑ v ∈ Finset.univ.erase σ,
          Real.exp (if v = σ then -(1 / 2 : ℝ) else 0)) = (2 : ℝ) ^ s - 1 := by
        have hc : (#(Finset.univ.erase σ) : ℝ) = (2 : ℝ) ^ s - 1 := by
          have h1 : #(Finset.univ.erase σ) + 1 = 2 ^ s := by
            rw [Finset.card_erase_add_one (mem_univ σ), Finset.card_univ, Fintype.card_fun,
              Fintype.card_bool, Fintype.card_fin]
          have hR : (#(Finset.univ.erase σ) : ℝ) + 1 = ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at hR; linarith
        calc (∑ v ∈ Finset.univ.erase σ, Real.exp (if v = σ then -(1 / 2 : ℝ) else 0))
            = ∑ _ ∈ Finset.univ.erase σ, (1 : ℝ) :=
              Finset.sum_congr rfl fun v hv ↦ by
                simp only [Finset.ne_of_mem_erase hv, ↓reduceIte, Real.exp_zero]
          _ = (2 : ℝ) ^ s - 1 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
      rw [herase]
      have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      have h1 : Real.exp (-(1 / 2 : ℝ)) + ((2 : ℝ) ^ s - 1) ≤
          (2 : ℝ) ^ s * (1 - 1 / (3 * (2 : ℝ) ^ s)) := by
        have hid : (2 : ℝ) ^ s * (1 - 1 / (3 * (2 : ℝ) ^ s)) = (2 : ℝ) ^ s - 1 / 3 := by
          field_simp [h2s_pos.ne']
        rw [hid]; linarith
      exact h1.trans (mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (-(1 / (3 * (2 : ℝ) ^ s)))]) h2s_pos.le)
    have hmgf :
        (∑ Ω : Fin m → Fin s → Bool,
          Real.exp (-(1 / 2 : ℝ) * (#{t : Fin m | Ω t = σ} : ℝ))) ≤
          (((2 : ℝ) ^ s) ^ m) * Real.exp (-((m : ℝ) / (3 * (2 : ℝ) ^ s))) := by
      have hexp_eq : ∀ Ω : Fin m → Fin s → Bool,
          Real.exp (-(1 / 2 : ℝ) * (#{t : Fin m | Ω t = σ} : ℝ)) =
            ∏ t : Fin m, Real.exp (if Ω t = σ then -(1 / 2 : ℝ) else 0) := fun Ω ↦ by
        rw [← Real.exp_sum]
        congr 1
        have hc : (#{t : Fin m | Ω t = σ} : ℝ) = ∑ t : Fin m, (if Ω t = σ then (1 : ℝ) else 0) := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
        rw [hc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> ring
      simp_rw [hexp_eq]
      rw [← Fintype.prod_sum (f := fun _ v ↦ Real.exp (if v = σ then -(1 / 2 : ℝ) else 0))]
      calc (∏ _ : Fin m, ∑ v : Fin s → Bool, Real.exp (if v = σ then -(1 / 2 : ℝ) else 0))
          ≤ ∏ _ : Fin m, ((2 : ℝ) ^ s * Real.exp (-(1 / (3 * (2 : ℝ) ^ s)))) :=
            Finset.prod_le_prod₀ (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
              fun _ _ ↦ hrow
        _ = (((2 : ℝ) ^ s) ^ m) * Real.exp (-((m : ℝ) / (3 * (2 : ℝ) ^ s))) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin, ← Real.exp_nat_mul]
            congr 2; ring
    let Bad : Finset (Fin m → Fin s → Bool) := {Ω : Fin m → Fin s →
      Bool | (#{t : Fin m | Ω t = σ} : ℝ) ≤ (m : ℝ) / (2 * (2 : ℝ) ^ s)}
    have hmarkov : (#Bad : ℝ) * Real.exp (-((m : ℝ) / (4 * (2 : ℝ) ^ s))) ≤
        ∑ Ω : Fin m → Fin s → Bool, Real.exp (-(1 / 2 : ℝ) * (#{t : Fin m | Ω t = σ} : ℝ)) := by
      calc (#Bad : ℝ) * Real.exp (-((m : ℝ) / (4 * (2 : ℝ) ^ s)))
          = ∑ _ ∈ Bad, Real.exp (-((m : ℝ) / (4 * (2 : ℝ) ^ s))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ Ω ∈ Bad, Real.exp (-(1 / 2 : ℝ) * (#{t : Fin m | Ω t = σ} : ℝ)) :=
            Finset.sum_le_sum fun Ω hΩ ↦ Real.exp_le_exp.2 (by
              have hle := (Finset.mem_filter.1 hΩ).2
              linarith [show (1 / 2 : ℝ) * ((m : ℝ) / (2 * (2 : ℝ) ^ s)) =
                (m : ℝ) / (4 * (2 : ℝ) ^ s) by ring])
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ ↦ (Real.exp_pos _).le)
    have hmul := mul_le_mul_of_nonneg_right (hmarkov.trans hmgf)
      (Real.exp_pos ((m : ℝ) / (4 * (2 : ℝ) ^ s))).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
      mul_assoc, ← Real.exp_add] at hmul
    refine hmul.trans_eq ?_
    congr 2; ring
  let BadOf (σ : Fin s → Bool) : Finset (Fin m → Fin s → Bool) :=
    {Ω : Fin m → Fin s → Bool | (#{t : Fin m | Ω t = σ} : ℝ) ≤ (m : ℝ) / (2 * (2 : ℝ) ^ s)}
  let BadAll : Finset (Fin m → Fin s → Bool) := Finset.univ.biUnion BadOf
  have hBadAll_le : (#BadAll : ℝ) ≤
      (2 : ℝ) ^ s * (((2 : ℝ) ^ s) ^ m) * Real.exp (-((m : ℝ) / (12 * (2 : ℝ) ^ s))) := by
    have hnat := Finset.card_biUnion_le (s := (@Finset.univ (Fin s → Bool) _)) (t := BadOf)
    have hR : (#BadAll : ℝ) ≤ ∑ σ : Fin s → Bool, (#(BadOf σ) : ℝ) := by exact_mod_cast hnat
    refine hR.trans ?_
    calc (∑ σ : Fin s → Bool, (#(BadOf σ) : ℝ))
        ≤ ∑ _ : Fin s → Bool,
            (((2 : ℝ) ^ s) ^ m) * Real.exp (-((m : ℝ) / (12 * (2 : ℝ) ^ s))) :=
          Finset.sum_le_sum fun σ _ ↦ hpat σ
      _ = (2 : ℝ) ^ s * (((2 : ℝ) ^ s) ^ m) * Real.exp (-((m : ℝ) / (12 * (2 : ℝ) ^ s))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  let P_good (Ω : Fin m → Fin s → Bool) : Prop :=
    ∀ α : Fin s → ℝ,
      (m : ℝ) / (2 * (2 : ℝ) ^ s) ≤
        (#{t : Fin m | ∀ r : Fin s, 0 ≤ α r * Cslib.BitString.signVal (Ω t r)} : ℝ)
  let GoodSet : Finset (Fin m → Fin s → Bool) := Finset.univ.filter P_good
  have hcompl_sub : BadAllᶜ ⊆ GoodSet := by
    intro Ω hΩ
    have hnot : Ω ∉ BadAll := Finset.mem_compl.1 hΩ
    refine Finset.mem_filter.2 ⟨mem_univ Ω, fun α ↦ ?_⟩
    let σ_α : Fin s → Bool := fun r ↦ decide (α r < 0)
    have hgt : (m : ℝ) / (2 * (2 : ℝ) ^ s) < (#{t : Fin m | Ω t = σ_α} : ℝ) := by
      by_contra hle; push Not at hle
      exact hnot (Finset.mem_biUnion.2 ⟨σ_α, mem_univ σ_α, Finset.mem_filter.2 ⟨mem_univ Ω, hle⟩⟩)
    refine hgt.le.trans (Nat.cast_le.2 (Finset.card_le_card fun t ht ↦ ?_))
    have heq_t : Ω t = σ_α := (Finset.mem_filter.1 ht).2
    refine Finset.mem_filter.2 ⟨mem_univ t, fun r ↦ ?_⟩
    rw [congrFun heq_t r]
    dsimp [σ_α]
    rcases lt_or_ge (α r) 0 with hneg | hnn
    · have hs : Cslib.BitString.signVal true = -1 := rfl
      simp only [hneg, decide_true, hs, mul_neg, mul_one]
      linarith
    · simp [not_lt.2 hnn, Cslib.BitString.signVal, hnn]
  set Total := ((2 : ℝ) ^ s) ^ m
  have hTotal_pos : 0 < Total := by positivity
  have hbridge :=
    Cslib.Probability.PMF.card_filter_univ_eq_card_mul_toOuterMeasure_uniformOfFintype
      (α := Fin m → Fin s → Bool) P_good
  have hcard_univ : (Fintype.card (Fin m → Fin s → Bool) : ℝ) = Total := by
    simp [Total]
  rw [hcard_univ, mul_comm Total] at hbridge
  have hsum_univ : (#(BadAllᶜ) : ℝ) + (#BadAll : ℝ) = Total := by
    have hnat : #(BadAllᶜ) + #BadAll = (2 ^ s) ^ m := by
      rw [Finset.card_compl, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, Fintype.card_fin, Nat.sub_add_cancel (by
          simpa [Fintype.card_fun] using Finset.card_le_univ BadAll)]
    have hR : (#(BadAllᶜ) : ℝ) + (#BadAll : ℝ) = (((2 ^ s) ^ m : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Total] using hR
  have hGood_ge : (#(BadAllᶜ) : ℝ) ≤ (#GoodSet : ℝ) := by
    exact_mod_cast Finset.card_le_card hcompl_sub
  have hGood_eq : (#GoodSet : ℝ) =
      (((Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin s → Bool)).toOuterMeasure
        {Ω | P_good Ω})).toReal * Total := hbridge
  have hmul_le :
      (1 - (2 : ℝ) ^ s * Real.exp (-((m : ℝ) / (12 * (2 : ℝ) ^ s)))) * Total ≤
        (((Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin s → Bool)).toOuterMeasure
          {Ω | P_good Ω})).toReal * Total := by
    linarith [hBadAll_le, hsum_univ, hGood_ge, hGood_eq]
  exact le_of_mul_le_mul_right hmul_le hTotal_pos

end CslibFrontier.Probability

end
