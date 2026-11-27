module

public import CslibFrontier.Foundations.Data.Code.LocalProperty.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The MRRSW Random Linear Code Threshold Theorem

This module proves the Mosheiff–Resch–Ron-Zewi–Silas–Wootters (MRRSW) Random Linear Code (RLC)
Threshold Theorem for monotone-increasing, `b`-local, row-symmetric properties of linear codes over
a finite field `F`: first-moment upper bound, Chebyshev second-moment lower bound, quantitative
threshold characterization `|R_RLC(𝒫) - mrrswRate(𝒫)| ≤ O_{q,b}(log_q(n + 1) / n)`, and sharp
threshold behavior below and above `R_RLC(𝒫)`.
All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main results

* `CslibFrontier.Foundations.Data.Code.rlc_upper_bound`: first-moment upper bound.
* `CslibFrontier.Foundations.Data.Code.rlc_lower_bound`: second-moment lower bound.
* `CslibFrontier.Foundations.Data.Code.rlcThreshold_sub_mrrswRate_abs_le`: quantitative MRRSW
  threshold characterization.
* `CslibFrontier.Foundations.Data.Code.rlc_sharp_below` and
  `CslibFrontier.Foundations.Data.Code.rlc_sharp_above`: sharp threshold below and above `R_RLC`.

## Tags

random linear codes, threshold theorem, local properties, coding theory
-/

public section

namespace CslibFrontier.Foundations.Data.Code

open scoped Matrix

section ThresholdTheorem

variable {F : Type*} [Field F] [Fintype F]

/-- **MRRSW Upper Bound (First Moment)**: for any monotone-increasing, `b`-local, row-symmetric
property `P` with `¬ P ⊥` and any `k`:
`rlcProb F n k P ≤ (n + 1) ^ (q ^ b) * q ^ (-n * (mrrswRate - k/n))`. -/
theorem rlc_upper_bound {n b k : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    (hbot : ¬ P ⊥) :
    rlcProb F n k P ≤
      ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
        (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) := by
  classical
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := lt_trans zero_lt_one hq
  by_cases hsign : mrrswRate F hn b P ≤ (k : ℝ) / (n : ℝ)
  · have hexp : 0 ≤ -((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ))) := by
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hpow : (1 : ℝ) ≤ (Fintype.card F : ℝ) ^
        (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) :=
      Real.one_le_rpow hq.le hexp
    have hfac : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (Fintype.card F ^ b) :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact (rlcProb_le_one F n k P).trans (by nlinarith)
  have hdiff_pos : 0 ≤ mrrswRate F hn b P - (k : ℝ) / (n : ℝ) := by linarith
  have hcov :
      (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ P (rowSpan G)) ⊆
        (minimalTypesFinset hn b P).biUnion (fun p ↦
          Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            ∃ A ∈ typeClassFinset n hn p.2, MatrixContainedIn A (rowSpan G)) := by
    intro G hG
    have hPG : P (rowSpan G) := (Finset.mem_filter.mp hG).2
    obtain ⟨a, hab, A, hAmin, hAG⟩ := exists_isMinimalMatrix_of_sat hmono hloc hPG
    rw [Finset.mem_biUnion]
    refine ⟨⟨⟨a, Nat.lt_succ_of_le hab⟩, empDist hn A⟩, ?_, ?_⟩
    · rw [mem_minimalTypesFinset_iff]
      exact ⟨isFeasibleType_iff.mpr ⟨A, rfl⟩, isMinimalType_iff.mpr ⟨A, hAmin, rfl⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨A, mem_typeClassFinset.mpr rfl, hAG⟩
  have hper_type : ∀ p ∈ minimalTypesFinset hn b P,
      (((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          ∃ A ∈ typeClassFinset n hn p.2, MatrixContainedIn A (rowSpan G)).card : ℝ) /
        (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) ≤
        (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) := by
    intro ⟨a, τ⟩ hp
    have hp_mem := hp
    rw [mem_minimalTypesFinset_iff] at hp
    dsimp only at hp
    obtain ⟨A₀, hA₀_min, hA₀_eq⟩ := isMinimalType_iff.mp hp.2
    have hfullτ : IsFullRankDist τ :=
      hA₀_eq ▸ (isFullRankDist_empDist_iff hn A₀).mpr (isMinimalMatrix_iff.mp hA₀_min).1
    have himp_bound : ∀ (a' : ℕ) (τ' : PMF (Fin a' → F)),
        IsImpliedDist τ τ' → 1 ≤ a' →
        (((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            ∃ A ∈ typeClassFinset n hn τ, MatrixContainedIn A (rowSpan G)).card : ℝ) /
          (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) ≤
          (Fintype.card F : ℝ) ^
            ((n : ℝ) * (pmfEntropyBase (Fintype.card F) τ' -
              (a' : ℝ) * (1 - (k : ℝ) / (n : ℝ)))) := by
      intro a' τ' himp _ha'_pos
      have hsub :
          (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              ∃ A ∈ typeClassFinset n hn τ, MatrixContainedIn A (rowSpan G)) ⊆
            (typeClassFinset n hn τ').biUnion (fun A' ↦
              Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                MatrixContainedIn A' (rowSpan G)) := by
        intro G hG
        obtain ⟨A, hA, hAG⟩ := (Finset.mem_filter.mp hG).2
        obtain ⟨A', hA', hA'G⟩ := exists_mem_typeClass_of_isImpliedDist hn himp hA hAG
        exact Finset.mem_biUnion.mpr ⟨A', hA', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA'G⟩⟩
      have hA'_prob : ∀ A' ∈ typeClassFinset n hn τ',
          (((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              MatrixContainedIn A' (rowSpan G)).card : ℝ) /
            (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) ≤
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((a' : ℝ) * (1 - (k : ℝ) / (n : ℝ))))) := by
        intro A'₀ hA'
        let A' : Matrix (Fin n) (Fin a') F := A'₀
        have hfullA' : HasFullColRank A' := by
          have hfullτ' : IsFullRankDist τ' :=
            isFullRankDist_of_isImpliedDist hn (isFeasibleType_iff.mpr ⟨A₀, hA₀_eq⟩) hfullτ himp
          exact (isFullRankDist_empDist_iff hn A').mp ((mem_typeClassFinset.mp hA').symm ▸ hfullτ')
        have hU_cov :
            (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                MatrixContainedIn A' (rowSpan G)) ⊆
              (Finset.univ.filter fun U : Matrix (Fin a') (Fin k) F ↦ HasFullRowRank U).biUnion
                (fun U ↦ Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U * G = A'ᵀ) := by
          intro G hG
          have hcol : MatrixContainedIn A' (rowSpan G) := (Finset.mem_filter.mp hG).2
          have hexU : ∀ j : Fin a', ∃ u : Fin k → F, Matrix.vecMul u G = fun i ↦ A' i j := by
            intro j
            have hj : (fun i : Fin n ↦ A' i j) ∈ rowSpan G :=
              (matrixContainedIn_iff_colSpan_le A' (rowSpan G)).mp hcol
                (by rw [colSpan_eq_span_range]; exact Submodule.subset_span ⟨j, rfl⟩)
            exact (mem_rowSpan_iff_exists_vecMul G _).mp hj
          choose U₀ hU using hexU
          let U : Matrix (Fin a') (Fin k) F := U₀
          have hUG : U * G = A'ᵀ := by
            ext j i
            have hij := congrFun (hU j) i
            simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct] using
              hij
          have hU_rank : HasFullRowRank U := by
            rw [hasFullRowRank_iff_linearIndependent, Fintype.linearIndependent_iff]
            intro c hc
            have h0 : Matrix.vecMul c (U * G) = 0 := by
              rw [← Matrix.vecMul_vecMul]
              have hU0 : Matrix.vecMul c U = 0 := by
                ext r
                have hr := congrFun hc r
                simpa [Matrix.vecMul, dotProduct, mul_comm] using hr
              rw [hU0, Matrix.zero_vecMul]
            rw [hUG] at h0
            have hA'0 : A'.mulVec c = 0 := by
              ext i
              have hi := congrFun h0 i
              simpa [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm] using hi
            have hc0 : c = 0 :=
              (hasFullColRank_iff_mulVec_injective A').mp hfullA'
                (hA'0.trans (Matrix.mulVec_zero A').symm)
            intro j; rw [hc0]; rfl
          exact Finset.mem_biUnion.mpr
            ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_rank⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUG⟩⟩
        have h1 :
            (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                MatrixContainedIn A' (rowSpan G)).card ≤
              numFullRowRank F a' k * Fintype.card F ^ ((k - a') * n) := by
          have h1' := (Finset.card_le_card hU_cov).trans Finset.card_biUnion_le
          have h2' :
              ∑ U ∈ Finset.univ.filter (fun U : Matrix (Fin a') (Fin k) F ↦ HasFullRowRank U),
                  (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U * G = A'ᵀ).card =
                numFullRowRank F a' k * Fintype.card F ^ ((k - a') * n) := by
            rw [Finset.sum_congr rfl fun U hU ↦
              card_matrix_mul_eq_of_fullRowRank (Finset.mem_filter.mp hU).2 A'ᵀ,
              Finset.sum_const, smul_eq_mul, numFullRowRank_eq_card]
          omega
        by_cases hak : a' ≤ k
        · have hnum_le : numFullRowRank F a' k ≤ Fintype.card F ^ (a' * k) := by
            rw [numFullRowRank_eq_card]
            calc
              _ ≤ Fintype.card (Matrix (Fin a') (Fin k) F) := Finset.card_filter_le _ _
              _ = Fintype.card F ^ (a' * k) := by
                change Fintype.card (Fin a' → Fin k → F) = _
                rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
                  ← pow_mul, mul_comm]
          have hcard_le :
              ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                  MatrixContainedIn A' (rowSpan G)).card : ℝ) ≤
                (Fintype.card F : ℝ) ^ (a' * k) * (Fintype.card F : ℝ) ^ ((k - a') * n) := by
            exact_mod_cast h1.trans (Nat.mul_le_mul_right _ hnum_le)
          have htot : (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ) =
              (Fintype.card F : ℝ) ^ (k * n) := by
            have hcard : Fintype.card (Matrix (Fin k) (Fin n) F) = Fintype.card F ^ (k * n) := by
              change Fintype.card (Fin k → Fin n → F) = _
              rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
                ← pow_mul, mul_comm]
            exact_mod_cast hcard
          rw [htot, div_le_iff₀ (pow_pos hq_pos _)]
          refine hcard_le.trans (le_of_eq ?_)
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
            ← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos]
          congr 1
          have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hak]
          field_simp [hn0]
          ring
        · have hzero : numFullRowRank F a' k = 0 := by
            rw [numFullRowRank_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro U _ hU
            have := LinearIndependent.fintype_card_le_finrank
              ((hasFullRowRank_iff_linearIndependent U).mp hU)
            simp only [Module.finrank_pi, Fintype.card_fin] at this
            omega
          rw [hzero, zero_mul] at h1
          rw [Nat.eq_zero_of_le_zero h1, Nat.cast_zero, zero_div]
          exact Real.rpow_nonneg hq_pos.le _
      have hcard_union :
          (((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              ∃ A ∈ typeClassFinset n hn τ, MatrixContainedIn A (rowSpan G)).card : ℝ) /
            (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) ≤
            ∑ A' ∈ typeClassFinset n hn τ',
              (((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                  MatrixContainedIn A' (rowSpan G)).card : ℝ) /
                (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) := by
        rw [← Finset.sum_div]
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      calc
        _ ≤ ∑ _A' ∈ typeClassFinset n hn τ',
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((a' : ℝ) * (1 - (k : ℝ) / (n : ℝ))))) :=
          hcard_union.trans (Finset.sum_le_sum hA'_prob)
        _ = ((typeClassFinset n hn τ').card : ℝ) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((a' : ℝ) * (1 - (k : ℝ) / (n : ℝ))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card F : ℝ) ^ ((n : ℝ) * pmfEntropyBase (Fintype.card F) τ') *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((a' : ℝ) * (1 - (k : ℝ) / (n : ℝ))))) :=
          mul_le_mul_of_nonneg_right (card_typeClassFinset_le hn hq τ')
            (Real.rpow_nonneg hq_pos.le _)
        _ = (Fintype.card F : ℝ) ^
              ((n : ℝ) * (pmfEntropyBase (Fintype.card F) τ' -
                (a' : ℝ) * (1 - (k : ℝ) / (n : ℝ)))) := by
          rw [← Real.rpow_add hq_pos]; congr 1; ring
    obtain ⟨a', ha'_pos, _, τ', himp', _, _, hmrrsw_le⟩ :=
      exists_implied_of_mem_minimalTypes hn hbot hp_mem
    have hH_le : pmfEntropyBase (Fintype.card F) τ' ≤ (a' : ℝ) * (1 - mrrswRate F hn b P) := by
      have ha'R : (0 : ℝ) < (a' : ℝ) := Nat.cast_pos.mpr ha'_pos
      have h2 : pmfEntropyBase (Fintype.card F) τ' / (a' : ℝ) ≤ 1 - mrrswRate F hn b P := by
        linarith
      rwa [div_le_iff₀ ha'R, mul_comm] at h2
    refine (himp_bound a' τ' himp' ha'_pos).trans ?_
    refine Real.rpow_le_rpow_of_exponent_le hq.le ?_
    have ha'_ge1 : (1 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha'_pos
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hinner : pmfEntropyBase (Fintype.card F) τ' - (a' : ℝ) * (1 - (k : ℝ) / (n : ℝ)) ≤
        -(mrrswRate F hn b P - (k : ℝ) / (n : ℝ)) := by nlinarith
    have := mul_le_mul_of_nonneg_left hinner hn_nn
    linarith
  have hsum :
      rlcProb F n k P ≤
        ∑ p ∈ minimalTypesFinset hn b P,
          (((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              ∃ A ∈ typeClassFinset n hn p.2, MatrixContainedIn A (rowSpan G)).card : ℝ) /
            (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) := by
    rw [rlcProb_eq_card_div, ← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  calc
    rlcProb F n k P
        ≤ ∑ _p ∈ minimalTypesFinset hn b P,
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) :=
      hsum.trans (Finset.sum_le_sum hper_type)
    _ = ((minimalTypesFinset hn b P).card : ℝ) *
          (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
          (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq_pos.le _)
      exact_mod_cast card_minimalTypesFinset_le hn b P

private lemma rlc_pair_intersection_bound {n b k a d : ℕ} (hn : 0 < n)
    (ha_le : a ≤ b) (hd1 : 1 ≤ d) (hda : d ≤ a) (hak : a + 1 ≤ k)
    {τ : PMF (Fin a → F)} {r : ℝ}
    (hH_ge : ∀ (a' : ℕ), 1 ≤ a' → ∀ (τ' : PMF (Fin a' → F)),
      IsImpliedDist τ τ' → (a' : ℝ) * (1 - r) ≤ pmfEntropyBase (Fintype.card F) τ')
    {U₁ U₂ : Matrix (Fin a) (Fin k) F} (hU₁r : HasFullRowRank U₁) (hU₂r : HasFullRowRank U₂)
    (hdim : Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d) :
    let M_τ : Finset (Matrix (Fin n) (Fin a) F) := typeClassFinset n hn τ
    ({G : Matrix (Fin k) (Fin n) F | (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ}.ncard : ℝ) ≤
      (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
        (Fintype.card F : ℝ) ^ (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * r) /
        (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ) := by
  classical
  intro M_τ
  have hncard_G :
      {G : Matrix (Fin k) (Fin n) F | (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ}.ncard =
        (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card := by
    rw [← Set.ncard_coe_finset]
    congr 1; ext G; simp
  rw [hncard_G]
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := lt_trans zero_lt_one hq
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hN_eq : (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (k * n) := by
    have hcard : Fintype.card (Matrix (Fin k) (Fin n) F) = Fintype.card F ^ (k * n) := by
      change Fintype.card (Fin k → Fin n → F) = _
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, mul_comm]
    exact_mod_cast hcard
  let W := rowSpan U₁ ⊓ rowSpan U₂
  let bW := Module.finBasis F W
  let B : Matrix (Fin d) (Fin k) F := fun row ↦ (bW (row.cast hdim.symm) : Fin k → F)
  have hB_li : HasFullRowRank B := by
    rw [hasFullRowRank_iff_linearIndependent]
    exact (W.subtype.linearIndependent_iff_of_injOn (Submodule.injective_subtype W).injOn).mpr
      (bW.linearIndependent.comp (Fin.cast hdim.symm) (Fin.cast_injective hdim.symm))
  have hexC1 : ∀ row : Fin d, ∃ c : Fin a → F, Matrix.vecMul c U₁ = B row := fun row ↦
    (mem_rowSpan_iff_exists_vecMul U₁ _).mp (bW (row.cast hdim.symm)).2.1
  have hexC2 : ∀ row : Fin d, ∃ c : Fin a → F, Matrix.vecMul c U₂ = B row := fun row ↦
    (mem_rowSpan_iff_exists_vecMul U₂ _).mp (bW (row.cast hdim.symm)).2.2
  choose C₁ hC₁ using hexC1
  choose C₂ hC₂ using hexC2
  let D₁ : Matrix (Fin a) (Fin d) F := C₁ᵀ
  let D₂ : Matrix (Fin a) (Fin d) F := C₂ᵀ
  have hD₁U₁ : D₁ᵀ * U₁ = B := by
    ext row j; change (∑ x, C₁ row x * U₁ x j) = B row j
    simpa only [Matrix.vecMul, dotProduct] using congrFun (hC₁ row) j
  have hD₂U₂ : D₂ᵀ * U₂ = B := by
    ext row j; change (∑ x, C₂ row x * U₂ x j) = B row j
    simpa only [Matrix.vecMul, dotProduct] using congrFun (hC₂ row) j
  have hD_rank : ∀ {U : Matrix (Fin a) (Fin k) F} {D : Matrix (Fin a) (Fin d) F},
      Dᵀ * U = B → HasFullColRank D := fun {U} {D} hDU ↦ by
    rw [hasFullColRank_iff_mulVec_injective]
    intro u v huv
    apply (hasFullRowRank_iff_vecMul_injective B).mp hB_li
    change Matrix.vecMul u B = Matrix.vecMul v B
    rw [← hDU, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    have hm : ∀ w : Fin d → F, Matrix.vecMul w Dᵀ = D.mulVec w := fun w ↦ by
      ext t; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
    rw [hm u, hm v, huv]
  have hD₁_rank : HasFullColRank D₁ := hD_rank hD₁U₁
  have hD₂_rank : HasFullColRank D₂ := hD_rank hD₂U₂
  have hcov_d :
      (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
        (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ) ⊆
      (M_τ.sigma fun A₁ ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).biUnion fun p ↦
        Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U₁ * G = p.1ᵀ ∧
          U₂ * G = p.2ᵀ := by
    intro G hG
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hG).2
    have heq_AD : (U₂ * G)ᵀ * D₂ = (U₁ * G)ᵀ * D₁ := by
      have htrans_eq : ((U₂ * G)ᵀ * D₂)ᵀ = ((U₁ * G)ᵀ * D₁)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
          hD₂U₂, hD₁U₁]
      exact Matrix.transpose_injective htrans_eq
    exact Finset.mem_biUnion.mpr ⟨⟨(U₁ * G)ᵀ, (U₂ * G)ᵀ⟩,
      Finset.mem_sigma.mpr ⟨h1, Finset.mem_filter.mpr ⟨h2, heq_AD⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  have hsum_d :
      ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
        (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) ≤
      ∑ p ∈ M_τ.sigma (fun A₁ ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁),
        ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcov_d).trans Finset.card_biUnion_le
  have h2a_d_le : 2 * a - d ≤ k := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (rowSpan U₁) (rowSpan U₂)
    rw [(hasFullRowRank_iff_finrank U₁).mp hU₁r,
      (hasFullRowRank_iff_finrank U₂).mp hU₂r, hdim] at hsup
    have hle : Module.finrank F ↥(rowSpan U₁ ⊔ rowSpan U₂) ≤ k := by
      simpa [Module.finrank_pi, Fintype.card_fin] using
        Submodule.finrank_le (rowSpan U₁ ⊔ rowSpan U₂)
    omega
  have hG_fiber : ∀ p ∈ M_τ.sigma (fun A₁ ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁),
      ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
        U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ).card : ℝ) ≤
        (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) := by
    intro p _
    by_cases hex : ∃ G₀ : Matrix (Fin k) (Fin n) F, U₁ * G₀ = p.1ᵀ ∧ U₂ * G₀ = p.2ᵀ
    · rw [card_pair_matrix_mul_eq hU₁r hU₂r p.1ᵀ p.2ᵀ hex, hdim]; push_cast; rfl
    · have hempty : (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro G _ h; exact hex ⟨G, h⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity
  have hA₂_fiber : ∀ A₁ ∈ M_τ,
      ((M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card : ℝ) ≤
        (M_τ.card : ℝ) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
          (Fintype.card F : ℝ) ^ (-(n : ℝ) * ((d : ℝ) * (1 - r))) := by
    intro A₁ hA₁
    by_cases hne_f : (M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).Nonempty
    · let τ' : PMF (Fin d → F) := empDist hn (A₁ * D₁)
      let M_τ' : Finset (Matrix (Fin n) (Fin d) F) := typeClassFinset n hn τ'
      have himp' : IsImpliedDist τ τ' := by
        refine isImpliedDist_iff.mpr ⟨D₁, hD₁_rank, ?_⟩
        have hA₁_eq : empDist hn (fun i j ↦ A₁ i j) = τ := mem_typeClassFinset.mp hA₁
        rw [← hA₁_eq]
        exact empDist_map hn (fun i j ↦ A₁ i j) (fun x ↦ Matrix.vecMul x D₁)
      have hfib_eq : ∀ M ∈ M_τ',
          (M_τ.filter fun A₂ ↦ A₂ * D₂ = M).card =
            (M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card := by
        intro M hM
        have heq_M : empDist hn (A₁ * D₁) = empDist hn M := (mem_typeClassFinset.mp hM).symm
        obtain ⟨π, hπ⟩ := (empDist_eq_iff_exists_perm hn (A₁ * D₁) M).mp heq_M
        refine Finset.card_bij (fun A₂ _ ↦ A₂.submatrix ⇑π.symm id) ?_ ?_ ?_
        · intro A₂ hA₂
          have hA₂' := Finset.mem_filter.mp hA₂
          refine Finset.mem_filter.mpr
            ⟨mem_typeClassFinset.mpr ((empDist_comp_perm hn A₂ π⁻¹).trans
              (mem_typeClassFinset.mp hA₂'.1)), ?_⟩
          ext i j
          change (A₂ * D₂) (π⁻¹ i) j = (A₁ * D₁) i j
          have h1 : (A₁ * D₁) i j = M (π⁻¹ i) j :=
            (congrArg (fun row ↦ (A₁ * D₁) row j) (π.apply_symm_apply i).symm).trans
              (congrFun (congrFun hπ (π⁻¹ i)) j)
          exact (congrFun (congrFun hA₂'.2 (π⁻¹ i)) j).trans h1.symm
        · intro B₁ _ B₂ _ h; ext i j
          simpa [Matrix.submatrix] using congrFun (congrFun h (π i)) j
        · intro B hB
          have hB' := Finset.mem_filter.mp hB
          refine ⟨B.submatrix ⇑π id,
            Finset.mem_filter.mpr
              ⟨mem_typeClassFinset.mpr ((empDist_comp_perm hn B π).trans
                (mem_typeClassFinset.mp hB'.1)), ?_⟩,
            by ext i j; simp [Matrix.submatrix]⟩
          ext i j; change (B * D₂) (π i) j = M i j
          exact (congrFun (congrFun hB'.2 (π i)) j).trans (congrFun (congrFun hπ i) j)
      have hdisj : M_τ'.card * (M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card ≤ M_τ.card := by
        have hbi : (M_τ'.biUnion fun M ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = M) ⊆ M_τ := by
          intro A₂ hA₂; obtain ⟨_, _, h⟩ := Finset.mem_biUnion.mp hA₂
          exact (Finset.mem_filter.mp h).1
        have hcard_bi : (M_τ'.biUnion fun M ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = M).card =
            M_τ'.card * (M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card := by
          rw [Finset.card_biUnion]
          · rw [Finset.sum_congr rfl hfib_eq, Finset.sum_const, smul_eq_mul]
          · intro M₁ _ M₂ _ hne
            exact Finset.disjoint_left.mpr fun A₂ h₁ h₂ ↦
              hne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
        rw [← hcard_bi]; exact Finset.card_le_card hbi
      have hMτ'_ge : (((n + 1 : ℝ) ^ (Fintype.card F ^ b))⁻¹) *
            (Fintype.card F : ℝ) ^ ((n : ℝ) * ((d : ℝ) * (1 - r))) ≤ (M_τ'.card : ℝ) := by
        have hge := card_typeClassFinset_ge hn hq
          (isFeasibleType_iff.mpr ⟨A₁ * D₁, rfl⟩ : IsFeasibleType n hn τ')
        have hcard_le : (Fintype.card (Fin d → F)) ≤ Fintype.card F ^ b := by
          simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact Nat.pow_le_pow_right Fintype.card_pos (hda.trans ha_le)
        have hinv_le : (((n + 1 : ℝ) ^ (Fintype.card F ^ b))⁻¹) ≤
            (((n + 1 : ℝ) ^ Fintype.card (Fin d → F))⁻¹) :=
          inv_anti₀ (by positivity)
            (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) hcard_le)
        have hpow_le : (Fintype.card F : ℝ) ^ ((n : ℝ) * ((d : ℝ) * (1 - r))) ≤
            (Fintype.card F : ℝ) ^ ((n : ℝ) * pmfEntropyBase (Fintype.card F) τ') :=
          Real.rpow_le_rpow_of_exponent_le hq.le
            (mul_le_mul_of_nonneg_left (hH_ge d hd1 τ' himp') hn_pos.le)
        exact (mul_le_mul hinv_le hpow_le (Real.rpow_nonneg hq_pos.le _) (by positivity)).trans hge
      have hdisjR : (M_τ'.card : ℝ) *
          ((M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card : ℝ) ≤ (M_τ.card : ℝ) := by
        exact_mod_cast hdisj
      have hmul_le := (mul_le_mul_of_nonneg_right hMτ'_ge (Nat.cast_nonneg _)).trans hdisjR
      have hpos_lhs : 0 < (((n + 1 : ℝ) ^ (Fintype.card F ^ b))⁻¹) *
          (Fintype.card F : ℝ) ^ ((n : ℝ) * ((d : ℝ) * (1 - r))) := by positivity
      rw [mul_comm] at hmul_le
      refine ((le_div_iff₀ hpos_lhs).mpr hmul_le).trans (le_of_eq ?_)
      rw [div_mul_eq_div_div, div_inv_eq_mul, div_eq_mul_inv, ← Real.rpow_neg hq_pos.le, neg_mul]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne_f, Finset.card_empty, Nat.cast_zero]; positivity
  have htotal_p :
      (∑ p ∈ M_τ.sigma (fun A₁ ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁),
        ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ).card : ℝ)) ≤
      (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
        (Fintype.card F : ℝ) ^ (-(n : ℝ) * ((d : ℝ) * (1 - r))) *
        (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) := by
    calc
      _ ≤ ∑ _p ∈ M_τ.sigma (fun A₁ ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁),
            (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) := Finset.sum_le_sum hG_fiber
      _ = (((M_τ.sigma fun A₁ ↦ M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card : ℝ)) *
            (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (∑ A₁ ∈ M_τ, ((M_τ.filter fun A₂ ↦ A₂ * D₂ = A₁ * D₁).card : ℝ)) *
            (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) := by
          rw [Finset.card_sigma, Nat.cast_sum]
      _ ≤ (∑ _A₁ ∈ M_τ, ((M_τ.card : ℝ) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
              (Fintype.card F : ℝ) ^ (-(n : ℝ) * ((d : ℝ) * (1 - r))))) *
            (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum hA₂_fiber) (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  refine (hsum_d.trans htotal_p).trans ?_
  rw [hN_eq, le_div_iff₀ (pow_pos hq_pos _)]
  have hexp_eq :
      (Fintype.card F : ℝ) ^ (-(n : ℝ) * ((d : ℝ) * (1 - r))) *
          (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) * (Fintype.card F : ℝ) ^ (k * n) =
        (Fintype.card F : ℝ) ^ (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos]
    congr 1
    have hka : 2 * a ≤ 2 * k := by omega
    have hsub1 : ((k - (2 * a - d) : ℕ) : ℝ) = (k : ℝ) - (2 * (a : ℝ) - (d : ℝ)) := by
      rw [Nat.cast_sub h2a_d_le, Nat.cast_sub (by omega : d ≤ 2 * a)]; push_cast; ring
    have hsub2 : ((2 * k - 2 * a : ℕ) : ℝ) = 2 * (k : ℝ) - 2 * (a : ℝ) := by
      rw [Nat.cast_sub hka]; push_cast; ring
    rw [Nat.cast_mul, Nat.cast_mul, hsub1, hsub2]; ring
  calc
    _ = (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
          ((Fintype.card F : ℝ) ^ (-(n : ℝ) * ((d : ℝ) * (1 - r))) *
            (Fintype.card F : ℝ) ^ ((k - (2 * a - d)) * n) * (Fintype.card F : ℝ) ^ (k * n)) := by
      ring
    _ ≤ _ := by rw [hexp_eq]

/-- **MRRSW Lower Bound (Second Moment / Chebyshev)**: for any monotone-increasing, `b`-local,
row-symmetric property `P` with `¬ P ⊥`, `P ⊤`, `1 ≤ b`, and `b + 1 ≤ k`:
`1 - rlcProb F n k P ≤
  2 * b * q ^ (2 * b ^ 2) * (n + 1) ^ (q ^ b) * q ^ (-n * (k/n - mrrswRate))`. -/
theorem rlc_lower_bound {n b k : ℕ} (hn : 0 < n) (hb : 1 ≤ b) (hbk : b + 1 ≤ k)
    {P : Submodule F (Fin n → F) → Prop} (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    (hrow : IsRowSymmetric P) (hbot : ¬ P ⊥) (htop : P ⊤) :
    1 - rlcProb F n k P ≤
      (2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) *
        ((n + 1 : ℝ) ^ (Fintype.card F ^ b))) *
        (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) := by
  classical
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := lt_trans zero_lt_one hq
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hq_ge2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  by_cases hsign : (k : ℝ) / (n : ℝ) ≤ mrrswRate F hn b P
  · have hexp : 0 ≤ -((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P)) := by nlinarith
    have hpow : (1 : ℝ) ≤ (Fintype.card F : ℝ) ^
        (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) := Real.one_le_rpow hq.le hexp
    have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hqpow : (1 : ℝ) ≤ (Fintype.card F : ℝ) ^ (2 * b * b) := one_le_pow₀ hq.le
    have hfac : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (Fintype.card F ^ b) :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hC_ge1 : (1 : ℝ) ≤ 2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) *
        ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) := by
      have h1 : (1 : ℝ) ≤ 2 * (b : ℝ) := by linarith
      have h2 : (1 : ℝ) ≤ 2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) := by nlinarith
      nlinarith
    have hle1 : 1 - rlcProb F n k P ≤ 1 := by linarith [rlcProb_nonneg F n k P]
    exact hle1.trans (by nlinarith)
  have hdelta_pos : 0 < (k : ℝ) / (n : ℝ) - mrrswRate F hn b P := by linarith
  -- Choose a minimal type `p₀ = ⟨a₀, τ₀⟩` attaining `mrrswRate`.
  let rFun : (Σ a : Fin (b + 1), PMF (Fin a.val → F)) → ℝ := fun p ↦
    sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
      IsImpliedDist p.2 τ' ∧ s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}
  have hmin_ne : (minimalTypesFinset hn b P).Nonempty := by
    obtain ⟨a, hab, A, hAmin, _⟩ := exists_isMinimalMatrix_of_sat hmono hloc htop
    refine ⟨⟨⟨a, Nat.lt_succ_of_le hab⟩, empDist hn A⟩, ?_⟩
    rw [mem_minimalTypesFinset_iff]
    exact ⟨isFeasibleType_iff.mpr ⟨A, rfl⟩, isMinimalType_iff.mpr ⟨A, hAmin, rfl⟩⟩
  obtain ⟨⟨a₀, τ⟩, hp₀_mem, hp₀_min⟩ :=
    Finset.exists_min_image (minimalTypesFinset hn b P) rFun hmin_ne
  rw [mem_minimalTypesFinset_iff] at hp₀_mem
  dsimp only at hp₀_mem
  obtain ⟨A₀, hA₀_min, hA₀_eq⟩ := isMinimalType_iff.mp hp₀_mem.2
  let a : ℕ := a₀.val
  have ha_pos : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    have hcol : colSpan A₀ = ⊥ := by
      rw [colSpan_eq_span_range]
      have : Set.range (fun j : Fin a ↦ fun i : Fin n ↦ A₀ i j) = ∅ := by ext v; simp [ha0]
      rw [this, Submodule.span_empty]
    exact hbot (hcol ▸ (isMinimalMatrix_iff.mp hA₀_min).2.1)
  have ha_le : a ≤ b := Nat.le_of_lt_succ a₀.isLt
  have hak : a + 1 ≤ k := by omega
  have hr_eq : rFun ⟨a₀, τ⟩ = mrrswRate F hn b P := by
    rw [mrrswRate_eq_sInf]
    apply le_antisymm
    · refine le_csInf ?_ ?_
      · exact ⟨rFun ⟨a₀, τ⟩, a, ha_pos, ha_le, τ, isMinimalType_iff.mpr ⟨A₀, hA₀_min, hA₀_eq⟩, rfl⟩
      · rintro r ⟨a₁, _, ha₁_le, τ₁, hmin₁, rfl⟩
        have hmem₁ : ⟨⟨a₁, Nat.lt_succ_of_le ha₁_le⟩, τ₁⟩ ∈ minimalTypesFinset hn b P := by
          obtain ⟨A₁, hA₁, hA₁eq⟩ := isMinimalType_iff.mp hmin₁
          rw [mem_minimalTypesFinset_iff]
          exact ⟨isFeasibleType_iff.mpr ⟨A₁, hA₁eq⟩, isMinimalType_iff.mpr ⟨A₁, hA₁, hA₁eq⟩⟩
        exact hp₀_min _ hmem₁
    · refine csInf_le ?_ ⟨a, ha_pos, ha_le, τ, isMinimalType_iff.mpr ⟨A₀, hA₀_min, hA₀_eq⟩, rfl⟩
      refine ⟨0, ?_⟩
      rintro r ⟨a₁, ha₁, _, τ₁, hmin₁, rfl⟩
      obtain ⟨A₁, hA₁, hA₁eq⟩ := isMinimalType_iff.mp hmin₁
      have hfull₁ : IsFullRankDist τ₁ :=
        hA₁eq ▸ (isFullRankDist_empDist_iff hn A₁).mpr (isMinimalMatrix_iff.mp hA₁).1
      have hbdd₁ : BddAbove {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
          IsImpliedDist τ₁ τ' ∧
            s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)} := by
        refine ⟨1, ?_⟩
        rintro s ⟨_, _, τ', _, rfl⟩
        linarith [div_nonneg (pmfEntropyBase_nonneg hq τ') (Nat.cast_nonneg (distDim τ'))]
      have hself₁ : (1 - pmfEntropyBase (Fintype.card F) τ₁ / (distDim τ₁ : ℝ)) ∈
          {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
            IsImpliedDist τ₁ τ' ∧
              s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)} := by
        refine ⟨a₁, ha₁, τ₁, isImpliedDist_iff.mpr ⟨1, ?_, by
          simp only [Matrix.vecMul_one]; exact PMF.map_id τ₁⟩, rfl⟩
        rw [hasFullColRank_iff_mulVec_injective]; intro u v huv; simpa using huv
      have h0₁ : 0 ≤ 1 - pmfEntropyBase (Fintype.card F) τ₁ / (distDim τ₁ : ℝ) := by
        rw [(isFullRankDist_iff τ₁).mp hfull₁]
        have hle := pmfEntropyBase_le_logb_card (α := Fin a₁ → F) hq τ₁
        have hlog : Real.logb (Fintype.card F) (Fintype.card (Fin a₁ → F)) = (a₁ : ℝ) := by
          simp [Fintype.card_pi, Real.logb_pow, Real.logb_self_eq_one hq]
        rw [hlog] at hle
        rw [sub_nonneg, div_le_one (Nat.cast_pos.mpr ha₁)]
        exact hle
      exact h0₁.trans (le_csSup hbdd₁ hself₁)
  have hfullτ : IsFullRankDist τ :=
    hA₀_eq ▸ (isFullRankDist_empDist_iff hn A₀).mpr (isMinimalMatrix_iff.mp hA₀_min).1
  -- Entropy lower bound for every implied distribution `τ' ∈ ℐ_τ` with `1 ≤ a'`.
  have hH_ge : ∀ (a' : ℕ) (ha' : 1 ≤ a') (τ' : PMF (Fin a' → F)),
      IsImpliedDist τ τ' →
      (a' : ℝ) * (1 - mrrswRate F hn b P) ≤ pmfEntropyBase (Fintype.card F) τ' := by
    intro a' ha' τ' himp'
    have hfullτ' : IsFullRankDist τ' :=
      isFullRankDist_of_isImpliedDist hn (isFeasibleType_iff.mpr ⟨A₀, hA₀_eq⟩) hfullτ himp'
    have hbdd : BddAbove {s : ℝ | ∃ (a'' : ℕ) (_ : 1 ≤ a'') (τ'' : PMF (Fin a'' → F)),
        IsImpliedDist τ τ'' ∧
          s = 1 - pmfEntropyBase (Fintype.card F) τ'' / (distDim τ'' : ℝ)} := by
      refine ⟨1, ?_⟩
      rintro s ⟨_, _, τ'', _, rfl⟩
      linarith [div_nonneg (pmfEntropyBase_nonneg hq τ'') (Nat.cast_nonneg (distDim τ''))]
    have hle : 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ) ≤ mrrswRate F hn b P := by
      rw [← hr_eq]
      exact le_csSup hbdd ⟨a', ha', τ', himp', rfl⟩
    have hdim : (distDim τ' : ℝ) = (a' : ℝ) := by exact_mod_cast (isFullRankDist_iff τ').mp hfullτ'
    rw [hdim] at hle
    have ha'R : (0 : ℝ) < (a' : ℝ) := Nat.cast_pos.mpr ha'
    have h1 : 1 - mrrswRate F hn b P ≤ pmfEntropyBase (Fintype.card F) τ' / (a' : ℝ) := by linarith
    rwa [le_div_iff₀ ha'R, mul_comm] at h1
  -- Define counting variable `X(G) = #{U ∈ S_U | (U * G)ᵀ ∈ ℳ_{n,τ}}`.
  let S_U : Finset (Matrix (Fin a) (Fin k) F) :=
    Finset.univ.filter fun U : Matrix (Fin a) (Fin k) F ↦ HasFullRowRank U
  let M_τ : Finset (Matrix (Fin n) (Fin a) F) := typeClassFinset n hn τ
  let X : Matrix (Fin k) (Fin n) F → ℝ := fun G ↦
    ((S_U.filter fun U ↦ (U * G)ᵀ ∈ M_τ).card : ℝ)
  let N : ℝ := (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)
  have hN_eq : N = (Fintype.card F : ℝ) ^ (k * n) := by
    have hcard : Fintype.card (Matrix (Fin k) (Fin n) F) = Fintype.card F ^ (k * n) := by
      change Fintype.card (Fin k → Fin n → F) = _
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, mul_comm]
    change (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ) = (Fintype.card F : ℝ) ^ (k * n)
    exact_mod_cast hcard
  have hN_pos : 0 < N := by rw [hN_eq]; positivity
  -- If `¬ P (rowSpan G)`, then `X G = 0`.
  have hX_zero : ∀ G : Matrix (Fin k) (Fin n) F, ¬ P (rowSpan G) → X G = 0 := by
    intro G hnot
    dsimp only [X]
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro U _ hUG
    apply hnot
    have hmin_UG : IsMinimalMatrix P (U * G)ᵀ :=
      isMinimalMatrix_of_empDist_eq hn hrow hA₀_min (hA₀_eq.trans (mem_typeClassFinset.mp hUG).symm)
    have hcont : MatrixContainedIn (U * G)ᵀ (rowSpan G) := by
      rw [matrixContainedIn_iff_colSpan_le, colSpan_eq_span_range, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (mem_rowSpan_iff_exists_vecMul G _).mpr
        ⟨U j, by ext i; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]⟩
    exact (isMonotoneIncreasing_iff.mp hmono) (colSpan (U * G)ᵀ) (rowSpan G)
      ((matrixContainedIn_iff_colSpan_le _ _).mp hcont)
      (isMinimalMatrix_iff.mp hmin_UG).2.1
  -- Compute the first moment `∑ G, X G = S_U.card * M_τ.card * q ^ ((k - a) * n)`.
  have hfirst_nat :
      ∑ G : Matrix (Fin k) (Fin n) F, (S_U.filter fun U ↦ (U * G)ᵀ ∈ M_τ).card =
        S_U.card * M_τ.card * Fintype.card F ^ ((k - a) * n) := by
    calc
      ∑ G : Matrix (Fin k) (Fin n) F, (S_U.filter fun U ↦ (U * G)ᵀ ∈ M_τ).card
          = ∑ G : Matrix (Fin k) (Fin n) F, ∑ U ∈ S_U, if (U * G)ᵀ ∈ M_τ then 1 else 0 := by
            refine Finset.sum_congr rfl fun G _ ↦ ?_
            rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ U ∈ S_U, ∑ G : Matrix (Fin k) (Fin n) F, if (U * G)ᵀ ∈ M_τ then 1 else 0 :=
            Finset.sum_comm
      _ = ∑ U ∈ S_U, ∑ A ∈ M_τ,
            (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U * G = Aᵀ).card := by
            refine Finset.sum_congr rfl fun U _ ↦ ?_
            have h1 : ∀ G : Matrix (Fin k) (Fin n) F,
                (if (U * G)ᵀ ∈ M_τ then (1 : ℕ) else 0) =
                  ∑ A ∈ M_τ, if U * G = Aᵀ then 1 else 0 := fun G ↦ by
              by_cases hmem : (U * G)ᵀ ∈ M_τ
              · simp only [hmem, ↓reduceIte]
                rw [Finset.sum_eq_single (U * G)ᵀ]
                · simp
                · intro A _ hne
                  have hne' : U * G ≠ Aᵀ := fun h ↦ hne (by rw [h, Matrix.transpose_transpose])
                  simp [hne']
                · intro h; exact (h hmem).elim
              · simp only [hmem, ↓reduceIte]
                rw [Finset.sum_eq_zero]
                intro A hA
                have hne' : U * G ≠ Aᵀ := fun h ↦
                  hmem (by rw [h, Matrix.transpose_transpose]; exact hA)
                simp [hne']
            simp_rw [h1]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun A _ ↦ ?_
            rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ U ∈ S_U, ∑ _A ∈ M_τ, Fintype.card F ^ ((k - a) * n) := by
            refine Finset.sum_congr rfl fun U hU ↦ Finset.sum_congr rfl fun A _ ↦ ?_
            exact card_matrix_mul_eq_of_fullRowRank (Finset.mem_filter.mp hU).2 Aᵀ
      _ = S_U.card * M_τ.card * Fintype.card F ^ ((k - a) * n) := by
            simp [Finset.sum_const, smul_eq_mul, mul_assoc]
  have hfirst : ∑ G : Matrix (Fin k) (Fin n) F, X G =
      (S_U.card : ℝ) * (M_τ.card : ℝ) * (Fintype.card F : ℝ) ^ ((k - a) * n) := by
    have := congrArg (Nat.cast (R := ℝ)) hfirst_nat
    simpa [X, Nat.cast_sum] using this
  have hSU_pos : (0 : ℝ) < (S_U.card : ℝ) := by
    have hge := numFullRowRank_ge_half (F := F) a k hak
    rw [numFullRowRank_eq_card] at hge
    have hpow : (0 : ℝ) < (Fintype.card F : ℝ) ^ (a * k) := by positivity
    change (Fintype.card F : ℝ) ^ (a * k) ≤ 2 * (S_U.card : ℝ) at hge
    linarith
  have hM_pos : (0 : ℝ) < (M_τ.card : ℝ) := by
    have hmem : A₀ ∈ M_τ := mem_typeClassFinset.mpr hA₀_eq
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨A₀, hmem⟩)
  have hfirst_pos : 0 < ∑ G : Matrix (Fin k) (Fin n) F, X G := by
    rw [hfirst]
    positivity
  -- Chebyshev / Cauchy–Schwarz: `1 - rlcProb ≤ (N * ∑ X^2) / (∑ X)^2 - 1`.
  have hcheb : 1 - rlcProb F n k P ≤
      (N * ∑ G : Matrix (Fin k) (Fin n) F, (X G) ^ 2) /
        (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 - 1 := by
    let S_good := Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ P (rowSpan G)
    let S_bad := Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ ¬ P (rowSpan G)
    have hsum_good : ∑ G ∈ S_good, X G = ∑ G : Matrix (Fin k) (Fin n) F, X G := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun G ↦ P (rowSpan G))]
      have hbad0 : ∑ G ∈ S_bad, X G = 0 :=
        Finset.sum_eq_zero fun G hG ↦ hX_zero G (Finset.mem_filter.mp hG).2
      change ∑ G ∈ S_good, X G = ∑ G ∈ S_good, X G + ∑ G ∈ S_bad, X G
      rw [hbad0, add_zero]
    have hcs : (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 ≤
        (S_good.card : ℝ) * ∑ G : Matrix (Fin k) (Fin n) F, (X G) ^ 2 := by
      rw [← hsum_good]
      have h1 : (∑ G ∈ S_good, X G) ^ 2 ≤ (S_good.card : ℝ) * ∑ G ∈ S_good, (X G) ^ 2 := by
        have hnn : (0 : ℝ) ≤ ∑ x ∈ S_good, ∑ y ∈ S_good, (X x - X y) ^ 2 :=
          Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
        have hexp : ∑ x ∈ S_good, ∑ y ∈ S_good, (X x - X y) ^ 2 =
            2 * ((S_good.card : ℝ) * ∑ x ∈ S_good, (X x) ^ 2 - (∑ x ∈ S_good, X x) ^ 2) := by
          have hsub : ∀ x : Matrix (Fin k) (Fin n) F,
              ∑ y ∈ S_good, (X x - X y) ^ 2 =
                (S_good.card : ℝ) * (X x) ^ 2 - 2 * X x * (∑ y ∈ S_good, X y) +
                  ∑ y ∈ S_good, (X y) ^ 2 := fun x ↦ by
            simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
              nsmul_eq_mul, mul_assoc, ← Finset.mul_sum]
          simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
        linarith
      have h2 : ∑ G ∈ S_good, (X G) ^ 2 ≤ ∑ G : Matrix (Fin k) (Fin n) F, (X G) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg fun G ↦ sq_nonneg (X G)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
    have hcompl : (S_good.card : ℝ) + (S_bad.card : ℝ) = N := by
      have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun G : Matrix (Fin k) (Fin n) F ↦ P (rowSpan G))
      rw [Finset.card_univ] at h
      change S_good.card + S_bad.card = Fintype.card (Matrix (Fin k) (Fin n) F) at h
      have h' : ((S_good.card + S_bad.card : ℕ) : ℝ) =
          (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ) := by exact_mod_cast h
      simpa [Nat.cast_add] using h'
    have hrlc_eq : 1 - rlcProb F n k P = (S_bad.card : ℝ) / N := by
      rw [rlcProb_eq_card_div]
      change 1 - (S_good.card : ℝ) / N = (S_bad.card : ℝ) / N
      field_simp [hN_pos.ne']
      linarith
    have hsumsq_pos : 0 < ∑ G : Matrix (Fin k) (Fin n) F, (X G) ^ 2 := by
      have hgood_nn : (0 : ℝ) ≤ (S_good.card : ℝ) := Nat.cast_nonneg _
      have hsq_pos : 0 < (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 := sq_pos_of_pos hfirst_pos
      nlinarith
    rw [hrlc_eq, div_le_iff₀ hN_pos, sub_mul, one_mul, le_sub_iff_add_le]
    have h1 : (S_bad.card : ℝ) + (S_good.card : ℝ) = N := by linarith
    -- Directly: `(S_bad + N) * (∑ X)^2 ≤ N * (N * ∑ X^2)` from `(∑ X)^2 ≤ (N - S_bad) * (∑ X^2)`.
    have hmain : ((S_bad.card : ℝ) + N) * (∑ G, X G) ^ 2 ≤
        N * (N * ∑ G, (X G) ^ 2) := by
      have hle_N : (∑ G, X G) ^ 2 ≤ N * ∑ G, (X G) ^ 2 := by
        have hsg_le : (S_good.card : ℝ) ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) S_bad.card]
        exact hcs.trans (mul_le_mul_of_nonneg_right hsg_le hsumsq_pos.le)
      have hsub_le : (S_bad.card : ℝ) * ∑ G, (X G) ^ 2 ≤
          N * ∑ G, (X G) ^ 2 - (∑ G, X G) ^ 2 := by
        have : (S_good.card : ℝ) = N - (S_bad.card : ℝ) := by linarith
        rw [this] at hcs
        linarith
      have hbad_nn : (0 : ℝ) ≤ (S_bad.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hsq_pos : 0 < (∑ G, X G) ^ 2 := sq_pos_of_pos hfirst_pos
    rw [← le_div_iff₀ hsq_pos] at hmain
    have hgoal2 : N * (N * ∑ G, (X G) ^ 2) / (∑ G, X G) ^ 2 =
        (N * ∑ G, (X G) ^ 2) / (∑ G, X G) ^ 2 * N := by ring
    linarith
  -- Expand `∑ G, (X G)^2` over `(U₁, U₂) ∈ S_U × S_U` partitioned by `d = finrank (rowSpan U₁ ⊓
  -- rowSpan U₂)`.
  have hsecond_split :
      ∑ G : Matrix (Fin k) (Fin n) F, (X G) ^ 2 =
        ∑ d ∈ Finset.range (a + 1),
          ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) := by
    have hsq : ∀ G : Matrix (Fin k) (Fin n) F,
        (X G) ^ 2 =
          ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U, if (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ then (1 : ℝ) else 0 := by
      intro G
      dsimp only [X]
      rw [sq, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun U₁ _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun U₂ _ ↦ ?_
      split_ifs <;> simp_all
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hswap :
        (∑ U₁ ∈ S_U, ∑ G : Matrix (Fin k) (Fin n) F, ∑ U₂ ∈ S_U,
            if (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ then (1 : ℝ) else 0) =
          ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U,
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) := by
      refine Finset.sum_congr rfl fun U₁ _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun U₂ _ ↦ ?_
      rw [Finset.sum_boole]
    rw [hswap]
    have hpart : ∀ U₁ ∈ S_U,
        (∑ U₂ ∈ S_U, ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) =
          ∑ d ∈ Finset.range (a + 1),
            ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
              ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) := by
      intro U₁ hU₁
      have hmaps : ∀ U₂ ∈ S_U,
          Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) ∈ Finset.range (a + 1) := by
        intro U₂ _
        rw [Finset.mem_range]
        have hle : Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) ≤ Module.finrank F (rowSpan U₁) :=
          Submodule.finrank_mono inf_le_left
        rw [(hasFullRowRank_iff_finrank U₁).mp (Finset.mem_filter.mp hU₁).2] at hle
        omega
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    rw [Finset.sum_congr rfl hpart, Finset.sum_comm]
  -- Bound the `d = 0` term by `(∑ G, X G)^2 / N`.
  have hd0_bound :
      (∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = 0),
          ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) ≤
        (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 / N := by
    have hpair0 : ∀ U₁ ∈ S_U, ∀ U₂ ∈ S_U.filter
        (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = 0),
        ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) ≤
          (M_τ.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 / N := by
      intro U₁ hU₁ U₂ hU₂
      have hU₁r := (Finset.mem_filter.mp hU₁).2
      have hU₂r := (Finset.mem_filter.mp (Finset.mem_filter.mp hU₂).1).2
      have hd0 : Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = 0 := (Finset.mem_filter.mp hU₂).2
      have hcov_pair :
          (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ) ⊆
          (M_τ ×ˢ M_τ).biUnion fun p ↦
            Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U₁ * G = p.1ᵀ ∧
              U₂ * G = p.2ᵀ := by
        intro G hG
        obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hG).2
        exact Finset.mem_biUnion.mpr ⟨((U₁ * G)ᵀ, (U₂ * G)ᵀ), Finset.mem_product.mpr ⟨h1, h2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
      have hsum_le :
          ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) ≤
          ∑ p ∈ M_τ ×ˢ M_τ,
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hcov_pair).trans Finset.card_biUnion_le
      have hterm_le : ∀ p ∈ M_τ ×ˢ M_τ,
          ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ).card : ℝ) ≤
            ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 / N := by
        intro p _
        by_cases hex : ∃ G₀ : Matrix (Fin k) (Fin n) F, U₁ * G₀ = p.1ᵀ ∧ U₂ * G₀ = p.2ᵀ
        · rw [card_pair_matrix_mul_eq hU₁r hU₂r p.1ᵀ p.2ᵀ hex, hd0, Nat.sub_zero]
          -- Note `2 * a ≤ k` since `rowSpan U₁ ⊔ rowSpan U₂ ≤ ⊤` has finrank `2 * a`.
          have h2a_le : 2 * a ≤ k := by
            have hsup := Submodule.finrank_sup_add_finrank_inf_eq (rowSpan U₁) (rowSpan U₂)
            rw [(hasFullRowRank_iff_finrank U₁).mp hU₁r,
              (hasFullRowRank_iff_finrank U₂).mp hU₂r, hd0, add_zero] at hsup
            have hle : Module.finrank F ↥(rowSpan U₁ ⊔ rowSpan U₂) ≤ k := by
              simpa [Module.finrank_pi, Fintype.card_fin] using
                Submodule.finrank_le (rowSpan U₁ ⊔ rowSpan U₂)
            omega
          rw [hN_eq, le_div_iff₀ (pow_pos hq_pos _)]
          push_cast
          rw [← pow_mul, ← pow_add]
          refine le_of_eq (congrArg _ ?_)
          have hsub1 : (k - 2 * a) * n + k * n = (2 * k - 2 * a) * n := by
            rw [← add_mul]; congr 1; omega
          have hsub2 : (k - a) * n * 2 = (2 * k - 2 * a) * n := by
            have : (k - a) * 2 = 2 * k - 2 * a := by omega
            calc (k - a) * n * 2 = (k - a) * 2 * n := by ring
            _ = (2 * k - 2 * a) * n := by rw [this]
          omega
        · have hempty :
              (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
                U₁ * G = p.1ᵀ ∧ U₂ * G = p.2ᵀ) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro G _ h; exact hex ⟨G, h⟩
          rw [hempty, Finset.card_empty, Nat.cast_zero]
          positivity
      calc
        _ ≤ ∑ _p ∈ M_τ ×ˢ M_τ, ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 / N :=
          hsum_le.trans (Finset.sum_le_sum hterm_le)
        _ = (M_τ.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 / N := by
          rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
          push_cast; ring
    calc
      _ ≤ ∑ U₁ ∈ S_U, ∑ _U₂ ∈ S_U.filter
            (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = 0),
            ((M_τ.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 / N) :=
        Finset.sum_le_sum fun U₁ hU₁ ↦ Finset.sum_le_sum fun U₂ hU₂ ↦ hpair0 U₁ hU₁ U₂ hU₂
      _ ≤ ∑ _U₁ ∈ S_U, ∑ _U₂ ∈ S_U,
            ((M_τ.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 / N) := by
        refine Finset.sum_le_sum fun U₁ _ ↦ ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ ?_
        positivity
      _ = (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 / N := by
        rw [hfirst]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  -- Bound each `1 ≤ d ≤ a` term!
  have hd_pos_bound : ∀ d ∈ Finset.Icc 1 a,
      (N * ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter
          (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
          ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) /
        (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 ≤
        2 * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
          (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) := by
    intro d hd_mem
    obtain ⟨hd1, hda⟩ := Finset.mem_Icc.mp hd_mem
    have hpair_d : ∀ U₁ ∈ S_U, ∀ U₂ ∈ S_U.filter
        (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
        ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
          (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) ≤
          (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            (Fintype.card F : ℝ) ^
              (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) /
            N := fun U₁ hU₁ U₂ hU₂ ↦ by
      have hncard :
          (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card =
            {G : Matrix (Fin k) (Fin n) F | (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ}.ncard := by
        rw [← Set.ncard_coe_finset]
        congr 1; ext G; simp
      rw [hncard]
      exact rlc_pair_intersection_bound hn ha_le hd1 hda hak hH_ge (Finset.mem_filter.mp hU₁).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hU₂).1).2 (Finset.mem_filter.mp hU₂).2
    -- Sum `hpair_d` over `(U₁, U₂)` using `card_fullRowRank_inter_le`.
    have hsum_U :
        (∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter
            (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) ≤
          (S_U.card : ℝ) * (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) *
            ((M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
              (Fintype.card F : ℝ) ^
                (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) /
              N) := by
      calc
        _ ≤ ∑ U₁ ∈ S_U, ∑ _U₂ ∈ S_U.filter
              (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
              ((M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
                (Fintype.card F : ℝ) ^
                  (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) +
                    (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) / N) :=
          Finset.sum_le_sum fun U₁ hU₁ ↦ Finset.sum_le_sum fun U₂ hU₂ ↦ hpair_d U₁ hU₁ U₂ hU₂
        _ = (∑ U₁ ∈ S_U,
              ((S_U.filter fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d).card : ℝ)) *
              ((M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
                (Fintype.card F : ℝ) ^
                  (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) +
                    (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) / N) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
        _ ≤ (∑ _U₁ ∈ S_U, (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k)) *
              ((M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
                (Fintype.card F : ℝ) ^
                  (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) +
                    (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) / N) := by
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun U₁ hU₁ ↦ ?_)
            (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
              (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]) _))
              (Real.rpow_nonneg hq_pos.le _)) hN_pos.le)
          have hcard := card_fullRowRank_inter_le (Finset.mem_filter.mp hU₁).2 hda
          have hsame :
              (S_U.filter fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d).card =
                {U₂ : Matrix (Fin a) (Fin k) F |
                  HasFullRowRank U₂ ∧ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d}.ncard := by
            rw [← Set.ncard_coe_finset]
            congr 1; ext U₂; simp [S_U]
          rw [hsame]
          exact_mod_cast hcard
        _ = (S_U.card : ℝ) * (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) *
              ((M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
                (Fintype.card F : ℝ) ^
                  (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) +
                    (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) / N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    -- Divide by `(∑ G, X G)^2 = S_U.card^2 * M_τ.card^2 * q^((2k - 2a)n)` and use `q^(a*k) ≤ 2 *
    -- S_U.card`!
    rw [div_le_iff₀ (sq_pos_of_pos hfirst_pos)]
    have hmul_N :
        N * ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter
            (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) ≤
          (S_U.card : ℝ) * (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) *
            (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            (Fintype.card F : ℝ) ^
              (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) := by
      have h := mul_le_mul_of_nonneg_left hsum_U hN_pos.le
      refine h.trans (le_of_eq ?_)
      rw [mul_left_comm, mul_div_cancel₀ _ hN_pos.ne']
      ring
    refine hmul_N.trans ?_
    rw [hfirst]
    have hSU_ge : (Fintype.card F : ℝ) ^ (a * k) ≤ 2 * (S_U.card : ℝ) := by
      have hge := numFullRowRank_ge_half (F := F) a k hak
      rw [numFullRowRank_eq_card] at hge
      exact hge
    have hq_2ad : (Fintype.card F : ℝ) ^ (2 * a * d) ≤ (Fintype.card F : ℝ) ^ (2 * b * b) :=
      pow_le_pow_right₀ hq.le (Nat.mul_le_mul (Nat.mul_le_mul_left 2 ha_le) (hda.trans ha_le))
    have hq_exp :
        (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) *
            (Fintype.card F : ℝ) ^
              (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) ≤
          (Fintype.card F : ℝ) ^ (2 * b * b) *
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) *
            ((Fintype.card F : ℝ) ^ (a * k) * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2) := by
      have hstep :
          (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) *
              (Fintype.card F : ℝ) ^
                (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) +
                  (n : ℝ) * (d : ℝ) * mrrswRate F hn b P) =
            (Fintype.card F : ℝ) ^ (2 * a * d) *
              (Fintype.card F : ℝ) ^ (-((d : ℝ) * (n : ℝ) * ((k : ℝ) / (n : ℝ) -
                mrrswRate F hn b P))) *
              ((Fintype.card F : ℝ) ^ (a * k) * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2) := by
        rw [← pow_mul ((Fintype.card F : ℝ)) ((k - a) * n) 2,
          ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos,
          ← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos]
        congr 1
        have hka : a ≤ k := by omega
        have h2ka : 2 * a ≤ 2 * k := by omega
        have hsub1 : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) := Nat.cast_sub hka
        have hsub2 : ((a - d : ℕ) : ℝ) = (a : ℝ) - (d : ℝ) := Nat.cast_sub hda
        have hsub3 : ((2 * k - 2 * a : ℕ) : ℝ) = 2 * (k : ℝ) - 2 * (a : ℝ) := by
          rw [Nat.cast_sub h2ka]; push_cast; ring
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hsub1, hsub2, hsub3]
        have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
        rw [mul_assoc (d : ℝ) (n : ℝ), mul_sub (n : ℝ), mul_div_cancel₀ _ hn0]
        ring
      rw [hstep]
      have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      have hpow_le :
          (Fintype.card F : ℝ) ^ (-((d : ℝ) * (n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) ≤
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) := by
        refine Real.rpow_le_rpow_of_exponent_le hq.le ?_
        have hdn : (n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P) ≤
            (d : ℝ) * ((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P)) :=
          le_mul_of_one_le_left (mul_nonneg hn_pos.le hdelta_pos.le) hd_ge1
        exact neg_le_neg (by simpa [mul_assoc] using hdn)
      have h1 := mul_le_mul hq_2ad hpow_le (Real.rpow_nonneg hq_pos.le _)
        (pow_nonneg hq_pos.le _)
      exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (pow_nonneg hq_pos.le _) (sq_nonneg _))
    have hmul_S :
        (S_U.card : ℝ) * (Fintype.card F : ℝ) ^ (a * k) ≤ 2 * (S_U.card : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hSU_ge (Nat.cast_nonneg (α := ℝ) S_U.card)
      exact h.trans (le_of_eq (by ring))
    have hfinal :
        (S_U.card : ℝ) * (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            ((Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) *
              (Fintype.card F : ℝ) ^
                (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) +
                  (n : ℝ) * (d : ℝ) * mrrswRate F hn b P)) ≤
          (S_U.card : ℝ) * (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            ((Fintype.card F : ℝ) ^ (2 * b * b) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) *
              ((Fintype.card F : ℝ) ^ (a * k) * ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hq_exp
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
          (pow_nonneg (add_nonneg (Nat.cast_nonneg n) zero_le_one) _))
    calc
      (S_U.card : ℝ) * (Fintype.card F : ℝ) ^ (2 * a * d + (a - d) * k) * (M_τ.card : ℝ) ^ 2 *
          ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
          (Fintype.card F : ℝ) ^
            (((2 * k - 2 * a : ℕ) : ℝ) * (n : ℝ) + (n : ℝ) * (d : ℝ) * mrrswRate F hn b P)
          ≤ (S_U.card : ℝ) * (Fintype.card F : ℝ) ^ (a * k) * (M_τ.card : ℝ) ^ 2 *
              ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
              ((Fintype.card F : ℝ) ^ (2 * b * b) *
                (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) *
                ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2) := by
        convert hfinal using 1 <;> ring
      _ ≤ (2 * (S_U.card : ℝ) ^ 2) * (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            ((Fintype.card F : ℝ) ^ (2 * b * b) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) *
              ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2) := by
        have hpos_r : 0 ≤ (M_τ.card : ℝ) ^ 2 * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            ((Fintype.card F : ℝ) ^ (2 * b * b) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) *
              ((Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2) :=
          mul_nonneg (mul_nonneg (sq_nonneg _)
            (pow_nonneg (add_nonneg (Nat.cast_nonneg n) zero_le_one) _))
            (mul_nonneg (mul_nonneg (pow_nonneg hq_pos.le _) (Real.rpow_nonneg hq_pos.le _))
              (sq_nonneg _))
        have h := mul_le_mul_of_nonneg_right hmul_S hpos_r
        convert h using 1 <;> ring
      _ = 2 * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) *
            ((S_U.card : ℝ) * (M_τ.card : ℝ) * (Fintype.card F : ℝ) ^ ((k - a) * n)) ^ 2 := by
        ring
  -- Combine `d = 0` and `1 ≤ d ≤ a`!
  have hsplit_range :
      (∑ d ∈ Finset.range (a + 1),
          ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) =
        (∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = 0),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) +
        ∑ d ∈ Finset.Icc 1 a,
          ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ) := by
    have hrange : Finset.range (a + 1) = insert 0 (Finset.Icc 1 a) := by
      ext d; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
  refine hcheb.trans ?_
  rw [hsecond_split, hsplit_range, mul_add, add_div]
  have hd0_div :
      (N * ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = 0),
          ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) /
        (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hfirst_pos)]
    have h := mul_le_mul_of_nonneg_left hd0_bound hN_pos.le
    exact h.trans (le_of_eq (mul_div_cancel₀ _ hN_pos.ne'))
  have hsum_pos_d :
      (N * ∑ d ∈ Finset.Icc 1 a,
          ∑ U₁ ∈ S_U, ∑ U₂ ∈ S_U.filter (fun U₂ ↦ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d),
            ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
              (U₁ * G)ᵀ ∈ M_τ ∧ (U₂ * G)ᵀ ∈ M_τ).card : ℝ)) /
        (∑ G : Matrix (Fin k) (Fin n) F, X G) ^ 2 ≤
        2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) *
          ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
          (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) := by
    rw [Finset.mul_sum, Finset.sum_div]
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 a,
            2 * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) :=
        Finset.sum_le_sum hd_pos_bound
      _ = ((Finset.Icc 1 a).card : ℝ) *
            (2 * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (b : ℝ) *
            (2 * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P)))) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq_pos.le _))
            (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]) _))
            (Real.rpow_nonneg hq_pos.le _))
        rw [Nat.card_Icc]
        have : a + 1 - 1 ≤ b := by omega
        exact_mod_cast this
      _ = _ := by ring
  exact (sub_le_sub_right (add_le_add hd0_div hsum_pos_d) 1).trans (le_of_eq (by ring))

/-- **MRRSW RLC Threshold Theorem** (`thm:RLCThreshold`): `|R_RLC(𝒫) - mrrswRate(𝒫)|` is
bounded by `O_{q,b}(log_q(n + 1) / n)`. -/
theorem rlcThreshold_sub_mrrswRate_abs_le {n b : ℕ} (hn : 0 < n) (hb : 1 ≤ b)
    {P : Submodule F (Fin n → F) → Prop} (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    (hrow : IsRowSymmetric P) (hbot : ¬ P ⊥) (htop : P ⊤) :
    |rlcThreshold F n P - mrrswRate F hn b P| ≤
      ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
        Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := lt_trans zero_lt_one hq
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlogq : 0 < Real.log (Fintype.card F) := Real.log_pos hq
  let δ := ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
      Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ)
  have hlog_n1 : 0 ≤ Real.logb (Fintype.card F) (n + 1) :=
    Real.logb_nonneg hq (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlog_4b : 0 ≤ Real.logb (Fintype.card F) (4 * (b : ℝ)) := by
    refine Real.logb_nonneg hq ?_
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    refine div_pos ?_ hn_pos
    have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    nlinarith [pow_nonneg hq_pos.le b]
  rw [abs_le]
  constructor
  · -- Lower bound: `mrrswRate - δ ≤ rlcThreshold`.
    have hle1 : mrrswRate F hn b P - δ ≤ 1 := by
      linarith [mrrswRate_le_one hn hmono hloc hbot htop]
    have hlow : mrrswRate F hn b P - δ ≤ rlcThreshold F n P := by
      refine le_rlcThreshold_of_forall_lt hle1 fun k _hk hlt ↦ ?_
      have hup := rlc_upper_bound (F := F) hn hmono hloc hbot (k := k)
      have hlt_pow :
          ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) *
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) <
            (1 / 2 : ℝ) := by
        have h1 : (n : ℝ) * δ < (n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)) :=
          mul_lt_mul_of_pos_left (by linarith) hn_pos
        have hpow_lt :
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ)))) <
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * δ)) :=
          Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
        have hC_pos : (0 : ℝ) < (n + 1 : ℝ) ^ (Fintype.card F ^ b) := by positivity
        have hmul_lt := mul_lt_mul_of_pos_left hpow_lt hC_pos
        refine hmul_lt.trans_le ?_
        -- Show `(n+1)^(q^b) * q^(-n*δ) ≤ 1/2`.
        have hn1_eq : ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) =
            (Fintype.card F : ℝ) ^ ((Fintype.card F ^ b : ℝ) *
              Real.logb (Fintype.card F) (n + 1)) := by
          rw [mul_comm, Real.rpow_mul hq_pos.le,
            Real.rpow_logb hq_pos hq.ne' (by positivity), ← Nat.cast_pow, Real.rpow_natCast]
        have hhalf : (1 / 2 : ℝ) ≥ (Fintype.card F : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one]
          have hq2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
          have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq2
          linarith
        rw [hn1_eq, ← Real.rpow_add hq_pos]
        refine (Real.rpow_le_rpow_of_exponent_le hq.le ?_).trans hhalf
        have hnδ : (n : ℝ) * δ = (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
            Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2 := by
          dsimp only [δ]; field_simp [hn_pos.ne']
        rw [hnδ]
        have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        nlinarith
      exact hup.trans_lt hlt_pow
    linarith
  · -- Upper bound: `rlcThreshold ≤ mrrswRate + δ`.
    by_cases hgt1 : 1 ≤ mrrswRate F hn b P + δ
    · linarith [rlcThreshold_le_one F n P]
    · push Not at hgt1
      -- Pick `k = ⌈(mrrswRate + δ') * n⌉` with `δ' = δ - 1 / n`.
      let δ' := ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 1) / (n : ℝ)
      have hδ'_eq : δ' + 1 / (n : ℝ) = δ := by dsimp only [δ', δ]; ring
      let k := Nat.ceil ((mrrswRate F hn b P + δ') * (n : ℝ))
      have hk_le_n : k ≤ n := by
        rw [Nat.ceil_le]
        have h1 : mrrswRate F hn b P + δ' ≤ 1 := by
          have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
          linarith
        nlinarith
      have hk_ge_R : mrrswRate F hn b P + δ' ≤ (k : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ hn_pos]
        exact Nat.le_ceil _
      have hk_lt_R : (k : ℝ) / (n : ℝ) < mrrswRate F hn b P + δ := by
        have hlt_ceil : (k : ℝ) < (mrrswRate F hn b P + δ') * (n : ℝ) + 1 := by
          have hnn : 0 ≤ (mrrswRate F hn b P + δ') * (n : ℝ) := by
            have hm := mrrswRate_nonneg (F := F) hn (b := b) (P := P)
            have hδ'0 : 0 ≤ δ' := by
              dsimp only [δ']
              refine div_nonneg ?_ hn_pos.le
              have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
              nlinarith [pow_nonneg hq_pos.le b]
            nlinarith
          exact Nat.ceil_lt_add_one hnn
        rw [div_lt_iff₀ hn_pos, ← hδ'_eq]
        have hmul : (mrrswRate F hn b P + (δ' + 1 / (n : ℝ))) * (n : ℝ) =
            (mrrswRate F hn b P + δ') * (n : ℝ) + 1 := by
          field_simp [hn_pos.ne']; ring
        linarith
      have hbk : b + 1 ≤ k := by
        have h1 : ((b : ℝ) + 1) / (n : ℝ) ≤ δ' := by
          dsimp only [δ']
          refine div_le_div_of_nonneg_right ?_ hn_pos.le
          have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
          nlinarith [pow_nonneg hq_pos.le b]
        have h2 : ((b : ℝ) + 1) / (n : ℝ) ≤ (k : ℝ) / (n : ℝ) := by
          linarith [mrrswRate_nonneg (F := F) hn (b := b) (P := P)]
        have h3 : (b : ℝ) + 1 ≤ (k : ℝ) := by
          rwa [div_le_div_iff_of_pos_right hn_pos] at h2
        exact_mod_cast h3
      have hlow := rlc_lower_bound (F := F) hn hb hbk hmono hloc hrow hbot htop
      have hfail_le :
          (2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) *
            ((n + 1 : ℝ) ^ (Fintype.card F ^ b))) *
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) ≤
            (1 / 2 : ℝ) := by
        have h1 : (n : ℝ) * δ' ≤ (n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P) :=
          mul_le_mul_of_nonneg_left (by linarith) hn_pos.le
        have hpow_le :
            (Fintype.card F : ℝ) ^ (-((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P))) ≤
              (Fintype.card F : ℝ) ^ (-((n : ℝ) * δ')) :=
          Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
        refine (mul_le_mul_of_nonneg_left hpow_le (by positivity)).trans ?_
        -- Show `2 * b * q^(2b^2) * (n+1)^(q^b) * q^(-n*δ') ≤ 1/2`, i.e. `4 * b * q^(2b^2) *
        -- (n+1)^(q^b) ≤ q^(n*δ')`.
        have h4b_eq : 4 * (b : ℝ) =
          (Fintype.card F : ℝ) ^ Real.logb (Fintype.card F) (4 * (b : ℝ)) := by
          have hb_pos : (0 : ℝ) < 4 * (b : ℝ) := by
            have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
            linarith
          exact (Real.rpow_logb hq_pos hq.ne' hb_pos).symm
        have hn1_eq : ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) =
            (Fintype.card F : ℝ) ^ ((Fintype.card F ^ b : ℝ) *
              Real.logb (Fintype.card F) (n + 1)) := by
          rw [mul_comm, Real.rpow_mul hq_pos.le,
            Real.rpow_logb hq_pos hq.ne' (by positivity), ← Nat.cast_pow, Real.rpow_natCast]
        have h2bb_eq : (Fintype.card F : ℝ) ^ (2 * b * b) =
            (Fintype.card F : ℝ) ^ (2 * (b : ℝ) ^ 2) := by
          rw [← Real.rpow_natCast]; congr 1; push_cast; ring
        have hprod_eq :
            2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n +
              1 : ℝ) ^ (Fintype.card F ^ b)) =
              (1 / 2 : ℝ) *
                (Fintype.card F : ℝ) ^ (Real.logb (Fintype.card F) (4 * (b : ℝ)) +
                  2 * (b : ℝ) ^ 2 + (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n +
                    1)) := by
          rw [Real.rpow_add hq_pos, Real.rpow_add hq_pos, ← h4b_eq, ← h2bb_eq, ← hn1_eq]
          ring
        rw [hprod_eq, mul_assoc, ← Real.rpow_add hq_pos]
        have hnδ' : (n : ℝ) * δ' = (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
            Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 1 := by
          dsimp only [δ']; field_simp [hn_pos.ne']
        have hexp_le :
            Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 +
              (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) + -((n : ℝ) * δ') ≤
                0 := by
          rw [hnδ']
          have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
          linarith
        have hpow1 :
            (Fintype.card F : ℝ) ^ (Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 +
              (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) + -((n : ℝ) * δ')) ≤
                1 := by
          calc
            _ ≤ (Fintype.card F : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le hexp_le
            _ = 1 := Real.rpow_zero _
        linarith
      have hprob_ge : (1 / 2 : ℝ) ≤ rlcProb F n k P := by linarith
      have hthr_le := rlcThreshold_le_of_prob_ge hk_le_n hprob_ge
      linarith

/-- **MRRSW Sharp Threshold (Below Threshold)**: if `k / n ≤ rlcThreshold F n P - ε`, then
`rlcProb F n k P ≤ q ^ (-n * (ε - O_{q,b}(log(n+1)/n)))`. -/
theorem rlc_sharp_below {n b k : ℕ} (hn : 0 < n) (hb : 1 ≤ b)
    {P : Submodule F (Fin n → F) → Prop} (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    (hrow : IsRowSymmetric P) (hbot : ¬ P ⊥) (htop : P ⊤) {ε : ℝ}
    (hR : (k : ℝ) / (n : ℝ) ≤ rlcThreshold F n P - ε) :
    rlcProb F n k P ≤
      (Fintype.card F : ℝ) ^
        (-((n : ℝ) * (ε - (2 * (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) +
            2) / (n : ℝ)))) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := lt_trans zero_lt_one hq
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hup := rlc_upper_bound (F := F) hn hmono hloc hbot (k := k)
  have hthr := (abs_le.mp (rlcThreshold_sub_mrrswRate_abs_le hn hb hmono hloc hrow hbot htop)).2
  have hn1_eq : ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) =
      (Fintype.card F : ℝ) ^ ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) := by
    rw [mul_comm, Real.rpow_mul hq_pos.le,
      Real.rpow_logb hq_pos hq.ne' (by positivity), ← Nat.cast_pow, Real.rpow_natCast]
  refine hup.trans ?_
  rw [hn1_eq, ← Real.rpow_add hq_pos]
  refine Real.rpow_le_rpow_of_exponent_le hq.le ?_
  have h1 : (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
      -((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ))) =
      -((n : ℝ) * (mrrswRate F hn b P - (k : ℝ) / (n : ℝ) -
        ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) / (n : ℝ))) := by
    field_simp [hn_pos.ne']; ring
  rw [h1]
  have h2 : ε - (2 * (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
        Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) ≤
      mrrswRate F hn b P - (k : ℝ) / (n : ℝ) -
        ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) / (n : ℝ) := by
    have hdiv :
        (2 * (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) =
        ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) +
          ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) / (n : ℝ) := by
      ring
    linarith
  nlinarith

/-- **MRRSW Sharp Threshold (Above Threshold)**: if `k / n ≥ rlcThreshold F n P + ε` and
`b + 1 ≤ k`, then `1 - rlcProb F n k P ≤ q ^ (-n * (ε - O_{q,b}(log(n+1)/n)))`. -/
theorem rlc_sharp_above {n b k : ℕ} (hn : 0 < n) (hb : 1 ≤ b) (hbk : b + 1 ≤ k)
    {P : Submodule F (Fin n → F) → Prop} (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    (hrow : IsRowSymmetric P) (hbot : ¬ P ⊥) (htop : P ⊤) {ε : ℝ}
    (hR : rlcThreshold F n P + ε ≤ (k : ℝ) / (n : ℝ)) :
    1 - rlcProb F n k P ≤
      (Fintype.card F : ℝ) ^
        (-((n : ℝ) * (ε - (2 * (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          2 * Real.logb (Fintype.card F) (4 * (b : ℝ)) + 4 * (b : ℝ) ^ 2 + (b : ℝ) +
            2) / (n : ℝ)))) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := lt_trans zero_lt_one hq
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlow := rlc_lower_bound (F := F) hn hb hbk hmono hloc hrow hbot htop
  have hthr := (abs_le.mp (rlcThreshold_sub_mrrswRate_abs_le hn hb hmono hloc hrow hbot htop)).1
  have h2b_le : 2 * (b : ℝ) ≤ 4 * (b : ℝ) := by
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b; linarith
  have h4b_eq : 4 * (b : ℝ) = (Fintype.card F : ℝ) ^ Real.logb (Fintype.card F) (4 * (b : ℝ)) := by
    have hb_pos : (0 : ℝ) < 4 * (b : ℝ) := by
      have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      linarith
    exact (Real.rpow_logb hq_pos hq.ne' hb_pos).symm
  have hn1_eq : ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) =
      (Fintype.card F : ℝ) ^ ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) := by
    rw [mul_comm, Real.rpow_mul hq_pos.le,
      Real.rpow_logb hq_pos hq.ne' (by positivity), ← Nat.cast_pow, Real.rpow_natCast]
  have h2bb_eq : (Fintype.card F : ℝ) ^ (2 * b * b) =
      (Fintype.card F : ℝ) ^ (2 * (b : ℝ) ^ 2) := by
    rw [← Real.rpow_natCast]; congr 1; push_cast; ring
  have hC_le :
      2 * (b : ℝ) * (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) ≤
        (Fintype.card F : ℝ) ^ (Real.logb (Fintype.card F) (4 * (b : ℝ)) +
          2 * (b : ℝ) ^ 2 + (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) := by
    rw [Real.rpow_add hq_pos, Real.rpow_add hq_pos, ← h4b_eq, ← h2bb_eq, ← hn1_eq]
    have : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ (2 * b * b) * ((n + 1 : ℝ) ^ (Fintype.card F ^ b)) := by
      positivity
    nlinarith
  refine hlow.trans ?_
  refine (mul_le_mul_of_nonneg_right hC_le (Real.rpow_nonneg hq_pos.le _)).trans ?_
  rw [← Real.rpow_add hq_pos]
  refine Real.rpow_le_rpow_of_exponent_le hq.le ?_
  have h1 :
      Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 +
          (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
        -((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P)) =
      -((n : ℝ) * ((k : ℝ) / (n : ℝ) - mrrswRate F hn b P -
        (Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 +
          (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) / (n : ℝ))) := by
    field_simp [hn_pos.ne']; ring
  rw [h1]
  have h2 :
      ε - (2 * (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
        2 * Real.logb (Fintype.card F) (4 * (b : ℝ)) + 4 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) ≤
      (k : ℝ) / (n : ℝ) - mrrswRate F hn b P -
        (Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 +
          (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) / (n : ℝ) := by
    have hdiv :
        (2 * (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          2 * Real.logb (Fintype.card F) (4 * (b : ℝ)) + 4 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) =
        ((Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1) +
          Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 + (b : ℝ) + 2) / (n : ℝ) +
          (Real.logb (Fintype.card F) (4 * (b : ℝ)) + 2 * (b : ℝ) ^ 2 +
            (Fintype.card F ^ b : ℝ) * Real.logb (Fintype.card F) (n + 1)) / (n : ℝ) := by
      ring
    linarith
  nlinarith

end ThresholdTheorem

end CslibFrontier.Foundations.Data.Code
