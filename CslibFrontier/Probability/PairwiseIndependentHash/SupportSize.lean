module

public import CslibFrontier.Probability.BitString.AffineHash
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pairwise-Independent Affine-Hash Support-Size Estimator

This module defines the zero-hitting probability `affineHashHitProb R j T` of a uniformly random
`j`-bit affine hash function on a finite set `T ⊆ BitString R` and proves that summing this
probability over `j = 0, ..., R` estimates `⌊log₂ |T|⌋` within `[-1, +3]`.

## Main definitions

* `CslibFrontier.Probability.PairwiseIndependentHash.affineHashHitProb`: exact probability that a
  uniformly random `j`-bit affine hash sends some element of `T ⊆ BitString R` to `0^j`.

## Main results

* `CslibFrontier.Probability.PairwiseIndependentHash.affineHashHitProb_empty`
* `CslibFrontier.Probability.PairwiseIndependentHash.affineHashHitSum_bounds`:
  `⌊log₂ #T⌋ - 1 ≤ ∑_{j=0}^R Pr[0 ∈ h_j(T)] ≤ ⌊log₂ #T⌋ + 3` for every nonempty `T ⊆ BitString R`.
-/

public section

namespace CslibFrontier.Probability.PairwiseIndependentHash

open Finset Cslib Cslib.BitString
open scoped BigOperators NNReal

/-! ### : Pairwise-Independent Affine-Hash Support-Size Estimator -/

/-- Exact real probability that a uniformly random `j`-bit affine hash sends some element of
`T ⊆ BitString R` to `0^j`. -/
@[expose] noncomputable def affineHashHitProb (R j : ℕ) (T : Finset (BitString R)) : ℝ :=
  ((Finset.dens {seed : (Fin j → BitString R) × BitString j |
      (fun _ => false) ∈ T.image (Cslib.BitString.LinearHash.affineHash seed)} : ℚ≥0) : ℝ)

/-- `affineHashHitProb R j T` is `0` when `T = ∅`. -/
theorem affineHashHitProb_empty (R j : ℕ) : affineHashHitProb R j ∅ = 0 := by
  simp [affineHashHitProb]

/-- **Affine-hash support-size estimator**: for every nonempty `T ⊆ BitString R`,
`⌊log₂ #T⌋ - 1 ≤ ∑_{j=0}^R Pr[0 ∈ affineHash_j(T)] ≤ ⌊log₂ #T⌋ + 3`. -/
theorem affineHashHitSum_bounds (R : ℕ) {T : Finset (BitString R)} (hT : T.Nonempty) :
    (Nat.log 2 #T : ℝ) - 1 ≤ (∑ j : Fin (R + 1), affineHashHitProb R j.val T) ∧
      (∑ j : Fin (R + 1), affineHashHitProb R j.val T) ≤ (Nat.log 2 #T : ℝ) + 3 := by
  set L := Nat.log 2 #T
  have hT_pos : 0 < #T := hT.card_pos
  have hT_le : #T ≤ 2 ^ R := by
    calc #T ≤ #(Finset.univ : Finset (BitString R)) := Finset.card_le_univ T
      _ = 2 ^ R := by simp
  have hL_le_R : L ≤ R := by
    have h := Nat.log_mono_right (b := 2) hT_le
    rwa [Nat.log_pow one_lt_two] at h
  have h2L_le : (2 : ℝ) ^ L ≤ (#T : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hT_pos.ne'
  have hT_lt_2L1 : (#T : ℝ) < (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two #T
  have hprob_bd : ∀ j : ℕ, 0 ≤ affineHashHitProb R j T ∧ affineHashHitProb R j T ≤ 1 := fun j =>
    ⟨NNRat.cast_nonneg _, by
      dsimp only [affineHashHitProb]
      have h1 : Finset.dens {seed : (Fin j → BitString R) × BitString j |
          (fun _ => false) ∈ T.image (Cslib.BitString.LinearHash.affineHash seed)} ≤ 1 :=
        Finset.dens_le_one
      exact_mod_cast h1⟩
  have hprob_le : ∀ j : ℕ, affineHashHitProb R j T ≤ (#T : ℝ) / (2 : ℝ) ^ j := fun j => by
    have hh := Cslib.BitString.LinearHash.isPairwiseIndependentHash_affineHash j R
    have hq := hh.dens_filter_mem_image_le T (fun _ => false)
    dsimp only [affineHashHitProb]
    have hR : ((Finset.dens {seed : (Fin j → BitString R) × BitString j |
        (fun _ => false) ∈ T.image (Cslib.BitString.LinearHash.affineHash seed)} : ℚ≥0) : ℝ) ≤
        (((#T : ℚ≥0) / (Fintype.card (BitString j) : ℚ≥0) : ℚ≥0) : ℝ) := by
      exact_mod_cast hq
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hR
  have hprob_ge : ∀ j : ℕ, 1 - (2 : ℝ) ^ j / (#T : ℝ) ≤ affineHashHitProb R j T := fun j => by
    have hh := Cslib.BitString.LinearHash.isPairwiseIndependentHash_affineHash j R
    have hq := hh.dens_filter_notMem_image_le hT (fun _ => false)
    have hsplit := Finset.dens_filter_add_dens_filter_not_eq_dens
      (s := (Finset.univ : Finset ((Fin j → BitString R) × BitString j)))
      (fun seed => (fun _ => false) ∈ T.image (Cslib.BitString.LinearHash.affineHash seed))
    rw [Finset.dens_univ] at hsplit
    have hsplitR : affineHashHitProb R j T +
        ((Finset.dens {seed : (Fin j → BitString R) × BitString j |
          (fun _ => false) ∉ T.image (Cslib.BitString.LinearHash.affineHash seed)} : ℚ≥0) : ℝ) =
        1 := by
      dsimp only [affineHashHitProb]
      exact_mod_cast hsplit
    have hmiss : ((Finset.dens {seed : (Fin j → BitString R) × BitString j |
          (fun _ => false) ∉ T.image (Cslib.BitString.LinearHash.affineHash seed)} : ℚ≥0) : ℝ) ≤
        (2 : ℝ) ^ j / (#T : ℝ) := by
      have hR : ((Finset.dens {seed : (Fin j → BitString R) × BitString j |
            (fun _ => false) ∉ T.image (Cslib.BitString.LinearHash.affineHash seed)} : ℚ≥0) : ℝ) ≤
          (((Fintype.card (BitString j) : ℚ≥0) / (#T : ℚ≥0) : ℚ≥0) : ℝ) := by
        exact_mod_cast hq
      simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hR
    linarith
  have hsum_range : ∑ j : Fin (R + 1), affineHashHitProb R j.val T =
      ∑ j ∈ Finset.range (R + 1), affineHashHitProb R j T :=
    Fin.sum_univ_eq_sum_range (fun j => affineHashHitProb R j T) (R + 1)
  rw [hsum_range]
  constructor
  · -- Lower bound: keep terms `j = 0 .. L`.
    have hsub : Finset.range (L + 1) ⊆ Finset.range (R + 1) :=
      Finset.range_mono (by omega)
    have hgeom : ∑ j ∈ Finset.range (L + 1), (2 : ℝ) ^ j = (2 : ℝ) ^ (L + 1) - 1 := by
      have := geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) (L + 1)
      linarith
    calc (L : ℝ) - 1
        = ((L + 1 : ℝ)) - 2 := by ring
      _ ≤ (L + 1 : ℝ) - ((2 : ℝ) ^ (L + 1) - 1) / (#T : ℝ) := by
          have hdiv : ((2 : ℝ) ^ (L + 1) - 1) / (#T : ℝ) ≤ 2 := by
            rw [div_le_iff₀ (by positivity)]
            have : (2 : ℝ) ^ (L + 1) = 2 * (2 : ℝ) ^ L := by rw [pow_succ']
            linarith
          linarith
      _ = ∑ j ∈ Finset.range (L + 1), (1 - (2 : ℝ) ^ j / (#T : ℝ)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            ← Finset.sum_div, hgeom, Nat.cast_add, Nat.cast_one]
      _ ≤ ∑ j ∈ Finset.range (L + 1), affineHashHitProb R j T :=
          Finset.sum_le_sum fun j _ => hprob_ge j
      _ ≤ ∑ j ∈ Finset.range (R + 1), affineHashHitProb R j T :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (hprob_bd j).1
  · -- Upper bound: split at `L + 1`; terms `< L + 1` are `≤ 1`, tail decays geometrically.
    have hsplit : ∑ j ∈ Finset.range (R + 1), affineHashHitProb R j T =
        ∑ j ∈ Finset.range (L + 1), affineHashHitProb R j T +
        ∑ k ∈ Finset.range (R - L), affineHashHitProb R (L + 1 + k) T := by
      have hR : R + 1 = (L + 1) + (R - L) := by omega
      rw [hR, Finset.sum_range_add]
    rw [hsplit]
    have hhead : ∑ j ∈ Finset.range (L + 1), affineHashHitProb R j T ≤ (L : ℝ) + 1 := by
      calc ∑ j ∈ Finset.range (L + 1), affineHashHitProb R j T
          ≤ ∑ _j ∈ Finset.range (L + 1), (1 : ℝ) := Finset.sum_le_sum fun j _ => (hprob_bd j).2
        _ = (L : ℝ) + 1 := by simp
    have htail : ∑ k ∈ Finset.range (R - L), affineHashHitProb R (L + 1 + k) T ≤ 2 := by
      have h1 : ∀ k : ℕ, affineHashHitProb R (L + 1 + k) T ≤ (1 / 2 : ℝ) ^ k := fun k => by
        refine (hprob_le (L + 1 + k)).trans ?_
        rw [pow_add, one_div_pow, div_le_iff₀ (by positivity)]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        field_simp [hpos.ne']
        linarith
      have hgeom : ∑ k ∈ Finset.range (R - L), (1 / 2 : ℝ) ^ k ≤ 2 := by
        rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        have hneg : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
        rw [hneg, div_neg]
        have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (R - L) := by positivity
        linarith
      exact (Finset.sum_le_sum fun k _ => h1 k).trans hgeom
    linarith

end CslibFrontier.Probability.PairwiseIndependentHash
