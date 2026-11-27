/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.Combinatorics.Expander.Basic
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Combinatorics.Expander.AffineFamily
import CslibFrontier.Foundations.Combinatorics.Expander.Loops
import CslibFrontier.Foundations.Combinatorics.Expander.Mixing
import CslibFrontier.Foundations.Combinatorics.Expander.Power
import CslibFrontier.Foundations.Combinatorics.Expander.Reindex
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vector-Valued Expander Mixing and Explicit Power-of-Two-Degree Expanders

This module extends `CslibFrontier`'s expander library with two general tools:

1. **Vector-valued expander mixing lemma** (`Cslib.RotationMap.abs_expect_sum_mul_neighbor_le`):
   for a `D`-regular graph `H : RotationMap V D` with `H.spectralExpansion ≤ lam` and mean-zero
   vector-valued functions `α, β : V → ι → ℝ`,
   `|𝔼 x, 𝔼 d, ∑ i, α x i * β (H.neighbor x d) i|` is bounded by
   `lam * √(𝔼 x, ∑ i, α x i ^ 2) * √(𝔼 y, ∑ i, β y i ^ 2)`.
2. **Explicit power-of-two-degree $\lambda$-expander families**
   (`Cslib.RotationMap.powTwoExpanderFin`, `Cslib.RotationMap.powTwoExpanderBitString`,
   `Cslib.RotationMap.exists_pow_two_expander_family`): instantiating
   `Cslib.RotationMap.affinePlaneFamily` over `GaloisField 2 8` (`q = 256`, base degree
   `2 * 256 ^ 12 = 2 ^ 97`) and powering with `RotationMap.pow` yields `2^d`-regular
   `lam`-expanders on arbitrary finite vertex sets with `d = O(log (1 / lam) + 1)`.

## Main definitions

* `Cslib.RotationMap.baseExpanderFin`: `2 ^ 97`-regular `GF(256)` base expander on `Fin n`.
* `Cslib.RotationMap.powTwoExpanderFin`: `2 ^ d`-regular `lam`-expander on `Fin n`.
* `Cslib.RotationMap.powTwoExpanderBitString`: `2 ^ d`-regular `lam`-expander on `BitString m`.

## Main results

* `Cslib.RotationMap.abs_expect_sum_mul_neighbor_le`: vector-valued expander mixing lemma.
* `Cslib.RotationMap.spectralExpansion_powTwoExpanderFin_le`: spectral bound on `Fin n`.
* `Cslib.RotationMap.spectralExpansion_powTwoExpanderBitString_le`: spectral bound on `BitString m`.
* `Cslib.RotationMap.exists_pow_two_expander_family`: universal constant `C > 0` with
  `d ≤ C * (Real.log (1 / lam) + 1)` and `H.spectralExpansion ≤ lam`.
-/

public section

namespace Cslib.RotationMap

open Cslib Finset
open scoped BigOperators

/-! ### Vector-Valued Expander Mixing Lemma -/

/-- **Vector-valued expander mixing lemma**: for a regular graph `H` with spectral expansion at
most `lam` and mean-zero vector-valued functions `α, β : V → ι → ℝ`,
`|𝔼 x, 𝔼 d, ∑ i, α x i * β (H.neighbor x d) i|` is bounded by
`lam * √(𝔼 x, ∑ i, α x i ^ 2) * √(𝔼 y, ∑ i, β y i ^ 2)`. -/
theorem abs_expect_sum_mul_neighbor_le {V D ι : Type*} [Fintype V] [Fintype D] [Nonempty D]
    [Fintype ι] (H : RotationMap V D) {lam : ℝ} (hH : H.spectralExpansion ≤ lam)
    (α β : V → ι → ℝ) (hα : ∀ i, 𝔼 x, α x i = 0) (hβ : ∀ i, 𝔼 y, β y i = 0) :
    |𝔼 x, 𝔼 d, ∑ i, α x i * β (H.neighbor x d) i| ≤
      lam * Real.sqrt (𝔼 x, ∑ i, α x i ^ 2) * Real.sqrt (𝔼 y, ∑ i, β y i ^ 2) := by
  have hlam : 0 ≤ lam := H.spectralExpansion_nonneg.trans hH
  have hsum : (𝔼 x, 𝔼 d, ∑ i, α x i * β (H.neighbor x d) i) =
      ∑ i, 𝔼 x, α x i * H.walk (fun y ↦ β y i) x := by
    have h1 : (𝔼 x, 𝔼 d, ∑ i, α x i * β (H.neighbor x d) i) =
        𝔼 x, ∑ i, 𝔼 d, α x i * β (H.neighbor x d) i :=
      expect_congr rfl fun _ _ ↦ expect_sum_comm _ _ _
    rw [h1, expect_sum_comm]
    refine sum_congr rfl fun i _ ↦ expect_congr rfl fun x _ ↦ ?_
    rw [RotationMap.walk_apply, mul_expect]
  have hcoord : ∀ i : ι, |𝔼 x, α x i * H.walk (fun y ↦ β y i) x| ≤
      lam * Real.sqrt (𝔼 x, α x i ^ 2) * Real.sqrt (𝔼 y, β y i ^ 2) := by
    intro i
    have hmix := H.sq_expect_mul_walk_pow_sub_le 1 (fun x ↦ α x i) (fun y ↦ β y i)
    simp only [pow_one, mul_one, hα i, hβ i, mul_zero, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hmix
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _),
      Real.sq_sqrt (expect_nonneg fun _ _ ↦ sq_nonneg _)]
    calc (𝔼 x, α x i * H.walk (fun y ↦ β y i) x) ^ 2
        ≤ H.spectralExpansion ^ 2 * (𝔼 x, α x i ^ 2) * (𝔼 y, β y i ^ 2) := hmix
      _ ≤ lam ^ 2 * (𝔼 x, α x i ^ 2) * (𝔼 y, β y i ^ 2) := by gcongr
  calc |𝔼 x, 𝔼 d, ∑ i, α x i * β (H.neighbor x d) i|
      = |∑ i, 𝔼 x, α x i * H.walk (fun y ↦ β y i) x| := by rw [hsum]
    _ ≤ ∑ i, |𝔼 x, α x i * H.walk (fun y ↦ β y i) x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, lam * Real.sqrt (𝔼 x, α x i ^ 2) * Real.sqrt (𝔼 y, β y i ^ 2) :=
        sum_le_sum fun i _ ↦ hcoord i
    _ = lam * ∑ i, Real.sqrt (𝔼 x, α x i ^ 2) * Real.sqrt (𝔼 y, β y i ^ 2) := by
        simp only [mul_assoc, ← mul_sum]
    _ ≤ lam * (Real.sqrt (∑ i, 𝔼 x, α x i ^ 2) * Real.sqrt (∑ i, 𝔼 y, β y i ^ 2)) := by
        gcongr
        exact Real.sum_sqrt_mul_sqrt_le univ (fun _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _)
          (fun _ ↦ expect_nonneg fun _ _ ↦ sq_nonneg _)
    _ = lam * Real.sqrt (𝔼 x, ∑ i, α x i ^ 2) * Real.sqrt (𝔼 y, ∑ i, β y i ^ 2) := by
        rw [expect_sum_comm, expect_sum_comm, mul_assoc]

/-! ### Explicit Power-of-Two-Degree Expander Family over `GF(256)` -/

/-- Base degree exponent for the explicit `GF(256)` affine-plane expander family:
`2 * 256 ^ 12 = 2 ^ 97`. -/
def baseExpanderDegreeExp : ℕ := 97

/-- Base spectral-gap denominator constant for `GF(256)`: the base expander has spectral expansion
at most `1 - 9 / (400 * 256 ^ 16)`. -/
def baseExpanderGapDenom : ℕ := 400 * 256 ^ 16

/-- Base spectral expansion upper bound $\mu_0 = 1 - 9 / (400 \cdot 256^{16})$. -/
noncomputable def baseExpanderMu : ℝ := 1 - 9 / (baseExpanderGapDenom : ℝ)

/-- Power exponent $t(\lambda)$ chosen so that $\mu_0^{t(\lambda)} \le \lambda$ for any
$\lambda > 0$. -/
noncomputable def expanderPowerCount (lam : ℝ) : ℕ :=
  Nat.ceil ((baseExpanderGapDenom : ℝ) / 9 * Real.log (1 / lam))

/-- Degree exponent $d(\lambda) = 97 \cdot t(\lambda)$ of the powered `GF(256)` expander family,
giving degree $2^{d(\lambda)} = (1/\lambda)^{O(1)}$. -/
noncomputable def expanderDegreeExp (lam : ℝ) : ℕ :=
  baseExpanderDegreeExp * expanderPowerCount lam

private theorem prime_two_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

@[instance_reducible]
private noncomputable def gf256Fintype : Fintype (GaloisField 2 8) :=
  have : Fact (Nat.Prime 2) := prime_two_fact
  Fintype.ofFinite (GaloisField 2 8)

private noncomputable def gf256Numbering : GaloisField 2 8 ≃ Fin 256 :=
  have : Fact (Nat.Prime 2) := prime_two_fact
  have : Fintype (GaloisField 2 8) := gf256Fintype
  have hcardK : Fintype.card (GaloisField 2 8) = 256 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 8 (by decide)]
    norm_num
  Fintype.equivFinOfCardEq hcardK

/-- The `GF(256)` base expander on `Fin n` with degree `2 ^ 97` (`BitString 97`), obtained from
`Cslib.RotationMap.affinePlaneFamily` over `GaloisField 2 8`. -/
noncomputable def baseExpanderFin (n : ℕ) : RotationMap (Fin n) (BitString baseExpanderDegreeExp) :=
  have : Fact (Nat.Prime 2) := prime_two_fact
  have : Fintype (GaloisField 2 8) := gf256Fintype
  have hcardL : Fintype.card (AffinePlaneFamilyLabel (GaloisField 2 8) 256) =
      Fintype.card (BitString baseExpanderDegreeExp) := by
    rw [card_affinePlaneFamilyLabel gf256Numbering]
    change _ = Fintype.card (Fin baseExpanderDegreeExp → Bool)
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num [baseExpanderDegreeExp]
  (affinePlaneFamily gf256Numbering (by decide) n).relabel (Fintype.equivOfCardEq hcardL)

/-- Spectral expansion bound for the base `GF(256)` expander family. -/
theorem spectralExpansion_baseExpanderFin_le (n : ℕ) :
    (baseExpanderFin n).spectralExpansion ≤ baseExpanderMu := by
  have : Fact (Nat.Prime 2) := prime_two_fact
  have : Fintype (GaloisField 2 8) := gf256Fintype
  unfold baseExpanderFin baseExpanderMu baseExpanderGapDenom
  rw [spectralExpansion_relabel]
  exact (spectralExpansion_affinePlaneFamily_le gf256Numbering (by decide) n).trans_eq (by
    norm_num)

/-- The powered `GF(256)` expander on `Fin n` with degree `2 ^ (expanderDegreeExp lam)` and
spectral expansion at most `lam` (for `lam > 0`). -/
noncomputable def powTwoExpanderFin (lam : ℝ) (n : ℕ) :
    RotationMap (Fin n) (BitString (expanderDegreeExp lam)) :=
  have hcard : Fintype.card (Fin (expanderPowerCount lam) → BitString baseExpanderDegreeExp) =
      Fintype.card (BitString (expanderDegreeExp lam)) := by
    change Fintype.card (Fin (expanderPowerCount lam) → Fin baseExpanderDegreeExp → Bool) =
      Fintype.card (Fin (expanderDegreeExp lam) → Bool)
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_mul, expanderDegreeExp]
  ((baseExpanderFin n).pow (expanderPowerCount lam)).relabel (Fintype.equivOfCardEq hcard)

/-- The powered `GF(256)` expander transported to `BitString m` via `Fintype.equivFin`. -/
noncomputable def powTwoExpanderBitString (lam : ℝ) (m : ℕ) :
    RotationMap (BitString m) (BitString (expanderDegreeExp lam)) :=
  (powTwoExpanderFin lam (2 ^ m)).reindex
    (Fintype.equivFinOfCardEq (by simp)).symm

/-- Spectral expansion bound for the powered `GF(256)` expander family on `Fin n`. -/
theorem spectralExpansion_powTwoExpanderFin_le {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    (powTwoExpanderFin lam n).spectralExpansion ≤ lam := by
  unfold powTwoExpanderFin
  rw [spectralExpansion_relabel]
  refine ((baseExpanderFin n).spectralExpansion_pow_le _).trans ?_
  have hbase_nn : 0 ≤ (baseExpanderFin n).spectralExpansion :=
    (baseExpanderFin n).spectralExpansion_nonneg
  have hmu_le : baseExpanderMu ≤ Real.exp (-(9 / (baseExpanderGapDenom : ℝ))) := by
    have h := Real.add_one_le_exp (-(9 / (baseExpanderGapDenom : ℝ)))
    unfold baseExpanderMu
    linarith
  have hmu_nn : 0 ≤ baseExpanderMu := by
    unfold baseExpanderMu baseExpanderGapDenom
    norm_num
  calc (baseExpanderFin n).spectralExpansion ^ expanderPowerCount lam
      ≤ baseExpanderMu ^ expanderPowerCount lam :=
        pow_le_pow_left₀ hbase_nn (spectralExpansion_baseExpanderFin_le n) _
    _ ≤ (Real.exp (-(9 / (baseExpanderGapDenom : ℝ)))) ^ expanderPowerCount lam :=
        pow_le_pow_left₀ hmu_nn hmu_le _
    _ = Real.exp (-((9 / (baseExpanderGapDenom : ℝ)) * (expanderPowerCount lam : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ Real.exp (-Real.log (1 / lam)) := by
        apply Real.exp_le_exp.mpr
        have hceil : (baseExpanderGapDenom : ℝ) / 9 * Real.log (1 / lam) ≤
            (expanderPowerCount lam : ℝ) := Nat.le_ceil _
        have hpos : (0 : ℝ) < 9 / (baseExpanderGapDenom : ℝ) := by
          unfold baseExpanderGapDenom; positivity
        have hmul := mul_le_mul_of_nonneg_left hceil hpos.le
        have hsimp : 9 / (baseExpanderGapDenom : ℝ) *
            ((baseExpanderGapDenom : ℝ) / 9 * Real.log (1 / lam)) = Real.log (1 / lam) := by
          have hne : (baseExpanderGapDenom : ℝ) ≠ 0 := by unfold baseExpanderGapDenom; positivity
          field_simp [hne]
        linarith
    _ = lam := by
        rw [one_div, Real.log_inv, neg_neg, Real.exp_log hlam]

/-- Spectral expansion bound for the powered `GF(256)` expander family on `BitString m`. -/
theorem spectralExpansion_powTwoExpanderBitString_le {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    (powTwoExpanderBitString lam m).spectralExpansion ≤ lam := by
  unfold powTwoExpanderBitString
  rw [spectralExpansion_reindex]
  exact spectralExpansion_powTwoExpanderFin_le hlam (2 ^ m)

/-- Explicit bound on the degree exponent $d(\lambda) = O(\log(1/\lambda) + 1)$. -/
theorem expanderDegreeExp_le {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (expanderDegreeExp lam : ℝ) ≤
      97 * ((baseExpanderGapDenom : ℝ) / 9 + 1) * (Real.log (1 / lam) + 1) := by
  have hlog_nn : 0 ≤ Real.log (1 / lam) := Real.log_nonneg ((one_le_div hlam).mpr hlam1)
  have hceil : (expanderPowerCount lam : ℝ) <
      (baseExpanderGapDenom : ℝ) / 9 * Real.log (1 / lam) + 1 :=
    Nat.ceil_lt_add_one (by unfold baseExpanderGapDenom; positivity)
  have hbound : (expanderDegreeExp lam : ℝ) = 97 * (expanderPowerCount lam : ℝ) := by
    simp [expanderDegreeExp, baseExpanderDegreeExp]
  rw [hbound]
  have h1 : (baseExpanderGapDenom : ℝ) / 9 * Real.log (1 / lam) + 1 ≤
      ((baseExpanderGapDenom : ℝ) / 9 + 1) * (Real.log (1 / lam) + 1) := by
    have hg : (0 : ℝ) ≤ (baseExpanderGapDenom : ℝ) / 9 := by
      unfold baseExpanderGapDenom; positivity
    nlinarith
  linarith

/-- **Explicit power-of-two-degree $\lambda$-expander family**: there exists a universal constant
$C > 0$ such that for every $\lambda \in (0, 1]$ and $n \in \mathbb{N}$, there is a $2^d$-regular
$\lambda$-expander on $n$ vertices with $d \le C (\log(1/\lambda) + 1)$. -/
theorem exists_pow_two_expander_family :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ), 0 < lam → lam ≤ 1 →
      ∃ d : ℕ, (d : ℝ) ≤ C * (Real.log (1 / lam) + 1) ∧
        ∀ n : ℕ, ∃ H : RotationMap (Fin n) (BitString d), H.spectralExpansion ≤ lam := by
  refine ⟨97 * ((baseExpanderGapDenom : ℝ) / 9 + 1), by unfold baseExpanderGapDenom; positivity,
    fun lam hlam hlam1 ↦ ⟨expanderDegreeExp lam, expanderDegreeExp_le hlam hlam1,
      fun n ↦ ⟨powTwoExpanderFin lam n, spectralExpansion_powTwoExpanderFin_le hlam n⟩⟩⟩

end Cslib.RotationMap
