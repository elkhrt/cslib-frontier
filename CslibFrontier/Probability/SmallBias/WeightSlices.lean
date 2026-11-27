/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.Data.BitString.Weight
public import CslibFrontier.Probability.Fooling
public import CslibFrontier.Probability.PMF.Event
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed sums, Hamming weight slices, permutation symmetrization, and coordinate-reset noise

For a Boolean vector `x : ι → Bool`, reading `false ↦ 1` and `true ↦ -1` via `BitString.signVal`
defines the *signed sum* `signedSum x = ∑ i, signVal (x i)`, which is linked to the Hamming weight
by `signedSum x = |ι| - 2 * weight x`.

This module develops three foundational operations on distributions `PMF (BitString n)` over the
Boolean cube and establishes their Fourier-bias and `k`-wise independence properties:

1. **Uniform Hamming-weight slices (`uniformWeightLayer`)**: for `w ≤ n`, the uniform distribution
   on strings of weight `w` satisfies `bias (uniformWeightLayer n w hw) Sᶜ = (-1) ^ w *
   bias (uniformWeightLayer n w hw) S`, so complementary coordinate sets have equal bias magnitude.
2. **Permutation symmetrization (`symmetrizePMF`)**: averaging `D` over a uniformly random
   coordinate permutation `π : Equiv.Perm (Fin n)` preserves `k`-wise `ε`-bias and `k`-wise
   independence while leaving the distribution of all permutation-invariant events (in particular,
   Hamming weight and signed sum) unchanged.
3. **Iterated random coordinate-reset smoothing (`coordResetStep`, `coordReset`)**: independently
   picking a uniformly random coordinate `i : Fin n` and resetting `x i` to a uniform bit `r` times
   multiplies the Fourier bias at every set `S` by `(1 - #S / n) ^ r` (`bias_coordReset`), never
   increases any bias, preserves `k`-wise independence, and changes `signedSum` on its support by at
   most `2 * r`.

## Main definitions

* `CslibFrontier.BitString.signedSum`: sum of `±1` bit signs `∑ i, signVal (x i)`.
* `CslibFrontier.BitString.uniformWeightLayer`: uniform distribution on `{x : BitString n |
  weight x = w}` for `w ≤ n`.
* `CslibFrontier.BitString.symmetrizePMF`: coordinate-permutation symmetrization of a distribution
  on `BitString n`.
* `CslibFrontier.BitString.coordResetStep`, `CslibFrontier.BitString.coordReset`: one-step and
  `r`-step random single-coordinate uniform reset operators on `BitString n`.

## Main results

* `CslibFrontier.BitString.signedSum_eq_card_sub_two_mul_weight`:
  `signedSum x = |ι| - 2 * weight x`.
* `CslibFrontier.BitString.bias_uniformWeightLayer_compl`,
  `CslibFrontier.BitString.abs_bias_uniformWeightLayer_compl`: complementary parity biases on a
  fixed Hamming slice differ by `(-1) ^ w`.
* `CslibFrontier.BitString.isKWiseSmallBias_symmetrizePMF`,
  `CslibFrontier.BitString.isKWiseIndependent_symmetrizePMF`: permutation symmetrization preserves
  `k`-wise small bias and `k`-wise independence.
* `CslibFrontier.BitString.toOuterMeasure_symmetrizePMF_of_perm_invariant`: permutation
  symmetrization preserves the probability of every permutation-invariant event.
* `CslibFrontier.BitString.bias_coordReset`: exact eigenvalue identity
  `bias (coordReset r D) S = (1 - #S / n) ^ r * bias D S`.
* `CslibFrontier.BitString.abs_bias_coordReset_le`,
  `CslibFrontier.BitString.abs_bias_coordReset_le_pow`: coordinate-reset smoothing contracts biases
  and bounds them by `(1 - #S / n) ^ r`.
* `CslibFrontier.BitString.abs_signedSum_sub_le_of_mem_support_coordReset`: `r` coordinate resets
  change `signedSum` by at most `2 * r`.
-/

public section

namespace CslibFrontier.BitString

open Finset Cslib Cslib.BitString Cslib.Probability
open scoped BigOperators ENNReal

/-! ### 1. Signed Sums on the Boolean Cube -/

/-- The signed sum `∑ i, signVal (x i)` of a Boolean vector, reading `false ↦ 1` and `true ↦ -1`. -/
def signedSum {ι : Type*} [Fintype ι] (x : ι → Bool) : ℝ :=
  ∑ i : ι, signVal (x i)

/-- The signed sum equals `|ι| - 2 * weight x`. -/
theorem signedSum_eq_card_sub_two_mul_weight {ι : Type*} [Fintype ι] (x : ι → Bool) :
    signedSum x = (Fintype.card ι : ℝ) - 2 * (weight x : ℝ) := by
  have hbit : (weight x : ℝ) = ∑ i : ι, bitVal ℝ (x i) := by
    rw [weight_eq_sum_toNat, Nat.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    cases x i <;> simp
  rw [signedSum, hbit, mul_sum]
  have hterm : ∀ i : ι, signVal (x i) = 1 - 2 * bitVal ℝ (x i) := fun i =>
    signVal_eq_one_sub_two_mul_bitVal (x i)
  simp only [hterm, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]

/-- On `BitString n`, `signedSum x = n - 2 * weight x`. -/
theorem signedSum_eq_length_sub_two_mul_weight {n : ℕ} (x : BitString n) :
    signedSum x = (n : ℝ) - 2 * (weight x : ℝ) := by
  simpa only [Fintype.card_fin] using signedSum_eq_card_sub_two_mul_weight x

/-- Bitwise negation negates the signed sum. -/
@[simp]
theorem signedSum_not {ι : Type*} [Fintype ι] (x : ι → Bool) :
    signedSum (fun i => !x i) = -signedSum x := by
  simp only [signedSum, signVal_not, sum_neg_distrib]

/-- The absolute signed sum never exceeds the number of coordinates. -/
theorem abs_signedSum_le_card {ι : Type*} [Fintype ι] (x : ι → Bool) :
    |signedSum x| ≤ (Fintype.card ι : ℝ) := by
  rw [signedSum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_signVal, sum_const, card_univ, nsmul_eq_mul, mul_one, le_rfl]

/-- Permuting coordinates preserves the signed sum. -/
theorem signedSum_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (x : ι → Bool) :
    signedSum (fun k => x (e k)) = signedSum x :=
  Fintype.sum_equiv e (fun k => signVal (x (e k))) (fun i => signVal (x i)) fun _ => rfl

/-- Updating a single coordinate changes `signedSum` by at most `2`. -/
theorem abs_signedSum_update_sub_le_two {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Bool)
    (i : ι) (b : Bool) :
    |signedSum (Function.update x i b) - signedSum x| ≤ 2 := by
  rw [signedSum, signedSum, ← sum_sub_distrib]
  have hsingle : ∑ j : ι, (signVal (Function.update x i b j) - signVal (x j)) =
      signVal b - signVal (x i) := by
    rw [sum_eq_single i]
    · simp only [Function.update_self]
    · intro j _ hji
      simp only [Function.update_of_ne hji, sub_self]
    · exact fun h => absurd (mem_univ i) h
  rw [hsingle]
  cases b <;> cases x i <;> norm_num

/-! ### 2. Uniform Hamming-Weight Slices -/

/-- The finite set of `n`-bit strings of Hamming weight `w`. -/
def weightSliceFinset (n w : ℕ) : Finset (BitString n) :=
  univ.filter fun x => weight x = w

/-- For `w ≤ n`, the weight-`w` slice of `BitString n` is nonempty. -/
theorem weightSliceFinset_nonempty {n w : ℕ} (hw : w ≤ n) :
    (weightSliceFinset n w).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hcard : #(weightSliceFinset n w) = n.choose w := by
    simpa only [weightSliceFinset, Fintype.card_fin] using card_filter_weight_eq (ι := Fin n) w
  rw [hemp, card_empty] at hcard
  exact (Nat.choose_pos hw).ne' hcard.symm

/-- The uniform distribution on `{x : BitString n | weight x = w}` for `w ≤ n`. -/
noncomputable def uniformWeightLayer (n w : ℕ) (hw : w ≤ n) : PMF (BitString n) :=
  PMF.uniformOfFinset (weightSliceFinset n w) (weightSliceFinset_nonempty hw)

/-- Every point in the support of `uniformWeightLayer n w hw` has Hamming weight `w`. -/
theorem weight_eq_of_mem_support_uniformWeightLayer {n w : ℕ} {hw : w ≤ n} {x : BitString n}
    (hx : x ∈ (uniformWeightLayer n w hw).support) : weight x = w := by
  rw [uniformWeightLayer, PMF.mem_support_uniformOfFinset_iff] at hx
  exact (mem_filter.1 hx).2

/-- Every point in the support of `uniformWeightLayer n w hw` has signed sum `n - 2 * w`. -/
theorem signedSum_eq_of_mem_support_uniformWeightLayer {n w : ℕ} {hw : w ≤ n} {x : BitString n}
    (hx : x ∈ (uniformWeightLayer n w hw).support) :
    signedSum x = (n : ℝ) - 2 * (w : ℝ) := by
  rw [signedSum_eq_length_sub_two_mul_weight, weight_eq_of_mem_support_uniformWeightLayer hx]

private theorem chi_univ_eq_neg_one_pow_weight {ι : Type*} [Fintype ι] (x : ι → Bool) :
    chi ℝ (univ : Finset ι) x = (-1 : ℝ) ^ weight x := by
  rw [chi, weight_eq_sum_toNat]
  induction (univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons a s has ih => rw [prod_cons, sum_cons, pow_add, ih]

/-- On `uniformWeightLayer n w hw`, the character of `Sᶜ` has bias `(-1) ^ w` times the bias of
`S`. -/
theorem bias_uniformWeightLayer_compl {n w : ℕ} (hw : w ≤ n) (S : Finset (Fin n)) :
    bias (uniformWeightLayer n w hw) Sᶜ =
      (-1 : ℝ) ^ w * bias (uniformWeightLayer n w hw) S := by
  rw [bias, bias, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ (uniformWeightLayer n w hw).support
  · have hw_eq : weight x = w := weight_eq_of_mem_support_uniformWeightLayer hx
    have hprod : chi ℝ S x * chi ℝ Sᶜ x = (-1 : ℝ) ^ w := by
      rw [← chi_union disjoint_compl_right, union_compl, chi_univ_eq_neg_one_pow_weight, hw_eq]
    have hsq : chi ℝ S x * chi ℝ S x = 1 := chi_mul_self S x
    have hc : chi ℝ Sᶜ x = (-1 : ℝ) ^ w * chi ℝ S x := by
      linear_combination chi ℝ S x * hprod - chi ℝ Sᶜ x * hsq
    rw [hc]
    ring
  · have hx0 : uniformWeightLayer n w hw x = 0 := by
      rwa [PMF.mem_support_iff, not_not] at hx
    simp only [hx0, ENNReal.toReal_zero, zero_mul, mul_zero]

/-- Complementary sets of coordinates have identical bias magnitude under `uniformWeightLayer`. -/
theorem abs_bias_uniformWeightLayer_compl {n w : ℕ} (hw : w ≤ n) (S : Finset (Fin n)) :
    |bias (uniformWeightLayer n w hw) Sᶜ| = |bias (uniformWeightLayer n w hw) S| := by
  rw [bias_uniformWeightLayer_compl, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-! ### 3. Coordinate-Permutation Symmetrization -/

/-- Symmetrize `D : PMF (BitString n)` by applying a uniformly random coordinate permutation
`π : Equiv.Perm (Fin n)`. -/
noncomputable def symmetrizePMF {n : ℕ} (D : PMF (BitString n)) : PMF (BitString n) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).bind fun π => D.map fun x i => x (π i)

private theorem chi_comp_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (x : BitString n) :
    chi ℝ S (fun i => x (π i)) = chi ℝ (S.map π.toEmbedding) x := by
  simp only [chi, prod_map, Equiv.coe_toEmbedding]

private theorem bias_map_perm {n : ℕ} (D : PMF (BitString n)) (π : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    bias (D.map fun x i => x (π i)) S = bias D (S.map π.toEmbedding) := by
  rw [bias_map]
  simp only [chi_comp_perm, bias]

/-- Bias of `symmetrizePMF D` at `S` is the average of `bias D (S.map π.toEmbedding)` over all
permutations `π`. -/
theorem bias_symmetrizePMF {n : ℕ} (D : PMF (BitString n)) (S : Finset (Fin n)) :
    bias (symmetrizePMF D) S =
      ∑ π : Equiv.Perm (Fin n),
        ((PMF.uniformOfFintype (Equiv.Perm (Fin n))) π).toReal *
          bias D (S.map π.toEmbedding) := by
  rw [bias, symmetrizePMF, PMF.sum_bind_mul]
  refine sum_congr rfl fun π _ => ?_
  rw [← bias, bias_map_perm]

/-- Coordinate-permutation symmetrization preserves `k`-wise `ε`-bias. -/
theorem isKWiseSmallBias_symmetrizePMF {n k : ℕ} {ε : ℝ} {D : PMF (BitString n)}
    (hD : IsKWiseSmallBias k ε D) : IsKWiseSmallBias k ε (symmetrizePMF D) := by
  intro S hS hSk
  rw [bias_symmetrizePMF]
  have hε : 0 ≤ ε :=
    (abs_nonneg _).trans (hD S hS hSk)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ π : Equiv.Perm (Fin n),
        |((PMF.uniformOfFintype (Equiv.Perm (Fin n))) π).toReal *
          bias D (S.map π.toEmbedding)|
      ≤ ∑ π : Equiv.Perm (Fin n),
          ((PMF.uniformOfFintype (Equiv.Perm (Fin n))) π).toReal * ε := by
        refine sum_le_sum fun π _ => ?_
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        exact hD (S.map π.toEmbedding) (hS.map) (by simpa only [card_map] using hSk)
    _ = ε := by
        rw [← sum_mul, PMF.sum_toReal, one_mul]

/-- Coordinate-permutation symmetrization preserves `k`-wise independence. -/
theorem isKWiseIndependent_symmetrizePMF {n k : ℕ} {D : PMF (BitString n)}
    (hD : IsKWiseIndependent k D) : IsKWiseIndependent k (symmetrizePMF D) :=
  isKWiseSmallBias_symmetrizePMF hD

/-- Any permutation-invariant event has the exact same probability under `symmetrizePMF D` as under
`D`. -/
theorem toOuterMeasure_symmetrizePMF_of_perm_invariant {n : ℕ} (D : PMF (BitString n))
    (E : Set (BitString n)) (hinv : ∀ (π : Equiv.Perm (Fin n)) (x : BitString n),
      (fun i => x (π i)) ∈ E ↔ x ∈ E) :
    (symmetrizePMF D).toOuterMeasure E = D.toOuterMeasure E := by
  classical
  rw [symmetrizePMF, PMF.toOuterMeasure_bind_apply]
  have hmap : ∀ π : Equiv.Perm (Fin n),
      (D.map fun x i => x (π i)).toOuterMeasure E = D.toOuterMeasure E := fun π => by
    rw [PMF.toOuterMeasure_map_apply]
    congr 1
    ext x
    exact hinv π x
  simp only [hmap, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### 4. Iterated Random Coordinate-Reset Smoothing -/

/-- One step of random coordinate-reset noise on `BitString n`: pick `i : Fin n` uniformly at
random and overwrite `x i` with an independent uniform bit. -/
noncomputable def coordResetStep {n : ℕ} [NeZero n] (x : BitString n) : PMF (BitString n) :=
  (PMF.uniformOfFintype (Fin n)).bind fun i =>
    (PMF.uniformOfFintype Bool).map fun b => Function.update x i b

/-- Apply `r` independent steps of random single-coordinate uniform reset to `D`. -/
noncomputable def coordReset {n : ℕ} [NeZero n] : ℕ → PMF (BitString n) → PMF (BitString n)
  | 0, D => D
  | r + 1, D => (coordReset r D).bind coordResetStep

@[simp]
theorem coordReset_zero {n : ℕ} [NeZero n] (D : PMF (BitString n)) : coordReset 0 D = D := by
  rfl

theorem coordReset_succ {n : ℕ} [NeZero n] (r : ℕ) (D : PMF (BitString n)) :
    coordReset (r + 1) D = (coordReset r D).bind coordResetStep := by
  rfl

private theorem sum_bool_chi_update {n : ℕ} (x : BitString n) (S : Finset (Fin n)) (i : Fin n) :
    ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal * chi ℝ S (Function.update x i b) =
      if i ∈ S then 0 else chi ℝ S x := by
  have hunif : ∀ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal = (1 / 2 : ℝ) := fun b => by
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, one_div]
  simp only [hunif, Fintype.sum_bool]
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    have hsplit : ∀ b : Bool,
        chi ℝ S (Function.update x i b) =
          ((-1 : ℝ) ^ b.toNat) * ∏ j ∈ S.erase i, (-1 : ℝ) ^ (x j).toNat := fun b => by
      rw [chi, ← mul_prod_erase S _ hi, Function.update_self]
      congr 1
      refine prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (mem_erase.1 hj).1]
    rw [hsplit true, hsplit false]
    simp only [Bool.toNat_true, Bool.toNat_false, pow_one, pow_zero]
    ring
  · simp only [hi, ↓reduceIte]
    have hsame : ∀ b : Bool, chi ℝ S (Function.update x i b) = chi ℝ S x := fun b => by
      simp only [chi]
      refine prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne hji]
    rw [hsame true, hsame false]
    ring

/-- One coordinate-reset step from a deterministic string `x` has bias `(1 - #S / n) * chi ℝ S x`.
-/
theorem bias_coordResetStep {n : ℕ} [NeZero n] (x : BitString n) (S : Finset (Fin n)) :
    bias (coordResetStep x) S = (1 - (#S : ℝ) / (n : ℝ)) * chi ℝ S x := by
  rw [bias, coordResetStep, PMF.sum_bind_mul]
  have hinner : ∀ i : Fin n,
      (∑ y : BitString n,
        (((PMF.uniformOfFintype Bool).map fun b => Function.update x i b) y).toReal *
          chi ℝ S y) =
        if i ∈ S then 0 else chi ℝ S x := fun i => by
    rw [PMF.sum_map_mul]
    exact sum_bool_chi_update x S i
  simp only [hinner]
  have hunif_i : ∀ i : Fin n, ((PMF.uniformOfFintype (Fin n)) i).toReal = (n : ℝ)⁻¹ := fun i => by
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
  simp only [hunif_i, ← mul_sum]
  have hcompl : (∑ i : Fin n, if i ∈ S then (0 : ℝ) else chi ℝ S x) =
      ((n : ℝ) - (#S : ℝ)) * chi ℝ S x := by
    have hfilter : (∑ i : Fin n, if i ∈ S then (0 : ℝ) else chi ℝ S x) =
        ∑ _i ∈ Sᶜ, chi ℝ S x := by
      have hite : ∀ i : Fin n,
          (if i ∈ S then (0 : ℝ) else chi ℝ S x) = if i ∈ Sᶜ then chi ℝ S x else 0 := fun i => by
        by_cases hi : i ∈ S <;> simp [hi]
      simp only [hite, ← sum_filter]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and]
    rw [hfilter, sum_const, nsmul_eq_mul, card_compl, Fintype.card_fin,
      Nat.cast_sub (card_le_univ S |> fun h => by simpa only [Fintype.card_fin] using h)]
  rw [hcompl]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  field_simp

/-- **Exact bias damping under `r` coordinate resets**: `coordReset r D` multiplies the bias at `S`
by `(1 - #S / n) ^ r`. -/
theorem bias_coordReset {n : ℕ} [NeZero n] (r : ℕ) (D : PMF (BitString n))
    (S : Finset (Fin n)) :
    bias (coordReset r D) S = (1 - (#S : ℝ) / (n : ℝ)) ^ r * bias D S := by
  induction r with
  | zero => simp only [coordReset_zero, pow_zero, one_mul]
  | succ r ih =>
    rw [coordReset_succ, bias, PMF.sum_bind_mul]
    have hstep : ∀ x : BitString n,
        (∑ y : BitString n, (coordResetStep x y).toReal * chi ℝ S y) =
          (1 - (#S : ℝ) / (n : ℝ)) * chi ℝ S x := fun x => bias_coordResetStep x S
    simp only [hstep]
    have hpull : (∑ x : BitString n,
        ((coordReset r D) x).toReal * ((1 - (#S : ℝ) / (n : ℝ)) * chi ℝ S x)) =
        (1 - (#S : ℝ) / (n : ℝ)) * bias (coordReset r D) S := by
      rw [bias, mul_sum]
      exact sum_congr rfl fun x _ => by ring
    rw [hpull, ih, pow_succ']
    ring

private theorem factor_coordReset_mem_Icc {n : ℕ} [NeZero n] (S : Finset (Fin n)) :
    0 ≤ 1 - (#S : ℝ) / (n : ℝ) ∧ 1 - (#S : ℝ) / (n : ℝ) ≤ 1 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hcard : (#S : ℝ) ≤ (n : ℝ) := by
    have hle := card_le_univ S
    simpa only [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).2 hle
  exact ⟨sub_nonneg.2 ((div_le_one hn_pos).2 hcard), sub_le_self 1 (by positivity)⟩

/-- Coordinate-reset noise never increases the magnitude of any bias. -/
theorem abs_bias_coordReset_le {n : ℕ} [NeZero n] (r : ℕ) (D : PMF (BitString n))
    (S : Finset (Fin n)) :
    |bias (coordReset r D) S| ≤ |bias D S| := by
  obtain ⟨h0, h1⟩ := factor_coordReset_mem_Icc S
  rw [bias_coordReset, abs_mul, abs_of_nonneg (pow_nonneg h0 r)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ h0 h1)

/-- `r` coordinate resets bound the bias at `S` by `(1 - #S / n) ^ r`. -/
theorem abs_bias_coordReset_le_pow {n : ℕ} [NeZero n] (r : ℕ) (D : PMF (BitString n))
    (S : Finset (Fin n)) :
    |bias (coordReset r D) S| ≤ (1 - (#S : ℝ) / (n : ℝ)) ^ r := by
  obtain ⟨h0, _⟩ := factor_coordReset_mem_Icc S
  rw [bias_coordReset, abs_mul, abs_of_nonneg (pow_nonneg h0 r)]
  exact mul_le_of_le_one_right (pow_nonneg h0 r) (abs_bias_le_one D S)

/-- Coordinate-reset smoothing preserves `k`-wise independence. -/
theorem isKWiseIndependent_coordReset {n k : ℕ} [NeZero n] (r : ℕ) {D : PMF (BitString n)}
    (hD : IsKWiseIndependent k D) : IsKWiseIndependent k (coordReset r D) := by
  intro S hS hSk
  exact (abs_bias_coordReset_le r D S).trans (hD S hS hSk)

/-- Every outcome in the support of `coordReset r D` differs in `signedSum` by at most `2 * r` from
some outcome in the support of `D`. -/
theorem exists_mem_support_abs_signedSum_sub_le_coordReset {n : ℕ} [NeZero n] :
    ∀ (r : ℕ) (D : PMF (BitString n)) {y : BitString n},
      y ∈ (coordReset r D).support →
        ∃ x ∈ D.support, |signedSum y - signedSum x| ≤ 2 * (r : ℝ)
  | 0, D, y, hy => ⟨y, hy, by simp⟩
  | r + 1, D, y, hy => by
    rw [coordReset_succ, PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rw [coordResetStep, PMF.mem_support_bind_iff] at hyz
    obtain ⟨i, _, hyb⟩ := hyz
    rw [PMF.mem_support_map_iff] at hyb
    obtain ⟨b, _, rfl⟩ := hyb
    obtain ⟨x, hx, hzx⟩ := exists_mem_support_abs_signedSum_sub_le_coordReset r D hz
    refine ⟨x, hx, ?_⟩
    have hstep := abs_signedSum_update_sub_le_two z i b
    have htri := abs_sub_le (signedSum (Function.update z i b)) (signedSum z) (signedSum x)
    push_cast
    linarith

/-- Starting from a point mass `PMF.pure x`, every outcome in `(coordReset r (PMF.pure x)).support`
satisfies `|signedSum y - signedSum x| ≤ 2 * r`. -/
theorem abs_signedSum_sub_le_of_mem_support_coordReset {n : ℕ} [NeZero n] (r : ℕ)
    (x : BitString n) {y : BitString n}
    (hy : y ∈ (coordReset r (PMF.pure x)).support) :
    |signedSum y - signedSum x| ≤ 2 * (r : ℝ) := by
  obtain ⟨x', hx', hle⟩ := exists_mem_support_abs_signedSum_sub_le_coordReset r (PMF.pure x) hy
  rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
  rwa [hx'] at hle

end CslibFrontier.BitString
