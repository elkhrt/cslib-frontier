/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cslib.Probability.PMF
public import CslibFrontier.Foundations.Data.Code.Interleaved
public import Mathlib.InformationTheory.Hamming

import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tensor-Structured Interleaved Proximity Gap and Uniform Hitting Bounds

Under standard Lean axioms, this module extends `CslibFrontier.Foundations.Data.Code.Interleaved`
with two characteristic-independent coding-theoretic and probabilistic bounds for tensor-structured
random linear combinations over arbitrary linear codes:

1. **Multilinear tensor-basis interleaved proximity gap (`tensor_eqVec_proximity_gap`,
   `tensor_eqVec_proximity_gap_pad`)**: for any linear code `C : Submodule F (Fin ℓ → F)` with
   `3 * e < Cslib.Code.minDist C`, if a column-indexed matrix `U : Fin ℓ → Fin (2 ^ μ) → F` (or
   more generally `Fin ℓ → Fin s → F` with `s ≤ 2 ^ μ`) lies at column-Hamming distance strictly
   greater than `e` from `Cslib.Code.interleavedLinear _ C`, then a uniformly random tensor-product
   combination `j ↦ ∑ i, eqVec z i * U j i` with `z : Fin μ → F` lands within Hamming distance `e`
   of `C` with probability at most `μ * (e + 1) / |F|`.
2. **Independent uniform hitting-set sample bound (`exists_sample_count_miss_prob_le`)**: for any
   density threshold `p > 0` and target failure probability `B > 0`, `q = ⌈1 / (p * B)⌉ + 1`
   independent uniform samples miss every subset of relative density at least `p` with probability
   at most `B`.

## Main definitions

* `CslibFrontier.Code.eqVec`: MSB-first multilinear indicator basis vector over `Fin (2 ^ μ)`.

## Main results

* `CslibFrontier.Code.exists_correlatedAgreement_module`: correlated agreement over arbitrary
  linear codes on a module alphabet within the `d / 3` radius.
* `CslibFrontier.Code.tensor_eqVec_proximity_gap`,
  `CslibFrontier.Code.tensor_eqVec_proximity_gap_pad`: tensor-structured interleaved proximity gap
  for `2 ^ μ`-row and zero-padded `s`-row matrices.
* `CslibFrontier.Code.exists_sample_count_miss_prob_le`: uniform hitting-set sample complexity.
-/

public section

open scoped BigOperators ENNReal
open Cslib.Probability

namespace CslibFrontier.Code

universe u

private def splitLeft {F : Type u} {μ : ℕ} (v : Fin (2 ^ (μ + 1)) → F) : Fin (2 ^ μ) → F :=
  fun i ↦ v ⟨i.val, by have := pow_succ 2 μ; omega⟩

private def splitRight {F : Type u} {μ : ℕ} (v : Fin (2 ^ (μ + 1)) → F) : Fin (2 ^ μ) → F :=
  fun i ↦ v ⟨2 ^ μ + i.val, by have := pow_succ 2 μ; omega⟩

private def joinHalves {F : Type u} {μ : ℕ} (u v : Fin (2 ^ μ) → F) : Fin (2 ^ (μ + 1)) → F :=
  fun idx ↦
    if h : idx.val < 2 ^ μ then u ⟨idx.val, h⟩
    else v ⟨idx.val - 2 ^ μ, by have := pow_succ 2 μ; have := idx.isLt; omega⟩

private lemma joinHalves_split {F : Type u} {μ : ℕ} (v : Fin (2 ^ (μ + 1)) → F) :
    joinHalves (splitLeft v) (splitRight v) = v := by
  funext idx
  by_cases h : idx.val < 2 ^ μ
  · simp [joinHalves, splitLeft, h]
  · simp only [joinHalves, splitRight, h, ↓reduceDIte]
    congr 1; ext; dsimp; omega

private def foldMsg {F : Type u} [CommRing F] {μ : ℕ} (α : F)
    (v : Fin (2 ^ (μ + 1)) → F) : Fin (2 ^ μ) → F :=
  fun i ↦ (1 - α) * splitLeft v i + α * splitRight v i

/-- MSB-first multilinear indicator basis vector `eq(z, ·) : Fin (2 ^ μ) → F`. -/
@[expose]
def eqVec {F : Type u} [CommRing F] : {μ : ℕ} → (Fin μ → F) → Fin (2 ^ μ) → F
  | 0, _, _ => 1
  | μ + 1, z, idx =>
    if h : idx.val < 2 ^ μ then
      (1 - z 0) * eqVec (z ∘ Fin.succ) ⟨idx.val, h⟩
    else
      z 0 * eqVec (z ∘ Fin.succ)
        ⟨idx.val - 2 ^ μ, by have := pow_succ 2 μ; have := idx.isLt; omega⟩

private lemma sum_fin_pow_succ {μ : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin (2 ^ (μ + 1)) → M) :
    (∑ idx : Fin (2 ^ (μ + 1)), f idx) =
      (∑ i : Fin (2 ^ μ), f ⟨i.val, by have := pow_succ 2 μ; omega⟩) +
      (∑ i : Fin (2 ^ μ), f ⟨2 ^ μ + i.val, by have := pow_succ 2 μ; omega⟩) := by
  have h2 : 2 ^ (μ + 1) = 2 ^ μ + 2 ^ μ := by rw [pow_succ]; omega
  have heq : (∑ idx : Fin (2 ^ (μ + 1)), f idx) =
      ∑ idx : Fin (2 ^ μ + 2 ^ μ), f (Fin.cast h2.symm idx) :=
    Fintype.sum_equiv (Fin.castOrderIso h2).toEquiv _ _ fun _ ↦ rfl
  rw [heq, Fin.sum_univ_add]
  congr 1

private lemma sum_eqVec_succ {F : Type u} [CommRing F] {μ : ℕ}
    (v : Fin (2 ^ (μ + 1)) → F) (z : Fin (μ + 1) → F) :
    (∑ i : Fin (2 ^ (μ + 1)), eqVec z i * v i) =
      ∑ i : Fin (2 ^ μ), eqVec (z ∘ Fin.succ) i * foldMsg (z 0) v i := by
  rw [sum_fin_pow_succ]
  have hL : ∀ i : Fin (2 ^ μ),
      eqVec z ⟨i.val, by have := pow_succ 2 μ; omega⟩ *
          v ⟨i.val, by have := pow_succ 2 μ; omega⟩ =
        eqVec (z ∘ Fin.succ) i * ((1 - z 0) * splitLeft v i) := fun i ↦ by
    simp only [eqVec, i.isLt, ↓reduceDIte, splitLeft]; ring
  have hR : ∀ i : Fin (2 ^ μ),
      eqVec z ⟨2 ^ μ + i.val, by have := pow_succ 2 μ; omega⟩ *
          v ⟨2 ^ μ + i.val, by have := pow_succ 2 μ; omega⟩ =
        eqVec (z ∘ Fin.succ) i * (z 0 * splitRight v i) := fun i ↦ by
    have hnot : ¬ (2 ^ μ + i.val < 2 ^ μ) := by omega
    simp only [eqVec, hnot, ↓reduceDIte, splitRight]
    have hsub : (⟨2 ^ μ + i.val - 2 ^ μ, by omega⟩ : Fin (2 ^ μ)) = i := by ext; simp
    rw [hsub]; ring
  simp_rw [hL, hR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [foldMsg]; ring

/-- Correlated agreement over an arbitrary linear code `C : Submodule F (ι → M)` within the `d / 3`
unique-decoding regime (`3 * e < minDist C`): if more than `e + 1` points on the affine line
`u₀ + z • u₁` lie within Hamming distance `e` of `C`, then `u₀` and `u₁` agree simultaneously with
codewords `v₀, v₁ ∈ C` on at least `|ι| - e` coordinates. -/
theorem exists_correlatedAgreement_module {F ι M : Type*} [Field F] [Fintype ι]
    [AddCommGroup M] [Module F M] [DecidableEq M] {C : Submodule F (ι → M)} {e : ℕ}
    (hmin : 3 * (e : ℕ∞) < Cslib.Code.minDist (C : Set (ι → M)))
    (u₀ u₁ : ι → M) (S : Finset F) (hS : e + 1 < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ C, hammingDist (u₀ + z • u₁) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  classical
  obtain ⟨z₀, hz₀, z₁, hz₁, hz_ne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  obtain ⟨c₀, hc₀, hd₀⟩ := hclose z₀ hz₀
  obtain ⟨c₁, hc₁, hd₁⟩ := hclose z₁ hz₁
  have hsub_ne : z₁ - z₀ ≠ 0 := sub_ne_zero.2 hz_ne.symm
  let v₁ : ι → M := (z₁ - z₀)⁻¹ • (c₁ - c₀)
  let v₀ : ι → M := c₀ - z₀ • v₁
  have hv₁ : v₁ ∈ C := C.smul_mem _ (C.sub_mem hc₁ hc₀)
  have hv₀ : v₀ ∈ C := C.sub_mem hc₀ (C.smul_mem _ hv₁)
  have hv_z₀ : v₀ + z₀ • v₁ = c₀ := sub_add_cancel c₀ (z₀ • v₁)
  have hv_z₁ : v₀ + z₁ • v₁ = c₁ := by
    have h1 : (z₁ - z₀) • v₁ = c₁ - c₀ := by
      dsimp only [v₁]
      rw [smul_smul, mul_inv_cancel₀ hsub_ne, one_smul]
    calc v₀ + z₁ • v₁ = c₀ + (z₁ - z₀) • v₁ := by
          rw [sub_smul]; dsimp only [v₀]; abel
      _ = c₀ + (c₁ - c₀) := by rw [h1]
      _ = c₁ := add_sub_cancel c₀ c₁
  let η₀ : ι → M := u₀ - v₀
  let η₁ : ι → M := u₁ - v₁
  let B : Finset ι := Finset.univ.filter fun i ↦ η₀ i ≠ 0 ∨ η₁ i ≠ 0
  have hdiff (z : F) (i : ι) : (u₀ + z • u₁) i - (v₀ + z • v₁) i = η₀ i + z • η₁ i := by
    simp only [η₀, η₁, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_sub]
    abel
  have hnot_mem {i : ι} {za zb : F} (hne : za ≠ zb) (ha : η₀ i + za • η₁ i = 0)
      (hb : η₀ i + zb • η₁ i = 0) : i ∉ B := by
    have hdiff_smul : (za - zb) • η₁ i = 0 := by
      rw [sub_smul]
      have h1 : (η₀ i + za • η₁ i) - (η₀ i + zb • η₁ i) = 0 := by rw [ha, hb, sub_self]
      simpa only [add_sub_add_left_eq_sub] using h1
    have hη₁ : η₁ i = 0 := (smul_eq_zero.mp hdiff_smul).resolve_left (sub_ne_zero.2 hne)
    have hη₀ : η₀ i = 0 := by simpa only [hη₁, smul_zero, add_zero] using ha
    simp [B, hη₀, hη₁]
  have hB_sub : B ⊆ (Finset.univ.filter fun i ↦ (u₀ + z₀ • u₁) i ≠ c₀ i) ∪
      (Finset.univ.filter fun i ↦ (u₀ + z₁ • u₁) i ≠ c₁ i) := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra! hboth
    exact hnot_mem hz_ne (by rw [← hdiff, hv_z₀, hboth.1, sub_self])
      (by rw [← hdiff, hv_z₁, hboth.2, sub_self]) hi
  have hB_le : B.card ≤ 2 * e := by
    have hcard := (Finset.card_le_card hB_sub).trans (Finset.card_union_le _ _)
    change B.card ≤ hammingDist (u₀ + z₀ • u₁) c₀ + hammingDist (u₀ + z₁ • u₁) c₁ at hcard
    omega
  have hdist_v (z : F) (hz : z ∈ S) : hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ e := by
    obtain ⟨cz, hcz, hdz⟩ := hclose z hz
    have hle_B : hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ B.card := by
      refine Finset.card_le_card fun i hi ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hi ⊢
      by_contra! h0
      exact hi (by rw [← sub_eq_zero, hdiff z i, h0.1, h0.2, smul_zero, add_zero])
    have htri := hammingDist_triangle cz (u₀ + z • u₁) (v₀ + z • v₁)
    rw [hammingDist_comm cz (u₀ + z • u₁)] at htri
    have hceq : cz = v₀ + z • v₁ := by
      by_contra hne
      exact hmin.not_ge
        ((Cslib.Code.minDist_le_hammingDist hcz (C.add_mem hv₀ (C.smul_mem z hv₁)) hne).trans
          (by exact_mod_cast (by omega : hammingDist cz (v₀ + z • v₁) ≤ 3 * e)))
    rwa [← hceq]
  have hzero_ge (z : F) (hz : z ∈ S) :
      B.card - e ≤ (B.filter fun i ↦ η₀ i + z • η₁ i = 0).card := by
    have hpart := Finset.card_filter_add_card_filter_not (s := B) (fun i ↦ η₀ i + z • η₁ i = 0)
    have hle : (B.filter fun i ↦ ¬ (η₀ i + z • η₁ i = 0)).card ≤
        hammingDist (u₀ + z • u₁) (v₀ + z • v₁) :=
      Finset.card_le_card fun i hi ↦ Finset.mem_filter.2 ⟨Finset.mem_univ i, fun h ↦
        (Finset.mem_filter.1 hi).2 (by rw [← hdiff z i, h, sub_self])⟩
    have := hdist_v z hz
    omega
  have hroot_le (i : ι) (hi : i ∈ B) :
      (S.filter fun z ↦ η₀ i + z • η₁ i = 0).card ≤ 1 :=
    Finset.card_le_one.2 fun za hza zb hzb ↦ of_not_not fun hne ↦
      hnot_mem hne (Finset.mem_filter.1 hza).2 (Finset.mem_filter.1 hzb).2 hi
  have hsum_bound : S.card * (B.card - e) ≤ B.card := by
    have h1 := Finset.card_nsmul_le_sum S _ _ hzero_ge
    have h2 := Finset.sum_le_card_nsmul B _ 1 hroot_le
    simp only [smul_eq_mul, mul_one, Finset.card_filter] at h1 h2
    exact h1.trans (Finset.sum_comm.trans_le h2)
  have hB_le_e : B.card ≤ e := by
    by_contra! hgt
    have hpos : 1 ≤ B.card - e := Nat.sub_pos_of_lt hgt
    nlinarith only [hS, hsum_bound, hpos, Nat.sub_add_cancel hgt.le]
  refine ⟨Bᶜ, by rw [Finset.card_compl]; omega, v₀, hv₀, v₁, hv₁, fun i hi ↦ ?_⟩
  simp only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_or, ne_eq,
    not_not] at hi
  exact ⟨sub_eq_zero.1 hi.1, sub_eq_zero.1 hi.2⟩

/-- **Tensor-structured `eqVec` interleaved proximity gap**: for any linear code
`C : Submodule F (Fin ℓ → F)` with `3 * e < minDist C`, if `U : Fin ℓ → Fin (2 ^ μ) → F` has
column-Hamming distance strictly greater than `e` from `interleavedLinear (Fin (2 ^ μ)) C`, then
over uniform `z : Fin μ → F`, the tensor linear combination `j ↦ ∑ i, eqVec z i * U j i` lands
within Hamming distance `e` of `C` with probability at most `(μ * (e + 1)) / |F|`. -/
theorem tensor_eqVec_proximity_gap {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ℓ e : ℕ} {C : Submodule F (Fin ℓ → F)}
    (hmin : 3 * (e : ℕ∞) < Cslib.Code.minDist (C : Set (Fin ℓ → F))) :
    ∀ {μ : ℕ} (U : Fin ℓ → Fin (2 ^ μ) → F),
      (∀ V ∈ Cslib.Code.interleavedLinear (Fin (2 ^ μ)) C, e < hammingDist U V) →
      (PMF.uniformOfFintype (Fin μ → F)).toOuterMeasure
        {z | ∃ cw ∈ C, hammingDist (fun j ↦ ∑ i : Fin (2 ^ μ), eqVec z i * U j i) cw ≤ e} ≤
        ((μ * (e + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
  | 0, U, hfar => by
    have hemp : {z : Fin 0 → F |
        ∃ cw ∈ C, hammingDist (fun j ↦ ∑ i : Fin (2 ^ 0), eqVec z i * U j i) cw ≤ e} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
      intro cw hcw
      let V : Fin ℓ → Fin (2 ^ 0) → F := fun j _ ↦ cw j
      have hV : V ∈ Cslib.Code.interleavedLinear (Fin (2 ^ 0)) C :=
        Cslib.Code.mem_interleavedLinear.mpr fun _ ↦ hcw
      have hhd : hammingDist U V =
          hammingDist (fun j ↦ ∑ i : Fin (2 ^ 0), eqVec z i * U j i) cw := by
        unfold hammingDist
        congr 1; ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, V, ne_eq, not_iff_not]
        constructor
        · intro h; simpa [eqVec] using congrFun h 0
        · intro h; funext i
          have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
          subst hi; simpa [eqVec] using h
      rw [← hhd]; exact hfar V hV
    rw [hemp]; simp
  | μ + 1, U, hfar => by
    classical
    let UL : Fin ℓ → Fin (2 ^ μ) → F := fun j i ↦ splitLeft (U j) i
    let UR : Fin ℓ → Fin (2 ^ μ) → F := fun j i ↦ splitRight (U j) i
    let Cinter := Cslib.Code.interleavedLinear (Fin (2 ^ μ)) C
    have hmin_inter : 3 * (e : ℕ∞) <
        Cslib.Code.minDist (Cinter : Set (Fin ℓ → Fin (2 ^ μ) → F)) := by
      have : Nonempty (Fin (2 ^ μ)) := ⟨⟨0, by positivity⟩⟩
      simpa only [Cinter, Cslib.Code.minDist_interleavedLinear] using hmin
    let Bad0 (z₀ : F) : Prop :=
      ∃ V ∈ Cinter, hammingDist (UL + z₀ • (UR - UL)) V ≤ e
    let S : Finset F := Finset.univ.filter fun z₀ : F ↦ Bad0 z₀
    have hBad0_card : S.card ≤ e + 1 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨D', hD'_card, V₀, hV₀, V₁, hV₁, hag⟩ :=
        exists_correlatedAgreement_module hmin_inter UL (UR - UL)
          S hgt (fun z₀ hz₀ ↦ (Finset.mem_filter.mp hz₀).2)
      let Vfull : Fin ℓ → Fin (2 ^ (μ + 1)) → F := fun j ↦ joinHalves (V₀ j) ((V₀ + V₁) j)
      have hV₀' := Cslib.Code.mem_interleavedLinear.mp hV₀
      have hV01' := Cslib.Code.mem_interleavedLinear.mp (Cinter.add_mem hV₀ hV₁)
      have hVfull_mem : Vfull ∈ Cslib.Code.interleavedLinear (Fin (2 ^ (μ + 1))) C := by
        refine Cslib.Code.mem_interleavedLinear.mpr fun i ↦ ?_
        by_cases hi : i.val < 2 ^ μ
        · have heq : (fun j ↦ Vfull j i) = fun j ↦ V₀ j ⟨i.val, hi⟩ := by
            funext j; simp [Vfull, joinHalves, hi]
          rw [heq]; exact hV₀' ⟨i.val, hi⟩
        · have heq : (fun j ↦ Vfull j i) = fun j ↦ (V₀ + V₁) j
              ⟨i.val - 2 ^ μ, by have := pow_succ 2 μ; have := i.isLt; omega⟩ := by
            funext j; simp [Vfull, joinHalves, hi]
          rw [heq]; exact hV01' _
      have hsub : (Finset.univ.filter fun j : Fin ℓ ↦ U j ≠ Vfull j) ⊆ D'ᶜ := by
        intro j hj
        rw [Finset.mem_compl]
        intro hmem
        obtain ⟨h0, h1⟩ := hag j hmem
        have hUR_eq : UR j = (V₀ + V₁) j := by
          have hsum : UL j + (UR - UL) j = (V₀ + V₁) j := by rw [Pi.add_apply, h0, h1]
          simpa [Pi.sub_apply] using hsum
        have hUj : U j = Vfull j := by
          rw [← joinHalves_split (U j)]
          change joinHalves (UL j) (UR j) = joinHalves (V₀ j) ((V₀ + V₁) j)
          rw [h0, hUR_eq]
        exact (Finset.mem_filter.mp hj).2 hUj
      have hhd_le : hammingDist U Vfull ≤ e := by
        have hcompl : D'ᶜ.card ≤ e := by
          have := Finset.card_add_card_compl D'
          simp only [Fintype.card_fin] at this hD'_card
          omega
        exact (Finset.card_le_card hsub).trans hcompl
      exact Nat.not_lt.mpr hhd_le (hfar Vfull hVfull_mem)
    have hBad0_prob : (PMF.uniformOfFintype F).toOuterMeasure {z₀ | Bad0 z₀} ≤
        ((e + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
      refine Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div
        (Fintype.card_pos (α := F)) ?_
      simpa [mul_comm] using Nat.mul_le_mul_left (Fintype.card F) hBad0_card
    let splitE : (Fin (μ + 1) → F) ≃ F × (Fin μ → F) :=
      { toFun := fun z ↦ (z 0, z ∘ Fin.succ)
        invFun := fun p ↦ Fin.cons p.1 p.2
        left_inv := fun z ↦ by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
        right_inv := fun ⟨z0, zr⟩ ↦ by ext <;> simp }
    refine (Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_cond_le splitE
      (fun z₀ ↦ ¬ Bad0 z₀) _
      (p_top := ((e + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      (p_bot := ((μ * (e + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ?_ ?_).trans ?_
    · simpa only [not_not] using hBad0_prob
    · intro z₀ hgood0
      have hfar0 : ∀ V ∈ Cinter, e < hammingDist (UL + z₀ • (UR - UL)) V := by
        intro V hV
        by_contra hle
        exact hgood0 ⟨V, hV, Nat.le_of_not_lt hle⟩
      have ih := tensor_eqVec_proximity_gap hmin (UL + z₀ • (UR - UL)) hfar0
      have hEqSet : {zr : Fin μ → F | ∃ cw ∈ C,
          hammingDist (fun j ↦ ∑ i : Fin (2 ^ (μ + 1)),
            eqVec (splitE.symm (z₀, zr)) i * U j i) cw ≤ e} =
          {zr : Fin μ → F | ∃ cw ∈ C,
            hammingDist (fun j ↦ ∑ i : Fin (2 ^ μ),
              eqVec zr i * (UL + z₀ • (UR - UL)) j i) cw ≤ e} := by
        ext zr
        have hfun : (fun j ↦ ∑ i : Fin (2 ^ (μ + 1)),
            eqVec (Fin.cons z₀ zr) i * U j i) =
            fun j ↦ ∑ i : Fin (2 ^ μ), eqVec zr i * (UL + z₀ • (UR - UL)) j i := by
          funext j
          rw [sum_eqVec_succ]
          have hcons : Fin.cons z₀ zr ∘ Fin.succ = zr := by funext k; simp
          rw [Fin.cons_zero, hcons]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [UL, UR, foldMsg, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          ring
        simp only [Set.mem_ofPred_eq, splitE, Equiv.coe_fn_symm_mk, hfun]
      rw [hEqSet]; exact ih
    · rw [← ENNReal.add_div, ← Nat.cast_add]
      refine le_of_eq ?_; congr 2; ring

/-- Zero-padded corollary of `tensor_eqVec_proximity_gap` for arbitrary `s ≤ 2 ^ μ` rows. -/
theorem tensor_eqVec_proximity_gap_pad {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ℓ s μ e : ℕ} (hs : s ≤ 2 ^ μ) {C : Submodule F (Fin ℓ → F)}
    (hmin : 3 * (e : ℕ∞) < Cslib.Code.minDist (C : Set (Fin ℓ → F)))
    (U : Fin ℓ → Fin s → F)
    (hfar : ∀ V ∈ Cslib.Code.interleavedLinear (Fin s) C, e < hammingDist U V) :
    (PMF.uniformOfFintype (Fin μ → F)).toOuterMeasure
      {z | ∃ cw ∈ C, hammingDist (fun j ↦
        ∑ i : Fin s, eqVec z ⟨i.val, lt_of_lt_of_le i.isLt hs⟩ * U j i) cw ≤ e} ≤
      ((μ * (e + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  let Upad : Fin ℓ → Fin (2 ^ μ) → F := fun j i ↦
    if hi : i.val < s then U j ⟨i.val, hi⟩ else 0
  have hfarPad : ∀ V ∈ Cslib.Code.interleavedLinear (Fin (2 ^ μ)) C, e < hammingDist Upad V := by
    intro V hV
    let Vres : Fin ℓ → Fin s → F := fun j i ↦ V j ⟨i.val, lt_of_lt_of_le i.isLt hs⟩
    have hVres : Vres ∈ Cslib.Code.interleavedLinear (Fin s) C :=
      Cslib.Code.mem_interleavedLinear.mpr fun i ↦
        (Cslib.Code.mem_interleavedLinear.mp hV) ⟨i.val, lt_of_lt_of_le i.isLt hs⟩
    have hle : hammingDist U Vres ≤ hammingDist Upad V := by
      refine Finset.card_le_card fun j hj ↦ ?_
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, fun hEq ↦ hj.2 (funext fun i ↦ ?_)⟩
      have hi := congrFun hEq ⟨i.val, lt_of_lt_of_le i.isLt hs⟩
      simpa [Upad, Vres, i.isLt] using hi
    exact lt_of_lt_of_le (hfar Vres hVres) hle
  have hsum_eq : ∀ (z : Fin μ → F) (j : Fin ℓ),
      (∑ i : Fin (2 ^ μ), eqVec z i * Upad j i) =
        ∑ i : Fin s, eqVec z ⟨i.val, lt_of_lt_of_le i.isLt hs⟩ * U j i := by
    intro z j
    rw [← Finset.sum_subset (s₁ := Finset.univ.filter fun i : Fin (2 ^ μ) ↦ i.val < s)
      (Finset.subset_univ _)]
    · refine Finset.sum_bij (fun i hi ↦ ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
        (fun _ _ ↦ Finset.mem_univ _)
        (fun a _ b _ h ↦ Fin.ext (congrArg (Fin.val (n := s)) h))
        (fun i _ ↦ ⟨⟨i.val, lt_of_lt_of_le i.isLt hs⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩)
        (fun i hi ↦ by
          have hlt := (Finset.mem_filter.mp hi).2
          simp [Upad, hlt])
    · intro i _ hi
      have hnot : ¬ i.val < s := by simpa using hi
      simp [Upad, hnot]
  simpa only [hsum_eq] using tensor_eqVec_proximity_gap hmin Upad hfarPad

/-- **Independent uniform hitting-set sample bound**: for any `p > 0` and `B > 0`, choosing
`q = ⌈1 / (p * B)⌉ + 1` ensures that for every `ℓ ≥ 1` and every `S : Finset (Fin ℓ)` with
`p * ℓ ≤ S.card`, `q` independent uniform samples all miss `S` with probability at most `B`. -/
theorem exists_sample_count_miss_prob_le {p B : ℝ} (hp : 0 < p) (hB : 0 < B) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ {ℓ : ℕ} [NeZero ℓ] (S : Finset (Fin ℓ)),
      p * (ℓ : ℝ) ≤ (S.card : ℝ) →
      (PMF.uniformOfFintype (Fin q → Fin ℓ)).toOuterMeasure {J | ∀ r : Fin q, J r ∉ S} ≤
        ENNReal.ofReal B := by
  let q : ℕ := Nat.ceil (1 / (p * B)) + 1
  refine ⟨q, by omega, fun {ℓ} _ S hcard ↦ ?_⟩
  classical
  have hℓ : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)
  let missFinset : Finset (Fin q → Fin ℓ) := Fintype.piFinset fun _ : Fin q ↦ Sᶜ
  have hsub : {J : Fin q → Fin ℓ | ∀ r : Fin q, J r ∉ S} ⊆ (missFinset : Set (Fin q → Fin ℓ)) := by
    intro J hJ
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro r
    exact Finset.mem_compl.mpr (hJ r)
  have hdens_le : (missFinset.dens : ℝ) ≤ B := by
    have hdens_eq : (missFinset.dens : ℝ) = (Sᶜ.card : ℝ) ^ q / (ℓ : ℝ) ^ q := by
      simp [Finset.dens_eq_card_div_card, missFinset]
    rw [hdens_eq, ← div_pow]
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    have hcompl_le : (Sᶜ.card : ℝ) ≤ (1 - p) * (ℓ : ℝ) := by
      have hadd_nat : S.card + Sᶜ.card = ℓ := by simp [Fintype.card_fin]
      have hadd : (S.card : ℝ) + (Sᶜ.card : ℝ) = (ℓ : ℝ) := by exact_mod_cast hadd_nat
      linarith
    have hratio_le : (Sᶜ.card : ℝ) / (ℓ : ℝ) ≤ Real.exp (-p) := by
      calc (Sᶜ.card : ℝ) / (ℓ : ℝ) ≤ ((1 - p) * (ℓ : ℝ)) / (ℓ : ℝ) :=
            div_le_div_of_nonneg_right hcompl_le hℓ_pos.le
        _ = 1 - p := by field_simp [hℓ_pos.ne']
        _ ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    have hratio_nn : 0 ≤ (Sᶜ.card : ℝ) / (ℓ : ℝ) := by positivity
    have hq_gt : 1 / (p * B) < (q : ℝ) := by
      have hceil : 1 / (p * B) ≤ (Nat.ceil (1 / (p * B)) : ℝ) := Nat.le_ceil _
      have hq_cast : (q : ℝ) = (Nat.ceil (1 / (p * B)) : ℝ) + 1 := by simp [q]
      linarith
    have hpq_gt : 1 / B < p * (q : ℝ) := by
      have h1 : 1 / (p * B) * p < (q : ℝ) * p := mul_lt_mul_of_pos_right hq_gt hp
      have h2 : 1 / (p * B) * p = 1 / B := by field_simp [hp.ne', hB.ne']
      linarith
    calc ((Sᶜ.card : ℝ) / (ℓ : ℝ)) ^ q
        ≤ (Real.exp (-p)) ^ q := pow_le_pow_left₀ hratio_nn hratio_le q
      _ = Real.exp (-(p * (q : ℝ))) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = (Real.exp (p * (q : ℝ)))⁻¹ := Real.exp_neg _
      _ ≤ (1 + p * (q : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (p * (q : ℝ))])
      _ ≤ B := by
          rw [inv_le_comm₀ (by positivity) hB]
          have : 1 / B = B⁻¹ := one_div B
          linarith
  exact Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_dens_le _ missFinset
    hsub hdens_le

end CslibFrontier.Code
