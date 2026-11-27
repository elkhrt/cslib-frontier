/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Extractor.Basic
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Seeded randomness dispersers and Radhakrishnan–Ta-Shma bounds

A *`(K, ε)`-disperser* `disp : Input → Seed → Output` is the one-sided (support) analogue of a
seeded randomness extractor: for every input subset `A` of cardinality at least `K`, its image
`dispSupport disp A` across all seeds covers strictly more than a `1 - ε` fraction of `Output`
(`CslibFrontier.Probability.IsDisperser`). It is *strong* if the seed-output pairs `(s, disp x s)`
cover strictly more than a `1 - ε` fraction of `Seed × Output`
(`CslibFrontier.Probability.IsStrongDisperser`) [Sipser],
[Nisan, Ta-Shma], [Radhakrishnan, Ta-Shma],
.

This module establishes the foundational relationship between seeded extractors, seeded dispersers,
and one-sided (RP) hitting amplification, together with the quantitative seed-degree bounds of
Radhakrishnan and Ta-Shma:

* **Extractor-to-disperser bridge** (`card_dispSupport_ge_of_isExtractor`,
  `isDisperser_of_isExtractor`, `isStrongDisperser_of_isStrongExtractor`): every `(k, ε)`-extractor
  reaches at least `(1 - ε) |Output|` outputs on every nonempty set of size `≥ 2^k`, and is
  therefore a `(K, ε')`-disperser for every `K ≥ max 1 ⌈2^k⌉` and `ε' > ε` (and analogously for
  strong extractors).
* **Duality with one-sided error confinement and RP hitting**
  (`isDisperser_iff_card_trappedInputs_lt`, `isDisperser_iff_card_missed_lt`): `disp` is a
  `(K, ε)`-disperser if and only if every target set `T` of size at most `(1 - ε) |Output|` confines
  strictly fewer than `K` inputs — equivalently, every witness set `W` of size at least
  `ε |Output|` is completely missed by strictly fewer than `K` inputs.
* **Seed-size and seedless impossibility** (`not_isDisperser_of_card_seed_le`,
  `not_isDisperser_of_subsingleton_seed`): no function with `K |Seed| ≤ (1 - ε) |Output|` (in
  particular, with a subsingleton seed and `K ≤ (1 - ε) |Output|`) can be a `(K, ε)`-disperser.
* **Radhakrishnan–Ta-Shma seed-degree lower bound** (`IsDisperser.log_div_lt_card_seed_mul`,
  `IsDisperser.card_seed_gt_inv_mul_log`): every `(K, ε)`-disperser with `1 ≤ K`, `0 < ε < 1 / 2`,
  `1 ≤ ε |Output|`, and `3 |Seed| ≤ |Output|` satisfies
  `ln (|Input| / K) < 12 |Seed| ε`, i.e. `|Seed| > (1 / 12) ε⁻¹ ln (|Input| / K)`.
* **Radhakrishnan–Ta-Shma probabilistic existence** (`exists_isDisperser`): whenever
  `1 ≤ K ≤ |Input|`, `0 < ε < 1`, and
  `ε⁻¹ (ln (|Input| / K) + 1) + (|Output| / K) (ln (ε⁻¹) + 1) < |Seed|`, there exists a
  `(K, ε)`-disperser `disp : Input → Seed → Output`.

## Main definitions

* `CslibFrontier.Probability.dispSupport`: output set reachable from `A` across all seeds.
* `CslibFrontier.Probability.strongDispSupport`: `(seed, output)` pairs reachable from `A`.
* `CslibFrontier.Probability.trappedInputs`: inputs whose seeded outputs all fall in a bad set `B`.
* `CslibFrontier.Probability.IsDisperser`: `(K, ε)`-seeded dispersers.
* `CslibFrontier.Probability.IsStrongDisperser`: strong `(K, ε)`-seeded dispersers.

## Main results

* `CslibFrontier.Probability.IsStrongDisperser.isDisperser`: strong dispersers are dispersers.
* `CslibFrontier.Probability.card_dispSupport_ge_of_isExtractor`,
  `CslibFrontier.Probability.isDisperser_of_isExtractor`,
  `CslibFrontier.Probability.isStrongDisperser_of_isStrongExtractor`: extractors yield dispersers.
* `CslibFrontier.Probability.isDisperser_iff_card_trappedInputs_lt`,
  `CslibFrontier.Probability.isDisperser_iff_card_missed_lt`: duality with confinement and one-sided
  (RP) witness hitting.
* `CslibFrontier.Probability.card_dispSupport_le_mul`,
  `CslibFrontier.Probability.not_isDisperser_of_card_seed_le`,
  `CslibFrontier.Probability.not_isDisperser_of_subsingleton_seed`: trivial output bound and
  impossibility with insufficient or trivial seed.
* `CslibFrontier.Probability.IsDisperser.log_div_lt_card_seed_mul`,
  `CslibFrontier.Probability.IsDisperser.card_seed_gt_inv_mul_log`: Radhakrishnan–Ta-Shma seed lower
  bound.
* `CslibFrontier.Probability.exists_isDisperser`: Radhakrishnan–Ta-Shma
  probabilistic existence of seeded dispersers.
-/

public section

namespace CslibFrontier.Probability

open Cslib.Probability Cslib.Probability.PMF
open scoped Finset

section Definitions

variable {Input Seed Output : Type*}

/-- The finite set `{disp x s | x ∈ A, s : Seed}` of outputs reachable from an input subset `A`
across all seeds. -/
def dispSupport [Fintype Seed] [DecidableEq Output] (disp : Input → Seed → Output)
    (A : Finset Input) : Finset Output :=
  (A ×ˢ (Finset.univ : Finset Seed)).image (fun p ↦ disp p.1 p.2)

/-- Membership in `dispSupport disp A`. -/
@[simp]
theorem mem_dispSupport [Fintype Seed] [DecidableEq Output] {disp : Input → Seed → Output}
    {A : Finset Input} {y : Output} :
    y ∈ dispSupport disp A ↔ ∃ x ∈ A, ∃ s : Seed, disp x s = y := by
  simp only [dispSupport, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Prod.exists, exists_and_left]

/-- Monotonicity of `dispSupport` in the input subset. -/
theorem dispSupport_mono [Fintype Seed] [DecidableEq Output] (disp : Input → Seed → Output)
    {A₁ A₂ : Finset Input} (h : A₁ ⊆ A₂) :
    dispSupport disp A₁ ⊆ dispSupport disp A₂ := fun _ hy ↦ by
  rcases mem_dispSupport.mp hy with ⟨x, hx, s, rfl⟩
  exact mem_dispSupport.mpr ⟨x, h hx, s, rfl⟩

/-- The finite set `{(s, disp x s) | x ∈ A, s : Seed}` of seed-output pairs reachable from `A`. -/
def strongDispSupport [Fintype Seed] [DecidableEq Seed] [DecidableEq Output]
    (disp : Input → Seed → Output) (A : Finset Input) : Finset (Seed × Output) :=
  (A ×ˢ (Finset.univ : Finset Seed)).image (fun p ↦ (p.2, disp p.1 p.2))

/-- Membership in `strongDispSupport disp A`. -/
@[simp]
theorem mem_strongDispSupport [Fintype Seed] [DecidableEq Seed] [DecidableEq Output]
    {disp : Input → Seed → Output} {A : Finset Input} {q : Seed × Output} :
    q ∈ strongDispSupport disp A ↔ ∃ x ∈ A, disp x q.1 = q.2 := by
  rcases q with ⟨s, y⟩
  simp only [strongDispSupport, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨x, t, hx, rfl, hy⟩
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, s, hx, rfl, hy⟩

/-- The finite set `{x : Input | ∀ s : Seed, disp x s ∈ B}` of inputs whose seeded outputs are all
confined to a bad output subset `B` (corresponding to inputs on which every correlated trial of a
one-sided randomized algorithm fails). -/
def trappedInputs [Fintype Input] [Fintype Seed] [DecidableEq Output]
    (disp : Input → Seed → Output) (B : Finset Output) : Finset Input :=
  Finset.univ.filter (fun x ↦ ∀ s : Seed, disp x s ∈ B)

/-- Membership in `trappedInputs disp B`. -/
@[simp]
theorem mem_trappedInputs [Fintype Input] [Fintype Seed] [DecidableEq Output]
    {disp : Input → Seed → Output} {B : Finset Output} {x : Input} :
    x ∈ trappedInputs disp B ↔ ∀ s : Seed, disp x s ∈ B := by
  simp [trappedInputs]

/-- A **`(K, ε)`-seeded disperser**: every input subset `A` of cardinality at least `K` reaches
strictly more than `(1 - ε) |Output|` distinct outputs across all seeds. -/
def IsDisperser [Fintype Seed] [Fintype Output] [DecidableEq Output]
    (disp : Input → Seed → Output) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ A : Finset Input, K ≤ #A →
    (1 - ε) * (Fintype.card Output : ℝ) < (#(dispSupport disp A) : ℝ)

/-- A **strong `(K, ε)`-seeded disperser**: every input subset `A` of cardinality at least `K`
produces strictly more than `(1 - ε) |Seed| |Output|` distinct `(seed, output)` pairs. -/
def IsStrongDisperser [Fintype Seed] [DecidableEq Seed] [Fintype Output] [DecidableEq Output]
    (disp : Input → Seed → Output) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ A : Finset Input, K ≤ #A →
    (1 - ε) * (Fintype.card (Seed × Output) : ℝ) < (#(strongDispSupport disp A) : ℝ)

/-- Dispersers remain dispersers for larger source-size thresholds and larger error parameters. -/
theorem IsDisperser.mono [Fintype Seed] [Fintype Output] [DecidableEq Output]
    {disp : Input → Seed → Output} {K K' : ℕ} {ε ε' : ℝ}
    (h : IsDisperser disp K ε) (hK : K ≤ K') (hε : ε ≤ ε') :
    IsDisperser disp K' ε' := fun A hA ↦
  (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)).trans_lt (h A (hK.trans hA))

/-- Strong dispersers remain strong dispersers for larger thresholds and larger errors. -/
theorem IsStrongDisperser.mono [Fintype Seed] [DecidableEq Seed] [Fintype Output]
    [DecidableEq Output] {disp : Input → Seed → Output} {K K' : ℕ} {ε ε' : ℝ}
    (h : IsStrongDisperser disp K ε) (hK : K ≤ K') (hε : ε ≤ ε') :
    IsStrongDisperser disp K' ε' := fun A hA ↦
  (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)).trans_lt (h A (hK.trans hA))

/-- **Strong dispersers are dispersers**: every missing output `y ∉ dispSupport disp A` misses all
`|Seed|` pairs `(s, y)` in `strongDispSupport disp A`. -/
theorem IsStrongDisperser.isDisperser [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
    [Fintype Output] [DecidableEq Output] {disp : Input → Seed → Output} {K : ℕ} {ε : ℝ}
    (h : IsStrongDisperser disp K ε) : IsDisperser disp K ε := by
  have hS_pos : (0 : ℝ) < (Fintype.card Seed : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro A hA
  have hsub : strongDispSupport disp A ⊆ (Finset.univ : Finset Seed) ×ˢ dispSupport disp A := by
    intro q hq
    rcases mem_strongDispSupport.mp hq with ⟨x, hx, hxq⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ q.1, mem_dispSupport.mpr ⟨x, hx, q.1, hxq⟩⟩
  have hcard : (#(strongDispSupport disp A) : ℝ) ≤
      (Fintype.card Seed : ℝ) * (#(dispSupport disp A) : ℝ) := by
    have hnat := (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
    rw [Finset.card_univ] at hnat
    exact_mod_cast hnat
  have hstrong := (h A hA).trans_le hcard
  rw [Fintype.card_prod, Nat.cast_mul] at hstrong
  exact lt_of_mul_lt_mul_left
    (show (Fintype.card Seed : ℝ) * ((1 - ε) * (Fintype.card Output : ℝ)) <
      (Fintype.card Seed : ℝ) * (#(dispSupport disp A) : ℝ) by linarith) hS_pos.le

end Definitions

/-! ### Seeded extractors yield seeded dispersers -/

section ExtractorBridge

variable {Input Seed Output : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Output]
  [Nonempty Output]

private lemma toOuterMeasure_toReal_eq_one_of_support_subset {α : Type*} (p : PMF α)
    (S : Finset α) (hsupp : p.support ⊆ (S : Set α)) :
    (p.toOuterMeasure (S : Set α)).toReal = 1 := by
  have hcompl : p.toOuterMeasure (S : Set α)ᶜ = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff]
    exact Set.disjoint_compl_right_iff_subset.mpr hsupp
  have hsum := toOuterMeasure_add_compl_ennreal p (S : Set α)
  rw [hcompl, add_zero] at hsum
  simp [hsum]

private lemma toOuterMeasure_uniformOfFintype_finset_toReal {α : Type*} [Fintype α] [Nonempty α]
    (S : Finset α) :
    ((PMF.uniformOfFintype α).toOuterMeasure (S : Set α)).toReal =
      (#S : ℝ) / (Fintype.card α : ℝ) := by
  have hfilt : ∀ inst : DecidablePred (fun a : α ↦ a ∈ (S : Set α)),
      @Finset.filter α _ inst Finset.univ = S := fun _ ↦ by ext a; simp
  rw [toOuterMeasure_apply_toReal, ← Finset.sum_filter, hfilt]
  have hcongr : ∑ a ∈ S, ((PMF.uniformOfFintype α) a).toReal =
      ∑ _a ∈ S, ((Fintype.card α : ℝ))⁻¹ :=
    Finset.sum_congr rfl fun a _ ↦ by simp [PMF.uniformOfFintype_apply]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Extractor output support bound**: if `ext : Input → Seed → Output` is a `(k, ε)`-extractor,
every nonempty input subset `A` with `2^k ≤ |A|` reaches at least `(1 - ε) |Output|` distinct
outputs. -/
theorem card_dispSupport_ge_of_isExtractor [DecidableEq Output] {ext : Input → Seed → Output}
    {k ε : ℝ} (hext : IsExtractor ext k ε) {A : Finset Input} (hA_ne : A.Nonempty)
    (hA_card : (2 : ℝ) ^ k ≤ (#A : ℝ)) :
    (1 - ε) * (Fintype.card Output : ℝ) ≤ (#(dispSupport ext A) : ℝ) := by
  have hM_pos : (0 : ℝ) < (Fintype.card Output : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hA_pos : (0 : ℝ) < (#A : ℝ) := Nat.cast_pos.mpr hA_ne.card_pos
  let src : PMF Input := PMF.uniformOfFinset A hA_ne
  have hmin : k ≤ minEntropy src := by
    rw [minEntropy_uniformOfFinset, Real.le_logb_iff_rpow_le one_lt_two hA_pos]
    exact hA_card
  let out : PMF Output := src.bind fun x ↦ (PMF.uniformOfFintype Seed).map fun s ↦ ext x s
  have hdist : dist out (PMF.uniformOfFintype Output) ≤ ε := hext src hmin
  let S : Finset Output := dispSupport ext A
  have hsupp : out.support ⊆ (S : Set Output) := by
    intro y hy
    simp only [out, src, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
      PMF.mem_support_uniformOfFinset_iff hA_ne, mem_support_uniformOfFintype, true_and] at hy
    rcases hy with ⟨x, hx, s, rfl⟩
    exact Finset.mem_coe.mpr (mem_dispSupport.mpr ⟨x, hx, s, rfl⟩)
  have hev :=
    abs_toOuterMeasure_toReal_sub_le_dist out (PMF.uniformOfFintype Output) (S : Set Output)
  rw [toOuterMeasure_toReal_eq_one_of_support_subset out S hsupp,
    toOuterMeasure_uniformOfFintype_finset_toReal S] at hev
  have hgap : 1 - (#S : ℝ) / (Fintype.card Output : ℝ) ≤ ε :=
    (le_abs_self _).trans (hev.trans hdist)
  have hdiv : 1 - ε ≤ (#S : ℝ) / (Fintype.card Output : ℝ) := by linarith
  exact (le_div_iff₀ hM_pos).mp hdiv

/-- **Seeded extractors are seeded dispersers**: every `(k, ε)`-extractor is a `(K, ε')`-disperser
whenever `1 ≤ K`, `2^k ≤ K`, and `ε < ε'`. -/
theorem isDisperser_of_isExtractor [DecidableEq Output] {ext : Input → Seed → Output}
    {k ε ε' : ℝ} {K : ℕ} (hext : IsExtractor ext k ε) (hK1 : 1 ≤ K)
    (hkK : (2 : ℝ) ^ k ≤ (K : ℝ)) (hε : ε < ε') :
    IsDisperser ext K ε' := by
  have hM_pos : (0 : ℝ) < (Fintype.card Output : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro A hA
  have hA_ne : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hK1.trans hA))
  have hge := card_dispSupport_ge_of_isExtractor hext hA_ne (hkK.trans (Nat.cast_le.mpr hA))
  exact (mul_lt_mul_of_pos_right (by linarith) hM_pos).trans_le hge

/-- **Strong seeded extractors are strong seeded dispersers**: every strong `(k, ε)`-extractor is a
strong `(K, ε')`-disperser whenever `1 ≤ K`, `2^k ≤ K`, and `ε < ε'`. -/
theorem isStrongDisperser_of_isStrongExtractor [DecidableEq Seed] [DecidableEq Output]
    {ext : Input → Seed → Output} {k ε ε' : ℝ} {K : ℕ} (hext : IsStrongExtractor ext k ε)
    (hK1 : 1 ≤ K) (hkK : (2 : ℝ) ^ k ≤ (K : ℝ)) (hε : ε < ε') :
    IsStrongDisperser ext K ε' := by
  have hSM_pos : (0 : ℝ) < (Fintype.card (Seed × Output) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro A hA
  have hA_ne : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hK1.trans hA))
  let src : PMF Input := PMF.uniformOfFinset A hA_ne
  have hmin : k ≤ minEntropy src := by
    rw [minEntropy_uniformOfFinset,
      Real.le_logb_iff_rpow_le one_lt_two (Nat.cast_pos.mpr hA_ne.card_pos)]
    exact hkK.trans (Nat.cast_le.mpr hA)
  let out : PMF (Seed × Output) :=
    src.bind fun x ↦ (PMF.uniformOfFintype Seed).map fun s ↦ (s, ext x s)
  let S : Finset (Seed × Output) := strongDispSupport ext A
  have hsupp : out.support ⊆ (S : Set (Seed × Output)) := by
    intro q hq
    simp only [out, src, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
      PMF.mem_support_uniformOfFinset_iff hA_ne, mem_support_uniformOfFintype, true_and] at hq
    rcases hq with ⟨x, hx, s, rfl⟩
    exact Finset.mem_coe.mpr (mem_strongDispSupport.mpr ⟨x, hx, rfl⟩)
  have hev := abs_toOuterMeasure_toReal_sub_le_dist out
    (PMF.uniformOfFintype (Seed × Output)) (S : Set (Seed × Output))
  rw [toOuterMeasure_toReal_eq_one_of_support_subset out S hsupp,
    toOuterMeasure_uniformOfFintype_finset_toReal S] at hev
  have hgap : 1 - (#S : ℝ) / (Fintype.card (Seed × Output) : ℝ) ≤ ε :=
    (le_abs_self _).trans (hev.trans (hext src hmin))
  have hge : (1 - ε) * (Fintype.card (Seed × Output) : ℝ) ≤ (#S : ℝ) :=
    (le_div_iff₀ hSM_pos).mp (by linarith)
  exact (mul_lt_mul_of_pos_right (by linarith) hSM_pos).trans_le hge

end ExtractorBridge

/-! ### Confinement duality (RP error reduction) and seedless impossibility -/

section DualityAndImpossibility

variable {Input Seed Output : Type*}

/-- **Disperser–confinement duality**: `disp` is a `(K, ε)`-disperser if and only if for every
output subset `T` of cardinality at most `(1 - ε) |Output|`, strictly fewer than `K` inputs have all
their seeded outputs confined to `T`. -/
theorem isDisperser_iff_card_trappedInputs_lt [Fintype Input] [Fintype Seed] [Fintype Output]
    [DecidableEq Output] (disp : Input → Seed → Output) (K : ℕ) (ε : ℝ) :
    IsDisperser disp K ε ↔
      ∀ T : Finset Output, (#T : ℝ) ≤ (1 - ε) * (Fintype.card Output : ℝ) →
        #(trappedInputs disp T) < K := by
  constructor
  · intro hdisp T hT
    by_contra hge
    have hK : K ≤ #(trappedInputs disp T) := Nat.le_of_not_lt hge
    have hsub : dispSupport disp (trappedInputs disp T) ⊆ T := by
      intro y hy
      rcases mem_dispSupport.mp hy with ⟨x, hx, s, rfl⟩
      exact (mem_trappedInputs.mp hx) s
    have hcard : (#(dispSupport disp (trappedInputs disp T)) : ℝ) ≤ (#T : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    exact not_lt_of_ge (hcard.trans hT) (hdisp (trappedInputs disp T) hK)
  · intro htrap A hA
    by_contra hle
    have hsub : A ⊆ trappedInputs disp (dispSupport disp A) := fun x hx ↦
      mem_trappedInputs.mpr fun s ↦ mem_dispSupport.mpr ⟨x, hx, s, rfl⟩
    have hlt := htrap (dispSupport disp A) (le_of_not_gt hle)
    exact not_lt_of_ge (hA.trans (Finset.card_le_card hsub)) hlt

/-- **Disperser–hitting duality (one-sided RP error amplification)**: `disp` is a
`(K, ε)`-disperser if and only if for every witness set `W ⊆ Output` of size at least
`ε |Output|`, strictly fewer than `K` inputs miss `W` on every seed. -/
theorem isDisperser_iff_card_missed_lt [Fintype Input] [Fintype Seed] [Fintype Output]
    [DecidableEq Output] (disp : Input → Seed → Output) (K : ℕ) (ε : ℝ) :
    IsDisperser disp K ε ↔
      ∀ W : Finset Output, ε * (Fintype.card Output : ℝ) ≤ (#W : ℝ) →
        #(Finset.univ.filter (fun x : Input ↦ ∀ s : Seed, disp x s ∉ W)) < K := by
  rw [isDisperser_iff_card_trappedInputs_lt]
  have hfilt : ∀ W : Finset Output,
      Finset.univ.filter (fun x : Input ↦ ∀ s : Seed, disp x s ∉ W) =
        trappedInputs disp (Finset.univ \ W) := fun W ↦ by
    ext x
    simp [mem_trappedInputs]
  have hcompl_card : ∀ S : Finset Output,
      (#(Finset.univ \ S) : ℝ) = (Fintype.card Output : ℝ) - (#S : ℝ) := fun S ↦ by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Nat.cast_sub (Finset.card_le_univ S)]
  constructor
  · intro htrap W hW
    rw [hfilt W]
    refine htrap (Finset.univ \ W) ?_
    rw [hcompl_card W]
    linarith
  · intro hmiss T hT
    have heq : Finset.univ \ (Finset.univ \ T) = T := by
      ext y
      simp
    have hW := hmiss (Finset.univ \ T) (by rw [hcompl_card T]; linarith)
    rwa [hfilt (Finset.univ \ T), heq] at hW

/-- Trivial cardinality upper bound on the reachable output support of a subset `A`. -/
theorem card_dispSupport_le_mul [Fintype Seed] [DecidableEq Output]
    (disp : Input → Seed → Output) (A : Finset Input) :
    #(dispSupport disp A) ≤ #A * Fintype.card Seed := by
  calc #(dispSupport disp A)
      ≤ #(A ×ˢ (Finset.univ : Finset Seed)) := Finset.card_image_le
    _ = #A * Fintype.card Seed := by rw [Finset.card_product, Finset.card_univ]

/-- **Seed-size impossibility**: if `K ≤ |Input|` and `K |Seed| ≤ (1 - ε) |Output|`, no function
`disp : Input → Seed → Output` can be a `(K, ε)`-disperser. -/
theorem not_isDisperser_of_card_seed_le [Fintype Input] [Fintype Seed] [Fintype Output]
    [DecidableEq Output] (disp : Input → Seed → Output) {K : ℕ} {ε : ℝ}
    (hK : K ≤ Fintype.card Input)
    (hbound : (K : ℝ) * (Fintype.card Seed : ℝ) ≤ (1 - ε) * (Fintype.card Output : ℝ)) :
    ¬ IsDisperser disp K ε := by
  intro hdisp
  have hKu : K ≤ #(Finset.univ : Finset Input) := by simpa using hK
  obtain ⟨A, -, hAcard⟩ := Finset.exists_subset_card_eq hKu
  have hle : (#(dispSupport disp A) : ℝ) ≤ (K : ℝ) * (Fintype.card Seed : ℝ) := by
    have hnat := card_dispSupport_le_mul disp A
    rw [hAcard] at hnat
    exact_mod_cast hnat
  exact not_lt_of_ge (hle.trans hbound) (hdisp A hAcard.ge)

/-- **Seedless impossibility**: with a subsingleton (deterministic or empty) seed, no function can
disperse subsets of size `K ≤ |Input|` when `K ≤ (1 - ε) |Output|`. -/
theorem not_isDisperser_of_subsingleton_seed [Fintype Input] [Fintype Seed] [Subsingleton Seed]
    [Fintype Output] [DecidableEq Output] (disp : Input → Seed → Output) {K : ℕ} {ε : ℝ}
    (hK : K ≤ Fintype.card Input)
    (hbound : (K : ℝ) ≤ (1 - ε) * (Fintype.card Output : ℝ)) :
    ¬ IsDisperser disp K ε := by
  have hS : (Fintype.card Seed : ℝ) ≤ 1 := by
    exact_mod_cast Fintype.card_le_one_iff_subsingleton.mpr ‹_›
  refine not_isDisperser_of_card_seed_le disp hK ?_
  calc (K : ℝ) * (Fintype.card Seed : ℝ)
      ≤ (K : ℝ) * 1 := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg K)
    _ = (K : ℝ) := mul_one _
    _ ≤ (1 - ε) * (Fintype.card Output : ℝ) := hbound

end DualityAndImpossibility

/-! ### Radhakrishnan–Ta-Shma seed-degree lower bound and probabilistic existence -/

section RadhakrishnanTaShma

variable {Input Seed Output : Type*}

private lemma choose_sub_div_choose_eq_prod {m s d : ℕ} (h : s + d ≤ m) :
    ((m - d).choose s : ℝ) / (m.choose s : ℝ) =
      ∏ j ∈ Finset.range d, (((m - s - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) := by
  induction d with
  | zero =>
    have hmpos : (0 : ℝ) < (m.choose s : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    simp [div_self hmpos.ne']
  | succ j ih =>
    rw [Finset.prod_range_succ, ← ih (by omega)]
    have hstep_nat : (m - (j + 1)).choose s * (m - j) = (m - j).choose s * (m - s - j) := by
      have h1 := Nat.choose_mul_succ_eq (m - (j + 1)) s
      rwa [show m - (j + 1) + 1 = m - j by omega, show m - j - s = m - s - j by omega] at h1
    have hstep : ((m - (j + 1)).choose s : ℝ) * ((m - j : ℕ) : ℝ) =
        ((m - j).choose s : ℝ) * ((m - s - j : ℕ) : ℝ) := by exact_mod_cast hstep_nat
    have hmj_pos : (0 : ℝ) < ((m - j : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hch_pos : (0 : ℝ) < ((m - j).choose s : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hm_pos : (0 : ℝ) < (m.choose s : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    field_simp [hmj_pos.ne', hch_pos.ne', hm_pos.ne']
    linarith

private lemma exp_le_choose_sub_div_choose {m s d : ℕ} {ε : ℝ}
    (hm3 : 3 ≤ m) (h3d : 3 * d ≤ m) (h2s : 2 * s ≤ m + 1)
    (hε0 : 0 < ε) (hs_le : (s : ℝ) ≤ 2 * ε * (m : ℝ)) :
    Real.exp (-12 * (d : ℝ) * ε) ≤ ((m - d).choose s : ℝ) / (m.choose s : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [choose_sub_div_choose_eq_prod (by omega)]
  have hfac : ∀ j ∈ Finset.range d,
      Real.exp (-12 * ε) ≤ ((m - s - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ) := fun j hj ↦ by
    rw [Finset.mem_range] at hj
    have hmsj_ge : (m : ℝ) / 6 ≤ ((m - s - j : ℕ) : ℝ) := by
      have hr : (m : ℝ) ≤ 6 * ((m - s - j : ℕ) : ℝ) := by
        exact_mod_cast (show m ≤ 6 * (m - s - j) by omega)
      linarith
    have hmsj_pos : (0 : ℝ) < ((m - s - j : ℕ) : ℝ) := by linarith
    have hmj_eq : ((m - j : ℕ) : ℝ) = ((m - s - j : ℕ) : ℝ) + (s : ℝ) := by
      exact_mod_cast (show m - j = m - s - j + s by omega)
    have hinv_le : ((m - j : ℕ) : ℝ) / ((m - s - j : ℕ) : ℝ) ≤ Real.exp (12 * ε) := by
      have hdiv : (s : ℝ) / ((m - s - j : ℕ) : ℝ) ≤ (2 * ε * (m : ℝ)) / ((m : ℝ) / 6) :=
        div_le_div₀ (by positivity) hs_le (by positivity) hmsj_ge
      have hsimp : (2 * ε * (m : ℝ)) / ((m : ℝ) / 6) = 12 * ε := by
        field_simp [hm_pos.ne']
        ring
      have h1 : ((m - j : ℕ) : ℝ) / ((m - s - j : ℕ) : ℝ) ≤ 1 + 12 * ε := by
        rw [hmj_eq, add_div, div_self hmsj_pos.ne']
        linarith
      exact h1.trans (by linarith [Real.add_one_le_exp (12 * ε)])
    rw [show -12 * ε = -(12 * ε) by ring, Real.exp_neg]
    exact (inv_anti₀ (div_pos (by linarith) hmsj_pos) hinv_le).trans_eq (inv_div _ _)
  calc Real.exp (-12 * (d : ℝ) * ε)
      = ∏ _j ∈ Finset.range d, Real.exp (-12 * ε) := by
        rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ ∏ j ∈ Finset.range d, (((m - s - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) hfac

private lemma choose_le_exp_mul_log_add_one {N t : ℕ} (ht1 : 1 ≤ t) (htN : t ≤ N) :
    (N.choose t : ℝ) ≤ Real.exp ((t : ℝ) * (Real.log ((N : ℝ) / (t : ℝ)) + 1)) := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht1
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (ht1.trans htN)
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos t)
  have hdesc : (t.factorial : ℝ) * (N.choose t : ℝ) ≤ (N : ℝ) ^ t := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose N t).symm.trans_le
      (Nat.descFactorial_le_pow N t)
  have hstep1 :
      (N.choose t : ℝ) ≤ ((N : ℝ) / (t : ℝ)) ^ t * ((t : ℝ) ^ t / (t.factorial : ℝ)) := by
    rw [div_pow, div_mul_div_cancel₀ (pow_ne_zero t ht_pos.ne')]
    exact (le_div_iff₀ hfac_pos).mpr (by linarith)
  have hstep2 : (t : ℝ) ^ t / (t.factorial : ℝ) ≤ Real.exp (t : ℝ) :=
    Real.pow_div_factorial_le_exp (t : ℝ) ht_pos.le t
  have hpow :
      ((N : ℝ) / (t : ℝ)) ^ t = Real.exp ((t : ℝ) * Real.log ((N : ℝ) / (t : ℝ))) := by
    rw [Real.exp_nat_mul, Real.exp_log (div_pos hN_pos ht_pos)]
  calc (N.choose t : ℝ)
      ≤ ((N : ℝ) / (t : ℝ)) ^ t * ((t : ℝ) ^ t / (t.factorial : ℝ)) := hstep1
    _ ≤ Real.exp ((t : ℝ) * Real.log ((N : ℝ) / (t : ℝ))) * Real.exp (t : ℝ) := by
        rw [← hpow]
        exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = Real.exp ((t : ℝ) * (Real.log ((N : ℝ) / (t : ℝ)) + 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Radhakrishnan–Ta-Shma seed-degree lower bound**:
every `(K, ε)`-disperser `disp : Input → Seed → Output` on a nonempty input alphabet with
`1 ≤ K`, `0 < ε < 1 / 2`, `1 ≤ ε |Output|`, and `3 |Seed| ≤ |Output|` satisfies
`ln (|Input| / K) < 12 |Seed| ε`.
-/
theorem IsDisperser.log_div_lt_card_seed_mul [Fintype Input] [Nonempty Input] [Fintype Seed]
    [Fintype Output] [DecidableEq Output] {disp : Input → Seed → Output} {K : ℕ} {ε : ℝ}
    (hdisp : IsDisperser disp K ε) (hK : 1 ≤ K) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hεm : 1 ≤ ε * (Fintype.card Output : ℝ))
    (h3d : 3 * Fintype.card Seed ≤ Fintype.card Output) :
    Real.log ((Fintype.card Input : ℝ) / (K : ℝ)) < 12 * (Fintype.card Seed : ℝ) * ε := by
  set n : ℕ := Fintype.card Input
  set d : ℕ := Fintype.card Seed
  set m : ℕ := Fintype.card Output
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hm3 : 3 ≤ m := by
    have hgt : 2 < m := by exact_mod_cast (show (2 : ℝ) < (m : ℝ) by nlinarith)
    omega
  set s : ℕ := Nat.floor (ε * (m : ℝ)) + 1
  have h2s : 2 * s ≤ m + 1 := by
    have hfl_lt : (2 * Nat.floor (ε * (m : ℝ)) : ℝ) < (m : ℝ) := by
      nlinarith [Nat.floor_le (by positivity : 0 ≤ ε * (m : ℝ))]
    have hnat : 2 * Nat.floor (ε * (m : ℝ)) < m := by exact_mod_cast hfl_lt
    omega
  have hs_le : (s : ℝ) ≤ 2 * ε * (m : ℝ) := by
    push_cast [s]
    linarith [Nat.floor_le (by positivity : 0 ≤ ε * (m : ℝ))]
  have hs_gt : ε * (m : ℝ) < (s : ℝ) := by
    push_cast [s]
    exact Nat.lt_floor_add_one _
  let ℬ : Finset (Finset Output) := (Finset.univ : Finset Output).powersetCard s
  let Z : Finset Output → Finset Input :=
    fun W ↦ Finset.univ.filter (fun x : Input ↦ ∀ t : Seed, disp x t ∉ W)
  have hmiss := (isDisperser_iff_card_missed_lt disp K ε).mp hdisp
  have hZ_lt : ∀ W ∈ ℬ, #(Z W) < K := fun W hW ↦ by
    have hcard : #W = s := (Finset.mem_powersetCard.mp hW).2
    exact hmiss W (by rw [hcard]; exact hs_gt.le)
  have hpow_pos : (0 : ℝ) < (m.choose s : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hsum_lt : ∑ W ∈ ℬ, (#(Z W) : ℝ) < (m.choose s : ℝ) * (K : ℝ) := by
    have hne : ℬ.Nonempty := by
      rw [Finset.powersetCard_nonempty, Finset.card_univ]
      omega
    calc ∑ W ∈ ℬ, (#(Z W) : ℝ)
        < ∑ _W ∈ ℬ, (K : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne fun W hW ↦ Nat.cast_lt.mpr (hZ_lt W hW)
      _ = (m.choose s : ℝ) * (K : ℝ) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hsum_ge : (n : ℝ) * ((m - d).choose s : ℝ) ≤ ∑ W ∈ ℬ, (#(Z W) : ℝ) := by
    have hx_count : ∀ x : Input, ((m - d).choose s : ℝ) ≤
        ∑ W ∈ ℬ, (if ∀ t : Seed, disp x t ∉ W then (1 : ℝ) else 0) := fun x ↦ by
      let img : Finset Output := (Finset.univ : Finset Seed).image (disp x)
      rw [Finset.sum_boole]
      have hfilt : ℬ.filter (fun W ↦ ∀ t : Seed, disp x t ∉ W) =
          (Finset.univ \ img).powersetCard s := by
        ext W
        simp only [ℬ, img, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
          true_and, Finset.subset_sdiff, Finset.disjoint_left, Finset.mem_image, Finset.mem_univ]
        constructor
        · rintro ⟨hcard, hno⟩
          refine ⟨fun y hy ↦ ?_, hcard⟩
          rintro ⟨t, rfl⟩
          exact hno t hy
        · rintro ⟨hdisj, hcard⟩
          exact ⟨hcard, fun t ht ↦ hdisj ht ⟨t, rfl⟩⟩
      have himg_le : #img ≤ d := Finset.card_image_le.trans_eq Finset.card_univ
      rw [hfilt, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ img),
        Finset.card_univ]
      exact Nat.cast_le.mpr (Nat.choose_le_choose s (by omega))
    calc (n : ℝ) * ((m - d).choose s : ℝ)
        = ∑ _x : Input, ((m - d).choose s : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x : Input, ∑ W ∈ ℬ, (if ∀ t : Seed, disp x t ∉ W then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun x _ ↦ hx_count x
      _ = ∑ W ∈ ℬ, ∑ x : Input, (if ∀ t : Seed, disp x t ∉ W then (1 : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ W ∈ ℬ, (#(Z W) : ℝ) := by
          refine Finset.sum_congr rfl fun W _ ↦ ?_
          rw [Finset.sum_boole]
  have hratio := exp_le_choose_sub_div_choose hm3 h3d h2s hε0 hs_le
  have hmul_lt : (n : ℝ) * Real.exp (-12 * (d : ℝ) * ε) < (K : ℝ) := by
    calc (n : ℝ) * Real.exp (-12 * (d : ℝ) * ε)
        ≤ (n : ℝ) * (((m - d).choose s : ℝ) / (m.choose s : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio hn_pos.le
      _ = ((n : ℝ) * ((m - d).choose s : ℝ)) / (m.choose s : ℝ) := (mul_div_assoc _ _ _).symm
      _ ≤ (∑ W ∈ ℬ, (#(Z W) : ℝ)) / (m.choose s : ℝ) :=
          (div_le_div_iff_of_pos_right hpow_pos).mpr hsum_ge
      _ < (K : ℝ) := (div_lt_iff₀ hpow_pos).mpr (by linarith)
  have hdiv_lt : (n : ℝ) / (K : ℝ) < Real.exp (12 * (d : ℝ) * ε) := by
    rw [div_lt_iff₀ hK_pos]
    have hmul := mul_lt_mul_of_pos_right hmul_lt (Real.exp_pos (12 * (d : ℝ) * ε))
    rw [mul_assoc, ← Real.exp_add, show -12 * (d : ℝ) * ε + 12 * (d : ℝ) * ε = 0 by ring,
      Real.exp_zero, mul_one, mul_comm] at hmul
    exact hmul
  have hlog := Real.log_lt_log (div_pos hn_pos hK_pos) hdiv_lt
  rwa [Real.log_exp] at hlog

/-- **Radhakrishnan–Ta-Shma seed-degree lower bound**:
every `(K, ε)`-disperser on a nonempty input alphabet with `1 ≤ K`, `0 < ε < 1 / 2`,
`1 ≤ ε |Output|`, and `3 |Seed| ≤ |Output|` requires
`|Seed| > (1 / 12) ε⁻¹ ln (|Input| / K)`.
-/
theorem IsDisperser.card_seed_gt_inv_mul_log [Fintype Input] [Nonempty Input] [Fintype Seed]
    [Fintype Output] [DecidableEq Output] {disp : Input → Seed → Output} {K : ℕ} {ε : ℝ}
    (hdisp : IsDisperser disp K ε) (hK : 1 ≤ K) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hεm : 1 ≤ ε * (Fintype.card Output : ℝ))
    (h3d : 3 * Fintype.card Seed ≤ Fintype.card Output) :
    (1 / 12 : ℝ) * ε⁻¹ * Real.log ((Fintype.card Input : ℝ) / (K : ℝ)) <
      (Fintype.card Seed : ℝ) := by
  have hlog := hdisp.log_div_lt_card_seed_mul hK hε0 hε1 hεm h3d
  have hpos : (0 : ℝ) < (1 / 12 : ℝ) * ε⁻¹ := by positivity
  refine (mul_lt_mul_of_pos_left hlog hpos).trans_eq ?_
  field_simp [hε0.ne']

/-- **Radhakrishnan–Ta-Shma probabilistic disperser existence**:
whenever `1 ≤ K ≤ |Input|`, `0 < ε < 1`, and
`ε⁻¹ (ln (|Input| / K) + 1) + (|Output| / K) (ln (ε⁻¹) + 1) < |Seed|`, there exists a
`(K, ε)`-seeded disperser `disp : Input → Seed → Output`.
-/
theorem exists_isDisperser [Fintype Input] [Fintype Seed] [Fintype Output] [Nonempty Output]
    [DecidableEq Output] {K : ℕ} {ε : ℝ} (hK1 : 1 ≤ K) (hKn : K ≤ Fintype.card Input)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hd : ε⁻¹ * (Real.log ((Fintype.card Input : ℝ) / (K : ℝ)) + 1) +
        ((Fintype.card Output : ℝ) / (K : ℝ)) * (Real.log (ε⁻¹) + 1) <
      (Fintype.card Seed : ℝ)) :
    ∃ disp : Input → Seed → Output, IsDisperser disp K ε := by
  classical
  set n : ℕ := Fintype.card Input
  set d : ℕ := Fintype.card Seed
  set m : ℕ := Fintype.card Output
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK1
  have hm1 : 1 ≤ m := Fintype.card_pos
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm1
  set s : ℕ := Nat.ceil (ε * (m : ℝ))
  have hs1 : 1 ≤ s := Nat.succ_le_of_lt (Nat.ceil_pos.mpr (mul_pos hε0 hm_pos))
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs1
  have hsm : s ≤ m := Nat.ceil_le.mpr (by nlinarith)
  have hs_ge : ε * (m : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  let Ω : Finset (Input → Seed → Output) := Finset.univ
  have hΩ_card : #Ω = (m ^ d) ^ n := by
    simp [Ω, n, d, m]
  have hΩ_pos : (0 : ℝ) < (#Ω : ℝ) := by
    rw [hΩ_card]
    exact_mod_cast pow_pos (pow_pos hm1 d) n
  let 𝒜 : Finset (Finset Input) := (Finset.univ : Finset Input).powersetCard K
  let ℬ : Finset (Finset Output) := (Finset.univ : Finset Output).powersetCard s
  let bad : Finset Input × Finset Output → Finset (Input → Seed → Output) :=
    fun q ↦ Ω.filter (fun disp ↦ ∀ x ∈ q.1, ∀ t : Seed, disp x t ∈ Finset.univ \ q.2)
  have hbad_le : ∀ A ∈ 𝒜, ∀ W ∈ ℬ,
      (#(bad (A, W)) : ℝ) / (#Ω : ℝ) ≤
        Real.exp (-((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ)) := by
    intro A hA W hW
    have hAcard : #A = K := (Finset.mem_powersetCard.mp hA).2
    have hWcard : #W = s := (Finset.mem_powersetCard.mp hW).2
    let fullSeed : Finset (Seed → Output) := Finset.univ
    let avoidSeed : Finset (Seed → Output) :=
      Fintype.piFinset (fun _ : Seed ↦ Finset.univ \ W)
    have hpi : bad (A, W) =
        Fintype.piFinset (fun x : Input ↦ if x ∈ A then avoidSeed else fullSeed) := by
      ext disp
      simp only [bad, Ω, fullSeed, avoidSeed, Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      constructor
      · intro h x
        by_cases hx : x ∈ A
        · simp [hx, h x hx]
        · simp [hx]
      · intro h x hx t
        have hxt := h x
        simp only [hx, ↓reduceIte, Fintype.mem_piFinset] at hxt
        exact hxt t
    have hfull_card : #fullSeed = m ^ d := by simp [fullSeed, d, m]
    have havoid_card : #avoidSeed = (m - s) ^ d := by
      simp [avoidSeed, d, m, Finset.card_sdiff_of_subset (Finset.subset_univ W), hWcard]
    have hbad_card : #(bad (A, W)) = ((m - s) ^ d) ^ K * (m ^ d) ^ (n - K) := by
      rw [hpi, Fintype.card_piFinset]
      have hprod : (∏ x : Input, #(if x ∈ A then avoidSeed else fullSeed)) =
          ∏ x : Input, (if x ∈ A then (m - s) ^ d else m ^ d) := by
        refine Finset.prod_congr rfl fun x _ ↦ ?_
        by_cases hx : x ∈ A <;> simp [hx, havoid_card, hfull_card]
      rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
        show Finset.univ.filter (fun x : Input ↦ x ∈ A) = A by ext x; simp,
        show Finset.univ.filter (fun x : Input ↦ x ∉ A) = Finset.univ \ A by ext x; simp,
        Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, hAcard]
    have hratio : (#(bad (A, W)) : ℝ) / (#Ω : ℝ) = (((m - s : ℕ) : ℝ) / (m : ℝ)) ^ (d * K) := by
      have hmd_ne : ((m : ℝ) ^ d) ^ (n - K) ≠ 0 := by positivity
      have hΩ_split : #Ω = (m ^ d) ^ K * (m ^ d) ^ (n - K) := by
        rw [hΩ_card, ← pow_add, Nat.add_sub_of_le hKn]
      rw [hbad_card, hΩ_split]
      push_cast
      rw [mul_div_mul_right _ _ hmd_ne, ← pow_mul, ← pow_mul, div_pow]
    rw [hratio, Nat.cast_sub hsm, sub_div, div_self hm_pos.ne']
    have hbase : 1 - (s : ℝ) / (m : ℝ) ≤ Real.exp (-((s : ℝ) / (m : ℝ))) := by
      linarith [Real.add_one_le_exp (-((s : ℝ) / (m : ℝ)))]
    have hbase_nn : 0 ≤ 1 - (s : ℝ) / (m : ℝ) := by
      rw [sub_nonneg, div_le_one hm_pos]
      exact_mod_cast hsm
    exact (pow_le_pow_left₀ hbase_nn hbase (d * K)).trans_eq
      (by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring)
  have hsum_lt_one : (∑ q ∈ 𝒜 ×ˢ ℬ, (#(bad q) : ℝ)) / (#Ω : ℝ) < 1 := by
    rw [Finset.sum_div, Finset.sum_product]
    have h𝒜_le : (#𝒜 : ℝ) ≤ Real.exp ((K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1)) := by
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact choose_le_exp_mul_log_add_one hK1 hKn
    have hℬ_le : (#ℬ : ℝ) ≤ Real.exp ((s : ℝ) * (Real.log ((m : ℝ) / (s : ℝ)) + 1)) := by
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact choose_le_exp_mul_log_add_one hs1 hsm
    have hprod_le : ∑ A ∈ 𝒜, ∑ W ∈ ℬ, (#(bad (A, W)) : ℝ) / (#Ω : ℝ) ≤
        Real.exp ((K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1) +
          (s : ℝ) * (Real.log ((m : ℝ) / (s : ℝ)) + 1) -
          ((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ)) := by
      calc ∑ A ∈ 𝒜, ∑ W ∈ ℬ, (#(bad (A, W)) : ℝ) / (#Ω : ℝ)
          ≤ ∑ _A ∈ 𝒜, ∑ _W ∈ ℬ, Real.exp (-((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ)) :=
            Finset.sum_le_sum fun A hA ↦ Finset.sum_le_sum fun W hW ↦ hbad_le A hA W hW
        _ = (#𝒜 : ℝ) * (#ℬ : ℝ) * Real.exp (-((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
        _ ≤ Real.exp ((K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1)) *
              Real.exp ((s : ℝ) * (Real.log ((m : ℝ) / (s : ℝ)) + 1)) *
              Real.exp (-((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul h𝒜_le hℬ_le (Nat.cast_nonneg _) (Real.exp_pos _).le)
              (Real.exp_pos _).le
        _ = Real.exp ((K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1) +
              (s : ℝ) * (Real.log ((m : ℝ) / (s : ℝ)) + 1) -
              ((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    refine hprod_le.trans_lt (Real.exp_lt_one_iff.mpr ?_)
    have hsdK : ((s : ℝ) / (ε * (m : ℝ))) * ((K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1)) +
        (s : ℝ) * (Real.log (ε⁻¹) + 1) < ((s : ℝ) / (m : ℝ)) * (d : ℝ) * (K : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hd (show 0 < ((s : ℝ) / (m : ℝ)) * (K : ℝ) by positivity)
      refine (le_of_eq ?_).trans_lt (hmul.trans_eq (by ring))
      field_simp [hm_pos.ne', hK_pos.ne', hε0.ne']
    have hterm1 : (K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1) ≤
        ((s : ℝ) / (ε * (m : ℝ))) * ((K : ℝ) * (Real.log ((n : ℝ) / (K : ℝ)) + 1)) := by
      have hlog_nn : 0 ≤ Real.log ((n : ℝ) / (K : ℝ)) :=
        Real.log_nonneg ((one_le_div hK_pos).mpr (Nat.cast_le.mpr hKn))
      exact le_mul_of_one_le_left (by positivity) ((one_le_div (mul_pos hε0 hm_pos)).mpr hs_ge)
    have hterm2 : (s : ℝ) * (Real.log ((m : ℝ) / (s : ℝ)) + 1) ≤
        (s : ℝ) * (Real.log (ε⁻¹) + 1) := by
      have hms_le : (m : ℝ) / (s : ℝ) ≤ ε⁻¹ := by
        rw [div_le_iff₀ hs_pos, inv_mul_eq_div, le_div_iff₀ hε0]
        linarith
      have hlog_le : Real.log ((m : ℝ) / (s : ℝ)) ≤ Real.log (ε⁻¹) :=
        Real.log_le_log (div_pos hm_pos hs_pos) hms_le
      exact mul_le_mul_of_nonneg_left (by linarith) hs_pos.le
    linarith
  have hbiUnion_lt : #((𝒜 ×ˢ ℬ).biUnion bad) < #Ω := by
    have hle : (#((𝒜 ×ˢ ℬ).biUnion bad) : ℝ) ≤ ∑ q ∈ 𝒜 ×ˢ ℬ, (#(bad q) : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hlt_r : (#((𝒜 ×ˢ ℬ).biUnion bad) : ℝ) < (#Ω : ℝ) :=
      hle.trans_lt ((div_lt_one hΩ_pos).mp hsum_lt_one)
    exact_mod_cast hlt_r
  have hgood_ne : (Ω \ (𝒜 ×ˢ ℬ).biUnion bad).Nonempty := by
    rw [← Finset.card_pos]
    have hsub : (𝒜 ×ˢ ℬ).biUnion bad ⊆ Ω :=
      Finset.biUnion_subset.mpr fun _ _ ↦ Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  obtain ⟨disp, hdisp_mem⟩ := hgood_ne
  have hnot_bad : ∀ A ∈ 𝒜, ∀ W ∈ ℬ, disp ∉ bad (A, W) := fun A hA W hW hmem ↦
    (Finset.mem_sdiff.mp hdisp_mem).2
      (Finset.mem_biUnion.mpr ⟨(A, W), Finset.mem_product.mpr ⟨hA, hW⟩, hmem⟩)
  refine ⟨disp, fun A' hA' ↦ ?_⟩
  obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq hA'
  have hA_mem : A ∈ 𝒜 := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hA_card⟩
  have hmiss_lt : #(Finset.univ \ dispSupport disp A) < s := by
    by_contra hge
    obtain ⟨W, hW_sub, hW_card⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_lt hge)
    have hW_mem : W ∈ ℬ := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ W, hW_card⟩
    refine hnot_bad A hA_mem W hW_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ disp, ?_⟩)
    intro x hx t
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hWxt ↦ ?_⟩
    exact (Finset.mem_sdiff.mp (hW_sub hWxt)).2 (mem_dispSupport.mpr ⟨x, hx, t, rfl⟩)
  have hmiss_real : (#(Finset.univ \ dispSupport disp A) : ℝ) < ε * (m : ℝ) :=
    Nat.lt_ceil.mp hmiss_lt
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Nat.cast_sub (Finset.card_le_univ _)] at hmiss_real
  have hA_gt : (1 - ε) * (m : ℝ) < (#(dispSupport disp A) : ℝ) := by linarith
  exact hA_gt.trans_le (Nat.cast_le.mpr (Finset.card_le_card (dispSupport_mono disp hA_sub)))

end RadhakrishnanTaShma

end CslibFrontier.Probability
