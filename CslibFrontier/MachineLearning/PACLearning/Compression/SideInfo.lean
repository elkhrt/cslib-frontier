/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import CslibFrontier.MachineLearning.PACLearning.RealizableSample
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Sort
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.MachineLearning.PACLearning.FiniteClass
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Sample Compression Schemes with Side Information

This module extends `Cslib.MachineLearning.PACLearning.SampleCompressionScheme` to sample
compression schemes with `(k, ℓ)` parameters: on any realizable sample of length `m`, the
compression map selects a subset `I ⊆ Fin m` of size at most `k` (keeping its subsequence in
increasing index order) together with an `ℓ`-bit side-information string `σ : Fin ℓ → Bool`, and
the reconstruction map produces a hypothesis consistent with the entire original sample.

## Main definitions

- `CslibFrontier.MachineLearning.PACLearning.SideInfoCompressionScheme`: sample compression scheme
  with parameters `(k, ℓ)` (at most `k` retained examples plus `ℓ` bits of side information).
- `CslibFrontier.MachineLearning.PACLearning.SideInfoCompressionScheme.learner`: the learner
  induced by compressing and reconstructing.
- `CslibFrontier.MachineLearning.PACLearning.MeasurableSideInfoReconstruction`: joint measurability
  of the misclassification sets of a reconstruction map with side information.

## Main results

- `SideInfoCompressionScheme.measure_pi_lt_error_learner_le_sum_choose`:
  exact Littlestone–Warmuth binomial bound
  $\Pr[\mathrm{err}_D(h, c) > \varepsilon] \le 2^\ell \sum_{i=0}^k \binom{m}{i}
  e^{-\varepsilon (m - i)}$.
- `SideInfoCompressionScheme.measure_pi_lt_error_learner_le_of_sample_bound`:
  explicit sample-complexity bound: for $\varepsilon, \delta \in (0, 1)$, taking
  $m \ge (6 k \ln(2/\varepsilon) + 2 \ell \ln 2 + 2 \ln(1/\delta)) / \varepsilon$ suffices to
  ensure error at most $\varepsilon$ with probability at least $1 - \delta$.
- `CslibFrontier.MachineLearning.PACLearning.sum_choose_le_exp_mul_div_pow`: standard binomial
  estimate $\sum_{i=0}^k \binom{m}{i} \le (e m / k)^k$ for $1 \le k \le m$.
-/

public section

namespace CslibFrontier.MachineLearning.PACLearning

open MeasureTheory Set
open Cslib.MachineLearning.PACLearning
open scoped ENNReal NNReal

variable {α β : Type*}

/-- A **sample compression scheme with side information** of parameters `(k, ℓ)` for a concept
class `C`: on every sample realized by `C`, `compress` outputs a subset `I` of at most `k` indices
(retaining the corresponding subsequence in increasing index order) together with an `ℓ`-bit
string `σ : Fin ℓ → Bool`, and `reconstruct` maps `(S|_I, σ)` to a hypothesis consistent with the
entire sample `S`. -/
structure SideInfoCompressionScheme (C : ConceptClass α β) (k ℓ : ℕ) where
  /-- The retained index subset `I ⊆ Fin m` and `ℓ`-bit side-information string `σ`. -/
  compress : ∀ {m : ℕ}, LabeledSample α β m → Finset (Fin m) × (Fin ℓ → Bool)
  /-- Reconstruction map from the sorted retained subsequence and side information to a
  hypothesis. -/
  reconstruct : List (α × β) → (Fin ℓ → Bool) → α → β
  /-- On every realizable sample, at most `k` indices are retained. -/
  card_compress_le : ∀ {m : ℕ} (S : LabeledSample α β m), Realizable C S →
    (compress S).1.card ≤ k
  /-- On every realizable sample, the reconstructed hypothesis agrees with every example in `S`. -/
  reconstruct_correct : ∀ {m : ℕ} (S : LabeledSample α β m), Realizable C S →
    ∀ i : Fin m,
      reconstruct (((compress S).1.sort (· ≤ ·)).map S) (compress S).2 (S i).1 = (S i).2

namespace SideInfoCompressionScheme

variable {C : ConceptClass α β} {k ℓ : ℕ}

/-- The learner associated with a `(k, ℓ)`-sample compression scheme. -/
@[expose] def learner (κ : SideInfoCompressionScheme C k ℓ) {m : ℕ} : Learner α β m :=
  fun S => κ.reconstruct (((κ.compress S).1.sort (· ≤ ·)).map S) (κ.compress S).2

/-- On a realizable sample, the induced learner is consistent with every example. -/
theorem learner_apply_eq (κ : SideInfoCompressionScheme C k ℓ) {m : ℕ}
    {S : LabeledSample α β m} (hS : Realizable C S) (i : Fin m) :
    κ.learner S (S i).1 = (S i).2 :=
  κ.reconstruct_correct S hS i

/-- Restricting a `(k, ℓ)`-sample compression scheme to a subclass `C' ⊆ C`. -/
def ofSubset (κ : SideInfoCompressionScheme C k ℓ) {C' : ConceptClass α β} (h : C' ⊆ C) :
    SideInfoCompressionScheme C' k ℓ where
  compress := κ.compress
  reconstruct := κ.reconstruct
  card_compress_le S hS :=
    κ.card_compress_le S (let ⟨c, hc, hcS⟩ := hS; ⟨c, h hc, hcS⟩)
  reconstruct_correct S hS :=
    κ.reconstruct_correct S (let ⟨c, hc, hcS⟩ := hS; ⟨c, h hc, hcS⟩)

/-- `ofSubset` preserves the underlying compression map. -/
@[simp]
theorem ofSubset_compress (κ : SideInfoCompressionScheme C k ℓ) {C' : ConceptClass α β}
    (h : C' ⊆ C) {m : ℕ} (S : LabeledSample α β m) :
    (κ.ofSubset h).compress S = κ.compress S := by rfl

/-- `ofSubset` preserves the underlying reconstruction map. -/
@[simp]
theorem ofSubset_reconstruct (κ : SideInfoCompressionScheme C k ℓ) {C' : ConceptClass α β}
    (h : C' ⊆ C) : (κ.ofSubset h).reconstruct = κ.reconstruct := by rfl

/-- `ofSubset` preserves the induced learner. -/
@[simp]
theorem ofSubset_learner (κ : SideInfoCompressionScheme C k ℓ) {C' : ConceptClass α β}
    (h : C' ⊆ C) {m : ℕ} : (κ.ofSubset h).learner (m := m) = κ.learner := by rfl

end SideInfoCompressionScheme

/-- Joint measurability of misclassification sets of a reconstruction map with `ℓ` bits of side
information. Automatically satisfied on any countable domain with measurable singletons. -/
def MeasurableSideInfoReconstruction [MeasurableSpace α] [MeasurableSpace β] {ℓ : ℕ}
    (ρ : List (α × β) → (Fin ℓ → Bool) → α → β) : Prop :=
  ∀ (σ : Fin ℓ → Bool), MeasurableReconstruction (fun L => ρ L σ)

/-- On countable domains with measurable singletons, every reconstruction map with side
information has measurable misclassification sets. -/
theorem measurableSideInfoReconstruction_of_countable [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {ℓ : ℕ} (ρ : List (α × β) → (Fin ℓ → Bool) → α → β) :
    MeasurableSideInfoReconstruction ρ :=
  fun σ => measurableReconstruction_of_countable (fun L => ρ L σ)

/-- Standard binomial tail estimate: for `1 ≤ k` and `k ≤ m`,
`∑ i ∈ Finset.range (k + 1), m.choose i ≤ (e * m / k) ^ k`. -/
theorem sum_choose_le_exp_mul_div_pow {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ)) ≤
      (Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le hk hkm)
  have hr_pos : (0 : ℝ) < (k : ℝ) / (m : ℝ) := div_pos hk_pos hm_pos
  have hr_le : (k : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hm_pos).mpr (Nat.cast_le.mpr hkm)
  have hstep1 : ((k : ℝ) / (m : ℝ)) ^ k * ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) ≤
      ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * ((k : ℝ) / (m : ℝ)) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr_pos.le hr_le hik) (Nat.cast_nonneg _)
  have hstep2 : ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * ((k : ℝ) / (m : ℝ)) ^ i ≤
      (1 + (k : ℝ) / (m : ℝ)) ^ m := by
    rw [add_comm (1 : ℝ), add_pow]
    have hsub : Finset.range (k + 1) ⊆ Finset.range (m + 1) :=
      Finset.range_mono (Nat.succ_le_succ hkm)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans_eq' ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [one_pow, mul_one]
    ring
  have hstep3 : (1 + (k : ℝ) / (m : ℝ)) ^ m ≤ Real.exp (k : ℝ) := by
    calc (1 + (k : ℝ) / (m : ℝ)) ^ m
        ≤ (Real.exp ((k : ℝ) / (m : ℝ))) ^ m :=
          pow_le_pow_left₀ (by positivity)
            (by linarith [Real.add_one_le_exp ((k : ℝ) / (m : ℝ))]) m
      _ = Real.exp ((m : ℝ) * ((k : ℝ) / (m : ℝ))) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (k : ℝ) := by rw [mul_div_cancel₀ _ hm_pos.ne']
  have hcomb : ((k : ℝ) / (m : ℝ)) ^ k * ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) ≤
      Real.exp (k : ℝ) :=
    hstep1.trans (hstep2.trans hstep3)
  have hpow_pos : 0 < ((k : ℝ) / (m : ℝ)) ^ k := pow_pos hr_pos k
  calc (∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ))
      ≤ Real.exp (k : ℝ) / ((k : ℝ) / (m : ℝ)) ^ k := (le_div_iff₀' hpow_pos).mpr hcomb
    _ = (Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k := by
        symm
        rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one]
        symm
        rw [div_pow, div_div_eq_mul_div]

/-- **Exact Littlestone–Warmuth binomial bound for `(k, ℓ)`-sample compression**:
for any `(k, ℓ)`-sample compression scheme with measurable reconstruction and any distribution
`D` realizable by `C`, on `m` i.i.d. examples,
`Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (κ.learner S)}`
is at most `ENNReal.ofReal (2 ^ ℓ * ∑ i ∈ Finset.range (k +
  1), m.choose i * exp (-ε * (m - i)))`. -/
theorem SideInfoCompressionScheme.measure_pi_lt_error_learner_le_sum_choose
    [MeasurableSpace α] [MeasurableSpace β] {C : ConceptClass α β} {k ℓ : ℕ}
    (κ : SideInfoCompressionScheme C k ℓ)
    (hκ : MeasurableSideInfoReconstruction κ.reconstruct)
    {D : Measure (α × β)} [IsProbabilityMeasure D] (hD : IsRealizableBy D C)
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (κ.learner S)} ≤
      ENNReal.ofReal ((2 : ℝ) ^ ℓ *
        ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * Real.exp (-ε * ((m : ℝ) - (i : ℝ)))) := by
  classical
  set μ := Measure.pi (fun _ : Fin m => D)
  let Pairs := {I : Finset (Fin m) // I.card ≤ k} × (Fin ℓ → Bool)
  let g (p : Pairs) (S : LabeledSample α β m) : α → β :=
    κ.reconstruct ((p.1.1.sort (· ≤ ·)).map S) p.2
  let B (p : Pairs) : Set (LabeledSample α β m) :=
    {S | ENNReal.ofReal ε < error D (g p S) ∧ ∀ i ∉ p.1.1, g p S (S i).1 = (S i).2}
  have hsub : {S | ENNReal.ofReal ε < error D (κ.learner S)} ≤ᵐ[μ] ⋃ p, B p := by
    filter_upwards [hD.ae_realizable m] with S hS hlt
    let p : Pairs := (⟨(κ.compress S).1, κ.card_compress_le S hS⟩, (κ.compress S).2)
    refine mem_iUnion.mpr ⟨p, ?_, fun i _ => ?_⟩
    · exact hlt
    · exact κ.learner_apply_eq hS i
  have hB : ∀ p : Pairs,
      μ (B p) ≤ ENNReal.ofReal (Real.exp (-ε * ((m : ℝ) - (p.1.1.card : ℝ)))) := by
    intro p
    have hdep : DependsOn (g p) (p.1.1 : Set (Fin m)) := by
      intro S S' hSS'
      dsimp only [g]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      exact hSS' i (Finset.mem_coe.mpr ((Finset.mem_sort (· ≤ ·)).mp hi))
    have hmeas : MeasurableSet
        {q : (LabeledSample α β m × α) × β | Function.uncurry (g p) q.1 ≠ q.2} := by
      let L := p.1.1.sort (· ≤ ·)
      let fn : (LabeledSample α β m × α) × β →
          (LabeledSample α β L.length × α) × β :=
        fun q => ((fun t => q.1.1 (L.get t), q.1.2), q.2)
      have hfn : Measurable fn := by fun_prop
      have hpre := (hκ p.2 L.length).preimage hfn
      refine hpre.congr ?_
      ext ⟨⟨S, x⟩, y⟩
      simp only [mem_preimage, mem_ofPred_eq, Function.uncurry_apply_pair, fn, g, L]
      have hmap : (List.ofFn fun t => S (L.get t)) = L.map S := by
        calc (List.ofFn fun t => S (L.get t))
            = List.ofFn (S ∘ L.get) := rfl
          _ = (List.ofFn L.get).map S := List.map_ofFn.symm
          _ = L.map S := by rw [List.ofFn_get]
      rw [hmap]
    have hhold := measure_pi_lt_error_and_forall_notMem_apply_eq_le D p.1.1 hdep hmeas
      (ENNReal.ofReal ε)
    refine hhold.trans ?_
    have hcard_le : p.1.1.card ≤ m :=
      (Finset.card_le_univ p.1.1).trans (by rw [Fintype.card_fin])
    have h1 : 1 - ENNReal.ofReal ε ≤ ENNReal.ofReal (Real.exp (-ε)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hε]
      exact ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg ε)
    calc (1 - ENNReal.ofReal ε) ^ (m - p.1.1.card)
        ≤ ENNReal.ofReal (Real.exp (-ε)) ^ (m - p.1.1.card) := by gcongr
      _ = ENNReal.ofReal (Real.exp (-ε * ((m - p.1.1.card : ℕ) : ℝ))) := by
          rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 2
          ring
      _ = ENNReal.ofReal (Real.exp (-ε * ((m : ℝ) - (p.1.1.card : ℝ)))) := by
          rw [Nat.cast_sub hcard_le]
  calc μ {S | ENNReal.ofReal ε < error D (κ.learner S)}
      ≤ μ (⋃ p, B p) := measure_mono_ae hsub
    _ ≤ ∑ p : Pairs, μ (B p) := measure_iUnion_fintype_le μ B
    _ ≤ ∑ p : Pairs, ENNReal.ofReal (Real.exp (-ε * ((m : ℝ) - (p.1.1.card : ℝ)))) :=
        Finset.sum_le_sum fun p _ => hB p
    _ = ENNReal.ofReal (∑ p : Pairs, Real.exp (-ε * ((m : ℝ) - (p.1.1.card : ℝ)))) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal ((2 : ℝ) ^ ℓ *
          ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) *
            Real.exp (-ε * ((m : ℝ) - (i : ℝ)))) := by
        congr 1
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset {I : Finset (Fin m) // I.card ≤ k}))
            (g := fun I : {I : Finset (Fin m) // I.card ≤ k} => I.1.card)
            (t := Finset.range (k + 1))
            (fun I _ => Finset.mem_range.mpr (Nat.lt_succ_of_le I.2))]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hcongr : ∑ x ∈ (Finset.univ : Finset {I : Finset (Fin m) // I.card ≤ k}).filter
              (fun I => I.1.card = i),
            Real.exp (-ε * ((m : ℝ) - (x.1.card : ℝ))) =
            ∑ _x ∈ (Finset.univ : Finset {I : Finset (Fin m) // I.card ≤ k}).filter
              (fun I => I.1.card = i),
              Real.exp (-ε * ((m : ℝ) - (i : ℝ))) :=
          Finset.sum_congr rfl fun x hx => by
            rw [(Finset.mem_filter.mp hx).2]
        rw [hcongr, Finset.sum_const, nsmul_eq_mul]
        congr 1
        have hbij : ((Finset.univ : Finset {I : Finset (Fin m) // I.card ≤ k}).filter
            (fun I => I.1.card = i)).card =
            (Finset.powersetCard i (Finset.univ : Finset (Fin m))).card := by
          refine Finset.card_bij (fun I _ => I.1) ?_ ?_ ?_
          · intro I hI
            exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hI).2⟩
          · intro I₁ _ I₂ _ h
            exact Subtype.ext h
          · intro J hJ
            have hJcard := (Finset.mem_powersetCard.mp hJ).2
            have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            exact ⟨⟨J, hJcard.le.trans hik⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJcard⟩, rfl⟩
        rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Explicit sample-complexity bound for `(k, ℓ)`-sample compression**: for any
`ε, δ ∈ (0, 1)`, taking `m ≥ (6 * k * log (2 / ε) + 2 * ℓ * log 2 + 2 * log (1 / δ)) / ε`
(and `m ≥ k`) guarantees that the reconstructed hypothesis has error at most `ε` with probability
at least `1 - δ`. -/
theorem SideInfoCompressionScheme.measure_pi_lt_error_learner_le_of_sample_bound
    [MeasurableSpace α] [MeasurableSpace β] {C : ConceptClass α β} {k ℓ m : ℕ}
    (κ : SideInfoCompressionScheme C k ℓ)
    (hκ : MeasurableSideInfoReconstruction κ.reconstruct)
    {D : Measure (α × β)} [IsProbabilityMeasure D] (hD : IsRealizableBy D C)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hkm : k ≤ m)
    (hm : (6 * (k : ℝ) * Real.log (2 / ε) + 2 * (ℓ : ℝ) * Real.log 2 + 2 * Real.log δ⁻¹) / ε ≤
      (m : ℝ)) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (κ.learner S)} ≤
      ENNReal.ofReal δ := by
  refine (κ.measure_pi_lt_error_learner_le_sum_choose hκ hD m hε0.le).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum_le :
      (∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * Real.exp (-ε * ((m : ℝ) - (i : ℝ)))) ≤
        (∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ)) * Real.exp (-ε * ((m : ℝ) - (k : ℝ))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Nat.cast_nonneg _)
  have hεm : 6 * (k : ℝ) * Real.log (2 / ε) + 2 * (ℓ : ℝ) * Real.log 2 + 2 * Real.log δ⁻¹ ≤
      ε * (m : ℝ) := by
    have := (div_le_iff₀ hε0).mp hm
    linarith
  have hlog2ε : (0 : ℝ) < Real.log (2 / ε) := Real.log_pos (by rw [one_lt_div hε0]; linarith)
  have hlogδ_nn : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ0).mpr hδ1)
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by
    have h1 : (1 / 2 : ℝ) < Real.exp (-1 / 2) := by
      have := Real.add_one_lt_exp (by norm_num : (-1 / 2 : ℝ) ≠ 0)
      linarith
    have h2 : Real.exp (1 / 2) < 2 := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg] at h1
      have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
      have := (lt_inv_comm₀ (by norm_num : (0 : ℝ) < 1 / 2) hpos).mp h1
      linarith
    have h3 := Real.log_lt_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h3
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one,
      Nat.cast_zero, sub_zero, one_mul, mul_zero, zero_mul, zero_add] at hsum_le hεm ⊢
    have hexp_bound : (2 : ℝ) ^ ℓ * Real.exp (-ε * (m : ℝ)) =
        Real.exp ((ℓ : ℝ) * Real.log 2 - ε * (m : ℝ)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp [div_eq_mul_inv, Real.exp_neg]
    have hlogδ : Real.log δ⁻¹ = -Real.log δ := Real.log_inv δ
    have h1 : (ℓ : ℝ) * Real.log 2 - ε * (m : ℝ) ≤ Real.log δ := by
      have : 0 ≤ (ℓ : ℝ) * Real.log 2 := by positivity
      linarith
    calc (2 : ℝ) ^ ℓ * (Real.exp (-ε * (m : ℝ)))
        = Real.exp ((ℓ : ℝ) * Real.log 2 - ε * (m : ℝ)) := hexp_bound
      _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr h1
      _ = δ := Real.exp_log hδ0
  · have hbin := sum_choose_le_exp_mul_div_pow hk hkm
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le hk hkm)
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hlog_emk : Real.log (Real.exp 1 * (m : ℝ) / (k : ℝ)) ≤
        ε * (m : ℝ) / (2 * (k : ℝ)) + Real.log (2 / ε) := by
      have harg : Real.exp 1 * (m : ℝ) / (k : ℝ) =
          Real.exp 1 * (ε * (m : ℝ) / (2 * (k : ℝ))) * (2 / ε) := by
        field_simp [hε0.ne', hk_pos.ne']
      rw [harg, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      have hlog_le :=
        Real.log_le_sub_one_of_pos (show 0 < ε * (m : ℝ) / (2 * (k : ℝ)) by positivity)
      linarith
    have h2 : (2 : ℝ) ^ ℓ * ((Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k *
        Real.exp (-ε * ((m : ℝ) - (k : ℝ)))) ≤ δ := by
      have hexp_eq : (2 : ℝ) ^ ℓ * ((Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k *
          Real.exp (-ε * ((m : ℝ) - (k : ℝ)))) =
          Real.exp ((ℓ : ℝ) * Real.log 2 +
            (k : ℝ) * Real.log (Real.exp 1 * (m : ℝ) / (k : ℝ)) -
            ε * ((m : ℝ) - (k : ℝ))) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log (by positivity)]
        simp [div_eq_mul_inv, Real.exp_neg, mul_assoc]
      rw [hexp_eq, ← Real.exp_log hδ0]
      refine Real.exp_le_exp.mpr ?_
      have hk_mul : (k : ℝ) * Real.log (Real.exp 1 * (m : ℝ) / (k : ℝ)) ≤
          ε * (m : ℝ) / 2 + (k : ℝ) * Real.log (2 / ε) := by
        have := mul_le_mul_of_nonneg_left hlog_emk hk_pos.le
        have hcancel : (k : ℝ) * (ε * (m : ℝ) / (2 * (k : ℝ))) = ε * (m : ℝ) / 2 := by
          field_simp [hk_pos.ne']
        linarith
      have hεk : ε * (k : ℝ) ≤ 2 * (k : ℝ) * Real.log (2 / ε) := by
        have h1 : (1 : ℝ) < 2 / ε := (one_lt_div hε0).mpr (by linarith)
        have hlog2_le : Real.log 2 ≤ Real.log (2 / ε) :=
          Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε0]; nlinarith)
        nlinarith
      have hlogδ : Real.log δ⁻¹ = -Real.log δ := Real.log_inv δ
      have hℓ_nn : 0 ≤ (ℓ : ℝ) * Real.log 2 := by positivity
      linarith
    calc (2 : ℝ) ^ ℓ *
          ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * Real.exp (-ε * ((m : ℝ) - (i : ℝ)))
        ≤ (2 : ℝ) ^ ℓ * ((∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ)) *
            Real.exp (-ε * ((m : ℝ) - (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ ≤ (2 : ℝ) ^ ℓ * ((Real.exp 1 * (m : ℝ) / (k : ℝ)) ^ k *
            Real.exp (-ε * ((m : ℝ) - (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hbin (Real.exp_pos _).le) (by positivity)
      _ ≤ δ := h2

end CslibFrontier.MachineLearning.PACLearning
