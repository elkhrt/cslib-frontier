module

public import CslibFrontier.Probability.CorrelatedSampling
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.MutualInformation
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Probability.StatisticalDistance.Event
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Base-2 Kullback–Leibler Divergence, Tail Bounds, and Threshold-Exact Finite Samplers

This module develops reusable information-theoretic identities and finite-support sampling tools
for discrete probability distributions (`PMF`):

* **Statistical distance as supremum event gap** (`dist_eq_iSup_finset`): on any finite type,
  `dist p q = ⨆ s : Finset α, |p(s) - q(s)|`.
* **Base-2 Kullback–Leibler divergence** (`klDivBitsReal`): finite-sum KL divergence in bits,
  bridged to Mathlib's `InformationTheory.klDiv` (`klDivBitsReal_eq_toReal_klDiv_div_log`),
  together with Gibbs' inequality and its equality characterization (`klDivBitsReal_nonneg`,
  `klDivBitsReal_eq_zero_iff`).
* **Expected divergence identities** (`mutualInfo_eq_sum_klDivBits`,
  `condMutualInfo_eq_sum_mutualInfo`, `condMutualInfo_eq_sum_klDivBits`): mutual information and
  conditional mutual information expressed as expected base-2 KL divergence between conditional
  and marginal laws.
* **Likelihood-ratio tail bound from KL divergence** (`klDiv_tail_lt`): if `D₂(p ‖ q) ≤ I` and
  `ε > 0`, then `p {x | 2 ^ ((I + 1) / ε) * q(x) < p(x)} < ε`.
* **Threshold-exact finite cell sampler** (`thresholdPMF`, `thresholdPMF_toOuterMeasure_le`,
  `thresholdPMF_toOuterMeasure_le_and_le`): given a finite threshold set `T ⊆ [0, K]` containing
  `K > 0`, constructs a finite-support `PMF` over `T` whose cumulative distribution satisfies
  `Pr[a ≤ p] = p / K` and `Pr[a ≤ p ∧ a ≤ q] = min p q / K` identically for all `p, q ∈ T`.
-/

public section

namespace CslibFrontier.Probability.Divergence

open Finset MeasureTheory InformationTheory Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal NNReal

/-! ### Statistical distance as maximum event gap -/

/-- The statistical distance between two finite distributions equals the supremum over all
finite events of the absolute difference in event probabilities. -/
theorem dist_eq_iSup_finset {α : Type*} [Fintype α] (p q : PMF α) :
    dist p q = ⨆ s : Finset α,
      |(p.toOuterMeasure (s : Set α)).toReal - (q.toOuterMeasure (s : Set α)).toReal| := by
  classical
  refine le_antisymm ?_ ?_
  · let s : Finset α := Finset.univ.filter fun a => (q a).toReal < (p a).toReal
    have hs : dist p q =
        (p.toOuterMeasure (s : Set α)).toReal - (q.toOuterMeasure (s : Set α)).toReal := by
      rw [dist_eq_sum_filter_lt, toOuterMeasure_apply_toReal, toOuterMeasure_apply_toReal,
        ← Finset.sum_sub_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> ring
    have hle : dist p q ≤
        |(p.toOuterMeasure (s : Set α)).toReal - (q.toOuterMeasure (s : Set α)).toReal| :=
      hs ▸ le_abs_self _
    exact hle.trans (le_ciSup
      (f := fun t : Finset α =>
        |(p.toOuterMeasure (t : Set α)).toReal - (q.toOuterMeasure (t : Set α)).toReal|)
      (Set.finite_range _).bddAbove s)
  · exact ciSup_le fun s => abs_toOuterMeasure_toReal_sub_le_dist p q (s : Set α)

/-! ### Base-2 Kullback–Leibler divergence -/

/-- Base-2 Kullback–Leibler divergence (in bits) of two finite distributions:
`D₂(p ‖ q) = ∑ x, p(x) * log₂(p(x) / q(x))`.
When `p.support ⊆ q.support`, this equals
`(InformationTheory.klDiv p.toMeasure q.toMeasure).toReal / Real.log 2`. -/
noncomputable def klDivBitsReal {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal)

/-- When `p.support ⊆ q.support`, `klDivBitsReal p q` equals Mathlib's `klDiv` converted from
nats to bits. -/
theorem klDivBitsReal_eq_toReal_klDiv_div_log {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    klDivBitsReal p q = (klDiv p.toMeasure q.toMeasure).toReal / Real.log 2 := by
  rw [toReal_klDiv_toMeasure h, klDivBitsReal, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Real.logb, mul_div_assoc]

/-- Gibbs' inequality in bits: `0 ≤ klDivBitsReal p q` whenever `p.support ⊆ q.support`. -/
theorem klDivBitsReal_nonneg {α : Type*} [Fintype α] {p q : PMF α}
    (h : p.support ⊆ q.support) : 0 ≤ klDivBitsReal p q := by
  let : MeasurableSpace α := ⊤
  rw [klDivBitsReal_eq_toReal_klDiv_div_log h]
  exact div_nonneg ENNReal.toReal_nonneg (Real.log_nonneg (by norm_num))

/-- Equality case of Gibbs' inequality in bits: `klDivBitsReal p q = 0 ↔ p = q`. -/
theorem klDivBitsReal_eq_zero_iff {α : Type*} [Fintype α] {p q : PMF α}
    (h : p.support ⊆ q.support) : klDivBitsReal p q = 0 ↔ p = q := by
  have hsum : klDivBitsReal p q =
      (∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) / Real.log 2 := by
    rw [klDivBitsReal, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.logb, mul_div_assoc]
  rw [hsum, div_eq_zero_iff, or_iff_left (Real.log_pos (by norm_num)).ne']
  exact sum_mul_log_div_eq_zero_iff h

/-! ### Mutual information and conditional mutual information as expected divergence -/

/-- For any supported `a`, the conditional distribution `B | A = a` has support contained in
the marginal distribution of `B`. -/
theorem support_conditionalSnd_subset_map_snd {α β : Type*} (joint : PMF (α × β))
    {a : α} (ha : a ∈ (joint.map Prod.fst).support) :
    (conditionalSnd joint a).support ⊆ (joint.map Prod.snd).support := by
  intro b hb
  have hab : (a, b) ∈ joint.support := (mem_support_conditionalSnd_iff joint a ha b).mp hb
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(a, b), hab, rfl⟩

/-- Mutual information expanded in terms of entropies. -/
private theorem mutualInfo_eq_sub {α β : Type*} [Finite α] [Finite β] (p : PMF (α × β)) :
    mutualInfo p = entropy (p.map Prod.fst) + entropy (p.map Prod.snd) - entropy p := by
  have h := mutualInfo_map p Prod.fst Prod.snd
  have hid : (p.map fun ω : α × β => (ω.1, ω.2)) = p := PMF.map_id p
  simpa [hid] using h

/-- Conditional entropy expanded as joint entropy minus conditioning entropy. -/
private theorem conditionalEntropy_eq_sub {α β : Type*} [Finite α] [Finite β] (p : PMF (α × β)) :
    conditionalEntropy p = entropy p - entropy (p.map Prod.fst) := by
  have h1 := mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy p
  have h2 := mutualInfo_eq_sub p
  linarith

/-- Conditional mutual information expanded in terms of entropies. -/
private theorem condMutualInfo_eq_sub {γ α β : Type*} [Finite γ] [Finite α] [Finite β]
    (joint : PMF (γ × α × β)) :
    condMutualInfo joint =
      entropy (joint.map (Prod.map id Prod.fst)) + entropy (joint.map (Prod.map id Prod.snd)) -
        entropy joint - entropy (joint.map Prod.fst) := by
  have h := condMutualInfo_map joint Prod.fst (fun q => q.2.1) (fun q => q.2.2)
  have hid : (joint.map fun ω : γ × α × β => (ω.1, ω.2.1, ω.2.2)) = joint := PMF.map_id joint
  have hf : (fun ω : γ × α × β => (ω.1, ω.2.1)) = Prod.map id Prod.fst := rfl
  have hs : (fun ω : γ × α × β => (ω.1, ω.2.2)) = Prod.map id Prod.snd := rfl
  rw [hid, hf, hs] at h
  exact h

/-- Mutual information equals expected base-2 KL divergence from the marginal:
`I(A; B) = ∑ a, P(A = a) * D₂(B | A = a ‖ B)`. -/
theorem mutualInfo_eq_sum_klDivBits {α β : Type*} [Fintype α] [Fintype β]
    (joint : PMF (α × β)) :
    mutualInfo joint =
      ∑ a, ((joint.map Prod.fst) a).toReal *
        klDivBitsReal (conditionalSnd joint a) (joint.map Prod.snd) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  rw [mutualInfo_eq_sub, entropy_map_fst_add_entropy_map_snd_sub_entropy, ← toMeasure_bind_pair,
    toReal_klDiv_toMeasure (support_subset_bind_map_prodMk joint), Finset.sum_div,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [klDivBitsReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : joint (a, b) = 0
  · have hmul : ((joint.map Prod.fst) a).toReal * (conditionalSnd joint a b).toReal = 0 := by
      rw [← ENNReal.toReal_mul, marginal_mul_conditionalSnd, hab, ENNReal.toReal_zero]
    rw [hab, ENNReal.toReal_zero, zero_mul, zero_div, ← mul_assoc, hmul, zero_mul]
  · have ha : a ∈ (joint.map Prod.fst).support := by
      rw [PMF.mem_support_iff]
      intro h0
      exact hab (le_antisymm (h0 ▸ apply_le_map_fst joint a b) bot_le)
    have hprod : ((joint.map Prod.fst).bind fun x => (joint.map Prod.snd).map (x, ·)) (a, b) =
        (joint.map Prod.fst) a * (joint.map Prod.snd) b :=
      bind_map_prodMk_apply _ _ (a, b)
    have hpa_pos : (0 : ℝ) < ((joint.map Prod.fst) a).toReal :=
      ENNReal.toReal_pos ha (PMF.apply_ne_top _ _)
    have hrat : (conditionalSnd joint a b).toReal / ((joint.map Prod.snd) b).toReal =
        (joint (a, b)).toReal /
          (((joint.map Prod.fst) a).toReal * ((joint.map Prod.snd) b).toReal) := by
      rw [conditionalSnd_apply joint a ha b, ENNReal.toReal_div, div_div, mul_comm]
    have hmc : ((joint.map Prod.fst) a).toReal * (conditionalSnd joint a b).toReal =
        (joint (a, b)).toReal := by
      rw [← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
    rw [hprod, ENNReal.toReal_mul, ← mul_assoc, hmc, hrat, Real.logb, ← mul_div_assoc]

/-- Conditioning first on `C` and then on `A` agrees with conditioning jointly on `(C, A)`. -/
theorem conditionalSnd_conditionalSnd_eq {γ α β : Type*} (joint : PMF (γ × α × β))
    {c : γ} {a : α} (hca : (c, a) ∈ (joint.map (Prod.map id Prod.fst)).support) :
    conditionalSnd (conditionalSnd joint c) a =
      conditionalSnd (joint.map (Equiv.prodAssoc γ α β).symm) (c, a) := by
  have hc : c ∈ (joint.map Prod.fst).support := by
    obtain ⟨⟨c', a', b'⟩, hmem, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hca
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at heq
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(c', a', b'), hmem, heq.1⟩
  have hmap_fst : (conditionalSnd joint c).map Prod.fst =
      conditionalSnd (joint.map (Prod.map id Prod.fst)) c := by
    ext a'
    rw [map_fst_apply, conditionalSnd_apply _ c (by simpa [PMF.map_comp] using hc)]
    have hca_eq : (joint.map (Prod.map id Prod.fst)) (c, a') = ∑' b, joint (c, a', b) := by
      have : joint.map (Prod.map id Prod.fst) =
          (joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst := by
        rw [PMF.map_comp]; rfl
      rw [this, map_fst_apply]
      refine tsum_congr fun b => ?_
      rw [map_equiv_apply]
      rfl
    have hfst_eq :
        ((joint.map (Prod.map id Prod.fst)).map Prod.fst) c = (joint.map Prod.fst) c := by
      rw [PMF.map_comp]; rfl
    rw [hfst_eq, hca_eq, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun b => ?_
    rw [conditionalSnd_apply joint c hc (a', b), div_eq_mul_inv]
  have ha_supp : a ∈ ((conditionalSnd joint c).map Prod.fst).support := by
    rw [hmap_fst]
    exact (mem_support_conditionalSnd_iff _ c (by simpa [PMF.map_comp] using hc) a).mpr hca
  have hca_assoc : (c, a) ∈ ((joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst).support := by
    have : (joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst =
        joint.map (Prod.map id Prod.fst) := by
      rw [PMF.map_comp]; rfl
    rwa [this]
  ext b
  rw [conditionalSnd_apply _ a ha_supp b, conditionalSnd_apply _ (c, a) hca_assoc b,
    conditionalSnd_apply joint c hc (a, b), hmap_fst,
    conditionalSnd_apply _ c (by simpa [PMF.map_comp] using hc) a]
  have h1 : (joint.map (Equiv.prodAssoc γ α β).symm) ((c, a), b) = joint (c, a, b) := by
    rw [map_equiv_apply]; rfl
  have h2 : ((joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst) (c, a) =
      (joint.map (Prod.map id Prod.fst)) (c, a) := by
    rw [PMF.map_comp]; rfl
  have h3 : ((joint.map (Prod.map id Prod.fst)).map Prod.fst) c = (joint.map Prod.fst) c := by
    rw [PMF.map_comp]; rfl
  rw [h1, h2, h3]
  have hc0 : (joint.map Prod.fst) c ≠ 0 := hc
  have hc_top : (joint.map Prod.fst) c ≠ ⊤ := PMF.apply_ne_top _ _
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hc_top))
      (Or.inl (ENNReal.inv_ne_top.mpr hc0)), inv_inv]
  calc
    (joint.map Prod.fst) c * ((joint.map (Prod.map id Prod.fst)) (c, a))⁻¹ *
        (((joint.map Prod.fst) c)⁻¹ * joint (c, a, b))
      = ((joint.map (Prod.map id Prod.fst)) (c, a))⁻¹ *
          ((joint.map Prod.fst) c * ((joint.map Prod.fst) c)⁻¹) * joint (c, a, b) := by ring
    _ = ((joint.map (Prod.map id Prod.fst)) (c, a))⁻¹ * joint (c, a, b) := by
        rw [ENNReal.mul_inv_cancel hc0 hc_top, mul_one]

/-- Marginalizing `A` out of `(A, B) | C = c` gives `B | C = c`. -/
theorem map_snd_conditionalSnd_eq {γ α β : Type*} (joint : PMF (γ × α × β))
    {c : γ} (hc : c ∈ (joint.map Prod.fst).support) :
    (conditionalSnd joint c).map Prod.snd =
      conditionalSnd (joint.map (Prod.map id Prod.snd)) c := by
  have hc' : c ∈ ((joint.map (Prod.map id Prod.snd)).map Prod.fst).support := by
    simpa [PMF.map_comp] using hc
  ext b
  rw [PMF.map_apply, conditionalSnd_apply _ c hc' b]
  have hfst : ((joint.map (Prod.map id Prod.snd)).map Prod.fst) c = (joint.map Prod.fst) c := by
    rw [PMF.map_comp]; rfl
  have hcb : (joint.map (Prod.map id Prod.snd)) (c, b) = ∑' a, joint (c, a, b) := by
    let e : γ × α × β ≃ (γ × β) × α :=
      ((Equiv.refl γ).prodCongr (Equiv.prodComm α β)).trans (Equiv.prodAssoc γ β α).symm
    have he : joint.map (Prod.map id Prod.snd) = (joint.map e).map Prod.fst := by
      rw [PMF.map_comp]; rfl
    rw [he, map_fst_apply]
    refine tsum_congr fun a => ?_
    rw [map_equiv_apply]
    rfl
  rw [hfst, hcb, div_eq_mul_inv, ← ENNReal.tsum_mul_right, tsum_prod']
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single b]
  · simp [conditionalSnd_apply joint c hc (a, b), div_eq_mul_inv]
  · intro b' hb'
    simp [Ne.symm hb']

/-- Conditional mutual information decomposes as the average over `C` of the conditional
mutual information `I(A; B | C = c)`. -/
theorem condMutualInfo_eq_sum_mutualInfo {γ α β : Type*} [Fintype γ] [Finite α] [Finite β]
    (joint : PMF (γ × α × β)) :
    condMutualInfo joint =
      ∑ c, ((joint.map Prod.fst) c).toReal * mutualInfo (conditionalSnd joint c) := by
  have hCA : conditionalEntropy (joint.map (Prod.map id Prod.fst)) =
      ∑ c, ((joint.map Prod.fst) c).toReal * entropy ((conditionalSnd joint c).map Prod.fst) := by
    rw [conditionalEntropy_eq_sum]
    have hfst : (joint.map (Prod.map id Prod.fst)).map Prod.fst = joint.map Prod.fst := by
      rw [PMF.map_comp]; rfl
    rw [hfst]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c ∈ (joint.map Prod.fst).support
    · congr 2
      ext a
      rw [map_fst_apply, conditionalSnd_apply _ c (by rwa [hfst])]
      have hca : (joint.map (Prod.map id Prod.fst)) (c, a) = ∑' b, joint (c, a, b) := by
        have : joint.map (Prod.map id Prod.fst) =
            (joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst := by
          rw [PMF.map_comp]; rfl
        rw [this, map_fst_apply]
        exact tsum_congr fun b => by rw [map_equiv_apply]; rfl
      rw [hfst, hca, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      exact (tsum_congr fun b => by
        rw [conditionalSnd_apply joint c hc (a, b), div_eq_mul_inv]).symm
    · rw [(PMF.apply_eq_zero_iff _ c).mpr hc, ENNReal.toReal_zero, zero_mul, zero_mul]
  have hCB : conditionalEntropy (joint.map (Prod.map id Prod.snd)) =
      ∑ c, ((joint.map Prod.fst) c).toReal * entropy ((conditionalSnd joint c).map Prod.snd) := by
    rw [conditionalEntropy_eq_sum]
    have hfst : (joint.map (Prod.map id Prod.snd)).map Prod.fst = joint.map Prod.fst := by
      rw [PMF.map_comp]; rfl
    rw [hfst]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c ∈ (joint.map Prod.fst).support
    · rw [map_snd_conditionalSnd_eq joint hc]
    · rw [(PMF.apply_eq_zero_iff _ c).mpr hc, ENNReal.toReal_zero, zero_mul, zero_mul]
  have hCAB : conditionalEntropy joint =
      ∑ c, ((joint.map Prod.fst) c).toReal * entropy (conditionalSnd joint c) :=
    conditionalEntropy_eq_sum joint
  have hdiff : condMutualInfo joint =
      conditionalEntropy (joint.map (Prod.map id Prod.fst)) +
        conditionalEntropy (joint.map (Prod.map id Prod.snd)) -
        conditionalEntropy joint := by
    have h1 : (joint.map (Prod.map id Prod.fst)).map Prod.fst = joint.map Prod.fst := by
      rw [PMF.map_comp]; rfl
    have h2 : (joint.map (Prod.map id Prod.snd)).map Prod.fst = joint.map Prod.fst := by
      rw [PMF.map_comp]; rfl
    rw [condMutualInfo_eq_sub, conditionalEntropy_eq_sub, conditionalEntropy_eq_sub,
      conditionalEntropy_eq_sub, h1, h2]
    ring
  rw [hdiff, hCA, hCB, hCAB, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mutualInfo_eq_sub]
  ring

/-- Conditional mutual information equals the expected base-2 KL divergence between
`B | (A = a, C = c)` and `B | (C = c)`: `I(A; B | C) = 𝔼_{a, c} [D₂(B_{a,c} ‖ B_c)]`. -/
theorem condMutualInfo_eq_sum_klDivBits {γ α β : Type*} [Fintype γ] [Fintype α] [Fintype β]
    (joint : PMF (γ × α × β)) :
    condMutualInfo joint =
      ∑ c, ∑ a, ((joint.map (Prod.map id Prod.fst)) (c, a)).toReal *
        klDivBitsReal
          (conditionalSnd (joint.map (Equiv.prodAssoc γ α β).symm) (c, a))
          (conditionalSnd (joint.map (Prod.map id Prod.snd)) c) := by
  rw [condMutualInfo_eq_sum_mutualInfo]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : c ∈ (joint.map Prod.fst).support
  · rw [mutualInfo_eq_sum_klDivBits, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hmul : ((joint.map Prod.fst) c).toReal *
        (((conditionalSnd joint c).map Prod.fst) a).toReal =
        ((joint.map (Prod.map id Prod.fst)) (c, a)).toReal := by
      rw [← ENNReal.toReal_mul]
      congr 1
      have hmap : (conditionalSnd joint c).map Prod.fst =
          conditionalSnd (joint.map (Prod.map id Prod.fst)) c := by
        ext a'
        rw [map_fst_apply, conditionalSnd_apply _ c (by simpa [PMF.map_comp] using hc)]
        have hca : (joint.map (Prod.map id Prod.fst)) (c, a') = ∑' b, joint (c, a', b) := by
          have : joint.map (Prod.map id Prod.fst) =
              (joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst := by
            rw [PMF.map_comp]; rfl
          rw [this, map_fst_apply]
          exact tsum_congr fun b => by rw [map_equiv_apply]; rfl
        have hfst : ((joint.map (Prod.map id Prod.fst)).map Prod.fst) c =
            (joint.map Prod.fst) c := by
          rw [PMF.map_comp]; rfl
        rw [hfst, hca, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun b => by rw [conditionalSnd_apply joint c hc (a', b), div_eq_mul_inv]
      rw [hmap]
      have hfst : (joint.map (Prod.map id Prod.fst)).map Prod.fst = joint.map Prod.fst := by
        rw [PMF.map_comp]; rfl
      simpa [hfst] using marginal_mul_conditionalSnd (joint.map (Prod.map id Prod.fst)) c a
    rw [← mul_assoc, hmul]
    by_cases hca : (c, a) ∈ (joint.map (Prod.map id Prod.fst)).support
    · rw [conditionalSnd_conditionalSnd_eq joint hca, map_snd_conditionalSnd_eq joint hc]
    · rw [(PMF.apply_eq_zero_iff _ (c, a)).mpr hca, ENNReal.toReal_zero, zero_mul, zero_mul]
  · have hc0 : (joint.map Prod.fst) c = 0 := (PMF.apply_eq_zero_iff _ c).mpr hc
    rw [hc0, ENNReal.toReal_zero, zero_mul]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    have hca0 : (joint.map (Prod.map id Prod.fst)) (c, a) = 0 := by
      have hfst : ((joint.map (Prod.map id Prod.fst)).map Prod.fst) c = 0 := by
        rw [PMF.map_comp]; exact hc0
      exact le_antisymm (hfst ▸ apply_le_map_fst (joint.map (Prod.map id Prod.fst)) c a) bot_le
    rw [hca0, ENNReal.toReal_zero, zero_mul]

/-! ### Likelihood-ratio tail bound from KL divergence -/

/-- For every `t ≥ 0`, `t * log₂ t ≥ -1 / (2 * log 2) > -1`. -/
private theorem neg_inv_two_log_two_le_mul_logb {t : ℝ} (ht : 0 ≤ t) :
    -(1 / (2 * Real.log 2)) ≤ t * Real.logb 2 t := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp only [zero_mul, neg_nonpos]
    positivity
  · have hu : 0 < 1 / (2 * t) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hu
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) ht_pos.ne'] at hlog
    have hmul : t * (-(Real.log 2 + Real.log t)) ≤ t * ((2 * t)⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left hlog ht_pos.le
    have hsimp : t * ((2 * t)⁻¹ - 1) = 1 / 2 - t := by
      field_simp [ht_pos.ne']
    have hlog_lt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hnat : -(1 / 2 : ℝ) ≤ t * Real.log t := by nlinarith
    rw [Real.logb, ← mul_div_assoc]
    calc
      -(1 / (2 * Real.log 2)) = -(1 / 2) / Real.log 2 := by ring
      _ ≤ (t * Real.log t) / Real.log 2 := div_le_div_of_nonneg_right hnat hlog2_pos.le

/-- Exponential likelihood-ratio tail bound from KL divergence: if `D₂(p ‖ q) ≤ I` (in bits)
and `ε > 0`, then `p {x | 2 ^ ((I + 1) / ε) * q(x) < p(x)} < ε`. -/
theorem klDiv_tail_lt {α : Type*} [Fintype α] {p q : PMF α} {I ε : ℝ}
    (hsupp : p.support ⊆ q.support) (hdiv : klDivBitsReal p q ≤ I) (hε : 0 < ε) :
    (p.toOuterMeasure {x | (2 : ℝ) ^ ((I + 1) / ε) * (q x).toReal < (p x).toReal}).toReal <
      ε := by
  classical
  have hI_nonneg : 0 ≤ I := (klDivBitsReal_nonneg hsupp).trans hdiv
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_pos : 0 < Real.log 2 := by linarith
  let L : Finset α :=
    Finset.univ.filter fun x => (2 : ℝ) ^ ((I + 1) / ε) * (q x).toReal < (p x).toReal
  let N : Finset α := Finset.univ.filter fun x => (p x).toReal < (q x).toReal
  have hdisj : Disjoint L N := by
    rw [Finset.disjoint_left]
    intro x hxL hxN
    simp only [L, N, Finset.mem_filter, Finset.mem_univ, true_and] at hxL hxN
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ ((I + 1) / ε) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hq_nonneg : 0 ≤ (q x).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hterm_L : ∀ x ∈ L,
      (p x).toReal * ((I + 1) / ε) ≤
        (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
    intro x hx
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((I + 1) / ε) := Real.rpow_pos_of_pos (by norm_num) _
    have hp_pos : 0 < (p x).toReal :=
      lt_of_le_of_lt (mul_nonneg hpow_pos.le ENNReal.toReal_nonneg) hx
    have hp_supp : x ∈ p.support :=
      (PMF.mem_support_iff p x).mpr (ENNReal.toReal_pos_iff.mp hp_pos).1.ne'
    have hq_pos : 0 < (q x).toReal := ENNReal.toReal_pos (hsupp hp_supp) (PMF.apply_ne_top _ _)
    have hrat : (2 : ℝ) ^ ((I + 1) / ε) < (p x).toReal / (q x).toReal :=
      (lt_div_iff₀ hq_pos).mpr (by linarith)
    have hlogb : (I + 1) / ε ≤ Real.logb 2 ((p x).toReal / (q x).toReal) := by
      have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
        (div_pos hp_pos hq_pos)).mpr hrat.le
      exact this
    exact mul_le_mul_of_nonneg_left hlogb hp_pos.le
  have hterm_N : ∀ x ∈ N,
      -(1 / (2 * Real.log 2)) * (q x).toReal ≤
        (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
    intro x hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hq_pos : 0 < (q x).toReal := lt_of_le_of_lt ENNReal.toReal_nonneg hx
    have ht : 0 ≤ (p x).toReal / (q x).toReal := div_nonneg ENNReal.toReal_nonneg hq_pos.le
    have hbound := neg_inv_two_log_two_le_mul_logb ht
    have hmul := mul_le_mul_of_nonneg_right hbound hq_pos.le
    have hsimp : (p x).toReal / (q x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) *
        (q x).toReal = (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
      field_simp [hq_pos.ne']
    linarith
  have hterm_rest : ∀ x ∉ L ∪ N,
      0 ≤ (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
    intro x hx
    have hxN : x ∉ N := fun h => hx (Finset.mem_union_right _ h)
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hxN
    by_cases hp0 : (p x).toReal = 0
    · simp [hp0]
    · have hp_pos : 0 < (p x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp0)
      have hp_supp : x ∈ p.support :=
        (PMF.mem_support_iff p x).mpr (ENNReal.toReal_pos_iff.mp hp_pos).1.ne'
      have hq_pos : 0 < (q x).toReal := ENNReal.toReal_pos (hsupp hp_supp) (PMF.apply_ne_top _ _)
      have hge1 : (1 : ℝ) ≤ (p x).toReal / (q x).toReal := (one_le_div hq_pos).mpr hxN
      exact mul_nonneg hp_pos.le (Real.logb_nonneg (by norm_num) hge1)
  have hsum_split :
      (∑ x ∈ L, (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal)) +
        (∑ x ∈ N, (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal)) ≤
      klDivBitsReal p q := by
    rw [klDivBitsReal, ← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ hx =>
      hterm_rest x hx
  have hsum_L : (∑ x ∈ L, (p x).toReal) * ((I + 1) / ε) ≤
      ∑ x ∈ L, (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm_L
  have hsum_N : -(1 / (2 * Real.log 2)) <
      ∑ x ∈ N, (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) ∨
      -(1 / (2 * Real.log 2)) ≤
      ∑ x ∈ N, (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
    right
    calc
      -(1 / (2 * Real.log 2)) = -(1 / (2 * Real.log 2)) * 1 := by ring
      _ ≤ -(1 / (2 * Real.log 2)) * ∑ x ∈ N, (q x).toReal := by
          have hqle : ∑ x ∈ N, (q x).toReal ≤ 1 := by
            calc ∑ x ∈ N, (q x).toReal ≤ ∑ x : α, (q x).toReal :=
                  Finset.sum_le_univ_sum_of_nonneg fun _ => ENNReal.toReal_nonneg
              _ = 1 := sum_toReal q
          have hneg : -(1 / (2 * Real.log 2)) ≤ 0 := by
            simp only [neg_nonpos]; positivity
          exact mul_le_mul_of_nonpos_left hqle hneg
      _ = ∑ x ∈ N, -(1 / (2 * Real.log 2)) * (q x).toReal := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum hterm_N
  have hN_gt : (-1 : ℝ) < ∑ x ∈ N, (p x).toReal * Real.logb 2 ((p x).toReal / (q x).toReal) := by
    have hconst : (-1 : ℝ) < -(1 / (2 * Real.log 2)) := by
      have : (1 : ℝ) / (2 * Real.log 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    rcases hsum_N with h | h <;> linarith
  have hmeas : (p.toOuterMeasure
      {x | (2 : ℝ) ^ ((I + 1) / ε) * (q x).toReal < (p x).toReal}).toReal =
      ∑ x ∈ L, (p x).toReal := by
    rw [toOuterMeasure_apply_toReal, ← Finset.sum_filter]
    rfl
  rw [hmeas]
  have hlt : (∑ x ∈ L, (p x).toReal) * ((I + 1) / ε) < I + 1 := by linarith
  have hI1 : 0 < I + 1 := by linarith
  have hmul_lt : (∑ x ∈ L, (p x).toReal) * (I + 1) < ε * (I + 1) := by
    have := (mul_lt_mul_iff_left₀ hε).mpr hlt
    have hcancel : (∑ x ∈ L, (p x).toReal) * ((I + 1) / ε) * ε =
        (∑ x ∈ L, (p x).toReal) * (I + 1) := by
      field_simp [hε.ne']
    linarith
  exact (mul_lt_mul_iff_left₀ hI1).mp hmul_lt

/-! ### Threshold-exact finite cell sampler -/

/-- A finite distribution on a threshold set `T ⊆ [0, K]` (containing `K > 0`) assigning each
`v ∈ T` probability `(v - predIn T v) / K`, so that `Pr[α ≤ v] = v / K` holds identically at
every threshold `v ∈ T`. -/
noncomputable def thresholdPMF (K : ℝ≥0) (hK : 0 < K) (T : Finset ℝ≥0) (hKT : K ∈ T)
    (hle : ∀ v ∈ T, v ≤ K) : PMF {v : ℝ≥0 // v ∈ T} :=
  PMF.ofFintype
    (fun v => (((v.1 - CorrelatedSampling.predIn T v.1 : ℝ≥0) : ℝ≥0∞) / (K : ℝ≥0∞)))
    (by
      have hsup : T.sup id = K :=
        le_antisymm (Finset.sup_le fun v hv => hle v hv) (Finset.le_sup (f := id) hKT)
      have hsum : ∑ v : {v : ℝ≥0 // v ∈ T}, (v.1 - CorrelatedSampling.predIn T v.1 : ℝ≥0) = K := by
        rw [Finset.univ_eq_attach,
          Finset.sum_attach (f := fun v => v - CorrelatedSampling.predIn T v)]
        exact (CorrelatedSampling.sum_sub_predIn T).trans hsup
      rw [← ENNReal.sum_div, ← ENNReal.ofNNReal_finsetSum, hsum]
      exact ENNReal.div_self (ENNReal.coe_ne_zero.mpr hK.ne') ENNReal.coe_ne_top)

/-- Under `thresholdPMF K hK T hKT hle`, the probability that a draw is at most any threshold
`p ∈ T` is exactly `p / K`. -/
theorem thresholdPMF_toOuterMeasure_le (K : ℝ≥0) (hK : 0 < K) (T : Finset ℝ≥0) (hKT : K ∈ T)
    (hle : ∀ v ∈ T, v ≤ K) {p : ℝ≥0} (hp : p ∈ T) :
    ((thresholdPMF K hK T hKT hle).toOuterMeasure {a | a.1 ≤ p}).toReal = (p : ℝ) / (K : ℝ) := by
  classical
  rw [toOuterMeasure_apply_toReal]
  trans (∑ a : {v : ℝ≥0 // v ∈ T},
    if a.1 ≤ p then ((a.1 - CorrelatedSampling.predIn T a.1 : ℝ≥0) : ℝ) / (K : ℝ) else 0)
  · refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h1 h2 h2
    · simp only [thresholdPMF, PMF.ofFintype_apply, ENNReal.toReal_div, ENNReal.coe_toReal]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  rw [← Finset.sum_filter]
  have hdiv : ∑ a ∈ Finset.univ.filter (fun a : {v : ℝ≥0 // v ∈ T} => a.1 ≤ p),
      ((a.1 - CorrelatedSampling.predIn T a.1 : ℝ≥0) : ℝ) / (K : ℝ) =
      (∑ a ∈ Finset.univ.filter (fun a : {v : ℝ≥0 // v ∈ T} => a.1 ≤ p),
        ((a.1 - CorrelatedSampling.predIn T a.1 : ℝ≥0) : ℝ)) / (K : ℝ) := by
    rw [Finset.sum_div]
  rw [hdiv]
  congr 1
  have hfilt : ∑ a ∈ Finset.univ.filter (fun a : {v : ℝ≥0 // v ∈ T} => a.1 ≤ p),
      (a.1 - CorrelatedSampling.predIn T a.1 : ℝ≥0) =
      ∑ v ∈ T.filter (· ≤ p), (v - CorrelatedSampling.predIn T v) := by
    rw [Finset.univ_eq_attach]
    refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a₁ _ a₂ _ h => Subtype.ext h)
      (fun v hv => ⟨⟨v, (Finset.mem_filter.mp hv).1⟩, ?_, rfl⟩) (fun _ _ => rfl)
    · exact Finset.mem_filter.mpr ⟨a.2, (Finset.mem_filter.mp ha).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp hv).2⟩
  rw [← NNReal.coe_sum, hfilt, CorrelatedSampling.sum_filter_le_sub_predIn hp]

/-- Under `thresholdPMF`, the joint event `a ≤ p ∧ a ≤ q` for `p, q ∈ T` has probability
`min p q / K`. -/
theorem thresholdPMF_toOuterMeasure_le_and_le (K : ℝ≥0) (hK : 0 < K) (T : Finset ℝ≥0)
    (hKT : K ∈ T) (hle : ∀ v ∈ T, v ≤ K) {p q : ℝ≥0} (hp : p ∈ T) (hq : q ∈ T) :
    ((thresholdPMF K hK T hKT hle).toOuterMeasure {a | a.1 ≤ p ∧ a.1 ≤ q}).toReal =
      min (p : ℝ) (q : ℝ) / (K : ℝ) := by
  have heq : {a : {v : ℝ≥0 // v ∈ T} | a.1 ≤ p ∧ a.1 ≤ q} = {a | a.1 ≤ min p q} := by
    ext a
    simp [le_min_iff]
  have hmin : min p q ∈ T := by
    rcases min_choice p q with h | h <;> rw [h] <;> assumption
  rw [heq, thresholdPMF_toOuterMeasure_le K hK T hKT hle hmin, NNReal.coe_min]

end CslibFrontier.Probability.Divergence
