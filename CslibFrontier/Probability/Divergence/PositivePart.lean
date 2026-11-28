module

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.Conditioning
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.Divergence.Pi
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.MutualInformation
public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.BigOperators
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Base-2 Divergence, Positive-Part Log-Ratio Bounds, and Conditional Mutual Information Identities

This module provides reusable finite-PMF information-theoretic identities and inequalities in bits:
- Variational characterization of statistical distance as the supremum probability difference over
  finite events (`statDist_eq_iSup_event`).
- Conditional mutual information chain rule (`condMutualInfo_chain_rule`), symmetry
  (`condMutualInfo_map_comm`), monotonicity (`condMutualInfo_le_pair_right`), and exact
  representation as expected conditional base-2 Kullback–Leibler divergence
  (`condMutualInfo_eq_expect_klDivBits`).
- Base-2 KL divergence (`klDivBits`), product additivity (`klDivBits_prod`, `klDivBits_pi`), and
  the expected positive-part log-likelihood ratio (`klDivPosBits`) together with the sharp upper
  bound `klDivPosBits p q ≤ klDivBits p q + 1 / (Real.exp 1 * Real.log 2)`.
- Finite-PMF Jensen and Cauchy–Schwarz inequalities for square roots
  (`sum_mul_sqrt_le_sqrt_sum`, `sum_sqrt_le_sqrt_card_mul_sum`).

## Main definitions

* `CslibFrontier.Probability.Divergence.PositivePart.klDivBits`: base-2 KL divergence on finite
  PMFs.
* `CslibFrontier.Probability.Divergence.PositivePart.klDivPosBits`: expected positive part
  `∑ x, P(x) * max 0 (log₂(P(x) / Q(x)))`.
* `CslibFrontier.Probability.Divergence.PositivePart.prodPMF`: independent binary product PMF.

## Main results

* `CslibFrontier.Probability.Divergence.PositivePart.statDist_eq_iSup_event`
* `CslibFrontier.Probability.Divergence.PositivePart.condMutualInfo_chain_rule`
* `CslibFrontier.Probability.Divergence.PositivePart.condMutualInfo_eq_expect_klDivBits`
* `CslibFrontier.Probability.Divergence.PositivePart.klDivBits_prod`
* `CslibFrontier.Probability.Divergence.PositivePart.klDivBits_pi`
* `CslibFrontier.Probability.Divergence.PositivePart.klDivPosBits_le_add_const`
* `CslibFrontier.Probability.Divergence.PositivePart.sum_mul_sqrt_le_sqrt_sum`
* `CslibFrontier.Probability.Divergence.PositivePart.sum_sqrt_le_sqrt_card_mul_sum`
-/

public section

namespace CslibFrontier.Probability.Divergence.PositivePart

open Finset Cslib.Probability Cslib.Probability.PMF InformationTheory
open scoped BigOperators ENNReal NNReal

variable {α β γ δ Ω : Type*}

/-- For every subset `T`, the probability gap `|p(T) - q(T)|` is at most `dist p q`. -/
theorem abs_toOuterMeasure_sub_le_dist [Fintype α] (p q : PMF α) (T : Finset α) :
    |(p.toOuterMeasure (T : Set α)).toReal - (q.toOuterMeasure (T : Set α)).toReal| ≤
      dist p q := by
  classical
  have hp : (p.toOuterMeasure (T : Set α)).toReal = ∑ s ∈ T, (p s).toReal := by
    rw [toOuterMeasure_apply_toReal]
    simp [Finset.sum_ite_mem]
  have hq : (q.toOuterMeasure (T : Set α)).toReal = ∑ s ∈ T, (q s).toReal := by
    rw [toOuterMeasure_apply_toReal]
    simp [Finset.sum_ite_mem]
  rw [hp, hq, ← Finset.sum_sub_distrib]
  have hsum_all : ∑ s : α, ((p s).toReal - (q s).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, sum_toReal, sum_toReal, sub_self]
  have hcompl :
      ∑ s ∈ T, ((p s).toReal - (q s).toReal) =
        -(∑ s ∈ Tᶜ, ((p s).toReal - (q s).toReal)) := by
    have hadd := Finset.sum_add_sum_compl T (fun s => (p s).toReal - (q s).toReal)
    linarith
  have h1 : |∑ s ∈ T, ((p s).toReal - (q s).toReal)| ≤
      ∑ s ∈ T, |(p s).toReal - (q s).toReal| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : |∑ s ∈ T, ((p s).toReal - (q s).toReal)| ≤
      ∑ s ∈ Tᶜ, |(p s).toReal - (q s).toReal| := by
    rw [hcompl, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have htot := Finset.sum_add_sum_compl T (fun s => |(p s).toReal - (q s).toReal|)
  rw [Cslib.Probability.PMF.dist_eq]
  linarith

/-- Variational characterization of statistical distance as the supremum probability difference
over all events `T : Finset α`. -/
theorem statDist_eq_iSup_event [Fintype α] (p q : PMF α) :
    dist p q =
      ⨆ T : Finset α,
        |(p.toOuterMeasure (T : Set α)).toReal - (q.toOuterMeasure (T : Set α)).toReal| := by
  classical
  refine le_antisymm ?_ ?_
  · let Tpos : Finset α := Finset.univ.filter (fun s => (q s).toReal < (p s).toReal)
    have hval :
        dist p q =
          |(p.toOuterMeasure (Tpos : Set α)).toReal -
            (q.toOuterMeasure (Tpos : Set α)).toReal| := by
      have hp : (p.toOuterMeasure (Tpos : Set α)).toReal = ∑ s ∈ Tpos, (p s).toReal := by
        rw [toOuterMeasure_apply_toReal]
        simp [Finset.sum_ite_mem]
      have hq : (q.toOuterMeasure (Tpos : Set α)).toReal = ∑ s ∈ Tpos, (q s).toReal := by
        rw [toOuterMeasure_apply_toReal]
        simp [Finset.sum_ite_mem]
      rw [hp, hq, ← Finset.sum_sub_distrib,
        abs_of_nonneg (Finset.sum_nonneg fun s hs =>
          sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp hs).2)),
        dist_eq_sum_filter_lt]
    rw [hval]
    exact le_ciSup
      (f := fun T : Finset α =>
        |(p.toOuterMeasure (T : Set α)).toReal - (q.toOuterMeasure (T : Set α)).toReal|)
      (Set.finite_range _).bddAbove Tpos
  · exact ciSup_le fun T => abs_toOuterMeasure_sub_le_dist p q T

/-- Symmetry of conditional mutual information in its two arguments:
`I(A; B | C) = I(B; A | C)`. -/
theorem condMutualInfo_map_comm [Finite γ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map]
  have hswap :
      entropy (ν.map fun ω => (C ω, A ω, B ω)) =
        entropy (ν.map fun ω => (C ω, B ω, A ω)) := by
    refine entropy_map_eq_of_comp ν
      (e := fun t : γ × β × α => (t.1, t.2.2, t.2.1)) ?_ (fun _ _ => rfl)
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  rw [hswap]
  ring

/-- Chain rule for conditional mutual information:
`I((C₁, C₂); B | D) = I(C₁; B | D) + I(C₂; B | (C₁, D))`. -/
theorem condMutualInfo_chain_rule {C₁ C₂ B D : Type*}
    [Finite C₁] [Finite C₂] [Finite B] [Finite D]
    (ν : PMF Ω) (c₁ : Ω → C₁) (c₂ : Ω → C₂) (b : Ω → B) (d : Ω → D) :
    condMutualInfo (ν.map fun ω => (d ω, (c₁ ω, c₂ ω), b ω)) =
      condMutualInfo (ν.map fun ω => (d ω, c₁ ω, b ω)) +
        condMutualInfo (ν.map fun ω => ((c₁ ω, d ω), c₂ ω, b ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map, condMutualInfo_map]
  have e1 :
      entropy (ν.map fun ω => (d ω, c₁ ω, c₂ ω)) =
        entropy (ν.map fun ω => ((c₁ ω, d ω), c₂ ω)) := by
    refine entropy_map_eq_of_comp ν
      (e := fun t : (C₁ × D) × C₂ => (t.1.2, t.1.1, t.2)) ?_ (fun _ _ => rfl)
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have e2 :
      entropy (ν.map fun ω => (d ω, (c₁ ω, c₂ ω), b ω)) =
        entropy (ν.map fun ω => ((c₁ ω, d ω), c₂ ω, b ω)) := by
    refine entropy_map_eq_of_comp ν
      (e := fun t : (C₁ × D) × C₂ × B => (t.1.2, (t.1.1, t.2.1), t.2.2)) ?_ (fun _ _ => rfl)
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.2.1.1 h.1) (Prod.ext h.2.1.2 h.2.2)
  have e3 :
      entropy (ν.map fun ω => (d ω, c₁ ω)) =
        entropy (ν.map fun ω => (c₁ ω, d ω)) :=
    entropy_map_eq_of_comp ν (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl)
  have e4 :
      entropy (ν.map fun ω => (d ω, c₁ ω, b ω)) =
        entropy (ν.map fun ω => ((c₁ ω, d ω), b ω)) := by
    refine entropy_map_eq_of_comp ν
      (e := fun t : (C₁ × D) × B => (t.1.2, t.1.1, t.2)) ?_ (fun _ _ => rfl)
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  rw [e1, e2, e3, e4]
  ring

/-- Monotonicity of conditional mutual information under pairing:
`I(A; B | C) ≤ I(A; (B, D) | C)`. -/
theorem condMutualInfo_le_pair_right [Finite γ] [Finite α] [Finite β] [Finite δ]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (B : Ω → β) (D : Ω → δ) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, (B ω, D ω))) := by
  rw [condMutualInfo_map_comm ν C A (fun ω => (B ω, D ω)),
    condMutualInfo_chain_rule ν B D A C,
    condMutualInfo_map_comm ν C B A]
  linarith [condMutualInfo_nonneg (ν.map fun ω => ((B ω, C ω), D ω, A ω))]

/-- Base-2 Kullback–Leibler divergence `D(P ‖ Q) = ∑ x, P(x) log₂(P(x) / Q(x))` on finite
distributions. -/
noncomputable def klDivBits [Finite α] (p q : PMF α) : ℝ :=
  let := Fintype.ofFinite α
  ∑ a, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal)

/-- Explicit finite-sum formula for `klDivBits`. -/
theorem klDivBits_eq_sum [Fintype α] (p q : PMF α) :
    klDivBits p q = ∑ a, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal) := by
  rw [klDivBits, Subsingleton.elim (Fintype.ofFinite α) ‹Fintype α›]

/-- Bridge between `klDivBits` (in bits) and Mathlib's `InformationTheory.klDiv` (in nats). -/
theorem klDivBits_eq_toReal_klDiv_div_log_two [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {p q : PMF α} (h : p.support ⊆ q.support) :
    klDivBits p q = (klDiv p.toMeasure q.toMeasure).toReal / Real.log 2 := by
  let := Fintype.ofFinite α
  rw [klDivBits_eq_sum, toReal_klDiv_toMeasure h, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Real.logb, mul_div_assoc]

/-- Nonnegativity of base-2 KL divergence (Gibbs' inequality) under support inclusion. -/
theorem klDivBits_nonneg [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    0 ≤ klDivBits p q := by
  let : MeasurableSpace α := ⊤
  rw [klDivBits_eq_toReal_klDiv_div_log_two h]
  exact div_nonneg ENNReal.toReal_nonneg (Real.log_nonneg (by norm_num))

/-- Divergence of a distribution from itself is zero. -/
@[simp] theorem klDivBits_self [Finite α] (p : PMF α) : klDivBits p p = 0 := by
  let := Fintype.ofFinite α
  rw [klDivBits_eq_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hp : (p a).toReal = 0
  · simp [hp]
  · simp [div_self hp]

/-- Conditional mutual information equals the expected divergence between conditional
distributions: `I(A; B | C) = E_{a, c ~ A, C}[D(B_{a, c} ‖ B_c)]`. -/
theorem condMutualInfo_eq_expect_klDivBits [Fintype α] [Finite β] [Fintype γ]
    (ν : PMF Ω) (A : Ω → α) (B : Ω → β) (C : Ω → γ) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      ∑ p : γ × α,
        ((ν.map fun ω => (C ω, A ω)) p).toReal *
          klDivBits
            (conditionalSnd (ν.map fun ω => ((C ω, A ω), B ω)) p)
            (conditionalSnd (ν.map fun ω => (C ω, B ω)) p.1) := by
  classical
  let _ := Fintype.ofFinite β
  set jCAB := ν.map fun ω => (C ω, A ω, B ω)
  set jCA := ν.map fun ω => (C ω, A ω)
  set jCB := ν.map fun ω => (C ω, B ω)
  set jC := ν.map C
  set jCA_B := ν.map fun ω => ((C ω, A ω), B ω)
  have hCA_fst : jCA_B.map Prod.fst = jCA := by
    simp only [jCA_B, jCA, PMF.map_comp]
    rfl
  have hCB_fst : jCB.map Prod.fst = jC := by
    simp only [jCB, jC, PMF.map_comp]
    rfl
  have hsum_rhs :
      ∑ p : γ × α, (jCA p).toReal *
          klDivBits (conditionalSnd jCA_B p) (conditionalSnd jCB p.1) =
        ∑ p : γ × α, ∑ b : β,
          (jCA_B (p, b)).toReal *
            (surprisal (conditionalSnd jCB p.1) b -
              surprisal (conditionalSnd jCA_B p) b) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [klDivBits_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hmarg : (jCA p).toReal * (conditionalSnd jCA_B p b).toReal = (jCA_B (p, b)).toReal := by
      rw [← ENNReal.toReal_mul, ← hCA_fst, marginal_mul_conditionalSnd]
    by_cases hcab : jCA_B (p, b) = 0
    · have hzero : (jCA p).toReal * (conditionalSnd jCA_B p b).toReal = 0 := by
        rw [hmarg, hcab, ENNReal.toReal_zero]
      have h0 : (jCA p).toReal = 0 ∨ (conditionalSnd jCA_B p b).toReal = 0 :=
        mul_eq_zero.mp hzero
      rcases h0 with h1 | h2
      · simp [h1, hcab]
      · simp [h2, hcab]
    · have hp_ne : jCA p ≠ 0 := by
        intro h0
        have := marginal_mul_conditionalSnd jCA_B p b
        rw [hCA_fst, h0, zero_mul] at this
        exact hcab this.symm
      have hcb_ne : jCB (p.1, b) ≠ 0 := by
        have hle : jCA_B (p, b) ≤ jCB (p.1, b) := by
          have hcomp : jCB = jCA_B.map (fun x => (x.1.1, x.2)) := by
            simp only [jCB, jCA_B, PMF.map_comp]
            rfl
          rw [hcomp]
          exact le_map_apply jCA_B (fun x => (x.1.1, x.2)) (p, b)
        exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hcab) hle)
      have hc_ne : jC p.1 ≠ 0 := by
        intro h0
        have := marginal_mul_conditionalSnd jCB p.1 b
        rw [hCB_fst, h0, zero_mul] at this
        exact hcb_ne this.symm
      have hcond1_ne : (conditionalSnd jCA_B p b).toReal ≠ 0 := by
        have hmem : b ∈ (conditionalSnd jCA_B p).support :=
          (mem_support_conditionalSnd_iff jCA_B p (by rwa [hCA_fst]) b).mpr hcab
        exact ENNReal.toReal_ne_zero.mpr ⟨hmem, PMF.apply_ne_top _ _⟩
      have hcond2_ne : (conditionalSnd jCB p.1 b).toReal ≠ 0 := by
        have hmem : b ∈ (conditionalSnd jCB p.1).support :=
          (mem_support_conditionalSnd_iff jCB p.1 (by rwa [hCB_fst]) b).mpr hcb_ne
        exact ENNReal.toReal_ne_zero.mpr ⟨hmem, PMF.apply_ne_top _ _⟩
      rw [← mul_assoc, hmarg, surprisal, surprisal, Real.logb_div hcond1_ne hcond2_ne]
      ring
  rw [hsum_rhs]
  have h1 :
      ∑ p : γ × α, ∑ b : β, (jCA_B (p, b)).toReal * surprisal (conditionalSnd jCA_B p) b =
        conditionalEntropy jCA_B := by
    rw [conditionalEntropy_eq_sum_surprisal]
    exact (Fintype.sum_prod_type
      (fun x : (γ × α) × β => (jCA_B x).toReal * surprisal (conditionalSnd jCA_B x.1) x.2)).symm
  have h2 :
      ∑ p : γ × α, ∑ b : β, (jCA_B (p, b)).toReal * surprisal (conditionalSnd jCB p.1) b =
        conditionalEntropy jCB := by
    have hcomp : jCB = jCA_B.map (fun x => (x.1.1, x.2)) := by
      simp only [jCB, jCA_B, PMF.map_comp]
      rfl
    rw [conditionalEntropy_eq_sum_surprisal]
    calc ∑ p : γ × α, ∑ b : β, (jCA_B (p, b)).toReal * surprisal (conditionalSnd jCB p.1) b
        = ∑ x : (γ × α) × β, (jCA_B x).toReal * surprisal (conditionalSnd jCB x.1.1) x.2 :=
          (Fintype.sum_prod_type (fun x : (γ × α) × β =>
            (jCA_B x).toReal * surprisal (conditionalSnd jCB x.1.1) x.2)).symm
      _ = ∑ cb : γ × β, ((jCA_B.map (fun x => (x.1.1, x.2))) cb).toReal *
            surprisal (conditionalSnd jCB cb.1) cb.2 :=
          (sum_map_mul jCA_B (fun x => (x.1.1, x.2))
            (fun cb => surprisal (conditionalSnd jCB cb.1) cb.2)).symm
      _ = _ := by rw [← hcomp]
  have hsub :
      ∑ p : γ × α, ∑ b : β,
          (jCA_B (p, b)).toReal *
            (surprisal (conditionalSnd jCB p.1) b - surprisal (conditionalSnd jCA_B p) b) =
        conditionalEntropy jCB - conditionalEntropy jCA_B := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [h2, h1]
  rw [hsub]
  have hent_eq : entropy jCA_B = entropy jCAB := by
    refine entropy_map_eq_of_comp ν
      (e := fun t : γ × α × β => ((t.1, t.2.1), t.2.2)) ?_ (fun _ _ => rfl)
    exact (Equiv.prodAssoc γ α β).symm.injective
  rw [condMutualInfo_map, conditionalEntropy, conditionalEntropy, hCB_fst, hCA_fst, hent_eq]
  ring

/-- Binary product PMF `p₁ × p₂`. -/
@[expose] noncomputable def prodPMF (p₁ : PMF α) (p₂ : PMF β) : PMF (α × β) :=
  p₁.bind fun a => p₂.map (a, ·)

/-- Pointwise evaluation of `prodPMF`. -/
@[simp] theorem prodPMF_apply (p₁ : PMF α) (p₂ : PMF β) (x : α × β) :
    prodPMF p₁ p₂ x = p₁ x.1 * p₂ x.2 :=
  bind_map_prodMk_apply p₁ (fun _ => p₂) x

/-- Divergence of binary product distributions is additive:
`D(P₁ × P₂ ‖ Q₁ × Q₂) = D(P₁ ‖ Q₁) + D(P₂ ‖ Q₂)`. -/
theorem klDivBits_prod [Finite α] [Finite β]
    {p₁ q₁ : PMF α} {p₂ q₂ : PMF β}
    (h₁ : p₁.support ⊆ q₁.support) (h₂ : p₂.support ⊆ q₂.support) :
    klDivBits (prodPMF p₁ p₂) (prodPMF q₁ q₂) = klDivBits p₁ q₁ + klDivBits p₂ q₂ := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [klDivBits_eq_sum, klDivBits_eq_sum, klDivBits_eq_sum, Fintype.sum_prod_type]
  have hterm (a : α) (b : β) :
      (prodPMF p₁ p₂ (a, b)).toReal *
          Real.logb 2 ((prodPMF p₁ p₂ (a, b)).toReal / (prodPMF q₁ q₂ (a, b)).toReal) =
        (p₁ a).toReal * (p₂ b).toReal * Real.logb 2 ((p₁ a).toReal / (q₁ a).toReal) +
          (p₁ a).toReal * (p₂ b).toReal * Real.logb 2 ((p₂ b).toReal / (q₂ b).toReal) := by
    by_cases hp1 : p₁ a = 0
    · simp [hp1]
    by_cases hp2 : p₂ b = 0
    · simp [hp2]
    have hq1 : q₁ a ≠ 0 := (PMF.mem_support_iff q₁ a).mp (h₁ ((PMF.mem_support_iff p₁ a).mpr hp1))
    have hq2 : q₂ b ≠ 0 := (PMF.mem_support_iff q₂ b).mp (h₂ ((PMF.mem_support_iff p₂ b).mpr hp2))
    have hp1r : (p₁ a).toReal ≠ 0 := by ennreal_to_real using hp1
    have hp2r : (p₂ b).toReal ≠ 0 := by ennreal_to_real using hp2
    have hq1r : (q₁ a).toReal ≠ 0 := by ennreal_to_real using hq1
    have hq2r : (q₂ b).toReal ≠ 0 := by ennreal_to_real using hq2
    simp only [prodPMF_apply, ENNReal.toReal_mul]
    rw [mul_div_mul_comm, Real.logb_mul (div_ne_zero hp1r hq1r) (div_ne_zero hp2r hq2r)]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hpull :
        ∑ b : β, (p₁ a).toReal * (p₂ b).toReal * Real.logb 2 ((p₁ a).toReal / (q₁ a).toReal) =
          (∑ b : β, (p₂ b).toReal) *
            ((p₁ a).toReal * Real.logb 2 ((p₁ a).toReal / (q₁ a).toReal)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => by ring
    rw [hpull, sum_toReal, one_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hpull :
        ∑ a : α, (p₁ a).toReal * (p₂ b).toReal * Real.logb 2 ((p₂ b).toReal / (q₂ b).toReal) =
          (∑ a : α, (p₁ a).toReal) *
            ((p₂ b).toReal * Real.logb 2 ((p₂ b).toReal / (q₂ b).toReal)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => by ring
    rw [hpull, sum_toReal, one_mul]

/-- Base-2 KL divergence tensorizes over arbitrary finite independent products. -/
theorem klDivBits_pi {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, Finite (X i)]
    {p q : ∀ i, PMF (X i)} (h : ∀ i, (p i).support ⊆ (q i).support) :
    klDivBits (PMF.pi p) (PMF.pi q) = ∑ i, klDivBits (p i) (q i) := by
  let (i : ι) : MeasurableSpace (X i) := ⊤
  have hms : MeasurableSingletonClass (∀ i, X i) := inferInstance
  rw [klDivBits_eq_toReal_klDiv_div_log_two (support_pi_subset_iff.mpr h),
    toReal_klDiv_pi h, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => (klDivBits_eq_toReal_klDiv_div_log_two (h i)).symm

/-- Expected positive part of the base-2 log likelihood ratio:
`D₊(P ‖ Q) = ∑ x, P(x) * max 0 (log₂(P(x) / Q(x)))`. -/
noncomputable def klDivPosBits [Finite α] (p q : PMF α) : ℝ :=
  let := Fintype.ofFinite α
  ∑ a, (p a).toReal * max 0 (Real.logb 2 ((p a).toReal / (q a).toReal))

/-- Explicit finite-sum formula for `klDivPosBits`. -/
theorem klDivPosBits_eq_sum [Fintype α] (p q : PMF α) :
    klDivPosBits p q =
      ∑ a, (p a).toReal * max 0 (Real.logb 2 ((p a).toReal / (q a).toReal)) := by
  rw [klDivPosBits, Subsingleton.elim (Fintype.ofFinite α) ‹Fintype α›]

/-- `klDivPosBits` is always nonnegative. -/
theorem klDivPosBits_nonneg [Finite α] (p q : PMF α) : 0 ≤ klDivPosBits p q := by
  let := Fintype.ofFinite α
  rw [klDivPosBits_eq_sum]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (le_max_left _ _)

private theorem neg_inv_exp_le_mul_log {u : ℝ} (hu : 0 ≤ u) :
    -(Real.exp 1)⁻¹ ≤ u * Real.log u := by
  rcases eq_or_lt_of_le hu with rfl | hpos
  · simp only [zero_mul, Left.neg_nonpos_iff, inv_nonneg]
    exact (Real.exp_pos 1).le
  · have hlog := Real.add_one_le_exp (-(Real.log u + 1))
    have hexp : Real.exp (-(Real.log u + 1)) = (u * Real.exp 1)⁻¹ := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_log hpos]
    rw [hexp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
    have hcancel : u * (u * Real.exp 1)⁻¹ = (Real.exp 1)⁻¹ := by
      field_simp [hpos.ne', (Real.exp_pos 1).ne']
    rw [hcancel] at hmul
    linarith

/-- The expected positive part of `log₂(P(x) / Q(x))` exceeds the base-2 KL divergence by at most
`1 / (e · ln 2)`. -/
theorem klDivPosBits_le_add_const [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    klDivPosBits p q ≤ klDivBits p q + 1 / (Real.exp 1 * Real.log 2) := by
  let := Fintype.ofFinite α
  rw [klDivPosBits_eq_sum, klDivBits_eq_sum]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiff :
      (∑ a, (p a).toReal * max 0 (Real.logb 2 ((p a).toReal / (q a).toReal))) -
        (∑ a, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal)) ≤
        ∑ a, (q a).toReal / (Real.exp 1 * Real.log 2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_sub]
    by_cases hp : p a = 0
    · simp only [hp, ENNReal.toReal_zero, zero_mul]
      exact div_nonneg ENNReal.toReal_nonneg (mul_nonneg (Real.exp_pos 1).le hlog2.le)
    · have hq : q a ≠ 0 := (PMF.mem_support_iff q a).mp (h ((PMF.mem_support_iff p a).mpr hp))
      have hp_pos : 0 < (p a).toReal := ENNReal.toReal_pos hp (PMF.apply_ne_top _ _)
      have hq_pos : 0 < (q a).toReal := ENNReal.toReal_pos hq (PMF.apply_ne_top _ _)
      by_cases hle : 0 ≤ Real.logb 2 ((p a).toReal / (q a).toReal)
      · rw [max_eq_right hle, sub_self, mul_zero]
        exact div_nonneg hq_pos.le (mul_nonneg (Real.exp_pos 1).le hlog2.le)
      · rw [max_eq_left (le_of_not_ge hle), zero_sub, mul_neg]
        have hu := neg_inv_exp_le_mul_log (div_nonneg hp_pos.le hq_pos.le)
        have hqmul := mul_le_mul_of_nonneg_left hu hq_pos.le
        have hsimpl :
            (q a).toReal * ((p a).toReal / (q a).toReal * Real.log ((p a).toReal / (q a).toReal)) =
              (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
          field_simp [hq_pos.ne']
        rw [hsimpl] at hqmul
        have hneg :
            -((p a).toReal * Real.log ((p a).toReal / (q a).toReal)) ≤
              (q a).toReal * (Real.exp 1)⁻¹ := by
          linarith
        have hdiv := div_le_div_of_nonneg_right hneg hlog2.le
        have hlhs :
            -((p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal)) =
              -((p a).toReal * Real.log ((p a).toReal / (q a).toReal)) / Real.log 2 := by
          rw [Real.logb]
          ring
        have hrhs :
            (q a).toReal * (Real.exp 1)⁻¹ / Real.log 2 =
              (q a).toReal / (Real.exp 1 * Real.log 2) := by
          field_simp [(Real.exp_pos 1).ne', hlog2.ne']
        rw [hlhs, ← hrhs]
        exact hdiv
  have hqsum :
      ∑ a, (q a).toReal / (Real.exp 1 * Real.log 2) = 1 / (Real.exp 1 * Real.log 2) := by
    rw [← Finset.sum_div, sum_toReal]
  linarith

/-- Jensen's inequality for `Real.sqrt` under a finite probability mass function. -/
theorem sum_mul_sqrt_le_sqrt_sum [Fintype α] (p : PMF α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) :
    ∑ a, (p a).toReal * Real.sqrt (f a) ≤ Real.sqrt (∑ a, (p a).toReal * f a) := by
  have hrew : ∑ a, (p a).toReal * Real.sqrt (f a) =
      ∑ a, Real.sqrt (p a).toReal * Real.sqrt ((p a).toReal * f a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.sqrt_mul ENNReal.toReal_nonneg, ← mul_assoc,
      Real.mul_self_sqrt ENNReal.toReal_nonneg]
  rw [hrew]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (p a).toReal) (fun a => Real.sqrt ((p a).toReal * f a))
  have hsq1 : ∑ a : α, Real.sqrt (p a).toReal ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt ENNReal.toReal_nonneg]
    exact sum_toReal p
  have hsq2 : ∑ a : α, Real.sqrt ((p a).toReal * f a) ^ 2 = ∑ a : α, (p a).toReal * f a :=
    Finset.sum_congr rfl fun a _ => Real.sq_sqrt (mul_nonneg ENNReal.toReal_nonneg (hf a))
  rw [hsq1, one_mul, hsq2] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- Cauchy–Schwarz inequality for sums of square roots:
`∑ i ∈ s, √(f i) ≤ √(s.card * ∑ i ∈ s, f i)` for nonnegative `f`. -/
theorem sum_sqrt_le_sqrt_card_mul_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, Real.sqrt (f i) ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, f i) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (f i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsq : ∑ i ∈ s, Real.sqrt (f i) ^ 2 = ∑ i ∈ s, f i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hf i hi)
  rw [hsq] at hcs
  exact Real.le_sqrt_of_sq_le hcs

end CslibFrontier.Probability.Divergence.PositivePart
