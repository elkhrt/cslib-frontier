/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.ComputableAnalysis.SemiComputableReal
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Data.EReal.Basic

import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The Zheng–Weihrauch Arithmetic Hierarchy of Real Numbers

Second level (`Δ₂`, `Σ₂`, `Π₂`) and general `n`-fold alternating `sup`/`inf` levels
(`Sigma n`, `Pi n`, `Delta n`) of the Zheng–Weihrauch arithmetic hierarchy of real numbers,
building on the first-level classes in
`CslibFrontier.Computability.ComputableAnalysis.SemiComputableReal`, proved under standard Lean
axioms.

## Main definitions

* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Delta2`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Sigma2`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Pi2`: recursively approximable real numbers
  (`Δ₂`,
  limits of computable sequences) and the second-level classes `Σ₂` and `Π₂` defined via guarded
  extended-real `⨆ n, ⨅ k` and `⨅ n, ⨆ k` of computable double sequences.
* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.altSupInf`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.altInfSup`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Sigma`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Pi`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Delta`: the complete Zheng–Weihrauch hierarchy
  `Σₙ`, `Πₙ`, and `Δₙ = Σₙ ∩ Πₙ` for all `n : ℕ`.

## Main results

* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.mem_sigma2_iff_guarded_real`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.mem_sigma2_iff_exists_rat_double`: bounded-real
  and
  rational double-sequence characterizations of `Σ₂`.
* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta2_eq_sigma2_inter_pi2`: `Δ₂ = Σ₂ ∩ Π₂`.
* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.sigma_one_eq_sigma1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.pi_one_eq_pi1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta_one_eq_delta1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.sigma_two_eq_sigma2`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.pi_two_eq_pi2`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta_two_eq_delta2`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta_subset_delta_succ`: consistency of the
  general
  `n`-level hierarchy with levels `1` and `2` and monotonicity `Δₙ ⊆ Δₙ₊₁`.
-/

public section

namespace CslibFrontier.ComputableAnalysis

namespace ZhengWeihrauch

/-! ### Second level: `Δ₂`, `Σ₂`, `Π₂`, and `Δ₂ = Σ₂ ∩ Π₂` -/

/-- The class `Δ₂` of recursively approximable real numbers: limits of computable sequences of
computable real numbers. -/
@[expose] def Delta2 : Set ℝ :=
  { x : ℝ | ∃ s : ℕ → ℝ, IsComputableRealSeq s ∧ Filter.Tendsto s Filter.atTop (nhds x) }

/-- The class `Σ₂` of the Zheng–Weihrauch hierarchy: reals representable as the extended-real
`⨆ n : ℕ, ⨅ k : ℕ, (ζ n k : EReal)` of a computable double sequence `ζ : ℕ → ℕ → ℝ`. -/
@[expose] def Sigma2 : Set ℝ :=
  { x : ℝ | ∃ ζ : ℕ → ℕ → ℝ, IsComputableRealDoubleSeq ζ ∧
      (x : EReal) = ⨆ n : ℕ, ⨅ k : ℕ, (ζ n k : EReal) }

/-- The class `Π₂` of the Zheng–Weihrauch hierarchy: reals representable as the extended-real
`⨅ n : ℕ, ⨆ k : ℕ, (ξ n k : EReal)` of a computable double sequence `ξ : ℕ → ℕ → ℝ`. -/
@[expose] def Pi2 : Set ℝ :=
  { x : ℝ | ∃ ξ : ℕ → ℕ → ℝ, IsComputableRealDoubleSeq ξ ∧
      (x : EReal) = ⨅ n : ℕ, ⨆ k : ℕ, (ξ n k : EReal) }

private lemma ereal_neg_iSup (g : ℕ → EReal) : -(⨆ i, g i) = ⨅ i, -g i :=
  le_antisymm (le_iInf fun i ↦ EReal.neg_le_neg_iff.mpr (le_iSup g i))
    (EReal.le_neg.mpr (iSup_le fun i ↦ EReal.le_neg_of_le_neg (iInf_le (fun j ↦ -g j) i)))

private lemma ereal_neg_iInf (g : ℕ → EReal) : -(⨅ i, g i) = ⨆ i, -g i := by
  have h := congrArg Neg.neg (ereal_neg_iSup fun i ↦ -g i)
  simp only [neg_neg] at h
  exact h.symm

/-- Inclusion `C₂ ⊆ Δ₂`. -/
theorem weaklyComputable_subset_delta2 : WeaklyComputable ⊆ Delta2 := fun _ hx ↦ by
  obtain ⟨α, hα, _, hlim⟩ := mem_weaklyComputable_iff_summable_diff.mp hx
  exact ⟨α, hα, hlim⟩

/-- Inclusion `Σ₁ ⊆ Δ₂`. -/
theorem sigma1_subset_delta2 : Sigma1 ⊆ Delta2 :=
  sigma1_subset_weaklyComputable.trans weaklyComputable_subset_delta2

/-- Inclusion `Π₁ ⊆ Δ₂`. -/
theorem pi1_subset_delta2 : Pi1 ⊆ Delta2 :=
  pi1_subset_weaklyComputable.trans weaklyComputable_subset_delta2

/-- Inclusion `Δ₁ ⊆ Δ₂`. -/
theorem delta1_subset_delta2 : Delta1 ⊆ Delta2 := delta1_subset_sigma1.trans sigma1_subset_delta2

/-- Symmetry `x ∈ Π₂ ↔ -x ∈ Σ₂`. -/
theorem mem_pi2_iff_neg_mem_sigma2 {x : ℝ} : x ∈ Pi2 ↔ -x ∈ Sigma2 := by
  constructor
  · rintro ⟨ξ, hξ, hx⟩
    refine ⟨fun n k ↦ -ξ n k, hξ.neg, ?_⟩
    rw [EReal.coe_neg, hx, ereal_neg_iInf]; simp_rw [ereal_neg_iSup, ← EReal.coe_neg]
  · rintro ⟨ζ, hζ, hx⟩
    refine ⟨fun n k ↦ -ζ n k, hζ.neg, ?_⟩
    have := congrArg Neg.neg hx
    rw [EReal.coe_neg, neg_neg, ereal_neg_iSup] at this
    simp_rw [ereal_neg_iInf, ← EReal.coe_neg] at this
    exact this

/-- Guarded real-valued characterization of `Σ₂`: `x ∈ Σ₂` iff `x = ⨆ n, ⨅ k, ζ n k` for a
computable double sequence `ζ` with every row bounded below and row infima bounded above. -/
theorem mem_sigma2_iff_guarded_real {x : ℝ} :
    x ∈ Sigma2 ↔
      ∃ ζ : ℕ → ℕ → ℝ, IsComputableRealDoubleSeq ζ ∧
        (∀ n, BddBelow (Set.range (ζ n))) ∧
        BddAbove (Set.range fun n ↦ ⨅ k, ζ n k) ∧
        x = ⨆ n : ℕ, ⨅ k : ℕ, ζ n k := by
  constructor
  · rintro ⟨ζ, hζ, hx⟩
    have hgt : ((x - 1 : ℝ) : EReal) < ⨆ n, ⨅ k, (ζ n k : EReal) := by
      rw [← hx]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨n0, hn0⟩ := lt_iSup_iff.mp hgt
    obtain ⟨B, hBx⟩ : ∃ B : ℚ, (B : ℝ) ≤ x :=
      let ⟨B, hB⟩ := exists_rat_lt x; ⟨B, hB.le⟩
    let ζ' : ℕ → ℕ → ℝ := fun n k ↦ max (ζ n k) (B : ℝ)
    have hζ' : IsComputableRealDoubleSeq ζ' :=
      hζ.max (isComputableReal_rat B).constDoubleSeq
    have hbdd_lo : ∀ n, BddBelow (Set.range (ζ' n)) := fun n ↦
      ⟨(B : ℝ), by rintro _ ⟨k, rfl⟩; exact le_max_right _ _⟩
    have hrow_le : ∀ n, (⨅ k, ζ' n k) ≤ x := fun n ↦ by
      have hE : ⨅ k, (ζ n k : EReal) ≤ (x : EReal) :=
        hx ▸ le_iSup (fun m ↦ ⨅ k, (ζ m k : EReal)) n
      by_contra hgt'; push Not at hgt'
      have hltE : ⨅ k, (ζ n k : EReal) < ((⨅ k, ζ' n k : ℝ) : EReal) :=
        hE.trans_lt (EReal.coe_lt_coe_iff.mpr hgt')
      obtain ⟨k, hk⟩ := iInf_lt_iff.mp hltE
      have hk' : ζ n k < ⨅ j, ζ' n j := EReal.coe_lt_coe_iff.mp hk
      have hle : ⨅ j, ζ' n j ≤ ζ' n k := ciInf_le (hbdd_lo n) k
      have hmax : ζ' n k = (B : ℝ) := max_eq_right (by
        by_contra h; push Not at h
        have : ζ' n k = ζ n k := max_eq_left h.le
        linarith)
      linarith
    have hbdd_hi : BddAbove (Set.range fun n ↦ ⨅ k, ζ' n k) :=
      ⟨x, by rintro _ ⟨n, rfl⟩; exact hrow_le n⟩
    refine ⟨ζ', hζ', hbdd_lo, hbdd_hi, le_antisymm ?_ (ciSup_le hrow_le)⟩
    by_contra hlt; push Not at hlt
    set y := ⨆ n, ⨅ k, ζ' n k
    have hyE : ((y : ℝ) : EReal) < ⨆ n, ⨅ k, (ζ n k : EReal) := by
      rw [← hx]; exact EReal.coe_lt_coe_iff.mpr hlt
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hyE
    have hrow_ge : y ≤ ⨅ k, ζ' n k :=
      le_ciInf fun k ↦
        (EReal.coe_le_coe_iff.mp (hn.le.trans (iInf_le _ k))).trans (le_max_left _ _)
    have hrow_le_y : (⨅ k, ζ' n k) ≤ y := le_ciSup hbdd_hi n
    have hy_eq : (⨅ k, ζ' n k) = y := le_antisymm hrow_le_y hrow_ge
    -- Pick midpoint `m` between `y` and `x`
    set mid := (y + x) / 2
    have hmid : ((mid : ℝ) : EReal) < ⨆ m, ⨅ k, (ζ m k : EReal) := by
      rw [← hx]; exact EReal.coe_lt_coe_iff.mpr (by dsimp [mid]; linarith)
    obtain ⟨m, hm⟩ := lt_iSup_iff.mp hmid
    have hm_ge : mid ≤ ⨅ k, ζ' m k :=
      le_ciInf fun k ↦
        (EReal.coe_le_coe_iff.mp (hm.le.trans (iInf_le _ k))).trans (le_max_left _ _)
    have hm_le : (⨅ k, ζ' m k) ≤ y := le_ciSup hbdd_hi m
    dsimp [mid] at hm_ge; linarith
  · rintro ⟨ζ, hζ, hlo, hhi, rfl⟩
    refine ⟨ζ, hζ, le_antisymm ?_ ?_⟩
    · by_contra hlt; push Not at hlt
      obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.mp hlt
      have hq_lt : (q : ℝ) < ⨆ n, ⨅ k, ζ n k := EReal.coe_lt_coe_iff.mp hq2
      obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hq_lt
      have hrow : ((q : ℝ) : EReal) ≤ ⨅ k, (ζ n k : EReal) :=
        le_iInf fun k ↦ EReal.coe_le_coe_iff.mpr (hn.le.trans (ciInf_le (hlo n) k))
      exact not_le_of_gt hq1 (hrow.trans (le_iSup (fun m ↦ ⨅ k, (ζ m k : EReal)) n))
    · refine iSup_le fun n ↦ ?_
      by_cases hbot : (⨅ k, (ζ n k : EReal)) = ⊥
      · rw [hbot]; exact bot_le
      · refine le_of_forall_lt_imp_le_of_dense fun z hz ↦ ?_
        obtain ⟨q, hzq, hqinf⟩ := EReal.lt_iff_exists_rat_btwn.mp hz
        have hq_le : (q : ℝ) ≤ ⨅ k, ζ n k :=
          le_ciInf fun k ↦ EReal.coe_le_coe_iff.mp (hqinf.le.trans (iInf_le _ k))
        exact hzq.le.trans (EReal.coe_le_coe_iff.mpr (hq_le.trans (le_ciSup hhi n)))

/-- Rational double-sequence characterization of `Σ₂`: `x ∈ Σ₂` iff
`(x : EReal) = ⨆ n, ⨅ k, (r n k : EReal)` for a computable rational double sequence `r`. -/
theorem mem_sigma2_iff_exists_rat_double {x : ℝ} :
    x ∈ Sigma2 ↔
      ∃ r : ℕ → ℕ → ℚ, IsComputableRatMap₂ r ∧
        (x : EReal) = ⨆ n : ℕ, ⨅ k : ℕ, ((r n k : ℝ) : EReal) := by
  constructor
  · rintro ⟨ζ, hζ, hx⟩
    obtain ⟨q, hq, hc⟩ := isComputableRealDoubleSeq_iff_exists_rat_approx.mp hζ
    let r : ℕ → ℕ → ℚ := fun p k ↦
      q (p.unpair.1, k) p.unpair.2 - (2 : ℚ) ^ (-(p.unpair.2 : ℤ))
    have hr : IsComputableRatMap₂ r := by
      have hn : Computable fun p : ℕ × ℕ ↦ p.1.unpair.1 :=
        Computable.fst.comp (Computable.unpair.comp .fst)
      have hM : Computable fun p : ℕ × ℕ ↦ p.1.unpair.2 :=
        Computable.snd.comp (Computable.unpair.comp .fst)
      exact ((hq.comp (.pair hn .snd) hM).sub
        ((IsComputableRatMap.const 2).zpow
          (primrec_int_neg.to_comp.comp (primrec_int_ofNat.to_comp.comp hM)))).to₂
    refine ⟨r, hr, le_antisymm ?_ ?_⟩
    · by_contra hlt; push Not at hlt
      obtain ⟨u, hu1, hu2⟩ := EReal.lt_iff_exists_rat_btwn.mp hlt
      set ε := (x - (u : ℝ)) / 2
      have hε : 0 < ε := half_pos (sub_pos.mpr (EReal.coe_lt_coe_iff.mp hu2))
      have hmid : (((u : ℝ) + ε : ℝ) : EReal) < ⨆ n, ⨅ k, (ζ n k : EReal) := by
        have hlt' : (u : ℝ) + ε < x := by
          have : (u : ℝ) < x := EReal.coe_lt_coe_iff.mp hu2
          have hdef : ε = (x - (u : ℝ)) / 2 := rfl
          linarith
        rw [← hx]; exact EReal.coe_lt_coe_iff.mpr hlt'
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp hmid
      have hz0 : Filter.Tendsto (fun M : ℕ ↦ (2 : ℝ) * (2 : ℝ) ^ (-(M : ℤ)))
          Filter.atTop (nhds 0) := by
        simpa only [mul_zero, one_div, inv_pow, zpow_neg, zpow_natCast] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2)
            (by norm_num)).const_mul 2
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hz0 ε hε
      have hM' : 2 * (2 : ℝ) ^ (-(M : ℤ)) < ε := by
        have hpos : (0 : ℝ) < 2 * (2 : ℝ) ^ (-(M : ℤ)) :=
          mul_pos two_pos (zpow_pos two_pos _)
        simpa [Real.dist_eq, abs_of_pos hpos] using hM M le_rfl
      have hrow : ((u : ℝ) : EReal) ≤ ⨅ k, ((r (Nat.pair n M) k : ℝ) : EReal) := by
        refine le_iInf fun k ↦ EReal.coe_le_coe_iff.mpr ?_
        have hζk : (u : ℝ) + ε ≤ ζ n k := EReal.coe_le_coe_iff.mp (hn.le.trans (iInf_le _ k))
        have he := abs_lt.mp (hc n k M)
        dsimp [r]; simp only [Nat.unpair_pair]; push_cast
        linarith
      exact not_le_of_gt hu1 (hrow.trans (le_iSup (fun p ↦ ⨅ k, ((r p k : ℝ) : EReal)) _))
    · rw [hx]
      refine iSup_le fun p ↦ (le_iSup (fun n ↦ ⨅ k, (ζ n k : EReal)) p.unpair.1).trans' ?_
      refine iInf_mono fun k ↦ EReal.coe_le_coe_iff.mpr ?_
      have he := abs_lt.mp (hc p.unpair.1 k p.unpair.2)
      dsimp [r]; push_cast; linarith [he.1]
  · rintro ⟨r, hr, hx⟩
    exact ⟨fun n k ↦ (r n k : ℝ), isComputableRealDoubleSeq_rat hr, hx⟩

/-- Second-level characterization: a real number is recursively approximable
(`x ∈ Δ₂`) if and only if `x ∈ Σ₂ ∩ Π₂`.
-/
theorem mem_delta2_iff_mem_sigma2_and_pi2 {x : ℝ} :
    x ∈ Delta2 ↔ x ∈ Sigma2 ∧ x ∈ Pi2 := by
  have hlim_to_sigma2 : ∀ {y : ℝ}, y ∈ Delta2 → y ∈ Sigma2 := by
    rintro y ⟨s, hs, hlim⟩
    let ζ : ℕ → ℕ → ℝ := fun n k ↦ s (n + k)
    have hζ : IsComputableRealDoubleSeq ζ := hs.comp₂ Primrec.nat_add.to_comp
    refine ⟨ζ, hζ, le_antisymm ?_ ?_⟩
    · by_contra hlt; push Not at hlt
      obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.mp hlt
      have hqy : (q : ℝ) < y := EReal.coe_lt_coe_iff.mp hq2
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (y - (q : ℝ)) (sub_pos.mpr hqy)
      have hrow : ((q : ℝ) : EReal) ≤ ⨅ k, (ζ N k : EReal) := by
        refine le_iInf fun k ↦ EReal.coe_le_coe_iff.mpr ?_
        have h1 := abs_lt.mp (by simpa [Real.dist_eq] using hN (N + k) (Nat.le_add_right N k))
        dsimp [ζ]; linarith [h1.1]
      exact not_le_of_gt hq1 (hrow.trans (le_iSup (fun n ↦ ⨅ k, (ζ n k : EReal)) N))
    · refine iSup_le fun n ↦ ?_
      by_contra hlt; push Not at hlt
      obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.mp hlt
      have hyq : y < (q : ℝ) := EReal.coe_lt_coe_iff.mp hq1
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ((q : ℝ) - y) (sub_pos.mpr hyq)
      have h1 := abs_lt.mp (by simpa [Real.dist_eq] using hN (n + N) (Nat.le_add_left N n))
      have hle : ⨅ k, (ζ n k : EReal) ≤ (s (n + N) : EReal) := iInf_le _ N
      have hsq : s (n + N) < (q : ℝ) := by linarith [h1.2]
      exact not_lt_of_ge hle ((EReal.coe_lt_coe_iff.mpr hsq).trans hq2)
  constructor
  · intro hx
    refine ⟨hlim_to_sigma2 hx, mem_pi2_iff_neg_mem_sigma2.mpr (hlim_to_sigma2 ?_)⟩
    obtain ⟨s, hs, hlim⟩ := hx
    exact ⟨fun n ↦ -s n, hs.neg, hlim.neg⟩
  · rintro ⟨hσ, hπ⟩
    obtain ⟨a, ha, hxa⟩ := mem_sigma2_iff_exists_rat_double.mp hσ
    obtain ⟨bNeg, hbNeg, hxbNeg⟩ :=
      mem_sigma2_iff_exists_rat_double.mp (mem_pi2_iff_neg_mem_sigma2.mp hπ)
    let b : ℕ → ℕ → ℚ := fun j k ↦ -bNeg j k
    have hb : IsComputableRatMap₂ b := hbNeg.neg.to₂
    let aTilde : ℕ → ℕ → ℚ := fun i s ↦
      (Finset.range (s + 1)).inf' Finset.nonempty_range_add_one (a i)
    let bTilde : ℕ → ℕ → ℚ := fun j s ↦
      (Finset.range (s + 1)).sup' Finset.nonempty_range_add_one (b j)
    have haT : IsComputableRatMap₂ aTilde :=
      (IsComputableRatMap.inf'_range .snd (ha.comp (Computable.fst.comp .fst) .snd).to₂).to₂
    have hbT : IsComputableRatMap₂ bTilde :=
      (IsComputableRatMap.sup'_range .snd (hb.comp (Computable.fst.comp .fst) .snd).to₂).to₂
    let bCap : ℕ → ℕ → ℚ := fun i s ↦
      (Finset.range (i + 1)).inf' Finset.nonempty_range_add_one fun j ↦ bTilde j s
    have hbCap : IsComputableRatMap₂ bCap :=
      (IsComputableRatMap.inf'_range .fst (hbT.comp .snd (Computable.snd.comp .fst)).to₂).to₂
    let r : ℕ → ℚ := fun s ↦
      (Finset.range (s + 1)).sup' Finset.nonempty_range_add_one fun i ↦
        Min.min (aTilde i s) (bCap i s)
    have hr : IsComputableRatSeq r :=
      IsComputableRatMap.sup'_range .id
        ((haT.comp .snd .fst).min (hbCap.comp .snd .fst)).to₂
    have hneg_sup : ∀ (g : ℕ → EReal), -(⨆ i, g i) = ⨅ i, -g i := fun g ↦
      le_antisymm (le_iInf fun i ↦ EReal.neg_le_neg_iff.mpr (le_iSup g i))
        (EReal.le_neg.mpr (iSup_le fun i ↦ EReal.le_neg_of_le_neg (iInf_le (fun j ↦ -g j) i)))
    have hneg_inf : ∀ (g : ℕ → EReal), -(⨅ i, g i) = ⨆ i, -g i := fun g ↦ by
      have h := congrArg Neg.neg (hneg_sup fun i ↦ -g i)
      simp only [neg_neg] at h
      exact h.symm
    have hxb : (x : EReal) = ⨅ j : ℕ, ⨆ k : ℕ, ((b j k : ℝ) : EReal) := by
      have h := congrArg Neg.neg hxbNeg
      rw [EReal.coe_neg, neg_neg, hneg_sup] at h
      simp_rw [hneg_inf, ← EReal.coe_neg] at h
      refine h.trans (iInf_congr fun j ↦ iSup_congr fun k ↦ ?_)
      dsimp [b]; push_cast; rfl
    refine ⟨fun s ↦ (r s : ℝ), isComputableRealSeq_rat hr, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Lower bound: pick `i₀` with `x - ε < ⨅ k, a i₀ k`, and wait for `bTilde j s > x - ε` (`j ≤
    -- i₀`).
    have hlo_ex : (((x - ε : ℝ)) : EReal) < ⨆ i, ⨅ k, ((a i k : ℝ) : EReal) := by
      rw [← hxa]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨i0, hi0⟩ := lt_iSup_iff.mp hlo_ex
    have hai0 : ∀ s : ℕ, x - ε < (aTilde i0 s : ℝ) := fun s ↦ by
      have hcast : (aTilde i0 s : ℝ) =
          (Finset.range (s + 1)).inf' Finset.nonempty_range_add_one fun t ↦ (a i0 t : ℝ) := by
        simpa [aTilde] using Finset.apply_inf'_eq_inf'_comp Finset.nonempty_range_add_one
          (f := a i0) (g := ((↑) : ℚ → ℝ)) (fun _ _ ↦ Rat.cast_min _ _)
      rw [hcast, Finset.lt_inf'_iff]
      exact fun t _ ↦ EReal.coe_lt_coe_iff.mp (hi0.trans_le (iInf_le _ t))
    have hbj_ex : ∀ j : ℕ, ∃ t : ℕ, x - ε < (b j t : ℝ) := fun j ↦ by
      have : (((x - ε : ℝ)) : EReal) < ⨆ k, ((b j k : ℝ) : EReal) :=
        (EReal.coe_lt_coe_iff.mpr (by linarith : x - ε < x)).trans_le (hxb ▸ iInf_le _ j)
      obtain ⟨t, ht⟩ := lt_iSup_iff.mp this
      exact ⟨t, EReal.coe_lt_coe_iff.mp ht⟩
    choose tb htb using hbj_ex
    let S1 := max i0 ((Finset.range (i0 + 1)).sup tb)
    -- Upper bound: pick `j₀` with `⨆ k, b j₀ k < x + ε`, and wait for `aTilde i s < x + ε` (`i <
    -- j₀`).
    have hhi_ex : ⨅ j, ⨆ k, ((b j k : ℝ) : EReal) < ((x + ε : ℝ) : EReal) := by
      rw [← hxb]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨j0, hj0⟩ := iInf_lt_iff.mp hhi_ex
    have hbj0 : ∀ s : ℕ, (bTilde j0 s : ℝ) < x + ε := fun s ↦ by
      have hcast : (bTilde j0 s : ℝ) =
          (Finset.range (s + 1)).sup' Finset.nonempty_range_add_one fun t ↦ (b j0 t : ℝ) := by
        simpa [bTilde] using Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one
          (f := b j0) (g := ((↑) : ℚ → ℝ)) (fun _ _ ↦ Rat.cast_max _ _)
      rw [hcast, Finset.sup'_lt_iff]
      exact fun t _ ↦
        EReal.coe_lt_coe_iff.mp ((le_iSup (fun k ↦ ((b j0 k : ℝ) : EReal)) t).trans_lt hj0)
    have hai_ex : ∀ i : ℕ, ∃ t : ℕ, (a i t : ℝ) < x + ε := fun i ↦ by
      have : ⨅ k, ((a i k : ℝ) : EReal) < ((x + ε : ℝ) : EReal) :=
        (le_iSup (fun m ↦ ⨅ k, ((a m k : ℝ) : EReal)) i).trans_lt
          (hxa ▸ EReal.coe_lt_coe_iff.mpr (by linarith))
      obtain ⟨t, ht⟩ := iInf_lt_iff.mp this
      exact ⟨t, EReal.coe_lt_coe_iff.mp ht⟩
    choose ta hta using hai_ex
    let S2 := max j0 ((Finset.range j0).sup ta)
    refine ⟨max S1 S2, fun s hs ↦ ?_⟩
    have hs1 : S1 ≤ s := (le_max_left _ _).trans hs
    have hs2 : S2 ≤ s := (le_max_right _ _).trans hs
    have hr_cast : (r s : ℝ) = (Finset.range (s + 1)).sup' Finset.nonempty_range_add_one
        fun i ↦ min (aTilde i s : ℝ) (bCap i s : ℝ) := by
      simpa [r, Rat.cast_min] using Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one
        (f := fun i ↦ min (aTilde i s) (bCap i s)) (g := ((↑) : ℚ → ℝ))
        (fun _ _ ↦ Rat.cast_max _ _)
    have hr_gt : x - ε < (r s : ℝ) := by
      have hi0_s : i0 ∈ Finset.range (s + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_max_left _ _).trans hs1))
      have hbCap_gt : x - ε < (bCap i0 s : ℝ) := by
        have hcast : (bCap i0 s : ℝ) =
            (Finset.range (i0 +
              1)).inf' Finset.nonempty_range_add_one fun j ↦ (bTilde j s : ℝ) := by
          simpa [bCap] using Finset.apply_inf'_eq_inf'_comp Finset.nonempty_range_add_one
            (f := fun j ↦ bTilde j s) (g := ((↑) : ℚ → ℝ)) (fun _ _ ↦ Rat.cast_min _ _)
        rw [hcast, Finset.lt_inf'_iff]
        intro j hj
        have hts : tb j ≤ s := (Finset.le_sup hj).trans ((le_max_right _ _).trans hs1)
        have hle : (b j (tb j) : ℝ) ≤ (bTilde j s : ℝ) := by
          exact_mod_cast Finset.le_sup' (b j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hts))
        exact (htb j).trans_le hle
      rw [hr_cast]
      exact (lt_min (hai0 s) hbCap_gt).trans_le
        (Finset.le_sup' (f := fun i ↦ min (aTilde i s : ℝ) (bCap i s : ℝ)) hi0_s)
    have hr_lt : (r s : ℝ) < x + ε := by
      rw [hr_cast, Finset.sup'_lt_iff]
      intro i _
      by_cases hij : j0 ≤ i
      · refine (min_le_right _ _).trans_lt ?_
        have hle : (bCap i s : ℝ) ≤ (bTilde j0 s : ℝ) := by
          exact_mod_cast Finset.inf'_le (fun j ↦ bTilde j s)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
        exact hle.trans_lt (hbj0 s)
      · have hilt : i ∈ Finset.range j0 := Finset.mem_range.mpr (lt_of_not_ge hij)
        have hts : ta i ≤ s := (Finset.le_sup hilt).trans ((le_max_right _ _).trans hs2)
        refine (min_le_left _ _).trans_lt ?_
        have hle : (aTilde i s : ℝ) ≤ (a i (ta i) : ℝ) := by
          exact_mod_cast Finset.inf'_le (a i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hts))
        exact hle.trans_lt (hta i)
    rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩

/-- Set equality `Δ₂ = Σ₂ ∩ Π₂`. -/
theorem delta2_eq_sigma2_inter_pi2 : Delta2 = Sigma2 ∩ Pi2 :=
  Set.ext fun _ ↦ mem_delta2_iff_mem_sigma2_and_pi2

/-! ### Complete `n`-level Zheng–Weihrauch hierarchy (`Σₙ`, `Πₙ`, `Δₙ`) -/

mutual

/-- `n`-fold alternating extended-real operator `sup_{m₁} inf_{m₂} sup_{m₃} ... f(m₁, ..., mₙ)`
starting with `sup`. -/
noncomputable def altSupInf : (n : ℕ) → ((Fin n → ℕ) → EReal) → EReal
  | 0, f => f Fin.elim0
  | n + 1, f => ⨆ m : ℕ, altInfSup n fun v ↦ f (Fin.cons m v)

/-- `n`-fold alternating extended-real operator `inf_{m₁} sup_{m₂} inf_{m₃} ... f(m₁, ..., mₙ)`
starting with `inf`. -/
noncomputable def altInfSup : (n : ℕ) → ((Fin n → ℕ) → EReal) → EReal
  | 0, f => f Fin.elim0
  | n + 1, f => ⨅ m : ℕ, altSupInf n fun v ↦ f (Fin.cons m v)

end

/-- The `n`-th `Σ`-class `Σₙ` of the Zheng–Weihrauch hierarchy: real numbers representable as
`altSupInf n r` for a computable `n`-fold rational sequence `r : (Fin n → ℕ) → ℚ`. -/
@[expose] def Sigma (n : ℕ) : Set ℝ :=
  { x : ℝ | ∃ r : (Fin n → ℕ) → ℚ, IsComputableRatMap r ∧
      (x : EReal) = altSupInf n fun v ↦ ((r v : ℝ) : EReal) }

/-- The `n`-th `Π`-class `Πₙ` of the Zheng–Weihrauch hierarchy: real numbers representable as
`altInfSup n r` for a computable `n`-fold rational sequence `r : (Fin n → ℕ) → ℚ`. -/
@[expose] def Pi (n : ℕ) : Set ℝ :=
  { x : ℝ | ∃ r : (Fin n → ℕ) → ℚ, IsComputableRatMap r ∧
      (x : EReal) = altInfSup n fun v ↦ ((r v : ℝ) : EReal) }

/-- The `n`-th `Δ`-class `Δₙ = Σₙ ∩ Πₙ` of the Zheng–Weihrauch hierarchy. -/
@[expose] def Delta (n : ℕ) : Set ℝ := Sigma n ∩ Pi n

private lemma computable_fin_cons {n : ℕ} :
    Computable₂ (@Fin.cons n (fun _ ↦ ℕ)) := by
  have hvec : Primrec fun p : ℕ × (Fin n → ℕ) ↦
      (List.Vector.cons p.1 (List.Vector.ofFn p.2)).get :=
    Primrec.vector_get'.comp
      (Primrec.vector_cons.comp .fst (Primrec.vector_ofFn'.comp .snd))
  exact Computable.of_eq hvec.to_comp (fun p ↦ by
    ext i; refine Fin.cases rfl (fun j ↦ by simp) i)

private lemma computable_fin_tail {n : ℕ} :
    Computable fun v : Fin (n + 1) → ℕ ↦ Fin.tail v := by
  have hvec : Primrec fun v : Fin (n + 1) → ℕ ↦ (List.Vector.tail (List.Vector.ofFn v)).get :=
    Primrec.vector_get'.comp (Primrec.vector_tail.comp Primrec.vector_ofFn')
  exact hvec.to_comp.of_eq fun v ↦ by ext j; simp [Fin.tail]

/-- Base case `altSupInf 0 f = f Fin.elim0`. -/
@[simp] theorem altSupInf_zero (f : (Fin 0 → ℕ) → EReal) : altSupInf 0 f = f Fin.elim0 := by
  simp [altSupInf]

/-- Base case `altInfSup 0 f = f Fin.elim0`. -/
@[simp] theorem altInfSup_zero (f : (Fin 0 → ℕ) → EReal) : altInfSup 0 f = f Fin.elim0 := by
  simp [altInfSup]

private lemma altSupInf_neg_and_altInfSup_neg : ∀ (n : ℕ),
    (∀ f : (Fin n → ℕ) → EReal, -(altSupInf n f) = altInfSup n (fun v ↦ -f v)) ∧
      (∀ f : (Fin n → ℕ) → EReal, -(altInfSup n f) = altSupInf n (fun v ↦ -f v))
  | 0 => ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := altSupInf_neg_and_altInfSup_neg n
    have hneg_sup : ∀ (g : ℕ → EReal), -(⨆ i, g i) = ⨅ i, -g i := fun g ↦
      le_antisymm (le_iInf fun i ↦ EReal.neg_le_neg_iff.mpr (le_iSup g i))
        (EReal.le_neg.mpr (iSup_le fun i ↦ EReal.le_neg_of_le_neg (iInf_le (fun j ↦ -g j) i)))
    have h1 : ∀ f : (Fin (n + 1) → ℕ) → EReal,
        -(altSupInf (n + 1) f) = altInfSup (n + 1) (fun v ↦ -f v) := fun f ↦ by
      simp only [altSupInf, altInfSup, hneg_sup]
      exact iInf_congr fun m ↦ ih2 (fun v ↦ f (Fin.cons m v))
    refine ⟨h1, fun f ↦ ?_⟩
    have h := congrArg Neg.neg (h1 fun v ↦ -f v)
    simpa only [neg_neg] using h.symm

private lemma altInfSup_neg (n : ℕ) (f : (Fin n → ℕ) → EReal) :
    -(altSupInf n f) = altInfSup n (fun v ↦ -f v) :=
  (altSupInf_neg_and_altInfSup_neg n).1 f

/-- Symmetry `x ∈ Πₙ ↔ -x ∈ Σₙ` for all `n : ℕ`. -/
theorem mem_pi_iff_neg_mem_sigma {n : ℕ} {x : ℝ} : x ∈ Pi n ↔ -x ∈ Sigma n := by
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨fun v ↦ -r v, hr.neg, ?_⟩
    have h := altInfSup_neg n (fun v ↦ (-(r v : ℝ) : EReal))
    simp only [neg_neg] at h
    have := congrArg Neg.neg h
    rw [neg_neg] at this
    rw [EReal.coe_neg, hx, ← this]
    push_cast; rfl
  · rintro ⟨r, hr, hx⟩
    refine ⟨fun v ↦ -r v, hr.neg, ?_⟩
    have h := congrArg Neg.neg hx
    rw [EReal.coe_neg, neg_neg, altInfSup_neg] at h
    convert h using 3 with v; push_cast; simp

/-- Consistency at `n = 1`: `Sigma 1 = Sigma1`. -/
theorem sigma_one_eq_sigma1 : Sigma 1 = Sigma1 := by
  ext x; rw [mem_sigma1_iff_exists_rat_iSup]
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨fun m ↦ r (Fin.cons m Fin.elim0),
      hr.comp (computable_fin_cons.comp .id (.const Fin.elim0)), ?_⟩
    simpa [altSupInf, altInfSup] using hx
  · rintro ⟨r, hr, hx⟩
    refine ⟨fun v ↦ r (v 0), hr.comp (Computable.fin_app.comp .id (.const 0)), ?_⟩
    simpa [altSupInf, altInfSup] using hx

/-- Consistency at `n = 1`: `Pi 1 = Pi1`. -/
theorem pi_one_eq_pi1 : Pi 1 = Pi1 := by
  ext x; rw [mem_pi_iff_neg_mem_sigma, sigma_one_eq_sigma1, mem_pi1_iff_neg_mem_sigma1]

/-- Consistency at `n = 1`: `Delta 1 = Delta1`. -/
theorem delta_one_eq_delta1 : Delta 1 = Delta1 := by
  rw [Delta, sigma_one_eq_sigma1, pi_one_eq_pi1, delta1_eq_sigma1_inter_pi1]

/-- Consistency at `n = 2`: `Sigma 2 = Sigma2`. -/
theorem sigma_two_eq_sigma2 : Sigma 2 = Sigma2 := by
  ext x; rw [mem_sigma2_iff_exists_rat_double]
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨fun m₁ m₂ ↦ r (Fin.cons m₁ (Fin.cons m₂ Fin.elim0)),
      (hr.comp (computable_fin_cons.comp .fst
        (computable_fin_cons.comp .snd (.const Fin.elim0)))).to₂, ?_⟩
    simpa [altSupInf, altInfSup] using hx
  · rintro ⟨r, hr, hx⟩
    refine ⟨fun v ↦ r (v 0) (v 1),
      hr.comp (Computable.fin_app.comp .id (.const 0))
        (Computable.fin_app.comp .id (.const 1)), ?_⟩
    simpa [altSupInf, altInfSup] using hx

/-- Consistency at `n = 2`: `Pi 2 = Pi2`. -/
theorem pi_two_eq_pi2 : Pi 2 = Pi2 := by
  ext x; rw [mem_pi_iff_neg_mem_sigma, sigma_two_eq_sigma2, mem_pi2_iff_neg_mem_sigma2]

/-- Consistency at `n = 2`: `Delta 2 = Delta2`. -/
theorem delta_two_eq_delta2 : Delta 2 = Delta2 := by
  rw [Delta, sigma_two_eq_sigma2, pi_two_eq_pi2, delta2_eq_sigma2_inter_pi2]

/-- Inclusion `Πₙ ⊆ Σₙ₊₁` for all `n : ℕ` (by ignoring the outermost `sup` index). -/
theorem pi_subset_sigma_succ (n : ℕ) : Pi n ⊆ Sigma (n + 1) := by
  rintro x ⟨r, hr, hx⟩
  refine ⟨fun v ↦ r (Fin.tail v), hr.comp computable_fin_tail, ?_⟩
  simp only [altSupInf, Fin.tail_cons, iSup_const, hx]

/-- Inclusion `Σₙ ⊆ Πₙ₊₁` for all `n : ℕ` (by ignoring the outermost `inf` index). -/
theorem sigma_subset_pi_succ (n : ℕ) : Sigma n ⊆ Pi (n + 1) := by
  intro x hx
  rw [mem_pi_iff_neg_mem_sigma]
  exact pi_subset_sigma_succ n (mem_pi_iff_neg_mem_sigma.mpr (by simpa using hx))

private lemma computable_fin_dropLast : ∀ (n : ℕ),
    Computable fun v : Fin (n + 1) → ℕ ↦ Fin.init v
  | 0 => (Computable.const Fin.elim0).of_eq fun _ ↦ by ext i; exact i.elim0
  | n + 1 => by
    have ih := computable_fin_dropLast n
    refine (computable_fin_cons.comp (Computable.fin_app.comp .id (.const 0))
      (ih.comp computable_fin_tail)).of_eq fun v ↦ ?_
    ext i; refine Fin.cases rfl (fun _ ↦ rfl) i

private lemma altSupInf_init : ∀ (n : ℕ) (f : (Fin n → ℕ) → EReal),
    altSupInf (n + 1) (fun v ↦ f (Fin.init v)) = altSupInf n f
  | 0, f => by
    have heq : ∀ m : ℕ, Fin.init (@Fin.cons 0 (fun _ ↦ ℕ) m Fin.elim0) = Fin.elim0 :=
      fun _ ↦ Subsingleton.elim _ _
    simp [altSupInf, heq]
  | n + 1, f => by
    simp only [altSupInf]
    refine iSup_congr fun m ↦ ?_
    have h := altSupInf_init n (fun w ↦ -f (Fin.cons m w))
    have h1 := congrArg Neg.neg h
    rw [altInfSup_neg, altInfSup_neg] at h1
    simp only [neg_neg] at h1
    have hinit : ∀ v : Fin (n + 1) → ℕ,
        Fin.init (@Fin.cons (n + 1) (fun _ ↦ ℕ) m v) = @Fin.cons n (fun _ ↦ ℕ) m (Fin.init v) :=
      fun v ↦ by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [Fin.init]
        · simp [Fin.init, Fin.castSucc_succ]
    simpa only [hinit] using h1

/-- Inclusion `Σₙ ⊆ Σₙ₊₁` for all `n : ℕ` (by ignoring the innermost index). -/
theorem sigma_subset_sigma_succ (n : ℕ) : Sigma n ⊆ Sigma (n + 1) := by
  rintro x ⟨r, hr, hx⟩
  refine ⟨fun v ↦ r (Fin.init v), hr.comp (computable_fin_dropLast n), ?_⟩
  rw [hx, ← altSupInf_init]

/-- Inclusion `Πₙ ⊆ Πₙ₊₁` for all `n : ℕ` (by ignoring the innermost index). -/
theorem pi_subset_pi_succ (n : ℕ) : Pi n ⊆ Pi (n + 1) := fun _ hx ↦
  mem_pi_iff_neg_mem_sigma.mpr (sigma_subset_sigma_succ n (mem_pi_iff_neg_mem_sigma.mp hx))

/-- Nested level monotonicity `Δₙ ⊆ Δₙ₊₁` for every `n : ℕ`. -/
theorem delta_subset_delta_succ (n : ℕ) : Delta n ⊆ Delta (n + 1) := fun _ ⟨hσ, hπ⟩ ↦
  ⟨pi_subset_sigma_succ n hπ, sigma_subset_pi_succ n hσ⟩

/-- Strict inclusion `Δ₂ ⊂neq Σ₂` and `Δ₂ ⊂neq Π₂` follow once we note `Δ₁ ⊂neq C₂ ⊆ Δ₂`. -/
theorem sigma1_subset_sigma2 : Sigma1 ⊆ Sigma2 := by
  rw [← sigma_one_eq_sigma1, ← sigma_two_eq_sigma2]; exact sigma_subset_sigma_succ 1

/-- Inclusion `Π₁ ⊆ Π₂`. -/
theorem pi1_subset_pi2 : Pi1 ⊆ Pi2 := by
  rw [← pi_one_eq_pi1, ← pi_two_eq_pi2]; exact pi_subset_pi_succ 1

end ZhengWeihrauch

end CslibFrontier.ComputableAnalysis
