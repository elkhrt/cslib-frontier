/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.ComputableAnalysis.ComputableReal

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Semi-Computable and Weakly Computable Real Numbers

First level of the Zheng–Weihrauch arithmetic hierarchy of real numbers: computable (`Δ₁`),
left-computable (`Σ₁`), right-computable (`Π₁`), semi-computable (`C₁ = Σ₁ ∪ Π₁`), and weakly
computable / difference-of-left-computable (`C₂`) real numbers, including `Δ₁ = Σ₁ ∩ Π₁`, the
Weihrauch–Zheng absolutely convergent computable-limit characterization of `C₂`, the Specker–Turing
separation `Δ₁ ⊂neq Σ₁, Π₁`, and the Ambos-Spies–Weihrauch–Zheng finite-injury separation
`Σ₁ ∪ Π₁ ⊂neq C₂`, proved under standard Lean axioms.

## Main definitions

* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Delta1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Sigma1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.Pi1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.SemiComputable`: the classes `Δ₁`, `Σ₁`, `Π₁`,
  and
  `C₁ = Σ₁ ∪ Π₁`.
* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.WeaklyComputable`: the class `C₂` of weakly
  computable (d-c.e.) real numbers `{ a - b | a, b ∈ Σ₁ }`.

## Main results

* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta1_eq_sigma1_inter_pi1`: `Δ₁ = Σ₁ ∩ Π₁`.
* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.mem_weaklyComputable_iff_summable_diff`: a real
  number belongs to `C₂` iff it is the limit of a computable sequence `(αₙ)` with
  `∑ |αₙ₊₁ - αₙ| < ∞`.
* `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.exists_pos_mem_sigma1_not_mem_delta1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta1_ssubset_sigma1`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.delta1_ssubset_pi1`: Specker–Turing halting-real
  separations `Δ₁ ⊂neq Σ₁` (with strictly positive witness) and `Δ₁ ⊂neq Π₁`.
* `ComputableAnalysis.ZhengWeihrauch.exists_mem_weaklyComputable_not_mem_semiComputable`,
  `CslibFrontier.ComputableAnalysis.ZhengWeihrauch.semiComputable_ssubset_weaklyComputable`:
  Ambos-Spies–Weihrauch–Zheng finite-injury separation `Σ₁ ∪ Π₁ ⊂neq C₂`.
-/

public section

namespace CslibFrontier.ComputableAnalysis

namespace ZhengWeihrauch

/-! ### First level: `Δ₁`, `Σ₁`, `Π₁`, `C₁`, and `C₂` -/

/-- The class `Δ₁` of computable real numbers. -/
@[expose] def Delta1 : Set ℝ := { x : ℝ | IsComputableReal x }

/-- The class `Σ₁` of left-computable real numbers: limits of monotonically increasing computable
sequences of computable real numbers. -/
@[expose] def Sigma1 : Set ℝ :=
  { x : ℝ | ∃ ζ : ℕ → ℝ, IsComputableRealSeq ζ ∧ Monotone ζ ∧
      Filter.Tendsto ζ Filter.atTop (nhds x) }

/-- The class `Π₁` of right-computable real numbers: limits of monotonically decreasing computable
sequences of computable real numbers. -/
@[expose] def Pi1 : Set ℝ :=
  { x : ℝ | ∃ ξ : ℕ → ℝ, IsComputableRealSeq ξ ∧ Antitone ξ ∧
      Filter.Tendsto ξ Filter.atTop (nhds x) }

/-- The class `C₁ = Σ₁ ∪ Π₁` of semi-computable real numbers. -/
@[expose]
def SemiComputable : Set ℝ := Sigma1 ∪ Pi1

/-- The class `C₂` of weakly computable (d-c.e.) real numbers `{ a - b | a, b ∈ Σ₁ }`. -/
@[expose] def WeaklyComputable : Set ℝ :=
  { x : ℝ | ∃ a ∈ Sigma1, ∃ b ∈ Sigma1, x = a - b }

/-- Membership in `Δ₁` is `IsComputableReal`. -/
@[simp] theorem mem_delta1_iff {x : ℝ} : x ∈ Delta1 ↔ IsComputableReal x := Iff.rfl

/-- Symmetry `x ∈ Π₁ ↔ -x ∈ Σ₁`. -/
theorem mem_pi1_iff_neg_mem_sigma1 {x : ℝ} : x ∈ Pi1 ↔ -x ∈ Sigma1 := by
  constructor
  · rintro ⟨ξ, hξ, hanti, hlim⟩
    exact ⟨fun n ↦ -ξ n, hξ.neg, fun _ _ h ↦ neg_le_neg (hanti h), hlim.neg⟩
  · rintro ⟨ζ, hζ, hmono, hlim⟩
    exact ⟨fun n ↦ -ζ n, hζ.neg, fun _ _ h ↦ neg_le_neg (hmono h), by simpa using hlim.neg⟩

/-- Rational monotone approximation characterization of `Σ₁`: `x ∈ Σ₁` iff `x` is the limit of a
monotonically increasing computable rational sequence. -/
theorem mem_sigma1_iff_exists_monotone_rat {x : ℝ} :
    x ∈ Sigma1 ↔
      ∃ r : ℕ → ℚ, IsComputableRatSeq r ∧ Monotone r ∧
        Filter.Tendsto (fun n ↦ (r n : ℝ)) Filter.atTop (nhds x) := by
  constructor
  · rintro ⟨ζ, hζ, hmono, hlim⟩
    obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hζ
    let base : ℕ → ℚ := fun n ↦ q n (n + 1) - (2 : ℚ) ^ (-((n + 1 : ℕ) : ℤ))
    have hbase : IsComputableRatSeq base :=
      (hq.comp .id Computable.succ).sub
        ((IsComputableRatMap.const 2).zpow
          (primrec_int_neg.to_comp.comp (primrec_int_ofNat.to_comp.comp Computable.succ)))
    let r : ℕ → ℚ := fun N ↦
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one base
    have hr : IsComputableRatSeq r :=
      IsComputableRatMap.sup'_range .id (hbase.comp .snd).to₂
    have hr_mono : Monotone r := fun a b hab ↦
      Finset.sup'_mono base (Finset.range_mono (Nat.succ_le_succ hab))
        Finset.nonempty_range_add_one
    have hbase_bounds : ∀ n : ℕ,
        ζ n - (2 : ℝ) ^ (-(n : ℤ)) ≤ (base n : ℝ) ∧ (base n : ℝ) ≤ ζ n := fun n ↦ by
      have he := abs_lt.mp (hc n (n + 1))
      have hd : (2 : ℝ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(n : ℤ)) := by
        rw [show (2 : ℝ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) =
          (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) by rw [zpow_one],
          ← zpow_add₀ two_ne_zero]; congr 1; push_cast; omega
      have hbc : (base n : ℝ) = (q n (n + 1) : ℝ) - (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
        dsimp [base]; rw [Rat.cast_sub, Rat.cast_zpow, Rat.cast_ofNat]
      rw [hbc]
      exact ⟨by linarith [he.2, hd], by linarith [he.1]⟩
    have hr_le : ∀ N : ℕ, (r N : ℝ) ≤ x := fun N ↦ by
      have hcast : (r N : ℝ) =
          (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k ↦ (base k : ℝ) := by
        simpa [r] using Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one
          (f := base) (g := ((↑) : ℚ → ℝ)) (fun _ _ ↦ Rat.cast_max _ _)
      rw [hcast]
      exact Finset.sup'_le _ _ fun k _ ↦
        (hbase_bounds k).2.trans (ge_of_tendsto hlim
          (Filter.eventually_atTop.mpr ⟨k, fun m hm ↦ hmono hm⟩))
    have hr_ge : ∀ N : ℕ, ζ N - (2 : ℝ) ^ (-(N : ℤ)) ≤ (r N : ℝ) := fun N ↦
      (hbase_bounds N).1.trans <| by
        exact_mod_cast Finset.le_sup' base (Finset.mem_range.mpr (Nat.lt_succ_self N))
    have hlo_lim : Filter.Tendsto (fun N : ℕ ↦ ζ N - (2 : ℝ) ^ (-(N : ℤ)))
        Filter.atTop (nhds x) := by
      have hz : Filter.Tendsto (fun N : ℕ ↦ (2 : ℝ) ^ (-(N : ℤ))) Filter.atTop (nhds 0) := by
        simpa only [one_div, inv_pow, zpow_neg, zpow_natCast] using
          tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa using hlim.sub hz
    exact ⟨r, hr, hr_mono, tendsto_of_tendsto_of_tendsto_of_le_of_le hlo_lim tendsto_const_nhds
      hr_ge hr_le⟩
  · rintro ⟨r, hr, hmono, hlim⟩
    exact ⟨fun n ↦ (r n : ℝ), isComputableRealSeq_rat hr,
      fun _ _ h ↦ Rat.cast_le.mpr (hmono h), hlim⟩

/-- Extended-real supremum characterization of `Σ₁`: `x ∈ Σ₁` iff `(x : EReal) = ⨆ n, (r n : EReal)`
for a computable rational sequence `r`. -/
theorem mem_sigma1_iff_exists_rat_iSup {x : ℝ} :
    x ∈ Sigma1 ↔
      ∃ r : ℕ → ℚ, IsComputableRatSeq r ∧ (x : EReal) = ⨆ n : ℕ, ((r n : ℝ) : EReal) := by
  rw [mem_sigma1_iff_exists_monotone_rat]
  constructor
  · rintro ⟨r, hr, hmono, hlim⟩
    refine ⟨r, hr, le_antisymm ?_ (iSup_le fun n ↦ EReal.coe_le_coe_iff.mpr
      (ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨n,
        fun m hm ↦ Rat.cast_le.mpr (hmono hm)⟩)))⟩
    have hlimE : Filter.Tendsto (fun n ↦ ((r n : ℝ) : EReal)) Filter.atTop (nhds (x : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp hlim
    exact le_of_tendsto' hlimE fun n ↦ le_iSup (fun k ↦ ((r k : ℝ) : EReal)) n
  · rintro ⟨r, hr, hx⟩
    let s : ℕ → ℚ := fun N ↦ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one r
    have hs : IsComputableRatSeq s := IsComputableRatMap.sup'_range .id (hr.comp .snd).to₂
    have hs_mono : Monotone s := fun a b hab ↦
      Finset.sup'_mono r (Finset.range_mono (Nat.succ_le_succ hab)) Finset.nonempty_range_add_one
    have hr_le : ∀ n : ℕ, (r n : ℝ) ≤ x := fun n ↦
      EReal.coe_le_coe_iff.mp (hx ▸ le_iSup (fun k ↦ ((r k : ℝ) : EReal)) n)
    have hs_le : ∀ N : ℕ, (s N : ℝ) ≤ x := fun N ↦ by
      obtain ⟨k, _, hsk⟩ : ∃ k ∈ Finset.range (N + 1), s N = r k := by
        induction N with
        | zero => exact ⟨0, by simp, by simp [s]⟩
        | succ m ih =>
          obtain ⟨k, hk, hmk⟩ := ih
          have hstep : s (m + 1) = max (r (m + 1)) (s m) := by
            simp [s, Finset.range_add_one]
          rcases max_choice (r (m + 1)) (s m) with hc | hc
          · exact ⟨m + 1, Finset.mem_range.mpr (Nat.lt_succ_self _), hstep.trans hc⟩
          · exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)),
              hstep.trans (hc.trans hmk)⟩
      rw [hsk]; exact hr_le k
    refine ⟨s, hs, hs_mono, ?_⟩
    have hbdd : BddAbove (Set.range fun N : ℕ ↦ (s N : ℝ)) :=
      ⟨x, by rintro _ ⟨N, rfl⟩; exact hs_le N⟩
    have htend := tendsto_atTop_ciSup (f := fun N : ℕ ↦ (s N : ℝ))
      (fun _ _ h ↦ Rat.cast_le.mpr (hs_mono h)) hbdd
    suffices hsup : (⨆ N : ℕ, (s N : ℝ)) = x by rwa [hsup] at htend
    refine le_antisymm (ciSup_le hs_le) ?_
    rw [← EReal.coe_le_coe_iff, hx]
    refine iSup_le fun n ↦ EReal.coe_le_coe_iff.mpr ?_
    have hle : (r n : ℝ) ≤ (s n : ℝ) := by
      exact_mod_cast Finset.le_sup' r (Finset.mem_range.mpr (Nat.lt_succ_self n))
    exact hle.trans (le_ciSup hbdd n)

/-- First-level characterization (Pour-El–Richards / Zheng–Weihrauch): a real number is computable
(`x ∈ Δ₁`) if and only if it is both left- and right-computable (`x ∈ Σ₁ ∩ Π₁`). -/
theorem mem_delta1_iff_mem_sigma1_and_pi1 {x : ℝ} :
    x ∈ Delta1 ↔ x ∈ Sigma1 ∧ x ∈ Pi1 := by
  constructor
  · intro hx
    have hsup : ∀ z : ℝ, IsComputableReal z → z ∈ Sigma1 := fun z hz ↦ by
      obtain ⟨r, hr, hcr⟩ := isComputableReal_iff_exists_rat_approx.mp hz
      let a : ℕ → ℚ := fun M ↦ r M - (2 : ℚ) ^ (-(M : ℤ))
      have ha : IsComputableRatSeq a :=
        hr.sub ((IsComputableRatMap.const 2).zpow
          (primrec_int_neg.to_comp.comp primrec_int_ofNat.to_comp))
      refine mem_sigma1_iff_exists_rat_iSup.mpr ⟨a, ha, le_antisymm ?_ ?_⟩
      · have halim : Filter.Tendsto (fun M : ℕ ↦ ((a M : ℝ) : EReal)) Filter.atTop
            (nhds (z : EReal)) := by
          refine continuous_coe_real_ereal.continuousAt.tendsto.comp ?_
          rw [Metric.tendsto_atTop]
          intro ε hε
          have hz0 : Filter.Tendsto (fun M : ℕ ↦ (2 : ℝ) * (2 : ℝ) ^ (-(M : ℤ)))
              Filter.atTop (nhds 0) := by
            simpa only [mul_zero, one_div, inv_pow, zpow_neg, zpow_natCast] using
              (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2)
                (by norm_num)).const_mul 2
          obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz0 ε hε
          refine ⟨N, fun M hM ↦ ?_⟩
          rw [Real.dist_eq]
          have he := abs_lt.mp (hcr M)
          have hpos : (a M : ℝ) ≤ z := by dsimp [a]; push_cast; linarith [he.1]
          have hhi : z - (a M : ℝ) < 2 * (2 : ℝ) ^ (-(M : ℤ)) := by
            dsimp [a]; push_cast; linarith [he.2]
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hpos)]
          have h2p : (0 : ℝ) < 2 * (2 : ℝ) ^ (-(M : ℤ)) := mul_pos two_pos (zpow_pos two_pos _)
          exact hhi.trans (by simpa [Real.dist_eq, abs_of_pos h2p] using hN M hM)
        exact le_of_tendsto' halim fun M ↦ le_iSup (fun k ↦ ((a k : ℝ) : EReal)) M
      · refine iSup_le fun M ↦ EReal.coe_le_coe_iff.mpr ?_
        dsimp [a]; push_cast; linarith [(abs_lt.mp (hcr M)).1]
    exact ⟨hsup x hx, mem_pi1_iff_neg_mem_sigma1.mpr (hsup (-x) hx.neg)⟩
  · rintro ⟨hs, hp⟩
    obtain ⟨a, ha, ha_mono, ha_lim⟩ := mem_sigma1_iff_exists_monotone_rat.mp hs
    obtain ⟨b, hb, hb_mono, hb_lim⟩ :=
      mem_sigma1_iff_exists_monotone_rat.mp (mem_pi1_iff_neg_mem_sigma1.mp hp)
    -- `a n ≤ x ≤ -b n` and `(-b n) - a n → 0`
    let u : ℕ → ℚ := fun n ↦ -b n
    have hu : IsComputableRatSeq u := hb.neg
    have ha_le : ∀ n, (a n : ℝ) ≤ x := fun n ↦
      ge_of_tendsto ha_lim (Filter.eventually_atTop.mpr ⟨n,
        fun m hm ↦ Rat.cast_le.mpr (ha_mono hm)⟩)
    have hx_le : ∀ n, x ≤ (u n : ℝ) := fun n ↦ by
      have : (b n : ℝ) ≤ -x :=
        ge_of_tendsto hb_lim (Filter.eventually_atTop.mpr ⟨n,
          fun m hm ↦ Rat.cast_le.mpr (hb_mono hm)⟩)
      dsimp [u]; push_cast; linarith
    let close : ℕ → ℕ → Bool := fun M n ↦ decide (u n - a n < (2 : ℚ) ^ (-(M : ℤ)))
    have hclose : Computable₂ close :=
      (((hu.comp .snd).sub (ha.comp .snd)).decide_lt
        ((IsComputableRatMap.const 2).zpow
          (primrec_int_neg.to_comp.comp (primrec_int_ofNat.to_comp.comp .fst)))).to₂
    have hex : ∀ M : ℕ, ∃ n : ℕ, close M n = true := fun M ↦ by
      have hdiff : Filter.Tendsto (fun n ↦ (u n : ℝ) - (a n : ℝ)) Filter.atTop (nhds 0) := by
        have hulim : Filter.Tendsto (fun n ↦ (u n : ℝ)) Filter.atTop (nhds x) := by
          simpa [u] using hb_lim.neg
        simpa using hulim.sub ha_lim
      obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hdiff ((2 : ℝ) ^ (-(M : ℤ))) (zpow_pos two_pos _)
      refine ⟨n, decide_eq_true ?_⟩
      have hnn : 0 ≤ (u n : ℝ) - (a n : ℝ) := by linarith [ha_le n, hx_le n]
      have hlt : ((u n - a n : ℚ) : ℝ) < (((2 : ℚ) ^ (-(M : ℤ)) : ℚ) : ℝ) := by
        rw [Rat.cast_sub, Rat.cast_zpow, Rat.cast_ofNat]
        simpa [Real.dist_eq, abs_of_nonneg hnn] using hn n le_rfl
      exact Rat.cast_lt.mp hlt
    let idx : ℕ → ℕ := fun M ↦ Nat.find (hex M)
    have hidx : Computable idx :=
      Partrec.of_eq_tot (Partrec.rfind hclose.partrec₂) fun M ↦ nat_find_mem_rfind (hex M)
    refine isComputableReal_iff_exists_rat_approx.mpr ⟨fun M ↦ a (idx M), ha.comp hidx, fun M ↦ ?_⟩
    have hsp : (u (idx M) : ℝ) - (a (idx M) : ℝ) < (2 : ℝ) ^ (-(M : ℤ)) := by
      have hq := Rat.cast_lt (K := ℝ).mpr (of_decide_eq_true (Nat.find_spec (hex M)))
      rwa [Rat.cast_sub, Rat.cast_zpow, Rat.cast_ofNat] at hq
    rw [abs_of_nonneg (sub_nonneg.mpr (ha_le (idx M)))]
    linarith [hx_le (idx M)]

/-- Set equality `Δ₁ = Σ₁ ∩ Π₁`. -/
theorem delta1_eq_sigma1_inter_pi1 : Delta1 = Sigma1 ∩ Pi1 :=
  Set.ext fun _ ↦ mem_delta1_iff_mem_sigma1_and_pi1

/-- Inclusion `Δ₁ ⊆ Σ₁`. -/
theorem delta1_subset_sigma1 : Delta1 ⊆ Sigma1 := by
  rw [delta1_eq_sigma1_inter_pi1]; exact Set.inter_subset_left

/-- Inclusion `Δ₁ ⊆ Π₁`. -/
theorem delta1_subset_pi1 : Delta1 ⊆ Pi1 := by
  rw [delta1_eq_sigma1_inter_pi1]; exact Set.inter_subset_right

/-- Inclusion `Σ₁ ⊆ C₂`. -/
theorem sigma1_subset_weaklyComputable : Sigma1 ⊆ WeaklyComputable := fun x hx ↦
  ⟨x, hx, 0, delta1_subset_sigma1 isComputableReal_zero, (sub_zero x).symm⟩

/-- Inclusion `Π₁ ⊆ C₂`. -/
theorem pi1_subset_weaklyComputable : Pi1 ⊆ WeaklyComputable := fun x hx ↦
  ⟨0, delta1_subset_sigma1 isComputableReal_zero, -x, mem_pi1_iff_neg_mem_sigma1.mp hx,
    by simp⟩

/-- Inclusion `C₁ ⊆ C₂`. -/
theorem semiComputable_subset_weaklyComputable : SemiComputable ⊆ WeaklyComputable :=
  Set.union_subset sigma1_subset_weaklyComputable pi1_subset_weaklyComputable

/-- Inclusion `Δ₁ ⊆ C₂`. -/
theorem delta1_subset_weaklyComputable : Delta1 ⊆ WeaklyComputable :=
  delta1_subset_sigma1.trans sigma1_subset_weaklyComputable

/-- Weihrauch–Zheng : a real number `x` belongs to `C₂` if and only if there exists a
computable sequence `α : ℕ → ℝ` with `Summable (fun n ↦ |α (n + 1) - α n|)` and `α n → x`.
-/
theorem mem_weaklyComputable_iff_summable_diff {x : ℝ} :
    x ∈ WeaklyComputable ↔
      ∃ α : ℕ → ℝ, IsComputableRealSeq α ∧
        Summable (fun n : ℕ ↦ |α (n + 1) - α n|) ∧
        Filter.Tendsto α Filter.atTop (nhds x) := by
  constructor
  · rintro ⟨a, ⟨ζ, hζ, hζm, hζl⟩, b, ⟨ξ, hξ, hξm, hξl⟩, rfl⟩
    refine ⟨fun n ↦ ζ n - ξ n, hζ.sub hξ, ?_, hζl.sub hξl⟩
    have hsum_bd : ∀ N : ℕ, ∑ n ∈ Finset.range N, |(ζ (n + 1) - ξ (n + 1)) - (ζ n - ξ n)| ≤
        (a - ζ 0) + (b - ξ 0) := fun N ↦ by
      have htel : ∑ n ∈ Finset.range N, ((ζ (n + 1) - ζ n) + (ξ (n + 1) - ξ n)) =
          (ζ N - ζ 0) + (ξ N - ξ 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_range_sub (f := ζ), Finset.sum_range_sub (f := ξ)]
      have hζN : ζ N ≤ a :=
        ge_of_tendsto hζl (Filter.eventually_atTop.mpr ⟨N, fun m hm ↦ hζm hm⟩)
      have hξN : ξ N ≤ b :=
        ge_of_tendsto hξl (Filter.eventually_atTop.mpr ⟨N, fun m hm ↦ hξm hm⟩)
      refine (Finset.sum_le_sum fun n _ ↦ ?_).trans (htel.le.trans (by linarith))
      rw [show (ζ (n + 1) - ξ (n + 1)) - (ζ n - ξ n) =
        (ζ (n + 1) - ζ n) + -(ξ (n + 1) - ξ n) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr (hζm (Nat.le_succ n))),
        abs_of_nonneg (sub_nonneg.mpr (hξm (Nat.le_succ n)))]
    exact summable_of_sum_range_le (fun _ ↦ abs_nonneg _) hsum_bd
  · rintro ⟨α, hα, hsum, hlim⟩
    let dPos : ℕ → ℝ := fun k ↦ max (α (k + 1) - α k) 0
    let dNeg : ℕ → ℝ := fun k ↦ max (α k - α (k + 1)) 0
    have hdPos_comp : IsComputableRealSeq dPos :=
      ((hα.comp Computable.succ).sub hα).max isComputableReal_zero.constSeq
    have hdNeg_comp : IsComputableRealSeq dNeg :=
      (hα.sub (hα.comp Computable.succ)).max isComputableReal_zero.constSeq
    have hdPos_sum : Summable dPos :=
      Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _)
        (fun k ↦ max_le (le_abs_self _) (abs_nonneg _)) hsum
    have hdNeg_sum : Summable dNeg :=
      Summable.of_nonneg_of_le (fun _ ↦ le_max_right _ _)
        (fun k ↦ max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _)) hsum
    let ζ : ℕ → ℝ := fun N ↦ α 0 + ∑ k ∈ Finset.range N, dPos k
    let ξ : ℕ → ℝ := fun N ↦ ∑ k ∈ Finset.range N, dNeg k
    have hζ_comp : IsComputableRealSeq ζ :=
      (hα.apply 0).constSeq.add ((hdPos_comp.comp₂ Computable.snd.to₂).sum_range .id)
    have hξ_comp : IsComputableRealSeq ξ :=
      (hdNeg_comp.comp₂ Computable.snd.to₂).sum_range .id
    have hζ_mono : Monotone ζ := fun _ _ hmn ↦
      add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
        fun _ _ _ ↦ le_max_right _ _)
    have hξ_mono : Monotone ξ := fun m n hmn ↦
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun _ _ _ ↦ le_max_right _ _
    have hζ_lim : Filter.Tendsto ζ Filter.atTop (nhds (α 0 + ∑' k, dPos k)) :=
      tendsto_const_nhds.add hdPos_sum.hasSum.tendsto_sum_nat
    have hξ_lim : Filter.Tendsto ξ Filter.atTop (nhds (∑' k, dNeg k)) :=
      hdNeg_sum.hasSum.tendsto_sum_nat
    have hdiff : ∀ N : ℕ, ζ N - ξ N = α N := fun N ↦ by
      dsimp [ζ, ξ]
      rw [add_sub_assoc, ← Finset.sum_sub_distrib]
      have hterm : ∀ k, dPos k - dNeg k = α (k + 1) - α k := fun k ↦ by
        dsimp [dPos, dNeg]
        rcases le_total (α k) (α (k + 1)) with h | h
        · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h), sub_zero]
        · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring
      simp_rw [hterm]
      rw [Finset.sum_range_sub (f := α)]; ring
    have heq : x = (α 0 + ∑' k, dPos k) - ∑' k, dNeg k :=
      tendsto_nhds_unique hlim ((hζ_lim.sub hξ_lim).congr hdiff)
    exact ⟨α 0 + ∑' k, dPos k, ⟨ζ, hζ_comp, hζ_mono, hζ_lim⟩,
      ∑' k, dNeg k, ⟨ξ, hξ_comp, hξ_mono, hξ_lim⟩, heq⟩

/-! ### Bounded-step evaluation and separations `Δ₁ ⊂neq Σ₁`, `Δ₁ ⊂neq Π₁`, `C₁ ⊂neq C₂` -/

section FirstLevelSeparations

private def haltsBy (s e x : ℕ) : Bool :=
  (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) x).isSome

private lemma primrec_haltsBy : Primrec fun p : (ℕ × ℕ) × ℕ ↦ haltsBy p.1.1 p.1.2 p.2 := by
  have hev : Primrec fun p : (ℕ × ℕ) × ℕ ↦
      Nat.Partrec.Code.evaln p.1.1 (Denumerable.ofNat Nat.Partrec.Code p.1.2) p.2 :=
    Nat.Partrec.Code.primrec_evaln.comp <| Primrec.pair
      (Primrec.pair (Primrec.fst.comp .fst)
        ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.snd.comp .fst)))
      .snd
  exact (Primrec.option_casesOn hev (.const false) (Primrec.const true).to₂).of_eq fun p ↦ by
    dsimp only [haltsBy]
    cases Nat.Partrec.Code.evaln p.1.1 (Denumerable.ofNat Nat.Partrec.Code p.1.2) p.2 <;> rfl

private lemma haltsBy_mono {s₁ s₂ e x : ℕ} (hs : s₁ ≤ s₂) (h : haltsBy s₁ e x = true) :
    haltsBy s₂ e x = true := by
  dsimp [haltsBy] at h ⊢
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨y, Nat.Partrec.Code.evaln_mono hs hy⟩

private lemma exists_haltsBy_iff (e x : ℕ) :
    (∃ s : ℕ, haltsBy s e x = true) ↔
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) x).Dom := by
  simp only [haltsBy, Option.isSome_iff_exists, Part.dom_iff_mem]
  constructor
  · rintro ⟨s, y, hy⟩; exact ⟨y, Nat.Partrec.Code.evaln_complete.mpr ⟨s, hy⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hy
    exact ⟨s, y, hs⟩

private lemma haltsSelf_iff (e s : ℕ) :
    (∃ t, haltsBy t e 0 = true) ↔
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom :=
  let _ := s; exists_haltsBy_iff e 0

/-- There exists a strictly positive left-computable real number `α ∈ Σ₁ \ Δ₁` (Turing's ternary
halting real `∑_{e : eval(c_e, 0)↓} 3 ^ (-(e + 1))`). -/
theorem exists_pos_mem_sigma1_not_mem_delta1 :
    ∃ α : ℝ, 0 < α ∧ α ∈ Sigma1 ∧ α ∉ Delta1 := by
  classical
  let bit : ℕ → ℕ → ℚ := fun s e ↦ if haltsBy s e 0 = true then (1 / 3 : ℚ) ^ (e + 1) else 0
  let r : ℕ → ℚ := fun s ↦ ∑ e ∈ Finset.range s, bit s e
  have hbit : IsComputableRatMap₂ bit :=
    (IsComputableRatMap.ite (primrec_haltsBy.to_comp.comp (.pair (.pair .fst .snd) (.const 0)))
      ((IsComputableRatMap.const (1 / 3)).pow (Computable.succ.comp .snd))
      (.const 0)).to₂
  have hr : IsComputableRatSeq r := IsComputableRatMap.sum_range .id hbit
  have hr_mono : Monotone r := fun s₁ s₂ hs ↦ by
    calc ∑ e ∈ Finset.range s₁, bit s₁ e
        ≤ ∑ e ∈ Finset.range s₁, bit s₂ e := Finset.sum_le_sum fun e _ ↦ by
          dsimp [bit]
          cases h1 : haltsBy s₁ e 0
          · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> positivity
          · simp only [haltsBy_mono hs h1, ↓reduceIte, le_rfl]
      _ ≤ ∑ e ∈ Finset.range s₂, bit s₂ e :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hs) fun e _ _ ↦ by
            dsimp [bit]; split_ifs <;> positivity
  let term : ℕ → ℝ := fun e ↦
    if (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom then
      (1 / 3 : ℝ) ^ (e + 1)
    else 0
  have hgeo : Summable fun e : ℕ ↦ (1 / 3 : ℝ) ^ (e + 1) :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_right (1 / 3) |>.congr
      fun e ↦ (pow_succ _ _).symm
  have hterm_sum : Summable term :=
    Summable.of_nonneg_of_le (fun e ↦ by dsimp [term]; split_ifs <;> positivity)
      (fun e ↦ by dsimp [term]; split_ifs <;> [exact le_rfl; positivity]) hgeo
  set α : ℝ := ∑' e : ℕ, term e
  have hr_lim : Filter.Tendsto (fun s ↦ (r s : ℝ)) Filter.atTop (nhds α) := by
    have hr_le : ∀ s : ℕ, (r s : ℝ) ≤ α := fun s ↦ by
      dsimp [r]; rw [Rat.cast_sum]
      calc ∑ e ∈ Finset.range s, (bit s e : ℝ)
          ≤ ∑ e ∈ Finset.range s, term e := Finset.sum_le_sum fun e _ ↦ by
            dsimp [bit, term]
            cases h : haltsBy s e 0
            · simp only [Bool.false_eq_true, ↓reduceIte, Rat.cast_zero]
              split_ifs <;> positivity
            · have hd : (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom :=
                (exists_haltsBy_iff e 0).mp ⟨s, h⟩
              simp only [hd, ↓reduceIte]; push_cast; rfl
        _ ≤ α := hterm_sum.sum_le_tsum _ fun e _ ↦ by dsimp [term]; split_ifs <;> positivity
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hterm_sum.hasSum.tendsto_sum_nat ε hε
    classical
    have hstage : ∀ e ∈ Finset.range N, ∃ s : ℕ, (bit s e : ℝ) = term e := fun e _ ↦ by
      dsimp [term]
      by_cases hd : (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom
      · obtain ⟨s, hs⟩ := (exists_haltsBy_iff e 0).mpr hd
        exact ⟨s, by simp [bit, hs, hd]⟩
      · exact ⟨0, by
          have hn : haltsBy 0 e 0 ≠ true := fun h ↦ hd ((exists_haltsBy_iff e 0).mp ⟨0, h⟩)
          simp [bit, hn, hd]⟩
    choose st hst using hstage
    let S := max N ((Finset.range N).attach.sup fun e ↦ st e.1 e.2)
    refine ⟨S, fun s hs ↦ ?_⟩
    have hsum_le : ∑ e ∈ Finset.range N, term e ≤ (r s : ℝ) := by
      dsimp [r]; rw [Rat.cast_sum]
      calc ∑ e ∈ Finset.range N, term e
          ≤ ∑ e ∈ Finset.range N, (bit s e : ℝ) := Finset.sum_le_sum fun e he ↦ by
            have hle_st : st e he ≤ s :=
              (Finset.le_sup (f := fun x : {x // x ∈ Finset.range N} ↦ st x.1 x.2)
                (Finset.mem_attach _ ⟨e, he⟩)).trans ((le_max_right _ _).trans hs)
            rw [← hst e he]; dsimp [bit]
            cases h : haltsBy (st e he) e 0
            · simp only [Bool.false_eq_true, ↓reduceIte, Rat.cast_zero]
              split_ifs <;> positivity
            · simp only [haltsBy_mono hle_st h, ↓reduceIte, le_rfl]
        _ ≤ ∑ e ∈ Finset.range s, (bit s e : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ((le_max_left _ _).trans hs))
              fun e _ _ ↦ by dsimp [bit]; split_ifs <;> positivity
    have hN' : α - ∑ e ∈ Finset.range N, term e < ε := by
      have h1 := hN N le_rfl
      rw [Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (hterm_sum.sum_le_tsum _ fun e _ ↦ by
          dsimp [term]; split_ifs <;> positivity))] at h1
      exact h1
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hr_le s))]
    linarith [hr_le s]
  have hα_pos : 0 < α := by
    let e0 := Encodable.encode Nat.Partrec.Code.zero
    have hdom0 : (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e0) 0).Dom := by
      rw [Denumerable.ofNat_encode, Part.dom_iff_mem]
      exact ⟨0, Part.mem_some_iff.mpr rfl⟩
    have hle : term e0 ≤ α :=
      hterm_sum.le_tsum e0 fun e _ ↦ by dsimp [term]; split_ifs <;> positivity
    exact (by dsimp [term]; simp only [hdom0, ↓reduceIte]; positivity : 0 < term e0).trans_le hle
  have hα_sigma : α ∈ Sigma1 :=
    mem_sigma1_iff_exists_monotone_rat.mpr ⟨r, hr, hr_mono, hr_lim⟩
  have hα_not_delta : α ∉ Delta1 := by
    intro hcomp
    obtain ⟨q, hq, hc⟩ := isComputableReal_iff_exists_rat_approx.mp hcomp
    have hSprev : IsComputableRatMap fun prev : List Bool ↦
        ∑ j ∈ Finset.range prev.length,
          if prev.getD j false = true then (1 / 3 : ℚ) ^ (j + 1) else 0 :=
      IsComputableRatMap.sum_range Computable.list_length
        (IsComputableRatMap.ite ((Primrec.list_getD false).to_comp.comp .fst .snd)
          ((IsComputableRatMap.const (1 / 3)).pow (Computable.succ.comp .snd))
          (.const 0)).to₂
    have he_len : Computable (@List.length Bool) := Computable.list_length
    have hM : Computable fun prev : List Bool ↦ 2 * prev.length + 4 :=
      Primrec.nat_add.to_comp.comp (Primrec.nat_double.to_comp.comp he_len) (.const 4)
    have hpred : Computable fun prev : List Bool ↦
        decide ((3 / 4 : ℚ) * (1 / 3 : ℚ) ^ (prev.length + 1) ≤
          q (2 * prev.length + 4) -
            ∑ j ∈ Finset.range prev.length,
              if prev.getD j false = true then (1 / 3 : ℚ) ^ (j + 1) else 0) :=
      ((IsComputableRatMap.const (3 / 4)).mul
        ((IsComputableRatMap.const (1 / 3)).pow (Computable.succ.comp he_len))).decide_le
        ((hq.comp hM).sub hSprev)
    let acc : ℕ → List Bool := fun n ↦
      Nat.rec [] (fun _ l ↦
        let e := l.length
        let Sprev : ℚ := ∑ j ∈ Finset.range e,
          if l.getD j false = true then (1 / 3 : ℚ) ^ (j + 1) else 0
        l ++ [decide ((3 / 4 : ℚ) * (1 / 3 : ℚ) ^ (e + 1) ≤ q (2 * e + 4) - Sprev)]) n
    have hacc : Computable acc :=
      Computable.nat_rec .id (.const [])
        (Computable.list_concat.comp (Computable.snd.comp .snd)
          (hpred.comp (Computable.snd.comp .snd))).to₂
    have hacc_len : ∀ n, (acc n).length = n := fun n ↦ by
      induction n with
      | zero => rfl
      | succ k ih => dsimp [acc]; rw [List.length_append, ih]; simp
    have htail_bd : ∀ e : ℕ, ∑' k : ℕ, term (k + (e + 1)) ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ (e + 1) :=
      fun e ↦ by
        have hts : HasSum (fun k : ℕ ↦ (1 / 3 : ℝ) ^ (e + 2) * (1 / 3 : ℝ) ^ k)
            ((1 / 2 : ℝ) * (1 / 3 : ℝ) ^ (e + 1)) := by
          have h := (hasSum_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by positivity)
            (by norm_num)).mul_left ((1 / 3 : ℝ) ^ (e + 2))
          rwa [show (1 / 3 : ℝ) ^ (e + 2) * (1 - (1 / 3 : ℝ))⁻¹ =
            (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ (e + 1) by rw [pow_succ]; ring] at h
        have hsub : Summable fun k : ℕ ↦ term (k + (e + 1)) :=
          (summable_nat_add_iff (e + 1)).mpr hterm_sum
        refine (hsub.tsum_le_tsum (fun k ↦ ?_) hts.summable).trans_eq hts.tsum_eq
        dsimp [term]; split_ifs
        · rw [show k + (e + 1) + 1 = (e + 2) + k by omega, pow_add]
        · positivity
    have hacc_spec : ∀ n j, j < n →
        ((acc n).getD j false = true ↔
          (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code j) 0).Dom) := by
      intro n
      induction n with
      | zero => intro _ hj; omega
      | succ e ih =>
        intro j hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | hje
        · dsimp [acc]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rwa [hacc_len]),
            ← List.getD_eq_getElem?_getD]
          exact ih j hlt
        · subst j
          have hget : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
            intro l b; simp [List.getD_eq_getElem?_getD]
          have hstep : (acc (e + 1)).getD e false =
              decide ((3 / 4 : ℚ) * (1 / 3 : ℚ) ^ (e + 1) ≤ q (2 * e + 4) -
                ∑ i ∈ Finset.range e,
                  if (acc e).getD i false = true then (1 / 3 : ℚ) ^ (i + 1) else 0) := by
            have h1 : acc (e + 1) = acc e ++
                [decide ((3 / 4 : ℚ) * (1 / 3 : ℚ) ^ ((acc e).length + 1) ≤
                  q (2 * (acc e).length + 4) -
                    ∑ i ∈ Finset.range (acc e).length,
                      if (acc e).getD i false = true then (1 / 3 : ℚ) ^ (i + 1) else 0)] := rfl
            rw [h1]
            have h2 := hget (acc e)
              (decide ((3 / 4 : ℚ) * (1 / 3 : ℚ) ^ (e + 1) ≤ q (2 * e + 4) -
                ∑ i ∈ Finset.range e,
                  if (acc e).getD i false = true then (1 / 3 : ℚ) ^ (i + 1) else 0))
            simpa only [hacc_len e] using h2
          rw [hstep, decide_eq_true_eq]
          set Sprev : ℚ := ∑ i ∈ Finset.range e,
            if (acc e).getD i false = true then (1 / 3 : ℚ) ^ (i + 1) else 0
          have hS_eq : (Sprev : ℝ) = ∑ i ∈ Finset.range e, term i := by
            dsimp [Sprev]; rw [Rat.cast_sum]
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            have hiff := ih i (Finset.mem_range.mp hi)
            dsimp [term]
            by_cases hb : (acc e).getD i false = true
            · simp only [hb, hiff.mp hb, ↓reduceIte]; push_cast; rfl
            · have hnd : ¬(Nat.Partrec.Code.eval
                (Denumerable.ofNat Nat.Partrec.Code i) 0).Dom := fun hd ↦ hb (hiff.mpr hd)
              simp only [hb, hnd, ↓reduceIte]; push_cast; rfl
          have hsplit : α = (Sprev : ℝ) + term e + ∑' k : ℕ, term (k + (e + 1)) := by
            have := (hterm_sum.sum_add_tsum_nat_add (e + 1)).symm
            rw [Finset.sum_range_succ, ← hS_eq] at this; exact this
          have hq_err : |α - (q (2 * e + 4) : ℝ)| < (1 / 4 : ℝ) * (1 / 3 : ℝ) ^ (e + 1) := by
            refine (hc (2 * e + 4)).trans_le ?_
            have h34 : (3 : ℝ) ^ (e + 1) ≤ (4 : ℝ) ^ (e + 1) :=
              pow_le_pow_left₀ (by norm_num) (by norm_num) _
            have hpow : (2 : ℝ) ^ (-((2 * e + 4 : ℕ) : ℤ)) =
                (1 / 4 : ℝ) * ((4 : ℝ) ^ (e + 1))⁻¹ := by
              rw [zpow_neg, zpow_natCast, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
                show 2 * e + 4 = 2 + 2 * (e + 1) by omega, pow_add, mul_inv]
              norm_num
            rw [hpow, show (1 / 3 : ℝ) ^ (e + 1) = ((3 : ℝ) ^ (e + 1))⁻¹ by
              rw [one_div, inv_pow]]
            exact mul_le_mul_of_nonneg_left
              (inv_anti₀ (by positivity) h34) (by norm_num)
          have htail_nn : 0 ≤ ∑' k : ℕ, term (k + (e + 1)) :=
            tsum_nonneg fun k ↦ by dsimp [term]; split_ifs <;> positivity
          have htail := htail_bd e
          have he := abs_lt.mp hq_err
          have hgoal_r : ((3 / 4 : ℚ) * (1 / 3 : ℚ) ^ (e + 1) ≤ q (2 * e + 4) - Sprev) ↔
              (3 / 4 : ℝ) * (1 / 3 : ℝ) ^ (e + 1) ≤ (q (2 * e + 4) : ℝ) - (Sprev : ℝ) := by
            rw [← Rat.cast_le (K := ℝ)]; push_cast; rfl
          rw [hgoal_r]
          constructor
          · intro hge
            by_contra hnd
            have ht0 : term e = 0 := by simp [term, hnd]
            linarith [hsplit, ht0, htail, he.1]
          · intro hd
            have ht1 : term e = (1 / 3 : ℝ) ^ (e + 1) := by simp [term, hd]
            linarith [hsplit, ht1, htail_nn, he.2]
    have hdec : ComputablePred fun c : Nat.Partrec.Code ↦ (Nat.Partrec.Code.eval c 0).Dom := by
      let decFn : Nat.Partrec.Code → Bool := fun c ↦
        (acc (Encodable.encode c + 1)).getD (Encodable.encode c) false
      have hdecFn : Computable decFn :=
        (Primrec.list_getD false).to_comp.comp
          (hacc.comp (Computable.succ.comp Computable.encode)) Computable.encode
      refine ⟨Classical.decPred _, hdecFn.of_eq fun c ↦ Bool.eq_iff_iff.mpr ?_⟩
      have h := hacc_spec (Encodable.encode c + 1) (Encodable.encode c) (Nat.lt_succ_self _)
      simpa [decFn, Denumerable.ofNat_encode] using h
    exact ComputablePred.halting_problem 0 hdec
  exact ⟨α, hα_pos, hα_sigma, hα_not_delta⟩

/-- Strict inclusion `Δ₁ ⊂neq Σ₁`. -/
theorem delta1_ssubset_sigma1 : Delta1 ⊂ Sigma1 := by
  refine ssubset_iff_subset_ne.mpr ⟨delta1_subset_sigma1, fun heq ↦ ?_⟩
  obtain ⟨α, _, hσ, hδ⟩ := exists_pos_mem_sigma1_not_mem_delta1
  exact hδ (heq ▸ hσ)

/-- Strict inclusion `Δ₁ ⊂neq Π₁`. -/
theorem delta1_ssubset_pi1 : Delta1 ⊂ Pi1 := by
  refine ssubset_iff_subset_ne.mpr ⟨delta1_subset_pi1, fun heq ↦ ?_⟩
  obtain ⟨α, _, hσ, hδ⟩ := exists_pos_mem_sigma1_not_mem_delta1
  have hπ : -α ∈ Pi1 := mem_pi1_iff_neg_mem_sigma1.mpr (by simpa using hσ)
  have hnδ : -α ∉ Delta1 := fun h ↦ hδ (by simpa using h.neg)
  exact hnδ (heq ▸ hπ)

private lemma exists_code_left_cut_of_mem_sigma1 {y : ℝ} (hy : y ∈ Sigma1) :
    ∃ e : ℕ, ∀ q : ℚ,
      ((q : ℝ) < y ↔ ∃ s : ℕ, haltsBy s e (ratEncode q) = true) := by
  obtain ⟨r, hr, hmono, hlim⟩ := mem_sigma1_iff_exists_monotone_rat.mp hy
  have hcut : ∀ q : ℚ, (q : ℝ) < y ↔ ∃ n : ℕ, q < r n := fun q ↦ by
    constructor
    · intro hlt
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (y - (q : ℝ)) (sub_pos.mpr hlt)
      refine ⟨N, ?_⟩
      have h1 := abs_lt.mp (by simpa [Real.dist_eq] using hN N le_rfl)
      have hqr : (q : ℝ) < (r N : ℝ) := by linarith [h1.1]
      exact_mod_cast hqr
    · rintro ⟨n, hlt⟩
      have hr_le : (r n : ℝ) ≤ y :=
        ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨n, fun m hm ↦ Rat.cast_le.mpr (hmono hm)⟩)
      exact (Rat.cast_lt.mpr hlt).trans_le hr_le
  have hpart : Nat.Partrec fun m : ℕ ↦
      Nat.rfind fun n ↦ Part.some (decide (ratOfNat m < r n)) :=
    Partrec.nat_iff.mp <| Partrec.rfind
      (((isComputableRatMap_ratOfNat.comp .fst).decide_lt (hr.comp .snd)).to₂.partrec₂)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨Encodable.encode c, fun q ↦ ?_⟩
  have hca := congrFun hc (ratEncode q)
  rw [exists_haltsBy_iff, Denumerable.ofNat_encode, hca, hcut q]
  refine Iff.symm (Nat.rfind_dom.trans ?_)
  simp [ratOfNat_ratEncode, eq_comm (a := true)]

private def zwPrefixRat (k : ℕ) (prev : List ℕ) : ℚ :=
  ∑ j ∈ Finset.range k, (prev.getD j 0 : ℚ) * (1 / 8 : ℚ) ^ (j + 1)

private def zwThreshRat (k : ℕ) (prev : List ℕ) : ℚ :=
  zwPrefixRat k prev + (3 / 2 : ℚ) * (1 / 8 : ℚ) ^ (k + 1)

private def zwStepDigit (k s : ℕ) (prev : List ℕ) : ℕ :=
  let fired := haltsBy s (k / 2) (ratEncode (zwThreshRat k prev))
  if k % 2 = 0 then (if fired = true then 0 else 2) else (if fired = true then 2 else 0)

private def zwDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, s =>
      let prev := zwDigits k s
      prev ++ [zwStepDigit k s prev]

private lemma zwDigits_length (k s : ℕ) : (zwDigits k s).length = k := by
  induction k with
  | zero => rfl
  | succ m ih => dsimp [zwDigits]; rw [List.length_append, ih]; simp

private lemma zwDigits_getD_eq {j k s : ℕ} (hj : j < k) :
    (zwDigits k s).getD j 0 = zwStepDigit j s (zwDigits j s) := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
    · dsimp [zwDigits]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rwa [zwDigits_length]),
        ← List.getD_eq_getElem?_getD]
      exact ih hlt
    · dsimp only [zwDigits]
      have hget : ∀ (l : List ℕ) (a : ℕ), (l ++ [a]).getD l.length 0 = a := fun l a ↦ by
        simp [List.getD_eq_getElem?_getD]
      simpa only [zwDigits_length j s] using
        hget (zwDigits j s) (zwStepDigit j s (zwDigits j s))

private lemma zwStepDigit_le_two (k s : ℕ) (prev : List ℕ) : zwStepDigit k s prev ≤ 2 := by
  dsimp [zwStepDigit]; split_ifs <;> omega

private lemma card_changes_zwDigits_le (k S : ℕ) :
    ((Finset.range S).filter fun s ↦ zwDigits k (s + 1) ≠ zwDigits k s).card ≤ 3 ^ k - 1 := by
  induction k with
  | zero => simp [zwDigits]
  | succ m ih =>
    let A := (Finset.range S).filter fun s ↦ zwDigits m (s + 1) ≠ zwDigits m s
    let B := (Finset.range S).filter fun s ↦
      zwDigits m (s + 1) = zwDigits m s ∧
        zwStepDigit m (s + 1) (zwDigits m (s + 1)) ≠ zwStepDigit m s (zwDigits m s)
    let C := (Finset.range S).filter fun s ↦ zwDigits (m + 1) (s + 1) ≠ zwDigits (m + 1) s
    have hsub : C ⊆ A ∪ B := fun s hs ↦ by
      simp only [C, A, B, Finset.mem_filter, Finset.mem_union] at hs ⊢
      by_cases heq : zwDigits m (s + 1) = zwDigits m s
      · right; refine ⟨hs.1, heq, fun hd ↦ hs.2 ?_⟩
        dsimp only [zwDigits]; rw [← hd, heq]
      · left; exact ⟨hs.1, heq⟩
    -- Between any two distinct `s₁ < s₂` in `B`, there must lie some `t ∈ A` with `s₁ < t < s₂`.
    have hbetween : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ < s₂ → ∃ t ∈ A, s₁ < t ∧ t < s₂ := by
      intro s₁ hs₁ s₂ hs₂ hlt
      by_contra hno; push Not at hno
      have hs₁' := (Finset.mem_filter.mp hs₁).2
      have hs₂' := (Finset.mem_filter.mp hs₂).2
      have hs₂_lt : s₂ < S := Finset.mem_range.mp (Finset.mem_filter.mp hs₂).1
      have hconst : ∀ u, s₁ ≤ u → u ≤ s₂ + 1 → zwDigits m u = zwDigits m s₁ := by
        intro u hu1 hu2
        induction u with
        | zero =>
          have : s₁ = 0 := by omega
          subst this; rfl
        | succ v ihv =>
          rcases eq_or_lt_of_le hu1 with heq | hltv
          · rw [← heq]
          · have hv1 : s₁ ≤ v := by omega
            have hv_prev := ihv hv1 (by omega)
            rcases eq_or_lt_of_le hv1 with rfl | hgt
            · exact hs₁'.1
            · rcases eq_or_lt_of_le (show v ≤ s₂ by omega) with rfl | hlt2
              · exact hs₂'.1.trans hv_prev
              · have hv_notA : v ∉ A := fun hvA ↦ (hno v hvA hgt).not_gt hlt2
                have hveq : zwDigits m (v + 1) = zwDigits m v := by
                  by_contra hne
                  exact hv_notA (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne⟩)
                exact hveq.trans hv_prev
      set P := zwDigits m s₁
      have hP1 : zwDigits m (s₁ + 1) = P := hconst (s₁ + 1) (by omega) (by omega)
      have hP2 : zwDigits m s₂ = P := hconst s₂ (by omega) (by omega)
      have hP2' : zwDigits m (s₂ + 1) = P := hconst (s₂ + 1) (by omega) (by omega)
      set x := ratEncode (zwThreshRat m P)
      have hchange1 : haltsBy (s₁ + 1) (m / 2) x ≠ haltsBy s₁ (m / 2) x := by
        intro heq; apply hs₁'.2; rw [hP1]; dsimp [zwStepDigit]; rw [heq]
      have hchange2 : haltsBy (s₂ + 1) (m / 2) x ≠ haltsBy s₂ (m / 2) x := by
        intro heq; apply hs₂'.2; rw [hP2, hP2']; dsimp [zwStepDigit]; rw [heq]
      have hf1 : haltsBy (s₁ + 1) (m / 2) x = true := by
        cases h0 : haltsBy s₁ (m / 2) x
        · cases h1 : haltsBy (s₁ + 1) (m / 2) x
          · exact absurd (h1.trans h0.symm) hchange1
          · rfl
        · exact haltsBy_mono (Nat.le_succ s₁) h0
      have hf2 : haltsBy s₂ (m / 2) x = true := haltsBy_mono (by omega) hf1
      have hf2' : haltsBy (s₂ + 1) (m / 2) x = true := haltsBy_mono (Nat.le_succ s₂) hf2
      exact hchange2 (hf2'.trans hf2.symm)
    have hB_le : B.card ≤ A.card + 1 := by
      classical
      by_cases hBne : B.Nonempty
      · set bmax := B.max' hBne
        let B' := B.erase bmax
        have hBcard : B.card = B'.card + 1 :=
          (Finset.card_erase_add_one (Finset.max'_mem B hBne)).symm
        rw [hBcard, add_le_add_iff_right]
        have hex_next : ∀ b ∈ B', ∃ t ∈ A, b < t ∧ ∀ b2 ∈ B, b < b2 → t < b2 := by
          intro b hb
          have hb_mem : b ∈ B := Finset.mem_of_mem_erase hb
          have hb_lt : b < bmax := lt_of_le_of_ne (Finset.le_max' B b hb_mem)
            (Finset.ne_of_mem_erase hb)
          let upper := B.filter (b < ·)
          have hup_ne : upper.Nonempty :=
            ⟨bmax, Finset.mem_filter.mpr ⟨Finset.max'_mem B hBne, hb_lt⟩⟩
          let bnext := upper.min' hup_ne
          have hbn_mem := Finset.mem_filter.mp (Finset.min'_mem upper hup_ne)
          obtain ⟨t, htA, hbt, htn⟩ := hbetween b hb_mem bnext hbn_mem.1 hbn_mem.2
          exact ⟨t, htA, hbt, fun b2 hb2 hbb2 ↦
            htn.trans_le (Finset.min'_le upper b2 (Finset.mem_filter.mpr ⟨hb2, hbb2⟩))⟩
        let pick : ℕ → ℕ := fun b ↦
          if hb : b ∈ B' then Classical.choose (hex_next b hb) else 0
        refine Finset.card_le_card_of_injOn pick (fun b hb ↦ ?_) (fun b₁ hb₁ b₂ hb₂ heq ↦ ?_)
        · have hp : pick b = Classical.choose (hex_next b hb) :=
            dite_eq_left_of_eq_true (eq_true hb)
          rw [hp]; exact (Classical.choose_spec (hex_next b hb)).1
        · have hp1 : pick b₁ = Classical.choose (hex_next b₁ hb₁) :=
            dite_eq_left_of_eq_true (eq_true hb₁)
          have hp2 : pick b₂ = Classical.choose (hex_next b₂ hb₂) :=
            dite_eq_left_of_eq_true (eq_true hb₂)
          rw [hp1, hp2] at heq
          have h1 := (Classical.choose_spec (hex_next b₁ hb₁)).2
          have h2 := (Classical.choose_spec (hex_next b₂ hb₂)).2
          rcases lt_trichotomy b₁ b₂ with hlt | rfl | hgt
          · have := h1.2 b₂ (Finset.mem_of_mem_erase hb₂) hlt
            have := h2.1; omega
          · rfl
          · have := h2.2 b₁ (Finset.mem_of_mem_erase hb₁) hgt
            have := h1.1; omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hBne, Finset.card_empty]; exact Nat.zero_le _
    have hC_le : C.card ≤ A.card + B.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
    have hpow : 1 ≤ 3 ^ m := Nat.one_le_pow m 3 (by norm_num)
    have h3 : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ]; ring
    change C.card ≤ 3 ^ (m + 1) - 1
    have hA : A.card ≤ 3 ^ m - 1 := ih
    omega

private lemma eventually_const_zwDigits (k : ℕ) :
    ∃ L : List ℕ, ∃ S : ℕ, ∀ s ≥ S, zwDigits k s = L := by
  by_contra hno; push Not at hno
  -- Build a strictly increasing sequence of `3 ^ k` change points, contradicting the bound.
  have hnext : ∀ s : ℕ, ∃ t ≥ s, zwDigits k (t + 1) ≠ zwDigits k t := fun s ↦ by
    by_contra hall; push Not at hall
    have hconst : ∀ u ≥ s, zwDigits k u = zwDigits k s := fun u hu ↦ by
      induction u, hu using Nat.le_induction with
      | base => rfl
      | succ v hv ih => exact (hall v hv).trans ih
    obtain ⟨u, hu, hne⟩ := hno (zwDigits k s) s
    exact hne (hconst u hu)
  choose nxt hnxt using hnext
  let seq : ℕ → ℕ := fun i ↦ Nat.rec 0 (fun _ prev ↦ nxt (prev + 1)) i
  have hseq_mono : StrictMono seq := strictMono_nat_of_lt_succ fun i ↦ by
    dsimp [seq]; exact Nat.lt_of_succ_le (hnxt _).1
  have hseq_chg : ∀ i, zwDigits k (seq (i + 1) + 1) ≠ zwDigits k (seq (i + 1)) := fun i ↦
    (hnxt _).2
  let M := 3 ^ k
  let S := seq M + 1
  let img := (Finset.range M).image fun i ↦ seq (i + 1)
  have himg_sub : img ⊆ (Finset.range S).filter (fun s ↦ zwDigits k (s + 1) ≠ zwDigits k s) := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hseq_chg i⟩
    have : i + 1 ≤ M := Finset.mem_range.mp hi
    exact Nat.lt_succ_of_le (hseq_mono.monotone this)
  have hcard : img.card = M :=
    (Finset.card_image_of_injective (Finset.range M) fun _ _ h ↦
      Nat.succ.inj (hseq_mono.injective h)).trans (Finset.card_range M)
  have hle := (Finset.card_le_card himg_sub).trans (card_changes_zwDigits_le k S)
  rw [hcard] at hle
  have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
  dsimp [M] at hle; omega

/-- Ambos-Spies–Weihrauch–Zheng separation: there exists a weakly computable real number
`α ∈ C₂` that is neither left-computable nor right-computable (`α ∉ Σ₁ ∪ Π₁`). -/
theorem exists_mem_weaklyComputable_not_mem_semiComputable :
    ∃ α : ℝ, α ∈ WeaklyComputable ∧ α ∉ SemiComputable := by
  have hpre : IsComputableRatMap₂ zwPrefixRat :=
    (IsComputableRatMap.sum_range .fst
      ((IsComputableRatMap.ofNat
        ((Primrec.list_getD 0).to_comp.comp (Computable.snd.comp .fst) .snd)).mul
        ((IsComputableRatMap.const (1 / 8)).pow (Computable.succ.comp .snd))).to₂).to₂
  have hthresh : IsComputableRatMap₂ zwThreshRat :=
    (hpre.add ((IsComputableRatMap.const (3 / 2)).mul
      ((IsComputableRatMap.const (1 / 8)).pow (Computable.succ.comp .fst)))).to₂
  have hstepD : Computable fun p : (ℕ × ℕ) × List ℕ ↦ zwStepDigit p.1.1 p.1.2 p.2 := by
    have hk : Computable fun p : (ℕ × ℕ) × List ℕ ↦ p.1.1 := Computable.fst.comp .fst
    have hs : Computable fun p : (ℕ × ℕ) × List ℕ ↦ p.1.2 := Computable.snd.comp .fst
    have hfired : Computable fun p : (ℕ × ℕ) × List ℕ ↦
        haltsBy p.1.2 (p.1.1 / 2) (ratEncode (zwThreshRat p.1.1 p.2)) :=
      primrec_haltsBy.to_comp.comp
        (.pair (.pair hs (Primrec.nat_div.to_comp.comp hk (.const 2)))
          (hthresh.comp hk .snd).ratEncode)
    exact (Computable.cond
      (Primrec.beq.to_comp.comp (Primrec.nat_mod.to_comp.comp hk (.const 2)) (.const 0))
      (Computable.cond hfired (.const 0) (.const 2))
      (Computable.cond hfired (.const 2) (.const 0))).of_eq fun p ↦ by
      dsimp only [zwStepDigit]
      cases h2 : haltsBy p.1.2 (p.1.1 / 2) (ratEncode (zwThreshRat p.1.1 p.2)) <;>
        by_cases h1 : p.1.1 % 2 = 0 <;> simp [h1]
  have hdigits : Computable₂ zwDigits :=
    (Computable.nat_rec .fst (.const [])
      (Computable.list_concat.comp (Computable.snd.comp .snd)
        (hstepD.comp (.pair (.pair (Computable.fst.comp .snd) (Computable.snd.comp .fst))
          (Computable.snd.comp .snd)))).to₂).of_eq
      fun ⟨k, s⟩ ↦ by
        induction k with
        | zero => rfl
        | succ m ih => dsimp only [zwDigits] at ih ⊢; rw [ih]
  let d : ℕ → ℕ → ℕ := fun k s ↦ zwStepDigit k s (zwDigits k s)
  let xRat : ℕ → ℚ := fun s ↦ zwPrefixRat s (zwDigits s s)
  have hxRat : IsComputableRatSeq xRat := hpre.comp .id (hdigits.comp .id .id)
  have hxRat_eq : ∀ s : ℕ, (xRat s : ℝ) =
      ∑ k ∈ Finset.range s, (d k s : ℝ) * (1 / 8 : ℝ) ^ (k + 1) := fun s ↦ by
    dsimp [xRat, zwPrefixRat]; rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    push_cast; rw [zwDigits_getD_eq (Finset.mem_range.mp hk)]
  -- Bound the total variation `∑_{s < S} |xRat (s + 1) - xRat s| ≤ 2`.
  have hvar_bd : ∀ S : ℕ, ∑ s ∈ Finset.range S, |(xRat (s + 1) : ℝ) - (xRat s : ℝ)| ≤ 2 := by
    intro S
    have hstep_bd : ∀ s < S, |(xRat (s + 1) : ℝ) - (xRat s : ℝ)| ≤
        2 * (1 / 8 : ℝ) ^ (s + 1) + ∑ k ∈ Finset.range S,
          (if d k (s + 1) ≠ d k s then (2 : ℝ) else 0) * (1 / 8 : ℝ) ^ (k + 1) := by
      intro s hsS
      rw [hxRat_eq (s + 1), hxRat_eq s, Finset.sum_range_succ, add_comm _ ((d s (s + 1) : ℝ) * _),
        add_sub_assoc, ← Finset.sum_sub_distrib]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · have hp8 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (s + 1) := by positivity
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hp8]
        exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (zwStepDigit_le_two s (s + 1) (zwDigits s (s + 1)))) hp8
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum (g := fun k ↦
            (if d k (s + 1) ≠ d k s then (2 : ℝ) else 0) * (1 / 8 : ℝ) ^ (k + 1))
          fun k _ ↦ ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsS.le) fun k _ _ ↦ by
            split_ifs <;> positivity)
        have hp8k : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (k + 1) := by positivity
        rw [← sub_mul, abs_mul, abs_of_nonneg hp8k]
        refine mul_le_mul_of_nonneg_right ?_ hp8k
        by_cases hne : d k (s + 1) ≠ d k s
        · rw [ite_eq_left hne, abs_le]
          have h1 : (d k (s + 1) : ℝ) ≤ 2 := by exact_mod_cast zwStepDigit_le_two k (s + 1) _
          have h2 : (d k s : ℝ) ≤ 2 := by exact_mod_cast zwStepDigit_le_two k s _
          exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) (d k (s + 1))],
            by linarith [Nat.cast_nonneg (α := ℝ) (d k s)]⟩
        · push Not at hne; simp [hne]
    have hsum1 : ∑ s ∈ Finset.range S, 2 * (1 / 8 : ℝ) ^ (s + 1) ≤ 2 / 7 := by
      have hts : HasSum (fun s : ℕ ↦ 2 * (1 / 8 : ℝ) ^ (s + 1)) (2 / 7 : ℝ) := by
        have h := ((hasSum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by positivity)
          (by norm_num)).mul_left (2 * (1 / 8 : ℝ))).congr_fun
          (g := fun s : ℕ ↦ 2 * (1 / 8 : ℝ) ^ (s + 1)) fun s ↦ by rw [pow_succ]; ring
        norm_num at h; exact h
      exact (hts.summable.sum_le_tsum _ fun _ _ ↦ by positivity).trans_eq hts.tsum_eq
    have hd_chg : ∀ k : ℕ,
        ((Finset.range S).filter fun s ↦ d k (s + 1) ≠ d k s).card ≤ 3 ^ (k + 1) := fun k ↦ by
      refine (Finset.card_le_card (t := (Finset.range S).filter
        fun s ↦ zwDigits (k + 1) (s + 1) ≠ zwDigits (k + 1) s) fun s hs ↦ ?_).trans
        ((card_changes_zwDigits_le (k + 1) S).trans (Nat.sub_le _ _))
      simp only [Finset.mem_filter] at hs ⊢
      refine ⟨hs.1, fun heq ↦ hs.2 ?_⟩
      have := congrArg (fun l ↦ l.getD k 0) heq
      rwa [zwDigits_getD_eq (Nat.lt_succ_self k), zwDigits_getD_eq (Nat.lt_succ_self k)] at this
    have hsum2 : ∑ k ∈ Finset.range S,
        ∑ s ∈ Finset.range S, (if d k (s + 1) ≠ d k s then (2 : ℝ) else 0) *
          (1 / 8 : ℝ) ^ (k + 1) ≤ 6 / 5 := by
      have hts : HasSum (fun k : ℕ ↦ (2 : ℝ) * (3 / 8 : ℝ) ^ (k + 1)) (6 / 5 : ℝ) := by
        have h := ((hasSum_geometric_of_lt_one (r := (3 / 8 : ℝ)) (by positivity)
          (by norm_num)).mul_left (2 * (3 / 8 : ℝ))).congr_fun
          (g := fun k : ℕ ↦ (2 : ℝ) * (3 / 8 : ℝ) ^ (k + 1)) fun k ↦ by rw [pow_succ]; ring
        norm_num at h; exact h
      refine (Finset.sum_le_sum (g := fun k ↦ (2 : ℝ) * (3 / 8 : ℝ) ^ (k + 1)) fun k _ ↦ ?_).trans
        ((hts.summable.sum_le_tsum _ fun _ _ ↦ by positivity).trans_eq hts.tsum_eq)
      rw [← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul]
      calc (((Finset.range S).filter fun s ↦ d k (s + 1) ≠ d k s).card : ℝ) * 2 *
              (1 / 8 : ℝ) ^ (k + 1)
          ≤ ((3 ^ (k + 1) : ℕ) : ℝ) * 2 * (1 / 8 : ℝ) ^ (k + 1) := by
            gcongr; exact_mod_cast hd_chg k
        _ = 2 * (3 / 8 : ℝ) ^ (k + 1) := by
            push_cast; rw [mul_comm _ (2 : ℝ), mul_assoc, ← mul_pow]; norm_num
    calc ∑ s ∈ Finset.range S, |(xRat (s + 1) : ℝ) - (xRat s : ℝ)|
        ≤ ∑ s ∈ Finset.range S, (2 * (1 / 8 : ℝ) ^ (s + 1) +
            ∑ k ∈ Finset.range S, (if d k (s + 1) ≠ d k s then (2 : ℝ) else 0) *
              (1 / 8 : ℝ) ^ (k + 1)) :=
          Finset.sum_le_sum fun s hs ↦ hstep_bd s (Finset.mem_range.mp hs)
      _ = (∑ s ∈ Finset.range S, 2 * (1 / 8 : ℝ) ^ (s + 1)) +
            ∑ k ∈ Finset.range S, ∑ s ∈ Finset.range S,
              (if d k (s + 1) ≠ d k s then (2 : ℝ) else 0) * (1 / 8 : ℝ) ^ (k + 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ 2 / 7 + 6 / 5 := add_le_add hsum1 hsum2
      _ ≤ 2 := by norm_num
  have hsum_diff : Summable fun s : ℕ ↦ |(xRat (s + 1) : ℝ) - (xRat s : ℝ)| :=
    summable_of_sum_range_le (fun _ ↦ abs_nonneg _) hvar_bd
  -- Limiting digits `dLim k ∈ {0, 2}` and limiting real `α = ∑' k, dLim k * (1/8)^(k+1)`.
  have hd_stab : ∀ k : ℕ, ∃ S : ℕ, ∀ s ≥ S,
      zwDigits (k + 1) s = zwDigits (k + 1) S ∧ d k s = d k S := fun k ↦ by
    obtain ⟨L, S, hS⟩ := eventually_const_zwDigits (k + 1)
    refine ⟨S, fun s hs ↦ ⟨(hS s hs).trans (hS S le_rfl).symm, ?_⟩⟩
    have := congrArg (fun l ↦ l.getD k 0) ((hS s hs).trans (hS S le_rfl).symm)
    rwa [zwDigits_getD_eq (Nat.lt_succ_self k), zwDigits_getD_eq (Nat.lt_succ_self k)] at this
  choose Sstab hSstab using hd_stab
  let dLim : ℕ → ℕ := fun k ↦ d k (Sstab k)
  have hdLim_eq : ∀ k s, Sstab k ≤ s → d k s = dLim k := fun k s hs ↦ (hSstab k s hs).2
  have hdLim_le : ∀ k, dLim k ≤ 2 := fun k ↦ zwStepDigit_le_two k _ _
  have hgeo8 : Summable fun k : ℕ ↦ (2 : ℝ) * (1 / 8 : ℝ) ^ (k + 1) :=
    ((summable_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by positivity)
      (by norm_num)).mul_left (2 * (1 / 8 : ℝ))).congr fun k ↦ by rw [pow_succ]; ring
  have hα_sum : Summable fun k : ℕ ↦ (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun k ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast hdLim_le k) (by positivity)) hgeo8
  set α : ℝ := ∑' k : ℕ, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1)
  have htail8 : ∀ k : ℕ, ∑' j : ℕ, (2 : ℝ) * (1 / 8 : ℝ) ^ (j + k + 1) =
      (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ k := fun k ↦ by
    have hts : HasSum (fun j : ℕ ↦ (2 : ℝ) * (1 / 8 : ℝ) ^ (k + 1) * (1 / 8 : ℝ) ^ j)
        ((2 / 7 : ℝ) * (1 / 8 : ℝ) ^ k) := by
      have h := (hasSum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by positivity)
        (by norm_num)).mul_left ((2 : ℝ) * (1 / 8 : ℝ) ^ (k + 1))
      rwa [show (2 : ℝ) * (1 / 8 : ℝ) ^ (k + 1) * (1 - (1 / 8 : ℝ))⁻¹ =
        (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ k by rw [pow_succ]; ring] at h
    exact (hts.congr_fun fun j ↦ by
      rw [mul_assoc, ← pow_add, show k + 1 + j = j + k + 1 by omega]).tsum_eq
  have hxRat_lim : Filter.Tendsto (fun s ↦ (xRat s : ℝ)) Filter.atTop (nhds α) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h0 : Filter.Tendsto (fun N : ℕ ↦ (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ N)
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by positivity : (0 : ℝ) ≤ 1 / 8) (by norm_num)).const_mul (2 / 7 : ℝ)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h0 (ε / 2) (half_pos hε)
    let S := max N ((Finset.range N).sup Sstab)
    refine ⟨S, fun s hs ↦ ?_⟩
    have hNs : N ≤ s := (le_max_left _ _).trans hs
    have hpre_eq : ∀ k ∈ Finset.range N, d k s = dLim k := fun k hk ↦
      hdLim_eq k s ((Finset.le_sup hk).trans ((le_max_right _ _).trans hs))
    have hα_split : α - ∑ k ∈ Finset.range N, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1) =
        ∑' j : ℕ, (dLim (j + N) : ℝ) * (1 / 8 : ℝ) ^ (j + N + 1) :=
      (eq_sub_of_add_eq' (hα_sum.sum_add_tsum_nat_add N)).symm
    have hN_lt : (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ N < ε / 2 := by
      have h1 := hN N le_rfl
      have hpos : (0 : ℝ) < (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ N := by positivity
      rwa [Real.dist_eq, sub_zero, abs_of_pos hpos] at h1
    have hα_tail : |α - ∑ k ∈ Finset.range N, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1)| < ε / 2 := by
      rw [hα_split, abs_of_nonneg (tsum_nonneg fun _ ↦ by positivity)]
      have hsub := (summable_nat_add_iff N).mpr hα_sum
      have hsub8 := (summable_nat_add_iff N).mpr hgeo8
      exact ((hsub.tsum_le_tsum (fun j ↦ mul_le_mul_of_nonneg_right
        (by exact_mod_cast hdLim_le (j + N)) (by positivity))
        hsub8).trans_eq (htail8 N)).trans_lt hN_lt
    have hx_tail : |(xRat s : ℝ) - ∑ k ∈ Finset.range N, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1)| <
        ε / 2 := by
      rw [hxRat_eq s]
      have hsplit_s : ∑ k ∈ Finset.range s, (d k s : ℝ) * (1 / 8 : ℝ) ^ (k + 1) =
          (∑ k ∈ Finset.range N, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1)) +
            ∑ j ∈ Finset.range (s - N), (d (j + N) s : ℝ) * (1 / 8 : ℝ) ^ (j + N + 1) := by
        have hs_eq : Finset.range s = Finset.range (N + (s - N)) :=
          congrArg Finset.range (by omega)
        rw [hs_eq, Finset.sum_range_add]
        congr 1
        · exact Finset.sum_congr rfl fun k hk ↦ by rw [hpre_eq k hk]
        · exact Finset.sum_congr rfl fun j _ ↦ by rw [add_comm N j]
      rw [hsplit_s, add_sub_cancel_left,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)]
      have hsub8 : Summable fun j : ℕ ↦ (2 : ℝ) * (1 / 8 : ℝ) ^ (j + N + 1) :=
        (summable_nat_add_iff N).mpr hgeo8
      exact ((Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right
        (by exact_mod_cast zwStepDigit_le_two (j + N) s _) (by positivity)).trans
        ((hsub8.sum_le_tsum _ fun _ _ ↦ by positivity).trans_eq (htail8 N))).trans_lt hN_lt
    rw [Real.dist_eq]
    calc |(xRat s : ℝ) - α|
        ≤ |(xRat s : ℝ) - ∑ k ∈ Finset.range N, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1)| +
            |(∑ k ∈ Finset.range N, (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1)) - α| :=
          abs_sub_le _ _ _
      _ < ε := by rw [abs_sub_comm _ α]; linarith
  have hα_c2 : α ∈ WeaklyComputable :=
    mem_weaklyComputable_iff_summable_diff.mpr
      ⟨fun s ↦ (xRat s : ℝ), isComputableRealSeq_rat hxRat,
        hsum_diff, hxRat_lim⟩
  -- Helper establishing the digit bounds at level `k`.
  have hlevel : ∀ k : ℕ, ∃ (s0 : ℕ), (∀ s ≥ s0, zwDigits k s = zwDigits k s0 ∧ d k s = dLim k) ∧
      (zwPrefixRat k (zwDigits k s0) : ℝ) + (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1) ≤ α ∧
      α ≤ (zwPrefixRat k (zwDigits k s0) : ℝ) +
        ((dLim k : ℝ) + 2 / 7) * (1 / 8 : ℝ) ^ (k + 1) := fun k ↦ by
    obtain ⟨L, S0, hS0⟩ := eventually_const_zwDigits k
    let s0 := max S0 ((Finset.range (k + 1)).sup Sstab)
    have hstab : ∀ s ≥ s0, zwDigits k s = zwDigits k s0 ∧ d k s = dLim k := fun s hs ↦
      ⟨(hS0 s ((le_max_left _ _).trans hs)).trans (hS0 s0 (le_max_left _ _)).symm,
        hdLim_eq k s ((Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans
          ((le_max_right _ _).trans hs))⟩
    have hpre_eq : (zwPrefixRat k (zwDigits k s0) : ℝ) =
        ∑ j ∈ Finset.range k, (dLim j : ℝ) * (1 / 8 : ℝ) ^ (j + 1) := by
      dsimp [zwPrefixRat]; rw [Rat.cast_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      push_cast
      have hj' := Finset.mem_range.mp hj
      rw [zwDigits_getD_eq hj']
      have hjs : Sstab j ≤ s0 :=
        (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_lt hj'))).trans (le_max_right _ _)
      change (d j s0 : ℝ) * (1 / 8 : ℝ) ^ (j + 1) = (dLim j : ℝ) * (1 / 8 : ℝ) ^ (j + 1)
      rw [hdLim_eq j s0 hjs]
    have hsplit : α = (zwPrefixRat k (zwDigits k s0) : ℝ) +
        (dLim k : ℝ) * (1 / 8 : ℝ) ^ (k + 1) +
        ∑' j : ℕ, (dLim (j + (k + 1)) : ℝ) * (1 / 8 : ℝ) ^ (j + (k + 1) + 1) := by
      have := (hα_sum.sum_add_tsum_nat_add (k + 1)).symm
      rw [Finset.sum_range_succ, ← hpre_eq] at this; exact this
    have ht_nn : 0 ≤ ∑' j : ℕ, (dLim (j + (k + 1)) : ℝ) * (1 / 8 : ℝ) ^ (j + (k + 1) + 1) :=
      tsum_nonneg fun _ ↦ by positivity
    have ht_hi : ∑' j : ℕ, (dLim (j + (k + 1)) : ℝ) * (1 / 8 : ℝ) ^ (j + (k + 1) + 1) ≤
        (2 / 7 : ℝ) * (1 / 8 : ℝ) ^ (k + 1) :=
      (((summable_nat_add_iff (k + 1)).mpr hα_sum).tsum_le_tsum
        (fun j ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast hdLim_le _) (by positivity))
        ((summable_nat_add_iff (k + 1)).mpr hgeo8)).trans_eq (htail8 (k + 1))
    exact ⟨s0, hstab, by linarith, by linarith⟩
  have hα_not_sigma : α ∉ Sigma1 := fun hσ ↦ by
    obtain ⟨e, he⟩ := exists_code_left_cut_of_mem_sigma1 hσ
    let k := 2 * e
    obtain ⟨s0, hstab, hlo, hhi⟩ := hlevel k
    set q := zwThreshRat k (zwDigits k s0)
    have hq_eq : (q : ℝ) = (zwPrefixRat k (zwDigits k s0) : ℝ) +
        (3 / 2 : ℝ) * (1 / 8 : ℝ) ^ (k + 1) := by dsimp [q, zwThreshRat]; push_cast; rfl
    have hp : (0 : ℝ) < (1 / 8 : ℝ) ^ (k + 1) := by positivity
    by_cases hhalt : ∃ s : ℕ, haltsBy s e (ratEncode q) = true
    · obtain ⟨s, hs⟩ := hhalt
      let s' := max s s0
      have ⟨hL, hd'⟩ := hstab s' (le_max_right _ _)
      have hd0 : dLim k = 0 := by
        rw [← hd']; dsimp [d, zwStepDigit]
        have hk1 : k / 2 = e := by omega
        have hk2 : k % 2 = 0 := by omega
        have hf : haltsBy s' e (ratEncode q) = true := haltsBy_mono (le_max_left _ _) hs
        simp [hL, hk1, hk2, hf, q]
      have hlt : (q : ℝ) < α := (he q).mpr ⟨s, hs⟩
      rw [hd0, Nat.cast_zero] at hhi; nlinarith
    · have hfalse : haltsBy s0 e (ratEncode q) ≠ true := fun h ↦ hhalt ⟨s0, h⟩
      have hd2 : dLim k = 2 := by
        rw [← (hstab s0 le_rfl).2]; dsimp [d, zwStepDigit]
        have hk1 : k / 2 = e := by omega
        have hk2 : k % 2 = 0 := by omega
        simp [hk1, hk2, hfalse, q]
      rw [hd2, Nat.cast_ofNat] at hlo
      have hlt : (q : ℝ) < α := by nlinarith
      exact hhalt ((he q).mp hlt)
  have hα_not_pi : α ∉ Pi1 := fun hπ ↦ by
    obtain ⟨e, he⟩ := exists_code_left_cut_of_mem_sigma1 (mem_pi1_iff_neg_mem_sigma1.mp hπ)
    have hpart : Nat.Partrec fun m : ℕ ↦
        Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e)
          (ratEncode (-ratOfNat m)) :=
      Partrec.nat_iff.mp <|
        Nat.Partrec.Code.eval_part.comp (.const _) isComputableRatMap_ratOfNat.neg.ratEncode
    obtain ⟨c', hc'⟩ := Nat.Partrec.Code.exists_code.mp hpart
    let e' := Encodable.encode c'
    have he' : ∀ q : ℚ, α < (q : ℝ) ↔ ∃ s : ℕ, haltsBy s e' (ratEncode q) = true := by
      intro q
      have hcap := congrFun hc' (ratEncode q)
      rw [exists_haltsBy_iff, Denumerable.ofNat_encode, hcap, ratOfNat_ratEncode,
        ← exists_haltsBy_iff, ← he (-q)]
      push_cast; constructor <;> intro h <;> linarith
    let k := 2 * e' + 1
    obtain ⟨s0, hstab, hlo, hhi⟩ := hlevel k
    set q := zwThreshRat k (zwDigits k s0)
    have hq_eq : (q : ℝ) = (zwPrefixRat k (zwDigits k s0) : ℝ) +
        (3 / 2 : ℝ) * (1 / 8 : ℝ) ^ (k + 1) := by dsimp [q, zwThreshRat]; push_cast; rfl
    have hp : (0 : ℝ) < (1 / 8 : ℝ) ^ (k + 1) := by positivity
    by_cases hhalt : ∃ s : ℕ, haltsBy s e' (ratEncode q) = true
    · obtain ⟨s, hs⟩ := hhalt
      let s' := max s s0
      have ⟨hL, hd'⟩ := hstab s' (le_max_right _ _)
      have hd2 : dLim k = 2 := by
        rw [← hd']; dsimp [d, zwStepDigit]
        have hk1 : k / 2 = e' := by omega
        have hk2 : k % 2 ≠ 0 := by omega
        have hf : haltsBy s' e' (ratEncode q) = true := haltsBy_mono (le_max_left _ _) hs
        simp [hL, hk1, hk2, hf, q]
      have hlt : α < (q : ℝ) := (he' q).mpr ⟨s, hs⟩
      rw [hd2, Nat.cast_ofNat] at hlo; nlinarith
    · have hfalse : haltsBy s0 e' (ratEncode q) ≠ true := fun h ↦ hhalt ⟨s0, h⟩
      have hd0 : dLim k = 0 := by
        rw [← (hstab s0 le_rfl).2]; dsimp [d, zwStepDigit]
        have hk1 : k / 2 = e' := by omega
        have hk2 : k % 2 ≠ 0 := by omega
        simp [hk1, hk2, hfalse, q]
      rw [hd0, Nat.cast_zero] at hhi
      have hlt : α < (q : ℝ) := by nlinarith
      exact hhalt ((he' q).mp hlt)
  exact ⟨α, hα_c2, fun h ↦ h.elim hα_not_sigma hα_not_pi⟩

/-- Strict inclusion `C₁ = Σ₁ ∪ Π₁ ⊂neq C₂`. -/
theorem semiComputable_ssubset_weaklyComputable : SemiComputable ⊂ WeaklyComputable := by
  refine ssubset_iff_subset_ne.mpr ⟨semiComputable_subset_weaklyComputable, fun heq ↦ ?_⟩
  obtain ⟨α, hc2, hnc1⟩ := exists_mem_weaklyComputable_not_mem_semiComputable
  exact hnc1 (heq.symm ▸ hc2)

/-- Strict inclusion `Δ₁ ⊂neq C₂`. -/
theorem delta1_ssubset_weaklyComputable : Delta1 ⊂ WeaklyComputable :=
  delta1_ssubset_sigma1.trans_subset sigma1_subset_weaklyComputable

/-- Existence of a weakly computable real number that is not computable (`α ∈ C₂ \ Δ₁`). -/
theorem exists_mem_weaklyComputable_not_mem_delta1 :
    ∃ α : ℝ, α ∈ WeaklyComputable ∧ α ∉ Delta1 := by
  obtain ⟨α, hc2, hnc1⟩ := exists_mem_weaklyComputable_not_mem_semiComputable
  exact ⟨α, hc2, fun hδ ↦ hnc1 (Or.inl (delta1_subset_sigma1 hδ))⟩

end FirstLevelSeparations


end ZhengWeihrauch

end CslibFrontier.ComputableAnalysis
