module

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prékopa–Leindler Inequality and 1D Grünbaum Bisection

Self-contained proofs of the one-dimensional Brunn–Minkowski inequality, the one-dimensional and
multivariate Prékopa–Leindler inequalities on `Fin m → ℝ`, and the elementary one-dimensional
Grünbaum mass-bisection bound (`≤ 4/5`) for nonnegative concave profiles.

## Main results

* `CslibFrontier.Analysis.Convex.brunn_minkowski_1d_compact`: one-dimensional Brunn–Minkowski
  inequality for compact nonempty subsets of `ℝ`.
* `CslibFrontier.Analysis.Convex.brunn_minkowski_1d_weighted`: weighted one-dimensional
  Brunn–Minkowski inequality for measurable subsets of `ℝ`.
* `CslibFrontier.Analysis.Convex.prekopa_leindler_one`: one-dimensional Prékopa–Leindler inequality
  for bounded nonnegative measurable functions, proved via layer-cake integration.
* `CslibFrontier.Analysis.Convex.prekopa_leindler_pi`: `m`-dimensional Prékopa–Leindler inequality
  on `Fin m → ℝ` by induction and Fubini's theorem.
* `CslibFrontier.Analysis.Convex.concave_moment_ge_third`: first-moment lower bound for nonnegative
  concave functions on `[0, b]`.
* `CslibFrontier.Analysis.Convex.grunbaum_1d_concave`: `≤ 4/5` mass-bisection inequality for
  nonnegative concave profiles centered at `0`.
-/

public section

open scoped BigOperators ENNReal Pointwise
open MeasureTheory Finset Real

namespace CslibFrontier.Analysis.Convex

/-! ### Self-contained Brunn–Minkowski (1D) and Prékopa–Leindler on `ℝ^m` -/

/-- One-dimensional Brunn–Minkowski inequality for compact nonempty sets `A, B ⊆ ℝ`:
`volume (A + B) ≥ volume A + volume B`. -/
theorem brunn_minkowski_1d_compact {A B : Set ℝ} (hAc : IsCompact A) (hBc : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a₀, ha₀A, ha₀max⟩ := hAc.exists_isMaxOn hAne continuousOn_id
  obtain ⟨b₀, hb₀B, hb₀min⟩ := hBc.exists_isMinOn hBne continuousOn_id
  have h1 : (fun x ↦ x + b₀) '' A ⊆ A + B := by
    rintro _ ⟨a, ha, rfl⟩; exact Set.add_mem_add ha hb₀B
  have h2 : (fun y ↦ a₀ + y) '' B ⊆ A + B := by
    rintro _ ⟨b, hb, rfl⟩; exact Set.add_mem_add ha₀A hb
  have hle1 : (fun x ↦ x + b₀) '' A ⊆ Set.Iic (a₀ + b₀) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ≤ a₀ := ha₀max ha
    change a + b₀ ≤ a₀ + b₀
    linarith
  have hge2 : (fun y ↦ a₀ + y) '' B ⊆ Set.Ici (a₀ + b₀) := by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b₀ ≤ b := hb₀min hb
    change a₀ + b₀ ≤ a₀ + b
    linarith
  have hinter : ((fun x ↦ x + b₀) '' A) ∩ ((fun y ↦ a₀ + y) '' B) ⊆ {a₀ + b₀} := by
    intro z ⟨hz1, hz2⟩
    exact Set.mem_singleton_iff.2 (le_antisymm (hle1 hz1) (hge2 hz2))
  have hnull : volume (((fun x ↦ x + b₀) '' A) ∩ ((fun y ↦ a₀ + y) '' B)) = 0 :=
    measure_mono_null hinter (measure_singleton _)
  have hmeas1 : MeasurableSet ((fun x ↦ x + b₀) '' A) :=
    (hAc.image (continuous_id.add continuous_const)).measurableSet
  have hmeas2 : MeasurableSet ((fun y ↦ a₀ + y) '' B) :=
    (hBc.image (continuous_const.add continuous_id)).measurableSet
  have hunion : volume (((fun x ↦ x + b₀) '' A) ∪ ((fun y ↦ a₀ + y) '' B)) =
      volume ((fun x ↦ x + b₀) '' A) + volume ((fun y ↦ a₀ + y) '' B) := by
    have h := measure_union_add_inter (μ := (volume : Measure ℝ))
      ((fun x ↦ x + b₀) '' A) hmeas2
    rw [hnull, add_zero] at h
    exact h
  have htr1 : volume ((fun x ↦ x + b₀) '' A) = volume A := by
    have heq : (fun x ↦ x + b₀) '' A = (fun x ↦ x + (-b₀)) ⁻¹' A := by
      ext z; simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨a, ha, h⟩ ↦ by rwa [show z + -b₀ = a by linarith],
        fun hz ↦ ⟨z + -b₀, hz, by ring⟩⟩
    rw [heq]; exact measure_preimage_add_right volume (-b₀) A
  have htr2 : volume ((fun y ↦ a₀ + y) '' B) = volume B := by
    have heq : (fun y ↦ a₀ + y) '' B = (fun y ↦ y + (-a₀)) ⁻¹' B := by
      ext z; simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨b, hb, h⟩ ↦ by rwa [show z + -a₀ = b by linarith],
        fun hz ↦ ⟨z + -a₀, hz, by ring⟩⟩
    rw [heq]; exact measure_preimage_add_right volume (-a₀) B
  calc volume A + volume B
      = volume ((fun x ↦ x + b₀) '' A) + volume ((fun y ↦ a₀ + y) '' B) := by rw [htr1, htr2]
    _ = volume (((fun x ↦ x + b₀) '' A) ∪ ((fun y ↦ a₀ + y) '' B)) := hunion.symm
    _ ≤ volume (A + B) := measure_mono (Set.union_subset h1 h2)

/-- One-dimensional weighted Brunn–Minkowski inequality for arbitrary nonempty measurable sets
`A, B ⊆ ℝ` (via inner regularity by compact subsets) and `θ ∈ (0, 1)`. -/
theorem brunn_minkowski_1d_weighted {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hsub : ∀ a ∈ A, ∀ b ∈ B, (1 - θ) * a + θ * b ∈ C) :
    ENNReal.ofReal (1 - θ) * volume A + ENNReal.ofReal θ * volume B ≤ volume C := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  -- Inner regularity: approximate `A` and `B` from inside by compact subsets containing `a₀, b₀`
  have hstep : ∀ (K L : Set ℝ), K ⊆ A → L ⊆ B → IsCompact K → IsCompact L →
      K.Nonempty → L.Nonempty →
      ENNReal.ofReal (1 - θ) * volume K + ENNReal.ofReal θ * volume L ≤ volume C := by
    intro K L hKA hLB hKc hLc hKne hLne
    let K' := (1 - θ) • K
    let L' := θ • L
    have hK'c : IsCompact K' := hKc.image (continuous_const_smul (1 - θ))
    have hL'c : IsCompact L' := hLc.image (continuous_const_smul θ)
    have hK'ne : K'.Nonempty := hKne.image _
    have hL'ne : L'.Nonempty := hLne.image _
    have hsum_sub : K' + L' ⊆ C := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact hsub a (hKA ha) b (hLB hb)
    have hbm := brunn_minkowski_1d_compact hK'c hL'c hK'ne hL'ne
    have hvolK : volume K' = ENNReal.ofReal (1 - θ) * volume K := by
      simp [K', Measure.addHaar_smul_of_nonneg volume h1θ.le]
    have hvolL : volume L' = ENNReal.ofReal θ * volume L := by
      simp [L', Measure.addHaar_smul_of_nonneg volume hθ0.le]
    rw [hvolK, hvolL] at hbm
    exact hbm.trans (measure_mono hsum_sub)
  -- Use `MeasurableSet.measure_eq_iSup_isCompact` over nonempty subtypes of compact subsets
  let SA := {K : Set ℝ // K ⊆ A ∧ IsCompact K}
  let SB := {L : Set ℝ // L ⊆ B ∧ IsCompact L}
  have : Nonempty SA := ⟨⟨{a₀}, Set.singleton_subset_iff.2 ha₀, isCompact_singleton⟩⟩
  have : Nonempty SB := ⟨⟨{b₀}, Set.singleton_subset_iff.2 hb₀, isCompact_singleton⟩⟩
  have hregA : volume A ≤ ⨆ K : SA, volume K.1 := by
    rw [hA.measure_eq_iSup_isCompact volume]
    exact iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hKc ↦
      le_iSup (fun K : SA ↦ volume K.1) ⟨K, hKA, hKc⟩
  have hregB : volume B ≤ ⨆ L : SB, volume L.1 := by
    rw [hB.measure_eq_iSup_isCompact volume]
    exact iSup_le fun L ↦ iSup_le fun hLB ↦ iSup_le fun hLc ↦
      le_iSup (fun L : SB ↦ volume L.1) ⟨L, hLB, hLc⟩
  refine (add_le_add (mul_le_mul' le_rfl hregA) (mul_le_mul' le_rfl hregB)).trans ?_
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup, ENNReal.iSup_add]
  refine iSup_le fun K ↦ ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun L ↦ ?_
  have hK1 : IsCompact (K.1 ∪ {a₀}) := K.2.2.union isCompact_singleton
  have hL1 : IsCompact (L.1 ∪ {b₀}) := L.2.2.union isCompact_singleton
  have hKA1 : K.1 ∪ {a₀} ⊆ A := Set.union_subset K.2.1 (Set.singleton_subset_iff.2 ha₀)
  have hLB1 : L.1 ∪ {b₀} ⊆ B := Set.union_subset L.2.1 (Set.singleton_subset_iff.2 hb₀)
  have hle := hstep (K.1 ∪ {a₀}) (L.1 ∪ {b₀}) hKA1 hLB1 hK1 hL1
    ⟨a₀, Set.mem_union_right _ rfl⟩ ⟨b₀, Set.mem_union_right _ rfl⟩
  exact (add_le_add (mul_le_mul' le_rfl (measure_mono Set.subset_union_left))
    (mul_le_mul' le_rfl (measure_mono Set.subset_union_left))).trans hle

/-- One-dimensional Prékopa–Leindler inequality for bounded nonnegative measurable functions on
`ℝ` with finite integrals (`θ ∈ (0, 1)`). -/
theorem prekopa_leindler_one {f g h : ℝ → ℝ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) (hh0 : ∀ z, 0 ≤ h z)
    (hf_bdd : ∃ M, ∀ x, f x ≤ M) (hg_bdd : ∃ M, ∀ y, g y ≤ M)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume) (hh_int : Integrable h volume)
    (hpl : ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) * x + θ * y)) :
    (∫ x, f x) ^ (1 - θ) * (∫ y, g y) ^ θ ≤ ∫ z, h z := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  have hIf0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hIg0 : 0 ≤ ∫ y, g y := integral_nonneg hg0
  have hIh0 : 0 ≤ ∫ z, h z := integral_nonneg hh0
  rcases hIf0.eq_or_lt with hIf_zero | hIf_pos
  · rw [← hIf_zero, Real.zero_rpow h1θ.ne', zero_mul]; exact hIh0
  rcases hIg0.eq_or_lt with hIg_zero | hIg_pos
  · rw [← hIg_zero, Real.zero_rpow hθ0.ne', mul_zero]; exact hIh0
  -- Essential supremum / supremum normalization: `M_f = sSup (Set.range f) > 0`, `M_g = sSup
  -- (Set.range g) > 0`
  set Mf : ℝ := sSup (Set.range f)
  set Mg : ℝ := sSup (Set.range g)
  have hf_bdd_above : BddAbove (Set.range f) := by
    obtain ⟨M, hM⟩ := hf_bdd; exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
  have hg_bdd_above : BddAbove (Set.range g) := by
    obtain ⟨M, hM⟩ := hg_bdd; exact ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩
  have hMf_pos : 0 < Mf := by
    by_contra hle
    push Not at hle
    have hf_le0 : ∀ x, f x = 0 := fun x ↦
      le_antisymm ((le_csSup hf_bdd_above ⟨x, rfl⟩).trans hle) (hf0 x)
    have : ∫ x, f x = 0 := by simp [hf_le0]
    linarith
  have hMg_pos : 0 < Mg := by
    by_contra hle
    push Not at hle
    have hg_le0 : ∀ y, g y = 0 := fun y ↦
      le_antisymm ((le_csSup hg_bdd_above ⟨y, rfl⟩).trans hle) (hg0 y)
    have : ∫ y, g y = 0 := by simp [hg_le0]
    linarith
  let fn : ℝ → ℝ := fun x ↦ f x / Mf
  let gn : ℝ → ℝ := fun y ↦ g y / Mg
  let hn : ℝ → ℝ := fun z ↦ h z / (Mf ^ (1 - θ) * Mg ^ θ)
  have hfn_le1 : ∀ x, fn x ≤ 1 := fun x ↦
    (div_le_one hMf_pos).2 (le_csSup hf_bdd_above ⟨x, rfl⟩)
  have hgn_le1 : ∀ y, gn y ≤ 1 := fun y ↦
    (div_le_one hMg_pos).2 (le_csSup hg_bdd_above ⟨y, rfl⟩)
  have hpl_n : ∀ x y, fn x ^ (1 - θ) * gn y ^ θ ≤ hn ((1 - θ) * x + θ * y) := by
    intro x y
    dsimp [fn, gn, hn]
    rw [Real.div_rpow (hf0 x) hMf_pos.le, Real.div_rpow (hg0 y) hMg_pos.le, div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hpl x y) (by positivity)
  -- Layer-cake on `(0, 1)` via `ENNReal` lintegral
  have hlc_unit : ∀ {u : ℝ → ℝ}, Measurable u → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) →
      ∫⁻ x, ENNReal.ofReal (u x) = ∫⁻ s in Set.Ioo (0 : ℝ) 1, volume {x | s < u x} := by
    intro u hu_m hu0 hu1
    rw [lintegral_eq_lintegral_meas_lt (μ := (volume : Measure ℝ))
      (ae_of_all _ hu0) hu_m.aemeasurable]
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) := by
      ext s; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
      constructor
      · intro hs; by_cases h1 : s < 1
        · exact Or.inl ⟨hs, h1⟩
        · exact Or.inr (not_lt.1 h1)
      · rintro (⟨h0, _⟩ | h1)
        · exact h0
        · linarith
    have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici (1 : ℝ)) := by
      rw [Set.disjoint_left]; intro s hs1 hs2; exact not_lt.2 hs2 hs1.2
    rw [hsplit, lintegral_union measurableSet_Ici hdisj]
    have hzero : ∫⁻ s in Set.Ici (1 : ℝ), volume {x | s < u x} = 0 := by
      refine (setLIntegral_congr_fun measurableSet_Ici (f := fun _ ↦ (0 : ℝ≥0∞)) ?_).symm.trans
        (by simp)
      intro s hs
      have hempty : {x | s < u x} = ∅ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (hu1 x).trans hs
      dsimp only
      rw [hempty, measure_empty]
    rw [hzero, add_zero]
  have hfn_m : Measurable fn := hf_meas.div_const Mf
  have hgn_m : Measurable gn := hg_meas.div_const Mg
  have hhn_m : Measurable hn := hh_meas.div_const _
  have hfn0 : ∀ x, 0 ≤ fn x := fun x ↦ div_nonneg (hf0 x) hMf_pos.le
  have hgn0 : ∀ y, 0 ≤ gn y := fun y ↦ div_nonneg (hg0 y) hMg_pos.le
  have hhn0 : ∀ z, 0 ≤ hn z := fun z ↦ div_nonneg (hh0 z) (by positivity)
  have hlevel : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - θ) * volume {x | s < fn x} +
        ENNReal.ofReal θ * volume {y | s < gn y} ≤ volume {z | s < hn z} := by
    intro s hs
    have hAne : {x | s < fn x}.Nonempty := by
      have hlt : s * Mf < Mf := by nlinarith [hs.2]
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (Set.range_nonempty f) hlt
      exact ⟨x, (lt_div_iff₀ hMf_pos).2 hx⟩
    have hBne : {y | s < gn y}.Nonempty := by
      have hlt : s * Mg < Mg := by nlinarith [hs.2]
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (Set.range_nonempty g) hlt
      exact ⟨y, (lt_div_iff₀ hMg_pos).2 hy⟩
    refine brunn_minkowski_1d_weighted (measurableSet_lt measurable_const hfn_m)
      (measurableSet_lt measurable_const hgn_m) hAne hBne hθ0 hθ1 fun a ha b hb ↦ ?_
    have hs0 : 0 < s := hs.1
    have h1 : s ^ (1 - θ) < fn a ^ (1 - θ) := Real.rpow_lt_rpow hs0.le ha h1θ
    have h2 : s ^ θ < gn b ^ θ := Real.rpow_lt_rpow hs0.le hb hθ0
    have hprod : s < fn a ^ (1 - θ) * gn b ^ θ := by
      calc s = s ^ (1 - θ + θ) := by rw [sub_add_cancel, Real.rpow_one]
        _ = s ^ (1 - θ) * s ^ θ := Real.rpow_add hs0 _ _
        _ < fn a ^ (1 - θ) * gn b ^ θ := mul_lt_mul'' h1 h2 (by positivity) (by positivity)
    exact lt_of_lt_of_le hprod (hpl_n a b)
  have hlin_enn : ENNReal.ofReal (1 - θ) * (∫⁻ x, ENNReal.ofReal (fn x) ∂volume) +
      ENNReal.ofReal θ * (∫⁻ y, ENNReal.ofReal (gn y) ∂volume) ≤
        ∫⁻ z, ENNReal.ofReal (hn z) ∂volume := by
    have hfn_lc := hlc_unit hfn_m hfn0 hfn_le1
    have hgn_lc := hlc_unit hgn_m hgn0 hgn_le1
    have hhn_lc := lintegral_eq_lintegral_meas_lt (μ := (volume : Measure ℝ))
      (ae_of_all _ hhn0) hhn_m.aemeasurable
    rw [hfn_lc, hgn_lc, hhn_lc]
    have hm_fn : Measurable (fun s : ℝ ↦ volume {x | s < fn x}) :=
      Antitone.measurable fun _ _ hle ↦ measure_mono fun _ hx ↦ lt_of_le_of_lt hle hx
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left'
        (f := fun s : ℝ ↦ ENNReal.ofReal (1 - θ) * volume {x | s < fn x})
        (measurable_const.mul hm_fn).aemeasurable]
    calc ∫⁻ s in Set.Ioo (0 : ℝ) 1, (ENNReal.ofReal (1 - θ) * volume {x | s < fn x} +
            ENNReal.ofReal θ * volume {y | s < gn y})
        ≤ ∫⁻ s in Set.Ioo (0 : ℝ) 1, volume {z | s < hn z} :=
          setLIntegral_mono' measurableSet_Ioo hlevel
      _ ≤ ∫⁻ s in Set.Ioi (0 : ℝ), volume {z | s < hn z} :=
          lintegral_mono_set fun _ hs ↦ hs.1
  have hfn_int : Integrable fn volume := hf_int.div_const Mf
  have hgn_int : Integrable gn volume := hg_int.div_const Mg
  have hhn_int : Integrable hn volume := hh_int.div_const _
  have hfn_eq := ofReal_integral_eq_lintegral_ofReal hfn_int (ae_of_all _ hfn0)
  have hgn_eq := ofReal_integral_eq_lintegral_ofReal hgn_int (ae_of_all _ hgn0)
  have hhn_eq := ofReal_integral_eq_lintegral_ofReal hhn_int (ae_of_all _ hhn0)
  rw [← hfn_eq, ← hgn_eq, ← hhn_eq,
    ← ENNReal.ofReal_mul h1θ.le, ← ENNReal.ofReal_mul hθ0.le,
    ← ENNReal.ofReal_add (mul_nonneg h1θ.le (integral_nonneg hfn0))
      (mul_nonneg hθ0.le (integral_nonneg hgn0)),
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg hhn0)] at hlin_enn
  have hamgm : (∫ x, fn x) ^ (1 - θ) * (∫ y, gn y) ^ θ ≤
      (1 - θ) * (∫ x, fn x) + θ * (∫ y, gn y) :=
    Real.geom_mean_le_arith_mean2_weighted h1θ.le hθ0.le
      (integral_nonneg hfn0) (integral_nonneg hgn0) (sub_add_cancel 1 θ)
  have hcomb := hamgm.trans hlin_enn
  have hIfn : ∫ x, fn x = (∫ x, f x) / Mf := integral_div Mf f
  have hIgn : ∫ y, gn y = (∫ y, g y) / Mg := integral_div Mg g
  have hIhn : ∫ z, hn z = (∫ z, h z) / (Mf ^ (1 - θ) * Mg ^ θ) := integral_div _ h
  rw [hIfn, hIgn, hIhn, Real.div_rpow hIf0 hMf_pos.le, Real.div_rpow hIg0 hMg_pos.le,
    div_mul_div_comm] at hcomb
  exact (div_le_div_iff_of_pos_right (by positivity)).1 hcomb

/-- `m`-dimensional Prékopa–Leindler inequality on `Fin m → ℝ` for bounded nonnegative measurable
functions supported inside `[-R, R]^m` (`R > 0`, `θ ∈ (0, 1)`). -/
theorem prekopa_leindler_pi : ∀ (m : ℕ) {R M θ : ℝ}, 0 < R → 0 ≤ M → 0 < θ → θ < 1 →
    ∀ {f g h : (Fin m → ℝ) → ℝ},
      Measurable f → Measurable g → Measurable h →
      (∀ x, 0 ≤ f x) → (∀ y, 0 ≤ g y) → (∀ z, 0 ≤ h z) →
      (∀ x, f x ≤ M) → (∀ y, g y ≤ M) → (∀ z, h z ≤ M) →
      (∀ x, (∃ i, R < |x i|) → f x = 0) →
      (∀ y, (∃ i, R < |y i|) → g y = 0) →
      (∀ z, (∃ i, R < |z i|) → h z = 0) →
      (∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h ((1 - θ) • x + θ • y)) →
      (∫ x, f x) ^ (1 - θ) * (∫ y, g y) ^ θ ≤ ∫ z, h z
  | 0, _, _, θ, _, _, hθ0, hθ1, f, g, h, _, _, _, _, _, _, _, _, _, _, _, _, hpl => by
    have h0 : ∀ u : (Fin 0 → ℝ) → ℝ, ∫ x, u x = u 0 := fun u ↦ by
      rw [MeasureTheory.integral_unique]
      have hvol_enn : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        change (Measure.pi fun _ : Fin 0 ↦ (volume : Measure ℝ)) Set.univ = 1
        have huniv : (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi fun _ ↦ Set.univ := by ext x; simp
        rw [huniv, Measure.pi_pi]
        simp
      have hvol : volume.real (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
        simp [Measure.real, hvol_enn]
      rw [hvol, one_smul]
      congr 1; exact Subsingleton.elim _ _
    rw [h0 f, h0 g, h0 h]
    simpa using hpl 0 0
  | m + 1, R, M, θ, hR, hM, hθ0, hθ1, f, g, h, hfm, hgm, hhm, hf0, hg0, hh0, hfM, hgM, hhM,
      hfs, hgs, hhs, hpl => by
    have hbox_int : ∀ {u : (Fin (m + 1) → ℝ) → ℝ}, Measurable u → (∀ x, 0 ≤ u x) →
        (∀ x, u x ≤ M) → (∀ x, (∃ i, R < |x i|) → u x = 0) → Integrable u volume := by
      intro u hum hu0 huM hus
      let box : Set (Fin (m + 1) → ℝ) := Set.univ.pi fun _ ↦ Set.Icc (-R) R
      have hbox_meas : MeasurableSet box := MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
      have hbox_fin : volume box < ⊤ := by
        change (Measure.pi fun _ : Fin (m + 1) ↦ (volume : Measure ℝ)) box < ⊤
        rw [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ ↦ by simp [Real.volume_Icc]
      have hind_int : Integrable (box.indicator fun _ : Fin (m + 1) → ℝ ↦ M) volume :=
        (integrableOn_const hbox_fin.ne).integrable_indicator hbox_meas
      refine Integrable.mono' hind_int hum.aestronglyMeasurable
        (ae_of_all _ fun x ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]
      by_cases hx : x ∈ box
      · rw [Set.indicator_of_mem hx]; exact huM x
      · rw [Set.indicator_of_notMem hx]
        simp only [box, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc, not_forall] at hx
        obtain ⟨i, hi⟩ := hx
        have hgt : R < |x i| := by
          rw [lt_abs]
          by_cases h1 : -R ≤ x i
          · exact Or.inl (not_le.1 fun h2 ↦ hi ⟨h1, h2⟩)
          · exact Or.inr (by linarith)
        rw [hus x ⟨i, hgt⟩]
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0
    have hcons : ∀ (t : ℝ) (x : Fin m → ℝ), e.symm (t, x) = Fin.cons t x := fun t x ↦ by
      ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;>
        simp [e, MeasurableEquiv.piFinSuccAbove]
    let F : ℝ → ℝ := fun t ↦ ∫ x : Fin m → ℝ, f (Fin.cons t x)
    let G : ℝ → ℝ := fun t ↦ ∫ y : Fin m → ℝ, g (Fin.cons t y)
    let H : ℝ → ℝ := fun t ↦ ∫ z : Fin m → ℝ, h (Fin.cons t z)
    have hF_eq : ∫ x, f x = ∫ t, F t := by
      have hint : Integrable (fun p : ℝ × (Fin m → ℝ) ↦ f (e.symm p)) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (hbox_int hfm hf0 hfM hfs)
      rw [← hmp.symm.integral_comp', Measure.volume_eq_prod, MeasureTheory.integral_prod _ hint]
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp [F]; refine integral_congr_ae (ae_of_all _ fun x ↦ by dsimp only; rw [hcons])
    have hG_eq : ∫ y, g y = ∫ t, G t := by
      have hint : Integrable (fun p : ℝ × (Fin m → ℝ) ↦ g (e.symm p)) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (hbox_int hgm hg0 hgM hgs)
      rw [← hmp.symm.integral_comp', Measure.volume_eq_prod, MeasureTheory.integral_prod _ hint]
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp [G]; refine integral_congr_ae (ae_of_all _ fun y ↦ by dsimp only; rw [hcons])
    have hH_eq : ∫ z, h z = ∫ t, H t := by
      have hint : Integrable (fun p : ℝ × (Fin m → ℝ) ↦ h (e.symm p)) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (hbox_int hhm hh0 hhM hhs)
      rw [← hmp.symm.integral_comp', Measure.volume_eq_prod, MeasureTheory.integral_prod _ hint]
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp [H]; refine integral_congr_ae (ae_of_all _ fun z ↦ by dsimp only; rw [hcons])
    rw [hF_eq, hG_eq, hH_eq]
    have hslice_meas : ∀ {u : (Fin (m + 1) → ℝ) → ℝ}, Measurable u →
        Measurable fun t : ℝ ↦ ∫ x : Fin m → ℝ, u (Fin.cons t x) := by
      intro u hum
      have hcomp : Measurable fun p : ℝ × (Fin m → ℝ) ↦ u (e.symm p) := hum.comp e.symm.measurable
      simpa only [hcons] using hcomp.stronglyMeasurable.integral_prod_right'.measurable
    have hslice_int : ∀ {u : (Fin (m + 1) → ℝ) → ℝ}, Measurable u → (∀ x, 0 ≤ u x) →
        (∀ x, u x ≤ M) → (∀ x, (∃ i, R < |x i|) → u x = 0) →
        Integrable (fun t : ℝ ↦ ∫ x : Fin m → ℝ, u (Fin.cons t x)) volume := by
      intro u hum hu0 huM hus
      have hint : Integrable (fun p : ℝ × (Fin m → ℝ) ↦ u (e.symm p)) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (hbox_int hum hu0 huM hus)
      simpa only [hcons] using hint.integral_prod_left
    have hslice_bdd : ∀ {u : (Fin (m + 1) → ℝ) → ℝ}, (∀ x, 0 ≤ u x) → (∀ x, u x ≤ M) →
        (∀ x, (∃ i, R < |x i|) → u x = 0) →
        ∀ t : ℝ, ∫ x : Fin m → ℝ, u (Fin.cons t x) ≤ M * (2 * R) ^ m := by
      intro u hu0 huM hus t
      let boxm : Set (Fin m → ℝ) := Set.univ.pi fun _ ↦ Set.Icc (-R) R
      have hbm : MeasurableSet boxm := MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
      have hbm_fin : volume boxm < ⊤ := by
        change (Measure.pi fun _ : Fin m ↦ (volume : Measure ℝ)) boxm < ⊤
        rw [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ ↦ by simp [Real.volume_Icc]
      have hvol : volume.real boxm = (2 * R) ^ m := by
        rw [Measure.real]
        change ((Measure.pi fun _ : Fin m ↦ (volume : Measure ℝ)) boxm).toReal = (2 * R) ^ m
        rw [Measure.pi_pi]
        simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [show R - -R = 2 * R by ring, ← ENNReal.ofReal_pow (by positivity),
          ENNReal.toReal_ofReal (by positivity)]
      have hle : ∀ x : Fin m → ℝ, u (Fin.cons t x) ≤ boxm.indicator (fun _ ↦ M) x := by
        intro x
        by_cases hx : x ∈ boxm
        · rw [Set.indicator_of_mem hx]; exact huM _
        · rw [Set.indicator_of_notMem hx]
          simp only [boxm, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc, not_forall] at hx
          obtain ⟨j, hj⟩ := hx
          have hgt : R < |x j| := by
            rw [lt_abs]
            by_cases h1 : -R ≤ x j
            · exact Or.inl (not_le.1 fun h2 ↦ hj ⟨h1, h2⟩)
            · exact Or.inr (by linarith)
          rw [hus (Fin.cons t x) ⟨j.succ, by simpa using hgt⟩]
      by_cases hint : Integrable (fun x : Fin m → ℝ ↦ u (Fin.cons t x)) volume
      · have hind_m : Integrable (boxm.indicator fun _ : Fin m → ℝ ↦ M) volume :=
          (integrableOn_const hbm_fin.ne).integrable_indicator hbm
        refine (integral_mono hint hind_m hle).trans_eq ?_
        rw [integral_indicator hbm, setIntegral_const, smul_eq_mul, hvol, mul_comm]
      · rw [integral_undef hint]; positivity
    have hpl_slice : ∀ s t : ℝ, F s ^ (1 - θ) * G t ^ θ ≤ H ((1 - θ) * s + θ * t) := by
      intro s t
      refine prekopa_leindler_pi m hR hM hθ0 hθ1
        (hfm.comp (Measurable.of_eval fun i ↦ Fin.cases measurable_const measurable_pi_apply i))
        (hgm.comp (Measurable.of_eval fun i ↦ Fin.cases measurable_const measurable_pi_apply i))
        (hhm.comp (Measurable.of_eval fun i ↦ Fin.cases measurable_const measurable_pi_apply i))
        (fun x ↦ hf0 _) (fun y ↦ hg0 _) (fun z ↦ hh0 _)
        (fun x ↦ hfM _) (fun y ↦ hgM _) (fun z ↦ hhM _)
        (fun x ⟨j, hj⟩ ↦ hfs _ ⟨j.succ, by simpa using hj⟩)
        (fun y ⟨j, hj⟩ ↦ hgs _ ⟨j.succ, by simpa using hj⟩)
        (fun z ⟨j, hj⟩ ↦ hhs _ ⟨j.succ, by simpa using hj⟩)
        (fun x y ↦ ?_)
      have hcomb : (1 - θ) • Fin.cons s x + θ • Fin.cons t y =
          Fin.cons ((1 - θ) * s + θ * t) ((1 - θ) • x + θ • y) := by
        ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      simpa only [hcomb] using hpl (Fin.cons s x) (Fin.cons t y)
    exact prekopa_leindler_one hθ0 hθ1 (hslice_meas hfm) (hslice_meas hgm) (hslice_meas hhm)
      (fun t ↦ integral_nonneg fun _ ↦ hf0 _) (fun t ↦ integral_nonneg fun _ ↦ hg0 _)
      (fun t ↦ integral_nonneg fun _ ↦ hh0 _)
      ⟨M * (2 * R) ^ m, hslice_bdd hf0 hfM hfs⟩ ⟨M * (2 * R) ^ m, hslice_bdd hg0 hgM hgs⟩
      (hslice_int hfm hf0 hfM hfs) (hslice_int hgm hg0 hgM hgs) (hslice_int hhm hh0 hhM hhs)
      hpl_slice

/-! ### Elementary 2D Grünbaum bisection (`≤ 4/5`) -/

/-- Secant-line moment bound for a nonnegative concave function on `[0, b]`:
`∫_0^b t h(t) dt ≥ (b / 3) * ∫_0^b h(t) dt`. -/
theorem concave_moment_ge_third {h : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hconc : ConcaveOn ℝ (Set.Icc 0 b) h) (hnn : ∀ t ∈ Set.Icc 0 b, 0 ≤ h t)
    (hint : IntervalIntegrable h volume 0 b) :
    (b / 3) * (∫ t in (0 : ℝ)..b, h t) ≤ ∫ t in (0 : ℝ)..b, t * h t := by
  let c : ℝ := b / 3
  let L : ℝ → ℝ := fun t ↦ h c * (b - t) / (2 * b / 3)
  have hc_mem : c ∈ Set.Icc (0 : ℝ) b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) b, (t - c) * L t ≤ (t - c) * h t := by
    intro t ht
    by_cases htc : t ≤ c
    · -- `t ∈ [0, b/3]`: `c = ((b - c)/(b - t)) * t + ((c - t)/(b - t)) * b` gives `h t ≤ L t`
      have hbt : 0 < b - t := by dsimp [c] at htc; linarith
      have hu : 0 ≤ (b - c) / (b - t) := div_nonneg (by dsimp [c]; linarith) hbt.le
      have hv : 0 ≤ (c - t) / (b - t) := div_nonneg (by linarith) hbt.le
      have huv : (b - c) / (b - t) + (c - t) / (b - t) = 1 := by field_simp [hbt.ne']; ring
      have hcomb : ((b - c) / (b - t)) • t + ((c - t) / (b - t)) • b = c := by
        simp only [smul_eq_mul]; field_simp [hbt.ne']; ring
      have hcv := hconc.2 ht ⟨hb.le, le_rfl⟩ hu hv huv
      rw [hcomb] at hcv
      have hb0 := hnn b ⟨hb.le, le_rfl⟩
      have hle : ((b - c) / (b - t)) * h t ≤ h c := by
        simp only [smul_eq_mul] at hcv; nlinarith
      have hLt : h t ≤ L t := by
        dsimp [L, c] at hle ⊢
        have hbc : b - b / 3 = 2 * b / 3 := by ring
        rw [hbc] at hle
        rw [le_div_iff₀ (by positivity)]
        have := (div_le_iff₀ hbt).1 (by simpa [div_mul_eq_mul_div] using hle :
          (2 * b / 3 * h t) / (b - t) ≤ h (b / 3))
        linarith
      nlinarith
    · -- `t ∈ (b/3, b]`: `t = ((b - t)/(b - c)) * c + ((t - c)/(b - c)) * b` gives `L t ≤ h t`
      push Not at htc
      have hbc : 0 < b - c := by dsimp [c]; linarith
      have hu : 0 ≤ (b - t) / (b - c) := div_nonneg (by linarith [ht.2]) hbc.le
      have hv : 0 ≤ (t - c) / (b - c) := div_nonneg (by linarith) hbc.le
      have huv : (b - t) / (b - c) + (t - c) / (b - c) = 1 := by field_simp [hbc.ne']; ring
      have hcomb : ((b - t) / (b - c)) • c + ((t - c) / (b - c)) • b = t := by
        simp only [smul_eq_mul]; field_simp [hbc.ne']; ring
      have hcv := hconc.2 hc_mem ⟨hb.le, le_rfl⟩ hu hv huv
      rw [hcomb] at hcv
      have hb0 := hnn b ⟨hb.le, le_rfl⟩
      have hLt : L t ≤ h t := by
        simp only [smul_eq_mul] at hcv
        dsimp [L, c] at hcv ⊢
        have hbc' : b - b / 3 = 2 * b / 3 := by ring
        rw [hbc'] at hcv
        have : h (b / 3) * (b - t) / (2 * b / 3) = (b - t) / (2 * b / 3) * h (b / 3) := by ring
        have hterm : 0 ≤ (t - b / 3) / (2 * b / 3) * h b :=
          mul_nonneg (div_nonneg (by dsimp [c] at htc; linarith) (by positivity)) hb0
        linarith
      nlinarith
  have hint_L : IntervalIntegrable (fun t : ℝ ↦ (t - c) * L t) volume 0 b :=
    ((continuous_id.sub continuous_const).mul
      ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _)).intervalIntegrable
      0 b
  have hint_th : IntervalIntegrable (fun t : ℝ ↦ (t - c) * h t) volume 0 b := by
    have hmul : IntervalIntegrable (fun t : ℝ ↦ t * h t) volume 0 b :=
      hint.continuousOn_mul continuousOn_id
    simpa [sub_mul] using hmul.sub (hint.const_mul c)
  have hzero_L : ∫ t in (0 : ℝ)..b, (t - c) * L t = 0 := by
    have hexp : ∀ t : ℝ, (t - c) * L t =
        (h c / (2 * b / 3)) * ((b + c) * t - t ^ 2 - c * b) := fun t ↦ by
      dsimp [L]; ring
    simp_rw [hexp]
    have hp1 : IntervalIntegrable (fun t : ℝ ↦ t) volume 0 b :=
      continuous_id.intervalIntegrable 0 b
    have hp2 : IntervalIntegrable (fun t : ℝ ↦ t ^ 2) volume 0 b :=
      (continuous_pow 2).intervalIntegrable 0 b
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((hp1.const_mul (b + c)).sub hp2) intervalIntegrable_const,
      intervalIntegral.integral_sub (hp1.const_mul (b + c)) hp2,
      intervalIntegral.integral_const_mul,
      show (fun t : ℝ ↦ t) = fun t ↦ t ^ 1 by ext t; simp,
      integral_pow, integral_pow, intervalIntegral.integral_const]
    dsimp [c]
    simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 3 ≠ 0)]
    ring
  have hmono := intervalIntegral.integral_mono_on hb.le hint_L hint_th hpt
  rw [hzero_L] at hmono
  have hsub : ∫ t in (0 : ℝ)..b, (t - c) * h t =
      (∫ t in (0 : ℝ)..b, t * h t) - c * (∫ t in (0 : ℝ)..b, h t) := by
    have hmul : IntervalIntegrable (fun t : ℝ ↦ t * h t) volume 0 b :=
      hint.continuousOn_mul continuousOn_id
    have heq : (fun t : ℝ ↦ (t - c) * h t) = fun t ↦ t * h t - c * h t := by ext t; ring
    rw [heq, intervalIntegral.integral_sub hmul (hint.const_mul c),
      intervalIntegral.integral_const_mul]
  rw [hsub] at hmono
  dsimp [c] at hmono
  linarith

/-- **Elementary 2D Grünbaum bisection (`≤ 4/5`)**: for any nonnegative concave profile `h` on
`[-a, b]` (`a, b > 0`) with `∫_{-a}^b t h(t) dt = 0`, at most `4/5` of its mass lies on `[0, b]`. -/
theorem grunbaum_1d_concave {h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hconc : ConcaveOn ℝ (Set.Icc (-a) b) h) (hnn : ∀ t ∈ Set.Icc (-a) b, 0 ≤ h t)
    (hintL : IntervalIntegrable h volume (-a) 0) (hintR : IntervalIntegrable h volume 0 b)
    (hcent : ∫ t in (-a)..b, t * h t = 0) :
    ∫ t in (0 : ℝ)..b, h t ≤ (4 / 5 : ℝ) * (∫ t in (-a)..b, h t) := by
  set M_neg : ℝ := ∫ t in (-a)..0, h t
  set M_pos : ℝ := ∫ t in (0 : ℝ)..b, h t
  have hM_neg0 : 0 ≤ M_neg := intervalIntegral.integral_nonneg (by linarith) fun t ht ↦
    hnn t ⟨ht.1, ht.2.trans hb.le⟩
  have hM_pos0 : 0 ≤ M_pos := intervalIntegral.integral_nonneg hb.le fun t ht ↦
    hnn t ⟨by linarith [ht.1], ht.2⟩
  have hM_tot : ∫ t in (-a)..b, h t = M_neg + M_pos :=
    (intervalIntegral.integral_add_adjacent_intervals hintL hintR).symm
  rw [hM_tot]
  by_contra hgt
  push Not at hgt
  -- `hgt : 4/5 * (M_neg + M_pos) < M_pos`, i.e., `4 * M_neg < M_pos`
  have h4 : 4 * M_neg < M_pos := by linarith
  have hM_pos_pos : 0 < M_pos := by linarith
  -- Step 1: Moment balance `∫_0^b t h = ∫_{-a}^0 (-t) h`
  have hbal : ∫ t in (0 : ℝ)..b, t * h t = ∫ t in (-a)..0, (-t) * h t := by
    have hmulL : IntervalIntegrable (fun t : ℝ ↦ t * h t) volume (-a) 0 :=
      hintL.continuousOn_mul continuousOn_id
    have hmulR : IntervalIntegrable (fun t : ℝ ↦ t * h t) volume 0 b :=
      hintR.continuousOn_mul continuousOn_id
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hmulL hmulR
    rw [hcent] at hsplit
    have hneg : ∫ t in (-a)..0, (-t) * h t = -(∫ t in (-a)..0, t * h t) := by
      simp_rw [neg_mul]; exact intervalIntegral.integral_neg
    linarith
  -- Step 2: `(b / 3) M_pos ≤ ∫_0^b t h = ∫_{-a}^0 (-t) h ≤ a * M_neg`
  have hconcR : ConcaveOn ℝ (Set.Icc 0 b) h :=
    hconc.subset (fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩) (convex_Icc 0 b)
  have hlow := concave_moment_ge_third hb hconcR (fun t ht ↦ hnn t ⟨by linarith [ht.1], ht.2⟩) hintR
  have hhigh : ∫ t in (-a)..0, (-t) * h t ≤ a * M_neg := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      (hintL.continuousOn_mul continuousOn_neg) (hintL.const_mul a) fun t ht ↦ ?_
    exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (hnn t ⟨ht.1, ht.2.trans hb.le⟩)
  have hba : (b / 3) * M_pos ≤ a * M_neg := by linarith
  -- Deduce `0 < M_neg` (since `0 < (b/3) * M_pos ≤ a * M_neg`) and `b < a`
  have hM_neg_pos : 0 < M_neg := by nlinarith
  have hba_lt : b < a := by nlinarith
  -- Step 3: `h(0) > 0` and on `[0, b]`, `h(t) ≤ 2 * h(0)` by concavity on `[-a, b]`
  set h0 : ℝ := h 0
  have hupper : ∀ t ∈ Set.Icc (0 : ℝ) b, h t ≤ 2 * h0 := by
    intro t ht
    have hden : 0 < a + t := by linarith [ht.1]
    have hu : 0 ≤ t / (a + t) := div_nonneg ht.1 hden.le
    have hv : 0 ≤ a / (a + t) := div_nonneg ha.le hden.le
    have huv : t / (a + t) + a / (a + t) = 1 := by field_simp [hden.ne']; ring
    have hcomb : (t / (a + t)) • (-a) + (a / (a + t)) • t = 0 := by
      simp only [smul_eq_mul]; field_simp [hden.ne']; ring
    have hcv := hconc.2 ⟨le_rfl, by linarith⟩ ⟨by linarith [ht.1], ht.2⟩ hu hv huv
    rw [hcomb] at hcv
    simp only [smul_eq_mul] at hcv
    have hna0 := hnn (-a) ⟨le_rfl, by linarith⟩
    have h1 : (a / (a + t)) * h t ≤ h0 := by nlinarith
    have h2 : h t ≤ ((a + t) / a) * h0 := by
      have := mul_le_mul_of_nonneg_left h1 (div_nonneg hden.le ha.le)
      have hcancel : ((a + t) / a) * (a / (a + t)) = 1 := by field_simp [ha.ne', hden.ne']
      linarith [show ((a + t) / a) * (a / (a + t) * h t) =
        h t by rw [← mul_assoc, hcancel, one_mul]]
    have h0nn : 0 ≤ h0 := hnn 0 ⟨by linarith, hb.le⟩
    have hrat : (a + t) / a ≤ 2 := by rw [div_le_iff₀ ha]; linarith [ht.2]
    nlinarith
  have hM_pos_le : M_pos ≤ 2 * b * h0 := by
    calc M_pos ≤ ∫ _ in (0 : ℝ)..b, (2 * h0) :=
          intervalIntegral.integral_mono_on hb.le hintR intervalIntegrable_const hupper
      _ = 2 * b * h0 := by simp [intervalIntegral.integral_const]; ring
  -- Step 4: On `[-a, 0]`, `h(t) ≥ ((a + t)/a) * h0`, so `M_neg ≥ (1/2) * a * h0`
  have hlower : ∀ t ∈ Set.Icc (-a) 0, ((a + t) / a) * h0 ≤ h t := by
    intro t ht
    have hu : 0 ≤ (-t) / a := div_nonneg (by linarith [ht.2]) ha.le
    have hv : 0 ≤ (a + t) / a := div_nonneg (by linarith [ht.1]) ha.le
    have huv : (-t) / a + (a + t) / a = 1 := by field_simp [ha.ne']; ring
    have hcomb : ((-t) / a) • (-a) + ((a + t) / a) • (0 : ℝ) = t := by
      simp only [smul_eq_mul]; field_simp [ha.ne']; ring
    have hcv := hconc.2 ⟨le_rfl, by linarith⟩ ⟨by linarith, hb.le⟩ hu hv huv
    rw [hcomb] at hcv
    simp only [smul_eq_mul] at hcv
    have hna0 := hnn (-a) ⟨le_rfl, by linarith⟩
    nlinarith
  have hM_neg_ge : (1 / 2 : ℝ) * a * h0 ≤ M_neg := by
    have hlin : IntervalIntegrable (fun t : ℝ ↦ ((a + t) / a) * h0) volume (-a) 0 :=
      (((continuous_const.add continuous_id).div_const a).mul continuous_const).intervalIntegrable
        (-a) 0
    have hint_val : ∫ t in (-a)..0, ((a + t) / a) * h0 = (1 / 2 : ℝ) * a * h0 := by
      have hexp : ∀ t : ℝ, ((a + t) / a) * h0 = h0 + (h0 / a) * t := fun t ↦ by
        field_simp [ha.ne']
      simp_rw [hexp]
      have hid : IntervalIntegrable (fun t : ℝ ↦ t) volume (-a) 0 :=
        continuous_id.intervalIntegrable (-a) 0
      rw [intervalIntegral.integral_add intervalIntegrable_const (hid.const_mul (h0 / a)),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        show (fun t : ℝ ↦ t) = fun t ↦ t ^ 1 by ext t; simp, integral_pow]
      simp only [smul_eq_mul, zero_sub, sub_neg_eq_add, zero_add, Nat.reduceAdd,
        zero_pow (by norm_num : 2 ≠ 0)]
      field_simp [ha.ne']; ring
    rw [← hint_val]
    exact intervalIntegral.integral_mono_on (by linarith) hlin hintL hlower
  -- Step 5: `M_pos² ≤ 2 b h0 * M_pos ≤ 6 a h0 * M_neg ≤ 12 M_neg²`, contradicting `4 M_neg < M_pos`
  have h0nn : 0 ≤ h0 := hnn 0 ⟨by linarith, hb.le⟩
  have hsq : M_pos ^ 2 ≤ 12 * M_neg ^ 2 := by
    calc M_pos ^ 2 = M_pos * M_pos := sq _
      _ ≤ (2 * b * h0) * M_pos := mul_le_mul_of_nonneg_right hM_pos_le hM_pos0
      _ = 6 * h0 * ((b / 3) * M_pos) := by ring
      _ ≤ 6 * h0 * (a * M_neg) := mul_le_mul_of_nonneg_left hba (by positivity)
      _ = 12 * ((1 / 2 : ℝ) * a * h0) * M_neg := by ring
      _ ≤ 12 * M_neg * M_neg := by nlinarith
      _ = 12 * M_neg ^ 2 := by ring
  nlinarith

end CslibFrontier.Analysis.Convex
