module

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# 1D Remez and Log-Concave Carbery–Wright Anticoncentration Inequalities

Self-contained proofs of the one-dimensional Remez/Lagrange anticoncentration inequality for real
univariate polynomials on compact intervals and the one-dimensional Carbery–Wright inequality for
compactly supported bounded nonnegative log-concave densities on `ℝ`.

## Main results

* `CslibFrontier.Probability.Gaussian.remez_1d_Icc`: 1D Remez/Lagrange polynomial
  anticoncentration inequality on `[0, 1]` with explicit constant `2 e²`.
* `CslibFrontier.Probability.Gaussian.remez_1d_Icc_general`: 1D Remez/Lagrange polynomial
  anticoncentration inequality on an arbitrary compact interval `[a, b]`.
* `CslibFrontier.Probability.Gaussian.carbery_wright_1d_logConcave`: 1D Carbery–Wright
  anticoncentration inequality for compactly supported log-concave densities on `ℝ`.
-/

public section

open scoped BigOperators ENNReal Pointwise
open MeasureTheory Finset Real

namespace CslibFrontier.Probability.Gaussian

/-! ### 1D Remez / Lagrange inequality on `[0, 1]` and 1D Log-Concave Carbery–Wright -/

/-- **1D Remez inequality on `[0, 1]`**: for any real polynomial `q` of degree at most `d ≥ 1`,
`α ≥ 0`, and `M > 0` with `∃ x₀ ∈ [0, 1], M ≤ |q.eval x₀|`,
`volume.real {t ∈ [0, 1] | |q.eval t| ≤ α} ≤ 2 e² · (α / M)^{1/d}`. -/
theorem remez_1d_Icc {d : ℕ} (hd : 1 ≤ d) (q : Polynomial ℝ) (hq : q.natDegree ≤ d)
    {α M : ℝ} (hα : 0 ≤ α) (hM : 0 < M) (hsup : ∃ x₀ ∈ Set.Icc (0 : ℝ) 1, M ≤ |q.eval x₀|) :
    volume.real {t ∈ Set.Icc (0 : ℝ) 1 | |q.eval t| ≤ α} ≤
      2 * Real.exp 2 * (α / M) ^ (1 / (d : ℝ)) := by
  let E : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 | |q.eval t| ≤ α}
  set μ : ℝ := volume.real E
  have hE_closed : IsClosed E :=
    isClosed_Icc.inter (isClosed_le ((Polynomial.continuous q).abs) continuous_const)
  have hE_meas : MeasurableSet E := hE_closed.measurableSet
  have hμ0 : 0 ≤ μ := measureReal_nonneg
  rcases hμ0.eq_or_lt with hμ_zero | hμ_pos
  · rw [← hμ_zero]; positivity
  rcases hα.eq_or_lt with rfl | hα_pos
  · -- `α = 0`: `q ≠ 0` has finitely many roots, so `E` has measure 0
    obtain ⟨x₀, _, hx₀⟩ := hsup
    have hq0 : q ≠ 0 := by intro h; rw [h, Polynomial.eval_zero, abs_zero] at hx₀; linarith
    have hfin : E.Finite := (q.roots.toFinset.finite_toSet).subset fun t ht ↦ by
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq0, Polynomial.IsRoot]
      exact abs_nonpos_iff.1 ht.2
    have h0 : volume E = 0 := hfin.measure_zero volume
    simp only [μ, Measure.real, h0, ENNReal.toReal_zero] at hμ_pos
    exact absurd hμ_pos (lt_irrefl 0)
  -- Define 1-Lipschitz CDF `F(t) = volume.real (E ∩ [0, t])` on `[0, 1]`
  let F : ℝ → ℝ := fun t ↦ volume.real (E ∩ Set.Icc 0 t)
  have hF_lip : ∀ s t : ℝ, s ≤ t → F t - F s ≤ t - s := by
    intro s t hst
    have hsub : E ∩ Set.Icc 0 t ⊆ (E ∩ Set.Icc 0 s) ∪ Set.Icc s t := by
      intro u ⟨huE, hu0, hut⟩
      by_cases hus : u ≤ s
      · exact Or.inl ⟨huE, hu0, hus⟩
      · exact Or.inr ⟨(not_le.1 hus).le, hut⟩
    have hfin1 : volume (E ∩ Set.Icc 0 s) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc])
        (measure_mono Set.inter_subset_right)
    have hfin2 : volume (Set.Icc s t) ≠ ⊤ := by simp [Real.volume_Icc]
    have hle : volume.real (E ∩ Set.Icc 0 t) ≤
        volume.real (E ∩ Set.Icc 0 s) + volume.real (Set.Icc s t) :=
      (measureReal_mono hsub
        (measure_union_lt_top (lt_top_iff_ne_top.2 hfin1) (lt_top_iff_ne_top.2 hfin2)).ne).trans
        (measureReal_union_le _ _)
    have hvol : volume.real (Set.Icc s t) = t - s := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hst)]
    linarith
  have hF_mono : Monotone F := fun s t hst ↦
    measureReal_mono (Set.inter_subset_inter_right E (Set.Icc_subset_Icc_right hst))
      (ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.inter_subset_right))
  have hF_cont : Continuous F := by
    refine Metric.continuous_iff.2 fun x ε hε ↦ ⟨ε, hε, fun y hy ↦ ?_⟩
    rw [Real.dist_eq] at hy ⊢
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.2 (hF_mono hxy))]
      have := hF_lip x y hxy
      rw [abs_of_nonneg (sub_nonneg.2 hxy)] at hy
      linarith
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hF_mono hyx))]
      have := hF_lip y x hyx
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hyx)] at hy
      linarith
  have hF0 : F 0 = 0 := by
    have hsub : E ∩ Set.Icc (0 : ℝ) 0 ⊆ {0} := fun x hx ↦
      Set.mem_singleton_iff.2 (le_antisymm hx.2.2 hx.2.1)
    have h0 : volume (E ∩ Set.Icc (0 : ℝ) 0) = 0 := measure_mono_null hsub (measure_singleton 0)
    rw [show F 0 = volume.real (E ∩ Set.Icc 0 0) from rfl, Measure.real, h0, ENNReal.toReal_zero]
  have hF1 : F 1 = μ := by
    have heq : E ∩ Set.Icc (0 : ℝ) 1 = E := Set.inter_eq_left.2 fun _ hx ↦ hx.1
    simp [F, μ, heq]
  -- Pick `d + 1` nodes `t_j = sInf {t ∈ [0, 1] | c_j ≤ F t}` in `E`
  let c : Fin (d + 1) → ℝ := fun j ↦ ((2 * (j.1 : ℝ) + 1) / (2 * (d : ℝ) + 2)) * μ
  let node : Fin (d + 1) → ℝ := fun j ↦ sInf {t ∈ Set.Icc (0 : ℝ) 1 | c j ≤ F t}
  have hc_pos : ∀ j : Fin (d + 1), 0 < c j := fun j ↦ by dsimp [c]; positivity
  have hc_lt : ∀ j : Fin (d + 1), c j < μ := fun j ↦ by
    dsimp [c]
    have hj : (j.1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.2
    have hfrac : (2 * (j.1 : ℝ) + 1) / (2 * (d : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith
  have hnode_props : ∀ j : Fin (d + 1),
      node j ∈ Set.Icc (0 : ℝ) 1 ∧ F (node j) = c j ∧ node j ∈ E := by
    intro j
    let S := {t ∈ Set.Icc (0 : ℝ) 1 | c j ≤ F t}
    have hS_closed : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hF_cont)
    have hS_ne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hF1]; exact (hc_lt j).le⟩
    have hS_bdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1.1⟩
    have hmem : node j ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
    have hF_eq : F (node j) = c j := by
      refine le_antisymm ?_ hmem.2
      by_contra hgt
      push Not at hgt
      have hpos : 0 < node j := by
        rcases hmem.1.1.eq_or_lt with h0 | hpos
        · rw [← h0, hF0] at hgt; linarith [hc_pos j]
        · exact hpos
      have hnhds := Metric.tendsto_nhds.1 (hF_cont.continuousAt (x := node j))
        ((F (node j) - c j) / 2) (by linarith)
      rw [Filter.Eventually, Metric.mem_nhds_iff] at hnhds
      obtain ⟨r, hr0, hr⟩ := hnhds
      let t' := max 0 (node j - min (node j / 2) (r / 2))
      have ht'_lt : t' < node j := by
        dsimp [t']
        exact max_lt hpos (by linarith [lt_min (half_pos hpos) (half_pos hr0)])
      have ht'_mem : t' ∈ Set.Icc (0 : ℝ) 1 := ⟨le_max_left _ _, ht'_lt.le.trans hmem.1.2⟩
      have hdist : dist t' (node j) < r := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.2 ht'_lt)]
        have h1 : node j - min (node j / 2) (r / 2) ≤ t' := le_max_right _ _
        linarith [min_le_right (node j / 2) (r / 2)]
      have hclose := hr hdist
      dsimp only [Set.mem_ofPred_eq] at hclose
      rw [Real.dist_eq] at hclose
      have hct' : c j ≤ F t' := by linarith [(abs_lt.1 hclose).1]
      have : node j ≤ t' := csInf_le hS_bdd ⟨ht'_mem, hct'⟩
      linarith
    have hmemE : node j ∈ E := by
      by_contra hnot
      have hopen : IsOpen Eᶜ := hE_closed.isOpen_compl
      obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.1 hopen (node j) hnot
      have hpos : 0 < node j := by
        rcases hmem.1.1.eq_or_lt with h0 | hpos
        · rw [← h0, hF0] at hF_eq; linarith [hc_pos j]
        · exact hpos
      let t' := max 0 (node j - min (node j / 2) (r / 2))
      have ht'_lt : t' < node j :=
        max_lt hpos (by linarith [lt_min (half_pos hpos) (half_pos hr0)])
      have hsub : E ∩ Set.Icc 0 (node j) ⊆ E ∩ Set.Icc 0 t' := by
        intro u ⟨huE, hu0, hun⟩
        refine ⟨huE, hu0, ?_⟩
        by_contra hgt
        push Not at hgt
        have hdist : dist u (node j) < r := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hun)]
          have h1 : node j - min (node j / 2) (r / 2) ≤ t' := le_max_right _ _
          linarith [min_le_right (node j / 2) (r / 2)]
        exact hr hdist huE
      have hFt' : F (node j) ≤ F t' := measureReal_mono hsub
        (ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.inter_subset_right))
      have : node j ≤ t' :=
        csInf_le hS_bdd ⟨⟨le_max_left _ _, ht'_lt.le.trans hmem.1.2⟩, by linarith⟩
      linarith
    exact ⟨hmem.1, hF_eq, hmemE⟩
  -- Separation: `|node k - node j| ≥ |k - j| * (μ / (d + 1))`
  have hsep : ∀ j k : Fin (d + 1),
      |(k.1 : ℝ) - (j.1 : ℝ)| * (μ / ((d : ℝ) + 1)) ≤ |node k - node j| := by
    intro j k
    have hdiff_c : ∀ a b : Fin (d + 1), a.1 ≤ b.1 →
        ((b.1 : ℝ) - (a.1 : ℝ)) * (μ / ((d : ℝ) + 1)) = c b - c a := fun a b _ ↦ by
      dsimp [c]; field_simp [(by positivity : (2 * (d : ℝ) + 2) ≠ 0),
        (by positivity : ((d : ℝ) + 1) ≠ 0)]; ring
    rcases le_total j.1 k.1 with hjk | hkj
    · have hlt : node j ≤ node k := by
        by_contra hgt; push Not at hgt
        have hFj := (hnode_props j).2.1
        have hFk := (hnode_props k).2.1
        have hmono := hF_mono hgt.le
        have hcle : c j ≤ c k := by
          have := hdiff_c j k hjk
          have : (0 : ℝ) ≤ ((k.1 : ℝ) - (j.1 : ℝ)) * (μ / ((d : ℝ) + 1)) := by
            refine mul_nonneg (sub_nonneg.2 (by exact_mod_cast hjk)) (by positivity)
          linarith
        have hce : c j = c k := le_antisymm hcle (by linarith)
        have hjeq : j.1 = k.1 := by
          have := hdiff_c j k hjk
          have hpos : (0 : ℝ) < μ / ((d : ℝ) + 1) := by positivity
          have : (k.1 : ℝ) - (j.1 : ℝ) = 0 := by nlinarith
          exact_mod_cast (by linarith : (j.1 : ℝ) = (k.1 : ℝ))
        have : j = k := Fin.ext hjeq
        rw [this] at hgt; exact lt_irrefl _ hgt
      rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hjk)),
        abs_of_nonneg (sub_nonneg.2 hlt), hdiff_c j k hjk,
        ← (hnode_props j).2.1, ← (hnode_props k).2.1]
      exact hF_lip (node j) (node k) hlt
    · rw [abs_sub_comm (k.1 : ℝ), abs_sub_comm (node k)]
      have hlt : node k ≤ node j := by
        by_contra hgt; push Not at hgt
        have hFj := (hnode_props j).2.1
        have hFk := (hnode_props k).2.1
        have hmono := hF_mono hgt.le
        have hcle : c k ≤ c j := by
          have := hdiff_c k j hkj
          have : (0 : ℝ) ≤ ((j.1 : ℝ) - (k.1 : ℝ)) * (μ / ((d : ℝ) + 1)) := by
            refine mul_nonneg (sub_nonneg.2 (by exact_mod_cast hkj)) (by positivity)
          linarith
        have hce : c k = c j := le_antisymm hcle (by linarith)
        have hjeq : k.1 = j.1 := by
          have := hdiff_c k j hkj
          have hpos : (0 : ℝ) < μ / ((d : ℝ) + 1) := by positivity
          have : (j.1 : ℝ) - (k.1 : ℝ) = 0 := by nlinarith
          exact_mod_cast (by linarith : (k.1 : ℝ) = (j.1 : ℝ))
        have : k = j := Fin.ext hjeq
        rw [this] at hgt; exact lt_irrefl _ hgt
      rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hkj)),
        abs_of_nonneg (sub_nonneg.2 hlt), hdiff_c k j hkj,
        ← (hnode_props k).2.1, ← (hnode_props j).2.1]
      exact hF_lip (node k) (node j) hlt
  have hinj : Set.InjOn node (↑(Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) := by
    intro j _ k _ heq
    by_contra hne
    have h1 := hsep j k
    rw [heq, sub_self, abs_zero] at h1
    have hne' : (k.1 : ℝ) ≠ (j.1 : ℝ) := fun h ↦ hne (Fin.ext (by exact_mod_cast h.symm))
    have hpos : 0 < |(k.1 : ℝ) - (j.1 : ℝ)| * (μ / ((d : ℝ) + 1)) :=
      mul_pos (abs_pos.2 (sub_ne_zero.2 hne')) (by positivity)
    linarith
  -- Apply Lagrange interpolation at `node`
  have hlag : q = Lagrange.interpolate Finset.univ node (fun j ↦ q.eval (node j)) := by
    have hdeg : q.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.2 hq)).trans_lt
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self d))
    exact Lagrange.eq_interpolate hinj hdeg
  obtain ⟨x₀, hx₀I, hx₀M⟩ := hsup
  have hq_eval : q.eval x₀ = ∑ j : Fin (d + 1),
      q.eval (node j) * ∏ k ∈ Finset.univ.erase j, (x₀ - node k) / (node j - node k) := by
    conv_lhs => rw [hlag]
    rw [Lagrange.interpolate_apply]
    change Polynomial.evalRingHom x₀ _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C, Lagrange.basis]
    congr 1
    change Polynomial.evalRingHom x₀ _ = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    simp [Lagrange.basisDivisor, div_eq_inv_mul]
  -- Bound each Lagrange basis polynomial at `x₀ ∈ [0, 1]`
  have hprod_idx : ∀ j : Fin (d + 1),
      ∏ k ∈ Finset.univ.erase j, |(j.1 : ℝ) - (k.1 : ℝ)| =
        ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
    intro j
    have hsplit : Finset.univ.erase j =
        (Finset.univ.filter fun k : Fin (d + 1) ↦ k.1 < j.1) ∪
        (Finset.univ.filter fun k : Fin (d + 1) ↦ j.1 < k.1) := by
      ext k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, Finset.mem_union,
        Finset.mem_filter]
      constructor
      · intro hne; exact lt_or_gt_of_ne fun h ↦ hne (Fin.ext h)
      · rintro (h | h) rfl <;> exact lt_irrefl _ h
    have hdisj : Disjoint (Finset.univ.filter fun k : Fin (d + 1) ↦ k.1 < j.1)
        (Finset.univ.filter fun k : Fin (d + 1) ↦ j.1 < k.1) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2; omega
    rw [hsplit, Finset.prod_union hdisj, Nat.cast_mul]
    congr 1
    · have hbij : ∏ k ∈ Finset.univ.filter (fun k : Fin (d + 1) ↦ k.1 < j.1),
            |(j.1 : ℝ) - (k.1 : ℝ)| =
          ∏ m ∈ Finset.range j.1, ((m + 1 : ℕ) : ℝ) := by
        refine Finset.prod_nbij (fun k ↦ j.1 - 1 - k.1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact Finset.mem_range.2 (by omega)
        · intro k1 hk1 k2 hk2 heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
          dsimp only at heq
          exact Fin.ext (by omega)
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_range] at hm
          have hj := j.2
          refine ⟨⟨j.1 - 1 - m, by omega⟩,
            Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp only; omega⟩),
            by dsimp only; omega⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hk.le))]
          have : j.1 - 1 - k.1 + 1 = j.1 - k.1 := by omega
          rw [this, Nat.cast_sub hk.le]
      rw [hbij]
      clear hbij hsplit hdisj
      induction j.1 with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, ih, mul_comm]
    · have hbij : ∏ k ∈ Finset.univ.filter (fun k : Fin (d + 1) ↦ j.1 < k.1),
            |(j.1 : ℝ) - (k.1 : ℝ)| =
          ∏ m ∈ Finset.range (d - j.1), ((m + 1 : ℕ) : ℝ) := by
        refine Finset.prod_nbij (fun k ↦ k.1 - j.1 - 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hk2 := k.2
          exact Finset.mem_range.2 (by omega)
        · intro k1 hk1 k2 hk2 heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
          dsimp only at heq
          exact Fin.ext (by omega)
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_range] at hm
          have hj := j.2
          refine ⟨⟨j.1 + 1 + m, by omega⟩,
            Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp only; omega⟩),
            by dsimp only; omega⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hk.le))]
          have : k.1 - j.1 - 1 + 1 = k.1 - j.1 := by omega
          rw [this, Nat.cast_sub hk.le]
      rw [hbij]
      clear hbij hsplit hdisj
      induction (d - j.1) with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, ih, mul_comm]
  have hM_le : M ≤ α * (2 * Real.exp 2 / μ) ^ d := by
    have h1 : M ≤ ∑ j : Fin (d + 1),
        α * (((d : ℝ) + 1) / μ) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
      refine hx₀M.trans ?_
      rw [hq_eval]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [abs_mul, Finset.abs_prod]
      have hqj : |q.eval (node j)| ≤ α := (hnode_props j).2.2.2
      have hden_pos : 0 < ∏ k ∈ Finset.univ.erase j, |node j - node k| :=
        Finset.prod_pos fun k hk ↦ by
          have hne : k ≠ j := (Finset.mem_erase.1 hk).1
          exact abs_pos.2 (sub_ne_zero.2 fun h ↦
            hne (hinj (Finset.mem_univ _) (Finset.mem_univ _) h.symm))
      have hnum_le : ∏ k ∈ Finset.univ.erase j, |x₀ - node k| ≤ 1 := by
        calc ∏ k ∈ Finset.univ.erase j, |x₀ - node k|
            ≤ ∏ _k ∈ Finset.univ.erase j, (1 : ℝ) := by
              gcongr with k _
              have hkI := (hnode_props k).1
              rw [abs_le]; constructor <;> linarith [hx₀I.1, hx₀I.2, hkI.1, hkI.2]
          _ = 1 := by simp
      have hden_ge : ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) *
            (μ / ((d : ℝ) + 1)) ^ d ≤ ∏ k ∈ Finset.univ.erase j, |node j - node k| := by
        rw [← hprod_idx j]
        have hcard : (Finset.univ.erase j : Finset (Fin (d + 1))).card = d := by
          simp [Finset.card_erase_of_mem]
        have hpow_prod : (μ / ((d : ℝ) + 1)) ^ d =
            ∏ _k ∈ Finset.univ.erase j, (μ / ((d : ℝ) + 1)) := by
          rw [Finset.prod_const, hcard]
        rw [hpow_prod, ← Finset.prod_mul_distrib]
        gcongr with k _
        exact hsep k j
      have hprod_le : ∏ k ∈ Finset.univ.erase j, |(x₀ - node k) / (node j - node k)| ≤
          (((d : ℝ) + 1) / μ) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
        simp_rw [abs_div, Finset.prod_div_distrib]
        have hfact_pos : (0 : ℝ) < ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
        calc (∏ k ∈ Finset.univ.erase j, |x₀ - node k|) /
              (∏ k ∈ Finset.univ.erase j, |node j - node k|)
            ≤ 1 / (((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) * (μ / ((d : ℝ) + 1)) ^ d) :=
              div_le_div₀ zero_le_one hnum_le (by positivity) hden_ge
          _ = (((d : ℝ) + 1) / μ) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
              rw [div_pow, div_pow]; field_simp [hfact_pos.ne', hμ_pos.ne',
                (by positivity : ((d : ℝ) + 1) ≠ 0)]
      calc |q.eval (node j)| * ∏ k ∈ Finset.univ.erase j, |(x₀ - node k) / (node j - node k)|
          ≤ α * ((((d : ℝ) + 1) / μ) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ)) :=
            mul_le_mul hqj hprod_le (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) hα_pos.le
        _ = α * (((d : ℝ) + 1) / μ) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by ring
    refine h1.trans ?_
    have hsum_inv : ∑ j : Fin (d + 1),
        (1 : ℝ) / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
        (2 : ℝ) ^ d / (d.factorial : ℝ) := by
      have hch : ∀ j : Fin (d + 1),
          (1 : ℝ) / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
          (d.choose j.1 : ℝ) / (d.factorial : ℝ) := fun j ↦ by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ j.2)
        have hcast : (d.choose j.1 : ℝ) * ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
            (d.factorial : ℝ) := by
          exact_mod_cast (by linarith [mul_assoc (d.choose j.1) j.1.factorial (d - j.1).factorial] :
            d.choose j.1 * (j.1.factorial * (d - j.1).factorial) = d.factorial)
        have hf1 : ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
        have hf2 : (d.factorial : ℝ) ≠ 0 := by positivity
        rw [div_eq_div_iff hf1 hf2]; linarith
      simp_rw [hch, ← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k ↦ (d.choose k : ℝ))]
      congr 1
      exact_mod_cast Nat.sum_range_choose d
    have hfac : ∑ j : Fin (d + 1),
          α * (((d : ℝ) + 1) / μ) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
        α * (((d : ℝ) + 1) / μ) ^ d * ((2 : ℝ) ^ d / (d.factorial : ℝ)) := by
      rw [← hsum_inv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hfac]
    -- Bound `(d + 1)^d / d! ≤ exp (d + 1) ≤ (exp 2)^d`
    have hexp_bound : ((d : ℝ) + 1) ^ d / (d.factorial : ℝ) ≤ (Real.exp 2) ^ d := by
      have hterm : ((d : ℝ) + 1) ^ d / (d.factorial : ℝ) ≤ Real.exp ((d : ℝ) + 1) := by
        have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1) (d + 1)
        exact (Finset.single_le_sum (f := fun k ↦ ((d : ℝ) + 1) ^ k / (k.factorial : ℝ))
          (fun _ _ ↦ by positivity) (Finset.mem_range.2 (Nat.lt_succ_self d))).trans hsum
      have h2d : (d : ℝ) + 1 ≤ 2 * (d : ℝ) := by
        have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      calc ((d : ℝ) + 1) ^ d / (d.factorial : ℝ)
          ≤ Real.exp ((d : ℝ) + 1) := hterm
        _ ≤ Real.exp (2 * (d : ℝ)) := Real.exp_le_exp.2 h2d
        _ = (Real.exp 2) ^ d := by rw [mul_comm, Real.exp_nat_mul]
    calc α * (((d : ℝ) + 1) / μ) ^ d * ((2 : ℝ) ^ d / (d.factorial : ℝ))
        = α * ((2 : ℝ) ^ d / μ ^ d) * (((d : ℝ) + 1) ^ d / (d.factorial : ℝ)) := by
          rw [div_pow]; ring
      _ ≤ α * ((2 : ℝ) ^ d / μ ^ d) * (Real.exp 2) ^ d :=
          mul_le_mul_of_nonneg_left hexp_bound (by positivity)
      _ = α * (2 * Real.exp 2 / μ) ^ d := by rw [div_pow, mul_pow]; ring
  -- Rearrange `M ≤ α * (2 e² / μ)^d` to `μ ≤ 2 e² * (α / M)^{1/d}`
  have hpow : μ ^ d ≤ (2 * Real.exp 2) ^ d * (α / M) := by
    rw [div_pow] at hM_le
    have h1 : M * μ ^ d ≤ α * (2 * Real.exp 2) ^ d := by
      rwa [← mul_div_assoc, le_div_iff₀ (pow_pos hμ_pos d)] at hM_le
    rw [mul_div_assoc', le_div_iff₀ hM]
    linarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hrt := Real.rpow_le_rpow (pow_nonneg hμ_pos.le d) hpow (by positivity : 0 ≤ 1 / (d : ℝ))
  rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le, mul_one_div_cancel hd_pos.ne',
    Real.rpow_one, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), mul_one_div_cancel hd_pos.ne', Real.rpow_one] at hrt
  exact hrt

/-- **1D Remez inequality on an arbitrary compact interval `[a, b]` (`a < b`)**. -/
theorem remez_1d_Icc_general {d : ℕ} (hd : 1 ≤ d) (q : Polynomial ℝ) (hq : q.natDegree ≤ d)
    {a b α M : ℝ} (hab : a < b) (hα : 0 ≤ α) (hM : 0 < M)
    (hsup : ∃ x₀ ∈ Set.Icc a b, M ≤ |q.eval x₀|) :
    volume.real {t ∈ Set.Icc a b | |q.eval t| ≤ α} ≤
      (b - a) * (2 * Real.exp 2 * (α / M) ^ (1 / (d : ℝ))) := by
  let L : Polynomial ℝ := Polynomial.C (b - a) * Polynomial.X + Polynomial.C a
  let q' : Polynomial ℝ := q.comp L
  have hdegL : L.natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (Polynomial.natDegree_mul_le).trans (by simp)
  have hq' : q'.natDegree ≤ d := by
    calc q'.natDegree ≤ q.natDegree * L.natDegree := Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hq hdegL
      _ = d := mul_one d
  have hL_eval : ∀ u : ℝ, q'.eval u = q.eval ((b - a) * u + a) := fun u ↦ by
    simp [q', L, Polynomial.eval_comp]
  have hsup' : ∃ u₀ ∈ Set.Icc (0 : ℝ) 1, M ≤ |q'.eval u₀| := by
    obtain ⟨x₀, hx₀, hx₀M⟩ := hsup
    refine ⟨(x₀ - a) / (b - a), ⟨div_nonneg (by linarith [hx₀.1]) (by linarith),
      (div_le_one (by linarith)).2 (by linarith [hx₀.2])⟩, ?_⟩
    rw [hL_eval]
    have heq : (b - a) * ((x₀ - a) / (b - a)) + a = x₀ := by field_simp [(sub_pos.2 hab).ne']; ring
    rwa [heq]
  have h01 := remez_1d_Icc hd q' hq' hα hM hsup'
  have himg : {t ∈ Set.Icc a b | |q.eval t| ≤ α} =
      (fun u : ℝ ↦ (b - a) * u + a) '' {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨⟨ht1, ht2⟩, hqt⟩
      refine ⟨(t - a) / (b - a), ⟨⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩, ?_⟩
      · rw [hL_eval]
        have heq : (b - a) * ((t - a) / (b - a)) + a = t := by
          field_simp [(sub_pos.2 hab).ne']; ring
        rwa [heq]
      · field_simp [(sub_pos.2 hab).ne']; ring
    · rintro ⟨u, ⟨⟨hu0, hu1⟩, hqu⟩, rfl⟩
      rw [hL_eval] at hqu
      exact ⟨⟨by nlinarith, by nlinarith⟩, hqu⟩
  have hvol : volume.real {t ∈ Set.Icc a b | |q.eval t| ≤ α} =
      (b - a) * volume.real {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α} := by
    rw [himg]
    have hcomp : (fun u : ℝ ↦ (b - a) * u + a) '' {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α} =
        (fun t ↦ t + a) '' ((b - a) • {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α}) := by
      ext t
      simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨(b - a) * u, ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
    rw [hcomp, Measure.real]
    have htr : volume ((fun t ↦ t + a) '' ((b - a) • {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α})) =
        volume ((b - a) • {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α}) := by
      have heq : (fun t ↦ t + a) '' ((b - a) • {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α}) =
          (fun t ↦ t + (-a)) ⁻¹' ((b - a) • {u ∈ Set.Icc (0 : ℝ) 1 | |q'.eval u| ≤ α}) := by
        ext z
        simp only [Set.mem_image, Set.mem_preimage]
        exact ⟨fun ⟨x, hx, hxz⟩ ↦ by rwa [show z + -a = x by linarith],
          fun hz ↦ ⟨z + -a, hz, by ring⟩⟩
      rw [heq]; exact measure_preimage_add_right volume (-a) _
    rw [htr, Measure.addHaar_smul_of_nonneg volume (sub_pos.2 hab).le, Module.finrank_self ℝ,
      pow_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_pos.2 hab).le]
    rfl
  rw [hvol]
  exact mul_le_mul_of_nonneg_left h01 (sub_pos.2 hab).le

/-- **Extrapolation of a degree-`≤ d` polynomial from an interval `[a, b]` (`a < b`) to a
`k`-fold dilation around `x₀ ∈ [a, b]`**: if `|q(z)| ≤ S` on `[a, b]`, then for any `t` with
`|t - x₀| ≤ k * (b - a)`, `|q(t)| ≤ S * (2 e (k + 1))^d`. -/
private theorem abs_eval_le_of_dilated_Icc {d : ℕ} (hd : 1 ≤ d) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ d) {a b x₀ S : ℝ} (hab : a < b) (hx₀ : x₀ ∈ Set.Icc a b) (hS : 0 ≤ S)
    (hbd : ∀ z ∈ Set.Icc a b, |q.eval z| ≤ S) {k : ℝ} (hk : 0 ≤ k) {t : ℝ}
    (ht : |t - x₀| ≤ k * (b - a)) :
    |q.eval t| ≤ S * (2 * Real.exp 1 * (k + 1)) ^ d := by
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.2 hab
  let z : Fin (d + 1) → ℝ := fun j ↦ a + ((j.1 : ℝ) / (d : ℝ)) * L
  have hz_mem : ∀ j : Fin (d + 1), z j ∈ Set.Icc a b := fun j ↦ by
    have hj : (j.1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.2
    have hfrac : (j.1 : ℝ) / (d : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.2 hd)).2 hj
    have hnn : 0 ≤ (j.1 : ℝ) / (d : ℝ) := div_nonneg (Nat.cast_nonneg j.1) (Nat.cast_nonneg d)
    exact ⟨by dsimp [z]; nlinarith, by dsimp [z, L]; nlinarith⟩
  have hinj : Set.InjOn z (↑(Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) := by
    intro j _ r _ heq
    have h1 : ((j.1 : ℝ) / (d : ℝ)) * L = ((r.1 : ℝ) / (d : ℝ)) * L := by dsimp [z] at heq; linarith
    have h2 : (j.1 : ℝ) = (r.1 : ℝ) := by
      have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiv := mul_right_cancel₀ hL.ne' h1
      exact mul_right_cancel₀ hd0 ((div_eq_div_iff hd0 hd0).1 hdiv)
    exact Fin.ext (by exact_mod_cast h2)
  have hlag : q = Lagrange.interpolate Finset.univ z (fun j ↦ q.eval (z j)) := by
    have hdeg : q.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.2 hq)).trans_lt
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self d))
    exact Lagrange.eq_interpolate hinj hdeg
  have hq_eval : q.eval t = ∑ j : Fin (d + 1),
      q.eval (z j) * ∏ r ∈ Finset.univ.erase j, (t - z r) / (z j - z r) := by
    conv_lhs => rw [hlag]
    rw [Lagrange.interpolate_apply]
    change Polynomial.evalRingHom t _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C, Lagrange.basis]
    congr 1
    change Polynomial.evalRingHom t _ = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    simp [Lagrange.basisDivisor, div_eq_inv_mul]
  have htz : ∀ r : Fin (d + 1), |t - z r| ≤ (k + 1) * L := fun r ↦ by
    have hr := hz_mem r
    have hx0r : |x₀ - z r| ≤ L := by
      rw [abs_le]; dsimp [L]; constructor <;> linarith [hx₀.1, hx₀.2, hr.1, hr.2]
    calc |t - z r| = |(t - x₀) + (x₀ - z r)| := by ring_nf
      _ ≤ |t - x₀| + |x₀ - z r| := abs_add_le _ _
      _ ≤ k * L + L := add_le_add ht hx0r
      _ = (k + 1) * L := by ring
  have hprod_idx : ∀ j : Fin (d + 1),
      ∏ r ∈ Finset.univ.erase j, |(j.1 : ℝ) - (r.1 : ℝ)| =
        ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
    intro j
    have hsplit : Finset.univ.erase j =
        (Finset.univ.filter fun r : Fin (d + 1) ↦ r.1 < j.1) ∪
        (Finset.univ.filter fun r : Fin (d + 1) ↦ j.1 < r.1) := by
      ext r
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, Finset.mem_union,
        Finset.mem_filter]
      constructor
      · intro hne; exact lt_or_gt_of_ne fun h ↦ hne (Fin.ext h)
      · rintro (h | h) rfl <;> exact lt_irrefl _ h
    have hdisj : Disjoint (Finset.univ.filter fun r : Fin (d + 1) ↦ r.1 < j.1)
        (Finset.univ.filter fun r : Fin (d + 1) ↦ j.1 < r.1) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    rw [hsplit, Finset.prod_union hdisj, Nat.cast_mul]
    congr 1
    · have hbij : ∏ r ∈ Finset.univ.filter (fun r : Fin (d + 1) ↦ r.1 < j.1),
            |(j.1 : ℝ) - (r.1 : ℝ)| = ∏ m ∈ Finset.range j.1, ((m + 1 : ℕ) : ℝ) := by
        refine Finset.prod_nbij (fun r ↦ j.1 - 1 - r.1) ?_ ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact Finset.mem_range.2 (by omega)
        · intro r1 h1 r2 h2 heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          dsimp only at heq
          exact Fin.ext (by omega)
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_range] at hm
          have hj := j.2
          exact ⟨⟨j.1 - 1 - m, by omega⟩,
            Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp only; omega⟩),
            by dsimp only; omega⟩
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hr.le))]
          have : j.1 - 1 - r.1 + 1 = j.1 - r.1 := by omega
          rw [this, Nat.cast_sub hr.le]
      rw [hbij]; clear hbij hsplit hdisj
      induction j.1 with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, ih, mul_comm]
    · have hbij : ∏ r ∈ Finset.univ.filter (fun r : Fin (d + 1) ↦ j.1 < r.1),
            |(j.1 : ℝ) - (r.1 : ℝ)| = ∏ m ∈ Finset.range (d - j.1), ((m + 1 : ℕ) : ℝ) := by
        refine Finset.prod_nbij (fun r ↦ r.1 - j.1 - 1) ?_ ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          have hr2 := r.2
          exact Finset.mem_range.2 (by omega)
        · intro r1 h1 r2 h2 heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          dsimp only at heq
          exact Fin.ext (by omega)
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_range] at hm
          have hj := j.2
          exact ⟨⟨j.1 + 1 + m, by omega⟩,
            Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp only; omega⟩),
            by dsimp only; omega⟩
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hr.le))]
          have : r.1 - j.1 - 1 + 1 = r.1 - j.1 := by omega
          rw [this, Nat.cast_sub hr.le]
      rw [hbij]; clear hbij hsplit hdisj
      induction (d - j.1) with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, ih, mul_comm]
  rw [hq_eval]
  have hsum_le : |∑ j : Fin (d + 1),
        q.eval (z j) * ∏ r ∈ Finset.univ.erase j, (t - z r) / (z j - z r)| ≤
      S * ((d : ℝ) * (k + 1)) ^ d *
        ∑ j : Fin (d + 1), (1 : ℝ) / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul, Finset.abs_prod]
    have hcard : (Finset.univ.erase j : Finset (Fin (d + 1))).card = d := by
      simp [Finset.card_erase_of_mem]
    have hnum : ∏ r ∈ Finset.univ.erase j, |t - z r| ≤ ((k + 1) * L) ^ d := by
      calc ∏ r ∈ Finset.univ.erase j, |t - z r|
          ≤ ∏ _r ∈ Finset.univ.erase j, ((k + 1) * L) := by
            gcongr with r _; exact htz r
        _ = ((k + 1) * L) ^ d := by rw [Finset.prod_const, hcard]
    have hden : ∏ r ∈ Finset.univ.erase j, |z j - z r| =
        ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) * (L / (d : ℝ)) ^ d := by
      have hdiff : ∀ r : Fin (d + 1), |z j - z r| = |(j.1 : ℝ) - (r.1 : ℝ)| * (L / (d : ℝ)) := by
        intro r
        dsimp [z]
        have : a + (j.1 : ℝ) / (d : ℝ) * L - (a + (r.1 : ℝ) / (d : ℝ) * L) =
            ((j.1 : ℝ) - (r.1 : ℝ)) * (L / (d : ℝ)) := by ring
        rw [this, abs_mul, abs_of_pos (div_pos hL (Nat.cast_pos.2 hd))]
      simp_rw [hdiff, Finset.prod_mul_distrib, Finset.prod_const, hcard, hprod_idx j]
    have hprod_le : ∏ r ∈ Finset.univ.erase j, |(t - z r) / (z j - z r)| ≤
        ((d : ℝ) * (k + 1)) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
      simp_rw [abs_div, Finset.prod_div_distrib, hden]
      have hfact_pos : (0 : ℝ) < ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      calc (∏ r ∈ Finset.univ.erase j, |t - z r|) /
            (((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) * (L / (d : ℝ)) ^ d)
          ≤ ((k + 1) * L) ^ d /
            (((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) * (L / (d : ℝ)) ^ d) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = ((d : ℝ) * (k + 1)) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) := by
            rw [mul_pow, mul_pow, div_pow]; field_simp [hfact_pos.ne', hL.ne', hd0]
    have hqj := hbd (z j) (hz_mem j)
    calc |q.eval (z j)| * ∏ r ∈ Finset.univ.erase j, |(t - z r) / (z j - z r)|
        ≤ S * (((d : ℝ) * (k + 1)) ^ d / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ)) :=
          mul_le_mul hqj hprod_le (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) hS
      _ = S * ((d : ℝ) * (k + 1)) ^ d * (1 / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ)) := by
          ring
  refine hsum_le.trans ?_
  have hsum_inv : ∑ j : Fin (d + 1),
      (1 : ℝ) / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
      (2 : ℝ) ^ d / (d.factorial : ℝ) := by
    have hch : ∀ j : Fin (d + 1),
        (1 : ℝ) / ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
        (d.choose j.1 : ℝ) / (d.factorial : ℝ) := fun j ↦ by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ j.2)
      have hcast : (d.choose j.1 : ℝ) * ((j.1.factorial * (d - j.1).factorial : ℕ) : ℝ) =
          (d.factorial : ℝ) := by
        exact_mod_cast (by linarith [mul_assoc (d.choose j.1) j.1.factorial (d - j.1).factorial] :
          d.choose j.1 * (j.1.factorial * (d - j.1).factorial) = d.factorial)
      rw [div_eq_div_iff (by positivity) (by positivity)]; linarith
    simp_rw [hch, ← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k ↦ (d.choose k : ℝ))]
    congr 1; exact_mod_cast Nat.sum_range_choose d
  rw [hsum_inv]
  have hpow_d : (d : ℝ) ^ d / (d.factorial : ℝ) ≤ (Real.exp 1) ^ d := by
    have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg d) (d + 1)
    have hterm := (Finset.single_le_sum (f := fun j ↦ (d : ℝ) ^ j / (j.factorial : ℝ))
      (fun _ _ ↦ by positivity) (Finset.mem_range.2 (Nat.lt_succ_self d))).trans hsum
    rw [← mul_one (d : ℝ), Real.exp_nat_mul] at hterm
    simpa using hterm
  calc S * ((d : ℝ) * (k + 1)) ^ d * ((2 : ℝ) ^ d / (d.factorial : ℝ))
      = S * (2 * (k + 1)) ^ d * ((d : ℝ) ^ d / (d.factorial : ℝ)) := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ S * (2 * (k + 1)) ^ d * (Real.exp 1) ^ d :=
        mul_le_mul_of_nonneg_left hpow_d (by positivity)
    _ = S * (2 * Real.exp 1 * (k + 1)) ^ d := by rw [mul_pow, mul_pow]; ring

/-- Elementary exponential series bound:
`∑' k : ℕ, ((k + 2 : ℝ)) ^ m * exp (-k) ≤ 3 * (2 * m + 4) ^ m` for `m : ℕ`. -/
private theorem tsum_pow_mul_exp_neg_le (m : ℕ) :
    Summable (fun k : ℕ ↦ ((k + 2 : ℝ)) ^ m * Real.exp (-(k : ℝ))) ∧
    (∑' k : ℕ, ((k + 2 : ℝ)) ^ m * Real.exp (-(k : ℝ))) ≤ 3 * ((2 * (m : ℝ) + 4) ^ m) := by
  have hgeom_ratio : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  have hpt : ∀ k : ℕ, ((k + 2 : ℝ)) ^ m * Real.exp (-(k : ℝ)) ≤
      ((2 * (m : ℝ) + 4) ^ m) * (Real.exp (-(1 / 2 : ℝ))) ^ k := by
    intro k
    have hsplit : Real.exp (-(k : ℝ)) =
        Real.exp (-(k : ℝ) / 2) * (Real.exp (-(1 / 2 : ℝ))) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    -- Show `(k + 2)^m * exp(-k/2) ≤ (2m + 4)^m`, i.e., `(k + 2) * exp(-k / (2m)) ≤ 2m + 4`
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add]
      exact Real.exp_le_one_iff.2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
    · have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
      have hexp_half : Real.exp (-(k : ℝ) / 2) = (Real.exp (-(k : ℝ) / (2 * (m : ℝ)))) ^ m := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp [hm_pos.ne']
      rw [hexp_half, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ m
      -- Show `(k + 2) ≤ (2m + 4) * exp(k / (2m))`: by `1 + x ≤ exp x`, `exp(k/(2m)) ≥ 1 + k/(2m)`
      have h1 : 1 + (k : ℝ) / (2 * (m : ℝ)) ≤ Real.exp ((k : ℝ) / (2 * (m : ℝ))) := by
        linarith [Real.add_one_le_exp ((k : ℝ) / (2 * (m : ℝ)))]
      have h2 : (k : ℝ) + 2 ≤ (2 * (m : ℝ) + 4) * Real.exp ((k : ℝ) / (2 * (m : ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 4)
        have hexp : (2 * (m : ℝ) + 4) * (1 + (k : ℝ) / (2 * (m : ℝ))) =
            2 * (m : ℝ) + 4 + (k : ℝ) + 2 * (k : ℝ) / (m : ℝ) := by
          field_simp [hm_pos.ne']; ring
        have : (0 : ℝ) ≤ 2 * (k : ℝ) / (m : ℝ) := by positivity
        linarith
      rw [neg_div, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      exact h2
  have hsum_g : Summable (fun k : ℕ ↦ ((2 * (m : ℝ) + 4) ^ m) * (Real.exp (-(1 / 2 : ℝ))) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hgeom_ratio).mul_left _
  have hsum : Summable (fun k : ℕ ↦ ((k + 2 : ℝ)) ^ m * Real.exp (-(k : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity) hpt hsum_g
  refine ⟨hsum, ?_⟩
  refine (hsum.tsum_le_tsum hpt hsum_g).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hgeom_ratio]
  have he_le : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    -- `exp(1/2) ≥ 1 + 1/2 = 3/2`, so `exp(-1/2) ≤ 2/3`
    have h1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hinv : (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc (2 * (m : ℝ) + 4) ^ m * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹
      ≤ (2 * (m : ℝ) + 4) ^ m * 3 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 3 * (2 * (m : ℝ) + 4) ^ m := mul_comm _ _

/-- **1D Log-Concave Carbery–Wright inequality**: for any `d ≥ 1`, real polynomial `q` of degree at
most `d`, compactly supported bounded nonnegative log-concave density `w : ℝ → ℝ` with
`Z = ∫ w > 0` and `0 < ∫ q² w`, and `α > 0`,
`(∫ t in {|q(t)| ≤ α}, w t) / Z ≤ 3000000 * d * (α / √((∫ t, (q.eval t)² * w t) / Z))^{1/d}`. -/
theorem carbery_wright_1d_logConcave {d : ℕ} (hd : 1 ≤ d) (q : Polynomial ℝ) (hq : q.natDegree ≤ d)
    {w : ℝ → ℝ} {R M : ℝ} (_hR : 0 < R) (hw_meas : Measurable w) (hw0 : ∀ t, 0 ≤ w t)
    (hwM : ∀ t, w t ≤ M) (hw_supp : ∀ t, R < |t| → w t = 0)
    (hw_lc : ∀ x y θ, 0 < θ → θ < 1 → w x ^ (1 - θ) * w y ^ θ ≤ w ((1 - θ) * x + θ * y))
    (hZ : 0 < ∫ t, w t) (hq2 : 0 < ∫ t, q.eval t ^ 2 * w t) {α : ℝ} (hα : 0 < α) :
    (∫ t in {t : ℝ | |q.eval t| ≤ α}, w t) / (∫ t, w t) ≤
      3000000 * (d : ℝ) * (α / √((∫ t, q.eval t ^ 2 * w t) / (∫ t, w t))) ^ (1 / (d : ℝ)) := by
  set Z : ℝ := ∫ t, w t
  set Mw : ℝ := sSup (Set.range w)
  have hw_bdd : BddAbove (Set.range w) := ⟨M, by rintro _ ⟨t, rfl⟩; exact hwM t⟩
  have hMw_pos : 0 < Mw := by
    by_contra hle; push Not at hle
    have h0 : ∀ t, w t = 0 := fun t ↦ le_antisymm ((le_csSup hw_bdd ⟨t, rfl⟩).trans hle) (hw0 t)
    have : Z = 0 := by simp [Z, h0]
    linarith
  have hw_le_Mw : ∀ t, w t ≤ Mw := fun t ↦ le_csSup hw_bdd ⟨t, rfl⟩
  -- Pick near-mode `x₀` with `Mw / 2 ≤ w x₀`
  obtain ⟨_, ⟨x₀, rfl⟩, hx₀⟩ : ∃ y ∈ Set.range w, Mw / 2 < y :=
    exists_lt_of_lt_csSup ⟨w 0, ⟨0, rfl⟩⟩ (by linarith)
  -- Level sets `I_k = {t | exp(-k) * (Mw / 2) ≤ w t}` for `k ≥ 1`
  let I : ℕ → Set ℝ := fun k ↦ {t : ℝ | Real.exp (-(k : ℝ)) * (Mw / 2) ≤ w t}
  have hI_conv : ∀ k : ℕ, Convex ℝ (I k) := by
    intro k x hx y hy a b ha hb hab
    rcases ha.eq_or_lt with rfl | ha0
    · simp only [zero_smul, zero_add] at hab ⊢; rw [show b = 1 by linarith, one_smul]; exact hy
    rcases hb.eq_or_lt with rfl | hb0
    · simp only [zero_smul, add_zero] at hab ⊢; rw [show a = 1 by linarith, one_smul]; exact hx
    have hb1 : b < 1 := by linarith
    have ha_eq : a = 1 - b := by linarith
    rw [ha_eq]
    simp only [I, Set.mem_ofPred_eq, smul_eq_mul] at hx hy ⊢
    have hlc := hw_lc x y b hb0 hb1
    have hpos : 0 < Real.exp (-(k : ℝ)) * (Mw / 2) := by positivity
    calc Real.exp (-(k : ℝ)) * (Mw / 2)
        = (Real.exp (-(k : ℝ)) * (Mw / 2)) ^ (1 - b + b) := by rw [sub_add_cancel, Real.rpow_one]
      _ = (Real.exp (-(k : ℝ)) * (Mw / 2)) ^ (1 - b) * (Real.exp (-(k : ℝ)) * (Mw / 2)) ^ b :=
          Real.rpow_add hpos _ _
      _ ≤ w x ^ (1 - b) * w y ^ b :=
          mul_le_mul (Real.rpow_le_rpow hpos.le hx (by linarith))
            (Real.rpow_le_rpow hpos.le hy hb0.le) (Real.rpow_nonneg hpos.le _)
            (Real.rpow_nonneg (hw0 x) _)
      _ ≤ w ((1 - b) * x + b * y) := hlc
  have hI_sub_R : ∀ k : ℕ, I k ⊆ Set.Icc (-R) R := by
    intro k t ht
    by_contra hnot
    have hgt : R < |t| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      rw [lt_abs]; rcases hnot with h1 | h2
      · exact Or.inr (by linarith)
      · exact Or.inl h2
    have h0 := hw_supp t hgt
    simp only [I, Set.mem_ofPred_eq, h0] at ht
    have hpos : 0 < Real.exp (-(k : ℝ)) * (Mw / 2) := by positivity
    linarith
  have hx₀_mem : ∀ k : ℕ, x₀ ∈ I k := fun k ↦ by
    simp only [I, Set.mem_ofPred_eq]
    have h1 : Real.exp (-(k : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
    nlinarith
  -- Key dilation: for `k ≥ 1`, `t ∈ I k → (1 - 1/k) * x₀ + (1/k) * t ∈ I 1`
  have hI_dil : ∀ {k : ℕ}, 1 ≤ k → ∀ t ∈ I k,
      (1 - 1 / (k : ℝ)) * x₀ + (1 / (k : ℝ)) * t ∈ I 1 := by
    intro k hk t ht
    rcases eq_or_lt_of_le hk with rfl | hk2
    · simpa using ht
    · have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 (by omega)
      have hθ0 : 0 < 1 / (k : ℝ) := by positivity
      have hθ1 : 1 / (k : ℝ) < 1 := by
        rw [div_lt_one hk_pos]; exact_mod_cast hk2
      have hlc := hw_lc x₀ t (1 / (k : ℝ)) hθ0 hθ1
      simp only [I, Set.mem_ofPred_eq, Nat.cast_one] at ht ⊢
      have h1 : (Mw / 2) ^ (1 - 1 / (k : ℝ)) *
            (Real.exp (-(k : ℝ)) * (Mw / 2)) ^ (1 / (k : ℝ)) ≤
          w x₀ ^ (1 - 1 / (k : ℝ)) * w t ^ (1 / (k : ℝ)) :=
        mul_le_mul (Real.rpow_le_rpow (by positivity) hx₀.le (by linarith))
          (Real.rpow_le_rpow (by positivity) ht hθ0.le)
          (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (hw0 x₀) _)
      have hsimp : (Mw / 2) ^ (1 - 1 / (k : ℝ)) *
            (Real.exp (-(k : ℝ)) * (Mw / 2)) ^ (1 / (k : ℝ)) =
          Real.exp (-1) * (Mw / 2) := by
        rw [Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul,
          mul_left_comm, ← Real.rpow_add (by positivity), sub_add_cancel, Real.rpow_one]
        congr 1; congr 1; field_simp [hk_pos.ne']
      linarith
  -- Interval bounds `a_k = sInf (I k)`, `b_k = sSup (I k)`, `L_k = b_k - a_k`
  let aI : ℕ → ℝ := fun k ↦ sInf (I k)
  let bI : ℕ → ℝ := fun k ↦ sSup (I k)
  have hI_Icc : ∀ k : ℕ, I k ⊆ Set.Icc (aI k) (bI k) := fun k t ht ↦
    ⟨csInf_le ⟨-R, fun _ hu ↦ (hI_sub_R k hu).1⟩ ht,
     le_csSup ⟨R, fun _ hu ↦ (hI_sub_R k hu).2⟩ ht⟩
  have hI_Ioo : ∀ k : ℕ, Set.Ioo (aI k) (bI k) ⊆ I k := by
    intro k t ⟨h1, h2⟩
    obtain ⟨u, huI, hu_lt⟩ := exists_lt_of_csInf_lt ⟨x₀, hx₀_mem k⟩ h1
    obtain ⟨v, hvI, hv_gt⟩ := exists_lt_of_lt_csSup ⟨x₀, hx₀_mem k⟩ h2
    exact (hI_conv k).ordConnected.out huI hvI ⟨hu_lt.le, hv_gt.le⟩
  have hI_vol : ∀ k : ℕ, volume.real (I k) = bI k - aI k := by
    intro k
    have hab : aI k ≤ bI k :=
      le_trans (csInf_le ⟨-R, fun _ hu ↦ (hI_sub_R k hu).1⟩ (hx₀_mem k))
        (le_csSup ⟨R, fun _ hu ↦ (hI_sub_R k hu).2⟩ (hx₀_mem k))
    have h1 : volume.real (Set.Ioo (aI k) (bI k)) ≤ volume.real (I k) :=
      measureReal_mono (hI_Ioo k)
        (ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono (hI_sub_R k)))
    have h2 : volume.real (I k) ≤ volume.real (Set.Icc (aI k) (bI k)) :=
      measureReal_mono (hI_Icc k) (by simp [Real.volume_Icc])
    have hv1 : volume.real (Set.Ioo (aI k) (bI k)) = bI k - aI k := by
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
    have hv2 : volume.real (Set.Icc (aI k) (bI k)) = bI k - aI k := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
    linarith
  set L1 : ℝ := bI 1 - aI 1
  have hIk_bound : ∀ {k : ℕ}, 1 ≤ k → ∀ t ∈ I k, |t - x₀| ≤ (k : ℝ) * L1 := by
    intro k hk t ht
    have hmem := hI_dil hk t ht
    have hIcc1 := hI_Icc 1 hmem
    have hx01 := hI_Icc 1 (hx₀_mem 1)
    have hdiff : |(1 - 1 / (k : ℝ)) * x₀ + (1 / (k : ℝ)) * t - x₀| ≤ L1 := by
      rw [abs_le]; dsimp [L1]; constructor <;> linarith [hIcc1.1, hIcc1.2, hx01.1, hx01.2]
    have heq : (1 - 1 / (k : ℝ)) * x₀ + (1 / (k : ℝ)) * t - x₀ = (t - x₀) / (k : ℝ) := by
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      field_simp [hk0]; ring
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
    rw [heq, abs_div, abs_of_pos hk_pos, div_le_iff₀ hk_pos] at hdiff
    linarith
  have hLk_le : ∀ {k : ℕ}, 1 ≤ k → bI k - aI k ≤ (k : ℝ) * L1 := by
    intro k hk
    -- Show `bI k - x₀ ≤ k * (bI 1 - x₀)` and `x₀ - aI k ≤ k * (x₀ - aI 1)`
    have hhi : bI k ≤ x₀ + (k : ℝ) * (bI 1 - x₀) := by
      refine csSup_le ⟨x₀, hx₀_mem k⟩ fun t ht ↦ ?_
      have hmem := (hI_Icc 1 (hI_dil hk t ht)).2
      have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
      have := mul_le_mul_of_nonneg_left hmem hk0.le
      have hsimp : (k : ℝ) * ((1 - 1 / (k : ℝ)) * x₀ + 1 / (k : ℝ) * t) =
          ((k : ℝ) - 1) * x₀ + t := by field_simp [hk0.ne']
      linarith
    have hlo : x₀ - (k : ℝ) * (x₀ - aI 1) ≤ aI k := by
      refine le_csInf ⟨x₀, hx₀_mem k⟩ fun t ht ↦ ?_
      have hmem := (hI_Icc 1 (hI_dil hk t ht)).1
      have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
      have := mul_le_mul_of_nonneg_left hmem hk0.le
      have hsimp : (k : ℝ) * ((1 - 1 / (k : ℝ)) * x₀ + 1 / (k : ℝ) * t) =
          ((k : ℝ) - 1) * x₀ + t := by field_simp [hk0.ne']
      linarith
    dsimp [L1]; linarith
  -- Integrability of `w` and `q² w`
  have hw_int : Integrable w volume := by
    have hind_int : Integrable ((Set.Icc (-R) R).indicator fun _ : ℝ ↦ M) volume :=
      (integrableOn_const (by simp [Real.volume_Icc] : volume (Set.Icc (-R) R) ≠
        ⊤)).integrable_indicator
        measurableSet_Icc
    refine Integrable.mono' hind_int hw_meas.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 t)]
    by_cases ht : t ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem ht]; exact hwM t
    · rw [Set.indicator_of_notMem ht]
      have hgt : R < |t| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rw [lt_abs]; rcases ht with h1 | h2
        · exact Or.inr (by linarith)
        · exact Or.inl h2
      rw [hw_supp t hgt]
  -- Partition `{w > 0}` into `A_0 = {w > e^{-1} (Mw/2)} ⊆ I 1` and
  -- `A_k = {e^{-(k+1)} (Mw/2) < w ≤ e^{-k} (Mw/2)} ⊆ I (k+1)` for `k ≥ 1`
  let A : ℕ → Set ℝ := fun k ↦
    if k = 0 then {t | Real.exp (-1) * (Mw / 2) < w t}
    else {t | Real.exp (-((k + 1 : ℕ) : ℝ)) * (Mw / 2) < w t ∧
              w t ≤ Real.exp (-(k : ℝ)) * (Mw / 2)}
  have hA_meas : ∀ k, MeasurableSet (A k) := fun k ↦ by
    dsimp [A]; split_ifs
    · exact measurableSet_lt measurable_const hw_meas
    · exact (measurableSet_lt measurable_const hw_meas).inter
        (measurableSet_le hw_meas measurable_const)
  have hA_disj : Pairwise (Function.onFun Disjoint A) := by
    intro j k hjk
    rw [Function.onFun, Set.disjoint_left]
    intro t htj htk
    wlog hlt : j < k generalizing j k
    · exact this hjk.symm htk htj (lt_of_le_of_ne (not_lt.1 hlt) hjk.symm)
    have hk0 : k ≠ 0 := by omega
    have htk' : Real.exp (-((k + 1 : ℕ) : ℝ)) * (Mw / 2) < w t ∧
        w t ≤ Real.exp (-(k : ℝ)) * (Mw / 2) := by
      simpa [A, hk0] using htk
    by_cases hj0 : j = 0
    · have htj' : Real.exp (-1) * (Mw / 2) < w t := by simpa [A, hj0] using htj
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hexp : Real.exp (-(k : ℝ)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      nlinarith
    · have htj' : Real.exp (-((j + 1 : ℕ) : ℝ)) * (Mw / 2) < w t ∧
          w t ≤ Real.exp (-(j : ℝ)) * (Mw / 2) := by simpa [A, hj0] using htj
      have hjk1 : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show j + 1 ≤ k by omega)
      have hexp : Real.exp (-(k : ℝ)) ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.2 (by linarith)
      nlinarith
  have hA_sub : ∀ k, A k ⊆ I (k + 1) := by
    intro k t ht
    dsimp [A, I] at ht ⊢
    split_ifs at ht with hk0
    · subst hk0; simpa [Nat.cast_one] using ht.le
    · exact ht.1.le
  have hA_upper : ∀ k, ∀ t ∈ A k, w t ≤ Real.exp (-(k : ℝ)) * Mw := by
    intro k t ht
    dsimp [A] at ht
    split_ifs at ht with hk0
    · subst hk0; simpa using hw_le_Mw t
    · have h2 : w t ≤ Real.exp (-(k : ℝ)) * (Mw / 2) := ht.2
      nlinarith [Real.exp_pos (-(k : ℝ))]
  have hA_cover : {t | 0 < w t} = ⋃ k : ℕ, A k := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hpos
      by_cases h0 : Real.exp (-1) * (Mw / 2) < w t
      · exact ⟨0, by simp [A, h0]⟩
      · push Not at h0
        -- Let `k = Nat.floor (Real.log ((Mw / 2) / w t))` (with `k ≥ 1`)
        have hratio : Real.exp 1 ≤ (Mw / 2) / w t := by
          rw [le_div_iff₀ hpos]
          have := mul_le_mul_of_nonneg_left h0 (Real.exp_pos 1).le
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
          linarith
        have hlog1 : 1 ≤ Real.log ((Mw / 2) / w t) := by
          have := Real.log_le_log (Real.exp_pos 1) hratio
          rwa [Real.log_exp] at this
        let k : ℕ := Nat.floor (Real.log ((Mw / 2) / w t))
        have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hlog1)
        refine ⟨k, ?_⟩
        simp only [A, ite_eq_right (show k ≠ 0 by omega), Set.mem_ofPred_eq]
        constructor
        · have hlt : Real.log ((Mw / 2) / w t) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
          have hexp := Real.exp_lt_exp.2 hlt
          rw [Real.exp_log (div_pos (by positivity) hpos)] at hexp
          have hmul := mul_lt_mul_of_pos_left hexp (Real.exp_pos (-((k + 1 : ℕ) : ℝ)))
          rw [← Real.exp_add] at hmul
          have hcancel : -((k + 1 : ℕ) : ℝ) + ((k : ℝ) + 1) = 0 := by push_cast; ring
          rw [hcancel, Real.exp_zero] at hmul
          rw [mul_div_assoc', div_lt_one hpos] at hmul
          exact hmul
        · have hle : (k : ℝ) ≤ Real.log ((Mw / 2) / w t) := Nat.floor_le (by linarith)
          have hexp := Real.exp_le_exp.2 hle
          rw [Real.exp_log (div_pos (by positivity) hpos)] at hexp
          have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-(k : ℝ))).le
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
          rw [mul_div_assoc', le_div_iff₀ hpos] at hmul
          linarith
    · rintro ⟨k, htk⟩
      have hmem := hA_sub k htk
      simp only [I, Set.mem_ofPred_eq] at hmem
      exact lt_of_lt_of_le (by positivity) hmem
  -- Prove `L1 > 0` and `Mw * L1 ≤ 2 e * Z`
  have hL1_pos : 0 < L1 := by
    by_contra hle; push Not at hle
    have hI_null : ∀ k : ℕ, volume (I (k + 1)) = 0 := fun k ↦ by
      have hv := hI_vol (k + 1)
      have hle0 : bI (k + 1) - aI (k + 1) ≤ 0 :=
        (hLk_le (Nat.succ_le_succ (Nat.zero_le k))).trans
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hle)
      have hfin : volume (I (k + 1)) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono (hI_sub_R (k + 1)))
      have hreal0 : volume.real (I (k + 1)) = 0 := le_antisymm (hv ▸ hle0) measureReal_nonneg
      exact (ENNReal.toReal_eq_zero_iff _).1 hreal0 |>.resolve_right hfin
    have hpos_null : volume {t | 0 < w t} = 0 := by
      rw [hA_cover]
      exact measure_iUnion_null fun k ↦ measure_mono_null (hA_sub k) (hI_null k)
    have hwae : w =ᵐ[volume] 0 := by
      filter_upwards [compl_mem_ae_iff.2 hpos_null] with t ht
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at ht
      exact le_antisymm ht (hw0 t)
    have : Z = 0 := by rw [show Z = ∫ t, w t from rfl, integral_congr_ae hwae]; simp
    linarith
  have hMwL1_le : Mw * L1 ≤ 2 * Real.exp 1 * Z := by
    have hsub : ∫ t in I 1, Real.exp (-1) * (Mw / 2) ≤ Z := by
      calc ∫ t in I 1, Real.exp (-1) * (Mw / 2)
          ≤ ∫ t in I 1, w t := setIntegral_mono_on
            (integrableOn_const (ne_top_of_le_ne_top (by simp [Real.volume_Icc])
              (measure_mono (hI_sub_R 1))))
            hw_int.integrableOn (measurableSet_le measurable_const hw_meas)
            fun t ht ↦ by simpa [I] using ht
        _ ≤ ∫ t, w t := setIntegral_le_integral hw_int (ae_of_all _ hw0)
    rw [setIntegral_const, smul_eq_mul, hI_vol 1] at hsub
    have hmul := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1)
    have hcancel : 2 * Real.exp 1 * (L1 * (Real.exp (-1) * (Mw / 2))) = Mw * L1 := by
      calc 2 * Real.exp 1 * (L1 * (Real.exp (-1) * (Mw / 2)))
          = (Real.exp 1 * Real.exp (-1)) * (Mw * L1) := by ring
        _ = Mw * L1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    linarith
  -- Let `S = sup_{t ∈ [aI 1, bI 1]} |q.eval t|`; show `S > 0` and bound `∫ q² w` in terms of `S²`
  have hab1 : aI 1 < bI 1 := by dsimp [L1] at hL1_pos; linarith
  obtain ⟨tS, htS_mem, htS_max⟩ := (isCompact_Icc (a := aI 1) (b := bI 1)).exists_isMaxOn
    ⟨aI 1, ⟨le_rfl, hab1.le⟩⟩ q.continuous.abs.continuousOn
  set S : ℝ := |q.eval tS|
  have hS_bd : ∀ t ∈ Set.Icc (aI 1) (bI 1), |q.eval t| ≤ S := fun t ht ↦ htS_max ht
  have hS0 : 0 ≤ S := abs_nonneg _
  have hq2_int : Integrable (fun t ↦ q.eval t ^ 2 * w t) volume := by
    obtain ⟨Bq, hBq⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
      (q.continuous.pow 2).continuousOn
    refine Integrable.mono' (hw_int.const_mul (max Bq 0))
      ((q.continuous.pow 2).measurable.mul hw_meas).aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hw0 t)]
    by_cases ht : t ∈ Set.Icc (-R) R
    · have h1 := hBq t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h1
      exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (hw0 t)
    · have hgt : R < |t| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        rw [lt_abs]; rcases ht with h1 | h2
        · exact Or.inr (by linarith)
        · exact Or.inl h2
      rw [hw_supp t hgt, mul_zero, mul_zero]
  -- Bound `∫ q² w` by summing over `A k`
  have hL2_bound : (∫ t, q.eval t ^ 2 * w t) / Z ≤
      (6 * Real.exp 1) * (2 * Real.exp 1) ^ (2 * d) * ((4 * (d : ℝ) + 6) ^ (2 * d +
        1)) * S ^ 2 := by
    have hdom : ∫ t, q.eval t ^ 2 * w t = ∑' k : ℕ, ∫ t in A k, q.eval t ^ 2 * w t := by
      have hpos_eq : ∫ t, q.eval t ^ 2 * w t = ∫ t in {t | 0 < w t}, q.eval t ^ 2 * w t := by
        rw [← integral_indicator (measurableSet_lt measurable_const hw_meas)]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        by_cases h : 0 < w t
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]; dsimp only
          rw [le_antisymm (not_lt.1 h) (hw0 t), mul_zero]
      rw [hpos_eq, hA_cover]
      exact integral_iUnion hA_meas hA_disj hq2_int.integrableOn
    have hterm_k : ∀ k : ℕ, ∫ t in A k, q.eval t ^ 2 * w t ≤
        (Mw * L1 * S ^ 2 * (2 * Real.exp 1) ^ (2 * d)) *
          (((k + 2 : ℝ)) ^ (2 * d + 1) * Real.exp (-(k : ℝ))) := by
      intro k
      have hpt : ∀ t ∈ A k, q.eval t ^ 2 * w t ≤
          (S * (2 * Real.exp 1 * ((k + 1 : ℕ) + 1 : ℝ)) ^ d) ^ 2 * (Real.exp (-(k : ℝ)) * Mw) := by
        intro t ht
        have hI := hA_sub k ht
        have hdil := hIk_bound (Nat.succ_le_succ (Nat.zero_le k)) t hI
        have hqle := abs_eval_le_of_dilated_Icc hd q hq hab1 (hI_Icc 1 (hx₀_mem 1)) hS0 hS_bd
          (Nat.cast_nonneg (k + 1)) hdil
        have hsq : q.eval t ^ 2 ≤ (S * (2 * Real.exp 1 * ((k + 1 : ℕ) + 1 : ℝ)) ^ d) ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hqle 2
        exact mul_le_mul hsq (hA_upper k t ht) (hw0 t) (sq_nonneg _)
      have hA_fin : volume (A k) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp [Real.volume_Icc])
          (measure_mono ((hA_sub k).trans (hI_sub_R (k + 1))))
      have hvolA : volume.real (A k) ≤ ((k + 1 : ℕ) : ℝ) * L1 := by
        calc volume.real (A k) ≤ volume.real (I (k + 1)) :=
              measureReal_mono (hA_sub k) (ne_top_of_le_ne_top (by simp [Real.volume_Icc])
                (measure_mono (hI_sub_R (k + 1))))
          _ = bI (k + 1) - aI (k + 1) := hI_vol (k + 1)
          _ ≤ ((k + 1 : ℕ) : ℝ) * L1 := hLk_le (Nat.succ_le_succ (Nat.zero_le k))
      have hint_le : ∫ t in A k, q.eval t ^ 2 * w t ≤
          volume.real (A k) *
            ((S * (2 * Real.exp 1 * ((k + 1 : ℕ) + 1 : ℝ)) ^ d) ^ 2 *
              (Real.exp (-(k : ℝ)) * Mw)) := by
        have h := setIntegral_mono_on hq2_int.integrableOn (integrableOn_const hA_fin)
          (hA_meas k) hpt
        simpa [setIntegral_const, smul_eq_mul] using h
      refine hint_le.trans ?_
      have hk_le : ((k + 1 : ℕ) : ℝ) ≤ (k + 2 : ℝ) := by push_cast; linarith
      have hk2_eq : ((k + 1 : ℕ) + 1 : ℝ) = (k + 2 : ℝ) := by push_cast; ring
      rw [hk2_eq]
      calc volume.real (A k) *
            ((S * (2 * Real.exp 1 * (k + 2 : ℝ)) ^ d) ^ 2 * (Real.exp (-(k : ℝ)) * Mw))
          ≤ (((k + 1 : ℕ) : ℝ) * L1) *
            ((S * (2 * Real.exp 1 * (k + 2 : ℝ)) ^ d) ^ 2 * (Real.exp (-(k : ℝ)) * Mw)) :=
            mul_le_mul_of_nonneg_right hvolA (by positivity)
        _ ≤ ((k + 2 : ℝ) * L1) *
            ((S * (2 * Real.exp 1 * (k + 2 : ℝ)) ^ d) ^ 2 * (Real.exp (-(k : ℝ)) * Mw)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk_le hL1_pos.le) (by positivity)
        _ = (Mw * L1 * S ^ 2 * (2 * Real.exp 1) ^ (2 * d)) *
              ((k + 2 : ℝ) ^ (2 * d + 1) * Real.exp (-(k : ℝ))) := by
            rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm d 2, pow_succ]; ring
    obtain ⟨hsum_pow, htsum_le⟩ := tsum_pow_mul_exp_neg_le (2 * d + 1)
    have hsum_lhs : Summable (fun k : ℕ ↦ ∫ t in A k, q.eval t ^ 2 * w t) :=
      Summable.of_nonneg_of_le
        (fun _ ↦ setIntegral_nonneg (hA_meas _) fun t _ ↦ mul_nonneg (sq_nonneg _) (hw0 t))
        hterm_k (hsum_pow.mul_left _)
    have htot := hsum_lhs.tsum_le_tsum hterm_k (hsum_pow.mul_left _)
    rw [← hdom, tsum_mul_left] at htot
    have hle1 : ∫ t, q.eval t ^ 2 * w t ≤
        (Mw * L1 * S ^ 2 * (2 * Real.exp 1) ^ (2 * d)) *
          (3 * ((2 * ((2 * d + 1 : ℕ) : ℝ) + 4) ^ (2 * d + 1))) :=
      htot.trans (mul_le_mul_of_nonneg_left htsum_le (by positivity))
    have hcast : 2 * ((2 * d + 1 : ℕ) : ℝ) + 4 = 4 * (d : ℝ) + 6 := by push_cast; ring
    rw [hcast] at hle1
    rw [div_le_iff₀ hZ]
    calc ∫ t, q.eval t ^ 2 * w t
        ≤ (Mw * L1) * (3 * (2 * Real.exp 1) ^ (2 * d) * (4 * (d : ℝ) + 6) ^ (2 * d +
          1) * S ^ 2) := by
          linarith
      _ ≤ (2 * Real.exp 1 * Z) *
            (3 * (2 * Real.exp 1) ^ (2 * d) * (4 * (d : ℝ) + 6) ^ (2 * d + 1) * S ^ 2) :=
          mul_le_mul_of_nonneg_right hMwL1_le (by positivity)
      _ = 6 * Real.exp 1 * (2 * Real.exp 1) ^ (2 * d) * (4 * (d : ℝ) + 6) ^ (2 * d +
        1) * S ^ 2 * Z := by
          ring
  -- Deduce `S > 0` from `hq2 > 0`
  have hS_pos : 0 < S := by
    rcases hS0.eq_or_lt with h0 | hpos
    · rw [← h0, zero_pow (by norm_num), mul_zero] at hL2_bound
      linarith [div_pos hq2 hZ]
    · exact hpos
  -- Bound `(∫_{|q| ≤ α} w) / Z` by summing Remez (`remez_1d_Icc_general`) over `A k ⊆ I (k+1)`
  let E : Set ℝ := {t : ℝ | |q.eval t| ≤ α}
  have hE_meas : MeasurableSet E := isClosed_le q.continuous.abs continuous_const |>.measurableSet
  have hprob_S : (∫ t in E, w t) / Z ≤ 72 * Real.exp 3 * (α / S) ^ (1 / (d : ℝ)) := by
    have hdom : ∫ t in E, w t = ∑' k : ℕ, ∫ t in E ∩ A k, w t := by
      have hpos_eq : ∫ t in E, w t = ∫ t in E ∩ {t | 0 < w t}, w t := by
        rw [← integral_indicator hE_meas,
          ← integral_indicator (hE_meas.inter (measurableSet_lt measurable_const hw_meas))]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        by_cases htE : t ∈ E
        · by_cases hpos : 0 < w t
          · simp [Set.indicator, htE, hpos]
          · simp [Set.indicator, htE, le_antisymm (not_lt.1 hpos) (hw0 t)]
        · simp [Set.indicator, htE]
      rw [hpos_eq, hA_cover, Set.inter_iUnion]
      exact integral_iUnion (fun k ↦ hE_meas.inter (hA_meas k))
        (fun j k hjk ↦ (hA_disj hjk).mono Set.inter_subset_right Set.inter_subset_right)
        hw_int.integrableOn
    have hterm_k : ∀ k : ℕ, ∫ t in E ∩ A k, w t ≤
        (Mw * L1 * (2 * Real.exp 2) * (α / S) ^ (1 / (d : ℝ))) *
          (((k + 2 : ℝ)) ^ 1 * Real.exp (-(k : ℝ))) := by
      intro k
      have hab_k : aI (k + 1) < bI (k + 1) := by
        have hsub1 : I 1 ⊆ I (k + 1) := fun t ht ↦ by
          simp only [I, Set.mem_ofPred_eq, Nat.cast_one] at ht ⊢
          have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
          have := Real.exp_le_exp.2 (show -((k + 1 : ℕ) : ℝ) ≤ -1 by linarith)
          nlinarith
        have hlo : aI (k + 1) ≤ aI 1 := csInf_le_csInf ⟨-R, fun _ hu ↦ (hI_sub_R _ hu).1⟩
          ⟨x₀, hx₀_mem 1⟩ hsub1
        have hhi : bI 1 ≤ bI (k + 1) := csSup_le_csSup ⟨R, fun _ hu ↦ (hI_sub_R _ hu).2⟩
          ⟨x₀, hx₀_mem 1⟩ hsub1
        linarith
      have hsup_k : ∃ u₀ ∈ Set.Icc (aI (k + 1)) (bI (k + 1)), S ≤ |q.eval u₀| := by
        have hsub1 : I 1 ⊆ I (k + 1) := fun t ht ↦ by
          simp only [I, Set.mem_ofPred_eq, Nat.cast_one] at ht ⊢
          have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
          have := Real.exp_le_exp.2 (show -((k + 1 : ℕ) : ℝ) ≤ -1 by linarith)
          nlinarith
        have hlo : aI (k + 1) ≤ aI 1 := csInf_le_csInf ⟨-R, fun _ hu ↦ (hI_sub_R _ hu).1⟩
          ⟨x₀, hx₀_mem 1⟩ hsub1
        have hhi : bI 1 ≤ bI (k + 1) := csSup_le_csSup ⟨R, fun _ hu ↦ (hI_sub_R _ hu).2⟩
          ⟨x₀, hx₀_mem 1⟩ hsub1
        exact ⟨tS, ⟨hlo.trans htS_mem.1, htS_mem.2.trans hhi⟩, le_rfl⟩
      have hrem := remez_1d_Icc_general hd q hq hab_k hα.le hS_pos hsup_k
      have hsub_EA : E ∩ A k ⊆ {t ∈ Set.Icc (aI (k + 1)) (bI (k + 1)) | |q.eval t| ≤ α} := by
        intro t ⟨htE, htA⟩
        exact ⟨hI_Icc (k + 1) (hA_sub k htA), htE⟩
      have hEA_fin : volume (E ∩ A k) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp [Real.volume_Icc])
          (measure_mono (Set.inter_subset_right.trans ((hA_sub k).trans (hI_sub_R (k + 1)))))
      have hvolEA : volume.real (E ∩ A k) ≤
          (bI (k + 1) - aI (k + 1)) * (2 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ))) :=
        (measureReal_mono hsub_EA (ne_top_of_le_ne_top (by simp [Real.volume_Icc])
          (measure_mono fun _ h ↦ h.1))).trans hrem
      have hint_le : ∫ t in E ∩ A k, w t ≤ volume.real (E ∩ A k) * (Real.exp (-(k : ℝ)) * Mw) := by
        have h := setIntegral_mono_on hw_int.integrableOn (integrableOn_const hEA_fin)
          (hE_meas.inter (hA_meas k)) fun t ht ↦ hA_upper k t ht.2
        simpa [setIntegral_const, smul_eq_mul] using h
      refine hint_le.trans ?_
      have hLk := hLk_le (Nat.succ_le_succ (Nat.zero_le k))
      have hk_le : ((k + 1 : ℕ) : ℝ) ≤ (k + 2 : ℝ) := by push_cast; linarith
      calc volume.real (E ∩ A k) * (Real.exp (-(k : ℝ)) * Mw)
          ≤ ((bI (k + 1) - aI (k + 1)) * (2 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ)))) *
              (Real.exp (-(k : ℝ)) * Mw) := mul_le_mul_of_nonneg_right hvolEA (by positivity)
        _ ≤ (((k + 1 : ℕ) : ℝ) * L1 * (2 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ)))) *
              (Real.exp (-(k : ℝ)) * Mw) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hLk (by positivity)) (by positivity)
        _ ≤ ((k + 2 : ℝ) * L1 * (2 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ)))) *
              (Real.exp (-(k : ℝ)) * Mw) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk_le hL1_pos.le)
                (by positivity)) (by positivity)
        _ = (Mw * L1 * (2 * Real.exp 2) * (α / S) ^ (1 / (d : ℝ))) *
              ((k + 2 : ℝ) ^ 1 * Real.exp (-(k : ℝ))) := by rw [pow_one]; ring
    obtain ⟨hsum1, htsum1⟩ := tsum_pow_mul_exp_neg_le 1
    have hsum_lhs : Summable (fun k : ℕ ↦ ∫ t in E ∩ A k, w t) :=
      Summable.of_nonneg_of_le (fun _ ↦ setIntegral_nonneg (hE_meas.inter (hA_meas _))
        fun _ _ ↦ hw0 _) hterm_k (hsum1.mul_left _)
    have htot := hsum_lhs.tsum_le_tsum hterm_k (hsum1.mul_left _)
    rw [← hdom, tsum_mul_left] at htot
    have h18 : (3 : ℝ) * (2 * (1 : ℕ) + 4) ^ 1 = 18 := by norm_num
    rw [h18] at htsum1
    rw [div_le_iff₀ hZ]
    have hle1 : ∫ t in E, w t ≤ (Mw * L1) * (36 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ))) := by
      have := htot.trans (mul_le_mul_of_nonneg_left htsum1 (by positivity))
      linarith
    have he3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
    calc ∫ t in E, w t
        ≤ (Mw * L1) * (36 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ))) := hle1
      _ ≤ (2 * Real.exp 1 * Z) * (36 * Real.exp 2 * (α / S) ^ (1 / (d : ℝ))) :=
          mul_le_mul_of_nonneg_right hMwL1_le (by positivity)
      _ = 72 * (Real.exp 1 * Real.exp 2) * (α / S) ^ (1 / (d : ℝ)) * Z := by ring
      _ = 72 * Real.exp 3 * (α / S) ^ (1 / (d : ℝ)) * Z := by rw [he3]
  -- Combine `hprob_S` with `hL2_bound` to replace `S` by `√((∫ q² w) / Z)`
  set N2 : ℝ := √((∫ t, q.eval t ^ 2 * w t) / Z)
  have hN2_pos : 0 < N2 := Real.sqrt_pos.2 (div_pos hq2 hZ)
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have he_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hN2_div_S : (N2 / S) ^ (1 / (d : ℝ)) ≤ 1500 * (d : ℝ) := by
    have hrat_sq : (N2 / S) ^ 2 ≤
        (6 * Real.exp 1) * (2 * Real.exp 1) ^ (2 * d) * (4 * (d : ℝ) + 6) ^ (2 * d + 1) := by
      rw [div_pow, Real.sq_sqrt (div_pos hq2 hZ).le, div_le_iff₀ (sq_pos_of_pos hS_pos)]
      exact hL2_bound
    -- Bound `(4 d + 6) ≤ 10 d` and `10 d ≤ 20^d`, so `(6 e) * (2 e)^{2d} * (4 d + 6)^{2d + 1} ≤
    -- (1500 d)^{2d}`
    have h4d6 : 4 * (d : ℝ) + 6 ≤ 10 * (d : ℝ) := by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hd_le_2pow : (d : ℝ) ≤ 2 ^ d := by
      have : d ≤ 2 ^ d := Nat.lt_two_pow_self.le
      exact_mod_cast this
    have h10d_le : 10 * (d : ℝ) ≤ 20 ^ d := by
      have h10 : (10 : ℝ) ≤ 10 ^ d := by
        calc (10 : ℝ) = 10 ^ 1 := (pow_one 10).symm
          _ ≤ 10 ^ d := pow_le_pow_right₀ (by norm_num) hd
      calc 10 * (d : ℝ) ≤ 10 ^ d * 2 ^ d :=
        mul_le_mul h10 hd_le_2pow (Nat.cast_nonneg d) (by positivity)
        _ = 20 ^ d := by rw [← mul_pow]; norm_num
    have h6e : 6 * Real.exp 1 ≤ 20 ^ d := by
      have h20 : (20 : ℝ) ≤ 20 ^ d := by
        calc (20 : ℝ) = 20 ^ 1 := (pow_one 20).symm
          _ ≤ 20 ^ d := pow_le_pow_right₀ (by norm_num) hd
      linarith
    have hpow2d : (N2 / S) ^ 2 ≤ (1500 * (d : ℝ)) ^ (2 * d) := by
      have h2e : (2 * Real.exp 1) ^ (2 * d) ≤ 6 ^ (2 * d) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (2 * d)
      have h4d_pow : (4 * (d : ℝ) + 6) ^ (2 * d + 1) ≤ (10 * (d : ℝ)) ^ (2 * d) * 20 ^ d := by
        rw [pow_succ]
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) h4d6 (2 * d))
          (h4d6.trans h10d_le) (by positivity) (by positivity)
      have hprod : (6 * Real.exp 1) * (2 * Real.exp 1) ^ (2 * d) * (4 * (d : ℝ) + 6) ^ (2 * d + 1) ≤
          (1500 * (d : ℝ)) ^ (2 * d) := by
        calc (6 * Real.exp 1) * (2 * Real.exp 1) ^ (2 * d) * (4 * (d : ℝ) + 6) ^ (2 * d + 1)
            ≤ 20 ^ d * 6 ^ (2 * d) * ((10 * (d : ℝ)) ^ (2 * d) * 20 ^ d) := by
              refine mul_le_mul (mul_le_mul h6e h2e (by positivity) (by positivity))
                h4d_pow (by positivity) (by positivity)
          _ = (20 * 20 * 6 ^ 2 * (10 * (d : ℝ)) ^ 2) ^ d := by
              simp only [mul_pow, ← pow_mul]; ring
          _ ≤ ((1500 * (d : ℝ)) ^ 2) ^ d := by
              refine pow_le_pow_left₀ (by positivity) ?_ d
              have : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
              nlinarith
          _ = (1500 * (d : ℝ)) ^ (2 * d) := by rw [← pow_mul]
      exact hrat_sq.trans hprod
    have hrt := Real.rpow_le_rpow (sq_nonneg _) hpow2d (by positivity : (0 : ℝ) ≤ 1 / (2 * (d : ℝ)))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hrt
    have hmul1 : (2 : ℝ) * (1 / (2 * (d : ℝ))) = 1 / (d : ℝ) := by field_simp [hd_pos.ne']
    have hmul2 : ((2 * d : ℕ) : ℝ) * (1 / (2 * (d : ℝ))) = 1 := by
      push_cast; field_simp [hd_pos.ne']
    rw [show ((2 : ℕ) : ℝ) = 2 from rfl, hmul1, hmul2, Real.rpow_one] at hrt
    exact hrt
  have hfactor : (α / S) ^ (1 / (d : ℝ)) = (N2 / S) ^ (1 / (d : ℝ)) * (α / N2) ^ (1 / (d : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp [hN2_pos.ne', hS_pos.ne']
  rw [hfactor] at hprob_S
  have he3_lt : 72 * Real.exp 3 ≤ 2000 := by
    have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have hpow : (Real.exp 1) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he_lt3.le 3
    linarith [show (3 : ℝ) ^ 3 = 27 by norm_num]
  calc (∫ t in E, w t) / Z
      ≤ 72 * Real.exp 3 * ((N2 / S) ^ (1 / (d : ℝ)) * (α / N2) ^ (1 / (d : ℝ))) := hprob_S
    _ ≤ 2000 * (1500 * (d : ℝ) * (α / N2) ^ (1 / (d : ℝ))) := by
        refine mul_le_mul he3_lt
          (mul_le_mul_of_nonneg_right hN2_div_S (by positivity))
          (by positivity) (by norm_num)
    _ = 3000000 * (d : ℝ) * (α / N2) ^ (1 / (d : ℝ)) := by ring

end CslibFrontier.Probability.Gaussian
