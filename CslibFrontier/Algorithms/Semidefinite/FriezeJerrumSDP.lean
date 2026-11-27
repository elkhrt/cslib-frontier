/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Foundations.Probability.Gaussian.Correlated
public import CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import CslibFrontier.Foundations.Probability.Gaussian.CDF
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Probability.Independence.Basic

/-!
# Frieze–Jerrum Semidefinite Relaxation and Gaussian Argmax Rounding

This module develops the Frieze–Jerrum semidefinite programming relaxation for maximum `k`-colouring
and its `ℓ`-colour Gaussian argmax rounding analysis under standard Lean
axioms:

1. Explicit unit simplex vectors in `ℝ^n` (`n ≥ k ≥ 2`) with pairwise inner product `-1 / (k - 1)`.
2. The weighted multigraph Frieze–Jerrum SDP relaxation (`IsFriezeJerrumFeasible`,
   `friezeJerrumSdpValue`), exact embedding of `k`-colourings via simplex vectors, relaxation
   soundness, and existence of optimal solutions by compactness.
3. Deterministic lexicographic argmax (`argmaxFin`), scale-invariant Gaussian argmax rounding
   (`argmaxColoring`), exact rotational invariance to the `ℓ`-dimensional correlated Gaussian
   collision probability `N_ℓ(a) = ℓ * P_ℓ(a)`, and exact expectation formula.
4. Complete Taylor series of `N_ℓ(a) = ∑' r, c_r a^r` on `[-1, 1]` via the multivariate Hermite
   expansion (`CslibFrontier`), proving `c_r ≥ 0`, `c_0 = 1 / ℓ`, `N_ℓ(0) = 1 / ℓ`, `N_ℓ(1) = 1`,
   `N_ℓ(-1) = 0`, `∑' i, c_{2i} = 1 / 2`, convexity on `[0, 1]`, continuity on `[-1, 1]`, the
   quadratic upper bound `N_ℓ(a) ≤ 1 / ℓ + c_1 a + a² / 2` on `[-1, 0]`, and the strict inequality
   `N_ℓ(a) < 1 / ℓ` on `[-1, 0)`.

## Main definitions

* `CslibFrontier.Algorithms.Semidefinite.simplexVector`: explicit unit simplex vectors in `ℝ^n`.
* `CslibFrontier.Algorithms.Semidefinite.coloringCutValue`: weighted multigraph `ℓ`-colouring value.
* `CslibFrontier.Algorithms.Semidefinite.IsFriezeJerrumFeasible`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumSdpValue`: Frieze–Jerrum SDP feasibility and
  objective.
* `CslibFrontier.Algorithms.Semidefinite.argmaxFin`,
  `CslibFrontier.Algorithms.Semidefinite.argmaxColoring`:
  lexicographic argmax and Gaussian argmax rounding.
* `CslibFrontier.Algorithms.Semidefinite.gaussianMaxIndicator`: coordinate-maximum indicator on
  `ℝ^ℓ`.
* `CslibFrontier.Algorithms.Semidefinite.friezeJerrumPairProb`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumCollisionProb`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumTaylorCoeff`: `P_ℓ(a)`, `N_ℓ(a)`, and Taylor
  coefficients `c_r(ℓ)`.

## Main results

* `CslibFrontier.Algorithms.Semidefinite.exists_simplex_vectors`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumSdpValue_simplex`: simplex vectors and exact
  embedding.
* `CslibFrontier.Algorithms.Semidefinite.coloringCutValue_le_friezeJerrumSdpValue_add`,
  `CslibFrontier.Algorithms.Semidefinite.exists_isMaxOn_friezeJerrumSdpValue`: relaxation soundness
  and
  existence of optimal solutions.
* `CslibFrontier.Algorithms.Semidefinite.integral_coloringCutValue_argmaxColoring`: exact expected
  value of
  Gaussian argmax rounding.
* `CslibFrontier.Algorithms.Semidefinite.hasSum_friezeJerrumCollisionProb`,
  `CslibFrontier.Algorithms.Semidefinite.hasSum_friezeJerrumTaylorCoeff_even`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumCollisionProb_le_neg`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumCollisionProb_convexOn`,
  `CslibFrontier.Algorithms.Semidefinite.friezeJerrumCollisionProb_lt_inv_of_neg`: Taylor series and
  analytic properties of `N_ℓ(a)`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Finset BigOperators
open scoped RealInnerProductSpace NNReal ENNReal

namespace CslibFrontier.Algorithms.Semidefinite

/-! ### Simplex vectors in `ℝ^n` -/

/-- Explicit `i`-th simplex vector in `EuclideanSpace ℝ (Fin n)` with `k` nonzero entries:
`(1 - k) / √(k(k - 1))` at coordinate `i` and `1 / √(k(k - 1))` at the other `k - 1` coordinates
below `k`. -/
noncomputable def simplexVector (k n : ℕ) (i : Fin k) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n =>
    if j.1 = i.1 then (1 - (k : ℝ)) / √((k : ℝ) * ((k : ℝ) - 1))
    else if j.1 < k then 1 / √((k : ℝ) * ((k : ℝ) - 1))
    else 0

theorem simplexVector_inner {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) (i j : Fin k) :
    ⟪simplexVector k n i, simplexVector k n j⟫ = if i = j then 1 else -1 / ((k : ℝ) - 1) := by
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hden_pos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := mul_pos hk_pos hkm1
  set s : ℝ := √((k : ℝ) * ((k : ℝ) - 1))
  have hs_sq : s * s = (k : ℝ) * ((k : ℝ) - 1) := Real.mul_self_sqrt hden_pos.le
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, simplexVector]
  let f : Fin k → ℝ := fun m =>
    (if m = j then (1 - (k : ℝ)) / s else 1 / s) * (if m = i then (1 - (k : ℝ)) / s else 1 / s)
  have hsum_eq : ∑ m : Fin n,
      (if m.1 = j.1 then (1 - (k : ℝ)) / s else if m.1 < k then 1 / s else 0) *
      (if m.1 = i.1 then (1 - (k : ℝ)) / s else if m.1 < k then 1 / s else 0) =
      ∑ m : Fin k, f m := by
    let emb : Fin k ↪ Fin n := Fin.castLEEmb hn
    have hmap : ∑ m : Fin k, f m =
        ∑ m ∈ Finset.univ.map emb,
          (if m.1 = j.1 then (1 - (k : ℝ)) / s else if m.1 < k then 1 / s else 0) *
          (if m.1 = i.1 then (1 - (k : ℝ)) / s else if m.1 < k then 1 / s else 0) := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hval : (emb m).1 = m.1 := rfl
      simp [f, hval, Fin.ext_iff]
    rw [hmap]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hnotlt : ¬ m.1 < k := fun hlt =>
      hm (Finset.mem_map.mpr ⟨⟨m.1, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hne_i : m.1 ≠ i.1 := fun h => hnotlt (h ▸ i.2)
    have hne_j : m.1 ≠ j.1 := fun h => hnotlt (h ▸ j.2)
    simp [hne_i, hne_j, hnotlt]
  change (∑ m : Fin n,
      (if m.1 = j.1 then (1 - (k : ℝ)) / s else if m.1 < k then 1 / s else 0) *
      (if m.1 = i.1 then (1 - (k : ℝ)) / s else if m.1 < k then 1 / s else 0)) = _
  rw [hsum_eq]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)]
    have hrest : ∑ m ∈ Finset.univ.erase i, f m = ((k - 1 : ℕ) : ℝ) * ((1 / s) * (1 / s)) := by
      have hterm : ∀ m ∈ Finset.univ.erase i, f m = (1 / s) * (1 / s) := fun m hm => by
        simp [f, (Finset.mem_erase.mp hm).1]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hrest, show f i = ((1 - (k : ℝ)) / s) * ((1 - (k : ℝ)) / s) by simp [f],
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hmul : ((1 - (k : ℝ)) / s) * ((1 - (k : ℝ)) / s) +
        ((k : ℝ) - 1) * ((1 / s) * (1 / s)) =
        ((1 - (k : ℝ)) ^ 2 + ((k : ℝ) - 1)) / (s * s) := by ring
    rw [hmul, hs_sq]
    field_simp [hk_pos.ne', hkm1.ne']
    ring
  · simp only [hij, ↓reduceIte]
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i),
      ← Finset.add_sum_erase (Finset.univ.erase i) f
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    have hrest : ∑ m ∈ (Finset.univ.erase i).erase j, f m =
        ((k - 2 : ℕ) : ℝ) * ((1 / s) * (1 / s)) := by
      have hterm : ∀ m ∈ (Finset.univ.erase i).erase j, f m = (1 / s) * (1 / s) := fun m hm => by
        have h1 := (Finset.mem_erase.mp hm).1
        have h2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
        simp [f, h1, h2]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have : k - 1 - 1 = k - 2 := by omega
      rw [this]
    rw [hrest, show f i = (1 / s) * ((1 - (k : ℝ)) / s) by simp [f, hij],
      show f j = ((1 - (k : ℝ)) / s) * (1 / s) by simp [f, Ne.symm hij],
      Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_ofNat]
    have hmul : (1 / s) * ((1 - (k : ℝ)) / s) + (((1 - (k : ℝ)) / s) * (1 / s) +
        ((k : ℝ) - 2) * ((1 / s) * (1 / s))) =
        (2 * (1 - (k : ℝ)) + ((k : ℝ) - 2)) / (s * s) := by ring
    rw [hmul, hs_sq]
    field_simp [hk_pos.ne', hkm1.ne']
    ring

theorem simplexVector_norm {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) (i : Fin k) :
    ‖simplexVector k n i‖ = 1 := by
  have h1 : ‖simplexVector k n i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, simplexVector_inner hk hn i i]
    simp
  nlinarith [norm_nonneg (simplexVector k n i)]

/-- For `n ≥ k ≥ 2`, there exist `k` unit vectors in `ℝ^n` with pairwise inner product
`-1 / (k - 1)`. -/
theorem exists_simplex_vectors {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    ∃ v : Fin k → EuclideanSpace ℝ (Fin n),
      ∀ i j : Fin k, ⟪v i, v j⟫ = if i = j then 1 else -1 / ((k : ℝ) - 1) :=
  ⟨simplexVector k n, simplexVector_inner hk hn⟩

/-! ### Weighted multigraph Frieze–Jerrum SDP relaxation -/

/-- Weighted multigraph `ℓ`-colouring value: total weight of properly coloured edges. -/
@[expose] noncomputable def coloringCutValue {ι V : Type*} [Fintype ι]
    (ends : ι → V × V) (w : ι → ℝ) {ℓ : ℕ} (c : V → Fin ℓ) : ℝ :=
  ∑ e : ι, if c (ends e).1 ≠ c (ends e).2 then w e else 0

/-- Feasibility predicate for the Frieze–Jerrum `k`-colouring SDP: unit vectors with pairwise
inner products at least `-1 / (k - 1)`. -/
@[expose] def IsFriezeJerrumFeasible {V F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (k : ℕ) (v : V → F) : Prop :=
  (∀ i : V, ‖v i‖ = 1) ∧ (∀ i j : V, -1 / ((k : ℝ) - 1) ≤ ⟪v i, v j⟫)

/-- Objective of the Frieze–Jerrum `k`-colouring SDP relaxation. -/
@[expose] noncomputable def friezeJerrumSdpValue {ι V F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (k : ℕ) (ends : ι → V × V) (w : ι → ℝ) (v : V → F) : ℝ :=
  ∑ e : ι, w e * ((((k : ℝ) - 1) / (k : ℝ)) * (1 - ⟪v (ends e).1, v (ends e).2⟫))

theorem isFriezeJerrumFeasible_simplex {V : Type*} {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    (c : V → Fin k) : IsFriezeJerrumFeasible k (fun i => simplexVector k n (c i)) := by
  refine ⟨fun i => simplexVector_norm hk hn (c i), fun i j => ?_⟩
  rw [simplexVector_inner hk hn]
  split_ifs
  · have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have : -1 / ((k : ℝ) - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hkm1.le
    linarith
  · exact le_rfl

theorem friezeJerrumSdpValue_simplex {ι V : Type*} [Fintype ι] {k n : ℕ} (hk : 2 ≤ k)
    (hn : k ≤ n) (ends : ι → V × V) (w : ι → ℝ) (c : V → Fin k) :
    friezeJerrumSdpValue k ends w (fun i => simplexVector k n (c i)) =
      coloringCutValue ends w c := by
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  unfold friezeJerrumSdpValue coloringCutValue
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [simplexVector_inner hk hn]
  by_cases h : c (ends e).1 = c (ends e).2
  · simp [h]
  · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true]
    have h1 : (((k : ℝ) - 1) / (k : ℝ)) * (1 - -1 / ((k : ℝ) - 1)) = 1 := by
      field_simp [hk_pos.ne', hkm1.ne']
      ring
    rw [h1, mul_one]

/-- Relaxation soundness: any `ε`-optimal feasible vector solution in `ℝ^n` (`n ≥ k ≥ 2`) has
SDP value at least every `k`-colouring value minus `ε`. -/
theorem coloringCutValue_le_friezeJerrumSdpValue_add {ι V : Type*} [Fintype ι] {k n : ℕ}
    (hk : 2 ≤ k) (hn : k ≤ n) {ends : ι → V × V} {w : ι → ℝ}
    {v : V → EuclideanSpace ℝ (Fin n)} {ε : ℝ}
    (hopt : ∀ v' : V → EuclideanSpace ℝ (Fin n), IsFriezeJerrumFeasible k v' →
      friezeJerrumSdpValue k ends w v' ≤ friezeJerrumSdpValue k ends w v + ε)
    (c : V → Fin k) :
    coloringCutValue ends w c ≤ friezeJerrumSdpValue k ends w v + ε := by
  rw [← friezeJerrumSdpValue_simplex hk hn ends w c]
  exact hopt _ (isFriezeJerrumFeasible_simplex hk hn c)

/-- Compactness: for any vertex type `V` and `k ≥ 2`, `n ≥ 1`, the Frieze–Jerrum SDP attains its
maximum over `V → EuclideanSpace ℝ (Fin n)`. -/
theorem exists_isMaxOn_friezeJerrumSdpValue {ι V : Type*} [Fintype ι]
    {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (ends : ι → V × V) (w : ι → ℝ) :
    ∃ v : V → EuclideanSpace ℝ (Fin n),
      IsFriezeJerrumFeasible k v ∧
      ∀ v' : V → EuclideanSpace ℝ (Fin n), IsFriezeJerrumFeasible k v' →
        friezeJerrumSdpValue k ends w v' ≤ friezeJerrumSdpValue k ends w v := by
  let S : Set (V → EuclideanSpace ℝ (Fin n)) := {v | IsFriezeJerrumFeasible k v}
  have hcomp : IsCompact S := by
    have hsub : S ⊆ Set.pi Set.univ fun _ : V => Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      fun v hv i _ => by simpa [Metric.mem_sphere, dist_zero_right] using hv.1 i
    have hclosed : IsClosed S := by
      have h1 : IsClosed {v : V → EuclideanSpace ℝ (Fin n) | ∀ i : V, ‖v i‖ = 1} := by
        simpa [Set.ofPred_forall] using isClosed_iInter fun i : V =>
          isClosed_eq (continuous_norm.comp (continuous_apply i)) continuous_const
      have h2 : IsClosed {v : V → EuclideanSpace ℝ (Fin n) |
          ∀ i j : V, -1 / ((k : ℝ) - 1) ≤ ⟪v i, v j⟫} := by
        simpa [Set.ofPred_forall] using isClosed_iInter fun i : V => isClosed_iInter fun j : V =>
          isClosed_le continuous_const
            ((continuous_apply i).inner (continuous_apply j))
      exact h1.inter h2
    exact (isCompact_univ_pi fun _ =>
        isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset hclosed hsub
  have hne : S.Nonempty := by
    let u0 : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single ⟨0, hn⟩ (1 : ℝ))
    have hu0 : ‖u0‖ = 1 := by
      have h1 : ‖u0‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
        simp [u0, dotProduct, Pi.single_apply]
      nlinarith [norm_nonneg u0]
    refine ⟨fun _ => u0, fun _ => hu0, fun _ _ => ?_⟩
    rw [real_inner_self_eq_norm_sq, hu0, one_pow]
    have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have : -1 / ((k : ℝ) - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hkm1.le
    linarith
  have hcont : Continuous (friezeJerrumSdpValue k ends w :
      (V → EuclideanSpace ℝ (Fin n)) → ℝ) := by
    unfold friezeJerrumSdpValue
    refine continuous_finsetSum _ fun e _ => continuous_const.mul (continuous_const.mul
      (continuous_const.sub ((continuous_apply _).inner (continuous_apply _))))
  obtain ⟨v, hvS, hvmax⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
  exact ⟨v, hvS, fun v' hv' => hvmax hv'⟩

/-! ### Deterministic `argmaxFin` and Gaussian argmax rounding -/

/-- Deterministic lexicographic argmax of `x : Fin ℓ → ℝ` (`ℓ > 0`): the smallest index
attaining the maximum of `x`. -/
noncomputable def argmaxFin {ℓ : ℕ} (hℓ : 0 < ℓ) (x : Fin ℓ → ℝ) : Fin ℓ :=
  (Finset.univ.filter fun c : Fin ℓ => ∀ d : Fin ℓ, x d ≤ x c).min' (by
    obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ x
      ⟨⟨0, hℓ⟩, Finset.mem_univ _⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, fun d => hc d (Finset.mem_univ d)⟩⟩)

theorem argmaxFin_le {ℓ : ℕ} (hℓ : 0 < ℓ) (x : Fin ℓ → ℝ) (d : Fin ℓ) :
    x d ≤ x (argmaxFin hℓ x) := by
  have hmem := Finset.min'_mem (Finset.univ.filter fun c : Fin ℓ => ∀ a : Fin ℓ, x a ≤ x c) (by
    obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ x ⟨⟨0, hℓ⟩, Finset.mem_univ _⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, fun a => hc a (Finset.mem_univ a)⟩⟩)
  exact (Finset.mem_filter.mp hmem).2 d

theorem argmaxFin_eq_of_strict_max {ℓ : ℕ} (hℓ : 0 < ℓ) {x : Fin ℓ → ℝ} {c : Fin ℓ}
    (hc : ∀ d : Fin ℓ, d ≠ c → x d < x c) :
    argmaxFin hℓ x = c := by
  have hmem : c ∈ Finset.univ.filter fun a : Fin ℓ => ∀ d : Fin ℓ, x d ≤ x a :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, fun d => by
      by_cases h : d = c
      · subst h; exact le_rfl
      · exact (hc d h).le⟩
  have hle : argmaxFin hℓ x ≤ c := Finset.min'_le _ c hmem
  by_contra hne
  have h1 := hc (argmaxFin hℓ x) hne
  have h2 := argmaxFin_le hℓ x c
  linarith

theorem argmaxFin_smul_pos {ℓ : ℕ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (x : Fin ℓ → ℝ) :
    argmaxFin hℓ (fun c => t * x c) = argmaxFin hℓ x := by
  unfold argmaxFin
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h d => le_of_mul_le_mul_left (h d) ht,
    fun h d => mul_le_mul_of_nonneg_left (h d) ht.le⟩

/-- Frieze–Jerrum Gaussian argmax rounding: vertex `i` receives colour `argmax_c ⟪v i, g c⟫`. -/
@[expose] noncomputable def argmaxColoring {V F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {ℓ : ℕ} (hℓ : 0 < ℓ) (v : V → F) (g : Fin ℓ → F) (i : V) : Fin ℓ :=
  argmaxFin hℓ fun c => ⟪v i, g c⟫

theorem argmaxColoring_smul_pos {V F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ℓ : ℕ} (hℓ : 0 < ℓ) {t : V → ℝ} (ht : ∀ i, 0 < t i) (v : V → F) (g : Fin ℓ → F) :
    argmaxColoring hℓ (fun i => t i • v i) g = argmaxColoring hℓ v g := by
  funext i
  simp only [argmaxColoring, real_inner_smul_left]
  exact argmaxFin_smul_pos hℓ (ht i) _

/-- Coordinate-maximum indicator `1_{∀ d, x d ≤ x c}` on `Fin ℓ → ℝ`. -/
@[expose] noncomputable def gaussianMaxIndicator (ℓ : ℕ) (c : Fin ℓ) (x : Fin ℓ → ℝ) : ℝ :=
  if ∀ d : Fin ℓ, x d ≤ x c then 1 else 0

@[fun_prop]
theorem measurable_gaussianMaxIndicator (ℓ : ℕ) (c : Fin ℓ) :
    Measurable (gaussianMaxIndicator ℓ c) := by
  have hset : MeasurableSet {x : Fin ℓ → ℝ | ∀ d : Fin ℓ, x d ≤ x c} := by
    simpa [Set.ofPred_forall] using MeasurableSet.iInter fun d : Fin ℓ =>
      measurableSet_le (measurable_pi_apply d) (measurable_pi_apply c)
  exact Measurable.ite hset measurable_const measurable_const

theorem memLp_gaussianMaxIndicator (ℓ : ℕ) (c : Fin ℓ) :
    MemLp (gaussianMaxIndicator ℓ c) 2 (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) := by
  refine MemLp.of_bound (measurable_gaussianMaxIndicator ℓ c).aestronglyMeasurable 1
    (ae_of_all _ fun x => ?_)
  simp only [gaussianMaxIndicator, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-! ### Collision probability `N_ℓ(a)`, pair probability `P_ℓ(a)`, and Taylor series -/

/-- Frieze–Jerrum pair probability `P_ℓ(a) = Stab_a[1_{x_0 = max x}]`. -/
@[expose] noncomputable def friezeJerrumPairProb (ℓ : ℕ) (a : ℝ) : ℝ :=
  if h : 0 < ℓ then gaussianNoiseStability a (gaussianMaxIndicator ℓ ⟨0, h⟩) else 0

/-- Frieze–Jerrum collision probability `N_ℓ(a) = ℓ * P_ℓ(a)`. -/
@[expose] noncomputable def friezeJerrumCollisionProb (ℓ : ℕ) (a : ℝ) : ℝ :=
  (ℓ : ℝ) * friezeJerrumPairProb ℓ a

/-- `r`-th Taylor coefficient `c_r(ℓ)` of `N_ℓ(a)` from the multivariate Hermite expansion. -/
@[expose] noncomputable def friezeJerrumTaylorCoeff (ℓ r : ℕ) : ℝ :=
  if h : 0 < ℓ then
    (ℓ : ℝ) * ∑ α ∈ (Fintype.piFinset fun _ : Fin ℓ => Finset.range (r + 1)).filter
        (fun α : Fin ℓ → ℕ => ∑ i : Fin ℓ, α i = r),
      hermiteCoeff (gaussianMaxIndicator ℓ ⟨0, h⟩) α ^ 2
  else 0

theorem friezeJerrumTaylorCoeff_nonneg (ℓ r : ℕ) : 0 ≤ friezeJerrumTaylorCoeff ℓ r := by
  unfold friezeJerrumTaylorCoeff
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · exact le_rfl

/-- Almost surely under `γ^ℓ`, all coordinates of `x : Fin ℓ → ℝ` are pairwise distinct. -/
theorem ae_pairwise_ne_pi_gaussianReal (ℓ : ℕ) :
    ∀ᵐ x : Fin ℓ → ℝ ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1),
      ∀ c d : Fin ℓ, c ≠ d → x c ≠ x d := by
  rw [ae_all_iff]
  intro c
  rw [ae_all_iff]
  intro d
  by_cases hcd : c = d
  · exact ae_of_all _ fun _ h => absurd hcd h
  · have hne : ∀ᵐ x : Fin ℓ → ℝ ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1), x c ≠ x d := by
      change (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) {x | ¬ x c ≠ x d} = 0
      simp only [not_not]
      have hmp : MeasurePreserving (fun x : Fin ℓ → ℝ => (x c, x d))
          (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1)
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        refine ⟨(measurable_pi_apply c).prodMk (measurable_pi_apply d), ?_⟩
        have hindep : (fun x : Fin ℓ → ℝ => x c)
            ⟂ᵢ[Measure.pi fun _ : Fin ℓ => gaussianReal 0 1] fun x => x d :=
          (iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) fun _ => aemeasurable_id).indepFun hcd
        rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply c).aemeasurable
          (measurable_pi_apply d).aemeasurable] at hindep
        rw [hindep, (measurePreserving_eval _ c).map_eq, (measurePreserving_eval _ d).map_eq]
      have hpre : (fun x : Fin ℓ → ℝ => (x c, x d)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} =
          {x : Fin ℓ → ℝ | x c = x d} := rfl
      rw [← hpre, hmp.measure_preimage
        (measurableSet_eq_fun measurable_fst measurable_snd).nullMeasurableSet]
      rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      simp [measure_singleton]
    filter_upwards [hne] with x hx _ using hx

/-- Permutation symmetry of `Measure.pi`: swapping coordinates preserves `γ^ℓ`. -/
private theorem integral_gaussianMaxIndicator_eq_zero_coord {ℓ : ℕ} (hℓ : 0 < ℓ) (c : Fin ℓ) :
    ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ c z
        ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) =
      ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ ⟨0, hℓ⟩ z
        ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) := by
  let e : (Fin ℓ → ℝ) ≃ᵐ (Fin ℓ → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => ℝ) (Equiv.swap c ⟨0, hℓ⟩)
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1)
      (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ : Fin ℓ => gaussianReal 0 1) (Equiv.swap c ⟨0, hℓ⟩)
  rw [← hmp.integral_comp' (g := gaussianMaxIndicator ℓ ⟨0, hℓ⟩)]
  congr 1 with z
  change gaussianMaxIndicator ℓ c z = gaussianMaxIndicator ℓ ⟨0, hℓ⟩ (e z)
  simp only [gaussianMaxIndicator]
  have he_app : ∀ d : Fin ℓ, e z d = z ((Equiv.swap c ⟨0, hℓ⟩).symm d) := fun d => by
    conv_lhs => rw [← (Equiv.swap c ⟨0, hℓ⟩).apply_symm_apply d]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (Equiv.swap c ⟨0, hℓ⟩) z _
  simp only [he_app]
  have hiff : (∀ d : Fin ℓ, z d ≤ z c) ↔
      (∀ d : Fin ℓ, z ((Equiv.swap c ⟨0, hℓ⟩).symm d) ≤
        z ((Equiv.swap c ⟨0, hℓ⟩).symm ⟨0, hℓ⟩)) := by
    simp only [Equiv.symm_swap, Equiv.swap_apply_right]
    exact ⟨fun h d => h _, fun h d => by simpa using h (Equiv.swap c ⟨0, hℓ⟩ d)⟩
  exact if_congr hiff rfl rfl

/-- By symmetry of the `ℓ` coordinates, `E[1_{x_c = max x}] = 1 / ℓ`. -/
theorem integral_gaussianMaxIndicator {ℓ : ℕ} (hℓ : 0 < ℓ) (c : Fin ℓ) :
    ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ c z
        ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) = 1 / (ℓ : ℝ) := by
  have hsum : ∑ d : Fin ℓ, ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ d z
      ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) = 1 := by
    rw [← integral_finsetSum _ fun d _ => (memLp_gaussianMaxIndicator ℓ d).integrable one_le_two]
    have hae : (fun z => ∑ d : Fin ℓ, gaussianMaxIndicator ℓ d z) =ᵐ[Measure.pi fun _ : Fin ℓ =>
        gaussianReal 0 1] fun _ => (1 : ℝ) := by
      filter_upwards [ae_pairwise_ne_pi_gaussianReal ℓ] with z hz
      let m := argmaxFin hℓ z
      rw [Finset.sum_eq_single m]
      · simp [gaussianMaxIndicator, m, argmaxFin_le hℓ z]
      · intro d _ hdm
        simp only [gaussianMaxIndicator]
        have hlt : z d < z m := lt_of_le_of_ne (argmaxFin_le hℓ z d) (hz d m hdm)
        have hnot : ¬ ∀ e, z e ≤ z d := fun h => not_lt_of_ge (h m) hlt
        simp [hnot]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [integral_congr_ae hae, integral_const, probReal_univ, smul_eq_mul, mul_one]
  have hconst : ∑ d : Fin ℓ, ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ d z
      ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) =
      (ℓ : ℝ) * ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ c z
        ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) := by
    have heq : ∀ d : Fin ℓ, ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ d z
        ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) =
        ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ c z
          ∂(Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) := fun d =>
      (integral_gaussianMaxIndicator_eq_zero_coord hℓ d).trans
        (integral_gaussianMaxIndicator_eq_zero_coord hℓ c).symm
    simp only [Finset.sum_congr rfl fun d _ => heq d, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hℓpos : (ℓ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hℓ).ne'
  rw [hconst] at hsum
  exact eq_one_div_of_mul_eq_one_right (by linarith)

/-- Exact expected value of Frieze–Jerrum Gaussian argmax rounding over `ℓ` i.i.d. standard
Gaussian vectors in `F`. -/
theorem integral_coloringCutValue_argmaxColoring {ι V F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {ℓ : ℕ} (hℓ : 0 < ℓ) (ends : ι → V × V) (w : ι → ℝ)
    {v : V → F} (hv : ∀ i : V, ‖v i‖ = 1) :
    ∫ g : Fin ℓ → F, coloringCutValue ends w (argmaxColoring hℓ v g)
        ∂(Measure.pi fun _ : Fin ℓ => stdGaussian F) =
      ∑ e : ι, w e * (1 - friezeJerrumCollisionProb ℓ ⟪v (ends e).1, v (ends e).2⟫) := by
  let μ : Measure (Fin ℓ → F) := Measure.pi fun _ : Fin ℓ => stdGaussian F
  have h_edge : ∀ (u₁ u₂ : F), ‖u₁‖ = 1 → ‖u₂‖ = 1 →
      ∫ g : Fin ℓ → F, (if argmaxFin hℓ (fun c => ⟪u₁, g c⟫) ≠ argmaxFin hℓ (fun c => ⟪u₂, g c⟫)
          then (1 : ℝ) else 0) ∂μ =
        1 - friezeJerrumCollisionProb ℓ ⟪u₁, u₂⟫ := by
    intro u₁ u₂ hu₁ hu₂
    let φ : (Fin ℓ → F) → (Fin ℓ → ℝ) × (Fin ℓ → ℝ) :=
      fun g => (fun c => ⟪u₁, g c⟫, fun c => ⟪u₂, g c⟫)
    have hφ_meas : Measurable φ := by fun_prop
    have hmap : μ.map φ = correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫ := by
      have h1 := Measure.pi_map_pi (μ := fun _ : Fin ℓ => stdGaussian F)
        (f := fun _ : Fin ℓ => fun x : F => (⟪u₁, x⟫, ⟪u₂, x⟫)) (fun _ => by fun_prop)
      simp only [stdGaussian_map_inner_prod_eq_correlatedGaussian hu₁ hu₂] at h1
      rw [correlatedGaussianPi_eq_map_pi, ← h1, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    have hF_meas : Measurable (fun p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) =>
        if argmaxFin hℓ p.1 ≠ argmaxFin hℓ p.2 then (1 : ℝ) else 0) := by
      have hset : MeasurableSet {p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) |
          argmaxFin hℓ p.1 ≠ argmaxFin hℓ p.2} := by
        have heq_set : {p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) | argmaxFin hℓ p.1 = argmaxFin hℓ p.2} =
            ⋃ c : Fin ℓ, {p | argmaxFin hℓ p.1 = c} ∩ {p | argmaxFin hℓ p.2 = c} := by
          ext p; simp [eq_comm]
        have harg_meas : ∀ (c : Fin ℓ), MeasurableSet {x : Fin ℓ → ℝ | argmaxFin hℓ x = c} := by
          intro c
          have hsub : {x : Fin ℓ → ℝ | argmaxFin hℓ x = c} =
              {x | ∀ d : Fin ℓ, x d ≤ x c} ∩
                ⋂ d : Fin ℓ, {x | (d < c) → ¬ ∀ e, x e ≤ x d} := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
            constructor
            · intro hxc
              subst hxc
              refine ⟨argmaxFin_le hℓ x, fun d hd hmax => ?_⟩
              have hle : argmaxFin hℓ x ≤ d :=
                Finset.min'_le _ d (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hmax⟩)
              exact not_lt_of_ge hle hd
            · rintro ⟨hmax, hmin⟩
              have hle : argmaxFin hℓ x ≤ c :=
                Finset.min'_le _ c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hmax⟩)
              refine le_antisymm hle ?_
              by_contra hlt
              exact hmin (argmaxFin hℓ x) (lt_of_not_ge hlt) (argmaxFin_le hℓ x)
          rw [hsub]
          have hm1 : MeasurableSet {x : Fin ℓ → ℝ | ∀ d : Fin ℓ, x d ≤ x c} := by
            simpa [Set.ofPred_forall] using MeasurableSet.iInter fun d : Fin ℓ =>
              measurableSet_le (measurable_pi_apply d) (measurable_pi_apply c)
          refine hm1.inter (MeasurableSet.iInter fun d : Fin ℓ => ?_)
          by_cases hdc : d < c
          · simp only [hdc, true_imp_iff]
            have hm2 : MeasurableSet {x : Fin ℓ → ℝ | ∀ e : Fin ℓ, x e ≤ x d} := by
              simpa [Set.ofPred_forall] using MeasurableSet.iInter fun e : Fin ℓ =>
                measurableSet_le (measurable_pi_apply e) (measurable_pi_apply d)
            exact hm2.compl
          · simp [hdc]
        have hcompl : MeasurableSet {p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) |
            argmaxFin hℓ p.1 = argmaxFin hℓ p.2} := by
          rw [heq_set]
          exact MeasurableSet.iUnion fun c =>
            (measurable_fst (harg_meas c)).inter (measurable_snd (harg_meas c))
        exact hcompl.compl
      exact Measurable.ite hset measurable_const measurable_const
    have hcomp : ∫ g : Fin ℓ → F,
        (if argmaxFin hℓ (fun c => ⟪u₁, g c⟫) ≠ argmaxFin hℓ (fun c => ⟪u₂, g c⟫)
          then (1 : ℝ) else 0) ∂μ =
        ∫ p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ),
          (if argmaxFin hℓ p.1 ≠ argmaxFin hℓ p.2 then (1 : ℝ) else 0)
          ∂(correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫) := by
      rw [← hmap, integral_map hφ_meas.aemeasurable hF_meas.aestronglyMeasurable]
    rw [hcomp]
    have hρ : |⟪u₁, u₂⟫| ≤ 1 := by
      have := abs_real_inner_le_norm u₁ u₂
      rwa [hu₁, hu₂, mul_one] at this
    have hae1 : ∀ᵐ p ∂correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫,
        ∀ c d : Fin ℓ, c ≠ d → p.1 c ≠ p.1 d :=
      (measurePreserving_fst_correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫).quasiMeasurePreserving.ae
        (ae_pairwise_ne_pi_gaussianReal ℓ)
    have hae2 : ∀ᵐ p ∂correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫,
        ∀ c d : Fin ℓ, c ≠ d → p.2 c ≠ p.2 d :=
      (measurePreserving_snd_correlatedGaussianPi (Fin ℓ) hρ).quasiMeasurePreserving.ae
        (ae_pairwise_ne_pi_gaussianReal ℓ)
    have hae_eq : (fun p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) =>
        if argmaxFin hℓ p.1 ≠
          argmaxFin hℓ p.2 then (1 : ℝ) else 0) =ᵐ[correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫]
        fun p => 1 - ∑ c : Fin ℓ, gaussianMaxIndicator ℓ c p.1 * gaussianMaxIndicator ℓ c p.2 := by
      filter_upwards [hae1, hae2] with p hp1 hp2
      let m1 := argmaxFin hℓ p.1
      let m2 := argmaxFin hℓ p.2
      have hind : ∀ (x : Fin ℓ → ℝ) (hx : ∀ c d, c ≠ d → x c ≠ x d) (c : Fin ℓ),
          gaussianMaxIndicator ℓ c x = if c = argmaxFin hℓ x then 1 else 0 := by
        intro x hx c
        simp only [gaussianMaxIndicator]
        by_cases hc : c = argmaxFin hℓ x
        · subst hc; simp [argmaxFin_le hℓ x]
        · have hlt : x c < x (argmaxFin hℓ x) :=
            lt_of_le_of_ne (argmaxFin_le hℓ x c) (hx c _ hc)
          have hnot : ¬ ∀ d, x d ≤ x c := fun h => not_lt_of_ge (h _) hlt
          simp [hc, hnot]
      simp only [hind p.1 hp1, hind p.2 hp2]
      by_cases h12 : m1 = m2
      · simp only [m1, m2] at h12
        simp [h12]
      · have h0 : ∑ c : Fin ℓ, (if c = m1 then (1 : ℝ) else 0) *
            (if c = m2 then (1 : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun c _ => ?_
          by_cases hc : c = m1
          · subst hc; simp [h12]
          · simp [hc]
        rw [h0, sub_zero]
        simp only [m1, m2] at h12
        simp [h12]
    rw [integral_congr_ae hae_eq]
    have hint_c : ∀ c : Fin ℓ, Integrable (fun p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) =>
        gaussianMaxIndicator ℓ c p.1 * gaussianMaxIndicator ℓ c p.2)
        (correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫) := fun c => by
      refine Integrable.of_bound
        (((measurable_gaussianMaxIndicator ℓ c).comp measurable_fst).mul
          ((measurable_gaussianMaxIndicator ℓ c).comp measurable_snd)).aestronglyMeasurable
        1 (ae_of_all _ fun p => ?_)
      simp only [gaussianMaxIndicator, Real.norm_eq_abs]
      split_ifs <;> norm_num
    rw [integral_sub (integrable_const (1 : ℝ)) (integrable_finsetSum _ fun c _ => hint_c c),
      integral_const, probReal_univ, smul_eq_mul, mul_one,
      integral_finsetSum _ fun c _ => hint_c c]
    have hperm : ∀ c : Fin ℓ,
        ∫ p : (Fin ℓ → ℝ) × (Fin ℓ → ℝ),
          gaussianMaxIndicator ℓ c p.1 * gaussianMaxIndicator ℓ c p.2
          ∂(correlatedGaussianPi (Fin ℓ) ⟪u₁, u₂⟫) =
        gaussianNoiseStability ⟪u₁, u₂⟫ (gaussianMaxIndicator ℓ ⟨0, hℓ⟩) := by
      intro c
      let e : (Fin ℓ → ℝ × ℝ) ≃ᵐ (Fin ℓ → ℝ × ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => ℝ × ℝ) (Equiv.swap c ⟨0, hℓ⟩)
      have hmp := measurePreserving_piCongrLeft (fun _ : Fin ℓ => correlatedGaussian ⟪u₁, u₂⟫)
        (Equiv.swap c ⟨0, hℓ⟩)
      rw [gaussianNoiseStability, correlatedGaussianPi_eq_map_pi,
        integral_map (by fun_prop) (by fun_prop),
        integral_map (by fun_prop) (by fun_prop), ← hmp.integral_comp']
      congr 1 with q
      change gaussianMaxIndicator ℓ c (fun i => (e q i).1) *
          gaussianMaxIndicator ℓ c (fun i => (e q i).2) =
        gaussianMaxIndicator ℓ ⟨0, hℓ⟩ (fun i => (q i).1) *
          gaussianMaxIndicator ℓ ⟨0, hℓ⟩ (fun i => (q i).2)
      have he_app : ∀ d : Fin ℓ, e q d = q ((Equiv.swap c ⟨0, hℓ⟩).symm d) := fun d => by
        conv_lhs => rw [← (Equiv.swap c ⟨0, hℓ⟩).apply_symm_apply d]
        exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ × ℝ)
          (Equiv.swap c ⟨0, hℓ⟩) q _
      simp only [gaussianMaxIndicator, he_app]
      have hiff1 : (∀ d : Fin ℓ, (q ((Equiv.swap c ⟨0, hℓ⟩).symm d)).1 ≤
            (q ((Equiv.swap c ⟨0, hℓ⟩).symm c)).1) ↔
          (∀ d : Fin ℓ, (q d).1 ≤ (q ⟨0, hℓ⟩).1) := by
        simp only [Equiv.symm_swap, Equiv.swap_apply_left]
        exact ⟨fun h d => by simpa using h (Equiv.swap c ⟨0, hℓ⟩ d), fun h d => h _⟩
      have hiff2 : (∀ d : Fin ℓ, (q ((Equiv.swap c ⟨0, hℓ⟩).symm d)).2 ≤
            (q ((Equiv.swap c ⟨0, hℓ⟩).symm c)).2) ↔
          (∀ d : Fin ℓ, (q d).2 ≤ (q ⟨0, hℓ⟩).2) := by
        simp only [Equiv.symm_swap, Equiv.swap_apply_left]
        exact ⟨fun h d => by simpa using h (Equiv.swap c ⟨0, hℓ⟩ d), fun h d => h _⟩
      rw [if_congr hiff1 rfl rfl, if_congr hiff2 rfl rfl]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      friezeJerrumCollisionProb, friezeJerrumPairProb, hℓ, ↓reduceDIte]
  unfold coloringCutValue argmaxColoring
  have hint_e : ∀ e : ι, Integrable (fun g : Fin ℓ → F =>
      if argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) ≠
        argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫) then w e else 0) μ := by
    intro e
    have harg_m : ∀ (u : F) (c : Fin ℓ),
        MeasurableSet {g : Fin ℓ → F | argmaxFin hℓ (fun d => ⟪u, g d⟫) = c} := by
      intro u c
      have hsub : {g : Fin ℓ → F | argmaxFin hℓ (fun d => ⟪u, g d⟫) = c} =
          {g | ∀ d : Fin ℓ, ⟪u, g d⟫ ≤ ⟪u, g c⟫} ∩
            ⋂ d : Fin ℓ, {g | (d < c) → ¬ ∀ a, ⟪u, g a⟫ ≤ ⟪u, g d⟫} := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
        constructor
        · intro hgc
          rw [← hgc]
          refine ⟨argmaxFin_le hℓ _, fun d hd hmax => ?_⟩
          have hle : argmaxFin hℓ (fun d => ⟪u, g d⟫) ≤ d :=
            Finset.min'_le _ d (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hmax⟩)
          exact not_lt_of_ge hle hd
        · rintro ⟨hmax, hmin⟩
          have hle : argmaxFin hℓ (fun d => ⟪u, g d⟫) ≤ c :=
            Finset.min'_le _ c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hmax⟩)
          refine le_antisymm hle ?_
          by_contra hlt
          exact hmin _ (lt_of_not_ge hlt) (argmaxFin_le hℓ _)
      rw [hsub]
      have hm1 : MeasurableSet {g : Fin ℓ → F | ∀ d : Fin ℓ, ⟪u, g d⟫ ≤ ⟪u, g c⟫} := by
        simpa [Set.ofPred_forall] using MeasurableSet.iInter fun d : Fin ℓ =>
          measurableSet_le (by fun_prop) (by fun_prop)
      refine hm1.inter (MeasurableSet.iInter fun d : Fin ℓ => ?_)
      by_cases hdc : d < c
      · simp only [hdc, true_imp_iff]
        have hm2 : MeasurableSet {g : Fin ℓ → F | ∀ a : Fin ℓ, ⟪u, g a⟫ ≤ ⟪u, g d⟫} := by
          simpa [Set.ofPred_forall] using MeasurableSet.iInter fun a : Fin ℓ =>
            measurableSet_le (by fun_prop) (by fun_prop)
        exact hm2.compl
      · simp [hdc]
    have hset : MeasurableSet {g : Fin ℓ → F |
        argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) ≠
          argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫)} := by
      have heq_set : {g : Fin ℓ → F | argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) =
          argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫)} =
          ⋃ c : Fin ℓ, {g | argmaxFin hℓ (fun d => ⟪v (ends e).1, g d⟫) = c} ∩
            {g | argmaxFin hℓ (fun d => ⟪v (ends e).2, g d⟫) = c} := by
        ext g; simp [eq_comm]
      have hm_eq : MeasurableSet {g : Fin ℓ → F | argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) =
          argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫)} := by
        rw [heq_set]
        exact MeasurableSet.iUnion fun c => (harg_m _ c).inter (harg_m _ c)
      exact hm_eq.compl
    have hind_eq : (fun g : Fin ℓ → F =>
        if argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) ≠
          argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫) then w e else 0) =
        {g : Fin ℓ → F | argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) ≠
          argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫)}.indicator (fun _ => w e) := by
      ext g; simp [Set.indicator]
    rw [hind_eq]
    exact (integrable_const (w e)).indicator hset
  rw [integral_finsetSum _ fun e _ => hint_e e]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hmul : (fun g : Fin ℓ → F =>
      if argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) ≠
        argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫) then w e else 0) =
      fun g => w e * (if argmaxFin hℓ (fun c => ⟪v (ends e).1, g c⟫) ≠
        argmaxFin hℓ (fun c => ⟪v (ends e).2, g c⟫) then (1 : ℝ) else 0) := by
    ext g; split_ifs <;> ring
  rw [hmul, integral_const_mul, h_edge _ _ (hv _) (hv _)]

/-! ### Taylor series, boundary values, convexity, continuity, and strict negativity -/

/-- Complete Taylor series of `N_ℓ(a) = ∑' r, c_r a^r` on `[-1, 1]`. -/
theorem hasSum_friezeJerrumCollisionProb {ℓ : ℕ} {a : ℝ} (ha : |a| ≤ 1) :
    HasSum (fun r : ℕ => friezeJerrumTaylorCoeff ℓ r * a ^ r) (friezeJerrumCollisionProb ℓ a) := by
  by_cases hℓ : 0 < ℓ
  · have hstab := hasSum_gaussianNoiseStability ha (memLp_gaussianMaxIndicator ℓ ⟨0, hℓ⟩)
    have habs : Summable (fun α : Fin ℓ → ℕ =>
        ‖a ^ (∑ i, α i) * hermiteCoeff (gaussianMaxIndicator ℓ ⟨0, hℓ⟩) α ^ 2‖) := by
      have hsq := (hasSum_hermiteCoeff_sq (memLp_gaussianMaxIndicator ℓ ⟨0, hℓ⟩)).summable
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_) hsq
      rw [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (sq_nonneg (hermiteCoeff (gaussianMaxIndicator ℓ ⟨0, hℓ⟩) α))]
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) ha)
    have hfib := hstab.tsum_fiberwise (fun α : Fin ℓ → ℕ => ∑ i : Fin ℓ, α i)
    have hterm : ∀ r : ℕ,
        (∑' α : {α : Fin ℓ → ℕ // ∑ i, α i = r},
          a ^ (∑ i, α.1 i) * hermiteCoeff (gaussianMaxIndicator ℓ ⟨0, hℓ⟩) α.1 ^ 2) =
        (∑ α ∈ (Fintype.piFinset fun _ : Fin ℓ => Finset.range (r + 1)).filter
            (fun α : Fin ℓ → ℕ => ∑ i : Fin ℓ, α i = r),
          hermiteCoeff (gaussianMaxIndicator ℓ ⟨0, hℓ⟩) α ^ 2) * a ^ r := by
      intro r
      let S := (Fintype.piFinset fun _ : Fin ℓ => Finset.range (r + 1)).filter
        (fun α : Fin ℓ → ℕ => ∑ i : Fin ℓ, α i = r)
      let e : {α : Fin ℓ → ℕ // ∑ i, α i = r} ≃ S :=
        { toFun := fun α => ⟨α.1, Finset.mem_filter.mpr
            ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by
              have := Finset.single_le_sum (fun j _ => Nat.zero_le (α.1 j)) (Finset.mem_univ i)
              omega), α.2⟩⟩
          invFun := fun α => ⟨α.1, (Finset.mem_filter.mp α.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Equiv.tsum_eq e.symm, tsum_fintype, ← Finset.sum_coe_sort S, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp [e, (Finset.mem_filter.mp α.2).2, mul_comm]
    have hmul := (hfib.congr_fun fun r => (hterm r).symm).mul_left (ℓ : ℝ)
    simpa only [friezeJerrumCollisionProb, friezeJerrumPairProb, friezeJerrumTaylorCoeff, hℓ,
      ↓reduceDIte, ← mul_assoc] using hmul
  · simp [friezeJerrumCollisionProb, friezeJerrumPairProb, friezeJerrumTaylorCoeff, hℓ, hasSum_zero]

theorem friezeJerrumTaylorCoeff_zero {ℓ : ℕ} (hℓ : 0 < ℓ) :
    friezeJerrumTaylorCoeff ℓ 0 = 1 / (ℓ : ℝ) := by
  have hS : ((Fintype.piFinset fun _ : Fin ℓ => Finset.range 1).filter
      (fun α : Fin ℓ → ℕ => ∑ i : Fin ℓ, α i = 0)) = {0} := by
    ext α
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h0⟩
      ext i
      exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
    · rintro rfl
      exact ⟨fun _ => Nat.zero_lt_one, by simp⟩
  simp only [friezeJerrumTaylorCoeff, hℓ, ↓reduceDIte, hS, Finset.sum_singleton,
    hermiteCoeff_zero, integral_gaussianMaxIndicator hℓ]
  have hℓ0 : (ℓ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hℓ).ne'
  field_simp [hℓ0]

theorem friezeJerrumCollisionProb_zero {ℓ : ℕ} (hℓ : 0 < ℓ) :
    friezeJerrumCollisionProb ℓ 0 = 1 / (ℓ : ℝ) := by
  have hs := hasSum_friezeJerrumCollisionProb (ℓ := ℓ) (a := 0) (by norm_num)
  have h0 : HasSum (fun r : ℕ => friezeJerrumTaylorCoeff ℓ r * (0 : ℝ) ^ r)
      (friezeJerrumTaylorCoeff ℓ 0) := by
    simpa only [pow_zero, mul_one] using
      hasSum_single (f := fun r : ℕ => friezeJerrumTaylorCoeff ℓ r * (0 : ℝ) ^ r) 0
        fun r hr => by simp [zero_pow hr]
  rw [hs.unique h0, friezeJerrumTaylorCoeff_zero hℓ]

theorem friezeJerrumCollisionProb_one {ℓ : ℕ} (hℓ : 0 < ℓ) :
    friezeJerrumCollisionProb ℓ 1 = 1 := by
  simp only [friezeJerrumCollisionProb, friezeJerrumPairProb, hℓ, ↓reduceDIte,
    gaussianNoiseStability, correlatedGaussianPi_one]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hsq : ∀ z : Fin ℓ → ℝ,
      gaussianMaxIndicator ℓ ⟨0, hℓ⟩ z * gaussianMaxIndicator ℓ ⟨0, hℓ⟩ z =
        gaussianMaxIndicator ℓ ⟨0, hℓ⟩ z := fun z => by
    simp only [gaussianMaxIndicator]; split_ifs <;> norm_num
  simp only [hsq, integral_gaussianMaxIndicator hℓ]
  exact mul_one_div_cancel (Nat.cast_pos.mpr hℓ).ne'

theorem friezeJerrumCollisionProb_neg_one {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    friezeJerrumCollisionProb ℓ (-1) = 0 := by
  have hℓ0 : 0 < ℓ := by omega
  simp only [friezeJerrumCollisionProb, friezeJerrumPairProb, hℓ0, ↓reduceDIte,
    gaussianNoiseStability]
  have hneg1 : correlatedGaussianPi (Fin ℓ) (-1) =
      (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1).map fun z => (z, -z) := by
    have h : (fun q : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) =>
        (q.1, fun i => (-1 : ℝ) * q.1 i + √(1 - (-1 : ℝ) ^ 2) * q.2 i)) =
        (fun z : Fin ℓ → ℝ => (z, -z)) ∘ Prod.fst := by
      ext q i <;> simp
    rw [correlatedGaussianPi_eq_map, h, ← Measure.map_map (by fun_prop) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [hneg1, integral_map (by fun_prop) (by fun_prop)]
  have hae : (fun z : Fin ℓ → ℝ =>
      gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ z * gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ (-z)) =ᵐ[
        Measure.pi fun _ : Fin ℓ => gaussianReal 0 1] fun _ => (0 : ℝ) := by
    filter_upwards [ae_pairwise_ne_pi_gaussianReal ℓ] with z hz
    have hne : (⟨1, by omega⟩ : Fin ℓ) ≠ ⟨0, hℓ0⟩ := by simp [Fin.ext_iff]
    have hdistinct := hz ⟨1, by omega⟩ ⟨0, hℓ0⟩ hne
    simp only [gaussianMaxIndicator, Pi.neg_apply, neg_le_neg_iff]
    by_cases h1 : ∀ d, z d ≤ z ⟨0, hℓ0⟩
    · have h2 : ¬ ∀ d, z ⟨0, hℓ0⟩ ≤ z d := fun h => hdistinct (le_antisymm (h1 _) (h _))
      simp [h1, h2]
    · simp [h1]
  rw [integral_congr_ae hae, integral_zero, mul_zero]

/-- Sum of even Taylor coefficients: `∑' i, c_{2i}(ℓ) = 1 / 2` for `ℓ ≥ 2`. -/
theorem hasSum_friezeJerrumTaylorCoeff_even {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    HasSum (fun i : ℕ => friezeJerrumTaylorCoeff ℓ (2 * i)) (1 / 2) := by
  have hℓ0 : 0 < ℓ := by omega
  have h1 := hasSum_friezeJerrumCollisionProb (ℓ := ℓ) (a := 1) (by norm_num)
  have hm1 := hasSum_friezeJerrumCollisionProb (ℓ := ℓ) (a := -1) (by norm_num)
  rw [friezeJerrumCollisionProb_one hℓ0] at h1
  rw [friezeJerrumCollisionProb_neg_one hℓ] at hm1
  have hadd := (h1.add hm1).mul_left (1 / 2 : ℝ)
  have hzero : ∀ r : ℕ, (1 / 2 : ℝ) *
      (friezeJerrumTaylorCoeff ℓ r * (1 : ℝ) ^ r +
        friezeJerrumTaylorCoeff ℓ r * (-1 : ℝ) ^ r) =
      if Even r then friezeJerrumTaylorCoeff ℓ r else 0 := by
    intro r
    rcases Nat.even_or_odd r with he | ho
    · simp [he, he.neg_one_pow]; ring
    · have hnot : ¬ Even r := Nat.not_even_iff_odd.mpr ho
      simp [hnot, ho.neg_one_pow]
  have hadd' : HasSum (fun r : ℕ => if Even r then friezeJerrumTaylorCoeff ℓ r else 0) (1 / 2) := by
    have h12 : (1 / 2 : ℝ) * (1 + 0) = 1 / 2 := by norm_num
    rw [h12] at hadd
    exact hadd.congr_fun fun r => (hzero r).symm
  have hinj : Function.Injective (fun i : ℕ => 2 * i) := fun a b h => by
    dsimp only at h; omega
  have hext : Function.extend (fun i : ℕ => 2 * i) (fun i => friezeJerrumTaylorCoeff ℓ (2 * i)) 0 =
      fun r : ℕ => if Even r then friezeJerrumTaylorCoeff ℓ r else 0 := by
    ext r
    by_cases h : r ∈ Set.range (fun i : ℕ => 2 * i)
    · obtain ⟨i, rfl⟩ := h
      rw [hinj.extend_apply]
      simp
    · rw [Function.extend_apply' _ _ _ h]
      have hnot : ¬ Even r := by rintro ⟨i, rfl⟩; exact h ⟨i, by dsimp; omega⟩
      simp [hnot]
  rw [← hext] at hadd'
  exact (hasSum_extend_zero hinj).mp hadd'

/-- Quadratic upper bound on `[-1, 0]`: `N_ℓ(a) ≤ 1 / ℓ + c_1(ℓ) * a + a² / 2` (`ℓ ≥ 2`). -/
theorem friezeJerrumCollisionProb_le_neg {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {a : ℝ}
    (ha0 : -1 ≤ a) (ha1 : a ≤ 0) :
    friezeJerrumCollisionProb ℓ a ≤
      1 / (ℓ : ℝ) + friezeJerrumTaylorCoeff ℓ 1 * a + a ^ 2 / 2 := by
  have hℓ0 : 0 < ℓ := by omega
  have ha : |a| ≤ 1 := abs_le.mpr ⟨ha0, by linarith⟩
  have hsum_a := hasSum_friezeJerrumCollisionProb (ℓ := ℓ) ha
  have hsum_even := hasSum_friezeJerrumTaylorCoeff_even hℓ
  let g : ℕ → ℝ := fun r =>
    if r = 0 then friezeJerrumTaylorCoeff ℓ 0
    else if r = 1 then friezeJerrumTaylorCoeff ℓ 1 * a
    else if Even r then friezeJerrumTaylorCoeff ℓ r * a ^ 2
    else 0
  have hg_sum : HasSum g
      (1 / (ℓ : ℝ) + friezeJerrumTaylorCoeff ℓ 1 * a + (1 / 2 - 1 / (ℓ : ℝ)) * a ^ 2) := by
    have h0 : HasSum (fun r : ℕ => if r = 0 then friezeJerrumTaylorCoeff ℓ 0 else 0)
        (1 / (ℓ : ℝ)) := by
      rw [← friezeJerrumTaylorCoeff_zero hℓ0]
      exact hasSum_single 0 fun r hr => by simp [hr]
    have h1 : HasSum (fun r : ℕ => if r = 1 then friezeJerrumTaylorCoeff ℓ 1 * a else 0)
        (friezeJerrumTaylorCoeff ℓ 1 * a) :=
      hasSum_single 1 fun r hr => by simp [hr]
    have heven_all : HasSum (fun r : ℕ => if Even r then friezeJerrumTaylorCoeff ℓ r else 0)
        (1 / 2) := by
      have hinj : Function.Injective (fun i : ℕ => 2 * i) := fun x y h => by
        dsimp only at h; omega
      have hext : Function.extend (fun i : ℕ => 2 * i)
          (fun i => friezeJerrumTaylorCoeff ℓ (2 * i)) 0 =
          fun r : ℕ => if Even r then friezeJerrumTaylorCoeff ℓ r else 0 := by
        ext r
        by_cases h : r ∈ Set.range (fun i : ℕ => 2 * i)
        · obtain ⟨i, rfl⟩ := h; rw [hinj.extend_apply]; simp
        · rw [Function.extend_apply' _ _ _ h]
          have hnot : ¬ Even r := by rintro ⟨i, rfl⟩; exact h ⟨i, by dsimp; omega⟩
          simp [hnot]
      rw [← hext]
      exact (hasSum_extend_zero hinj).mpr hsum_even
    have h0_even : HasSum (fun r : ℕ => if r = 0 then friezeJerrumTaylorCoeff ℓ 0 else 0)
        (1 / (ℓ : ℝ)) := h0
    have heven_ge2 : HasSum (fun r : ℕ =>
        if r ≠ 0 ∧ Even r then friezeJerrumTaylorCoeff ℓ r * a ^ 2 else 0)
        ((1 / 2 - 1 / (ℓ : ℝ)) * a ^ 2) := by
      have hsub := (heven_all.sub h0_even).mul_right (a ^ 2)
      refine hsub.congr_fun fun r => ?_
      by_cases hr0 : r = 0
      · subst hr0; simp
      · by_cases he : Even r <;> simp [hr0, he]
    refine ((h0.add h1).add heven_ge2).congr_fun fun r => ?_
    dsimp only [g]
    by_cases hr0 : r = 0
    · subst hr0; simp
    · by_cases hr1 : r = 1
      · subst hr1; simp [show ¬ Even 1 by decide]
      · simp [hr0, hr1]
  have hle : friezeJerrumCollisionProb ℓ a ≤
      1 / (ℓ : ℝ) + friezeJerrumTaylorCoeff ℓ 1 * a + (1 / 2 - 1 / (ℓ : ℝ)) * a ^ 2 := by
    refine hasSum_le (fun r => ?_) hsum_a hg_sum
    dsimp only [g]
    by_cases hr0 : r = 0
    · subst hr0; simp
    · by_cases hr1 : r = 1
      · subst hr1; simp
      · simp only [hr0, hr1, ↓reduceIte]
        have hc := friezeJerrumTaylorCoeff_nonneg ℓ r
        rcases Nat.even_or_odd r with he | ho
        · simp only [he, ↓reduceIte]
          obtain ⟨m, rfl⟩ := he
          have hm : 1 ≤ m := by omega
          have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
          have ha2_le : a ^ 2 ≤ 1 := by nlinarith
          have hpow : a ^ (m + m) ≤ a ^ 2 := by
            rw [show m + m = 2 * m by omega, pow_mul]
            have : (a ^ 2) ^ m ≤ (a ^ 2) ^ 1 := pow_le_pow_of_le_one ha2 ha2_le hm
            simpa using this
          exact mul_le_mul_of_nonneg_left hpow hc
        · have hnot : ¬ Even r := Nat.not_even_iff_odd.mpr ho
          simp only [hnot, ↓reduceIte]
          have hpow : a ^ r ≤ 0 := by
            obtain ⟨m, rfl⟩ := ho
            rw [pow_succ, pow_mul]
            exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sq_nonneg a) m) ha1
          exact mul_nonpos_of_nonneg_of_nonpos hc hpow
  have hsub_le : (1 / 2 - 1 / (ℓ : ℝ)) * a ^ 2 ≤ a ^ 2 / 2 := by
    have hinv : (0 : ℝ) ≤ 1 / (ℓ : ℝ) := by positivity
    nlinarith [sq_nonneg a]
  linarith

/-- Convexity of `N_ℓ(a)` on `[0, 1]`. -/
theorem friezeJerrumCollisionProb_convexOn (ℓ : ℕ) :
    ConvexOn ℝ (Icc 0 1) (friezeJerrumCollisionProb ℓ) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy s t hs ht hst => ?_⟩
  have hxy : s * x + t * y ∈ Icc (0 : ℝ) 1 := convex_Icc 0 1 hx hy hs ht hst
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hy1 : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hxy1 : |s * x + t * y| ≤ 1 := abs_le.mpr ⟨by linarith [hxy.1], hxy.2⟩
  have hsum_xy := hasSum_friezeJerrumCollisionProb (ℓ := ℓ) hxy1
  have hsum_rhs := ((hasSum_friezeJerrumCollisionProb (ℓ := ℓ) hx1).mul_left s).add
    ((hasSum_friezeJerrumCollisionProb (ℓ := ℓ) hy1).mul_left t)
  refine hasSum_le (fun r => ?_) hsum_xy hsum_rhs
  have hpow_conv : (s * x + t * y) ^ r ≤ s * x ^ r + t * y ^ r :=
    (convexOn_pow r).2 hx.1 hy.1 hs ht hst
  have hc := friezeJerrumTaylorCoeff_nonneg ℓ r
  have := mul_le_mul_of_nonneg_left hpow_conv hc
  linarith

/-- Continuity of `N_ℓ(a)` on `[-1, 1]`. -/
theorem friezeJerrumCollisionProb_continuousOn (ℓ : ℕ) :
    ContinuousOn (friezeJerrumCollisionProb ℓ) (Icc (-1) 1) := by
  have h1 := (hasSum_friezeJerrumCollisionProb (ℓ := ℓ) (a := 1) (by norm_num)).summable
  have hsum : Summable (friezeJerrumTaylorCoeff ℓ) := by simpa using h1
  have hcont : ContinuousOn (fun a : ℝ => ∑' r : ℕ, friezeJerrumTaylorCoeff ℓ r * a ^ r)
      (Icc (-1) 1) := by
    refine continuousOn_tsum (u := friezeJerrumTaylorCoeff ℓ)
      (fun r => (continuous_const.mul (continuous_pow r)).continuousOn) hsum fun r a ha => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (friezeJerrumTaylorCoeff_nonneg ℓ r), abs_pow]
    exact mul_le_of_le_one_right (friezeJerrumTaylorCoeff_nonneg ℓ r)
      (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ha))
  refine hcont.congr fun a ha => ?_
  exact (hasSum_friezeJerrumCollisionProb (abs_le.mpr ha)).tsum_eq.symm

/-- Strict inequality on `[-1, 0)`: `N_ℓ(a) < 1 / ℓ` for `ℓ ≥ 2` and `-1 ≤ a < 0`. -/
theorem friezeJerrumCollisionProb_lt_inv_of_neg {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {a : ℝ}
    (ha0 : -1 ≤ a) (ha1 : a < 0) :
    friezeJerrumCollisionProb ℓ a < 1 / (ℓ : ℝ) := by
  have hℓ0 : 0 < ℓ := by omega
  rcases eq_or_lt_of_le ha0 with rfl | ha_gt
  · rw [friezeJerrumCollisionProb_neg_one hℓ]
    positivity
  -- `-1 < a < 0`: write `y_i = a x_i + s g_i` and condition on `(x, g_0)`.
  set s : ℝ := √(1 - a ^ 2)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  set A : ℝ := -a / s
  have hA_pos : 0 < A := div_pos (by linarith) hs_pos
  -- Express `P_ℓ(a)` as `∫ x, f(x) * H_A(x)` where `H_A(x) = ∫ g_0, ∏_{i>0} Φ(g_0 - A(x_0 - x_i))`.
  have hℓ_eq : ℓ = (ℓ - 1) + 1 := by omega
  let m : ℕ := ℓ - 1
  have hm_pos : 0 < m := by omega
  let γℓ : Measure (Fin ℓ → ℝ) := Measure.pi fun _ : Fin ℓ => gaussianReal 0 1
  let γ : Measure ℝ := gaussianReal 0 1
  let Φ : ℝ → ℝ := cdf (gaussianReal 0 1)
  have hcond : ∀ (c : ℝ) (hc : 0 < c) (α : ℝ) (x : Fin ℓ → ℝ),
      ∫ g : Fin ℓ → ℝ,
          gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ (fun i => α * x i + c * g i) ∂γℓ =
        ∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩,
            Φ (g0 - (-α / c) * (x ⟨0, hℓ0⟩ - x i))) ∂γ := by
    intro c hc α x
    let e : (Fin (m + 1) → ℝ) ≃ᵐ (Fin ℓ → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => ℝ) (finCongr hℓ_eq.symm)
    have hmp_e : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => γ) γℓ :=
      measurePreserving_piCongrLeft (fun _ : Fin ℓ => γ) (finCongr hℓ_eq.symm)
    have hmp_succ := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => γ) 0
    let eAll : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin ℓ → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.trans e
    have hcomp : MeasurePreserving eAll (γ.prod (Measure.pi fun _ : Fin m => γ)) γℓ :=
      hmp_e.comp hmp_succ.symm
    rw [← hcomp.integral_comp']
    have hint_prod : Integrable (fun q : ℝ × (Fin m → ℝ) =>
        gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ (fun i => α * x i + c * eAll q i))
        (γ.prod (Measure.pi fun _ : Fin m => γ)) := by
      refine Integrable.of_bound ?_ 1 (ae_of_all _ fun q => ?_)
      · exact ((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).comp
          (Measurable.of_eval fun i => measurable_const.add
            (measurable_const.mul
              ((measurable_pi_apply i).comp hcomp.measurable)))).aestronglyMeasurable
      · simp only [gaussianMaxIndicator, Real.norm_eq_abs]; split_ifs <;> norm_num
    rw [integral_prod _ hint_prod]
    refine integral_congr_ae (ae_of_all _ fun g0 => ?_)
    -- Inner integral over `g' : Fin m → ℝ` is a product of `1_{g' j ≤ g0 - (-α/c)(x_0 - x_{j+1})}`
    let bound : Fin m → ℝ := fun j =>
      g0 - (-α / c) * (x ⟨0, hℓ0⟩ - x ⟨j.1 + 1, by omega⟩)
    have hpt : ∀ g' : Fin m → ℝ,
        gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ (fun i => α * x i + c * eAll (g0, g') i) =
        ∏ j : Fin m, if g' j ≤ bound j then (1 : ℝ) else 0 := by
      intro g'
      have he_app : ∀ (q : ℝ × (Fin m → ℝ)) (d : Fin ℓ),
          eAll q d = ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm q)
            ((finCongr hℓ_eq.symm).symm d) := fun q d => by
        change e ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm q) d = _
        conv_lhs => rw [← (finCongr hℓ_eq.symm).apply_symm_apply d]
        exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (finCongr hℓ_eq.symm) _ _
      have he_val0 : eAll (g0, g') ⟨0, hℓ0⟩ = g0 := by
        rw [he_app]
        have hidx : (finCongr hℓ_eq.symm).symm ⟨0, hℓ0⟩ = 0 := by ext; simp
        rw [hidx, MeasurableEquiv.piFinSuccAbove_symm_apply]
        simp [Fin.cons_zero]
      have he_val_succ : ∀ j : Fin m, eAll (g0, g') ⟨j.1 + 1, by omega⟩ = g' j := by
        intro j
        rw [he_app]
        have hidx : (finCongr hℓ_eq.symm).symm ⟨j.1 + 1, by omega⟩ = j.succ := by
          ext; simp [Fin.succ]
        rw [hidx, MeasurableEquiv.piFinSuccAbove_symm_apply]
        simp [Fin.cons_succ]
      simp only [gaussianMaxIndicator, he_val0]
      have hiff : (∀ d : Fin ℓ, α * x d + c * eAll (g0, g') d ≤ α * x ⟨0, hℓ0⟩ + c * g0) ↔
          ∀ j : Fin m, g' j ≤ bound j := by
        constructor
        · intro h j
          have hj := h ⟨j.1 + 1, by omega⟩
          rw [he_val_succ j] at hj
          dsimp only [bound]
          have hdiv : c * g' j ≤ c * (g0 - (-α / c) * (x ⟨0, hℓ0⟩ - x ⟨j.1 + 1, by omega⟩)) := by
            have : c * (g0 - (-α / c) * (x ⟨0, hℓ0⟩ - x ⟨j.1 + 1, by omega⟩)) =
                c * g0 + α * (x ⟨0, hℓ0⟩ - x ⟨j.1 + 1, by omega⟩) := by
              field_simp [hc.ne']; ring
            linarith
          exact le_of_mul_le_mul_left hdiv hc
        · intro h d
          by_cases hd0 : d.1 = 0
          · have : d = ⟨0, hℓ0⟩ := Fin.ext hd0
            subst this; rw [he_val0]
          · let j : Fin m := ⟨d.1 - 1, by omega⟩
            have hd_eq : d = ⟨j.1 + 1, by omega⟩ := Fin.ext (by simp [j]; omega)
            rw [hd_eq, he_val_succ j]
            have hj := h j
            have hmul := mul_le_mul_of_nonneg_left hj hc.le
            dsimp only [bound] at hmul
            have : c * (g0 - (-α / c) * (x ⟨0, hℓ0⟩ - x ⟨j.1 + 1, by omega⟩)) =
                c * g0 + α * (x ⟨0, hℓ0⟩ - x ⟨j.1 + 1, by omega⟩) := by
              field_simp [hc.ne']; ring
            linarith
      rw [if_congr hiff rfl rfl]
      by_cases hall : ∀ j : Fin m, g' j ≤ bound j
      · simp [hall]
      · simp only [hall, ↓reduceIte]
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [not_le.mpr hj])).symm
    simp only [hpt]
    rw [integral_fintype_prod_eq_prod (f := fun j r => if r ≤ bound j then (1 : ℝ) else 0)]
    have hprod_fin : (∏ j : Fin m, ∫ r : ℝ, (if r ≤ bound j then (1 : ℝ) else 0) ∂γ) =
        ∏ j : Fin m, Φ (bound j) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      have hind_eq : (fun r : ℝ => if r ≤ bound j then (1 : ℝ) else 0) =
          (Iic (bound j)).indicator (fun _ => (1 : ℝ)) := by
        ext r; simp [Set.indicator]
      rw [hind_eq, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
        ← cdf_eq_real]
    rw [hprod_fin]
    -- Match `∏ j : Fin m, Φ (bound j)` with `∏ i ∈ univ.filter (· ≠ 0), Φ (...)`
    let emb : Fin m ↪ Fin ℓ :=
      { toFun := fun j => ⟨j.1 + 1, by omega⟩
        inj' := fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega) }
    have hset : (Finset.univ.filter fun i : Fin ℓ => i ≠ ⟨0, hℓ0⟩) = Finset.univ.map emb := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hi
        have hi0 : i.1 ≠ 0 := fun h => hi (Fin.ext h)
        exact ⟨⟨i.1 - 1, by omega⟩, Fin.ext (by change (i.1 - 1) + 1 = i.1; omega)⟩
      · rintro ⟨j, rfl⟩ h
        have hv : j.1 + 1 = 0 := congrArg Fin.val h
        omega
    rw [hset, Finset.prod_map]
    rfl
  -- Now compare `P_ℓ(a)` with `P_ℓ(0) = 1 / ℓ²`
  have hPa : friezeJerrumPairProb ℓ a =
      ∫ x : Fin ℓ → ℝ, gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x *
        (∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ) ∂γℓ := by
    simp only [friezeJerrumPairProb, hℓ0, ↓reduceDIte, gaussianNoiseStability,
      correlatedGaussianPi_eq_map]
    rw [integral_map (by fun_prop) (by fun_prop)]
    have hint_ab : Integrable (fun q : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) =>
        gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ q.1 *
          gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ (fun i => a * q.1 i + s * q.2 i)) (γℓ.prod γℓ) := by
      refine Integrable.of_bound ?_ 1 (ae_of_all _ fun q => ?_)
      · exact (((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).comp measurable_fst).mul
          ((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).comp
            (Measurable.of_eval fun i =>
              (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
                (measurable_const.mul
                  ((measurable_pi_apply i).comp measurable_snd))))).aestronglyMeasurable
      · simp only [gaussianMaxIndicator, Real.norm_eq_abs]; split_ifs <;> norm_num
    rw [integral_prod _ hint_ab]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [integral_const_mul, hcond s hs_pos a x]
  have hP0 : friezeJerrumPairProb ℓ 0 =
      ∫ x : Fin ℓ → ℝ, gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x *
        (∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) ∂γ) ∂γℓ := by
    simp only [friezeJerrumPairProb, hℓ0, ↓reduceDIte, gaussianNoiseStability,
      correlatedGaussianPi_eq_map]
    rw [integral_map (by fun_prop) (by fun_prop)]
    have hint_0 : Integrable (fun q : (Fin ℓ → ℝ) × (Fin ℓ → ℝ) =>
        gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ q.1 *
          gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ (fun i => (0 : ℝ) * q.1 i + √(1 - (0 : ℝ) ^ 2) * q.2 i))
        (γℓ.prod γℓ) := by
      refine Integrable.of_bound ?_ 1 (ae_of_all _ fun q => ?_)
      · exact (((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).comp measurable_fst).mul
          ((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).comp
            (Measurable.of_eval fun i =>
              (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
                (measurable_const.mul
                  ((measurable_pi_apply i).comp measurable_snd))))).aestronglyMeasurable
      · simp only [gaussianMaxIndicator, Real.norm_eq_abs]; split_ifs <;> norm_num
    rw [integral_prod _ hint_0]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [integral_const_mul, hcond (√(1 - (0 : ℝ) ^ 2)) (by norm_num) 0 x]
    simp
  have hdiff_pos : 0 < friezeJerrumPairProb ℓ 0 - friezeJerrumPairProb ℓ a := by
    let F0 : (Fin ℓ → ℝ) → ℝ := fun x => gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x *
      (∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) ∂γ)
    let FA : (Fin ℓ → ℝ) → ℝ := fun x => gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x *
      (∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ)
    have hF0_int : Integrable F0 γℓ := by
      refine Integrable.of_bound ?_ 1 (ae_of_all _ fun x => ?_)
      · exact ((measurable_gaussianMaxIndicator ℓ ⟨0,
        hℓ0⟩).mul measurable_const).aestronglyMeasurable
      · dsimp only [F0]
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x| ≤ 1 := by
          simp only [gaussianMaxIndicator]; split_ifs <;> norm_num
        have h2 : |∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) ∂γ| ≤ 1 := by
          have hnn : 0 ≤ ∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) ∂γ :=
            integral_nonneg fun g0 => Finset.prod_nonneg fun _ _ => cdf_nonneg _ _
          rw [abs_of_nonneg hnn]
          calc ∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) ∂γ
              ≤ ∫ _ : ℝ, (1 : ℝ) ∂γ :=
                integral_mono_of_nonneg
                  (ae_of_all _ fun _ => Finset.prod_nonneg fun _ _ => cdf_nonneg _ _)
                  (integrable_const 1) (ae_of_all _ fun g0 =>
                    Finset.prod_le_one₀ (fun _ _ => cdf_nonneg _ _) (fun _ _ => cdf_le_one _ _))
            _ = 1 := by simp
        nlinarith [abs_nonneg (gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x),
          abs_nonneg (∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) ∂γ)]
    have hFA_int : Integrable FA γℓ := by
      have hmeas_int : StronglyMeasurable fun x : Fin ℓ → ℝ =>
          ∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ := by
        have hcont_g : Continuous fun p : (Fin ℓ → ℝ) × ℝ =>
            ∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (p.2 - A * (p.1 ⟨0, hℓ0⟩ - p.1 i)) :=
          continuous_finsetProd _ fun i _ =>
            (continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)
        exact hcont_g.stronglyMeasurable.integral_prod_right'
      refine Integrable.of_bound ((measurable_gaussianMaxIndicator ℓ ⟨0,
        hℓ0⟩).stronglyMeasurable.mul
          hmeas_int).aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
      dsimp only [FA]
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x| ≤ 1 := by
        simp only [gaussianMaxIndicator]; split_ifs <;> norm_num
      have h2 : |∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩,
          Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ| ≤ 1 := by
        have hnn : 0 ≤ ∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩,
            Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ :=
          integral_nonneg fun g0 => Finset.prod_nonneg fun _ _ => cdf_nonneg _ _
        rw [abs_of_nonneg hnn]
        calc ∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩,
                Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ
            ≤ ∫ _ : ℝ, (1 : ℝ) ∂γ :=
              integral_mono_of_nonneg
                (ae_of_all _ fun _ => Finset.prod_nonneg fun _ _ => cdf_nonneg _ _)
                (integrable_const 1) (ae_of_all _ fun g0 =>
                  Finset.prod_le_one₀ (fun _ _ => cdf_nonneg _ _) (fun _ _ => cdf_le_one _ _))
          _ = 1 := by simp
      nlinarith [abs_nonneg (gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x),
        abs_nonneg (∫ g0 : ℝ, (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩,
          Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) ∂γ)]
    have hnonneg : ∀ x : Fin ℓ → ℝ, 0 ≤ F0 x - FA x := by
      intro x
      dsimp only [F0, FA]
      rw [← mul_sub]
      by_cases hx : ∀ d : Fin ℓ, x d ≤ x ⟨0, hℓ0⟩
      · have hg : gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x = 1 := by
          simp [gaussianMaxIndicator, hx]
        rw [hg, one_mul, sub_nonneg]
        have hcont0 : Continuous fun g0 : ℝ => ∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0 :=
          continuous_finsetProd _ fun _ _ => continuous_cdf_gaussianReal 0 one_ne_zero
        refine integral_mono_of_nonneg
          (ae_of_all _ fun _ => Finset.prod_nonneg fun _ _ => cdf_nonneg _ _)
          (Integrable.of_bound hcont0.aestronglyMeasurable 1 (ae_of_all _ fun _ => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun _ _ => cdf_nonneg _ _)]
            exact Finset.prod_le_one₀ (fun _ _ => cdf_nonneg _ _) (fun _ _ => cdf_le_one _ _)))
          (ae_of_all _ fun g0 => Finset.prod_le_prod₀ (fun _ _ => cdf_nonneg _ _) fun i _ =>
            (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone (by nlinarith [hx i]))
      · simp [gaussianMaxIndicator, hx]
    let U : Set (Fin ℓ → ℝ) := Set.pi Set.univ fun i =>
      if i = ⟨0, hℓ0⟩ then Ioo 1 2 else Ioo 0 1
    have hU_meas : MeasurableSet U := MeasurableSet.univ_pi fun i => by
      split_ifs <;> exact measurableSet_Ioo
    have hU_pos : 0 < γℓ U := by
      dsimp only [γℓ, U]
      rw [Measure.pi_pi]
      have hpos_open : ∀ a b : ℝ, a < b → 0 < γ (Ioo a b) := fun a b hab => by
        have hlt := strictMono_cdf_gaussianReal 0 one_ne_zero hab
        rw [cdf_eq_real, cdf_eq_real] at hlt
        have hsub : Iic a ⊆ Iic b := Iic_subset_Iic.mpr hab.le
        have hdiff : Iic b \ Iic a = Ioc a b := by ext r; simp [and_comm]
        have hmeas_lt : γ (Iic a) < γ (Iic b) :=
          (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hlt
        have hpos_Ioc : 0 < γ (Ioc a b) := by
          rw [← hdiff, measure_sdiff hsub measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _)]
          exact tsub_pos_of_lt hmeas_lt
        have hnull_b : γ {b} = 0 :=
          have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
          measure_singleton b
        have hunion : Ioc a b = Ioo a b ∪ {b} := (Ioo_union_right hab).symm
        rw [hunion, measure_union (Set.disjoint_singleton_right.mpr (fun (h : b ∈ Ioo a b) =>
          lt_irrefl b h.2)) (measurableSet_singleton b), hnull_b, add_zero] at hpos_Ioc
        exact hpos_Ioc
      rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro i _
      split_ifs
      · exact (hpos_open 1 2 (by norm_num)).ne'
      · exact (hpos_open 0 1 (by norm_num)).ne'
    have hU_strict : ∀ x ∈ U, 0 < F0 x - FA x := by
      intro x hx
      have hx0 : x ⟨0, hℓ0⟩ ∈ Ioo (1 : ℝ) 2 := by simpa [U] using hx ⟨0, hℓ0⟩ (Set.mem_univ _)
      have hxi : ∀ i : Fin ℓ, i ≠ ⟨0, hℓ0⟩ → x i ∈ Ioo (0 : ℝ) 1 := fun i hi => by
        simpa [U, hi] using hx i (Set.mem_univ _)
      have hmax : ∀ d : Fin ℓ, x d ≤ x ⟨0, hℓ0⟩ := fun d => by
        by_cases hd : d = ⟨0, hℓ0⟩
        · subst hd; exact le_rfl
        · linarith [hx0.1, (hxi d hd).2]
      have hcont0 : Continuous fun g0 : ℝ => ∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0 :=
        continuous_finsetProd _ fun _ _ => continuous_cdf_gaussianReal 0 one_ne_zero
      have hcontA : Continuous fun g0 : ℝ =>
          ∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i)) :=
        continuous_finsetProd _ fun _ _ =>
          (continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)
      have hint0 : Integrable (fun g0 : ℝ => ∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) γ :=
        Integrable.of_bound hcont0.aestronglyMeasurable 1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun _ _ => cdf_nonneg _ _)]
          exact Finset.prod_le_one₀ (fun _ _ => cdf_nonneg _ _) (fun _ _ => cdf_le_one _ _))
      have hintA : Integrable (fun g0 : ℝ =>
          ∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))) γ :=
        Integrable.of_bound hcontA.aestronglyMeasurable 1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun _ _ => cdf_nonneg _ _)]
          exact Finset.prod_le_one₀ (fun _ _ => cdf_nonneg _ _) (fun _ _ => cdf_le_one _ _))
      dsimp only [F0, FA]
      have hg : gaussianMaxIndicator ℓ ⟨0, hℓ0⟩ x = 1 := by
        simp [gaussianMaxIndicator, hmax]
      rw [hg, one_mul, one_mul, ← integral_sub hint0 hintA]
      refine (integral_pos_iff_support_of_nonneg_ae ?_ (hint0.sub hintA)).mpr ?_
      · exact ae_of_all _ fun g0 => sub_nonneg.mpr
          (Finset.prod_le_prod₀ (fun _ _ => cdf_nonneg _ _) fun i _ =>
            (strictMono_cdf_gaussianReal 0 one_ne_zero).monotone (by nlinarith [hmax i]))
      · have hsupp : Function.support (fun g0 : ℝ =>
            (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) -
              (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i)))) = Set.univ := by
          ext g0
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          refine ne_of_gt (sub_pos.mpr ?_)
          have hne_set : (Finset.univ.filter fun i : Fin ℓ => i ≠ ⟨0, hℓ0⟩).Nonempty :=
            ⟨⟨1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Fin.ext_iff]⟩⟩
          refine Finset.prod_lt_prod_of_nonempty₀ (fun i _ =>
            cdf_pos (gaussianReal_absolutelyContinuous' 0 one_ne_zero) _)
            (fun i hi => by
              have hne : i ≠ ⟨0, hℓ0⟩ := (Finset.mem_filter.mp hi).2
              have hlt_x : x i < x ⟨0, hℓ0⟩ := lt_trans (hxi i hne).2 hx0.1
              exact strictMono_cdf_gaussianReal 0 one_ne_zero (by nlinarith))
            hne_set
        change 0 < γ (Function.support fun g0 : ℝ =>
          (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ g0) -
            (∏ i : Fin ℓ with i ≠ ⟨0, hℓ0⟩, Φ (g0 - A * (x ⟨0, hℓ0⟩ - x i))))
        rw [hsupp]
        simp
    rw [hP0, hPa, ← integral_sub hF0_int hFA_int]
    have hge : ∫ x in U, (F0 x - FA x) ∂γℓ ≤ ∫ x, (F0 x - FA x) ∂γℓ :=
      setIntegral_le_integral (hF0_int.sub hFA_int) (ae_of_all _ hnonneg)
    have hpos_U : 0 < ∫ x in U, (F0 x - FA x) ∂γℓ := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hnonneg)
        (hF0_int.sub hFA_int).integrableOn).mpr ?_
      have hsub : U ⊆ Function.support (fun x => F0 x - FA x) ∩ U :=
        fun x hx => ⟨ne_of_gt (hU_strict x hx), hx⟩
      exact lt_of_lt_of_le hU_pos (measure_mono hsub)
    linarith
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ0
  have hmul_lt := mul_lt_mul_of_pos_left (sub_pos.mp hdiff_pos) hℓ_pos
  have h0_val := friezeJerrumCollisionProb_zero hℓ0
  dsimp only [friezeJerrumCollisionProb] at h0_val ⊢
  linarith

end CslibFrontier.Algorithms.Semidefinite
