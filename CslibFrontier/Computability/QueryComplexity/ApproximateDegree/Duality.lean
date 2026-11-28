module

public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Probability.PMF
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximation–Orthogonality Duality for Boolean Functions

Proves the dual characterization of polynomial approximate degree on the Boolean hypercube via
finite-dimensional Hahn–Banach separation: whenever a real-valued function `f : {0, 1}^m → ℝ`
has `δ`-approximate degree `d ≥ 1` (`δ ≥ 0`), there exist a Boolean function `g : {0, 1}^m → Bool`
and a probability distribution `μ` on `{0, 1}^m` such that `signVal ∘ g` is orthogonal under `μ`
to every Fourier character of degree strictly less than `d`, while achieving correlation strictly
greater than `δ` with `f`.

## Main definitions

* `CslibFrontier.Computability.QueryComplexity.corr`: weighted correlation
  `|𝔼_{x ∼ μ} f(x) g(x)|` under a finite probability mass function.
* `CslibFrontier.Computability.QueryComplexity.IsOrthogonal`: `(μ, d)`-orthogonality of a
  Boolean function against all low-degree Fourier characters.
* `CslibFrontier.Computability.QueryComplexity.signApproxDegree`: `δ`-approximate degree of a
  real-valued function on `{0, 1}^m`.

## Main results

* `CslibFrontier.Computability.QueryComplexity.IsOrthogonal.sum_mul_eq_zero`: orthogonality
  extends from characters `χ_S` (`|S| < d`) to the entire subspace `lowDegree ℝ (Fin m) D`
  (`D < d`).
* `CslibFrontier.Computability.QueryComplexity.signApproxDegree_signVal_eq_approxDegree`: exact
  bridge `signApproxDegree δ (signVal ∘ f) = approxDegree (δ / 2) f`.
* `CslibFrontier.Computability.QueryComplexity.exists_orthogonal_and_corr_gt`: dual witness
  existence via geometric Hahn–Banach separation.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity Finset
open scoped BigOperators ENNReal NNReal

/-- Correlation `|𝔼_{x ∼ μ} f(x) g(x)|` of two real functions under a finite `PMF`. -/
noncomputable def corr {α : Type*} [Fintype α] (μ : PMF α) (f g : α → ℝ) : ℝ :=
  |∑ x, (μ x).toReal * f x * g x|

/-- Explicit formula for `corr`. -/
theorem corr_eq_abs_sum {α : Type*} [Fintype α] (μ : PMF α) (f g : α → ℝ) :
    corr μ f g = |∑ x, (μ x).toReal * f x * g x| := by
  rw [corr]

/-- A Boolean function `f : {0, 1}^m → Bool` (read in `{-1, +1}` via `signVal`) is
`(μ, d)`-orthogonal if `𝔼_{x ∼ μ} signVal(f(x)) χ_S(x) = 0` for every subset `S ⊆ Fin m` of
cardinality strictly less than `d`. -/
def IsOrthogonal {m : ℕ} (μ : PMF (BitString m)) (d : ℕ) (f : BooleanFunction m) : Prop :=
  ∀ S : Finset (Fin m), #S < d →
    ∑ x : BitString m, (μ x).toReal * signVal (f x) * chi ℝ S x = 0

/-- Explicit characterization of `IsOrthogonal`. -/
theorem isOrthogonal_iff {m : ℕ} (μ : PMF (BitString m)) (d : ℕ) (f : BooleanFunction m) :
    IsOrthogonal μ d f ↔
      ∀ S : Finset (Fin m), #S < d →
        ∑ x : BitString m, (μ x).toReal * signVal (f x) * chi ℝ S x = 0 := by
  rw [IsOrthogonal]

/-- If `f` is `(μ, d)`-orthogonal, then `∑_x μ(x) signVal(f(x)) p(x) = 0` for every real function
`p` of degree strictly less than `d`. -/
theorem IsOrthogonal.sum_mul_eq_zero {m d : ℕ} {μ : PMF (BitString m)} {f : BooleanFunction m}
    (hf : IsOrthogonal μ d f) {p : BitString m → ℝ} {D : ℕ} (hD : D < d)
    (hp : p ∈ lowDegree ℝ (Fin m) D) :
    ∑ x : BitString m, (μ x).toReal * signVal (f x) * p x = 0 := by
  have hexp : ∀ x, p x = ∑ S : Finset (Fin m), fourierCoeff p S * chi ℝ S x :=
    fun x => (sum_fourierCoeff_mul_chi p x).symm
  calc ∑ x, (μ x).toReal * signVal (f x) * p x
      = ∑ x, (μ x).toReal * signVal (f x) * ∑ S, fourierCoeff p S * chi ℝ S x :=
          Finset.sum_congr rfl fun x _ => by rw [hexp x]
    _ = ∑ S, fourierCoeff p S * ∑ x, (μ x).toReal * signVal (f x) * chi ℝ S x := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => by ring
    _ = 0 := by
          refine Finset.sum_eq_zero fun S _ => ?_
          by_cases hS : #S < d
          · rw [hf S hS, mul_zero]
          · have hgt : D < #S := by omega
            rw [fourierCoeff_eq_zero_of_mem_lowDegree hp hgt, zero_mul]

/-- The `δ`-approximate degree of a real-valued function `f : {0, 1}^m → ℝ`: the least degree `D`
such that some `p ∈ lowDegree ℝ (Fin m) D` satisfies `|f x - p x| ≤ δ` for all `x`. -/
noncomputable def signApproxDegree {m : ℕ} (δ : ℝ) (f : BitString m → ℝ) : ℕ :=
  sInf {D | ∃ p ∈ lowDegree ℝ (Fin m) D, ∀ x, |f x - p x| ≤ δ}

/-- A polynomial of degree at most `D` approximating `f` within `δ` bounds `signApproxDegree δ f`
by `D`. -/
theorem signApproxDegree_le_of_mem_lowDegree {m D : ℕ} {δ : ℝ} {f p : BitString m → ℝ}
    (hp : p ∈ lowDegree ℝ (Fin m) D) (h : ∀ x, |f x - p x| ≤ δ) :
    signApproxDegree δ f ≤ D :=
  Nat.sInf_le ⟨p, hp, h⟩

/-- For nonnegative `δ`, the `δ`-approximate degree is attained. -/
theorem exists_mem_lowDegree_signApproxDegree {m : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : BitString m → ℝ) :
    ∃ p ∈ lowDegree ℝ (Fin m) (signApproxDegree δ f), ∀ x, |f x - p x| ≤ δ :=
  Nat.sInf_mem (s := {D | ∃ p ∈ lowDegree ℝ (Fin m) D, ∀ x, |f x - p x| ≤ δ})
    ⟨m, f, by simpa using mem_lowDegree_self f, fun x => by simpa using hδ⟩

/-- Exact bridge between `signApproxDegree` (in `{-1, +1}` values) and
`Cslib.QueryComplexity.approxDegree` (in `{0, 1}` values). -/
theorem signApproxDegree_signVal_eq_approxDegree {m : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : BooleanFunction m) :
    signApproxDegree δ (fun x => signVal (f x)) =
      approxDegree (⟨δ / 2, by positivity⟩ : ℝ≥0) f := by
  let ε : ℝ≥0 := ⟨δ / 2, by positivity⟩
  change signApproxDegree δ (fun x => signVal (f x)) = approxDegree ε f
  have hcoe : (ε : ℝ) = δ / 2 := rfl
  unfold signApproxDegree approxDegree
  congr 1
  ext D
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, hqf⟩
    refine ⟨(2⁻¹ : ℝ) • (1 - q), Submodule.smul_mem _ _ (one_sub_mem_lowDegree hq), fun x => ?_⟩
    have hx := hqf x
    rw [signVal_eq_one_sub_two_mul_bitVal] at hx
    have hdiff : ((2⁻¹ : ℝ) • (1 - q)) x - bitVal ℝ (f x) =
        (1 - 2 * bitVal ℝ (f x) - q x) / 2 := by
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
      ring
    rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), hcoe]
    linarith
  · rintro ⟨p, hp, hpf⟩
    refine ⟨1 - (2 : ℝ) • p, one_sub_mem_lowDegree (Submodule.smul_mem _ _ hp), fun x => ?_⟩
    have hx := hpf x
    rw [hcoe] at hx
    rw [signVal_eq_one_sub_two_mul_bitVal]
    have hdiff : 1 - 2 * bitVal ℝ (f x) - (1 - (2 : ℝ) • p) x =
        2 * (p x - bitVal ℝ (f x)) := by
      simp only [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-- **Approximation–orthogonality duality**: if `f : {0, 1}^m → ℝ` satisfies
`signApproxDegree δ f = d ≥ 1` (`δ ≥ 0`), then there exist a Boolean function
`g : BooleanFunction m` and a probability distribution `μ` on `BitString m` such that `g` is
`(μ, d)`-orthogonal and `corr μ f (signVal ∘ g) > δ`. -/
theorem exists_orthogonal_and_corr_gt {m d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {f : BitString m → ℝ} (hd : signApproxDegree δ f = d) (hd1 : 1 ≤ d) :
    ∃ (g : BooleanFunction m) (μ : PMF (BitString m)),
      IsOrthogonal μ d g ∧ δ < corr μ f (fun x => signVal (g x)) := by
  classical
  let V : Submodule ℝ (BitString m → ℝ) := lowDegree ℝ (Fin m) (d - 1)
  let K : Set (BitString m → ℝ) := Metric.closedBall f δ
  have hV_conv : Convex ℝ (V : Set (BitString m → ℝ)) := V.convex
  have hV_closed : IsClosed (V : Set (BitString m → ℝ)) :=
    Submodule.isClosed_of_finiteDimensional V
  have hK_conv : Convex ℝ K := convex_closedBall f δ
  have hK_comp : IsCompact K := isCompact_closedBall f δ
  have hdisj : Disjoint (V : Set (BitString m → ℝ)) K := by
    rw [Set.disjoint_left]
    intro p hpV hpK
    have hp_err : ∀ x : BitString m, |f x - p x| ≤ δ := by
      intro x
      have hdist : dist p f ≤ δ := Metric.mem_closedBall.mp hpK
      have hpi : dist (p x) (f x) ≤ δ := (dist_pi_le_iff hδ).mp hdist x
      rw [Real.dist_eq, abs_sub_comm] at hpi
      exact hpi
    have hlt : d - 1 < signApproxDegree δ f := by omega
    exact absurd (signApproxDegree_le_of_mem_lowDegree hpV hp_err) (not_le.mpr hlt)
  obtain ⟨L, u, v, hLV, huv, hLK⟩ :=
    geometric_hahn_banach_closed_compact hV_conv hV_closed hK_conv hK_comp hdisj
  have hL_zero_on_V : ∀ p ∈ V, L p = 0 := by
    intro p hp
    by_contra hne
    set t : ℝ := (|u| + 1) / L p
    have htp : t • p ∈ V := V.smul_mem t hp
    have hlt := hLV (t • p) htp
    rw [map_smul, smul_eq_mul] at hlt
    have heq : t * L p = |u| + 1 := div_mul_cancel₀ _ hne
    rw [heq] at hlt
    linarith [le_abs_self u]
  have hv_pos : 0 < v := by
    have h0 : L 0 < u := hLV 0 V.zero_mem
    rw [map_zero] at h0
    linarith
  let w : BitString m → ℝ := fun x => L (Pi.single x (1 : ℝ))
  have hL_sum (y : BitString m → ℝ) : L y = ∑ x : BitString m, y x * w x := by
    have hy : y = ∑ x : BitString m, y x • Pi.single x (1 : ℝ) := by
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => by simp [w]
  let h : BitString m → ℝ := fun x => if 0 ≤ w x then δ else -δ
  have hfmh_mem : f - h ∈ K := by
    rw [Metric.mem_closedBall, dist_pi_le_iff hδ]
    intro x
    rw [Real.dist_eq, Pi.sub_apply, show f x - h x - f x = -h x by ring, abs_neg]
    simp only [h]
    split_ifs <;> simp [abs_of_nonneg hδ]
  have hL_fmh : 0 < L (f - h) := lt_trans hv_pos (hLK (f - h) hfmh_mem)
  have hL_fmh_eq : L (f - h) = (∑ x, f x * w x) - δ * ∑ x, |w x| := by
    rw [hL_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.sub_apply, h]
    split_ifs with hw
    · rw [abs_of_nonneg hw]; ring
    · rw [abs_of_neg (not_le.mp hw)]; ring
  set Z : ℝ := ∑ x : BitString m, |w x|
  have hZ_pos : 0 < Z := by
    have hZ_nn : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases eq_or_lt_of_le hZ_nn with hZ0 | hZpos
    · exfalso
      have hw0 : ∀ x : BitString m, w x = 0 := fun x =>
        abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).mp hZ0.symm
          x (mem_univ x))
      have hzero : L (f - h) = 0 := by rw [hL_sum]; simp [hw0]
      linarith
    · exact hZpos
  let μ : PMF (BitString m) :=
    PMF.ofFintype (fun x => ENNReal.ofReal (|w x| / Z)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg (abs_nonneg _) hZ_pos.le),
        ← Finset.sum_div, div_self hZ_pos.ne', ENNReal.ofReal_one])
  let g : BooleanFunction m := fun x => decide (w x < 0)
  have hμ_sign (x : BitString m) : (μ x).toReal * signVal (g x) = w x / Z := by
    have hμx : (μ x).toReal = |w x| / Z := by
      simp only [μ, PMF.ofFintype_apply]
      exact ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hZ_pos.le)
    rw [hμx]
    by_cases hw : w x < 0
    · simp only [g, decide_eq_true hw, signVal_true, abs_of_neg hw]
      ring
    · simp only [g, decide_eq_false hw, signVal_false, abs_of_nonneg (not_lt.mp hw)]
      ring
  refine ⟨g, μ, ?_, ?_⟩
  · rw [isOrthogonal_iff]
    intro S hS
    have hchi_mem : chi ℝ S ∈ V := lowDegree_mono (by omega) (chi_mem_lowDegree S)
    have hL_chi : L (chi ℝ S) = 0 := hL_zero_on_V (chi ℝ S) hchi_mem
    rw [hL_sum] at hL_chi
    calc ∑ x : BitString m, (μ x).toReal * signVal (g x) * chi ℝ S x
        = ∑ x : BitString m, (chi ℝ S x * w x) / Z :=
            Finset.sum_congr rfl fun x _ => by rw [hμ_sign x]; ring
      _ = (∑ x : BitString m, chi ℝ S x * w x) / Z := (Finset.sum_div _ _ _).symm
      _ = 0 := by rw [hL_chi, zero_div]
  · rw [corr_eq_abs_sum]
    have hsum_eq : ∑ x : BitString m, (μ x).toReal * f x * signVal (g x) =
        (∑ x : BitString m, f x * w x) / Z := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => by
        rw [show (μ x).toReal * f x * signVal (g x) = f x * ((μ x).toReal * signVal (g x)) by ring,
          hμ_sign x]
        ring
    have hgt : δ < (∑ x : BitString m, f x * w x) / Z := by
      rw [lt_div_iff₀ hZ_pos]
      linarith
    exact lt_of_lt_of_le hgt (by rw [← hsum_eq]; exact le_abs_self _)

end CslibFrontier.Computability.QueryComplexity
