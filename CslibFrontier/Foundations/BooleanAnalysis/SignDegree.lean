/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Order.IntermediateValue

/-!
# Sign-Degree, Pure High Degree, and Symmetric Boolean Functions

This module develops textbook results on polynomial sign-representations and Fourier spectrum
degrees of Boolean functions under standard Lean axioms.

Reading bits `b : Bool` as real signs `Cslib.BitString.signVal b ∈ {-1, 1}` (`false ↦ 1`,
`true ↦ -1`), a real function `p : (ι → Bool) → ℝ` *sign-represents* `f : (ι → Bool) → Bool`
when `0 < signVal (f x) * p x` for all `x`. The *sign-degree*
(`CslibFrontier.BooleanAnalysis.signDegree`) is the least polynomial degree `d`
(`p ∈ Cslib.BitString.lowDegree ℝ ι d`) of a sign-representing polynomial, while the *pure high
degree* (`CslibFrontier.BooleanAnalysis.pureHighDegree`) is the minimum cardinality `#S` of a
nonzero Fourier coefficient of `x ↦ signVal (f x)`.

## Main definitions

* `CslibFrontier.BooleanAnalysis.signFn`: real `±1`-valued representation `x ↦ signVal (f x)`.
* `CslibFrontier.BooleanAnalysis.IsSignRepresentedBy`: strict sign agreement
  `0 < signVal (f x) * p x`.
* `CslibFrontier.BooleanAnalysis.IsNormalizedPoly`: uniform bound `∀ x, |p x| ≤ 1`.
* `CslibFrontier.BooleanAnalysis.polyBias`: minimum magnitude `min_x |p x|` on the Boolean cube.
* `CslibFrontier.BooleanAnalysis.signDegree`: minimum degree of a sign-representing polynomial
  for `f`.
* `CslibFrontier.BooleanAnalysis.fourierL1Norm`: spectral `ℓ₁` norm `∑_S |f̂(S)|`.
* `CslibFrontier.BooleanAnalysis.pureHighDegree`: minimum Fourier level `#S` with `f̂(S) ≠ 0`.
* `CslibFrontier.BooleanAnalysis.layerVal`, `CslibFrontier.BooleanAnalysis.signChanges`:
  Hamming-weight layer
  evaluation and univariate sign-change count on `{0, …, t}`.

## Main results

* `CslibFrontier.BooleanAnalysis.signDegree_le_iff_normalized`: sign-degree `≤ d` is achieved by a
  normalized sign-representing polynomial with positive bias.
* `CslibFrontier.BooleanAnalysis.abs_fourierCoeff_empty_add_sum_singleton_le_one`: any normalized
  degree-`≤ 1` polynomial `p(x) = α₀ + ∑ᵢ αᵢ xᵢ` satisfies `|α₀| + ∑ᵢ |αᵢ| ≤ 1`.
* `CslibFrontier.BooleanAnalysis.pureHighDegree_le_signDegree`: duality bound `phdeg(f) ≤ sdeg(f)`.
* `CslibFrontier.BooleanAnalysis.sum_pow_card_mul_fourierCoeff_sq_le`: Kahn–Kalai–Linial /
  Bonami–Beckner hypercontractive level-weight bound for `{-1, 0, 1}`-valued functions.
* `CslibFrontier.BooleanAnalysis.signDegree_eq_signChanges`: Aspnes–Beigel–Furst–Rudich theorem
  that the
  sign-degree of a symmetric Boolean function equals its number of Hamming-weight sign changes.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Finset Cslib Cslib.BitString
open scoped BigOperators

section GeneralCube

variable {ι : Type*}

/-- The `±1`-valued real representation `x ↦ signVal (f x)` of a Boolean function `f`. -/
@[expose]
def signFn (f : (ι → Bool) → Bool) (x : ι → Bool) : ℝ :=
  signVal (f x)

/-- Pointwise evaluation of `signFn`. -/
@[simp]
theorem signFn_apply (f : (ι → Bool) → Bool) (x : ι → Bool) :
    signFn f x = signVal (f x) := by
  rfl

/-- A real function `p` *sign-represents* `f` on the Boolean cube when `p x` has the same strict
nonzero sign as `signVal (f x)` at every point `x`. -/
def IsSignRepresentedBy (f : (ι → Bool) → Bool) (p : (ι → Bool) → ℝ) : Prop :=
  ∀ x, 0 < signVal (f x) * p x

/-- Characterization of `IsSignRepresentedBy` by pointwise strict sign agreement. -/
theorem isSignRepresentedBy_iff {f : (ι → Bool) → Bool} {p : (ι → Bool) → ℝ} :
    IsSignRepresentedBy f p ↔ ∀ x, 0 < signVal (f x) * p x :=
  Iff.rfl

/-- A real polynomial `p` on the Boolean cube is *normalized* when `|p x| ≤ 1` everywhere. -/
def IsNormalizedPoly (p : (ι → Bool) → ℝ) : Prop :=
  ∀ x, |p x| ≤ 1

/-- Characterization of `IsNormalizedPoly`. -/
theorem isNormalizedPoly_iff {p : (ι → Bool) → ℝ} :
    IsNormalizedPoly p ↔ ∀ x, |p x| ≤ 1 :=
  Iff.rfl

/-- Every Boolean function is sign-represented by its own `±1` function `signFn f`. -/
theorem isSignRepresentedBy_signFn (f : (ι → Bool) → Bool) :
    IsSignRepresentedBy f (signFn f) := by
  intro x
  rw [signFn_apply, signVal_mul_self]
  exact zero_lt_one

/-- `signFn f` is normalized on the Boolean cube. -/
theorem isNormalizedPoly_signFn (f : (ι → Bool) → Bool) :
    IsNormalizedPoly (signFn f) := by
  intro x
  rw [signFn_apply, abs_signVal]

/-- Positive scaling preserves `IsSignRepresentedBy`. -/
theorem IsSignRepresentedBy.const_mul {f : (ι → Bool) → Bool} {p : (ι → Bool) → ℝ}
    (hp : IsSignRepresentedBy f p) {c : ℝ} (hc : 0 < c) :
    IsSignRepresentedBy f (fun x ↦ c * p x) := by
  intro x
  have hx := hp x
  nlinarith

/-- If `p` sign-represents `f`, then `signVal (f x) * p x = |p x|` at every input `x`. -/
theorem IsSignRepresentedBy.signVal_mul_eq_abs {f : (ι → Bool) → Bool} {p : (ι → Bool) → ℝ}
    (hp : IsSignRepresentedBy f p) (x : ι → Bool) :
    signVal (f x) * p x = |p x| := by
  have hx := hp x
  have habs : |signVal (f x) * p x| = |p x| := by
    rw [abs_mul, abs_signVal, one_mul]
  rw [← habs, abs_of_pos hx]

end GeneralCube

section FiniteCube

variable {ι : Type*} [Fintype ι]

/-- The *bias* `β = min_x |p x|` of a real polynomial `p` on a finite Boolean cube. -/
noncomputable def polyBias (p : (ι → Bool) → ℝ) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (fun x ↦ |p x|)

/-- The bias of `p` lower-bounds `|p x|` at every point `x`. -/
theorem polyBias_le_abs (p : (ι → Bool) → ℝ) (x : ι → Bool) :
    polyBias p ≤ |p x| := by
  classical
  unfold polyBias
  exact Finset.inf'_le (fun y ↦ |p y|) (Finset.mem_univ x)

/-- The bias of any polynomial on the Boolean cube is nonnegative. -/
theorem polyBias_nonneg (p : (ι → Bool) → ℝ) : 0 ≤ polyBias p := by
  classical
  obtain ⟨x, -, hx⟩ :=
    Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (ι → Bool)))
      Finset.univ_nonempty (fun y : ι → Bool ↦ |p y|)
  unfold polyBias
  rw [hx]
  exact abs_nonneg (p x)

/-- If `p` sign-represents `f`, then `polyBias p` is strictly positive. -/
theorem IsSignRepresentedBy.polyBias_pos {f : (ι → Bool) → Bool} {p : (ι → Bool) → ℝ}
    (hp : IsSignRepresentedBy f p) : 0 < polyBias p := by
  classical
  unfold polyBias
  rw [Finset.lt_inf'_iff]
  intro x _
  rw [← hp.signVal_mul_eq_abs x]
  exact hp x

/-- If `p` is normalized, then `polyBias p ≤ 1`. -/
theorem IsNormalizedPoly.polyBias_le_one {p : (ι → Bool) → ℝ} (hp : IsNormalizedPoly p) :
    polyBias p ≤ 1 :=
  (polyBias_le_abs p (fun _ ↦ false)).trans (hp _)

/-- The *sign-degree* `sdeg(f)` of a Boolean function `f : (ι → Bool) → Bool`: the minimum degree
`d` of a real polynomial `p ∈ lowDegree ℝ ι d` that sign-represents `f`. -/
noncomputable def signDegree (f : (ι → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find
    (⟨Fintype.card ι, signFn f, mem_lowDegree_self (signFn f), isSignRepresentedBy_signFn f⟩ :
      ∃ d : ℕ, ∃ p ∈ lowDegree ℝ ι d, IsSignRepresentedBy f p)

/-- `signDegree f ≤ d` holds if and only if some polynomial in `lowDegree ℝ ι d` sign-represents
`f`. -/
theorem signDegree_le_iff {f : (ι → Bool) → Bool} {d : ℕ} :
    signDegree f ≤ d ↔ ∃ p ∈ lowDegree ℝ ι d, IsSignRepresentedBy f p := by
  classical
  rw [signDegree, Nat.find_le_iff]
  refine ⟨fun ⟨k, hk, p, hp, hrep⟩ ↦ ⟨p, lowDegree_mono hk hp, hrep⟩,
    fun ⟨p, hp, hrep⟩ ↦ ⟨d, le_rfl, p, hp, hrep⟩⟩

/-- Every Boolean function on `ι → Bool` has sign-degree at most `Fintype.card ι`. -/
theorem signDegree_le_card (f : (ι → Bool) → Bool) :
    signDegree f ≤ Fintype.card ι :=
  signDegree_le_iff.mpr ⟨signFn f, mem_lowDegree_self (signFn f), isSignRepresentedBy_signFn f⟩

/-- There exists a polynomial of degree `≤ signDegree f` that sign-represents `f`. -/
theorem exists_isSignRepresentedBy_signDegree (f : (ι → Bool) → Bool) :
    ∃ p ∈ lowDegree ℝ ι (signDegree f), IsSignRepresentedBy f p :=
  signDegree_le_iff.mp le_rfl

/-- `signDegree f ≤ d` holds if and only if some *normalized* polynomial in `lowDegree ℝ ι d`
sign-represents `f`. -/
theorem signDegree_le_iff_normalized {f : (ι → Bool) → Bool} {d : ℕ} :
    signDegree f ≤ d ↔
      ∃ p ∈ lowDegree ℝ ι d, IsNormalizedPoly p ∧ IsSignRepresentedBy f p := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨p, hp, _, hrep⟩ ↦ signDegree_le_iff.mpr ⟨p, hp, hrep⟩⟩
  obtain ⟨p, hp, hrep⟩ := signDegree_le_iff.mp h
  let hne : (Finset.univ : Finset (ι → Bool)).Nonempty := ⟨fun _ ↦ false, Finset.mem_univ _⟩
  let M : ℝ := Finset.univ.sup' hne (fun x ↦ |p x|)
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hrep.polyBias_pos
      ((polyBias_le_abs p (fun _ ↦ false)).trans
        (Finset.le_sup' (fun x : ι → Bool ↦ |p x|) (Finset.mem_univ _)))
  refine ⟨M⁻¹ • p, Submodule.smul_mem _ M⁻¹ hp, fun x ↦ ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hM_pos)]
    rw [inv_mul_le_iff₀ hM_pos, mul_one]
    exact Finset.le_sup' (fun y : ι → Bool ↦ |p y|) (Finset.mem_univ x)
  · exact hrep.const_mul (inv_pos.mpr hM_pos)

/-- Negating a Boolean function preserves its sign-degree. -/
theorem signDegree_not (f : (ι → Bool) → Bool) :
    signDegree (fun x ↦ !f x) = signDegree f := by
  apply le_antisymm
  · obtain ⟨p, hp, hrep⟩ := exists_isSignRepresentedBy_signDegree f
    refine signDegree_le_iff.mpr ⟨-p, Submodule.neg_mem _ hp, fun x ↦ ?_⟩
    simpa only [signVal_not, Pi.neg_apply, neg_mul_neg] using hrep x
  · obtain ⟨p, hp, hrep⟩ := exists_isSignRepresentedBy_signDegree (fun x ↦ !f x)
    refine signDegree_le_iff.mpr ⟨-p, Submodule.neg_mem _ hp, fun x ↦ ?_⟩
    have hx := hrep x
    rw [signVal_not] at hx
    simp only [Pi.neg_apply]
    linarith

end FiniteCube

section FourierAndPureHighDegree

variable {ι : Type*} [Fintype ι]

/-- Any degree-`≤ 1` real polynomial on `ι → Bool` expands in the linear Fourier basis
`p x = p̂(∅) + ∑ᵢ p̂({i}) signVal (x i)`. -/
theorem eq_fourierCoeff_empty_add_sum_singleton [DecidableEq ι] {p : (ι → Bool) → ℝ}
    (hp : p ∈ lowDegree ℝ ι 1) (x : ι → Bool) :
    p x = fourierCoeff p ∅ + ∑ i : ι, fourierCoeff p {i} * signVal (x i) := by
  rw [← sum_fourierCoeff_mul_chi p x]
  have hsplit : (∑ S : Finset ι, fourierCoeff p S * chi ℝ S x) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 1),
        fourierCoeff p S * chi ℝ S x := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun S _ hS ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hS
    rw [fourierCoeff_eq_zero_of_mem_lowDegree hp hS, zero_mul]
  rw [hsplit]
  have hcard1 : (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 1) =
      insert (∅ : Finset ι) (Finset.univ.image (fun i : ι ↦ ({i} : Finset ι))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · intro hS
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with h0 | h1
      · exact Or.inl (Finset.card_eq_zero.mp h0)
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
        exact Or.inr ⟨i, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
  rw [hcard1, Finset.sum_insert (by simp), chi_empty, mul_one,
    Finset.sum_image (fun i _ j _ hij ↦ Finset.singleton_injective hij)]
  refine congrArg (fourierCoeff p ∅ + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [chi_singleton]

/-- If `p ∈ lowDegree ℝ ι 1` is normalized (`|p x| ≤ 1` for all `x`), then the sum of absolute
values of its constant and degree-`1` Fourier coefficients is at most `1`. -/
theorem abs_fourierCoeff_empty_add_sum_singleton_le_one [DecidableEq ι] {p : (ι → Bool) → ℝ}
    (hp : p ∈ lowDegree ℝ ι 1) (hnorm : IsNormalizedPoly p) :
    |fourierCoeff p ∅| + ∑ i : ι, |fourierCoeff p {i}| ≤ 1 := by
  have hs_abs (r : ℝ) : signVal (decide (r < 0)) * r = |r| := by
    by_cases hr : r < 0
    · rw [decide_eq_true hr, signVal_true, neg_one_mul, abs_of_neg hr]
    · rw [decide_eq_false hr, signVal_false, one_mul, abs_of_nonneg (not_lt.mp hr)]
  let s₀ : Bool := decide (fourierCoeff p ∅ < 0)
  let s₁ : ι → Bool := fun i ↦ decide (fourierCoeff p {i} < 0)
  let x : ι → Bool := fun i ↦ xor s₀ (s₁ i)
  have hs₀ : signVal s₀ * fourierCoeff p ∅ = |fourierCoeff p ∅| := hs_abs _
  have hs₁ (i : ι) : signVal (s₁ i) * fourierCoeff p {i} = |fourierCoeff p {i}| := hs_abs _
  have hval : signVal s₀ * p x = |fourierCoeff p ∅| + ∑ i : ι, |fourierCoeff p {i}| := by
    rw [eq_fourierCoeff_empty_add_sum_singleton hp x, mul_add, hs₀, Finset.mul_sum]
    refine congrArg (|fourierCoeff p ∅| + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    dsimp only [x]
    rw [signVal_xor]
    calc
      signVal s₀ * (fourierCoeff p {i} * (signVal s₀ * signVal (s₁ i)))
          = (signVal s₀ * signVal s₀) * (signVal (s₁ i) * fourierCoeff p {i}) := by ring
      _ = |fourierCoeff p {i}| := by rw [signVal_mul_self, one_mul, hs₁]
  calc
    |fourierCoeff p ∅| + ∑ i : ι, |fourierCoeff p {i}|
        = signVal s₀ * p x := hval.symm
    _ ≤ |p x| := signVal_mul_le_abs s₀ (p x)
    _ ≤ 1 := hnorm x

/-- The spectral `ℓ₁` norm `∑_{S ⊆ ι} |f̂(S)|` of a Boolean function `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def fourierL1Norm [DecidableEq ι] (f : (ι → Bool) → Bool) : ℝ :=
  ∑ S : Finset ι, |fourierCoeff (signFn f) S|

/-- Sum expansion of `fourierL1Norm` over all Fourier subsets. -/
theorem fourierL1Norm_eq_sum [DecidableEq ι] (f : (ι → Bool) → Bool) :
    fourierL1Norm f = ∑ S : Finset ι, |fourierCoeff (signFn f) S| :=
  rfl

/-- Every Boolean function has spectral `ℓ₁` norm at least `1`. -/
theorem one_le_fourierL1Norm [DecidableEq ι] (f : (ι → Bool) → Bool) :
    1 ≤ fourierL1Norm f := by
  rw [← sum_fourierCoeff_sq_signVal f, fourierL1Norm]
  refine Finset.sum_le_sum fun S _ ↦ ?_
  have habs : |fourierCoeff (signFn f) S| ≤ 1 := abs_fourierCoeff_signVal_le_one f S
  have hsq : fourierCoeff (fun x ↦ signVal (f x)) S ^ 2 = |fourierCoeff (signFn f) S| ^ 2 :=
    (sq_abs _).symm
  rw [hsq]
  nlinarith [abs_nonneg (fourierCoeff (signFn f) S)]

private theorem exists_fourierCoeff_signFn_ne_zero [DecidableEq ι]
    (f : (ι → Bool) → Bool) :
    ∃ d : ℕ, ∃ S : Finset ι, #S = d ∧ fourierCoeff (signFn f) S ≠ 0 := by
  by_contra h
  push Not at h
  have hsum : ∑ S : Finset ι, fourierCoeff (fun x ↦ signVal (f x)) S ^ 2 = 0 :=
    Finset.sum_eq_zero fun S _ ↦ by
      have h0 : fourierCoeff (signFn f) S = 0 := h #S S rfl
      change fourierCoeff (signFn f) S ^ 2 = 0
      rw [h0, sq, mul_zero]
  linarith [sum_fourierCoeff_sq_signVal f]

/-- The *pure high degree* `phdeg(f)` of a Boolean function `f : (ι → Bool) → Bool`: the smallest
cardinality `#S` of a subset `S : Finset ι` with `fourierCoeff (signFn f) S ≠ 0`. -/
noncomputable def pureHighDegree (f : (ι → Bool) → Bool) : ℕ :=
  @Nat.find _ (Classical.decPred _)
    (@exists_fourierCoeff_signFn_ne_zero ι _ (Classical.typeDecidableEq ι) f)

/-- Every Fourier coefficient strictly below `pureHighDegree f` vanishes. -/
theorem fourierCoeff_eq_zero_of_card_lt_pureHighDegree [inst : DecidableEq ι]
    {f : (ι → Bool) → Bool} {S : Finset ι}
    (hS : #S < pureHighDegree f) : fourierCoeff (signFn f) S = 0 := by
  obtain rfl : inst = Classical.typeDecidableEq ι := Subsingleton.elim _ _
  unfold pureHighDegree at hS
  by_contra hne
  exact @Nat.find_min _ (Classical.decPred _)
    (@exists_fourierCoeff_signFn_ne_zero ι _ (Classical.typeDecidableEq ι) f) _ hS ⟨S, rfl, hne⟩

/-- There exists a Fourier support set `S` of size `pureHighDegree f` with `f̂(S) ≠ 0`. -/
theorem exists_card_eq_pureHighDegree [inst : DecidableEq ι] (f : (ι → Bool) → Bool) :
    ∃ S : Finset ι, #S = pureHighDegree f ∧ fourierCoeff (signFn f) S ≠ 0 := by
  obtain rfl : inst = Classical.typeDecidableEq ι := Subsingleton.elim _ _
  unfold pureHighDegree
  exact @Nat.find_spec _ (Classical.decPred _)
    (@exists_fourierCoeff_signFn_ne_zero ι _ (Classical.typeDecidableEq ι) f)

/-- `d ≤ pureHighDegree f` holds if and only if `f̂(S) = 0` for all `#S < d`. -/
theorem le_pureHighDegree_iff [DecidableEq ι] {f : (ι → Bool) → Bool} {d : ℕ} :
    d ≤ pureHighDegree f ↔ ∀ S : Finset ι, #S < d → fourierCoeff (signFn f) S = 0 := by
  refine ⟨fun hd S hS ↦ fourierCoeff_eq_zero_of_card_lt_pureHighDegree (lt_of_lt_of_le hS hd),
    fun h ↦ ?_⟩
  obtain ⟨S, hcard, hne⟩ := exists_card_eq_pureHighDegree f
  by_contra hlt
  exact hne (h S (hcard.trans_lt (not_le.mp hlt)))

/-- Characterization of `pureHighDegree f = d`. -/
theorem pureHighDegree_eq_iff [DecidableEq ι] {f : (ι → Bool) → Bool} {d : ℕ} :
    pureHighDegree f = d ↔
      (∀ S : Finset ι, #S < d → fourierCoeff (signFn f) S = 0) ∧
        (∃ S : Finset ι, #S = d ∧ fourierCoeff (signFn f) S ≠ 0) := by
  constructor
  · rintro rfl
    exact ⟨fun S hS ↦ fourierCoeff_eq_zero_of_card_lt_pureHighDegree hS,
      exists_card_eq_pureHighDegree f⟩
  · rintro ⟨hzero, ⟨S, rfl, hne⟩⟩
    apply le_antisymm
    · by_contra hgt
      exact hne (fourierCoeff_eq_zero_of_card_lt_pureHighDegree (not_le.mp hgt))
    · exact le_pureHighDegree_iff.mpr hzero

/-- Every Boolean function on `ι → Bool` has pure high degree at most `Fintype.card ι`. -/
theorem pureHighDegree_le_card (f : (ι → Bool) → Bool) :
    pureHighDegree f ≤ Fintype.card ι := by
  classical
  obtain ⟨S, hcard, -⟩ := exists_card_eq_pureHighDegree f
  exact hcard.symm.trans_le (Finset.card_le_univ S)

/-- **Duality bound between pure high degree and sign-degree**:
`pureHighDegree f ≤ signDegree f` for every Boolean function `f`.
-/
theorem pureHighDegree_le_signDegree (f : (ι → Bool) → Bool) :
    pureHighDegree f ≤ signDegree f := by
  classical
  obtain ⟨p, hp, hrep⟩ := exists_isSignRepresentedBy_signDegree f
  by_contra hlt
  have hgt : signDegree f < pureHighDegree f := not_le.mp hlt
  have hpos : 0 < 𝔼 x : ι → Bool, signFn f x * p x :=
    Finset.expect_pos' (fun x _ ↦ le_of_lt (hrep x))
      ⟨fun _ ↦ false, Finset.mem_univ _, hrep _⟩
  have hparseval : 𝔼 x : ι → Bool, signFn f x * p x = 0 := by
    rw [expect_mul_eq_sum_fourierCoeff_mul]
    refine Finset.sum_eq_zero fun S _ ↦ ?_
    by_cases hS : signDegree f < #S
    · rw [fourierCoeff_eq_zero_of_mem_lowDegree hp hS, mul_zero]
    · have hS' : #S < pureHighDegree f := lt_of_le_of_lt (not_lt.mp hS) hgt
      rw [fourierCoeff_eq_zero_of_card_lt_pureHighDegree hS', zero_mul]
  linarith

/-- **Kahn–Kalai–Linial / Bonami–Beckner level-weight inequality**: for any function
`g : (ι → Bool) → ℝ` taking values in `{-1, 0, 1}` and any `δ ∈ [0, 1]`,
`∑_{S ⊆ ι} δ ^ |S| ĝ(S)² ≤ (|{x | g x ≠ 0}| / 2 ^ |ι|) ^ (2 / (1 + δ))`. -/
theorem sum_pow_card_mul_fourierCoeff_sq_le [DecidableEq ι] {g : (ι → Bool) → ℝ}
    (hg : ∀ x, g x = -1 ∨ g x = 0 ∨ g x = 1) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ∑ S : Finset ι, δ ^ #S * fourierCoeff g S ^ 2 ≤
      ((#{x : ι → Bool | g x ≠ 0} : ℝ) / 2 ^ Fintype.card ι) ^ (2 / (1 + δ)) := by
  let ρ : ℝ := Real.sqrt δ
  let p : ℝ := 1 + δ
  have hp₁ : 1 ≤ p := by dsimp [p]; linarith
  have hp₂ : p ≤ 2 := by dsimp [p]; linarith
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp₁
  have hρ₀ : 0 ≤ ρ := Real.sqrt_nonneg δ
  have hρ_le : ρ ≤ Real.sqrt (p - 1) := by
    dsimp [ρ, p]
    rw [add_sub_cancel_left]
  have hbb := lpNorm_two_noiseOp_le hp₁ hp₂ hρ₀ hρ_le g
  have hbb_sq : lpNorm 2 (noiseOp ρ g) ^ 2 ≤ lpNorm p g ^ 2 :=
    pow_le_pow_left₀ (lpNorm_nonneg 2 (noiseOp ρ g)) hbb 2
  have hlhs : lpNorm 2 (noiseOp ρ g) ^ 2 = ∑ S : Finset ι, δ ^ #S * fourierCoeff g S ^ 2 := by
    rw [lpNorm_two_sq, expect_sq_eq_sum_fourierCoeff_sq]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [fourierCoeff_noiseOp, mul_pow, ← pow_mul, mul_comm #S 2, pow_mul,
      Real.sq_sqrt hδ₀]
  have habs_p (x : ι → Bool) : |g x| ^ p = if g x ≠ 0 then (1 : ℝ) else 0 := by
    rcases hg x with hx | hx | hx <;> simp [hx, Real.zero_rpow hp_pos.ne']
  have hexp : (𝔼 x : ι → Bool, |g x| ^ p) =
      (#{x : ι → Bool | g x ≠ 0} : ℝ) / 2 ^ Fintype.card ι := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    simp_rw [habs_p]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  have hrhs : lpNorm p g ^ 2 =
      ((#{x : ι → Bool | g x ≠ 0} : ℝ) / 2 ^ Fintype.card ι) ^ (2 / (1 + δ)) := by
    rw [lpNorm, hexp, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    dsimp [p]
    ring
  rwa [hlhs, hrhs] at hbb_sq

end FourierAndPureHighDegree

section SymmetricSignDegree

/-- Evaluation of `f : BooleanFunction t` on the canonical weight-`w` prefix vector
`i ↦ decide (i.1 < w)`. When `f` is symmetric and `w ≤ t`, `f x = layerVal f (weight x)`. -/
@[expose]
def layerVal {t : ℕ} (f : BooleanFunction t) (w : ℕ) : Bool :=
  f (fun i : Fin t ↦ decide (i.1 < w))

/-- Evaluation of `layerVal` on the canonical weight-`w` prefix vector. -/
theorem layerVal_apply {t : ℕ} (f : BooleanFunction t) (w : ℕ) :
    layerVal f w = f (fun i : Fin t ↦ decide (i.1 < w)) :=
  rfl

/-- Number of sign changes of a Boolean sequence `g 0, g 1, …, g t`. -/
@[expose]
def signChanges (g : ℕ → Bool) (t : ℕ) : ℕ :=
  #((Finset.range t).filter fun k ↦ g k ≠ g (k + 1))

/-- Filter-cardinality formula for `signChanges`. -/
theorem signChanges_eq_card_filter (g : ℕ → Bool) (t : ℕ) :
    signChanges g t = #((Finset.range t).filter fun k ↦ g k ≠ g (k + 1)) :=
  rfl

/-- `signChanges` on an empty prefix `0` is `0`. -/
@[simp]
theorem signChanges_zero (g : ℕ → Bool) : signChanges g 0 = 0 := by
  simp [signChanges]

private theorem weight_prefix {t w : ℕ} (hw : w ≤ t) :
    weight (fun i : Fin t ↦ decide (i.1 < w)) = w := by
  have heq : ({i : Fin t | decide (i.1 < w) = true} : Finset (Fin t)) =
      (Finset.range w).attach.map
        ⟨fun k ↦ ⟨k.1, lt_of_lt_of_le (Finset.mem_range.mp k.2) hw⟩,
          fun a b h ↦ Subtype.ext (Fin.mk.inj h)⟩ := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      Finset.mem_map, Finset.mem_attach, true_and]
    refine ⟨fun h ↦ ⟨⟨i, Finset.mem_range.mpr h⟩, rfl⟩, ?_⟩
    rintro ⟨⟨k, hk⟩, hki⟩
    have hki' : k = i := Fin.mk.inj hki
    exact hki' ▸ Finset.mem_range.mp hk
  rw [weight, heq, Finset.card_map, Finset.card_attach, Finset.card_range]

/-- For a symmetric Boolean function `f : BooleanFunction t`, `f x` equals
`layerVal f (weight x)`. -/
theorem IsSymmetric.apply_eq_layerVal {t : ℕ} {f : BooleanFunction t}
    (hf : f.IsSymmetric) (x : BitString t) :
    f x = layerVal f (weight x) :=
  hf x _ (weight_prefix (weight_le_length x)).symm

/-- Parity of `signChanges g w` determines `signVal (g w)` relative to `signVal (g 0)`. -/
theorem signVal_eq_mul_neg_one_pow_signChanges (g : ℕ → Bool) (w : ℕ) :
    signVal (g w) = signVal (g 0) * (-1 : ℝ) ^ signChanges g w := by
  induction w with
  | zero =>
    simp [signChanges]
  | succ w ih =>
    have hfilt : (Finset.range (w + 1)).filter (fun k ↦ g k ≠ g (k + 1)) =
        if g w ≠ g (w + 1) then
          insert w ((Finset.range w).filter (fun k ↦ g k ≠ g (k + 1)))
        else
          (Finset.range w).filter (fun k ↦ g k ≠ g (k + 1)) := by
      rw [Finset.range_add_one, Finset.filter_insert]
    rw [signChanges, hfilt]
    split_ifs with hne
    · rw [Finset.card_insert_of_notMem (by simp), ← signChanges, pow_succ, ← mul_assoc, ← ih]
      cases hgw : g w <;> cases hgw1 : g (w + 1)
      · exact False.elim (hne (hgw.trans hgw1.symm))
      · simp
      · simp
      · exact False.elim (hne (hgw.trans hgw1.symm))
    · push Not at hne
      rw [← signChanges, ← hne, ih]

private theorem signDegree_le_signChanges {t : ℕ} {f : BooleanFunction t}
    (hf : f.IsSymmetric) :
    signDegree f ≤ signChanges (layerVal f) t := by
  let C : Finset ℕ := (Finset.range t).filter fun k ↦ layerVal f k ≠ layerVal f (k + 1)
  let p : BitString t → ℝ := fun x ↦
    signVal (layerVal f 0) * ∏ k ∈ C, ((k : ℝ) + 1 / 2 - (weight x : ℝ))
  have hw_deg : (fun x : BitString t ↦ (weight x : ℝ)) ∈ lowDegree ℝ (Fin t) 1 := by
    have hsum : (fun x : BitString t ↦ (weight x : ℝ)) =
        ∑ i : Fin t, fun x : BitString t ↦ bitVal ℝ (x i) := by
      funext x
      rw [Finset.sum_apply, weight_eq_sum_toNat, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      cases x i <;> simp [bitVal]
    rw [hsum]
    exact sum_mem_lowDegree Finset.univ fun i _ ↦ bitVal_mem_lowDegree i
  have hp_deg : p ∈ lowDegree ℝ (Fin t) (signChanges (layerVal f) t) := by
    have hlin (k : ℕ) :
        (fun x : BitString t ↦ (k : ℝ) + 1 / 2 - (weight x : ℝ)) ∈ lowDegree ℝ (Fin t) 1 :=
      Submodule.sub_mem _ (const_mem_lowDegree 1 ((k : ℝ) + 1 / 2)) hw_deg
    have hprod := prod_mem_lowDegree C (a := 1) fun k _ ↦ hlin k
    rw [mul_one] at hprod
    have hprod' : (fun x : BitString t ↦ ∏ k ∈ C, ((k : ℝ) + 1 / 2 - (weight x : ℝ))) ∈
        lowDegree ℝ (Fin t) (signChanges (layerVal f) t) := by
      have heq : (∏ k ∈ C, fun x : BitString t ↦ (k : ℝ) + 1 / 2 - (weight x : ℝ)) =
          fun x : BitString t ↦ ∏ k ∈ C, ((k : ℝ) + 1 / 2 - (weight x : ℝ)) := by
        funext x
        exact Finset.prod_apply x C _
      rw [← heq]
      exact hprod
    exact Submodule.smul_mem _ (signVal (layerVal f 0)) hprod'
  refine signDegree_le_iff.mpr ⟨p, hp_deg, fun x ↦ ?_⟩
  set w := weight x
  have hw_le : w ≤ t := weight_le_length x
  rw [IsSymmetric.apply_eq_layerVal hf x]
  change 0 < signVal (layerVal f w) *
    (signVal (layerVal f 0) * ∏ k ∈ C, ((k : ℝ) + 1 / 2 - (w : ℝ)))
  let C_lt := C.filter (· < w)
  let C_ge := C.filter (w ≤ ·)
  have hC_lt_eq : C_lt = (Finset.range w).filter fun k ↦ layerVal f k ≠ layerVal f (k + 1) := by
    ext k
    simp only [C_lt, C, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨⟨_, hne⟩, hkw⟩ ↦ ⟨hkw, hne⟩,
      fun ⟨hkw, hne⟩ ↦ ⟨⟨lt_of_lt_of_le hkw hw_le, hne⟩, hkw⟩⟩
  have hC_union : C = C_lt ∪ C_ge := by
    ext k
    simp only [C_lt, C_ge, Finset.mem_union, Finset.mem_filter]
    exact ⟨fun hk ↦ (lt_or_ge k w).elim (fun h ↦ Or.inl ⟨hk, h⟩) (fun h ↦ Or.inr ⟨hk, h⟩),
      fun h ↦ h.elim And.left And.left⟩
  have hC_disj : Disjoint C_lt C_ge :=
    Finset.disjoint_left.mpr fun k h1 h2 ↦
      not_lt_of_ge (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hprod_lt :
      ∏ k ∈ C_lt, ((k : ℝ) + 1 / 2 - (w : ℝ)) =
        (-1 : ℝ) ^ #C_lt * ∏ k ∈ C_lt, ((w : ℝ) - (k : ℝ) - 1 / 2) := by
    calc
      ∏ k ∈ C_lt, ((k : ℝ) + 1 / 2 - (w : ℝ))
          = ∏ k ∈ C_lt, ((-1 : ℝ) * ((w : ℝ) - (k : ℝ) - 1 / 2)) :=
            Finset.prod_congr rfl fun k _ ↦ by ring
      _ = (-1 : ℝ) ^ #C_lt * ∏ k ∈ C_lt, ((w : ℝ) - (k : ℝ) - 1 / 2) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hpos_lt : 0 < ∏ k ∈ C_lt, ((w : ℝ) - (k : ℝ) - 1 / 2) :=
    Finset.prod_pos fun k hk ↦ by
      have hkw : k + 1 ≤ w := (Finset.mem_filter.mp hk).2
      have hkwR : (k : ℝ) + 1 ≤ (w : ℝ) := by exact_mod_cast hkw
      linarith
  have hpos_ge : 0 < ∏ k ∈ C_ge, ((k : ℝ) + 1 / 2 - (w : ℝ)) :=
    Finset.prod_pos fun k hk ↦ by
      have hwk : w ≤ k := (Finset.mem_filter.mp hk).2
      have hwkR : (w : ℝ) ≤ (k : ℝ) := by exact_mod_cast hwk
      linarith
  have hsign := signVal_eq_mul_neg_one_pow_signChanges (layerVal f) w
  have hcard_lt : #C_lt = signChanges (layerVal f) w := by
    rw [hC_lt_eq, signChanges]
  rw [hsign, hC_union, Finset.prod_union hC_disj, hprod_lt, hcard_lt]
  set A := ∏ k ∈ C_lt, ((w : ℝ) - (k : ℝ) - 1 / 2)
  set B := ∏ k ∈ C_ge, ((k : ℝ) + 1 / 2 - (w : ℝ))
  set s := signVal (layerVal f 0) * (-1 : ℝ) ^ signChanges (layerVal f) w
  have hsq : s * s = 1 := by
    dsimp only [s]
    calc
      (signVal (layerVal f 0) * (-1 : ℝ) ^ signChanges (layerVal f) w) *
          (signVal (layerVal f 0) * (-1 : ℝ) ^ signChanges (layerVal f) w)
          = (signVal (layerVal f 0) * signVal (layerVal f 0)) *
              ((-1 : ℝ) ^ signChanges (layerVal f) w *
                (-1 : ℝ) ^ signChanges (layerVal f) w) := by
                ring
      _ = 1 := by
            rw [signVal_mul_self, one_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hrew :
      s * (signVal (layerVal f 0) * ((-1 : ℝ) ^ signChanges (layerVal f) w * A * B)) =
        (s * s) * (A * B) := by
    dsimp only [s]
    ring
  rw [hrew, hsq, one_mul]
  exact mul_pos hpos_lt hpos_ge

private noncomputable def fallingPoly (m : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range m, (Polynomial.X - Polynomial.C (j : ℝ))

private theorem natDegree_fallingPoly_le (m : ℕ) : (fallingPoly m).natDegree ≤ m := by
  induction m with
  | zero => simp [fallingPoly]
  | succ m ih =>
    rw [fallingPoly, Finset.prod_range_succ, ← fallingPoly]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_X_sub_C]
    omega

private theorem eval_fallingPoly_nat (m w : ℕ) :
    (fallingPoly m).eval (w : ℝ) = (w.choose m : ℝ) * (Nat.factorial m : ℝ) := by
  induction m generalizing w with
  | zero => simp [fallingPoly]
  | succ m ih =>
    rw [fallingPoly, Finset.prod_range_succ, ← fallingPoly, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ih w, Nat.factorial_succ]
    push_cast
    have hchoose := Nat.choose_succ_right_eq w m
    have hchooseR : (w.choose (m + 1) : ℝ) * ((m : ℝ) + 1) =
        (w.choose m : ℝ) * ((w - m : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    by_cases hmw : m ≤ w
    · rw [Nat.cast_sub hmw] at hchooseR
      calc
        (w.choose m : ℝ) * (Nat.factorial m : ℝ) * ((w : ℝ) - (m : ℝ))
            = ((w.choose m : ℝ) * ((w : ℝ) - (m : ℝ))) * (Nat.factorial m : ℝ) := by ring
        _ = ((w.choose (m + 1) : ℝ) * ((m : ℝ) + 1)) * (Nat.factorial m : ℝ) := by rw [hchooseR]
        _ = (w.choose (m + 1) : ℝ) * (((m : ℝ) + 1) * (Nat.factorial m : ℝ)) := by ring
    · have hlt : w < m + 1 := by omega
      have hlt' : w < m := not_le.mp hmw
      simp [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hlt']

private theorem choose_mul_sum_weightLayer_monomial {t : ℕ} (S : Finset (Fin t)) (w : ℕ) :
    (t.choose #S : ℝ) * ∑ x ∈ weightLayer t w, monomial ℝ S x =
      (t.choose w : ℝ) * (w.choose #S : ℝ) := by
  have hsum_card :
      (∑ x ∈ weightLayer t w, monomial ℝ S x) =
        (#((weightLayer t w).filter fun x ↦ ∀ i ∈ S, x i = true) : ℝ) := by
    induction (weightLayer t w) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.filter_insert, ih, monomial_apply]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (fun hm ↦ ha (Finset.mem_filter.mp hm).1)]
        push_cast
        ring
      · ring
  rw [hsum_card]
  by_cases hSw : #S ≤ w
  · let complType := {i : Fin t // i ∉ S}
    let eCompl : complType ≃ {i : Fin t // i ∈ Sᶜ} :=
      { toFun := fun i ↦ ⟨i.1, Finset.mem_compl.mpr i.2⟩
        invFun := fun i ↦ ⟨i.1, Finset.mem_compl.mp i.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hcard_compl : Fintype.card complType = t - #S := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have hbij : #((weightLayer t w).filter fun x ↦ ∀ i ∈ S, x i = true) =
        #{y : complType → Bool | weight y = w - #S} := by
      refine Finset.card_nbij'
        (fun x (i : complType) ↦ x i.1)
        (fun y (i : Fin t) ↦ if h : i ∈ S then true else y ⟨i, h⟩)
        (fun x hx ↦ ?_) (fun y hy ↦ ?_) (fun x hx ↦ ?_) (fun y _ ↦ ?_)
      · simp only [Finset.mem_coe, Finset.mem_filter, mem_weightLayer, Finset.mem_univ,
          true_and] at hx ⊢
        have hwx : weight x = #S + weight (fun i : complType ↦ x i.1) := by
          rw [weight_eq_sum_toNat, weight_eq_sum_toNat, ← Finset.sum_add_sum_compl S]
          congr 1
          · rw [Finset.sum_eq_card_nsmul (b := 1) fun i hi ↦ by simp [hx.2 i hi],
              smul_eq_mul, mul_one]
          · refine (Finset.sum_coe_sort Sᶜ (fun i ↦ (x i).toNat)).symm.trans ?_
            exact Fintype.sum_equiv eCompl.symm _ _ fun _ ↦ rfl
        omega
      · simp only [Finset.mem_coe, Finset.mem_filter, mem_weightLayer, Finset.mem_univ,
          true_and] at hy ⊢
        refine ⟨?_, fun i hi ↦ by simp [hi]⟩
        rw [weight_eq_sum_toNat, ← Finset.sum_add_sum_compl S]
        have h1 : ∑ i ∈ S, (if h : i ∈ S then true else y ⟨i, h⟩).toNat = #S := by
          rw [Finset.sum_eq_card_nsmul (b := 1) fun i hi ↦ by simp [hi], smul_eq_mul, mul_one]
        have h2 : ∑ i ∈ Sᶜ, (if h : i ∈ S then true else y ⟨i, h⟩).toNat = weight y := by
          rw [weight_eq_sum_toNat]
          refine (Finset.sum_coe_sort Sᶜ
            (fun i ↦ (if h : i ∈ S then true else y ⟨i, h⟩).toNat)).symm.trans ?_
          refine Fintype.sum_equiv eCompl.symm
            (fun i : {i : Fin t // i ∈ Sᶜ} ↦ (if h : i.1 ∈ S then true else y ⟨i.1, h⟩).toNat)
            (fun j : complType ↦ (y j).toNat) fun i ↦ ?_
          have hnot : i.1 ∉ S := Finset.mem_compl.mp i.2
          simp [eCompl, hnot]
        omega
      · simp only [Finset.mem_coe, Finset.mem_filter] at hx
        funext i
        by_cases hi : i ∈ S
        · simp [hi, hx.2 i hi]
        · simp [hi]
      · funext i
        simp [i.2]
    rw [hbij, card_filter_weight_eq, hcard_compl]
    exact_mod_cast (Nat.choose_mul (n := t) hSw).symm
  · have hempty : ((weightLayer t w).filter fun x ↦ ∀ i ∈ S, x i = true) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hSall
      rw [mem_weightLayer] at hx
      have hle : #S ≤ weight x := by
        rw [weight]
        exact Finset.card_le_card fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hSall i hi⟩
      omega
    rw [hempty, Finset.card_empty, Nat.choose_eq_zero_of_lt (not_le.mp hSw)]
    simp

private theorem exists_univariate_layer_poly {t d : ℕ} {p : BitString t → ℝ}
    (hp : p ∈ lowDegree ℝ (Fin t) d) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ d ∧
      ∀ w ≤ t, (t.choose w : ℝ) * P.eval (w : ℝ) = ∑ x ∈ weightLayer t w, p x := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨S, hS, rfl⟩
    have hm_le_t : #S ≤ t := (Finset.card_le_univ S).trans_eq (Fintype.card_fin t)
    have hchoose_pos : (0 : ℝ) < t.choose #S := by exact_mod_cast Nat.choose_pos hm_le_t
    have hfact_pos : (0 : ℝ) < Nat.factorial #S := by exact_mod_cast Nat.factorial_pos #S
    let c : ℝ := ((t.choose #S : ℝ) * (Nat.factorial #S : ℝ))⁻¹
    refine ⟨Polynomial.C c * fallingPoly #S, ?_, fun w hw ↦ ?_⟩
    · refine (Polynomial.natDegree_C_mul_le c (fallingPoly #S)).trans ?_
      exact (natDegree_fallingPoly_le #S).trans hS
    · rw [Polynomial.eval_mul, Polynomial.eval_C, eval_fallingPoly_nat]
      have hmul := choose_mul_sum_weightLayer_monomial S w
      dsimp only [c]
      have hne1 : (t.choose #S : ℝ) ≠ 0 := hchoose_pos.ne'
      have hne2 : (Nat.factorial #S : ℝ) ≠ 0 := hfact_pos.ne'
      field_simp [hne1, hne2]
      linarith
  · exact ⟨0, Nat.zero_le d, fun w _ ↦ by simp⟩
  · rintro f₁ f₂ - - ⟨P₁, hdeg₁, hP₁⟩ ⟨P₂, hdeg₂, hP₂⟩
    refine ⟨P₁ + P₂, (Polynomial.natDegree_add_le P₁ P₂).trans (max_le hdeg₁ hdeg₂),
      fun w hw ↦ ?_⟩
    rw [Polynomial.eval_add, mul_add, hP₁ w hw, hP₂ w hw, ← Finset.sum_add_distrib]
    rfl
  · rintro a f₁ - ⟨P₁, hdeg₁, hP₁⟩
    refine ⟨Polynomial.C a * P₁, (Polynomial.natDegree_C_mul_le a P₁).trans hdeg₁, fun w hw ↦ ?_⟩
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← mul_assoc, mul_comm (t.choose w : ℝ) a,
      mul_assoc, hP₁ w hw, Finset.mul_sum]
    rfl

private theorem signChanges_le_signDegree {t : ℕ} {f : BooleanFunction t}
    (hf : f.IsSymmetric) :
    signChanges (layerVal f) t ≤ signDegree f := by
  obtain ⟨p, hp, hrep⟩ := exists_isSignRepresentedBy_signDegree f
  obtain ⟨P, hP_deg, hP_eval⟩ := exists_univariate_layer_poly hp
  have hP_sign (w : ℕ) (hw : w ≤ t) : 0 < signVal (layerVal f w) * P.eval (w : ℝ) := by
    have hchoose_pos : (0 : ℝ) < t.choose w := by exact_mod_cast Nat.choose_pos hw
    have hsum_pos : 0 < ∑ x ∈ weightLayer t w, signVal (layerVal f w) * p x := by
      refine Finset.sum_pos (fun x hx ↦ ?_) (weightLayer_nonempty hw)
      have hfx : f x = layerVal f w := by
        rw [IsSymmetric.apply_eq_layerVal hf x, mem_weightLayer.mp hx]
      simpa only [hfx] using hrep x
    rw [← Finset.mul_sum, ← hP_eval w hw] at hsum_pos
    nlinarith
  have hP_ne : P ≠ 0 := by
    intro h0
    have h0' := hP_sign 0 (Nat.zero_le t)
    simp [h0] at h0'
  let C : Finset ℕ := (Finset.range t).filter fun k ↦ layerVal f k ≠ layerVal f (k + 1)
  have hroot_exists (k : ℕ) (hk : k ∈ C) :
      ∃ r : ℝ, (k : ℝ) < r ∧ r < (k : ℝ) + 1 ∧ P.eval r = 0 := by
    have hk_lt : k < t := (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    have hne : layerVal f k ≠ layerVal f (k + 1) := (Finset.mem_filter.mp hk).2
    have hs0 := hP_sign k hk_lt.le
    have hs1 := hP_sign (k + 1) hk_lt
    rw [Nat.cast_add, Nat.cast_one] at hs1
    have hopp : P.eval (k : ℝ) * P.eval ((k : ℝ) + 1) < 0 := by
      cases h0 : layerVal f k <;> cases h1 : layerVal f (k + 1)
      · exact False.elim (hne (h0.trans h1.symm))
      · simp only [h0, signVal_false, one_mul] at hs0
        simp only [h1, signVal_true, neg_one_mul, Left.neg_pos_iff] at hs1
        exact mul_neg_of_pos_of_neg hs0 hs1
      · simp only [h0, signVal_true, neg_one_mul, Left.neg_pos_iff] at hs0
        simp only [h1, signVal_false, one_mul] at hs1
        exact mul_neg_of_neg_of_pos hs0 hs1
      · exact False.elim (hne (h0.trans h1.symm))
    have hcont : ContinuousOn (fun x : ℝ ↦ P.eval x) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
      have hsum_cont (s : Finset ℕ) : Continuous (fun x : ℝ ↦ ∑ i ∈ s, P.coeff i * x ^ i) := by
        induction s using Finset.induction_on with
        | empty => simpa using continuous_const
        | insert a s ha ih =>
          have hstep : (fun x : ℝ ↦ ∑ i ∈ insert a s, P.coeff i * x ^ i) =
              fun x : ℝ ↦ P.coeff a * x ^ a + ∑ i ∈ s, P.coeff i * x ^ i := by
            funext x
            exact Finset.sum_insert ha
          rw [hstep]
          exact (continuous_const.mul (continuous_pow a)).add ih
      have hpoly_cont : Continuous (fun x : ℝ ↦ P.eval x) := by
        have heq : (fun x : ℝ ↦ P.eval x) =
            fun x : ℝ ↦ ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i := by
          funext x
          exact P.eval_eq_sum_range x
        rw [heq]
        exact hsum_cont _
      exact hpoly_cont.continuousOn
    have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    by_cases hk_neg : P.eval (k : ℝ) < 0
    · have hk1_pos : 0 < P.eval ((k : ℝ) + 1) := pos_of_mul_neg_right hopp hk_neg.le
      obtain ⟨r, ⟨hr0, hr1⟩, hr_eq⟩ := intermediate_value_Icc hle hcont ⟨hk_neg.le, hk1_pos.le⟩
      dsimp only at hr_eq
      refine ⟨r, lt_of_le_of_ne hr0 (fun h ↦ ?_), lt_of_le_of_ne hr1 (fun h ↦ ?_), hr_eq⟩
      · rw [← h] at hr_eq; linarith
      · rw [h] at hr_eq; linarith
    · have hk_pos : 0 < P.eval (k : ℝ) :=
        lt_of_le_of_ne (not_lt.mp hk_neg) (fun h ↦ by rw [← h, zero_mul] at hopp; linarith)
      have hk1_neg : P.eval ((k : ℝ) + 1) < 0 := neg_of_mul_neg_right hopp hk_pos.le
      obtain ⟨r, ⟨hr0, hr1⟩, hr_eq⟩ := intermediate_value_Icc' hle hcont ⟨hk1_neg.le, hk_pos.le⟩
      dsimp only at hr_eq
      refine ⟨r, lt_of_le_of_ne hr0 (fun h ↦ ?_), lt_of_le_of_ne hr1 (fun h ↦ ?_), hr_eq⟩
      · rw [← h] at hr_eq; linarith
      · rw [h] at hr_eq; linarith
  classical
  let rootOf : {k // k ∈ C} → ℝ := fun k ↦ (hroot_exists k.1 k.2).choose
  have hroot_spec (k : {k // k ∈ C}) :
      (k.1 : ℝ) < rootOf k ∧ rootOf k < (k.1 : ℝ) + 1 ∧ P.eval (rootOf k) = 0 :=
    (hroot_exists k.1 k.2).choose_spec
  have hinj : Function.Injective (fun k : {k // k ∈ C} ↦ (⟨rootOf k,
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr (hroot_spec k).2.2)⟩ :
        P.roots.toFinset)) := by
    intro k₁ k₂ heq
    have hr_eq : rootOf k₁ = rootOf k₂ := congrArg Subtype.val heq
    rcases lt_trichotomy k₁.1 k₂.1 with hlt | heq_val | hgt
    · have hle : (k₁.1 : ℝ) + 1 ≤ (k₂.1 : ℝ) := by exact_mod_cast hlt
      linarith [(hroot_spec k₁).2.1, (hroot_spec k₂).1]
    · exact Subtype.ext heq_val
    · have hle : (k₂.1 : ℝ) + 1 ≤ (k₁.1 : ℝ) := by exact_mod_cast hgt
      linarith [(hroot_spec k₂).2.1, (hroot_spec k₁).1]
  have hcard_le : #C ≤ P.roots.toFinset.card := by
    rw [← Fintype.card_coe C, ← Fintype.card_coe P.roots.toFinset]
    exact Fintype.card_le_of_injective _ hinj
  exact hcard_le.trans ((Multiset.toFinset_card_le P.roots).trans
    ((Polynomial.card_roots' P).trans hP_deg))

/-- **Aspnes–Beigel–Furst–Rudich theorem**: the sign-degree of any symmetric Boolean
function `f : BooleanFunction t` equals the number of sign changes of `f` across the Hamming-weight
layers `0, 1, …, t`.
-/
theorem signDegree_eq_signChanges {t : ℕ} {f : BooleanFunction t}
    (hf : f.IsSymmetric) :
    signDegree f = signChanges (layerVal f) t :=
  le_antisymm (signDegree_le_signChanges hf) (signChanges_le_signDegree hf)

end SymmetricSignDegree

end CslibFrontier.BooleanAnalysis
