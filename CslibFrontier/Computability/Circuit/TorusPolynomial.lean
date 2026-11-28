module

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import CslibFrontier.Computability.QueryComplexity.NisanSzegedy
import CslibFrontier.Computability.QueryComplexity.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.Mobius
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Torus Polynomial Approximations of Boolean Functions and Threshold Degree Lower Bounds

This module develops torus polynomial and `α`-torus polynomial approximations of Boolean functions
on `{0, 1}^n`, subgroup-symmetric multivariate polynomials (`Γ ≤ S_n`), base-`p` integer modular
polynomial encodings, and degree lower bounds for approximating the `n`-bit conjunction
`Cslib.threshold n n` on the real torus `ℝ / ℤ`.

## Main definitions

* `CslibFrontier.Computability.Circuit.TorusPolynomial.boolPoint`: `{0, 1}`-valued cube embedding
  `Cslib.BitString n → Fin n → R`.
* `CslibFrontier.Computability.Circuit.TorusPolynomial.IsTorusApprox`,
  `CslibFrontier.Computability.Circuit.TorusPolynomial.IsAlphaTorusApprox`: uniform torus and
  `α`-torus polynomial approximations of a Boolean function.
* `CslibFrontier.Computability.Circuit.TorusPolynomial.IsGroupSymmetricPoly`: syntactic invariance
  of a multivariate polynomial under a permutation subgroup `Γ ≤ S_n`.
* `CslibFrontier.Computability.Circuit.TorusPolynomial.IsIntBaseApprox`,
  `CslibFrontier.Computability.Circuit.TorusPolynomial.scaleIntPolyToTorus`: base-`p` integer
  modular polynomial encodings at scale `p ^ ℓ` and conversion to `(1 / p)`-torus polynomials.

## Main results

* `CslibFrontier.Computability.Circuit.TorusPolynomial.isGroupSymmetricPoly_iff_coeff_orbit`:
  `Γ`-symmetry is equivalent to orbit-constant monomial coefficients.
* `CslibFrontier.Computability.Circuit.TorusPolynomial.IsIntBaseApprox.toAlphaTorusApprox`,
  `CslibFrontier.Computability.Circuit.TorusPolynomial.IsIntBaseApprox.toTorusApprox`: scaling a
  base-`p` integer encoding by `p ^ (-(ℓ + 1))` yields a `(1 / p)`-torus approximation within
  `p ^ (-(e + 1))`.
* `CslibFrontier.Computability.Circuit.TorusPolynomial.sym_torus_approx_threshold_self_degree_lb`:
  any symmetric torus polynomial approximating `Cslib.threshold n n` within error `< 1 / (2 * n)`
  satisfies `n < (deg(P) + 1) ^ 2 * (⌊log₂(n + 1)⌋ + 1)`.
* `CslibFrontier.Computability.Circuit.TorusPolynomial.torus_approx_threshold_self_nisan_szegedy`:
  any torus polynomial of degree `d` approximating `Cslib.threshold n n` within error
  `ε' < 2 ^ (-(d + 1))` satisfies `(1 - 4 * ε') * n ≤ 2 * d ^ 2`, yielding
  `log₂(1 / ε) - 1 < deg(P)` whenever `2 * (log₂(1 / ε)) ^ 2 ≤ (1 - 4 * ε) * n`.
-/

public section

namespace CslibFrontier.Computability.Circuit.TorusPolynomial

open Finset
open scoped BigOperators

/-! ### 1. Boolean cube evaluation points and total-degree helpers -/

/-- Embedding of a Boolean bit string `a ∈ {0, 1}^n` into `Fin n → R` via `0` and `1`. -/
@[expose] def boolPoint (R : Type*) [CommRing R] {n : ℕ} (a : Cslib.BitString n) : Fin n → R :=
  fun i => Cslib.BitString.bitVal R (a i)

@[simp]
theorem boolPoint_apply (R : Type*) [CommRing R] {n : ℕ} (a : Cslib.BitString n) (i : Fin n) :
    boolPoint R a i = Cslib.BitString.bitVal R (a i) :=
  rfl

/-- Compatibility of `boolPoint` with coordinate reindexing. -/
theorem boolPoint_comp {R : Type*} [CommRing R] {m n : ℕ} (a : Cslib.BitString n)
    (g : Fin m → Fin n) :
    boolPoint R (a ∘ g) = boolPoint R a ∘ g :=
  rfl

private theorem totalDegree_neg_eq {σ R : Type*} [CommRing R] (P : MvPolynomial σ R) :
    (-P).totalDegree = P.totalDegree := by
  classical
  simp only [MvPolynomial.totalDegree]
  congr 1
  ext d
  simp [MvPolynomial.mem_support_iff]

private theorem totalDegree_sub_le {σ R : Type*} [CommRing R] (P Q : MvPolynomial σ R) :
    (P - Q).totalDegree ≤ max P.totalDegree Q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add P (-Q)).trans (by rw [totalDegree_neg_eq])

private theorem threshold_self_eq_true_iff_weight {n : ℕ} {a : Cslib.BitString n} :
    Cslib.threshold n n a = true ↔ Cslib.BitString.weight a = n := by
  have hle := Cslib.BitString.weight_le_length a
  rw [Cslib.threshold_eq_true_iff]
  omega

private theorem threshold_self_of_weight_lt {n : ℕ} {a : Cslib.BitString n}
    (ha : Cslib.BitString.weight a < n) :
    Cslib.threshold n n a = false := by
  rw [← Bool.not_eq_true, threshold_self_eq_true_iff_weight]
  omega

/-! ### 2. Torus polynomials, `α`-torus polynomials, and `Γ`-symmetry -/

/-- `P ∈ ℝ[x₁, ..., xₙ]` is a torus polynomial approximating `f : {0, 1}^n → {0, 1}` within error
`ε` (`0 ≤ ε < 1 / 4`) if there exists `Z : {0, 1}^n → ℤ` such that
`|P(a) - (Z(a) + f(a) / 2)| ≤ ε` for every `a ∈ {0, 1}^n`. -/
@[expose] def IsTorusApprox {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (f : Cslib.BooleanFunction n)
    (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε < 1 / 4 ∧
    ∃ Z : Cslib.BitString n → ℤ, ∀ a : Cslib.BitString n,
      |MvPolynomial.eval (boolPoint ℝ a) P -
        ((Z a : ℝ) + Cslib.BitString.bitVal ℝ (f a) / 2)| ≤ ε

/-- For `α ∈ (0, 1)`, `P ∈ ℝ[x₁, ..., xₙ]` is an `α`-torus polynomial approximating
`f : {0, 1}^n → {0, 1}` within error `ε` (`0 ≤ ε`) if there exists `Z : {0, 1}^n → ℤ` such that
`|P(a) - (Z(a) + α * f(a))| ≤ ε` for every `a ∈ {0, 1}^n`. -/
@[expose] def IsAlphaTorusApprox {n : ℕ} (α : ℝ) (P : MvPolynomial (Fin n) ℝ)
    (f : Cslib.BooleanFunction n) (ε : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ 0 ≤ ε ∧
    ∃ Z : Cslib.BitString n → ℤ, ∀ a : Cslib.BitString n,
      |MvPolynomial.eval (boolPoint ℝ a) P -
        ((Z a : ℝ) + α * Cslib.BitString.bitVal ℝ (f a))| ≤ ε

/-- For `ε < 1 / 4`, torus approximation coincides with `(1 / 2)`-torus approximation. -/
theorem isTorusApprox_iff_isAlphaTorusApprox_half {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (f : Cslib.BooleanFunction n) {ε : ℝ} (hε : ε < 1 / 4) :
    IsTorusApprox P f ε ↔ IsAlphaTorusApprox (1 / 2) P f ε := by
  refine ⟨fun ⟨h0, _, Z, hZ⟩ => ⟨by norm_num, by norm_num, h0, Z, fun a => ?_⟩,
    fun ⟨_, _, h0, Z, hZ⟩ => ⟨h0, hε, Z, fun a => ?_⟩⟩
  · simpa only [one_div, inv_mul_eq_div] using hZ a
  · simpa only [one_div, inv_mul_eq_div] using hZ a

/-- Error monotonicity for `IsTorusApprox`. -/
theorem IsTorusApprox.mono_err {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    {f : Cslib.BooleanFunction n} {ε ε' : ℝ} (h : IsTorusApprox P f ε) (hle : ε ≤ ε')
    (hε' : ε' < 1 / 4) :
    IsTorusApprox P f ε' := by
  obtain ⟨h0, _, Z, hZ⟩ := h
  exact ⟨h0.trans hle, hε', Z, fun a => (hZ a).trans hle⟩

/-- Error monotonicity for `IsAlphaTorusApprox`. -/
theorem IsAlphaTorusApprox.mono_err {n : ℕ} {α : ℝ} {P : MvPolynomial (Fin n) ℝ}
    {f : Cslib.BooleanFunction n} {ε ε' : ℝ} (h : IsAlphaTorusApprox α P f ε) (hle : ε ≤ ε') :
    IsAlphaTorusApprox α P f ε' := by
  obtain ⟨hα0, hα1, h0, Z, hZ⟩ := h
  exact ⟨hα0, hα1, h0.trans hle, Z, fun a => (hZ a).trans hle⟩

/-- Subgroup symmetry of a multivariate polynomial `P ∈ R[x₁, ..., xₙ]` under `Γ ≤ S_n`. -/
@[expose] def IsGroupSymmetricPoly {n : ℕ} {R : Type*} [CommSemiring R]
    (Γ : Subgroup (Equiv.Perm (Fin n))) (P : MvPolynomial (Fin n) R) : Prop :=
  ∀ π ∈ Γ, MvPolynomial.rename π P = P

/-- Full `S_n`-symmetry (`Γ = ⊤`) coincides with `MvPolynomial.IsSymmetric`. -/
theorem isGroupSymmetricPoly_top_iff {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin n) R) :
    IsGroupSymmetricPoly ⊤ P ↔ P.IsSymmetric :=
  ⟨fun h π => h π (Subgroup.mem_top π), fun h π _ => h π⟩

/-- Orbit characterization of `Γ`-symmetry: monomials in the same `Γ`-orbit share equal
coefficients. -/
theorem isGroupSymmetricPoly_iff_coeff_orbit {n : ℕ} {R : Type*} [CommSemiring R]
    (Γ : Subgroup (Equiv.Perm (Fin n))) (P : MvPolynomial (Fin n) R) :
    IsGroupSymmetricPoly Γ P ↔
      ∀ π ∈ Γ, ∀ d : Fin n →₀ ℕ, P.coeff (d.mapDomain π) = P.coeff d := by
  refine ⟨fun h π hπ d => ?_, fun h π hπ => ?_⟩
  · rw [← h π hπ, MvPolynomial.coeff_rename_mapDomain π π.injective, h π hπ]
  · ext d
    have hd : d = (d.mapDomain π.symm).mapDomain π := by
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
    rw [hd, MvPolynomial.coeff_rename_mapDomain π π.injective]
    exact (h π hπ (d.mapDomain π.symm)).symm

/-! ### 3. Base-`p` integer modular polynomial encodings -/

/-- Integer base-`p` modular polynomial encoding of `f` at scale `p ^ ℓ` and precision `e`:
`e ≤ ℓ` and for every `a ∈ {0, 1}^n`, `Q(a) ≡ f(a) * p ^ ℓ + E [ZMOD p ^ (ℓ + e)]` for some
integer `0 ≤ E ≤ p ^ (ℓ - e)`. -/
@[expose] def IsIntBaseApprox {n : ℕ} (p ℓ e : ℕ) (Q : MvPolynomial (Fin n) ℤ)
    (f : Cslib.BooleanFunction n) : Prop :=
  e ≤ ℓ ∧ ∀ a : Cslib.BitString n, ∃ E : ℤ,
    0 ≤ E ∧ E ≤ (p : ℤ) ^ (ℓ - e) ∧
    MvPolynomial.eval (boolPoint ℤ a) Q ≡
      Cslib.BitString.bitVal ℤ (f a) * (p : ℤ) ^ ℓ + E [ZMOD (p : ℤ) ^ (ℓ + e)]

private theorem totalDegree_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (Q : MvPolynomial σ R) :
    (Q.map φ).totalDegree ≤ Q.totalDegree := by
  classical
  refine Finset.sup_le fun d hd => MvPolynomial.le_totalDegree ?_
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hd
  exact MvPolynomial.mem_support_iff.2 fun h0 => hd (by rw [h0, map_zero])

private theorem eval_map_boolPoint {n : ℕ} (a : Cslib.BitString n) (Q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.eval (boolPoint ℝ a) (Q.map (Int.castRingHom ℝ)) =
      (MvPolynomial.eval (boolPoint ℤ a) Q : ℝ) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.eval_X, hp, boolPoint_apply, Int.cast_mul]
    congr 1
    cases a i <;> simp [Cslib.BitString.bitVal]

/-- Scale an integer polynomial `Q ∈ ℤ[x₁, ..., xₙ]` by `1 / (p ^ (ℓ + 1))` into `ℝ[x₁, ..., xₙ]`.
-/
noncomputable def scaleIntPolyToTorus {n : ℕ} (p ℓ : ℕ) (Q : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (((p : ℝ) ^ (ℓ + 1))⁻¹) * Q.map (Int.castRingHom ℝ)

/-- Scaling into `ℝ[x₁, ..., xₙ]` never increases total degree. -/
theorem totalDegree_scaleIntPolyToTorus_le {n : ℕ} (p ℓ : ℕ) (Q : MvPolynomial (Fin n) ℤ) :
    (scaleIntPolyToTorus p ℓ Q).totalDegree ≤ Q.totalDegree := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_map_le _ Q

/-- Dividing a base-`p` integer encoding `Q` (`p ≥ 2`, `e ≥ 1`) by `p ^ (ℓ + 1)` gives a
`(1 / p)`-torus polynomial approximating `f` within error `1 / p ^ (e + 1)`. -/
theorem IsIntBaseApprox.toAlphaTorusApprox {n p ℓ e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e)
    {Q : MvPolynomial (Fin n) ℤ} {f : Cslib.BooleanFunction n}
    (hQ : IsIntBaseApprox p ℓ e Q f) :
    IsAlphaTorusApprox (1 / (p : ℝ)) (scaleIntPolyToTorus p ℓ Q) f
      (1 / ((p : ℝ) ^ (e + 1))) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  refine ⟨by positivity, by rw [div_lt_one hp0]; linarith, by positivity, ?_⟩
  obtain ⟨heℓ, hpoint⟩ := hQ
  choose E hE0 hEle hmod using hpoint
  have hdvd (a : Cslib.BitString n) :
      ((p : ℤ) ^ (ℓ + 1)) ∣
        MvPolynomial.eval (boolPoint ℤ a) Q -
          (Cslib.BitString.bitVal ℤ (f a) * (p : ℤ) ^ ℓ + E a) := by
    have h1 : ((p : ℤ) ^ (ℓ + e)) ∣
        (Cslib.BitString.bitVal ℤ (f a) * (p : ℤ) ^ ℓ + E a) -
          MvPolynomial.eval (boolPoint ℤ a) Q :=
      Int.modEq_iff_dvd.1 (hmod a)
    have h2 : ((p : ℤ) ^ (ℓ + 1)) ∣ ((p : ℤ) ^ (ℓ + e)) :=
      pow_dvd_pow (p : ℤ) (by omega)
    simpa only [neg_sub] using (h2.trans h1).neg_right
  choose Z hZ using hdvd
  refine ⟨Z, fun a => ?_⟩
  have heval : MvPolynomial.eval (boolPoint ℝ a) (scaleIntPolyToTorus p ℓ Q) =
      (MvPolynomial.eval (boolPoint ℤ a) Q : ℝ) / ((p : ℝ) ^ (ℓ + 1)) := by
    unfold scaleIntPolyToTorus
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_map_boolPoint, inv_mul_eq_div]
  have hQeq : (MvPolynomial.eval (boolPoint ℤ a) Q : ℝ) =
      (Z a : ℝ) * (p : ℝ) ^ (ℓ + 1) +
        Cslib.BitString.bitVal ℝ (f a) * (p : ℝ) ^ ℓ + (E a : ℝ) := by
    have hZa := eq_add_of_sub_eq' (hZ a)
    have hcast : (MvPolynomial.eval (boolPoint ℤ a) Q : ℝ) =
        ((Cslib.BitString.bitVal ℤ (f a) * (p : ℤ) ^ ℓ + E a +
          (p : ℤ) ^ (ℓ + 1) * Z a : ℤ) : ℝ) := by
      rw [← hZa]
    have hb : (Cslib.BitString.bitVal ℤ (f a) : ℝ) = Cslib.BitString.bitVal ℝ (f a) := by
      cases f a <;> simp [Cslib.BitString.bitVal]
    push_cast at hcast
    rw [hb] at hcast
    linarith
  have hp_pow_pos : (0 : ℝ) < (p : ℝ) ^ (ℓ + 1) := by positivity
  rw [heval, hQeq]
  have hdiff : ((Z a : ℝ) * (p : ℝ) ^ (ℓ + 1) +
        Cslib.BitString.bitVal ℝ (f a) * (p : ℝ) ^ ℓ + (E a : ℝ)) / ((p : ℝ) ^ (ℓ + 1)) -
      ((Z a : ℝ) + 1 / (p : ℝ) * Cslib.BitString.bitVal ℝ (f a)) =
      (E a : ℝ) / ((p : ℝ) ^ (ℓ + 1)) := by
    rw [pow_succ]
    field_simp
    ring
  rw [hdiff, abs_of_nonneg (div_nonneg (by exact_mod_cast hE0 a) hp_pow_pos.le)]
  have hER : (E a : ℝ) ≤ (p : ℝ) ^ (ℓ - e) := by exact_mod_cast hEle a
  have hpow_eq : (p : ℝ) ^ (ℓ + 1) = (p : ℝ) ^ (ℓ - e) * (p : ℝ) ^ (e + 1) := by
    rw [← pow_add, show ℓ - e + (e + 1) = ℓ + 1 by omega]
  rw [hpow_eq, div_mul_eq_div_div]
  have h1 : (E a : ℝ) / (p : ℝ) ^ (ℓ - e) ≤ 1 :=
    (div_le_one (by positivity)).2 hER
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- Base-`2` specialization (`e ≥ 2`) producing a standard torus polynomial approximation within
`1 / 2 ^ (e + 1)`. -/
theorem IsIntBaseApprox.toTorusApprox {n ℓ e : ℕ} (he : 2 ≤ e)
    {Q : MvPolynomial (Fin n) ℤ} {f : Cslib.BooleanFunction n}
    (hQ : IsIntBaseApprox 2 ℓ e Q f) :
    IsTorusApprox (scaleIntPolyToTorus 2 ℓ Q) f (1 / ((2 : ℝ) ^ (e + 1))) := by
  have herr : (1 : ℝ) / ((2 : ℝ) ^ (e + 1)) < 1 / 4 := by
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ (e + 1) := by
      calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ (e + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  exact (isTorusApprox_iff_isAlphaTorusApprox_half _ _ herr).2
    (hQ.toAlphaTorusApprox le_rfl (by omega))

/-! ### 4. Symmetric and general torus degree lower bounds for `Cslib.threshold n n` -/

private theorem exists_perm_of_weight_eq {n : ℕ} {a b : Cslib.BitString n}
    (hw : Cslib.BitString.weight a = Cslib.BitString.weight b) :
    ∃ π : Equiv.Perm (Fin n), b = a ∘ π := by
  let Sa : Finset (Fin n) := univ.filter fun i => a i = true
  let Sb : Finset (Fin n) := univ.filter fun i => b i = true
  have h1 : Fintype.card Sb = Fintype.card Sa := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact hw.symm
  have h0 : Fintype.card ((univ \ Sb : Finset (Fin n))) =
      Fintype.card ((univ \ Sa : Finset (Fin n))) := by
    rw [Fintype.card_coe, Fintype.card_coe, card_sdiff_of_subset (subset_univ Sb),
      card_sdiff_of_subset (subset_univ Sa), card_univ, Fintype.card_fin]
    change n - Cslib.BitString.weight b = n - Cslib.BitString.weight a
    rw [hw]
  let e1 : Sb ≃ Sa := Fintype.equivOfCardEq h1
  let e0 : (univ \ Sb : Finset (Fin n)) ≃ (univ \ Sa : Finset (Fin n)) :=
    Fintype.equivOfCardEq h0
  let toFun : Fin n → Fin n := fun i =>
    if hi : i ∈ Sb then (e1 ⟨i, hi⟩).1 else (e0 ⟨i, mem_sdiff.2 ⟨mem_univ i, hi⟩⟩).1
  let invFun : Fin n → Fin n := fun j =>
    if hj : j ∈ Sa then (e1.symm ⟨j, hj⟩).1 else (e0.symm ⟨j, mem_sdiff.2 ⟨mem_univ j, hj⟩⟩).1
  have hleft : Function.LeftInverse invFun toFun := fun i => by
    by_cases hi : i ∈ Sb
    · have hmem : toFun i ∈ Sa := by
        dsimp only [toFun]; rw [dite_eq_left hi]; exact (e1 ⟨i, hi⟩).2
      dsimp only [invFun]
      rw [dite_eq_left hmem]
      dsimp only [toFun]
      simp only [hi, ↓reduceDIte]
      exact congr_arg Subtype.val (e1.symm_apply_apply ⟨i, hi⟩)
    · have hmem : toFun i ∉ Sa := by
        dsimp only [toFun]
        rw [dite_eq_right hi]
        exact (mem_sdiff.1 (e0 ⟨i, mem_sdiff.2 ⟨mem_univ i, hi⟩⟩).2).2
      dsimp only [invFun]
      rw [dite_eq_right hmem]
      dsimp only [toFun]
      simp only [hi, ↓reduceDIte]
      exact congr_arg Subtype.val (e0.symm_apply_apply _)
  have hright : Function.RightInverse invFun toFun := fun j => by
    by_cases hj : j ∈ Sa
    · have hmem : invFun j ∈ Sb := by
        dsimp only [invFun]
        rw [dite_eq_left hj]
        exact (e1.symm ⟨j, hj⟩).2
      dsimp only [toFun]
      rw [dite_eq_left hmem]
      dsimp only [invFun]
      simp only [hj, ↓reduceDIte]
      exact congr_arg Subtype.val (e1.apply_symm_apply ⟨j, hj⟩)
    · have hmem : invFun j ∉ Sb := by
        dsimp only [invFun]
        rw [dite_eq_right hj]
        exact (mem_sdiff.1 (e0.symm ⟨j, mem_sdiff.2 ⟨mem_univ j, hj⟩⟩).2).2
      dsimp only [toFun]
      rw [dite_eq_right hmem]
      dsimp only [invFun]
      simp only [hj, ↓reduceDIte]
      exact congr_arg Subtype.val (e0.apply_symm_apply _)
  refine ⟨⟨toFun, invFun, hleft, hright⟩, funext fun i => ?_⟩
  change b i = a (toFun i)
  by_cases hbi : b i = true
  · have hi : i ∈ Sb := mem_filter.2 ⟨mem_univ i, hbi⟩
    have hai : a (toFun i) = true := by
      simp only [toFun, hi, ↓reduceDIte]
      exact (mem_filter.1 (e1 ⟨i, hi⟩).2).2
    rw [hbi, hai]
  · have hi : i ∉ Sb := fun h => hbi (mem_filter.1 h).2
    have hai : ¬ a (toFun i) = true := by
      simp only [toFun, hi, ↓reduceDIte]
      intro ha_t
      exact (mem_sdiff.1 (e0 ⟨i, mem_sdiff.2 ⟨mem_univ i, hi⟩⟩).2).2
        (mem_filter.2 ⟨mem_univ _, ha_t⟩)
    simp only [Bool.not_eq_true] at hbi hai
    rw [hbi, hai]

private theorem add_one_pow_ge_pow_add_one {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    n ^ (m + 1) + 1 ≤ (n + 1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc n ^ (m + 2) + 1 ≤ n ^ (m + 2) + n ^ (m + 1) + n + 1 := by omega
      _ = (n ^ (m + 1) + 1) * (n + 1) := by ring
      _ ≤ (n + 1) ^ (m + 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) ih
      _ = (n + 1) ^ (m + 2) := (pow_succ (n + 1) (m + 1)).symm

/-- Any symmetric torus polynomial `P ∈ ℝ[x₁, ..., xₙ]` (`n ≥ 1`) approximating
`Cslib.threshold n n` within error `ε < 1 / (2 * n)` satisfies
`n < (P.totalDegree + 1) ^ 2 * (⌊log₂(n + 1)⌋ + 1)`. -/
theorem sym_torus_approx_threshold_self_degree_lb {n : ℕ} (hn : 1 ≤ n)
    {P : MvPolynomial (Fin n) ℝ} (hsym : P.IsSymmetric) {ε : ℝ}
    (happ : IsTorusApprox P (Cslib.threshold n n) ε) (hε : ε < 1 / (2 * (n : ℝ))) :
    n < (P.totalDegree + 1) ^ 2 * (Nat.log 2 (n + 1) + 1) := by
  set d := P.totalDegree
  by_contra hle
  push Not at hle
  let g : Cslib.BitString n → ℝ := fun x => MvPolynomial.eval (boolPoint ℝ x) P
  have hg : g ∈ Cslib.BitString.lowDegree ℝ (Fin n) d :=
    Cslib.BitString.eval_mem_lowDegree (q := d) P le_rfl
  obtain ⟨q, hqdeg, hqavg⟩ := Cslib.BitString.exists_natDegree_le_eval_eq_layerAverage hg
  have hg_const {x y : Cslib.BitString n}
      (hw : Cslib.BitString.weight x = Cslib.BitString.weight y) : g x = g y := by
    obtain ⟨π, rfl⟩ := exists_perm_of_weight_eq hw
    change MvPolynomial.eval (boolPoint ℝ x) P = MvPolynomial.eval (boolPoint ℝ (x ∘ π)) P
    rw [boolPoint_comp, ← MvPolynomial.eval_rename, hsym π]
  have hrep (u : Fin (n + 1)) : ∃ a : Cslib.BitString n,
      Cslib.BitString.weight a = u.1 ∧ q.eval (u.1 : ℝ) = g a := by
    obtain ⟨a, ha⟩ := Cslib.BitString.weightLayer_nonempty (n := n) (Nat.le_of_lt_succ u.2)
    have hwa : Cslib.BitString.weight a = u.1 := Cslib.BitString.mem_weightLayer.1 ha
    refine ⟨a, hwa, ?_⟩
    rw [hqavg u.1 (by rw [Fintype.card_fin]; exact Nat.le_of_lt_succ u.2),
      Cslib.BitString.layerAverage]
    have hne : ({x : Cslib.BitString n | Cslib.BitString.weight x = u.1} :
        Finset (Cslib.BitString n)).Nonempty := ⟨a, by simp [hwa]⟩
    rw [Finset.expect_eq_sum_div_card]
    have hsum : (∑ x ∈ ({x : Cslib.BitString n | Cslib.BitString.weight x = u.1} :
        Finset (Cslib.BitString n)), g x) =
        #({x : Cslib.BitString n | Cslib.BitString.weight x = u.1} :
          Finset (Cslib.BitString n)) • g a := by
      rw [← Finset.sum_const]
      exact Finset.sum_congr rfl fun x hx => hg_const ((mem_filter.1 hx).2.trans hwa.symm)
    rw [hsum, nsmul_eq_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hne.card_pos.ne')]
  choose rep hrep_wt hrep_eval using hrep
  have hpow_bound (c : Fin n → Bool) (j : Fin (d + 1)) :
      (∑ k : Fin n, if c k then (k : ℕ) ^ j.1 else 0) < (n + 1) ^ (d + 1) := by
    have hk_le (k : Fin n) : (if c k then (k : ℕ) ^ j.1 else 0) ≤ n ^ d := by
      split_ifs
      · rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
        · rw [hk0]
          rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
          · rw [hj0, pow_zero]
            exact Nat.one_le_pow d n hn
          · rw [zero_pow hjpos.ne']
            exact Nat.zero_le _
        · calc (k : ℕ) ^ j.1 ≤ n ^ j.1 := Nat.pow_le_pow_left k.2.le j.1
            _ ≤ n ^ d := Nat.pow_le_pow_right hn (Nat.le_of_lt_succ j.2)
      · exact Nat.zero_le _
    calc (∑ k : Fin n, if c k then (k : ℕ) ^ j.1 else 0)
        ≤ ∑ _k : Fin n, n ^ d := Finset.sum_le_sum fun k _ => hk_le k
      _ = n * n ^ d := by simp [smul_eq_mul]
      _ = n ^ (d + 1) := (pow_succ' n d).symm
      _ < n ^ (d + 1) + 1 := Nat.lt_succ_self _
      _ ≤ (n + 1) ^ (d + 1) := add_one_pow_ge_pow_add_one hn d
  let Φ : (Fin n → Bool) → Fin (d + 1) → Fin ((n + 1) ^ (d + 1)) :=
    fun c j => ⟨∑ k : Fin n, if c k then (k : ℕ) ^ j.1 else 0, hpow_bound c j⟩
  have hcard_lt : Fintype.card (Fin (d + 1) → Fin ((n + 1) ^ (d + 1))) <
      Fintype.card (Fin n → Bool) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, ← pow_mul, ← sq]
    have hlog : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by decide) (n + 1)
    calc (n + 1) ^ ((d + 1) ^ 2)
        < (2 ^ (Nat.log 2 (n + 1) + 1)) ^ ((d + 1) ^ 2) :=
          Nat.pow_lt_pow_left hlog (by positivity)
      _ = 2 ^ ((Nat.log 2 (n + 1) + 1) * (d + 1) ^ 2) := (pow_mul _ _ _).symm
      _ = 2 ^ ((d + 1) ^ 2 * (Nat.log 2 (n + 1) + 1)) := by rw [mul_comm]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hle
  obtain ⟨c₁, c₂, hc_ne, hΦeq⟩ := Fintype.exists_ne_map_eq_of_card_lt Φ hcard_lt
  let v : ℕ → ℤ := fun k =>
    if hk : k < n then Cslib.BitString.bitVal ℤ (c₁ ⟨k, hk⟩) -
      Cslib.BitString.bitVal ℤ (c₂ ⟨k, hk⟩) else 0
  have hne_supp : ((range n).filter fun k => v k ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc_ne
    refine ⟨i.1, mem_filter.2 ⟨mem_range.2 i.2, ?_⟩⟩
    simp only [v, i.2, ↓reduceDIte]
    cases hc1 : c₁ i <;> cases hc2 : c₂ i <;> simp_all [Cslib.BitString.bitVal]
  let m : ℕ := ((range n).filter fun k => v k ≠ 0).max' hne_supp
  have hm_mem := max'_mem ((range n).filter fun k => v k ≠ 0) hne_supp
  have hm_lt : m < n := mem_range.1 (mem_filter.1 hm_mem).1
  have hvm_ne : v m ≠ 0 := (mem_filter.1 hm_mem).2
  have hv_above {k : ℕ} (hk : m < k) : v k = 0 := by
    by_cases hkn : k < n
    · by_contra hvk
      exact not_le_of_gt hk (le_max' _ k (mem_filter.2 ⟨mem_range.2 hkn, hvk⟩))
    · simp [v, hkn]
  have hv_abs (k : ℕ) : |(v k : ℝ)| ≤ 1 := by
    by_cases hkn : k < n
    · simp only [v, hkn, ↓reduceDIte]
      cases c₁ ⟨k, hkn⟩ <;> cases c₂ ⟨k, hkn⟩ <;> norm_num [Cslib.BitString.bitVal]
    · simp [v, hkn]
  have hvm_odd : v m = 1 ∨ v m = -1 := by
    simp only [v, hm_lt, ↓reduceDIte] at hvm_ne ⊢
    cases hc1 : c₁ ⟨m, hm_lt⟩ <;> cases hc2 : c₂ ⟨m, hm_lt⟩ <;>
      simp_all [Cslib.BitString.bitVal]
  have hv_moments (j : ℕ) (hj : j ≤ d) :
      (∑ k ∈ range (m + 1), (v k : ℝ) * (k : ℝ) ^ j) = 0 := by
    have hΦj := congr_arg (fun f => (f ⟨j, Nat.lt_succ_of_le hj⟩).1) hΦeq
    simp only [Φ] at hΦj
    have hsum_n : (∑ k ∈ range n, (v k : ℝ) * (k : ℝ) ^ j) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have hsplit : ∀ k : Fin n, (v k.1 : ℝ) * (k.1 : ℝ) ^ j =
          (if c₁ k then ((k.1 ^ j : ℕ) : ℝ) else 0) -
          (if c₂ k then ((k.1 ^ j : ℕ) : ℝ) else 0) := by
        intro k
        simp only [v, k.2, ↓reduceDIte]
        cases c₁ k <;> cases c₂ k <;> simp [Cslib.BitString.bitVal]
      simp_rw [hsplit, Finset.sum_sub_distrib]
      have hcast : (∑ k : Fin n, if c₁ k then ((k.1 ^ j : ℕ) : ℝ) else 0) =
          ((∑ k : Fin n, if c₁ k then k.1 ^ j else 0 : ℕ) : ℝ) := by
        push_cast
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      have hcast2 : (∑ k : Fin n, if c₂ k then ((k.1 ^ j : ℕ) : ℝ) else 0) =
          ((∑ k : Fin n, if c₂ k then k.1 ^ j else 0 : ℕ) : ℝ) := by
        push_cast
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      rw [hcast, hcast2, hΦj, sub_self]
    rw [← hsum_n]
    refine Finset.sum_subset (range_mono (by omega : m + 1 ≤ n)) fun k _ hkm => ?_
    rw [mem_range, not_lt] at hkm
    rw [hv_above (by omega), Int.cast_zero, zero_mul]
  let s : ℕ := n - m
  have hs_pos : 1 ≤ s := by omega
  let γ : Fin (n + 1) → ℤ := fun u => if u.1 < s then 0 else v (u.1 - s)
  have hγ_zero : γ 0 = 0 := by simp [γ, show (0 : ℕ) < s by omega]
  have hγ_last : γ (Fin.last n) = v m := by
    simp [γ, Fin.last, show ¬ n < s by omega, show n - s = m by omega]
  have hγ_l1 : (∑ u : Fin (n + 1), |(γ u : ℝ)|) ≤ (n : ℝ) := by
    rw [← Finset.add_sum_erase univ (fun u : Fin (n + 1) => |(γ u : ℝ)|) (mem_univ 0),
      hγ_zero, Int.cast_zero, abs_zero, zero_add]
    calc (∑ u ∈ univ.erase (0 : Fin (n + 1)), |(γ u : ℝ)|)
        ≤ ∑ _u ∈ univ.erase (0 : Fin (n + 1)), (1 : ℝ) := by
          refine Finset.sum_le_sum fun u _ => ?_
          simp only [γ]
          split_ifs
          · simp
          · exact hv_abs _
      _ = (n : ℝ) := by simp [card_erase_of_mem]
  have hγ_orth : (∑ u : Fin (n + 1), (γ u : ℝ) * q.eval (u.1 : ℝ)) = 0 := by
    let r : Polynomial ℝ := q.comp (Polynomial.X + Polynomial.C (s : ℝ))
    have hr_deg : r.natDegree ≤ d := by
      calc r.natDegree ≤ q.natDegree * (Polynomial.X + Polynomial.C (s : ℝ)).natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ d * 1 := Nat.mul_le_mul hqdeg (Polynomial.natDegree_add_C.trans_le (by simp))
        _ = d := mul_one d
    have hr_vanish : (∑ k ∈ range (m + 1), (v k : ℝ) * r.eval (k : ℝ)) = 0 := by
      have heval (k : ℕ) : r.eval (k : ℝ) = ∑ j ∈ range (d + 1), r.coeff j * (k : ℝ) ^ j :=
        Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hr_deg) (k : ℝ)
      simp_rw [heval, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hpull : (∑ k ∈ range (m + 1), (v k : ℝ) * (r.coeff j * (k : ℝ) ^ j)) =
          r.coeff j * ∑ k ∈ range (m + 1), (v k : ℝ) * (k : ℝ) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hpull, hv_moments j (Nat.lt_succ_iff.1 (mem_range.1 hj)), mul_zero]
    dsimp only [γ]
    rw [Fin.sum_univ_eq_sum_range (fun u => ((if u < s then (0 : ℤ) else v (u - s) : ℤ) : ℝ) *
      q.eval (u : ℝ))]
    have hsplit := Finset.sum_range_add
      (fun u => ((if u < s then (0 : ℤ) else v (u - s) : ℤ) : ℝ) * q.eval (u : ℝ)) s (m + 1)
    rw [show s + (m + 1) = n + 1 by omega] at hsplit
    rw [hsplit]
    have hleft : (∑ u ∈ range s, ((if u < s then (0 : ℤ) else v (u - s) : ℤ) : ℝ) *
        q.eval (u : ℝ)) = 0 :=
      Finset.sum_eq_zero fun u hu => by simp [mem_range.1 hu]
    have hright : (∑ k ∈ range (m + 1),
        ((if s + k < s then (0 : ℤ) else v (s + k - s) : ℤ) : ℝ) * q.eval ((s + k : ℕ) : ℝ)) =
        ∑ k ∈ range (m + 1), (v k : ℝ) * r.eval (k : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hlt : ¬ s + k < s := by omega
      rw [ite_eq_right hlt, Nat.add_sub_cancel_left]
      congr 1
      simp [r, Polynomial.eval_comp, add_comm]
    rw [hleft, zero_add, hright, hr_vanish]
  obtain ⟨hε0, _, Z, hZ⟩ := happ
  let fval : Fin (n + 1) → ℝ := fun u => if u.1 = n then 1 / 2 else 0
  have hfval_eq (u : Fin (n + 1)) :
      Cslib.BitString.bitVal ℝ (Cslib.threshold n n (rep u)) / 2 = fval u := by
    by_cases hun : u.1 = n
    · have ht : Cslib.threshold n n (rep u) = true :=
        threshold_self_eq_true_iff_weight.2 ((hrep_wt u).trans hun)
      simp [fval, hun, ht]
    · have hf : Cslib.threshold n n (rep u) = false :=
        threshold_self_of_weight_lt ((hrep_wt u).trans_lt (by omega))
      simp [fval, hun, hf]
  let δ : Fin (n + 1) → ℝ := fun u => q.eval (u.1 : ℝ) - ((Z (rep u) : ℝ) + fval u)
  have hδ_le (u : Fin (n + 1)) : |δ u| ≤ ε := by
    simpa only [δ, ← hfval_eq u, hrep_eval u] using hZ (rep u)
  let M_int : ℤ := 2 * (∑ u : Fin (n + 1), γ u * Z (rep u)) + γ (Fin.last n)
  have hM_ne : M_int ≠ 0 := by
    dsimp only [M_int]
    rw [hγ_last]
    rcases hvm_odd with h1 | hm1 <;> omega
  have hM_ge : (1 : ℝ) ≤ |(M_int : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |M_int| := Int.one_le_abs hM_ne
    rw [← Int.cast_abs]
    exact_mod_cast h1
  have hident : -(∑ u : Fin (n + 1), (γ u : ℝ) * δ u) = (M_int : ℝ) / 2 := by
    have hsum_δ : (∑ u : Fin (n + 1), (γ u : ℝ) * δ u) =
        (∑ u : Fin (n + 1), (γ u : ℝ) * q.eval (u.1 : ℝ)) -
          (∑ u : Fin (n + 1), (γ u : ℝ) * (Z (rep u) : ℝ)) -
          (∑ u : Fin (n + 1), (γ u : ℝ) * fval u) := by
      simp only [δ, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have hfsum : (∑ u : Fin (n + 1), (γ u : ℝ) * fval u) = (γ (Fin.last n) : ℝ) / 2 := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · simp [fval, Fin.last, div_eq_mul_inv]
      · intro u _ hu
        have hun : u.1 ≠ n := fun h => hu (Fin.ext h)
        simp [fval, hun]
      · simp
    rw [hsum_δ, hγ_orth, hfsum]
    simp only [M_int, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sum]
    ring
  have hhalf_le : (1 : ℝ) / 2 ≤ |∑ u : Fin (n + 1), (γ u : ℝ) * δ u| := by
    have habs : |∑ u : Fin (n + 1), (γ u : ℝ) * δ u| = |(M_int : ℝ)| / 2 := by
      rw [← abs_neg, hident, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hub : |∑ u : Fin (n + 1), (γ u : ℝ) * δ u| < 1 / 2 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    calc |∑ u : Fin (n + 1), (γ u : ℝ) * δ u|
        ≤ ∑ u : Fin (n + 1), |(γ u : ℝ) * δ u| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u : Fin (n + 1), |(γ u : ℝ)| * |δ u| :=
          Finset.sum_congr rfl fun _ _ => abs_mul _ _
      _ ≤ ∑ u : Fin (n + 1), |(γ u : ℝ)| * ε :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hδ_le u) (abs_nonneg _)
      _ = (∑ u : Fin (n + 1), |(γ u : ℝ)|) * ε := (Finset.sum_mul _ _ _).symm
      _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_right hγ_l1 hε0
      _ < (n : ℝ) * (1 / (2 * (n : ℝ))) := mul_lt_mul_of_pos_left hε hn_pos
      _ = 1 / 2 := by field_simp
  linarith

/-- If `P ∈ ℝ[x₁, ..., xₙ]` (`n ≥ 1`) approximates `Cslib.threshold n n` on the torus within error
`ε' < (1 / 2) ^ (deg(P) + 1)`, then `(1 - 4 * ε') * n ≤ 2 * deg(P) ^ 2`. -/
theorem torus_approx_threshold_self_nisan_szegedy {n : ℕ} (hn : 1 ≤ n)
    {P : MvPolynomial (Fin n) ℝ} {ε' : ℝ} (happ : IsTorusApprox P (Cslib.threshold n n) ε')
    (hε'_pow : ε' < (1 / 2 : ℝ) ^ (P.totalDegree + 1)) :
    (1 - 4 * ε') * (n : ℝ) ≤ 2 * (P.totalDegree : ℝ) ^ 2 := by
  set d := P.totalDegree
  obtain ⟨hε'0, _, Z, hZ⟩ := happ
  by_cases hdn : n ≤ d
  · have hdR : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  push Not at hdn
  let ind : Finset (Fin n) → Cslib.BitString n := fun T i => decide (i ∈ T)
  let cMob : Finset (Fin n) → ℤ := Cslib.BitString.subsetMobius (fun T => Z (ind T))
  let Q₀ : MvPolynomial (Fin n) ℤ :=
    ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => #S ≤ d),
      MvPolynomial.C (cMob S) * ∏ i ∈ S, MvPolynomial.X i
  have hQ₀_deg : Q₀.totalDegree ≤ d := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun S hS => ?_)
    have hcard : #S ≤ d := (mem_filter.1 hS).2
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hC : (MvPolynomial.C (cMob S) : MvPolynomial (Fin n) ℤ).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    have hprod : (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)).totalDegree ≤ #S := by
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      have := sum_le_card_nsmul S
        (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ).totalDegree) 1 fun i _ => by simp
      simpa only [smul_eq_mul, mul_one] using this
    omega
  let P₁ : MvPolynomial (Fin n) ℝ := P - Q₀.map (Int.castRingHom ℝ)
  have hP₁_deg : P₁.totalDegree ≤ d :=
    (totalDegree_sub_le _ _).trans
      (max_le le_rfl ((totalDegree_map_le _ Q₀).trans hQ₀_deg))
  let g₁ : Cslib.BitString n → ℝ := fun a => MvPolynomial.eval (boolPoint ℝ a) P₁
  have hg₁ : g₁ ∈ Cslib.BitString.lowDegree ℝ (Fin n) d :=
    Cslib.BitString.eval_mem_lowDegree (q := d) P₁ hP₁_deg
  let Z₁ : Cslib.BitString n → ℤ := fun a => Z a - MvPolynomial.eval (boolPoint ℤ a) Q₀
  have hZ₁_approx (a : Cslib.BitString n) :
      |g₁ a - ((Z₁ a : ℝ) + Cslib.BitString.bitVal ℝ (Cslib.threshold n n a) / 2)| ≤ ε' := by
    dsimp only [g₁, P₁, Z₁]
    rw [map_sub, eval_map_boolPoint, Int.cast_sub]
    have heq : MvPolynomial.eval (boolPoint ℝ a) P - (MvPolynomial.eval (boolPoint ℤ a) Q₀ : ℝ) -
        ((Z a : ℝ) - (MvPolynomial.eval (boolPoint ℤ a) Q₀ : ℝ) +
          Cslib.BitString.bitVal ℝ (Cslib.threshold n n a) / 2) =
        MvPolynomial.eval (boolPoint ℝ a) P -
          ((Z a : ℝ) + Cslib.BitString.bitVal ℝ (Cslib.threshold n n a) / 2) := by ring
    rw [heq]
    exact hZ a
  have hZ₁_low {T : Finset (Fin n)} (hT : #T ≤ d) : Z₁ (ind T) = 0 := by
    have heval_ind : MvPolynomial.eval (boolPoint ℤ (ind T)) Q₀ = Z (ind T) := by
      simp only [Q₀, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_prod, MvPolynomial.eval_X, boolPoint_apply, ind]
      have hterm (S : Finset (Fin n)) :
          (∏ i ∈ S, Cslib.BitString.bitVal ℤ (decide (i ∈ T))) =
            if S ⊆ T then (1 : ℤ) else 0 := by
        split_ifs with hST
        · exact prod_eq_one fun i hi => by simp [hST hi]
        · obtain ⟨i, hiS, hiT⟩ := not_subset.1 hST
          exact prod_eq_zero hiS (by simp [hiT])
      simp_rw [hterm, mul_ite, mul_one, mul_zero, ← sum_filter]
      have hfilt : ((univ.filter fun S : Finset (Fin n) => #S ≤ d).filter (· ⊆ T)) =
          T.powerset := by
        ext S
        simp only [mem_filter, mem_univ, true_and, mem_powerset]
        exact ⟨And.right, fun hST => ⟨(card_le_card hST).trans hT, hST⟩⟩
      rw [hfilt]
      exact Cslib.BitString.sum_powerset_subsetMobius (fun U => Z (ind U)) T
    simp only [Z₁, heval_ind, sub_self]
  have hZ₁_below_n : ∀ w : ℕ, w < n → ∀ T : Finset (Fin n), #T = w → Z₁ (ind T) = 0 := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hwn T hTw
      by_cases hwd : w ≤ d
      · exact hZ₁_low (hTw ▸ hwd)
      push Not at hwd
      obtain ⟨S₁, hS₁T, hS₁card⟩ := exists_subset_card_eq (by omega : w - (d + 1) ≤ #T)
      set Dset : Finset (Fin n) := T \ S₁
      have hDcard : #Dset = d + 1 := by
        rw [card_sdiff_of_subset hS₁T, hTw, hS₁card]
        omega
      let g₁' : Cslib.BitString n → ℝ := fun y => g₁ fun i => if i ∈ S₁ then true else y i
      have hg₁' : g₁' ∈ Cslib.BitString.lowDegree ℝ (Fin n) d := by
        refine Cslib.BitString.comp_mem_lowDegree (fun i => ?_) hg₁
        by_cases hi : i ∈ S₁
        · simpa [hi] using Cslib.BitString.const_mem_lowDegree (R := ℝ) (ι := Fin n) 1
            (Cslib.BitString.bitVal ℝ true)
        · simpa [hi] using Cslib.BitString.bitVal_mem_lowDegree (R := ℝ) i
      have hmob_zero : Cslib.BitString.subsetMobius (fun U => g₁' (ind U)) Dset = 0 :=
        Cslib.BitString.subsetMobius_eq_zero_of_mem_lowDegree hg₁' (by omega)
      have hind_eq {U : Finset (Fin n)} (_hU : U ∈ Dset.powerset) :
          (fun i => if i ∈ S₁ then true else decide (i ∈ U)) = ind (S₁ ∪ U) := by
        funext i
        simp only [ind]
        by_cases hi : i ∈ S₁ <;> simp [hi]
      have hZ₁_sub {U : Finset (Fin n)} (hU : U ∈ Dset.powerset) (hne : U ≠ Dset) :
          Z₁ (ind (S₁ ∪ U)) = 0 := by
        have hUD : U ⊂ Dset := (mem_powerset.1 hU).ssubset_of_ne hne
        have hdisj : Disjoint S₁ U :=
          disjoint_of_subset_right (mem_powerset.1 hU) disjoint_sdiff_self_right
        have hcard_lt : #(S₁ ∪ U) < w := by
          rw [card_union_of_disjoint hdisj, hS₁card]
          have := card_lt_card hUD
          omega
        exact ih #(S₁ ∪ U) hcard_lt (hcard_lt.trans hwn) (S₁ ∪ U) rfl
      have hand_sub {U : Finset (Fin n)} (hU : U ∈ Dset.powerset) :
          Cslib.threshold n n (ind (S₁ ∪ U)) = false := by
        refine threshold_self_of_weight_lt ?_
        have hsub : S₁ ∪ U ⊆ T :=
          union_subset hS₁T ((mem_powerset.1 hU).trans sdiff_subset)
        have hwt : Cslib.BitString.weight (ind (S₁ ∪ U)) = #(S₁ ∪ U) := by
          simp only [Cslib.BitString.weight, ind, decide_eq_true_eq]
          congr 1
          ext i
          simp
        exact hwt.trans_lt ((card_le_card hsub).trans_lt (hTw ▸ hwn))
      have hZT_eq : (Z₁ (ind T) : ℝ) =
          -(∑ U ∈ Dset.powerset, (-1 : ℝ) ^ (#Dset - #U) *
            (g₁ (ind (S₁ ∪ U)) - ((Z₁ (ind (S₁ ∪ U)) : ℝ) +
              Cslib.BitString.bitVal ℝ (Cslib.threshold n n (ind (S₁ ∪ U))) / 2))) := by
        have hsum_g : (∑ U ∈ Dset.powerset, (-1 : ℝ) ^ (#Dset - #U) * g₁ (ind (S₁ ∪ U))) = 0 := by
          rw [← hmob_zero, Cslib.BitString.subsetMobius]
          refine Finset.sum_congr rfl fun U hU => ?_
          dsimp only [g₁']
          rw [hind_eq hU, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
        have hsum_Z : (∑ U ∈ Dset.powerset, (-1 : ℝ) ^ (#Dset - #U) *
            ((Z₁ (ind (S₁ ∪ U)) : ℝ) +
              Cslib.BitString.bitVal ℝ (Cslib.threshold n n (ind (S₁ ∪ U))) / 2)) =
            (Z₁ (ind T) : ℝ) := by
          rw [Finset.sum_eq_single Dset]
          · rw [hand_sub (mem_powerset_self Dset), Cslib.BitString.bitVal_false, zero_div,
              add_zero, tsub_self, pow_zero, one_mul, union_sdiff_of_subset hS₁T]
          · intro U hU hne
            rw [hZ₁_sub hU hne, hand_sub hU, Int.cast_zero, Cslib.BitString.bitVal_false,
              zero_div, add_zero, mul_zero]
          · exact fun h => absurd (mem_powerset_self Dset) h
        simp only [mul_sub, Finset.sum_sub_distrib, hsum_g, hsum_Z, zero_sub, neg_neg]
      have habs_lt : |(Z₁ (ind T) : ℝ)| < 1 := by
        rw [hZT_eq, abs_neg]
        calc |∑ U ∈ Dset.powerset, (-1 : ℝ) ^ (#Dset - #U) *
              (g₁ (ind (S₁ ∪ U)) - ((Z₁ (ind (S₁ ∪ U)) : ℝ) +
                Cslib.BitString.bitVal ℝ (Cslib.threshold n n (ind (S₁ ∪ U))) / 2))|
            ≤ ∑ U ∈ Dset.powerset, |(-1 : ℝ) ^ (#Dset - #U) *
                (g₁ (ind (S₁ ∪ U)) - ((Z₁ (ind (S₁ ∪ U)) : ℝ) +
                  Cslib.BitString.bitVal ℝ (Cslib.threshold n n (ind (S₁ ∪ U))) / 2))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _U ∈ Dset.powerset, ε' := by
              refine Finset.sum_le_sum fun U _ => ?_
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
              exact hZ₁_approx (ind (S₁ ∪ U))
          _ = ((2 : ℝ) ^ (d + 1)) * ε' := by
              rw [Finset.sum_const, card_powerset, hDcard, nsmul_eq_mul, Nat.cast_pow,
                Nat.cast_ofNat]
          _ < ((2 : ℝ) ^ (d + 1)) * ((1 / 2 : ℝ) ^ (d + 1)) :=
              mul_lt_mul_of_pos_left hε'_pow (by positivity)
          _ = 1 := by rw [← mul_pow]; norm_num
      have hnat : (Z₁ (ind T)).natAbs < 1 := by
        have : ((Z₁ (ind T)).natAbs : ℝ) < 1 := by simpa using habs_lt
        exact_mod_cast this
      exact Int.natAbs_eq_zero.1 (by omega)
  let allTrue : Cslib.BitString n := fun _ => true
  let cTop : ℝ := (Z₁ allTrue : ℝ) + 1 / 2
  have hcTop_abs : (1 : ℝ) / 2 ≤ |cTop| := by
    have hne_odd : (2 * Z₁ allTrue + 1 : ℤ) ≠ 0 := by omega
    have hge1 : (1 : ℤ) ≤ |2 * Z₁ allTrue + 1| := Int.one_le_abs hne_odd
    have hge1R : (1 : ℝ) ≤ |((2 * Z₁ allTrue + 1 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast hge1
    have hcTop_eq : cTop = ((2 * Z₁ allTrue + 1 : ℤ) : ℝ) / 2 := by
      simp only [cTop, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
      ring
    rw [hcTop_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  let pReal : Cslib.BitString n → ℝ := cTop⁻¹ • g₁
  have hpReal_deg : pReal ∈ Cslib.BitString.lowDegree ℝ (Fin n) d :=
    Submodule.smul_mem _ _ hg₁
  have hpReal_approx (a : Cslib.BitString n) :
      |pReal a - Cslib.BitString.bitVal ℝ (Cslib.threshold n n a)| ≤ 2 * ε' := by
    by_cases ha : Cslib.BitString.weight a = n
    · have ha_eq : a = allTrue := by
        have ht : Cslib.threshold n n a = true := threshold_self_eq_true_iff_weight.2 ha
        rw [Cslib.threshold_self, decide_eq_true_eq] at ht
        funext i
        exact ht i
      subst ha_eq
      have ht : Cslib.threshold n n allTrue = true := by
        rw [Cslib.threshold_self, decide_eq_true_eq]
        exact fun _ => rfl
      have hcTop_ne : cTop ≠ 0 := fun h => by linarith [hcTop_abs, show |cTop| = 0 by simp [h]]
      have hdiff : pReal allTrue - Cslib.BitString.bitVal ℝ (Cslib.threshold n n allTrue) =
          (g₁ allTrue - cTop) / cTop := by
        simp only [pReal, Pi.smul_apply, smul_eq_mul, ht, Cslib.BitString.bitVal_true]
        field_simp
      rw [hdiff, abs_div]
      have hnum : |g₁ allTrue - cTop| ≤ ε' := by
        simpa [cTop, ht] using hZ₁_approx allTrue
      exact (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hcTop_abs).trans
        (by linarith)
    · have hlt : Cslib.BitString.weight a < n :=
        lt_of_le_of_ne (Cslib.BitString.weight_le_length a) ha
      let Ta : Finset (Fin n) := univ.filter fun i => a i = true
      have hind_Ta : ind Ta = a := by
        funext i
        simp [ind, Ta]
      have hZa0 : Z₁ a = 0 := by
        rw [← hind_Ta]
        exact hZ₁_below_n #Ta hlt Ta rfl
      have hf : Cslib.threshold n n a = false := threshold_self_of_weight_lt hlt
      have hnum : |g₁ a| ≤ ε' := by
        simpa [hZa0, hf] using hZ₁_approx a
      have hdiff : pReal a - Cslib.BitString.bitVal ℝ (Cslib.threshold n n a) = g₁ a / cTop := by
        simp [pReal, hf, div_eq_inv_mul]
      rw [hdiff, abs_div]
      exact (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hcTop_abs).trans
        (by linarith)
  have hns := Cslib.QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_of_mem_lowDegree
    hpReal_deg hpReal_approx
  have hbs : Cslib.QueryComplexity.blockSensitivity (Cslib.threshold n n) = n := by
    rw [Cslib.QueryComplexity.blockSensitivity_threshold hn le_rfl]
    omega
  rw [hbs] at hns
  linarith

/-- For `n ≥ 1` and `0 < ε < 1 / 4` in the Nisan–Szegedy regime
`2 * (log₂(1 / ε)) ^ 2 ≤ (1 - 4 * ε) * n`, any torus polynomial approximating `Cslib.threshold n n`
within error `ε' < ε` has total degree strictly greater than `log₂(1 / ε) - 1`. -/
theorem torus_approx_threshold_self_degree_gt_log_inv_eps_sub_one {n : ℕ} (hn : 1 ≤ n)
    {ε ε' : ℝ} (hε0 : 0 < ε) (_hε4 : ε < 1 / 4)
    (hregime : 2 * (Real.logb 2 (1 / ε)) ^ 2 ≤ (1 - 4 * ε) * (n : ℝ))
    {P : MvPolynomial (Fin n) ℝ} (happ : IsTorusApprox P (Cslib.threshold n n) ε') (hε' : ε' < ε) :
    Real.logb 2 (1 / ε) - 1 < (P.totalDegree : ℝ) := by
  by_contra hle
  push Not at hle
  have h1 : (P.totalDegree : ℝ) + 1 ≤ Real.logb 2 (1 / ε) := by linarith
  have hpow : (2 : ℝ) ^ (P.totalDegree + 1 : ℕ) ≤ 1 / ε := by
    rw [← Real.rpow_natCast (2 : ℝ) (P.totalDegree + 1), Nat.cast_add, Nat.cast_one]
    exact (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).1 h1
  have hε_le : ε ≤ (1 / 2 : ℝ) ^ (P.totalDegree + 1) := by
    have hmul : ε * (2 : ℝ) ^ (P.totalDegree + 1) ≤ 1 := (le_div_iff₀' hε0).1 hpow
    calc ε = ε * (2 : ℝ) ^ (P.totalDegree + 1) * (1 / 2 : ℝ) ^ (P.totalDegree + 1) := by
          rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 1 * (1 / 2 : ℝ) ^ (P.totalDegree + 1) :=
          mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = (1 / 2 : ℝ) ^ (P.totalDegree + 1) := one_mul _
  have hns := torus_approx_threshold_self_nisan_szegedy hn happ (hε'.trans_le hε_le)
  have hdeg_lt : (P.totalDegree : ℝ) < Real.logb 2 (1 / ε) := by linarith
  have hsq_lt : (P.totalDegree : ℝ) ^ 2 < (Real.logb 2 (1 / ε)) ^ 2 :=
    sq_lt_sq.2 (by
      rw [abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) P.totalDegree])]
      exact hdeg_lt)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  nlinarith

end CslibFrontier.Computability.Circuit.TorusPolynomial
