module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Data.Finsupp.Order
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Generic Linear Combinations of Polynomial Systems

For a field extension `E / F` and any finite family `f₁, ..., fₛ ∈ F[x₁, ..., xₙ]`, taking `n + 1`
linear combinations `g_j = ∑_i α_{i, j} f_i` whose coefficients `(α_{i, j}) ∈ E^{s(n+1)}` are
algebraically independent over `F` preserves the common zero locus in `E^n`.

The proof builds an iterated tower of purely transcendental extensions
`K₀ = F`, `K_{k+1} = Frac(K_k[t₁, ..., tₛ])`, shows that each generic linear combination avoids the
extended prime ideal whenever some generator lies outside it, and derives a contradiction from the
Krull dimension `ringKrullDim (MvPolynomial (Fin n) K_{n+1}) = n`.

## Main results

* `CslibFrontier.Foundations.AlgebraicGeometry.zeroLocus_linearCombination_eq`: `n + 1` generic
  linear combinations with `F`-algebraically independent coefficients in `E` have the same affine
  zero locus in `E^n` as the original polynomial family over `F`.
* `CslibFrontier.Foundations.AlgebraicGeometry.exists_algebraicIndependent_complex`: for every
  `r : ℕ`, there exists an `r`-tuple of complex numbers algebraically independent over `ℚ`.
-/

public section

namespace CslibFrontier.Foundations.AlgebraicGeometry

open MvPolynomial

private lemma exists_common_denom {A : Type*} [CommRing A] [IsDomain A] {n : ℕ}
    (p : MvPolynomial (Fin n) (FractionRing A)) :
    ∃ (d : A) (num : (Fin n →₀ ℕ) → A), d ≠ 0 ∧
      ∀ μ, algebraMap A (FractionRing A) d * p.coeff μ = algebraMap A (FractionRing A) (num μ) := by
  classical
  have hrep : ∀ μ : Fin n →₀ ℕ,
      ∃ a b : A, b ≠ 0 ∧ algebraMap A (FractionRing A) b * p.coeff μ =
        algebraMap A (FractionRing A) a := by
    intro μ
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ :=
      IsLocalization.mk'_surjective (nonZeroDivisors A) (p.coeff μ)
    refine ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, ?_⟩
    rw [← hab]
    exact IsLocalization.mk'_spec' (FractionRing A) a ⟨b, hb⟩
  choose a b hb hab using hrep
  refine ⟨∏ μ ∈ p.support, b μ,
    fun μ => if μ ∈ p.support then a μ * ∏ μ' ∈ p.support.erase μ, b μ' else 0,
    Finset.prod_ne_zero_iff.mpr fun μ _ => hb μ, ?_⟩
  intro μ
  by_cases hμ : μ ∈ p.support
  · rw [← Finset.mul_prod_erase p.support b hμ]
    simp only [hμ, ↓reduceIte, map_mul, map_prod]
    calc
      algebraMap A (FractionRing A) (b μ) * (∏ x ∈ p.support.erase μ, algebraMap A _ (b x)) *
          p.coeff μ
        = (algebraMap A (FractionRing A) (b μ) * p.coeff μ) *
            ∏ x ∈ p.support.erase μ, algebraMap A _ (b x) := by ring
      _ = algebraMap A (FractionRing A) (a μ) *
            ∏ x ∈ p.support.erase μ, algebraMap A _ (b x) := by rw [hab μ]
  · simp only [hμ, ↓reduceIte, map_zero]
    rw [MvPolynomial.notMem_support_iff.mp hμ, mul_zero]

private lemma prime_extension_step {K : Type*} [Field K] {s n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) K)) (hq : q.IsPrime) :
    let L := FractionRing (MvPolynomial (Fin s) K)
    let ι : K →+* L := (algebraMap (MvPolynomial (Fin s) K) L).comp C
    (q.map (MvPolynomial.map ι)).IsPrime ∧
    (q.map (MvPolynomial.map ι)).comap (MvPolynomial.map ι) = q ∧
    ∀ (f : Fin s → MvPolynomial (Fin n) K) (i₀ : Fin s), f i₀ ∉ q →
      (∑ i : Fin s, C (algebraMap (MvPolynomial (Fin s) K) L (X i)) *
        (f i).map ι) ∉ q.map (MvPolynomial.map ι) := by
  classical
  intro L ι
  have : q.IsPrime := hq
  let D := MvPolynomial (Fin n) K ⧸ q
  let M := FractionRing (MvPolynomial (Fin s) D)
  let mkQ : MvPolynomial (Fin n) K →+* D := Ideal.Quotient.mk q
  let kToD : K →+* D := mkQ.comp C
  have hkToD_inj : Function.Injective kToD := kToD.injective
  let mapCoeff : MvPolynomial (Fin s) K →+* M :=
    (algebraMap (MvPolynomial (Fin s) D) M).comp (MvPolynomial.map kToD)
  have hmapCoeff_inj : Function.Injective mapCoeff :=
    (IsFractionRing.injective (MvPolynomial (Fin s) D) M).comp
      (MvPolynomial.map_injective kToD hkToD_inj)
  let ψCoeff : L →+* M := IsFractionRing.lift (g := mapCoeff) hmapCoeff_inj
  have hψCoeff_alg : ∀ r : MvPolynomial (Fin s) K,
      ψCoeff (algebraMap (MvPolynomial (Fin s) K) L r) = mapCoeff r := fun r =>
    IsFractionRing.lift_algebraMap hmapCoeff_inj r
  let ψ : MvPolynomial (Fin n) L →+* M :=
    MvPolynomial.eval₂Hom ψCoeff fun j => algebraMap (MvPolynomial (Fin s) D) M (C (mkQ (X j)))
  have hψ_map : ∀ h : MvPolynomial (Fin n) K,
      ψ (h.map ι) = algebraMap (MvPolynomial (Fin s) D) M (C (mkQ h)) := by
    intro h
    induction h using MvPolynomial.induction_on with
    | C c =>
      simp [ψ, ι, map_C, hψCoeff_alg, mapCoeff, kToD]
    | add h₁ h₂ ih₁ ih₂ =>
      simp [map_add, ih₁, ih₂]
    | mul_X h j ih =>
      simp [ψ, map_mul, ih]
  have hker : RingHom.ker ψ = q.map (MvPolynomial.map ι) := by
    apply le_antisymm
    · intro p hp
      rw [RingHom.mem_ker] at hp
      obtain ⟨d, num, hd, hnum⟩ := exists_common_denom p
      let qPoly : MvPolynomial (Fin n) L := C (algebraMap (MvPolynomial (Fin s) K) L d) * p
      let Sν : Finset (Fin s →₀ ℕ) := p.support.biUnion fun μ => (num μ).support
      let hν : (Fin s →₀ ℕ) → MvPolynomial (Fin n) K :=
        fun ν => ∑ μ ∈ p.support, monomial μ ((num μ).coeff ν)
      have hqPoly_eq :
          qPoly = ∑ ν ∈ Sν, C (algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1)) *
            (hν ν).map ι := by
        ext μ
        simp only [qPoly, coeff_C_mul, coeff_sum, coeff_map]
        rw [hnum μ]
        have hsum_inner : ∀ μ' ∈ p.support,
            (∑ ν ∈ Sν, algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1) *
              ι ((monomial μ' ((num μ').coeff ν)).coeff μ)) =
            if μ' = μ then algebraMap (MvPolynomial (Fin s) K) L (num μ) else 0 := by
          intro μ' hμ'
          by_cases hμeq : μ' = μ
          · subst hμeq
            simp only [↓reduceIte, coeff_monomial]
            have hsub : (num μ').support ⊆ Sν :=
              Finset.subset_biUnion_of_mem (fun μ => (num μ).support) hμ'
            have hconv :
                (∑ ν ∈ Sν, algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1) *
                  ι ((num μ').coeff ν)) =
                algebraMap (MvPolynomial (Fin s) K) L
                  (∑ ν ∈ Sν, monomial ν ((num μ').coeff ν)) := by
              rw [map_sum]
              refine Finset.sum_congr rfl fun ν _ => ?_
              simp only [ι, RingHom.comp_apply, ← map_mul, C_apply, monomial_mul_monomial,
                add_zero, one_mul]
            rw [hconv]
            congr 1
            rw [← Finset.sum_subset hsub]
            · exact (num μ').as_sum.symm
            · intro ν _ hνnot
              rw [MvPolynomial.notMem_support_iff.mp hνnot, monomial_zero]
          · simp only [hμeq, ↓reduceIte]
            refine Finset.sum_eq_zero fun ν _ => ?_
            simp [coeff_monomial, hμeq]
        have hterm :
            (∑ ν ∈ Sν, algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1) *
              ι ((hν ν).coeff μ)) =
            ∑ μ' ∈ p.support, ∑ ν ∈ Sν,
              algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1) *
                ι ((monomial μ' ((num μ').coeff ν)).coeff μ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          simp only [hν, coeff_sum, map_sum, Finset.mul_sum]
        rw [hterm]
        have hsum_ite :
            (∑ μ' ∈ p.support,
              if μ' = μ then algebraMap (MvPolynomial (Fin s) K) L (num μ) else 0) =
            if μ ∈ p.support then algebraMap (MvPolynomial (Fin s) K) L (num μ) else 0 := by
          simp
        calc
          algebraMap (MvPolynomial (Fin s) K) L (num μ)
            = if μ ∈ p.support then algebraMap (MvPolynomial (Fin s) K) L (num μ) else 0 := by
              by_cases hμ : μ ∈ p.support
              · simp [hμ]
              · simp only [hμ, ↓reduceIte]
                have hzero := hnum μ
                rw [MvPolynomial.notMem_support_iff.mp hμ, mul_zero] at hzero
                exact hzero.symm
          _ = ∑ μ' ∈ p.support,
              if μ' = μ then algebraMap (MvPolynomial (Fin s) K) L (num μ) else 0 :=
            hsum_ite.symm
          _ = ∑ μ' ∈ p.support, ∑ ν ∈ Sν,
              algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1) *
                ι ((monomial μ' ((num μ').coeff ν)).coeff μ) := by
            refine Finset.sum_congr rfl fun μ' hμ' => (hsum_inner μ' hμ').symm
      have hψq : ψ qPoly = 0 := by
        simp [qPoly, map_mul, hp]
      have hψq_eval :
          ψ qPoly = algebraMap (MvPolynomial (Fin s) D) M
            (∑ ν ∈ Sν, monomial ν (mkQ (hν ν))) := by
        rw [hqPoly_eq, map_sum, map_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [map_mul, hψ_map]
        have hC : ψ (C (algebraMap (MvPolynomial (Fin s) K) L (monomial ν 1))) =
            algebraMap (MvPolynomial (Fin s) D) M (monomial ν 1) := by
          simp [ψ, hψCoeff_alg, mapCoeff, map_monomial]
        rw [hC, ← map_mul]
        congr 1
        rw [C_apply, monomial_mul_monomial, add_zero, one_mul]
      have hpoly_zero : (∑ ν ∈ Sν, monomial ν (mkQ (hν ν))) = 0 := by
        apply IsFractionRing.injective (MvPolynomial (Fin s) D) M
        rw [map_zero, ← hψq_eval, hψq]
      have hhν_mem : ∀ ν ∈ Sν, hν ν ∈ q := by
        intro ν hνS
        have hcoeff0 : (∑ ν' ∈ Sν, monomial ν' (mkQ (hν ν'))).coeff ν = 0 := by
          rw [hpoly_zero]
          simp
        rw [coeff_sum] at hcoeff0
        simp only [coeff_monomial] at hcoeff0
        rw [Finset.sum_ite_eq' Sν ν] at hcoeff0
        simp only [hνS, ↓reduceIte] at hcoeff0
        exact (Ideal.Quotient.eq_zero_iff_mem).mp hcoeff0
      have hqPoly_mem : qPoly ∈ q.map (MvPolynomial.map ι) := by
        rw [hqPoly_eq]
        exact Ideal.sum_mem _ fun ν hνS =>
          Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hhν_mem ν hνS))
      have hd_ne : algebraMap (MvPolynomial (Fin s) K) L d ≠ 0 := by
        intro h0
        exact hd (IsFractionRing.injective (MvPolynomial (Fin s) K) L (by simpa using h0))
      have hp_eq : p = C (algebraMap (MvPolynomial (Fin s) K) L d)⁻¹ * qPoly := by
        simp [qPoly, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd_ne]
      rw [hp_eq]
      exact Ideal.mul_mem_left _ _ hqPoly_mem
    · rw [Ideal.map_le_iff_le_comap]
      intro h hh
      rw [Ideal.mem_comap, RingHom.mem_ker, hψ_map]
      have : mkQ h = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hh
      simp [this]
  refine ⟨hker ▸ RingHom.ker_isPrime ψ, ?_, ?_⟩
  · ext h
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, hψ_map]
    constructor
    · intro h0
      have hC0 : (C (mkQ h) : MvPolynomial (Fin s) D) = 0 :=
        IsFractionRing.injective (MvPolynomial (Fin s) D) M (h0.trans (map_zero _).symm)
      have hmk0 : mkQ h = 0 := by
        have := congrArg (fun u : MvPolynomial (Fin s) D => u.coeff 0) hC0
        simpa using this
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hmk0
    · intro hh
      have hmk0 : mkQ h = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hh
      simp [hmk0]
  · intro f i₀ hi₀ hmem
    rw [← hker, RingHom.mem_ker] at hmem
    have hψg :
        ψ (∑ i : Fin s, C (algebraMap (MvPolynomial (Fin s) K) L (X i)) * (f i).map ι) =
        algebraMap (MvPolynomial (Fin s) D) M (∑ i : Fin s, X i * C (mkQ (f i))) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hψ_map]
      have hX : ψ (C (algebraMap (MvPolynomial (Fin s) K) L (X i))) =
          algebraMap (MvPolynomial (Fin s) D) M (X i) := by
        simp [ψ, hψCoeff_alg, mapCoeff]
      rw [hX, ← map_mul]
    rw [hψg] at hmem
    have hsum0 : (∑ i : Fin s, X i * C (mkQ (f i)) : MvPolynomial (Fin s) D) = 0 :=
      IsFractionRing.injective (MvPolynomial (Fin s) D) M (by simpa using hmem)
    have hcoeff0 := congrArg (fun u : MvPolynomial (Fin s) D => u.coeff (Finsupp.single i₀ 1)) hsum0
    have hzero_coeff : (0 : MvPolynomial (Fin s) D).coeff (Finsupp.single i₀ 1) = 0 := by simp
    rw [hzero_coeff, coeff_sum] at hcoeff0
    have hsingle : ∀ i : Fin s,
        (X i * C (mkQ (f i)) : MvPolynomial (Fin s) D).coeff (Finsupp.single i₀ 1) =
        if i = i₀ then mkQ (f i₀) else 0 := by
      intro i
      rw [X, C_apply, monomial_mul_monomial, add_zero, one_mul, coeff_monomial]
      by_cases hi : i = i₀
      · subst hi; simp
      · have hne : Finsupp.single i 1 ≠ Finsupp.single i₀ 1 := by
          intro heq
          have := congrArg (fun u : Fin s →₀ ℕ => u i) heq
          simp [hi] at this
        simp [hi, hne]
    simp only [hsingle, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hcoeff0
    exact hi₀ ((Ideal.Quotient.eq_zero_iff_mem).mp hcoeff0)

universe u

private noncomputable def transcTowerPair (F : Type u) [Field F] (s : ℕ) :
    ℕ → Σ K : Type u, Field K
  | 0 => ⟨F, ‹Field F›⟩
  | k + 1 =>
    let p := transcTowerPair F s k
    let _ : Field p.1 := p.2
    ⟨FractionRing (MvPolynomial (Fin s) p.1), inferInstance⟩

private noncomputable def TranscTower (F : Type u) [Field F] (s k : ℕ) : Type u :=
  (transcTowerPair F s k).1

private noncomputable local instance instFieldTranscTower (F : Type u) [Field F] (s k : ℕ) :
    Field (TranscTower F s k) :=
  (transcTowerPair F s k).2

private noncomputable local instance instAlgebraTranscTowerStep (F : Type u) [Field F] (s k : ℕ) :
    Algebra (MvPolynomial (Fin s) (TranscTower F s k)) (TranscTower F s (k + 1)) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin s) (TranscTower F s k))
    (FractionRing (MvPolynomial (Fin s) (TranscTower F s k))))

private local instance instIsFractionRingTranscTowerStep (F : Type u) [Field F] (s k : ℕ) :
    IsFractionRing (MvPolynomial (Fin s) (TranscTower F s k)) (TranscTower F s (k + 1)) :=
  inferInstanceAs (IsFractionRing (MvPolynomial (Fin s) (TranscTower F s k))
    (FractionRing (MvPolynomial (Fin s) (TranscTower F s k))))

private noncomputable def transcZeroEquiv (F : Type u) [Field F] (s : ℕ) :
    TranscTower F s 0 ≃+* F :=
  RingEquiv.refl F

private noncomputable def transcStep (F : Type u) [Field F] (s : ℕ) (k : ℕ) :
    TranscTower F s k →+* TranscTower F s (k + 1) :=
  (algebraMap (MvPolynomial (Fin s) (TranscTower F s k)) (TranscTower F s (k + 1))).comp C

private noncomputable def transcBase (F : Type u) [Field F] (s : ℕ) :
    (k : ℕ) → F →+* TranscTower F s k
  | 0 => RingHom.id F
  | k + 1 => (transcStep F s k).comp (transcBase F s k)

private noncomputable def transcLift (F : Type u) [Field F] (s : ℕ) :
    (j k : ℕ) → (hjk : j ≤ k) → TranscTower F s j →+* TranscTower F s k
  | j, 0, hjk => by
    have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
    subst hj
    exact RingHom.id F
  | j, k + 1, hjk =>
    if h : j = k + 1 then
      h ▸ RingHom.id (TranscTower F s (k + 1))
    else
      (transcStep F s k).comp (transcLift F s j k (by omega))

private lemma transcLift_succ {F : Type u} [Field F] {s j k : ℕ} (hjk : j ≤ k) :
    transcLift F s j (k + 1) (Nat.le_succ_of_le hjk) =
      (transcStep F s k).comp (transcLift F s j k hjk) := by
  conv_lhs => unfold transcLift
  have hne : j ≠ k + 1 := by omega
  simp [hne]

private lemma transcLift_refl {F : Type u} [Field F] {s k : ℕ} :
    transcLift F s k k le_rfl = RingHom.id (TranscTower F s k) := by
  cases k with
  | zero => rfl
  | succ k =>
    conv_lhs => unfold transcLift
    simp

private noncomputable def transcVar (F : Type*) [Field F] (s : ℕ) {j k : ℕ} (hjk : j < k)
    (i : Fin s) : TranscTower F s k :=
  transcLift F s (j + 1) k hjk
    (algebraMap (MvPolynomial (Fin s) (TranscTower F s j)) (TranscTower F s (j + 1)) (X i))

private lemma transcStep_transcVar {F : Type*} [Field F] {s j k : ℕ} (hjk : j < k) (i : Fin s) :
    transcStep F s k (transcVar F s hjk i) = transcVar F s (Nat.lt_succ_of_lt hjk) i := by
  simp only [transcVar, transcLift_succ hjk, RingHom.comp_apply]

private lemma transcVar_last {F : Type*} [Field F] {s k : ℕ} (i : Fin s) :
    transcVar F s (Nat.lt_succ_self k) i =
      algebraMap (MvPolynomial (Fin s) (TranscTower F s k)) (TranscTower F s (k + 1)) (X i) := by
  simp [transcVar, transcLift_refl]

private noncomputable def towerGenPoly {F : Type*} [Field F] {s n : ℕ}
    (f : Fin s → MvPolynomial (Fin n) F) {j k : ℕ} (hjk : j < k) :
    MvPolynomial (Fin n) (TranscTower F s k) :=
  ∑ i : Fin s, C (transcVar F s hjk i) * (f i).map (transcBase F s k)

private lemma map_towerGenPoly {F : Type*} [Field F] {s n : ℕ}
    (f : Fin s → MvPolynomial (Fin n) F) {j k : ℕ} (hjk : j < k) :
    (towerGenPoly f hjk).map (transcStep F s k) = towerGenPoly f (Nat.lt_succ_of_lt hjk) := by
  simp only [towerGenPoly, map_sum, map_mul, map_C, transcStep_transcVar, MvPolynomial.map_map]
  rfl

private lemma exists_prime_chain_of_tower {F : Type u} [Field F] {s n : ℕ}
    (f : Fin s → MvPolynomial (Fin n) F) :
    ∀ k : ℕ, ∀ (P : Ideal (MvPolynomial (Fin n) (TranscTower F s k))),
      (hP : P.IsPrime) →
      (∀ (j : ℕ) (hjk : j < k), towerGenPoly f hjk ∈ P) →
      (∃ i₀ : Fin s, (f i₀).map (transcBase F s k) ∉ P) →
      ∃ c : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) (TranscTower F s k))),
        c.length = k ∧ c.last = ⟨P, hP⟩ := by
  intro k
  induction k with
  | zero =>
    intro P hP _ _
    refine ⟨RelSeries.singleton _ ⟨P, hP⟩, rfl, rfl⟩
  | succ k ih =>
    intro P hP hgen hmiss
    let ι := transcStep F s k
    let P₀ : Ideal (MvPolynomial (Fin n) (TranscTower F s k)) := P.comap (MvPolynomial.map ι)
    have hP₀ : P₀.IsPrime := Ideal.IsPrime.comap (MvPolynomial.map ι)
    have hgen₀ : ∀ (j : ℕ) (hjk : j < k), towerGenPoly f hjk ∈ P₀ := by
      intro j hjk
      rw [Ideal.mem_comap, map_towerGenPoly]
      exact hgen j (Nat.lt_succ_of_lt hjk)
    have hmiss₀ : ∃ i₀ : Fin s, (f i₀).map (transcBase F s k) ∉ P₀ := by
      obtain ⟨i₀, hi₀⟩ := hmiss
      refine ⟨i₀, fun hmem => hi₀ ?_⟩
      rw [Ideal.mem_comap, MvPolynomial.map_map] at hmem
      exact hmem
    obtain ⟨c₀, hlen₀, hlast₀⟩ := ih P₀ hP₀ hgen₀ hmiss₀
    have hstep_prime : ∀ q : PrimeSpectrum (MvPolynomial (Fin n) (TranscTower F s k)),
        (q.asIdeal.map (MvPolynomial.map ι)).IsPrime := fun q =>
      (prime_extension_step q.asIdeal q.isPrime).1
    have hstep_comap : ∀ q : PrimeSpectrum (MvPolynomial (Fin n) (TranscTower F s k)),
        (q.asIdeal.map (MvPolynomial.map ι)).comap (MvPolynomial.map ι) = q.asIdeal := fun q =>
      (prime_extension_step q.asIdeal q.isPrime).2.1
    let liftSpec : PrimeSpectrum (MvPolynomial (Fin n) (TranscTower F s k)) →
        PrimeSpectrum (MvPolynomial (Fin n) (TranscTower F s (k + 1))) :=
      fun q => ⟨q.asIdeal.map (MvPolynomial.map ι), hstep_prime q⟩
    have hlift_strict : StrictMono liftSpec := by
      intro q₁ q₂ hlt
      change q₁.asIdeal.map (MvPolynomial.map ι) < q₂.asIdeal.map (MvPolynomial.map ι)
      refine lt_of_le_of_ne (Ideal.map_mono hlt.le) fun heq => hlt.ne ?_
      apply PrimeSpectrum.ext
      rw [← hstep_comap q₁, ← hstep_comap q₂, heq]
    let c₁ : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) (TranscTower F s (k + 1)))) :=
      c₀.map liftSpec hlift_strict
    obtain ⟨i₀, hi₀⟩ := hmiss₀
    have hg_not_mem : towerGenPoly f (Nat.lt_succ_self k) ∉ P₀.map (MvPolynomial.map ι) := by
      have h := (prime_extension_step P₀ hP₀).2.2 (fun i => (f i).map (transcBase F s k)) i₀ hi₀
      convert h using 1
      simp only [towerGenPoly, transcVar_last, MvPolynomial.map_map]
      rfl
    have hstrict_top : c₁.last < ⟨P, hP⟩ := by
      have hlast1 : c₁.last = liftSpec ⟨P₀, hP₀⟩ := by
        simp [c₁, hlast₀]
      rw [hlast1]
      change P₀.map (MvPolynomial.map ι) < P
      refine lt_of_le_of_ne Ideal.map_comap_le fun heq => hg_not_mem ?_
      rw [heq]
      exact hgen k (Nat.lt_succ_self k)
    refine ⟨c₁.snoc ⟨P, hP⟩ hstrict_top, ?_, by simp⟩
    simp [c₁, hlen₀]

private lemma exists_tower_to_flat {F : Type*} [Field F] {s m : ℕ} :
    ∀ k : ℕ, (hk : k ≤ m) →
      ∃ φ : TranscTower F s k →+* FractionRing (MvPolynomial (Fin s × Fin m) F),
        (∀ c : F, φ (transcBase F s k c) =
          algebraMap (MvPolynomial (Fin s × Fin m) F) _ (C c)) ∧
        (∀ (j : ℕ) (hjk : j < k) (i : Fin s),
          φ (transcVar F s hjk i) =
            algebraMap (MvPolynomial (Fin s × Fin m) F) _ (X (i, ⟨j, lt_of_lt_of_le hjk hk⟩))) ∧
        (∀ x : TranscTower F s k,
          ∃ a b : MvPolynomial (Fin s × Fin k) F, b ≠ 0 ∧
            φ x * algebraMap (MvPolynomial (Fin s × Fin m) F) _
              (rename (Prod.map id (Fin.castLE hk)) b) =
            algebraMap (MvPolynomial (Fin s × Fin m) F) _
              (rename (Prod.map id (Fin.castLE hk)) a)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    let A := MvPolynomial (Fin s × Fin m) F
    let Km := FractionRing A
    let φ₀ : TranscTower F s 0 →+* Km :=
      ((algebraMap A Km).comp C).comp (transcZeroEquiv F s).toRingHom
    refine ⟨φ₀, fun _ => rfl, fun _ hj => by omega, fun x => ?_⟩
    refine ⟨C (transcZeroEquiv F s x), 1, one_ne_zero, ?_⟩
    simp only [φ₀, RingHom.comp_apply, map_one, mul_one, rename_C]
    rfl
  | succ k ih =>
    intro hk
    let A := MvPolynomial (Fin s × Fin m) F
    let Km := FractionRing A
    obtain ⟨φk, hbase, hvar, hfrac⟩ := ih (Nat.le_of_succ_le hk)
    let evalNext : MvPolynomial (Fin s) (TranscTower F s k) →+* Km :=
      MvPolynomial.eval₂Hom φk fun i => algebraMap A Km (X (i, ⟨k, hk⟩))
    have hevalNext_inj : Function.Injective evalNext := by
      classical
      rw [injective_iff_map_eq_zero]
      intro p hp
      have hrep : ∀ ν : Fin s →₀ ℕ,
          ∃ a b : MvPolynomial (Fin s × Fin k) F, b ≠ 0 ∧
            φk (p.coeff ν) * algebraMap A Km
              (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) b) =
            algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) a) :=
        fun ν => hfrac (p.coeff ν)
      choose a b hb hab using hrep
      let d : MvPolynomial (Fin s × Fin k) F := ∏ ν ∈ p.support, b ν
      have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ν _ => hb ν
      let emb : (Fin s × Fin k) ⊕ Fin s → Fin s × Fin m :=
        Sum.elim (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (fun i => (i, ⟨k, hk⟩))
      have hemb_inj : Function.Injective emb := by
        rintro (⟨i₁, j₁⟩ | i₁) (⟨i₂, j₂⟩ | i₂) heq
        · simp only [emb, Sum.elim_inl, Prod.map_apply, id_eq, Prod.mk.injEq, Fin.ext_iff,
            Fin.val_castLE] at heq
          exact congrArg Sum.inl (Prod.ext (Fin.ext heq.1) (Fin.ext heq.2))
        · simp only [emb, Sum.elim_inl, Sum.elim_inr, Prod.map_apply, id_eq, Prod.mk.injEq,
            Fin.ext_iff, Fin.val_castLE] at heq
          exact absurd heq.2 (ne_of_lt j₁.isLt)
        · simp only [emb, Sum.elim_inl, Sum.elim_inr, Prod.map_apply, id_eq, Prod.mk.injEq,
            Fin.ext_iff, Fin.val_castLE] at heq
          exact absurd heq.2.symm (ne_of_lt j₂.isLt)
        · simp only [emb, Sum.elim_inr, Prod.mk.injEq] at heq
          exact congrArg Sum.inr heq.1
      let numPoly : (Fin s →₀ ℕ) → MvPolynomial (Fin s × Fin k) F :=
        fun ν => a ν * ∏ ν' ∈ p.support.erase ν, b ν'
      let Q : MvPolynomial ((Fin s × Fin k) ⊕ Fin s) F :=
        ∑ ν ∈ p.support, (rename Sum.inl (numPoly ν)) * monomial (ν.mapDomain Sum.inr) 1
      have hQ_eval :
          algebraMap A Km (rename emb Q) =
          evalNext p * algebraMap A Km
            (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) d) := by
        conv_rhs => rw [p.as_sum, map_sum, Finset.sum_mul]
        dsimp only [Q]
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun ν hν => ?_
        have hmon : evalNext (monomial ν (p.coeff ν)) =
            φk (p.coeff ν) * algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) := by
          rw [eval₂Hom_monomial, Finsupp.prod]
          have hprod :
              (∏ i ∈ ν.support, (algebraMap A Km (X (i, ⟨k, hk⟩))) ^ (ν i)) =
              algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) := by
            simp_rw [← map_pow]
            rw [← map_prod]
            congr 1
            rw [monomial_eq, map_one, one_mul, Finsupp.prod_mapDomain_index_inj]
            · rfl
            · intro i₁ i₂ heq
              exact (Prod.mk.inj heq).1
          rw [hprod]
        rw [hmon, map_mul, rename_rename, map_mul, rename_monomial]
        have hcomp_inl : emb ∘ Sum.inl = Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)) := rfl
        have hcomp_inr : emb ∘ Sum.inr = fun i => (i, ⟨k, hk⟩) := rfl
        rw [hcomp_inl, ← Finsupp.mapDomain_comp, hcomp_inr]
        have hd_split :
            rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) d =
            rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (b ν) *
              rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                (∏ ν' ∈ p.support.erase ν, b ν') := by
          simp only [d, ← map_mul, Finset.mul_prod_erase p.support b hν]
        rw [hd_split, map_mul]
        simp only [map_mul]
        calc
          algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (a ν)) *
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                (∏ ν' ∈ p.support.erase ν, b ν')) *
              algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1)
            = (φk (p.coeff ν) * algebraMap A Km
                (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (b ν))) *
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                (∏ ν' ∈ p.support.erase ν, b ν')) *
              algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) := by rw [hab ν]
          _ = φk (p.coeff ν) * algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) *
              (algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (b ν)) *
                algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                  (∏ ν' ∈ p.support.erase ν, b ν'))) := by ring
      rw [hp, zero_mul] at hQ_eval
      have hQ_zero : Q = 0 :=
        rename_injective emb hemb_inj (IsFractionRing.injective A Km (by simpa using hQ_eval))
      ext ν
      have h0ν : (0 : MvPolynomial (Fin s) (TranscTower F s k)).coeff ν = 0 := by simp
      rw [h0ν]
      by_cases hν : ν ∈ p.support
      · have hnum_zero : numPoly ν = 0 := by
          ext μ
          have h0μ : (0 : MvPolynomial (Fin s × Fin k) F).coeff μ = 0 := by simp
          rw [h0μ]
          let target : ((Fin s × Fin k) ⊕ Fin s) →₀ ℕ :=
            μ.mapDomain Sum.inl + ν.mapDomain Sum.inr
          have htarget := congrArg (fun u : MvPolynomial _ F => u.coeff target) hQ_zero
          have h0t : (0 : MvPolynomial ((Fin s × Fin k) ⊕ Fin s) F).coeff target = 0 := by simp
          rw [h0t, coeff_sum] at htarget
          have hterm : ∀ ν' ∈ p.support,
              ((rename Sum.inl (numPoly ν')) * monomial (ν'.mapDomain Sum.inr) 1).coeff target =
              if ν' = ν then (numPoly ν).coeff μ else 0 := by
            intro ν' _
            rw [mul_comm, coeff_monomial_mul']
            have hle_iff : ν'.mapDomain Sum.inr ≤ target ↔ ν' ≤ ν := by
              constructor
              · intro hle i
                have hi := hle (Sum.inr i)
                simp only [target, Finsupp.add_apply,
                  Finsupp.mapDomain_apply_of_injective Sum.inr_injective] at hi
                have hinl : μ.mapDomain Sum.inl (Sum.inr i) = 0 := by
                  rw [Finsupp.mapDomain_of_notMem_range]
                  rintro ⟨_, h⟩
                  cases h
                simpa [hinl] using hi
              · intro hle x
                rcases x with z | i
                · simp only [target, Finsupp.add_apply]
                  have : ν'.mapDomain Sum.inr (Sum.inl z) = 0 := by
                    rw [Finsupp.mapDomain_of_notMem_range]
                    rintro ⟨_, h⟩
                    cases h
                  rw [this]
                  exact Nat.zero_le _
                · simp only [target, Finsupp.add_apply,
                    Finsupp.mapDomain_apply_of_injective Sum.inr_injective]
                  exact le_add_of_le_right (hle i)
            by_cases hν'eq : ν' = ν
            · subst hν'eq
              have hle : ν'.mapDomain Sum.inr ≤ target := hle_iff.mpr le_rfl
              have hsub : target - ν'.mapDomain Sum.inr = μ.mapDomain Sum.inl := by
                ext x
                simp [target]
              simp only [hle, ↓reduceIte, one_mul, hsub, coeff_rename_mapDomain _ Sum.inl_injective]
            · simp only [hν'eq, ↓reduceIte]
              by_cases hle : ν'.mapDomain Sum.inr ≤ target
              · simp only [hle, ↓reduceIte, one_mul]
                have hnot_inl :
                    ∃ i, ((target - ν'.mapDomain Sum.inr : ((Fin s × Fin k) ⊕ Fin s) →₀ ℕ))
                      (Sum.inr i) ≠ 0 := by
                  have hlt : ∃ i, ν' i < ν i := by
                    have hle' := hle_iff.mp hle
                    by_contra hall
                    push Not at hall
                    exact hν'eq (Finsupp.ext fun i => le_antisymm (hle' i) (hall i))
                  obtain ⟨i, hi⟩ := hlt
                  refine ⟨i, ?_⟩
                  have hinl : μ.mapDomain Sum.inl (Sum.inr i) = 0 := by
                    rw [Finsupp.mapDomain_of_notMem_range]
                    rintro ⟨_, h⟩
                    cases h
                  simp only [Finsupp.tsub_apply, target, Finsupp.add_apply,
                    Finsupp.mapDomain_apply_of_injective Sum.inr_injective, hinl, zero_add]
                  omega
                obtain ⟨i, hi⟩ := hnot_inl
                by_contra hnz
                rw [coeff_rename_eq_zero] at hnz
                · exact hnz rfl
                · intro u hu
                  have hu_i := congrArg (fun f : _ →₀ ℕ => f (Sum.inr i)) hu
                  have hinl : u.mapDomain Sum.inl (Sum.inr i) = 0 := by
                    rw [Finsupp.mapDomain_of_notMem_range]
                    rintro ⟨_, h⟩
                    cases h
                  exact False.elim (hi (hu_i.symm.trans hinl))
              · simp [hle]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at htarget
          simpa [hν] using htarget
        have ha_zero : a ν = 0 := by
          have hprod_ne : ∏ ν' ∈ p.support.erase ν, b ν' ≠ 0 :=
            Finset.prod_ne_zero_iff.mpr fun ν' hν' => hb ν'
          exact (mul_eq_zero.mp hnum_zero).resolve_right hprod_ne
        have hφ_zero : φk (p.coeff ν) = 0 := by
          have h1 := hab ν
          rw [ha_zero, map_zero, map_zero] at h1
          have hb_ne : algebraMap A Km
              (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (b ν)) ≠ 0 := by
            intro h0
            have hren := IsFractionRing.injective A Km (by simpa using h0)
            have hinj : Function.Injective
                (Prod.map (id : Fin s → Fin s) (Fin.castLE (Nat.le_of_succ_le hk))) :=
              Function.Injective.prodMap Function.injective_id (Fin.castLE_injective _)
            exact hb ν (rename_injective _ hinj (by simpa using hren))
          exact (mul_eq_zero.mp h1).resolve_right hb_ne
        exact (injective_iff_map_eq_zero φk).mp φk.injective _ hφ_zero
      · exact MvPolynomial.notMem_support_iff.mp hν
    let φnext : TranscTower F s (k + 1) →+* Km :=
      IsFractionRing.lift (g := evalNext) hevalNext_inj
    have hφnext_alg : ∀ p : MvPolynomial (Fin s) (TranscTower F s k),
        φnext (algebraMap (MvPolynomial (Fin s) (TranscTower F s k)) _ p) = evalNext p :=
      IsFractionRing.lift_algebraMap hevalNext_inj
    refine ⟨φnext, ?_, ?_, ?_⟩
    · intro c
      change φnext (algebraMap (MvPolynomial (Fin s) (TranscTower F s k)) _
        (C (transcBase F s k c))) = _
      rw [hφnext_alg]
      simpa [evalNext] using hbase c
    · intro j hj i
      by_cases hjk : j < k
      · rw [← transcStep_transcVar hjk i]
        change φnext (algebraMap (MvPolynomial (Fin s) (TranscTower F s k)) _
          (C (transcVar F s hjk i))) = _
        rw [hφnext_alg]
        simpa [evalNext] using hvar j hjk i
      · have hjeq : j = k := by omega
        subst hjeq
        rw [transcVar_last, hφnext_alg]
        simp only [evalNext, eval₂Hom_X']
        rfl
    · intro x
      obtain ⟨⟨p, ⟨q, hq⟩⟩, hpq⟩ :=
        IsLocalization.mk'_surjective
          (nonZeroDivisors (MvPolynomial (Fin s) (TranscTower F s k))) x
      have hq_ne : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
      have hrep_p : ∀ ν : Fin s →₀ ℕ,
          ∃ a b : MvPolynomial (Fin s × Fin k) F, b ≠ 0 ∧
            φk (p.coeff ν) * algebraMap A Km
              (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) b) =
            algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) a) :=
        fun ν => hfrac (p.coeff ν)
      have hrep_q : ∀ ν : Fin s →₀ ℕ,
          ∃ a b : MvPolynomial (Fin s × Fin k) F, b ≠ 0 ∧
            φk (q.coeff ν) * algebraMap A Km
              (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) b) =
            algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) a) :=
        fun ν => hfrac (q.coeff ν)
      choose ap bp hbp habp using hrep_p
      choose aq bq hbq habq using hrep_q
      let Dk : MvPolynomial (Fin s × Fin k) F :=
        (∏ ν ∈ p.support, bp ν) * (∏ ν ∈ q.support, bq ν)
      have hDk_ne : Dk ≠ 0 :=
        mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ν _ => hbp ν)
          (Finset.prod_ne_zero_iff.mpr fun ν _ => hbq ν)
      let liftK : MvPolynomial (Fin s × Fin k) F →ₐ[F] MvPolynomial (Fin s × Fin (k + 1)) F :=
        rename (Prod.map id Fin.castSucc)
      let evalLift : (MvPolynomial (Fin s) (TranscTower F s k)) →
          (∀ ν, MvPolynomial (Fin s × Fin k) F) → (∀ ν, MvPolynomial (Fin s × Fin k) F) →
          MvPolynomial (Fin s × Fin k) F → MvPolynomial (Fin s × Fin (k + 1)) F :=
        fun r ar br extra =>
          ∑ ν ∈ r.support,
            liftK (ar ν * (∏ ν' ∈ r.support.erase ν, br ν') * extra) *
              monomial (ν.mapDomain fun i => (i, Fin.last k)) 1
      let A1 : MvPolynomial (Fin s × Fin (k + 1)) F :=
        evalLift p ap bp (∏ ν ∈ q.support, bq ν)
      let B1 : MvPolynomial (Fin s × Fin (k + 1)) F :=
        evalLift q aq bq (∏ ν ∈ p.support, bp ν)
      have hevalLift_eq :
          ∀ (r : MvPolynomial (Fin s) (TranscTower F s k))
            (ar br : (Fin s →₀ ℕ) → MvPolynomial (Fin s × Fin k) F)
            (extra : MvPolynomial (Fin s × Fin k) F),
            (∀ ν, φk (r.coeff ν) * algebraMap A Km
              (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (br ν)) =
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (ar ν))) →
            algebraMap A Km (rename (Prod.map id (Fin.castLE hk)) (evalLift r ar br extra)) =
            evalNext r * algebraMap A Km
              (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                ((∏ ν ∈ r.support, br ν) * extra)) := by
        intro r ar br extra hr
        conv_rhs =>
          arg 1
          rw [r.as_sum, map_sum]
        rw [Finset.sum_mul]
        dsimp only [evalLift]
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun ν hν => ?_
        have hmon : evalNext (monomial ν (r.coeff ν)) =
            φk (r.coeff ν) * algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) := by
          rw [eval₂Hom_monomial, Finsupp.prod]
          have hprod :
              (∏ i ∈ ν.support, (algebraMap A Km (X (i, ⟨k, hk⟩))) ^ (ν i)) =
              algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) := by
            simp_rw [← map_pow]
            rw [← map_prod]
            congr 1
            rw [monomial_eq, map_one, one_mul, Finsupp.prod_mapDomain_index_inj]
            · rfl
            · intro i₁ i₂ heq; exact (Prod.mk.inj heq).1
          rw [hprod]
        rw [hmon, map_mul, map_mul, rename_monomial, ← Finsupp.mapDomain_comp]
        have hcomp1 : (Prod.map (id : Fin s → Fin s) (Fin.castLE hk)) ∘
            (Prod.map id Fin.castSucc) =
            Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)) := by
          ext ⟨i, j⟩ <;> rfl
        have hcomp2 : (Prod.map (id : Fin s → Fin s) (Fin.castLE hk)) ∘
            (fun i => (i, Fin.last k)) = fun i => (i, ⟨k, hk⟩) := by
          funext i
          rfl
        have hren_lift : ∀ u : MvPolynomial (Fin s × Fin k) F,
            rename (Prod.map id (Fin.castLE hk)) (liftK u) =
            rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) u := fun u => by
          simp only [liftK, rename_rename, hcomp1]
        rw [hren_lift, hcomp2, map_mul, map_mul, map_mul, map_mul]
        have hprod_split :
            (∏ ν' ∈ r.support, br ν') = br ν * ∏ ν' ∈ r.support.erase ν, br ν' :=
          (Finset.mul_prod_erase r.support br hν).symm
        rw [hprod_split, map_mul, map_mul, map_mul, map_mul]
        calc
          algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (ar ν)) *
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                (∏ ν' ∈ r.support.erase ν, br ν')) *
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) extra) *
              algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1)
            = (φk (r.coeff ν) * algebraMap A Km
                (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (br ν))) *
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                (∏ ν' ∈ r.support.erase ν, br ν')) *
              algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) extra) *
              algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) := by rw [hr ν]
          _ = φk (r.coeff ν) * algebraMap A Km (monomial (ν.mapDomain fun i => (i, ⟨k, hk⟩)) 1) *
              (algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) (br ν)) *
                algebraMap A Km (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk)))
                  (∏ ν' ∈ r.support.erase ν, br ν')) *
                algebraMap A Km
                  (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) extra)) := by
            ring
      have hA1 : algebraMap A Km (rename (Prod.map id (Fin.castLE hk)) A1) =
          evalNext p * algebraMap A Km
            (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) Dk) :=
        hevalLift_eq p ap bp (∏ ν ∈ q.support, bq ν) habp
      have hB1 : algebraMap A Km (rename (Prod.map id (Fin.castLE hk)) B1) =
          evalNext q * algebraMap A Km
            (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) Dk) := by
        have h := hevalLift_eq q aq bq (∏ ν ∈ p.support, bp ν) habq
        have hDk_comm : (∏ ν ∈ q.support, bq ν) * (∏ ν ∈ p.support, bp ν) = Dk := mul_comm _ _
        rw [hDk_comm] at h
        exact h
      have hB1_ne : B1 ≠ 0 := by
        intro h0
        rw [h0, map_zero, map_zero] at hB1
        have hq0 : evalNext q ≠ 0 := fun hqeval =>
          hq_ne ((injective_iff_map_eq_zero evalNext).mp hevalNext_inj q hqeval)
        have hDk0 : algebraMap A Km
            (rename (Prod.map id (Fin.castLE (Nat.le_of_succ_le hk))) Dk) ≠ 0 := by
          intro hdk
          have hren := IsFractionRing.injective A Km (by simpa using hdk)
          have hinj : Function.Injective
              (Prod.map (id : Fin s → Fin s) (Fin.castLE (Nat.le_of_succ_le hk))) :=
            Function.Injective.prodMap Function.injective_id (Fin.castLE_injective _)
          exact hDk_ne (rename_injective _ hinj (by simpa using hren))
        exact mul_ne_zero hq0 hDk0 hB1.symm
      refine ⟨A1, B1, hB1_ne, ?_⟩
      dsimp only at hpq
      have hxpq : x * algebraMap (MvPolynomial (Fin s) (TranscTower F s k))
            (TranscTower F s (k + 1)) q =
          algebraMap (MvPolynomial (Fin s) (TranscTower F s k))
            (TranscTower F s (k + 1)) p := by
        rw [← hpq, mul_comm]
        exact IsLocalization.mk'_spec' (TranscTower F s (k + 1)) p ⟨q, hq⟩
      have hφx : φnext x * evalNext q = evalNext p := by
        have := congrArg φnext hxpq
        simpa [map_mul, hφnext_alg] using this
      rw [hB1, hA1, ← mul_assoc, hφx]

/-- Over any field extension `E / F`, `n + 1` linear combinations of `f₁, ..., fₛ ∈ F[x₁, ..., xₙ]`
whose coefficients `(α_{i, j}) ∈ E^{s(n+1)}` are algebraically independent over `F` define the exact
same affine zero locus in `E^n`. -/
theorem zeroLocus_linearCombination_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    {s n : ℕ} (f : Fin s → MvPolynomial (Fin n) F) (α : Fin s × Fin (n + 1) → E)
    (hα : AlgebraicIndependent F α) (x : Fin n → E) :
    (∀ j : Fin (n + 1),
      eval x (∑ i : Fin s, C (α (i, j)) * (f i).map (algebraMap F E)) = 0) ↔
    (∀ i : Fin s, aeval x (f i) = 0) := by
  constructor
  · intro hg
    by_contra hnot
    push Not at hnot
    obtain ⟨i₀, hi₀⟩ := hnot
    let A := MvPolynomial (Fin s × Fin (n + 1)) F
    let Kflat := FractionRing A
    have haeval_inj : Function.Injective (aeval α : A →ₐ[F] E).toRingHom :=
      algebraicIndependent_iff_injective_aeval.mp hα
    let flatToE : Kflat →+* E :=
      IsFractionRing.lift (g := (aeval α : A →ₐ[F] E).toRingHom) haeval_inj
    obtain ⟨φ, hφ_base, hφ_var, _⟩ := exists_tower_to_flat (F := F) (s := s) (m := n + 1)
      (n + 1) le_rfl
    let emb : TranscTower F s (n + 1) →+* E := flatToE.comp φ
    have hemb_base : ∀ c : F, emb (transcBase F s (n + 1) c) = algebraMap F E c := by
      intro c
      simp only [emb, RingHom.comp_apply, hφ_base, flatToE]
      rw [IsFractionRing.lift_algebraMap haeval_inj]
      exact aeval_C α c
    have hemb_var : ∀ (j : Fin (n + 1)) (i : Fin s),
        emb (transcVar F s j.isLt i) = α (i, j) := by
      intro j i
      simp only [emb, RingHom.comp_apply, hφ_var j.val j.isLt i, flatToE]
      rw [IsFractionRing.lift_algebraMap haeval_inj]
      exact aeval_X α (i, j)
    have hemb_comp : emb.comp (transcBase F s (n + 1)) = algebraMap F E :=
      RingHom.ext hemb_base
    let evalX : MvPolynomial (Fin n) (TranscTower F s (n + 1)) →+* E :=
      MvPolynomial.eval₂Hom emb x
    let P : Ideal (MvPolynomial (Fin n) (TranscTower F s (n + 1))) := RingHom.ker evalX
    have hP : P.IsPrime := RingHom.ker_isPrime evalX
    have hgen : ∀ (j : ℕ) (hjn : j < n + 1), towerGenPoly f hjn ∈ P := by
      intro j hjn
      rw [RingHom.mem_ker]
      have heval_f : ∀ i : Fin s,
          evalX ((f i).map (transcBase F s (n + 1))) = eval x ((f i).map (algebraMap F E)) := by
        intro i
        simp only [evalX, eval₂Hom_map_hom, eval_map, hemb_comp]
        rfl
      simp only [towerGenPoly, map_sum, map_mul, evalX, eval₂Hom_C]
      have hsum :
          (∑ i : Fin s, emb (transcVar F s hjn i) *
            eval₂Hom emb x ((f i).map (transcBase F s (n + 1)))) =
          eval x (∑ i : Fin s, C (α (i, ⟨j, hjn⟩)) * (f i).map (algebraMap F E)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, eval_C, hemb_var ⟨j, hjn⟩ i]
        exact congrArg (α (i, ⟨j, hjn⟩) * ·) (heval_f i)
      rw [hsum]
      exact hg ⟨j, hjn⟩
    have hmiss : ∃ i₀ : Fin s, (f i₀).map (transcBase F s (n + 1)) ∉ P := by
      refine ⟨i₀, fun hmem => hi₀ ?_⟩
      rw [RingHom.mem_ker] at hmem
      have : evalX ((f i₀).map (transcBase F s (n + 1))) = aeval x (f i₀) := by
        simp only [evalX, eval₂Hom_map_hom, aeval_def, hemb_comp]
        rfl
      exact this.symm.trans hmem
    obtain ⟨c, hlen, _⟩ := exists_prime_chain_of_tower f (n + 1) P hP hgen hmiss
    have hdim : ringKrullDim (MvPolynomial (Fin n) (TranscTower F s (n + 1))) = n := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hle : (c.length : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin n) (TranscTower F s (n + 1))) :=
      le_iSup (fun s : LTSeries (PrimeSpectrum _) => (s.length : WithBot ℕ∞)) c
    rw [hlen, hdim] at hle
    norm_cast at hle
    omega
  · intro hf j
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, eval_C, eval_map, ← aeval_def, hf i, mul_zero]

/-- For every `r : ℕ`, there exists an `r`-tuple of complex numbers algebraically independent
over `ℚ`. -/
theorem exists_algebraicIndependent_complex (r : ℕ) :
    ∃ α : Fin r → ℂ, AlgebraicIndependent ℚ α := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis (R := ℚ) (A := ℂ)
  have hinf : B.Infinite := by
    intro hfin
    let _ : Countable B := hfin.countable
    let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range ((↑) : B → ℂ))
    have hK_card : Cardinal.mk K ≤ Cardinal.aleph0 := by
      have h1 := IntermediateField.cardinalMk_adjoin_le (F := ℚ) (E := ℂ)
        (Set.range ((↑) : B → ℂ))
      have hQ : Cardinal.mk ℚ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      have hB_le : Cardinal.mk (Set.range ((↑) : B → ℂ)) ≤ Cardinal.aleph0 :=
        (Cardinal.mk_range_le).trans Cardinal.mk_le_aleph0
      exact h1.trans (max_le (max_le hQ hB_le) le_rfl)
    let _ : Countable K := Cardinal.mk_le_aleph0_iff.mp hK_card
    have halg : Algebra.IsAlgebraic K ℂ := hB.isAlgebraic_field
    have hpoly_count : Countable (Polynomial K) := by
      refine Function.Injective.countable (f := fun p : Polynomial K =>
        List.ofFn fun i : Fin (p.natDegree + 1) => p.coeff i.val) ?_
      intro p q h
      have hlen : p.natDegree = q.natDegree := by
        have := congrArg List.length h
        simpa using this
      apply AddMonoidAlgebra.ext
      apply Finsupp.ext
      intro i
      by_cases hi : i < p.natDegree + 1
      · have hget := congrArg (fun l : List K => l[i]?) h
        have hiq : i < q.natDegree + 1 := by omega
        simp only [List.getElem?_ofFn, hi, hiq, ↓reduceDIte, Option.some.injEq] at hget
        exact hget
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    let _ : Countable (Polynomial K) := hpoly_count
    have hC_count : Countable ℂ := by
      let _ : Countable {p : Polynomial K // p ≠ 0} := inferInstance
      let rootsOf : {p : Polynomial K // p ≠ 0} → Finset ℂ :=
        fun p => (p.1.map (algebraMap K ℂ)).roots.toFinset
      have hcover :
          (Set.univ : Set ℂ) ⊆ ⋃ p : {p : Polynomial K // p ≠ 0}, (rootsOf p : Set ℂ) := by
        intro z _
        obtain ⟨p, hp0, hpz⟩ := halg.isAlgebraic z
        refine Set.mem_iUnion.mpr ⟨⟨p, hp0⟩, ?_⟩
        simp only [rootsOf, Finset.mem_coe, Multiset.mem_toFinset]
        rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp0), Polynomial.IsRoot,
          Polynomial.eval_map, ← Polynomial.aeval_def]
        exact hpz
      have h_union_count : (⋃ p : {p : Polynomial K // p ≠ 0}, (rootsOf p : Set ℂ)).Countable :=
        Set.countable_iUnion fun p => (rootsOf p).countable_toSet
      exact Set.countable_univ_iff.mp (h_union_count.mono hcover)
    have hcardC : Cardinal.mk ℂ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
    rw [Cardinal.mk_complex] at hcardC
    exact not_le_of_gt Cardinal.aleph0_lt_continuum hcardC
  let f := hinf.natEmbedding
  refine ⟨fun i : Fin r => (f i.val).1, ?_⟩
  exact hB.1.comp (fun i : Fin r => f i.val) fun i j hij =>
    Fin.ext (f.injective hij)

end CslibFrontier.Foundations.AlgebraicGeometry
