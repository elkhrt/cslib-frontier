module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Schwartz–Zippel Lemma over Finite Commutative Rings

Structure theorem decomposing every finite commutative ring into finite local rings, univariate
and multivariate zero bounds over commutative rings with a non-zero-divisor subring, and the
Schwartz–Zippel lemma over finite local commutative rings of prime-power characteristic.

## Main definitions

* `CslibFrontier.Algebra.nilpotencyIndex`: least positive integer `m` with `(nilradical R) ^ m = ⊥`
  in a finite commutative ring `R`.
* `CslibFrontier.Algebra.finiteCommRingEquivPiLocal`: canonical algebra isomorphism
  `R ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal ^ nilpotencyIndex R`.
* `CslibFrontier.Algebra.annihilatorIdeal`: ideal `{r : R | (p : R) ^ k * r = 0}`.

## Main results

* `CslibFrontier.Algebra.finiteCommRing_struct_thm`: decomposition of finite commutative rings
  and their multivariate polynomial rings into products over finite local rings.
* `CslibFrontier.Algebra.finite_localRing_char_prime_pow`: every finite local commutative ring
  has prime-power characteristic `p ^ α` (`α > 0`).
* `CslibFrontier.Algebra.card_roots_le_natDegree_of_nonZeroDivisors`: root bound over any
  subring of non-zero-divisors (in particular any field or finite integral domain subring).
* `CslibFrontier.Algebra.weighted_schwartz_zippel_ring` and
  `CslibFrontier.Algebra.schwartz_zippel_ring_uniform`: weighted and uniform Schwartz–Zippel bounds
  over commutative rings with a non-zero-divisor subring.
* `CslibFrontier.Algebra.sz_finite_local_ring`: Schwartz–Zippel lemma over a finite local
  commutative ring of characteristic `p ^ α` under uniform integer sampling modulo `M`.
-/

public section

namespace CslibFrontier.Algebra

open Polynomial MvPolynomial

/-! ### Structure theorem for finite commutative rings -/

/-- The nilpotency index of the nilradical of a finite commutative ring $R$: a positive integer
$m \ge 1$ such that $(\mathrm{nilradical}\ R)^m = \bot$. -/
noncomputable def nilpotencyIndex (R : Type*) [CommRing R] [Finite R] : ℕ :=
  let h : ∃ m : ℕ, 0 < m ∧ (nilradical R) ^ m = ⊥ := by
    obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
    refine ⟨m + 1, Nat.succ_pos m, ?_⟩
    rw [pow_succ, hm, Ideal.zero_eq_bot, Ideal.bot_mul]
  Nat.find h

/-- `nilpotencyIndex R` is positive. -/
theorem nilpotencyIndex_pos (R : Type*) [CommRing R] [Finite R] :
    0 < nilpotencyIndex R :=
  (Nat.find_spec (p := fun m ↦ 0 < m ∧ (nilradical R) ^ m = ⊥) _).1

/-- `(nilradical R) ^ (nilpotencyIndex R) = ⊥`. -/
theorem nilradical_pow_nilpotencyIndex (R : Type*) [CommRing R] [Finite R] :
    (nilradical R) ^ (nilpotencyIndex R) = ⊥ :=
  (Nat.find_spec (p := fun m ↦ 0 < m ∧ (nilradical R) ^ m = ⊥) _).2

/-- For any maximal ideal $P$ of a commutative ring $R$ and $m \ge 1$, the quotient $R / P^m$
is a local ring. -/
theorem isLocalRing_quot_max_pow {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsMaximal]
    {m : ℕ} (hm : 0 < m) :
    IsLocalRing (R ⧸ P ^ m) := by
  have hne_top : P ^ m ≠ ⊤ := by
    intro htop
    have hle : P ^ m ≤ P := Ideal.pow_le_self (by omega)
    rw [htop] at hle
    exact hP.ne_top (top_le_iff.mp hle)
  have : Nontrivial (R ⧸ P ^ m) := Ideal.Quotient.nontrivial_iff.mpr hne_top
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨P.map (Ideal.Quotient.mk (P ^ m)), ?_, ?_⟩
  · have hle : P ^ m ≤ P := Ideal.pow_le_self (by omega)
    have hmax :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient (P.map (Ideal.Quotient.mk (P ^ m)))).mpr ?_
    · exact hmax
    · have e : ((R ⧸ P ^ m) ⧸ P.map (Ideal.Quotient.mk (P ^ m))) ≃+* (R ⧸ P) :=
        DoubleQuot.quotQuotEquivQuotOfLE hle
      exact e.toMulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp hP)
  · intro Q hQ
    have hQ_comap_max : (Q.comap (Ideal.Quotient.mk (P ^ m))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hpow_le : P ^ m ≤ Q.comap (Ideal.Quotient.mk (P ^ m)) := by
      intro x hx
      change Ideal.Quotient.mk (P ^ m) x ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Q.zero_mem
    have hP_le : P ≤ Q.comap (Ideal.Quotient.mk (P ^ m)) :=
      hQ_comap_max.isPrime.le_of_pow_le hpow_le
    have hP_eq : P = Q.comap (Ideal.Quotient.mk (P ^ m)) :=
      hP.eq_of_le hQ_comap_max.ne_top hP_le
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (P ^ m))
      Ideal.Quotient.mk_surjective Q, ← hP_eq]

/-- Canonical algebra isomorphism decomposing any finite commutative ring $R$ as a finite product
of the local rings $R / P^m$ over all maximal ideals $P$ of $R$. -/
noncomputable def finiteCommRingEquivPiLocal (R : Type*) [CommRing R] [Finite R] :
    R ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal ^ (nilpotencyIndex R) :=
  let eBot : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) :=
    AlgEquiv.ofBijective (Ideal.Quotient.mkₐ R ⊥)
      ⟨fun a b h ↦ by
        have hsub : a - b ∈ (⊥ : Ideal R) := Ideal.Quotient.eq.mp h
        exact sub_eq_zero.mp (Ideal.mem_bot.mp hsub),
      Ideal.Quotient.mk_surjective⟩
  eBot.trans
    ((Ideal.quotientEquivAlgOfEq R (nilradical_pow_nilpotencyIndex R).symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R (nilpotencyIndex R)))

/-- Evaluation of `finiteCommRingEquivPiLocal R` on each factor is the quotient projection. -/
@[simp]
theorem finiteCommRingEquivPiLocal_apply {R : Type*} [CommRing R] [Finite R]
    (r : R) (I : MaximalSpectrum R) :
    finiteCommRingEquivPiLocal R r I = Ideal.Quotient.mk (I.asIdeal ^ nilpotencyIndex R) r := by
  simp only [finiteCommRingEquivPiLocal, AlgEquiv.trans_apply,
    IsArtinianRing.quotNilradicalPowEquivPi]
  rfl

/-- Structure theorem for finite commutative rings: $R$ decomposes into a finite product of finite
local rings $R / P^m$, and this isomorphism extends naturally to multivariate polynomials. -/
theorem finiteCommRing_struct_thm (R : Type*) [CommRing R] [Finite R] (n : ℕ) :
    (∀ I : MaximalSpectrum R, IsLocalRing (R ⧸ I.asIdeal ^ nilpotencyIndex R)) ∧
    Nonempty (R ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal ^ nilpotencyIndex R) ∧
    Nonempty (MvPolynomial (Fin n) R ≃+*
      ∀ I : MaximalSpectrum R, MvPolynomial (Fin n) (R ⧸ I.asIdeal ^ nilpotencyIndex R)) := by
  refine ⟨fun I ↦ isLocalRing_quot_max_pow I.asIdeal (nilpotencyIndex_pos R),
    ⟨finiteCommRingEquivPiLocal R⟩, ?_⟩
  let φ := finiteCommRingEquivPiLocal R
  refine ⟨{
    toFun := fun p I ↦ MvPolynomial.map
      (Ideal.Quotient.mk (I.asIdeal ^ nilpotencyIndex R)) p
    invFun := fun ps ↦
      ∑ s ∈ Finset.biUnion (Set.toFinite (Set.univ : Set (MaximalSpectrum R))).toFinset
        (fun I ↦ (ps I).support),
        MvPolynomial.monomial s (φ.symm fun I ↦ (ps I).coeff s)
    left_inv := fun p ↦ by
      classical
      ext s
      rw [MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      by_cases hs : s ∈ (Set.toFinite (Set.univ : Set (MaximalSpectrum R))).toFinset.biUnion
          (fun I ↦ (MvPolynomial.map
            (Ideal.Quotient.mk (I.asIdeal ^ nilpotencyIndex R)) p).support)
      · rw [Finset.sum_ite_eq' _ s]
        simp only [hs, ↓reduceIte]
        have hcomp : (fun I : MaximalSpectrum R ↦
            (MvPolynomial.map (Ideal.Quotient.mk (I.asIdeal ^ nilpotencyIndex R)) p).coeff s) =
            φ (p.coeff s) := by
          ext I
          simp [φ, MvPolynomial.coeff_map]
        rw [hcomp, AlgEquiv.symm_apply_apply]
      · rw [Finset.sum_ite_eq' _ s]
        simp only [hs, ↓reduceIte]
        have hall0 : φ (p.coeff s) = 0 := by
          ext I
          have hnot : s ∉ (MvPolynomial.map
              (Ideal.Quotient.mk (I.asIdeal ^ nilpotencyIndex R)) p).support := by
            intro hmem
            exact hs (Finset.mem_biUnion.mpr ⟨I, by simp, hmem⟩)
          rw [MvPolynomial.mem_support_iff, not_not, MvPolynomial.coeff_map] at hnot
          simpa [φ] using hnot
        exact (φ.map_eq_zero_iff.mp hall0).symm
    right_inv := fun ps ↦ by
      classical
      ext I s
      dsimp only
      rw [map_sum, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.map_monomial, MvPolynomial.coeff_monomial]
      by_cases hs : s ∈ (Set.toFinite (Set.univ : Set (MaximalSpectrum R))).toFinset.biUnion
          (fun J ↦ (ps J).support)
      · rw [Finset.sum_ite_eq' _ s]
        simp only [hs, ↓reduceIte]
        have happ := congrFun (φ.apply_symm_apply (fun J ↦ (ps J).coeff s)) I
        simpa [φ] using happ
      · rw [Finset.sum_ite_eq' _ s]
        simp only [hs, ↓reduceIte]
        have hnot : s ∉ (ps I).support := fun hmem ↦
          hs (Finset.mem_biUnion.mpr ⟨I, by simp, hmem⟩)
        exact (not_not.mp (MvPolynomial.mem_support_iff.not.mp hnot)).symm
    map_mul' := fun p q ↦ by ext I; simp
    map_add' := fun p q ↦ by ext I; simp
  }⟩

/-- Every finite local commutative ring has prime-power characteristic $p^\alpha$ with $p$ prime
and $\alpha > 0$. -/
theorem finite_localRing_char_prime_pow (R : Type*) [CommRing R] [Finite R] [IsLocalRing R] :
    ∃ p α : ℕ, Nat.Prime p ∧ 0 < α ∧ ringChar R = p ^ α := by
  let M := IsLocalRing.maximalIdeal R
  let k := R ⧸ M
  have : Field k := Ideal.Quotient.field M
  have : Finite k := Quotient.finite _
  let p := ringChar k
  have hp_prime : Nat.Prime p := by
    have hcp : CharP k p := ringChar.charP k
    have hne0 : p ≠ 0 := by
      intro h0
      have : CharP k 0 := h0 ▸ hcp
      have : CharZero k := CharP.charP_to_charZero k
      have : Infinite k := Infinite.of_injective Nat.cast Nat.cast_injective
      exact not_finite k
    exact (CharP.char_is_prime_or_zero k p).resolve_right hne0
  have hp_mem_M : (p : R) ∈ M := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcast : Ideal.Quotient.mk M (p : R) = (p : k) := map_natCast _ p
    rw [hcast]
    exact ringChar.Nat.cast_ringChar
  have hM_eq_nil : M = nilradical R := by
    rw [IsArtinianRing.nilradical_eq_iInf]
    apply le_antisymm
    · rw [le_iInf_iff]
      intro I
      have : I.asIdeal.IsMaximal := I.isMaximal
      rw [IsLocalRing.eq_maximalIdeal I.isMaximal]
    · exact iInf_le (fun I : MaximalSpectrum R ↦ I.asIdeal)
        ⟨M, IsLocalRing.maximalIdeal.isMaximal R⟩
  have hp_nil : IsNilpotent (p : R) := by
    rw [hM_eq_nil] at hp_mem_M
    exact hp_mem_M
  obtain ⟨e, he⟩ := hp_nil
  have hpow0 : ((p ^ e : ℕ) : R) = 0 := by simpa using he
  have hdvd : ringChar R ∣ p ^ e := ringChar.dvd hpow0
  obtain ⟨α, _, hchar_eq⟩ := (Nat.dvd_prime_pow hp_prime).mp hdvd
  have hα_pos : 0 < α := by
    by_contra h0
    have hα0 : α = 0 := by omega
    rw [hα0, pow_zero] at hchar_eq
    have h1 : (1 : R) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := R)
      rw [hchar_eq, Nat.cast_one] at this
      exact this
    exact one_ne_zero h1
  exact ⟨p, α, hp_prime, hα_pos, hchar_eq⟩

/-! ### Univariate and multivariate zero bounds over non-zero-divisor subrings -/

/-- If $R$ is a commutative ring and $D \subseteq R$ is a subring whose nonzero elements are
non-zero-divisors in $R$ (which holds whenever $D$ is a field or a finite integral domain), then
every nonzero $f \in R[x]$ has at most $\deg(f)$ roots in $D$. -/
theorem card_roots_le_natDegree_of_nonZeroDivisors {R : Type*} [CommRing R] [DecidableEq R]
    (D : Subring R) (hD : ∀ a ∈ D, a ≠ 0 → a ∈ nonZeroDivisors R)
    {f : Polynomial R} (hf : f ≠ 0) (S : Finset R) (hS : ∀ a ∈ S, a ∈ D) :
    (S.filter fun a ↦ f.eval a = 0).card ≤ f.natDegree := by
  set T := S.filter fun a ↦ f.eval a = 0
  have hT_mem : ∀ a ∈ T, a ∈ D := fun a ha ↦ hS a (Finset.mem_filter.mp ha).1
  have hT_root : ∀ a ∈ T, f.eval a = 0 := fun a ha ↦ (Finset.mem_filter.mp ha).2
  have hdvd : (∏ a ∈ T, (Polynomial.X - Polynomial.C a)) ∣ f := by
    clear hS
    revert hT_mem hT_root
    induction T using Finset.induction_on with
    | empty => intro _ _; simp
    | @insert b T' hb ih =>
      intro hT_mem hT_root
      have hT'_mem : ∀ a ∈ T', a ∈ D := fun a ha ↦ hT_mem a (Finset.mem_insert_of_mem ha)
      have hT'_root : ∀ a ∈ T', f.eval a = 0 := fun a ha ↦ hT_root a (Finset.mem_insert_of_mem ha)
      obtain ⟨g, hg⟩ := ih hT'_mem hT'_root
      have hfb : f.eval b = 0 := hT_root b (Finset.mem_insert_self b T')
      rw [hg, Polynomial.eval_mul, Polynomial.eval_prod] at hfb
      have hprod_nzd : (∏ a ∈ T', (Polynomial.X - Polynomial.C a).eval b) ∈ nonZeroDivisors R := by
        apply Submonoid.prod_mem (nonZeroDivisors R)
        intro a ha
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        refine hD (b - a) (D.sub_mem (hT_mem b (Finset.mem_insert_self b T')) (hT'_mem a ha)) ?_
        exact sub_ne_zero.mpr (fun heq ↦ hb (heq ▸ ha))
      have hgb : g.eval b = 0 := by
        rw [mul_comm] at hfb
        exact (mem_nonZeroDivisors_iff.mp hprod_nzd).2 (g.eval b) hfb
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hgb
      rw [Finset.prod_insert hb]
      refine ⟨q, ?_⟩
      rw [hg, hq]
      ring
  have hmonic : (∏ a ∈ T, (Polynomial.X - Polynomial.C a)).Monic :=
    Polynomial.monic_prod_of_monic T _ fun a _ ↦ Polynomial.monic_X_sub_C a
  have hdeg_prod : (∏ a ∈ T, (Polynomial.X - Polynomial.C a)).natDegree = T.card := by
    have : Nontrivial R := ⟨⟨f.leadingCoeff, 0, Polynomial.leadingCoeff_ne_zero.mpr hf⟩⟩
    rw [Polynomial.natDegree_prod_of_monic T _ fun a _ ↦ Polynomial.monic_X_sub_C a]
    simp
  obtain ⟨q, hq⟩ := hdvd
  have hq_ne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hq
    exact hf hq
  rw [← hdeg_prod, hq, hmonic.natDegree_mul' hq_ne]
  exact Nat.le_add_right _ _

/-- Every subring `D` that is a field satisfies the non-zero-divisor hypothesis in `R`. -/
theorem nonZeroDivisors_of_field_subring {R : Type*} [CommRing R] (D : Subring R)
    (hD : IsField D) :
    ∀ a ∈ D, a ≠ 0 → a ∈ nonZeroDivisors R := by
  intro a ha hane
  have hneD : (⟨a, ha⟩ : D) ≠ 0 := fun h ↦ hane (congrArg Subtype.val h)
  obtain ⟨b, hb⟩ := hD.mul_inv_cancel hneD
  have hab : a * b.val = 1 := congrArg Subtype.val hb
  exact IsUnit.mem_nonZeroDivisors (IsUnit.of_mul_eq_one b.val hab)

/-- Every finite integral domain subring `D` is a field, hence satisfies the non-zero-divisor
hypothesis in `R`. -/
theorem nonZeroDivisors_of_finite_domain_subring {R : Type*} [CommRing R] (D : Subring R)
    [Finite D] [IsDomain D] :
    ∀ a ∈ D, a ≠ 0 → a ∈ nonZeroDivisors R := by
  intro a ha hane
  have hneD : (⟨a, ha⟩ : D) ≠ 0 := fun h ↦ hane (congrArg Subtype.val h)
  have hsurj : Function.Surjective (fun x : D ↦ (⟨a, ha⟩ : D) * x) :=
    Finite.injective_iff_surjective.mp (mul_right_injective₀ hneD)
  obtain ⟨b, hb⟩ := hsurj 1
  have hab : a * b.val = 1 := congrArg Subtype.val hb
  exact IsUnit.mem_nonZeroDivisors (IsUnit.of_mul_eq_one b.val hab)

/-- Univariate root bound over a field subring `D` of a commutative ring `R`. -/
theorem card_roots_le_natDegree_of_field_subring {R : Type*} [CommRing R] [DecidableEq R]
    (D : Subring R) (hD : IsField D)
    {f : Polynomial R} (hf : f ≠ 0) (S : Finset R) (hS : ∀ a ∈ S, a ∈ D) :
    (S.filter fun a ↦ f.eval a = 0).card ≤ f.natDegree :=
  card_roots_le_natDegree_of_nonZeroDivisors D (nonZeroDivisors_of_field_subring D hD) hf S hS

/-- Weighted Schwartz–Zippel lemma over a commutative ring $R$ containing a non-zero-divisor
subring $D$: for any product distribution $\mu^{\otimes n}$ on $A^n$ ($A \subseteq D$) with
$\max_{a \in A} \mu(a) \le \delta$ and any nonzero $g \in R[x_1,\dots,x_n]$ of individual degree
at most $d$, $\Pr_{x \sim \mu^{\otimes n}}[g(x) = 0] \le n d \delta$. -/
theorem weighted_schwartz_zippel_ring {R : Type*} [CommRing R] [DecidableEq R]
    (D : Subring R) (hD : ∀ a ∈ D, a ≠ 0 → a ∈ nonZeroDivisors R)
    (A : Finset R) (hA : ∀ a ∈ A, a ∈ D)
    (μ : R → ℝ) (hμ_nonneg : ∀ a ∈ A, 0 ≤ μ a) (hμ_sum : ∑ a ∈ A, μ a = 1)
    {δ : ℝ} (hμ_le : ∀ a ∈ A, μ a ≤ δ) :
    ∀ {n d : ℕ} {g : MvPolynomial (Fin n) R},
      g ≠ 0 → (∀ i : Fin n, g.degreeOf i ≤ d) →
      ∑ x ∈ (Fintype.piFinset fun _ : Fin n ↦ A).filter (fun x ↦ MvPolynomial.eval x g = 0),
        ∏ i : Fin n, μ (x i) ≤ (n * d : ℝ) * δ := by
  intro n
  induction n with
  | zero =>
    intro d g hg _
    have hne : ∀ x : Fin 0 → R, MvPolynomial.eval x g ≠ 0 := by
      intro x hev
      apply hg
      have hgC : g = MvPolynomial.C (g.coeff 0) := by
        ext s
        rw [Subsingleton.elim s 0]
        simp [MvPolynomial.coeff_C]
      rw [hgC, MvPolynomial.eval_C] at hev
      rw [hgC, hev, map_zero]
    have hempty : (Fintype.piFinset fun _ : Fin 0 ↦ A).filter
        (fun x ↦ MvPolynomial.eval x g = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _; exact hne x
    rw [hempty, Finset.sum_empty]
    simp
  | succ n ih =>
    intro d g hg hdeg
    let P : Polynomial (MvPolynomial (Fin n) R) := MvPolynomial.finSuccEquiv R n g
    have hP_ne : P ≠ 0 := by
      intro h0
      exact hg ((MvPolynomial.finSuccEquiv R n).map_eq_zero_iff.mp h0)
    have hlc_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
    have hP_deg : P.natDegree ≤ d := by
      have h0 := MvPolynomial.natDegree_finSuccEquiv g
      rw [h0]
      exact hdeg 0
    have hlc_deg : ∀ j : Fin n, P.leadingCoeff.degreeOf j ≤ d := by
      intro j
      have hle := MvPolynomial.degreeOf_coeff_finSuccEquiv g j P.natDegree
      exact hle.trans (hdeg j.succ)
    have heval_cons : ∀ (a : R) (y : Fin n → R),
        MvPolynomial.eval (Fin.cons a y) g = (P.map (MvPolynomial.eval y)).eval a := by
      intro a y
      rw [← MvPolynomial.eval_eq_eval_mv_eval']
    let B_n : Finset (Fin n → R) := Fintype.piFinset fun _ : Fin n ↦ A
    let B_succ : Finset (Fin (n + 1) → R) := Fintype.piFinset fun _ : Fin (n + 1) ↦ A
    have hprod_nonneg : ∀ y ∈ B_n, 0 ≤ ∏ i : Fin n, μ (y i) := fun y hy ↦
      Finset.prod_nonneg fun i _ ↦ hμ_nonneg _ ((Fintype.mem_piFinset.mp hy) i)
    have hprod_sum' : ∑ y ∈ B_n, ∏ i : Fin n, μ (y i) = 1 := by
      calc
        ∑ y ∈ B_n, ∏ i : Fin n, μ (y i)
          = ∏ _i : Fin n, ∑ a ∈ A, μ a := (Finset.prod_univ_sum (fun _ ↦ A) (fun _ a ↦ μ a)).symm
        _ = 1 := by simp [hμ_sum]
    have hsum_split :
        ∑ x ∈ B_succ.filter (fun x ↦ MvPolynomial.eval x g = 0), ∏ i : Fin (n + 1), μ (x i) =
          ∑ y ∈ B_n, (∏ i : Fin n, μ (y i)) *
            ∑ a ∈ A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0), μ a := by
      let f_bij : (Fin (n + 1) → R) → (Fin n → R) × R := fun x ↦ (Fin.tail x, x 0)
      have hbij :
          ∑ x ∈ B_succ.filter (fun x ↦ MvPolynomial.eval x g = 0), ∏ i : Fin (n + 1), μ (x i) =
            ∑ p ∈ (B_n ×ˢ A).filter (fun p ↦ (P.map (MvPolynomial.eval p.1)).eval p.2 = 0),
              (∏ i : Fin n, μ (p.1 i)) * μ p.2 := by
        refine Finset.sum_bij (fun x _ ↦ f_bij x) ?_ ?_ ?_ ?_
        · intro x hx
          rw [Finset.mem_filter] at hx ⊢
          refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · exact Fintype.mem_piFinset.mpr fun i ↦ (Fintype.mem_piFinset.mp hx.1) i.succ
          · exact (Fintype.mem_piFinset.mp hx.1) 0
          · dsimp [f_bij]
            rw [← heval_cons, Fin.cons_self_tail]
            exact hx.2
        · intro x₁ _ x₂ _ h
          have ht : Fin.tail x₁ = Fin.tail x₂ := congrArg Prod.fst h
          have h0 : x₁ 0 = x₂ 0 := congrArg Prod.snd h
          ext i
          refine Fin.cases h0 (fun j ↦ congrFun ht j) i
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_product] at hp
          refine ⟨Fin.cons p.2 p.1, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
          · refine Fintype.mem_piFinset.mpr fun i ↦ Fin.cases hp.1.2
              (fun j ↦ (Fintype.mem_piFinset.mp hp.1.1) j) i
          · rw [heval_cons]; exact hp.2
          · ext <;> simp [f_bij]
        · intro x _
          rw [Fin.prod_univ_succ, mul_comm]
          rfl
      rw [hbij, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_filter, Finset.mul_sum]
      simp [mul_ite]
    rw [hsum_split]
    rw [← Finset.sum_filter_add_sum_filter_not B_n (fun y ↦ MvPolynomial.eval y P.leadingCoeff = 0)]
    have hpart1 :
        ∑ y ∈ B_n.filter (fun y ↦ MvPolynomial.eval y P.leadingCoeff = 0),
          (∏ i : Fin n, μ (y i)) *
            ∑ a ∈ A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0), μ a ≤
          (n * d : ℝ) * δ := by
      calc
        _ ≤ ∑ y ∈ B_n.filter (fun y ↦ MvPolynomial.eval y P.leadingCoeff = 0),
              (∏ i : Fin n, μ (y i)) * 1 := by
            refine Finset.sum_le_sum fun y hy ↦ ?_
            have hyB : y ∈ B_n := (Finset.mem_filter.mp hy).1
            refine mul_le_mul_of_nonneg_left ?_ (hprod_nonneg y hyB)
            calc
              ∑ a ∈ A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0), μ a
                ≤ ∑ a ∈ A, μ a := Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.filter_subset _ A) fun a ha _ ↦ hμ_nonneg a ha
              _ = 1 := hμ_sum
        _ = ∑ y ∈ B_n.filter (fun y ↦ MvPolynomial.eval y P.leadingCoeff = 0),
              ∏ i : Fin n, μ (y i) := by simp
        _ ≤ (n * d : ℝ) * δ := ih hlc_ne hlc_deg
    have hpart2 :
        ∑ y ∈ B_n.filter (fun y ↦ ¬ MvPolynomial.eval y P.leadingCoeff = 0),
          (∏ i : Fin n, μ (y i)) *
            ∑ a ∈ A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0), μ a ≤
          (d : ℝ) * δ := by
      have hδ_nonneg : 0 ≤ δ := by
        by_cases hA_empty : A = ∅
        · rw [hA_empty, Finset.sum_empty] at hμ_sum; norm_num at hμ_sum
        · obtain ⟨a₀, ha₀⟩ := Finset.nonempty_iff_ne_empty.mpr hA_empty
          exact (hμ_nonneg a₀ ha₀).trans (hμ_le a₀ ha₀)
      calc
        _ ≤ ∑ y ∈ B_n.filter (fun y ↦ ¬ MvPolynomial.eval y P.leadingCoeff = 0),
              (∏ i : Fin n, μ (y i)) * ((d : ℝ) * δ) := by
            refine Finset.sum_le_sum fun y hy ↦ ?_
            obtain ⟨hyB, hlc_y_ne⟩ := Finset.mem_filter.mp hy
            refine mul_le_mul_of_nonneg_left ?_ (hprod_nonneg y hyB)
            have hPy_ne : P.map (MvPolynomial.eval y) ≠ 0 := by
              intro h0
              have hc := congrArg (fun q : Polynomial R ↦ q.coeff P.natDegree) h0
              rw [Polynomial.coeff_map, Polynomial.coeff_natDegree, Polynomial.coeff_zero] at hc
              exact hlc_y_ne hc
            have hPy_deg : (P.map (MvPolynomial.eval y)).natDegree ≤ d :=
              Polynomial.natDegree_map_le.trans hP_deg
            have hcard_le :
                (A.filter fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0).card ≤ d :=
              (card_roots_le_natDegree_of_nonZeroDivisors D hD hPy_ne A hA).trans hPy_deg
            calc
              ∑ a ∈ A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0), μ a
                ≤ ∑ _a ∈ A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0), δ :=
                  Finset.sum_le_sum fun a ha ↦ hμ_le a (Finset.mem_filter.mp ha).1
              _ = ((A.filter (fun a ↦ (P.map (MvPolynomial.eval y)).eval a = 0)).card : ℝ) * δ := by
                  simp
              _ ≤ (d : ℝ) * δ :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) hδ_nonneg
        _ = (∑ y ∈ B_n.filter (fun y ↦ ¬ MvPolynomial.eval y P.leadingCoeff = 0),
              ∏ i : Fin n, μ (y i)) * ((d : ℝ) * δ) := by
            rw [← Finset.sum_mul]
        _ ≤ (∑ y ∈ B_n, ∏ i : Fin n, μ (y i)) * ((d : ℝ) * δ) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg d) hδ_nonneg)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ B_n)
              fun y hy _ ↦ hprod_nonneg y hy
        _ = (d : ℝ) * δ := by rw [hprod_sum', one_mul]
    calc
      _ ≤ (n * d : ℝ) * δ + (d : ℝ) * δ := add_le_add hpart1 hpart2
      _ = (((n + 1 : ℕ) : ℝ) * d) * δ := by push_cast; ring

/-- Uniform Schwartz–Zippel bound over a commutative ring $R$ containing a non-zero-divisor
subring $D$. -/
theorem schwartz_zippel_ring_uniform {R : Type*} [CommRing R] [DecidableEq R]
    (D : Subring R) (hD : ∀ a ∈ D, a ≠ 0 → a ∈ nonZeroDivisors R)
    (A : Finset R) (hAne : A.Nonempty) (hA : ∀ a ∈ A, a ∈ D)
    {n d : ℕ} {g : MvPolynomial (Fin n) R}
    (hg : g ≠ 0) (hdeg : ∀ i : Fin n, g.degreeOf i ≤ d) :
    (((Fintype.piFinset fun _ : Fin n ↦ A).filter
      (fun x ↦ MvPolynomial.eval x g = 0)).card : ℝ) / (A.card : ℝ) ^ n ≤
      (n * d : ℝ) / A.card := by
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hμ_sum : ∑ _a ∈ A, (1 / (A.card : ℝ)) = 1 := by
    simp [hApos.ne']
  have h := weighted_schwartz_zippel_ring D hD A hA (fun _ ↦ 1 / (A.card : ℝ))
    (fun _ _ ↦ by positivity) hμ_sum (δ := 1 / (A.card : ℝ)) (fun _ _ ↦ le_rfl) hg hdeg
  have hlhs :
      ∑ _x ∈ (Fintype.piFinset fun _ : Fin n ↦ A).filter (fun x ↦ MvPolynomial.eval x g = 0),
        ∏ _i : Fin n, (1 / (A.card : ℝ)) =
      (((Fintype.piFinset fun _ : Fin n ↦ A).filter
        (fun x ↦ MvPolynomial.eval x g = 0)).card : ℝ) / (A.card : ℝ) ^ n := by
    simp [div_eq_mul_inv]
  rw [hlhs] at h
  simpa [div_eq_mul_inv] using h

/-! ### Schwartz–Zippel lemma over finite local commutative rings -/

/-- Almost-uniform distribution of `c % p` when `c` is sampled uniformly from `Fin M`. -/
theorem card_mod_eq_bounds {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (b : Fin p) :
    let cnt := (Finset.univ.filter fun c : Fin M ↦ c.val % p = b.val).card
    (1 - (p : ℝ) / M) / p ≤ (cnt : ℝ) / M ∧ (cnt : ℝ) / M ≤ (1 + (p : ℝ) / M) / p := by
  intro cnt
  have hcnt_range : M / p ≤ cnt ∧ cnt ≤ M / p + 1 := by
    let f : ℕ → ℕ := fun q ↦ q * p + b.val
    have hf_inj : Function.Injective f := fun q₁ q₂ h ↦ by
      dsimp [f] at h
      have : q₁ * p = q₂ * p := by omega
      exact Nat.eq_of_mul_eq_mul_right hp this
    have hlow : M / p ≤ cnt := by
      rw [← Finset.card_range (M / p)]
      let gFin : ℕ → Fin M := fun q ↦
        if h : q * p + b.val < M then ⟨q * p + b.val, h⟩ else ⟨0, hM⟩
      have hlt_q : ∀ q ∈ Finset.range (M / p), q * p + b.val < M := by
        intro q hq
        rw [Finset.mem_range] at hq
        have hq1 : (q + 1) * p ≤ M :=
          (Nat.mul_le_mul_right p hq).trans (Nat.div_mul_le_self M p)
        have := b.isLt
        nlinarith
      refine Finset.card_le_card_of_injOn gFin ?_ ?_
      · intro q hq
        rw [Finset.mem_coe] at hq
        have hlt := hlt_q q hq
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [gFin, hlt, ↓reduceDIte]
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt b.isLt]
      · intro q₁ hq₁ q₂ hq₂ heq
        rw [Finset.mem_coe] at hq₁ hq₂
        have h1 := hlt_q q₁ hq₁
        have h2 := hlt_q q₂ hq₂
        have hv := congrArg Fin.val heq
        simp only [gFin, h1, h2, ↓reduceDIte] at hv
        exact hf_inj hv
    have hhigh : cnt ≤ M / p + 1 := by
      have hcard_img : ((Finset.range (M / p + 1)).image f).card = M / p + 1 := by
        rw [Finset.card_image_of_injective _ hf_inj, Finset.card_range]
      rw [← hcard_img]
      refine Finset.card_le_card_of_injOn (fun c : Fin M ↦ c.val) ?_ ?_
      · intro c hc
        rw [Finset.mem_coe, Finset.mem_filter] at hc
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨c.val / p, Finset.mem_range.mpr ?_, ?_⟩
        · have : c.val / p ≤ M / p := Nat.div_le_div_right c.isLt.le
          omega
        · dsimp [f]
          have hdiv := Nat.div_add_mod c.val p
          rw [hc.2] at hdiv
          linarith [Nat.mul_comm p (c.val / p)]
      · intro c₁ _ c₂ _ h
        exact Fin.ext h
    exact ⟨hlow, hhigh⟩
  have hdiv_mul : (M / p) * p ≤ M ∧ M < (M / p + 1) * p := by
    refine ⟨Nat.div_mul_le_self M p, ?_⟩
    have := Nat.div_add_mod M p
    have := Nat.mod_lt M hp
    nlinarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcnt1 : ((M / p : ℕ) : ℝ) ≤ (cnt : ℝ) := by exact_mod_cast hcnt_range.1
  have hcnt2 : (cnt : ℝ) ≤ ((M / p : ℕ) : ℝ) + 1 := by exact_mod_cast hcnt_range.2
  have hdm1 : ((M / p : ℕ) : ℝ) * p ≤ M := by exact_mod_cast hdiv_mul.1
  have hdm2 : (M : ℝ) < (((M / p : ℕ) : ℝ) + 1) * p := by exact_mod_cast hdiv_mul.2
  have hmul_sub : (1 - (p : ℝ) / M) * M = M - p := by field_simp
  have hmul_add : (1 + (p : ℝ) / M) * M = M + p := by field_simp
  constructor
  · rw [div_le_div_iff₀ hpR hMR, hmul_sub]
    nlinarith
  · rw [div_le_div_iff₀ hMR hpR, hmul_add]
    nlinarith

/-- The annihilator ideal $\{r \in R \mid p^k r = 0\}$. -/
def annihilatorIdeal (R : Type*) [CommRing R] (p k : ℕ) : Ideal R where
  carrier := {r : R | ((p : R) ^ k) * r = 0}
  add_mem' {a b} ha hb := by
    change (p : R) ^ k * (a + b) = 0
    rw [mul_add, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    change (p : R) ^ k * (c * x) = 0
    rw [mul_left_comm, hx, mul_zero]

/-- Membership characterization for `annihilatorIdeal R p k`. -/
theorem mem_annihilatorIdeal_iff {R : Type*} [CommRing R] {p k : ℕ} {x : R} :
    x ∈ annihilatorIdeal R p k ↔ (p : R) ^ k * x = 0 :=
  Iff.rfl

/-- Existence of the maximal power $p^k$ dividing a nonzero multivariate polynomial over a ring of
characteristic $p^\alpha$, with the quotient polynomial supported inside `g.support`. -/
theorem exists_max_prime_pow_factor_mvPoly {R : Type*} [CommRing R] {n p α : ℕ}
    (hchar : ringChar R = p ^ α)
    {g : MvPolynomial (Fin n) R} (hg : g ≠ 0) :
    ∃ (k : ℕ) (g_hat : MvPolynomial (Fin n) R),
      k < α ∧
      g = MvPolynomial.C ((p : R) ^ k) * g_hat ∧
      g_hat.support ⊆ g.support ∧
      (∀ h : MvPolynomial (Fin n) R, g ≠ MvPolynomial.C ((p : R) ^ (k + 1)) * h) := by
  classical
  have hpowα : (p : R) ^ α = 0 := by
    have h1 : ((p ^ α : ℕ) : R) = 0 := by
      rw [← hchar]
      exact ringChar.Nat.cast_ringChar
    simpa using h1
  have hex_not : ∃ j : ℕ, ∀ h : MvPolynomial (Fin n) R, g ≠ MvPolynomial.C ((p : R) ^ j) * h := by
    refine ⟨α, fun h heq ↦ hg ?_⟩
    rw [heq, hpowα, map_zero, zero_mul]
  let j₀ := Nat.find hex_not
  have hj₀_spec : ∀ h : MvPolynomial (Fin n) R, g ≠ MvPolynomial.C ((p : R) ^ j₀) * h :=
    Nat.find_spec hex_not
  have hj₀_pos : 0 < j₀ := by
    by_contra h0
    have hj0 : j₀ = 0 := by omega
    rw [hj0] at hj₀_spec
    exact hj₀_spec g (by simp)
  have hj₀_le : j₀ ≤ α := Nat.find_min' hex_not fun h heq ↦
    hg (by rw [heq, hpowα, map_zero, zero_mul])
  let k := j₀ - 1
  have hk_lt : k < j₀ := by omega
  have hmin := Nat.find_min hex_not hk_lt
  push Not at hmin
  obtain ⟨g_hat0, hg_eq0⟩ := hmin
  let g_hat : MvPolynomial (Fin n) R :=
    ∑ s ∈ g.support, MvPolynomial.monomial s (g_hat0.coeff s)
  have hcoeff_ghat : ∀ s : Fin n →₀ ℕ,
      g_hat.coeff s = if s ∈ g.support then g_hat0.coeff s else 0 := by
    intro s
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hsupp_sub : g_hat.support ⊆ g.support := by
    intro s hs
    by_contra hnot
    rw [MvPolynomial.mem_support_iff, hcoeff_ghat] at hs
    simp only [hnot, ↓reduceIte] at hs
    exact hs rfl
  have hg_eq : g = MvPolynomial.C ((p : R) ^ k) * g_hat := by
    ext s
    rw [MvPolynomial.coeff_C_mul, hcoeff_ghat]
    by_cases hs : s ∈ g.support
    · simp only [hs, ↓reduceIte]
      have h0 := congrArg (fun q : MvPolynomial (Fin n) R ↦ q.coeff s) hg_eq0
      rw [MvPolynomial.coeff_C_mul] at h0
      exact h0
    · simp only [hs, ↓reduceIte, mul_zero]
      exact not_not.mp (MvPolynomial.mem_support_iff.not.mp hs)
  refine ⟨k, g_hat, by omega, hg_eq, hsupp_sub, ?_⟩
  have hk1 : k + 1 = j₀ := by omega
  rw [hk1]
  exact hj₀_spec

/-- Quotient reduction: if $g = p^k \hat{g} \notin p^{k+1} R[x_1,\dots,x_n]$, then in
$S = R / (\mathrm{ann}(p^k) + p R)$, the image of $\hat{g}$ is nonzero, $S$ is nontrivial, and
$S$ has characteristic $p$. -/
theorem quotient_reduction_nonzero_and_field {R : Type*} [CommRing R] {n p k : ℕ}
    (hp : Nat.Prime p) {g g_hat : MvPolynomial (Fin n) R}
    (hg_eq : g = MvPolynomial.C ((p : R) ^ k) * g_hat)
    (hg_not : ∀ h : MvPolynomial (Fin n) R, g ≠ MvPolynomial.C ((p : R) ^ (k + 1)) * h) :
    let J := annihilatorIdeal R p k ⊔ Ideal.span {(p : R)}
    let S := R ⧸ J
    let π : R →+* S := Ideal.Quotient.mk J
    MvPolynomial.map π g_hat ≠ 0 ∧ Nontrivial S ∧ CharP S p := by
  intro J S π
  have hghat_ne : MvPolynomial.map π g_hat ≠ 0 := by
    intro h0
    have hcoeff_J : ∀ s : Fin n →₀ ℕ, g_hat.coeff s ∈ J := by
      intro s
      have hc := congrArg (fun q : MvPolynomial (Fin n) S ↦ q.coeff s) h0
      rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at hc
      exact Ideal.Quotient.eq_zero_iff_mem.mp hc
    have hsplit : ∀ s : Fin n →₀ ℕ, ∃ u r : R,
        (p : R) ^ k * u = 0 ∧ g_hat.coeff s = u + (p : R) * r := by
      intro s
      have hmem := Submodule.mem_sup.mp (hcoeff_J s)
      obtain ⟨u, hu, v, hv, huv⟩ := hmem
      rw [Ideal.mem_span_singleton] at hv
      obtain ⟨r, rfl⟩ := hv
      exact ⟨u, r, hu, huv.symm⟩
    choose u r hu hr using hsplit
    let g₂ : MvPolynomial (Fin n) R :=
      ∑ s ∈ g_hat.support, MvPolynomial.monomial s (r s)
    apply hg_not g₂
    rw [hg_eq]
    ext s
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hs : s ∈ g_hat.support
    · rw [Finset.sum_ite_eq' _ s]
      simp only [hs, ↓reduceIte]
      rw [hr s, mul_add, hu s, zero_add, pow_succ, mul_assoc]
    · have h0s : g_hat.coeff s = 0 := not_not.mp (MvPolynomial.mem_support_iff.not.mp hs)
      rw [Finset.sum_ite_eq' _ s]
      simp only [hs, ↓reduceIte, h0s, mul_zero]
  have hS_nontriv : Nontrivial S := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    exact hghat_ne (Subsingleton.elim _ _)
  have hchar_p : CharP S p := by
    have hpS : (p : S) = 0 := by
      change Ideal.Quotient.mk J (p : R) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
    have hdvd : ringChar S ∣ p := ringChar.dvd hpS
    have hne1 : ringChar S ≠ 1 := by
      intro h1
      have h10 : (1 : S) = 0 := by
        have := ringChar.Nat.cast_ringChar (R := S)
        rw [h1, Nat.cast_one] at this
        exact this
      exact one_ne_zero h10
    have hring_eq : ringChar S = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
    rw [← hring_eq]
    exact ringChar.charP S
  exact ⟨hghat_ne, hS_nontriv, hchar_p⟩

/-- Schwartz–Zippel lemma over a finite local commutative ring $R$ of characteristic $p^\alpha$
($|R| \le 2^m$): sampling each coordinate $c_i \in \{0, \dots, M - 1\}$ independently and uniformly
with $M > 2^{m + 1} / \varepsilon$ and evaluating a nonzero $g \in R[x_1,\dots,x_n]$ of individual
degree at most $d$ at $(c_1 \cdot 1_R, \dots, c_n \cdot 1_R)$ yields $0$ with probability at most
$\frac{n d}{p} (1 + \frac{\varepsilon}{2})$. -/
theorem sz_finite_local_ring {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] [IsLocalRing R]
    {m p α n d M : ℕ} {ε : ℝ}
    (hp : Nat.Prime p) (hchar : ringChar R = p ^ α)
    (hcard : Fintype.card R ≤ 2 ^ m)
    (hε : 0 < ε) (hM_bound : (2 : ℝ) ^ (m + 1) / ε < M)
    {g : MvPolynomial (Fin n) R} (hg : g ≠ 0) (hdeg : ∀ i : Fin n, g.degreeOf i ≤ d) :
    (((Finset.univ.filter fun c : Fin n → Fin M ↦
        MvPolynomial.eval (fun i ↦ ((c i).val : R)) g = 0).card : ℝ) / (M : ℝ) ^ n) ≤
      ((n * d : ℝ) / p) * (1 + ε / 2) := by
  classical
  have hM_pos : 0 < M := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) / ε := by positivity
    have hMR : (0 : ℝ) < M := hpos.trans hM_bound
    exact_mod_cast hMR
  have hMR_pos : (0 : ℝ) < M := by exact_mod_cast hM_pos
  have hp_pos : 0 < p := hp.pos
  have hpR_pos : (0 : ℝ) < p := by exact_mod_cast hp_pos
  have hp_le_card : p ≤ Fintype.card R := by
    have hcard0 : ((Fintype.card R : ℕ) : R) = 0 := by
      obtain ⟨q, hq⟩ := addOrderOf_dvd_card (x := (1 : R))
      rw [← nsmul_one, hq, mul_nsmul, addOrderOf_nsmul_eq_zero, smul_zero]
    have hdvd_card : ringChar R ∣ Fintype.card R := ringChar.dvd hcard0
    rw [hchar] at hdvd_card
    have hα_pos : 0 < α := by
      by_contra h0
      have hα0 : α = 0 := by omega
      rw [hα0, pow_zero] at hchar
      have h10 : (1 : R) = 0 := by
        have := ringChar.Nat.cast_ringChar (R := R)
        rw [hchar, Nat.cast_one] at this; exact this
      exact one_ne_zero h10
    have hp_dvd_pα : p ∣ p ^ α := dvd_pow_self p (by omega)
    exact Nat.le_of_dvd Fintype.card_pos (hp_dvd_pα.trans hdvd_card)
  have hp_le_2m : p ≤ 2 ^ m := hp_le_card.trans hcard
  obtain ⟨k, g_hat, _, hg_eq, hghat_supp, hg_not⟩ :=
    exists_max_prime_pow_factor_mvPoly hchar hg
  let J := annihilatorIdeal R p k ⊔ Ideal.span {(p : R)}
  let S := R ⧸ J
  let π : R →+* S := Ideal.Quotient.mk J
  obtain ⟨hghat_ne, hS_nontriv, hcharS⟩ := quotient_reduction_nonzero_and_field hp hg_eq hg_not
  have : CharP S p := hcharS
  have : Fact p.Prime := ⟨hp⟩
  let φ : ZMod p →+* S := ZMod.castHom (dvd_refl p) S
  have hcast_inj : Function.Injective φ := RingHom.injective φ
  let D : Subring S := φ.range
  have hD_field : IsField D := by
    let e : ZMod p ≃+* D := RingEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b h ↦ hcast_inj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
    exact e.symm.toMulEquiv.isField (Field.toIsField (ZMod p))
  have hD_nzd := nonZeroDivisors_of_field_subring D hD_field
  let A : Finset S := Finset.univ.image φ
  have hA_sub : ∀ a ∈ A, a ∈ D := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨b, _, rfl⟩ := ha
    exact ⟨b, rfl⟩
  let μ : S → ℝ := fun a ↦
    ((Finset.univ.filter fun c : Fin M ↦ φ (c.val : ZMod p) = a).card : ℝ) / M
  have hμ_nonneg : ∀ a ∈ A, 0 ≤ μ a := fun _ _ ↦ by positivity
  have hμ_sum : ∑ a ∈ A, μ a = 1 := by
    simp only [μ, ← Finset.sum_div]
    have hpart : ∑ a ∈ A, (Finset.univ.filter fun c : Fin M ↦ φ (c.val : ZMod p) = a).card = M := by
      trans (Finset.univ : Finset (Fin M)).card
      · exact (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin M)))
          (f := fun c : Fin M ↦ φ (c.val : ZMod p)) (t := A)
          (fun c _ ↦ Finset.mem_image.mpr ⟨(c.val : ZMod p), Finset.mem_univ _, rfl⟩)).symm
      · exact Fintype.card_fin M
    rw [← Nat.cast_sum, hpart, div_self hMR_pos.ne']
  have hμ_le : ∀ a ∈ A, μ a ≤ (1 + ε / 2) / p := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨b, _, rfl⟩ := ha
    let bFin : Fin p := ⟨b.val, b.val_lt⟩
    have hfilt_eq :
        (Finset.univ.filter fun c : Fin M ↦ φ (c.val : ZMod p) = φ b) =
        (Finset.univ.filter fun c : Fin M ↦ c.val % p = bFin.val) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcast_inj.eq_iff]
      constructor
      · intro heq
        have hv := congrArg ZMod.val heq
        rw [ZMod.val_natCast] at hv
        exact hv
      · intro hmod
        apply ZMod.val_injective
        rw [ZMod.val_natCast]
        exact hmod
    have hbd := (card_mod_eq_bounds hp_pos hM_pos bFin).2
    dsimp [μ]
    rw [hfilt_eq]
    refine hbd.trans ?_
    apply div_le_div_of_nonneg_right _ hpR_pos.le
    have h1 : (p : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hp_le_2m
    have h2 : (2 : ℝ) ^ (m + 1) < M * ε := (div_lt_iff₀ hε).mp hM_bound
    have h3 : (p : ℝ) / M ≤ ε / 2 := by
      rw [div_le_div_iff₀ hMR_pos (by norm_num : (0 : ℝ) < 2)]
      have hpow : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := pow_succ (2 : ℝ) m
      nlinarith
    linarith
  have hghat_deg : ∀ i : Fin n, (MvPolynomial.map π g_hat).degreeOf i ≤ d := by
    intro i
    rw [MvPolynomial.degreeOf_le_iff]
    intro s hs
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hs
    have hs' : s ∈ g_hat.support :=
      MvPolynomial.mem_support_iff.mpr fun h0 ↦ hs (by rw [h0, map_zero])
    exact (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) s (hghat_supp hs')
  let fS : (Fin n → Fin M) → (Fin n → S) := fun c i ↦ φ ((c i).val : ZMod p)
  let Z : Finset (Fin n → S) :=
    (Fintype.piFinset fun _ : Fin n ↦ A).filter fun x ↦
      MvPolynomial.eval x (MvPolynomial.map π g_hat) = 0
  have hmap_zero : ∀ c : Fin n → Fin M,
      MvPolynomial.eval (fun i ↦ ((c i).val : R)) g = 0 → fS c ∈ Z := by
    intro c hc
    rw [hg_eq, map_mul, MvPolynomial.eval_C] at hc
    have hmemJ : MvPolynomial.eval (fun i ↦ ((c i).val : R)) g_hat ∈ J :=
      Submodule.mem_sup_left hc
    have hπ0 : π (MvPolynomial.eval (fun i ↦ ((c i).val : R)) g_hat) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmemJ
    have hcomp : (fun i : Fin n ↦ π ((c i).val : R)) = fS c := by
      ext i
      simp [fS, map_natCast]
    have hevS : MvPolynomial.eval (fS c) (MvPolynomial.map π g_hat) = 0 := by
      rw [MvPolynomial.eval_map, ← hcomp]
      change MvPolynomial.eval₂ (π.comp (RingHom.id R)) (fun i ↦ π ((c i).val : R)) g_hat = 0
      rw [← MvPolynomial.hom_eval₂]
      exact hπ0
    refine Finset.mem_filter.mpr ⟨?_, hevS⟩
    exact Fintype.mem_piFinset.mpr fun i ↦
      Finset.mem_image.mpr ⟨((c i).val : ZMod p), Finset.mem_univ _, rfl⟩
  have hsub :
      (Finset.univ.filter fun c : Fin n → Fin M ↦
        MvPolynomial.eval (fun i ↦ ((c i).val : R)) g = 0) ⊆
      (Finset.univ.filter fun c : Fin n → Fin M ↦ fS c ∈ Z) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hmap_zero c hc.2⟩
  have hcard_push :
      ((Finset.univ.filter fun c : Fin n → Fin M ↦ fS c ∈ Z).card : ℝ) / (M : ℝ) ^ n =
        ∑ x ∈ Z, ∏ i : Fin n, μ (x i) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun c : Fin n → Fin M ↦ fS c ∈ Z) (t := Z) (f := fS)
      (fun c hc ↦ (Finset.mem_filter.mp hc).2)
    rw [hfib, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hfib_eq :
        ((Finset.univ.filter fun c : Fin n → Fin M ↦ fS c ∈ Z).filter fun c ↦ fS c = x) =
        Fintype.piFinset fun i : Fin n ↦
          Finset.univ.filter fun c : Fin M ↦ φ (c.val : ZMod p) = x i := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · intro h i
        exact congrFun h.2 i
      · intro h
        have hfx : fS c = x := funext h
        exact ⟨hfx ▸ hx, hfx⟩
    rw [hfib_eq, Fintype.card_piFinset, Nat.cast_prod]
    have hMn : (M : ℝ) ^ n = ∏ _i : Fin n, (M : ℝ) := by simp
    rw [hMn, ← Finset.prod_div_distrib]
  calc
    (((Finset.univ.filter fun c : Fin n → Fin M ↦
        MvPolynomial.eval (fun i ↦ ((c i).val : R)) g = 0).card : ℝ) / (M : ℝ) ^ n)
      ≤ (((Finset.univ.filter fun c : Fin n → Fin M ↦ fS c ∈ Z).card : ℝ) / (M : ℝ) ^ n) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card hsub
    _ = ∑ x ∈ Z, ∏ i : Fin n, μ (x i) := hcard_push
    _ ≤ (n * d : ℝ) * ((1 + ε / 2) / p) :=
          weighted_schwartz_zippel_ring D hD_nzd A hA_sub μ hμ_nonneg hμ_sum hμ_le
            hghat_ne hghat_deg
    _ = ((n * d : ℝ) / p) * (1 + ε / 2) := by ring

end CslibFrontier.Algebra
