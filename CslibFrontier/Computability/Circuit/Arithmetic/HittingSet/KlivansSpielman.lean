/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Klivans–Spielman Modular Kronecker Hitting Sets for Sparse Products

Explicit polynomial-cardinality hitting sets (`Cslib.Circuits.Arithmetic.IsHittingSet`) for sparse
polynomials and products of sparse polynomials (`ΠΣΠ` gates) over arbitrary integral domains via
Klivans and Spielman's modular Kronecker substitution.

For an `n`-variate polynomial of individual degree at most `d` in every coordinate, base-`(d + 1)`
Kronecker substitution `X j ↦ T ^ ((d + 1) ^ j)` maps distinct monomials injectively to distinct
powers below `(d + 1) ^ n`. Reducing exponents modulo a prime `p` produces a univariate polynomial
of degree at most `n * d * (p - 1)` per factor, and a pigeonhole count on prime divisors of
exponent differences guarantees that among the first
`m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1` primes at least one preserves nonvanishing of all
`≤ m` factors of sparsity `≤ s`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.kroneckerWeight`: base-`(d + 1)` exponent weight.
* `CslibFrontier.Computability.Circuit.Arithmetic.kroneckerHom`: exact Kronecker substitution.
* `CslibFrontier.Computability.Circuit.Arithmetic.kroneckerModHom`: modular Kronecker substitution.
* `CslibFrontier.Computability.Circuit.Arithmetic.klivansSpielmanHittingSet`: explicit modular
  Kronecker hitting set for products of sparse polynomials.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.injOn_kroneckerWeight`,
  `CslibFrontier.Computability.Circuit.Arithmetic.kroneckerHom_eq_zero_iff`: faithfulness of exact
  base-`(d + 1)` Kronecker substitution.
* `CslibFrontier.Computability.Circuit.Arithmetic.card_klivansSpielmanHittingSet_le`: cardinality
  bound `(m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1) * S.card`.
* `CslibFrontier.Computability.Circuit.Arithmetic.isHittingSet_klivansSpielmanHittingSet`:
  Klivans–Spielman hitting-set theorem for products of at most `m` sparse polynomials.
* `CslibFrontier.Computability.Circuit.Arithmetic.isHittingSet_klivansSpielmanHittingSet_sparse`:
  specialization (`m = 1`) to `s`-sparse polynomials of individual degree at most `d`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open MvPolynomial

/-- Base-`(d + 1)` Kronecker exponent weight `∑ j : Fin n, α j * (d + 1) ^ j.1`. -/
@[expose]
def kroneckerWeight (d : ℕ) {n : ℕ} (α : Fin n →₀ ℕ) : ℕ :=
  ∑ j : Fin n, α j * (d + 1) ^ j.1

private lemma baseTupleWeight_lt_pow (d : ℕ) :
    ∀ {n : ℕ} (f : Fin n → ℕ), (∀ j : Fin n, f j ≤ d) →
      ∑ j : Fin n, f j * (d + 1) ^ j.1 < (d + 1) ^ n
  | 0, _, _ => by simp
  | n + 1, f, hf => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have ih := baseTupleWeight_lt_pow d (fun i : Fin n ↦ f i.castSucc) fun i ↦ hf i.castSucc
    have hlast : f (Fin.last n) * (d + 1) ^ n ≤ d * (d + 1) ^ n :=
      Nat.mul_le_mul_right ((d + 1) ^ n) (hf (Fin.last n))
    have hpow : (d + 1) ^ (n + 1) = (d + 1) ^ n + d * (d + 1) ^ n := by ring
    omega

private lemma baseTupleWeight_eq_imp_eq (d : ℕ) :
    ∀ {n : ℕ} {f g : Fin n → ℕ},
      (∀ j : Fin n, f j ≤ d) → (∀ j : Fin n, g j ≤ d) →
      ∑ j : Fin n, f j * (d + 1) ^ j.1 = ∑ j : Fin n, g j * (d + 1) ^ j.1 → f = g
  | 0, f, g, _, _, _ => funext fun j ↦ Fin.elim0 j
  | n + 1, f, g, hf, hg, hsum => by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
    simp only [Fin.val_castSucc, Fin.val_last] at hsum
    have hSf := baseTupleWeight_lt_pow d (fun i : Fin n ↦ f i.castSucc) fun i ↦ hf i.castSucc
    have hSg := baseTupleWeight_lt_pow d (fun i : Fin n ↦ g i.castSucc) fun i ↦ hg i.castSucc
    have hlast : f (Fin.last n) = g (Fin.last n) := by
      rcases lt_trichotomy (f (Fin.last n)) (g (Fin.last n)) with hlt | heq | hgt
      · exfalso
        have hmul : (f (Fin.last n) + 1) * (d + 1) ^ n ≤ g (Fin.last n) * (d + 1) ^ n :=
          Nat.mul_le_mul_right ((d + 1) ^ n) hlt
        have hexp : (f (Fin.last n) + 1) * (d + 1) ^ n =
            (d + 1) ^ n + f (Fin.last n) * (d + 1) ^ n := by ring
        omega
      · exact heq
      · exfalso
        have hmul : (g (Fin.last n) + 1) * (d + 1) ^ n ≤ f (Fin.last n) * (d + 1) ^ n :=
          Nat.mul_le_mul_right ((d + 1) ^ n) hgt
        have hexp : (g (Fin.last n) + 1) * (d + 1) ^ n =
            (d + 1) ^ n + g (Fin.last n) * (d + 1) ^ n := by ring
        omega
    rw [hlast] at hsum
    have hinit : (fun i : Fin n ↦ f i.castSucc) = fun i : Fin n ↦ g i.castSucc :=
      baseTupleWeight_eq_imp_eq d (fun i ↦ hf i.castSucc) (fun i ↦ hg i.castSucc)
        (Nat.add_right_cancel hsum)
    funext j
    refine Fin.lastCases hlast (fun i ↦ ?_) j
    exact congr_fun hinit i

/-- Every exponent tuple bounded coordinatewise by `d` has Kronecker weight `< (d + 1) ^ n`. -/
theorem kroneckerWeight_lt_pow {d n : ℕ} {α : Fin n →₀ ℕ} (hα : ∀ j : Fin n, α j ≤ d) :
    kroneckerWeight d α < (d + 1) ^ n :=
  baseTupleWeight_lt_pow d α hα

/-- Base-`(d + 1)` Kronecker weights are injective on `{α : Fin n →₀ ℕ | ∀ j, α j ≤ d}`. -/
theorem injOn_kroneckerWeight (n d : ℕ) :
    Set.InjOn (kroneckerWeight d) {α : Fin n →₀ ℕ | ∀ j : Fin n, α j ≤ d} := by
  intro α hα β hβ heq
  exact DFunLike.coe_injective (baseTupleWeight_eq_imp_eq d hα hβ heq)

/-- Exact Kronecker substitution `X j ↦ X ^ ((d + 1) ^ j.1)`. -/
@[expose]
noncomputable def kroneckerHom (R : Type*) [CommSemiring R] (n d : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun j : Fin n ↦ Polynomial.X ^ ((d + 1) ^ j.1)

private lemma aeval_X_pow_monomial {R : Type*} [CommSemiring R] {n : ℕ} (w : Fin n → ℕ)
    (α : Fin n →₀ ℕ) (c : R) :
    MvPolynomial.aeval (fun j : Fin n ↦ (Polynomial.X : Polynomial R) ^ w j) (monomial α c) =
      Polynomial.monomial (∑ j : Fin n, α j * w j) c := by
  rw [aeval_monomial, Polynomial.algebraMap_eq,
    Finsupp.prod_of_support_subset α (Finset.subset_univ _) _ (fun _ _ ↦ pow_zero _)]
  have hprod : (∏ j : Fin n, ((Polynomial.X : Polynomial R) ^ w j) ^ α j) =
      Polynomial.X ^ ∑ j : Fin n, α j * w j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← pow_mul, mul_comm]
  rw [hprod, Polynomial.C_mul_X_pow_eq_monomial]

@[simp]
theorem kroneckerHom_monomial (R : Type*) [CommSemiring R] (n d : ℕ) (α : Fin n →₀ ℕ) (c : R) :
    kroneckerHom R n d (monomial α c) = Polynomial.monomial (kroneckerWeight d α) c :=
  aeval_X_pow_monomial (fun j ↦ (d + 1) ^ j.1) α c

/-- Coefficient preservation of `kroneckerHom` on individual-degree-`≤ d` polynomials. -/
theorem coeff_kroneckerHom_of_forall_le {R : Type*} [CommSemiring R] {n d : ℕ}
    {f : MvPolynomial (Fin n) R} (hf : ∀ j : Fin n, f.degreeOf j ≤ d)
    {α : Fin n →₀ ℕ} (hα : ∀ j : Fin n, α j ≤ d) :
    (kroneckerHom R n d f).coeff (kroneckerWeight d α) = f.coeff α := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  have hterm (β : Fin n →₀ ℕ) (hβ : β ∈ f.support) :
      (kroneckerHom R n d (monomial β (f.coeff β))).coeff (kroneckerWeight d α) =
        if β = α then f.coeff β else 0 := by
    rw [kroneckerHom_monomial, Polynomial.coeff_monomial, Finsupp.single_apply]
    have hβ_le : ∀ j : Fin n, β j ≤ d := fun j ↦ (monomial_le_degreeOf j hβ).trans (hf j)
    have hinj : kroneckerWeight d β = kroneckerWeight d α ↔ β = α :=
      ⟨fun h ↦ injOn_kroneckerWeight n d hβ_le hα h, congrArg (kroneckerWeight d)⟩
    simp [hinj]
  rw [Finset.sum_congr rfl hterm]
  by_cases hmem : α ∈ f.support
  · rw [Finset.sum_ite_eq' f.support α (fun β ↦ f.coeff β), ite_eq_left_iff.mpr fun h ↦
      absurd hmem h]
  · rw [Finset.sum_ite_eq' f.support α (fun β ↦ f.coeff β), ite_eq_right_iff.mpr fun h ↦
      absurd h hmem, notMem_support_iff.mp hmem]

/-- Exact base-`(d + 1)` Kronecker substitution is faithful on individual-degree-`≤ d`
polynomials. -/
theorem kroneckerHom_eq_zero_iff {R : Type*} [CommSemiring R] {n d : ℕ}
    {f : MvPolynomial (Fin n) R} (hf : ∀ j : Fin n, f.degreeOf j ≤ d) :
    kroneckerHom R n d f = 0 ↔ f = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rw [h0, map_zero]⟩
  ext α
  change f.coeff α = 0
  by_cases hα : ∀ j : Fin n, α j ≤ d
  · rw [← coeff_kroneckerHom_of_forall_le hf hα, h0, Polynomial.coeff_zero]
  · push Not at hα
    obtain ⟨j, hj⟩ := hα
    by_contra hne
    have hle := (monomial_le_degreeOf j (mem_support_iff.mpr hne)).trans (hf j)
    omega

/-- Modular Kronecker substitution `X j ↦ X ^ ((d + 1) ^ j.1 % p)`. -/
@[expose]
noncomputable def kroneckerModHom (R : Type*) [CommSemiring R] (n d p : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun j : Fin n ↦ Polynomial.X ^ ((d + 1) ^ j.1 % p)

private def kroneckerModWeight (d p : ℕ) {n : ℕ} (α : Fin n →₀ ℕ) : ℕ :=
  ∑ j : Fin n, α j * ((d + 1) ^ j.1 % p)

private lemma kroneckerModHom_monomial {R : Type*} [CommSemiring R] {n d p : ℕ}
    (α : Fin n →₀ ℕ) (c : R) :
    kroneckerModHom R n d p (monomial α c) = Polynomial.monomial (kroneckerModWeight d p α) c :=
  aeval_X_pow_monomial (fun j ↦ (d + 1) ^ j.1 % p) α c

private lemma sum_modEq {ι : Type*} (s : Finset ι) {f g : ι → ℕ} {p : ℕ}
    (h : ∀ i ∈ s, f i ≡ g i [MOD p]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [MOD p] := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

private lemma kroneckerModWeight_mod_eq (d p : ℕ) {n : ℕ} (α : Fin n →₀ ℕ) :
    kroneckerModWeight d p α % p = kroneckerWeight d α % p :=
  sum_modEq Finset.univ fun j _ ↦ (Nat.mod_modEq ((d + 1) ^ j.1) p).mul_left (α j)

private def natDist (a b : ℕ) : ℕ := max a b - min a b

private lemma dvd_natDist_of_mod_eq {a b p : ℕ} (hmod : a % p = b % p) :
    p ∣ natDist a b := by
  have hle : ∀ {x y : ℕ}, x ≤ y → x % p = y % p → p ∣ y - x := by
    intro x y hxy hm
    have hx := Nat.div_add_mod x p
    have hy := Nat.div_add_mod y p
    refine ⟨y / p - x / p, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega
  rcases le_total a b with hab | hba
  · simpa [natDist, max_eq_right hab, min_eq_left hab] using hle hab hmod
  · simpa [natDist, max_eq_left hba, min_eq_right hba] using hle hba hmod.symm

private lemma exists_mem_dvd_of_prime_dvd_prod {q : ℕ} (hq : Nat.Prime q) :
    ∀ {Q : Finset ℕ}, q ∣ ∏ p ∈ Q, p → ∃ p ∈ Q, q ∣ p := by
  classical
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact fun h1 ↦ absurd h1 hq.not_dvd_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hdvd
    rcases hq.dvd_mul.mp hdvd with hqa | hqs
    · exact ⟨a, Finset.mem_insert_self a s, hqa⟩
    · obtain ⟨p, hps, hqp⟩ := ih hqs
      exact ⟨p, Finset.mem_insert_of_mem hps, hqp⟩

private lemma prod_primes_dvd_of_forall_dvd {M : ℕ} {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, Nat.Prime p ∧ p ∣ M) : (∏ p ∈ Q, p) ∣ M := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | insert q Q hq ih =>
    rw [Finset.prod_insert hq]
    have hq_mem := hQ q (Finset.mem_insert_self q Q)
    have ih' := ih fun p hp ↦ hQ p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ Q, p) := by
      rw [hq_mem.1.coprime_iff_not_dvd]
      intro hdvd
      obtain ⟨p, hpQ, hqp⟩ := exists_mem_dvd_of_prime_dvd_prod hq_mem.1 hdvd
      have hp_prime := (hQ p (Finset.mem_insert_of_mem hpQ)).1
      exact hq (((Nat.prime_dvd_prime_iff_eq hq_mem.1 hp_prime).mp hqp) ▸ hpQ)
    exact hcop.mul_dvd_of_dvd_of_dvd hq_mem.2 ih'

private lemma two_pow_card_le_of_forall_prime_dvd {M : ℕ} (hM : 1 ≤ M) {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, Nat.Prime p ∧ p ∣ M) : 2 ^ Q.card ≤ M := by
  have hprod_le : (∏ p ∈ Q, p) ≤ M :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by omega)) (prod_primes_dvd_of_forall_dvd hQ)
  have htwo : 2 ^ Q.card ≤ ∏ p ∈ Q, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod fun p hp ↦ (hQ p hp).1.two_le
  exact htwo.trans hprod_le

private lemma natDegree_kroneckerModHom_le {R : Type*} [CommSemiring R] {n d p B : ℕ}
    (hp : 0 < p) (hpB : p - 1 ≤ B) {g : MvPolynomial (Fin n) R}
    (hg : ∀ j : Fin n, g.degreeOf j ≤ d) :
    (kroneckerModHom R n d p g).natDegree ≤ n * d * B := by
  conv_lhs => rw [g.as_sum]
  rw [map_sum]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun α hα ↦ ?_)
  dsimp only [Function.comp_apply]
  rw [kroneckerModHom_monomial]
  refine (Polynomial.natDegree_monomial_le _).trans ?_
  have hterm : ∀ j : Fin n, α j * ((d + 1) ^ j.1 % p) ≤ d * B := fun j ↦ by
    have hαj : α j ≤ d := (monomial_le_degreeOf j hα).trans (hg j)
    have hmod : (d + 1) ^ j.1 % p ≤ B :=
      (Nat.le_sub_one_of_lt (Nat.mod_lt _ hp)).trans hpB
    exact Nat.mul_le_mul hαj hmod
  calc
    kroneckerModWeight d p α = ∑ j : Fin n, α j * ((d + 1) ^ j.1 % p) := rfl
    _ ≤ ∑ _ : Fin n, d * B := Finset.sum_le_sum fun j _ ↦ hterm j
    _ = n * d * B := by simp [Nat.mul_assoc]

private lemma natDegree_list_prod_le {R : Type*} [CommSemiring R] (B : ℕ) :
    ∀ (L : List (Polynomial R)), (∀ q ∈ L, q.natDegree ≤ B) → L.prod.natDegree ≤ L.length * B
  | [], _ => by simp
  | q :: qs, hL => by
    simp only [List.prod_cons, List.length_cons]
    refine Polynomial.natDegree_mul_le.trans ?_
    have hq := hL q List.mem_cons_self
    have hqs := natDegree_list_prod_le B qs fun r hr ↦ hL r (List.mem_cons_of_mem q hr)
    have hexp : (qs.length + 1) * B = B + qs.length * B := by ring
    omega

private lemma eval_kroneckerModHom {R : Type*} [CommSemiring R] (n d p : ℕ) (β : R)
    (f : MvPolynomial (Fin n) R) :
    (kroneckerModHom R n d p f).eval β =
      MvPolynomial.eval (fun j : Fin n ↦ β ^ ((d + 1) ^ j.1 % p)) f := by
  have hcomp : (Polynomial.evalRingHom β).comp (kroneckerModHom R n d p).toRingHom =
      MvPolynomial.eval (fun j : Fin n ↦ β ^ ((d + 1) ^ j.1 % p)) := by
    ext r <;> simp [kroneckerModHom]
  exact RingHom.congr_fun hcomp f

/-- Klivans–Spielman modular Kronecker hitting set for products of at most `m` polynomials in `n`
variables of monomial sparsity at most `s` and individual degree at most `d`. -/
@[expose]
noncomputable def klivansSpielmanHittingSet {R : Type*} [Monoid R]
    (m s d n : ℕ) (S : Finset R) : Finset (Fin n → R) := by
  classical
  let N := m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1
  let primes := (Finset.range N).image (Nat.nth Nat.Prime)
  exact primes.biUnion fun p ↦ S.image fun (β : R) (j : Fin n) ↦ β ^ ((d + 1) ^ j.1 % p)

/-- Membership in `klivansSpielmanHittingSet`. -/
theorem mem_klivansSpielmanHittingSet {R : Type*} [Monoid R]
    {m s d n : ℕ} {S : Finset R} {x : Fin n → R} :
    x ∈ klivansSpielmanHittingSet m s d n S ↔
      ∃ k < m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1,
        ∃ β ∈ S, (fun j : Fin n ↦ β ^ ((d + 1) ^ j.1 % Nat.nth Nat.Prime k)) = x := by
  simp [klivansSpielmanHittingSet]

/-- Cardinality bound for `klivansSpielmanHittingSet`. -/
theorem card_klivansSpielmanHittingSet_le {R : Type*} [Monoid R]
    (m s d n : ℕ) (S : Finset R) :
    (klivansSpielmanHittingSet m s d n S).card ≤
      (m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1) * S.card := by
  classical
  let N := m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1
  let primes := (Finset.range N).image (Nat.nth Nat.Prime)
  let tup (p : ℕ) (β : R) : Fin n → R := fun j ↦ β ^ ((d + 1) ^ j.1 % p)
  have hH : klivansSpielmanHittingSet m s d n S =
      primes.biUnion fun p ↦ S.image (tup p) := by
    ext x; simp [klivansSpielmanHittingSet, N, primes, tup]
  rw [hH]
  calc
    (primes.biUnion fun p ↦ S.image (tup p)).card
      ≤ ∑ p ∈ primes, (S.image (tup p)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ primes, S.card := Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le
    _ = primes.card * S.card := by simp
    _ ≤ N * S.card :=
      Nat.mul_le_mul_right S.card (Finset.card_image_le.trans (by simp [N]))

private lemma kroneckerModHom_ne_zero_of_forall_not_dvd {R : Type*} [CommSemiring R]
    {n d p : ℕ} {g : MvPolynomial (Fin n) R} {α₀ : Fin n →₀ ℕ} (hα₀ : α₀ ∈ g.support)
    (hndvd : ∀ α ∈ g.support.erase α₀,
      ¬ p ∣ natDist (kroneckerWeight d α) (kroneckerWeight d α₀)) :
    kroneckerModHom R n d p g ≠ 0 := by
  intro h0
  have hcoeff0 : (kroneckerModHom R n d p g).coeff (kroneckerModWeight d p α₀) = 0 := by
    rw [h0, Polynomial.coeff_zero]
  have hcoeff_eq : (kroneckerModHom R n d p g).coeff (kroneckerModWeight d p α₀) = g.coeff α₀ := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single α₀]
    · rw [kroneckerModHom_monomial, Polynomial.coeff_monomial, Finsupp.single_apply,
        ite_eq_left_iff.mpr fun h ↦ absurd rfl h]
    · intro α hα_supp hα_ne
      rw [kroneckerModHom_monomial, Polynomial.coeff_monomial, Finsupp.single_apply,
        ite_eq_right_iff]
      intro hmw_eq
      have hmod : kroneckerWeight d α % p = kroneckerWeight d α₀ % p := by
        rw [← kroneckerModWeight_mod_eq d p α, ← kroneckerModWeight_mod_eq d p α₀, hmw_eq]
      exact False.elim (hndvd α (Finset.mem_erase.mpr ⟨hα_ne, hα_supp⟩)
        (dvd_natDist_of_mod_eq hmod))
    · exact fun hnot ↦ absurd hα₀ hnot
  exact mem_support_iff.mp hα₀ (hcoeff_eq.symm.trans hcoeff0)

private lemma card_filter_dvd_kronecker_dist_le {n d N : ℕ} {α α₀ : Fin n →₀ ℕ}
    (hα_ne : α ≠ α₀) (hα_le : ∀ j : Fin n, α j ≤ d) (hα₀_le : ∀ j : Fin n, α₀ j ≤ d) :
    (((Finset.range N).image (Nat.nth Nat.Prime)).filter fun p ↦
      p ∣ natDist (kroneckerWeight d α) (kroneckerWeight d α₀)).card ≤
      n * (Nat.log 2 (d + 1) + 1) := by
  let K := n * (Nat.log 2 (d + 1) + 1)
  have hw_ne : kroneckerWeight d α ≠ kroneckerWeight d α₀ := fun heq ↦
    hα_ne (injOn_kroneckerWeight n d hα_le hα₀_le heq)
  have hw_lt₁ := kroneckerWeight_lt_pow hα_le
  have hw_lt₂ := kroneckerWeight_lt_pow hα₀_le
  let M := natDist (kroneckerWeight d α) (kroneckerWeight d α₀)
  have hM_pos : 1 ≤ M := by dsimp only [M, natDist]; omega
  have hM_lt_pow : M < (d + 1) ^ n := by dsimp only [M, natDist]; omega
  have hd_le_two : d + 1 ≤ 2 ^ (Nat.log 2 (d + 1) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (d + 1)).le
  have hpow_le : (d + 1) ^ n ≤ 2 ^ K := by
    calc
      (d + 1) ^ n ≤ (2 ^ (Nat.log 2 (d + 1) + 1)) ^ n := Nat.pow_le_pow_left hd_le_two n
      _ = 2 ^ K := by rw [← Nat.pow_mul, Nat.mul_comm]
  let Q := (((Finset.range N).image (Nat.nth Nat.Prime)).filter fun p ↦ p ∣ M)
  have htwo_le : 2 ^ Q.card ≤ M :=
    two_pow_card_le_of_forall_prime_dvd hM_pos fun p hp ↦ by
      obtain ⟨hp_pr, hp_dvd⟩ := Finset.mem_filter.mp hp
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp_pr
      exact ⟨Nat.prime_nth_prime k, hp_dvd⟩
  have htwo_lt : 2 ^ Q.card < 2 ^ K :=
    lt_of_le_of_lt htwo_le (lt_of_lt_of_le hM_lt_pow hpow_le)
  by_contra! hgt
  exact absurd (Nat.pow_le_pow_right (by decide : 0 < 2) hgt.le) (not_le_of_gt htwo_lt)

/-- **Klivans–Spielman hitting-set theorem for products of sparse polynomials**
: over an integral domain `R`, if `S` has cardinality strictly
exceeding `m * n * d * (Nat.nth Nat.Prime (N - 1) - 1)` where
`N := m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1`, then `klivansSpielmanHittingSet m s d n S`
is a hitting set (`Cslib.Circuits.Arithmetic.IsHittingSet`) for all products of at most `m`
polynomials in `n` variables of sparsity at most `s` and individual degree at most `d`.
-/
theorem isHittingSet_klivansSpielmanHittingSet {R : Type*} [CommRing R] [IsDomain R]
    (m s d n : ℕ) (S : Finset R)
    (hS :
      let N := m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1
      m * n * d * (Nat.nth Nat.Prime (N - 1) - 1) < S.card) :
    Cslib.Circuits.Arithmetic.IsHittingSet
      (klivansSpielmanHittingSet m s d n S)
      {f : MvPolynomial (Fin n) R | ∃ L : List (MvPolynomial (Fin n) R),
        L.length ≤ m ∧
        (∀ g ∈ L, g.support.card ≤ s ∧ ∀ j : Fin n, g.degreeOf j ≤ d) ∧
        L.prod = f} := by
  classical
  let K := n * (Nat.log 2 (d + 1) + 1)
  let N := m * (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1
  let primes : Finset ℕ := (Finset.range N).image (Nat.nth Nat.Prime)
  have hprimes_card : primes.card = N := by
    rw [Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOfPred_prime),
      Finset.card_range]
  rintro f ⟨L, hlen, hfac, rfl⟩ hf_ne
  have hmem_ne : ∀ g ∈ L, g ≠ 0 := fun g hg hg0 ↦
    hf_ne (List.prod_eq_zero (hg0 ▸ hg))
  let gAt (idx : Fin L.length) : MvPolynomial (Fin n) R := L[idx.1]
  have hgAt_mem (idx : Fin L.length) : gAt idx ∈ L := List.getElem_mem idx.2
  have hgAt_supp (idx : Fin L.length) : (gAt idx).support.Nonempty :=
    support_nonempty.mpr (hmem_ne (gAt idx) (hgAt_mem idx))
  let α₀ (idx : Fin L.length) : Fin n →₀ ℕ := (hgAt_supp idx).choose
  have hα₀_mem (idx : Fin L.length) : α₀ idx ∈ (gAt idx).support :=
    (hgAt_supp idx).choose_spec
  let rem (idx : Fin L.length) : Finset (Fin n →₀ ℕ) :=
    (gAt idx).support.erase (α₀ idx)
  let badPair (idx : Fin L.length) (α : Fin n →₀ ℕ) : Finset ℕ :=
    primes.filter fun p ↦ p ∣ natDist (kroneckerWeight d α) (kroneckerWeight d (α₀ idx))
  have hbadPair_card (idx : Fin L.length) {α : Fin n →₀ ℕ} (hα : α ∈ rem idx) :
      (badPair idx α).card ≤ K := by
    have hdeg := (hfac (gAt idx) (hgAt_mem idx)).2
    exact card_filter_dvd_kronecker_dist_le (Finset.mem_erase.mp hα).1
      (fun j ↦ (monomial_le_degreeOf j (Finset.mem_erase.mp hα).2).trans (hdeg j))
      (fun j ↦ (monomial_le_degreeOf j (hα₀_mem idx)).trans (hdeg j))
  let badPrimes : Finset ℕ :=
    Finset.univ.biUnion fun idx : Fin L.length ↦ (rem idx).biUnion (badPair idx)
  have hbad_lt : badPrimes.card < primes.card := by
    have hrem_card (idx : Fin L.length) : (rem idx).card ≤ s - 1 := by
      rw [Finset.card_erase_of_mem (hα₀_mem idx)]
      exact Nat.sub_le_sub_right (hfac (gAt idx) (hgAt_mem idx)).1 1
    have hsum_le : badPrimes.card ≤ m * (s - 1) * K := by
      calc
        badPrimes.card
          ≤ ∑ idx : Fin L.length, ((rem idx).biUnion (badPair idx)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ idx : Fin L.length, ∑ α ∈ rem idx, (badPair idx α).card :=
            Finset.sum_le_sum fun _ _ ↦ Finset.card_biUnion_le
        _ ≤ ∑ idx : Fin L.length, ∑ _ ∈ rem idx, K :=
            Finset.sum_le_sum fun idx _ ↦ Finset.sum_le_sum fun α hα ↦ hbadPair_card idx hα
        _ = ∑ idx : Fin L.length, (rem idx).card * K := by simp
        _ ≤ ∑ _ : Fin L.length, (s - 1) * K :=
            Finset.sum_le_sum fun idx _ ↦ Nat.mul_le_mul_right K (hrem_card idx)
        _ = L.length * ((s - 1) * K) := by simp
        _ ≤ m * ((s - 1) * K) := Nat.mul_le_mul_right ((s - 1) * K) hlen
        _ = m * (s - 1) * K := by ring
    rw [hprimes_card]
    have hNK : N = m * (s - 1) * K + 1 := by dsimp only [N, K]; ring
    omega
  have hgood_nonempty : (primes \ badPrimes).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
    exact absurd (Finset.card_le_card hempty) (not_le_of_gt hbad_lt)
  obtain ⟨p, hp_sdiff⟩ := hgood_nonempty
  obtain ⟨hp_primes, hp_not_bad⟩ := Finset.mem_sdiff.mp hp_sdiff
  obtain ⟨k_idx, hk_mem, rfl⟩ := Finset.mem_image.mp hp_primes
  have hk_lt : k_idx < N := Finset.mem_range.mp hk_mem
  let p := Nat.nth Nat.Prime k_idx
  have hp_prime : Nat.Prime p := Nat.prime_nth_prime k_idx
  have hp_le_max : p ≤ Nat.nth Nat.Prime (N - 1) :=
    Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
  have hg_mod_ne (idx : Fin L.length) : kroneckerModHom R n d p (gAt idx) ≠ 0 :=
    kroneckerModHom_ne_zero_of_forall_not_dvd (hα₀_mem idx) fun α hα hdvd ↦
      hp_not_bad (Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ idx,
        Finset.mem_biUnion.mpr ⟨α, hα, Finset.mem_filter.mpr ⟨hp_primes, hdvd⟩⟩⟩)
  let F : Polynomial R := kroneckerModHom R n d p L.prod
  have hF_prod : F = (L.map (kroneckerModHom R n d p)).prod :=
    map_list_prod (kroneckerModHom R n d p).toRingHom L
  have hF_ne : F ≠ 0 := by
    rw [hF_prod]
    refine List.prod_ne_zero fun hzero ↦ ?_
    obtain ⟨g, hg_mem, hg_eq0⟩ := List.mem_map.mp hzero
    obtain ⟨idx_val, hidx_lt, rfl⟩ := List.mem_iff_getElem.mp hg_mem
    exact hg_mod_ne ⟨idx_val, hidx_lt⟩ hg_eq0
  have hF_deg : F.natDegree < S.card := by
    rw [hF_prod]
    let B := Nat.nth Nat.Prime (N - 1) - 1
    have hL_deg : (L.map (kroneckerModHom R n d p)).prod.natDegree ≤
        L.length * (n * d * B) := by
      simpa using natDegree_list_prod_le (n * d * B)
        (L.map (kroneckerModHom R n d p)) fun q hq ↦ by
          obtain ⟨g, hg_mem, rfl⟩ := List.mem_map.mp hq
          exact natDegree_kroneckerModHom_le hp_prime.pos
            (Nat.sub_le_sub_right hp_le_max 1) (hfac g hg_mem).2
    have hmul_le : L.length * (n * d * B) ≤ m * n * d * B := by
      calc
        L.length * (n * d * B) ≤ m * (n * d * B) :=
          Nat.mul_le_mul_right (n * d * B) hlen
        _ = m * n * d * B := by ring
    exact (hL_deg.trans hmul_le).trans_lt hS
  have hex_β : ∃ β ∈ S, F.eval β ≠ 0 := by
    by_contra! hall
    exact hF_ne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' F S hall hF_deg)
  obtain ⟨β, hβ_mem, hFβ_ne⟩ := hex_β
  refine ⟨fun j : Fin n ↦ β ^ ((d + 1) ^ j.1 % p), ?_, ?_⟩
  · exact mem_klivansSpielmanHittingSet.mpr ⟨k_idx, hk_lt, β, hβ_mem, rfl⟩
  · rwa [← eval_kroneckerModHom n d p β L.prod]

/-- Specialization of `isHittingSet_klivansSpielmanHittingSet` (`m = 1`) to `s`-sparse polynomials
of individual degree at most `d`. -/
theorem isHittingSet_klivansSpielmanHittingSet_sparse {R : Type*} [CommRing R] [IsDomain R]
    (s d n : ℕ) (S : Finset R)
    (hS :
      let N := (s - 1) * n * (Nat.log 2 (d + 1) + 1) + 1
      n * d * (Nat.nth Nat.Prime (N - 1) - 1) < S.card) :
    Cslib.Circuits.Arithmetic.IsHittingSet
      (klivansSpielmanHittingSet 1 s d n S)
      {f : MvPolynomial (Fin n) R | f.support.card ≤ s ∧ ∀ j : Fin n, f.degreeOf j ≤ d} := by
  refine (isHittingSet_klivansSpielmanHittingSet 1 s d n S (by simpa using hS)).mono le_rfl ?_
  rintro f ⟨hsp, hdeg⟩
  exact ⟨[f], by simp, fun g hg ↦ by simpa [List.mem_singleton.mp hg] using ⟨hsp, hdeg⟩, by simp⟩

end CslibFrontier.Computability.Circuit.Arithmetic
