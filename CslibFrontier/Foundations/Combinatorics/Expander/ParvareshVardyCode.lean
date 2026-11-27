module
/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.XorExpander
public import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Foundations.Combinatorics.Expander.Bipartite
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic Parvaresh–Vardy Lossless Vertex Expanders and Explicit Graph Families

This module proves the algebraic lossless bipartite vertex expansion of the
Guruswami–Umans–Vadhan graph built from Parvaresh–Vardy multivariate polynomial codes over finite
fields, the irreducibility of the explicit `3 ^ (k + 1)`-th cyclotomic trinomials
`X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1` over binary fields of degree coprime to `6`, and the general
conversion from polynomial-time explicit bipartite graph families to polynomial-size Boolean
neighbor-list circuits, under standard Lean constraints.

Given a finite field `F`, a monic irreducible polynomial `E : F[X]` of degree `n ≥ 2`, and
parameters `h ≥ 2`, `m ≥ 1` with `m * (h - 1) * (n - 1) < |F|`, the Parvaresh–Vardy bipartite graph
has left vertex set `PvLeft F E = {f : F[X] // f.natDegree < n}`, right vertex set
`F × (Fin m → F)`, left degree `|F|`, and `y`-th neighbor of `f` equal to
`(y, f(y), (f^h mod E)(y), …, (f^(h^(m-1)) mod E)(y))`. Algebraic list-decoding shows that every
left subset `W` of size at most `h ^ m` has at least
`(|F| - m * (h - 1) * (n - 1)) * |W|` right neighbors.

## Main definitions

* `CslibFrontier.ParvareshVardy.trinom`: the cyclotomic trinomial
  `X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1`.
* `CslibFrontier.ParvareshVardy.PvLeft`, `CslibFrontier.ParvareshVardy.pvLeftEquiv`: left vertex
  space of
  polynomials of degree strictly less than `E.natDegree` and its coordinate equivalence.
* `CslibFrontier.ParvareshVardy.pvPowerRem`, `CslibFrontier.ParvareshVardy.pvNeighbor`,
  `CslibFrontier.ParvareshVardy.pvAdj`: iterated `h`-th power remainders, neighbor map, and
  bipartite
  incidence relation of the Parvaresh–Vardy expander.
* `CslibFrontier.ParvareshVardy.lsbValue`: little-endian natural-number value of `List Bool`.
* `CslibFrontier.ParvareshVardy.ExplicitBipartiteFamily`: left-regular bipartite graph family whose
  neighbor function is computable in polynomial time on binary encodings.

## Main results

* `CslibFrontier.ParvareshVardy.irreducible_trinom`: `trinom F k` is irreducible of degree
  `2 * 3 ^ k`
  over every finite field `F` of cardinality `2 ^ t` with `Nat.Coprime t 6`.
* `CslibFrontier.ParvareshVardy.isBipartiteExpander_pvAdj`,
  `CslibFrontier.ParvareshVardy.isVertexExpander_pvAdj`: `pvAdj E h m` is an
  `(h ^ m, |F|, |F| - m * (h - 1) * (E.natDegree - 1))`-expander.
* `CslibFrontier.ParvareshVardy.isBipartiteExpander_pullback`: expansion is preserved under pulling
  back
  along a left injection and a right equivalence.
* `CslibFrontier.ParvareshVardy.exists_circuit_family_of_polyTime_bits`: fixing a parameter and
  input
  width of a polynomial-time Boolean predicate yields polynomial-size De Morgan circuits.
* `CslibFrontier.ParvareshVardy.exists_neighbor_circuit_of_explicit`: every
  `ExplicitBipartiteFamily`
  admits polynomial-size De Morgan circuits computing the binary neighbor list of a left vertex.
-/

public section

namespace CslibFrontier.ParvareshVardy

open Polynomial Finset
open CslibFrontier.ProofComplexity

/-! ### Explicit Irreducible Cyclotomic Trinomials over Binary Fields -/

section IrreducibleTrinomial

/-- The `3 ^ (k + 1)`-th cyclotomic trinomial `X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1`. -/
@[expose] noncomputable def trinom (R : Type*) [Semiring R] (k : ℕ) : R[X] :=
  X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1

private theorem pow_two_two_mul_three_pow (k : ℕ) :
    ∃ c : ℕ, 2 ^ (2 * 3 ^ k) = 1 + 3 ^ (k + 1) * c ∧ ¬ 3 ∣ c := by
  induction k with
  | zero => exact ⟨1, by norm_num, by decide⟩
  | succ k ih =>
    obtain ⟨c, hc, hndvd⟩ := ih
    refine ⟨c + 3 * (3 ^ k * c ^ 2 + 3 ^ (2 * k) * c ^ 3), ?_, ?_⟩
    · have hexp : 2 * 3 ^ (k + 1) = 2 * 3 ^ k * 3 := by ring
      rw [hexp, pow_mul, hc]
      ring
    · intro hdvd
      have h3 : 3 ∣ 3 * (3 ^ k * c ^ 2 + 3 ^ (2 * k) * c ^ 3) := dvd_mul_right 3 _
      exact hndvd ((Nat.dvd_add_iff_left h3).2 hdvd)

private theorem pow_two_odd_mod_three (m : ℕ) (hm : m % 2 = 1) : 2 ^ m % 3 = 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
  clear hm
  induction j with
  | zero => rfl
  | succ j ih =>
    have hexp : 2 ^ (2 * (j + 1) + 1) = 4 * 2 ^ (2 * j + 1) := by ring
    rw [hexp, Nat.mul_mod, ih]

private theorem three_pow_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

private theorem coprime_two_three_pow (k : ℕ) : Nat.Coprime 2 (3 ^ (k + 1)) :=
  Nat.Coprime.pow_right (k + 1) (by decide)

private theorem orderOf_two_mod_three_pow (k : ℕ) :
    orderOf (ZMod.unitOfCoprime 2 (coprime_two_three_pow k)) = 2 * 3 ^ k := by
  set u := ZMod.unitOfCoprime 2 (coprime_two_three_pow k)
  have hu_pow : ∀ m : ℕ, ((u ^ m : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) =
      ((2 ^ m : ℕ) : ZMod (3 ^ (k + 1))) := fun m ↦ by simp [u]
  apply orderOf_eq_of_pow_and_pow_div_prime
  · apply Units.ext
    rw [hu_pow, Units.val_one]
    obtain ⟨c, hc, -⟩ := pow_two_two_mul_three_pow k
    rw [hc, Nat.cast_add, Nat.cast_one, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  · intro p hp hdvd
    have hp23 : p = 2 ∨ (p = 3 ∧ 1 ≤ k) := by
      rcases hp.dvd_mul.1 hdvd with h2 | h3
      · have hle := Nat.le_of_dvd (by decide) h2
        have hge := hp.two_le
        exact .inl (by omega)
      · rcases k with _ | k'
        · simp [hp.ne_one] at h3
        · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
            (hp.dvd_of_dvd_pow h3)
          exact .inr ⟨hp3, Nat.succ_le_succ (Nat.zero_le k')⟩
    rcases hp23 with rfl | ⟨rfl, hk1⟩
    · intro h1
      have hdiv : 2 * 3 ^ k / 2 = 3 ^ k := Nat.mul_div_cancel_left _ (by decide)
      have h1' : u ^ 3 ^ k = 1 := hdiv ▸ h1
      have hval := congrArg Units.val h1'
      rw [hu_pow, Units.val_one] at hval
      have hge1 : 1 ≤ 2 ^ 3 ^ k := Nat.one_le_pow _ _ (by decide)
      have hsub : ((2 ^ 3 ^ k - 1 : ℕ) : ZMod (3 ^ (k + 1))) = 0 := by
        rw [Nat.cast_sub hge1, hval, Nat.cast_one, sub_self]
      have hdvd3 : 3 ^ (k + 1) ∣ 2 ^ 3 ^ k - 1 := (ZMod.natCast_eq_zero_iff _ _).1 hsub
      have hd3 : 3 ∣ 2 ^ 3 ^ k - 1 := dvd_trans ⟨3 ^ k, by ring⟩ hdvd3
      have hmod0 := Nat.mod_eq_zero_of_dvd hd3
      have hmod := pow_two_odd_mod_three (3 ^ k) (three_pow_mod_two k)
      omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      intro h1
      have hdiv : 2 * 3 ^ (k' + 1) / 3 = 2 * 3 ^ k' := by
        have hmul : 2 * 3 ^ (k' + 1) = 3 * (2 * 3 ^ k') := by ring
        rw [hmul]
        exact Nat.mul_div_cancel_left (2 * 3 ^ k') (by decide)
      have h1' : u ^ (2 * 3 ^ k') = 1 := hdiv ▸ h1
      have hval := congrArg Units.val h1'
      rw [hu_pow, Units.val_one] at hval
      obtain ⟨c, hc, hndvd⟩ := pow_two_two_mul_three_pow k'
      have hsub : ((3 ^ (k' + 1) * c : ℕ) : ZMod (3 ^ (k' + 2))) = 0 := by
        have hcast : ((1 + 3 ^ (k' + 1) * c : ℕ) : ZMod (3 ^ (k' + 2))) = 1 := hc ▸ hval
        rw [Nat.cast_add, Nat.cast_one] at hcast
        exact add_left_cancel (hcast.trans (add_zero 1).symm)
      have hdvd' : 3 ^ (k' + 2) ∣ 3 ^ (k' + 1) * c := (ZMod.natCast_eq_zero_iff _ _).1 hsub
      have hpow : 3 ^ (k' + 2) = 3 ^ (k' + 1) * 3 := by ring
      rw [hpow] at hdvd'
      exact hndvd ((Nat.mul_dvd_mul_iff_left (by positivity)).1 hdvd')

private theorem orderOf_two_pow_mod_three_pow {t : ℕ} (hcop : Nat.Coprime t 6) (k : ℕ) :
    orderOf (ZMod.unitOfCoprime (2 ^ t) ((coprime_two_three_pow k).pow_left t)) = 2 * 3 ^ k := by
  have heq : ZMod.unitOfCoprime (2 ^ t) ((coprime_two_three_pow k).pow_left t) =
      ZMod.unitOfCoprime 2 (coprime_two_three_pow k) ^ t := by
    apply Units.ext; simp
  have hcop2 : Nat.Coprime t 2 := Nat.Coprime.coprime_dvd_right (by decide) hcop
  have hcop3 : Nat.Coprime t 3 := Nat.Coprime.coprime_dvd_right (by decide) hcop
  have hcop_ord : Nat.Coprime (2 * 3 ^ k) t := hcop2.symm.mul_left (hcop3.symm.pow_left k)
  rw [heq]
  rw [← orderOf_two_mod_three_pow k] at hcop_ord ⊢
  exact hcop_ord.orderOf_pow

/-- `trinom R k` coincides with the `3 ^ (k + 1)`-th cyclotomic polynomial. -/
theorem cyclotomic_three_pow_eq_trinom (R : Type*) [CommRing R] (k : ℕ) :
    Polynomial.cyclotomic (3 ^ (k + 1)) R = trinom R k := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_three, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, trinom]
  ring

/-- `trinom R k` has degree `2 * 3 ^ k` over every nontrivial semiring. -/
theorem natDegree_trinom (R : Type*) [Semiring R] [Nontrivial R] (k : ℕ) :
    (trinom R k).natDegree = 2 * 3 ^ k := by
  have hpos : 0 < 3 ^ k := by positivity
  have hrest : (X ^ 3 ^ k + (1 : R[X])).natDegree < (X ^ (2 * 3 ^ k) : R[X]).natDegree := by
    rw [natDegree_X_pow]
    calc (X ^ 3 ^ k + (1 : R[X])).natDegree
        ≤ max (X ^ 3 ^ k : R[X]).natDegree (1 : R[X]).natDegree := natDegree_add_le _ _
      _ = 3 ^ k := by simp
      _ < 2 * 3 ^ k := by omega
  rw [trinom, add_assoc, natDegree_add_eq_left_of_natDegree_lt hrest, natDegree_X_pow]

/-- `trinom R k` is monic over every semiring. -/
theorem monic_trinom (R : Type*) [Semiring R] (k : ℕ) : (trinom R k).Monic := by
  nontriviality R
  have hpos : 0 < 3 ^ k := by positivity
  rw [trinom, add_assoc]
  apply Monic.add_of_left (monic_X_pow _)
  calc (X ^ 3 ^ k + (1 : R[X])).degree
      ≤ max (X ^ 3 ^ k : R[X]).degree (1 : R[X]).degree := degree_add_le _ _
    _ ≤ (3 ^ k : ℕ) := by simp [degree_X_pow]
    _ < ((2 * 3 ^ k : ℕ) : WithBot ℕ) := by exact_mod_cast (show 3 ^ k < 2 * 3 ^ k by omega)
    _ = (X ^ (2 * 3 ^ k) : R[X]).degree := (degree_X_pow _).symm

/-- `trinom R k` has degree at least `2` over every nontrivial semiring. -/
theorem two_le_natDegree_trinom (R : Type*) [Semiring R] [Nontrivial R] (k : ℕ) :
    2 ≤ (trinom R k).natDegree := by
  rw [natDegree_trinom]
  have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by decide)
  omega

/-- Over any finite field `F` of cardinality `2 ^ t` with `Nat.Coprime t 6`, the trinomial
`X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1` is irreducible for every `k : ℕ`. -/
theorem irreducible_trinom {F : Type*} [Field F] [Fintype F] {t : ℕ}
    (ht : Fintype.card F = 2 ^ t) (hcop : Nat.Coprime t 6) (k : ℕ) :
    Irreducible (trinom F k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Polynomial.irreducible_of_dvd_cyclotomic_of_natDegree ht (coprime_two_three_pow k)
  · rw [cyclotomic_three_pow_eq_trinom]
  · rw [natDegree_trinom, orderOf_two_pow_mod_three_pow hcop k]

end IrreducibleTrinomial

/-! ### Algebraic Parvaresh–Vardy Lossless Vertex Expansion -/

section AlgebraicExpansion

/-- Left vertices of the Parvaresh–Vardy bipartite graph: polynomials over `F` of degree strictly
less than `E.natDegree`. -/
@[expose] def PvLeft (F : Type*) [Semiring F] (E : F[X]) : Type _ :=
  { f : F[X] // f.natDegree < E.natDegree }

/-- Coordinate equivalence between `Fin E.natDegree → F` and `PvLeft F E` when
`0 < E.natDegree`. -/
noncomputable def pvLeftEquiv {F : Type*} [Semiring F] {E : F[X]} (hE : 0 < E.natDegree) :
    (Fin E.natDegree → F) ≃ PvLeft F E where
  toFun c := ⟨∑ i : Fin E.natDegree, C (c i) * X ^ i.val, by
    refine (natDegree_sum_le _ _).trans_lt ?_
    rw [Finset.fold_max_lt]
    exact ⟨hE, fun i _ ↦ (natDegree_C_mul_X_pow_le (c i) i.val).trans_lt i.isLt⟩⟩
  invFun f i := f.1.coeff i.val
  left_inv c := by
    funext i
    simp only [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i
      (fun j _ hne ↦ by have : i.val ≠ j.val := fun h ↦ hne (Fin.ext h.symm); simp [this])
      (fun hm ↦ absurd (Finset.mem_univ _) hm)]
    simp
  right_inv f := by
    apply Subtype.ext
    ext j
    simp only [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases hj : j < E.natDegree
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro i _ hne
        have hne' : j ≠ i.val := fun h ↦ hne (Fin.ext h.symm)
        simp [hne']
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [Finset.sum_eq_zero]
      · exact (coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le f.2 (by omega))).symm
      · intro i _
        have hne' : j ≠ i.val := by have := i.isLt; omega
        simp [hne']

/-- Iterated `h`-th power remainder `f ^ (h ^ i) %ₘ E` used in the Parvaresh–Vardy code. -/
@[expose] noncomputable def pvPowerRem {F : Type*} [CommRing F] (E : F[X]) (h : ℕ)
    (f : F[X]) (i : ℕ) : F[X] :=
  (f ^ (h ^ i)) %ₘ E

/-- Base case `i = 0` for `pvPowerRem`: reduces `f` modulo `E`. -/
@[simp] theorem pvPowerRem_zero {F : Type*} [CommRing F] (E : F[X]) (h : ℕ) (f : F[X]) :
    pvPowerRem E h f 0 = f %ₘ E := by
  simp [pvPowerRem]

/-- Recursive step for `pvPowerRem`: raising to the `h`-th power and reducing modulo a monic `E`. -/
theorem pvPowerRem_succ {F : Type*} [CommRing F] {E : F[X]} (hE : E.Monic) (h : ℕ)
    (f : F[X]) (i : ℕ) :
    pvPowerRem E h f (i + 1) = (pvPowerRem E h f i ^ h) %ₘ E := by
  simp only [pvPowerRem, pow_succ, pow_mul]
  set g := f ^ h ^ i
  apply Polynomial.modByMonic_eq_of_dvd_sub hE
  have h1 : E ∣ g - g %ₘ E :=
    ⟨g /ₘ E, (eq_sub_of_add_eq' (Polynomial.modByMonic_add_div g E)).symm⟩
  exact dvd_trans h1 (sub_dvd_pow_sub_pow g (g %ₘ E) h)

/-- The `y`-th right neighbor of left vertex `f` in the Parvaresh–Vardy bipartite graph:
`(y, fun i ↦ (f ^ (h ^ i) %ₘ E).eval y)`. -/
@[expose] noncomputable def pvNeighbor {F : Type*} [CommRing F] (E : F[X]) (h m : ℕ)
    (f : PvLeft F E) (y : F) : F × (Fin m → F) :=
  (y, fun i ↦ (pvPowerRem E h f.1 i.val).eval y)

/-- For every left vertex `f`, the neighbor map `y ↦ pvNeighbor E h m f y` is injective. -/
theorem pvNeighbor_injective {F : Type*} [CommRing F] (E : F[X]) (h m : ℕ) (f : PvLeft F E) :
    Function.Injective (pvNeighbor E h m f) :=
  fun _ _ hxy ↦ congrArg Prod.fst hxy

/-- Bipartite adjacency relation of the Parvaresh–Vardy graph over `F` modulo `E`. -/
@[expose] def pvAdj {F : Type*} [CommRing F] (E : F[X]) (h m : ℕ)
    (f : PvLeft F E) (v : F × (Fin m → F)) : Prop :=
  pvNeighbor E h m f v.1 = v

/-- Decidability of `pvAdj E h m f v` over any commutative ring with decidable equality. -/
noncomputable instance instDecidablePvAdj {F : Type*} [CommRing F] [DecidableEq F] (E : F[X])
    (h m : ℕ) (f : PvLeft F E) (v : F × (Fin m → F)) : Decidable (pvAdj E h m f v) :=
  inferInstanceAs (Decidable (pvNeighbor E h m f v.1 = v))

/-- Adjacency in `pvAdj E h m` holds iff `v` is `pvNeighbor E h m f y` for some `y : F`. -/
theorem pvAdj_iff_exists {F : Type*} [CommRing F] {E : F[X]} {h m : ℕ}
    {f : PvLeft F E} {v : F × (Fin m → F)} :
    pvAdj E h m f v ↔ ∃ y : F, pvNeighbor E h m f y = v :=
  ⟨fun hv ↦ ⟨v.1, hv⟩, fun ⟨y, hy⟩ ↦ by
    change pvNeighbor E h m f v.1 = v
    rwa [← congrArg Prod.fst hy]⟩

private def baseHVal (h m : ℕ) (e : Fin m → Fin h) : ℕ :=
  ∑ i : Fin m, (e i).val * h ^ i.val

private def baseHInv (h m : ℕ) (hh : 0 < h) (k : ℕ) (i : Fin m) : Fin h :=
  ⟨(k / h ^ i.val) % h, Nat.mod_lt _ hh⟩

private theorem baseHVal_succ (h m : ℕ) (e : Fin (m + 1) → Fin h) :
    baseHVal h (m + 1) e = (e 0).val + h * baseHVal h m (fun i ↦ e i.succ) := by
  simp only [baseHVal, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ by ring

private theorem baseHVal_lt (h : ℕ) (hh : 0 < h) :
    ∀ (m : ℕ) (e : Fin m → Fin h), baseHVal h m e < h ^ m
  | 0, _ => by simp [baseHVal]
  | m + 1, e => by
    rw [baseHVal_succ, pow_succ']
    have h0 := (e 0).isLt
    have h1 : baseHVal h m (fun i ↦ e i.succ) + 1 ≤ h ^ m := baseHVal_lt h hh m _
    have hmul := Nat.mul_le_mul_left h h1
    linarith

private theorem baseHInv_baseHVal (h : ℕ) (hh : 0 < h) :
    ∀ (m : ℕ) (e : Fin m → Fin h), baseHInv h m hh (baseHVal h m e) = e
  | 0, e => funext fun i ↦ i.elim0
  | m + 1, e => by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · apply Fin.ext
      simp [baseHInv, baseHVal_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (e 0).isLt]
    · have hdiv : baseHVal h (m + 1) e / h = baseHVal h m (fun i ↦ e i.succ) := by
        rw [baseHVal_succ, Nat.add_mul_div_left _ _ hh,
          Nat.div_eq_zero_iff.2 (.inr (e 0).isLt), zero_add]
      have hstep : baseHInv h (m + 1) hh (baseHVal h (m + 1) e) j.succ =
          baseHInv h m hh (baseHVal h m (fun i ↦ e i.succ)) j := by
        apply Fin.ext
        simp only [baseHInv, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
      rw [hstep, baseHInv_baseHVal h hh m]

private theorem baseHVal_baseHInv (h : ℕ) (hh : 0 < h) :
    ∀ (m k : ℕ), k < h ^ m → baseHVal h m (baseHInv h m hh k) = k
  | 0, k, hk => by simp [baseHVal] at hk ⊢; omega
  | m + 1, k, hk => by
    rw [baseHVal_succ]
    have hsucc : (fun i : Fin m ↦ baseHInv h (m + 1) hh k i.succ) = baseHInv h m hh (k / h) := by
      funext i
      apply Fin.ext
      simp [baseHInv, pow_succ', Nat.div_div_eq_div_mul]
    have hk' : k / h < h ^ m := Nat.div_lt_of_lt_mul (by rwa [← pow_succ'])
    rw [hsucc, baseHVal_baseHInv h hh m (k / h) hk']
    simp only [baseHInv, Fin.val_zero, pow_zero, Nat.div_one]
    exact Nat.mod_add_div k h

private theorem baseHVal_injective (h m : ℕ) (hh : 0 < h) :
    Function.Injective (baseHVal h m) := fun e₁ e₂ h12 ↦ by
  rw [← baseHInv_baseHVal h hh m e₁, ← baseHInv_baseHVal h hh m e₂, h12]

private theorem eval_ne_zero_of_irreducible {F : Type*} [Field F] {E : F[X]}
    (hE_irr : Irreducible E) (hE_deg : 2 ≤ E.natDegree) (y : F) : E.eval y ≠ 0 := by
  intro hy
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.2 hy
  rcases hE_irr.isUnit_or_isUnit hq with hu | hu
  · have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at hdeg
    exact one_ne_zero hdeg
  · have hdeg : E.natDegree = 1 := by
      rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero y) hu.ne_zero,
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu]
    omega

private theorem natDegree_pvPowerRem_le {F : Type*} [Field F] {E : F[X]}
    (hE_mon : E.Monic) (hE_deg : 2 ≤ E.natDegree) (h : ℕ) (f : F[X]) (i : ℕ) :
    (pvPowerRem E h f i).natDegree ≤ E.natDegree - 1 := by
  dsimp [pvPowerRem]
  have hE1 : E ≠ 1 := fun h1 ↦ by rw [h1, natDegree_one] at hE_deg; omega
  have hlt := Polynomial.natDegree_modByMonic_lt (f ^ h ^ i) hE_mon hE1
  omega

private theorem exists_common_pow_div {F : Type*} [Field F] {ι : Type*} (univS : Finset ι)
    (hmem : ∀ e, e ∈ univS) {E : F[X]} (hE_mon : E.Monic) (hE_deg : 2 ≤ E.natDegree)
    {a : ℕ} (ha : 1 ≤ a) (cPoly : ι → F[X])
    (hdeg : ∀ e, (cPoly e).natDegree ≤ a - 1) (hne : ∃ e, cPoly e ≠ 0) :
    ∃ (r : ℕ) (dPoly : ι → F[X]) (e₀ : ι),
      (∀ e, cPoly e = E ^ r * dPoly e) ∧
      (∀ e, (dPoly e).natDegree ≤ a - 1) ∧
      ¬ (E ∣ dPoly e₀) := by
  classical
  have hpow_bound : ∀ (e : ι) (k : ℕ), cPoly e ≠ 0 → E ^ k ∣ cPoly e → k < a := by
    intro e k hce hdvd
    have hle := Polynomial.natDegree_le_of_dvd hdvd hce
    rw [hE_mon.natDegree_pow] at hle
    have hd := hdeg e
    have hk2 : k * 2 ≤ k * E.natDegree := Nat.mul_le_mul_left k hE_deg
    omega
  let valid (e : ι) : Finset ℕ := (Finset.range a).filter fun k ↦ E ^ k ∣ cPoly e
  have hvalid_ne : ∀ e, (valid e).Nonempty := fun e ↦
    ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, by simp⟩⟩
  let mult (e : ι) : ℕ := (valid e).max' (hvalid_ne e)
  have hmult_dvd : ∀ e, E ^ mult e ∣ cPoly e := fun e ↦
    (Finset.mem_filter.1 ((valid e).max'_mem (hvalid_ne e))).2
  have hmult_max : ∀ e, cPoly e ≠ 0 → ¬ (E ^ (mult e + 1) ∣ cPoly e) := by
    intro e hce hdvd
    have hlt : mult e + 1 < a := hpow_bound e (mult e + 1) hce hdvd
    have hle : mult e + 1 ≤ mult e :=
      (valid e).le_max' _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hdvd⟩)
    omega
  let nz : Finset ι := univS.filter fun e ↦ cPoly e ≠ 0
  obtain ⟨e₁, he₁⟩ := hne
  have hnz : nz.Nonempty := ⟨e₁, Finset.mem_filter.2 ⟨hmem e₁, he₁⟩⟩
  obtain ⟨e₀, he₀_mem, he₀_min⟩ := nz.exists_min_image mult hnz
  set r := mult e₀
  have hr_dvd : ∀ e, E ^ r ∣ cPoly e := fun e ↦ by
    by_cases hce : cPoly e = 0
    · simp [hce]
    · exact dvd_trans (pow_dvd_pow E (he₀_min e (Finset.mem_filter.2 ⟨hmem e, hce⟩)))
        (hmult_dvd e)
  let dPoly (e : ι) : F[X] := cPoly e /ₘ E ^ r
  have hfac : ∀ e, cPoly e = E ^ r * dPoly e := fun e ↦ by
    have hmod : cPoly e %ₘ E ^ r = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (hE_mon.pow r)).2 (hr_dvd e)
    have hdiv := Polynomial.modByMonic_add_div (cPoly e) (E ^ r)
    rw [hmod, zero_add] at hdiv
    exact hdiv.symm
  refine ⟨r, dPoly, e₀, hfac, fun e ↦ ?_, fun hdvd ↦ ?_⟩
  · rcases eq_or_ne (dPoly e) 0 with hd0 | hd0
    · simp [hd0]
    · have hc := hdeg e
      rw [hfac e, Polynomial.natDegree_mul (hE_mon.pow r).ne_zero hd0] at hc
      omega
  · apply hmult_max e₀ (Finset.mem_filter.1 he₀_mem).2
    rw [hfac e₀, pow_succ]
    exact mul_dvd_mul_left (E ^ r) hdvd

/-- **Parvaresh–Vardy lossless bipartite expansion**: for any finite field `F`, monic irreducible
`E : F[X]` of degree at least `2`, `h ≥ 2`, and `m ≥ 1` with
`m * (h - 1) * (E.natDegree - 1) < Fintype.card F`, the graph `pvAdj E h m` is an
`(h ^ m, |F|, |F| - m * (h - 1) * (E.natDegree - 1))`-expander. -/
theorem isBipartiteExpander_pvAdj {F : Type*} [Field F] [Fintype F]
    {E : F[X]} (hE_mon : E.Monic) (hE_irr : Irreducible E) (hE_deg : 2 ≤ E.natDegree)
    {h m : ℕ} (hh : 2 ≤ h) (hm : 1 ≤ m)
    (hbound : m * (h - 1) * (E.natDegree - 1) < Fintype.card F) :
    IsBipartiteExpander (pvAdj E h m) (h ^ m) (Fintype.card F)
      ((Fintype.card F - m * (h - 1) * (E.natDegree - 1) : ℕ) : ℝ) := by
  classical
  have _ := hm
  refine ⟨fun f ↦ ?_, fun W hW ↦ ?_⟩
  · have heq : bipartiteNeighbors (pvAdj E h m) f =
        Finset.univ.image (pvNeighbor E h m f) := by
      ext v; simp [pvAdj_iff_exists]
    rw [heq, Finset.card_image_of_injective _ (pvNeighbor_injective E h m f), Finset.card_univ]
  · rcases Nat.eq_zero_or_pos W.card with hW0 | hWpos
    · simp [hW0]
    set a := Fintype.card F - m * (h - 1) * (E.natDegree - 1)
    have ha : 1 ≤ a := by omega
    set S := bipartiteNeighborSet (pvAdj E h m) W
    suffices hnat : a * W.card ≤ S.card by exact_mod_cast hnat
    by_contra hlt
    push Not at hlt
    have hhpos : 0 < h := by omega
    let ExpSet := { e : Fin m → Fin h // baseHVal h m e < W.card }
    have hcard_exp : Fintype.card ExpSet = W.card := by
      have heq : ExpSet ≃ Fin W.card :=
        { toFun := fun e ↦ ⟨baseHVal h m e.1, e.2⟩
          invFun := fun k ↦ ⟨baseHInv h m hhpos k.val, by
            rw [baseHVal_baseHInv h hhpos m k.val (lt_of_lt_of_le k.isLt hW)]
            exact k.isLt⟩
          left_inv := fun e ↦ Subtype.ext (baseHInv_baseHVal h hhpos m e.1)
          right_inv := fun k ↦ Fin.ext
            (baseHVal_baseHInv h hhpos m k.val (lt_of_lt_of_le k.isLt hW)) }
      simpa using Fintype.card_congr heq
    let Idx := Fin a × ExpSet
    let evalBasis (idx : Idx) (v : F × (Fin m → F)) : F :=
      v.1 ^ idx.1.val * ∏ i : Fin m, (v.2 i) ^ (idx.2.1 i).val
    let Φ : (Idx → F) →ₗ[F] (S → F) :=
      { toFun := fun c v ↦ ∑ idx : Idx, c idx * evalBasis idx v.1
        map_add' := fun c₁ c₂ ↦ by funext v; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun r c ↦ by funext v; simp [mul_assoc, Finset.mul_sum] }
    have hnot_inj : ¬ Function.Injective Φ := by
      intro hinj
      have hfr := LinearMap.finrank_le_finrank_of_injective hinj
      rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin,
        hcard_exp, Fintype.card_coe] at hfr
      omega
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnot_inj
    push Not at hnot_inj
    obtain ⟨c, hc_ker, hc_ne⟩ := hnot_inj
    rw [LinearMap.mem_ker] at hc_ker
    let cPoly (e : ExpSet) : F[X] := ∑ j : Fin a, C (c (j, e)) * X ^ j.val
    have hcPoly_deg : ∀ e, (cPoly e).natDegree ≤ a - 1 := fun e ↦ by
      refine (natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      exact ⟨Nat.zero_le _, fun j _ ↦ (natDegree_C_mul_X_pow_le _ _).trans (by omega)⟩
    have hcPoly_ne : ∃ e, cPoly e ≠ 0 := by
      obtain ⟨⟨j₁, e₁⟩, hne₁⟩ := Function.ne_iff.1 hc_ne
      refine ⟨e₁, fun h0 ↦ hne₁ ?_⟩
      have hcoeff := congrArg (fun p : F[X] ↦ p.coeff j₁.val) h0
      simp only [cPoly, Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero,
        mul_ite, mul_one, mul_zero] at hcoeff
      rw [Finset.sum_eq_single j₁
        (fun j _ hne ↦ by have : j₁.val ≠ j.val := fun h ↦ hne (Fin.ext h.symm); simp [this])
        (fun hm' ↦ absurd (Finset.mem_univ _) hm')] at hcoeff
      simpa using hcoeff
    obtain ⟨r, dPoly, e₀, hfac, hdPoly_deg, hndvd⟩ :=
      exists_common_pow_div Finset.univ Finset.mem_univ hE_mon hE_deg ha cPoly hcPoly_deg hcPoly_ne
    let termPoly (f : PvLeft F E) (e : ExpSet) : F[X] :=
      ∏ i : Fin m, (pvPowerRem E h f.1 i.val) ^ (e.1 i).val
    let Pf (f : PvLeft F E) : F[X] := ∑ e : ExpSet, dPoly e * termPoly f e
    have hPf_zero : ∀ f ∈ W, Pf f = 0 := by
      intro f hf
      have hdeg_lt : (Pf f).natDegree < Fintype.card F := by
        refine ((natDegree_sum_le _ _).trans ?_).trans_lt
          (show a - 1 + m * (h - 1) * (E.natDegree - 1) < Fintype.card F by omega)
        rw [Finset.fold_max_le]
        refine ⟨Nat.zero_le _,
          fun e _ ↦ natDegree_mul_le.trans (Nat.add_le_add (hdPoly_deg e) ?_)⟩
        calc (termPoly f e).natDegree
            ≤ ∑ i : Fin m, ((pvPowerRem E h f.1 i.val) ^ (e.1 i).val).natDegree :=
              Polynomial.natDegree_prod_le _ _
          _ ≤ ∑ _i : Fin m, (h - 1) * (E.natDegree - 1) := by
              refine Finset.sum_le_sum fun i _ ↦ Polynomial.natDegree_pow_le.trans ?_
              have hei : (e.1 i).val ≤ h - 1 := by have := (e.1 i).isLt; omega
              exact Nat.mul_le_mul hei (natDegree_pvPowerRem_le hE_mon hE_deg h f.1 i.val)
          _ = m * (h - 1) * (E.natDegree - 1) := by simp [mul_assoc]
      have heval_zero : ∀ y : F, (Pf f).eval y = 0 := by
        intro y
        have hvS : pvNeighbor E h m f y ∈ S := mem_bipartiteNeighborSet.2 ⟨f, hf, rfl⟩
        have hΦ : (∑ j : Fin a, ∑ e : ExpSet,
            c (j, e) * evalBasis (j, e) (pvNeighbor E h m f y)) = 0 := by
          have h0 : (∑ idx : Fin a × ExpSet,
              c idx * evalBasis idx (pvNeighbor E h m f y)) = 0 :=
            congrFun hc_ker ⟨pvNeighbor E h m f y, hvS⟩
          rwa [Fintype.sum_prod_type] at h0
        have hrewrite :
            (∑ j : Fin a, ∑ e : ExpSet, c (j, e) * evalBasis (j, e) (pvNeighbor E h m f y)) =
              E.eval y ^ r * (Pf f).eval y := by
          have hPf_ev : (Pf f).eval y = ∑ e : ExpSet, (dPoly e).eval y * (termPoly f e).eval y := by
            dsimp only [Pf]; rw [← Polynomial.coe_evalRingHom, map_sum]; simp
          rw [Finset.sum_comm, hPf_ev, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ ↦ ?_
          have hce : (cPoly e).eval y = ∑ j : Fin a, c (j, e) * y ^ j.val := by
            dsimp only [cPoly]; rw [← Polynomial.coe_evalRingHom, map_sum]; simp
          have hte : (termPoly f e).eval y =
              ∏ i : Fin m, ((pvPowerRem E h f.1 i.val).eval y) ^ (e.1 i).val := by
            simp [termPoly, Polynomial.eval_prod]
          have hfe : (cPoly e).eval y = E.eval y ^ r * (dPoly e).eval y := by
            rw [hfac e, Polynomial.eval_mul, Polynomial.eval_pow]
          calc (∑ j : Fin a, c (j, e) * evalBasis (j, e) (pvNeighbor E h m f y))
              = (∑ j : Fin a, c (j, e) * y ^ j.val) *
                  ∏ i : Fin m, ((pvPowerRem E h f.1 i.val).eval y) ^ (e.1 i).val := by
                simp only [evalBasis, pvNeighbor, Finset.sum_mul, mul_assoc]
            _ = E.eval y ^ r * ((dPoly e).eval y * (termPoly f e).eval y) := by
                rw [← hce, ← hte, hfe, mul_assoc]
        rw [hrewrite] at hΦ
        exact (mul_eq_zero.1 hΦ).resolve_left
          (pow_ne_zero r (eval_ne_zero_of_irreducible hE_irr hE_deg y))
      by_contra hne0
      have hsub : (Finset.univ : Finset F).val ≤ (Pf f).roots := by
        rw [Multiset.le_iff_count]
        intro y
        rw [Multiset.count_eq_of_nodup Finset.univ.nodup]
        simp only [Finset.mem_val, Finset.mem_univ, ↓reduceIte]
        exact Nat.succ_le_of_lt
          (Multiset.count_pos.2 ((Polynomial.mem_roots hne0).2 (heval_zero y)))
      have hcards : Fintype.card F ≤ (Pf f).natDegree :=
        (Multiset.card_le_card hsub).trans (Polynomial.card_roots' (Pf f))
      omega
    have : Fact (Irreducible E) := ⟨hE_irr⟩
    let R : (AdjoinRoot E)[X] :=
      ∑ e : ExpSet, C (AdjoinRoot.mk E (dPoly e)) * X ^ baseHVal h m e.1
    have hR_ne : R ≠ 0 := by
      intro h0
      have hcoeff := congrArg (fun p : (AdjoinRoot E)[X] ↦ p.coeff (baseHVal h m e₀.1)) h0
      simp only [R, Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero,
        mul_ite, mul_one, mul_zero] at hcoeff
      rw [Finset.sum_eq_single e₀
        (fun e _ hne ↦ by
          have : baseHVal h m e₀.1 ≠ baseHVal h m e.1 := fun heq ↦
            hne (Subtype.ext (baseHVal_injective h m hhpos heq.symm))
          simp [this])
        (fun hm' ↦ absurd (Finset.mem_univ _) hm')] at hcoeff
      simp only [↓reduceIte] at hcoeff
      exact hndvd (AdjoinRoot.mk_eq_zero.1 hcoeff)
    have hR_deg : R.natDegree < W.card := by
      refine (natDegree_sum_le _ _).trans_lt ?_
      rw [Finset.fold_max_lt]
      exact ⟨hWpos, fun e _ ↦ (natDegree_C_mul_X_pow_le _ _).trans_lt e.2⟩
    have hmk_rem : ∀ (f : F[X]) (i : ℕ),
        AdjoinRoot.mk E (pvPowerRem E h f i) = AdjoinRoot.mk E f ^ h ^ i := fun f i ↦ by
      have hmk := congrArg (AdjoinRoot.mk E) (Polynomial.modByMonic_add_div (f ^ h ^ i) E)
      simpa only [pvPowerRem, map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero,
        map_pow] using hmk
    have hR_root : ∀ f ∈ W, R.eval (AdjoinRoot.mk E f.1) = 0 := fun f hf ↦ by
      have h0 := congrArg (AdjoinRoot.mk E) (hPf_zero f hf)
      simp only [Pf, map_zero, map_sum, map_mul] at h0
      have hRev : R.eval (AdjoinRoot.mk E f.1) =
          ∑ e : ExpSet, AdjoinRoot.mk E (dPoly e) * AdjoinRoot.mk E f.1 ^ baseHVal h m e.1 := by
        dsimp only [R]; rw [← Polynomial.coe_evalRingHom, map_sum]; simp
      rw [hRev, ← h0]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      congr 1
      simp only [termPoly, map_prod, map_pow, hmk_rem, ← pow_mul]
      have hcomm : (∑ x : Fin m, h ^ x.val * (e.1 x).val) = baseHVal h m e.1 :=
        Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
      rw [← hcomm, Finset.prod_pow_eq_pow_sum]
    have hmk_inj : Function.Injective (fun f : PvLeft F E ↦ AdjoinRoot.mk E f.1) := by
      intro f₁ f₂ h12
      dsimp only at h12
      apply Subtype.ext
      have hdvd : E ∣ f₁.1 - f₂.1 :=
        AdjoinRoot.mk_eq_zero.1 (by rw [map_sub, h12, sub_self])
      by_contra hne
      have hle := Polynomial.natDegree_le_of_dvd hdvd (sub_ne_zero.2 hne)
      have hlt' := (Polynomial.natDegree_sub_le f₁.1 f₂.1).trans_lt (max_lt f₁.2 f₂.2)
      omega
    let rootsSet : Finset (AdjoinRoot E) := W.image fun f ↦ AdjoinRoot.mk E f.1
    have hsub : rootsSet.val ≤ R.roots := by
      rw [Multiset.le_iff_count]
      intro α
      rw [Multiset.count_eq_of_nodup rootsSet.nodup]
      by_cases hα : α ∈ rootsSet
      · simp only [Finset.mem_val, hα, ↓reduceIte]
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hα
        exact Nat.succ_le_of_lt
          (Multiset.count_pos.2 ((Polynomial.mem_roots hR_ne).2 (hR_root f hf)))
      · simp [hα]
    have hcard_roots : W.card ≤ R.natDegree :=
      calc W.card = rootsSet.card := (Finset.card_image_of_injective W hmk_inj).symm
        _ ≤ R.roots.card := Multiset.card_le_card hsub
        _ ≤ R.natDegree := Polynomial.card_roots' R
    omega

/-- Compatibility bridge: `pvAdj E h m` satisfies `Cslib.Bipartite.IsVertexExpander`. -/
theorem isVertexExpander_pvAdj {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {E : F[X]} {h m : ℕ}
    (hE_mon : E.Monic) (hE_irr : Irreducible E) (hE_deg : 2 ≤ E.natDegree)
    (hh : 2 ≤ h) (hm : 1 ≤ m)
    (hbound : m * (h - 1) * (E.natDegree - 1) < Fintype.card F) :
    Cslib.Bipartite.IsVertexExpander (pvAdj E h m) (h ^ m)
      ((Fintype.card F - m * (h - 1) * (E.natDegree - 1) : ℕ) : ℝ) := by
  have hexp := isBipartiteExpander_pvAdj hE_mon hE_irr hE_deg hh hm hbound
  intro S hS
  have heq : Cslib.Bipartite.neighbors (pvAdj E h m) S =
      bipartiteNeighborSet (pvAdj E h m) S := by ext v; simp
  rw [heq]
  exact hexp.2 S hS

/-- Pulling back a bipartite expander along a left injection `ιL` and a right equivalence `eR`
preserves expansion (and allows tightening `r' ≤ r` and `c' ≤ c`). -/
theorem isBipartiteExpander_pullback {U V U' V' : Type*} [Fintype V] [Fintype V']
    {adj : U → V → Prop} {r r' k : ℕ} {c c' : ℝ}
    (hexp : IsBipartiteExpander adj r k c)
    (ιL : U' → U) (hιL : Function.Injective ιL) (eR : V ≃ V')
    (hr : r' ≤ r) (hc : c' ≤ c) :
    IsBipartiteExpander (fun u' v' ↦ adj (ιL u') (eR.symm v')) r' k c' := by
  classical
  refine ⟨fun u' ↦ ?_, fun W' hW' ↦ ?_⟩
  · have heq : bipartiteNeighbors (fun u' v' ↦ adj (ιL u') (eR.symm v')) u' =
        (bipartiteNeighbors adj (ιL u')).image eR := by
      ext v'
      simp only [mem_bipartiteNeighbors, Finset.mem_image]
      exact ⟨fun h ↦ ⟨eR.symm v', h, eR.apply_symm_apply v'⟩,
        fun ⟨v, hv, hvv'⟩ ↦ by subst hvv'; simpa using hv⟩
    rw [heq, Finset.card_image_of_injective _ eR.injective, hexp.1 (ιL u')]
  · have heq : bipartiteNeighborSet (fun u' v' ↦ adj (ιL u') (eR.symm v')) W' =
        (bipartiteNeighborSet adj (W'.image ιL)).image eR := by
      ext v'
      simp only [mem_bipartiteNeighborSet, Finset.mem_image]
      exact ⟨fun ⟨u', hu', hadj⟩ ↦
          ⟨eR.symm v', ⟨ιL u', ⟨u', hu', rfl⟩, hadj⟩, eR.apply_symm_apply v'⟩,
        fun ⟨v, ⟨_, ⟨u', hu', rfl⟩, hadj⟩, hvv'⟩ ↦ by
          subst hvv'; exact ⟨u', hu', by simpa using hadj⟩⟩
    have hcardW : (W'.image ιL).card = W'.card := Finset.card_image_of_injective W' hιL
    rw [heq, Finset.card_image_of_injective _ eR.injective]
    calc c' * (W'.card : ℝ)
        ≤ c * (W'.card : ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ = c * ((W'.image ιL).card : ℝ) := by rw [hcardW]
      _ ≤ ((bipartiteNeighborSet adj (W'.image ιL)).card : ℝ) :=
          hexp.2 _ (hcardW.le.trans (hW'.trans hr))

end AlgebraicExpansion

/-! ### Little-Endian Bit Words and Explicit Bipartite Graph Families -/

section ExplicitFamilies

open Turing.MultiTapeTM ComputableInPolyTime Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- Little-endian natural number value of a list of bits (`bit 0` is least significant). -/
@[expose] def lsbValue (word : List Bool) : ℕ :=
  Cslib.BitString.binaryValue word.reverse

@[simp]
theorem lsbValue_nil : lsbValue [] = 0 := rfl

@[simp]
theorem lsbValue_cons (b : Bool) (l : List Bool) :
    lsbValue (b :: l) = 2 * lsbValue l + b.toNat := by
  rw [lsbValue, List.reverse_cons, Cslib.BitString.binaryValue_snoc, ← lsbValue]

/-- `lsbValue l` is strictly less than `2 ^ l.length`. -/
theorem lsbValue_lt_two_pow (l : List Bool) : lsbValue l < 2 ^ l.length := by
  simpa [lsbValue] using Cslib.BitString.binaryValue_lt_two_pow l.reverse

/-- The `i`-th binary bit of `lsbValue l` is `l.getD i false`. -/
theorem testBit_lsbValue (l : List Bool) (i : ℕ) :
    (lsbValue l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero => cases b <;> simp [Nat.testBit_zero]
    | succ i =>
      rw [lsbValue_cons, Nat.testBit_succ]
      have hdiv : (2 * lsbValue l + b.toNat) / 2 = lsbValue l := by
        cases b <;> dsimp [Bool.toNat] <;> omega
      rw [hdiv, ih i]
      simp

/-- Taking the low `w` bits of `n` and decoding recovers `n % 2 ^ w`. -/
theorem lsbValue_lowBits (w n : ℕ) :
    lsbValue (Cslib.BitString.lowBits w n) = n % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lsbValue, Nat.testBit_mod_two_pow]
  by_cases hi : i < w
  · simp [Cslib.BitString.lowBits, List.getD_eq_getElem?_getD, hi]
  · have hlen : (Cslib.BitString.lowBits w n).length ≤ i := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
    simp [hi]

/-- When `n < 2 ^ w`, `lsbValue (lowBits w n) = n`. -/
theorem lsbValue_lowBits_of_lt {w n : ℕ} (hn : n < 2 ^ w) :
    lsbValue (Cslib.BitString.lowBits w n) = n := by
  rw [lsbValue_lowBits, Nat.mod_eq_of_lt hn]

/-- Encoding `lsbValue l` at width `l.length` recovers `l`. -/
theorem lowBits_lsbValue (l : List Bool) :
    Cslib.BitString.lowBits l.length (lsbValue l) = l := by
  refine List.ext_getElem (by simp) fun i _ h₂ ↦ ?_
  have htb := testBit_lsbValue l i
  simp only [Cslib.BitString.lowBits, List.getElem_map, List.getElem_range]
  simpa [List.getD_eq_getElem?_getD, h₂] using htb

/-- `lsbValue` is injective on words of equal length. -/
theorem lsbValue_injective_of_length {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hval : lsbValue l₁ = lsbValue l₂) : l₁ = l₂ := by
  rw [← lowBits_lsbValue l₁, ← lowBits_lsbValue l₂, hlen, hval]

/-- Decoding `n.bits` in little-endian recovers `n`. -/
@[simp]
theorem lsbValue_bits (n : ℕ) : lsbValue n.bits = n :=
  Cslib.BitString.binaryValue_reverse_bits n

/-- `lsbValue` is computable in polynomial time from `encBits` to `encNat`. -/
theorem computableInPolyTime_lsbValue :
    ComputableInPolyTime lsbValue encBits encNat :=
  bitsBinaryValue.comp (listToBits.comp ((listReverse encBool).comp bitsToList))

/-- A family of left-regular bipartite graphs `{G_n = (U_n, V_n, E_n)}_{n : ℕ}` whose neighbor map
`(n, u, j) ↦ v` is computable in polynomial time on binary encodings by a multi-tape Turing
machine. When `n ≤ leftSize n`, the runtime is polynomial in `log |U_n|`. -/
structure ExplicitBipartiteFamily where
  /-- Number of left vertices `|U_n|` at index `n`. -/
  leftSize : ℕ → ℕ
  /-- Number of right vertices `|V_n|` at index `n`. -/
  rightSize : ℕ → ℕ
  /-- Left degree `d_n` at index `n`. -/
  leftDeg : ℕ → ℕ
  /-- Neighbor function returning the `j`-th right neighbor of left vertex `u` in `G_n`. -/
  neighbor : ℕ → ℕ → ℕ → ℕ
  /-- Every neighbor index lies strictly below `rightSize n`. -/
  neighbor_lt : ∀ n u j, u < leftSize n → j < leftDeg n → neighbor n u j < rightSize n
  /-- For each left vertex `u < leftSize n`, its `leftDeg n` neighbors are pairwise distinct. -/
  neighbor_injOn : ∀ n u, u < leftSize n → Set.InjOn (neighbor n u) { j | j < leftDeg n }
  /-- Polynomial-time computability of `(n, u, j) ↦ neighbor n u j` in binary. -/
  polyTime : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ ↦ neighbor p.1 p.2.1 p.2.2) encNat3 encNat

/-- Typed neighbor map `Fin (G.leftSize n) → Fin (G.leftDeg n) → Fin (G.rightSize n)`. -/
@[expose] def ExplicitBipartiteFamily.neighborFin (G : ExplicitBipartiteFamily) (n : ℕ)
    (u : Fin (G.leftSize n)) (j : Fin (G.leftDeg n)) : Fin (G.rightSize n) :=
  ⟨G.neighbor n u.val j.val, G.neighbor_lt n u.val j.val u.isLt j.isLt⟩

/-- Underlying natural-number index of `G.neighborFin n u j`. -/
@[simp] theorem ExplicitBipartiteFamily.val_neighborFin (G : ExplicitBipartiteFamily) (n : ℕ)
    (u : Fin (G.leftSize n)) (j : Fin (G.leftDeg n)) :
    (G.neighborFin n u j).val = G.neighbor n u.val j.val :=
  rfl

/-- Adjacency relation of the `n`-th graph in an `ExplicitBipartiteFamily`. -/
@[expose] def ExplicitBipartiteFamily.adj (G : ExplicitBipartiteFamily) (n : ℕ)
    (u : Fin (G.leftSize n)) (v : Fin (G.rightSize n)) : Prop :=
  ∃ j : Fin (G.leftDeg n), G.neighborFin n u j = v

/-- Characterization of `G.adj n u v` via edge labels and raw neighbor indices. -/
theorem ExplicitBipartiteFamily.adj_iff (G : ExplicitBipartiteFamily) (n : ℕ)
    (u : Fin (G.leftSize n)) (v : Fin (G.rightSize n)) :
    G.adj n u v ↔ ∃ j : Fin (G.leftDeg n), G.neighbor n u.val j.val = v.val := by
  simp [ExplicitBipartiteFamily.adj, Fin.ext_iff]

/-- Every left vertex of `G.adj n` has exact degree `G.leftDeg n`. -/
theorem ExplicitBipartiteFamily.card_neighbors (G : ExplicitBipartiteFamily) (n : ℕ)
    (u : Fin (G.leftSize n)) :
    (bipartiteNeighbors (G.adj n) u).card = G.leftDeg n := by
  classical
  have hinj : Function.Injective (G.neighborFin n u) := fun j₁ j₂ h ↦
    Fin.ext (G.neighbor_injOn n u.val u.isLt j₁.isLt j₂.isLt (congrArg Fin.val h))
  have heq : bipartiteNeighbors (G.adj n) u = Finset.univ.image (G.neighborFin n u) := by
    ext v; simp [ExplicitBipartiteFamily.adj]
  rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_fin]

/-- Circuit extraction from a polynomial-time Boolean predicate on `encPair encBits encP`: fixing
the parameter `p : π` and input width `w : ℕ` yields a single-output De Morgan circuit of size
polynomial in `w + (encP p).length`. -/
theorem exists_circuit_family_of_polyTime_bits {π : Type} {encP : π ↪ List Bool}
    {f : List Bool × π → Bool}
    (hf : ComputableInPolyTime f (encPair encBits encP) encBool) :
    ∃ C K : ℕ, ∀ (w : ℕ) (p : π),
      ∃ c : Circuit Boolean.signature w 1,
        c.size ≤ C * (w + (encP p).length + 2) ^ K ∧
        ∀ x : BitString w, c.eval Boolean.interpretation x 0 = f (List.ofFn x, p) := by
  obtain ⟨t, _, ht, -, htm⟩ := hf
  obtain ⟨L, C₀, hL, hC₀⟩ := exists_complexity_slice_le_of_computableInTime htm
  have hpoly : PolynomiallyBounded fun N ↦ C₀ * (N + t N + 1) ^ 2 + 4 := by fun_prop
  obtain ⟨C₁, K, hbound⟩ := polynomiallyBounded_iff_le.1 hpoly
  refine ⟨C₁ * 3 ^ K, K, fun w p ↦ ?_⟩
  let rBits : List Bool := encP p
  set P := rBits.length
  let rFn : Fin P → Bool := fun i ↦ rBits[i.val]
  have hr : List.ofFn rFn = rBits :=
    List.ext_getElem (by simp [P]) fun i _ _ ↦ by simp [rFn]
  let g : BitString w → Bool := fun x ↦ framedSlice L w P (substitute (appendInputs rFn) x)
  have hcomp : complexity Boolean.interpretation (single g) ≤
      C₀ * (2 * w + 1 + P + t (2 * w + 1 + P) + 1) ^ 2 + 4 :=
    calc complexity Boolean.interpretation (single g)
        ≤ complexity Boolean.interpretation (single (framedSlice L w P)) + 2 :=
          complexity_substitute_le (appendInputs rFn) (framedSlice L w P)
      _ ≤ complexity Boolean.interpretation (single (L.slice (2 * w + 1 + P))) + 2 + 2 :=
          Nat.add_le_add_right (complexity_substitute_le (frameWiring w P) _) 2
      _ ≤ C₀ * (2 * w + 1 + P + t (2 * w + 1 + P) + 1) ^ 2 + 4 := by
          have := hC₀ (2 * w + 1 + P); omega
  obtain ⟨c, hc_eval, hc_size⟩ :=
    exists_computes_size_eq_complexity (I := Boolean.interpretation) (f := single g)
  refine ⟨c, ?_, fun x ↦ ?_⟩
  · rw [hc_size]
    refine hcomp.trans ((hbound (2 * w + 1 + P)).trans ?_)
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_left (by omega) K)
  · rw [congrFun (hc_eval x) 0]
    dsimp [single, g]
    rw [Bool.eq_iff_iff, substitute_appendInputs, framedSlice_append_eq_true, hr,
      hL (List.ofFn x, p), encPair_apply, encBits_apply]

private theorem length_encNat_le (n : ℕ) : (encNat n).length ≤ Nat.clog 2 (n + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  rcases eq_or_ne n 0 with rfl | _
  · simp
  · rw [Nat.size_le]
    exact Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) (n + 1))

private theorem clog_two_le_self (w : ℕ) : Nat.clog 2 w ≤ w := by
  rcases w with _ | w'
  · simp
  · exact ((Nat.clog_le_iff_le_pow (by decide)).2 (le_of_lt Nat.lt_two_pow_self))

private theorem testBit_eq_shiftRight (v b : ℕ) :
    v.testBit b = decide (0 < ((v >>> b) &&& 1)) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ b) with h | h <;> simp [h]

/-- **Polynomial-size neighbor circuits for explicit bipartite graph families**: every
`G : ExplicitBipartiteFamily` admits uniform constants `C K : ℕ` such that at each index `n`,
there is a De Morgan circuit on `wU = Nat.clog 2 (G.leftSize n)` inputs with `G.leftDeg n * wV`
outputs (`wV = Nat.clog 2 (G.rightSize n)`) computing all `wV` binary bits of every neighbor of
`u`, of size polynomial in `wU + log(n + 1) + log(d_n + 1) + wV`. -/
theorem exists_neighbor_circuit_of_explicit (G : ExplicitBipartiteFamily) :
    ∃ C K : ℕ, ∀ n : ℕ,
      let wU := Nat.clog 2 (G.leftSize n)
      let wV := Nat.clog 2 (G.rightSize n)
      ∃ c : Circuit Boolean.signature wU (G.leftDeg n * wV),
        c.size ≤ C * G.leftDeg n * wV *
          (wU + Nat.clog 2 (n + 1) + Nat.clog 2 (G.leftDeg n + 1) + wV + 2) ^ K ∧
        ∀ (x : BitString wU) (j : Fin (G.leftDeg n)) (b : Fin wV)
          (k : Fin (G.leftDeg n * wV)),
          k.val = j.val * wV + b.val →
          c.eval Boolean.interpretation x k =
            (G.neighbor n (lsbValue (List.ofFn x)) j.val).testBit b.val := by
  let pred : List Bool × (ℕ × ℕ × ℕ) → Bool :=
    fun q ↦ decide (0 < ((G.neighbor q.2.1 (lsbValue q.1) q.2.2.1 >>> q.2.2.2) &&& 1))
  have hpred : ComputableInPolyTime pred (encPair encBits encNat3) encBool := by
    have hx := computableInPolyTime_lsbValue.comp (fst encBits encNat3)
    have hp := snd encBits encNat3
    have hn := (fst encNat (encPair encNat encNat)).comp hp
    have hj := (fst encNat encNat).comp ((snd encNat (encPair encNat encNat)).comp hp)
    have hb := (snd encNat encNat).comp ((snd encNat (encPair encNat encNat)).comp hp)
    have hneigh := G.polyTime.comp (hn.prod (hx.prod hj))
    exact binary_pos.comp (binary_and' (binary_shiftRight' hneigh hb) (const 1))
  obtain ⟨C₀, K, hcirc⟩ := exists_circuit_family_of_polyTime_bits hpred
  refine ⟨C₀ * 4 ^ K, K, fun n ↦ ?_⟩
  set wU := Nat.clog 2 (G.leftSize n)
  set wV := Nat.clog 2 (G.rightSize n)
  rcases Nat.eq_zero_or_pos (G.leftDeg n * wV) with hM | hMpos
  · refine ⟨Circuit.pi fun k : Fin (G.leftDeg n * wV) ↦ Fin.elim0 (hM ▸ k), ?_,
      fun _ _ _ k _ ↦ Fin.elim0 (hM ▸ k)⟩
    have hpi : (Circuit.pi fun k : Fin (G.leftDeg n * wV) ↦
        (Fin.elim0 (hM ▸ k) : Circuit Boolean.signature wU 1)).size = 0 := by
      have hsz : (Circuit.pi fun k : Fin (G.leftDeg n * wV) ↦
          (Fin.elim0 (hM ▸ k) : Circuit Boolean.signature wU 1)).size =
          ∑ k : Fin (G.leftDeg n * wV),
            (Fin.elim0 (hM ▸ k) : Circuit Boolean.signature wU 1).size := by simp
      rw [hsz]
      exact Finset.sum_eq_zero fun k _ ↦ Fin.elim0 (hM ▸ k)
    rw [hpi]
    exact Nat.zero_le _
  have hwV_pos : 0 < wV := Nat.pos_of_mul_pos_left hMpos
  let bitC (k : Fin (G.leftDeg n * wV)) : Circuit Boolean.signature wU 1 :=
    (hcirc wU (n, k.val / wV, k.val % wV)).choose
  let bigC : Circuit Boolean.signature wU (G.leftDeg n * wV) := Circuit.pi bitC
  refine ⟨bigC, ?_, fun x j b k hk ↦ ?_⟩
  · have hsize_each : ∀ k : Fin (G.leftDeg n * wV), (bitC k).size ≤
        C₀ * 4 ^ K *
          (wU + Nat.clog 2 (n + 1) + Nat.clog 2 (G.leftDeg n + 1) + wV + 2) ^ K := by
      intro k
      have hk0 := (hcirc wU (n, k.val / wV, k.val % wV)).choose_spec.1
      have hj_lt : k.val / wV < G.leftDeg n :=
        Nat.div_lt_of_lt_mul (by linarith [k.isLt])
      have hb_lt : k.val % wV < wV := Nat.mod_lt _ hwV_pos
      have hlen_n := length_encNat_le n
      have hlen_j : (encNat (k.val / wV)).length ≤ Nat.clog 2 (G.leftDeg n + 1) :=
        (length_encNat_le _).trans (Nat.clog_mono_right 2 (by omega))
      have hlen_b : (encNat (k.val % wV)).length ≤ wV :=
        (length_encNat_le _).trans ((Nat.clog_mono_right 2 hb_lt).trans (clog_two_le_self wV))
      have hlenP : (encNat3 (n, k.val / wV, k.val % wV)).length ≤
          2 * Nat.clog 2 (n + 1) + 2 * Nat.clog 2 (G.leftDeg n + 1) + wV + 2 := by
        simp only [encNat3, length_encPair]; omega
      refine hk0.trans ?_
      rw [mul_assoc, ← mul_pow]
      exact Nat.mul_le_mul_left C₀ (Nat.pow_le_pow_left (by omega) K)
    have hpi : bigC.size = ∑ k : Fin (G.leftDeg n * wV), (bitC k).size := by simp [bigC]
    rw [hpi]
    calc ∑ k : Fin (G.leftDeg n * wV), (bitC k).size
        ≤ ∑ _k : Fin (G.leftDeg n * wV), C₀ * 4 ^ K *
            (wU + Nat.clog 2 (n + 1) + Nat.clog 2 (G.leftDeg n + 1) + wV + 2) ^ K :=
          Finset.sum_le_sum fun k _ ↦ hsize_each k
      _ = C₀ * 4 ^ K * G.leftDeg n * wV *
            (wU + Nat.clog 2 (n + 1) + Nat.clog 2 (G.leftDeg n + 1) + wV + 2) ^ K := by
          simp; ring
  · have hdiv : k.val / wV = j.val := by
      rw [hk, mul_comm j.val wV, Nat.mul_add_div hwV_pos,
        Nat.div_eq_zero_iff.2 (.inr b.isLt), add_zero]
    have hmod : k.val % wV = b.val := by
      rw [hk, mul_comm j.val wV, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
    have hev : bigC.eval Boolean.interpretation x k =
        (bitC k).eval Boolean.interpretation x 0 := by simp [bigC]
    rw [hev, (hcirc wU (n, k.val / wV, k.val % wV)).choose_spec.2 x]
    dsimp [pred]
    rw [hdiv, hmod, ← testBit_eq_shiftRight]

end ExplicitFamilies

end CslibFrontier.ParvareshVardy
