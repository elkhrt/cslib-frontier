module
/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.Basic
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
import CslibFrontier.Foundations.Data.Finsupp.OddSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Static Sum-of-Squares Proofs, Boolean Multilinearization, and Substitutions

This module develops static real Sum-of-Squares (SoS) proofs and refutations together with their
degree and monomial-size complexity measures, Boolean hypercube multilinearization, and closure
under variable and polynomial substitutions, under standard Lean constraints.

## Main definitions

* `CslibFrontier.ProofComplexity.boolPoint`: `{0, 1}` evaluation point of `a : σ → Bool`.
* `CslibFrontier.ProofComplexity.boolAxiom`: Boolean equation polynomial `X i ^ 2 - X i`.
* `CslibFrontier.ProofComplexity.multilinExp`, `CslibFrontier.ProofComplexity.multilin`: exponent
  and
  polynomial multilinearization modulo `{X i ^ 2 - X i}`.
* `CslibFrontier.ProofComplexity.SosProof`, `CslibFrontier.ProofComplexity.SosRefutation`: static
  real
  Sum-of-Squares proofs and refutations, with `.degree` and `.size` (total monomial count).
* `CslibFrontier.ProofComplexity.SosDerivableInDegree`,
  `CslibFrontier.ProofComplexity.SosRefutableInDegree`,
  `CslibFrontier.ProofComplexity.SosRefutableInSize`: bounded-degree and bounded-size SoS
  predicates.
* `CslibFrontier.ProofComplexity.sosRefuteDeg`, `CslibFrontier.ProofComplexity.sosRefuteSize`:
  minimum SoS
  refutation degree and monomial size in `ℕ∞`.
* `CslibFrontier.ProofComplexity.AtomSubst`, `CslibFrontier.ProofComplexity.restrictPolySubst`:
  atomic
  (`0`, `1`, variable) and bounded-degree polynomial substitutions on equation systems.
* `CslibFrontier.ProofComplexity.Lit`, `CslibFrontier.ProofComplexity.twinBoolAxioms`,
  `CslibFrontier.ProofComplexity.TwinVarSubst`: twin-literal Boolean variables `(x_v, x̄_v)` with
  Boolean and complementation constraints and complement-respecting variable substitutions.

## Main results

* `CslibFrontier.ProofComplexity.eq_multilin_add_sum_mul_boolAxiom`: degree-bounded decomposition of
  any polynomial into `multilin p + ∑ i, q i * (X i ^ 2 - X i)`.
* `CslibFrontier.ProofComplexity.eq_sum_mul_boolAxiom_of_eval_eq_zero`: any polynomial of total
  degree
  at most `d` vanishing on `{0, 1}^σ` is a sum `∑ i, q i * (X i ^ 2 - X i)` with every summand of
  total degree at most `d`.
* `CslibFrontier.ProofComplexity.sosRefutableInDegree_iff_cslib`: equivalence between unweighted
  real
  `SosRefutableInDegree` and `Cslib.Logic.PL.SOS.RefutableInDegree`.
* `CslibFrontier.ProofComplexity.sosRefuteDeg_atomSubst_le`,
  `CslibFrontier.ProofComplexity.sosRefuteSize_atomSubst_le`,
  `CslibFrontier.ProofComplexity.twinVarSubst_refuteDeg_and_size_le`: variable substitutions do not
  increase SoS refutation degree or monomial size.
* `CslibFrontier.ProofComplexity.SosRefutableInDegree.polySubst`: a polynomial substitution of
  degree
  at most `k` multiplies SoS refutation degree by at most `k`.
-/

public section

namespace CslibFrontier.ProofComplexity

open MvPolynomial Finset
open Cslib.Logic.PL

/-! ### Boolean Hypercube Ideal and Degree-Preserving Multilinearization -/

section BooleanIdeal

/-- The `{0, 1}`-valued point in `σ → R` corresponding to a Boolean assignment `a : σ → Bool`. -/
@[expose]
def boolPoint (R : Type*) [Zero R] [One R] {σ : Type*} (a : σ → Bool) : σ → R :=
  fun i ↦ if a i then 1 else 0

/-- The Boolean polynomial `X i ^ 2 - X i` enforcing `x_i ∈ {0, 1}`. -/
@[expose]
noncomputable def boolAxiom (R : Type*) [CommRing R] {σ : Type*} (i : σ) : MvPolynomial σ R :=
  X i ^ 2 - X i

variable {σ R : Type*} [CommRing R]

@[simp] theorem boolPoint_true (a : σ → Bool) {i : σ} (h : a i = true) :
    boolPoint R a i = 1 := by simp [boolPoint, h]

@[simp] theorem boolPoint_false (a : σ → Bool) {i : σ} (h : a i = false) :
    boolPoint R a i = 0 := by simp [boolPoint, h]

/-- Explicit `0`/`1` value of `boolPoint R a i`. -/
theorem boolPoint_eq_ite (a : σ → Bool) (i : σ) : boolPoint R a i = if a i then 1 else 0 := rfl

/-- Algebraic expression `X i ^ 2 - X i` of `boolAxiom R i`. -/
theorem boolAxiom_eq_sub (i : σ) : boolAxiom R i = X i ^ 2 - X i := rfl

/-- Evaluation of `boolAxiom R i` at an arbitrary point `x : σ → R`. -/
@[simp] theorem eval_boolAxiom (x : σ → R) (i : σ) : eval x (boolAxiom R i) = x i ^ 2 - x i := by
  simp [boolAxiom]

/-- Image of `boolAxiom R i` under `aeval`. -/
@[simp] theorem aeval_boolAxiom {A : Type*} [CommRing A] [Algebra R A] (f : σ → A) (i : σ) :
    aeval f (boolAxiom R i) = f i ^ 2 - f i := by simp [boolAxiom]

/-- Total degree of a variable `X i` is at most `1` over any commutative ring. -/
theorem totalDegree_var_le (i : σ) : (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le (Finsupp.single i 1) (1 : R)).trans (by simp)

/-- Characterization of membership in `p.vars` via monomial supports. -/
theorem mem_vars_iff {p : MvPolynomial σ R} {i : σ} :
    i ∈ p.vars ↔ ∃ m ∈ p.support, i ∈ m.support := by
  classical
  simp [vars_def, mem_degrees, mem_support_iff]

/-- Any variable in the support of a monomial of `p` belongs to `p.vars`. -/
theorem mem_vars_of_mem_support {p : MvPolynomial σ R} {m : σ →₀ ℕ} {i : σ}
    (hm : m ∈ p.support) (hi : i ∈ m.support) : i ∈ p.vars :=
  mem_vars_iff.mpr ⟨m, hm, hi⟩

private theorem vars_zero_eq : (0 : MvPolynomial σ R).vars = ∅ := by
  ext u; rw [mem_vars_iff]; simp

private theorem vars_one_eq : (1 : MvPolynomial σ R).vars = ∅ := by
  rw [← C_1]; exact vars_C

/-- `vars` of a variable `X w` is contained in `{w}`. -/
theorem vars_X_subset_singleton (w : σ) : (X w : MvPolynomial σ R).vars ⊆ {w} := by
  intro u hu
  obtain ⟨m, hm, hum⟩ := mem_vars_iff.mp hu
  have hmeq : m = Finsupp.single w 1 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst hmeq
  exact Finset.mem_singleton.mpr (by by_contra hne; simp [hne] at hum)

/-- `vars (a - b) ⊆ a.vars ∪ b.vars`. -/
theorem vars_sub_le [DecidableEq σ] (a b : MvPolynomial σ R) :
    (a - b).vars ⊆ a.vars ∪ b.vars := by
  rw [sub_eq_add_neg]
  simpa [vars_neg] using vars_add_subset a (-b)

/-- `vars` of a finite product is contained in the union of the factors' `vars`. -/
theorem vars_prod_le [DecidableEq σ] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∏ i ∈ s, f i).vars ⊆ s.biUnion fun i ↦ (f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.biUnion_insert]
    exact (vars_mul _ _).trans (Finset.union_subset_union_right ih)

/-- Every Boolean constraint polynomial vanishes at every `{0, 1}` point. -/
theorem eval_boolPoint_boolAxiom (a : σ → Bool) (i : σ) :
    eval (boolPoint R a) (boolAxiom R i) = 0 := by
  cases h : a i <;> simp [h]

/-- Total degree of `boolAxiom R i` is at most `2`. -/
theorem totalDegree_boolAxiom_le (i : σ) : (boolAxiom R i).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · have h := totalDegree_var_le (R := R) i
    exact (totalDegree_pow _ 2).trans (by omega)
  · exact (totalDegree_var_le i).trans (by omega)

/-- Multilinearized exponent of `m : σ →₀ ℕ`, clamping every positive exponent to `1`. -/
noncomputable def multilinExp (m : σ →₀ ℕ) : σ →₀ ℕ :=
  m.mapRange (fun k ↦ min k 1) (by simp)

@[simp]
theorem multilinExp_apply (m : σ →₀ ℕ) (i : σ) :
    multilinExp m i = min (m i) 1 :=
  Finsupp.mapRange_apply

@[simp]
theorem support_multilinExp (m : σ →₀ ℕ) :
    (multilinExp m).support = m.support := by
  ext i
  simp only [Finsupp.mem_support_iff, multilinExp_apply]
  omega

/-- The total degree of `multilinExp m` equals the size of `m.support`. -/
theorem sum_multilinExp (m : σ →₀ ℕ) :
    ((multilinExp m).sum fun _ e ↦ e) = m.support.card := by
  rw [Finsupp.sum, support_multilinExp]
  have h1 : ∀ i ∈ m.support, multilinExp m i = 1 := fun i hi ↦ by
    have hne : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
    simp only [multilinExp_apply]; omega
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]

/-- Multilinearizing an exponent never increases its total degree. -/
theorem sum_multilinExp_le (m : σ →₀ ℕ) :
    ((multilinExp m).sum fun _ e ↦ e) ≤ (m.sum fun _ e ↦ e) := by
  rw [Finsupp.sum, Finsupp.sum, support_multilinExp]
  exact Finset.sum_le_sum fun i _ ↦ Nat.min_le_left _ _

/-- Multilinearization of a multivariate polynomial, replacing `X ^ m` by `X ^ (multilinExp m)`. -/
noncomputable def multilin (p : MvPolynomial σ R) : MvPolynomial σ R :=
  (basisMonomials σ R).constr R (fun m ↦ monomial (multilinExp m) (1 : R)) p

@[simp]
theorem multilin_monomial (m : σ →₀ ℕ) (c : R) :
    multilin (monomial m c) = monomial (multilinExp m) c := by
  have hm : monomial m c = c • basisMonomials σ R m := by simp [smul_monomial]
  have hc : multilin (c • basisMonomials σ R m) =
      c • (basisMonomials σ R).constr R (fun s ↦ monomial (multilinExp s) (1 : R))
        (basisMonomials σ R m) :=
    map_smul ((basisMonomials σ R).constr R fun s ↦ monomial (multilinExp s) (1 : R)) c _
  rw [hm, hc, Module.Basis.constr_basis, smul_monomial, smul_eq_mul, mul_one]

/-- Decomposition of `multilin p` over `p.support`. -/
theorem multilin_eq_sum (p : MvPolynomial σ R) :
    multilin p = ∑ m ∈ p.support, monomial (multilinExp m) (p.coeff m) := by
  have h : multilin p = multilin (∑ m ∈ p.support, monomial m (p.coeff m)) :=
    congrArg multilin p.as_sum
  rw [h, show multilin (∑ m ∈ p.support, monomial m (p.coeff m)) =
      ∑ m ∈ p.support, multilin (monomial m (p.coeff m)) from
    map_sum ((basisMonomials σ R).constr R _) _ _]
  exact Finset.sum_congr rfl fun m _ ↦ multilin_monomial m _

/-- Total degree of `multilin p` is bounded by the maximum support cardinality of `p`'s
monomials. -/
theorem totalDegree_multilin_le_of_support {p : MvPolynomial σ R} {b : ℕ}
    (hb : ∀ m ∈ p.support, m.support.card ≤ b) :
    (multilin p).totalDegree ≤ b := by
  rw [multilin_eq_sum]
  refine totalDegree_finsetSum_le fun m hm ↦ ?_
  exact (totalDegree_monomial_le _ _).trans ((sum_multilinExp m).trans_le (hb m hm))

/-- Multilinearization does not increase total degree. -/
theorem totalDegree_multilin_le (p : MvPolynomial σ R) :
    (multilin p).totalDegree ≤ p.totalDegree := by
  rw [multilin_eq_sum]
  refine totalDegree_finsetSum_le fun m hm ↦ ?_
  exact (totalDegree_monomial_le _ _).trans
    ((sum_multilinExp_le m).trans (le_totalDegree hm))

/-- Every variable has degree at most `1` in `multilin p`. -/
theorem degreeOf_multilin_le_one (p : MvPolynomial σ R) (i : σ) :
    (multilin p).degreeOf i ≤ 1 := by
  classical
  rw [degreeOf_eq_sup]
  refine Finset.sup_le fun d hd ↦ ?_
  rw [multilin_eq_sum] at hd
  obtain ⟨m, _, hdm⟩ := Finset.mem_biUnion.mp (support_sum hd)
  have hdeq : d = multilinExp m := Finset.mem_singleton.mp (support_monomial_subset hdm)
  rw [hdeq, multilinExp_apply]
  exact Nat.min_le_right _ _

/-- `multilin p` agrees with `p` at every `{0, 1}` point. -/
@[simp]
theorem eval_boolPoint_multilin (a : σ → Bool) (p : MvPolynomial σ R) :
    eval (boolPoint R a) (multilin p) = eval (boolPoint R a) p := by
  rw [multilin_eq_sum, map_sum]
  conv_rhs => rw [p.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [eval_monomial, eval_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset (multilinExp m) (support_multilinExp m).le _ (by simp)]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hpos : 0 < m i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hmin : min (m i) 1 = 1 := by omega
  simp only [multilinExp_apply, hmin, pow_one, boolPoint]
  cases a i
  · simp [zero_pow hpos.ne']
  · simp

/-- Degree-bounded reduction of a single monomial to its multilinearization modulo Boolean
constraints. -/
theorem monomial_sub_multilin [Fintype σ] (m : σ →₀ ℕ) (c : R) :
    ∃ q : σ → MvPolynomial σ R,
      monomial m c - monomial (multilinExp m) c = ∑ i, q i * boolAxiom R i ∧
      (∀ i, (q i * boolAxiom R i).totalDegree ≤ (m.sum fun _ e ↦ e)) ∧
      (∀ i, i ∉ m.support → q i = 0) := by
  classical
  have hgen : ∀ k, (m.sum fun _ e ↦ e) - m.support.card = k →
      ∃ q : σ → MvPolynomial σ R,
        monomial m c - monomial (multilinExp m) c = ∑ i, q i * boolAxiom R i ∧
        (∀ i, (q i * boolAxiom R i).totalDegree ≤ (m.sum fun _ e ↦ e)) ∧
        (∀ i, i ∉ m.support → q i = 0) := by
    intro k
    induction k generalizing m with
    | zero =>
      intro hk
      have hml : multilinExp m = m := by
        ext i
        by_cases hi : i ∈ m.support
        · have hge : ∀ j ∈ m.support, 1 ≤ m j := fun j hj ↦
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
          have hsub : ∑ j ∈ m.support, (m j - 1) = 0 := by
            have hadd : ∑ j ∈ m.support, ((m j - 1) + 1) = m.sum fun _ e ↦ e :=
              Finset.sum_congr rfl fun j hj ↦ Nat.sub_add_cancel (hge j hj)
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hadd
            omega
          have hi0 : m i - 1 = 0 := Nat.eq_zero_of_le_zero
            ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans hsub.le)
          have hpos := hge i hi
          simp only [multilinExp_apply]; omega
        · rw [Finsupp.notMem_support_iff] at hi
          simp [hi]
      exact ⟨0, by simp [hml], by simp, by simp⟩
    | succ k ih =>
      intro hk
      have hex : ∃ i ∈ m.support, 2 ≤ m i := by
        by_contra hall
        push Not at hall
        have hle : (m.sum fun _ e ↦ e) ≤ m.support.card := by
          rw [Finsupp.sum, Finset.card_eq_sum_ones]
          exact Finset.sum_le_sum fun j hj ↦ by have := hall j hj; omega
        omega
      obtain ⟨i₀, hi₀, h2⟩ := hex
      let m' : σ →₀ ℕ := m - Finsupp.single i₀ 1
      let r : σ →₀ ℕ := m - Finsupp.single i₀ 2
      have hm'_supp : m'.support = m.support := by
        ext j
        by_cases hj : j = i₀
        · subst hj
          simp only [m', Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [m', hj]
      have hm'_ml : multilinExp m' = multilinExp m := by
        ext j
        by_cases hj : j = i₀
        · subst hj
          simp only [multilinExp_apply, m', Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [m', hj]
      have hm_eq : r + Finsupp.single i₀ 2 = m := by
        ext j
        by_cases hj : j = i₀
        · subst hj
          simp only [r, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        · simp [r, hj]
      have hm'_eq : r + Finsupp.single i₀ 1 = m' := by
        ext j
        by_cases hj : j = i₀
        · subst hj
          simp only [r, m', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        · simp [r, m', hj]
      have hm'_add : m' + Finsupp.single i₀ 1 = m := by
        ext j
        by_cases hj : j = i₀
        · subst hj
          simp only [m', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        · simp [m', hj]
      have hm'_deg : (m'.sum fun _ e ↦ e) + 1 = (m.sum fun _ e ↦ e) := by
        rw [← hm'_add, Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
          Finsupp.sum_single_index rfl]
      obtain ⟨q', hq'_eq, hq'_deg, hq'_supp⟩ := ih m' (by rw [hm'_supp]; omega)
      have hstep : monomial m c - monomial m' c = monomial r c * boolAxiom R i₀ := by
        rw [boolAxiom, mul_sub, X_pow_eq_monomial, X, monomial_mul_monomial,
          monomial_mul_monomial, mul_one, hm_eq, hm'_eq]
      have hstep_deg : (monomial r c * boolAxiom R i₀).totalDegree ≤ (m.sum fun _ e ↦ e) := by
        rw [← hstep]
        have htm' : (monomial m' c).totalDegree ≤ (m'.sum fun _ e ↦ e) :=
          totalDegree_monomial_le m' c
        exact (totalDegree_sub _ _).trans (max_le (totalDegree_monomial_le m c)
          (htm'.trans (by omega)))
      refine ⟨fun j ↦ q' j + if j = i₀ then monomial r c else 0, ?_, ?_, ?_⟩
      · have hsum_ite : (∑ j : σ, (if j = i₀ then monomial r c else 0) * boolAxiom R j) =
            monomial r c * boolAxiom R i₀ := by
          simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp_rw [add_mul, Finset.sum_add_distrib, hsum_ite, ← hq'_eq, ← hstep, hm'_ml]
        ring
      · intro j
        rw [add_mul]
        refine (totalDegree_add _ _).trans (max_le ((hq'_deg j).trans (by omega)) ?_)
        by_cases hj : j = i₀
        · subst hj; simpa using hstep_deg
        · simp [hj]
      · intro j hj
        have hne : j ≠ i₀ := fun h ↦ hj (h ▸ hi₀)
        dsimp only
        rw [hq'_supp j (hm'_supp.symm ▸ hj)]
        simp [hne]
  exact hgen _ rfl

/-- Every polynomial `p` decomposes as `multilin p + ∑ i, q i * (X i ^ 2 - X i)` with every
summand of total degree at most `p.totalDegree` and `q i = 0` outside `p.vars`. -/
theorem eq_multilin_add_sum_mul_boolAxiom [Fintype σ] (p : MvPolynomial σ R) :
    ∃ q : σ → MvPolynomial σ R,
      p = multilin p + ∑ i, q i * boolAxiom R i ∧
      (∀ i, (q i * boolAxiom R i).totalDegree ≤ p.totalDegree) ∧
      (∀ i, i ∉ p.vars → q i = 0) := by
  classical
  choose qm hqm_eq hqm_deg hqm_supp using fun m : σ →₀ ℕ ↦ monomial_sub_multilin m (p.coeff m)
  refine ⟨fun i ↦ ∑ m ∈ p.support, qm m i, ?_, ?_, ?_⟩
  · have hsub : p - multilin p =
        ∑ m ∈ p.support, (monomial m (p.coeff m) - monomial (multilinExp m) (p.coeff m)) := by
      rw [Finset.sum_sub_distrib, ← multilin_eq_sum]
      exact congrArg (· - multilin p) p.as_sum
    have hsum : ∑ i, (∑ m ∈ p.support, qm m i) * boolAxiom R i = p - multilin p := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm, hsub]
      exact Finset.sum_congr rfl fun m _ ↦ (hqm_eq m).symm
    rw [hsum]; ring
  · intro i
    rw [Finset.sum_mul]
    exact totalDegree_finsetSum_le fun m hm ↦ (hqm_deg m i).trans (le_totalDegree hm)
  · intro i hi
    exact Finset.sum_eq_zero fun m hm ↦ hqm_supp m i fun him ↦ hi (mem_vars_of_mem_support hm him)

/-- A multilinear polynomial vanishing at every `{0, 1}` point is the zero polynomial. -/
theorem eq_zero_of_degreeOf_le_one_of_eval_boolPoint {p : MvPolynomial σ R}
    (hml : ∀ i, p.degreeOf i ≤ 1) (heval : ∀ a : σ → Bool, eval (boolPoint R a) p = 0) :
    p = 0 := by
  classical
  by_contra hp
  obtain ⟨m₀, hm₀, hmin⟩ :=
    p.support.exists_min_image (fun m ↦ m.support.card) (support_nonempty.mpr hp)
  let a : σ → Bool := fun i ↦ decide (i ∈ m₀.support)
  have hval := heval a
  rw [eval_eq] at hval
  have hsingle : ∀ m ∈ p.support,
      p.coeff m * (∏ i ∈ m.support, boolPoint R a i ^ m i) =
      if m = m₀ then p.coeff m₀ else 0 := by
    intro m hm
    by_cases h : m = m₀
    · subst h
      simp only [↓reduceIte]
      rw [Finset.prod_eq_one (fun i hi ↦ ?_), mul_one]
      have ha : a i = true := decide_eq_true hi
      simp [ha]
    · simp only [h, ↓reduceIte]
      by_cases hsub : m.support ⊆ m₀.support
      · have hcard_lt : m.support.card < m₀.support.card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hse ↦ h ?_⟩)
          ext i
          have hmi : m i ≤ 1 :=
            (degreeOf_eq_sup i p ▸ Finset.le_sup (f := fun d : σ →₀ ℕ ↦ d i) hm).trans (hml i)
          have hm0i : m₀ i ≤ 1 :=
            (degreeOf_eq_sup i p ▸ Finset.le_sup (f := fun d : σ →₀ ℕ ↦ d i) hm₀).trans (hml i)
          by_cases hi : i ∈ m.support
          · have h1 := Finsupp.mem_support_iff.mp hi
            have h2 := Finsupp.mem_support_iff.mp (hse ▸ hi)
            omega
          · have hi0 : i ∉ m₀.support := hse ▸ hi
            rw [Finsupp.notMem_support_iff.mp hi, Finsupp.notMem_support_iff.mp hi0]
        exact absurd (hmin m hm) hcard_lt.not_ge
      · obtain ⟨j, hjm, hjm0⟩ := Finset.not_subset.mp hsub
        have hjpos : m j ≠ 0 := Finsupp.mem_support_iff.mp hjm
        have haj : a j = false := decide_eq_false hjm0
        rw [Finset.prod_eq_zero hjm (by simp [haj, zero_pow hjpos]), mul_zero]
  rw [Finset.sum_congr rfl hsingle, Finset.sum_ite_eq'] at hval
  simp only [hm₀, ↓reduceIte] at hval
  exact (mem_support_iff.mp hm₀) hval

/-- Two multilinear polynomials agreeing at every `{0, 1}` point are equal. -/
theorem eq_of_degreeOf_le_one_of_eval_boolPoint {p q : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (heval : ∀ a : σ → Bool, eval (boolPoint R a) p = eval (boolPoint R a) q) :
    p = q := by
  refine sub_eq_zero.mp (eq_zero_of_degreeOf_le_one_of_eval_boolPoint (fun i ↦ ?_) fun a ↦ ?_)
  · exact (degreeOf_sub_le i p q).trans (max_le (hp i) (hq i))
  · rw [map_sub, heval a, sub_self]

/-- **Boolean vanishing ideal with degree bound**: any polynomial `p : MvPolynomial σ R` of total
degree at most `d` vanishing on `{0, 1}^σ` decomposes as `∑ i, q i * (X i ^ 2 - X i)` where every
term has total degree at most `d` and `q i = 0` outside `p.vars`. -/
theorem eq_sum_mul_boolAxiom_of_eval_eq_zero [Fintype σ] {p : MvPolynomial σ R} {d : ℕ}
    (hdeg : p.totalDegree ≤ d) (heval : ∀ a : σ → Bool, eval (boolPoint R a) p = 0) :
    ∃ q : σ → MvPolynomial σ R,
      p = ∑ i, q i * boolAxiom R i ∧
      (∀ i, (q i * boolAxiom R i).totalDegree ≤ d) ∧
      (∀ i, i ∉ p.vars → q i = 0) := by
  obtain ⟨q, hq_eq, hq_deg, hq_vars⟩ := eq_multilin_add_sum_mul_boolAxiom p
  have hml_zero : multilin p = 0 :=
    eq_zero_of_degreeOf_le_one_of_eval_boolPoint (degreeOf_multilin_le_one p)
      fun a ↦ by rw [eval_boolPoint_multilin, heval a]
  rw [hml_zero, zero_add] at hq_eq
  exact ⟨q, hq_eq, fun i ↦ (hq_deg i).trans hdeg, hq_vars⟩

end BooleanIdeal

/-! ### Sum-of-Squares Proofs, Refutations, Degree, and Monomial Size -/

section SosDefs

variable {σ τ : Type*}

/-- A static Sum-of-Squares proof over `ℝ` of `f ≥ 0` from the polynomial equations `F`:
multipliers `mult` for each constraint in `F` and unweighted squares `squares` satisfying
`∑ i, mult i * F[i] + ∑ s ∈ squares, s ^ 2 = f`. -/
structure SosProof (F : List (MvPolynomial σ ℝ)) (f : MvPolynomial σ ℝ) where
  /-- Polynomial multiplier for each equation `F[i] = 0`. -/
  mult : Fin F.length → MvPolynomial σ ℝ
  /-- List of polynomials whose squares are summed. -/
  squares : List (MvPolynomial σ ℝ)
  /-- Algebraic identity certifying `f` modulo `F` plus a sum of squares. -/
  eq : ∑ i, mult i * F.get i + (squares.map fun s ↦ s ^ 2).sum = f

/-- Degree of a Sum-of-Squares proof: the maximum total degree among all `mult i * F[i]` and
`2 * s.totalDegree` for `s ∈ squares`. -/
noncomputable def SosProof.degree {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ}
    (π : SosProof F f) : ℕ :=
  max (Finset.univ.sup fun i ↦ (π.mult i * F.get i).totalDegree)
    ((π.squares.map fun s ↦ 2 * s.totalDegree).foldr max 0)

/-- Total monomial size of a Sum-of-Squares proof: sum of the numbers of nonzero monomials across
all multiplier polynomials and square-root polynomials in `π`. -/
@[expose]
noncomputable def SosProof.size {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ}
    (π : SosProof F f) : ℕ :=
  (∑ i, (π.mult i).support.card) + (π.squares.map fun s ↦ s.support.card).sum

/-- Decomposition of `π.size` into multiplier and square-root monomial counts. -/
theorem SosProof.size_eq_sum {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ}
    (π : SosProof F f) :
    π.size = (∑ i, (π.mult i).support.card) + (π.squares.map fun s ↦ s.support.card).sum :=
  rfl

/-- Characterization of `π.degree ≤ d`. -/
theorem SosProof.degree_le_iff {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ}
    {π : SosProof F f} {d : ℕ} :
    π.degree ≤ d ↔
      (∀ i, (π.mult i * F.get i).totalDegree ≤ d) ∧
      (∀ s ∈ π.squares, 2 * s.totalDegree ≤ d) := by
  simp only [SosProof.degree, max_le_iff, Finset.sup_le_iff, Finset.mem_univ, forall_const]
  refine and_congr_right fun _ ↦ ?_
  induction π.squares with
  | nil => simp
  | cons s ss ih => simp [max_le_iff, ih]

/-- A Sum-of-Squares refutation of `F` is a Sum-of-Squares proof of `-1 ≥ 0` from `F`. -/
abbrev SosRefutation (F : List (MvPolynomial σ ℝ)) : Type _ :=
  SosProof F (-1)

/-- `F` admits an SoS proof of `f ≥ 0` of degree at most `d`. -/
@[expose]
def SosDerivableInDegree (F : List (MvPolynomial σ ℝ)) (f : MvPolynomial σ ℝ) (d : ℕ) : Prop :=
  ∃ π : SosProof F f, π.degree ≤ d

/-- `F` admits a Nullstellensatz (square-free SoS) derivation of `f` in degree at most `d`. -/
@[expose]
def NsDerivableInDegree (F : List (MvPolynomial σ ℝ)) (f : MvPolynomial σ ℝ) (d : ℕ) : Prop :=
  ∃ mult : Fin F.length → MvPolynomial σ ℝ,
    ∑ i, mult i * F.get i = f ∧ ∀ i, (mult i * F.get i).totalDegree ≤ d

/-- Every square-free Nullstellensatz derivation is an SoS derivation of the same degree. -/
theorem NsDerivableInDegree.toSos {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ} {d : ℕ}
    (h : NsDerivableInDegree F f d) : SosDerivableInDegree F f d := by
  obtain ⟨mult, heq, hdeg⟩ := h
  exact ⟨⟨mult, [], by simpa using heq⟩, SosProof.degree_le_iff.mpr ⟨hdeg, by simp⟩⟩

/-- `F` admits an SoS refutation of degree at most `d`. -/
@[expose]
def SosRefutableInDegree (F : List (MvPolynomial σ ℝ)) (d : ℕ) : Prop :=
  ∃ π : SosRefutation F, π.degree ≤ d

/-- `F` admits an SoS refutation of monomial size at most `s`. -/
@[expose]
def SosRefutableInSize (F : List (MvPolynomial σ ℝ)) (s : ℕ) : Prop :=
  ∃ π : SosRefutation F, π.size ≤ s

/-- Minimum degree of an SoS refutation of `F` (`⊤` if no refutation exists). -/
noncomputable def sosRefuteDeg (F : List (MvPolynomial σ ℝ)) : ℕ∞ :=
  sInf {d : ℕ∞ | ∃ d₀ : ℕ, d = d₀ ∧ SosRefutableInDegree F d₀}

/-- Minimum monomial size of an SoS refutation of `F` (`⊤` if no refutation exists). -/
noncomputable def sosRefuteSize (F : List (MvPolynomial σ ℝ)) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ s₀ : ℕ, s = s₀ ∧ SosRefutableInSize F s₀}

/-- Any degree-`d` refutation bounds `sosRefuteDeg F` above by `d`. -/
theorem sosRefuteDeg_le_of_refutable {F : List (MvPolynomial σ ℝ)} {d : ℕ}
    (h : SosRefutableInDegree F d) : sosRefuteDeg F ≤ d :=
  sInf_le ⟨d, rfl, h⟩

/-- Lower bound characterization of `sosRefuteDeg F`. -/
theorem le_sosRefuteDeg_iff {F : List (MvPolynomial σ ℝ)} {b : ℕ∞} :
    b ≤ sosRefuteDeg F ↔ ∀ d : ℕ, SosRefutableInDegree F d → b ≤ d := by
  rw [sosRefuteDeg, le_sInf_iff]
  exact ⟨fun h d hd ↦ h d ⟨d, rfl, hd⟩, by rintro h _ ⟨d, rfl, hd⟩; exact h d hd⟩

/-- Any size-`s` refutation bounds `sosRefuteSize F` above by `s`. -/
theorem sosRefuteSize_le_of_refutable {F : List (MvPolynomial σ ℝ)} {s : ℕ}
    (h : SosRefutableInSize F s) : sosRefuteSize F ≤ s :=
  sInf_le ⟨s, rfl, h⟩

/-- Lower bound characterization of `sosRefuteSize F`. -/
theorem le_sosRefuteSize_iff {F : List (MvPolynomial σ ℝ)} {b : ℕ∞} :
    b ≤ sosRefuteSize F ↔ ∀ s : ℕ, SosRefutableInSize F s → b ≤ s := by
  rw [sosRefuteSize, le_sInf_iff]
  exact ⟨fun h s hs ↦ h s ⟨s, rfl, hs⟩, by rintro h _ ⟨s, rfl, hs⟩; exact h s hs⟩

/-- Monotonicity of `SosRefutableInDegree`. -/
theorem SosRefutableInDegree.mono {F : List (MvPolynomial σ ℝ)} {d d' : ℕ}
    (h : SosRefutableInDegree F d) (hd : d ≤ d') : SosRefutableInDegree F d' :=
  let ⟨π, hπ⟩ := h
  ⟨π, hπ.trans hd⟩

/-- Monotonicity of `SosRefutableInSize`. -/
theorem SosRefutableInSize.mono {F : List (MvPolynomial σ ℝ)} {s s' : ℕ}
    (h : SosRefutableInSize F s) (hs : s ≤ s') : SosRefutableInSize F s' :=
  let ⟨π, hπ⟩ := h
  ⟨π, hπ.trans hs⟩

/-- Equivalence between unweighted real `SosRefutableInDegree` and upstream
`Cslib.Logic.PL.SOS.RefutableInDegree`. -/
theorem sosRefutableInDegree_iff_cslib {F : List (MvPolynomial σ ℝ)} {d : ℕ} :
    SosRefutableInDegree F d ↔ SOS.RefutableInDegree F d := by
  rw [SOS.refutableInDegree_iff]
  constructor
  · rintro ⟨π, hπ⟩
    obtain ⟨hmul, hsq⟩ := SosProof.degree_le_iff.mp hπ
    refine ⟨⟨π.mult, π.squares.map fun s ↦ (1, s), ?_, hmul, by simp, ?_⟩⟩
    · simpa [List.map_map, Function.comp_def] using π.eq
    · intro p hp
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
      exact hsq s hs
  · rintro ⟨r⟩
    refine ⟨⟨r.mult, r.squares.map fun p ↦ C (Real.sqrt p.1) * p.2, ?_⟩,
      SosProof.degree_le_iff.mpr ⟨r.totalDegree_mul_le, ?_⟩⟩
    · rw [List.map_map, ← r.eq]
      congr 2
      refine List.map_congr_left fun p hp ↦ ?_
      dsimp only [Function.comp_apply]
      rw [mul_pow, ← map_pow, Real.sq_sqrt (r.weight_nonneg p hp)]
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      have hle : (C (Real.sqrt p.1) * p.2).totalDegree ≤ p.2.totalDegree :=
        (totalDegree_mul _ _).trans (by simp)
      exact (Nat.mul_le_mul_left 2 hle).trans (r.two_mul_totalDegree_le p hp)

/-- Soundness of Sum-of-Squares: a system with a real common zero has no refutation in any
degree. -/
theorem not_sosRefutableInDegree_of_eval_eq_zero {F : List (MvPolynomial σ ℝ)}
    (x : σ → ℝ) (hx : ∀ f ∈ F, eval x f = 0) (d : ℕ) :
    ¬ SosRefutableInDegree F d := fun hd ↦
  (sosRefutableInDegree_iff_cslib.mp hd).not_exists_eval_eq_zero ⟨x, hx⟩

/-- Soundness for arbitrary SoS refutations. -/
theorem not_sosRefutation_of_eval_eq_zero {F : List (MvPolynomial σ ℝ)}
    (x : σ → ℝ) (hx : ∀ f ∈ F, eval x f = 0) (π : SosRefutation F) : False :=
  not_sosRefutableInDegree_of_eval_eq_zero x hx π.degree ⟨π, le_rfl⟩

/-- Build a degree-`d` SoS derivation witness from a list of `(multiplier, constraint)` pairs and a
list of unweighted squares. -/
theorem SosDerivableInDegree.of_list {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ} {d : ℕ}
    (L : List (MvPolynomial σ ℝ × MvPolynomial σ ℝ))
    (hL : ∀ p ∈ L, p.2 ∈ F ∧ (p.1 * p.2).totalDegree ≤ d)
    (squares : List (MvPolynomial σ ℝ))
    (hsq : ∀ s ∈ squares, 2 * s.totalDegree ≤ d)
    (heq : (L.map fun p ↦ p.1 * p.2).sum + (squares.map fun s ↦ s ^ 2).sum = f) :
    SosDerivableInDegree F f d := by
  classical
  choose idx hidx using fun i : Fin L.length ↦ List.mem_iff_get.mp (hL _ (List.get_mem L i)).1
  let mult : Fin F.length → MvPolynomial σ ℝ :=
    fun j ↦ ∑ i ∈ Finset.univ.filter (idx · = j), (L.get i).1
  have hmul (j : Fin F.length) :
      mult j * F.get j = ∑ i ∈ Finset.univ.filter (idx · = j), (L.get i).1 * (L.get i).2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [← (Finset.mem_filter.mp hi).2, hidx i]
  refine ⟨⟨mult, squares, ?_⟩, SosProof.degree_le_iff.mpr ⟨fun j ↦ ?_, hsq⟩⟩
  · rw [Finset.sum_congr rfl fun j _ ↦ hmul j, Finset.sum_fiberwise, ← heq]
    congr 1
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ext_getElem (by simp) (by simp))
  · rw [hmul]
    exact totalDegree_finsetSum_le fun i _ ↦ (hL _ (List.get_mem L i)).2

/-- Build a degree-`d` Nullstellensatz derivation from a list of `(multiplier, constraint)` pairs.
-/
theorem NsDerivableInDegree.of_list {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ} {d : ℕ}
    (L : List (MvPolynomial σ ℝ × MvPolynomial σ ℝ))
    (hL : ∀ p ∈ L, p.2 ∈ F ∧ (p.1 * p.2).totalDegree ≤ d)
    (heq : (L.map fun p ↦ p.1 * p.2).sum = f) :
    NsDerivableInDegree F f d := by
  classical
  choose idx hidx using fun i : Fin L.length ↦ List.mem_iff_get.mp (hL _ (List.get_mem L i)).1
  let mult : Fin F.length → MvPolynomial σ ℝ :=
    fun j ↦ ∑ i ∈ Finset.univ.filter (idx · = j), (L.get i).1
  have hmul (j : Fin F.length) :
      mult j * F.get j = ∑ i ∈ Finset.univ.filter (idx · = j), (L.get i).1 * (L.get i).2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [← (Finset.mem_filter.mp hi).2, hidx i]
  refine ⟨mult, ?_, fun j ↦ ?_⟩
  · rw [Finset.sum_congr rfl fun j _ ↦ hmul j, Finset.sum_fiberwise, ← heq, ← List.sum_ofFn]
    exact congrArg List.sum (List.ext_getElem (by simp) (by simp))
  · rw [hmul]
    exact totalDegree_finsetSum_le fun i _ ↦ (hL _ (List.get_mem L i)).2

/-- Build a degree-`d` SoS refutation witness from a list of `(multiplier, constraint)` pairs and
unweighted squares. -/
theorem SosRefutableInDegree.of_list {F : List (MvPolynomial σ ℝ)} {d : ℕ}
    (L : List (MvPolynomial σ ℝ × MvPolynomial σ ℝ))
    (hL : ∀ p ∈ L, p.2 ∈ F ∧ (p.1 * p.2).totalDegree ≤ d)
    (squares : List (MvPolynomial σ ℝ))
    (hsq : ∀ s ∈ squares, 2 * s.totalDegree ≤ d)
    (heq : (L.map fun p ↦ p.1 * p.2).sum + (squares.map fun s ↦ s ^ 2).sum = -1) :
    SosRefutableInDegree F d :=
  SosDerivableInDegree.of_list L hL squares hsq heq

/-- Nullstellensatz derivations are closed under addition, scalar multiplication, polynomial
multiplication, and finite sums. -/
theorem NsDerivableInDegree.add {F : List (MvPolynomial σ ℝ)} {f g : MvPolynomial σ ℝ} {d : ℕ}
    (hf : NsDerivableInDegree F f d) (hg : NsDerivableInDegree F g d) :
    NsDerivableInDegree F (f + g) d := by
  obtain ⟨mf, rfl, hdf⟩ := hf
  obtain ⟨mg, rfl, hdg⟩ := hg
  refine ⟨mf + mg, by simp [add_mul, Finset.sum_add_distrib], fun i ↦ ?_⟩
  simp only [Pi.add_apply, add_mul]
  exact (totalDegree_add _ _).trans (max_le (hdf i) (hdg i))

/-- Negating a Nullstellensatz derivation preserves degree. -/
theorem NsDerivableInDegree.neg {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ} {d : ℕ}
    (hf : NsDerivableInDegree F f d) : NsDerivableInDegree F (-f) d := by
  obtain ⟨mf, rfl, hdf⟩ := hf
  refine ⟨-mf, by simp [neg_mul, Finset.sum_neg_distrib], fun i ↦ ?_⟩
  simpa [neg_mul] using hdf i

/-- Multiplying a Nullstellensatz derivation by a polynomial `r` adds at most `r.totalDegree`. -/
theorem NsDerivableInDegree.mul_left {F : List (MvPolynomial σ ℝ)} {f : MvPolynomial σ ℝ} {d : ℕ}
    (r : MvPolynomial σ ℝ) (hf : NsDerivableInDegree F f d) :
    NsDerivableInDegree F (r * f) (r.totalDegree + d) := by
  obtain ⟨mf, rfl, hdf⟩ := hf
  refine ⟨fun i ↦ r * mf i, by simp [Finset.mul_sum, mul_assoc], fun i ↦ ?_⟩
  rw [mul_assoc]
  exact (totalDegree_mul _ _).trans (Nat.add_le_add_left (hdf i) _)

/-- Finite sum of degree-`d` Nullstellensatz derivations has degree at most `d`. -/
theorem NsDerivableInDegree.finsetSum {F : List (MvPolynomial σ ℝ)} {d : ℕ} {ι : Type*}
    (s : Finset ι) {g : ι → MvPolynomial σ ℝ}
    (hg : ∀ i ∈ s, NsDerivableInDegree F (g i) d) :
    NsDerivableInDegree F (∑ i ∈ s, g i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))

/-- Transitivity of Nullstellensatz derivations: if `F` has a degree-`d` SoS refutation and every
constraint `g ∈ F` is Nullstellensatz-derivable from `G` in degree `c + g.totalDegree`, then `G` has
an
SoS refutation of degree at most `d + c`. -/
theorem SosRefutableInDegree.of_nsDerivable {F G : List (MvPolynomial σ ℝ)} {d c : ℕ}
    (href : SosRefutableInDegree F d)
    (hder : ∀ g ∈ F, g ≠ 0 → NsDerivableInDegree G g (g.totalDegree + c)) :
    SosRefutableInDegree G (d + c) := by
  obtain ⟨π, hπ⟩ := href
  obtain ⟨hmul, hsq⟩ := SosProof.degree_le_iff.mp hπ
  have hterm : ∀ i : Fin F.length,
      NsDerivableInDegree G (π.mult i * F.get i) (d + c) := by
    intro i
    by_cases hmi : π.mult i = 0
    · exact ⟨0, by simp [hmi], by simp⟩
    · by_cases hfi : F.get i = 0
      · exact ⟨0, by rw [hfi, mul_zero]; simp, by simp⟩
      · obtain ⟨mg, hmg_eq, hmg_deg⟩ := hder _ (List.get_mem F i) hfi
        have htot : (π.mult i).totalDegree + (F.get i).totalDegree ≤ d := by
          have hdi := hmul i
          rwa [totalDegree_mul_of_isDomain hmi hfi] at hdi
        refine ⟨fun j ↦ π.mult i * mg j, ?_, fun j ↦ ?_⟩
        · rw [← hmg_eq, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by dsimp only; rw [mul_assoc]
        · dsimp only
          rw [mul_assoc]
          have := (totalDegree_mul (π.mult i) (mg j * G.get j)).trans
            (Nat.add_le_add_left (hmg_deg j) _)
          omega
  obtain ⟨mTot, hmTot_eq, hmTot_deg⟩ :=
    NsDerivableInDegree.finsetSum Finset.univ fun i _ ↦ hterm i
  refine ⟨⟨mTot, π.squares, by rw [hmTot_eq, π.eq]⟩,
    SosProof.degree_le_iff.mpr ⟨hmTot_deg, fun s hs ↦ (hsq s hs).trans (by omega)⟩⟩

/-- Every SoS refutation has positive monomial size (`1 ≤ π.size`). -/
theorem SosRefutation.one_le_size {F : List (MvPolynomial σ ℝ)} (π : SosRefutation F) :
    1 ≤ π.size := by
  by_contra h0
  have hsz : π.size = 0 := by omega
  simp only [SosProof.size, Nat.add_eq_zero_iff, Finset.sum_eq_zero_iff, Finset.mem_univ,
    forall_const, Finset.card_eq_zero, support_eq_empty, List.sum_eq_zero_iff,
    List.mem_map] at hsz
  have h1 : ∑ i, π.mult i * F.get i = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hsz.1 i, zero_mul]
  have h2 : (π.squares.map fun s ↦ s ^ 2).sum = 0 :=
    List.sum_eq_zero fun x hx ↦ by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      have hs0 : s = 0 := support_eq_empty.mp (Finset.card_eq_zero.mp (hsz.2 _ ⟨s, hs, rfl⟩))
      simp [hs0]
  have heq := π.eq
  rw [h1, h2, add_zero] at heq
  have := congrArg (constantCoeff (R := ℝ) (σ := σ)) heq
  simp at this

/-- An SoS refutation of monomial size at most `1` necessarily has degree `0`. -/
theorem SosRefutation.degree_eq_zero_of_size_le_one {F : List (MvPolynomial σ ℝ)}
    (π : SosRefutation F) (hsz : π.size ≤ 1) : π.degree = 0 := by
  have h1 : π.size = 1 := le_antisymm hsz π.one_le_size
  rcases Nat.eq_zero_or_pos (π.squares.map fun s ↦ s.support.card).sum with hsq0 | hsqpos
  · have hsq_all : ∀ s ∈ π.squares, s = 0 := fun s hs ↦
      support_eq_empty.mp (Finset.card_eq_zero.mp
        (List.sum_eq_zero_iff.mp hsq0 _ (List.mem_map_of_mem hs)))
    have hsq_sum : (π.squares.map fun s ↦ s ^ 2).sum = 0 :=
      List.sum_eq_zero fun x hx ↦ by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        simp [hsq_all s hs]
    have hmult_sum : ∑ i, (π.mult i).support.card = 1 := by
      simp only [SosProof.size] at h1; omega
    have hpos : ∃ i₀ : Fin F.length, 0 < (π.mult i₀).support.card := by
      by_contra hall
      push Not at hall
      have : ∑ i, (π.mult i).support.card = 0 :=
        Finset.sum_eq_zero fun i _ ↦ Nat.eq_zero_of_le_zero (hall i)
      omega
    obtain ⟨i₀, hpos₀⟩ := hpos
    have hrest0 : ∀ j, j ≠ i₀ → π.mult j = 0 := by
      intro j hne
      refine support_eq_empty.mp (Finset.card_eq_zero.mp ?_)
      by_contra hjne
      have hle := Finset.add_le_sum (f := fun i ↦ (π.mult i).support.card)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i₀) (Finset.mem_univ j) hne.symm
      omega
    have hprod : π.mult i₀ * F.get i₀ = -1 := by
      have heq := π.eq
      rw [hsq_sum, add_zero, Finset.sum_eq_single i₀
        (fun j _ hne ↦ by rw [hrest0 j hne, zero_mul]) (by simp)] at heq
      exact heq
    refine Nat.eq_zero_of_le_zero (SosProof.degree_le_iff.mpr ⟨fun j ↦ ?_, fun s hs ↦ ?_⟩)
    · by_cases hj : j = i₀
      · subst hj; rw [hprod, totalDegree_neg, totalDegree_one]
      · simp [hrest0 j hj]
    · simp [hsq_all s hs]
  · have hmult0 : ∀ i, π.mult i = 0 := fun i ↦ by
      have hms : ∑ j, (π.mult j).support.card = 0 := by
        simp only [SosProof.size] at h1; omega
      exact support_eq_empty.mp (Finset.card_eq_zero.mp
        (Finset.sum_eq_zero_iff.mp hms i (Finset.mem_univ i)))
    exfalso
    have heq := congrArg (eval (0 : σ → ℝ)) π.eq
    simp only [hmult0, zero_mul, Finset.sum_const_zero, zero_add,
      map_list_sum, List.map_map, map_neg, map_one] at heq
    have hnn : 0 ≤ (π.squares.map (eval (0 : σ → ℝ) ∘ fun s ↦ s ^ 2)).sum :=
      List.sum_nonneg fun x hx ↦ by
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
        simp only [Function.comp_apply, map_pow]
        exact sq_nonneg _
    linarith

/-! ### Variable Substitutions and Polynomial Substitutions -/

/-- Atomic variable substitution sending each `i : σ` to `0`, `1`, or a variable `j : τ`. -/
abbrev AtomSubst (σ τ : Type*) : Type _ := σ → Bool ⊕ τ

/-- Polynomial assigned to `i : σ` by `ρ : AtomSubst σ τ`. -/
@[expose]
noncomputable def AtomSubst.toPoly (ρ : AtomSubst σ τ) (i : σ) : MvPolynomial τ ℝ :=
  match ρ i with
  | .inl false => 0
  | .inl true => 1
  | .inr j => X j

@[simp]
theorem AtomSubst.toPoly_of_false {ρ : AtomSubst σ τ} {i : σ} (h : ρ i = .inl false) :
    ρ.toPoly i = 0 := by simp [AtomSubst.toPoly, h]

@[simp]
theorem AtomSubst.toPoly_of_true {ρ : AtomSubst σ τ} {i : σ} (h : ρ i = .inl true) :
    ρ.toPoly i = 1 := by simp [AtomSubst.toPoly, h]

@[simp]
theorem AtomSubst.toPoly_of_inr {ρ : AtomSubst σ τ} {i : σ} {j : τ} (h : ρ i = .inr j) :
    ρ.toPoly i = X j := by simp [AtomSubst.toPoly, h]

theorem AtomSubst.toPoly_eq_match (ρ : AtomSubst σ τ) (i : σ) :
    ρ.toPoly i = match ρ i with | .inl false => 0 | .inl true => 1 | .inr j => X j := rfl

/-- Induced algebra homomorphism `MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ`. -/
@[expose]
noncomputable def AtomSubst.evalHom (ρ : AtomSubst σ τ) :
    MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ :=
  aeval ρ.toPoly

theorem AtomSubst.evalHom_eq_aeval (ρ : AtomSubst σ τ) : ρ.evalHom = aeval ρ.toPoly := rfl

@[simp]
theorem AtomSubst.evalHom_X (ρ : AtomSubst σ τ) (i : σ) : ρ.evalHom (X i) = ρ.toPoly i :=
  aeval_X ρ.toPoly i

theorem AtomSubst.evalHom_C (ρ : AtomSubst σ τ) (c : ℝ) : ρ.evalHom (C c) = C c :=
  aeval_C ρ.toPoly c

@[simp]
theorem AtomSubst.evalHom_boolAxiom (ρ : AtomSubst σ τ) (i : σ) :
    ρ.evalHom (boolAxiom ℝ i) = ρ.toPoly i ^ 2 - ρ.toPoly i :=
  aeval_boolAxiom ρ.toPoly i

/-- Image of a monomial under `ρ.evalHom`. -/
theorem AtomSubst.evalHom_monomial_eq (ρ : AtomSubst σ τ) (m : σ →₀ ℕ) (c : ℝ) :
    ρ.evalHom (monomial m c) = C c * m.prod fun i k ↦ ρ.toPoly i ^ k := by
  rw [AtomSubst.evalHom, aeval_monomial, algebraMap_eq]

/-- Restrict an equation system `F` by `ρ : AtomSubst σ τ`, removing `0 = 0` equations. -/
@[expose]
noncomputable def AtomSubst.restrictSystem (ρ : AtomSubst σ τ)
    (F : List (MvPolynomial σ ℝ)) : List (MvPolynomial τ ℝ) := by
  classical
  exact (F.map ρ.evalHom).filter (· ≠ 0)

theorem AtomSubst.restrictSystem_eq_filter [DecidableEq (MvPolynomial τ ℝ)]
    (ρ : AtomSubst σ τ) (F : List (MvPolynomial σ ℝ)) :
    ρ.restrictSystem F = (F.map ρ.evalHom).filter (· ≠ 0) := by
  unfold AtomSubst.restrictSystem; congr 1; funext p; congr 1

/-- Membership in `ρ.restrictSystem F`: nonzero images of polynomials in `F`. -/
theorem AtomSubst.mem_restrictSystem_iff (ρ : AtomSubst σ τ)
    {F : List (MvPolynomial σ ℝ)} {g : MvPolynomial τ ℝ} :
    g ∈ ρ.restrictSystem F ↔ (∃ f ∈ F, ρ.evalHom f = g) ∧ g ≠ 0 := by
  classical
  simp [AtomSubst.restrictSystem]

@[simp]
theorem AtomSubst.restrictSystem_append (ρ : AtomSubst σ τ)
    (F G : List (MvPolynomial σ ℝ)) :
    ρ.restrictSystem (F ++ G) = ρ.restrictSystem F ++ ρ.restrictSystem G := by
  classical
  simp [AtomSubst.restrictSystem, List.filter_append]

/-- Each variable maps to a polynomial of total degree at most `1`. -/
theorem AtomSubst.totalDegree_toPoly_le (ρ : AtomSubst σ τ) (i : σ) :
    (ρ.toPoly i).totalDegree ≤ 1 := by
  rcases h : ρ i with (_ | _) | j
  · simp [AtomSubst.toPoly, h]
  · simp [AtomSubst.toPoly, h]
  · simp only [AtomSubst.toPoly, h]
    exact totalDegree_var_le j

private theorem AtomSubst.evalHom_monomial (ρ : AtomSubst σ τ) (m : σ →₀ ℕ) (c : ℝ) :
    ρ.evalHom (monomial m c) = 0 ∨ ∃ m' : τ →₀ ℕ, ρ.evalHom (monomial m c) = monomial m' c := by
  classical
  rw [AtomSubst.evalHom, aeval_monomial, algebraMap_eq]
  by_cases hzero : ∃ i ∈ m.support, ρ i = .inl false
  · left
    obtain ⟨i, hi, hri⟩ := hzero
    rw [Finsupp.prod, Finset.prod_eq_zero hi
      (by simp [AtomSubst.toPoly, hri, zero_pow (Finsupp.mem_support_iff.mp hi)]), mul_zero]
  · right
    push Not at hzero
    let step : σ → ℕ → (τ →₀ ℕ) := fun i k ↦
      match ρ i with
      | .inl _ => 0
      | .inr j => Finsupp.single j k
    refine ⟨m.sum step, ?_⟩
    have hprod : m.prod (fun i k ↦ ρ.toPoly i ^ k) = monomial (m.sum step) 1 := by
      rw [Finsupp.prod, Finsupp.sum]
      have hfac : ∀ i ∈ m.support, ρ.toPoly i ^ m i = monomial (step i (m i)) (1 : ℝ) := by
        intro i hi
        rcases hri : ρ i with (_ | _) | j
        · exact absurd hri (hzero i hi)
        · simp [AtomSubst.toPoly, step, hri, C_1]
        · simp [AtomSubst.toPoly, step, hri, X_pow_eq_monomial]
      rw [Finset.prod_congr rfl hfac]
      clear hfac hzero
      induction m.support using Finset.induction_on with
      | empty => simp [C_1]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, monomial_mul_monomial, mul_one]
    rw [hprod, C_mul_monomial, mul_one]

/-- An atomic variable substitution never increases the monomial count of a polynomial. -/
theorem AtomSubst.card_support_evalHom_le (ρ : AtomSubst σ τ) (p : MvPolynomial σ ℝ) :
    (ρ.evalHom p).support.card ≤ p.support.card := by
  classical
  have h1 : ρ.evalHom p = ∑ m ∈ p.support, ρ.evalHom (monomial m (p.coeff m)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [h1]
  refine (Finset.card_le_card support_sum).trans (Finset.card_biUnion_le.trans ?_)
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun m _ ↦ ?_
  rcases ρ.evalHom_monomial m (p.coeff m) with h0 | ⟨m', hm'⟩
  · simp [h0]
  · rw [hm']
    exact (Finset.card_le_card support_monomial_subset).trans (by simp)

/-- Polynomial substitution total-degree bound. -/
theorem totalDegree_aeval_le_mul {ρ : σ → MvPolynomial τ ℝ} {k : ℕ}
    (hρ : ∀ i, (ρ i).totalDegree ≤ k) (p : MvPolynomial σ ℝ) :
    (aeval ρ p).totalDegree ≤ p.totalDegree * k := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun m hm ↦ ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ m.support, (ρ i ^ m i).totalDegree
        ≤ ∑ i ∈ m.support, m i * (ρ i).totalDegree :=
      Finset.sum_le_sum fun i _ ↦ totalDegree_pow _ _
    _ ≤ ∑ i ∈ m.support, m i * k :=
      Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_left _ (hρ i)
    _ = (m.sum fun _ e ↦ e) * k := by rw [← Finset.sum_mul]; rfl
    _ ≤ p.totalDegree * k := Nat.mul_le_mul_right k (le_totalDegree hm)

/-- An atomic variable substitution never increases total degree. -/
theorem AtomSubst.totalDegree_evalHom_le (ρ : AtomSubst σ τ) (p : MvPolynomial σ ℝ) :
    (ρ.evalHom p).totalDegree ≤ p.totalDegree := by
  simpa [AtomSubst.evalHom] using totalDegree_aeval_le_mul ρ.totalDegree_toPoly_le p

/-- Applying `ρ : AtomSubst σ τ` to an SoS refutation yields a refutation of `ρ.restrictSystem F`
with no larger degree and no larger monomial size. -/
theorem AtomSubst.mapRefutation (ρ : AtomSubst σ τ) {F : List (MvPolynomial σ ℝ)}
    (π : SosRefutation F) :
    ∃ π' : SosRefutation (ρ.restrictSystem F),
      π'.degree ≤ π.degree ∧ π'.size ≤ π.size := by
  classical
  let G := F.map ρ.evalHom
  have hlen : G.length = F.length := List.length_map _
  let multG (i : Fin G.length) := ρ.evalHom (π.mult (i.cast hlen))
  let sqG := π.squares.map ρ.evalHom
  have heqG : ∑ i : Fin G.length, multG i * G.get i + (sqG.map fun s ↦ s ^ 2).sum = -1 := by
    have heq := congrArg ρ.evalHom π.eq
    simp only [map_add, map_sum, map_mul, map_list_sum, List.map_map, map_neg, map_one] at heq
    rw [← heq]
    congr 1
    · exact Finset.sum_bij (fun (i : Fin G.length) _ ↦ i.cast hlen)
        (fun _ _ ↦ Finset.mem_univ _)
        (fun _ _ _ _ h ↦ Fin.ext (by simpa using congrArg Fin.val h))
        (fun j _ ↦ ⟨j.cast hlen.symm, Finset.mem_univ _, Fin.ext rfl⟩)
        fun i _ ↦ by simp [G, multG]
    · simp [sqG, List.map_map, Function.comp_def, map_pow]
  obtain ⟨hd1, hd2⟩ := SosProof.degree_le_iff.mp (le_refl π.degree)
  let H := ρ.restrictSystem F
  have hmem : ∀ i : Fin G.length, G.get i ≠ 0 → G.get i ∈ H := fun i hne ↦ by
    simp only [H, AtomSubst.restrictSystem, List.mem_filter, decide_eq_true_eq]
    exact ⟨List.get_mem G i, hne⟩
  choose idx hidx using fun p : {i : Fin G.length // G.get i ≠ 0} ↦
    List.mem_iff_get.mp (hmem p.1 p.2)
  let multH : Fin H.length → MvPolynomial τ ℝ :=
    fun j ↦ ∑ p ∈ Finset.univ.filter (idx · = j), multG p.1
  have hmulH (j : Fin H.length) :
      multH j * H.get j = ∑ p ∈ Finset.univ.filter (idx · = j), multG p.1 * G.get p.1 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp ↦ by rw [← (Finset.mem_filter.mp hp).2, hidx p]
  refine ⟨⟨multH, sqG, ?_⟩, SosProof.degree_le_iff.mpr ⟨fun j ↦ ?_, fun s hs ↦ ?_⟩, ?_⟩
  · rw [Finset.sum_congr rfl fun j _ ↦ hmulH j, Finset.sum_fiberwise, ← heqG]
    congr 1
    rw [← Finset.sum_filter_ne_zero (s := Finset.univ)
      (f := fun p : {i : Fin G.length // G.get i ≠ 0} ↦ multG p.1 * G.get p.1)]
    symm
    rw [← Finset.sum_filter_ne_zero (s := Finset.univ) (f := fun i : Fin G.length ↦
      multG i * G.get i)]
    exact Finset.sum_bij (fun i hi ↦ ⟨i, right_ne_zero_of_mul (Finset.mem_filter.mp hi).2⟩)
      (fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
      (fun _ _ _ _ h ↦ congrArg Subtype.val h)
      (fun p hp ↦ ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩,
        Subtype.ext rfl⟩)
      (fun _ _ ↦ rfl)
  · rw [hmulH]
    refine totalDegree_finsetSum_le fun p _ ↦ ?_
    have hget : multG p.1 * G.get p.1 =
        ρ.evalHom (π.mult (p.1.cast hlen) * F.get (p.1.cast hlen)) := by
      simp [G, multG, map_mul]
    rw [hget]
    exact (ρ.totalDegree_evalHom_le _).trans (hd1 _)
  · obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
    exact (Nat.mul_le_mul_left 2 (ρ.totalDegree_evalHom_le s₀)).trans (hd2 s₀ hs₀)
  · refine Nat.add_le_add ?_ ?_
    · calc
        ∑ j : Fin H.length, (multH j).support.card
            ≤ ∑ j : Fin H.length,
                ∑ p ∈ Finset.univ.filter (idx · = j), (multG p.1).support.card :=
          Finset.sum_le_sum fun j _ ↦
            (Finset.card_le_card support_sum).trans Finset.card_biUnion_le
        _ = ∑ p : {i : Fin G.length // G.get i ≠ 0}, (multG p.1).support.card :=
          Finset.sum_fiberwise _ _ _
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin G.length ↦ G.get i ≠ 0),
              (multG i).support.card :=
          (Finset.sum_subtype (Finset.univ.filter fun i : Fin G.length ↦ G.get i ≠ 0)
            (fun _ ↦ by simp) (fun i ↦ (multG i).support.card)).symm
        _ ≤ ∑ i : Fin G.length, (multG i).support.card :=
          Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
        _ ≤ ∑ i : Fin G.length, (π.mult (i.cast hlen)).support.card :=
          Finset.sum_le_sum fun i _ ↦ ρ.card_support_evalHom_le _
        _ = ∑ j : Fin F.length, (π.mult j).support.card :=
          Finset.sum_bij (fun i _ ↦ i.cast hlen) (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ Fin.ext (by simpa using congrArg Fin.val h))
            (fun j _ ↦ ⟨j.cast hlen.symm, Finset.mem_univ _, Fin.ext rfl⟩) (fun _ _ ↦ rfl)
    · dsimp only [sqG]
      rw [List.map_map]
      clear heqG hd2
      induction π.squares with
      | nil => simp
      | cons s ss ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply]
        exact Nat.add_le_add (ρ.card_support_evalHom_le s) ih

/-- Variable substitution monotonicity for SoS refutation degree. -/
theorem sosRefuteDeg_atomSubst_le (ρ : AtomSubst σ τ) (F : List (MvPolynomial σ ℝ)) :
    sosRefuteDeg (ρ.restrictSystem F) ≤ sosRefuteDeg F := by
  refine le_sosRefuteDeg_iff.mpr fun d ⟨π, hπ⟩ ↦ ?_
  obtain ⟨π', hdeg, _⟩ := ρ.mapRefutation π
  exact sosRefuteDeg_le_of_refutable ⟨π', hdeg.trans hπ⟩

/-- Variable substitution monotonicity for SoS refutation monomial size. -/
theorem sosRefuteSize_atomSubst_le (ρ : AtomSubst σ τ) (F : List (MvPolynomial σ ℝ)) :
    sosRefuteSize (ρ.restrictSystem F) ≤ sosRefuteSize F := by
  refine le_sosRefuteSize_iff.mpr fun s ⟨π, hπ⟩ ↦ ?_
  obtain ⟨π', _, hsz⟩ := ρ.mapRefutation π
  exact sosRefuteSize_le_of_refutable ⟨π', hsz.trans hπ⟩

/-- Restrict an equation system `F` by a polynomial substitution `ρ : σ → MvPolynomial τ ℝ`,
removing `0 = 0` equations. -/
@[expose]
noncomputable def restrictPolySubst (ρ : σ → MvPolynomial τ ℝ)
    (F : List (MvPolynomial σ ℝ)) : List (MvPolynomial τ ℝ) := by
  classical
  exact (F.map (aeval ρ)).filter (· ≠ 0)

theorem restrictPolySubst_eq_filter [DecidableEq (MvPolynomial τ ℝ)]
    (ρ : σ → MvPolynomial τ ℝ) (F : List (MvPolynomial σ ℝ)) :
    restrictPolySubst ρ F = (F.map (aeval ρ)).filter (· ≠ 0) := by
  unfold restrictPolySubst; congr 1; funext p; congr 1

/-- Membership in `restrictPolySubst ρ F`: nonzero substituted images of polynomials in `F`. -/
theorem mem_restrictPolySubst_iff {ρ : σ → MvPolynomial τ ℝ}
    {F : List (MvPolynomial σ ℝ)} {g : MvPolynomial τ ℝ} :
    g ∈ restrictPolySubst ρ F ↔ (∃ f ∈ F, aeval ρ f = g) ∧ g ≠ 0 := by
  classical
  simp [restrictPolySubst]

/-- **Polynomial substitution lemma for Sum-of-Squares**: if `F` has a degree-`d` SoS refutation
and every `ρ i` has total degree at most `k`, then `restrictPolySubst ρ F` has an SoS refutation
of degree at most `d * k`. -/
theorem SosRefutableInDegree.polySubst {F : List (MvPolynomial σ ℝ)} {d k : ℕ}
    (h : SosRefutableInDegree F d) {ρ : σ → MvPolynomial τ ℝ}
    (hρ : ∀ i, (ρ i).totalDegree ≤ k) :
    SosRefutableInDegree (restrictPolySubst ρ F) (d * k) := by
  classical
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hmul, hsq⟩ := SosProof.degree_le_iff.mp hπ
  let L : List (MvPolynomial τ ℝ × MvPolynomial τ ℝ) :=
    ((List.finRange F.length).map fun i ↦ (aeval ρ (π.mult i), aeval ρ (F.get i))).filter
      fun p ↦ p.2 ≠ 0
  refine SosRefutableInDegree.of_list L ?_ (π.squares.map (aeval ρ)) ?_ ?_
  · intro p hp
    simp only [L, List.mem_filter, List.mem_map, List.mem_finRange, true_and,
      decide_eq_true_eq] at hp
    obtain ⟨⟨i, rfl⟩, hne⟩ := hp
    refine ⟨?_, ?_⟩
    · simp only [restrictPolySubst, List.mem_filter, decide_eq_true_eq]
      exact ⟨List.mem_map_of_mem (List.get_mem F i), hne⟩
    · rw [← map_mul]
      exact (totalDegree_aeval_le_mul hρ _).trans (Nat.mul_le_mul_right k (hmul i))
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
    calc
      2 * (aeval ρ s₀).totalDegree ≤ 2 * (s₀.totalDegree * k) :=
        Nat.mul_le_mul_left 2 (totalDegree_aeval_le_mul hρ s₀)
      _ = (2 * s₀.totalDegree) * k := (Nat.mul_assoc 2 _ k).symm
      _ ≤ d * k := Nat.mul_le_mul_right k (hsq s₀ hs₀)
  · have heq := congrArg (aeval ρ) π.eq
    simp only [map_add, map_sum, map_mul, map_list_sum, List.map_map, map_neg, map_one] at heq
    rw [← heq]
    congr 1
    · have hfilter : ∀ l : List (MvPolynomial τ ℝ × MvPolynomial τ ℝ),
          ((l.filter fun p ↦ decide (p.2 ≠ 0)).map fun p ↦ p.1 * p.2).sum =
          (l.map fun p ↦ p.1 * p.2).sum := by
        intro l
        induction l with
        | nil => simp
        | cons p ps ih =>
          rw [List.filter_cons, List.map_cons, List.sum_cons]
          split_ifs with h
          · rw [List.map_cons, List.sum_cons, ih]
          · have hp0 : p.2 = 0 := not_ne_iff.mp (fun hne ↦ h (decide_eq_true hne))
            rw [hp0, mul_zero, zero_add, ih]
      rw [hfilter, List.map_map, ← Fin.sum_univ_def]
      rfl
    · simp [List.map_map, Function.comp_def, map_pow]

/-! ### Twin Boolean Literals and Complement-Preserving Variable Substitutions -/

/-- Twin literal variable type `V × Bool`: `(v, false)` is `x_v` and `(v, true)` is `x̄_v`. -/
abbrev Lit (V : Type*) : Type _ := V × Bool

/-- Positive literal `x_v`. -/
@[expose]
def Lit.pos {V : Type*} (v : V) : Lit V := (v, false)

/-- Negated ("bar") literal `x̄_v`. -/
@[expose]
def Lit.neg {V : Type*} (v : V) : Lit V := (v, true)

@[simp] theorem Lit.pos_fst {V : Type*} (v : V) : (Lit.pos v).1 = v := rfl
@[simp] theorem Lit.pos_snd {V : Type*} (v : V) : (Lit.pos v).2 = false := rfl
@[simp] theorem Lit.neg_fst {V : Type*} (v : V) : (Lit.neg v).1 = v := rfl
@[simp] theorem Lit.neg_snd {V : Type*} (v : V) : (Lit.neg v).2 = true := rfl

/-- Pair representation `(v, false)` of `Lit.pos v`. -/
theorem Lit.pos_eq_pair {V : Type*} (v : V) : Lit.pos v = (v, false) := rfl

/-- Pair representation `(v, true)` of `Lit.neg v`. -/
theorem Lit.neg_eq_pair {V : Type*} (v : V) : Lit.neg v = (v, true) := rfl

/-- Formal complement involution swapping `x_v` and `x̄_v`. -/
@[expose]
def Lit.compl {V : Type*} (l : Lit V) : Lit V := (l.1, !l.2)

@[simp]
theorem Lit.compl_pair {V : Type*} (v : V) (b : Bool) : Lit.compl (v, b) = (v, !b) := rfl

theorem Lit.compl_pos {V : Type*} (v : V) : Lit.compl (Lit.pos v) = Lit.neg v := rfl

theorem Lit.compl_neg {V : Type*} (v : V) : Lit.compl (Lit.neg v) = Lit.pos v := rfl

theorem Lit.compl_eq_pair {V : Type*} (l : Lit V) : Lit.compl l = (l.1, !l.2) := rfl

@[simp]
theorem Lit.compl_compl {V : Type*} (l : Lit V) : Lit.compl (Lit.compl l) = l := by
  cases l; simp

/-- Extend `a : V → Bool` to `Lit V → Bool` sending `x_v ↦ a v` and `x̄_v ↦ !(a v)`. -/
@[expose]
def Lit.evalBool {V : Type*} (a : V → Bool) (l : Lit V) : Bool :=
  if l.2 then !(a l.1) else a l.1

theorem Lit.evalBool_eq_ite {V : Type*} (a : V → Bool) (l : Lit V) :
    Lit.evalBool a l = if l.2 then !(a l.1) else a l.1 := rfl

@[simp]
theorem Lit.evalBool_false {V : Type*} (a : V → Bool) (v : V) :
    Lit.evalBool a (v, false) = a v := rfl

@[simp]
theorem Lit.evalBool_true {V : Type*} (a : V → Bool) (v : V) :
    Lit.evalBool a (v, true) = !(a v) := rfl

@[simp]
theorem Lit.evalBool_pos {V : Type*} (a : V → Bool) (v : V) :
    Lit.evalBool a (Lit.pos v) = a v := rfl

@[simp]
theorem Lit.evalBool_neg {V : Type*} (a : V → Bool) (v : V) :
    Lit.evalBool a (Lit.neg v) = !(a v) := rfl

@[simp]
theorem Lit.evalBool_compl {V : Type*} (a : V → Bool) (l : Lit V) :
    Lit.evalBool a l.compl = !(Lit.evalBool a l) := by
  rcases l with ⟨v, _ | _⟩ <;> simp [Lit.evalBool, Lit.compl]

/-- Standard twin Boolean and complementation constraints over a finite variable set `V`:
`x_v ^ 2 - x_v`, `x̄_v ^ 2 - x̄_v`, and `1 - x_v - x̄_v` for every `v : V`. -/
@[expose]
noncomputable def twinBoolAxioms (V : Type*) [Fintype V] :
    List (MvPolynomial (Lit V) ℝ) :=
  Finset.univ.toList.flatMap fun v ↦
    [boolAxiom ℝ (Lit.pos v), boolAxiom ℝ (Lit.neg v),
     1 - X (Lit.pos v) - X (Lit.neg v)]

/-- Membership of `boolAxiom ℝ l` in `twinBoolAxioms V`. -/
theorem boolAxiom_mem_twinBoolAxioms {V : Type*} [Fintype V] (l : Lit V) :
    boolAxiom ℝ l ∈ twinBoolAxioms V := by
  rcases l with ⟨v, _ | _⟩ <;>
    exact List.mem_flatMap.mpr
      ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), by simp [Lit.pos, Lit.neg]⟩

/-- Membership of `1 - x_v - x̄_v` in `twinBoolAxioms V`. -/
theorem complAxiom_mem_twinBoolAxioms {V : Type*} [Fintype V] (v : V) :
    (1 - X (Lit.pos v) - X (Lit.neg v) : MvPolynomial (Lit V) ℝ) ∈ twinBoolAxioms V :=
  List.mem_flatMap.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), by simp⟩

/-- Every constraint in `twinBoolAxioms V` has total degree at most `2`. -/
theorem totalDegree_le_two_of_mem_twinBoolAxioms {V : Type*} [Fintype V]
    {p : MvPolynomial (Lit V) ℝ} (hp : p ∈ twinBoolAxioms V) : p.totalDegree ≤ 2 := by
  obtain ⟨v, _, hm⟩ := List.mem_flatMap.mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact totalDegree_boolAxiom_le _
  · exact totalDegree_boolAxiom_le _
  · refine (totalDegree_sub _ _).trans (max_le ?_ ((totalDegree_var_le _).trans (by omega)))
    exact (totalDegree_sub _ _).trans (max_le (by simp) ((totalDegree_var_le _).trans (by omega)))

/-- Every constraint in `twinBoolAxioms V` vanishes on `boolPoint ℝ (Lit.evalBool a)`. -/
theorem eval_twinBoolAxioms_eq_zero {V : Type*} [Fintype V] (a : V → Bool)
    {p : MvPolynomial (Lit V) ℝ} (hp : p ∈ twinBoolAxioms V) :
    eval (boolPoint ℝ (Lit.evalBool a)) p = 0 := by
  obtain ⟨v, _, hm⟩ := List.mem_flatMap.mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact eval_boolPoint_boolAxiom _ _
  · exact eval_boolPoint_boolAxiom _ _
  · cases h : a v <;> simp [boolPoint, h]

/-- Variable substitution on twin Boolean variables `V → Bool ⊕ Lit V`, extending to `x̄_v` via
`0̄ = 1`, `1̄ = 0`, and `x̿_w = x_w`. -/
abbrev TwinVarSubst (V : Type*) : Type _ := V → Bool ⊕ Lit V

/-- Extend `ρ : TwinVarSubst V` to a complement-respecting `AtomSubst (Lit V) (Lit V)`. -/
@[expose]
def TwinVarSubst.toAtomSubst {V : Type*} (ρ : TwinVarSubst V) : AtomSubst (Lit V) (Lit V)
  | (v, false) => ρ v
  | (v, true) =>
    match ρ v with
    | .inl b => .inl (!b)
    | .inr l => .inr l.compl

@[simp]
theorem TwinVarSubst.toAtomSubst_false {V : Type*} (ρ : TwinVarSubst V) (v : V) :
    ρ.toAtomSubst (v, false) = ρ v := rfl

@[simp]
theorem TwinVarSubst.toAtomSubst_pos {V : Type*} (ρ : TwinVarSubst V) (v : V) :
    ρ.toAtomSubst (Lit.pos v) = ρ v := rfl

theorem TwinVarSubst.toAtomSubst_true_eq {V : Type*} (ρ : TwinVarSubst V) (v : V) :
    ρ.toAtomSubst (v, true) = match ρ v with | .inl b => .inl (!b) | .inr l => .inr l.compl := rfl

theorem TwinVarSubst.toAtomSubst_neg_eq {V : Type*} (ρ : TwinVarSubst V) (v : V) :
    ρ.toAtomSubst (Lit.neg v) = match ρ v with | .inl b => .inl (!b) | .inr l => .inr l.compl := rfl

theorem TwinVarSubst.toAtomSubst_eq_match {V : Type*} (ρ : TwinVarSubst V) (l : Lit V) :
    ρ.toAtomSubst l = match l with
      | (v, false) => ρ v
      | (v, true) => match ρ v with | .inl b => .inl (!b) | .inr l' => .inr l'.compl := by
  rcases l with ⟨v, _ | _⟩ <;> rfl

@[simp]
theorem TwinVarSubst.toAtomSubst_true_of_inl {V : Type*} {ρ : TwinVarSubst V} {v : V} {b : Bool}
    (h : ρ v = .inl b) : ρ.toAtomSubst (v, true) = .inl (!b) := by
  simp [TwinVarSubst.toAtomSubst, h]

@[simp]
theorem TwinVarSubst.toAtomSubst_true_of_inr {V : Type*} {ρ : TwinVarSubst V} {v : V} {l : Lit V}
    (h : ρ v = .inr l) : ρ.toAtomSubst (v, true) = .inr l.compl := by
  simp [TwinVarSubst.toAtomSubst, h]

@[simp]
theorem TwinVarSubst.toAtomSubst_neg_of_inl {V : Type*} {ρ : TwinVarSubst V} {v : V} {b : Bool}
    (h : ρ v = .inl b) : ρ.toAtomSubst (Lit.neg v) = .inl (!b) :=
  TwinVarSubst.toAtomSubst_true_of_inl h

@[simp]
theorem TwinVarSubst.toAtomSubst_neg_of_inr {V : Type*} {ρ : TwinVarSubst V} {v : V} {l : Lit V}
    (h : ρ v = .inr l) : ρ.toAtomSubst (Lit.neg v) = .inr l.compl :=
  TwinVarSubst.toAtomSubst_true_of_inr h

/-- Evaluate `ρ : TwinVarSubst V` on a base variable `v : V` under a total assignment
`σ : V → Bool`. -/
@[expose]
def TwinVarSubst.evalBool {V : Type*} (ρ : TwinVarSubst V) (σ : V → Bool) (v : V) : Bool :=
  match ρ v with
  | .inl b => b
  | .inr l => Lit.evalBool σ l

theorem TwinVarSubst.evalBool_eq_match {V : Type*} (ρ : TwinVarSubst V) (σ : V → Bool) (v : V) :
    ρ.evalBool σ v = match ρ v with | .inl b => b | .inr l => Lit.evalBool σ l := rfl

@[simp]
theorem TwinVarSubst.evalBool_of_inl {V : Type*} {ρ : TwinVarSubst V} (σ : V → Bool) {v : V}
    {b : Bool} (h : ρ v = .inl b) : ρ.evalBool σ v = b := by
  simp [TwinVarSubst.evalBool, h]

@[simp]
theorem TwinVarSubst.evalBool_of_inr {V : Type*} {ρ : TwinVarSubst V} (σ : V → Bool) {v : V}
    {l : Lit V} (h : ρ v = .inr l) : ρ.evalBool σ v = Lit.evalBool σ l := by
  simp [TwinVarSubst.evalBool, h]

/-- Evaluating a restricted polynomial `ρ.toAtomSubst.evalHom p` at `boolPoint ℝ (Lit.evalBool σ)`
equals evaluating `p` at `boolPoint ℝ (Lit.evalBool (ρ.evalBool σ))`. -/
@[simp]
theorem TwinVarSubst.eval_evalHom {V : Type*} (ρ : TwinVarSubst V) (σ : V → Bool)
    (p : MvPolynomial (Lit V) ℝ) :
    eval (boolPoint ℝ (Lit.evalBool σ)) (ρ.toAtomSubst.evalHom p) =
      eval (boolPoint ℝ (Lit.evalBool (ρ.evalBool σ))) p := by
  have heq : (eval (boolPoint ℝ (Lit.evalBool σ))).comp ρ.toAtomSubst.evalHom.toRingHom =
      eval (boolPoint ℝ (Lit.evalBool (ρ.evalBool σ))) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp [AtomSubst.evalHom]) ?_
    rintro ⟨v, _ | _⟩
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AtomSubst.evalHom, aeval_X, eval_X]
      rcases h : ρ v with (_ | _) | l <;>
        simp [TwinVarSubst.toAtomSubst, TwinVarSubst.evalBool, Lit.evalBool, AtomSubst.toPoly,
          boolPoint, h]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AtomSubst.evalHom, aeval_X, eval_X]
      rcases h : ρ v with (_ | _) | ⟨w, _ | _⟩ <;>
        simp [TwinVarSubst.toAtomSubst, TwinVarSubst.evalBool, Lit.compl, Lit.evalBool,
          AtomSubst.toPoly, boolPoint, h]
  exact RingHom.congr_fun heq p

/-- Restrict a twin-variable polynomial system `F` by `ρ : TwinVarSubst V`, dropping `0 = 0`. -/
@[expose]
noncomputable def TwinVarSubst.restrict {V : Type*} (ρ : TwinVarSubst V)
    (F : List (MvPolynomial (Lit V) ℝ)) : List (MvPolynomial (Lit V) ℝ) :=
  ρ.toAtomSubst.restrictSystem F

theorem TwinVarSubst.restrict_eq_restrictSystem {V : Type*} (ρ : TwinVarSubst V)
    (F : List (MvPolynomial (Lit V) ℝ)) : ρ.restrict F = ρ.toAtomSubst.restrictSystem F := rfl

/-- Membership in `ρ.restrict F`: nonzero substituted images of polynomials in `F`. -/
theorem TwinVarSubst.mem_restrict_iff {V : Type*} (ρ : TwinVarSubst V)
    {F : List (MvPolynomial (Lit V) ℝ)} {g : MvPolynomial (Lit V) ℝ} :
    g ∈ ρ.restrict F ↔ (∃ f ∈ F, ρ.toAtomSubst.evalHom f = g) ∧ g ≠ 0 :=
  ρ.toAtomSubst.mem_restrictSystem_iff

@[simp]
theorem TwinVarSubst.restrict_append {V : Type*} (ρ : TwinVarSubst V)
    (F G : List (MvPolynomial (Lit V) ℝ)) :
    ρ.restrict (F ++ G) = ρ.restrict F ++ ρ.restrict G :=
  ρ.toAtomSubst.restrictSystem_append F G

/-- Composition of two twin variable substitutions: restricting by `τ` and then by `ρ` equals
restricting by `ρ.comp τ`. -/
@[expose]
def TwinVarSubst.comp {V : Type*} (ρ τ : TwinVarSubst V) : TwinVarSubst V := fun v ↦
  match τ v with
  | .inl b => .inl b
  | .inr l => ρ.toAtomSubst l

theorem TwinVarSubst.comp_eq_match {V : Type*} (ρ τ : TwinVarSubst V) (v : V) :
    (ρ.comp τ) v = match τ v with | .inl b => .inl b | .inr l => ρ.toAtomSubst l := rfl

@[simp]
theorem TwinVarSubst.comp_of_inl {V : Type*} (ρ : TwinVarSubst V) {τ : TwinVarSubst V} {v : V}
    {b : Bool} (h : τ v = .inl b) : (ρ.comp τ) v = .inl b := by
  simp [TwinVarSubst.comp, h]

@[simp]
theorem TwinVarSubst.comp_of_inr {V : Type*} (ρ : TwinVarSubst V) {τ : TwinVarSubst V} {v : V}
    {l : Lit V} (h : τ v = .inr l) : (ρ.comp τ) v = ρ.toAtomSubst l := by
  simp [TwinVarSubst.comp, h]

@[simp]
theorem TwinVarSubst.evalHom_comp {V : Type*} (ρ τ : TwinVarSubst V)
    (p : MvPolynomial (Lit V) ℝ) :
    (ρ.comp τ).toAtomSubst.evalHom p = ρ.toAtomSubst.evalHom (τ.toAtomSubst.evalHom p) := by
  have heq : (ρ.comp τ).toAtomSubst.evalHom =
      ρ.toAtomSubst.evalHom.comp τ.toAtomSubst.evalHom := by
    refine MvPolynomial.algHom_ext ?_
    rintro ⟨v, _ | _⟩
    · simp only [AlgHom.comp_apply, AtomSubst.evalHom, aeval_X]
      rcases h : τ v with (_ | _) | l <;>
        simp [TwinVarSubst.toAtomSubst, TwinVarSubst.comp, AtomSubst.toPoly, h]
    · simp only [AlgHom.comp_apply, AtomSubst.evalHom, aeval_X]
      rcases h : τ v with (_ | _) | ⟨w, _ | _⟩
      · simp [TwinVarSubst.toAtomSubst, TwinVarSubst.comp, AtomSubst.toPoly, h]
      · simp [TwinVarSubst.toAtomSubst, TwinVarSubst.comp, AtomSubst.toPoly, h]
      · simp [TwinVarSubst.toAtomSubst, TwinVarSubst.comp, AtomSubst.toPoly, Lit.compl, h]
      · rcases h' : ρ w with (_ | _) | ⟨u, _ | _⟩ <;>
          simp [TwinVarSubst.toAtomSubst, TwinVarSubst.comp, AtomSubst.toPoly, Lit.compl, h, h']
  exact AlgHom.congr_fun heq p

/-- Restricting sequentially by `τ` then `ρ` produces the exact same polynomial system as
`(ρ.comp τ).restrict`. -/
theorem TwinVarSubst.restrict_restrict {V : Type*} (ρ τ : TwinVarSubst V)
    (F : List (MvPolynomial (Lit V) ℝ)) :
    ρ.restrict (τ.restrict F) = (ρ.comp τ).restrict F := by
  simp only [TwinVarSubst.restrict, AtomSubst.restrictSystem]
  induction F with
  | nil => simp
  | cons f fs ih =>
    rw [List.map_cons, List.filter_cons, List.map_cons, List.filter_cons,
      TwinVarSubst.evalHom_comp]
    split_ifs with h1 h2 h2
    · rw [List.map_cons, List.filter_cons, ite_eq_left h2, ih]
    · rw [List.map_cons, List.filter_cons, ite_eq_right h2, ih]
    · have hf0 : τ.toAtomSubst.evalHom f = 0 := by
        simpa [decide_eq_true_eq] using h1
      have hne : ρ.toAtomSubst.evalHom (τ.toAtomSubst.evalHom f) ≠ 0 := by
        simpa [decide_eq_true_eq] using h2
      exact absurd (by rw [hf0, map_zero]) hne
    · exact ih

/-- Active ("unset") base variables occurring in a twin-variable polynomial system `F`. -/
noncomputable def activeTwinVars {V : Type*} [DecidableEq V]
    (F : List (MvPolynomial (Lit V) ℝ)) : Finset V :=
  (F.toFinset.biUnion MvPolynomial.vars).image Prod.fst

/-- Membership of occurring literal base variables in `activeTwinVars F`. -/
theorem fst_mem_activeTwinVars {V : Type*} [DecidableEq V]
    {F : List (MvPolynomial (Lit V) ℝ)} {f : MvPolynomial (Lit V) ℝ} (hf : f ∈ F)
    {l : Lit V} (hl : l ∈ f.vars) : l.1 ∈ activeTwinVars F :=
  Finset.mem_image.mpr ⟨l, Finset.mem_biUnion.mpr ⟨f, List.mem_toFinset.mpr hf, hl⟩, rfl⟩

/-- Restricting by a twin variable substitution `ρ` never increases SoS refutation degree or
monomial size. -/
theorem twinVarSubst_refuteDeg_and_size_le {V : Type*} (ρ : TwinVarSubst V)
    (F : List (MvPolynomial (Lit V) ℝ)) :
    sosRefuteDeg (ρ.restrict F) ≤ sosRefuteDeg F ∧
    sosRefuteSize (ρ.restrict F) ≤ sosRefuteSize F :=
  ⟨sosRefuteDeg_atomSubst_le ρ.toAtomSubst F, sosRefuteSize_atomSubst_le ρ.toAtomSubst F⟩

end SosDefs

end CslibFrontier.ProofComplexity
