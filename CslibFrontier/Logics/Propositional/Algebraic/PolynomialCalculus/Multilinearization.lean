module

public import CslibFrontier.Logics.Propositional.Algebraic.Boolean
public import CslibFrontier.Logics.Propositional.Algebraic.CNF.PCR
public import CslibFrontier.Logics.Propositional.Algebraic.CNF.Boolean
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# Multilinearization of Multivariate Polynomials and Polynomial Calculus Proofs

This module defines the multilinearization linear operator on multivariate polynomials over a
commutative ring and proves its algebraic characterization and application to algebraic proof
systems:

* `IsMultilinear` and `multilinearize`: reducing every positive variable exponent to `1`, proved
  idempotent, preserving evaluation on the Boolean hypercube `{0, 1}^V`, unique modulo the Boolean
  ideal, and satisfying the variable-splitting identity for `X r * p`.
* `substZero` and `substOne`: single-variable `0`/`1` restrictions preserving multilinearity.
* `multilinear_pcr_of_pc`: transforming any Polynomial Calculus (`PC`) proof from multilinear
  initial axioms into a strictly multilinear Polynomial Calculus with Resolution (`PCR`) proof of
  size `O((n + 1) * (PC.size ls + ls.length))`.

## Main definitions

* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.IsMultilinear`,
  `multilinearize`: multilinear polynomials and the multilinearization operator.
* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.substZero`, `substOne`:
  single-variable Boolean restrictions.
* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.multilinearPCRAxioms`:
  multilinear complementarity axioms for `PCR`.

## Main results

* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.eq_multilinearize_iff`:
  uniqueness modulo the Boolean ideal.
* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.multilinearize_X_mul`:
  single-variable multilinearization step identity.
* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.multilinear_pcr_of_pc`:
  polynomial-size multilinearization of `PC` proofs into `PCR`.
-/

public section

namespace CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus

open MvPolynomial Cslib.Logic.PL Cslib.Logic.PL.Algebraic Cslib.BitString

/-! ### Multilinearization operator on multivariate polynomials -/

section Multilinearization

variable {V F : Type*} [CommRing F]

private theorem support_add_subset [DecidableEq V] {p q : MvPolynomial V F} :
    (p + q).support ⊆ p.support ∪ q.support := by
  intro m hm
  by_contra h
  simp only [Finset.mem_union, mem_support_iff, not_or, not_not] at h hm
  exact hm (by simp [h.1, h.2])

private theorem support_sub_subset [DecidableEq V] {p q : MvPolynomial V F} :
    (p - q).support ⊆ p.support ∪ q.support := by
  intro m hm
  by_contra h
  simp only [Finset.mem_union, mem_support_iff, not_or, not_not] at h hm
  exact hm (by simp [h.1, h.2])

private theorem support_smul_subset {a : F} {p : MvPolynomial V F} :
    (C a * p).support ⊆ p.support := by
  intro m hm
  rw [mem_support_iff, coeff_C_mul] at hm
  exact mem_support_iff.2 (right_ne_zero_of_mul hm)

/-- A commutative polynomial `p` is **multilinear** if every variable has exponent at most `1` in
every supported monomial. -/
@[expose] def IsMultilinear (p : MvPolynomial V F) : Prop :=
  ∀ m ∈ p.support, ∀ v : V, m v ≤ 1

/-- Clamp every variable exponent in a monomial `m` to `{0, 1}`. -/
@[expose] noncomputable def multilinExp (m : V →₀ ℕ) : V →₀ ℕ :=
  m.mapRange (fun k => if k = 0 then 0 else 1) (by simp)

/-- Value of `multilinExp m` at a variable `v`. -/
@[simp] theorem multilinExp_apply (m : V →₀ ℕ) (v : V) :
    multilinExp m v = if m v = 0 then 0 else 1 := rfl

/-- `multilinExp` is idempotent. -/
@[simp] theorem multilinExp_idem (m : V →₀ ℕ) : multilinExp (multilinExp m) = multilinExp m := by
  ext v
  simp only [multilinExp_apply]
  by_cases h : m v = 0 <;> simp [h]

/-- `multilinExp m` has every exponent `≤ 1`. -/
theorem multilinExp_le_one (m : V →₀ ℕ) (v : V) : multilinExp m v ≤ 1 := by
  simp only [multilinExp_apply]; split_ifs <;> omega

/-- `multilinExp (0) = 0`. -/
@[simp] theorem multilinExp_zero : multilinExp (0 : V →₀ ℕ) = 0 := by
  ext v; simp

/-- `multilinExp (Finsupp.single v 1) = Finsupp.single v 1`. -/
@[simp] theorem multilinExp_single_one (v : V) :
    multilinExp (Finsupp.single v 1) = Finsupp.single v 1 := by
  classical
  ext u
  by_cases huv : u = v
  · subst huv; simp
  · simp [Finsupp.single_eq_of_ne huv]

/-- `multilinExp (m₁ + m₂) = multilinExp (m₁ + multilinExp m₂)`. -/
theorem multilinExp_add_right (m₁ m₂ : V →₀ ℕ) :
    multilinExp (m₁ + multilinExp m₂) = multilinExp (m₁ + m₂) := by
  ext v
  simp only [multilinExp_apply, Finsupp.add_apply]
  by_cases h1 : m₁ v = 0 <;> by_cases h2 : m₂ v = 0 <;> simp [h1, h2]

/-- The multilinearization linear operator `multilinearize`, mapping
each monomial `∏ x_i^{e_i}` to `∏_{e_i ≥ 1} x_i`. -/
noncomputable def multilinearize : MvPolynomial V F →ₗ[F] MvPolynomial V F where
  toFun p := ∑ m ∈ p.support, monomial (multilinExp m) (p.coeff m)
  map_add' p q := by
    classical
    let S := p.support ∪ q.support
    have h1 : ∀ f : MvPolynomial V F, f.support ⊆ S →
        ∑ m ∈ f.support, monomial (multilinExp m) (f.coeff m) =
          ∑ m ∈ S, monomial (multilinExp m) (f.coeff m) := fun f hf =>
      Finset.sum_subset hf fun m _ hnot => by simp [notMem_support_iff.1 hnot]
    rw [h1 (p + q) support_add_subset, h1 p Finset.subset_union_left,
      h1 q Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => by simp [map_add]
  map_smul' a p := by
    classical
    simp only [RingHom.id_apply]
    have hsub : (a • p).support ⊆ p.support := by
      intro m hm
      rw [mem_support_iff, coeff_smul, smul_eq_mul] at hm
      exact mem_support_iff.2 (right_ne_zero_of_mul hm)
    rw [Finset.sum_subset hsub (fun m _ hnot => by rw [notMem_support_iff.1 hnot, map_zero]),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => by
      rw [coeff_smul, smul_monomial]

/-- Action of `multilinearize` on a monomial. -/
@[simp] theorem multilinearize_monomial (m : V →₀ ℕ) (c : F) :
    multilinearize (monomial m c) = monomial (multilinExp m) c := by
  classical
  change ∑ m' ∈ (monomial m c).support, monomial (multilinExp m') ((monomial m c).coeff m') = _
  by_cases hc : c = 0
  · subst hc; simp
  · rw [support_monomial]
    simp only [hc, ↓reduceIte, Finset.sum_singleton, coeff_monomial, ↓reduceIte]

/-- `multilinearize (C a) = C a`. -/
@[simp] theorem multilinearize_C (a : F) : multilinearize (C a : MvPolynomial V F) = C a := by
  rw [← monomial_zero', multilinearize_monomial, multilinExp_zero]

/-- `multilinearize 1 = 1`. -/
@[simp] theorem multilinearize_one : multilinearize (1 : MvPolynomial V F) = 1 := by
  simpa using multilinearize_C (V := V) (1 : F)

/-- `multilinearize (X v) = X v`. -/
@[simp] theorem multilinearize_X (v : V) : multilinearize (X v : MvPolynomial V F) = X v := by
  rw [X, multilinearize_monomial, multilinExp_single_one]

/-- Support of `multilinearize p` lies inside the image of `p.support` under `multilinExp`. -/
theorem support_multilinearize_subset [DecidableEq V] (p : MvPolynomial V F) :
    (multilinearize p).support ⊆ p.support.image multilinExp := by
  intro m hm
  change m ∈ (∑ m' ∈ p.support, monomial (multilinExp m') (p.coeff m')).support at hm
  obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
  exact Finset.mem_image.2 ⟨m', hm', (Finset.mem_singleton.1 (support_monomial_subset hmem)).symm⟩

/-- Every supported monomial of `multilinearize p` is multilinear. -/
theorem isMultilinear_multilinearize (p : MvPolynomial V F) :
    IsMultilinear (multilinearize p) := by
  classical
  intro m hm v
  obtain ⟨m', _, rfl⟩ := Finset.mem_image.1 (support_multilinearize_subset p hm)
  exact multilinExp_le_one m' v

/-- Support size never grows under `multilinearize`. -/
theorem card_support_multilinearize_le (p : MvPolynomial V F) :
    (multilinearize p).support.card ≤ p.support.card := by
  classical
  exact (Finset.card_le_card (support_multilinearize_subset p)).trans Finset.card_image_le

/-- `multilinearize` fixes every multilinear polynomial. -/
theorem multilinearize_eq_self_of_isMultilinear {p : MvPolynomial V F} (hp : IsMultilinear p) :
    multilinearize p = p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [multilinearize_monomial]
  have hmeq : multilinExp m = m := by
    ext v
    have hv := hp m hm v
    simp only [multilinExp_apply]
    split_ifs <;> omega
  rw [hmeq]

/-- `multilinearize` is idempotent. -/
@[simp] theorem multilinearize_idempotent (p : MvPolynomial V F) :
    multilinearize (multilinearize p) = multilinearize p :=
  multilinearize_eq_self_of_isMultilinear (isMultilinear_multilinearize p)

/-- `multilinearize (p * multilinearize q) = multilinearize (p * q)`. -/
theorem multilinearize_mul_multilinearize_right (p q : MvPolynomial V F) :
    multilinearize (p * multilinearize q) = multilinearize (p * q) := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  conv_rhs => rw [p.as_sum, q.as_sum]
  rw [map_sum, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [multilinearize_monomial, monomial_mul_monomial, monomial_mul_monomial,
    multilinearize_monomial, multilinearize_monomial, multilinExp_add_right]

/-- `multilinearize (multilinearize p * q) = multilinearize (p * q)`. -/
theorem multilinearize_mul_multilinearize_left (p q : MvPolynomial V F) :
    multilinearize (multilinearize p * q) = multilinearize (p * q) := by
  rw [mul_comm, multilinearize_mul_multilinearize_right, mul_comm]

/-- `multilinearize` agrees with `p` on every Boolean assignment `σ : V → Bool`. -/
theorem eval_bitPoint_multilinearize (σ : V → Bool) (p : MvPolynomial V F) :
    eval (bitPoint σ) (multilinearize p) = eval (bitPoint σ) p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [multilinearize_monomial, eval_monomial, eval_monomial]
  congr 1
  rw [Finsupp.prod, Finsupp.prod]
  have hsupp : (multilinExp m).support = m.support := by
    ext v; simp [Finsupp.mem_support_iff]
  rw [hsupp]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hne : m v ≠ 0 := Finsupp.mem_support_iff.1 hv
  simp only [multilinExp_apply, hne, ↓reduceIte, pow_one, bitPoint, bitVal]
  cases σ v
  · exact (zero_pow hne).symm
  · exact (one_pow _).symm

/-- `multilinearize (boolAxiom v) = 0`. -/
@[simp] theorem multilinearize_boolAxiom (v : V) :
    multilinearize (boolAxiom v : MvPolynomial V F) = 0 := by
  classical
  rw [boolAxiom, map_sub, X, pow_two, monomial_mul_monomial, one_mul, multilinearize_monomial,
    multilinearize_monomial]
  have h : multilinExp (Finsupp.single v 1 + Finsupp.single v 1) =
      multilinExp (Finsupp.single v 1) := by
    ext u
    by_cases huv : u = v
    · subst huv; simp
    · simp [Finsupp.single_eq_of_ne huv]
  rw [h, sub_self]

/-- Single-variable restriction substituting `0` for `r`. -/
@[expose] noncomputable def substZero [DecidableEq V] (r : V) :
    MvPolynomial V F →ₐ[F] MvPolynomial V F :=
  MvPolynomial.aeval (Function.update X r 0)

/-- Single-variable restriction substituting `1` for `r`. -/
@[expose] noncomputable def substOne [DecidableEq V] (r : V) :
    MvPolynomial V F →ₐ[F] MvPolynomial V F :=
  MvPolynomial.aeval (Function.update X r 1)

/-- Action of `substZero r` on `X v`. -/
@[simp] theorem substZero_X [DecidableEq V] (r v : V) :
    substZero r (X v : MvPolynomial V F) = if v = r then 0 else X v := by
  simp [substZero, Function.update]

/-- Action of `substOne r` on `X v`. -/
@[simp] theorem substOne_X [DecidableEq V] (r v : V) :
    substOne r (X v : MvPolynomial V F) = if v = r then 1 else X v := by
  simp [substOne, Function.update]

/-- Action of `substZero r` on a monomial. -/
theorem substZero_monomial [DecidableEq V] (r : V) (m : V →₀ ℕ) (c : F) :
    substZero r (monomial m c) = if m r = 0 then monomial m c else 0 := by
  rw [monomial_eq, map_mul, show substZero r (C c) = C c by simp [substZero], Finsupp.prod,
    map_prod]
  by_cases hmr : m r = 0
  · simp only [hmr, ↓reduceIte]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvr : v ≠ r := fun h => Finsupp.mem_support_iff.1 hv (h ▸ hmr)
    simp [hvr]
  · simp only [hmr, ↓reduceIte]
    have hmem : r ∈ m.support := Finsupp.mem_support_iff.2 hmr
    rw [Finset.prod_eq_zero hmem (by simp [zero_pow hmr]), mul_zero]

/-- Action of `substOne r` on a monomial. -/
theorem substOne_monomial [DecidableEq V] (r : V) (m : V →₀ ℕ) (c : F) :
    substOne r (monomial m c) = monomial (m.erase r) c := by
  rw [monomial_eq, monomial_eq, map_mul, show substOne r (C c) = C c by simp [substOne]]
  congr 1
  rw [Finsupp.prod, Finsupp.prod, map_prod, Finsupp.support_erase]
  by_cases hmem : r ∈ m.support
  · rw [← Finset.mul_prod_erase m.support _ hmem]
    simp only [map_pow, substOne_X, ↓reduceIte, one_pow, one_mul]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvr : v ≠ r := (Finset.mem_erase.1 hv).1
    simp [hvr, Finsupp.erase_ne hvr]
  · rw [Finset.erase_eq_of_notMem hmem]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvr : v ≠ r := fun h => hmem (h ▸ hv)
    simp [hvr, Finsupp.erase_ne hvr]

/-- `substZero r` preserves multilinearity. -/
theorem isMultilinear_substZero [DecidableEq V] (r : V) {p : MvPolynomial V F}
    (hp : IsMultilinear p) : IsMultilinear (substZero r p) := by
  intro m hm v
  rw [p.as_sum, map_sum] at hm
  obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [substZero_monomial] at hmem
  split_ifs at hmem with h0
  · have hm_eq := Finset.mem_singleton.1 (support_monomial_subset hmem)
    rw [hm_eq]
    exact hp m' hm' v
  · simp at hmem

/-- `substOne r` preserves multilinearity. -/
theorem isMultilinear_substOne [DecidableEq V] (r : V) {p : MvPolynomial V F}
    (hp : IsMultilinear p) : IsMultilinear (substOne r p) := by
  intro m hm v
  rw [p.as_sum, map_sum] at hm
  obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [substOne_monomial] at hmem
  have hm_eq := Finset.mem_singleton.1 (support_monomial_subset hmem)
  rw [hm_eq]
  by_cases hvr : v = r
  · subst hvr; simp
  · rw [Finsupp.erase_ne hvr]; exact hp m' hm' v

/-- `substZero r p` does not contain variable `r` in any supported monomial. -/
theorem coeff_substZero_eq_zero_of_pos [DecidableEq V] (r : V) (p : MvPolynomial V F)
    {m : V →₀ ℕ} (hm : m ∈ (substZero r p).support) : m r = 0 := by
  rw [p.as_sum, map_sum] at hm
  obtain ⟨m', _, hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [substZero_monomial] at hmem
  split_ifs at hmem with h0
  · rw [Finset.mem_singleton.1 (support_monomial_subset hmem)]; exact h0
  · simp at hmem

/-- `substOne r p` does not contain variable `r` in any supported monomial. -/
theorem coeff_substOne_eq_zero_of_pos [DecidableEq V] (r : V) (p : MvPolynomial V F)
    {m : V →₀ ℕ} (hm : m ∈ (substOne r p).support) : m r = 0 := by
  rw [p.as_sum, map_sum] at hm
  obtain ⟨m', _, hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [substOne_monomial] at hmem
  rw [Finset.mem_singleton.1 (support_monomial_subset hmem)]
  simp

/-- Variable-splitting decomposition of any multilinear polynomial:
`p = p|_{r=0} + X r * (p|_{r=1} - p|_{r=0})`. -/
theorem isMultilinear_decomp [DecidableEq V] {p : MvPolynomial V F} (hp : IsMultilinear p) (r : V) :
    p = substZero r p + X r * (substOne r p - substZero r p) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [substZero_monomial, substOne_monomial]
  have hmr : m r ≤ 1 := hp m hm r
  by_cases h0 : m r = 0
  · have herase : m.erase r = m := Finsupp.erase_of_notMem_support (by simp [h0])
    simp only [h0, ↓reduceIte, herase, sub_self, mul_zero, add_zero]
  · have h1 : m r = 1 := by omega
    have hadd : Finsupp.single r 1 + m.erase r = m := by
      ext v
      by_cases hvr : v = r
      · subst hvr; simp [h1]
      · simp [Finsupp.single_eq_of_ne hvr, Finsupp.erase_ne hvr]
    simp only [h0, ↓reduceIte, sub_zero, zero_add, X, monomial_mul_monomial, one_mul, hadd]

/-- `substZero r` commutes with `multilinearize`. -/
theorem substZero_multilinearize [DecidableEq V] (r : V) (p : MvPolynomial V F) :
    substZero r (multilinearize p) = multilinearize (substZero r p) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [multilinearize_monomial, substZero_monomial, substZero_monomial]
  by_cases h0 : m r = 0 <;> simp [h0]

/-- `substOne r` commutes with `multilinearize`. -/
theorem substOne_multilinearize [DecidableEq V] (r : V) (p : MvPolynomial V F) :
    substOne r (multilinearize p) = multilinearize (substOne r p) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [multilinearize_monomial, substOne_monomial, substOne_monomial, multilinearize_monomial]
  have heq : (multilinExp m).erase r = multilinExp (m.erase r) := by
    ext v
    by_cases hvr : v = r
    · subst hvr; simp
    · simp [Finsupp.erase_ne hvr]
  rw [heq]

/-- **Key multilinearization multiplication identity**:
`M[X r * p] = X r * M[p] - (X r^2 - X r) * (M[p]|_{r=1} - M[p]|_{r=0})`. -/
theorem multilinearize_X_mul [DecidableEq V] (r : V) (p : MvPolynomial V F) :
    multilinearize (X r * p) =
      X r * multilinearize p -
        boolAxiom r * (substOne r (multilinearize p) - substZero r (multilinearize p)) := by
  rw [← multilinearize_mul_multilinearize_right]
  set q := multilinearize p
  have hq : IsMultilinear q := isMultilinear_multilinearize p
  set A := substZero r q
  set B := substOne r q - substZero r q
  have hdecomp : q = A + X r * B := isMultilinear_decomp hq r
  have hB_no_r : ∀ m ∈ B.support, m r = 0 := by
    intro m hm
    rcases Finset.mem_union.1 (support_sub_subset hm) with h1 | h2
    · exact coeff_substOne_eq_zero_of_pos r q h1
    · exact coeff_substZero_eq_zero_of_pos r q h2
  have hA_no_r : ∀ m ∈ A.support, m r = 0 := fun m hm => coeff_substZero_eq_zero_of_pos r q hm
  have hA_ml : IsMultilinear A := isMultilinear_substZero r hq
  have hB_ml : IsMultilinear B := fun m hm v => by
    rcases Finset.mem_union.1 (support_sub_subset hm) with h1 | h2
    · exact isMultilinear_substOne r hq m h1 v
    · exact isMultilinear_substZero r hq m h2 v
  have hmul_ml : ∀ g : MvPolynomial V F, IsMultilinear g → (∀ m ∈ g.support, m r = 0) →
      IsMultilinear (X r * g) := by
    intro g hg hno m hm v
    rw [support_X_mul] at hm
    obtain ⟨m', hm', rfl⟩ := Finset.mem_map.1 hm
    change (Finsupp.single r (1 : ℕ) + m') v ≤ 1
    rw [Finsupp.add_apply]
    by_cases hvr : v = r
    · subst hvr
      simp [Finsupp.single_eq_same, hno m' hm']
    · rw [Finsupp.single_eq_of_ne hvr, zero_add]; exact hg m' hm' v
  have hX2B : multilinearize (X r * (X r * B)) = X r * B := by
    have hsub_eq : multilinearize (X r * (X r * B)) - multilinearize (X r * B) =
        multilinearize (boolAxiom r * B) := by
      rw [← map_sub]; congr 1; simp [boolAxiom]; ring
    have hzero : multilinearize (boolAxiom r * B) = 0 := by
      rw [← multilinearize_mul_multilinearize_left, multilinearize_boolAxiom, zero_mul, map_zero]
    rw [hzero, sub_eq_zero] at hsub_eq
    rw [hsub_eq, multilinearize_eq_self_of_isMultilinear (hmul_ml B hB_ml hB_no_r)]
  calc multilinearize (X r * q)
      = multilinearize (X r * A + X r * (X r * B)) := by rw [hdecomp, mul_add]
    _ = multilinearize (X r * A) + multilinearize (X r * (X r * B)) := map_add _ _ _
    _ = X r * A + X r * B := by
        rw [multilinearize_eq_self_of_isMultilinear (hmul_ml A hA_ml hA_no_r), hX2B]
    _ = X r * (A + X r * B) - boolAxiom r * B := by simp [boolAxiom]; ring
    _ = X r * q - boolAxiom r * B := by rw [← hdecomp]

/-- A multilinear polynomial that vanishes on all `{0, 1}`-assignments is identically `0` (over any
commutative ring). -/
theorem eq_zero_of_isMultilinear_of_eval_bitPoint_eq_zero
    {p : MvPolynomial V F} (hp : IsMultilinear p)
    (heval : ∀ σ : V → Bool, eval (bitPoint σ) p = 0) : p = 0 := by
  classical
  have hcoeff : ∀ k : ℕ, ∀ m : V →₀ ℕ, (∀ v, m v ≤ 1) → m.support.card = k → p.coeff m = 0 := by
    intro k
    refine Nat.strongRecOn k fun k ih m hm1 hk => ?_
    let σ : V → Bool := fun v => decide (v ∈ m.support)
    have h0 := heval σ
    rw [p.as_sum, map_sum] at h0
    have hterm : ∀ m' ∈ p.support,
        eval (bitPoint σ) (monomial m' (p.coeff m')) =
          if m'.support ⊆ m.support then p.coeff m' else 0 := by
      intro m' hm'
      rw [eval_monomial, Finsupp.prod]
      by_cases hsub : m'.support ⊆ m.support
      · simp only [hsub, ↓reduceIte]
        have hprod1 : ∏ v ∈ m'.support, (bitPoint σ v : F) ^ m' v = 1 :=
          Finset.prod_eq_one fun v hv => by
            have hne : m v ≠ 0 := Finsupp.mem_support_iff.1 (hsub hv)
            simp [σ, bitPoint, bitVal, hne]
        rw [hprod1, mul_one]
      · simp only [hsub, ↓reduceIte]
        obtain ⟨v, hv1, hv2⟩ := Finset.not_subset.1 hsub
        have hpos : m' v ≠ 0 := Finsupp.mem_support_iff.1 hv1
        have hz : m v = 0 := Finsupp.notMem_support_iff.1 hv2
        have hprod0 : ∏ u ∈ m'.support, (bitPoint σ u : F) ^ m' u = 0 :=
          Finset.prod_eq_zero hv1 (by simp [σ, bitPoint, bitVal, hz, zero_pow hpos])
        rw [hprod0, mul_zero]
    rw [Finset.sum_congr rfl hterm] at h0
    have hsingle : ∑ m' ∈ p.support, (if m'.support ⊆ m.support then p.coeff m' else 0) =
        p.coeff m := by
      by_cases hm_mem : m ∈ p.support
      · rw [Finset.sum_eq_single m]
        · simp
        · intro m' hm' hne
          split_ifs with hsub
          · have hlt : m'.support.card < m.support.card := by
              refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, ?_⟩)
              intro heq
              apply hne
              ext v
              have hv1 := hp m' hm' v
              have hv2 := hm1 v
              have hiff : v ∈ m'.support ↔ v ∈ m.support := by rw [heq]
              simp only [Finsupp.mem_support_iff] at hiff
              omega
            exact ih m'.support.card (hk ▸ hlt) m' (hp m' hm') rfl
          · rfl
        · intro h; exact absurd hm_mem h
      · have hzero_m : p.coeff m = 0 := notMem_support_iff.1 hm_mem
        rw [hzero_m]
        refine Finset.sum_eq_zero fun m' hm' => ?_
        split_ifs with hsub
        · have hne : m' ≠ m := fun h => hm_mem (h ▸ hm')
          have hlt : m'.support.card < m.support.card := by
            refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, ?_⟩)
            intro heq
            apply hne
            ext v
            have hv1 := hp m' hm' v
            have hv2 := hm1 v
            have hiff : v ∈ m'.support ↔ v ∈ m.support := by rw [heq]
            simp only [Finsupp.mem_support_iff] at hiff
            omega
          exact ih m'.support.card (hk ▸ hlt) m' (hp m' hm') rfl
        · rfl
    rw [hsingle] at h0
    exact h0
  ext m
  by_cases hm : m ∈ p.support
  · exact hcoeff m.support.card m (hp m hm) rfl
  · exact notMem_support_iff.1 hm

/-- `p - multilinearize p` belongs to the Boolean ideal generated by `{X v ^ 2 - X v}`. -/
theorem sub_multilinearize_mem_boolIdeal (p : MvPolynomial V F) :
    p - multilinearize p ∈ Ideal.span (Set.range (boolAxiom (R := F) : V → MvPolynomial V F)) := by
  classical
  set I := Ideal.span (Set.range (boolAxiom (R := F) : V → MvPolynomial V F))
  have hpow : ∀ (v : V) (e : ℕ), 1 ≤ e → (X v : MvPolynomial V F) ^ e - X v ∈ I := by
    intro v e he
    induction e with
    | zero => omega
    | succ e ih =>
      cases e with
      | zero => simp
      | succ e =>
        have hsplit : (X v : MvPolynomial V F) ^ (e + 2) - X v =
            X v ^ e * boolAxiom v + (X v ^ (e + 1) - X v) := by
          simp [boolAxiom]; ring
        rw [hsplit]
        exact I.add_mem (I.mul_mem_left _ (Ideal.subset_span ⟨v, rfl⟩)) (ih (by omega))
  have hsub_eq : p - multilinearize p =
      ∑ m ∈ p.support, (monomial m (p.coeff m) - monomial (multilinExp m) (p.coeff m)) := by
    conv_lhs => rw [p.as_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => by rw [multilinearize_monomial]
  rw [hsub_eq]
  refine I.sum_mem fun m _ => ?_
  have hfactor : monomial m (p.coeff m) - monomial (multilinExp m) (p.coeff m) =
      C (p.coeff m) * (monomial m 1 - monomial (multilinExp m) 1) := by
    rw [mul_sub, C_mul_monomial, C_mul_monomial, mul_one]
  rw [hfactor]
  refine I.mul_mem_left _ ?_
  rw [monomial_eq, monomial_eq, C_1, one_mul, one_mul, Finsupp.prod, Finsupp.prod]
  have hsupp : (multilinExp m).support = m.support := by ext v; simp [Finsupp.mem_support_iff]
  rw [hsupp]
  have hprod_sub : ∀ (S : Finset V) (f g : V → MvPolynomial V F),
      (∀ v ∈ S, f v - g v ∈ I) → (∏ v ∈ S, f v) - (∏ v ∈ S, g v) ∈ I := by
    intro S f g hfg
    induction S using Finset.induction with
    | empty => simp
    | @insert v s hvs ih =>
      rw [Finset.prod_insert hvs, Finset.prod_insert hvs]
      have heq : f v * ∏ u ∈ s, f u - g v * ∏ u ∈ s, g u =
          (f v - g v) * ∏ u ∈ s, f u + g v * ((∏ u ∈ s, f u) - (∏ u ∈ s, g u)) := by ring
      rw [heq]
      exact I.add_mem (I.mul_mem_right _ (hfg v (Finset.mem_insert_self v s)))
        (I.mul_mem_left _ (ih fun u hu => hfg u (Finset.mem_insert_of_mem hu)))
  refine hprod_sub m.support _ _ fun v hv => ?_
  have hpos : 1 ≤ m v := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
  have hne : m v ≠ 0 := by omega
  simpa [multilinExp_apply, hne] using hpow v (m v) hpos

/-- **Uniqueness of `multilinearize` modulo the Boolean ideal**:
`q = multilinearize p` iff `q` is multilinear and `p - q` belongs to the ideal generated by
`{X v ^ 2 - X v}`. -/
theorem eq_multilinearize_iff {p q : MvPolynomial V F} :
    q = multilinearize p ↔
      IsMultilinear q ∧
        p - q ∈ Ideal.span (Set.range (boolAxiom (R := F) : V → MvPolynomial V F)) := by
  classical
  constructor
  · rintro rfl
    exact ⟨isMultilinear_multilinearize p, sub_multilinearize_mem_boolIdeal p⟩
  · rintro ⟨hq, hmem⟩
    have hdiff_ml : IsMultilinear (q - multilinearize p) := fun m hm v => by
      rcases Finset.mem_union.1 (support_sub_subset hm) with h1 | h2
      · exact hq m h1 v
      · exact isMultilinear_multilinearize p m h2 v
    have heval : ∀ σ : V → Bool, eval (bitPoint σ) (q - multilinearize p) = 0 := by
      intro σ
      have hI0 : ∀ f ∈ Ideal.span (Set.range (boolAxiom (R := F) : V → MvPolynomial V F)),
          eval (bitPoint σ) f = 0 := by
        intro f hf
        refine Submodule.span_induction (p := fun f _ => eval (bitPoint σ) f = 0) ?_ ?_ ?_ ?_ hf
        · rintro _ ⟨v, rfl⟩; exact eval_boolAxiom σ v
        · simp
        · intro x y _ _ hx hy; simp [hx, hy]
        · intro a x _ hx; simp [hx]
      have h1 := hI0 (p - q) hmem
      rw [map_sub, sub_eq_zero] at h1
      rw [map_sub, eval_bitPoint_multilinearize, h1, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_isMultilinear_of_eval_bitPoint_eq_zero hdiff_ml heval)

end Multilinearization

/-! ### Multilinearization of Polynomial Calculus proofs into PCR -/

section Prop53

/-- The multilinear PCR axioms: complementarity `X (v, true) + X (v, false) - 1` and
mutual-exclusion `X (v, true) * X (v, false)` for every variable `v : V`. -/
@[expose] noncomputable def multilinearPCRAxioms (V F : Type*) [Fintype V] [CommRing F] :
    List (MvPolynomial (Literal V) F) :=
  Finset.univ.toList.map PCR.complementAxiom ++
    Finset.univ.toList.map fun v : V =>
      (X (v, true) : MvPolynomial (Literal V) F) * X (v, false)

variable {V F : Type*} [CommRing F]

/-- Every axiom in `multilinearPCRAxioms V F` is multilinear. -/
theorem isMultilinear_of_mem_multilinearPCRAxioms [Fintype V]
    {p : MvPolynomial (Literal V) F} (hp : p ∈ multilinearPCRAxioms V F) :
    IsMultilinear p := by
  classical
  rcases List.mem_append.1 hp with h1 | h2
  · obtain ⟨v, _, rfl⟩ := List.mem_map.1 h1
    intro m hm l
    rcases Finset.mem_union.1 (support_sub_subset hm) with h12 | h3
    · rcases Finset.mem_union.1 (support_add_subset h12) with ha | hb
      · rw [X] at ha
        rw [Finset.mem_singleton.1 (support_monomial_subset ha)]
        by_cases hlv : l = (v, true)
        · subst hlv; simp
        · rw [Finsupp.single_eq_of_ne hlv]; exact Nat.zero_le 1
      · rw [X] at hb
        rw [Finset.mem_singleton.1 (support_monomial_subset hb)]
        by_cases hlv : l = (v, false)
        · subst hlv; simp
        · rw [Finsupp.single_eq_of_ne hlv]; exact Nat.zero_le 1
    · have h1m : (1 : MvPolynomial (Literal V) F) = monomial 0 1 := by simp
      rw [h1m] at h3
      have hm0 := Finset.mem_singleton.1 (support_monomial_subset h3)
      simp [hm0]
  · obtain ⟨v, _, rfl⟩ := List.mem_map.1 h2
    intro m hm l
    have hmul : (X (v, true) : MvPolynomial (Literal V) F) * X (v, false) =
        monomial (Finsupp.single (v, true) 1 + Finsupp.single (v, false) 1) 1 := by
      rw [X, X, monomial_mul_monomial, one_mul]
    rw [hmul] at hm
    rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
    simp only [Finsupp.add_apply]
    by_cases h1 : l = (v, true)
    · subst h1; simp
    · by_cases h2 : l = (v, false)
      · subst h2; simp
      · rw [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2]
        exact Nat.zero_le 1

private theorem support_rename_subset {σ τ : Type*} [DecidableEq τ] (f : σ → τ)
    (p : MvPolynomial σ F) :
    (MvPolynomial.rename f p).support ⊆ p.support.image (Finsupp.mapDomain f) := by
  intro m hm
  rw [p.as_sum, map_sum] at hm
  obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
  rw [MvPolynomial.rename_monomial] at hmem
  exact Finset.mem_image.2 ⟨m', hm', (Finset.mem_singleton.1 (support_monomial_subset hmem)).symm⟩

private theorem card_support_rename_le {σ τ : Type*} (f : σ → τ) (p : MvPolynomial σ F) :
    (MvPolynomial.rename f p).support.card ≤ p.support.card := by
  classical
  exact (Finset.card_le_card (support_rename_subset f p)).trans Finset.card_image_le

/-- Derive `f * g` in multilinear `PC` from an axiom `f` (whose variables are disjoint from `g`'s)
and a multilinear polynomial `g` in at most `(2 * n + 2) * #g.support + 2` steps. -/
private theorem exists_multilinear_mul_proof [Fintype V]
    {Q : List (MvPolynomial (Literal V) F)}
    {f g : MvPolynomial (Literal V) F} (hf : f ∈ Q)
    (hf_ml : IsMultilinear f) (hg_ml : IsMultilinear g)
    (hdisj : ∀ m₁ ∈ f.support, ∀ m₂ ∈ g.support, ∀ l, m₁ l = 0 ∨ m₂ l = 0) :
    ∃ ls : List (MvPolynomial (Literal V) F),
      PC.IsProof Q ls ∧
      (∀ p ∈ ls, IsMultilinear p) ∧
      f * g ∈ ls ∧
      ls.length ≤ (2 * Fintype.card V + 2) * g.support.card + 2 := by
  classical
  have hmon : ∀ (m : Literal V →₀ ℕ), (∀ l, m l ≤ 1) →
      (∀ m₁ ∈ f.support, ∀ l, m₁ l = 0 ∨ m l = 0) →
      ∃ ms : List (MvPolynomial (Literal V) F),
        PC.IsProof Q ms ∧
        (∀ p ∈ ms, IsMultilinear p) ∧
        monomial m 1 * f ∈ ms ∧
        ms.length ≤ m.degree + 1 := by
    intro m
    induction m using Finsupp.induction with
    | zero =>
      intro _ _
      refine ⟨[f], PC.IsProof.nil.mem hf, List.forall_mem_singleton.2 hf_ml, ?_, by simp⟩
      simp
    | single_add l e t hlt he ih =>
      intro hm1 hmd
      have he1 : e = 1 := by
        have hle := hm1 l
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hle
        omega
      subst he1
      have ht1 : ∀ u, t u ≤ 1 := fun u => by
        have hle := hm1 u
        simp only [Finsupp.add_apply] at hle
        omega
      have htd : ∀ m₁ ∈ f.support, ∀ u, m₁ u = 0 ∨ t u = 0 := fun m₁ hm₁ u => by
        rcases hmd m₁ hm₁ u with h1 | h2
        · exact Or.inl h1
        · simp only [Finsupp.add_apply] at h2; exact Or.inr (by omega)
      have hfl0 : ∀ m₁ ∈ f.support, m₁ l = 0 := fun m₁ hm₁ => by
        rcases hmd m₁ hm₁ l with h1 | h2
        · exact h1
        · simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h2; omega
      obtain ⟨ms, hms, hms_ml, hmem, hlen⟩ := ih ht1 htd
      have heq : X l * (monomial t 1 * f) = monomial (Finsupp.single l 1 + t) 1 * f := by
        rw [← mul_assoc, X, monomial_mul_monomial, mul_one]
      have hml_new : IsMultilinear (monomial (Finsupp.single l 1 + t) 1 * f) := by
        intro u hu w
        rw [← heq, support_X_mul] at hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_map.1 hu
        change (Finsupp.single l (1 : ℕ) + u') w ≤ 1
        rw [Finsupp.add_apply]
        have hu'_ml : u' w ≤ 1 := hms_ml _ hmem u' hu' w
        by_cases hwl : w = l
        · subst hwl
          have hu'0 : u' w = 0 := by
            rw [f.as_sum, Finset.mul_sum] at hu'
            obtain ⟨m₁, hm₁, hmem₁⟩ := Finset.mem_biUnion.1 (support_sum hu')
            rw [monomial_mul_monomial, one_mul] at hmem₁
            rw [Finset.mem_singleton.1 (support_monomial_subset hmem₁), Finsupp.add_apply,
              Finsupp.notMem_support_iff.1 hlt, hfl0 m₁ hm₁]
          simp [Finsupp.single_eq_same, hu'0]
        · rw [Finsupp.single_eq_of_ne hwl, zero_add]; exact hu'_ml
      refine ⟨(monomial (Finsupp.single l 1 + t) 1 * f) :: ms,
        heq ▸ hms.mulVar l hmem,
        List.forall_mem_cons.2 ⟨hml_new, hms_ml⟩,
        List.mem_cons_self, ?_⟩
      rw [List.length_cons, map_add, Finsupp.degree_single]
      omega
  have hsum : ∀ S : Finset (Literal V →₀ ℕ), S ⊆ g.support →
      ∃ ls : List (MvPolynomial (Literal V) F),
        PC.IsProof Q ls ∧
        (∀ p ∈ ls, IsMultilinear p) ∧
        (∑ m ∈ S, C (g.coeff m) * (monomial m 1 * f)) ∈ ls ∧
        ls.length ≤ (2 * Fintype.card V + 2) * S.card + 2 := by
    intro S hS
    induction S using Finset.induction with
    | empty =>
      refine ⟨[0, f], ?_, ?_, List.mem_cons_self, by simp⟩
      · have h0 : (0 : MvPolynomial (Literal V) F) = C 0 * f + C 0 * f := by simp
        exact h0 ▸ (PC.IsProof.nil.mem hf).linear 0 0 List.mem_cons_self List.mem_cons_self
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · intro m hm; simp at hm
        · exact hf_ml
    | @insert m s hms ih =>
      have hm_supp : m ∈ g.support := hS (Finset.mem_insert_self m s)
      obtain ⟨ls₁, hls₁, hml₁, hmem₁, hlen₁⟩ :=
        ih (Finset.Subset.trans (Finset.subset_insert m s) hS)
      obtain ⟨ms, hms_p, hms_ml, hms_mem, hms_len⟩ :=
        hmon m (hg_ml m hm_supp) (fun m₁ hm₁ l => hdisj m₁ hm₁ m hm_supp l)
      have hmdeg : m.degree ≤ 2 * Fintype.card V := by
        calc m.degree = ∑ l ∈ m.support, m l := rfl
          _ ≤ ∑ _l ∈ m.support, 1 := Finset.sum_le_sum fun l _ => hg_ml m hm_supp l
          _ = m.support.card := by simp
          _ ≤ Fintype.card (Literal V) := Finset.card_le_univ _
          _ = 2 * Fintype.card V := by simp [Fintype.card_prod, mul_comm]
      let acc := ∑ m' ∈ s, C (g.coeff m') * (monomial m' 1 * f)
      let nxt := C (g.coeff m) * (monomial m 1 * f) + C 1 * acc
      have hnxt_eq : nxt = ∑ m' ∈ insert m s, C (g.coeff m') * (monomial m' 1 * f) := by
        simp [nxt, acc, Finset.sum_insert hms]
      have hnxt_ml : IsMultilinear nxt := by
        intro u hu w
        rcases Finset.mem_union.1 (support_add_subset hu) with h1 | h2
        · exact hms_ml _ hms_mem u (support_smul_subset h1) w
        · exact hml₁ _ hmem₁ u (support_smul_subset h2) w
      refine ⟨nxt :: (ms ++ ls₁),
        (hms_p.append hls₁).linear (g.coeff m) 1 (List.mem_append_left _ hms_mem)
          (List.mem_append_right _ hmem₁),
        List.forall_mem_cons.2 ⟨hnxt_ml, List.forall_mem_append.2 ⟨hms_ml, hml₁⟩⟩,
        hnxt_eq ▸ List.mem_cons_self, ?_⟩
      rw [List.length_cons, List.length_append, Finset.card_insert_of_notMem hms]
      have hmul : (2 * Fintype.card V + 2) * (s.card + 1) =
          (2 * Fintype.card V + 2) * s.card + (2 * Fintype.card V + 2) := by ring
      omega
  obtain ⟨ls, hls, hml, hmem, hlen⟩ := hsum g.support Finset.Subset.rfl
  have heq : ∑ m ∈ g.support, C (g.coeff m) * (monomial m 1 * f) = f * g := by
    conv_rhs => rw [g.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_assoc, C_mul_monomial, mul_one, mul_comm]
  exact ⟨ls, hls, hml, heq ▸ hmem, hlen⟩

/-- **Multilinearization of PC refutations into strictly multilinear PCR proofs**:
given any `PC` proof `ls` from multilinear initial polynomials `Q` (and Boolean axioms), there is a
**strictly multilinear** `PCR` proof (from `Q.map liftPos ++ multilinearPCRAxioms V F`) containing
the positive-variable lift of `multilinearize p` for every `p ∈ ls`, with total step count at most
`O((n + 1) * (PC.size ls + ls.length))`. -/
theorem multilinear_pcr_of_pc [Fintype V]
    {Q ls : List (MvPolynomial V F)}
    (hQ : ∀ q ∈ Q, IsMultilinear q)
    (h : PC.IsProof (Q ++ boolAxioms V F) ls) :
    ∃ ls' : List (MvPolynomial (Literal V) F),
      PC.IsProof (Q.map (MvPolynomial.rename (·, true)) ++ multilinearPCRAxioms V F) ls' ∧
      (∀ p ∈ ls', IsMultilinear p) ∧
      (∀ p ∈ ls, MvPolynomial.rename (·, true) (multilinearize p) ∈ ls') ∧
      ls'.length ≤ (8 * Fintype.card V + 16) * (PC.size ls + ls.length) := by
  classical
  let emb : MvPolynomial V F →ₐ[F] MvPolynomial (Literal V) F := MvPolynomial.rename (·, true)
  let Q' := Q.map emb ++ multilinearPCRAxioms V F
  have hemb_ml : ∀ p : MvPolynomial V F, IsMultilinear p → IsMultilinear (emb p) := by
    intro p hp m hm l
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 (support_rename_subset (·, true) p hm)
    rcases l with ⟨v, b⟩
    cases b
    · have : Finsupp.mapDomain (·, true) m' (v, false) = 0 := by
        rw [Finsupp.mapDomain_of_notMem_range]
        rintro ⟨u, hu⟩; simp at hu
      omega
    · have hinj : Function.Injective (fun u : V => (u, true)) := fun _ _ h => (Prod.mk.inj h).1
      change Finsupp.mapDomain (fun u : V => (u, true)) m' (v, true) ≤ 1
      rw [Finsupp.mapDomain_apply_of_injective hinj]
      exact hp m' hm' v
  have hemb_no_r : ∀ (r : V) (p : MvPolynomial V F), (∀ m ∈ p.support, m r = 0) →
      ∀ m ∈ (emb p).support, m (r, true) = 0 ∧ m (r, false) = 0 := by
    intro r p hno m hm
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 (support_rename_subset (·, true) p hm)
    have hinj : Function.Injective (fun u : V => (u, true)) := fun _ _ h => (Prod.mk.inj h).1
    constructor
    · change Finsupp.mapDomain (fun u : V => (u, true)) m' (r, true) = 0
      rw [Finsupp.mapDomain_apply_of_injective hinj]; exact hno m' hm'
    · rw [Finsupp.mapDomain_of_notMem_range]; rintro ⟨u, hu⟩; simp at hu
  have hzero_of_nonempty : ∀ {p₀ : MvPolynomial (Literal V) F}, p₀ ∈ Q' → IsMultilinear p₀ →
      ∃ zs : List (MvPolynomial (Literal V) F),
        PC.IsProof Q' zs ∧ (∀ q ∈ zs, IsMultilinear q) ∧ (0 : MvPolynomial (Literal V) F) ∈ zs ∧
        zs.length = 2 := by
    intro p₀ hp₀ hml₀
    refine ⟨[0, p₀], ?_, ?_, List.mem_cons_self, rfl⟩
    · have h0 : (0 : MvPolynomial (Literal V) F) = C 0 * p₀ + C 0 * p₀ := by simp
      exact h0 ▸ (PC.IsProof.nil.mem hp₀).linear 0 0 List.mem_cons_self List.mem_cons_self
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · intro m hm; simp at hm
      · exact hml₀
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp, by simp⟩
  | @mem ms p _ hp ih =>
    obtain ⟨ls', hls', hml', hcov', hlen'⟩ := ih
    rcases List.mem_append.1 hp with hq | hb
    · have hml_p : IsMultilinear p := hQ p hq
      have hml_eq : multilinearize p = p := multilinearize_eq_self_of_isMultilinear hml_p
      refine ⟨emb p :: ls',
        hls'.mem (List.mem_append_left _ (List.mem_map_of_mem hq)),
        List.forall_mem_cons.2 ⟨hemb_ml p hml_p, hml'⟩,
        fun u hu => ?_, ?_⟩
      · rcases List.mem_cons.1 hu with rfl | hum
        · rw [hml_eq]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hcov' u hum)
      · simp only [List.length_cons, PC.size_cons]; nlinarith
    · obtain ⟨v, rfl⟩ := mem_boolAxioms.1 hb
      have hcomp_mem : PCR.complementAxiom v ∈ Q' :=
        List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ v))))
      have hcomp_ml : IsMultilinear (PCR.complementAxiom v : MvPolynomial (Literal V) F) :=
        isMultilinear_of_mem_multilinearPCRAxioms
          (List.mem_append_left _ (List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ v))))
      obtain ⟨zs, hzs, hzs_ml, h0mem, hzs_len⟩ := hzero_of_nonempty hcomp_mem hcomp_ml
      refine ⟨zs ++ ls', hzs.append hls', List.forall_mem_append.2 ⟨hzs_ml, hml'⟩,
        fun u hu => ?_, ?_⟩
      · rcases List.mem_cons.1 hu with rfl | hum
        · rw [multilinearize_boolAxiom, map_zero]
          exact List.mem_append_left _ h0mem
        · exact List.mem_append_right _ (hcov' u hum)
      · simp only [List.length_append, hzs_len, List.length_cons, PC.size_cons]; nlinarith
  | @linear ms p q a b _ hp hq ih =>
    obtain ⟨ls', hls', hml', hcov', hlen'⟩ := ih
    have hp' := hcov' p hp
    have hq' := hcov' q hq
    have heq : emb (multilinearize (C a * p + C b * q)) =
        C a * emb (multilinearize p) + C b * emb (multilinearize q) := by
      simp only [map_add, C_mul', map_smul]
    refine ⟨emb (multilinearize (C a * p + C b * q)) :: ls',
      heq ▸ hls'.linear a b hp' hq',
      List.forall_mem_cons.2 ⟨hemb_ml _ (isMultilinear_multilinearize _), hml'⟩,
      fun u hu => ?_, ?_⟩
    · rcases List.mem_cons.1 hu with rfl | hum
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hcov' u hum)
    · simp only [List.length_cons, PC.size_cons]; nlinarith
  | @mulVar ms p r _ hp ih =>
    obtain ⟨ls', hls', hml', hcov', hlen'⟩ := ih
    have hp' := hcov' p hp
    set q := multilinearize p
    have hq_ml : IsMultilinear q := isMultilinear_multilinearize p
    set A := substZero r q
    set B := substOne r q - substZero r q
    have hdecomp : q = A + X r * B := isMultilinear_decomp hq_ml r
    have hA_ml : IsMultilinear A := isMultilinear_substZero r hq_ml
    have hB_ml : IsMultilinear B := fun m hm v => by
      rcases Finset.mem_union.1 (support_sub_subset hm) with h1 | h2
      · exact isMultilinear_substOne r hq_ml m h1 v
      · exact isMultilinear_substZero r hq_ml m h2 v
    have hA_no : ∀ m ∈ A.support, m r = 0 := fun m hm => coeff_substZero_eq_zero_of_pos r q hm
    have hB_no : ∀ m ∈ B.support, m r = 0 := fun m hm => by
      rcases Finset.mem_union.1 (support_sub_subset hm) with h1 | h2
      · exact coeff_substOne_eq_zero_of_pos r q h1
      · exact coeff_substZero_eq_zero_of_pos r q h2
    have hq_no_false : ∀ m ∈ (emb q).support, m (r, false) = 0 := by
      intro m hm
      obtain ⟨m', _, rfl⟩ := Finset.mem_image.1 (support_rename_subset (·, true) q hm)
      rw [Finsupp.mapDomain_of_notMem_range]; rintro ⟨u, hu⟩; simp at hu
    have hstep1_ml : IsMultilinear (X (r, false) * emb q) := by
      intro m hm l
      rw [support_X_mul] at hm
      obtain ⟨m', hm', rfl⟩ := Finset.mem_map.1 hm
      change (Finsupp.single (r, false) (1 : ℕ) + m') l ≤ 1
      rw [Finsupp.add_apply]
      by_cases hl : l = (r, false)
      · subst hl; simp [Finsupp.single_eq_same, hq_no_false m' hm']
      · rw [Finsupp.single_eq_of_ne hl, zero_add]; exact hemb_ml q hq_ml m' hm' l
    let excl : MvPolynomial (Literal V) F := X (r, true) * X (r, false)
    have hexcl_mem : excl ∈ Q' := List.mem_append_right _ (List.mem_append_right _
      (List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ r))))
    have hexcl_ml : IsMultilinear excl := isMultilinear_of_mem_multilinearPCRAxioms
      (List.mem_append_right _ (List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ r))))
    have hexcl_disj : ∀ m₁ ∈ excl.support, ∀ m₂ ∈ (emb B).support, ∀ l, m₁ l = 0 ∨ m₂ l = 0 := by
      intro m₁ hm₁ m₂ hm₂ l
      have hmul : excl = monomial (Finsupp.single (r, true) 1 + Finsupp.single (r, false) 1) 1 := by
        simp [excl, X, monomial_mul_monomial]
      rw [hmul] at hm₁
      rw [Finset.mem_singleton.1 (support_monomial_subset hm₁), Finsupp.add_apply]
      by_cases h1 : l = (r, true)
      · subst h1; exact Or.inr (hemb_no_r r B hB_no m₂ hm₂).1
      · by_cases h2 : l = (r, false)
        · subst h2; exact Or.inr (hemb_no_r r B hB_no m₂ hm₂).2
        · exact Or.inl (by simp [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2])
    obtain ⟨lsB, hlsB, hlsB_ml, hB_mem, hlsB_len⟩ :=
      exists_multilinear_mul_proof hexcl_mem hexcl_ml (hemb_ml B hB_ml) hexcl_disj
    let comp : MvPolynomial (Literal V) F := PCR.complementAxiom r
    have hcomp_mem : comp ∈ Q' := List.mem_append_right _ (List.mem_append_left _
      (List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ r))))
    have hcomp_ml : IsMultilinear comp := isMultilinear_of_mem_multilinearPCRAxioms
      (List.mem_append_left _ (List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ r))))
    have hcomp_disj : ∀ m₁ ∈ comp.support, ∀ m₂ ∈ (emb A).support, ∀ l, m₁ l = 0 ∨ m₂ l = 0 := by
      intro m₁ hm₁ m₂ hm₂ l
      rcases Finset.mem_union.1 (support_sub_subset hm₁) with h12 | h3
      · rcases Finset.mem_union.1 (support_add_subset h12) with ha | hb
        · rw [X] at ha
          rw [Finset.mem_singleton.1 (support_monomial_subset ha)]
          by_cases h1 : l = (r, true)
          · subst h1; exact Or.inr (hemb_no_r r A hA_no m₂ hm₂).1
          · exact Or.inl (Finsupp.single_eq_of_ne h1)
        · rw [X] at hb
          rw [Finset.mem_singleton.1 (support_monomial_subset hb)]
          by_cases h2 : l = (r, false)
          · subst h2; exact Or.inr (hemb_no_r r A hA_no m₂ hm₂).2
          · exact Or.inl (Finsupp.single_eq_of_ne h2)
      · have h1m : (1 : MvPolynomial (Literal V) F) = monomial 0 1 := by simp
        rw [h1m] at h3
        rw [Finset.mem_singleton.1 (support_monomial_subset h3)]; exact Or.inl rfl
    obtain ⟨lsA, hlsA, hlsA_ml, hA_mem, hlsA_len⟩ :=
      exists_multilinear_mul_proof hcomp_mem hcomp_ml (hemb_ml A hA_ml) hcomp_disj
    let base := lsA ++ lsB ++ ls'
    have hbase : PC.IsProof Q' base := (hlsA.append hlsB).append hls'
    have hbase_ml : ∀ u ∈ base, IsMultilinear u :=
      List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨hlsA_ml, hlsB_ml⟩, hml'⟩
    have hq_base : emb q ∈ base := List.mem_append_right _ hp'
    have hB_base : excl * emb B ∈ base := List.mem_append_left _ (List.mem_append_right _ hB_mem)
    have hA_base : comp * emb A ∈ base := List.mem_append_left _ (List.mem_append_left _ hA_mem)
    let l1 := X (r, false) * emb q
    let l2 := X (r, false) * emb A
    let l3 := emb q - l2
    let l4 := emb (multilinearize (X r * p))
    have hl2_eq : C (1 : F) * l1 + C (-1 : F) * (excl * emb B) = l2 := by
      have hqd : emb q = emb A + X (r, true) * emb B := by
        have := congrArg emb hdecomp
        simpa [emb] using this
      simp only [l1, l2, excl, hqd, map_one, map_neg, one_mul, neg_one_mul]; ring
    have hl2_ml : IsMultilinear l2 := by
      intro m hm l
      rw [support_X_mul] at hm
      obtain ⟨m', hm', rfl⟩ := Finset.mem_map.1 hm
      change (Finsupp.single (r, false) (1 : ℕ) + m') l ≤ 1
      rw [Finsupp.add_apply]
      by_cases hl : l = (r, false)
      · subst hl; simp [Finsupp.single_eq_same, (hemb_no_r r A hA_no m' hm').2]
      · rw [Finsupp.single_eq_of_ne hl, zero_add]; exact hemb_ml A hA_ml m' hm' l
    have hl3_eq : C (1 : F) * emb q + C (-1 : F) * l2 = l3 := by simp [l3]; ring
    have hl3_ml : IsMultilinear l3 := fun m hm l => by
      rcases Finset.mem_union.1 (support_sub_subset hm) with h1 | h2
      · exact hemb_ml q hq_ml m h1 l
      · exact hl2_ml m h2 l
    have hl4_eq : C (1 : F) * l3 + C (1 : F) * (comp * emb A) = l4 := by
      have hml_xr : multilinearize (X r * p) = X r * A + X r * B := by
        rw [multilinearize_X_mul]
        change X r * q - boolAxiom r * B = X r * A + X r * B
        rw [hdecomp]; simp [boolAxiom]; ring
      have hqd : emb q = emb A + X (r, true) * emb B := by
        have := congrArg emb hdecomp
        simpa [emb] using this
      have hl4_exp : l4 = X (r, true) * emb A + X (r, true) * emb B := by
        simp [l4, hml_xr, emb]
      simp only [l3, l2, comp, PCR.complementAxiom, hqd, hl4_exp, map_one, one_mul]
      ring
    have hl4_ml : IsMultilinear l4 := hemb_ml _ (isMultilinear_multilinearize _)
    have hproof : PC.IsProof Q' (l4 :: l3 :: l2 :: l1 :: base) := by
      have p1 : PC.IsProof Q' (l1 :: base) := hbase.mulVar (r, false) hq_base
      have p2 : PC.IsProof Q' (l2 :: l1 :: base) :=
        hl2_eq ▸ p1.linear 1 (-1) List.mem_cons_self (List.mem_cons_of_mem _ hB_base)
      have p3 : PC.IsProof Q' (l3 :: l2 :: l1 :: base) :=
        hl3_eq ▸ p2.linear 1 (-1) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq_base))
          List.mem_cons_self
      exact hl4_eq ▸ p3.linear 1 1 List.mem_cons_self
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hA_base)))
    have hA_card : (emb A).support.card ≤ p.support.card := by
      have h1 : (emb A).support.card ≤ A.support.card :=
        card_support_rename_le (·, true) A
      have h2 : A.support.card ≤ q.support.card := by
        have hsub : A.support ⊆ q.support := by
          intro m hm
          rw [show A = substZero r q from rfl, q.as_sum, map_sum] at hm
          obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
          rw [substZero_monomial] at hmem
          split_ifs at hmem with h0
          · rwa [Finset.mem_singleton.1 (support_monomial_subset hmem)]
          · simp at hmem
        exact Finset.card_le_card hsub
      exact (h1.trans h2).trans (card_support_multilinearize_le p)
    have hB_card : (emb B).support.card ≤ 2 * p.support.card := by
      have h1 : (emb B).support.card ≤ B.support.card :=
        card_support_rename_le (·, true) B
      have h2 : B.support.card ≤ (substOne r q).support.card + A.support.card :=
        (Finset.card_le_card support_sub_subset).trans (Finset.card_union_le _ _)
      have h3 : (substOne r q).support.card ≤ q.support.card := by
        have hsub : (substOne r q).support ⊆ q.support.image (fun m => m.erase r) := by
          intro m hm
          rw [q.as_sum, map_sum] at hm
          obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
          rw [substOne_monomial] at hmem
          exact Finset.mem_image.2
            ⟨m', hm', (Finset.mem_singleton.1 (support_monomial_subset hmem)).symm⟩
        exact (Finset.card_le_card hsub).trans Finset.card_image_le
      have h4 : A.support.card ≤ q.support.card := by
        have hsub : A.support ⊆ q.support := by
          intro m hm
          rw [show A = substZero r q from rfl, q.as_sum, map_sum] at hm
          obtain ⟨m', hm', hmem⟩ := Finset.mem_biUnion.1 (support_sum hm)
          rw [substZero_monomial] at hmem
          split_ifs at hmem with h0
          · rwa [Finset.mem_singleton.1 (support_monomial_subset hmem)]
          · simp at hmem
        exact Finset.card_le_card hsub
      have hq_card : q.support.card ≤ p.support.card := card_support_multilinearize_le p
      omega
    have hXr_card : (X r * p).support.card = p.support.card := by simp [support_X_mul]
    refine ⟨l4 :: l3 :: l2 :: l1 :: base, hproof,
      List.forall_mem_cons.2 ⟨hl4_ml, List.forall_mem_cons.2 ⟨hl3_ml,
        List.forall_mem_cons.2 ⟨hl2_ml, List.forall_mem_cons.2 ⟨hstep1_ml, hbase_ml⟩⟩⟩⟩,
      fun u hu => ?_, ?_⟩
    · rcases List.mem_cons.1 hu with rfl | hum
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_append_right _ (hcov' u hum)))))
    · simp only [base, List.length_cons, List.length_append, PC.size_cons, hXr_card]
      nlinarith

end Prop53

end CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus
