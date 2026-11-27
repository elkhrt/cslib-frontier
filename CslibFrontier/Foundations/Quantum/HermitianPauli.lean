module

public import CslibFrontier.Foundations.Quantum.PauliTwirl
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Finset.Powerset

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hermitian Pauli strings, involutory exponentials, and bounded-order Hamiltonians

This module defines Hermitian Pauli strings on a finite qubit register `ι` on top of
`Cslib.Quantum.pauliString`, establishes their involutory, unitary, and exponential identities,
counts Pauli strings of bounded interaction order `B`, and introduces bounded-order Pauli
Hamiltonians and Pauli-`Z` (diagonal) Hamiltonians.

## Main definitions

* `pauliYCount`: number of qubits carrying a Pauli-`Y` factor in `(a, b)`.
* `pauliWeight`: interaction order (number of non-identity sites) of `(a, b)`.
* `hermitianPauliString`: the Hermitian Pauli string `i^{y(a,b)} X^a Z^b`.
* `BoundedOrderHamiltonian`: a real linear combination of Hermitian Pauli strings of weight at most
  `B`.
* `PauliZHamiltonian`: a real linear combination of Pauli-`Z` strings of weight at most `B`.

## Main results

* `isHermitian_hermitianPauliString`, `hermitianPauliString_mul_self`,
  `hermitianPauliString_mem_unitaryGroup`: Hermitian Pauli strings are Hermitian, involutory, and
  unitary.
* `exp_smul_of_mul_self_eq_one`, `exp_neg_smul_of_mul_self_eq_one`: exact hyperbolic exponential
  formula `exp (α • S) = cosh α • 1 + sinh α • S` for any involutory complex matrix `S`.
* `card_pauliWeight_le`: exact cardinality `∑ k ∈ range (B + 1), 3 ^ k * (card ι).choose k` of Pauli
  strings of weight at most `B`.
* `card_pauliWeight_le_four_pow_mul_choose`, `card_pauliWeight_le_pow`: upper bounds `4 ^ B * (card
  ι).choose B` (for `B ≤ card ι`) and `(3 * card ι + 1) ^ B` (unconditional).
* `singleShotVariance_le_one`: variance of any involutory Hermitian observable on a unit state is at
  most `1`.
-/

public section

namespace CslibFrontier.Foundations.Quantum

open Matrix Finset Complex
open scoped Matrix.Norms.L2Operator

section BasicPauli

variable {ι : Type*} [Fintype ι]

/-- Number of qubits `q : ι` on which `(a, b)` carries both `X` and `Z` (a Pauli-`Y` factor). -/
def pauliYCount (a b : ι → Bool) : ℕ :=
  (Finset.univ.filter fun q ↦ a q && b q).card

/-- Interaction order (Pauli weight) of `(a, b)`: number of qubits on which `a q` or `b q` is
nonzero. -/
@[expose] def pauliWeight (a b : ι → Bool) : ℕ :=
  (Finset.univ.filter fun q ↦ a q || b q).card

/-- The support of a Pauli string `(a, b)` is the finset of qubits where `a q || b q`. -/
@[expose] def pauliSupport (a b : ι → Bool) : Finset ι :=
  Finset.univ.filter fun q ↦ a q || b q

/-- The Pauli weight equals the cardinality of the Pauli support. -/
theorem pauliWeight_eq_card_pauliSupport (a b : ι → Bool) :
    pauliWeight a b = (pauliSupport a b).card := by
  rw [pauliWeight, pauliSupport]

/-- Every Pauli-`Z` string has zero `Y`-count. -/
@[simp]
theorem pauliYCount_zero_left (b : ι → Bool) : pauliYCount 0 b = 0 := by
  simp [pauliYCount]

/-- Every Pauli-`X` string has zero `Y`-count. -/
@[simp]
theorem pauliYCount_zero_right (a : ι → Bool) : pauliYCount a 0 = 0 := by
  simp [pauliYCount]

end BasicPauli

section HermitianPauli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **Hermitian Pauli string** `i^{y(a,b)} X^a Z^b` on register `ι`, where `y(a,b)` counts
the sites carrying both `X` and `Z` (so that each such site contributes `i X Z = Y`). -/
noncomputable def hermitianPauliString (a b : ι → Bool) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  (Complex.I ^ pauliYCount a b) • Cslib.Quantum.pauliString a b

/-- On `a = 0`, the Hermitian Pauli string reduces to the diagonal Pauli-`Z` string `Z^b`. -/
@[simp]
theorem hermitianPauliString_zero_left (b : ι → Bool) :
    hermitianPauliString 0 b = Cslib.Quantum.pauliZPow b := by
  simp [hermitianPauliString, Cslib.Quantum.pauliString, Cslib.Quantum.pauliXPow_zero]

/-- On `b = 0`, the Hermitian Pauli string reduces to the Pauli-`X` string `X^a`. -/
@[simp]
theorem hermitianPauliString_zero_right (a : ι → Bool) :
    hermitianPauliString a 0 = Cslib.Quantum.pauliXPow a := by
  simp [hermitianPauliString, Cslib.Quantum.pauliString, Cslib.Quantum.pauliZPow_zero]

omit [DecidableEq ι] in
private lemma signVal_dotProduct_eq_neg_one_pow (a b : ι → Bool) :
    (Cslib.BitString.signVal (a ⬝ᵥ b) : ℂ) = (-1 : ℂ) ^ pauliYCount a b := by
  classical
  have hgen : ∀ s : Finset ι,
      (Cslib.BitString.signVal (∑ q ∈ s, a q * b q) : ℂ) =
        (-1 : ℂ) ^ (s.filter fun q ↦ a q && b q).card := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.filter_empty, Finset.card_empty, pow_zero]
      change (Cslib.BitString.signVal false : ℂ) = 1
      rw [Cslib.BitString.signVal_false]
      norm_num
    | @insert q s hq ih =>
      rw [Finset.sum_insert hq, Finset.filter_insert]
      have hmul : (Cslib.BitString.signVal (a q * b q + ∑ x ∈ s, a x * b x) : ℂ) =
          (Cslib.BitString.signVal (a q * b q) : ℂ) *
            (Cslib.BitString.signVal (∑ x ∈ s, a x * b x) : ℂ) := by
        exact_mod_cast Cslib.BitString.signVal_xor (a q * b q) (∑ x ∈ s, a x * b x)
      rw [hmul, ih]
      have hqnot : q ∉ s.filter (fun x ↦ a x && b x) := fun hm ↦ hq (Finset.mem_filter.mp hm).1
      cases ha : a q <;> cases hb : b q
      · change (Cslib.BitString.signVal false : ℂ) * _ = _
        simp [Cslib.BitString.signVal_false]
      · change (Cslib.BitString.signVal false : ℂ) * _ = _
        simp [Cslib.BitString.signVal_false]
      · change (Cslib.BitString.signVal false : ℂ) * _ = _
        simp [Cslib.BitString.signVal_false]
      · change (Cslib.BitString.signVal true : ℂ) * _ = _
        rw [Cslib.BitString.signVal_true]
        simp only [Bool.and_self, ↓reduceIte, Finset.card_insert_of_notMem hqnot, pow_succ']
        push_cast
        ring
  simpa [dotProduct, pauliYCount] using hgen Finset.univ

/-- Every Hermitian Pauli string is Hermitian. -/
theorem isHermitian_hermitianPauliString (a b : ι → Bool) :
    (hermitianPauliString a b).IsHermitian := by
  rw [Matrix.IsHermitian, hermitianPauliString, Matrix.conjTranspose_smul,
    Cslib.Quantum.pauliString, Matrix.conjTranspose_mul,
    (Cslib.Quantum.pauliZPow_isHermitian b).eq, (Cslib.Quantum.pauliXPow_isHermitian a).eq,
    Cslib.Quantum.pauliZPow_mul_pauliXPow, smul_smul, signVal_dotProduct_eq_neg_one_pow,
    RCLike.star_def, map_pow, Complex.conj_I, ← mul_pow]
  have hneg : (-Complex.I) * (-1 : ℂ) = Complex.I := by ring
  rw [hneg]

/-- Every Hermitian Pauli string squares to the identity matrix. -/
theorem hermitianPauliString_mul_self (a b : ι → Bool) :
    hermitianPauliString a b * hermitianPauliString a b = 1 := by
  rw [hermitianPauliString, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Cslib.Quantum.pauliString, Matrix.mul_assoc, ← Matrix.mul_assoc (Cslib.Quantum.pauliZPow b),
    Cslib.Quantum.pauliZPow_mul_pauliXPow, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc (Cslib.Quantum.pauliXPow a),
    Cslib.Quantum.pauliXPow_mul_self, Matrix.one_mul, Cslib.Quantum.pauliZPow_mul_self,
    signVal_dotProduct_eq_neg_one_pow, ← pow_add, ← two_mul, pow_mul, Complex.I_sq, ← mul_pow]
  norm_num

/-- Every Hermitian Pauli string is unitary. -/
theorem hermitianPauliString_mem_unitaryGroup (a b : ι → Bool) :
    hermitianPauliString a b ∈ Matrix.unitaryGroup (ι → Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    (isHermitian_hermitianPauliString a b).eq, hermitianPauliString_mul_self]

/-- The `ℓ²` operator norm of every Hermitian Pauli string is `1`. -/
theorem norm_hermitianPauliString (a b : ι → Bool) :
    ‖hermitianPauliString a b‖ = 1 := by
  have hu : hermitianPauliString a b ∈ unitary (Matrix (ι → Bool) (ι → Bool) ℂ) :=
    hermitianPauliString_mem_unitaryGroup a b
  rw [← mul_one (hermitianPauliString a b), CStarRing.norm_mem_unitary_mul _ hu, norm_one]

/-- A Pauli-`Z` string acts diagonally on every state vector. -/
theorem hermitianPauliString_zero_left_mulVec (b : ι → Bool) (v : (ι → Bool) → ℂ)
    (z : ι → Bool) :
    (hermitianPauliString 0 b *ᵥ v) z = (Cslib.BitString.signVal (b ⬝ᵥ z) : ℂ) * v z := by
  rw [hermitianPauliString_zero_left, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single z]
  · simp [Cslib.Quantum.pauliZPow_apply]
  · intro y _ hy
    simp [Cslib.Quantum.pauliZPow_apply, hy.symm]
  · simp

end HermitianPauli

section InvolutoryExponential

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Exact hyperbolic exponential of an involutory matrix**: if `S * S = 1`, then for every
real scalar `α`, `exp (α • S) = cosh α • 1 + sinh α • S`. -/
theorem exp_smul_of_mul_self_eq_one {S : Matrix m m ℂ} (hS : S * S = 1) (α : ℝ) :
    NormedSpace.exp ((α : ℂ) • S) = (Real.cosh α : ℂ) • 1 + (Real.sinh α : ℂ) • S := by
  let g : ℝ → Matrix m m ℂ := fun t ↦
    NormedSpace.exp ((-(t : ℂ)) • S) * ((Real.cosh t : ℂ) • 1 + (Real.sinh t : ℂ) • S)
  have hg : ∀ t : ℝ, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ ↦ NormedSpace.exp ((-(s : ℂ)) • S))
        (NormedSpace.exp ((-(t : ℂ)) • S) * (-S)) t := by
      have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-S) t
      have heq : (fun s : ℝ ↦ NormedSpace.exp (s • (-S))) =
          fun s : ℝ ↦ NormedSpace.exp ((-(s : ℂ)) • S) := by
        funext s; congr 1; ext i j; simp
      rw [heq] at hexp
      simpa using hexp
    have h2 : HasDerivAt (fun s : ℝ ↦ (Real.cosh s : ℂ) • 1 + (Real.sinh s : ℂ) • S)
        ((Real.sinh t : ℂ) • 1 + (Real.cosh t : ℂ) • S) t := by
      have hc : HasDerivAt (fun s : ℝ ↦ (Real.cosh s : ℂ)) (Real.sinh t : ℂ) t :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_cosh t)
      have hs : HasDerivAt (fun s : ℝ ↦ (Real.sinh s : ℂ)) (Real.cosh t : ℂ) t :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_sinh t)
      exact (hc.smul_const (1 : Matrix m m ℂ)).add (hs.smul_const S)
    have hprod := h1.mul h2
    have hzero :
        NormedSpace.exp ((-(t : ℂ)) • S) * (-S) *
            ((Real.cosh t : ℂ) • 1 + (Real.sinh t : ℂ) • S) +
          NormedSpace.exp ((-(t : ℂ)) • S) *
            ((Real.sinh t : ℂ) • 1 + (Real.cosh t : ℂ) • S) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_add]
      have hcancel :
          (-S) * ((Real.cosh t : ℂ) • 1 + (Real.sinh t : ℂ) • S) +
            ((Real.sinh t : ℂ) • 1 + (Real.cosh t : ℂ) • S) = 0 := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.neg_mul, Matrix.neg_mul,
          Matrix.mul_one, hS]
        simp only [smul_neg]
        abel
      rw [hcancel, Matrix.mul_zero]
    rwa [hzero] at hprod
  have hconst : g α = g 0 :=
    is_const_of_deriv_eq_zero (fun t ↦ (hg t).differentiableAt) (fun t ↦ (hg t).deriv) α 0
  have hg0 : g 0 = 1 := by simp [g]
  rw [hg0] at hconst
  have hcomm : Commute ((α : ℂ) • S) ((-(α : ℂ)) • S) :=
    ((Commute.refl S).smul_left _).smul_right _
  have hcancel : NormedSpace.exp ((α : ℂ) • S) * NormedSpace.exp ((-(α : ℂ)) • S) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ hcomm]
    simp
  calc
    NormedSpace.exp ((α : ℂ) • S) = NormedSpace.exp ((α : ℂ) • S) * 1 := (Matrix.mul_one _).symm
    _ = NormedSpace.exp ((α : ℂ) • S) * g α := by rw [hconst]
    _ = (NormedSpace.exp ((α : ℂ) • S) * NormedSpace.exp ((-(α : ℂ)) • S)) *
          ((Real.cosh α : ℂ) • 1 + (Real.sinh α : ℂ) • S) := by
      simp [g, Matrix.mul_assoc]
    _ = (Real.cosh α : ℂ) • 1 + (Real.sinh α : ℂ) • S := by
      rw [hcancel, Matrix.one_mul]

/-- Negative-sign specialization `exp (-(α • S)) = cosh α • 1 - sinh α • S` for involutory `S`. -/
theorem exp_neg_smul_of_mul_self_eq_one {S : Matrix m m ℂ} (hS : S * S = 1) (α : ℝ) :
    NormedSpace.exp (-((α : ℂ) • S)) = (Real.cosh α : ℂ) • 1 - (Real.sinh α : ℂ) • S := by
  have h := exp_smul_of_mul_self_eq_one hS (-α)
  simp only [Complex.ofReal_neg, neg_smul, Real.cosh_neg, Real.sinh_neg] at h
  rw [h, sub_eq_add_neg]

end InvolutoryExponential

section PauliCardinality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exact cardinality of Pauli strings of weight at most `B`**: on `Q = card ι` qubits, there
are exactly `∑ k ∈ range (B + 1), 3 ^ k * Q.choose k` Pauli strings with at most `B` non-identity
factors. -/
theorem card_pauliWeight_le (B : ℕ) :
    (Finset.univ.filter fun p : (ι → Bool) × (ι → Bool) ↦ pauliWeight p.1 p.2 ≤ B).card =
      ∑ k ∈ Finset.range (B + 1), 3 ^ k * (Fintype.card ι).choose k := by
  let S : Finset ((ι → Bool) × (ι → Bool)) :=
    Finset.univ.filter fun p ↦ pauliWeight p.1 p.2 ≤ B
  let supp : (ι → Bool) × (ι → Bool) → Finset ι := fun p ↦ pauliSupport p.1 p.2
  have hpart : S.card =
      ∑ T ∈ Finset.univ.filter (fun T : Finset ι ↦ T.card ≤ B),
        (S.filter fun p ↦ supp p = T).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [S, supp, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        pauliWeight_eq_card_pauliSupport]
      exact ⟨fun hp ↦ ⟨pauliSupport p.1 p.2, hp, hp, rfl⟩, fun ⟨_, _, hp, _⟩ ↦ hp⟩
    · intro T₁ _ T₂ _ hne
      exact Finset.disjoint_left.mpr fun p hp₁ hp₂ ↦
        hne ((Finset.mem_filter.mp hp₁).2.symm.trans (Finset.mem_filter.mp hp₂).2)
  have hfiber : ∀ T : Finset ι, T.card ≤ B →
      (S.filter fun p ↦ supp p = T).card = 3 ^ T.card := by
    intro T hT
    let NonId := {x : Bool × Bool // x.1 || x.2}
    have hcardNonId : Fintype.card NonId = 3 := by decide
    let e : {p : (ι → Bool) × (ι → Bool) // p ∈ S.filter fun p ↦ supp p = T} ≃
        (T → NonId) :=
      { toFun := fun ⟨p, hp⟩ q ↦
          ⟨(p.1 q.1, p.2 q.1), by
            have hq : q.1 ∈ supp p := by
              rw [(Finset.mem_filter.mp hp).2]
              exact q.2
            exact (Finset.mem_filter.mp hq).2⟩
        invFun := fun f ↦
          ⟨(fun q ↦ if hq : q ∈ T then (f ⟨q, hq⟩).1.1 else false,
            fun q ↦ if hq : q ∈ T then (f ⟨q, hq⟩).1.2 else false), by
            have hsupp : pauliSupport
                (fun q ↦ if hq : q ∈ T then (f ⟨q, hq⟩).1.1 else false)
                (fun q ↦ if hq : q ∈ T then (f ⟨q, hq⟩).1.2 else false) = T := by
              ext q
              simp only [pauliSupport, Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hq : q ∈ T
              · simp [hq, (f ⟨q, hq⟩).2]
              · simp [hq]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hsupp⟩
            rw [pauliWeight_eq_card_pauliSupport, hsupp]
            exact hT⟩
        left_inv := fun ⟨p, hp⟩ ↦ by
          apply Subtype.ext
          have hsupp : supp p = T := (Finset.mem_filter.mp hp).2
          ext q <;> by_cases hq : q ∈ T
          · simp [hq]
          · have hnot : q ∉ supp p := by rwa [hsupp]
            have hfalse : (p.1 q || p.2 q) = false := by
              simpa [supp, pauliSupport] using hnot
            simp [hq, (Bool.or_eq_false_iff.mp hfalse).1]
          · simp [hq]
          · have hnot : q ∉ supp p := by rwa [hsupp]
            have hfalse : (p.1 q || p.2 q) = false := by
              simpa [supp, pauliSupport] using hnot
            simp [hq, (Bool.or_eq_false_iff.mp hfalse).2]
        right_inv := fun f ↦ by
          ext ⟨q, hq⟩ <;> simp [hq] }
    have h1 := Fintype.card_congr e
    rw [Fintype.card_coe, Fintype.card_fun, hcardNonId, Fintype.card_coe] at h1
    exact h1
  rw [hpart, Finset.sum_congr rfl fun T hT ↦ hfiber T (Finset.mem_filter.mp hT).2]
  have hgroup :
      (∑ T ∈ Finset.univ.filter (fun T : Finset ι ↦ T.card ≤ B), 3 ^ T.card) =
        ∑ k ∈ Finset.range (B + 1),
          ∑ T ∈ Finset.powersetCard k (Finset.univ : Finset ι), 3 ^ T.card := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, Nat.lt_succ_iff]
      exact ⟨fun h ↦ ⟨T.card, h, rfl⟩, fun ⟨_, hk, hTk⟩ ↦ hTk ▸ hk⟩
    · intro k₁ _ k₂ _ hne
      exact Finset.disjoint_left.mpr fun T hT₁ hT₂ ↦
        hne ((Finset.mem_powersetCard.mp hT₁).2.symm.trans (Finset.mem_powersetCard.mp hT₂).2)
  rw [hgroup]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_congr rfl fun T hT ↦ by rw [(Finset.mem_powersetCard.mp hT).2],
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul, mul_comm]

/-- For `B ≤ card ι`, the number of Pauli strings of weight at most `B` is bounded above by
`4 ^ B * (card ι).choose B`. -/
theorem card_pauliWeight_le_four_pow_mul_choose {B : ℕ} (hB : B ≤ Fintype.card ι) :
    (Finset.univ.filter fun p : (ι → Bool) × (ι → Bool) ↦ pauliWeight p.1 p.2 ≤ B).card ≤
      4 ^ B * (Fintype.card ι).choose B := by
  let S : Finset ((ι → Bool) × (ι → Bool)) :=
    Finset.univ.filter fun p ↦ pauliWeight p.1 p.2 ≤ B
  let box : Finset ι → Finset ((ι → Bool) × (ι → Bool)) := fun T ↦
    Finset.univ.filter fun p ↦ pauliSupport p.1 p.2 ⊆ T
  have hsub : S ⊆ (Finset.powersetCard B (Finset.univ : Finset ι)).biUnion box := by
    intro p hp
    have hcard : (pauliSupport p.1 p.2).card ≤ B := by
      rw [← pauliWeight_eq_card_pauliSupport]
      exact (Finset.mem_filter.mp hp).2
    obtain ⟨T, hsubT, hTcard⟩ := Finset.exists_superset_card_eq hcard hB
    exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsubT⟩⟩
  have hbox_card : ∀ T ∈ Finset.powersetCard B (Finset.univ : Finset ι),
      (box T).card = 4 ^ B := by
    intro T hT
    have hTcard : T.card = B := (Finset.mem_powersetCard.mp hT).2
    let e : {p : (ι → Bool) × (ι → Bool) // p ∈ box T} ≃ (T → Bool × Bool) :=
      { toFun := fun ⟨p, _⟩ q ↦ (p.1 q.1, p.2 q.1)
        invFun := fun f ↦
          ⟨(fun q ↦ if hq : q ∈ T then (f ⟨q, hq⟩).1 else false,
            fun q ↦ if hq : q ∈ T then (f ⟨q, hq⟩).2 else false), by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq ↦ ?_⟩
            by_contra hnot
            have : (if h : q ∈ T then (f ⟨q, h⟩).1 else false) ||
                (if h : q ∈ T then (f ⟨q, h⟩).2 else false) = true :=
              (Finset.mem_filter.mp hq).2
            simp [hnot] at this⟩
        left_inv := fun ⟨p, hp⟩ ↦ by
          apply Subtype.ext
          have hsubT : pauliSupport p.1 p.2 ⊆ T := (Finset.mem_filter.mp hp).2
          ext q <;> by_cases hq : q ∈ T
          · simp [hq]
          · have hnot : q ∉ pauliSupport p.1 p.2 := fun hm ↦ hq (hsubT hm)
            have hfalse : (p.1 q || p.2 q) = false := by simpa [pauliSupport] using hnot
            simp [hq, (Bool.or_eq_false_iff.mp hfalse).1]
          · simp [hq]
          · have hnot : q ∉ pauliSupport p.1 p.2 := fun hm ↦ hq (hsubT hm)
            have hfalse : (p.1 q || p.2 q) = false := by simpa [pauliSupport] using hnot
            simp [hq, (Bool.or_eq_false_iff.mp hfalse).2]
        right_inv := fun f ↦ by
          ext ⟨q, hq⟩ <;> simp [hq] }
    have h1 := Fintype.card_congr e
    rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_coe, hTcard] at h1
    simpa using h1
  calc
    S.card ≤ ((Finset.powersetCard B (Finset.univ : Finset ι)).biUnion box).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ T ∈ Finset.powersetCard B (Finset.univ : Finset ι), (box T).card :=
      Finset.card_biUnion_le
    _ = ∑ _T ∈ Finset.powersetCard B (Finset.univ : Finset ι), 4 ^ B :=
      Finset.sum_congr rfl hbox_card
    _ = 4 ^ B * (Fintype.card ι).choose B := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul, mul_comm]

/-- Unconditional polynomial upper bound: for all `B` and `Q = card ι`, the number of Pauli
strings of weight at most `B` is bounded by `(3 * Q + 1) ^ B`. -/
theorem card_pauliWeight_le_pow (B : ℕ) :
    (Finset.univ.filter fun p : (ι → Bool) × (ι → Bool) ↦ pauliWeight p.1 p.2 ≤ B).card ≤
      (3 * Fintype.card ι + 1) ^ B := by
  rw [card_pauliWeight_le, add_pow]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hkB : k ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : 1 ≤ B.choose k := Nat.choose_pos hkB
  have h2 : (Fintype.card ι).choose k ≤ (Fintype.card ι) ^ k :=
    Nat.choose_le_pow (Fintype.card ι) k
  calc
    3 ^ k * (Fintype.card ι).choose k ≤ 3 ^ k * (Fintype.card ι) ^ k := by gcongr
    _ = (3 * Fintype.card ι) ^ k := (mul_pow 3 (Fintype.card ι) k).symm
    _ = (3 * Fintype.card ι) ^ k * 1 ^ (B - k) * 1 := by simp
    _ ≤ (3 * Fintype.card ι) ^ k * 1 ^ (B - k) * B.choose k := by gcongr

end PauliCardinality

section VarianceAndHamiltonians

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Single-shot variance bound for an involutory Hermitian observable**: if `S` is Hermitian
and `S * S = 1`, then for any unit state `ψ` its quantum expectation `μ = Re ⟨ψ, S ψ⟩` lies in
`[-1, 1]` and its measurement variance `1 - μ ^ 2` is at most `1`. -/
theorem singleShotVariance_le_one {S : Matrix ι ι ℂ} (hS : S.IsHermitian) (hS2 : S * S = 1)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    let μ := RCLike.re (@inner ℂ _ _ ψ (WithLp.toLp 2 (S *ᵥ ψ.ofLp)))
    |μ| ≤ 1 ∧ 0 ≤ 1 - μ ^ 2 ∧ 1 - μ ^ 2 ≤ 1 := by
  intro μ
  have hU : S ∈ unitary (Matrix ι ι ℂ) := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hS.eq, hS2]
  have hnormS : ‖S‖ ≤ 1 := by
    have hne : Nonempty ι := by
      by_contra h
      have h0 : ψ = 0 := by
        ext i
        exact False.elim (h ⟨i⟩)
      simp [h0] at hψ
    have hnt : Nontrivial (Matrix ι ι ℂ) :=
      ⟨1, 0, fun heq ↦ (one_ne_zero : (1 : ℂ) ≠ 0) (by
        simpa using congrArg (fun M : Matrix ι ι ℂ ↦ M hne.some hne.some) heq)⟩
    rw [← mul_one S, CStarRing.norm_mem_unitary_mul _ hU, norm_one]
  have hnormVec : ‖WithLp.toLp 2 (S *ᵥ ψ.ofLp)‖ ≤ 1 := by
    calc
      ‖WithLp.toLp 2 (S *ᵥ ψ.ofLp)‖ ≤ ‖S‖ * ‖ψ‖ := Matrix.l2_opNorm_mulVec S ψ
      _ ≤ 1 * 1 := by rw [hψ]; gcongr
      _ = 1 := one_mul 1
  have hinner : ‖@inner ℂ _ _ ψ (WithLp.toLp 2 (S *ᵥ ψ.ofLp))‖ ≤ 1 := by
    calc
      ‖@inner ℂ _ _ ψ (WithLp.toLp 2 (S *ᵥ ψ.ofLp))‖
          ≤ ‖ψ‖ * ‖WithLp.toLp 2 (S *ᵥ ψ.ofLp)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [hψ]; gcongr
      _ = 1 := one_mul 1
  have habs : |μ| ≤ 1 := (Complex.abs_re_le_norm _).trans hinner
  have hsq : μ ^ 2 ≤ 1 := by nlinarith [abs_le.mp habs]
  exact ⟨habs, by linarith, by nlinarith⟩

/-- A **bounded-order Pauli Hamiltonian** on `Q` qubits of interaction order at most `B`:
a real linear combination `H = ∑ i, a_i S_i` of Hermitian Pauli strings of weight at most `B`. -/
@[ext]
structure BoundedOrderHamiltonian (Q B : ℕ) where
  /-- Real coefficient of each Pauli string `(a, b)`. -/
  coeff : (Fin Q → Bool) × (Fin Q → Bool) → ℝ
  /-- Only Pauli strings of weight at most `B` may have nonzero coefficient. -/
  weight_le : ∀ p, coeff p ≠ 0 → pauliWeight p.1 p.2 ≤ B

namespace BoundedOrderHamiltonian

/-- The Hermitian matrix `∑ p, coeff p • hermitianPauliString p.1 p.2` represented by a
bounded-order Hamiltonian. -/
noncomputable def toMatrix {Q B : ℕ} (H : BoundedOrderHamiltonian Q B) :
    Matrix (Fin Q → Bool) (Fin Q → Bool) ℂ :=
  ∑ p : (Fin Q → Bool) × (Fin Q → Bool),
    (H.coeff p : ℂ) • hermitianPauliString p.1 p.2

/-- Every bounded-order Pauli Hamiltonian is Hermitian. -/
theorem isHermitian_toMatrix {Q B : ℕ} (H : BoundedOrderHamiltonian Q B) :
    H.toMatrix.IsHermitian := by
  rw [toMatrix, Matrix.isHermitian_iff_isSelfAdjoint]
  refine isSelfAdjoint_sum _ fun p _ ↦ ?_
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    (isHermitian_hermitianPauliString p.1 p.2).eq]
  simp

/-- The number of active (nonzero-coefficient) Pauli terms in a bounded-order Hamiltonian is
bounded by `4 ^ B * Q.choose B` whenever `B ≤ Q`. -/
theorem card_support_le_four_pow_mul_choose {Q B : ℕ} (H : BoundedOrderHamiltonian Q B)
    (hB : B ≤ Q) :
    (Finset.univ.filter fun p ↦ H.coeff p ≠ 0).card ≤ 4 ^ B * Q.choose B := by
  calc
    (Finset.univ.filter fun p ↦ H.coeff p ≠ 0).card
        ≤ (Finset.univ.filter fun p : (Fin Q → Bool) × (Fin Q → Bool) ↦
            pauliWeight p.1 p.2 ≤ B).card := by
      refine Finset.card_le_card fun p hp ↦ ?_
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.weight_le p (Finset.mem_filter.mp hp).2⟩
    _ ≤ 4 ^ B * (Fintype.card (Fin Q)).choose B :=
      card_pauliWeight_le_four_pow_mul_choose (by simpa using hB)
    _ = 4 ^ B * Q.choose B := by simp

end BoundedOrderHamiltonian

/-- A **Pauli-`Z` (combinatorial optimization) Hamiltonian** on `Q` qubits of interaction order at
most `B`: a real linear combination of diagonal Pauli-`Z` strings `Z^b` of weight at most `B`. -/
@[ext]
structure PauliZHamiltonian (Q B : ℕ) where
  /-- Real coefficient of each Pauli-`Z` string `b`. -/
  coeff : (Fin Q → Bool) → ℝ
  /-- Only Pauli-`Z` strings of weight at most `B` may have nonzero coefficient. -/
  weight_le : ∀ b, coeff b ≠ 0 → pauliWeight 0 b ≤ B

namespace PauliZHamiltonian

/-- Embed a Pauli-`Z` Hamiltonian into `BoundedOrderHamiltonian Q B`. -/
@[expose] def toBoundedOrder {Q B : ℕ} (H : PauliZHamiltonian Q B) :
    BoundedOrderHamiltonian Q B where
  coeff p := if p.1 = 0 then H.coeff p.2 else 0
  weight_le p hp := by
    by_cases h1 : p.1 = 0
    · rw [h1]
      exact H.weight_le p.2 (by simpa [h1] using hp)
    · simp [h1] at hp

/-- The diagonal energy function on computational basis strings `z : Fin Q → Bool`. -/
@[expose] def energy {Q B : ℕ} (H : PauliZHamiltonian Q B) (z : Fin Q → Bool) : ℝ :=
  ∑ b : Fin Q → Bool, H.coeff b * Cslib.BitString.signVal (b ⬝ᵥ z)

/-- Evaluating `H.energy` by restricting the sum to any finite superset of the active Pauli-`Z`
support. -/
theorem energy_eq_sum_of_support {Q B : ℕ} (H : PauliZHamiltonian Q B)
    {S : Finset (Fin Q → Bool)} (hS : ∀ b, H.coeff b ≠ 0 → b ∈ S) (z : Fin Q → Bool) :
    H.energy z = ∑ b ∈ S, H.coeff b * Cslib.BitString.signVal (b ⬝ᵥ z) := by
  rw [energy, ← Finset.sum_subset (Finset.subset_univ S)]
  intro b _ hb
  have h0 : H.coeff b = 0 := by_contra fun hne ↦ hb (hS b hne)
  rw [h0, zero_mul]

/-- The matrix of a Pauli-`Z` Hamiltonian is diagonal with entries `H.energy z`. -/
theorem toMatrix_eq_diagonal {Q B : ℕ} (H : PauliZHamiltonian Q B) :
    H.toBoundedOrder.toMatrix = Matrix.diagonal (fun z ↦ (H.energy z : ℂ)) := by
  ext y z
  simp only [BoundedOrderHamiltonian.toMatrix, toBoundedOrder, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : Fin Q → Bool)]
  · simp only [↓reduceIte, hermitianPauliString_zero_left, Matrix.diagonal_apply, energy,
      Complex.ofReal_sum, Complex.ofReal_mul]
    by_cases hyz : y = z
    · subst hyz
      simp only [↓reduceIte]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Cslib.Quantum.pauliZPow_apply, ite_eq_left rfl]
    · simp only [hyz, ↓reduceIte]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [Cslib.Quantum.pauliZPow_apply, ite_eq_right hyz, mul_zero]
  · intro a _ ha
    simp [ha]
  · simp

/-- Every computational basis state `|z⟩` is an eigenstate of a Pauli-`Z` Hamiltonian with
eigenvalue `H.energy z`. -/
theorem mulVec_ket {Q B : ℕ} (H : PauliZHamiltonian Q B) (z : Fin Q → Bool) :
    H.toBoundedOrder.toMatrix *ᵥ (Cslib.Quantum.ket z).ofLp =
      (H.energy z : ℂ) • (Cslib.Quantum.ket z).ofLp := by
  rw [toMatrix_eq_diagonal]
  ext y
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Cslib.Quantum.ket_apply]
  by_cases h : y = z <;> simp [h]

end PauliZHamiltonian

end VarianceAndHamiltonians

end CslibFrontier.Foundations.Quantum
