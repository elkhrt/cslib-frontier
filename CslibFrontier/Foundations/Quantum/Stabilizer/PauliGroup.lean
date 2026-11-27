/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Foundations.Data.BitString
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Multiqubit Pauli Group and Symplectic Phase Space

This module defines the `n`-qubit Hermitian Pauli operators `CslibFrontier.Quantum.pauli` indexed by
the
`2n`-dimensional `ZMod 2` symplectic phase space `CslibFrontier.Quantum.SympVec n`, and proves their
fundamental algebraic and trace-completeness identities:

* Hermiticity, involution (`P_u² = 1`), multiplication phase, and symplectic commutation
  `P_u P_v = (-1)^{[u, v]} P_v P_u`.
* Trace orthogonality and the SWAP completeness identity
  `∑_u (P_u a₁ b₁)(P_u a₂ b₂) = 2^n δ_{a₁, b₂} δ_{a₂, b₁}`.
* Pairwise, triple, and commuting-pair triple Pauli trace identities used in stabilizer design
  and classical shadow analysis.

All results are proved from first principles under standard Lean axioms.

## Main definitions

* `CslibFrontier.Quantum.pauli1`, `CslibFrontier.Quantum.pauliPhase1`: single-qubit Hermitian Pauli
  matrices
  and their multiplication phases.
* `CslibFrontier.Quantum.SympVec`, `CslibFrontier.Quantum.sympForm`: `2n`-dimensional `ZMod 2` phase
  space
  and its canonical symplectic inner product.
* `CslibFrontier.Quantum.pauli`, `CslibFrontier.Quantum.pauliPhase`: `n`-qubit Hermitian Pauli
  matrices and
  their multiplication phases.

## Main results

* `CslibFrontier.Quantum.pauli_comm`: `P_u P_v = (-1)^{[u, v]} P_v P_u`.
* `CslibFrontier.Quantum.pauli_swap_completeness`:
  `∑_u (P_u a₁ b₁)(P_u a₂ b₂) = 2^n δ_{a₁, b₂} δ_{a₂, b₁}`.
* `CslibFrontier.Quantum.sum_trace_pauli_mul_trace_pauli`: `∑_u Tr(A P_u) Tr(B P_u) = 2^n Tr(A B)`.
* `CslibFrontier.Quantum.sum_trace_pauli_triple`:
  `∑_{u,v} Tr(A P_u) Tr(B P_v) Tr(C P_u P_v) = 4^n Tr(A B C)`.
* `CslibFrontier.Quantum.sum_commuting_trace_pauli_triple`:
  `∑_{[u,v]=0} Tr(A P_u) Tr(B P_v) Tr(C P_u P_v) = (4^n / 2) (Tr(A B C) + Tr(A C B))`.
-/

public section

namespace CslibFrontier.Quantum

open Matrix Finset Cslib

/-! ### Single-qubit Pauli matrices -/

section Pauli1

/-- Single-qubit Hermitian Pauli matrix indexed by `(x, z) : ZMod 2 × ZMod 2`:
`(0,0) ↦ I`, `(1,0) ↦ X`, `(0,1) ↦ Z`, `(1,1) ↦ -Y = [[0, i], [-i, 0]]`. -/
def pauli1 (x z : ZMod 2) : Matrix Bool Bool ℂ :=
  fun a b ↦
    if x = 0 then
      if z = 0 then (if a = b then 1 else 0)
      else (if a = b then (if a then -1 else 1) else 0)
    else
      if z = 0 then (if a = b then 0 else 1)
      else (if a = b then 0 else (if a then -Complex.I else Complex.I))

/-- Single-qubit Pauli multiplication phase `c` in
`pauli1 x₁ z₁ * pauli1 x₂ z₂ = c • pauli1 (x₁ + x₂) (z₁ + z₂)`. -/
def pauliPhase1 (x₁ z₁ x₂ z₂ : ZMod 2) : ℂ :=
  if x₁ = 0 ∧ z₁ = 0 then 1
  else if x₂ = 0 ∧ z₂ = 0 then 1
  else if x₁ = x₂ ∧ z₁ = z₂ then 1
  else if (x₁ = 1 ∧ z₁ = 0 ∧ x₂ = 0 ∧ z₂ = 1) ∨
          (x₁ = 1 ∧ z₁ = 1 ∧ x₂ = 1 ∧ z₂ = 0) ∨
          (x₁ = 0 ∧ z₁ = 1 ∧ x₂ = 1 ∧ z₂ = 1) then Complex.I
  else -Complex.I

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem pauli1_isHermitian (x z : ZMod 2) : (pauli1 x z).IsHermitian := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  ext a b
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases z with rfl | rfl <;>
    cases a <;> cases b <;> simp [pauli1, conjTranspose_apply, h10]

theorem pauli1_mul_self (x z : ZMod 2) : pauli1 x z * pauli1 x z = 1 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  ext a b
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases z with rfl | rfl <;>
    cases a <;> cases b <;>
    simp [pauli1, Matrix.mul_apply, h10]

theorem pauli1_trace (x z : ZMod 2) :
    (pauli1 x z).trace = if x = 0 ∧ z = 0 then (2 : ℂ) else 0 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases z with rfl | rfl <;>
    simp [pauli1, Matrix.trace, Matrix.diag_apply, h10]

theorem pauli1_comm (x₁ z₁ x₂ z₂ : ZMod 2) :
    pauli1 x₁ z₁ * pauli1 x₂ z₂ =
      (if x₁ * z₂ + z₁ * x₂ = 0 then (1 : ℂ) else -1) • (pauli1 x₂ z₂ * pauli1 x₁ z₁) := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  ext a b
  rcases zmod2_cases x₁ with rfl | rfl <;> rcases zmod2_cases z₁ with rfl | rfl <;>
    rcases zmod2_cases x₂ with rfl | rfl <;> rcases zmod2_cases z₂ with rfl | rfl <;>
    cases a <;> cases b <;>
    simp [pauli1, Matrix.mul_apply, h10, h11]

theorem pauli1_mul_eq_phase_smul (x₁ z₁ x₂ z₂ : ZMod 2) :
    pauli1 x₁ z₁ * pauli1 x₂ z₂ = pauliPhase1 x₁ z₁ x₂ z₂ • pauli1 (x₁ + x₂) (z₁ + z₂) := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  ext a b
  rcases zmod2_cases x₁ with rfl | rfl <;> rcases zmod2_cases z₁ with rfl | rfl <;>
    rcases zmod2_cases x₂ with rfl | rfl <;> rcases zmod2_cases z₂ with rfl | rfl <;>
    cases a <;> cases b <;>
    simp [pauli1, pauliPhase1, Matrix.mul_apply, h10, h11]

theorem pauli1_swap_completeness (a₁ b₁ a₂ b₂ : Bool) :
    ∑ u : ZMod 2 × ZMod 2, pauli1 u.1 u.2 a₁ b₁ * pauli1 u.1 u.2 a₂ b₂ =
      if a₁ = b₂ ∧ a₂ = b₁ then (2 : ℂ) else 0 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [Fintype.sum_prod_type]
  have h2 (g : ZMod 2 → ℂ) : ∑ x : ZMod 2, g x = g 0 + g 1 := by
    exact Fin.sum_univ_two g
  simp_rw [h2]
  cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> simp [pauli1, h10] <;> norm_num

end Pauli1

/-! ### Multiqubit Pauli matrices and symplectic phase space -/

section MultiqubitPauli

/-- The `2n`-dimensional `ZMod 2` symplectic phase space of `n`-qubit Pauli operators. -/
abbrev SympVec (n : ℕ) : Type := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- Canonical symplectic form `[u, v] = ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)` on `SympVec n`. -/
def sympForm {n : ℕ} (u v : SympVec n) : ZMod 2 :=
  ∑ i : Fin n, (u.1 i * v.2 i + u.2 i * v.1 i)

@[simp]
theorem sympForm_zero_left {n : ℕ} (v : SympVec n) : sympForm 0 v = 0 := by
  simp [sympForm]

@[simp]
theorem sympForm_zero_right {n : ℕ} (u : SympVec n) : sympForm u 0 = 0 := by
  simp [sympForm]

@[simp]
theorem sympForm_self {n : ℕ} (u : SympVec n) : sympForm u u = 0 := by
  simp only [sympForm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  generalize u.1 i = a
  generalize u.2 i = b
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

theorem sympForm_comm {n : ℕ} (u v : SympVec n) : sympForm u v = sympForm v u := by
  simp only [sympForm]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

theorem sympForm_add_left {n : ℕ} (u₁ u₂ v : SympVec n) :
    sympForm (u₁ + u₂) v = sympForm u₁ v + sympForm u₂ v := by
  simp only [sympForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem sympForm_add_right {n : ℕ} (u v₁ v₂ : SympVec n) :
    sympForm u (v₁ + v₂) = sympForm u v₁ + sympForm u v₂ := by
  rw [sympForm_comm, sympForm_add_left, sympForm_comm v₁, sympForm_comm v₂]

theorem sympForm_smul_left {n : ℕ} (r : ZMod 2) (u v : SympVec n) :
    sympForm (r • u) v = r * sympForm u v := by
  simp only [sympForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem sympForm_smul_right {n : ℕ} (r : ZMod 2) (u v : SympVec n) :
    sympForm u (r • v) = r * sympForm u v := by
  rw [sympForm_comm, sympForm_smul_left, sympForm_comm]

theorem sympForm_nondegenerate {n : ℕ} {u : SympVec n} (h : ∀ v, sympForm u v = 0) : u = 0 := by
  ext i
  · simpa [sympForm, Pi.single_apply] using h (0, Pi.single i 1)
  · simpa [sympForm, Pi.single_apply] using h (Pi.single i 1, 0)

/-- `n`-qubit Hermitian Pauli matrix indexed by `u : SympVec n`. -/
def pauli {n : ℕ} (u : SympVec n) : Matrix (BitString n) (BitString n) ℂ :=
  fun a b ↦ ∏ i : Fin n, pauli1 (u.1 i) (u.2 i) (a i) (b i)

/-- Phase factor `c` in `pauli u * pauli v = c • pauli (u + v)`. -/
def pauliPhase {n : ℕ} (u v : SympVec n) : ℂ :=
  ∏ i : Fin n, pauliPhase1 (u.1 i) (u.2 i) (v.1 i) (v.2 i)

@[simp]
theorem pauli_zero {n : ℕ} : pauli (0 : SympVec n) = 1 := by
  ext a b
  simp only [pauli, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Matrix.one_apply]
  have h1 (i : Fin n) : pauli1 0 0 (a i) (b i) = if a i = b i then 1 else 0 := by
    cases a i <;> cases b i <;> simp [pauli1]
  simp_rw [h1]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by simpa [funext_iff] using h
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem pauli_isHermitian {n : ℕ} (u : SympVec n) : (pauli u).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, pauli, star_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  exact congrFun (congrFun (pauli1_isHermitian (u.1 i) (u.2 i)).eq (a i)) (b i)

theorem pauli_mul_eq_phase_smul {n : ℕ} (u v : SympVec n) :
    pauli u * pauli v = pauliPhase u v • pauli (u + v) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, pauli, pauliPhase,
    Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have hprod : (∏ i : Fin n, pauliPhase1 (u.1 i) (u.2 i) (v.1 i) (v.2 i)) *
      (∏ i : Fin n, pauli1 (u.1 i + v.1 i) (u.2 i + v.2 i) (a i) (b i)) =
      ∏ i : Fin n, (pauliPhase1 (u.1 i) (u.2 i) (v.1 i) (v.2 i) *
        pauli1 (u.1 i + v.1 i) (u.2 i + v.2 i) (a i) (b i)) :=
    (Finset.prod_mul_distrib).symm
  rw [hprod]
  have hterm (i : Fin n) :
      pauliPhase1 (u.1 i) (u.2 i) (v.1 i) (v.2 i) *
        pauli1 (u.1 i + v.1 i) (u.2 i + v.2 i) (a i) (b i) =
      ∑ c : Bool, pauli1 (u.1 i) (u.2 i) (a i) c * pauli1 (v.1 i) (v.2 i) c (b i) := by
    have h := congrFun (congrFun (pauli1_mul_eq_phase_smul (u.1 i) (u.2 i) (v.1 i) (v.2 i))
      (a i)) (b i)
    simpa [Matrix.mul_apply] using h.symm
  simp_rw [hterm]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.prod_mul_distrib.symm

theorem pauli_mul_self {n : ℕ} (u : SympVec n) : pauli u * pauli u = 1 := by
  ext a b
  simp only [Matrix.mul_apply, pauli]
  have hprod : ∀ c : BitString n,
      (∏ i : Fin n, pauli1 (u.1 i) (u.2 i) (a i) (c i)) *
        (∏ i : Fin n, pauli1 (u.1 i) (u.2 i) (c i) (b i)) =
      ∏ i : Fin n, (pauli1 (u.1 i) (u.2 i) (a i) (c i) * pauli1 (u.1 i) (u.2 i) (c i) (b i)) :=
    fun c ↦ (Finset.prod_mul_distrib).symm
  simp_rw [hprod]
  have hps : ∑ c : BitString n,
      ∏ i : Fin n, (pauli1 (u.1 i) (u.2 i) (a i) (c i) * pauli1 (u.1 i) (u.2 i) (c i) (b i)) =
      ∏ i : Fin n, ∑ c : Bool,
        pauli1 (u.1 i) (u.2 i) (a i) c * pauli1 (u.1 i) (u.2 i) c (b i) :=
    (Fintype.prod_sum (fun (i : Fin n) (c : Bool) ↦
      pauli1 (u.1 i) (u.2 i) (a i) c * pauli1 (u.1 i) (u.2 i) c (b i))).symm
  rw [hps]
  have h1 (i : Fin n) :
      ∑ c : Bool, pauli1 (u.1 i) (u.2 i) (a i) c * pauli1 (u.1 i) (u.2 i) c (b i) =
        if a i = b i then 1 else 0 := by
    have h := congrFun (congrFun (pauli1_mul_self (u.1 i) (u.2 i)) (a i)) (b i)
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  simp_rw [h1]
  rw [Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by simpa [funext_iff] using h
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem pauli_comm {n : ℕ} (u v : SympVec n) :
    pauli u * pauli v = (if sympForm u v = 0 then (1 : ℂ) else -1) • (pauli v * pauli u) := by
  have h1 (i : Fin n) (a b : Bool) :
      (pauli1 (u.1 i) (u.2 i) * pauli1 (v.1 i) (v.2 i)) a b =
        (if u.1 i * v.2 i + u.2 i * v.1 i = 0 then (1 : ℂ) else -1) *
          (pauli1 (v.1 i) (v.2 i) * pauli1 (u.1 i) (u.2 i)) a b := by
    have h := congrFun (congrFun (pauli1_comm (u.1 i) (u.2 i) (v.1 i) (v.2 i)) a) b
    simpa using h
  have hentry (x y : SympVec n) (a b : BitString n) :
      (pauli x * pauli y) a b =
        ∏ i : Fin n, (pauli1 (x.1 i) (x.2 i) * pauli1 (y.1 i) (y.2 i)) (a i) (b i) := by
    simp only [Matrix.mul_apply, pauli]
    have hp (c : BitString n) :
        (∏ i, pauli1 (x.1 i) (x.2 i) (a i) (c i)) * (∏ i, pauli1 (y.1 i) (y.2 i) (c i) (b i)) =
          ∏ i, (pauli1 (x.1 i) (x.2 i) (a i) (c i) * pauli1 (y.1 i) (y.2 i) (c i) (b i)) :=
      (Finset.prod_mul_distrib).symm
    simp_rw [hp]
    exact (Fintype.prod_sum (fun (i : Fin n) (c : Bool) ↦
      pauli1 (x.1 i) (x.2 i) (a i) c * pauli1 (y.1 i) (y.2 i) c (b i))).symm
  ext a b
  rw [hentry u v a b, Matrix.smul_apply, smul_eq_mul, hentry v u a b]
  simp_rw [h1, Finset.prod_mul_distrib]
  congr 1
  have hsign : ∀ (s : Finset (Fin n)) (f : Fin n → ZMod 2),
      ∏ i ∈ s, (if f i = 0 then (1 : ℂ) else -1) = if ∑ i ∈ s, f i = 0 then 1 else -1 := by
    intro s f
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, ih, Finset.sum_insert hi]
      generalize f i = x
      generalize ∑ j ∈ s, f j = y
      rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
        simp [h10, h11]
  exact hsign Finset.univ (fun i ↦ u.1 i * v.2 i + u.2 i * v.1 i)

theorem pauli_trace {n : ℕ} (u : SympVec n) :
    (pauli u).trace = if u = 0 then (2 : ℂ) ^ n else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, pauli]
  have hps : ∑ a : BitString n, ∏ i : Fin n, pauli1 (u.1 i) (u.2 i) (a i) (a i) =
      ∏ i : Fin n, ∑ a : Bool, pauli1 (u.1 i) (u.2 i) a a :=
    (Fintype.prod_sum (fun (i : Fin n) (a : Bool) ↦ pauli1 (u.1 i) (u.2 i) a a)).symm
  rw [hps]
  have h1 (i : Fin n) :
      ∑ a : Bool, pauli1 (u.1 i) (u.2 i) a a = if u.1 i = 0 ∧ u.2 i = 0 then (2 : ℂ) else 0 := by
    simpa [Matrix.trace, Matrix.diag_apply] using pauli1_trace (u.1 i) (u.2 i)
  simp_rw [h1]
  by_cases hu : u = 0
  · subst hu; simp
  · simp only [hu, ite_false]
    have hex : ∃ i : Fin n, ¬ (u.1 i = 0 ∧ u.2 i = 0) := by
      by_contra hall
      push Not at hall
      apply hu
      ext i
      · exact (hall i).1
      · exact (hall i).2
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

/-- **SWAP completeness identity**: `∑_u (P_u a₁ b₁)(P_u a₂ b₂) = 2^n δ_{a₁,b₂} δ_{a₂,b₁}`. -/
theorem pauli_swap_completeness {n : ℕ} (a₁ b₁ a₂ b₂ : BitString n) :
    ∑ u : SympVec n, pauli u a₁ b₁ * pauli u a₂ b₂ =
      if a₁ = b₂ ∧ a₂ = b₁ then (2 : ℂ) ^ n else 0 := by
  let e : SympVec n ≃ (Fin n → ZMod 2 × ZMod 2) :=
    { toFun := fun u i ↦ (u.1 i, u.2 i)
      invFun := fun f ↦ (fun i ↦ (f i).1, fun i ↦ (f i).2)
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hrew : ∑ u : SympVec n, pauli u a₁ b₁ * pauli u a₂ b₂ =
      ∑ f : Fin n → ZMod 2 × ZMod 2, pauli (e.symm f) a₁ b₁ * pauli (e.symm f) a₂ b₂ :=
    (e.symm.sum_comp (fun u ↦ pauli u a₁ b₁ * pauli u a₂ b₂)).symm
  rw [hrew]
  have hterm (f : Fin n → ZMod 2 × ZMod 2) :
      pauli (e.symm f) a₁ b₁ * pauli (e.symm f) a₂ b₂ =
        ∏ i : Fin n, (pauli1 (f i).1 (f i).2 (a₁ i) (b₁ i) *
          pauli1 (f i).1 (f i).2 (a₂ i) (b₂ i)) := by
    simp only [pauli, e]
    exact (Finset.prod_mul_distrib).symm
  simp_rw [hterm]
  have hps : ∑ f : Fin n → ZMod 2 × ZMod 2,
      ∏ i : Fin n, (pauli1 (f i).1 (f i).2 (a₁ i) (b₁ i) *
        pauli1 (f i).1 (f i).2 (a₂ i) (b₂ i)) =
      ∏ i : Fin n, ∑ u : ZMod 2 × ZMod 2,
        pauli1 u.1 u.2 (a₁ i) (b₁ i) * pauli1 u.1 u.2 (a₂ i) (b₂ i) :=
    (Fintype.prod_sum (fun (i : Fin n) (u : ZMod 2 × ZMod 2) ↦
      pauli1 u.1 u.2 (a₁ i) (b₁ i) * pauli1 u.1 u.2 (a₂ i) (b₂ i))).symm
  rw [hps]
  simp_rw [pauli1_swap_completeness]
  by_cases h : a₁ = b₂ ∧ a₂ = b₁
  · rcases h with ⟨rfl, rfl⟩
    simp
  · simp only [h, ite_false]
    have hex : ∃ i : Fin n, ¬ (a₁ i = b₂ i ∧ a₂ i = b₁ i) := by
      by_contra hall
      push Not at hall
      exact h ⟨funext fun i ↦ (hall i).1, funext fun i ↦ (hall i).2⟩
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

/-- Pauli trace pairing: `∑_u Tr(A P_u) Tr(B P_u) = 2^n Tr(A B)`. -/
theorem sum_trace_pauli_mul_trace_pauli {n : ℕ} (A B : Matrix (BitString n) (BitString n) ℂ) :
    ∑ u : SympVec n, (A * pauli u).trace * (B * pauli u).trace = (2 : ℂ) ^ n * (A * B).trace := by
  have hpair (u : SympVec n) :
      (A * pauli u).trace * (B * pauli u).trace =
        ∑ p : (BitString n × BitString n) × (BitString n × BitString n),
          A p.1.1 p.1.2 * B p.2.1 p.2.2 * (pauli u p.1.2 p.1.1 * pauli u p.2.2 p.2.1) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b₁ _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₂ _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b₂ _ ↦ by ring
  simp_rw [hpair]
  rw [Finset.sum_comm]
  have hswap :
      (∑ p : (BitString n × BitString n) × (BitString n × BitString n),
        ∑ u : SympVec n,
          A p.1.1 p.1.2 * B p.2.1 p.2.2 * (pauli u p.1.2 p.1.1 * pauli u p.2.2 p.2.1)) =
      ∑ p : (BitString n × BitString n) × (BitString n × BitString n),
        A p.1.1 p.1.2 * B p.2.1 p.2.2 *
          (if p.1.2 = p.2.1 ∧ p.2.2 = p.1.1 then (2 : ℂ) ^ n else 0) := by
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.mul_sum, pauli_swap_completeness]
  rw [hswap]
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a₁ _ ↦ Finset.sum_congr rfl fun b₁ _ ↦ ?_
  rw [Finset.sum_eq_single b₁]
  · rw [Finset.sum_eq_single a₁]
    · simp; ring
    · intro b₂ _ hb2; simp [hb2]
    · intro h; exact absurd (mem_univ _) h
  · intro a₂ _ ha2
    refine Finset.sum_eq_zero fun b₂ _ ↦ ?_
    simp [Ne.symm ha2]
  · intro h; exact absurd (mem_univ _) h

/-- Triple Pauli sum: `∑_{u,v} Tr(A P_u) Tr(B P_v) Tr(C P_u P_v) = 4^n Tr(A B C)`. -/
theorem sum_trace_pauli_triple {n : ℕ} (A B C : Matrix (BitString n) (BitString n) ℂ) :
    ∑ u : SympVec n, ∑ v : SympVec n,
      (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace =
        ((2 : ℂ) ^ n) ^ 2 * (A * B * C).trace := by
  have hinner (u : SympVec n) :
      ∑ v : SympVec n, (B * pauli v).trace * (C * (pauli u * pauli v)).trace =
        (2 : ℂ) ^ n * (B * (C * pauli u)).trace := by
    have heq (v : SympVec n) :
        (C * (pauli u * pauli v)).trace = ((C * pauli u) * pauli v).trace := by
      rw [Matrix.mul_assoc]
    simp_rw [heq]
    exact sum_trace_pauli_mul_trace_pauli B (C * pauli u)
  calc
    ∑ u : SympVec n, ∑ v : SympVec n,
        (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace
        = ∑ u : SympVec n, (A * pauli u).trace *
            ∑ v : SympVec n, (B * pauli v).trace * (C * (pauli u * pauli v)).trace := by
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ ↦ by ring
    _ = ∑ u : SympVec n, (A * pauli u).trace * ((2 : ℂ) ^ n * (B * (C * pauli u)).trace) := by
      simp_rw [hinner]
    _ = (2 : ℂ) ^ n * ∑ u : SympVec n, (A * pauli u).trace * ((B * C) * pauli u).trace := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ ↦ by rw [Matrix.mul_assoc]; ring
    _ = (2 : ℂ) ^ n * ((2 : ℂ) ^ n * (A * (B * C)).trace) := by
      rw [sum_trace_pauli_mul_trace_pauli]
    _ = ((2 : ℂ) ^ n) ^ 2 * (A * B * C).trace := by
      rw [Matrix.mul_assoc]; ring

/-- Commuting-pair triple Pauli sum:
`∑_{[u,v]=0} Tr(A P_u) Tr(B P_v) Tr(C P_u P_v) = (4^n / 2) (Tr(A B C) + Tr(A C B))`. -/
theorem sum_commuting_trace_pauli_triple {n : ℕ} (A B C : Matrix (BitString n) (BitString n) ℂ) :
    ∑ u : SympVec n, ∑ v ∈ Finset.univ.filter (fun v ↦ sympForm u v = 0),
      (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace =
        (((2 : ℂ) ^ n) ^ 2 / 2) * ((A * B * C).trace + (A * C * B).trace) := by
  have hhalf (u v : SympVec n) :
      (if sympForm u v = 0 then (C * (pauli u * pauli v)).trace else 0) =
        (2 : ℂ)⁻¹ * ((C * (pauli u * pauli v)).trace + (C * (pauli v * pauli u)).trace) := by
    have hcomm := pauli_comm u v
    by_cases h : sympForm u v = 0
    · simp only [h, ite_true] at hcomm ⊢
      rw [one_smul] at hcomm
      rw [← hcomm]
      ring
    · simp only [h, ite_false] at hcomm ⊢
      rw [show ((-1 : ℂ) • (pauli v * pauli u)) = -(pauli v * pauli u) by simp] at hcomm
      rw [hcomm, Matrix.mul_neg, trace_neg, neg_add_cancel, mul_zero]
  have h1 :
      ∑ u : SympVec n, ∑ v ∈ Finset.univ.filter (fun v ↦ sympForm u v = 0),
          (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace =
      (2 : ℂ)⁻¹ *
        ((∑ u, ∑ v, (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace) +
         (∑ u, ∑ v, (A * pauli u).trace * (B * pauli v).trace * (C * (pauli v * pauli u)).trace))
           := by
    simp_rw [Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases h : sympForm u v = 0
    · have hhh := hhalf u v
      simp only [h, ite_true] at hhh ⊢
      calc
        (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace
            = (A * pauli u).trace * (B * pauli v).trace *
                ((2 : ℂ)⁻¹ * ((C * (pauli u * pauli v)).trace +
                  (C * (pauli v * pauli u)).trace)) := by
              conv_lhs => rw [hhh]
        _ = _ := by ring
    · have hhh := hhalf u v
      simp only [h, ite_false] at hhh ⊢
      have hz : (C * (pauli u * pauli v)).trace + (C * (pauli v * pauli u)).trace = 0 := by
        have := congrArg (2 * ·) hhh
        simpa [← mul_assoc] using this.symm
      rw [show (A * pauli u).trace * (B * pauli v).trace * (C * (pauli u * pauli v)).trace +
        (A * pauli u).trace * (B * pauli v).trace * (C * (pauli v * pauli u)).trace =
        (A * pauli u).trace * (B * pauli v).trace *
          ((C * (pauli u * pauli v)).trace + (C * (pauli v * pauli u)).trace) by ring,
        hz, mul_zero, mul_zero]
  rw [h1, sum_trace_pauli_triple A B C]
  have h2 : ∑ u : SympVec n, ∑ v : SympVec n,
      (A * pauli u).trace * (B * pauli v).trace * (C * (pauli v * pauli u)).trace =
        ((2 : ℂ) ^ n) ^ 2 * (A * C * B).trace := by
    rw [Finset.sum_comm]
    have hrew : ∑ v : SympVec n, ∑ u : SympVec n,
        (A * pauli u).trace * (B * pauli v).trace * (C * (pauli v * pauli u)).trace =
        ∑ v : SympVec n, ∑ u : SympVec n,
          (B * pauli v).trace * (A * pauli u).trace * (C * (pauli v * pauli u)).trace :=
      Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun u _ ↦ by ring
    rw [hrew, sum_trace_pauli_triple B A C]
    congr 1
    rw [Matrix.mul_assoc B A C, trace_mul_comm B]
  rw [h2]
  ring

end MultiqubitPauli

end CslibFrontier.Quantum
