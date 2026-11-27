module

public import CslibFrontier.Foundations.Data.Code.FiniteFieldFourier
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Finset.Card

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Empirical Row Distributions and the Method of Types

This module develops base-`q` Shannon entropy and Kullback–Leibler divergence for finite `PMF`s,
empirical distributions `empDist` of finite tuples and matrix rows, type classes `ℳ_{n,τ}`, the
polynomial upper bound `(n + 1) ^ |α|` on the number of `n`-feasible types, Cover–Thomas
, and two-sided multinomial entropy bounds on `|ℳ_{n,τ}|`. All results are proved
under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Foundations.Data.Code.pmfEntropyBase`:
  base-`q` Shannon entropy `H_q(τ)` of a `PMF`.
* `CslibFrontier.Foundations.Data.Code.pmfKLBase`: base-`q` KL divergence `D_{KL,q}(τ ‖ σ)`.
* `CslibFrontier.Foundations.Data.Code.empDist`: empirical distribution of `A : Fin n → α`.
* `CslibFrontier.Foundations.Data.Code.typeClassFinset`: the type class `ℳ_{n,τ}` of tuples with
  empirical distribution `τ`.
* `CslibFrontier.Foundations.Data.Code.feasibleTypesFinset`: the set of `n`-feasible distributions
  over `α`.
* `CslibFrontier.Foundations.Data.Code.IsFeasibleType`: predicate that `τ` is `n`-feasible.

## Main results

* `CslibFrontier.Foundations.Data.Code.empDist_eq_iff_exists_perm`: two tuples share the same
  empirical distribution iff they differ by a coordinate permutation.
* `CslibFrontier.Foundations.Data.Code.card_feasibleTypesFinset_le`: at most `(n + 1) ^ |α|`
  `n`-feasible distributions over `α`.
* `CslibFrontier.Foundations.Data.Code.prob_empDist_eq_le_kl`: Cover–Thomas.
* `CslibFrontier.Foundations.Data.Code.card_typeClassFinset_le` and
  `card_typeClassFinset_ge`: two-sided multinomial entropy bounds on `|ℳ_{n,τ}|`.

## Tags

method of types, empirical distribution, Shannon entropy, KL divergence, multinomial
-/

public section

namespace CslibFrontier.Foundations.Data.Code

/-! ### Base-`q` Entropy and KL-Divergence -/

/-- Base-`q` Shannon entropy `H_q(τ) = -∑ x, τ(x) log_q τ(x)` of a finite `PMF`. -/
noncomputable def pmfEntropyBase {α : Type*} [Fintype α] (q : ℝ) (τ : PMF α) : ℝ :=
  (∑ x : α, Real.negMulLog (τ x).toReal) / Real.log q

/-- Base-`q` Kullback–Leibler divergence `D_{KL,q}(τ ‖ σ) = ∑ x, τ(x) log_q (τ(x)/σ(x))`. -/
noncomputable def pmfKLBase {α : Type*} [Fintype α] (q : ℝ) (τ σ : PMF α) : ℝ :=
  (∑ x : α, (τ x).toReal * Real.log ((τ x).toReal / (σ x).toReal)) / Real.log q

theorem pmfKLBase_eq_div_log {α : Type*} [Fintype α] (q : ℝ) (τ σ : PMF α) :
    pmfKLBase q τ σ =
      (∑ x : α, (τ x).toReal * Real.log ((τ x).toReal / (σ x).toReal)) / Real.log q := by rfl

theorem pmfEntropyBase_eq_div_log {α : Type*} [Fintype α] (q : ℝ) (τ : PMF α) :
    pmfEntropyBase q τ = (∑ x : α, Real.negMulLog (τ x).toReal) / Real.log q := by rfl

@[simp]
theorem pmfKLBase_self {α : Type*} [Fintype α] (q : ℝ) (τ : PMF α) :
    pmfKLBase q τ τ = 0 := by
  unfold pmfKLBase
  have h : ∀ x : α, (τ x).toReal * Real.log ((τ x).toReal / (τ x).toReal) = 0 := fun x ↦ by
    by_cases hx : (τ x).toReal = 0
    · simp [hx]
    · rw [div_self hx, Real.log_one, mul_zero]
  rw [Finset.sum_eq_zero fun x _ ↦ h x, zero_div]

theorem pmfSumToReal_eq_one {α : Type*} [Fintype α] (τ : PMF α) :
    ∑ x : α, (τ x).toReal = 1 := by
  have hsum : ∑ a : α, τ a = 1 :=
    (tsum_fintype (fun a : α ↦ τ a)).symm.trans τ.tsum_coe
  rw [← ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _), hsum, ENNReal.toReal_one]

theorem pmf_toReal_le_one {α : Type*} (τ : PMF α) (x : α) : (τ x).toReal ≤ 1 := by
  have hle : τ x ≤ 1 := PMF.coe_le_one τ x
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle

theorem pmfEntropyBase_nonneg {α : Type*} [Fintype α] {q : ℝ} (hq : 1 < q) (τ : PMF α) :
    0 ≤ pmfEntropyBase q τ := by
  unfold pmfEntropyBase
  refine div_nonneg (Finset.sum_nonneg fun x _ ↦ ?_) (Real.log_pos hq).le
  exact Real.negMulLog_nonneg ENNReal.toReal_nonneg (pmf_toReal_le_one τ x)

theorem pmfEntropyBase_eq_sum_logb {α : Type*} [Fintype α] (q : ℝ) (τ : PMF α) :
    pmfEntropyBase q τ = -∑ x : α, (τ x).toReal * Real.logb q (τ x).toReal := by
  unfold pmfEntropyBase Real.logb
  simp_rw [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_div]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

theorem pmfEntropyBase_le_logb_card {α : Type*} [Fintype α] [Nonempty α] {q : ℝ} (hq : 1 < q)
    (τ : PMF α) :
    pmfEntropyBase q τ ≤ Real.logb q (Fintype.card α) := by
  have hlogq : 0 < Real.log q := Real.log_pos hq
  unfold pmfEntropyBase Real.logb
  refine div_le_div_of_nonneg_right ?_ hlogq.le
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hstep :
      ∑ x : α, Real.negMulLog (τ x).toReal - Real.log (Fintype.card α) ≤ 0 := by
    have h1 :
        ∑ x : α, Real.negMulLog (τ x).toReal - Real.log (Fintype.card α) =
          ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
            (τ x).toReal * Real.log (1 / ((Fintype.card α : ℝ) * (τ x).toReal)) := by
      have hsum_filt :
          ∑ x : α, (τ x).toReal =
            ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (τ x).toReal := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        split_ifs with h
        · rfl
        · exact le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
      have hsum_neg :
          ∑ x : α, Real.negMulLog (τ x).toReal =
            ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
              Real.negMulLog (τ x).toReal := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        split_ifs with h
        · rfl
        · have h0 : (τ x).toReal = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
          simp [h0]
      have hlog_eq : Real.log (Fintype.card α) =
          ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
            (τ x).toReal * Real.log (Fintype.card α) := by
        rw [← Finset.sum_mul, ← hsum_filt, pmfSumToReal_eq_one, one_mul]
      rw [hsum_neg, hlog_eq, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hxpos : 0 < (τ x).toReal := (Finset.mem_filter.mp hx).2
      rw [Real.negMulLog, one_div, Real.log_inv, Real.log_mul hcard.ne' hxpos.ne']
      ring
    rw [h1]
    calc
      ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
          (τ x).toReal * Real.log (1 / ((Fintype.card α : ℝ) * (τ x).toReal))
          ≤ ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
              (τ x).toReal * (1 / ((Fintype.card α : ℝ) * (τ x).toReal) - 1) := by
        refine Finset.sum_le_sum fun x hx ↦ ?_
        have hxpos : 0 < (τ x).toReal := (Finset.mem_filter.mp hx).2
        refine mul_le_mul_of_nonneg_left ?_ hxpos.le
        exact Real.log_le_sub_one_of_pos (by positivity)
      _ = ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
            ((Fintype.card α : ℝ)⁻¹ - (τ x).toReal) := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hxpos : 0 < (τ x).toReal := (Finset.mem_filter.mp hx).2
        field_simp [hcard.ne', hxpos.ne']
      _ = ((Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal)).card : ℝ) *
            (Fintype.card α : ℝ)⁻¹ -
            ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (τ x).toReal := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card α : ℝ) * (Fintype.card α : ℝ)⁻¹ - 1 := by
        have hle1 : ((Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal)).card : ℝ) ≤
            (Fintype.card α : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
        have hsum1 :
            ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (τ x).toReal = 1 := by
          rw [Finset.sum_filter]
          calc
            ∑ x : α, (if 0 < (τ x).toReal then (τ x).toReal else 0) =
                ∑ x : α, (τ x).toReal :=
              Finset.sum_congr rfl fun x _ ↦ by
                split_ifs with h
                · rfl
                · exact (le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg).symm
            _ = 1 := pmfSumToReal_eq_one τ
        rw [hsum1]
        have hinv : (0 : ℝ) ≤ (Fintype.card α : ℝ)⁻¹ := by positivity
        nlinarith
      _ = 0 := by rw [mul_inv_cancel₀ hcard.ne', sub_self]
  linarith

theorem pmfKLBase_nonneg {α : Type*} [Fintype α] {q : ℝ} (hq : 1 < q) {τ σ : PMF α}
    (hsupp : τ.support ⊆ σ.support) :
    0 ≤ pmfKLBase q τ σ := by
  have hlogq : 0 < Real.log q := Real.log_pos hq
  unfold pmfKLBase
  refine div_nonneg ?_ hlogq.le
  have hneg :
      -(∑ x : α, (τ x).toReal * Real.log ((τ x).toReal / (σ x).toReal)) ≤ 0 := by
    have h1 :
        -(∑ x : α, (τ x).toReal * Real.log ((τ x).toReal / (σ x).toReal)) =
          ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
            (τ x).toReal * Real.log ((σ x).toReal / (τ x).toReal) := by
      rw [← Finset.sum_neg_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      split_ifs with h
      · have hσ : 0 < (σ x).toReal := by
          have hmem : x ∈ τ.support := by
            rw [PMF.mem_support_iff]
            intro h0
            simp [h0] at h
          have hσne : σ x ≠ 0 := by
            have := hsupp hmem
            rwa [PMF.mem_support_iff] at this
          exact ENNReal.toReal_pos hσne (PMF.apply_ne_top _ _)
        rw [← mul_neg, ← Real.log_inv, inv_div]
      · have h0 : (τ x).toReal = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
        simp [h0]
    rw [h1]
    calc
      ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
          (τ x).toReal * Real.log ((σ x).toReal / (τ x).toReal)
          ≤ ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
              (τ x).toReal * ((σ x).toReal / (τ x).toReal - 1) := by
        refine Finset.sum_le_sum fun x hx ↦ ?_
        have hxpos : 0 < (τ x).toReal := (Finset.mem_filter.mp hx).2
        have hσ : 0 < (σ x).toReal := by
          have hmem : x ∈ τ.support := by
            rw [PMF.mem_support_iff]
            intro h0
            simp [h0] at hxpos
          have hσne : σ x ≠ 0 := by
            have := hsupp hmem
            rwa [PMF.mem_support_iff] at this
          exact ENNReal.toReal_pos hσne (PMF.apply_ne_top _ _)
        exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hσ hxpos)) hxpos.le
      _ = ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal),
            ((σ x).toReal - (τ x).toReal) := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hxpos : 0 < (τ x).toReal := (Finset.mem_filter.mp hx).2
        field_simp [hxpos.ne']
      _ = (∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (σ x).toReal) -
            (∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (τ x).toReal) := by
        rw [Finset.sum_sub_distrib]
      _ ≤ 1 - 1 := by
        have hσ_le :
            ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (σ x).toReal ≤ 1 := by
          calc
            _ ≤ ∑ x : α, (σ x).toReal :=
              Finset.sum_le_univ_sum_of_nonneg fun _ ↦ ENNReal.toReal_nonneg
            _ = 1 := pmfSumToReal_eq_one σ
        have hτ_eq :
            ∑ x ∈ Finset.univ.filter (fun x : α ↦ 0 < (τ x).toReal), (τ x).toReal = 1 := by
          rw [Finset.sum_filter]
          calc
            ∑ x : α, (if 0 < (τ x).toReal then (τ x).toReal else 0) =
                ∑ x : α, (τ x).toReal :=
              Finset.sum_congr rfl fun x _ ↦ by
                split_ifs with h
                · rfl
                · exact (le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg).symm
            _ = 1 := pmfSumToReal_eq_one τ
        linarith
      _ = 0 := sub_self 1
  linarith

/-! ### Empirical Distributions, Type Classes, and Method of Types -/

/-- Empirical distribution of a tuple `A : Fin n → α` for `0 < n`. -/
noncomputable def empDist {α : Type*} {n : ℕ} (hn : 0 < n) (A : Fin n → α) : PMF α :=
  @empiricalPMF α (Fin n) _ ⟨⟨0, hn⟩⟩ A

/-- The type class `ℳ_{n,τ}` of all `A : Fin n → α` with empirical distribution `τ`. -/
noncomputable def typeClassFinset {α : Type*} [Fintype α] (n : ℕ) (hn : 0 < n) (τ : PMF α) :
    Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter fun A : Fin n → α ↦ empDist hn A = τ

/-- The finite set of all `n`-feasible distributions over `α`. -/
noncomputable def feasibleTypesFinset (α : Type*) [Fintype α] (n : ℕ) (hn : 0 < n) :
    Finset (PMF α) := by
  classical
  exact Finset.univ.image (empDist hn)

/-- A distribution `τ : PMF α` is `n`-feasible if some `A : Fin n → α` has `empDist hn A = τ`. -/
def IsFeasibleType {α : Type*} (n : ℕ) (hn : 0 < n) (τ : PMF α) : Prop :=
  ∃ A : Fin n → α, empDist hn A = τ

theorem isFeasibleType_iff {α : Type*} {n : ℕ} {hn : 0 < n} {τ : PMF α} :
    IsFeasibleType n hn τ ↔ ∃ A : Fin n → α, empDist hn A = τ := by rfl

@[simp]
theorem mem_typeClassFinset {α : Type*} [Fintype α] {n : ℕ} {hn : 0 < n} {τ : PMF α}
    {A : Fin n → α} :
    A ∈ typeClassFinset n hn τ ↔ empDist hn A = τ := by
  classical
  simp [typeClassFinset]

@[simp]
theorem mem_feasibleTypesFinset {α : Type*} [Fintype α] {n : ℕ} {hn : 0 < n} {τ : PMF α} :
    τ ∈ feasibleTypesFinset α n hn ↔ IsFeasibleType n hn τ := by
  classical
  simp [feasibleTypesFinset, IsFeasibleType]

theorem empDist_eq_empiricalPMF {α : Type*} {n : ℕ} (hn : 0 < n) [Nonempty (Fin n)]
    (A : Fin n → α) :
    empDist hn A = empiricalPMF A := by
  unfold empDist
  rfl

theorem empDist_apply_toReal {α : Type*} [DecidableEq α] {n : ℕ} (hn : 0 < n) (A : Fin n → α)
    (x : α) :
    (empDist hn A x).toReal =
      ((Finset.univ.filter fun i : Fin n ↦ A i = x).card : ℝ) / (n : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [empDist, empiricalPMF_apply_toReal, Fintype.card_fin]

theorem empDist_map {α β : Type*} {n : ℕ} (hn : 0 < n) (A : Fin n → α) (f : α → β) :
    (empDist hn A).map f = empDist hn (f ∘ A) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact empiricalPMF_map A f

theorem support_empDist {α : Type*} {n : ℕ} (hn : 0 < n) (A : Fin n → α) :
    (empDist hn A).support = Set.range A := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact support_empiricalPMF A

theorem empDist_comp_perm {α : Type*} {n : ℕ} (hn : 0 < n) (A : Fin n → α)
    (π : Equiv.Perm (Fin n)) :
    empDist hn (A ∘ π) = empDist hn A := by
  classical
  ext x
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _) |>.mp ?_
  simp only [empDist_apply_toReal, Function.comp_apply]
  congr 1
  exact_mod_cast Finset.card_equiv π (fun i ↦ by simp)

/-- Two tuples have the same empirical distribution iff one is a coordinate permutation of the
other. -/
theorem empDist_eq_iff_exists_perm {α : Type*} {n : ℕ} (hn : 0 < n) (A B : Fin n → α) :
    empDist hn A = empDist hn B ↔ ∃ π : Equiv.Perm (Fin n), A ∘ π = B := by
  classical
  constructor
  · intro h
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hcard : ∀ x : α,
        (Finset.univ.filter fun i : Fin n ↦ A i = x).card =
          (Finset.univ.filter fun i : Fin n ↦ B i = x).card := by
      intro x
      have hx := congrArg (fun p : PMF α ↦ (p x).toReal) h
      simp only [empDist_apply_toReal] at hx
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hcast : ((Finset.univ.filter fun i : Fin n ↦ A i = x).card : ℝ) =
          ((Finset.univ.filter fun i : Fin n ↦ B i = x).card : ℝ) := by
        field_simp [hn0] at hx
        exact hx
      exact_mod_cast hcast
    have hequiv : ∀ x : α,
        {i : Fin n // A i = x} ≃ {i : Fin n // B i = x} := fun x ↦ by
      apply Fintype.equivOfCardEq
      simp only [Fintype.card_subtype]
      exact hcard x
    let e : Fin n ≃ Fin n :=
      (Equiv.sigmaFiberEquiv B).symm.trans
        ((Equiv.sigmaCongrRight fun x ↦ (hequiv x).symm).trans (Equiv.sigmaFiberEquiv A))
    refine ⟨e, funext fun i ↦ ?_⟩
    exact ((hequiv (B i)).symm ⟨i, rfl⟩).2
  · rintro ⟨π, rfl⟩
    exact (empDist_comp_perm hn A π).symm

/-- Fact (Number of types): there are at most `(n + 1) ^ |α|` `n`-feasible types over `α`. -/
theorem card_feasibleTypesFinset_le (α : Type*) [Fintype α] (n : ℕ) (hn : 0 < n) :
    (feasibleTypesFinset α n hn).card ≤ (n + 1) ^ Fintype.card α := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let f : PMF α → (α → Fin (n + 1)) := fun τ x ↦
    ⟨Nat.floor ((n : ℝ) * (τ x).toReal + 1 / 2), by
      have hle : (τ x).toReal ≤ 1 := pmf_toReal_le_one τ x
      have hlt : (n : ℝ) * (τ x).toReal + 1 / 2 < (n + 1 : ℕ) := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        push_cast
        nlinarith
      exact Nat.floor_lt (by positivity) |>.mpr hlt⟩
  have hinj : Set.InjOn f (feasibleTypesFinset α n hn : Set (PMF α)) := by
    intro τ₁ h₁ τ₂ h₂ hfeq
    obtain ⟨A₁, rfl⟩ := mem_feasibleTypesFinset.mp h₁
    obtain ⟨A₂, rfl⟩ := mem_feasibleTypesFinset.mp h₂
    ext x
    have hx := congrArg (fun g : α → Fin (n + 1) ↦ (g x).val) hfeq
    simp only [f] at hx
    have hcount : ∀ A : Fin n → α,
        Nat.floor ((n : ℝ) * (empDist hn A x).toReal + 1 / 2) =
          (Finset.univ.filter fun i : Fin n ↦ A i = x).card := by
      intro A
      rw [empDist_apply_toReal]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [mul_div_cancel₀ _ hn0]
      refine Nat.floor_eq_iff (by positivity) |>.mpr ⟨?_, ?_⟩
      · linarith
      · linarith
    rw [hcount A₁, hcount A₂] at hx
    refine ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _) |>.mp ?_
    simp only [empDist_apply_toReal, hx]
  calc
    (feasibleTypesFinset α n hn).card
        = ((feasibleTypesFinset α n hn).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (α → Fin (n + 1))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = (n + 1) ^ Fintype.card α := by simp [Fintype.card_pi]

private lemma prod_toReal_eq_rpow_of_mem_typeClass {α : Type*} [Fintype α] {n : ℕ} {hn : 0 < n}
    {q : ℝ} (hq : 1 < q) {τ σ : PMF α} {A : Fin n → α} (hA : A ∈ typeClassFinset n hn τ)
    (hsupp : τ.support ⊆ σ.support) :
    ∏ i : Fin n, (σ (A i)).toReal =
      q ^ ((n : ℝ) * (∑ x : α, (τ x).toReal * Real.log ((σ x).toReal)) / Real.log q) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hcount : ∀ x : α,
      ((Finset.univ.filter fun i : Fin n ↦ A i = x).card : ℝ) = (n : ℝ) * (τ x).toReal := by
    intro x
    have hx := congrArg (fun p : PMF α ↦ (p x).toReal) (mem_typeClassFinset.mp hA)
    rw [empDist_apply_toReal] at hx
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hn0] at hx
    linarith
  have hprod :
      ∏ i : Fin n, (σ (A i)).toReal =
        ∏ x : α, (σ x).toReal ^ (Finset.univ.filter fun i : Fin n ↦ A i = x).card := by
    rw [← Finset.prod_fiberwise_of_maps_to (fun i _ ↦ Finset.mem_univ (A i))]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    calc
      ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ A i = x), (σ (A i)).toReal
          = ∏ _i ∈ Finset.univ.filter (fun i : Fin n ↦ A i = x), (σ x).toReal :=
        Finset.prod_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2]
      _ = (σ x).toReal ^ (Finset.univ.filter fun i : Fin n ↦ A i = x).card := by
        rw [Finset.prod_const]
  rw [hprod]
  have hrhs :
      q ^ ((n : ℝ) * (∑ x : α, (τ x).toReal * Real.log (σ x).toReal) / Real.log q) =
        Real.exp (∑ x : α, ((n : ℝ) * (τ x).toReal) * Real.log (σ x).toReal) := by
    rw [Real.rpow_def_of_pos hqpos]
    congr 1
    have hmul : Real.log q * ((n : ℝ) * (∑ x : α, (τ x).toReal * Real.log (σ x).toReal) /
        Real.log q) = ∑ x : α, (n : ℝ) * (τ x).toReal * Real.log (σ x).toReal := by
      rw [mul_div_cancel₀ _ hlogq.ne', Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ by ring
    exact hmul
  rw [hrhs, Real.exp_sum]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  rw [← hcount x]
  by_cases hcx : (Finset.univ.filter fun i : Fin n ↦ A i = x).card = 0
  · simp [hcx]
  · have hcpos : 0 < (Finset.univ.filter fun i : Fin n ↦ A i = x).card :=
      Nat.pos_of_ne_zero hcx
    have hτpos : 0 < (τ x).toReal := by
      have h := hcount x
      have hpos : (0 : ℝ) < (n : ℝ) * (τ x).toReal := by
        rw [← h]; exact Nat.cast_pos.mpr hcpos
      exact pos_of_mul_pos_right hpos (Nat.cast_nonneg n)
    have hmem : x ∈ τ.support := by
      rw [PMF.mem_support_iff]
      intro h0; simp [h0] at hτpos
    have hσpos : 0 < (σ x).toReal := by
      have hσne : σ x ≠ 0 := by
        have := hsupp hmem
        rwa [PMF.mem_support_iff] at this
      exact ENNReal.toReal_pos hσne (PMF.apply_ne_top _ _)
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hσpos, mul_comm]

private lemma sum_prod_toReal_eq_one {α : Type*} [Fintype α] (n : ℕ) (σ : PMF α) :
    ∑ A : Fin n → α, ∏ i : Fin n, (σ (A i)).toReal = 1 := by
  have h := (Fintype.prod_sum (fun (_ : Fin n) (x : α) ↦ (σ x).toReal)).symm
  simpa [pmfSumToReal_eq_one σ] using h

/-- Exact multinomial counting formula for a type class `|ℳ_{n,τ}|`. -/
private lemma card_typeClass_mul_prod_factorial {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    {hn : 0 < n} {τ : PMF α} {A₀ : Fin n → α} (hA₀ : A₀ ∈ typeClassFinset n hn τ) :
    (typeClassFinset n hn τ).card *
        ∏ x : α, ((Finset.univ.filter fun i : Fin n ↦ A₀ i = x).card).factorial =
      n.factorial := by
  classical
  have htrans : ∀ A ∈ typeClassFinset n hn τ,
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ A₀ ∘ π = A).card =
        ∏ x : α, ((Finset.univ.filter fun i : Fin n ↦ A₀ i = x).card).factorial := by
    intro A hA
    have heq : empDist hn A₀ = empDist hn A :=
      (mem_typeClassFinset.mp hA₀).trans (mem_typeClassFinset.mp hA).symm
    obtain ⟨π₀, hπ₀⟩ := (empDist_eq_iff_exists_perm hn A₀ A).mp heq
    have hbij :
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ A₀ ∘ π = A).card =
          (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦ A₀ ∘ σ = A₀).card := by
      refine Finset.card_bij (fun π _ ↦ π * π₀⁻¹) ?_ ?_ ?_
      · intro π hπ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
        ext i
        have h1 := congrFun hπ (π₀⁻¹ i)
        have h2 := congrFun hπ₀ (π₀⁻¹ i)
        simp only [Function.comp_apply, Equiv.Perm.mul_apply] at h1 h2 ⊢
        rw [h1, ← h2]
        simp
      · intro π₁ _ π₂ _ h
        exact mul_right_cancel h
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        refine ⟨σ * π₀, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        ext i
        have h1 := congrFun hσ (π₀ i)
        have h2 := congrFun hπ₀ i
        simp only [Function.comp_apply, Equiv.Perm.mul_apply] at h1 h2 ⊢
        rw [h1, h2]
    rw [hbij]
    let stabEquiv :
        {σ : Equiv.Perm (Fin n) // A₀ ∘ σ = A₀} ≃
          ∀ x : α, Equiv.Perm {i : Fin n // A₀ i = x} :=
      { toFun := fun ⟨σ, hσ⟩ x ↦
          { toFun := fun ⟨i, hi⟩ ↦ ⟨σ i, by simpa [Function.comp_apply, hi] using congrFun hσ i⟩
            invFun := fun ⟨i, hi⟩ ↦
              ⟨σ⁻¹ i, by
                have h := congrFun hσ (σ⁻¹ i)
                simpa [Function.comp_apply, hi] using h.symm⟩
            left_inv := fun ⟨i, _⟩ ↦ by simp
            right_inv := fun ⟨i, _⟩ ↦ by simp }
        invFun := fun f ↦
          ⟨(Equiv.sigmaFiberEquiv A₀).symm.trans
              ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv A₀)), by
            ext i
            exact ((f (A₀ i)) ⟨i, rfl⟩).2⟩
        left_inv := fun ⟨σ, hσ⟩ ↦ by
          ext i
          rfl
        right_inv := fun f ↦ by
          funext x
          ext ⟨i, hi⟩
          subst hi
          rfl }
    have hcard_eq :
        (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦ A₀ ∘ σ = A₀).card =
          Fintype.card (∀ x : α, Equiv.Perm {i : Fin n // A₀ i = x}) := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr stabEquiv
    rw [hcard_eq, Fintype.card_pi]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [Fintype.card_perm, Fintype.card_subtype]
  have hsum :
      ∑ A ∈ typeClassFinset n hn τ,
          (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ A₀ ∘ π = A).card =
        Fintype.card (Equiv.Perm (Fin n)) := by
    rw [← Finset.card_biUnion]
    · have huniv :
          (typeClassFinset n hn τ).biUnion
              (fun A ↦ Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ A₀ ∘ π = A) =
            Finset.univ := by
        ext π
        simp only [Finset.mem_biUnion, mem_typeClassFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, iff_true]
        exact ⟨A₀ ∘ π, (empDist_comp_perm hn A₀ π).trans (mem_typeClassFinset.mp hA₀), rfl⟩
      rw [huniv, Finset.card_univ]
    · intro A₁ _ A₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro π h₁ h₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact hne (h₁.symm.trans h₂)
  have hsum' :
      ∑ A ∈ typeClassFinset n hn τ,
          (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ A₀ ∘ π = A).card =
        (typeClassFinset n hn τ).card *
          ∏ x : α, ((Finset.univ.filter fun i : Fin n ↦ A₀ i = x).card).factorial := by
    calc
      ∑ A ∈ typeClassFinset n hn τ,
          (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ A₀ ∘ π = A).card
          = ∑ _A ∈ typeClassFinset n hn τ,
              ∏ x : α, ((Finset.univ.filter fun i : Fin n ↦ A₀ i = x).card).factorial :=
        Finset.sum_congr rfl htrans
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  rw [← hsum', hsum, Fintype.card_perm, Fintype.card_fin]

/-- Upper bound of the method of types: `|ℳ_{n,τ}| ≤ q ^ (n * H_q(τ))`. -/
theorem card_typeClassFinset_le {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 1 < q)
    (τ : PMF α) :
    ((typeClassFinset n hn τ).card : ℝ) ≤ q ^ ((n : ℝ) * pmfEntropyBase q τ) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hsum_le :
      ∑ A ∈ typeClassFinset n hn τ, ∏ i : Fin n, (τ (A i)).toReal ≤ 1 := by
    calc
      ∑ A ∈ typeClassFinset n hn τ, ∏ i : Fin n, (τ (A i)).toReal
          ≤ ∑ A : Fin n → α, ∏ i : Fin n, (τ (A i)).toReal :=
        Finset.sum_le_univ_sum_of_nonneg fun _ ↦
          Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
      _ = 1 := sum_prod_toReal_eq_one n τ
  have hconst : ∀ A ∈ typeClassFinset n hn τ,
      ∏ i : Fin n, (τ (A i)).toReal = q ^ (-(n : ℝ) * pmfEntropyBase q τ) := by
    intro A hA
    rw [prod_toReal_eq_rpow_of_mem_typeClass hq hA (Set.Subset.refl _)]
    congr 1
    unfold pmfEntropyBase
    simp_rw [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum_le
  have hpow_pos : 0 < q ^ (-(n : ℝ) * pmfEntropyBase q τ) := Real.rpow_pos_of_pos hqpos _
  have h1 : ((typeClassFinset n hn τ).card : ℝ) ≤ (q ^ (-(n : ℝ) * pmfEntropyBase q τ))⁻¹ := by
    rwa [← le_div_iff₀ hpow_pos, one_div] at hsum_le
  rwa [← Real.rpow_neg hqpos.le, neg_mul, neg_neg] at h1

/-- Fact: for i.i.d. draws from `σ`,
`Pr[empDist A = τ] ≤ q ^ (-n * D_{KL,q}(τ ‖ σ))`.
-/
theorem prob_empDist_eq_le_kl {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 1 < q)
    (τ σ : PMF α) (hsupp : τ.support ⊆ σ.support) :
    ∑ A ∈ typeClassFinset n hn τ, ∏ i : Fin n, (σ (A i)).toReal ≤
      q ^ (-(n : ℝ) * pmfKLBase q τ σ) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hconst : ∀ A ∈ typeClassFinset n hn τ,
      ∏ i : Fin n, (σ (A i)).toReal =
        q ^ ((n : ℝ) * (∑ x : α, (τ x).toReal * Real.log (σ x).toReal) / Real.log q) :=
    fun A hA ↦ prod_toReal_eq_rpow_of_mem_typeClass hq hA hsupp
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  calc
    ((typeClassFinset n hn τ).card : ℝ) *
        q ^ ((n : ℝ) * (∑ x : α, (τ x).toReal * Real.log (σ x).toReal) / Real.log q)
        ≤ q ^ ((n : ℝ) * pmfEntropyBase q τ) *
            q ^ ((n : ℝ) * (∑ x : α, (τ x).toReal * Real.log (σ x).toReal) / Real.log q) :=
      mul_le_mul_of_nonneg_right (card_typeClassFinset_le hn hq τ)
        (Real.rpow_nonneg hqpos.le _)
    _ = q ^ ((n : ℝ) * pmfEntropyBase q τ +
          (n : ℝ) * (∑ x : α, (τ x).toReal * Real.log (σ x).toReal) / Real.log q) :=
      (Real.rpow_add hqpos _ _).symm
    _ = q ^ (-(n : ℝ) * pmfKLBase q τ σ) := by
      congr 1
      unfold pmfEntropyBase pmfKLBase
      have hlogq : Real.log q ≠ 0 := (Real.log_pos hq).ne'
      have hsum :
          ∑ x : α, (τ x).toReal * Real.log ((τ x).toReal / (σ x).toReal) =
            (∑ x : α, (τ x).toReal * Real.log (τ x).toReal) -
              ∑ x : α, (τ x).toReal * Real.log (σ x).toReal := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        by_cases hτ0 : (τ x).toReal = 0
        · simp [hτ0]
        · have hτpos : 0 < (τ x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hτ0)
          have hmem : x ∈ τ.support := by
            rw [PMF.mem_support_iff]; intro h0; simp [h0] at hτpos
          have hσpos : 0 < (σ x).toReal := by
            have hσne : σ x ≠ 0 := by
              have := hsupp hmem
              rwa [PMF.mem_support_iff] at this
            exact ENNReal.toReal_pos hσne (PMF.apply_ne_top _ _)
          rw [Real.log_div hτpos.ne' hσpos.ne']
          ring
      rw [hsum]
      simp_rw [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
      field_simp [hlogq]
      ring

/-- Lower bound of the method of types: for `n`-feasible `τ`,
`((n + 1) ^ |α|)⁻¹ * q ^ (n * H_q(τ)) ≤ |ℳ_{n,τ}|`. -/
theorem card_typeClassFinset_ge {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 1 < q)
    {τ : PMF α} (hτ : IsFeasibleType n hn τ) :
    (((n + 1 : ℝ) ^ Fintype.card α)⁻¹) * q ^ ((n : ℝ) * pmfEntropyBase q τ) ≤
      ((typeClassFinset n hn τ).card : ℝ) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  let P : PMF α → ℝ := fun τ' ↦ ∑ A ∈ typeClassFinset n hn τ', ∏ i : Fin n, (τ (A i)).toReal
  have hP_max : ∀ τ' ∈ feasibleTypesFinset α n hn, P τ' ≤ P τ := by
    have hne : (feasibleTypesFinset α n hn).Nonempty := ⟨τ, mem_feasibleTypesFinset.mpr hτ⟩
    obtain ⟨τ_star, hτ_star_mem, hτ_star_max⟩ :=
      Finset.exists_max_image (feasibleTypesFinset α n hn) P hne
    suffices h : P τ_star ≤ P τ from fun τ' hτ' ↦ (hτ_star_max τ' hτ').trans h
    by_cases heq : τ_star = τ
    · rw [heq]
    · obtain ⟨A₀, hA₀_eq⟩ := mem_feasibleTypesFinset.mp hτ_star_mem
      have hA₀ : A₀ ∈ typeClassFinset n hn τ_star := mem_typeClassFinset.mpr hA₀_eq
      obtain ⟨B₀, hB₀_eq⟩ := hτ
      have hBτ : IsFeasibleType n hn τ := ⟨B₀, hB₀_eq⟩
      have hB₀ : B₀ ∈ typeClassFinset n hn τ := mem_typeClassFinset.mpr hB₀_eq
      let c' : α → ℕ := fun x ↦ (Finset.univ.filter fun i : Fin n ↦ A₀ i = x).card
      let c : α → ℕ := fun x ↦ (Finset.univ.filter fun i : Fin n ↦ B₀ i = x).card
      have hc_eq : ∀ x : α, (c x : ℝ) = (n : ℝ) * (τ x).toReal := by
        intro x
        have hx := congrArg (fun p : PMF α ↦ (p x).toReal) hB₀_eq
        rw [empDist_apply_toReal] at hx
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        field_simp [hn0] at hx
        linarith
      have hc'_eq : ∀ x : α, (c' x : ℝ) = (n : ℝ) * (τ_star x).toReal := by
        intro x
        have hx := congrArg (fun p : PMF α ↦ (p x).toReal) hA₀_eq
        rw [empDist_apply_toReal] at hx
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        field_simp [hn0] at hx
        linarith
      have hc_ne : c' ≠ c := by
        intro hcc
        apply heq
        ext x
        refine ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _) |>.mp ?_
        have hx := congrFun hcc x
        have h1 := hc'_eq x; have h2 := hc_eq x
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        rw [hx] at h1
        exact mul_left_cancel₀ hn0 (h1.symm.trans h2)
      have hsum_c : ∑ x : α, c x = n := by
        have h := Finset.card_eq_sum_card_fiberwise (f := B₀) (s := Finset.univ) (t := Finset.univ)
          (fun i _ ↦ Finset.mem_univ (B₀ i))
        simpa [c] using h.symm
      have hsum_c' : ∑ x : α, c' x = n := by
        have h := Finset.card_eq_sum_card_fiberwise (f := A₀) (s := Finset.univ) (t := Finset.univ)
          (fun i _ ↦ Finset.mem_univ (A₀ i))
        simpa [c'] using h.symm
      have hex_gt : ∃ x : α, c x < c' x := by
        by_contra h
        push Not at h
        have hle_eq : ∀ x ∈ (Finset.univ : Finset α), c' x = c x :=
          fun x hx ↦ le_antisymm (h x) (by
            by_contra hlt
            have hlt' : c' x < c x := not_le.mp hlt
            have hsum_lt : ∑ z : α, c' z < ∑ z : α, c z :=
              Finset.sum_lt_sum (fun z _ ↦ h z) ⟨x, hx, hlt'⟩
            omega)
        exact hc_ne (funext fun x ↦ hle_eq x (Finset.mem_univ x))
      have hex_lt : ∃ y : α, c' y < c y := by
        by_contra h
        push Not at h
        have hge_eq : ∀ x ∈ (Finset.univ : Finset α), c x = c' x :=
          fun x hx ↦ le_antisymm (h x) (by
            by_contra hlt
            have hlt' : c x < c' x := not_le.mp hlt
            have hsum_lt : ∑ z : α, c z < ∑ z : α, c' z :=
              Finset.sum_lt_sum (fun z _ ↦ h z) ⟨x, hx, hlt'⟩
            omega)
        exact hc_ne (funext fun x ↦ (hge_eq x (Finset.mem_univ x)).symm)
      obtain ⟨x₀, hx₀⟩ := hex_gt
      obtain ⟨y₀, hy₀⟩ := hex_lt
      have hx₀_ne_y₀ : x₀ ≠ y₀ := by intro hxy; subst hxy; omega
      by_cases hτx₀ : (τ x₀).toReal = 0
      · have hP0 : P τ_star = 0 := by
          refine Finset.sum_eq_zero fun A hA ↦ ?_
          have hmem_x₀ : ∃ i : Fin n, A i = x₀ := by
            have hcard_eq : (Finset.univ.filter fun i : Fin n ↦ A i = x₀).card = c' x₀ := by
              have heqA := (mem_typeClassFinset.mp hA).trans hA₀_eq.symm
              have hx := congrArg (fun p : PMF α ↦ (p x₀).toReal) heqA
              rw [empDist_apply_toReal, empDist_apply_toReal] at hx
              have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
              have hcast : ((Finset.univ.filter fun i : Fin n ↦ A i = x₀).card : ℝ) =
                  (c' x₀ : ℝ) := by
                field_simp [hn0] at hx; exact hx
              exact_mod_cast hcast
            have hpos : 0 < (Finset.univ.filter fun i : Fin n ↦ A i = x₀).card := by omega
            obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
            exact ⟨i, (Finset.mem_filter.mp hi).2⟩
          obtain ⟨i, hi⟩ := hmem_x₀
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hτx₀])
        rw [hP0]
        exact Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
      · have hτx₀_pos : 0 < (τ x₀).toReal :=
          lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hτx₀)
        have hτy₀_pos : 0 < (τ y₀).toReal := by
          have h1 := hc_eq y₀
          have hpos : (0 : ℝ) < (n : ℝ) * (τ y₀).toReal := by
            rw [← h1]; exact Nat.cast_pos.mpr (by omega)
          exact pos_of_mul_pos_right hpos (Nat.cast_nonneg n)
        have hpos_x₀ : 0 < (Finset.univ.filter fun i : Fin n ↦ A₀ i = x₀).card := by
          change 0 < c' x₀; omega
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hpos_x₀
        have hi₀_eq : A₀ i₀ = x₀ := (Finset.mem_filter.mp hi₀).2
        let A₁ : Fin n → α := Function.update A₀ i₀ y₀
        let τ₁ : PMF α := empDist hn A₁
        have hτ₁_mem : τ₁ ∈ feasibleTypesFinset α n hn :=
          mem_feasibleTypesFinset.mpr ⟨A₁, rfl⟩
        have hA₁ : A₁ ∈ typeClassFinset n hn τ₁ := mem_typeClassFinset.mpr rfl
        have hP_formula : ∀ (τ' : PMF α) (A : Fin n → α) (hA : A ∈ typeClassFinset n hn τ'),
            P τ' *
                (∏ x : α, ((Finset.univ.filter fun i : Fin n ↦ A i = x).card.factorial : ℝ)) =
              (n.factorial : ℝ) *
                ∏ x : α, (τ x).toReal ^ (Finset.univ.filter fun i : Fin n ↦ A i = x).card := by
          intro τ' A hA
          have hconst : ∀ B ∈ typeClassFinset n hn τ',
              ∏ i : Fin n, (τ (B i)).toReal =
                ∏ x : α, (τ x).toReal ^ (Finset.univ.filter fun i : Fin n ↦ A i = x).card := by
            intro B hB
            rw [← Finset.prod_fiberwise_of_maps_to (fun i _ ↦ Finset.mem_univ (B i))]
            refine Finset.prod_congr rfl fun x _ ↦ ?_
            have hBcard : (Finset.univ.filter fun i : Fin n ↦ B i = x).card =
                (Finset.univ.filter fun i : Fin n ↦ A i = x).card := by
              have heqB := (mem_typeClassFinset.mp hB).trans (mem_typeClassFinset.mp hA).symm
              have hx := congrArg (fun p : PMF α ↦ (p x).toReal) heqB
              rw [empDist_apply_toReal, empDist_apply_toReal] at hx
              have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
              have hcast : ((Finset.univ.filter fun i : Fin n ↦ B i = x).card : ℝ) =
                  ((Finset.univ.filter fun i : Fin n ↦ A i = x).card : ℝ) := by
                field_simp [hn0] at hx; exact hx
              exact_mod_cast hcast
            rw [← hBcard]
            calc
              ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ B i = x), (τ (B i)).toReal
                  = ∏ _i ∈ Finset.univ.filter (fun i : Fin n ↦ B i = x), (τ x).toReal :=
                Finset.prod_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2]
              _ = _ := by rw [Finset.prod_const]
          dsimp only [P]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm, ← mul_assoc]
          have hfact := card_typeClass_mul_prod_factorial hA
          have hfactR :
              ((typeClassFinset n hn τ').card : ℝ) *
                  (∏ x : α,
                    ((Finset.univ.filter fun i : Fin n ↦ A i = x).card.factorial : ℝ)) =
                (n.factorial : ℝ) := by
            have := congrArg (Nat.cast (R := ℝ)) hfact
            simpa [Nat.cast_mul, Nat.cast_prod] using this
          rw [mul_comm _ ((typeClassFinset n hn τ').card : ℝ), hfactR]
        have hcount_A₁ : ∀ x : α,
            (Finset.univ.filter fun i : Fin n ↦ A₁ i = x).card =
              if x = x₀ then c' x₀ - 1 else if x = y₀ then c' y₀ + 1 else c' x := by
          intro x
          dsimp only [A₁, c']
          by_cases hx1 : x = x₀
          · rw [hx1]
            have hsub : Finset.univ.filter (fun i : Fin n ↦ Function.update A₀ i₀ y₀ i = x₀) =
                (Finset.univ.filter fun i : Fin n ↦ A₀ i = x₀).erase i₀ := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
              by_cases hi : i = i₀
              · subst hi
                simp only [Function.update_self, ne_eq, not_true_eq_false, false_and, iff_false]
                exact hx₀_ne_y₀.symm
              · simp [hi]
            rw [ite_eq_left rfl, hsub, Finset.card_erase_of_mem hi₀]
          · rw [ite_eq_right hx1]
            by_cases hx2 : x = y₀
            · rw [hx2]
              have hnotmem : i₀ ∉ Finset.univ.filter (fun i : Fin n ↦ A₀ i = y₀) := by
                simp [hi₀_eq, hx₀_ne_y₀]
              have hins :
                  Finset.univ.filter (fun i : Fin n ↦ Function.update A₀ i₀ y₀ i = y₀) =
                    insert i₀ (Finset.univ.filter fun i : Fin n ↦ A₀ i = y₀) := by
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
                by_cases hi : i = i₀
                · subst hi; simp
                · simp [hi]
              rw [ite_eq_left rfl, hins, Finset.card_insert_of_notMem hnotmem]
            · rw [ite_eq_right hx2]
              congr 1
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hi : i = i₀
              · subst hi; simp [hi₀_eq, Ne.symm hx1, Ne.symm hx2]
              · simp [hi]
        have hstrict : P τ_star < P τ₁ := by
          have hF₀ := hP_formula τ_star A₀ hA₀
          have hF₁ := hP_formula τ₁ A₁ hA₁
          let F_rest :=
            ∏ x ∈ (Finset.univ.erase x₀).erase y₀, ((c' x).factorial : ℝ)
          let G_rest :=
            ∏ x ∈ (Finset.univ.erase x₀).erase y₀, (τ x).toReal ^ c' x
          have hfact₀ :
              ∏ x : α, ((c' x).factorial : ℝ) =
                ((c' x₀).factorial : ℝ) * ((c' y₀).factorial : ℝ) * F_rest := by
            have hy_mem : y₀ ∈ (Finset.univ : Finset α).erase x₀ :=
              Finset.mem_erase.mpr ⟨Ne.symm hx₀_ne_y₀, Finset.mem_univ y₀⟩
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x₀),
              ← Finset.mul_prod_erase _ _ hy_mem, mul_assoc]
          have hfact₁ :
              ∏ x : α, ((Finset.univ.filter fun i : Fin n ↦ A₁ i = x).card.factorial : ℝ) =
                (((c' x₀ - 1).factorial : ℝ) * ((c' y₀ + 1).factorial : ℝ) * F_rest) := by
            have hy_mem : y₀ ∈ (Finset.univ : Finset α).erase x₀ :=
              Finset.mem_erase.mpr ⟨Ne.symm hx₀_ne_y₀, Finset.mem_univ y₀⟩
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x₀),
              ← Finset.mul_prod_erase _ _ hy_mem, mul_assoc]
            simp only [hcount_A₁, ↓reduceIte, hx₀_ne_y₀.symm]
            congr 1
            congr 1
            refine Finset.prod_congr rfl fun x hx ↦ ?_
            have hxy : x ≠ y₀ := (Finset.mem_erase.mp hx).1
            have hxx : x ≠ x₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            simp [hxx, hxy]
          have hpow₀ :
              ∏ x : α, (τ x).toReal ^ c' x =
                (τ x₀).toReal ^ c' x₀ * (τ y₀).toReal ^ c' y₀ * G_rest := by
            have hy_mem : y₀ ∈ (Finset.univ : Finset α).erase x₀ :=
              Finset.mem_erase.mpr ⟨Ne.symm hx₀_ne_y₀, Finset.mem_univ y₀⟩
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x₀),
              ← Finset.mul_prod_erase _ _ hy_mem, mul_assoc]
          have hpow₁ :
              ∏ x : α, (τ x).toReal ^ (Finset.univ.filter fun i : Fin n ↦ A₁ i = x).card =
                (τ x₀).toReal ^ (c' x₀ - 1) * (τ y₀).toReal ^ (c' y₀ + 1) * G_rest := by
            have hy_mem : y₀ ∈ (Finset.univ : Finset α).erase x₀ :=
              Finset.mem_erase.mpr ⟨Ne.symm hx₀_ne_y₀, Finset.mem_univ y₀⟩
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x₀),
              ← Finset.mul_prod_erase _ _ hy_mem, mul_assoc]
            simp only [hcount_A₁, ↓reduceIte, hx₀_ne_y₀.symm]
            congr 1
            congr 1
            refine Finset.prod_congr rfl fun x hx ↦ ?_
            have hxy : x ≠ y₀ := (Finset.mem_erase.mp hx).1
            have hxx : x ≠ x₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            simp [hxx, hxy]
          have hF₀' : P τ_star * (((c' x₀).factorial : ℝ) * ((c' y₀).factorial : ℝ) * F_rest) =
              (n.factorial : ℝ) * ((τ x₀).toReal ^ c' x₀ * (τ y₀).toReal ^ c' y₀ * G_rest) := by
            simpa [c', hfact₀, hpow₀] using hF₀
          have hF₁' :
              P τ₁ * (((c' x₀ - 1).factorial : ℝ) * ((c' y₀ + 1).factorial : ℝ) * F_rest) =
                (n.factorial : ℝ) *
                  ((τ x₀).toReal ^ (c' x₀ - 1) * (τ y₀).toReal ^ (c' y₀ + 1) * G_rest) := by
            simpa [hfact₁, hpow₁] using hF₁
          have hfac_x₀ :
              ((c' x₀).factorial : ℝ) = (c' x₀ : ℝ) * ((c' x₀ - 1).factorial : ℝ) := by
            have h := Nat.mul_factorial_pred (by omega : c' x₀ ≠ 0)
            exact_mod_cast h.symm
          have hfac_y₀ : ((c' y₀ + 1).factorial : ℝ) =
              ((c' y₀ : ℝ) + 1) * ((c' y₀).factorial : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            rfl
          have hpow_x₀ :
              (τ x₀).toReal ^ c' x₀ = (τ x₀).toReal * (τ x₀).toReal ^ (c' x₀ - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ c' x₀), pow_succ, mul_comm]
          have hpow_y₀ :
              (τ y₀).toReal ^ (c' y₀ + 1) = (τ y₀).toReal * (τ y₀).toReal ^ c' y₀ := by
            rw [pow_succ, mul_comm]
          have hF_pos : 0 < ((c' x₀ - 1).factorial : ℝ) * ((c' y₀).factorial : ℝ) * F_rest := by
            refine mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
              (Nat.cast_pos.mpr (Nat.factorial_pos _))) ?_
            exact Finset.prod_pos fun _ _ ↦ Nat.cast_pos.mpr (Nat.factorial_pos _)
          by_cases hG0 : G_rest = 0
          · exfalso
            have hP_star0 : P τ_star = 0 := by
              rw [hG0, mul_zero, mul_zero] at hF₀'
              have hfac_pos :
                  0 < ((c' x₀).factorial : ℝ) * ((c' y₀).factorial : ℝ) * F_rest := by
                rw [hfac_x₀]
                have hcx0 : (0 : ℝ) < (c' x₀ : ℝ) := Nat.cast_pos.mpr (by omega)
                nlinarith
              exact (mul_eq_zero.mp hF₀').resolve_right hfac_pos.ne'
            have hPτ_pos : 0 < P τ := by
              have hFτ := hP_formula τ B₀ hB₀
              have hprod_pos :
                  0 < ∏ x : α,
                    (τ x).toReal ^ (Finset.univ.filter fun i : Fin n ↦ B₀ i = x).card := by
                refine Finset.prod_pos fun x _ ↦ ?_
                by_cases h0 : (Finset.univ.filter fun i : Fin n ↦ B₀ i = x).card = 0
                · simp [h0]
                · have hcp : (0 : ℝ) < (n : ℝ) * (τ x).toReal := by
                    rw [← hc_eq x]; exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
                  exact pow_pos (pos_of_mul_pos_right hcp (Nat.cast_nonneg n)) _
              have hfac_pos :
                  0 < ∏ x : α,
                    ((Finset.univ.filter fun i : Fin n ↦ B₀ i = x).card.factorial : ℝ) :=
                Finset.prod_pos fun _ _ ↦ Nat.cast_pos.mpr (Nat.factorial_pos _)
              have hmul_pos : 0 < P τ *
                  ∏ x : α,
                    ((Finset.univ.filter fun i : Fin n ↦ B₀ i = x).card.factorial : ℝ) := by
                rw [hFτ]
                exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hprod_pos
              exact pos_of_mul_pos_left hmul_pos hfac_pos.le
            have := hτ_star_max τ (mem_feasibleTypesFinset.mpr hBτ)
            linarith
          · have hG_pos : 0 < G_rest :=
              lt_of_le_of_ne
                (Finset.prod_nonneg fun _ _ ↦ pow_nonneg ENNReal.toReal_nonneg _) (Ne.symm hG0)
            have hratio : ((c' y₀ : ℝ) + 1) * (τ x₀).toReal < (c' x₀ : ℝ) * (τ y₀).toReal := by
              have hcx_ge : (c x₀ : ℝ) + 1 ≤ (c' x₀ : ℝ) := by exact_mod_cast hx₀
              have hcy_le : (c' y₀ : ℝ) + 1 ≤ (c y₀ : ℝ) := by exact_mod_cast hy₀
              rw [hc_eq x₀] at hcx_ge
              rw [hc_eq y₀] at hcy_le
              have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
              have hmul1 : ((c' y₀ : ℝ) + 1) * ((n : ℝ) * (τ x₀).toReal) <
                  (c' x₀ : ℝ) * ((n : ℝ) * (τ y₀).toReal) := by
                have hcy_pos : (0 : ℝ) < (c' y₀ : ℝ) + 1 := by positivity
                have h1 : ((c' y₀ : ℝ) + 1) * ((n : ℝ) * (τ x₀).toReal) <
                    ((c' y₀ : ℝ) + 1) * (c' x₀ : ℝ) :=
                  mul_lt_mul_of_pos_left (by linarith) hcy_pos
                have h2 : ((c' y₀ : ℝ) + 1) * (c' x₀ : ℝ) ≤
                    ((n : ℝ) * (τ y₀).toReal) * (c' x₀ : ℝ) :=
                  mul_le_mul_of_nonneg_right hcy_le (Nat.cast_nonneg _)
                linarith
              have hmul2 : (n : ℝ) * (((c' y₀ : ℝ) + 1) * (τ x₀).toReal) <
                  (n : ℝ) * ((c' x₀ : ℝ) * (τ y₀).toReal) := by
                linarith
              exact (mul_lt_mul_iff_right₀ hn_pos).mp hmul2
            have hP_pos : 0 < P τ_star := by
              have hfac_pos :
                  0 < ((c' x₀).factorial : ℝ) * ((c' y₀).factorial : ℝ) * F_rest := by
                rw [hfac_x₀]
                have hcx0 : (0 : ℝ) < (c' x₀ : ℝ) := Nat.cast_pos.mpr (by omega)
                positivity
              have hrhs_pos : 0 < (n.factorial : ℝ) *
                  ((τ x₀).toReal ^ c' x₀ * (τ y₀).toReal ^ c' y₀ * G_rest) := by
                refine mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) ?_
                exact mul_pos (mul_pos (pow_pos hτx₀_pos _) (pow_pos hτy₀_pos _)) hG_pos
              rw [← hF₀'] at hrhs_pos
              exact pos_of_mul_pos_left hrhs_pos hfac_pos.le
            have h2 :
                P τ_star * ((c' x₀ : ℝ) * (τ y₀).toReal) =
                  P τ₁ * (((c' y₀ : ℝ) + 1) * (τ x₀).toReal) := by
              have h1 :
                  P τ_star * (((c' x₀).factorial : ℝ) * ((c' y₀).factorial : ℝ) * F_rest) *
                      (τ y₀).toReal =
                    P τ₁ * (((c' x₀ - 1).factorial : ℝ) * ((c' y₀ + 1).factorial : ℝ) * F_rest) *
                      (τ x₀).toReal := by
                rw [hF₀', hF₁', hpow_x₀, hpow_y₀]
                ring
              rw [hfac_x₀, hfac_y₀] at h1
              apply mul_right_cancel₀ hF_pos.ne'
              linarith
            have hcy1 : (0 : ℝ) < (c' y₀ : ℝ) + 1 := by positivity
            have hprod_pos : 0 < ((c' y₀ : ℝ) + 1) * (τ x₀).toReal := mul_pos hcy1 hτx₀_pos
            have hmul_lt : P τ_star * (((c' y₀ : ℝ) + 1) * (τ x₀).toReal) <
                P τ_star * ((c' x₀ : ℝ) * (τ y₀).toReal) :=
              mul_lt_mul_of_pos_left hratio hP_pos
            rw [h2] at hmul_lt
            exact (mul_lt_mul_iff_left₀ hprod_pos).mp hmul_lt
        exact absurd hstrict (not_lt.mpr (hτ_star_max τ₁ hτ₁_mem))
  have hsum_all : ∑ τ' ∈ feasibleTypesFinset α n hn, P τ' = 1 := by
    dsimp only [P]
    rw [← Finset.sum_biUnion]
    · have huniv :
          (feasibleTypesFinset α n hn).biUnion (fun τ' ↦ typeClassFinset n hn τ') =
            Finset.univ := by
        ext A
        simp only [Finset.mem_biUnion, mem_feasibleTypesFinset, mem_typeClassFinset,
          Finset.mem_univ, iff_true]
        exact ⟨empDist hn A, ⟨A, rfl⟩, rfl⟩
      rw [huniv]
      exact sum_prod_toReal_eq_one n τ
    · intro τ₁ _ τ₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro A h₁ h₂
      exact hne ((mem_typeClassFinset.mp h₁).symm.trans (mem_typeClassFinset.mp h₂))
  have hbound : 1 ≤ ((feasibleTypesFinset α n hn).card : ℝ) * P τ := by
    calc
      (1 : ℝ) = ∑ τ' ∈ feasibleTypesFinset α n hn, P τ' := hsum_all.symm
      _ ≤ ∑ _τ' ∈ feasibleTypesFinset α n hn, P τ := Finset.sum_le_sum hP_max
      _ = ((feasibleTypesFinset α n hn).card : ℝ) * P τ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hPτ_eq : P τ = ((typeClassFinset n hn τ).card : ℝ) *
      q ^ (-(n : ℝ) * pmfEntropyBase q τ) := by
    have hconst : ∀ A ∈ typeClassFinset n hn τ,
        ∏ i : Fin n, (τ (A i)).toReal = q ^ (-(n : ℝ) * pmfEntropyBase q τ) := by
      intro A hA
      rw [prod_toReal_eq_rpow_of_mem_typeClass hq hA (Set.Subset.refl _)]
      congr 1
      unfold pmfEntropyBase
      simp_rw [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
      ring
    dsimp only [P]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard_le : ((feasibleTypesFinset α n hn).card : ℝ) ≤ (n + 1 : ℝ) ^ Fintype.card α := by
    exact_mod_cast card_feasibleTypesFinset_le α n hn
  have hP_nonneg : 0 ≤ P τ :=
    Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  have h1 : 1 ≤ (n + 1 : ℝ) ^ Fintype.card α *
      (((typeClassFinset n hn τ).card : ℝ) * q ^ (-(n : ℝ) * pmfEntropyBase q τ)) := by
    rw [← hPτ_eq]
    exact hbound.trans (mul_le_mul_of_nonneg_right hcard_le hP_nonneg)
  have hden_pos : 0 < (n + 1 : ℝ) ^ Fintype.card α := by positivity
  have hpow_pos : 0 < q ^ (-(n : ℝ) * pmfEntropyBase q τ) := Real.rpow_pos_of_pos hqpos _
  have h2 : (((n + 1 : ℝ) ^ Fintype.card α)⁻¹) * (q ^ (-(n : ℝ) * pmfEntropyBase q τ))⁻¹ ≤
      ((typeClassFinset n hn τ).card : ℝ) := by
    rw [← mul_inv, inv_le_iff_one_le_mul₀ (mul_pos hden_pos hpow_pos)]
    linarith
  rwa [← Real.rpow_neg hqpos.le, neg_mul, neg_neg] at h2

end CslibFrontier.Foundations.Data.Code
