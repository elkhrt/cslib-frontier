/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.MarkovOperators

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Guruswami–Sinop Colourful Markov Operator on `[k]²`

This module formalizes the explicit colourful symmetric Markov operator of Guruswami and Sinop on
`[k]²` (`Fin 2 → Fin k`) for `k ≥ 6`, establishing symmetry, nonnegativity, unit row sums,
colourfulness, rational denominator structure, and the spectral radius bound `4 / (k - 1)` on `1^⊥`
under standard Lean axioms via an explicit orthogonal decomposition into five invariant/coupled
subspaces.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.guruswamiSinopMatrix`: the Guruswami–Sinop Markov
  operator on
  `Fin 2 → Fin k`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.guruswamiSinop_markov_operator`: for `k ≥ 6`,
  `guruswamiSinopMatrix k` is a colourful symmetric Markov operator with spectral radius bound
  `4 / (k - 1)` on `1^⊥` and entries that are nonnegative integer multiples of
  `1 / ((k - 1)(k - 2)(k - 3))`.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Foundations.BooleanAnalysis

/-- The Guruswami–Sinop colourful symmetric Markov operator on `[k]²` (`Fin 2 → Fin k`) for `k ≥ 6`:
diagonal pairs `(x, x)` transition uniformly to disjoint off-diagonal pairs `(y₁, y₂)` with
weight `1 / ((k - 1)(k - 2))`, and off-diagonal pairs `(x₁, x₂)` transition to disjoint diagonal
pairs with weight `1 / ((k - 1)(k - 2))` and to disjoint off-diagonal pairs with weight
`1 / ((k - 1)(k - 3))`. -/
@[expose] noncomputable def guruswamiSinopMatrix (k : ℕ) :
    Matrix (Fin 2 → Fin k) (Fin 2 → Fin k) ℝ :=
  Matrix.of fun x y =>
    if ∀ i j : Fin 2, x i ≠ y j then
      if x 0 = x 1 then
        if y 0 = y 1 then 0 else 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))
      else
        if y 0 = y 1 then 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))
        else 1 / (((k : ℝ) - 1) * ((k : ℝ) - 3))
    else 0

/-! ### Private counting and orthogonal-decomposition helpers -/

private theorem card_erase_fin {k : ℕ} (c : Fin k) :
    (Finset.univ.erase c).card = k - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]

private theorem card_erase_erase_fin {k : ℕ} {c₁ c₂ : Fin k} (hne : c₁ ≠ c₂) :
    ((Finset.univ.erase c₁).erase c₂).card = k - 2 := by
  have hmem : c₂ ∈ Finset.univ.erase c₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ c₂⟩
  rw [Finset.card_erase_of_mem hmem, card_erase_fin c₁]
  omega

private theorem fin2_vec_eq {α : Type*} (x : Fin 2 → α) : ![x 0, x 1] = x := by
  ext i
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;> simp [hi]

private theorem fin2_diag_eq {α : Type*} {x : Fin 2 → α} (hx : x 0 = x 1) :
    x = ![x 0, x 0] := by
  ext i
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;> simp [hi, hx]

private theorem sum_fin2_split {k : ℕ} (f : (Fin 2 → Fin k) → ℝ) :
    ∑ x : Fin 2 → Fin k, f x =
      (∑ c : Fin k, f ![c, c]) +
        ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] := by
  classical
  let e : (Fin 2 → Fin k) ≃ Fin k × Fin k :=
    { toFun := fun x => (x 0, x 1)
      invFun := fun p => ![p.1, p.2]
      left_inv := fun x => fin2_vec_eq x
      right_inv := fun p => by simp }
  rw [Fintype.sum_equiv e _ (fun p => f ![p.1, p.2]) (fun x => by
    change f x = f ![x 0, x 1]; rw [fin2_vec_eq]), Fintype.sum_prod_type]
  have hsplit : ∀ c₁ : Fin k,
      ∑ c₂ : Fin k, f ![c₁, c₂] = f ![c₁, c₁] + ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] :=
    fun c₁ => (Finset.add_sum_erase Finset.univ (fun c₂ => f ![c₁, c₂]) (Finset.mem_univ c₁)).symm
  simp only [hsplit, Finset.sum_add_distrib]

private theorem sum_erase_swap {k : ℕ} (g : Fin k → Fin k → ℝ) :
    ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, g c₂ c₁ =
      ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, g c₁ c₂ := by
  classical
  have h1 : ∀ h : Fin k → Fin k → ℝ,
      ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, h c₁ c₂ =
        ∑ c₁ : Fin k, ∑ c₂ : Fin k, if c₁ ≠ c₂ then h c₁ c₂ else 0 := fun h =>
    Finset.sum_congr rfl fun c₁ _ => by
      rw [← Finset.sum_filter]
      congr 1; ext d; simp [ne_comm]
  rw [h1, h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
  by_cases h : c₁ = c₂ <;> simp [h, Ne.symm]

private theorem sum_sq_add_of_dot_zero {k : ℕ} (f g : (Fin 2 → Fin k) → ℝ)
    (hfg : ∑ x, f x * g x = 0) :
    ∑ x, (f x + g x) ^ 2 = (∑ x, f x ^ 2) + ∑ x, g x ^ 2 := by
  have h : ∀ x, (f x + g x) ^ 2 = f x ^ 2 + 2 * (f x * g x) + g x ^ 2 := fun x => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hfg, mul_zero, add_zero]

private theorem gs_entry_diag_diag {k : ℕ} (c d : Fin k) :
    guruswamiSinopMatrix k ![c, c] ![d, d] = 0 := by
  classical
  simp only [guruswamiSinopMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ↓reduceIte, ite_self]

private theorem gs_entry_diag_off {k : ℕ} {c c₁ c₂ : Fin k} (h12 : c₁ ≠ c₂) :
    guruswamiSinopMatrix k ![c, c] ![c₁, c₂] =
      if c₁ ≠ c ∧ c₂ ≠ c then 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2)) else 0 := by
  classical
  simp only [guruswamiSinopMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ↓reduceIte, h12]
  have hiff : (∀ i j : Fin 2, (![c, c] : Fin 2 → Fin k) i ≠ ![c₁, c₂] j) ↔ c₁ ≠ c ∧ c₂ ≠ c := by
    constructor
    · intro h; exact ⟨(h 0 0).symm, (h 0 1).symm⟩
    · intro ⟨h1, h2⟩ i j
      rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;>
        rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;>
        simp [hi, hj, h1.symm, h2.symm]
  exact if_congr hiff rfl rfl

private theorem gs_entry_off_diag {k : ℕ} {c₁ c₂ c : Fin k} (h12 : c₁ ≠ c₂) :
    guruswamiSinopMatrix k ![c₁, c₂] ![c, c] =
      if c ≠ c₁ ∧ c ≠ c₂ then 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2)) else 0 := by
  classical
  simp only [guruswamiSinopMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ↓reduceIte, h12]
  have hiff : (∀ i j : Fin 2, (![c₁, c₂] : Fin 2 → Fin k) i ≠ ![c, c] j) ↔ c ≠ c₁ ∧ c ≠ c₂ := by
    constructor
    · intro h; exact ⟨(h 0 0).symm, (h 1 0).symm⟩
    · intro ⟨h1, h2⟩ i j
      rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;>
        rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;>
        simp [hi, hj, h1.symm, h2.symm]
  exact if_congr hiff rfl rfl

private theorem gs_entry_off_off {k : ℕ} {c₁ c₂ x₁ x₂ : Fin k} (h12 : c₁ ≠ c₂) (hx : x₁ ≠ x₂) :
    guruswamiSinopMatrix k ![c₁, c₂] ![x₁, x₂] =
      if (x₁ ≠ c₁ ∧ x₁ ≠ c₂) ∧ (x₂ ≠ c₁ ∧ x₂ ≠ c₂) then
        1 / (((k : ℝ) - 1) * ((k : ℝ) - 3)) else 0 := by
  classical
  simp only [guruswamiSinopMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ↓reduceIte, h12, hx]
  have hiff : (∀ i j : Fin 2, (![c₁, c₂] : Fin 2 → Fin k) i ≠ ![x₁, x₂] j) ↔
      (x₁ ≠ c₁ ∧ x₁ ≠ c₂) ∧ (x₂ ≠ c₁ ∧ x₂ ≠ c₂) := by
    constructor
    · intro h; exact ⟨⟨(h 0 0).symm, (h 1 0).symm⟩, ⟨(h 0 1).symm, (h 1 1).symm⟩⟩
    · intro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ i j
      rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi <;>
        rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;>
        simp [hi, hj, h1.symm, h2.symm, h3.symm, h4.symm]
  exact if_congr hiff rfl rfl

private theorem gs_mulVec_diag {k : ℕ} (f : (Fin 2 → Fin k) → ℝ) (c : Fin k) :
    (guruswamiSinopMatrix k).mulVec f ![c, c] =
      (1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))) *
        ((∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) -
          ∑ d ∈ Finset.univ.erase c, (f ![c, d] + f ![d, c])) := by
  classical
  set a : ℝ := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_fin2_split]
  have h0 : ∑ d : Fin k, guruswamiSinopMatrix k ![c, c] ![d, d] * f ![d, d] = 0 :=
    Finset.sum_eq_zero fun d _ => by rw [gs_entry_diag_diag, zero_mul]
  rw [h0, zero_add]
  have h1 : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁,
      guruswamiSinopMatrix k ![c, c] ![c₁, c₂] * f ![c₁, c₂] =
      if c₁ = c then 0 else a * ((∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) - f ![c₁, c]) := by
    intro c₁
    by_cases hc₁ : c₁ = c
    · subst hc₁
      simp only [↓reduceIte]
      refine Finset.sum_eq_zero fun c₂ hc₂ => ?_
      rw [gs_entry_diag_off (Finset.mem_erase.mp hc₂).1.symm]
      simp
    · simp only [hc₁, ↓reduceIte]
      have hterm : ∀ c₂ ∈ Finset.univ.erase c₁,
          guruswamiSinopMatrix k ![c, c] ![c₁, c₂] * f ![c₁, c₂] =
            if c₂ ≠ c then a * f ![c₁, c₂] else 0 := fun c₂ hc₂ => by
        rw [gs_entry_diag_off (Finset.mem_erase.mp hc₂).1.symm]
        by_cases h2 : c₂ = c <;> simp [hc₁, h2, a]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
        show (Finset.univ.erase c₁).filter (fun c₂ => c₂ ≠ c) =
          (Finset.univ.erase c₁).erase c by ext z; simp [and_comm],
        ← Finset.mul_sum]
      have hsub := Finset.add_sum_erase (Finset.univ.erase c₁) (fun c₂ => f ![c₁, c₂])
        (Finset.mem_erase.mpr ⟨Ne.symm hc₁, Finset.mem_univ c⟩)
      congr 1; linarith
  rw [Finset.sum_congr rfl fun c₁ _ => h1 c₁]
  have hfilt : ∑ c₁ : Fin k, (if c₁ = c then 0 else
      a * ((∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) - f ![c₁, c])) =
      ∑ c₁ ∈ Finset.univ.erase c,
        a * ((∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) - f ![c₁, c]) := by
    have hrewrite : ∀ c₁ : Fin k,
        (if c₁ = c then 0 else a * ((∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) - f ![c₁, c])) =
        if c₁ ≠ c then a * ((∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) - f ![c₁, c]) else 0 :=
      fun c₁ => by by_cases h : c₁ = c <;> simp [h]
    rw [Finset.sum_congr rfl fun c₁ _ => hrewrite c₁, ← Finset.sum_filter]
    congr 1; ext z; simp
  rw [hfilt, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hfirst := Finset.add_sum_erase Finset.univ
    (fun c₁ => ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) (Finset.mem_univ c)
  congr 1; linarith

private theorem gs_mulVec_off {k : ℕ} (f : (Fin 2 → Fin k) → ℝ) {c₁ c₂ : Fin k} (hne : c₁ ≠ c₂) :
    (guruswamiSinopMatrix k).mulVec f ![c₁, c₂] =
      (1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))) *
        ((∑ c : Fin k, f ![c, c]) - f ![c₁, c₁] - f ![c₂, c₂]) +
      (1 / (((k : ℝ) - 1) * ((k : ℝ) - 3))) *
        ((∑ x₁ : Fin k, ∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂]) -
          (∑ d ∈ Finset.univ.erase c₁, (f ![c₁, d] + f ![d, c₁])) -
          (∑ d ∈ Finset.univ.erase c₂, (f ![c₂, d] + f ![d, c₂])) +
          (f ![c₁, c₂] + f ![c₂, c₁])) := by
  classical
  set a : ℝ := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))
  set b : ℝ := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 3))
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_fin2_split]
  have hd : ∑ c : Fin k, guruswamiSinopMatrix k ![c₁, c₂] ![c, c] * f ![c, c] =
      a * ((∑ c : Fin k, f ![c, c]) - f ![c₁, c₁] - f ![c₂, c₂]) := by
    have hterm : ∀ c : Fin k, guruswamiSinopMatrix k ![c₁, c₂] ![c, c] * f ![c, c] =
        if c ≠ c₁ ∧ c ≠ c₂ then a * f ![c, c] else 0 := fun c => by
      rw [gs_entry_off_diag hne]
      by_cases h : c ≠ c₁ ∧ c ≠ c₂ <;> simp [h, a]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_filter,
      show Finset.univ.filter (fun c : Fin k => c ≠ c₁ ∧ c ≠ c₂) =
        (Finset.univ.erase c₁).erase c₂ by ext c; simp [and_comm],
      ← Finset.mul_sum]
    have h1 := Finset.add_sum_erase Finset.univ (fun c => f ![c, c]) (Finset.mem_univ c₁)
    have h2 := Finset.add_sum_erase (Finset.univ.erase c₁) (fun c => f ![c, c])
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ c₂⟩)
    congr 1; linarith
  have ho : ∑ x₁ : Fin k, ∑ x₂ ∈ Finset.univ.erase x₁,
      guruswamiSinopMatrix k ![c₁, c₂] ![x₁, x₂] * f ![x₁, x₂] =
      b * ((∑ x₁ : Fin k, ∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂]) -
        (∑ d ∈ Finset.univ.erase c₁, (f ![c₁, d] + f ![d, c₁])) -
        (∑ d ∈ Finset.univ.erase c₂, (f ![c₂, d] + f ![d, c₂])) +
        (f ![c₁, c₂] + f ![c₂, c₁])) := by
    have hstep : ∀ x₁ : Fin k, ∑ x₂ ∈ Finset.univ.erase x₁,
        guruswamiSinopMatrix k ![c₁, c₂] ![x₁, x₂] * f ![x₁, x₂] =
          if x₁ ≠ c₁ ∧ x₁ ≠ c₂ then
            b * ((∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂]) - f ![x₁, c₁] - f ![x₁, c₂])
          else 0 := by
      intro x₁
      split_ifs with hx₁
      · have hterm : ∀ x₂ ∈ Finset.univ.erase x₁,
            guruswamiSinopMatrix k ![c₁, c₂] ![x₁, x₂] * f ![x₁, x₂] =
              if x₂ ≠ c₁ ∧ x₂ ≠ c₂ then b * f ![x₁, x₂] else 0 := fun x₂ hx₂ => by
          rw [gs_entry_off_off hne (Finset.mem_erase.mp hx₂).1.symm]
          by_cases h2 : x₂ ≠ c₁ ∧ x₂ ≠ c₂ <;> simp [hx₁, h2, b]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
          show (Finset.univ.erase x₁).filter (fun x₂ => x₂ ≠ c₁ ∧ x₂ ≠ c₂) =
            ((Finset.univ.erase x₁).erase c₁).erase c₂ by
              ext z; simp [and_comm, and_left_comm, and_assoc],
          ← Finset.mul_sum]
        have h1 := Finset.add_sum_erase (Finset.univ.erase x₁) (fun x₂ => f ![x₁, x₂])
          (Finset.mem_erase.mpr ⟨hx₁.1.symm, Finset.mem_univ c₁⟩)
        have h2 := Finset.add_sum_erase ((Finset.univ.erase x₁).erase c₁)
          (fun x₂ => f ![x₁, x₂])
          (Finset.mem_erase.mpr ⟨hne.symm,
            Finset.mem_erase.mpr ⟨hx₁.2.symm, Finset.mem_univ c₂⟩⟩)
        congr 1; linarith
      · refine Finset.sum_eq_zero fun x₂ hx₂ => ?_
        rw [gs_entry_off_off hne (Finset.mem_erase.mp hx₂).1.symm]
        have hfalse : ¬((x₁ ≠ c₁ ∧ x₁ ≠ c₂) ∧ (x₂ ≠ c₁ ∧ x₂ ≠ c₂)) := fun h => hx₁ h.1
        simp only [hfalse, ↓reduceIte, zero_mul]
    rw [Finset.sum_congr rfl fun x₁ _ => hstep x₁, ← Finset.sum_filter,
      show Finset.univ.filter (fun x₁ : Fin k => x₁ ≠ c₁ ∧ x₁ ≠ c₂) =
        (Finset.univ.erase c₁).erase c₂ by ext z; simp [and_comm],
      ← Finset.mul_sum]
    congr 1
    have hA := Finset.add_sum_erase Finset.univ
      (fun x₁ => ∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂]) (Finset.mem_univ c₁)
    have hB := Finset.add_sum_erase (Finset.univ.erase c₁)
      (fun x₁ => ∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂])
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ c₂⟩)
    have hC := Finset.add_sum_erase (Finset.univ.erase c₁)
      (fun x₁ => f ![x₁, c₁]) (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ c₂⟩)
    have hD := Finset.add_sum_erase (Finset.univ.erase c₂)
      (fun x₁ => f ![x₁, c₂]) (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ c₁⟩)
    have hE : (∑ x₁ ∈ (Finset.univ.erase c₁).erase c₂,
        ((∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂]) - f ![x₁, c₁] - f ![x₁, c₂])) =
        (∑ x₁ ∈ (Finset.univ.erase c₁).erase c₂, ∑ x₂ ∈ Finset.univ.erase x₁, f ![x₁, x₂]) -
          (∑ x₁ ∈ (Finset.univ.erase c₁).erase c₂, f ![x₁, c₁]) -
          (∑ x₁ ∈ (Finset.univ.erase c₁).erase c₂, f ![x₁, c₂]) := by
      simp [Finset.sum_sub_distrib]
    have hswap_e : (Finset.univ.erase c₁).erase c₂ = (Finset.univ.erase c₂).erase c₁ := by
      ext z; simp [and_comm]
    rw [hE]
    rw [← hswap_e] at hD
    simp only [Finset.sum_add_distrib]
    linarith
  rw [hd, ho]

private def gsE0 (k : ℕ) (x : Fin 2 → Fin k) : ℝ :=
  if x 0 = x 1 then (k : ℝ) - 1 else -1

private def gsDfun {k : ℕ} (u : Fin k → ℝ) (x : Fin 2 → Fin k) : ℝ :=
  if x 0 = x 1 then u (x 0) else 0

private def gsRfun {k : ℕ} (u : Fin k → ℝ) (x : Fin 2 → Fin k) : ℝ :=
  if x 0 = x 1 then 0 else u (x 0) + u (x 1)

private theorem gsE0_diag {k : ℕ} (c : Fin k) : gsE0 k ![c, c] = (k : ℝ) - 1 := by
  simp [gsE0]

private theorem gsE0_off {k : ℕ} {c₁ c₂ : Fin k} (h : c₁ ≠ c₂) : gsE0 k ![c₁, c₂] = -1 := by
  simp [gsE0, h]

private theorem gsDfun_diag {k : ℕ} (u : Fin k → ℝ) (c : Fin k) : gsDfun u ![c, c] = u c := by
  simp [gsDfun]

private theorem gsDfun_off {k : ℕ} (u : Fin k → ℝ) {c₁ c₂ : Fin k} (h : c₁ ≠ c₂) :
    gsDfun u ![c₁, c₂] = 0 := by
  simp [gsDfun, h]

private theorem gsRfun_diag {k : ℕ} (u : Fin k → ℝ) (c : Fin k) : gsRfun u ![c, c] = 0 := by
  simp [gsRfun]

private theorem gsRfun_off {k : ℕ} (u : Fin k → ℝ) {c₁ c₂ : Fin k} (h : c₁ ≠ c₂) :
    gsRfun u ![c₁, c₂] = u c₁ + u c₂ := by
  simp [gsRfun, h]

private theorem gs_row_sum {k : ℕ} (hk : 6 ≤ k) (x : Fin 2 → Fin k) :
    ∑ y : Fin 2 → Fin k, guruswamiSinopMatrix k x y = 1 := by
  classical
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hkm3 : (0 : ℝ) < (k : ℝ) - 3 := by linarith
  have h1 : (guruswamiSinopMatrix k).mulVec (fun _ => 1) x =
      ∑ y : Fin 2 → Fin k, guruswamiSinopMatrix k x y := by
    simp [Matrix.mulVec, dotProduct]
  rw [← h1]
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, gs_mulVec_diag]
    have hcard_off : ∑ c₁ : Fin k, ∑ _c₂ ∈ Finset.univ.erase c₁, (1 : ℝ) =
        (k : ℝ) * ((k : ℝ) - 1) := by
      simp only [Finset.sum_const, card_erase_fin, nsmul_eq_mul, mul_one,
        Finset.card_univ, Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hcard_row : ∑ _d ∈ Finset.univ.erase (x 0), ((1 : ℝ) + 1) =
        2 * ((k : ℝ) - 1) := by
      simp only [Finset.sum_const, card_erase_fin, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      ring
    rw [hcard_off, hcard_row]
    field_simp [hkm1.ne', hkm2.ne']
  · rw [← fin2_vec_eq x, gs_mulVec_off _ hx]
    have hcard_d : ∑ _c : Fin k, (1 : ℝ) = (k : ℝ) := by simp
    have hcard_off : ∑ c₁ : Fin k, ∑ _c₂ ∈ Finset.univ.erase c₁, (1 : ℝ) =
        (k : ℝ) * ((k : ℝ) - 1) := by
      simp only [Finset.sum_const, card_erase_fin, nsmul_eq_mul, mul_one,
        Finset.card_univ, Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hcard_row : ∀ c : Fin k, ∑ _d ∈ Finset.univ.erase c, ((1 : ℝ) + 1) =
        2 * ((k : ℝ) - 1) := fun c => by
      simp only [Finset.sum_const, card_erase_fin, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      ring
    rw [hcard_d, hcard_off, hcard_row, hcard_row]
    field_simp [hkm1.ne', hkm2.ne', hkm3.ne']
    ring

private theorem gs_mulVec_e0 {k : ℕ} (hk : 6 ≤ k) :
    (guruswamiSinopMatrix k).mulVec (gsE0 k) = fun x => (-1 / ((k : ℝ) - 1)) * gsE0 k x := by
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hkm3 : (0 : ℝ) < (k : ℝ) - 3 := by linarith
  have hdiag : ∑ c : Fin k, gsE0 k ![c, c] = (k : ℝ) * ((k : ℝ) - 1) := by
    simp [gsE0_diag]; ring
  have hoff : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsE0 k ![c₁, c₂] =
      -((k : ℝ) * ((k : ℝ) - 1)) := by
    have h1 : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsE0 k ![c₁, c₂] =
        -((k : ℝ) - 1) := fun c₁ => by
      rw [Finset.sum_congr rfl fun c₂ hc₂ => gsE0_off (Finset.mem_erase.mp hc₂).1.symm]
      simp [Nat.cast_sub (by omega : 1 ≤ k)]
    simp [h1]; ring
  have hrow : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, (gsE0 k ![c, d] + gsE0 k ![d, c]) =
      -2 * ((k : ℝ) - 1) := fun c => by
    have h1 : ∀ d ∈ Finset.univ.erase c, gsE0 k ![c, d] + gsE0 k ![d, c] = -2 := fun d hd => by
      have hne := (Finset.mem_erase.mp hd).1
      rw [gsE0_off hne.symm, gsE0_off hne]; ring
    rw [Finset.sum_congr rfl h1]
    simp only [Finset.sum_const, card_erase_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  ext x
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, gs_mulVec_diag, hoff, hrow, gsE0_diag]
    field_simp [hkm1.ne', hkm2.ne']
    ring
  · rw [← fin2_vec_eq x, gs_mulVec_off _ hx, hdiag, hoff, hrow, hrow,
      gsE0_diag, gsE0_diag, gsE0_off hx, gsE0_off (Ne.symm hx)]
    field_simp [hkm1.ne', hkm2.ne', hkm3.ne']
    ring

private theorem gs_mulVec_D {k : ℕ} (u : Fin k → ℝ) (hu : ∑ c, u c = 0) :
    (guruswamiSinopMatrix k).mulVec (gsDfun u) =
      fun x => -(1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))) * gsRfun u x := by
  ext x
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, gs_mulVec_diag, gsRfun_diag]
    have h1 : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsDfun u ![c₁, c₂] = 0 :=
      Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun c₂ hc₂ =>
        gsDfun_off u (Finset.mem_erase.mp hc₂).1.symm
    have h2 : ∑ d ∈ Finset.univ.erase (x 0), (gsDfun u ![x 0, d] + gsDfun u ![d, x 0]) = 0 :=
      Finset.sum_eq_zero fun d hd => by
        have hne := (Finset.mem_erase.mp hd).1
        rw [gsDfun_off u hne.symm, gsDfun_off u hne, add_zero]
    rw [h1, h2]; ring
  · rw [← fin2_vec_eq x, gs_mulVec_off _ hx, gsRfun_off u hx]
    have hd : ∑ c : Fin k, gsDfun u ![c, c] = 0 := by simp [gsDfun_diag, hu]
    have h1 : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsDfun u ![c₁, c₂] = 0 :=
      Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun c₂ hc₂ =>
        gsDfun_off u (Finset.mem_erase.mp hc₂).1.symm
    have h2 : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, (gsDfun u ![c, d] + gsDfun u ![d, c]) = 0 :=
      fun c => Finset.sum_eq_zero fun d hd => by
        have hne := (Finset.mem_erase.mp hd).1
        rw [gsDfun_off u hne.symm, gsDfun_off u hne, add_zero]
    rw [hd, h1, h2, h2, gsDfun_diag, gsDfun_diag, gsDfun_off u hx, gsDfun_off u (Ne.symm hx)]
    ring

private theorem gs_mulVec_R {k : ℕ} (hk : 6 ≤ k) (u : Fin k → ℝ) (hu : ∑ c, u c = 0) :
    (guruswamiSinopMatrix k).mulVec (gsRfun u) =
      fun x => -(2 / ((k : ℝ) - 1)) * gsDfun u x - (2 / ((k : ℝ) - 1)) * gsRfun u x := by
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hkm3 : (0 : ℝ) < (k : ℝ) - 3 := by linarith
  have htot : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] = 0 := by
    have h1 : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] =
        ((k : ℝ) - 2) * u c₁ := fun c₁ => by
      rw [Finset.sum_congr rfl fun c₂ hc₂ => gsRfun_off u (Finset.mem_erase.mp hc₂).1.symm,
        Finset.sum_add_distrib, Finset.sum_const, card_erase_fin, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
        show ∑ c₂ ∈ Finset.univ.erase c₁, u c₂ = -u c₁ by
          have := Finset.add_sum_erase Finset.univ u (Finset.mem_univ c₁); linarith]
      ring
    simp [h1, ← Finset.mul_sum, hu]
  have hrow : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, (gsRfun u ![c, d] + gsRfun u ![d, c]) =
      2 * ((k : ℝ) - 2) * u c := fun c => by
    have h1 : ∀ d ∈ Finset.univ.erase c, gsRfun u ![c, d] + gsRfun u ![d, c] = 2 * (u c + u d) :=
      fun d hd => by
        have hne := (Finset.mem_erase.mp hd).1
        rw [gsRfun_off u hne.symm, gsRfun_off u hne]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      card_erase_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
      show ∑ d ∈ Finset.univ.erase c, u d = -u c by
        have := Finset.add_sum_erase Finset.univ u (Finset.mem_univ c); linarith]
    ring
  ext x
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, gs_mulVec_diag, htot, hrow, gsDfun_diag, gsRfun_diag]
    field_simp [hkm1.ne', hkm2.ne']
    ring
  · rw [← fin2_vec_eq x, gs_mulVec_off _ hx, htot, hrow, hrow,
      show ∑ c : Fin k, gsRfun u ![c, c] = 0 by simp [gsRfun_diag],
      gsRfun_diag, gsRfun_diag, gsDfun_off u hx, gsRfun_off u hx, gsRfun_off u (Ne.symm hx)]
    field_simp [hkm1.ne', hkm3.ne']
    ring

private theorem gs_mulVec_sym {k : ℕ} {f : (Fin 2 → Fin k) → ℝ}
    (hdiag : ∀ c : Fin k, f ![c, c] = 0)
    (hsym : ∀ c₁ c₂ : Fin k, f ![c₁, c₂] = f ![c₂, c₁])
    (hrow : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, f ![c, d] = 0) :
    (guruswamiSinopMatrix k).mulVec f =
      fun x => (2 * (1 / (((k : ℝ) - 1) * ((k : ℝ) - 3)))) * f x := by
  have htot : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] = 0 := by simp [hrow]
  have hrow2 : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, (f ![c, d] + f ![d, c]) = 0 := fun c => by
    have h1 : ∀ d ∈ Finset.univ.erase c, f ![c, d] + f ![d, c] = 2 * f ![c, d] :=
      fun d _ => by rw [hsym d c]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hrow, mul_zero]
  ext x
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, gs_mulVec_diag, htot, hrow2, hdiag]
    ring
  · rw [← fin2_vec_eq x, gs_mulVec_off _ hx, htot, hrow2, hrow2,
      show ∑ c : Fin k, f ![c, c] = 0 by simp [hdiag],
      hdiag, hdiag, hsym (x 1) (x 0)]
    ring

private theorem gs_mulVec_anti {k : ℕ} {f : (Fin 2 → Fin k) → ℝ}
    (hdiag : ∀ c : Fin k, f ![c, c] = 0)
    (hanti : ∀ c₁ c₂ : Fin k, f ![c₁, c₂] + f ![c₂, c₁] = 0) :
    (guruswamiSinopMatrix k).mulVec f = fun _ => 0 := by
  have htot : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] = 0 := by
    have hsum0 : (∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) +
        (∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₂, c₁]) = 0 := by
      simp only [← Finset.sum_add_distrib, hanti, Finset.sum_const_zero]
    rw [sum_erase_swap (fun c₁ c₂ => f ![c₁, c₂])] at hsum0
    linarith
  have hrow0 : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, (f ![c, d] + f ![d, c]) = 0 :=
    fun c => Finset.sum_eq_zero fun d _ => hanti c d
  ext x
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, gs_mulVec_diag, htot, hrow0]; ring
  · rw [← fin2_vec_eq x, gs_mulVec_off _ hx, htot, hrow0, hrow0,
      show ∑ c : Fin k, f ![c, c] = 0 by simp [hdiag],
      hdiag, hdiag, hanti (x 0) (x 1)]
    ring

private theorem gs_orth_e0 {k : ℕ} (f : (Fin 2 → Fin k) → ℝ)
    (h1 : ∑ c : Fin k, f ![c, c] = 0)
    (h2 : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] = 0) :
    ∑ x, gsE0 k x * f x = 0 := by
  rw [sum_fin2_split]
  have hd : ∑ c : Fin k, gsE0 k ![c, c] * f ![c, c] = ((k : ℝ) - 1) * ∑ c : Fin k, f ![c, c] := by
    simp [gsE0_diag, Finset.mul_sum]
  have ho : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsE0 k ![c₁, c₂] * f ![c₁, c₂] =
      - ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c₁ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c₂ hc₂ => ?_
    rw [gsE0_off (Finset.mem_erase.mp hc₂).1.symm]; ring
  rw [hd, ho, h1, h2]; ring

private theorem gs_orth_DR {k : ℕ} (u w : Fin k → ℝ) :
    ∑ x, gsDfun u x * gsRfun w x = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x 0 = x 1 <;> simp [gsDfun, gsRfun, hx]

private theorem gs_orth_DvSym {k : ℕ} (u : Fin k → ℝ) {f : (Fin 2 → Fin k) → ℝ}
    (hdiag : ∀ c, f ![c, c] = 0) :
    ∑ x, gsDfun u x * f x = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x 0 = x 1
  · rw [fin2_diag_eq hx, hdiag, mul_zero]
  · simp [gsDfun, hx]

private theorem gs_orth_RvSym {k : ℕ} (u : Fin k → ℝ) {f : (Fin 2 → Fin k) → ℝ}
    (hsym : ∀ c₁ c₂, f ![c₁, c₂] = f ![c₂, c₁])
    (hrow : ∀ c, ∑ d ∈ Finset.univ.erase c, f ![c, d] = 0) :
    ∑ x, gsRfun u x * f x = 0 := by
  rw [sum_fin2_split]
  have hd : ∑ c : Fin k, gsRfun u ![c, c] * f ![c, c] = 0 := by simp [gsRfun_diag]
  rw [hd, zero_add]
  have ho : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] * f ![c₁, c₂] =
      ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, (u c₁ + u c₂) * f ![c₁, c₂] :=
    Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ hc₂ => by
      rw [gsRfun_off u (Finset.mem_erase.mp hc₂).1.symm]
  rw [ho]
  have hsplit : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, (u c₁ + u c₂) * f ![c₁, c₂] =
      u c₁ * (∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂]) +
        ∑ c₂ ∈ Finset.univ.erase c₁, u c₂ * f ![c₁, c₂] := fun c₁ => by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hsplit, hrow, mul_zero, zero_add]
  have hswap : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, u c₂ * f ![c₁, c₂] =
      ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, u c₁ * f ![c₁, c₂] := by
    rw [← sum_erase_swap (fun c₁ c₂ => u c₂ * f ![c₁, c₂])]
    refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
    rw [hsym c₂ c₁]
  rw [hswap]
  simp only [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]

private theorem gs_orth_sym_anti {k : ℕ} {f g : (Fin 2 → Fin k) → ℝ}
    (hf : ∀ c₁ c₂, f ![c₁, c₂] = f ![c₂, c₁])
    (hg_diag : ∀ c, g ![c, c] = 0)
    (hg_anti : ∀ c₁ c₂, g ![c₁, c₂] + g ![c₂, c₁] = 0) :
    ∑ x, f x * g x = 0 := by
  rw [sum_fin2_split]
  have hd : ∑ c : Fin k, f ![c, c] * g ![c, c] = 0 := by simp [hg_diag]
  rw [hd, zero_add]
  have hsum0 : (∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₁, c₂] * g ![c₁, c₂]) +
      (∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, f ![c₂, c₁] * g ![c₂, c₁]) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c₁ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c₂ _ => ?_
    rw [hf c₂ c₁]
    have hneg : g ![c₂, c₁] = -g ![c₁, c₂] := by linarith [hg_anti c₁ c₂]
    rw [hneg]; ring
  have hswap := sum_erase_swap (fun c₁ c₂ => f ![c₁, c₂] * g ![c₁, c₂])
  linarith

private theorem gs_norm_D {k : ℕ} (u : Fin k → ℝ) :
    ∑ x, gsDfun u x ^ 2 = ∑ c, u c ^ 2 := by
  rw [sum_fin2_split]
  have ho : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsDfun u ![c₁, c₂] ^ 2 = 0 :=
    Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun c₂ hc₂ => by
      rw [gsDfun_off u (Finset.mem_erase.mp hc₂).1.symm]; ring
  rw [ho, add_zero]
  simp only [gsDfun_diag]

private theorem gs_norm_R {k : ℕ} (hk : 6 ≤ k) (u : Fin k → ℝ) (hu : ∑ c, u c = 0) :
    ∑ x, gsRfun u x ^ 2 = 2 * ((k : ℝ) - 2) * ∑ c, u c ^ 2 := by
  rw [sum_fin2_split]
  have hd : ∑ c : Fin k, gsRfun u ![c, c] ^ 2 = 0 := by simp [gsRfun_diag]
  rw [hd, zero_add]
  have hterm : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] ^ 2 =
      ((k : ℝ) - 2) * u c₁ ^ 2 + (∑ c, u c ^ 2) + 2 * u c₁ * (-u c₁) := by
    intro c₁
    have h1 : ∀ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] ^ 2 =
        u c₁ ^ 2 + 2 * u c₁ * u c₂ + u c₂ ^ 2 := fun c₂ hc₂ => by
      rw [gsRfun_off u (Finset.mem_erase.mp hc₂).1.symm]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, card_erase_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k),
      ← Finset.mul_sum]
    have he1 := Finset.add_sum_erase Finset.univ u (Finset.mem_univ c₁)
    have he2 := Finset.add_sum_erase Finset.univ (fun c => u c ^ 2) (Finset.mem_univ c₁)
    have hsum_er : ∑ i ∈ Finset.univ.erase c₁, u i = -u c₁ := by linarith
    rw [hsum_er]
    simp only [Nat.cast_one]
    linarith
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum_neg : ∑ c₁ : Fin k, 2 * u c₁ * (-u c₁) = -2 * ∑ c, u c ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum_neg]
  ring

private theorem gs_R_sums {k : ℕ} (hk : 6 ≤ k) (u : Fin k → ℝ) (hu : ∑ c, u c = 0) :
    (∑ c, gsRfun u ![c, c] = 0) ∧
      (∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] = 0) := by
  refine ⟨by simp [gsRfun_diag], ?_⟩
  have h1 : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsRfun u ![c₁, c₂] =
      ((k : ℝ) - 2) * u c₁ := fun c₁ => by
    rw [Finset.sum_congr rfl fun c₂ hc₂ => gsRfun_off u (Finset.mem_erase.mp hc₂).1.symm,
      Finset.sum_add_distrib, Finset.sum_const, card_erase_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
      show ∑ c₂ ∈ Finset.univ.erase c₁, u c₂ = -u c₁ by
        have := Finset.add_sum_erase Finset.univ u (Finset.mem_univ c₁); linarith]
    ring
  simp [h1, ← Finset.mul_sum, hu]

private theorem gs_D_sums {k : ℕ} (u : Fin k → ℝ) (hu : ∑ c, u c = 0) :
    (∑ c, gsDfun u ![c, c] = 0) ∧
      (∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsDfun u ![c₁, c₂] = 0) :=
  ⟨by simpa [gsDfun_diag] using hu,
    Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun c₂ hc₂ =>
      gsDfun_off u (Finset.mem_erase.mp hc₂).1.symm⟩

private theorem gs_piece12_bound {k : ℕ} (hk : 6 ≤ k) {uD uR : Fin k → ℝ}
    (huD : ∑ c, uD c = 0) (huR : ∑ c, uR c = 0) :
    (∑ x, (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) ^ 2) +
      (∑ x, (-(1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))) * gsRfun uD x -
        (2 / ((k : ℝ) - 1)) * gsRfun uR x) ^ 2) ≤
    (4 / ((k : ℝ) - 1)) ^ 2 * ((∑ x, gsDfun uD x ^ 2) + (∑ x, gsRfun uR x ^ 2)) := by
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  set a : ℝ := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))
  have hcs : ∑ x, (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) ^ 2 ≤
      2 * a ^ 2 * (∑ x, gsRfun uD x ^ 2) +
        2 * (2 / ((k : ℝ) - 1)) ^ 2 * (∑ x, gsRfun uR x ^ 2) := by
    have hpt : ∀ x, (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) ^ 2 ≤
        2 * a ^ 2 * gsRfun uD x ^ 2 + 2 * (2 / ((k : ℝ) - 1)) ^ 2 * gsRfun uR x ^ 2 :=
      fun x => by nlinarith [sq_nonneg (-a * gsRfun uD x + (2 / ((k : ℝ) - 1)) * gsRfun uR x)]
    calc
      ∑ x, (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) ^ 2
          ≤ ∑ x, (2 * a ^ 2 * gsRfun uD x ^ 2 +
              2 * (2 / ((k : ℝ) - 1)) ^ 2 * gsRfun uR x ^ 2) :=
            Finset.sum_le_sum fun x _ => hpt x
      _ = 2 * a ^ 2 * (∑ x, gsRfun uD x ^ 2) +
            2 * (2 / ((k : ℝ) - 1)) ^ 2 * (∑ x, gsRfun uR x ^ 2) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hD_uR : ∑ x, (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) ^ 2 =
      (4 / ((k : ℝ) - 1) ^ 2) * (∑ c, uR c ^ 2) := by
    rw [show (fun x => (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) ^ 2) =
        fun x => (-(2 / ((k : ℝ) - 1))) ^ 2 * gsDfun uR x ^ 2 from funext fun x => mul_pow _ _ 2,
      ← Finset.mul_sum, gs_norm_D]
    congr 1
    rw [neg_sq, div_pow]
    norm_num
  have hR_uD_eq : 2 * a ^ 2 * (∑ x, gsRfun uD x ^ 2) =
      (4 / (((k : ℝ) - 2) * ((k : ℝ) - 1) ^ 2)) * (∑ c, uD c ^ 2) := by
    rw [gs_norm_R hk uD huD]
    dsimp only [a]; field_simp [hkm1.ne', hkm2.ne']; ring
  have hN_uD : 0 ≤ ∑ c, uD c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN_uR : 0 ≤ ∑ c, uR c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcoefD : 4 / (((k : ℝ) - 2) * ((k : ℝ) - 1) ^ 2) ≤ 16 / ((k : ℝ) - 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hcoefR : 4 / ((k : ℝ) - 1) ^ 2 +
      2 * (2 / ((k : ℝ) - 1)) ^ 2 * (2 * ((k : ℝ) - 2)) ≤
      16 / ((k : ℝ) - 1) ^ 2 * (2 * ((k : ℝ) - 2)) := by
    have h1 : 4 / ((k : ℝ) - 1) ^ 2 + 2 * (2 / ((k : ℝ) - 1)) ^ 2 * (2 * ((k : ℝ) - 2)) =
        (4 + 16 * ((k : ℝ) - 2)) / ((k : ℝ) - 1) ^ 2 := by field_simp [hkm1.ne']; ring
    have h2 : 16 / ((k : ℝ) - 1) ^ 2 * (2 * ((k : ℝ) - 2)) =
        (32 * ((k : ℝ) - 2)) / ((k : ℝ) - 1) ^ 2 := by field_simp [hkm1.ne']; ring
    rw [h1, h2]; exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have h16 : (4 / ((k : ℝ) - 1)) ^ 2 = 16 / ((k : ℝ) - 1) ^ 2 := by rw [div_pow]; norm_num
  rw [h16, gs_norm_D, gs_norm_R hk uR huR, hD_uR]
  rw [hR_uD_eq, gs_norm_R hk uR huR] at hcs
  have hm1 := mul_le_mul_of_nonneg_right hcoefD hN_uD
  have hm2 := mul_le_mul_of_nonneg_right hcoefR hN_uR
  linarith

private theorem gs_spectral_bound {k : ℕ} (hk : 6 ≤ k) :
    HasMarkovSpectralRadiusBound (guruswamiSinopMatrix k) (4 / ((k : ℝ) - 1)) := by
  intro v hv
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hkm3 : (0 : ℝ) < (k : ℝ) - 3 := by linarith
  set a : ℝ := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 2))
  set b : ℝ := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 3))
  let SD : ℝ := ∑ c : Fin k, v ![c, c]
  let α : ℝ := SD / ((k : ℝ) * ((k : ℝ) - 1))
  let v1 : (Fin 2 → Fin k) → ℝ := fun x => v x - α * gsE0 k x
  have hSD_v1 : ∑ c : Fin k, v1 ![c, c] = 0 := by
    simp only [v1, gsE0_diag, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp only [α, SD]
    field_simp [hk_pos.ne', hkm1.ne']
    ring
  have he0_sum : ∑ x : Fin 2 → Fin k, gsE0 k x = 0 := by
    rw [sum_fin2_split]
    have hd : ∑ c : Fin k, gsE0 k ![c, c] = (k : ℝ) * ((k : ℝ) - 1) := by
      simp [gsE0_diag]; ring
    have ho : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsE0 k ![c₁, c₂] =
        -((k : ℝ) * ((k : ℝ) - 1)) := by
      have h1 : ∀ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, gsE0 k ![c₁, c₂] =
          -((k : ℝ) - 1) := fun c₁ => by
        rw [Finset.sum_congr rfl fun c₂ hc₂ => gsE0_off (Finset.mem_erase.mp hc₂).1.symm]
        simp [Nat.cast_sub (by omega : 1 ≤ k)]
      simp [h1]; ring
    rw [hd, ho]; ring
  have hSO_v1 : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, v1 ![c₁, c₂] = 0 := by
    have hsum_v1 : ∑ x : Fin 2 → Fin k, v1 x = 0 := by
      simp only [v1, Finset.sum_sub_distrib, ← Finset.mul_sum, he0_sum, hv, mul_zero, sub_zero]
    linarith [sum_fin2_split v1]
  let uD : Fin k → ℝ := fun c => v1 ![c, c]
  let rVec : Fin k → ℝ := fun c => ∑ d ∈ Finset.univ.erase c, (v1 ![c, d] + v1 ![d, c])
  have hrVec_sum : ∑ c : Fin k, rVec c = 0 := by
    simp only [rVec, Finset.sum_add_distrib, sum_erase_swap (fun c d => v1 ![c, d]), hSO_v1,
      add_zero]
  let uR : Fin k → ℝ := fun c => rVec c / (2 * ((k : ℝ) - 2))
  have huR_sum : ∑ c : Fin k, uR c = 0 := by
    simp only [uR, ← Finset.sum_div, hrVec_sum, zero_div]
  let v2 : (Fin 2 → Fin k) → ℝ := fun x => v1 x - gsDfun uD x - gsRfun uR x
  let vSym : (Fin 2 → Fin k) → ℝ := fun x => (v2 ![x 0, x 1] + v2 ![x 1, x 0]) / 2
  let vAnti : (Fin 2 → Fin k) → ℝ := fun x => (v2 ![x 0, x 1] - v2 ![x 1, x 0]) / 2
  have hv2_diag : ∀ c : Fin k, v2 ![c, c] = 0 := fun c => by
    simp [v2, gsDfun_diag, gsRfun_diag, uD]
  have hv2_row : ∀ c : Fin k, ∑ d ∈ Finset.univ.erase c, (v2 ![c, d] + v2 ![d, c]) = 0 := by
    intro c
    have hR_sum : ∑ d ∈ Finset.univ.erase c, (gsRfun uR ![c, d] + gsRfun uR ![d, c]) = rVec c := by
      have hterm : ∀ d ∈ Finset.univ.erase c,
          gsRfun uR ![c, d] + gsRfun uR ![d, c] = 2 * (uR c + uR d) := fun d hd => by
        have hne := (Finset.mem_erase.mp hd).1
        rw [gsRfun_off uR hne.symm, gsRfun_off uR hne]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        card_erase_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
        show ∑ d ∈ Finset.univ.erase c, uR d = -uR c by
          have := Finset.add_sum_erase Finset.univ uR (Finset.mem_univ c); linarith]
      dsimp only [uR]
      field_simp [hkm2.ne']
      ring
    have h1 : ∀ d ∈ Finset.univ.erase c,
        v2 ![c, d] + v2 ![d, c] =
          (v1 ![c, d] + v1 ![d, c]) - (gsRfun uR ![c, d] + gsRfun uR ![d, c]) := fun d hd => by
      have hne := (Finset.mem_erase.mp hd).1
      dsimp only [v2]
      rw [gsDfun_off uD hne.symm, gsDfun_off uD hne]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hR_sum, sub_self]
  have hvSym_diag : ∀ c, vSym ![c, c] = 0 := fun c => by simp [vSym, hv2_diag c]
  have hvSym_sym : ∀ c₁ c₂, vSym ![c₁, c₂] = vSym ![c₂, c₁] := fun c₁ c₂ => by
    simp [vSym, add_comm]
  have hvSym_row : ∀ c, ∑ d ∈ Finset.univ.erase c, vSym ![c, d] = 0 := fun c => by
    simp only [vSym, Matrix.cons_val_zero, Matrix.cons_val_one, ← Finset.sum_div, hv2_row c,
      zero_div]
  have hvSym_tot : ∑ c₁ : Fin k, ∑ c₂ ∈ Finset.univ.erase c₁, vSym ![c₁, c₂] = 0 := by
    simp [hvSym_row]
  have hvAnti_diag : ∀ c, vAnti ![c, c] = 0 := fun c => by simp [vAnti]
  have hvAnti_swap : ∀ c₁ c₂, vAnti ![c₁, c₂] + vAnti ![c₂, c₁] = 0 := fun c₁ c₂ => by
    simp [vAnti]; ring
  have hv_eq : ∀ x, v x = α * gsE0 k x + gsDfun uD x + gsRfun uR x + vSym x + vAnti x := by
    intro x
    have hsa : vSym x + vAnti x = v2 x := by
      have : v2 ![x 0, x 1] = v2 x := by rw [fin2_vec_eq]
      dsimp only [vSym, vAnti]; linarith
    dsimp only [v2, v1] at hsa ⊢; linarith
  have hTv_eq : ∀ x, (guruswamiSinopMatrix k).mulVec v x =
      (-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
      (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) +
      (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) +
      (2 * b) * vSym x := by
    intro x
    have hfun : v = fun y =>
        α • gsE0 k y + (gsDfun uD y + (gsRfun uR y + (vSym y + vAnti y))) := by
      ext y; simp only [smul_eq_mul]; linarith [hv_eq y]
    have hlin : (guruswamiSinopMatrix k).mulVec v =
        α • (guruswamiSinopMatrix k).mulVec (gsE0 k) +
        ((guruswamiSinopMatrix k).mulVec (gsDfun uD) +
          ((guruswamiSinopMatrix k).mulVec (gsRfun uR) +
            ((guruswamiSinopMatrix k).mulVec vSym + (guruswamiSinopMatrix k).mulVec vAnti))) := by
      conv_lhs => rw [hfun]
      simp only [← Pi.add_def, ← Pi.smul_def, Matrix.mulVec_add, Matrix.mulVec_smul]
    have hx := congrFun hlin x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gs_mulVec_e0 hk, gs_mulVec_D uD hSD_v1,
      gs_mulVec_R hk uR huR_sum, gs_mulVec_sym hvSym_diag hvSym_sym hvSym_row,
      gs_mulVec_anti hvAnti_diag hvAnti_swap] at hx
    dsimp only [a, b]; linarith
  have hv_norm : ∑ x, v x ^ 2 =
      (∑ x, (α * gsE0 k x) ^ 2) + (∑ x, gsDfun uD x ^ 2) + (∑ x, gsRfun uR x ^ 2) +
        (∑ x, vSym x ^ 2) + (∑ x, vAnti x ^ 2) := by
    have h1 : ∑ x, v x ^ 2 =
        (∑ x, (α * gsE0 k x + gsDfun uD x + gsRfun uR x + vSym x) ^ 2) + ∑ x, vAnti x ^ 2 := by
      rw [show (fun x => v x ^ 2) = fun x =>
          ((α * gsE0 k x + gsDfun uD x + gsRfun uR x + vSym x) + vAnti x) ^ 2 from
          funext fun x => by rw [hv_eq x]]
      refine sum_sq_add_of_dot_zero _ _ (gs_orth_sym_anti ?_ hvAnti_diag hvAnti_swap)
      intro c₁ c₂
      by_cases h : c₁ = c₂
      · subst h; rfl
      · rw [gsE0_off h, gsE0_off (Ne.symm h), gsDfun_off uD h, gsDfun_off uD (Ne.symm h),
          gsRfun_off uR h, gsRfun_off uR (Ne.symm h), hvSym_sym c₁ c₂]; ring
    have h2 : ∑ x, (α * gsE0 k x + gsDfun uD x + gsRfun uR x + vSym x) ^ 2 =
        (∑ x, (α * gsE0 k x + gsDfun uD x + gsRfun uR x) ^ 2) + ∑ x, vSym x ^ 2 := by
      refine sum_sq_add_of_dot_zero _ _ ?_
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [gs_orth_e0 vSym (by simp [hvSym_diag]) hvSym_tot,
        gs_orth_DvSym uD hvSym_diag, gs_orth_RvSym uR hvSym_sym hvSym_row]; ring
    have h3 : ∑ x, (α * gsE0 k x + gsDfun uD x + gsRfun uR x) ^ 2 =
        (∑ x, (α * gsE0 k x + gsDfun uD x) ^ 2) + ∑ x, gsRfun uR x ^ 2 := by
      refine sum_sq_add_of_dot_zero _ _ ?_
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [gs_orth_e0 _ (gs_R_sums hk uR huR_sum).1 (gs_R_sums hk uR huR_sum).2,
        gs_orth_DR]; ring
    have h4 : ∑ x, (α * gsE0 k x + gsDfun uD x) ^ 2 =
        (∑ x, (α * gsE0 k x) ^ 2) + ∑ x, gsDfun uD x ^ 2 := by
      refine sum_sq_add_of_dot_zero _ _ ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [gs_orth_e0 _ (gs_D_sums uD hSD_v1).1 (gs_D_sums uD hSD_v1).2, mul_zero]
    linarith
  have hTv_norm : ∑ x, ((guruswamiSinopMatrix k).mulVec v x) ^ 2 =
      (∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x)) ^ 2) +
      (∑ x, (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) ^ 2) +
      (∑ x, (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) ^ 2) +
      (∑ x, ((2 * b) * vSym x) ^ 2) := by
    rw [show (fun x => ((guruswamiSinopMatrix k).mulVec v x) ^ 2) = fun x =>
        (((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) + (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) +
          (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x)) + (2 * b) * vSym x) ^ 2 from
        funext fun x => by rw [hTv_eq x]]
    have h1 : ∑ x, (((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
          (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) +
          (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x)) + (2 * b) * vSym x) ^ 2 =
        (∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) + (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) +
          (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x)) ^ 2) +
        ∑ x, ((2 * b) * vSym x) ^ 2 := by
      refine sum_sq_add_of_dot_zero _ _ ?_
      have hmul_c : ∀ f : (Fin 2 → Fin k) → ℝ,
          ∑ x, f x * ((2 * b) * vSym x) = (2 * b) * ∑ x, f x * vSym x := fun f => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      rw [hmul_c]
      have hzero : ∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
          (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) +
          (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x)) * vSym x = 0 := by
        simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          mul_assoc, ← Finset.mul_sum,
          gs_orth_e0 vSym (by simp [hvSym_diag]) hvSym_tot,
          gs_orth_DvSym uR hvSym_diag, gs_orth_RvSym uD hvSym_sym hvSym_row,
          gs_orth_RvSym uR hvSym_sym hvSym_row]
        ring
      rw [hzero, mul_zero]
    have h2 : ∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
          (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) +
          (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x)) ^ 2 =
        (∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
          (-(2 / ((k : ℝ) - 1)) * gsDfun uR x)) ^ 2) +
        ∑ x, (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) ^ 2 := by
      refine sum_sq_add_of_dot_zero _ _ ?_
      have hexp : ∀ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
            (-(2 / ((k : ℝ) - 1)) * gsDfun uR x)) *
            (-a * gsRfun uD x - (2 / ((k : ℝ) - 1)) * gsRfun uR x) =
            ((-1 / ((k : ℝ) - 1)) * α * (-a)) * (gsE0 k x * gsRfun uD x) +
            ((-1 / ((k : ℝ) - 1)) * α * (-(2 / ((k : ℝ) - 1)))) * (gsE0 k x * gsRfun uR x) +
            ((-(2 / ((k : ℝ) - 1))) * (-a)) * (gsDfun uR x * gsRfun uD x) +
            ((-(2 / ((k : ℝ) - 1))) * (-(2 / ((k : ℝ) - 1)))) * (gsDfun uR x * gsRfun uR x) :=
        fun x => by ring
      simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum,
        gs_orth_e0 _ (gs_R_sums hk uD hSD_v1).1 (gs_R_sums hk uD hSD_v1).2,
        gs_orth_e0 _ (gs_R_sums hk uR huR_sum).1 (gs_R_sums hk uR huR_sum).2, gs_orth_DR]
      ring
    have h3 : ∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x) +
          (-(2 / ((k : ℝ) - 1)) * gsDfun uR x)) ^ 2 =
        (∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x)) ^ 2) +
        ∑ x, (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) ^ 2 := by
      refine sum_sq_add_of_dot_zero _ _ ?_
      have hexp : ∀ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x)) *
          (-(2 / ((k : ℝ) - 1)) * gsDfun uR x) =
          ((-1 / ((k : ℝ) - 1)) * α * (-(2 / ((k : ℝ) - 1)))) * (gsE0 k x * gsDfun uR x) :=
        fun x => by ring
      simp only [hexp, ← Finset.mul_sum,
        gs_orth_e0 _ (gs_D_sums uR huR_sum).1 (gs_D_sums uR huR_sum).2, mul_zero]
    linarith
  have hpiece0 : ∑ x, ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x)) ^ 2 ≤
      (4 / ((k : ℝ) - 1)) ^ 2 * ∑ x, (α * gsE0 k x) ^ 2 := by
    rw [show (fun x => ((-1 / ((k : ℝ) - 1)) * (α * gsE0 k x)) ^ 2) =
        fun x => (-1 / ((k : ℝ) - 1)) ^ 2 * (α * gsE0 k x) ^ 2 from funext fun x => mul_pow _ _ 2,
      ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  have hpiece3 : ∑ x, ((2 * b) * vSym x) ^ 2 ≤ (4 / ((k : ℝ) - 1)) ^ 2 * ∑ x, vSym x ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h2b : 2 * b ≤ 4 / ((k : ℝ) - 1) := by
      dsimp only [b]
      rw [show 2 * (1 / (((k : ℝ) - 1) * ((k : ℝ) - 3))) =
          (2 / ((k : ℝ) - 3)) / ((k : ℝ) - 1) by field_simp [hkm1.ne', hkm3.ne']]
      refine div_le_div_of_nonneg_right ?_ hkm1.le
      rw [div_le_iff₀ hkm3]; linarith
    have h2b_nn : 0 ≤ 2 * b := by positivity
    nlinarith
  have hpiece12 := gs_piece12_bound hk hSD_v1 huR_sum
  have hvAnti_nn : 0 ≤ ∑ x, vAnti x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4sq_nn : 0 ≤ (4 / ((k : ℝ) - 1)) ^ 2 := sq_nonneg _
  rw [hTv_norm, hv_norm]
  nlinarith

/-! ### Main theorem -/

/-- **Guruswami–Sinop,**: for `k ≥ 6`, `guruswamiSinopMatrix k` is a colourful
symmetric Markov operator on `[k]²` with spectral radius at most `4 / (k - 1)` whose entries are
nonnegative integer multiples of `1 / ((k - 1)(k - 2)(k - 3))`.
-/
theorem guruswamiSinop_markov_operator {k : ℕ} (hk : 6 ≤ k) :
    let T := guruswamiSinopMatrix k
    IsSymmetricMarkovOperator T ∧
      IsColourfulMarkov T ∧
      HasMarkovSpectralRadiusBound T (4 / ((k : ℝ) - 1)) ∧
      (∀ x y : Fin 2 → Fin k, ∃ m : ℕ,
        T x y = (m : ℝ) * (1 / (((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3)))) := by
  classical
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hkm3 : (0 : ℝ) < (k : ℝ) - 3 := by linarith
  refine ⟨⟨?_, ?_, gs_row_sum hk⟩, ?_, gs_spectral_bound hk, ?_⟩
  · ext x y
    simp only [Matrix.transpose_apply, guruswamiSinopMatrix, Matrix.of_apply]
    have hdisj : (∀ i j : Fin 2, y i ≠ x j) ↔ (∀ i j : Fin 2, x i ≠ y j) :=
      ⟨fun h i j heq => h j i heq.symm, fun h i j heq => h j i heq.symm⟩
    rw [if_congr hdisj rfl rfl]
    by_cases hx : x 0 = x 1 <;> by_cases hy : y 0 = y 1 <;> simp [hx, hy]
  · intro x y
    simp only [guruswamiSinopMatrix, Matrix.of_apply]
    split_ifs <;> positivity
  · intro x y hpos
    by_contra h
    simp only [guruswamiSinopMatrix, Matrix.of_apply, h, ↓reduceIte] at hpos
    exact lt_irrefl 0 hpos
  · intro x y
    simp only [guruswamiSinopMatrix, Matrix.of_apply]
    split_ifs
    · exact ⟨0, by simp⟩
    · refine ⟨k - 3, ?_⟩
      rw [Nat.cast_sub (by omega)]; simp only [Nat.cast_ofNat]
      field_simp [hkm1.ne', hkm2.ne', hkm3.ne']
    · refine ⟨k - 3, ?_⟩
      rw [Nat.cast_sub (by omega)]; simp only [Nat.cast_ofNat]
      field_simp [hkm1.ne', hkm2.ne', hkm3.ne']
    · refine ⟨k - 2, ?_⟩
      rw [Nat.cast_sub (by omega)]; simp only [Nat.cast_ofNat]
      field_simp [hkm1.ne', hkm2.ne', hkm3.ne']
    · exact ⟨0, by simp⟩

end CslibFrontier.Foundations.BooleanAnalysis
