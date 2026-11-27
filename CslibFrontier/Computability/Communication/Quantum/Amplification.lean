/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Quantum.Factorization

import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Amplified QMA Communication Factorization

This module proves `qma_comm_amplified_factorization`: for every `w`-qubit, `c`-qubit
`QuantumCommProtocol X Y w` (with unlimited finite-dimensional shared entanglement) computing
`F : X × Y → Bool` with completeness and soundness error `1 / 3` and every `δ ∈ (0, 1 / 4]`,
there exist a real matrix `Π` and real factorization `Π = A * B` such that:

- on YES inputs, `Π x y ∈ [(1 - δ) * 2^{-w}, 1]`,
- on NO inputs, `Π x y ∈ [0, δ]`,
- `‖A‖_F * ‖B‖_F ≤ 4^{c'} * √(|X| * |Y|)` with `c' = 0` when `c = 0` and
  `c' ≤ 2 * c * (⌈288 * log(1 / δ)⌉₊ + 1)` when `c ≥ 1`.

The proof evaluates the majority Bernstein polynomial `Q_T(M_{x,y})` on the witness acceptance
operator `M_{x,y}` and combines `exists_schmidt_operator_factorization` with a `T`-fold
operator-norm induction, avoiding any dependence on the shared entanglement dimension.

## Main results

* `CslibFrontier.CommunicationComplexity.qma_comm_amplified_factorization`: amplified maximally-
  mixed
  real factorization for QMA communication protocols with unlimited shared entanglement.
-/

public section

open scoped BigOperators
open Finset Matrix Cslib Cslib.BitString

namespace CslibFrontier.CommunicationComplexity

section Amplification

variable {X Y : Type*} [Fintype X] [Fintype Y] {w : ℕ}

/-- Elementary Bernoulli majority tail bound for `lam ≤ 1/3`:
`∑_{weight z ≥ T/2} lam^{weight z} (1 - lam)^{T - weight z} ≤ exp(-T / 288)`. -/
private lemma bernoulli_majority_tail {T : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 3) :
    ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
      lam ^ weight z * (1 - lam) ^ (T - weight z) ≤ Real.exp (-(T : ℝ) / 288) := by
  set u : ℝ := (1 / 2 - lam) / 4
  have hu0 : 0 < u := by simp only [u]; linarith
  have hu1 : u ≤ 1 / 4 := by simp only [u]; linarith
  have hexp_u : Real.exp u ≤ 1 + u + 2 * u ^ 2 := by
    have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have h2 : (1 - u) * Real.exp u ≤ 1 := by
      calc (1 - u) * Real.exp u ≤ Real.exp (-u) * Real.exp u :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg u)
        _ = 1 := by rw [← Real.exp_add]; simp
    have h3 : 1 ≤ (1 - u) * (1 + u + 2 * u ^ 2) := by nlinarith
    nlinarith
  have hstep : Real.exp (-u * (1 / 2)) * (1 - lam + lam * Real.exp u) ≤
      Real.exp (-(1 / 2 - lam) ^ 2 / 8) := by
    have hmgf : 1 - lam + lam * Real.exp u ≤ Real.exp (lam * u + 2 * u ^ 2) := by
      have h1 : 1 - lam + lam * Real.exp u ≤ 1 + (lam * u + 2 * u ^ 2) := by nlinarith
      exact h1.trans (by linarith [Real.add_one_le_exp (lam * u + 2 * u ^ 2)])
    calc Real.exp (-u * (1 / 2)) * (1 - lam + lam * Real.exp u)
        ≤ Real.exp (-u * (1 / 2)) * Real.exp (lam * u + 2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = Real.exp (-u * (1 / 2) + (lam * u + 2 * u ^ 2)) := (Real.exp_add _ _).symm
      _ = Real.exp (-(1 / 2 - lam) ^ 2 / 8) := by congr 1; simp only [u]; ring
  have hmarkov : ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
      lam ^ weight z * (1 - lam) ^ (T - weight z) ≤
      Real.exp (-u * ((T : ℝ) / 2)) *
        ∑ z : BitString T,
          Real.exp (u * (weight z : ℝ)) * (lam ^ weight z * (1 - lam) ^ (T - weight z)) := by
    rw [Finset.mul_sum]
    calc ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
          lam ^ weight z * (1 - lam) ^ (T - weight z)
        ≤ ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
            Real.exp (-u * ((T : ℝ) / 2)) *
              (Real.exp (u * (weight z : ℝ)) * (lam ^ weight z * (1 - lam) ^ (T - weight z))) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hwz : (T : ℝ) / 2 ≤ (weight z : ℝ) := (Finset.mem_filter.mp hz).2
          have hexp1 : (1 : ℝ) ≤ Real.exp (-u * ((T : ℝ) / 2)) * Real.exp (u * (weight z : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
          nlinarith [mul_nonneg (pow_nonneg hlam0 (weight z))
            (pow_nonneg (by linarith : 0 ≤ 1 - lam) (T - weight z))]
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun z =>
          mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _)
            (mul_nonneg (pow_nonneg hlam0 _) (pow_nonneg (by linarith) _)))
  have hprod : ∑ z : BitString T,
      Real.exp (u * (weight z : ℝ)) * (lam ^ weight z * (1 - lam) ^ (T - weight z)) =
      (1 - lam + lam * Real.exp u) ^ T := by
    have hfac : ∀ z : BitString T,
        Real.exp (u * (weight z : ℝ)) * (lam ^ weight z * (1 - lam) ^ (T - weight z)) =
        ∏ i : Fin T, (if z i = true then lam * Real.exp u else 1 - lam) := by
      intro z
      have hcard : #{i : Fin T | z i = false} = T - weight z := by
        simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight z
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin T => z i = true)]
      have h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin T => z i = true),
          (if z i = true then lam * Real.exp u else 1 - lam) = (lam * Real.exp u) ^ weight z := by
        calc ∏ i ∈ Finset.univ.filter (fun i : Fin T => z i = true),
              (if z i = true then lam * Real.exp u else 1 - lam)
            = ∏ _i ∈ Finset.univ.filter (fun i : Fin T => z i = true), (lam * Real.exp u) :=
              Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
          _ = (lam * Real.exp u) ^ weight z := by rw [Finset.prod_const]; rfl
      have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin T => ¬ z i = true),
          (if z i = true then lam * Real.exp u else 1 - lam) = (1 - lam) ^ (T - weight z) := by
        have hnot : Finset.univ.filter (fun i : Fin T => ¬ z i = true) =
            Finset.univ.filter (fun i : Fin T => z i = false) := by ext i; simp
        rw [hnot]
        calc ∏ i ∈ Finset.univ.filter (fun i : Fin T => z i = false),
              (if z i = true then lam * Real.exp u else 1 - lam)
            = ∏ _i ∈ Finset.univ.filter (fun i : Fin T => z i = false), (1 - lam) :=
              Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
          _ = (1 - lam) ^ (T - weight z) := by rw [Finset.prod_const, hcard]
      rw [h1, h2, mul_pow, ← Real.exp_nat_mul, mul_comm (weight z : ℝ) u]; ring
    simp_rw [hfac]
    rw [← Fintype.prod_sum (fun (_ : Fin T) (b : Bool) =>
      if b = true then lam * Real.exp u else 1 - lam)]
    refine (Finset.prod_congr rfl fun _ _ => ?_).trans
      (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]; ring
  calc ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
        lam ^ weight z * (1 - lam) ^ (T - weight z)
      ≤ Real.exp (-u * ((T : ℝ) / 2)) * (1 - lam + lam * Real.exp u) ^ T := by
        rw [← hprod]; exact hmarkov
    _ = (Real.exp (-u * (1 / 2)) * (1 - lam + lam * Real.exp u)) ^ T := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
    _ ≤ (Real.exp (-(1 / 2 - lam) ^ 2 / 8)) ^ T :=
        pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) (by nlinarith [Real.exp_nonneg u])) hstep T
    _ = Real.exp (-(T : ℝ) * (1 / 2 - lam) ^ 2 / 8) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(T : ℝ) / 288) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : (1 / 6 : ℝ) ^ 2 ≤ (1 / 2 - lam) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 2
        nlinarith [Nat.cast_nonneg (α := ℝ) T]

/-- Total binomial probability mass equals `1`. -/
private lemma bernoulli_sum_eq_one {T : ℕ} (lam : ℝ) :
    ∑ z : BitString T, lam ^ weight z * (1 - lam) ^ (T - weight z) = 1 := by
  have hfac : ∀ z : BitString T, lam ^ weight z * (1 - lam) ^ (T - weight z) =
      ∏ i : Fin T, (if z i then lam else 1 - lam) := by
    intro z
    have hcard : #{i : Fin T | z i = false} = T - weight z := by
      simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight z
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin T => z i = true)]
    have h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin T => z i = true),
        (if z i then lam else 1 - lam) = lam ^ weight z := by
      calc ∏ i ∈ Finset.univ.filter (fun i : Fin T => z i = true),
            (if z i then lam else 1 - lam)
          = ∏ _i ∈ Finset.univ.filter (fun i : Fin T => z i = true), lam :=
            Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        _ = lam ^ weight z := by rw [Finset.prod_const]; rfl
    have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin T => ¬ z i = true),
        (if z i then lam else 1 - lam) = (1 - lam) ^ (T - weight z) := by
      have hnot : Finset.univ.filter (fun i : Fin T => ¬ z i = true) =
          Finset.univ.filter (fun i : Fin T => z i = false) := by ext i; simp
      rw [hnot]
      calc ∏ i ∈ Finset.univ.filter (fun i : Fin T => z i = false),
            (if z i then lam else 1 - lam)
          = ∏ _i ∈ Finset.univ.filter (fun i : Fin T => z i = false), (1 - lam) :=
            Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        _ = (1 - lam) ^ (T - weight z) := by rw [Finset.prod_const, hcard]
    rw [h1, h2]
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun (_ : Fin T) (b : Bool) => if b then lam else 1 - lam)]
  simp

/-- Complement Bernoulli majority tail bound for `2/3 ≤ lam ≤ 1`:
`1 - Real.exp (-T / 288) ≤ ∑_{weight z ≥ T/2} lam^{weight z} (1 - lam)^{T - weight z}`. -/
private lemma bernoulli_majority_lower {T : ℕ} {lam : ℝ} (hlam0 : 2 / 3 ≤ lam) (hlam1 : lam ≤ 1) :
    1 - Real.exp (-(T : ℝ) / 288) ≤
      ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
        lam ^ weight z * (1 - lam) ^ (T - weight z) := by
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun z : BitString T => (T : ℝ) / 2 ≤ (weight z : ℝ))
    (fun z => lam ^ weight z * (1 - lam) ^ (T - weight z))
  rw [bernoulli_sum_eq_one] at hpart
  have hcompl : ∑ z ∈ Finset.univ.filter (fun z : BitString T => ¬ (T : ℝ) / 2 ≤ (weight z : ℝ)),
      lam ^ weight z * (1 - lam) ^ (T - weight z) ≤ Real.exp (-(T : ℝ) / 288) := by
    let flip : BitString T ≃ BitString T :=
      { toFun := fun z i => !z i
        invFun := fun z i => !z i
        left_inv := fun z => by funext i; simp
        right_inv := fun z => by funext i; simp }
    have hflip : ∀ z : BitString T, weight (flip z) = T - weight z := fun z => by
      simpa [flip, Fintype.card_fin] using weight_not z
    have hle_flip : ∑ z ∈ Finset.univ.filter (fun z : BitString T => ¬ (T : ℝ) / 2 ≤
          (weight z : ℝ)), lam ^ weight z * (1 - lam) ^ (T - weight z) ≤
        ∑ z' : BitString T with (T : ℝ) / 2 ≤ (weight z' : ℝ),
          (1 - lam) ^ weight z' * (1 - (1 - lam)) ^ (T - weight z') := by
      calc ∑ z ∈ Finset.univ.filter (fun z : BitString T => ¬ (T : ℝ) / 2 ≤ (weight z : ℝ)),
            lam ^ weight z * (1 - lam) ^ (T - weight z)
          = ∑ z' : BitString T with (T : ℝ) / 2 < (weight z' : ℝ),
              (1 - lam) ^ weight z' * (1 - (1 - lam)) ^ (T - weight z') := by
            refine Finset.sum_bij (fun z _ => flip z) ?_ ?_ ?_ ?_
            · intro z hz
              have hwle : weight z ≤ T := by simpa [Fintype.card_fin] using weight_le z
              have hlt : (weight z : ℝ) < (T : ℝ) / 2 := not_le.mp (Finset.mem_filter.mp hz).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rw [hflip, Nat.cast_sub hwle]; linarith
            · intro a _ b _ h; exact flip.injective h
            · intro z' hz'
              have hwle : weight z' ≤ T := by simpa [Fintype.card_fin] using weight_le z'
              have hgt : (T : ℝ) / 2 < (weight z' : ℝ) := (Finset.mem_filter.mp hz').2
              refine ⟨flip z', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
                by funext i; simp [flip]⟩
              rw [hflip, Nat.cast_sub hwle]; linarith
            · intro z _
              have hwle : weight z ≤ T := by simpa [Fintype.card_fin] using weight_le z
              rw [hflip, Nat.sub_sub_self hwle, sub_sub_cancel, mul_comm]
        _ ≤ ∑ z' : BitString T with (T : ℝ) / 2 ≤ (weight z' : ℝ),
              (1 - lam) ^ weight z' * (1 - (1 - lam)) ^ (T - weight z') :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun z' hz' =>
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp hz').2⟩)
              (fun z' _ _ => mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))
    exact hle_flip.trans (bernoulli_majority_tail (by linarith) (by linarith))
  linarith

/-- Matrix product expansion for `foldl (· * ·) 1` of sums over `T₀`. -/
private lemma foldl_mul_sum_eq {α T₀ : Type*} [Fintype α] [DecidableEq α] [Fintype T₀]
    (n : ℕ) (r : T₀ → ℂ) (f : Fin n → T₀ → Matrix α α ℂ) :
    (List.ofFn fun i : Fin n => ∑ t : T₀, r t • f i t).foldl (· * ·) 1 =
      ∑ t : Fin n → T₀, (∏ i : Fin n, r (t i)) •
        (List.ofFn fun i : Fin n => f i (t i)).foldl (· * ·) 1 := by
  induction n with
  | zero =>
    have hsing : (Finset.univ : Finset (Fin 0 → T₀)) = {Fin.elim0} := by
      ext g; simp [funext_iff]
    rw [hsing, Finset.sum_singleton]; simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, ih (fun i => f i.castSucc)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Finset.sum_mul]
    have hstep : ∀ g : Fin n → T₀,
        ((∏ i : Fin n, r (g i)) • (List.ofFn fun i : Fin n => f i.castSucc (g i)).foldl (· * ·) 1) *
          (∑ tLast : T₀, r tLast • f (Fin.last n) tLast) =
        ∑ tLast : T₀, (∏ i : Fin (n + 1), r (Fin.snoc (α := fun _ => T₀) g tLast i)) •
          (List.ofFn fun i : Fin (n + 1) =>
            f i (Fin.snoc (α := fun _ => T₀) g tLast i)).foldl (· * ·) 1 := by
      intro g
      rw [Matrix.mul_sum]
      refine Finset.sum_congr rfl fun tLast _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [hstep]
    let e : (Fin n → T₀) × T₀ ≃ (Fin (n + 1) → T₀) :=
      { toFun := fun p => Fin.snoc (α := fun _ => T₀) p.1 p.2
        invFun := fun h => (fun i => h i.castSucc, h (Fin.last n))
        left_inv := fun ⟨_, _⟩ => Prod.ext (funext fun _ => by simp) (by simp)
        right_inv := fun h => by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp }
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- `T`-fold operator norm bound for `Smat`. -/
private lemma sum_norm_sq_foldl_Smat_le {α T₀ : Type*} [Fintype α] [DecidableEq α] [Fintype T₀]
    {C : ℝ} (hC : 0 ≤ C) (Smat : Bool → T₀ → Matrix α α ℂ)
    (hS : ∀ v : EuclideanSpace ℂ α,
      ∑ t : T₀, ∑ z : Bool, ‖(Smat z t).toEuclideanLin v‖ ^ 2 ≤ C * ‖v‖ ^ 2) :
    ∀ (n : ℕ) (v : EuclideanSpace ℂ α),
      ∑ t : Fin n → T₀, ∑ z : BitString n,
        ‖((List.ofFn fun i : Fin n => Smat (z i) (t i)).foldl (· * ·) 1).toEuclideanLin v‖ ^ 2 ≤
        C ^ n * ‖v‖ ^ 2 := by
  intro n; induction n with
  | zero =>
    intro v
    have h1 : (Finset.univ : Finset (Fin 0 → T₀)) = {Fin.elim0} := by ext g; simp [funext_iff]
    have h2 : (Finset.univ : Finset (BitString 0)) = {Fin.elim0} := by ext g; simp [funext_iff]
    rw [h1, Finset.sum_singleton, h2, Finset.sum_singleton]; simp
  | succ n ih =>
    intro v
    let eT : (Fin n → T₀) × T₀ ≃ (Fin (n + 1) → T₀) :=
      { toFun := fun p => Fin.snoc (α := fun _ => T₀) p.1 p.2
        invFun := fun h => (fun i => h i.castSucc, h (Fin.last n))
        left_inv := fun ⟨_, _⟩ => by ext i <;> simp
        right_inv := fun h => by funext i; refine Fin.lastCases ?_ ?_ i <;> simp }
    let eZ : BitString n × Bool ≃ BitString (n + 1) :=
      { toFun := fun p => Fin.snoc (α := fun _ => Bool) p.1 p.2
        invFun := fun h => (fun i => h i.castSucc, h (Fin.last n))
        left_inv := fun ⟨_, _⟩ => by ext i <;> simp
        right_inv := fun h => by funext i; refine Fin.lastCases ?_ ?_ i <;> simp }
    have houter : ∑ t : Fin (n + 1) → T₀, ∑ z : BitString (n + 1),
          ‖((List.ofFn fun i : Fin (n + 1) => Smat (z i) (t i)).foldl (· * ·) 1).toEuclideanLin
            v‖ ^ 2 =
        ∑ tLast : T₀, ∑ g : Fin n → T₀, ∑ z : BitString (n + 1),
          ‖((List.ofFn fun i : Fin (n + 1) =>
            Smat (z i) (Fin.snoc (α := fun _ => T₀) g tLast i)).foldl (· * ·) 1).toEuclideanLin
            v‖ ^ 2 := by
      refine (Fintype.sum_equiv eT
        (fun p => ∑ z : BitString (n + 1),
          ‖((List.ofFn fun i : Fin (n + 1) =>
            Smat (z i) (Fin.snoc (α := fun _ => T₀) p.1 p.2 i)).foldl (· * ·) 1).toEuclideanLin
            v‖ ^ 2)
        _ (fun _ => rfl)).symm.trans ?_
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [houter]
    have hinner : ∀ (g : Fin n → T₀) (tLast : T₀),
        ∑ z : BitString (n + 1),
          ‖((List.ofFn fun i : Fin (n + 1) =>
            Smat (z i) (Fin.snoc (α := fun _ => T₀) g tLast i)).foldl (· * ·) 1).toEuclideanLin
            v‖ ^ 2 =
        ∑ zLast : Bool, ∑ zInit : BitString n,
          ‖((List.ofFn fun i : Fin n => Smat (zInit i) (g i)).foldl (· * ·) 1).toEuclideanLin
            ((Smat zLast tLast).toEuclideanLin v)‖ ^ 2 := by
      intro g tLast
      have h1 : ∑ z : BitString (n + 1),
            ‖((List.ofFn fun i : Fin (n + 1) =>
              Smat (z i) (Fin.snoc (α := fun _ => T₀) g tLast i)).foldl (· * ·) 1).toEuclideanLin
              v‖ ^ 2 =
          ∑ zLast : Bool, ∑ zInit : BitString n,
            ‖((List.ofFn fun i : Fin (n + 1) =>
              Smat (Fin.snoc (α := fun _ => Bool) zInit zLast i)
                (Fin.snoc (α := fun _ => T₀) g tLast i)).foldl (· * ·) 1).toEuclideanLin
              v‖ ^ 2 := by
        refine (Fintype.sum_equiv eZ
          (fun p => ‖((List.ofFn fun i : Fin (n + 1) =>
            Smat (Fin.snoc (α := fun _ => Bool) p.1 p.2 i)
              (Fin.snoc (α := fun _ => T₀) g tLast i)).foldl (· * ·) 1).toEuclideanLin v‖ ^ 2)
          _ (fun _ => rfl)).symm.trans ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      rw [h1]
      refine Finset.sum_congr rfl fun zLast _ => Finset.sum_congr rfl fun zInit _ => ?_
      congr 2
      simp only [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons,
        List.foldl_nil, Fin.snoc_castSucc, Fin.snoc_last]
      change Matrix.toLpLin 2 2 (_ * _) v = _
      rw [Matrix.toLpLin_mul_same]; rfl
    simp_rw [hinner]
    have hstep1 : ∀ (tLast : T₀) (zLast : Bool),
        ∑ g : Fin n → T₀, ∑ zInit : BitString n,
          ‖((List.ofFn fun i : Fin n => Smat (zInit i) (g i)).foldl (· * ·) 1).toEuclideanLin
            ((Smat zLast tLast).toEuclideanLin v)‖ ^ 2 ≤
          C ^ n * ‖(Smat zLast tLast).toEuclideanLin v‖ ^ 2 :=
      fun tLast zLast => ih ((Smat zLast tLast).toEuclideanLin v)
    calc ∑ tLast : T₀, ∑ g : Fin n → T₀, ∑ zLast : Bool, ∑ zInit : BitString n, _
        = ∑ tLast : T₀, ∑ zLast : Bool, ∑ g : Fin n → T₀, ∑ zInit : BitString n, _ := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ ≤ ∑ tLast : T₀, ∑ zLast : Bool, C ^ n * ‖(Smat zLast tLast).toEuclideanLin v‖ ^ 2 :=
          Finset.sum_le_sum fun tLast _ => Finset.sum_le_sum fun zLast _ => hstep1 tLast zLast
      _ = C ^ n * ∑ tLast : T₀, ∑ zLast : Bool, ‖(Smat zLast tLast).toEuclideanLin v‖ ^ 2 := by
          simp_rw [← Finset.mul_sum]
      _ ≤ C ^ n * (C * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left (hS v) (pow_nonneg hC n)
      _ = C ^ (n + 1) * ‖v‖ ^ 2 := by ring

private def stdBasisVec {w : ℕ} (u : BitString w) : EuclideanSpace ℂ (BitString w) :=
  WithLp.toLp 2 fun a => if a = u then 1 else 0

private lemma norm_sq_stdBasisVec {w : ℕ} (u : BitString w) : ‖stdBasisVec u‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  trans ∑ x : BitString w, if x = u then (1 : ℝ) else 0
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x = u <;> simp [stdBasisVec, h]
  · simp

private lemma matrix_trace_norm_sq_le {w : ℕ} (M : Matrix (BitString w) (BitString w) ℂ) :
    ‖M.trace‖ ^ 2 ≤ (2 : ℝ) ^ w * ∑ u : BitString w,
      ‖M.toEuclideanLin (stdBasisVec u)‖ ^ 2 := by
  have htri : ‖M.trace‖ ≤ ∑ u : BitString w, (1 : ℝ) * ‖M.toEuclideanLin (stdBasisVec u)‖ := by
    calc ‖M.trace‖ ≤ ∑ u : BitString w, ‖M u u‖ := norm_sum_le _ _
      _ ≤ ∑ u : BitString w, ‖M.toEuclideanLin (stdBasisVec u)‖ := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hcoord : (M.toEuclideanLin (stdBasisVec u)).ofLp u = M u u := by
          simp [stdBasisVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
        rw [← hcoord]
        exact PiLp.norm_apply_le _ u
      _ = _ := by simp
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (BitString w))
    (fun _ => (1 : ℝ)) (fun u => ‖M.toEuclideanLin (stdBasisVec u)‖)
  simpa [Fintype.card_fun] using hsq.trans hcs

private lemma qma_comm_B_pt_sq_le {w T : ℕ}
    (M : BitString T → Matrix (BitString w) (BitString w) ℂ) :
    ‖((2 : ℝ) ^ (-(w : ℤ)) : ℂ) * ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
      (M z).trace‖ ^ 2 ≤
    (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) *
      ∑ z : BitString T, ∑ u : BitString w, ‖(M z).toEuclideanLin (stdBasisVec u)‖ ^ 2 := by
  have hnorm_w : ‖((2 : ℝ) ^ (-(w : ℤ)) : ℂ)‖ = (2 : ℝ) ^ (-(w : ℤ)) := by
    rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [norm_mul, mul_pow, hnorm_w]
  have hcs_z : ‖∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ), (M z).trace‖ ^ 2 ≤
      (2 : ℝ) ^ T * ∑ z : BitString T, ‖(M z).trace‖ ^ 2 := by
    have htri : ‖∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ), (M z).trace‖ ≤
        ∑ z : BitString T, (1 : ℝ) * ‖(M z).trace‖ := by
      calc _ ≤ ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ), ‖(M z).trace‖ :=
            norm_sum_le _ _
        _ ≤ ∑ z : BitString T, ‖(M z).trace‖ :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _
        _ = _ := by simp
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (BitString T))
      (fun _ => (1 : ℝ)) (fun z => ‖(M z).trace‖)
    simpa [Fintype.card_fun] using hsq.trans hcs
  have hpow_w : ((2 : ℝ) ^ (-(w : ℤ))) ^ 2 * (2 : ℝ) ^ w = (2 : ℝ) ^ (-(w : ℤ)) := by
    rw [_root_.zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  calc ((2 : ℝ) ^ (-(w : ℤ))) ^ 2 *
        ‖∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ), (M z).trace‖ ^ 2
      ≤ ((2 : ℝ) ^ (-(w : ℤ))) ^ 2 * ((2 : ℝ) ^ T * ∑ z : BitString T, ‖(M z).trace‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs_z (sq_nonneg _)
    _ ≤ ((2 : ℝ) ^ (-(w : ℤ))) ^ 2 * ((2 : ℝ) ^ T * ∑ z : BitString T,
          (2 : ℝ) ^ w * ∑ u : BitString w, ‖(M z).toEuclideanLin (stdBasisVec u)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun z _ => matrix_trace_norm_sq_le (M z)) (by positivity))
          (sq_nonneg _)
    _ = (2 : ℝ) ^ T * (((2 : ℝ) ^ (-(w : ℤ))) ^ 2 * (2 : ℝ) ^ w) *
          ∑ z : BitString T, ∑ u : BitString w, ‖(M z).toEuclideanLin (stdBasisVec u)‖ ^ 2 := by
        simp_rw [← Finset.mul_sum]; ring
    _ = (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) *
          ∑ z : BitString T, ∑ u : BitString w, ‖(M z).toEuclideanLin (stdBasisVec u)‖ ^ 2 := by
        rw [hpow_w]

private lemma qma_comm_B_col_sq_le {T₀ : Type*} [Fintype T₀] {w c T : ℕ}
    (Smat : Bool → T₀ → Matrix (BitString w) (BitString w) ℂ)
    (hS : ∀ v : EuclideanSpace ℂ (BitString w),
      ∑ t : T₀, ∑ z : Bool, ‖(Smat z t).toEuclideanLin v‖ ^ 2 ≤ (4 : ℝ) ^ c * ‖v‖ ^ 2) :
    ∑ t : Fin T → T₀,
      ‖((2 : ℝ) ^ (-(w : ℤ)) : ℂ) * ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
        ((List.ofFn fun r : Fin T => Smat (z r) (t r)).foldl (· * ·) 1).trace‖ ^ 2 ≤
      (4 : ℝ) ^ ((c + 1) * T) := by
  let g (t : Fin T → T₀) (z : BitString T) (u : BitString w) : ℝ :=
    ‖((List.ofFn fun r : Fin T => Smat (z r) (t r)).foldl (· * ·) 1).toEuclideanLin
      (stdBasisVec u)‖ ^ 2
  have h1 : ∑ t : Fin T → T₀,
        ‖((2 : ℝ) ^ (-(w : ℤ)) : ℂ) * ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
          ((List.ofFn fun r : Fin T => Smat (z r) (t r)).foldl (· * ·) 1).trace‖ ^ 2 ≤
      (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) *
        ∑ t : Fin T → T₀, ∑ z : BitString T, ∑ u : BitString w, g t z u := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ =>
      qma_comm_B_pt_sq_le (fun z =>
        (List.ofFn fun r : Fin T => Smat (z r) (t r)).foldl (· * ·) 1)
  have h2 : ∑ t : Fin T → T₀, ∑ z : BitString T, ∑ u : BitString w, g t z u =
      ∑ u : BitString w, ∑ t : Fin T → T₀, ∑ z : BitString T, g t z u := by
    trans ∑ t : Fin T → T₀, ∑ u : BitString w, ∑ z : BitString T, g t z u
    · exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
    · exact Finset.sum_comm
  have h3 : ∑ u : BitString w, ∑ t : Fin T → T₀, ∑ z : BitString T, g t z u ≤
      (2 : ℝ) ^ w * ((4 : ℝ) ^ c) ^ T := by
    have h4 : ∑ u : BitString w, ∑ t : Fin T → T₀, ∑ z : BitString T, g t z u ≤
        ∑ _u : BitString w, ((4 : ℝ) ^ c) ^ T := by
      refine Finset.sum_le_sum fun u _ => ?_
      simpa only [g, norm_sq_stdBasisVec u, mul_one] using
        sum_norm_sq_foldl_Smat_le (by positivity) Smat hS T (stdBasisVec u)
    refine h4.trans_eq ?_
    simp [Finset.sum_const]
  have h4 : (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) * ((2 : ℝ) ^ w * ((4 : ℝ) ^ c) ^ T) =
      (2 : ℝ) ^ T * ((4 : ℝ) ^ c) ^ T := by
    rw [_root_.zpow_neg, zpow_natCast]
    have hinv : ((2 : ℝ) ^ w)⁻¹ * (2 : ℝ) ^ w = 1 := inv_mul_cancel₀ (by positivity)
    linear_combination (2 : ℝ) ^ T * ((4 : ℝ) ^ c) ^ T * hinv
  have h5 : (2 : ℝ) ^ T * ((4 : ℝ) ^ c) ^ T ≤ (4 : ℝ) ^ ((c + 1) * T) := by
    rw [add_mul, one_mul, pow_add, ← pow_mul, mul_comm ((4 : ℝ) ^ (c * T))]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) T)
      (by positivity)
  calc _ ≤ (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) *
            ∑ t : Fin T → T₀, ∑ z : BitString T, ∑ u : BitString w, g t z u := h1
    _ = (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) *
            ∑ u : BitString w, ∑ t : Fin T → T₀, ∑ z : BitString T, g t z u := by rw [h2]
    _ ≤ (2 : ℝ) ^ T * (2 : ℝ) ^ (-(w : ℤ)) * ((2 : ℝ) ^ w * ((4 : ℝ) ^ c) ^ T) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (2 : ℝ) ^ T * ((4 : ℝ) ^ c) ^ T := h4
    _ ≤ (4 : ℝ) ^ ((c + 1) * T) := h5

/-- Spectral evaluation of the majority Bernstein trace on a Hermitian matrix `M` with
`M + IM = 1`. -/
private lemma hermitian_majority_trace_spectral {w T : ℕ}
    (M IM : Matrix (BitString w) (BitString w) ℂ) (hM_herm : M.IsHermitian)
    (hM_plus_IM : M + IM = 1) (acc : EuclideanSpace ℂ (BitString w) → ℝ)
    (hM_quad : ∀ ψ : EuclideanSpace ℂ (BitString w), dotProduct (star ⇑ψ) (M *ᵥ ⇑ψ) = (acc ψ : ℂ)) :
    let eV := hM_herm.eigenvectorBasis
    let lam := hM_herm.eigenvalues
    (∀ j, lam j = acc (eV j)) ∧
    (∀ ψ : EuclideanSpace ℂ (BitString w),
      acc ψ = ∑ j : BitString w, ‖inner ℂ (eV j) ψ‖ ^ 2 * lam j) ∧
    (∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
        ((List.ofFn fun r : Fin T => if z r then M else IM).foldl (· * ·) 1).trace).re =
      ∑ j : BitString w, ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
        (lam j) ^ weight z * (1 - lam j) ^ (T - weight z) := by
  intro eV lam
  have heig : ∀ j, M *ᵥ ⇑(eV j) = (lam j : ℂ) • ⇑(eV j) := fun j => by
    ext u; have h := congrFun (hM_herm.mulVec_eigenvectorBasis j) u
    simpa [eV, lam, Complex.real_smul] using h
  have hlam_eq : ∀ j, lam j = acc (eV j) := fun j => by
    dsimp only [lam]
    rw [hM_herm.eigenvalues_eq j, hM_quad (eV j), RCLike.re_eq_complex_re, Complex.ofReal_re]
  have hspec : ∀ ψ, acc ψ = ∑ j, ‖inner ℂ (eV j) ψ‖ ^ 2 * lam j := by
    intro ψ
    have hrepr : ψ = ∑ j, inner ℂ (eV j) ψ • eV j := (eV.sum_repr' ψ).symm
    have hMψ : M *ᵥ ⇑ψ = ∑ j, (inner ℂ (eV j) ψ * (lam j : ℂ)) • ⇑(eV j) := by
      have hlin : ∀ S_fin : Finset (BitString w),
          M *ᵥ ⇑(∑ j ∈ S_fin, inner ℂ (eV j) ψ • eV j) =
            ∑ j ∈ S_fin, (inner ℂ (eV j) ψ * (lam j : ℂ)) • ⇑(eV j) := by
        intro S_fin; induction S_fin using Finset.induction_on with
        | empty => simp
        | insert a S_fin ha ih =>
          have hadd : (⇑(inner ℂ (eV a) ψ • eV a + ∑ j ∈ S_fin, inner ℂ (eV j) ψ • eV j) :
              BitString w → ℂ) = ⇑(inner ℂ (eV a) ψ • eV a) +
              ⇑(∑ j ∈ S_fin, inner ℂ (eV j) ψ • eV j) := by funext i; rfl
          have hsm : (⇑(inner ℂ (eV a) ψ • eV a) : BitString w → ℂ) =
              inner ℂ (eV a) ψ • ⇑(eV a) := by funext i; rfl
          rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, Matrix.mulVec_add,
            hsm, Matrix.mulVec_smul, heig a, smul_smul, ih]
      conv_lhs => rw [hrepr]
      exact hlin Finset.univ
    have hdot : dotProduct (star ⇑ψ) (M *ᵥ ⇑ψ) =
        ∑ j : BitString w, ((‖inner ℂ (eV j) ψ‖ ^ 2 * lam j : ℝ) : ℂ) := by
      rw [hMψ, dotProduct_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
      have h1 : dotProduct (star ⇑ψ) ⇑(eV j) = inner ℂ ψ (eV j) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h1, ← inner_conj_symm ψ (eV j), mul_comm (inner ℂ (eV j) ψ), mul_assoc,
        mul_comm (lam j : ℂ), Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    have hre := congrArg Complex.re ((hM_quad ψ).symm.trans hdot)
    rw [← Complex.ofReal_sum] at hre
    simpa only [Complex.ofReal_re] using hre
  refine ⟨hlam_eq, hspec, ?_⟩
  have hprod_eig : ∀ (z : BitString T) (j : BitString w),
      ((List.ofFn fun r : Fin T => if z r then M else IM).foldl (· * ·) 1) *ᵥ ⇑(eV j) =
        (((lam j) ^ weight z * (1 - lam j) ^ (T - weight z) : ℝ) : ℂ) • ⇑(eV j) := by
    intro z j
    have hIM_eig : IM *ᵥ ⇑(eV j) = ((1 - lam j : ℝ) : ℂ) • ⇑(eV j) := by
      have h1 := congrArg (fun A : Matrix (BitString w) (BitString w) ℂ => A *ᵥ ⇑(eV j)) hM_plus_IM
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, heig j] at h1
      ext u; have hu := congrFun h1 u
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
        Complex.ofReal_one] at hu ⊢
      linear_combination hu
    have hfold : ∀ (l : List Bool),
        ((l.map fun b => if b then M else IM).foldl (· * ·) 1) *ᵥ ⇑(eV j) =
          (((lam j) ^ (l.count true) * (1 - lam j) ^ (l.count false) : ℝ) : ℂ) • ⇑(eV j) := by
      intro l
      suffices hgen : ∀ (accM : Matrix (BitString w) (BitString w) ℂ) (c : ℂ),
          accM *ᵥ ⇑(eV j) = c • ⇑(eV j) →
          ((l.map fun b => if b then M else IM).foldl (· * ·) accM) *ᵥ ⇑(eV j) =
            (c * (((lam j) ^ (l.count true) * (1 -
              lam j) ^ (l.count false) : ℝ) : ℂ)) • ⇑(eV j) by
        simpa using hgen 1 1 (by simp)
      induction l with
      | nil => intro accM c hacc; simpa using hacc
      | cons b l ih =>
        intro accM c hacc
        simp only [List.map_cons, List.foldl_cons]
        have hstep : (accM * (if b then M else IM)) *ᵥ ⇑(eV j) =
            (c * if b then (lam j : ℂ) else ((1 - lam j : ℝ) : ℂ)) • ⇑(eV j) := by
          rw [← Matrix.mulVec_mulVec]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, hIM_eig, Matrix.mulVec_smul, hacc,
              smul_smul, mul_comm c]
          · simp only [↓reduceIte, heig j, Matrix.mulVec_smul, hacc, smul_smul, mul_comm c]
        rw [ih _ _ hstep]
        cases b <;> simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
    have hlist := hfold (List.ofFn z)
    have hmap : (List.ofFn z).map (fun b => if b then M else IM) =
        List.ofFn fun r : Fin T => if z r then M else IM := by rw [List.map_ofFn]; rfl
    have hct : (List.ofFn z).count true = weight z := by rw [List.count_ofFn]; rfl
    have hcf : (List.ofFn z).count false = T - weight z := by
      rw [List.count_ofFn]
      simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight z
    simpa only [hmap, hct, hcf] using hlist
  have htr_z : ∀ z : BitString T,
      ((List.ofFn fun r : Fin T => if z r then M else IM).foldl (· * ·) 1).trace =
        ∑ j : BitString w, (((lam j) ^ weight z * (1 - lam j) ^ (T - weight z) : ℝ) : ℂ) := by
    intro z
    let Q : Matrix (BitString w) (BitString w) ℂ := Matrix.of fun u j => (eV j).ofLp u
    have hQu : Qᴴ * Q = 1 := by
      ext i j; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
        Matrix.one_apply]
      have hi : inner ℂ (eV i) (eV j) = ∑ u, star ((eV i).ofLp u) * (eV j).ofLp u := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
      rw [← hi]; by_cases hij : i = j
      · subst hij; simp [eV.orthonormal.1 i]
      · simp [hij, eV.orthonormal.2 hij]
    have hQu' : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQu
    let A : Matrix (BitString w) (BitString w) ℂ :=
      (List.ofFn fun r : Fin T => if z r then M else IM).foldl (· * ·) 1
    have htr_cyc : A.trace = (Qᴴ * A * Q).trace := by
      rw [Matrix.trace_mul_cycle Qᴴ A Q, hQu', Matrix.one_mul]
    change A.trace = _
    rw [htr_cyc]
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hmul : (Qᴴ * A * Q) j j = dotProduct (star ⇑(eV j)) (A *ᵥ ⇑(eV j)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [hmul, hprod_eig z j, dotProduct_smul, smul_eq_mul]
    have h1 : dotProduct (star ⇑(eV j)) ⇑(eV j) = 1 := by
      have hnorm : inner ℂ (eV j) (eV j) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, eV.orthonormal.1 j, RCLike.ofReal_one, one_pow]
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hnorm
      exact hnorm
    rw [h1, mul_one]
  simp_rw [htr_z]; rw [Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => by rw [Complex.re_sum]; simp only [Complex.ofReal_re]

/-- **Amplified QMA Communication Factorization**:
given a `w`-qubit, `c`-qubit QMA communication protocol `P` computing `F` with completeness and
soundness error `1 / 3` and any `δ ∈ (0, 1 / 4]`, there exist a real matrix `Pmat` and real
factorization `Pmat = A * B` such that:
- `F (x, y) = true → (1 - δ) * 2^{-w} ≤ Pmat x y ∧ Pmat x y ≤ 1`,
- `F (x, y) = false → 0 ≤ Pmat x y ∧ Pmat x y ≤ δ`,
- `‖A‖_F * ‖B‖_F ≤ 4^{c'} * √(|X| * |Y|)`, where `c' = 0` if `c = 0` and
  `c' ≤ 2 * c * (⌈288 * log(1 / δ)⌉₊ + 1)` if `c ≥ 1` (zero dependence on shared entanglement
  dimension). -/
theorem qma_comm_amplified_factorization (P : QuantumCommProtocol X Y w)
    {F : X × Y → Bool} (hP : P.Computes F (1 / 3) (1 / 3))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (c' : ℕ) (Pmat : Matrix X Y ℝ) (Z : Type) (_ : Fintype Z)
      (A : Matrix X Z ℝ) (B : Matrix Z Y ℝ),
      (P.comm = 0 → c' = 0) ∧
      c' ≤ 2 * P.comm * (⌈288 * Real.log (1 / δ)⌉₊ + 1) ∧
      A * B = Pmat ∧
      frobeniusNorm A * frobeniusNorm B ≤
        (4 : ℝ) ^ c' * Real.sqrt (Fintype.card X * Fintype.card Y) ∧
      (∀ x y, F (x, y) = true → (1 - δ) * (2 : ℝ) ^ (-(w : ℤ)) ≤ Pmat x y ∧ Pmat x y ≤ 1) ∧
      (∀ x y, F (x, y) = false → 0 ≤ Pmat x y ∧ Pmat x y ≤ δ) := by
  classical
  obtain ⟨T₀, _, R, Smat, hR, hS, hM, hIM, hcomm0⟩ := exists_schmidt_operator_factorization P
  set T : ℕ := ⌈288 * Real.log (1 / δ)⌉₊ + 1
  have hT_exp : Real.exp (-(T : ℝ) / 288) ≤ δ := by
    have hlog : Real.log (1 / δ) ≤ (T : ℝ) / 288 := by
      have hc : 288 * Real.log (1 / δ) ≤ (⌈288 * Real.log (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
      have hT1 : (⌈288 * Real.log (1 / δ)⌉₊ : ℝ) ≤ (T : ℝ) := by simp only [T]; push_cast; linarith
      linarith
    calc Real.exp (-(T : ℝ) / 288) ≤ Real.exp (-Real.log (1 / δ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ0]
  let Mmat (x : X) (y : Y) : Matrix (BitString w) (BitString w) ℂ :=
    Matrix.of fun u v => ∑ t : T₀, R x t * Smat y true t u v
  let IMmat (x : X) (y : Y) : Matrix (BitString w) (BitString w) ℂ :=
    Matrix.of fun u v => ∑ t : T₀, R x t * Smat y false t u v
  have hM_herm : ∀ x y, (Mmat x y).IsHermitian := by
    intro x y; ext u v
    simp only [Matrix.conjTranspose_apply, Mmat, Matrix.of_apply, ← hM x y]
    have hsymm : ∀ a b : EuclideanSpace ℂ P.Joint,
        inner ℂ a (WithLp.toLp 2 fun p => if (p.1.2, p.2) ∈ P.accept then b.ofLp p else 0) =
        inner ℂ (WithLp.toLp 2 fun p => if (p.1.2, p.2) ∈ P.accept then a.ofLp p else 0) b := by
      intro a b; simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
      refine Finset.sum_congr rfl fun p _ => ?_; split_ifs <;> simp
    rw [hsymm, ← inner_conj_symm]; simp [hsymm]
  have hM_plus_IM : ∀ x y, Mmat x y + IMmat x y = 1 := by
    intro x y; ext u v
    simp only [Matrix.add_apply, Mmat, IMmat, Matrix.of_apply, ← hM x y, ← hIM x y,
      ← inner_add_right]
    have hsum : (WithLp.toLp 2 fun p : P.Joint => if (p.1.2, p.2) ∈ P.accept then
          (P.finalState x y (WithLp.toLp 2 fun a => if a = v then 1 else 0)).ofLp p else 0) +
        (WithLp.toLp 2 fun p : P.Joint => if (p.1.2, p.2) ∉ P.accept then
          (P.finalState x y (WithLp.toLp 2 fun a => if a = v then 1 else 0)).ofLp p else 0) =
        P.finalState x y (WithLp.toLp 2 fun a => if a = v then 1 else 0) := by
      ext p; simp only [PiLp.add_apply]
      by_cases h : (p.1.2, p.2) ∈ P.accept <;> simp [h]
    rw [hsum, P.inner_finalState]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single u (fun a _ ha => by simp [ha]) (by simp)]
    by_cases huv : u = v <;> simp [huv]
  let prodMat (x : X) (y : Y) (z : BitString T) : Matrix (BitString w) (BitString w) ℂ :=
    (List.ofFn fun r : Fin T => if z r then Mmat x y else IMmat x y).foldl (· * ·) 1
  let Pmat : Matrix X Y ℝ := Matrix.of fun x y =>
    (2 : ℝ) ^ (-(w : ℤ)) *
      (∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ), (prodMat x y z).trace).re
  -- Linearity of `P.finalState` in `ψ` for the quadratic-form identity.
  have hfinal_lin : ∀ (x : X) (y : Y) (ψ : EuclideanSpace ℂ (BitString w)),
      P.finalState x y ψ = ∑ u : BitString w,
        ψ.ofLp u • P.finalState x y (WithLp.toLp 2 fun a => if a = u then 1 else 0) := by
    intro x y ψ
    have hadd : ∀ a b, P.finalState x y (a + b) = P.finalState x y a + P.finalState x y b :=
      P.finalState_add x y
    have hsm : ∀ (c : ℂ) a, P.finalState x y (c • a) = c • P.finalState x y a :=
      P.finalState_smul x y
    have hψ : ψ = ∑ u : BitString w, ψ.ofLp u • (WithLp.toLp 2 fun a => if a =
      u then 1 else 0) := by
      ext a; simp [Finset.sum_apply]
    have hlin : ∀ (S_fin : Finset (BitString w)),
        P.finalState x y (∑ u ∈ S_fin, ψ.ofLp u • (WithLp.toLp 2 fun a => if a = u then 1 else 0)) =
        ∑ u ∈ S_fin, ψ.ofLp u • P.finalState x y (WithLp.toLp 2 fun a => if a =
          u then 1 else 0) := by
      intro S_fin; induction S_fin using Finset.induction_on with
      | empty => simpa using hsm 0 0
      | insert a S_fin ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsm, ih]
    conv_lhs => rw [hψ]
    exact hlin Finset.univ
  have hPmat_spectral : ∀ x y,
      ∃ (eV : OrthonormalBasis (BitString w) ℂ (EuclideanSpace ℂ (BitString w)))
        (lam : BitString w → ℝ),
        (∀ j, lam j = P.acceptProb x y (eV j)) ∧
        (∀ ψ : EuclideanSpace ℂ (BitString w),
          P.acceptProb x y ψ = ∑ j : BitString w, ‖inner ℂ (eV j) ψ‖ ^ 2 * lam j) ∧
        Pmat x y = (2 : ℝ) ^ (-(w : ℤ)) * ∑ j : BitString w,
          ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
            (lam j) ^ weight z * (1 - lam j) ^ (T - weight z) := by
    intro x y
    have hM_quad : ∀ ψ : EuclideanSpace ℂ (BitString w),
        dotProduct (star ⇑ψ) (Mmat x y *ᵥ ⇑ψ) = (P.acceptProb x y ψ : ℂ) := by
      intro ψ
      have hinner : dotProduct (star ⇑ψ) (Mmat x y *ᵥ ⇑ψ) =
          inner ℂ (P.finalState x y ψ)
            (WithLp.toLp 2 fun p => if (p.1.2,
              p.2) ∈ P.accept then (P.finalState x y ψ).ofLp p else 0) := by
        rw [hfinal_lin x y ψ, sum_inner]
        simp only [dotProduct, Matrix.mulVec, Mmat, Matrix.of_apply, Pi.star_apply,
          Complex.star_def, Finset.mul_sum, ← hM x y]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [inner_smul_left]
        have hacc_sum : (WithLp.toLp 2 fun p : P.Joint => if (p.1.2, p.2) ∈ P.accept then
              (∑ v' : BitString w, ψ.ofLp v' • P.finalState x y (WithLp.toLp 2 fun a => if a =
                v' then 1 else 0)).ofLp p else 0) =
            ∑ v' : BitString w, ψ.ofLp v' • (WithLp.toLp 2 fun p : P.Joint => if (p.1.2,
              p.2) ∈ P.accept then
              (P.finalState x y (WithLp.toLp 2 fun a => if a =
                v' then 1 else 0)).ofLp p else 0) := by
          ext p; simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
          split_ifs <;> simp
        rw [hacc_sum, inner_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v' _ => by rw [inner_smul_right]; ring
      rw [hinner, P.acceptProb_eq_sum_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
        Finset.sum_filter, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs
      · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp
    obtain ⟨hlam_eq, hspec, htr_eq⟩ := hermitian_majority_trace_spectral (T := T)
      (Mmat x y) (IMmat x y) (hM_herm x y) (hM_plus_IM x y) (P.acceptProb x y) hM_quad
    exact ⟨(hM_herm x y).eigenvectorBasis, (hM_herm x y).eigenvalues, hlam_eq, hspec, by
      simp only [Pmat, Matrix.of_apply, prodMat, htr_eq]⟩
  -- Completeness and soundness bounds on `Pmat x y`.
  have hPmat_yes : ∀ x y, F (x, y) = true →
      (1 - δ) * (2 : ℝ) ^ (-(w : ℤ)) ≤ Pmat x y ∧ Pmat x y ≤ 1 := by
    intro x y hxy
    obtain ⟨ψ₀, hψ₀, hacc₀⟩ := hP.1 x y hxy
    obtain ⟨eV, lam, hlam, hspec, hPmateq⟩ := hPmat_spectral x y
    have hlam01 : ∀ j, 0 ≤ lam j ∧ lam j ≤ 1 := fun j =>
      ⟨hlam j ▸ P.acceptProb_nonneg x y (eV j),
        hlam j ▸ P.acceptProb_le_one x y (eV.orthonormal.1 j)⟩
    have hex_j : ∃ j₀ : BitString w, 2 / 3 ≤ lam j₀ := by
      by_contra hall; push Not at hall
      have hsum1 : ∑ j : BitString w, ‖inner ℂ (eV j) ψ₀‖ ^ 2 = 1 := by
        have := eV.sum_sq_norm_inner_right ψ₀; rwa [hψ₀, one_pow] at this
      have hlt : ∑ j : BitString w, ‖inner ℂ (eV j) ψ₀‖ ^ 2 * lam j < 2 / 3 := by
        have hexp : ∃ j₁, 0 < ‖inner ℂ (eV j₁) ψ₀‖ ^ 2 := by
          by_contra h0; push Not at h0
          have : ∑ j, ‖inner ℂ (eV j) ψ₀‖ ^ 2 = 0 :=
            Finset.sum_eq_zero fun j _ => le_antisymm (h0 j) (sq_nonneg _)
          linarith
        obtain ⟨j₁, hj₁⟩ := hexp
        calc ∑ j, ‖inner ℂ (eV j) ψ₀‖ ^ 2 * lam j
            < ∑ j, ‖inner ℂ (eV j) ψ₀‖ ^ 2 * (2 / 3) :=
              Finset.sum_lt_sum
                (fun j _ => mul_le_mul_of_nonneg_left (le_of_lt (hall j)) (sq_nonneg _))
                ⟨j₁, Finset.mem_univ _, mul_lt_mul_of_pos_left (hall j₁) hj₁⟩
          _ = 2 / 3 := by rw [← Finset.sum_mul, hsum1, one_mul]
      rw [← hspec ψ₀] at hlt; linarith
    obtain ⟨j₀, hj₀⟩ := hex_j
    rw [hPmateq]
    constructor
    · rw [mul_comm (1 - δ)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsingle : ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
            (lam j₀) ^ weight z * (1 - lam j₀) ^ (T - weight z) ≤
          ∑ j : BitString w, ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
            (lam j) ^ weight z * (1 - lam j) ^ (T - weight z) :=
        Finset.single_le_sum
          (f := fun j : BitString w => ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
            (lam j) ^ weight z * (1 - lam j) ^ (T - weight z))
          (fun j _ => Finset.sum_nonneg fun z _ =>
            mul_nonneg (pow_nonneg (hlam01 j).1 _) (pow_nonneg (by linarith [(hlam01 j).2]) _))
          (Finset.mem_univ j₀)
      have hge := bernoulli_majority_lower (T := T) hj₀ (hlam01 j₀).2
      linarith
    · have hsum_le : ∑ j : BitString w, ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
          (lam j) ^ weight z * (1 - lam j) ^ (T - weight z) ≤ (2 : ℝ) ^ w := by
        calc ∑ j : BitString w, ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
              (lam j) ^ weight z * (1 - lam j) ^ (T - weight z)
            ≤ ∑ _j : BitString w, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
              (Finset.sum_le_univ_sum_of_nonneg (f := fun z : BitString T =>
                (lam j) ^ weight z * (1 - lam j) ^ (T - weight z)) fun z =>
                mul_nonneg (pow_nonneg (hlam01 j).1 _)
                  (pow_nonneg (by linarith [(hlam01 j).2]) _)).trans_eq
                (bernoulli_sum_eq_one (T := T) (lam j))
          _ = (2 : ℝ) ^ w := by simp
      rw [_root_.zpow_neg, zpow_natCast, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w),
        mul_one]
      exact hsum_le
  have hPmat_no : ∀ x y, F (x, y) = false → 0 ≤ Pmat x y ∧ Pmat x y ≤ δ := by
    intro x y hxy
    obtain ⟨eV, lam, hlam, _, hPmateq⟩ := hPmat_spectral x y
    rw [hPmateq]
    have hlam0 : ∀ j, 0 ≤ lam j := fun j => hlam j ▸ P.acceptProb_nonneg x y (eV j)
    have hlam13 : ∀ j, lam j ≤ 1 / 3 := fun j => hlam j ▸ hP.2 x y hxy (eV j) (eV.orthonormal.1 j)
    constructor
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun z _ =>
        mul_nonneg (pow_nonneg (hlam0 j) _) (pow_nonneg (by linarith [hlam13 j]) _))
    · have hsum_le : ∑ j : BitString w, ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
          (lam j) ^ weight z * (1 - lam j) ^ (T - weight z) ≤ (2 : ℝ) ^ w * δ := by
        calc ∑ j : BitString w, ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
              (lam j) ^ weight z * (1 - lam j) ^ (T - weight z)
            ≤ ∑ _j : BitString w, δ := Finset.sum_le_sum fun j _ =>
              (bernoulli_majority_tail (hlam0 j) (hlam13 j)).trans hT_exp
          _ = (2 : ℝ) ^ w * δ := by simp
      rw [_root_.zpow_neg, zpow_natCast, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w)]
      exact hsum_le
  -- Now construct the real factorization `A * B = Pmat`!
  by_cases hc0 : P.comm = 0
  · -- Zero communication: `Pmat x y` is independent of `x`!
    have hPmat_indep : ∀ x₁ x₂ y, Pmat x₁ y = Pmat x₂ y := by
      intro x₁ x₂ y
      have hMeq : Mmat x₁ y = Mmat x₂ y := by ext u v; exact hcomm0 hc0 x₁ x₂ y u v
      have hIMeq : IMmat x₁ y = IMmat x₂ y := by
        have h1 := hM_plus_IM x₁ y; have h2 := hM_plus_IM x₂ y
        rw [hMeq] at h1
        have := congrArg (fun M => M - Mmat x₂ y) (h1.trans h2.symm)
        simpa using this
      simp only [Pmat, Matrix.of_apply, prodMat, hMeq, hIMeq]
    by_cases hX : Nonempty X
    · obtain ⟨x₀⟩ := hX
      let A : Matrix X Unit ℝ := Matrix.of fun _ _ => 1
      let B : Matrix Unit Y ℝ := Matrix.of fun _ y => Pmat x₀ y
      refine ⟨0, Pmat, Unit, inferInstance, A, B, fun _ => rfl, Nat.zero_le _, ?_, ?_, hPmat_yes,
        hPmat_no⟩
      · ext x y; simp [Matrix.mul_apply, A, B, hPmat_indep x x₀ y]
      · have hA : frobeniusNorm A = Real.sqrt (Fintype.card X) := by
          simp [frobeniusNorm_eq_sqrt_sum, A]
        have hB : frobeniusNorm B ≤ Real.sqrt (Fintype.card Y) := by
          have h01 : ∀ y, 0 ≤ Pmat x₀ y ∧ Pmat x₀ y ≤ 1 := fun y => by
            cases hF : F (x₀, y)
            · have := hPmat_no x₀ y hF; exact ⟨this.1, this.2.trans (by linarith)⟩
            · have := hPmat_yes x₀ y hF
              exact ⟨le_trans (mul_nonneg (by linarith) (by positivity)) this.1, this.2⟩
          have hsq : frobeniusNorm B ^ 2 ≤ (Real.sqrt (Fintype.card Y)) ^ 2 := by
            rw [sq_frobeniusNorm, Real.sq_sqrt (Nat.cast_nonneg _)]
            calc ∑ _u : Unit, ∑ y : Y, B _u y ^ 2
                = ∑ y : Y, Pmat x₀ y ^ 2 := by simp [B]
              _ ≤ ∑ _y : Y, (1 : ℝ) := Finset.sum_le_sum fun y _ => by nlinarith [h01 y]
              _ = Fintype.card Y := by simp
          exact (sq_le_sq₀ (frobeniusNorm_nonneg B) (Real.sqrt_nonneg _)).mp hsq
        rw [pow_zero, one_mul, Real.sqrt_mul (Nat.cast_nonneg _), hA]
        exact mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
    · have : IsEmpty X := not_nonempty_iff.mp hX
      refine ⟨0, Pmat, Empty, inferInstance, 0, 0, fun _ => rfl, Nat.zero_le _, ?_, ?_, hPmat_yes,
        hPmat_no⟩
      · ext x; exact IsEmpty.elim ‹IsEmpty X› x
      · simp [frobeniusNorm_zero]
  · -- Positive communication `P.comm ≥ 1`: `T`-fold factorization with `c' = 2 * P.comm * T`.
    have hcpos : 1 ≤ P.comm := Nat.pos_of_ne_zero hc0
    let c' := 2 * P.comm * T
    let Aℂ : X → (Fin T → T₀) → ℂ := fun x t => ∏ r : Fin T, R x (t r)
    let Bℂ : (Fin T → T₀) → Y → ℂ := fun t y =>
      ((2 : ℝ) ^ (-(w : ℤ)) : ℂ) * ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ),
        ((List.ofFn fun r : Fin T => Smat y (z r) (t r)).foldl (· * ·) 1).trace
    let A : Matrix X ((Fin T → T₀) × Bool) ℝ := Matrix.of fun x tb =>
      if tb.2 then -(Aℂ x tb.1).im else (Aℂ x tb.1).re
    let B : Matrix ((Fin T → T₀) × Bool) Y ℝ := Matrix.of fun tb y =>
      if tb.2 then (Bℂ tb.1 y).im else (Bℂ tb.1 y).re
    refine ⟨c', Pmat, (Fin T → T₀) × Bool, inferInstance, A, B, fun h => absurd h hc0, le_rfl,
      ?_, ?_, hPmat_yes, hPmat_no⟩
    · ext x y
      have hPmat_complex : (∑ t : Fin T → T₀, Aℂ x t * Bℂ t y).re = Pmat x y := by
        have hsum_eq : ∑ t : Fin T → T₀, Aℂ x t * Bℂ t y =
            ((2 : ℝ) ^ (-(w : ℤ)) : ℂ) *
              ∑ z : BitString T with (T : ℝ) / 2 ≤ (weight z : ℝ), (prodMat x y z).trace := by
          simp_rw [Bℂ, ← mul_assoc, mul_comm (Aℂ x _), mul_assoc, ← Finset.mul_sum]
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z _ => ?_
          have hprod : prodMat x y z =
              ∑ t : Fin T → T₀, (Aℂ x t) •
                (List.ofFn fun r : Fin T => Smat y (z r) (t r)).foldl (· * ·) 1 := by
            have h := foldl_mul_sum_eq T (R x) (fun r t => Smat y (z r) t)
            have hlhs : (List.ofFn fun r : Fin T => ∑ t : T₀, R x t • Smat y (z r) t) =
                List.ofFn fun r : Fin T => if z r then Mmat x y else IMmat x y := by
              refine congrArg List.ofFn (funext fun r => ?_)
              ext u v
              cases z r <;> simp [Mmat, IMmat]
            rw [hlhs] at h; exact h
          rw [hprod]
          simp only [Matrix.trace, Matrix.diag_apply, Matrix.sum_apply, Matrix.smul_apply,
            smul_eq_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => by rw [← Finset.mul_sum, mul_comm]
        rw [hsum_eq, ← Complex.ofReal_zpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        rfl
      rw [← hPmat_complex, Complex.re_sum]
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, A, B, Matrix.of_apply,
        ↓reduceIte, Bool.false_eq_true, Complex.mul_re]
      refine Finset.sum_congr rfl fun t _ => by ring
    · -- Bound `‖A‖_F * ‖B‖_F ≤ 4^{2 * P.comm * T} * √(|X| * |Y|)`!
      have hA_sq : frobeniusNorm A ^ 2 ≤ (4 : ℝ) ^ (P.comm * T) * Fintype.card X := by
        rw [sq_frobeniusNorm]
        calc ∑ x : X, ∑ tb : (Fin T → T₀) × Bool, A x tb ^ 2
            = ∑ x : X, ∑ t : Fin T → T₀, ‖Aℂ x t‖ ^ 2 := by
              refine Finset.sum_congr rfl fun x _ => ?_
              simp only [Fintype.sum_prod_type, Fintype.sum_bool, A, Matrix.of_apply,
                ↓reduceIte, Bool.false_eq_true]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [Complex.sq_norm, Complex.normSq_apply]; ring
          _ = ∑ x : X, (∑ t₀ : T₀, ‖R x t₀‖ ^ 2) ^ T := by
              refine Finset.sum_congr rfl fun x _ => ?_
              have hprod : ∀ t : Fin T → T₀, ‖Aℂ x t‖ ^ 2 = ∏ r : Fin T, ‖R x (t r)‖ ^ 2 :=
                fun t => by
                simp only [Aℂ, norm_prod, Finset.prod_pow]
              simp_rw [hprod]
              rw [← Fintype.prod_sum (fun (_ : Fin T) (t₀ : T₀) => ‖R x t₀‖ ^ 2)]
              simp
          _ ≤ ∑ _x : X, ((4 : ℝ) ^ P.comm) ^ T :=
              Finset.sum_le_sum fun x _ =>
                pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hR x) T
          _ = (4 : ℝ) ^ (P.comm * T) * Fintype.card X := by rw [← pow_mul]; simp [mul_comm]
      have hB_sq : frobeniusNorm B ^ 2 ≤ (4 : ℝ) ^ ((P.comm + 1) * T) * Fintype.card Y := by
        rw [sq_frobeniusNorm]
        calc ∑ tb : (Fin T → T₀) × Bool, ∑ y : Y, B tb y ^ 2
            = ∑ y : Y, ∑ t : Fin T → T₀, ‖Bℂ t y‖ ^ 2 := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun y _ => ?_
              simp only [Fintype.sum_prod_type, Fintype.sum_bool, B, Matrix.of_apply,
                ↓reduceIte, Bool.false_eq_true]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [Complex.sq_norm, Complex.normSq_apply]; ring
          _ ≤ ∑ y : Y, (4 : ℝ) ^ ((P.comm + 1) * T) :=
              Finset.sum_le_sum fun y _ => qma_comm_B_col_sq_le (Smat y) (hS y)
          _ = (4 : ℝ) ^ ((P.comm + 1) * T) * Fintype.card Y := by simp [mul_comm]
      have hprod_sq : (frobeniusNorm A * frobeniusNorm B) ^ 2 ≤
          ((4 : ℝ) ^ c' * Real.sqrt (Fintype.card X * Fintype.card Y)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have h4 : (4 : ℝ) ^ (P.comm * T) * (4 : ℝ) ^ ((P.comm + 1) * T) ≤ ((4 : ℝ) ^ c') ^ 2 := by
          rw [← pow_add, ← pow_mul]
          refine pow_le_pow_right₀ (by norm_num) ?_
          simp only [c']; nlinarith
        calc frobeniusNorm A ^ 2 * frobeniusNorm B ^ 2
            ≤ ((4 : ℝ) ^ (P.comm * T) * Fintype.card X) *
                ((4 : ℝ) ^ ((P.comm + 1) * T) * Fintype.card Y) :=
              mul_le_mul hA_sq hB_sq (sq_nonneg _) (by positivity)
          _ = ((4 : ℝ) ^ (P.comm * T) * (4 : ℝ) ^ ((P.comm + 1) * T)) *
                (Fintype.card X * Fintype.card Y) := by ring
          _ ≤ ((4 : ℝ) ^ c') ^ 2 * (Fintype.card X * Fintype.card Y) :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
      exact (sq_le_sq₀ (mul_nonneg (frobeniusNorm_nonneg A) (frobeniusNorm_nonneg B))
        (by positivity)).mp hprod_sq

end Amplification

end CslibFrontier.CommunicationComplexity
