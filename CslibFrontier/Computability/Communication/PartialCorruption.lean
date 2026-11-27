/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Distributional
public import CslibFrontier.Computability.Communication.Rectangle
import CslibFrontier.Probability.PMF.Event
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Threshold Corruption Lower Bound for Partial Boolean Functions

Yao's threshold-$\delta$ corruption method
 lower-bounds the public-coin randomized
communication complexity of a partial (promise) Boolean function `f : X → Y → Option Bool`. Unlike
total-function corruption (`Cslib.Communication.Corrupted`), promise inputs allow arbitrary protocol
outputs outside `dom(f)` (`f x y = none`) with zero error penalty, while rectangle corruption is
required only on rectangles `A × B` whose total mass under a hard distribution `ν` exceeds `δ`:
`γ · ν((A × B) ∩ f⁻¹(false)) ≤ ν((A × B) ∩ f⁻¹(true))`.

## Main definitions

* `CslibFrontier.Communication.partialBoolRel`: relational promise specification of
  `f : X → Y → Option Bool`.
* `CslibFrontier.Communication.ThresholdCorrupted`: threshold-$\delta$ rectangle corruption for
  partial Boolean functions.

## Main results

* `CslibFrontier.Communication.ThresholdCorrupted.partial_corruption_protocol`: deterministic
  distributional lower bound `(1 / δ) (ν(f⁻¹(false)) - err / γ) ≤ 2 ^ P.depth`.
* `CslibFrontier.Communication.ThresholdCorrupted.partial_corruption_ecomplexity`: public-coin
  randomized communication lower bound `(1 / δ) (ν(f⁻¹(false)) - ε / γ) ≤ 2 ^ c`.
-/

public section

namespace CslibFrontier.Communication

open Finset Cslib.Communication

/-- Promise relation associated with a partial Boolean function `f : X → Y → Option Bool`:
whenever `f x y = some b`, a valid output `z` must equal `b`; when `f x y = none`, every output is
permitted. -/
def partialBoolRel {X Y : Type*} (f : X → Y → Option Bool) (x : X) (y : Y) (z : Bool) : Prop :=
  ∀ b, f x y = some b → z = b

@[simp]
theorem partialBoolRel_some {X Y : Type*} (g : X → Y → Bool) (x : X) (y : Y) (z : Bool) :
    partialBoolRel (fun x' y' ↦ some (g x' y')) x y z ↔ g x y = z := by
  simp [partialBoolRel, eq_comm]

/-- A partial Boolean function `f` is `(γ, δ)`-*threshold-corrupted* under `ν` when every
combinatorial rectangle `A × B` of `ν`-mass strictly greater than `δ` has `1`-fiber mass at least
`γ` times its `0`-fiber mass. -/
def ThresholdCorrupted {X Y : Type*} (ν : PMF (X × Y)) (f : X → Y → Option Bool)
    (γ δ : ℝ) : Prop :=
  ∀ (A : Finset X) (B : Finset Y),
    δ < (∑ x ∈ A, ∑ y ∈ B, (ν (x, y)).toReal) →
      γ * (∑ x ∈ A, ∑ y ∈ B, if f x y = some false then (ν (x, y)).toReal else 0) ≤
        ∑ x ∈ A, ∑ y ∈ B, if f x y = some true then (ν (x, y)).toReal else 0

namespace ThresholdCorrupted

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Deterministic distributional corruption lower bound for partial Boolean functions. -/
theorem partial_corruption_protocol {ν : PMF (X × Y)} {f : X → Y → Option Bool}
    {γ δ ε : ℝ} (hcorr : ThresholdCorrupted ν f γ δ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (P : Protocol X Y Bool) (herr : P.distributionalError ν (partialBoolRel f) ≤ ε) :
    (1 / δ) *
      ((∑ x : X, ∑ y : Y, if f x y = some false then (ν (x, y)).toReal else 0) - ε / γ) ≤
      (2 : ℝ) ^ P.depth := by
  classical
  let μ : X → Y → ℝ := fun x y ↦ (ν (x, y)).toReal
  have hμ_nn (x : X) (y : Y) : 0 ≤ μ x y := ENNReal.toReal_nonneg
  let w : X → Y → ℝ := fun x y ↦
    (if f x y = some false then μ x y else 0) -
      (1 / γ) * (if f x y = some true then μ x y else 0)
  have hleaf : ∀ (i : Fin P.leafCount), P.leafOutput i = false →
      ∑ x ∈ univ.filter (· ∈ P.leafAlice i),
        ∑ y ∈ univ.filter (· ∈ P.leafBob i), w x y ≤ δ := by
    intro i _
    let A := univ.filter (· ∈ P.leafAlice i)
    let B := univ.filter (· ∈ P.leafBob i)
    change ∑ x ∈ A, ∑ y ∈ B, w x y ≤ δ
    simp only [w, sum_sub_distrib, ← mul_sum]
    by_cases hbig : δ < ∑ x ∈ A, ∑ y ∈ B, μ x y
    · have hc := hcorr A B hbig
      have hdiv : (∑ x ∈ A, ∑ y ∈ B, if f x y = some false then μ x y else 0) ≤
          (1 / γ) * ∑ x ∈ A, ∑ y ∈ B, if f x y = some true then μ x y else 0 := by
        rw [one_div, le_inv_mul_iff₀ hγ0]; exact hc
      linarith
    · push Not at hbig
      have h0_le : (∑ x ∈ A, ∑ y ∈ B, if f x y = some false then μ x y else 0) ≤ δ := by
        refine (sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_).trans hbig
        split_ifs
        · exact le_rfl
        · exact hμ_nn x y
      have h1_nn : 0 ≤ (1 / γ) * ∑ x ∈ A, ∑ y ∈ B, if f x y = some true then μ x y else 0 :=
        mul_nonneg (by positivity)
          (sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦ by
            split_ifs <;> [exact hμ_nn x y; exact le_rfl])
      linarith
  have hsum := P.sum_filter_run_le_mul false w (K := δ) hleaf
  have hleaves : (#(univ.filter fun i ↦ P.leafOutput i = false) : ℝ) * δ ≤
      (2 : ℝ) ^ P.depth * δ := by
    refine mul_le_mul_of_nonneg_right ?_ hδ.le
    exact_mod_cast (card_le_univ _).trans (by simpa using P.leafCount_le_two_pow_depth)
  set E := P.distributionalError ν (partialBoolRel f)
  have hE_eq : E = ∑ q : X × Y,
      if partialBoolRel f q.1 q.2 (P.run q.1 q.2) then 0 else μ q.1 q.2 :=
    Cslib.Probability.PMF.errorProb_eq_sum _ ν P
  let E₀ : ℝ := ∑ q : X × Y,
    if f q.1 q.2 = some false ∧ P.run q.1 q.2 = true then μ q.1 q.2 else 0
  let E₁ : ℝ := ∑ q : X × Y,
    if f q.1 q.2 = some true ∧ P.run q.1 q.2 = false then μ q.1 q.2 else 0
  have hE₀_nn : 0 ≤ E₀ := sum_nonneg fun q _ ↦ by
    split_ifs <;> [exact hμ_nn _ _; exact le_rfl]
  have hE_split : E₀ + E₁ ≤ E := by
    rw [hE_eq]; dsimp [E₀, E₁]; rw [← sum_add_distrib]
    refine sum_le_sum fun q _ ↦ ?_
    cases hfq : f q.1 q.2 with
    | none => simp [partialBoolRel, hfq]
    | some b =>
      cases b <;> cases P.run q.1 q.2 <;>
        simp [partialBoolRel, hfq]
  have hfalse_split :
      (∑ x : X, ∑ y : Y, if f x y = some false then μ x y else 0) =
        (∑ q : X × Y,
          if P.run q.1 q.2 = false ∧ f q.1 q.2 = some false then μ q.1 q.2 else 0) + E₀ := by
    rw [← Fintype.sum_prod_type' fun x y ↦ if f x y = some false then μ x y else 0]
    dsimp [E₀]; rw [← sum_add_distrib]
    refine sum_congr rfl fun q _ ↦ ?_
    cases P.run q.1 q.2 <;> by_cases hf0 : f q.1 q.2 = some false <;>
      simp [hf0]
  have hw_eq :
      (∑ q ∈ univ.filter (fun q : X × Y ↦ P.run q.1 q.2 = false), w q.1 q.2) =
        ((∑ x : X, ∑ y : Y, if f x y = some false then μ x y else 0) - E₀) - (1 / γ) * E₁ := by
    rw [sum_filter]; dsimp [w, E₁]
    have hrew :
        (∑ q : X × Y,
          if P.run q.1 q.2 = false then
            (if f q.1 q.2 = some false then μ q.1 q.2 else 0) -
              (1 / γ) * (if f q.1 q.2 = some true then μ q.1 q.2 else 0)
          else 0) =
        (∑ q : X × Y,
          if P.run q.1 q.2 = false ∧ f q.1 q.2 = some false then μ q.1 q.2 else 0) -
          (1 / γ) * ∑ q : X × Y,
            if f q.1 q.2 = some true ∧ P.run q.1 q.2 = false then μ q.1 q.2 else 0 := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun q _ ↦ ?_
      by_cases hr : P.run q.1 q.2 = false <;>
        by_cases hf0 : f q.1 q.2 = some false <;>
        by_cases hf1 : f q.1 q.2 = some true <;>
        simp [hr, hf0, hf1]
    rw [hrew]; linarith [hfalse_split]
  have hmain :
      (∑ x : X, ∑ y : Y, if f x y = some false then μ x y else 0) - ε / γ ≤
        (2 : ℝ) ^ P.depth * δ := by
    have hdiv_eq : (1 / γ) * (E₀ + E₁) ≤ (1 / γ) * ε :=
      mul_le_mul_of_nonneg_left (hE_split.trans herr) (by positivity)
    have h1_le_inv : 1 ≤ 1 / γ := (one_le_div hγ0).mpr hγ1
    have hE₀_scale : E₀ ≤ (1 / γ) * E₀ := by nlinarith
    have hε_eq : (1 / γ) * ε = ε / γ := one_div_mul_eq_div γ ε
    linarith [hsum, hleaves, hw_eq]
  rw [one_div, inv_mul_le_iff₀ hδ, mul_comm]
  exact hmain

/-- Public-coin randomized communication lower bound from threshold-$\delta$ corruption on a partial
Boolean function `f`. -/
theorem partial_corruption_ecomplexity {ν : PMF (X × Y)} {f : X → Y → Option Bool}
    {γ δ ε : ℝ} {c : ℕ} (hcorr : ThresholdCorrupted ν f γ δ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hc : PublicCoin.ecomplexity ε (partialBoolRel f) Set.univ Set.univ ≤ c) :
    (1 / δ) *
      ((∑ x : X, ∑ y : Y, if f x y = some false then (ν (x, y)).toReal else 0) - ε / γ) ≤
      (2 : ℝ) ^ c := by
  have hdc : Protocol.distributionalComplexity ε (partialBoolRel f) ν ≤ c :=
    (PublicCoin.distributionalComplexity_le_ecomplexity
      fun _ _ ↦ ⟨trivial, trivial⟩).trans hc
  obtain ⟨P, herr, hdepth⟩ := Protocol.distributionalComplexity_le_iff.mp hdc
  exact (hcorr.partial_corruption_protocol hγ0 hγ1 hδ P herr).trans
    (pow_le_pow_right₀ one_le_two hdepth)

end ThresholdCorrupted

end CslibFrontier.Communication
