/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.MultipartyOneWay
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.StatisticalDistance

import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiparty Set Disjointness Separation and Hellinger Cut-and-Paste Bound

This module formalizes `t`-party number-in-hand unique-intersection set disjointness and proves
both sides of the non-product player-count separation:

1. **Deterministic `(t - 1)`-player one-way upper bound (`≤ t - 1` bits)**: under any assignment of
   `t` subset indicators (`t ≥ 2`) to `t - 1` players, some player receives two distinct subsets by
   the pigeonhole principle and locally decides unique-intersection disjointness, forwarding a
   single bit along the one-way chain.
2. **Randomized `t`-player interactive lower bound (`Ω(m / t²)` bits)**: via discrete Hellinger
   cut-and-paste on `t`-dimensional product-rectangle leaf distributions, the elementary
   Jensen–Shannon / Hellinger inequality, and coordinatewise entropy subadditivity over random
   single-owner masks, every public-coin `t`-party NIH protocol solving `m`-bit unique-intersection
   set disjointness with error `δ < 1 / 2` uses `Ω((1 - 2 δ)² m / t²)` bits of communication.

## Main definitions

* `Cslib.Communication.multipartyDisjointness`: Boolean indicator testing whether `t`
  subsets of `Fin m` share a common element (`∃ j, ∀ i, x i j = true`).
* `Cslib.Communication.UniqueDisjointPromise`: unique-intersection promise requiring
  either pairwise disjointness (`∀ j, #{i | x i j} ≤ 1`) or a common element at one coordinate `j`
  with pairwise disjointness on all other coordinates `j' ≠ j`.
* `Cslib.Communication.hellingerSq`,
  `Cslib.Communication.hellingerDist`: discrete squared Hellinger distance and
  Hellinger metric on finite `PMF`s.

## Main results

* `Cslib.Communication.isSymmetricParty_multipartyDisjointness`: symmetry of
  `multipartyDisjointness` under player permutations.
* `Cslib.Communication.oneWay_pred_multipartyDisjointness_le`: under any map
  `assign : Fin t → Fin (t - 1)` (`t ≥ 2`), `(t - 1)`-player deterministic one-way communication on
  `UniqueDisjointPromise` is at most `t - 2` (hence at most `t - 1`).
* `Cslib.Communication.hellingerSq_allTrue_le_mul_sum_single`: cut-and-paste Hellinger
  bound `h²(P_0, P_1) ≤ t * ∑ r, h²(P_0, P_{e_r})` for `t`-party product-rectangle leaf laws.
* `Cslib.Communication.rcc_multipartyDisjointness_lower`: randomized `t`-party NIH
  lower bound `(1 - 2 * δ) ^ 2 * m ≤ 16 * Real.log 2 * t ^ 2 * c` for any protocol of cost `c` and
  error `δ ≤ 1 / 2` (`t ≥ 2`).
-/

public section

namespace Cslib.Communication

open Finset Cslib Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

/-! ### 1. Multiparty Unique-Intersection Set Disjointness and `(t - 1)`-Player Upper Bound -/

section DisjointnessProblem

/-- Boolean `t`-party set-intersection indicator on `BitString m`: returns `true` iff some
coordinate `j : Fin m` belongs to all `t` players' indicator vectors (`∀ i, x i j = true`). -/
def multipartyDisjointness {t m : ℕ} (x : Fin t → BitString m) : Bool :=
  decide (∃ j : Fin m, ∀ i : Fin t, x i j = true)

/-- The unique-intersection promise `D_{m, t} ⊆ (BitString m) ^ t`: either all `t` sets are
pairwise disjoint (`∀ j, #{i | x i j = true} ≤ 1`), or there exists a coordinate `j` contained in
every player's set while all other coordinates `j' ≠ j` appear in at most one player's set. -/
def UniqueDisjointPromise {t m : ℕ} (x : Fin t → BitString m) : Prop :=
  (∀ j : Fin m, (Finset.univ.filter fun i : Fin t ↦ x i j = true).card ≤ 1) ∨
    ∃ j : Fin m, (∀ i : Fin t, x i j = true) ∧
      ∀ j' : Fin m, j' ≠ j → (Finset.univ.filter fun i : Fin t ↦ x i j' = true).card ≤ 1

/-- `multipartyDisjointness` is invariant under arbitrary permutations of the `t` players. -/
theorem isSymmetricParty_multipartyDisjointness {t m : ℕ} :
    IsSymmetricParty (multipartyDisjointness (t := t) (m := m)) := by
  intro x σ
  simp only [multipartyDisjointness, decide_eq_decide]
  exact ⟨fun ⟨j, hj⟩ ↦ ⟨j, fun i ↦ by simpa using hj (σ.symm i)⟩,
    fun ⟨j, hj⟩ ↦ ⟨j, fun i ↦ hj (σ i)⟩⟩

/-- On `UniqueDisjointPromise`, any two distinct players `a ≠ b` witness whether all `t` sets
intersect: `multipartyDisjointness x = true` iff `x a` and `x b` share a coordinate. -/
theorem multipartyDisjointness_eq_pair_inter {t m : ℕ} {x : Fin t → BitString m}
    (hx : UniqueDisjointPromise x) {a b : Fin t} (hab : a ≠ b) :
    multipartyDisjointness x = decide (∃ j : Fin m, x a j = true ∧ x b j = true) := by
  simp only [multipartyDisjointness, decide_eq_decide]
  refine ⟨fun ⟨j, hj⟩ ↦ ⟨j, hj a, hj b⟩, fun ⟨j, ha, hb⟩ ↦ ?_⟩
  have htwo : 2 ≤ (Finset.univ.filter fun i : Fin t ↦ x i j = true).card := by
    have hsub : ({a, b} : Finset (Fin t)) ⊆ Finset.univ.filter fun i : Fin t ↦ x i j = true := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hi with rfl | rfl <;> assumption
    simpa [Finset.card_pair hab] using Finset.card_le_card hsub
  rcases hx with hdisj | ⟨j0, hj0, _⟩
  · have := hdisj j
    omega
  · exact ⟨j0, hj0⟩

private def extractMsg {P : Prop} [inst : Decidable P] {α : P → Type} {β : ¬P → Type}
    (hP : P) (v : @dite Type P inst α β) : α hP :=
  match inst, v with
  | isTrue _, w => w
  | isFalse hn, _ => absurd hP hn

/-- **Deterministic `(t - 1)`-player one-way upper bound on `UniqueDisjointPromise`**: for every
`t ≥ 2` and every assignment `assign : Fin (t + 1) → Fin t` of `t + 1` input sets among
`t = (t - 1) + 1` players, there is a deterministic `t`-player `OneWayProtocol` of total
communication cost at most `t - 1` (hence at most `t`) deciding `multipartyDisjointness` on
`UniqueDisjointPromise`. -/
theorem oneWay_pred_multipartyDisjointness_le {s m : ℕ}
    (assign : Fin (s + 2) → Fin (s + 1)) :
    ∃ P : OneWayProtocol (fun p : Fin (s + 1) ↦ {i : Fin (s + 2) // assign i = p} → BitString m)
        Bool,
      P.cost ≤ s ∧
        ∀ x : Fin (s + 2) → BitString m, UniqueDisjointPromise x →
          P.run (fun _ sub ↦ x sub.val) = multipartyDisjointness x := by
  classical
  -- By Pigeonhole (`s + 1 < s + 2`), `assign` is not injective.
  have hnotinj : ¬Function.Injective assign := fun hinj ↦ by
    have := Fintype.card_le_of_injective assign hinj
    simp at this
  obtain ⟨a, b, habEq, habNe⟩ : ∃ a b : Fin (s + 2), assign a = assign b ∧ a ≠ b := by
    by_contra! hall
    exact hnotinj fun a b h ↦ hall a b h
  let checkAt (p : Fin (s + 1)) (hp : assign a = p)
      (u : {i : Fin (s + 2) // assign i = p} → BitString m) : Bool :=
    decide (∃ j : Fin m, u ⟨a, hp⟩ j = true ∧ u ⟨b, habEq.symm.trans hp⟩ j = true)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- `s = 0`: 1 player (`Fin 1`) holds both `a` and `b` and sends `0` bits.
    have hsub : Subsingleton (Fin (0 + 1)) := by change Subsingleton (Fin 1); infer_instance
    refine ⟨{ msgLen := Fin.elim0
              step := fun i ↦ i.elim0
              finish := fun u _ ↦ checkAt (Fin.last 0) (hsub.elim _ _) u }, by simp,
      fun x hx ↦ ?_⟩
    rw [OneWayProtocol.run_eq_finish, OneWayProtocol.prefixMsg_zero]
    exact (multipartyDisjointness_eq_pair_inter hx habNe).symm
  · -- `s ≥ 1`: pass a running 1-bit accumulator across the `s` links.
    let P : OneWayProtocol
        (fun p : Fin (s + 1) ↦ {i : Fin (s + 2) // assign i = p} → BitString m) Bool :=
      { msgLen := fun _ ↦ 1
        step := fun i u prev ↦
          let prevBit : Bool := if h : 0 < i.val then extractMsg h prev 0 else false
          let curBit : Bool :=
            if hp : assign a = i.castSucc then prevBit || checkAt i.castSucc hp u else prevBit
          fun _ ↦ curBit
        finish := fun u lastMsg ↦
          let prevBit : Bool := extractMsg hs lastMsg 0
          if hp : assign a = Fin.last s then prevBit || checkAt (Fin.last s) hp u else prevBit }
    refine ⟨P, by simp [P], fun x hx ↦ ?_⟩
    let target : Bool := decide (∃ j : Fin m, x a j = true ∧ x b j = true)
    have hpref : ∀ (r : ℕ) (hr : r ≤ s) (hrpos : 0 < r),
        extractMsg hrpos (P.prefixMsg (fun _ sub ↦ x sub.val) r hr) 0 =
          if (assign a).val < r then target else false := by
      intro r hr hrpos
      induction r with
      | zero => omega
      | succ r ih =>
        rcases Nat.eq_zero_or_pos r with rfl | hr0
        · rw [OneWayProtocol.prefixMsg_succ, OneWayProtocol.prefixMsg_zero]
          change (if hp : assign a = (⟨0, hr⟩ : Fin s).castSucc then
              false || target else false) = if (assign a).val < 1 then target else false
          rw [Bool.false_or]
          split_ifs with hp0 hval
          · rfl
          · exfalso; have := congrArg Fin.val hp0; dsimp at this; omega
          · exfalso; exact hp0 (Fin.ext (by dsimp; omega))
          · rfl
        · have prev := ih (by omega) hr0
          rw [OneWayProtocol.prefixMsg_succ]
          let rawPrev := P.prefixMsg (fun _ sub ↦ x sub.val) r (by omega)
          change (if hp : assign a = (⟨r, hr⟩ : Fin s).castSucc then
              (if h : 0 < r then extractMsg h rawPrev 0 else false) || target
            else (if h : 0 < r then extractMsg h rawPrev 0 else false)) =
            if (assign a).val < r + 1 then target else false
          simp only [hr0, ↓reduceDIte]
          have prev' : extractMsg hr0 rawPrev 0 = if (assign a).val < r then target else false :=
            prev
          rw [prev']
          split_ifs with hpr hlt1 hlt2
          · exact Bool.or_self target
          · exfalso; omega
          · exact Bool.false_or target
          · exfalso; have := congrArg Fin.val hpr; dsimp at this; omega
          · rfl
          · exfalso; omega
          · exfalso; exact hpr (Fin.ext (by dsimp; omega))
          · rfl
    have hfin := hpref s le_rfl hs
    let fBit := extractMsg hs (P.prefixMsg (fun _ sub ↦ x sub.val) s le_rfl) 0
    rw [OneWayProtocol.run_eq_finish]
    change (if hp : assign a = Fin.last s then fBit || target else fBit) =
      multipartyDisjointness x
    have hfin' : fBit = if (assign a).val < s then target else false := hfin
    rw [hfin', multipartyDisjointness_eq_pair_inter hx habNe]
    change _ = target
    have hisLt := (assign a).isLt
    split_ifs with hlast hlt
    · exfalso; have := congrArg Fin.val hlast; dsimp at this; omega
    · exact Bool.false_or target
    · rfl
    · exfalso; exact hlast (Fin.ext (by dsimp; omega))

end DisjointnessProblem

/-! ### 2. Discrete Hellinger Metric, Cut-and-Paste, and Jensen–Shannon Inequality -/

section Hellinger

variable {α : Type*} [Fintype α]

/-- Discrete squared Hellinger distance `h²(P, Q) = (1 / 2) ∑ a, (√P(a) - √Q(a))²` on a finite
type `α`. -/
noncomputable def hellingerSq (P Q : PMF α) : ℝ :=
  (1 / 2) * ∑ a : α, (Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal) ^ 2

/-- Discrete Hellinger metric `h(P, Q) = √(h²(P, Q))` on a finite type `α`. -/
noncomputable def hellingerDist (P Q : PMF α) : ℝ :=
  Real.sqrt (hellingerSq P Q)

/-- Squared Hellinger distance is nonnegative. -/
theorem hellingerSq_nonneg (P Q : PMF α) : 0 ≤ hellingerSq P Q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

@[simp]
theorem hellingerSq_self (P : PMF α) : hellingerSq P P = 0 := by
  simp [hellingerSq]

/-- Hellinger distance is nonnegative. -/
theorem hellingerDist_nonneg (P : PMF α) (Q : PMF α) : 0 ≤ hellingerDist P Q :=
  Real.sqrt_nonneg _

@[simp]
theorem hellingerDist_self (P : PMF α) : hellingerDist P P = 0 := by
  simp [hellingerDist]

@[simp]
theorem hellingerDist_sq (P Q : PMF α) : hellingerDist P Q ^ 2 = hellingerSq P Q :=
  Real.sq_sqrt (hellingerSq_nonneg P Q)

/-- Squared Hellinger distance is symmetric. -/
theorem hellingerSq_comm (P Q : PMF α) : hellingerSq P Q = hellingerSq Q P := by
  unfold hellingerSq
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- Hellinger distance is symmetric. -/
theorem hellingerDist_comm (P Q : PMF α) : hellingerDist P Q = hellingerDist Q P := by
  rw [hellingerDist, hellingerDist, hellingerSq_comm]

/-- Elementary finite Cauchy–Schwarz inequality `(∑ i ∈ s, f i * g i) ≤ √(∑ f²) * √(∑ g²)`. -/
private theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  set A := ∑ i ∈ s, f i ^ 2
  set B := ∑ i ∈ s, g i ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rcases hA.eq_or_lt with hA0 | hApos
  · have hf0 : ∀ i ∈ s, f i = 0 := fun i hi ↦
      sq_eq_zero_iff.mp (le_antisymm
        ((Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) hi).trans hA0.symm.le) (sq_nonneg _))
    rw [Finset.sum_eq_zero fun i hi ↦ by simp [hf0 i hi], ← hA0, Real.sqrt_zero, zero_mul]
  · rcases hB.eq_or_lt with hB0 | hBpos
    · have hg0 : ∀ i ∈ s, g i = 0 := fun i hi ↦
        sq_eq_zero_iff.mp (le_antisymm
          ((Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) hi).trans hB0.symm.le) (sq_nonneg _))
      rw [Finset.sum_eq_zero fun i hi ↦ by simp [hg0 i hi], ← hB0, Real.sqrt_zero, mul_zero]
    · set sA := Real.sqrt A
      set sB := Real.sqrt B
      have hsA : 0 < sA := Real.sqrt_pos.mpr hApos
      have hsB : 0 < sB := Real.sqrt_pos.mpr hBpos
      have hsq : 0 ≤ ∑ i ∈ s, (sB * f i - sA * g i) ^ 2 :=
        Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have hexp : ∑ i ∈ s, (sB * f i - sA * g i) ^ 2 =
          sB ^ 2 * A + sA ^ 2 * B - 2 * sA * sB * ∑ i ∈ s, f i * g i := by
        calc ∑ i ∈ s, (sB * f i - sA * g i) ^ 2
            = ∑ i ∈ s, (sB ^ 2 * f i ^ 2 + sA ^ 2 * g i ^ 2 - 2 * sA * sB * (f i * g i)) :=
              Finset.sum_congr rfl fun _ _ ↦ by ring
          _ = _ := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, A, B]
      rw [hexp, Real.sq_sqrt hA, Real.sq_sqrt hB] at hsq
      have hAB : A * B = (sA * sB) * (sA * sB) := by
        calc A * B = sA ^ 2 * sB ^ 2 := by rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
          _ = (sA * sB) * (sA * sB) := by ring
      have hpos : 0 < 2 * sA * sB := by positivity
      nlinarith

/-- Triangle inequality for the discrete Hellinger metric `hellingerDist`. -/
theorem hellingerDist_triangle (P Q R : PMF α) :
    hellingerDist P R ≤ hellingerDist P Q + hellingerDist Q R := by
  let f (a : α) : ℝ := Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal
  let g (a : α) : ℝ := Real.sqrt (Q a).toReal - Real.sqrt (R a).toReal
  have hcs := sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  set A := ∑ a : α, f a ^ 2
  set B := ∑ a : α, g a ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsum : ∑ a : α, (Real.sqrt (P a).toReal - Real.sqrt (R a).toReal) ^ 2 ≤
      (Real.sqrt A + Real.sqrt B) ^ 2 := by
    calc ∑ a : α, (Real.sqrt (P a).toReal - Real.sqrt (R a).toReal) ^ 2
        = ∑ a : α, (f a + g a) ^ 2 := Finset.sum_congr rfl fun a _ ↦ by simp [f, g]
      _ = A + B + 2 * ∑ a : α, f a * g a := by
          have : ∀ a : α, (f a + g a) ^ 2 = f a ^ 2 + g a ^ 2 + 2 * (f a * g a) := fun _ ↦ by ring
          simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, A, B]
      _ ≤ A + B + 2 * (Real.sqrt A * Real.sqrt B) := by linarith
      _ = (Real.sqrt A + Real.sqrt B) ^ 2 := by
          calc A + B + 2 * (Real.sqrt A * Real.sqrt B)
              = Real.sqrt A ^ 2 + Real.sqrt B ^ 2 + 2 * (Real.sqrt A * Real.sqrt B) := by
                rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
            _ = (Real.sqrt A + Real.sqrt B) ^ 2 := by ring
  have hrhs0 : 0 ≤ hellingerDist P Q + hellingerDist Q R :=
    add_nonneg (hellingerDist_nonneg P Q) (hellingerDist_nonneg Q R)
  rw [← Real.sqrt_sq hrhs0]
  refine Real.sqrt_le_sqrt ?_
  have h1 : hellingerDist P Q = Real.sqrt (1 / 2) * Real.sqrt A := by
    rw [hellingerDist, hellingerSq, Real.sqrt_mul (by norm_num)]
  have h2 : hellingerDist Q R = Real.sqrt (1 / 2) * Real.sqrt B := by
    rw [hellingerDist, hellingerSq, Real.sqrt_mul (by norm_num)]
  rw [h1, h2]
  calc hellingerSq P R = (1 / 2) * ∑ a : α, (Real.sqrt (P a).toReal - Real.sqrt (R a).toReal) ^ 2 :=
        rfl
    _ ≤ (1 / 2) * (Real.sqrt A + Real.sqrt B) ^ 2 := by linarith
    _ = (Real.sqrt (1 / 2) * Real.sqrt A + Real.sqrt (1 / 2) * Real.sqrt B) ^ 2 := by
        have hsq2 : Real.sqrt (1 / 2) ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
        calc (1 / 2 : ℝ) * (Real.sqrt A + Real.sqrt B) ^ 2
            = Real.sqrt (1 / 2) ^ 2 * (Real.sqrt A + Real.sqrt B) ^ 2 := by rw [hsq2]
          _ = (Real.sqrt (1 / 2) * (Real.sqrt A + Real.sqrt B)) ^ 2 := by ring
          _ = _ := by ring

/-- Statistical distance is bounded by `√2` times Hellinger distance:
`dist P Q ^ 2 ≤ 2 * hellingerSq P Q`. -/
theorem dist_sq_le_two_mul_hellingerSq (P Q : PMF α) :
    dist P Q ^ 2 ≤ 2 * hellingerSq P Q := by
  let f (a : α) : ℝ := |Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal|
  let g (a : α) : ℝ := Real.sqrt (P a).toReal + Real.sqrt (Q a).toReal
  have hdiff (a : α) : |(P a).toReal - (Q a).toReal| = f a * g a := by
    have hp : 0 ≤ (P a).toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ (Q a).toReal := ENNReal.toReal_nonneg
    have hfac : (P a).toReal - (Q a).toReal =
        (Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal) * g a := by
      calc (P a).toReal - (Q a).toReal
          = Real.sqrt (P a).toReal ^ 2 - Real.sqrt (Q a).toReal ^ 2 := by
            rw [Real.sq_sqrt hp, Real.sq_sqrt hq]
        _ = _ := by ring
    rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hcs := sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  have hf2 : ∑ a : α, f a ^ 2 = 2 * hellingerSq P Q := by
    simp only [f, sq_abs, hellingerSq]
    ring
  have hg2 : ∑ a : α, g a ^ 2 ≤ 4 := by
    have hpt (a : α) : g a ^ 2 ≤ 2 * ((P a).toReal + (Q a).toReal) := by
      have hp : 0 ≤ (P a).toReal := ENNReal.toReal_nonneg
      have hq : 0 ≤ (Q a).toReal := ENNReal.toReal_nonneg
      have h0 : 0 ≤ (Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal) ^ 2 := sq_nonneg _
      have hexp : g a ^ 2 + (Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal) ^ 2 =
          2 * ((P a).toReal + (Q a).toReal) := by
        calc g a ^ 2 + (Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal) ^ 2
            = 2 * (Real.sqrt (P a).toReal ^ 2 + Real.sqrt (Q a).toReal ^ 2) := by
              simp only [g]; ring
          _ = _ := by rw [Real.sq_sqrt hp, Real.sq_sqrt hq]
      linarith
    calc ∑ a : α, g a ^ 2 ≤ ∑ a : α, 2 * ((P a).toReal + (Q a).toReal) :=
          Finset.sum_le_sum fun a _ ↦ hpt a
      _ = 2 * (∑ a : α, (P a).toReal + ∑ a : α, (Q a).toReal) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = 4 := by rw [PMF.sum_toReal, PMF.sum_toReal]; norm_num
  have hdist : 2 * dist P Q ≤ Real.sqrt (2 * hellingerSq P Q) * 2 := by
    have hd : 2 * dist P Q = ∑ a : α, f a * g a := by
      rw [PMF.dist_eq, Finset.sum_congr rfl fun a _ ↦ hdiff a]
      ring
    rw [hd, ← hf2]
    refine hcs.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ a : α, g a ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hg2
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hle : dist P Q ≤ Real.sqrt (2 * hellingerSq P Q) := by linarith
  calc dist P Q ^ 2 ≤ Real.sqrt (2 * hellingerSq P Q) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg hle 2
    _ = 2 * hellingerSq P Q := Real.sq_sqrt (mul_nonneg (by norm_num) (hellingerSq_nonneg P Q))

/-- **Cut-and-paste Hellinger bound on `t`-party product-rectangle laws**: if a family of finite
distributions `P : (Fin t → Bool) → PMF α` factors coordinatewise at every outcome `a : α` as
`(P u a).toReal = ∏ i : Fin t, w i a (u i)`, then
`hellingerSq (P (fun _ ↦ false)) (P (fun _ ↦ true))` is at most `t` times the sum of single-bit
Hellinger squares `∑ r : Fin t, hellingerSq (P (fun _ ↦ false)) (P (fun i ↦ decide (i = r)))`. -/
theorem hellingerSq_allTrue_le_mul_sum_single {t : ℕ} (P : (Fin t → Bool) → PMF α)
    (w : Fin t → α → Bool → ℝ)
    (hfac : ∀ u a, (P u a).toReal = ∏ i : Fin t, w i a (u i)) :
    hellingerSq (P fun _ ↦ false) (P fun _ ↦ true) ≤
      t * ∑ r : Fin t, hellingerSq (P fun _ ↦ false) (P fun i ↦ decide (i = r)) := by
  let z (k : ℕ) : Fin t → Bool := fun i ↦ decide (i.val < k)
  let e (r : Fin t) : Fin t → Bool := fun i ↦ decide (i = r)
  have hz0 : z 0 = (fun _ ↦ false) := by ext i; simp [z]
  have hzt : z t = (fun _ ↦ true) := by ext i; simp [z, i.isLt]
  -- Cut-and-paste step: `hellingerSq (P (z 0)) (P (z (k + 1))) = hellingerSq (P (z k)) (P (e k))`.
  have hcut (k : ℕ) (hk : k < t) :
      hellingerDist (P (z 0)) (P (z (k + 1))) = hellingerDist (P (z k)) (P (e ⟨k, hk⟩)) := by
    rw [hellingerDist, hellingerDist]
    congr 1
    have hsum1 : ∀ u, ∑ a : α, (P u a).toReal = 1 := fun u ↦ PMF.sum_toReal (P u)
    have hexp (Q R : PMF α) :
        hellingerSq Q R = 1 - ∑ a : α, Real.sqrt ((Q a).toReal * (R a).toReal) := by
      unfold hellingerSq
      have hterm (a : α) : (Real.sqrt (Q a).toReal - Real.sqrt (R a).toReal) ^ 2 =
          (Q a).toReal + (R a).toReal - 2 * Real.sqrt ((Q a).toReal * (R a).toReal) := by
        rw [Real.sqrt_mul ENNReal.toReal_nonneg]
        calc (Real.sqrt (Q a).toReal - Real.sqrt (R a).toReal) ^ 2
            = Real.sqrt (Q a).toReal ^ 2 + Real.sqrt (R a).toReal ^ 2 -
                2 * (Real.sqrt (Q a).toReal * Real.sqrt (R a).toReal) := by ring
          _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]
      simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        PMF.sum_toReal]
      ring
    rw [hexp, hexp]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    rw [hfac, hfac, hfac, hfac, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hik : i.val < k
    · have hik1 : i.val < k + 1 := by omega
      have hine : i ≠ ⟨k, hk⟩ := fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega
      simp [z, e, hik, hik1, hine, mul_comm]
    · by_cases hieq : i.val = k
      · have hi : i = ⟨k, hk⟩ := Fin.ext hieq
        simp [z, e, hi]
      · have hik1 : ¬i.val < k + 1 := by omega
        have hine : i ≠ ⟨k, hk⟩ := fun h ↦ hieq (congrArg Fin.val h)
        simp [z, e, hik, hik1, hine]
  -- Induction on `k ≤ t` bounding `hellingerDist (P (z 0)) (P (z k))`.
  have hind : ∀ (k : ℕ) (hk : k ≤ t),
      hellingerDist (P (z 0)) (P (z k)) ≤
        ∑ r ∈ Finset.univ.filter (fun r : Fin t ↦ r.val < k),
          hellingerDist (P (z 0)) (P (e r)) := by
    intro k hk
    induction k with
    | zero =>
      simp [hellingerDist, hellingerSq]
    | succ k ih =>
      have hklt : k < t := by omega
      have hfilt : Finset.univ.filter (fun r : Fin t ↦ r.val < k + 1) =
          insert ⟨k, hklt⟩ (Finset.univ.filter fun r : Fin t ↦ r.val < k) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotMem : (⟨k, hklt⟩ : Fin t) ∉ Finset.univ.filter (fun r : Fin t ↦ r.val < k) := by
        simp
      rw [hfilt, Finset.sum_insert hnotMem, hcut k hklt]
      have htri := hellingerDist_triangle (P (z k)) (P (z 0)) (P (e ⟨k, hklt⟩))
      rw [hellingerDist_comm (P (z k)) (P (z 0))] at htri
      linarith [ih hklt.le]
  have hall := hind t le_rfl
  have hfiltAll : Finset.univ.filter (fun r : Fin t ↦ r.val < t) = Finset.univ := by
    ext r
    simp
  rw [hfiltAll, hz0, hzt] at hall
  -- Square via Cauchy–Schwarz against `g ≡ 1`.
  have hcs := sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin t))
    (fun r ↦ hellingerDist (P fun _ ↦ false) (P (e r))) (fun _ ↦ 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    hellingerDist_sq] at hcs
  have hle := hall.trans hcs
  calc hellingerSq (P fun _ ↦ false) (P fun _ ↦ true)
      = hellingerDist (P fun _ ↦ false) (P fun _ ↦ true) ^ 2 := (hellingerDist_sq _ _).symm
    _ ≤ (Real.sqrt (∑ r : Fin t, hellingerSq (P fun _ ↦ false) (P (e r))) * Real.sqrt t) ^ 2 :=
        pow_le_pow_left₀ (hellingerDist_nonneg _ _) hle 2
    _ = t * ∑ r : Fin t, hellingerSq (P fun _ ↦ false) (P (e r)) := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ hellingerSq_nonneg _ _),
          Real.sq_sqrt (Nat.cast_nonneg t), mul_comm]

/-- Pointwise scalar Jensen–Shannon / Hellinger inequality: for `u, v ≥ 0` with `m = (u + v) / 2`,
`(1 / 4) * (√u - √v)² ≤ (u / 2) * log (u / m) + (v / 2) * log (v / m)`. -/
private theorem quarter_sq_sqrt_sub_le_js {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (1 / 4) * (Real.sqrt u - Real.sqrt v) ^ 2 ≤
      (u / 2) * (if u = 0 then 0 else Real.log (u / ((u + v) / 2))) +
        (v / 2) * (if v = 0 then 0 else Real.log (v / ((u + v) / 2))) := by
  set m := (u + v) / 2
  have hterm (x : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) (hxm : x ≤ 2 * m) :
      x - Real.sqrt (x * m) ≤ (x / 2) * (if x = 0 then 0 else Real.log (x / m)) := by
    rcases hx.eq_or_lt with rfl | hxpos
    · simp
    · have hmpos : 0 < m := by linarith
      simp only [hxpos.ne', ↓reduceIte]
      have hrat : 0 < Real.sqrt (m / x) := Real.sqrt_pos.mpr (div_pos hmpos hxpos)
      have hlog := Real.log_le_sub_one_of_pos hrat
      have hlogSq : Real.log (Real.sqrt (m / x)) = -(1 / 2) * Real.log (x / m) := by
        rw [Real.log_sqrt (div_nonneg hmpos.le hxpos.le), show m / x = (x / m)⁻¹ by field_simp,
          Real.log_inv]
        ring
      rw [hlogSq] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hxpos.le
      have hsqmul : x * Real.sqrt (m / x) = Real.sqrt (x * m) := by
        calc x * Real.sqrt (m / x)
            = Real.sqrt (x ^ 2) * Real.sqrt (m / x) := by rw [Real.sqrt_sq hxpos.le]
          _ = Real.sqrt (x ^ 2 * (m / x)) := (Real.sqrt_mul (sq_nonneg x) _).symm
          _ = Real.sqrt (x * m) := by congr 1; field_simp
      nlinarith
  have hm0 : 0 ≤ m := by positivity
  have hmDef : m = (u + v) / 2 := rfl
  have h1 := hterm u hu hm0 (by linarith [hmDef])
  have h2 := hterm v hv hm0 (by linarith [hmDef])
  -- Check `(1 / 4) * (√u - √v)² ≤ (u + v) - √(u * m) - √(v * m)`.
  set su := Real.sqrt u
  set sv := Real.sqrt v
  set sm := Real.sqrt m
  have hsu2 : su ^ 2 = u := Real.sq_sqrt hu
  have hsv2 : sv ^ 2 = v := Real.sq_sqrt hv
  have hsm2 : sm ^ 2 = m := Real.sq_sqrt hm0
  have hprod1 : Real.sqrt (u * m) = su * sm := Real.sqrt_mul hu m
  have hprod2 : Real.sqrt (v * m) = sv * sm := Real.sqrt_mul hv m
  have halg : (1 / 4) * (su - sv) ^ 2 ≤ u + v - su * sm - sv * sm := by
    have lhs_ge : 0 ≤ (3 / 4) * (u + v) + (1 / 2) * (su * sv) := by
      have : 0 ≤ su * sv := mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)
      linarith
    have rhs_ge : 0 ≤ sm * (su + sv) :=
      mul_nonneg (Real.sqrt_nonneg m) (add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v))
    have hdiffSq : ((3 / 4) * (u + v) + (1 / 2) * (su * sv)) ^ 2 - (sm * (su + sv)) ^ 2 =
        (1 / 16) * (su - sv) ^ 4 := by
      calc ((3 / 4) * (u + v) + (1 / 2) * (su * sv)) ^ 2 - (sm * (su + sv)) ^ 2
          = ((3 / 4) * (su ^ 2 + sv ^ 2) + (1 / 2) * (su * sv)) ^ 2 -
              sm ^ 2 * (su + sv) ^ 2 := by rw [hsu2, hsv2]; ring
        _ = ((3 / 4) * (su ^ 2 + sv ^ 2) + (1 / 2) * (su * sv)) ^ 2 -
              ((su ^ 2 + sv ^ 2) / 2) * (su + sv) ^ 2 := by rw [hsm2, hmDef, hsu2, hsv2]
        _ = (1 / 16) * (su - sv) ^ 4 := by ring
    have hsqge : (sm * (su + sv)) ^ 2 ≤ ((3 / 4) * (u + v) + (1 / 2) * (su * sv)) ^ 2 := by
      have : 0 ≤ (1 / 16 : ℝ) * (su - sv) ^ 4 := by positivity
      linarith
    have habs : sm * (su + sv) ≤ (3 / 4) * (u + v) + (1 / 2) * (su * sv) := by
      nlinarith
    have hid : u + v - (1 / 4) * (su - sv) ^ 2 = (3 / 4) * (u + v) + (1 / 2) * (su * sv) := by
      calc u + v - (1 / 4) * (su - sv) ^ 2
          = su ^ 2 + sv ^ 2 - (1 / 4) * (su - sv) ^ 2 := by rw [hsu2, hsv2]
        _ = (3 / 4) * (su ^ 2 + sv ^ 2) + (1 / 2) * (su * sv) := by ring
        _ = _ := by rw [hsu2, hsv2]
    linarith
  linarith

/-- **Jensen–Shannon / Hellinger inequality**: when a fair coin `B ~ uniformOfFintype Bool`
selects `P` on `false` and `Q` on `true`, the conditional entropy reduction
`1 - conditionalEntropy joint` is at least `hellingerSq P Q / (2 * Real.log 2)`. -/
theorem hellingerSq_le_two_mul_log_two_mul_one_sub_condEntropy (P Q : PMF α) :
    hellingerSq P Q ≤ 2 * Real.log 2 *
      (1 - conditionalEntropy ((PMF.uniformOfFintype Bool).bind fun b ↦
        (if b then Q else P).map (fun a ↦ (a, b)))) := by
  classical
  set joint : PMF (α × Bool) := (PMF.uniformOfFintype Bool).bind fun b ↦
    (if b then Q else P).map (fun a ↦ (a, b))
  have hjoint (a : α) (b : Bool) : (joint (a, b)).toReal =
      (1 / 2) * (if b then (Q a).toReal else (P a).toReal) := by
    simp only [joint, PMF.bind_apply, tsum_fintype, Fintype.sum_bool, PMF.uniformOfFintype_apply,
      Fintype.card_bool, Nat.cast_ofNat, PMF.map_apply, ↓reduceIte, Bool.false_eq_true]
    cases b
    · have h1 : ∑ x : α, (if (a, false) = (x, true) then Q x else 0) = 0 := by simp
      have h2 : ∑ x : α, (if (a, false) = (x, false) then P x else 0) = P a := by simp
      rw [h1, h2, mul_zero, zero_add, ENNReal.toReal_mul]
      simp
    · have h1 : ∑ x : α, (if (a, true) = (x, true) then Q x else 0) = Q a := by simp
      have h2 : ∑ x : α, (if (a, true) = (x, false) then P x else 0) = 0 := by simp
      rw [h1, h2, mul_zero, add_zero, ENNReal.toReal_mul]
      simp
  have hmarg (a : α) : ((joint.map Prod.fst) a).toReal = ((P a).toReal + (Q a).toReal) / 2 := by
    rw [PMF.map_fst_apply, tsum_fintype, Fintype.sum_bool,
      ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), hjoint, hjoint]
    simp only [↓reduceIte, Bool.false_eq_true]
    ring
  -- Express `1 - conditionalEntropy joint` directly as the normalized Jensen–Shannon sum.
  have hce : Real.log 2 * (1 - conditionalEntropy joint) =
      ∑ a : α, (((P a).toReal / 2) *
          (if (P a).toReal = 0 then 0
            else Real.log ((P a).toReal / (((P a).toReal + (Q a).toReal) / 2))) +
        ((Q a).toReal / 2) *
          (if (Q a).toReal = 0 then 0
            else Real.log ((Q a).toReal / (((P a).toReal + (Q a).toReal) / 2)))) := by
    rw [conditionalEntropy, entropy_eq_sum, entropy_eq_sum, Fintype.sum_prod_type]
    have hsum1 : (1 : ℝ) = ∑ a : α, (((P a).toReal + (Q a).toReal) / 2) := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, PMF.sum_toReal, PMF.sum_toReal]
      norm_num
    rw [hsum1]
    have hpt (a : α) :
        Real.log 2 * (((P a).toReal + (Q a).toReal) / 2) -
          ((∑ b : Bool, Real.negMulLog (joint (a, b)).toReal) -
            Real.negMulLog ((joint.map Prod.fst) a).toReal) =
        ((P a).toReal / 2) *
          (if (P a).toReal = 0 then 0
            else Real.log ((P a).toReal / (((P a).toReal + (Q a).toReal) / 2))) +
        ((Q a).toReal / 2) *
          (if (Q a).toReal = 0 then 0
            else Real.log ((Q a).toReal / (((P a).toReal + (Q a).toReal) / 2))) := by
      rw [Fintype.sum_bool, hjoint, hjoint, hmarg]
      simp only [↓reduceIte, Bool.false_eq_true, Real.negMulLog]
      set u := (P a).toReal
      set v := (Q a).toReal
      have hu : 0 ≤ u := ENNReal.toReal_nonneg
      have hv : 0 ≤ v := ENNReal.toReal_nonneg
      rcases hu.eq_or_lt with hu0 | hupos <;> rcases hv.eq_or_lt with hv0 | hvpos
      · simp [← hu0, ← hv0]
      · simp only [← hu0, hvpos.ne', ↓reduceIte, zero_div, zero_add, mul_zero]
        rw [show v / (v / 2) = 2 by field_simp, Real.log_mul (by norm_num) hvpos.ne',
          Real.log_div hvpos.ne' (by norm_num), show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
        ring
      · simp only [hupos.ne', ← hv0, ↓reduceIte, zero_div, add_zero, mul_zero]
        rw [show u / (u / 2) = 2 by field_simp, Real.log_mul (by norm_num) hupos.ne',
          Real.log_div hupos.ne' (by norm_num), show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
        ring
      · have hmne : (u + v) / 2 ≠ 0 := by positivity
        simp only [hupos.ne', hvpos.ne', ↓reduceIte]
        rw [Real.log_mul (by norm_num) hvpos.ne', Real.log_mul (by norm_num) hupos.ne',
          Real.log_div hupos.ne' hmne, Real.log_div hvpos.ne' hmne,
          show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
        ring
    calc Real.log 2 *
          ((∑ a : α, ((P a).toReal + (Q a).toReal) / 2) -
            ((∑ a : α, ∑ b : Bool, Real.negMulLog (joint (a, b)).toReal) / Real.log 2 -
              (∑ a : α, Real.negMulLog ((joint.map Prod.fst) a).toReal) / Real.log 2))
        = Real.log 2 * (∑ a : α, ((P a).toReal + (Q a).toReal) / 2) -
            ((∑ a : α, ∑ b : Bool, Real.negMulLog (joint (a, b)).toReal) -
              ∑ a : α, Real.negMulLog ((joint.map Prod.fst) a).toReal) := by
          have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
          field_simp
      _ = ∑ a : α, (Real.log 2 * (((P a).toReal + (Q a).toReal) / 2) -
            ((∑ b : Bool, Real.negMulLog (joint (a, b)).toReal) -
              Real.negMulLog ((joint.map Prod.fst) a).toReal)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      _ = _ := Finset.sum_congr rfl fun a _ ↦ hpt a
  have hsum_js : (1 / 4) * ∑ a : α, (Real.sqrt (P a).toReal - Real.sqrt (Q a).toReal) ^ 2 ≤
      Real.log 2 * (1 - conditionalEntropy joint) := by
    rw [hce, Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ ↦
      quarter_sq_sqrt_sub_le_js ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  unfold hellingerSq; linarith
end Hellinger

/-! ### 3. Coordinatewise Subadditivity of Entropy and `Ω(m / t²)` Lower Bound -/
section MultipartyDisjointnessLowerBound

/-- Coordinatewise subadditivity of Shannon entropy on `Fin m → β`: the entropy of a joint law on
`m`-tuples is at most the sum of the entropies of its `m` coordinate marginals. -/
theorem entropy_le_sum_coord {β : Type*} [Finite β] {m : ℕ} (p : PMF (Fin m → β)) :
    entropy p ≤ ∑ j : Fin m, entropy (p.map fun v ↦ v j) := by
  induction m with
  | zero =>
    have : Subsingleton (Fin 0 → β) := inferInstance
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    let _ := Fintype.ofFinite (Fin 0 → β)
    have := entropy_le_log_card p
    have hfc : Fintype.card (Fin 0 → β) = 1 := by simp
    rwa [hfc, Nat.cast_one, Real.logb_one] at this
  | succ m ih =>
    let split : (Fin (m + 1) → β) ≃ β × (Fin m → β) :=
      { toFun := fun v ↦ (v 0, Fin.tail v)
        invFun := fun pair ↦ Fin.cons pair.1 pair.2
        left_inv := fun v ↦ Fin.cons_self_tail v
        right_inv := fun ⟨b, w⟩ ↦ by simp }
    have heq : entropy p = entropy (p.map split) :=
      (entropy_map_of_injective p split.injective).symm
    have hsub := entropy_le_entropy_map_fst_add_entropy_map_snd (p.map split)
    have hfst : (p.map split).map Prod.fst = p.map (fun v ↦ v 0) := by
      rw [PMF.map_comp]; rfl
    have hsnd : (p.map split).map Prod.snd = p.map Fin.tail := by
      rw [PMF.map_comp]; rfl
    rw [hfst, hsnd] at hsub
    have htail := ih (p.map Fin.tail)
    have hsum : ∑ j : Fin m, entropy ((p.map Fin.tail).map fun v ↦ v j) =
        ∑ j : Fin m, entropy (p.map fun v ↦ v j.succ) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [PMF.map_comp]; rfl
    rw [Fin.sum_univ_succ]
    linarith

/-- Conditional coordinatewise subadditivity: for any joint law `joint : PMF (α × (Fin m → β))`,
`conditionalEntropy joint ≤ ∑ j : Fin m, conditionalEntropy (joint.map (Prod.map id (· j)))`. -/
theorem conditionalEntropy_le_sum_coord {α β : Type*} [Finite α] [Finite β] {m : ℕ}
    (joint : PMF (α × (Fin m → β))) :
    conditionalEntropy joint ≤
      ∑ j : Fin m, conditionalEntropy (joint.map fun pair ↦ (pair.1, pair.2 j)) := by
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  rw [conditionalEntropy_eq_sum]
  have hcoord (j : Fin m) :
      conditionalEntropy (joint.map fun pair ↦ (pair.1, pair.2 j)) =
        ∑ a : α, ((joint.map Prod.fst) a).toReal *
          entropy ((conditionalSnd joint a).map fun v ↦ v j) := by
    rw [conditionalEntropy_eq_sum]
    have hfst : (joint.map fun pair ↦ (pair.1, pair.2 j)).map Prod.fst = joint.map Prod.fst := by
      rw [PMF.map_comp]; rfl
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hfst]
    by_cases ha : (joint.map Prod.fst) a = 0
    · simp [ha]
    · congr 2
      ext b
      have ha1 : a ∈ ((joint.map fun pair ↦ (pair.1, pair.2 j)).map Prod.fst).support := by
        rw [hfst]; exact ha
      have ha2 : a ∈ (joint.map Prod.fst).support := ha
      rw [conditionalSnd_apply _ a ha1 b, hfst]
      conv_rhs => rw [PMF.map_apply]
      have hite (v : Fin m → β) :
          (if b = v j then conditionalSnd joint a v else 0) =
            (if b = v j then joint (a, v) else 0) / (joint.map Prod.fst) a := by
        rw [conditionalSnd_apply _ a ha2 v]
        by_cases hbv : b = v j <;> simp [hbv]
      simp_rw [hite]
      rw [tsum_fintype, ← ENNReal.sum_div]
      congr 1
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
      simp only [Prod.mk.injEq]
      have hprod (a' : α) :
          (∑ v : Fin m → β, if a = a' ∧ b = v j then joint (a', v) else 0) =
            if a = a' then ∑ v : Fin m → β, if b = v j then joint (a', v) else 0 else 0 := by
        by_cases haa : a = a' <;> simp [haa]
      simp_rw [hprod]
      rw [Finset.sum_ite_eq]
      simp
  simp_rw [hcoord]
  rw [← Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (entropy_le_sum_coord _) ENNReal.toReal_nonneg

/-- Helper: probability of a predicate under `uniformOfFintype (BitString m)` equals a product over
fibers of `part : Fin m → Fin t` when the predicate is a conjunction of fiberwise predicates. -/
private theorem uniformOfFintype_bitString_fiber_prod {t m : ℕ} (part : Fin m → Fin t)
    (pred : Fin t → BitString m → Bool)
    (hlocal : ∀ (i : Fin t) (b₁ b₂ : BitString m),
      (∀ j : Fin m, part j = i → b₁ j = b₂ j) → pred i b₁ = pred i b₂) :
    (((PMF.uniformOfFintype (BitString m)).toOuterMeasure
      {b | ∀ i : Fin t, pred i b = true}).toReal) =
        ∏ i : Fin t,
          ((PMF.uniformOfFintype (BitString m)).toOuterMeasure {b | pred i b = true}).toReal := by
  classical
  -- Prove by induction on `t`, splitting off fiber `part j = Fin.last t'` via subset/complement
  -- bijection `(Fin m → Bool) ≃ ({j // P j} → Bool) × ({j // ¬P j} → Bool)`.
  have hsplit : ∀ (S : Finset (Fin t)),
      (((PMF.uniformOfFintype (BitString m)).toOuterMeasure
        {b | ∀ i ∈ S, pred i b = true}).toReal) =
          ∏ i ∈ S,
            ((PMF.uniformOfFintype (BitString m)).toOuterMeasure {b | pred i b = true}).toReal := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hev : {b : BitString m | ∀ i ∈ (∅ : Finset (Fin t)), pred i b = true} = Set.univ := by
        ext b; simp
      rw [hev, Finset.prod_empty, toOuterMeasure_apply_toReal]
      simp
    | @insert i₀ S hi₀ ih =>
      rw [Finset.prod_insert hi₀, ← ih]
      let P (j : Fin m) : Prop := part j = i₀
      let e : BitString m ≃ ({j : Fin m // P j} → Bool) × ({j : Fin m // ¬P j} → Bool) :=
        { toFun := fun b ↦ (fun j ↦ b j.1, fun j ↦ b j.1)
          invFun := fun pair j ↦ if h : P j then pair.1 ⟨j, h⟩ else pair.2 ⟨j, h⟩
          left_inv := fun b ↦ by ext j; dsimp only; split_ifs <;> rfl
          right_inv := fun ⟨u, v⟩ ↦ by
            ext ⟨j, hj⟩
            · simp [hj]
            · simp [hj] }
      let liftL (u : {j : Fin m // P j} → Bool) : BitString m :=
        e.symm (u, fun _ ↦ false)
      let liftR (v : {j : Fin m // ¬P j} → Bool) : BitString m :=
        e.symm (fun _ ↦ false, v)
      have hL (b : BitString m) : pred i₀ b = pred i₀ (liftL (e b).1) :=
        hlocal i₀ b _ fun j hj ↦ by simp [liftL, e, P, hj]
      have hR (i : Fin t) (hiS : i ∈ S) (b : BitString m) :
          pred i b = pred i (liftR (e b).2) := by
        have hne : i ≠ i₀ := fun h ↦ hi₀ (h ▸ hiS)
        exact hlocal i b _ fun j hj ↦ by
          have hnp : ¬P j := fun hp ↦ hne (hj.symm.trans hp)
          simp [liftR, e, hnp]
      simp only [toOuterMeasure_apply_toReal, PMF.uniformOfFintype_apply, Set.mem_ofPred_eq]
      have hcard : (Fintype.card (BitString m) : ℝ) =
          (Fintype.card ({j : Fin m // P j} → Bool) : ℝ) *
            (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ) := by
        exact_mod_cast (Fintype.card_congr e).trans (Fintype.card_prod _ _)
      have hsum_split (g : BitString m → ℝ) :
          ∑ b : BitString m, g b =
            ∑ u : {j : Fin m // P j} → Bool, ∑ v : {j : Fin m // ¬P j} → Bool,
              g (e.symm (u, v)) :=
        (Fintype.sum_equiv e _ (fun p ↦ g (e.symm p)) fun b ↦ by simp).trans
          (Fintype.sum_prod_type _)
      have hconst : ((Fintype.card (BitString m) : ℝ≥0∞)⁻¹).toReal =
          ((Fintype.card ({j : Fin m // P j} → Bool) : ℝ) *
            (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ))⁻¹ := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard]
      simp_rw [hconst]
      have hboth :
          (∑ b : BitString m,
            if ∀ i ∈ insert i₀ S, pred i b = true then
              ((Fintype.card ({j : Fin m // P j} → Bool) : ℝ) *
                (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ))⁻¹
            else 0) =
          (∑ u : {j : Fin m // P j} → Bool,
            if pred i₀ (liftL u) = true then
              (Fintype.card ({j : Fin m // P j} → Bool) : ℝ)⁻¹ else 0) *
          (∑ v : {j : Fin m // ¬P j} → Bool,
            if ∀ i ∈ S, pred i (liftR v) = true then
              (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ)⁻¹ else 0) := by
        rw [hsum_split, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        have he1 : (e (e.symm (u, v))).1 = u := by simp
        have he2 : (e (e.symm (u, v))).2 = v := by simp
        have hiff : (∀ i ∈ insert i₀ S, pred i (e.symm (u, v)) = true) ↔
            pred i₀ (liftL u) = true ∧ ∀ i ∈ S, pred i (liftR v) = true := by
          rw [Finset.forall_mem_insert, hL (e.symm (u, v)), he1]
          exact and_congr_right fun _ ↦ forall₂_congr fun i hiS ↦ by
            rw [hR i hiS (e.symm (u, v)), he2]
        rw [ite_congr (propext hiff) (fun _ ↦ rfl) (fun _ ↦ rfl)]
        by_cases h1 : pred i₀ (liftL u) = true <;>
          by_cases h2 : ∀ i ∈ S, pred i (liftR v) = true <;>
          simp [h1, h2, mul_inv_rev, mul_comm]
      have hleft :
          (∑ b : BitString m,
            if pred i₀ b = true then
              ((Fintype.card ({j : Fin m // P j} → Bool) : ℝ) *
                (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ))⁻¹
            else 0) =
          ∑ u : {j : Fin m // P j} → Bool,
            if pred i₀ (liftL u) = true then
              (Fintype.card ({j : Fin m // P j} → Bool) : ℝ)⁻¹ else 0 := by
        rw [hsum_split]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        have hcongr : ∀ v, pred i₀ (e.symm (u, v)) = pred i₀ (liftL u) := fun v ↦ by
          have := hL (e.symm (u, v))
          simpa using this
        simp only [hcongr]
        by_cases hu : pred i₀ (liftL u) = true
        · simp only [hu, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hpos : (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ) ≠ 0 := by positivity
          field_simp
        · simp [hu]
      have hright :
          (∑ b : BitString m,
            if ∀ i ∈ S, pred i b = true then
              ((Fintype.card ({j : Fin m // P j} → Bool) : ℝ) *
                (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ))⁻¹
            else 0) =
          ∑ v : {j : Fin m // ¬P j} → Bool,
            if ∀ i ∈ S, pred i (liftR v) = true then
              (Fintype.card ({j : Fin m // ¬P j} → Bool) : ℝ)⁻¹ else 0 := by
        rw [hsum_split, Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        have hcongr : ∀ u, (∀ i ∈ S, pred i (e.symm (u, v)) = true) ↔
            (∀ i ∈ S, pred i (liftR v) = true) := fun u ↦
          forall₂_congr fun i hiS ↦ by
            have := hR i hiS (e.symm (u, v))
            simpa using this
        simp only [hcongr]
        by_cases hv : ∀ i ∈ S, pred i (liftR v) = true
        · rw [ite_eq_left hv]
          simp only [ite_eq_left hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hpos : (Fintype.card ({j : Fin m // P j} → Bool) : ℝ) ≠ 0 := by positivity
          field_simp
        · rw [ite_eq_right hv]
          simp only [ite_eq_right hv, Finset.sum_const_zero]
      rw [hboth, hleft, hright]
  simpa using hsplit Finset.univ

/-- **Randomized `t`-party NIH lower bound for unique-intersection set disjointness**
: for `t ≥ 2`, `m ≥ 0`, `δ ≤ 1 / 2`, and `c : ℕ`,
if `(NIHProtocol.randomizedCost (fun _ : Fin t ↦ BitString m) Bool).ecomplexity δ` on
`UniqueDisjointPromise` is at most `c`, then
`(1 - 2 * δ) ^ 2 * m ≤ 16 * Real.log 2 * t ^ 2 * c`.
-/
theorem rcc_multipartyDisjointness_lower {t m c : ℕ} {δ : ℝ} (ht : 2 ≤ t) (hδ : δ ≤ 1 / 2)
    (hc : (NIHProtocol.randomizedCost (fun _ : Fin t ↦ BitString m) Bool).ecomplexity δ
      (fun x z ↦ multipartyDisjointness x = z)
      {x | UniqueDisjointPromise x} ≤ c) :
    (1 - 2 * δ) ^ 2 * m ≤ 16 * Real.log 2 * (t : ℝ) ^ 2 * c := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, mul_zero]
    positivity
  have : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- Step 1: Hard NO and YES embeddings supported inside `UniqueDisjointPromise`.
  let embedNo (r : Fin m → Fin t) (b : BitString m) : Fin t → BitString m :=
    fun i j ↦ decide (r j = i ∧ b j = true)
  let embedSpike (r : Fin m → Fin t) (b : BitString m) (jStar : Fin m) (u : Fin t → Bool) :
      Fin t → BitString m :=
    fun i j ↦ if j = jStar then u i else decide (r j = i ∧ b j = true)
  have hNoValid (r : Fin m → Fin t) (b : BitString m) :
      UniqueDisjointPromise (embedNo r b) ∧ multipartyDisjointness (embedNo r b) = false := by
    have hcard (j : Fin m) :
        (Finset.univ.filter fun i : Fin t ↦ embedNo r b i j = true).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, embedNo, decide_eq_true_eq]
        at hi₁ hi₂
      exact hi₁.1.symm.trans hi₂.1
    refine ⟨Or.inl hcard, ?_⟩
    simp only [multipartyDisjointness, decide_eq_false_iff_not, not_exists, not_forall]
    intro j
    by_cases h0 : r j = ⟨0, by omega⟩
    · refine ⟨⟨1, ht⟩, ?_⟩
      simp [embedNo, h0, Fin.ext_iff]
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [embedNo, h0]
  have hYesValid (r : Fin m → Fin t) (b : BitString m) (jStar : Fin m) :
      UniqueDisjointPromise (embedSpike r b jStar fun _ ↦ true) ∧
        multipartyDisjointness (embedSpike r b jStar fun _ ↦ true) = true := by
    refine ⟨Or.inr ⟨jStar, fun i ↦ by simp [embedSpike], fun j' hj' ↦ ?_⟩, ?_⟩
    · refine Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, embedSpike, hj', ↓reduceIte,
        decide_eq_true_eq] at hi₁ hi₂
      exact hi₁.1.symm.trans hi₂.1
    · simp only [multipartyDisjointness, decide_eq_true_eq]
      exact ⟨jStar, fun i ↦ by simp [embedSpike]⟩
  -- Step 2: Yao coin-fixing on the balanced mixture of `embedNo` and `embedSpike · · jStar 1`.
  let Seed := Bool × (Fin m → Fin t) × BitString m × Fin m
  let genInput : Seed → (Fin t → BitString m) := fun ⟨isYes, r, b, jStar⟩ ↦
    if isYes then embedSpike r b jStar (fun _ ↦ true) else embedNo r b
  let hardMix : PMF (Fin t → BitString m) := (PMF.uniformOfFintype Seed).map genInput
  have hsupp : ∀ x ∈ hardMix.support, x ∈ {x | UniqueDisjointPromise x} := by
    intro x hx
    obtain ⟨⟨isYes, r, b, jStar⟩, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    cases isYes
    · exact (hNoValid r b).1
    · exact (hYesValid r b jStar).1
  obtain ⟨μ, hμSolves, hμCost⟩ := RandomizedCost.ecomplexity_le_iff.mp hc
  obtain ⟨P, hPsupp, hPerr⟩ := hμSolves.exists_distributionalError_le hardMix hsupp
  have hPdepth : P.depth ≤ c := by
    exact_mod_cast (PMF.le_maxCost hPsupp).trans hμCost
  -- Step 3: Relate distributional error of deterministic `P` to leaf-distribution TV distances.
  let RB := (Fin m → Fin t) × BitString m
  let noLeaf : PMF (Fin P.leafCount) :=
    (PMF.uniformOfFintype RB).map fun q ↦ P.leaf (embedNo q.1 q.2)
  let yesLeaf (jStar : Fin m) : PMF (Fin P.leafCount) :=
    (PMF.uniformOfFintype RB).map fun q ↦ P.leaf (embedSpike q.1 q.2 jStar fun _ ↦ true)
  have herr_avg :
      1 - 2 * δ ≤ (m : ℝ)⁻¹ * ∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) := by
    -- Express `distributionalError` via `PMF.uniformOfFintype Seed`.
    have herrEq :
        (NIHProtocol.randomizedCost (fun _ : Fin t ↦ BitString m) Bool).distributionalError
          P hardMix (fun x z ↦ multipartyDisjointness x = z) =
        (1 / 2) * (∑ ℓ : Fin P.leafCount,
            if P.leafValue ℓ = true then (noLeaf ℓ).toReal else 0) +
        (1 / 2) * ((m : ℝ)⁻¹ * ∑ jStar : Fin m, ∑ ℓ : Fin P.leafCount,
            if P.leafValue ℓ = false then (yesLeaf jStar ℓ).toReal else 0) := by
      unfold RandomizedCost.distributionalError PMF.errorProb hardMix
      rw [PMF.toOuterMeasure_map_apply, toOuterMeasure_apply_toReal]
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, NIHProtocol.randomizedCost_eval, genInput]
      dsimp only [Seed]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, ENNReal.toReal_inv,
        ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ↓reduceIte,
        Bool.false_eq_true]
      -- Simplify YES sum and NO sum
      have hYesTerm (q : RB × Fin m) :
          (¬multipartyDisjointness (embedSpike q.1.1 q.1.2 q.2 fun _ ↦ true) =
            P.run (embedSpike q.1.1 q.1.2 q.2 fun _ ↦ true)) ↔
          P.leafValue (P.leaf (embedSpike q.1.1 q.1.2 q.2 fun _ ↦ true)) = false := by
        rw [(hYesValid q.1.1 q.1.2 q.2).2, P.run_eq_leafValue_leaf]
        cases P.leafValue _ <;> simp
      have hNoTerm (q : RB × Fin m) :
          (¬multipartyDisjointness (embedNo q.1.1 q.1.2) =
            P.run (embedNo q.1.1 q.1.2)) ↔
          P.leafValue (P.leaf (embedNo q.1.1 q.1.2)) = true := by
        rw [(hNoValid q.1.1 q.1.2).2, P.run_eq_leafValue_leaf]
        cases P.leafValue _ <;> simp
      -- Rewrite both branches via leaf marginals
      have hleafSum (f : RB → Fin P.leafCount) (want : Bool) :
          (∑ q : RB, if P.leafValue (f q) = want then ((Fintype.card RB : ℝ))⁻¹ else 0) =
          ∑ ℓ : Fin P.leafCount,
            if P.leafValue ℓ = want then (((PMF.uniformOfFintype RB).map f) ℓ).toReal else 0 := by
        have hmap (ℓ : Fin P.leafCount) :
            (((PMF.uniformOfFintype RB).map f) ℓ).toReal =
              ∑ q : RB, if ℓ = f q then ((Fintype.card RB : ℝ))⁻¹ else 0 := by
          rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun _ _ ↦ by split_ifs <;> simp]
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          by_cases hq : ℓ = f q <;>
            simp [hq, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        have hite_sum (cond : Prop) [Decidable cond] (g : RB → ℝ) :
            (if cond then ∑ q : RB, g q else 0) = ∑ q : RB, if cond then g q else 0 := by
          split_ifs <;> simp
        simp_rw [hmap, hite_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        have hswap_if (ℓ : Fin P.leafCount) :
            (if P.leafValue ℓ = want then if ℓ = f q then ((Fintype.card RB : ℝ))⁻¹ else 0
              else 0) =
            if ℓ = f q then (if P.leafValue ℓ = want then ((Fintype.card RB : ℝ))⁻¹ else 0)
              else 0 := by
          split_ifs <;> rfl
        simp_rw [hswap_if]
        rw [Finset.sum_ite_eq']
        simp
      have hRBpos : (Fintype.card RB : ℝ) ≠ 0 := by positivity
      have hmpos : (m : ℝ) ≠ 0 := by positivity
      calc (∑ x : (Fin m → Fin t) × BitString m × Fin m,
              if ¬multipartyDisjointness (embedSpike x.1 x.2.1 x.2.2 fun _ ↦ true) =
                P.run (embedSpike x.1 x.2.1 x.2.2 fun _ ↦ true) then
                (2 * ((Fintype.card (Fin m → Fin t) : ℝ) *
                  ((Fintype.card (BitString m) : ℝ) * m)))⁻¹
              else 0) +
            (∑ x : (Fin m → Fin t) × BitString m × Fin m,
              if ¬multipartyDisjointness (embedNo x.1 x.2.1) = P.run (embedNo x.1 x.2.1) then
                (2 * ((Fintype.card (Fin m → Fin t) : ℝ) *
                  ((Fintype.card (BitString m) : ℝ) * m)))⁻¹
              else 0)
          = (1 / 2) * ((m : ℝ)⁻¹ * ∑ jStar : Fin m, ∑ q : RB,
              if P.leafValue (P.leaf (embedSpike q.1 q.2 jStar fun _ ↦ true)) = false then
                ((Fintype.card RB : ℝ))⁻¹ else 0) +
            (1 / 2) * ((m : ℝ)⁻¹ * ∑ _jStar : Fin m, ∑ q : RB,
              if P.leafValue (P.leaf (embedNo q.1 q.2)) = true then
                ((Fintype.card RB : ℝ))⁻¹ else 0) := by
            have hcardRB : (Fintype.card RB : ℝ) =
                (Fintype.card (Fin m → Fin t) : ℝ) * (Fintype.card (BitString m) : ℝ) := by
              exact_mod_cast Fintype.card_prod _ _
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
            simp_rw [Fintype.sum_prod_type]
            congr 1
            · conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun jStar _ ↦ ?_
              dsimp only [RB]
              rw [Fintype.sum_prod_type]
              simp_rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
              have hiff := hYesTerm ((r, b), jStar)
              dsimp only at hiff
              rw [ite_congr (propext hiff) (fun _ ↦ rfl) (fun _ ↦ rfl), hcardRB]
              split_ifs <;> ring
            · conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun jStar _ ↦ ?_
              dsimp only [RB]
              rw [Fintype.sum_prod_type]
              simp_rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
              have hiff := hNoTerm ((r, b), jStar)
              dsimp only at hiff
              rw [ite_congr (propext hiff) (fun _ ↦ rfl) (fun _ ↦ rfl), hcardRB]
              split_ifs <;> ring
        _ = _ := by
            rw [add_comm]
            congr 1
            · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                inv_mul_cancel_left₀ hmpos]
              exact congrArg ((1 / 2 : ℝ) * ·) (hleafSum _ true)
            · congr 2
              exact Finset.sum_congr rfl fun jStar _ ↦ hleafSum _ false
    -- For each `jStar`, `1 - dist noLeaf (yesLeaf jStar) ≤ errNo + errYes jStar`.
    have htv (jStar : Fin m) :
        1 - dist noLeaf (yesLeaf jStar) ≤
          (∑ ℓ : Fin P.leafCount, if P.leafValue ℓ = true then (noLeaf ℓ).toReal else 0) +
          (∑ ℓ : Fin P.leafCount,
            if P.leafValue ℓ = false then (yesLeaf jStar ℓ).toReal else 0) := by
      have hov := PMF.sum_min_toReal noLeaf (yesLeaf jStar)
      rw [← hov, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ℓ _ ↦ ?_
      cases P.leafValue ℓ
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        exact min_le_right _ _
      · simp only [↓reduceIte, Bool.true_eq_false, add_zero]
        exact min_le_left _ _
    have hsum_tv : (m : ℝ) - ∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) ≤
        m * (∑ ℓ : Fin P.leafCount, if P.leafValue ℓ = true then (noLeaf ℓ).toReal else 0) +
        ∑ jStar : Fin m, ∑ ℓ : Fin P.leafCount,
          if P.leafValue ℓ = false then (yesLeaf jStar ℓ).toReal else 0 := by
      have h := Finset.sum_le_sum fun jStar (_ : jStar ∈ Finset.univ) ↦ htv jStar
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      linarith
    rw [herrEq] at hPerr
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hmul := mul_le_mul_of_nonneg_left hPerr (by positivity : (0 : ℝ) ≤ 2 * m)
    have hsimp : (2 * (m : ℝ)) *
        ((1 / 2) * (∑ ℓ, if P.leafValue ℓ = true then (noLeaf ℓ).toReal else 0) +
          (1 / 2) * ((m : ℝ)⁻¹ * ∑ jStar, ∑ ℓ,
            if P.leafValue ℓ = false then (yesLeaf jStar ℓ).toReal else 0)) =
        m * (∑ ℓ, if P.leafValue ℓ = true then (noLeaf ℓ).toReal else 0) +
        ∑ jStar, ∑ ℓ, if P.leafValue ℓ = false then (yesLeaf jStar ℓ).toReal else 0 := by
      field_simp
    rw [hsimp] at hmul
    have h1 : (1 - 2 * δ) * m ≤ ∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) := by linarith
    exact (le_inv_mul_iff₀ hmpos).mpr (by linarith)
  -- Step 4: Bound each `dist noLeaf (yesLeaf jStar)` via rectangle Hellinger cut-and-paste.
  let Q (r₀ : Fin m → Fin t) (jStar : Fin m) (u : Fin t → Bool) : PMF (Fin P.leafCount) :=
    (PMF.uniformOfFintype (BitString m)).map fun b₀ ↦ P.leaf (embedSpike r₀ b₀ jStar u)
  have hQ_rect (r₀ : Fin m → Fin t) (jStar : Fin m) :
      hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true) ≤
        t * ∑ r_j : Fin t,
          hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) := by
    let pred (u : Fin t → Bool) (ℓ : Fin P.leafCount) (i : Fin t) (b₀ : BitString m) : Bool :=
      decide (embedSpike r₀ b₀ jStar u i ∈ P.leafCoord ℓ i)
    let w (i : Fin t) (ℓ : Fin P.leafCount) (bit : Bool) : ℝ :=
      ((PMF.uniformOfFintype (BitString m)).toOuterMeasure
        {b₀ | (fun j ↦ if j = jStar then bit else decide (r₀ j = i ∧ b₀ j = true)) ∈
          P.leafCoord ℓ i}).toReal
    refine hellingerSq_allTrue_le_mul_sum_single (Q r₀ jStar) w fun u ℓ ↦ ?_
    have hQeq : (Q r₀ jStar u ℓ).toReal =
        ((PMF.uniformOfFintype (BitString m)).toOuterMeasure
          {b₀ | ∀ i : Fin t, pred u ℓ i b₀ = true}).toReal := by
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      congr 2
      ext b₀
      simp only [Set.mem_preimage, Set.mem_singleton_iff, P.leaf_eq_iff_mem_leafCoord,
        Set.mem_ofPred_eq, pred, decide_eq_true_eq]
    rw [hQeq, uniformOfFintype_bitString_fiber_prod r₀ (pred u ℓ)]
    · refine Finset.prod_congr rfl fun i _ ↦ ?_
      simp [w, pred, embedSpike]
    · intro i b₁ b₂ hagree
      simp only [pred]
      congr 2
      ext j
      by_cases hj : j = jStar
      · simp [embedSpike, hj]
      · simp only [embedSpike, hj, ↓reduceIte]
        by_cases hr : r₀ j = i
        · simp [hr, hagree j hr]
        · simp [hr]
  -- Express `noLeaf` and `yesLeaf jStar` as `uniformOfFintype (Fin m → Fin t)`-mixtures over `r₀`.
  let noKernel (r₀ : Fin m → Fin t) (jStar : Fin m) : PMF (Fin P.leafCount) :=
    (PMF.uniformOfFintype (Fin t × Bool)).bind fun ⟨r_j, b_j⟩ ↦
      Q r₀ jStar (fun i ↦ decide (r_j = i ∧ b_j = true))
  have hyesEq (jStar : Fin m) :
      yesLeaf jStar = (PMF.uniformOfFintype (Fin m → Fin t)).bind fun r₀ ↦
        Q r₀ jStar (fun _ ↦ true) := by
    have hp := (PMF.uniformOfFintype_prod (Fin m → Fin t) (BitString m)).symm
    dsimp only [yesLeaf, RB, Q]
    rw [hp, PMF.map_bind]
    exact congrArg (PMF.uniformOfFintype (Fin m → Fin t)).bind
      (funext fun _ ↦ PMF.map_comp _ _ _)
  have hnoEq (jStar : Fin m) :
      noLeaf = (PMF.uniformOfFintype (Fin m → Fin t)).bind fun r₀ ↦ noKernel r₀ jStar := by
    -- Resample coordinate `jStar` of `r` and of `b` independently using `uniformOfFintype_update`.
    have hupdR := uniformOfFintype_update (γ := Fin t) jStar
    have hupdB := uniformOfFintype_update (γ := Bool) jStar
    have hRB : PMF.uniformOfFintype RB =
        (PMF.uniformOfFintype (Fin m → Fin t)).bind fun r₀ ↦
          (PMF.uniformOfFintype (BitString m)).bind fun b₀ ↦
            (PMF.uniformOfFintype (Fin t)).bind fun r_j ↦
              (PMF.uniformOfFintype Bool).map fun b_j ↦
                (Function.update r₀ jStar r_j, Function.update b₀ jStar b_j) := by
      have hp := (PMF.uniformOfFintype_prod (Fin m → Fin t) (BitString m)).symm
      dsimp only [RB]
      conv_lhs => rw [hp, ← hupdR, ← hupdB]
      ext ⟨r, b⟩
      simp only [PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def,
        PMF.bind_apply, PMF.map_apply, tsum_fintype]
      -- Commute the four finite sums
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r₀ _ ↦ ?_
      conv_lhs => arg 2; ext r_j; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b₀ _ ↦
        Finset.sum_congr rfl fun r_j _ ↦ Finset.sum_congr rfl fun b_j _ ↦ ?_
      split_ifs <;> ring
    have hemb (r₀ : Fin m → Fin t) (b₀ : BitString m) (r_j : Fin t) (b_j : Bool) :
        embedNo (Function.update r₀ jStar r_j) (Function.update b₀ jStar b_j) =
          embedSpike r₀ b₀ jStar (fun i ↦ decide (r_j = i ∧ b_j = true)) := by
      ext i j
      by_cases hj : j = jStar
      · subst hj; simp [embedNo, embedSpike]
      · simp [embedNo, embedSpike, hj]
    unfold noLeaf noKernel Q
    rw [hRB, ← PMF.uniformOfFintype_prod (Fin t) Bool]
    simp only [PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def, hemb]
    congr 1 with r₀ : 1
    ext ℓ
    simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype]
    simp_rw [Finset.mul_sum]
    conv_rhs => arg 2; ext r_j; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₀ _ ↦
      Finset.sum_congr rfl fun r_j _ ↦ Finset.sum_congr rfl fun b_j _ ↦ ?_
    split_ifs <;> ring
  -- Bound `dist (noKernel r₀ jStar) (Q r₀ jStar 1)` via `hellingerSq`.
  have hdist_r0 (r₀ : Fin m → Fin t) (jStar : Fin m) :
      dist (noKernel r₀ jStar) (Q r₀ jStar fun _ ↦ true) ^ 2 ≤
        8 * (t : ℝ) * ∑ r_j : Fin t,
          hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) := by
    have hconv := dist_bind_left_le (PMF.uniformOfFintype (Fin t × Bool))
      (fun p ↦ Q r₀ jStar (fun i ↦ decide (p.1 = i ∧ p.2 = true)))
      (Q r₀ jStar fun _ ↦ true)
    rw [Fintype.sum_prod_type] at hconv
    have hsplit_b (r_j : Fin t) :
        ∑ b_j : Bool, (PMF.uniformOfFintype (Fin t × Bool) (r_j, b_j)).toReal *
          dist (Q r₀ jStar fun i ↦ decide (r_j = i ∧ b_j = true))
            (Q r₀ jStar fun _ ↦ true) ≤
        ((2 * (t : ℝ))⁻¹) *
          (2 * dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true) +
            dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j))) := by
      rw [Fintype.sum_bool]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_mul,
        ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Bool.false_eq_true, and_false, decide_false,
        and_true]
      have heq_r : (fun i : Fin t ↦ decide (r_j = i)) = (fun i : Fin t ↦ decide (i = r_j)) := by
        ext i; exact decide_eq_decide.mpr eq_comm
      rw [heq_r]
      have htri : dist (Q r₀ jStar fun i ↦ decide (i = r_j)) (Q r₀ jStar fun _ ↦ true) ≤
          dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) +
            dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true) := by
        rw [dist_comm (Q r₀ jStar fun _ ↦ false)]
        exact dist_triangle _ _ _
      have htpos : (0 : ℝ) < (t * 2 : ℝ)⁻¹ := by positivity
      have hinv : ((t : ℝ) * 2)⁻¹ = (2 * (t : ℝ))⁻¹ := by ring
      rw [hinv] at htpos ⊢
      nlinarith
    have htpos : (t : ℝ) ≠ 0 := by positivity
    have hstep1 : dist (noKernel r₀ jStar) (Q r₀ jStar fun _ ↦ true) ≤
        dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true) +
          (2 * (t : ℝ))⁻¹ * ∑ r_j : Fin t,
            dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) := by
      refine hconv.trans ((Finset.sum_le_sum fun r_j _ ↦ hsplit_b r_j).trans ?_)
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring_nf
      exact le_rfl
    -- Bound each `dist` by `√2 * hellingerDist`.
    have hd_le_h (A B : PMF (Fin P.leafCount)) : dist A B ≤ Real.sqrt 2 * hellingerDist A B := by
      have hsq := dist_sq_le_two_mul_hellingerSq A B
      have hrhs : 0 ≤ Real.sqrt 2 * hellingerDist A B :=
        mul_nonneg (Real.sqrt_nonneg 2) (hellingerDist_nonneg A B)
      rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_sq hrhs]
      refine Real.sqrt_le_sqrt ?_
      calc dist A B ^ 2 ≤ 2 * hellingerSq A B := hsq
        _ = (Real.sqrt 2 * hellingerDist A B) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num), hellingerDist_sq]
    set S := ∑ r_j : Fin t,
      hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j))
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ hellingerSq_nonneg _ _
    have hmainH : hellingerDist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true) ≤
        Real.sqrt t * Real.sqrt S := by
      rw [hellingerDist, ← Real.sqrt_mul (Nat.cast_nonneg t)]
      exact Real.sqrt_le_sqrt (hQ_rect r₀ jStar)
    have hsumD : ∑ r_j : Fin t,
          dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) ≤
        Real.sqrt 2 * (Real.sqrt t * Real.sqrt S) := by
      calc ∑ r_j : Fin t,
            dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j))
          ≤ ∑ r_j : Fin t, Real.sqrt 2 *
              hellingerDist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) :=
            Finset.sum_le_sum fun r_j _ ↦ hd_le_h _ _
        _ = Real.sqrt 2 * ∑ r_j : Fin t,
              hellingerDist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) := by
            rw [← Finset.mul_sum]
        _ ≤ Real.sqrt 2 * (Real.sqrt S * Real.sqrt t) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
            have hcs := sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin t))
              (fun r_j ↦ hellingerDist (Q r₀ jStar fun _ ↦ false)
                (Q r₀ jStar fun i ↦ decide (i = r_j)))
              (fun _ ↦ 1)
            simpa [hellingerDist_sq, S] using hcs
        _ = Real.sqrt 2 * (Real.sqrt t * Real.sqrt S) := by ring
    have htot : dist (noKernel r₀ jStar) (Q r₀ jStar fun _ ↦ true) ≤
        2 * Real.sqrt 2 * (Real.sqrt t * Real.sqrt S) := by
      have h0 := hd_le_h (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true)
      have h1 : dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun _ ↦ true) ≤
          Real.sqrt 2 * (Real.sqrt t * Real.sqrt S) :=
        h0.trans (mul_le_mul_of_nonneg_left hmainH (Real.sqrt_nonneg 2))
      have htge1 : (1 : ℝ) ≤ 2 * t := by exact_mod_cast (by omega : 1 ≤ 2 * t)
      have h2 : (2 * (t : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ htge1
      have hprod0 : 0 ≤ Real.sqrt 2 * (Real.sqrt t * Real.sqrt S) := by positivity
      have h3 : (2 * (t : ℝ))⁻¹ * ∑ r_j : Fin t,
            dist (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) ≤
          1 * (Real.sqrt 2 * (Real.sqrt t * Real.sqrt S)) :=
        mul_le_mul h2 hsumD (Finset.sum_nonneg fun _ _ ↦ dist_nonneg) zero_le_one
      linarith
    calc dist (noKernel r₀ jStar) (Q r₀ jStar fun _ ↦ true) ^ 2
        ≤ (2 * Real.sqrt 2 * (Real.sqrt t * Real.sqrt S)) ^ 2 :=
          pow_le_pow_left₀ dist_nonneg htot 2
      _ = 8 * (t : ℝ) * S := by
          calc (2 * Real.sqrt 2 * (Real.sqrt t * Real.sqrt S)) ^ 2
              = 4 * Real.sqrt 2 ^ 2 * Real.sqrt t ^ 2 * Real.sqrt S ^ 2 := by ring
            _ = 8 * (t : ℝ) * S := by
                rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg t), Real.sq_sqrt hS0]
                ring
  -- Step 5: Link `∑ jStar, 𝔼_r [hellingerSq]` to `P.depth ≤ c` via Jensen–Shannon + subadditivity.
  let unifR := PMF.uniformOfFintype (Fin m → Fin t)
  have hInfoSum :
      ∑ jStar : Fin m, ∑ r₀ : Fin m → Fin t, (unifR r₀).toReal *
          ∑ r_j : Fin t,
            hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) ≤
        2 * Real.log 2 * (t : ℝ) * c := by
    -- Reindex `(r₀, r_j)` by `r = Function.update r₀ jStar r_j`.
    have hreindex (jStar : Fin m) :
        ∑ r₀ : Fin m → Fin t, (unifR r₀).toReal *
            ∑ r_j : Fin t,
              hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) =
          (t : ℝ) * ∑ r : Fin m → Fin t, (unifR r).toReal *
            hellingerSq (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar)) := by
      have hQinv (r₀ : Fin m → Fin t) (r_j : Fin t) (u : Fin t → Bool) :
          Q (Function.update r₀ jStar r_j) jStar u = Q r₀ jStar u := by
        refine congrArg (PMF.map · _) (funext fun b₀ ↦
          congrArg P.leaf (funext fun i ↦ funext fun j ↦ ?_))
        by_cases hj : j = jStar
        · subst hj; simp [embedSpike]
        · simp [embedSpike, hj]
      have hupd := congrArg (fun ν : PMF (Fin m → Fin t) ↦
          ∑ r : Fin m → Fin t, (ν r).toReal *
            hellingerSq (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar)))
        (uniformOfFintype_update (γ := Fin t) jStar)
      simp only [sum_bind_mul, sum_map_mul] at hupd
      rw [← hupd]
      simp_rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r₀ _ ↦ ?_
      refine Finset.sum_congr rfl fun r_j _ ↦ ?_
      rw [hQinv r₀ r_j, hQinv r₀ r_j, Function.update_self]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, unifR]
      have htpos : (t : ℝ) ≠ 0 := by positivity
      field_simp
    simp_rw [hreindex, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    -- For each fixed `r`, bound `∑ jStar, hellingerSq (Q r jStar 0) (Q r jStar (e (r jStar)))`.
    have hperR (r : Fin m → Fin t) :
        ∑ jStar : Fin m,
            hellingerSq (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar)) ≤
          2 * Real.log 2 * c := by
      let fullJoint : PMF (Fin P.leafCount × BitString m) :=
        (PMF.uniformOfFintype (BitString m)).map fun b ↦ (P.leaf (embedNo r b), b)
      have hcoordJoint (jStar : Fin m) :
          ((PMF.uniformOfFintype Bool).bind fun bit ↦
            (if bit then Q r jStar (fun i ↦ decide (i = r jStar))
              else Q r jStar (fun _ ↦ false)).map (fun ℓ ↦ (ℓ, bit))) =
          fullJoint.map (fun pair ↦ (pair.1, pair.2 jStar)) := by
        have hupdB := uniformOfFintype_update (γ := Bool) jStar
        unfold fullJoint Q
        conv_rhs => rw [← hupdB]
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
        congr 1 with bit : 1
        ext ⟨ℓ, bit'⟩
        have hembBit (b₀ : BitString m) :
            embedNo r (Function.update b₀ jStar bit) =
              embedSpike r b₀ jStar (if bit then fun i ↦ decide (i =
                r jStar) else fun _ ↦ false) := by
          ext i j
          by_cases hj : j = jStar
          · subst hj
            cases bit
            · simp [embedNo, embedSpike]
            · simp only [embedNo, embedSpike, ↓reduceIte, Function.update_self, and_true]
              exact decide_eq_decide.mpr eq_comm
          · simp [embedNo, embedSpike, hj]
        cases bit <;> simp [PMF.map_comp, Function.comp_def, hembBit]
      have hjs_sum :
          ∑ jStar : Fin m,
              hellingerSq (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar)) ≤
            2 * Real.log 2 * ∑ jStar : Fin m,
              (1 - conditionalEntropy (fullJoint.map fun pair ↦ (pair.1, pair.2 jStar))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun jStar _ ↦ ?_
        have hjs := hellingerSq_le_two_mul_log_two_mul_one_sub_condEntropy
          (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar))
        rwa [hcoordJoint jStar] at hjs
      -- Subadditivity: `conditionalEntropy fullJoint ≤ ∑ jStar, conditionalEntropy (...)`.
      have hsub := conditionalEntropy_le_sum_coord fullJoint
      have hlog2pow (n : ℕ) : Real.logb 2 ((2 : ℝ) ^ n) = n := by
        rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
      -- Exact entropy of `fullJoint`: `entropy fullJoint = m`, so `m - conditionalEntropy = H(L)`.
      have hentFull : entropy fullJoint = m := by
        have hinj : Function.Injective (fun b : BitString m ↦ (P.leaf (embedNo r b), b)) :=
          fun _ _ h ↦ (Prod.mk.inj h).2
        rw [entropy_map_of_injective _ hinj, entropy_uniform]
        simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
          Nat.cast_ofNat]
        exact hlog2pow m
      have hleafBound : entropy (fullJoint.map Prod.fst) ≤ c := by
        have h1 := entropy_le_log_card (fullJoint.map Prod.fst)
        rw [Fintype.card_fin] at h1
        have h2 : Real.logb 2 P.leafCount ≤ P.depth :=
          calc Real.logb 2 P.leafCount ≤ Real.logb 2 ((2 : ℝ) ^ P.depth) :=
                Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast P.leafCount_pos)
                  (by exact_mod_cast P.leafCount_le_two_pow_depth)
            _ = P.depth := hlog2pow P.depth
        exact (h1.trans h2).trans (by exact_mod_cast hPdepth)
      have hsum1 : ∑ jStar : Fin m,
            (1 - conditionalEntropy (fullJoint.map fun pair ↦ (pair.1, pair.2 jStar))) ≤ c := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        have hceDef : conditionalEntropy fullJoint =
            entropy fullJoint - entropy (fullJoint.map Prod.fst) := rfl
        linarith
      refine hjs_sum.trans ?_
      exact mul_le_mul_of_nonneg_left hsum1 (mul_nonneg (by norm_num) (Real.log_nonneg one_le_two))
    calc (t : ℝ) * ∑ r : Fin m → Fin t, ∑ jStar : Fin m,
            (unifR r).toReal *
              hellingerSq (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar))
        = (t : ℝ) * ∑ r : Fin m → Fin t,
            (unifR r).toReal * ∑ jStar : Fin m,
              hellingerSq (Q r jStar fun _ ↦ false) (Q r jStar fun i ↦ decide (i = r jStar)) := by
          congr 1; exact Finset.sum_congr rfl fun _ _ ↦ (Finset.mul_sum _ _ _).symm
      _ ≤ (t : ℝ) * ∑ r : Fin m → Fin t, (unifR r).toReal * (2 * Real.log 2 * c) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ ↦
            mul_le_mul_of_nonneg_left (hperR r) ENNReal.toReal_nonneg) (Nat.cast_nonneg t)
      _ = 2 * Real.log 2 * (t : ℝ) * c := by
          rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
          ring
  -- Step 6: Combine `herr_avg`, convexity of `(·)^2` over `(jStar, r₀)`, `hdist_r0`, and
  -- `hInfoSum`.
  by_cases hpos : 1 - 2 * δ ≤ 0
  · have hzero : 1 - 2 * δ = 0 := by linarith
    rw [hzero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg one_le_two))
      (sq_nonneg _)) (Nat.cast_nonneg c)
  · push Not at hpos
    have htv_r0 (jStar : Fin m) :
        dist noLeaf (yesLeaf jStar) ^ 2 ≤
          ∑ r₀ : Fin m → Fin t, (unifR r₀).toReal *
            dist (noKernel r₀ jStar) (Q r₀ jStar fun _ ↦ true) ^ 2 := by
      -- Map `(r₀, ℓ) ↦ ℓ` does not increase distance, and `dist_bind_pair_sq_le` bounds square!
      rw [hnoEq jStar, hyesEq jStar]
      have h1 : (unifR.bind fun r₀ ↦ (noKernel r₀ jStar).map (r₀, ·)).map Prod.snd =
          unifR.bind fun r₀ ↦ noKernel r₀ jStar := by
        rw [PMF.map_bind]
        exact congrArg unifR.bind (funext fun r₀ ↦ (PMF.map_comp _ _ _).trans (PMF.map_id _))
      have h2 : (unifR.bind fun r₀ ↦ (Q r₀ jStar fun _ ↦ true).map (r₀, ·)).map Prod.snd =
          unifR.bind fun r₀ ↦ Q r₀ jStar fun _ ↦ true := by
        rw [PMF.map_bind]
        exact congrArg unifR.bind (funext fun r₀ ↦ (PMF.map_comp _ _ _).trans (PMF.map_id _))
      rw [← h1, ← h2]
      refine (pow_le_pow_left₀ dist_nonneg (PMF.dist_map_le _ _ Prod.snd) 2).trans ?_
      exact dist_bind_pair_sq_le unifR (fun r₀ ↦ noKernel r₀ jStar)
        (fun r₀ ↦ Q r₀ jStar fun _ ↦ true)
    have hcs_m := sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
      (fun jStar ↦ dist noLeaf (yesLeaf jStar)) (fun _ ↦ 1)
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hcs_m
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : (1 - 2 * δ) * m ≤ ∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) := by
      linarith [(le_inv_mul_iff₀ hmpos).mp herr_avg]
    have h2 : ((1 - 2 * δ) * m) ^ 2 ≤
        (Real.sqrt (∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) ^ 2) * Real.sqrt m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (h1.trans hcs_m) 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
      Real.sq_sqrt hmpos.le] at h2
    have h3 : (1 - 2 * δ) ^ 2 * m ≤ ∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) ^ 2 := by
      nlinarith
    calc (1 - 2 * δ) ^ 2 * m
        ≤ ∑ jStar : Fin m, dist noLeaf (yesLeaf jStar) ^ 2 := h3
      _ ≤ ∑ jStar : Fin m, ∑ r₀ : Fin m → Fin t, (unifR r₀).toReal *
            dist (noKernel r₀ jStar) (Q r₀ jStar fun _ ↦ true) ^ 2 :=
          Finset.sum_le_sum fun jStar _ ↦ htv_r0 jStar
      _ ≤ ∑ jStar : Fin m, ∑ r₀ : Fin m → Fin t, (unifR r₀).toReal *
            (8 * (t : ℝ) * ∑ r_j : Fin t,
              hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j))) :=
          Finset.sum_le_sum fun jStar _ ↦ Finset.sum_le_sum fun r₀ _ ↦
            mul_le_mul_of_nonneg_left (hdist_r0 r₀ jStar) ENNReal.toReal_nonneg
      _ = 8 * (t : ℝ) * ∑ jStar : Fin m, ∑ r₀ : Fin m → Fin t, (unifR r₀).toReal *
            ∑ r_j : Fin t,
              hellingerSq (Q r₀ jStar fun _ ↦ false) (Q r₀ jStar fun i ↦ decide (i = r_j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun jStar _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r₀ _ ↦ by ring
      _ ≤ 8 * (t : ℝ) * (2 * Real.log 2 * (t : ℝ) * c) :=
          mul_le_mul_of_nonneg_left hInfoSum (by positivity)
      _ = 16 * Real.log 2 * (t : ℝ) ^ 2 * c := by ring

-- Concrete non-vacuity sanity check on 3-party unique-intersection promise
example : ∃ x : Fin 3 → BitString 2,
    UniqueDisjointPromise x ∧ multipartyDisjointness x = true :=
  ⟨fun _ j ↦ decide (j = 0),
    Or.inr ⟨0, fun _ ↦ rfl, fun j' hj' ↦ by
      have : j' = 1 := by omega
      subst this
      simp⟩,
    by decide⟩

end MultipartyDisjointnessLowerBound

end Cslib.Communication
