/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Defs
public import CslibFrontier.Algorithms.Lean.Query.Arith.Karatsuba.Defs
public import CslibFrontier.Init
public import Mathlib.RingTheory.PowerSeries.Inverse

import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Cost
import CslibFrontier.Algorithms.Lean.Query.Arith.Karatsuba.Cost
import CslibFrontier.Algorithms.Lean.Query.Arith.Lemmas
import CslibFrontier.Algorithms.Lean.Query.FreeM.MOfFn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Newton–Raphson Power Series Inversion and Division in the Arithmetic Query Model

This module formalizes representation-polymorphic Newton–Raphson formal power series inversion and
truncated power series division
in `Cslib`'s arithmetic query monad `Cslib.FreeM (Cslib.Query.ArithQuery α)` under standard Lean
axioms, together with concrete query-complexity instantiations via `Cslib.Query.fftMul` and
`Cslib.Query.Karatsuba.mulFit`.

## Main definitions

* `CslibFrontier.Query.IsTruncMulProg`: specification of a dyadic truncated polynomial multiplier.
* `CslibFrontier.Query.newtonInvProg`: Newton–Raphson power series inversion to precision `2 ^ K`
  using only `[Zero α] [One α]`.
* `CslibFrontier.Query.divSeriesProg`: truncated power series division `ψ / φ mod X ^ (2 ^ K)`.
* `CslibFrontier.Query.fftTruncMul`: dyadic truncated multiplication via `Cslib.Query.fftMul`.
* `CslibFrontier.Query.karatsubaTruncMul`: dyadic truncated multiplication via
  `Cslib.Query.Karatsuba.mulFit`.

## Main results

* `CslibFrontier.Query.eval_newtonInvProg_eq`, `CslibFrontier.Query.eval_divSeriesProg_eq`:
  correctness of `newtonInvProg` and `divSeriesProg` under `Cslib.Query.ArithQuery.honest`.
* `CslibFrontier.Query.countQueries_newtonInvProg_le`: `newtonInvProg` makes at most
  `3 * m K + (2 ^ K - 1)` queries under *every* oracle whenever `2 * m k ≤ m (k + 1)`.
* `CslibFrontier.Query.countQueries_divSeriesProg_le`: **von zur Gathen–Gerhard** —
  `divSeriesProg` makes at most `4 * m K + 2 ^ K` queries under *every* oracle.
* `CslibFrontier.Query.countQueries_divSeriesFFT_le`: FFT-backed power series division makes at
  most `56 * 2 ^ K * (K + 1) + 2 ^ K` queries (`O(N log N)`).
* `CslibFrontier.Query.countQueries_divSeriesKaratsuba_le`: Karatsuba-backed power series division
  makes at most `36 * 3 ^ K + 2 ^ K` queries (`O(N ^ (log₂ 3))`).
-/

public section

namespace CslibFrontier.Query

/-- Specification that a family of arithmetic-query programs `mulPow2 k` computes the low `2 ^ k`
coefficients of the Cauchy product of two inputs under `Cslib.Query.ArithQuery.honest`. -/
def IsTruncMulProg {α : Type} [CommRing α]
    (mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)) : Prop :=
  ∀ (k : ℕ) (a b : Fin (2 ^ k) → α) (i : Fin (2 ^ k)),
    ((mulPow2 k a b).eval Cslib.Query.ArithQuery.honest) i =
      ∑ j : Fin (i.val + 1),
        a ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩ *
          b ⟨i.val - j.val, by have := i.isLt; omega⟩

/-- Constructive Newton–Raphson power series inversion in `Cslib.FreeM (ArithQuery α)`, using only
`[Zero α] [One α]`. -/
def newtonInvProg {α : Type} [Zero α] [One α]
    (mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)) :
    (k : ℕ) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)
  | 0, _ => pure (fun _ ↦ 1)
  | k + 1, φ => do
    let φLow : Fin (2 ^ k) → α := fun i ↦
      φ ⟨i.val, lt_trans i.isLt (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self k))⟩
    let g ← newtonInvProg mulPow2 k φLow
    let gPad : Fin (2 ^ (k + 1)) → α := fun i ↦
      if h : i.val < 2 ^ k then g ⟨i.val, h⟩ else 0
    let p ← mulPow2 (k + 1) φ gPad
    let pHigh : Fin (2 ^ k) → α := fun j ↦
      p ⟨2 ^ k + j.val, by
        have := j.isLt
        have : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        omega⟩
    let qHigh ← mulPow2 k g pHigh
    let negQ ← List.Vector.mOfFn fun j : Fin (2 ^ k) ↦
      Cslib.Query.ArithQuery.doSub (0 : α) (qHigh j)
    return fun i : Fin (2 ^ (k + 1)) ↦
      if h : i.val < 2 ^ k then g ⟨i.val, h⟩
      else negQ.get ⟨i.val - 2 ^ k, by
        have hi : i.val < 2 ^ k * 2 := by simpa only [pow_succ] using i.isLt
        omega⟩

/-- Constructive truncated power series division `ψ / φ mod X ^ (2 ^ K)` in
`Cslib.FreeM (ArithQuery α)`. -/
def divSeriesProg {α : Type} [Zero α] [One α]
    (mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α))
    (K : ℕ) (ψ φ : Fin (2 ^ K) → α) :
    Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ K) → α) := do
  let inv ← newtonInvProg mulPow2 K φ
  mulPow2 K ψ inv

private lemma eval_honest_doSub {α : Type} [Add α] [Sub α] [Mul α] (a b : α) :
    (Cslib.Query.ArithQuery.doSub a b).eval Cslib.Query.ArithQuery.honest = a - b :=
  rfl

private lemma cost_unit_doSub {α : Type}
    (oracle : {ι : Type} → Cslib.Query.ArithQuery α ι → ι) (a b : α) :
    (Cslib.Query.ArithQuery.doSub a b).cost oracle (fun _ ↦ (1 : ℕ)) = 1 :=
  rfl

/-- Honest evaluation of `newtonInvProg` agrees with `PowerSeries.invOfUnit φSeries 1` on all
coefficients `< 2 ^ K` whenever `constantCoeff φSeries = 1`. -/
theorem eval_newtonInvProg_eq {α : Type} [CommRing α]
    {mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)}
    (hmul : IsTruncMulProg mulPow2) {φSeries : _root_.PowerSeries α}
    (hφ₀ : _root_.PowerSeries.constantCoeff φSeries = 1) :
    ∀ (K : ℕ) (φ : Fin (2 ^ K) → α),
      (∀ i : Fin (2 ^ K), φ i = _root_.PowerSeries.coeff i.val φSeries) →
      ∀ i : Fin (2 ^ K),
        ((newtonInvProg mulPow2 K φ).eval Cslib.Query.ArithQuery.honest) i =
          _root_.PowerSeries.coeff i.val (_root_.PowerSeries.invOfUnit φSeries 1)
  | 0, φ, _, i => by
    have hi0 : i.val = 0 := by have := i.isLt; omega
    simp only [newtonInvProg, Cslib.FreeM.eval_pure, hi0,
      _root_.PowerSeries.coeff_zero_eq_constantCoeff_apply,
      _root_.PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  | k + 1, φ, hφ, i => by
    have hφ_unit : _root_.PowerSeries.constantCoeff φSeries = ↑(1 : αˣ) := hφ₀
    have hlt_pow : ∀ n < 2 ^ k, n < 2 ^ (k + 1) := fun n hn ↦
      lt_trans hn (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self k))
    let φLow : Fin (2 ^ k) → α := fun j ↦ φ ⟨j.val, hlt_pow j.val j.isLt⟩
    have hφLow : ∀ j : Fin (2 ^ k), φLow j = _root_.PowerSeries.coeff j.val φSeries :=
      fun j ↦ hφ ⟨j.val, hlt_pow j.val j.isLt⟩
    set g := (newtonInvProg mulPow2 k φLow).eval Cslib.Query.ArithQuery.honest
    have hg_ih : ∀ j : Fin (2 ^ k),
        g j = _root_.PowerSeries.coeff j.val (_root_.PowerSeries.invOfUnit φSeries 1) :=
      eval_newtonInvProg_eq hmul hφ₀ k φLow hφLow
    set G : _root_.PowerSeries α :=
      _root_.PowerSeries.mk fun n ↦ if h : n < 2 ^ k then g ⟨n, h⟩ else 0
    have hG_coeff : ∀ n, _root_.PowerSeries.coeff n G =
        if h : n < 2 ^ k then g ⟨n, h⟩ else 0 :=
      fun n ↦ _root_.PowerSeries.coeff_mk n _
    have hres_low : ∀ n < 2 ^ k, _root_.PowerSeries.coeff n (1 - φSeries * G) = 0 := by
      intro n hn
      have hG_agree : _root_.PowerSeries.coeff n (φSeries * G) =
          _root_.PowerSeries.coeff n (φSeries * _root_.PowerSeries.invOfUnit φSeries 1) := by
        rw [_root_.PowerSeries.coeff_mul, _root_.PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
        rw [Finset.mem_antidiagonal] at hab
        have hb : b < 2 ^ k := by omega
        rw [hG_coeff, dite_eq_left hb, hg_ih ⟨b, hb⟩]
      rw [map_sub, hG_agree, mul_comm φSeries, _root_.PowerSeries.invOfUnit_mul _ 1 hφ_unit,
        sub_self]
    set nextG : _root_.PowerSeries α := G + G * (1 - φSeries * G)
    have hstep_inv : ∀ n < 2 ^ (k + 1),
        _root_.PowerSeries.coeff n nextG =
          _root_.PowerSeries.coeff n (_root_.PowerSeries.invOfUnit φSeries 1) := by
      intro n hn
      have hsq : 1 - φSeries * nextG = (1 - φSeries * G) ^ 2 := by dsimp only [nextG]; ring
      have hdiff : _root_.PowerSeries.invOfUnit φSeries 1 - nextG =
          _root_.PowerSeries.invOfUnit φSeries 1 * (1 - φSeries * nextG) := by
        rw [mul_sub, mul_one, ← mul_assoc, _root_.PowerSeries.invOfUnit_mul _ 1 hφ_unit, one_mul]
      have hzero : _root_.PowerSeries.coeff n
          (_root_.PowerSeries.invOfUnit φSeries 1 - nextG) = 0 := by
        rw [hdiff, hsq, sq, _root_.PowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        rintro ⟨a, b⟩ hab
        rw [Finset.mem_antidiagonal] at hab
        rw [_root_.PowerSeries.coeff_mul]
        have hinner : (∑ x ∈ Finset.antidiagonal b,
            _root_.PowerSeries.coeff x.1 (1 - φSeries * G) *
              _root_.PowerSeries.coeff x.2 (1 - φSeries * G)) = 0 := by
          apply Finset.sum_eq_zero
          rintro ⟨c, d⟩ hcd
          rw [Finset.mem_antidiagonal] at hcd
          have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
          by_cases hc : c < 2 ^ k
          · rw [hres_low c hc, zero_mul]
          · rw [hres_low d (by omega), mul_zero]
        rw [hinner, mul_zero]
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero.symm
    rw [← hstep_inv i.val i.isLt]
    let gPad : Fin (2 ^ (k + 1)) → α := fun m ↦
      if h : m.val < 2 ^ k then g ⟨m.val, h⟩ else 0
    set p := (mulPow2 (k + 1) φ gPad).eval Cslib.Query.ArithQuery.honest
    have hp_eq : ∀ m : Fin (2 ^ (k + 1)),
        p m = _root_.PowerSeries.coeff m.val (φSeries * G) := by
      intro m
      dsimp only [p]
      rw [hmul (k + 1) φ gPad m, _root_.PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b ↦ _root_.PowerSeries.coeff a φSeries * _root_.PowerSeries.coeff b G),
        ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hφ ⟨a.val, by have := a.isLt; have := m.isLt; omega⟩]
      congr 1
      simp only [gPad, hG_coeff]
    let pHigh : Fin (2 ^ k) → α := fun j ↦
      p ⟨2 ^ k + j.val, by
        have := j.isLt
        have : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        omega⟩
    set qHigh := (mulPow2 k g pHigh).eval Cslib.Query.ArithQuery.honest
    simp only [newtonInvProg, Cslib.FreeM.eval_bind, Cslib.FreeM.eval_pure,
      Cslib.FreeM.eval_mOfFn, List.Vector.get_ofFn, eval_honest_doSub, zero_sub]
    change (if h : i.val < 2 ^ k then g ⟨i.val, h⟩ else -qHigh ⟨i.val - 2 ^ k, _⟩) =
      _root_.PowerSeries.coeff i.val (G + G * (1 - φSeries * G))
    rw [map_add]
    split_ifs with hi_lt
    · have hzero : _root_.PowerSeries.coeff i.val (G * (1 - φSeries * G)) = 0 := by
        rw [_root_.PowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        rintro ⟨a, b⟩ hab
        rw [Finset.mem_antidiagonal] at hab
        rw [hres_low b (by omega), mul_zero]
      rw [hzero, add_zero, hG_coeff, dite_eq_left hi_lt]
    · have hG0 : _root_.PowerSeries.coeff i.val G = 0 := by
        rw [hG_coeff, dite_eq_right hi_lt]
      rw [hG0, zero_add]
      set r := i.val - 2 ^ k
      have hr_lt : r < 2 ^ k := by
        have hi : i.val < 2 ^ k * 2 := by simpa only [pow_succ] using i.isLt
        omega
      have hq : qHigh ⟨r, hr_lt⟩ =
          ∑ a ∈ Finset.range (r + 1),
            (if h : a < 2 ^ k then g ⟨a, h⟩ else 0) *
              (if h : r - a < 2 ^ k then pHigh ⟨r - a, h⟩ else 0) := by
        dsimp only [qHigh]
        rw [hmul k g pHigh ⟨r, hr_lt⟩, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        have ha1 : a.val < 2 ^ k := by have := a.isLt; omega
        have ha2 : r - a.val < 2 ^ k := by omega
        rw [dite_eq_left ha1, dite_eq_left ha2]
      rw [hq, _root_.PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b ↦ _root_.PowerSeries.coeff a G * _root_.PowerSeries.coeff b (1 - φSeries * G))]
      have hsub : r + 1 ≤ i.val + 1 := by omega
      rw [← Finset.sum_subset (Finset.range_mono hsub)]
      · rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a ha ↦ ?_
        rw [Finset.mem_range] at ha
        have ha_lt : a < 2 ^ k := by omega
        have hra_lt : r - a < 2 ^ k := by omega
        have hb_eq : i.val - a = 2 ^ k + (r - a) := by omega
        have hb_lt : 2 ^ k + (r - a) < 2 ^ (k + 1) := by
          have : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
          omega
        rw [dite_eq_left ha_lt, dite_eq_left hra_lt, hG_coeff, dite_eq_left ha_lt, hb_eq, map_sub,
          _root_.PowerSeries.coeff_one,
          ite_eq_right (by have := Nat.one_le_two_pow (n := k); omega),
          zero_sub, ← hp_eq ⟨2 ^ k + (r - a), hb_lt⟩]
        dsimp only [pHigh]
        ring
      · intro a ha_all ha_not
        rw [Finset.mem_range] at ha_all ha_not
        by_cases ha_lt : a < 2 ^ k
        · rw [hres_low (i.val - a) (by omega), mul_zero]
        · rw [hG_coeff, dite_eq_right ha_lt, zero_mul]

/-- **Honest Evaluation of `divSeriesProg`**. -/
theorem eval_divSeriesProg_eq {α : Type} [CommRing α]
    {mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)}
    (hmul : IsTruncMulProg mulPow2) {ψSeries φSeries : _root_.PowerSeries α}
    (hφ₀ : _root_.PowerSeries.constantCoeff φSeries = 1)
    (K : ℕ) (ψ φ : Fin (2 ^ K) → α)
    (hψ : ∀ i : Fin (2 ^ K), ψ i = _root_.PowerSeries.coeff i.val ψSeries)
    (hφ : ∀ i : Fin (2 ^ K), φ i = _root_.PowerSeries.coeff i.val φSeries)
    (i : Fin (2 ^ K)) :
    ((divSeriesProg mulPow2 K ψ φ).eval Cslib.Query.ArithQuery.honest) i =
      _root_.PowerSeries.coeff i.val (ψSeries * _root_.PowerSeries.invOfUnit φSeries 1) := by
  simp only [divSeriesProg, Cslib.FreeM.eval_bind]
  rw [hmul K ψ _ i, _root_.PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ _root_.PowerSeries.coeff a ψSeries *
        _root_.PowerSeries.coeff b (_root_.PowerSeries.invOfUnit φSeries 1)),
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hψ ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
    eval_newtonInvProg_eq hmul hφ₀ K φ hφ ⟨i.val - j.val, by have := i.isLt; omega⟩]

/-- **Von zur Gathen & Gerhard (Inversion Query Bound)**: at most
`3 * m K + (2 ^ K - 1)` queries under every oracle.
-/
theorem countQueries_newtonInvProg_le {α : Type} [Zero α] [One α]
    (oracle : {ι : Type} → Cslib.Query.ArithQuery α ι → ι)
    {mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)}
    {m : ℕ → ℕ}
    (hm_bound : ∀ k a b, (mulPow2 k a b).countQueries oracle ≤ m k)
    (hm_super : ∀ k, 2 * m k ≤ m (k + 1)) :
    ∀ (K : ℕ) (φ : Fin (2 ^ K) → α),
      (newtonInvProg mulPow2 K φ).countQueries oracle ≤ 3 * m K + (2 ^ K - 1)
  | 0, _ => by simp only [newtonInvProg, Cslib.FreeM.countQueries_pure, zero_le]
  | k + 1, φ => by
    let φLow : Fin (2 ^ k) → α := fun i ↦
      φ ⟨i.val, lt_trans i.isLt (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self k))⟩
    let g := (newtonInvProg mulPow2 k φLow).eval oracle
    let gPad : Fin (2 ^ (k + 1)) → α := fun i ↦
      if h : i.val < 2 ^ k then g ⟨i.val, h⟩ else 0
    let p := (mulPow2 (k + 1) φ gPad).eval oracle
    let pHigh : Fin (2 ^ k) → α := fun j ↦
      p ⟨2 ^ k + j.val, by
        have := j.isLt
        have : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        omega⟩
    let qHigh := (mulPow2 k g pHigh).eval oracle
    simp only [newtonInvProg, Cslib.FreeM.countQueries_bind, Cslib.FreeM.countQueries_pure,
      add_zero]
    have hneg : (List.Vector.mOfFn fun j : Fin (2 ^ k) ↦
        Cslib.Query.ArithQuery.doSub (0 : α) (qHigh j)).countQueries oracle = 2 ^ k := by
      rw [Cslib.FreeM.countQueries_eq_cost_one, Cslib.FreeM.cost_mOfFn]
      simp only [cost_unit_doSub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    change (newtonInvProg mulPow2 k φLow).countQueries oracle +
      ((mulPow2 (k + 1) φ gPad).countQueries oracle +
        ((mulPow2 k g pHigh).countQueries oracle +
          (List.Vector.mOfFn fun j : Fin (2 ^ k) ↦
            Cslib.Query.ArithQuery.doSub (0 : α) (qHigh j)).countQueries oracle)) ≤
      3 * m (k + 1) + (2 ^ (k + 1) - 1)
    rw [hneg]
    have hih := countQueries_newtonInvProg_le oracle hm_bound hm_super k φLow
    have hm1 := hm_bound (k + 1) φ gPad
    have hm0 := hm_bound k g pHigh
    have hsup := hm_super k
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2k_succ : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    omega

/-- **Von zur Gathen & Gerhard (Division Query Bound)**: at most `4 * m K + 2 ^ K`
queries under every oracle.
-/
theorem countQueries_divSeriesProg_le {α : Type} [Zero α] [One α]
    (oracle : {ι : Type} → Cslib.Query.ArithQuery α ι → ι)
    {mulPow2 : (k : ℕ) → (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α) →
      Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α)}
    {m : ℕ → ℕ}
    (hm_bound : ∀ k a b, (mulPow2 k a b).countQueries oracle ≤ m k)
    (hm_super : ∀ k, 2 * m k ≤ m (k + 1))
    (K : ℕ) (ψ φ : Fin (2 ^ K) → α) :
    (divSeriesProg mulPow2 K ψ φ).countQueries oracle ≤ 4 * m K + 2 ^ K := by
  simp only [divSeriesProg, Cslib.FreeM.countQueries_bind]
  have hinv := countQueries_newtonInvProg_le oracle hm_bound hm_super K φ
  have hmul := hm_bound K ψ ((newtonInvProg mulPow2 K φ).eval oracle)
  have h2K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  omega

/-- Dyadic truncated multiplication via zero-padded `Cslib.Query.fftMul`. -/
def fftTruncMul {α : Type} [Zero α] [One α] (ω nInv : ℕ → α) (k : ℕ)
    (a b : Fin (2 ^ k) → α) :
    Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α) := do
  let aPad : Fin (2 ^ (k + 1)) → α := fun i ↦ if h : i.val < 2 ^ k then a ⟨i.val, h⟩ else 0
  let bPad : Fin (2 ^ (k + 1)) → α := fun i ↦ if h : i.val < 2 ^ k then b ⟨i.val, h⟩ else 0
  let prod ← Cslib.Query.fftMul k (ω k) (nInv k) aPad bPad
  return fun i : Fin (2 ^ k) ↦
    prod ⟨i.val, lt_trans i.isLt (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self k))⟩

/-- Dyadic truncated multiplication via `Cslib.Query.Karatsuba.mulFit`. -/
def karatsubaTruncMul {α : Type} [Zero α] (k : ℕ) (a b : Fin (2 ^ k) → α) :
    Cslib.FreeM (Cslib.Query.ArithQuery α) (Fin (2 ^ k) → α) := do
  let prod ← Cslib.Query.Karatsuba.mulFit (2 ^ k) (List.ofFn a) (List.ofFn b)
  return fun i : Fin (2 ^ k) ↦ prod.getD i.val 0

/-- FFT-backed truncated power series division makes `O(N log N)` (`≤ 56 * 2 ^ K * (K + 1) + 2 ^ K`)
queries under every oracle. -/
theorem countQueries_divSeriesFFT_le {α : Type} [Zero α] [One α]
    (oracle : {ι : Type} → Cslib.Query.ArithQuery α ι → ι)
    (ω nInv : ℕ → α) (K : ℕ) (ψ φ : Fin (2 ^ K) → α) :
    (divSeriesProg (fftTruncMul ω nInv) K ψ φ).countQueries oracle ≤
      56 * 2 ^ K * (K + 1) + 2 ^ K := by
  let m : ℕ → ℕ := fun k ↦
    3 * (2 ^ k * (k + 1)) + 4 * 2 ^ k + (2 ^ k - 1) + 3 * (2 ^ (k + 1) * (k + 1))
  have hm_eq : ∀ k a b, (fftTruncMul ω nInv k a b).countQueries oracle ≤ m k := fun k a b ↦ by
    simp only [fftTruncMul, Cslib.FreeM.countQueries_bind, Cslib.FreeM.countQueries_pure,
      add_zero, Cslib.Query.countQueries_fftMul, m, le_refl]
  have hm_sup : ∀ k, 2 * m k ≤ m (k + 1) := fun k ↦ by
    dsimp only [m]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have h3 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
    rw [h3, h2]
    set P := 2 ^ k
    have hs1 : P - 1 + 1 = P := Nat.sub_add_cancel h1
    have hs2 : 2 * P - 1 + 1 = 2 * P := Nat.sub_add_cancel (by omega)
    nlinarith
  have hd := countQueries_divSeriesProg_le oracle hm_eq hm_sup K ψ φ
  have hmK : m K ≤ 14 * 2 ^ K * (K + 1) := by
    dsimp only [m]
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
    rw [h2]
    set P := 2 ^ K
    have hs1 : P - 1 + 1 = P := Nat.sub_add_cancel h1
    nlinarith
  nlinarith

/-- Karatsuba-backed truncated power series division makes `O(N ^ (log₂ 3))`
(`≤ 36 * 3 ^ K + 2 ^ K`) queries under every oracle. -/
theorem countQueries_divSeriesKaratsuba_le {α : Type} [Zero α] [One α]
    (oracle : {ι : Type} → Cslib.Query.ArithQuery α ι → ι)
    (K : ℕ) (ψ φ : Fin (2 ^ K) → α) :
    (divSeriesProg karatsubaTruncMul K ψ φ).countQueries oracle ≤
      36 * 3 ^ K + 2 ^ K := by
  let m : ℕ → ℕ := fun k ↦ 9 * 3 ^ k
  have hm_le : ∀ k a b, (karatsubaTruncMul k a b).countQueries oracle ≤ m k := fun k a b ↦ by
    unfold karatsubaTruncMul
    rw [Cslib.FreeM.countQueries_bind, Cslib.FreeM.countQueries_pure, add_zero]
    simp only [Cslib.Query.ArithQuery.countQueries_eq_cost_weight_one,
      Cslib.Query.Karatsuba.cost_mulFit, one_mul, m]
    have h1 := Cslib.Query.Karatsuba.mulCount_two_pow k
    have h2 := Cslib.Query.Karatsuba.addCount_two_pow k
    have h3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
    omega
  have hm_sup : ∀ k, 2 * m k ≤ m (k + 1) := fun k ↦ by
    dsimp only [m]; rw [pow_succ]; omega
  have hd := countQueries_divSeriesProg_le oracle hm_le hm_sup K ψ φ
  dsimp only [m] at hd
  linarith

end CslibFrontier.Query
