/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AC0
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constant-Depth Subexponential Circuits for Logspace and Padded `AC⁰` Closure

Every language in nondeterministic logarithmic space (`Cslib.Complexity.NL`), and hence every
language in deterministic logarithmic space (`Cslib.Complexity.L`), is decided at every input
length $n$ by constant-depth unbounded-fan-in Boolean circuits of subexponential size
$O(2^{n^\varepsilon})$ for each fixed $\varepsilon > 0$
. Consequently, any polylogarithmically padded version of a language in `NL` or `L` lies in
`Cslib.Circuits.Boolean.AC0`, proved under standard Lean axioms.

## Main definitions

- `CslibFrontier.Circuits.intRoot`: integer $r$-th root $\lfloor n^{1/r} \rfloor$ for $r \ge 1$.
- `CslibFrontier.Circuits.paddedLanguage`: language obtained by evaluating a slice family
  on a prefix of length $m(N) \le N$ of an $N$-bit input.

## Main results

- `CslibFrontier.Circuits.nl_subexp_unbounded_circuits`,
  `CslibFrontier.Circuits.l_subexp_unbounded_circuits`:
  for every $r \ge 1$, languages in `NL` and `L` have constant-depth unbounded-fan-in circuits of
  size $O(2^{\lfloor n^{1/r} \rfloor})$.
- `CslibFrontier.Circuits.nl_subexp_unbounded_circuits_rpow`,
  `CslibFrontier.Circuits.l_subexp_unbounded_circuits_rpow`:
  real-exponent subexponential size bound $O(2^{n^\varepsilon})$ for every real $\varepsilon > 0$.
- `CslibFrontier.Circuits.mem_AC0_of_mem_NL_padded`,
  `CslibFrontier.Circuits.mem_AC0_of_mem_L_padded`:
  polylogarithmically padded languages from `NL` and `L` belong to `AC⁰`.
-/

public section

namespace CslibFrontier.Circuits

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing Turing.MultiTapeTM Turing.MultiTapeNTM

/-! ### 1. Integer $r$-th roots and exponent bounds -/

/-- The integer $r$-th root $\lfloor n^{1/r} \rfloor$ for $r \ge 1$ (`0` when `r = 0`). -/
def intRoot (r n : ℕ) : ℕ :=
  if hr : 1 ≤ r then
    ((Finset.range (n + 1)).filter fun m ↦ m ^ r ≤ n).max'
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos n), by
        rw [Nat.zero_pow (by omega)]; exact Nat.zero_le n⟩⟩
  else 0

/-- For $r \ge 1$, `(intRoot r n) ^ r ≤ n`. -/
theorem intRoot_pow_le {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : (intRoot r n) ^ r ≤ n := by
  unfold intRoot
  simp only [hr, ↓reduceDIte]
  exact (Finset.mem_filter.mp
    (Finset.max'_mem ((Finset.range (n + 1)).filter fun m ↦ m ^ r ≤ n) _)).2

/-- Galois connection for `intRoot`: when $r \ge 1$, `m ≤ intRoot r n ↔ m ^ r ≤ n`. -/
theorem le_intRoot_iff {r m n : ℕ} (hr : 1 ≤ r) : m ≤ intRoot r n ↔ m ^ r ≤ n := by
  constructor
  · intro hm
    exact (Nat.pow_le_pow_left hm r).trans (intRoot_pow_le hr n)
  · intro hpow
    have hmn : m ≤ n := by
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact Nat.zero_le n
      · calc m = m ^ 1 := (pow_one m).symm
          _ ≤ m ^ r := Nat.pow_le_pow_right hmpos hr
          _ ≤ n := hpow
    unfold intRoot
    simp only [hr, ↓reduceDIte]
    exact Finset.le_max' _ m
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmn), hpow⟩)

/-- Strict upper bound `n < (intRoot r n + 1) ^ r` for $r \ge 1$. -/
theorem lt_succ_intRoot_pow {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : n < (intRoot r n + 1) ^ r := by
  by_contra hle
  push Not at hle
  have h := (le_intRoot_iff hr).mpr hle
  omega

/-- Squaring `(intRoot (2 * r) n)` stays at most `intRoot r n` for $r \ge 1$. -/
theorem intRoot_sq_le {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (intRoot (2 * r) n) ^ 2 ≤ intRoot r n := by
  rw [le_intRoot_iff hr, ← pow_mul]
  exact intRoot_pow_le (by omega) n

/-- Real upper bound `(intRoot r n : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ))` for $r \ge 1$. -/
theorem intRoot_cast_le_rpow {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (intRoot r n : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpow : ((intRoot r n : ℝ)) ^ r ≤ (n : ℝ) := by exact_mod_cast intRoot_pow_le hr n
  have h1 := Real.rpow_le_rpow (by positivity) hpow (by positivity : (0 : ℝ) ≤ 1 / (r : ℝ))
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    mul_one_div_cancel hrpos.ne', Real.rpow_one] at h1

private lemma add_two_le_add_two_pow {d t : ℕ} (hd : 1 ≤ d) (n : ℕ)
    (hn : n < (t + 1) ^ d) : n + 2 ≤ (t + 2) ^ d := by
  have hsucc : ∀ k ≥ 1, ∀ a ≥ 1, a ^ k + 1 ≤ (a + 1) ^ k := by
    intro k hk a ha
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      calc a ^ (k + 1) + 1 = a ^ k * a + 1 := by rw [pow_succ]
        _ ≤ a ^ k * a + a := by omega
        _ = (a ^ k + 1) * a := by ring
        _ ≤ (a + 1) ^ k * (a + 1) := Nat.mul_le_mul (ih) (by omega)
        _ = (a + 1) ^ (k + 1) := (pow_succ (a + 1) k).symm
  have h1 : (t + 1) ^ d + 1 ≤ (t + 2) ^ d := hsucc d hd (t + 1) (by omega)
  linarith

private lemma mul_log_bound (A t : ℕ) :
    A * (t + 3) * (Nat.log 2 (t + 2) + 1) ≤
      t ^ 2 + ((5 + 16 * A ^ 2 + 4 * A) ^ 2 + 3 * (5 + 16 * A ^ 2 + 4 * A)) := by
  have hlog := Nat.mul_log_le_add_sq Nat.one_lt_two (4 * A) (t + 2)
  set B := 5 + 16 * A ^ 2 + 4 * A
  have hB : B = 5 + 16 * A ^ 2 + 4 * A := rfl
  have h4 : 4 * (A * (t + 3) * (Nat.log 2 (t + 2) + 1)) ≤ 4 * (t ^ 2 + (B ^ 2 + 3 * B)) := by
    have hmul : 4 * A * (Nat.log 2 (t + 2) + 1) ≤ t + 2 + 16 * A ^ 2 + 4 * A := by
      nlinarith [hlog]
    have hprod : (t + 3) * (4 * A * (Nat.log 2 (t + 2) + 1)) ≤
        (t + 3) * (t + 2 + 16 * A ^ 2 + 4 * A) := Nat.mul_le_mul_left (t + 3) hmul
    have hquad : (t + 3) * (t + 2 + 16 * A ^ 2 + 4 * A) ≤ 4 * t ^ 2 + 4 * (B ^ 2 + 3 * B) := by
      have hsq : 0 ≤ (2 * (t : ℤ) - (B : ℤ)) ^ 2 := sq_nonneg _
      have hBZ : (B : ℤ) = 5 + 16 * (A : ℤ) ^ 2 + 4 * (A : ℤ) := by rw [hB]; push_cast; ring
      zify
      nlinarith
    nlinarith
  omega

/-! ### 2. Bounded-step reflexive reachability and $b$-way divide-and-conquer circuits -/

section ReachCircuits

private def RelPow {α : Type*} (R : α → α → Prop) : ℕ → α → α → Prop
  | 0, u, v => u = v
  | m + 1, u, v => ∃ z, RelPow R m u z ∧ R z v

private lemma relPow_one_iff {α : Type*} {R : α → α → Prop} {u v : α} :
    RelPow R 1 u v ↔ R u v :=
  ⟨fun ⟨_, hz, hzv⟩ ↦ hz ▸ hzv, fun h ↦ ⟨u, rfl, h⟩⟩

private lemma relPow_add_iff {α : Type*} {R : α → α → Prop} (a b : ℕ) (u v : α) :
    RelPow R (a + b) u v ↔ ∃ z, RelPow R a u z ∧ RelPow R b z v := by
  induction b generalizing v with
  | zero =>
    simp only [Nat.add_zero, RelPow, exists_eq_right]
  | succ b ih =>
    constructor
    · rintro ⟨w, hw, hwv⟩
      obtain ⟨z, huz, hzw⟩ := (ih w).mp hw
      exact ⟨z, huz, w, hzw, hwv⟩
    · rintro ⟨z, huz, w, hzw, hwv⟩
      exact ⟨w, (ih w).mpr ⟨z, huz, hzw⟩, hwv⟩

private lemma relPow_mono_of_refl {α : Type*} {R : α → α → Prop} (hrefl : ∀ x, R x x)
    {m m' : ℕ} (hle : m ≤ m') {u v : α} (h : RelPow R m u v) : RelPow R m' u v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using h
  | succ k ih => exact ⟨v, ih (Nat.le_add_right m k), hrefl v⟩

private lemma relPow_iff_walk {α : Type*} {R : α → α → Prop} (m : ℕ) (u v : α) :
    RelPow R m u v ↔ ∃ p : Fin (m + 1) → α, p 0 = u ∧ p (Fin.last m) = v ∧
      ∀ i : Fin m, R (p i.castSucc) (p i.succ) := by
  induction m generalizing v with
  | zero =>
    constructor
    · rintro rfl
      exact ⟨fun _ ↦ u, rfl, rfl, fun i ↦ i.elim0⟩
    · rintro ⟨p, hp0, hplast, _⟩
      exact hp0.symm.trans hplast
  | succ m ih =>
    constructor
    · rintro ⟨z, huz, hzv⟩
      obtain ⟨p, hp0, hplast, hstep⟩ := (ih z).mp huz
      refine ⟨Fin.snoc p v, ?_, by simp, fun i ↦ ?_⟩
      · simpa [Fin.snoc] using hp0
      · refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hplast]
          exact hzv
        · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hstep j
    · rintro ⟨p, hp0, hplast, hstep⟩
      refine ⟨p (Fin.castSucc (Fin.last m)), (ih _).mpr ⟨p ∘ Fin.castSucc, hp0, rfl, fun j ↦ ?_⟩,
        hplast ▸ hstep (Fin.last m)⟩
      simpa only [Function.comp_apply, Fin.succ_castSucc] using hstep j.castSucc

private lemma reflTransGen_iff_relPow_of_card_le {V : ℕ} {R : Fin V → Fin V → Prop}
    (hrefl : ∀ x, R x x) {L : ℕ} (hVL : V ≤ L) (u v : Fin V) :
    Relation.ReflTransGen R u v ↔ RelPow R L u v := by
  constructor
  · intro h
    have hex : ∃ m, RelPow R m u v := by
      induction h with
      | refl => exact ⟨0, rfl⟩
      | tail _ hstep ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨m + 1, _, hm, hstep⟩
    classical
    let m := Nat.find hex
    have hm : RelPow R m u v := Nat.find_spec hex
    have hm_lt : m < V := by
      by_contra hge
      push Not at hge
      obtain ⟨p, hp0, hplast, hstep⟩ := (relPow_iff_walk m u v).mp hm
      have hcard : Fintype.card (Fin V) < Fintype.card (Fin (m + 1)) := by
        simp only [Fintype.card_fin]; omega
      obtain ⟨i, j, hij, hpij⟩ := Fintype.exists_ne_map_eq_of_card_lt p hcard
      wlog hlt : i < j generalizing i j
      · exact this j i hij.symm hpij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
      let d := j.val - i.val
      have hd_pos : 0 < d := by have := Fin.lt_def.mp hlt; omega
      let m' := m - d
      have hm'_lt : m' < m := by have := j.isLt; omega
      let q : Fin (m' + 1) → Fin V := fun k ↦
        if k.val ≤ i.val then p ⟨k.val, by have := k.isLt; omega⟩
        else p ⟨k.val + d, by have := k.isLt; have := j.isLt; omega⟩
      have hq0 : q 0 = u := by simp [q, hp0]
      have hqlast : q (Fin.last m') = v := by
        dsimp only [q, Fin.val_last]
        split_ifs with hle
        · have hj_eq : j.val = m := by have := j.isLt; omega
          have hi_eq : m' = i.val := by omega
          have hpj : p j = v := by rw [show j = Fin.last m from Fin.ext hj_eq, hplast]
          rw [show (⟨m', _⟩ : Fin (m + 1)) = i from Fin.ext hi_eq, hpij, hpj]
        · have hidx : m' + d = m := by have := j.isLt; omega
          have hFinEq : (⟨m' + d, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext hidx
          rw [hFinEq, hplast]
      have hqstep : ∀ r : Fin m', R (q r.castSucc) (q r.succ) := fun r ↦ by
        dsimp only [q, Fin.val_castSucc, Fin.val_succ]
        by_cases hr1 : r.val + 1 ≤ i.val
        · have hr0 : r.val ≤ i.val := by omega
          simp only [hr0, hr1, ↓reduceIte]
          exact hstep ⟨r.val, by have := i.isLt; omega⟩
        · by_cases hr0 : r.val ≤ i.val
          · have hri : r.val = i.val := by omega
            simp only [hr0, hr1, ↓reduceIte]
            have h1 : (⟨r.val, by have := r.isLt; omega⟩ : Fin (m + 1)) = i := Fin.ext hri
            have h2 : r.val + 1 + d = j.val + 1 := by omega
            rw [h1, hpij]
            have hjlt : j.val < m := by have := r.isLt; have := j.isLt; omega
            have h3 : (⟨r.val + 1 + d, by omega⟩ : Fin (m + 1)) = (⟨j.val, hjlt⟩ : Fin m).succ :=
              Fin.ext h2
            rw [h3]
            have hstepj := hstep ⟨j.val, hjlt⟩
            rwa [show (⟨j.val, hjlt⟩ : Fin m).castSucc = j from Fin.ext rfl] at hstepj
          · simp only [hr0, hr1, ↓reduceIte]
            have hlt_m : r.val + d < m := by have := r.isLt; have := j.isLt; omega
            simpa [Nat.add_right_comm r.val 1 d] using hstep ⟨r.val + d, hlt_m⟩
      exact Nat.find_min hex hm'_lt ((relPow_iff_walk m' u v).mpr ⟨q, hq0, hqlast, hqstep⟩)
    exact relPow_mono_of_refl hrefl (hm_lt.le.trans hVL) hm
  · intro h
    have hgen : ∀ k {a b : Fin V}, RelPow R k a b → Relation.ReflTransGen R a b := by
      intro k
      induction k with
      | zero => rintro a b rfl; exact .refl
      | succ k ih => rintro a b ⟨z, haz, hzb⟩; exact (ih haz).tail hzb
    exact hgen L h

private def chainNode {V b : ℕ} (u v : Fin V) (mid : Fin (b - 1) → Fin V)
    (k : Fin (b + 1)) : Fin V :=
  if hk0 : k.val = 0 then u
  else if hkLast : k.val = b then v
  else mid ⟨k.val - 1, by omega⟩

private lemma relPow_mul_iff_exists_mid {V b L : ℕ} (hb : 2 ≤ b) {R : Fin V → Fin V → Prop}
    (u v : Fin V) :
    RelPow R (b * L) u v ↔
      ∃ mid : Fin (b - 1) → Fin V,
        ∀ j : Fin b, RelPow R L (chainNode u v mid j.castSucc) (chainNode u v mid j.succ) := by
  have hmul : ∀ (k : ℕ) (x y : Fin V),
      RelPow R (k * L) x y ↔ RelPow (RelPow R L) k x y := by
    intro k
    induction k with
    | zero => simp [RelPow]
    | succ k ih =>
      intro x y
      rw [Nat.succ_mul, relPow_add_iff]
      exact exists_congr fun z ↦ and_congr_left fun _ ↦ ih x z
  rw [hmul, relPow_iff_walk]
  constructor
  · rintro ⟨p, hp0, hplast, hstep⟩
    refine ⟨fun i ↦ p ⟨i.val + 1, by omega⟩, fun j ↦ ?_⟩
    have heq : ∀ k : Fin (b + 1), chainNode u v (fun i ↦ p ⟨i.val + 1, by omega⟩) k = p k := by
      intro k
      unfold chainNode
      split_ifs with hk0 hkLast
      · rw [show k = 0 from Fin.ext hk0, hp0]
      · rw [show k = Fin.last b from Fin.ext hkLast, hplast]
      · exact congrArg p (Fin.ext (by dsimp only; omega))
    rw [heq, heq]
    exact hstep j
  · rintro ⟨mid, hmid⟩
    refine ⟨chainNode u v mid, by simp [chainNode], ?_, hmid⟩
    simp [chainNode, show b ≠ 0 by omega]

private noncomputable def stepPairCircuit (V b : ℕ) (p : Fin (V * V)) :
    Circuit Unbounded.signature (V * V) 1 :=
  let uv := finProdFinEquiv.symm p
  let M_card := Fintype.card (Fin (b - 1) → Fin V)
  let enumMid := (Fintype.equivFin (Fin (b - 1) → Fin V)).symm
  let pathAnd (m : Fin M_card) : Circuit Unbounded.signature (V * V) 1 :=
    Circuit.oneGate (Unbounded.Op.and b) fun j : Fin b ↦
      finProdFinEquiv (chainNode uv.1 uv.2 (enumMid m) j.castSucc,
        chainNode uv.1 uv.2 (enumMid m) j.succ)
  (Circuit.oneGate (Unbounded.Op.or M_card) id).comp (Circuit.pi pathAnd)

private noncomputable def stepLayerGadget (V b : ℕ) :
    Circuit Unbounded.signature (V * V) (V * V) :=
  Circuit.pi (stepPairCircuit V b)

private lemma eval_stepLayerGadget {V b : ℕ} (y : BitString (V * V)) (p : Fin (V * V)) :
    (stepLayerGadget V b).eval Unbounded.interpretation y p = true ↔
      ∃ mid : Fin (b - 1) → Fin V, ∀ j : Fin b,
        y (finProdFinEquiv (chainNode (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
          mid j.castSucc,
          chainNode (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
          mid j.succ)) = true := by
  simp only [stepLayerGadget, stepPairCircuit, Circuit.eval_pi, Circuit.eval_comp,
    Circuit.eval_oneGate, Unbounded.interpretation_or, Unbounded.interpretation_and, id_eq,
    decide_eq_true_eq]
  exact ⟨fun ⟨m, hm⟩ ↦ ⟨_, hm⟩,
    fun ⟨mid, hmid⟩ ↦ ⟨Fintype.equivFin _ mid, by simpa only [Equiv.symm_apply_apply] using hmid⟩⟩

private lemma depth_stepLayerGadget_le (V b : ℕ) : (stepLayerGadget V b).depth ≤ 2 := by
  refine Circuit.depth_pi_le (D := 2) _ fun p ↦ ?_
  dsimp only [stepPairCircuit]
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_oneGate]
  exact Nat.add_le_add_left (Circuit.depth_pi_le (D :=
    1) _ fun _ ↦ (Circuit.depth_oneGate _ _).le) 1

private lemma size_stepLayerGadget_le {V b : ℕ} (hV : 1 ≤ V) (hb : 2 ≤ b) :
    (stepLayerGadget V b).size ≤ 2 * V ^ (b + 1) := by
  simp only [stepLayerGadget, stepPairCircuit, Circuit.size_pi, Circuit.size_comp,
    Circuit.size_oneGate, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, Fintype.card_fun]
  have hpow1 : V * V * V ^ (b - 1) = V ^ (b + 1) := by
    calc V * V * V ^ (b - 1) = V ^ 2 * V ^ (b - 1) := by ring
      _ = V ^ (2 + (b - 1)) := (pow_add V 2 (b - 1)).symm
      _ = V ^ (b + 1) := by congr 1; omega
  have hpow2 : V * V ≤ V ^ (b + 1) := by
    calc V * V = V ^ 2 := (sq V).symm
      _ ≤ V ^ (b + 1) := Nat.pow_le_pow_right hV (by omega)
  nlinarith

private noncomputable def baseEdgeCircuit {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V : ℕ) (p : Fin (V * V)) :
    Circuit Unbounded.signature n 1 :=
  let φ := Signature.Hom.id Unbounded.signature
  let uv := finProdFinEquiv.symm p
  if uv.1 = uv.2 then
    Unbounded.constCircuit φ true
  else
    let q := ConfigurationGraph.queryIndex (k := k) B uv.1.val
    if hq : q < n then
      let bT := ConfigurationGraph.edgeWithSymbol ntm B n uv.1.val uv.2.val (some true)
      let bF := ConfigurationGraph.edgeWithSymbol ntm B n uv.1.val uv.2.val (some false)
      match bT, bF with
      | true, true => Unbounded.constCircuit φ true
      | false, false => Unbounded.constCircuit φ false
      | true, false => Circuit.wiring Unbounded.signature fun _ ↦ ⟨q, hq⟩
      | false, true =>
          Unbounded.notCircuit φ
            (Circuit.wiring Unbounded.signature fun _ ↦ ⟨q, hq⟩)
    else
      Unbounded.constCircuit φ
        (ConfigurationGraph.edgeWithSymbol ntm B n uv.1.val uv.2.val none)

private lemma eval_baseEdgeCircuit {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V : ℕ) (p : Fin (V * V)) (x : BitString n) :
    (baseEdgeCircuit ntm B n V p).eval Unbounded.interpretation x 0 = true ↔
      ((finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm p).2 ∨
        ConfigurationGraph.Edge ntm B (List.ofFn x)
          (finProdFinEquiv.symm p).1.val (finProdFinEquiv.symm p).2.val) := by
  unfold baseEdgeCircuit
  dsimp only
  generalize (finProdFinEquiv.symm p).1 = u, (finProdFinEquiv.symm p).2 = v
  split_ifs with huv hq
  · simp [huv]
  · have hget : (List.ofFn x)[ConfigurationGraph.queryIndex (k := k) B u.val]? =
        some (x ⟨ConfigurationGraph.queryIndex (k := k) B u.val, hq⟩) := by
      simp only [List.getElem?_ofFn, hq, ↓reduceDIte]
    rw [ConfigurationGraph.Edge, List.length_ofFn, hget]
    simp only [huv, false_or]
    cases hbT : ConfigurationGraph.edgeWithSymbol ntm B n u.val v.val (some true) <;>
      cases hbF : ConfigurationGraph.edgeWithSymbol ntm B n u.val v.val (some false) <;>
      cases hx : x ⟨ConfigurationGraph.queryIndex (k := k) B u.val, hq⟩ <;>
      simp_all
  · have hget : (List.ofFn x)[ConfigurationGraph.queryIndex (k := k) B u.val]? = none := by
      simp only [List.getElem?_ofFn, hq, ↓reduceDIte]
    rw [ConfigurationGraph.Edge, List.length_ofFn, hget]
    simp [huv]

private lemma size_baseEdgeCircuit_le {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V : ℕ) (p : Fin (V * V)) :
    (baseEdgeCircuit ntm B n V p).size ≤ 1 := by
  unfold baseEdgeCircuit
  dsimp only
  split_ifs with h1 h2
  · simp
  · split <;> simp
  · simp

private lemma depth_baseEdgeCircuit_le {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V : ℕ) (p : Fin (V * V)) :
    (baseEdgeCircuit ntm B n V p).depth ≤ 1 := by
  unfold baseEdgeCircuit
  dsimp only
  split_ifs with h1 h2
  · exact Unbounded.depth_constCircuit_le _
  · split
    · exact Unbounded.depth_constCircuit_le _
    · exact Unbounded.depth_constCircuit_le _
    · simp
    · exact (Unbounded.depth_notCircuit_le _).trans (by simp)
  · exact Unbounded.depth_constCircuit_le _

private noncomputable def reachPowCircuit {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V b : ℕ) :
    ℕ → Circuit Unbounded.signature n (V * V)
  | 0 => Circuit.pi (baseEdgeCircuit ntm B n V)
  | K + 1 => (stepLayerGadget V b).comp (reachPowCircuit ntm B n V b K)

private lemma eval_reachPowCircuit {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V b : ℕ) (hb : 2 ≤ b) (K : ℕ)
    (x : BitString n) (p : Fin (V * V)) :
    (reachPowCircuit ntm B n V b K).eval Unbounded.interpretation x p = true ↔
      RelPow (fun u v : Fin V ↦ u = v ∨
        ConfigurationGraph.Edge ntm B (List.ofFn x) u.val v.val) (b ^ K)
        (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 := by
  induction K generalizing p with
  | zero =>
    rw [reachPowCircuit, Circuit.eval_pi, eval_baseEdgeCircuit, pow_zero, relPow_one_iff]
  | succ K ih =>
    rw [reachPowCircuit, Circuit.eval_comp, eval_stepLayerGadget, pow_succ',
      relPow_mul_iff_exists_mid hb]
    refine exists_congr fun mid ↦ forall_congr' fun j ↦ ?_
    rw [ih, Equiv.symm_apply_apply]

private lemma depth_reachPowCircuit_le {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V b K : ℕ) :
    (reachPowCircuit ntm B n V b K).depth ≤ 2 * K + 1 := by
  induction K with
  | zero =>
    exact Circuit.depth_pi_le _ (depth_baseEdgeCircuit_le ntm B n V)
  | succ K ih =>
    rw [reachPowCircuit]
    have h1 := Circuit.depth_comp_le (stepLayerGadget V b) (reachPowCircuit ntm B n V b K)
    have h2 := depth_stepLayerGadget_le V b
    omega

private lemma size_reachPowCircuit_le {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (B n V b K : ℕ) (hV : 1 ≤ V) (hb : 2 ≤ b) :
    (reachPowCircuit ntm B n V b K).size ≤ (2 * K + 1) * V ^ (b + 1) := by
  induction K with
  | zero =>
    rw [reachPowCircuit, Circuit.size_pi]
    have hsum : ∑ j : Fin (V * V), (baseEdgeCircuit ntm B n V j).size ≤ V * V := by
      calc ∑ j : Fin (V * V), (baseEdgeCircuit ntm B n V j).size
          ≤ ∑ _j : Fin (V * V), 1 := Finset.sum_le_sum fun j _ ↦ size_baseEdgeCircuit_le ..
        _ = V * V := by simp
    have hpow : V * V ≤ V ^ (b + 1) := by
      calc V * V = V ^ 2 := (sq V).symm
        _ ≤ V ^ (b + 1) := Nat.pow_le_pow_right hV (by omega)
    simpa using hsum.trans hpow
  | succ K ih =>
    rw [reachPowCircuit, Circuit.size_comp]
    have hg := size_stepLayerGadget_le hV hb
    nlinarith

end ReachCircuits

/-! ### 3. Main Subexponential Constant-Depth Simulation of `NL` and `L` -/

/-- **Subexponential constant-depth simulation of `NL`**:
for every language `A ∈ Cslib.Complexity.NL encBits` and every integer $r \ge 1$, there exist a
depth bound $D$ and constant $C$ such that at every input length $n$, some unbounded-fan-in
Boolean circuit of depth at most $D$ and size at most $C \cdot 2^{\lfloor n^{1/r} \rfloor}$
computes the $n$-bit slice of `A`.
-/
theorem nl_subexp_unbounded_circuits {A : Language Bool}
    (hA : A ∈ Cslib.Complexity.NL Turing.MultiTapeTM.encBits) {r : ℕ} (hr : 1 ≤ r) :
    ∃ D C : ℕ, ∀ n : ℕ, ∃ cir : Circuit Unbounded.signature n 1,
      cir.Computes Unbounded.interpretation (single (A.slice n)) ∧
      cir.depth ≤ D ∧
      cir.size ≤ C * 2 ^ intRoot r n := by
  obtain ⟨k, State, hFinState, ntm, c, hdec⟩ := hA
  let _ : Fintype State := Fintype.ofFinite State
  let D_rad := ConfigurationGraph.radixExponent State c
  let M_raw := D_rad * Fintype.card (ConfigurationGraph.Register k)
  let M := max M_raw 1
  let K := 2 * r * M
  let A_const := 2 * r * M
  let B_const := 5 + 16 * A_const ^ 2 + 4 * A_const
  let E_const := B_const ^ 2 + 3 * B_const
  refine ⟨2 * K + 2, (2 * K + 2) * 2 ^ E_const, fun n ↦ ?_⟩
  let B := ConfigurationGraph.radix D_rad n
  let V := ConfigurationGraph.vertexBound (k := k) B
  have hV_eq : V = (n + 2) ^ M_raw := ConfigurationGraph.vertexBound_eq_pow D_rad n
  have hV_pos : 1 ≤ V := by rw [hV_eq]; exact Nat.one_le_pow _ _ (by omega)
  let t := intRoot (2 * r) n
  let b := t + 2
  have hb2 : 2 ≤ b := by omega
  have hV_le_bK : V ≤ b ^ K := by
    have ht_lt : n < (t + 1) ^ (2 * r) := lt_succ_intRoot_pow (by omega) n
    have hn2_le : n + 2 ≤ b ^ (2 * r) := add_two_le_add_two_pow (by omega) n ht_lt
    calc V = (n + 2) ^ M_raw := hV_eq
      _ ≤ (n + 2) ^ M := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      _ ≤ (b ^ (2 * r)) ^ M := Nat.pow_le_pow_left hn2_le M
      _ = b ^ K := (pow_mul b (2 * r) M).symm
  have hs0_lt : ConfigurationGraph.startID ntm B < V := by
    let w₀ := List.replicate n false
    have hw₀_len : w₀.length = n := List.length_replicate
    have hs₀ : ntm.RunsInSpace w₀ (c * (Nat.log2 w₀.length + 1)) := (hdec.1 w₀).1
    have hlt := ConfigurationGraph.vertexID_lt_pow_of_runsInSpace c hs₀ .refl
    rw [ConfigurationGraph.vertexID_init, hw₀_len, ← hV_eq] at hlt
    exact hlt
  let s₀ : Fin V := ⟨ConfigurationGraph.startID ntm B, hs0_lt⟩
  let badTargets : List (Fin V) :=
    (List.finRange V).filter fun u ↦ ConfigurationGraph.bad (k := k) (State := State) B n u.val
  let reachCir := reachPowCircuit ntm B n V b K
  let topGate : Circuit Unbounded.signature (V * V) 1 :=
    Circuit.oneGate (.or badTargets.length) fun i ↦ finProdFinEquiv (s₀, badTargets[i])
  let cir := topGate.comp reachCir
  refine ⟨cir, fun x ↦ funext fun j ↦ ?_, ?_, ?_⟩
  · rw [Subsingleton.elim j 0, single_apply]
    dsimp only [cir, topGate]
    rw [Circuit.eval_comp, Circuit.eval_oneGate, Unbounded.interpretation_or]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, Language.slice_eq_true_iff]
    set w := List.ofFn x
    have hw_len : w.length = n := List.length_ofFn
    have hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1)) := (hdec.1 w).1
    have hacc : w ∈ A ↔ ntm.Accepts w := (hdec.1 w).2
    have haccIff : ntm.Accepts w ↔ ∃ u : ℕ,
        Relation.ReflTransGen (ConfigurationGraph.Edge ntm B w)
          (ConfigurationGraph.startID ntm B) u ∧
        ConfigurationGraph.bad (k := k) (State := State) B n u = true := by
      have h := ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace c hs
      simpa only [hw_len, B] using h
    rw [hacc, haccIff]
    let StepRel : Fin V → Fin V → Prop :=
      fun u v ↦ u = v ∨ ConfigurationGraph.Edge ntm B w u.val v.val
    have hStepRefl : ∀ u : Fin V, StepRel u u := fun _ ↦ Or.inl rfl
    constructor
    · rintro ⟨i, hi⟩
      set u : Fin V := badTargets[i]
      have hu_mem : u ∈ badTargets := List.getElem_mem _
      have hu_bad : ConfigurationGraph.bad (k := k) (State := State) B n u.val = true :=
        (List.mem_filter.mp hu_mem).2
      have hiPow : RelPow StepRel (b ^ K) s₀ u := by
        have h := (eval_reachPowCircuit ntm B n V b hb2 K x (finProdFinEquiv (s₀, u))).mp hi
        simpa only [Equiv.symm_apply_apply] using h
      have hiRefl : Relation.ReflTransGen StepRel s₀ u :=
        (reflTransGen_iff_relPow_of_card_le hStepRefl hV_le_bK s₀ u).mpr hiPow
      have hLiftBack : ∀ {z : Fin V}, Relation.ReflTransGen StepRel s₀ z →
          Relation.ReflTransGen (ConfigurationGraph.Edge ntm B w) s₀.val z.val := by
        intro z hz
        induction hz with
        | refl => exact .refl
        | tail _ hstep ih =>
          rcases hstep with rfl | hedge
          · exact ih
          · exact ih.tail hedge
      exact ⟨u.val, hLiftBack hiRefl, hu_bad⟩
    · rintro ⟨u_val, hreach, hubad⟩
      have hu_lt : u_val < V := by
        rw [hV_eq, ← hw_len]
        exact ConfigurationGraph.reachable_lt_pow_of_runsInSpace c hs
          (by simpa only [hw_len, B] using hreach)
      let u : Fin V := ⟨u_val, hu_lt⟩
      have hu_fin : Relation.ReflTransGen StepRel s₀ u := by
        have hlift : ∀ {y : ℕ},
            Relation.ReflTransGen (ConfigurationGraph.Edge ntm B w) s₀.val y →
            ∃ hy : y < V, Relation.ReflTransGen StepRel s₀ ⟨y, hy⟩ := by
          intro y hy_reach
          induction hy_reach with
          | refl => exact ⟨s₀.isLt, .refl⟩
          | @tail a d _ had ih =>
            obtain ⟨ha_lt, hrel⟩ := ih
            have hd_lt : d < V :=
              (ConfigurationGraph.lt_vertexBound_of_edgeWithSymbol had).2
            exact ⟨hd_lt, hrel.tail (Or.inr had)⟩
        obtain ⟨_, hrel⟩ := hlift hreach
        exact hrel
      have hu_pow : RelPow StepRel (b ^ K) s₀ u :=
        (reflTransGen_iff_relPow_of_card_le hStepRefl hV_le_bK s₀ u).mp hu_fin
      have hu_mem : u ∈ badTargets :=
        List.mem_filter.mpr ⟨List.mem_finRange u, hubad⟩
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp hu_mem
      refine ⟨⟨idx, hidx_lt⟩, ?_⟩
      change (reachPowCircuit ntm B n V b K).eval Unbounded.interpretation x
        (finProdFinEquiv (s₀, badTargets[idx])) = true
      rw [hidx_eq, eval_reachPowCircuit ntm B n V b hb2 K x, Equiv.symm_apply_apply]
      exact hu_pow
  · have h1 : cir.depth ≤ topGate.depth + reachCir.depth := Circuit.depth_comp_le topGate reachCir
    have h2 : topGate.depth = 1 := Circuit.depth_oneGate _ _
    have h3 : reachCir.depth ≤ 2 * K + 1 := depth_reachPowCircuit_le ntm B n V b K
    omega
  · dsimp only [cir, topGate, reachCir]
    rw [Circuit.size_comp, Circuit.size_oneGate]
    have hsize := size_reachPowCircuit_le ntm B n V b K hV_pos hb2
    have hVb : V ^ (b + 1) ≤ 2 ^ E_const * 2 ^ intRoot r n := by
      have ht_lt : n < (t + 1) ^ (2 * r) := lt_succ_intRoot_pow (by omega) n
      have hn2_le : n + 2 ≤ (t + 2) ^ (2 * r) := add_two_le_add_two_pow (by omega) n ht_lt
      have ht2_pow : t + 2 ≤ 2 ^ (Nat.log 2 (t + 2) + 1) :=
        (Nat.lt_pow_succ_log_self Nat.one_lt_two (t + 2)).le
      have hV_le_2 : V ≤ 2 ^ (2 * r * M * (Nat.log 2 (t + 2) + 1)) := by
        calc V = (n + 2) ^ M_raw := hV_eq
          _ ≤ (n + 2) ^ M := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
          _ ≤ ((t + 2) ^ (2 * r)) ^ M := Nat.pow_le_pow_left hn2_le M
          _ ≤ ((2 ^ (Nat.log 2 (t + 2) + 1)) ^ (2 * r)) ^ M :=
              Nat.pow_le_pow_left (Nat.pow_le_pow_left ht2_pow _) M
          _ = 2 ^ (2 * r * M * (Nat.log 2 (t + 2) + 1)) := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              ring
      have hexp : A_const * (t + 3) * (Nat.log 2 (t + 2) + 1) ≤ t ^ 2 + E_const :=
        mul_log_bound A_const t
      have ht_sq : t ^ 2 ≤ intRoot r n := intRoot_sq_le hr n
      calc V ^ (b + 1)
          ≤ (2 ^ (2 * r * M * (Nat.log 2 (t + 2) + 1))) ^ (t + 3) :=
            Nat.pow_le_pow_left hV_le_2 (t + 3)
        _ = 2 ^ (A_const * (t + 3) * (Nat.log 2 (t + 2) + 1)) := by
            rw [← pow_mul]
            congr 1
            dsimp only [A_const]
            ring
        _ ≤ 2 ^ (t ^ 2 + E_const) := Nat.pow_le_pow_right (by omega) hexp
        _ ≤ 2 ^ (intRoot r n + E_const) :=
            Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right ht_sq E_const)
        _ = 2 ^ E_const * 2 ^ intRoot r n := by rw [pow_add, mul_comm]
    have hpos2 : 1 ≤ V ^ (b + 1) := Nat.one_le_pow _ _ hV_pos
    have hstep1 : (reachPowCircuit ntm B n V b K).size + 1 ≤ (2 * K + 2) * V ^ (b + 1) := by
      nlinarith
    calc (reachPowCircuit ntm B n V b K).size + 1
        ≤ (2 * K + 2) * V ^ (b + 1) := hstep1
      _ ≤ (2 * K + 2) * (2 ^ E_const * 2 ^ intRoot r n) := Nat.mul_le_mul_left _ hVb
      _ = (2 * K + 2) * 2 ^ E_const * 2 ^ intRoot r n := (mul_assoc _ _ _).symm

/-- **Subexponential constant-depth simulation of `L`**: deterministic specialization of
`nl_subexp_unbounded_circuits` via `Cslib.Complexity.L_subset_NL`. -/
theorem l_subexp_unbounded_circuits {A : Language Bool}
    (hA : A ∈ Cslib.Complexity.L Turing.MultiTapeTM.encBits) {r : ℕ} (hr : 1 ≤ r) :
    ∃ D C : ℕ, ∀ n : ℕ, ∃ cir : Circuit Unbounded.signature n 1,
      cir.Computes Unbounded.interpretation (single (A.slice n)) ∧
      cir.depth ≤ D ∧
      cir.size ≤ C * 2 ^ intRoot r n :=
  nl_subexp_unbounded_circuits (Cslib.Complexity.L_subset_NL hA) hr

/-- Real-exponent form of `nl_subexp_unbounded_circuits`: for every $\varepsilon > 0$, circuits of
constant depth and size at most $C \cdot 2^{n^\varepsilon}$ decide `A ∈ NL`. -/
theorem nl_subexp_unbounded_circuits_rpow {A : Language Bool}
    (hA : A ∈ Cslib.Complexity.NL Turing.MultiTapeTM.encBits) {ε : ℝ} (hε : 0 < ε) :
    ∃ D C : ℕ, ∀ n : ℕ, ∃ cir : Circuit Unbounded.signature n 1,
      cir.Computes Unbounded.interpretation (single (A.slice n)) ∧
      cir.depth ≤ D ∧
      (cir.size : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
  let r : ℕ := max (Nat.ceil (1 / ε)) 1
  have hr1 : 1 ≤ r := le_max_right _ _
  obtain ⟨D, C, hDC⟩ := nl_subexp_unbounded_circuits hA hr1
  refine ⟨D, C + 1, fun n ↦ ?_⟩
  obtain ⟨cir, hcomp, hdepth, hsize⟩ := hDC n
  refine ⟨cir, hcomp, hdepth, ?_⟩
  have hcast : (cir.size : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ (intRoot r n : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hsize
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : intRoot r 0 = 0 := by
      have hpow0 := intRoot_pow_le hr1 0
      rcases Nat.eq_zero_or_pos (intRoot r 0) with h | hpos
      · exact h
      · have := Nat.one_le_pow r (intRoot r 0) hpos
        omega
    rw [h0] at hcast
    have hpow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((0 : ℝ) ^ ε) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    push_cast at hcast ⊢
    nlinarith
  · have hr_ge : 1 / ε ≤ (r : ℝ) :=
      (Nat.le_ceil (1 / ε)).trans (by exact_mod_cast le_max_left _ _)
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    have hexp_le : 1 / (r : ℝ) ≤ ε := by
      rw [div_le_iff₀ hr_pos]
      have := mul_le_mul_of_nonneg_left hr_ge hε.le
      rwa [mul_one_div_cancel hε.ne'] at this
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hroot : (intRoot r n : ℝ) ≤ (n : ℝ) ^ ε :=
      (intRoot_cast_le_rpow hr1 n).trans (Real.rpow_le_rpow_of_exponent_le hn1 hexp_le)
    have h2 : (2 : ℝ) ^ (intRoot r n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ε) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two hroot
    have hC : (C : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact hcast.trans (mul_le_mul hC h2 (by positivity) (by positivity))

/-- Real-exponent form of `l_subexp_unbounded_circuits`. -/
theorem l_subexp_unbounded_circuits_rpow {A : Language Bool}
    (hA : A ∈ Cslib.Complexity.L Turing.MultiTapeTM.encBits) {ε : ℝ} (hε : 0 < ε) :
    ∃ D C : ℕ, ∀ n : ℕ, ∃ cir : Circuit Unbounded.signature n 1,
      cir.Computes Unbounded.interpretation (single (A.slice n)) ∧
      cir.depth ≤ D ∧
      (cir.size : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ ε) :=
  nl_subexp_unbounded_circuits_rpow (Cslib.Complexity.L_subset_NL hA) hε

/-! ### 4. Polylogarithmically Padded `NL` and `L` Languages in `AC⁰` -/

/-- The padded language evaluating the $m(N)$-bit slice of `A` on the $m(N)$-bit prefix of each
$N$-bit input (`m N ≤ N`). -/
noncomputable def paddedLanguage (A : Language Bool) (m : ℕ → ℕ) (hm : ∀ N, m N ≤ N) :
    Language Bool :=
  Language.ofSlices fun N x ↦ A.slice (m N) (fun i ↦ x (Fin.castLE (hm N) i))

/-- Slice evaluation for `paddedLanguage`. -/
@[simp]
theorem slice_paddedLanguage (A : Language Bool) (m : ℕ → ℕ) (hm : ∀ N, m N ≤ N)
    (N : ℕ) (x : BitString N) :
    (paddedLanguage A m hm).slice N x = A.slice (m N) (fun i ↦ x (Fin.castLE (hm N) i)) := by
  rw [paddedLanguage, Language.slice_ofSlices]

/-- Word-membership characterization for `paddedLanguage`. -/
@[simp]
theorem mem_paddedLanguage (A : Language Bool) (m : ℕ → ℕ) (hm : ∀ N, m N ≤ N)
    (w : List Bool) :
    w ∈ paddedLanguage A m hm ↔
      A.slice (m w.length) (fun i ↦ w[Fin.castLE (hm w.length) i]) = true := by
  rw [paddedLanguage, Language.mem_ofSlices]

/-- Prefix padding preserves monotonicity of slices. -/
theorem monotone_slice_paddedLanguage {A : Language Bool} {m : ℕ → ℕ} (hm : ∀ N, m N ≤ N)
    {N : ℕ} (hmono : Monotone (A.slice (m N))) :
    Monotone ((paddedLanguage A m hm).slice N) := by
  intro x y hxy
  rw [slice_paddedLanguage, slice_paddedLanguage]
  exact hmono fun i ↦ hxy (Fin.castLE (hm N) i)

/-- **Polylogarithmically padded `NL` is in `AC⁰`**: if `A ∈ NL encBits` and
$m(N) \le \min(N,\; c (\lfloor \log_2 N \rfloor + 1)^d)$ for constants $c, d$, then
`paddedLanguage A m hm ∈ AC0`. -/
theorem mem_AC0_of_mem_NL_padded {A : Language Bool}
    (hA : A ∈ Cslib.Complexity.NL Turing.MultiTapeTM.encBits)
    {m : ℕ → ℕ} (hm : ∀ N, m N ≤ N) {c d : ℕ}
    (hpolylog : ∀ N, m N ≤ c * (Nat.log2 N + 1) ^ d) :
    paddedLanguage A m hm ∈ AC0 := by
  let r := max d 1
  have hr1 : 1 ≤ r := le_max_right _ _
  obtain ⟨D, C, hDC⟩ := nl_subexp_unbounded_circuits hA hr1
  have hpoly : PolynomiallyBounded (fun N ↦ C * 2 ^ (c + 1) * (N + 1) ^ (c + 1)) :=
    PolynomiallyBounded.of_forall_le (C * 2 ^ (c + 1)) (c + 1) (fun _ ↦ le_rfl)
  refine ConstDepth.mem_iff.mpr ⟨D, fun N ↦ C * 2 ^ (c + 1) * (N + 1) ^ (c + 1), hpoly,
    fun N ↦ ?_⟩
  obtain ⟨cir, hcomp, hdepth, hsize⟩ := hDC (m N)
  let proj := Circuit.wiring Unbounded.signature (Fin.castLE (hm N))
  let paddedCir := cir.comp proj
  refine ⟨paddedCir, fun x ↦ ?_, ?_, ?_⟩
  · funext j
    rw [Circuit.eval_comp, Circuit.eval_wiring, hcomp, single_apply, single_apply,
      slice_paddedLanguage]
    rfl
  · exact (Circuit.depth_comp_le cir proj).trans (by rw [Circuit.depth_wiring]; omega)
  · rw [Circuit.size_comp, Circuit.size_wiring, zero_add]
    have hm_pow : m N ≤ ((c + 1) * (Nat.log2 N + 1)) ^ r := by
      have hc_le : c ≤ (c + 1) ^ r := by
        calc c ≤ c + 1 := Nat.le_succ c
          _ = (c + 1) ^ 1 := (pow_one _).symm
          _ ≤ (c + 1) ^ r := Nat.pow_le_pow_right (Nat.succ_pos c) hr1
      have hd_le : (Nat.log2 N + 1) ^ d ≤ (Nat.log2 N + 1) ^ r :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      calc m N ≤ c * (Nat.log2 N + 1) ^ d := hpolylog N
        _ ≤ (c + 1) ^ r * (Nat.log2 N + 1) ^ r := Nat.mul_le_mul hc_le hd_le
        _ = ((c + 1) * (Nat.log2 N + 1)) ^ r := (mul_pow _ _ _).symm
    have hroot_le : intRoot r (m N) ≤ (c + 1) * (Nat.log2 N + 1) := by
      by_contra hgt
      push Not at hgt
      have h1 : ((c + 1) * (Nat.log2 N + 1) + 1) ^ r ≤ m N :=
        (le_intRoot_iff hr1).mp hgt
      have h2 : ((c + 1) * (Nat.log2 N + 1)) ^ r < ((c + 1) * (Nat.log2 N + 1) + 1) ^ r :=
        Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by omega)
      omega
    have hpow2 : 2 ^ intRoot r (m N) ≤ 2 ^ (c + 1) * (N + 1) ^ (c + 1) := by
      calc 2 ^ intRoot r (m N)
          ≤ 2 ^ ((c + 1) * (Nat.log2 N + 1)) := Nat.pow_le_pow_right (by omega) hroot_le
        _ = (2 ^ (Nat.log2 N + 1)) ^ (c + 1) := by rw [mul_comm, pow_mul]
        _ ≤ (2 * (N + 1)) ^ (c + 1) :=
            Nat.pow_le_pow_left (Nat.two_pow_log2_succ_le N) (c + 1)
        _ = 2 ^ (c + 1) * (N + 1) ^ (c + 1) := mul_pow _ _ _
    calc cir.size ≤ C * 2 ^ intRoot r (m N) := hsize
      _ ≤ C * (2 ^ (c + 1) * (N + 1) ^ (c + 1)) := Nat.mul_le_mul_left C hpow2
      _ = C * 2 ^ (c + 1) * (N + 1) ^ (c + 1) := (mul_assoc _ _ _).symm

/-- **Polylogarithmically padded `L` is in `AC⁰`**: specialization of `mem_AC0_of_mem_NL_padded`
via `Cslib.Complexity.L_subset_NL`. -/
theorem mem_AC0_of_mem_L_padded {A : Language Bool}
    (hA : A ∈ Cslib.Complexity.L Turing.MultiTapeTM.encBits)
    {m : ℕ → ℕ} (hm : ∀ N, m N ≤ N) {c d : ℕ}
    (hpolylog : ∀ N, m N ≤ c * (Nat.log2 N + 1) ^ d) :
    paddedLanguage A m hm ∈ AC0 :=
  mem_AC0_of_mem_NL_padded (Cslib.Complexity.L_subset_NL hA) hm hpolylog

section SanityCheck

private lemma padded_univ_mem_AC0 :
    paddedLanguage (⊤ : Language Bool) (fun N ↦ min (Nat.log2 N) N)
      (fun _ ↦ Nat.min_le_right _ _) ∈ AC0 := by
  refine mem_AC0_of_mem_L_padded ⟨fun _ ↦ true, ComputableInLogSpace.const true, fun _ ↦ ?_⟩
    (fun _ ↦ Nat.min_le_right _ _) (c := 1) (d := 1) fun N ↦ ?_
  · exact ⟨fun _ ↦ rfl, fun _ ↦ trivial⟩
  · simp only [one_mul, pow_one]
    exact (Nat.min_le_left _ _).trans (Nat.le_succ _)

end SanityCheck

end CslibFrontier.Circuits
