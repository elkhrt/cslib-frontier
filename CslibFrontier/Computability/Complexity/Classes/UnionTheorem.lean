/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.ModP.Time
public import CslibFrontier.Computability.Complexity.Classes.Operators
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.PP.Time
public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.UP.Machine
public import Mathlib.Computability.Partrec

import CslibFrontier.Computability.BlumComplexity.MonotoneUnion
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayVerdict
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Nondeterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space
import CslibFrontier.Computability.Machines.Turing.TM2.PartrecToTM2
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Clock
import CslibFrontier.Computability.Probabilistic.Sampling.Verifier
import CslibFrontier.Foundations.Data.Nat.AffineBound
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.Map
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Simultaneous polynomial union theorem across complexity classes

This module defines timed complexity classes `RTIME`, `UTIME`, `SigmaTIME`, and `PiTIME` for `RP`,
`UP`, `SigmaP`, and `PiP`, proves their exact polynomial-union characterizations, and applies
non-decreasing McCreight–Meyer priority-queue diagonalization to construct a *single* total
computable, non-decreasing bound `t : ℕ → ℕ` dominating every polynomial `n ^ d` almost everywhere
such that simultaneously over `encBits`:

* `P = DTIME t`, `NP = NTIME t`, `coNP = compl ⁻¹' NTIME t`, `PSPACE = DSPACE t`, and
  `AP = ATIME t`;
* `PP = PPTIME t`, `BPP = BPTIME t = BPOp (DTIME t)`, `RP = RTIME t`, and
  `coRP = compl ⁻¹' RTIME t`;
* `SharpP = SharpTIME t`, `UP = UTIME t`, `coUP = compl ⁻¹' UTIME t`,
  `ParityP = ParityTIME t = ParityOp (DTIME t)`, `∀ k, ModP k = ModTIME k t`, and
  `∀ k, coModP k = compl ⁻¹' ModTIME k t`;
* `∀ k, SigmaP k = SigmaTIME k t` and `∀ k, PiP k = PiTIME k t`.

## Main definitions

* `Cslib.Complexity.DecidesWithOneSidedErrorInTime`, `Cslib.Complexity.RTIME`: one-sided-error
  randomized time class matching `RP`.
* `Cslib.Complexity.UTIME`: unambiguous nondeterministic time class matching `UP`.
* `Cslib.Complexity.AltTIME`, `Cslib.Complexity.SigmaTIME`, `Cslib.Complexity.PiTIME`:
  alternating bounded-witness verifier time classes matching `SigmaP` and `PiP`.

## Main results

* `Cslib.Complexity.mem_RP_iff_exists_mem_RTIME`, `Cslib.Complexity.mem_UP_iff_exists_mem_UTIME`,
  `Cslib.Complexity.mem_SigmaP_iff_exists_mem_SigmaTIME`,
  `Cslib.Complexity.mem_PiP_iff_exists_mem_PiTIME`: polynomial-union characterizations.
* `Cslib.Complexity.exists_poly_union_bound`: simultaneous non-decreasing McCreight–Meyer union
  theorem across deterministic, nondeterministic, probabilistic, counting, modular, and alternating
  polynomial-bounded complexity classes.
-/

public section

namespace Cslib.Complexity

open Cslib.BlumComplexity Cslib.Probability Filter
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open scoped ENNReal

/-! ### Timed counterparts `RTIME`, `UTIME`, `SigmaTIME`, and `PiTIME` -/

/-- One-sided-error fair-coin Turing-machine decidability within all-branches clock `t`. -/
def DecidesWithOneSidedErrorInTime {k : ℕ} {State : Type} {α : Type*}
    (machine : MultiTapePTM k Bool State) (enc : α ↪ List Bool) (A : Set α) (t : α → ℕ) : Prop :=
  ∀ a, (∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom (t a) (machine.initialConfig (enc a)))).support,
      final.tapes.state = none) ∧
    (a ∈ A → 1 / 2 ≤ ProbComp.eval (machine.runClosed (t a) (enc a)) [true]) ∧
    (a ∉ A → ProbComp.eval (machine.runClosed (t a) (enc a)) [true] = 0)

/-- Enlarging an all-branches halting clock preserves `DecidesWithOneSidedErrorInTime`. -/
theorem DecidesWithOneSidedErrorInTime.mono {k : ℕ} {State : Type} {α : Type*}
    {machine : MultiTapePTM k Bool State} {enc : α ↪ List Bool} {A : Set α} {t t' : α → ℕ}
    (h : DecidesWithOneSidedErrorInTime machine enc A t) (ht : ∀ a, t a ≤ t' a) :
    DecidesWithOneSidedErrorInTime machine enc A t' := fun a ↦ by
  obtain ⟨hhalt, hyes, hno⟩ := h a
  refine ⟨?_, ?_, ?_⟩
  · rwa [machine.eval_runClosedConfigFrom_eq_of_halted _ (ht a) hhalt]
  · rwa [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]
  · rwa [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]

/-- One-sided-error randomized time complexity class `RTIME enc t`. -/
def RTIME {α : Type*} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State),
      DecidesWithOneSidedErrorInTime machine enc A fun a ↦ c₁ * t (enc a).length + c₂}

/-- `RTIME` absorbs affine constants `t₁ n ≤ C * t₂ n + C`. -/
theorem RTIME_mono_of_le_mul_add {α : Type*} {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} {C : ℕ}
    (h : ∀ n, t₁ n ≤ C * t₂ n + C) : RTIME enc t₁ ⊆ RTIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfin, machine, hA⟩
  exact ⟨c₁ * C, c₁ * C + c₂, k, State, hfin, machine,
    hA.mono fun _ ↦ Nat.mul_add_le_mul_add_of_le_mul_add (h _) c₁ c₂⟩

/-- `RTIME` is monotone under almost-everywhere domination. -/
theorem RTIME_mono_of_eventually_le {α : Type*} {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ}
    (h : t₁ ≤ᶠ[atTop] t₂) : RTIME enc t₁ ⊆ RTIME enc t₂ :=
  let ⟨_, hC⟩ := Nat.exists_le_mul_add_of_eventually_le h
  RTIME_mono_of_le_mul_add hC

private lemma half_le_uniformList_map_iff {β : Type} (V : β × List Bool → Bool) (b : β) (n : ℕ) :
    (1 / 2 : ℝ≥0∞) ≤ ((BitString.uniformList n).map fun w ↦ V (b, w)) true ↔
      2 ^ n ≤ 2 * acceptCount V b n := by
  rw [uniformList_acceptCount]
  have h2ne0 : (2 ^ n : ℝ≥0∞) ≠ 0 := by positivity
  have h2net : (2 ^ n : ℝ≥0∞) ≠ ⊤ := by simp
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2ne0) (Or.inl h2net)]
  have hmul : (1 / 2 : ℝ≥0∞) * (2 : ℝ≥0∞) = 1 := by
    rw [one_div]; exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  constructor
  · intro h
    have h2 := mul_le_mul_right h (2 : ℝ≥0∞)
    have hlhs : (2 : ℝ≥0∞) * (1 / 2 * 2 ^ n) = ((2 ^ n : ℕ) : ℝ≥0∞) := by
      rw [← mul_assoc, mul_comm (2 : ℝ≥0∞) (1 / 2), hmul, one_mul]; simp
    have hrhs : (2 : ℝ≥0∞) * (acceptCount V b n : ℝ≥0∞) =
        ((2 * acceptCount V b n : ℕ) : ℝ≥0∞) := by push_cast; rfl
    rw [hlhs, hrhs] at h2
    exact Nat.cast_le.mp h2
  · intro h
    have hhalf := mul_le_mul_right (Nat.cast_le (α := ℝ≥0∞).mpr h) (1 / 2 : ℝ≥0∞)
    have hrhs : (1 / 2 : ℝ≥0∞) * ((2 * acceptCount V b n : ℕ) : ℝ≥0∞) =
        (acceptCount V b n : ℝ≥0∞) := by push_cast; rw [← mul_assoc, hmul, one_mul]
    rw [hrhs] at hhalf
    simpa using hhalf

private lemma uniformList_map_eq_zero_iff {β : Type} (V : β × List Bool → Bool) (b : β) (n : ℕ) :
    ((BitString.uniformList n).map fun w ↦ V (b, w)) true = 0 ↔
      ∀ r : Fin n → Bool, V (b, List.ofFn r) = false := by
  rw [uniformList_acceptCount, ENNReal.div_eq_zero_iff]
  simp [acceptCount_eq_zero_iff]

/-- `RP enc` is the union of `RTIME enc (· ^ d)` over all polynomial degrees `d : ℕ`. -/
theorem mem_RP_iff_exists_mem_RTIME {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ RP enc ↔ ∃ d : ℕ, A ∈ RTIME enc (· ^ d) := by
  rw [mem_RP]
  have htrue (μ : PMF Bool) : μ.map encBool [true] = μ true := by
    simp [PMF.map_apply, encBool_apply]
  constructor
  · rintro ⟨p, V, hV, hA⟩
    obtain ⟨k, State, hfinite, machine, c, d, heval, hhalt⟩ :=
      (isPPTOn_sampleVerify p hV).exists_halting_machine
    refine ⟨d, c * 2 ^ d, c, k, State, hfinite, machine,
      DecidesWithOneSidedErrorInTime.mono (t := fun a ↦ c * ((enc a).length + 1) ^ d)
        (fun a ↦ ⟨hhalt (enc a), fun ha ↦ ?_, fun hna ↦ ?_⟩)
        fun _ ↦ Nat.mul_add_one_pow_le_two_pow c d _⟩
    · rw [← heval a, htrue, ProbComp.eval_map, BitString.eval_sampleList,
        half_le_uniformList_map_iff]
      exact (hA a).1 ha
    · rw [← heval a, htrue, ProbComp.eval_map, BitString.eval_sampleList,
        uniformList_map_eq_zero_iff]
      exact (hA a).2 hna
  · rintro ⟨d, c₁, c₂, k, State, hfinite, machine, hA⟩
    let p : Polynomial ℕ := Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂
    let V : List Bool × List Bool → Bool := fun x ↦ decide (machine.runClosedCoins x.2 x.1 = [true])
    refine ⟨p, fun x ↦ V (enc x.1, x.2),
      MultiTapePTM.computableInPolyTime_decide_runClosedCoins machine, fun a ↦ ?_⟩
    have hevalP : p.eval (enc a).length = c₁ * (enc a).length ^ d + c₂ := by simp [p]
    let T := c₁ * (enc a).length ^ d + c₂
    have hpmf : ProbComp.eval (machine.runClosed T (enc a)) [true] =
        ((BitString.uniformList T).map fun w ↦ V (enc a, w)) true := by
      rw [machine.eval_runClosed_eq_map_coins]
      simp only [PMF.map_apply, V]
      refine tsum_congr fun w ↦ ?_
      by_cases hw : machine.runClosedCoins w (enc a) = [true]
      · simp [hw]
      · have hw' : [true] ≠ machine.runClosedCoins w (enc a) := fun h ↦ hw h.symm
        simp [hw, hw']
    have hcount : acceptCount (fun x : α × List Bool ↦ V (enc x.1, x.2)) a T =
        acceptCount V (enc a) T := rfl
    refine ⟨fun ha ↦ ?_, fun hna ↦ ?_⟩
    · rw [hevalP]
      exact hcount ▸ (half_le_uniformList_map_iff V (enc a) T).mp (hpmf ▸ (hA a).2.1 ha)
    · have hz := (uniformList_map_eq_zero_iff V (enc a) T).mp (hpmf ▸ (hA a).2.2 hna)
      intro r
      have hfn : List.ofFn r = List.ofFn (fun i : Fin T ↦ r (Fin.cast hevalP.symm i)) :=
        List.ext_getElem (by simp [T, hevalP]) fun _ _ _ ↦ by simp
      exact hfn ▸ hz fun i ↦ r (Fin.cast hevalP.symm i)

/-- Unambiguous nondeterministic time complexity class `UTIME enc t`. -/
def UTIME {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ f ∈ SharpTIME enc t, (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ f a = 1}

/-- `UTIME` absorbs affine constants `t₁ n ≤ C * t₂ n + C`. -/
theorem UTIME_mono_of_le_mul_add {α : Type} {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} {C : ℕ}
    (h : ∀ n, t₁ n ≤ C * t₂ n + C) : UTIME enc t₁ ⊆ UTIME enc t₂ :=
  fun _ ⟨f, hf, hle, hA⟩ ↦ ⟨f, SharpTIME_mono_of_le_mul_add h hf, hle, hA⟩

/-- `UTIME` is monotone under almost-everywhere domination. -/
theorem UTIME_mono_of_eventually_le {α : Type} {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ}
    (h : t₁ ≤ᶠ[atTop] t₂) : UTIME enc t₁ ⊆ UTIME enc t₂ :=
  let ⟨_, hC⟩ := Nat.exists_le_mul_add_of_eventually_le h
  UTIME_mono_of_le_mul_add hC

/-- `UP enc` is the union of `UTIME enc (· ^ d)` over all polynomial degrees `d : ℕ`. -/
theorem mem_UP_iff_exists_mem_UTIME {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ UP enc ↔ ∃ d : ℕ, A ∈ UTIME enc (· ^ d) :=
  ⟨fun ⟨f, hf, hle, hA⟩ ↦
    let ⟨d, hd⟩ := mem_SharpP_iff_exists_mem_SharpTIME.mp hf
    ⟨d, f, hd, hle, hA⟩,
    fun ⟨d, f, hf, hle, hA⟩ ↦ ⟨f, SharpTIME.subset_SharpP d hf, hle, hA⟩⟩

/-- Witness-independent alternating verifier time class (`q = true` for `Σ_k`, `q = false` for
`Π_k`) whose polynomial union characterizes the `k`-th level of the polynomial hierarchy. -/
def AltTIME (q : Bool) (k : ℕ) {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool)
      (c₁ c₂ : ℕ) (s : ℕ → ℕ) (m : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM m Bool State),
    ps.length = k ∧
    IsAlternatingVerifier enc q ps V A ∧
    (∀ (a : α) (w : List Bool),
      w.length = (ps.map fun p ↦ p.eval (enc a).length).sum →
      tm.ComputesInTimeAndSpace (encPair enc encBits (a, w)) [V (a, w)]
        (c₁ * t (enc a).length + c₂) (s (encPair enc encBits (a, w)).length)) ∧
    (∀ x : α × List Bool,
      tm.ComputesInTimeAndSpace (encPair enc encBits x) [V x]
        (c₁ * t (encPair enc encBits x).length + c₂) (s (encPair enc encBits x).length))}

/-- Witness-independent `Σ_k` alternating time class `SigmaTIME k enc t`. -/
def SigmaTIME (k : ℕ) {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  AltTIME true k enc t

/-- Witness-independent `Π_k` alternating time class `PiTIME k enc t`. -/
def PiTIME (k : ℕ) {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  AltTIME false k enc t

/-- `AltTIME` absorbs affine constants `t₁ n ≤ C * t₂ n + C`. -/
theorem AltTIME_mono_of_le_mul_add {q : Bool} {k : ℕ} {α : Type} {enc : α ↪ List Bool}
    {t₁ t₂ : ℕ → ℕ} {C : ℕ} (h : ∀ n, t₁ n ≤ C * t₂ n + C) :
    AltTIME q k enc t₁ ⊆ AltTIME q k enc t₂ := by
  rintro A ⟨ps, V, c₁, c₂, s, m, State, hfin, tm, hlen, hver, hon, hall⟩
  exact ⟨ps, V, c₁ * C, c₁ * C + c₂, s, m, State, hfin, tm, hlen, hver,
    fun a w hw ↦ ⟨(hon a w hw).1,
      (hon a w hw).2.1.mono (Nat.mul_add_le_mul_add_of_le_mul_add (h _) c₁ c₂), (hon a w hw).2.2⟩,
    fun x ↦ ⟨(hall x).1,
      (hall x).2.1.mono (Nat.mul_add_le_mul_add_of_le_mul_add (h _) c₁ c₂), (hall x).2.2⟩⟩

/-- `AltTIME` is monotone under almost-everywhere domination. -/
theorem AltTIME_mono_of_eventually_le {q : Bool} {k : ℕ} {α : Type} {enc : α ↪ List Bool}
    {t₁ t₂ : ℕ → ℕ} (h : t₁ ≤ᶠ[atTop] t₂) : AltTIME q k enc t₁ ⊆ AltTIME q k enc t₂ :=
  let ⟨_, hC⟩ := Nat.exists_le_mul_add_of_eventually_le h
  AltTIME_mono_of_le_mul_add hC

private lemma polySum_bound (ps : List (Polynomial ℕ)) :
    ∃ C D : ℕ, ∀ n : ℕ, 2 * n + 1 + (ps.map fun p ↦ p.eval n).sum ≤ C * (n + 1) ^ D := by
  induction ps with
  | nil => exact ⟨2, 1, fun _ ↦ by simp⟩
  | cons p ps ih =>
    obtain ⟨C₁, D₁, h1⟩ := ih
    obtain ⟨C₂, D₂, h2⟩ := polynomiallyBounded_iff_le.mp (PolynomiallyBounded.polynomial_eval p)
    refine ⟨C₁ + C₂, max D₁ D₂, fun n ↦ ?_⟩
    have hle1 : 2 * n + 1 + (ps.map fun p ↦ p.eval n).sum ≤ C₁ * (n + 1) ^ max D₁ D₂ :=
      (h1 n).trans (Nat.mul_le_mul_left C₁
        (Nat.pow_le_pow_right (Nat.add_one_pos n) (le_max_left D₁ D₂)))
    have hle2 : p.eval n ≤ C₂ * (n + 1) ^ max D₁ D₂ :=
      (h2 n).trans (Nat.mul_le_mul_left C₂
        (Nat.pow_le_pow_right (Nat.add_one_pos n) (le_max_right D₁ D₂)))
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    omega

private lemma mem_altP_iff_exists_mem_AltTIME {q : Bool} {k : ℕ} {α : Type}
    {enc : α ↪ List Bool} {A : Set α} :
    (∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool),
      ps.length = k ∧ ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc q ps V A) ↔
    ∃ d : ℕ, A ∈ AltTIME q k enc (· ^ d) := by
  constructor
  · rintro ⟨ps, V, hlen, ⟨tv, sv, htv, -, ⟨m, State, hfin, tm, htm⟩⟩, hver⟩
    obtain ⟨ct, dt, htv_le⟩ := polynomiallyBounded_iff_le.mp htv
    obtain ⟨cp, dp, hps_le⟩ := polySum_bound ps
    let D := max dt (dp * dt)
    have hpow_le : ∀ {e n : ℕ}, e ≤ D → n ^ e ≤ n ^ D + 1 := fun {e n} he ↦ by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rcases Nat.eq_zero_or_pos e with rfl | he0
        · simp
        · simp [Nat.zero_pow he0]
      · exact (Nat.pow_le_pow_right hn he).trans (Nat.le_succ _)
    let C₁ := ct * 2 ^ dt
    let C₂ := ct * (cp + 1) ^ dt * 2 ^ (dp * dt)
    let K := max C₁ C₂
    refine ⟨D, ps, V, K, 2 * K, sv, m, State, hfin, tm, hlen, hver, fun a w hw ↦ ?_, fun x ↦ ?_⟩
    · refine ⟨(htm (a, w)).1, (htm (a, w)).2.1.mono ?_, (htm (a, w)).2.2⟩
      set n := (enc a).length
      have hzlen : (encPair enc encBits (a, w)).length ≤ cp * (n + 1) ^ dp := by
        simpa [length_encPair, encBits, hw] using hps_le n
      have h1 : (encPair enc encBits (a, w)).length + 1 ≤ (cp + 1) * (n + 1) ^ dp := by
        have := Nat.one_le_pow dp (n + 1) (Nat.succ_pos n)
        rw [Nat.add_mul, one_mul]; omega
      have h2 : tv (encPair enc encBits (a, w)).length ≤
          ct * (cp + 1) ^ dt * (n + 1) ^ (dp * dt) :=
        (htv_le _).trans <| (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left h1 dt)).trans_eq
          (by rw [Nat.mul_pow, ← pow_mul, mul_assoc])
      have h3 := h2.trans (Nat.mul_add_one_pow_le_two_pow (ct * (cp + 1) ^ dt) (dp * dt) n)
      have h4 : C₂ * n ^ (dp * dt) ≤ K * n ^ D + K := by
        simpa [Nat.mul_add] using (Nat.mul_le_mul_right _ (le_max_right C₁ C₂)).trans
          (Nat.mul_le_mul_left K (hpow_le (le_max_right dt _)))
      have h5 : ct * (cp + 1) ^ dt ≤ K :=
        (Nat.le_mul_of_pos_right _ (by positivity : 0 < 2 ^ (dp * dt))).trans (le_max_right C₁ C₂)
      exact h3.trans ((Nat.add_le_add h4 h5).trans_eq (by ring))
    · refine ⟨(htm x).1, (htm x).2.1.mono ?_, (htm x).2.2⟩
      set N := (encPair enc encBits x).length
      have h1 := (htv_le N).trans (Nat.mul_add_one_pow_le_two_pow ct dt N)
      have h2 : C₁ * N ^ dt ≤ K * N ^ D + K := by
        simpa [Nat.mul_add] using (Nat.mul_le_mul_right _ (le_max_left C₁ C₂)).trans
          (Nat.mul_le_mul_left K (hpow_le (le_max_left dt _)))
      have h3 : ct ≤ K :=
        (Nat.le_mul_of_pos_right _ (by positivity : 0 < 2 ^ dt)).trans (le_max_left C₁ C₂)
      exact h1.trans ((Nat.add_le_add h2 h3).trans_eq (by ring))
  · rintro ⟨d, ps, V, c₁, c₂, s, m, State, hfin, tm, hlen, hver, -, hall⟩
    have hdt : {x : α × List Bool | V x = true} ∈ DTIME (encPair enc encBits) (· ^ d) :=
      ⟨c₁, c₂, s, decidableInTimeAndSpace_iff.mpr ⟨V, ⟨m, State, hfin, tm, hall⟩, fun _ ↦ Iff.rfl⟩⟩
    obtain ⟨V', hV', hiff⟩ := mem_P_iff_exists_mem_DTIME.mpr ⟨d, hdt⟩
    have heq : V' = V := funext fun x ↦ Bool.eq_iff_iff.mpr (hiff x).symm
    exact ⟨ps, V, hlen, heq ▸ hV', hver⟩

/-- `SigmaP k enc` is the union of `SigmaTIME k enc (· ^ d)` over all polynomial degrees `d`. -/
theorem mem_SigmaP_iff_exists_mem_SigmaTIME {k : ℕ} {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ SigmaP k enc ↔ ∃ d : ℕ, A ∈ SigmaTIME k enc (· ^ d) :=
  mem_altP_iff_exists_mem_AltTIME (q := true)

/-- `PiP k enc` is the union of `PiTIME k enc (· ^ d)` over all polynomial degrees `d`. -/
theorem mem_PiP_iff_exists_mem_PiTIME {k : ℕ} {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PiP k enc ↔ ∃ d : ℕ, A ∈ PiTIME k enc (· ^ d) :=
  mem_altP_iff_exists_mem_AltTIME (q := false)

/-! ### Primitive recursive bounded-space and nondeterministic-time deciders on `Desc` -/

private def descOfCode (e : ℕ) : Desc := (Encodable.decode (α := Desc) e).getD default

private lemma primrec_descOfCode : Primrec descOfCode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const default)

private lemma descOfCode_encode (d : Desc) : descOfCode (Encodable.encode d) = d := by
  simp [descOfCode]

private lemma primrec₂_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := by
  refine (Primrec.nat_iterate Primrec.snd (Primrec.const 1)
    (Primrec.nat_mul.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂).to₂.of_eq fun a b ↦ ?_
  induction b with
  | zero => rfl
  | succ b ih => dsimp only at ih ⊢; rw [Function.iterate_succ_apply', ih, pow_succ]

private lemma simulate_snd_mono {d : Desc} {x : List ℕ} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    (h : (simulate d x t₁).2 = true) : (simulate d x t₂).2 = true :=
  congrArg Prod.snd (simulate_eq_of_halted ht (Prod.ext rfl h))

private noncomputable def tmHaltingSteps (d : Desc) (x : List ℕ) : Part ℕ :=
  Nat.rfind fun m ↦ Part.some (simulate d x m).2

private lemma mem_tmHaltingSteps_iff {d : Desc} {x : List ℕ} {m : ℕ} :
    m ∈ tmHaltingSteps d x ↔
      (simulate d x m).2 = true ∧ (m = 0 ∨ (simulate d x (m - 1)).2 = false) := by
  refine (Nat.mem_rfind (p := fun k ↦ Part.some (simulate d x k).2)).trans ?_
  simp only [Part.mem_some_iff, eq_comm (a := true), eq_comm (a := false)]
  refine ⟨fun ⟨hm, hlt⟩ ↦ ⟨hm, ?_⟩, fun ⟨hm, hprev⟩ ↦ ⟨hm, fun {j} hj ↦ ?_⟩⟩
  · rcases m with _ | m'
    · exact Or.inl rfl
    · exact Or.inr (hlt (Nat.lt_succ_self m'))
  · rcases hprev with rfl | hprev
    · omega
    · exact Bool.eq_false_iff.mpr fun hjt ↦
        Bool.false_ne_true (hprev.symm.trans (simulate_snd_mono (by omega) hjt))

private lemma exists_tmHaltingSteps_le_iff {d : Desc} {x : List ℕ} {B : ℕ} :
    (∃ m ∈ tmHaltingSteps d x, m ≤ B) ↔ (simulate d x B).2 = true := by
  refine ⟨fun ⟨_, hm, hmB⟩ ↦ simulate_snd_mono hmB (mem_tmHaltingSteps_iff.mp hm).1, fun hB ↦ ?_⟩
  classical
  have hex : ∃ k : ℕ, (simulate d x k).2 = true := ⟨B, hB⟩
  exact ⟨Nat.find hex, Nat.mem_rfind.mpr ⟨Part.mem_some_iff.mpr (Nat.find_spec hex).symm,
    fun {_} hj ↦ Part.mem_some_iff.mpr (Bool.eq_false_iff.mpr (Nat.find_min hex hj)).symm⟩,
    Nat.find_min' hex hB⟩

private lemma run_eq_of_halted {d : Desc} {x : List ℕ} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    (h : (simulate d x t₁).2 = true) : run d x t₂ = run d x t₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hst : ((stepOut d x)^[t₁] (init d, [])).1.state = none := by simpa [simulate] using h
  unfold run
  rw [Nat.add_comm, Function.iterate_add_apply]
  rcases hiter : (stepOut d x)^[t₁] (init d, []) with ⟨c, o⟩
  rw [hiter] at hst
  rw [stepOut_iterate_of_state_none d x c o hst]

private lemma simSpace_mono (d : Desc) (x : List ℕ) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    simSpace d x j₁ ≤ simSpace d x j₂ :=
  Finset.sum_le_sum fun i _ ↦ Finset.card_le_card (visited_mono d x h i)

private lemma simSpace_eq_of_halted {d : Desc} {x : List ℕ} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    (h : (simulate d x t₁).2 = true) : simSpace d x t₂ = simSpace d x t₁ := by
  refine le_antisymm (Finset.sum_le_sum fun i _ ↦ Finset.card_le_card fun z hz ↦ ?_)
    (simSpace_mono d x ht)
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
  rcases le_or_gt j t₁ with hle | hgt
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), rfl⟩
  · have hrun : headAt d x j i = headAt d x t₁ i := by simp only [headAt, run_eq_of_halted hgt.le h]
    exact hrun ▸ headAt_mem d x t₁ i

private def spaceTimeCutoff (d : Desc) (n S : ℕ) : ℕ :=
  2 ^ (cfgSpaceBound (descLen d) n d.tapes S + 1)

private def haltsInSpaceBool (d : Desc) (x : List ℕ) (S : ℕ) : Bool :=
  let B := spaceTimeCutoff d x.length S
  (simulate d x B).2 && decide (simSpace d x B ≤ S)

private lemma haltingSteps_le_of_simSpace_le {d : Desc} {x : List ℕ} {m S : ℕ}
    (hm : m ∈ tmHaltingSteps d x) (hS : simSpace d x m ≤ S) :
    m ≤ spaceTimeCutoff d x.length S := by
  classical
  let K := cfgSpaceBound (descLen d) x.length d.tapes S
  let B := 2 ^ (K + 1)
  change m ≤ B
  by_contra hgt
  let pool : Finset (List Bool) :=
    (Finset.range (K + 1)).biUnion fun l ↦ (Finset.univ : Finset (Fin l → Bool)).image List.ofFn
  have hcard_pool : pool.card < B := by
    have hsum : ∀ n : ℕ, ∑ l ∈ Finset.range (n + 1), (2 : ℕ) ^ l < 2 ^ (n + 1) := fun n ↦ by
      induction n with | zero => simp | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega
    exact (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ ↦
      Finset.card_image_le.trans (by simp))).trans_lt (hsum K)
  have hfit : ∀ j : Fin B, eCfg (run d x j.1) ∈ pool := fun j ↦ by
    have hlen : (eCfg (run d x j.1)).length ≤ K := (length_eCfg_le_space d x j.1).trans (by
      have := Nat.mul_le_mul_left (3 * (2 * descLen d + 5) * 2)
        ((simSpace_mono d x (by omega : j.1 ≤ m)).trans hS)
      dsimp only [K, cfgSpaceBound]; omega)
    refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hlen),
      Finset.mem_image.mpr ⟨(eCfg (run d x j.1)).get, Finset.mem_univ _,
        List.ext_getElem (by simp) fun _ _ _ ↦ by simp⟩⟩
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin B ↦ (⟨eCfg (run d x j.1), hfit j⟩ : {bs // bs ∈ pool}))
    (by rw [Fintype.card_coe, Fintype.card_fin]; exact hcard_pool)
  have hrun_eq : run d x a.1 = run d x b.1 := eCfg.injective (congrArg Subtype.val hfab)
  obtain ⟨j₁, j₂, hj12, hj2m, hloop⟩ : ∃ j₁ j₂, j₁ < j₂ ∧ j₂ < m ∧ run d x j₁ = run d x j₂ := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt'
    · exact ⟨a.1, b.1, hlt, by omega, hrun_eq⟩
    · exact ⟨b.1, a.1, hgt', by omega, hrun_eq.symm⟩
  let p := j₂ - j₁
  have hadd : ∀ t : ℕ, run d x (j₁ + t) = run d x (j₂ + t) := fun t ↦ by
    induction t with
    | zero => simpa using hloop
    | succ t ih => rw [← add_assoc, ← add_assoc, run_succ, run_succ, ih]
  have hmod : ∀ q : ℕ, run d x (j₁ + q) = run d x (j₁ + q % p) := fun q ↦ by
    induction q using Nat.strong_induction_on with
    | ind q ih =>
      rcases lt_or_ge q p with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
      · rw [show j₁ + q = j₂ + (q - p) by omega, ← hadd (q - p), ih (q - p) (by omega),
          Nat.mod_eq_sub_mod hge]
  have hm_eq : run d x m = run d x (j₁ + (m - j₁) % p) := by
    conv_lhs => rw [show m = j₁ + (m - j₁) by omega]
    exact hmod (m - j₁)
  have hsmall : j₁ + (m - j₁) % p < m := by have := Nat.mod_lt (m - j₁) (by omega : 0 < p); omega
  have hhalt_s : (simulate d x (j₁ + (m - j₁) % p)).2 = true := by
    change (run d x (j₁ + (m - j₁) % p)).state.isNone = true
    rw [← hm_eq]; exact (mem_tmHaltingSteps_iff.mp hm).1
  have hnot_s : (simulate d x (j₁ + (m - j₁) % p)).2 = false :=
    (Part.mem_some_iff.mp ((Nat.mem_rfind.mp hm).2 hsmall)).symm
  exact Bool.false_ne_true (hnot_s.symm.trans hhalt_s)

private lemma haltsInSpaceBool_eq_true_iff {d : Desc} {x : List ℕ} {S : ℕ} :
    haltsInSpaceBool d x S = true ↔ ∃ m ∈ tmHaltingSteps d x, simSpace d x m ≤ S := by
  simp only [haltsInSpaceBool, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun ⟨hh, hsp⟩ ↦ ?_, fun ⟨m, hm, hsp⟩ ↦ ?_⟩
  · obtain ⟨m, hm, hmB⟩ := exists_tmHaltingSteps_le_iff.mpr hh
    exact ⟨m, hm, by rwa [simSpace_eq_of_halted hmB (mem_tmHaltingSteps_iff.mp hm).1] at hsp⟩
  · have hmB := haltingSteps_le_of_simSpace_le hm hsp
    have hh := (mem_tmHaltingSteps_iff.mp hm).1
    exact ⟨simulate_snd_mono hmB hh, by rwa [simSpace_eq_of_halted hmB hh]⟩

private lemma haltsInSpaceBool_mono {d : Desc} {x : List ℕ} {S₁ S₂ : ℕ} (h : S₁ ≤ S₂)
    (hs : haltsInSpaceBool d x S₁ = true) : haltsInSpaceBool d x S₂ = true :=
  let ⟨m, hm, hle⟩ := haltsInSpaceBool_eq_true_iff.mp hs
  haltsInSpaceBool_eq_true_iff.mpr ⟨m, hm, hle.trans h⟩

private def insertNatDedup (a : ℕ) (acc : List ℕ) : List ℕ :=
  cond (acc.any (· == a)) acc (a :: acc)

private lemma primrec_insertNatDedup : Primrec₂ insertNatDedup := by
  have hany : Primrec fun p : ℕ × List ℕ ↦ p.2.any (· == p.1) :=
    (Primrec.list_foldr Primrec.snd (Primrec.const false)
      (Primrec.or.comp
        (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun (a, l) ↦ by
      induction l with | nil => rfl | cons x xs ih => simp [List.any_cons, ih]
  exact (Primrec.cond hany Primrec.snd (Primrec.list_cons.comp Primrec.fst Primrec.snd)).to₂

private lemma length_dedupNat_eq_card_toFinset (l : List ℕ) :
    (l.foldr insertNatDedup []).length = l.toFinset.card := by
  have hmem : ∀ (xs : List ℕ) (x : ℕ), x ∈ xs.foldr insertNatDedup [] ↔ x ∈ xs := fun xs ↦ by
    induction xs with
    | nil => intro x; simp
    | cons a as ih =>
      intro x; rw [List.foldr_cons, insertNatDedup]
      cases h : (as.foldr insertNatDedup []).any (· == a)
      · rw [Bool.cond_false, List.mem_cons, ih x, List.mem_cons]
      · rw [Bool.cond_true, ih x, List.mem_cons]
        obtain ⟨y, hy, hya⟩ := List.any_eq_true.mp h
        have ha : a ∈ as := (beq_iff_eq.mp hya) ▸ (ih y).mp hy
        exact ⟨Or.inr, fun h' ↦ h'.elim (fun hx ↦ hx ▸ ha) id⟩
  have hnodup : ∀ xs : List ℕ, (xs.foldr insertNatDedup []).Nodup := fun xs ↦ by
    induction xs with
    | nil => exact List.nodup_nil
    | cons a as ih =>
      rw [List.foldr_cons, insertNatDedup]
      cases h : (as.foldr insertNatDedup []).any (· == a)
      · exact List.nodup_cons.mpr
          ⟨fun ha ↦ Bool.false_ne_true (h.symm.trans (List.any_eq_true.mpr ⟨a, ha, by simp⟩)), ih⟩
      · exact ih
  have hfeq : (l.foldr insertNatDedup []).toFinset = l.toFinset := by ext x; simp [hmem]
  rw [← hfeq, List.toFinset_card_of_nodup (hnodup l)]

private lemma primrec_simSpace : Primrec fun p : Desc × List ℕ × ℕ ↦ simSpace p.1 p.2.1 p.2.2 := by
  have hrun : Primrec fun p : Desc × List ℕ × ℕ ↦ run p.1 p.2.1 p.2.2 :=
    (Primrec.nat_iterate (Primrec.snd.comp Primrec.snd) (primrec_init.comp Primrec.fst)
      (Primrec.fst.comp (primrec_step.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))).to₂).of_eq
      fun (d, x, j) ↦ by
        induction j with
        | zero => rfl
        | succ j ih => dsimp only at ih ⊢; rw [Function.iterate_succ_apply', run_succ, ih]
  have hheadCode : Primrec fun q : (Desc × List ℕ × ℕ) × ℕ × ℕ ↦
      Encodable.encode (intEquivNatSumNat (headAt q.1.1 q.1.2.1 q.2.1 q.2.2)) := by
    have hcfg : Primrec fun q : (Desc × List ℕ × ℕ) × ℕ × ℕ ↦ run q.1.1 q.1.2.1 q.2.1 :=
      hrun.comp (g := fun q : (Desc × List ℕ × ℕ) × ℕ × ℕ ↦ (q.1.1, q.1.2.1, q.2.1))
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd)))
    have htape : Primrec fun q : (Desc × List ℕ × ℕ) × ℕ × ℕ ↦
        (run q.1.1 q.1.2.1 q.2.1).workTapes.getD q.2.2 Tape.blank :=
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp (primrec_scfg_workTapes.comp hcfg)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.const Tape.blank)).of_eq fun _ ↦ (List.getD_eq_getElem?_getD ..).symm
    exact Primrec.encode.comp (primrec_tape_head.comp htape)
  have hcardTape : Primrec fun r : (Desc × List ℕ × ℕ) × ℕ ↦
      (visited r.1.1 r.1.2.1 r.1.2.2 r.2).card := by
    have hcodes : Primrec fun r : (Desc × List ℕ × ℕ) × ℕ ↦
        (List.range (r.1.2.2 + 1)).map fun j ↦
          Encodable.encode (intEquivNatSumNat (headAt r.1.1 r.1.2.1 j r.2)) :=
      Primrec.list_map
        (Primrec.list_range.comp (Primrec.succ.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (hheadCode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))).to₂
    have hdedup := Primrec.list_foldr hcodes (Primrec.const [])
      (primrec_insertNatDedup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
    refine (Primrec.list_length.comp hdedup).of_eq fun ((d, x, B), i) ↦ ?_
    dsimp only; rw [length_dedupNat_eq_card_toFinset]
    let emb : ℤ ↪ ℕ := intEquivNatSumNat.toEmbedding.trans
      ⟨Encodable.encode, Encodable.encode_injective⟩
    have hto : ((List.range (B + 1)).map fun j ↦ emb (headAt d x j i)).toFinset =
        (visited d x B i).map emb := by ext m; simp [visited, Finset.mem_map, Finset.mem_image]
    change ((List.range (B + 1)).map fun j ↦ emb (headAt d x j i)).toFinset.card = _
    rw [hto, Finset.card_map]
  refine (Primrec.list_foldr (Primrec.list_range.comp (primrec_desc_tapes.comp Primrec.fst))
    (Primrec.const 0)
    (Primrec.nat_add.comp
      (hcardTape.comp (g := fun q : (Desc × List ℕ × ℕ) × ℕ × ℕ ↦ (q.1, q.2.1))
        (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun (d, x, B) ↦ ?_
  dsimp only [simSpace]
  have hadd : ∀ (l : List ℕ) (a : ℕ),
      l.foldr (fun i acc ↦ (visited d x B i).card + acc) a =
        l.foldr (fun i acc ↦ (visited d x B i).card + acc) 0 + a := fun l a ↦ by
    induction l with
    | nil => simp
    | cons k ks ih =>
      rw [List.foldr_cons, List.foldr_cons, ih]
      omega
  have hsum : ∀ n : ℕ, (List.range n).foldr (fun i acc ↦ (visited d x B i).card + acc) 0 =
      ∑ i ∈ Finset.range n, (visited d x B i).card := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, add_zero, hadd, ih,
        Finset.sum_range_succ]
  exact hsum d.tapes

private lemma primrec_len_eSym : Primrec fun o : Option ℕ ↦ (eSym o).length :=
  (Primrec.option_casesOn Primrec.id (Primrec.const 0) (Primrec.succ.comp Primrec.snd).to₂).of_eq
    fun o ↦ by cases o <;> simp

private lemma primrec_len_encList {β : Type} [Primcodable β] (enc : β ↪ List Bool)
    (h : Primrec fun b : β ↦ (enc b).length) : Primrec fun l : List β ↦ (encList enc l).length :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (h.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun l ↦ by
    induction l with
    | nil => simp
    | cons a as ih =>
      dsimp only [id_eq] at ih ⊢
      rw [List.foldr_cons, ih, encList_cons, List.length_append, length_frame]

private lemma primrec_descLen : Primrec descLen := by
  have hkeyLen : Primrec fun k : Key ↦ (eKey k).length := by
    have htup := Primrec.of_equiv (e := Key.equivTuple)
    have hs := Primrec.fst.comp htup
    have hi := primrec_len_eSym.comp (Primrec.fst.comp (Primrec.snd.comp htup))
    have hw := (primrec_len_encList eSym primrec_len_eSym).comp
      (Primrec.snd.comp (Primrec.snd.comp htup))
    exact (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hs))
      (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hi))
        hw)).of_eq fun k ↦ by
      simp only [eKey_apply, length_encPair, encUnary_apply, List.length_replicate, Key.equivTuple,
        Equiv.coe_fn_mk]
  have hsignLen : Primrec fun s : SignType ↦ (encSign s).length := Primrec.dom_finite _
  have htaLen : Primrec fun ta : Option (Option ℕ) × SignType ↦ (eTA ta).length := by
    have ho : Primrec fun o : Option (Option ℕ) ↦ (encOption eSym o).length :=
      (Primrec.option_casesOn Primrec.id (Primrec.const 0)
        (Primrec.succ.comp (primrec_len_eSym.comp Primrec.snd)).to₂).of_eq
        fun o ↦ by cases o <;> simp
    exact (Primrec.nat_add.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (ho.comp Primrec.fst)))
      (hsignLen.comp Primrec.snd)).of_eq fun _ ↦ by simp only [eTA, length_encPair]
  have hactLen : Primrec fun a : Act ↦ (eAct a).length :=
    (Primrec.nat_add.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (hsignLen.comp primrec_act_inputTape)))
      (Primrec.nat_add.comp
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          ((primrec_len_encList eTA htaLen).comp primrec_act_workTapes)))
        (Primrec.nat_add.comp
          (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
            (primrec_len_eSym.comp primrec_act_output)))
          (primrec_len_eSym.comp primrec_act_state)))).of_eq fun _ ↦ by
      simp only [eAct_apply, length_encPair]
  have hentryLen : Primrec fun e : Key × Act ↦ (encPair eKey eAct e).length :=
    (Primrec.nat_add.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (hkeyLen.comp Primrec.fst)))
      (hactLen.comp Primrec.snd)).of_eq fun _ ↦ by simp only [length_encPair]
  exact (Primrec.nat_add.comp
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_desc_tapes))
    (Primrec.nat_add.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_desc_q₀))
      ((primrec_len_encList (encPair eKey eAct) hentryLen).comp primrec_desc_table))).of_eq
    fun _ ↦ by simp only [descLen, eDesc_apply, length_encPair, encUnary_apply,
      List.length_replicate]

private lemma primrec_spaceTimeCutoff :
    Primrec fun p : Desc × ℕ × ℕ ↦ spaceTimeCutoff p.1 p.2.1 p.2.2 := by
  have hD : Primrec fun p : Desc × ℕ × ℕ ↦ descLen p.1 := primrec_descLen.comp Primrec.fst
  have hX : Primrec fun p : Desc × ℕ × ℕ ↦ (Nat.bits (p.2.1 + 1)).length :=
    Primrec.list_length.comp
      (PartrecToTM2.primrec_bits.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  have hterm1 := Primrec.succ.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hD) (Primrec.const 3))
    (Primrec.nat_mul.comp (Primrec.const 2) hX))
  have hterm2 := Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp (Primrec.const 3)
          (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hD) (Primrec.const 5)))
        (Primrec.const 2))
      (Primrec.snd.comp Primrec.snd))
    (primrec_desc_tapes.comp Primrec.fst)
  exact (primrec₂_pow.comp (Primrec.const 2)
    (Primrec.succ.comp (Primrec.nat_add.comp hterm1 hterm2))).of_eq fun _ ↦ by
    dsimp only [spaceTimeCutoff, cfgSpaceBound, encNat_apply]; congr 2; omega

private lemma primrec_haltsInSpaceBool :
    Primrec fun p : Desc × List ℕ × ℕ ↦ haltsInSpaceBool p.1 p.2.1 p.2.2 := by
  have hB : Primrec fun p : Desc × List ℕ × ℕ ↦ spaceTimeCutoff p.1 p.2.1.length p.2.2 :=
    primrec_spaceTimeCutoff.comp
      (g := fun p : Desc × List ℕ × ℕ ↦ (p.1, p.2.1.length, p.2.2))
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)))
  have htriple : Primrec fun p : Desc × List ℕ × ℕ ↦
      (p.1, p.2.1, spaceTimeCutoff p.1 p.2.1.length p.2.2) :=
    Primrec.pair Primrec.fst (Primrec.pair (Primrec.fst.comp Primrec.snd) hB)
  exact Primrec.and.comp
    (Primrec.snd.comp (primrec_simulate.comp
      (g := fun p : Desc × List ℕ × ℕ ↦ (p.1, p.2.1, spaceTimeCutoff p.1 p.2.1.length p.2.2))
      htriple))
    (Primrec.nat_le.comp
      (primrec_simSpace.comp
        (g := fun p : Desc × List ℕ × ℕ ↦ (p.1, p.2.1, spaceTimeCutoff p.1 p.2.1.length p.2.2))
        htriple)
      (Primrec.snd.comp Primrec.snd)).decide

private def insertSCfg (c : SCfg) (l : List SCfg) : List SCfg :=
  cond (l.any fun c' ↦ decide (Encodable.encode c' = Encodable.encode c)) l (c :: l)

private lemma mem_insertSCfg_iff {c x : SCfg} {l : List SCfg} :
    x ∈ insertSCfg c l ↔ x = c ∨ x ∈ l := by
  dsimp only [insertSCfg]
  cases h : l.any fun c' ↦ decide (Encodable.encode c' = Encodable.encode c)
  · simp
  · simp only [Bool.cond_true]
    obtain ⟨c', hc', heq⟩ := List.any_eq_true.mp h
    have hcc : c = c' := Encodable.encode_injective (of_decide_eq_true heq).symm
    exact ⟨Or.inr, fun hx ↦ hx.elim (fun hxc ↦ hxc ▸ hcc ▸ hc') id⟩

private def nStepSuccs (d : Desc) (x : List ℕ) (s : SCfg) : List SCfg :=
  match s.state with
  | none => []
  | some q =>
    d.table.foldr (fun e acc ↦ cond (decide (e.1 = s.key x q)) (e.2.apply x s :: acc) acc) []

private lemma mem_nStepSuccs_iff {d : Desc} {x : List ℕ} {s s' : SCfg} :
    s' ∈ nStepSuccs d x s ↔ ∃ out' : List ℕ, NStep d x (s, []) (s', out') := by
  dsimp only [nStepSuccs, NStep]
  cases s.state with
  | none => simp
  | some q =>
    simp only [Option.some.injEq, exists_eq_left', List.nil_append]
    have hfold : ∀ tbl : List (Key × Act),
        s' ∈ tbl.foldr (fun e acc ↦ cond (decide (e.1 = s.key x q)) (e.2.apply x s :: acc) acc)
          [] ↔ ∃ e ∈ tbl, e.1 = s.key x q ∧ s' = e.2.apply x s := fun tbl ↦ by
      induction tbl with
      | nil => simp
      | cons e es ih =>
        dsimp only [List.foldr_cons]
        by_cases hk : e.1 = s.key x q
        · simp only [decide_eq_true hk, Bool.cond_true, List.mem_cons, ih]
          exact ⟨fun h ↦ h.elim (fun h1 ↦ ⟨e, Or.inl rfl, hk, h1⟩)
              fun ⟨e', he', hk', hs'⟩ ↦ ⟨e', Or.inr he', hk', hs'⟩,
            fun ⟨e', he', hk', hs'⟩ ↦ he'.elim (fun h1 ↦ Or.inl (h1 ▸ hs'))
              fun h2 ↦ Or.inr ⟨e', h2, hk', hs'⟩⟩
        · simp only [decide_eq_false hk, Bool.cond_false, ih, List.mem_cons]
          exact ⟨fun ⟨e', he', hk', hs'⟩ ↦ ⟨e', Or.inr he', hk', hs'⟩,
            fun ⟨e', he', hk', hs'⟩ ↦ he'.elim (fun h1 ↦ absurd (h1 ▸ hk') hk)
              fun h2 ↦ ⟨e', h2, hk', hs'⟩⟩
    rw [hfold]
    exact ⟨fun ⟨e, he, hk, hs'⟩ ↦ ⟨e.2.output.toList, e, he, hk, Prod.ext hs' rfl⟩,
      fun ⟨_, e, he, hk, hp⟩ ↦ ⟨e, he, hk, (Prod.mk.inj hp).1⟩⟩

private def advanceFrontier (d : Desc) (x : List ℕ) (fs : List SCfg) : List SCfg :=
  fs.foldr (fun s acc ↦ (nStepSuccs d x s).foldr insertSCfg acc) []

private lemma mem_advanceFrontier_iff {d : Desc} {x : List ℕ} {fs : List SCfg} {s' : SCfg} :
    s' ∈ advanceFrontier d x fs ↔ ∃ s ∈ fs, s' ∈ nStepSuccs d x s := by
  have hins : ∀ l acc : List SCfg, s' ∈ l.foldr insertSCfg acc ↔ s' ∈ l ∨ s' ∈ acc := fun l acc ↦ by
    induction l with | nil => simp | cons a as ih => simp [ih, mem_insertSCfg_iff, or_assoc]
  dsimp only [advanceFrontier]
  induction fs with | nil => simp | cons s ss ih => simp [hins, ih]

private def ntmRunsInTimeBool (d : Desc) (x : List ℕ) (B : ℕ) : Bool :=
  ((advanceFrontier d x)^[B] [init d]).foldr (fun s acc ↦ s.state.isNone && acc) true

private lemma listAllHalted_iff {fs : List SCfg} :
    fs.foldr (fun s acc ↦ s.state.isNone && acc) true = true ↔ ∀ s ∈ fs, s.state = none := by
  induction fs with
  | nil => simp
  | cons s ss ih =>
    simp only [List.foldr_cons, Bool.and_eq_true, Option.isNone_iff_eq_none, List.mem_cons,
      forall_eq_or_imp]
    exact and_congr_right fun _ ↦ ih

private lemma ntmRunsInTimeBool_mono {d : Desc} {x : List ℕ} {B₁ B₂ : ℕ} (h : B₁ ≤ B₂)
    (ht : ntmRunsInTimeBool d x B₁ = true) : ntmRunsInTimeBool d x B₂ = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact ht
  | succ k ih =>
    have hall := listAllHalted_iff.mp (ih (Nat.le_add_right B₁ k))
    rw [ntmRunsInTimeBool, listAllHalted_iff, ← add_assoc, Function.iterate_succ_apply']
    intro s' hs'
    obtain ⟨s, hs, hsucc⟩ := mem_advanceFrontier_iff.mp hs'
    simp [nStepSuccs, hall s hs] at hsucc

private lemma primrec₂_insertSCfg : Primrec₂ insertSCfg := by
  have hany : Primrec fun p : SCfg × List SCfg ↦
      p.2.any fun c' ↦ decide (Encodable.encode c' = Encodable.encode p.1) :=
    (Primrec.list_foldr Primrec.snd (Primrec.const false)
      (Primrec.or.comp
        (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.encode.comp (Primrec.fst.comp Primrec.fst))).decide
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun (c, l) ↦ by
      induction l with | nil => rfl | cons a as ih => simp [List.any_cons, ih]
  exact (Primrec.cond hany Primrec.snd (Primrec.list_cons.comp Primrec.fst Primrec.snd)).to₂

private lemma primrec₂_mergeSCfg : Primrec₂ fun l acc : List SCfg ↦ l.foldr insertSCfg acc :=
  (Primrec.list_foldr Primrec.fst Primrec.snd
    (primrec₂_insertSCfg.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).to₂

private lemma primrec_nStepSuccs :
    Primrec fun p : Desc × List ℕ × SCfg ↦ nStepSuccs p.1 p.2.1 p.2.2 := by
  have hkey : Primrec fun pq : (Desc × List ℕ × SCfg) × ℕ ↦ pq.1.2.2.key pq.1.2.1 pq.2 :=
    primrec_scfg_key.comp
      (g := fun pq : (Desc × List ℕ × SCfg) × ℕ ↦ (pq.1.2.2, pq.1.2.1, pq.2))
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have hcond : Primrec fun r : ((Desc × List ℕ × SCfg) × ℕ) × (Key × Act) × List SCfg ↦
      decide (r.2.1.1 = r.1.1.2.2.key r.1.1.2.1 r.1.2) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (hkey.comp Primrec.fst)).decide
  have happ : Primrec fun r : ((Desc × List ℕ × SCfg) × ℕ) × (Key × Act) × List SCfg ↦
      r.2.1.2.apply r.1.1.2.1 r.1.1.2.2 :=
    primrec_act_apply.comp
      (g := fun r : ((Desc × List ℕ × SCfg) × ℕ) × (Key × Act) × List SCfg ↦
        (r.2.1.2, r.1.1.2.1, r.1.1.2.2))
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
  have hsome : Primrec₂ fun (p : Desc × List ℕ × SCfg) (q : ℕ) ↦
      p.1.table.foldr
        (fun e acc ↦ cond (decide (e.1 = p.2.2.key p.2.1 q)) (e.2.apply p.2.1 p.2.2 :: acc) acc)
        [] :=
    (Primrec.list_foldr (primrec_desc_table.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const [])
      (Primrec.cond hcond (Primrec.list_cons.comp happ (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).to₂
  exact (Primrec.option_casesOn (primrec_scfg_state.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.const []) hsome).of_eq fun (d, x,
      s) ↦ by dsimp only [nStepSuccs]; cases s.state <;> rfl

private lemma primrec_advanceFrontier :
    Primrec fun p : (Desc × List ℕ) × List SCfg ↦ advanceFrontier p.1.1 p.1.2 p.2 := by
  have hsub : Primrec fun q : ((Desc × List ℕ) × List SCfg) × SCfg × List SCfg ↦
      nStepSuccs q.1.1.1 q.1.1.2 q.2.1 :=
    primrec_nStepSuccs.comp
      (g := fun q : ((Desc × List ℕ) × List SCfg) × SCfg × List SCfg ↦
        (q.1.1.1, q.1.1.2, q.2.1))
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)))
  exact Primrec.list_foldr Primrec.snd (Primrec.const [])
    (primrec₂_mergeSCfg.comp hsub (Primrec.snd.comp Primrec.snd)).to₂

private lemma primrec_ntmRunsInTimeBool :
    Primrec fun p : Desc × List ℕ × ℕ ↦ ntmRunsInTimeBool p.1 p.2.1 p.2.2 := by
  have hstep : Primrec₂ fun (p : Desc × List ℕ × ℕ) (fs : List SCfg) ↦
      advanceFrontier p.1 p.2.1 fs :=
    (primrec_advanceFrontier.comp
      (g := fun q : (Desc × List ℕ × ℕ) × List SCfg ↦ ((q.1.1, q.1.2.1), q.2))
      (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)).to₂
  have hiter := Primrec.nat_iterate (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (primrec_init.comp Primrec.fst) (Primrec.const [])) hstep
  have hisNone : Primrec fun s : SCfg ↦ s.state.isNone :=
    (Primrec.not.comp (Primrec.option_isSome.comp primrec_scfg_state)).of_eq
      fun s ↦ by cases s.state <;> rfl
  exact Primrec.list_foldr hiter (Primrec.const true)
    (Primrec.and.comp (hisNone.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private lemma ntmRunsInTimeBool_descN_iff {k : ℕ} {State : Type} [Finite State]
    (eS : State ↪ ℕ) (ntm : MultiTapeNTM k Bool State) (x : List Bool) (B : ℕ) :
    ntmRunsInTimeBool (descN eS eBit ntm) (x.map eBit) B = true ↔ ntm.RunsInTime x B := by
  let d := descN eS eBit ntm
  have hreach : ∀ (j : ℕ) {s : SCfg}, s ∈ (advanceFrontier d (x.map eBit))^[j] [init d] →
      ∃ π : ntm.RunPath x, π.head = ntm.initCfg x ∧ π.length = j ∧
        s.WellShaped k (x.map eBit) ∧
        ∃ out : List ℕ, s.toCfg k (x.map eBit) out = π.last.map eS eBit := fun j ↦ by
    induction j with
    | zero =>
      intro s hs; simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hs; subst hs
      obtain ⟨hinit, hshape⟩ := toCfg_init (x := x.map eBit) (descN_tapes eS eBit ntm)
      exact ⟨RelSeries.singleton _ (ntm.initCfg x), rfl, rfl, hshape, [],
        hinit.trans (descN_q₀ eS eBit ntm ▸ (Cfg.map_init eS eBit ntm.q₀).symm)⟩
    | succ j ih =>
      intro s' hs'; rw [Function.iterate_succ_apply'] at hs'
      obtain ⟨s, hs, hsucc⟩ := mem_advanceFrontier_iff.mp hs'
      obtain ⟨π, hhead, hlen, hshape, out, hsc⟩ := ih hs
      obtain ⟨_, q, hq, e, he, hk, hp⟩ := mem_nStepSuccs_iff.mp hsucc
      have hnstep : NStep d (x.map eBit) (s, out) (s', out ++ e.2.output.toList) :=
        ⟨q, hq, e, he, hk, Prod.ext (Prod.mk.inj hp).1 rfl⟩
      obtain ⟨c', hstep, hshape', hsc'⟩ := exists_step_of_nStep eS eBit ntm hshape hsc hnstep
      exact ⟨π.snoc c' hstep, by simpa using hhead, by simp [hlen], hshape',
        out ++ e.2.output.toList, by simpa using hsc'⟩
  have hlive_mem : ∀ (π : ntm.RunPath x), π.head = ntm.initCfg x → ¬ π.last.Halted →
      ∃ s ∈ (advanceFrontier d (x.map eBit))^[π.length] [init d],
        s.WellShaped k (x.map eBit) ∧
        s.toCfg k (x.map eBit) (π.last.map eS eBit).output = π.last.map eS eBit := fun π ↦ by
    induction π using RelSeries.inductionOn' with
    | singleton c =>
      intro hhead _; simp only [RelSeries.head_singleton] at hhead; subst hhead
      obtain ⟨hinit, hshape⟩ := toCfg_init (x := x.map eBit) (descN_tapes eS eBit ntm)
      exact ⟨init d, by simp, hshape,
        hinit.trans (descN_q₀ eS eBit ntm ▸ (Cfg.map_init eS eBit ntm.q₀).symm)⟩
    | snoc π c hc ih =>
      intro hhead hlive
      simp only [RelSeries.head_snoc, RelSeries.last_snoc] at hhead hlive ⊢
      have hprev : ¬ π.last.Halted := fun hh ↦ hlive (((MultiTapeNTM.step_of_halt hh).mp hc) ▸ hh)
      obtain ⟨s, hs, hshape, hsc⟩ := ih hhead hprev
      obtain ⟨s', ⟨q, hq, e, he, hk, hp⟩, hshape', hsc'⟩ :=
        exists_nStep_of_step eS eBit ntm hprev hc hshape hsc
      refine ⟨s', ?_, hshape', hsc'⟩
      rw [RelSeries.snoc_length, Function.iterate_succ_apply']
      exact mem_advanceFrontier_iff.mpr
        ⟨s, hs, mem_nStepSuccs_iff.mpr ⟨e.2.output.toList, q, hq, e, he, hk,
          Prod.ext (Prod.mk.inj hp).1 rfl⟩⟩
  rw [ntmRunsInTimeBool, listAllHalted_iff]
  refine ⟨fun hall ⟨π, hhead⟩ hB ↦ ?_, fun hruns s hs ↦ ?_⟩
  · by_contra hlive
    have hpref : ∀ (ρ : ntm.RunPath x), ρ.head = ntm.initCfg x → B ≤ ρ.length → ¬ ρ.last.Halted →
        ∃ ρ' : ntm.RunPath x, ρ'.head = ntm.initCfg x ∧ ρ'.length = B ∧ ¬ ρ'.last.Halted :=
      fun ρ ↦ by
      induction ρ using RelSeries.inductionOn' with
      | singleton c =>
        intro hh hle hl
        exact ⟨RelSeries.singleton _ c, hh, (show B = 0 by simpa using hle).symm, hl⟩
      | snoc ρ c hc ih =>
        intro hh hle hl
        rcases eq_or_lt_of_le hle with heq | hlt
        · exact ⟨ρ.snoc c hc, hh, heq.symm, hl⟩
        · simp only [RelSeries.head_snoc, RelSeries.last_snoc, RelSeries.snoc_length] at hh hl hlt
          exact ih hh (by omega) fun hrh ↦ hl (((MultiTapeNTM.step_of_halt hrh).mp hc) ▸ hrh)
    obtain ⟨πB, hhB, hlB, hliveB⟩ := hpref π hhead hB hlive
    obtain ⟨s, hs, -, hsc⟩ := hlive_mem πB hhB hliveB
    have hnone := hall s (hlB ▸ hs)
    have hst : Option.map eS πB.last.state = none := by
      simpa [SCfg.toCfg, hnone] using (congrArg Cfg.state hsc).symm
    exact hliveB (Option.map_eq_none_iff.mp hst)
  · obtain ⟨π, hhead, hlen, -, _, hsc⟩ := hreach B hs
    have hh : π.last.Halted := hruns ⟨π, hhead⟩ hlen.ge
    simpa [SCfg.toCfg, Cfg.Halted, hh] using congrArg Cfg.state hsc

/-! ### Simultaneous polynomial union bound across `Cslib.Complexity` -/

private def bitWordsOfLen : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitWordsOfLen n).map (false :: ·) ++ (bitWordsOfLen n).map (true :: ·)

private lemma mem_bitWordsOfLen_iff {n : ℕ} {w : List Bool} :
    w ∈ bitWordsOfLen n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [bitWordsOfLen, List.length_eq_zero_iff]
  | succ n ih => rcases w with _ | ⟨_ | _, ws⟩ <;> simp [bitWordsOfLen, ih]

private lemma primrec_bitWordsOfLen : Primrec bitWordsOfLen := by
  have hstep : Primrec fun ws : List (List Bool) ↦
      ws.map (false :: ·) ++ ws.map (true :: ·) :=
    Primrec.list_append.comp
      (Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)
      (Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)
  refine (Primrec.nat_iterate Primrec.id (Primrec.const [[]])
    (hstep.comp Primrec.snd).to₂).of_eq fun n ↦ ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [id_eq] at ih ⊢; rw [Function.iterate_succ_apply', ih]; rfl

private lemma primrec_bitWordsUpTo : Primrec fun n : ℕ ↦
    (List.range (n + 1)).foldr (fun k acc ↦ bitWordsOfLen k ++ acc) [] :=
  Primrec.list_foldr (Primrec.list_range.comp Primrec.succ) (Primrec.const [])
    (Primrec.list_append.comp (primrec_bitWordsOfLen.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private lemma mem_bitWordsUpTo_iff {n : ℕ} {w : List Bool} :
    w ∈ (List.range (n + 1)).foldr (fun k acc ↦ bitWordsOfLen k ++ acc) [] ↔ w.length ≤ n := by
  have hfold : ∀ l : List ℕ, w ∈ l.foldr (fun k acc ↦ bitWordsOfLen k ++ acc) [] ↔ w.length ∈ l :=
    fun l ↦ by
    induction l with
    | nil => simp
    | cons k ks ih => rw [List.foldr_cons, List.mem_append, mem_bitWordsOfLen_iff, ih,
      List.mem_cons]
  rw [hfold, List.mem_range, Nat.lt_succ_iff]

private def listExistsBool {β : Type*} (l : List β) (p : β → Bool) : Bool :=
  l.foldr (fun b acc ↦ p b || acc) false

private lemma listExistsBool_eq_true_iff {β : Type*} {l : List β} {p : β → Bool} :
    listExistsBool l p = true ↔ ∃ b ∈ l, p b = true := by
  induction l with
  | nil => simp [listExistsBool]
  | cons a as ih =>
    simp only [listExistsBool, List.foldr_cons, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    exact or_congr_right ih

private lemma listExistsBool_eq_false_iff {β : Type*} {l : List β} {p : β → Bool} :
    listExistsBool l p = false ↔ ∀ b ∈ l, p b = false := by
  induction l with
  | nil => simp [listExistsBool]
  | cons a as ih =>
    simp only [listExistsBool, List.foldr_cons, Bool.or_eq_false_iff, List.mem_cons,
      forall_eq_or_imp]
    exact and_congr_right fun _ ↦ ih

private lemma computable_listExistsBool {β γ : Type*} [Primcodable β] [Primcodable γ]
    {f : β → List γ} {p : β → γ → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun b ↦ listExistsBool (f b) (p b) := by
  let step : List γ → (γ → Bool) → ℕ → Bool :=
    fun l q k ↦ Nat.rec false (fun i acc ↦ ((l[i]?).map q).getD false || acc) k
  refine (Computable.nat_rec (Primrec.list_length.to_comp.comp hf) (Computable.const false)
    (Primrec.or.to_comp.comp
      (Computable.option_getD (Computable.option_map
        (Computable.list_getElem?.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd))
        (hp.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂) (Computable.const false))
      (Computable.snd.comp Computable.snd)).to₂).of_eq fun b ↦ Bool.eq_iff_iff.mpr ?_
  have hstep : ∀ k : ℕ, step (f b) (p b) k = true ↔
      ∃ i < k, ((f b)[i]?.map (p b)).getD false = true := fun k ↦ by
    induction k with
    | zero => simp [step]
    | succ k ih =>
      simp only [step, Bool.or_eq_true, ih, Nat.lt_succ_iff_lt_or_eq]
      exact ⟨fun h ↦ h.elim (fun hk ↦ ⟨k, Or.inr rfl, hk⟩)
          fun ⟨i, hi, hq⟩ ↦ ⟨i, Or.inl hi, hq⟩,
        fun ⟨i, hi, hq⟩ ↦ hi.elim (fun hlt ↦ Or.inr ⟨i, hlt, hq⟩) fun heq ↦ Or.inl (heq ▸ hq)⟩
  rw [hstep, listExistsBool_eq_true_iff]
  exact ⟨fun ⟨i, hi, hq⟩ ↦ ⟨(f b)[i], List.getElem_mem hi, by simpa [hi] using hq⟩,
    fun ⟨a, ha, hq⟩ ↦ let ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ha
      ⟨i, hi, by simp [hi, hget, hq]⟩⟩

private def inRangeEncPairBits (z : List Bool) : Bool :=
  listExistsBool ((List.range (z.length + 1)).foldr (fun k acc ↦ bitWordsOfLen k ++ acc) [])
    fun a ↦ decide (z.take (frame a).length = frame a)

private lemma inRangeEncPairBits_eq_true_iff {z : List Bool} :
    inRangeEncPairBits z = true ↔ ∃ p : List Bool × List Bool, encPair encBits encBits p = z := by
  simp only [inRangeEncPairBits, listExistsBool_eq_true_iff, mem_bitWordsUpTo_iff,
    decide_eq_true_eq]
  refine ⟨fun ⟨a, _, htake⟩ ↦ ⟨(a, z.drop (frame a).length),
      (congrArg (· ++ z.drop (frame a).length) htake).symm.trans
        (List.take_append_drop (frame a).length z)⟩,
    fun ⟨⟨a, w⟩, h⟩ ↦ by
      subst h
      exact ⟨a, by simp; omega, by
        change (frame a ++ w).take (frame a).length = frame a
        simp⟩⟩

private lemma computable_inRangeEncPairBits : Computable inRangeEncPairBits :=
  computable_listExistsBool (primrec_bitWordsUpTo.comp Primrec.list_length).to_comp
    (Primrec.eq.decide.to_comp.comp
      (Primrec.list_take.to_comp.comp
        (Primrec.list_length.to_comp.comp (computable_frame.comp Computable.snd)) Computable.fst)
      (computable_frame.comp Computable.snd)).to₂

private lemma affine_poly_from_tail {P : List Bool → ℕ → Prop}
    (hmono : ∀ {x : List Bool} {B₁ B₂ : ℕ}, B₁ ≤ B₂ → P x B₁ → P x B₂)
    {t : ℕ → ℕ} {c₁ c₂ c g : ℕ}
    (hall : ∀ x : List Bool, P x (c₁ * t x.length + c₂))
    (htail : ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → P x (c * n ^ g + c)) :
    ∃ K : ℕ, ∀ x : List Bool, P x (c * x.length ^ g + K) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let M := (Finset.range N).sup fun n ↦ c₁ * t n + c₂
  refine ⟨c + M, fun x ↦ ?_⟩
  rcases lt_or_ge x.length N with hlt | hge
  · have hsup := Finset.le_sup (f := fun n ↦ c₁ * t n + c₂) (Finset.mem_range.mpr hlt)
    exact hmono (by omega) (hall x)
  · exact hmono (by omega) (hN x.length hge x rfl)

private lemma ptm_all_halted_iff_runsInTime {k : ℕ} {State : Type}
    (machine : MultiTapePTM k Bool State) (x : List Bool) (T : ℕ) :
    (∀ final ∈ (ProbComp.eval
        (machine.runClosedConfigFrom T (machine.initialConfig x))).support,
      final.tapes.state = none) ↔
    machine.toNTM.RunsInTime x T :=
  ⟨machine.runsInTime_toNTM, fun hruns final hfin ↦ by
    obtain ⟨π, hhead, hlen, hlast⟩ := machine.mem_support_runClosedConfigFrom_iff.mp hfin
    exact hlast ▸ hruns ⟨π, hhead⟩ hlen.ge⟩

private lemma ptm_eval_runClosed_congr {k : ℕ} {State : Type}
    (machine : MultiTapePTM k Bool State) (x : List Bool) {T₁ T₂ : ℕ}
    (h₁ : ∀ final ∈ (ProbComp.eval
        (machine.runClosedConfigFrom T₁ (machine.initialConfig x))).support,
      final.tapes.state = none)
    (h₂ : ∀ final ∈ (ProbComp.eval
        (machine.runClosedConfigFrom T₂ (machine.initialConfig x))).support,
      final.tapes.state = none) :
    ProbComp.eval (machine.runClosed T₁ x) = ProbComp.eval (machine.runClosed T₂ x) :=
  (machine.eval_runClosed_eq_of_halted x (Nat.le_max_left T₁ T₂) h₁).symm.trans
    (machine.eval_runClosed_eq_of_halted x (Nat.le_max_right T₁ T₂) h₂)

private lemma det_halted_of_runsInTime {k : ℕ} {State : Type}
    (tm : MultiTapeTM k Bool State) (x : List Bool) (T : ℕ) (h : tm.RunsInTime x T) :
    (tm.runFrom (tm.initCfg x) T).Halted := by
  have hh : (MultiTapeNTM.ComputationPath.ofDeterministic tm x T).toRunPath.last.Halted :=
    h (MultiTapeNTM.ComputationPath.ofDeterministic tm x T) le_rfl
  rwa [MultiTapeTM.computationPath_last_eq_runFrom] at hh

private lemma ctm_haltsWithin_iff_runsInTime {k : ℕ} {State : Type}
    {machine : MultiTapeCTM k Bool State} (hnon : machine.Nonblocking)
    (x : List Bool) (T : ℕ) :
    machine.HaltsWithin T (Cfg.init machine.initial x) ↔ machine.toNTM.RunsInTime x T := by
  refine ⟨fun hh π hT ↦ hh.paths_halted π.1 π.2 hT, fun hr ↦ ?_⟩
  have haux : ∀ (fuel : ℕ) (cfg : Cfg k Bool State x) (π : machine.toNTM.RunPath x),
      π.head = machine.toNTM.initCfg x → π.last = cfg →
      (∀ ρ : machine.toNTM.ComputationPath x, π.length + fuel ≤ ρ.length → ρ.last.Halted) →
      machine.HaltsWithin fuel cfg := fun fuel ↦ by
    induction fuel with
    | zero => intro cfg π hh hl hsub; exact .halt (hl ▸ hsub ⟨π, hh⟩ (by simp))
    | succ fuel ih =>
      intro cfg π hh hl hsub
      cases hs : cfg.state with
      | none => exact .halt hs
      | some _ =>
        refine .step (hnon.actions_ne_nil cfg (by simp [hs])) fun idx ↦ ?_
        have hnotH : ¬ cfg.Halted := by simp [Cfg.Halted, hs]
        let nxt : Cfg k Bool State x := (machine.actions cfg)[idx.1].apply cfg
        have hstep : machine.toNTM.Step π.last nxt := by
          rw [hl]
          exact (machine.step_toNTM_iff hnotH).mpr
            ⟨idx.1, (machine.step?_eq_some_iff ..).mpr ⟨idx.2, rfl⟩⟩
        exact ih nxt (π.snoc nxt hstep) (by simpa using hh) (RelSeries.last_snoc ..)
          fun ρ hρ ↦ hsub ρ (by rw [RelSeries.snoc_length] at hρ; omega)
  exact haux T _ (RelSeries.singleton _ (machine.toNTM.initCfg x)) rfl rfl
    fun ρ hρ ↦ hr ρ (by rw [RelSeries.singleton_length, zero_add] at hρ; exact hρ)

private lemma mul_add_le_max_mul_add (c₁ c₂ a : ℕ) :
    c₁ * a + c₂ ≤ max c₁ c₂ * a + max c₁ c₂ :=
  Nat.add_le_add (Nat.mul_le_mul_right a (le_max_left c₁ c₂)) (le_max_right c₁ c₂)

/-- **Simultaneous non-decreasing polynomial union theorem**:
there exists a *single* total computable, non-decreasing function `t : ℕ → ℕ` dominating every
polynomial `n ^ d` almost everywhere that simultaneously characterizes `P`, `NP`, `coNP`, `PP`,
`BPP`, `RP`, `coRP`, `UP`, `coUP`, `PSPACE`, `#P`, `⊕P`, `Mod_k P`, `coMod_k P`, `Σ_k^P`, `Π_k^P`,
and `AP` as their corresponding `t`-bounded classes over `encBits`. -/
theorem exists_poly_union_bound :
    ∃ t : ℕ → ℕ,
      Computable t ∧
      Monotone t ∧
      (∀ d : ℕ, (fun n ↦ n ^ d) ≤ᶠ[atTop] t) ∧
      P encBits = DTIME encBits t ∧
      NP encBits = NTIME encBits t ∧
      coNP encBits = compl ⁻¹' NTIME encBits t ∧
      PP encBits = PPTIME encBits t ∧
      BPP encBits = BPTIME encBits t ∧
      BPP encBits = BPOp encBits (DTIME (encPair encBits encBits) t) ∧
      RP encBits = RTIME encBits t ∧
      coRP encBits = compl ⁻¹' RTIME encBits t ∧
      UP encBits = UTIME encBits t ∧
      coUP encBits = compl ⁻¹' UTIME encBits t ∧
      PSPACE encBits = DSPACE encBits t ∧
      SharpP encBits = SharpTIME encBits t ∧
      ParityP encBits = ParityTIME encBits t ∧
      ParityP encBits = ParityOp encBits (DTIME (encPair encBits encBits) t) ∧
      (∀ k : ℕ, ModP k encBits = ModTIME k encBits t) ∧
      (∀ k : ℕ, coModP k encBits = compl ⁻¹' ModTIME k encBits t) ∧
      (∀ k : ℕ, SigmaP k encBits = SigmaTIME k encBits t) ∧
      (∀ k : ℕ, PiP k encBits = PiTIME k encBits t) ∧
      AP encBits = ATIME encBits t := by
  let F : ℕ → ℕ → ℕ := fun i n ↦ n ^ i
  have hF_comp : Computable₂ F := (primrec₂_pow.comp Primrec.snd Primrec.fst).to₂.to_comp
  have hF_le : ∀ ⦃i j : ℕ⦄, i ≤ j → F i ≤ᶠ[atTop] F j := fun _ _ hij ↦
    eventually_atTop.mpr ⟨1, fun _ hn ↦ Nat.pow_le_pow_right hn hij⟩
  have hF_mono : ∀ i : ℕ, Monotone (F i) := fun i _ _ h ↦ Nat.pow_le_pow_left h i
  have hF_unbdd : ∃ i : ℕ, ∀ B : ℕ, ∃ n : ℕ, B ≤ F i n := ⟨1, fun B ↦ ⟨B, by simp [F]⟩⟩
  let viol : ℕ → ℕ → ℕ → Bool := fun r n B ↦
    let tag := r % 4
    let dc := (r / 4).unpair
    let d := descOfCode dc.1
    let budget := dc.2 * B + dc.2
    if tag = 0 then
      listExistsBool (bitWordsOfLen n) fun x ↦ !(simulate d (x.map eBit) budget).2
    else if tag = 1 then
      listExistsBool (bitWordsOfLen n) fun z ↦
        inRangeEncPairBits z && !(simulate d (z.map eBit) budget).2
    else if tag = 2 then
      listExistsBool (bitWordsOfLen n) fun x ↦ !haltsInSpaceBool d (x.map eBit) budget
    else
      listExistsBool (bitWordsOfLen n) fun x ↦ !ntmRunsInTimeBool d (x.map eBit) budget
  have hviol_comp : Computable fun p : ℕ × ℕ × ℕ ↦ viol p.1 p.2.1 p.2.2 := by
    have heBitMap : Primrec fun x : List Bool ↦ x.map eBit :=
      Primrec.list_map Primrec.id ((Primrec.dom_finite eBit).comp Primrec.snd).to₂
    have htag : Computable fun p : ℕ × ℕ × ℕ ↦ p.1 % 4 :=
      (Primrec.nat_mod.comp Primrec.fst (Primrec.const 4)).to_comp
    have hdc : Computable fun p : ℕ × ℕ × ℕ ↦ (p.1 / 4).unpair :=
      (Primrec.unpair.comp (Primrec.nat_div.comp Primrec.fst (Primrec.const 4))).to_comp
    have hbud : Computable fun p : ℕ × ℕ × ℕ ↦
        (p.1 / 4).unpair.2 * p.2.2 + (p.1 / 4).unpair.2 :=
      Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp (Computable.snd.comp hdc)
          (Computable.snd.comp Computable.snd)) (Computable.snd.comp hdc)
    have hws : Computable fun p : ℕ × ℕ × ℕ ↦ bitWordsOfLen p.2.1 :=
      (primrec_bitWordsOfLen.comp (Primrec.fst.comp Primrec.snd)).to_comp
    have htriple : Computable fun q : (ℕ × ℕ × ℕ) × List Bool ↦
        (descOfCode (q.1.1 / 4).unpair.1, q.2.map eBit,
          (q.1.1 / 4).unpair.2 * q.1.2.2 + (q.1.1 / 4).unpair.2) :=
      Computable.pair ((primrec_descOfCode.to_comp.comp (Computable.fst.comp hdc)).comp
        Computable.fst)
        (Computable.pair (heBitMap.to_comp.comp Computable.snd) (hbud.comp Computable.fst))
    have hsimNot := (Primrec.not.comp (Primrec.snd.comp primrec_simulate)).to_comp.comp
      (g := fun q : (ℕ × ℕ × ℕ) × List Bool ↦
        (descOfCode (q.1.1 / 4).unpair.1, q.2.map eBit,
          (q.1.1 / 4).unpair.2 * q.1.2.2 + (q.1.1 / 4).unpair.2)) htriple
    have hb0 := computable_listExistsBool hws hsimNot.to₂
    have hb1 := computable_listExistsBool hws
      (Primrec.and.to_comp.comp (computable_inRangeEncPairBits.comp Computable.snd) hsimNot).to₂
    have hb2 := computable_listExistsBool hws
      ((Primrec.not.comp primrec_haltsInSpaceBool).to_comp.comp
        (g := fun q : (ℕ × ℕ × ℕ) × List Bool ↦
          (descOfCode (q.1.1 / 4).unpair.1, q.2.map eBit,
            (q.1.1 / 4).unpair.2 * q.1.2.2 + (q.1.1 / 4).unpair.2)) htriple).to₂
    have hb3 := computable_listExistsBool hws
      ((Primrec.not.comp primrec_ntmRunsInTimeBool).to_comp.comp
        (g := fun q : (ℕ × ℕ × ℕ) × List Bool ↦
          (descOfCode (q.1.1 / 4).unpair.1, q.2.map eBit,
            (q.1.1 / 4).unpair.2 * q.1.2.2 + (q.1.1 / 4).unpair.2)) htriple).to₂
    have heq (k : ℕ) := Primrec.eq.decide.to_comp.comp htag (Computable.const k)
    refine (Computable.cond (heq 0) hb0
      (Computable.cond (heq 1) hb1 (Computable.cond (heq 2) hb2 hb3))).of_eq fun (r, n, B) ↦ ?_
    dsimp only [viol]
    rcases (show r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ (r % 4 ≠ 0 ∧ r % 4 ≠ 1 ∧ r % 4 ≠ 2)
      by omega) with h | h | h | ⟨h0, h1, h2⟩
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h0, h1, h2]
  have hviol_mono : ∀ {r n B₁ B₂ : ℕ}, B₁ ≤ B₂ → viol r n B₁ = false → viol r n B₂ = false := by
    intro r n B₁ B₂ h12 hv
    have hbud : (r / 4).unpair.2 * B₁ + (r / 4).unpair.2 ≤
        (r / 4).unpair.2 * B₂ + (r / 4).unpair.2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ h12) _
    dsimp only [viol] at hv ⊢
    split_ifs at hv ⊢
    · simp only [listExistsBool_eq_false_iff, Bool.not_eq_false'] at hv ⊢
      exact fun x hx ↦ simulate_snd_mono hbud (hv x hx)
    · simp only [listExistsBool_eq_false_iff, Bool.and_eq_false_imp, Bool.not_eq_false'] at hv ⊢
      exact fun z hz hr ↦ simulate_snd_mono hbud (hv z hz hr)
    · simp only [listExistsBool_eq_false_iff, Bool.not_eq_false'] at hv ⊢
      exact fun x hx ↦ haltsInSpaceBool_mono hbud (hv x hx)
    · simp only [listExistsBool_eq_false_iff, Bool.not_eq_false'] at hv ⊢
      exact fun x hx ↦ ntmRunsInTimeBool_mono hbud (hv x hx)
  obtain ⟨t, ht_comp, ht_mono, ht_dom, ht_diag⟩ :=
    exists_computable_monotone_diagonal_union_bound hF_comp hF_le hF_mono hF_unbdd
      hviol_comp hviol_mono
  have hcode (tag : ℕ) (d : Desc) (c : ℕ) (htag : tag < 4) :
      (4 * Nat.pair (Encodable.encode d) c + tag) % 4 = tag ∧
      ((4 * Nat.pair (Encodable.encode d) c + tag) / 4).unpair = (Encodable.encode d, c) :=
    ⟨by omega, by rw [show (4 * Nat.pair (Encodable.encode d) c + tag) / 4 =
        Nat.pair (Encodable.encode d) c by omega, Nat.unpair_pair]⟩
  have h0 (d : Desc) (c : ℕ)
      (hall : ∀ x : List Bool, (simulate d (x.map eBit) (c * t x.length + c)).2 = true) :
      ∃ g : ℕ, ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n →
        (simulate d (x.map eBit) (c * n ^ g + c)).2 = true := by
    obtain ⟨hm, hd⟩ := hcode 0 d c (by omega)
    obtain ⟨g, hg⟩ := ht_diag (4 * Nat.pair (Encodable.encode d) c + 0)
      (Eventually.of_forall fun n ↦ by
        simp only [viol, hm, ↓reduceIte, hd, descOfCode_encode, listExistsBool_eq_false_iff,
          mem_bitWordsOfLen_iff, Bool.not_eq_false']
        exact fun x hx ↦ hx ▸ hall x)
    refine ⟨g, hg.mono fun n hn x hx ↦ ?_⟩
    simp only [viol, hm, ↓reduceIte, hd, descOfCode_encode, listExistsBool_eq_false_iff,
      mem_bitWordsOfLen_iff, Bool.not_eq_false', F] at hn
    exact hn x hx
  have h1 (d : Desc) (c : ℕ) (hall : ∀ p : List Bool × List Bool,
      let z := encPair encBits encBits p
      (simulate d (z.map eBit) (c * t z.length + c)).2 = true) :
      ∃ g : ℕ, ∀ᶠ n in atTop, ∀ p : List Bool × List Bool,
        let z := encPair encBits encBits p
        z.length = n → (simulate d (z.map eBit) (c * n ^ g + c)).2 = true := by
    obtain ⟨hm, hd⟩ := hcode 1 d c (by omega)
    obtain ⟨g, hg⟩ := ht_diag (4 * Nat.pair (Encodable.encode d) c + 1)
      (Eventually.of_forall fun n ↦ by
        simp only [viol, hm, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, hd, descOfCode_encode,
          listExistsBool_eq_false_iff, mem_bitWordsOfLen_iff, Bool.and_eq_false_imp,
          inRangeEncPairBits_eq_true_iff, Bool.not_eq_false']
        rintro _ rfl ⟨p, rfl⟩; exact hall p)
    refine ⟨g, hg.mono fun n hn p hp ↦ ?_⟩
    simp only [viol, hm, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, hd, descOfCode_encode,
      listExistsBool_eq_false_iff, mem_bitWordsOfLen_iff, Bool.and_eq_false_imp,
      inRangeEncPairBits_eq_true_iff, Bool.not_eq_false', F] at hn
    exact hn (encPair encBits encBits p) hp ⟨p, rfl⟩
  have h2 (d : Desc) (c : ℕ)
      (hall : ∀ x : List Bool, haltsInSpaceBool d (x.map eBit) (c * t x.length + c) = true) :
      ∃ g : ℕ, ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n →
        haltsInSpaceBool d (x.map eBit) (c * n ^ g + c) = true := by
    obtain ⟨hm, hd⟩ := hcode 2 d c (by omega)
    obtain ⟨g, hg⟩ := ht_diag (4 * Nat.pair (Encodable.encode d) c + 2)
      (Eventually.of_forall fun n ↦ by
        simp only [viol, hm, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, hd,
          descOfCode_encode, listExistsBool_eq_false_iff, mem_bitWordsOfLen_iff,
          Bool.not_eq_false']
        exact fun x hx ↦ hx ▸ hall x)
    refine ⟨g, hg.mono fun n hn x hx ↦ ?_⟩
    simp only [viol, hm, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, hd,
      descOfCode_encode, listExistsBool_eq_false_iff, mem_bitWordsOfLen_iff, Bool.not_eq_false',
      F] at hn
    exact hn x hx
  have h3 (d : Desc) (c : ℕ)
      (hall : ∀ x : List Bool, ntmRunsInTimeBool d (x.map eBit) (c * t x.length + c) = true) :
      ∃ g : ℕ, ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n →
        ntmRunsInTimeBool d (x.map eBit) (c * n ^ g + c) = true := by
    obtain ⟨hm, hd⟩ := hcode 3 d c (by omega)
    obtain ⟨g, hg⟩ := ht_diag (4 * Nat.pair (Encodable.encode d) c + 3)
      (Eventually.of_forall fun n ↦ by
        simp only [viol, hm, show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
          show (3 : ℕ) ≠ 2 by omega, ↓reduceIte, hd, descOfCode_encode,
          listExistsBool_eq_false_iff, mem_bitWordsOfLen_iff, Bool.not_eq_false']
        exact fun x hx ↦ hx ▸ hall x)
    refine ⟨g, hg.mono fun n hn x hx ↦ ?_⟩
    simp only [viol, hm, show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
      show (3 : ℕ) ≠ 2 by omega, ↓reduceIte, hd, descOfCode_encode, listExistsBool_eq_false_iff,
      mem_bitWordsOfLen_iff, Bool.not_eq_false', F] at hn
    exact hn x hx
  have hNTM : ∀ {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State) (c₁ c₂ : ℕ),
      (∀ x : List Bool, ntm.RunsInTime x (c₁ * t x.length + c₂)) →
      ∃ g c K : ℕ, ∀ x : List Bool, ntm.RunsInTime x (c * x.length ^ g + K) := by
    intro k State _ ntm c₁ c₂ hruns
    cases nonempty_fintype State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    obtain ⟨g, hg⟩ := h3 (descN eS eBit ntm) (max c₁ c₂) fun x ↦
      (ntmRunsInTimeBool_descN_iff eS ntm x _).mpr ((hruns x).mono (mul_add_le_max_mul_add ..))
    obtain ⟨K, hK⟩ := affine_poly_from_tail (P := fun x B ↦ ntm.RunsInTime x B)
      (fun hB hr ↦ hr.mono hB) hruns
      (hg.mono fun _ hn x hx ↦ (ntmRunsInTimeBool_descN_iff eS ntm x _).mp (hn x hx))
    exact ⟨g, max c₁ c₂, K, hK⟩
  have hP : P encBits = DTIME encBits t := by
    refine Set.Subset.antisymm
      (fun _ hA ↦ let ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp hA
        DTIME_mono_of_eventually_le (ht_dom d) hd)
      fun _ ⟨c₁, c₂, s, hdec⟩ ↦ ?_
    obtain ⟨f, ⟨k, State, hfin, tm, htm⟩, hf⟩ := decidableInTimeAndSpace_iff.mp hdec
    cases nonempty_fintype State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    have hsim0 : ∀ x : List Bool,
        (simulate (desc eS eBit tm) (x.map eBit) (c₁ * t x.length + c₂)).2 = true := fun x ↦ by
      rw [simulate_desc, Option.isNone_iff_eq_none]
      exact det_halted_of_runsInTime tm x _ (htm x).2.1
    obtain ⟨g, hg⟩ := h0 (desc eS eBit tm) (max c₁ c₂) fun x ↦
      simulate_snd_mono (mul_add_le_max_mul_add ..) (hsim0 x)
    obtain ⟨K, hK⟩ := affine_poly_from_tail
      (P := fun x B ↦ (simulate (desc eS eBit tm) (x.map eBit) B).2 = true)
      (fun hB hs ↦ simulate_snd_mono hB hs) hsim0 hg
    refine mem_P_iff_exists_mem_DTIME.mpr ⟨g, max c₁ c₂, K, s, decidableInTimeAndSpace_iff.mpr
      ⟨f, ⟨k, State, hfin, tm, fun x ↦ ⟨(htm x).1, runsInTime_of_halted ?_, (htm x).2.2⟩⟩, hf⟩⟩
    have hs := hK x; rwa [simulate_desc, Option.isNone_iff_eq_none] at hs
  have hPpair : P (encPair encBits encBits) = DTIME (encPair encBits encBits) t := by
    refine Set.Subset.antisymm
      (fun _ hA ↦ let ⟨d, hd⟩ := mem_P_iff_exists_mem_DTIME.mp hA
        DTIME_mono_of_eventually_le (ht_dom d) hd)
      fun _ ⟨c₁, c₂, s, hdec⟩ ↦ ?_
    obtain ⟨f, ⟨k, State, hfin, tm, htm⟩, hf⟩ := decidableInTimeAndSpace_iff.mp hdec
    cases nonempty_fintype State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    let c := max c₁ c₂
    have hsim_p : ∀ p : List Bool × List Bool,
        let z := encPair encBits encBits p
        (simulate (desc eS eBit tm) (z.map eBit) (c₁ * t z.length + c₂)).2 = true := fun p ↦ by
      dsimp only; rw [simulate_desc, Option.isNone_iff_eq_none]
      exact det_halted_of_runsInTime tm (encPair encBits encBits p) _ (htm p).2.1
    obtain ⟨g, hg⟩ := h1 (desc eS eBit tm) c fun p ↦
      simulate_snd_mono (mul_add_le_max_mul_add ..) (hsim_p p)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hg
    let M := (Finset.range N).sup fun n ↦ c₁ * t n + c₂
    refine mem_P_iff_exists_mem_DTIME.mpr ⟨g, c, c + M, s, decidableInTimeAndSpace_iff.mpr
      ⟨f, ⟨k, State, hfin, tm, fun p ↦ ?_⟩, hf⟩⟩
    set z := encPair encBits encBits p
    have hs : (simulate (desc eS eBit tm) (z.map eBit) (c * z.length ^ g + (c + M))).2 = true := by
      rcases lt_or_ge z.length N with hlt | hge
      · have hsup : c₁ * t z.length + c₂ ≤ M :=
          Finset.le_sup (f := fun n ↦ c₁ * t n + c₂) (Finset.mem_range.mpr hlt)
        exact simulate_snd_mono (hsup.trans (by omega)) (hsim_p p)
      · exact simulate_snd_mono (by omega) (hN z.length hge p rfl)
    rw [simulate_desc, Option.isNone_iff_eq_none] at hs
    exact ⟨(htm p).1, runsInTime_of_halted hs, (htm p).2.2⟩
  have hNP : NP encBits = NTIME encBits t := Set.Subset.antisymm
    (fun _ hA ↦ let ⟨d, hd⟩ := mem_NP_iff_exists_mem_NTIME.mp hA
      NTIME_mono_of_eventually_le (ht_dom d) hd)
    fun _ ⟨c₁, c₂, k, State, hfin, ntm, hdec⟩ ↦
      let ⟨g, c, K, hK⟩ := hNTM ntm c₁ c₂ fun x ↦ (hdec x).1
      mem_NP_iff_exists_mem_NTIME.mpr ⟨g, c, K, k, State, hfin, ntm, fun x ↦ ⟨hK x, (hdec x).2⟩⟩
  have hPP : PP encBits = PPTIME encBits t := Set.Subset.antisymm
    (fun _ hA ↦ by
      obtain ⟨d, c₁, c₂, k, State, hfin, machine, hdec⟩ := mem_PP_iff_exists_mem_PPTIME.mp hA
      obtain ⟨C, hC⟩ := Nat.exists_le_mul_add_of_eventually_le (ht_dom d)
      exact ⟨c₁ * C, c₁ * C + c₂, k, State, hfin, machine,
        hdec.mono fun _ ↦ Nat.mul_add_le_mul_add_of_le_mul_add (hC _) c₁ c₂⟩)
    fun _ ⟨c₁, c₂, k, State, hfin, machine, hdec⟩ ↦ by
      obtain ⟨g, c, K, hK⟩ := hNTM machine.toNTM c₁ c₂ fun x ↦
        (ptm_all_halted_iff_runsInTime machine x _).mp (hdec x).1
      refine mem_PP_iff_exists_mem_PPTIME.mpr ⟨g, c, K, k, State, hfin, machine, fun x ↦ ?_⟩
      have hh' := (ptm_all_halted_iff_runsInTime machine x _).mpr (hK x)
      exact ⟨hh', ptm_eval_runClosed_congr machine x (hdec x).1 hh' ▸ (hdec x).2⟩
  have hBPP : BPP encBits = BPTIME encBits t := Set.Subset.antisymm
    (fun _ hA ↦ let ⟨d, hd⟩ := mem_BPP_iff_exists_mem_BPTIME.mp hA
      BPTIME_mono_of_eventually_le (ht_dom d) hd)
    fun _ ⟨c₁, c₂, k, State, hfin, machine, hdec⟩ ↦ by
      obtain ⟨g, c, K, hK⟩ := hNTM machine.toNTM c₁ c₂ fun x ↦
        (ptm_all_halted_iff_runsInTime machine x _).mp (hdec x).1
      refine mem_BPP_iff_exists_mem_BPTIME.mpr ⟨g, c, K, k, State, hfin, machine, fun x ↦ ?_⟩
      have hh' := (ptm_all_halted_iff_runsInTime machine x _).mpr (hK x)
      exact ⟨hh', ptm_eval_runClosed_congr machine x (hdec x).1 hh' ▸ (hdec x).2⟩
  have hRP : RP encBits = RTIME encBits t := Set.Subset.antisymm
    (fun _ hA ↦ let ⟨d, hd⟩ := mem_RP_iff_exists_mem_RTIME.mp hA
      RTIME_mono_of_eventually_le (ht_dom d) hd)
    fun _ ⟨c₁, c₂, k, State, hfin, machine, hdec⟩ ↦ by
      obtain ⟨g, c, K, hK⟩ := hNTM machine.toNTM c₁ c₂ fun x ↦
        (ptm_all_halted_iff_runsInTime machine x _).mp (hdec x).1
      refine mem_RP_iff_exists_mem_RTIME.mpr ⟨g, c, K, k, State, hfin, machine, fun x ↦ ?_⟩
      have hh' := (ptm_all_halted_iff_runsInTime machine x _).mpr (hK x)
      have heq := ptm_eval_runClosed_congr machine x (hdec x).1 hh'
      exact ⟨hh', heq ▸ (hdec x).2.1, heq ▸ (hdec x).2.2⟩
  have hSharpP : SharpP encBits = SharpTIME encBits t := Set.Subset.antisymm
    (fun _ hf ↦ by
      obtain ⟨d, hd⟩ := mem_SharpP_iff_exists_mem_SharpTIME.mp hf
      obtain ⟨C, hC⟩ := Nat.exists_le_mul_add_of_eventually_le (ht_dom d)
      exact SharpTIME_mono_of_le_mul_add hC hd)
    fun _ ⟨c₁, c₂, k, State, hfin, machine, hnon, hm⟩ ↦ by
      obtain ⟨g, c, K, hK⟩ := hNTM machine.toNTM c₁ c₂ fun x ↦
        (ctm_haltsWithin_iff_runsInTime hnon x _).mp (hm x).1
      refine mem_SharpP_iff_exists_mem_SharpTIME.mpr
        ⟨g, c, K, k, State, hfin, machine, hnon, fun x ↦ ?_⟩
      have hh' := (ctm_haltsWithin_iff_runsInTime hnon x _).mpr (hK x)
      have hb1 := (hm x).1.branchCount_eq
        (Nat.le_max_left (c₁ * t x.length + c₂) (c * x.length ^ g + K)) (· == [true])
      have hb2 := hh'.branchCount_eq
        (Nat.le_max_right (c₁ * t x.length + c₂) (c * x.length ^ g + K)) (· == [true])
      exact ⟨hh', hb2.symm.trans (hb1.trans (hm x).2)⟩
  have hUP : UP encBits = UTIME encBits t := by
    ext A; simp only [UP, UTIME, Set.mem_ofPred_eq, hSharpP]
  have hPSPACE : PSPACE encBits = DSPACE encBits t := Set.Subset.antisymm
    (fun _ hA ↦ let ⟨d, hd⟩ := mem_PSPACE_iff_exists_mem_DSPACE.mp hA
      DSPACE_mono_of_eventually_le (ht_dom d) hd)
    fun _ ⟨c₁, c₂, timeFn, hdec⟩ ↦ by
      obtain ⟨f, ⟨k, State, hfin, tm, htm⟩, hf⟩ := decidableInTimeAndSpace_iff.mp hdec
      cases nonempty_fintype State
      let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
      let d := desc eS eBit tm
      have hsp_x : ∀ x : List Bool,
          haltsInSpaceBool d (x.map eBit) (c₁ * t x.length + c₂) = true := fun x ↦ by
        obtain ⟨⟨u, hhu, -⟩, -, hsp⟩ := htm x
        have hsim_u : (simulate d (x.map eBit) u).2 = true := by
          rw [simulate_desc, Option.isNone_iff_eq_none]; exact hhu
        obtain ⟨m, hm, _⟩ := exists_tmHaltingSteps_le_iff.mpr hsim_u
        exact haltsInSpaceBool_eq_true_iff.mpr ⟨m, hm,
          (simSpace_desc eS eBit tm x m).trans_le
            (hsp ⟨MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) m, rfl⟩)⟩
      obtain ⟨g, hg⟩ := h2 d (max c₁ c₂) fun x ↦
        haltsInSpaceBool_mono (mul_add_le_max_mul_add ..) (hsp_x x)
      obtain ⟨K, hK⟩ := affine_poly_from_tail
        (P := fun x S ↦ haltsInSpaceBool d (x.map eBit) S = true)
        (fun hS hs ↦ haltsInSpaceBool_mono hS hs) hsp_x hg
      refine mem_PSPACE_iff_exists_mem_DSPACE.mpr ⟨g, mem_DSPACE_iff.mpr
        ⟨max c₁ c₂, K, fun x ↦ timeFn x.length, decidableInTimeAndSpace_iff.mpr
          ⟨f, ⟨k, State, hfin, tm, fun x ↦ ?_⟩, hf⟩⟩⟩
      obtain ⟨m, hm, hmS⟩ := haltsInSpaceBool_eq_true_iff.mp (hK x)
      refine ⟨(htm x).1, (htm x).2.1, fun π ↦ ?_⟩
      change MultiTapeNTM.RunPath.space π.toRunPath ≤ _
      rw [π.eq_ofDeterministic]
      change (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) π.time).space ≤ _
      rw [← simSpace_desc eS eBit tm x π.time]
      rcases le_or_gt π.time m with hjm | hmj
      · exact (simSpace_mono d (x.map eBit) hjm).trans hmS
      · exact (simSpace_eq_of_halted hmj.le (mem_tmHaltingSteps_iff.mp hm).1) ▸ hmS
  have hMod : ∀ k : ℕ, ModP k encBits = ModTIME k encBits t := fun k ↦ by
    ext A; simp only [ModP, ModTIME, Set.mem_ofPred_eq, hSharpP]
  have hAlt : ∀ (q : Bool) (k : ℕ),
      {A | ∃ (ps : List (Polynomial ℕ)) (V : List Bool × List Bool → Bool),
        ps.length = k ∧ ComputableInPolyTime V (encPair encBits encBits) encBool ∧
        IsAlternatingVerifier encBits q ps V A} = AltTIME q k encBits t := fun q k ↦
    Set.Subset.antisymm
      (fun _ hA ↦ let ⟨d, hd⟩ := mem_altP_iff_exists_mem_AltTIME.mp hA
        AltTIME_mono_of_eventually_le (ht_dom d) hd)
      fun _ ⟨ps, V, c₁, c₂, s, m, State, hfin, tm, hlen, hver, _, hall⟩ ↦ by
        have hdt : {x | V x = true} ∈ DTIME (encPair encBits encBits) t :=
          ⟨c₁, c₂, s, decidableInTimeAndSpace_iff.mpr
            ⟨V, ⟨m, State, hfin, tm, hall⟩, fun _ ↦ Iff.rfl⟩⟩
        rw [← hPpair] at hdt
        obtain ⟨V', hV', hiff⟩ := hdt
        exact ⟨ps, V, hlen, (funext fun x ↦ Bool.eq_iff_iff.mpr (hiff x).symm) ▸ hV', hver⟩
  have hAP : AP encBits = ATIME encBits t := Set.Subset.antisymm
    (fun _ hA ↦ let ⟨d, hd⟩ := mem_AP_iff_exists_mem_ATIME.mp hA
      ATIME_mono_of_eventually_le (ht_dom d) hd)
    fun _ ⟨c₁, c₂, k, State, hfin, atm, hdec⟩ ↦
      let ⟨g, c, K, hK⟩ := hNTM atm.toPTM.toNTM c₁ c₂ fun x ↦ (hdec x).1
      mem_AP_iff_exists_mem_ATIME.mpr ⟨g, c, K, k, State, hfin, atm, fun x ↦ ⟨hK x, (hdec x).2⟩⟩
  refine ⟨t, ht_comp, ht_mono, ht_dom, hP, hNP, ?_, hPP, hBPP, by rw [← hPpair, BPOp_P],
    hRP, ?_, hUP, ?_, hPSPACE, hSharpP, ?_, by rw [← hPpair]; rfl, hMod, ?_,
    fun k ↦ hAlt true k, fun k ↦ hAlt false k, hAP⟩
  · ext A; change Aᶜ ∈ NP encBits ↔ Aᶜ ∈ NTIME encBits t; rw [hNP]
  · ext A; change Aᶜ ∈ RP encBits ↔ Aᶜ ∈ RTIME encBits t; rw [hRP]
  · ext A; change Aᶜ ∈ UP encBits ↔ Aᶜ ∈ UTIME encBits t; rw [hUP]
  · ext A; simp only [mem_ParityP_iff_exists_SharpP, ParityTIME, Set.mem_ofPred_eq, hSharpP]
  · intro k; ext A; change Aᶜ ∈ ModP k encBits ↔ Aᶜ ∈ ModTIME k encBits t; rw [hMod k]

end Cslib.Complexity
