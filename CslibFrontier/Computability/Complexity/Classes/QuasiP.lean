module

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Problems.Coloring

import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Logics.Propositional.CNF.Compact
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quasipolynomial Time, NP-Intermediate Problems, and Subexponential Lower Bounds

Defines the deterministic quasipolynomial time class `QuasiP`, the intermediate complexity
predicates `NPIntermediate` and `coNPIntermediate`, and the quasipolynomial subexponential time
predicate `DecidableInQuasiSubexpTime` (deterministic time `2 ^ o((log |enc a|) ^ r)`).

Also develops:
- Closure of `QuasiP` under complement and polynomial-time many-one reductions, together with
  `P ⊆ QuasiP ⊆ EXP`.
- Unconditional input-horizon lower bounds for `Turing.MultiTapeTM` ruling out
  `DecidableInQuasiSubexpTime A enc 1` (`o(n)` time) from indistinguishable prefix pairs.
- Fine-grained transfer from `DecidableInQuasiSubexpTime B encB r` (`r ≥ 2`) along
  `2 ^ O(m ^ (1 / r))`-time reductions with `O(m ^ (1 / r))` log-output length to
  `DecidableInSubexpTime A encA m`.
- Under `Cslib.Complexity.ETH`, linear-size `KColoring k` lower bounds (`k ≥ 3`), and non-membership
  of `ThreeSAT` (and every `NP`-complete / `coNP`-complete problem) in `QuasiP`.

## Main definitions

- `Cslib.Complexity.QuasiP`: deterministic quasipolynomial time
  `⋃ c, DTIME enc (fun n ↦ 2 ^ Nat.log 2 n ^ c)`.
- `Cslib.Complexity.NPIntermediate`,
  `Cslib.Complexity.coNPIntermediate`: `NP`- and `coNP`-intermediate problems.
- `Cslib.Complexity.DecidableInQuasiSubexpTime`: deterministic time
  `2 ^ o((log |enc a|) ^ r)`.

## Main results

- `Cslib.Complexity.P_subset_QuasiP`,
  `Cslib.Complexity.QuasiP_subset_EXP`,
  `Cslib.Complexity.compl_mem_QuasiP`,
  `Cslib.Complexity.PolyTimeReducible.mem_QuasiP`: structural properties of
  `QuasiP`.
- `Cslib.Complexity.not_decidableInQuasiSubexpTime_one_of_prefix_indistinguishable`
  : unconditional `MultiTapeTM` input-horizon lower bound for `r = 1`.
- `Cslib.Complexity.DecidableInQuasiSubexpTime.decidableInSubexpTime_of_reduction`:
  subexponential transfer from `2 ^ o((log S) ^ r)` deciders (`r ≥ 2`).
- `Cslib.Complexity.ETH.not_decidableInSubexpTime_KColoring`: under `ETH`,
  `KColoring k` (`k ≥ 3`) is not decidable in `2 ^ o(|V| + |E|)` time.
- `Cslib.Complexity.ETH.not_NPComplete_of_mem_QuasiP`,
  `Cslib.Complexity.ETH.not_coNPComplete_of_mem_QuasiP`: under `ETH`, no
  `NP`-complete or `coNP`-complete problem lies in `QuasiP`.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL Filter Turing Turing.MultiTapeTM

/-! ### Quasipolynomial time and intermediate classes -/

section Classes

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- Deterministic quasipolynomial time: problems decidable in time `O(2 ^ (log₂ n) ^ c)` for some
constant `c : ℕ` on instances whose binary encoding has length `n`. -/
def QuasiP (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ c : ℕ, DTIME enc fun n ↦ 2 ^ Nat.log 2 n ^ c

/-- Membership in `QuasiP` unfolds to membership in `DTIME` for some polylogarithmic exponent. -/
theorem mem_QuasiP_iff :
    A ∈ QuasiP enc ↔ ∃ c : ℕ, A ∈ DTIME enc fun n ↦ 2 ^ Nat.log 2 n ^ c :=
  Set.mem_iUnion

/-- A problem is `NP`-intermediate if it lies in `NP`, is not in `P`, and is not `NP`-complete. -/
def NPIntermediate {α : Type} (enc : α ↪ List Bool) (A : Set α) : Prop :=
  A ∈ NP enc ∧ A ∉ P enc ∧ ¬NPComplete enc A

/-- Characterization of `NP`-intermediate problems. -/
theorem npIntermediate_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    NPIntermediate enc A ↔ A ∈ NP enc ∧ A ∉ P enc ∧ ¬NPComplete enc A :=
  Iff.rfl

/-- A problem is `coNP`-intermediate if it lies in `coNP`, is not in `P`, and is not
`coNP`-complete. -/
def coNPIntermediate {α : Type} (enc : α ↪ List Bool) (A : Set α) : Prop :=
  A ∈ coNP enc ∧ A ∉ P enc ∧ ¬coNPComplete enc A

/-- Characterization of `coNP`-intermediate problems. -/
theorem coNPIntermediate_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    coNPIntermediate enc A ↔ A ∈ coNP enc ∧ A ∉ P enc ∧ ¬coNPComplete enc A :=
  Iff.rfl

/-- The complement of an `NP`-intermediate problem is `coNP`-intermediate. -/
theorem NPIntermediate.compl {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (h : NPIntermediate enc A) : coNPIntermediate enc Aᶜ :=
  ⟨by rw [mem_coNP, compl_compl]; exact h.1,
    fun hP ↦ h.2.1 (by simpa only [compl_compl] using compl_mem_P hP),
    fun hC ↦ h.2.2 (by simpa only [compl_compl] using hC.compl)⟩

/-- The complement of a `coNP`-intermediate problem is `NP`-intermediate. -/
theorem coNPIntermediate.compl {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (h : coNPIntermediate enc A) : NPIntermediate enc Aᶜ :=
  ⟨h.1, fun hP ↦ h.2.1 (by simpa only [compl_compl] using compl_mem_P hP),
    fun hC ↦ h.2.2 (by simpa only [compl_compl] using hC.compl)⟩

/-- Deterministic time `2 ^ o((log₂ |enc a|) ^ r)`: for every `δ > 0`, `A` is decidable within time
`O(2 ^ (δ * (Nat.log 2 (enc a).length) ^ r))` (with no extra polynomial factor, which is essential
when `r = 1`). -/
def DecidableInQuasiSubexpTime (A : Set α) (enc : α ↪ List Bool) (r : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    DecidableInTimeO A enc fun a ↦ (2 : ℝ) ^ (δ * ((Nat.log 2 (enc a).length : ℝ) ^ r))

private lemma pow_le_two_pow_log_pow (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, n ^ k ≤ 2 ^ Nat.log 2 n ^ (k + 2) := by
  filter_upwards [eventually_ge_atTop (2 ^ (k + 2))] with n hn
  have hlog : k + 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two hn
  have h1 : 1 ≤ Nat.log 2 n := by omega
  have h2 : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  calc n ^ k
      ≤ (2 ^ (Nat.log 2 n + 1)) ^ k := Nat.pow_le_pow_left h2 k
    _ = 2 ^ ((Nat.log 2 n + 1) * k) := by rw [← Nat.pow_mul]
    _ ≤ 2 ^ (Nat.log 2 n ^ (k + 2)) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have hmul : (Nat.log 2 n + 1) * k ≤ (k + 1) * Nat.log 2 n := by nlinarith
      have hpow : (k + 1) * Nat.log 2 n ≤ Nat.log 2 n * Nat.log 2 n :=
        Nat.mul_le_mul_right _ (by omega)
      have hsq : Nat.log 2 n ^ 2 ≤ Nat.log 2 n ^ (k + 2) :=
        Nat.pow_le_pow_right h1 (by omega)
      rw [sq] at hsq
      omega

/-- **Polynomial time is contained in quasipolynomial time.** -/
theorem P_subset_QuasiP : P enc ⊆ QuasiP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  exact mem_QuasiP_iff.mpr ⟨k + 2, DTIME_mono_of_eventually_le (pow_le_two_pow_log_pow k) hk⟩

/-- **Quasipolynomial time is contained in exponential time.** -/
theorem QuasiP_subset_EXP : QuasiP enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨c, hc⟩ := mem_QuasiP_iff.mp hA
  refine mem_EXP_iff.mpr ⟨c, DTIME_mono (fun n ↦ ?_) hc⟩
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (Nat.log_le_self 2 n) c)

/-- **`QuasiP` is closed under complement.** -/
theorem compl_mem_QuasiP {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ QuasiP enc) :
    Aᶜ ∈ QuasiP enc :=
  let ⟨c, hc⟩ := mem_QuasiP_iff.mp h
  mem_QuasiP_iff.mpr ⟨c, compl_mem_DTIME hc⟩

/-- The empty language lies in `QuasiP`. -/
@[simp] theorem empty_mem_QuasiP : (∅ : Set α) ∈ QuasiP enc :=
  P_subset_QuasiP empty_mem_P

/-- The universal language lies in `QuasiP`. -/
@[simp] theorem univ_mem_QuasiP : (Set.univ : Set α) ∈ QuasiP enc :=
  P_subset_QuasiP univ_mem_P

/-- Complement membership equivalence for `QuasiP`. -/
@[simp] theorem compl_mem_QuasiP_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    Aᶜ ∈ QuasiP enc ↔ A ∈ QuasiP enc :=
  ⟨fun h ↦ by simpa only [compl_compl] using compl_mem_QuasiP h, compl_mem_QuasiP⟩

private lemma log_mul_add_one_pow_eventually_le (c d k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Nat.log 2 (c * (n + 1) ^ d) ^ k ≤ Nat.log 2 n ^ (k + 1) := by
  set B := Nat.log 2 (c + 1) + 2 * d + 2
  filter_upwards [eventually_ge_atTop (max 2 (2 ^ (B ^ k + 1)))] with n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hlog_ge : B ^ k + 1 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le Nat.one_lt_two ((le_max_right _ _).trans hn)
  have hlog1 : 1 ≤ Nat.log 2 n := by omega
  have hbase : c * (n + 1) ^ d ≤ 2 ^ (B * Nat.log 2 n) := by
    have hn_le : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := by
      have := Nat.lt_pow_succ_log_self Nat.one_lt_two n; omega
    have hpow_le : (n + 1) ^ d ≤ 2 ^ (2 * d * Nat.log 2 n) := by
      calc (n + 1) ^ d
          ≤ (2 ^ (Nat.log 2 n + 1)) ^ d := Nat.pow_le_pow_left hn_le d
        _ = 2 ^ ((Nat.log 2 n + 1) * d) := by rw [← Nat.pow_mul]
        _ ≤ 2 ^ (2 * d * Nat.log 2 n) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_; nlinarith
    have hc_le : c ≤ 2 ^ (Nat.log 2 (c + 1) + 1) :=
      (Nat.le_succ c).trans (Nat.lt_pow_succ_log_self Nat.one_lt_two (c + 1)).le
    calc c * (n + 1) ^ d
        ≤ 2 ^ (Nat.log 2 (c + 1) + 1) * 2 ^ (2 * d * Nat.log 2 n) :=
          Nat.mul_le_mul hc_le hpow_le
      _ = 2 ^ (Nat.log 2 (c + 1) + 1 + 2 * d * Nat.log 2 n) := by rw [← Nat.pow_add]
      _ ≤ 2 ^ (B * Nat.log 2 n) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have : Nat.log 2 (c + 1) + 1 ≤ (Nat.log 2 (c + 1) + 2) * Nat.log 2 n := by nlinarith
        dsimp only [B]; nlinarith
  have hlog_le : Nat.log 2 (c * (n + 1) ^ d) ≤ B * Nat.log 2 n := by
    rcases eq_or_ne (c * (n + 1) ^ d) 0 with h0 | hne
    · simp [h0]
    · exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow hne
        (hbase.trans_lt (Nat.pow_lt_pow_right Nat.one_lt_two (by omega))))
  calc Nat.log 2 (c * (n + 1) ^ d) ^ k
      ≤ (B * Nat.log 2 n) ^ k := Nat.pow_le_pow_left hlog_le k
    _ = B ^ k * Nat.log 2 n ^ k := Nat.mul_pow B (Nat.log 2 n) k
    _ ≤ Nat.log 2 n * Nat.log 2 n ^ k := Nat.mul_le_mul_right _ (by omega)
    _ = Nat.log 2 n ^ (k + 1) := by rw [pow_succ']

/-- **`QuasiP` is closed under polynomial-time many-one reductions.** -/
theorem PolyTimeReducible.mem_QuasiP {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ QuasiP encB) :
    A ∈ QuasiP encA := by
  obtain ⟨f, hf, hred⟩ := hAB
  obtain ⟨k, hk⟩ := mem_QuasiP_iff.mp hB
  obtain ⟨d₁, _, hdeg⟩ := hf.exists_degree
  obtain ⟨c₀, d₂, hcd⟩ := hf.polyBounded_length.exists_le
  set c : ℕ := c₀ + 1
  set d : ℕ := max d₁ d₂
  have hpre : f ⁻¹' B ∈ DTIME encA
      (fun n ↦ c * (n + 1) ^ d + 2 ^ Nat.log 2 (c * (n + 1) ^ d) ^ k) := by
    refine preimage_mem_DTIME (C := 1) hk hdeg.inO fun a ↦ ?_
    have hca : (encB (f a)).length ≤ c * ((encA a).length + 1) ^ d :=
      (hcd a).trans (Nat.mul_le_mul (Nat.le_succ c₀)
        (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right d₁ d₂)))
    have hT : ((encA a).length + 1) ^ d₁ ≤ c * ((encA a).length + 1) ^ d :=
      (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left d₁ d₂)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos c₀))
    have hlog : Nat.log 2 (encB (f a)).length ≤ Nat.log 2 (c * ((encA a).length + 1) ^ d) :=
      Nat.log_mono_right hca
    have hpow : 2 ^ Nat.log 2 (encB (f a)).length ^ k ≤
        2 ^ Nat.log 2 (c * ((encA a).length + 1) ^ d) ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hlog k)
    omega
  have hA_eq : A = f ⁻¹' B := Set.ext hred
  rw [hA_eq]
  refine mem_QuasiP_iff.mpr ⟨k + d + 4, DTIME_mono_of_eventually_le ?_ hpre⟩
  filter_upwards [log_mul_add_one_pow_eventually_le c d k,
    pow_le_two_pow_log_pow (d + 1),
    eventually_ge_atTop (max 4 ((c + 1) * 2 ^ d))] with n h1 h2 h3
  have hn4 : 4 ≤ n := (le_max_left _ _).trans h3
  have hc_le : (c + 1) * 2 ^ d ≤ n := (le_max_right _ _).trans h3
  have hlog2 : 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two (by norm_num; omega)
  have hlog1 : 1 ≤ Nat.log 2 n := by omega
  have hpoly : c * (n + 1) ^ d ≤ 2 ^ Nat.log 2 n ^ (d + 3) := by
    have hstep : c * (n + 1) ^ d ≤ n ^ (d + 1) := by
      have hn1 : n + 1 ≤ 2 * n := by omega
      calc c * (n + 1) ^ d
          ≤ c * (2 * n) ^ d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hn1 d)
        _ = (c * 2 ^ d) * n ^ d := by rw [Nat.mul_pow]; ring
        _ ≤ n * n ^ d := Nat.mul_le_mul_right _ (by
          have : c * 2 ^ d ≤ (c + 1) * 2 ^ d := Nat.mul_le_mul_right _ (Nat.le_succ c)
          omega)
        _ = n ^ (d + 1) := by rw [pow_succ']
    exact hstep.trans h2
  have hlog_mono1 : Nat.log 2 n ^ (k + 1) ≤ Nat.log 2 n ^ (k + d + 3) :=
    Nat.pow_le_pow_right hlog1 (by omega)
  have hlog_mono2 : Nat.log 2 n ^ (d + 3) ≤ Nat.log 2 n ^ (k + d + 3) :=
    Nat.pow_le_pow_right hlog1 (by omega)
  have hterm1 : c * (n + 1) ^ d ≤ 2 ^ Nat.log 2 n ^ (k + d + 3) :=
    hpoly.trans (Nat.pow_le_pow_right (by norm_num) hlog_mono2)
  have hterm2 : 2 ^ Nat.log 2 (c * (n + 1) ^ d) ^ k ≤ 2 ^ Nat.log 2 n ^ (k + d + 3) :=
    Nat.pow_le_pow_right (by norm_num) (h1.trans hlog_mono1)
  calc c * (n + 1) ^ d + 2 ^ Nat.log 2 (c * (n + 1) ^ d) ^ k
      ≤ 2 ^ Nat.log 2 n ^ (k + d + 3) + 2 ^ Nat.log 2 n ^ (k + d + 3) :=
        Nat.add_le_add hterm1 hterm2
    _ = 2 ^ (Nat.log 2 n ^ (k + d + 3) + 1) := by rw [← two_mul, ← pow_succ']
    _ ≤ 2 ^ Nat.log 2 n ^ (k + d + 4) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have hge : 2 * Nat.log 2 n ^ (k + d + 3) ≤ Nat.log 2 n * Nat.log 2 n ^ (k + d + 3) :=
        Nat.mul_le_mul_right _ hlog2
      have hpos : 1 ≤ Nat.log 2 n ^ (k + d + 3) := Nat.one_le_pow _ _ hlog1
      have hrhs : Nat.log 2 n ^ (k + d + 4) = Nat.log 2 n * Nat.log 2 n ^ (k + d + 3) :=
        pow_succ' _ _
      omega

/-- `DecidableInQuasiSubexpTime` is closed under complement. -/
theorem DecidableInQuasiSubexpTime.compl {α : Type} {enc : α ↪ List Bool} {A : Set α} {r : ℕ}
    (h : DecidableInQuasiSubexpTime A enc r) :
    DecidableInQuasiSubexpTime Aᶜ enc r := by
  intro δ hδ
  obtain ⟨g, t, c, hg, hgA, ht⟩ := (h δ hδ).exists_computableInO
  refine DecidableInTimeO.mono (T := fun a ↦ (t a : ℝ))
    (DecidableInTimeO.of_computableInO hg.not' (fun a ↦ by simp [hgA]) fun _ ↦ le_rfl)
    c (fun a ↦ by simpa using ht a) (fun _ ↦ by positivity)

/-- `DecidableInQuasiSubexpTime` is monotone in the exponent `r`. -/
theorem DecidableInQuasiSubexpTime.mono {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    (h : DecidableInQuasiSubexpTime A enc r₁) : DecidableInQuasiSubexpTime A enc r₂ := by
  intro δ hδ
  refine (h δ hδ).mono ⌈(2 : ℝ) ^ δ⌉₊ (fun a ↦ ?_) (fun _ ↦ by positivity)
  have hceil : (2 : ℝ) ^ δ ≤ (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) := Nat.le_ceil _
  have h2δ : (1 : ℝ) ≤ (2 : ℝ) ^ δ := Real.one_le_rpow (by norm_num) hδ.le
  have hC1 : (1 : ℝ) ≤ (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) := h2δ.trans hceil
  have hC0 : (0 : ℝ) ≤ (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (Nat.log 2 (enc a).length) with hz | hpos
  · rcases Nat.eq_zero_or_pos r₁ with rfl | hr1
    · simp only [hz, Nat.cast_zero, pow_zero, mul_one]
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (0 : ℝ) ^ r₂) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hmul : (2 : ℝ) ^ δ ≤ (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (0 : ℝ) ^ r₂) := by
        simpa only [mul_one] using mul_le_mul hceil h1 (by positivity) hC0
      linarith
    · have hbase : ((Nat.log 2 (enc a).length : ℝ) ^ r₁) ≤ (Nat.log 2 (enc a).length : ℝ) ^ r₂ := by
        simp [hz, zero_pow (Nat.ne_of_gt hr1), zero_pow (Nat.ne_of_gt (hr1.trans_le hr))]
      have hpow : (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₁) ≤
          (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₂) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hbase hδ.le)
      have hmul : (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₂) ≤
          (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₂) :=
        le_mul_of_one_le_left (by positivity) hC1
      linarith
  · have hbase : ((Nat.log 2 (enc a).length : ℝ) ^ r₁) ≤ (Nat.log 2 (enc a).length : ℝ) ^ r₂ :=
      pow_le_pow_right₀ (by exact_mod_cast hpos) hr
    have hpow : (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₁) ≤
        (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₂) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hbase hδ.le)
    have hmul : (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₂) ≤
        (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (Nat.log 2 (enc a).length : ℝ) ^ r₂) :=
      le_mul_of_one_le_left (by positivity) hC1
    linarith

/-- For `r ≥ 2`, every problem in `P` is decidable in `2 ^ o((log₂ n) ^ r)` time. -/
theorem DecidableInQuasiSubexpTime.of_mem_P {r : ℕ} (hr : 2 ≤ r) (hP : A ∈ P enc) :
    DecidableInQuasiSubexpTime A enc r := by
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hP
  have htime := mem_DTIME_iff_decidableInTimeO.mp hk
  intro δ hδ
  set t₀ : ℕ := ⌈(2 * (k : ℝ) + 1) / δ⌉₊ + 2
  set M : ℕ := k * (t₀ + 1)
  refine htime.mono ⌈(2 : ℝ) ^ (M : ℝ)⌉₊ (fun a ↦ ?_) (fun _ ↦ by positivity)
  set t : ℕ := Nat.log 2 (enc a).length
  have hL : ((enc a).length : ℝ) ≤ (2 : ℝ) ^ (t + 1) := by
    have := (Nat.lt_pow_succ_log_self Nat.one_lt_two (enc a).length).le
    exact_mod_cast this
  have hLk : (((enc a).length ^ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((k * (t + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hL k
  have hexp : ((k * (t + 1) : ℕ) : ℝ) ≤ (M : ℝ) + δ * ((t : ℝ) ^ r) := by
    by_cases ht : t ≤ t₀
    · have : k * (t + 1) ≤ M := Nat.mul_le_mul_left k (Nat.add_le_add_right ht 1)
      have hcast : ((k * (t + 1) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
      have hnonneg : 0 ≤ δ * ((t : ℝ) ^ r) := by positivity
      linarith
    · push Not at ht
      have ht_ge : (2 * (k : ℝ) + 1) / δ ≤ (t : ℝ) := by
        have h1 : (2 * (k : ℝ) + 1) / δ ≤ (t₀ : ℝ) := by
          have := Nat.le_ceil ((2 * (k : ℝ) + 1) / δ)
          dsimp only [t₀]; push_cast; linarith
        exact h1.trans (by exact_mod_cast ht.le)
      have hmul : 2 * (k : ℝ) + 1 ≤ δ * (t : ℝ) := by
        linarith [(div_le_iff₀ hδ).mp ht_ge]
      have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
      have ht2 : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ r := pow_le_pow_right₀ ht1 hr
      have hquad : (k : ℝ) * ((t : ℝ) + 1) ≤ δ * ((t : ℝ) ^ r) := by
        have h2t : (k : ℝ) * ((t : ℝ) + 1) ≤ (2 * (k : ℝ) + 1) * (t : ℝ) := by nlinarith
        have h3t : (2 * (k : ℝ) + 1) * (t : ℝ) ≤ δ * ((t : ℝ) ^ 2) := by
          rw [sq]; nlinarith
        exact h2t.trans (h3t.trans (mul_le_mul_of_nonneg_left ht2 hδ.le))
      push_cast
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
  have hpow : (2 : ℝ) ^ ((k * (t + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) + δ * ((t : ℝ) ^ r)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  rw [Real.rpow_add (by norm_num)] at hpow
  have hceil : (2 : ℝ) ^ (M : ℝ) ≤ (⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hpos : 0 ≤ (2 : ℝ) ^ (δ * ((t : ℝ) ^ r)) := by positivity
  have hmain := hLk.trans (hpow.trans (mul_le_mul_of_nonneg_right hceil hpos))
  have hC0 : (0 : ℝ) ≤ (⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith

/-- If `A` is not decidable in `2 ^ o((log₂ n) ^ r)` time for some `r ≥ 2`, then `A ∉ P`. -/
theorem not_mem_P_of_not_decidableInQuasiSubexpTime {r : ℕ} (hr : 2 ≤ r)
    (h : ¬DecidableInQuasiSubexpTime A enc r) : A ∉ P enc :=
  fun hP ↦ h (.of_mem_P hr hP)

end Classes

/-! ### Unconditional `MultiTapeTM` input-horizon lower bound (`r = 1`) -/

section InputHorizon

private lemma inputAt_eq_of_take_eq {x y : List Bool} {t j : ℕ}
    (htake : x.take t = y.take t) (hj : j ≤ t) :
    inputAt x j = inputAt y j := by
  simp only [inputAt]
  split_ifs with h0
  · rfl
  · have hlt : j - 1 < t := by omega
    have hx : x[j - 1]? = (x.take t)[j - 1]? := by
      rw [List.getElem?_take_of_lt hlt]
    have hy : y[j - 1]? = (y.take t)[j - 1]? := by
      rw [List.getElem?_take_of_lt hlt]
    rw [hx, hy, htake]

private lemma moveInputPosNat_eq_of_lt {nx ny j : ℕ} (d : SignType)
    (hx : j < nx) (hy : j < ny) :
    moveInputPosNat nx j d = moveInputPosNat ny j d := by
  rcases d with _ | _ | _ <;>
    simp only [moveInputPosNat, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
      SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one] <;> omega

/-- **Input-horizon lemma for `MultiTapeTM`**: if two binary inputs `x` and `y` have length
strictly greater than `t` and agree on their first `t` symbols, then after any `s ≤ t` steps from
the initial configuration, a deterministic multi-tape machine reaches the same state, input head
position (bounded by `s + 1`), work tapes, and output on `x` and `y`. -/
theorem runFrom_agree_of_prefix {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State)
    {x y : List Bool} {t : ℕ} (htx : t < x.length) (hty : t < y.length)
    (htake : x.take t = y.take t) {s : ℕ} (hs : s ≤ t) :
    let cx := tm.runFrom (tm.initCfg x) s
    let cy := tm.runFrom (tm.initCfg y) s
    cx.state = cy.state ∧ cx.inputPos.val = cy.inputPos.val ∧ cx.inputPos.val ≤ s + 1 ∧
      cx.workTapePos = cy.workTapePos ∧ cx.workTapes = cy.workTapes ∧ cx.output = cy.output := by
  induction s with
  | zero =>
    simp [MultiTapeTM.runFrom, MultiTapeNTM.initCfg, Cfg.init]
  | succ s ih =>
    obtain ⟨hstate, hpos, hle, hwpos, hwtapes, hout⟩ := ih (Nat.le_of_succ_le hs)
    set cx := tm.runFrom (tm.initCfg x) s
    set cy := tm.runFrom (tm.initCfg y) s
    rw [MultiTapeTM.runFrom_succ, MultiTapeTM.runFrom_succ]
    change (tm.step cx).state = (tm.step cy).state ∧
      (tm.step cx).inputPos.val = (tm.step cy).inputPos.val ∧
      (tm.step cx).inputPos.val ≤ s + 2 ∧
      (tm.step cx).workTapePos = (tm.step cy).workTapePos ∧
      (tm.step cx).workTapes = (tm.step cy).workTapes ∧
      (tm.step cx).output = (tm.step cy).output
    have hinp : cx.inputSymbol = cy.inputSymbol := by
      rw [Cfg.inputSymbol_eq_inputAt, Cfg.inputSymbol_eq_inputAt, hpos]
      exact inputAt_eq_of_take_eq htake (by omega)
    have hwsym : cx.workTapeSymbols = cy.workTapeSymbols := by
      funext i
      simp only [Cfg.workTapeSymbols, hwpos, hwtapes]
    cases hstx : cx.state with
    | none =>
      have hsty : cy.state = none := hstate.symm.trans hstx
      rw [MultiTapeTM.step_of_halt hstx, MultiTapeTM.step_of_halt hsty]
      exact ⟨hstate, hpos, by omega, hwpos, hwtapes, hout⟩
    | some q =>
      have hsty : cy.state = some q := hstate.symm.trans hstx
      rw [MultiTapeTM.step_of_state hstx, MultiTapeTM.step_of_state hsty, hinp, hwsym]
      set act := tm.tr q cy.inputSymbol cy.workTapeSymbols
      have hpos' : (moveInputPos cx.inputPos act.inputTape).val =
          (moveInputPos cy.inputPos act.inputTape).val := by
        rw [val_moveInputPos_eq_moveInputPosNat, val_moveInputPos_eq_moveInputPosNat, hpos]
        exact moveInputPosNat_eq_of_lt act.inputTape (by omega) (by omega)
      have hstep_le : (moveInputPos cx.inputPos act.inputTape).val ≤ s + 2 :=
        (val_moveInputPos_le cx.inputPos act.inputTape).trans (by omega)
      refine ⟨rfl, hpos', hstep_le, ?_, ?_, ?_⟩
      · funext i; simp only [Action.apply_workTapePos, hwpos]
      · funext i z; simp only [Action.apply_workTapes_eq_ite, hwpos, hwtapes]
      · simp only [Action.apply_output, hout]

/-- **Unconditional `o(n)` lower bound (`r = 1`)**: if for arbitrarily large `n` there exist
`a ∈ A` and `b ∉ A` whose encodings have length at least `n + 1`, agree on their first `n` bits,
and satisfy `(enc a).length ≤ C * (n + 1)`, then `A` is not decidable in `2 ^ o(log₂ |enc x|)`
time. -/
theorem not_decidableInQuasiSubexpTime_one_of_prefix_indistinguishable {α : Type}
    {enc : α ↪ List Bool} {A : Set α} {C : ℕ}
    (h : ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ a b : α, a ∈ A ∧ b ∉ A ∧
      n < (enc a).length ∧ n < (enc b).length ∧
      (enc a).length ≤ C * (n + 1) ∧ (enc a).take n = (enc b).take n) :
    ¬DecidableInQuasiSubexpTime A enc 1 := by
  intro hdec
  obtain ⟨c, t, s, ht, htm⟩ := hdec (1 / 2) (by norm_num)
  obtain ⟨f, ⟨k, State, _, tm, hcomp⟩, hfA⟩ := decidableInTimeAndSpace_iff.mp htm
  -- Choose `n₀` large enough that `c * √(C * (n + 1)) + c < n` for all `n ≥ n₀`.
  set n₀ : ℕ := 2 * (c + 1) ^ 2 * (C + 1) + 4 * c + 4
  obtain ⟨n, hn, a, b, haA, hbA, hna, hnb, hlen, htake⟩ := h n₀
  have hta : t a < n := by
    have hta_real : (t a : ℝ) ≤
      c * (2 : ℝ) ^ ((1 / 2 : ℝ) * (Nat.log 2 (enc a).length : ℝ)) + c := by
      simpa only [pow_one] using ht a
    have hsq : ((2 : ℝ) ^ ((1 / 2 : ℝ) * (Nat.log 2 (enc a).length : ℝ))) ^ 2 ≤
        ((enc a).length : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have hhalf : (1 / 2 : ℝ) * (Nat.log 2 (enc a).length : ℝ) * (2 : ℕ) =
          (Nat.log 2 (enc a).length : ℝ) := by push_cast; ring
      rw [hhalf, Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hpow_le : (2 : ℝ) ^ ((1 / 2 : ℝ) * (Nat.log 2 (enc a).length : ℝ)) ≤
        ((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ) + ((n : ℝ) / (2 * (c + 1 : ℝ))) := by
      -- Since `x^2 ≤ C*(n+1) ≤ ((c+1)*(C+1) + n/(2*(c+1)))^2`:
      have hpos : 0 ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * (Nat.log 2 (enc a).length : ℝ)) := by positivity
      have hrhs : 0 ≤ ((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ) + ((n : ℝ) / (2 * (c + 1 : ℝ))) := by
        positivity
      have hlen_real : ((enc a).length : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hlen
      have hc1 : (0 : ℝ) < (c + 1 : ℝ) := by positivity
      have hsq_rhs : (C : ℝ) * ((n : ℝ) + 1) ≤
          (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ) + ((n : ℝ) / (2 * (c + 1 : ℝ)))) ^ 2 := by
        have hcross : 2 * (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ)) *
            ((n : ℝ) / (2 * (c + 1 : ℝ))) = ((C + 1 : ℕ) : ℝ) * (n : ℝ) := by
          push_cast; field_simp [hc1.ne']
        have hfirst : (C : ℝ) ≤ (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ)) ^ 2 := by
          have : (C : ℝ) ≤ (C + 1 : ℝ) := by linarith
          have h1 : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ (c + 1) * (C + 1) by nlinarith)
          have h2 : (C : ℝ) ≤ ((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ) := by
            push_cast; nlinarith
          nlinarith
        have hnonneg : 0 ≤ ((n : ℝ) / (2 * (c + 1 : ℝ))) ^ 2 := sq_nonneg _
        have hexpand : (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ) + ((n : ℝ) / (2 * (c + 1 : ℝ)))) ^ 2 =
            (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ)) ^ 2 + ((C + 1 : ℕ) : ℝ) * (n : ℝ) +
              ((n : ℝ) / (2 * (c + 1 : ℝ))) ^ 2 := by
          ring_nf at hcross ⊢; linarith
        rw [hexpand]; push_cast at *; nlinarith
      nlinarith [hsq.trans (hlen_real.trans hsq_rhs)]
    have hmul_le : (c : ℝ) * (2 : ℝ) ^ ((1 / 2 : ℝ) * (Nat.log 2 (enc a).length : ℝ)) ≤
        (c : ℝ) * (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ)) + (n : ℝ) / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hpow_le (Nat.cast_nonneg c)
      have hc1 : (0 : ℝ) < (c + 1 : ℝ) := by positivity
      have h2 : (c : ℝ) * ((n : ℝ) / (2 * (c + 1 : ℝ))) ≤ (n : ℝ) / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hlt_real : (t a : ℝ) < (n : ℝ) := by
      have hn_real : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hbound : (c : ℝ) * (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ)) + (c : ℝ) < (n : ℝ) / 2 := by
        have : (c : ℝ) * (((c + 1 : ℕ) : ℝ) * ((C + 1 : ℕ) : ℝ)) ≤
            (((c + 1) ^ 2 * (C + 1) : ℕ) : ℝ) := by
          push_cast; nlinarith
        dsimp only [n₀] at hn_real
        push_cast at hn_real this ⊢
        linarith
      linarith
    exact_mod_cast hlt_real
  have htake' : (enc a).take (t a) = (enc b).take (t a) := by
    have h1 : ((enc a).take n).take (t a) = (enc a).take (t a) := by
      rw [List.take_take, Nat.min_eq_left hta.le]
    have h2 : ((enc b).take n).take (t a) = (enc b).take (t a) := by
      rw [List.take_take, Nat.min_eq_left hta.le]
    rw [← h1, ← h2, htake]
  obtain ⟨hstate, -, -, -, -, hout⟩ :=
    runFrom_agree_of_prefix tm (hta.trans hna) (hta.trans hnb) htake' le_rfl
  obtain ⟨hhalt_a, hout_a⟩ := (hcomp a).runFrom_of_le (le_refl (t a))
  have hhalt_b : (tm.runFrom (tm.initCfg (enc b)) (t a)).Halted :=
    hstate.symm.trans hhalt_a
  have hfa : f a = true := (hfA a).mp haA
  have hfb : f b = false := by
    cases h : f b
    · rfl
    · exact absurd ((hfA b).mpr h) hbA
  have hout_b_ta : (tm.runFrom (tm.initCfg (enc b)) (t a)).output = [true] := by
    rw [← hout, hout_a, hfa]; rfl
  obtain ⟨-, hout_b_J⟩ := (hcomp b).runFrom_of_le (le_max_right (t a) (t b))
  have hout_b_J' : (tm.runFrom (tm.initCfg (enc b)) (max (t a) (t b))).output = [true] := by
    rw [MultiTapeTM.runFrom_eq_of_halt tm _ (le_max_left (t a) (t b)) hhalt_b, hout_b_ta]
  rw [hout_b_J, hfb] at hout_b_J'
  exact Bool.false_ne_true (List.head_eq_of_cons_eq hout_b_J')

end InputHorizon

/-! ### Subexponential transfer from `2 ^ o((log₂ S) ^ r)` deciders (`r ≥ 2`) -/

section SubexpTransfer

private lemma natNthRoot_exists {r : ℕ} (hr : 0 < r) (m : ℕ) :
    ∃ k : ℕ, m < (k + 1) ^ r :=
  ⟨m, by
    have h1 : m + 1 ≤ (m + 1) ^ r := Nat.le_self_pow (Nat.ne_of_gt hr) (m + 1)
    omega⟩

/-- Elementary integer `r`-th root `⌊m ^ (1 / r)⌋` (`0` for `r = 0`), defined without real-analysis
dependencies. -/
def natNthRoot (r m : ℕ) : ℕ :=
  if hr : 0 < r then Nat.find (natNthRoot_exists hr m) else 0

/-- For `0 < r`, `m < (natNthRoot r m + 1) ^ r`. -/
theorem lt_succ_natNthRoot_pow {r : ℕ} (hr : 0 < r) (m : ℕ) :
    m < (natNthRoot r m + 1) ^ r := by
  simp only [natNthRoot, hr, dite_true]
  exact Nat.find_spec (natNthRoot_exists hr m)

/-- For `0 < r`, `(natNthRoot r m) ^ r ≤ m`. -/
theorem natNthRoot_pow_le {r : ℕ} (hr : 0 < r) (m : ℕ) :
    (natNthRoot r m) ^ r ≤ m := by
  simp only [natNthRoot, hr, dite_true]
  set k := Nat.find (natNthRoot_exists hr m)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, zero_pow (Nat.ne_of_gt hr)]; exact Nat.zero_le m
  · have hprev : ¬ m < (k - 1 + 1) ^ r :=
      Nat.find_min (natNthRoot_exists hr m) (Nat.sub_lt hk Nat.one_pos)
    rw [Nat.sub_add_cancel hk] at hprev
    exact Nat.le_of_not_lt hprev

/-- Characterization `k ≤ natNthRoot r m ↔ k ^ r ≤ m` for `0 < r`. -/
theorem le_natNthRoot_iff {r k m : ℕ} (hr : 0 < r) :
    k ≤ natNthRoot r m ↔ k ^ r ≤ m := by
  constructor
  · intro hk
    exact (Nat.pow_le_pow_left hk r).trans (natNthRoot_pow_le hr m)
  · intro hkm
    by_contra hlt
    push Not at hlt
    have h2 : (natNthRoot r m + 1) ^ r ≤ k ^ r := Nat.pow_le_pow_left hlt r
    have h3 : m < (natNthRoot r m + 1) ^ r := lt_succ_natNthRoot_pow hr m
    omega

/-- **Subexponential transfer from quasipolynomial-subexponential deciders** (`r ≥ 2`): if `f`
reduces `A` to `B` in time `O(2 ^ (D * (natNthRoot r (m a) + 1)) * (|encA a| + 1) ^ D)` with
log-output length `Nat.log 2 (encB (f a)).length ≤ K * (natNthRoot r (m a) + 1)`, then a
`2 ^ o((log₂ S) ^ r)` decider for `B` yields a `2 ^ o(m a)` decider for `A`. -/
theorem DecidableInQuasiSubexpTime.decidableInSubexpTime_of_reduction {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β} {m : α → ℕ}
    {r C D K : ℕ} (hr : 2 ≤ r) {f : α → β}
    (hf : ComputableInO f encA encB
      (fun a ↦ C * 2 ^ (D * (natNthRoot r (m a) + 1)) * ((encA a).length + 1) ^ D)
      (fun a ↦ C * 2 ^ (D * (natNthRoot r (m a) + 1)) * ((encA a).length + 1) ^ D))
    (hmem : ∀ a, a ∈ A ↔ f a ∈ B)
    (hlog : ∀ a, Nat.log 2 (encB (f a)).length ≤ K * (natNthRoot r (m a) + 1))
    (hB : DecidableInQuasiSubexpTime B encB r) :
    DecidableInSubexpTime A encA m := by
  intro δ hδ
  set K' : ℕ := max 1 K
  set δB : ℝ := δ / (2 * (2 * (K' : ℝ)) ^ r)
  have hδB : 0 < δB := by positivity
  obtain ⟨g, tg, cg, hg, hgB, htg⟩ := (hB δB hδB).exists_computableInO
  set t₀ : ℕ := ⌈(2 * (D : ℝ) + 1) / (δ / 2)⌉₊ + 2
  set M₁ : ℕ := D * (t₀ + 1)
  set M₂ : ℕ := ⌈δB * (2 * (K' : ℝ)) ^ r⌉₊ + 1
  set Coeff : ℕ := C * ⌈(2 : ℝ) ^ (M₁ : ℝ)⌉₊ + cg * ⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ + cg + 1
  refine DecidableInExpTime.of_computableInO (hg.comp hf)
    (fun a ↦ (hmem a).trans (hgB (f a))) Coeff D fun a ↦ ?_
  set n : ℕ := natNthRoot r (m a)
  have hr0 : 0 < r := by omega
  have hnr : n ^ r ≤ m a := natNthRoot_pow_le hr0 (m a)
  -- Bound the reduction time `C * 2^(D*(n+1)) * (L+1)^D` by `C * 2^M₁ * 2^((δ/2)*m a) * (L+1)^D`.
  have hred_exp : ((D * (n + 1) : ℕ) : ℝ) ≤ (M₁ : ℝ) + (δ / 2) * (m a : ℝ) := by
    by_cases hn : n ≤ t₀
    · have : D * (n + 1) ≤ M₁ := Nat.mul_le_mul_left D (Nat.add_le_add_right hn 1)
      have hcast : ((D * (n + 1) : ℕ) : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast this
      linarith [show 0 ≤ (δ / 2) * (m a : ℝ) by positivity]
    · push Not at hn
      have hn_ge : (2 * (D : ℝ) + 1) / (δ / 2) ≤ (n : ℝ) := by
        have h1 : (2 * (D : ℝ) + 1) / (δ / 2) ≤ (t₀ : ℝ) := by
          have := Nat.le_ceil ((2 * (D : ℝ) + 1) / (δ / 2))
          dsimp only [t₀]; push_cast; linarith
        exact h1.trans (by exact_mod_cast hn.le)
      have hmul : 2 * (D : ℝ) + 1 ≤ (δ / 2) * (n : ℝ) := by
        linarith [(div_le_iff₀ (by positivity : (0 : ℝ) < δ / 2)).mp hn_ge]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have hnr_real : (n : ℝ) ^ r ≤ (m a : ℝ) := by exact_mod_cast hnr
      have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ r := pow_le_pow_right₀ hn1 hr
      have hquad : (D : ℝ) * ((n : ℝ) + 1) ≤ (δ / 2) * (m a : ℝ) := by
        have h1 : (D : ℝ) * ((n : ℝ) + 1) ≤ (2 * (D : ℝ) + 1) * (n : ℝ) := by nlinarith
        have h2 : (2 * (D : ℝ) + 1) * (n : ℝ) ≤ (δ / 2) * ((n : ℝ) ^ 2) := by
          rw [sq]; nlinarith
        exact h1.trans (h2.trans ((mul_le_mul_of_nonneg_left hn2 (by positivity)).trans
          (mul_le_mul_of_nonneg_left hnr_real (by positivity))))
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) M₁]
  have hred_pow : (2 : ℝ) ^ ((D * (n + 1) : ℕ) : ℝ) ≤
      (⌈(2 : ℝ) ^ (M₁ : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ ((δ / 2) * (m a : ℝ)) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hred_exp
    rw [Real.rpow_add (by norm_num)] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  -- Bound the decider time `tg (f a)` by `cg * 2^M₂ * 2^((δ/2)*m a) + cg`.
  have hlog_pow : ((Nat.log 2 (encB (f a)).length : ℝ) ^ r) ≤
      (2 * (K' : ℝ)) ^ r * ((m a : ℝ) + 1) := by
    have h1 : (Nat.log 2 (encB (f a)).length : ℝ) ≤ (K' : ℝ) * ((n : ℝ) + 1) := by
      have : Nat.log 2 (encB (f a)).length ≤ K' * (n + 1) :=
        (hlog a).trans (Nat.mul_le_mul_right _ (le_max_right 1 K))
      exact_mod_cast this
    have h2 : ((Nat.log 2 (encB (f a)).length : ℝ) ^ r) ≤ ((K' : ℝ) * ((n : ℝ) + 1)) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 r
    have hn1_pow : ((n : ℝ) + 1) ^ r ≤ (2 : ℝ) ^ r * ((m a : ℝ) + 1) := by
      by_cases hn0 : n = 0
      · simp only [hn0, Nat.cast_zero, zero_add, one_pow]
        have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
        have hm1 : (1 : ℝ) ≤ (m a : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (m a)]
        nlinarith
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
        have hsum : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
        have hnr_real : (n : ℝ) ^ r ≤ (m a : ℝ) := by exact_mod_cast hnr
        calc ((n : ℝ) + 1) ^ r
            ≤ (2 * (n : ℝ)) ^ r := pow_le_pow_left₀ (by positivity) hsum r
          _ = (2 : ℝ) ^ r * (n : ℝ) ^ r := mul_pow 2 (n : ℝ) r
          _ ≤ (2 : ℝ) ^ r * ((m a : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc ((Nat.log 2 (encB (f a)).length : ℝ) ^ r)
        ≤ ((K' : ℝ) * ((n : ℝ) + 1)) ^ r := h2
      _ = (K' : ℝ) ^ r * ((n : ℝ) + 1) ^ r := mul_pow _ _ r
      _ ≤ (K' : ℝ) ^ r * ((2 : ℝ) ^ r * ((m a : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hn1_pow (by positivity)
      _ = (2 * (K' : ℝ)) ^ r * ((m a : ℝ) + 1) := by rw [mul_pow]; ring
  have hdec_exp : δB * ((Nat.log 2 (encB (f a)).length : ℝ) ^ r) ≤
      (M₂ : ℝ) + (δ / 2) * (m a : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hlog_pow hδB.le
    have hcoeff : δB * (2 * (K' : ℝ)) ^ r = δ / 2 := by
      dsimp only [δB]
      have hne : (2 * (K' : ℝ)) ^ r ≠ 0 := by positivity
      field_simp [hne]
    have hM2 : δB * (2 * (K' : ℝ)) ^ r ≤ (M₂ : ℝ) :=
      (Nat.le_ceil _).trans (by dsimp only [M₂]; push_cast; linarith)
    linarith [show δB * ((2 * (K' : ℝ)) ^ r * ((m a : ℝ) + 1)) =
      (δ / 2) * (m a : ℝ) + δB * (2 * (K' : ℝ)) ^ r by rw [← mul_assoc, hcoeff]; ring]
  have hdec_pow : (2 : ℝ) ^ (δB * ((Nat.log 2 (encB (f a)).length : ℝ) ^ r)) ≤
      (⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ ((δ / 2) * (m a : ℝ)) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hdec_exp
    rw [Real.rpow_add (by norm_num)] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  -- Combine both bounds into `Coeff * (2 ^ (δ * m a) * (L + 1) ^ D)`.
  have hhalf_le : (2 : ℝ) ^ ((δ / 2) * (m a : ℝ)) ≤ (2 : ℝ) ^ (δ * (m a : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) (m a)])
  have hL_ge : (1 : ℝ) ≤ (((encA a).length : ℝ) + 1) ^ D :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encA a).length])
  have h2_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (m a : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (m a : ℝ)) * (((encA a).length : ℝ) + 1) ^ D :=
    one_le_mul_of_one_le_of_one_le h2_ge hL_ge
  have hterm1 : ((C * 2 ^ (D * (n + 1)) * ((encA a).length + 1) ^ D : ℕ) : ℝ) ≤
      (C * ⌈(2 : ℝ) ^ (M₁ : ℝ)⌉₊ : ℕ) *
        ((2 : ℝ) ^ (δ * (m a : ℝ)) * (((encA a).length : ℝ) + 1) ^ D) := by
    push_cast
    rw [← Real.rpow_natCast (2 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_left
      (hred_pow.trans (mul_le_mul_of_nonneg_left hhalf_le (Nat.cast_nonneg _))) (Nat.cast_nonneg C)
    have hmul2 := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤
      (((encA a).length : ℝ) + 1) ^ D)
    linarith
  have hterm2 : (tg (f a) : ℝ) ≤
      ((cg * ⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ + cg : ℕ) : ℝ) *
        ((2 : ℝ) ^ (δ * (m a : ℝ)) * (((encA a).length : ℝ) + 1) ^ D) := by
    have hmul := mul_le_mul_of_nonneg_left
      (hdec_pow.trans (mul_le_mul_of_nonneg_left hhalf_le (Nat.cast_nonneg _))) (Nat.cast_nonneg cg)
    have h1 : (tg (f a) : ℝ) ≤
        (cg : ℝ) * ((⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (m a : ℝ))) + (cg : ℝ) := by
      linarith [htg (f a), hmul]
    have h2 : (cg : ℝ) * ((⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (m a : ℝ))) ≤
        (cg : ℝ) * (⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ : ℝ) *
          ((2 : ℝ) ^ (δ * (m a : ℝ)) * (((encA a).length : ℝ) + 1) ^ D) := by
      have h := mul_le_mul_of_nonneg_left hL_ge (by positivity : 0 ≤ (2 : ℝ) ^ (δ * (m a : ℝ)))
      have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤
        (cg : ℝ) * (⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ : ℝ))
      linarith
    have h3 : (cg : ℝ) ≤ (cg : ℝ) *
        ((2 : ℝ) ^ (δ * (m a : ℝ)) * (((encA a).length : ℝ) + 1) ^ D) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h1_le (Nat.cast_nonneg cg)
    push_cast; linarith
  change (((C * 2 ^ (D * (n + 1)) * ((encA a).length + 1) ^ D + tg (f a) : ℕ) : ℝ)) ≤ _
  rw [Nat.cast_add]
  have hsum := add_le_add hterm1 hterm2
  have hCoeff : ((C * ⌈(2 : ℝ) ^ (M₁ : ℝ)⌉₊ : ℕ) : ℝ) +
      ((cg * ⌈(2 : ℝ) ^ (M₂ : ℝ)⌉₊ + cg : ℕ) : ℝ) ≤ (Coeff : ℝ) := by
    dsimp only [Coeff]; push_cast; linarith
  exact hsum.trans (by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hCoeff (by positivity))

end SubexpTransfer

/-! ### ETH consequences for `KColoring` and `QuasiP` -/

section ETHConsequences

/-- **Linear size of `SAT.toKColoring`**: on a formula `φ` whose clauses have width at most `k`,
the gadget graph `SAT.toKColoring m φ` has `O(φ.length)` vertices and edges (counted as listed). -/
theorem SAT.length_toKColoring_le {k : ℕ} (m : ℕ) {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (SAT.toKColoring m φ).vertices.length + (SAT.toKColoring m φ).edges.length ≤
      3 * ((2 * m + 1) * ((8 * k + 4) * φ.length + 3) + m * m) := by
  have hthree := SAT.length_toThreeColoring_le hφ
  have hV_three : (SAT.toThreeColoring φ).vertices.length = 2 * (SAT.coloringEdges φ).length := by
    simp only [SAT.toThreeColoring, List.length_flatMap, List.length_cons, List.length_nil,
      List.map_const', List.sum_replicate, smul_eq_mul]
    ring
  have hE_le : (SAT.coloringEdges φ).length ≤ (8 * k + 4) * φ.length + 3 := by
    rw [hV_three] at hthree
    simp only [SAT.toThreeColoring] at hthree
    nlinarith
  have hke : (SAT.kColoringEdges m φ).length ≤
      (2 * m + 1) * (SAT.coloringEdges φ).length + m * m := by
    have hflat : ((List.range m).flatMap fun r ↦
        ((SAT.coloringEdges φ).flatMap fun e ↦ [e.1, e.2]).map
          (fun v ↦ (SAT.universalVertex r, v)) ++
        (List.range r).map fun r' ↦ (SAT.universalVertex r, SAT.universalVertex r')).length ≤
        m * (2 * (SAT.coloringEdges φ).length + m) := by
      rw [List.length_flatMap]
      have hsum := List.sum_le_length_nsmul
        ((List.range m).map fun r ↦
          (((SAT.coloringEdges φ).flatMap fun e ↦ [e.1, e.2]).map
            (fun v ↦ (SAT.universalVertex r, v)) ++
          (List.range r).map fun r' ↦ (SAT.universalVertex r, SAT.universalVertex r')).length)
        (2 * (SAT.coloringEdges φ).length + m) fun x hx ↦ by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
          have hrm : r < m := List.mem_range.mp hr
          simp only [List.length_append, List.length_map, List.length_range, List.length_flatMap,
            List.length_cons, List.length_nil, List.map_const', List.sum_replicate, smul_eq_mul]
          omega
      simpa only [List.length_map, List.length_range, smul_eq_mul] using hsum
    simp only [SAT.kColoringEdges, List.length_append]
    nlinarith
  have hV : (SAT.toKColoring m φ).vertices.length = 2 * (SAT.kColoringEdges m φ).length := by
    simp only [SAT.toKColoring, List.length_flatMap, List.length_cons, List.length_nil,
      List.map_const', List.sum_replicate, smul_eq_mul]
    ring
  simp only [SAT.toKColoring] at hV ⊢
  rw [hV]
  have h1 : (2 * m + 1) * (SAT.coloringEdges φ).length ≤
      (2 * m + 1) * ((8 * k + 4) * φ.length + 3) :=
    Nat.mul_le_mul_left _ hE_le
  nlinarith

/-- **ETH lower bound for `KColoring`**: under `ETH`, for every `k ≥ 3`, `k`-colorability cannot be
decided in time `2 ^ o(|V| + |E|)` (counted as listed). -/
theorem ETH.not_decidableInSubexpTime_KColoring (hETH : ETH) {k : ℕ} (hk : 3 ≤ k) :
    ¬DecidableInSubexpTime (KColoring k) encGraph
      (fun G ↦ G.vertices.length + G.edges.length) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  refine ETH.not_decidableInSubexpTime_of_reduction hETH
    (SAT.computableInPolyTime_toKColoring m)
    (fun φ _ ↦ SAT.toKColoring_mem_iff m φ)
    (k := 3 * ((2 * m + 1) * 28 + 3 * (2 * m + 1) + m * m)) fun φ hφ ↦ ?_
  have h := SAT.length_toKColoring_le m hφ
  nlinarith

private lemma computableInPolyTime_compact_binary :
    ComputableInPolyTime (CNF.compact (V := ℕ)) encCNF encCNF := by
  have h1 : ComputableInPolyTime (CNF.compact (V := ℕ)) encCNF (encCNFOver encUnary) :=
    CNF.isPolyTime_compact encNat
  have h2 : ComputableInPolyTime (CNF.relabel (id : ℕ → ℕ)) (encCNFOver encUnary) encCNF :=
    CNF.computableInPolyTime_relabel ComputableInPolyTime.unary_to_binary
  have heq : (CNF.relabel (id : ℕ → ℕ)) ∘ (CNF.compact (V := ℕ)) = CNF.compact :=
    funext fun φ ↦ CNF.relabel_id φ.compact
  rw [← heq]
  exact h2.comp h1

private lemma length_encCNF_compact_le {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (encCNF φ.compact).length ≤ 60 * (φ.length + 1) * (Nat.log 2 (3 * φ.length + 2) + 1) := by
  have hvars_le : φ.vars.length ≤ 3 * φ.length := CNF.length_vars_le_mul_length hφ
  have hlit_len : ∀ c ∈ φ.compact, ∀ l ∈ c,
      (encPair encNat encBool l).length ≤ 2 * (Nat.log 2 (3 * φ.length + 2) + 1) + 2 := by
    intro c hc l hl
    have hv : l.1 ∈ φ.compact.vars := by
      simp only [CNF.vars]
      exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩
    have hvlt : l.1 < φ.vars.length := CNF.mem_vars_compact_lt φ hv
    have hbits : (encNat l.1).length ≤ Nat.log 2 (3 * φ.length + 2) + 1 := by
      have hle : l.1 ≤ 3 * φ.length + 2 := by omega
      have h1 : (encNat l.1).length ≤ Nat.log 2 l.1 + 1 := by
        rw [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le_log_two_add_one l.1
      exact h1.trans (Nat.add_le_add_right (Nat.log_mono_right hle) 1)
    simp only [length_encPair, encBool_apply, List.length_singleton]
    omega
  have hclause_len : ∀ c ∈ φ.compact,
      (encList (encPair encNat encBool) c).length ≤
        3 * (4 * (Nat.log 2 (3 * φ.length + 2) + 1) + 5) := by
    intro c hc
    have hcl : c.length ≤ 3 := by
      have : c.length ∈ φ.compact.map List.length := List.mem_map.mpr ⟨c, hc, rfl⟩
      rw [CNF.map_length_compact] at this
      obtain ⟨d, hd, hlen⟩ := List.mem_map.mp this
      exact hlen ▸ hφ d hd
    rw [length_encList]
    have hsum : (c.map fun l ↦ 2 * (encPair encNat encBool l).length + 1).sum ≤
        c.length * (4 * (Nat.log 2 (3 * φ.length + 2) + 1) + 5) := by
      have := List.sum_le_length_nsmul (c.map fun l ↦ 2 * (encPair encNat encBool l).length + 1)
        (4 * (Nat.log 2 (3 * φ.length + 2) + 1) + 5) fun x hx ↦ by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
          have := hlit_len c hc l hl
          omega
      simpa only [List.length_map, smul_eq_mul] using this
    exact hsum.trans (Nat.mul_le_mul_right _ hcl)
  rw [encCNF, length_encList]
  have hsum : (φ.compact.map fun c ↦ 2 * (encList (encPair encNat encBool) c).length + 1).sum ≤
      φ.compact.length * (2 * (3 * (4 * (Nat.log 2 (3 * φ.length + 2) + 1) + 5)) + 1) := by
    have := List.sum_le_length_nsmul
      (φ.compact.map fun c ↦ 2 * (encList (encPair encNat encBool) c).length + 1)
      (2 * (3 * (4 * (Nat.log 2 (3 * φ.length + 2) + 1) + 5)) + 1) fun x hx ↦ by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        have := hclause_len c hc
        omega
    simpa only [List.length_map, smul_eq_mul] using this
  rw [CNF.length_compact] at hsum
  have hpos : 1 ≤ Nat.log 2 (3 * φ.length + 2) + 1 := Nat.succ_pos _
  nlinarith

private lemma log_pow_eventually_le_linear (c : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m : ℕ,
      ((Nat.log 2 (60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1)) : ℝ) ^ c) ≤
        (M : ℝ) + δ * (m : ℝ) := by
  set B : ℕ := 2 * c + 10
  set K : ℝ := ((B ^ c * 2 ^ c : ℕ) : ℝ)
  set T₀ : ℕ := ⌈(K + δ) / δ⌉₊ + 2
  refine ⟨B ^ c * (T₀ + 1) ^ c, fun m ↦ ?_⟩
  set t : ℕ := natNthRoot (c + 1) (m + 1)
  have hlog_le : Nat.log 2 (60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1)) ≤ B * (t + 1) := by
    have hlog3 : Nat.log 2 (3 * m + 2) + 1 ≤ 3 * (m + 1) := by
      have := Nat.log_le_self 2 (3 * m + 2)
      omega
    have hprod : 60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1) ≤ 180 * (m + 1) ^ 2 := by
      calc 60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1)
          ≤ 60 * (m + 1) * (3 * (m + 1)) := Nat.mul_le_mul_left _ hlog3
        _ = 180 * (m + 1) ^ 2 := by ring
    have hm1_lt : m + 1 < (t + 1) ^ (c + 1) := lt_succ_natNthRoot_pow (Nat.succ_pos c) (m + 1)
    have ht_pow : t + 1 < 2 ^ (t + 1) := Nat.lt_two_pow_self
    have h180 : 180 < 2 ^ 8 := by norm_num
    have hlt_pow : 60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1) < 2 ^ (B * (t + 1)) := by
      calc 60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1)
          ≤ 180 * (m + 1) ^ 2 := hprod
        _ < 2 ^ 8 * ((t + 1) ^ (c + 1)) ^ 2 :=
          Nat.mul_lt_mul_of_lt_of_le h180 (Nat.pow_le_pow_left hm1_lt.le 2) (by positivity)
        _ ≤ 2 ^ 8 * ((2 ^ (t + 1)) ^ (c + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_le_pow_left ht_pow.le _) 2)
        _ = 2 ^ (8 + 2 * (c + 1) * (t + 1)) := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]; ring_nf
        _ ≤ 2 ^ (B * (t + 1)) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          dsimp only [B]; nlinarith
    exact (Nat.log_lt_of_lt_pow (by positivity) hlt_pow).le
  have hpow_le : ((Nat.log 2 (60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1)) : ℝ) ^ c) ≤
      ((B ^ c * (t + 1) ^ c : ℕ) : ℝ) := by
    have : Nat.log 2 (60 * (m + 1) * (Nat.log 2 (3 * m + 2) + 1)) ^ c ≤ B ^ c * (t + 1) ^ c := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left hlog_le c
    exact_mod_cast this
  refine hpow_le.trans ?_
  by_cases ht : t ≤ T₀
  · have : B ^ c * (t + 1) ^ c ≤ B ^ c * (T₀ + 1) ^ c :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) c)
    have hcast : ((B ^ c * (t + 1) ^ c : ℕ) : ℝ) ≤ ((B ^ c * (T₀ + 1) ^ c : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith [show 0 ≤ δ * (m : ℝ) by positivity]
  · push Not at ht
    have ht_pow_le : (t : ℝ) ^ (c + 1) ≤ (m : ℝ) + 1 := by
      exact_mod_cast natNthRoot_pow_le (Nat.succ_pos c) (m + 1)
    have ht_ge : (K + δ) / δ ≤ (t : ℝ) := by
      have h1 : (K + δ) / δ ≤ (T₀ : ℝ) := by
        have := Nat.le_ceil ((K + δ) / δ)
        dsimp only [T₀]; push_cast; linarith
      exact h1.trans (by exact_mod_cast ht.le)
    have hmul : K + δ ≤ δ * (t : ℝ) := by
      rw [mul_comm]
      exact (div_le_iff₀ hδ).mp ht_ge
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
    have ht1_pow : (1 : ℝ) ≤ (t : ℝ) ^ c := one_le_pow₀ ht1
    have hstep1 : ((B ^ c * (t + 1) ^ c : ℕ) : ℝ) ≤ K * (t : ℝ) ^ c := by
      have h2t : (t : ℝ) + 1 ≤ 2 * (t : ℝ) := by linarith
      have hp : ((t : ℝ) + 1) ^ c ≤ (2 : ℝ) ^ c * (t : ℝ) ^ c := by
        calc ((t : ℝ) + 1) ^ c ≤ (2 * (t : ℝ)) ^ c := pow_le_pow_left₀ (by positivity) h2t c
          _ = (2 : ℝ) ^ c * (t : ℝ) ^ c := mul_pow 2 (t : ℝ) c
      have hB0 : (0 : ℝ) ≤ (B : ℝ) ^ c := by positivity
      calc ((B ^ c * (t + 1) ^ c : ℕ) : ℝ)
          = (B : ℝ) ^ c * ((t : ℝ) + 1) ^ c := by push_cast; rfl
        _ ≤ (B : ℝ) ^ c * ((2 : ℝ) ^ c * (t : ℝ) ^ c) := mul_le_mul_of_nonneg_left hp hB0
        _ = K * (t : ℝ) ^ c := by dsimp only [K]; push_cast; ring
    have hstep2 : K * (t : ℝ) ^ c + δ ≤ δ * ((t : ℝ) ^ (c + 1)) := by
      rw [pow_succ']
      have h1 : (K + δ) * (t : ℝ) ^ c ≤ δ * (t : ℝ) * (t : ℝ) ^ c :=
        mul_le_mul_of_nonneg_right hmul (by positivity)
      have h2 : δ ≤ δ * (t : ℝ) ^ c := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1_pow hδ.le
      linarith
    have hstep3 : δ * (t : ℝ) ^ (c + 1) ≤ δ * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left ht_pow_le hδ.le
    have hnonneg : (0 : ℝ) ≤ ((B ^ c * (T₀ + 1) ^ c : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- **Under `ETH`, `ThreeSAT` is not in `QuasiP`.** -/
theorem ETH.not_mem_QuasiP_ThreeSAT (hETH : ETH) : ThreeSAT ∉ QuasiP encCNF := by
  intro hQ
  obtain ⟨c, hc⟩ := mem_QuasiP_iff.mp hQ
  have htime := mem_DTIME_iff_decidableInTimeO.mp hc
  -- Reduce `ThreeSAT` to itself via `CNF.compact` (so encoded size is `O(m log m)`).
  have hcomp : ComputableInPolyTime (fun φ : CNF ℕ ↦
      if φ.all (fun cl ↦ decide (cl.length ≤ 3)) then φ.compact else [[]]) encCNF encCNF :=
    (computableInPolyTime_all_length_le 3).ite computableInPolyTime_compact_binary
      (ComputableInPolyTime.const [[]])
  have hsub : DecidableInSubexpTime ThreeSAT encCNF List.length := by
    intro δ hδ
    obtain ⟨g, tg, cg, hg, hg3, htg⟩ := htime.exists_computableInO
    obtain ⟨d, _, hcomp'⟩ := hcomp.exists_degree
    obtain ⟨M, hM⟩ := log_pow_eventually_le_linear c hδ
    refine DecidableInExpTime.of_computableInO (hg.comp hcomp'.inO) (fun φ ↦ ?_)
      (cg * ⌈(2 : ℝ) ^ (M : ℝ)⌉₊ + cg + 2) d fun φ ↦ ?_
    · dsimp only [Function.comp_apply]
      split_ifs with hw
      · have hw' : ∀ cl ∈ φ, cl.length ≤ 3 := by simpa using hw
        have hlen' : ∀ cl ∈ φ.compact, cl.length ≤ 3 := fun cl hcl ↦ by
          have : cl.length ∈ φ.compact.map List.length := List.mem_map.mpr ⟨cl, hcl, rfl⟩
          rw [CNF.map_length_compact] at this
          obtain ⟨d, hd, hdl⟩ := List.mem_map.mp this
          exact hdl ▸ hw' d hd
        rw [← hg3 φ.compact]
        exact ⟨fun h ↦ ⟨hlen', (CNF.satisfiable_compact φ).mpr h.2⟩,
          fun h ↦ ⟨hw', (CNF.satisfiable_compact φ).mp h.2⟩⟩
      · have hnot : ¬∀ cl ∈ φ, cl.length ≤ 3 := by simpa using hw
        rw [← hg3 [[]]]
        exact ⟨fun h ↦ (hnot h.1).elim, fun h ↦ by
          obtain ⟨σ, hσ⟩ := h.2; simp at hσ⟩
    · set f := fun φ : CNF ℕ ↦ if φ.all (fun cl ↦ decide (cl.length ≤ 3)) then φ.compact else [[]]
      have hlen_f : (encCNF (f φ)).length ≤
          60 * (φ.length + 1) * (Nat.log 2 (3 * φ.length + 2) + 1) := by
        dsimp only [f]
        split_ifs with hw
        · exact length_encCNF_compact_le (by simpa using hw)
        · have h1 : (encCNF ([[]] : CNF ℕ)).length ≤ 10 := by decide
          have h2 : 1 ≤ φ.length + 1 := Nat.succ_pos _
          have h3 : 1 ≤ Nat.log 2 (3 * φ.length + 2) + 1 := Nat.succ_pos _
          nlinarith
      have hlog_f : Nat.log 2 (encCNF (f φ)).length ≤
          Nat.log 2 (60 * (φ.length + 1) * (Nat.log 2 (3 * φ.length + 2) + 1)) :=
        Nat.log_mono_right hlen_f
      have hexp : (2 : ℝ) ^ ((Nat.log 2 (encCNF (f φ)).length ^ c : ℕ) : ℝ) ≤
          (⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (φ.length : ℝ)) := by
        have h1a : ((Nat.log 2 (encCNF (f φ)).length ^ c : ℕ) : ℝ) ≤
            ((Nat.log 2 (60 * (φ.length + 1) * (Nat.log 2 (3 * φ.length + 2) + 1)) : ℝ) ^ c) := by
          exact_mod_cast Nat.pow_le_pow_left hlog_f c
        have h1 : ((Nat.log 2 (encCNF (f φ)).length ^ c : ℕ) : ℝ) ≤
            (M : ℝ) + δ * (φ.length : ℝ) :=
          h1a.trans (hM φ.length)
        have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1
        rw [Real.rpow_add (by norm_num)] at h2
        exact h2.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
      have h2_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hL_ge : (1 : ℝ) ≤ ((encCNF φ).length + 1 : ℝ) ^ d :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (encCNF φ).length])
      have htg' := htg (f φ)
      rw [Real.rpow_natCast] at hexp
      change ((((encCNF φ).length + 1) ^ d + tg (f φ) : ℕ) : ℝ) ≤ _
      push_cast at htg' ⊢
      have hpow_nat : (2 : ℝ) ^ (Nat.log 2 (encCNF (f φ)).length ^ c) ≤
          (⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (φ.length : ℝ)) := by
        simpa only [Real.rpow_natCast] using hexp
      have htg'' : (tg (f φ) : ℝ) ≤
          (cg : ℝ) * ((⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (φ.length : ℝ))) + (cg : ℝ) := by
        refine htg'.trans ?_
        have := mul_le_mul_of_nonneg_left hpow_nat (Nat.cast_nonneg cg)
        linarith
      have hterm1 : (((encCNF φ).length : ℝ) + 1) ^ d ≤
          (2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ d :=
        le_mul_of_one_le_left (by positivity) h2_ge
      have hterm2 : (cg : ℝ) * ((⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) * (2 : ℝ) ^ (δ * (φ.length : ℝ))) ≤
          (cg : ℝ) * (⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ) *
            ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ d) := by
        have := mul_le_mul_of_nonneg_left hL_ge (by positivity : 0 ≤ (2 : ℝ) ^ (δ * (φ.length : ℝ)))
        have := mul_le_mul_of_nonneg_left this
          (by positivity : 0 ≤ (cg : ℝ) * (⌈(2 : ℝ) ^ (M : ℝ)⌉₊ : ℝ))
        linarith
      have hterm3 : (cg : ℝ) ≤
          (cg : ℝ) * ((2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ d) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (one_le_mul_of_one_le_of_one_le h2_ge hL_ge) (Nat.cast_nonneg cg)
      have hpos : (0 : ℝ) ≤
          (2 : ℝ) ^ (δ * (φ.length : ℝ)) * (((encCNF φ).length : ℝ) + 1) ^ d := by positivity
      linarith
  exact ETH_iff_not_decidableInSubexpTime_length.mp hETH hsub

/-- **Under `ETH`, no `NP`-complete problem lies in `QuasiP`.** -/
theorem ETH.not_NPComplete_of_mem_QuasiP {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hETH : ETH) (hQ : A ∈ QuasiP enc) : ¬NPComplete enc A := fun hC ↦
  ETH.not_mem_QuasiP_ThreeSAT hETH
    (PolyTimeReducible.mem_QuasiP (hC.2 encCNF ThreeSAT ThreeSAT.mem_NP) hQ)

/-- **Under `ETH`, no `coNP`-complete problem lies in `QuasiP`.** -/
theorem ETH.not_coNPComplete_of_mem_QuasiP {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hETH : ETH) (hQ : A ∈ QuasiP enc) : ¬coNPComplete enc A := fun hC ↦
  ETH.not_NPComplete_of_mem_QuasiP hETH (compl_mem_QuasiP hQ) hC.compl

end ETHConsequences

end Cslib.Complexity
