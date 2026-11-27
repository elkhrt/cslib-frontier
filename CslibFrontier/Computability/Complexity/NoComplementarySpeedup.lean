module

public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.Constructible
import CslibFrontier.Computability.Complexity.Classes.Constructible.Log
import CslibFrontier.Computability.Complexity.Classes.Hierarchy
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.ShortDesc
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TimePolylog
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.WindowedComplexity
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# No Complementary Speedup

This module establishes the folklore no-complementary-speedup theorem: for every `b ≥ 1`,
`coNTIME[(n + 1)^{b + 1}] ⊈ NTIME[(n + 1)^b]_{/o(n)}`.

## Main definitions

* `CslibFrontier.Computability.Complexity.coNTIME`: complement of `NTIME`.
* `CslibFrontier.Computability.Complexity.NTIMEWithAdvice`,
  `CslibFrontier.Computability.Complexity.NTIMEWithSublinearAdvice`: nondeterministic time with
  advice
  and sublinear (`o(n)`) advice.
* `CslibFrontier.Computability.Complexity.hardLanguage`: diagonal hard language in
  `coNTIME[(n + 1)^{b + 1}]`.

## Main results

* `CslibFrontier.Computability.Complexity.hardLanguage_mem_coNTIME`: membership of `hardLanguage b`
  in
  `coNTIME[(n + 1)^{b + 1}]`.
* `CslibFrontier.Computability.Complexity.no_complementary_speedup`: for every `b ≥ 1`,
  `¬ coNTIME encBits (fun n => (n + 1) ^ (b + 1)) ⊆ NTIMEWithSublinearAdvice (fun n => (n + 1)^b)`.
-/

public section

namespace CslibFrontier.Computability.Complexity

open Cslib Cslib.Complexity
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

/-! ### Co-Nondeterministic Time and Nondeterministic Time with Sublinear Advice -/

/-- Co-nondeterministic time `coNTIME[t]` relative to encoding `enc`: languages whose complement
lies in `NTIME enc t`. -/
def coNTIME {α : Type*} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {L | Lᶜ ∈ NTIME enc t}

@[simp] theorem mem_coNTIME_iff {α : Type*} {enc : α ↪ List Bool} {t : ℕ → ℕ} {L : Set α} :
    L ∈ coNTIME enc t ↔ Lᶜ ∈ NTIME enc t := Iff.rfl

/-- Nondeterministic time `t` with exact advice length `a n` at input length `n`. -/
@[expose] def NTIMEWithAdvice (t a : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ advice : ℕ → List Bool, (∀ n, (advice n).length = a n) ∧
    ∃ A ∈ NTIME (encPair encBits encBits) t, ∀ x, x ∈ L ↔ (advice x.length, x) ∈ A}

/-- Nondeterministic time `t` with sublinear (`o(n)`) advice: `∀ c, ∃ N, ∀ n ≥ N, c * a n ≤ n`. -/
@[expose] def NTIMEWithSublinearAdvice (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ a : ℕ → ℕ, (∀ c : ℕ, ∃ N, ∀ n ≥ N, c * a n ≤ n) ∧ L ∈ NTIMEWithAdvice t a}

/-! ### Part 1: No Complementary Speedup (`coNTIME[n^{b+1}] ⊈ NTIME[n^b]_{/o(n)}`) -/

/-- Certificate-length clock `L_b(n) = (n + 1)^b * (size((n + 1)^b) + 1)`. -/
private def diagClockL (b n : ℕ) : ℕ :=
  (n + 1) ^ b * (Nat.size ((n + 1) ^ b) + 1)

/-- Simulation clock `J_b(n) = L_b(n) * (size(L_b(n)) + 1)`. -/
private def diagClockJ (b n : ℕ) : ℕ :=
  diagClockL b n * (Nat.size (diagClockL b n) + 1)

private lemma timeConstructible_succ_pow_pos (b : ℕ) (hb : 1 ≤ b) :
    TimeConstructible (fun n => (n + 1) ^ b) := by
  rcases eq_or_lt_of_le hb with rfl | h2
  · simpa only [pow_one] using timeConstructible_succ
  · exact timeConstructible_succ_pow (by omega)

private lemma timeConstructible_diagClockL (b : ℕ) (hb : 1 ≤ b) :
    TimeConstructible (diagClockL b) :=
  (timeConstructible_succ_pow_pos b hb).mul_size_succ

private lemma timeConstructible_diagClockJ (b : ℕ) (hb : 1 ≤ b) :
    TimeConstructible (diagClockJ b) :=
  (timeConstructible_diagClockL b hb).mul_size_succ

private lemma diagClockL_ge_base (b n : ℕ) : (n + 1) ^ b ≤ diagClockL b n :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

private lemma diagClockL_le_diagClockJ (b n : ℕ) : diagClockL b n ≤ diagClockJ b n :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

private lemma n_le_diagClockL (b n : ℕ) (hb : 1 ≤ b) : n + 1 ≤ diagClockL b n :=
  (Nat.le_self_pow (by omega) (n + 1)).trans (diagClockL_ge_base b n)

/-- Verifier for the diagonal complement language `compH b`: given `(x, w)`, checks that `x` has a
short framed machine description and that the universal machine accepts the described verifier run
on `((unframe (dropFrame x), x), w)` within `diagClockJ b x.length` steps. -/
private def diagVerifier (b : ℕ) (p : List Bool × List Bool) : Bool :=
  if Diagonal.shortDesc p.1 then
    !(Diagonal.verdict (universal
      (decodeDesc (unframe p.1),
       (encPair (encPair encBits encBits) encBits
         ((unframe (dropFrame p.1), p.1), p.2)).map eBit,
       diagClockJ b p.1.length)))
  else false

/-- Complement of the hard diagonal language for `no_complementary_speedup`. -/
private def compH (b : ℕ) : Set (List Bool) :=
  {x | ∃ w : List Bool, w.length = diagClockL b x.length ∧ diagVerifier b (x, w) = true}

/-- Hard language `H_b ∈ coNTIME[(n + 1)^{b + 1}] \ NTIME[(n + 1)^b]_{/o(n)}`. -/
def hardLanguage (b : ℕ) : Set (List Bool) := (compH b)ᶜ

private lemma polylog_eventually_le_succ (b k : ℕ) (hb : 1 ≤ b) :
    ∀ᶠ n in atTop,
      n + (Nat.log 2 (n + 1) + 1) ^ k *
        ((diagClockJ b n + 1) * (Nat.log 2 (diagClockJ b n + 1) + 1)) ≤ (n + 1) ^ (b + 1) := by
  have hlog_pow : ∀ᶠ n in atTop,
      4 * (Nat.log 2 (n + 1) + 1) ^ (k + 6) ≤ n + 1 := by
    have hpoly := PolynomiallyBounded.eventually_lt_two_pow
      (f := fun m => 4 * (m + 2) ^ (k + 6)) (by fun_prop)
    rw [eventually_atTop] at hpoly ⊢
    obtain ⟨M, hM⟩ := hpoly
    refine ⟨2 ^ M + 1, fun n hn => ?_⟩
    have hMle : M ≤ Nat.log 2 (n + 1) :=
      Nat.le_log_of_pow_le (by norm_num) (by omega)
    have h1 := (hM (Nat.log 2 (n + 1)) hMle).le
    have h2 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    have h3 : (Nat.log 2 (n + 1) + 1) ^ (k + 6) ≤ (Nat.log 2 (n + 1) + 2) ^ (k + 6) :=
      Nat.pow_le_pow_left (by omega) _
    nlinarith
  rw [eventually_atTop] at hlog_pow ⊢
  obtain ⟨N₀, hN₀⟩ := hlog_pow
  refine ⟨max N₀ (2 ^ (b + 5) + 16), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnbig : 2 ^ (b + 5) + 16 ≤ n := (le_max_right _ _).trans hn
  set ℓ := Nat.log 2 (n + 1) + 1 with hℓ
  have hℓ1 : 1 ≤ ℓ := Nat.le_add_left _ _
  have hℓbig : b + 6 ≤ ℓ := by
    have : b + 5 ≤ Nat.log 2 (n + 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega
  have hpow_le : (n + 1) ^ b ≤ 2 ^ (b * ℓ) := by
    have h1 : n + 1 < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    calc (n + 1) ^ b ≤ (2 ^ ℓ) ^ b := Nat.pow_le_pow_left h1.le b
      _ = 2 ^ (b * ℓ) := by rw [← pow_mul, Nat.mul_comm]
  have hsize_f0 : Nat.size ((n + 1) ^ b) + 1 ≤ (b + 1) * ℓ + 1 := by
    have h1 : Nat.size ((n + 1) ^ b) ≤ b * ℓ := Nat.size_le.mpr (by
      have hlt : n + 1 < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
      have hpow_lt : (n + 1) ^ b < (2 ^ ℓ) ^ b :=
        Nat.pow_lt_pow_left hlt (by omega)
      rwa [← pow_mul, Nat.mul_comm] at hpow_lt)
    have : b * ℓ ≤ (b + 1) * ℓ := Nat.mul_le_mul_right ℓ (Nat.le_succ b)
    omega
  have hL_le : diagClockL b n ≤ (n + 1) ^ b * ℓ ^ 2 := by
    unfold diagClockL
    refine Nat.mul_le_mul_left _ ?_
    have : (b + 1) * ℓ + 1 ≤ ℓ ^ 2 := by rw [sq]; nlinarith
    omega
  have hL_pow : diagClockL b n < 2 ^ ((b + 2) * ℓ) := by
    have h2 : 2 ^ (b * ℓ) * (2 ^ ℓ) ^ 2 = 2 ^ ((b + 2) * ℓ) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    have hlt2 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    have hp2 : ℓ ^ 2 < (2 ^ ℓ) ^ 2 := Nat.pow_lt_pow_left hlt2 (by norm_num)
    have hpow_lt : (n + 1) ^ b * ℓ ^ 2 < 2 ^ (b * ℓ) * (2 ^ ℓ) ^ 2 :=
      calc (n + 1) ^ b * ℓ ^ 2
          < (n + 1) ^ b * (2 ^ ℓ) ^ 2 := Nat.mul_lt_mul_of_pos_left hp2 (by positivity)
        _ ≤ 2 ^ (b * ℓ) * (2 ^ ℓ) ^ 2 := Nat.mul_le_mul_right _ hpow_le
    exact (hL_le.trans_lt hpow_lt).trans_eq h2
  have hsize_L : Nat.size (diagClockL b n) + 1 ≤ ℓ ^ 2 := by
    have h1 : Nat.size (diagClockL b n) ≤ (b + 2) * ℓ := Nat.size_le.mpr hL_pow
    have : (b + 2) * ℓ + 1 ≤ ℓ ^ 2 := by rw [sq]; nlinarith
    omega
  have hJ_le : diagClockJ b n ≤ (n + 1) ^ b * ℓ ^ 4 := by
    unfold diagClockJ
    calc diagClockL b n * (Nat.size (diagClockL b n) + 1)
        ≤ ((n + 1) ^ b * ℓ ^ 2) * ℓ ^ 2 := Nat.mul_le_mul hL_le hsize_L
      _ = (n + 1) ^ b * ℓ ^ 4 := by ring
  have hJ1_le : diagClockJ b n + 1 ≤ 2 * ((n + 1) ^ b * ℓ ^ 4) := by
    have hpos : 1 ≤ (n + 1) ^ b * ℓ ^ 4 :=
      Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) (Nat.pow_pos hℓ1)
    omega
  have hlogJ_le : Nat.log 2 (diagClockJ b n + 1) + 1 ≤ ℓ ^ 2 := by
    have hlt : diagClockJ b n + 1 < 2 ^ ((b + 5) * ℓ) := by
      have h1 : (n + 1) ^ b * ℓ ^ 4 ≤ 2 ^ (b * ℓ) * (2 ^ ℓ) ^ 4 :=
        Nat.mul_le_mul hpow_le (Nat.pow_le_pow_left Nat.lt_two_pow_self.le 4)
      have h2 : 2 * (2 ^ (b * ℓ) * (2 ^ ℓ) ^ 4) < 2 ^ ((b + 5) * ℓ) := by
        have h2a : 2 ^ 1 * (2 ^ (b * ℓ) * 2 ^ (4 * ℓ)) = 2 ^ (1 + b * ℓ + 4 * ℓ) := by
          rw [← pow_add, ← pow_add, Nat.add_assoc]
        have h2b : 1 + b * ℓ + 4 * ℓ < (b + 5) * ℓ := by nlinarith
        calc 2 * (2 ^ (b * ℓ) * (2 ^ ℓ) ^ 4)
            = 2 ^ 1 * (2 ^ (b * ℓ) * 2 ^ (4 * ℓ)) := by rw [← pow_mul, Nat.mul_comm ℓ 4]; ring
          _ = 2 ^ (1 + b * ℓ + 4 * ℓ) := h2a
          _ < 2 ^ ((b + 5) * ℓ) := Nat.pow_lt_pow_right (by norm_num) h2b
      exact hJ1_le.trans_lt ((Nat.mul_le_mul_left 2 h1).trans_lt h2)
    have hlog_lt : Nat.log 2 (diagClockJ b n + 1) < (b + 5) * ℓ :=
      (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hlt
    have : (b + 5) * ℓ ≤ ℓ ^ 2 := by rw [sq]; nlinarith
    omega
  have hmain : ℓ ^ k * ((diagClockJ b n + 1) * (Nat.log 2 (diagClockJ b n + 1) + 1)) ≤
      2 * (n + 1) ^ b * ℓ ^ (k + 6) := by
    calc ℓ ^ k * ((diagClockJ b n + 1) * (Nat.log 2 (diagClockJ b n + 1) + 1))
        ≤ ℓ ^ k * ((2 * ((n + 1) ^ b * ℓ ^ 4)) * ℓ ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hJ1_le hlogJ_le)
      _ = 2 * (n + 1) ^ b * (ℓ ^ k * ℓ ^ 6) := by ring
      _ = 2 * (n + 1) ^ b * ℓ ^ (k + 6) := by rw [pow_add]
  have h4ℓ : 4 * ℓ ^ (k + 6) ≤ n + 1 := hN₀ n hn0
  have hpow_pos : 1 ≤ (n + 1) ^ b := Nat.pow_pos (Nat.succ_pos _)
  have hℓ_pos : 1 ≤ ℓ ^ (k + 6) := Nat.pow_pos hℓ1
  have hn_le : n ≤ (n + 1) ^ b * (2 * ℓ ^ (k + 6)) := by
    have hnb : n + 1 ≤ (n + 1) ^ b := Nat.le_self_pow (by omega) (n + 1)
    nlinarith
  calc n + ℓ ^ k * ((diagClockJ b n + 1) * (Nat.log 2 (diagClockJ b n + 1) + 1))
      ≤ (n + 1) ^ b * (2 * ℓ ^ (k + 6)) + 2 * (n + 1) ^ b * ℓ ^ (k + 6) :=
        Nat.add_le_add hn_le hmain
    _ = (n + 1) ^ b * (4 * ℓ ^ (k + 6)) := by ring
    _ ≤ (n + 1) ^ b * (n + 1) := Nat.mul_le_mul_left _ h4ℓ
    _ = (n + 1) ^ (b + 1) := by rw [pow_succ]

/-- Numeric resource bound for `diagVerifier`: mirrors `TimePolylog.polylogBounds_aux` for
inputs `(x, w)`. -/
private lemma diagBounds_aux (E e ce cA : ℕ) (hE : 1 ≤ E) :
    ∃ K, ∀ {n W L A D M J I : ℕ},
      2 ^ L ≤ n → A ≤ cA * (n + 1) → D ≤ ce * (L + 1) ^ e → M ≤ 1 →
      I ≤ 2 * D + 1 + (2 * (3 * (6 * n + 3 + W)) + 1 + J) →
      (2 * n + 1 + W) + A + (6 * n + 3 + W) + (n + J) +
        (I + (D + M + 2) ^ E * ((J + 1) * (Nat.log 2 (J + 1) + 1))) ≤
        K * (n + W + (Nat.log 2 (n + 1) + 1) ^ (e * E) *
          ((J + 1) * (Nat.log 2 (J + 1) + 1)) + 1) := by
  refine ⟨cA + 2 * ce + (ce + 3) ^ E + 128, fun {n W L A D M J I} hL hA hD hM hI => ?_⟩
  set ℓ := Nat.log 2 (n + 1) + 1 with hℓ
  set Y := (J + 1) * (Nat.log 2 (J + 1) + 1) with hY
  set V := ℓ ^ (e * E) * Y with hV
  have hℓ1 : 1 ≤ ℓ := Nat.le_add_left _ _
  have hLℓ : L + 1 ≤ ℓ := Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num)
    (hL.trans (Nat.le_succ n)))
  have hJY : J + 1 ≤ Y := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hYV : Y ≤ V := Nat.le_mul_of_pos_left _ (Nat.pow_pos hℓ1)
  have hpow : (L + 1) ^ e ≤ ℓ ^ e := Nat.pow_le_pow_left hLℓ e
  have hΛ : ℓ ^ e ≤ ℓ ^ (e * E) := Nat.pow_le_pow_right hℓ1 (Nat.le_mul_of_pos_right _ hE)
  have hΛV : ℓ ^ (e * E) ≤ V := Nat.le_mul_of_pos_right _ (by omega)
  have hDV : D ≤ ce * V := hD.trans (Nat.mul_le_mul_left _ ((hpow.trans hΛ).trans hΛV))
  have hB : (D + M + 2) ^ E * Y ≤ (ce + 3) ^ E * V := by
    have h₁ : D + M + 2 ≤ (ce + 3) * ℓ ^ e := by
      have := Nat.mul_le_mul_left ce hpow
      have : 1 ≤ ℓ ^ e := Nat.one_le_pow _ _ hℓ1
      have e₁ : (ce + 3) * ℓ ^ e = ce * ℓ ^ e + 3 * ℓ ^ e := by ring
      omega
    calc (D + M + 2) ^ E * Y ≤ ((ce + 3) * ℓ ^ e) ^ E * Y :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h₁ E)
      _ = (ce + 3) ^ E * V := by rw [hV, mul_pow, ← pow_mul]; ring
  have hcA : cA * (n + 1) ≤ cA * (n + W + V + 1) := Nat.mul_le_mul_left _ (by omega)
  have hce : ce * V ≤ ce * (n + W + V + 1) := Nat.mul_le_mul_left _ (by omega)
  have hC : (ce + 3) ^ E * V ≤ (ce + 3) ^ E * (n + W + V + 1) := Nat.mul_le_mul_left _ (by omega)
  have e₁ : (cA + 2 * ce + (ce + 3) ^ E + 128) * (n + W + V + 1) = cA * (n + W + V + 1) +
      2 * (ce * (n + W + V + 1)) + (ce + 3) ^ E * (n + W + V + 1) + 128 * (n + W + V + 1) := by
    ring
  rw [e₁]
  omega

/-- Membership `compH b ∈ NTIME[(n + 1)^{b + 1}]` for `b ≥ 1`. -/
private lemma compH_mem_NTIME (b : ℕ) (hb : 1 ≤ b) :
    compH b ∈ NTIME encBits (fun n => (n + 1) ^ (b + 1)) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨ce, hce⟩ := hdec.2
  obtain ⟨cA, hcA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
    (by fun_prop)
  obtain ⟨K, hK⟩ := diagBounds_aux 6 ed ce cA (by norm_num)
  have hL_tc := timeConstructible_diagClockL b hb
  have hJ_tc := timeConstructible_diagClockJ b hb
  have hℓ : ComputableInO (fun x : List Bool => diagClockL b x.length) encBits encUnary
      (fun x => diagClockL b x.length) (fun x => diagClockL b x.length) := by
    have h := ComputableInO.natToUnary.comp hL_tc.computableInO
    exact h.mono 2 (fun x => by omega) (fun x => by omega)
  have hfst : ComputableInO (Prod.fst : List Bool × List Bool → List Bool)
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length) :=
    ComputableInO.fst encBits encBits
  have hsnd : ComputableInO (Prod.snd : List Bool × List Bool → List Bool)
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length) :=
    ComputableInO.snd encBits encBits
  have hu : ComputableInO unframe encBits encBits (fun x => x.length) (fun x => x.length) :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hdesc := (hdec.inO.comp hu).comp hfst
  have hα : ComputableInO (fun p : List Bool × List Bool => unframe (dropFrame p.1))
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length) := by
    have h1 : ComputableInO (fun x : List Bool => unframe (dropFrame x)) encBits encBits
        (fun x => x.length) (fun x => x.length) :=
      (ComputableInO.unframe' (ComputableInO.dropFrame' (ComputableInO.of_eq fun _ => rfl)))
    exact (h1.comp hfst).mono 2 (fun p => by enc_len) (fun p => by enc_len)
  have hpair : ComputableInO
      (fun p : List Bool × List Bool =>
        encPair (encPair encBits encBits) encBits ((unframe (dropFrame p.1), p.1), p.2))
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length) := by
    have hraw : ComputableInO
        (fun p : List Bool × List Bool => ((unframe (dropFrame p.1), p.1), p.2))
        (encPair encBits encBits) (encPair (encPair encBits encBits) encBits)
        (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length +
          (encPair encBits encBits p).length)
        (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length +
          (encPair encBits encBits p).length) :=
      (hα.prod hfst).prod hsnd
    have hconv : ComputableInO
        (fun q : (List Bool × List Bool) × List Bool =>
          encPair (encPair encBits encBits) encBits q)
        (encPair (encPair encBits encBits) encBits) encBits
        (fun q => (encPair (encPair encBits encBits) encBits q).length)
        (fun q => (encPair (encPair encBits encBits) encBits q).length) :=
      ComputableInO.of_eq fun _ => rfl
    refine (hconv.comp hraw).mono 64 (fun p => ?_) (fun p => ?_)
    all_goals
      have hlen1 := length_unframe_le (dropFrame p.1)
      have hlen2 : (dropFrame p.1).length ≤ p.1.length := length_dropFrame_le p.1
      enc_len
  have hsym := Universal.computableInO_map_eBit.comp hpair
  have hclock := hJ_tc.computableInO.comp hfst
  have hU := computableInO_universal_nlogn.comp (hdesc.prod (hsym.prod hclock))
  have hnot : ComputableInO (fun b : Bool => !b) encBool encBool (fun _ => 1) (fun _ => 1) :=
    (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) (!·)).inO_one
  have htest := hnot.comp (Diagonal.computableInO_verdict_linear.comp hU)
  have hshort := Diagonal.computableInO_shortDesc.comp hfst
  have hV := hshort.ite htest (ComputableInO.const (encMid := encBool) false)
  obtain ⟨cO, hcO⟩ := hU.length_le
  set B : List Bool × List Bool → ℕ := fun p =>
    p.1.length + p.2.length +
      (Nat.log 2 (p.1.length + 1) + 1) ^ (ed * 6) *
        ((diagClockJ b p.1.length + 1) * (Nat.log 2 (diagClockJ b p.1.length + 1) + 1))
  have hV_time : ComputableInO (diagVerifier b) (encPair encBits encBits) encBool B B := by
    have hbound (p : List Bool × List Bool) (hs : Diagonal.shortDesc p.1 = true) :
        (2 * p.1.length + 1 + p.2.length) + ((unframe p.1).length + 1) ^ dd +
          (6 * p.1.length + 3 + p.2.length) + (p.1.length + diagClockJ b p.1.length) +
          ((eIn (decodeDesc (unframe p.1),
            (encPair (encPair encBits encBits) encBits
              ((unframe (dropFrame p.1), p.1), p.2)).map eBit,
            diagClockJ b p.1.length)).length +
            (descLen (decodeDesc (unframe p.1)) +
              listMax id ((encPair (encPair encBits encBits) encBits
                ((unframe (dropFrame p.1), p.1), p.2)).map eBit) + 2) ^ 6 *
              ((diagClockJ b p.1.length + 1) * (Nat.log 2 (diagClockJ b p.1.length + 1) + 1))) ≤
          K * (B p + 1) := by
      have hL : 2 ^ (unframe p.1).length ≤ p.1.length := of_decide_eq_true hs
      have hN := length_encList_map_eBit_le
        (encPair (encPair encBits encBits) encBits ((unframe (dropFrame p.1), p.1), p.2))
      have hJlen := Universal.length_encNat_le (diagClockJ b p.1.length)
      have hlen1 := length_unframe_le (dropFrame p.1)
      have hlen2 : (dropFrame p.1).length ≤ p.1.length := length_dropFrame_le p.1
      have hpair_len : (encPair (encPair encBits encBits) encBits
          ((unframe (dropFrame p.1), p.1), p.2)).length ≤ 6 * p.1.length + 3 + p.2.length := by
        enc_len
      refine hK hL ((hcA _).trans (Nat.mul_le_mul_left _ (hL.trans (Nat.le_succ _)))) (hce _)
        (listMax_le fun a ha => ?_) ?_
      · obtain ⟨bt, -, rfl⟩ := List.mem_map.mp ha
        cases bt <;> decide
      · enc_len [descLen]
    refine hV.mono (16 * (K + 1) * (cO + 1) + 16) (fun p => ?_) (fun p => ?_)
    all_goals
      have hO := hcO p
      dsimp only [Function.comp_apply, encBits_apply] at hO ⊢
      set W := B p with hW_def
      have hp1 : p.1.length ≤ W := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      have hp2 : p.2.length ≤ W := (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      have hlen1 := length_unframe_le (dropFrame p.1)
      have hlen2 : (dropFrame p.1).length ≤ p.1.length := length_dropFrame_le p.1
      have h1_enc : (encPair encBits encBits p).length = 2 * p.1.length + 1 + p.2.length := by
        enc_len
      have hpair_len : (encPair (encPair encBits encBits) encBits
          ((unframe (dropFrame p.1), p.1), p.2)).length ≤ 6 * p.1.length + 3 + p.2.length := by
        enc_len
      split_ifs with hs
      · have hT := hbound p hs
        rw [← hW_def] at hT
        have hmul_O : cO * (K * (W + 1) + 1) = cO * (K * (W + 1)) + cO := by ring
        have hmul_cO : cO ≤ cO * (W + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        have hmul_KW : cO * (K * (W + 1)) = (cO * K) * (W + 1) := by ring
        have hbig : (16 * (K + 1) * (cO + 1) + 16) * (W + 1) =
            16 * ((cO * K) * (W + 1)) + 16 * (K * (W + 1)) + 16 * (cO * (W + 1)) +
              32 * (W + 1) := by
          ring
        have hsum_le :
            (encPair encBits encBits p).length + (p.1.length + ((unframe p.1).length + 1) ^ dd) +
              ((encPair encBits encBits p).length +
                (encPair (encPair encBits encBits) encBits
                  ((unframe (dropFrame p.1), p.1), p.2)).length +
                ((encPair encBits encBits p).length + diagClockJ b p.1.length)) +
              ((eIn (decodeDesc (unframe p.1),
                (encPair (encPair encBits encBits) encBits
                  ((unframe (dropFrame p.1), p.1), p.2)).map eBit,
                diagClockJ b p.1.length)).length +
                (descLen (decodeDesc (unframe p.1)) +
                  listMax id ((encPair (encPair encBits encBits) encBits
                    ((unframe (dropFrame p.1), p.1), p.2)).map eBit) + 2) ^ 6 *
                  ((diagClockJ b p.1.length + 1) *
                    (Nat.log 2 (diagClockJ b p.1.length + 1) + 1))) ≤
              4 * (K * (W + 1)) := by omega
        have hO_le : (eOut (universal (decodeDesc (unframe p.1),
            (encPair (encPair encBits encBits) encBits
              ((unframe (dropFrame p.1), p.1), p.2)).map eBit,
            diagClockJ b p.1.length))).length ≤ cO * (4 * (K * (W + 1)) + 1) :=
          hO.trans (Nat.mul_le_mul_left cO (Nat.add_le_add_right hsum_le 1))
        have hO_exp : cO * (4 * (K * (W + 1)) + 1) = 4 * ((cO * K) * (W + 1)) + cO := by ring
        omega
      · have hbig : (16 * (K + 1) * (cO + 1) + 16) * (W + 1) =
            16 * (K + 1) * (cO + 1) * (W + 1) + 16 * (W + 1) := by ring
        omega
  -- Apply `setOf_exists_mem_NTIME` with `t = fun n => n + polylog(n) * J log J`,
  -- then weaken to `(n + 1) ^ (b + 1)` using `polylog_eventually_le_succ`.
  set t0 : ℕ → ℕ := fun n =>
    n + (Nat.log 2 (n + 1) + 1) ^ (ed * 6) *
      ((diagClockJ b n + 1) * (Nat.log 2 (diagClockJ b n + 1) + 1))
  have hmem0 : compH b ∈ NTIME encBits t0 := by
    refine setOf_exists_mem_NTIME (C := 4) hℓ hV_time fun x w hw => ?_
    dsimp only [encBits_apply, B, t0]
    have hLleJ : diagClockL b x.length ≤ diagClockJ b x.length := diagClockL_le_diagClockJ b _
    have hJleY : diagClockJ b x.length ≤
        (diagClockJ b x.length + 1) * (Nat.log 2 (diagClockJ b x.length + 1) + 1) :=
      (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    have hYleV : (diagClockJ b x.length + 1) * (Nat.log 2 (diagClockJ b x.length + 1) + 1) ≤
        (Nat.log 2 (x.length + 1) + 1) ^ (ed * 6) *
          ((diagClockJ b x.length + 1) * (Nat.log 2 (diagClockJ b x.length + 1) + 1)) :=
      Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
    omega
  exact NTIME_mono_of_eventually_le (polylog_eventually_le_succ b (ed * 6) hb) hmem0

/-- The hard language `hardLanguage b` lies in `coNTIME[(n + 1)^{b + 1}]`. -/
theorem hardLanguage_mem_coNTIME (b : ℕ) (hb : 1 ≤ b) :
    hardLanguage b ∈ coNTIME encBits (fun n => (n + 1) ^ (b + 1)) := by
  change (hardLanguage b)ᶜ ∈ NTIME encBits (fun n => (n + 1) ^ (b + 1))
  simpa [hardLanguage] using compH_mem_NTIME b hb

/-- The hard language `hardLanguage b` is not in `NTIME[(n + 1)^b]_{/o(n)}`. -/
theorem hardLanguage_notMem_NTIMEWithSublinearAdvice (b : ℕ) (hb : 1 ≤ b) :
    hardLanguage b ∉ NTIMEWithSublinearAdvice (fun n => (n + 1) ^ b) := by
  intro hmem
  rcases hmem with ⟨a, ha_sub, advice, hadv_len, A, hA, hA_iff⟩
  obtain ⟨V, cV, hV_inO, hV_iff⟩ := exists_verifier_of_mem_NTIME hA
  obtain ⟨c₁, htm_run, -⟩ := hV_inO
  obtain ⟨kT, State, hfin, tmV, htmV⟩ := htm_run
  let c₂ : ℕ := c₁
  have := Fintype.ofFinite State
  classical
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  let descV : List Bool := eDesc (desc eS eBit tmV)
  -- Pick `n` large enough that:
  -- (1) `2 ^ descV.length ≤ n` (`shortDesc`),
  -- (2) `2 * descV.length + 1 + (2 * a n + 1) ≤ n`,
  -- (3) `cV * (2 * a n + 1 + n + 1) ^ b + cV ≤ diagClockL b n`,
  -- (4) `c₁ * (6 * n + 3 + diagClockL b n) + c₂ ≤ diagClockJ b n`.
  obtain ⟨N1, hN1⟩ := ha_sub 4
  have hsize_inf : ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, C ≤ Nat.size ((n + 1) ^ b) + 1 := by
    intro C
    refine ⟨2 ^ C, fun n hn => ?_⟩
    have h1 : 2 ^ C ≤ n + 1 := by omega
    have h2 : 2 ^ C ≤ (n + 1) ^ b := h1.trans (Nat.le_self_pow (by omega) (n + 1))
    have h3 : C < Nat.size ((n + 1) ^ b) := Nat.lt_size.mpr h2
    omega
  obtain ⟨N2, hN2⟩ := hsize_inf (cV * 3 ^ b + cV + 1)
  obtain ⟨N3, hN3⟩ :=
    (show ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, C ≤ Nat.size (diagClockL b n) + 1 by
      intro C; refine ⟨2 ^ C, fun n hn => ?_⟩
      have h1 : 2 ^ C ≤ diagClockL b n := (by omega : 2 ^ C ≤ n + 1).trans (n_le_diagClockL b n hb)
      have h2 : C < Nat.size (diagClockL b n) := Nat.lt_size.mpr h1
      omega) (c₁ * 10 + c₂ + 1)
  obtain ⟨n, hn_desc, hn1, hn2, hn3⟩ :
      ∃ n, 2 ^ descV.length + 4 * descV.length + 8 ≤ n ∧ N1 ≤ n ∧ N2 ≤ n ∧ N3 ≤ n :=
    ⟨max (max (2 ^ descV.length + 4 * descV.length + 8) (max N1 N2)) N3,
      (le_max_left _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)),
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)),
      le_max_right _ _⟩
  have ha_le : 4 * a n ≤ n := hN1 n hn1
  have hn_lin : 4 * descV.length + 8 ≤ n :=
    (Nat.le_add_left _ (2 ^ descV.length)).trans hn_desc
  have hfit : (frame descV).length + (frame (advice n)).length ≤ n := by
    simp only [length_frame, hadv_len n]
    omega
  let pad := List.replicate (n - ((frame descV).length + (frame (advice n)).length)) false
  let x₀ : List Bool := frame descV ++ frame (advice n) ++ pad
  have hx₀_len : x₀.length = n := by
    simp only [x₀, pad, List.length_append, List.length_replicate]
    omega
  have hunframe_x₀ : unframe x₀ = descV := by
    simp only [x₀, List.append_assoc, unframe_frame_append]
  have hdrop_x₀ : unframe (dropFrame x₀) = advice n := by
    simp only [x₀, List.append_assoc, dropFrame_frame_append, unframe_frame_append]
  have hshort_x₀ : Diagonal.shortDesc x₀ = true := by
    rw [Diagonal.shortDesc, decide_eq_true_iff, hunframe_x₀, hx₀_len]
    have := Nat.zero_le (4 * descV.length + 8)
    omega
  have hL_ge : cV * ((encPair encBits encBits (advice n, x₀)).length + 1) ^ b + cV ≤
      diagClockL b n := by
    have hpair_len : (encPair encBits encBits (advice n, x₀)).length ≤ 2 * n := by
      simp only [length_encPair, encBits_apply, hadv_len n, hx₀_len]
      omega
    have hpow_le : ((encPair encBits encBits (advice n, x₀)).length + 1) ^ b ≤
        (3 * (n + 1)) ^ b := Nat.pow_le_pow_left (by omega) b
    have hmul : cV * (3 * (n + 1)) ^ b + cV ≤ (cV * 3 ^ b + cV + 1) * (n + 1) ^ b := by
      rw [mul_pow]
      have hpos : 1 ≤ (n + 1) ^ b := Nat.pow_pos (Nat.succ_pos _)
      have h1 : cV * (3 ^ b * (n + 1) ^ b) = (cV * 3 ^ b) * (n + 1) ^ b := by ring
      have h2 : (cV * 3 ^ b + cV + 1) * (n + 1) ^ b =
          (cV * 3 ^ b) * (n + 1) ^ b + cV * (n + 1) ^ b + (n + 1) ^ b := by ring
      have h3 : cV ≤ cV * (n + 1) ^ b := Nat.le_mul_of_pos_right _ hpos
      omega
    have hstep := Nat.mul_le_mul_left ((n + 1) ^ b) (hN2 n hn2)
    unfold diagClockL
    calc cV * ((encPair encBits encBits (advice n, x₀)).length + 1) ^ b + cV
        ≤ cV * (3 * (n + 1)) ^ b + cV := by gcongr
      _ ≤ (cV * 3 ^ b + cV + 1) * (n + 1) ^ b := hmul
      _ = (n + 1) ^ b * (cV * 3 ^ b + cV + 1) := Nat.mul_comm _ _
      _ ≤ (n + 1) ^ b * (Nat.size ((n + 1) ^ b) + 1) := hstep
  have hdiag_iff : x₀ ∈ compH b ↔ x₀ ∈ hardLanguage b := by
    rw [hA_iff x₀, hx₀_len, hV_iff (advice n, x₀) (diagClockL b n) hL_ge]
    change (∃ w, w.length = diagClockL b x₀.length ∧ diagVerifier b (x₀, w) = true) ↔ _
    rw [hx₀_len]
    refine exists_congr fun w => and_congr_right fun hw => ?_
    simp only [diagVerifier, hx₀_len, hshort_x₀, ↓reduceIte, hunframe_x₀, hdrop_x₀]
    set u := encPair (encPair encBits encBits) encBits ((advice n, x₀), w)
    have hu_len : u.length ≤ 6 * n + 3 + diagClockL b n := by
      simp only [u, length_encPair, encBits_apply, hadv_len n, hx₀_len, hw]
      omega
    have htime_le : c₁ * (u.length + 1) ≤ diagClockJ b n := by
      have h1 : 6 * n + 3 + diagClockL b n + 1 ≤ 10 * diagClockL b n := by
        have := n_le_diagClockL b n hb
        omega
      have h2 : c₁ * (u.length + 1) ≤ (c₁ * 10 + c₂ + 1) * diagClockL b n := by
        have hpos : 1 ≤ diagClockL b n := (Nat.succ_pos _).trans_le (n_le_diagClockL b n hb)
        have ha : c₁ * (u.length + 1) ≤ c₁ * (10 * diagClockL b n) :=
          Nat.mul_le_mul_left c₁ (by omega)
        have hb' : c₁ * (10 * diagClockL b n) = (c₁ * 10) * diagClockL b n := by ring
        have hc' : (c₁ * 10 + c₂ + 1) * diagClockL b n =
            (c₁ * 10) * diagClockL b n + (c₂ + 1) * diagClockL b n := by ring
        omega
      have h3 := Nat.mul_le_mul_left (diagClockL b n) (hN3 n hn3)
      unfold diagClockJ
      calc c₁ * (u.length + 1) ≤ (c₁ * 10 + c₂ + 1) * diagClockL b n := h2
        _ = diagClockL b n * (c₁ * 10 + c₂ + 1) := Nat.mul_comm _ _
        _ ≤ diagClockL b n * (Nat.size (diagClockL b n) + 1) := h3
    obtain ⟨hhalt, hout⟩ := (htmV ((advice n, x₀), w)).runFrom_of_le htime_le
    rw [decodeDesc_eDesc, universal_desc, hout]
    simp only [Cfg.Halted] at hhalt
    rw [hhalt, encBool_apply, List.map_cons, List.map_nil]
    cases V ((advice n, x₀), w) <;> simp [Diagonal.verdict, eBit]
  have hcontra : x₀ ∈ compH b ↔ x₀ ∉ compH b := hdiag_iff
  exact absurd (hcontra.mpr fun h => hcontra.mp h h) (fun h => hcontra.mp h h)

/-- ** (No Complementary Speedup)**: for every `b ≥ 1`,
`coNTIME[(n + 1)^{b + 1}] ⊈ NTIME[(n + 1)^b]_{/o(n)}`.
-/
theorem no_complementary_speedup (b : ℕ) (hb : 1 ≤ b) :
    ¬ coNTIME encBits (fun n => (n + 1) ^ (b + 1)) ⊆
      NTIMEWithSublinearAdvice (fun n => (n + 1) ^ b) :=
  fun hsub => hardLanguage_notMem_NTIMEWithSublinearAdvice b hb
    (hsub (hardLanguage_mem_coNTIME b hb))

end CslibFrontier.Computability.Complexity
