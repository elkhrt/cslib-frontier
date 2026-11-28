/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Alternation-Trading Proof Calculus and Time-Space Lower Bounds

This module formalizes a standalone alternation-trading proof calculus for simultaneous time-space
lower bounds on nondeterministic linear time and bounded-alternation classes:

* Concrete block-configuration splitting for deterministic finite-state transition systems
  (`DetTransSys`, `verifySegmentPacked`, `dtisp_config_split`, `dtisp_config_split_exact_div`).
* Input-constrained alternating time-space states, speedup and slowdown transition rules,
  normal-form alternation-trading certificates (`ATState`, `ATStep`, `execATScript`, `ATProof`),
  and soundness for any parametric time-space calculus (`GenTimeSpaceSystem`,
  `atProof_refutes_sat_dtisp`).
* A postulate-free canonical semantic model (`canonicalGenTimeSpaceSystem`,
  `canonical_sat_dtisp_iff`) witnessing non-vacuity and exact sharpness of the quadratic barrier.
* The minimal cubic identity `u ^ 3 - u ^ 2 - 2 * u + 1 = 0` for `2 cos(π / 7)`
  (`twoCosPiDivSeven`, `cubic_root_identity`).
* A linear potential function proving the exact `c ≥ 1 + β` barrier (`atPotential`,
  `generalized_barrier_one_add_beta`, `quadratic_barrier`).

## Main definitions

* `CslibFrontier.Complexity.AlternationTrading.DetTransSys`, `verifySegmentPacked`
* `CslibFrontier.Complexity.AlternationTrading.ATState`, `ATStep`, `execATScript`, `ATProof`
* `CslibFrontier.Complexity.AlternationTrading.GenTimeSpaceSystem`, `TimeSpaceSystem`,
  `canonicalGenTimeSpaceSystem`
* `CslibFrontier.Complexity.AlternationTrading.twoCosPiDivSeven`, `atPotential`

## Main results

* `CslibFrontier.Complexity.AlternationTrading.dtisp_config_split`, `dtisp_config_split_exact_div`
* `CslibFrontier.Complexity.AlternationTrading.atProof_refutes_sat_dtisp`
* `CslibFrontier.Complexity.AlternationTrading.canonical_sat_dtisp_iff`
* `CslibFrontier.Complexity.AlternationTrading.cubic_root_identity`
* `CslibFrontier.Complexity.AlternationTrading.generalized_barrier_one_add_beta`,
  `quadratic_barrier`
-/

public section

namespace CslibFrontier.Complexity.AlternationTrading

/-! ## 1. Elementary Real Power Helpers -/

private theorem bernoulli_pow_ge {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ n : ℕ, 1 + (n : ℝ) * δ ≤ (1 + δ) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_pow_ge hδ n
    have h1 : 0 ≤ 1 + δ := by linarith
    have h2 : (1 + δ) * (1 + (n : ℝ) * δ) ≤ (1 + δ) * (1 + δ) ^ n :=
      mul_le_mul_of_nonneg_left ih h1
    have h3 : (1 + δ) ^ (n + 1) = (1 + δ) * (1 + δ) ^ n := pow_succ' (1 + δ) n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h4 : 0 ≤ (n : ℝ) * δ ^ 2 := mul_nonneg hn (sq_nonneg δ)
    push_cast
    nlinarith

private theorem exists_pow_gt_of_one_lt {r B : ℝ} (hr : 1 < r) : ∃ m : ℕ, B < r ^ m := by
  let δ := r - 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((max B 0) / δ)
  refine ⟨m, ?_⟩
  have h1 : max B 0 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hm
  have h2 := bernoulli_pow_ge (le_of_lt hδ) m
  have hr_eq : 1 + δ = r := by dsimp [δ]; ring
  rw [hr_eq] at h2
  linarith [le_max_left B 0]

/-! ## 2. Concrete Deterministic Block-Configuration Speedup -/

/-- A Boolean assignment of `n` bits. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- Deterministic finite-state transition system on `S`-bit configurations. -/
structure DetTransSys (S : ℕ) where
  init : Assignment S
  step : Assignment S → Assignment S
  accept : Assignment S → Bool

/-- Acceptance of `M` after exactly `T` transitions. -/
@[expose] def DetTransSys.acceptsIn {S : ℕ} (M : DetTransSys S) (T : ℕ) : Bool :=
  M.accept (M.step^[T] M.init)

/-- Ceiling per-segment step cap `⌈T / k⌉`. -/
@[expose] def segStepCap (T k : ℕ) : ℕ :=
  (T + k - 1) / k

/-- Cumulative step count after the first `i` segments. -/
@[expose] def segPrefixSteps (T k i : ℕ) : ℕ :=
  min T (i * segStepCap T k)

/-- Exact step count of segment `i : Fin k`. -/
@[expose] def segLen (T k : ℕ) (i : Fin k) : ℕ :=
  segPrefixSteps T k (i.val + 1) - segPrefixSteps T k i.val

private theorem segPrefixSteps_mono (T k : ℕ) {i j : ℕ} (hij : i ≤ j) :
    segPrefixSteps T k i ≤ segPrefixSteps T k j :=
  min_le_min_left T (Nat.mul_le_mul_right _ hij)

private theorem segPrefixSteps_add_segLen (T k i : ℕ) (hk : i < k) :
    segPrefixSteps T k i + segLen T k ⟨i, hk⟩ = segPrefixSteps T k (i + 1) :=
  Nat.add_sub_of_le (segPrefixSteps_mono T k (Nat.le_succ i))

private theorem segPrefixSteps_full (T : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    segPrefixSteps T k k = T := by
  unfold segPrefixSteps segStepCap
  apply min_eq_left
  have hk_pos : 0 < k := by omega
  have h1 := Nat.div_add_mod (T + k - 1) k
  have h2 := Nat.mod_lt (T + k - 1) hk_pos
  have h3 : k * ((T + k - 1) / k) = ((T + k - 1) / k) * k := Nat.mul_comm _ _
  omega

private theorem segLen_le_cap (T k : ℕ) (i : Fin k) : segLen T k i ≤ segStepCap T k := by
  unfold segLen segPrefixSteps
  have hmul : (i.val + 1) * segStepCap T k = i.val * segStepCap T k + segStepCap T k := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hmul]
  omega

/-- Pack `k - 1` intermediate `S`-bit configurations into a flat `((k - 1) * S)`-bit witness. -/
@[expose] def packMids {S k : ℕ} (mids : Fin (k - 1) → Assignment S) :
    Assignment ((k - 1) * S) :=
  fun idx =>
    if hS : 0 < S then
      mids ⟨idx.val / S, (Nat.div_lt_iff_lt_mul hS).mpr idx.isLt⟩
        ⟨idx.val % S, Nat.mod_lt idx.val hS⟩
    else False.elim (by
      have h0 : S = 0 := Nat.eq_zero_of_not_pos hS
      have := idx.isLt
      simp [h0] at this)

/-- Unpack a flat `((k - 1) * S)`-bit witness back into `k - 1` intermediate configurations. -/
@[expose] def unpackMids {S k : ℕ} (w : Assignment ((k - 1) * S)) :
    Fin (k - 1) → Assignment S :=
  fun j b => w ⟨j.val * S + b.val, by
    have h1 : j.val + 1 ≤ k - 1 := j.isLt
    have h2 : (j.val + 1) * S ≤ (k - 1) * S := Nat.mul_le_mul_right S h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left b.isLt _) h2⟩

private theorem unpackMids_packMids {S k : ℕ} (mids : Fin (k - 1) → Assignment S) :
    unpackMids (packMids mids) = mids := by
  funext j b
  have hS : 0 < S := Nat.zero_lt_of_lt b.isLt
  unfold unpackMids packMids
  simp only [hS, ↓reduceDIte]
  have hdiv : (j.val * S + b.val) / S = j.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt b.isLt,
      Nat.zero_add]
  have hmod : (j.val * S + b.val) % S = b.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
  have hj : (⟨(j.val * S + b.val) / S, by
      exact (Nat.div_lt_iff_lt_mul hS).mpr (by
        have h1 : j.val + 1 ≤ k - 1 := j.isLt
        have h2 : (j.val + 1) * S ≤ (k - 1) * S := Nat.mul_le_mul_right S h1
        rw [Nat.add_mul, Nat.one_mul] at h2
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left b.isLt _) h2)⟩ : Fin (k - 1)) = j :=
    Fin.ext hdiv
  have hb : (⟨(j.val * S + b.val) % S, Nat.mod_lt _ hS⟩ : Fin S) = b := Fin.ext hmod
  rw [hj, hb]

/-- Little-endian natural number decoded from `m` bits. -/
@[expose] def bitsToNat : {m : ℕ} → Assignment m → ℕ
  | 0, _ => 0
  | _ + 1, u => (if u 0 then 1 else 0) + 2 * bitsToNat (fun i => u i.succ)

/-- Little-endian `m`-bit binary encoding of `n`. -/
@[expose] def natToBits (m n : ℕ) : Assignment m :=
  fun i => n.testBit i.val

private theorem bitsToNat_natToBits :
    ∀ (m n : ℕ), n < 2 ^ m → bitsToNat (natToBits m n) = n
  | 0, n, hn => by simp only [bitsToNat, pow_zero] at hn ⊢; omega
  | m + 1, n, hn => by
    unfold bitsToNat
    have htail : (fun i : Fin m => natToBits (m + 1) n i.succ) = natToBits m (n / 2) := by
      funext i; simp only [natToBits, Fin.val_succ, Nat.testBit_div_two]
    have h0 : natToBits (m + 1) n 0 = decide (n % 2 = 1) := by
      simp [natToBits, Nat.testBit_zero]
    rw [htail, h0, bitsToNat_natToBits m (n / 2) (by rw [pow_succ'] at hn; omega)]
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;> simp [hm] <;> omega

/-- Deterministic verifier for segment `i : Fin k` of a `k`-way split of `M` over `T` steps. -/
@[expose] def verifySegment {S : ℕ} (M : DetTransSys S) (T k : ℕ)
    (mids : Fin (k - 1) → Assignment S) (i : Fin k) : Bool :=
  let startCfg : Assignment S :=
    if h0 : i.val = 0 then M.init else mids ⟨i.val - 1, by omega⟩
  let endCfg := M.step^[segLen T k i] startCfg
  if hlast : i.val < k - 1 then
    decide (endCfg = mids ⟨i.val, hlast⟩)
  else
    M.accept endCfg

/-- Packed `Σ₂` segment verifier: existentially guesses `w` of `(k - 1) * S` bits and universally
checks `u` of `⌈log₂ k⌉` bits. -/
@[expose] def verifySegmentPacked {S : ℕ} (M : DetTransSys S) (T k : ℕ)
    (w : Assignment ((k - 1) * S)) (u : Assignment (Nat.clog 2 k)) : Bool :=
  let idx := bitsToNat u
  if h : idx < k then verifySegment M T k (unpackMids w) ⟨idx, h⟩ else true

/-- **Concrete Block-Configuration Speedup Theorem**:
For every deterministic transition system `M` on `S`-bit configurations, step budget `T`, and
block count `k ≥ 1`, every segment has length `≤ ⌈T / k⌉`, and `M` accepts in `T` steps iff
there exists a `((k - 1) * S)`-bit intermediate configuration table verified universally across
all `⌈log₂ k⌉`-bit segment indices. -/
theorem dtisp_config_split {S : ℕ} (M : DetTransSys S) (T k : ℕ) (hk : 1 ≤ k) :
    (∀ i : Fin k, segLen T k i ≤ segStepCap T k) ∧
    (M.acceptsIn T = true ↔
      ∃ w : Assignment ((k - 1) * S),
        ∀ u : Assignment (Nat.clog 2 k),
          verifySegmentPacked M T k w u = true) := by
  refine ⟨fun i => segLen_le_cap T k i, ?_⟩
  constructor
  · intro hacc
    let trueMids : Fin (k - 1) → Assignment S :=
      fun j => M.step^[segPrefixSteps T k (j.val + 1)] M.init
    refine ⟨packMids trueMids, fun u => ?_⟩
    unfold verifySegmentPacked
    dsimp only
    split_ifs with hlt
    · rw [unpackMids_packMids]
      unfold verifySegment
      dsimp only
      have hstart : (if h0 : bitsToNat u = 0 then M.init
            else trueMids ⟨bitsToNat u - 1, by omega⟩) =
          M.step^[segPrefixSteps T k (bitsToNat u)] M.init := by
        split_ifs with h0
        · simp [h0, segPrefixSteps]
        · dsimp [trueMids]
          have heq : bitsToNat u - 1 + 1 = bitsToNat u := by omega
          rw [heq]
      rw [hstart, ← Function.iterate_add_apply,
        Nat.add_comm (segLen T k ⟨bitsToNat u, hlt⟩),
        segPrefixSteps_add_segLen T k (bitsToNat u) hlt]
      split_ifs with hlast
      · simp [trueMids]
      · have heqk : bitsToNat u + 1 = k := by omega
        simp only [heqk, segPrefixSteps_full T hk]
        exact hacc
    · rfl
  · rintro ⟨w, hw⟩
    let mids := unpackMids w
    have hseg : ∀ i : Fin k, verifySegment M T k mids i = true := by
      intro i
      have hpow : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by norm_num : 1 < 2) k
      have hilt : i.val < 2 ^ Nat.clog 2 k := Nat.lt_of_lt_of_le i.isLt hpow
      have hu := hw (natToBits (Nat.clog 2 k) i.val)
      unfold verifySegmentPacked at hu
      dsimp only at hu
      simp only [bitsToNat_natToBits _ _ hilt, i.isLt, ↓reduceDIte] at hu
      exact hu
    have hind : ∀ (j : ℕ) (hj : j < k - 1),
        mids ⟨j, hj⟩ = M.step^[segPrefixSteps T k (j + 1)] M.init := by
      intro j
      induction j with
      | zero =>
        intro hj
        have hs0 := hseg ⟨0, by omega⟩
        unfold verifySegment at hs0
        simp only [↓reduceDIte, hj, decide_eq_true_eq] at hs0
        have hlen0 : segLen T k ⟨0, by omega⟩ = segPrefixSteps T k (0 + 1) := by
          have h := segPrefixSteps_add_segLen T k 0 (by omega)
          simp only [segPrefixSteps, Nat.zero_mul, Nat.min_zero, Nat.zero_add] at h
          exact h
        rw [hlen0] at hs0
        exact hs0.symm
      | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        have hsj := hseg ⟨j + 1, by omega⟩
        unfold verifySegment at hsj
        have hne0 : j + 1 ≠ 0 := by omega
        simp only [hne0, ↓reduceDIte, Nat.add_sub_cancel, hj, decide_eq_true_eq] at hsj
        rw [hprev, ← Function.iterate_add_apply,
          Nat.add_comm (segLen T k ⟨j + 1, by omega⟩),
          segPrefixSteps_add_segLen T k (j + 1)] at hsj
        exact hsj.symm
    have hslast := hseg ⟨k - 1, by omega⟩
    unfold verifySegment at hslast
    have hnlt : ¬(k - 1 < k - 1) := Nat.lt_irrefl _
    by_cases hk1 : k - 1 = 0
    · have hkeq1 : k = 1 := by omega
      subst hkeq1
      simp only [↓reduceDIte, hnlt] at hslast
      have hlen1 : segLen T 1 ⟨0, by omega⟩ = T := by
        have h := segPrefixSteps_add_segLen T 1 0 (by omega)
        rw [Nat.zero_add, segPrefixSteps_full T le_rfl] at h
        simp only [segPrefixSteps, Nat.zero_mul, Nat.min_zero, Nat.zero_add] at h
        exact h
      rwa [hlen1] at hslast
    · simp only [hk1, ↓reduceDIte, hnlt] at hslast
      have hprev := hind (k - 2) (by omega)
      have hidx : (⟨k - 1 - 1, by omega⟩ : Fin (k - 1)) = ⟨k - 2, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hidx, hprev, show k - 2 + 1 = k - 1 by omega, ← Function.iterate_add_apply,
        Nat.add_comm (segLen T k ⟨k - 1, by omega⟩),
        segPrefixSteps_add_segLen T k (k - 1) (by omega),
        show k - 1 + 1 = k by omega, segPrefixSteps_full T hk] at hslast
      exact hslast

/-- Exact-divisibility corollary: when `k ∣ T`, every segment runs in `≤ T / k` steps. -/
theorem dtisp_config_split_exact_div {S : ℕ} (M : DetTransSys S) (T k : ℕ)
    (hk : 1 ≤ k) (hdvd : k ∣ T) :
    (∀ i : Fin k, segLen T k i ≤ T / k) ∧
    (M.acceptsIn T = true ↔
      ∃ w : Assignment ((k - 1) * S),
        ∀ u : Assignment (Nat.clog 2 k),
          verifySegmentPacked M T k w u = true) := by
  obtain ⟨hlen, hiff⟩ := dtisp_config_split M T k hk
  have hcap : segStepCap T k = T / k := by
    rcases hdvd with ⟨q, rfl⟩
    unfold segStepCap
    have hk_pos : 0 < k := by omega
    rw [Nat.mul_div_right q hk_pos]
    have h1 : k * q + k - 1 = (k - 1) + q * k := by
      have := Nat.mul_comm k q; omega
    rw [h1, Nat.add_mul_div_right _ _ hk_pos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [← hcap]
  exact ⟨hlen, hiff⟩

/-! ## 3. Alternation-Trading Calculus, Canonical Model, Bounds, and Quadratic Barrier -/

/-- Quantifier polarity (`∃` or `∀`). -/
inductive Quant where
  | ex
  | fa
  deriving DecidableEq, Repr

/-- Dual quantifier polarity. -/
@[expose] def Quant.dual : Quant → Quant
  | .ex => .fa
  | .fa => .ex

/-- Preceding input-constraint exponent `b_k` (`1` when `pref` is empty). -/
@[expose] def prevInputBound : List (Quant × ℝ × ℝ) → ℝ
  | [] => 1
  | [(_, _, b)] => b
  | _ :: tl => prevInputBound tl

private theorem prevInputBound_eq_revHead :
    ∀ l : List (Quant × ℝ × ℝ),
      prevInputBound l = match l.reverse with | [] => 1 | (_, _, b) :: _ => b
  | [] => rfl
  | [_] => rfl
  | _ :: b :: rest => by
    have ih := prevInputBound_eq_revHead (b :: rest)
    dsimp only [prevInputBound]
    rw [ih]
    rcases h : (b :: rest).reverse with _ | ⟨hd, tl⟩
    · simp at h
    · simp [h]

/-- Input-constrained alternating time-space class state. -/
@[ext] structure ATState where
  blocks : List (Quant × ℝ × ℝ)
  dtsTime : ℝ
  dtsSpace : ℝ

/-- Syntactic alternation-trading derivation step. -/
inductive ATStep where
  | speedup0 (q : Quant) (x : ℝ)
  | speedup1 (x : ℝ)
  | speedup2 (x : ℝ)
  | slowdown

/-- Exact step transition semantics for trade parameter `β ≥ 1`, time exponent `c`, space `ε`. -/
@[expose] noncomputable def execATStep (β c ε : ℝ) (step : ATStep) (st : ATState) :
    Option ATState :=
  match step with
  | .speedup0 q x =>
    match st.blocks with
    | [] =>
      if 0 ≤ st.dtsSpace ∧ 0 < x ∧ β * x < st.dtsTime then
        some ⟨[(q, x + st.dtsSpace, max (x + st.dtsSpace) 1),
               (q.dual, 0, max st.dtsSpace 1)], st.dtsTime - β * x, st.dtsSpace⟩
      else none
    | _ :: _ => none
  | .speedup1 x =>
    match st.blocks.reverse with
    | [] => none
    | (qk, ak, bk1) :: revPref =>
      if 0 ≤ st.dtsSpace ∧ 0 < x ∧ β * x < st.dtsTime then
        some ⟨revPref.reverse ++
                [(qk, max ak (x + st.dtsSpace), max (x + st.dtsSpace) bk1),
                 (qk.dual, 0, max st.dtsSpace bk1)],
              st.dtsTime - β * x, st.dtsSpace⟩
      else none
  | .speedup2 x =>
    match st.blocks.reverse with
    | [] => none
    | (qk, ak, bk1) :: revPref =>
      if 0 ≤ st.dtsSpace ∧ 0 < x ∧ β * x < st.dtsTime then
        some ⟨revPref.reverse ++
                [(qk, ak, bk1), (qk.dual, x + st.dtsSpace, max (x + st.dtsSpace) bk1),
                 (qk, 0, max st.dtsSpace bk1)],
              st.dtsTime - β * x, st.dtsSpace⟩
      else none
  | .slowdown =>
    match st.blocks.reverse with
    | [] => none
    | (_, ak, bk1) :: revPref =>
      if st.dtsSpace ≤ st.dtsTime then
        let pref := revPref.reverse
        let M := max st.dtsTime (max ak (max (prevInputBound pref) bk1))
        some ⟨pref, c * M, ε * M⟩
      else none

/-- Sequential script execution. -/
@[expose] noncomputable def execATScript (β c ε : ℝ) :
    List ATStep → ATState → Option ATState
  | [], st => some st
  | s :: rest, st =>
    match execATStep β c ε s st with
    | none => none
    | some st' => execATScript β c ε rest st'

/-- A finite normal-form alternation-trading proof certificate establishing a strict contraction
`DTISP[a₀, (ε / c) · a₀] ⊆ DTISP[a₁, (ε / c) · a₁]` with `1 ≤ a₁ < a₀`. -/
structure ATProof (β c ε : ℝ) where
  a₀ : ℝ
  a₁ : ℝ
  script : List ATStep
  ha₁_ge_one : 1 ≤ a₁
  ha₁_lt_a₀ : a₁ < a₀
  valid_run :
    execATScript β c ε script ⟨[], a₀, (ε / c) * a₀⟩ = some ⟨[], a₁, (ε / c) * a₁⟩

/-- Parametric complexity calculus supporting block-configuration speedup with trade factor `β ≥ 1`,
slowdown under `NTIME 1 ⊆ DTISP c ε`, polynomial padding,
  and the nondeterministic time hierarchy. -/
structure GenTimeSpaceSystem (β : ℝ) where
  Class : Type
  sub : Class → Class → Prop
  sub_refl : ∀ C, sub C C
  sub_trans : ∀ {A B C}, sub A B → sub B C → sub A C
  hβ : 1 ≤ β
  dtisp : ℝ → ℝ → Class
  icClass : List (Quant × ℝ × ℝ) → ℝ → ℝ → Class
  ntime : ℝ → Class
  icClass_nil : ∀ d e, icClass [] d e = dtisp d e
  dtisp_sub_ntime : ∀ {a b : ℝ}, 1 ≤ a → b ≤ a → sub (dtisp a b) (ntime a)
  pad_dtisp : ∀ {a₁ b₁ a₂ b₂ r : ℝ}, 1 ≤ r →
    sub (dtisp a₁ b₁) (dtisp a₂ b₂) → sub (dtisp (r * a₁) (r * b₁)) (dtisp (r * a₂) (r * b₂))
  pad_ntime_to_dtisp : ∀ {c ε r : ℝ}, 1 ≤ r →
    sub (ntime 1) (dtisp c ε) → sub (ntime r) (dtisp (c * r) (ε * r))
  speedup_rule0 : ∀ (q₁ : Quant) {d e x : ℝ}, 0 ≤ e → 0 < x → β * x < d →
    sub (icClass [] d e)
      (icClass [(q₁, x + e, max (x + e) 1), (q₁.dual, 0, max e 1)] (d - β * x) e)
  speedup_rule1 : ∀ (pref : List (Quant × ℝ × ℝ)) (qk : Quant) {ak bk1 d e x : ℝ},
    0 ≤ e → 0 < x → β * x < d →
    sub (icClass (pref ++ [(qk, ak, bk1)]) d e)
      (icClass (pref ++ [(qk, max ak (x + e), max (x + e) bk1), (qk.dual, 0, max e bk1)])
        (d - β * x) e)
  speedup_rule2 : ∀ (pref : List (Quant × ℝ × ℝ)) (qk : Quant) {ak bk1 d e x : ℝ},
    0 ≤ e → 0 < x → β * x < d →
    sub (icClass (pref ++ [(qk, ak, bk1)]) d e)
      (icClass (pref ++ [(qk, ak, bk1), (qk.dual, x + e, max (x + e) bk1),
        (qk, 0, max e bk1)]) (d - β * x) e)
  slowdown_rule : ∀ {c ε : ℝ} (pref : List (Quant × ℝ × ℝ)) (qk : Quant) {ak bk1 d e : ℝ},
    0 ≤ ε → e ≤ d → sub (ntime 1) (dtisp c ε) →
    let M := max d (max ak (max (prevInputBound pref) bk1))
    sub (icClass (pref ++ [(qk, ak, bk1)]) d e) (icClass pref (c * M) (ε * M))
  ntime_hierarchy : ∀ {r s : ℝ}, 1 ≤ s → s < r → ¬ sub (ntime r) (ntime s)

/-- Classical simultaneous time-space calculus (`β = 1`). -/
abbrev TimeSpaceSystem := GenTimeSpaceSystem 1

private theorem execATStep_sound {β c ε : ℝ} (sys : GenTimeSpaceSystem β)
    (hε : 0 ≤ ε) (hsat : sys.sub (sys.ntime 1) (sys.dtisp c ε))
    (step : ATStep) (st st' : ATState)
    (hexec : execATStep β c ε step st = some st') :
    sys.sub (sys.icClass st.blocks st.dtsTime st.dtsSpace)
      (sys.icClass st'.blocks st'.dtsTime st'.dtsSpace) := by
  rcases st with ⟨blocks, d, e⟩
  cases step with
  | speedup0 q x =>
    dsimp only [execATStep] at hexec
    cases blocks with
    | cons _ _ => simp at hexec
    | nil =>
      split_ifs at hexec with hcond
      rcases Option.some.inj hexec with rfl
      exact sys.speedup_rule0 q hcond.1 hcond.2.1 hcond.2.2
  | speedup1 x =>
    dsimp only [execATStep] at hexec
    rcases hrev : blocks.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec
      split_ifs at hexec with hcond
      rcases Option.some.inj hexec with rfl
      have hbl : blocks = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      rw [hbl]
      exact sys.speedup_rule1 revPref.reverse qk hcond.1 hcond.2.1 hcond.2.2
  | speedup2 x =>
    dsimp only [execATStep] at hexec
    rcases hrev : blocks.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec
      split_ifs at hexec with hcond
      rcases Option.some.inj hexec with rfl
      have hbl : blocks = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      rw [hbl]
      exact sys.speedup_rule2 revPref.reverse qk hcond.1 hcond.2.1 hcond.2.2
  | slowdown =>
    dsimp only [execATStep] at hexec
    rcases hrev : blocks.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec
      split_ifs at hexec with hed
      rcases Option.some.inj hexec with rfl
      have hbl : blocks = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      rw [hbl]
      exact sys.slowdown_rule revPref.reverse qk hε hed hsat

private theorem execATScript_sound {β c ε : ℝ} (sys : GenTimeSpaceSystem β)
    (hε : 0 ≤ ε) (hsat : sys.sub (sys.ntime 1) (sys.dtisp c ε))
    (script : List ATStep) (st st' : ATState)
    (hexec : execATScript β c ε script st = some st') :
    sys.sub (sys.icClass st.blocks st.dtsTime st.dtsSpace)
      (sys.icClass st'.blocks st'.dtsTime st'.dtsSpace) := by
  induction script generalizing st with
  | nil =>
    simp only [execATScript, Option.some.injEq] at hexec; subst hexec; exact sys.sub_refl _
  | cons hd tl ih =>
    simp only [execATScript] at hexec
    cases h1 : execATStep β c ε hd st with
    | none => simp [h1] at hexec
    | some mid =>
      rw [h1] at hexec
      exact sys.sub_trans (execATStep_sound sys hε hsat hd st mid h1) (ih mid hexec)

private theorem iterated_pad_dtisp {β : ℝ} (sys : GenTimeSpaceSystem β)
    {a₀ a₁ ρ : ℝ} (ha₁ : 1 ≤ a₁) (hlt : a₁ < a₀)
    (hsub : sys.sub (sys.dtisp a₀ (ρ * a₀)) (sys.dtisp a₁ (ρ * a₁))) :
    ∀ m : ℕ, sys.sub
      (sys.dtisp ((a₀ / a₁) ^ m * a₁) (ρ * ((a₀ / a₁) ^ m * a₁)))
      (sys.dtisp a₁ (ρ * a₁))
  | 0 => by simp only [pow_zero, one_mul]; exact sys.sub_refl _
  | m + 1 => by
    have ih := iterated_pad_dtisp sys ha₁ hlt hsub m
    have hrat : 1 < a₀ / a₁ := (one_lt_div (by linarith)).mpr hlt
    have hpad := sys.pad_dtisp (r := (a₀ / a₁) ^ m) (one_le_pow₀ (le_of_lt hrat)) hsub
    have ha₁_ne : a₁ ≠ 0 := by linarith
    have heq1 : (a₀ / a₁) ^ m * a₀ = (a₀ / a₁) ^ (m + 1) * a₁ := by rw [pow_succ]; field_simp
    have heq2 : (a₀ / a₁) ^ m * (ρ * a₀) = ρ * ((a₀ / a₁) ^ (m + 1) * a₁) := by
      rw [← mul_left_comm ρ, heq1]
    have heq3 : (a₀ / a₁) ^ m * (ρ * a₁) = ρ * ((a₀ / a₁) ^ m * a₁) := by ring
    rw [heq1, heq2, heq3] at hpad
    exact sys.sub_trans hpad ih

/-- **Universal Alternation-Trading Soundness**:
Existence of any valid strict-contraction `ATProof β c ε` (`1 ≤ c`, `0 ≤ ε ≤ c`) refutes
`ntime 1 ⊆ dtisp c ε` in every `GenTimeSpaceSystem β`. -/
theorem atProof_refutes_sat_dtisp {β c ε : ℝ} (sys : GenTimeSpaceSystem β)
    (hc : 1 ≤ c) (hε0 : 0 ≤ ε) (hεc : ε ≤ c) (P : ATProof β c ε) :
    ¬ sys.sub (sys.ntime 1) (sys.dtisp c ε) := by
  intro hsat
  have hc_pos : 0 < c := by linarith
  have hstep : sys.sub (sys.dtisp P.a₀ ((ε / c) * P.a₀)) (sys.dtisp P.a₁ ((ε / c) * P.a₁)) := by
    have hs := execATScript_sound sys hε0 hsat P.script _ _ P.valid_run
    simpa [sys.icClass_nil] using hs
  have hrat : 1 < P.a₀ / P.a₁ := (one_lt_div (by linarith [P.ha₁_ge_one])).mpr P.ha₁_lt_a₀
  obtain ⟨m, hm⟩ := exists_pow_gt_of_one_lt (B := c) hrat
  let R : ℝ := (P.a₀ / P.a₁) ^ m * (P.a₁ / c)
  have hR_gt_a₁ : P.a₁ < R := by
    dsimp [R]
    have h1 := mul_lt_mul_of_pos_right hm (div_pos (by linarith [P.ha₁_ge_one] : 0 < P.a₁) hc_pos)
    rwa [mul_div_cancel₀ P.a₁ (ne_of_gt hc_pos)] at h1
  have hnt_dt : sys.sub (sys.ntime R) (sys.dtisp ((P.a₀ / P.a₁) ^ m * P.a₁)
      ((ε / c) * ((P.a₀ / P.a₁) ^ m * P.a₁))) := by
    have hp := sys.pad_ntime_to_dtisp (le_trans P.ha₁_ge_one (le_of_lt hR_gt_a₁)) hsat
    have heqT : c * R = (P.a₀ / P.a₁) ^ m * P.a₁ := by dsimp [R]; field_simp
    have heqS : ε * R = (ε / c) * ((P.a₀ / P.a₁) ^ m * P.a₁) := by dsimp [R]; field_simp
    rwa [heqT, heqS] at hp
  have hiter := iterated_pad_dtisp sys P.ha₁_ge_one P.ha₁_lt_a₀ hstep m
  have hdt_nt : sys.sub (sys.dtisp P.a₁ ((ε / c) * P.a₁)) (sys.ntime P.a₁) := by
    refine sys.dtisp_sub_ntime P.ha₁_ge_one ?_
    have hdiv_le : ε / c ≤ 1 := (div_le_one hc_pos).mpr hεc
    nlinarith [P.ha₁_ge_one]
  exact sys.ntime_hierarchy P.ha₁_ge_one hR_gt_a₁
    (sys.sub_trans hnt_dt (sys.sub_trans hiter hdt_nt))

/-! ## 4. Non-Vacuous Canonical Model & Sharp Barrier Equivalence -/

private noncomputable def modelRevEval (β : ℝ) : List (Quant × ℝ × ℝ) → ℝ → ℝ
  | [], cur => cur
  | (_, ak, bk1) :: revPref, cur =>
    let prevB := match revPref with | [] => 1 | (_, _, bp) :: _ => bp
    modelRevEval β revPref ((1 + β) * max cur (max ak (max prevB bk1)))

private theorem modelRevEval_mono {β : ℝ} (hβ : 0 ≤ 1 + β) :
    ∀ (rev : List (Quant × ℝ × ℝ)) {u₁ u₂ : ℝ}, u₁ ≤ u₂ →
      modelRevEval β rev u₁ ≤ modelRevEval β rev u₂
  | [], _, _, h => h
  | (_, _, _) :: revPref, _, _, h =>
    modelRevEval_mono hβ revPref (mul_le_mul_of_nonneg_left (max_le_max h le_rfl) hβ)

/-- Constructive, postulate-free canonical model of `GenTimeSpaceSystem β` for every `β ≥ 1`. -/
noncomputable def canonicalGenTimeSpaceSystem (β : ℝ) (hβ : 1 ≤ β) : GenTimeSpaceSystem β where
  Class := ℝ → ℝ
  sub := fun C₁ C₂ => ∀ s : ℝ, 1 ≤ s → C₁ s ≤ C₂ s
  sub_refl := fun _ _ _ => le_rfl
  sub_trans := fun h₁ h₂ s hs => le_trans (h₁ s hs) (h₂ s hs)
  hβ := hβ
  dtisp := fun a b s => max a (max b 0) * s
  icClass := fun blocks d e s => modelRevEval β blocks.reverse (max d (max e 0)) * s
  ntime := fun a s => (1 + β) * max a 1 * s
  icClass_nil := fun _ _ => rfl
  dtisp_sub_ntime := fun {a b} ha hba s hs => by
    have hmax : max a (max b 0) = a := max_eq_left (max_le hba (by linarith))
    have ha1 : max a 1 = a := max_eq_left ha
    rw [hmax, ha1]
    have has : 0 ≤ a * s := mul_nonneg (by linarith) (by linarith)
    nlinarith
  pad_dtisp := fun {a₁ b₁ a₂ b₂ r} hr hsub s hs => by
    dsimp only at hsub ⊢
    have hr0 : 0 ≤ r := by linarith
    have hm : ∀ u v : ℝ, max (r * u) (max (r * v) 0) = r * max u (max v 0) := fun u v => by
      have h1 : max (r * v) 0 = r * max v 0 := by simpa using (mul_max_of_nonneg v 0 hr0).symm
      rw [h1, ← mul_max_of_nonneg u (max v 0) hr0]
    rw [hm a₁ b₁, hm a₂ b₂, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hsub s hs) hr0
  pad_ntime_to_dtisp := fun {c ε r} hr hsub s hs => by
    have h1 := hsub 1 le_rfl
    simp only [max_self, mul_one] at h1
    have hr1 : max r 1 = r := max_eq_left hr
    have hcr : max (c * r) (max (ε * r) 0) = max c (max ε 0) * r := by
      have hr0 : 0 ≤ r := by linarith
      have hm1 : max (ε * r) 0 = max ε 0 * r := by
        simpa [mul_comm] using (mul_max_of_nonneg ε 0 hr0).symm
      have hm2 : max (c * r) (max ε 0 * r) = max c (max ε 0) * r := by
        simpa [mul_comm] using (mul_max_of_nonneg c (max ε 0) hr0).symm
      rw [hm1, hm2]
    rw [hr1, hcr]
    have hrs : 0 ≤ r * s := by nlinarith
    nlinarith
  speedup_rule0 := fun q₁ {d e x} he hx hxd s hs => by
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, modelRevEval]
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    set u := max (d - β * x) (max e 0)
    set m1 := (1 + β) * max u (max 0 (max (max (x + e) 1) (max e 1)))
    have hm1_ge : (1 + β) * max (d - β * x) (x + e) ≤ m1 := by
      dsimp [m1]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      exact max_le (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hd_le : max d (max e 0) ≤ (1 + β) * max (d - β * x) (x + e) := by
      have hd1 : d ≤ (1 + β) * max (d - β * x) (x + e) := by
        by_cases hcmp : d - β * x ≤ x + e
        · rw [max_eq_right hcmp]; nlinarith
        · rw [max_eq_left (le_of_not_ge hcmp)]; nlinarith
      have he1 : max e 0 ≤ (1 + β) * max (d - β * x) (x + e) := by
        have hxe : max e 0 ≤ x + e := max_le (by linarith) (by linarith)
        have h2 := le_trans hxe (le_max_right (d - β * x) (x + e))
        have hpos : 0 ≤ max (d - β * x) (x + e) := le_trans (by linarith) (le_max_right _ _)
        nlinarith
      exact max_le hd1 he1
    have hm1_le : m1 ≤ (1 + β) * max m1 (max (x + e) (max 1 (max (x + e) 1))) := by
      have hpos : 0 ≤ max m1 (max (x + e) (max 1 (max (x + e) 1))) :=
        le_trans zero_le_one
          (le_trans (le_max_left 1 _) (le_trans (le_max_right (x + e) _) (le_max_right m1 _)))
      have h1 := le_max_left m1 (max (x + e) (max 1 (max (x + e) 1)))
      nlinarith
    exact le_trans hd_le (le_trans hm1_ge hm1_le)
  speedup_rule1 := fun pref qk {ak bk1 d e x} he hx hxd s hs => by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, modelRevEval]
    refine mul_le_mul_of_nonneg_right (modelRevEval_mono (by linarith) pref.reverse ?_)
      (by linarith)
    set pB : ℝ := match pref.reverse with | [] => 1 | (_, _, bp) :: _ => bp
    set u := max (d - β * x) (max e 0)
    set m1 := (1 + β) * max u (max 0 (max (max (x + e) bk1) (max e bk1)))
    have hm1_ge : max d (max e 0) ≤ m1 := by
      dsimp [m1]
      have hsub : max (d - β * x) (x + e) ≤ max u (max 0 (max (max (x + e) bk1) (max e bk1))) :=
        max_le (le_trans (le_max_left _ _) (le_max_left _ _))
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
      have hle : (1 + β) * max (d - β * x) (x + e) ≤ m1 :=
        mul_le_mul_of_nonneg_left hsub (by linarith)
      have hd1 : d ≤ (1 + β) * max (d - β * x) (x + e) := by
        by_cases hcmp : d - β * x ≤ x + e
        · rw [max_eq_right hcmp]; nlinarith
        · rw [max_eq_left (le_of_not_ge hcmp)]; nlinarith
      have he1 : max e 0 ≤ (1 + β) * max (d - β * x) (x + e) := by
        have hxe : max e 0 ≤ x + e := max_le (by linarith) (by linarith)
        have h2 := le_trans hxe (le_max_right (d - β * x) (x + e))
        have hpos : 0 ≤ max (d - β * x) (x + e) := le_trans (by linarith) (le_max_right _ _)
        nlinarith
      exact le_trans (max_le hd1 he1) hle
    exact mul_le_mul_of_nonneg_left
      (max_le_max hm1_ge (max_le_max (le_max_left _ _) (max_le_max le_rfl (le_max_right _ _))))
      (by linarith)
  speedup_rule2 := fun pref qk {ak bk1 d e x} he hx hxd s hs => by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, modelRevEval]
    refine mul_le_mul_of_nonneg_right (modelRevEval_mono (by linarith) pref.reverse ?_)
      (by linarith)
    set u := max (d - β * x) (max e 0)
    set m1 := (1 + β) * max u (max 0 (max (max (x + e) bk1) (max e bk1)))
    set m2 := (1 + β) * max m1 (max (x + e) (max bk1 (max (x + e) bk1)))
    have hm1_ge : max d (max e 0) ≤ m1 := by
      dsimp [m1]
      have hsub : max (d - β * x) (x + e) ≤ max u (max 0 (max (max (x + e) bk1) (max e bk1))) :=
        max_le (le_trans (le_max_left _ _) (le_max_left _ _))
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
      have hle : (1 + β) * max (d - β * x) (x + e) ≤ m1 :=
        mul_le_mul_of_nonneg_left hsub (by linarith)
      have hd1 : d ≤ (1 + β) * max (d - β * x) (x + e) := by
        by_cases hcmp : d - β * x ≤ x + e
        · rw [max_eq_right hcmp]; nlinarith
        · rw [max_eq_left (le_of_not_ge hcmp)]; nlinarith
      have he1 : max e 0 ≤ (1 + β) * max (d - β * x) (x + e) := by
        have hxe : max e 0 ≤ x + e := max_le (by linarith) (by linarith)
        have h2 := le_trans hxe (le_max_right (d - β * x) (x + e))
        have hpos : 0 ≤ max (d - β * x) (x + e) := le_trans (by linarith) (le_max_right _ _)
        nlinarith
      exact le_trans (max_le hd1 he1) hle
    have hm2_ge : m1 ≤ m2 := by
      dsimp [m2]
      have hm1_nn : 0 ≤ m1 := le_trans (le_trans (le_max_right e 0) (le_max_right d _)) hm1_ge
      have h1 := le_max_left m1 (max (x + e) (max bk1 (max (x + e) bk1)))
      nlinarith
    exact mul_le_mul_of_nonneg_left
      (max_le_max (le_trans hm1_ge hm2_ge) le_rfl) (by linarith)
  slowdown_rule := fun {c ε} pref qk {ak bk1 d e} hε hed hsat s hs => by
    have hsat1 := hsat 1 le_rfl
    simp only [max_self, mul_one] at hsat1
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
    refine mul_le_mul_of_nonneg_right (modelRevEval_mono (by linarith) pref.reverse ?_)
      (by linarith)
    set pB : ℝ := match pref.reverse with | [] => 1 | (_, _, bp) :: _ => bp
    have hpB_eq : prevInputBound pref = pB := prevInputBound_eq_revHead pref
    let M := max d (max ak (max (prevInputBound pref) bk1))
    have hprev_eq : max (max d (max e 0)) (max ak (max pB bk1)) ≤ max M 0 := by
      rw [← hpB_eq]
      exact max_le (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
        (max_le (le_trans hed (le_trans (le_max_left _ _) (le_max_left _ _))) (le_max_right _ _)))
        (le_trans (le_max_right _ _) (le_max_left _ _))
    have hmax_c : max (c * M) (max (ε * M) 0) ≥ max c (max ε 0) * max M 0 := by
      by_cases hM0 : 0 ≤ M
      · rw [max_eq_left hM0]
        have hm1 : max (ε * M) 0 = max ε 0 * M := by
          simpa [mul_comm] using (mul_max_of_nonneg ε 0 hM0).symm
        have hm2 : max (c * M) (max ε 0 * M) = max c (max ε 0) * M := by
          simpa [mul_comm] using (mul_max_of_nonneg c (max ε 0) hM0).symm
        rw [hm1, hm2]
      · rw [max_eq_right (le_of_not_ge hM0), mul_zero]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h1 : (1 + β) * max (max d (max e 0)) (max ak (max pB bk1)) ≤ (1 + β) * max M 0 :=
      mul_le_mul_of_nonneg_left hprev_eq (by linarith)
    have h2 : (1 + β) * max M 0 ≤ max c (max ε 0) * max M 0 :=
      mul_le_mul_of_nonneg_right hsat1 (le_max_right _ _)
    exact le_trans h1 (le_trans h2 hmax_c)
  ntime_hierarchy := fun {r s} hs hsr hsub => by
    have h1 := hsub 1 le_rfl
    rw [max_eq_left (by linarith : 1 ≤ r), max_eq_left hs] at h1
    nlinarith

/-- In `canonicalGenTimeSpaceSystem β`, `ntime 1 ⊆ dtisp c 0` holds iff `1 + β ≤ c`. -/
theorem canonical_sat_dtisp_iff {β : ℝ} (hβ : 1 ≤ β) (c : ℝ) :
    (canonicalGenTimeSpaceSystem β hβ).sub
      ((canonicalGenTimeSpaceSystem β hβ).ntime 1)
      ((canonicalGenTimeSpaceSystem β hβ).dtisp c 0) ↔ 1 + β ≤ c := by
  dsimp [canonicalGenTimeSpaceSystem]
  constructor
  · intro h
    have h1 := h 1 le_rfl
    simp only [max_self, mul_one] at h1
    by_cases hc0 : 0 ≤ c
    · rwa [max_eq_left hc0] at h1
    · rw [max_eq_right (le_of_not_ge hc0)] at h1; linarith
  · intro hc s hs
    simp only [max_self, mul_one, max_eq_left (by linarith : 0 ≤ c)]
    exact mul_le_mul_of_nonneg_right hc (by linarith)

/-! ## 5. Explicit Multi-Stage `2 cos(π / 7)` Lower Bound -/

/-- The cubic root `2 cos(π / 7) ≈ 1.8019377358...`. -/
@[expose] noncomputable def twoCosPiDivSeven : ℝ :=
  2 * Real.cos (Real.pi / 7)

/-- Exact minimal cubic satisfied by `2 cos(π / 7)`: `u ^ 3 - u ^ 2 - 2 * u + 1 = 0`. -/
theorem cubic_root_identity :
    twoCosPiDivSeven ^ 3 - twoCosPiDivSeven ^ 2 - 2 * twoCosPiDivSeven + 1 = 0 := by
  unfold twoCosPiDivSeven
  set θ := Real.pi / 7
  have hcos_eq : Real.cos (4 * θ) + Real.cos (3 * θ) = 0 := by
    rw [show 4 * θ = Real.pi - 3 * θ by dsimp [θ]; ring, Real.cos_pi_sub]; ring
  have hcos4 : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, Real.cos_two_mul]; ring
  rw [hcos4, Real.cos_three_mul] at hcos_eq
  have hfac : ((2 * Real.cos θ) + 2) *
      ((2 * Real.cos θ) ^ 3 - (2 * Real.cos θ) ^ 2 - 2 * (2 * Real.cos θ) + 1) =
      2 * (8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 +
        (4 * Real.cos θ ^ 3 - 3 * Real.cos θ)) := by ring
  rw [hcos_eq, mul_zero] at hfac
  have hgt : Real.sqrt 2 < 2 * Real.cos θ := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hcos := Real.strictAntiOn_cos
      (⟨by dsimp [θ]; linarith, by dsimp [θ]; linarith⟩ : θ ∈ Set.Icc 0 Real.pi)
      (⟨by linarith, by linarith⟩ : Real.pi / 4 ∈ Set.Icc 0 Real.pi) (by dsimp [θ]; linarith)
    rw [Real.cos_pi_div_four] at hcos
    linarith
  rcases mul_eq_zero.mp hfac with h0 | h0
  · linarith [Real.sqrt_nonneg 2]
  · exact h0

/-! ## 6. Linear Potential Function and Exact `c ≥ 1 + β` Barrier -/

private theorem dropLast_append_singleton {α : Type*} :
    ∀ (l : List α) (x : α), (l ++ [x]).dropLast = l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, x => congrArg (a :: ·) (dropLast_append_singleton (b :: rest) x)

private theorem rev_eq_last_cons_dropLast {α : Type*} :
    ∀ (l : List α) (hpos : 0 < l.length),
      l.reverse = l[l.length - 1]'(Nat.sub_lt hpos zero_lt_one) :: l.dropLast.reverse
  | [], hpos => by simp at hpos
  | [_], _ => rfl
  | a :: b :: rest, _ => by
    have ih := rev_eq_last_cons_dropLast (b :: rest) (by simp)
    simp only [List.dropLast, List.reverse_cons] at ih ⊢
    rw [ih, List.cons_append]; rfl

/-- Linear potential on `ATState`: `dtsTime + β * ∑_{j=0}^{k-2} b_{j+1}`. -/
@[expose] noncomputable def atPotential (β : ℝ) (st : ATState) : ℝ :=
  st.dtsTime + β * (st.blocks.dropLast.map (fun blk => blk.2.2)).sum

private def blocksBNonneg (st : ATState) : Prop :=
  ∀ blk ∈ st.blocks, 0 ≤ blk.2.2

private theorem blocksBNonneg_step {β c : ℝ} {step : ATStep} {st st' : ATState}
    (hnn : blocksBNonneg st) (he : st.dtsSpace = 0)
    (hexec : execATStep β c 0 step st = some st') : blocksBNonneg st' := by
  rcases st with ⟨b, d, e⟩; dsimp at he; subst he
  cases step with
  | speedup0 q x =>
    dsimp only [execATStep] at hexec
    cases b with
    | cons _ _ => simp at hexec
    | nil =>
      split_ifs at hexec; rcases Option.some.inj hexec with rfl
      intro blk hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> exact le_trans zero_le_one (le_max_right _ _)
  | speedup1 x =>
    dsimp only [execATStep] at hexec
    rcases hrev : b.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec; split_ifs at hexec; rcases Option.some.inj hexec with rfl
      have hbl : b = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      intro blk hm; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hp | rfl | rfl
      · exact hnn blk (by rw [hbl]; simp [hp])
      · exact le_trans (hnn (qk, ak, bk1) (by rw [hbl]; simp)) (le_max_right _ _)
      · exact le_max_left 0 bk1
  | speedup2 x =>
    dsimp only [execATStep] at hexec
    rcases hrev : b.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec; split_ifs at hexec; rcases Option.some.inj hexec with rfl
      have hbl : b = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      intro blk hm; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hp | rfl | rfl | rfl
      · exact hnn blk (by rw [hbl]; simp [hp])
      · exact hnn (qk, ak, bk1) (by rw [hbl]; simp)
      · exact le_trans (hnn (qk, ak, bk1) (by rw [hbl]; simp)) (le_max_right _ _)
      · exact le_max_left 0 bk1
  | slowdown =>
    dsimp only [execATStep] at hexec
    rcases hrev : b.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec; split_ifs at hexec; rcases Option.some.inj hexec with rfl
      have hbl : b = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      intro blk hm; exact hnn blk (by rw [hbl]; simp [hm])

private theorem execATStep_pos_zero {β c : ℝ} (hc : 1 ≤ c) (step : ATStep) (st₀ st₁ : ATState)
    (hd0 : 0 < st₀.dtsTime) (he0 : st₀.dtsSpace = 0)
    (hstep : execATStep β c 0 step st₀ = some st₁) :
    0 < st₁.dtsTime ∧ st₁.dtsSpace = 0 := by
  rcases st₀ with ⟨b₀, d₀, e₀⟩; dsimp at hd0 he0; subst he0
  cases step with
  | speedup0 q x =>
    dsimp only [execATStep] at hstep
    cases b₀ with
    | cons _ _ => simp at hstep
    | nil =>
      split_ifs at hstep with hcond; rcases Option.some.inj hstep with rfl
      exact ⟨by dsimp; linarith [hcond.2.2], rfl⟩
  | speedup1 x =>
    dsimp only [execATStep] at hstep
    rcases hrev : b₀.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hstep
    · simp only [hrev] at hstep
      split_ifs at hstep with hcond; rcases Option.some.inj hstep with rfl
      exact ⟨by dsimp; linarith [hcond.2.2], rfl⟩
  | speedup2 x =>
    dsimp only [execATStep] at hstep
    rcases hrev : b₀.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hstep
    · simp only [hrev] at hstep
      split_ifs at hstep with hcond; rcases Option.some.inj hstep with rfl
      exact ⟨by dsimp; linarith [hcond.2.2], rfl⟩
  | slowdown =>
    dsimp only [execATStep] at hstep
    rcases hrev : b₀.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hstep
    · simp only [hrev] at hstep; split_ifs at hstep; rcases Option.some.inj hstep with rfl
      exact ⟨mul_pos (by linarith) (lt_of_lt_of_le hd0 (le_max_left _ _)), zero_mul _⟩

private theorem atPotential_step_le_and_final_lt {β c : ℝ} (hβ : 1 ≤ β) (hbar : 1 + β ≤ c)
    {step : ATStep} {st st' : ATState}
    (hnn : blocksBNonneg st) (hd : 0 < st.dtsTime) (he : st.dtsSpace = 0)
    (hexec : execATStep β c 0 step st = some st') :
    atPotential β st ≤ atPotential β st' ∧
      (st'.blocks = [] → atPotential β st < atPotential β st') := by
  rcases st with ⟨b, d, e⟩; dsimp at hd he; subst he
  cases step with
  | speedup0 q x =>
    dsimp only [execATStep] at hexec
    cases b with
    | cons _ _ => simp at hexec
    | nil =>
      split_ifs at hexec; rcases Option.some.inj hexec with rfl
      refine ⟨?_, fun h => by simp at h⟩
      unfold atPotential
      simp only [List.dropLast, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, mul_zero]
      nlinarith [le_max_left x 1]
  | speedup1 x =>
    dsimp only [execATStep] at hexec
    rcases hrev : b.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec; split_ifs at hexec; rcases Option.some.inj hexec with rfl
      refine ⟨?_, fun h => by simp at h⟩
      have hbl : b = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      unfold atPotential; dsimp only
      rw [hbl, dropLast_append_singleton]
      have hdl2 : (revPref.reverse ++
          [(qk, max ak (x + 0), max (x + 0) bk1), (qk.dual, 0, max 0 bk1)]).dropLast =
          revPref.reverse ++ [(qk, max ak (x + 0), max (x + 0) bk1)] := by
        have hassoc : revPref.reverse ++
            [(qk, max ak (x + 0), max (x + 0) bk1), (qk.dual, 0, max 0 bk1)] =
            (revPref.reverse ++ [(qk, max ak (x + 0), max (x + 0) bk1)]) ++
              [(qk.dual, 0, max 0 bk1)] := by simp
        rw [hassoc, dropLast_append_singleton]
      rw [hdl2]
      simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, add_zero]
      nlinarith [le_max_left x bk1]
  | speedup2 x =>
    dsimp only [execATStep] at hexec
    rcases hrev : b.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec; split_ifs at hexec; rcases Option.some.inj hexec with rfl
      refine ⟨?_, fun h => by simp at h⟩
      have hbl : b = revPref.reverse ++ [(qk, ak, bk1)] := by
        simpa using congrArg List.reverse hrev
      have hbk_nn : 0 ≤ bk1 := hnn (qk, ak, bk1) (by rw [hbl]; simp)
      unfold atPotential; dsimp only
      rw [hbl, dropLast_append_singleton]
      have hdl2 : (revPref.reverse ++
          [(qk, ak, bk1), (qk.dual, x + 0, max (x + 0) bk1), (qk, 0, max 0 bk1)]).dropLast =
          revPref.reverse ++ [(qk, ak, bk1), (qk.dual, x + 0, max (x + 0) bk1)] := by
        have hassoc : revPref.reverse ++
            [(qk, ak, bk1), (qk.dual, x + 0, max (x + 0) bk1), (qk, 0, max 0 bk1)] =
            (revPref.reverse ++ [(qk, ak, bk1), (qk.dual, x + 0, max (x + 0) bk1)]) ++
              [(qk, 0, max 0 bk1)] := by simp
        rw [hassoc, dropLast_append_singleton]
      rw [hdl2]
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, add_zero]
      nlinarith [le_max_left x bk1]
  | slowdown =>
    dsimp only [execATStep] at hexec
    rcases hrev : b.reverse with _ | ⟨⟨qk, ak, bk1⟩, revPref⟩
    · simp [hrev] at hexec
    · simp only [hrev] at hexec; split_ifs at hexec; rcases Option.some.inj hexec with rfl
      let pref := revPref.reverse
      let M := max d (max ak (max (prevInputBound pref) bk1))
      have hbl : b = pref ++ [(qk, ak, bk1)] := by simpa [pref] using congrArg List.reverse hrev
      have hM_ge_d : d ≤ M := le_max_left _ _
      have hM_ge_prev : prevInputBound pref ≤ M :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hM_pos : 0 < M := lt_of_lt_of_le hd hM_ge_d
      have hcM_ge : (1 + β) * M ≤ c * M := mul_le_mul_of_nonneg_right hbar (le_of_lt hM_pos)
      by_cases hp_nil : pref = []
      · unfold atPotential; dsimp only
        rw [hbl, dropLast_append_singleton, hp_nil]
        have hrev_nil : revPref.reverse = [] := hp_nil
        rw [hrev_nil]
        simp only [List.dropLast, List.map_nil, List.sum_nil, mul_zero, add_zero]
        have hstrict : d < c * M := by nlinarith
        dsimp [M] at hstrict
        rw [hp_nil] at hstrict
        exact ⟨le_of_lt hstrict, fun _ => hstrict⟩
      · have hpos_p : 0 < pref.length := List.length_pos_of_ne_nil hp_nil
        rcases hlast_p : pref[pref.length - 1] with ⟨qp, ap, bp⟩
        have hprev_eq : prevInputBound pref = bp := by
          rw [prevInputBound_eq_revHead, rev_eq_last_cons_dropLast pref hpos_p, hlast_p]
        have hpref_split : pref = pref.dropLast ++ [(qp, ap, bp)] := by
          have h := congrArg List.reverse (rev_eq_last_cons_dropLast pref hpos_p)
          rw [hlast_p] at h; simpa using h
        unfold atPotential; dsimp only
        rw [hbl, dropLast_append_singleton]
        conv_lhs => rw [hpref_split]
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        rw [hprev_eq] at hM_ge_prev
        exact ⟨by nlinarith, fun hnil => absurd hnil hp_nil⟩

private theorem atPotential_script_strict {β c : ℝ} (hβ : 1 ≤ β) (hbar : 1 + β ≤ c) :
    ∀ (script : List ATStep) (st st_end : ATState),
      script ≠ [] → blocksBNonneg st → 0 < st.dtsTime → st.dtsSpace = 0 →
      st_end.blocks = [] →
      execATScript β c 0 script st = some st_end →
      atPotential β st < atPotential β st_end
  | [], _, _, hne, _, _, _, _, _ => absurd rfl hne
  | [step], st, st_end, _, hnn, hd, he, hnil_end, hexec => by
    simp only [execATScript] at hexec
    cases h1 : execATStep β c 0 step st with
    | none => simp [h1] at hexec
    | some mid =>
      rw [h1] at hexec; simp only [Option.some.injEq] at hexec; subst hexec
      exact (atPotential_step_le_and_final_lt hβ hbar hnn hd he h1).2 hnil_end
  | step :: s₂ :: rest, st, st_end, _, hnn, hd, he, hnil_end, hexec => by
    rw [execATScript] at hexec
    cases h1 : execATStep β c 0 step st with
    | none => simp [h1] at hexec
    | some mid =>
      rw [h1] at hexec; dsimp only at hexec
      obtain ⟨hd_mid, he_mid⟩ := execATStep_pos_zero (by linarith) step st mid hd he h1
      have hstep_le := (atPotential_step_le_and_final_lt hβ hbar hnn hd he h1).1
      have hrest_lt := atPotential_script_strict hβ hbar (s₂ :: rest) mid st_end
        (List.cons_ne_nil _ _) (blocksBNonneg_step hnn he h1) hd_mid he_mid hnil_end hexec
      exact lt_of_le_of_lt hstep_le hrest_lt

/-- **Generalized `1 + β` Alternation-Trading Barrier**:
For every `1 ≤ β` and `c ≥ 1 + β`, no zero-space alternation-trading proof `ATProof β c 0`
of any length can exist. -/
theorem generalized_barrier_one_add_beta {β c : ℝ} (hβ : 1 ≤ β) (hbar : 1 + β ≤ c) :
    IsEmpty (ATProof β c 0) :=
  ⟨fun P => by
    have ha₀_pos : 0 < P.a₀ :=
      lt_of_lt_of_le zero_lt_one (le_trans P.ha₁_ge_one (le_of_lt P.ha₁_lt_a₀))
    have hrun : execATScript β c 0 P.script ⟨[], P.a₀, 0⟩ = some ⟨[], P.a₁, 0⟩ := by
      simpa [zero_div, zero_mul] using P.valid_run
    have hne : P.script ≠ [] := by
      intro hnil; rw [hnil] at hrun
      simp only [execATScript, Option.some.injEq, ATState.mk.injEq] at hrun
      linarith [P.ha₁_lt_a₀, hrun.2.1]
    have hlt := atPotential_script_strict hβ hbar P.script ⟨[], P.a₀, 0⟩ ⟨[], P.a₁, 0⟩
      hne (fun _ h => by simp at h) ha₀_pos rfl rfl hrun
    unfold atPotential at hlt
    simp only [List.dropLast, List.map_nil, List.sum_nil, mul_zero, add_zero] at hlt
    linarith [P.ha₁_lt_a₀]⟩

/-- **Quadratic Time-Space Barrier**: at `β = 1`, no alternation-trading proof can reach `c ≥ 2`,
and `canonicalGenTimeSpaceSystem 1 le_rfl` satisfies `ntime 1 ⊆ dtisp c 0` for all `c ≥ 2`. -/
theorem quadratic_barrier {c : ℝ} (hc2 : 2 ≤ c) :
    IsEmpty (ATProof 1 c 0) ∧
    (canonicalGenTimeSpaceSystem 1 le_rfl).sub
      ((canonicalGenTimeSpaceSystem 1 le_rfl).ntime 1)
      ((canonicalGenTimeSpaceSystem 1 le_rfl).dtisp c 0) :=
  ⟨generalized_barrier_one_add_beta (β := 1) le_rfl (by linarith),
   (canonical_sat_dtisp_iff le_rfl c).mpr (by linarith)⟩

end CslibFrontier.Complexity.AlternationTrading
