/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module

public import CslibFrontier.Computability.Streaming.Basic
public import CslibFrontier.Computability.Streaming.MultiPass
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad

import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Cyclic Multiparty Blackboard Protocols, Multi-Pass Streaming Simulation, and Pointer/Set Chasing

This module formalizes pass-indexed multi-pass token streaming algorithms (lifting
`Cslib.Streaming.Algorithm` and `Cslib.Streaming.MultiPass`), number-in-hand cyclic `(k, r)`-round
multiparty blackboard protocols (`CyclicProtocol`, `RandomizedCyclicProtocol`), the exact
`r * k * ⌈log₂ |S|⌉`-bit simulation of `r`-pass streaming algorithms on `k`-player partitioned
streams, and the multiparty pointer-chasing (`pointerChasing`) and set-chasing intersection
(`setChasingIntersect`) problems with their round-sharpness upper bounds and base-case
communication lower bounds.

## Main definitions

* `CslibFrontier.Communication.MultiPassTokenStreamingAlgorithm`,
  `CslibFrontier.Communication.RandomizedMultiPassStreaming`: deterministic and public-coin
  randomized pass-indexed multi-pass streaming algorithms.
* `CslibFrontier.Communication.CyclicProtocol`,
  `CslibFrontier.Communication.RandomizedCyclicProtocol`: deterministic and public-coin randomized
  `(k, r)`-round cyclic multiparty communication protocols in the blackboard model.
* `CslibFrontier.Communication.concatChunks`,
  `CslibFrontier.Communication.MultiPassTokenStreamingAlgorithm.toCyclicProtocol`,
  `CslibFrontier.Communication.RandomizedMultiPassStreaming.toRandomizedCyclicProtocol`: simulation
  of multi-pass streaming algorithms by cyclic multiparty protocols.
* `CslibFrontier.Communication.pointerChasing`, `CslibFrontier.Communication.setLift`,
  `CslibFrontier.Communication.setChasing`, `CslibFrontier.Communication.setChasingLeft`,
  `CslibFrontier.Communication.setChasingRight`, `CslibFrontier.Communication.setChasingIntersect`:
  multiparty pointer chasing and set-chasing intersection.

## Main results

* `CslibFrontier.Communication.MultiPassTokenStreamingAlgorithm.run_toCyclicProtocol`,
  `CslibFrontier.Communication.RandomizedMultiPassStreaming`
  (`computesWithError_toRandomizedCyclicProtocol`): output and error preservation for
  multi-pass streaming simulation in the cyclic blackboard model.
* `CslibFrontier.Communication.exists_cyclicProtocol_pointerChasing_k_rounds`,
  `CslibFrontier.Communication.exists_cyclicProtocol_pointerChasing_one`,
  `CslibFrontier.Communication.exists_cyclicProtocol_setChasingIntersect_two_rounds`:
  deterministic round-sharpness upper bounds for pointer chasing and set-chasing intersection.
* `CslibFrontier.Communication.two_player_pointerChasing_card_le`,
  `CslibFrontier.Communication.not_computesWithError_setChasingIntersect_one`,
  `CslibFrontier.Communication.one_le_cost_of_computesWithError_setChasingIntersect`:
  base-case communication lower bounds.
-/

public section

open scoped ENNReal

namespace CslibFrontier.Communication

/-! ### Finite Bit-String Encodings -/

section BitEncoding

private noncomputable def finBitsOfFintype {S : Type*} [Fintype S] (s : S) :
    Fin (Nat.clog 2 (Fintype.card S)) → Bool :=
  let e := Fintype.equivFin S
  let b := Nat.clog 2 (Fintype.card S)
  (Cslib.BitString.equivFin b).symm
    ⟨(e s).1, lt_of_lt_of_le (e s).2 (Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card S))⟩

private noncomputable def fintypeOfFinBits {S : Type*} [Fintype S] [Nonempty S]
    (bits : Fin (Nat.clog 2 (Fintype.card S)) → Bool) : S :=
  let e := Fintype.equivFin S
  let idx := (Cslib.BitString.equivFin (Nat.clog 2 (Fintype.card S)) bits).1
  if h : idx < Fintype.card S then e.symm ⟨idx, h⟩ else Classical.arbitrary S

private lemma fintypeOfFinBits_finBitsOfFintype {S : Type*} [Fintype S] [Nonempty S] (s : S) :
    fintypeOfFinBits (finBitsOfFintype s) = s := by
  simp only [fintypeOfFinBits, finBitsOfFintype, Equiv.apply_symm_apply, Fin.is_lt, ↓reduceDIte,
    Fin.eta, Equiv.symm_apply_apply]

private noncomputable def encodeFin {n : ℕ} (u : Fin n) : Fin (Nat.clog 2 n) → Bool :=
  (Cslib.BitString.equivFin (Nat.clog 2 n)).symm
    ⟨u.1, lt_of_lt_of_le u.2 (Nat.le_pow_clog (by decide : 1 < 2) n)⟩

private noncomputable def decodeFin {n : ℕ} (hn : 0 < n) (bits : Fin (Nat.clog 2 n) → Bool) :
    Fin n :=
  let v := (Cslib.BitString.equivFin (Nat.clog 2 n) bits).1
  if hv : v < n then ⟨v, hv⟩ else ⟨0, hn⟩

private lemma decodeFin_encodeFin {n : ℕ} (hn : 0 < n) (u : Fin n) :
    decodeFin hn (encodeFin u) = u := by
  simp [decodeFin, encodeFin, u.2]

end BitEncoding

/-! ### Pass-Indexed Multi-Pass Token Streaming Algorithms -/

section MultiPassStreaming

/-- A deterministic `p`-pass token streaming algorithm over token alphabet `Token` with state
space `S` and output space `Z`, allowing pass-dependent transitions `step : Fin p → S → Token → S`.
-/
@[ext] structure MultiPassTokenStreamingAlgorithm (Token Z S : Type*) (p : ℕ) where
  /-- Initial memory state in `S`. -/
  initState : S
  /-- Single-token state transition function during pass `t : Fin p`. -/
  step : Fin p → S → Token → S
  /-- Final output map from the terminal memory state in `S` to `Z`. -/
  output : S → Z

variable {Token Z S Ω : Type*} {p : ℕ}

/-- State after executing pass `t : Fin p` of `A` on token stream `σ` from starting state `s`. -/
def MultiPassTokenStreamingAlgorithm.runPass
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (t : Fin p) (s : S)
    (σ : List Token) : S :=
  σ.foldl (A.step t) s

/-- Evaluating a pass on the empty stream leaves the state unchanged. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.runPass_nil
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (t : Fin p) (s : S) :
    A.runPass t s [] = s := by exact id rfl

/-- Evaluating a pass on `a :: σ` applies `A.step t s a` and continues on `σ`. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.runPass_cons
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (t : Fin p) (s : S) (a : Token)
    (σ : List Token) :
    A.runPass t s (a :: σ) = A.runPass t (A.step t s a) σ := by exact id rfl

/-- Evaluating a pass on a concatenated stream `xs ++ ys` runs `xs` then `ys`. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.runPass_append
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (t : Fin p) (s : S)
    (xs ys : List Token) :
    A.runPass t s (xs ++ ys) = A.runPass t (A.runPass t s xs) ys :=
  List.foldl_append

/-- State after executing the first `m ≤ p` passes of `A` on token stream `σ`. -/
def MultiPassTokenStreamingAlgorithm.runFirstPasses
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (σ : List Token) :
    ∀ (m : ℕ), m ≤ p → S
  | 0, _ => A.initState
  | m + 1, hm => A.runPass ⟨m, hm⟩ (A.runFirstPasses σ m (Nat.le_of_succ_le hm)) σ

/-- Zero passes leave `A` at `A.initState`. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.runFirstPasses_zero
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (σ : List Token) (h0 : 0 ≤ p) :
    A.runFirstPasses σ 0 h0 = A.initState := by exact id rfl

/-- Pass recursion for `MultiPassTokenStreamingAlgorithm.runFirstPasses`. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.runFirstPasses_succ
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (σ : List Token) (m : ℕ) (hm : m + 1 ≤ p) :
    A.runFirstPasses σ (m + 1) hm =
      A.runPass ⟨m, hm⟩ (A.runFirstPasses σ m (Nat.le_of_succ_le hm)) σ := by exact id rfl

private lemma runFirstPasses_congr
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (σ : List Token)
    {a b : ℕ} (ha : a ≤ p) (hb : b ≤ p) (hab : a = b) :
    A.runFirstPasses σ a ha = A.runFirstPasses σ b hb := by
  subst hab; rfl

/-- Terminal memory state after all `p` passes of `A` on token stream `σ`. -/
def MultiPassTokenStreamingAlgorithm.runPasses
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (σ : List Token) : S :=
  A.runFirstPasses σ p le_rfl

/-- Final output of `A` after `p` passes over token stream `σ`. -/
def MultiPassTokenStreamingAlgorithm.runStream
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) (σ : List Token) : Z :=
  A.output (A.runPasses σ)

/-- Lift a single-pass `Cslib.Streaming.Algorithm S Token Z` to a `1`-pass
`MultiPassTokenStreamingAlgorithm Token Z S 1`. -/
def MultiPassTokenStreamingAlgorithm.ofStreamingAlgorithm
    (A : Cslib.Streaming.Algorithm S Token Z) :
    MultiPassTokenStreamingAlgorithm Token Z S 1 where
  initState := A.init
  step _ := A.update
  output := A.output

/-- `ofStreamingAlgorithm` preserves `run` on every stream `σ`. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.runStream_ofStreamingAlgorithm
    (A : Cslib.Streaming.Algorithm S Token Z) (σ : List Token) :
    (ofStreamingAlgorithm A).runStream σ = A.run σ := by exact id rfl

/-- Lift a time-homogeneous `Cslib.Streaming.MultiPass S Token Z` to a `p`-pass
`MultiPassTokenStreamingAlgorithm Token Z S p`. -/
def MultiPassTokenStreamingAlgorithm.ofStreamingMultiPass
    (A : Cslib.Streaming.MultiPass S Token Z) (p : ℕ) :
    MultiPassTokenStreamingAlgorithm Token Z S p where
  initState := A.init
  step _ := A.update
  output := A.output

/-- When `A.endPass = id`, `ofStreamingMultiPass A p` agrees with `A.run p` on every stream. -/
theorem MultiPassTokenStreamingAlgorithm.runStream_ofStreamingMultiPass
    (A : Cslib.Streaming.MultiPass S Token Z) (hend : A.endPass = id) (p : ℕ) (σ : List Token) :
    (ofStreamingMultiPass A p).runStream σ = A.run p σ := by
  suffices ∀ (m : ℕ) (hm : m ≤ p),
      (ofStreamingMultiPass A p).runFirstPasses σ m hm = A.passes σ m by
    exact congr_arg A.output (this p le_rfl)
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [runFirstPasses_succ, ih (Nat.le_of_succ_le hm), A.passes_succ,
      Cslib.Streaming.MultiPass.pass, hend, id_eq]
    simp [runPass, ofStreamingMultiPass, Cslib.Streaming.Algorithm.stateFrom]

/-- A public-coin randomized `p`-pass token streaming algorithm over `Token` with state space `S`,
output space `Z`, and random seed distribution `dist : PMF Ω`. -/
@[ext] structure RandomizedMultiPassStreaming (Token Z S : Type*) (p : ℕ) (Ω : Type*) where
  /-- Deterministic `p`-pass streaming algorithm executed for each random seed `ω : Ω`. -/
  alg : Ω → MultiPassTokenStreamingAlgorithm Token Z S p
  /-- Probability mass function over random seeds `Ω`. -/
  dist : PMF Ω

/-- Error probability of a randomized `p`-pass streaming algorithm `A` on stream `σ` for target
function `f`. -/
noncomputable def RandomizedMultiPassStreaming.errorProb
    (A : RandomizedMultiPassStreaming Token Z S p Ω) (f : List Token → Z)
    (σ : List Token) : ℝ≥0∞ :=
  A.dist.toOuterMeasure {ω | (A.alg ω).runStream σ ≠ f σ}

/-- A randomized `p`-pass streaming algorithm `A` computes `f` on streams satisfying `Valid` with
error probability at most `ε`. -/
def RandomizedMultiPassStreaming.ComputesWithErrorOn
    (A : RandomizedMultiPassStreaming Token Z S p Ω) (Valid : List Token → Prop)
    (f : List Token → Z) (ε : ℝ≥0∞) : Prop :=
  ∀ σ, Valid σ → A.errorProb f σ ≤ ε

/-- Pull back a randomized multi-pass streaming algorithm along a token map `φ : Token' → Token`.
-/
def RandomizedMultiPassStreaming.comapTokens {Token' : Type*}
    (A : RandomizedMultiPassStreaming Token Z S p Ω) (φ : Token' → Token) :
    RandomizedMultiPassStreaming Token' Z S p Ω where
  alg ω :=
    { initState := (A.alg ω).initState
      step := fun t s tok ↦ (A.alg ω).step t s (φ tok)
      output := (A.alg ω).output }
  dist := A.dist

/-- Error probability of `A.comapTokens φ` on `σ` equals the error probability of `A` on `σ.map φ`
whenever `f' σ = f (σ.map φ)`. -/
theorem RandomizedMultiPassStreaming.errorProb_comapTokens {Token' : Type*}
    (A : RandomizedMultiPassStreaming Token Z S p Ω) (φ : Token' → Token)
    {f : List Token → Z} {f' : List Token' → Z} {σ : List Token'}
    (hf : f' σ = f (σ.map φ)) :
    (A.comapTokens φ).errorProb f' σ = A.errorProb f (σ.map φ) := by
  have hpass : ∀ (ω : Ω) (m : ℕ) (hm : m ≤ p),
      ((A.comapTokens φ).alg ω).runFirstPasses σ m hm =
        (A.alg ω).runFirstPasses (σ.map φ) m hm := by
    intro ω m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [MultiPassTokenStreamingAlgorithm.runFirstPasses_succ,
        MultiPassTokenStreamingAlgorithm.runFirstPasses_succ, ih (Nat.le_of_succ_le hm)]
      simp only [MultiPassTokenStreamingAlgorithm.runPass, comapTokens]
      exact List.foldl_map.symm
  simp only [errorProb, MultiPassTokenStreamingAlgorithm.runStream,
    MultiPassTokenStreamingAlgorithm.runPasses, hpass _ p le_rfl, hf]
  rfl

/-- View a deterministic `MultiPassTokenStreamingAlgorithm` as a randomized one over `PUnit`. -/
noncomputable def MultiPassTokenStreamingAlgorithm.toRandomized
    (A : MultiPassTokenStreamingAlgorithm Token Z S p) :
    RandomizedMultiPassStreaming Token Z S p PUnit where
  alg _ := A
  dist := PMF.pure PUnit.unit

/-- A deterministic multi-pass algorithm computing `f` on `Valid` has error probability `0`. -/
theorem MultiPassTokenStreamingAlgorithm.computesWithErrorOn_zero
    {A : MultiPassTokenStreamingAlgorithm Token Z S p} {Valid : List Token → Prop}
    {f : List Token → Z} (hA : ∀ σ, Valid σ → A.runStream σ = f σ) :
    A.toRandomized.ComputesWithErrorOn Valid f 0 := by
  intro σ hσ
  simp [RandomizedMultiPassStreaming.errorProb, MultiPassTokenStreamingAlgorithm.toRandomized,
    hA σ hσ]

end MultiPassStreaming

/-! ### Cyclic `(k, r)`-Round Multiparty Blackboard Protocols -/

section CyclicProtocols

/-- Speaker index in `Fin k` at linear turn `t : ℕ` under cyclic order `0 → 1 → ⋯ → k - 1`. -/
def cyclicSpeaker (k : ℕ) [NeZero k] (t : ℕ) : Fin k :=
  ⟨t % k, Nat.mod_lt t (NeZero.pos k)⟩

/-- Underlying natural value of `cyclicSpeaker k t`. -/
@[simp] lemma val_cyclicSpeaker (k : ℕ) [NeZero k] (t : ℕ) :
    (cyclicSpeaker k t).1 = t % k := by exact id rfl

/-- The last player index `k - 1` in `Fin k` when `[NeZero k]`. -/
def lastPlayer (k : ℕ) [NeZero k] : Fin k :=
  ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩

/-- Underlying natural value of `lastPlayer k`. -/
@[simp] lemma val_lastPlayer (k : ℕ) [NeZero k] :
    (lastPlayer k).1 = k - 1 := by exact id rfl

/-- Total number of bits written before linear turn `m` given per-turn bit lengths `msgBits`. -/
def prefixBits {n : ℕ} (msgBits : Fin n → ℕ) (m : ℕ) : ℕ :=
  ∑ j : Fin n, if j.1 < m then msgBits j else 0

/-- Before turn `0`, zero bits have been written. -/
@[simp] lemma prefixBits_zero {n : ℕ} (msgBits : Fin n → ℕ) :
    prefixBits msgBits 0 = 0 := by
  simp [prefixBits]

/-- `prefixBits msgBits` is monotone in the turn index. -/
lemma prefixBits_mono {n : ℕ} (msgBits : Fin n → ℕ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    prefixBits msgBits m₁ ≤ prefixBits msgBits m₂ :=
  Finset.sum_le_sum fun _ _ ↦ by split_ifs <;> omega

/-- Advancing from turn `m` to turn `m + 1` adds `msgBits ⟨m, hm⟩` bits to the transcript. -/
lemma prefixBits_succ {n : ℕ} (msgBits : Fin n → ℕ) {m : ℕ} (hm : m < n) :
    prefixBits msgBits (m + 1) = prefixBits msgBits m + msgBits ⟨m, hm⟩ := by
  classical
  simp only [prefixBits]
  have hstep : ∀ j : Fin n,
      (if j.1 < m + 1 then msgBits j else 0) =
        (if j.1 < m then msgBits j else 0) + (if j = ⟨m, hm⟩ then msgBits j else 0) := by
    intro j
    by_cases hlt : j.1 < m
    · have hne : j ≠ ⟨m, hm⟩ := fun h ↦ by subst h; exact Nat.lt_irrefl m hlt
      simp [hlt, Nat.lt_succ_of_lt hlt, hne]
    · by_cases heq : j = ⟨m, hm⟩
      · subst heq; simp
      · have hne_val : j.1 ≠ m := fun h ↦ heq (Fin.ext h)
        simp [hlt, heq, show ¬ j.1 < m + 1 by omega]
  simp_rw [hstep, Finset.sum_add_distrib]
  simp

/-- After all `n` turns, `prefixBits msgBits n` equals the sum of all per-turn bit lengths. -/
lemma prefixBits_self {n : ℕ} (msgBits : Fin n → ℕ) :
    prefixBits msgBits n = ∑ j : Fin n, msgBits j := by
  simp [prefixBits]

/-- For constant per-turn bit length `b`, `prefixBits (fun _ ↦ b) m = m * b` for `m ≤ n`. -/
lemma prefixBits_const {n : ℕ} (b : ℕ) {m : ℕ} (hm : m ≤ n) :
    prefixBits (fun _ : Fin n ↦ b) m = m * b := by
  induction m with
  | zero => simp
  | succ m ih => rw [prefixBits_succ _ hm, ih (Nat.le_of_succ_le hm)]; ring

/-- A deterministic `(k, r)`-round cyclic multiparty communication protocol in the number-in-hand
blackboard model: `k` players with private inputs `X : Fin k → Type*` speak in fixed cyclic order
`0 → 1 → ⋯ → k - 1` for `r` rounds, and the last player `k - 1` outputs a value in `Z`. -/
structure CyclicProtocol (k r : ℕ) [NeZero k] (X : Fin k → Type*) (Z : Type*) where
  /-- Number of bits written by the active speaker at linear turn `t : Fin (r * k)`. -/
  msgBits : Fin (r * k) → ℕ
  /-- Message function of speaker `t % k` at linear turn `t`, given their private input and the
  prior blackboard transcript of length `prefixBits msgBits t.1`. -/
  send : ∀ t : Fin (r * k), X (cyclicSpeaker k t.1) →
    (Fin (prefixBits msgBits t.1) → Bool) → (Fin (msgBits t) → Bool)
  /-- Final output map evaluated by the last player `k - 1` on their private input and the complete
  transcript of length `prefixBits msgBits (r * k)`. -/
  out : X (lastPlayer k) → (Fin (prefixBits msgBits (r * k)) → Bool) → Z

/-- Total number of bits communicated by a deterministic cyclic protocol `P`. -/
def CyclicProtocol.totalBits {k r : ℕ} [NeZero k] {X : Fin k → Type*} {Z : Type*}
    (P : CyclicProtocol k r X Z) : ℕ :=
  ∑ t : Fin (r * k), P.msgBits t

/-- Each individual turn writes at most `P.totalBits` bits. -/
lemma CyclicProtocol.msgBits_le_totalBits {k r : ℕ} [NeZero k] {X : Fin k → Type*} {Z : Type*}
    (P : CyclicProtocol k r X Z) (t : Fin (r * k)) :
    P.msgBits t ≤ P.totalBits :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ t)

/-- `prefixBits P.msgBits (r * k)` equals `P.totalBits`. -/
@[simp] lemma CyclicProtocol.prefixBits_total {k r : ℕ} [NeZero k] {X : Fin k → Type*} {Z : Type*}
    (P : CyclicProtocol k r X Z) :
    prefixBits P.msgBits (r * k) = P.totalBits :=
  prefixBits_self P.msgBits

/-- A public-coin randomized `(k, r)`-round cyclic protocol of worst-case total communication cost
at most `c` bits across the support of `dist`. -/
@[ext] structure RandomizedCyclicProtocol (k r : ℕ) [NeZero k] (X : Fin k → Type*) (Z : Type*)
    (c : ℕ) (Ω : Type*) where
  /-- Deterministic cyclic protocol executed for each random seed `ω : Ω`. -/
  proto : Ω → CyclicProtocol k r X Z
  /-- Probability mass function over random seeds `Ω`. -/
  dist : PMF Ω
  /-- Worst-case total communication bit bound `≤ c` across all supported seeds `ω ∈ dist.support`.
  -/
  cost_le : ∀ ω ∈ dist.support, (proto ω).totalBits ≤ c

variable {k r : ℕ} [NeZero k] {X : Fin k → Type*} {Z : Type*}

/-- Partial blackboard transcript of `P` after the first `m ≤ r * k` linear turns on input `x`. -/
def CyclicProtocol.partialTranscript (P : CyclicProtocol k r X Z) (x : ∀ i : Fin k, X i) :
    ∀ (m : ℕ), m ≤ r * k → (Fin (prefixBits P.msgBits m) → Bool)
  | 0, _ => fun i ↦ Fin.elim0 (by simpa using i)
  | m + 1, hm => fun i ↦
      if hi : i.1 < prefixBits P.msgBits m then
        P.partialTranscript x m (Nat.le_of_succ_le hm) ⟨i.1, hi⟩
      else
        P.send ⟨m, hm⟩ (x (cyclicSpeaker k m))
          (P.partialTranscript x m (Nat.le_of_succ_le hm))
          ⟨i.1 - prefixBits P.msgBits m, by
            have hlt : i.1 < prefixBits P.msgBits m + P.msgBits ⟨m, hm⟩ := by
              rw [← prefixBits_succ P.msgBits hm]; exact i.2
            omega⟩

/-- Reading a bit from turn `< m` in `partialTranscript (m + 1)` matches `partialTranscript m`. -/
lemma CyclicProtocol.partialTranscript_succ_lt (P : CyclicProtocol k r X Z)
    (x : ∀ i : Fin k, X i) (m : ℕ) (hm : m + 1 ≤ r * k)
    {i : Fin (prefixBits P.msgBits (m + 1))} (hi : i.1 < prefixBits P.msgBits m) :
    P.partialTranscript x (m + 1) hm i =
      P.partialTranscript x m (Nat.le_of_succ_le hm) ⟨i.1, hi⟩ := by
  simp [CyclicProtocol.partialTranscript, hi]

/-- Reading a bit written during turn `m` in `partialTranscript (m + 1)` recovers `P.send`. -/
lemma CyclicProtocol.partialTranscript_succ_ge (P : CyclicProtocol k r X Z)
    (x : ∀ i : Fin k, X i) (m : ℕ) (hm : m + 1 ≤ r * k)
    {i : Fin (prefixBits P.msgBits (m + 1))} (hi : ¬ i.1 < prefixBits P.msgBits m) :
    P.partialTranscript x (m + 1) hm i =
      P.send ⟨m, hm⟩ (x (cyclicSpeaker k m))
        (P.partialTranscript x m (Nat.le_of_succ_le hm))
        ⟨i.1 - prefixBits P.msgBits m, by
          have hlt : i.1 < prefixBits P.msgBits m + P.msgBits ⟨m, hm⟩ := by
            rw [← prefixBits_succ P.msgBits hm]; exact i.2
          omega⟩ := by
  simp [CyclicProtocol.partialTranscript, hi]

/-- Earlier transcript bits remain unchanged at all later turns `m₂ ≥ m₁`. -/
lemma CyclicProtocol.partialTranscript_mono (P : CyclicProtocol k r X Z)
    (x : ∀ i : Fin k, X i) {m₁ m₂ : ℕ} (hm₁ : m₁ ≤ r * k) (hm₂ : m₂ ≤ r * k)
    (hle : m₁ ≤ m₂) (i : Fin (prefixBits P.msgBits m₁)) :
    P.partialTranscript x m₂ hm₂ ⟨i.1, lt_of_lt_of_le i.2 (prefixBits_mono P.msgBits hle)⟩ =
      P.partialTranscript x m₁ hm₁ i := by
  induction m₂ with
  | zero =>
    obtain rfl : m₁ = 0 := by omega
    rfl
  | succ m₂ ih =>
    by_cases heq : m₁ = m₂ + 1
    · subst heq; rfl
    · have hm12 : m₁ ≤ m₂ := by omega
      rw [P.partialTranscript_succ_lt x m₂ hm₂
        (lt_of_lt_of_le i.2 (prefixBits_mono P.msgBits hm12))]
      exact ih (Nat.le_of_succ_le hm₂) hm12

/-- Complete blackboard transcript of `P` on input profile `x`. -/
def CyclicProtocol.transcript (P : CyclicProtocol k r X Z) (x : ∀ i : Fin k, X i) :
    Fin (prefixBits P.msgBits (r * k)) → Bool :=
  P.partialTranscript x (r * k) le_rfl

/-- Output produced by `P` on input profile `x`. -/
def CyclicProtocol.run (P : CyclicProtocol k r X Z) (x : ∀ i : Fin k, X i) : Z :=
  P.out (x (lastPlayer k)) (P.transcript x)

/-- Equality of full transcripts and the last player's input forces equality of outputs. -/
lemma CyclicProtocol.run_congr (P : CyclicProtocol k r X Z) {x y : ∀ i : Fin k, X i}
    (hlast : x (lastPlayer k) = y (lastPlayer k))
    (htr : P.transcript x = P.transcript y) :
    P.run x = P.run y := by
  simp only [run, hlast, htr]

/-- Error probability of a randomized cyclic protocol `P` on input `x` for target `f`. -/
noncomputable def RandomizedCyclicProtocol.errorProb {c : ℕ} {Ω : Type*}
    (P : RandomizedCyclicProtocol k r X Z c Ω) (f : (∀ i : Fin k, X i) → Z)
    (x : ∀ i : Fin k, X i) : ℝ≥0∞ :=
  P.dist.toOuterMeasure {ω | (P.proto ω).run x ≠ f x}

/-- If a randomized cyclic protocol produces identical outputs on `x₁` and `x₂` for every seed
`ω ∈ P.dist.support` while `f x₁ ≠ f x₂`, the sum of its error probabilities on `x₁` and `x₂` is
at least `1`. -/
theorem RandomizedCyclicProtocol.one_le_errorProb_add_of_run_eq {c : ℕ} {Ω : Type*}
    (P : RandomizedCyclicProtocol k r X Z c Ω) (f : (∀ i : Fin k, X i) → Z)
    {x₁ x₂ : ∀ i : Fin k, X i}
    (hrun : ∀ ω ∈ P.dist.support, (P.proto ω).run x₁ = (P.proto ω).run x₂)
    (hne : f x₁ ≠ f x₂) :
    (1 : ℝ≥0∞) ≤ P.errorProb f x₁ + P.errorProb f x₂ := by
  simp only [errorProb, PMF.toOuterMeasure_apply]
  rw [← tsum_add, ← P.dist.tsum_coe]
  refine tsum_le_tsum fun ω ↦ ?_
  by_cases hω : ω ∈ P.dist.support
  · by_cases h1 : (P.proto ω).run x₁ ≠ f x₁
    · simp [Set.indicator, h1]
    · by_cases h2 : (P.proto ω).run x₂ ≠ f x₂
      · simp [Set.indicator, h2]
      · push Not at h1 h2
        exact absurd (h1.symm.trans ((hrun ω hω).trans h2)) hne
  · have h0 : P.dist ω = 0 := by simpa [PMF.mem_support_iff] using hω
    rw [h0]; exact zero_le

/-- A randomized cyclic protocol `P` computes `f` with error probability at most `ε`. -/
def RandomizedCyclicProtocol.ComputesWithError {c : ℕ} {Ω : Type*}
    (P : RandomizedCyclicProtocol k r X Z c Ω) (f : (∀ i : Fin k, X i) → Z) (ε : ℝ≥0∞) : Prop :=
  ∀ x, P.errorProb f x ≤ ε

/-- View a deterministic `CyclicProtocol` as a `RandomizedCyclicProtocol` over `PUnit`. -/
noncomputable def CyclicProtocol.toRandomized (P : CyclicProtocol k r X Z) :
    RandomizedCyclicProtocol k r X Z P.totalBits PUnit where
  proto _ := P
  dist := PMF.pure PUnit.unit
  cost_le _ _ := le_rfl

/-- A deterministic cyclic protocol computing `f` computes `f` with error probability `0`. -/
theorem CyclicProtocol.computesWithError_zero_of_run_eq {P : CyclicProtocol k r X Z}
    {f : (∀ i : Fin k, X i) → Z} (hP : ∀ x, P.run x = f x) :
    P.toRandomized.ComputesWithError f 0 := by
  intro x
  simp [RandomizedCyclicProtocol.errorProb, toRandomized, hP x]

/-- Weaken the communication cost bound of a `RandomizedCyclicProtocol`. -/
def RandomizedCyclicProtocol.castCost {c₁ c₂ : ℕ} {Ω : Type*}
    (P : RandomizedCyclicProtocol k r X Z c₁ Ω) (h : c₁ ≤ c₂) :
    RandomizedCyclicProtocol k r X Z c₂ Ω where
  proto := P.proto
  dist := P.dist
  cost_le ω hω := (P.cost_le ω hω).trans h

end CyclicProtocols

/-! ### Simulating Multi-Pass Streaming Algorithms via Cyclic Protocols -/

section StreamingToCyclic

/-- Concatenation of `k` per-player token lists in player order `0, 1, ..., k - 1`. -/
def concatChunks {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) : List Token :=
  (List.finRange k).flatMap (fun i ↦ chunk i (x i))

/-- Flat-map formula for `concatChunks chunk x`. -/
lemma concatChunks_eq_flatMap {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) :
    concatChunks chunk x = (List.finRange k).flatMap (fun i ↦ chunk i (x i)) := by exact id rfl

/-- Mapping `φ` over `concatChunks chunk x` distributes into each player's chunk. -/
lemma map_concatChunks {Token Token' : Type*} {k : ℕ} {X : Fin k → Type*}
    (φ : Token → Token') (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) :
    (concatChunks chunk x).map φ = concatChunks (fun i xi ↦ (chunk i xi).map φ) x := by
  simp [concatChunks, List.map_flatMap]

/-- Membership in `concatChunks chunk x` holds iff the token lies in some player's chunk. -/
lemma mem_concatChunks {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    {chunk : ∀ i : Fin k, X i → List Token} {x : ∀ i : Fin k, X i} {a : Token} :
    a ∈ concatChunks chunk x ↔ ∃ i : Fin k, a ∈ chunk i (x i) := by
  simp [concatChunks]

/-- `concatChunks chunk x` is duplicate-free when each chunk is duplicate-free and distinct
players emit disjoint chunks. -/
lemma nodup_concatChunks {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    {chunk : ∀ i : Fin k, X i → List Token} {x : ∀ i : Fin k, X i}
    (hchunk : ∀ i : Fin k, (chunk i (x i)).Nodup)
    (hdisj : ∀ {i₁ i₂ : Fin k}, i₁ ≠ i₂ → List.Disjoint (chunk i₁ (x i₁)) (chunk i₂ (x i₂))) :
    (concatChunks chunk x).Nodup :=
  List.nodup_flatMap.mpr ⟨fun i _ ↦ hchunk i, (List.nodup_finRange k).imp hdisj⟩

private def prefixChunks {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) (j : ℕ) : List Token :=
  ((List.finRange k).take j).flatMap (fun i ↦ chunk i (x i))

private lemma prefixChunks_zero {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) :
    prefixChunks chunk x 0 = [] := by exact id rfl

private lemma prefixChunks_eq_concatChunks_of_eq {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) {m : ℕ} (hm : m = k) :
    prefixChunks chunk x m = concatChunks chunk x := by
  subst hm
  simp [prefixChunks, concatChunks,
    List.take_of_length_le (show (List.finRange m).length ≤ m by simp)]

private lemma prefixChunks_succ {Token : Type*} {k : ℕ} {X : Fin k → Type*}
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) {j : ℕ} (hj : j < k) :
    prefixChunks chunk x (j + 1) = prefixChunks chunk x j ++ chunk ⟨j, hj⟩ (x ⟨j, hj⟩) := by
  have htake : (List.finRange k).take (j + 1) = (List.finRange k).take j ++ [⟨j, hj⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hj])]; simp
  simp [prefixChunks, htake, List.flatMap_append]

private def extractLastBits {b m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {msgBits : Fin n → ℕ}
    (hmsg : msgBits = fun _ ↦ b) (hist : Fin (prefixBits msgBits m) → Bool) : Fin b → Bool :=
  fun j ↦ hist ⟨(m - 1) * b + j.1, by
    subst hmsg
    rw [prefixBits_const b hmn]
    have hmul : (m - 1) * b + b = m * b := by
      calc (m - 1) * b + b = (m - 1 + 1) * b := by ring
        _ = m * b := by rw [Nat.sub_add_cancel hm]
    omega⟩

/-- Canonical deterministic `(k, r)`-round cyclic protocol simulating an `r`-pass streaming
algorithm `A` over a finite nonempty state space `S` on the concatenated player stream
`concatChunks chunk x`, followed by post-processing `dec : Z → W`. -/
noncomputable def MultiPassTokenStreamingAlgorithm.toCyclicProtocol
    {Token Z W S : Type*} [Fintype S] [Nonempty S] {k r : ℕ} [NeZero k]
    {X : Fin k → Type*} (A : MultiPassTokenStreamingAlgorithm Token Z S r)
    (chunk : ∀ i : Fin k, X i → List Token) (dec : Z → W) :
    CyclicProtocol k r X W where
  msgBits _ := Nat.clog 2 (Fintype.card S)
  send t xt hist :=
    let sPrev : S :=
      if ht : 0 < t.1 then fintypeOfFinBits (extractLastBits ht (le_of_lt t.2) rfl hist)
      else A.initState
    let passIdx : Fin r := ⟨t.1 / k, (Nat.div_lt_iff_lt_mul (NeZero.pos k)).mpr
      (by simpa [Nat.mul_comm] using t.2)⟩
    finBitsOfFintype ((chunk (cyclicSpeaker k t.1) xt).foldl (A.step passIdx) sPrev)
  out _ fullHist :=
    if hr : 0 < r then
      dec (A.output (fintypeOfFinBits
        (extractLastBits (Nat.mul_pos hr (NeZero.pos k)) le_rfl rfl fullHist)))
    else
      dec (A.output A.initState)

/-- Total communication cost of `MultiPassTokenStreamingAlgorithm.toCyclicProtocol` is
`r * k * Nat.clog 2 (Fintype.card S)`. -/
@[simp] lemma MultiPassTokenStreamingAlgorithm.totalBits_toCyclicProtocol
    {Token Z W S : Type*} [Fintype S] [Nonempty S] {k r : ℕ} [NeZero k]
    {X : Fin k → Type*} (A : MultiPassTokenStreamingAlgorithm Token Z S r)
    (chunk : ∀ i : Fin k, X i → List Token) (dec : Z → W) :
    (A.toCyclicProtocol chunk dec).totalBits = r * k * Nat.clog 2 (Fintype.card S) := by
  simp [CyclicProtocol.totalBits, MultiPassTokenStreamingAlgorithm.toCyclicProtocol]

private lemma div_le_of_le_mul_right {m r k : ℕ} (hk : 0 < k) (hm : m ≤ r * k) :
    m / k ≤ r := by
  rw [Nat.div_le_iff_le_mul_add_pred hk]
  calc m ≤ r * k := hm
    _ = k * r := mul_comm r k
    _ ≤ k * r + (k - 1) := Nat.le_add_right _ _

private lemma div_lt_of_succ_le_mul_right {m r k : ℕ} (hk : 0 < k) (hm : m + 1 ≤ r * k) :
    m / k < r :=
  (Nat.div_lt_iff_lt_mul hk).mpr (by simpa [Nat.mul_comm] using hm)

private def simState {Token Z S : Type*} {k r : ℕ} [NeZero k] {X : Fin k → Type*}
    (A : MultiPassTokenStreamingAlgorithm Token Z S r)
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i)
    (m : ℕ) (hm : m ≤ r * k) : S :=
  if hrem : m % k = 0 then
    A.runFirstPasses (concatChunks chunk x) (m / k)
      (div_le_of_le_mul_right (NeZero.pos k) hm)
  else
    let q := m / k
    have hq : q < r := by
      have hlt : m < r * k := lt_of_le_of_ne hm fun heq ↦ by
        subst heq; exact hrem (Nat.mul_mod_left r k)
      exact div_lt_of_succ_le_mul_right (NeZero.pos k) hlt
    A.runPass ⟨q, hq⟩ (A.runFirstPasses (concatChunks chunk x) q (le_of_lt hq))
      (prefixChunks chunk x (m % k))

private lemma simState_zero {Token Z S : Type*} {k r : ℕ} [NeZero k] {X : Fin k → Type*}
    (A : MultiPassTokenStreamingAlgorithm Token Z S r)
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i) :
    simState A chunk x 0 (Nat.zero_le _) = A.initState := by
  simp [simState]

private lemma simState_succ {Token Z S : Type*} {k r : ℕ} [NeZero k] {X : Fin k → Type*}
    (A : MultiPassTokenStreamingAlgorithm Token Z S r)
    (chunk : ∀ i : Fin k, X i → List Token) (x : ∀ i : Fin k, X i)
    (m : ℕ) (hm : m + 1 ≤ r * k) :
    simState A chunk x (m + 1) hm =
      (chunk (cyclicSpeaker k m) (x (cyclicSpeaker k m))).foldl
        (A.step ⟨m / k, div_lt_of_succ_le_mul_right (NeZero.pos k) hm⟩)
        (simState A chunk x m (Nat.le_of_succ_le hm)) := by
  have hkpos : 0 < k := NeZero.pos k
  have hmod_lt : m % k < k := Nat.mod_lt m hkpos
  have hdiv_lt : m / k < r := div_lt_of_succ_le_mul_right hkpos hm
  by_cases hlast : m % k + 1 = k
  · have hmul_eq : m + 1 = (m / k + 1) * k := by have := Nat.div_add_mod m k; nlinarith
    have hm1_mod : (m + 1) % k = 0 := by rw [hmul_eq, Nat.mul_mod_left]
    have hm1_div : (m + 1) / k = m / k + 1 := by rw [hmul_eq, Nat.mul_div_cancel _ hkpos]
    simp only [simState, hm1_mod, ↓reduceDIte]
    rw [runFirstPasses_congr A (concatChunks chunk x) _ (Nat.succ_le_of_lt hdiv_lt) hm1_div,
      MultiPassTokenStreamingAlgorithm.runFirstPasses_succ]
    by_cases hm0 : m % k = 0
    · simp only [hm0, ↓reduceDIte]
      have hcat : concatChunks chunk x = chunk (cyclicSpeaker k m) (x (cyclicSpeaker k m)) := by
        rw [← prefixChunks_eq_concatChunks_of_eq chunk x hlast,
          prefixChunks_succ chunk x hmod_lt,
          show prefixChunks chunk x (m % k) = [] by rw [hm0]; rfl, List.nil_append]
        rfl
      rw [hcat]; rfl
    · simp only [hm0, ↓reduceDIte]
      have hcat : concatChunks chunk x =
          prefixChunks chunk x (m % k) ++ chunk (cyclicSpeaker k m) (x (cyclicSpeaker k m)) := by
        rw [← prefixChunks_eq_concatChunks_of_eq chunk x hlast, prefixChunks_succ chunk x hmod_lt]
        rfl
      rw [hcat, MultiPassTokenStreamingAlgorithm.runPass_append]; rfl
  · have hm1_lt : m % k + 1 < k := by omega
    have hmul_eq : m + 1 = k * (m / k) + (m % k + 1) := by have := Nat.div_add_mod m k; omega
    have hm1_mod : (m + 1) % k = m % k + 1 := by
      rw [hmul_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hm1_lt]
    have hm1_div : (m + 1) / k = m / k := by
      rw [hmul_eq, Nat.mul_add_div hkpos, Nat.div_eq_of_lt hm1_lt, add_zero]
    have hm1_ne : (m + 1) % k ≠ 0 := by omega
    simp only [simState, hm1_ne, ↓reduceDIte]
    have hstep_eq :
        A.runPass ⟨(m + 1) / k, by omega⟩
            (A.runFirstPasses (concatChunks chunk x) ((m + 1) / k) (by omega))
            (prefixChunks chunk x ((m + 1) % k)) =
          A.runPass ⟨m / k, hdiv_lt⟩
            (A.runFirstPasses (concatChunks chunk x) (m / k) (le_of_lt hdiv_lt))
            (prefixChunks chunk x (m % k + 1)) := by
      rw [hm1_mod]
      have hf := runFirstPasses_congr A (concatChunks chunk x)
        (le_of_lt (by omega : (m + 1) / k < r)) (le_of_lt hdiv_lt) hm1_div
      rw [show (⟨(m + 1) / k, by omega⟩ : Fin r) = ⟨m / k, hdiv_lt⟩ from Fin.ext hm1_div, hf]
    rw [hstep_eq, prefixChunks_succ chunk x hmod_lt,
      MultiPassTokenStreamingAlgorithm.runPass_append]
    by_cases hm0 : m % k = 0 <;> simp only [hm0, ↓reduceDIte, prefixChunks_zero] <;> rfl

/-- Exact output preservation: simulating `A` via `A.toCyclicProtocol chunk dec` computes
`dec (A.runStream (concatChunks chunk x))` on every input profile `x`. -/
theorem MultiPassTokenStreamingAlgorithm.run_toCyclicProtocol
    {Token Z W S : Type*} [Fintype S] [Nonempty S] {k r : ℕ} [NeZero k]
    {X : Fin k → Type*} (A : MultiPassTokenStreamingAlgorithm Token Z S r)
    (chunk : ∀ i : Fin k, X i → List Token) (dec : Z → W) (x : ∀ i : Fin k, X i) :
    (A.toCyclicProtocol chunk dec).run x = dec (A.runStream (concatChunks chunk x)) := by
  let P := A.toCyclicProtocol chunk dec
  have hmsg : P.msgBits = fun _ ↦ Nat.clog 2 (Fintype.card S) := rfl
  have hinv : ∀ (m : ℕ) (hm : m ≤ r * k) (hpos : 0 < m),
      fintypeOfFinBits (extractLastBits hpos hm hmsg (P.partialTranscript x m hm)) =
        simState A chunk x m hm := by
    intro m
    induction m with
    | zero => intro _ h0; exact absurd h0 (Nat.lt_irrefl 0)
    | succ m ih =>
      intro hm hpos
      let b := Nat.clog 2 (Fintype.card S)
      have hbits :
          extractLastBits hpos hm hmsg (P.partialTranscript x (m + 1) hm) =
            P.send ⟨m, hm⟩ (x (cyclicSpeaker k m))
              (P.partialTranscript x m (Nat.le_of_succ_le hm)) := by
        funext j
        have hpre : prefixBits P.msgBits m = m * b := by
          rw [hmsg]; exact prefixBits_const b (Nat.le_of_succ_le hm)
        change P.partialTranscript x (m + 1) hm ⟨m * b + j.1, _⟩ = _
        rw [CyclicProtocol.partialTranscript_succ_ge P x m hm
          (by change ¬ m * b + j.1 < prefixBits P.msgBits m; omega)]
        congr 1; apply Fin.ext; dsimp; omega
      rw [hbits]
      have hsend :
          P.send ⟨m, hm⟩ (x (cyclicSpeaker k m))
              (P.partialTranscript x m (Nat.le_of_succ_le hm)) =
            finBitsOfFintype
              ((chunk (cyclicSpeaker k m) (x (cyclicSpeaker k m))).foldl
                (A.step ⟨m / k, div_lt_of_succ_le_mul_right (NeZero.pos k) hm⟩)
                (simState A chunk x m (Nat.le_of_succ_le hm))) := by
        change finBitsOfFintype
          ((chunk (cyclicSpeaker k m) (x (cyclicSpeaker k m))).foldl
            (A.step ⟨m / k, div_lt_of_succ_le_mul_right (NeZero.pos k) hm⟩) _) = _
        congr 2
        by_cases hm0 : 0 < m
        · simp only [hm0, ↓reduceDIte]; exact ih (Nat.le_of_succ_le hm) hm0
        · simp only [hm0, ↓reduceDIte]
          obtain rfl : m = 0 := by omega
          exact (simState_zero A chunk x).symm
      rw [hsend, fintypeOfFinBits_finBitsOfFintype, simState_succ]
  simp only [CyclicProtocol.run, CyclicProtocol.transcript]
  change (if hr : 0 < r then
      dec (A.output (fintypeOfFinBits
        (extractLastBits (Nat.mul_pos hr (NeZero.pos k)) le_rfl hmsg
          (P.partialTranscript x (r * k) le_rfl))))
    else dec (A.output A.initState)) = dec (A.runStream (concatChunks chunk x))
  by_cases hr : 0 < r
  · simp only [hr, ↓reduceDIte, hinv (r * k) le_rfl (Nat.mul_pos hr (NeZero.pos k))]
    have hsim : simState A chunk x (r * k) le_rfl = A.runPasses (concatChunks chunk x) := by
      simp only [simState, Nat.mul_mod_left r k, ↓reduceDIte,
        MultiPassTokenStreamingAlgorithm.runPasses]
      exact runFirstPasses_congr A (concatChunks chunk x) _ le_rfl
        (Nat.mul_div_cancel r (NeZero.pos k))
    rw [hsim]; rfl
  · obtain rfl : r = 0 := by omega
    rfl

/-- Canonical randomized `(k, r)`-round cyclic protocol simulating a randomized `r`-pass streaming
algorithm `A` over a finite nonempty state space `S`, using `r * k * ⌈log₂ |S|⌉` total bits. -/
noncomputable def RandomizedMultiPassStreaming.toRandomizedCyclicProtocol
    {Token Z W S Ω : Type*} [Fintype S] [Nonempty S] {k r : ℕ} [NeZero k]
    {X : Fin k → Type*} (A : RandomizedMultiPassStreaming Token Z S r Ω)
    (chunk : ∀ i : Fin k, X i → List Token) (dec : Z → W) :
    RandomizedCyclicProtocol k r X W (r * k * Nat.clog 2 (Fintype.card S)) Ω where
  proto ω := (A.alg ω).toCyclicProtocol chunk dec
  dist := A.dist
  cost_le ω _ := le_of_eq ((A.alg ω).totalBits_toCyclicProtocol chunk dec)

/-- Error preservation for `RandomizedMultiPassStreaming.toRandomizedCyclicProtocol`. -/
theorem RandomizedMultiPassStreaming.computesWithError_toRandomizedCyclicProtocol
    {Token Z W S Ω : Type*} [Fintype S] [Nonempty S] {k r : ℕ} [NeZero k]
    {X : Fin k → Type*} {A : RandomizedMultiPassStreaming Token Z S r Ω}
    {Valid : List Token → Prop} {g : List Token → Z} {ε : ℝ≥0∞}
    (hA : A.ComputesWithErrorOn Valid g ε)
    (chunk : ∀ i : Fin k, X i → List Token) (dec : Z → W)
    {f : (∀ i : Fin k, X i) → W}
    (hValid : ∀ x, Valid (concatChunks chunk x))
    (hDec : ∀ x, dec (g (concatChunks chunk x)) = f x) :
    (A.toRandomizedCyclicProtocol chunk dec).ComputesWithError f ε := by
  intro x
  refine (A.dist.toOuterMeasure.mono ?_).trans (hA (concatChunks chunk x) (hValid x))
  intro ω hω heq
  apply hω
  change ((A.alg ω).toCyclicProtocol chunk dec).run x = f x
  rw [MultiPassTokenStreamingAlgorithm.run_toCyclicProtocol, heq, hDec x]

end StreamingToCyclic

/-! ### Multiparty Pointer Chasing and Set-Chasing Intersection -/

section PointerAndSetChasing

/-- `k`-player pointer-chasing function `f 0 (f 1 (... (f (k - 1) x₀)))` on `Fin n`. -/
def pointerChasing {n k : ℕ} (f : Fin k → Fin n → Fin n) (x₀ : Fin n) : Fin n :=
  (List.finRange k).foldr (fun i x ↦ f i x) x₀

/-- Zero-player pointer chasing returns `x₀`. -/
@[simp] lemma pointerChasing_zero {n : ℕ} (f : Fin 0 → Fin n → Fin n) (x₀ : Fin n) :
    pointerChasing f x₀ = x₀ := by exact id rfl

/-- Head recursion for `pointerChasing` peeling off the final evaluator `0`. -/
lemma pointerChasing_succ {n k : ℕ} (f : Fin (k + 1) → Fin n → Fin n) (x₀ : Fin n) :
    pointerChasing f x₀ = f 0 (pointerChasing (fun i ↦ f i.succ) x₀) := by
  simp only [pointerChasing, List.finRange_succ, List.foldr_cons, List.foldr_map]

/-- Tail recursion for `pointerChasing` peeling off the first-acting player `Fin.last k`. -/
lemma pointerChasing_succ_last {n k : ℕ} (f : Fin (k + 1) → Fin n → Fin n) (x₀ : Fin n) :
    pointerChasing f x₀ = pointerChasing (fun i ↦ f i.castSucc) (f (Fin.last k) x₀) := by
  rw [pointerChasing, List.finRange_succ_last, List.foldr_append, List.foldr_map]; rfl

/-- Set-valued union lift `F'(S) = ⋃ u ∈ S, F u` on `Finset (Fin n)`. -/
def setLift {n : ℕ} (F : Fin n → Finset (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.biUnion F

/-- Membership characterization for `setLift`. -/
lemma mem_setLift {n : ℕ} {F : Fin n → Finset (Fin n)} {S : Finset (Fin n)} {v : Fin n} :
    v ∈ setLift F S ↔ ∃ u ∈ S, v ∈ F u :=
  Finset.mem_biUnion

/-- `setLift` maps `∅` to `∅`. -/
@[simp] lemma setLift_empty {n : ℕ} (F : Fin n → Finset (Fin n)) :
    setLift F ∅ = ∅ := by exact id rfl

/-- `setLift` on a singleton `{u}` equals `F u`. -/
@[simp] lemma setLift_singleton {n : ℕ} (F : Fin n → Finset (Fin n)) (u : Fin n) :
    setLift F {u} = F u := by
  ext v; simp [mem_setLift]

/-- `k`-player set chasing `F'_0 (F'_1 (... (F'_{k-1} S₀)))` on `Finset (Fin n)`. -/
def setChasing {n k : ℕ} (F : Fin k → Fin n → Finset (Fin n)) (S₀ : Finset (Fin n)) :
    Finset (Fin n) :=
  (List.finRange k).foldr (fun i S ↦ setLift (F i) S) S₀

/-- Zero-player set chasing returns `S₀`. -/
@[simp] lemma setChasing_zero {n : ℕ} (F : Fin 0 → Fin n → Finset (Fin n))
    (S₀ : Finset (Fin n)) : setChasing F S₀ = S₀ := by exact id rfl

/-- Head recursion for `setChasing`. -/
lemma setChasing_succ {n k : ℕ} (F : Fin (k + 1) → Fin n → Finset (Fin n))
    (S₀ : Finset (Fin n)) :
    setChasing F S₀ = setLift (F 0) (setChasing (fun i ↦ F i.succ) S₀) := by
  simp only [setChasing, List.finRange_succ, List.foldr_cons, List.foldr_map]

/-- Left-half set-chasing output on the first `p` players `0, ..., p - 1`. -/
def setChasingLeft {n p : ℕ} (F : Fin (2 * p) → Fin n → Finset (Fin n))
    (S₀ : Finset (Fin n)) : Finset (Fin n) :=
  setChasing (fun i : Fin p ↦ F ⟨i.1, by omega⟩) S₀

/-- Right-half set-chasing output on the last `p` players `p, ..., 2 * p - 1`. -/
def setChasingRight {n p : ℕ} (F : Fin (2 * p) → Fin n → Finset (Fin n))
    (S₀ : Finset (Fin n)) : Finset (Fin n) :=
  setChasing (fun i : Fin p ↦ F ⟨p + i.1, by omega⟩) S₀

/-- Boolean indicator of `INTERSECT(SC_{n, p})`. -/
def setChasingIntersect {n p : ℕ} (F : Fin (2 * p) → Fin n → Finset (Fin n))
    (S₀ : Finset (Fin n)) : Bool :=
  decide ((setChasingLeft F S₀ ∩ setChasingRight F S₀).Nonempty)

/-- Characterization of `setChasingIntersect F S₀ = true` via nonempty intersection. -/
lemma setChasingIntersect_eq_true_iff {n p : ℕ}
    (F : Fin (2 * p) → Fin n → Finset (Fin n)) (S₀ : Finset (Fin n)) :
    setChasingIntersect F S₀ = true ↔
      (setChasingLeft F S₀ ∩ setChasingRight F S₀).Nonempty := by
  simp [setChasingIntersect]

private def pcSuffix {n k : ℕ} (f : Fin k → Fin n → Fin n) (r : ℕ) (x₀ : Fin n) : Fin n :=
  ((List.finRange k).drop (k - r)).foldr (fun i x ↦ f i x) x₀

private lemma pcSuffix_zero {n k : ℕ} (f : Fin k → Fin n → Fin n) (x₀ : Fin n) :
    pcSuffix f 0 x₀ = x₀ := by
  have hnil : (List.finRange k).drop k = [] := List.drop_eq_nil_of_le (by simp)
  simp only [pcSuffix, Nat.sub_zero, hnil, List.foldr_nil]

private lemma pcSuffix_succ {n k : ℕ} (f : Fin k → Fin n → Fin n) (x₀ : Fin n)
    {r : ℕ} (hr : r < k) :
    pcSuffix f (r + 1) x₀ = f ⟨k - 1 - r, by omega⟩ (pcSuffix f r x₀) := by
  simp only [pcSuffix]
  have hlt : k - (r + 1) < (List.finRange k).length := by simp; omega
  rw [List.drop_eq_getElem_cons hlt, show k - (r + 1) + 1 = k - r by omega, List.foldr_cons,
    List.getElem_finRange]
  congr 1; apply Fin.ext; dsimp; omega

private lemma pcSuffix_self {n k : ℕ} (f : Fin k → Fin n → Fin n) (x₀ : Fin n) :
    pcSuffix f k x₀ = pointerChasing f x₀ := by
  simp [pcSuffix, pointerChasing]

/-- **Round sharpness of pointer chasing**: with `k` full cyclic rounds across `k` players,
`k * Nat.clog 2 n` bits suffice to compute `pointerChasing f x₀` deterministically. -/
theorem exists_cyclicProtocol_pointerChasing_k_rounds {n k : ℕ} [NeZero k] (hn : 0 < n)
    (x₀ : Fin n) :
    ∃ P : CyclicProtocol k k (fun _ : Fin k ↦ Fin n → Fin n) (Fin n),
      P.totalBits ≤ k * Nat.clog 2 n ∧
        ∀ f : Fin k → Fin n → Fin n, P.run f = pointerChasing f x₀ := by
  have hk : 0 < k := NeZero.pos k
  let b := Nat.clog 2 n
  let writeTurn : ℕ → ℕ := fun r ↦ r * k + (k - 1 - r)
  have hwrite_div : ∀ r, r < k → writeTurn r / k = r := fun r hr ↦ by
    rw [show writeTurn r = (k - 1 - r) + k * r by simp only [writeTurn]; ring,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega), zero_add]
  have hwrite_mod : ∀ r, r < k → writeTurn r % k = k - 1 - r := fun r hr ↦ by
    rw [show writeTurn r = (k - 1 - r) + k * r by simp only [writeTurn]; ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hwrite_lt : ∀ r, r < k → writeTurn r < k * k := fun r hr ↦ calc
    r * k + (k - 1 - r) < r * k + k := Nat.add_lt_add_left (by omega) _
    _ = (r + 1) * k := by ring
    _ ≤ k * k := Nat.mul_le_mul_right k hr
  have hwrite_step_lt : ∀ r, r + 1 < k → writeTurn r + 1 ≤ writeTurn (r + 1) := fun r hr ↦ by
    simp only [writeTurn]; have : (r + 1) * k = r * k + k := by ring
    omega
  let msgB : Fin (k * k) → ℕ := fun t ↦ if ∃ r < k, t.1 = writeTurn r then b else 0
  have hmsg_eq : ∀ {t : Fin (k * k)} {r : ℕ}, r < k → t.1 = writeTurn r → msgB t = b :=
    fun hr ht ↦ ite_eq_left_of_eq_true b 0 (eq_true ⟨_, hr, ht⟩)
  have hmsg_zero : ∀ {t : Fin (k * k)}, ¬ (∃ r < k, t.1 = writeTurn r) → msgB t = 0 :=
    fun ht ↦ ite_eq_right_of_eq_false b 0 (eq_false ht)
  have hblock_le : ∀ {r m : ℕ}, r < k → writeTurn r + 1 ≤ m →
      prefixBits msgB (writeTurn r) + b ≤ prefixBits msgB m := fun {r m} hr hwm ↦ calc
    prefixBits msgB (writeTurn r) + b
        = prefixBits msgB (writeTurn r) + msgB ⟨writeTurn r, hwrite_lt _ hr⟩ := by
      rw [hmsg_eq hr rfl]
    _ = prefixBits msgB (writeTurn r + 1) := (prefixBits_succ msgB (hwrite_lt _ hr)).symm
    _ ≤ prefixBits msgB m := prefixBits_mono msgB hwm
  let P : CyclicProtocol k k (fun _ : Fin k ↦ Fin n → Fin n) (Fin n) :=
    { msgBits := msgB
      send := fun t f_spk hist ↦
        if ht : ∃ r < k, t.1 = writeTurn r then
          have hmt : b = msgB t := let ⟨r', hr', htr'⟩ := ht; (hmsg_eq hr' htr').symm
          let r := t.1 / k
          if hr0 : r = 0 then
            fun j ↦ encodeFin (f_spk x₀) (Fin.cast hmt.symm j)
          else
            let rPrev := r - 1
            have hrPrev_lt_k : rPrev < k := by
              rcases ht with ⟨r', hr', htr'⟩
              have : r < k := by simpa [r, htr', hwrite_div r' hr'] using hr'
              omega
            have hprev_lt_t : writeTurn rPrev + 1 ≤ t.1 := by
              rcases ht with ⟨r', hr', htr'⟩
              have hr_eq : r = r' := by simpa [r, htr'] using hwrite_div r' hr'
              rw [htr', show r' = rPrev + 1 by omega]
              exact hwrite_step_lt rPrev (by omega)
            let prevVal : Fin n := decodeFin hn fun j : Fin b ↦
              hist ⟨prefixBits msgB (writeTurn rPrev) + j.1, by
                have := hblock_le hrPrev_lt_k hprev_lt_t; omega⟩
            fun j ↦ encodeFin (f_spk prevVal) (Fin.cast hmt.symm j)
        else fun j ↦ False.elim (Nat.not_lt_zero j.1 (lt_of_lt_of_eq j.2 (hmsg_zero ht)))
      out := fun _ fullHist ↦
        decodeFin hn fun j : Fin b ↦
          fullHist ⟨prefixBits msgB (writeTurn (k - 1)) + j.1, by
            have := hblock_le (r := k - 1) (m := k * k) (by omega) (hwrite_lt (k - 1) (by omega))
            omega⟩ }
  have hround_val : ∀ (f : Fin k → Fin n → Fin n) (r : ℕ) (hr : r < k),
      (fun j : Fin b ↦ P.partialTranscript f (writeTurn r + 1) (hwrite_lt r hr)
        ⟨prefixBits msgB (writeTurn r) + j.1, by
          change prefixBits msgB (writeTurn r) + j.1 < prefixBits msgB (writeTurn r + 1)
          rw [prefixBits_succ _ (hwrite_lt r hr), hmsg_eq hr rfl]
          exact Nat.add_lt_add_left j.2 _⟩) =
        encodeFin (pcSuffix f (r + 1) x₀) := by
    intro f r
    induction r with
    | zero =>
      intro hr; funext j
      rw [P.partialTranscript_succ_ge f (writeTurn 0) (hwrite_lt 0 hr)
        (by change ¬ prefixBits msgB _ + j.1 < prefixBits msgB _; omega)]
      have ht : ∃ r' < k, (⟨writeTurn 0, hwrite_lt 0 hr⟩ : Fin (k * k)).1 = writeTurn r' :=
        ⟨0, hr, rfl⟩
      have hdiv0 : (⟨writeTurn 0, hwrite_lt 0 hr⟩ : Fin (k * k)).1 / k = 0 := hwrite_div 0 hr
      have hmod0 : cyclicSpeaker k (writeTurn 0) = ⟨k - 1, by omega⟩ :=
        Fin.ext (by simpa using hwrite_mod 0 hr)
      rw [pcSuffix_succ f x₀ hr, pcSuffix_zero]
      simp only [P, ht, ↓reduceDIte, hdiv0, hmod0]
      congr 1; apply Fin.ext; simp
    | succ r ih =>
      intro hr; have hr' : r < k := by omega
      funext j
      rw [P.partialTranscript_succ_ge f (writeTurn (r + 1)) (hwrite_lt (r + 1) hr)
        (by change ¬ prefixBits msgB _ + j.1 < prefixBits msgB _; omega)]
      have ht : ∃ r' < k, (⟨writeTurn (r + 1), hwrite_lt (r + 1) hr⟩ : Fin (k * k)).1 =
          writeTurn r' := ⟨r + 1, hr, rfl⟩
      have hdiv : (⟨writeTurn (r + 1), hwrite_lt (r + 1) hr⟩ : Fin (k * k)).1 / k = r + 1 :=
        hwrite_div (r + 1) hr
      have hmod : cyclicSpeaker k (writeTurn (r + 1)) = ⟨k - 1 - (r + 1), by omega⟩ :=
        Fin.ext (by simpa using hwrite_mod (r + 1) hr)
      have hhist_eq :
          (fun j' : Fin b ↦
            P.partialTranscript f (writeTurn (r + 1)) (le_of_lt (hwrite_lt (r + 1) hr))
              ⟨prefixBits msgB (writeTurn r) + j'.1, by
                have := hblock_le hr' (hwrite_step_lt r hr)
                change prefixBits msgB (writeTurn r) + j'.1 < prefixBits msgB (writeTurn (r + 1))
                omega⟩) = encodeFin (pcSuffix f (r + 1) x₀) := by
        funext j'
        exact (P.partialTranscript_mono f (hwrite_lt r hr') (le_of_lt (hwrite_lt (r + 1) hr))
          (hwrite_step_lt r hr) ⟨prefixBits msgB (writeTurn r) + j'.1, by
            change prefixBits msgB (writeTurn r) + j'.1 < prefixBits msgB (writeTurn r + 1)
            rw [prefixBits_succ _ (hwrite_lt r hr'), hmsg_eq hr' rfl]
            exact Nat.add_lt_add_left j'.2 _⟩).trans (congr_fun (ih hr') j')
      rw [pcSuffix_succ f x₀ hr]
      simp only [P, ht, ↓reduceDIte]
      rw [dite_eq_right_of_eq_false (eq_false (by rw [hdiv]; exact Nat.succ_ne_zero r))]
      have hbits_arg :
          (fun j' : Fin b ↦ P.partialTranscript f (writeTurn (r + 1))
            (le_of_lt (hwrite_lt (r + 1) hr))
            ⟨prefixBits msgB (writeTurn ((⟨writeTurn (r + 1), hwrite_lt (r + 1) hr⟩ :
              Fin (k * k)).1 / k - 1)) + j'.1, by
              have hdiv1 : (⟨writeTurn (r + 1), hwrite_lt (r + 1) hr⟩ :
                  Fin (k * k)).1 / k - 1 = r := by rw [hdiv]; omega
              have := hblock_le hr' (hwrite_step_lt r hr)
              change prefixBits msgB _ + j'.1 < prefixBits msgB (writeTurn (r + 1))
              rw [hdiv1]; omega⟩) = encodeFin (pcSuffix f (r + 1) x₀) := by
        funext j'
        have hdiv1 : (⟨writeTurn (r + 1), hwrite_lt (r + 1) hr⟩ : Fin (k * k)).1 / k - 1 = r := by
          rw [hdiv]; omega
        simpa only [hdiv1] using congr_fun hhist_eq j'
      rw [hbits_arg, decodeFin_encodeFin hn, hmod]
      congr 1; apply Fin.ext; simp
  refine ⟨P, ?_, fun f ↦ ?_⟩
  · change ∑ t : Fin (k * k), msgB t ≤ k * b
    rw [← Finset.sum_filter (p := fun t : Fin (k * k) ↦ ∃ r < k, t.1 = writeTurn r)
      (f := fun _ ↦ b) (s := Finset.univ), Finset.sum_const, smul_eq_mul]
    have hsplit : (Finset.univ : Finset (Fin (k * k))).filter
        (fun t ↦ ∃ r < k, t.1 = writeTurn r) =
        (Finset.range k).attach.image
          (fun r ↦ (⟨writeTurn r.1, hwrite_lt r.1 (Finset.mem_range.mp r.2)⟩ : Fin (k * k))) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_attach, Subtype.exists, Finset.mem_range]
      exact ⟨fun ⟨r, hr, htr⟩ ↦ ⟨r, hr, Fin.ext htr.symm⟩, fun ⟨r, hr, h⟩ ↦ ⟨r, hr, by rw [← h]⟩⟩
    rw [hsplit]
    exact Nat.mul_le_mul_right b
      (Finset.card_image_le.trans_eq (Finset.card_attach.trans (Finset.card_range k)))
  · change decodeFin hn _ = pointerChasing f x₀
    have hag : (fun j : Fin b ↦ P.transcript f
        ⟨prefixBits msgB (writeTurn (k - 1)) + j.1, by
          have := hblock_le (r := k - 1) (m := k * k) (by omega) (hwrite_lt (k - 1) (by omega))
          change prefixBits msgB (writeTurn (k - 1)) + j.1 < prefixBits msgB (k * k); omega⟩) =
        encodeFin (pointerChasing f x₀) := by
      funext j
      have h1 := P.partialTranscript_mono f (hwrite_lt (k - 1) (by omega)) le_rfl
        (hwrite_lt (k - 1) (by omega))
        ⟨prefixBits msgB (writeTurn (k - 1)) + j.1, by
          change prefixBits msgB (writeTurn (k - 1)) + j.1 < prefixBits msgB (writeTurn (k - 1) + 1)
          rw [prefixBits_succ _ (hwrite_lt (k - 1) (by omega)), hmsg_eq (by omega) rfl]
          exact Nat.add_lt_add_left j.2 _⟩
      have h2 := congr_fun (hround_val f (k - 1) (by omega)) j
      rw [show k - 1 + 1 = k by omega, pcSuffix_self] at h2
      exact h1.trans h2
    rw [hag, decodeFin_encodeFin hn]

/-- **Base case `k = 1` (`0` rounds) for pointer chasing**: `0` bits suffice deterministically. -/
theorem exists_cyclicProtocol_pointerChasing_one {n : ℕ} (x₀ : Fin n) :
    ∃ P : CyclicProtocol 1 0 (fun _ : Fin 1 ↦ Fin n → Fin n) (Fin n),
      P.totalBits = 0 ∧ ∀ f : Fin 1 → Fin n → Fin n, P.run f = pointerChasing f x₀ := by
  refine ⟨{
    msgBits := fun t ↦ Fin.elim0 (by simpa using t)
    send := fun t ↦ Fin.elim0 (by simpa using t)
    out := fun f₀ _ ↦ f₀ x₀ }, rfl, fun f ↦ ?_⟩
  rw [pointerChasing_succ, pointerChasing_zero]; rfl

/-- **Base case `p = 1` (`0` rounds) for `INTERSECT(SC_{n, 1})`**: no `0`-round randomized protocol
solves `setChasingIntersect` with error probability at most `1 / 3`. -/
theorem not_computesWithError_setChasingIntersect_one {n c : ℕ} (hn : 0 < n) {Ω : Type*}
    (P : RandomizedCyclicProtocol 2 0 (fun _ : Fin 2 ↦ Fin n → Finset (Fin n)) Bool c Ω) :
    ¬ P.ComputesWithError
      (fun F ↦ setChasingIntersect (fun i : Fin (2 * 1) ↦ F ⟨i.1, i.2⟩) {⟨0, hn⟩})
      (1 / 3 : ℝ≥0∞) := by
  intro hP
  let target : (Fin 2 → Fin n → Finset (Fin n)) → Bool :=
    fun F ↦ setChasingIntersect (fun i : Fin (2 * 1) ↦ F ⟨i.1, i.2⟩) {⟨0, hn⟩}
  let F₁ : Fin 2 → Fin n → Finset (Fin n) := fun _ _ ↦ {⟨0, hn⟩}
  let F₀ : Fin 2 → Fin n → Finset (Fin n) := fun i _ ↦ if i = 0 then ∅ else {⟨0, hn⟩}
  have hrun : ∀ ω ∈ P.dist.support, (P.proto ω).run F₁ = (P.proto ω).run F₀ := fun ω _ ↦
    (P.proto ω).run_congr rfl (funext fun j ↦ Fin.elim0 (by simpa using j))
  have hv₁ : target F₁ = true := by
    refine (setChasingIntersect_eq_true_iff _ _).mpr ⟨⟨0, hn⟩, Finset.mem_inter.mpr ?_⟩
    simp [setChasingLeft, setChasingRight, setChasing_succ, setChasing_zero, F₁]
  have hv₀ : target F₀ = false := by
    rw [← Bool.not_eq_true, setChasingIntersect_eq_true_iff]
    rintro ⟨z, hz⟩
    simp [setChasingLeft, setChasing_succ, setChasing_zero, F₀] at hz
  have h1 := P.one_le_errorProb_add_of_run_eq target hrun (by rw [hv₁, hv₀]; decide)
  have hsum : (1 : ℝ≥0∞) ≤ (1 / 3 : ℝ≥0∞) + (1 / 3 : ℝ≥0∞) := h1.trans (add_le_add (hP F₁) (hP F₀))
  have hmul := mul_le_mul_right hsum (3 : ℝ≥0∞)
  have hcancel : (3 : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) = 1 := by
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [mul_one, mul_add, hcancel] at hmul
  norm_num at hmul

/-- **Unconditional nontriviality (`1 ≤ c`) for `INTERSECT(SC_{n, k})`**: for `n ≥ 1` and `k ≥ 2`,
no `0`-bit randomized `(2 * k, k - 1)`-round cyclic protocol computes `setChasingIntersect` with
error probability at most `1 / 10`. -/
theorem one_le_cost_of_computesWithError_setChasingIntersect {n k c : ℕ}
    (hk : 2 ≤ k) [NeZero (2 * k)] {Ω : Type*} (u₀ : Fin n)
    (P : RandomizedCyclicProtocol (2 * k) (k - 1) (fun _ : Fin (2 * k) ↦ Fin n → Finset (Fin n))
      Bool c Ω)
    (hP : P.ComputesWithError (fun F ↦ setChasingIntersect F {u₀}) (1 / 10 : ℝ≥0∞)) :
    1 ≤ c := by
  by_contra hc
  have hc0 : c = 0 := by omega
  let F₁ : Fin (2 * k) → Fin n → Finset (Fin n) := fun _ _ ↦ {u₀}
  let F₀ : Fin (2 * k) → Fin n → Finset (Fin n) := fun i _ ↦ if i = 0 then ∅ else {u₀}
  have hmem_const : ∀ m : ℕ,
      u₀ ∈ setChasing (fun _ : Fin m ↦ (fun _ : Fin n ↦ ({u₀} : Finset (Fin n)))) {u₀} := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [setChasing_succ, mem_setLift]; exact ⟨u₀, ih, Finset.mem_singleton_self u₀⟩
  have hval₁ : setChasingIntersect F₁ {u₀} = true :=
    (setChasingIntersect_eq_true_iff _ _).mpr ⟨u₀, Finset.mem_inter.mpr ⟨hmem_const k,
      hmem_const k⟩⟩
  have hval₀ : setChasingIntersect F₀ {u₀} = false := by
    rw [← Bool.not_eq_true, setChasingIntersect_eq_true_iff]
    rintro ⟨z, hz⟩
    have hL : setChasingLeft F₀ {u₀} = ∅ := by
      simp only [setChasingLeft]
      generalize hg : (fun i : Fin k ↦ F₀ ⟨i.1, by omega⟩) = g
      have hg0 : g ⟨0, by omega⟩ = fun _ ↦ ∅ := by rw [← hg]; funext v; simp [F₀]
      clear hg
      cases k with
      | zero => omega
      | succ m =>
        rw [setChasing_succ]; ext w
        have hg0' : g 0 = fun _ ↦ ∅ := hg0
        simp [mem_setLift, hg0']
    rw [hL] at hz; simp at hz
  have hlast_ne : lastPlayer (2 * k) ≠ 0 := fun heq ↦ by
    have hval := congr_arg Fin.val heq
    simp only [val_lastPlayer, Fin.val_zero] at hval; omega
  have hrun : ∀ ω ∈ P.dist.support, (P.proto ω).run F₁ = (P.proto ω).run F₀ := fun ω hω ↦ by
    have htot0 : (P.proto ω).totalBits = 0 := Nat.eq_zero_of_le_zero (hc0 ▸ P.cost_le ω hω)
    have hpref0 : prefixBits (P.proto ω).msgBits ((k - 1) * (2 * k)) = 0 := by
      rw [CyclicProtocol.prefixBits_total, htot0]
    exact (P.proto ω).run_congr (by funext v; simp [F₁, F₀, hlast_ne])
      (funext fun j ↦ False.elim (Nat.not_lt_zero j.1 (lt_of_lt_of_eq j.2 hpref0)))
  have h1 := P.one_le_errorProb_add_of_run_eq (fun F ↦ setChasingIntersect F {u₀}) hrun
    (by rw [hval₁, hval₀]; decide)
  have hsum : (1 : ℝ≥0∞) ≤ (1 / 10 : ℝ≥0∞) + (1 / 10 : ℝ≥0∞) :=
    h1.trans (add_le_add (hP F₁) (hP F₀))
  have hmul := mul_le_mul_right hsum (10 : ℝ≥0∞)
  have hcancel : (10 : ℝ≥0∞) * (1 / 10 : ℝ≥0∞) = 1 := by
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [mul_one, mul_add, hcancel] at hmul
  norm_num at hmul

/-- **Round sharpness (`k = 2`, `2` full rounds) for `INTERSECT(SC_{n, 2})`**: with `2` full cyclic
rounds across `4` players, `4 * n` bits compute `setChasingIntersect` deterministically. -/
theorem exists_cyclicProtocol_setChasingIntersect_two_rounds {n : ℕ} (u₀ : Fin n) :
    ∃ P : CyclicProtocol 4 2 (fun _ : Fin 4 ↦ Fin n → Finset (Fin n)) Bool,
      P.totalBits ≤ 4 * n ∧
        ∀ F : Fin 4 → Fin n → Finset (Fin n),
          P.run F = setChasingIntersect (p := 2) F {u₀} := by
  let msgB : Fin (2 * 4) → ℕ :=
    fun t ↦ if t.1 = 1 ∨ t.1 = 3 ∨ t.1 = 4 ∨ t.1 = 6 then n else 0
  have hp0 : prefixBits msgB 0 = 0 := prefixBits_zero msgB
  have hp1 : prefixBits msgB 1 = 0 := by rw [prefixBits_succ _ (by decide), hp0]; simp [msgB]
  have hp2 : prefixBits msgB 2 = n := by rw [prefixBits_succ _ (by decide), hp1]; simp [msgB]
  have hp3 : prefixBits msgB 3 = n := by rw [prefixBits_succ _ (by decide), hp2]; simp [msgB]
  have hp4 : prefixBits msgB 4 = 2 * n := by
    rw [prefixBits_succ _ (by decide), hp3]; simp [msgB]; omega
  have hp5 : prefixBits msgB 5 = 3 * n := by
    rw [prefixBits_succ _ (by decide), hp4]; simp [msgB]; omega
  have hp6 : prefixBits msgB 6 = 3 * n := by rw [prefixBits_succ _ (by decide), hp5]; simp [msgB]
  have hp7 : prefixBits msgB 7 = 4 * n := by
    rw [prefixBits_succ _ (by decide), hp6]; simp [msgB]; omega
  have hp8 : prefixBits msgB 8 = 4 * n := by rw [prefixBits_succ _ (by decide), hp7]; simp [msgB]
  let decodeSet : ∀ {m : ℕ} (off : ℕ), off + n ≤ m → (Fin m → Bool) → Finset (Fin n) :=
    fun off _ hist ↦ Finset.univ.filter fun u : Fin n ↦ hist ⟨off + u.1, by omega⟩
  let P : CyclicProtocol 4 2 (fun _ : Fin 4 ↦ Fin n → Finset (Fin n)) Bool :=
    { msgBits := msgB
      send := fun t f hist ↦
        if ht1 : t.1 = 1 then
          fun j ↦ decide (⟨j.1, lt_of_lt_of_eq j.2 (by simp [msgB, ht1])⟩ ∈ f u₀)
        else if ht3 : t.1 = 3 then
          fun j ↦ decide (⟨j.1, lt_of_lt_of_eq j.2 (by simp [msgB, ht3])⟩ ∈ f u₀)
        else if ht4 : t.1 = 4 then
          let s1 := decodeSet 0 (by rw [ht4, hp4]; omega) hist
          fun j ↦ decide (⟨j.1, lt_of_lt_of_eq j.2 (by simp [msgB, ht4])⟩ ∈ setLift f s1)
        else if ht6 : t.1 = 6 then
          let s3 := decodeSet n (by rw [ht6, hp6]; omega) hist
          fun j ↦ decide (⟨j.1, lt_of_lt_of_eq j.2 (by simp [msgB, ht6])⟩ ∈ setLift f s3)
        else
          fun j ↦ False.elim (Nat.not_lt_zero j.1 (lt_of_lt_of_eq j.2 (by
            simp [msgB, ht1, ht3, ht4, ht6])))
      out := fun _ fullHist ↦
        let sL := decodeSet (2 * n) (by rw [hp8]; omega) fullHist
        let sR := decodeSet (3 * n) (by rw [hp8]; omega) fullHist
        decide ((sL ∩ sR).Nonempty) }
  refine ⟨P, by rw [← P.prefixBits_total]; exact le_of_eq hp8, fun F ↦ ?_⟩
  have hturn1 : ∀ u : Fin n,
      P.partialTranscript F 2 (by decide) ⟨u.1, by rw [hp2]; exact u.2⟩ = decide (u ∈ F 1 u₀) := by
    intro u
    rw [P.partialTranscript_succ_ge F 1 (by decide)
      (by change ¬ u.1 < prefixBits msgB 1; omega)]
    have hc1 : cyclicSpeaker 4 1 = 1 := rfl
    simp only [P, hc1, ↓reduceDIte]
    congr 1
  have hturn3 : ∀ u : Fin n,
      P.partialTranscript F 4 (by decide) ⟨n + u.1, by rw [hp4]; omega⟩ = decide (u ∈ F 3 u₀) := by
    intro u
    rw [P.partialTranscript_succ_ge F 3 (by decide)
      (by change ¬ n + u.1 < prefixBits msgB 3; rw [hp3]; omega)]
    have hc3 : cyclicSpeaker 4 3 = 3 := rfl
    simp only [P, hc3]
    split_ifs with h1
    · omega
    · congr 1; apply Fin.ext
      change n + u.1 - prefixBits msgB 3 = u.1
      rw [hp3, Nat.add_sub_cancel_left]
  have hs1_4 : decodeSet 0 (by rw [hp4]; omega) (P.partialTranscript F 4 (by decide)) = F 1 u₀ := by
    ext u
    simp only [decodeSet, Finset.mem_filter, Finset.mem_univ, true_and, Nat.zero_add]
    have hag : P.partialTranscript F 4 (by decide) ⟨u.1, by rw [hp4]; omega⟩ =
        P.partialTranscript F 2 (by decide) ⟨u.1, by rw [hp2]; exact u.2⟩ :=
      P.partialTranscript_mono F (by decide) (by decide) (by decide) ⟨u.1, by rw [hp2]; exact u.2⟩
    rw [hag, hturn1 u, decide_eq_true_eq]
  have hs3_6 : decodeSet n (by rw [hp6]; omega) (P.partialTranscript F 6 (by decide)) = F 3 u₀ := by
    ext u
    simp only [decodeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hag : P.partialTranscript F 6 (by decide) ⟨n + u.1, by rw [hp6]; omega⟩ =
        P.partialTranscript F 4 (by decide) ⟨n + u.1, by rw [hp4]; omega⟩ :=
      P.partialTranscript_mono F (by decide) (by decide) (by decide) ⟨n + u.1, by rw [hp4]; omega⟩
    rw [hag, hturn3 u, decide_eq_true_eq]
  have hturn4 : ∀ u : Fin n,
      P.partialTranscript F 5 (by decide) ⟨2 * n + u.1, by rw [hp5]; omega⟩ =
        decide (u ∈ setChasingLeft (p := 2) F {u₀}) := by
    intro u
    rw [P.partialTranscript_succ_ge F 4 (by decide)
      (by change ¬ 2 * n + u.1 < prefixBits msgB 4; rw [hp4]; omega)]
    have hc4 : cyclicSpeaker 4 4 = 0 := rfl
    simp only [P, hc4]
    split_ifs with h1 h3
    · omega
    · omega
    · change decide (_ ∈ setLift (F 0) (decodeSet 0
        (by change 0 + n ≤ prefixBits msgB 4; rw [hp4]; omega)
        (P.partialTranscript F 4 (by decide)))) = _
      have hidx : (⟨2 * n + u.1 - prefixBits msgB 4, by rw [hp4]; omega⟩ : Fin n) = u := by
        apply Fin.ext; change 2 * n + u.1 - prefixBits msgB 4 = u.1; rw [hp4]; omega
      have hL : setChasingLeft (p := 2) F {u₀} = setLift (F 0) (F 1 u₀) := by
        simp only [setChasingLeft, setChasing_succ, setChasing_zero, setLift_singleton]; rfl
      rw [hs1_4, hidx, hL]
  have hturn6 : ∀ u : Fin n,
      P.partialTranscript F 7 (by decide) ⟨3 * n + u.1, by rw [hp7]; omega⟩ =
        decide (u ∈ setChasingRight (p := 2) F {u₀}) := by
    intro u
    rw [P.partialTranscript_succ_ge F 6 (by decide)
      (by change ¬ 3 * n + u.1 < prefixBits msgB 6; rw [hp6]; omega)]
    have hc6 : cyclicSpeaker 4 6 = 2 := rfl
    simp only [P, hc6]
    split_ifs with h1 h3 h4
    · omega
    · omega
    · omega
    · change decide (_ ∈ setLift (F 2) (decodeSet n
        (by change n + n ≤ prefixBits msgB 6; rw [hp6]; omega)
        (P.partialTranscript F 6 (by decide)))) = _
      have hidx : (⟨3 * n + u.1 - prefixBits msgB 6, by rw [hp6]; omega⟩ : Fin n) = u := by
        apply Fin.ext; change 3 * n + u.1 - prefixBits msgB 6 = u.1; rw [hp6]; omega
      have hR : setChasingRight (p := 2) F {u₀} = setLift (F 2) (F 3 u₀) := by
        simp only [setChasingRight, setChasing_succ, setChasing_zero, setLift_singleton]; rfl
      rw [hs3_6, hidx, hR]
  have hsL : decodeSet (2 * n) (by rw [hp8]; omega) (P.transcript F) =
      setChasingLeft (p := 2) F {u₀} := by
    ext u
    simp only [decodeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hag : P.partialTranscript F 8 (by decide) ⟨2 * n + u.1, by rw [hp8]; omega⟩ =
        P.partialTranscript F 5 (by decide) ⟨2 * n + u.1, by rw [hp5]; omega⟩ :=
      P.partialTranscript_mono F (by decide) (by decide) (by decide)
        ⟨2 * n + u.1, by rw [hp5]; omega⟩
    change P.partialTranscript F 8 (by decide) ⟨2 * n + u.1, _⟩ = true ↔ _
    rw [hag, hturn4 u, decide_eq_true_eq]
  have hsR : decodeSet (3 * n) (by rw [hp8]; omega) (P.transcript F) =
      setChasingRight (p := 2) F {u₀} := by
    ext u
    simp only [decodeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hag : P.partialTranscript F 8 (by decide) ⟨3 * n + u.1, by rw [hp8]; omega⟩ =
        P.partialTranscript F 7 (by decide) ⟨3 * n + u.1, by rw [hp7]; omega⟩ :=
      P.partialTranscript_mono F (by decide) (by decide) (by decide)
        ⟨3 * n + u.1, by rw [hp7]; omega⟩
    change P.partialTranscript F 8 (by decide) ⟨3 * n + u.1, _⟩ = true ↔ _
    rw [hag, hturn6 u, decide_eq_true_eq]
  change decide ((decodeSet (2 * n)
      (by change 2 * n + n ≤ prefixBits msgB 8; rw [hp8]; omega) (P.transcript F) ∩
    decodeSet (3 * n)
      (by change 3 * n + n ≤ prefixBits msgB 8; rw [hp8]; omega) (P.transcript F)).Nonempty) = _
  rw [hsL, hsR, Bool.eq_iff_iff, decide_eq_true_eq, setChasingIntersect_eq_true_iff]

/-- **Two-player one-round deterministic pointer-chasing lower bound (`k = 2, r = 1`)**: every
deterministic `(2, 1)`-round cyclic protocol computing `pointerChasing f x₀` satisfies
`n ^ n ≤ 2 ^ P.totalBits`. -/
theorem two_player_pointerChasing_card_le {n : ℕ} (x₀ : Fin n)
    (P : CyclicProtocol 2 1 (fun _ : Fin 2 ↦ Fin n → Fin n) (Fin n))
    (hP : ∀ f : Fin 2 → Fin n → Fin n, P.run f = pointerChasing f x₀) :
    n ^ n ≤ 2 ^ P.totalBits := by
  let enc : (Fin n → Fin n) → (Fin (P.msgBits 0) → Bool) :=
    fun g ↦ P.send 0 g (P.partialTranscript (fun _ ↦ g) 0 (Nat.zero_le _))
  have hinj : Function.Injective enc := by
    intro g₁ g₂ hEq
    funext u
    let f₁ : Fin 2 → Fin n → Fin n := fun i ↦ if i = 0 then g₁ else fun _ ↦ u
    let f₂ : Fin 2 → Fin n → Fin n := fun i ↦ if i = 0 then g₂ else fun _ ↦ u
    have hrun₁ : P.run f₁ = g₁ u := by
      rw [hP f₁, pointerChasing_succ, pointerChasing_succ, pointerChasing_zero]; rfl
    have hrun₂ : P.run f₂ = g₂ u := by
      rw [hP f₂, pointerChasing_succ, pointerChasing_succ, pointerChasing_zero]; rfl
    have htr₁ : P.partialTranscript f₁ 1 (by decide) = P.partialTranscript f₂ 1 (by decide) := by
      funext i
      have hi : ¬ i.1 < prefixBits P.msgBits 0 := by simp
      rw [P.partialTranscript_succ_ge f₁ 0 (by decide) hi,
        P.partialTranscript_succ_ge f₂ 0 (by decide) hi]
      have hp₁ : P.partialTranscript f₁ 0 (Nat.zero_le _) =
          P.partialTranscript (fun _ ↦ g₁) 0 (Nat.zero_le _) :=
        funext fun j ↦ Fin.elim0 (by simpa using j)
      have hp₂ : P.partialTranscript f₂ 0 (Nat.zero_le _) =
          P.partialTranscript (fun _ ↦ g₂) 0 (Nat.zero_le _) :=
        funext fun j ↦ Fin.elim0 (by simpa using j)
      have hf₁0 : f₁ (cyclicSpeaker 2 0) = g₁ := rfl
      have hf₂0 : f₂ (cyclicSpeaker 2 0) = g₂ := rfl
      rw [hf₁0, hf₂0, hp₁, hp₂]
      exact congr_fun hEq _
    have htr₂ : P.transcript f₁ = P.transcript f₂ := by
      funext i
      by_cases hi : i.1 < prefixBits P.msgBits 1
      · change P.partialTranscript f₁ 2 le_rfl i = P.partialTranscript f₂ 2 le_rfl i
        rw [P.partialTranscript_succ_lt f₁ 1 (by decide) hi,
          P.partialTranscript_succ_lt f₂ 1 (by decide) hi, htr₁]
      · change P.partialTranscript f₁ 2 le_rfl i = P.partialTranscript f₂ 2 le_rfl i
        rw [P.partialTranscript_succ_ge f₁ 1 (by decide) hi,
          P.partialTranscript_succ_ge f₂ 1 (by decide) hi]
        have hf₁1 : f₁ (cyclicSpeaker 2 1) = fun _ ↦ u := rfl
        have hf₂1 : f₂ (cyclicSpeaker 2 1) = fun _ ↦ u := rfl
        rw [hf₁1, hf₂1, htr₁]
    exact hrun₁.symm.trans ((P.run_congr (x := f₁) (y := f₂) rfl htr₂).trans hrun₂)
  have hcard := Fintype.card_le_of_injective enc hinj
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  exact hcard.trans (Nat.pow_le_pow_right (by norm_num) (P.msgBits_le_totalBits 0))

end PointerAndSetChasing

end CslibFrontier.Communication
