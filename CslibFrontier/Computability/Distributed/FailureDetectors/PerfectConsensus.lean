/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.FailureDetectors.Consensus

/-!
# Perfect Failure Detector Consensus for Arbitrary Crash Budgets

Proves Chandra and Toueg's Perfect (`P`) failure detector consensus solvability for arbitrary crash
budgets `t : ℕ` in `FDAsyncRoundProtocol` (contrasting with the `2 * t < |P|` impossibility
threshold of `◇P` in `CslibFrontier.Computability.Distributed.FailureDetectors.Consensus`).
-/

public section

namespace CslibFrontier.Computability.Distributed.FailureDetectors

open Cslib.Distributed.FailureDetectors

/-- Exact crash-detection oracle history reporting `F t` to every process at tick `t`. -/
def exactCrashDetector {P : Type*} (F : FailurePattern P) : DetectorHistory P :=
  fun _ t ↦ F t

/-- On any finite process set `P`, `exactCrashDetector F` satisfies `IsPerfect F`. -/
theorem isPerfect_exactCrashDetector {P : Type*} [Finite P] (F : FailurePattern P) :
    IsPerfect F (exactCrashDetector F) := by
  obtain ⟨t₀, ht₀⟩ := F.exists_stabilize
  exact ⟨⟨t₀, fun p hp _ _ t' ht' ↦ ((ht₀ t' ht').1 p).mpr hp⟩,
    fun _ _ hp _ _ ↦ hp⟩

/-- Local process state for `perfectFDProtocol`: stores the process's `initial` input value and
its optional write-once `decided` output value. -/
structure PerfectFDState (V : Type*) where
  /-- Process's initial input value broadcast in subround `0`. -/
  initial : V
  /-- Latched consensus decision (`none` before subround `1`). -/
  decided : Option V

/-- Deterministic 1-subround consensus protocol for `StrongAccuracy` / `IsPerfect` failure
detectors (after).
-/
def perfectFDProtocol (P V : Type*) [DecidableEq P] (procs : List P) :
    FDAsyncRoundProtocol P V (PerfectFDState V) V where
  init _ v := ⟨v, none⟩
  send _ _ s _ := s.initial
  update k _ s _ m := ⟨s.initial, if k = 0 then procs.dedup.findSome? m else s.decided⟩
  output _ s := s.decided

private theorem exists_of_findSome?_eq_some {α β : Type*} {f : α → Option β} :
    ∀ {l : List α} {b : β}, l.findSome? f = some b → ∃ a ∈ l, f a = some b
  | [], _, h => by nomatch h
  | a :: rest, b, h => by
      simp only [List.findSome?] at h
      cases hfa : f a with
      | some b' =>
          simp only [hfa] at h
          obtain rfl : b' = b := Option.some.inj h
          exact ⟨a, List.mem_cons_self, hfa⟩
      | none =>
          simp only [hfa] at h
          obtain ⟨a', ha', hfa'⟩ := exists_of_findSome?_eq_some h
          exact ⟨a', List.mem_cons_of_mem a ha', hfa'⟩

private theorem perfectFDProtocol_decision_zero {P V : Type*} [DecidableEq P] (procs : List P)
    (F : FailurePattern P) (H : DetectorHistory P)
    (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) (x : P → V) (p : P) :
    (perfectFDProtocol P V procs).decision F H tick deliver x 0 p = none :=
  rfl

private theorem perfectFDProtocol_decision_pos {P V : Type*} [DecidableEq P] (procs : List P)
    (F : FailurePattern P) (H : DetectorHistory P)
    (tick : ℕ → ℕ) (deliver : ℕ → P → P → Bool) (x : P → V)
    {k : ℕ} (hk : 1 ≤ k) {p : P} (hp : p ∈ F.Correct) :
    (perfectFDProtocol P V procs).decision F H tick deliver x k p =
      procs.dedup.findSome?
        ((perfectFDProtocol P V procs).incoming F tick deliver
          ((perfectFDProtocol P V procs).state F H tick deliver x 0) 0 p) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  induction m with
  | zero =>
      change ((perfectFDProtocol P V procs).state F H tick deliver x 1 p).decided = _
      simp [FDAsyncRoundProtocol.state, hp (tick 0), perfectFDProtocol]
  | succ m ihm =>
      change ((perfectFDProtocol P V procs).state F H tick deliver x (m + 2) p).decided = _
      simp only [FDAsyncRoundProtocol.state, hp (tick (m + 1)), ↓reduceIte,
        perfectFDProtocol, Nat.succ_ne_zero]
      exact ihm (by omega)

private theorem perfectFDProtocol_incoming_zero_eq {P V : Type*} [Fintype P] [DecidableEq P]
    (procs : List P) {F : FailurePattern P} {H : DetectorHistory P} {t : ℕ}
    {tick : ℕ → ℕ} {deliver : ℕ → P → P → Bool}
    (hadm : AdmissibleFDNetwork F H t tick deliver)
    (hSA : StrongAccuracy F H) (x : P → V) {p : P} (hp : p ∈ F.Correct) :
    (perfectFDProtocol P V procs).incoming F tick deliver
        ((perfectFDProtocol P V procs).state F H tick deliver x 0) 0 p =
      fun q ↦ if q ∉ F (tick 0) then some (x q) else none := by
  funext q
  simp only [FDAsyncRoundProtocol.incoming, FDAsyncRoundProtocol.state, perfectFDProtocol]
  by_cases hq : q ∈ F (tick 0)
  · simp [hq]
  · have hns : q ∉ H p (tick 0) := hSA (tick 0) q hq p (hp (tick 0))
    have hdel : deliver 0 q p = true := hadm.deliver_of_notMem hp hns
    simp [hq, hdel]

/-- Whenever `procs` enumerates all processes in `P`, `perfectFDProtocol P V procs` solves
`t`-resilient consensus under `StrongAccuracy` for every fault budget `t : ℕ`. -/
theorem solvesFDAsyncRoundConsensus_perfectFDProtocol_strongAccuracy
    {P V : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (t : ℕ) :
    (perfectFDProtocol P V procs).SolvesFDAsyncRoundConsensus t StrongAccuracy where
  irrevocable F _ H tick deliver x _ _ k₁ k₂ hk p hp v hdec := by
    rcases Nat.eq_zero_or_pos k₁ with rfl | hk₁
    · rw [perfectFDProtocol_decision_zero] at hdec; nomatch hdec
    · rw [perfectFDProtocol_decision_pos procs F H tick deliver x hk₁ hp] at hdec
      rw [perfectFDProtocol_decision_pos procs F H tick deliver x (hk₁.trans_le hk) hp]
      exact hdec
  agreement F _ H tick deliver x hadm hSA k₁ k₂ p₁ hp₁ p₂ hp₂ v₁ v₂ h₁ h₂ := by
    rcases Nat.eq_zero_or_pos k₁ with rfl | hk₁
    · rw [perfectFDProtocol_decision_zero] at h₁; nomatch h₁
    · rcases Nat.eq_zero_or_pos k₂ with rfl | hk₂
      · rw [perfectFDProtocol_decision_zero] at h₂; nomatch h₂
      · rw [perfectFDProtocol_decision_pos procs F H tick deliver x hk₁ hp₁,
          perfectFDProtocol_incoming_zero_eq procs hadm hSA x hp₁] at h₁
        rw [perfectFDProtocol_decision_pos procs F H tick deliver x hk₂ hp₂,
          perfectFDProtocol_incoming_zero_eq procs hadm hSA x hp₂] at h₂
        exact Option.some.inj (h₁.symm.trans h₂)
  validity F _ H tick deliver x hadm hSA k p hp v hdec := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [perfectFDProtocol_decision_zero] at hdec; nomatch hdec
    · rw [perfectFDProtocol_decision_pos procs F H tick deliver x hk hp,
        perfectFDProtocol_incoming_zero_eq procs hadm hSA x hp] at hdec
      obtain ⟨q, _, hq⟩ := exists_of_findSome?_eq_some hdec
      split_ifs at hq
      exact ⟨q, Option.some.inj hq⟩
  termination F _ H tick deliver x hadm hSA p hp := by
    refine ⟨1, ?_⟩
    rw [perfectFDProtocol_decision_pos procs F H tick deliver x le_rfl hp,
      perfectFDProtocol_incoming_zero_eq procs hadm hSA x hp]
    exact List.findSome?_isSome_iff.mpr
      ⟨p, List.mem_dedup.mpr (hprocs p), by simp [hp (tick 0)]⟩

/-- `perfectFDProtocol` solves `t`-resilient consensus under `IsPerfect` (`P`) for every `t : ℕ`. -/
theorem solvesFDAsyncRoundConsensus_perfectFDProtocol
    {P V : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (t : ℕ) :
    (perfectFDProtocol P V procs).SolvesFDAsyncRoundConsensus t IsPerfect :=
  (solvesFDAsyncRoundConsensus_perfectFDProtocol_strongAccuracy hprocs t).mono
    fun _ _ _ hP ↦ hP.2

/-- Unconditional solvability of `t`-resilient consensus under `IsPerfect` (`P`) for every
`t : ℕ`. -/
theorem exists_solvesFDAsyncRoundConsensus_perfect.{u, v} (P : Type u) (V : Type v)
    [Fintype P] [DecidableEq P] (t : ℕ) :
    ∃ (S M : Type v) (π : FDAsyncRoundProtocol P V S M),
      π.SolvesFDAsyncRoundConsensus t IsPerfect := by
  let e := Fintype.equivFin P
  let procs : List P := List.ofFn e.symm
  have hprocs : ∀ p : P, p ∈ procs := fun p ↦
    List.mem_ofFn.mpr ⟨e p, Equiv.symm_apply_apply e p⟩
  exact ⟨PerfectFDState V, V, perfectFDProtocol P V procs,
    solvesFDAsyncRoundConsensus_perfectFDProtocol hprocs t⟩

end CslibFrontier.Computability.Distributed.FailureDetectors
