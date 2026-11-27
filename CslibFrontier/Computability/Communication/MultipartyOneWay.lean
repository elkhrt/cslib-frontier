/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.RandomizedCost
public import CslibFrontier.Computability.Streaming.MultiPass
public import CslibFrontier.Probability.IID

import CslibFrontier.Foundations.Data.ENat.IInf
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiparty Number-in-Hand, One-Way, and Simultaneous Communication Complexity

This module develops textbook foundations for multiparty number-in-hand (NIH) communication
complexity, one-way (sententious) communication protocols, simultaneous message-passing protocols,
worst-case contiguous input partitions, and their quantitative connections to single-pass and
multi-pass data stream algorithms.

## Main definitions

* `Cslib.Communication.IsSymmetricParty`: invariance of a `k`-argument function under
  coordinate permutations `Equiv.Perm (Fin k)`.
* `Cslib.Communication.NIHProtocol`: deterministic `t`-party number-in-hand protocol
  trees with worst-case depth, leaf count, leaf rectangle predicates, and `Cslib.RandomizedCost`
  model instance.
* `Cslib.Communication.OneWayProtocol`: deterministic `(t + 1)`-player one-way
  number-in-hand protocols in which players `0, …, t - 1` pass messages sequentially and the final
  player outputs locally without an extra announcement bit.
* `Cslib.Communication.SimProtocol`: deterministic `(t + 1)`-player simultaneous
  protocols in which the first `t` players send independent messages to the final referee player.
* `Cslib.Communication.ContiguousPartition`: monotone boundary indices
  `0 = cut 0 ≤ cut 1 ≤ … ≤ cut t = m` partitioning an `m`-item input stream among `t` players.

## Main results

* `Cslib.Communication.NIHProtocol.leafCount_le_two_pow_depth`,
  `Cslib.Communication.NIHProtocol.isRectangle_leafSet`: a deterministic `t`-party
  NIH protocol of depth `d` partitions the input space into at most `2 ^ d` monochromatic
  combinatorial rectangles.
* `Cslib.Communication.OneWayProtocol.ofStreaming`,
  `Cslib.Communication.oneWay_cost_le_of_spaceLE`: simulating a single-pass `b`-bit
  streaming algorithm across any `(t + 1)`-block contiguous partition uses at most `t * b` bits of
  one-way communication.
* `Cslib.Communication.streaming_spaceLE_of_twoPartyOneWay`: conversely, if every
  2-block contiguous partition of an `m`-element domain (`m ≥ 1`) admits a deterministic 2-player
  one-way protocol of cost at most `c`, then a deterministic single-pass streaming algorithm
  computes `f` in at most `c + Nat.clog 2 m` bits of memory.
* `Cslib.Communication.iid_strictMajority_odd_tail`: strict-majority tail bound
  `δ * (4 * δ * (1 - δ)) ^ r` for `2 * r + 1` independent Bernoulli error indicators of rate at
  most `δ ≤ 1 / 2`.
-/

public section

namespace Cslib.Communication

open Finset Cslib Cslib.Probability

/-! ### 1. Symmetric Multiparty Functions and Combinatorial Rectangles -/

section SymmetryAndRectangles

variable {α β : Type*} {k : ℕ}

/-- A `k`-argument function `f : (Fin k → α) → β` is symmetric if permuting its coordinates by any
`σ : Equiv.Perm (Fin k)` leaves its value unchanged. -/
@[expose]
def IsSymmetricParty (f : (Fin k → α) → β) : Prop :=
  ∀ (x : Fin k → α) (σ : Equiv.Perm (Fin k)), f (fun i ↦ x (σ i)) = f x

/-- Logical characterization of `IsSymmetricParty`. -/
theorem isSymmetricParty_iff {f : (Fin k → α) → β} :
    IsSymmetricParty f ↔ ∀ (x : Fin k → α) (σ : Equiv.Perm (Fin k)), f (fun i ↦ x (σ i)) = f x :=
  Iff.rfl

/-- A subset `R` of a product input space `∀ i : Fin k, X i` is a combinatorial rectangle if it is
the Cartesian product `Set.pi Set.univ S` of per-player subsets `S i : Set (X i)`. -/
@[expose]
def IsProductRectangle {X : Fin k → Type*} (R : Set (∀ i, X i)) : Prop :=
  ∃ S : ∀ i, Set (X i), R = Set.univ.pi S

/-- The whole product space is a combinatorial rectangle. -/
theorem isProductRectangle_univ {X : Fin k → Type*} :
    IsProductRectangle (Set.univ : Set (∀ i, X i)) :=
  ⟨fun _ ↦ Set.univ, by ext x; simp⟩

/-- The intersection of a combinatorial rectangle with a single-coordinate slice remains a
combinatorial rectangle. -/
theorem IsProductRectangle.inter_coord {X : Fin k → Type*} {R : Set (∀ i, X i)}
    (hR : IsProductRectangle R) (p : Fin k) (T : Set (X p)) :
    IsProductRectangle (R ∩ {x | x p ∈ T}) := by
  classical
  rcases hR with ⟨S, rfl⟩
  refine ⟨fun i ↦ if h : i = p then S i ∩ (h ▸ T) else S i, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq]
  refine ⟨fun ⟨hxS, hxp⟩ i ↦ ?_, fun hx ↦ ⟨fun i ↦ ?_, ?_⟩⟩
  · split_ifs with h
    · subst h
      exact ⟨hxS i, hxp⟩
    · exact hxS i
  · specialize hx i
    split_ifs at hx with h
    · exact hx.1
    · exact hx
  · have hxp := hx p
    simp only [↓reduceDIte] at hxp
    exact hxp.2

end SymmetryAndRectangles

/-! ### 2. Interactive Number-in-Hand Protocol Trees -/

section NIHProtocol

variable {t : ℕ} {X : Fin t → Type*} {Z : Type*}

/-- A deterministic `t`-party number-in-hand (NIH) communication protocol over input family `X` and
output type `Z`. At each internal node, a designated speaker `player : Fin t` broadcasts one bit
computed solely from `x player`. -/
inductive NIHProtocol (X : Fin t → Type*) (Z : Type*) where
  /-- Terminate and output `z`. -/
  | output (z : Z)
  /-- Player `player` broadcasts `bit (x player)` and execution branches to `ifFalse` or
  `ifTrue`. -/
  | send (player : Fin t) (bit : X player → Bool) (ifFalse ifTrue : NIHProtocol X Z)

namespace NIHProtocol

/-- Evaluate `P` on input profile `x : ∀ i, X i`. -/
@[expose] def run : NIHProtocol X Z → (∀ i, X i) → Z
  | output z, _ => z
  | send p bit p₀ p₁, x => cond (bit (x p)) (p₁.run x) (p₀.run x)

/-- Worst-case communication cost (tree depth) of `P`. -/
@[expose] def depth : NIHProtocol X Z → ℕ
  | output _ => 0
  | send _ _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- Number of leaves of `P`. -/
@[expose] def leafCount : NIHProtocol X Z → ℕ
  | output _ => 1
  | send _ _ p₀ p₁ => p₀.leafCount + p₁.leafCount

@[simp]
theorem run_output (z : Z) (x : ∀ i, X i) : (output z : NIHProtocol X Z).run x = z := rfl

@[simp]
theorem run_send (p : Fin t) (bit : X p → Bool) (p₀ p₁ : NIHProtocol X Z) (x : ∀ i, X i) :
    (send p bit p₀ p₁).run x = cond (bit (x p)) (p₁.run x) (p₀.run x) := rfl

@[simp]
theorem depth_output (z : Z) : (output z : NIHProtocol X Z).depth = 0 := rfl

@[simp]
theorem depth_send (p : Fin t) (bit : X p → Bool) (p₀ p₁ : NIHProtocol X Z) :
    (send p bit p₀ p₁).depth = max p₀.depth p₁.depth + 1 := rfl

@[simp]
theorem leafCount_output (z : Z) : (output z : NIHProtocol X Z).leafCount = 1 := rfl

@[simp]
theorem leafCount_send (p : Fin t) (bit : X p → Bool) (p₀ p₁ : NIHProtocol X Z) :
    (send p bit p₀ p₁).leafCount = p₀.leafCount + p₁.leafCount := rfl

/-- Every `NIHProtocol` has at least one leaf. -/
theorem leafCount_pos (P : NIHProtocol X Z) : 0 < P.leafCount := by
  induction P with
  | output _ => simp
  | send _ _ _ _ ih₀ ih₁ =>
    simp only [leafCount_send]
    omega

/-- A `t`-party NIH protocol of depth `d` has at most `2 ^ d` leaves. -/
theorem leafCount_le_two_pow_depth (P : NIHProtocol X Z) : P.leafCount ≤ 2 ^ P.depth := by
  induction P with
  | output _ => simp
  | send _ _ _ _ ih₀ ih₁ => exact Nat.add_le_two_pow_max_succ ih₀ ih₁

/-- Index of the unique leaf reached by `P` on input profile `x`. -/
@[expose] def leaf : (P : NIHProtocol X Z) → (∀ i, X i) → Fin P.leafCount
  | output _, _ => ⟨0, Nat.zero_lt_one⟩
  | send p bit p₀ p₁, x =>
      if bit (x p) then
        Fin.natAdd p₀.leafCount (p₁.leaf x)
      else
        Fin.castAdd p₁.leafCount (p₀.leaf x)

/-- Output label attached to leaf `ℓ : Fin P.leafCount`. -/
@[expose] def leafValue : (P : NIHProtocol X Z) → Fin P.leafCount → Z
  | output z, _ => z
  | send _ _ p₀ p₁, ℓ =>
      if h : ℓ.val < p₀.leafCount then
        p₀.leafValue ⟨ℓ.val, h⟩
      else
        p₁.leafValue ⟨ℓ.val - p₀.leafCount, by
          have hlt : ℓ.val < p₀.leafCount + p₁.leafCount := ℓ.isLt
          omega⟩

/-- Evaluating `P` on `x` returns the constant label `P.leafValue (P.leaf x)` of its leaf. -/
theorem run_eq_leafValue_leaf (P : NIHProtocol X Z) (x : ∀ i, X i) :
    P.run x = P.leafValue (P.leaf x) := by
  induction P with
  | output z => rfl
  | send p bit p₀ p₁ ih₀ ih₁ =>
    dsimp only [run, leaf, leafValue]
    cases h : bit (x p)
    · have hlt : (Fin.castAdd p₁.leafCount (p₀.leaf x)).val < p₀.leafCount := (p₀.leaf x).isLt
      simp only [Bool.false_eq_true, ↓reduceIte, hlt, ↓reduceDIte, Bool.cond_false]
      exact ih₀
    · have hge : ¬(Fin.natAdd p₀.leafCount (p₁.leaf x)).val < p₀.leafCount := by
        simp only [Fin.val_natAdd]; omega
      simp only [↓reduceIte, hge, ↓reduceDIte, Bool.cond_true]
      rw [ih₁]
      congr 1
      ext
      simp

/-- Per-player coordinate acceptance set for leaf `ℓ : Fin P.leafCount`. -/
@[expose] def leafCoord : (P : NIHProtocol X Z) → Fin P.leafCount → ∀ i, Set (X i)
  | output _, _, _ => Set.univ
  | send p bit p₀ p₁, ℓ, i =>
      if h : ℓ.val < p₀.leafCount then
        p₀.leafCoord ⟨ℓ.val, h⟩ i ∩ {u | ∀ e : i = p, bit (e ▸ u) = false}
      else
        p₁.leafCoord ⟨ℓ.val - p₀.leafCount, by
          have hlt : ℓ.val < p₀.leafCount + p₁.leafCount := ℓ.isLt
          omega⟩ i ∩ {u | ∀ e : i = p, bit (e ▸ u) = true}

/-- Input profile `x` reaches leaf `ℓ` iff every coordinate `x i` lies in `P.leafCoord ℓ i`. -/
theorem leaf_eq_iff_mem_leafCoord (P : NIHProtocol X Z) (x : ∀ i, X i) (ℓ : Fin P.leafCount) :
    P.leaf x = ℓ ↔ ∀ i, x i ∈ P.leafCoord ℓ i := by
  induction P with
  | output z =>
    have hℓ0 : ℓ.val = 0 := by
      have h1 : ℓ.val < 1 := ℓ.isLt
      omega
    have heq : (output z).leaf x = ℓ := Fin.ext hℓ0.symm
    exact ⟨fun _ _ ↦ trivial, fun _ ↦ heq⟩
  | send p bit p₀ p₁ ih₀ ih₁ =>
    rw [Fin.ext_iff]
    have hleaf_val : ((send p bit p₀ p₁).leaf x).val =
        if bit (x p) then p₀.leafCount + (p₁.leaf x).val else (p₀.leaf x).val := by
      dsimp only [leaf]
      cases bit (x p) <;> simp
    rw [hleaf_val]
    dsimp only [leafCoord]
    by_cases hlt : ℓ.val < p₀.leafCount
    · simp only [hlt, ↓reduceDIte]
      cases hbit : bit (x p)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have heq : (p₀.leaf x).val = ℓ.val ↔ p₀.leaf x = ⟨ℓ.val, hlt⟩ := by
          simp [Fin.ext_iff]
        rw [heq, ih₀]
        refine ⟨fun h i ↦ ⟨h i, fun e ↦ ?_⟩, fun h i ↦ (h i).1⟩
        subst e
        exact hbit
      · simp only [↓reduceIte]
        refine ⟨fun h ↦ by omega, fun h ↦ ?_⟩
        have hp := (h p).2 rfl
        rw [hbit] at hp
        exact Bool.noConfusion hp
    · simp only [hlt, ↓reduceDIte]
      have hge : p₀.leafCount ≤ ℓ.val := Nat.le_of_not_lt hlt
      cases hbit : bit (x p)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun h ↦ by have := (p₀.leaf x).isLt; omega, fun h ↦ ?_⟩
        have hp := (h p).2 rfl
        rw [hbit] at hp
        exact Bool.noConfusion hp
      · simp only [↓reduceIte]
        have heq : p₀.leafCount + (p₁.leaf x).val = ℓ.val ↔
            p₁.leaf x = ⟨ℓ.val - p₀.leafCount, by
              have hlt' : ℓ.val < p₀.leafCount + p₁.leafCount := ℓ.isLt
              omega⟩ := by
          simp only [Fin.ext_iff]
          omega
        rw [heq, ih₁]
        refine ⟨fun h i ↦ ⟨h i, fun e ↦ ?_⟩, fun h i ↦ (h i).1⟩
        subst e
        exact hbit

/-- Every leaf fiber `{x | P.leaf x = ℓ}` of an `NIHProtocol` is a combinatorial rectangle on which
`P.run` is constant with value `P.leafValue ℓ`. -/
theorem isRectangle_leafSet (P : NIHProtocol X Z) (ℓ : Fin P.leafCount) :
    IsProductRectangle {x | P.leaf x = ℓ} ∧ ∀ x, P.leaf x = ℓ → P.run x = P.leafValue ℓ := by
  refine ⟨⟨P.leafCoord ℓ, ?_⟩, fun x hx ↦ by rw [run_eq_leafValue_leaf, hx]⟩
  ext x
  simp [leaf_eq_iff_mem_leafCoord]

/-- Player `p` broadcasts a `b`-bit string `msg (x p)` and execution continues with `cont`. -/
def playerSend (p : Fin t) :
    (b : ℕ) → (X p → BitString b) → (BitString b → NIHProtocol X Z) → NIHProtocol X Z
  | 0, _, cont => cont Fin.elim0
  | b + 1, msg, cont =>
      send p (fun u ↦ msg u 0)
        (playerSend p b (fun u ↦ Fin.tail (msg u)) fun m ↦ cont (Fin.cons false m))
        (playerSend p b (fun u ↦ Fin.tail (msg u)) fun m ↦ cont (Fin.cons true m))

@[simp]
theorem run_playerSend (p : Fin t) (b : ℕ) (msg : X p → BitString b)
    (cont : BitString b → NIHProtocol X Z) (x : ∀ i, X i) :
    (playerSend p b msg cont).run x = (cont (msg (x p))).run x := by
  induction b with
  | zero => rw [playerSend, Subsingleton.elim (msg (x p)) Fin.elim0]
  | succ b ih =>
    simp only [playerSend, run_send, ih]
    conv_rhs => rw [← Fin.cons_self_tail (msg (x p))]
    cases msg (x p) 0 <;> rfl

/-- Broadcasting `b` bits adds at most `b` to the protocol depth. -/
theorem depth_playerSend_le (p : Fin t) {b d : ℕ} {msg : X p → BitString b}
    {cont : BitString b → NIHProtocol X Z} (h : ∀ m, (cont m).depth ≤ d) :
    (playerSend p b msg cont).depth ≤ b + d := by
  induction b generalizing d with
  | zero => simpa [playerSend] using h _
  | succ b ih =>
    simp only [playerSend, depth_send]
    have h₀ := ih (msg := fun u ↦ Fin.tail (msg u))
      (cont := fun m ↦ cont (Fin.cons false m)) fun m ↦ h _
    have h₁ := ih (msg := fun u ↦ Fin.tail (msg u))
      (cont := fun m ↦ cont (Fin.cons true m)) fun m ↦ h _
    omega

/-- Pull back an `NIHProtocol` along coordinatewise maps `g : ∀ i, X' i → X i`. -/
def comap {X' : Fin t → Type*} (g : ∀ i, X' i → X i) : NIHProtocol X Z → NIHProtocol X' Z
  | output z => output z
  | send p bit p₀ p₁ => send p (fun u ↦ bit (g p u)) (p₀.comap g) (p₁.comap g)

@[simp]
theorem run_comap {X' : Fin t → Type*} (g : ∀ i, X' i → X i) (P : NIHProtocol X Z)
    (x : ∀ i, X' i) : (P.comap g).run x = P.run (fun i ↦ g i (x i)) := by
  induction P with
  | output _ => rfl
  | send _ _ _ _ ih₀ ih₁ => simp [comap, ih₀, ih₁]

@[simp]
theorem depth_comap {X' : Fin t → Type*} (g : ∀ i, X' i → X i) (P : NIHProtocol X Z) :
    (P.comap g).depth = P.depth := by
  induction P with
  | output _ => rfl
  | send _ _ _ _ ih₀ ih₁ => simp [comap, ih₀, ih₁]

/-- Deterministic `t`-party NIH protocols as a `Cslib.RandomizedCost` model. -/
@[expose, simps] def randomizedCost (X : Fin t → Type*) (Z : Type*) :
    RandomizedCost (NIHProtocol X Z) (∀ i, X i) Z where
  eval := run
  cost := depth

/-- Sequence `r` deterministic `NIHProtocol`s and combine their Boolean outputs by `comb`. -/
def runAll : {r : ℕ} → (Fin r → NIHProtocol X Bool) → ((Fin r → Bool) → Bool) → NIHProtocol X Bool
  | 0, _, comb => output (comb Fin.elim0)
  | _ + 1, ps, comb =>
      let rec appendLeaf (P : NIHProtocol X Bool) (k : Bool → NIHProtocol X Bool) :
          NIHProtocol X Bool :=
        match P with
        | output b => k b
        | send p bit p₀ p₁ => send p bit (appendLeaf p₀ k) (appendLeaf p₁ k)
      appendLeaf (ps 0) fun b₀ ↦ runAll (fun j ↦ ps j.succ) (fun bs ↦ comb (Fin.cons b₀ bs))

private theorem run_appendLeaf (P : NIHProtocol X Bool) (k : Bool → NIHProtocol X Bool)
    (x : ∀ i, X i) : (runAll.appendLeaf P k).run x = (k (P.run x)).run x := by
  induction P with
  | output b => rfl
  | send p bit p₀ p₁ ih₀ ih₁ =>
    simp only [runAll.appendLeaf, run_send]
    cases bit (x p) <;> simp [ih₀, ih₁]

private theorem depth_appendLeaf_le (P : NIHProtocol X Bool) (k : Bool → NIHProtocol X Bool)
    {d : ℕ} (hk : ∀ b, (k b).depth ≤ d) : (runAll.appendLeaf P k).depth ≤ P.depth + d := by
  induction P with
  | output b => simpa [runAll.appendLeaf] using hk b
  | send p bit p₀ p₁ ih₀ ih₁ =>
    simp only [runAll.appendLeaf, depth_send]
    have h₀ := ih₀
    have h₁ := ih₁
    omega

/-- Evaluating `runAll ps comb` applies `comb` to the coordinatewise outputs `(ps j).run x`. -/
theorem run_runAll {r : ℕ} (ps : Fin r → NIHProtocol X Bool) (comb : (Fin r → Bool) → Bool)
    (x : ∀ i, X i) : (runAll ps comb).run x = comb (fun j ↦ (ps j).run x) := by
  induction r with
  | zero =>
    simp only [runAll, run_output]
    congr 1
    funext j
    exact j.elim0
  | succ r ih =>
    simp only [runAll]
    rw [run_appendLeaf, ih]
    congr 1
    funext j
    cases j using Fin.cases <;> rfl

/-- Sequencing `r` protocols each of depth at most `d` has depth at most `r * d`. -/
theorem depth_runAll_le {r d : ℕ} {ps : Fin r → NIHProtocol X Bool}
    {comb : (Fin r → Bool) → Bool} (h : ∀ j, (ps j).depth ≤ d) :
    (runAll ps comb).depth ≤ r * d := by
  induction r with
  | zero => simp [runAll]
  | succ r ih =>
    simp only [runAll]
    refine (depth_appendLeaf_le (ps 0) _ fun b ↦ ih fun j ↦ h j.succ).trans ?_
    have h0 := h 0
    calc (ps 0).depth + r * d ≤ d + r * d := Nat.add_le_add_right h0 _
      _ = (r + 1) * d := by ring

end NIHProtocol

end NIHProtocol

/-! ### 3. One-Way and Simultaneous Multiparty Protocols -/

section OneWayAndSim

/-- A deterministic `(t + 1)`-player one-way (sententious) number-in-hand protocol: for each step
`i : Fin t`, player `i.castSucc` sends a bit-string of length `msgLen i` computed from its input and
the incoming message from the previous step, and final player `Fin.last t` computes the output
locally from its input and the final message without incurring an extra announcement bit. -/
structure OneWayProtocol {t : ℕ} (X : Fin (t + 1) → Type*) (Z : Type*) where
  /-- Bit-length of the message sent by player `i.castSucc` to player `i.succ`. -/
  msgLen : Fin t → ℕ
  /-- First message function when `t > 0`, or step transition taking incoming bits to outgoing
  bits. -/
  step : ∀ i : Fin t, X i.castSucc →
    (if h : 0 < i.val then BitString (msgLen ⟨i.val - 1, by omega⟩) else Unit) →
      BitString (msgLen i)
  /-- Local output map of the final player `Fin.last t`. -/
  finish : X (Fin.last t) →
    (if h : 0 < t then BitString (msgLen ⟨t - 1, by omega⟩) else Unit) → Z

namespace OneWayProtocol

variable {t : ℕ} {X : Fin (t + 1) → Type*} {Z : Type*}

/-- Total communication cost `∑ i : Fin t, P.msgLen i` of a `(t + 1)`-player one-way protocol. -/
@[expose] def cost (P : OneWayProtocol X Z) : ℕ :=
  ∑ i : Fin t, P.msgLen i

@[simp]
theorem cost_mk (m : Fin t → ℕ)
    (s : ∀ i : Fin t, X i.castSucc →
      (if h : 0 < i.val then BitString (m ⟨i.val - 1, by omega⟩) else Unit) → BitString (m i))
    (f : X (Fin.last t) →
      (if h : 0 < t then BitString (m ⟨t - 1, by omega⟩) else Unit) → Z) :
    ({ msgLen := m, step := s, finish := f } : OneWayProtocol X Z).cost = ∑ i : Fin t, m i := rfl

/-- Sum formula for `OneWayProtocol.cost`. -/
theorem cost_eq_sum (P : OneWayProtocol X Z) : P.cost = ∑ i : Fin t, P.msgLen i := rfl

/-- Maximum single-message length across all `t` speakers. -/
@[expose] def maxMsgLen (P : OneWayProtocol X Z) : ℕ :=
  Finset.univ.sup P.msgLen

/-- Message produced after the first `s` speakers (`0 ≤ s ≤ t`) on input profile `x`. -/
@[expose] def prefixMsg (P : OneWayProtocol X Z) (x : ∀ i, X i) :
    (s : ℕ) → (hs : s ≤ t) →
      if h : 0 < s then BitString (P.msgLen ⟨s - 1, by omega⟩) else Unit
  | 0, _ => ()
  | s + 1, hs =>
      let prev := P.prefixMsg x s (by omega)
      have hsub : (if h : 0 < (⟨s, hs⟩ : Fin t).val then
          BitString (P.msgLen ⟨s - 1, by omega⟩) else Unit) =
          (if h : 0 < s then BitString (P.msgLen ⟨s - 1, by omega⟩) else Unit) := rfl
      P.step ⟨s, hs⟩ (x (Fin.castSucc ⟨s, hs⟩)) (hsub ▸ prev)

@[simp]
theorem prefixMsg_zero (P : OneWayProtocol X Z) (x : ∀ i, X i) (hs : 0 ≤ t) :
    P.prefixMsg x 0 hs = () := rfl

@[simp]
theorem prefixMsg_succ (P : OneWayProtocol X Z) (x : ∀ i, X i) (s : ℕ) (hs : s + 1 ≤ t) :
    P.prefixMsg x (s + 1) hs =
      P.step ⟨s, hs⟩ (x (Fin.castSucc ⟨s, hs⟩)) (P.prefixMsg x s (by omega)) := rfl

/-- Evaluate a `(t + 1)`-player one-way protocol `P` on input profile `x`. -/
@[expose] def run (P : OneWayProtocol X Z) (x : ∀ i, X i) : Z :=
  P.finish (x (Fin.last t)) (P.prefixMsg x t le_rfl)

/-- Unfolding identity for `OneWayProtocol.run`. -/
theorem run_eq_finish (P : OneWayProtocol X Z) (x : ∀ i, X i) :
    P.run x = P.finish (x (Fin.last t)) (P.prefixMsg x t le_rfl) := rfl

/-- Deterministic `(t + 1)`-player one-way protocols as a `Cslib.RandomizedCost` model. -/
@[expose, simps] def randomizedCost (X : Fin (t + 1) → Type*) (Z : Type*) :
    RandomizedCost (OneWayProtocol X Z) (∀ i, X i) Z where
  eval := run
  cost := cost

/-- Pull back a `OneWayProtocol` along coordinatewise input maps `g : ∀ i, X' i → X i`. -/
@[expose, simps] def comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i)
    (P : OneWayProtocol X Z) : OneWayProtocol X' Z where
  msgLen := P.msgLen
  step i u prev := P.step i (g i.castSucc u) prev
  finish u lastMsg := P.finish (g (Fin.last t) u) lastMsg

private theorem prefixMsg_comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i)
    (P : OneWayProtocol X Z) (x : ∀ i, X' i) (s : ℕ) (hs : s ≤ t) :
    (P.comap g).prefixMsg x s hs = P.prefixMsg (fun i ↦ g i (x i)) s hs := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [prefixMsg_succ, ih (by omega)]
    rfl

@[simp]
theorem run_comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i) (P : OneWayProtocol X Z)
    (x : ∀ i, X' i) : (P.comap g).run x = P.run (fun i ↦ g i (x i)) := by
  rw [run_eq_finish, prefixMsg_comap]
  rfl

@[simp]
theorem cost_comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i) (P : OneWayProtocol X Z) :
    (P.comap g).cost = P.cost := by rfl

private def extractMsg {P : Prop} [inst : Decidable P] {α β : Type} (hP : P)
    (v : @dite Type P inst (fun _ ↦ α) (fun _ ↦ β)) : α :=
  match inst, v with
  | isTrue _, w => w
  | isFalse hn, _ => absurd hP hn

/-- Simulate a single-pass `b`-bit streaming algorithm `A : Streaming.Algorithm σ α Z` on streams
`u 0 (x 0) ++ … ++ u t (x t)` whose prefix up to player `t - 1` has total length at most `m`. -/
noncomputable def ofStreaming {σ α : Type*} (A : Streaming.Algorithm σ α Z)
    (m b : ℕ) (enc : σ → BitString b) (u : ∀ i : Fin (t + 1), X i → List α) :
    OneWayProtocol X Z where
  msgLen _ := b
  step i xi prev :=
    have : Nonempty σ := ⟨A.init⟩
    let q : σ :=
      if h : 0 < i.val then
        Function.invFunOn enc (A.reachable m) (extractMsg h prev)
      else
        A.init
    enc (A.stateFrom q (u i.castSucc xi))
  finish xt lastMsg :=
    have : Nonempty σ := ⟨A.init⟩
    let q : σ :=
      if h : 0 < t then
        Function.invFunOn enc (A.reachable m) (extractMsg h lastMsg)
      else
        A.init
    A.output (A.stateFrom q (u (Fin.last t) xt))

private theorem ofStreaming_step {σ α : Type*} (A : Streaming.Algorithm σ α Z) (m b : ℕ)
    (enc : σ → BitString b) (u : ∀ i : Fin (t + 1), X i → List α)
    (i : Fin t) (xi : X i.castSucc)
    (prev : if h : 0 < i.val then
      BitString ((ofStreaming A m b enc u).msgLen ⟨i.val - 1, by omega⟩) else Unit) :
    (ofStreaming A m b enc u).step i xi prev =
      have : Nonempty σ := ⟨A.init⟩
      enc (A.stateFrom
        (if h : 0 < i.val then Function.invFunOn enc (A.reachable m) (extractMsg h prev)
         else A.init)
        (u i.castSucc xi)) := rfl

private theorem ofStreaming_finish {σ α : Type*} (A : Streaming.Algorithm σ α Z) (m b : ℕ)
    (enc : σ → BitString b) (u : ∀ i : Fin (t + 1), X i → List α)
    (xt : X (Fin.last t))
    (lastMsg : if h : 0 < t then
      BitString ((ofStreaming A m b enc u).msgLen ⟨t - 1, by omega⟩) else Unit) :
    (ofStreaming A m b enc u).finish xt lastMsg =
      have : Nonempty σ := ⟨A.init⟩
      A.output (A.stateFrom
        (if h : 0 < t then Function.invFunOn enc (A.reachable m) (extractMsg h lastMsg)
         else A.init)
        (u (Fin.last t) xt)) := rfl

/-- The one-way protocol simulating a `b`-bit streaming algorithm across `t + 1` players sends
exactly `t * b` bits in total. -/
theorem cost_ofStreaming {σ α : Type*} (A : Streaming.Algorithm σ α Z) (m b : ℕ)
    (enc : σ → BitString b) (u : ∀ i : Fin (t + 1), X i → List α) :
    (ofStreaming A m b enc u).cost = t * b := by
  simp [cost, ofStreaming]

/-- Concatenation of the first `s` stream blocks `u 0 (x 0) ++ … ++ u (s - 1) (x (s - 1))`. -/
@[expose] def streamPrefix {α : Type*} (u : ∀ i : Fin (t + 1), X i → List α) (x : ∀ i, X i) :
    (s : ℕ) → s ≤ t + 1 → List α
  | 0, _ => []
  | s + 1, hs => streamPrefix u x s (by omega) ++ u ⟨s, hs⟩ (x ⟨s, hs⟩)

@[simp]
theorem streamPrefix_zero {α : Type*} (u : ∀ i : Fin (t + 1), X i → List α) (x : ∀ i, X i)
    (hs : 0 ≤ t + 1) : streamPrefix u x 0 hs = [] := by rfl

@[simp]
theorem streamPrefix_succ {α : Type*} (u : ∀ i : Fin (t + 1), X i → List α) (x : ∀ i, X i)
    (s : ℕ) (hs : s + 1 ≤ t + 1) :
    streamPrefix u x (s + 1) hs = streamPrefix u x s (by omega) ++ u ⟨s, hs⟩ (x ⟨s, hs⟩) := by rfl

private theorem prefixMsg_ofStreaming {σ α : Type*} (A : Streaming.Algorithm σ α Z) {m b : ℕ}
    {enc : σ → BitString b} (henc : Set.InjOn enc (A.reachable m))
    (u : ∀ i : Fin (t + 1), X i → List α) (x : ∀ i, X i) :
    ∀ (s : ℕ) (hs : s ≤ t),
      (streamPrefix u x s (by omega)).length ≤ m →
      ∀ h0 : 0 < s,
        extractMsg h0 ((ofStreaming A m b enc u).prefixMsg x s hs) =
          enc (A.state (streamPrefix u x s (by omega)))
  | 0, _, _, h0 => absurd h0 (lt_irrefl 0)
  | s + 1, hs, hlen, _ => by
    have : Nonempty σ := ⟨A.init⟩
    have _ := henc
    change (ofStreaming A m b enc u).prefixMsg x (s + 1) hs = _
    rw [prefixMsg_succ, ofStreaming_step]
    rcases Nat.eq_zero_or_pos s with rfl | hspos
    · simp [streamPrefix, Streaming.Algorithm.state]
      rfl
    · have hprevLen : (streamPrefix u x s (by omega)).length ≤ m := by
        simp only [streamPrefix_succ, List.length_append] at hlen
        omega
      have ih := prefixMsg_ofStreaming A henc u x s (by omega) hprevLen hspos
      have hreach : A.state (streamPrefix u x s (by omega)) ∈ A.reachable m :=
        A.state_mem_reachable hprevLen
      simp only [Fin.val_mk, hspos, ↓reduceDIte]
      rw [ih, henc.leftInvOn_invFunOn hreach, streamPrefix_succ, A.state_append]
      rfl

/-- Correctness of `ofStreaming`: when `enc` is injective on `A.reachable m` and the first `t`
stream blocks have combined length at most `m`, `(ofStreaming A m b enc u).run x` equals the
streaming output `A.run` on the full concatenated stream. -/
theorem run_ofStreaming {σ α : Type*} (A : Streaming.Algorithm σ α Z) {m b : ℕ}
    {enc : σ → BitString b} (henc : Set.InjOn enc (A.reachable m))
    (u : ∀ i : Fin (t + 1), X i → List α) (x : ∀ i, X i)
    (hlen : (streamPrefix u x t (by omega)).length ≤ m) :
    (ofStreaming A m b enc u).run x = A.run (streamPrefix u x (t + 1) le_rfl) := by
  have : Nonempty σ := ⟨A.init⟩
  rw [run_eq_finish, ofStreaming_finish]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [streamPrefix, Streaming.Algorithm.run, Streaming.Algorithm.state, Fin.last]
  · have hm := prefixMsg_ofStreaming A henc u x t le_rfl hlen ht
    have hreach : A.state (streamPrefix u x t (by omega)) ∈ A.reachable m :=
      A.state_mem_reachable hlen
    simp only [ht, ↓reduceDIte, Streaming.Algorithm.run]
    rw [hm, henc.leftInvOn_invFunOn hreach, streamPrefix_succ, ← A.state_append]
    rfl

end OneWayProtocol

/-- **Single-pass streaming space bounds multiparty one-way communication**: if a randomized
single-pass streaming algorithm `μ` uses at most `b` bits of space on streams of length at most `m`
and computes `R` with error at most `δ` on concatenated streams of `t + 1` players, then the
public-coin `(t + 1)`-player one-way complexity is at most `t * b`. -/
theorem oneWay_cost_le_of_spaceLE {t : ℕ} {X : Fin (t + 1) → Type*} {σ α Z : Type*} {m b : ℕ}
    (μ : Streaming.Randomized σ α Z) (hμ : μ.SpaceLE m b)
    (u : ∀ i : Fin (t + 1), X i → List α)
    (hlen : ∀ x : ∀ i, X i, (OneWayProtocol.streamPrefix u x t (by omega)).length ≤ m)
    {R : (∀ i, X i) → Z → Prop} {S : Set (∀ i, X i)} {δ : ℝ}
    (hsol : ∀ x ∈ S,
      (μ.toOuterMeasure {A | ¬R x (A.run (OneWayProtocol.streamPrefix u x (t + 1) le_rfl))}).toReal
        ≤ δ) :
    (OneWayProtocol.randomizedCost X Z).ecomplexity δ R S ≤ t * b := by
  classical
  have hzero : Nonempty Z → True := fun _ ↦ trivial
  let _ := hzero
  by_cases hS : S = ∅
  · subst hS
    rcases μ.support_nonempty with ⟨A₀, hA₀⟩
    obtain ⟨enc₀, _⟩ := hμ A₀ hA₀
    refine (RandomizedCost.ecomplexity_le_maxCost
      (μ := PMF.pure (OneWayProtocol.ofStreaming A₀ m b enc₀ u))
      (fun x hx ↦ absurd hx (Set.notMem_empty x))).trans ?_
    simp [OneWayProtocol.randomizedCost, OneWayProtocol.cost_ofStreaming]
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hS
    rcases μ.support_nonempty with ⟨A₀, _⟩
    let z₀ : Z := A₀.run []
    let F : Streaming.Algorithm σ α Z → OneWayProtocol X Z := fun A ↦
      if h : A.SpaceLE m b then
        OneWayProtocol.ofStreaming A m b h.choose u
      else
        { msgLen := fun _ ↦ 0, step := fun _ _ _ ↦ Fin.elim0, finish := fun _ _ ↦ z₀ }
    refine (RandomizedCost.ecomplexity_le_maxCost (μ := μ.map F) fun x hx ↦ ?_).trans ?_
    · refine le_trans ?_ (hsol x hx)
      unfold RandomizedCost.errorProb PMF.errorProb
      rw [PMF.toOuterMeasure_map_apply]
      refine ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
        (PMF.toOuterMeasure_mono _ fun A ⟨hA, hsupp⟩ ↦ ?_)
      have hs := hμ A hsupp
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, F, dite_eq_left hs,
        OneWayProtocol.randomizedCost] at hA ⊢
      rwa [OneWayProtocol.run_ofStreaming A hs.choose_spec u x (hlen x)] at hA
    · refine PMF.maxCost_map_le_of_le (OneWayProtocol.randomizedCost X Z).cost F μ fun A hA ↦ ?_
      simp [F, dite_eq_left (hμ A hA), OneWayProtocol.randomizedCost,
        OneWayProtocol.cost_ofStreaming]

/-- A deterministic `(t + 1)`-player simultaneous protocol: each non-referee player `i.castSucc`
(`i : Fin t`) independently sends a message of `msgLen i` bits computed from its own input alone,
and the referee `Fin.last t` outputs from its input and the tuple of `t` messages. -/
structure SimProtocol {t : ℕ} (X : Fin (t + 1) → Type*) (Z : Type*) where
  /-- Bit-length of player `i.castSucc`'s message to the referee. -/
  msgLen : Fin t → ℕ
  /-- Message map of non-referee player `i.castSucc`. -/
  send : ∀ i : Fin t, X i.castSucc → BitString (msgLen i)
  /-- Referee decision map using `x (Fin.last t)` and all `t` received messages. -/
  decide : X (Fin.last t) → (∀ i : Fin t, BitString (msgLen i)) → Z

namespace SimProtocol

variable {t : ℕ} {X : Fin (t + 1) → Type*} {Z : Type*}

/-- Total communication cost `∑ i : Fin t, P.msgLen i` of a simultaneous protocol. -/
@[expose] def cost (P : SimProtocol X Z) : ℕ :=
  ∑ i : Fin t, P.msgLen i

@[simp]
theorem cost_mk (m : Fin t → ℕ)
    (s : ∀ i : Fin t, X i.castSucc → BitString (m i))
    (d : X (Fin.last t) → (∀ i : Fin t, BitString (m i)) → Z) :
    ({ msgLen := m, send := s, decide := d } : SimProtocol X Z).cost = ∑ i : Fin t, m i := rfl

/-- Sum formula for `SimProtocol.cost`. -/
theorem cost_eq_sum (P : SimProtocol X Z) : P.cost = ∑ i : Fin t, P.msgLen i := rfl

/-- Evaluate a simultaneous protocol `P` on input profile `x`. -/
@[expose] def run (P : SimProtocol X Z) (x : ∀ i, X i) : Z :=
  P.decide (x (Fin.last t)) (fun i ↦ P.send i (x i.castSucc))

/-- Unfolding identity for `SimProtocol.run`. -/
theorem run_eq_decide (P : SimProtocol X Z) (x : ∀ i, X i) :
    P.run x = P.decide (x (Fin.last t)) (fun i ↦ P.send i (x i.castSucc)) := rfl

/-- Deterministic `(t + 1)`-player simultaneous protocols as a `Cslib.RandomizedCost` model. -/
@[expose, simps] def randomizedCost (X : Fin (t + 1) → Type*) (Z : Type*) :
    RandomizedCost (SimProtocol X Z) (∀ i, X i) Z where
  eval := run
  cost := cost

/-- Pull back a `SimProtocol` along coordinatewise input maps `g : ∀ i, X' i → X i`. -/
@[expose, simps] def comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i)
    (P : SimProtocol X Z) : SimProtocol X' Z where
  msgLen := P.msgLen
  send i u := P.send i (g i.castSucc u)
  decide u msgs := P.decide (g (Fin.last t) u) msgs

@[simp]
theorem run_comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i) (P : SimProtocol X Z)
    (x : ∀ i, X' i) : (P.comap g).run x = P.run (fun i ↦ g i (x i)) := rfl

@[simp]
theorem cost_comap {X' : Fin (t + 1) → Type*} (g : ∀ i, X' i → X i) (P : SimProtocol X Z) :
    (P.comap g).cost = P.cost := rfl

end SimProtocol

end OneWayAndSim

/-! ### 4. Contiguous Partitions and Exact 2-Player One-Way ↔ Streaming Equivalence -/

section StreamingEquivalence

/-- A contiguous `t`-block partition of `Fin m` given by monotone cut points
`0 = cut 0 ≤ cut 1 ≤ … ≤ cut t = m`. -/
@[ext] structure ContiguousPartition (m t : ℕ) where
  /-- Boundary cut positions `0, …, t`. -/
  cut : Fin (t + 1) → ℕ
  /-- Left boundary starts at `0`. -/
  cut_zero : cut 0 = 0
  /-- Right boundary ends at `m`. -/
  cut_last : cut (Fin.last t) = m
  /-- Cut positions are nondecreasing. -/
  mono : Monotone cut

/-- Slice of `x : Fin m → α` between `a` and `b` (`b ≤ m`) as a function `Fin (b - a) → α`. -/
@[expose] def sliceVec {α : Type*} {m : ℕ} (x : Fin m → α) (a b : ℕ) (hb : b ≤ m) :
    Fin (b - a) → α :=
  fun j ↦ x ⟨a + j.val, by omega⟩

@[simp]
theorem sliceVec_apply {α : Type*} {m : ℕ} (x : Fin m → α) (a b : ℕ) (hb : b ≤ m)
    (j : Fin (b - a)) : sliceVec x a b hb j = x ⟨a + j.val, by omega⟩ := rfl

/-- Convert a vector `Fin m → α` to a `List α` of length `m`. -/
@[expose] def vecToList {α : Type*} {m : ℕ} (x : Fin m → α) : List α :=
  List.ofFn x

/-- `vecToList x` equals `List.ofFn x`. -/
theorem vecToList_eq_ofFn {α : Type*} {m : ℕ} (x : Fin m → α) :
    vecToList x = List.ofFn x := rfl

@[simp]
theorem length_vecToList {α : Type*} {m : ℕ} (x : Fin m → α) :
    (vecToList x).length = m :=
  List.length_ofFn

@[simp]
theorem getElem_vecToList {α : Type*} {m : ℕ} (x : Fin m → α) (i : ℕ)
    (hi : i < (vecToList x).length) :
    (vecToList x)[i] = x ⟨i, by simpa using hi⟩ := by
  simp [vecToList]

/-- Reassemble a prefix `u : Fin k → α` and suffix `v : Fin (m - k) → α` (`k ≤ m`) into
`Fin m → α`. -/
@[expose] def glueSplit {α : Type*} {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (u : Fin k → α) (v : Fin (m - k) → α) : Fin m → α :=
  fun j ↦ if h : j.val < k then u ⟨j.val, h⟩ else v ⟨j.val - k, by omega⟩

@[simp]
theorem glueSplit_of_lt {α : Type*} {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (u : Fin k → α) (v : Fin (m - k) → α) (j : Fin m) (h : j.val < k) :
    glueSplit k hk u v j = u ⟨j.val, h⟩ := by
  simp [glueSplit, h]

@[simp]
theorem glueSplit_of_not_lt {α : Type*} {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (u : Fin k → α) (v : Fin (m - k) → α) (j : Fin m) (h : ¬j.val < k) :
    glueSplit k hk u v j = v ⟨j.val - k, by omega⟩ := by
  simp [glueSplit, h]

/-- Gluing the prefix and suffix slices of `x` recovers `x`. -/
theorem glueSplit_sliceVec {α : Type*} {m : ℕ} (k : ℕ) (hk : k ≤ m) (x : Fin m → α) :
    glueSplit k hk (sliceVec x 0 k hk) (sliceVec x k m le_rfl) = x := by
  ext j
  by_cases h : j.val < k
  · simp [h]
  · simp only [glueSplit_of_not_lt _ _ _ _ _ h, sliceVec_apply]
    congr 1
    ext
    dsimp only
    omega

/-- **Deterministic 2-player one-way communication simulates in single-pass streaming**: if for
every split `0 ≤ k ≤ m` of `Fin m` (`m ≥ 1`) there is a deterministic 2-player one-way protocol of
message length at most `c` computing `f : (Fin m → α) → β`, then there is a deterministic
single-pass streaming algorithm over finite state `Fin m × BitString c` using at most
`c + Nat.clog 2 m` bits of memory that computes `f` on every `m`-item stream. -/
theorem streaming_spaceLE_of_twoPartyOneWay {α β : Type*} [Nonempty α] {m c : ℕ} (hm : 0 < m)
    (f : (Fin m → α) → β)
    (hprot : ∀ (k : ℕ) (hk : k ≤ m),
      ∃ (send : (Fin k → α) → BitString c) (dec : (Fin (m - k) → α) → BitString c → β),
        ∀ (u : Fin k → α) (v : Fin (m - k) → α), dec v (send u) = f (glueSplit k hk u v)) :
    ∃ A : Streaming.Algorithm (Fin m × BitString c) α β,
      A.SpaceLE m (c + Nat.clog 2 m) ∧ ∀ x : Fin m → α, A.run (vecToList x) = f x := by
  classical
  choose send dec hcorrect using hprot
  let guess (k : ℕ) (hk : k ≤ m) (msg : BitString c) : Fin k → α :=
    if h : ∃ u : Fin k → α, send k hk u = msg then Classical.choose h
    else fun _ ↦ Classical.arbitrary α
  let emp : Fin (m - m) → α := fun q ↦ absurd q.isLt (by omega)
  let A : Streaming.Algorithm (Fin m × BitString c) α β :=
    { init := (⟨0, hm⟩, send 0 (Nat.zero_le m) Fin.elim0)
      update := fun ⟨idx, msg⟩ a ↦
        let uPrev : Fin idx.val → α :=
          if h0 : idx.val = 0 then fun q ↦ absurd q.isLt (by omega)
          else guess idx.val idx.isLt.le msg
        let nextC := idx.val + 1
        have hle : nextC ≤ m := idx.isLt
        (⟨nextC % m, Nat.mod_lt _ hm⟩, send nextC hle (Fin.snoc uPrev a))
      output := fun ⟨_, msg⟩ ↦ dec m le_rfl emp msg }
  refine ⟨A, ?_, fun x ↦ ?_⟩
  · refine A.spaceLE_of_card_le ?_
    calc Fintype.card (Fin m × BitString c)
        = m * 2 ^ c := by simp [Fintype.card_prod]
      _ ≤ 2 ^ Nat.clog 2 m * 2 ^ c :=
          Nat.mul_le_mul_right _ (Nat.le_pow_clog one_lt_two m)
      _ = 2 ^ (c + Nat.clog 2 m) := by rw [← pow_add, add_comm]
  · have hinv : ∀ (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m),
        ∃ u : Fin k → α,
          (∀ v : Fin (m - k) → α, f (glueSplit k hkm u v) =
            f (glueSplit k hkm (sliceVec x 0 k hkm) v)) ∧
          A.state ((vecToList x).take k) = (⟨k % m, Nat.mod_lt k hm⟩, send k hkm u) := by
      intro k hk hkm
      induction k with
      | zero => omega
      | succ k ih =>
        have htake : (vecToList x).take (k + 1) =
            (vecToList x).take k ++ [x ⟨k, by omega⟩] := by
          rw [List.take_add_one]
          simp [vecToList, show k < m by omega]
        rw [Streaming.Algorithm.state, htake, A.stateFrom_append,
          Streaming.Algorithm.stateFrom_cons, Streaming.Algorithm.stateFrom_nil]
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp only [List.take_zero, Streaming.Algorithm.stateFrom_nil, A, ↓reduceDIte, zero_add]
          refine ⟨sliceVec x 0 1 hkm, fun _ ↦ rfl, Prod.ext rfl ?_⟩
          apply congrArg (send 1 hkm)
          ext j
          have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
          subst hj
          simp [Fin.snoc]
        · obtain ⟨u₀, hu₀f, hst⟩ := ih hkpos (by omega)
          have hklt : k < m := by omega
          have hmod : k % m = k := Nat.mod_eq_of_lt hklt
          have hfin_eq : (⟨k % m, Nat.mod_lt k hm⟩ : Fin m) = ⟨k, hklt⟩ := Fin.ext hmod
          rw [hfin_eq] at hst
          change ∃ u, _ ∧ A.update (A.state ((vecToList x).take k)) (x ⟨k, hklt⟩) = _
          rw [hst]
          have hex : ∃ u' : Fin k → α, send k hklt.le u' = send k hklt.le u₀ := ⟨u₀, rfl⟩
          let uGuess : Fin k → α := guess k hklt.le (send k hklt.le u₀)
          have huGuessSend : send k hklt.le uGuess = send k hklt.le u₀ := by
            simp only [uGuess, guess, hex, ↓reduceDIte]
            exact Classical.choose_spec hex
          refine ⟨Fin.snoc uGuess (x ⟨k, hklt⟩), fun suf ↦ ?_, ?_⟩
          · let sufExt : Fin (m - k) → α := fun j ↦
              if hj0 : j.val = 0 then x ⟨k, hklt⟩ else suf ⟨j.val - 1, by have := j.isLt; omega⟩
            have hglue1 : glueSplit (k + 1) hkm (Fin.snoc uGuess (x ⟨k, hklt⟩)) suf =
                glueSplit k hklt.le uGuess sufExt := by
              ext j
              by_cases hjv : j.val < k
              · have hjv1 : j.val < k + 1 := by omega
                rw [glueSplit_of_lt _ _ _ _ _ hjv1, glueSplit_of_lt _ _ _ _ _ hjv]
                simp [Fin.snoc, hjv]
              · by_cases hjeq : j.val = k
                · have hjv1 : j.val < k + 1 := by omega
                  rw [glueSplit_of_lt _ _ _ _ _ hjv1, glueSplit_of_not_lt _ _ _ _ _ hjv]
                  simp [sufExt, hjeq, Fin.snoc]
                · have hnot1 : ¬j.val < k + 1 := by omega
                  have hnot0 : j.val - k ≠ 0 := by omega
                  rw [glueSplit_of_not_lt _ _ _ _ _ hnot1, glueSplit_of_not_lt _ _ _ _ _ hjv]
                  simp only [sufExt, hnot0, ↓reduceDIte]
                  exact congrArg suf (Fin.ext (by simp only; omega))
            have hglue2 : glueSplit (k + 1) hkm (sliceVec x 0 (k + 1) hkm) suf =
                glueSplit k hklt.le (sliceVec x 0 k hklt.le) sufExt := by
              ext j
              by_cases hjv : j.val < k
              · have hjv1 : j.val < k + 1 := by omega
                simp [hjv1, hjv]
              · by_cases hjeq : j.val = k
                · simp [sufExt, hjeq]
                · have hnot1 : ¬j.val < k + 1 := by omega
                  have hnot0 : j.val - k ≠ 0 := by omega
                  rw [glueSplit_of_not_lt _ _ _ _ _ hnot1, glueSplit_of_not_lt _ _ _ _ _ hjv]
                  simp only [sufExt, hnot0, ↓reduceDIte]
                  exact congrArg suf (Fin.ext (by simp only; omega))
            rw [hglue1, ← hcorrect k hklt.le uGuess sufExt, huGuessSend,
              hcorrect k hklt.le u₀ sufExt, hu₀f sufExt, ← hglue2]
          · simp only [A, Fin.val_mk, hkpos.ne', ↓reduceDIte]
            rfl
    obtain ⟨uFinal, huFinal, hst⟩ := hinv m hm le_rfl
    have htakeAll : (vecToList x).take m = vecToList x :=
      List.take_of_length_le (by simp)
    rw [htakeAll] at hst
    simp only [Streaming.Algorithm.run, hst, A]
    have hemp_eq : emp = sliceVec x m m le_rfl := funext fun q ↦ absurd q.isLt (by omega)
    rw [hcorrect m le_rfl uFinal emp, huFinal emp, hemp_eq, glueSplit_sliceVec m le_rfl x]

end StreamingEquivalence

/-! ### 5. Odd-Trial Strict-Majority Tail Bound -/

section Amplification

/-- **Odd-trial strict-majority tail bound**: among `2 * r + 1` independent Boolean trials that
are each `true` with probability at most `δ ≤ 1 / 2`, strictly more than `r` trials are `true` with
probability at most `δ * (4 * δ * (1 - δ)) ^ r`. -/
theorem iid_strictMajority_odd_tail {q : PMF Bool} {δ : ℝ} (hq : (q true).toReal ≤ δ)
    (hδ : δ ≤ 1 / 2) (r : ℕ) :
    ((PMF.iid q (2 * r + 1)).toOuterMeasure
      {v | r + 1 ≤ (Finset.univ.filter fun i ↦ v i = true).card}).toReal ≤
        δ * (4 * δ * (1 - δ)) ^ r := by
  classical
  set a := (q true).toReal
  set b := (q false).toReal
  have hab : a + b = 1 := by
    have hsum := PMF.sum_toReal q
    rw [Fintype.sum_bool] at hsum
    linarith
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hab' : a ≤ b := by linarith
  have hterm (v : Fin (2 * r + 1) → Bool)
      (hv : r + 1 ≤ (Finset.univ.filter fun i ↦ v i = true).card) :
      ∏ i, (q (v i)).toReal ≤ a * (a * b) ^ r := by
    have hprod : ∏ i, (q (v i)).toReal = ∏ i, (if v i = true then a else b) :=
      Finset.prod_congr rfl fun i _ ↦ by cases v i <;> rfl
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i ↦ v i = true
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    set t := (Finset.univ.filter fun i ↦ v i = true).card
    set u := (Finset.univ.filter fun i ↦ ¬v i = true).card
    rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    obtain ⟨d, hd⟩ : ∃ d, t = r + 1 + d := Nat.exists_eq_add_of_le hv
    have hru : r = u + d := by omega
    have hb0 : 0 ≤ b := ha.trans hab'
    calc a ^ t * b ^ u = a * (a ^ u * a ^ d * b ^ u * a ^ d) := by
          rw [hd, hru]
          ring
      _ ≤ a * (a ^ u * a ^ d * b ^ u * b ^ d) := by gcongr
      _ = a * (a * b) ^ r := by
          rw [hru]
          ring
  -- Pair each vector `v` having `≥ r + 1` trues with `!v`, which has `≤ r` trues, so at most half
  -- of the `2 ^ (2 * r + 1) = 2 * 4 ^ r` vectors satisfy the predicate.
  let S : Finset (Fin (2 * r + 1) → Bool) :=
    Finset.univ.filter fun v ↦ r + 1 ≤ (Finset.univ.filter fun i ↦ v i = true).card
  let negEmb : (Fin (2 * r + 1) → Bool) ↪ (Fin (2 * r + 1) → Bool) :=
    ⟨fun v i ↦ !v i, fun u v h ↦ funext fun i ↦ Bool.not_inj (congrFun h i)⟩
  have hdisj : Disjoint S (S.map negEmb) := by
    rw [Finset.disjoint_left]
    intro v hv hmap
    rcases Finset.mem_map.mp hmap with ⟨w, hw, rfl⟩
    have hvw := (Finset.mem_filter.mp hv).2
    have hww := (Finset.mem_filter.mp hw).2
    change r + 1 ≤ (Finset.univ.filter fun i ↦ (!w i) = true).card at hvw
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i ↦ w i = true
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have heq : (Finset.univ.filter fun i ↦ (!w i) = true) =
        Finset.univ.filter fun i ↦ ¬w i = true := by
      ext i
      cases w i <;> simp
    rw [heq] at hvw
    omega
  have hcardS : 2 * S.card ≤ 2 ^ (2 * r + 1) := by
    have hu := Finset.card_union_of_disjoint hdisj
    have hle : (S ∪ S.map negEmb).card ≤
        (Finset.univ : Finset (Fin (2 * r + 1) → Bool)).card :=
      Finset.card_le_univ _
    rw [hu, Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] at hle
    omega
  have hcardS' : S.card ≤ 4 ^ r := by
    have : 2 ^ (2 * r + 1) = 2 * 4 ^ r := by
      rw [pow_succ', pow_mul]
      norm_num
    omega
  have hset :
      {v : Fin (2 * r + 1) → Bool | r + 1 ≤ (Finset.univ.filter fun i ↦ v i = true).card} =
        (S : Set (Fin (2 * r + 1) → Bool)) := by
    ext v
    simp [S]
  rw [hset, PMF.toOuterMeasure_apply_toReal]
  simp only [Finset.mem_coe, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hb0 : 0 ≤ b := ha.trans hab'
  have hab_nn : 0 ≤ 4 * (a * b) := mul_nonneg (by norm_num) (mul_nonneg ha hb0)
  have hδ_nn : 0 ≤ 4 * δ * (1 - δ) := by nlinarith [ha.trans hq]
  calc ∑ v ∈ S, (PMF.iid q (2 * r + 1) v).toReal
      ≤ ∑ _v ∈ S, a * (a * b) ^ r := by
        refine Finset.sum_le_sum fun v hv ↦ ?_
        rw [PMF.iid_apply, ENNReal.toReal_prod]
        exact hterm v (Finset.mem_filter.mp hv).2
    _ = S.card * (a * (a * b) ^ r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 ^ r * (a * (a * b) ^ r) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg ha (pow_nonneg (mul_nonneg ha hb0) r))
        exact_mod_cast hcardS'
    _ = a * (4 * (a * b)) ^ r := by
        rw [mul_pow]
        ring
    _ ≤ δ * (4 * δ * (1 - δ)) ^ r := by
        have hbEq : b = 1 - a := by linarith
        rw [hbEq]
        have hab_eq : 4 * (a * (1 - a)) = 4 * a * (1 - a) := by ring
        rw [hab_eq]
        refine mul_le_mul hq (pow_le_pow_left₀ (by nlinarith) ?_ r)
          (pow_nonneg (by nlinarith) r) (ha.trans hq)
        nlinarith

end Amplification

-- Non-vacuity sanity check on concrete 2-party XOR streaming equivalence
example : ∃ A : Streaming.Algorithm (Fin 2 × BitString 1) Bool Bool,
    A.SpaceLE 2 (1 + Nat.clog 2 2) ∧
      ∀ x : Fin 2 → Bool, A.run (vecToList x) = xor (x 0) (x 1) := by
  refine streaming_spaceLE_of_twoPartyOneWay (by decide) (fun x ↦ xor (x 0) (x 1)) fun k hk ↦ ?_
  interval_cases k
  · refine ⟨fun _ ↦ fun _ ↦ false, fun v _ ↦ xor (v 0) (v 1), fun _ _ ↦ rfl⟩
  · refine ⟨fun u ↦ fun _ ↦ u 0, fun v m ↦ xor (m 0) (v 0), fun _ _ ↦ rfl⟩
  · refine ⟨fun u ↦ fun _ ↦ xor (u 0) (u 1), fun _ m ↦ m 0, fun _ _ ↦ rfl⟩

end Cslib.Communication
