module

public import Cslib.Probability.PMF
public import CslibFrontier.Probability.Entropy
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Log
public import CslibFrontier.Computability.Complexity.SyntacticMorphism

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Deterministic Pebble Automata, the Pebble Hierarchy, and Coding-Configuration Entropy

This module formalizes deterministic two-way `k`-pebble finite automata (marker automata)
with left and right endmarkers, their configurations and coding configurations, the pebble
hierarchy `REG k`, Shannon entropy upper bounds on uniformly sampled visited coding
configurations, pebble-change cardinality bounds, and a general deterministic dilution upper
bound. All results are proved under standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Main definitions

* `CslibFrontier.Computability.Automata.TapeSymbol`: Input tape symbols augmented with left and
  right endmarkers.
* `CslibFrontier.Computability.Automata.Move`: Head movement directions (`left`, `stay`, `right`).
* `CslibFrontier.Computability.Automata.PebbleAutomaton`: Deterministic `k`-pebble two-way
  automaton with pebble conservation and no pebbles placed on endmarkers.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.Cfg`: Instantaneous configuration
  `(state, head, pebbles)`.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.CodingCfg`: Coding configuration
  `(state, pebbles)`.
* `CslibFrontier.Computability.Automata.REG`: The `k`-th level of the pebble hierarchy.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.codingConfigPMF`: Uniform distribution
  over the finite set of coding configurations visited during a run.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.pebbleChangeCount`: Number of steps in
  a run prefix where the pebble-position tuple changes.

## Main results

* `CslibFrontier.Computability.Automata.PebbleAutomaton.card_visitedCodingConfigs_le_of_halts_in`:
  Cardinality of visited coding configurations is bounded by
  `|Q| * (1 + pebbleChangeCount)`.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.entropy_codingConfigDist_le`: Shannon
  entropy of the coding-configuration distribution on length `n` is at most
  `k * log₂ (n + 1) + log₂ |Q|`.
* `CslibFrontier.Computability.Automata.not_mem_REG_of_asymp_entropy_ge`: An asymptotic entropy
  lower bound `(1 - γ) * k * ⌈log₂ l⌉` across all accepting automata implies `L ∉ REG (k - 1)`.
* `CslibFrontier.Computability.Automata.PebbleAutomaton.entropy_codingConfigDist_diluted_le`:
  Deterministic dilution upper bound on coding-configuration entropy.
-/

public section

namespace CslibFrontier.Computability.Automata

open CslibFrontier.Computability.Complexity
open Cslib.Probability.PMF

universe u

/-- Input tape alphabet augmented with standard left and right endmarkers. -/
inductive TapeSymbol (α : Type*) where
  | leftEnd : TapeSymbol α
  | rightEnd : TapeSymbol α
  | sym (a : α) : TapeSymbol α
  deriving DecidableEq

/-- Head movement direction on a two-way tape (`-1`, `0`, `+1`). -/
inductive Move where
  | left : Move
  | stay : Move
  | right : Move
  deriving DecidableEq

/-- The symbol at tape cell `i : Fin (w.length + 2)` of input `w`, with `0` as left endmarker,
`1 .. w.length` as input cells, and `w.length + 1` as right endmarker. -/
def tapeAt {α : Type*} (w : List α) (i : Fin (w.length + 2)) : TapeSymbol α :=
  if h0 : i.val = 0 then
    .leftEnd
  else if h1 : i.val ≤ w.length then
    .sym (w.get ⟨i.val - 1, by omega⟩)
  else
    .rightEnd

theorem tapeAt_zero {α : Type*} (w : List α) :
    tapeAt w ⟨0, by omega⟩ = .leftEnd := by
  simp [tapeAt]

@[simp]
theorem tapeAt_last {α : Type*} (w : List α) :
    tapeAt w ⟨w.length + 1, by omega⟩ = .rightEnd := by
  simp [tapeAt]

theorem tapeAt_inner {α : Type*} (w : List α) (i : Fin (w.length + 2))
    (h0 : 0 < i.val) (h1 : i.val ≤ w.length) :
    tapeAt w i = .sym (w.get ⟨i.val - 1, by omega⟩) := by
  simp [tapeAt, Nat.ne_of_gt h0, h1]

/-- Advance a head position `pos : Fin (n + 2)` by `m : Move`, clamping at endmarkers `0` and
`n + 1`. -/
def moveHead {n : ℕ} (pos : Fin (n + 2)) (m : Move) : Fin (n + 2) :=
  match m with
  | .left => ⟨pos.val - 1, by omega⟩
  | .stay => pos
  | .right => if h : pos.val + 1 < n + 2 then ⟨pos.val + 1, h⟩ else pos

@[simp]
theorem moveHead_stay {n : ℕ} (pos : Fin (n + 2)) : moveHead pos .stay = pos := by
  simp [moveHead]

@[simp]
theorem moveHead_left_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveHead pos .left).val = pos.val - 1 := by
  simp [moveHead]

theorem moveHead_right_val {n : ℕ} (pos : Fin (n + 2)) (h : pos.val + 1 < n + 2) :
    (moveHead pos .right).val = pos.val + 1 := by
  simp [moveHead, h]

theorem moveHead_right_last (n : ℕ) :
    moveHead (⟨n + 1, by omega⟩ : Fin (n + 2)) .right = ⟨n + 1, by omega⟩ := by
  simp [moveHead]

/-- A deterministic two-way `k`-pebble automaton (marker automaton) over alphabet `α` with state
space `Q`. Pebbles may only be placed on input cells (never on endmarkers), and every transition
conserves the partition between pebbles on the current cell (`A`) and available pebbles (`B`). -/
@[ext]
structure PebbleAutomaton (k : ℕ) (α : Type*) (Q : Type*) where
  /-- Initial state. -/
  q₀ : Q
  /-- Set of halting states. -/
  halting : Set Q
  /-- Set of accepting states (a subset of `halting`). -/
  accepting : Set Q
  /-- Accepting states are halting. -/
  accepting_subset_halting : accepting ⊆ halting
  /-- Deterministic transition function `δ q a A B = (q', C, D, dir)`. -/
  δ : Q → TapeSymbol α → Finset (Fin k) → Finset (Fin k) →
    Q × Finset (Fin k) × Finset (Fin k) × Move
  /-- New current-cell pebbles `C` and available pebbles `D` are disjoint whenever `A` and `B`
  are disjoint. -/
  pebble_disjoint : ∀ q a A B, Disjoint A B → Disjoint (δ q a A B).2.1 (δ q a A B).2.2.1
  /-- Pebble conservation `C ∪ D = A ∪ B` whenever `A` and `B` are disjoint. -/
  pebble_conserved : ∀ q a A B, Disjoint A B →
    (δ q a A B).2.1 ∪ (δ q a A B).2.2.1 = A ∪ B
  /-- No pebble is placed on the left endmarker. -/
  no_pebble_leftEnd : ∀ q A B, Disjoint A B → (δ q .leftEnd A B).2.1 = ∅
  /-- No pebble is placed on the right endmarker. -/
  no_pebble_rightEnd : ∀ q A B, Disjoint A B → (δ q .rightEnd A B).2.1 = ∅

namespace PebbleAutomaton

/-- Instantaneous configuration `(state, head, pebbles)` of a `k`-pebble automaton on an input
of length `n`. Pebble position `0` represents an available (off-tape) pebble; positions `1 .. n`
represent input tape cells. -/
@[ext]
structure Cfg (k n : ℕ) (Q : Type*) where
  /-- Current internal state. -/
  state : Q
  /-- Current input head position (`0` = left endmarker, `1 .. n` = input, `n + 1` = right
  endmarker). -/
  head : Fin (n + 2)
  /-- Positions of the `k` pebbles (`0` = off-tape, `1 .. n` = input cell). -/
  pebbles : Fin k → Fin (n + 1)
  deriving DecidableEq

/-- Coding configuration `(state, pebbles)` obtained by omitting the head position. -/
abbrev CodingCfg (k n : ℕ) (Q : Type*) := Q × (Fin k → Fin (n + 1))

/-- Project an instantaneous configuration to its coding configuration. -/
@[expose]
def Cfg.coding {k n : ℕ} {Q : Type*} (c : Cfg k n Q) : CodingCfg k n Q :=
  (c.state, c.pebbles)

/-- Initial configuration: state `q₀`, head at left endmarker `0`, all pebbles off-tape (`0`). -/
def initCfg {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (n : ℕ) : Cfg k n Q :=
  ⟨M.q₀, ⟨0, by omega⟩, fun _ ↦ ⟨0, by omega⟩⟩

@[simp]
theorem initCfg_state {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (n : ℕ) :
    (M.initCfg n).state = M.q₀ := by
  simp [initCfg]

@[simp]
theorem initCfg_head_val {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (n : ℕ) :
    (M.initCfg n).head.val = 0 := by
  simp [initCfg]

@[simp]
theorem initCfg_pebbles_val {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (n : ℕ) (r : Fin k) :
    ((M.initCfg n).pebbles r).val = 0 := by
  simp [initCfg]

/-- Pebbles currently resting on the scanned cell (`∅` when scanning an endmarker). -/
def pebblesAtHead {k n : ℕ} {Q : Type*} (c : Cfg k n Q) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ (c.pebbles i).val = c.head.val ∧ c.head.val ≠ 0

theorem mem_pebblesAtHead_iff {k n : ℕ} {Q : Type*} (c : Cfg k n Q) (i : Fin k) :
    i ∈ pebblesAtHead c ↔ (c.pebbles i).val = c.head.val ∧ c.head.val ≠ 0 := by
  simp [pebblesAtHead]

/-- Pebbles currently available (off-tape, position `0`). -/
def pebblesAvail {k n : ℕ} {Q : Type*} (c : Cfg k n Q) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ (c.pebbles i).val = 0

theorem mem_pebblesAvail_iff {k n : ℕ} {Q : Type*} (c : Cfg k n Q) (i : Fin k) :
    i ∈ pebblesAvail c ↔ (c.pebbles i).val = 0 := by
  simp [pebblesAvail]

theorem disjoint_pebblesAtHead_pebblesAvail {k n : ℕ} {Q : Type*} (c : Cfg k n Q) :
    Disjoint (pebblesAtHead c) (pebblesAvail c) := by
  rw [Finset.disjoint_left]
  intro i hiA hiB
  simp only [pebblesAtHead, pebblesAvail, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
  exact hiA.2 (hiA.1.symm.trans hiB)

/-- Single deterministic transition step of a `k`-pebble automaton on input `w`. Halting states
are fixed points. -/
noncomputable def step {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α)
    (c : Cfg k w.length Q) : Cfg k w.length Q :=
  let := Classical.propDecidable
  if c.state ∈ M.halting then
    c
  else
    let A := pebblesAtHead c
    let B := pebblesAvail c
    let res := M.δ c.state (tapeAt w c.head) A B
    let q' := res.1
    let C := res.2.1
    let D := res.2.2.1
    let dir := res.2.2.2
    let p' : Fin k → Fin (w.length + 1) := fun i ↦
      if i ∈ C then
        if hpos : c.head.val ≤ w.length then
          ⟨c.head.val, Nat.lt_succ_of_le hpos⟩
        else
          ⟨0, Nat.zero_lt_succ _⟩
      else if i ∈ D then
        ⟨0, Nat.zero_lt_succ _⟩
      else
        c.pebbles i
    ⟨q', moveHead c.head dir, p'⟩

/-- Configuration reached by `M` on input `w` after `t` steps. -/
noncomputable def run {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) (t : ℕ) :
    Cfg k w.length Q :=
  (M.step w)^[t] (M.initCfg w.length)

@[simp]
theorem run_zero {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) :
    M.run w 0 = M.initCfg w.length := by
  simp [run]

theorem run_succ {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) (t : ℕ) :
    M.run w (t + 1) = M.step w (M.run w t) :=
  Function.iterate_succ_apply' (M.step w) t (M.initCfg w.length)

theorem run_add {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) (d t : ℕ) :
    M.run w (d + t) = (M.step w)^[d] (M.run w t) :=
  Function.iterate_add_apply (M.step w) d t (M.initCfg w.length)

theorem step_of_mem_halting {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α)
    {c : Cfg k w.length Q} (h : c.state ∈ M.halting) : M.step w c = c := by
  simp [step, h]

theorem step_of_not_mem_halting {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α)
    {c : Cfg k w.length Q} (h : c.state ∉ M.halting) :
    M.step w c =
      let res := M.δ c.state (tapeAt w c.head) (pebblesAtHead c) (pebblesAvail c)
      ⟨res.1, moveHead c.head res.2.2.2,
        fun i ↦
          if i ∈ res.2.1 then
            if hpos : c.head.val ≤ w.length then ⟨c.head.val, Nat.lt_succ_of_le hpos⟩
            else ⟨0, Nat.zero_lt_succ _⟩
          else if i ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩
          else c.pebbles i⟩ := by
  unfold step
  simp only [h, ↓reduceIte]
  congr 1
  funext i
  by_cases h1 : i ∈ (M.δ c.state (tapeAt w c.head) (pebblesAtHead c) (pebblesAvail c)).2.1
  · by_cases hpos : c.head.val ≤ w.length <;> simp [h1, hpos]
  · by_cases h2 : i ∈ (M.δ c.state (tapeAt w c.head) (pebblesAtHead c) (pebblesAvail c)).2.2.1
    · simp [h1, h2]
    · simp [h1, h2]

theorem run_eq_of_mem_halting {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α)
    {t : ℕ} (h : (M.run w t).state ∈ M.halting) : ∀ s ≥ t, M.run w s = M.run w t := by
  intro s hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show t + (d + 1) = (t + d) + 1 by omega, run_succ, ih (by omega),
      step_of_mem_halting M w h]

/-- `M` halts on input `w`. -/
@[expose]
def Halts {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) : Prop :=
  ∃ t : ℕ, (M.run w t).state ∈ M.halting

/-- `M` accepts input `w`. -/
@[expose]
def Accepts {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) : Prop :=
  ∃ t : ℕ, (M.run w t).state ∈ M.accepting

/-- `M` rejects input `w` (halts in a non-accepting state). -/
@[expose]
def Rejects {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) (w : List α) : Prop :=
  ∃ t : ℕ, (M.run w t).state ∈ M.halting ∧ (M.run w t).state ∉ M.accepting

theorem accepts_iff_not_rejects_of_halts {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    {w : List α} (hH : M.Halts w) : M.Accepts w ↔ ¬ M.Rejects w := by
  constructor
  · rintro ⟨t₁, ht₁⟩ ⟨t₂, ht₂H, ht₂N⟩
    rcases le_total t₁ t₂ with hle | hle
    · have heq := M.run_eq_of_mem_halting w (M.accepting_subset_halting ht₁) t₂ hle
      exact ht₂N (heq ▸ ht₁)
    · have heq := M.run_eq_of_mem_halting w ht₂H t₁ hle
      exact ht₂N (heq.symm ▸ ht₁)
  · intro hNR
    rcases hH with ⟨t, ht⟩
    by_contra hNA
    exact hNR ⟨t, ht, fun ha ↦ hNA ⟨t, ha⟩⟩

/-- The language accepted by `M`. -/
@[expose]
def acceptedLanguage {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q) : Set (List α) :=
  {w | M.Accepts w}

theorem mem_acceptedLanguage_iff {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (w : List α) : w ∈ M.acceptedLanguage ↔ M.Accepts w :=
  Iff.rfl

/-- The finite set of coding configurations visited by `M` during its run on `w`. -/
noncomputable def visitedCodingConfigs {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) : Finset (CodingCfg k w.length Q) :=
  let := Classical.propDecidable
  Finset.univ.filter fun c ↦ ∃ t : ℕ, (M.run w t).coding = c

theorem mem_visitedCodingConfigs_iff {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) (c : CodingCfg k w.length Q) :
    c ∈ M.visitedCodingConfigs w ↔ ∃ t : ℕ, (M.run w t).coding = c := by
  classical
  simp [visitedCodingConfigs]

theorem initCfg_coding_mem_visitedCodingConfigs {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) :
    (M.initCfg w.length).coding ∈ M.visitedCodingConfigs w := by
  classical
  simp only [visitedCodingConfigs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, by simp⟩

theorem visitedCodingConfigs_nonempty {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) :
    (M.visitedCodingConfigs w).Nonempty :=
  ⟨(M.initCfg w.length).coding, M.initCfg_coding_mem_visitedCodingConfigs w⟩

/-- The finite set of pebble-position tuples visited by `M` on `w`. -/
noncomputable def visitedPebbleTuples {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) : Finset (Fin k → Fin (w.length + 1)) :=
  (M.visitedCodingConfigs w).image Prod.snd

theorem card_visitedCodingConfigs_le_mul_pebbleTuples {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) :
    (M.visitedCodingConfigs w).card ≤
      Fintype.card Q * (M.visitedPebbleTuples w).card := by
  classical
  have hsub : M.visitedCodingConfigs w ⊆
      (Finset.univ : Finset Q) ×ˢ M.visitedPebbleTuples w := by
    intro c hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ c.1,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  calc
    (M.visitedCodingConfigs w).card
      ≤ ((Finset.univ : Finset Q) ×ˢ M.visitedPebbleTuples w).card :=
        Finset.card_le_card hsub
    _ = Fintype.card Q * (M.visitedPebbleTuples w).card := by
        rw [Finset.card_product, Finset.card_univ]

/-- Number of steps in `[0, T)` at which the pebble-position tuple changes. -/
noncomputable def pebbleChangeCount {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (w : List α) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    pebbleChangeCount M w t +
      if (M.run w (t + 1)).pebbles = (M.run w t).pebbles then 0 else 1

@[simp]
theorem pebbleChangeCount_zero {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (w : List α) : M.pebbleChangeCount w 0 = 0 := by rfl

theorem pebbleChangeCount_succ {k : ℕ} {α Q : Type*} (M : PebbleAutomaton k α Q)
    (w : List α) (t : ℕ) :
    M.pebbleChangeCount w (t + 1) =
      M.pebbleChangeCount w t +
        if (M.run w (t + 1)).pebbles = (M.run w t).pebbles then 0 else 1 := by rfl

theorem card_pebbleTuples_range_le {k : ℕ} {α Q : Type*}
    (M : PebbleAutomaton k α Q) (w : List α) (T : ℕ) :
    ((Finset.range (T + 1)).image (fun t ↦ (M.run w t).pebbles)).card ≤
      1 + M.pebbleChangeCount w T := by
  induction T with
  | zero => simp [pebbleChangeCount]
  | succ t ih =>
    rw [Finset.range_add_one, Finset.image_insert, pebbleChangeCount]
    by_cases h : (M.run w (t + 1)).pebbles = (M.run w t).pebbles
    · simp only [h, ↓reduceIte, add_zero]
      have hmem : (M.run w t).pebbles ∈
          (Finset.range (t + 1)).image (fun s ↦ (M.run w s).pebbles) :=
        Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_self t), rfl⟩
      rw [Finset.insert_eq_of_mem hmem]
      exact ih
    · simp only [h, ↓reduceIte]
      calc
        (insert (M.run w (t + 1)).pebbles
            ((Finset.range (t + 1)).image (fun s ↦ (M.run w s).pebbles))).card
          ≤ ((Finset.range (t + 1)).image (fun s ↦ (M.run w s).pebbles)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (1 + M.pebbleChangeCount w t) + 1 := by omega
        _ = 1 + (M.pebbleChangeCount w t + 1) := by omega

theorem card_visitedCodingConfigs_le_of_halts_in {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) (T : ℕ)
    (hT : (M.run w T).state ∈ M.halting) :
    (M.visitedCodingConfigs w).card ≤ Fintype.card Q * (1 + M.pebbleChangeCount w T) := by
  classical
  have hsub : M.visitedPebbleTuples w ⊆
      (Finset.range (T + 1)).image (fun t ↦ (M.run w t).pebbles) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨c, hc, rfl⟩
    simp only [visitedCodingConfigs, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨t, rfl⟩
    by_cases ht : t ≤ T
    · exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_of_le ht), rfl⟩
    · refine Finset.mem_image.mpr ⟨T, Finset.mem_range.mpr (Nat.lt_succ_self T), ?_⟩
      exact congrArg Cfg.pebbles (M.run_eq_of_mem_halting w hT t (by omega)).symm
  calc
    (M.visitedCodingConfigs w).card
      ≤ Fintype.card Q * (M.visitedPebbleTuples w).card :=
        M.card_visitedCodingConfigs_le_mul_pebbleTuples w
    _ ≤ Fintype.card Q * ((Finset.range (T + 1)).image (fun t ↦ (M.run w t).pebbles)).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
    _ ≤ Fintype.card Q * (1 + M.pebbleChangeCount w T) :=
        Nat.mul_le_mul_left _ (M.card_pebbleTuples_range_le w T)

/-- Uniform distribution over the finite set of coding configurations visited by `M` on `w`. -/
noncomputable def codingConfigPMF {k : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (w : List α) : PMF (CodingCfg k w.length Q) :=
  uniformOfFinset (M.visitedCodingConfigs w) (M.visitedCodingConfigs_nonempty w)

theorem codingConfigPMF_apply {k : ℕ} {α Q : Type*} [Fintype Q] [DecidableEq Q]
    (M : PebbleAutomaton k α Q) (w : List α) (c : CodingCfg k w.length Q) :
    M.codingConfigPMF w c =
      if c ∈ M.visitedCodingConfigs w then ((M.visitedCodingConfigs w).card : ENNReal)⁻¹
      else 0 := by
  simp [codingConfigPMF, uniformOfFinset_apply]

/-- The random variable `X_M(W)` obtained by sampling `w` from `W` (supported on strings of
length `n`) and then sampling a visited coding configuration of `M` on `w` uniformly at random. -/
noncomputable def codingConfigDist {k n : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (W : PMF {w : List α // w.length = n}) :
    PMF (CodingCfg k n Q) :=
  W.bind fun w ↦ w.2 ▸ M.codingConfigPMF w.1

theorem codingConfigDist_eq {k n : ℕ} {α Q : Type*} [Fintype Q]
    (M : PebbleAutomaton k α Q) (W : PMF {w : List α // w.length = n}) :
    M.codingConfigDist W = W.bind fun w ↦ w.2 ▸ M.codingConfigPMF w.1 := by rfl

/-- Shannon entropy of `X_M(W)` (in bits) is bounded above by
`k * log₂ (n + 1) + log₂ |Q|`. -/
theorem entropy_codingConfigDist_le {k n : ℕ} {α Q : Type*} [Fintype Q] [Nonempty Q]
    (M : PebbleAutomaton k α Q) (W : PMF {w : List α // w.length = n}) :
    entropy (M.codingConfigDist W) ≤
      (k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ) := by
  have hle := entropy_le_log_card (M.codingConfigDist W)
  have hcard : (Fintype.card (CodingCfg k n Q) : ℝ) =
      (Fintype.card Q : ℝ) * ((n + 1 : ℝ) ^ k) := by
    simp [CodingCfg, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  have hQpos : (0 : ℝ) < (Fintype.card Q : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  rw [hcard, Real.logb_mul hQpos.ne' (pow_pos hnpos k).ne', Real.logb_pow] at hle
  linarith

private theorem entropy_le_logb_card_of_support_subset {γ : Type*} [Finite γ]
    (p : PMF γ) (B : Finset γ) (hB : B.Nonempty) (hsupp : ∀ x ∈ p.support, x ∈ B) :
    entropy p ≤ Real.logb 2 (B.card : ℝ) := by
  classical
  let e : γ → {x : γ // x ∈ B} := fun x ↦
    if hx : x ∈ B then ⟨x, hx⟩ else ⟨hB.choose, hB.choose_spec⟩
  have he : Set.InjOn e p.support := by
    intro x hx y hy hxy
    have hxB : x ∈ B := hsupp x hx
    have hyB : y ∈ B := hsupp y hy
    simp only [e, hxB, hyB, ↓reduceDIte, Subtype.mk.injEq] at hxy
    exact hxy
  rw [← entropy_map_of_injOn p he]
  simpa [Fintype.card_coe] using entropy_le_log_card (p.map e)

/-- General deterministic dilution upper bound: if `B` is a deterministic nonempty set of
coding configurations of size `K` contained in `visitedCodingConfigs M w` for every `w` in the
support of `W`, and at most `S` additional coding configurations outside `B` are visited for
each such `w`, then
`H(X_M(W)) ≤ 1 + log₂ K + (S / K) * (k * log₂ (n + 1) + log₂ |Q|)`. -/
theorem entropy_codingConfigDist_diluted_le {k n : ℕ} {α Q : Type*}
    [Fintype Q] [Nonempty Q] [DecidableEq Q]
    (M : PebbleAutomaton k α Q) (W : PMF {w : List α // w.length = n})
    (B : Finset (CodingCfg k n Q)) (hBne : B.Nonempty) (S : ℕ)
    (hBsub : ∀ w ∈ W.support, B ⊆ w.2 ▸ M.visitedCodingConfigs w.1)
    (hS : ∀ w ∈ W.support, ((w.2 ▸ M.visitedCodingConfigs w.1) \ B).card ≤ S) :
    entropy (M.codingConfigDist W) ≤
      1 + Real.logb 2 (B.card : ℝ) +
        ((S : ℝ) / (B.card : ℝ)) *
          ((k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ)) := by
  classical
  set X : PMF (CodingCfg k n Q) := M.codingConfigDist W
  let ind : CodingCfg k n Q → Bool := fun c ↦ decide (c ∉ B)
  let joint : PMF (Bool × CodingCfg k n Q) := X.map fun c ↦ (ind c, c)
  have hX_eq : entropy X = entropy (joint.map Prod.fst) + conditionalEntropy joint := by
    have hinj : Function.Injective (fun c : CodingCfg k n Q ↦ (ind c, c)) :=
      fun _ _ h ↦ (Prod.mk.inj h).2
    have hj : entropy joint = entropy X := entropy_map_of_injective X hinj
    simp [conditionalEntropy, hj]
  have hbool : entropy (joint.map Prod.fst) ≤ 1 := by
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      entropy_le_log_card (joint.map Prod.fst)
  have hcond : conditionalEntropy joint =
      ((joint.map Prod.fst) false).toReal * entropy (conditionalSnd joint false) +
      ((joint.map Prod.fst) true).toReal * entropy (conditionalSnd joint true) := by
    rw [conditionalEntropy_eq_sum, Fintype.sum_bool, add_comm]
  have hfalse_term :
      ((joint.map Prod.fst) false).toReal * entropy (conditionalSnd joint false) ≤
        Real.logb 2 (B.card : ℝ) := by
    by_cases hpf : (joint.map Prod.fst) false = 0
    · simp only [hpf, ENNReal.toReal_zero, zero_mul]
      exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hBne.card_pos)
    · have hsupp : ∀ c ∈ (conditionalSnd joint false).support, c ∈ B := by
        intro c hc
        have hmem := (mem_support_conditionalSnd_iff joint false hpf c).mp hc
        have hmem' := (PMF.mem_support_map_iff _ _ _).mp hmem
        rcases hmem' with ⟨c', _, hc'⟩
        have hind : ind c' = false := (Prod.mk.inj hc').1
        have hcc : c' = c := (Prod.mk.inj hc').2
        rw [← hcc]
        simpa [ind] using hind
      have hent := entropy_le_logb_card_of_support_subset
        (conditionalSnd joint false) B hBne hsupp
      have hprob_le : ((joint.map Prod.fst) false).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one
          (by simpa using PMF.coe_le_one (joint.map Prod.fst) false)
      have hlog_nonneg : 0 ≤ Real.logb 2 (B.card : ℝ) :=
        Real.logb_nonneg (by norm_num) (by exact_mod_cast hBne.card_pos)
      calc
        ((joint.map Prod.fst) false).toReal * entropy (conditionalSnd joint false)
          ≤ ((joint.map Prod.fst) false).toReal * Real.logb 2 (B.card : ℝ) :=
            mul_le_mul_of_nonneg_left hent ENNReal.toReal_nonneg
        _ ≤ 1 * Real.logb 2 (B.card : ℝ) :=
            mul_le_mul_of_nonneg_right hprob_le hlog_nonneg
        _ = Real.logb 2 (B.card : ℝ) := one_mul _
  have htrue_prob : ((joint.map Prod.fst) true).toReal ≤ (S : ℝ) / (B.card : ℝ) := by
    have hmap : joint.map Prod.fst = X.map ind := by
      simp [joint, PMF.map_comp, Function.comp_def]
    rw [hmap]
    have hsum : (X.map ind) true =
        ∑' w : {w : List α // w.length = n}, W w *
          ((w.2 ▸ M.codingConfigPMF w.1 : PMF (CodingCfg k n Q)).map ind) true := by
      simp [X, codingConfigDist, PMF.map_bind, PMF.bind_apply]
    have hpt : ∀ w : {w : List α // w.length = n},
        W w * ((w.2 ▸ M.codingConfigPMF w.1 : PMF (CodingCfg k n Q)).map ind) true ≤
          W w * ENNReal.ofReal ((S : ℝ) / (B.card : ℝ)) := by
      intro w
      by_cases hw : W w = 0
      · simp [hw]
      · refine mul_le_mul_of_nonneg_left ?_ zero_le
        have hwsupp : w ∈ W.support := (PMF.mem_support_iff W w).mpr hw
        rcases w with ⟨wlist, hwlen⟩
        subst hwlen
        set V := M.visitedCodingConfigs wlist
        have hBsub' : B ⊆ V := hBsub ⟨wlist, rfl⟩ hwsupp
        have hS' : (V \ B).card ≤ S := hS ⟨wlist, rfl⟩ hwsupp
        have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr hBne.card_pos
        have hpmf : ((M.codingConfigPMF wlist).map ind) true =
            ((V \ B).card : ENNReal) / (V.card : ENNReal) := by
          rw [PMF.map_apply, tsum_fintype, ← Finset.sum_subset (Finset.subset_univ (V \ B))]
          · rw [div_eq_mul_inv, ← nsmul_eq_mul, ← Finset.sum_const]
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            rcases Finset.mem_sdiff.mp ha with ⟨haV, haB⟩
            have hind : true = ind a := by simp [ind, haB]
            simp only [hind, ↓reduceIte, codingConfigPMF, uniformOfFinset_apply]
            have haV' : a ∈ M.visitedCodingConfigs wlist := haV
            simp [haV']
            rfl
          · intro a _ haVB
            by_cases haB : a ∈ B
            · have hind : ¬ (true = ind a) := by simp [ind, haB]
              simp [hind]
            · have haV : a ∉ M.visitedCodingConfigs wlist :=
                fun h ↦ haVB (Finset.mem_sdiff.mpr ⟨h, haB⟩)
              split_ifs
              · rw [codingConfigPMF, uniformOfFinset_apply]; simp [haV]
              · rfl
        rw [hpmf]
        have hle1 : ((V \ B).card : ENNReal) / (V.card : ENNReal) ≤
            (S : ENNReal) / (B.card : ENNReal) := by
          refine ENNReal.div_le_div ?_ ?_
          · exact_mod_cast hS'
          · exact_mod_cast Finset.card_le_card hBsub'
        have hle2 : (S : ENNReal) / (B.card : ENNReal) =
            ENNReal.ofReal ((S : ℝ) / (B.card : ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos hBpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        exact hle2 ▸ hle1
    have hle_enn : (X.map ind) true ≤ ENNReal.ofReal ((S : ℝ) / (B.card : ℝ)) := by
      rw [hsum]
      calc
        ∑' w, W w * ((w.2 ▸ M.codingConfigPMF w.1 : PMF (CodingCfg k n Q)).map ind) true
          ≤ ∑' w, W w * ENNReal.ofReal ((S : ℝ) / (B.card : ℝ)) := tsum_le_tsum hpt
        _ = (∑' w, W w) * ENNReal.ofReal ((S : ℝ) / (B.card : ℝ)) := ENNReal.tsum_mul_right
        _ = ENNReal.ofReal ((S : ℝ) / (B.card : ℝ)) := by rw [W.tsum_coe, one_mul]
    have hnonneg : (0 : ℝ) ≤ (S : ℝ) / (B.card : ℝ) := by positivity
    exact ENNReal.toReal_le_of_le_ofReal hnonneg hle_enn
  have htrue_ent : entropy (conditionalSnd joint true) ≤
      (k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ) := by
    have hle := entropy_le_log_card (conditionalSnd joint true)
    have hcard : (Fintype.card (CodingCfg k n Q) : ℝ) =
        (Fintype.card Q : ℝ) * ((n + 1 : ℝ) ^ k) := by
      simp [CodingCfg, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
    have hQpos : (0 : ℝ) < (Fintype.card Q : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hnpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    rw [hcard, Real.logb_mul hQpos.ne' (pow_pos hnpos k).ne', Real.logb_pow] at hle
    linarith
  have htrue_term :
      ((joint.map Prod.fst) true).toReal * entropy (conditionalSnd joint true) ≤
        ((S : ℝ) / (B.card : ℝ)) *
          ((k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ)) := by
    have hE_nonneg : 0 ≤ entropy (conditionalSnd joint true) := entropy_nonneg _
    have hR_nonneg : 0 ≤ (k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ) :=
      le_trans hE_nonneg htrue_ent
    calc
      ((joint.map Prod.fst) true).toReal * entropy (conditionalSnd joint true)
        ≤ ((joint.map Prod.fst) true).toReal *
            ((k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ)) :=
          mul_le_mul_of_nonneg_left htrue_ent ENNReal.toReal_nonneg
      _ ≤ ((S : ℝ) / (B.card : ℝ)) *
            ((k : ℝ) * Real.logb 2 (n + 1 : ℝ) + Real.logb 2 (Fintype.card Q : ℝ)) :=
          mul_le_mul_of_nonneg_right htrue_prob hR_nonneg
  linarith

end PebbleAutomaton

/-- The `k`-th level `REG_k` of the deterministic pebble hierarchy: languages over finite
alphabets decided by a halting deterministic `k`-pebble automaton. -/
@[expose]
def REG (k : ℕ) : LanguageClass.{u} :=
  fun {α} _ ↦ {L : Set (List α) |
    ∃ (Q : Type u) (_ : Fintype Q) (M : PebbleAutomaton k α Q),
      (∀ w, M.Halts w) ∧ M.acceptedLanguage = L}

theorem mem_REG_iff {k : ℕ} {α : Type u} [Fintype α] {L : Set (List α)} :
    L ∈ REG k ↔ ∃ (Q : Type u) (_ : Fintype Q) (M : PebbleAutomaton k α Q),
      (∀ w, M.Halts w) ∧ M.acceptedLanguage = L :=
  Iff.rfl

/-- Ceiling base-2 logarithm `⌈log₂ l⌉` (`Nat.clog 2 l`). -/
def ceilLog2 (l : ℕ) : ℕ := Nat.clog 2 l

/-- Asymptotic entropy lower bound across all halting automata accepting `L` implies
`L ∉ REG (k - 1)`. -/
theorem not_mem_REG_of_asymp_entropy_ge {k : ℕ} (hk : 1 ≤ k) {α : Type u} [Fintype α]
    {L : Set (List α)} (S : Set (List α))
    (X : ∀ l : ℕ, (S ∩ {w | w.length = l}).Nonempty → PMF {w : List α // w.length = l})
    (hinf : ∀ N : ℕ, ∃ l ≥ N, (S ∩ {w | w.length = l}).Nonempty)
    (hbound : ∀ (Q : Type u) [Fintype Q] (M : PebbleAutomaton (k - 1) α Q),
      (∀ w, M.Halts w) → M.acceptedLanguage = L →
      ∀ γ : ℝ, 0 < γ → ∃ N : ℕ, ∀ l ≥ N,
        ∀ hne : (S ∩ {w | w.length = l}).Nonempty,
          (1 - γ) * (k : ℝ) * (ceilLog2 l : ℝ) ≤ entropy (M.codingConfigDist (X l hne))) :
    L ∉ REG (k - 1) := by
  rintro ⟨Q, _, M, hHalts, hAcc⟩
  have hQne : Nonempty Q := ⟨M.q₀⟩
  have hγ : (0 : ℝ) < 1 / (2 * (k : ℝ) + 1) := by positivity
  obtain ⟨N, hN⟩ := hbound Q M hHalts hAcc (1 / (2 * (k : ℝ) + 1)) hγ
  set C : ℕ := Nat.ceil (Real.logb 2 (Fintype.card Q : ℝ)) + 1
  obtain ⟨l, hl_ge, hne⟩ := hinf (max N (2 ^ (4 * k * C + 8) + 2))
  have hlN : N ≤ l := le_trans (le_max_left _ _) hl_ge
  have hl_big : 2 ^ (4 * k * C + 8) + 2 ≤ l := le_trans (le_max_right _ _) hl_ge
  have hlb := hN l hlN hne
  have hub := M.entropy_codingConfigDist_le (X l hne)
  have hpow : l ≤ 2 ^ ceilLog2 l := Nat.le_pow_clog (by norm_num) l
  have hl1_le : ((l : ℝ) + 1) ≤ (2 : ℝ) ^ (ceilLog2 l + 1) := by
    have hnat : l + 1 ≤ 2 ^ (ceilLog2 l + 1) := by
      have : 1 ≤ 2 ^ (4 * k * C + 8) := Nat.one_le_pow _ _ (by norm_num)
      calc l + 1 ≤ 2 * l := by omega
        _ ≤ 2 * 2 ^ ceilLog2 l := by omega
        _ = 2 ^ (ceilLog2 l + 1) := by rw [pow_succ']
    exact_mod_cast hnat
  have hlog_l1 : Real.logb 2 ((l : ℝ) + 1) ≤ (ceilLog2 l : ℝ) + 1 := by
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (l : ℝ) + 1) hl1_le
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h1
    exact_mod_cast h1
  have hclog_big : 4 * k * C + 8 ≤ ceilLog2 l := by
    have h1 : 2 ^ (4 * k * C + 8) < l := by omega
    have h2 : 2 ^ (4 * k * C + 8) < 2 ^ ceilLog2 l := lt_of_lt_of_le h1 hpow
    have h3 : 4 * k * C + 8 < ceilLog2 l := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
    omega
  have hclog_R : (4 * (k : ℝ) * (C : ℝ) + 8 : ℝ) ≤ (ceilLog2 l : ℝ) := by
    exact_mod_cast hclog_big
  have hlogQ_le : Real.logb 2 (Fintype.card Q : ℝ) ≤ (C : ℝ) := by
    have h1 := Nat.le_ceil (Real.logb 2 (Fintype.card Q : ℝ))
    have h2 : (Nat.ceil (Real.logb 2 (Fintype.card Q : ℝ)) : ℝ) ≤ (C : ℝ) := by
      dsimp [C]; push_cast; linarith
    linarith
  have hk_R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hC_R : (1 : ℝ) ≤ (C : ℝ) := by
    dsimp [C]; push_cast; linarith
  have hgap : ((k - 1 : ℕ) : ℝ) * ((ceilLog2 l : ℝ) + 1) + (C : ℝ) <
      (1 - 1 / (2 * (k : ℝ) + 1)) * (k : ℝ) * (ceilLog2 l : ℝ) := by
    have hk_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
    rw [hk_sub]
    have hdenom : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    rw [show 1 - 1 / (2 * (k : ℝ) + 1) = (2 * (k : ℝ)) / (2 * (k : ℝ) + 1) by field_simp; ring]
    rw [show (2 * (k : ℝ)) / (2 * (k : ℝ) + 1) * (k : ℝ) * (ceilLog2 l : ℝ) =
        (2 * (k : ℝ) * (k : ℝ) * (ceilLog2 l : ℝ)) / (2 * (k : ℝ) + 1) by ring]
    rw [lt_div_iff₀ hdenom]
    nlinarith [mul_le_mul_of_nonneg_left hclog_R (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (C : ℝ) - 1)]
  have hkm1_nonneg : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hub' : entropy (M.codingConfigDist (X l hne)) ≤
      ((k - 1 : ℕ) : ℝ) * ((ceilLog2 l : ℝ) + 1) + (C : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hlog_l1 hkm1_nonneg
    linarith
  linarith

end CslibFrontier.Computability.Automata
