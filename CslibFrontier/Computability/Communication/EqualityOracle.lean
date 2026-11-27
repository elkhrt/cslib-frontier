/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Protocol
public import Mathlib.Data.Nat.Log
public import Mathlib.InformationTheory.Hamming

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Oracle Communication Protocols and Equality-Oracle Complexity

This module defines deterministic two-party communication protocols equipped with an
unrestricted-width Boolean communication oracle family (`OracleProtocol`), and specializes the model
to the `Equality` oracle (`eqOracle`) and the `k`-Hamming distance oracle (`hammingOracle k`),
together with nondeterministic `Equality`-oracle communication complexity
(`ndEqOracleComplexity`), under standard Lean axioms.

## Main definitions

* `CslibFrontier.Communication.OracleProtocol`: deterministic two-party communication protocol
making
  adaptive queries to an oracle family `Q : ∀ i, A i → B i → Bool` of arbitrary instance index `i`.
* `CslibFrontier.Communication.oracleEcomplexity`: worst-case deterministic `Q`-oracle query
complexity
  in `ℕ∞`.
* `CslibFrontier.Communication.eqOracle`, `CslibFrontier.Communication.eqOracleEcomplexity`,
  `CslibFrontier.Communication.eqOracleComplexity`: unrestricted-width `Equality` oracle and its
  deterministic query complexity `D^Eq`.
* `CslibFrontier.Communication.hammingOracle`,
`CslibFrontier.Communication.hammingOracleEcomplexity`,
  `CslibFrontier.Communication.hammingOracleComplexity`: unrestricted-width `k`-Hamming distance
  oracle
  `HD_k` and its deterministic query complexity `D^{HD_k}`.
* `CslibFrontier.Communication.HasNdEqCover`, `CslibFrontier.Communication.ndEqOracleComplexity`:
  nondeterministic `Equality`-oracle covers and complexity `ND^Eq`.

## Main results

* `CslibFrontier.Communication.oracleEcomplexity_le_mul_of_simulate`: query-for-query simulation
bound
  between oracle communication models.
* `CslibFrontier.Communication.eqOracleEcomplexity_le_protocol`: `D^Eq(f) ≤ D(f)` for every
two-party
  function `f`.
* `CslibFrontier.Communication.hammingOracleEcomplexity_le_eqOracle`: `D^{HD_k}(f) ≤ D^Eq(f)` via
  `(k + 1)`-fold repetition of query coordinates.
* `CslibFrontier.Communication.eqOracleComplexity_le_clog_card_succ`: `D^Eq(f) ≤ ⌈log₂ |X|⌉ + 1` on
any
  finite domain `X`.
* `CslibFrontier.Communication.ndEqOracleComplexity_le_eqOracleComplexity`: `ND^Eq(f) ≤ D^Eq(f)`.
-/

public section

open Finset Cslib Cslib.Communication

namespace CslibFrontier.Communication

section OracleProtocol

variable {ι : Type*} {A B : ι → Type*}

/-- A deterministic two-party communication protocol with access to a Boolean communication oracle
family `Q : ∀ i, A i → B i → Bool`. At each internal node, Alice and Bob choose an oracle instance
`idx : ι`, locally map their inputs via `alice : X → A idx` and `bob : Y → B idx`, query
`Q idx (alice x) (bob y)`, and branch on the Boolean answer. -/
inductive OracleProtocol (Q : ∀ i, A i → B i → Bool) (X Y Z : Type*) where
  /-- Terminate and output `val : Z`. -/
  | output (val : Z)
  /-- Query oracle instance `idx` on `(alice x, bob y)` and branch on `false` vs. `true`. -/
  | query (idx : ι) (alice : X → A idx) (bob : Y → B idx)
      (onFalse onTrue : OracleProtocol Q X Y Z)

namespace OracleProtocol

variable {Q : ∀ i, A i → B i → Bool} {X Y Z W X' Y' : Type*}

/-- Evaluate an oracle communication protocol on input pair `(x, y)`. -/
def eval : OracleProtocol Q X Y Z → X → Y → Z
  | output z, _, _ => z
  | query i a b p₀ p₁, x, y => cond (Q i (a x) (b y)) (p₁.eval x y) (p₀.eval x y)

/-- Worst-case number of oracle queries (depth) of an oracle communication protocol. -/
def depth : OracleProtocol Q X Y Z → ℕ
  | output _ => 0
  | query _ _ _ p₀ p₁ => max p₀.depth p₁.depth + 1

@[simp]
theorem eval_output (z : Z) (x : X) (y : Y) :
    (output z : OracleProtocol Q X Y Z).eval x y = z := by rfl

@[simp]
theorem eval_query (i : ι) (a : X → A i) (b : Y → B i) (p₀ p₁ : OracleProtocol Q X Y Z)
    (x : X) (y : Y) :
    (query i a b p₀ p₁).eval x y = cond (Q i (a x) (b y)) (p₁.eval x y) (p₀.eval x y) := by rfl

@[simp]
theorem depth_output (z : Z) : (output z : OracleProtocol Q X Y Z).depth = 0 := by rfl

@[simp]
theorem depth_query (i : ι) (a : X → A i) (b : Y → B i) (p₀ p₁ : OracleProtocol Q X Y Z) :
    (query i a b p₀ p₁).depth = max p₀.depth p₁.depth + 1 := by rfl

/-- Pull back an oracle protocol along local input maps `f : X' → X` and `g : Y' → Y`. -/
def comap (f : X' → X) (g : Y' → Y) : OracleProtocol Q X Y Z → OracleProtocol Q X' Y' Z
  | output z => output z
  | query i a b p₀ p₁ => query i (a ∘ f) (b ∘ g) (p₀.comap f g) (p₁.comap f g)

@[simp]
theorem eval_comap (f : X' → X) (g : Y' → Y) (p : OracleProtocol Q X Y Z) (x : X') (y : Y') :
    (p.comap f g).eval x y = p.eval (f x) (g y) := by
  induction p with
  | output _ => rfl
  | query i a b p₀ p₁ ih₀ ih₁ =>
    cases h : Q i (a (f x)) (b (g y)) <;> simp [comap, Function.comp_apply, h, ih₀, ih₁]

@[simp]
theorem depth_comap (f : X' → X) (g : Y' → Y) (p : OracleProtocol Q X Y Z) :
    (p.comap f g).depth = p.depth := by
  induction p with
  | output _ => rfl
  | query _ _ _ _ _ ih₀ ih₁ => simp [comap, ih₀, ih₁]

/-- Sequentially compose an oracle protocol `p` with a family of continuation protocols `k`. -/
def bind : OracleProtocol Q X Y Z → (Z → OracleProtocol Q X Y W) → OracleProtocol Q X Y W
  | output z, k => k z
  | query i a b p₀ p₁, k => query i a b (p₀.bind k) (p₁.bind k)

@[simp]
theorem eval_bind (p : OracleProtocol Q X Y Z) (k : Z → OracleProtocol Q X Y W) (x : X) (y : Y) :
    (p.bind k).eval x y = (k (p.eval x y)).eval x y := by
  induction p with
  | output _ => rfl
  | query i a b p₀ p₁ ih₀ ih₁ =>
    cases h : Q i (a x) (b y) <;> simp [bind, h, ih₀, ih₁]

/-- Binding a depth-`≤ d₁` oracle protocol with depth-`≤ d₂` continuations yields depth at most
`d₁ + d₂`. -/
theorem depth_bind_le {p : OracleProtocol Q X Y Z} {k : Z → OracleProtocol Q X Y W}
    {d₁ d₂ : ℕ} (hp : p.depth ≤ d₁) (hk : ∀ z, (k z).depth ≤ d₂) :
    (p.bind k).depth ≤ d₁ + d₂ := by
  induction p generalizing d₁ with
  | output z => exact (hk z).trans (Nat.le_add_left d₂ d₁)
  | query i a b p₀ p₁ ih₀ ih₁ =>
    cases d₁ with
    | zero => simp at hp
    | succ d₁ =>
      simp only [depth_query, Nat.add_le_add_iff_right, max_le_iff] at hp
      simp only [bind, depth_query]
      have h₀ := ih₀ hp.1
      have h₁ := ih₁ hp.2
      omega

/-- Swap the roles of Alice and Bob for a symmetric oracle family. -/
def swap {C : ι → Type*} {S : ∀ i, C i → C i → Bool} :
    OracleProtocol S X Y Z → OracleProtocol S Y X Z
  | output z => output z
  | query i a b p₀ p₁ => query i b a p₀.swap p₁.swap

/-- `swap` computes `(y, x) ↦ p.eval x y` whenever every oracle in `S` is symmetric. -/
theorem eval_swap {C : ι → Type*} {S : ∀ i, C i → C i → Bool}
    (hS : ∀ i u v, S i u v = S i v u) (p : OracleProtocol S X Y Z) (x : X) (y : Y) :
    p.swap.eval y x = p.eval x y := by
  induction p with
  | output _ => rfl
  | query i a b p₀ p₁ ih₀ ih₁ =>
    simp only [swap, eval_query, hS i (b y) (a x)]
    cases S i (a x) (b y) <;> simp [ih₀, ih₁]

@[simp]
theorem depth_swap {C : ι → Type*} {S : ∀ i, C i → C i → Bool}
    (p : OracleProtocol S X Y Z) : p.swap.depth = p.depth := by
  induction p with
  | output _ => rfl
  | query _ _ _ _ _ ih₀ ih₁ => simp [swap, ih₀, ih₁]

/-- Replace every `Q₂`-query in `p` with a simulating `Q`-protocol supplied by `sim`. -/
def simulate {ι₂ : Type*} {A₂ B₂ : ι₂ → Type*} {Q₂ : ∀ j, A₂ j → B₂ j → Bool}
    (sim : ∀ j : ι₂, (X → A₂ j) → (Y → B₂ j) → OracleProtocol Q X Y Bool) :
    OracleProtocol Q₂ X Y Z → OracleProtocol Q X Y Z
  | output z => output z
  | query j a b p₀ p₁ =>
      (sim j a b).bind (fun ans ↦ if ans then p₁.simulate sim else p₀.simulate sim)

/-- `p.simulate sim` computes the same function as `p` whenever `sim` computes each query. -/
theorem eval_simulate {ι₂ : Type*} {A₂ B₂ : ι₂ → Type*} {Q₂ : ∀ j, A₂ j → B₂ j → Bool}
    (sim : ∀ j : ι₂, (X → A₂ j) → (Y → B₂ j) → OracleProtocol Q X Y Bool)
    (hsim : ∀ j a b x y, (sim j a b).eval x y = Q₂ j (a x) (b y))
    (p : OracleProtocol Q₂ X Y Z) (x : X) (y : Y) :
    (p.simulate sim).eval x y = p.eval x y := by
  induction p with
  | output _ => rfl
  | query j a b p₀ p₁ ih₀ ih₁ =>
    simp only [simulate, eval_bind, hsim, eval_query]
    cases Q₂ j (a x) (b y) <;> simp [ih₀, ih₁]

/-- If every simulated query has `Q`-depth at most `c`, then `(p.simulate sim).depth ≤ p.depth * c`.
-/
theorem depth_simulate_le {ι₂ : Type*} {A₂ B₂ : ι₂ → Type*} {Q₂ : ∀ j, A₂ j → B₂ j → Bool}
    (sim : ∀ j : ι₂, (X → A₂ j) → (Y → B₂ j) → OracleProtocol Q X Y Bool)
    {c : ℕ} (hsim : ∀ j a b, (sim j a b).depth ≤ c) (p : OracleProtocol Q₂ X Y Z) :
    (p.simulate sim).depth ≤ p.depth * c := by
  induction p with
  | output _ => simp [simulate]
  | query j a b p₀ p₁ ih₀ ih₁ =>
    simp only [simulate, depth_query, Nat.succ_mul]
    rw [add_comm _ c]
    refine depth_bind_le (hsim j a b) (fun ans ↦ ?_)
    have h₀ : p₀.depth * c ≤ max p₀.depth p₁.depth * c :=
      Nat.mul_le_mul_right c (le_max_left _ _)
    have h₁ : p₁.depth * c ≤ max p₀.depth p₁.depth * c :=
      Nat.mul_le_mul_right c (le_max_right _ _)
    cases ans <;> simp <;> omega

end OracleProtocol

/-- Minimum `Q`-oracle communication cost `D^Q(f)` (in `ℕ∞`) of computing `f : X → Y → Z`. -/
noncomputable def oracleEcomplexity (Q : ∀ i, A i → B i → Bool) {X Y Z : Type*}
    (f : X → Y → Z) : ℕ∞ :=
  ⨅ (p : OracleProtocol Q X Y Z) (_ : p.eval = f), (p.depth : ℕ∞)

/-- Any `Q`-protocol computing `f` bounds `oracleEcomplexity Q f`. -/
theorem oracleEcomplexity_le_depth {Q : ∀ i, A i → B i → Bool} {X Y Z : Type*}
    {p : OracleProtocol Q X Y Z} {f : X → Y → Z} (hp : p.eval = f) :
    oracleEcomplexity Q f ≤ p.depth :=
  iInf₂_le p hp

/-- `oracleEcomplexity Q f ≤ k` (for `k : ℕ`) iff there exists a depth-`≤ k` `Q`-protocol for `f`.
-/
theorem oracleEcomplexity_le_iff {Q : ∀ i, A i → B i → Bool} {X Y Z : Type*}
    {f : X → Y → Z} {k : ℕ} :
    oracleEcomplexity Q f ≤ k ↔ ∃ p : OracleProtocol Q X Y Z, p.eval = f ∧ p.depth ≤ k := by
  constructor
  · intro h
    have hlt : oracleEcomplexity Q f < (k + 1 : ℕ∞) :=
      lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self k)
    simp only [oracleEcomplexity, iInf_lt_iff] at hlt
    obtain ⟨p, hp, hd⟩ := hlt
    exact ⟨p, hp, by exact_mod_cast Order.le_of_lt_add_one hd⟩
  · rintro ⟨p, hp, hd⟩
    exact (oracleEcomplexity_le_depth hp).trans (by exact_mod_cast hd)

/-- Lower-bound principle for `oracleEcomplexity Q f`. -/
theorem le_oracleEcomplexity_iff {Q : ∀ i, A i → B i → Bool} {X Y Z : Type*}
    {f : X → Y → Z} {k : ℕ∞} :
    k ≤ oracleEcomplexity Q f ↔ ∀ p : OracleProtocol Q X Y Z, p.eval = f → k ≤ p.depth := by
  simp [oracleEcomplexity]

/-- Pulling back inputs does not increase `oracleEcomplexity`. -/
theorem oracleEcomplexity_comap_le (Q : ∀ i, A i → B i → Bool) {X Y Z X' Y' : Type*}
    (f : X → Y → Z) (a : X' → X) (b : Y' → Y) :
    oracleEcomplexity Q (fun x y ↦ f (a x) (b y)) ≤ oracleEcomplexity Q f := by
  rw [le_oracleEcomplexity_iff]
  intro p hp
  have hcomp : (p.comap a b).eval = fun x y ↦ f (a x) (b y) := by
    ext x y; simp [hp]
  exact (oracleEcomplexity_le_depth hcomp).trans (by simp)

/-- Oracle simulation inequality: `D^{Q₁}(f) ≤ D^{Q₂}(f) * c` whenever every `Q₂`-query on `X × Y`
can be computed in `Q₁`-cost at most `c`. -/
theorem oracleEcomplexity_le_mul_of_simulate
    {Q₁ : ∀ i, A i → B i → Bool} {ι₂ : Type*} {A₂ B₂ : ι₂ → Type*}
    {Q₂ : ∀ j, A₂ j → B₂ j → Bool} {X Y Z : Type*} (f : X → Y → Z) {c : ℕ}
    (hfin : oracleEcomplexity Q₂ f ≠ ⊤)
    (hsim : ∀ (j : ι₂) (a : X → A₂ j) (b : Y → B₂ j),
      oracleEcomplexity Q₁ (fun x y ↦ Q₂ j (a x) (b y)) ≤ c) :
    oracleEcomplexity Q₁ f ≤ oracleEcomplexity Q₂ f * c := by
  lift oracleEcomplexity Q₂ f to ℕ using hfin with d hd
  obtain ⟨p, hp, hpd⟩ := oracleEcomplexity_le_iff.mp hd.symm.le
  have hex : ∀ (j : ι₂) (a : X → A₂ j) (b : Y → B₂ j),
      ∃ q : OracleProtocol Q₁ X Y Bool,
        q.eval = (fun x y ↦ Q₂ j (a x) (b y)) ∧ q.depth ≤ c :=
    fun j a b ↦ oracleEcomplexity_le_iff.mp (hsim j a b)
  choose sim hsim_eval hsim_depth using hex
  let q := p.simulate sim
  have hq_eval : q.eval = f := by
    ext x y
    rw [OracleProtocol.eval_simulate sim
      (fun j a b x y ↦ congr_fun₂ (hsim_eval j a b) x y), hp]
  have hq_depth : q.depth ≤ d * c :=
    (OracleProtocol.depth_simulate_le sim hsim_depth p).trans (Nat.mul_le_mul_right c hpd)
  exact (oracleEcomplexity_le_depth hq_eval).trans (by exact_mod_cast hq_depth)

end OracleProtocol

section EqualityAndHammingOracles

variable {X Y Z X' Y' : Type*}

/-- The unrestricted-width `Equality` communication oracle family on bit strings of arbitrary
length `m : ℕ`. -/
def eqOracle (m : ℕ) : BitString m → BitString m → Bool :=
  equality

@[simp]
theorem eqOracle_apply (m : ℕ) (x y : BitString m) : eqOracle m x y = equality x y := by rfl

/-- The unrestricted-width `k`-Hamming distance communication oracle family `HD_k^m` on bit strings
of arbitrary length `m : ℕ`: returns `true` iff `hammingDist x y ≤ k`. -/
def hammingOracle (k : ℕ) (m : ℕ) : BitString m → BitString m → Bool :=
  fun x y ↦ decide (hammingDist x y ≤ k)

@[simp]
theorem hammingOracle_apply (k m : ℕ) (x y : BitString m) :
    hammingOracle k m x y = decide (hammingDist x y ≤ k) := by rfl

/-- Injective one-hot encoding of `Fin m` into `BitString m`. -/
private def oneHotFin {m : ℕ} (i : Fin m) : BitString m :=
  fun j ↦ decide (i = j)

private theorem oneHotFin_injective {m : ℕ} : Function.Injective (oneHotFin (m := m)) := by
  intro i₁ i₂ h
  have hi := congr_fun h i₂
  simpa [oneHotFin] using hi

/-- Construct a single `Equality`-oracle query comparing arbitrary finite-valued functions
`a : X → α` and `b : Y → α`. -/
noncomputable def eqQuery {α : Type*} [Finite α] (a : X → α) (b : Y → α)
    (onFalse onTrue : OracleProtocol eqOracle X Y Z) : OracleProtocol eqOracle X Y Z :=
  let _ : Fintype α := Fintype.ofFinite α
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  OracleProtocol.query (Fintype.card α)
    (fun x ↦ oneHotFin (e (a x))) (fun y ↦ oneHotFin (e (b y))) onFalse onTrue

/-- `eqQuery a b p₀ p₁` branches on whether `a x = b y`. -/
theorem eval_eqQuery {α : Type*} [Finite α] [DecidableEq α] (a : X → α) (b : Y → α)
    (p₀ p₁ : OracleProtocol eqOracle X Y Z) (x : X) (y : Y) :
    (eqQuery a b p₀ p₁).eval x y = cond (decide (a x = b y)) (p₁.eval x y) (p₀.eval x y) := by
  unfold eqQuery
  let _ : Fintype α := Fintype.ofFinite α
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have heq : eqOracle (Fintype.card α) (oneHotFin (e (a x))) (oneHotFin (e (b y))) =
      decide (a x = b y) := by
    simp only [eqOracle, equality, decide_eq_decide]
    exact oneHotFin_injective.eq_iff.trans e.injective.eq_iff
  change cond (eqOracle (Fintype.card α) (oneHotFin (e (a x))) (oneHotFin (e (b y))))
    (p₁.eval x y) (p₀.eval x y) = _
  rw [heq]

/-- `eqQuery` adds exactly `1` to the maximum subtree depth. -/
@[simp]
theorem depth_eqQuery {α : Type*} [Finite α] (a : X → α) (b : Y → α)
    (p₀ p₁ : OracleProtocol eqOracle X Y Z) :
    (eqQuery a b p₀ p₁).depth = max p₀.depth p₁.depth + 1 := by
  unfold eqQuery
  rfl

/-- Every standard deterministic protocol `p : Protocol X Y Z` can be simulated query-for-query by
an `Equality`-oracle protocol of identical depth. -/
def eqProtocolOfProtocol : Protocol X Y Z → OracleProtocol eqOracle X Y Z
  | .output z => .output z
  | .alice send p₀ p₁ =>
      .query 1 (fun x _ ↦ send x) (fun _ _ ↦ true)
        (eqProtocolOfProtocol p₀) (eqProtocolOfProtocol p₁)
  | .bob send p₀ p₁ =>
      .query 1 (fun _ _ ↦ true) (fun y _ ↦ send y)
        (eqProtocolOfProtocol p₀) (eqProtocolOfProtocol p₁)

@[simp]
theorem eval_eqProtocolOfProtocol (p : Protocol X Y Z) (x : X) (y : Y) :
    (eqProtocolOfProtocol p).eval x y = p.run x y := by
  induction p with
  | output _ => rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    simp only [eqProtocolOfProtocol, OracleProtocol.eval_query, eqOracle, ih₀, ih₁]
    cases hx : send x
    · have hf : equality (fun _ : Fin 1 ↦ false) (fun _ : Fin 1 ↦ true) = false := by
        simp [equality, funext_iff]
      simp [Protocol.run_alice, hx, hf]
    · have ht : equality (fun _ : Fin 1 ↦ true) (fun _ : Fin 1 ↦ true) = true := by
        simp [equality]
      simp [Protocol.run_alice, hx, ht]
  | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [eqProtocolOfProtocol, OracleProtocol.eval_query, eqOracle, ih₀, ih₁]
    cases hy : send y
    · have hf : equality (fun _ : Fin 1 ↦ true) (fun _ : Fin 1 ↦ false) = false := by
        simp [equality, funext_iff]
      simp [Protocol.run_bob, hy, hf]
    · have ht : equality (fun _ : Fin 1 ↦ true) (fun _ : Fin 1 ↦ true) = true := by
        simp [equality]
      simp [Protocol.run_bob, hy, ht]

@[simp]
theorem depth_eqProtocolOfProtocol (p : Protocol X Y Z) :
    (eqProtocolOfProtocol p).depth = p.depth := by
  induction p with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ => simp [eqProtocolOfProtocol, Protocol.depth_alice, ih₀, ih₁]
  | bob _ _ _ ih₀ ih₁ => simp [eqProtocolOfProtocol, Protocol.depth_bob, ih₀, ih₁]

/-- Deterministic `Equality`-oracle complexity `D^Eq(f)` in `ℕ∞`. -/
noncomputable def eqOracleEcomplexity (f : X → Y → Z) : ℕ∞ :=
  oracleEcomplexity eqOracle f

/-- Deterministic `k`-Hamming distance oracle complexity `D^{HD_k}(f)` in `ℕ∞`. -/
noncomputable def hammingOracleEcomplexity (k : ℕ) (f : X → Y → Z) : ℕ∞ :=
  oracleEcomplexity (hammingOracle k) f

/-- `D^Eq(f)` never exceeds ordinary deterministic communication complexity `D(f)`. -/
theorem eqOracleEcomplexity_le_protocol (f : X → Y → Z) :
    eqOracleEcomplexity f ≤ Protocol.ecomplexityFun f := by
  rw [Protocol.le_ecomplexityFun_iff]
  intro p hp
  have hev : (eqProtocolOfProtocol p).eval = f := by ext x y; simp [← hp]
  exact (oracleEcomplexity_le_depth hev).trans (by simp)

/-- Every `Equality` query can be simulated by a single `HD_k` query by repeating each bit `k + 1`
times, so `D^{HD_k}(f) ≤ D^Eq(f)`. -/
theorem hammingOracleEcomplexity_le_eqOracle (k : ℕ) (f : X → Y → Z) :
    hammingOracleEcomplexity k f ≤ eqOracleEcomplexity f := by
  unfold eqOracleEcomplexity
  rw [le_oracleEcomplexity_iff]
  intro p hp
  let sim : ∀ m : ℕ, (X → BitString m) → (Y → BitString m) →
      OracleProtocol (hammingOracle k) X Y Bool := fun m a b ↦
    OracleProtocol.query (m * (k + 1))
      (fun x idx ↦ a x ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩)
      (fun y idx ↦ b y ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩)
      (.output false) (.output true)
  have hsim : ∀ m a b x y, (sim m a b).eval x y = eqOracle m (a x) (b y) := by
    intro m a b x y
    simp only [sim, OracleProtocol.eval_query, hammingOracle, eqOracle, equality]
    by_cases heq : a x = b y
    · simp [heq]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp heq
      let emb : Fin (k + 1) ↪ Fin (m * (k + 1)) :=
        ⟨fun r ↦ ⟨i.1 * (k + 1) + r.1, by have := i.2; have := r.2; nlinarith⟩,
         fun r₁ r₂ hr ↦ Fin.ext (by simp only [Fin.mk.injEq] at hr; omega)⟩
      have hcard : k + 1 ≤ hammingDist
          (fun idx : Fin (m * (k + 1)) ↦
            a x ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩)
          (fun idx : Fin (m * (k + 1)) ↦
            b y ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩) := by
        rw [hammingDist]
        have hsub : Finset.univ.map emb ⊆ Finset.univ.filter (fun idx : Fin (m * (k + 1)) ↦
            a x ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩ ≠
              b y ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩) := by
          intro idx hidx
          simp only [Finset.mem_map, Finset.mem_univ, true_and] at hidx
          obtain ⟨r, rfl⟩ := hidx
          have hdiv : (i.1 * (k + 1) + r.1) / (k + 1) = i.1 := by
            rw [mul_comm i.1, Nat.mul_add_div (Nat.succ_pos k),
              Nat.div_eq_zero_iff.mpr (Or.inr r.2), add_zero]
          have hfin : (⟨(emb r).1 / (k + 1),
              Nat.div_lt_of_lt_mul (by linarith [(emb r).2])⟩ : Fin m) = i :=
            Fin.ext hdiv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfin]
          exact hi
        simpa using Finset.card_le_card hsub
      have hnot : ¬hammingDist
          (fun idx : Fin (m * (k + 1)) ↦
            a x ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩)
          (fun idx : Fin (m * (k + 1)) ↦
            b y ⟨idx.1 / (k + 1), Nat.div_lt_of_lt_mul (by linarith [idx.2])⟩) ≤ k := by omega
      simp [heq, hnot]
  have hev : (p.simulate sim).eval = f := by
    ext x y; rw [OracleProtocol.eval_simulate sim hsim, hp]
  have hd : (p.simulate sim).depth ≤ p.depth := by
    simpa using OracleProtocol.depth_simulate_le sim (c := 1) (fun _ _ _ ↦ by simp [sim]) p
  exact (oracleEcomplexity_le_depth hev).trans (by exact_mod_cast hd)

/-- When `X` is finite, every `f : X → Y → Bool` is computed by a finite-depth `Equality`-oracle
protocol. -/
theorem exists_eqProtocol_finite [Finite X] (f : X → Y → Bool) :
    ∃ p : OracleProtocol eqOracle X Y Bool, p.eval = f := by
  cases nonempty_fintype X
  classical
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let n := Fintype.card X
  let pBit : Protocol (BitString n) Y Bool :=
    Protocol.aliceSend n id (fun bs ↦
      Protocol.bob (fun y ↦
        if h : ∃ x : X, oneHotFin (e x) = bs then f h.choose y else false)
        (.output false) (.output true))
  let p : Protocol X Y Bool := pBit.comap (fun x ↦ oneHotFin (e x)) id
  refine ⟨eqProtocolOfProtocol p, ?_⟩
  ext x y
  have hex : ∃ x' : X, oneHotFin (e x') = oneHotFin (e x) := ⟨x, rfl⟩
  have hch : hex.choose = x := e.injective (oneHotFin_injective hex.choose_spec)
  simp only [eval_eqProtocolOfProtocol, p, Protocol.run_comap, id_eq, pBit,
    Protocol.run_aliceSend, Protocol.run_bob]
  rw [dite_eq_left_of_eq_true (eq_true hex), hch]
  cases f x y <;> rfl

/-- Natural-number deterministic `Equality`-oracle complexity `D^Eq(f)` (for finite `X`, equals
`eqOracleEcomplexity f` by `coe_eqOracleComplexity`). -/
noncomputable def eqOracleComplexity (f : X → Y → Bool) : ℕ :=
  sInf { d : ℕ | ∃ p : OracleProtocol eqOracle X Y Bool, p.eval = f ∧ p.depth ≤ d }

/-- Natural-number deterministic `k`-Hamming distance oracle complexity `D^{HD_k}(f)` (for finite
`X`, equals `hammingOracleEcomplexity k f` by `coe_hammingOracleComplexity`). -/
noncomputable def hammingOracleComplexity (k : ℕ) (f : X → Y → Bool) : ℕ :=
  sInf { d : ℕ | ∃ p : OracleProtocol (hammingOracle k) X Y Bool, p.eval = f ∧ p.depth ≤ d }

/-- Any `Equality`-oracle protocol computing `f` bounds `eqOracleComplexity f`. -/
theorem eqOracleComplexity_le_depth {f : X → Y → Bool}
    {p : OracleProtocol eqOracle X Y Bool} (hp : p.eval = f) :
    eqOracleComplexity f ≤ p.depth :=
  Nat.sInf_le ⟨p, hp, le_rfl⟩

/-- There exists an `Equality`-oracle protocol computing `f` of depth at most
`eqOracleComplexity f`. -/
theorem exists_eval_depth_le_eqOracleComplexity [Finite X] (f : X → Y → Bool) :
    ∃ p : OracleProtocol eqOracle X Y Bool, p.eval = f ∧ p.depth ≤ eqOracleComplexity f := by
  obtain ⟨p₀, hp₀⟩ := exists_eqProtocol_finite f
  have hne :
      { d : ℕ | ∃ p : OracleProtocol eqOracle X Y Bool, p.eval = f ∧ p.depth ≤ d }.Nonempty :=
    ⟨p₀.depth, p₀, hp₀, le_rfl⟩
  exact Nat.sInf_mem hne

/-- `eqOracleComplexity f ≤ d` iff `f` has an `Equality`-oracle protocol of depth at most `d`. -/
theorem eqOracleComplexity_le_iff [Finite X] {f : X → Y → Bool} {d : ℕ} :
    eqOracleComplexity f ≤ d ↔
      ∃ p : OracleProtocol eqOracle X Y Bool, p.eval = f ∧ p.depth ≤ d := by
  refine ⟨fun h ↦ ?_, fun ⟨p, hp, hd⟩ ↦ (eqOracleComplexity_le_depth hp).trans hd⟩
  obtain ⟨p, hp, hpd⟩ := exists_eval_depth_le_eqOracleComplexity f
  exact ⟨p, hp, hpd.trans h⟩

/-- `(eqOracleComplexity f : ℕ∞)` agrees with `eqOracleEcomplexity f`. -/
@[simp, norm_cast]
theorem coe_eqOracleComplexity [Finite X] (f : X → Y → Bool) :
    (eqOracleComplexity f : ℕ∞) = eqOracleEcomplexity f := by
  apply le_antisymm
  · unfold eqOracleEcomplexity
    rw [le_oracleEcomplexity_iff]
    intro p hp
    exact_mod_cast eqOracleComplexity_le_depth hp
  · obtain ⟨p, hp, hd⟩ := exists_eval_depth_le_eqOracleComplexity f
    exact (oracleEcomplexity_le_depth hp).trans (by exact_mod_cast hd)

/-- Pulling back inputs does not increase `eqOracleComplexity`. -/
theorem eqOracleComplexity_comap_le [Finite X] [Finite X'] (f : X → Y → Bool)
    (a : X' → X) (b : Y' → Y) :
    eqOracleComplexity (fun x y ↦ f (a x) (b y)) ≤ eqOracleComplexity f := by
  have h := oracleEcomplexity_comap_le eqOracle f a b
  change eqOracleEcomplexity _ ≤ eqOracleEcomplexity f at h
  rw [← coe_eqOracleComplexity, ← coe_eqOracleComplexity] at h
  exact_mod_cast h

private theorem eqOracleComplexity_swap_le [Finite X] (f : X → Y → Bool) :
    eqOracleComplexity (fun y x ↦ f x y) ≤ eqOracleComplexity f := by
  obtain ⟨p, hp, hd⟩ := exists_eval_depth_le_eqOracleComplexity f
  have hev : p.swap.eval = fun y x ↦ f x y := by
    ext y x
    rw [p.eval_swap (fun _ u v ↦ by simp [eqOracle, equality, eq_comm]), hp]
  exact (eqOracleComplexity_le_depth hev).trans (by simpa using hd)

/-- Swapping Alice and Bob preserves `eqOracleComplexity`. -/
theorem eqOracleComplexity_swap [Finite X] [Finite Y] (f : X → Y → Bool) :
    eqOracleComplexity (fun y x ↦ f x y) = eqOracleComplexity f :=
  le_antisymm (eqOracleComplexity_swap_le f) (eqOracleComplexity_swap_le fun y x ↦ f x y)

/-- Pointwise Boolean conjunction is subadditive under `eqOracleComplexity`. -/
theorem eqOracleComplexity_and_le [Finite X] (f g : X → Y → Bool) :
    eqOracleComplexity (fun x y ↦ f x y && g x y) ≤
      eqOracleComplexity f + eqOracleComplexity g := by
  obtain ⟨pf, hpf, hdf⟩ := exists_eval_depth_le_eqOracleComplexity f
  obtain ⟨pg, hpg, hdg⟩ := exists_eval_depth_le_eqOracleComplexity g
  let p := pf.bind (fun b ↦ if b then pg else .output false)
  have hev : p.eval = fun x y ↦ f x y && g x y := by
    ext x y
    simp only [p, OracleProtocol.eval_bind, hpf]
    cases f x y <;> simp [hpg]
  have hd : p.depth ≤ eqOracleComplexity f + eqOracleComplexity g :=
    OracleProtocol.depth_bind_le hdf (fun b ↦ by cases b <;> simp [hdg])
  exact (eqOracleComplexity_le_depth hev).trans hd

/-- Pointwise Boolean disjunction is subadditive under `eqOracleComplexity`. -/
theorem eqOracleComplexity_or_le [Finite X] (f g : X → Y → Bool) :
    eqOracleComplexity (fun x y ↦ f x y || g x y) ≤
      eqOracleComplexity f + eqOracleComplexity g := by
  obtain ⟨pf, hpf, hdf⟩ := exists_eval_depth_le_eqOracleComplexity f
  obtain ⟨pg, hpg, hdg⟩ := exists_eval_depth_le_eqOracleComplexity g
  let p := pf.bind (fun b ↦ if b then .output true else pg)
  have hev : p.eval = fun x y ↦ f x y || g x y := by
    ext x y
    simp only [p, OracleProtocol.eval_bind, hpf]
    cases f x y <;> simp [hpg]
  have hd : p.depth ≤ eqOracleComplexity f + eqOracleComplexity g :=
    OracleProtocol.depth_bind_le hdf (fun b ↦ by cases b <;> simp [hdg])
  exact (eqOracleComplexity_le_depth hev).trans hd

/-- For finite `X`, Alice can announce her input in `Nat.clog 2 (card X)` bits and Bob replies in
`1` bit, giving `eqOracleComplexity f ≤ Nat.clog 2 (card X) + 1`. -/
theorem eqOracleComplexity_le_clog_card_succ [Fintype X] (f : X → Y → Bool) :
    eqOracleComplexity f ≤ Nat.clog 2 (Fintype.card X) + 1 := by
  classical
  let b := Nat.clog 2 (Fintype.card X)
  have hpow : Fintype.card X ≤ 2 ^ b := Nat.le_pow_clog (by norm_num) _
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let enc : X → BitString b := fun x i ↦ (eX x).1.testBit i.1
  have henc_inj : Function.Injective enc := by
    intro x₁ x₂ h
    apply eX.injective
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < b
    · exact congr_fun h ⟨j, hj⟩
    · have h₁ : (eX x₁).1 < 2 ^ j :=
        ((eX x₁).2.trans_le hpow).trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj))
      have h₂ : (eX x₂).1 < 2 ^ j :=
        ((eX x₂).2.trans_le hpow).trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj))
      rw [Nat.testBit_lt_two_pow h₁, Nat.testBit_lt_two_pow h₂]
  let p : Protocol X Y Bool :=
    Protocol.aliceSend b enc (fun bs ↦
      Protocol.bob (fun y ↦ if h : ∃ x, enc x = bs then f h.choose y else false)
        (.output false) (.output true))
  have hp_run : p.run = f := by
    ext x y
    have hex : ∃ x', enc x' = enc x := ⟨x, rfl⟩
    have hch : hex.choose = x := henc_inj hex.choose_spec
    simp only [p, Protocol.run_aliceSend, Protocol.run_bob]
    rw [dite_eq_left_of_eq_true (eq_true hex), hch]
    cases f x y <;> rfl
  have hp_depth : p.depth ≤ b + 1 :=
    Protocol.depth_aliceSend_le (fun _ ↦ by simp [Protocol.depth_bob])
  have hev : (eqProtocolOfProtocol p).eval = f := by ext x y; simp [hp_run]
  exact (eqOracleComplexity_le_depth hev).trans (by simpa using hp_depth)

/-- There exists an `HD_k`-oracle protocol computing `f` of depth at most
`hammingOracleComplexity k f`. -/
theorem exists_eval_depth_le_hammingOracleComplexity [Finite X] (k : ℕ) (f : X → Y → Bool) :
    ∃ p : OracleProtocol (hammingOracle k) X Y Bool,
      p.eval = f ∧ p.depth ≤ hammingOracleComplexity k f := by
  have hle : hammingOracleEcomplexity k f ≤ eqOracleComplexity f :=
    (hammingOracleEcomplexity_le_eqOracle k f).trans_eq (coe_eqOracleComplexity f).symm
  obtain ⟨p₀, hp₀, _⟩ := oracleEcomplexity_le_iff.mp hle
  have hne :
      { d : ℕ | ∃ p : OracleProtocol (hammingOracle k) X Y Bool, p.eval = f ∧ p.depth ≤ d
        }.Nonempty := ⟨p₀.depth, p₀, hp₀, le_rfl⟩
  exact Nat.sInf_mem hne

/-- Any `HD_k`-oracle protocol computing `f` bounds `hammingOracleComplexity k f`. -/
theorem hammingOracleComplexity_le_depth {k : ℕ} {f : X → Y → Bool}
    {p : OracleProtocol (hammingOracle k) X Y Bool} (hp : p.eval = f) :
    hammingOracleComplexity k f ≤ p.depth :=
  Nat.sInf_le ⟨p, hp, le_rfl⟩

/-- `(hammingOracleComplexity k f : ℕ∞)` agrees with `hammingOracleEcomplexity k f`. -/
@[simp, norm_cast]
theorem coe_hammingOracleComplexity [Finite X] (k : ℕ) (f : X → Y → Bool) :
    (hammingOracleComplexity k f : ℕ∞) = hammingOracleEcomplexity k f := by
  apply le_antisymm
  · unfold hammingOracleEcomplexity
    rw [le_oracleEcomplexity_iff]
    intro p hp
    exact_mod_cast hammingOracleComplexity_le_depth hp
  · obtain ⟨p, hp, hd⟩ := exists_eval_depth_le_hammingOracleComplexity k f
    exact (oracleEcomplexity_le_depth hp).trans (by exact_mod_cast hd)

/-- Pulling back inputs does not increase `hammingOracleComplexity k`. -/
theorem hammingOracleComplexity_comap_le [Finite X] [Finite X'] (k : ℕ) (f : X → Y → Bool)
    (a : X' → X) (b : Y' → Y) :
    hammingOracleComplexity k (fun x y ↦ f (a x) (b y)) ≤ hammingOracleComplexity k f := by
  have h := oracleEcomplexity_comap_le (hammingOracle k) f a b
  change hammingOracleEcomplexity k _ ≤ hammingOracleEcomplexity k f at h
  rw [← coe_hammingOracleComplexity, ← coe_hammingOracleComplexity] at h
  exact_mod_cast h

/-- Oracle simulation bound connecting `D^Eq` and `D^{HD_k}` on finite domains:
if every `HD_k` query on `X × Y` has `D^Eq ≤ c`, then `D^Eq(f) ≤ D^{HD_k}(f) * c`. -/
theorem eqOracleComplexity_le_hammingOracleComplexity_mul [Finite X] (k : ℕ) (f : X → Y → Bool)
    {c : ℕ} (hsim : ∀ (m : ℕ) (a : X → BitString m) (b : Y → BitString m),
      eqOracleComplexity (fun x y ↦ decide (hammingDist (a x) (b y) ≤ k)) ≤ c) :
    eqOracleComplexity f ≤ hammingOracleComplexity k f * c := by
  obtain ⟨p, hp, hpd⟩ := exists_eval_depth_le_hammingOracleComplexity k f
  have hex : ∀ (m : ℕ) (a : X → BitString m) (b : Y → BitString m),
      ∃ q : OracleProtocol eqOracle X Y Bool,
        q.eval = (fun x y ↦ hammingOracle k m (a x) (b y)) ∧ q.depth ≤ c :=
    fun m a b ↦ eqOracleComplexity_le_iff.mp (hsim m a b)
  choose sim hsim_eval hsim_depth using hex
  have hev : (p.simulate sim).eval = f := by
    ext x y
    rw [OracleProtocol.eval_simulate sim (fun j a b x y ↦ congr_fun₂ (hsim_eval j a b) x y), hp]
  have hd : (p.simulate sim).depth ≤ hammingOracleComplexity k f * c :=
    (OracleProtocol.depth_simulate_le sim hsim_depth p).trans (Nat.mul_le_mul_right c hpd)
  exact (eqOracleComplexity_le_depth hev).trans hd

/-- `HasNdEqCover f m d` holds when `f` is the pointwise OR of `2 ^ m` Boolean functions each
computed by a deterministic `Equality`-oracle protocol of depth at most `d`. -/
def HasNdEqCover (f : X → Y → Bool) (m d : ℕ) : Prop :=
  ∃ p : Fin (2 ^ m) → OracleProtocol eqOracle X Y Bool,
    (∀ i, (p i).depth ≤ d) ∧
    (∀ x y, f x y = true ↔ ∃ i, (p i).eval x y = true)

/-- Characterization of `HasNdEqCover f m d` as a `2 ^ m`-fold disjunction of Boolean functions
with deterministic `Equality`-oracle complexity at most `d`. -/
theorem hasNdEqCover_iff [Finite X] {f : X → Y → Bool} {m d : ℕ} :
    HasNdEqCover f m d ↔
      ∃ M : Fin (2 ^ m) → X → Y → Bool,
        (∀ i, eqOracleComplexity (M i) ≤ d) ∧
        (∀ x y, f x y = true ↔ ∃ i, M i x y = true) := by
  constructor
  · rintro ⟨p, hd, hcov⟩
    exact ⟨fun i ↦ (p i).eval, fun i ↦ (eqOracleComplexity_le_depth rfl).trans (hd i), hcov⟩
  · rintro ⟨M, hd, hcov⟩
    choose p hp_eval hp_depth using fun i ↦ eqOracleComplexity_le_iff.mp (hd i)
    refine ⟨p, hp_depth, fun x y ↦ (hcov x y).trans ?_⟩
    exact exists_congr fun i ↦ by rw [hp_eval i]

/-- Nondeterministic `Equality`-oracle complexity `ND^Eq(f)`: the minimum of `m + d` over all
`(m, d)` with `HasNdEqCover f m d`. -/
noncomputable def ndEqOracleComplexity (f : X → Y → Bool) : ℕ :=
  sInf { t : ℕ | ∃ m d : ℕ, m + d = t ∧ HasNdEqCover f m d }

/-- Any `(m, d)` cover witnesses `ndEqOracleComplexity f ≤ m + d`. -/
theorem ndEqOracleComplexity_le {f : X → Y → Bool} {m d : ℕ}
    (h : HasNdEqCover f m d) : ndEqOracleComplexity f ≤ m + d :=
  Nat.sInf_le ⟨m, d, rfl, h⟩

/-- Deterministic `Equality`-oracle protocols are `(0, D^Eq(f))` nondeterministic covers, so
`ND^Eq(f) ≤ D^Eq(f)`. -/
theorem ndEqOracleComplexity_le_eqOracleComplexity [Finite X] (f : X → Y → Bool) :
    ndEqOracleComplexity f ≤ eqOracleComplexity f := by
  simpa using ndEqOracleComplexity_le (m := 0) (d := eqOracleComplexity f)
    (hasNdEqCover_iff.mpr
      ⟨fun _ ↦ f, fun _ ↦ le_rfl, fun _ _ ↦ ⟨fun h ↦ ⟨0, h⟩, fun ⟨_, h⟩ ↦ h⟩⟩)

/-- There exists an optimal cover `(m, d)` with `m + d = ndEqOracleComplexity f`. -/
theorem exists_hasNdEqCover_eq [Finite X] (f : X → Y → Bool) :
    ∃ m d : ℕ, m + d = ndEqOracleComplexity f ∧ HasNdEqCover f m d := by
  have hne : { t : ℕ | ∃ m d : ℕ, m + d = t ∧ HasNdEqCover f m d }.Nonempty :=
    ⟨eqOracleComplexity f, 0, eqOracleComplexity f, zero_add _,
      hasNdEqCover_iff.mpr
        ⟨fun _ ↦ f, fun _ ↦ le_rfl, fun _ _ ↦ ⟨fun h ↦ ⟨0, h⟩, fun ⟨_, h⟩ ↦ h⟩⟩⟩
  exact Nat.sInf_mem hne

/-- Pulling back inputs does not increase `ndEqOracleComplexity`. -/
theorem ndEqOracleComplexity_comap_le [Finite X] (f : X → Y → Bool)
    (a : X' → X) (b : Y' → Y) :
    ndEqOracleComplexity (fun x y ↦ f (a x) (b y)) ≤ ndEqOracleComplexity f := by
  obtain ⟨m, d, hmd, p, hpd, hcov⟩ := exists_hasNdEqCover_eq f
  rw [← hmd]
  exact ndEqOracleComplexity_le ⟨fun i ↦ (p i).comap a b,
    fun i ↦ by simpa using hpd i, fun x y ↦ by simpa using hcov (a x) (b y)⟩

-- Non-vacuity check: `equality` on `BitString 4` has `D^Eq = 1`.
example : eqOracleComplexity (equality : BitString 4 → BitString 4 → Bool) = 1 := by
  apply le_antisymm
  · let p : OracleProtocol eqOracle (BitString 4) (BitString 4) Bool :=
      .query 4 id id (.output false) (.output true)
    have hev : p.eval = equality := by
      ext x y
      simp only [p, OracleProtocol.eval_query, eqOracle, id_eq]
      cases equality x y <;> simp
    exact (eqOracleComplexity_le_depth hev).trans (by simp [p])
  · by_contra hlt
    have h0 : eqOracleComplexity (equality : BitString 4 → BitString 4 → Bool) ≤ 0 := by omega
    obtain ⟨p, hp, hd⟩ := eqOracleComplexity_le_iff.mp h0
    cases p with
    | query _ _ _ _ _ => simp at hd
    | output b =>
      have h1 := congr_fun₂ hp (fun _ ↦ false) (fun _ ↦ false)
      have h2 := congr_fun₂ hp (fun _ ↦ false) (fun _ ↦ true)
      simp only [OracleProtocol.eval_output, equality, decide_true] at h1 h2
      have hne : (fun _ : Fin 4 ↦ false) ≠ (fun _ : Fin 4 ↦ true) := by
        intro h; have := congr_fun h 0; cases this
      simp [hne, h1] at h2

end EqualityAndHammingOracles

end CslibFrontier.Communication
