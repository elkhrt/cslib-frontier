/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.PMF
public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.Communication.Randomized
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Log

import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-Party Pointer Chasing and Bounded-Round Alternating Protocols

Defines the $K$-step two-party pointer chasing problem (`pointerChase`, `pointerChasing`) and
deterministic / public-coin bounded-round alternating communication protocols
(`BoundedRoundProtocol`, `PublicCoinRoundProtocol`) with explicit bit-length budgets and bridges to
`Cslib.Communication.Protocol` and `Cslib.Communication.PublicCoin`.

Under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), proves:
* `one_le_totalBits_of_solves_pointerChasing`: any $1/3$-error randomized protocol for
  $\mathrm{PC}_K$ ($N \ge 2, K \ge 1$) sends at least $1$ bit;
* `pointerChasing_det_twoRound_bobFirst_lower_bound`: every deterministic $2$-round Bob-first
  protocol solving $\mathrm{PC}_2$ sends at least $N$ bits;
* `pointerChasing_aliceFirst_upper_bound`: $K$-round Alice-first deterministic upper bound of
  $(K - 1) \lceil \log_2 N \rceil + 1$ bits;
* `pointerChasing_one_vertex_trivial`, `pointerChasing_two_vertex_upper_bound`,
  `pointerChasing_half_error_zero_bits`: exact sharpness witnesses in $N$, $+K$, and error $1/2$.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib
open Cslib.Communication
open Cslib.Probability

/-! ### Pointer chasing problem -/

/-- The $K$-step alternating pointer walk on `Fin N` starting at `0 : Fin N`, applying `fA` at
odd 1-indexed steps ($r = 1, 3, \dots$) and `fB` at even 1-indexed steps ($r = 2, 4, \dots$). -/
def pointerChase {N : ℕ} [NeZero N] : ℕ → (Fin N → Fin N) → (Fin N → Fin N) → Fin N
  | 0, _, _ => 0
  | r + 1, fA, fB =>
    if r % 2 = 0 then fA (pointerChase r fA fB) else fB (pointerChase r fA fB)

@[simp] theorem pointerChase_zero {N : ℕ} [NeZero N] (fA fB : Fin N → Fin N) :
    pointerChase 0 fA fB = 0 := by
  rfl

@[simp] theorem pointerChase_succ_even {N : ℕ} [NeZero N] {r : ℕ} (hr : r % 2 = 0)
    (fA fB : Fin N → Fin N) :
    pointerChase (r + 1) fA fB = fA (pointerChase r fA fB) := by
  simp [pointerChase, hr]

@[simp] theorem pointerChase_succ_odd {N : ℕ} [NeZero N] {r : ℕ} (hr : r % 2 = 1)
    (fA fB : Fin N → Fin N) :
    pointerChase (r + 1) fA fB = fB (pointerChase r fA fB) := by
  simp [pointerChase, hr]

/-- The Boolean $K$-step pointer chasing function $\mathrm{PC}_K(f_A, f_B)$, outputting the parity
of the 1-indexed endpoint `pointerChase K fA fB + 1` (equivalently `val % 2 = 0` on `Fin N`). -/
def pointerChasing {N : ℕ} [NeZero N] (K : ℕ) (fA fB : Fin N → Fin N) : Bool :=
  decide ((pointerChase K fA fB).val % 2 = 0)

/-- Characterization of `pointerChasing` as the parity of `pointerChase`. -/
theorem pointerChasing_eq {N : ℕ} [NeZero N] (K : ℕ) (fA fB : Fin N → Fin N) :
    pointerChasing K fA fB = decide ((pointerChase K fA fB).val % 2 = 0) := by
  rfl

/-- Walking with constant `fA` and identity `fB` reaches `a` in any `K ≥ 1` steps. -/
theorem pointerChase_const_id {N : ℕ} [NeZero N] (a : Fin N) (K : ℕ) (hK : 1 ≤ K) :
    pointerChase K (fun _ => a) id = a := by
  induction K with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => simp [pointerChase]
    | succ s =>
      have hs : 1 ≤ s + 1 := by omega
      have hprev := ih hs
      by_cases hpar : (s + 1) % 2 = 0
      · rw [pointerChase_succ_even hpar]
      · have hodd : (s + 1) % 2 = 1 := by omega
        rw [pointerChase_succ_odd hodd, hprev]
        rfl

/-- For `N ≥ 2` and `K ≥ 1`, `pointerChasing K` is non-constant. -/
theorem pointerChasing_nonconstant {N : ℕ} (hN : 2 ≤ N) {K : ℕ} (hK : 1 ≤ K) :
    have : NeZero N := ⟨by omega⟩
    ∃ fA₀ fA₁ fB : Fin N → Fin N,
      pointerChasing K fA₀ fB = true ∧ pointerChasing K fA₁ fB = false := by
  have : NeZero N := ⟨by omega⟩
  refine ⟨fun _ => ⟨0, by omega⟩, fun _ => ⟨1, by omega⟩, id, ?_, ?_⟩
  · simp [pointerChasing, pointerChase_const_id _ K hK]
  · simp [pointerChasing, pointerChase_const_id _ K hK]

/-! ### Bounded-round alternating two-party protocols -/

/-- A deterministic alternating two-party communication protocol with at most `r` messages, starting
with Alice if `turn = true` and Bob if `turn = false`. Each internal node transmits a fixed-length
`BitString c` computed from the speaker's input; leaves produce an output determined by the
transcript. -/
inductive BoundedRoundProtocol (X Y Z : Type*) : Bool → ℕ → Type _
  /-- Output `z : Z` determined by the transcript so far. -/
  | output {turn : Bool} {r : ℕ} (z : Z) : BoundedRoundProtocol X Y Z turn r
  /-- Alice sends a `c`-bit message and transfers the turn to Bob. -/
  | alice {r : ℕ} (c : ℕ) (send : X → BitString c)
      (next : BitString c → BoundedRoundProtocol X Y Z false r) :
      BoundedRoundProtocol X Y Z true (r + 1)
  /-- Bob sends a `c`-bit message and transfers the turn to Alice. -/
  | bob {r : ℕ} (c : ℕ) (send : Y → BitString c)
      (next : BitString c → BoundedRoundProtocol X Y Z true r) :
      BoundedRoundProtocol X Y Z false (r + 1)

namespace BoundedRoundProtocol

variable {X Y Z : Type*}

/-- Evaluate a bounded-round protocol on inputs `x : X` and `y : Y`. -/
def run {turn : Bool} {r : ℕ} : BoundedRoundProtocol X Y Z turn r → X → Y → Z
  | .output z, _, _ => z
  | .alice _ send next, x, y => (next (send x)).run x y
  | .bob _ send next, x, y => (next (send y)).run x y

@[simp] theorem run_output {turn : Bool} {r : ℕ} (z : Z) (x : X) (y : Y) :
    (output z : BoundedRoundProtocol X Y Z turn r).run x y = z := by
  rfl

@[simp] theorem run_alice {r : ℕ} (c : ℕ) (send : X → BitString c)
    (next : BitString c → BoundedRoundProtocol X Y Z false r) (x : X) (y : Y) :
    (alice c send next).run x y = (next (send x)).run x y := by
  rfl

@[simp] theorem run_bob {r : ℕ} (c : ℕ) (send : Y → BitString c)
    (next : BitString c → BoundedRoundProtocol X Y Z true r) (x : X) (y : Y) :
    (bob c send next).run x y = (next (send y)).run x y := by
  rfl

/-- Worst-case total number of bits transmitted along any branch of the protocol. -/
def totalBits {turn : Bool} {r : ℕ} : BoundedRoundProtocol X Y Z turn r → ℕ
  | .output _ => 0
  | .alice c _ next => c + Finset.univ.sup (fun m => (next m).totalBits)
  | .bob c _ next => c + Finset.univ.sup (fun m => (next m).totalBits)

@[simp] theorem totalBits_output {turn : Bool} {r : ℕ} (z : Z) :
    (output z : BoundedRoundProtocol X Y Z turn r).totalBits = 0 := by
  rfl

@[simp] theorem totalBits_alice {r : ℕ} (c : ℕ) (send : X → BitString c)
    (next : BitString c → BoundedRoundProtocol X Y Z false r) :
    (alice c send next).totalBits = c + Finset.univ.sup (fun m => (next m).totalBits) := by
  rfl

@[simp] theorem totalBits_bob {r : ℕ} (c : ℕ) (send : Y → BitString c)
    (next : BitString c → BoundedRoundProtocol X Y Z true r) :
    (bob c send next).totalBits = c + Finset.univ.sup (fun m => (next m).totalBits) := by
  rfl

/-- Compile a bounded-round protocol into a `Cslib.Communication.Protocol` bit tree. -/
def toProtocol {turn : Bool} {r : ℕ} :
    BoundedRoundProtocol X Y Z turn r → Protocol X Y Z
  | .output z => .output z
  | .alice c send next => Protocol.aliceSend c send (fun m => (next m).toProtocol)
  | .bob c send next => Protocol.bobSend c send (fun m => (next m).toProtocol)

@[simp] theorem run_toProtocol {turn : Bool} {r : ℕ}
    (P : BoundedRoundProtocol X Y Z turn r) (x : X) (y : Y) :
    P.toProtocol.run x y = P.run x y := by
  induction P with
  | output z => rfl
  | alice c send next ih =>
    simp [toProtocol, ih]
  | bob c send next ih =>
    simp [toProtocol, ih]

/-- Compiling to `Cslib.Communication.Protocol` respects `totalBits`. -/
theorem depth_toProtocol_le {turn : Bool} {r : ℕ}
    (P : BoundedRoundProtocol X Y Z turn r) :
    P.toProtocol.depth ≤ P.totalBits := by
  induction P with
  | output z => simp [toProtocol]
  | alice c send next ih =>
    simp only [toProtocol, totalBits_alice]
    refine Protocol.depth_aliceSend_le fun m => ?_
    exact (ih m).trans (Finset.le_sup (f := fun m => (next m).totalBits) (Finset.mem_univ m))
  | bob c send next ih =>
    simp only [toProtocol, totalBits_bob]
    refine Protocol.depth_bobSend_le fun m => ?_
    exact (ih m).trans (Finset.le_sup (f := fun m => (next m).totalBits) (Finset.mem_univ m))

/-- Pad a bounded-round protocol to a larger round budget without changing its output or bit
complexity. -/
def weakenRounds {turn : Bool} :
    {r r' : ℕ} → r ≤ r' → BoundedRoundProtocol X Y Z turn r → BoundedRoundProtocol X Y Z turn r'
  | _, _, _, .output z => .output z
  | _ + 1, 0, h, .alice _ _ _ => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, h, .alice c send next =>
    .alice c send fun m => (next m).weakenRounds (Nat.le_of_succ_le_succ h)
  | _ + 1, 0, h, .bob _ _ _ => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, h, .bob c send next =>
    .bob c send fun m => (next m).weakenRounds (Nat.le_of_succ_le_succ h)

@[simp] theorem run_weakenRounds {turn : Bool} {r r' : ℕ} (h : r ≤ r')
    (P : BoundedRoundProtocol X Y Z turn r) (x : X) (y : Y) :
    (P.weakenRounds h).run x y = P.run x y := by
  induction P generalizing r' with
  | output z => simp [weakenRounds]
  | alice c send next ih =>
    cases r' with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ r'' => exact ih (send x) (Nat.le_of_succ_le_succ h)
  | bob c send next ih =>
    cases r' with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ r'' => exact ih (send y) (Nat.le_of_succ_le_succ h)

@[simp] theorem totalBits_weakenRounds {turn : Bool} {r r' : ℕ} (h : r ≤ r')
    (P : BoundedRoundProtocol X Y Z turn r) :
    (P.weakenRounds h).totalBits = P.totalBits := by
  induction P generalizing r' with
  | output z => simp [weakenRounds]
  | alice c send next ih =>
    cases r' with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ r'' =>
      simp only [weakenRounds, totalBits_alice]
      congr 1
      refine Finset.sup_congr rfl fun m _ => ih m (Nat.le_of_succ_le_succ h)
  | bob c send next ih =>
    cases r' with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ r'' =>
      simp only [weakenRounds, totalBits_bob]
      congr 1
      refine Finset.sup_congr rfl fun m _ => ih m (Nat.le_of_succ_le_succ h)

/-- Prepend a 0-bit dummy Bob message to convert an Alice-first `r`-round protocol into a
Bob-first `(r + 1)`-round protocol with identical output and bit complexity. -/
def prependEmptyBob {r : ℕ} (P : BoundedRoundProtocol X Y Z true r) :
    BoundedRoundProtocol X Y Z false (r + 1) :=
  .bob 0 (fun _ => Fin.elim0) (fun _ => P)

@[simp] theorem run_prependEmptyBob {r : ℕ} (P : BoundedRoundProtocol X Y Z true r)
    (x : X) (y : Y) :
    P.prependEmptyBob.run x y = P.run x y := by
  rfl

@[simp] theorem totalBits_prependEmptyBob {r : ℕ} (P : BoundedRoundProtocol X Y Z true r) :
    P.prependEmptyBob.totalBits = P.totalBits := by
  simp [prependEmptyBob]

/-- A `1`-round Alice-first protocol ignores Bob's input. -/
theorem run_eq_of_one_alice (P : BoundedRoundProtocol X Y Z true 1) (x : X) (y₁ y₂ : Y) :
    P.run x y₁ = P.run x y₂ := by
  cases P with
  | output z => rfl
  | alice _ send next =>
    simp only [run_alice]
    cases next (send x) with
    | output z => rfl

/-- A 0-bit deterministic protocol produces a constant output independent of both inputs. -/
theorem run_eq_of_totalBits_eq_zero {turn : Bool} {r : ℕ}
    (P : BoundedRoundProtocol X Y Z turn r) (hP : P.totalBits = 0)
    (x x' : X) (y y' : Y) :
    P.run x y = P.run x' y' := by
  induction P with
  | output z => rfl
  | alice c send next ih =>
    simp only [totalBits_alice, Nat.add_eq_zero_iff] at hP
    obtain ⟨rfl, hsup⟩ := hP
    have h0 : (next (send x)).totalBits = 0 :=
      Nat.eq_zero_of_le_zero
        ((Finset.le_sup (f := fun m => (next m).totalBits) (Finset.mem_univ _)).trans_eq hsup)
    have hsend : send x = send x' := Subsingleton.elim _ _
    simp only [run_alice, hsend]
    exact ih (send x') (by rw [← hsend]; exact h0)
  | bob c send next ih =>
    simp only [totalBits_bob, Nat.add_eq_zero_iff] at hP
    obtain ⟨rfl, hsup⟩ := hP
    have h0 : (next (send y)).totalBits = 0 :=
      Nat.eq_zero_of_le_zero
        ((Finset.le_sup (f := fun m => (next m).totalBits) (Finset.mem_univ _)).trans_eq hsup)
    have hsend : send y = send y' := Subsingleton.elim _ _
    simp only [run_bob, hsend]
    exact ih (send y') (by rw [← hsend]; exact h0)

end BoundedRoundProtocol

/-! ### Public-coin randomized bounded-round protocols -/

/-- A public-coin randomized bounded-round protocol: a distribution over deterministic
`BoundedRoundProtocol`s with round budget `r` and starting speaker `turn`. -/
abbrev PublicCoinRoundProtocol (X Y Z : Type*) (turn : Bool) (r : ℕ) : Type _ :=
  PMF (BoundedRoundProtocol X Y Z turn r)

namespace PublicCoinRoundProtocol

variable {X Y Z : Type*} {turn : Bool} {r : ℕ}

/-- The probability that a protocol drawn from `μ` fails to satisfy `R x y` on `(x, y)`. -/
@[expose] noncomputable def errorProb (μ : PublicCoinRoundProtocol X Y Z turn r)
    (R : X → Y → Z → Prop) (x : X) (y : Y) : ℝ :=
  (μ.toOuterMeasure {P | ¬R x y (P.run x y)}).toReal

/-- `μ` solves relation `R` on `A × B` with error at most `ε`. -/
@[expose] def Solves (μ : PublicCoinRoundProtocol X Y Z turn r) (ε : ℝ)
    (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, μ.errorProb R x y ≤ ε

/-- `μ` computes function `f` with error at most `ε` on all inputs. -/
@[expose] def SolvesFun (μ : PublicCoinRoundProtocol X Y Z turn r) (ε : ℝ) (f : X → Y → Z) :
    Prop :=
  μ.Solves ε (fun x y z => f x y = z) Set.univ Set.univ

/-- Every deterministic protocol in the support of `μ` transmits at most `C` bits. -/
@[expose] def BitsLE (μ : PublicCoinRoundProtocol X Y Z turn r) (C : ℕ) : Prop :=
  ∀ P ∈ μ.support, P.totalBits ≤ C

/-- Compile a public-coin bounded-round protocol to a `Cslib.Communication.PublicCoin` protocol. -/
noncomputable def toPublicCoin (μ : PublicCoinRoundProtocol X Y Z turn r) :
    PublicCoin X Y Z :=
  μ.map BoundedRoundProtocol.toProtocol

@[simp] theorem errorProb_toPublicCoin (μ : PublicCoinRoundProtocol X Y Z turn r)
    (R : X → Y → Z → Prop) (x : X) (y : Y) :
    μ.toPublicCoin.errorProb R x y = μ.errorProb R x y := by
  simp [PublicCoin.errorProb, toPublicCoin, errorProb, PMF.errorProb]

/-- Pushing forward a distribution through a map `g` pulls back `errorProb` by preimage. -/
theorem errorProb_map_eq {α : Type*} (ν : PMF α)
    (g : α → BoundedRoundProtocol X Y Z turn r)
    (R : X → Y → Z → Prop) (x : X) (y : Y) :
    errorProb (ν.map g) R x y =
      (ν.toOuterMeasure (g ⁻¹' {P | ¬R x y (P.run x y)})).toReal := by
  simp [errorProb, PMF.toOuterMeasure_map_apply]

/-- Compiling to `Cslib.Communication.PublicCoin` preserves the bit budget. -/
theorem depth_toPublicCoin_le {μ : PublicCoinRoundProtocol X Y Z turn r} {C : ℕ}
    (hμ : μ.BitsLE C) :
    μ.toPublicCoin.depth ≤ C := by
  rw [PublicCoin.depth_le_iff]
  intro p hp
  obtain ⟨P, hP, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
  exact_mod_cast (P.depth_toProtocol_le).trans (hμ P hP)

/-- Compiling to `Cslib.Communication.PublicCoin` preserves `Solves`. -/
theorem Solves.toPublicCoin {μ : PublicCoinRoundProtocol X Y Z turn r} {ε : ℝ}
    {R : X → Y → Z → Prop} {A : Set X} {B : Set Y}
    (h : μ.Solves ε R A B) :
    μ.toPublicCoin.Solves ε R A B :=
  fun x hx y hy => (errorProb_toPublicCoin μ R x y).trans_le (h x hx y hy)

/-- Padding rounds preserves both error guarantees and bit budgets. -/
noncomputable def weakenRounds {r' : ℕ} (h : r ≤ r')
    (μ : PublicCoinRoundProtocol X Y Z turn r) :
    PublicCoinRoundProtocol X Y Z turn r' :=
  μ.map (BoundedRoundProtocol.weakenRounds h)

@[simp] theorem errorProb_weakenRounds {r' : ℕ} (h : r ≤ r')
    (μ : PublicCoinRoundProtocol X Y Z turn r) (R : X → Y → Z → Prop) (x : X) (y : Y) :
    (μ.weakenRounds h).errorProb R x y = μ.errorProb R x y := by
  simp [errorProb, weakenRounds]

/-- Round padding preserves `SolvesFun`. -/
theorem SolvesFun.weakenRounds {r' : ℕ} (h : r ≤ r')
    {μ : PublicCoinRoundProtocol X Y Z turn r} {ε : ℝ} {f : X → Y → Z}
    (hμ : μ.SolvesFun ε f) :
    (μ.weakenRounds h).SolvesFun ε f :=
  fun x hx y hy => (errorProb_weakenRounds h μ _ x y).trans_le (hμ x hx y hy)

/-- Round padding preserves `BitsLE`. -/
theorem BitsLE.weakenRounds {r' : ℕ} (h : r ≤ r')
    {μ : PublicCoinRoundProtocol X Y Z turn r} {C : ℕ} (hμ : μ.BitsLE C) :
    (μ.weakenRounds h).BitsLE C := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hP
  simpa using hμ Q hQ

/-- Prepend a 0-bit dummy Bob message to a public-coin Alice-first protocol. -/
noncomputable def prependEmptyBob (μ : PublicCoinRoundProtocol X Y Z true r) :
    PublicCoinRoundProtocol X Y Z false (r + 1) :=
  μ.map BoundedRoundProtocol.prependEmptyBob

@[simp] theorem errorProb_prependEmptyBob (μ : PublicCoinRoundProtocol X Y Z true r)
    (R : X → Y → Z → Prop) (x : X) (y : Y) :
    μ.prependEmptyBob.errorProb R x y = μ.errorProb R x y := by
  simp [errorProb, prependEmptyBob]

/-- Prepending an empty Bob message preserves `SolvesFun`. -/
theorem SolvesFun.prependEmptyBob {μ : PublicCoinRoundProtocol X Y Z true r}
    {ε : ℝ} {f : X → Y → Z} (hμ : μ.SolvesFun ε f) :
    μ.prependEmptyBob.SolvesFun ε f :=
  fun x hx y hy => (errorProb_prependEmptyBob μ _ x y).trans_le (hμ x hx y hy)

/-- Prepending an empty Bob message preserves `BitsLE`. -/
theorem BitsLE.prependEmptyBob {μ : PublicCoinRoundProtocol X Y Z true r} {C : ℕ}
    (hμ : μ.BitsLE C) :
    μ.prependEmptyBob.BitsLE C := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hP
  simpa using hμ Q hQ

/-- A deterministic protocol solving `f` yields a 0-error public-coin protocol with the same
bit budget. -/
theorem solvesFun_pure {f : X → Y → Z} {P : BoundedRoundProtocol X Y Z turn r}
    (hP : ∀ x y, P.run x y = f x y) :
    SolvesFun (PMF.pure P) 0 f := by
  classical
  intro x _ y _
  simp [errorProb, PMF.toOuterMeasure_pure_apply, hP x y]

/-- A pure distribution satisfies `BitsLE C` whenever its protocol transmits at most `C` bits. -/
theorem bitsLE_pure {P : BoundedRoundProtocol X Y Z turn r} {C : ℕ} (hP : P.totalBits ≤ C) :
    BitsLE (PMF.pure P) C := by
  intro Q hQ
  exact (PMF.mem_support_pure_iff _ _).1 hQ ▸ hP

end PublicCoinRoundProtocol

/-! ### Unconditional lower bounds and sharpness witnesses under standard Lean axioms -/

/-- Any public-coin protocol computing a non-constant Boolean function with error strictly below
`1 / 2` must transmit at least `1` bit. -/
theorem one_le_bits_of_solvesFun_nonconstant {X Y : Type*} {turn : Bool} {r C : ℕ}
    {f : X → Y → Bool} {μ : PublicCoinRoundProtocol X Y Bool turn r} {ε : ℝ}
    (hε : ε < 1 / 2)
    (hnonconst : ∃ x₀ x₁ y₀ y₁, f x₀ y₀ = true ∧ f x₁ y₁ = false)
    (hsol : μ.SolvesFun ε f) (hbits : μ.BitsLE C) :
    1 ≤ C := by
  by_contra hC
  have hC0 : C = 0 := by omega
  subst hC0
  obtain ⟨x₀, x₁, y₀, y₁, h0, h1⟩ := hnonconst
  have hEq : ∀ P ∈ μ.support, P.run x₀ y₀ = P.run x₁ y₁ := fun P hP =>
    P.run_eq_of_totalBits_eq_zero (Nat.eq_zero_of_le_zero (hbits P hP)) x₀ x₁ y₀ y₁
  have hmeas0 : μ.toOuterMeasure {P | ¬(f x₀ y₀ = P.run x₀ y₀)} =
      μ.toOuterMeasure {P | P.run x₀ y₀ = false} := by
    refine congrArg μ.toOuterMeasure ?_
    ext P; simp [h0]
  have hmeas1 : μ.toOuterMeasure {P | ¬(f x₁ y₁ = P.run x₁ y₁)} =
      μ.toOuterMeasure {P | P.run x₀ y₀ = true} := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun P => ?_
    by_cases hmem : P ∈ μ.support
    · have he := hEq P hmem
      cases hr : P.run x₀ y₀ <;> simp [h1, ← he, hr]
    · have hzero : μ P = 0 := not_not.1 ((PMF.mem_support_iff _ _).not.1 hmem)
      simp [Set.indicator_apply, hzero]
  have hsum_real : μ.errorProb (fun x y z => f x y = z) x₀ y₀ +
      μ.errorProb (fun x y z => f x y = z) x₁ y₁ = 1 := by
    unfold PublicCoinRoundProtocol.errorProb
    have hc : ({P : BoundedRoundProtocol X Y Bool turn r | P.run x₀ y₀ = false})ᶜ =
        {P | P.run x₀ y₀ = true} := by
      ext P; cases P.run x₀ y₀ <;> simp
    rw [hmeas0, hmeas1, ← hc]
    exact Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ _
  have he0 := hsol x₀ (Set.mem_univ _) y₀ (Set.mem_univ _)
  have he1 := hsol x₁ (Set.mem_univ _) y₁ (Set.mem_univ _)
  linarith

/-- Every `1/3`-error public-coin protocol solving `pointerChasing K` for `N ≥ 2` and `K ≥ 1`
transmits at least `1` bit. -/
theorem one_le_totalBits_of_solves_pointerChasing {N K C : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    {turn : Bool} {r : ℕ}
    (μ : PublicCoinRoundProtocol (Fin N → Fin N) (Fin N → Fin N) Bool turn r)
    (hsol : have : NeZero N := ⟨by omega⟩; μ.SolvesFun (1 / 3) (pointerChasing K))
    (hbits : μ.BitsLE C) :
    1 ≤ C := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨fA₀, fA₁, fB, h0, h1⟩ := pointerChasing_nonconstant hN hK
  exact one_le_bits_of_solvesFun_nonconstant (by norm_num) ⟨fA₀, fA₁, fB, fB, h0, h1⟩ hsol hbits

/-- **Exact deterministic `K = 2` lower bound**: every deterministic `2`-round Bob-first
protocol (one Bob message followed by Alice's announcement) solving `pointerChasing 2` on `Fin N`
transmits at least `N` bits. -/
theorem pointerChasing_det_twoRound_bobFirst_lower_bound {N : ℕ} (hN : 2 ≤ N)
    (P : BoundedRoundProtocol (Fin N → Fin N) (Fin N → Fin N) Bool false 2)
    (hsol : have : NeZero N := ⟨by omega⟩;
      ∀ fA fB, P.run fA fB = pointerChasing 2 fA fB) :
    N ≤ P.totalBits := by
  have : NeZero N := ⟨by omega⟩
  cases P with
  | output z =>
    obtain ⟨fA₀, fA₁, fB, h0, h1⟩ := pointerChasing_nonconstant hN (K := 2) (by omega)
    have e0 := hsol fA₀ fB
    have e1 := hsol fA₁ fB
    simp only [BoundedRoundProtocol.run_output, h0, h1] at e0 e1
    exact absurd (e0.symm.trans e1) (by decide)
  | bob c send next =>
    have hc : N ≤ c := by
      let parity : (Fin N → Bool) → (Fin N → Fin N) := fun g j =>
        if g j then ⟨0, by omega⟩ else ⟨1, by omega⟩
      have hinj : Function.Injective (fun g : Fin N → Bool => send (parity g)) := by
        intro g₁ g₂ hEq
        funext j
        have h1 := hsol (fun _ => j) (parity g₁)
        have h2 := hsol (fun _ => j) (parity g₂)
        simp only [BoundedRoundProtocol.run_bob, hEq] at h1
        simp only [BoundedRoundProtocol.run_bob] at h2
        rw [BoundedRoundProtocol.run_eq_of_one_alice _ _ (parity g₁) (parity g₂)] at h1
        have hsame : pointerChasing 2 (fun _ => j) (parity g₁) =
            pointerChasing 2 (fun _ => j) (parity g₂) := h1.symm.trans h2
        have hpc : ∀ g : Fin N → Bool,
            pointerChasing 2 (fun _ => j) (parity g) = g j := by
          intro g
          simp only [pointerChasing, pointerChase, parity]
          cases hgj : g j <;> simp [hgj]
        rwa [hpc g₁, hpc g₂] at hsame
      have hcard := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
      exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hcard
    exact hc.trans (Nat.le_add_right c _)

/-- Auxiliary encoding of `Fin N` into `BitString (Nat.clog 2 N)`. -/
private noncomputable def finEncode (N : ℕ) : Fin N ↪ BitString (Nat.clog 2 N) := by
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (BitString (Nat.clog 2 N)) := by
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
    exact Nat.le_pow_clog (by omega) N
  exact Classical.choice (Function.Embedding.nonempty_of_card_le hcard)

/-- Auxiliary deterministic Alice-first or Bob-first pointer-chasing continuation sending the
remaining `r` pointers and announcing the final parity in `1` bit. -/
private noncomputable def chaseFrom {N : ℕ} [NeZero N] :
    (turn : Bool) → (r : ℕ) → Fin N →
      BoundedRoundProtocol (Fin N → Fin N) (Fin N → Fin N) Bool turn (r + 1)
  | true, 0, v =>
    .alice 1 (fun fA _ => decide ((fA v).val % 2 = 0))
      (fun m => .output (m ⟨0, by omega⟩))
  | false, 0, v =>
    .bob 1 (fun fB _ => decide ((fB v).val % 2 = 0))
      (fun m => .output (m ⟨0, by omega⟩))
  | true, r + 1, v =>
    .alice (Nat.clog 2 N) (fun fA => finEncode N (fA v)) fun m =>
      chaseFrom false r (Function.invFun (finEncode N) m)
  | false, r + 1, v =>
    .bob (Nat.clog 2 N) (fun fB => finEncode N (fB v)) fun m =>
      chaseFrom true r (Function.invFun (finEncode N) m)

private theorem run_chaseFrom {N : ℕ} [NeZero N] :
    ∀ (turn : Bool) (r : ℕ) (v : Fin N) (fA fB : Fin N → Fin N),
      (chaseFrom turn r v).run fA fB =
        decide ((Nat.iterate
          (fun p : Fin N × Bool => (if p.2 then fA p.1 else fB p.1, !p.2))
          (r + 1) (v, turn)).1.val % 2 = 0)
  | true, 0, v, fA, fB => by
    simp [chaseFrom]
  | false, 0, v, fA, fB => by
    simp [chaseFrom]
  | true, r + 1, v, fA, fB => by
    have hinv : Function.invFun (finEncode N) (finEncode N (fA v)) = fA v :=
      Function.leftInverse_invFun (finEncode N).injective (fA v)
    simp only [chaseFrom, BoundedRoundProtocol.run_alice, hinv, run_chaseFrom]
    rw [Function.iterate_succ_apply]
    simp
  | false, r + 1, v, fA, fB => by
    have hinv : Function.invFun (finEncode N) (finEncode N (fB v)) = fB v :=
      Function.leftInverse_invFun (finEncode N).injective (fB v)
    simp only [chaseFrom, BoundedRoundProtocol.run_bob, hinv, run_chaseFrom]
    rw [Function.iterate_succ_apply]
    simp

private theorem totalBits_chaseFrom {N : ℕ} [NeZero N] :
    ∀ (turn : Bool) (r : ℕ) (v : Fin N),
      (chaseFrom turn r v).totalBits ≤ r * Nat.clog 2 N + 1
  | true, 0, v => by
    simp [chaseFrom]
  | false, 0, v => by
    simp [chaseFrom]
  | true, r + 1, v => by
    simp only [chaseFrom, BoundedRoundProtocol.totalBits_alice]
    have hsup : Finset.univ.sup (fun m => (chaseFrom false r
        (Function.invFun (finEncode N) m)).totalBits) ≤ r * Nat.clog 2 N + 1 :=
      Finset.sup_le fun m _ => totalBits_chaseFrom false r _
    calc
      Nat.clog 2 N + _ ≤ Nat.clog 2 N + (r * Nat.clog 2 N + 1) := Nat.add_le_add_left hsup _
      _ = (r + 1) * Nat.clog 2 N + 1 := by ring
  | false, r + 1, v => by
    simp only [chaseFrom, BoundedRoundProtocol.totalBits_bob]
    have hsup : Finset.univ.sup (fun m => (chaseFrom true r
        (Function.invFun (finEncode N) m)).totalBits) ≤ r * Nat.clog 2 N + 1 :=
      Finset.sup_le fun m _ => totalBits_chaseFrom true r _
    calc
      Nat.clog 2 N + _ ≤ Nat.clog 2 N + (r * Nat.clog 2 N + 1) := Nat.add_le_add_left hsup _
      _ = (r + 1) * Nat.clog 2 N + 1 := by ring

private theorem pointerChase_eq_iterate {N : ℕ} [NeZero N] (K : ℕ) (fA fB : Fin N → Fin N) :
    (pointerChase K fA fB, decide (K % 2 = 0)) =
      Nat.iterate (fun p : Fin N × Bool => (if p.2 then fA p.1 else fB p.1, !p.2)) K (0, true) := by
  induction K with
  | zero => simp [pointerChase]
  | succ r ih =>
    rw [Function.iterate_succ_apply', ← ih]
    by_cases hpar : r % 2 = 0
    · have h1 : (r + 1) % 2 = 1 := by omega
      simp [pointerChase, hpar, h1]
    · have h0 : (r + 1) % 2 = 0 := by omega
      simp [pointerChase, hpar, h0]

/-- **Sharpness in rounds**: an Alice-first `K`-round deterministic protocol solves
`pointerChasing K` with error `0` and `(K - 1) * ⌈log₂ N⌉ + 1` bits. -/
theorem pointerChasing_aliceFirst_upper_bound {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    have : NeZero N := ⟨by omega⟩
    ∃ P : BoundedRoundProtocol (Fin N → Fin N) (Fin N → Fin N) Bool true K,
      (∀ fA fB, P.run fA fB = pointerChasing K fA fB) ∧
      P.totalBits ≤ (K - 1) * Nat.clog 2 N + 1 := by
  have : NeZero N := ⟨by omega⟩
  cases K with
  | zero => omega
  | succ r =>
    refine ⟨chaseFrom true r 0, fun fA fB => ?_, totalBits_chaseFrom true r 0⟩
    rw [run_chaseFrom]
    have hiter := pointerChase_eq_iterate (r + 1) fA fB
    have hf : pointerChase (r + 1) fA fB =
        (Nat.iterate (fun p : Fin N × Bool => (if p.2 then fA p.1 else fB p.1, !p.2))
          (r + 1) (0, true)).1 :=
      congrArg Prod.fst hiter
    simp [pointerChasing, hf]

/-- **Sharpness in `N`**: for `N = 1`, `pointerChasing K` is solved with `0` bits and error `0`. -/
theorem pointerChasing_one_vertex_trivial (K : ℕ) :
    ∃ P : BoundedRoundProtocol (Fin 1 → Fin 1) (Fin 1 → Fin 1) Bool false 0,
      (∀ fA fB, P.run fA fB = pointerChasing K fA fB) ∧ P.totalBits = 0 := by
  refine ⟨.output true, fun fA fB => ?_, rfl⟩
  have h0 : pointerChase K fA fB = 0 := Subsingleton.elim _ _
  simp [pointerChasing, h0]

/-- **Sharpness of the `+ K` term for 2-function pointer chasing**: for `N = 2` and every `K ≥ 1`,
a `2`-round Bob-first deterministic protocol solves `pointerChasing K` in `3` bits. -/
theorem pointerChasing_two_vertex_upper_bound (K : ℕ) :
    ∃ P : BoundedRoundProtocol (Fin 2 → Fin 2) (Fin 2 → Fin 2) Bool false 2,
      (∀ fA fB, P.run fA fB = pointerChasing K fA fB) ∧ P.totalBits ≤ 3 := by
  let encB : (Fin 2 → Fin 2) → BitString 2 := fun fB i => decide (fB i = 1)
  let decB : BitString 2 → (Fin 2 → Fin 2) := fun m i => if m i then 1 else 0
  have hdec : ∀ fB, decB (encB fB) = fB := by
    intro fB; funext i
    simp only [decB, encB]
    have h01 : fB i = 0 ∨ fB i = 1 := by
      have hlt := (fB i).isLt
      by_cases h0 : (fB i).val = 0
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext (by omega))
    rcases h01 with h | h <;> simp [h]
  refine ⟨.bob 2 encB fun mB =>
    .alice 1 (fun fA _ => pointerChasing K fA (decB mB)) fun mA =>
      .output (mA 0), ?_, ?_⟩
  · intro fA fB
    simp [hdec]
  · simp only [BoundedRoundProtocol.totalBits_bob, BoundedRoundProtocol.totalBits_alice]
    have hsup2 : Finset.univ.sup (fun mB : BitString 2 =>
        1 + Finset.univ.sup (fun mA : BitString 1 =>
          (BoundedRoundProtocol.output (turn := false) (r := 0) (mA 0) :
            BoundedRoundProtocol (Fin 2 → Fin 2) (Fin 2 → Fin 2) Bool false 0).totalBits)) ≤ 1 :=
      Finset.sup_le fun mB _ => by simp
    omega

/-- **Sharpness in error**: a `0`-bit public-coin protocol (uniform coin flip) achieves error `1/2`
for every `N ≥ 1` and `K`. -/
theorem pointerChasing_half_error_zero_bits {N : ℕ} [NeZero N] (K : ℕ) :
    ∃ μ : PublicCoinRoundProtocol (Fin N → Fin N) (Fin N → Fin N) Bool false 0,
      μ.SolvesFun (1 / 2) (pointerChasing K) ∧ μ.BitsLE 0 := by
  let μ : PublicCoinRoundProtocol (Fin N → Fin N) (Fin N → Fin N) Bool false 0 :=
    (PMF.uniformOfFintype Bool).map BoundedRoundProtocol.output
  refine ⟨μ, ?_, ?_⟩
  · intro fA _ fB _
    unfold PublicCoinRoundProtocol.errorProb
    have hpre : μ.toOuterMeasure {P | ¬(pointerChasing K fA fB = P.run fA fB)} =
        (PMF.uniformOfFintype Bool).toOuterMeasure {b : Bool | b ≠ pointerChasing K fA fB} := by
      simp only [μ, PMF.toOuterMeasure_map_apply]
      congr 1
      ext b
      simp [eq_comm]
    rw [hpre]
    have hcard : ({b : Bool | b ≠ pointerChasing K fA fB} : Set Bool) =
        {!pointerChasing K fA fB} := by
      ext b; cases b <;> cases pointerChasing K fA fB <;> simp
    rw [hcard, PMF.toOuterMeasure_apply_singleton]
    simp [PMF.uniformOfFintype_apply]
  · intro P hP
    obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hP
    simp

end CslibFrontier.Computability.Communication
