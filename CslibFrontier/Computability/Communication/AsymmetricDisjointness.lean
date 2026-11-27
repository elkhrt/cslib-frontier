/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.Communication.Operations
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Log

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Asymmetric Communication Costs and Lopsided Set Disjointness

This module develops asymmetric worst-case Alice and Bob bit-cost accounting directly on
`Cslib.Communication.Protocol` strictly under standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`), proving the Miltersen–Nisan–Safra–Wigderson (MNSW)
leaf-projection sum inequalities and Pătrașcu's two-bucket rectangle lower bounds for Blocked and
Switch-Permutation Lopsided Set Disjointness.

## Main definitions

* `CslibFrontier.Communication.aliceCost`, `CslibFrontier.Communication.bobCost`:
  separate worst-case Alice and Bob bit budgets on `Cslib.Communication.Protocol`.
* `CslibFrontier.Communication.natToBitString`,
  `CslibFrontier.Communication.bitStringToNat`,
  `CslibFrontier.Communication.aliceSendFin`,
  `CslibFrontier.Communication.aliceFinish`: little-endian bit-string codecs, bounded-integer
  `Fin M` transmission in `⌈log₂ M⌉` bits, and Alice-local leaf finishing.
* `CslibFrontier.Communication.leavesFrom`: top-down decomposition of a finite rectangle
  `A₀ × B₀` into monochromatic protocol leaf rectangles.
* `CslibFrontier.Communication.BlockedAlice`,
  `CslibFrontier.Communication.blockedDisjoint`: Blocked Lopsided Set Disjointness
  $\mathsf{BLSD}_{N, B}$.
* `CslibFrontier.Communication.SwitchPermAlice`,
  `CslibFrontier.Communication.switchPermDisjoint`: Switch-Permutation Lopsided Set
  Disjointness $\mathsf{SPLSD}_{M, B}$.

## Main results

* `CslibFrontier.Communication.sum_card_snd_leavesFrom_le`,
  `CslibFrontier.Communication.sum_card_fst_leavesFrom_le`: MNSW leaf-projection sum bounds
  $\sum_\ell |B_\ell| \le 2^{a(P)} |B_0|$ and $\sum_\ell |A_\ell| \le 2^{b(P)} |A_0|$.
* `CslibFrontier.Communication.wire_selector_lsd_lower_bound`: master two-bucket rectangle
  trade-off for injective wire-selector families.
* `CslibFrontier.Communication.blocked_lsd_master_lower_bound`,
  `CslibFrontier.Communication.blocked_lsd_sqrt_lower_bound`,
  `CslibFrontier.Communication.blocked_lsd_lower_bound`: Blocked LSD asymmetric lower bounds.
* `CslibFrontier.Communication.div_exp_one_pow_le_factorial`,
  `CslibFrontier.Communication.switch_perm_lsd_master_lower_bound`,
  `CslibFrontier.Communication.switch_perm_lsd_sqrt_lower_bound`: Switch-Permutation LSD
  asymmetric lower bounds.

## Tags

communication complexity, asymmetric communication, lopsided set disjointness, rectangle bound
-/

public section

open scoped BigOperators

namespace CslibFrontier.Communication

open Cslib.Communication

/-! ### 1. Separate Alice and Bob Bit Budgets, Round Combinators, and MNSW Leaf Bounds -/

section ProtocolCostsAndMNSW

variable {X X' Y Y' Z Z' : Type*}

/-- Worst-case number of bits transmitted by Alice along any root-to-leaf path in `P`. -/
def aliceCost : Protocol X Y Z → ℕ
  | .output _ => 0
  | .alice _ p₀ p₁ => 1 + max (aliceCost p₀) (aliceCost p₁)
  | .bob _ p₀ p₁ => max (aliceCost p₀) (aliceCost p₁)

@[simp, grind =]
theorem aliceCost_output (z : Z) : aliceCost (Protocol.output z : Protocol X Y Z) = 0 := by rfl

@[simp, grind =]
theorem aliceCost_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) :
    aliceCost (.alice send p₀ p₁) = 1 + max (aliceCost p₀) (aliceCost p₁) := by rfl

@[simp, grind =]
theorem aliceCost_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) :
    aliceCost (.bob send p₀ p₁) = max (aliceCost p₀) (aliceCost p₁) := by rfl

/-- Worst-case number of bits transmitted by Bob along any root-to-leaf path in `P`. -/
def bobCost : Protocol X Y Z → ℕ
  | .output _ => 0
  | .alice _ p₀ p₁ => max (bobCost p₀) (bobCost p₁)
  | .bob _ p₀ p₁ => 1 + max (bobCost p₀) (bobCost p₁)

@[simp, grind =]
theorem bobCost_output (z : Z) : bobCost (Protocol.output z : Protocol X Y Z) = 0 := by rfl

@[simp, grind =]
theorem bobCost_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) :
    bobCost (.alice send p₀ p₁) = max (bobCost p₀) (bobCost p₁) := by rfl

@[simp, grind =]
theorem bobCost_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) :
    bobCost (.bob send p₀ p₁) = 1 + max (bobCost p₀) (bobCost p₁) := by rfl

/-- Total tree depth is bounded above by the sum of Alice's and Bob's worst-case bit costs. -/
theorem depth_le_aliceCost_add_bobCost (P : Protocol X Y Z) :
    P.depth ≤ aliceCost P + bobCost P := by
  induction P with
  | output _ => simp
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp only [Protocol.depth_alice, Protocol.depth_bob, aliceCost_alice, aliceCost_bob,
      bobCost_alice, bobCost_bob]
    omega

/-- Exchanging players via `Protocol.swap` swaps Alice's and Bob's bit costs. -/
@[simp, grind =]
theorem aliceCost_swap (P : Protocol X Y Z) : aliceCost P.swap = bobCost P := by
  induction P with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [Protocol.swap, ih₀, ih₁]

/-- Exchanging players via `Protocol.swap` swaps Bob's and Alice's bit costs. -/
@[simp, grind =]
theorem bobCost_swap (P : Protocol X Y Z) : bobCost P.swap = aliceCost P := by
  induction P with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [Protocol.swap, ih₀, ih₁]

/-- Input pullback `Protocol.comap` preserves Alice's worst-case bit cost. -/
@[simp, grind =]
theorem aliceCost_comap (fX : X' → X) (fY : Y' → Y) (P : Protocol X Y Z) :
    aliceCost (P.comap fX fY) = aliceCost P := by
  induction P with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [Protocol.comap, ih₀, ih₁]

/-- Input pullback `Protocol.comap` preserves Bob's worst-case bit cost. -/
@[simp, grind =]
theorem bobCost_comap (fX : X' → X) (fY : Y' → Y) (P : Protocol X Y Z) :
    bobCost (P.comap fX fY) = bobCost P := by
  induction P with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [Protocol.comap, ih₀, ih₁]

/-- Output relabeling `Protocol.map` preserves Alice's worst-case bit cost. -/
@[simp, grind =]
theorem aliceCost_map (h : Z → Z') (P : Protocol X Y Z) :
    aliceCost (P.map h) = aliceCost P := by
  induction P with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [Protocol.map, ih₀, ih₁]

/-- Output relabeling `Protocol.map` preserves Bob's worst-case bit cost. -/
@[simp, grind =]
theorem bobCost_map (h : Z → Z') (P : Protocol X Y Z) :
    bobCost (P.map h) = bobCost P := by
  induction P with
  | output _ => rfl
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [Protocol.map, ih₀, ih₁]

/-- If `aliceCost P = 0`, the output of `P` is independent of Alice's input `x` for fixed `y`. -/
theorem run_eq_of_aliceCost_eq_zero {P : Protocol X Y Z} (ha : aliceCost P = 0)
    (x₁ x₂ : X) (y : Y) : P.run x₁ y = P.run x₂ y := by
  induction P with
  | output _ => rfl
  | alice _ _ _ =>
    rw [aliceCost_alice] at ha
    omega
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [aliceCost_bob] at ha
    rw [Protocol.run_bob, Protocol.run_bob]
    cases send y
    · exact ih₀ (by omega)
    · exact ih₁ (by omega)

/-- If `bobCost P = 0`, the output of `P` is independent of Bob's input `y` for fixed `x`. -/
theorem run_eq_of_bobCost_eq_zero {P : Protocol X Y Z} (hb : bobCost P = 0)
    (x : X) (y₁ y₂ : Y) : P.run x y₁ = P.run x y₂ := by
  induction P with
  | output _ => rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [bobCost_alice] at hb
    rw [Protocol.run_alice, Protocol.run_alice]
    cases send x
    · exact ih₀ (by omega)
    · exact ih₁ (by omega)
  | bob _ _ _ =>
    rw [bobCost_bob] at hb
    omega

/-- Any protocol with zero Alice cost and zero Bob cost is constant on `X × Y`. -/
theorem run_eq_of_aliceCost_eq_zero_of_bobCost_eq_zero {P : Protocol X Y Z}
    (ha : aliceCost P = 0) (hb : bobCost P = 0) (x₁ x₂ : X) (y₁ y₂ : Y) :
    P.run x₁ y₁ = P.run x₂ y₂ :=
  (run_eq_of_aliceCost_eq_zero ha x₁ x₂ y₁).trans (run_eq_of_bobCost_eq_zero hb x₂ y₁ y₂)

/-- Sending `n` bits via `Protocol.aliceSend` adds at most `n` to Alice's bit cost. -/
theorem aliceCost_aliceSend_le {n a : ℕ} {msg : X → Cslib.BitString n}
    {cont : Cslib.BitString n → Protocol X Y Z} (h : ∀ m, aliceCost (cont m) ≤ a) :
    aliceCost (Protocol.aliceSend n msg cont) ≤ n + a := by
  induction n with
  | zero => simpa [Protocol.aliceSend] using h Fin.elim0
  | succ n ih =>
    simp only [Protocol.aliceSend, aliceCost_alice]
    have hf := ih (msg := fun x ↦ Fin.tail (msg x)) fun m ↦ h (Fin.cons false m)
    have ht := ih (msg := fun x ↦ Fin.tail (msg x)) fun m ↦ h (Fin.cons true m)
    omega

/-- Alice sending `n` bits via `Protocol.aliceSend` adds `0` to Bob's bit cost. -/
theorem bobCost_aliceSend_le {n b : ℕ} {msg : X → Cslib.BitString n}
    {cont : Cslib.BitString n → Protocol X Y Z} (h : ∀ m, bobCost (cont m) ≤ b) :
    bobCost (Protocol.aliceSend n msg cont) ≤ b := by
  induction n with
  | zero => simpa [Protocol.aliceSend] using h Fin.elim0
  | succ n ih =>
    simp only [Protocol.aliceSend, bobCost_alice]
    exact max_le (ih fun m ↦ h (Fin.cons false m)) (ih fun m ↦ h (Fin.cons true m))

/-- Bob sending `n` bits via `Protocol.bobSend` adds `0` to Alice's bit cost. -/
theorem aliceCost_bobSend_le {n a : ℕ} {msg : Y → Cslib.BitString n}
    {cont : Cslib.BitString n → Protocol X Y Z} (h : ∀ m, aliceCost (cont m) ≤ a) :
    aliceCost (Protocol.bobSend n msg cont) ≤ a := by
  simpa [Protocol.bobSend] using
    bobCost_aliceSend_le (msg := msg) fun m ↦ (bobCost_swap (cont m)).trans_le (h m)

/-- Sending `n` bits via `Protocol.bobSend` adds at most `n` to Bob's bit cost. -/
theorem bobCost_bobSend_le {n b : ℕ} {msg : Y → Cslib.BitString n}
    {cont : Cslib.BitString n → Protocol X Y Z} (h : ∀ m, bobCost (cont m) ≤ b) :
    bobCost (Protocol.bobSend n msg cont) ≤ n + b := by
  simpa [Protocol.bobSend] using
    aliceCost_aliceSend_le (msg := msg) fun m ↦ (aliceCost_swap (cont m)).trans_le (h m)

/-- Little-endian `L`-bit binary encoding of a natural number `n : ℕ`. -/
def natToBitString : (L : ℕ) → ℕ → Cslib.BitString L
  | 0, _ => Fin.elim0
  | L + 1, n => Fin.cons (decide (n % 2 = 1)) (natToBitString L (n / 2))

@[simp, grind =]
theorem natToBitString_zero (n : ℕ) : natToBitString 0 n = Fin.elim0 := by rfl

/-- Natural number decoded from a little-endian `L`-bit string `m : Cslib.BitString L`. -/
def bitStringToNat : {L : ℕ} → Cslib.BitString L → ℕ
  | 0, _ => 0
  | _ + 1, m => (if m 0 then 1 else 0) + 2 * bitStringToNat (Fin.tail m)

@[simp, grind =]
theorem bitStringToNat_zero (m : Cslib.BitString 0) : bitStringToNat m = 0 := by rfl

/-- Decoding the `L`-bit little-endian binary expansion of any `n < 2 ^ L` recovers `n`. -/
@[simp, grind =]
theorem bitStringToNat_natToBitString_of_lt {L n : ℕ} (hn : n < 2 ^ L) :
    bitStringToNat (natToBitString L n) = n := by
  induction L generalizing n with
  | zero =>
    simp only [Nat.pow_zero] at hn
    rw [bitStringToNat_zero]
    omega
  | succ L ih =>
    rw [Nat.pow_succ] at hn
    rw [natToBitString, bitStringToNat, Fin.cons_zero, Fin.tail_cons, ih (by omega)]
    by_cases hpar : n % 2 = 1
    · simp only [decide_eq_true hpar, ↓reduceIte]; omega
    · simp only [decide_eq_false hpar, Bool.false_eq_true, ↓reduceIte]; omega

/-- Bounded-integer Alice transmission combinator in which Alice sends `msg x : Fin M` using
`Nat.clog 2 M` bits and continues in `cont (msg x)`. -/
def aliceSendFin {M : ℕ} [NeZero M] (msg : X → Fin M)
    (cont : Fin M → Protocol X Y Z) : Protocol X Y Z :=
  Protocol.aliceSend (Nat.clog 2 M) (fun x ↦ natToBitString (Nat.clog 2 M) (msg x).1)
    (fun m ↦ cont (if h : bitStringToNat m < M then ⟨bitStringToNat m, h⟩ else ⟨0, NeZero.pos M⟩))

/-- Evaluating `aliceSendFin msg cont` runs `cont (msg x)`. -/
@[simp, grind =]
theorem run_aliceSendFin {M : ℕ} [NeZero M] (msg : X → Fin M)
    (cont : Fin M → Protocol X Y Z) (x : X) (y : Y) :
    (aliceSendFin msg cont).run x y = (cont (msg x)).run x y := by
  rw [aliceSendFin, Protocol.run_aliceSend]
  have hlt : (msg x).1 < 2 ^ Nat.clog 2 M :=
    (msg x).2.trans_le (Nat.le_pow_clog (by norm_num : 1 < 2) M)
  simp only [bitStringToNat_natToBitString_of_lt hlt, (msg x).2, ↓reduceDIte, Fin.eta]

/-- Transmitting a message in `Fin M` via `aliceSendFin` costs Alice at most `Nat.clog 2 M` bits
beyond the continuation cost. -/
theorem aliceCost_aliceSendFin_le {M a : ℕ} [NeZero M] {msg : X → Fin M}
    {cont : Fin M → Protocol X Y Z} (h : ∀ u, aliceCost (cont u) ≤ a) :
    aliceCost (aliceSendFin msg cont) ≤ Nat.clog 2 M + a :=
  aliceCost_aliceSend_le fun _ ↦ h _

/-- Alice transmitting in `Fin M` via `aliceSendFin` adds `0` to Bob's continuation cost. -/
theorem bobCost_aliceSendFin_le {M b : ℕ} [NeZero M] {msg : X → Fin M}
    {cont : Fin M → Protocol X Y Z} (h : ∀ u, bobCost (cont u) ≤ b) :
    bobCost (aliceSendFin msg cont) ≤ b :=
  bobCost_aliceSend_le fun _ ↦ h _

/-- Converts an Alice-output protocol `P : Protocol X Y (X → Z)` into a Boolean protocol
`Protocol X Y Bool` via `ψ : X → Z → Bool`, appending a single Alice bit node at each leaf. -/
def aliceFinish (ψ : X → Z → Bool) : Protocol X Y (X → Z) → Protocol X Y Bool
  | .output g => .alice (fun x ↦ ψ x (g x)) (.output false) (.output true)
  | .alice send p₀ p₁ => .alice send (aliceFinish ψ p₀) (aliceFinish ψ p₁)
  | .bob send p₀ p₁ => .bob send (aliceFinish ψ p₀) (aliceFinish ψ p₁)

@[simp, grind =]
theorem aliceFinish_output (ψ : X → Z → Bool) (g : X → Z) :
    aliceFinish ψ (Protocol.output g : Protocol X Y (X → Z)) =
      .alice (fun x ↦ ψ x (g x)) (.output false) (.output true) := by rfl

@[simp, grind =]
theorem aliceFinish_alice (ψ : X → Z → Bool) (send : X → Bool) (p₀ p₁ : Protocol X Y (X → Z)) :
    aliceFinish ψ (.alice send p₀ p₁) = .alice send (aliceFinish ψ p₀) (aliceFinish ψ p₁) := by rfl

@[simp, grind =]
theorem aliceFinish_bob (ψ : X → Z → Bool) (send : Y → Bool) (p₀ p₁ : Protocol X Y (X → Z)) :
    aliceFinish ψ (.bob send p₀ p₁) = .bob send (aliceFinish ψ p₀) (aliceFinish ψ p₁) := by rfl

/-- Evaluating `aliceFinish ψ P` on `(x, y)` computes `ψ x (P.run x y x)`. -/
@[simp, grind =]
theorem run_aliceFinish (ψ : X → Z → Bool) (P : Protocol X Y (X → Z)) (x : X) (y : Y) :
    (aliceFinish ψ P).run x y = ψ x (P.run x y x) := by
  induction P with
  | output g =>
    simp only [aliceFinish_output, Protocol.run_alice, Protocol.run_output]
    cases ψ x (g x) <;> rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    simp only [aliceFinish_alice, Protocol.run_alice]
    cases send x <;> [exact ih₀; exact ih₁]
  | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [aliceFinish_bob, Protocol.run_bob]
    cases send y <;> [exact ih₀; exact ih₁]

/-- Finishing an Alice-output protocol via `aliceFinish` adds `1` bit to Alice's cost. -/
@[simp, grind =]
theorem aliceCost_aliceFinish (ψ : X → Z → Bool) (P : Protocol X Y (X → Z)) :
    aliceCost (aliceFinish ψ P) = aliceCost P + 1 := by
  induction P with
  | output _ => simp
  | alice _ p₀ p₁ ih₀ ih₁ | bob _ p₀ p₁ ih₀ ih₁ =>
    simp only [aliceFinish_alice, aliceFinish_bob, aliceCost_alice, aliceCost_bob, ih₀, ih₁]
    omega

/-- Finishing an Alice-output protocol via `aliceFinish` preserves Bob's cost unchanged. -/
@[simp, grind =]
theorem bobCost_aliceFinish (ψ : X → Z → Bool) (P : Protocol X Y (X → Z)) :
    bobCost (aliceFinish ψ P) = bobCost P := by
  induction P with
  | output _ => simp
  | alice _ _ _ ih₀ ih₁ | bob _ _ _ ih₀ ih₁ =>
    simp [ih₀, ih₁]

/-- Top-down decomposition of a finite rectangle `A₀ × B₀ ⊆ X × Y` along a protocol `P` into
labeled leaf rectangles `(A_ℓ, B_ℓ, z_ℓ)`. -/
def leavesFrom : Protocol X Y Z → Finset X → Finset Y → List (Finset X × Finset Y × Z)
  | .output z, A₀, B₀ => [(A₀, B₀, z)]
  | .alice send p₀ p₁, A₀, B₀ =>
      leavesFrom p₀ (A₀.filter fun x ↦ send x = false) B₀ ++
        leavesFrom p₁ (A₀.filter fun x ↦ send x = true) B₀
  | .bob send p₀ p₁, A₀, B₀ =>
      leavesFrom p₀ A₀ (B₀.filter fun y ↦ send y = false) ++
        leavesFrom p₁ A₀ (B₀.filter fun y ↦ send y = true)

@[simp, grind =]
theorem leavesFrom_output (z : Z) (A₀ : Finset X) (B₀ : Finset Y) :
    leavesFrom (Protocol.output z : Protocol X Y Z) A₀ B₀ = [(A₀, B₀, z)] := by rfl

@[simp, grind =]
theorem leavesFrom_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z)
    (A₀ : Finset X) (B₀ : Finset Y) :
    leavesFrom (.alice send p₀ p₁) A₀ B₀ =
      leavesFrom p₀ (A₀.filter fun x ↦ send x = false) B₀ ++
        leavesFrom p₁ (A₀.filter fun x ↦ send x = true) B₀ := by rfl

@[simp, grind =]
theorem leavesFrom_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z)
    (A₀ : Finset X) (B₀ : Finset Y) :
    leavesFrom (.bob send p₀ p₁) A₀ B₀ =
      leavesFrom p₀ A₀ (B₀.filter fun y ↦ send y = false) ++
        leavesFrom p₁ A₀ (B₀.filter fun y ↦ send y = true) := by rfl

private lemma card_filter_bool_false_add_true {α : Type*} (S : Finset α) (f : α → Bool) :
    (S.filter fun a ↦ f a = false).card + (S.filter fun a ↦ f a = true).card = S.card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext a; simp only [Finset.mem_union, Finset.mem_filter]; cases f a <;> tauto
  · exact Finset.disjoint_left.mpr fun a h0 h1 ↦ Bool.false_ne_true <|
      (Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h1).2

/-- **Miltersen–Nisan–Safra–Wigderson Bob-Projection Sum Bound**: the sum of `|B_ℓ|` over all
leaf rectangles in `leavesFrom P A₀ B₀` is at most `2 ^ aliceCost P * B₀.card`. -/
theorem sum_card_snd_leavesFrom_le (P : Protocol X Y Z) (A₀ : Finset X) (B₀ : Finset Y) :
    ((leavesFrom P A₀ B₀).map fun r ↦ r.2.1.card).sum ≤ 2 ^ aliceCost P * B₀.card := by
  induction P generalizing A₀ B₀ with
  | output _ => simp
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_alice, List.map_append, List.sum_append, aliceCost_alice]
    have h0 := (ih₀ (A₀.filter fun x ↦ send x = false) B₀).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_left (aliceCost p₀) (aliceCost p₁))))
    have h1 := (ih₁ (A₀.filter fun x ↦ send x = true) B₀).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_right (aliceCost p₀) (aliceCost p₁))))
    refine (Nat.add_le_add h0 h1).trans_eq ?_
    rw [Nat.pow_add, Nat.pow_one, two_mul, add_mul]
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_bob, List.map_append, List.sum_append, aliceCost_bob]
    have h0 := (ih₀ A₀ (B₀.filter fun y ↦ send y = false)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_left (aliceCost p₀) (aliceCost p₁))))
    have h1 := (ih₁ A₀ (B₀.filter fun y ↦ send y = true)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_right (aliceCost p₀) (aliceCost p₁))))
    refine (Nat.add_le_add h0 h1).trans_eq ?_
    rw [← mul_add, card_filter_bool_false_add_true]

/-- **Miltersen–Nisan–Safra–Wigderson Alice-Projection Sum Bound**: the sum of `|A_ℓ|` over all
leaf rectangles in `leavesFrom P A₀ B₀` is at most `2 ^ bobCost P * A₀.card`. -/
theorem sum_card_fst_leavesFrom_le (P : Protocol X Y Z) (A₀ : Finset X) (B₀ : Finset Y) :
    ((leavesFrom P A₀ B₀).map fun r ↦ r.1.card).sum ≤ 2 ^ bobCost P * A₀.card := by
  induction P generalizing A₀ B₀ with
  | output _ => simp
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_alice, List.map_append, List.sum_append, bobCost_alice]
    have h0 := (ih₀ (A₀.filter fun x ↦ send x = false) B₀).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_left (bobCost p₀) (bobCost p₁))))
    have h1 := (ih₁ (A₀.filter fun x ↦ send x = true) B₀).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_right (bobCost p₀) (bobCost p₁))))
    refine (Nat.add_le_add h0 h1).trans_eq ?_
    rw [← mul_add, card_filter_bool_false_add_true]
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_bob, List.map_append, List.sum_append, bobCost_bob]
    have h0 := (ih₀ A₀ (B₀.filter fun y ↦ send y = false)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_left (bobCost p₀) (bobCost p₁))))
    have h1 := (ih₁ A₀ (B₀.filter fun y ↦ send y = true)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (le_max_right (bobCost p₀) (bobCost p₁))))
    refine (Nat.add_le_add h0 h1).trans_eq ?_
    rw [Nat.pow_add, Nat.pow_one, two_mul, add_mul]

/-- Every leaf rectangle `(A, B, z)` in `leavesFrom P A₀ B₀` satisfies `A ⊆ A₀`, `B ⊆ B₀`, and
monochromatic evaluation `P.run x y = z` on `A × B`. -/
theorem mem_leavesFrom_subset_and_run {P : Protocol X Y Z}
    {A₀ A : Finset X} {B₀ B : Finset Y} {z : Z}
    (hr : (A, B, z) ∈ leavesFrom P A₀ B₀) :
    A ⊆ A₀ ∧ B ⊆ B₀ ∧ ∀ x ∈ A, ∀ y ∈ B, P.run x y = z := by
  induction P generalizing A₀ B₀ with
  | output z₀ =>
    rw [leavesFrom_output, List.mem_singleton, Prod.mk.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl, rfl⟩
    exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ _ _ ↦ rfl⟩
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_alice, List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨hA, hB, hev⟩ := ih₀ hr
      refine ⟨hA.trans (Finset.filter_subset _ A₀), hB, fun x hx y hy ↦ ?_⟩
      rw [Protocol.run_alice, (Finset.mem_filter.mp (hA hx)).2]
      exact hev x hx y hy
    · obtain ⟨hA, hB, hev⟩ := ih₁ hr
      refine ⟨hA.trans (Finset.filter_subset _ A₀), hB, fun x hx y hy ↦ ?_⟩
      rw [Protocol.run_alice, (Finset.mem_filter.mp (hA hx)).2]
      exact hev x hx y hy
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_bob, List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨hA, hB, hev⟩ := ih₀ hr
      refine ⟨hA, hB.trans (Finset.filter_subset _ B₀), fun x hx y hy ↦ ?_⟩
      rw [Protocol.run_bob, (Finset.mem_filter.mp (hB hy)).2]
      exact hev x hx y hy
    · obtain ⟨hA, hB, hev⟩ := ih₁ hr
      refine ⟨hA, hB.trans (Finset.filter_subset _ B₀), fun x hx y hy ↦ ?_⟩
      rw [Protocol.run_bob, (Finset.mem_filter.mp (hB hy)).2]
      exact hev x hx y hy

/-- Exact pair-counting partition identity for `leavesFrom` with respect to any Boolean pair
predicate `Good : X → Y → Bool`. -/
theorem card_filter_product_eq_sum_leavesFrom (P : Protocol X Y Z)
    (A₀ : Finset X) (B₀ : Finset Y) (Good : X → Y → Bool) :
    ((A₀ ×ˢ B₀).filter fun p ↦ Good p.1 p.2).card =
      ((leavesFrom P A₀ B₀).map fun r ↦
        ((r.1 ×ˢ r.2.1).filter fun p ↦ Good p.1 p.2).card).sum := by
  classical
  induction P generalizing A₀ B₀ with
  | output _ => simp
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_alice, List.map_append, List.sum_append, ← ih₀, ← ih₁]
    let Af := ((A₀.filter fun x ↦ send x = false) ×ˢ B₀).filter fun p ↦ Good p.1 p.2
    let At := ((A₀.filter fun x ↦ send x = true) ×ˢ B₀).filter fun p ↦ Good p.1 p.2
    have hdisj : Disjoint Af At := Finset.disjoint_left.mpr fun p h₁ h₂ ↦ Bool.false_ne_true <|
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₁).1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₂).1).1).2
    have hunion : ((A₀ ×ˢ B₀).filter fun p ↦ Good p.1 p.2) = Af ∪ At := by
      ext ⟨x, y⟩; simp only [Af, At, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
      cases send x <;> tauto
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [leavesFrom_bob, List.map_append, List.sum_append, ← ih₀, ← ih₁]
    let Bf := (A₀ ×ˢ (B₀.filter fun y ↦ send y = false)).filter fun p ↦ Good p.1 p.2
    let Bt := (A₀ ×ˢ (B₀.filter fun y ↦ send y = true)).filter fun p ↦ Good p.1 p.2
    have hdisj : Disjoint Bf Bt := Finset.disjoint_left.mpr fun p h₁ h₂ ↦ Bool.false_ne_true <|
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₁).1).2).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₂).1).2).2
    have hunion : ((A₀ ×ˢ B₀).filter fun p ↦ Good p.1 p.2) = Bf ∪ Bt := by
      ext ⟨x, y⟩; simp only [Bf, Bt, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
      cases send y <;> tauto
    rw [hunion, Finset.card_union_of_disjoint hdisj]

end ProtocolCostsAndMNSW

/-! ### 2. Master Wire-Selector Two-Bucket Rectangle Lower Bound -/

section MasterWireSelector

private lemma card_powersetCard_filter_subset {β : Type*} [DecidableEq β]
    (U T : Finset β) {K : ℕ} (hTU : T ⊆ U) (hTK : T.card ≤ K) :
    ((U.powersetCard K).filter fun S ↦ T ⊆ S).card = (U.card - T.card).choose (K - T.card) := by
  have hsdiff : (U \ T).card = U.card - T.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTU]
  rw [← hsdiff, ← Finset.card_powersetCard]
  refine Finset.card_bij (fun S _ ↦ S \ T) ?_ ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSK, hTS⟩
    rcases Finset.mem_powersetCard.mp hSK with ⟨hSU, hcard⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hSU Finset.Subset.rfl,
      by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTS, hcard]⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    rw [← Finset.union_sdiff_of_subset (Finset.mem_filter.mp hS₁).2, heq,
      Finset.union_sdiff_of_subset (Finset.mem_filter.mp hS₂).2]
  · intro D hD
    rcases Finset.mem_powersetCard.mp hD with ⟨hDU, hDcard⟩
    have hdisj : Disjoint T D := Disjoint.mono_right hDU disjoint_sdiff_self_right
    refine ⟨T ∪ D, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.union_subset hTU (hDU.trans Finset.sdiff_subset), ?_⟩, Finset.subset_union_left⟩,
      Finset.union_sdiff_cancel_left hdisj⟩
    rw [Finset.card_union_of_disjoint hdisj, hDcard]; omega

private lemma choose_sub_mul_pow_le {B K s : ℕ} (hsK : s ≤ K) (hKB : K ≤ B) :
    (B - s).choose (K - s) * B ^ s ≤ B.choose K * K ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hid : (B - s) * (B - (s + 1)).choose (K - (s + 1)) =
        (B - s).choose (K - s) * (K - s) := by
      have h := Nat.add_one_mul_choose_eq (B - (s + 1)) (K - (s + 1))
      rwa [show B - (s + 1) + 1 = B - s by omega, show K - (s + 1) + 1 = K - s by omega] at h
    have hKB_sub : (K - s) * B ≤ K * (B - s) := by
      rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_comm s B]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_right s hKB) (K * B)
    have hstep : (B - (s + 1)).choose (K - (s + 1)) * B ≤ (B - s).choose (K - s) * K := by
      refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < B - s)
      calc
        (B - s) * ((B - (s + 1)).choose (K - (s + 1)) * B)
          = ((B - s) * (B - (s + 1)).choose (K - (s + 1))) * B := by ring
        _ = (B - s).choose (K - s) * ((K - s) * B) := by rw [hid]; ring
        _ ≤ (B - s).choose (K - s) * (K * (B - s)) := Nat.mul_le_mul_left _ hKB_sub
        _ = (B - s) * ((B - s).choose (K - s) * K) := by ring
    calc
      (B - (s + 1)).choose (K - (s + 1)) * B ^ (s + 1)
        = ((B - (s + 1)).choose (K - (s + 1)) * B) * B ^ s := by ring
      _ ≤ ((B - s).choose (K - s) * K) * B ^ s := Nat.mul_le_mul_right _ hstep
      _ = ((B - s).choose (K - s) * B ^ s) * K := by ring
      _ ≤ (B.choose K * K ^ s) * K := Nat.mul_le_mul_right _ (ih (Nat.le_of_succ_le hsK))
      _ = B.choose K * K ^ (s + 1) := by ring

private lemma cast_choose_sub_le {B K s : ℕ} (hB : 1 ≤ B) (hsK : s ≤ K) (hKB : K ≤ B) :
    ((B - s).choose (K - s) : ℝ) ≤ (B.choose K : ℝ) * ((K : ℝ) / (B : ℝ)) ^ s := by
  rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < B) s)]
  exact_mod_cast choose_sub_mul_pow_le hsK hKB

private lemma finset_prod_le_prod {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hf_a := hf a (Finset.mem_insert_self a s)
    have hfg_a := hfg a (Finset.mem_insert_self a s)
    have hf_s : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul hfg_a
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi)))
      hf_s (hf_a.trans hfg_a)

private lemma prod_le_mean_pow {W : Type*} [Fintype W] (hW : 1 ≤ Fintype.card W)
    (s : W → ℕ) (hs : ∀ w, 1 ≤ s w) :
    (∏ w : W, (s w : ℝ)) ≤ ((∑ w : W, (s w : ℝ)) / (Fintype.card W : ℝ)) ^ Fintype.card W := by
  let N := Fintype.card W
  have hNpos : (0 : ℝ) < N := by positivity
  let S : ℝ := ∑ w : W, (s w : ℝ)
  have hSpos : 0 < S := lt_of_lt_of_le hNpos <| by
    simpa [N, S] using Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) ↦
      (by exact_mod_cast hs w : (1 : ℝ) ≤ s w)
  let μ : ℝ := S / (N : ℝ)
  have hμpos : 0 < μ := div_pos hSpos hNpos
  have hprod_div : (∏ w : W, ((s w : ℝ) / μ)) ≤ 1 := by
    calc
      (∏ w : W, ((s w : ℝ) / μ))
        ≤ ∏ w : W, Real.exp ((s w : ℝ) / μ - 1) :=
          finset_prod_le_prod Finset.univ (fun _ _ ↦ by positivity) fun w _ ↦ by
            linarith [Real.add_one_le_exp ((s w : ℝ) / μ - 1)]
      _ = Real.exp (∑ w : W, ((s w : ℝ) / μ - 1)) := (Real.exp_sum Finset.univ _).symm
      _ = 1 := by
          have hSμ : S / μ = (N : ℝ) := by dsimp [μ]; field_simp [ne_of_gt hSpos]
          have hdiv_sum : (∑ w : W, (s w : ℝ) / μ) = S / μ := by
            dsimp [S]; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
          rw [Finset.sum_sub_distrib, hdiv_sum, hSμ]
          simp [N]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] at hprod_div
  exact (div_le_one (pow_pos hμpos N)).mp hprod_div

private lemma list_sum_filter_le {α : Type*} (L : List α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (p : α → Bool) : ((L.filter p).map f).sum ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases p a
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith [hf a]
    · simp only [↓reduceIte, List.map_cons, List.sum_cons]; linarith

private lemma list_sum_filter_add_neg {α : Type*} (L : List α) (f : α → ℝ) (p : α → Bool) :
    ((L.filter p).map f).sum + ((L.filter fun a ↦ !p a).map f).sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a tl ih => cases hp : p a <;> simp [hp, ← ih] <;> ring

private lemma list_sum_ite_eq_filter {α : Type*} (L : List α) (p : α → Bool) (f : α → ℝ) :
    (L.map fun a ↦ if p a then f a else 0).sum = ((L.filter p).map f).sum := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    cases p a
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, ih]
    · simp only [↓reduceIte, List.map_cons, List.sum_cons, ih]

private lemma list_sum_map_le_mul {α : Type*} (L : List α) (f g : α → ℝ) (C : ℝ)
    (h : ∀ r ∈ L, f r ≤ C * g r) : (L.map f).sum ≤ C * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons r tl ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add (h r List.mem_cons_self) (ih fun r' hr' ↦ h r' (List.mem_cons_of_mem r hr'))

private lemma wire_selector_bucket_split {α β : Type*} {N B K a b : ℕ}
    {t AliceCard BobCard : ℝ} (Active : List (Finset α × Finset β × Bool))
    (spread : Finset α × Finset β × Bool → ℕ)
    (hBpos : (0 : ℝ) < B) (hKpos : (0 : ℝ) < K) (hKB : K ≤ B)
    (hNpos : (0 : ℝ) < N) (ht : 1 ≤ t) (hApos : 0 < AliceCard) (hBob_pos : 0 < BobCard)
    (hYes : AliceCard * BobCard * ((K : ℝ) / (B : ℝ)) ^ N =
      (Active.map fun r ↦ (r.1.card : ℝ) * (r.2.1.card : ℝ)).sum)
    (hmnsw_snd : (Active.map fun r ↦ (r.2.1.card : ℝ)).sum ≤ (2 : ℝ) ^ a * BobCard)
    (hmnsw_fst : (Active.map fun r ↦ (r.1.card : ℝ)).sum ≤ (2 : ℝ) ^ b * AliceCard)
    (hA_bound : ∀ r ∈ Active, (r.1.card : ℝ) ≤ ((spread r : ℝ) / (N : ℝ)) ^ N)
    (hB_bound : ∀ r ∈ Active, (r.2.1.card : ℝ) ≤ BobCard * ((K : ℝ) / (B : ℝ)) ^ spread r) :
    AliceCard * ((K : ℝ) / (t * B)) ^ N ≤ (2 : ℝ) ^ (a + 1) ∨
      ((B : ℝ) / K) ^ ((t - 1) * (N : ℝ)) ≤ (2 : ℝ) ^ (b + 1) := by
  have htpos : 0 < t := by linarith
  let leafWeight : Finset α × Finset β × Bool → ℝ :=
    fun r ↦ (r.1.card : ℝ) * (r.2.1.card : ℝ)
  let smallPred : Finset α × Finset β × Bool → Bool :=
    fun r ↦ decide ((spread r : ℝ) ≤ t * (N : ℝ))
  let Bucket1 := Active.filter smallPred
  let Bucket2 := Active.filter fun r ↦ !smallPred r
  have hsplit : AliceCard * BobCard * ((K : ℝ) / (B : ℝ)) ^ N =
      (Bucket1.map leafWeight).sum + (Bucket2.map leafWeight).sum := by
    rw [hYes, ← list_sum_filter_add_neg Active leafWeight smallPred]
  have half_or : AliceCard * BobCard * ((K : ℝ) / (B : ℝ)) ^ N / 2 ≤
        (Bucket1.map leafWeight).sum ∨
      AliceCard * BobCard * ((K : ℝ) / (B : ℝ)) ^ N / 2 ≤
        (Bucket2.map leafWeight).sum := by
    by_contra h; push Not at h; linarith [h.1, h.2, hsplit]
  rcases half_or with hB1_half | hB2_half
  · left
    have hsum1 : (Bucket1.map leafWeight).sum ≤
        t ^ N * (Bucket1.map fun r ↦ (r.2.1.card : ℝ)).sum :=
      list_sum_map_le_mul Bucket1 leafWeight (fun r ↦ (r.2.1.card : ℝ)) (t ^ N) fun r hr ↦ by
        rcases List.mem_filter.mp hr with ⟨hrAct, hsm⟩
        have hdiv : (spread r : ℝ) / (N : ℝ) ≤ t :=
          (div_le_iff₀ hNpos).mpr (decide_eq_true_iff.mp hsm)
        exact mul_le_mul_of_nonneg_right
          ((hA_bound r hrAct).trans
            (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hNpos.le) hdiv N))
          (Nat.cast_nonneg _)
    have hmnsw1 : (Bucket1.map fun r ↦ (r.2.1.card : ℝ)).sum ≤ (2 : ℝ) ^ a * BobCard :=
      (list_sum_filter_le Active _ (fun _ ↦ Nat.cast_nonneg _) smallPred).trans hmnsw_snd
    have hineq := hB1_half.trans
      (hsum1.trans (mul_le_mul_of_nonneg_left hmnsw1 (pow_nonneg htpos.le N)))
    have hcancel_bob : AliceCard * ((K : ℝ) / (B : ℝ)) ^ N ≤ t ^ N * (2 : ℝ) ^ (a + 1) := by
      refine le_of_mul_le_mul_right ?_ hBob_pos
      rw [pow_succ]; linarith
    have hlhs : AliceCard * ((K : ℝ) / (t * (B : ℝ))) ^ N =
        AliceCard * ((K : ℝ) / (B : ℝ)) ^ N / t ^ N := by
      rw [mul_div_assoc, ← div_pow]; congr 2; ring
    rw [hlhs, div_le_iff₀ (pow_pos htpos N)]; linarith
  · right
    let q : ℝ := (K : ℝ) / (B : ℝ)
    have hq_pos : 0 < q := div_pos hKpos hBpos
    have hq_le1 : q ≤ 1 := (div_le_one hBpos).mpr (by exact_mod_cast hKB)
    have hsum2 : (Bucket2.map leafWeight).sum ≤
        (BobCard * q ^ (t * (N : ℝ))) * (Bucket2.map fun r ↦ (r.1.card : ℝ)).sum :=
      list_sum_map_le_mul Bucket2 leafWeight (fun r ↦ (r.1.card : ℝ))
        (BobCard * q ^ (t * (N : ℝ))) fun r hr ↦ by
        rcases List.mem_filter.mp hr with ⟨hrAct, hnsm⟩
        have hgt : t * (N : ℝ) < (spread r : ℝ) := by simpa [smallPred] using hnsm
        have hpow_le : q ^ spread r ≤ q ^ (t * (N : ℝ)) := by
          rw [← Real.rpow_natCast q (spread r)]
          exact Real.rpow_le_rpow_of_exponent_ge hq_pos hq_le1 hgt.le
        have hBle := (hB_bound r hrAct).trans (mul_le_mul_of_nonneg_left hpow_le hBob_pos.le)
        exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right hBle (Nat.cast_nonneg _))
    have hmnsw2 : (Bucket2.map fun r ↦ (r.1.card : ℝ)).sum ≤ (2 : ℝ) ^ b * AliceCard :=
      (list_sum_filter_le Active _ (fun _ ↦ Nat.cast_nonneg _) _).trans hmnsw_fst
    have hineq := hB2_half.trans (hsum2.trans
      (mul_le_mul_of_nonneg_left hmnsw2 (mul_nonneg hBob_pos.le (Real.rpow_nonneg hq_pos.le _))))
    have hq_ineq : q ^ N ≤ q ^ (t * (N : ℝ)) * (2 : ℝ) ^ (b + 1) := by
      refine le_of_mul_le_mul_right ?_ (mul_pos hApos hBob_pos)
      change ((K : ℝ) / (B : ℝ)) ^ N * (AliceCard * BobCard) ≤ _
      rw [pow_succ]; linarith
    let p : ℝ := (B : ℝ) / (K : ℝ)
    have hp_pos : 0 < p := div_pos hBpos hKpos
    have hqp : q * p = 1 := by dsimp [q, p]; field_simp [ne_of_gt hKpos, ne_of_gt hBpos]
    have hcancel_q : q ^ (t * (N : ℝ)) * p ^ (t * (N : ℝ)) = 1 := by
      rw [← Real.mul_rpow hq_pos.le hp_pos.le, hqp, Real.one_rpow]
    have hlhs_eq : q ^ N * p ^ (t * (N : ℝ)) = p ^ ((t - 1) * (N : ℝ)) := by
      have hq_inv : q ^ N = p ^ (-(N : ℝ)) := by
        rw [show q = p⁻¹ by dsimp [q, p]; rw [inv_div], ← Real.rpow_natCast p⁻¹ N,
          Real.inv_rpow hp_pos.le, ← Real.rpow_neg hp_pos.le]
      rw [hq_inv, ← Real.rpow_add hp_pos]; congr 1; ring
    calc
      p ^ ((t - 1) * (N : ℝ)) = q ^ N * p ^ (t * (N : ℝ)) := hlhs_eq.symm
      _ ≤ (q ^ (t * (N : ℝ)) * (2 : ℝ) ^ (b + 1)) * p ^ (t * (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hq_ineq (Real.rpow_nonneg hp_pos.le _)
      _ = (q ^ (t * (N : ℝ)) * p ^ (t * (N : ℝ))) * (2 : ℝ) ^ (b + 1) := by ring
      _ = (2 : ℝ) ^ (b + 1) := by rw [hcancel_q, one_mul]

/-- **Master Wire-Selector Two-Bucket Rectangle Lower Bound**: for any finite wire set `W` with
`N = |W| ≥ 1`, integers `1 ≤ K ≤ B`, real threshold `t ≥ 1`, nonempty finite family `AliceFam`
with an injective wire selector `sel : α → (W → Fin B)`, and deterministic protocol `P` computing
wire-graph disjointness on `AliceFam × Finset (W × Fin B)`, either
`|AliceFam| (K / (t B))^N ≤ 2 ^ (aliceCost P + 1)` or `(B / K)^((t - 1) N) ≤ 2 ^ (bobCost P + 1)`.
-/
theorem wire_selector_lsd_lower_bound {W α : Type*} [Fintype W] [DecidableEq W]
    {B K : ℕ} {t : ℝ} {AliceFam : Finset α} (hAlice : AliceFam.Nonempty)
    {sel : α → W → Fin B} (hsel : Function.Injective sel)
    (hK1 : 1 ≤ K) (hKB : K ≤ B) (hW : 1 ≤ Fintype.card W) (ht : 1 ≤ t)
    {P : Protocol α (Finset (W × Fin B)) Bool}
    (hP : ∀ x ∈ AliceFam, ∀ Y : Finset (W × Fin B),
      P.run x Y = decide (Disjoint (Finset.univ.image fun w ↦ (w, sel x w)) Y)) :
    (AliceFam.card : ℝ) * ((K : ℝ) / (t * B)) ^ Fintype.card W ≤
        (2 : ℝ) ^ (aliceCost P + 1) ∨
      ((B : ℝ) / K) ^ ((t - 1) * (Fintype.card W : ℝ)) ≤ (2 : ℝ) ^ (bobCost P + 1) := by
  classical
  let N := Fintype.card W
  have hB1 : 1 ≤ B := hK1.trans hKB
  have hBpos : (0 : ℝ) < B := by positivity
  have hKpos : (0 : ℝ) < K := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have htpos : 0 < t := by linarith
  have hApos : (0 : ℝ) < AliceFam.card := by exact_mod_cast hAlice.card_pos
  -- Step 1: Construct Bob's block-complement family `BobFam` and count disjoint pairs `YesPairs`.
  let KSub : Finset (Finset (Fin B)) := (Finset.univ : Finset (Fin B)).powersetCard K
  let ZFam : Finset (W → Finset (Fin B)) := Fintype.piFinset fun _ : W ↦ KSub
  let bobSet : (W → Finset (Fin B)) → Finset (W × Fin B) :=
    fun Z ↦ Finset.univ.filter fun p ↦ p.2 ∉ Z p.1
  have hbobSet_inj : Set.InjOn bobSet (ZFam : Set (W → Finset (Fin B))) := by
    intro Z₁ _ Z₂ _ heq; ext w b
    have hmem : (w, b) ∈ bobSet Z₁ ↔ (w, b) ∈ bobSet Z₂ := by rw [heq]
    simpa [bobSet] using hmem.not
  let BobFam : Finset (Finset (W × Fin B)) := ZFam.image bobSet
  have hBob_card : BobFam.card = B.choose K ^ N := by
    rw [Finset.card_image_of_injOn hbobSet_inj]
    dsimp only [ZFam, KSub, N]
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  have hBob_pos : (0 : ℝ) < BobFam.card := by
    rw [hBob_card]; have := Nat.choose_pos hKB; positivity
  have hdisj_bobSet : ∀ (x : α) (Z : W → Finset (Fin B)),
      Disjoint (Finset.univ.image fun w ↦ (w, sel x w)) (bobSet Z) ↔ ∀ w, sel x w ∈ Z w := by
    intro x Z; rw [Finset.disjoint_left]; constructor
    · intro hd w; simpa [bobSet] using hd (Finset.mem_image_of_mem _ (Finset.mem_univ w))
    · rintro hall _ hw; rcases Finset.mem_image.mp hw with ⟨w, _, rfl⟩; simp [bobSet, hall w]
  have hZ_pi : ∀ T : W → Finset (Fin B), (ZFam.filter fun Z ↦ ∀ w, T w ⊆ Z w) =
      Fintype.piFinset fun w ↦ KSub.filter fun S ↦ T w ⊆ S := fun T ↦ by
    ext Z; simp only [ZFam, Finset.mem_filter, Fintype.mem_piFinset]; exact forall_and.symm
  let YesPairs := (AliceFam ×ˢ BobFam).filter fun p ↦ P.run p.1 p.2
  have hYes_card_x : ∀ x ∈ AliceFam,
      (BobFam.filter fun Y ↦ P.run x Y).card = ((B - 1).choose (K - 1)) ^ N := by
    intro x hx
    have himg : BobFam.filter (fun Y ↦ P.run x Y) =
        (ZFam.filter fun Z ↦ ∀ w, {sel x w} ⊆ Z w).image bobSet := by
      ext Y; simp only [BobFam, Finset.mem_filter, Finset.mem_image, Finset.singleton_subset_iff]
      constructor
      · rintro ⟨⟨Z, hZ, rfl⟩, hev⟩
        rw [hP x hx, decide_eq_true_eq, hdisj_bobSet] at hev; exact ⟨Z, ⟨hZ, hev⟩, rfl⟩
      · rintro ⟨Z, ⟨hZ, hall⟩, rfl⟩
        refine ⟨⟨Z, hZ, rfl⟩, ?_⟩; rw [hP x hx, decide_eq_true_eq, hdisj_bobSet]; exact hall
    rw [himg, Finset.card_image_of_injOn (hbobSet_inj.mono (Finset.coe_subset.mpr
      (Finset.filter_subset _ ZFam))), hZ_pi, Fintype.card_piFinset]
    have hcoord : ∀ w : W, (KSub.filter fun S ↦ {sel x w} ⊆ S).card =
        (B - 1).choose (K - 1) := fun w ↦ by
      simpa [KSub] using card_powersetCard_filter_subset (Finset.univ : Finset (Fin B))
        {sel x w} (Finset.subset_univ _) (by simpa using hK1)
    rw [Finset.prod_congr rfl fun w _ ↦ hcoord w, Finset.prod_const, Finset.card_univ]
  have hYes_real : (YesPairs.card : ℝ) =
      (AliceFam.card : ℝ) * (BobFam.card : ℝ) * ((K : ℝ) / (B : ℝ)) ^ N := by
    have hbi : YesPairs = AliceFam.biUnion fun x ↦ {x} ×ˢ (BobFam.filter fun Y ↦ P.run x Y) := by
      ext ⟨x, Y⟩; simp [YesPairs]; tauto
    have hdisj : (AliceFam : Set α).PairwiseDisjoint
        (fun x ↦ {x} ×ˢ (BobFam.filter fun Y ↦ P.run x Y)) := fun x₁ _ x₂ _ hne ↦
      Finset.disjoint_left.mpr fun p h₁ h₂ ↦ hne <|
        (Finset.mem_singleton.mp (Finset.mem_product.mp h₁).1).symm.trans
          (Finset.mem_singleton.mp (Finset.mem_product.mp h₂).1)
    have hnat : YesPairs.card = AliceFam.card * ((B - 1).choose (K - 1)) ^ N := by
      rw [hbi, Finset.card_biUnion hdisj]
      simp only [Finset.card_product, Finset.card_singleton, one_mul]
      rw [Finset.sum_congr rfl hYes_card_x, Finset.sum_const, smul_eq_mul]
    have hch : ((B - 1).choose (K - 1) : ℝ) = (B.choose K : ℝ) * ((K : ℝ) / (B : ℝ)) := by
      have hid := Nat.add_one_mul_choose_eq (B - 1) (K - 1)
      rw [show B - 1 + 1 = B by omega, show K - 1 + 1 = K by omega] at hid
      have hidR : (B : ℝ) * ((B - 1).choose (K - 1) : ℝ) = (B.choose K : ℝ) * (K : ℝ) := by
        exact_mod_cast hid
      rw [mul_div_assoc', eq_div_iff (ne_of_gt hBpos)]; linarith
    rw [hnat, Nat.cast_mul, Nat.cast_pow, hch, mul_pow, hBob_card, Nat.cast_pow]; ring
  -- Step 2: Partition `YesPairs` across active `true`-leaves and bound `|A_ℓ|` and `|B_ℓ|`.
  let L := leavesFrom P AliceFam BobFam
  let leafWeight : Finset α × Finset (Finset (W × Fin B)) × Bool → ℝ :=
    fun r ↦ (r.1.card : ℝ) * (r.2.1.card : ℝ)
  let isActive : Finset α × Finset (Finset (W × Fin B)) × Bool → Bool :=
    fun r ↦ r.2.2 && decide (0 < r.1.card)
  let Active := L.filter isActive
  have hActive_mem : ∀ {r}, r ∈ Active → r ∈ L ∧ r.2.2 = true ∧ 0 < r.1.card := fun hr ↦ by
    rcases List.mem_filter.mp hr with ⟨hrL, hact⟩
    simp only [isActive, Bool.and_eq_true, decide_eq_true_eq] at hact
    exact ⟨hrL, hact.1, hact.2⟩
  have hYes_eq_Active : (YesPairs.card : ℝ) = (Active.map leafWeight).sum := by
    have hpart := card_filter_product_eq_sum_leavesFrom P AliceFam BobFam (fun x Y ↦ P.run x Y)
    have hterm : ∀ r ∈ L,
        ((((r.1 ×ˢ r.2.1).filter fun p ↦ P.run p.1 p.2).card : ℕ) : ℝ) =
          if isActive r then leafWeight r else 0 := by
      rintro ⟨A, B_rect, z⟩ hrL
      obtain ⟨_, _, heval⟩ := mem_leavesFrom_subset_and_run hrL
      split_ifs with hact
      · simp only [isActive, Bool.and_eq_true, decide_eq_true_eq] at hact
        have hfull : ((A ×ˢ B_rect).filter fun p ↦ P.run p.1 p.2) = A ×ˢ B_rect :=
          Finset.filter_eq_self.mpr fun ⟨x, Y⟩ hp ↦ by
            rcases Finset.mem_product.mp hp with ⟨hx, hY⟩
            rw [heval x hx Y hY, hact.1]
        rw [hfull, Finset.card_product, Nat.cast_mul]
      · simp only [isActive, Bool.and_eq_true, decide_eq_true_eq, not_and_or] at hact
        rcases hact with hz | hA0
        · have hz_f : z = false := Bool.eq_false_iff.mpr hz
          have hemp : ((A ×ˢ B_rect).filter fun p ↦ P.run p.1 p.2) = ∅ :=
            Finset.filter_eq_empty_iff.mpr fun ⟨x, Y⟩ hp ↦ by
              rcases Finset.mem_product.mp hp with ⟨hx, hY⟩
              rw [heval x hx Y hY, hz_f]; exact Bool.false_ne_true
          rw [hemp, Finset.card_empty, Nat.cast_zero]
        · have hAemp : A = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hA0)
          dsimp only
          rw [hAemp, Finset.empty_product, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    have hcast : (YesPairs.card : ℝ) =
        (L.map fun r ↦ ((((r.1 ×ˢ r.2.1).filter fun p ↦ P.run p.1 p.2).card : ℕ) : ℝ)).sum := by
      rw [show YesPairs = (AliceFam ×ˢ BobFam).filter (fun p ↦ P.run p.1 p.2) from rfl, hpart,
        Nat.cast_list_sum, List.map_map]
      rfl
    rw [hcast, congr_arg List.sum (List.map_congr_left hterm), list_sum_ite_eq_filter]
  let spread : Finset α × Finset (Finset (W × Fin B)) × Bool → ℕ :=
    fun r ↦ ∑ w : W, (r.1.image fun x ↦ sel x w).card
  have hA_bound : ∀ r ∈ Active, (r.1.card : ℝ) ≤ ((spread r : ℝ) / (N : ℝ)) ^ N := by
    intro r hr
    obtain ⟨_, _, hApos_r⟩ := hActive_mem hr
    let Tw : W → Finset (Fin B) := fun w ↦ r.1.image fun x ↦ sel x w
    have hs1 : ∀ w, 1 ≤ (Tw w).card := fun w ↦
      Finset.card_pos.mpr ((Finset.card_pos.mp hApos_r).image _)
    have hinj_pi : r.1.image sel ⊆ Fintype.piFinset Tw := fun f hf ↦ by
      rcases Finset.mem_image.mp hf with ⟨x, hx, rfl⟩
      exact Fintype.mem_piFinset.mpr fun w ↦ Finset.mem_image_of_mem _ hx
    have hA_nat : r.1.card ≤ ∏ w, (Tw w).card := by
      rw [← Finset.card_image_of_injective r.1 hsel, ← Fintype.card_piFinset]
      exact Finset.card_le_card hinj_pi
    have hA_real : (r.1.card : ℝ) ≤ ∏ w, ((Tw w).card : ℝ) := by exact_mod_cast hA_nat
    exact hA_real.trans
      (by simpa [spread, Tw, N] using prod_le_mean_pow hW (fun w ↦ (Tw w).card) hs1)
  have hB_bound : ∀ r ∈ Active,
      (r.2.1.card : ℝ) ≤ (BobFam.card : ℝ) * ((K : ℝ) / (B : ℝ)) ^ spread r := by
    rintro ⟨A, B_rect, z⟩ hr
    obtain ⟨hrL, rfl, _⟩ := hActive_mem hr
    obtain ⟨hA_sub, hB_sub, heval⟩ := mem_leavesFrom_subset_and_run hrL
    let Tw : W → Finset (Fin B) := fun w ↦ A.image fun x ↦ sel x w
    by_cases hall_le : ∀ w, (Tw w).card ≤ K
    · have hB_sub_img : B_rect ⊆ (ZFam.filter fun Z ↦ ∀ w, Tw w ⊆ Z w).image bobSet := by
        intro Y hY
        rcases Finset.mem_image.mp (hB_sub hY) with ⟨Z, hZ, rfl⟩
        refine Finset.mem_image.mpr ⟨Z, Finset.mem_filter.mpr ⟨hZ, fun w b hb ↦ ?_⟩, rfl⟩
        rcases Finset.mem_image.mp hb with ⟨x, hxA, rfl⟩
        have hev := heval x hxA (bobSet Z) hY
        rw [hP x (hA_sub hxA), decide_eq_true_eq, hdisj_bobSet] at hev; exact hev w
      have hB_nat : B_rect.card ≤ ∏ w, (B - (Tw w).card).choose (K - (Tw w).card) := by
        calc
          B_rect.card ≤ ((ZFam.filter fun Z ↦ ∀ w, Tw w ⊆ Z w).image bobSet).card :=
              Finset.card_le_card hB_sub_img
          _ = ∏ w, (KSub.filter fun S ↦ Tw w ⊆ S).card := by
              rw [Finset.card_image_of_injOn (hbobSet_inj.mono (Finset.coe_subset.mpr
                (Finset.filter_subset _ ZFam))), hZ_pi, Fintype.card_piFinset]
          _ = ∏ w, (B - (Tw w).card).choose (K - (Tw w).card) := Finset.prod_congr rfl fun w _ ↦ by
              simpa [KSub] using card_powersetCard_filter_subset
                (Finset.univ : Finset (Fin B)) (Tw w) (Finset.subset_univ _) (hall_le w)
      have hB_real : (B_rect.card : ℝ) ≤
          ∏ w, (((B - (Tw w).card).choose (K - (Tw w).card) : ℕ) : ℝ) := by exact_mod_cast hB_nat
      refine hB_real.trans ?_
      calc
        (∏ w, (((B - (Tw w).card).choose (K - (Tw w).card) : ℕ) : ℝ))
          ≤ ∏ w, ((B.choose K : ℝ) * ((K : ℝ) / (B : ℝ)) ^ (Tw w).card) :=
            finset_prod_le_prod Finset.univ (fun _ _ ↦ by positivity) fun w _ ↦
              cast_choose_sub_le hB1 (hall_le w) hKB
        _ = (BobFam.card : ℝ) * ((K : ℝ) / (B : ℝ)) ^ spread (A, B_rect, true) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
              Finset.prod_pow_eq_pow_sum, hBob_card, Nat.cast_pow]
    · push Not at hall_le; rcases hall_le with ⟨w₀, hw₀⟩
      have hB_emp : B_rect = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun Y hY ↦ by
        rcases Finset.mem_image.mp (hB_sub hY) with ⟨Z, hZ, rfl⟩
        have hTw_sub : Tw w₀ ⊆ Z w₀ := fun b hb ↦ by
          rcases Finset.mem_image.mp hb with ⟨x, hxA, rfl⟩
          have hev := heval x hxA (bobSet Z) hY
          rw [hP x (hA_sub hxA), decide_eq_true_eq, hdisj_bobSet] at hev; exact hev w₀
        have hZcard : (Z w₀).card = K :=
          (Finset.mem_powersetCard.mp ((Fintype.mem_piFinset.mp hZ) w₀)).2
        have := hZcard ▸ Finset.card_le_card hTw_sub; omega
      rw [hB_emp, Finset.card_empty, Nat.cast_zero]; positivity
  -- Step 3: Invoke the generic two-bucket MNSW leaf-splitting lemma.
  have hmnsw_snd : (Active.map fun r ↦ (r.2.1.card : ℝ)).sum ≤
      (2 : ℝ) ^ aliceCost P * (BobFam.card : ℝ) := by
    refine (list_sum_filter_le L _ (fun _ ↦ Nat.cast_nonneg _) isActive).trans ?_
    have hcast : (((L.map fun r ↦ r.2.1.card).sum : ℕ) : ℝ) ≤
        (2 : ℝ) ^ aliceCost P * (BobFam.card : ℝ) := by
      exact_mod_cast sum_card_snd_leavesFrom_le P AliceFam BobFam
    simpa [List.map_map, Function.comp_def] using hcast
  have hmnsw_fst : (Active.map fun r ↦ (r.1.card : ℝ)).sum ≤
      (2 : ℝ) ^ bobCost P * (AliceFam.card : ℝ) := by
    refine (list_sum_filter_le L _ (fun _ ↦ Nat.cast_nonneg _) isActive).trans ?_
    have hcast : (((L.map fun r ↦ r.1.card).sum : ℕ) : ℝ) ≤
        (2 : ℝ) ^ bobCost P * (AliceFam.card : ℝ) := by
      exact_mod_cast sum_card_fst_leavesFrom_le P AliceFam BobFam
    simpa [List.map_map, Function.comp_def] using hcast
  exact wire_selector_bucket_split Active spread hBpos hKpos hKB hNpos ht hApos hBob_pos
    (hYes_real.symm.trans hYes_eq_Active) hmnsw_snd hmnsw_fst hA_bound hB_bound

end MasterWireSelector

/-! ### 3. Blocked LSD and Switch-Permutation LSD Lower Bounds -/

section LopsidedSetDisjointness

/-- Alice's input space `Fin N → Fin B` for Blocked Lopsided Set Disjointness, selecting one
element per block across `N` blocks of size `B`. -/
abbrev BlockedAlice (N B : ℕ) : Type := Fin N → Fin B

/-- Blocked Lopsided Set Disjointness $\mathsf{BLSD}_{N, B}$, testing whether Alice's block
selector graph `{(i, x i) | i : Fin N}` is disjoint from Bob's subset `Y ⊆ Fin N × Fin B`. -/
def blockedDisjoint (N B : ℕ) (x : BlockedAlice N B) (Y : Finset (Fin N × Fin B)) :
    Bool :=
  decide (Disjoint (Finset.univ.image fun i : Fin N ↦ (i, x i)) Y)

/-- `blockedDisjoint N B x Y` evaluates to `true` iff Alice's block-selector graph is disjoint
from `Y`. -/
theorem blockedDisjoint_eq_true_iff {N B : ℕ} {x : BlockedAlice N B}
    {Y : Finset (Fin N × Fin B)} :
    blockedDisjoint N B x Y = true ↔
      Disjoint (Finset.univ.image fun i : Fin N ↦ (i, x i)) Y := by
  exact decide_eq_true_iff

/-- **Master Asymmetric Rectangle Bound for Blocked Lopsided Set Disjointness**: for `1 ≤ K ≤ B`,
`1 ≤ N`, and `t ≥ 1`, any deterministic protocol `P` computing `blockedDisjoint N B` satisfies
`(K / t)^N ≤ 2 ^ (aliceCost P + 1)` or `(B / K)^((t - 1) N) ≤ 2 ^ (bobCost P + 1)`. -/
theorem blocked_lsd_master_lower_bound {N B K : ℕ} {t : ℝ}
    (hK1 : 1 ≤ K) (hKB : K ≤ B) (hN : 1 ≤ N) (ht : 1 ≤ t)
    {P : Protocol (BlockedAlice N B) (Finset (Fin N × Fin B)) Bool}
    (hP : P.run = blockedDisjoint N B) :
    ((K : ℝ) / t) ^ N ≤ (2 : ℝ) ^ (aliceCost P + 1) ∨
      ((B : ℝ) / K) ^ ((t - 1) * (N : ℝ)) ≤ (2 : ℝ) ^ (bobCost P + 1) := by
  have hB1 : 1 ≤ B := hK1.trans hKB
  have hBne : (B : ℝ) ≠ 0 := by positivity
  have hne : (Finset.univ : Finset (BlockedAlice N B)).Nonempty :=
    Finset.card_pos.mp (by
      simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_const]
      exact Nat.pow_pos hB1)
  have hmaster := wire_selector_lsd_lower_bound (W := Fin N) hne Function.injective_id hK1 hKB
    (by simpa using hN) ht (fun x _ Y ↦ congrFun₂ hP x Y)
  simp only [Fintype.card_fin, Finset.card_univ, Fintype.card_fun, Nat.cast_pow] at hmaster
  refine hmaster.imp (fun h1 ↦ ?_) id
  have heq : (B : ℝ) ^ N * ((K : ℝ) / (t * (B : ℝ))) ^ N = ((K : ℝ) / t) ^ N := by
    rw [← mul_pow]; congr 1; field_simp [hBne]
  rwa [heq] at h1

private lemma logb_four_pow_alice_bound {N B a : ℕ} {u : ℝ} (hB : 1 ≤ B)
    (hr : Real.sqrt (Real.sqrt B) ≤ u) (hpow : u ^ N ≤ (2 : ℝ) ^ (a + 1)) :
    (N : ℝ) * Real.logb 2 B / 4 ≤ (a : ℝ) + 1 := by
  let r := Real.sqrt (Real.sqrt B)
  have hr4 : r ^ 4 = (B : ℝ) := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (Real.sqrt B) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = (B : ℝ) := Real.sq_sqrt (by positivity)
  have hrN : r ^ N ≤ (2 : ℝ) ^ (a + 1) :=
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) hr N).trans hpow
  have hB_pow : (B : ℝ) ^ N ≤ (2 : ℝ) ^ (4 * (a + 1)) := by
    calc
      (B : ℝ) ^ N = (r ^ N) ^ 4 := by rw [← hr4]; ring
      _ ≤ ((2 : ℝ) ^ (a + 1)) ^ 4 := pow_le_pow_left₀ (by positivity) hrN 4
      _ = (2 : ℝ) ^ (4 * (a + 1)) := by rw [← pow_mul, mul_comm]
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (B : ℝ) ^ N) hB_pow
  rw [Real.logb_pow, ← Real.rpow_natCast (2 : ℝ) (4 * (a + 1)),
    Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  push_cast at hlog; linarith

private lemma sqrt_bob_bound_of_rpow {N B b : ℕ} (hB : 64 ≤ B)
    (hpow : ((B : ℝ) / ((B / 2 : ℕ) : ℝ)) ^ ((Real.sqrt B - 1) * (N : ℝ)) ≤
      (2 : ℝ) ^ (b + 1)) :
    (N : ℝ) * Real.sqrt B / 2 ≤ (b : ℝ) + 1 := by
  let K : ℕ := B / 2
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by dsimp [K]; omega : 0 < K)
  have h2le : (2 : ℝ) ≤ (B : ℝ) / (K : ℝ) :=
    (le_div_iff₀ hKpos).mpr (by exact_mod_cast Nat.mul_div_le B 2)
  have hsqrt8 : (8 : ℝ) ≤ Real.sqrt B := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
    exact Real.sqrt_le_sqrt (by norm_num; exact_mod_cast hB)
  have hexp_le : (N : ℝ) * Real.sqrt B / 2 ≤ (Real.sqrt B - 1) * (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right (by linarith : Real.sqrt B / 2 ≤ Real.sqrt B - 1)
      (by positivity : (0 : ℝ) ≤ N)
    linarith
  have hexp_nn : 0 ≤ (Real.sqrt B - 1) * (N : ℝ) :=
    (by positivity : 0 ≤ (N : ℝ) * Real.sqrt B / 2).trans hexp_le
  have h2pow : (2 : ℝ) ^ ((N : ℝ) * Real.sqrt B / 2) ≤ (2 : ℝ) ^ ((b : ℝ) + 1) := by
    calc
      (2 : ℝ) ^ ((N : ℝ) * Real.sqrt B / 2)
        ≤ (2 : ℝ) ^ ((Real.sqrt B - 1) * (N : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      _ ≤ ((B : ℝ) / (K : ℝ)) ^ ((Real.sqrt B - 1) * (N : ℝ)) :=
          Real.rpow_le_rpow (by norm_num) h2le hexp_nn
      _ ≤ (2 : ℝ) ^ (b + 1) := hpow
      _ = (2 : ℝ) ^ ((b : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h2pow

/-- **Concrete Square-Root Lower Bound for Blocked Lopsided Set Disjointness**: for `B ≥ 64` and
`N ≥ 1`, every deterministic protocol `P` computing `blockedDisjoint N B` satisfies either
`N * log₂ B / 4 ≤ aliceCost P + 1` or `N * √B / 2 ≤ bobCost P + 1`. -/
theorem blocked_lsd_sqrt_lower_bound {N B : ℕ} (hB : 64 ≤ B) (hN : 1 ≤ N)
    {P : Protocol (BlockedAlice N B) (Finset (Fin N × Fin B)) Bool}
    (hP : P.run = blockedDisjoint N B) :
    (N : ℝ) * Real.logb 2 B / 4 ≤ (aliceCost P : ℝ) + 1 ∨
      (N : ℝ) * Real.sqrt B / 2 ≤ (bobCost P : ℝ) + 1 := by
  let K : ℕ := B / 2
  have ht1 : (1 : ℝ) ≤ Real.sqrt B := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ B))
  rcases blocked_lsd_master_lower_bound (K := K) (by omega) (Nat.div_le_self B 2) hN ht1 hP with
    hA | hB_side
  · left
    let r := Real.sqrt (Real.sqrt B)
    have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = Real.sqrt B := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hr4 : r ^ 4 = (B : ℝ) := by
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = (B : ℝ) := by rw [hr2]; exact Real.sq_sqrt (by positivity)
    have hr_ge : (9 / 4 : ℝ) ≤ r := by
      by_contra hlt; push Not at hlt
      have hpow4 : r ^ 4 < (9 / 4 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hr_nn (by omega)
      have hB64 : (64 : ℝ) ≤ B := by exact_mod_cast hB
      rw [hr4] at hpow4; norm_num at hpow4; linarith
    have h4B : (4 : ℝ) * (B : ℝ) ≤ 9 * (K : ℝ) := by
      exact_mod_cast (by omega : 4 * B ≤ 9 * (B / 2))
    have hr_le : r ≤ (K : ℝ) / Real.sqrt B := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < B)), ← hr2]
      have : 0 ≤ r ^ 3 := pow_nonneg hr_nn 3
      nlinarith [hr4, h4B]
    exact logb_four_pow_alice_bound (by omega) hr_le hA
  · exact Or.inr (sqrt_bob_bound_of_rpow hB hB_side)

/-- **Pătrașcu's General-`δ` Blocked Lopsided Set Disjointness Lower Bound**: for every real `δ`
with `0 < δ ≤ 1 / 8`, there exists `B₀ : ℕ` such that for all `B ≥ B₀` and `N ≥ 1`, every
deterministic protocol `P` computing `blockedDisjoint N B` satisfies either
`δ * N * log₂ B ≤ aliceCost P` or `N * B ^ (1 - 4 * δ) ≤ bobCost P`. -/
theorem blocked_lsd_lower_bound {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 8) :
    ∃ B₀ : ℕ, ∀ ⦃B N : ℕ⦄, B₀ ≤ B → 1 ≤ N →
      ∀ ⦃P : Protocol (BlockedAlice N B) (Finset (Fin N × Fin B)) Bool⦄,
        P.run = blockedDisjoint N B →
        δ * (N : ℝ) * Real.logb 2 B ≤ (aliceCost P : ℝ) ∨
          (N : ℝ) * (B : ℝ) ^ (1 - 4 * δ) ≤ (bobCost P : ℝ) := by
  let m : ℕ := Nat.ceil (2 / δ)
  refine ⟨max 4 (2 ^ (2 * m)), fun {B N} hB hN {P} hP ↦ ?_⟩
  have hB4 : 4 ≤ B := (le_max_left 4 _).trans hB
  have hB_pow2 : 2 ^ (2 * m) ≤ B := (le_max_right 4 _).trans hB
  have hBpos : (0 : ℝ) < B := by positivity
  have hB1_real : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have h2mδ : (4 : ℝ) ≤ (2 * m : ℝ) * δ := by
    have hmδ : 2 ≤ (m : ℝ) * δ := (div_le_iff₀ hδ_pos).mp (Nat.le_ceil (2 / δ))
    linarith
  have hBδ_ge16 : (16 : ℝ) ≤ (B : ℝ) ^ δ := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((2 * m : ℝ) * δ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2mδ
      _ = ((2 : ℝ) ^ (2 * m)) ^ δ := by
          rw [Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) (2 * m)]; push_cast; rfl
      _ ≤ (B : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hB_pow2) hδ_pos.le
  let K : ℕ := B / 2
  let t : ℝ := (B : ℝ) ^ (1 - 3 * δ)
  have ht1 : 1 ≤ t := Real.one_le_rpow hB1_real (by linarith)
  rcases blocked_lsd_master_lower_bound (K := K) (by omega) (Nat.div_le_self B 2) hN ht1 hP with
    hA | hB_side
  · left
    have hK_ge : (B : ℝ) / 4 ≤ (K : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      exact_mod_cast (by dsimp [K]; omega : B ≤ K * 4)
    have ht_pos : 0 < t := Real.rpow_pos_of_pos hBpos _
    have hB_split : (B : ℝ) = t * (B : ℝ) ^ (2 * δ) * (B : ℝ) ^ δ := by
      dsimp [t]; rw [← Real.rpow_add hBpos, ← Real.rpow_add hBpos]
      rw [show 1 - 3 * δ + 2 * δ + δ = 1 by ring, Real.rpow_one]
    have hB2δ_ge8 : (8 : ℝ) ≤ (B : ℝ) ^ (2 * δ) := by
      have hsq : ((B : ℝ) ^ δ) ^ (2 : ℝ) = (B : ℝ) ^ (2 * δ) := by
        rw [← Real.rpow_mul hBpos.le, mul_comm]
      rw [← hsq, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
    have hKt_ge : 2 * (B : ℝ) ^ δ ≤ (K : ℝ) / t := by
      rw [le_div_iff₀ ht_pos]
      have hBδ_pos : 0 < (B : ℝ) ^ δ := Real.rpow_pos_of_pos hBpos δ
      have h1 : 8 * t * (B : ℝ) ^ δ ≤ (B : ℝ) := by
        calc
          8 * t * (B : ℝ) ^ δ = t * 8 * (B : ℝ) ^ δ := by ring
          _ ≤ t * (B : ℝ) ^ (2 * δ) * (B : ℝ) ^ δ := by nlinarith [mul_pos ht_pos hBδ_pos]
          _ = (B : ℝ) := hB_split.symm
      linarith
    have hpow_ge : 2 * ((B : ℝ) ^ δ) ^ N ≤ (2 : ℝ) ^ (aliceCost P + 1) := by
      have h2N : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
        exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hN
      calc
        2 * ((B : ℝ) ^ δ) ^ N ≤ (2 : ℝ) ^ N * ((B : ℝ) ^ δ) ^ N :=
            mul_le_mul_of_nonneg_right h2N (by positivity)
        _ = (2 * (B : ℝ) ^ δ) ^ N := (mul_pow _ _ _).symm
        _ ≤ ((K : ℝ) / t) ^ N := pow_le_pow_left₀ (by positivity) hKt_ge N
        _ ≤ (2 : ℝ) ^ (aliceCost P + 1) := hA
    have hpow_alice : ((B : ℝ) ^ δ) ^ N ≤ (2 : ℝ) ^ aliceCost P := by
      rw [pow_succ] at hpow_ge; linarith
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < ((B : ℝ) ^ δ) ^ N) hpow_alice
    rw [Real.logb_pow, Real.logb_rpow_eq_mul_logb_of_pos hBpos,
      ← Real.rpow_natCast (2 : ℝ) (aliceCost P),
      Real.logb_rpow (by norm_num) (by norm_num)] at hlog
    linarith
  · right
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (by dsimp [K]; omega : 0 < K)
    have h2le : (2 : ℝ) ≤ (B : ℝ) / (K : ℝ) :=
      (le_div_iff₀ hKpos).mpr (by exact_mod_cast Nat.mul_div_le B 2)
    have hB_14 : 1 ≤ (B : ℝ) ^ (1 - 4 * δ) := Real.one_le_rpow hB1_real (by linarith)
    have ht_eq : t = (B : ℝ) ^ (1 - 4 * δ) * (B : ℝ) ^ δ := by
      dsimp [t]; rw [← Real.rpow_add hBpos]; congr 1; ring
    have ht_sub1 : (B : ℝ) ^ (1 - 4 * δ) + 1 ≤ t - 1 := by rw [ht_eq]; nlinarith
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hexp_ge : (N : ℝ) * (B : ℝ) ^ (1 - 4 * δ) + 1 ≤ (t - 1) * (N : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right ht_sub1 (by positivity : (0 : ℝ) ≤ N); nlinarith
    have hexp_nn : 0 ≤ (t - 1) * (N : ℝ) := by
      have : 0 ≤ (N : ℝ) * (B : ℝ) ^ (1 - 4 * δ) := mul_nonneg (by positivity) (by linarith)
      linarith
    have h2pow : (2 : ℝ) ^ ((N : ℝ) * (B : ℝ) ^ (1 - 4 * δ) + 1) ≤
        (2 : ℝ) ^ ((bobCost P : ℝ) + 1) := by
      calc
        (2 : ℝ) ^ ((N : ℝ) * (B : ℝ) ^ (1 - 4 * δ) + 1)
          ≤ (2 : ℝ) ^ ((t - 1) * (N : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
        _ ≤ ((B : ℝ) / (K : ℝ)) ^ ((t - 1) * (N : ℝ)) :=
            Real.rpow_le_rpow (by norm_num) h2le hexp_nn
        _ ≤ (2 : ℝ) ^ (bobCost P + 1) := hB_side
        _ = (2 : ℝ) ^ ((bobCost P : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
    linarith [(Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h2pow]

/-- Alice's input space `M → Equiv.Perm (Fin B)` for Switch-Permutation Lopsided Set Disjointness,
assigning a permutation of `Fin B` to each switch `m : M`. -/
abbrev SwitchPermAlice (M : Type*) (B : ℕ) : Type _ := M → Equiv.Perm (Fin B)

/-- Switch-Permutation Lopsided Set Disjointness $\mathsf{SPLSD}_{M, B}$, testing whether Alice's
switch-edge graph `{((m, i), π m i) | (m, i) : M × Fin B}` is disjoint from Bob's subset
`Y ⊆ (M × Fin B) × Fin B`. -/
def switchPermDisjoint (M : Type*) [Fintype M] [DecidableEq M] (B : ℕ)
    (π : SwitchPermAlice M B) (Y : Finset ((M × Fin B) × Fin B)) : Bool :=
  decide (Disjoint (Finset.univ.image fun w : M × Fin B ↦ (w, π w.1 w.2)) Y)

/-- `switchPermDisjoint M B π Y` evaluates to `true` iff Alice's switch-permutation graph is
disjoint from `Y`. -/
theorem switchPermDisjoint_eq_true_iff {M : Type*} [Fintype M] [DecidableEq M] {B : ℕ}
    {π : SwitchPermAlice M B} {Y : Finset ((M × Fin B) × Fin B)} :
    switchPermDisjoint M B π Y = true ↔
      Disjoint (Finset.univ.image fun w : M × Fin B ↦ (w, π w.1 w.2)) Y := by
  exact decide_eq_true_iff

/-- Elementary factorial lower bound `(B / e) ^ B ≤ B!` deduced from the `B`-th term of the
exponential series of `e ^ B`. -/
theorem div_exp_one_pow_le_factorial (B : ℕ) :
    ((B : ℝ) / Real.exp 1) ^ B ≤ (Nat.factorial B : ℝ) := by
  have hfac_pos : (0 : ℝ) < (Nat.factorial B : ℝ) := by positivity
  have hser := @Real.pow_div_factorial_le_exp (B : ℝ) (by positivity) B
  rw [show Real.exp (B : ℝ) = Real.exp 1 ^ B by rw [← Real.exp_nat_mul, mul_one],
    div_le_iff₀ hfac_pos] at hser
  rw [div_pow, div_le_iff₀ (by positivity : 0 < Real.exp 1 ^ B)]; linarith

/-- **Master Asymmetric Rectangle Bound for Switch-Permutation Lopsided Set Disjointness**: for a
nonempty finite switch set `M`, integers `1 ≤ K ≤ B`, and real `t ≥ 1`, every deterministic
protocol `P` computing `switchPermDisjoint M B` satisfies either
`(K / (e * t)) ^ (|M| * B) ≤ 2 ^ (aliceCost P + 1)` or
`(B / K) ^ ((t - 1) * (|M| * B)) ≤ 2 ^ (bobCost P + 1)`. -/
theorem switch_perm_lsd_master_lower_bound {M : Type*} [Fintype M] [DecidableEq M]
    {B K : ℕ} {t : ℝ} (hK1 : 1 ≤ K) (hKB : K ≤ B) (hM : 1 ≤ Fintype.card M) (ht : 1 ≤ t)
    {P : Protocol (SwitchPermAlice M B) (Finset ((M × Fin B) × Fin B)) Bool}
    (hP : P.run = switchPermDisjoint M B) :
    ((K : ℝ) / (Real.exp 1 * t)) ^ (Fintype.card M * B) ≤ (2 : ℝ) ^ (aliceCost P + 1) ∨
      ((B : ℝ) / K) ^ ((t - 1) * ((Fintype.card M * B : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (bobCost P + 1) := by
  have hB1 : 1 ≤ B := hK1.trans hKB
  have hBne : (B : ℝ) ≠ 0 := by positivity
  have hcard_perm : (Finset.univ : Finset (SwitchPermAlice M B)).card =
      (Nat.factorial B) ^ Fintype.card M := by
    simp [Fintype.card_perm]
  have hne : (Finset.univ : Finset (SwitchPermAlice M B)).Nonempty := Finset.card_pos.mp
    (by rw [hcard_perm]; exact Nat.pow_pos (Nat.factorial_pos B))
  have hsel_inj : Function.Injective
      (fun (π : SwitchPermAlice M B) (w : M × Fin B) ↦ π w.1 w.2) :=
    fun _ _ h ↦ funext fun m ↦ Equiv.ext fun i ↦ congrFun h (m, i)
  have hW_card : Fintype.card (M × Fin B) = Fintype.card M * B := by simp
  have hW1 : 1 ≤ Fintype.card (M × Fin B) := hW_card ▸ Nat.mul_le_mul hM hB1
  have hmaster := wire_selector_lsd_lower_bound (W := M × Fin B) hne hsel_inj hK1 hKB hW1 ht
    (fun π _ Y ↦ congrFun₂ hP π Y)
  rw [hW_card] at hmaster
  refine hmaster.imp (fun h1 ↦ ?_) id
  have hcard_ge : ((B : ℝ) / Real.exp 1) ^ (Fintype.card M * B) ≤
      ((Finset.univ : Finset (SwitchPermAlice M B)).card : ℝ) := by
    rw [hcard_perm, Nat.cast_pow, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (div_exp_one_pow_le_factorial B) (Fintype.card M)
  have hprod_eq : ((B : ℝ) / Real.exp 1) ^ (Fintype.card M * B) *
      ((K : ℝ) / (t * (B : ℝ))) ^ (Fintype.card M * B) =
      ((K : ℝ) / (Real.exp 1 * t)) ^ (Fintype.card M * B) := by
    rw [← mul_pow]; congr 1; field_simp [hBne, ne_of_gt (Real.exp_pos 1)]
  exact hprod_eq ▸ (mul_le_mul_of_nonneg_right hcard_ge (by positivity)).trans h1

/-- **Concrete Square-Root Lower Bound for Switch-Permutation Lopsided Set Disjointness**: for
`B ≥ 4096` and `|M| ≥ 1`, every deterministic protocol `P` computing `switchPermDisjoint M B`
satisfies either `(Fintype.card M * B : ℝ) * log₂ B / 4 ≤ aliceCost P + 1` or
`(Fintype.card M * B : ℝ) * √B / 2 ≤ bobCost P + 1`. -/
theorem switch_perm_lsd_sqrt_lower_bound {M : Type*} [Fintype M] [DecidableEq M] {B : ℕ}
    (hB : 4096 ≤ B) (hM : 1 ≤ Fintype.card M)
    {P : Protocol (SwitchPermAlice M B) (Finset ((M × Fin B) × Fin B)) Bool}
    (hP : P.run = switchPermDisjoint M B) :
    ((Fintype.card M * B : ℕ) : ℝ) * Real.logb 2 B / 4 ≤ (aliceCost P : ℝ) + 1 ∨
      ((Fintype.card M * B : ℕ) : ℝ) * Real.sqrt B / 2 ≤ (bobCost P : ℝ) + 1 := by
  let K : ℕ := B / 2
  have ht1 : (1 : ℝ) ≤ Real.sqrt B := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ B))
  rcases switch_perm_lsd_master_lower_bound (K := K) (by omega) (Nat.div_le_self B 2) hM ht1 hP with
    hA | hB_side
  · left
    have hexp : Real.exp 1 ≤ 27 / 8 := by
      have h13 : (2 / 3 : ℝ) ≤ Real.exp (-1 / 3) := by linarith [Real.add_one_le_exp (-1 / 3 : ℝ)]
      have hcube : (8 / 27 : ℝ) ≤ Real.exp (-1) := by
        calc
          (8 / 27 : ℝ) = (2 / 3 : ℝ) ^ 3 := by norm_num
          _ ≤ (Real.exp (-1 / 3)) ^ 3 := pow_le_pow_left₀ (by norm_num) h13 3
          _ = Real.exp (3 * (-1 / 3 : ℝ)) := (Real.exp_nat_mul (-1 / 3 : ℝ) 3).symm
          _ = Real.exp (-1) := by norm_num
      rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos 1)] at hcube; linarith
    let r := Real.sqrt (Real.sqrt B)
    have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = Real.sqrt B := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hr4 : r ^ 4 = (B : ℝ) := by
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = (B : ℝ) := by rw [hr2]; exact Real.sq_sqrt (by positivity)
    have hr_ge8 : (8 : ℝ) ≤ r := by
      by_contra hlt; push Not at hlt
      have hpow4 : r ^ 4 < (8 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hr_nn (by omega)
      have hB4096 : (4096 : ℝ) ≤ B := by exact_mod_cast hB
      rw [hr4] at hpow4; norm_num at hpow4; linarith
    have h27B : (27 : ℝ) * (B : ℝ) ≤ 64 * (K : ℝ) := by
      exact_mod_cast (by omega : 27 * B ≤ 64 * (B / 2))
    have hr_le : r ≤ (K : ℝ) / (Real.exp 1 * Real.sqrt B) := by
      have hd_pos : 0 < Real.exp 1 * Real.sqrt B :=
        mul_pos (Real.exp_pos 1) (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < B))
      rw [le_div_iff₀ hd_pos, ← hr2]
      have hr3_nn : 0 ≤ r ^ 3 := pow_nonneg hr_nn 3
      have h1 : Real.exp 1 * r ^ 3 ≤ (27 / 8 : ℝ) * r ^ 3 :=
        mul_le_mul_of_nonneg_right hexp hr3_nn
      have h2 : (27 / 8 : ℝ) * r ^ 3 ≤ (27 / 64 : ℝ) * r ^ 4 := by nlinarith
      linarith [show r * (Real.exp 1 * r ^ 2) = Real.exp 1 * r ^ 3 by ring, h1.trans h2, hr4, h27B]
    exact logb_four_pow_alice_bound (by omega) hr_le hA
  · exact Or.inr (sqrt_bob_bound_of_rpow (by omega) hB_side)

/-! ### 4. Private Benchmark Witnesses -/

private def blockedDisjointTwoTwoProtocol :
    Protocol (BlockedAlice 2 2) (Finset (Fin 2 × Fin 2)) Bool :=
  Protocol.aliceSend 2 (fun x i ↦ decide (x i = 1)) fun b ↦
    let xHat : BlockedAlice 2 2 := fun i ↦ if b i then 1 else 0
    .bob (fun Y ↦ blockedDisjoint 2 2 xHat Y) (.output false) (.output true)

private theorem run_blockedDisjointTwoTwoProtocol :
    blockedDisjointTwoTwoProtocol.run = blockedDisjoint 2 2 := by
  funext x Y
  have hfin2 : ∀ u : Fin 2, (if decide (u = 1) then (1 : Fin 2) else 0) = u := by
    intro u; fin_cases u <;> rfl
  have hx : (fun i : Fin 2 ↦ if decide (x i = 1) then (1 : Fin 2) else 0) = x :=
    funext fun i ↦ hfin2 (x i)
  simp only [blockedDisjointTwoTwoProtocol, Protocol.run_aliceSend, Protocol.run_bob,
    Protocol.run_output, hx]
  cases blockedDisjoint 2 2 x Y <;> rfl

private theorem exists_protocol_blockedDisjoint_two_two :
    ∃ P : Protocol (BlockedAlice 2 2) (Finset (Fin 2 × Fin 2)) Bool,
      P.run = blockedDisjoint 2 2 ∧ aliceCost P ≤ 2 ∧ bobCost P ≤ 1 :=
  ⟨blockedDisjointTwoTwoProtocol, run_blockedDisjointTwoTwoProtocol,
    by rw [blockedDisjointTwoTwoProtocol]; simpa using aliceCost_aliceSend_le (a :=
      0) fun _ ↦ by simp,
    by rw [blockedDisjointTwoTwoProtocol]; exact bobCost_aliceSend_le fun _ ↦ by simp⟩

private theorem not_run_eq_blockedDisjoint_of_cost_zero {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    {P : Protocol (BlockedAlice N B) (Finset (Fin N × Fin B)) Bool}
    (ha : aliceCost P = 0) (hb : bobCost P = 0) :
    P.run ≠ blockedDisjoint N B := by
  intro hcomp
  let x₀ : BlockedAlice N B := fun _ ↦ ⟨0, hB⟩
  have hconst := run_eq_of_aliceCost_eq_zero_of_bobCost_eq_zero ha hb x₀ x₀ ∅ Finset.univ
  rw [congrFun₂ hcomp x₀ ∅, congrFun₂ hcomp x₀ Finset.univ] at hconst
  have hempty : blockedDisjoint N B x₀ ∅ = true := by simp [blockedDisjoint]
  have huniv : blockedDisjoint N B x₀ Finset.univ = false := by
    rw [blockedDisjoint, decide_eq_false_iff_not, Finset.not_disjoint_iff]
    exact ⟨(⟨0, hN⟩, x₀ ⟨0, hN⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), Finset.mem_univ _⟩
  rw [hempty, huniv] at hconst
  exact Bool.false_ne_true hconst.symm

end LopsidedSetDisjointness

end CslibFrontier.Communication
