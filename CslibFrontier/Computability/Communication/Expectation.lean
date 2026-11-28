module

public import CslibFrontier.Computability.Communication.Operations
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Matrix.ColumnRowPartitioned

import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Randomized Communication Protocols Computing Matrices in Expectation

Formalizes randomized communication protocols with private randomness computing nonnegative real
matrices in expectation and their quantitative equivalence with nonnegative matrix rank:

- `RandProtocol`: a rooted binary tree whose internal nodes belong to Alice (`X`) or Bob (`Y`)
  with private transition probabilities in `[0, 1]` and whose leaves carry nonnegative real values,
  with `depth`, `leafCount`, expected output `expect`, `ComputesInExpectation`, event probability
  `probEvent`, positive-output probability `probPos`, and one-way predicate `IsOneWay`.
- `nonnegRank_le_two_pow_depth`: any randomized protocol of complexity at most `c` computing a
  nonnegative matrix `M` in expectation yields a nonnegative factorization of rank at most `2 ^ c`.
- `exists_randProtocol_of_row_partition`: combining protocols on a two-part row partition costs
  at most `1 + max c₁ c₂` bits.
- `exists_randProtocol_split_nonneg` & `exists_randProtocol_split_polytope`: splitting a
  nonnegative matrix into `d` nonnegative coordinate rows and a remaining submatrix of complexity
  `c` costs at most `1 + max c (⌈log₂ d⌉ + 1)` bits, and `exists_simplex_no_depth_two_randProtocol`
  establishes tightness on the standard 2-simplex.
- `exists_oneWay_randProtocol_of_nonnegFactorization`: any rank-`r` nonnegative factorization
  yields a one-way randomized protocol of complexity at most `⌈log₂ (r + 1)⌉ + 1`.
-/

public section

namespace CslibFrontier.Communication

open Matrix Cslib.Communication

/-! ### Randomized communication protocols with private randomness -/

section Defs

/-- A randomized communication protocol with private random bits between Alice (holding `x : X`)
and Bob (holding `y : Y`) outputting nonnegative real leaf values. -/
inductive RandProtocol (X Y : Type*) where
  /-- Leaf outputting a fixed nonnegative real value `val`. -/
  | leaf (val : ℝ) (hval : 0 ≤ val)
  /-- Internal node owned by Alice: descends left with probability `prob x ∈ [0, 1]`, right with
  probability `1 - prob x`. -/
  | alice (prob : X → ℝ) (hprob : ∀ x, prob x ∈ Set.Icc (0 : ℝ) 1)
      (left right : RandProtocol X Y)
  /-- Internal node owned by Bob: descends left with probability `prob y ∈ [0, 1]`, right with
  probability `1 - prob y`. -/
  | bob (prob : Y → ℝ) (hprob : ∀ y, prob y ∈ Set.Icc (0 : ℝ) 1)
      (left right : RandProtocol X Y)

namespace RandProtocol

variable {X Y X' Y' : Type*}

/-- The communication complexity (tree height) of a randomized protocol. -/
def depth : RandProtocol X Y → ℕ
  | leaf _ _ => 0
  | alice _ _ l r => max l.depth r.depth + 1
  | bob _ _ l r => max l.depth r.depth + 1

/-- The number of leaves of a randomized protocol tree. -/
def leafCount : RandProtocol X Y → ℕ
  | leaf _ _ => 1
  | alice _ _ l r => l.leafCount + r.leafCount
  | bob _ _ l r => l.leafCount + r.leafCount

/-- The expected output value of a randomized protocol on input pair `(x, y)`. -/
def expect : RandProtocol X Y → X → Y → ℝ
  | leaf v _, _, _ => v
  | alice p _ l r, x, y => p x * l.expect x y + (1 - p x) * r.expect x y
  | bob q _ l r, x, y => q y * l.expect x y + (1 - q y) * r.expect x y

/-- A randomized protocol computes a matrix `M` in expectation if its expected output on every
input `(x, y)` equals `M x y`. -/
@[expose] def ComputesInExpectation (P : RandProtocol X Y) (M : Matrix X Y ℝ) : Prop :=
  ∀ x y, P.expect x y = M x y

/-- The probability that an execution of `P` on `(x, y)` terminates at a leaf whose value
satisfies predicate `Q`. -/
noncomputable def probEvent (P : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) : ℝ := by
  classical
  exact match P with
  | leaf v _ => if Q v then 1 else 0
  | alice p _ l r => p x * l.probEvent Q x y + (1 - p x) * r.probEvent Q x y
  | bob q _ l r => q y * l.probEvent Q x y + (1 - q y) * r.probEvent Q x y

/-- The probability that an execution of `P` on `(x, y)` outputs a strictly positive value. -/
@[expose] noncomputable def probPos (P : RandProtocol X Y) (x : X) (y : Y) : ℝ :=
  P.probEvent (fun v => 0 < v) x y

/-- A protocol is one-way (from Alice to Bob) if no Alice node appears strictly below a Bob node. -/
@[expose] def IsBobOnly : RandProtocol X Y → Prop
  | leaf _ _ => True
  | alice _ _ _ _ => False
  | bob _ _ l r => l.IsBobOnly ∧ r.IsBobOnly

/-- A protocol is one-way from Alice to Bob if all Alice nodes occur above all Bob nodes. -/
@[expose] def IsOneWay : RandProtocol X Y → Prop
  | leaf _ _ => True
  | alice _ _ l r => l.IsOneWay ∧ r.IsOneWay
  | bob _ _ l r => l.IsBobOnly ∧ r.IsBobOnly

@[simp] theorem depth_leaf (v : ℝ) (hv : 0 ≤ v) :
    (leaf v hv : RandProtocol X Y).depth = 0 := by rfl

@[simp] theorem depth_alice (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) : (alice p hp l r).depth = max l.depth r.depth + 1 := by rfl

@[simp] theorem depth_bob (q : Y → ℝ) (hq : ∀ y, q y ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) : (bob q hq l r).depth = max l.depth r.depth + 1 := by rfl

@[simp] theorem leafCount_leaf (v : ℝ) (hv : 0 ≤ v) :
    (leaf v hv : RandProtocol X Y).leafCount = 1 := by rfl

@[simp] theorem leafCount_alice (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) : (alice p hp l r).leafCount = l.leafCount + r.leafCount := by rfl

@[simp] theorem leafCount_bob (q : Y → ℝ) (hq : ∀ y, q y ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) : (bob q hq l r).leafCount = l.leafCount + r.leafCount := by rfl

@[simp] theorem expect_leaf (v : ℝ) (hv : 0 ≤ v) (x : X) (y : Y) :
    (leaf v hv : RandProtocol X Y).expect x y = v := by rfl

@[simp] theorem expect_alice (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) (x : X) (y : Y) :
    (alice p hp l r).expect x y = p x * l.expect x y + (1 - p x) * r.expect x y := by rfl

@[simp] theorem expect_bob (q : Y → ℝ) (hq : ∀ y, q y ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) (x : X) (y : Y) :
    (bob q hq l r).expect x y = q y * l.expect x y + (1 - q y) * r.expect x y := by rfl

@[simp] theorem probEvent_leaf (v : ℝ) (hv : 0 ≤ v) (Q : ℝ → Prop) [Decidable (Q v)] (x : X)
    (y : Y) : (leaf v hv : RandProtocol X Y).probEvent Q x y = if Q v then 1 else 0 := by
  classical
  simp only [probEvent]
  split_ifs <;> rfl

@[simp] theorem probEvent_alice (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) :
    (alice p hp l r).probEvent Q x y = p x * l.probEvent Q x y + (1 - p x) * r.probEvent Q x y := by
  rfl

@[simp] theorem probEvent_bob (q : Y → ℝ) (hq : ∀ y, q y ∈ Set.Icc (0 : ℝ) 1)
    (l r : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) :
    (bob q hq l r).probEvent Q x y = q y * l.probEvent Q x y + (1 - q y) * r.probEvent Q x y := by
  rfl

/-- Every randomized protocol tree has at least one leaf. -/
theorem leafCount_pos (P : RandProtocol X Y) : 0 < P.leafCount := by
  induction P with
  | leaf _ _ => exact Nat.zero_lt_one
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr =>
    simp only [leafCount_alice, leafCount_bob]
    omega

/-- A randomized protocol of depth `d` has at most `2 ^ d` leaves. -/
theorem leafCount_le_two_pow_depth (P : RandProtocol X Y) : P.leafCount ≤ 2 ^ P.depth := by
  induction P with
  | leaf _ _ => simp
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr =>
    exact Nat.add_le_two_pow_max_succ ihl ihr

/-- The expected output of a randomized protocol is always nonnegative. -/
theorem expect_nonneg (P : RandProtocol X Y) (x : X) (y : Y) : 0 ≤ P.expect x y := by
  induction P with
  | leaf v hv => exact hv
  | alice p hp l r ihl ihr =>
    have hpx := hp x
    exact add_nonneg (mul_nonneg hpx.1 ihl) (mul_nonneg (sub_nonneg.2 hpx.2) ihr)
  | bob q hq l r ihl ihr =>
    have hqy := hq y
    exact add_nonneg (mul_nonneg hqy.1 ihl) (mul_nonneg (sub_nonneg.2 hqy.2) ihr)

/-- Every event probability lies in `[0, 1]`. -/
theorem probEvent_mem_Icc (P : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) :
    P.probEvent Q x y ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  induction P with
  | leaf v hv =>
    rw [probEvent_leaf]
    split_ifs <;> simp
  | alice p hp l r ihl ihr =>
    rcases hp x with ⟨hp0, hp1⟩
    simp only [probEvent_alice, Set.mem_Icc] at ihl ihr ⊢
    constructor <;> nlinarith
  | bob q hq l r ihl ihr =>
    rcases hq y with ⟨hq0, hq1⟩
    simp only [probEvent_bob, Set.mem_Icc] at ihl ihr ⊢
    constructor <;> nlinarith

/-- Event probabilities are nonnegative. -/
theorem probEvent_nonneg (P : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) :
    0 ≤ P.probEvent Q x y :=
  (P.probEvent_mem_Icc Q x y).1

/-- Event probabilities are at most `1`. -/
theorem probEvent_le_one (P : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) :
    P.probEvent Q x y ≤ 1 :=
  (P.probEvent_mem_Icc Q x y).2

/-- Event probabilities are complementary: `P[Q] + P[¬ Q] = 1`. -/
theorem probEvent_add_not (P : RandProtocol X Y) (Q : ℝ → Prop) (x : X) (y : Y) :
    P.probEvent Q x y + P.probEvent (fun v => ¬ Q v) x y = 1 := by
  classical
  induction P with
  | leaf v hv =>
    rw [probEvent_leaf, probEvent_leaf]
    split_ifs <;> norm_num
  | alice p hp l r ihl ihr =>
    simp only [probEvent_alice]
    have h1 := mul_add (p x) (l.probEvent Q x y) (l.probEvent (fun v => ¬ Q v) x y)
    have h2 := mul_add (1 - p x) (r.probEvent Q x y) (r.probEvent (fun v => ¬ Q v) x y)
    rw [ihl, mul_one] at h1
    rw [ihr, mul_one] at h2
    linarith
  | bob q hq l r ihl ihr =>
    simp only [probEvent_bob]
    have h1 := mul_add (q y) (l.probEvent Q x y) (l.probEvent (fun v => ¬ Q v) x y)
    have h2 := mul_add (1 - q y) (r.probEvent Q x y) (r.probEvent (fun v => ¬ Q v) x y)
    rw [ihl, mul_one] at h1
    rw [ihr, mul_one] at h2
    linarith

/-- One-sided zero error: if the expected output on `(x, y)` is `0`, then the probability of
outputting a strictly positive value is `0`. -/
theorem probPos_eq_zero_of_expect_eq_zero (P : RandProtocol X Y) {x : X} {y : Y}
    (h0 : P.expect x y = 0) : P.probPos x y = 0 := by
  induction P with
  | leaf v hv =>
    simp only [expect_leaf] at h0
    subst h0
    simp [probPos]
  | alice p hp l r ihl ihr =>
    rcases hp x with ⟨hp0, hp1⟩
    have hl0 := l.expect_nonneg x y
    have hr0 := r.expect_nonneg x y
    simp only [expect_alice] at h0
    have h1 : p x * l.expect x y = 0 := by nlinarith
    have h2 : (1 - p x) * r.expect x y = 0 := by nlinarith
    simp only [probPos, probEvent_alice]
    have hl' : p x * l.probPos x y = 0 := by
      rcases mul_eq_zero.1 h1 with hp0' | hle0
      · simp [hp0']
      · simp [ihl hle0]
    have hr' : (1 - p x) * r.probPos x y = 0 := by
      rcases mul_eq_zero.1 h2 with hp1' | hre0
      · simp [hp1']
      · simp [ihr hre0]
    simpa only [probPos] using congrArg₂ (· + ·) hl' hr' |>.trans (add_zero 0)
  | bob q hq l r ihl ihr =>
    rcases hq y with ⟨hq0, hq1⟩
    have hl0 := l.expect_nonneg x y
    have hr0 := r.expect_nonneg x y
    simp only [expect_bob] at h0
    have h1 : q y * l.expect x y = 0 := by nlinarith
    have h2 : (1 - q y) * r.expect x y = 0 := by nlinarith
    simp only [probPos, probEvent_bob]
    have hl' : q y * l.probPos x y = 0 := by
      rcases mul_eq_zero.1 h1 with hq0 | hle0
      · simp [hq0]
      · simp [ihl hle0]
    have hr' : (1 - q y) * r.probPos x y = 0 := by
      rcases mul_eq_zero.1 h2 with hq1 | hre0
      · simp [hq1]
      · simp [ihr hre0]
    simpa only [probPos] using congrArg₂ (· + ·) hl' hr' |>.trans (add_zero 0)

/-! ### Combinators on randomized protocols -/

/-- Run `P` on transformed inputs `f x'` and `g y'`. -/
def comap (f : X' → X) (g : Y' → Y) : RandProtocol X Y → RandProtocol X' Y'
  | leaf v hv => leaf v hv
  | alice p hp l r => alice (fun x => p (f x)) (fun x => hp (f x)) (l.comap f g) (r.comap f g)
  | bob q hq l r => bob (fun y => q (g y)) (fun y => hq (g y)) (l.comap f g) (r.comap f g)

@[simp] theorem expect_comap (f : X' → X) (g : Y' → Y) (P : RandProtocol X Y) (x : X') (y : Y') :
    (P.comap f g).expect x y = P.expect (f x) (g y) := by
  induction P with
  | leaf _ _ => rfl
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr => simp [comap, ihl, ihr]

@[simp] theorem depth_comap (f : X' → X) (g : Y' → Y) (P : RandProtocol X Y) :
    (P.comap f g).depth = P.depth := by
  induction P with
  | leaf _ _ => rfl
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr => simp [comap, ihl, ihr]

@[simp] theorem probEvent_comap (f : X' → X) (g : Y' → Y) (P : RandProtocol X Y) (Q : ℝ → Prop)
    (x : X') (y : Y') : (P.comap f g).probEvent Q x y = P.probEvent Q (f x) (g y) := by
  classical
  induction P with
  | leaf _ _ => simp [comap]
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr => simp [comap, ihl, ihr]

/-- Swap the roles of Alice and Bob. -/
def swap : RandProtocol X Y → RandProtocol Y X
  | leaf v hv => leaf v hv
  | alice p hp l r => bob p hp l.swap r.swap
  | bob q hq l r => alice q hq l.swap r.swap

@[simp] theorem expect_swap (P : RandProtocol X Y) (y : Y) (x : X) :
    P.swap.expect y x = P.expect x y := by
  induction P with
  | leaf _ _ => rfl
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr => simp [swap, ihl, ihr]

@[simp] theorem depth_swap (P : RandProtocol X Y) : P.swap.depth = P.depth := by
  induction P with
  | leaf _ _ => rfl
  | alice _ _ _ _ ihl ihr | bob _ _ _ _ ihl ihr => simp [swap, ihl, ihr]

/-- Deterministic Alice branch on a Boolean predicate. -/
def aliceDet (b : X → Bool) (ifFalse ifTrue : RandProtocol X Y) : RandProtocol X Y :=
  alice (fun x => if b x then 0 else 1) (fun x => by cases b x <;> simp) ifFalse ifTrue

/-- Deterministic Bob branch on a Boolean predicate. -/
def bobDet (b : Y → Bool) (ifFalse ifTrue : RandProtocol X Y) : RandProtocol X Y :=
  bob (fun y => if b y then 0 else 1) (fun y => by cases b y <;> simp) ifFalse ifTrue

@[simp] theorem expect_aliceDet (b : X → Bool) (l r : RandProtocol X Y) (x : X) (y : Y) :
    (aliceDet b l r).expect x y = cond (b x) (r.expect x y) (l.expect x y) := by
  cases hb : b x <;> simp [aliceDet, hb]

@[simp] theorem expect_bobDet (b : Y → Bool) (l r : RandProtocol X Y) (x : X) (y : Y) :
    (bobDet b l r).expect x y = cond (b y) (r.expect x y) (l.expect x y) := by
  cases hb : b y <;> simp [bobDet, hb]

@[simp] theorem depth_aliceDet (b : X → Bool) (l r : RandProtocol X Y) :
    (aliceDet b l r).depth = max l.depth r.depth + 1 := by rfl

@[simp] theorem depth_bobDet (b : Y → Bool) (l r : RandProtocol X Y) :
    (bobDet b l r).depth = max l.depth r.depth + 1 := by rfl

/-- Predicate stating that every leaf value of a deterministic real-valued protocol is
nonnegative. -/
@[expose] def ProtocolNonneg : Protocol X Y ℝ → Prop
  | .output z => 0 ≤ z
  | .alice _ p₀ p₁ => ProtocolNonneg p₀ ∧ ProtocolNonneg p₁
  | .bob _ p₀ p₁ => ProtocolNonneg p₀ ∧ ProtocolNonneg p₁

/-- Embed a deterministic `Cslib.Communication.Protocol` with nonnegative real outputs as a
randomized protocol of identical depth and expected output equal to its deterministic output. -/
def ofDeterministic : (p : Protocol X Y ℝ) → ProtocolNonneg p → RandProtocol X Y
  | .output z, hz => leaf z hz
  | .alice s p₀ p₁, h => aliceDet s (ofDeterministic p₀ h.1) (ofDeterministic p₁ h.2)
  | .bob s p₀ p₁, h => bobDet s (ofDeterministic p₀ h.1) (ofDeterministic p₁ h.2)

@[simp] theorem expect_ofDeterministic (p : Protocol X Y ℝ) (hp : ProtocolNonneg p)
    (x : X) (y : Y) : (ofDeterministic p hp).expect x y = p.run x y := by
  induction p with
  | output z => rfl
  | alice s p₀ p₁ ih₀ ih₁ =>
    simp only [ofDeterministic, expect_aliceDet, Protocol.run_alice, ih₀ hp.1, ih₁ hp.2]
  | bob s p₀ p₁ ih₀ ih₁ =>
    simp only [ofDeterministic, expect_bobDet, Protocol.run_bob, ih₀ hp.1, ih₁ hp.2]

@[simp] theorem depth_ofDeterministic (p : Protocol X Y ℝ) (hp : ProtocolNonneg p) :
    (ofDeterministic p hp).depth = p.depth := by
  induction p with
  | output z => rfl
  | alice s p₀ p₁ ih₀ ih₁ =>
    simp only [ofDeterministic, depth_aliceDet, Protocol.depth_alice, ih₀ hp.1, ih₁ hp.2]
  | bob s p₀ p₁ ih₀ ih₁ =>
    simp only [ofDeterministic, depth_bobDet, Protocol.depth_bob, ih₀ hp.1, ih₁ hp.2]

/-- Run a deterministic protocol `p : Protocol X Y Z`, then continue with a randomized protocol
`cont z` depending on its output `z`. -/
def bindDeterministic {Z : Type*} :
    Protocol X Y Z → (Z → RandProtocol X Y) → RandProtocol X Y
  | .output z, cont => cont z
  | .alice s p₀ p₁, cont => aliceDet s (bindDeterministic p₀ cont) (bindDeterministic p₁ cont)
  | .bob s p₀ p₁, cont => bobDet s (bindDeterministic p₀ cont) (bindDeterministic p₁ cont)

@[simp] theorem expect_bindDeterministic {Z : Type*} (p : Protocol X Y Z)
    (cont : Z → RandProtocol X Y) (x : X) (y : Y) :
    (bindDeterministic p cont).expect x y = (cont (p.run x y)).expect x y := by
  induction p with
  | output z => rfl
  | alice s p₀ p₁ ih₀ ih₁ => cases hs : s x <;> simp [bindDeterministic, hs, ih₀, ih₁]
  | bob s p₀ p₁ ih₀ ih₁ => cases hs : s y <;> simp [bindDeterministic, hs, ih₀, ih₁]

theorem depth_bindDeterministic_le {Z : Type*} (p : Protocol X Y Z) (cont : Z → RandProtocol X Y)
    {d : ℕ} (hd : ∀ z, (cont z).depth ≤ d) :
    (bindDeterministic p cont).depth ≤ p.depth + d := by
  induction p with
  | output z => simpa [bindDeterministic] using hd z
  | alice s p₀ p₁ ih₀ ih₁ | bob s p₀ p₁ ih₀ ih₁ =>
    simp only [bindDeterministic, depth_aliceDet, depth_bobDet, Protocol.depth_alice,
      Protocol.depth_bob]
    omega

/-- Alice outputs a nonnegative value `v x ∈ [0, B]` in expectation using 1 randomized bit. -/
noncomputable def aliceOutputVal (v : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ B) : RandProtocol X Y :=
  if hB0 : B = 0 then leaf 0 le_rfl
  else
    alice (fun x => v x / B)
      (fun x => ⟨div_nonneg (hv x).1 hB,
        (div_le_one (lt_of_le_of_ne hB (Ne.symm hB0))).2 (hv x).2⟩)
      (leaf B hB) (leaf 0 le_rfl)

/-- Bob outputs a nonnegative value `v y ∈ [0, B]` in expectation using 1 randomized bit. -/
noncomputable def bobOutputVal (v : Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ y, 0 ≤ v y ∧ v y ≤ B) : RandProtocol X Y :=
  (aliceOutputVal v B hB hv).swap

@[simp] theorem expect_aliceOutputVal (v : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ B) (x : X) (y : Y) :
    (aliceOutputVal v B hB hv : RandProtocol X Y).expect x y = v x := by
  unfold aliceOutputVal
  split_ifs with hB0
  · subst hB0
    exact (le_antisymm (hv x).2 (hv x).1).symm
  · simp only [expect_alice, expect_leaf, mul_zero, add_zero]
    exact div_mul_cancel₀ (v x) hB0

theorem depth_aliceOutputVal_le (v : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ B) :
    (aliceOutputVal v B hB hv : RandProtocol X Y).depth ≤ 1 := by
  unfold aliceOutputVal
  split_ifs <;> simp

@[simp] theorem expect_bobOutputVal (v : Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ y, 0 ≤ v y ∧ v y ≤ B) (x : X) (y : Y) :
    (bobOutputVal v B hB hv : RandProtocol X Y).expect x y = v y := by
  simp [bobOutputVal]

theorem depth_bobOutputVal_le (v : Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ y, 0 ≤ v y ∧ v y ≤ B) :
    (bobOutputVal v B hB hv : RandProtocol X Y).depth ≤ 1 := by
  simpa [bobOutputVal] using depth_aliceOutputVal_le (Y := X) v B hB hv

theorem isBobOnly_bobOutputVal (v : Y → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ y, 0 ≤ v y ∧ v y ≤ B) :
    (bobOutputVal v B hB hv : RandProtocol X Y).IsBobOnly := by
  unfold bobOutputVal aliceOutputVal
  split_ifs <;> simp [swap, IsBobOnly]

/-- Alice deterministically sends a value `f x` in a finite nonempty type `Z` using
`⌈log₂ |Z|⌉` bits, then continues with `cont (f x)`. -/
noncomputable def aliceSendFin {Z : Type*} [Fintype Z] [Nonempty Z] (f : X → Z)
    (cont : Z → RandProtocol X Y) : RandProtocol X Y :=
  let e : Z ↪ Cslib.BitString (Nat.clog 2 (Fintype.card Z)) :=
    (Function.Embedding.nonempty_of_card_le
      (Cslib.BitString.card ▸ Nat.le_pow_clog one_lt_two _)).some
  bindDeterministic
    (Protocol.aliceSend _ (fun x => e (f x)) fun m => Protocol.output (Function.invFun e m))
    cont

/-- Bob deterministically sends a value `f y` in a finite nonempty type `Z` using
`⌈log₂ |Z|⌉` bits, then continues with `cont (f y)`. -/
noncomputable def bobSendFin {Z : Type*} [Fintype Z] [Nonempty Z] (f : Y → Z)
    (cont : Z → RandProtocol X Y) : RandProtocol X Y :=
  (aliceSendFin f fun z => (cont z).swap).swap

theorem expect_aliceSendFin {Z : Type*} [Fintype Z] [Nonempty Z] (f : X → Z)
    (cont : Z → RandProtocol X Y) (x : X) (y : Y) :
    (aliceSendFin f cont).expect x y = (cont (f x)).expect x y := by
  unfold aliceSendFin
  simp only [expect_bindDeterministic, Protocol.run_aliceSend, Protocol.run_output]
  congr 2
  exact Function.leftInverse_invFun
    (Function.Embedding.nonempty_of_card_le
      (Cslib.BitString.card ▸ Nat.le_pow_clog one_lt_two (Fintype.card Z))).some.injective (f x)

theorem depth_aliceSendFin_le {Z : Type*} [Fintype Z] [Nonempty Z] (f : X → Z)
    (cont : Z → RandProtocol X Y) {d : ℕ} (hd : ∀ z, (cont z).depth ≤ d) :
    (aliceSendFin f cont).depth ≤ Nat.clog 2 (Fintype.card Z) + d := by
  unfold aliceSendFin
  refine (depth_bindDeterministic_le _ _ hd).trans ?_
  have h1 := Protocol.depth_aliceSend_le (d := 0) (X := X) (Y := Y) (Z := Z)
    (msg := fun x => (Function.Embedding.nonempty_of_card_le
      (Cslib.BitString.card ▸ Nat.le_pow_clog one_lt_two (Fintype.card Z))).some (f x))
    (cont := fun m => Protocol.output (Function.invFun (Function.Embedding.nonempty_of_card_le
      (Cslib.BitString.card ▸ Nat.le_pow_clog one_lt_two (Fintype.card Z))).some m))
    (fun _ => le_rfl)
  exact Nat.add_le_add_right (by simpa using h1) d

theorem expect_bobSendFin {Z : Type*} [Fintype Z] [Nonempty Z] (f : Y → Z)
    (cont : Z → RandProtocol X Y) (x : X) (y : Y) :
    (bobSendFin f cont).expect x y = (cont (f y)).expect x y := by
  simp [bobSendFin, expect_aliceSendFin]

theorem depth_bobSendFin_le {Z : Type*} [Fintype Z] [Nonempty Z] (f : Y → Z)
    (cont : Z → RandProtocol X Y) {d : ℕ} (hd : ∀ z, (cont z).depth ≤ d) :
    (bobSendFin f cont).depth ≤ Nat.clog 2 (Fintype.card Z) + d := by
  simpa [bobSendFin] using
    depth_aliceSendFin_le f (fun z => (cont z).swap) (fun z => by simpa using hd z)

/-- Balanced binary tree of depth `d` of Alice nodes sampling `k : Fin (2 ^ d)` with probability
`p x k`, then running `cont k`. -/
noncomputable def aliceSamplePow : (d : ℕ) → (p : X → Fin (2 ^ d) → ℝ) →
    (∀ x k, 0 ≤ p x k) → (∀ x, ∑ k, p x k = 1) →
    (Fin (2 ^ d) → RandProtocol X Y) → RandProtocol X Y
  | 0, _, _, _, cont => cont ⟨0, by decide⟩
  | d + 1, p, hp, hsum, cont =>
    let split : Fin (2 ^ d) ⊕ Fin (2 ^ d) ≃ Fin (2 ^ (d + 1)) :=
      finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))
    let pL : X → Fin (2 ^ d) → ℝ := fun x k => p x (split (Sum.inl k))
    let pR : X → Fin (2 ^ d) → ℝ := fun x k => p x (split (Sum.inr k))
    let wL : X → ℝ := fun x => ∑ k, pL x k
    let wR : X → ℝ := fun x => ∑ k, pR x k
    have hsplit : ∀ x, wL x + wR x = 1 := fun x => by
      have h := (Equiv.sum_comp split (p x)).trans (hsum x)
      rwa [Fintype.sum_sum_type] at h
    have hwL : ∀ x, wL x ∈ Set.Icc (0 : ℝ) 1 := fun x =>
      ⟨Finset.sum_nonneg fun k _ => hp x _, by
        have hR0 : 0 ≤ wR x := Finset.sum_nonneg fun k _ => hp x _
        linarith [hsplit x]⟩
    have hpos_d : 0 < 2 ^ d := Nat.two_pow_pos d
    let qL : X → Fin (2 ^ d) → ℝ := fun x k =>
      if wL x = 0 then if k = ⟨0, hpos_d⟩ then 1 else 0 else pL x k / wL x
    let qR : X → Fin (2 ^ d) → ℝ := fun x k =>
      if wR x = 0 then if k = ⟨0, hpos_d⟩ then 1 else 0 else pR x k / wR x
    have hqL0 : ∀ x k, 0 ≤ qL x k := fun x k => by
      dsimp only [qL]
      split_ifs
      · exact zero_le_one
      · exact le_rfl
      · exact div_nonneg (hp x _) (hwL x).1
    have hqR0 : ∀ x k, 0 ≤ qR x k := fun x k => by
      dsimp only [qR]
      split_ifs
      · exact zero_le_one
      · exact le_rfl
      · exact div_nonneg (hp x _) (Finset.sum_nonneg fun _ _ => hp x _)
    have hqL1 : ∀ x, ∑ k, qL x k = 1 := fun x => by
      dsimp only [qL]
      by_cases h0 : wL x = 0
      · simp only [h0, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
      · simp only [h0, ↓reduceIte, ← Finset.sum_div]
        exact div_self h0
    have hqR1 : ∀ x, ∑ k, qR x k = 1 := fun x => by
      dsimp only [qR]
      by_cases h0 : wR x = 0
      · simp only [h0, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
      · simp only [h0, ↓reduceIte, ← Finset.sum_div]
        exact div_self h0
    alice wL hwL
      (aliceSamplePow d qL hqL0 hqL1 fun k => cont (split (Sum.inl k)))
      (aliceSamplePow d qR hqR0 hqR1 fun k => cont (split (Sum.inr k)))

theorem expect_aliceSamplePow : ∀ (d : ℕ) (p : X → Fin (2 ^ d) → ℝ)
    (hp : ∀ x k, 0 ≤ p x k) (hsum : ∀ x, ∑ k, p x k = 1)
    (cont : Fin (2 ^ d) → RandProtocol X Y) (x : X) (y : Y),
    (aliceSamplePow d p hp hsum cont).expect x y = ∑ k, p x k * (cont k).expect x y
  | 0, p, hp, hsum, cont, x, y => by
    have hu : ∀ k : Fin (2 ^ 0), k = ⟨0, by decide⟩ := fun k => Fin.ext (by have := k.2; omega)
    have hsum' : ∀ f : Fin (2 ^ 0) → ℝ, ∑ k, f k = f ⟨0, by decide⟩ := fun f => by
      rw [Finset.sum_eq_single ⟨0, by decide⟩]
      · intro k _ hk; exact absurd (hu k) hk
      · intro h; exact absurd (Finset.mem_univ _) h
    have h1 : p x ⟨0, by decide⟩ = 1 := by simpa [hsum'] using hsum x
    rw [hsum', h1, one_mul]
    rfl
  | d + 1, p, hp, hsum, cont, x, y => by
    simp only [aliceSamplePow, expect_alice]
    rw [expect_aliceSamplePow d, expect_aliceSamplePow d]
    let split : Fin (2 ^ d) ⊕ Fin (2 ^ d) ≃ Fin (2 ^ (d + 1)) :=
      finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))
    have htot : (∑ k, p x (split (Sum.inl k))) + (∑ k, p x (split (Sum.inr k))) = 1 := by
      have h := (Equiv.sum_comp split (p x)).trans (hsum x)
      rwa [Fintype.sum_sum_type] at h
    have hsub : 1 - ∑ k, p x (split (Sum.inl k)) = ∑ k, p x (split (Sum.inr k)) := by linarith
    change (∑ k, p x (split (Sum.inl k))) *
        (∑ k, (if (∑ j, p x (split (Sum.inl j))) = 0 then
          if k = ⟨0, Nat.two_pow_pos d⟩ then (1 : ℝ) else 0
          else p x (split (Sum.inl k)) / ∑ j, p x (split (Sum.inl j))) *
          (cont (split (Sum.inl k))).expect x y) +
      (1 - ∑ k, p x (split (Sum.inl k))) *
        (∑ k, (if (∑ j, p x (split (Sum.inr j))) = 0 then
          if k = ⟨0, Nat.two_pow_pos d⟩ then (1 : ℝ) else 0
          else p x (split (Sum.inr k)) / ∑ j, p x (split (Sum.inr j))) *
          (cont (split (Sum.inr k))).expect x y) = _
    rw [hsub]
    have hL : (∑ k, p x (split (Sum.inl k))) *
        ∑ k, (if (∑ j, p x (split (Sum.inl j))) = 0 then
          if k = ⟨0, Nat.two_pow_pos d⟩ then (1 : ℝ) else 0
          else p x (split (Sum.inl k)) / ∑ j, p x (split (Sum.inl j))) *
          (cont (split (Sum.inl k))).expect x y =
        ∑ k, p x (split (Sum.inl k)) * (cont (split (Sum.inl k))).expect x y := by
      by_cases h0 : ∑ j, p x (split (Sum.inl j)) = 0
      · rw [h0, zero_mul]
        symm
        refine Finset.sum_eq_zero fun k _ => ?_
        have hk0 : p x (split (Sum.inl k)) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hp x _).1 h0 k (Finset.mem_univ k)
        rw [hk0, zero_mul]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [h0, ↓reduceIte]
        rw [← mul_assoc, mul_div_cancel₀ _ h0]
    have hR : (∑ k, p x (split (Sum.inr k))) *
        ∑ k, (if (∑ j, p x (split (Sum.inr j))) = 0 then
          if k = ⟨0, Nat.two_pow_pos d⟩ then (1 : ℝ) else 0
          else p x (split (Sum.inr k)) / ∑ j, p x (split (Sum.inr j))) *
          (cont (split (Sum.inr k))).expect x y =
        ∑ k, p x (split (Sum.inr k)) * (cont (split (Sum.inr k))).expect x y := by
      by_cases h0 : ∑ j, p x (split (Sum.inr j)) = 0
      · rw [h0, zero_mul]
        symm
        refine Finset.sum_eq_zero fun k _ => ?_
        have hk0 : p x (split (Sum.inr k)) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hp x _).1 h0 k (Finset.mem_univ k)
        rw [hk0, zero_mul]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [h0, ↓reduceIte]
        rw [← mul_assoc, mul_div_cancel₀ _ h0]
    rw [hL, hR]
    rw [← Fintype.sum_sum_type (f := fun s => p x (split s) * (cont (split s)).expect x y)]
    exact Equiv.sum_comp split (fun k => p x k * (cont k).expect x y)

theorem depth_aliceSamplePow_le : ∀ (d : ℕ) (p : X → Fin (2 ^ d) → ℝ)
    (hp : ∀ x k, 0 ≤ p x k) (hsum : ∀ x, ∑ k, p x k = 1)
    (cont : Fin (2 ^ d) → RandProtocol X Y) {c : ℕ} (_ : ∀ k, (cont k).depth ≤ c),
    (aliceSamplePow d p hp hsum cont).depth ≤ d + c
  | 0, _, _, _, cont, _, hc => by simpa [aliceSamplePow] using hc ⟨0, by decide⟩
  | d + 1, p, hp, hsum, cont, c, hc => by
    simp only [aliceSamplePow, depth_alice]
    refine (Nat.add_le_add_right (max_le (c := d + c) ?_ ?_) 1).trans (by omega)
    · exact depth_aliceSamplePow_le d _ _ _ _ fun k => hc _
    · exact depth_aliceSamplePow_le d _ _ _ _ fun k => hc _

theorem isOneWay_aliceSamplePow : ∀ (d : ℕ) (p : X → Fin (2 ^ d) → ℝ)
    (hp : ∀ x k, 0 ≤ p x k) (hsum : ∀ x, ∑ k, p x k = 1)
    (cont : Fin (2 ^ d) → RandProtocol X Y),
    (∀ k, (cont k).IsOneWay) → (aliceSamplePow d p hp hsum cont).IsOneWay
  | 0, _, _, _, cont, hc => hc ⟨0, by decide⟩
  | d + 1, _, _, _, cont, hc =>
    ⟨isOneWay_aliceSamplePow d _ _ _ _ fun k => hc _,
      isOneWay_aliceSamplePow d _ _ _ _ fun k => hc _⟩

/-- Alice samples an element `z` of a finite type `Z` with probability `p x z` using
`⌈log₂ |Z|⌉` bits, then continues with `cont z`. -/
noncomputable def aliceSample {Z : Type*} [Fintype Z] (p : X → Z → ℝ)
    (hp : ∀ x z, 0 ≤ p x z) (hsum : ∀ x, ∑ z, p x z = 1)
    (cont : Z → RandProtocol X Y) : RandProtocol X Y := by
  classical
  let d := Nat.clog 2 (Fintype.card Z)
  let e : Z ↪ Fin (2 ^ d) :=
    (Function.Embedding.nonempty_of_card_le
      ((Fintype.card_fin (2 ^ d)).symm ▸ Nat.le_pow_clog one_lt_two _)).some
  let p' : X → Fin (2 ^ d) → ℝ := fun x k => Function.extend e (p x) 0 k
  have hp' : ∀ x k, 0 ≤ p' x k := fun x k => by
    dsimp only [p']
    by_cases hk : ∃ z, e z = k
    · obtain ⟨z, rfl⟩ := hk
      rw [e.injective.extend_apply]
      exact hp x z
    · rw [Function.extend_apply' _ _ _ hk]
      exact le_rfl
  have hsum' : ∀ x, ∑ k, p' x k = 1 := fun x => by
    dsimp only [p']
    rw [← hsum x]
    symm
    refine Fintype.sum_of_injective e e.injective _ _ ?_ ?_
    · intro k hk
      rw [Function.extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply]
    · intro z
      exact (e.injective.extend_apply _ _ z).symm
  let cont' : Fin (2 ^ d) → RandProtocol X Y := fun k =>
    if h : ∃ z, e z = k then cont h.choose else leaf 0 le_rfl
  exact aliceSamplePow d p' hp' hsum' cont'

theorem expect_aliceSample {Z : Type*} [Fintype Z] (p : X → Z → ℝ)
    (hp : ∀ x z, 0 ≤ p x z) (hsum : ∀ x, ∑ z, p x z = 1)
    (cont : Z → RandProtocol X Y) (x : X) (y : Y) :
    (aliceSample p hp hsum cont).expect x y = ∑ z, p x z * (cont z).expect x y := by
  classical
  unfold aliceSample
  rw [expect_aliceSamplePow]
  set d := Nat.clog 2 (Fintype.card Z)
  set e : Z ↪ Fin (2 ^ d) :=
    (Function.Embedding.nonempty_of_card_le
      ((Fintype.card_fin (2 ^ d)).symm ▸ Nat.le_pow_clog one_lt_two _)).some
  symm
  refine Fintype.sum_of_injective e e.injective _ _ ?_ ?_
  · intro k hk
    have hnot : ¬ ∃ z, e z = k := by simpa using hk
    rw [Function.extend_apply' _ _ _ hnot, Pi.zero_apply, zero_mul]
  · intro z
    rw [e.injective.extend_apply]
    have hex : ∃ z', e z' = e z := ⟨z, rfl⟩
    have hch : hex.choose = z := e.injective hex.choose_spec
    simp only [hex, ↓reduceDIte, hch]

theorem depth_aliceSample_le {Z : Type*} [Fintype Z] (p : X → Z → ℝ)
    (hp : ∀ x z, 0 ≤ p x z) (hsum : ∀ x, ∑ z, p x z = 1)
    (cont : Z → RandProtocol X Y) {c : ℕ} (hc : ∀ z, (cont z).depth ≤ c) :
    (aliceSample p hp hsum cont).depth ≤ Nat.clog 2 (Fintype.card Z) + c := by
  classical
  unfold aliceSample
  refine depth_aliceSamplePow_le _ _ _ _ _ fun k => ?_
  split_ifs
  · exact hc _
  · exact Nat.zero_le c

theorem isOneWay_aliceSample {Z : Type*} [Fintype Z] (p : X → Z → ℝ)
    (hp : ∀ x z, 0 ≤ p x z) (hsum : ∀ x, ∑ z, p x z = 1)
    (cont : Z → RandProtocol X Y) (hc : ∀ z, (cont z).IsOneWay) :
    (aliceSample p hp hsum cont).IsOneWay := by
  classical
  unfold aliceSample
  refine isOneWay_aliceSamplePow _ _ _ _ _ fun k => ?_
  split_ifs
  · exact hc _
  · trivial

/-- Bob samples an element `z` of a finite type `Z` with probability `q y z` using
`⌈log₂ |Z|⌉` bits, then continues with `cont z`. -/
noncomputable def bobSample {Z : Type*} [Fintype Z] (q : Y → Z → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (hsum : ∀ y, ∑ z, q y z = 1)
    (cont : Z → RandProtocol X Y) : RandProtocol X Y :=
  (aliceSample q hq hsum fun z => (cont z).swap).swap

theorem expect_bobSample {Z : Type*} [Fintype Z] (q : Y → Z → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (hsum : ∀ y, ∑ z, q y z = 1)
    (cont : Z → RandProtocol X Y) (x : X) (y : Y) :
    (bobSample q hq hsum cont).expect x y = ∑ z, q y z * (cont z).expect x y := by
  simp [bobSample, expect_aliceSample]

theorem depth_bobSample_le {Z : Type*} [Fintype Z] (q : Y → Z → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (hsum : ∀ y, ∑ z, q y z = 1)
    (cont : Z → RandProtocol X Y) {c : ℕ} (hc : ∀ z, (cont z).depth ≤ c) :
    (bobSample q hq hsum cont).depth ≤ Nat.clog 2 (Fintype.card Z) + c := by
  simpa [bobSample] using depth_aliceSample_le q hq hsum (fun z => (cont z).swap)
    (fun z => by simpa using hc z)

end RandProtocol

end Defs

/-! ### Nonnegative factorizations from randomized protocols -/

section ProtocolToFactorization

variable {X Y : Type*}

/-- Alice's path-traversal probability factor to each leaf of `P`. -/
def RandProtocol.leafAliceProb : (P : RandProtocol X Y) → X → Fin P.leafCount → ℝ
  | .leaf _ _, _, _ => 1
  | .alice p _ l r, x, k =>
    Fin.addCases (fun i => p x * l.leafAliceProb x i)
      (fun j => (1 - p x) * r.leafAliceProb x j) k
  | .bob _ _ l r, x, k =>
    Fin.addCases (l.leafAliceProb x) (r.leafAliceProb x) k

/-- Bob's path-traversal probability factor to each leaf of `P`. -/
def RandProtocol.leafBobProb : (P : RandProtocol X Y) → Y → Fin P.leafCount → ℝ
  | .leaf _ _, _, _ => 1
  | .alice _ _ l r, y, k =>
    Fin.addCases (l.leafBobProb y) (r.leafBobProb y) k
  | .bob q _ l r, y, k =>
    Fin.addCases (fun i => q y * l.leafBobProb y i)
      (fun j => (1 - q y) * r.leafBobProb y j) k

/-- The nonnegative value attached to each leaf of `P`. -/
def RandProtocol.leafVal : (P : RandProtocol X Y) → Fin P.leafCount → ℝ
  | .leaf v _, _ => v
  | .alice _ _ l r, k => Fin.addCases l.leafVal r.leafVal k
  | .bob _ _ l r, k => Fin.addCases l.leafVal r.leafVal k

private theorem leafAliceProb_nonneg (P : RandProtocol X Y) (x : X) (k : Fin P.leafCount) :
    0 ≤ P.leafAliceProb x k := by
  induction P with
  | leaf _ _ => exact zero_le_one
  | alice p hp l r ihl ihr =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.castAdd r.leafCount i)
      rw [Fin.addCases_left]
      exact mul_nonneg (hp x).1 (ihl i)
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.natAdd l.leafCount j)
      rw [Fin.addCases_right]
      exact mul_nonneg (sub_nonneg.2 (hp x).2) (ihr j)
  | bob q hq l r ihl ihr =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.castAdd r.leafCount i)
      rw [Fin.addCases_left]
      exact ihl i
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.natAdd l.leafCount j)
      rw [Fin.addCases_right]
      exact ihr j

private theorem leafBobProb_nonneg (P : RandProtocol X Y) (y : Y) (k : Fin P.leafCount) :
    0 ≤ P.leafBobProb y k := by
  induction P with
  | leaf _ _ => exact zero_le_one
  | alice p hp l r ihl ihr =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.castAdd r.leafCount i)
      rw [Fin.addCases_left]
      exact ihl i
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.natAdd l.leafCount j)
      rw [Fin.addCases_right]
      exact ihr j
  | bob q hq l r ihl ihr =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.castAdd r.leafCount i)
      rw [Fin.addCases_left]
      exact mul_nonneg (hq y).1 (ihl i)
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.natAdd l.leafCount j)
      rw [Fin.addCases_right]
      exact mul_nonneg (sub_nonneg.2 (hq y).2) (ihr j)

private theorem leafVal_nonneg (P : RandProtocol X Y) (k : Fin P.leafCount) :
    0 ≤ P.leafVal k := by
  induction P with
  | leaf _ hv => exact hv
  | alice _ _ l r ihl ihr | bob _ _ l r ihl ihr =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.castAdd r.leafCount i)
      rw [Fin.addCases_left]
      exact ihl i
    · change (0 : ℝ) ≤ Fin.addCases _ _ (Fin.natAdd l.leafCount j)
      rw [Fin.addCases_right]
      exact ihr j

private theorem sum_leaf_mul_eq_expect (P : RandProtocol X Y) (x : X) (y : Y) :
    ∑ k : Fin P.leafCount, (P.leafVal k * P.leafAliceProb x k) * P.leafBobProb y k =
      P.expect x y := by
  induction P with
  | leaf v hv => simp [RandProtocol.leafVal, RandProtocol.leafAliceProb, RandProtocol.leafBobProb]
  | alice p hp l r ihl ihr =>
    change ∑ k : Fin (l.leafCount + r.leafCount),
      (Fin.addCases l.leafVal r.leafVal k *
        Fin.addCases (fun i => p x * l.leafAliceProb x i)
          (fun j => (1 - p x) * r.leafAliceProb x j) k) *
      Fin.addCases (l.leafBobProb y) (r.leafBobProb y) k =
      p x * l.expect x y + (1 - p x) * r.expect x y
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [← ihl, ← ihr, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  | bob q hq l r ihl ihr =>
    change ∑ k : Fin (l.leafCount + r.leafCount),
      (Fin.addCases l.leafVal r.leafVal k *
        Fin.addCases (l.leafAliceProb x) (r.leafAliceProb x) k) *
      Fin.addCases (fun i => q y * l.leafBobProb y i)
        (fun j => (1 - q y) * r.leafBobProb y j) k =
      q y * l.expect x y + (1 - q y) * r.expect x y
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [← ihl, ← ihr, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-- Every randomized protocol yields a nonnegative factorization of its expected output matrix
with inner dimension equal to its number of leaves. -/
theorem RandProtocol.hasNonnegFactorization_of_computesInExpectation {P : RandProtocol X Y}
    {M : Matrix X Y ℝ} (hP : P.ComputesInExpectation M) :
    M.HasNonnegFactorization (Fin P.leafCount) := by
  refine ⟨Matrix.of fun x k => P.leafVal k * P.leafAliceProb x k,
    Matrix.of fun k y => P.leafBobProb y k,
    fun x k => mul_nonneg (leafVal_nonneg P k) (leafAliceProb_nonneg P x k),
    fun k y => leafBobProb_nonneg P y k, Matrix.ext fun x y => ?_⟩
  simpa [Matrix.mul_apply, hP x y] using sum_leaf_mul_eq_expect P x y

/-- If there exists a randomized protocol of
complexity at most `c` computing a nonnegative matrix `M` in expectation, then the nonnegative
rank of `M` is at most `2 ^ c`. -/
theorem nonnegRank_le_two_pow_depth {P : RandProtocol X Y} {M : Matrix X Y ℝ} {c : ℕ}
    (hP : P.ComputesInExpectation M) (hc : P.depth ≤ c) :
    M.nonnegRank ≤ (2 ^ c : ℕ) := by
  have h1 := (P.hasNonnegFactorization_of_computesInExpectation hP).nonnegRank_le
  rw [Fintype.card_fin] at h1
  exact h1.trans (Nat.cast_le.2 (P.leafCount_le_two_pow_depth.trans
    (Nat.pow_le_pow_right two_pos hc)))

end ProtocolToFactorization

/-! ### Row partitions and coordinate-row splitting -/

section PartitionAndSplit

variable {X Y : Type*}

/-- Row-partition lemma: if the rows of `M` are partitioned
into `R₁` and `R₂` and the corresponding submatrices have randomized protocols of complexities
`c₁` and `c₂`, then `M` has a randomized protocol of complexity at most `1 + max c₁ c₂`. -/
theorem exists_randProtocol_of_row_partition {M : Matrix X Y ℝ} (R₁ R₂ : Set X)
    (hdisj : Disjoint R₁ R₂)
    (hcov : R₁ ∪ R₂ = Set.univ) {c₁ c₂ : ℕ}
    (h₁ : ∃ P₁ : RandProtocol R₁ Y, P₁.ComputesInExpectation (M.submatrix Subtype.val id) ∧
      P₁.depth ≤ c₁)
    (h₂ : ∃ P₂ : RandProtocol R₂ Y, P₂.ComputesInExpectation (M.submatrix Subtype.val id) ∧
      P₂.depth ≤ c₂) :
    ∃ P : RandProtocol X Y, P.ComputesInExpectation M ∧ P.depth ≤ 1 + max c₁ c₂ := by
  classical
  obtain ⟨P₁, hP₁, hd₁⟩ := h₁
  obtain ⟨P₂, hP₂, hd₂⟩ := h₂
  rcases Set.eq_empty_or_nonempty R₁ with rfl | ⟨x₁, hx₁⟩
  · have hR₂ : ∀ x : X, x ∈ R₂ := fun x => by
      have : x ∈ (∅ : Set X) ∪ R₂ := hcov ▸ Set.mem_univ x
      simpa using this
    refine ⟨P₂.comap (fun x => ⟨x, hR₂ x⟩) id, fun x y => by simpa using hP₂ ⟨x, hR₂ x⟩ y, ?_⟩
    simp only [RandProtocol.depth_comap]
    omega
  rcases Set.eq_empty_or_nonempty R₂ with rfl | ⟨x₂, hx₂⟩
  · have hR₁ : ∀ x : X, x ∈ R₁ := fun x => by
      have : x ∈ R₁ ∪ (∅ : Set X) := hcov ▸ Set.mem_univ x
      simpa using this
    refine ⟨P₁.comap (fun x => ⟨x, hR₁ x⟩) id, fun x y => by simpa using hP₁ ⟨x, hR₁ x⟩ y, ?_⟩
    simp only [RandProtocol.depth_comap]
    omega
  let toR₁ : X → R₁ := fun x => if hx : x ∈ R₁ then ⟨x, hx⟩ else ⟨x₁, hx₁⟩
  let toR₂ : X → R₂ := fun x => if hx : x ∈ R₂ then ⟨x, hx⟩ else ⟨x₂, hx₂⟩
  refine ⟨RandProtocol.aliceDet (fun x => decide (x ∉ R₁)) (P₁.comap toR₁ id) (P₂.comap toR₂ id),
    fun x y => ?_, ?_⟩
  · by_cases hx : x ∈ R₁
    · simp [hx, toR₁, hP₁ ⟨x, hx⟩ y]
    · have hx₂' : x ∈ R₂ := by
        have hmem : x ∈ R₁ ∪ R₂ := hcov ▸ Set.mem_univ x
        exact hmem.resolve_left hx
      simp [hx, hx₂', toR₂, hP₂ ⟨x, hx₂'⟩ y]
  · simp only [RandProtocol.depth_aliceDet, RandProtocol.depth_comap]
    omega

/-- Coordinate-row splitting: splitting a nonnegative matrix into at most `d` nonnegative rows
and a remaining submatrix of complexity `c` yields a randomized protocol of complexity at most
`1 + max c (⌈log₂ d⌉ + 1)` (tight by `exists_simplex_no_depth_two_randProtocol`). -/
theorem exists_randProtocol_split_nonneg {ι μ : Type*} [Fintype μ] [Finite Y]
    (M : Matrix (μ ⊕ ι) Y ℝ) (hM : ∀ i y, 0 ≤ M (Sum.inl i) y) {d c : ℕ}
    (hcard : Fintype.card μ ≤ d)
    (h' : ∃ P' : RandProtocol ι Y, P'.ComputesInExpectation (M.submatrix Sum.inr id) ∧
      P'.depth ≤ c) :
    ∃ P : RandProtocol (μ ⊕ ι) Y, P.ComputesInExpectation M ∧
      P.depth ≤ 1 + max c (Nat.clog 2 d + 1) := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  obtain ⟨P', hP', hc⟩ := h'
  rcases isEmpty_or_nonempty μ with hμ | hμ
  · refine ⟨P'.comap (Sum.elim hμ.elim id) id, fun x y => ?_, ?_⟩
    · rcases x with i | i
      · exact hμ.elim i
      · simpa using hP' i y
    · simp only [RandProtocol.depth_comap]
      omega
  have hY : ∃ P₀ : RandProtocol μ Y, P₀.ComputesInExpectation (M.submatrix Sum.inl id) ∧
      P₀.depth ≤ Nat.clog 2 d + 1 := by
    rcases isEmpty_or_nonempty Y with hY | hY
    · refine ⟨RandProtocol.leaf 0 le_rfl, fun _ y => hY.elim y, Nat.zero_le _⟩
    let B : μ → ℝ := fun i => Finset.univ.sup' Finset.univ_nonempty (fun y => M (Sum.inl i) y)
    have hB : ∀ i y, 0 ≤ M (Sum.inl i) y ∧ M (Sum.inl i) y ≤ B i := fun i y =>
      ⟨hM i y, Finset.le_sup' (fun y => M (Sum.inl i) y) (Finset.mem_univ y)⟩
    have hB0 : ∀ i, 0 ≤ B i := fun i =>
      (hB i (Classical.arbitrary Y)).1.trans (hB i (Classical.arbitrary Y)).2
    let P₀ : RandProtocol μ Y := RandProtocol.aliceSendFin id fun i =>
      RandProtocol.bobOutputVal (fun y => M (Sum.inl i) y) (B i) (hB0 i) (hB i)
    refine ⟨P₀, fun i y => ?_, ?_⟩
    · simp [P₀, RandProtocol.expect_aliceSendFin]
    · refine (RandProtocol.depth_aliceSendFin_le _ _ fun i =>
        RandProtocol.depth_bobOutputVal_le _ _ _ _).trans ?_
      have hclog : Nat.clog 2 (Fintype.card μ) ≤ Nat.clog 2 d := Nat.clog_mono_right 2 hcard
      omega
  obtain ⟨P₀, hP₀, hd₀⟩ := hY
  have hdisj : Disjoint (Set.range (Sum.inl : μ → μ ⊕ ι)) (Set.range (Sum.inr : ι → μ ⊕ ι)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, h⟩
    cases h
  have hcov : Set.range (Sum.inl : μ → μ ⊕ ι) ∪ Set.range (Sum.inr : ι → μ ⊕ ι) = Set.univ := by
    ext (i | j) <;> simp
  obtain ⟨P, hP, hd⟩ := exists_randProtocol_of_row_partition _ _ hdisj hcov
    ⟨P₀.comap (fun x => x.2.choose) id, fun x y => by
      have hx := x.2.choose_spec
      rw [RandProtocol.expect_comap]
      simpa [id_eq, hx] using hP₀ x.2.choose y, by simpa using hd₀⟩
    ⟨P'.comap (fun x => x.2.choose) id, fun x y => by
      have hx := x.2.choose_spec
      rw [RandProtocol.expect_comap]
      simpa [id_eq, hx] using hP' x.2.choose y, by simpa using hc⟩
  exact ⟨P, hP, hd.trans (by omega)⟩

/-- Polytope slack-matrix splitting: if `P ⊆ ℝ₊ᵈ` has nonnegative coordinate slacks on `Fin d`
and remaining inequalities indexed by `ι` whose sub-slack matrix has a randomized protocol of depth
at most `c`, then the full slack matrix has a randomized protocol of depth at most
`1 + max c (⌈log₂ d⌉ + 1)`. -/
theorem exists_randProtocol_split_polytope {d c : ℕ} {ι ν : Type*} [Finite ν]
    (A' : Matrix ι (Fin d) ℝ) (b' : ι → ℝ) (V : ν → Fin d → ℝ)
    (hnonneg : ∀ j i, 0 ≤ V j i)
    (h' : ∃ P' : RandProtocol ι ν,
      P'.ComputesInExpectation (A'.slackMatrix b' V) ∧ P'.depth ≤ c) :
    ∃ P : RandProtocol (Fin d ⊕ ι) ν,
      P.ComputesInExpectation
        ((Matrix.fromRows (-1 : Matrix (Fin d) (Fin d) ℝ) A').slackMatrix (Sum.elim 0 b') V) ∧
      P.depth ≤ 1 + max c (Nat.clog 2 d + 1) := by
  refine exists_randProtocol_split_nonneg
    ((Matrix.fromRows (-1 : Matrix (Fin d) (Fin d) ℝ) A').slackMatrix (Sum.elim 0 b') V)
    (fun i j => ?_) (by simp) ?_
  · rw [Matrix.slackMatrix_apply]
    change 0 ≤ 0 - ((-1 : Matrix (Fin d) (Fin d) ℝ).fromRows A' *ᵥ V j) (Sum.inl i)
    rw [Matrix.fromRows_mulVec]
    simp [Matrix.neg_mulVec, Matrix.one_mulVec, hnonneg j i]
  · obtain ⟨P', hP', hc⟩ := h'
    refine ⟨P', fun i j => ?_, hc⟩
    rw [Matrix.submatrix_apply, id_eq, Matrix.slackMatrix_apply]
    change P'.expect i j =
      b' i - ((-1 : Matrix (Fin d) (Fin d) ℝ).fromRows A' *ᵥ V j) (Sum.inr i)
    rw [Matrix.fromRows_mulVec]
    simpa [Matrix.slackMatrix_apply, Matrix.mulVec] using hP' i j

/-- A depth-1 randomized protocol whose expectation vanishes on off-diagonal entries of a subset `S`
of size at least `2` must vanish on the diagonal of `S`. -/
private theorem depth_le_one_diag_zero_of_two_offdiag {T : RandProtocol (Fin 3) (Fin 3)}
    (hd : T.depth ≤ 1) {S : Finset (Fin 3)} (hS : 2 ≤ S.card)
    (hoff : ∀ i ∈ S, ∀ j : Fin 3, j ≠ i → T.expect i j = 0) :
    ∀ i ∈ S, T.expect i i = 0 := by
  cases T with
  | leaf v hv =>
    obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    have hv0 : v = 0 := hoff i₁ hi₁ i₂ hne.symm
    intro i _
    exact hv0
  | alice p hp l r =>
    simp only [RandProtocol.depth_alice] at hd
    have hl : l.depth = 0 := by omega
    have hr : r.depth = 0 := by omega
    cases l with
    | leaf vl hvl =>
      cases r with
      | leaf vr hvr =>
        intro i hi
        have hex : ∃ j : Fin 3, j ≠ i := by
          fin_cases i
          · exact ⟨1, by decide⟩
          · exact ⟨0, by decide⟩
          · exact ⟨0, by decide⟩
        obtain ⟨j, hji⟩ := hex
        simpa [RandProtocol.expect_alice, RandProtocol.expect_leaf] using hoff i hi j hji
      | alice _ _ _ _ | bob _ _ _ _ => simp at hr
    | alice _ _ _ _ | bob _ _ _ _ => simp at hl
  | bob q hq l r =>
    simp only [RandProtocol.depth_bob] at hd
    have hl : l.depth = 0 := by omega
    have hr : r.depth = 0 := by omega
    cases l with
    | leaf vl hvl =>
      cases r with
      | leaf vr hvr =>
        intro i hi
        obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
        have hex : ∃ i' ∈ S, i' ≠ i := by
          by_cases h1 : i₁ = i
          · exact ⟨i₂, hi₂, h1 ▸ hne.symm⟩
          · exact ⟨i₁, hi₁, h1⟩
        obtain ⟨i', hi'S, hi'ne⟩ := hex
        simpa [RandProtocol.expect_bob, RandProtocol.expect_leaf] using hoff i' hi'S i hi'ne.symm
      | alice _ _ _ _ | bob _ _ _ _ => simp at hr
    | alice _ _ _ _ | bob _ _ _ _ => simp at hl

/-- No randomized protocol of depth at most `2` computes the `3 × 3` identity matrix `I₃` in
expectation. -/
private theorem not_exists_randProtocol_depth_le_two_id3 :
    ¬ ∃ P : RandProtocol (Fin 3) (Fin 3),
      P.ComputesInExpectation (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧ P.depth ≤ 2 := by
  rintro ⟨P, hP, hd⟩
  have hmain : ∀ Q : RandProtocol (Fin 3) (Fin 3),
      Q.ComputesInExpectation (1 : Matrix (Fin 3) (Fin 3) ℝ) → Q.depth ≤ 2 →
      (∀ (p : Fin 3 → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1) (l r : RandProtocol (Fin 3) (Fin 3)),
        Q = RandProtocol.alice p hp l r → False) := by
    intro Q hQ hQd p hp l r hEq
    subst hEq
    simp only [RandProtocol.depth_alice] at hQd
    have hld : l.depth ≤ 1 := by omega
    have hrd : r.depth ≤ 1 := by omega
    let SL : Finset (Fin 3) := Finset.univ.filter fun i => 0 < p i
    let SR : Finset (Fin 3) := Finset.univ.filter fun i => p i < 1
    have hoffL : ∀ i ∈ SL, ∀ j : Fin 3, j ≠ i → l.expect i j = 0 := by
      intro i hi j hji
      have hpi : 0 < p i := (Finset.mem_filter.1 hi).2
      have h0 : (RandProtocol.alice p hp l r).expect i j = 0 := by
        simpa [Matrix.one_apply, hji.symm] using hQ i j
      simp only [RandProtocol.expect_alice] at h0
      have hr0 : 0 ≤ (1 - p i) * r.expect i j :=
        mul_nonneg (sub_nonneg.2 (hp i).2) (r.expect_nonneg i j)
      have hl0 : 0 ≤ l.expect i j := l.expect_nonneg i j
      nlinarith
    have hoffR : ∀ i ∈ SR, ∀ j : Fin 3, j ≠ i → r.expect i j = 0 := by
      intro i hi j hji
      have hpi : p i < 1 := (Finset.mem_filter.1 hi).2
      have h0 : (RandProtocol.alice p hp l r).expect i j = 0 := by
        simpa [Matrix.one_apply, hji.symm] using hQ i j
      simp only [RandProtocol.expect_alice] at h0
      have hl0 : 0 ≤ p i * l.expect i j := mul_nonneg (hp i).1 (l.expect_nonneg i j)
      have hr0 : 0 ≤ r.expect i j := r.expect_nonneg i j
      nlinarith
    let PL : Finset (Fin 3) := Finset.univ.filter fun i => 0 < p i * l.expect i i
    let PR : Finset (Fin 3) := Finset.univ.filter fun i => 0 < (1 - p i) * r.expect i i
    have hPL_le : PL.card ≤ 1 := by
      by_cases h2 : 2 ≤ SL.card
      · have hzero := depth_le_one_diag_zero_of_two_offdiag hld h2 hoffL
        have hPL0 : PL = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
          have hpos : 0 < p i * l.expect i i := (Finset.mem_filter.1 hi).2
          have hpi : 0 < p i := by
            by_contra hle
            have hp0 : p i = 0 := le_antisymm (not_lt.1 hle) (hp i).1
            simp [hp0] at hpos
          have hiSL : i ∈ SL := Finset.mem_filter.2 ⟨Finset.mem_univ i, hpi⟩
          rw [hzero i hiSL, mul_zero] at hpos
          exact lt_irrefl 0 hpos
        simp [hPL0]
      · have hsub : PL ⊆ SL := fun i hi => by
          have hpos : 0 < p i * l.expect i i := (Finset.mem_filter.1 hi).2
          have hpi : 0 < p i := by
            by_contra hle
            have hp0 : p i = 0 := le_antisymm (not_lt.1 hle) (hp i).1
            simp [hp0] at hpos
          exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hpi⟩
        exact (Finset.card_le_card hsub).trans (by omega)
    have hPR_le : PR.card ≤ 1 := by
      by_cases h2 : 2 ≤ SR.card
      · have hzero := depth_le_one_diag_zero_of_two_offdiag hrd h2 hoffR
        have hPR0 : PR = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
          have hpos : 0 < (1 - p i) * r.expect i i := (Finset.mem_filter.1 hi).2
          have hpi : p i < 1 := by
            by_contra hge
            have hp1 : p i = 1 := le_antisymm (hp i).2 (not_lt.1 hge)
            simp [hp1] at hpos
          have hiSR : i ∈ SR := Finset.mem_filter.2 ⟨Finset.mem_univ i, hpi⟩
          rw [hzero i hiSR, mul_zero] at hpos
          exact lt_irrefl 0 hpos
        simp [hPR0]
      · have hsub : PR ⊆ SR := fun i hi => by
          have hpos : 0 < (1 - p i) * r.expect i i := (Finset.mem_filter.1 hi).2
          have hpi : p i < 1 := by
            by_contra hge
            have hp1 : p i = 1 := le_antisymm (hp i).2 (not_lt.1 hge)
            simp [hp1] at hpos
          exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hpi⟩
        exact (Finset.card_le_card hsub).trans (by omega)
    have hcov : (Finset.univ : Finset (Fin 3)) ⊆ PL ∪ PR := fun i _ => by
      have h1 : p i * l.expect i i + (1 - p i) * r.expect i i = 1 := by
        simpa [RandProtocol.expect_alice] using hQ i i
      have ha : 0 ≤ p i * l.expect i i := mul_nonneg (hp i).1 (l.expect_nonneg i i)
      have hb : 0 ≤ (1 - p i) * r.expect i i :=
        mul_nonneg (sub_nonneg.2 (hp i).2) (r.expect_nonneg i i)
      rw [Finset.mem_union]
      by_cases hpos : 0 < p i * l.expect i i
      · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ i, hpos⟩)
      · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ i, by linarith⟩)
    have h3 : 3 ≤ (PL ∪ PR).card := by
      simpa using Finset.card_le_card hcov
    have hu : (PL ∪ PR).card ≤ PL.card + PR.card := Finset.card_union_le PL PR
    omega
  cases P with
  | leaf v hv =>
    have h00 : v = 1 := by simpa using hP 0 0
    have h01 : v = 0 := by simpa using hP 0 1
    linarith
  | alice p hp l r => exact hmain _ hP hd p hp l r rfl
  | bob q hq l r =>
    have hswap : (RandProtocol.bob q hq l r).swap.ComputesInExpectation
        (1 : Matrix (Fin 3) (Fin 3) ℝ) := fun x y => by
      rw [RandProtocol.expect_swap, hP y x]
      simp [Matrix.one_apply, eq_comm]
    exact hmain _ hswap (by simpa using hd) q hq l.swap r.swap rfl

/-- Tightness of the `+ 1` bit in coordinate-row splitting: for the standard 2-simplex
`Δ₂ = {x ∈ ℝ₊² : x₀ + x₁ ≤ 1}` (`d = 2`, `⌈log₂ d⌉ = 1`), the non-trivial facet has a depth-1
randomized protocol, yet no depth-2 randomized protocol computes the full slack matrix `I₃`. -/
theorem exists_simplex_no_depth_two_randProtocol :
    let d := 2
    let A' : Matrix Unit (Fin d) ℝ := Matrix.of fun _ _ => 1
    let b' : Unit → ℝ := fun _ => 1
    let A : Matrix (Fin d ⊕ Unit) (Fin d) ℝ := Matrix.fromRows (-1 : Matrix (Fin d) (Fin d) ℝ) A'
    let b : Fin d ⊕ Unit → ℝ := Sum.elim 0 b'
    let V : Fin 3 → Fin d → ℝ := fun j =>
      match j with
      | 0 => ![1, 0]
      | 1 => ![0, 1]
      | 2 => ![0, 0]
    let P : Set (Fin d → ℝ) := {x | A *ᵥ x ≤ b}
    P = convexHull ℝ (Set.range V) ∧
    (∀ x ∈ P, ∀ i, 0 ≤ x i) ∧
    (∃ P' : RandProtocol Unit (Fin 3),
      P'.ComputesInExpectation (A'.slackMatrix b' V) ∧ P'.depth ≤ 1) ∧
    ¬ ∃ Q : RandProtocol (Fin d ⊕ Unit) (Fin 3),
      Q.ComputesInExpectation (A.slackMatrix b V) ∧ Q.depth ≤ 1 + max 1 (Nat.clog 2 d) := by
  intro d A' b' A b V P
  have hP_iff : ∀ x : Fin 2 → ℝ, x ∈ P ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
    intro x
    change A *ᵥ x ≤ b ↔ _
    simp only [A, b, A', b', Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
      Pi.le_def]
    constructor
    · intro h
      have h0 := h (Sum.inl 0)
      have h1 := h (Sum.inl 1)
      have h2 := h (Sum.inr ())
      simp only [d, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply,
        Left.neg_nonpos_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        one_mul] at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩ (i | u)
      · fin_cases i <;> simp [h0, h1]
      · simp [d, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h2]
  have hPV : P = convexHull ℝ (Set.range V) := by
    refine Set.Subset.antisymm ?_ (convexHull_min ?_ ?_)
    · intro x hx
      obtain ⟨hx0, hx1, hxsum⟩ := (hP_iff x).1 hx
      have hcomb : x = x 0 • V 0 + x 1 • V 1 + (1 - x 0 - x 1) • V 2 := by
        ext i
        fin_cases i <;> simp [V]
      rw [hcomb]
      have hw : x 0 + x 1 + (1 - x 0 - x 1) = 1 := by ring
      have hmem : ∀ j : Fin 3, V j ∈ convexHull ℝ (Set.range V) :=
        fun j => subset_convexHull ℝ _ ⟨j, rfl⟩
      have hconv := convex_convexHull ℝ (Set.range V)
      have hsum : x 0 • V 0 + x 1 • V 1 + (1 - x 0 - x 1) • V 2 =
          ∑ j : Fin 3, (![x 0, x 1, 1 - x 0 - x 1] j) • V j := by
        simp [Fin.sum_univ_three]
      rw [hsum]
      exact hconv.sum_mem (fun j _ => by fin_cases j <;> simp <;> linarith)
        (by
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val]
          ring)
        (fun j _ => hmem j)
    · rintro _ ⟨j, rfl⟩
      rw [hP_iff]
      fin_cases j <;> simp [V]
    · intro x hx y hy a c ha hc hac
      rw [hP_iff] at hx hy ⊢
      refine ⟨by simp; nlinarith, by simp; nlinarith, by simp; nlinarith⟩
  have hnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i := fun x hx i => by
    obtain ⟨h0, h1, _⟩ := (hP_iff x).1 hx
    fin_cases i <;> assumption
  have hS' : ∃ P' : RandProtocol Unit (Fin 3),
      P'.ComputesInExpectation (A'.slackMatrix b' V) ∧ P'.depth ≤ 1 := by
    refine ⟨RandProtocol.bobDet (fun j : Fin 3 => decide (j = 2))
      (RandProtocol.leaf 0 le_rfl) (RandProtocol.leaf 1 zero_le_one), fun _ j => ?_, by simp⟩
    fin_cases j <;> simp [d, A', b', V, Matrix.slackMatrix_apply, dotProduct, Fin.sum_univ_two]
  have hno : ¬ ∃ Q : RandProtocol (Fin d ⊕ Unit) (Fin 3),
      Q.ComputesInExpectation (A.slackMatrix b V) ∧ Q.depth ≤ 1 + max 1 (Nat.clog 2 d) := by
    rintro ⟨Q, hQ, hQd⟩
    have hclog : Nat.clog 2 d = 1 := by decide
    rw [hclog] at hQd
    let e : Fin 3 → Fin d ⊕ Unit := fun i =>
      match i with
      | 0 => Sum.inl 0
      | 1 => Sum.inl 1
      | 2 => Sum.inr ()
    refine not_exists_randProtocol_depth_le_two_id3 ⟨Q.comap e id, fun i j => ?_, by
      simpa using hQd⟩
    simp only [RandProtocol.expect_comap, id_eq]
    rw [hQ (e i) j]
    fin_cases i <;> fin_cases j <;>
      simp [d, e, A, b, A', b', V, Matrix.slackMatrix_apply, dotProduct, Fin.sum_univ_two,
        Matrix.one_apply]
  exact ⟨hPV, hnonneg, hS', hno⟩

end PartitionAndSplit

/-! ### One-way randomized protocols from nonnegative factorizations -/

section FactorizationToProtocol

variable {X Y : Type*}

/-- If a nonnegative matrix `M` admits a
rank-`r` nonnegative factorization, then there exists a one-way randomized protocol computing `M`
in expectation of complexity at most `⌈log₂ (r + 1)⌉ + 1`. -/
theorem exists_oneWay_randProtocol_of_nonnegFactorization [Finite X] [Finite Y]
    {M : Matrix X Y ℝ} {r : ℕ}
    (hfac : M.HasNonnegFactorization (Fin r)) :
    ∃ P : RandProtocol X Y, P.ComputesInExpectation M ∧ P.IsOneWay ∧
      P.depth ≤ Nat.clog 2 (r + 1) + 1 := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let _ : Fintype Y := Fintype.ofFinite Y
  obtain ⟨A, B, hA, hB, rfl⟩ := hfac
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨RandProtocol.leaf 0 le_rfl, fun x => hX.elim x, trivial, Nat.zero_le _⟩
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨RandProtocol.leaf 0 le_rfl, fun _ y => hY.elim y, trivial, Nat.zero_le _⟩
  let rowSum : X → ℝ := fun i => ∑ k : Fin r, A i k
  let Δ : ℝ := Finset.univ.sup' Finset.univ_nonempty rowSum
  have hrow_nonneg : ∀ i, 0 ≤ rowSum i := fun i => Finset.sum_nonneg fun k _ => hA i k
  have hrow_le : ∀ i, rowSum i ≤ Δ := fun i => Finset.le_sup' rowSum (Finset.mem_univ i)
  have hΔ0 : 0 ≤ Δ := (hrow_nonneg (Classical.arbitrary X)).trans (hrow_le _)
  by_cases hΔ : Δ = 0
  · refine ⟨RandProtocol.leaf 0 le_rfl, fun i j => ?_, trivial, Nat.zero_le _⟩
    have hsum0 : rowSum i = 0 := le_antisymm (hΔ ▸ hrow_le i) (hrow_nonneg i)
    have hAi0 : ∀ k : Fin r, A i k = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg fun k' _ => hA i k').1 hsum0 k (Finset.mem_univ k)
    simp [Matrix.mul_apply, hAi0]
  have hΔpos : 0 < Δ := lt_of_le_of_ne hΔ0 (Ne.symm hΔ)
  -- Construct row-stochastic `Ahat : X → Fin (r + 1) → ℝ` and scaled `Bhat : Fin (r + 1) → Y → ℝ`.
  let Ahat : X → Fin (r + 1) → ℝ := fun i k =>
    Fin.lastCases (1 - rowSum i / Δ) (fun k' => A i k' / Δ) k
  let Bhat : Fin (r + 1) → Y → ℝ := fun k j =>
    Fin.lastCases 0 (fun k' => Δ * B k' j) k
  have hAhat0 : ∀ i k, 0 ≤ Ahat i k := fun i k => by
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp only [Ahat, Fin.lastCases_last, sub_nonneg]
      exact (div_le_one hΔpos).2 (hrow_le i)
    · simp only [Ahat, Fin.lastCases_castSucc]
      exact div_nonneg (hA i k') hΔ0
  have hAhat_sum : ∀ i, ∑ k : Fin (r + 1), Ahat i k = 1 := fun i => by
    rw [Fin.sum_univ_castSucc]
    simp only [Ahat, Fin.lastCases_castSucc, Fin.lastCases_last, ← Finset.sum_div]
    change rowSum i / Δ + (1 - rowSum i / Δ) = 1
    ring
  have hBhat0 : ∀ k j, 0 ≤ Bhat k j := fun k j => by
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp [Bhat]
    · simp only [Bhat, Fin.lastCases_castSucc]
      exact mul_nonneg hΔ0 (hB k' j)
  let Mcol : Fin (r + 1) → ℝ := fun k => Finset.univ.sup' Finset.univ_nonempty (fun j => Bhat k j)
  have hMcol : ∀ k j, 0 ≤ Bhat k j ∧ Bhat k j ≤ Mcol k := fun k j =>
    ⟨hBhat0 k j, Finset.le_sup' (fun j => Bhat k j) (Finset.mem_univ j)⟩
  have hMcol0 : ∀ k, 0 ≤ Mcol k := fun k =>
    (hMcol k (Classical.arbitrary Y)).1.trans (hMcol k (Classical.arbitrary Y)).2
  let P : RandProtocol X Y :=
    RandProtocol.aliceSample Ahat hAhat0 hAhat_sum fun k =>
      RandProtocol.bobOutputVal (Bhat k) (Mcol k) (hMcol0 k) (hMcol k)
  refine ⟨P, fun i j => ?_, ?_, ?_⟩
  · simp only [P, RandProtocol.expect_aliceSample, RandProtocol.expect_bobOutputVal,
      Fin.sum_univ_castSucc, Ahat, Bhat, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero,
      add_zero, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  · exact RandProtocol.isOneWay_aliceSample _ _ _ _ fun k => by
      have hb := RandProtocol.isBobOnly_bobOutputVal (X := X) (Bhat k) (Mcol k) (hMcol0 k)
        (hMcol k)
      cases hP : RandProtocol.bobOutputVal (X := X) (Bhat k) (Mcol k) (hMcol0 k) (hMcol k) with
      | leaf _ _ => trivial
      | alice _ _ _ _ => simp [hP, RandProtocol.IsBobOnly] at hb
      | bob _ _ _ _ => simpa [hP, RandProtocol.IsBobOnly, RandProtocol.IsOneWay] using hb
  · simpa [Fintype.card_fin] using RandProtocol.depth_aliceSample_le Ahat hAhat0 hAhat_sum
      (fun k => RandProtocol.bobOutputVal (Bhat k) (Mcol k) (hMcol0 k) (hMcol k))
      (fun k => RandProtocol.depth_bobOutputVal_le _ _ _ _)

/-- Real-logarithm bound: for `1 ≤ r`,
`⌈log₂ (r + 1)⌉ + 1 ≤ log₂ r + 3`. -/
theorem clog_succ_add_one_le_logb_add_three {r : ℕ} (hr : 1 ≤ r) :
    ((Nat.clog 2 (r + 1) + 1 : ℕ) : ℝ) ≤ Real.logb 2 (r : ℝ) + 3 := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h1 : Nat.clog 2 (r + 1) ≤ Nat.log 2 r + 2 := by
    refine Nat.clog_le_of_le_pow ?_
    have hlt : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self one_lt_two r
    have hpow : 2 ^ (Nat.log 2 r + 1) ≤ 2 ^ (Nat.log 2 r + 2) :=
      Nat.pow_le_pow_right two_pos (by omega)
    omega
  have h2 : (Nat.log 2 r : ℝ) ≤ Real.logb 2 (r : ℝ) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hrpos]
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h1R : (Nat.clog 2 (r + 1) : ℝ) ≤ (Nat.log 2 r : ℝ) + 2 := by exact_mod_cast h1
  push_cast
  linarith

/-- Minimum complexity of a randomized protocol computing `M` in expectation. -/
noncomputable def minRandComplexity (M : Matrix X Y ℝ) : ℕ∞ :=
  ⨅ P : {P : RandProtocol X Y // P.ComputesInExpectation M}, (P.1.depth : ℕ∞)

/-- Upper bound characterizing `log₂ (rank₊ M)` up to additive constants:
`M.nonnegRank ≤ 2 ^ c` for any randomized protocol of depth `c`, and for finite matrices with
`M.nonnegRank = r`, `minRandComplexity M ≤ ⌈log₂ (r + 1)⌉ + 1`. -/
theorem minRandComplexity_le_clog_succ_add_one [Finite X] [Finite Y] {M : Matrix X Y ℝ} {r : ℕ}
    (hr : M.nonnegRank ≤ r) :
    minRandComplexity M ≤ (Nat.clog 2 (r + 1) + 1 : ℕ) := by
  obtain ⟨P, hP, _, hd⟩ :=
    exists_oneWay_randProtocol_of_nonnegFactorization (Matrix.nonnegRank_le_iff.1 hr)
  exact (iInf_le (fun Q : {Q : RandProtocol X Y // Q.ComputesInExpectation M} => (Q.1.depth : ℕ∞))
    ⟨P, hP⟩).trans (by exact_mod_cast hd)

/-- Lower bound half of the characterization: if `minRandComplexity M ≤ c`, then
`M.nonnegRank ≤ 2 ^ c`. -/
theorem nonnegRank_le_two_pow_of_minRandComplexity_le {M : Matrix X Y ℝ} {c : ℕ}
    (hc : minRandComplexity M ≤ c) : M.nonnegRank ≤ (2 ^ c : ℕ) := by
  have hex : ∃ P : RandProtocol X Y, P.ComputesInExpectation M ∧ P.depth ≤ c := by
    by_contra h
    push Not at h
    have hge : ((c + 1 : ℕ) : ℕ∞) ≤ minRandComplexity M := by
      refine le_iInf fun ⟨P, hP⟩ => ?_
      exact_mod_cast Nat.succ_le_of_lt (h P hP)
    have hle := hge.trans hc
    have hnat : c + 1 ≤ c := by exact_mod_cast hle
    omega
  obtain ⟨P, hP, hd⟩ := hex
  exact nonnegRank_le_two_pow_depth hP hd

end FactorizationToProtocol


end CslibFrontier.Communication
