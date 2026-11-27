/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import Cslib.Probability.PMF
public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.Communication.Randomized
public import CslibFrontier.Computability.Communication.Rank
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Basic.Real.Basic
public import CslibFrontier.Computability.Communication.FactorizationNorm

import CslibFrontier.Computability.Communication.Amplification
import CslibFrontier.Computability.Communication.Rectangle
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parity Decision Trees and Boolean Fourier Spectral Norms

This module develops deterministic and randomized parity decision trees, exact and approximate
Fourier `ℓ₁` spectral norms on the Boolean cube, and their connections to XOR communication
protocols and the matrix `γ₂` factorization norm under standard Lean axioms.

## Main definitions

* `CslibFrontier.ParityDecisionTree`: deterministic decision trees querying parities
`Cslib.parityOn S`.
* `CslibFrontier.ParityDecisionTree.pdtDepth`, `CslibFrontier.ParityDecisionTree.pdtSize`: minimum
depth and
  leaf count of a deterministic parity decision tree computing a Boolean-cube function.
* `CslibFrontier.RandomizedPDT`: distributions (`PMF`) over parity decision trees, with `depth`,
  `leafCount`, `errorProb`, `Computes`, `rpdtDepth`, `rpdtSize`, and one-sided AND repetition.
* `CslibFrontier.ParityDecisionTree.toXorProtocol`: deterministic communication protocol simulating
a
  parity decision tree on the XOR problem `(x, y) ↦ f (x + y)` with at most twice the depth.
* `CslibFrontier.BooleanAnalysis.fourierSpectralNorm`: exact Fourier spectral norm
  `‖f̂‖₁ = ∑ S, |fourierCoeff f S|`.
* `CslibFrontier.BooleanAnalysis.approxSpectralNorm`: `ε`-approximate Fourier spectral norm
  `‖f̂‖_{1,ε} = inf { ‖ĝ‖₁ | ∀ x, |f x - g x| < ε }`.

## Main results

* `CslibFrontier.RandomizedPDT.publicCoin_xor_le_two_mul_rpdtDepth`: public-coin randomized
  communication complexity of `f (x + y)` is at most twice the randomized parity decision tree
  depth of `f`.
* `CslibFrontier.BooleanAnalysis.fourierSpectralNorm_affineIndicator_le_one`: the `{0,1}` indicator
of
  any affine subspace of `{0,1}^ι` has Fourier spectral norm at most `1`.
* `CslibFrontier.BooleanAnalysis.fourierSpectralNorm_le_pdtSize`: the Fourier spectral norm of a
  Boolean function is at most its deterministic parity decision tree size.
* `CslibFrontier.BooleanAnalysis.gamma2Norm_xor_eq_fourierSpectralNorm`: for every `f : (ι → Bool)
→ ℝ`,
  the `γ₂` factorization norm of `(x, y) ↦ f (x + y)` equals `fourierSpectralNorm f`
.
* `CslibFrontier.BooleanAnalysis.approxSpectralNorm_le_two_pow_publicCoin`: for `0 ≤ ε' < ε`, if the
  public-coin communication cost of `(x, y) ↦ f (x + y)` at error `ε'` is at most `c`, then
  `approxSpectralNorm ε (bitVal ℝ ∘ f) ≤ 2 ^ c`
.
-/

public section

open Finset Cslib Cslib.BitString Cslib.Communication
open scoped BigOperators ENNReal

namespace CslibFrontier

/-- A deterministic parity decision tree over coordinates `ι` with leaf values in `β`: each
internal node queries the parity `Cslib.parityOn coords x` of a finite set of input bits. -/
inductive ParityDecisionTree (ι β : Type*) where
  /-- Return a constant output value without further queries. -/
  | leaf (val : β)
  /-- Query `Cslib.parityOn coords x` and branch to `onFalse` (even) or `onTrue` (odd). -/
  | query (coords : Finset ι) (onFalse onTrue : ParityDecisionTree ι β)

namespace ParityDecisionTree

variable {ι β γ : Type*}

/-- Evaluate a parity decision tree on a Boolean string `x : ι → Bool`. -/
def eval : ParityDecisionTree ι β → (ι → Bool) → β
  | leaf b, _ => b
  | query S t₀ t₁, x => cond (parityOn S x) (t₁.eval x) (t₀.eval x)

/-- Worst-case number of adaptive parity queries made by a parity decision tree. -/
def depth : ParityDecisionTree ι β → ℕ
  | leaf _ => 0
  | query _ t₀ t₁ => max t₀.depth t₁.depth + 1

/-- Size (number of leaves) of a parity decision tree. -/
def leafCount : ParityDecisionTree ι β → ℕ
  | leaf _ => 1
  | query _ t₀ t₁ => t₀.leafCount + t₁.leafCount

@[simp]
theorem eval_leaf (b : β) (x : ι → Bool) : (leaf b : ParityDecisionTree ι β).eval x = b := by rfl

@[simp]
theorem eval_query (S : Finset ι) (t₀ t₁ : ParityDecisionTree ι β) (x : ι → Bool) :
    (query S t₀ t₁).eval x = cond (parityOn S x) (t₁.eval x) (t₀.eval x) := by rfl

@[simp]
theorem depth_leaf (b : β) : (leaf b : ParityDecisionTree ι β).depth = 0 := by rfl

@[simp]
theorem depth_query (S : Finset ι) (t₀ t₁ : ParityDecisionTree ι β) :
    (query S t₀ t₁).depth = max t₀.depth t₁.depth + 1 := by rfl

@[simp]
theorem leafCount_leaf (b : β) : (leaf b : ParityDecisionTree ι β).leafCount = 1 := by rfl

@[simp]
theorem leafCount_query (S : Finset ι) (t₀ t₁ : ParityDecisionTree ι β) :
    (query S t₀ t₁).leafCount = t₀.leafCount + t₁.leafCount := by rfl

/-- Every parity decision tree has at least one leaf. -/
theorem leafCount_pos (t : ParityDecisionTree ι β) : 0 < t.leafCount := by
  induction t with
  | leaf _ => simp
  | query _ t₀ t₁ ih₀ _ => simp; omega

/-- A parity decision tree of depth `d` has at most `2 ^ d` leaves. -/
theorem leafCount_le_two_pow_depth (t : ParityDecisionTree ι β) :
    t.leafCount ≤ 2 ^ t.depth := by
  induction t with
  | leaf _ => simp
  | query _ t₀ t₁ ih₀ ih₁ =>
    simp only [leafCount_query, depth_query, pow_succ]
    have h₀ : 2 ^ t₀.depth ≤ 2 ^ max t₀.depth t₁.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h₁ : 2 ^ t₁.depth ≤ 2 ^ max t₀.depth t₁.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega

/-- Sequential composition of parity decision trees: run `t`, then feed its output to `k`. -/
def bind : ParityDecisionTree ι β → (β → ParityDecisionTree ι γ) → ParityDecisionTree ι γ
  | leaf b, k => k b
  | query S t₀ t₁, k => query S (t₀.bind k) (t₁.bind k)

@[simp]
theorem eval_bind (t : ParityDecisionTree ι β) (k : β → ParityDecisionTree ι γ) (x : ι → Bool) :
    (t.bind k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf _ => rfl
  | query S t₀ t₁ ih₀ ih₁ =>
    cases h : parityOn S x <;> simp [bind, h, ih₀, ih₁]

/-- Binding a depth-`≤ d₁` tree with depth-`≤ d₂` continuations yields depth at most `d₁ + d₂`. -/
theorem depth_bind_le {t : ParityDecisionTree ι β} {k : β → ParityDecisionTree ι γ}
    {d₁ d₂ : ℕ} (ht : t.depth ≤ d₁) (hk : ∀ b, (k b).depth ≤ d₂) :
    (t.bind k).depth ≤ d₁ + d₂ := by
  induction t generalizing d₁ with
  | leaf b =>
    exact (hk b).trans (Nat.le_add_left d₂ d₁)
  | query S t₀ t₁ ih₀ ih₁ =>
    cases d₁ with
    | zero => simp at ht
    | succ d₁ =>
      simp only [depth_query, Nat.add_le_add_iff_right, max_le_iff] at ht
      simp only [bind, depth_query]
      have h₀ := ih₀ ht.1
      have h₁ := ih₁ ht.2
      omega

/-- Query every parity in `ss : List (Finset ι)` adaptively and pass the boolean answers to `k`. -/
def queryList : (ss : List (Finset ι)) → ((Fin ss.length → Bool) → β) → ParityDecisionTree ι β
  | [], k => leaf (k Fin.elim0)
  | S :: ss, k =>
      query S
        (queryList ss (fun ans ↦ k (Fin.cons false ans)))
        (queryList ss (fun ans ↦ k (Fin.cons true ans)))

/-- Evaluating `queryList ss k` applies `k` to the tuple of parities `(parityOn ss[i] x)`. -/
theorem eval_queryList (ss : List (Finset ι)) (k : (Fin ss.length → Bool) → β) (x : ι → Bool) :
    (queryList ss k).eval x = k (fun i ↦ parityOn (ss.get i) x) := by
  induction ss with
  | nil =>
    simp only [queryList, eval_leaf]
    congr 1
    ext i
    exact i.elim0
  | cons S ss ih =>
    have hcons : ∀ b : Bool, parityOn S x = b →
        (Fin.cons b (fun i : Fin ss.length ↦ parityOn (ss.get i) x) :
          Fin (S :: ss).length → Bool) = fun i ↦ parityOn ((S :: ss).get i) x := by
      intro b hb
      ext i
      refine Fin.cases ?_ (fun j ↦ rfl) i
      exact hb.symm
    cases h : parityOn S x
    · simp only [queryList, eval_query, h, Bool.cond_false, ih, hcons false h]
    · simp only [queryList, eval_query, h, Bool.cond_true, ih, hcons true h]

/-- `queryList ss k` has depth exactly `ss.length`. -/
@[simp]
theorem depth_queryList (ss : List (Finset ι)) (k : (Fin ss.length → Bool) → β) :
    (queryList ss k).depth = ss.length := by
  induction ss with
  | nil => rfl
  | cons S ss ih => simp [queryList, ih]

/-- Short-circuit conjunction of two Boolean parity decision trees. -/
def andTree (t₁ t₂ : ParityDecisionTree ι Bool) : ParityDecisionTree ι Bool :=
  t₁.bind (fun b ↦ if b then t₂ else leaf false)

@[simp]
theorem eval_andTree (t₁ t₂ : ParityDecisionTree ι Bool) (x : ι → Bool) :
    (andTree t₁ t₂).eval x = (t₁.eval x && t₂.eval x) := by
  cases h : t₁.eval x <;> simp [andTree, h]

/-- `andTree t₁ t₂` has depth at most `t₁.depth + t₂.depth`. -/
theorem depth_andTree_le (t₁ t₂ : ParityDecisionTree ι Bool) :
    (andTree t₁ t₂).depth ≤ t₁.depth + t₂.depth :=
  depth_bind_le le_rfl (fun b ↦ by cases b <;> simp)

/-- Every function on a finite Boolean cube is computed by a parity decision tree of depth at most
`Fintype.card ι` (via singleton parity queries). -/
theorem exists_eval_eq [Fintype ι] (f : (ι → Bool) → β) :
    ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.depth ≤ Fintype.card ι := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ss : List (Finset ι) := List.ofFn (fun i : Fin (Fintype.card ι) ↦ ({e i} : Finset ι))
  have hlen : ss.length = Fintype.card ι := List.length_ofFn
  let t := queryList ss (fun ans ↦ f (fun a ↦ ans ((e.symm a).cast hlen.symm)))
  refine ⟨t, ?_, ?_⟩
  · ext x
    rw [eval_queryList]
    congr 1
    ext a
    simp [ss]
  · simp [t, hlen]

/-- Minimum depth of a deterministic parity decision tree computing `f : (ι → Bool) → β`. -/
noncomputable def pdtDepth (f : (ι → Bool) → β) : ℕ :=
  sInf { d : ℕ | ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.depth ≤ d }

/-- Minimum size (leaf count) of a deterministic parity decision tree computing
`f : (ι → Bool) → β`. -/
noncomputable def pdtSize (f : (ι → Bool) → β) : ℕ :=
  sInf { s : ℕ | ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.leafCount ≤ s }

/-- Any parity decision tree computing `f` bounds `pdtDepth f` from above. -/
theorem pdtDepth_le_depth {f : (ι → Bool) → β} {t : ParityDecisionTree ι β}
    (ht : t.eval = f) : pdtDepth f ≤ t.depth :=
  Nat.sInf_le ⟨t, ht, le_rfl⟩

/-- There exists a parity decision tree computing `f` with depth equal to `pdtDepth f`. -/
theorem exists_eval_depth_eq_pdtDepth [Finite ι] (f : (ι → Bool) → β) :
    ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.depth ≤ pdtDepth f := by
  cases nonempty_fintype ι
  obtain ⟨t₀, ht₀, _⟩ := exists_eval_eq f
  have hne : { d : ℕ | ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.depth ≤ d }.Nonempty :=
    ⟨t₀.depth, t₀, ht₀, le_rfl⟩
  exact Nat.sInf_mem hne

/-- Any parity decision tree computing `f` bounds `pdtSize f` from above. -/
theorem pdtSize_le_leafCount {f : (ι → Bool) → β} {t : ParityDecisionTree ι β}
    (ht : t.eval = f) : pdtSize f ≤ t.leafCount :=
  Nat.sInf_le ⟨t, ht, le_rfl⟩

/-- There exists a parity decision tree computing `f` with leaf count at most `pdtSize f`. -/
theorem exists_eval_leafCount_le_pdtSize [Finite ι] (f : (ι → Bool) → β) :
    ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.leafCount ≤ pdtSize f := by
  cases nonempty_fintype ι
  obtain ⟨t₀, ht₀, _⟩ := exists_eval_eq f
  have hne : { s : ℕ | ∃ t : ParityDecisionTree ι β, t.eval = f ∧ t.leafCount ≤ s }.Nonempty :=
    ⟨t₀.leafCount, t₀, ht₀, le_rfl⟩
  exact Nat.sInf_mem hne

/-- Deterministic parity decision tree size is always positive. -/
theorem pdtSize_pos [Finite ι] (f : (ι → Bool) → β) : 0 < pdtSize f := by
  obtain ⟨t, _, hle⟩ := exists_eval_leafCount_le_pdtSize f
  exact (leafCount_pos t).trans_le hle

/-- Deterministic parity decision tree size is at most `2 ^ pdtDepth f`. -/
theorem pdtSize_le_two_pow_pdtDepth [Finite ι] (f : (ι → Bool) → β) :
    pdtSize f ≤ 2 ^ pdtDepth f := by
  obtain ⟨t, ht, hd⟩ := exists_eval_depth_eq_pdtDepth f
  exact (pdtSize_le_leafCount ht).trans
    ((leafCount_le_two_pow_depth t).trans (Nat.pow_le_pow_right (by norm_num) hd))

/-- Simulate a parity decision tree `t` as a two-party deterministic communication protocol on the
XOR input `x + y`: at each query `S`, Alice sends `parityOn S x` and Bob sends `parityOn S y`. -/
def toXorProtocol : ParityDecisionTree ι β → Protocol (ι → Bool) (ι → Bool) β
  | leaf b => Protocol.output b
  | query S t₀ t₁ =>
      let p₀ := t₀.toXorProtocol
      let p₁ := t₁.toXorProtocol
      Protocol.alice (parityOn S)
        (Protocol.bob (parityOn S) p₀ p₁)
        (Protocol.bob (parityOn S) p₁ p₀)

/-- `t.toXorProtocol` computes `(x, y) ↦ t.eval (x + y)` on all inputs. -/
@[simp]
theorem run_toXorProtocol (t : ParityDecisionTree ι β) (x y : ι → Bool) :
    t.toXorProtocol.run x y = t.eval (x + y) := by
  induction t with
  | leaf _ => rfl
  | query S t₀ t₁ ih₀ ih₁ =>
    simp only [toXorProtocol, eval_query, parityOn_add]
    cases hx : parityOn S x <;> cases hy : parityOn S y <;>
      simp [Protocol.run_alice, Protocol.run_bob, hx, hy, ih₀, ih₁]

/-- `t.toXorProtocol` communicates at most `2 * t.depth` bits. -/
theorem depth_toXorProtocol_le (t : ParityDecisionTree ι β) :
    t.toXorProtocol.depth ≤ 2 * t.depth := by
  induction t with
  | leaf _ => simp [toXorProtocol]
  | query S t₀ t₁ ih₀ ih₁ =>
    simp only [toXorProtocol, Protocol.depth_alice, Protocol.depth_bob, depth_query]
    omega

end ParityDecisionTree

/-- A randomized parity decision tree is a probability mass function over deterministic parity
decision trees. -/
abbrev RandomizedPDT (ι β : Type*) : Type _ :=
  PMF (ParityDecisionTree ι β)

namespace RandomizedPDT

variable {ι β : Type*}

/-- Worst-case query depth of a randomized parity decision tree over its support. -/
noncomputable def depth (μ : RandomizedPDT ι β) : ℕ∞ :=
  ⨆ t ∈ μ.support, (t.depth : ℕ∞)

/-- Worst-case leaf count (size) of a randomized parity decision tree over its support. -/
noncomputable def leafCount (μ : RandomizedPDT ι β) : ℕ∞ :=
  ⨆ t ∈ μ.support, (t.leafCount : ℕ∞)

/-- Worst-case pointwise error probability `Pr_{T ~ μ}[T(x) ≠ f(x)]`. -/
@[expose]
noncomputable def errorProb (μ : RandomizedPDT ι β) (f : (ι → Bool) → β) (x : ι → Bool) : ℝ := by
  classical
  exact (∑' t, if t.eval x = f x then (0 : ℝ≥0∞) else μ t).toReal

/-- Correctness probability `Pr_{T ~ μ}[T(x) = f(x)]`. -/
@[expose]
noncomputable def successProb (μ : RandomizedPDT ι β) (f : (ι → Bool) → β)
    (x : ι → Bool) : ℝ := by
  classical
  exact (∑' t, if t.eval x = f x then μ t else (0 : ℝ≥0∞)).toReal

/-- `μ` computes `f` with error at most `ε` if `Pr_{T ~ μ}[T(x) ≠ f(x)] ≤ ε` for all inputs `x`. -/
def Computes (μ : RandomizedPDT ι β) (ε : ℝ) (f : (ι → Bool) → β) : Prop :=
  ∀ x : ι → Bool, μ.errorProb f x ≤ ε

/-- `μ.depth ≤ c` if and only if every tree in `μ.support` has depth at most `c`. -/
theorem depth_le_iff {μ : RandomizedPDT ι β} {c : ℕ∞} :
    μ.depth ≤ c ↔ ∀ t ∈ μ.support, (t.depth : ℕ∞) ≤ c := by
  simp [depth]

/-- `μ.leafCount ≤ s` if and only if every tree in `μ.support` has leaf count at most `s`. -/
theorem leafCount_le_iff {μ : RandomizedPDT ι β} {s : ℕ∞} :
    μ.leafCount ≤ s ↔ ∀ t ∈ μ.support, (t.leafCount : ℕ∞) ≤ s := by
  simp [leafCount]

/-- If `μ.depth ≤ d`, then `μ.leafCount ≤ 2 ^ d`. -/
theorem leafCount_le_two_pow_of_depth_le {μ : RandomizedPDT ι β} {d : ℕ}
    (hd : μ.depth ≤ d) : μ.leafCount ≤ (2 ^ d : ℕ) := by
  rw [leafCount_le_iff]
  intro t ht
  have htd : t.depth ≤ d := by exact_mod_cast depth_le_iff.mp hd t ht
  exact_mod_cast (t.leafCount_le_two_pow_depth).trans (Nat.pow_le_pow_right (by norm_num) htd)

/-- Success and error probabilities sum to `1`. -/
theorem successProb_add_errorProb (μ : RandomizedPDT ι β) (f : (ι → Bool) → β) (x : ι → Bool) :
    μ.successProb f x + μ.errorProb f x = 1 := by
  classical
  have h1 : (∑' t, if t.eval x = f x then μ t else 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (μ.tsum_coe ▸ ENNReal.one_ne_top)
      (tsum_le_tsum fun t ↦ by split_ifs <;> [exact le_rfl; exact zero_le])
  have h2 : (∑' t, if t.eval x = f x then 0 else μ t) ≠ ⊤ :=
    ne_top_of_le_ne_top (μ.tsum_coe ▸ ENNReal.one_ne_top)
      (tsum_le_tsum fun t ↦ by split_ifs <;> [exact zero_le; exact le_rfl])
  simp only [successProb, errorProb]
  rw [← ENNReal.toReal_add h1 h2, ← tsum_add]
  have hsum : (∑' t, ((if t.eval x = f x then μ t else 0) +
      (if t.eval x = f x then 0 else μ t))) = ∑' t, μ t :=
    tsum_congr (fun t ↦ by split_ifs <;> simp)
  rw [hsum, μ.tsum_coe, ENNReal.toReal_one]

/-- `μ.Computes ε f` holds iff `Pr_{T ~ μ}[T(x) = f(x)] ≥ 1 - ε` for all `x` (so `ε = 1/3` means
success probability at least `2/3`). -/
theorem computes_iff_successProb_ge {μ : RandomizedPDT ι β} {ε : ℝ} {f : (ι → Bool) → β} :
    μ.Computes ε f ↔ ∀ x : ι → Bool, 1 - ε ≤ μ.successProb f x := by
  refine forall_congr' (fun x ↦ ?_)
  have h := successProb_add_errorProb μ f x
  constructor <;> intro hx <;> linarith

/-- Monotonicity of `Computes` in the error threshold. -/
theorem Computes.mono {μ : RandomizedPDT ι β} {ε ε' : ℝ} {f : (ι → Bool) → β}
    (h : μ.Computes ε f) (hε : ε ≤ ε') : μ.Computes ε' f :=
  fun x ↦ (h x).trans hε

/-- Repeat a one-sided-error Boolean randomized parity decision tree `r` independent times,
accepting iff all `r` runs return `true`. -/
noncomputable def repeatAnd (μ : RandomizedPDT ι Bool) : ℕ → RandomizedPDT ι Bool
  | 0 => PMF.pure (.leaf true)
  | r + 1 => μ.bind (fun t₁ ↦ (repeatAnd μ r).map (fun t₂ ↦ t₁.andTree t₂))

/-- `r`-fold AND repetition multiplies worst-case depth by at most `r`. -/
theorem depth_repeatAnd_le {μ : RandomizedPDT ι Bool} {d : ℕ} (hd : μ.depth ≤ d) (r : ℕ) :
    (repeatAnd μ r).depth ≤ (r * d : ℕ) := by
  induction r with
  | zero => simp [repeatAnd, depth]
  | succ r ih =>
    rw [depth_le_iff]
    intro t ht
    simp only [repeatAnd, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht
    have h₁ : t₁.depth ≤ d := by exact_mod_cast depth_le_iff.mp hd t₁ ht₁
    have h₂ : t₂.depth ≤ r * d := by exact_mod_cast depth_le_iff.mp ih t₂ ht₂
    have hle : (t₁.andTree t₂).depth ≤ (r + 1) * d := by
      have := t₁.depth_andTree_le t₂
      rw [Nat.succ_mul]
      omega
    exact_mod_cast hle

/-- If `μ` always outputs `true` on `1`-inputs of `f` and outputs `true` with probability at most
`p` on `0`-inputs of `f`, then `repeatAnd μ r` computes `f` with error at most `p ^ r`. -/
theorem computes_repeatAnd_of_oneSided {μ : RandomizedPDT ι Bool} {f : (ι → Bool) → Bool}
    {p : ℝ} (hp : 0 ≤ p)
    (htrue : ∀ x, f x = true → ∀ t ∈ μ.support, t.eval x = true)
    (hfalse : ∀ x, f x = false → μ.errorProb f x ≤ p) (r : ℕ) :
    (repeatAnd μ r).Computes (p ^ r) f := by
  have htrue_r : ∀ k x, f x = true → ∀ t ∈ (repeatAnd μ k).support, t.eval x = true := by
    intro k
    induction k with
    | zero => simp [repeatAnd]
    | succ k ihk =>
      intro x hx t ht
      simp only [repeatAnd, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht
      simp [htrue x hx t₁ ht₁, ihk x hx t₂ ht₂]
  have hfalse_r : ∀ k x, f x = false → (repeatAnd μ k).errorProb f x ≤ p ^ k := by
    intro k
    induction k with
    | zero =>
      intro x hx
      classical
      simp only [repeatAnd, errorProb, hx, pow_zero, PMF.pure_apply]
      have hts : (∑' t : ParityDecisionTree ι Bool,
          if t.eval x = false then (0 : ℝ≥0∞)
          else if t = ParityDecisionTree.leaf true then 1 else 0) = 1 := by
        calc _ = ∑' t : ParityDecisionTree ι Bool,
              if t = ParityDecisionTree.leaf true then (1 : ℝ≥0∞) else 0 := by
              refine tsum_congr (fun t ↦ ?_)
              by_cases ht : t = ParityDecisionTree.leaf true
              · subst ht; simp
              · simp [ht]
          _ = 1 := tsum_ite_eq _ _
      simp [hts]
    | succ k ihk =>
      intro x hx
      classical
      have herr_eq : ∀ ν : RandomizedPDT ι Bool,
          (∑' t, if t.eval x = false then (0 : ℝ≥0∞) else ν t) =
            ∑' t, if t.eval x = true then ν t else 0 :=
        fun ν ↦ tsum_congr (fun t ↦ by cases t.eval x <;> simp)
      have hstep : (∑' t, if t.eval x = true then repeatAnd μ (k + 1) t else 0) =
          (∑' t₁, if t₁.eval x = true then μ t₁ else 0) *
            (∑' t₂, if t₂.eval x = true then repeatAnd μ k t₂ else 0) := by
        simp only [repeatAnd, PMF.bind_apply, PMF.map_apply]
        calc (∑' t, if t.eval x = true then
                ∑' t₁, μ t₁ * ∑' t₂, if t = t₁.andTree t₂ then repeatAnd μ k t₂ else 0 else 0)
            = ∑' t, ∑' t₁, ∑' t₂,
                if t = t₁.andTree t₂ then
                  (if (t₁.andTree t₂).eval x = true then μ t₁ * repeatAnd μ k t₂ else 0)
                else 0 := by
              refine tsum_congr (fun t ↦ ?_)
              by_cases htx : t.eval x = true
              · simp only [htx, ↓reduceIte]
                refine tsum_congr (fun t₁ ↦ ?_)
                rw [← ENNReal.tsum_mul_left]
                refine tsum_congr (fun t₂ ↦ ?_)
                by_cases heq : t = t₁.andTree t₂
                · subst heq; simp [htx]
                · simp [heq]
              · simp only [htx]
                symm
                refine tsum_eq_zero_iff.mpr (fun t₁ ↦ tsum_eq_zero_iff.mpr fun t₂ ↦ ?_)
                by_cases heq : t = t₁.andTree t₂
                · subst heq; simp [htx]
                · simp [heq]
          _ = ∑' t₁, ∑' t₂,
                if (t₁.andTree t₂).eval x = true then μ t₁ * repeatAnd μ k t₂ else 0 := by
              rw [tsum_comm]
              refine tsum_congr (fun t₁ ↦ ?_)
              rw [tsum_comm]
              exact tsum_congr (fun t₂ ↦ tsum_ite_eq _ _)
          _ = ∑' t₁, (if t₁.eval x = true then μ t₁ else 0) *
                ∑' t₂, (if t₂.eval x = true then repeatAnd μ k t₂ else 0) := by
              refine tsum_congr (fun t₁ ↦ ?_)
              rw [← ENNReal.tsum_mul_left]
              refine tsum_congr (fun t₂ ↦ ?_)
              cases h₁ : t₁.eval x <;> cases h₂ : t₂.eval x <;> simp [h₁, h₂]
          _ = _ := ENNReal.tsum_mul_right
      have hfin₁ : (∑' t₁, if t₁.eval x = true then μ t₁ else 0) ≠ ⊤ :=
        ne_top_of_le_ne_top (μ.tsum_coe ▸ ENNReal.one_ne_top)
          (tsum_le_tsum fun _ ↦ by split_ifs <;> [exact le_rfl; exact zero_le])
      have hfin₂ : (∑' t₂, if t₂.eval x = true then repeatAnd μ k t₂ else 0) ≠ ⊤ :=
        ne_top_of_le_ne_top ((repeatAnd μ k).tsum_coe ▸ ENNReal.one_ne_top)
          (tsum_le_tsum fun _ ↦ by split_ifs <;> [exact le_rfl; exact zero_le])
      have heq : (repeatAnd μ (k + 1)).errorProb f x =
          μ.errorProb f x * (repeatAnd μ k).errorProb f x := by
        simp only [errorProb, hx, herr_eq, hstep, ENNReal.toReal_mul]
      rw [heq, pow_succ']
      exact mul_le_mul (hfalse x hx) (ihk x hx) ENNReal.toReal_nonneg hp
  intro x
  cases hx : f x
  · exact hfalse_r r x hx
  · have hzero : (repeatAnd μ r).errorProb f x = 0 := by
      classical
      simp only [errorProb, hx]
      have : (∑' t, if t.eval x = true then (0 : ℝ≥0∞) else repeatAnd μ r t) = 0 := by
        refine tsum_eq_zero_iff.mpr (fun t ↦ ?_)
        by_cases ht : t ∈ (repeatAnd μ r).support
        · simp [htrue_r r x hx t ht]
        · simp only [PMF.mem_support_iff, not_not] at ht
          simp [ht]
      simp [this]
    rw [hzero]
    exact pow_nonneg hp r

/-- Minimum depth of an `ε`-error randomized parity decision tree computing `f`. -/
noncomputable def rpdtDepth (ε : ℝ) (f : (ι → Bool) → β) : ℕ∞ :=
  ⨅ (μ : RandomizedPDT ι β) (_ : μ.Computes ε f), μ.depth

/-- Minimum worst-case leaf count (size) of an `ε`-error randomized parity decision tree computing
`f`. -/
noncomputable def rpdtSize (ε : ℝ) (f : (ι → Bool) → β) : ℕ∞ :=
  ⨅ (μ : RandomizedPDT ι β) (_ : μ.Computes ε f), μ.leafCount

/-- Any `ε`-error randomized parity decision tree `μ` for `f` bounds `rpdtDepth ε f`. -/
theorem rpdtDepth_le_depth {μ : RandomizedPDT ι β} {ε : ℝ} {f : (ι → Bool) → β}
    (h : μ.Computes ε f) : rpdtDepth ε f ≤ μ.depth :=
  iInf₂_le μ h

/-- Any `ε`-error randomized parity decision tree `μ` for `f` bounds `rpdtSize ε f`. -/
theorem rpdtSize_le_leafCount {μ : RandomizedPDT ι β} {ε : ℝ} {f : (ι → Bool) → β}
    (h : μ.Computes ε f) : rpdtSize ε f ≤ μ.leafCount :=
  iInf₂_le μ h

/-- If `rpdtDepth ε f ≤ d`, then `rpdtSize ε f ≤ 2 ^ d`. -/
theorem rpdtSize_le_two_pow_of_rpdtDepth_le {ε : ℝ} {f : (ι → Bool) → β} {d : ℕ}
    (h : rpdtDepth ε f ≤ d) : rpdtSize ε f ≤ (2 ^ d : ℕ) := by
  have hlt : rpdtDepth ε f < (d + 1 : ℕ∞) :=
    lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self d)
  simp only [rpdtDepth, iInf_lt_iff] at hlt
  obtain ⟨μ, hμ, hd⟩ := hlt
  have hd' : μ.depth ≤ d := Order.le_of_lt_add_one hd
  exact (rpdtSize_le_leafCount hμ).trans (leafCount_le_two_pow_of_depth_le hd')

/-- Push a randomized parity decision tree forward to a public-coin communication protocol on the
XOR problem `(x, y) ↦ f (x + y)`. -/
noncomputable def toPublicCoin (μ : RandomizedPDT ι β) :
    PublicCoin (ι → Bool) (ι → Bool) β :=
  μ.map ParityDecisionTree.toXorProtocol

/-- `μ.toPublicCoin` has communication depth at most `2 * μ.depth`. -/
theorem depth_toPublicCoin_le {μ : RandomizedPDT ι β} {d : ℕ} (hd : μ.depth ≤ d) :
    μ.toPublicCoin.depth ≤ (2 * d : ℕ) := by
  rw [PublicCoin.depth_le_iff]
  intro p hp
  simp only [toPublicCoin, PMF.mem_support_map_iff] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  have htd : t.depth ≤ d := by exact_mod_cast depth_le_iff.mp hd t ht
  exact_mod_cast t.depth_toXorProtocol_le.trans (Nat.mul_le_mul_left 2 htd)

/-- `μ.toPublicCoin` preserves exact pointwise error probabilities on `(x, y) ↦ f (x + y)`. -/
theorem solves_toPublicCoin {μ : RandomizedPDT ι β} {ε : ℝ} {f : (ι → Bool) → β}
    (h : μ.Computes ε f) :
    μ.toPublicCoin.Solves ε (fun x y b ↦ f (x + y) = b) Set.univ Set.univ := by
  classical
  intro x _ y _
  have heq : μ.toPublicCoin.errorProb (fun x y b ↦ f (x + y) = b) x y =
      μ.errorProb f (x + y) := by
    unfold PublicCoin.errorProb toPublicCoin
    rw [Cslib.Probability.PMF.errorProb_map]
    simp only [Cslib.Probability.PMF.errorProb, PMF.toOuterMeasure_apply, errorProb]
    congr 1
    refine tsum_congr (fun t ↦ ?_)
    by_cases ht : t.eval (x + y) = f (x + y)
    · have hnot : t ∉ {a : ParityDecisionTree ι β | ¬f (x + y) = a.toXorProtocol.run x y} := by
        change ¬¬f (x + y) = t.toXorProtocol.run x y
        rw [ParityDecisionTree.run_toXorProtocol, not_not]
        exact ht.symm
      rw [Set.indicator_of_notMem hnot]
      simp [ht]
    · have hmem : t ∈ {a : ParityDecisionTree ι β | ¬f (x + y) = a.toXorProtocol.run x y} := by
        change ¬f (x + y) = t.toXorProtocol.run x y
        rw [ParityDecisionTree.run_toXorProtocol]
        exact Ne.symm ht
      rw [Set.indicator_of_mem hmem]
      simp [ht]
  rw [heq]
  exact h (x + y)

/-- Public-coin communication complexity of `(x, y) ↦ f (x + y)` is at most `2 * rpdtDepth ε f`. -/
theorem publicCoin_xor_le_two_mul_rpdtDepth (ε : ℝ) (f : (ι → Bool) → β) :
    PublicCoin.ecomplexityFun ε (fun x y : ι → Bool ↦ f (x + y)) ≤ 2 * rpdtDepth ε f := by
  by_cases htop : rpdtDepth ε f = ⊤
  · simp [htop]
  · lift rpdtDepth ε f to ℕ using htop with d hd
    have hlt : rpdtDepth ε f < (d + 1 : ℕ∞) := by
      rw [← hd]
      exact_mod_cast Nat.lt_succ_self d
    simp only [rpdtDepth, iInf_lt_iff] at hlt
    obtain ⟨μ, hμ, hμd⟩ := hlt
    have hμd' : μ.depth ≤ d := Order.le_of_lt_add_one hμd
    exact (PublicCoin.ecomplexity_le_depth (solves_toPublicCoin hμ)).trans
      (by simpa using depth_toPublicCoin_le hμd')

end RandomizedPDT

namespace BooleanAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact Fourier `ℓ₁` spectral norm `‖f̂‖₁ = ∑ S, |fourierCoeff f S|` of `f : (ι → Bool) → ℝ`. -/
noncomputable def fourierSpectralNorm (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S : Finset ι, |fourierCoeff f S|

/-- `ε`-approximate Fourier spectral norm `‖f̂‖_{1,ε} = inf { ‖ĝ‖₁ | ∀ x, |f x - g x| < ε }`. -/
noncomputable def approxSpectralNorm (ε : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  sInf { c : ℝ | ∃ g : (ι → Bool) → ℝ, (∀ x, |f x - g x| < ε) ∧ fourierSpectralNorm g = c }

/-- The Fourier spectral norm is nonnegative. -/
theorem fourierSpectralNorm_nonneg (f : (ι → Bool) → ℝ) : 0 ≤ fourierSpectralNorm f :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

/-- Triangle inequality for the Fourier spectral norm. -/
theorem fourierSpectralNorm_add_le (f g : (ι → Bool) → ℝ) :
    fourierSpectralNorm (fun x ↦ f x + g x) ≤ fourierSpectralNorm f + fourierSpectralNorm g := by
  simp only [fourierSpectralNorm, fourierCoeff_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun S _ ↦ abs_add_le _ _)

/-- Positive homogeneity of the Fourier spectral norm. -/
theorem fourierSpectralNorm_const_mul (c : ℝ) (f : (ι → Bool) → ℝ) :
    fourierSpectralNorm (fun x ↦ c * f x) = |c| * fourierSpectralNorm f := by
  simp only [fourierSpectralNorm, fourierCoeff_const_mul, abs_mul, ← Finset.mul_sum]

/-- The Fourier spectral norm of a constant function `c` is `|c|`. -/
@[simp]
theorem fourierSpectralNorm_const (c : ℝ) :
    fourierSpectralNorm (fun _ : ι → Bool ↦ c) = |c| := by
  simp only [fourierSpectralNorm, fourierCoeff_const]
  rw [Finset.sum_eq_single ∅ (fun S _ hS ↦ by simp [hS])
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp

/-- Multiplying by a parity character `chi ℝ T` leaves `fourierSpectralNorm` unchanged. -/
theorem fourierSpectralNorm_chi_mul (T : Finset ι) (f : (ι → Bool) → ℝ) :
    fourierSpectralNorm (fun x ↦ chi ℝ T x * f x) = fourierSpectralNorm f := by
  simp only [fourierSpectralNorm, fourierCoeff_chi_mul]
  let e : Finset ι ≃ Finset ι :=
    { toFun := fun S ↦ symmDiff T S
      invFun := fun S ↦ symmDiff T S
      left_inv := fun S ↦ by simp [symmDiff_symmDiff_cancel_left]
      right_inv := fun S ↦ by simp [symmDiff_symmDiff_cancel_left] }
  exact Equiv.sum_comp e (fun S ↦ |fourierCoeff f S|)

/-- Conditioning a function `f` on a parity constraint `parityOn T x = b` does not increase its
Fourier spectral norm. -/
theorem fourierSpectralNorm_parityFilter_le (T : Finset ι) (b : Bool) (f : (ι → Bool) → ℝ) :
    fourierSpectralNorm (fun x ↦ if parityOn T x = b then f x else 0) ≤
      fourierSpectralNorm f := by
  let s : ℝ := signVal b
  have hs : |s| = 1 := by cases b <;> simp [s]
  have hrew : (fun x ↦ if parityOn T x = b then f x else 0) =
      fun x ↦ (1 / 2 : ℝ) * f x + (s / 2) * (chi ℝ T x * f x) := by
    ext x
    rw [chi_eq_signVal_parityOn]
    cases parityOn T x <;> cases b <;> dsimp only [s, signVal, cond] <;>
      simp only [reduceCtorEq, ↓reduceIte] <;> ring
  rw [hrew]
  calc fourierSpectralNorm (fun x ↦ (1 / 2 : ℝ) * f x + (s / 2) * (chi ℝ T x * f x))
      ≤ fourierSpectralNorm (fun x ↦ (1 / 2 : ℝ) * f x) +
          fourierSpectralNorm (fun x ↦ (s / 2) * (chi ℝ T x * f x)) :=
        fourierSpectralNorm_add_le _ _
    _ = |(1 / 2 : ℝ)| * fourierSpectralNorm f +
          |s / 2| * fourierSpectralNorm f := by
        rw [fourierSpectralNorm_const_mul, fourierSpectralNorm_const_mul,
          fourierSpectralNorm_chi_mul]
    _ = fourierSpectralNorm f := by
        rw [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num, abs_div, hs, show |(2 : ℝ)| = 2 by norm_num]
        ring

/-- The `{0,1}` characteristic function of any affine subspace of `{0,1}^ι` defined by a list of
parity equations `parityOn S x = b` has Fourier spectral norm at most `1`. -/
theorem fourierSpectralNorm_affineIndicator_le_one (eqs : List (Finset ι × Bool)) :
    fourierSpectralNorm
        (fun x : ι → Bool ↦ if ∀ p ∈ eqs, parityOn p.1 x = p.2 then (1 : ℝ) else 0) ≤ 1 := by
  induction eqs with
  | nil => simp
  | cons p eqs ih =>
    have hrew : (fun x : ι → Bool ↦
          if ∀ q ∈ p :: eqs, parityOn q.1 x = q.2 then (1 : ℝ) else 0) =
        fun x ↦ if parityOn p.1 x = p.2 then
          (if ∀ q ∈ eqs, parityOn q.1 x = q.2 then (1 : ℝ) else 0) else 0 := by
      ext x
      by_cases hp : parityOn p.1 x = p.2 <;> simp [hp]
    rw [hrew]
    exact (fourierSpectralNorm_parityFilter_le p.1 p.2 _).trans ih

/-- Every parity decision tree `t` and bounded output map `g : β → ℝ` (`|g b| ≤ 1`) satisfies
`fourierSpectralNorm (g ∘ t.eval) ≤ t.leafCount`. -/
theorem fourierSpectralNorm_pdt_le_leafCount {β : Type*} (g : β → ℝ) (hg : ∀ b, |g b| ≤ 1)
    (t : ParityDecisionTree ι β) :
    fourierSpectralNorm (fun x ↦ g (t.eval x)) ≤ t.leafCount := by
  induction t with
  | leaf b =>
    simpa using hg b
  | query S t₀ t₁ ih₀ ih₁ =>
    have hrew : (fun x ↦ g ((ParityDecisionTree.query S t₀ t₁).eval x)) =
        fun x ↦ (if parityOn S x = false then g (t₀.eval x) else 0) +
          (if parityOn S x = true then g (t₁.eval x) else 0) := by
      ext x
      cases h : parityOn S x <;> simp [h]
    rw [hrew, ParityDecisionTree.leafCount_query, Nat.cast_add]
    exact (fourierSpectralNorm_add_le _ _).trans
      (add_le_add ((fourierSpectralNorm_parityFilter_le S false _).trans ih₀)
        ((fourierSpectralNorm_parityFilter_le S true _).trans ih₁))

/-- The Fourier spectral norm of the `{0,1}` encoding of a Boolean function `f` is bounded above
by its deterministic parity decision tree size `pdtSize f`. -/
theorem fourierSpectralNorm_le_pdtSize (f : (ι → Bool) → Bool) :
    fourierSpectralNorm (fun x ↦ bitVal ℝ (f x)) ≤ ParityDecisionTree.pdtSize f := by
  obtain ⟨t, ht, hle⟩ := ParityDecisionTree.exists_eval_leafCount_le_pdtSize f
  have hbound : fourierSpectralNorm (fun x ↦ bitVal ℝ (t.eval x)) ≤ t.leafCount :=
    fourierSpectralNorm_pdt_le_leafCount (bitVal ℝ) (fun b ↦ by cases b <;> simp) t
  rw [ht] at hbound
  exact hbound.trans (by exact_mod_cast hle)

/-- **Equivalence of `γ₂` norm and Fourier spectral norm for XOR functions**
: for every `f : (ι → Bool) → ℝ`, the `γ₂`
factorization norm of `M(x, y) = f (x + y)` equals `fourierSpectralNorm f`.
-/
theorem gamma2Norm_xor_eq_fourierSpectralNorm (f : (ι → Bool) → ℝ) :
    CslibFrontier.Matrix.gamma2Norm (_root_.Matrix.of fun x y : ι → Bool ↦ f (x + y)) =
      fourierSpectralNorm f := by
  have horth : ∀ S T : Finset ι, S ≠ T → ∑ x : ι → Bool, chi ℝ S x * chi ℝ T x = 0 := by
    intro S T hST
    have hexp := expect_chi_mul_chi (ι := ι) S T
    simp only [hST, ↓reduceIte] at hexp
    rw [Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hexp
    refine hexp.resolve_right ?_
    exact_mod_cast Fintype.card_ne_zero
  have hexp : (_root_.Matrix.of fun x y : ι → Bool ↦ f (x + y)) =
      _root_.Matrix.of fun x y : ι → Bool ↦
        ∑ S : Finset ι, fourierCoeff f S * chi ℝ S x * chi ℝ S y := by
    ext x y
    simp only [_root_.Matrix.of_apply]
    rw [← sum_fourierCoeff_mul_chi f (x + y)]
    refine Finset.sum_congr rfl (fun S _ ↦ ?_)
    rw [chi_add]
    ring
  rw [hexp]
  exact CslibFrontier.Matrix.gamma2Norm_eq_sum_abs_of_flat_orthogonal
    (fun S x ↦ chi ℝ S x) abs_chi horth (fourierCoeff f)

/-- Specialization of `gamma2Norm_xor_eq_fourierSpectralNorm` to the `{0,1}` communication matrix
of a Boolean XOR function `F(x, y) = f(x + y)`. -/
theorem gamma2Norm_communicationMatrix_xor (f : (ι → Bool) → Bool) :
    CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ fun x y : ι → Bool ↦ f (x + y)) =
      fourierSpectralNorm (fun x ↦ bitVal ℝ (f x)) :=
  gamma2Norm_xor_eq_fourierSpectralNorm (fun x ↦ bitVal ℝ (f x))

/-- Any `ε`-uniform approximant `g` to `f` gives an upper bound on `approxSpectralNorm ε f`. -/
theorem approxSpectralNorm_le_of_approx {ε : ℝ} {f g : (ι → Bool) → ℝ}
    (hg : ∀ x, |f x - g x| < ε) :
    approxSpectralNorm ε f ≤ fourierSpectralNorm g := by
  refine csInf_le ⟨0, ?_⟩ ⟨g, hg, rfl⟩
  rintro _ ⟨h, -, rfl⟩
  exact fourierSpectralNorm_nonneg h

/-- `approxSpectralNorm ε f` is always nonnegative. -/
theorem approxSpectralNorm_nonneg (ε : ℝ) (f : (ι → Bool) → ℝ) :
    0 ≤ approxSpectralNorm ε f := by
  by_cases hne :
      ({ c : ℝ | ∃ g : (ι → Bool) → ℝ, (∀ x, |f x - g x| < ε) ∧ fourierSpectralNorm g = c }
        ).Nonempty
  · refine le_csInf hne ?_
    rintro _ ⟨g, -, rfl⟩
    exact fourierSpectralNorm_nonneg g
  · rw [approxSpectralNorm, Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-- Averaging any matrix `G : Matrix (ι → Bool) (ι → Bool) ℝ` along XOR diagonals produces a
Boolean-cube function `g z = 𝔼 y, G (z + y) y` with `fourierSpectralNorm g ≤ gamma2Norm G`. -/
theorem fourierSpectralNorm_xorAvg_le_gamma2Norm (G : Matrix (ι → Bool) (ι → Bool) ℝ) :
    fourierSpectralNorm (fun z : ι → Bool ↦ (∑ y : ι → Bool, G (z + y) y) /
        (Fintype.card (ι → Bool) : ℝ)) ≤
      CslibFrontier.Matrix.gamma2Norm G := by
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hcard : (2 : ℝ) ^ Fintype.card ι = N := by
    simp [N]
  have horth : ∀ S T : Finset ι, S ≠ T → ∑ x : ι → Bool, chi ℝ S x * chi ℝ T x = 0 := by
    intro S T hST
    have hexp := expect_chi_mul_chi (ι := ι) S T
    simp only [hST, ↓reduceIte] at hexp
    rw [Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hexp
    exact hexp.resolve_right hN.ne'
  have hcoeff : ∀ S : Finset ι,
      fourierCoeff (fun z ↦ (∑ y, G (z + y) y) / N) S =
        (∑ x : ι → Bool, ∑ y : ι → Bool, chi ℝ S x * G x y * chi ℝ S y) / N ^ 2 := by
    intro S
    rw [fourierCoeff_eq_sum, hcard]
    have hsum : ∑ z : ι → Bool, (∑ y : ι → Bool, G (z + y) y) / N * chi ℝ S z =
        (∑ x : ι → Bool, ∑ y : ι → Bool, chi ℝ S x * G x y * chi ℝ S y) / N := by
      rw [Finset.sum_div]
      simp_rw [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ ↦ ?_)
      let ey : (ι → Bool) ≃ (ι → Bool) := Equiv.addRight y
      rw [← Equiv.sum_comp ey]
      refine Finset.sum_congr rfl (fun z _ ↦ ?_)
      have hzz : z + y + y = z := by
        ext i; change ((z i + y i) + y i : Bool) = z i; cases z i <;> cases y i <;> rfl
      change G (z + y + y) y * chi ℝ S (z + y) / N =
        chi ℝ S z * G z y * chi ℝ S y / N
      rw [hzz, chi_add]
      ring
    rw [hsum, div_div, sq]
  simp only [fourierSpectralNorm, hcoeff]
  exact CslibFrontier.Matrix.sum_abs_flat_orthogonal_pairing_le_gamma2Norm G (fun S x ↦ chi ℝ S x)
    abs_chi horth

/-- Every deterministic communication protocol `p` satisfies
`gamma2Norm (communicationMatrix ℝ p.run) ≤ p.leafCount`. -/
theorem gamma2Norm_communicationMatrix_protocol_le {X Y : Type*} [Fintype X] [Fintype Y]
    (p : Protocol X Y Bool) :
    CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p.run) ≤ p.leafCount := by
  classical
  have hdecomp : communicationMatrix ℝ p.run =
      ∑ l : Fin p.leafCount,
        if p.leafOutput l = true then
          _root_.Matrix.vecMulVec
            (fun x ↦ if x ∈ p.leafAlice l then (1 : ℝ) else 0)
            (fun y ↦ if y ∈ p.leafBob l then (1 : ℝ) else 0)
        else 0 := by
    ext x y
    simp only [communicationMatrix_apply, _root_.Matrix.sum_apply]
    rw [Finset.sum_eq_single (p.leaf x y)]
    · have hmem : x ∈ p.leafAlice (p.leaf x y) ∧ y ∈ p.leafBob (p.leaf x y) :=
        Protocol.leaf_eq_iff.mp rfl
      rw [Protocol.run_eq_leafOutput hmem.1 hmem.2]
      cases p.leafOutput (p.leaf x y) <;>
        simp [hmem.1, hmem.2, _root_.Matrix.vecMulVec_apply]
    · intro l _ hne
      by_cases hl : p.leafOutput l = true
      · simp only [hl, ↓reduceIte, _root_.Matrix.vecMulVec_apply]
        by_cases hxa : x ∈ p.leafAlice l
        · have hyb : y ∉ p.leafBob l := fun hy ↦ hne (Protocol.leaf_eq_iff.mpr ⟨hxa, hy⟩).symm
          simp [hxa, hyb]
        · simp [hxa]
      · simp [hl]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hdecomp]
  calc CslibFrontier.Matrix.gamma2Norm _
      ≤ ∑ l : Fin p.leafCount, CslibFrontier.Matrix.gamma2Norm
          (if p.leafOutput l = true then
            _root_.Matrix.vecMulVec
              (fun x ↦ if x ∈ p.leafAlice l then (1 : ℝ) else 0)
              (fun y ↦ if y ∈ p.leafBob l then (1 : ℝ) else 0)
          else 0) :=
        CslibFrontier.Matrix.gamma2Norm_sum_le Finset.univ _
    _ ≤ ∑ _l : Fin p.leafCount, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun l _ ↦ ?_)
        split_ifs
        · simpa using CslibFrontier.Matrix.gamma2Norm_vecMulVec_le zero_le_one zero_le_one
            (fun x ↦ by split_ifs <;> norm_num) (fun y ↦ by split_ifs <;> norm_num)
        · simp
    _ = p.leafCount := by simp

/-- **Approximate spectral norm upper bound from randomized communication**
: for every Boolean function
`f : (ι → Bool) → Bool`, any `0 ≤ ε' < ε`, and any `c : ℕ`, if the `ε'`-error public-coin
communication complexity of `(x, y) ↦ f (x + y)` is at most `c`, then
`approxSpectralNorm ε (bitVal ℝ ∘ f) ≤ 2 ^ c`.
-/
theorem approxSpectralNorm_le_two_pow_publicCoin {f : (ι → Bool) → Bool} {ε' ε : ℝ} {c : ℕ}
    (hε : ε' < ε)
    (hcc : PublicCoin.ecomplexityFun ε' (fun x y : ι → Bool ↦ f (x + y)) ≤ c) :
    approxSpectralNorm ε (fun x ↦ bitVal ℝ (f x)) ≤ (2 : ℝ) ^ c := by
  classical
  rw [PublicCoin.ecomplexityFun, PublicCoin.ecomplexity_le_iff] at hcc
  obtain ⟨μ, hsolves, hdepth⟩ := hcc
  let P := Protocol (ι → Bool) (ι → Bool) Bool
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hcard : (2 : ℝ) ^ Fintype.card ι = N := by simp [N]
  -- Summability of `(μ p).toReal` and bounded multiples thereof.
  have hsum_one : HasSum (fun p : P ↦ (μ p).toReal) 1 := by
    have h := ENNReal.hasSum_toReal (μ.tsum_coe ▸ ENNReal.one_ne_top)
    simpa [μ.tsum_coe] using h
  have hsumm : Summable (fun p : P ↦ (μ p).toReal) := hsum_one.summable
  have hsumm_bdd : ∀ (w : P → ℝ) (B : ℝ), (∀ p, |w p| ≤ B) →
      Summable (fun p : P ↦ (μ p).toReal * w p) := by
    intro w B hB
    refine Summable.of_norm_bounded (hsumm.mul_right (max B 0)) (fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left ((hB p).trans (le_max_left B 0)) ENNReal.toReal_nonneg
  let avg : P → (ι → Bool) → ℝ := fun p z ↦
    (∑ y : ι → Bool, bitVal ℝ (p.run (z + y) y)) / N
  have havg_bdd : ∀ p z, |avg p z| ≤ 1 := by
    intro p z
    have h0 : 0 ≤ avg p z :=
      div_nonneg (Finset.sum_nonneg fun y _ ↦ by cases p.run (z + y) y <;> norm_num) hN.le
    have h1 : avg p z ≤ 1 := by
      rw [div_le_one hN]
      calc ∑ y : ι → Bool, bitVal ℝ (p.run (z + y) y)
          ≤ ∑ _y : ι → Bool, (1 : ℝ) :=
            Finset.sum_le_sum (fun y _ ↦ by cases p.run (z + y) y <;> norm_num)
        _ = N := by simp [N]
    rw [abs_of_nonneg h0]
    exact h1
  let g : (ι → Bool) → ℝ := fun z ↦ ∑' p : P, (μ p).toReal * avg p z
  -- Step 1: Verify `|bitVal ℝ (f z) - g z| ≤ ε' < ε` for every `z`.
  have happrox : ∀ z : ι → Bool, |bitVal ℝ (f z) - g z| < ε := by
    intro z
    have hpt : ∀ y : ι → Bool,
        |bitVal ℝ (f (z + y + y)) - ∑' p : P, (μ p).toReal * bitVal ℝ (p.run (z + y) y)| ≤
          ε' := by
      intro y
      have herr : μ.errorProb (fun a b r ↦ f (a + b) = r) (z + y) y ≤ ε' :=
        hsolves (z + y) (Set.mem_univ _) y (Set.mem_univ _)
      have hsumm_pt := hsumm_bdd (fun p ↦ bitVal ℝ (p.run (z + y) y)) 1
        (fun p ↦ by cases p.run (z + y) y <;> norm_num)
      have hadd : z + y + y = z := by
        ext i; change ((z i + y i) + y i : Bool) = z i; cases z i <;> cases y i <;> rfl
      have hdiff : bitVal ℝ (f z) -
          (∑' p : P, (μ p).toReal * bitVal ℝ (p.run (z + y) y)) =
          ∑' p : P, (μ p).toReal * (bitVal ℝ (f z) - bitVal ℝ (p.run (z + y) y)) := by
        have hc : bitVal ℝ (f z) = ∑' p : P, (μ p).toReal * bitVal ℝ (f z) := by
          rw [tsum_mul_right, hsum_one.tsum_eq, one_mul]
        conv_lhs => rw [hc]
        rw [← (hsumm.mul_right _).tsum_sub hsumm_pt]
        exact tsum_congr (fun p ↦ by ring)
      rw [hadd, hdiff]
      have herr_tsum : μ.errorProb (fun a b r ↦ f (a + b) = r) (z + y) y =
          ∑' p : P, (μ p).toReal * |bitVal ℝ (f z) - bitVal ℝ (p.run (z + y) y)| := by
        simp only [PublicCoin.errorProb, Cslib.Probability.PMF.errorProb,
          PMF.toOuterMeasure_apply, hadd]
        rw [ENNReal.tsum_toReal_eq (fun p ↦ by
          simp only [Set.indicator_apply]
          split_ifs
          · exact μ.apply_ne_top p
          · exact ENNReal.zero_ne_top)]
        refine tsum_congr (fun p ↦ ?_)
        by_cases hfp : f z = p.run (z + y) y
        · have hnot : p ∉ {a : P | ¬f z = a.run (z + y) y} := not_not.mpr hfp
          rw [Set.indicator_of_notMem hnot, hfp]
          simp
        · have hmem : p ∈ {a : P | ¬f z = a.run (z + y) y} := hfp
          rw [Set.indicator_of_mem hmem]
          cases hf : f z <;> cases hp : p.run (z + y) y
          · exact absurd (hf.trans hp.symm) hfp
          · norm_num
          · norm_num
          · exact absurd (hf.trans hp.symm) hfp
      have hsumm_norm : Summable (fun p : P ↦
          ‖(μ p).toReal * (bitVal ℝ (f z) - bitVal ℝ (p.run (z + y) y))‖) := by
        refine (hsumm_bdd (fun p ↦ |bitVal ℝ (f z) - bitVal ℝ (p.run (z + y) y)|) 1
          (fun p ↦ by cases f z <;> cases p.run (z + y) y <;> norm_num)).congr (fun p ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      have hle : |∑' p : P, (μ p).toReal * (bitVal ℝ (f z) - bitVal ℝ (p.run (z + y) y))| ≤
          ∑' p : P, (μ p).toReal * |bitVal ℝ (f z) - bitVal ℝ (p.run (z + y) y)| := by
        have hn := norm_tsum_le_tsum_norm hsumm_norm
        rw [Real.norm_eq_abs] at hn
        refine hn.trans_eq (tsum_congr fun p ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (hle.trans_eq herr_tsum.symm).trans herr
    have hg_sum : g z =
        (∑ y : ι → Bool, ∑' p : P, (μ p).toReal * bitVal ℝ (p.run (z + y) y)) / N := by
      simp only [g, avg]
      simp_rw [← mul_div_assoc]
      rw [tsum_div_const]
      congr 1
      rw [← Summable.tsum_finsetSum (fun y _ ↦
        hsumm_bdd (fun p ↦ bitVal ℝ (p.run (z + y) y)) 1
          (fun p ↦ by cases p.run (z + y) y <;> norm_num))]
      exact tsum_congr (fun p ↦ Finset.mul_sum _ _ _)
    have hf_sum : bitVal ℝ (f z) = (∑ _y : ι → Bool, bitVal ℝ (f z)) / N := by
      simp [N]
    have hadd_cancel : ∀ y : ι → Bool, z + y + y = z := fun y ↦ by
      ext i; change ((z i + y i) + y i : Bool) = z i; cases z i <;> cases y i <;> rfl
    have hle : |bitVal ℝ (f z) - g z| ≤ ε' := by
      rw [hg_sum]
      conv_lhs => rw [hf_sum]
      rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hN, div_le_iff₀ hN]
      calc |∑ y : ι → Bool, (bitVal ℝ (f z) -
              ∑' p : P, (μ p).toReal * bitVal ℝ (p.run (z + y) y))|
          ≤ ∑ y : ι → Bool, |bitVal ℝ (f z) -
              ∑' p : P, (μ p).toReal * bitVal ℝ (p.run (z + y) y)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y : ι → Bool, ε' := Finset.sum_le_sum (fun y _ ↦ by
            simpa only [hadd_cancel y] using hpt y)
        _ = ε' * N := by simp [N, mul_comm]
    exact hle.trans_lt hε
  -- Step 2: Bound `fourierSpectralNorm g ≤ 2 ^ c` by interchanging finite sums with `tsum`.
  have hspec : fourierSpectralNorm g ≤ (2 : ℝ) ^ c := by
    have hfc : ∀ S : Finset ι, fourierCoeff g S =
        ∑' p : P, (μ p).toReal * fourierCoeff (avg p) S := by
      intro S
      simp only [fourierCoeff_eq_sum, hcard, g]
      have hcomm : ∑ z : ι → Bool, (∑' p : P, (μ p).toReal * avg p z) * chi ℝ S z =
          ∑' p : P, (μ p).toReal * ∑ z : ι → Bool, avg p z * chi ℝ S z := by
        simp_rw [← tsum_mul_right]
        rw [← Summable.tsum_finsetSum (fun z _ ↦
          (hsumm_bdd _ 1 (fun p ↦ havg_bdd p z)).mul_right _)]
        refine tsum_congr (fun p ↦ ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      rw [hcomm, ← tsum_div_const]
      exact tsum_congr (fun p ↦ mul_div_assoc _ _ _)
    have hfc_bdd : ∀ S p, |fourierCoeff (avg p) S| ≤ 1 := by
      intro S p
      rw [fourierCoeff_eq_sum, hcard, abs_div, abs_of_pos hN, div_le_one hN]
      calc |∑ z : ι → Bool, avg p z * chi ℝ S z|
          ≤ ∑ z : ι → Bool, |avg p z| * |chi ℝ S z| :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (le_of_eq (Finset.sum_congr rfl fun _ _ ↦ abs_mul _ _))
        _ ≤ ∑ _z : ι → Bool, (1 : ℝ) :=
            Finset.sum_le_sum (fun z _ ↦ by rw [abs_chi, mul_one]; exact havg_bdd p z)
        _ = N := by simp [N]
    have havg_norm : ∀ p : P, (μ p).toReal * fourierSpectralNorm (avg p) ≤
        (μ p).toReal * (2 : ℝ) ^ c := by
      intro p
      by_cases hp : p ∈ μ.support
      · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hpd : p.depth ≤ c := by
          exact_mod_cast PublicCoin.depth_le_iff.mp hdepth p hp
        calc fourierSpectralNorm (avg p)
            ≤ CslibFrontier.Matrix.gamma2Norm (communicationMatrix ℝ p.run) :=
              fourierSpectralNorm_xorAvg_le_gamma2Norm (communicationMatrix ℝ p.run)
          _ ≤ p.leafCount := gamma2Norm_communicationMatrix_protocol_le p
          _ ≤ (2 ^ p.depth : ℕ) := by exact_mod_cast p.leafCount_le_two_pow_depth
          _ ≤ (2 : ℝ) ^ c := by
              rw [Nat.cast_pow, Nat.cast_ofNat]
              exact pow_le_pow_right₀ (by norm_num) hpd
      · simp only [PMF.mem_support_iff, not_not] at hp
        simp [hp]
    have hfc_abs : ∀ S, Summable (fun p : P ↦ (μ p).toReal * |fourierCoeff (avg p) S|) :=
      fun S ↦ hsumm_bdd (fun p ↦ |fourierCoeff (avg p) S|) 1
        (fun p ↦ by simpa only [abs_abs] using hfc_bdd S p)
    calc fourierSpectralNorm g
        ≤ ∑ S : Finset ι, ∑' p : P, (μ p).toReal * |fourierCoeff (avg p) S| := by
          refine Finset.sum_le_sum (fun S _ ↦ ?_)
          rw [hfc S]
          have hs : Summable (fun p : P ↦ ‖(μ p).toReal * fourierCoeff (avg p) S‖) :=
            (hfc_abs S).congr (fun p ↦ by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])
          have hn := norm_tsum_le_tsum_norm hs
          rw [Real.norm_eq_abs] at hn
          exact hn.trans_eq (tsum_congr fun p ↦ by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])
      _ = ∑' p : P, (μ p).toReal * fourierSpectralNorm (avg p) := by
          rw [← Summable.tsum_finsetSum (fun S _ ↦ hfc_abs S)]
          exact tsum_congr (fun p ↦ by rw [← Finset.mul_sum]; rfl)
      _ ≤ ∑' p : P, (μ p).toReal * (2 : ℝ) ^ c := by
          have hsL : Summable (fun p : P ↦ (μ p).toReal * fourierSpectralNorm (avg p)) := by
            refine Summable.of_nonneg_of_le
              (fun p ↦ mul_nonneg ENNReal.toReal_nonneg (fourierSpectralNorm_nonneg _))
              havg_norm (hsumm.mul_right _)
          exact hsL.tsum_le_tsum havg_norm (hsumm.mul_right _)
      _ = (2 : ℝ) ^ c := by rw [tsum_mul_right, hsum_one.tsum_eq, one_mul]
  exact (approxSpectralNorm_le_of_approx happrox).trans hspec

/-- If `(x, y) ↦ f (x + y)` has `1/3`-error public-coin randomized communication cost at most `c`,
then `approxSpectralNorm (1 / 3) (bitVal ℝ ∘ f) ≤ 2 ^ (20 * c)`. -/
theorem approxSpectralNorm_one_third_le_of_publicCoin {f : (ι → Bool) → Bool} {c : ℕ}
    (hcc : PublicCoin.ecomplexityFun (1 / 3) (fun x y : ι → Bool ↦ f (x + y)) ≤ c) :
    approxSpectralNorm (1 / 3) (fun x ↦ bitVal ℝ (f x)) ≤ (2 : ℝ) ^ (20 * c) := by
  have hamp : PublicCoin.ecomplexityFun ((8 / 9 : ℝ) ^ 10) (fun x y ↦ f (x + y)) ≤
      (20 * c : ℕ) := by
    calc PublicCoin.ecomplexityFun ((8 / 9 : ℝ) ^ 10) (fun x y ↦ f (x + y))
        ≤ 2 * 10 * PublicCoin.ecomplexityFun (1 / 3) (fun x y ↦ f (x + y)) :=
          PublicCoin.ecomplexityFun_le_two_mul_mul_one_third 10
      _ ≤ 2 * 10 * (c : ℕ∞) := mul_le_mul_right hcc _
      _ = (20 * c : ℕ) := by norm_cast
  have hlt : (8 / 9 : ℝ) ^ 10 < 1 / 3 := by norm_num
  exact approxSpectralNorm_le_two_pow_publicCoin hlt hamp

end BooleanAnalysis

end CslibFrontier
