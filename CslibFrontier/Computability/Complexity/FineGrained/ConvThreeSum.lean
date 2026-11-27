/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Complexity.FineGrained.ResidueHashing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The 3SUM and Convolution-3SUM Problems and Reduction from Convolution-3SUM to 3SUM

This module formulates the positive-integer three-set `3SUM` and `Convolution-3SUM` decision
problems and their subquadratic fine-grained complexity hypotheses (`ThreeSumHypothesis` and
`ConvThreeSumHypothesis`) on deterministic multi-tape Turing machines, aligned with
`Cslib.Complexity.OVH`, and constructs the deterministic quasi-linear index-encoding reduction
`convToThreeSum : ConvThreeSum → ThreeSum`.

## Main definitions

* `CslibFrontier.Complexity.ThreeSumInput`, `CslibFrontier.Complexity.encThreeSum`,
  `CslibFrontier.Complexity.ThreeSum`, `CslibFrontier.Complexity.threeSumSize`,
  `CslibFrontier.Complexity.threeSumBitScale`, `CslibFrontier.Complexity.ThreeSumHypothesis`:
  the three-set positive-integer `3SUM` decision problem and hypothesis.
* `CslibFrontier.Complexity.encConvThreeSum`, `CslibFrontier.Complexity.ConvThreeSum`,
  `CslibFrontier.Complexity.convThreeSumBitScale`,
  `CslibFrontier.Complexity.ConvThreeSumHypothesis`:
  the positive-integer `Convolution-3SUM` decision problem and hypothesis.
* `CslibFrontier.Complexity.allPosNatList`, `CslibFrontier.Complexity.maxNatList`:
  streaming positivity check and list maximum on `List ℕ`.
* `CslibFrontier.Complexity.convToThreeSum`: deterministic index-encoding reduction from
  `ConvThreeSum`
  to `ThreeSum`.

## Main results

* `CslibFrontier.Complexity.exists_nat_size_pow_le_rpow`: polylogarithmic factors `(n.size + 1) ^
  K` are
  dominated by `C * n ^ δ` for every `δ > 0`.
* `CslibFrontier.Complexity.computableInO_allPosNatList`,
  `CslibFrontier.Complexity.computableInO_maxNatList`:
  quasi-linear multi-tape Turing machine complexity of `allPosNatList` and `maxNatList`.
* `CslibFrontier.Complexity.convToThreeSum_mem_iff`,
  `CslibFrontier.Complexity.computableInO_convToThreeSum`,
  `CslibFrontier.Complexity.threeSumHypothesis_of_convThreeSumHypothesis`:
  correctness, quasi-linear complexity, and transfer `ConvThreeSumHypothesis → ThreeSumHypothesis`.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Complexity

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

private theorem length_encList_le_mul {α : Type*} (enc : α ↪ List Bool) (L : List α) {b : ℕ}
    (hb : ∀ a ∈ L, (enc a).length ≤ b) :
    (encList enc L).length ≤ L.length * (2 * b + 1) := by
  induction L with
  | nil => simp
  | cons a as ih =>
    rw [encList_cons, List.length_append, length_frame, List.length_cons,
      Nat.add_mul as.length 1, Nat.one_mul]
    have ha := hb a (List.mem_cons_self ..)
    have has := ih fun x hx => hb x (List.mem_cons_of_mem _ hx)
    omega

private theorem size_pos_of_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n.size :=
  Nat.size_pos.mpr (by omega)

private theorem two_pow_pred_size_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ (n.size - 1) ≤ n := by
  by_contra! hc
  have := Nat.size_le.mpr hc
  have := size_pos_of_pos hn
  omega

/-- Every polylogarithmic factor `((n.size + 1 : ℕ) : ℝ) ^ K` is bounded by `C * (n : ℝ) ^ δ`
for all `n ≥ 1` whenever `δ > 0`. -/
theorem exists_nat_size_pow_le_rpow (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ((n.size + 1 : ℕ) : ℝ) ^ K ≤ (C : ℝ) * (n : ℝ) ^ δ := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine ⟨1, le_rfl, fun n hn => ?_⟩
    simp only [pow_zero, Nat.cast_one, one_mul]
    exact Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  · have hδK : 0 < δ / (K : ℝ) := div_pos hδ (by positivity)
    have hlo := (isLittleO_log_rpow_atTop hδK).eventuallyLE
    rw [Filter.eventually_atTop] at hlo
    obtain ⟨R, hR⟩ := hlo
    let N₀ : ℕ := max 1 (Nat.ceil R)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hsz_log (n : ℕ) (hn : 1 ≤ n) :
        ((n.size + 1 : ℕ) : ℝ) ≤ (1 / Real.log 2) * Real.log n + 2 := by
      have hsp : 1 ≤ n.size := size_pos_of_pos hn
      have hpow : (2 : ℝ) ^ (n.size - 1) ≤ (n : ℝ) := by exact_mod_cast two_pow_pred_size_le hn
      have hlg := Real.log_le_log (by positivity) hpow
      rw [Real.log_pow] at hlg
      have hdiv : ((n.size - 1 : ℕ) : ℝ) ≤ (1 / Real.log 2) * Real.log n := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog2]; linarith
      have hcast : ((n.size + 1 : ℕ) : ℝ) = ((n.size - 1 : ℕ) : ℝ) + 2 := by
        have : n.size + 1 = (n.size - 1) + 2 := by omega
        exact_mod_cast this
      linarith
    let A : ℝ := 1 / Real.log 2 + 2
    have hA_pos : 0 < A := by dsimp only [A]; positivity
    have htail : ∀ n : ℕ, N₀ ≤ n → ((n.size + 1 : ℕ) : ℝ) ^ K ≤ A ^ K * (n : ℝ) ^ δ := by
      intro n hn
      have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
      have hnR : R ≤ (n : ℝ) :=
        (Nat.le_ceil R).trans (by exact_mod_cast (le_max_right 1 _).trans hn)
      have hlr : Real.log (n : ℝ) ≤ (n : ℝ) ^ (δ / (K : ℝ)) := by
        have h := hR (n : ℝ) hnR
        have hnn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
        have hrnn : 0 ≤ (n : ℝ) ^ (δ / (K : ℝ)) := by positivity
        simpa only [Real.norm_of_nonneg hnn, Real.norm_of_nonneg hrnn] using h
      have h1r : (1 : ℝ) ≤ (n : ℝ) ^ (δ / (K : ℝ)) :=
        Real.one_le_rpow (by exact_mod_cast hn1) hδK.le
      have hbase : ((n.size + 1 : ℕ) : ℝ) ≤ A * (n : ℝ) ^ (δ / (K : ℝ)) := by
        have hs := hsz_log n hn1
        have hc : 0 ≤ 1 / Real.log 2 := by positivity
        dsimp only [A]; nlinarith
      calc ((n.size + 1 : ℕ) : ℝ) ^ K
          ≤ (A * (n : ℝ) ^ (δ / (K : ℝ))) ^ K := pow_le_pow_left₀ (by positivity) hbase K
        _ = A ^ K * ((n : ℝ) ^ (δ / (K : ℝ))) ^ (K : ℝ) := by
            rw [mul_pow, Real.rpow_natCast]
        _ = A ^ K * (n : ℝ) ^ δ := by
            rw [← Real.rpow_mul (Nat.cast_nonneg n), div_mul_cancel₀ δ (by positivity)]
    let C : ℕ := max 1 (max (Nat.ceil (A ^ K)) ((N₀.size + 1) ^ K))
    refine ⟨C, le_max_left 1 _, fun n hn => ?_⟩
    by_cases hge : N₀ ≤ n
    · refine (htail n hge).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans (le_max_right 1 _))
    · have hle : n ≤ N₀ := by omega
      have hsz : n.size + 1 ≤ N₀.size + 1 := Nat.succ_le_succ (Nat.size_le_size hle)
      have hpow : ((n.size + 1 : ℕ) : ℝ) ^ K ≤ (C : ℝ) := by
        have h1 : (n.size + 1) ^ K ≤ C :=
          (Nat.pow_le_pow_left hsz K).trans ((le_max_right _ _).trans (le_max_right 1 _))
        exact_mod_cast h1
      have hr1 : (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hn) hδ.le
      nlinarith

/-! ### Problem and hypothesis definitions -/

/-- Input triple `(X, (Y, Z))` of positive-integer lists for `ThreeSum`. -/
abbrev ThreeSumInput := List ℕ × (List ℕ × List ℕ)

/-- Binary tape encoding of `ThreeSumInput`. -/
@[expose] def encThreeSum : ThreeSumInput ↪ List Bool :=
  encPair (encList encNat) (encPair (encList encNat) (encList encNat))

/-- The positive-integer three-set `3SUM` problem: duplicate-free equal-length lists `X, Y, Z` of
positive natural numbers admitting `x ∈ X`, `y ∈ Y`, `z ∈ Z` with `x + y = z`. -/
def ThreeSum : Set ThreeSumInput :=
  {p | p.1.Nodup ∧ p.2.1.Nodup ∧ p.2.2.Nodup ∧
    p.1.length = p.2.1.length ∧ p.2.1.length = p.2.2.length ∧
    (∀ x ∈ p.1, 0 < x) ∧ (∀ y ∈ p.2.1, 0 < y) ∧ (∀ z ∈ p.2.2, 0 < z) ∧
    ∃ x ∈ p.1, ∃ y ∈ p.2.1, ∃ z ∈ p.2.2, x + y = z}

/-- Total list size `|X| + |Y| + |Z|` of a `ThreeSum` input (`3 * n` when `|X| = |Y| = |Z| = n`). -/
def threeSumSize (p : ThreeSumInput) : ℕ :=
  p.1.length + p.2.1.length + p.2.2.length

/-- Coordinate bit-scale `max_{w ∈ X ∪ Y ∪ Z} w.size + 1` of a `ThreeSum` input. -/
def threeSumBitScale (p : ThreeSumInput) : ℕ :=
  max (listMax Nat.size p.1) (max (listMax Nat.size p.2.1) (listMax Nat.size p.2.2)) + 1

/-- Explicit sum expansion of `threeSumSize`. -/
theorem threeSumSize_add (p : ThreeSumInput) :
    p.1.length + p.2.1.length + p.2.2.length = threeSumSize p := by
  unfold threeSumSize; rfl

@[simp]
theorem threeSumSize_empty : threeSumSize ([], ([], [])) = 0 := by
  unfold threeSumSize; rfl

@[simp]
theorem threeSumBitScale_empty : threeSumBitScale ([], ([], [])) = 1 := by
  unfold threeSumBitScale; rfl

/-- Every `threeSumBitScale p` is positive. -/
theorem threeSumBitScale_pos (p : ThreeSumInput) : 1 ≤ threeSumBitScale p := by
  unfold threeSumBitScale; omega

/-- Each component's maximum bit-length is strictly below `threeSumBitScale p`. -/
theorem listMax_size_lt_threeSumBitScale (p : ThreeSumInput) :
    listMax Nat.size p.1 < threeSumBitScale p ∧
      listMax Nat.size p.2.1 < threeSumBitScale p ∧
      listMax Nat.size p.2.2 < threeSumBitScale p := by
  unfold threeSumBitScale; omega

@[simp]
theorem not_empty_mem_threeSum : (([], ([], [])) : ThreeSumInput) ∉ ThreeSum := by
  unfold ThreeSum; simp

/-- Membership characterization for `ThreeSum`. -/
theorem mem_threeSum_iff (p : ThreeSumInput) :
    p ∈ ThreeSum ↔
      p.1.Nodup ∧ p.2.1.Nodup ∧ p.2.2.Nodup ∧
        p.1.length = p.2.1.length ∧ p.2.1.length = p.2.2.length ∧
        (∀ x ∈ p.1, 0 < x) ∧ (∀ y ∈ p.2.1, 0 < y) ∧ (∀ z ∈ p.2.2, 0 < z) ∧
        ∃ x ∈ p.1, ∃ y ∈ p.2.1, ∃ z ∈ p.2.2, x + y = z := Iff.rfl

/-- **The 3SUM Hypothesis**: for every `ε > 0` and `e : ℕ`, `ThreeSum` is not decidable on a
deterministic multi-tape Turing machine within time `O(N ^ (2 - ε) * (log M) ^ e)`. -/
@[expose] def ThreeSumHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ e : ℕ, ¬ DecidableInTimeO ThreeSum encThreeSum
    fun p => (threeSumSize p : ℝ) ^ (2 - ε) * (threeSumBitScale p : ℝ) ^ e

/-- Binary tape encoding of `ConvThreeSum` instances. -/
@[expose] def encConvThreeSum : List ℕ ↪ List Bool := encList encNat

/-- The positive-integer `Convolution-3SUM` problem: sequences `X` of positive natural numbers
admitting indices `i, j` with `i + j < X.length` and `X[i] + X[j] = X[i + j]`. -/
def ConvThreeSum : Set (List ℕ) :=
  {X | (∀ x ∈ X, 0 < x) ∧
    ∃ (i j : ℕ) (h : i + j < X.length), X[i]'(by omega) + X[j]'(by omega) = X[i + j]'h}

/-- Coordinate bit-scale `max_{x ∈ X} x.size + 1` of a `ConvThreeSum` input. -/
def convThreeSumBitScale (X : List ℕ) : ℕ :=
  listMax Nat.size X + 1

@[simp]
theorem convThreeSumBitScale_nil : convThreeSumBitScale [] = 1 := by
  unfold convThreeSumBitScale; rfl

/-- Upper bound on `convThreeSumBitScale X` from a uniform element bit-length bound. -/
theorem convThreeSumBitScale_le {X : List ℕ} {b : ℕ} (h : ∀ a ∈ X, a.size ≤ b) :
    convThreeSumBitScale X ≤ b + 1 :=
  Nat.succ_le_succ (listMax_le h)

/-- Lower bound `listMax Nat.size X < convThreeSumBitScale X`. -/
theorem listMax_size_lt_convThreeSumBitScale (X : List ℕ) :
    listMax Nat.size X < convThreeSumBitScale X := by
  unfold convThreeSumBitScale; omega

@[simp]
theorem not_nil_mem_convThreeSum : ([] : List ℕ) ∉ ConvThreeSum := by
  unfold ConvThreeSum; simp

/-- Membership characterization for `ConvThreeSum`. -/
theorem mem_convThreeSum_iff (X : List ℕ) :
    X ∈ ConvThreeSum ↔
      (∀ x ∈ X, 0 < x) ∧
        ∃ (i j : ℕ) (h : i + j < X.length), X[i]'(by omega) + X[j]'(by omega) = X[i + j]'h :=
  Iff.rfl

/-- **The Convolution-3SUM Hypothesis**: for every `ε > 0` and `e : ℕ`, `ConvThreeSum` is not
decidable on a deterministic multi-tape Turing machine within time
`O(n ^ (2 - ε) * (log M) ^ e)`. -/
@[expose] def ConvThreeSumHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ e : ℕ, ¬ DecidableInTimeO ConvThreeSum encConvThreeSum
    fun X => (X.length : ℝ) ^ (2 - ε) * (convThreeSumBitScale X : ℝ) ^ e

attribute [local irreducible] encNat encUnary

/-! ### Streaming positivity check and list maximum -/

/-- Decides whether every element of `L : List ℕ` is strictly positive via a single left fold. -/
def allPosNatList (L : List ℕ) : Bool :=
  L.foldl (fun b x => b && !decide (x = 0)) true

/-- `allPosNatList L = true` if and only if every element of `L` is strictly positive. -/
theorem allPosNatList_eq_true_iff (L : List ℕ) :
    allPosNatList L = true ↔ ∀ x ∈ L, 0 < x := by
  unfold allPosNatList
  suffices ∀ b, L.foldl (fun s x => s && !decide (x = 0)) b = true ↔
      b = true ∧ ∀ x ∈ L, 0 < x by simpa using this true
  induction L with
  | nil => simp
  | cons a as ih =>
    intro b; rw [List.foldl_cons, ih]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨⟨hb, ha⟩, has⟩; exact ⟨hb, by omega, has⟩
    · rintro ⟨hb, ha, has⟩; exact ⟨⟨hb, by omega⟩, has⟩

/-- `allPosNatList` is computable in quasi-linear time on a multi-tape Turing machine. -/
theorem computableInO_allPosNatList :
    ∃ d, ComputableInO allPosNatList (encList encNat) encBool
      (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ d)
      (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ d) := by
  have hnext : ComputableInPolyTime (fun p : Bool × ℕ => p.1 && !decide (p.2 = 0))
      (encPair encBool encNat) encBool := by fun_prop
  have hblen : ∀ b : Bool, (encBool b).length = 1 := by rintro (_ | _) <;> rfl
  obtain ⟨df, hfold⟩ := computableInO_streamFold
    (lMax := fun p : Bool × List ℕ => listMax Nat.size p.2 + 2)
    Prod.fst Prod.snd (fun _ => rfl) hnext
    (fun p j _ => by rw [hblen]; omega)
    (fun p j hj => by
      rw [length_encNat]; have := le_listMax (f := Nat.size) (List.getElem_mem hj); omega)
  have hinit : ComputableInO (fun L : List ℕ => (true, L))
      (encList encNat) (encPair encBool (encList encNat))
      (fun L => (encList encNat L).length) (fun L => (encList encNat L).length) :=
    ((ComputableInO.constZero true).prod (ComputableInO.of_eq fun _ => rfl)).mono 2
      (fun _ => by omega) (fun _ => by omega)
  refine ⟨df + 1, ((hfold.comp hinit).of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (12 + 2 ^ df) 0 fun L => ?_
    let S := listMax Nat.size L + 4
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hSD : S ≤ S ^ (df + 1) := Nat.le_self_pow (by omega) S
    have hlen : (encList encNat L).length ≤ 3 * ((L.length + 1) * S ^ (df + 1)) := by
      have h1 := (length_encList_le_mul encNat L (b := listMax Nat.size L) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _ (by dsimp only [S]; omega : _ ≤ 3 * S))
      nlinarith [Nat.mul_le_mul (Nat.le_succ L.length) hSD]
    have hpair : (encPair encBool (encList encNat) (true, L)).length ≤
        6 * ((L.length + 1) * S ^ (df + 1)) := by
      rw [length_encPair, hblen]; dsimp only
      have : 1 ≤ (L.length + 1) * S ^ (df + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ hS1)
      omega
    have hp : (listMax Nat.size L + 2 + 1) ^ df ≤ 2 ^ df * S ^ (df + 1) :=
      (Nat.pow_le_pow_left (by dsimp only [S]; omega : _ ≤ 2 * S) df).trans
        ((Nat.mul_pow 2 S df).le.trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by omega : df ≤ df + 1))))
    have hmul := (Nat.mul_le_mul_left (L.length + 1) hp).trans_eq (Nat.mul_left_comm _ _ _)
    have hp' := hp.trans (Nat.mul_le_mul_left _
      (Nat.le_mul_of_pos_left _ (show 0 < L.length + 1 by omega)))
    dsimp only [Function.comp_apply, S] at *
    rw [Nat.add_mul 12 (2 ^ df)]; omega

/-- Computes the maximum element of `L : List ℕ` (with `0` for `[]`) via a single left fold. -/
def maxNatList (L : List ℕ) : ℕ :=
  L.foldl (fun a b => if decide (a ≤ b) then b else a) 0

/-- `maxNatList L` equals `listMax id L`. -/
theorem maxNatList_eq_listMax (L : List ℕ) : maxNatList L = listMax id L := by
  have heq : (fun a b : ℕ => if decide (a ≤ b) then b else a) = max := by
    funext a b; simp only [Nat.max_def, decide_eq_true_eq]
  unfold maxNatList listMax
  rw [heq]
  suffices ∀ m, L.foldl max m = max m (L.foldr max 0) by simpa using this 0
  induction L with
  | nil => simp
  | cons x xs ih =>
    intro m; simp only [List.foldl_cons, List.foldr_cons, ih, max_assoc]

/-- The binary bit-length of `maxNatList L` is at most `listMax Nat.size L`. -/
theorem maxNatList_size_le (L : List ℕ) : (maxNatList L).size ≤ listMax Nat.size L := by
  rw [maxNatList_eq_listMax]
  induction L with
  | nil => rfl
  | cons x xs ih =>
    change (max x (listMax id xs)).size ≤ max x.size (listMax Nat.size xs)
    rcases le_total x (listMax id xs) with h | h
    · rw [max_eq_right h]; exact ih.trans (le_max_right _ _)
    · rw [max_eq_left h]; exact le_max_left _ _

/-- `maxNatList` is computable in quasi-linear time on a multi-tape Turing machine. -/
theorem computableInO_maxNatList :
    ∃ d, ComputableInO maxNatList (encList encNat) encNat
      (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ d)
      (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ d) := by
  have hnext : ComputableInPolyTime (fun p : ℕ × ℕ => if decide (p.1 ≤ p.2) then p.2 else p.1)
      (encPair encNat encNat) encNat := by fun_prop
  have hfold_sz (t : List ℕ) (m : ℕ) :
      (t.foldl (fun a b => if decide (a ≤ b) then b else a) m).size ≤
        max m.size (listMax Nat.size t) := by
    induction t generalizing m with
    | nil => exact le_max_left _ _
    | cons x xs ih =>
      rw [List.foldl_cons]
      change _ ≤ max m.size (max x.size (listMax Nat.size xs))
      refine (ih _).trans (max_le ?_ (le_max_of_le_right (le_max_right _ _)))
      split_ifs
      · exact le_max_of_le_right (le_max_left _ _)
      · exact le_max_left _ _
  obtain ⟨df, hfold⟩ := computableInO_streamFold
    (lMax := fun p : ℕ × List ℕ => p.1.size + listMax Nat.size p.2 + 2)
    Prod.fst Prod.snd (fun _ => rfl) hnext
    (fun p j _ => by
      simp only [streamState, length_encNat]
      have h1 := hfold_sz (p.2.take j) p.1
      have h2 : listMax Nat.size (p.2.take j) ≤ listMax Nat.size p.2 :=
        listMax_le fun x hx => le_listMax (f := Nat.size) (List.mem_of_mem_take hx)
      omega)
    (fun p j hj => by
      rw [length_encNat]; have := le_listMax (f := Nat.size) (List.getElem_mem hj); omega)
  have hinit : ComputableInO (fun L : List ℕ => (0, L))
      (encList encNat) (encPair encNat (encList encNat))
      (fun L => (encList encNat L).length) (fun L => (encList encNat L).length) :=
    ((ComputableInO.constZero 0).prod (ComputableInO.of_eq fun _ => rfl)).mono 2
      (fun _ => by omega) (fun _ => by omega)
  have h0s : (0 : ℕ).size = 0 := by decide
  refine ⟨df + 1, ((hfold.comp hinit).of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (12 + 2 ^ df) 0 fun L => ?_
    let S := listMax Nat.size L + 4
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hSD : S ≤ S ^ (df + 1) := Nat.le_self_pow (by omega) S
    have hlen : (encList encNat L).length ≤ 3 * ((L.length + 1) * S ^ (df + 1)) := by
      have h1 := (length_encList_le_mul encNat L (b := listMax Nat.size L) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _ (by dsimp only [S]; omega : _ ≤ 3 * S))
      nlinarith [Nat.mul_le_mul (Nat.le_succ L.length) hSD]
    have hpair : (encPair encNat (encList encNat) (0, L)).length ≤
        6 * ((L.length + 1) * S ^ (df + 1)) := by
      rw [length_encPair, length_encNat, h0s]; dsimp only
      have : 1 ≤ (L.length + 1) * S ^ (df + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ hS1)
      omega
    have hp : ((0 : ℕ).size + listMax Nat.size L + 2 + 1) ^ df ≤ 2 ^ df * S ^ (df + 1) :=
      (Nat.pow_le_pow_left (by rw [h0s]; dsimp only [S]; omega : _ ≤ 2 * S) df).trans
        ((Nat.mul_pow 2 S df).le.trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by omega : df ≤ df + 1))))
    have hmul := (Nat.mul_le_mul_left (L.length + 1) hp).trans_eq (Nat.mul_left_comm _ _ _)
    have hp' := hp.trans (Nat.mul_le_mul_left _
      (Nat.le_mul_of_pos_left _ (show 0 < L.length + 1 by omega)))
    dsimp only [Function.comp_apply, S] at *
    rw [Nat.add_mul 12 (2 ^ df)]; omega

/-- Mapping any polynomial-time `f : ℕ → ℤ` across `L : List ℕ` runs in quasi-linear time. -/
theorem computableInO_mapNatToInt (f : ℕ → ℤ) (hf : ComputableInPolyTime f encNat encIntBin) :
    ∃ d, ComputableInO (fun L : List ℕ => L.map f) (encList encNat) (encList encIntBin)
      (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ d)
      (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ d) := by
  have hf' := hf.comp (ComputableInPolyTime.snd encUnit encNat)
  obtain ⟨dm, hmap⟩ := computableInO_streamMapWith (f := fun q : Unit × ℕ => f q.2) hf'
    (lMax := fun p : Unit × List ℕ => listMax Nat.size p.2 + 2) (fun _ => Nat.zero_le _)
    (fun p j hj => by
      rw [length_encNat]; have := le_listMax (f := Nat.size) (List.getElem_mem hj); omega)
  have hinit : ComputableInO (fun L : List ℕ => ((), L))
      (encList encNat) (encPair encUnit (encList encNat))
      (fun L => (encList encNat L).length) (fun L => (encList encNat L).length) :=
    ((ComputableInO.constZero ()).prod (ComputableInO.of_eq fun _ => rfl)).mono 2
      (fun _ => by omega) (fun _ => by omega)
  refine ⟨dm + 1, ((hmap.comp hinit).of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (12 + 2 ^ dm) 0 fun L => ?_
    let S := listMax Nat.size L + 4
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hSD : S ≤ S ^ (dm + 1) := Nat.le_self_pow (by omega) S
    have hlen : (encList encNat L).length ≤ 3 * ((L.length + 1) * S ^ (dm + 1)) := by
      have h1 := (length_encList_le_mul encNat L (b := listMax Nat.size L) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _ (by dsimp only [S]; omega : _ ≤ 3 * S))
      nlinarith [Nat.mul_le_mul (Nat.le_succ L.length) hSD]
    have hpair : (encPair encUnit (encList encNat) ((), L)).length ≤
        6 * ((L.length + 1) * S ^ (dm + 1)) := by
      rw [length_encPair]; dsimp only
      have hu : (encUnit ()).length = 0 := rfl
      have : 1 ≤ (L.length + 1) * S ^ (dm + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ hS1)
      rw [hu]; omega
    have hp : (L.length + 1) * (listMax Nat.size L + 2 + 1) ^ dm ≤
        2 ^ dm * ((L.length + 1) * S ^ (dm + 1)) :=
      (Nat.mul_le_mul_left (L.length + 1)
        ((Nat.pow_le_pow_left (by dsimp only [S]; omega : _ ≤ 2 * S) dm).trans
          ((Nat.mul_pow 2 S dm).le.trans
            (Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by omega : dm ≤ dm + 1)))))).trans_eq
        (Nat.mul_left_comm _ _ _)
    dsimp only [Function.comp_apply, S] at *
    rw [Nat.add_mul 12 (2 ^ dm)]; omega

/-! ### Reduction from `ConvThreeSum` to `ThreeSum` -/

private def convShiftList (c B : ℕ) (X : List ℕ) : List ℕ :=
  streamList (fun q : (ℕ × ℕ) × ℕ => (q.1.1, q.1.2 + 1))
    (fun q => [(2 * q.1.2 + c) * q.1.1 + q.2]) (B, 0) X

private theorem convShiftList_aux (c B k : ℕ) (X : List ℕ) :
    streamList (fun q : (ℕ × ℕ) × ℕ => (q.1.1, q.1.2 + 1))
      (fun q => [(2 * q.1.2 + c) * q.1.1 + q.2]) (B, k) X =
      List.ofFn (fun i : Fin X.length => (2 * (k + i) + c) * B + X[i]) := by
  induction X generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [streamList_cons, ih (k + 1), List.ofFn_succ, List.singleton_append, List.cons.injEq]
    refine ⟨by simp, congrArg List.ofFn (funext fun i => ?_)⟩
    simp only [Fin.val_succ]
    change (2 * (k + 1 + ↑i) + c) * B + xs[↑i] = (2 * (k + (↑i + 1)) + c) * B + xs[↑i]
    congr 2; omega

private theorem convShiftList_eq_ofFn (c B : ℕ) (X : List ℕ) :
    convShiftList c B X = List.ofFn (fun i : Fin X.length => (2 * (i : ℕ) + c) * B + X[i]) := by
  simpa [convShiftList] using convShiftList_aux c B 0 X

/-- Deterministic index-encoding reduction from `ConvThreeSum` to `ThreeSum`. -/
def convToThreeSum (X : List ℕ) : ThreeSumInput :=
  if allPosNatList X then
    let B := 2 * (maxNatList X + 1)
    (convShiftList 1 B X, (convShiftList 2 B X, convShiftList 3 B X))
  else ([], ([], []))

/-- `convToThreeSum` is a faithful many-one reduction from `ConvThreeSum` to `ThreeSum`. -/
theorem convToThreeSum_mem_iff (X : List ℕ) : convToThreeSum X ∈ ThreeSum ↔ X ∈ ConvThreeSum := by
  unfold convToThreeSum
  by_cases hpos : allPosNatList X = true
  · simp only [hpos, ↓reduceIte]
    have hXpos : ∀ x ∈ X, 0 < x := (allPosNatList_eq_true_iff X).mp hpos
    let B := 2 * (maxNatList X + 1)
    have hB_gt (i : Fin X.length) : 2 * X[i] < B := by
      dsimp only [B]; rw [maxNatList_eq_listMax]
      have : X[i] ≤ listMax id X := le_listMax (f := id) (List.getElem_mem i.2)
      omega
    have hnd (c : ℕ) : (convShiftList c B X).Nodup := by
      rw [convShiftList_eq_ofFn]
      refine List.Pairwise.imp (fun {a b} (h : a < b) => h.ne) ?_
      rw [List.pairwise_ofFn]
      intro i j hij
      have hi := hB_gt i
      have hstep : 2 * (i : ℕ) + c + 1 ≤ 2 * (j : ℕ) + c := by have : (i : ℕ) < j := hij; omega
      have hmul := Nat.mul_le_mul_right B hstep
      rw [Nat.add_mul (2 * (i : ℕ) + c) 1, Nat.one_mul] at hmul
      omega
    have hall_pos (c : ℕ) (hc : 1 ≤ c) : ∀ y ∈ convShiftList c B X, 0 < y := by
      intro y hy; rw [convShiftList_eq_ofFn, List.mem_ofFn] at hy
      obtain ⟨i, rfl⟩ := hy
      have : 2 ≤ B := by dsimp only [B]; omega
      nlinarith
    have hlen (c : ℕ) : (convShiftList c B X).length = X.length := by
      rw [convShiftList_eq_ofFn, List.length_ofFn]
    change (convShiftList 1 B X).Nodup ∧ (convShiftList 2 B X).Nodup ∧
        (convShiftList 3 B X).Nodup ∧
        (convShiftList 1 B X).length = (convShiftList 2 B X).length ∧
        (convShiftList 2 B X).length = (convShiftList 3 B X).length ∧
        (∀ x ∈ convShiftList 1 B X, 0 < x) ∧ (∀ y ∈ convShiftList 2 B X, 0 < y) ∧
        (∀ z ∈ convShiftList 3 B X, 0 < z) ∧
        (∃ x ∈ convShiftList 1 B X, ∃ y ∈ convShiftList 2 B X,
          ∃ z ∈ convShiftList 3 B X, x + y = z) ↔
      (∀ x ∈ X, 0 < x) ∧
        ∃ (i j : ℕ) (h : i + j < X.length), X[i]'(by omega) + X[j]'(by omega) = X[i + j]'h
    simp only [hnd 1, hnd 2, hnd 3, hlen, true_and]
    rw [and_iff_right (hall_pos 1 (by omega)), and_iff_right (hall_pos 2 (by omega)),
      and_iff_right (hall_pos 3 (by omega)), and_iff_right hXpos]
    simp only [convShiftList_eq_ofFn, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, _, ⟨m, rfl⟩, heq⟩
      have hi := hB_gt i; have hj := hB_gt j; have hm := hB_gt m
      have hrew : (2 * ((i : ℕ) + j) + 3) * B + (X[i] + X[j]) = (2 * (m : ℕ) + 3) * B + X[m] := by
        linarith
      have hq : 2 * ((i : ℕ) + j) + 3 = 2 * (m : ℕ) + 3 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hlt)
          rw [Nat.add_mul _ 1, Nat.one_mul] at this; omega
        · have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hgt)
          rw [Nat.add_mul _ 1, Nat.one_mul] at this; omega
      have hm_eq : (m : ℕ) = (i : ℕ) + j := by omega
      have hij : (i : ℕ) + j < X.length := hm_eq ▸ m.2
      refine ⟨i, j, hij, ?_⟩
      have hXm : X[(i : ℕ) + j]'hij = X[m] := by simp [← hm_eq]
      change X[i] + X[j] = X[(i : ℕ) + j]'hij
      rw [hXm]; rw [hq] at hrew; linarith
    · rintro ⟨i, j, hij, hsum⟩
      refine ⟨_, ⟨⟨i, by omega⟩, rfl⟩, _, ⟨⟨j, by omega⟩, rfl⟩, _, ⟨⟨i + j, hij⟩, rfl⟩, ?_⟩
      change (2 * i + 1) * B + X[i] + ((2 * j + 2) * B + X[j]) =
        (2 * (i + j) + 3) * B + X[i + j]
      linarith
  · have hf : allPosNatList X = false := Bool.eq_false_iff.mpr hpos
    simp only [hf, Bool.false_eq_true, ↓reduceIte, not_empty_mem_threeSum, false_iff]
    rintro ⟨hXp, _⟩; exact absurd ((allPosNatList_eq_true_iff X).mpr hXp) hpos

/-- Total output length bound for `convToThreeSum`. -/
theorem threeSumSize_convToThreeSum_le (X : List ℕ) :
    threeSumSize (convToThreeSum X) ≤ 3 * X.length := by
  unfold convToThreeSum threeSumSize
  split_ifs
  · simp only [convShiftList_eq_ofFn, List.length_ofFn]; omega
  · simp

/-- Output element bit-length bound for `convToThreeSum`. -/
theorem threeSumBitScale_convToThreeSum_le (X : List ℕ) :
    threeSumBitScale (convToThreeSum X) ≤ X.length.size + convThreeSumBitScale X + 6 := by
  unfold convToThreeSum threeSumBitScale convThreeSumBitScale
  split_ifs
  · let B := 2 * (maxNatList X + 1)
    have hB_lt : B ≤ 2 ^ (listMax Nat.size X + 2) := by
      dsimp only [B]
      have hM : maxNatList X < 2 ^ listMax Nat.size X :=
        (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (maxNatList_size_le X))
      rw [Nat.pow_add]; omega
    have hcs (c : ℕ) (hc : c ≤ 3) :
        listMax Nat.size (convShiftList c B X) ≤ X.length.size + listMax Nat.size X + 6 := by
      refine listMax_le fun y hy => ?_
      rw [convShiftList_eq_ofFn, List.mem_ofFn] at hy
      obtain ⟨i, rfl⟩ := hy
      have hi : 2 * (i : ℕ) + c + 1 ≤ 2 ^ (X.length.size + 3) := by
        have := i.2.trans (Nat.lt_size_self X.length)
        rw [Nat.pow_add]; omega
      have hXi : X[i] < B := by
        dsimp only [B]; rw [maxNatList_eq_listMax]
        have : X[i] ≤ listMax id X := le_listMax (f := id) (List.getElem_mem i.2)
        omega
      refine Nat.size_le.mpr ?_
      calc (2 * (i : ℕ) + c) * B + X[i] < (2 * (i : ℕ) + c + 1) * B := by
            rw [Nat.add_mul (2 * (i : ℕ) + c) 1, Nat.one_mul]; omega
        _ ≤ 2 ^ (X.length.size + 3) * 2 ^ (listMax Nat.size X + 2) := Nat.mul_le_mul hi hB_lt
        _ = 2 ^ (X.length.size + listMax Nat.size X + 5) := by rw [← Nat.pow_add]; congr 1; omega
        _ < 2 ^ (X.length.size + listMax Nat.size X + 6) :=
            Nat.pow_lt_pow_right (by decide) (by omega)
    have h1 := hcs 1 (by omega); have h2 := hcs 2 (by omega); have h3 := hcs 3 (by omega)
    dsimp only [B] at h1 h2 h3 ⊢; omega
  · change max 0 (max 0 0) + 1 ≤ _; omega

private theorem computableInO_convShiftList (c : ℕ) :
    ∃ d, ComputableInO (fun p : ℕ × List ℕ => convShiftList c p.1 p.2)
      (encPair encNat (encList encNat)) (encList encNat)
      (fun p => (p.2.length + 1) * (p.1.size + listMax Nat.size p.2 + p.2.length.size + 6) ^ d)
      (fun p =>
        (p.2.length + 1) * (p.1.size + listMax Nat.size p.2 + p.2.length.size + 6) ^ d) := by
  let encS := encPair encNat encNat
  have hnext : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => (q.1.1, q.1.2 + 1))
      (encPair encS encNat) encS := by fun_prop
  have hemit : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ => [(2 * q.1.2 + c) * q.1.1 + q.2])
      (encPair encS encNat) (encList encNat) := by
    have h1 : ComputableInPolyTime (fun k : ℕ => 2 * k + c) encNat encNat := by fun_prop
    have hk := h1.comp ((ComputableInPolyTime.snd encNat encNat).comp
      (ComputableInPolyTime.fst encS encNat))
    have hB := (ComputableInPolyTime.fst encNat encNat).comp (ComputableInPolyTime.fst encS encNat)
    have hx := ComputableInPolyTime.snd encS encNat
    have hmul : ComputableInPolyTime (fun r : ℕ × ℕ => r.1 * r.2)
        (encPair encNat encNat) encNat := by fun_prop
    have hadd : ComputableInPolyTime (fun r : ℕ × ℕ => [r.1 + r.2])
        (encPair encNat encNat) (encList encNat) := by fun_prop
    exact hadd.comp ((hmul.comp (hk.prod hB)).prod hx)
  have hfold_st (t : List ℕ) (B k : ℕ) :
      t.foldl (fun s (_ : ℕ) => (s.1, s.2 + 1)) (B, k) = (B, k + t.length) := by
    induction t generalizing k with
    | nil => simp
    | cons _ ts ih => rw [List.foldl_cons, ih, List.length_cons]; congr 1; omega
  let lMax : (ℕ × ℕ) × List ℕ → ℕ :=
    fun p => 2 * p.1.1.size + p.1.2.size + listMax Nat.size p.2 + p.2.length.size + 4
  obtain ⟨ds, hstr⟩ := computableInO_streamList (lMax := lMax)
    Prod.fst Prod.snd (fun _ => rfl) hnext hemit (fun _ => rfl)
    (fun p j _ => by
      simp only [streamState, hfold_st, encS, length_encPair, length_encNat]
      have hsz := (Nat.size_le_size (Nat.add_le_add_left (List.length_take_le' j p.2) p.1.2)).trans
        (Nat.size_add_le p.1.2 p.2.length)
      change 2 * p.1.1.size + 1 + (p.1.2 + (p.2.take j).length).size ≤
        2 * p.1.1.size + p.1.2.size + listMax Nat.size p.2 + p.2.length.size + 4
      omega)
    (fun p j hj => by
      rw [length_encNat]; have := le_listMax (f := Nat.size) (List.getElem_mem hj)
      dsimp only [lMax]; omega)
  have h0Pt : ComputableInPolyTime (fun b : ℕ => (b, (0 : ℕ))) encNat encS := by fun_prop
  obtain ⟨di, _, hdi⟩ := h0Pt.exists_degree
  let encIn := encPair encNat (encList encNat)
  have hinit := ((hdi.inO.comp (ComputableInO.fst encNat (encList encNat))).prod
    (ComputableInO.snd encNat (encList encNat))).mono_le
    (T' := fun p => 2 * (encIn p).length + ((encNat p.1).length + 1) ^ di)
    (S' := fun p => 2 * (encIn p).length + ((encNat p.1).length + 1) ^ di)
    (fun _ => by dsimp only [encIn]; omega) (fun _ => by dsimp only [encIn]; omega)
  let D := di + ds + 2
  have h0s : (0 : ℕ).size = 0 := by decide
  refine ⟨D, ((hstr.comp hinit).of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (32 + 2 ^ di + 4 ^ ds) 0 fun p => ?_
    let S := p.1.size + listMax Nat.size p.2 + p.2.length.size + 6
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hSD : S ≤ S ^ D := Nat.le_self_pow (by dsimp only [D]; omega) S
    have hlenL : (encList encNat p.2).length ≤ 3 * ((p.2.length + 1) * S ^ D) := by
      have h1 := (length_encList_le_mul encNat p.2 (b := listMax Nat.size p.2) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _ (by dsimp only [S]; omega : _ ≤ 3 * S))
      nlinarith [Nat.mul_le_mul (Nat.le_succ p.2.length) hSD]
    have hlenIn : (encIn p).length ≤ 6 * ((p.2.length + 1) * S ^ D) := by
      rw [length_encPair, length_encNat]
      nlinarith [(by dsimp only [S]; omega : p.1.size ≤ S).trans hSD]
    have hpair : (encPair encS (encList encNat) ((p.1, 0), p.2)).length ≤
        12 * ((p.2.length + 1) * S ^ D) := by
      simp only [encS, length_encPair, length_encNat, h0s]
      nlinarith [(by dsimp only [S]; omega : p.1.size + 1 ≤ S).trans hSD]
    have hp_di : ((encNat p.1).length + 1) ^ di ≤ 2 ^ di * ((p.2.length + 1) * S ^ D) := by
      rw [length_encNat]
      exact (Nat.pow_le_pow_left (by dsimp only [S]; omega : _ ≤ 2 * S) di).trans
        ((Nat.mul_pow 2 S di).le.trans (Nat.mul_le_mul_left _
          ((Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega)).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))))
    have hp_ds : (p.2.length + 1) * (lMax ((p.1, 0), p.2) + 1) ^ ds ≤
        4 ^ ds * ((p.2.length + 1) * S ^ D) :=
      (Nat.mul_le_mul_left (p.2.length + 1)
        ((Nat.pow_le_pow_left (by dsimp only [lMax, S]; rw [h0s]; omega : _ ≤ 4 * S) ds).trans
          ((Nat.mul_pow 4 S ds).le.trans (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega)))))).trans_eq
        (Nat.mul_left_comm _ _ _)
    dsimp only [Function.comp_apply, S] at *
    rw [Nat.add_mul (32 + 2 ^ di) (4 ^ ds), Nat.add_mul 32 (2 ^ di)]; omega

/-- `convToThreeSum` is computable in quasi-linear time on a deterministic multi-tape Turing
machine. -/
theorem computableInO_convToThreeSum :
    ∃ d, ComputableInO convToThreeSum encConvThreeSum encThreeSum
      (fun X => (X.length + 1) * (convThreeSumBitScale X + X.length.size + 8) ^ d)
      (fun X => (X.length + 1) * (convThreeSumBitScale X + X.length.size + 8) ^ d) := by
  obtain ⟨da, hall⟩ := computableInO_allPosNatList
  obtain ⟨dm, hmax⟩ := computableInO_maxNatList
  have h2Pt : ComputableInPolyTime (fun m : ℕ => 2 * (m + 1)) encNat encNat := by fun_prop
  obtain ⟨d2, _, hd2⟩ := h2Pt.exists_degree
  obtain ⟨dc1, hc1⟩ := computableInO_convShiftList 1
  obtain ⟨dc2, hc2⟩ := computableInO_convShiftList 2
  obtain ⟨dc3, hc3⟩ := computableInO_convShiftList 3
  let sc (X : List ℕ) := convThreeSumBitScale X + X.length.size + 8
  have hBsz (X : List ℕ) : (2 * (maxNatList X + 1)).size ≤ listMax Nat.size X + 2 := by
    refine Nat.size_le.mpr ?_; rw [Nat.pow_add]
    have := (Nat.lt_size_self (maxNatList X)).trans_le
      (Nat.pow_le_pow_right (by decide) (maxNatList_size_le X))
    omega
  let dB := dm + d2 + 2
  have hBX : ComputableInO (fun X : List ℕ => (2 * (maxNatList X + 1), X))
      (encList encNat) (encPair encNat (encList encNat))
      (fun X => (X.length + 1) * sc X ^ dB) (fun X => (X.length + 1) * sc X ^ dB) := by
    have hB := hd2.inO.comp hmax
    refine (hB.prod (ComputableInO.of_eq fun _ => rfl)).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (8 + 2 ^ d2) 0 fun X => ?_
      have hS1 : 1 ≤ sc X := by dsimp only [sc]; omega
      have hSD : sc X ≤ sc X ^ dB := Nat.le_self_pow (by dsimp only [dB]; omega) _
      have h1 : (X.length + 1) * (listMax Nat.size X + 4) ^ dm ≤ (X.length + 1) * sc X ^ dB :=
        Nat.mul_le_mul_left (X.length + 1) ((Nat.pow_le_pow_left
          (by have := listMax_size_lt_convThreeSumBitScale X; dsimp only [sc]; omega) dm).trans
          (Nat.pow_le_pow_right hS1 (by dsimp only [dB]; omega)))
      have hmsz : (encNat (maxNatList X)).length + 1 ≤ 2 * sc X := by
        rw [length_encNat]
        have := (Nat.size_le_size (by omega : maxNatList X ≤ 2 * (maxNatList X + 1))).trans
          (hBsz X)
        have := listMax_size_lt_convThreeSumBitScale X; dsimp only [sc]; omega
      have h2 : ((encNat (maxNatList X)).length + 1) ^ d2 ≤
          2 ^ d2 * ((X.length + 1) * sc X ^ dB) :=
        (Nat.pow_le_pow_left hmsz d2).trans ((Nat.mul_pow 2 _ d2).le.trans
          (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right hS1 (by dsimp only [dB]; omega)).trans
            (Nat.le_mul_of_pos_left _ (show 0 < X.length + 1 by omega)))))
      have hlen : (encList encNat X).length ≤ 3 * ((X.length + 1) * sc X ^ dB) := by
        have hl := (length_encList_le_mul encNat X (b := listMax Nat.size X) fun x hx => by
          rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
          (Nat.mul_le_mul_left _
            (by have := listMax_size_lt_convThreeSumBitScale X; dsimp only [sc]; omega : _ ≤
              3 * sc X))
        nlinarith [Nat.mul_le_mul (Nat.le_succ X.length) hSD]
      rw [Nat.add_mul 8 (2 ^ d2)]; omega
  have mkShift {dc : ℕ} {c : ℕ}
      (hc : ComputableInO (fun p : ℕ × List ℕ => convShiftList c p.1 p.2)
        (encPair encNat (encList encNat)) (encList encNat)
        (fun p => (p.2.length + 1) * (p.1.size + listMax Nat.size p.2 + p.2.length.size + 6) ^ dc)
        (fun p => (p.2.length + 1) *
          (p.1.size + listMax Nat.size p.2 + p.2.length.size + 6) ^ dc)) :
      ComputableInO (fun X : List ℕ => convShiftList c (2 * (maxNatList X + 1)) X)
        (encList encNat) (encList encNat)
        (fun X => (X.length + 1) * sc X ^ (dB + dc + 1))
        (fun X => (X.length + 1) * sc X ^ (dB + dc + 1)) := by
    refine (hc.comp hBX).weaken ?_ ?_
    all_goals
      refine BigOLe.add (BigOLe.of_le fun X => Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by dsimp only [sc]; omega) (by omega)))
        (BigOLe.of_le_linear (2 ^ dc) 0 fun X => ?_)
      have hb : (2 * (maxNatList X + 1)).size + listMax Nat.size X + X.length.size + 6 ≤
          2 * sc X := by have := hBsz X; have :=
            listMax_size_lt_convThreeSumBitScale X; dsimp only [sc]; omega
      have hp := (Nat.pow_le_pow_left hb dc).trans ((Nat.mul_pow 2 _ dc).le.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by dsimp only [sc]; omega)
          (by omega : dc ≤ dB + dc + 1))))
      exact ((Nat.mul_le_mul_left (X.length + 1) hp).trans_eq (Nat.mul_left_comm _ _ _)).trans_eq
        (add_zero _).symm
  let D := da + dB + dc1 + dc2 + dc3 + 2
  have htriple := (mkShift hc1).prod ((mkShift hc2).prod (mkShift hc3))
  have hemp : ComputableInO (fun _ : List ℕ => (([], ([], [])) : ThreeSumInput))
      (encList encNat) encThreeSum (fun X => (encList encNat X).length) (fun _ => 0) :=
    ComputableInO.constZero ([], ([], []))
  refine ⟨D, ((hall.ite htriple hemp).of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear 16 0 fun X => ?_
    have hS1 : 1 ≤ sc X := by dsimp only [sc]; omega
    have hSD : sc X ≤ sc X ^ D := Nat.le_self_pow (by dsimp only [D]; omega) _
    have ha : (X.length + 1) * (listMax Nat.size X + 4) ^ da ≤ (X.length + 1) * sc X ^ D :=
      Nat.mul_le_mul_left (X.length + 1) ((Nat.pow_le_pow_left
        (by have := listMax_size_lt_convThreeSumBitScale X; dsimp only [sc]; omega) da).trans
        (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega)))
    have h1 := Nat.mul_le_mul_left (X.length + 1)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : dB + dc1 + 1 ≤ D))
    have h2 := Nat.mul_le_mul_left (X.length + 1)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : dB + dc2 + 1 ≤ D))
    have h3 := Nat.mul_le_mul_left (X.length + 1)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : dB + dc3 + 1 ≤ D))
    have hlen : (encList encNat X).length ≤ 3 * ((X.length + 1) * sc X ^ D) := by
      have hl := (length_encList_le_mul encNat X (b := listMax Nat.size X) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _ (by have :=
          listMax_size_lt_convThreeSumBitScale X; dsimp only [sc]; omega : _ ≤ 3 * sc X))
      nlinarith [Nat.mul_le_mul (Nat.le_succ X.length) hSD]
    change _ ≤ 16 * ((X.length + 1) * sc X ^ D) + 0
    split_ifs <;> omega

/-- **Convolution-3SUM reduces to 3SUM**: `ConvThreeSumHypothesis → ThreeSumHypothesis`. -/
theorem threeSumHypothesis_of_convThreeSumHypothesis (h : ConvThreeSumHypothesis) :
    ThreeSumHypothesis := by
  intro ε hε e hdec
  obtain ⟨g, tg, cg, hg, hg_iff, htg⟩ := hdec.exists_computableInO
  obtain ⟨dr, hr⟩ := computableInO_convToThreeSum
  let ε' : ℝ := min (ε / 2) (1 / 2)
  have hε' : 0 < ε' := by positivity
  obtain ⟨Clog, hClog1, hClog⟩ := exists_nat_size_pow_le_rpow (max dr e) (δ := ε') hε'
  refine h ε' hε' (max dr e) ?_
  have hcomp := hg.comp hr
  refine (DecidableInTimeO.of_computableInO hcomp
    (fun X => (convToThreeSum_mem_iff X).symm.trans (hg_iff _))
    (fun _ => le_rfl)).mono ((cg + 1) * Clog * 16 ^ (max dr e + 2)) (fun X => ?_)
    (fun X => by positivity)
  rcases Nat.eq_zero_or_pos X.length with hn0 | hn
  · have hnil : X = [] := List.length_eq_zero_iff.mp hn0
    subst hnil
    have hct : convToThreeSum [] = ([], ([], [])) := rfl
    have ht0 := htg ([], ([], []))
    have h0pow : ((threeSumSize ([], ([], [])) : ℕ) : ℝ) ^ (2 - ε) ≤ 1 := by
      rw [threeSumSize_empty, Nat.cast_zero]
      by_cases hz : 2 - ε = 0
      · simp [hz]
      · rw [Real.zero_rpow hz]; norm_num
    have hsz0 : (0 : ℕ).size = 0 := by decide
    simp only [List.length_nil, hct, threeSumBitScale_empty, convThreeSumBitScale_nil, hsz0,
      Nat.cast_one, one_pow, mul_one, Nat.cast_add, Nat.cast_mul, zero_add] at ht0 ⊢
    have ht0' : (tg ([], ([], [])) : ℝ) ≤ 2 * (cg : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left h0pow (Nat.cast_nonneg cg)]
    have h9 : (9 : ℝ) ^ dr ≤ (16 : ℝ) ^ (max dr e + 2) :=
      (pow_le_pow_left₀ (by positivity) (by norm_num) dr).trans
        (pow_le_pow_right₀ (by norm_num) (le_trans (le_max_left dr e) (by omega)))
    have hc1 : (1 : ℝ) ≤ Clog := by exact_mod_cast hClog1
    have hnn : (0 : ℝ) ≤
        (((cg + 1) * Clog * 16 ^ (max dr e + 2) : ℕ) : ℝ) * (0 : ℝ) ^ (2 - ε') := by positivity
    have h16 : (16 : ℝ) ≤ 16 ^ (max dr e + 2) :=
      (pow_one (16 : ℝ)).symm.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
    have h9' : (9 : ℝ) ^ dr + 2 * (cg : ℝ) ≤ ((cg + 1) * Clog * 16 ^ (max dr e + 2) : ℕ) := by
      push_cast
      have h1 : (9 : ℝ) ^ dr ≤ (16 : ℝ) ^ (max dr e + 2) := h9
      have h2 : (16 : ℝ) ≤ (Clog : ℝ) * 16 ^ (max dr e + 2) := by
        simpa only [one_mul] using
          mul_le_mul hc1 h16 (by norm_num : (0 : ℝ) ≤ 16) (Nat.cast_nonneg Clog)
      have h3 : (9 : ℝ) ^ dr ≤ (Clog : ℝ) * 16 ^ (max dr e + 2) := by
        simpa only [one_mul] using
          mul_le_mul hc1 h1 (by positivity : (0 : ℝ) ≤ (9 : ℝ) ^ dr) (Nat.cast_nonneg Clog)
      have h4 : (cg : ℝ) * 16 ≤ (cg : ℝ) * ((Clog : ℝ) * 16 ^ (max dr e + 2)) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg cg)
      have hcg_nn : (0 : ℝ) ≤ cg := Nat.cast_nonneg cg
      linarith
    push_cast at h9' hnn ⊢
    norm_num
    linarith
  · let n := X.length
    let b := convThreeSumBitScale X
    let K := max dr e
    have hb1 : 1 ≤ b := by dsimp only [b, convThreeSumBitScale]; omega
    have hlog := hClog n hn
    have hsc_le : b + n.size + 8 ≤ 9 * (n.size + 1) * b := by nlinarith
    have hred : (((n + 1) * (b + n.size + 8) ^ dr : ℕ) : ℝ) ≤
        2 * 9 ^ K * (Clog : ℝ) * ((n : ℝ) ^ (2 - ε') * (b : ℝ) ^ K) := by
      have hp : (b + n.size + 8) ^ dr ≤ (9 * (n.size + 1) * b) ^ K :=
        (Nat.pow_le_pow_left hsc_le dr).trans
          (Nat.pow_le_pow_right (by positivity) (le_max_left dr e))
      have hpR : ((b + n.size + 8 : ℕ) : ℝ) ^ dr ≤
          9 ^ K * ((n.size + 1 : ℕ) : ℝ) ^ K * (b : ℝ) ^ K := by
        have h0 : (((b + n.size + 8) ^ dr : ℕ) : ℝ) ≤
            ((9 ^ K * (n.size + 1) ^ K * b ^ K : ℕ) : ℝ) := by
          exact_mod_cast hp.trans_eq (by simp only [Nat.mul_pow])
        push_cast at h0 ⊢; exact h0
      have hn2 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)
      have hnr : (n : ℝ) * (n : ℝ) ^ ε' ≤ (n : ℝ) ^ (2 - ε') := by
        rw [← Real.rpow_one_add' (by positivity) (by linarith : 1 + ε' ≠ 0)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
          (by have : ε' ≤ 1 / 2 := min_le_right _ _; linarith)
      calc (((n + 1) * (b + n.size + 8) ^ dr : ℕ) : ℝ)
          = ((n + 1 : ℕ) : ℝ) * ((b + n.size + 8 : ℕ) : ℝ) ^ dr := by push_cast; ring
        _ ≤ (2 * (n : ℝ)) * (9 ^ K * ((Clog : ℝ) * (n : ℝ) ^ ε') * (b : ℝ) ^ K) :=
            mul_le_mul hn2 (hpR.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)))
              (by positivity) (by positivity)
        _ = 2 * 9 ^ K * (Clog : ℝ) * ((n : ℝ) * (n : ℝ) ^ ε') * (b : ℝ) ^ K := by ring
        _ ≤ 2 * 9 ^ K * (Clog : ℝ) * ((n : ℝ) ^ (2 - ε') * (b : ℝ) ^ K) := by
            nlinarith [mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnr (by positivity : (0 : ℝ) ≤ 2 * 9 ^ K * Clog))
              (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ K)]
    have hts_pow : (threeSumSize (convToThreeSum X) : ℝ) ^ (2 - ε) ≤
        9 * (n : ℝ) ^ (2 - 2 * ε') := by
      have hsz_le : (threeSumSize (convToThreeSum X) : ℝ) ≤ 3 * (n : ℝ) := by
        exact_mod_cast threeSumSize_convToThreeSum_le X
      by_cases h2e : 0 ≤ 2 - ε
      · calc (threeSumSize (convToThreeSum X) : ℝ) ^ (2 - ε)
            ≤ (3 * (n : ℝ)) ^ (2 - ε) := Real.rpow_le_rpow (by positivity) hsz_le h2e
          _ = (3 : ℝ) ^ (2 - ε) * (n : ℝ) ^ (2 - ε) :=
              Real.mul_rpow (by norm_num) (by positivity)
          _ ≤ 9 * (n : ℝ) ^ (2 - 2 * ε') := by
              refine mul_le_mul ?_ ?_ (by positivity) (by norm_num)
              · calc (3 : ℝ) ^ (2 - ε) ≤ (3 : ℝ) ^ (2 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                  _ = 9 := by norm_num
              · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
                  (by have : ε' ≤ ε / 2 := min_le_left _ _; linarith)
      · rcases Nat.eq_zero_or_pos (threeSumSize (convToThreeSum X)) with hz | hsp
        · rw [hz, Nat.cast_zero, Real.zero_rpow (by linarith)]; positivity
        · calc (threeSumSize (convToThreeSum X) : ℝ) ^ (2 - ε) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hsp) (by linarith)
            _ ≤ 9 * (n : ℝ) ^ (2 - 2 * ε') := by
                have : (1 : ℝ) ≤ (n : ℝ) ^ (2 - 2 * ε') := Real.one_le_rpow (by exact_mod_cast hn)
                  (by have : ε' ≤ 1 / 2 := min_le_right _ _; linarith)
                linarith
    have hbs_pow : (threeSumBitScale (convToThreeSum X) : ℝ) ^ e ≤
        9 ^ K * (Clog : ℝ) * (n : ℝ) ^ ε' * (b : ℝ) ^ K := by
      have h1 : threeSumBitScale (convToThreeSum X) ≤ 9 * (n.size + 1) * b :=
        (threeSumBitScale_convToThreeSum_le X).trans (by dsimp only [n, b]; nlinarith)
      have hp : threeSumBitScale (convToThreeSum X) ^ e ≤ (9 * (n.size + 1) * b) ^ K :=
        (Nat.pow_le_pow_left h1 e).trans
          (Nat.pow_le_pow_right (by positivity) (le_max_right dr e))
      have hpR : (threeSumBitScale (convToThreeSum X) : ℝ) ^ e ≤
          9 ^ K * ((n.size + 1 : ℕ) : ℝ) ^ K * (b : ℝ) ^ K := by
        have h0 : ((threeSumBitScale (convToThreeSum X) ^ e : ℕ) : ℝ) ≤
            ((9 ^ K * (n.size + 1) ^ K * b ^ K : ℕ) : ℝ) := by
          exact_mod_cast hp.trans_eq (by simp only [Nat.mul_pow])
        push_cast at h0 ⊢; exact h0
      calc (threeSumBitScale (convToThreeSum X) : ℝ) ^ e
          ≤ 9 ^ K * ((n.size + 1 : ℕ) : ℝ) ^ K * (b : ℝ) ^ K := hpR
        _ ≤ 9 ^ K * ((Clog : ℝ) * (n : ℝ) ^ ε') * (b : ℝ) ^ K :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity))
              (by positivity)
        _ = 9 ^ K * (Clog : ℝ) * (n : ℝ) ^ ε' * (b : ℝ) ^ K := by ring
    have htg_le : (tg (convToThreeSum X) : ℝ) ≤
        (cg : ℝ) * (9 * 9 ^ K * (Clog : ℝ)) * ((n : ℝ) ^ (2 - ε') * (b : ℝ) ^ K) + cg := by
      have h0 := htg (convToThreeSum X)
      have hmul := mul_le_mul hts_pow hbs_pow (by positivity) (by positivity)
      have hnr : (n : ℝ) ^ (2 - 2 * ε') * (n : ℝ) ^ ε' = (n : ℝ) ^ (2 - ε') := by
        rw [← Real.rpow_add (by exact_mod_cast hn)]; congr 1; ring
      have hprod : (threeSumSize (convToThreeSum X) : ℝ) ^ (2 - ε) *
          (threeSumBitScale (convToThreeSum X) : ℝ) ^ e ≤
          9 * 9 ^ K * (Clog : ℝ) * ((n : ℝ) ^ (2 - ε') * (b : ℝ) ^ K) := by
        calc _ ≤ (9 * (n : ℝ) ^ (2 - 2 * ε')) *
              (9 ^ K * (Clog : ℝ) * (n : ℝ) ^ ε' * (b : ℝ) ^ K) := hmul
          _ = 9 * 9 ^ K * (Clog : ℝ) * ((n : ℝ) ^ (2 - 2 * ε') * (n : ℝ) ^ ε') * (b : ℝ) ^ K := by
              ring
          _ = 9 * 9 ^ K * (Clog : ℝ) * ((n : ℝ) ^ (2 - ε') * (b : ℝ) ^ K) := by rw [hnr]; ring
      nlinarith [mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg cg)]
    have hcoeff : 2 * 9 ^ K + (cg : ℝ) * (9 * 9 ^ K) ≤ (cg + 1 : ℝ) * 16 ^ (K + 2) := by
      have h9 : (9 : ℝ) ^ K ≤ (16 : ℝ) ^ K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
      have h16 : (16 : ℝ) ^ (K + 2) = 256 * (16 : ℝ) ^ K := by rw [pow_add]; ring
      rw [h16]; nlinarith [Nat.cast_nonneg (α := ℝ) cg, (by positivity : (0 : ℝ) ≤ 9 ^ K)]
    have hcg_le : (cg : ℝ) ≤ ((cg + 1) * Clog * 16 ^ (K + 2) : ℕ) := by
      push_cast
      have hc1 : (1 : ℝ) ≤ Clog := by exact_mod_cast hClog1
      have h16 : (1 : ℝ) ≤ 16 ^ (K + 2) := one_le_pow₀ (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) cg, mul_le_mul hc1 h16 zero_le_one (by positivity)]
    have hmain := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg Clog))
      (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (2 - ε') * (b : ℝ) ^ K)
    change (((n + 1) * (b + n.size + 8) ^ dr + tg (convToThreeSum X) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add]; push_cast at hred hcg_le ⊢
    dsimp only [n, b, K] at *; linarith

end CslibFrontier.Complexity
