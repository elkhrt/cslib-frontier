/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Derandomization

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.Nat.Choose.Basic

/-!
# Explicit Polynomial-Time Weak Designs

This module constructs deterministic polynomial-time combinatorial weak designs following
Pooya Hatami and William M. Hoza, *Paradigms for Unconditional Pseudorandom Generators*,
, under standard Lean axioms.

Given parameters $n, \ell, t$ with $1 \le t \le \ell$ and $n \le 2^t$, we partition the universe
into $\ell$ buckets of size $q = 5 \lceil \ell / t \rceil$ ($R = \ell q \le 10 \ell^2 / t$) and
select $n$ blocks of size $\ell$ (one coordinate per bucket) via the method of conditional
expectations using exact integer dynamic programming (`dpTail`), achieving pairwise intersections
strictly less than $t$ and certifying `Turing.MultiTapeTM.ComputableInPolyTime`.

## Main definitions

* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.dpTail`: exact integer collision-tail
  dynamic program.
* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.hatamiHozaBucketSize`: bucket size
  $q = \max(1, 5 \lceil \ell / t \rceil)$.
* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.hatamiHozaMasks`: explicit list of $n$
  Boolean masks of length $R = \ell q$.
* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.hatamiHozaDesign`: canonical
  `Cslib.Crypto.PRG.NisanWigderson.Design` wrapper.

## Main results

* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.hatamiHozaUniverse_le`:
  $R = \ell q \le 10 \ell^2 / t$ for $1 \le t \le \ell$.
* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.pairwise_overlapCount_hatamiHozaMasks`:
  pairwise overlaps are at most $t - 1$.
* `CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.hatamiHozaMasks_polyTime`: multi-tape
  Turing machine polynomial-time certificate for `hatamiHozaMasks`.
-/

public section

namespace CslibFrontier.Crypto.Primitives.PRG.NisanWigderson

open Cslib Cslib.BitString Cslib.Crypto.PRG.NisanWigderson Finset
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped BigOperators

/-! ### Exact Integer Dynamic Program for Bucket Collisions -/

/-- Exact integer count of bucket-choice sequences in $\{0, \dots, q - 1\}^m$ that collide at least
$r$ times with a fixed target tuple. -/
def dpTail (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => q * dpTail q m 0
  | m + 1, r + 1 => dpTail q m r + (q - 1) * dpTail q m (r + 1)

theorem dpTail_zero_zero (q : ℕ) : dpTail q 0 0 = 1 := by
  rfl

@[simp]
theorem dpTail_zero_succ (q r : ℕ) : dpTail q 0 (r + 1) = 0 := by
  rfl

@[simp]
theorem dpTail_zero_right (q m : ℕ) : dpTail q m 0 = q ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change q * dpTail q m 0 = q ^ (m + 1)
    rw [ih, pow_succ']

private lemma list_sum_map_range (q : ℕ) (g : ℕ → ℕ) :
    ((List.range q).map g).sum = ∑ c ∈ range q, g c := by
  induction q with
  | zero => simp
  | succ q ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
    Finset.sum_range_succ]; simp

private lemma sum_range_dpTail_eq {q : ℕ} (m rem : ℕ) {v₀ : ℕ} (hv₀ : v₀ < q) :
    ((List.range q).map fun c ↦ dpTail q m (if c == v₀ then rem - 1 else rem)).sum =
      dpTail q (m + 1) rem := by
  rw [list_sum_map_range]
  have hcongr0 :
      (∑ c ∈ range q, dpTail q m (if c == v₀ then rem - 1 else rem)) =
        ∑ c ∈ range q, dpTail q m (if c = v₀ then rem - 1 else rem) := by
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases h : c = v₀ <;> simp [h]
  rw [hcongr0]
  cases rem with
  | zero =>
    simp only [Nat.zero_sub, ite_self, sum_const, card_range, smul_eq_mul]
    rfl
  | succ r =>
    have hmem : v₀ ∈ range q := mem_range.mpr hv₀
    rw [← Finset.add_sum_erase (range q) _ hmem]
    simp only [↓reduceIte, Nat.add_sub_cancel]
    have herase :
        ∑ c ∈ (range q).erase v₀, dpTail q m (if c = v₀ then r else r + 1) =
          (q - 1) * dpTail q m (r + 1) := by
      have hcongr :
          ∑ c ∈ (range q).erase v₀, dpTail q m (if c = v₀ then r else r + 1) =
            ∑ _c ∈ (range q).erase v₀, dpTail q m (r + 1) := by
        refine Finset.sum_congr rfl fun c hc ↦ ?_
        have hne : c ≠ v₀ := (mem_erase.mp hc).1
        simp [hne]
      rw [hcongr, sum_const, card_erase_of_mem hmem, card_range, smul_eq_mul]
    rw [herase]
    rfl

private lemma dpTail_mul_six_pow_le {q : ℕ} (hq : 1 ≤ q) :
    ∀ m r : ℕ, dpTail q m r * 6 ^ r ≤ (q + 5) ^ m
  | 0, 0 => by simp
  | 0, r + 1 => by simp
  | m + 1, 0 => by
    simp only [dpTail, pow_zero, mul_one, pow_succ']
    have ih := dpTail_mul_six_pow_le hq m 0
    simp only [pow_zero, mul_one] at ih
    exact Nat.mul_le_mul (by omega) ih
  | m + 1, r + 1 => by
    change (dpTail q m r + (q - 1) * dpTail q m (r + 1)) * 6 ^ (r + 1) ≤ (q + 5) ^ (m + 1)
    have ih₀ := dpTail_mul_six_pow_le hq m r
    have ih₁ := dpTail_mul_six_pow_le hq m (r + 1)
    calc (dpTail q m r + (q - 1) * dpTail q m (r + 1)) * 6 ^ (r + 1)
        = 6 * (dpTail q m r * 6 ^ r) + (q - 1) * (dpTail q m (r + 1) * 6 ^ (r + 1)) := by
          rw [pow_succ']
          ring
      _ ≤ 6 * (q + 5) ^ m + (q - 1) * (q + 5) ^ m :=
          Nat.add_le_add (Nat.mul_le_mul_left 6 ih₀) (Nat.mul_le_mul_left (q - 1) ih₁)
      _ = (q + 5) ^ (m + 1) := by
          rw [← add_mul, show 6 + (q - 1) = q + 5 by omega, pow_succ']

private lemma descFactorial_le_pow (a : ℕ) : ∀ k : ℕ, a.descFactorial k ≤ a ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le a k) (descFactorial_le_pow a k)

private lemma two_pow_pred_le_factorial : ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ k.factorial
  | 0, hk => by omega
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := two_pow_pred_le_factorial (k + 1) (by omega)
    change 2 ^ k ≤ (k + 1).factorial at ih
    change 2 ^ (k + 1) ≤ (k + 2).factorial
    rw [pow_succ', Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

private lemma sum_two_pow_range (n : ℕ) : (∑ i ∈ range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ']
    omega

private lemma add_one_pow_le_three_mul_pow {a : ℕ} (ha : 1 ≤ a) :
    (a + 1) ^ a ≤ 3 * a ^ a := by
  have h2pos : 0 < 2 ^ (a - 1) := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ h2pos
  rw [add_comm a 1, add_pow, Finset.mul_sum]
  have hsplit : range (a + 1) = insert 0 (Ico 1 (a + 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
  have htail :
      ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - 1) * (1 ^ k * a ^ (a - k) * (a.choose k : ℕ)) ≤
        ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - k) * a ^ a := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    rw [mem_Ico] at hk
    have hk1 : 1 ≤ k := hk.1
    have hka : k ≤ a := by omega
    have hpow_split : 2 ^ (a - 1) = 2 ^ (a - k) * 2 ^ (k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hchoose_fact : k.factorial * a.choose k ≤ a ^ k := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact descFactorial_le_pow a k
    have h2fact : 2 ^ (k - 1) ≤ k.factorial := two_pow_pred_le_factorial k hk1
    calc 2 ^ (a - 1) * (1 ^ k * a ^ (a - k) * a.choose k)
        = 2 ^ (a - k) * ((2 ^ (k - 1) * a.choose k) * a ^ (a - k)) := by
          rw [one_pow, one_mul, hpow_split]
          ring
      _ ≤ 2 ^ (a - k) * ((k.factorial * a.choose k) * a ^ (a - k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2fact))
      _ ≤ 2 ^ (a - k) * (a ^ k * a ^ (a - k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hchoose_fact)
      _ = 2 ^ (a - k) * a ^ a := by
          rw [← pow_add, Nat.add_sub_of_le hka]
  have hgeom : ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - k) ≤ 2 * 2 ^ (a - 1) := by
    have hbij : ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - k) = ∑ j ∈ range a, 2 ^ j := by
      refine Finset.sum_bij (fun k _ ↦ a - k) ?_ ?_ ?_ ?_
      · intro k hk; rw [mem_Ico] at hk; rw [mem_range]; omega
      · intro k₁ hk₁ k₂ hk₂ heq; rw [mem_Ico] at hk₁ hk₂; omega
      · intro j hj; rw [mem_range] at hj; exact ⟨a - j, by rw [mem_Ico]; omega, by omega⟩
      · intros; rfl
    rw [hbij]
    have hsum := sum_two_pow_range a
    have ha_pow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      cases a with
      | zero => omega
      | succ m => simp [pow_succ']
    omega
  calc 2 ^ (a - 1) * a ^ a +
        ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - 1) * (1 ^ k * a ^ (a - k) * a.choose k)
      ≤ 2 ^ (a - 1) * a ^ a + ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - k) * a ^ a :=
        Nat.add_le_add_left htail _
    _ = (2 ^ (a - 1) + ∑ k ∈ Ico 1 (a + 1), 2 ^ (a - k)) * a ^ a := by
        rw [← Finset.sum_mul, ← add_mul]
    _ ≤ (2 ^ (a - 1) + 2 * 2 ^ (a - 1)) * a ^ a :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left hgeom _)
    _ = 2 ^ (a - 1) * (3 * a ^ a) := by ring

/-- Bucket size $q = \max(1, 5 \lceil \ell / t \rceil)$ for the Hatami–Hoza weak design. -/
@[expose]
def hatamiHozaBucketSize (ℓ t : ℕ) : ℕ :=
  max 1 (5 * ((ℓ + t - 1) / t))

theorem one_le_hatamiHozaBucketSize (ℓ t : ℕ) : 1 ≤ hatamiHozaBucketSize ℓ t :=
  Nat.le_max_left 1 _

private lemma hatamiHozaBucketSize_eq_of_le {ℓ t : ℕ} (ht : 1 ≤ t) (htℓ : t ≤ ℓ) :
    hatamiHozaBucketSize ℓ t = 5 * ((ℓ + t - 1) / t) := by
  unfold hatamiHozaBucketSize
  have hdiv : 1 ≤ (ℓ + t - 1) / t := (Nat.le_div_iff_mul_le ht).mpr (by omega)
  exact max_eq_right (by omega)

/-- Universe size $R = \ell q \le 10 \ell^2 / t$ for $1 \le t \le \ell$. -/
theorem hatamiHozaUniverse_le {ℓ t : ℕ} (ht : 1 ≤ t) (htℓ : t ≤ ℓ) :
    ℓ * hatamiHozaBucketSize ℓ t ≤ 10 * ℓ ^ 2 / t := by
  rw [hatamiHozaBucketSize_eq_of_le ht htℓ, Nat.le_div_iff_mul_le ht]
  set a := (ℓ + t - 1) / t
  have hat : a * t ≤ ℓ + t - 1 := Nat.div_mul_le_self (ℓ + t - 1) t
  have hlt : ℓ + t - 1 ≤ 2 * ℓ := by omega
  calc ℓ * (5 * a) * t = 5 * ℓ * (a * t) := by ring
    _ ≤ 5 * ℓ * (2 * ℓ) := Nat.mul_le_mul_left (5 * ℓ) (hat.trans hlt)
    _ = 10 * ℓ ^ 2 := by ring

private lemma dpTail_mul_two_pow_le_pow {ℓ t : ℕ} (ht : 1 ≤ t) (htℓ : t ≤ ℓ) :
    dpTail (hatamiHozaBucketSize ℓ t) ℓ t * 2 ^ t ≤ (hatamiHozaBucketSize ℓ t) ^ ℓ := by
  set a := (ℓ + t - 1) / t
  set q := hatamiHozaBucketSize ℓ t
  have hq_eq : q = 5 * a := hatamiHozaBucketSize_eq_of_le ht htℓ
  have ha1 : 1 ≤ a := (Nat.le_div_iff_mul_le ht).mpr (by omega)
  have hq1 : 1 ≤ q := by omega
  have hℓ_le : ℓ ≤ a * t := by
    have hmod : t * a + (ℓ + t - 1) % t = ℓ + t - 1 := Nat.div_add_mod (ℓ + t - 1) t
    have hrem : (ℓ + t - 1) % t < t := Nat.mod_lt _ ht
    have hmul : t * a = a * t := Nat.mul_comm t a
    have h1ℓ : 1 ≤ ℓ := ht.trans htℓ
    omega
  have hqa : (q + 5) ^ a ≤ 3 * q ^ a := by
    rw [hq_eq, show 5 * a + 5 = 5 * (a + 1) by ring, mul_pow, mul_pow]
    calc 5 ^ a * (a + 1) ^ a
        ≤ 5 ^ a * (3 * a ^ a) := Nat.mul_le_mul_left _ (add_one_pow_le_three_mul_pow ha1)
      _ = 3 * (5 ^ a * a ^ a) := by ring
  have hqat : (q + 5) ^ (a * t) ≤ q ^ (a * t) * 3 ^ t := by
    calc (q + 5) ^ (a * t)
        = ((q + 5) ^ a) ^ t := pow_mul (q + 5) a t
      _ ≤ (3 * q ^ a) ^ t := Nat.pow_le_pow_left hqa t
      _ = q ^ (a * t) * 3 ^ t := by rw [mul_pow, ← pow_mul]; ring
  have hqℓ : (q + 5) ^ ℓ ≤ q ^ ℓ * 3 ^ t := by
    set s := a * t - ℓ
    have hqs : 0 < q ^ s := Nat.pos_of_ne_zero (pow_ne_zero s (by omega))
    refine Nat.le_of_mul_le_mul_right ?_ hqs
    calc (q + 5) ^ ℓ * q ^ s
        ≤ (q + 5) ^ ℓ * (q + 5) ^ s :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) s)
      _ = (q + 5) ^ (a * t) := by rw [← pow_add, Nat.add_sub_of_le hℓ_le]
      _ ≤ q ^ (a * t) * 3 ^ t := hqat
      _ = q ^ ℓ * 3 ^ t * q ^ s := by
          rw [show a * t = ℓ + s by omega, pow_add]
          ring
  have h3t : 0 < 3 ^ t := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ h3t
  calc dpTail q ℓ t * 2 ^ t * 3 ^ t
      = dpTail q ℓ t * 6 ^ t := by rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ (q + 5) ^ ℓ := dpTail_mul_six_pow_le hq1 ℓ t
    _ ≤ q ^ ℓ * 3 ^ t := hqℓ

/-! ### Explicit Construction of Hatami–Hoza Masks -/

private def dpInitRow (t : ℕ) : List ℕ :=
  1 :: List.replicate t 0

private def dpNextRow (q t : ℕ) (row : List ℕ) : List ℕ :=
  (List.range (t + 1)).map fun r ↦
    if r == 0 then q * row.getD 0 0 else row.getD (r - 1) 0 + (q - 1) * row.getD r 0

private def dpPrependStep (q t : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  dpNextRow q t (rows.headD []) :: rows

private def dpRevRows (q ℓ t : ℕ) : List (List ℕ) :=
  (dpPrependStep q t)^[ℓ] [dpInitRow t]

private lemma dpRevRows_succ (q m t : ℕ) :
    dpRevRows q (m + 1) t = dpNextRow q t ((dpRevRows q m t).headD []) :: dpRevRows q m t := by
  rw [dpRevRows, Function.iterate_succ_apply', dpPrependStep]
  rfl

private lemma getD_map_range {n r : ℕ} (f : ℕ → ℕ) (hr : r < n) :
    ((List.range n).map f).getD r 0 = f r := by
  simp [List.getD_eq_getElem?_getD, hr]

private lemma getD_dpRevRows_head (q t : ℕ) :
    ∀ m r : ℕ, r ≤ t → ((dpRevRows q m t).headD []).getD r 0 = dpTail q m r
  | 0, 0, _ => by simp [dpRevRows, dpInitRow]
  | 0, r + 1, hr => by
    have hlt : r < t := by omega
    simp [dpRevRows, dpInitRow, List.getD_eq_getElem?_getD, hlt]
  | m + 1, 0, _ => by
    rw [dpRevRows_succ, List.headD_cons, dpNextRow, getD_map_range _ (by omega)]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [getD_dpRevRows_head q t m 0 (Nat.zero_le t)]
    rfl
  | m + 1, r + 1, hr => by
    rw [dpRevRows_succ, List.headD_cons, dpNextRow, getD_map_range _ (by omega)]
    have hbeq : (r + 1 == 0) = false := by simp
    rw [hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    rw [getD_dpRevRows_head q t m r (by omega), getD_dpRevRows_head q t m (r + 1) hr]
    rfl

private lemma dpRevRows_eq_map_range (q : ℕ) :
    ∀ m t : ℕ, dpRevRows q m t = (List.range (m + 1)).map fun b ↦ (dpRevRows q (m - b) t).headD []
  | 0, t => by simp [dpRevRows]
  | m + 1, t => by
    have hcons : dpRevRows q (m + 1) t =
        (dpRevRows q (m + 1) t).headD [] :: dpRevRows q m t := by
      rw [dpRevRows_succ, List.headD_cons]
    conv_rhs => rw [List.range_succ_eq_map]
    rw [hcons, dpRevRows_eq_map_range q m t, List.map_cons, List.map_map]
    simp only [Nat.sub_zero]
    congr 1
    refine List.map_congr_left fun b _ ↦ ?_
    dsimp only [Function.comp_apply]
    have hidx : m + 1 - (b + 1) = m - b := by omega
    rw [hidx]

private lemma dpRevRows_tail_eq (q ℓ t : ℕ) :
    (dpRevRows q ℓ t).tail =
      (List.range ℓ).map fun b ↦ (dpRevRows q (ℓ - 1 - b) t).headD [] := by
  rw [dpRevRows_eq_map_range q ℓ t, List.range_succ_eq_map, List.map_cons, List.tail_cons,
    List.map_map]
  refine List.map_congr_left fun b _ ↦ ?_
  dsimp only [Function.comp_apply]
  have hidx : ℓ - (b + 1) = ℓ - 1 - b := by omega
  rw [hidx]

private def bucketChoiceScore (row : List ℕ) (active : List (List ℕ × ℕ)) (c : ℕ) : ℕ :=
  (active.map fun vr ↦ row.getD (if c == vr.1.headD 0 then vr.2 - 1 else vr.2) 0).sum

private def bucketChoiceStep (q : ℕ) (st : List ℕ × List (List ℕ × ℕ)) (row : List ℕ) :
    List ℕ × List (List ℕ × ℕ) :=
  let c :=
    ((List.range q).find? fun c ↦ decide (bucketChoiceScore row st.2 c < row.getD 0 0)).getD 0
  (st.1 ++ [c],
    st.2.map fun vr ↦ (vr.1.tail, if c == vr.1.headD 0 then vr.2 - 1 else vr.2))

private def nextChoiceList (q t : ℕ) (tailRows : List (List ℕ)) (kept : List (List ℕ)) : List ℕ :=
  (tailRows.foldl (bucketChoiceStep q) ([], kept.map fun v ↦ (v, t))).1

private def hatamiHozaChoices (n ℓ t : ℕ) : List (List ℕ) :=
  let q := hatamiHozaBucketSize ℓ t
  let tailRows := (dpRevRows q ℓ t).tail
  (fun kept ↦ kept ++ [nextChoiceList q t tailRows kept])^[n] []

private def choicesToMask (q : ℕ) (u : List ℕ) : List Bool :=
  u.flatMap fun c ↦ listSingle q c

/-- Explicit Hatami–Hoza design masks: `n` Boolean masks of length $R = \ell q \le 10 \ell^2 / t$,
each of weight $\ell$, with pairwise overlap at most $t - 1$ whenever $1 \le t \le \ell$ and
$n \le 2^t$. -/
def hatamiHozaMasks (n ℓ t : ℕ) : List (List Bool) :=
  (hatamiHozaChoices n ℓ t).map (choicesToMask (hatamiHozaBucketSize ℓ t))

/-! ### Correctness of `hatamiHozaMasks` -/

private lemma length_dpRevRows (q ℓ t : ℕ) : (dpRevRows q ℓ t).length = ℓ + 1 := by
  rw [dpRevRows_eq_map_range]
  simp

private lemma length_nextChoiceList (q t : ℕ) (tailRows : List (List ℕ)) (kept : List (List ℕ)) :
    (nextChoiceList q t tailRows kept).length = tailRows.length := by
  unfold nextChoiceList
  suffices ∀ (rows : List (List ℕ)) (st : List ℕ × List (List ℕ × ℕ)),
      (rows.foldl (bucketChoiceStep q) st).1.length = st.1.length + rows.length by
    simpa using this tailRows ([], kept.map fun v ↦ (v, t))
  intro rows
  induction rows with
  | nil => simp
  | cons row rest ih =>
    intro st
    rw [List.foldl_cons, ih]
    simp [bucketChoiceStep]
    omega

private lemma mem_lt_of_nextChoiceList {q : ℕ} (hq : 1 ≤ q) (t : ℕ)
    (tailRows : List (List ℕ)) (kept : List (List ℕ)) :
    ∀ c ∈ nextChoiceList q t tailRows kept, c < q := by
  unfold nextChoiceList
  suffices ∀ (rows : List (List ℕ)) (st : List ℕ × List (List ℕ × ℕ)),
      (∀ c ∈ st.1, c < q) → ∀ c ∈ (rows.foldl (bucketChoiceStep q) st).1, c < q by
    exact this tailRows ([], kept.map fun v ↦ (v, t)) (by simp)
  intro rows
  induction rows with
  | nil => intro st hst; exact hst
  | cons row rest ih =>
    intro st hst
    rw [List.foldl_cons]
    refine ih _ fun c hc ↦ ?_
    simp only [bucketChoiceStep, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hst c hc
    · cases hfind : (List.range q).find? fun c ↦
          decide (bucketChoiceScore row st.2 c < row.getD 0 0) with
      | none => exact Nat.pos_of_ne_zero (by omega)
      | some c₀ =>
        simp only [Option.getD_some]
        exact List.mem_range.mp (List.mem_of_find?_eq_some hfind)

private lemma sum_map_swap {α β : Type*} (la : List α) (lb : List β) (f : α → β → ℕ) :
    (la.map fun a ↦ (lb.map fun b ↦ f a b).sum).sum =
      (lb.map fun b ↦ (la.map fun a ↦ f a b).sum).sum := by
  induction la with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    symm
    exact List.sum_eq_zero_iff.mpr fun x hx ↦ by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    clear ih
    induction lb with
    | nil => simp
    | cons b lb' ihl =>
      simp only [List.map_cons, List.sum_cons] at ihl ⊢
      omega

private lemma mul_le_list_sum {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, B ≤ x) :
    l.length * B ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    simp only [List.length_cons, List.sum_cons, Nat.succ_mul]
    have hx := h x List.mem_cons_self
    have hrest := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    omega

private lemma foldl_bucketChoiceStep_collisions {q t : ℕ} (hq : 1 ≤ q) :
    ∀ (m : ℕ) (st : List ℕ × List (List ℕ × ℕ)),
      (∀ vr ∈ st.2, vr.1.length = m ∧ (∀ c ∈ vr.1, c < q) ∧ vr.2 ≤ t) →
      (st.2.map fun vr ↦ dpTail q m vr.2).sum < q ^ m →
      ∃ suffix : List ℕ,
        (((List.range m).map fun b ↦ (dpRevRows q (m - 1 - b) t).headD []).foldl
            (bucketChoiceStep q) st).1 = st.1 ++ suffix ∧
          suffix.length = m ∧
          ∀ vr ∈ st.2, 1 ≤ vr.2 - (List.zipWith (fun a b ↦ a == b) suffix vr.1).count true
  | 0, st, _, hsum => by
    refine ⟨[], by simp, rfl, fun vr hvr ↦ ?_⟩
    simp only [pow_zero, Nat.lt_one_iff, List.sum_eq_zero_iff, List.mem_map] at hsum
    have hzero : dpTail q 0 vr.2 = 0 := hsum _ ⟨vr, hvr, rfl⟩
    cases hrem : vr.2 with
    | zero => rw [hrem, dpTail_zero_zero] at hzero; exact absurd hzero one_ne_zero
    | succ r => simp
  | m + 1, st, hinv, hsum => by
    have hcons :
        ((List.range (m + 1)).map fun b ↦ (dpRevRows q (m + 1 - 1 - b) t).headD []) =
          ((dpRevRows q m t).headD []) ::
            ((List.range m).map fun b ↦ (dpRevRows q (m - 1 - b) t).headD []) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_sub_cancel, Nat.sub_zero]
      congr 1
      refine List.map_congr_left fun b _ ↦ ?_
      dsimp only [Function.comp_apply]
      have hidx : m - (b + 1) = m - 1 - b := by omega
      rw [hidx]
    rw [hcons, List.foldl_cons]
    set row := (dpRevRows q m t).headD []
    have hrow0 : row.getD 0 0 = q ^ m := by
      rw [getD_dpRevRows_head q t m 0 (Nat.zero_le t), dpTail_zero_right]
    have hscore_eq : ∀ c : ℕ,
        bucketChoiceScore row st.2 c =
          (st.2.map fun vr ↦ dpTail q m (if c == vr.1.headD 0 then vr.2 - 1 else vr.2)).sum := by
      intro c
      unfold bucketChoiceScore
      congr 1
      refine List.map_congr_left fun vr hvr ↦ ?_
      have hrem_le : (if c == vr.1.headD 0 then vr.2 - 1 else vr.2) ≤ t := by
        have := (hinv vr hvr).2.2
        split_ifs <;> omega
      exact getD_dpRevRows_head q t m _ hrem_le
    have havg :
        ((List.range q).map fun c ↦ bucketChoiceScore row st.2 c).sum < q * q ^ m := by
      simp_rw [hscore_eq]
      rw [sum_map_swap]
      have hinner :
          (st.2.map fun vr ↦
              ((List.range q).map fun c ↦
                dpTail q m (if c == vr.1.headD 0 then vr.2 - 1 else vr.2)).sum) =
            st.2.map fun vr ↦ dpTail q (m + 1) vr.2 := by
        refine List.map_congr_left fun vr hvr ↦ ?_
        have hlen := (hinv vr hvr).1
        have hlt := (hinv vr hvr).2.1
        cases hv : vr.1 with
        | nil => rw [hv] at hlen; simp at hlen
        | cons v₀ vtail =>
          have hv₀ : v₀ < q := hlt v₀ (hv ▸ List.mem_cons_self)
          rw [List.headD_cons]
          exact sum_range_dpTail_eq m vr.2 hv₀
      rw [hinner, ← pow_succ']
      exact hsum
    have hex_c : ∃ c ∈ List.range q, bucketChoiceScore row st.2 c < row.getD 0 0 := by
      rw [hrow0]
      by_contra hnot
      have hall : ∀ x ∈ (List.range q).map fun c ↦ bucketChoiceScore row st.2 c, q ^ m ≤ x := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact Nat.not_lt.mp fun hlt ↦ hnot ⟨c, hc, hlt⟩
      have hge := mul_le_list_sum hall
      rw [List.length_map, List.length_range] at hge
      omega
    obtain ⟨c_wit, hc_wit_mem, hc_wit_lt⟩ := hex_c
    let pred : ℕ → Bool := fun c ↦ decide (bucketChoiceScore row st.2 c < row.getD 0 0)
    have hfind_some : ∃ c₀, (List.range q).find? pred = some c₀ := by
      cases hfind : (List.range q).find? pred with
      | some c₀ => exact ⟨c₀, rfl⟩
      | none =>
        have hfalse := List.find?_eq_none.mp hfind c_wit hc_wit_mem
        have htrue : pred c_wit = true := decide_eq_true hc_wit_lt
        rw [htrue] at hfalse
        simp at hfalse
    obtain ⟨c₀, hc₀_eq⟩ := hfind_some
    have hc₀_lt_score : bucketChoiceScore row st.2 c₀ < q ^ m := by
      have hdec : pred c₀ = true := List.find?_some (p := pred) hc₀_eq
      have hlt := of_decide_eq_true hdec
      rwa [hrow0] at hlt
    set st₁ := bucketChoiceStep q st row
    have hst₁_fst : st₁.1 = st.1 ++ [c₀] := by
      dsimp only [st₁, bucketChoiceStep]
      rw [hc₀_eq]
      rfl
    have hst₁_snd :
        st₁.2 = st.2.map fun vr ↦ (vr.1.tail, if c₀ == vr.1.headD 0 then vr.2 - 1 else vr.2) := by
      dsimp only [st₁, bucketChoiceStep]
      rw [hc₀_eq]
      rfl
    have hinv₁ : ∀ vr' ∈ st₁.2, vr'.1.length = m ∧ (∀ c ∈ vr'.1, c < q) ∧ vr'.2 ≤ t := by
      intro vr' hvr'
      rw [hst₁_snd, List.mem_map] at hvr'
      obtain ⟨vr, hvr, rfl⟩ := hvr'
      obtain ⟨hlen, hlt, hrem⟩ := hinv vr hvr
      refine ⟨by simp [hlen], fun c hc ↦ hlt c (List.mem_of_mem_tail hc), ?_⟩
      split_ifs <;> omega
    have hsum₁ : (st₁.2.map fun vr' ↦ dpTail q m vr'.2).sum < q ^ m := by
      rw [hst₁_snd, List.map_map, Function.comp_def, ← hscore_eq c₀]
      exact hc₀_lt_score
    obtain ⟨suf, hsuf_eq, hsuf_len, hsuf_rem⟩ :=
      foldl_bucketChoiceStep_collisions hq m st₁ hinv₁ hsum₁
    refine ⟨c₀ :: suf, ?_, by simp [hsuf_len], fun vr hvr ↦ ?_⟩
    · rw [hsuf_eq, hst₁_fst, List.append_assoc, List.singleton_append]
    · have hmem₁ : (vr.1.tail, if c₀ == vr.1.headD 0 then vr.2 - 1 else vr.2) ∈ st₁.2 := by
        rw [hst₁_snd]
        exact List.mem_map.mpr ⟨vr, hvr, rfl⟩
      have h1 := hsuf_rem _ hmem₁
      have hlen := (hinv vr hvr).1
      cases hv : vr.1 with
      | nil => rw [hv] at hlen; simp at hlen
      | cons v₀ vtail =>
        simp only [hv, List.tail_cons, List.headD_cons] at h1
        rw [List.zipWith_cons_cons, List.count_cons]
        by_cases hcb : c₀ = v₀
        · have hbeq : (c₀ == v₀) = true := beq_iff_eq.mpr hcb
          rw [hbeq] at h1 ⊢
          simp only [↓reduceIte, beq_self_eq_true] at h1 ⊢
          omega
        · have hbeq : (c₀ == v₀) = false := beq_false_of_ne hcb
          rw [hbeq] at h1 ⊢
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_beq, Bool.not_true] at h1 ⊢
          omega

private lemma zipWith_beq_count_comm :
    ∀ u v : List ℕ,
      (List.zipWith (fun a b ↦ a == b) u v).count true =
        (List.zipWith (fun a b ↦ a == b) v u).count true
  | [], _ => by simp
  | _, [] => by simp
  | a :: u, b :: v => by
    simp only [List.zipWith_cons_cons, List.count_cons, Bool.beq_comm (a := a) (b := b),
      zipWith_beq_count_comm u v]

private lemma hatamiHozaChoices_spec {n ℓ t : ℕ} (ht : 1 ≤ t) (htℓ : t ≤ ℓ) (hn : n ≤ 2 ^ t) :
    let q := hatamiHozaBucketSize ℓ t
    (hatamiHozaChoices n ℓ t).length = n ∧
      (∀ u ∈ hatamiHozaChoices n ℓ t, u.length = ℓ ∧ ∀ c ∈ u, c < q) ∧
      (hatamiHozaChoices n ℓ t).Pairwise fun u v ↦
        (List.zipWith (fun a b ↦ a == b) u v).count true ≤ t - 1 := by
  set q := hatamiHozaBucketSize ℓ t
  have hq1 : 1 ≤ q := one_le_hatamiHozaBucketSize ℓ t
  have hdp : dpTail q ℓ t * 2 ^ t ≤ q ^ ℓ := dpTail_mul_two_pow_le_pow ht htℓ
  set tailRows := (dpRevRows q ℓ t).tail
  have htail_len : tailRows.length = ℓ := by
    simp [tailRows, length_dpRevRows]
  unfold hatamiHozaChoices
  let stepFn (kept : List (List ℕ)) : List (List ℕ) := kept ++ [nextChoiceList q t tailRows kept]
  suffices ∀ m ≤ n,
      (stepFn^[m] []).length = m ∧
        (∀ u ∈ stepFn^[m] [], u.length = ℓ ∧ ∀ c ∈ u, c < q) ∧
        (stepFn^[m] []).Pairwise fun u v ↦
          (List.zipWith (fun a b ↦ a == b) u v).count true ≤ t - 1 from this n le_rfl
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlen_m, hmem_m, hpair_m⟩ := ih (by omega)
    set kept := stepFn^[m] []
    rw [Function.iterate_succ_apply']
    change (kept ++ [nextChoiceList q t tailRows kept]).length = m + 1 ∧ _
    set u := nextChoiceList q t tailRows kept
    have hu_len : u.length = ℓ := (length_nextChoiceList q t tailRows kept).trans htail_len
    have hu_lt : ∀ c ∈ u, c < q := mem_lt_of_nextChoiceList hq1 t tailRows kept
    refine ⟨by rw [List.length_append, hlen_m]; rfl, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hmem_m w hw
      · rw [List.mem_singleton.mp hw]
        exact ⟨hu_len, hu_lt⟩
    · rw [List.pairwise_append]
      refine ⟨hpair_m, List.pairwise_singleton _ _, fun v hv w hw ↦ ?_⟩
      rw [List.mem_singleton.mp hw]
      have hinit_lt : ((kept.map fun v' : List ℕ ↦ (v', t)).map fun vr ↦ dpTail q ℓ vr.2).sum <
          q ^ ℓ := by
        rw [List.map_map]
        have hconst : (kept.map (fun _ ↦ dpTail q ℓ t)).sum = kept.length * dpTail q ℓ t := by
          simp [List.sum_replicate]
        change (kept.map (fun _ ↦ dpTail q ℓ t)).sum < q ^ ℓ
        rw [hconst, hlen_m]
        have hm_lt : m < 2 ^ t := lt_of_lt_of_le (Nat.lt_succ_self m) hm |>.trans_le hn
        by_cases h0 : dpTail q ℓ t = 0
        · rw [h0, mul_zero]
          exact Nat.pos_of_ne_zero (pow_ne_zero ℓ (by omega))
        · calc m * dpTail q ℓ t
              < 2 ^ t * dpTail q ℓ t := Nat.mul_lt_mul_of_pos_right hm_lt (Nat.pos_of_ne_zero h0)
            _ = dpTail q ℓ t * 2 ^ t := Nat.mul_comm _ _
            _ ≤ q ^ ℓ := hdp
      have hinv₀ : ∀ vr ∈ kept.map (fun v' : List ℕ ↦ (v', t)),
          vr.1.length = ℓ ∧ (∀ c ∈ vr.1, c < q) ∧ vr.2 ≤ t := by
        intro vr hvr
        rw [List.mem_map] at hvr
        obtain ⟨v', hv', rfl⟩ := hvr
        exact ⟨(hmem_m v' hv').1, (hmem_m v' hv').2, le_rfl⟩
      obtain ⟨suf, hsuf_eq, _, hsuf_rem⟩ :=
        foldl_bucketChoiceStep_collisions hq1 ℓ ([], kept.map fun v' ↦ (v', t)) hinv₀ hinit_lt
      have hu_eq : u = suf := by
        have h1 : (tailRows.foldl (bucketChoiceStep q) ([], kept.map fun v' ↦ (v', t))).1 =
            [] ++ suf := by
          simpa only [tailRows, dpRevRows_tail_eq] using hsuf_eq
        simpa only [u, nextChoiceList, List.nil_append] using h1
      have hrem_v := hsuf_rem (v, t) (List.mem_map.mpr ⟨v, hv, rfl⟩)
      dsimp only at hrem_v
      rw [← hu_eq, ← zipWith_beq_count_comm v u] at hrem_v
      change (List.zipWith (fun a b ↦ a == b) v u).count true ≤ t - 1
      omega

private lemma length_listSingle (q c : ℕ) : (listSingle q c).length = q := by
  simp [listSingle]

private lemma length_choicesToMask {q : ℕ} {u : List ℕ} :
    (choicesToMask q u).length = u.length * q := by
  induction u with
  | nil => simp [choicesToMask]
  | cons c rest ih =>
    rw [choicesToMask, List.flatMap_cons, List.length_append, length_listSingle]
    change q + (choicesToMask q rest).length = (rest.length + 1) * q
    rw [ih]
    ring

private lemma count_true_choicesToMask {q : ℕ} {u : List ℕ} (hu : ∀ c ∈ u, c < q) :
    (choicesToMask q u).count true = u.length := by
  induction u with
  | nil => simp [choicesToMask]
  | cons c rest ih =>
    rw [choicesToMask, List.flatMap_cons, List.count_append,
      count_true_listSingle (hu c List.mem_cons_self)]
    change 1 + (choicesToMask q rest).count true = rest.length + 1
    rw [ih fun x hx ↦ hu x (List.mem_cons_of_mem c hx)]
    omega

private lemma overlapCount_listSingle {q c₁ c₂ : ℕ} (hc₁ : c₁ < q) (hc₂ : c₂ < q) :
    overlapCount (listSingle q c₁) (listSingle q c₂) = if c₁ = c₂ then 1 else 0 := by
  have h1 := listSingle_eq_ofFn (⟨c₁, hc₁⟩ : Fin q)
  have h2 := listSingle_eq_ofFn (⟨c₂, hc₂⟩ : Fin q)
  change overlapCount (listSingle q (⟨c₁, hc₁⟩ : Fin q).1)
      (listSingle q (⟨c₂, hc₂⟩ : Fin q).1) = _
  rw [h1, h2, overlapCount_eq_card_inter List.length_ofFn List.length_ofFn]
  have hblock : ∀ idx : Fin q,
      maskBlock q (List.ofFn fun j : Fin q ↦ decide (j = idx)) = {idx} := by
    intro idx
    ext k
    simp [mem_maskBlock, List.getD_eq_getElem?_getD]
  rw [hblock ⟨c₁, hc₁⟩, hblock ⟨c₂, hc₂⟩]
  by_cases h : c₁ = c₂
  · subst h; simp
  · have hne : (⟨c₁, hc₁⟩ : Fin q) ≠ ⟨c₂, hc₂⟩ := fun heq ↦ h (congrArg Fin.val heq)
    simp [h, hne]

private lemma overlapCount_choicesToMask {q : ℕ} :
    ∀ {u v : List ℕ}, u.length = v.length → (∀ c ∈ u, c < q) → (∀ c ∈ v, c < q) →
      overlapCount (choicesToMask q u) (choicesToMask q v) =
        (u.zipWith (fun a b ↦ a == b) v).count true
  | [], [], _, _, _ => by simp [choicesToMask, overlapCount]
  | a :: u, b :: v, hlen, hu, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [choicesToMask, choicesToMask, List.flatMap_cons, List.flatMap_cons, overlapCount,
      List.zipWith_append (by simp [length_listSingle]), List.count_append]
    change overlapCount (listSingle q a) (listSingle q b) +
        overlapCount (choicesToMask q u) (choicesToMask q v) =
      ((a == b) :: u.zipWith (fun x y ↦ x == y) v).count true
    rw [overlapCount_listSingle (hu a List.mem_cons_self) (hv b List.mem_cons_self),
      overlapCount_choicesToMask hlen (fun x hx ↦ hu x (List.mem_cons_of_mem a hx))
        (fun x hx ↦ hv x (List.mem_cons_of_mem b hx)),
      List.count_cons]
    by_cases hab : a = b
    · subst hab; simp [Nat.add_comm]
    · have hbeq : (a == b) = false := beq_false_of_ne hab
      simp [hab, hbeq]

theorem length_hatamiHozaMasks (n ℓ t : ℕ) : (hatamiHozaMasks n ℓ t).length = n := by
  unfold hatamiHozaMasks hatamiHozaChoices
  rw [List.length_map]
  let stepFn (kept : List (List ℕ)) : List (List ℕ) :=
    kept ++ [nextChoiceList (hatamiHozaBucketSize ℓ t) t
      (dpRevRows (hatamiHozaBucketSize ℓ t) ℓ t).tail kept]
  suffices ∀ m, (stepFn^[m] []).length = m from this n
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    change (stepFn^[m] [] ++ [_]).length = m + 1
    rw [List.length_append, ih]
    rfl

theorem length_mem_hatamiHozaMasks {n ℓ t : ℕ} {w : List Bool}
    (hw : w ∈ hatamiHozaMasks n ℓ t) :
    w.length = ℓ * hatamiHozaBucketSize ℓ t := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  rw [length_choicesToMask]
  congr 1
  unfold hatamiHozaChoices at hu
  let stepFn (kept : List (List ℕ)) : List (List ℕ) :=
    kept ++ [nextChoiceList (hatamiHozaBucketSize ℓ t) t
      (dpRevRows (hatamiHozaBucketSize ℓ t) ℓ t).tail kept]
  suffices ∀ m, ∀ u ∈ stepFn^[m] [], u.length = ℓ from this n u hu
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro u' hu'
    rw [Function.iterate_succ_apply'] at hu'
    rcases List.mem_append.mp hu' with hu' | hu'
    · exact ih u' hu'
    · rw [List.mem_singleton.mp hu', length_nextChoiceList]
      simp [length_dpRevRows]

theorem count_true_mem_hatamiHozaMasks {n ℓ t : ℕ} {w : List Bool}
    (hw : w ∈ hatamiHozaMasks n ℓ t) :
    w.count true = ℓ := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  set q := hatamiHozaBucketSize ℓ t
  have hq1 : 1 ≤ q := one_le_hatamiHozaBucketSize ℓ t
  let stepFn (kept : List (List ℕ)) : List (List ℕ) :=
    kept ++ [nextChoiceList q t (dpRevRows q ℓ t).tail kept]
  suffices ∀ m, ∀ u ∈ stepFn^[m] [], u.length = ℓ ∧ ∀ c ∈ u, c < q by
    obtain ⟨hlen, hlt⟩ := this n u hu
    rw [count_true_choicesToMask hlt, hlen]
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro u' hu'
    rw [Function.iterate_succ_apply'] at hu'
    rcases List.mem_append.mp hu' with hu' | hu'
    · exact ih u' hu'
    · rw [List.mem_singleton.mp hu']
      refine ⟨(length_nextChoiceList q t _ _).trans ?_, mem_lt_of_nextChoiceList hq1 t _ _⟩
      simp [length_dpRevRows]

theorem pairwise_overlapCount_hatamiHozaMasks {n ℓ t : ℕ}
    (ht : 1 ≤ t) (htℓ : t ≤ ℓ) (hn : n ≤ 2 ^ t) :
    (hatamiHozaMasks n ℓ t).Pairwise fun u v ↦ overlapCount u v ≤ t - 1 := by
  obtain ⟨_, hmem, hpair⟩ := hatamiHozaChoices_spec ht htℓ hn
  unfold hatamiHozaMasks
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ hpair
  intro u v hu hv hcol
  rw [overlapCount_choicesToMask ((hmem u hu).1.trans (hmem v hv).1.symm) (hmem u hu).2
    (hmem v hv).2]
  exact hcol

/-- Explicit Hatami–Hoza $(R, \ell, t - 1)$-design with $n$ blocks and
$R = \ell q \le 10 \ell^2 / t$. -/
def hatamiHozaDesign {n ℓ t : ℕ} (ht : 1 ≤ t) (htℓ : t ≤ ℓ) (hn : n ≤ 2 ^ t) :
    Design (ℓ * hatamiHozaBucketSize ℓ t) ℓ (t - 1) n :=
  Design.ofMasks
    (fun i : Fin n ↦ (hatamiHozaMasks n ℓ t)[i.1]'(by rw [length_hatamiHozaMasks]; exact i.2))
    (fun i ↦ length_mem_hatamiHozaMasks (List.getElem_mem _))
    (fun i ↦ count_true_mem_hatamiHozaMasks (List.getElem_mem _))
    (fun i j hij ↦ by
      have hp := pairwise_overlapCount_hatamiHozaMasks ht htℓ hn
      rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
      · exact List.pairwise_iff_getElem.mp hp i.1 j.1 _ _ hlt
      · exact absurd (Fin.ext heq) hij
      · rw [overlapCount_comm]
        exact List.pairwise_iff_getElem.mp hp j.1 i.1 _ _ hgt)

theorem ofFn_restrict_hatamiHozaDesign {n ℓ t : ℕ} (ht : 1 ≤ t) (htℓ : t ≤ ℓ) (hn : n ≤ 2 ^ t)
    (i : Fin n) (z : BitString (ℓ * hatamiHozaBucketSize ℓ t)) :
    List.ofFn ((hatamiHozaDesign ht htℓ hn).restrict i z) =
      restrictMask
        ((hatamiHozaMasks n ℓ t)[i.1]'(by rw [length_hatamiHozaMasks]; exact i.2))
        (List.ofFn z) :=
  ofFn_restrict_ofMasks _ _ _ _ i z

/-! ### Polynomial-Time Certificate for `hatamiHozaMasks` -/

private lemma dpRevRows_entry_le (q t : ℕ) (hq : 1 ≤ q) :
    ∀ i : ℕ, ((dpPrependStep q t)^[i] [dpInitRow t]).length = i + 1 ∧
      ∀ row ∈ (dpPrependStep q t)^[i] [dpInitRow t],
        row.length = t + 1 ∧ ∀ v ∈ row, v ≤ q ^ i
  | 0 => by
    refine ⟨rfl, fun row hrow ↦ ?_⟩
    rw [List.mem_singleton.mp hrow]
    refine ⟨by simp [dpInitRow], fun v hv ↦ ?_⟩
    simp only [dpInitRow, List.mem_cons, List.mem_replicate] at hv
    rcases hv with rfl | ⟨_, rfl⟩ <;> simp
  | i + 1 => by
    obtain ⟨hlen_i, hrows_i⟩ := dpRevRows_entry_le q t hq i
    rw [Function.iterate_succ_apply', dpPrependStep]
    refine ⟨by rw [List.length_cons, hlen_i], fun row hrow ↦ ?_⟩
    rcases List.mem_cons.mp hrow with rfl | hmem
    · refine ⟨by simp [dpNextRow], fun v hv ↦ ?_⟩
      have hhead_mem : ((dpPrependStep q t)^[i] [dpInitRow t]).headD [] ∈
          (dpPrependStep q t)^[i] [dpInitRow t] := by
        cases hlist : (dpPrependStep q t)^[i] [dpInitRow t] with
        | nil => rw [hlist] at hlen_i; simp at hlen_i
        | cons r rs => simp
      have hhead_le : ∀ x ∈ ((dpPrependStep q t)^[i] [dpInitRow t]).headD [], x ≤ q ^ i :=
        (hrows_i _ hhead_mem).2
      have hgetD_le :
          ∀ idx, (((dpPrependStep q t)^[i] [dpInitRow t]).headD []).getD idx 0 ≤ q ^ i := by
        intro idx
        rw [List.getD_eq_getElem?_getD]
        cases hget : (((dpPrependStep q t)^[i] [dpInitRow t]).headD [])[idx]? with
        | none => simp
        | some val => exact hhead_le val (List.mem_of_getElem? hget)
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
      rw [pow_succ']
      split_ifs
      · exact Nat.mul_le_mul_left q (hgetD_le 0)
      · calc (((dpPrependStep q t)^[i] [dpInitRow t]).headD []).getD (r - 1) 0 +
              (q - 1) * (((dpPrependStep q t)^[i] [dpInitRow t]).headD []).getD r 0
            ≤ 1 * q ^ i + (q - 1) * q ^ i :=
              Nat.add_le_add (by simpa using hgetD_le (r - 1))
                (Nat.mul_le_mul_left (q - 1) (hgetD_le r))
          _ = q * q ^ i := by rw [← add_mul, show 1 + (q - 1) = q by omega]
    · obtain ⟨hr_len, hr_le⟩ := hrows_i row hmem
      refine ⟨hr_len, fun v hv ↦ (hr_le v hv).trans ?_⟩
      rw [pow_succ']
      exact Nat.le_mul_of_pos_left _ hq

private lemma length_encList_le_of_forall_le {α : Type} (enc : α ↪ List Bool) {l : List α} {B : ℕ}
    (hB : ∀ x ∈ l, (enc x).length ≤ B) :
    (encList enc l).length ≤ l.length * (2 * B + 1) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [length_encList] at ih ⊢
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have ha := hB a List.mem_cons_self
    have hrest := ih fun x hx ↦ hB x (List.mem_cons_of_mem a hx)
    nlinarith

private lemma dpRevRows_pos_polyTime :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) ↦ dpRevRows (max 1 p.1) p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) (encList (encList encNat)) := by
  let encIn := encPair encUnary (encPair encUnary encUnary)
  let stepFn (par : ℕ × ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
    dpPrependStep par.1 par.2 rows
  have hpar : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) ↦ (max 1 p.1, p.2.2))
      encIn (encPair encUnary encUnary) := by fun_prop
  have hcount : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) ↦ p.2.1) encIn encUnary := by fun_prop
  have hinit : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) ↦ [dpInitRow p.2.2])
      encIn (encList (encList encNat)) := by
    unfold dpInitRow
    fun_prop
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List ℕ) ↦ stepFn p.1 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encNat)))
      (encList (encList encNat)) := by
    unfold stepFn dpPrependStep dpNextRow
    have hq_bin : ComputableInPolyTime
        (fun p : ((ℕ × ℕ) × List (List ℕ)) × ℕ ↦ p.1.1.1)
        (encPair (encPair (encPair encUnary encUnary) (encList (encList encNat))) encUnary)
        encNat := unary_to_binary.comp (by fun_prop)
    have hqm1_bin : ComputableInPolyTime
        (fun p : ((ℕ × ℕ) × List (List ℕ)) × ℕ ↦ p.1.1.1 - 1)
        (encPair (encPair (encPair encUnary encUnary) (encList (encList encNat))) encUnary)
        encNat := unary_to_binary.comp (by fun_prop)
    fun_prop
  unfold dpRevRows
  refine iterateWith (step := stepFn) hpar hcount hinit hstep
    (bound := fun p ↦ (p.2.1 + 1) * (2 * ((p.2.2 + 1) * (2 * ((max 1 p.1) * p.2.1 + 1) + 1)) + 1))
    (polyBounded (by fun_prop))
    fun p i hi ↦ ?_
  set q := max 1 p.1
  have hq1 : 1 ≤ q := Nat.le_max_left 1 p.1
  obtain ⟨hlen_rows, hrows⟩ := dpRevRows_entry_le q p.2.2 hq1 i
  have hrow_bound : ∀ row ∈ (dpPrependStep q p.2.2)^[i] [dpInitRow p.2.2],
      (encList encNat row).length ≤ (p.2.2 + 1) * (2 * (q * p.2.1 + 1) + 1) := by
    intro row hrow
    obtain ⟨hr_len, hr_le⟩ := hrows row hrow
    rw [← hr_len]
    refine length_encList_le_of_forall_le encNat fun v hv ↦ ?_
    simp only [encNat_apply, Nat.size_eq_bits_len]
    refine Nat.size_le.mpr ?_
    have hv_le : v ≤ q ^ i := hr_le v hv
    have hqi_le : q ^ i ≤ q ^ p.2.1 := Nat.pow_le_pow_right hq1 hi
    have hq_lt : q < 2 ^ q := Nat.lt_two_pow_self
    calc v ≤ q ^ p.2.1 := hv_le.trans hqi_le
      _ ≤ (2 ^ q) ^ p.2.1 := Nat.pow_le_pow_left hq_lt.le p.2.1
      _ = 2 ^ (q * p.2.1) := (pow_mul 2 q p.2.1).symm
      _ < 2 ^ (q * p.2.1 + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have houter := length_encList_le_of_forall_le (encList encNat) hrow_bound
  rw [hlen_rows] at houter
  exact houter.trans (Nat.mul_le_mul_right _ (by omega))

private lemma bucketChoiceStep_polyTime :
    let encSt := encPair (encList encUnary) (encList (encPair (encList encUnary) encUnary))
    ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦
        bucketChoiceStep w.1.1 w.1.2 w.2)
      (encPair (encPair encUnary encSt) (encList encNat)) encSt := by
  intro encSt
  let encW := encPair (encPair encUnary encSt) (encList encNat)
  have hq_w : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦ w.1.1) encW encUnary :=
    (fst encUnary encSt).comp (fst _ (encList encNat))
  have hst1_w : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦ w.1.2.1)
      encW (encList encUnary) :=
    (fst (encList encUnary) (encList (encPair (encList encUnary) encUnary))).comp
      ((snd encUnary encSt).comp (fst _ (encList encNat)))
  have hst2_w : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦ w.1.2.2)
      encW (encList (encPair (encList encUnary) encUnary)) :=
    (snd (encList encUnary) (encList (encPair (encList encUnary) encUnary))).comp
      ((snd encUnary encSt).comp (fst _ (encList encNat)))
  have hrow_w : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦ w.2)
      encW (encList encNat) :=
    snd (encPair encUnary encSt) (encList encNat)
  have hrange : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦ List.range w.1.1)
      encW (encList encUnary) := by
    have := hq_w
    fun_prop
  have htest : ComputableInPolyTime
      (fun p : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ ↦
        decide (bucketChoiceScore p.1.2 p.1.1.2.2 p.2 < p.1.2.getD 0 0))
      (encPair encW encUnary) encBool := by
    unfold bucketChoiceScore
    have hst2_p := hst2_w.comp (fst encW encUnary)
    have hrow_p := hrow_w.comp (fst encW encUnary)
    have hc_p : ComputableInPolyTime
        (fun p : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ ↦ p.2)
        (encPair encW encUnary) encUnary := snd encW encUnary
    have hmapped : ComputableInPolyTime
        (fun p : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ ↦
          p.1.1.2.2.map fun vr ↦
            p.1.2.getD (if p.2 == vr.1.headD 0 then vr.2 - 1 else vr.2) 0)
        (encPair encW encUnary) (encList encNat) := by
      refine mapWithInput hst2_p ?_
      have hrow_pp :=
        hrow_p.comp (fst (encPair encW encUnary) (encPair (encList encUnary) encUnary))
      have hc_pp := hc_p.comp (fst (encPair encW encUnary) (encPair (encList encUnary) encUnary))
      have hvr1 : ComputableInPolyTime
          (fun q : (((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ) × (List ℕ × ℕ) ↦ q.2.1)
          (encPair (encPair encW encUnary) (encPair (encList encUnary) encUnary))
          (encList encUnary) :=
        (fst (encList encUnary) encUnary).comp (snd _ _)
      have hvr2 : ComputableInPolyTime
          (fun q : (((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ) × (List ℕ × ℕ) ↦ q.2.2)
          (encPair (encPair encW encUnary) (encPair (encList encUnary) encUnary)) encUnary :=
        (snd (encList encUnary) encUnary).comp (snd _ _)
      fun_prop
    have hsum_p : ComputableInPolyTime
        (fun p : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ ↦
          (p.1.1.2.2.map fun vr ↦
            p.1.2.getD (if p.2 == vr.1.headD 0 then vr.2 - 1 else vr.2) 0).sum)
        (encPair encW encUnary) encNat := binary_sum.comp hmapped
    have hrhs_p : ComputableInPolyTime
        (fun p : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × ℕ ↦ p.1.2.getD 0 0)
        (encPair encW encUnary) encNat := by
      have := hrow_p
      fun_prop
    exact binary_lt' hsum_p hrhs_p
  have hc_w : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦
        ((List.range w.1.1).find? fun c ↦
          decide (bucketChoiceScore w.2 w.1.2.2 c < w.2.getD 0 0)).getD 0)
      encW encUnary :=
    optionGetDWithInput (findWithInput hrange htest) (const 0)
  have hnew1 : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦
        w.1.2.1 ++ [((List.range w.1.1).find? fun c ↦
          decide (bucketChoiceScore w.2 w.1.2.2 c < w.2.getD 0 0)).getD 0])
      encW (encList encUnary) := by
    have := hst1_w
    have := hc_w
    fun_prop
  have hnew2 : ComputableInPolyTime
      (fun w : (ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ ↦
        w.1.2.2.map fun vr ↦
          (vr.1.tail,
            if ((List.range w.1.1).find? fun c ↦
                decide (bucketChoiceScore w.2 w.1.2.2 c < w.2.getD 0 0)).getD 0 ==
              vr.1.headD 0 then vr.2 - 1 else vr.2))
      encW (encList (encPair (encList encUnary) encUnary)) := by
    refine mapWithInput hst2_w ?_
    have hc_q := hc_w.comp (fst encW (encPair (encList encUnary) encUnary))
    have hvr1 : ComputableInPolyTime
        (fun q : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × (List ℕ × ℕ) ↦ q.2.1)
        (encPair encW (encPair (encList encUnary) encUnary)) (encList encUnary) :=
      (fst (encList encUnary) encUnary).comp (snd _ _)
    have hvr2 : ComputableInPolyTime
        (fun q : ((ℕ × (List ℕ × List (List ℕ × ℕ))) × List ℕ) × (List ℕ × ℕ) ↦ q.2.2)
        (encPair encW (encPair (encList encUnary) encUnary)) encUnary :=
      (snd (encList encUnary) encUnary).comp (snd _ _)
    fun_prop
  exact hnew1.prod hnew2

private lemma nextChoiceList_polyTime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦
        nextChoiceList p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encNat)))
        (encList (encList encUnary)))
      (encList encUnary) := by
  let encIn := encPair (encPair (encPair encUnary encUnary) (encList (encList encNat)))
    (encList (encList encUnary))
  let encSt := encPair (encList encUnary) (encList (encPair (encList encUnary) encUnary))
  have hpar : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦ p.1.1.1) encIn encUnary := by fun_prop
  have hlist : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦ p.1.2)
      encIn (encList (encList encNat)) := by fun_prop
  have hinit : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦
        (([] : List ℕ), p.2.map fun v ↦ (v, p.1.1.2)))
      encIn encSt := by
    have hp2 : ComputableInPolyTime
        (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦ p.2)
        encIn (encList (encList encUnary)) := snd _ (encList (encList encUnary))
    have ht_in : ComputableInPolyTime
        (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦ p.1.1.2) encIn encUnary := by fun_prop
    refine (const ([] : List ℕ)).prod (mapWithInput hp2 ?_)
    exact (snd encIn (encList encUnary)).prod (ht_in.comp (fst encIn (encList encUnary)))
  have hfold : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦
        p.1.2.foldl (bucketChoiceStep p.1.1.1) ([], p.2.map fun v ↦ (v, p.1.1.2)))
      encIn encSt := by
    refine foldlWith_of_bounded_growth (encB := encSt) (step := bucketChoiceStep)
      hpar hlist hinit bucketChoiceStep_polyTime
      (growth := fun p ↦ 4 * p.1.1.1 + 4) (polyBounded (by fun_prop))
      fun p st row _ ↦ ?_
    set q := p.1.1.1
    set c := ((List.range q).find? fun c ↦
      decide (bucketChoiceScore row st.2 c < row.getD 0 0)).getD 0
    have hc_le : c ≤ q := by
      cases hfind : (List.range q).find? fun c ↦
          decide (bucketChoiceScore row st.2 c < row.getD 0 0) with
      | none =>
        have hc0 : c = 0 := by dsimp only [c]; rw [hfind]; rfl
        omega
      | some c₀ =>
        have hlt : c₀ < q := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
        have hcc : c = c₀ := by dsimp only [c]; rw [hfind]; rfl
        omega
    have hfst_grow : (encList encUnary (st.1 ++ [c])).length ≤
        (encList encUnary st.1).length + (2 * q + 1) := by
      rw [length_encList, length_encList, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton, encUnary_apply, List.length_replicate]
      omega
    have hsnd_shrink :
        (encList (encPair (encList encUnary) encUnary)
          (st.2.map fun vr ↦ (vr.1.tail, if c == vr.1.headD 0 then vr.2 - 1 else vr.2))).length ≤
        (encList (encPair (encList encUnary) encUnary) st.2).length := by
      rw [length_encList, length_encList, List.map_map]
      refine List.sum_le_sum fun vr _ ↦ ?_
      simp only [Function.comp_apply, length_encPair, encUnary_apply, List.length_replicate]
      have htail_le : (encList encUnary vr.1.tail).length ≤ (encList encUnary vr.1).length := by
        cases vr.1 with
        | nil => simp
        | cons a rest => simp [length_encList]
      have hrem_le : (if c == vr.1.headD 0 then vr.2 - 1 else vr.2) ≤ vr.2 := by
        split_ifs <;> omega
      omega
    have hpair_lhs :
        (encSt (bucketChoiceStep q st row)).length =
          2 * (encList encUnary (st.1 ++ [c])).length + 1 +
            (encList (encPair (encList encUnary) encUnary)
              (st.2.map fun vr ↦ (vr.1.tail, if c == vr.1.headD 0 then vr.2 -
                1 else vr.2))).length :=
      length_encPair (bucketChoiceStep q st row)
    have hpair_rhs :
        (encSt st).length =
          2 * (encList encUnary st.1).length + 1 +
            (encList (encPair (encList encUnary) encUnary) st.2).length :=
      length_encPair st
    rw [hpair_lhs, hpair_rhs]
    omega
  exact hfold.fst'

attribute [local irreducible] dpRevRows nextChoiceList in
/-- **Hatami–Hoza design masks in polynomial time**: `hatamiHozaMasks n ℓ t` is computable in time
polynomial in `(n, ℓ, t)` on a multi-tape Turing machine. -/
theorem hatamiHozaMasks_polyTime :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) ↦ hatamiHozaMasks p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) (encList encBits) := by
  let encIn := encPair encUnary (encPair encUnary encUnary)
  let encPar := encPair (encPair encUnary encUnary) (encList (encList encNat))
  have hq : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) ↦ hatamiHozaBucketSize p.2.1 p.2.2) encIn encUnary := by
    unfold hatamiHozaBucketSize
    fun_prop
  have hrows : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) ↦ (dpRevRows (hatamiHozaBucketSize p.2.1 p.2.2) p.2.1 p.2.2).tail)
      encIn (encList (encList encNat)) := by
    have h1 := dpRevRows_pos_polyTime.comp (hq.prod (snd encUnary (encPair encUnary encUnary)))
    have hmax_eq : ∀ p : ℕ × (ℕ × ℕ),
        max 1 (hatamiHozaBucketSize p.2.1 p.2.2) = hatamiHozaBucketSize p.2.1 p.2.2 :=
      fun p ↦ max_eq_right (one_le_hatamiHozaBucketSize p.2.1 p.2.2)
    have h2 : ComputableInPolyTime
        (fun p : ℕ × (ℕ × ℕ) ↦ dpRevRows (hatamiHozaBucketSize p.2.1 p.2.2) p.2.1 p.2.2)
        encIn (encList (encList encNat)) := by
      convert h1 using 1
      funext p
      dsimp only [Function.comp_apply]
      rw [hmax_eq p]
    exact (listTail (encList encNat)).comp h2
  have hpar : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) ↦
        ((hatamiHozaBucketSize p.2.1 p.2.2, p.2.2),
          (dpRevRows (hatamiHozaBucketSize p.2.1 p.2.2) p.2.1 p.2.2).tail))
      encIn encPar := (hq.prod (by fun_prop)).prod hrows
  let outerStep (par : (ℕ × ℕ) × List (List ℕ)) (kept : List (List ℕ)) : List (List ℕ) :=
    kept ++ [nextChoiceList par.1.1 par.1.2 par.2 kept]
  have houterStep : ComputableInPolyTime
      (fun w : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦ outerStep w.1 w.2)
      (encPair encPar (encList (encList encUnary))) (encList (encList encUnary)) := by
    unfold outerStep
    have hkept : ComputableInPolyTime
        (fun w : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦ w.2)
        (encPair encPar (encList (encList encUnary))) (encList (encList encUnary)) :=
      snd encPar (encList (encList encUnary))
    have hsing : ComputableInPolyTime
        (fun w : ((ℕ × ℕ) × List (List ℕ)) × List (List ℕ) ↦
          [nextChoiceList w.1.1.1 w.1.1.2 w.1.2 w.2])
        (encPair encPar (encList (encList encUnary))) (encList (encList encUnary)) :=
      (ComputableInPolyTime.cons (encList encUnary)).comp (nextChoiceList_polyTime.prod (const []))
    exact (listAppend (encList encUnary)).comp (hkept.prod hsing)
  have hchoices : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) ↦ hatamiHozaChoices p.1 p.2.1 p.2.2)
      encIn (encList (encList encUnary)) := by
    have hgrow_poly :
        ComputableInPolyTime
          (fun p : ℕ × (ℕ × ℕ) ↦ 2 * (p.2.1 * (2 * hatamiHozaBucketSize p.2.1 p.2.2 + 1)) + 1)
          encIn encUnary :=
      unary_add'
        (unary_mul' (const 2)
          (unary_mul' ((fst encUnary encUnary).comp (snd encUnary (encPair encUnary encUnary)))
            (unary_add' (unary_mul' (const 2) hq) (const 1))))
        (const 1)
    unfold hatamiHozaChoices
    refine iterateWith_of_bounded_growth (encState := encList (encList encUnary))
      (step := outerStep) hpar (fst encUnary (encPair encUnary encUnary))
      (const []) houterStep
      (growth := fun p ↦ 2 * (p.2.1 * (2 * hatamiHozaBucketSize p.2.1 p.2.2 + 1)) + 1)
      (polyBounded hgrow_poly)
      fun p kept ↦ ?_
    set q := hatamiHozaBucketSize p.2.1 p.2.2
    have hq1 : 1 ≤ q := one_le_hatamiHozaBucketSize p.2.1 p.2.2
    set u := nextChoiceList q p.2.2 (dpRevRows q p.2.1 p.2.2).tail kept
    have hu_len : u.length = p.2.1 := by
      rw [length_nextChoiceList]
      simp [length_dpRevRows]
    have hu_lt : ∀ c ∈ u, c < q := mem_lt_of_nextChoiceList hq1 p.2.2 _ kept
    have hu_enc : (encList encUnary u).length ≤ p.2.1 * (2 * q + 1) := by
      rw [← hu_len]
      refine length_encList_le_of_forall_le encUnary fun c hc ↦ ?_
      simp only [encUnary_apply, List.length_replicate]
      exact (hu_lt c hc).le
    change (encList (encList encUnary) (kept ++ [u])).length ≤
      (encList (encList encUnary) kept).length + (2 * (p.2.1 * (2 * q + 1)) + 1)
    rw [length_encList, length_encList, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    omega
  unfold hatamiHozaMasks choicesToMask
  refine mapWithInput hchoices ?_
  have hq_sub := hq.comp (fst encIn (encList encUnary))
  have hu_sub : ComputableInPolyTime
      (fun r : (ℕ × (ℕ × ℕ)) × List ℕ ↦ r.2)
      (encPair encIn (encList encUnary)) (encList encUnary) := snd encIn (encList encUnary)
  exact flatMapToBitsWithInput hu_sub (bitsSingle.comp
    ((hq_sub.comp (fst (encPair encIn (encList encUnary)) encUnary)).prod
      (snd (encPair encIn (encList encUnary)) encUnary)))

end CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
