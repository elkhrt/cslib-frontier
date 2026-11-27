/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Dual

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Benchmark Boolean Functions for Approximate Degree: Surjectivity and $k$-Element Distinctness

This module defines binary-encoded input domains and the canonical benchmark Boolean functions
$\mathrm{SURJ}_{N, 2^b}$ (surjectivity) and $k\mathrm{ED}_{N, 2^b}$ ($k$-element distinctness),
together with their self-reduction embeddings showing that each contains block-composed conjunctions
of smaller instances as literal bit-restriction subfunctions.

## Main definitions

* `CslibFrontier.QueryComplexity.decodeFin`: binary decoding `BitString b → Fin (2 ^ b)`.
* `CslibFrontier.QueryComplexity.encodeFin`: binary encoding `Fin (2 ^ b) → BitString b`.
* `CslibFrontier.QueryComplexity.decodeTuple`: decoding `BitString (N * b)` as `Fin N → Fin (2 ^
  b)`.
* `CslibFrontier.QueryComplexity.surjFun`: the surjectivity function $\mathrm{SURJ}_{N, 2^b}$.
* `CslibFrontier.QueryComplexity.kEDFun`: the $k$-element distinctness function $k\mathrm{ED}_{N,
  2^b}$.
* `CslibFrontier.QueryComplexity.disjointRangeEmbed`: literal bit-restriction embedding of $2^a$
  blocks
  of $N'$ items in $[2^{b'}]$ into $2^a N'$ items in $[2^{a + b'}]$ with pairwise disjoint ranges.

## Main results

* `CslibFrontier.QueryComplexity.decodeFin_bijective`: `decodeFin b` is a bijection with inverse
  `encodeFin b`.
* `CslibFrontier.QueryComplexity.surjFun_disjointRangeEmbed`:
  $\mathrm{SURJ}_{2^a N', 2^{a+b'}} \circ \mathrm{embed} = \mathrm{AND}_{2^a} \circ
  \mathrm{SURJ}_{N', 2^{b'}}^{2^a}$.
* `CslibFrontier.QueryComplexity.kEDFun_disjointRangeEmbed`:
  $k\mathrm{ED}_{2^a N', 2^{a+b'}} \circ \mathrm{embed} = \mathrm{AND}_{2^a} \circ k\mathrm{ED}_{N',
  2^{b'}}^{2^a}$.
* `CslibFrontier.QueryComplexity.surjFun_zero_bits`,
  `CslibFrontier.QueryComplexity.kEDFun_one_eq_false`:
  boundary evaluations.
-/

public section

open Finset Cslib Cslib.BitString

namespace CslibFrontier.QueryComplexity

/-! ### Binary encoding and decoding -/

/-- Binary decoding of a `b`-bit string into `Fin (2 ^ b)`. -/
def decodeFin (b : ℕ) (w : BitString b) : Fin (2 ^ b) :=
  ⟨∑ i : Fin b, (w i).toNat * 2 ^ i.1, by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Fin.sum_univ_castSucc]
      have hlt : ∑ i : Fin b, (w i.castSucc).toNat * 2 ^ i.1 < 2 ^ b := ih (fun i => w i.castSucc)
      have hlast : (w (Fin.last b)).toNat * 2 ^ b ≤ 2 ^ b := by
        cases w (Fin.last b) <;> simp
      have hpow : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by ring
      simp only [Fin.val_castSucc, Fin.val_last] at hlt hlast ⊢
      omega⟩

/-- Binary encoding of an element of `Fin (2 ^ b)` as a `b`-bit string. -/
def encodeFin (b : ℕ) (k : Fin (2 ^ b)) : BitString b :=
  fun i => decide ((k.1 / 2 ^ i.1) % 2 = 1)

lemma decodeFin_val_eq_sum (b : ℕ) (w : BitString b) :
    (decodeFin b w).1 = ∑ i : Fin b, (w i).toNat * 2 ^ i.1 := by rfl

@[simp]
lemma decodeFin_encodeFin (b : ℕ) (k : Fin (2 ^ b)) : decodeFin b (encodeFin b k) = k := by
  apply Fin.ext
  change ∑ i : Fin b, (decide ((k.1 / 2 ^ i.1) % 2 = 1)).toNat * 2 ^ i.1 = k.1
  have hval : ∀ (m : ℕ) (n : ℕ), n < 2 ^ m →
      ∑ i : Fin m, (decide ((n / 2 ^ i.1) % 2 = 1)).toNat * 2 ^ i.1 = n := by
    intro m
    induction m with
    | zero =>
      intro n hn
      simp only [pow_zero] at hn
      simp [show n = 0 by omega]
    | succ m ih =>
      intro n hn
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ]
      have hrest : ∑ i : Fin m, (decide ((n / 2 ^ (i.1 + 1)) % 2 = 1)).toNat * 2 ^ (i.1 + 1) =
          2 * ∑ i : Fin m, (decide (((n / 2) / 2 ^ i.1) % 2 = 1)).toNat * 2 ^ i.1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm 2 (2 ^ i.1)]
        ring
      have hlt : n / 2 < 2 ^ m := by
        have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by ring
        omega
      rw [hrest, ih (n / 2) hlt]
      have hmod : (decide (n % 2 = 1)).toNat = n % 2 := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
      rw [hmod]
      omega
  exact hval b k.1 k.2

@[simp]
lemma encodeFin_decodeFin (b : ℕ) (w : BitString b) : encodeFin b (decodeFin b w) = w := by
  funext i
  have hbit : ∀ (m : ℕ) (v : BitString m) (j : Fin m),
      ((∑ r : Fin m, (v r).toNat * 2 ^ r.1) / 2 ^ j.1) % 2 = (v j).toNat := by
    intro m
    induction m with
    | zero => intro _ j; exact Fin.elim0 j
    | succ m ih =>
      intro v j
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have htail : ∑ r : Fin m, (v r.succ).toNat * 2 ^ (r.1 + 1) =
          2 * ∑ r : Fin m, (v r.succ).toNat * 2 ^ r.1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by rw [pow_succ]; ring
      rw [htail]
      refine Fin.cases ?_ ?_ j
      · simp only [Fin.val_zero, pow_zero, Nat.div_one]
        have h0 : (v 0).toNat < 2 := by cases v 0 <;> simp
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      · intro r
        simp only [Fin.val_succ, pow_succ, mul_comm (2 ^ r.1) 2, ← Nat.div_div_eq_div_mul]
        have h0 : (v 0).toNat < 2 := by cases v 0 <;> simp
        have hdiv : ((v 0).toNat + 2 * ∑ k : Fin m, (v k.succ).toNat * 2 ^ k.1) / 2 =
            ∑ k : Fin m, (v k.succ).toNat * 2 ^ k.1 := by omega
        rw [hdiv]
        exact ih (fun k => v k.succ) r
  have hb := hbit b w i
  simp only [encodeFin, decodeFin, hb]
  cases w i <;> decide

lemma decodeFin_bijective (b : ℕ) : Function.Bijective (decodeFin b) :=
  Function.bijective_iff_has_inverse.mpr ⟨encodeFin b, encodeFin_decodeFin b, decodeFin_encodeFin b⟩

lemma decodeFin_injective (b : ℕ) : Function.Injective (decodeFin b) :=
  (decodeFin_bijective b).1

lemma decodeFin_surjective (b : ℕ) : Function.Surjective (decodeFin b) :=
  (decodeFin_bijective b).2

/-- Decode a `BitString (N * b)` as a list of `N` elements of `Fin (2 ^ b)`. -/
def decodeTuple (N b : ℕ) (x : BitString (N * b)) : Fin N → Fin (2 ^ b) :=
  fun i => decodeFin b (fun j => x (finProdFinEquiv (i, j)))

lemma decodeTuple_apply (N b : ℕ) (x : BitString (N * b)) (i : Fin N) :
    decodeTuple N b x i = decodeFin b (fun j => x (finProdFinEquiv (i, j))) := by rfl

/-! ### Surjectivity and $k$-element distinctness -/

/-- The surjectivity function $\mathrm{SURJ}_{N, 2^b}$: evaluates to `true` (`-1`) iff every
element of `Fin (2 ^ b)` appears at least once in `decodeTuple N b x`. -/
def surjFun (N b : ℕ) : BooleanFunction (N * b) :=
  fun x => decide (Function.Surjective (decodeTuple N b x))

/-- The $k$-element distinctness function $k\mathrm{ED}_{N, 2^b}$: evaluates to `true` (`-1`) iff
no element of `Fin (2 ^ b)` appears `k` or more times in `decodeTuple N b x`. -/
def kEDFun (k N b : ℕ) : BooleanFunction (N * b) :=
  fun x => decide (∀ r : Fin (2 ^ b), #{i : Fin N | decodeTuple N b x i = r} < k)

lemma surjFun_eq_true_iff (N b : ℕ) (x : BitString (N * b)) :
    surjFun N b x = true ↔ Function.Surjective (decodeTuple N b x) := by
  simp [surjFun]

lemma kEDFun_eq_true_iff (k N b : ℕ) (x : BitString (N * b)) :
    kEDFun k N b x = true ↔ ∀ r : Fin (2 ^ b), #{i : Fin N | decodeTuple N b x i = r} < k := by
  simp [kEDFun]

/-! ### Boundary and non-degeneracy properties -/

lemma surjFun_zero_bits {N : ℕ} (hN : 1 ≤ N) (x : BitString (N * 0)) :
    surjFun N 0 x = true := by
  simp only [surjFun, decide_eq_true_eq]
  intro r
  refine ⟨⟨0, hN⟩, ?_⟩
  apply Fin.ext
  have hr := r.2
  simp only [pow_zero] at hr
  omega

lemma surjFun_false_of_lt {N b : ℕ} (h : N < 2 ^ b) (x : BitString (N * b)) :
    surjFun N b x = false := by
  simp only [surjFun, decide_eq_false_iff_not]
  intro hsurj
  have hle := Fintype.card_le_of_surjective _ hsurj
  simp [Fintype.card_fin] at hle
  omega

lemma kEDFun_one_eq_false {N b : ℕ} (hN : 1 ≤ N) (x : BitString (N * b)) :
    kEDFun 1 N b x = false := by
  simp only [kEDFun, decide_eq_false_iff_not, not_forall, not_lt]
  let i0 : Fin N := ⟨0, hN⟩
  refine ⟨decodeTuple N b x i0, ?_⟩
  exact Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

private example (b : ℕ) (hb : 1 ≤ b) :
    (∃ x, surjFun (2 ^ (b + 1)) b x = true) ∧ (∃ x, surjFun (2 ^ (b + 1)) b x = false) := by
  constructor
  · let y : BitString (2 ^ (b + 1) * b) := fun p =>
      let ij := finProdFinEquiv.symm p
      encodeFin b ⟨ij.1.1 % 2 ^ b, Nat.mod_lt _ (by positivity)⟩ ij.2
    refine ⟨y, ?_⟩
    simp only [surjFun, decide_eq_true_eq]
    intro r
    have hlt : r.1 < 2 ^ (b + 1) :=
      lt_trans r.2 (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self b))
    refine ⟨⟨r.1, hlt⟩, ?_⟩
    have hdec : decodeTuple (2 ^ (b + 1)) b y ⟨r.1, hlt⟩ = r := by
      simp only [decodeTuple, y, Equiv.symm_apply_apply]
      have hmod : r.1 % 2 ^ b = r.1 := Nat.mod_eq_of_lt r.2
      have hfin : (⟨r.1 % 2 ^ b, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ b)) = r :=
        Fin.ext hmod
      change decodeFin b (encodeFin b ⟨r.1 % 2 ^ b, Nat.mod_lt _ (by positivity)⟩) = r
      rw [hfin, decodeFin_encodeFin]
    exact hdec
  · refine ⟨fun _ => false, ?_⟩
    simp only [surjFun, decide_eq_false_iff_not]
    intro hsurj
    have h1lt : 1 < 2 ^ b := by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    obtain ⟨i, hi⟩ := hsurj ⟨1, h1lt⟩
    have hval := congrArg Fin.val hi
    simp only [decodeTuple, decodeFin, Bool.toNat_false, zero_mul, Finset.sum_const_zero] at hval
    omega

private example (k b : ℕ) (hk : 2 ≤ k) (hkb : k ≤ 2 ^ b) :
    (∃ x, kEDFun k (2 ^ b) b x = true) ∧ (∃ x, kEDFun k (2 ^ b) b x = false) := by
  constructor
  · let y : BitString (2 ^ b * b) := fun p =>
      let ij := finProdFinEquiv.symm p
      encodeFin b ij.1 ij.2
    refine ⟨y, ?_⟩
    simp only [kEDFun, decide_eq_true_eq]
    intro r
    have hcard : #{i : Fin (2 ^ b) | decodeTuple (2 ^ b) b y i = r} = 1 := by
      have hset : (Finset.univ.filter fun i : Fin (2 ^ b) => decodeTuple (2 ^ b) b y i = r) =
          {r} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        have hdec : decodeTuple (2 ^ b) b y i = i := by
          simp only [decodeTuple, y, Equiv.symm_apply_apply, decodeFin_encodeFin]
        rw [hdec]
      rw [hset, Finset.card_singleton]
    omega
  · refine ⟨fun _ => false, ?_⟩
    simp only [kEDFun, decide_eq_false_iff_not, not_forall, not_lt]
    refine ⟨⟨0, by positivity⟩, ?_⟩
    have hset : (Finset.univ.filter fun i : Fin (2 ^ b) =>
        decodeTuple (2 ^ b) b (fun _ => false) i = ⟨0, by positivity⟩) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      apply Fin.ext
      simp [decodeTuple, decodeFin]
    rw [hset, Finset.card_univ, Fintype.card_fin]
    exact hkb

/-! ### Self-reduction embedding for `SURJ` and `kED` -/

/-- Literal bit-restriction embedding of `2 ^ a` blocks of `N'` items in `Fin (2 ^ b')` into
`2 ^ a * N'` items in `Fin (2 ^ (a + b'))`, prefixing item `j` of block `t` with the `a`-bit
binary encoding of `t` so the `2 ^ a` blocks occupy pairwise disjoint subranges. -/
def disjointRangeEmbed (a b' N' : ℕ) (x : BitString (2 ^ a * (N' * b'))) :
    BitString ((2 ^ a * N') * (a + b')) :=
  fun p =>
    let qr := finProdFinEquiv.symm p
    let ti := finProdFinEquiv.symm qr.1
    if h : qr.2.1 < b' then
      x (finProdFinEquiv (ti.1, finProdFinEquiv (ti.2, ⟨qr.2.1, h⟩)))
    else
      encodeFin a ti.1 ⟨qr.2.1 - b', by have := qr.2.2; omega⟩

lemma disjointRangeEmbed_is_literal (a b' N' : ℕ) (p : Fin ((2 ^ a * N') * (a + b'))) :
    (∃ c : Bool, ∀ x, disjointRangeEmbed a b' N' x p = c) ∨
    (∃ q : Fin (2 ^ a * (N' * b')), ∀ x, disjointRangeEmbed a b' N' x p = x q) := by
  unfold disjointRangeEmbed
  dsimp only
  split_ifs with h
  · exact Or.inr ⟨_, fun _ => rfl⟩
  · exact Or.inl ⟨_, fun _ => rfl⟩

lemma decodeFin_concat (a b' : ℕ) (u : BitString b') (v : BitString a) :
    (decodeFin (a + b') (fun k => if h : k.1 < b' then u ⟨k.1, h⟩
        else v ⟨k.1 - b', by have := k.2; omega⟩)).1 =
      (decodeFin b' u).1 + 2 ^ b' * (decodeFin a v).1 := by
  simp only [decodeFin]
  let e : Fin b' ⊕ Fin a ≃ Fin (a + b') :=
    { toFun := fun s => match s with
        | .inl i => ⟨i.1, by omega⟩
        | .inr j => ⟨b' + j.1, by omega⟩
      invFun := fun k =>
        if h : k.1 < b' then .inl ⟨k.1, h⟩ else .inr ⟨k.1 - b', by omega⟩
      left_inv := fun s => by cases s with
        | inl i => simp [i.2]
        | inr j => simp
      right_inv := fun k => by
        dsimp only
        split_ifs with h
        · ext; simp
        · ext; dsimp; omega }
  rw [← Fintype.sum_equiv e (fun s => match s with
    | .inl i => (u i).toNat * 2 ^ i.1
    | .inr j => (v j).toNat * 2 ^ (b' + j.1)) _ (fun s => by
      cases s with
      | inl i => simp [e, i.2]
      | inr j =>
        have hnot : ¬ (b' + j.1 < b') := by omega
        simp [e, hnot])]
  rw [Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [pow_add]; ring

lemma decodeTuple_disjointRangeEmbed (a b' N' : ℕ) (x : BitString (2 ^ a * (N' * b')))
    (t : Fin (2 ^ a)) (i : Fin N') :
    (decodeTuple (2 ^ a * N') (a + b') (disjointRangeEmbed a b' N' x)
      (finProdFinEquiv (t, i))).1 =
    (decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) i).1 + 2 ^ b' * t.1 := by
  simp only [decodeTuple, disjointRangeEmbed, Equiv.symm_apply_apply]
  have hcat := decodeFin_concat a b'
    (fun j => x (finProdFinEquiv (t, finProdFinEquiv (i, j))))
    (encodeFin a t)
  rw [decodeFin_encodeFin] at hcat
  exact hcat

lemma surjFun_disjointRangeEmbed (a b' N' : ℕ) (x : BitString (2 ^ a * (N' * b'))) :
    surjFun (2 ^ a * N') (a + b') (disjointRangeEmbed a b' N' x) =
      blockComp (threshold (2 ^ a) (2 ^ a)) (surjFun N' b') x := by
  simp only [surjFun, blockComp_apply, threshold_apply]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  have hall_iff : 2 ^ a ≤ weight (fun t : Fin (2 ^ a) =>
        decide (Function.Surjective (decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q)))))) ↔
      ∀ t : Fin (2 ^ a), Function.Surjective (decodeTuple N' b' (fun q => x (finProdFinEquiv (t,
        q)))) := by
    constructor
    · intro hw t
      have hcard : #{t : Fin (2 ^ a) |
          decide (Function.Surjective (decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))))) =
            true} =
          2 ^ a :=
        le_antisymm ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)) hw
      have hfull := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin _).symm)
      have := Finset.ext_iff.mp hfull t
      simpa using this
    · intro hall
      have hfull : (Finset.univ.filter fun t : Fin (2 ^ a) =>
          decide (Function.Surjective (decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))))) =
            true) =
          Finset.univ := by
        ext t; simp [hall t]
      rw [weight, hfull, Finset.card_univ, Fintype.card_fin]
  rw [hall_iff]
  constructor
  · intro hsurj t r
    have hlt : r.1 + 2 ^ b' * t.1 < 2 ^ (a + b') := by
      have hpow : 2 ^ (a + b') = 2 ^ b' * 2 ^ a := by rw [pow_add, mul_comm]
      have ht1 : t.1 + 1 ≤ 2 ^ a := t.2
      nlinarith [r.2, show 0 < 2 ^ b' by positivity]
    obtain ⟨idx, hidx⟩ := hsurj ⟨r.1 + 2 ^ b' * t.1, hlt⟩
    let ti := finProdFinEquiv.symm idx
    have hidx' : idx = finProdFinEquiv (ti.1, ti.2) := (Equiv.apply_symm_apply _ _).symm
    rw [hidx'] at hidx
    have hval := congrArg Fin.val hidx
    rw [decodeTuple_disjointRangeEmbed] at hval
    dsimp only at hval
    have hr1 : (decodeTuple N' b' (fun q => x (finProdFinEquiv (ti.1, q))) ti.2).1 < 2 ^ b' :=
      (decodeTuple N' b' _ _).2
    have hti : ti.1 = t := by
      apply Fin.ext
      have hdiv1 : ((decodeTuple N' b' (fun q => x (finProdFinEquiv (ti.1, q))) ti.2).1 +
          2 ^ b' * ti.1.1) / 2 ^ b' = ti.1.1 := by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr1, zero_add]
      have hdiv2 : (r.1 + 2 ^ b' * t.1) / 2 ^ b' = t.1 := by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt r.2, zero_add]
      rw [← hdiv1, hval, hdiv2]
    subst hti
    refine ⟨ti.2, Fin.ext ?_⟩
    omega
  · intro hall r
    have hdiv_lt : r.1 / 2 ^ b' < 2 ^ a := by
      have hpow : 2 ^ (a + b') = 2 ^ b' * 2 ^ a := by rw [pow_add, mul_comm]
      have hr : r.1 < 2 ^ b' * 2 ^ a := by rw [← hpow]; exact r.2
      exact Nat.div_lt_of_lt_mul hr
    let t : Fin (2 ^ a) := ⟨r.1 / 2 ^ b', hdiv_lt⟩
    let s : Fin (2 ^ b') := ⟨r.1 % 2 ^ b', Nat.mod_lt _ (by positivity)⟩
    obtain ⟨i, hi⟩ := hall t s
    refine ⟨finProdFinEquiv (t, i), Fin.ext ?_⟩
    rw [decodeTuple_disjointRangeEmbed, hi]
    have hdm := Nat.mod_add_div r.1 (2 ^ b')
    simpa [s, t] using hdm

lemma kEDFun_disjointRangeEmbed (k a b' N' : ℕ) (x : BitString (2 ^ a * (N' * b'))) :
    kEDFun k (2 ^ a * N') (a + b') (disjointRangeEmbed a b' N' x) =
      blockComp (threshold (2 ^ a) (2 ^ a)) (kEDFun k N' b') x := by
  simp only [kEDFun, blockComp_apply, threshold_apply]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  have hall_iff : 2 ^ a ≤ weight (fun t : Fin (2 ^ a) =>
        decide (∀ s : Fin (2 ^ b'),
          #{i : Fin N' | decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) i = s} < k)) ↔
      ∀ t : Fin (2 ^ a), ∀ s : Fin (2 ^ b'),
        #{i : Fin N' | decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) i = s} < k := by
    constructor
    · intro hw t
      have hcard : #{t : Fin (2 ^ a) |
          decide (∀ s : Fin (2 ^ b'),
            #{i : Fin N' | decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) i = s} < k) =
              true} =
          2 ^ a :=
        le_antisymm ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)) hw
      have hfull := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin _).symm)
      have := Finset.ext_iff.mp hfull t
      simpa using this
    · intro hall
      have hfull : (Finset.univ.filter fun t : Fin (2 ^ a) =>
          decide (∀ s : Fin (2 ^ b'),
            #{i : Fin N' | decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) i = s} < k) =
              true) =
          Finset.univ := by
        ext t; simp [hall t]
      rw [weight, hfull, Finset.card_univ, Fintype.card_fin]
  rw [hall_iff]
  have hfiber : ∀ (t : Fin (2 ^ a)) (s : Fin (2 ^ b')),
      #{idx : Fin (2 ^ a * N') |
        decodeTuple (2 ^ a * N') (a + b') (disjointRangeEmbed a b' N' x) idx =
          ⟨s.1 + 2 ^ b' * t.1, by
            have hpow : 2 ^ (a + b') = 2 ^ b' * 2 ^ a := by rw [pow_add, mul_comm]
            have ht1 : t.1 + 1 ≤ 2 ^ a := t.2
            nlinarith [s.2, show 0 < 2 ^ b' by positivity]⟩} =
      #{i : Fin N' | decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) i = s} := by
    intro t s
    refine Finset.card_bij (fun idx _ => (finProdFinEquiv.symm idx).2)
      (fun idx hidx => ?_)
      (fun a1 ha1 a2 ha2 heq => ?_)
      (fun i hi => ?_)
    · have hval := congrArg Fin.val (Finset.mem_filter.mp hidx).2
      let ti := finProdFinEquiv.symm idx
      have hidx' : idx = finProdFinEquiv (ti.1, ti.2) := (Equiv.apply_symm_apply _ _).symm
      rw [hidx', decodeTuple_disjointRangeEmbed] at hval
      dsimp only at hval
      have hr1 : (decodeTuple N' b' (fun q => x (finProdFinEquiv (ti.1, q))) ti.2).1 < 2 ^ b' :=
        (decodeTuple N' b' _ _).2
      have hti : ti.1 = t := by
        apply Fin.ext
        have hdiv1 : ((decodeTuple N' b' (fun q => x (finProdFinEquiv (ti.1, q))) ti.2).1 +
            2 ^ b' * ti.1.1) / 2 ^ b' = ti.1.1 := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr1, zero_add]
        have hdiv2 : (s.1 + 2 ^ b' * t.1) / 2 ^ b' = t.1 := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt s.2, zero_add]
        rw [← hdiv1, hval, hdiv2]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext ?_⟩
      change (decodeTuple N' b' (fun q => x (finProdFinEquiv (t, q))) ti.2).1 = s.1
      rw [hti] at hval
      omega
    · have h1 := congrArg Fin.val (Finset.mem_filter.mp ha1).2
      have h2 := congrArg Fin.val (Finset.mem_filter.mp ha2).2
      let ti1 := finProdFinEquiv.symm a1
      let ti2 := finProdFinEquiv.symm a2
      have ha1' : a1 = finProdFinEquiv (ti1.1, ti1.2) := (Equiv.apply_symm_apply _ _).symm
      have ha2' : a2 = finProdFinEquiv (ti2.1, ti2.2) := (Equiv.apply_symm_apply _ _).symm
      rw [ha1', decodeTuple_disjointRangeEmbed] at h1
      rw [ha2', decodeTuple_disjointRangeEmbed] at h2
      dsimp only at h1 h2
      have hr1 : (decodeTuple N' b' (fun q => x (finProdFinEquiv (ti1.1, q))) ti1.2).1 < 2 ^ b' :=
        (decodeTuple N' b' _ _).2
      have hr2 : (decodeTuple N' b' (fun q => x (finProdFinEquiv (ti2.1, q))) ti2.2).1 < 2 ^ b' :=
        (decodeTuple N' b' _ _).2
      have ht1 : ti1.1 = t := by
        apply Fin.ext
        have hd1 : ((decodeTuple N' b' (fun q => x (finProdFinEquiv (ti1.1, q))) ti1.2).1 +
            2 ^ b' * ti1.1.1) / 2 ^ b' = ti1.1.1 := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr1, zero_add]
        have hds : (s.1 + 2 ^ b' * t.1) / 2 ^ b' = t.1 := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt s.2, zero_add]
        rw [← hd1, h1, hds]
      have ht2 : ti2.1 = t := by
        apply Fin.ext
        have hd2 : ((decodeTuple N' b' (fun q => x (finProdFinEquiv (ti2.1, q))) ti2.2).1 +
            2 ^ b' * ti2.1.1) / 2 ^ b' = ti2.1.1 := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr2, zero_add]
        have hds : (s.1 + 2 ^ b' * t.1) / 2 ^ b' = t.1 := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt s.2, zero_add]
        rw [← hd2, h2, hds]
      rw [ha1', ha2']
      exact congrArg finProdFinEquiv (Prod.ext (ht1.trans ht2.symm) heq)
    · refine ⟨finProdFinEquiv (t, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.ext ?_⟩, ?_⟩
      · rw [decodeTuple_disjointRangeEmbed, (Finset.mem_filter.mp hi).2]
      · simp
  constructor
  · intro hall t s
    rw [← hfiber t s]
    exact hall _
  · intro hall r
    have hdiv_lt : r.1 / 2 ^ b' < 2 ^ a := by
      have hpow : 2 ^ (a + b') = 2 ^ b' * 2 ^ a := by rw [pow_add, mul_comm]
      have hr : r.1 < 2 ^ b' * 2 ^ a := by rw [← hpow]; exact r.2
      exact Nat.div_lt_of_lt_mul hr
    let t : Fin (2 ^ a) := ⟨r.1 / 2 ^ b', hdiv_lt⟩
    let s : Fin (2 ^ b') := ⟨r.1 % 2 ^ b', Nat.mod_lt _ (by positivity)⟩
    have hr_eq : r = ⟨s.1 + 2 ^ b' * t.1, by
        have hpow : 2 ^ (a + b') = 2 ^ b' * 2 ^ a := by rw [pow_add, mul_comm]
        have ht1 : t.1 + 1 ≤ 2 ^ a := t.2
        nlinarith [s.2, show 0 < 2 ^ b' by positivity]⟩ := by
      apply Fin.ext
      exact (Nat.mod_add_div r.1 (2 ^ b')).symm
    rw [hr_eq, hfiber t s]
    exact hall t s

end CslibFrontier.QueryComplexity
