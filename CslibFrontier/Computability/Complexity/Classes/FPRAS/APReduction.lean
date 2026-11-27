/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.FPRAS
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

import CslibFrontier.Computability.Complexity.Classes.RepeatedTrials
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Sort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith

/-!
# Promise approximate counting, median amplification, and AP-reductions

Foundational definitions and structural lemmas for approximate counting on promise and total
counting problems, Valiant, and Vazirani and Dyer, Goldberg, Greenhill, and
Jerrum:

1. **Rational-pair median (`approxRatMedian`)**: polynomial-time stable merge-sort median on encoded
   numerator/denominator pairs `ℕ × ℕ`, preserving `ApproxWithin c p` whenever a strict majority of
   samples satisfies `ApproxWithin c p`.
2. **Promise FPTAS and FPRAS (`IsPromiseFPTAS`, `PromiseFPTAS`, `IsPromiseFPRAS`, `PromiseFPRAS`)**:
   agreeing with `Cslib.Complexity.IsFPRAS` and `Cslib.Complexity.FPRAS` on `Set.univ`, together
   with equivalence to constant-confidence (`3 / 4`) randomized approximation schemes via
   `approxRatMedian` repetition (`mem_PromiseFPRAS_iff_exists_isBoundedErrorFPRAS`).
3. **Promise parsimonious and approximation-preserving (`AP`) reductions**:
   `PromiseParsimoniousReducible`, `PromiseAPReducible`, `APReducible`, `SharpPHardPromiseAP`, and
   `SharpPHardAP`, plus reflexivity and lifting of parsimonious reductions to `AP`-reductions.

## Main definitions

* `Cslib.Complexity.leRatPair`, `Cslib.Complexity.approxRatMedian`.
* `Cslib.Complexity.IsPromiseFPTAS`, `Cslib.Complexity.PromiseFPTAS`,
  `Cslib.Complexity.FPTAS`.
* `Cslib.Complexity.IsPromiseFPRAS`, `Cslib.Complexity.PromiseFPRAS`,
  `Cslib.Complexity.IsBoundedErrorFPRAS`.
* `Cslib.Complexity.PromiseParsimoniousReducible`,
  `Cslib.Complexity.IsBoundedValidOracle`, `Cslib.Complexity.PromiseAPReducible`,
  `Cslib.Complexity.APReducible`, `Cslib.Complexity.SharpPHardPromiseAP`,
  `Cslib.Complexity.SharpPHardAP`.

## Main results

* `Cslib.Complexity.computableInPolyTime_approxRatMedian`,
  `Cslib.Complexity.approxWithin_approxRatMedian`.
* `Cslib.Complexity.mem_PromiseFPRAS_iff_exists_isBoundedErrorFPRAS`: median amplification
  from `3 / 4` success probability to `1 - (1 / 2) ^ t`.
* `Cslib.Complexity.IsBoundedErrorFPRAS.approx_real`: real-parameter `(1 ± ε)` guarantee for
  `0 < ε ≤ 1` with confidence `3 / 4`.
* `Cslib.Complexity.PromiseParsimoniousReducible.promiseAPReducible`,
  `Cslib.Complexity.PromiseParsimoniousReducible.mem_PromiseFPTAS`.
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

section RationalMedian

/-- Normalize a numerator/denominator pair so that a zero denominator becomes `1`. -/
@[expose] def normRatPair (a : ℕ × ℕ) : ℕ × ℕ :=
  (a.1, max a.2 1)

theorem pos_snd_normRatPair (a : ℕ × ℕ) : 0 < (normRatPair a).2 :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right a.2 1)

theorem normRatPair_eq_self {a : ℕ × ℕ} (ha : 0 < a.2) : normRatPair a = a := by
  ext
  · rfl
  · exact Nat.max_eq_left ha

/-- Total cross-multiplied preorder on rational pairs `ℕ × ℕ`, normalizing zero denominators to
`1` so transitivity holds unconditionally on all pairs. -/
@[expose] def leRatPair (a b : ℕ × ℕ) : Prop :=
  a.1 * max b.2 1 ≤ b.1 * max a.2 1

instance instDecidableRelLeRatPair : DecidableRel leRatPair :=
  fun a b => Nat.decLe (a.1 * max b.2 1) (b.1 * max a.2 1)

theorem leRatPair_refl (a : ℕ × ℕ) : leRatPair a a := le_rfl

theorem leRatPair_total (a b : ℕ × ℕ) : leRatPair a b ∨ leRatPair b a :=
  Nat.le_total _ _

theorem leRatPair_trans {a b c : ℕ × ℕ} (hab : leRatPair a b) (hbc : leRatPair b c) :
    leRatPair a c := by
  unfold leRatPair at hab hbc ⊢
  have hdb : 0 < max b.2 1 := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right b.2 1)
  have h1 : a.1 * max c.2 1 * max b.2 1 = a.1 * max b.2 1 * max c.2 1 := by ring
  have h2 : c.1 * max a.2 1 * max b.2 1 = c.1 * max b.2 1 * max a.2 1 := by ring
  refine Nat.le_of_mul_le_mul_right ?_ hdb
  rw [h1, h2]
  calc a.1 * max b.2 1 * max c.2 1
      ≤ b.1 * max a.2 1 * max c.2 1 := Nat.mul_le_mul_right _ hab
    _ = b.1 * max c.2 1 * max a.2 1 := by ring
    _ ≤ c.1 * max b.2 1 * max a.2 1 := Nat.mul_le_mul_right _ hbc

theorem leRatPair_iff_div_le {a b : ℕ × ℕ} (ha : 0 < a.2) (hb : 0 < b.2) :
    leRatPair a b ↔ (a.1 : ℝ) / a.2 ≤ (b.1 : ℝ) / b.2 := by
  unfold leRatPair
  rw [Nat.max_eq_left ha, Nat.max_eq_left hb,
    div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)]
  exact_mod_cast Iff.rfl

private lemma unary_half_eq_countP (n : ℕ) :
    n / 2 = (List.range n).countP (fun i => decide (2 * i + 1 < n)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | m
    · simp
    · simp
    · change (m + 2) / 2 = (List.range (m + 2)).countP (fun i => decide (2 * i + 1 < m + 2))
      have hm := ih m (by omega)
      have hsplit : List.range (m + 2) = 0 :: (List.range m).map (· + 1) ++ [m + 1] := by
        rw [List.range_succ, List.range_succ_eq_map]
      have hcongr :
          (List.range m).countP ((fun i => decide (2 * i + 1 < m + 2)) ∘ (· + 1)) =
            (List.range m).countP (fun i => decide (2 * i + 1 < m)) := by
        refine List.countP_congr fun i _ => ?_
        simp only [Function.comp_apply]
        by_cases hlt : 2 * i + 1 < m
        · have hlt' : 2 * (i + 1) + 1 < m + 2 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ (2 * (i + 1) + 1 < m + 2) := by omega
          simp [hlt, hlt']
      have h0 : decide (2 * 0 + 1 < m + 2) = true := by simp
      have hm1 : decide (2 * (m + 1) + 1 < m + 2) = false := by simp; omega
      rw [hsplit, List.countP_append, List.countP_cons, h0, List.countP_map, hcongr,
        List.countP_singleton, hm1, ← hm]
      simp only [↓reduceIte, Bool.false_eq_true]
      omega

private lemma computableInPolyTime_unary_half :
    ComputableInPolyTime (fun n : ℕ => n / 2) encUnary encUnary := by
  have h : ComputableInPolyTime
      (fun n : ℕ => (List.range n).countP (fun i => decide (2 * i + 1 < n)))
      encUnary encUnary := by
    fun_prop
  have hfn : (fun n : ℕ => n / 2) =
      fun n : ℕ => (List.range n).countP (fun i => decide (2 * i + 1 < n)) :=
    funext unary_half_eq_countP
  rwa [hfn]

@[fun_prop]
theorem computableInPolyTime_normRatPair :
    ComputableInPolyTime normRatPair (encPair encNat encNat) (encPair encNat encNat) := by
  have hmax : ComputableInPolyTime (fun a : ℕ × ℕ => if a.2 == 0 then 1 else a.2)
      (encPair encNat encNat) encNat := by
    fun_prop
  have hfn : normRatPair = fun a : ℕ × ℕ => (a.1, if a.2 == 0 then 1 else a.2) := by
    funext a
    ext
    · rfl
    · dsimp [normRatPair]
      cases a.2 <;> simp
  rw [hfn]
  exact (ComputableInPolyTime.fst encNat encNat).prod hmax

@[fun_prop]
theorem computableInPolyTime_decide_leRatPair :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (leRatPair p.1 p.2))
      (encPair (encPair encNat encNat) (encPair encNat encNat)) encBool := by
  let encP := encPair (encPair encNat encNat) (encPair encNat encNat)
  have hp1 : ComputableInPolyTime Prod.fst encP (encPair encNat encNat) :=
    ComputableInPolyTime.fst _ _
  have hp2 : ComputableInPolyTime Prod.snd encP (encPair encNat encNat) :=
    ComputableInPolyTime.snd _ _
  have ha1 : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) encP encNat :=
    (ComputableInPolyTime.fst encNat encNat).comp hp1
  have hb1 : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) encP encNat :=
    (ComputableInPolyTime.fst encNat encNat).comp hp2
  have ha2 : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (normRatPair p.1).2) encP encNat :=
    (ComputableInPolyTime.snd encNat encNat).comp (computableInPolyTime_normRatPair.comp hp1)
  have hb2 : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (normRatPair p.2).2) encP encNat :=
    (ComputableInPolyTime.snd encNat encNat).comp (computableInPolyTime_normRatPair.comp hp2)
  exact ComputableInPolyTime.binary_le'
    (ComputableInPolyTime.binary_mul' ha1 hb2)
    (ComputableInPolyTime.binary_mul' hb1 ha2)

/-- The **lower-upper median** of a list of rational pairs `(num, den) : ℕ × ℕ`: stably sort by
`leRatPair`, read index `xs.length / 2` (defaulting to `(0, 1)` on `[]`), and normalize a zero
denominator to `1`. -/
def approxRatMedian (xs : List (ℕ × ℕ)) : ℕ × ℕ :=
  normRatPair ((xs.mergeSort fun a b => decide (leRatPair a b)).getD (xs.length / 2) (0, 1))

theorem pos_snd_approxRatMedian (xs : List (ℕ × ℕ)) : 0 < (approxRatMedian xs).2 :=
  pos_snd_normRatPair _

/-- `approxRatMedian` is computable in polynomial time on framed lists of binary pairs. -/
@[fun_prop]
theorem computableInPolyTime_approxRatMedian :
    ComputableInPolyTime approxRatMedian
      (encList (encPair encNat encNat)) (encPair encNat encNat) := by
  have hsort : ComputableInPolyTime
      (fun xs : List (ℕ × ℕ) => xs.mergeSort fun a b => decide (leRatPair a b))
      (encList (encPair encNat encNat)) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.mergeSortWithInput (r := fun _ => leRatPair)
      ComputableInPolyTime.id' ?_ (fun _ _ _ _ => leRatPair_trans) (fun _ => leRatPair_total)
    exact computableInPolyTime_decide_leRatPair.comp
      (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  have hidx : ComputableInPolyTime
      (fun xs : List (ℕ × ℕ) => xs.length / 2)
      (encList (encPair encNat encNat)) encUnary :=
    computableInPolyTime_unary_half.comp
      (ComputableInPolyTime.length_list (encPair encNat encNat))
  have hdrop : ComputableInPolyTime
      (fun xs : List (ℕ × ℕ) =>
        (xs.mergeSort fun a b => decide (leRatPair a b)).drop (xs.length / 2))
      (encList (encPair encNat encNat)) (encList (encPair encNat encNat)) :=
    ComputableInPolyTime.listDropWithInput hsort hidx
  have hget : ComputableInPolyTime
      (fun xs : List (ℕ × ℕ) =>
        ((xs.mergeSort fun a b => decide (leRatPair a b)).drop (xs.length / 2)).headD (0, 1))
      (encList (encPair encNat encNat)) (encPair encNat encNat) :=
    ComputableInPolyTime.listHeadDWithInput hdrop (ComputableInPolyTime.const (0, 1))
  have hfn : approxRatMedian = fun xs : List (ℕ × ℕ) =>
      normRatPair (((xs.mergeSort fun a b => decide (leRatPair a b)).drop
        (xs.length / 2)).headD (0, 1)) := by
    funext xs
    simp [approxRatMedian, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]
  rw [hfn]
  exact computableInPolyTime_normRatPair.comp hget

/-- The encoded bit-length of `approxRatMedian xs` is bounded by `M + 3` whenever every entry of
`xs` has encoded bit-length at most `M`, independent of `xs.length`. -/
theorem length_enc_approxRatMedian_le {xs : List (ℕ × ℕ)} {M : ℕ}
    (hM : ∀ x ∈ xs, (encPair encNat encNat x).length ≤ M) :
    (encPair encNat encNat (approxRatMedian xs)).length ≤ M + 3 := by
  have hnorm_len : ∀ p : ℕ × ℕ,
      (encPair encNat encNat (normRatPair p)).length ≤ (encPair encNat encNat p).length + 1 := by
    intro ⟨a, b⟩
    rcases b with _ | b
    · simp [normRatPair, encNat_apply]
    · rw [normRatPair_eq_self (Nat.succ_pos b)]
      omega
  rcases xs with _ | ⟨hd, tl⟩
  · simp [approxRatMedian, normRatPair, encNat_apply]
  · set s := (hd :: tl).mergeSort fun a b => decide (leRatPair a b)
    have hperm : s.Perm (hd :: tl) := by
      dsimp only [s]
      rw [List.mergeSort_decide_eq_insertionSort leRatPair (fun _ _ _ => leRatPair_trans)
        leRatPair_total (hd :: tl)]
      exact List.perm_insertionSort leRatPair (hd :: tl)
    have hslen : s.length = (hd :: tl).length := hperm.length_eq
    have hlt : (hd :: tl).length / 2 < s.length := by
      have : 0 < (hd :: tl).length := by simp
      omega
    have hmem : s.getD ((hd :: tl).length / 2) (0, 1) ∈ (hd :: tl) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact hperm.subset (List.getElem_mem hlt)
    have h1 := hnorm_len (s.getD ((hd :: tl).length / 2) (0, 1))
    have h2 := hM _ hmem
    dsimp only [approxRatMedian]
    exact h1.trans (Nat.add_le_add_right h2 1 |>.trans (by omega))

/-- Exact natural-number characterization of `ApproxWithin c p num den` for `0 < p`. -/
theorem approxWithin_iff_nat {c p num den : ℕ} (hp : 0 < p) :
    ApproxWithin c p num den ↔
      0 < den ∧ c * den * p ≤ num * p + c * den ∧ num * p ≤ c * den * p + c * den := by
  unfold ApproxWithin
  constructor
  · rintro ⟨hden, hle⟩
    rw [abs_le] at hle
    have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hdp : (0 : ℝ) < (den : ℝ) * p := mul_pos hdenR hpR
    have hlo : (c : ℝ) * den * p ≤ (num : ℝ) * p + (c : ℝ) * den := by
      have h1 := mul_le_mul_of_nonneg_right hle.1 hdp.le
      have h2 : ((num : ℝ) / den - c) * (den * p) = (num : ℝ) * p - (c : ℝ) * den * p := by
        field_simp
      have h3 : -((c : ℝ) / p) * (den * p) = -(c : ℝ) * den := by
        field_simp
      linarith
    have hhi : (num : ℝ) * p ≤ (c : ℝ) * den * p + (c : ℝ) * den := by
      have h1 := mul_le_mul_of_nonneg_right hle.2 hdp.le
      have h2 : ((num : ℝ) / den - c) * (den * p) = (num : ℝ) * p - (c : ℝ) * den * p := by
        field_simp
      have h3 : (c : ℝ) / p * (den * p) = (c : ℝ) * den := by
        field_simp
      linarith
    exact ⟨hden, by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  · rintro ⟨hden, hlo, hhi⟩
    refine ⟨hden, ?_⟩
    have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hdp : (0 : ℝ) < (den : ℝ) * p := mul_pos hdenR hpR
    have hloR : (c : ℝ) * den * p ≤ (num : ℝ) * p + (c : ℝ) * den := by exact_mod_cast hlo
    have hhiR : (num : ℝ) * p ≤ (c : ℝ) * den * p + (c : ℝ) * den := by exact_mod_cast hhi
    rw [abs_le]
    constructor
    · refine le_of_mul_le_mul_right ?_ hdp
      have h2 : ((num : ℝ) / den - c) * (den * p) = (num : ℝ) * p - (c : ℝ) * den * p := by
        field_simp
      have h3 : -((c : ℝ) / p) * (den * p) = -(c : ℝ) * den := by
        field_simp
      linarith
    · refine le_of_mul_le_mul_right ?_ hdp
      have h2 : ((num : ℝ) / den - c) * (den * p) = (num : ℝ) * p - (c : ℝ) * den * p := by
        field_simp
      have h3 : (c : ℝ) / p * (den * p) = (c : ℝ) * den := by
        field_simp
      linarith

/-- Executable Boolean test for `ApproxWithin c p x.1 x.2` (exact when `0 < p`). -/
def approxWithinBool (c p : ℕ) (x : ℕ × ℕ) : Bool :=
  decide (0 < x.2) && decide (c * x.2 * p ≤ x.1 * p + c * x.2) &&
    decide (x.1 * p ≤ c * x.2 * p + c * x.2)

theorem approxWithinBool_eq_true_iff {c p : ℕ} (hp : 0 < p) (x : ℕ × ℕ) :
    approxWithinBool c p x = true ↔ ApproxWithin c p x.1 x.2 := by
  simp only [approxWithinBool, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact (approxWithin_iff_nat hp).symm

/-- **Majority correctness of `approxRatMedian`**: if strictly more than half of the pairs in `xs`
satisfy `ApproxWithin c p`, then `approxRatMedian xs` also satisfies `ApproxWithin c p`. -/
theorem approxWithin_approxRatMedian {c p : ℕ} {xs : List (ℕ × ℕ)}
    (hgood : ∀ x ∈ xs, (approxWithinBool c p x = true → ApproxWithin c p x.1 x.2))
    (hmaj : xs.length < 2 * xs.countP (approxWithinBool c p)) :
    ApproxWithin c p (approxRatMedian xs).1 (approxRatMedian xs).2 := by
  set P := approxWithinBool c p
  set s := xs.mergeSort fun a b => decide (leRatPair a b)
  have hperm : s.Perm xs := by
    dsimp only [s]
    rw [List.mergeSort_decide_eq_insertionSort leRatPair (fun _ _ _ => leRatPair_trans)
      leRatPair_total xs]
    exact List.perm_insertionSort leRatPair xs
  have hslen : s.length = xs.length := hperm.length_eq
  have hcount : s.countP P = xs.countP P := hperm.countP_eq P
  have hpos : 0 < xs.length := by
    by_contra h0
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hnil] at hmaj
  set m := xs.length / 2
  have hm_lt : m < s.length := by omega
  have hsorted : s.Pairwise leRatPair := by
    have hp := List.pairwise_mergeSort (le := fun a b => decide (leRatPair a b))
      (fun a b c hab hbc => decide_eq_true (leRatPair_trans (of_decide_eq_true hab)
        (of_decide_eq_true hbc)))
      (fun a b => by rcases leRatPair_total a b with h | h <;> simp [h]) xs
    exact hp.imp of_decide_eq_true
  have hex_left : ∃ i : Fin s.length, i.1 ≤ m ∧ P s[i] = true := by
    by_contra! hall
    have hsplit : s = s.take (m + 1) ++ s.drop (m + 1) := (List.take_append_drop _ _).symm
    have hc_take : (s.take (m + 1)).countP P = 0 := by
      rw [List.countP_eq_zero]
      intro x hx
      obtain ⟨i, hi_lt, rfl⟩ := List.getElem_of_mem hx
      have hi_s : i < s.length := by
        simp only [List.length_take] at hi_lt
        omega
      have hi_m : i ≤ m := by
        simp only [List.length_take] at hi_lt
        omega
      rw [List.getElem_take]
      exact by simpa using hall ⟨i, hi_s⟩ hi_m
    have hc_drop : (s.drop (m + 1)).countP P ≤ s.length - (m + 1) :=
      List.countP_le_length.trans_eq List.length_drop
    have htot : s.countP P ≤ s.length - (m + 1) := by
      conv_lhs => rw [hsplit, List.countP_append, hc_take, zero_add]
      exact hc_drop
    omega
  have hex_right : ∃ k : Fin s.length, m ≤ k.1 ∧ P s[k] = true := by
    by_contra! hall
    have hsplit : s = s.take m ++ s.drop m := (List.take_append_drop _ _).symm
    have hc_drop : (s.drop m).countP P = 0 := by
      rw [List.countP_eq_zero]
      intro x hx
      obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem hx
      simp only [List.length_drop] at hj_lt
      have hj_s : m + j < s.length := by omega
      rw [List.getElem_drop]
      exact by simpa using hall ⟨m + j, hj_s⟩ (Nat.le_add_right m j)
    have hc_take : (s.take m).countP P ≤ m := by
      refine List.countP_le_length.trans ?_
      simp
    have htot : s.countP P ≤ m := by
      conv_lhs => rw [hsplit, List.countP_append, hc_drop, add_zero]
      exact hc_take
    omega
  obtain ⟨i, him, hPi⟩ := hex_left
  obtain ⟨k, hmk, hPk⟩ := hex_right
  have hi_app : ApproxWithin c p s[i].1 s[i].2 :=
    hgood s[i] (hperm.subset (List.getElem_mem i.2)) hPi
  have hk_app : ApproxWithin c p s[k].1 s[k].2 :=
    hgood s[k] (hperm.subset (List.getElem_mem k.2)) hPk
  have hle_im : leRatPair s[i] s[m] := by
    rcases eq_or_lt_of_le him with heq | hlt
    · have : s[i] = s[m] := by simp [heq]
      rw [this]; exact leRatPair_refl _
    · exact List.pairwise_iff_getElem.1 hsorted i.1 m i.2 hm_lt hlt
  have hle_mk : leRatPair s[m] s[k] := by
    rcases eq_or_lt_of_le hmk with heq | hlt
    · have : s[m] = s[k] := by simp [← heq]
      rw [this]; exact leRatPair_refl _
    · exact List.pairwise_iff_getElem.1 hsorted m k.1 hm_lt k.2 hlt
  have hmed_eq : approxRatMedian xs = normRatPair s[m] := by
    simp [approxRatMedian, s, m, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_lt]
  rw [hmed_eq]
  have hpos_m : 0 < (normRatPair s[m]).2 := pos_snd_normRatPair s[m]
  have hle_im' : leRatPair s[i] (normRatPair s[m]) := by
    simpa [leRatPair, normRatPair] using hle_im
  have hle_mk' : leRatPair (normRatPair s[m]) s[k] := by
    simpa [leRatPair, normRatPair] using hle_mk
  have hdiv_lo : (s[i].1 : ℝ) / s[i].2 ≤ ((normRatPair s[m]).1 : ℝ) / (normRatPair s[m]).2 :=
    (leRatPair_iff_div_le hi_app.1 hpos_m).1 hle_im'
  have hdiv_hi : ((normRatPair s[m]).1 : ℝ) / (normRatPair s[m]).2 ≤ (s[k].1 : ℝ) / s[k].2 :=
    (leRatPair_iff_div_le hpos_m hk_app.1).1 hle_mk'
  refine ⟨hpos_m, ?_⟩
  rw [abs_le]
  have hi_abs := abs_le.1 hi_app.2
  have hk_abs := abs_le.1 hk_app.2
  constructor <;> linarith

end RationalMedian

section Schemes

variable {α β γ : Type}

/-- A deterministic **fully polynomial-time approximation scheme** (`FPTAS`) for a promise counting
problem `(P, f)` on instances encoded by `enc`. -/
@[expose] def IsPromiseFPTAS (enc : α ↪ List Bool) (P : Set α) (f : α → ℕ)
    (A : α → ℕ → ℕ × ℕ) : Prop :=
  ComputableInPolyTime (Function.uncurry A) (encPair enc encUnary) (encPair encNat encNat) ∧
    ∀ x ∈ P, ∀ p, 0 < p → ApproxWithin (f x) p (A x p).1 (A x p).2

/-- The counting functions admitting a deterministic `FPTAS` on the promise `P`. -/
@[expose] def PromiseFPTAS (enc : α ↪ List Bool) (P : Set α) : Set (α → ℕ) :=
  {f | ∃ A, IsPromiseFPTAS enc P f A}

/-- Total counting functions admitting a deterministic `FPTAS`. -/
@[expose] def FPTAS (enc : α ↪ List Bool) : Set (α → ℕ) :=
  PromiseFPTAS enc Set.univ

/-- A **fully polynomial randomized approximation scheme** (`FPRAS`) for a promise counting problem
`(P, f)` on instances encoded by `enc`, matching `Cslib.Complexity.IsFPRAS` when `P = Set.univ`. -/
@[expose] def IsPromiseFPRAS (enc : α ↪ List Bool) (P : Set α) (f : α → ℕ)
    (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) : Prop :=
  IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (A x)) ∧
    ∀ x ∈ P, ∀ p t, 0 < p → 1 - (1 / 2 : ℝ) ^ t ≤
      ((ProbComp.eval (A x p t)).toOuterMeasure
        {out | ApproxWithin (f x) p out.1 out.2}).toReal

/-- The counting functions admitting an `FPRAS` on the promise `P`. -/
@[expose] def PromiseFPRAS (enc : α ↪ List Bool) (P : Set α) : Set (α → ℕ) :=
  {f | ∃ A, IsPromiseFPRAS enc P f A}

/-- On `Set.univ`, `IsPromiseFPRAS` coincides with `Cslib.Complexity.IsFPRAS`. -/
theorem isPromiseFPRAS_univ_iff {enc : α ↪ List Bool} {f : α → ℕ}
    {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)} :
    IsPromiseFPRAS enc Set.univ f A ↔ Cslib.Complexity.IsFPRAS enc f A := by
  simp [IsPromiseFPRAS, Cslib.Complexity.IsFPRAS]

/-- On `Set.univ`, `PromiseFPRAS` coincides with `Cslib.Complexity.FPRAS`. -/
theorem promiseFPRAS_univ_eq (enc : α ↪ List Bool) :
    PromiseFPRAS enc Set.univ = Cslib.Complexity.FPRAS enc := by
  ext f
  simp [PromiseFPRAS, Cslib.Complexity.FPRAS, isPromiseFPRAS_univ_iff]

/-- Every deterministic `PromiseFPTAS` is a `PromiseFPRAS`. -/
theorem promiseFPTAS_subset_promiseFPRAS {enc : α ↪ List Bool} {P : Set α} :
    PromiseFPTAS enc P ⊆ PromiseFPRAS enc P := by
  rintro f ⟨A, hpoly, happrox⟩
  refine ⟨fun x p _ => pure (A x p), ?_, fun x hx p t hp => ?_⟩
  · have hprep : ComputableInPolyTime
        (fun xpt : α × (ℕ × ℕ) => (xpt.1, xpt.2.1))
        (encPair enc (encPair encUnary encUnary)) (encPair enc encUnary) :=
      (ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.fst encUnary encUnary).comp (ComputableInPolyTime.snd _ _))
    exact (hpoly.comp hprep).isPPTOn
  · have hmem : A x p ∈ {out : ℕ × ℕ | ApproxWithin (f x) p out.1 out.2} := happrox x hx p hp
    rw [ProbComp.eval_pure, _root_.PMF.toOuterMeasure_pure_apply]
    simp [hmem]

/-- **Constant-confidence (`3 / 4`) FPRAS** on a promise `P`: a strict `PPT` algorithm `Z x p`
taking instance `x` and unary `p` (`ε = 1 / p`) that outputs `(num, den)` within relative error
`1 / p` of `f x` with probability at least `3 / 4` whenever `x ∈ P` and `0 < p`. -/
@[expose] def IsBoundedErrorFPRAS (enc : α ↪ List Bool) (P : Set α) (f : α → ℕ)
    (Z : α → ℕ → ProbComp (ℕ × ℕ)) : Prop :=
  IsPPTOn (encPair enc encUnary) (encPair encNat encNat) (Function.uncurry Z) ∧
    ∀ x ∈ P, ∀ p, 0 < p → 3 / 4 ≤
      ((ProbComp.eval (Z x p)).toOuterMeasure
        {out | ApproxWithin (f x) p out.1 out.2}).toReal

/-- **Real-parameter `(1 ± ε)` guarantee**: for every `x ∈ P` and `0 < ε` (in particular
`0 < ε ≤ 1`), running `Z` at `p = ⌈ε⁻¹⌉₊` outputs a rational `num / den` (`0 < den`) satisfying
`(1 - ε) * f x ≤ num / den ≤ (1 + ε) * f x` with probability at least `3 / 4`. -/
theorem IsBoundedErrorFPRAS.approx_real {enc : α ↪ List Bool} {P : Set α} {f : α → ℕ}
    {Z : α → ℕ → ProbComp (ℕ × ℕ)} (hZ : IsBoundedErrorFPRAS enc P f Z)
    {x : α} (hx : x ∈ P) {ε : ℝ} (hε : 0 < ε) :
    3 / 4 ≤ ((ProbComp.eval (Z x ⌈ε⁻¹⌉₊)).toOuterMeasure
      {out | 0 < out.2 ∧ (1 - ε) * (f x : ℝ) ≤ (out.1 : ℝ) / out.2 ∧
        (out.1 : ℝ) / out.2 ≤ (1 + ε) * (f x : ℝ)}).toReal := by
  have hp : 0 < ⌈ε⁻¹⌉₊ := Nat.ceil_pos.2 (inv_pos.2 hε)
  have hinv : (1 : ℝ) / ⌈ε⁻¹⌉₊ ≤ ε := by
    rw [div_le_iff₀ (by exact_mod_cast hp), ← div_le_iff₀' hε, one_div]
    exact Nat.le_ceil _
  refine (hZ.2 x hx _ hp).trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
  rintro ⟨num, den⟩ ⟨hden, hle⟩
  have hbd : (f x : ℝ) / ⌈ε⁻¹⌉₊ ≤ ε * (f x : ℝ) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg _)
  rw [abs_le] at hle
  exact ⟨hden, by linarith, by linarith⟩

/-- **Median confidence amplification for `PromiseFPRAS`**
: taking the median `approxRatMedian` of `12 * (t + 1)` independent runs boosts success
probability `3 / 4` to `1 - (1 / 2) ^ (t + 1) ≥ 1 - (1 / 2) ^ t`. Consequently, `(P, f)` admits a
`PromiseFPRAS` if and only if it admits a `(3 / 4)`-confidence `IsBoundedErrorFPRAS`.
-/
theorem mem_PromiseFPRAS_iff_exists_isBoundedErrorFPRAS {enc : α ↪ List Bool} {P : Set α}
    {f : α → ℕ} :
    f ∈ PromiseFPRAS enc P ↔ ∃ Z, IsBoundedErrorFPRAS enc P f Z := by
  constructor
  · rintro ⟨A, hA_ppt, hA_prob⟩
    refine ⟨fun x p => A x p 2, ?_, fun x hx p hp => ?_⟩
    · have hprep : ComputableInPolyTime
          (fun xp : α × ℕ => (xp.1, (xp.2, (2 : ℕ))))
          (encPair enc encUnary) (encPair enc (encPair encUnary encUnary)) := by
        fun_prop
      exact hA_ppt.preprocess hprep
    · have h2 := hA_prob x hx p 2 hp
      norm_num at h2 ⊢
      exact h2
  · rintro ⟨Z, hZ_ppt, hZ_prob⟩
    let A : α → ℕ → ℕ → ProbComp (ℕ × ℕ) := fun x p t =>
      approxRatMedian <$> OracleComp.replicate (12 * (t + 1)) (Z x p)
    have hZ_lift : IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
        (fun xpt : α × (ℕ × ℕ) => Z xpt.1 xpt.2.1) :=
      hZ_ppt.preprocess
        ((ComputableInPolyTime.fst _ _).prod
          ((ComputableInPolyTime.fst encUnary encUnary).comp (ComputableInPolyTime.snd _ _)))
    have hcount : ComputableInPolyTime
        (fun xpt : α × (ℕ × ℕ) => 12 * (xpt.2.2 + 1))
        (encPair enc (encPair encUnary encUnary)) encUnary := by
      fun_prop
    have hA_ppt : IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
        (Function.uncurry fun x => Function.uncurry (A x)) := by
      have hrep := hZ_lift.replicate hcount
      exact (hrep.map computableInPolyTime_approxRatMedian).congr fun ⟨x, p, t⟩ => rfl
    refine ⟨A, hA_ppt, fun x hx p t hp => ?_⟩
    classical
    obtain ⟨c, d, evalZ, _, hlaw⟩ := hZ_ppt.exists_seeded_evaluator
    set W := c * ((encPair enc encUnary (x, p)).length + 1) ^ d
    set r := 6 * (t + 1)
    have h12 : 12 * (t + 1) = 2 * r := by dsimp [r]; ring
    have hlaw_xp : ProbComp.eval (Z x p) =
        (BitString.uniformList W).map (evalZ (x, p)) := hlaw (x, p)
    have hgood_run : 2 * 2 ^ W ≤
        3 * (Finset.univ.filter fun s : BitString W =>
          approxWithinBool (f x) p (evalZ (x, p) (List.ofFn s)) = true).card := by
      have h34 := hZ_prob x hx p hp
      rw [hlaw_xp, BitString.toOuterMeasure_map_uniformList_toReal,
        le_div_iff₀ (by positivity)] at h34
      have heq_card :
          (Finset.univ.filter fun s : BitString W =>
            evalZ (x, p) (List.ofFn s) ∈ {out : ℕ × ℕ | ApproxWithin (f x) p out.1 out.2}).card =
          (Finset.univ.filter fun s : BitString W =>
            approxWithinBool (f x) p (evalZ (x, p) (List.ofFn s)) = true).card := by
        congr 1
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        exact (approxWithinBool_eq_true_iff hp _).symm
      rw [heq_card] at h34
      have hreal : (2 : ℝ) * (2 : ℝ) ^ W ≤
          3 * ((Finset.univ.filter fun s : BitString W =>
            approxWithinBool (f x) p (evalZ (x, p) (List.ofFn s)) = true).card : ℝ) := by
        linarith [show (0 : ℝ) ≤ 2 ^ W by positivity]
      exact_mod_cast hreal
    have hchernoff :
        2 ^ (t + 1) *
          (Finset.univ.filter fun tape : BitString (2 * r * W) =>
            (Finset.univ.filter fun i : Fin (2 * r) =>
              approxWithinBool (f x) p (evalZ (x, p) (List.ofFn (BitString.block tape i))) =
                true).card ≤ r).card ≤
          2 ^ (2 * r * W) :=
      BitString.two_pow_mul_card_filter_card_filter_block_le
        (m := W) (e := t + 1) (R := r) rfl
        (fun s => approxWithinBool (f x) p (evalZ (x, p) (List.ofFn s)) = true) hgood_run
    have hrep_law :
        ProbComp.eval (A x p t) =
          (BitString.uniformList (2 * r * W)).map
            (fun tape => approxRatMedian
              ((BitString.listRows (2 * r) W tape).map (evalZ (x, p)))) := by
      dsimp only [A]
      rw [h12, ProbComp.eval_map,
        ProbComp.eval_replicate_of_uniformList (2 * r) W (Z x p) (evalZ (x, p)) hlaw_xp,
        _root_.PMF.map_comp]
      rfl
    rw [hrep_law, BitString.toOuterMeasure_map_uniformList_toReal]
    set Sgood : Finset (BitString (2 * r * W)) :=
      Finset.univ.filter fun tape : BitString (2 * r * W) =>
        approxRatMedian ((BitString.listRows (2 * r) W (List.ofFn tape)).map (evalZ (x, p))) ∈
          {out : ℕ × ℕ | ApproxWithin (f x) p out.1 out.2}
    let Sbad : Finset (BitString (2 * r * W)) :=
      Finset.univ.filter fun tape : BitString (2 * r * W) =>
        (Finset.univ.filter fun i : Fin (2 * r) =>
          approxWithinBool (f x) p (evalZ (x, p) (List.ofFn (BitString.block tape i))) =
            true).card ≤ r
    have hcompl_sub : Sgoodᶜ ⊆ Sbad := by
      intro tape htape
      simp only [Finset.mem_compl, Sgood, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at htape
      simp only [Sbad, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hgt
      push Not at hgt
      set samples := (BitString.listRows (2 * r) W (List.ofFn tape)).map (evalZ (x, p))
      have hrows_eq : samples =
          List.ofFn (fun i : Fin (2 * r) => evalZ (x, p) (List.ofFn (BitString.block tape i))) := by
        simp [samples, BitString.listRows_ofFn, List.map_ofFn, Function.comp_def]
      have hlen_s : samples.length = 2 * r := by simp only [hrows_eq, List.length_ofFn]
      have hcnt_s : samples.countP (approxWithinBool (f x) p) =
          (Finset.univ.filter fun i : Fin (2 * r) =>
            approxWithinBool (f x) p (evalZ (x, p) (List.ofFn (BitString.block tape i))) =
              true).card := by
        rw [hrows_eq, List.countP_ofFn]
      refine htape (approxWithin_approxRatMedian
        (fun y _ hy => (approxWithinBool_eq_true_iff hp y).1 hy) ?_)
      rw [hlen_s, hcnt_s]
      omega
    have hcard_compl : Sgood.card + Sgoodᶜ.card = 2 ^ (2 * r * W) := by
      rw [Finset.card_add_card_compl, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hbad_le : 2 ^ (t + 1) * Sgoodᶜ.card ≤ 2 ^ (2 * r * W) :=
      (Nat.mul_le_mul_left _ (Finset.card_le_card hcompl_sub)).trans hchernoff
    rw [le_div_iff₀ (by positivity)]
    have hbadR : (2 : ℝ) ^ (t + 1) * (Sgoodᶜ.card : ℝ) ≤ (2 : ℝ) ^ (2 * r * W) := by
      exact_mod_cast hbad_le
    have hsumR : (Sgood.card : ℝ) + (Sgoodᶜ.card : ℝ) = (2 : ℝ) ^ (2 * r * W) := by
      exact_mod_cast hcard_compl
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (t + 1) := by positivity
    have hinv_le : (1 : ℝ) / (2 : ℝ) ^ (t + 1) ≤ (1 / 2 : ℝ) ^ t := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (Nat.le_succ t))
    have hbad_frac : (Sgoodᶜ.card : ℝ) ≤ (1 / 2 : ℝ) ^ t * (2 : ℝ) ^ (2 * r * W) := by
      have h1 : (Sgoodᶜ.card : ℝ) ≤ (1 / (2 : ℝ) ^ (t + 1)) * (2 : ℝ) ^ (2 * r * W) := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hpow_pos, mul_comm]
        exact hbadR
      exact h1.trans (mul_le_mul_of_nonneg_right hinv_le (by positivity))
    linarith

end Schemes

section Reductions

variable {α β γ : Type}

/-- **Promise parsimonious reduction** from `(PA, f)` to `(PB, g)`: a polynomial-time computable
map `r : α → β` sending promises to promises and preserving exact counts on `PA`. -/
@[expose] def PromiseParsimoniousReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (PA : Set α) (PB : Set β) (f : α → ℕ) (g : β → ℕ) : Prop :=
  ∃ r : α → β, ComputableInPolyTime r encA encB ∧ ∀ a ∈ PA, r a ∈ PB ∧ f a = g (r a)

theorem promiseParsimoniousReducible_univ_iff {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → ℕ} {g : β → ℕ} :
    PromiseParsimoniousReducible encA encB Set.univ Set.univ f g ↔
      ParsimoniousReducible encA encB f g := by
  simp [PromiseParsimoniousReducible, ParsimoniousReducible]

@[refl]
theorem PromiseParsimoniousReducible.refl (encA : α ↪ List Bool) (PA : Set α) (f : α → ℕ) :
    PromiseParsimoniousReducible encA encA PA PA f f :=
  ⟨id, ComputableInPolyTime.id', fun _ ha => ⟨ha, rfl⟩⟩

@[trans]
theorem PromiseParsimoniousReducible.trans {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {PA : Set α} {PB : Set β} {PC : Set γ}
    {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}
    (hfg : PromiseParsimoniousReducible encA encB PA PB f g)
    (hgh : PromiseParsimoniousReducible encB encC PB PC g h) :
    PromiseParsimoniousReducible encA encC PA PC f h := by
  obtain ⟨r, hr, hfg⟩ := hfg
  obtain ⟨s, hs, hgh⟩ := hgh
  refine ⟨s ∘ r, hs.comp hr, fun a ha => ?_⟩
  obtain ⟨hra, heq₁⟩ := hfg a ha
  obtain ⟨hsra, heq₂⟩ := hgh (r a) hra
  exact ⟨hsra, heq₁.trans heq₂⟩

/-- `PromiseFPTAS` is closed downwards under `PromiseParsimoniousReducible`. -/
theorem PromiseParsimoniousReducible.mem_PromiseFPTAS {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {PA : Set α} {PB : Set β} {f : α → ℕ} {g : β → ℕ}
    (hred : PromiseParsimoniousReducible encA encB PA PB f g)
    (hg : g ∈ PromiseFPTAS encB PB) :
    f ∈ PromiseFPTAS encA PA := by
  obtain ⟨r, hr, hfg⟩ := hred
  obtain ⟨A, hA_poly, hA_app⟩ := hg
  refine ⟨fun a p => A (r a) p, ?_, fun a ha p hp => ?_⟩
  · have hprep : ComputableInPolyTime (fun ap : α × ℕ => (r ap.1, ap.2))
        (encPair encA encUnary) (encPair encB encUnary) :=
      (hr.comp (ComputableInPolyTime.fst encA encUnary)).prod
        (ComputableInPolyTime.snd encA encUnary)
    exact hA_poly.comp hprep
  · obtain ⟨hra, heq⟩ := hfg a ha
    rw [heq]
    exact hA_app (r a) hra p hp

/-- `PromiseFPRAS` is closed downwards under `PromiseParsimoniousReducible`. -/
theorem PromiseParsimoniousReducible.mem_PromiseFPRAS {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {PA : Set α} {PB : Set β} {f : α → ℕ} {g : β → ℕ}
    (hred : PromiseParsimoniousReducible encA encB PA PB f g)
    (hg : g ∈ PromiseFPRAS encB PB) :
    f ∈ PromiseFPRAS encA PA := by
  obtain ⟨r, hr, hfg⟩ := hred
  obtain ⟨A, hA_ppt, hA_prob⟩ := hg
  refine ⟨fun a p t => A (r a) p t, ?_, fun a ha p t hp => ?_⟩
  · have hprep : ComputableInPolyTime
        (fun apt : α × (ℕ × ℕ) => (r apt.1, apt.2))
        (encPair encA (encPair encUnary encUnary))
        (encPair encB (encPair encUnary encUnary)) :=
      (hr.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)
    exact hA_ppt.preprocess hprep
  · obtain ⟨hra, heq⟩ := hfg a ha
    rw [heq]
    exact hA_prob (r a) hra p t hp

/-- A deterministic word oracle `O : List Bool → List Bool` is a **`B`-bounded valid oracle** for
`(PB, g)` if on every encoded query `encPair encB encUnary (y, q)` with `y ∈ PB` and `0 < q`,
`O` returns an encoded pair `(num, den)` within relative error `1 / q` of `g y` of bit-length at
most `B.eval |(y, q)|`. -/
@[expose] def IsBoundedValidOracle (encB : β ↪ List Bool) (PB : Set β) (g : β → ℕ)
    (B : Polynomial ℕ) (O : List Bool → List Bool) : Prop :=
  ∀ y ∈ PB, ∀ q, 0 < q →
    ∃ num den : ℕ,
      O (encPair encB encUnary (y, q)) = encPair encNat encNat (num, den) ∧
      ApproxWithin (g y) q num den ∧
      (encPair encNat encNat (num, den)).length ≤ B.eval (encPair encB encUnary (y, q)).length

/-- **Approximation-preserving (`AP`) reduction** from `(PA, f)` to `(PB, g)`
: for every polynomial reply-length bound `B`, there
is a strict oracle `PPT` machine `M` taking `(x, p)` (`p` in unary for tolerance `ε = 1 / p`) such
that whenever `x ∈ PA` and `0 < p`:
1. Every oracle query made by `M (x, p)` is of the form `encPair encB encUnary (y, q)` with
   `y ∈ PB` and `0 < q`;
2. Against every deterministic `B`-bounded valid `(PB, g)`-oracle `O`, `M (x, p)` outputs an
   estimate satisfying `ApproxWithin (f x) p` with probability at least `3 / 4`.
-/
@[expose] def PromiseAPReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (PA : Set α) (PB : Set β) (f : α → ℕ) (g : β → ℕ) : Prop :=
  ∀ B : Polynomial ℕ,
    ∃ M : α × ℕ → WordOracleComp Unit (ℕ × ℕ),
      IsOraclePPTOn (encPair encA encUnary) (encPair encNat encNat) M ∧
      ∀ x ∈ PA, ∀ p, 0 < p →
        ProbOracleComp.QueriesSatisfy
          (fun req => ∃ y ∈ PB, ∃ q > 0, req.2 = encPair encB encUnary (y, q))
          (M (x, p)) ∧
        ∀ O : List Bool → List Bool, IsBoundedValidOracle encB PB g B O →
          3 / 4 ≤ (((ProbOracleComp.runWith (fun req _ => _root_.PMF.pure (O req.2, ()))
            (M (x, p)) ()).map Prod.fst).toOuterMeasure
              {out | ApproxWithin (f x) p out.1 out.2}).toReal

/-- Total **approximation-preserving (`AP`) reduction** (`PromiseAPReducible` on `Set.univ`). -/
@[expose] def APReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (f : α → ℕ)
    (g : β → ℕ) : Prop :=
  PromiseAPReducible encA encB Set.univ Set.univ f g

/-- A promise counting problem `(PB, g)` is **`#P`-hard under `AP`-reductions** if every counting
problem `f ∈ #P` (under any injective encoding `encA`) `AP`-reduces to `(PB, g)`. -/
@[expose] def SharpPHardPromiseAP (encB : β ↪ List Bool) (PB : Set β) (g : β → ℕ) : Prop :=
  ∀ {α : Type} (encA : α ↪ List Bool) (f : α → ℕ),
    f ∈ SharpP encA → PromiseAPReducible encA encB Set.univ PB f g

/-- A total counting problem `g` is **`#P`-hard under `AP`-reductions** if every `f ∈ #P`
`AP`-reduces to `g`. -/
@[expose] def SharpPHardAP (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  SharpPHardPromiseAP encB Set.univ g

/-- **Every parsimonious reduction is an `AP`-reduction**: given `r : α → β` with `r x ∈ PB` and
`f x = g (r x)` for `x ∈ PA`, forward `(r x, p)` directly to the `(PB, g)`-oracle (guarding `p = 0`
without calling the oracle) and decode the returned `(num, den)` pair. -/
theorem PromiseParsimoniousReducible.promiseAPReducible
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {PA : Set α} {PB : Set β}
    {f : α → ℕ} {g : β → ℕ}
    (hred : PromiseParsimoniousReducible encA encB PA PB f g) :
    PromiseAPReducible encA encB PA PB f g := by
  obtain ⟨r, hr, hfg⟩ := hred
  intro B
  let Dpair := Decoder.pair Decoder.nat Decoder.nat
  let reqFn (xp : α × ℕ) : List Bool := encPair encB encUnary (r xp.1, xp.2)
  let limFn (xp : α × ℕ) : ℕ := B.eval (reqFn xp).length
  let callBranch (xp : α × ℕ) : WordOracleComp Unit (ℕ × ℕ) :=
    Dpair.decode <$> (List.take (limFn xp) <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), reqFn xp))
  let M (xp : α × ℕ) : WordOracleComp Unit (ℕ × ℕ) :=
    if xp.2 == 0 then pure (0, 1) else callBranch xp
  have hreq : ComputableInPolyTime reqFn (encPair encA encUnary) encBits := by
    have hpair : ComputableInPolyTime (fun xp : α × ℕ => (r xp.1, xp.2))
        (encPair encA encUnary) (encPair encB encUnary) :=
      (hr.comp (ComputableInPolyTime.fst encA encUnary)).prod
        (ComputableInPolyTime.snd encA encUnary)
    exact (ComputableInPolyTime.of_eq fun _ => rfl).comp hpair
  have hlim : ComputableInPolyTime limFn (encPair encA encUnary) encUnary :=
    (ComputableInPolyTime.unary_eval B).comp
      (ComputableInPolyTime.length_bits.comp hreq)
  have hcall_ppt : IsOraclePPTOn (encPair encA encUnary) (encPair encNat encNat) callBranch :=
    (IsOraclePPTOn.query_take () hreq hlim).map Dpair.computableInPolyTime
  have hpzero : ComputableInPolyTime (fun xp : α × ℕ => xp.2 == 0)
      (encPair encA encUnary) encBool :=
    ComputableInPolyTime.unary_beq (ComputableInPolyTime.snd encA encUnary)
      (ComputableInPolyTime.const 0)
  have hM_ppt : IsOraclePPTOn (encPair encA encUnary) (encPair encNat encNat) M :=
    IsOraclePPTOn.cond hpzero ((ComputableInPolyTime.const (0, 1)).isOraclePPTOn) hcall_ppt
  refine ⟨M, hM_ppt, fun x hx p hp => ⟨?_, fun O hO => ?_⟩⟩
  · have hp0 : (p == 0) = false := beq_eq_false_iff_ne.2 hp.ne'
    simp only [M, hp0, Bool.false_eq_true, ↓reduceIte]
    dsimp only [callBranch, ProbOracleComp.QueriesSatisfy]
    rw [Functor.map_map, OracleComp.queriesSatisfy_map_iff]
    exact ProbOracleComp.QueriesSatisfy.query ⟨r x, (hfg x hx).1, p, hp, rfl⟩
  · have hp0 : (p == 0) = false := beq_eq_false_iff_ne.2 hp.ne'
    obtain ⟨hrx, heq⟩ := hfg x hx
    obtain ⟨num, den, hO_eq, happrox, hlen⟩ := hO (r x) hrx p hp
    have htake : (O (reqFn (x, p))).take (limFn (x, p)) = encPair encNat encNat (num, den) := by
      dsimp only [reqFn, limFn] at hlen ⊢
      rw [hO_eq]
      exact List.take_of_length_le hlen
    have hrun :
        (ProbOracleComp.runWith (fun req _ => _root_.PMF.pure (O req.2, ())) (M (x, p)) ()).map
          Prod.fst = _root_.PMF.pure (num, den) := by
      simp only [M, hp0, Bool.false_eq_true, ↓reduceIte]
      dsimp only [callBranch]
      rw [Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
      simp only [Prod.map_apply, _root_.PMF.pure_map, htake, Dpair.decode_enc]
    rw [hrun, _root_.PMF.toOuterMeasure_pure_apply]
    rw [heq]
    simp only [Set.mem_ofPred_eq, happrox, ↓reduceIte, ENNReal.toReal_one]
    norm_num

/-- Every `PromiseAPReducible` relation is reflexive. -/
@[refl]
theorem PromiseAPReducible.refl (encA : α ↪ List Bool) (PA : Set α) (f : α → ℕ) :
    PromiseAPReducible encA encA PA PA f f :=
  (PromiseParsimoniousReducible.refl encA PA f).promiseAPReducible

theorem ParsimoniousReducible.apReducible {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → ℕ} {g : β → ℕ} (h : ParsimoniousReducible encA encB f g) :
    APReducible encA encB f g :=
  (promiseParsimoniousReducible_univ_iff.2 h).promiseAPReducible

end Reductions

end Cslib.Complexity
