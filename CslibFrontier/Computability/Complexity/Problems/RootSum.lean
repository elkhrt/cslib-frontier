/-
Copyright (c) 2026 Cslib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cslib Contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD

/-!
# The $p$-ROOT-SUM and $(p / q)$-ROOT-SUM Decision Problems and Complexity Equivalence

`PRootSum p` (`p`-ROOT-SUM, generalizing `2`-ROOT-SUM / Square-Root-Sum) asks whether a list of
binary-encoded nonnegative integers `a_1, …, a_n` and a binary-encoded threshold `τ` satisfy
`∑_{i=1}^n a_i^{1/p} ≥ τ`. More generally, for `r : ℚ`, `RootSum r` tests
`∑_{i=1}^n a_i^{1/r} ≥ τ`, so `PQRootSum p q = RootSum (p / q)` tests `∑_{i=1}^n a_i^{q/p} ≥ τ`.

## Main definitions

* `CslibFrontier.Complexity.RootSumInstance`, `CslibFrontier.Complexity.encRootSum`: binary-encoded
  root-sum instances.
* `CslibFrontier.Complexity.RootSum`, `CslibFrontier.Complexity.PRootSum`,
  `CslibFrontier.Complexity.PQRootSum`, `CslibFrontier.Complexity.PRootSumClass`.
* `CslibFrontier.Complexity.nthRootFloor`, `CslibFrontier.Complexity.greedyPowers`: polynomial-time
  integer `p`-th root floor and greedy `p`-th power decomposition (`O(log log n)` summands).

## Main results

* `CslibFrontier.Complexity.polyTimeReducible_RootSum_mul`: `$r$-ROOT-SUM` reduces in polynomial
  time to `$(k r)$-ROOT-SUM` for `k ≥ 1`.
* `CslibFrontier.Complexity.computableInPolyTime_greedyPowers`,
  `CslibFrontier.Complexity.greedyPowers_sum_eq`,
  `CslibFrontier.Complexity.exists_greedyPowers_length_le_log_log`: polynomial-time greedy sum of
  `p`-th powers with `O(log log n)` terms.
* `CslibFrontier.Complexity.polyTimeReducible_PRootSum_PQRootSum`,
  `CslibFrontier.Complexity.polyTimeEquivalent_PRootSum_PQRootSum`: polynomial-time equivalence of
  `PRootSum p` and `PQRootSum p q` when `Nat.Coprime p q`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Finset Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- An instance of the `$r$-ROOT-SUM` decision problem: candidate nonnegative integers `numbers`
and target threshold `threshold`, all encoded in binary. -/
@[ext]
structure RootSumInstance where
  /-- Nonnegative integer radicands `a_1, …, a_n`. -/
  numbers : List ℕ
  /-- Nonnegative integer threshold `τ`. -/
  threshold : ℕ
  deriving DecidableEq, Repr

/-- Framed binary encoding of `RootSumInstance`. -/
enc_structure encRootSum : RootSumInstance where
  numbers : (encList encNat), threshold : encNat

attribute [fun_prop] encRootSum_numbers_polyTime encRootSum_threshold_polyTime
  encRootSum_mk_polyTime

/-- Real power sum `∑_{a ∈ nums} (a : ℝ) ^ exp`. -/
@[expose]
noncomputable def realPowListSum (exp : ℝ) (nums : List ℕ) : ℝ :=
  (nums.map fun a : ℕ ↦ (a : ℝ) ^ exp).sum

theorem realPowListSum_cons (exp : ℝ) (a : ℕ) (l : List ℕ) :
    realPowListSum exp (a :: l) = (a : ℝ) ^ exp + realPowListSum exp l := by
  simp [realPowListSum]

theorem realPowListSum_append (exp : ℝ) (l₁ l₂ : List ℕ) :
    realPowListSum exp (l₁ ++ l₂) = realPowListSum exp l₁ + realPowListSum exp l₂ := by
  simp [realPowListSum, List.map_append, List.sum_append]

theorem realPowListSum_filter_pos {exp : ℝ} (hexp : exp ≠ 0) (nums : List ℕ) :
    realPowListSum exp (nums.filter fun a ↦ decide (0 < a)) = realPowListSum exp nums := by
  induction nums with
  | nil => rfl
  | cons a l ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Nat.lt_irrefl, decide_false, List.filter_cons_of_neg, Bool.false_eq_true,
        not_false_eq_true, realPowListSum_cons, Nat.cast_zero, Real.zero_rpow hexp, zero_add, ih]
    · simp only [ha, decide_true, List.filter_cons_of_pos, realPowListSum_cons, ih]

/-- General rational `$r$-ROOT-SUM` language: `∑_{a ∈ x.numbers} a^{1/r} ≥ x.threshold`. -/
@[expose]
noncomputable def RootSum (r : ℚ) : Set RootSumInstance :=
  {x | (x.threshold : ℝ) ≤ realPowListSum (1 / (r : ℝ)) x.numbers}

/-- The `$p$-ROOT-SUM` decision problem: `∑_{i=1}^n a_i^{1/p} ≥ τ`. -/
@[expose]
noncomputable def PRootSum (p : ℕ) : Set RootSumInstance :=
  RootSum (p : ℚ)

/-- The `$(p / q)$-ROOT-SUM` decision problem: `∑_{i=1}^n a_i^{q/p} ≥ τ`. -/
@[expose]
noncomputable def PQRootSum (p q : ℕ) : Set RootSumInstance :=
  RootSum ((p : ℚ) / (q : ℚ))

theorem mem_PRootSum_iff {p : ℕ} {x : RootSumInstance} :
    x ∈ PRootSum p ↔ (x.threshold : ℝ) ≤ realPowListSum (1 / (p : ℝ)) x.numbers := by
  simp [PRootSum, RootSum]

theorem mem_PQRootSum_iff {p q : ℕ} {x : RootSumInstance} :
    x ∈ PQRootSum p q ↔ (x.threshold : ℝ) ≤ realPowListSum ((q : ℝ) / (p : ℝ)) x.numbers := by
  simp [PQRootSum, RootSum]

/-- The `$p$-ROOT-SUM` complexity class: problems polynomial-time many-one reducible to
`PRootSum p`. -/
@[expose]
def PRootSumClass (p : ℕ) {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | PolyTimeReducible enc encRootSum L (PRootSum p)}

/-- Raising every input integer to the constant power `k`. -/
@[expose]
def kpReduction (k : ℕ) (x : RootSumInstance) : RootSumInstance where
  numbers := x.numbers.map (· ^ k)
  threshold := x.threshold

theorem computableInPolyTime_kpReduction (k : ℕ) :
    ComputableInPolyTime (kpReduction k) encRootSum encRootSum := by
  have hpow : ComputableInPolyTime (fun a : ℕ ↦ a ^ k) encNat encNat :=
    binary_pow' id' (const k)
  have hnums : ComputableInPolyTime (fun x : RootSumInstance ↦ x.numbers.map (· ^ k))
      encRootSum (encList encNat) :=
    mapWith (hpow.comp (snd encBool encNat)) (const true) (encRootSum_numbers_polyTime id')
  exact encRootSum_mk_polyTime hnums (encRootSum_threshold_polyTime id')

theorem kpReduction_mem_iff {r : ℚ} {k : ℕ} (hk : 1 ≤ k) (x : RootSumInstance) :
    x ∈ RootSum r ↔ kpReduction k x ∈ RootSum ((k : ℚ) * r) := by
  simp only [RootSum, Set.mem_ofPred_eq, kpReduction, realPowListSum, List.map_map,
    Function.comp_def]
  have hk_ne : (k : ℝ) ≠ 0 := by positivity
  have hterm : (fun a : ℕ ↦ ((a ^ k : ℕ) : ℝ) ^ (1 / (((k : ℚ) * r : ℚ) : ℝ))) =
      fun a : ℕ ↦ (a : ℝ) ^ (1 / (r : ℝ)) := by
    funext a
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a),
      Rat.cast_mul, Rat.cast_natCast]
    congr 1
    by_cases hr : (r : ℝ) = 0
    · simp [hr]
    · field_simp [hk_ne, hr]
  rw [hterm]

/-- `$r$-ROOT-SUM` reduces in polynomial time to `$(k r)$-ROOT-SUM` for every `k ≥ 1`. -/
theorem polyTimeReducible_RootSum_mul (r : ℚ) {k : ℕ} (hk : 1 ≤ k) :
    PolyTimeReducible encRootSum encRootSum (RootSum r) (RootSum ((k : ℚ) * r)) :=
  ⟨kpReduction k, computableInPolyTime_kpReduction k, kpReduction_mem_iff hk⟩

/-- One MSB-to-LSB binary search step for computing `⌊n^{1/p}⌋`. -/
@[expose]
def nthRootStep (p n acc k : ℕ) : ℕ :=
  let cand := acc + 2 ^ k
  if decide (cand ^ p ≤ n) then cand else acc

/-- Exact integer `p`-th root floor `⌊n^{1/p}⌋`. -/
@[expose]
def nthRootFloor (p n : ℕ) : ℕ :=
  ((List.range n.size).reverse).foldl (nthRootStep p n) 0

private theorem nthRootFloor_spec_aux {p : ℕ} (hp : 1 ≤ p) :
    ComputableInPolyTime (nthRootFloor p) encNat encNat ∧
      ∀ n : ℕ, (nthRootFloor p n) ^ p ≤ n ∧ n < (nthRootFloor p n + 1) ^ p := by
  have hlist : ComputableInPolyTime (fun n : ℕ ↦ (List.range n.size).reverse)
      encNat (encList encUnary) := by
    fun_prop
  have hcand : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ ↦ q.1.2 + 2 ^ q.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by
    fun_prop
  have hpow : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ ↦ (q.1.2 + 2 ^ q.2) ^ p)
      (encPair (encPair encNat encNat) encUnary) encNat :=
    binary_pow' hcand (const p)
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × ℕ ↦ nthRootStep p q.1.1 q.1.2 q.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by
    unfold nthRootStep
    exact (binary_le' hpow (fst _ _).fst').ite' hcand (fst _ _).snd'
  let inv : ℕ → List ℕ → ℕ → Prop := fun n consumed acc ↦
    acc ^ p ≤ n ∧ n < (acc + 2 ^ (n.size - consumed.length)) ^ p
  have hspec := foldlWith_spec (encIn := encNat) (encP := encNat) (encA := encUnary)
    (encL := encList encUnary) (encB := encNat)
    (par := id) (list := fun n : ℕ ↦ (List.range n.size).reverse)
    (init := fun _ ↦ 0) (step := nthRootStep p)
    id' hlist (const 0) hstep inv
    (fun n ↦ by
      refine ⟨by simp [zero_pow (by omega : p ≠ 0)], ?_⟩
      simp only [List.length_nil, Nat.sub_zero, zero_add]
      have hlt : n < 2 ^ n.size := Nat.lt_size_self n
      have hpow_ge : 2 ^ n.size ≤ (2 ^ n.size) ^ p := by
        simpa using Nat.pow_le_pow_right (Nat.one_le_two_pow) hp
      exact hlt.trans_le hpow_ge)
    (fun n consumed acc k hpref ⟨hle, hlt⟩ ↦ by
      have hlen_lt : consumed.length < ((List.range n.size).reverse).length := by
        have hl := hpref.length_le
        simp only [List.length_append, List.length_singleton] at hl
        omega
      have hlen_rev : ((List.range n.size).reverse).length = n.size := by simp
      have hget : (consumed ++ [k])[consumed.length]'(by simp) =
          ((List.range n.size).reverse)[consumed.length]'hlen_lt :=
        hpref.getElem (by simp)
      have hk_eq : k = n.size - 1 - consumed.length := by
        simpa [List.getElem_reverse, hlen_rev] using hget
      have hsub1 : n.size - consumed.length = k + 1 := by omega
      have hsub2 : n.size - (consumed ++ [k]).length = k := by simp; omega
      rw [hsub1] at hlt
      dsimp only [inv, id, nthRootStep]
      rw [hsub2]
      have h2k : acc + 2 ^ k + 2 ^ k = acc + 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
      by_cases hc : (acc + 2 ^ k) ^ p ≤ n
      · rw [ite_eq_left (decide_eq_true hc)]
        exact ⟨hc, by rwa [h2k]⟩
      · rw [ite_eq_right (by simpa using hc)]
        exact ⟨hle, Nat.lt_of_not_le hc⟩)
    (size := fun n ↦ (encNat n).length) PolyBounded.self
    (fun n _ acc _ ⟨hle, _⟩ ↦ by
      have hacc_le : acc ≤ n := by
        rcases Nat.eq_zero_or_pos acc with rfl | hpos
        · exact Nat.zero_le n
        · exact (by simpa using Nat.pow_le_pow_right hpos hp : acc ≤ acc ^ p).trans hle
      simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hacc_le)
  refine ⟨hspec.1, fun n ↦ ?_⟩
  have hfin := hspec.2 n
  dsimp only [inv] at hfin
  simp only [List.length_reverse, List.length_range, Nat.sub_self, Nat.pow_zero] at hfin
  exact hfin

theorem computableInPolyTime_nthRootFloor {p : ℕ} (hp : 1 ≤ p) :
    ComputableInPolyTime (nthRootFloor p) encNat encNat :=
  (nthRootFloor_spec_aux hp).1

theorem nthRootFloor_pow_le {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (nthRootFloor p n) ^ p ≤ n :=
  ((nthRootFloor_spec_aux hp).2 n).1

theorem lt_succ_nthRootFloor_pow {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    n < (nthRootFloor p n + 1) ^ p :=
  ((nthRootFloor_spec_aux hp).2 n).2

theorem nthRootFloor_pos {p n : ℕ} (hp : 1 ≤ p) (hn : 0 < n) :
    0 < nthRootFloor p n := by
  by_contra h0
  have heq : nthRootFloor p n = 0 := by omega
  have hlt := lt_succ_nthRootFloor_pow hp n
  rw [heq, zero_add, one_pow] at hlt
  omega

/-- One step of greedy `p`-th power extraction. -/
@[expose]
def greedyPowerStep (p : ℕ) (st : ℕ × List ℕ) : ℕ × List ℕ :=
  if decide (st.1 ≤ 0) then
    st
  else
    let a := nthRootFloor p st.1
    (st.1 - a ^ p, st.2 ++ [a])

/-- Polynomial unary iteration budget `n.size + 2^{p(p+1)}`. -/
@[expose]
def greedyStepBudget (p n : ℕ) : ℕ :=
  n.size + 2 ^ (p * (p + 1))

/-- Greedy decomposition of `n` into positive `p`-th powers. -/
@[expose]
def greedyPowers (p n : ℕ) : List ℕ :=
  ((greedyPowerStep p)^[greedyStepBudget p n] (n, [])).2

theorem greedy_remainder_lt_two_pow_mul {p n : ℕ} (hp : 1 ≤ p) (hn : 0 < n) :
    n - (nthRootFloor p n) ^ p < 2 ^ p * (nthRootFloor p n) ^ (p - 1) := by
  set a := nthRootFloor p n
  have ha_pos : 1 ≤ a := nthRootFloor_pos hp hn
  have hlt : n < (a + 1) ^ p := lt_succ_nthRootFloor_pow hp n
  have hexp : (a + 1) ^ p = (∑ l ∈ range p, p.choose l * a ^ l) + a ^ p := by
    have hb := add_pow a 1 p
    rw [sum_range_succ] at hb
    simpa [Nat.choose_self, mul_comm] using hb
  have hsum_le : ∑ l ∈ range p, p.choose l * a ^ l ≤
      (∑ l ∈ range p, p.choose l) * a ^ (p - 1) := by
    rw [sum_mul]
    refine sum_le_sum fun l hl ↦ Nat.mul_le_mul_left _ ?_
    exact Nat.pow_le_pow_right ha_pos (by have := mem_range.mp hl; omega)
  have hchoose_lt : ∑ l ∈ range p, p.choose l < 2 ^ p := by
    have htot := Nat.sum_range_choose p
    rw [sum_range_succ, Nat.choose_self] at htot
    omega
  have hprod_lt : (∑ l ∈ range p, p.choose l) * a ^ (p - 1) < 2 ^ p * a ^ (p - 1) :=
    Nat.mul_lt_mul_of_pos_right hchoose_lt (Nat.pow_pos ha_pos)
  omega

private theorem greedyPowerStep_rem_zero {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (((greedyPowerStep p)^[greedyStepBudget p n] (n, [])).1) = 0 := by
  set C := 2 ^ (p * (p + 1))
  let Φ : ℕ → ℕ := fun r ↦ if r < C then r else C + r.size
  have hstep_dec : ∀ st : ℕ × List ℕ, 0 < st.1 → Φ (greedyPowerStep p st).1 < Φ st.1 := by
    intro st hpos
    have hnot : ¬st.1 ≤ 0 := by omega
    have hrem : (greedyPowerStep p st).1 = st.1 - (nthRootFloor p st.1) ^ p := by
      simp [greedyPowerStep, hnot]
    rw [hrem]
    set r := st.1
    set a := nthRootFloor p r
    have ha_pos : 1 ≤ a := nthRootFloor_pos hp hpos
    have ha_pow_pos : 1 ≤ a ^ p := Nat.one_le_pow p a ha_pos
    have ha_pow_le : a ^ p ≤ r := nthRootFloor_pow_le hp r
    set r' := r - a ^ p
    have hr'_lt : r' < r := by omega
    by_cases hrC : r < C
    · have hr'C : r' < C := hr'_lt.trans hrC
      simp only [Φ, ite_eq_left hrC, ite_eq_left hr'C]
      exact hr'_lt
    · rcases eq_or_lt_of_le hp with rfl | hp2
      · have hlt1 : r < (a + 1) ^ 1 := lt_succ_nthRootFloor_pow (le_refl 1) r
        simp only [pow_one] at ha_pow_le hlt1
        have hr'0 : r' = 0 := by dsimp only [r']; rw [pow_one]; omega
        rw [hr'0]
        have hC_pos : 0 < C := by positivity
        simp only [Φ, ite_eq_left hC_pos, ite_eq_right hrC]
        omega
      · have hpow_ge : (2 ^ (p + 1)) ^ p ≤ r := by
          rw [← Nat.pow_mul, mul_comm]
          exact not_lt.mp hrC
        have ha_ge : 2 ^ (p + 1) ≤ a := by
          by_contra hlt_a
          have hle_a : a + 1 ≤ 2 ^ (p + 1) := by omega
          have hpow_le : (a + 1) ^ p ≤ (2 ^ (p + 1)) ^ p := Nat.pow_le_pow_left hle_a p
          have hlt_r : r < (a + 1) ^ p := lt_succ_nthRootFloor_pow hp r
          omega
        have hrem_lt : r' < 2 ^ p * a ^ (p - 1) := greedy_remainder_lt_two_pow_mul hp hpos
        have h2r' : 2 * r' < r := by
          calc
            2 * r' < 2 * (2 ^ p * a ^ (p - 1)) := by omega
            _ = 2 ^ (p + 1) * a ^ (p - 1) := by rw [Nat.pow_succ]; ring
            _ ≤ a * a ^ (p - 1) := Nat.mul_le_mul_right _ ha_ge
            _ = a ^ p := by conv_rhs => rw [← Nat.sub_add_cancel hp, Nat.pow_succ']
            _ ≤ r := ha_pow_le
        have hr_size_pos : 1 ≤ r.size := Nat.size_pos.mpr hpos
        have hr'_size_lt : r'.size < r.size := by
          rcases Nat.eq_zero_or_pos r' with hr'0 | hr'pos
          · rw [hr'0, Nat.size_zero]; omega
          · refine (Nat.size_le.mpr ?_).trans_lt (Nat.lt_succ_self (r.size - 1)) |>.trans_eq
              (Nat.sub_add_cancel hr_size_pos)
            have hr_lt_pow : r < 2 ^ r.size := Nat.lt_size_self r
            have hpow_split : 2 ^ r.size = 2 * 2 ^ (r.size - 1) := by
              conv_lhs => rw [← Nat.sub_add_cancel hr_size_pos, Nat.pow_succ']
            omega
        dsimp only [Φ]
        rw [ite_eq_right hrC]
        split_ifs with hr'C <;> omega
  have hiter_bound : ∀ k : ℕ,
      Φ (((greedyPowerStep p)^[k] (n, [])).1) ≤ Φ n - k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      set st := (greedyPowerStep p)^[k] (n, [])
      rcases Nat.eq_zero_or_pos st.1 with h0 | hpos
      · have hfix : (greedyPowerStep p st).1 = 0 := by simp [greedyPowerStep, h0]
        have hΦ0 : Φ 0 = 0 := by
          have hC_pos : 0 < C := by positivity
          simp [Φ, hC_pos]
        rw [hfix, hΦ0]
        exact Nat.zero_le _
      · have hdec := hstep_dec st hpos
        omega
  have hΦ_le_budget : Φ n ≤ greedyStepBudget p n := by
    dsimp only [Φ, greedyStepBudget]
    split_ifs <;> omega
  have h0_le := hiter_bound (greedyStepBudget p n)
  have hΦ_end_zero : Φ (((greedyPowerStep p)^[greedyStepBudget p n] (n, [])).1) = 0 := by omega
  set r_end := ((greedyPowerStep p)^[greedyStepBudget p n] (n, [])).1
  have hΦ_r : Φ r_end = 0 := hΦ_end_zero
  by_contra hne
  have hpos_end : 0 < r_end := Nat.pos_of_ne_zero hne
  have hC_pos : 0 < C := by positivity
  dsimp only [Φ] at hΦ_r
  split_ifs at hΦ_r <;> omega

private theorem greedyPowers_polyTime_and_sum {p : ℕ} (hp : 1 ≤ p) :
    ComputableInPolyTime (greedyPowers p) encNat (encList encNat) ∧
      ∀ n : ℕ, (∀ a ∈ greedyPowers p n, 0 < a) ∧
        ((greedyPowers p n).map (· ^ p)).sum = n := by
  have hcount : ComputableInPolyTime (greedyStepBudget p) encNat encUnary :=
    unary_add' binary_size (const (2 ^ (p * (p + 1))))
  have hinit : ComputableInPolyTime (fun n : ℕ ↦ (n, ([] : List ℕ)))
      encNat (encPair encNat (encList encNat)) :=
    id'.prod (const [])
  have hroot : ComputableInPolyTime
      (fun st : ℕ × List ℕ ↦ nthRootFloor p st.1)
      (encPair encNat (encList encNat)) encNat :=
    (computableInPolyTime_nthRootFloor hp).comp (fst _ _)
  have hrem : ComputableInPolyTime
      (fun st : ℕ × List ℕ ↦ st.1 - (nthRootFloor p st.1) ^ p)
      (encPair encNat (encList encNat)) encNat :=
    binary_sub' (fst _ _) (binary_pow' hroot (const p))
  have happ : ComputableInPolyTime
      (fun st : ℕ × List ℕ ↦ st.2 ++ [nthRootFloor p st.1])
      (encPair encNat (encList encNat)) (encList encNat) :=
    (listAppend encNat).comp
      ((snd _ _).prod ((ComputableInPolyTime.cons encNat).comp (hroot.prod (const []))))
  have hstep : ComputableInPolyTime (greedyPowerStep p)
      (encPair encNat (encList encNat)) (encPair encNat (encList encNat)) := by
    unfold greedyPowerStep
    exact (binary_le' (fst _ _) (const 0)).ite' id' (hrem.prod happ)
  let inv : ℕ → ℕ → ℕ × List ℕ → Prop := fun n i st ↦
    st.1 ≤ n ∧ (∀ a ∈ st.2, 0 < a ∧ a ≤ n) ∧
      st.2.length ≤ i ∧ st.1 + (st.2.map (· ^ p)).sum = n ∧
      (encList encNat st.2).length ≤ i * (2 * (encNat n).length + 2)
  let sizeBound : ℕ → ℕ := fun n ↦
    2 * (encNat n).length + 3 + greedyStepBudget p n * (2 * (encNat n).length + 2)
  have hsize : PolyBounded (fun n : ℕ ↦ (encNat n).length) sizeBound := by
    have hb : PolyBounded (fun n : ℕ ↦ (encNat n).length) (greedyStepBudget p) :=
      hcount.polyBounded
    exact ((PolyBounded.const 2).mul PolyBounded.self |>.add (PolyBounded.const 3)).add
      (hb.mul (((PolyBounded.const 2).mul PolyBounded.self).add (PolyBounded.const 2)))
  have hspec := iterate_spec (encIn := encNat) (encState := encPair encNat (encList encNat))
    hcount hinit hstep inv
    (fun n ↦ by simp [inv])
    (fun n i st _ ⟨hrem_le, hall, hlen_i, hsum_eq, henc_le⟩ ↦ by
      by_cases h0 : st.1 ≤ 0
      · have hst : greedyPowerStep p st = st := by simp [greedyPowerStep, h0]
        rw [hst]
        refine ⟨hrem_le, hall, by omega, hsum_eq, ?_⟩
        exact henc_le.trans (Nat.mul_le_mul_right _ (Nat.le_succ i))
      · have hpos : 0 < st.1 := by omega
        set a := nthRootFloor p st.1
        have ha_pos : 0 < a := nthRootFloor_pos hp hpos
        have ha_pow_le : a ^ p ≤ st.1 := nthRootFloor_pow_le hp st.1
        have ha_le_n : a ≤ n :=
          (by simpa using Nat.pow_le_pow_right ha_pos hp : a ≤ a ^ p).trans
            (ha_pow_le.trans hrem_le)
        have ha_enc : (encNat a).length ≤ (encNat n).length := by
          simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size ha_le_n
        have hst : greedyPowerStep p st = (st.1 - a ^ p, st.2 ++ [a]) := by
          simp [greedyPowerStep, h0, a]
        rw [hst]
        refine ⟨by omega, ?_, by simp; omega, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx1 | hx2
          · exact hall x hx1
          · rw [List.mem_singleton.mp hx2]
            exact ⟨ha_pos, ha_le_n⟩
        · simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
          omega
        · simp only [encList_append, List.length_append, encList_cons, encList_nil,
            List.append_nil, length_frame]
          rw [Nat.add_mul, Nat.one_mul]
          omega)
    hsize
    (fun n i st hi ⟨hrem_le, _, _, _, henc_le⟩ ↦ by
      have hrem_enc : (encNat st.1).length ≤ (encNat n).length := by
        simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hrem_le
      have hmul : i * (2 * (encNat n).length + 2) ≤
          greedyStepBudget p n * (2 * (encNat n).length + 2) :=
        Nat.mul_le_mul_right _ hi
      simp only [length_encPair, sizeBound]
      omega)
  refine ⟨(snd encNat (encList encNat)).comp hspec.1, fun n ↦ ?_⟩
  have hfin := hspec.2 n
  have hrem0 := greedyPowerStep_rem_zero hp n
  dsimp only [inv] at hfin
  rw [hrem0, zero_add] at hfin
  exact ⟨fun a ha ↦ (hfin.2.1 a ha).1, hfin.2.2.2.1⟩

theorem computableInPolyTime_greedyPowers {p : ℕ} (hp : 1 ≤ p) :
    ComputableInPolyTime (greedyPowers p) encNat (encList encNat) :=
  (greedyPowers_polyTime_and_sum hp).1

theorem greedyPowers_sum_eq {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (∀ a ∈ greedyPowers p n, 0 < a) ∧ ((greedyPowers p n).map (· ^ p)).sum = n :=
  (greedyPowers_polyTime_and_sum hp).2 n

private lemma log_log_three_pos : 0 < Real.log (Real.log 3) := by
  have hexp_neg : 5 / 6 ≤ Real.exp (-1 / 6) := by
    have h := Real.add_one_le_exp (-1 / 6 : ℝ)
    linarith
  have hpow6 : (5 / 6 : ℝ) ^ 6 ≤ (Real.exp (-1 / 6)) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hexp_neg 6
  have hexp_m1 : (Real.exp (-1 / 6)) ^ 6 = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_nat_mul]
    norm_num
    exact Real.exp_neg 1
  rw [hexp_m1] at hpow6
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp_lt3 : Real.exp 1 < 3 := by
    have hm := mul_le_mul_of_nonneg_right hpow6 hexp_pos.le
    rw [inv_mul_cancel₀ hexp_pos.ne'] at hm
    norm_num at hm
    linarith
  have h1_lt_log3 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log hexp_pos hexp_lt3
  exact Real.log_pos h1_lt_log3

theorem exists_greedyPowers_length_le_log_log {p : ℕ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      ((greedyPowers p n).length : ℝ) ≤ C * Real.log (Real.log (n : ℝ)) := by
  have hll3 : 0 < Real.log (Real.log 3) := log_log_three_pos
  rcases eq_or_lt_of_le hp with rfl | hp2
  · refine ⟨1 / Real.log (Real.log 3), by positivity, fun n hn ↦ ?_⟩
    have hstep1 : greedyPowerStep 1 (n, []) = (0, [n]) := by
      have hnot : ¬(n, ([] : List ℕ)).1 ≤ 0 := by simp; omega
      have hr1 : nthRootFloor 1 n = n := by
        have h1 := nthRootFloor_pow_le (le_refl 1) n
        have h2 := lt_succ_nthRootFloor_pow (le_refl 1) n
        simp only [pow_one] at h1 h2
        omega
      simp [greedyPowerStep, hnot, hr1]
    have hfix0 : ∀ k, (greedyPowerStep 1)^[k] (0, [n]) = (0, [n]) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [greedyPowerStep]
    have hlen1 : (greedyPowers 1 n).length = 1 := by
      unfold greedyPowers
      have hbud_pos : 1 ≤ greedyStepBudget 1 n := by unfold greedyStepBudget; omega
      conv_lhs =>
        rw [← Nat.sub_add_cancel hbud_pos, Function.iterate_add_apply,
          Function.iterate_one, hstep1, hfix0]
      rfl
    rw [hlen1, Nat.cast_one]
    have hll_mono : Real.log (Real.log 3) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
    have hm := mul_le_mul_of_nonneg_left hll_mono (by positivity : 0 ≤ 1 / Real.log (Real.log 3))
    rwa [one_div_mul_cancel hll3.ne'] at hm
  · set B_tail := 2 ^ (p ^ 2 + 1)
    set α : ℝ := ((p - 1 : ℕ) : ℝ) / (p : ℝ)
    have hα_pos : 0 < α := by
      dsimp only [α]
      have : 1 ≤ p - 1 := by omega
      positivity
    have hα_lt1 : α < 1 := by
      dsimp only [α]
      rw [div_lt_one (by positivity)]
      exact_mod_cast (show p - 1 < p by omega)
    have hneg_logα : 0 < -Real.log α := neg_pos.mpr (Real.log_neg hα_pos hα_lt1)
    let C_step : ℝ := 1 / (-Real.log α)
    let C_const : ℝ := ((B_tail + 2 : ℕ) : ℝ) + |Real.log (Real.log 2)| * C_step
    refine ⟨C_step + C_const / Real.log (Real.log 3), by positivity, fun n hn ↦ ?_⟩
    let remAt : ℕ → ℕ := fun t ↦ ((greedyPowerStep p)^[t] (n, [])).1
    let listAt : ℕ → List ℕ := fun t ↦ ((greedyPowerStep p)^[t] (n, [])).2
    have hlogb_step : ∀ t : ℕ, 0 < remAt (t + 1) →
        Real.logb 2 (remAt (t + 1) : ℝ) - (p : ℝ) ^ 2 ≤
          α * (Real.logb 2 (remAt t : ℝ) - (p : ℝ) ^ 2) := by
      intro t hnext_pos
      have hcur_pos : 0 < remAt t := by
        by_contra hc0
        have heq0 : remAt t = 0 := by omega
        have hn0 : remAt (t + 1) = 0 := by
          dsimp only [remAt] at heq0 ⊢
          rw [Function.iterate_succ_apply', greedyPowerStep]; simp [heq0]
        omega
      have hrem_eq : remAt (t + 1) = remAt t - (nthRootFloor p (remAt t)) ^ p := by
        dsimp only [remAt]
        rw [Function.iterate_succ_apply', greedyPowerStep]
        have hnot : ¬((greedyPowerStep p)^[t] (n, [])).1 ≤ 0 := by
          change ¬remAt t ≤ 0; omega
        simp [hnot]
      have hlt_nat := greedy_remainder_lt_two_pow_mul hp hcur_pos
      rw [← hrem_eq] at hlt_nat
      have ha_le_rpow : (nthRootFloor p (remAt t) : ℝ) ≤ (remAt t : ℝ) ^ (1 / (p : ℝ)) := by
        have hpow_le : ((nthRootFloor p (remAt t) : ℝ)) ^ p ≤ (remAt t : ℝ) := by
          exact_mod_cast nthRootFloor_pow_le hp (remAt t)
        have hrpow := Real.rpow_le_rpow (by positivity) hpow_le (by positivity : 0 ≤ 1 / (p : ℝ))
        rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          mul_one_div_cancel (by positivity : (p : ℝ) ≠ 0), Real.rpow_one] at hrpow
      have hreal_le : (remAt (t + 1) : ℝ) ≤ (2 : ℝ) ^ p * (remAt t : ℝ) ^ α := by
        have hlt_real : (remAt (t + 1) : ℝ) ≤
            (2 : ℝ) ^ p * ((nthRootFloor p (remAt t) : ℝ)) ^ (p - 1) := by
          exact_mod_cast hlt_nat.le
        refine hlt_real.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        have hp1 := Real.rpow_le_rpow (by positivity) ha_le_rpow
          (Nat.cast_nonneg (p - 1))
        rw [Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hp1
        have hexp_eq : (1 / (p : ℝ)) * ((p - 1 : ℕ) : ℝ) = α := by dsimp only [α]; ring
        rwa [hexp_eq] at hp1
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogb_le : Real.logb 2 (remAt (t + 1) : ℝ) ≤
          (p : ℝ) + α * Real.logb 2 (remAt t : ℝ) := by
        unfold Real.logb
        have hl := Real.log_le_log (by positivity) hreal_le
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
          Real.log_rpow (by positivity)] at hl
        have hdiv := div_le_div_of_nonneg_right hl hlog2_pos.le
        rw [add_div, mul_div_assoc, div_self hlog2_pos.ne', mul_one, mul_div_assoc] at hdiv
        exact hdiv
      have hid : (p : ℝ) - (p : ℝ) ^ 2 = -α * (p : ℝ) ^ 2 := by
        dsimp only [α]
        have hp_sub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp]; simp
        rw [hp_sub]
        field_simp
        ring
      linarith
    have hlogb_iter : ∀ k : ℕ, 0 < remAt k →
        Real.logb 2 (remAt k : ℝ) - (p : ℝ) ^ 2 ≤
          α ^ k * (Real.logb 2 (n : ℝ) - (p : ℝ) ^ 2) := by
      intro k
      induction k with
      | zero => intro _; simp [remAt]
      | succ k ih =>
        intro hk1
        have hk0 : 0 < remAt k := by
          by_contra hc0
          have heq0 : remAt k = 0 := by omega
          have hn0 : remAt (k + 1) = 0 := by
            dsimp only [remAt] at heq0 ⊢
            rw [Function.iterate_succ_apply', greedyPowerStep]; simp [heq0]
          omega
        calc
          Real.logb 2 (remAt (k + 1) : ℝ) - (p : ℝ) ^ 2
            ≤ α * (Real.logb 2 (remAt k : ℝ) - (p : ℝ) ^ 2) := hlogb_step k hk1
          _ ≤ α * (α ^ k * (Real.logb 2 (n : ℝ) - (p : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (ih hk0) hα_pos.le
          _ = α ^ (k + 1) * (Real.logb 2 (n : ℝ) - (p : ℝ) ^ 2) := by rw [pow_succ']; ring
    let K_high : ℕ := ⌊C_step * Real.log (Real.logb 2 (n : ℝ))⌋₊ + 1
    have hhigh_drop : remAt K_high < B_tail := by
      by_contra hge
      have hrem_ge : B_tail ≤ remAt K_high := not_lt.mp hge
      have hpos_K : 0 < remAt K_high := (by positivity : 0 < B_tail).trans_le hrem_ge
      have hlogb_ge1 : 1 ≤ Real.logb 2 (remAt K_high : ℝ) - (p : ℝ) ^ 2 := by
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hpow_le : (2 : ℝ) ^ (p ^ 2 + 1) ≤ (remAt K_high : ℝ) := by exact_mod_cast hrem_ge
        have hl := Real.log_le_log (by positivity) hpow_le
        rw [Real.log_pow] at hl
        have hd : ((p ^ 2 + 1 : ℕ) : ℝ) ≤ Real.logb 2 (remAt K_high : ℝ) := by
          unfold Real.logb
          rw [le_div_iff₀ hlog2_pos]
          exact hl
        push_cast at hd
        linarith
      have hit := hlogb_iter K_high hpos_K
      have hlogb_n_gt1 : 1 < Real.logb 2 (n : ℝ) := by
        unfold Real.logb
        rw [one_lt_div (Real.log_pos (by norm_num))]
        exact Real.log_lt_log (by norm_num) (by exact_mod_cast hn)
      have hprod_ge1 : 1 ≤ α ^ K_high * Real.logb 2 (n : ℝ) := by
        have hsub_le : Real.logb 2 (n : ℝ) - (p : ℝ) ^ 2 ≤ Real.logb 2 (n : ℝ) := by
          have : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
          linarith
        exact hlogb_ge1.trans (hit.trans (mul_le_mul_of_nonneg_left hsub_le (by positivity)))
      have hlog_ge0 : 0 ≤ Real.log (α ^ K_high * Real.logb 2 (n : ℝ)) :=
        Real.log_nonneg hprod_ge1
      rw [Real.log_mul (by positivity) (by linarith), Real.log_pow] at hlog_ge0
      have hk_le : (K_high : ℝ) ≤ C_step * Real.log (Real.logb 2 (n : ℝ)) := by
        dsimp only [C_step]
        rw [one_div_mul_eq_div, le_div_iff₀ hneg_logα]
        linarith
      have hgt : C_step * Real.log (Real.logb 2 (n : ℝ)) < (K_high : ℝ) := by
        dsimp only [K_high]; push_cast; exact Nat.lt_floor_add_one _
      linarith
    have hrem_zero_at : ∀ m : ℕ, remAt K_high ≤ m → remAt (K_high + m) = 0 := by
      intro m
      induction m with
      | zero => intro hm; simp only [Nat.add_zero]; omega
      | succ m ih =>
        intro hm
        rcases Nat.eq_zero_or_pos (remAt (K_high + m)) with h0 | hpos
        · dsimp only [remAt] at h0 ⊢
          rw [Nat.add_succ, Function.iterate_succ_apply', greedyPowerStep]; simp [h0]
        · have hdec_m : ∀ j : ℕ, 0 < remAt (K_high + j) →
              remAt (K_high + j) + j ≤ remAt K_high := by
            intro j
            induction j with
            | zero => intro _; simp
            | succ j ihj =>
              intro hj1
              have hj0 : 0 < remAt (K_high + j) := by
                by_contra hc
                have he0 : remAt (K_high + j) = 0 := by omega
                have he1 : remAt (K_high + (j + 1)) = 0 := by
                  dsimp only [remAt] at he0 ⊢
                  rw [← Nat.add_assoc, Function.iterate_succ_apply', greedyPowerStep]; simp [he0]
                omega
              have hstep_j : remAt (K_high + (j + 1)) < remAt (K_high + j) := by
                dsimp only [remAt]
                rw [← Nat.add_assoc, Function.iterate_succ_apply', greedyPowerStep]
                have hnot : ¬((greedyPowerStep p)^[K_high + j] (n, [])).1 ≤ 0 := by
                  change ¬remAt (K_high + j) ≤ 0; omega
                simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte]
                have ha_p : 1 ≤ (nthRootFloor p (remAt (K_high + j))) ^ p :=
                  Nat.one_le_pow p _ (nthRootFloor_pos hp hj0)
                change remAt (K_high + j) - (nthRootFloor p (remAt (K_high + j))) ^ p <
                  remAt (K_high + j)
                omega
              have prev := ihj hj0
              omega
          have hle_k := hdec_m m hpos
          have hm1 : remAt (K_high + m) = 1 := by omega
          dsimp only [remAt]
          rw [Nat.add_succ, Function.iterate_succ_apply', greedyPowerStep]
          have hr1 : nthRootFloor p 1 = 1 := by
            have a1 := nthRootFloor_pow_le hp 1
            have a2 := lt_succ_nthRootFloor_pow hp 1
            by_contra hne1
            rcases Nat.lt_or_gt_of_ne hne1 with h0' | hgt1
            · have heq0 : nthRootFloor p 1 = 0 := by omega
              rw [heq0] at a2; simp at a2
            · have h2p : 2 ^ p ≤ (nthRootFloor p 1) ^ p := Nat.pow_le_pow_left hgt1 p
              have h2_gt : 1 < 2 ^ p := Nat.one_lt_two_pow (by omega)
              omega
          simp [show ((greedyPowerStep p)^[K_high + m] (n, [])).1 = 1 from hm1, hr1]
    have hzero_total : remAt (K_high + B_tail) = 0 :=
      hrem_zero_at B_tail hhigh_drop.le
    have hlen_le_step : ∀ t : ℕ, (listAt t).length ≤ t := by
      intro t
      induction t with
      | zero => simp [listAt]
      | succ t ih =>
        dsimp only [listAt]
        rw [Function.iterate_succ_apply', greedyPowerStep]
        split_ifs
        · exact ih.trans (Nat.le_succ t)
        · simp only [List.length_append, List.length_singleton]
          exact Nat.succ_le_succ ih
    have hfreeze : ∀ t d : ℕ, remAt t = 0 → listAt (t + d) = listAt t := by
      intro t d ht0
      induction d with
      | zero => simp
      | succ d ih =>
        have hrem_d : remAt (t + d) = 0 := by
          clear ih
          induction d with
          | zero => simpa using ht0
          | succ d ihd =>
            dsimp only [remAt] at ihd ⊢
            rw [Nat.add_succ, Function.iterate_succ_apply', greedyPowerStep]; simp [ihd]
        dsimp only [listAt]
        rw [Nat.add_succ, Function.iterate_succ_apply', greedyPowerStep]
        have hc0 : ((greedyPowerStep p)^[t + d] (n, [])).1 ≤ 0 := by
          change remAt (t + d) ≤ 0; omega
        simp only [hc0, decide_true, ↓reduceIte]
        exact ih
    have hlen_bound_nat : (greedyPowers p n).length ≤ K_high + B_tail := by
      unfold greedyPowers
      change (listAt (greedyStepBudget p n)).length ≤ K_high + B_tail
      rcases le_or_gt (greedyStepBudget p n) (K_high + B_tail) with hle | hgt
      · exact (hlen_le_step _).trans hle
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hgt.le
        rw [hd, hfreeze (K_high + B_tail) d hzero_total]
        exact hlen_le_step _
    have hlogb_split : Real.log (Real.logb 2 (n : ℝ)) =
        Real.log (Real.log (n : ℝ)) - Real.log (Real.log 2) := by
      unfold Real.logb
      have hln_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact Real.log_div hln_pos.ne' hl2_pos.ne'
    have hK_real : (K_high : ℝ) ≤
        C_step * Real.log (Real.log (n : ℝ)) + |Real.log (Real.log 2)| * C_step + 1 := by
      dsimp only [K_high]
      push_cast
      have hfl : (⌊C_step * Real.log (Real.logb 2 (n : ℝ))⌋₊ : ℝ) ≤
          max 0 (C_step * Real.log (Real.logb 2 (n : ℝ))) := by
        rcases le_or_gt 0 (C_step * Real.log (Real.logb 2 (n : ℝ))) with hnn | hneg
        · rw [max_eq_right hnn]; exact Nat.floor_le hnn
        · rw [Nat.floor_of_nonpos hneg.le, Nat.cast_zero]; exact le_max_left _ _
      have hub : C_step * Real.log (Real.logb 2 (n : ℝ)) ≤
          C_step * Real.log (Real.log (n : ℝ)) + |Real.log (Real.log 2)| * C_step := by
        rw [hlogb_split]
        have habs := neg_le_abs (Real.log (Real.log 2))
        have hm := mul_le_mul_of_nonneg_right habs (by positivity : 0 ≤ C_step)
        linarith
      have hll_pos : 0 < Real.log (Real.log (n : ℝ)) :=
        hll3.trans_le (Real.log_le_log (Real.log_pos (by norm_num))
          (Real.log_le_log (by norm_num) (by exact_mod_cast hn)))
      have hmax_le : max 0 (C_step * Real.log (Real.logb 2 (n : ℝ))) ≤
          C_step * Real.log (Real.log (n : ℝ)) + |Real.log (Real.log 2)| * C_step :=
        max_le (by positivity) hub
      linarith
    have hll_ge : Real.log (Real.log 3) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
    have hconst_le :
        C_const ≤ (C_const / Real.log (Real.log 3)) * Real.log (Real.log (n : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hll_ge
        (by positivity : 0 ≤ C_const / Real.log (Real.log 3))
      rwa [div_mul_cancel₀ _ hll3.ne'] at hm
    have hlen_real : ((greedyPowers p n).length : ℝ) ≤ (K_high : ℝ) + (B_tail : ℝ) := by
      exact_mod_cast hlen_bound_nat
    dsimp only [C_const] at hconst_le ⊢
    push_cast at hconst_le ⊢
    linarith

/-- Product of a list of binary natural numbers via signed binary integer product. -/
@[expose]
def natListProd (l : List ℕ) : ℕ :=
  (l.map fun a : ℕ ↦ (a : ℤ)).prod.toNat

theorem natListProd_eq_prod (l : List ℕ) : natListProd l = l.prod := by
  unfold natListProd
  have hcast : (l.map fun a : ℕ ↦ (a : ℤ)).prod = (l.prod : ℤ) := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul]
  rw [hcast, Int.toNat_natCast]

@[fun_prop]
theorem computableInPolyTime_natListProd :
    ComputableInPolyTime natListProd (encList encNat) encNat := by
  unfold natListProd
  exact intBin_toNat.comp (intBin_prod.comp
    (mapWith (intBin_natCast.comp (snd encBool encNat)) (const true) id'))

private theorem exists_lt_dvd_mul_add_one {p q : ℕ} (hq : 2 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ k : ℕ, 0 < k ∧ k < q ∧ q ∣ k * p + 1 := by
  have : NeZero q := ⟨by omega⟩
  let f : Fin q → Fin q := fun k ↦ ⟨(k.1 * p) % q, Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hmod : (a.1 * p) % q = (b.1 * p) % q := congr_arg Fin.val hab
    have hcong : a.1 * p ≡ b.1 * p [MOD q] := hmod
    have hc : a.1 ≡ b.1 [MOD q] := Nat.ModEq.cancel_right_of_coprime hcop.symm hcong
    rw [Nat.ModEq, Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at hc
    exact Fin.ext hc
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩).2
  obtain ⟨k, hk⟩ := hsurj ⟨q - 1, by omega⟩
  have hk_mod : (k.1 * p) % q = q - 1 := congr_arg Fin.val hk
  have hdvd : q ∣ k.1 * p + 1 := by
    have hdiv := Nat.div_add_mod (k.1 * p) q
    rw [hk_mod] at hdiv
    refine ⟨(k.1 * p) / q + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hk_pos : 0 < k.1 := by
    by_contra h0
    have heq0 : k.1 = 0 := by omega
    rw [heq0, zero_mul, Nat.zero_mod] at hk_mod
    omega
  exact ⟨k.1, hk_pos, k.2, hdvd⟩

/-- Polynomial-time reduction from `PRootSum p` to `PQRootSum p q` when `k * p + 1 = q * m`. -/
@[expose]
def pqReductionAux (p q k m : ℕ) (x : RootSumInstance) : RootSumInstance :=
  let pos := x.numbers.filter fun a ↦ decide (0 < a)
  let w := natListProd (pos.map (· ^ k))
  let terms := (List.range pos.length).flatMap fun i ↦
    let ai := pos.getD i 1
    let zi := natListProd (((pos.take i) ++ (pos.drop (i + 1))).map (· ^ k))
    let yi := ai ^ m
    (greedyPowers q zi).map fun c ↦ c ^ p * yi
  ⟨terms, w * x.threshold⟩

private theorem computableInPolyTime_pqReductionAux (p q k m : ℕ) (hq : 1 ≤ q) :
    ComputableInPolyTime (pqReductionAux p q k m) encRootSum encRootSum := by
  have hpos : ComputableInPolyTime
      (fun x : RootSumInstance ↦ x.numbers.filter fun a ↦ decide (0 < a))
      encRootSum (encList encNat) :=
    filterWith (binary_pos.comp (snd encBool encNat)) (const true)
      (encRootSum_numbers_polyTime id')
  have hpowk : ComputableInPolyTime (fun a : ℕ ↦ a ^ k) encNat encNat :=
    binary_pow' id' (const k)
  have hw : ComputableInPolyTime
      (fun x : RootSumInstance ↦
        natListProd ((x.numbers.filter fun a ↦ decide (0 < a)).map (· ^ k)))
      encRootSum encNat :=
    computableInPolyTime_natListProd.comp
      (mapWith (hpowk.comp (snd encBool encNat)) (const true) hpos)
  have hpos_p : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦ r.1.numbers.filter fun a ↦ decide (0 < a))
      (encPair encRootSum encUnary) (encList encNat) :=
    hpos.comp (fst _ _)
  have hai : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦
        (r.1.numbers.filter fun a ↦ decide (0 < a)).getD r.2 1)
      (encPair encRootSum encUnary) encNat :=
    listGetDWithInput hpos_p (snd _ _) 1
  have hyi : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦
        ((r.1.numbers.filter fun a ↦ decide (0 < a)).getD r.2 1) ^ m)
      (encPair encRootSum encUnary) encNat :=
    binary_pow' hai (const m)
  have hzi_list : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦
        (r.1.numbers.filter fun a ↦ decide (0 < a)).take r.2 ++
          (r.1.numbers.filter fun a ↦ decide (0 < a)).drop (r.2 + 1))
      (encPair encRootSum encUnary) (encList encNat) :=
    (listAppend encNat).comp
      ((listTakeWithInput hpos_p (snd _ _)).prod
        (listDropWithInput hpos_p (unary_add' (snd _ _) (const 1))))
  have hzi : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦
        natListProd
          (((r.1.numbers.filter fun a ↦ decide (0 < a)).take r.2 ++
            (r.1.numbers.filter fun a ↦ decide (0 < a)).drop (r.2 + 1)).map (· ^ k)))
      (encPair encRootSum encUnary) encNat :=
    computableInPolyTime_natListProd.comp
      (mapWith (hpowk.comp (snd encBool encNat)) (const true) hzi_list)
  have hcs : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦
        greedyPowers q
          (natListProd
            (((r.1.numbers.filter fun a ↦ decide (0 < a)).take r.2 ++
              (r.1.numbers.filter fun a ↦ decide (0 < a)).drop (r.2 + 1)).map (· ^ k))))
      (encPair encRootSum encUnary) (encList encNat) :=
    (computableInPolyTime_greedyPowers hq).comp hzi
  have hinner_elem : ComputableInPolyTime
      (fun u : (RootSumInstance × ℕ) × ℕ ↦
        u.2 ^ p * (((u.1.1.numbers.filter fun a ↦ decide (0 < a)).getD u.1.2 1) ^ m))
      (encPair (encPair encRootSum encUnary) encNat) encNat :=
    binary_mul' (binary_pow' (snd _ _) (const p)) (hyi.comp (fst _ _))
  have hrow : ComputableInPolyTime
      (fun r : RootSumInstance × ℕ ↦
        (greedyPowers q
          (natListProd
            (((r.1.numbers.filter fun a ↦ decide (0 < a)).take r.2 ++
              (r.1.numbers.filter fun a ↦ decide (0 < a)).drop (r.2 + 1)).map (· ^ k)))).map
          fun c ↦ c ^ p * (((r.1.numbers.filter fun a ↦ decide (0 < a)).getD r.2 1) ^ m))
      (encPair encRootSum encUnary) (encList encNat) :=
    mapWithInput hcs hinner_elem
  have hterms : ComputableInPolyTime
      (fun x : RootSumInstance ↦
        (List.range (x.numbers.filter fun a ↦ decide (0 < a)).length).flatMap fun i ↦
          (greedyPowers q
            (natListProd
              (((x.numbers.filter fun a ↦ decide (0 < a)).take i ++
                (x.numbers.filter fun a ↦ decide (0 < a)).drop (i + 1)).map (· ^ k)))).map
            fun c ↦ c ^ p * (((x.numbers.filter fun a ↦ decide (0 < a)).getD i 1) ^ m))
      encRootSum (encList encNat) :=
    flatMapWithInput (range.comp ((length_list encNat).comp hpos)) hrow
  have hthresh : ComputableInPolyTime
      (fun x : RootSumInstance ↦
        natListProd ((x.numbers.filter fun a ↦ decide (0 < a)).map (· ^ k)) * x.threshold)
      encRootSum encNat :=
    binary_mul' hw (encRootSum_threshold_polyTime id')
  unfold pqReductionAux
  exact encRootSum_mk_polyTime hterms hthresh

private lemma list_prod_take_drop_pow (l : List ℕ) (k : ℕ) {i : ℕ} (hi : i < l.length) :
    ((l.take i ++ l.drop (i + 1)).map (· ^ k)).prod * (l[i]) ^ k =
      (l.map (· ^ k)).prod := by
  have hsplit : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l, List.drop_eq_getElem_cons hi]
  conv_rhs => rw [hsplit]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

/-- `PRootSum p` reduces in polynomial time to `PQRootSum p q` when `Nat.Coprime p q`. -/
theorem polyTimeReducible_PRootSum_PQRootSum {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) :
    PolyTimeReducible encRootSum encRootSum (PRootSum p) (PQRootSum p q) := by
  rcases eq_or_lt_of_le hq with rfl | hq2
  · refine ⟨id, id', fun x ↦ ?_⟩
    simp [PRootSum, PQRootSum]
  · obtain ⟨k, _, _, q_dvd⟩ := exists_lt_dvd_mul_add_one hq2 hcop
    obtain ⟨m, hm_eq⟩ := q_dvd
    refine ⟨pqReductionAux p q k m, computableInPolyTime_pqReductionAux p q k m hq, fun x ↦ ?_⟩
    rw [mem_PRootSum_iff, mem_PQRootSum_iff]
    set pos := x.numbers.filter fun a ↦ decide (0 < a)
    have hpos_mem : ∀ a ∈ pos, 0 < a := fun a ha ↦ by simpa [pos] using (List.mem_filter.mp ha).2
    have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
    rw [← realPowListSum_filter_pos (by positivity) x.numbers]
    set w := natListProd (pos.map (· ^ k))
    have hw_eq : w = (pos.map (· ^ k)).prod := natListProd_eq_prod _
    have hw_pos_nat : 0 < w := by
      rw [hw_eq]
      refine List.prod_pos fun y hy ↦ ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
      exact Nat.pow_pos (hpos_mem a ha)
    have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw_pos_nat
    have hrow_sum : ∀ i : ℕ, (hi : i < pos.length) →
        realPowListSum ((q : ℝ) / (p : ℝ))
          ((greedyPowers q
            (natListProd (((pos.take i) ++ (pos.drop (i + 1))).map (· ^ k)))).map
            fun c ↦ c ^ p * (pos.getD i 1) ^ m) =
          (w : ℝ) * (pos[i] : ℝ) ^ (1 / (p : ℝ)) := by
      intro i hi
      set ai := pos[i]
      have hai_get : pos.getD i 1 = ai := List.getD_eq_getElem pos 1 hi
      rw [hai_get]
      have hai_pos : 0 < ai := hpos_mem ai (List.getElem_mem hi)
      have hai_real_pos : (0 : ℝ) < (ai : ℝ) := by exact_mod_cast hai_pos
      set zi := natListProd (((pos.take i) ++ (pos.drop (i + 1))).map (· ^ k))
      have hzi_prod : zi * ai ^ k = w := by
        dsimp only [zi]
        rw [natListProd_eq_prod, hw_eq]
        exact list_prod_take_drop_pow pos k hi
      have hgp_sum := (greedyPowers_sum_eq hq zi).2
      unfold realPowListSum
      rw [List.map_map]
      simp only [Function.comp_def]
      have hterm_eq :
          (fun c : ℕ ↦ ((c ^ p * ai ^ m : ℕ) : ℝ) ^ ((q : ℝ) / (p : ℝ))) =
            fun c : ℕ ↦ ((c ^ q : ℕ) : ℝ) * (((ai ^ k : ℕ) : ℝ) * (ai : ℝ) ^ (1 / (p : ℝ))) := by
        funext c
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
        have hc_part : ((c ^ p : ℕ) : ℝ) ^ ((q : ℝ) / (p : ℝ)) = ((c ^ q : ℕ) : ℝ) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg c),
            mul_div_cancel₀ _ hp_pos.ne', Real.rpow_natCast, Nat.cast_pow]
        have ha_part : ((ai ^ m : ℕ) : ℝ) ^ ((q : ℝ) / (p : ℝ)) =
            ((ai ^ k : ℕ) : ℝ) * (ai : ℝ) ^ (1 / (p : ℝ)) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hai_real_pos.le]
          have hexp : (m : ℝ) * ((q : ℝ) / (p : ℝ)) = (k : ℝ) + 1 / (p : ℝ) := by
            have hqm : (q : ℝ) * (m : ℝ) = (k : ℝ) * (p : ℝ) + 1 := by exact_mod_cast hm_eq.symm
            field_simp [hp_pos.ne']
            linarith
          rw [hexp, Real.rpow_add hai_real_pos, Real.rpow_natCast, Nat.cast_pow]
        rw [hc_part, ha_part]
      rw [hterm_eq]
      have hsum_factor : ∀ l : List ℕ, (R : ℝ) →
          (l.map fun c : ℕ ↦ ((c ^ q : ℕ) : ℝ) * R).sum =
            (((l.map (· ^ q)).sum : ℕ) : ℝ) * R := by
        intro l R
        induction l with
        | nil => simp
        | cons c l ih =>
          simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add]
          ring
      rw [hsum_factor (greedyPowers q zi) _, hgp_sum]
      have hzi_real : (zi : ℝ) * ((ai ^ k : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast hzi_prod
      calc
        (zi : ℝ) * (((ai ^ k : ℕ) : ℝ) * (ai : ℝ) ^ (1 / (p : ℝ)))
          = ((zi : ℝ) * ((ai ^ k : ℕ) : ℝ)) * (ai : ℝ) ^ (1 / (p : ℝ)) := by ring
        _ = (w : ℝ) * (ai : ℝ) ^ (1 / (p : ℝ)) := by rw [hzi_real]
    have hflat_sum : realPowListSum ((q : ℝ) / (p : ℝ)) (pqReductionAux p q k m x).numbers =
        (w : ℝ) * realPowListSum (1 / (p : ℝ)) pos := by
      have hfm : ∀ (idxs : List ℕ) (f : ℕ → List ℕ),
          realPowListSum ((q : ℝ) / (p : ℝ)) (idxs.flatMap f) =
            (idxs.map (realPowListSum ((q : ℝ) / (p : ℝ)) ∘ f)).sum := by
        intro idxs f
        induction idxs with
        | nil => rfl
        | cons h t ih =>
          rw [List.flatMap_cons, realPowListSum_append, List.map_cons, List.sum_cons, ih]
          rfl
      dsimp only [pqReductionAux]
      rw [hfm]
      have hrange_eq : ((List.range pos.length).map
          (realPowListSum ((q : ℝ) / (p : ℝ)) ∘ fun i ↦
            (greedyPowers q
              (natListProd (((pos.take i) ++ (pos.drop (i + 1))).map (· ^ k)))).map
              fun c ↦ c ^ p * (pos.getD i 1) ^ m)) =
          (pos.map fun a : ℕ ↦ (w : ℝ) * (a : ℝ) ^ (1 / (p : ℝ))) := by
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        simp only [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
        exact hrow_sum i hi1
      rw [hrange_eq]
      unfold realPowListSum
      clear hrange_eq hrow_sum
      induction pos with
      | nil => simp
      | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
    rw [hflat_sum]
    dsimp only [pqReductionAux]
    rw [Nat.cast_mul]
    exact ⟨fun h ↦ mul_le_mul_of_nonneg_left h hw_pos.le,
      fun h ↦ le_of_mul_le_mul_left h hw_pos⟩

/-- Polynomial-time equivalence of `PRootSum p` and `PQRootSum p q` when `Nat.Coprime p q`. -/
theorem polyTimeEquivalent_PRootSum_PQRootSum {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) :
    PolyTimeReducible encRootSum encRootSum (PRootSum p) (PQRootSum p q) ∧
      PolyTimeReducible encRootSum encRootSum (PQRootSum p q) (PRootSum p) := by
  refine ⟨polyTimeReducible_PRootSum_PQRootSum hp hq hcop, ?_⟩
  have hback : PolyTimeReducible encRootSum encRootSum
      (RootSum ((p : ℚ) / (q : ℚ))) (RootSum ((q : ℚ) * ((p : ℚ) / (q : ℚ)))) :=
    polyTimeReducible_RootSum_mul ((p : ℚ) / (q : ℚ)) hq
  have hcancel : (q : ℚ) * ((p : ℚ) / (q : ℚ)) = (p : ℚ) :=
    mul_div_cancel₀ (p : ℚ) (by positivity)
  rw [hcancel] at hback
  exact hback

end CslibFrontier.Complexity
