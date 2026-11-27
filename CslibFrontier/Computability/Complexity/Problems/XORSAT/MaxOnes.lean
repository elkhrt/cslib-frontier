/-
Copyright (c) 2026 PanMath Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Polynomial-Time 1/2-Approximation for Max-Ones over GF(2) Linear Equations

Given a satisfiable system of linear equations over `GF(2)` (`Cslib.Complexity.XORSAT.Dense`),
finding a solution maximizing the number of variables set to `1` (`true`) admits a
deterministic polynomial-time `1/2`-approximation algorithm
.

The algorithm uses the method of conditional expectations over the affine solution space. Using
Gaussian elimination (`Cslib.Complexity.XORSAT.Dense.decide`), for any satisfiable system `F`
each variable is either forced to `0`, forced to `1`, or unforced (equal to `1` in exactly half
of all solutions). Hence twice the expected Hamming weight of a uniformly random solution equals
`score F = 2 * (# forced to 1) + (# unforced)`, which is at least the maximum weight of any
solution. Assigning variables sequentially to maximize `score` preserves the conditional
expectation and yields a solution of weight at least half the optimum in polynomial time.

## Main definitions

* `Cslib.Complexity.XORSAT.MaxOnes.unitRow`: the parity equation `x_j = b`.
* `Cslib.Complexity.XORSAT.MaxOnes.score`: twice the expected Hamming weight of a uniform
  random solution to a dense linear system mod `2`.
* `Cslib.Complexity.XORSAT.MaxOnes.stepState`: one variable-fixing step of the derandomized
  algorithm.
* `Cslib.Complexity.XORSAT.MaxOnes.solve`: the deterministic derandomized `1/2`-approximation
  algorithm for Max-Ones over linear equations mod `2`.

## Main results

* `Cslib.Complexity.XORSAT.MaxOnes.solve_length`: `solve q` outputs a word of length `q.width`.
* `Cslib.Complexity.XORSAT.MaxOnes.solve_holds`: `solve q` satisfies every equation of a
  satisfiable well-formed system `q`.
* `Cslib.Complexity.XORSAT.MaxOnes.solve_approx`: `solve q` sets at least half as many
  variables to `1` as any solution of `q`.
* `Cslib.Complexity.XORSAT.MaxOnes.computableInPolyTime_solve`: `solve` is computable in
  polynomial time on multi-tape Turing machines.
-/

public section

namespace Cslib.Complexity.XORSAT.MaxOnes

open Cslib.Complexity.XORSAT
open scoped Cslib.Complexity.XORSAT.Dense
open Turing.MultiTapeTM

/-- The unit parity equation `x_j = b` of width `n`. -/
def unitRow (n j : ℕ) (b : Bool) : Dense.Row :=
  ⟨(List.range n).map fun i => decide (i = j), b⟩

/-- The `k`-th coordinate of `unitRow n j b` is `true` iff `k = j` (for `k < n`). -/
theorem getD_unitRow_coeffs {n j k : ℕ} {b : Bool} (hk : k < n) :
    (unitRow n j b).coeffs.getD k false = decide (k = j) := by
  simp [unitRow, List.getD_eq_getElem?_getD, hk]

@[simp]
theorem length_unitRow_coeffs (n j : ℕ) (b : Bool) :
    (unitRow n j b).coeffs.length = n := by
  simp [unitRow]

/-- Coordinatewise XOR of two Boolean words. -/
private def xorList (a b : List Bool) : List Bool :=
  a.zipWith Bool.xor b

private theorem dot_xorList_right (c : List Bool) {a b : List Bool} (hab : a.length = b.length) :
    Dense.dot c (xorList a b) = Dense.dot c a + Dense.dot c b := by
  induction c generalizing a b with
  | nil => simp [Dense.dot, Bool.zero_eq_false]
  | cons x xs ih =>
    cases a with
    | nil =>
      cases b with
      | nil => simp [xorList, Dense.dot, Bool.zero_eq_false]
      | cons _ _ => simp at hab
    | cons u us =>
      cases b with
      | nil => simp at hab
      | cons v vs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hab
        simp only [xorList, List.zipWith_cons_cons, Dense.dot, ← Bool.add_eq_xor, mul_add]
        rw [show List.zipWith xor us vs = xorList us vs from rfl, ih hab]
        abel

private theorem dot_unitRow_eq {n j : ℕ} {b : Bool} {a : List Bool}
    (ha : a.length = n) (hj : j < n) :
    Dense.dot (unitRow n j b).coeffs a = a.getD j false := by
  have haux : ∀ (m k : ℕ) (l : List Bool), l.length = m →
      Dense.dot ((List.range m).map fun i => decide (i + k = j)) l =
        if k ≤ j ∧ j < m + k then l.getD (j - k) false else false := by
    intro m
    induction m with
    | zero =>
      intro k l hl
      cases l with
      | nil => simp [Dense.dot]
      | cons _ _ => simp at hl
    | succ m ih =>
      intro k l hl
      cases l with
      | nil => simp at hl
      | cons x xs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, Dense.dot]
        have hmap : ((fun i => decide (i + k = j)) ∘ (· + 1)) =
            (fun i => decide (i + (k + 1) = j)) := by
          funext i
          dsimp only [Function.comp_apply]
          congr 1
          exact propext (by omega)
        rw [hmap, ih (k + 1) xs hl]
        by_cases hkj : k = j
        · subst hkj
          simp [show (true : Bool) = 1 from rfl, ← Bool.zero_eq_false]
        · have hne : decide (0 + k = j) = false := by simp [hkj]
          rw [hne]
          simp only [← Bool.zero_eq_false, zero_mul, zero_add]
          by_cases hcond : k + 1 ≤ j ∧ j < m + (k + 1)
          · have hcond' : k ≤ j ∧ j < m + 1 + k := by omega
            have hsub : j - k = (j - (k + 1)) + 1 := by omega
            simp [hcond, hcond', hsub]
          · have hcond' : ¬ (k ≤ j ∧ j < m + 1 + k) := by omega
            simp only [hcond, hcond', ↓reduceIte]
  have h0 := haux n 0 a ha
  simpa [unitRow, hj] using h0

/-- Twice the expected Hamming weight of a uniform random solution to `q`: each variable forced
to `1` contributes `2`, each unforced variable contributes `1`, and each variable forced to `0`
contributes `0`. -/
def score (q : Dense.Input) : ℕ :=
  (List.range q.width).countP (fun j => Dense.decide ⟨q.width, unitRow q.width j true :: q.rows⟩) +
    (List.range q.width).countP
      (fun j => !Dense.decide ⟨q.width, unitRow q.width j false :: q.rows⟩)

/-- Choice of bit for variable `st.1` in `stepState`. -/
private def nextBit (width : ℕ) (st : ℕ × Dense.System × List Bool) : Bool :=
  let i := st.1
  let F := st.2.1
  let q0 : Dense.Input := ⟨width, unitRow width i false :: F⟩
  let q1 : Dense.Input := ⟨width, unitRow width i true :: F⟩
  let s0 := Dense.decide q0
  let s1 := Dense.decide q1
  if s0 && s1 then decide (score q0 ≤ score q1)
  else if s1 then true
  else false

/-- One variable-fixing step of the derandomized Max-Ones algorithm: fix variable `i` to `true`
if setting `x_i = 1` is feasible and achieves at least as large a conditional expectation as
setting `x_i = 0` (or if `x_i = 0` is infeasible), and otherwise fix `x_i = false`. -/
def stepState (width : ℕ) (st : ℕ × Dense.System × List Bool) : ℕ × Dense.System × List Bool :=
  let b := nextBit width st
  (st.1 + 1, unitRow width st.1 b :: st.2.1, st.2.2 ++ [b])

/-- Deterministic polynomial-time `1/2`-approximation algorithm for Max-Ones over linear equations
mod `2`. -/
def solve (q : Dense.Input) : List Bool :=
  ((stepState q.width)^[q.width] (0, q.rows, [])).2.2

/-- Exact specification of `Dense.decide` on an augmented system with one extra unit row. -/
private theorem decide_unitRow_eq_true_iff {n j : ℕ} {b : Bool} {F : Dense.System}
    (hF : Dense.Width n F) (hj : j < n) :
    Dense.decide ⟨n, unitRow n j b :: F⟩ = true ↔
      ∃ a : List Bool, a.length = n ∧ Dense.Holds F a ∧ a.getD j false = b := by
  rw [Dense.decide_eq_true_iff]
  constructor
  · rintro ⟨_, a, ha, hholds⟩
    refine ⟨a, ha, fun e he => hholds e (List.mem_cons_of_mem _ he), ?_⟩
    have h0 := hholds (unitRow n j b) List.mem_cons_self
    rwa [dot_unitRow_eq ha hj] at h0
  · rintro ⟨a, ha, hholds, hget⟩
    refine ⟨?_, a, ha, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact length_unitRow_coeffs n j b
      · exact hF e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rwa [dot_unitRow_eq ha hj]
      · exact hholds e he

/-- The finite set of all solutions of width `n` to `F`. -/
private noncomputable def solSet (n : ℕ) (F : Dense.System) : Finset (List Bool) :=
  @Finset.filter _ (fun a => Dense.Holds F a) (Classical.decPred _)
    ((Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset Bool)).image List.ofFn)

private theorem mem_solSet_iff {n : ℕ} {F : Dense.System} {a : List Bool} :
    a ∈ solSet n F ↔ a.length = n ∧ Dense.Holds F a := by
  classical
  simp only [solSet, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset,
    Finset.mem_univ, implies_true, true_and]
  constructor
  · rintro ⟨⟨f, rfl⟩, h⟩
    exact ⟨List.length_ofFn, h⟩
  · rintro ⟨hlen, h⟩
    refine ⟨⟨fun i => a[i.1]'(hlen ▸ i.2), ?_⟩, h⟩
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi₁ hi₂
      simp

private theorem xorList_length {a b : List Bool} {n : ℕ} (ha : a.length = n) (hb : b.length = n) :
    (xorList a b).length = n := by
  simp [xorList, ha, hb]

private theorem xorList_self_cancel {a d : List Bool} (ha : a.length = d.length) :
    xorList (xorList a d) d = a := by
  induction a generalizing d with
  | nil => cases d <;> simp_all [xorList]
  | cons x xs ih =>
    cases d with
    | nil => simp at ha
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at ha
      dsimp only [xorList]
      rw [List.zipWith_cons_cons, List.zipWith_cons_cons, Bool.xor_assoc, Bool.xor_self,
        Bool.xor_false]
      exact congrArg (x :: ·) (ih ha)

private theorem getD_xorList {a d : List Bool} {j : ℕ} (hj : j < a.length)
    (hd : d.length = a.length) :
    (xorList a d).getD j false = (a.getD j false ^^ d.getD j false) := by
  have hj' : j < d.length := hd ▸ hj
  simp [xorList, hj, hj']

private theorem solSet_unitRow_eq_filter {n j : ℕ} {b : Bool} {F : Dense.System} (hj : j < n) :
    solSet n (unitRow n j b :: F) = (solSet n F).filter (fun a => a.getD j false = b) := by
  ext a
  simp only [Finset.mem_filter, mem_solSet_iff]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨⟨ha, fun e he => h e (List.mem_cons_of_mem _ he)⟩, ?_⟩
    have h0 := h (unitRow n j b) List.mem_cons_self
    rwa [dot_unitRow_eq ha hj] at h0
  · rintro ⟨⟨ha, h⟩, hget⟩
    refine ⟨ha, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · rwa [dot_unitRow_eq ha hj]
    · exact h e he

/-- If variable `j` is unforced in `F`, then the subsets of solutions with `a[j] = false` and
`a[j] = true` have equal cardinality, and their sum is `(solSet n F).card`. -/
private theorem card_solSet_split {n j : ℕ} {F : Dense.System} (hj : j < n)
    (h0 : ∃ a, a.length = n ∧ Dense.Holds F a ∧ a.getD j false = false)
    (h1 : ∃ a, a.length = n ∧ Dense.Holds F a ∧ a.getD j false = true) :
    (solSet n (unitRow n j false :: F)).card = (solSet n (unitRow n j true :: F)).card ∧
      (solSet n F).card =
        (solSet n (unitRow n j false :: F)).card + (solSet n (unitRow n j true :: F)).card := by
  classical
  obtain ⟨a₀, ha₀, hF₀, hj₀⟩ := h0
  obtain ⟨a₁, ha₁, hF₁, hj₁⟩ := h1
  let d := xorList a₀ a₁
  have hd_len : d.length = n := xorList_length ha₀ ha₁
  have hd_j : d.getD j false = true := by
    rw [getD_xorList (ha₀.symm ▸ hj) (ha₁.trans ha₀.symm), hj₀, hj₁]
    rfl
  have hd_hom : ∀ e ∈ F, Dense.dot e.coeffs d = false := by
    intro e he
    rw [dot_xorList_right e.coeffs (ha₀.trans ha₁.symm), hF₀ e he, hF₁ e he,
      BooleanRing.add_self, Bool.zero_eq_false]
  have hbij : (solSet n (unitRow n j false :: F)).card =
      (solSet n (unitRow n j true :: F)).card := by
    refine Finset.card_bij (fun a _ => xorList a d) ?_ ?_ ?_
    · intro a ha
      rw [solSet_unitRow_eq_filter hj, Finset.mem_filter, mem_solSet_iff] at ha ⊢
      obtain ⟨⟨hlen, hholds⟩, hget⟩ := ha
      refine ⟨⟨xorList_length hlen hd_len, fun e he => ?_⟩, ?_⟩
      · rw [dot_xorList_right e.coeffs (hlen.trans hd_len.symm), hholds e he, hd_hom e he,
          ← Bool.zero_eq_false, add_zero]
      · rw [getD_xorList (hlen.symm ▸ hj) (hd_len.trans hlen.symm), hget, hd_j]
        rfl
    · intro a₁ ha₁ a₂ ha₂ heq
      rw [solSet_unitRow_eq_filter hj, Finset.mem_filter, mem_solSet_iff] at ha₁ ha₂
      have h1 := xorList_self_cancel (a := a₁) (d := d) (ha₁.1.1.trans hd_len.symm)
      have h2 := xorList_self_cancel (a := a₂) (d := d) (ha₂.1.1.trans hd_len.symm)
      rw [← h1, heq, h2]
    · intro b hb
      rw [solSet_unitRow_eq_filter hj, Finset.mem_filter, mem_solSet_iff] at hb
      obtain ⟨⟨hlen, hholds⟩, hget⟩ := hb
      refine ⟨xorList b d, ?_, xorList_self_cancel (hlen.trans hd_len.symm)⟩
      rw [solSet_unitRow_eq_filter hj, Finset.mem_filter, mem_solSet_iff]
      refine ⟨⟨xorList_length hlen hd_len, fun e he => ?_⟩, ?_⟩
      · rw [dot_xorList_right e.coeffs (hlen.trans hd_len.symm), hholds e he, hd_hom e he,
          ← Bool.zero_eq_false, add_zero]
      · rw [getD_xorList (hlen.symm ▸ hj) (hd_len.trans hlen.symm), hget, hd_j]
        rfl
  refine ⟨hbij, ?_⟩
  rw [solSet_unitRow_eq_filter hj, solSet_unitRow_eq_filter hj]
  have hcompl : (solSet n F).filter (fun a => a.getD j false = true) =
      (solSet n F).filter (fun a => ¬ (a.getD j false = false)) := by
    ext a
    simp only [Finset.mem_filter]
    cases a.getD j false <;> simp
  rw [hcompl, Finset.card_filter_add_card_filter_not]

private theorem count_true_eq_sum_getD {a : List Bool} {n : ℕ} (ha : a.length = n) :
    a.count true = ∑ j ∈ Finset.range n, (a.getD j false).toNat := by
  have haux : ∀ (l : List Bool),
      l.count true = ∑ j ∈ Finset.range l.length, (l.getD j false).toNat := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.count_cons]
      rw [ih]
      cases x <;> simp [Nat.add_comm]
  rw [← ha, haux a]

/-- Fundamental conditional-expectation identity: for any satisfiable well-width system `q`,
twice the sum of Hamming weights over all solutions equals `|solSet| * score q`. -/
private theorem two_mul_sum_weight_eq_card_mul_score {q : Dense.Input}
    (hW : Dense.Width q.width q.rows) (hS : Dense.Satisfiable q.width q.rows) :
    2 * ∑ a ∈ solSet q.width q.rows, a.count true =
      (solSet q.width q.rows).card * score q := by
  classical
  have hsum_swap : ∑ a ∈ solSet q.width q.rows, a.count true =
      ∑ j ∈ Finset.range q.width,
        ((solSet q.width q.rows).filter fun a => a.getD j false = true).card := by
    calc ∑ a ∈ solSet q.width q.rows, a.count true
        = ∑ a ∈ solSet q.width q.rows, ∑ j ∈ Finset.range q.width, (a.getD j false).toNat :=
          Finset.sum_congr rfl fun a ha => count_true_eq_sum_getD (mem_solSet_iff.mp ha).1
      _ = ∑ j ∈ Finset.range q.width, ∑ a ∈ solSet q.width q.rows, (a.getD j false).toNat :=
          Finset.sum_comm
      _ = ∑ j ∈ Finset.range q.width,
            ((solSet q.width q.rows).filter fun a => a.getD j false = true).card := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          refine Finset.sum_congr rfl fun a _ => ?_
          cases a.getD j false <;> simp
  have hscore_sum : score q = ∑ j ∈ Finset.range q.width,
      ((if Dense.decide ⟨q.width, unitRow q.width j true :: q.rows⟩ then 1 else 0) +
       (if !Dense.decide ⟨q.width, unitRow q.width j false :: q.rows⟩ then 1 else 0)) := by
    have hcp (p : ℕ → Bool) (n : ℕ) :
        (List.range n).countP p = ∑ j ∈ Finset.range n, if p j then 1 else 0 := by
      induction n with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
        simp [List.countP_singleton]
    rw [score, hcp, hcp, ← Finset.sum_add_distrib]
  rw [hsum_swap, hscore_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < q.width := Finset.mem_range.mp hj
  have hdec1 := decide_unitRow_eq_true_iff (b := true) hW hj'
  have hdec0 := decide_unitRow_eq_true_iff (b := false) hW hj'
  cases hs1 : Dense.decide ⟨q.width, unitRow q.width j true :: q.rows⟩ <;>
    cases hs0 : Dense.decide ⟨q.width, unitRow q.width j false :: q.rows⟩
  · -- Impossible: `q` is satisfiable so at least one of `x_j = 0` or `x_j = 1` holds.
    obtain ⟨a, ha, hholds⟩ := hS
    cases hget : a.getD j false
    · exact absurd (hdec0.mpr ⟨a, ha, hholds, hget⟩) (by simp [hs0])
    · exact absurd (hdec1.mpr ⟨a, ha, hholds, hget⟩) (by simp [hs1])
  · -- Forced to `0`
    have hnone : (solSet q.width q.rows).filter (fun a => a.getD j false = true) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a ha hget
      obtain ⟨hlen, hholds⟩ := mem_solSet_iff.mp ha
      exact absurd (hdec1.mpr ⟨a, hlen, hholds, hget⟩) (by simp [hs1])
    rw [hnone]
    simp
  · -- Forced to `1`
    have hall : (solSet q.width q.rows).filter (fun a => a.getD j false = true) =
        solSet q.width q.rows := by
      rw [Finset.filter_eq_self]
      intro a ha
      obtain ⟨hlen, hholds⟩ := mem_solSet_iff.mp ha
      cases hget : a.getD j false with
      | false => exact absurd (hdec0.mpr ⟨a, hlen, hholds, hget⟩) (by simp [hs0])
      | true => rfl
    rw [hall]
    simp [Nat.mul_comm]
  · -- Unforced
    have h0 := hdec0.mp hs0
    have h1 := hdec1.mp hs1
    obtain ⟨heq, htot⟩ := card_solSet_split hj' h0 h1
    rw [solSet_unitRow_eq_filter hj', solSet_unitRow_eq_filter hj'] at heq htot
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mul_one]
    omega

/-- Every solution of a well-width system `q` has Hamming weight at most `score q`. -/
theorem weight_le_score {q : Dense.Input} {a : List Bool} (hW : Dense.Width q.width q.rows)
    (ha : a.length = q.width) (hholds : Dense.Holds q.rows a) :
    a.count true ≤ score q := by
  have hcp (p : ℕ → Bool) (n : ℕ) :
      (List.range n).countP p = ∑ j ∈ Finset.range n, if p j then 1 else 0 := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
      simp [List.countP_singleton]
  rw [count_true_eq_sum_getD ha, score, hcp, hcp, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j < q.width := Finset.mem_range.mp hj
  cases hget : a.getD j false with
  | false => simp
  | true =>
    have hdec1 : Dense.decide ⟨q.width, unitRow q.width j true :: q.rows⟩ = true :=
      (decide_unitRow_eq_true_iff hW hj').mpr ⟨a, ha, hholds, hget⟩
    simp [hdec1]

/-- For an unforced variable `j`, `2 * score q = score q₀ + score q₁`, hence
`score q ≤ max (score q₀) (score q₁)`. -/
private theorem score_le_max_branch {n j : ℕ} {F : Dense.System} (hW : Dense.Width n F)
    (hj : j < n)
    (h0 : Dense.decide ⟨n, unitRow n j false :: F⟩ = true)
    (h1 : Dense.decide ⟨n, unitRow n j true :: F⟩ = true) :
    score ⟨n, F⟩ ≤
      max (score ⟨n, unitRow n j false :: F⟩) (score ⟨n, unitRow n j true :: F⟩) := by
  have hW0 : Dense.Width n (unitRow n j false :: F) := fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact length_unitRow_coeffs n j false
    · exact hW e he
  have hW1 : Dense.Width n (unitRow n j true :: F) := fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact length_unitRow_coeffs n j true
    · exact hW e he
  have hS0 : Dense.Satisfiable n (unitRow n j false :: F) :=
    ((Dense.decide_eq_true_iff _).mp h0).2
  have hS1 : Dense.Satisfiable n (unitRow n j true :: F) :=
    ((Dense.decide_eq_true_iff _).mp h1).2
  have hS : Dense.Satisfiable n F :=
    let ⟨a, ha, hh⟩ := hS0
    ⟨a, ha, fun e he => hh e (List.mem_cons_of_mem _ he)⟩
  obtain ⟨heq, htot⟩ := card_solSet_split hj
    ((decide_unitRow_eq_true_iff hW hj).mp h0)
    ((decide_unitRow_eq_true_iff hW hj).mp h1)
  have hpos : 0 < (solSet n (unitRow n j false :: F)).card := by
    obtain ⟨a, ha, hh⟩ := hS0
    exact Finset.card_pos.mpr ⟨a, mem_solSet_iff.mpr ⟨ha, hh⟩⟩
  have hid := two_mul_sum_weight_eq_card_mul_score (q := ⟨n, F⟩) hW hS
  have hid0 := two_mul_sum_weight_eq_card_mul_score (q := ⟨n, unitRow n j false :: F⟩) hW0 hS0
  have hid1 := two_mul_sum_weight_eq_card_mul_score (q := ⟨n, unitRow n j true :: F⟩) hW1 hS1
  have hdisj : Disjoint (solSet n (unitRow n j false :: F)) (solSet n (unitRow n j true :: F)) := by
    rw [solSet_unitRow_eq_filter hj, solSet_unitRow_eq_filter hj, Finset.disjoint_left]
    intro a ha₁ ha₂
    have h₁ := (Finset.mem_filter.mp ha₁).2
    have h₂ := (Finset.mem_filter.mp ha₂).2
    rw [h₁] at h₂
    cases h₂
  have hunion : solSet n (unitRow n j false :: F) ∪ solSet n (unitRow n j true :: F) =
      solSet n F := by
    ext a
    simp only [Finset.mem_union, solSet_unitRow_eq_filter hj, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      cases hget : a.getD j false
      · exact Or.inl ⟨h, rfl⟩
      · exact Or.inr ⟨h, rfl⟩
  have hsum_union : ∑ a ∈ solSet n F, a.count true =
      (∑ a ∈ solSet n (unitRow n j false :: F), a.count true) +
      (∑ a ∈ solSet n (unitRow n j true :: F), a.count true) := by
    rw [← hunion, Finset.sum_union hdisj]
  have hmul : (solSet n (unitRow n j false :: F)).card * (2 * score ⟨n, F⟩) =
      (solSet n (unitRow n j false :: F)).card *
        (score ⟨n, unitRow n j false :: F⟩ + score ⟨n, unitRow n j true :: F⟩) := by
    nlinarith
  have h2 : 2 * score ⟨n, F⟩ =
      score ⟨n, unitRow n j false :: F⟩ + score ⟨n, unitRow n j true :: F⟩ :=
    Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

/-- Loop invariant for `stepState`. -/
private def StepInv (q : Dense.Input) (i : ℕ) (st : ℕ × Dense.System × List Bool) : Prop :=
  st.1 = i ∧
  st.2.2.length = i ∧
  Dense.Width q.width st.2.1 ∧
  (∀ e ∈ q.rows, e ∈ st.2.1) ∧
  (∀ k < i, unitRow q.width k (st.2.2.getD k false) ∈ st.2.1) ∧
  Dense.Satisfiable q.width st.2.1 ∧
  score q ≤ score ⟨q.width, st.2.1⟩

private theorem stepInv_preserve {q : Dense.Input} {i : ℕ} {st : ℕ × Dense.System × List Bool}
    (hi : i < q.width) (hinv : StepInv q i st) :
    StepInv q (i + 1) (stepState q.width st) := by
  obtain ⟨hst1, hlen, hW, hsub, hunits, hSat, hsc⟩ := hinv
  rcases st with ⟨idx, F, ans⟩
  dsimp only at hst1 hlen hW hsub hunits hSat hsc
  subst hst1
  dsimp only [stepState, nextBit]
  set q0 : Dense.Input := ⟨q.width, unitRow q.width idx false :: F⟩
  set q1 : Dense.Input := ⟨q.width, unitRow q.width idx true :: F⟩
  have hdec0 : Dense.decide q0 = true ↔
      ∃ a : List Bool, a.length = q.width ∧ Dense.Holds F a ∧ a.getD idx false = false :=
    decide_unitRow_eq_true_iff hW hi
  have hdec1 : Dense.decide q1 = true ↔
      ∃ a : List Bool, a.length = q.width ∧ Dense.Holds F a ∧ a.getD idx false = true :=
    decide_unitRow_eq_true_iff hW hi
  have hW_b (b : Bool) : Dense.Width q.width (unitRow q.width idx b :: F) := fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact length_unitRow_coeffs q.width idx b
    · exact hW e he
  have hsub_b (b : Bool) : ∀ e ∈ q.rows, e ∈ unitRow q.width idx b :: F :=
    fun e he => List.mem_cons_of_mem _ (hsub e he)
  have hunits_b (b : Bool) : ∀ k < idx + 1,
      unitRow q.width k ((ans ++ [b]).getD k false) ∈ unitRow q.width idx b :: F := by
    intro k hk
    by_cases hki : k < idx
    · have hget : (ans ++ [b]).getD k false = ans.getD k false := by
        rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega),
          List.getD_eq_getElem _ _ (by omega), List.getElem_append_left (by omega)]
      rw [hget]
      exact List.mem_cons_of_mem _ (hunits k hki)
    · have hk_eq : k = idx := by omega
      subst hk_eq
      have hget : (ans ++ [b]).getD k false = b := by
        rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [hlen]
      rw [hget]
      exact List.mem_cons_self
  have hstep_core (b : Bool) (hsat_b : Dense.Satisfiable q.width (unitRow q.width idx b :: F))
      (hsc_b : score ⟨q.width, F⟩ ≤ score ⟨q.width, unitRow q.width idx b :: F⟩) :
      StepInv q (idx + 1) (idx + 1, unitRow q.width idx b :: F, ans ++ [b]) :=
    ⟨rfl, by simp [hlen], hW_b b, hsub_b b, hunits_b b, hsat_b, hsc.trans hsc_b⟩
  cases hs0 : Dense.decide q0 <;> cases hs1 : Dense.decide q1
  · obtain ⟨a, ha, hh⟩ := hSat
    cases hget : a.getD idx false
    · exact absurd (hdec0.mpr ⟨a, ha, hh, hget⟩) (by simp [hs0])
    · exact absurd (hdec1.mpr ⟨a, ha, hh, hget⟩) (by simp [hs1])
  · -- Only `x_idx = true` is satisfiable: all solutions already have `x_idx = true`, so
    -- adding `unitRow q.width idx true` does not change the solution set or `score`.
    have hS1 : Dense.Satisfiable q.width q1.rows := ((Dense.decide_eq_true_iff q1).mp hs1).2
    have hsc_eq : score ⟨q.width, F⟩ = score q1 := by
      have hsol : solSet q.width q1.rows = solSet q.width F := by
        rw [solSet_unitRow_eq_filter hi, Finset.filter_eq_self]
        intro a ha
        obtain ⟨hlen_a, hh_a⟩ := mem_solSet_iff.mp ha
        cases hget : a.getD idx false with
        | false => exact absurd (hdec0.mpr ⟨a, hlen_a, hh_a, hget⟩) (by simp [hs0])
        | true => rfl
      have h1 := two_mul_sum_weight_eq_card_mul_score (q := ⟨q.width, F⟩) hW hSat
      have h2 := two_mul_sum_weight_eq_card_mul_score (q := q1) (hW_b true) hS1
      rw [hsol] at h2
      have hpos : 0 < (solSet q.width F).card := by
        obtain ⟨a, ha, hh⟩ := hSat
        exact Finset.card_pos.mpr ⟨a, mem_solSet_iff.mpr ⟨ha, hh⟩⟩
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
    simpa [hs0, hs1] using hstep_core true hS1 (le_of_eq hsc_eq)
  · -- Only `x_idx = false` is satisfiable.
    have hS0 : Dense.Satisfiable q.width q0.rows := ((Dense.decide_eq_true_iff q0).mp hs0).2
    have hsc_eq : score ⟨q.width, F⟩ = score q0 := by
      have hsol : solSet q.width q0.rows = solSet q.width F := by
        rw [solSet_unitRow_eq_filter hi, Finset.filter_eq_self]
        intro a ha
        obtain ⟨hlen_a, hh_a⟩ := mem_solSet_iff.mp ha
        cases hget : a.getD idx false with
        | false => rfl
        | true => exact absurd (hdec1.mpr ⟨a, hlen_a, hh_a, hget⟩) (by simp [hs1])
      have h1 := two_mul_sum_weight_eq_card_mul_score (q := ⟨q.width, F⟩) hW hSat
      have h2 := two_mul_sum_weight_eq_card_mul_score (q := q0) (hW_b false) hS0
      rw [hsol] at h2
      have hpos : 0 < (solSet q.width F).card := by
        obtain ⟨a, ha, hh⟩ := hSat
        exact Finset.card_pos.mpr ⟨a, mem_solSet_iff.mpr ⟨ha, hh⟩⟩
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
    simpa [hs0, hs1] using hstep_core false hS0 (le_of_eq hsc_eq)
  · -- Both `x_idx = false` and `x_idx = true` are satisfiable.
    have hS0 : Dense.Satisfiable q.width q0.rows := ((Dense.decide_eq_true_iff q0).mp hs0).2
    have hS1 : Dense.Satisfiable q.width q1.rows := ((Dense.decide_eq_true_iff q1).mp hs1).2
    have hmax := score_le_max_branch hW hi hs0 hs1
    by_cases hcmp : score q0 ≤ score q1
    · simp only [Bool.and_self, ↓reduceIte, hcmp, decide_true]
      exact hstep_core true hS1 (hmax.trans (max_le hcmp le_rfl))
    · simp only [Bool.and_self, ↓reduceIte, hcmp, decide_false]
      have hcmp' : score ⟨q.width, unitRow q.width idx true :: F⟩ ≤
          score ⟨q.width, unitRow q.width idx false :: F⟩ := by
        dsimp only [q0, q1] at hcmp
        omega
      exact hstep_core false hS0 (hmax.trans (max_le le_rfl hcmp'))

private theorem stepInv_final {q : Dense.Input} (hW : Dense.Width q.width q.rows)
    (hS : Dense.Satisfiable q.width q.rows) :
    StepInv q q.width ((stepState q.width)^[q.width] (0, q.rows, [])) := by
  have htrace : ∀ i ≤ q.width, StepInv q i ((stepState q.width)^[i] (0, q.rows, [])) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨rfl, rfl, hW, fun _ h => h, fun _ hk => absurd hk (Nat.not_lt_zero _), hS, le_rfl⟩
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply']
      exact stepInv_preserve (by omega) (ih (by omega))
  exact htrace q.width le_rfl

/-- `solve q` always outputs a Boolean word of length `q.width`. -/
theorem solve_length (q : Dense.Input) : (solve q).length = q.width := by
  have hlen : ∀ i, (((stepState q.width)^[i] (0, q.rows, [])).2.2).length = i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      simp [stepState, ih]
  exact hlen q.width

/-- For any satisfiable well-width system `q`, `solve q` satisfies every equation of `q`. -/
theorem solve_holds {q : Dense.Input} (hW : Dense.Width q.width q.rows)
    (hS : Dense.Satisfiable q.width q.rows) :
    Dense.Holds q.rows (solve q) := by
  obtain ⟨_, hlen, _, hsub, hunits, ⟨a, ha, hholds⟩, _⟩ := stepInv_final hW hS
  have heq : a = solve q := by
    apply List.ext_getElem (ha.trans hlen.symm)
    intro k hk₁ hk₂
    have hk : k < q.width := ha ▸ hk₁
    have hu := hholds (unitRow q.width k ((solve q).getD k false)) (hunits k hk)
    rw [dot_unitRow_eq ha hk, List.getD_eq_getElem _ _ hk₁] at hu
    dsimp only [unitRow, solve] at hu
    rw [List.getD_eq_getElem _ _ hk₂] at hu
    exact hu
  rw [← heq]
  exact fun e he => hholds e (hsub e he)

/-- **KSTW 1/2-approximation bound**
: for any well-width linear system `q` mod `2` and any solution `a` of `q`,
`solve q` sets at least half as many variables to `1` as `a`.
-/
theorem solve_approx {q : Dense.Input} {a : List Bool} (hW : Dense.Width q.width q.rows)
    (ha : a.length = q.width) (hholds : Dense.Holds q.rows a) :
    a.count true ≤ 2 * (solve q).count true := by
  have hS : Dense.Satisfiable q.width q.rows := ⟨a, ha, hholds⟩
  obtain ⟨_, hlen, hWf, _, hunits, hSf, hsc⟩ := stepInv_final hW hS
  set Ff := ((stepState q.width)^[q.width] (0, q.rows, [])).2.1
  have hsol_eq : ∀ b, b ∈ solSet q.width Ff ↔ b = solve q := by
    intro b
    rw [mem_solSet_iff]
    constructor
    · rintro ⟨hb, hhb⟩
      apply List.ext_getElem (hb.trans hlen.symm)
      intro k hk₁ hk₂
      have hk : k < q.width := hb ▸ hk₁
      have hu := hhb (unitRow q.width k ((solve q).getD k false)) (hunits k hk)
      rw [dot_unitRow_eq hb hk, List.getD_eq_getElem _ _ hk₁] at hu
      dsimp only [unitRow, solve] at hu
      rw [List.getD_eq_getElem _ _ hk₂] at hu
      exact hu
    · rintro rfl
      obtain ⟨c, hc, hhc⟩ := hSf
      have hce : c = solve q := by
        apply List.ext_getElem (hc.trans hlen.symm)
        intro k hk₁ hk₂
        have hk : k < q.width := hc ▸ hk₁
        have hu := hhc (unitRow q.width k ((solve q).getD k false)) (hunits k hk)
        rw [dot_unitRow_eq hc hk, List.getD_eq_getElem _ _ hk₁] at hu
        dsimp only [unitRow, solve] at hu
        rw [List.getD_eq_getElem _ _ hk₂] at hu
        exact hu
      exact hce ▸ ⟨hc, hhc⟩
  have hset : solSet q.width Ff = {solve q} := by
    ext b; simp [hsol_eq]
  have hid := two_mul_sum_weight_eq_card_mul_score (q := ⟨q.width, Ff⟩) hWf hSf
  rw [hset, Finset.sum_singleton, Finset.card_singleton, Nat.one_mul] at hid
  have hwa : a.count true ≤ score q := weight_le_score hW ha hholds
  omega

private theorem computableInPolyTime_unitRow :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => unitRow p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBool) Dense.encRow := by
  have hcoeffs : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Bool => (List.range p.1.1).map fun i => decide (i = p.1.2))
      (encPair (encPair encUnary encUnary) encBool) encBits :=
    ComputableInPolyTime.listToBits.comp
      (ComputableInPolyTime.mapWithInput (by fun_prop) (by fun_prop))
  unfold unitRow
  fun_prop

private theorem computableInPolyTime_score :
    ComputableInPolyTime score Dense.encInput encUnary := by
  have h1 : ComputableInPolyTime
      (fun q : Dense.Input =>
        (List.range q.width).countP fun j =>
          Dense.decide ⟨q.width, unitRow q.width j true :: q.rows⟩)
      Dense.encInput encUnary := by
    have htest : ComputableInPolyTime
        (fun p : Dense.Input × ℕ =>
          Dense.decide ⟨p.1.width, unitRow p.1.width p.2 true :: p.1.rows⟩)
        (encPair Dense.encInput encUnary) encBool := by
      have hargs : ComputableInPolyTime
          (fun p : Dense.Input × ℕ => ((p.1.width, p.2), true))
          (encPair Dense.encInput encUnary) (encPair (encPair encUnary encUnary) encBool) := by
        fun_prop
      have hu : ComputableInPolyTime
          (fun p : Dense.Input × ℕ => unitRow p.1.width p.2 true)
          (encPair Dense.encInput encUnary) Dense.encRow :=
        computableInPolyTime_unitRow.comp hargs
      have hq : ComputableInPolyTime
          (fun p : Dense.Input × ℕ =>
            (⟨p.1.width, unitRow p.1.width p.2 true :: p.1.rows⟩ : Dense.Input))
          (encPair Dense.encInput encUnary) Dense.encInput := by fun_prop
      exact Dense.computableInPolyTime_decide.comp hq
    exact ComputableInPolyTime.countPWithInput (by fun_prop) htest
  have h2 : ComputableInPolyTime
      (fun q : Dense.Input =>
        (List.range q.width).countP fun j =>
          !Dense.decide ⟨q.width, unitRow q.width j false :: q.rows⟩)
      Dense.encInput encUnary := by
    have htest : ComputableInPolyTime
        (fun p : Dense.Input × ℕ =>
          !Dense.decide ⟨p.1.width, unitRow p.1.width p.2 false :: p.1.rows⟩)
        (encPair Dense.encInput encUnary) encBool := by
      have hargs : ComputableInPolyTime
          (fun p : Dense.Input × ℕ => ((p.1.width, p.2), false))
          (encPair Dense.encInput encUnary) (encPair (encPair encUnary encUnary) encBool) := by
        fun_prop
      have hu : ComputableInPolyTime
          (fun p : Dense.Input × ℕ => unitRow p.1.width p.2 false)
          (encPair Dense.encInput encUnary) Dense.encRow :=
        computableInPolyTime_unitRow.comp hargs
      have hq : ComputableInPolyTime
          (fun p : Dense.Input × ℕ =>
            (⟨p.1.width, unitRow p.1.width p.2 false :: p.1.rows⟩ : Dense.Input))
          (encPair Dense.encInput encUnary) Dense.encInput := by fun_prop
      exact ComputableInPolyTime.bool_not.comp (Dense.computableInPolyTime_decide.comp hq)
    exact ComputableInPolyTime.countPWithInput (by fun_prop) htest
  unfold score
  exact ComputableInPolyTime.unary_add' h1 h2

private abbrev encState : (ℕ × Dense.System × List Bool) ↪ List Bool :=
  encPair encUnary (encPair Dense.encSystem encBits)

private theorem computableInPolyTime_nextBit :
    ComputableInPolyTime (fun p : ℕ × (ℕ × Dense.System × List Bool) => nextBit p.1 p.2)
      (encPair encUnary encState) encBool := by
  have hargs0 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => ((p.1, p.2.1), false))
      (encPair encUnary encState) (encPair (encPair encUnary encUnary) encBool) := by fun_prop
  have hu0 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => unitRow p.1 p.2.1 false)
      (encPair encUnary encState) Dense.encRow :=
    computableInPolyTime_unitRow.comp hargs0
  have hargs1 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => ((p.1, p.2.1), true))
      (encPair encUnary encState) (encPair (encPair encUnary encUnary) encBool) := by fun_prop
  have hu1 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => unitRow p.1 p.2.1 true)
      (encPair encUnary encState) Dense.encRow :=
    computableInPolyTime_unitRow.comp hargs1
  have hq0 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        (⟨p.1, unitRow p.1 p.2.1 false :: p.2.2.1⟩ : Dense.Input))
      (encPair encUnary encState) Dense.encInput := by fun_prop
  have hq1 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        (⟨p.1, unitRow p.1 p.2.1 true :: p.2.2.1⟩ : Dense.Input))
      (encPair encUnary encState) Dense.encInput := by fun_prop
  have hs0 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        Dense.decide ⟨p.1, unitRow p.1 p.2.1 false :: p.2.2.1⟩)
      (encPair encUnary encState) encBool :=
    Dense.computableInPolyTime_decide.comp hq0
  have hs1 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        Dense.decide ⟨p.1, unitRow p.1 p.2.1 true :: p.2.2.1⟩)
      (encPair encUnary encState) encBool :=
    Dense.computableInPolyTime_decide.comp hq1
  have hsc0 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        score ⟨p.1, unitRow p.1 p.2.1 false :: p.2.2.1⟩)
      (encPair encUnary encState) encUnary :=
    computableInPolyTime_score.comp hq0
  have hsc1 : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        score ⟨p.1, unitRow p.1 p.2.1 true :: p.2.2.1⟩)
      (encPair encUnary encState) encUnary :=
    computableInPolyTime_score.comp hq1
  dsimp only [nextBit]
  fun_prop

private theorem computableInPolyTime_stepState :
    ComputableInPolyTime (fun p : ℕ × (ℕ × Dense.System × List Bool) => stepState p.1 p.2)
      (encPair encUnary encState) encState := by
  have hb := computableInPolyTime_nextBit
  have hargsb : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => ((p.1, p.2.1), nextBit p.1 p.2))
      (encPair encUnary encState) (encPair (encPair encUnary encUnary) encBool) := by fun_prop
  have hub : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => unitRow p.1 p.2.1 (nextBit p.1 p.2))
      (encPair encUnary encState) Dense.encRow :=
    computableInPolyTime_unitRow.comp hargsb
  have hrow_cons : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) =>
        unitRow p.1 p.2.1 (nextBit p.1 p.2) :: p.2.2.1)
      (encPair encUnary encState) Dense.encSystem := by fun_prop
  have hsingleton : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => [nextBit p.1 p.2])
      (encPair encUnary encState) encBits :=
    ComputableInPolyTime.listToBits.comp (ComputableInPolyTime.cons' hb (.const []))
  have hans_new : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => p.2.2.2 ++ [nextBit p.1 p.2])
      (encPair encUnary encState) encBits :=
    ComputableInPolyTime.bitsAppend (by fun_prop) hsingleton
  have hi : ComputableInPolyTime
      (fun p : ℕ × (ℕ × Dense.System × List Bool) => p.2.1 + 1)
      (encPair encUnary encState) encUnary := by fun_prop
  exact hi.prod (hrow_cons.prod hans_new)

private theorem length_encRow_unitRow (n j : ℕ) (b : Bool) :
    (Dense.encRow (unitRow n j b)).length = 2 * n + 2 := by
  have h1 : (unitRow n j b).coeffs.length = n := length_unitRow_coeffs n j b
  enc_len [Dense.encRow_apply, h1]

private theorem length_encState_stepState (n : ℕ) (st : ℕ × Dense.System × List Bool) :
    (encState (stepState n st)).length ≤ (encState st).length + (8 * n + 13) := by
  have hrow := length_encRow_unitRow n st.1 (nextBit n st)
  dsimp only [stepState, encState, Dense.encSystem]
  enc_len [hrow]

/-- The derandomized `1/2`-approximation algorithm `solve` is computable in polynomial time
on native multi-tape Turing machines. -/
theorem computableInPolyTime_solve :
    ComputableInPolyTime solve Dense.encInput encBits := by
  have hloop : ComputableInPolyTime
      (fun q : Dense.Input => (stepState q.width)^[q.width] (0, q.rows, []))
      Dense.encInput encState := by
    refine ComputableInPolyTime.iterateWith (par := Dense.Input.width)
      (count := Dense.Input.width) (init := fun q => (0, q.rows, []))
      (step := stepState) (by fun_prop) (by fun_prop) (by fun_prop)
      computableInPolyTime_stepState
      (bound := fun q => (encState (0, q.rows, [])).length + q.width * (8 * q.width + 13))
      ?_ ?_
    · have hinit : ComputableInPolyTime (fun q : Dense.Input => (0, q.rows, ([] : List Bool)))
          Dense.encInput encState := by fun_prop
      have hlen : ComputableInPolyTime Dense.Input.width Dense.encInput encUnary := by fun_prop
      exact hinit.polyBounded_length.add
        (hlen.polyBounded.mul (((PolyBounded.const 8).mul hlen.polyBounded).add (.const 13)))
    · intro q i hi
      have htrace : ∀ k, (encState ((stepState q.width)^[k] (0, q.rows, []))).length ≤
          (encState (0, q.rows, [])).length + k * (8 * q.width + 13) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          have hstep := length_encState_stepState q.width ((stepState q.width)^[k] (0, q.rows, []))
          have hmul : (k + 1) * (8 * q.width + 13) = k * (8 * q.width + 13) + (8 * q.width + 13) :=
            Nat.succ_mul k (8 * q.width + 13)
          omega
      have hle : i * (8 * q.width + 13) ≤ q.width * (8 * q.width + 13) :=
        Nat.mul_le_mul_right _ hi
      exact (htrace i).trans (Nat.add_le_add_left hle _)
  unfold solve
  exact (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hloop)

end Cslib.Complexity.XORSAT.MaxOnes
