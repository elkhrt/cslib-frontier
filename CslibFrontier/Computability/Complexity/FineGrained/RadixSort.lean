/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Least-Significant-Digit Radix Sort on Multi-Tape Turing Machines

This module develops reusable streaming list combinators and least-significant-digit (LSD) binary
radix sort on framed list encodings `Turing.MultiTapeTM.encList` for deterministic multi-tape
Turing machines. Because each bit-partitioning pass is a permutation of the input list, the
encoded list length `encList enc l` is invariant across all passes, yielding a quasi-linear
running-time bound linear in the number of items and polynomial in the maximum item bit-length.

## Main definitions

* `CslibFrontier.Complexity.streamList`: single-pass streaming transducer over a list with state.
* `CslibFrontier.Complexity.radixPassBy`, `CslibFrontier.Complexity.radixStepBy`,
  `CslibFrontier.Complexity.radixSortBy`: stable LSD binary radix sort by a natural-number key.
* `CslibFrontier.Complexity.radixSortNat`: LSD binary radix sort on `List ℕ`.
* `CslibFrontier.Complexity.strictChainBool`: streaming strict-increase test on a sorted list.

## Main results

* `CslibFrontier.Complexity.computableInO_streamList`,
  `CslibFrontier.Complexity.computableInO_streamFold`,
  `CslibFrontier.Complexity.computableInO_streamFilterWith`,
  `CslibFrontier.Complexity.computableInO_streamMapWith`: linear-pass streaming combinators in
  `Turing.MultiTapeTM.ComputableInO`.
* `CslibFrontier.Complexity.radixSortBy_perm`,
  `CslibFrontier.Complexity.length_encList_radixSortBy`,
  `CslibFrontier.Complexity.pairwise_radixSortBy`: permutation, exact encoded-length invariance, and
  sortedness of `radixSortBy`.
* `CslibFrontier.Complexity.computableInO_radixSortBy`: multi-tape Turing machine time and space
  bound
  for `radixSortBy`.
* `CslibFrontier.Complexity.computableInO_radixSortNat`,
  `CslibFrontier.Complexity.computableInO_decide_nodup_nat`: quasi-linear sorting and duplicate
  detection on `List ℕ`.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM

section Streaming

variable {α β γ σ : Type}

/-- Single-pass streaming transducer over a list from initial state `s`, emitting `emit (s, a)` and
advancing to `next (s, a)` at each element `a`. -/
@[expose] def streamList (next : σ × α → σ) (emit : σ × α → List β) : σ → List α → List β
  | _, [] => []
  | s, a :: l => emit (s, a) ++ streamList next emit (next (s, a)) l

@[simp]
theorem streamList_nil (next : σ × α → σ) (emit : σ × α → List β) (s : σ) :
    streamList next emit s [] = [] := rfl

@[simp]
theorem streamList_cons (next : σ × α → σ) (emit : σ × α → List β) (s : σ) (a : α) (l : List α) :
    streamList next emit s (a :: l) = emit (s, a) ++ streamList next emit (next (s, a)) l := rfl

theorem encList_streamList (encB : β ↪ List Bool) (next : σ × α → σ) (emit : σ × α → List β)
    (s : σ) (l : List α) :
    encList encB (streamList next emit s l) =
      streamEmit next (fun p => encList encB (emit p)) s l := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [streamList_cons, encList_append, streamEmit, ih]

theorem streamList_filter (pred : σ × α → Bool) (s : σ) (l : List α) :
    streamList Prod.fst (fun p => if pred p then [p.2] else []) s l =
      l.filter (fun a => pred (s, a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [streamList_cons, ih, List.filter_cons]
    cases pred (s, a) <;> simp

theorem streamList_map (f : σ × α → β) (s : σ) (l : List α) :
    streamList Prod.fst (fun p => [f p]) s l = l.map (fun a => f (s, a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem streamState_fst (s : σ) (l : List α) (j : ℕ) :
    streamState s (Prod.fst : σ × α → σ) l j = s := by
  unfold streamState
  generalize l.take j = t
  induction t <;> simp [*]

/-- A single-pass streaming list transducer with polynomial-time callbacks runs in time and
charged space `O((encIn x).length + ((elems x).length + 1) * (lMax x + 1) ^ d)`. -/
theorem computableInO_streamList {encA : α ↪ List Bool} {encS : σ ↪ List Bool}
    {encB : β ↪ List Bool} {encIn : γ ↪ List Bool}
    (init : γ → σ) (elems : γ → List α)
    (hL : ∀ x, encIn x = encPair encS (encList encA) (init x, elems x))
    {next : σ × α → σ} {emit : σ × α → List β} {g : γ → List β}
    (hnext : ComputableInPolyTime next (encPair encS encA) encS)
    (hemit : ComputableInPolyTime emit (encPair encS encA) (encList encB))
    (hg : ∀ x, g x = streamList next emit (init x) (elems x))
    {lMax : γ → ℕ}
    (hS : ∀ x j, j ≤ (elems x).length →
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ d, ComputableInO g encIn (encList encB)
      (fun x => (encIn x).length + ((elems x).length + 1) * (lMax x + 1) ^ d)
      (fun x => (encIn x).length + ((elems x).length + 1) * (lMax x + 1) ^ d) := by
  obtain ⟨c, d, hc⟩ := ComputableInTimeAndSpace.streamFold_pair_list (g := g)
    init elems hL hnext hemit (fun x => by rw [hg x, encList_streamList]) hS hA
  refine ⟨d, ComputableInO.of_bounds hc c (fun _ => le_rfl) (fun x => ?_) (fun x => ?_)⟩
  · apply Nat.mul_le_mul_left c
    have h1 : (lMax x + 1) ^ d ≤ ((elems x).length + 1) * (lMax x + 1) ^ d :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  · exact hc.length_le x

private theorem streamEmit_empty (next : σ × α → σ) (s : σ) (l : List α) :
    streamEmit next (fun _ => ([] : List Bool)) s l = [] := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [streamEmit, ih]

/-- A single-pass streaming state fold `(elems x).foldl (fun s a => next (s, a)) (init x)` over a
pair-encoded input `(init x, elems x)` runs in linear input scan time plus per-element polynomial
work in `lMax x`, and polynomial workspace in `lMax x`. -/
theorem computableInO_streamFold {encA : α ↪ List Bool} {encS : σ ↪ List Bool}
    {encIn : γ ↪ List Bool}
    (init : γ → σ) (elems : γ → List α)
    (hL : ∀ x, encIn x = encPair encS (encList encA) (init x, elems x))
    {next : σ × α → σ}
    (hnext : ComputableInPolyTime next (encPair encS encA) encS)
    {lMax : γ → ℕ}
    (hS : ∀ x j, j ≤ (elems x).length →
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ d, ComputableInO (fun x => (elems x).foldl (fun s a => next (s, a)) (init x)) encIn encS
      (fun x => (encIn x).length + ((elems x).length + 1) * (lMax x + 1) ^ d)
      (fun x => (lMax x + 1) ^ d) := by
  obtain ⟨cn, dn, _, _, _, tmn, htn⟩ := Internal.NormalForm.polyTime hnext
  have hemitPt : ComputableInPolyTime (fun _ : σ × α => ([] : List Bool))
      (encPair encS encA) encBits := by fun_prop
  obtain ⟨ce, de, _, _, _, tme, hte⟩ := Internal.NormalForm.polyTime hemitPt
  let d := max dn de + 1
  let K := 3 ^ d * (cn + ce + 1) + 4
  have hstep_pow : ∀ x j (hj : j < (elems x).length),
      cn * ((encPair encS encA (streamState (init x) next (elems x) j, (elems x)[j])).length +
          1) ^ dn ≤ cn * (3 ^ d * (lMax x + 1) ^ d) ∧
        ce * ((encPair encS encA (streamState (init x) next (elems x) j, (elems x)[j])).length +
            1) ^ de ≤ ce * (3 ^ d * (lMax x + 1) ^ d) := by
    intro x j hj
    have hs0 := hS x j hj.le
    have ha := hA x j hj
    have hlen_p : (encPair encS encA (streamState (init x) next (elems x) j,
        (elems x)[j])).length + 1 ≤ 3 * (lMax x + 1) := by
      simp only [length_encPair]; omega
    have hpow_le : ∀ {e : ℕ}, e ≤ d →
        ((encPair encS encA (streamState (init x) next (elems x) j,
          (elems x)[j])).length + 1) ^ e ≤ 3 ^ d * (lMax x + 1) ^ d := fun he =>
      (Nat.pow_le_pow_left hlen_p _).trans
        ((Nat.pow_le_pow_right (by omega) he).trans_eq (Nat.mul_pow _ _ _))
    exact ⟨Nat.mul_le_mul_left _ (hpow_le (by omega)),
      Nat.mul_le_mul_left _ (hpow_le (by omega))⟩
  obtain ⟨c, hc⟩ := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun x => (elems x).foldl (fun s a => next (s, a)) (init x))
    (encOut := encS) (encE := encBits) (encF := encS)
    Internal.NativeCompiler.frameValueReader (fun a => frame (encA a))
    (fun a => frame_ne_nil (encA a))
    (fun a rest => Internal.NativeCompiler.read_frameValueReader (encA a) rest)
    init elems (fun x => by rw [hL x, encPair_apply]; rfl)
    ⟨_, _, inferInstance, tmn, htn⟩ ⟨_, _, inferInstance, tme, hte⟩
    computableTidilyInTimeAndSpace_id
    (fun x => by
      simp only [encBits_apply, streamEmit_empty, List.nil_append, id_eq, streamState,
        List.take_length])
    (roundCost := fun x _ => K * (lMax x + 1) ^ d)
    (sMax := fun x => K * (lMax x + 1) ^ d)
    (lMax := lMax)
    (fun x j hj => by
      obtain ⟨h1, h2⟩ := hstep_pow x j hj
      have hl1 : lMax x + 1 ≤ (lMax x + 1) ^ d := Nat.le_self_pow (by omega) _
      have h3mul : 3 * (lMax x + 1) ^ d ≤ 3 ^ d * (lMax x + 1) ^ d :=
        Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 3)
      dsimp only [K]
      linarith [hS x j hj.le, hS x (j + 1) hj, hA x j hj, h1, h2, hl1, h3mul])
    (fun x j hj => by
      obtain ⟨h1, h2⟩ := hstep_pow x j hj
      calc _ ≤ cn * (3 ^ d * (lMax x + 1) ^ d) + ce * (3 ^ d * (lMax x + 1) ^ d) :=
            Nat.add_le_add h1 h2
        _ = (3 ^ d * (cn + ce)) * (lMax x + 1) ^ d := by ring
        _ ≤ K * (lMax x + 1) ^ d := Nat.mul_le_mul_right _
            ((Nat.mul_le_mul_left (3 ^ d) (Nat.le_succ (cn + ce))).trans (Nat.le_add_right _ 4)))
    hS hA
  have hl (x : γ) : lMax x ≤ (lMax x + 1) ^ d :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
  have hplain := ComputableTidilyInTimeAndSpace.computableInTimeAndSpace hc
  refine ⟨d, ComputableInO.of_bounds hplain ((c + 1) * (K + 8)) (fun x => ?_) (fun x => ?_)
    (fun x => ?_)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hfin := hS x (elems x).length le_rfl
    simp only [streamState, List.take_length] at hfin ⊢
    have hlx := hl x
    set A := (encIn x).length
    set B := ((elems x).length + 1) * (lMax x + 1) ^ d
    have hKl : (elems x).length * (K * (lMax x + 1) ^ d) ≤ K * B := by
      calc (elems x).length * (K * (lMax x + 1) ^ d)
          = K * ((elems x).length * (lMax x + 1) ^ d) := by ring
        _ ≤ K * B := Nat.mul_le_mul_left K (Nat.mul_le_mul_right _ (Nat.le_succ _))
    have hB_ge : lMax x ≤ B := hlx.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hbase : 2 * (encS ((elems x).foldl (fun s a => next (s, a)) (init x))).length + 4 + A +
        (elems x).length * (K * (lMax x + 1) ^ d) + lMax x + 1 ≤ (K + 8) * (A + B + 1) := by
      nlinarith
    exact (Nat.mul_le_mul_left c hbase).trans
      (Nat.mul_le_mul_right _ (Nat.le_succ c) |>.trans_eq (Nat.mul_assoc ..).symm)
  · simp only [zero_add]
    have hbase : K * (lMax x + 1) ^ d + lMax x + 1 ≤ (K + 8) * ((lMax x + 1) ^ d + 1) := by
      nlinarith [hl x]
    exact (Nat.mul_le_mul_left c hbase).trans
      (Nat.mul_le_mul_right _ (Nat.le_succ c) |>.trans_eq (Nat.mul_assoc ..).symm)
  · have hfin := hS x (elems x).length le_rfl
    simp only [streamState, List.take_length] at hfin
    have hlx := hl x
    have h1 : 1 ≤ (c + 1) * (K + 8) := Nat.mul_pos (Nat.succ_pos c) (by omega)
    exact (hfin.trans (hlx.trans (Nat.le_succ _))).trans (Nat.le_mul_of_pos_left _ h1)

/-- Single-pass streaming `List.filter` with a polynomial-time predicate `pred : σ × α → Bool`. -/
theorem computableInO_streamFilterWith {encA : α ↪ List Bool} {encS : σ ↪ List Bool}
    (pred : σ × α → Bool) (hpred : ComputableInPolyTime pred (encPair encS encA) encBool)
    {lMax : σ × List α → ℕ}
    (hS : ∀ p : σ × List α, (encS p.1).length ≤ lMax p)
    (hA : ∀ (p : σ × List α) j (hj : j < p.2.length), (encA p.2[j]).length ≤ lMax p) :
    ∃ d, ComputableInO (fun p : σ × List α => p.2.filter (fun a => pred (p.1, a)))
      (encPair encS (encList encA)) (encList encA)
      (fun p => (encPair encS (encList encA) p).length + (p.2.length + 1) * (lMax p + 1) ^ d)
      (fun p => (encPair encS (encList encA) p).length + (p.2.length + 1) * (lMax p + 1) ^ d) := by
  have hnext : ComputableInPolyTime (Prod.fst : σ × α → σ) (encPair encS encA) encS := by fun_prop
  have hemit : ComputableInPolyTime (fun q : σ × α => if pred q then [q.2] else [])
      (encPair encS encA) (encList encA) := by fun_prop
  exact computableInO_streamList Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (fun p => (streamList_filter pred p.1 p.2).symm)
    (fun p j _ => by rw [streamState_fst]; exact hS p) hA

/-- Single-pass streaming `List.map` with a polynomial-time function `f : σ × α → β`. -/
theorem computableInO_streamMapWith {encA : α ↪ List Bool} {encS : σ ↪ List Bool}
    {encB : β ↪ List Bool}
    (f : σ × α → β) (hf : ComputableInPolyTime f (encPair encS encA) encB)
    {lMax : σ × List α → ℕ}
    (hS : ∀ p : σ × List α, (encS p.1).length ≤ lMax p)
    (hA : ∀ (p : σ × List α) j (hj : j < p.2.length), (encA p.2[j]).length ≤ lMax p) :
    ∃ d, ComputableInO (fun p : σ × List α => p.2.map (fun a => f (p.1, a)))
      (encPair encS (encList encA)) (encList encB)
      (fun p => (encPair encS (encList encA) p).length + (p.2.length + 1) * (lMax p + 1) ^ d)
      (fun p => (encPair encS (encList encA) p).length + (p.2.length + 1) * (lMax p + 1) ^ d) := by
  have hnext : ComputableInPolyTime (Prod.fst : σ × α → σ) (encPair encS encA) encS := by fun_prop
  have hemit : ComputableInPolyTime (fun q : σ × α => [f q])
      (encPair encS encA) (encList encB) := by fun_prop
  exact computableInO_streamList Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (fun p => (streamList_map f p.1 p.2).symm)
    (fun p j _ => by rw [streamState_fst]; exact hS p) hA

end Streaming

section RadixSort

variable {α : Type}

/-- Permutations preserve the exact bit-length of `encList enc`. -/
theorem length_encList_of_perm {enc : α ↪ List Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (encList enc l₁).length = (encList enc l₂).length := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [encList_cons, ih]
  | swap a b l => simp [encList_cons, List.length_append, Nat.add_assoc, Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One stable pass of binary radix sort at bit position `k`: elements whose key has bit `k` equal
to `false` precede elements whose key has bit `k` equal to `true`. -/
def radixPassBy (key : α → ℕ) (k : ℕ) (l : List α) : List α :=
  l.filter (fun a => !(key a).testBit k) ++ l.filter (fun a => (key a).testBit k)

/-- One indexed round `(k, l) ↦ (k + 1, radixPassBy key k l)` of LSD binary radix sort. -/
def radixStepBy (key : α → ℕ) (p : ℕ × List α) : ℕ × List α :=
  (p.1 + 1, radixPassBy key p.1 p.2)

/-- Stable least-significant-digit binary radix sort performing `b` bit passes on `l`. -/
def radixSortBy (key : α → ℕ) (b : ℕ) (l : List α) : List α :=
  ((radixStepBy key)^[b] (0, l)).2

theorem radixPassBy_perm (key : α → ℕ) (k : ℕ) (l : List α) :
    (radixPassBy key k l).Perm l := by
  unfold radixPassBy
  have h := List.filter_append_perm (fun a => !(key a).testBit k) l
  simpa only [Bool.not_not] using h

theorem iterate_radixStepBy_fst (key : α → ℕ) (j k : ℕ) (l : List α) :
    ((radixStepBy key)^[j] (k, l)).1 = k + j := by
  induction j generalizing k l with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, radixStepBy, ih]
    omega

theorem iterate_radixStepBy_perm (key : α → ℕ) (j k : ℕ) (l : List α) :
    (((radixStepBy key)^[j] (k, l)).2).Perm l := by
  induction j generalizing k l with
  | zero => exact List.Perm.refl l
  | succ j ih =>
    rw [Function.iterate_succ_apply, radixStepBy]
    exact (ih (k + 1) (radixPassBy key k l)).trans (radixPassBy_perm key k l)

theorem radixSortBy_perm (key : α → ℕ) (b : ℕ) (l : List α) :
    (radixSortBy key b l).Perm l :=
  iterate_radixStepBy_perm key b 0 l

@[simp]
theorem length_radixSortBy (key : α → ℕ) (b : ℕ) (l : List α) :
    (radixSortBy key b l).length = l.length :=
  (radixSortBy_perm key b l).length_eq

@[simp]
theorem mem_radixSortBy {key : α → ℕ} {b : ℕ} {l : List α} {a : α} :
    a ∈ radixSortBy key b l ↔ a ∈ l :=
  (radixSortBy_perm key b l).mem_iff

theorem length_encList_radixSortBy (enc : α ↪ List Bool) (key : α → ℕ) (b : ℕ) (l : List α) :
    (encList enc (radixSortBy key b l)).length = (encList enc l).length :=
  length_encList_of_perm (radixSortBy_perm key b l)

private theorem testBit_eq_div_mod (n k : ℕ) :
    n.testBit k = decide ((n / 2 ^ k) % 2 = 1) := by
  rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

private theorem mod_two_pow_succ_eq (n j : ℕ) :
    n % 2 ^ (j + 1) = n % 2 ^ j + 2 ^ j * (n.testBit j).toNat := by
  rw [Nat.mod_pow_succ, testBit_eq_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h]

private theorem pairwise_mod_radixPassBy (key : α → ℕ) (j : ℕ) {l : List α}
    (h : List.Pairwise (fun x y => key x % 2 ^ j ≤ key y % 2 ^ j) l) :
    List.Pairwise (fun x y => key x % 2 ^ (j + 1) ≤ key y % 2 ^ (j + 1)) (radixPassBy key j l) := by
  unfold radixPassBy
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · refine (h.filter _).imp_of_mem fun {x y} hx hy hxy => ?_
    have hbx : (key x).testBit j = false := by simpa using (List.mem_filter.mp hx).2
    have hby : (key y).testBit j = false := by simpa using (List.mem_filter.mp hy).2
    rw [mod_two_pow_succ_eq (key x) j, mod_two_pow_succ_eq (key y) j, hbx, hby]
    simpa using hxy
  · refine (h.filter _).imp_of_mem fun {x y} hx hy hxy => ?_
    have hbx : (key x).testBit j = true := by simpa using (List.mem_filter.mp hx).2
    have hby : (key y).testBit j = true := by simpa using (List.mem_filter.mp hy).2
    rw [mod_two_pow_succ_eq (key x) j, mod_two_pow_succ_eq (key y) j, hbx, hby]
    simp only [Bool.toNat_true, mul_one]
    omega
  · intro x hx y hy
    have hbx : (key x).testBit j = false := by simpa using (List.mem_filter.mp hx).2
    have hby : (key y).testBit j = true := by simpa using (List.mem_filter.mp hy).2
    have hlt : key x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
    rw [mod_two_pow_succ_eq (key x) j, mod_two_pow_succ_eq (key y) j, hbx, hby]
    simp only [Bool.toNat_false, mul_zero, add_zero, Bool.toNat_true, mul_one]
    omega

private theorem pairwise_mod_iterate_radixStepBy (key : α → ℕ) (j : ℕ) (l : List α) :
    List.Pairwise (fun x y => key x % 2 ^ j ≤ key y % 2 ^ j)
      (((radixStepBy key)^[j] (0, l)).2) := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, Nat.mod_one]
    exact List.pairwise_iff_getElem.mpr fun _ _ _ _ _ => le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', radixStepBy, iterate_radixStepBy_fst, zero_add]
    exact pairwise_mod_radixPassBy key j ih

/-- After `b` passes, `radixSortBy key b l` is sorted in nondecreasing key order whenever all keys
in `l` are strictly less than `2 ^ b`. -/
theorem pairwise_radixSortBy (key : α → ℕ) (b : ℕ) {l : List α}
    (hb : ∀ a ∈ l, key a < 2 ^ b) :
    List.Pairwise (fun x y => key x ≤ key y) (radixSortBy key b l) := by
  refine (pairwise_mod_iterate_radixStepBy key b l).imp_of_mem fun {x y} hx hy hxy => ?_
  have hx' : key x % 2 ^ b = key x := Nat.mod_eq_of_lt (hb x (mem_radixSortBy.mp hx))
  have hy' : key y % 2 ^ b = key y := Nat.mod_eq_of_lt (hb y (mem_radixSortBy.mp hy))
  rwa [hx', hy'] at hxy

private theorem testBit_eq_shiftRight_and (n k : ℕ) :
    n.testBit k = decide ((n >>> k) &&& 1 = 1) := by
  rw [testBit_eq_div_mod, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

private theorem computableInPolyTime_testBit :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1.testBit p.2) (encPair encNat encNat) encBool := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ => decide ((p.1 >>> p.2) &&& 1 = 1))
      (encPair encNat encNat) encBool := by fun_prop
  exact h.of_enc_eq fun p => congrArg encBool (testBit_eq_shiftRight_and p.1 p.2)

/-- One bit-partitioning pass `radixPassBy key` runs in linear scan time plus polynomial per-item
work in the maximum encoded bit-length of `(k, a)`. -/
theorem computableInO_radixPassBy {encA : α ↪ List Bool} {key : α → ℕ}
    (hkey : ComputableInPolyTime key encA encNat) :
    ∃ d, ComputableInO (fun p : ℕ × List α => radixPassBy key p.1 p.2)
      (encPair encNat (encList encA)) (encList encA)
      (fun p => (encPair encNat (encList encA) p).length +
        (p.2.length + 1) *
          (max (encNat p.1).length (listMax (fun a => (encA a).length) p.2) + 1) ^ d)
      (fun p => (encPair encNat (encList encA) p).length +
        (p.2.length + 1) *
          (max (encNat p.1).length (listMax (fun a => (encA a).length) p.2) + 1) ^ d) := by
  let lMax : ℕ × List α → ℕ :=
    fun p => max (encNat p.1).length (listMax (fun a => (encA a).length) p.2)
  have hbit1 : ComputableInPolyTime (fun q : ℕ × α => (key q.2).testBit q.1)
      (encPair encNat encA) encBool :=
    computableInPolyTime_testBit.comp
      ((hkey.comp (by fun_prop : ComputableInPolyTime Prod.snd (encPair encNat encA) encA)).prod
        (by fun_prop : ComputableInPolyTime Prod.fst (encPair encNat encA) encNat))
  have hbit0 : ComputableInPolyTime (fun q : ℕ × α => !(key q.2).testBit q.1)
      (encPair encNat encA) encBool := by fun_prop
  obtain ⟨d₀, hf₀⟩ := computableInO_streamFilterWith (lMax := lMax) _ hbit0
    (fun _ => le_max_left _ _)
    (fun p j hj =>
      (le_listMax (f := fun a => (encA a).length) (List.getElem_mem hj)).trans (le_max_right _ _))
  obtain ⟨d₁, hf₁⟩ := computableInO_streamFilterWith (lMax := lMax) _ hbit1
    (fun _ => le_max_left _ _)
    (fun p j hj =>
      (le_listMax (f := fun a => (encA a).length) (List.getElem_mem hj)).trans (le_max_right _ _))
  have happ := hf₀.append hf₁ (g := fun p : ℕ × List α => radixPassBy key p.1 p.2)
    (encOut := encList encA) (fun p => by simp [radixPassBy])
  refine ⟨d₀ + d₁, happ.mono 2 (fun p => ?_) (fun p => ?_)⟩ <;>
  · have h0 : (lMax p + 1) ^ d₀ ≤ (lMax p + 1) ^ (d₀ + d₁) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right d₀ d₁)
    have h1 : (lMax p + 1) ^ d₁ ≤ (lMax p + 1) ^ (d₀ + d₁) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left d₁ d₀)
    have hm0 := Nat.mul_le_mul_left (p.2.length + 1) h0
    have hm1 := Nat.mul_le_mul_left (p.2.length + 1) h1
    change (encPair encNat (encList encA) p).length + (p.2.length + 1) * (lMax p + 1) ^ d₀ +
        ((encPair encNat (encList encA) p).length + (p.2.length + 1) * (lMax p + 1) ^ d₁) ≤
      2 * ((encPair encNat (encList encA) p).length +
        (p.2.length + 1) * (lMax p + 1) ^ (d₀ + d₁) + 1)
    omega

/-- Least-significant-digit binary radix sort `radixSortBy key (b x) (elems x)` is computable on a
multi-tape Turing machine in `b x + 1` linear-scan passes with invariant list encoding length. -/
theorem computableInO_radixSortBy {γ : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {key : α → ℕ}
    (hkey : ComputableInPolyTime key encA encNat)
    {b : γ → ℕ} {elems : γ → List α} {Tb Sb Tl Sl lMax : γ → ℕ}
    (hb : ComputableInO b encIn encNat Tb Sb)
    (helems : ComputableInO elems encIn (encList encA) Tl Sl)
    (hbMax : ∀ x, (encNat (b x)).length ≤ lMax x)
    (hAMax : ∀ x, ∀ a ∈ elems x, (encA a).length ≤ lMax x) :
    ∃ d, ComputableInO (fun x => radixSortBy key (b x) (elems x)) encIn (encList encA)
      (fun x => Tb x + Tl x + (b x + 1) * ((encList encA (elems x)).length +
        ((elems x).length + 1) * (lMax x + 1) ^ d + ((encNat (b x)).length + 1) ^ 2))
      (fun x => Sb x + Sl x + (encList encA (elems x)).length +
        ((elems x).length + 1) * (lMax x + 1) ^ d + (encNat (b x)).length) := by
  obtain ⟨dp, hpass⟩ := computableInO_radixPassBy hkey
  have hinc : ComputableInO (fun p : ℕ × List α => p.1 + 1)
      (encPair encNat (encList encA)) encNat
      (fun p => (encPair encNat (encList encA) p).length)
      (fun p => (encPair encNat (encList encA) p).length) :=
    (ComputableInO.of_linear .natSucc).comp_linear (ComputableInO.fst encNat (encList encA))
  have hstep : ComputableInO (radixStepBy key)
      (encPair encNat (encList encA)) (encPair encNat (encList encA))
      (fun p => 2 * (encPair encNat (encList encA) p).length +
        (p.2.length + 1) *
          (max (encNat p.1).length (listMax (fun a => (encA a).length) p.2) + 1) ^ dp)
      (fun p => 2 * (encPair encNat (encList encA) p).length +
        (p.2.length + 1) *
          (max (encNat p.1).length (listMax (fun a => (encA a).length) p.2) + 1) ^ dp) := by
    refine (hinc.prod hpass).mono_le (fun _ => ?_) (fun _ => ?_) <;> omega
  have hinit' : ComputableInO (fun x : γ => (0, elems x)) encIn (encPair encNat (encList encA))
      Tl Sl := by
    have hpair0 : ComputableInO (fun l : List α => (0, l)) (encList encA)
        (encPair encNat (encList encA))
        (fun l => (encList encA l).length) (fun l => (encList encA l).length) :=
      ((ComputableInO.constZero 0).prod (ComputableInO.of_eq fun _ => rfl)).mono 2
        (fun _ => by omega) (fun _ => by omega)
    exact hpair0.comp_linear helems
  let R : γ → ℕ := fun x =>
    2 * (2 * (encNat (b x)).length + 1 + (encList encA (elems x)).length) +
      ((elems x).length + 1) * (lMax x + 1) ^ dp
  let B : γ → ℕ := fun x => 2 * (encNat (b x)).length + 1 + (encList encA (elems x)).length
  have hstate (x : γ) (k : ℕ) (hk : k ≤ b x) :
      (encPair encNat (encList encA) ((radixStepBy key)^[k] (0, elems x))).length ≤ B x := by
    have hfst : ((radixStepBy key)^[k] (0, elems x)).1 = k := by
      simpa using iterate_radixStepBy_fst key k 0 (elems x)
    have hperm := iterate_radixStepBy_perm key k 0 (elems x)
    have hlenL := length_encList_of_perm (enc := encA) hperm
    have hlenK : (encNat k).length ≤ (encNat (b x)).length := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le_size hk
    rw [length_encPair, hfst, hlenL]
    dsimp only [B]
    omega
  have hround (x : γ) (k : ℕ) (hk : k ≤ b x) :
      2 * (encPair encNat (encList encA) ((radixStepBy key)^[k] (0, elems x))).length +
        (((radixStepBy key)^[k] (0, elems x)).2.length + 1) *
          (max (encNat ((radixStepBy key)^[k] (0, elems x)).1).length
            (listMax (fun a => (encA a).length) ((radixStepBy key)^[k] (0, elems x)).2) + 1) ^ dp ≤
        R x := by
    have hst := hstate x k hk
    have hfst : ((radixStepBy key)^[k] (0, elems x)).1 = k := by
      simpa using iterate_radixStepBy_fst key k 0 (elems x)
    have hperm := iterate_radixStepBy_perm key k 0 (elems x)
    have hlenK : (encNat k).length ≤ lMax x := by
      refine (?_ : (encNat k).length ≤ (encNat (b x)).length).trans (hbMax x)
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le_size hk
    have hlMax : listMax (fun a => (encA a).length) ((radixStepBy key)^[k] (0, elems x)).2 ≤
        lMax x :=
      listMax_le fun a ha => hAMax x a (hperm.mem_iff.mp ha)
    have hmax : max (encNat ((radixStepBy key)^[k] (0, elems x)).1).length
        (listMax (fun a => (encA a).length) ((radixStepBy key)^[k] (0, elems x)).2) ≤ lMax x := by
      rw [hfst]
      exact max_le hlenK hlMax
    rw [hperm.length_eq]
    have hpow : (max (encNat ((radixStepBy key)^[k] (0, elems x)).1).length
        (listMax (fun a => (encA a).length) ((radixStepBy key)^[k] (0, elems x)).2) + 1) ^ dp ≤
        (lMax x + 1) ^ dp := Nat.pow_le_pow_left (Nat.succ_le_succ hmax) dp
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 hst) (Nat.mul_le_mul_left _ hpow)
  have hiter := (ComputableInO.iterate hb hinit' hstep hround hround hstate).snd'
  refine ⟨dp, hiter.mono 8 (fun x => ?_) (fun x => ?_)⟩
  · set E := (encNat (b x)).length
    set L := (encList encA (elems x)).length
    set M := ((elems x).length + 1) * (lMax x + 1) ^ dp
    have hEsq : 6 * E + 3 ≤ 6 * (E + 1) ^ 2 := by nlinarith
    have hRB : R x + B x + (E + 1) ^ 2 ≤ 7 * (L + M + (E + 1) ^ 2) := by
      change (2 * (2 * E + 1 + L) + M) + (2 * E + 1 + L) + (E + 1) ^ 2 ≤ 7 * (L + M + (E + 1) ^ 2)
      omega
    have hmul : (b x + 1) * (R x + B x + (E + 1) ^ 2) ≤
        7 * ((b x + 1) * (L + M + (E + 1) ^ 2)) :=
      (Nat.mul_le_mul_left (b x + 1) hRB).trans_eq (by ring)
    omega
  · dsimp only [R, B]
    omega

/-- LSD binary radix sort on `List ℕ`, using `(l.foldl max 0).size` bit passes. -/
def radixSortNat (l : List ℕ) : List ℕ :=
  radixSortBy id (l.foldl max 0).size l

theorem radixSortNat_perm (l : List ℕ) : (radixSortNat l).Perm l :=
  radixSortBy_perm id _ l

private theorem foldl_max_ge_of_mem {l : List ℕ} {init x : ℕ} (hx : x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right init x).trans (by
        clear hx ih
        generalize max init x = m
        induction l generalizing m with
        | nil => exact le_rfl
        | cons b l ihl => exact (le_max_left m b).trans (ihl (max m b)))
    · exact ih hx

private theorem foldl_max_le {l : List ℕ} {init B : ℕ} (h0 : init ≤ B) (hl : ∀ x ∈ l, x ≤ B) :
    l.foldl max init ≤ B := by
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    exact ih (max_le h0 (hl a (List.mem_cons_self ..)))
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem pairwise_radixSortNat (l : List ℕ) : List.Pairwise (· ≤ ·) (radixSortNat l) :=
  pairwise_radixSortBy id _ fun _ hx =>
    (foldl_max_ge_of_mem hx).trans_lt (Nat.lt_size_self _)

/-- `radixSortNat` runs in quasi-linear time `O(((encList encNat l).length + 1) * (b + 1) ^ d)`
where `b = listMax Nat.size l`. -/
theorem computableInO_radixSortNat :
    ∃ d, ComputableInO radixSortNat (encList encNat) (encList encNat)
      (fun l => ((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ d)
      (fun l => ((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ d) := by
  have hmaxStep : ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
      (encPair encNat encNat) encNat := by
    have h : ComputableInPolyTime (fun p : ℕ × ℕ => if p.1 ≤ p.2 then p.2 else p.1)
        (encPair encNat encNat) encNat := by fun_prop
    exact h.of_enc_eq fun p => congrArg encNat Nat.max_def
  have hpair0 : ComputableInO (fun l : List ℕ => (0, l)) (encList encNat)
      (encPair encNat (encList encNat))
      (fun l => (encList encNat l).length) (fun l => (encList encNat l).length) :=
    ((ComputableInO.constZero 0).prod (ComputableInO.of_eq fun _ => rfl)).mono 2
      (fun _ => by omega) (fun _ => by omega)
  obtain ⟨dm, hfoldMax⟩ := computableInO_streamFold (lMax := fun p : ℕ × List ℕ =>
      max (encNat p.1).length (listMax Nat.size p.2))
    Prod.fst Prod.snd (fun _ => rfl) hmaxStep
    (fun p j _ => by
      simp only [streamState, encNat_apply, Nat.size_eq_bits_len]
      have hle : ((p.2.take j).foldl max p.1).size ≤ max p.1.size (listMax Nat.size p.2) := by
        rcases le_or_gt ((p.2.take j).foldl max p.1) p.1 with h | h
        · exact (Nat.size_le_size h).trans (le_max_left _ _)
        · have hmem : ∃ x ∈ p.2.take j, (p.2.take j).foldl max p.1 ≤ x := by
            by_contra! hc
            have := foldl_max_le (l := p.2.take j) (init := p.1)
              (B := (p.2.take j).foldl max p.1 - 1) (by omega)
              (fun x hx => Nat.le_sub_one_of_lt (hc x hx))
            omega
          obtain ⟨x, hx, hle'⟩ := hmem
          exact (Nat.size_le_size hle').trans
            ((le_listMax (List.mem_of_mem_take hx)).trans (le_max_right _ _))
      simpa [encNat_apply, Nat.size_eq_bits_len] using hle)
    (fun p j hj => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact (le_listMax (List.getElem_mem hj)).trans (le_max_right _ _))
  have hsizePt : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  obtain ⟨ds, _, hsizeDeg⟩ := hsizePt.exists_degree
  have hbBound (l : List ℕ) : (l.foldl max 0).size ≤ listMax Nat.size l := by
    by_cases hl : l.foldl max 0 = 0
    · simp [hl]
    · have hmem : ∃ x ∈ l, l.foldl max 0 ≤ x := by
        by_contra! hc
        have := foldl_max_le (l := l) (init := 0) (B := l.foldl max 0 - 1) (by omega)
          (fun x hx => Nat.le_sub_one_of_lt (hc x hx))
        omega
      obtain ⟨x, hx, hle⟩ := hmem
      exact (Nat.size_le_size hle).trans (le_listMax hx)
  have hb : ComputableInO (fun l : List ℕ => (l.foldl max 0).size) (encList encNat) encNat
      (fun l => (encList encNat l).length + (l.length + 1) * (listMax Nat.size l + 1) ^ dm +
        (listMax Nat.size l + 1) ^ ds)
      (fun l => (encList encNat l).length + (listMax Nat.size l + 1) ^ dm +
        (listMax Nat.size l + 1) ^ ds) := by
    have h1 := hfoldMax.comp hpair0
    have h2 := hsizeDeg.inO.comp h1
    refine h2.mono 8 (fun l => ?_) (fun l => ?_)
    · dsimp only [Function.comp_apply]
      have hlen0 : (encNat 0).length = 0 := by simp [encNat_apply]
      have hsz : (encNat (l.foldl max 0)).length ≤ listMax Nat.size l := by
        simpa [encNat_apply, Nat.size_eq_bits_len] using hbBound l
      have hpow : ((encNat (l.foldl max 0)).length + 1) ^ ds ≤
          (listMax Nat.size l + 1) ^ ds := Nat.pow_le_pow_left (Nat.succ_le_succ hsz) ds
      rw [length_encPair, hlen0, Nat.zero_max]
      change (encList encNat l).length +
          (2 * 0 + 1 + (encList encNat l).length +
            (l.length + 1) * (listMax Nat.size l + 1) ^ dm) +
          ((encNat (l.foldl max 0)).length + 1) ^ ds ≤ _
      omega
    · dsimp only [Function.comp_apply]
      have hlen0 : (encNat 0).length = 0 := by simp [encNat_apply]
      have hsz : (encNat (l.foldl max 0)).length ≤ listMax Nat.size l := by
        simpa [encNat_apply, Nat.size_eq_bits_len] using hbBound l
      have hpow : ((encNat (l.foldl max 0)).length + 1) ^ ds ≤
          (listMax Nat.size l + 1) ^ ds := Nat.pow_le_pow_left (Nat.succ_le_succ hsz) ds
      rw [hlen0, Nat.zero_max]
      change (encList encNat l).length + (listMax Nat.size l + 1) ^ dm +
          ((encNat (l.foldl max 0)).length + 1) ^ ds ≤ _
      omega
  obtain ⟨dr, hsort⟩ := computableInO_radixSortBy (lMax := listMax Nat.size)
    (by fun_prop : ComputableInPolyTime (id : ℕ → ℕ) encNat encNat)
    hb (ComputableInO.of_eq fun _ => rfl)
    (fun l => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le_self _).trans (hbBound l))
    (fun l a ha => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact le_listMax ha)
  let D := dm + ds + dr + 3
  refine ⟨D, hsort.mono 16 (fun l => ?_) (fun l => ?_)⟩
  · have hlen : l.length ≤ (encList encNat l).length := length_le_length_encList encNat l
    have hbB := hbBound l
    have hbEnc : (encNat (l.foldl max 0).size).length ≤ listMax Nat.size l := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le_self _).trans hbB
    set B := listMax Nat.size l + 1
    have hB1 : 1 ≤ B := Nat.succ_pos _
    have hp1 : B ^ dm ≤ B ^ (dm + ds + dr + 2) := Nat.pow_le_pow_right hB1 (by omega)
    have hp2 : B ^ ds ≤ B ^ (dm + ds + dr + 2) := Nat.pow_le_pow_right hB1 (by omega)
    have hp3 : B ^ dr ≤ B ^ (dm + ds + dr + 2) := Nat.pow_le_pow_right hB1 (by omega)
    have hp4 : B ^ 2 ≤ B ^ (dm + ds + dr + 2) := Nat.pow_le_pow_right hB1 (by omega)
    have hBD : B * B ^ (dm + ds + dr + 2) = B ^ D :=
      (pow_succ' B (dm + ds + dr + 2)).symm
    set L := (encList encNat l).length
    have hterm1 : (l.length + 1) * B ^ dm ≤ (L + 1) * B ^ (dm + ds + dr + 2) :=
      Nat.mul_le_mul (by omega) hp1
    have hterm2 : B ^ ds ≤ (L + 1) * B ^ (dm + ds + dr + 2) :=
      hp2.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos L))
    have hterm3 : ((l.foldl max 0).size + 1) * (L + (l.length + 1) * B ^ dr +
        ((encNat (l.foldl max 0).size).length + 1) ^ 2) ≤ 3 * ((L + 1) * B ^ D) := by
      have hinner : L + (l.length + 1) * B ^ dr +
          ((encNat (l.foldl max 0).size).length + 1) ^ 2 ≤
          3 * ((L + 1) * B ^ (dm + ds + dr + 2)) := by
        have ha : L ≤ (L + 1) * B ^ (dm + ds + dr + 2) :=
          (Nat.le_succ L).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hB1))
        have hb' : (l.length + 1) * B ^ dr ≤ (L + 1) * B ^ (dm + ds + dr + 2) :=
          Nat.mul_le_mul (by omega) hp3
        have hc : ((encNat (l.foldl max 0).size).length + 1) ^ 2 ≤
            (L + 1) * B ^ (dm + ds + dr + 2) :=
          (Nat.pow_le_pow_left (Nat.succ_le_succ hbEnc) 2).trans
            (hp4.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos L)))
        exact (Nat.add_le_add (Nat.add_le_add ha hb') hc).trans_eq (by ring)
      calc ((l.foldl max 0).size + 1) * (L + (l.length + 1) * B ^ dr +
            ((encNat (l.foldl max 0).size).length + 1) ^ 2)
          ≤ B * (3 * ((L + 1) * B ^ (dm + ds + dr + 2))) :=
            Nat.mul_le_mul (Nat.succ_le_succ hbB) hinner
        _ = 3 * ((L + 1) * (B * B ^ (dm + ds + dr + 2))) := by ring
        _ = 3 * ((L + 1) * B ^ D) := by rw [hBD]
    have hsub : (L + 1) * B ^ (dm + ds + dr + 2) ≤ (L + 1) * B ^ D :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (by dsimp [D]; omega))
    have hL : L ≤ (L + 1) * B ^ D :=
      (Nat.le_succ L).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hB1))
    change L + (l.length + 1) * B ^ dm + B ^ ds + L +
      ((l.foldl max 0).size + 1) * (L + (l.length + 1) * B ^ dr +
        ((encNat (l.foldl max 0).size).length + 1) ^ 2) ≤ 16 * ((L + 1) * B ^ D + 1)
    omega
  · have hlen : l.length ≤ (encList encNat l).length := length_le_length_encList encNat l
    have hbEnc : (encNat (l.foldl max 0).size).length ≤ listMax Nat.size l := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le_self _).trans (hbBound l)
    set B := listMax Nat.size l + 1
    have hB1 : 1 ≤ B := Nat.succ_pos _
    set L := (encList encNat l).length
    have hp1 : B ^ dm ≤ B ^ D := Nat.pow_le_pow_right hB1 (by dsimp [D]; omega)
    have hp2 : B ^ ds ≤ B ^ D := Nat.pow_le_pow_right hB1 (by dsimp [D]; omega)
    have hp3 : B ^ dr ≤ B ^ D := Nat.pow_le_pow_right hB1 (by dsimp [D]; omega)
    have hBD1 : 1 ≤ B ^ D := Nat.one_le_pow _ _ hB1
    have h1 : B ^ dm ≤ (L + 1) * B ^ D := hp1.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos L))
    have h2 : B ^ ds ≤ (L + 1) * B ^ D := hp2.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos L))
    have h3 : (l.length + 1) * B ^ dr ≤ (L + 1) * B ^ D := Nat.mul_le_mul (by omega) hp3
    have h4 : L ≤ (L + 1) * B ^ D := (Nat.le_succ L).trans (Nat.le_mul_of_pos_right _ hBD1)
    have h5 : (encNat (l.foldl max 0).size).length ≤ (L + 1) * B ^ D :=
      (hbEnc.trans (Nat.le_succ _)).trans
        ((Nat.le_self_pow (by dsimp [D]; omega) B).trans
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos L)))
    change L + B ^ dm + B ^ ds + L + L + (l.length + 1) * B ^ dr +
      (encNat (l.foldl max 0).size).length ≤ 16 * ((L + 1) * B ^ D + 1)
    omega

/-- Streaming step testing whether a list of naturals is strictly increasing. -/
def strictChainStep (p : (Bool × Option ℕ) × ℕ) : Bool × Option ℕ :=
  match p.1.2 with
  | none => (p.1.1, some p.2)
  | some y => (p.1.1 && decide (y < p.2), some p.2)

/-- Boolean test for `List.IsChain (· < ·) l` computed by a single left fold. -/
def strictChainBool (l : List ℕ) : Bool :=
  (l.foldl (fun s x => strictChainStep (s, x)) (true, none)).1

private theorem foldl_strictChainStep_iff (l : List ℕ) (ok : Bool) (prev : Option ℕ) :
    (l.foldl (fun s x => strictChainStep (s, x)) (ok, prev)).1 = true ↔
      ok = true ∧ match prev with
        | none => l.IsChain (· < ·)
        | some y => (y :: l).IsChain (· < ·) := by
  induction l generalizing ok prev with
  | nil =>
    cases prev <;> simp
  | cons x xs ih =>
    cases prev with
    | none =>
      simp only [List.foldl_cons, strictChainStep]
      exact ih ok (some x)
    | some y =>
      rw [List.foldl_cons, strictChainStep, ih]
      simp [List.isChain_cons_cons, and_assoc]

theorem strictChainBool_eq_true_iff (l : List ℕ) :
    strictChainBool l = true ↔ l.IsChain (· < ·) := by
  simpa [strictChainBool] using foldl_strictChainStep_iff l true none

theorem strictChainBool_radixSortNat (l : List ℕ) :
    strictChainBool (radixSortNat l) = decide l.Nodup := by
  apply Bool.eq_iff_iff.mpr
  rw [strictChainBool_eq_true_iff, decide_eq_true_eq, List.isChain_iff_pairwise,
    ← (radixSortNat_perm l).nodup_iff, List.Nodup]
  exact ⟨fun h => h.imp fun hlt => ne_of_lt hlt,
    fun h => (pairwise_radixSortNat l).imp₂ (fun _ _ hle hne => lt_of_le_of_ne hle hne) h⟩

/-- Duplicate-freeness `decide l.Nodup` on `List ℕ` is computable in quasi-linear time
`O(((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ d)` via LSD binary radix sort. -/
theorem computableInO_decide_nodup_nat :
    ∃ d, ComputableInO (fun l : List ℕ => decide l.Nodup) (encList encNat) encBool
      (fun l => ((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ d)
      (fun l => ((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ d) := by
  obtain ⟨ds, hsort⟩ := computableInO_radixSortNat
  let encSt := encPair encBool (encOption encNat)
  have hstepPt : ComputableInPolyTime strictChainStep (encPair encSt encNat) encSt := by
    have h : ComputableInPolyTime
        (fun p : (Bool × Option ℕ) × ℕ =>
          if p.1.2.isSome then (p.1.1 && decide (p.1.2.getD 0 < p.2), some p.2)
          else (p.1.1, some p.2))
        (encPair encSt encNat) encSt := by fun_prop
    refine h.of_enc_eq fun p => ?_
    rcases p with ⟨⟨ok, _ | y⟩, x⟩ <;> rfl
  have hpairInit : ComputableInO (fun l : List ℕ => ((true, (none : Option ℕ)), l))
      (encList encNat) (encPair encSt (encList encNat))
      (fun l => (encList encNat l).length) (fun l => (encList encNat l).length) :=
    ((ComputableInO.constZero (true, (none : Option ℕ))).prod
      (ComputableInO.of_eq fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)
  have hprevMem (l : List ℕ) (j : ℕ) :
      (streamState (true, (none : Option ℕ)) strictChainStep l j).2 = none ∨
        ∃ y ∈ l, (streamState (true, (none : Option ℕ)) strictChainStep l j).2 = some y := by
    unfold streamState
    have hsub : ∀ x ∈ l.take j, x ∈ l := fun _ hx => List.mem_of_mem_take hx
    generalize l.take j = t at hsub
    suffices ∀ ok prev, (prev = none ∨ ∃ y ∈ l, prev = some y) →
        ((t.foldl (fun s x => strictChainStep (s, x)) (ok, prev)).2 = none ∨
          ∃ y ∈ l, (t.foldl (fun s x => strictChainStep (s, x)) (ok, prev)).2 = some y) from
      this true none (Or.inl rfl)
    induction t with
    | nil => intro _ _ h; exact h
    | cons x xs ih =>
      intro ok prev _
      have hx : x ∈ l := hsub x (List.mem_cons_self ..)
      have hsub' : ∀ z ∈ xs, z ∈ l := fun z hz => hsub z (List.mem_cons_of_mem _ hz)
      cases prev <;> exact ih hsub' _ (some x) (Or.inr ⟨x, hx, rfl⟩)
  obtain ⟨dc, hfold⟩ := computableInO_streamFold
    (lMax := fun p : (Bool × Option ℕ) × List ℕ =>
      (encSt p.1).length + listMax Nat.size p.2 + 6)
    Prod.fst Prod.snd (fun _ => rfl) hstepPt
    (fun p j _ => by
      by_cases hp0 : p.1 = (true, none)
      · rw [hp0]
        rcases hprevMem p.2 j with hnone | ⟨y, hy, hsome⟩
        · rw [show streamState (true, none) strictChainStep p.2 j =
              ((streamState (true, none) strictChainStep p.2 j).1, none) from
            Prod.ext rfl hnone]
          simp [encSt, encBool_apply, encOption_none]
        · rw [show streamState (true, none) strictChainStep p.2 j =
              ((streamState (true, none) strictChainStep p.2 j).1, some y) from
            Prod.ext rfl hsome]
          have hy' := le_listMax (f := Nat.size) hy
          simp only [encSt, length_encPair, encBool_apply, encOption_some, List.length_cons,
            encNat_apply, Nat.size_eq_bits_len]
          omega
      · have hgen : ∀ (t : List ℕ) (ok : Bool) (prev : Option ℕ),
            (∀ x ∈ t, x ∈ p.2) →
            (encSt (t.foldl (fun s x => strictChainStep (s, x)) (ok, prev))).length ≤
              (encSt (ok, prev)).length + listMax Nat.size p.2 + 6 := by
          intro t
          induction t with
          | nil =>
            intro ok prev _
            simp only [List.foldl_nil]
            omega
          | cons x xs _ =>
            intro ok prev hsub
            have hmem2 : ∃ z ∈ p.2,
                ((x :: xs).foldl (fun s a => strictChainStep (s, a)) (ok, prev)).2 = some z := by
              suffices ∀ (u : List ℕ) (b : Bool) (w : ℕ), (∀ a ∈ w :: u, a ∈ p.2) →
                  ∃ z ∈ p.2, (u.foldl (fun s a => strictChainStep (s, a)) (b, some w)).2 =
                    some z by
                cases prev with
                | none => exact this xs ok x hsub
                | some y => exact this xs (ok && decide (y < x)) x hsub
              intro u
              induction u with
              | nil => intro b w hw; exact ⟨w, hw w (List.mem_cons_self ..), rfl⟩
              | cons v us ihu =>
                intro b w hw
                exact ihu (b && decide (w < v)) v fun a ha =>
                  hw a (List.mem_cons_of_mem _ ha)
            obtain ⟨z, hz, hzs⟩ := hmem2
            have hzSz := le_listMax (f := Nat.size) hz
            rw [show (x :: xs).foldl (fun s a => strictChainStep (s, a)) (ok, prev) =
                (((x :: xs).foldl (fun s a => strictChainStep (s, a)) (ok, prev)).1, some z) from
              Prod.ext rfl hzs]
            simp only [encSt, length_encPair, encBool_apply, encOption_some, List.length_cons,
              encNat_apply, Nat.size_eq_bits_len]
            omega
        exact hgen (p.2.take j) p.1.1 p.1.2 fun _ hx => List.mem_of_mem_take hx)
    (fun p j hj => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      have := le_listMax (f := Nat.size) (List.getElem_mem hj)
      omega)
  have hchain : ComputableInO strictChainBool (encList encNat) encBool
      (fun l => ((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ (dc + 1))
      (fun l => ((encList encNat l).length + 1) * (listMax Nat.size l + 1) ^ (dc + 1)) := by
    refine ((hfold.comp hpairInit).fst').mono (12 ^ (dc + 1)) (fun l => ?_) (fun l => ?_)
    · dsimp only [Function.comp_apply]
      have hst0 : (encSt (true, none)).length = 3 := by
        simp [encSt, encBool_apply, encOption_none]
      have hlen : l.length ≤ (encList encNat l).length := length_le_length_encList encNat l
      have hpow : (3 + listMax Nat.size l + 6 + 1) ^ dc ≤
          10 ^ dc * (listMax Nat.size l + 1) ^ dc := by
        calc (3 + listMax Nat.size l + 6 + 1) ^ dc
            ≤ (10 * (listMax Nat.size l + 1)) ^ dc := Nat.pow_le_pow_left (by omega) dc
          _ = 10 ^ dc * (listMax Nat.size l + 1) ^ dc := Nat.mul_pow _ _ _
      have h10 : 10 ^ dc ≤ 12 ^ dc := Nat.pow_le_pow_left (by omega) dc
      have hB : (listMax Nat.size l + 1) ^ dc ≤ (listMax Nat.size l + 1) ^ (dc + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ dc)
      have hB1 : 1 ≤ (listMax Nat.size l + 1) ^ (dc + 1) :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      set L := (encList encNat l).length
      set P := (listMax Nat.size l + 1) ^ (dc + 1)
      have hLP : L ≤ (L + 1) * P := (Nat.le_succ L).trans (Nat.le_mul_of_pos_right _ hB1)
      have hmul : (l.length + 1) * (3 + listMax Nat.size l + 6 + 1) ^ dc ≤
          10 ^ dc * ((L + 1) * P + 1) := by
        calc (l.length + 1) * (3 + listMax Nat.size l + 6 + 1) ^ dc
            ≤ (L + 1) * (10 ^ dc * P) :=
              Nat.mul_le_mul (by omega) (hpow.trans (Nat.mul_le_mul_left _ hB))
          _ = 10 ^ dc * ((L + 1) * P) := by ring
          _ ≤ 10 ^ dc * ((L + 1) * P + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
      have h10' : 10 ^ dc + 9 ≤ 12 ^ (dc + 1) := by
        rw [pow_succ]; nlinarith [Nat.one_le_pow dc 12 (by omega), h10]
      rw [length_encPair, hst0]
      calc L + (2 * 3 + 1 + L + (l.length + 1) * (3 + listMax Nat.size l + 6 + 1) ^ dc)
          ≤ 9 * ((L + 1) * P + 1) + 10 ^ dc * ((L + 1) * P + 1) := by omega
        _ = (10 ^ dc + 9) * ((L + 1) * P + 1) := by ring
        _ ≤ 12 ^ (dc + 1) * ((L + 1) * P + 1) := Nat.mul_le_mul_right _ h10'
    · dsimp only [Function.comp_apply]
      have hst0 : (encSt (true, none)).length = 3 := by
        simp [encSt, encBool_apply, encOption_none]
      have hpow : (3 + listMax Nat.size l + 6 + 1) ^ dc ≤
          10 ^ dc * (listMax Nat.size l + 1) ^ dc := by
        calc (3 + listMax Nat.size l + 6 + 1) ^ dc
            ≤ (10 * (listMax Nat.size l + 1)) ^ dc := Nat.pow_le_pow_left (by omega) dc
          _ = 10 ^ dc * (listMax Nat.size l + 1) ^ dc := Nat.mul_pow _ _ _
      have h10 : 10 ^ dc ≤ 12 ^ dc := Nat.pow_le_pow_left (by omega) dc
      have hB : (listMax Nat.size l + 1) ^ dc ≤ (listMax Nat.size l + 1) ^ (dc + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ dc)
      have hB1 : 1 ≤ (listMax Nat.size l + 1) ^ (dc + 1) :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      set L := (encList encNat l).length
      set P := (listMax Nat.size l + 1) ^ (dc + 1)
      have hLP : L ≤ (L + 1) * P := (Nat.le_succ L).trans (Nat.le_mul_of_pos_right _ hB1)
      have hP : (3 + listMax Nat.size l + 6 + 1) ^ dc ≤ 10 ^ dc * ((L + 1) * P + 1) := by
        calc (3 + listMax Nat.size l + 6 + 1) ^ dc
            ≤ 10 ^ dc * P := hpow.trans (Nat.mul_le_mul_left _ hB)
          _ ≤ 10 ^ dc * ((L + 1) * P) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos L))
          _ ≤ 10 ^ dc * ((L + 1) * P + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
      have h10' : 10 ^ dc + 2 ≤ 12 ^ (dc + 1) := by
        rw [pow_succ]; nlinarith [Nat.one_le_pow dc 12 (by omega), h10]
      rw [hst0]
      calc L + (3 + listMax Nat.size l + 6 + 1) ^ dc
          ≤ 2 * ((L + 1) * P + 1) + 10 ^ dc * ((L + 1) * P + 1) := by omega
        _ = (10 ^ dc + 2) * ((L + 1) * P + 1) := by ring
        _ ≤ 12 ^ (dc + 1) * ((L + 1) * P + 1) := Nat.mul_le_mul_right _ h10'
  have hcomp := (hchain.comp hsort).of_enc_eq fun l =>
    congrArg encBool (strictChainBool_radixSortNat l).symm
  have hlistMaxEq (l : List ℕ) : listMax Nat.size (radixSortNat l) = listMax Nat.size l := by
    apply le_antisymm
    · exact listMax_le fun x hx => le_listMax ((radixSortNat_perm l).mem_iff.mp hx)
    · exact listMax_le fun x hx => le_listMax ((radixSortNat_perm l).mem_iff.mpr hx)
  refine ⟨ds + dc + 1, hcomp.mono 2 (fun l => ?_) (fun l => ?_)⟩ <;>
  · have hlenEq : (encList encNat (radixSortNat l)).length = (encList encNat l).length :=
      length_encList_radixSortBy encNat id _ l
    rw [hlenEq, hlistMaxEq]
    have h1 : (listMax Nat.size l + 1) ^ ds ≤ (listMax Nat.size l + 1) ^ (ds + dc + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have h2 : (listMax Nat.size l + 1) ^ (dc + 1) ≤ (listMax Nat.size l + 1) ^ (ds + dc + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hm1 := Nat.mul_le_mul_left ((encList encNat l).length + 1) h1
    have hm2 := Nat.mul_le_mul_left ((encList encNat l).length + 1) h2
    omega

end RadixSort

end CslibFrontier.Complexity
