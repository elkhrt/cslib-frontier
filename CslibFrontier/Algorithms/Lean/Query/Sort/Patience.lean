/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Patience Sorting for Longest Monotone Subsequences in the Comparison Query Model

Given a finite sequence `f : Fin n → α` over a linear order `α` and a subset of positions
`R : Finset (Fin n)`, patience sorting maintains piles
whose top (tail) elements are non-decreasing from left to right, placing each new index `x` onto
the leftmost pile whose tail value exceeds `f x` via binary search (`Cslib.Query.lowerBoundBy`)
and threading backpointers to the previous pile's tail.

## Main definitions

* `CslibFrontier.Query.PatiencePile`: a pile storing its current tail index and newest-first
  witness non-decreasing chain.
* `CslibFrontier.Query.patienceNonDecrStep`, `CslibFrontier.Query.patienceNonIncrStep`,
  `CslibFrontier.Query.patienceMaxStep`: pure longest non-decreasing, non-increasing, and monotone
  subsequence extractors on `R : Finset (Fin n)`.
* `CslibFrontier.Query.patienceNonDecrStepQ`, `CslibFrontier.Query.patienceMaxStepQ`: `FreeM`
  implementations charging `tick` once per binary-search comparison.

## Main results

* `CslibFrontier.Query.patienceNonDecrStep_spec`: `patienceNonDecrStep f R` is a non-decreasing
  subsequence in `R` of maximum cardinality among all non-decreasing subsets of `R` (proved via
  the dual pile-assignment strict-antitone coloring).
* `CslibFrontier.Query.eval_patienceNonDecrStepQ`, `CslibFrontier.Query.eval_patienceMaxStepQ`:
  equivalence between the `FreeM` algorithms and their pure specifications.
* `CslibFrontier.Query.cost_patienceNonDecrStepQ_le`,
  `CslibFrontier.Query.cost_patienceMaxStepQ_le`: `O(|R| log |R|)` comparison cost bounds.
-/

public section

namespace CslibFrontier.Query

open Cslib Cslib.FreeM Cslib.Query Cslib.Algorithms.Lean

/-- A single pile in patience sorting: the current tail index `tail` and a witness non-decreasing
subsequence `chain` (stored newest-first with head `tail`) of length `pileIndex + 1`. -/
structure PatiencePile (n : ℕ) where
  /-- Current tail index of the pile (head of `chain`). -/
  tail : Fin n
  /-- Witness non-decreasing subsequence ending at `tail`, stored newest-first. -/
  chain : List (Fin n)
  deriving DecidableEq

/-- Pure one-element update of the patience-sorting pile list for non-decreasing subsequences. -/
def patienceInsert {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (piles : List (PatiencePile n)) (x : Fin n) : List (PatiencePile n) × ℕ :=
  let pos := lowerBound (fun j => decide (f ((piles.getD j ⟨x, []⟩).tail) ≤ f x)) 0 piles.length
  let prevChain := if pos = 0 then [] else (piles.getD (pos - 1) ⟨x, []⟩).chain
  let newPile : PatiencePile n := ⟨x, x :: prevChain⟩
  let piles' := if pos < piles.length then piles.set pos newPile else piles ++ [newPile]
  (piles', pos)

/-- Left-fold helper for patience sorting recording pile assignments. -/
def patienceFold {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (piles : List (PatiencePile n)) (assign : List (Fin n × ℕ)) :
    List (Fin n) → List (PatiencePile n) × List (Fin n × ℕ)
  | [] => (piles, assign)
  | y :: ys =>
    let res := patienceInsert f piles y
    patienceFold f res.1 ((y, res.2) :: assign) ys

/-- Pure maximum non-decreasing subsequence of `f` on `R : Finset (Fin n)` via patience sorting. -/
noncomputable def patienceNonDecrStep {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (R : Finset (Fin n)) : Finset (Fin n) :=
  let xs := R.sort (· ≤ ·)
  let piles := (patienceFold f [] [] xs).1
  match piles.getLast? with
  | none => ∅
  | some p => p.chain.toFinset

/-- Pure maximum non-increasing subsequence of `f` on `R : Finset (Fin n)` via patience sorting
on `αᵒᵈ`. -/
noncomputable def patienceNonIncrStep {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (R : Finset (Fin n)) : Finset (Fin n) :=
  patienceNonDecrStep (fun i => OrderDual.toDual (f i)) R

/-- Pure maximum monotone (non-decreasing or non-increasing) subsequence of `f` on `R`. -/
noncomputable def patienceMaxStep {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (R : Finset (Fin n)) : Finset (Fin n) :=
  let s₁ := patienceNonDecrStep f R
  let s₂ := patienceNonIncrStep f R
  if s₂.card ≤ s₁.card then s₁ else s₂

private structure PatienceInv {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (seen : List (Fin n)) (piles : List (PatiencePile n)) (assign : List (Fin n × ℕ)) : Prop where
  tails_mono : ∀ (i j : ℕ) (hi : i < piles.length) (hj : j < piles.length),
    i ≤ j → f (piles[i].tail) ≤ f (piles[j].tail)
  chain_len : ∀ (j : ℕ) (hj : j < piles.length), piles[j].chain.length = j + 1
  chain_head : ∀ (j : ℕ) (hj : j < piles.length),
    piles[j].chain.head? = some piles[j].tail
  chain_sub : ∀ (j : ℕ) (hj : j < piles.length), ∀ x ∈ piles[j].chain, x ∈ seen
  chain_sorted_idx : ∀ (j : ℕ) (hj : j < piles.length),
    piles[j].chain.Pairwise (· > ·)
  chain_mono : ∀ (j : ℕ) (hj : j < piles.length),
    piles[j].chain.Pairwise (fun a b => f b ≤ f a)
  assign_mem : ∀ x ∈ seen, ∃ p < piles.length, (x, p) ∈ assign
  assign_sub : ∀ x p, (x, p) ∈ assign → x ∈ seen
  assign_tail_le : ∀ x p, (x, p) ∈ assign →
    ∃ hp : p < piles.length, f (piles[p].tail) ≤ f x
  assign_anti : ∀ x y p, (x, p) ∈ assign → (y, p) ∈ assign → x < y → f y < f x

private theorem patienceInv_nil {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α) :
    PatienceInv f [] [] [] where
  tails_mono _ _ hi := by simp at hi
  chain_len _ hj := by simp at hj
  chain_head _ hj := by simp at hj
  chain_sub _ hj := by simp at hj
  chain_sorted_idx _ hj := by simp at hj
  chain_mono _ hj := by simp at hj
  assign_mem _ hx := by simp at hx
  assign_sub _ _ h := by simp at h
  assign_tail_le _ _ h := by simp at h
  assign_anti _ _ _ h := by simp at h

private theorem list_getD_eq_getElem {β : Type*} (l : List β) (d : β) {i : ℕ}
    (hi : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem patienceInv_step {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    {seen : List (Fin n)} {piles : List (PatiencePile n)} {assign : List (Fin n × ℕ)}
    {x : Fin n} (hfresh : ∀ y ∈ seen, y < x) (hinv : PatienceInv f seen piles assign) :
    PatienceInv f (x :: seen) (patienceInsert f piles x).1
      ((x, (patienceInsert f piles x).2) :: assign) := by
  let t : ℕ → Bool := fun j => decide (f ((piles.getD j ⟨x, []⟩).tail) ≤ f x)
  have ht_mono : ∀ m m', 0 ≤ m → m ≤ m' → m' < piles.length → t m' = true → t m = true := by
    intro m m' _ hmm' hm' ht'
    have hm : m < piles.length := lt_of_le_of_lt hmm' hm'
    simp only [t, list_getD_eq_getElem _ _ hm, list_getD_eq_getElem _ _ hm',
      decide_eq_true_eq] at ht' ⊢
    exact (hinv.tails_mono m m' hm hm' hmm').trans ht'
  obtain ⟨_, hpos_le, hlt_true, hge_false⟩ := lowerBound_spec t ht_mono
  simp only [Nat.zero_le, max_eq_right] at hpos_le
  set pos := lowerBound t 0 piles.length
  set prevChain := if pos = 0 then [] else (piles.getD (pos - 1) ⟨x, []⟩).chain
  set newPile : PatiencePile n := ⟨x, x :: prevChain⟩
  set piles' := if pos < piles.length then piles.set pos newPile else piles ++ [newPile]
  have hlen' : piles'.length = if pos < piles.length then piles.length else piles.length + 1 := by
    dsimp only [piles']
    split_ifs <;> simp
  have hpos_lt' : pos < piles'.length := by
    rw [hlen']
    split_ifs with h <;> omega
  have hget_pos : piles'[pos] = newPile := by
    dsimp only [piles']
    split_ifs with h
    · simp
    · have hpeq : pos = piles.length := by omega
      simp [hpeq]
  have hget_ne : ∀ (j : ℕ) (hj : j < piles'.length), j ≠ pos →
      ∃ hj₀ : j < piles.length, piles'[j] = piles[j] := by
    intro j hj hjne
    dsimp only [piles'] at hj ⊢
    split_ifs at hj ⊢ with h
    · rw [List.length_set] at hj
      exact ⟨hj, List.getElem_set_ne (Ne.symm hjne) _⟩
    · rw [List.length_append, List.length_singleton] at hj
      have hj₀ : j < piles.length := by omega
      exact ⟨hj₀, List.getElem_append_left hj₀⟩
  have hprev_len : prevChain.length = pos := by
    dsimp only [prevChain]
    split_ifs with h
    · simp [h]
    · have hlt : pos - 1 < piles.length := by omega
      rw [list_getD_eq_getElem _ _ hlt, hinv.chain_len (pos - 1) hlt]
      omega
  have hprev_sub : ∀ y ∈ prevChain, y ∈ seen := by
    dsimp only [prevChain]
    split_ifs with h
    · simp
    · intro y hy
      have hlt : pos - 1 < piles.length := by omega
      rw [list_getD_eq_getElem _ _ hlt] at hy
      exact hinv.chain_sub (pos - 1) hlt y hy
  have hprev_le_x : ∀ y ∈ prevChain, f y ≤ f x := by
    dsimp only [prevChain]
    split_ifs with h
    · simp
    · intro y hy
      have hlt : pos - 1 < piles.length := by omega
      rw [list_getD_eq_getElem _ _ hlt] at hy
      have htail : f (piles[pos - 1].tail) ≤ f x := by
        have ht1 := hlt_true (pos - 1) (Nat.zero_le _) (by omega)
        simp only [t, list_getD_eq_getElem _ _ hlt, decide_eq_true_eq] at ht1
        exact ht1
      have hhead := hinv.chain_head (pos - 1) hlt
      have hmono := hinv.chain_mono (pos - 1) hlt
      cases hc : piles[pos - 1].chain with
      | nil => simp [hc] at hy
      | cons hd tl =>
        rw [hc, List.head?_cons] at hhead
        have hdeq : hd = piles[pos - 1].tail := Option.some.inj hhead
        rw [hc, List.mem_cons] at hy
        rcases hy with rfl | hytl
        · exact hdeq ▸ htail
        · rw [hc, List.pairwise_cons] at hmono
          exact (hmono.1 y hytl).trans (hdeq ▸ htail)
  have hnew_tail_le_old : ∀ (h : pos < piles.length), f x < f (piles[pos].tail) := by
    intro h
    have hf := hge_false pos (le_refl _) h
    simp only [t, list_getD_eq_getElem _ _ h, decide_eq_false_iff_not, not_le] at hf
    exact hf
  change PatienceInv f (x :: seen) piles' ((x, pos) :: assign)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    by_cases hip : i = pos
    · subst hip
      by_cases hjp : j = pos
      · subst hjp; exact le_rfl
      · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
        rw [hget_pos, hgetj]
        have hlt_pos : pos < piles.length := lt_of_le_of_lt hij hj₀
        exact le_of_lt (lt_of_lt_of_le (hnew_tail_le_old hlt_pos)
          (hinv.tails_mono pos j hlt_pos hj₀ hij))
    · obtain ⟨hi₀, hgeti⟩ := hget_ne i hi hip
      rw [hgeti]
      by_cases hjp : j = pos
      · subst hjp
        rw [hget_pos]
        have ht1 := hlt_true i (Nat.zero_le _) (lt_of_le_of_ne hij hip)
        simp only [t, list_getD_eq_getElem _ _ hi₀, decide_eq_true_eq] at ht1
        exact ht1
      · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
        rw [hgetj]
        exact hinv.tails_mono i j hi₀ hj₀ hij
  · intro j hj
    by_cases hjp : j = pos
    · subst hjp; rw [hget_pos]; simp [newPile, hprev_len]
    · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
      rw [hgetj]; exact hinv.chain_len j hj₀
  · intro j hj
    by_cases hjp : j = pos
    · subst hjp; rw [hget_pos]; simp [newPile]
    · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
      rw [hgetj]; exact hinv.chain_head j hj₀
  · intro j hj y hy
    by_cases hjp : j = pos
    · subst hjp
      rw [hget_pos] at hy
      rcases List.mem_cons.mp hy with rfl | hyp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hprev_sub y hyp)
    · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
      rw [hgetj] at hy
      exact List.mem_cons_of_mem _ (hinv.chain_sub j hj₀ y hy)
  · intro j hj
    by_cases hjp : j = pos
    · subst hjp
      rw [hget_pos]
      refine List.pairwise_cons.mpr ⟨fun y hy => hfresh y (hprev_sub y hy), ?_⟩
      dsimp only [prevChain]
      split_ifs with h
      · exact List.Pairwise.nil
      · have hlt : pos - 1 < piles.length := by omega
        rw [list_getD_eq_getElem _ _ hlt]
        exact hinv.chain_sorted_idx (pos - 1) hlt
    · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
      rw [hgetj]; exact hinv.chain_sorted_idx j hj₀
  · intro j hj
    by_cases hjp : j = pos
    · subst hjp
      rw [hget_pos]
      refine List.pairwise_cons.mpr ⟨hprev_le_x, ?_⟩
      dsimp only [prevChain]
      split_ifs with h
      · exact List.Pairwise.nil
      · have hlt : pos - 1 < piles.length := by omega
        rw [list_getD_eq_getElem _ _ hlt]
        exact hinv.chain_mono (pos - 1) hlt
    · obtain ⟨hj₀, hgetj⟩ := hget_ne j hj hjp
      rw [hgetj]; exact hinv.chain_mono j hj₀
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hys
    · exact ⟨pos, hpos_lt', List.mem_cons_self⟩
    · obtain ⟨p, hp, hmem⟩ := hinv.assign_mem y hys
      refine ⟨p, ?_, List.mem_cons_of_mem _ hmem⟩
      rw [hlen']; split_ifs <;> omega
  · intro y p hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, _⟩ := Prod.mk.inj heq; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hinv.assign_sub y p hmem')
  · intro y p hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨hpos_lt', by rw [hget_pos]⟩
    · obtain ⟨hp, hle⟩ := hinv.assign_tail_le y p hmem'
      have hp' : p < piles'.length := by rw [hlen']; split_ifs <;> omega
      refine ⟨hp', ?_⟩
      by_cases hpp : p = pos
      · subst hpp
        rw [hget_pos]
        exact le_of_lt (lt_of_lt_of_le (hnew_tail_le_old hp) hle)
      · obtain ⟨_, hgetp⟩ := hget_ne p hp' hpp
        rw [hgetp]; exact hle
  · intro y z p hy hz hyz
    rcases List.mem_cons.mp hy with heq | hy'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rcases List.mem_cons.mp hz with heq' | hz'
      · obtain ⟨rfl, _⟩ := Prod.mk.inj heq'; exact absurd hyz (lt_irrefl _)
      · exact absurd (hfresh z (hinv.assign_sub z pos hz')) (not_lt.mpr hyz.le)
    · rcases List.mem_cons.mp hz with heq | hz'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        obtain ⟨hp, hle⟩ := hinv.assign_tail_le y pos hy'
        exact lt_of_lt_of_le (hnew_tail_le_old hp) hle
      · exact hinv.assign_anti y z p hy' hz' hyz

private theorem patienceFold_inv {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α) :
    ∀ (xs seen : List (Fin n)) (piles : List (PatiencePile n)) (assign : List (Fin n × ℕ)),
      xs.Pairwise (· < ·) →
      (∀ y ∈ seen, ∀ z ∈ xs, y < z) →
      PatienceInv f seen piles assign →
      PatienceInv f (xs.reverse ++ seen)
        (patienceFold f piles assign xs).1 (patienceFold f piles assign xs).2 := by
  intro xs
  induction xs with
  | nil =>
    intro seen piles assign _ _ hinv
    simpa [patienceFold] using hinv
  | cons x xs ih =>
    intro seen piles assign hxs hlt hinv
    rw [List.pairwise_cons] at hxs
    have hfresh : ∀ y ∈ seen, y < x := fun y hy => hlt y hy x List.mem_cons_self
    have hstep := patienceInv_step f hfresh hinv
    have hlt' : ∀ y ∈ x :: seen, ∀ z ∈ xs, y < z := by
      intro y hy z hz
      rcases List.mem_cons.mp hy with rfl | hys
      · exact hxs.1 z hz
      · exact hlt y hys z (List.mem_cons_of_mem _ hz)
    have hrec := ih (x :: seen) _ _ hxs.2 hlt' hstep
    simpa [patienceFold, List.reverse_cons, List.append_assoc] using hrec

/-- `patienceNonDecrStep f R` is a subset of `R` on which `f` is non-decreasing and achieves the
maximum cardinality among all non-decreasing subsets of `R`. -/
theorem patienceNonDecrStep_spec {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (R : Finset (Fin n)) :
    patienceNonDecrStep f R ⊆ R ∧
    MonotoneOn f (patienceNonDecrStep f R) ∧
    ∀ S ⊆ R, MonotoneOn f S → S.card ≤ (patienceNonDecrStep f R).card := by
  classical
  let xs := R.sort (· ≤ ·)
  have hxs_nodup : xs.Nodup := R.sort_nodup (· ≤ ·)
  have hxs_sorted : xs.Pairwise (· ≤ ·) := R.pairwise_sort (· ≤ ·)
  have hxs_lt : xs.Pairwise (· < ·) :=
    List.pairwise_iff_getElem.mpr fun i j hi hj hij =>
      lt_of_le_of_ne (List.pairwise_iff_getElem.mp hxs_sorted i j hi hj hij)
        (fun heq => by
          have := (hxs_nodup.getElem_inj_iff (i := i) (j := j)).mp heq
          omega)
  have hinv := patienceFold_inv f xs [] [] [] hxs_lt (by simp) (patienceInv_nil f)
  set res := patienceFold f [] [] xs
  have hmem_iff : ∀ y, y ∈ xs.reverse ++ [] ↔ y ∈ R := fun y => by
    simp [xs, Finset.mem_sort]
  have hdef : patienceNonDecrStep f R =
      match res.1.getLast? with | none => ∅ | some p => p.chain.toFinset := rfl
  have hsub : patienceNonDecrStep f R ⊆ R := by
    rw [hdef]
    cases hlast : res.1.getLast? with
    | none => exact Finset.empty_subset R
    | some p =>
      intro y hy
      have hlen : 0 < res.1.length := by
        cases h0 : res.1 with
        | nil => simp [h0] at hlast
        | cons _ _ => simp
      have hpeq : res.1[res.1.length - 1] = p := by
        rw [List.getLast?_eq_some_iff] at hlast
        obtain ⟨init, hinit⟩ := hlast
        simp [hinit]
      rw [← hpeq] at hy
      have hy' : y ∈ res.1[res.1.length - 1].chain := List.mem_toFinset.mp hy
      exact (hmem_iff y).mp (hinv.chain_sub (res.1.length - 1) (by omega) y hy')
  have hmono : MonotoneOn f (patienceNonDecrStep f R) := by
    rw [hdef]
    cases hlast : res.1.getLast? with
    | none => simp [MonotoneOn]
    | some p =>
      have hlen : 0 < res.1.length := by
        cases h0 : res.1 with
        | nil => simp [h0] at hlast
        | cons _ _ => simp
      have hpeq : res.1[res.1.length - 1] = p := by
        rw [List.getLast?_eq_some_iff] at hlast
        obtain ⟨init, hinit⟩ := hlast
        simp [hinit]
      intro a ha b hb hab
      rw [Finset.mem_coe, List.mem_toFinset, ← hpeq] at ha hb
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact le_rfl
      · have hidx := hinv.chain_sorted_idx (res.1.length - 1) (by omega)
        have hval := hinv.chain_mono (res.1.length - 1) (by omega)
        have hba : ∃ (i j : ℕ) (hi : i < res.1[res.1.length - 1].chain.length)
            (hj : j < res.1[res.1.length - 1].chain.length),
            i < j ∧ res.1[res.1.length - 1].chain[i] = b ∧
            res.1[res.1.length - 1].chain[j] = a := by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
          rcases lt_trichotomy i j with hij | rfl | hji
          · exact ⟨i, j, hi, hj, hij, rfl, rfl⟩
          · exact absurd hlt (lt_irrefl _)
          · exfalso
            have := List.pairwise_iff_getElem.mp hidx j i hj hi hji
            exact absurd hlt (not_lt.mpr (le_of_lt this))
        obtain ⟨i, j, hi, hj, hij, hbi, haj⟩ := hba
        have := List.pairwise_iff_getElem.mp hval i j hi hj hij
        rwa [hbi, haj] at this
  have hmax : ∀ S ⊆ R, MonotoneOn f S → S.card ≤ (patienceNonDecrStep f R).card := by
    intro S hSR hSmono
    have hcard_eq : (patienceNonDecrStep f R).card = res.1.length := by
      dsimp only [patienceNonDecrStep]
      change (match res.1.getLast? with | none => ∅ | some p => p.chain.toFinset).card =
        res.1.length
      cases hlast : res.1.getLast? with
      | none =>
        have : res.1 = [] := List.getLast?_eq_none_iff.mp hlast
        simp [this]
      | some p =>
        have hlen : 0 < res.1.length := by
          cases h0 : res.1 with
          | nil => simp [h0] at hlast
          | cons _ _ => simp
        have hpeq : res.1[res.1.length - 1] = p := by
          rw [List.getLast?_eq_some_iff] at hlast
          obtain ⟨init, hinit⟩ := hlast
          simp [hinit]
        rw [← hpeq]
        have hnd : res.1[res.1.length - 1].chain.Nodup :=
          (hinv.chain_sorted_idx (res.1.length - 1) (by omega)).imp (fun h => ne_of_gt h)
        rw [List.toFinset_card_of_nodup hnd, hinv.chain_len (res.1.length - 1) (by omega)]
        omega
    rw [hcard_eq]
    have hchoose : ∀ x ∈ S, ∃ p : Fin res.1.length, (x, p.1) ∈ res.2 := by
      intro x hx
      obtain ⟨p, hp, hmem⟩ := hinv.assign_mem x ((hmem_iff x).mpr (hSR hx))
      exact ⟨⟨p, hp⟩, hmem⟩
    choose g hg using fun x : S => hchoose x.1 x.2
    have hginj : Function.Injective g := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      apply Subtype.ext
      rcases lt_trichotomy x y with hlt | heq | hgt
      · exfalso
        have h1 : f y < f x := hinv.assign_anti x y (g ⟨x, hx⟩).1 (hg ⟨x, hx⟩)
          (hxy ▸ hg ⟨y, hy⟩) hlt
        exact not_lt.mpr (hSmono hx hy hlt.le) h1
      · exact heq
      · exfalso
        have h1 : f x < f y := hinv.assign_anti y x (g ⟨y, hy⟩).1 (hg ⟨y, hy⟩)
          (hxy.symm ▸ hg ⟨x, hx⟩) hgt
        exact not_lt.mpr (hSmono hy hx hgt.le) h1
    simpa using Fintype.card_le_of_injective g hginj
  exact ⟨hsub, hmono, hmax⟩

/-- `patienceMaxStep f R` is a monotone (non-decreasing or non-increasing) subset of `R` of
maximum cardinality among all monotone subsets of `R`. -/
theorem patienceMaxStep_spec {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (R : Finset (Fin n)) :
    patienceMaxStep f R ⊆ R ∧
    (MonotoneOn f (patienceMaxStep f R) ∨ AntitoneOn f (patienceMaxStep f R)) ∧
    ∀ S ⊆ R, (MonotoneOn f S ∨ AntitoneOn f S) → S.card ≤ (patienceMaxStep f R).card := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [patienceMaxStep]
    split_ifs
    · exact (patienceNonDecrStep_spec f R).1
    · exact (patienceNonDecrStep_spec (fun i => OrderDual.toDual (f i)) R).1
  · dsimp only [patienceMaxStep]
    split_ifs
    · exact Or.inl (patienceNonDecrStep_spec f R).2.1
    · right
      have h := (patienceNonDecrStep_spec (fun i => OrderDual.toDual (f i)) R).2.1
      exact fun a ha b hb hab => h ha hb hab
  · intro S hSR hSmono
    dsimp only [patienceMaxStep]
    rcases hSmono with hm | ha
    · have h1 := (patienceNonDecrStep_spec f R).2.2 S hSR hm
      split_ifs <;> omega
    · have h2 := (patienceNonDecrStep_spec (fun i => OrderDual.toDual (f i)) R).2.2 S hSR
        (fun a hA b hB hab => ha hA hB hab)
      rw [← patienceNonIncrStep] at h2
      split_ifs <;> omega

/-- `FreeM` patience-sorting insertion using `Cslib.Query.lowerBoundBy`. -/
def patienceInsertQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (tick : FreeM Q Unit) (f : Fin n → α) (piles : List (PatiencePile n)) (x : Fin n) :
    FreeM Q (List (PatiencePile n) × ℕ) := do
  let pos ← lowerBoundBy
    (fun j => do
      tick
      pure (decide (f ((piles.getD j ⟨x, []⟩).tail) ≤ f x)))
    0 piles.length
  let prevChain := if pos = 0 then [] else (piles.getD (pos - 1) ⟨x, []⟩).chain
  let newPile : PatiencePile n := ⟨x, x :: prevChain⟩
  let piles' := if pos < piles.length then piles.set pos newPile else piles ++ [newPile]
  pure (piles', pos)

/-- `FreeM` patience-sorting fold over an index list. -/
def patienceFoldQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (tick : FreeM Q Unit) (f : Fin n → α) (piles : List (PatiencePile n)) :
    List (Fin n) → FreeM Q (List (PatiencePile n))
  | [] => pure piles
  | y :: ys => do
    let res ← patienceInsertQ tick f piles y
    patienceFoldQ tick f res.1 ys

/-- `FreeM` maximum non-decreasing subsequence extractor. -/
noncomputable def patienceNonDecrStepQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (tick : FreeM Q Unit) (f : Fin n → α) (R : Finset (Fin n)) : FreeM Q (Finset (Fin n)) := do
  let piles ← patienceFoldQ tick f [] (R.sort (· ≤ ·))
  pure <| match piles.getLast? with
    | none => ∅
    | some p => p.chain.toFinset

/-- `FreeM` maximum monotone subsequence extractor. -/
noncomputable def patienceMaxStepQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (tick : FreeM Q Unit) (f : Fin n → α) (R : Finset (Fin n)) : FreeM Q (Finset (Fin n)) := do
  let s₁ ← patienceNonDecrStepQ tick f R
  let s₂ ← patienceNonDecrStepQ tick (fun i => OrderDual.toDual (f i)) R
  pure (if s₂.card ≤ s₁.card then s₁ else s₂)

private theorem eval_patienceInsertQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (tick : FreeM Q Unit) (f : Fin n → α)
    (piles : List (PatiencePile n)) (x : Fin n) :
    (patienceInsertQ tick f piles x).eval oracle = patienceInsert f piles x := by
  simp [patienceInsertQ, patienceInsert]

private theorem eval_patienceFoldQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (tick : FreeM Q Unit) (f : Fin n → α) :
    ∀ (xs : List (Fin n)) (piles : List (PatiencePile n)) (assign : List (Fin n × ℕ)),
      (patienceFoldQ tick f piles xs).eval oracle = (patienceFold f piles assign xs).1
  | [], _, _ => rfl
  | y :: ys, piles, assign => by
    simp only [patienceFoldQ, patienceFold, FreeM.eval_bind, eval_patienceInsertQ]
    exact eval_patienceFoldQ oracle tick f ys _ _

/-- Evaluating `patienceNonDecrStepQ` agrees with `patienceNonDecrStep`. -/
theorem eval_patienceNonDecrStepQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (tick : FreeM Q Unit) (f : Fin n → α)
    (R : Finset (Fin n)) :
    (patienceNonDecrStepQ tick f R).eval oracle = patienceNonDecrStep f R := by
  simp only [patienceNonDecrStepQ, patienceNonDecrStep, FreeM.eval_bind, FreeM.eval_pure]
  rw [eval_patienceFoldQ oracle tick f _ [] []]

/-- Evaluating `patienceMaxStepQ` agrees with `patienceMaxStep`. -/
theorem eval_patienceMaxStepQ {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (tick : FreeM Q Unit) (f : Fin n → α)
    (R : Finset (Fin n)) :
    (patienceMaxStepQ tick f R).eval oracle = patienceMaxStep f R := by
  simp only [patienceMaxStepQ, patienceMaxStep, FreeM.eval_bind, FreeM.eval_pure,
    eval_patienceNonDecrStepQ, patienceNonIncrStep]
  rfl

private theorem length_patienceInsert_le {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin n → α)
    (piles : List (PatiencePile n)) (x : Fin n) :
    (patienceInsert f piles x).1.length ≤ piles.length + 1 := by
  dsimp only [patienceInsert]
  split_ifs <;> simp

private theorem cost_patienceInsertQ_le {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → ℕ)
    (tick : FreeM Q Unit) {c : ℕ} (htick : tick.cost oracle weight ≤ c)
    (f : Fin n → α) (piles : List (PatiencePile n)) (x : Fin n) :
    (patienceInsertQ tick f piles x).cost oracle weight ≤ c * (Nat.log 2 piles.length + 1) := by
  simp only [patienceInsertQ, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  refine cost_lowerBoundBy_le oracle weight _ fun m _ _ => ?_
  simpa only [FreeM.cost_bind, FreeM.cost_pure, add_zero] using htick

private theorem cost_patienceFoldQ_le {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → ℕ)
    (tick : FreeM Q Unit) {c : ℕ} (htick : tick.cost oracle weight ≤ c)
    (f : Fin n → α) :
    ∀ (xs : List (Fin n)) (piles : List (PatiencePile n)) (M : ℕ),
      piles.length + xs.length ≤ M →
      (patienceFoldQ tick f piles xs).cost oracle weight ≤
        xs.length * (c * (Nat.log 2 M + 1))
  | [], _, _, _ => by simp [patienceFoldQ]
  | y :: ys, piles, M, hM => by
    simp only [patienceFoldQ, FreeM.cost_bind, eval_patienceInsertQ, List.length_cons]
    have h1 := cost_patienceInsertQ_le oracle weight tick htick f piles y
    have hlog : Nat.log 2 piles.length ≤ Nat.log 2 M := Nat.log_mono_right (by omega)
    have hlen' : (patienceInsert f piles y).1.length + ys.length ≤ M := by
      have := length_patienceInsert_le f piles y
      simp only [List.length_cons] at hM
      omega
    have h2 := cost_patienceFoldQ_le oracle weight tick htick f ys (patienceInsert f piles y).1 M
      hlen'
    have h1' : (patienceInsertQ tick f piles y).cost oracle weight ≤ c * (Nat.log 2 M + 1) :=
      h1.trans (Nat.mul_le_mul_left c (Nat.add_le_add_right hlog 1))
    calc (patienceInsertQ tick f piles y).cost oracle weight +
          (patienceFoldQ tick f (patienceInsert f piles y).1 ys).cost oracle weight
        ≤ c * (Nat.log 2 M + 1) + ys.length * (c * (Nat.log 2 M + 1)) := Nat.add_le_add h1' h2
      _ = (ys.length + 1) * (c * (Nat.log 2 M + 1)) := by ring

/-- Cost bound for `patienceNonDecrStepQ`: at most `c * |R| * (⌊log₂ |R|⌋ + 1)`. -/
theorem cost_patienceNonDecrStepQ_le {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → ℕ)
    (tick : FreeM Q Unit) {c : ℕ} (htick : tick.cost oracle weight ≤ c)
    (f : Fin n → α) (R : Finset (Fin n)) :
    (patienceNonDecrStepQ tick f R).cost oracle weight ≤
      R.card * (c * (Nat.log 2 R.card + 1)) := by
  simp only [patienceNonDecrStepQ, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  have h := cost_patienceFoldQ_le oracle weight tick htick f (R.sort (· ≤ ·)) [] R.card (by simp)
  simpa only [Finset.length_sort] using h

/-- Cost bound for `patienceMaxStepQ`: at most `2 * c * |R| * (⌊log₂ |R|⌋ + 1)`. -/
theorem cost_patienceMaxStepQ_le {Q : Type → Type} {α : Type*} [LinearOrder α] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → ℕ)
    (tick : FreeM Q Unit) {c : ℕ} (htick : tick.cost oracle weight ≤ c)
    (f : Fin n → α) (R : Finset (Fin n)) :
    (patienceMaxStepQ tick f R).cost oracle weight ≤
      2 * c * (R.card * (Nat.log 2 R.card + 1)) := by
  have h1 := cost_patienceNonDecrStepQ_le oracle weight tick htick f R
  have h2 := cost_patienceNonDecrStepQ_le oracle weight tick htick
    (fun i => OrderDual.toDual (f i)) R
  simp only [patienceMaxStepQ, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  calc (patienceNonDecrStepQ tick f R).cost oracle weight +
        (patienceNonDecrStepQ tick (fun i => OrderDual.toDual (f i)) R).cost oracle weight
      ≤ R.card * (c * (Nat.log 2 R.card + 1)) + R.card * (c * (Nat.log 2 R.card + 1)) :=
        Nat.add_le_add h1 h2
    _ = 2 * c * (R.card * (Nat.log 2 R.card + 1)) := by ring

end CslibFrontier.Query
