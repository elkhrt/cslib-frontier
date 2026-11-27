/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.ResidueHashing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Remainder and Radix-Sort Residue Collision Counting on Turing Machines

This module implements deterministic multi-tape Turing machine algorithms with explicit
`ComputableInO` bounds for nonnegative modular remainders and residue collision counting:

1. Nonnegative integer remainder `intRemNat M x = (x % M).toNat` in polynomial time;
2. Radix-sort collision counting `collList M L = ChanHe.coll L.toFinset M` in quasi-linear time;
3. Streaming binary list length `computableInO_listLengthNat` in linear scan time.

## Main definitions

* `CslibFrontier.Complexity.intRemNat`: canonical remainder in `{0, …, M - 1}` of `x : ℤ` modulo
  `M`.
* `CslibFrontier.Complexity.collStep`, `CslibFrontier.Complexity.collSorted`,
  `CslibFrontier.Complexity.collList`: ordered-pair residue collision counting modulo `M`.
* `CslibFrontier.Complexity.collScale`: bit-scale bound for `collList`.

## Main results

* `CslibFrontier.Complexity.intRemNat_cast`, `CslibFrontier.Complexity.intRemNat_eq_iff_dvd`,
  `CslibFrontier.Complexity.computableInPolyTime_intRemNat`: modular remainder properties and
  polynomial-time Turing machine computability.
* `CslibFrontier.Complexity.collList_eq_coll`, `CslibFrontier.Complexity.collList_le_sq`,
  `CslibFrontier.Complexity.computableInO_collList`: exact agreement with `ChanHe.coll` and
  quasi-linear
  Turing machine bound.
* `CslibFrontier.Complexity.computableInO_listLengthNat`: streaming binary list length bound.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.ThreeSum.ChanHe

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

attribute [local irreducible] encNat encIntBin encUnary

section RemainderAndCollisions

/-- Canonical remainder in `{0, …, M - 1}` of `x : ℤ` modulo `M : ℕ` (`0` when `M = 0`). -/
def intRemNat (M : ℕ) (x : ℤ) : ℕ :=
  if M = 0 then 0
  else if x < 0 then
    if x.natAbs % M = 0 then 0 else M - x.natAbs % M
  else x.natAbs % M

theorem intRemNat_lt {M : ℕ} (hM : 0 < M) (x : ℤ) : intRemNat M x < M := by
  unfold intRemNat
  have hmod : x.natAbs % M < M := Nat.mod_lt _ hM
  split_ifs <;> omega

theorem intRemNat_le (M : ℕ) (x : ℤ) : intRemNat M x ≤ M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [intRemNat]
  · exact (intRemNat_lt hM x).le

theorem intRemNat_cast {M : ℕ} (hM : 0 < M) (x : ℤ) :
    ((intRemNat M x : ℕ) : ℤ) = x % (M : ℤ) := by
  unfold intRemNat
  have hmod : x.natAbs % M < M := Nat.mod_lt _ hM
  set q := x.natAbs / M
  set r := x.natAbs % M
  have hdiv : M * q + r = x.natAbs := Nat.div_add_mod x.natAbs M
  have hM0 : ¬ M = 0 := hM.ne'
  split_ifs with hx hr
  · have hx_eq : x = -((x.natAbs : ℕ) : ℤ) := by omega
    have hdvd : (M : ℤ) ∣ x := ⟨-(q : ℤ), by rw [hx_eq, ← hdiv, hr]; push_cast; ring⟩
    exact (Int.emod_eq_zero_of_dvd hdvd).symm
  · have hx_eq : x = -((x.natAbs : ℕ) : ℤ) := by omega
    have hdecomp : x = ((M - r : ℕ) : ℤ) + (M : ℤ) * (-(q : ℤ) - 1) := by
      have hMr : ((M - r : ℕ) : ℤ) = (M : ℤ) - (r : ℤ) := Nat.cast_sub hmod.le
      rw [hx_eq, ← hdiv, hMr]
      push_cast
      ring
    rw [hdecomp, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast (by omega : M - r < M))]
  · have hx_eq : x = ((x.natAbs : ℕ) : ℤ) := by omega
    rw [hx_eq]
    exact (Int.natCast_emod x.natAbs M).symm

theorem intRemNat_eq_iff_dvd {M : ℕ} (hM : 0 < M) (x y : ℤ) :
    intRemNat M x = intRemNat M y ↔ (M : ℤ) ∣ x - y := by
  rw [natCast_dvd_sub_iff_emod_eq, ← intRemNat_cast hM x, ← intRemNat_cast hM y]
  exact ⟨congrArg Nat.cast, fun h => Nat.cast_injective h⟩

@[fun_prop]
theorem computableInPolyTime_intRemNat :
    ComputableInPolyTime (fun p : ℕ × ℤ => intRemNat p.1 p.2)
      (encPair encNat encIntBin) encNat := by
  have hmod := ComputableInPolyTime.binary_mod' (α := ℕ × ℤ)
    (input := encPair encNat encIntBin) (left := fun p => p.2.natAbs) (right := fun p => p.1)
    (by fun_prop) (by fun_prop)
  have h : ComputableInPolyTime
      (fun p : ℕ × ℤ =>
        if decide (p.1 = 0) then 0
        else if decide (p.2 < 0) then
          if decide (p.2.natAbs % p.1 = 0) then 0 else p.1 - p.2.natAbs % p.1
        else p.2.natAbs % p.1)
      (encPair encNat encIntBin) encNat := by fun_prop
  refine h.of_enc_eq fun p => congrArg encNat ?_
  simp only [intRemNat, decide_eq_true_eq]

/-- Streaming step accumulating ordered colliding pairs `(prev, (run, acc))` on sorted residues. -/
def collStep (p : (Option ℕ × (ℕ × ℕ)) × ℕ) : Option ℕ × (ℕ × ℕ) :=
  match p.1.1 with
  | none => (some p.2, (1, p.1.2.2))
  | some r =>
    if p.2 = r then (some r, (p.1.2.1 + 1, p.1.2.2 + 2 * p.1.2.1))
    else (some p.2, (1, p.1.2.2))

/-- Collision count of a sorted list of natural-number residues. -/
def collSorted (R : List ℕ) : ℕ :=
  (R.foldl (fun s r => collStep (s, r)) (none, (0, 0))).2.2

/-- Collision count of `L : List ℤ` modulo `M : ℕ`, matching `ChanHe.coll L.toFinset M`. -/
def collList (M : ℕ) (L : List ℤ) : ℕ :=
  if M = 0 then 0
  else collSorted (radixSortBy id M.size (L.map (intRemNat M)))

private def pairCount : List ℕ → ℕ
  | [] => 0
  | r :: rs => 2 * rs.count r + pairCount rs

private theorem pairCount_perm {R₁ R₂ : List ℕ} (h : R₁.Perm R₂) :
    pairCount R₁ = pairCount R₂ := by
  induction h with
  | nil => rfl
  | cons r hp ih => simp [pairCount, ih, hp.count_eq]
  | swap a b rs =>
    simp only [pairCount, List.count_cons]
    by_cases hab : a = b
    · subst hab; simp
    · have hba : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm hab)
      have hab' : (a == b) = false := beq_eq_false_iff_ne.mpr hab
      simp only [hba, hab']
      omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem foldl_collStep_sorted (r run acc : ℕ) (s : List ℕ)
    (hs : List.Pairwise (· ≤ ·) (r :: s)) :
    (s.foldl (fun st x => collStep (st, x)) (some r, (run, acc))).2.2 =
      acc + 2 * run * s.count r + pairCount s := by
  induction s generalizing r run acc with
  | nil => simp [pairCount]
  | cons x xs ih =>
    obtain ⟨hr_le, hxs⟩ := List.pairwise_cons.mp hs
    have hrx : r ≤ x := hr_le x (List.mem_cons_self ..)
    by_cases hxr : x = r
    · subst hxr
      have hstep_eq : collStep ((some x, (run, acc)), x) = (some x, (run + 1, acc + 2 * run)) := by
        simp [collStep]
      rw [List.foldl_cons, hstep_eq, ih x (run + 1) (acc + 2 * run) hxs]
      simp only [pairCount, List.count_cons_self]
      ring
    · have hlt : r < x := lt_of_le_of_ne hrx (Ne.symm hxr)
      have hcnt0 : (x :: xs).count r = 0 := by
        rw [List.count_eq_zero]
        intro hz
        have hrz : r < r := lt_of_lt_of_le hlt (by
          rcases List.mem_cons.mp hz with hrx' | hz'
          · exact hrx'.symm.le
          · exact (List.pairwise_cons.mp hxs).1 r hz')
        omega
      have hstep_eq : collStep ((some r, (run, acc)), x) = (some x, (1, acc)) := by
        simp [collStep, hxr]
      rw [List.foldl_cons, hstep_eq, ih x 1 acc hxs, hcnt0]
      simp only [pairCount, mul_zero, add_zero]
      ring

private theorem collSorted_eq_pairCount {R : List ℕ} (hR : List.Pairwise (· ≤ ·) R) :
    collSorted R = pairCount R := by
  rcases R with _ | ⟨r, rs⟩
  · rfl
  · have hstep_eq : collStep ((none, (0, 0)), r) = (some r, (1, 0)) := rfl
    rw [collSorted, List.foldl_cons, hstep_eq, foldl_collStep_sorted r 1 0 rs hR, pairCount]
    ring

private theorem pairCount_rem_eq_coll {M : ℕ} (hM : 0 < M) {L : List ℤ} (hL : L.Nodup) :
    pairCount (L.map (intRemNat M)) = coll L.toFinset M := by
  induction L with
  | nil => simp [pairCount, coll]
  | cons x xs ih =>
    obtain ⟨hx_mem, hxs⟩ := List.nodup_cons.mp hL
    have hxS : x ∉ xs.toFinset := by simpa using hx_mem
    set S := xs.toFinset
    have hsplit : {p ∈ (insert x S).offDiag | (M : ℤ) ∣ p.1 - p.2} =
        (({x} : Finset ℤ) ×ˢ {y ∈ S | (M : ℤ) ∣ x - y} ∪
          {y ∈ S | (M : ℤ) ∣ y - x} ×ˢ ({x} : Finset ℤ)) ∪
          {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2} := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_union,
        Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨rfl | ha, rfl | hb, hne⟩, hdvd⟩
        · exact (hne rfl).elim
        · exact Or.inl (Or.inl ⟨rfl, hb, hdvd⟩)
        · exact Or.inl (Or.inr ⟨⟨ha, hdvd⟩, rfl⟩)
        · exact Or.inr ⟨⟨ha, hb, hne⟩, hdvd⟩
      · rintro ((⟨rfl, hb, hdvd⟩ | ⟨⟨ha, hdvd⟩, rfl⟩) | ⟨⟨ha, hb, hne⟩, hdvd⟩)
        · exact ⟨⟨Or.inl rfl, Or.inr hb, fun h => hxS (h ▸ hb)⟩, hdvd⟩
        · exact ⟨⟨Or.inr ha, Or.inl rfl, fun h => hxS (h ▸ ha)⟩, hdvd⟩
        · exact ⟨⟨Or.inr ha, Or.inr hb, hne⟩, hdvd⟩
    have hdisj1 : Disjoint (({x} : Finset ℤ) ×ˢ {y ∈ S | (M : ℤ) ∣ x - y})
        ({y ∈ S | (M : ℤ) ∣ y - x} ×ˢ ({x} : Finset ℤ)) := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at h1 h2
      exact hxS (h1.1 ▸ h2.1.1)
    have hdisj2 : Disjoint
        (({x} : Finset ℤ) ×ˢ {y ∈ S | (M : ℤ) ∣ x - y} ∪
          {y ∈ S | (M : ℤ) ∣ y - x} ×ˢ ({x} : Finset ℤ))
        {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2} := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_filter, Finset.mem_offDiag] at h1 h2
      rcases h1 with ⟨rfl, _⟩ | ⟨_, rfl⟩
      · exact hxS h2.1.1
      · exact hxS h2.1.2.1
    have hsymm : {y ∈ S | (M : ℤ) ∣ y - x} = {y ∈ S | (M : ℤ) ∣ x - y} := by
      ext y
      simp only [Finset.mem_filter, ← neg_sub x y, dvd_neg]
    have hcard_filter :
        ({y ∈ S | (M : ℤ) ∣ x - y} : Finset ℤ).card =
          (xs.map (intRemNat M)).count (intRemNat M x) := by
      have hfeq : ({y ∈ S | (M : ℤ) ∣ x - y} : Finset ℤ) =
          (xs.filter fun y => decide (intRemNat M y = intRemNat M x)).toFinset := by
        ext y
        simp only [S, Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
          intRemNat_eq_iff_dvd hM, ← neg_sub x y, dvd_neg]
      rw [hfeq, List.toFinset_card_of_nodup (hxs.filter _)]
      clear hfeq hxS hxs hx_mem hL ih hsplit hdisj1 hdisj2 hsymm S
      induction xs with
      | nil => rfl
      | cons z zs ihz =>
        simp only [List.filter_cons, List.map_cons, List.count_cons, beq_iff_eq, decide_eq_true_eq]
        split_ifs <;> simp [ihz]
    have ih' : pairCount (xs.map (intRemNat M)) = {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2}.card :=
      ih hxs
    rw [List.map_cons, pairCount, ih', List.toFinset_cons, coll]
    change 2 * (xs.map (intRemNat M)).count (intRemNat M x) +
        {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2}.card =
      {p ∈ (insert x S).offDiag | (M : ℤ) ∣ p.1 - p.2}.card
    rw [hsplit, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_product, Finset.card_product, Finset.card_singleton, one_mul, mul_one,
      hsymm, hcard_filter]
    omega

/-- For any duplicate-free integer list `L` and modulus `M`, `collList M L` equals
`ChanHe.coll L.toFinset M`. -/
theorem collList_eq_coll (M : ℕ) {L : List ℤ} (hL : L.Nodup) :
    collList M L = coll L.toFinset M := by
  by_cases hM : M = 0
  · subst hM
    simp only [collList, ↓reduceIte, coll, Nat.cast_zero, zero_dvd_iff, sub_eq_zero]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    exact (Finset.mem_offDiag.mp hp).2.2
  · have hM' : 0 < M := Nat.pos_of_ne_zero hM
    simp only [collList, hM, ↓reduceIte]
    have hlt : ∀ r ∈ L.map (intRemNat M), r < 2 ^ M.size := by
      intro r hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      exact (intRemNat_lt hM' x).trans (Nat.lt_size_self M)
    rw [collSorted_eq_pairCount (pairwise_radixSortBy id M.size hlt),
      pairCount_perm (radixSortBy_perm id M.size _), pairCount_rem_eq_coll hM' hL]

theorem collList_le_sq (M : ℕ) (L : List ℤ) : collList M L ≤ L.length ^ 2 := by
  suffices ∀ (t : List ℕ) (o : Option ℕ) (run acc seen : ℕ),
      run ≤ seen → acc ≤ seen ^ 2 →
      ((t.foldl (fun s r => collStep (s, r)) (o, (run, acc))).2.2 ≤ (seen + t.length) ^ 2) by
    by_cases hM : M = 0
    · simp [collList, hM]
    · simp only [collList, hM, ↓reduceIte, collSorted]
      have hlen : (radixSortBy id M.size (L.map (intRemNat M))).length = L.length := by
        simp
      simpa [hlen] using this (radixSortBy id M.size (L.map (intRemNat M))) none 0 0 0
        le_rfl le_rfl
  intro t
  induction t with
  | nil => intro _ _ _ _ _ hacc; simpa using hacc
  | cons x xs ih =>
    intro o run acc seen hrun hacc
    have h1 : (seen + (x :: xs).length) ^ 2 = (seen + 1 + xs.length) ^ 2 := by
      simp only [List.length_cons]; ring
    rw [h1]
    rcases o with _ | r
    · exact ih (some x) 1 acc (seen + 1) (by omega) (by nlinarith)
    · simp only [List.foldl_cons, collStep]
      split_ifs
      · exact ih (some r) (run + 1) (acc + 2 * run) (seen + 1) (by omega) (by nlinarith)
      · exact ih (some x) 1 acc (seen + 1) (by omega) (by nlinarith)

private theorem foldl_collStep_state_bounds (t : List ℕ) (B : ℕ) (hB : ∀ r ∈ t, r.size ≤ B) :
    let st := t.foldl (fun s r => collStep (s, r)) (none, (0, 0))
    (∀ r, st.1 = some r → r.size ≤ B) ∧ st.2.1 ≤ t.length ∧ st.2.2 ≤ t.length ^ 2 := by
  suffices ∀ (u : List ℕ) (o : Option ℕ) (run acc seen : ℕ),
      (∀ r ∈ u, r.size ≤ B) → (∀ r, o = some r → r.size ≤ B) →
      run ≤ seen → acc ≤ seen ^ 2 →
      let st := u.foldl (fun s r => collStep (s, r)) (o, (run, acc))
      (∀ r, st.1 = some r → r.size ≤ B) ∧ st.2.1 ≤ seen + u.length ∧
        st.2.2 ≤ (seen + u.length) ^ 2 by
    simpa using this t none 0 0 0 hB (by simp) le_rfl le_rfl
  intro u
  induction u with
  | nil =>
    intro o run acc seen _ ho hrun hacc
    simpa using ⟨ho, hrun, hacc⟩
  | cons x xs ih =>
    intro o run acc seen hu ho hrun hacc
    have hxB : x.size ≤ B := hu x (List.mem_cons_self ..)
    have hxsB : ∀ r ∈ xs, r.size ≤ B := fun r hr => hu r (List.mem_cons_of_mem _ hr)
    have hlen : seen + (x :: xs).length = seen + 1 + xs.length := by
      simp only [List.length_cons]; omega
    rw [hlen]
    rcases o with _ | r
    · exact ih (some x) 1 acc (seen + 1) hxsB (by rintro _ ⟨rfl⟩; exact hxB)
        (by omega) (by nlinarith)
    · simp only [List.foldl_cons, collStep]
      split_ifs
      · exact ih (some r) (run + 1) (acc + 2 * run) (seen + 1) hxsB ho
          (by omega) (by nlinarith)
      · exact ih (some x) 1 acc (seen + 1) hxsB (by rintro _ ⟨rfl⟩; exact hxB)
          (by omega) (by nlinarith)

/-- Encoded list length is bounded by `l.length * (2 * b + 1)` when items have length `≤ b`. -/
theorem length_encList_le_mul {α : Type} (enc : α ↪ List Bool) (l : List α) {b : ℕ}
    (hb : ∀ a ∈ l, (enc a).length ≤ b) :
    (encList enc l).length ≤ l.length * (2 * b + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [encList_cons, List.length_append, length_frame, List.length_cons]
    have ha := hb a (List.mem_cons_self ..)
    have hl := ih fun x hx => hb x (List.mem_cons_of_mem _ hx)
    nlinarith

/-- Bit-scale parameter for `collList M L`. -/
def collScale (p : ℕ × List ℤ) : ℕ :=
  p.1.size + listMax (fun x => (encIntBin x).length) p.2 + p.2.length.size + 1

/-- Componentwise upper bound on `collScale`. -/
theorem collScale_le {p : ℕ × List ℤ} {bM bL blen : ℕ}
    (hM : p.1.size ≤ bM) (hL : listMax (fun x => (encIntBin x).length) p.2 ≤ bL)
    (hlen : p.2.length.size ≤ blen) :
    collScale p ≤ bM + bL + blen + 1 := by
  dsimp only [collScale]
  omega

/-- `collSorted` runs in linear scan time plus polynomial per-item work in `(R.length.size + b)`. -/
theorem computableInO_collSorted :
    ∃ d, ComputableInO collSorted (encList encNat) encNat
      (fun R => (R.length + 1) * (listMax Nat.size R + R.length.size + 1) ^ d)
      (fun R => (R.length + 1) * (listMax Nat.size R + R.length.size + 1) ^ d) := by
  let encSt := encPair (encOption encNat) (encPair encNat encNat)
  have hstepPt : ComputableInPolyTime collStep (encPair encSt encNat) encSt := by
    have h : ComputableInPolyTime
        (fun p : (Option ℕ × (ℕ × ℕ)) × ℕ =>
          if p.1.1.isSome then
            if decide (p.2 = p.1.1.getD 0) then
              (some (p.1.1.getD 0), (p.1.2.1 + 1, p.1.2.2 + 2 * p.1.2.1))
            else (some p.2, (1, p.1.2.2))
          else (some p.2, (1, p.1.2.2)))
        (encPair encSt encNat) encSt := by fun_prop
    refine h.of_enc_eq fun p => ?_
    rcases p with ⟨⟨_ | r, run, acc⟩, x⟩
    · rfl
    · simp only [collStep, Option.isSome_some, ↓reduceIte, Option.getD_some, decide_eq_true_eq]
  let lMax : (Option ℕ × (ℕ × ℕ)) × List ℕ → ℕ :=
    fun p => 2 * (encSt p.1).length + 6 * listMax Nat.size p.2 + 6 * p.2.length.size + 24
  obtain ⟨dc, hfold⟩ := computableInO_streamFold (lMax := lMax)
    Prod.fst Prod.snd (fun _ => rfl) hstepPt
    (fun p j _ => by
      by_cases hp0 : p.1 = (none, (0, 0))
      · rw [hp0]
        simp only [streamState]
        have hb := foldl_collStep_state_bounds (p.2.take j) (listMax Nat.size p.2)
          fun r hr => le_listMax (List.mem_of_mem_take hr)
        set st := (p.2.take j).foldl (fun s r => collStep (s, r)) (none, (0, 0))
        have hlen_t : (p.2.take j).length ≤ p.2.length := List.length_take_le' j p.2
        have hrun_sz : st.2.1.size ≤ p.2.length.size := Nat.size_le_size (hb.2.1.trans hlen_t)
        have hacc_sz : st.2.2.size ≤ 2 * p.2.length.size + 1 :=
          (Nat.size_le_size (hb.2.2.trans (Nat.pow_le_pow_left hlen_t 2))).trans
            (Nat.size_pow_le p.2.length 2)
        have ho_len : (encOption encNat st.1).length ≤ listMax Nat.size p.2 + 1 := by
          rcases ho : st.1 with _ | r
          · simp
          · simp only [encOption_some, List.length_cons, length_encNat]
            exact Nat.succ_le_succ (hb.1 r ho)
        simp only [encSt, length_encPair, length_encNat]
        dsimp only [lMax]
        omega
      · have hgen : ∀ (t : List ℕ) (o : Option ℕ) (run acc : ℕ),
            t.length ≤ p.2.length → (∀ r ∈ t, r.size ≤ listMax Nat.size p.2) →
            let st := t.foldl (fun s r => collStep (s, r)) (o, (run, acc))
            (encSt st).length ≤
              2 * (encSt (o, (run, acc))).length + 6 * listMax Nat.size p.2 +
                6 * p.2.length.size + 24 := by
          intro t o run acc htl htB
          suffices ∀ (u : List ℕ) (o' : Option ℕ) (rn ac sn : ℕ),
              (∀ r ∈ u, r.size ≤ listMax Nat.size p.2) →
              (∀ r, o' = some r → r.size ≤ max (encOption encNat o).length (listMax Nat.size p.2)) →
              rn ≤ run + sn → ac ≤ acc + 2 * (run + sn) ^ 2 →
              let st := u.foldl (fun s r => collStep (s, r)) (o', (rn, ac))
              (∀ r, st.1 = some r →
                r.size ≤ max (encOption encNat o).length (listMax Nat.size p.2)) ∧
                st.2.1 ≤ run + (sn + u.length) ∧ st.2.2 ≤ acc + 2 * (run + (sn + u.length)) ^ 2 by
            have hmain := this t o run acc 0 htB
              (fun r hr => by
                subst hr
                simp only [encOption_some, List.length_cons, length_encNat]
                exact (Nat.le_succ _).trans (le_max_left _ _))
              le_rfl (by omega)
            set st := t.foldl (fun s r => collStep (s, r)) (o, (run, acc))
            have ho' : (encOption encNat st.1).length ≤
                (encOption encNat o).length + listMax Nat.size p.2 + 1 := by
              rcases hs1 : st.1 with _ | r
              · simp
              · simp only [encOption_some, List.length_cons, length_encNat]
                have := hmain.1 r hs1
                omega
            have hrn_sz : st.2.1.size ≤ run.size + p.2.length.size + 1 :=
              (Nat.size_le_size (hmain.2.1.trans (by omega : run + (0 + t.length) ≤
                run + p.2.length))).trans (Nat.size_add_le _ _)
            have hac_le : st.2.2 ≤ acc + 4 * run ^ 2 + 4 * p.2.length ^ 2 := by
              have h0 : 2 * (run + (0 + t.length)) ^ 2 ≤ 4 * run ^ 2 + 4 * t.length ^ 2 := by
                have hsq : ((run : ℤ) - (t.length : ℤ)) ^ 2 ≥ 0 := sq_nonneg _
                zify; nlinarith
              have ht2 : t.length ^ 2 ≤ p.2.length ^ 2 := Nat.pow_le_pow_left htl 2
              exact hmain.2.2.trans (by omega)
            have hac_sz : st.2.2.size ≤ acc.size + 2 * run.size + 2 * p.2.length.size + 10 := by
              have h1 := (Nat.size_le_size hac_le).trans
                (Nat.size_add_le (acc + 4 * run ^ 2) (4 * p.2.length ^ 2))
              have h2 := Nat.size_add_le acc (4 * run ^ 2)
              have h3 : (4 * run ^ 2).size ≤ 2 * run.size + 4 := by
                have := Nat.size_mul_le 4 (run ^ 2)
                have := Nat.size_pow_le run 2
                have h4sz : (4 : ℕ).size = 3 := by decide
                omega
              have h4 : (4 * p.2.length ^ 2).size ≤ 2 * p.2.length.size + 4 := by
                have := Nat.size_mul_le 4 (p.2.length ^ 2)
                have := Nat.size_pow_le p.2.length 2
                have h4sz : (4 : ℕ).size = 3 := by decide
                omega
              omega
            simp only [encSt, length_encPair, length_encNat]
            omega
          intro u
          induction u with
          | nil =>
            intro o' rn ac sn _ ho' hrn hac
            exact ⟨ho', by simpa using hrn, by simpa using hac⟩
          | cons x xs ih =>
            intro o' rn ac sn huB ho' hrn hac
            have hxB : x.size ≤ max (encOption encNat o).length (listMax Nat.size p.2) :=
              (huB x (List.mem_cons_self ..)).trans (le_max_right _ _)
            have hxsB : ∀ r ∈ xs, r.size ≤ listMax Nat.size p.2 :=
              fun r hr => huB r (List.mem_cons_of_mem _ hr)
            have hlen : sn + (x :: xs).length = sn + 1 + xs.length := by
              simp only [List.length_cons]; omega
            rw [hlen]
            rcases o' with _ | r
            · exact ih (some x) 1 ac (sn + 1) hxsB (by rintro _ ⟨rfl⟩; exact hxB)
                (by omega) (by nlinarith)
            · simp only [List.foldl_cons, collStep]
              split_ifs
              · exact ih (some r) (rn + 1) (ac + 2 * rn) (sn + 1) hxsB ho'
                  (by omega) (by nlinarith)
              · exact ih (some x) 1 ac (sn + 1) hxsB (by rintro _ ⟨rfl⟩; exact hxB)
                  (by omega) (by nlinarith)
        exact hgen (p.2.take j) p.1.1 p.1.2.1 p.1.2.2 (List.length_take_le' j p.2)
          fun r hr => le_listMax (List.mem_of_mem_take hr))
    (fun p j hj => by
      rw [length_encNat]
      have := le_listMax (f := Nat.size) (List.getElem_mem hj)
      dsimp only [lMax]
      omega)
  have hinit : ComputableInO (fun R : List ℕ => ((none, (0, 0)), R))
      (encList encNat) (encPair encSt (encList encNat))
      (fun R => (encList encNat R).length) (fun R => (encList encNat R).length) :=
    ((ComputableInO.constZero ((none : Option ℕ), (0, 0))).prod
      (ComputableInO.of_eq fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)
  have hcomp := ((hfold.comp hinit).snd').snd'
  have hst0 : (encSt ((none : Option ℕ), (0, 0))).length = 2 := by
    simp only [encSt, length_encPair, encOption_none, List.length_nil, length_encNat,
      Nat.size_zero]
  refine ⟨dc + 1, (hcomp.of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  · refine BigOLe.of_le_linear (16 + 29 ^ dc) 0 fun R => ?_
    set S := listMax Nat.size R + R.length.size + 1
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hS_pow : S ≤ S ^ (dc + 1) := Nat.le_self_pow (by omega) S
    have hlenR : (encList encNat R).length ≤ 3 * ((R.length + 1) * S ^ (dc + 1)) := by
      have h1 := length_encList_le_mul encNat R (b := listMax Nat.size R) fun r hr => by
        rw [length_encNat]; exact le_listMax hr
      have h2 : 2 * listMax Nat.size R + 1 ≤ 3 * S := by dsimp only [S]; omega
      calc (encList encNat R).length ≤ R.length * (3 * S) := h1.trans (Nat.mul_le_mul_left _ h2)
        _ ≤ 3 * ((R.length + 1) * S ^ (dc + 1)) := by
          nlinarith [Nat.mul_le_mul (Nat.le_succ R.length) hS_pow]
    have hlmax : lMax ((none, (0, 0)), R) + 1 ≤ 29 * S := by
      dsimp only [lMax, S]
      rw [hst0]
      omega
    have hpow : (lMax ((none, (0, 0)), R) + 1) ^ dc ≤ 29 ^ dc * S ^ (dc + 1) :=
      calc (lMax ((none, (0, 0)), R) + 1) ^ dc ≤ (29 * S) ^ dc := Nat.pow_le_pow_left hlmax dc
        _ = 29 ^ dc * S ^ dc := Nat.mul_pow 29 S dc
        _ ≤ 29 ^ dc * S ^ (dc + 1) := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hS1 (Nat.le_succ dc))
    have hmul : (R.length + 1) * (lMax ((none, (0, 0)), R) + 1) ^ dc ≤
        29 ^ dc * ((R.length + 1) * S ^ (dc + 1)) :=
      (Nat.mul_le_mul_left (R.length + 1) hpow).trans_eq (by ring)
    have hpair : (encPair encSt (encList encNat) ((none, (0, 0)), R)).length ≤
        12 * ((R.length + 1) * S ^ (dc + 1)) := by
      rw [length_encPair, hst0]
      dsimp only
      have h1 : 1 ≤ (R.length + 1) * S ^ (dc + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ hS1)
      omega
    change (encList encNat R).length +
      ((encPair encSt (encList encNat) ((none, (0, 0)), R)).length +
        (R.length + 1) * (lMax ((none, (0, 0)), R) + 1) ^ dc) ≤
      (16 + 29 ^ dc) * ((R.length + 1) * S ^ (dc + 1)) + 0
    nlinarith
  · refine BigOLe.of_le_linear (4 + 29 ^ dc) 0 fun R => ?_
    set S := listMax Nat.size R + R.length.size + 1
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hS_pow : S ≤ S ^ (dc + 1) := Nat.le_self_pow (by omega) S
    have hlenR : (encList encNat R).length ≤ 3 * ((R.length + 1) * S ^ (dc + 1)) := by
      have h1 := length_encList_le_mul encNat R (b := listMax Nat.size R) fun r hr => by
        rw [length_encNat]; exact le_listMax hr
      have h2 : 2 * listMax Nat.size R + 1 ≤ 3 * S := by dsimp only [S]; omega
      calc (encList encNat R).length ≤ R.length * (3 * S) := h1.trans (Nat.mul_le_mul_left _ h2)
        _ ≤ 3 * ((R.length + 1) * S ^ (dc + 1)) := by
          nlinarith [Nat.mul_le_mul (Nat.le_succ R.length) hS_pow]
    have hlmax : lMax ((none, (0, 0)), R) + 1 ≤ 29 * S := by
      dsimp only [lMax, S]
      rw [hst0]
      omega
    have hpow : (lMax ((none, (0, 0)), R) + 1) ^ dc ≤
        29 ^ dc * ((R.length + 1) * S ^ (dc + 1)) := by
      calc (lMax ((none, (0, 0)), R) + 1) ^ dc ≤ (29 * S) ^ dc := Nat.pow_le_pow_left hlmax dc
        _ = 29 ^ dc * S ^ dc := Nat.mul_pow 29 S dc
        _ ≤ 29 ^ dc * S ^ (dc + 1) := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hS1 (Nat.le_succ dc))
        _ ≤ 29 ^ dc * ((R.length + 1) * S ^ (dc + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    change (encList encNat R).length + (lMax ((none, (0, 0)), R) + 1) ^ dc ≤
      (4 + 29 ^ dc) * ((R.length + 1) * S ^ (dc + 1)) + 0
    nlinarith

/-- `collList M L` runs in quasi-linear time `O((L.length + 1) * collScale (M, L) ^ d)`. -/
theorem computableInO_collList :
    ∃ d, ComputableInO (fun p : ℕ × List ℤ => collList p.1 p.2)
      (encPair encNat (encList encIntBin)) encNat
      (fun p => (p.2.length + 1) * collScale p ^ d)
      (fun p => (p.2.length + 1) * collScale p ^ d) := by
  let encIn := encPair encNat (encList encIntBin)
  obtain ⟨dm, hmap⟩ := computableInO_streamMapWith
    (f := fun q : ℕ × ℤ => intRemNat q.1 q.2) computableInPolyTime_intRemNat
    (lMax := collScale)
    (fun p => by rw [length_encNat]; dsimp only [collScale]; omega)
    (fun p j hj => by
      have := le_listMax (f := fun x => (encIntBin x).length) (List.getElem_mem hj)
      dsimp only [collScale]; omega)
  have hsizePt : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  obtain ⟨dsz, _, hsizeDeg⟩ := hsizePt.exists_degree
  have hlenIn_le (p : ℕ × List ℤ) : (encIn p).length ≤ 6 * ((p.2.length + 1) * collScale p) := by
    rw [length_encPair, length_encNat]
    have hL := length_encList_le_mul encIntBin p.2
      (b := listMax (fun x => (encIntBin x).length) p.2)
      fun x hx => le_listMax (f := fun x => (encIntBin x).length) hx
    have h2 : 2 * listMax (fun x => (encIntBin x).length) p.2 + 1 ≤ 3 * collScale p := by
      dsimp only [collScale]; omega
    have hL' : (encList encIntBin p.2).length ≤ 3 * (p.2.length * collScale p) :=
      (hL.trans (Nat.mul_le_mul_left _ h2)).trans_eq (by ring)
    have hM : p.1.size ≤ collScale p := by dsimp only [collScale]; omega
    nlinarith
  have hb : ComputableInO (fun p : ℕ × List ℤ => p.1.size) encIn encNat
      (fun p => (p.2.length + 1) * collScale p ^ (dsz + 1))
      (fun p => (p.2.length + 1) * collScale p ^ (dsz + 1)) := by
    refine (hsizeDeg.inO.comp (ComputableInO.fst encNat (encList encIntBin))).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (6 + 2 ^ dsz) 0 fun p => ?_
      have hM : p.1.size + 1 ≤ 2 * collScale p := by dsimp only [collScale]; omega
      have hpow : (p.1.size + 1) ^ dsz ≤ 2 ^ dsz * ((p.2.length + 1) * collScale p ^ (dsz + 1)) :=
        calc (p.1.size + 1) ^ dsz ≤ (2 * collScale p) ^ dsz := Nat.pow_le_pow_left hM dsz
          _ = 2 ^ dsz * collScale p ^ dsz := Nat.mul_pow 2 _ dsz
          _ ≤ 2 ^ dsz * collScale p ^ (dsz + 1) := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (Nat.le_succ dsz))
          _ ≤ 2 ^ dsz * ((p.2.length + 1) * collScale p ^ (dsz + 1)) :=
              Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have hS1 : collScale p ≤ collScale p ^ (dsz + 1) := Nat.le_self_pow (by omega) _
      have hin : (encIn p).length ≤ 6 * ((p.2.length + 1) * collScale p ^ (dsz + 1)) :=
        (hlenIn_le p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS1])
      change (encIn p).length + ((encNat p.1).length + 1) ^ dsz ≤ _
      rw [length_encNat]
      nlinarith
  have hmap' : ComputableInO (fun p : ℕ × List ℤ => p.2.map (intRemNat p.1)) encIn (encList encNat)
      (fun p => (p.2.length + 1) * collScale p ^ (dm + 1))
      (fun p => (p.2.length + 1) * collScale p ^ (dm + 1)) := by
    refine hmap.weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (6 + 2 ^ dm) 0 fun p => ?_
      have hS1 : collScale p ≤ collScale p ^ (dm + 1) := Nat.le_self_pow (by omega) _
      have hin : (encIn p).length ≤ 6 * ((p.2.length + 1) * collScale p ^ (dm + 1)) :=
        (hlenIn_le p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS1])
      have hpow : (collScale p + 1) ^ dm ≤ 2 ^ dm * collScale p ^ (dm + 1) :=
        calc (collScale p + 1) ^ dm ≤ (2 * collScale p) ^ dm :=
              Nat.pow_le_pow_left (by dsimp only [collScale]; omega) dm
          _ = 2 ^ dm * collScale p ^ dm := Nat.mul_pow 2 _ dm
          _ ≤ 2 ^ dm * collScale p ^ (dm + 1) := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (Nat.le_succ dm))
      have hmul : (p.2.length + 1) * (collScale p + 1) ^ dm ≤
          2 ^ dm * ((p.2.length + 1) * collScale p ^ (dm + 1)) :=
        (Nat.mul_le_mul_left (p.2.length + 1) hpow).trans_eq (by ring)
      change (encIn p).length + (p.2.length + 1) * (collScale p + 1) ^ dm ≤ _
      nlinarith
  obtain ⟨dr, hsort⟩ := computableInO_radixSortBy (lMax := collScale)
    (by fun_prop : ComputableInPolyTime (id : ℕ → ℕ) encNat encNat)
    hb hmap'
    (fun p => by
      rw [length_encNat]
      exact (Nat.size_le_self _).trans (by dsimp only [collScale]; omega))
    (fun p r hr => by
      rw [length_encNat]
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      exact (Nat.size_le_size (intRemNat_le p.1 x)).trans (by dsimp only [collScale]; omega))
  let D₁ := dm + dsz + dr + 3
  have hsort' : ComputableInO
      (fun p : ℕ × List ℤ => radixSortBy id p.1.size (p.2.map (intRemNat p.1)))
      encIn (encList encNat)
      (fun p => (p.2.length + 1) * collScale p ^ D₁)
      (fun p => (p.2.length + 1) * collScale p ^ D₁) := by
    have hlen_rem (p : ℕ × List ℤ) :
        (encList encNat (p.2.map (intRemNat p.1))).length ≤
          3 * ((p.2.length + 1) * collScale p) := by
      have h1 := length_encList_le_mul encNat (p.2.map (intRemNat p.1)) (b := p.1.size)
        fun r hr => by
          rw [length_encNat]
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
          exact Nat.size_le_size (intRemNat_le p.1 x)
      rw [List.length_map] at h1
      have h2 : 2 * p.1.size + 1 ≤ 3 * collScale p := by dsimp only [collScale]; omega
      exact (h1.trans (Nat.mul_le_mul_left _ h2)).trans (by nlinarith)
    refine hsort.weaken ?_ ?_
    · refine BigOLe.add (BigOLe.add ?_ ?_) ?_
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (by dsimp only [D₁]; omega))
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (by dsimp only [D₁]; omega))
      · refine BigOLe.of_le_linear (8 + 2 ^ dr) 0 fun p => ?_
        set S := collScale p
        have hS1 : 1 ≤ S := by dsimp only [S, collScale]; omega
        have hS_pow : S ≤ S ^ (D₁ - 1) := Nat.le_self_pow (by dsimp only [D₁]; omega) S
        have hSD : S * S ^ (D₁ - 1) = S ^ D₁ :=
          (pow_succ' S (D₁ - 1)).symm.trans (congrArg (S ^ ·) (by dsimp only [D₁]; omega))
        have ha : (encList encNat (p.2.map (intRemNat p.1))).length ≤
            3 * ((p.2.length + 1) * S ^ (D₁ - 1)) :=
          (hlen_rem p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS_pow])
        have hb' : ((p.2.map (intRemNat p.1)).length + 1) * (S + 1) ^ dr ≤
            2 ^ dr * ((p.2.length + 1) * S ^ (D₁ - 1)) := by
          rw [List.length_map]
          have hp : (S + 1) ^ dr ≤ 2 ^ dr * S ^ (D₁ - 1) :=
            calc (S + 1) ^ dr ≤ (2 * S) ^ dr := Nat.pow_le_pow_left (by omega) dr
              _ = 2 ^ dr * S ^ dr := Nat.mul_pow 2 S dr
              _ ≤ 2 ^ dr * S ^ (D₁ - 1) := Nat.mul_le_mul_left _
                  (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
          exact (Nat.mul_le_mul_left _ hp).trans_eq (by ring)
        have hc : ((encNat p.1.size).length + 1) ^ 2 ≤ 4 * ((p.2.length + 1) * S ^ (D₁ - 1)) := by
          rw [length_encNat]
          have hsz : p.1.size.size + 1 ≤ 2 * S := by
            have := Nat.size_le_self p.1.size
            dsimp only [S, collScale]; omega
          have hsq : (p.1.size.size + 1) ^ 2 ≤ 4 * S ^ (D₁ - 1) :=
            calc (p.1.size.size + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left hsz 2
              _ = 4 * S ^ 2 := by ring
              _ ≤ 4 * S ^ (D₁ - 1) := Nat.mul_le_mul_left 4
                  (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
          exact hsq.trans (by nlinarith [Nat.one_le_pow (D₁ - 1) S hS1])
        have hsum : (encList encNat (p.2.map (intRemNat p.1))).length +
            ((p.2.map (intRemNat p.1)).length + 1) * (S + 1) ^ dr +
            ((encNat p.1.size).length + 1) ^ 2 ≤
            (8 + 2 ^ dr) * ((p.2.length + 1) * S ^ (D₁ - 1)) := by
          have := Nat.add_le_add (Nat.add_le_add ha hb') hc
          nlinarith
        have hbp1 : p.1.size + 1 ≤ S := by dsimp only [S, collScale]; omega
        calc (p.1.size + 1) * _ ≤ S * ((8 + 2 ^ dr) * ((p.2.length + 1) * S ^ (D₁ - 1))) :=
              Nat.mul_le_mul hbp1 hsum
          _ = (8 + 2 ^ dr) * ((p.2.length + 1) * (S * S ^ (D₁ - 1))) := by ring
          _ = (8 + 2 ^ dr) * ((p.2.length + 1) * S ^ D₁) + 0 := by rw [hSD, add_zero]
    · refine BigOLe.add (BigOLe.add (BigOLe.add (BigOLe.add ?_ ?_) ?_) ?_) ?_
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (by dsimp only [D₁]; omega))
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (by dsimp only [D₁]; omega))
      · refine BigOLe.of_le_linear 3 0 fun p => ?_
        have hS : collScale p ≤ collScale p ^ D₁ := Nat.le_self_pow (by dsimp only [D₁]; omega) _
        exact (hlen_rem p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS])
      · refine BigOLe.of_le_linear (2 ^ dr) 0 fun p => ?_
        rw [List.length_map]
        have hS1 : 1 ≤ collScale p := by dsimp only [collScale]; omega
        have hp : (collScale p + 1) ^ dr ≤ 2 ^ dr * collScale p ^ D₁ :=
          calc (collScale p + 1) ^ dr ≤ (2 * collScale p) ^ dr :=
                Nat.pow_le_pow_left (by omega) dr
            _ = 2 ^ dr * collScale p ^ dr := Nat.mul_pow 2 _ dr
            _ ≤ 2 ^ dr * collScale p ^ D₁ := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
        exact (Nat.mul_le_mul_left _ hp).trans_eq (by ring)
      · refine BigOLe.of_le_linear 1 0 fun p => ?_
        rw [length_encNat]
        have h1 : p.1.size.size ≤ collScale p :=
          (Nat.size_le_self _).trans (by dsimp only [collScale]; omega)
        have h2 : collScale p ≤ collScale p ^ D₁ := Nat.le_self_pow (by dsimp only [D₁]; omega) _
        nlinarith [Nat.mul_le_mul_left (p.2.length + 1) (h1.trans h2)]
  obtain ⟨dc, hcoll⟩ := computableInO_collSorted
  let D := D₁ + dc
  have hmain' : ComputableInO
      (fun p : ℕ × List ℤ => collSorted (radixSortBy id p.1.size (p.2.map (intRemNat p.1))))
      encIn encNat
      (fun p => (p.2.length + 1) * collScale p ^ D)
      (fun p => (p.2.length + 1) * collScale p ^ D) := by
    refine (hcoll.comp hsort').weaken ?_ ?_
    all_goals
      refine BigOLe.add ?_ ?_
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (by dsimp only [D]; omega))
      · refine BigOLe.of_le_linear (2 ^ dc) 0 fun p => ?_
        have hrem_sz : listMax Nat.size (radixSortBy id p.1.size (p.2.map (intRemNat p.1))) ≤
            p.1.size := by
          refine listMax_le fun r hr => ?_
          rw [mem_radixSortBy] at hr
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
          exact Nat.size_le_size (intRemNat_le p.1 x)
        have hbase : listMax Nat.size (radixSortBy id p.1.size (p.2.map (intRemNat p.1))) +
            (radixSortBy id p.1.size (p.2.map (intRemNat p.1))).length.size + 1 ≤
            2 * collScale p := by
          rw [length_radixSortBy, List.length_map]
          dsimp only [collScale]; omega
        have hpow : (listMax Nat.size (radixSortBy id p.1.size (p.2.map (intRemNat p.1))) +
            (radixSortBy id p.1.size (p.2.map (intRemNat p.1))).length.size + 1) ^ dc ≤
            2 ^ dc * collScale p ^ D :=
          calc _ ≤ (2 * collScale p) ^ dc := Nat.pow_le_pow_left hbase dc
            _ = 2 ^ dc * collScale p ^ dc := Nat.mul_pow 2 _ dc
            _ ≤ 2 ^ dc * collScale p ^ D := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right (by dsimp only [collScale]; omega) (by dsimp only [D]; omega))
        have hmul : (p.2.length + 1) *
            (listMax Nat.size (radixSortBy id p.1.size (p.2.map (intRemNat p.1))) +
              (radixSortBy id p.1.size (p.2.map (intRemNat p.1))).length.size + 1) ^ dc ≤
            2 ^ dc * ((p.2.length + 1) * collScale p ^ D) :=
          (Nat.mul_le_mul_left (p.2.length + 1) hpow).trans_eq (by ring)
        change ((radixSortBy id p.1.size (p.2.map (intRemNat p.1))).length + 1) * _ ≤
          2 ^ dc * ((p.2.length + 1) * collScale p ^ D) + 0
        rw [length_radixSortBy, List.length_map] at hmul
        rw [length_radixSortBy, List.length_map, add_zero]
        exact hmul
  have hcond : ComputableInO (fun p : ℕ × List ℤ => decide (p.1 = 0)) encIn encBool
      (fun p => (encIn p).length) (fun p => (encIn p).length) :=
    (ComputableInO.fst encNat (encList encIntBin)).natIsZero'
  have hzero : ComputableInO (fun _ : ℕ × List ℤ => (0 : ℕ)) encIn encNat
      (fun p => (encIn p).length) (fun _ => 0) := ComputableInO.constZero 0
  have hite := (hcond.iteDecide hzero hmain').of_enc_eq (g := fun p => collList p.1 p.2)
    fun p => congrArg encNat (by unfold collList; split_ifs <;> rfl)
  refine ⟨D, hite.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear 16 0 fun p => ?_
    have hin := hlenIn_le p
    have hS : collScale p ≤ collScale p ^ D := Nat.le_self_pow (by dsimp only [D, D₁]; omega) _
    have hin' : (encIn p).length ≤ 6 * ((p.2.length + 1) * collScale p ^ D) :=
      hin.trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS])
    split_ifs <;> omega

private theorem foldl_succ_eq_add_length {α : Type} (l : List α) (k : ℕ) :
    l.foldl (fun s _ => s + 1) k = k + l.length := by
  induction l generalizing k with
  | nil => simp
  | cons _ xs ih =>
    rw [List.foldl_cons, ih, List.length_cons]
    omega

/-- `List.length` into `encNat` runs in linear scan time plus logarithmic counter work. -/
theorem computableInO_listLengthNat {α : Type} (encA : α ↪ List Bool) :
    ∃ d, ComputableInO (List.length : List α → ℕ) (encList encA) encNat
      (fun l => (encList encA l).length +
        (l.length + 1) * (listMax (fun a => (encA a).length) l + l.length.size + 4) ^ d)
      (fun l => (encList encA l).length +
        (listMax (fun a => (encA a).length) l + l.length.size + 4) ^ d) := by
  have hnext : ComputableInPolyTime (fun p : ℕ × α => p.1 + 1)
      (encPair encNat encA) encNat := by fun_prop
  let lMax : ℕ × List α → ℕ :=
    fun p => (encNat p.1).length + listMax (fun a => (encA a).length) p.2 + p.2.length.size + 3
  obtain ⟨df, hfold⟩ := computableInO_streamFold (lMax := lMax)
    Prod.fst Prod.snd (fun _ => rfl) hnext
    (fun p j _ => by
      simp only [streamState, foldl_succ_eq_add_length, length_encNat]
      have hlen : p.1 + (p.2.take j).length ≤ p.1 + p.2.length :=
        Nat.add_le_add_left (List.length_take_le' j p.2) p.1
      have hsz := (Nat.size_le_size hlen).trans (Nat.size_add_le p.1 p.2.length)
      dsimp only [lMax]
      rw [length_encNat]
      omega)
    (fun p j hj => by
      have := le_listMax (f := fun a => (encA a).length) (List.getElem_mem hj)
      dsimp only [lMax]
      omega)
  have hinit : ComputableInO (fun l : List α => (0, l))
      (encList encA) (encPair encNat (encList encA))
      (fun l => (encList encA l).length) (fun l => (encList encA l).length) :=
    ((ComputableInO.constZero 0).prod
      (ComputableInO.of_eq fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)
  have hcomp := (hfold.comp hinit).of_enc_eq (g := List.length) fun l =>
    congrArg encNat (by dsimp only [Function.comp_apply]; rw [foldl_succ_eq_add_length, zero_add])
  refine ⟨df, hcomp.weaken ?_ ?_⟩
  · refine BigOLe.of_le_linear 4 0 fun l => ?_
    have h0 : (encNat 0).length = 0 := by rw [length_encNat]; rfl
    have hpair : (encPair encNat (encList encA) (0, l)).length = (encList encA l).length + 1 := by
      rw [length_encPair, h0]; dsimp only; omega
    have hlmax : lMax (0, l) + 1 = listMax (fun a => (encA a).length) l + l.length.size + 4 := by
      dsimp only [lMax]; rw [h0]; omega
    change (encList encA l).length +
      ((encPair encNat (encList encA) (0, l)).length +
        (l.length + 1) * (lMax (0, l) + 1) ^ df) ≤ _
    rw [hpair, hlmax]
    have h1 : 1 ≤ (l.length + 1) *
        (listMax (fun a => (encA a).length) l + l.length.size + 4) ^ df :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (by omega))
    omega
  · refine BigOLe.of_le fun l => ?_
    have h0 : (encNat 0).length = 0 := by rw [length_encNat]; rfl
    have hlmax : lMax (0, l) + 1 = listMax (fun a => (encA a).length) l + l.length.size + 4 := by
      dsimp only [lMax]; rw [h0]; omega
    change (encList encA l).length + (lMax (0, l) + 1) ^ df ≤ _
    rw [hlmax]

end RemainderAndCollisions

end CslibFrontier.Complexity
