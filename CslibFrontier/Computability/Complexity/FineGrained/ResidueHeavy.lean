/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.ResidueCollisions
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith

/-!
# Radix-Sort Extraction of Heavy Residue Elements on Multi-Tape Turing Machines

This module constructs a deterministic multi-tape Turing machine algorithm with explicit
`ComputableInO` bounds for extracting duplicate-free integer lists of residue-colliding elements
modulo `M`, matching `ChanHe.heavy` in Chan and He's 3SUM-to-Convolution-3SUM reduction
.

## Main definitions

* `CslibFrontier.Complexity.heavyList`: extracts the elements of `L : List ℤ` sharing their
  canonical
  residue modulo `M` with at least one other element of `L`.
* `CslibFrontier.Complexity.heavyScale`: bit-scale parameter for `heavyList`.

## Main results

* `CslibFrontier.Complexity.heavyList_zero`,
  `CslibFrontier.Complexity.heavyList_nil`: `@[simp]` base-case
  identities.
* `CslibFrontier.Complexity.heavyList_nodup`, `CslibFrontier.Complexity.length_heavyList_le`,
  `CslibFrontier.Complexity.mem_heavyList_sub`: duplicate-freeness, length bound, and subset
  membership.
* `CslibFrontier.Complexity.heavyList_toFinset`: exact finite-set agreement with `ChanHe.heavy`.
* `CslibFrontier.Complexity.heavyScale_le`: componentwise upper bound on `heavyScale`.
* `CslibFrontier.Complexity.computableInO_heavyList`: quasi-linear Turing machine time and space
  bound
  `O((L.length + 1) * heavyScale (M, L) ^ d)`.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Algorithms.ThreeSum.ChanHe

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

private theorem size_le_self (k : ℕ) : k.size ≤ k :=
  Nat.size_le.mpr k.lt_two_pow_self

private theorem head?_dropWhile_not {α : Type*} (p : α → Bool) :
    ∀ (l : List α) {b : α}, (l.dropWhile p).head? = some b → ¬ p b = true
  | [], _, h => by simp at h
  | a :: as, b, h => by
    rw [List.dropWhile_cons] at h
    split_ifs at h with hp
    · exact head?_dropWhile_not p as h
    · simp only [List.head?_cons, Option.some.injEq] at h
      rwa [← h]

attribute [local irreducible] encNat encIntBin encUnary

private abbrev HeavyState := Option (ℕ × ℤ) × Bool

private def encHeavyState : HeavyState ↪ List Bool :=
  encPair (encOption (encPair encNat encIntBin)) encBool

private def heavyNext (p : HeavyState × (ℕ × ℤ)) : HeavyState :=
  if p.1.1.isSome then
    if decide (p.2.1 = (p.1.1.getD (0, 0)).1) then (some p.2, true)
    else (some p.2, false)
  else (some p.2, false)

private def heavyEmit (p : HeavyState × (ℕ × ℤ)) : List ℤ :=
  if p.1.1.isSome then
    if decide (p.2.1 = (p.1.1.getD (0, 0)).1) then
      if p.1.2 then [p.2.2] else [(p.1.1.getD (0, 0)).2, p.2.2]
    else []
  else []

private def heavySorted (R : List (ℕ × ℤ)) : List ℤ :=
  streamList heavyNext heavyEmit (none, false) R

/-- Extracts the elements of `L` sharing their residue modulo `M` with another element of `L`. -/
def heavyList (M : ℕ) (L : List ℤ) : List ℤ :=
  if M = 0 then []
  else heavySorted (radixSortBy Prod.fst M.size (L.map fun x => (intRemNat M x, x)))

@[simp]
theorem heavyList_zero (L : List ℤ) : heavyList 0 L = [] := by
  unfold heavyList; rfl

@[simp]
theorem heavyList_nil (M : ℕ) : heavyList M [] = [] := by
  unfold heavyList heavySorted
  split_ifs with hM
  · rfl
  · have h : radixSortBy Prod.fst M.size ([] : List (ℕ × ℤ)) = [] := by
      simpa using radixSortBy_perm Prod.fst M.size ([] : List (ℕ × ℤ))
    rw [List.map_nil, h, streamList_nil]

private theorem streamList_heavy_sublist (R : List (ℕ × ℤ)) (st : HeavyState) :
    (streamList heavyNext heavyEmit st R).Sublist
      (match st with
        | (some q, false) => q.2 :: R.map Prod.snd
        | _ => R.map Prod.snd) := by
  induction R generalizing st with
  | nil => exact List.nil_sublist _
  | cons a rs ih =>
    rcases st with ⟨_ | q, _ | _⟩
    · simp only [streamList_cons, heavyEmit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        List.nil_append, heavyNext, List.map_cons]
      exact ih (some a, false)
    · simp only [streamList_cons, heavyEmit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        List.nil_append, heavyNext, List.map_cons]
      exact ih (some a, false)
    · by_cases h : a.1 = q.1
      · simp only [streamList_cons, heavyEmit, Option.isSome_some, Option.getD_some, h,
          decide_true, ↓reduceIte, Bool.false_eq_true, heavyNext, List.map_cons, List.cons_append,
          List.nil_append]
        exact List.Sublist.cons_cons q.2 (List.Sublist.cons_cons a.2 (ih (some a, true)))
      · simp only [streamList_cons, heavyEmit, Option.isSome_some, Option.getD_some, h,
          decide_false, Bool.false_eq_true, ↓reduceIte, List.nil_append, heavyNext, List.map_cons]
        exact (ih (some a, false)).trans (List.sublist_cons_self _ _)
    · by_cases h : a.1 = q.1
      · simp only [streamList_cons, heavyEmit, Option.isSome_some, Option.getD_some, h,
          decide_true, ↓reduceIte, heavyNext, List.map_cons, List.cons_append, List.nil_append]
        exact List.Sublist.cons_cons a.2 (ih (some a, true))
      · simp only [streamList_cons, heavyEmit, Option.isSome_some, Option.getD_some, h,
          decide_false, Bool.false_eq_true, ↓reduceIte, List.nil_append, heavyNext, List.map_cons]
        exact ih (some a, false)

private theorem heavySorted_sublist (R : List (ℕ × ℤ)) :
    (heavySorted R).Sublist (R.map Prod.snd) :=
  streamList_heavy_sublist R (none, false)

private theorem map_snd_radix_perm (M : ℕ) (L : List ℤ) :
    ((radixSortBy Prod.fst M.size (L.map fun x => (intRemNat M x, x))).map Prod.snd).Perm L := by
  have hp := (radixSortBy_perm Prod.fst M.size (L.map fun x => (intRemNat M x, x))).map Prod.snd
  simpa [Function.comp_def] using hp

theorem heavyList_nodup {M : ℕ} {L : List ℤ} (hL : L.Nodup) : (heavyList M L).Nodup := by
  unfold heavyList
  split_ifs with hM
  · exact List.nodup_nil
  · exact (heavySorted_sublist _).nodup ((map_snd_radix_perm M L).nodup_iff.mpr hL)

theorem length_heavyList_le (M : ℕ) (L : List ℤ) : (heavyList M L).length ≤ L.length := by
  unfold heavyList
  split_ifs with hM
  · simp
  · exact (heavySorted_sublist _).length_le.trans (map_snd_radix_perm M L).length_eq.le

theorem mem_heavyList_sub {M : ℕ} {L : List ℤ} {z : ℤ} (hz : z ∈ heavyList M L) : z ∈ L := by
  unfold heavyList at hz
  split_ifs at hz with hM
  · simp at hz
  · exact (map_snd_radix_perm M L).mem_iff.mp ((heavySorted_sublist _).subset hz)

private theorem streamList_heavy_reset {R : List (ℕ × ℤ)} {q : ℕ × ℤ} (b : Bool)
    (h : ∀ a ∈ R.head?, a.1 ≠ q.1) :
    streamList heavyNext heavyEmit (some q, b) R = heavySorted R := by
  cases R with
  | nil => rfl
  | cons a rs =>
    have hne : a.1 ≠ q.1 := h a rfl
    simp [heavySorted, streamList_cons, heavyEmit, heavyNext, hne]

private theorem streamList_heavy_run {same rest : List (ℕ × ℤ)} {k : ℕ}
    (hsame : ∀ u ∈ same, u.1 = k) (hrest : ∀ b ∈ rest.head?, b.1 ≠ k) :
    ∀ {q : ℕ × ℤ}, q.1 = k →
      streamList heavyNext heavyEmit (some q, true) (same ++ rest) =
        same.map Prod.snd ++ heavySorted rest := by
  induction same with
  | nil =>
    intro q hq
    simp only [List.nil_append, List.map_nil]
    exact streamList_heavy_reset true fun b hb => by rw [hq]; exact hrest b hb
  | cons u us ih =>
    intro q hq
    have hu : u.1 = k := hsame u (List.mem_cons_self ..)
    have hus : ∀ v ∈ us, v.1 = k := fun v hv => hsame v (List.mem_cons_of_mem _ hv)
    have huq : u.1 = q.1 := hu.trans hq.symm
    simp only [List.cons_append, streamList_cons, heavyEmit, Option.isSome_some, Option.getD_some,
      huq, decide_true, ↓reduceIte, heavyNext, List.map_cons, List.nil_append]
    rw [ih hus hu]

private theorem mem_heavySorted_iff {R : List (ℕ × ℤ)} (hsort : R.Pairwise fun a b => a.1 ≤ b.1)
    (hnd : (R.map Prod.snd).Nodup) (z : ℤ) :
    z ∈ heavySorted R ↔ ∃ r, (r, z) ∈ R ∧ ∃ y, y ≠ z ∧ (r, y) ∈ R := by
  suffices ∀ n (R : List (ℕ × ℤ)), R.length ≤ n →
      R.Pairwise (fun a b => a.1 ≤ b.1) → (R.map Prod.snd).Nodup →
      (z ∈ heavySorted R ↔ ∃ r, (r, z) ∈ R ∧ ∃ y, y ≠ z ∧ (r, y) ∈ R) from
    this R.length R le_rfl hsort hnd
  intro n
  induction n with
  | zero =>
    intro R hlen _ _
    cases R with
    | nil => simp [heavySorted]
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro R hlen hsortR hndR
    rcases R with _ | ⟨a, rs⟩
    · simp [heavySorted]
    · let pred : ℕ × ℤ → Bool := fun u => decide (u.1 = a.1)
      let same := rs.takeWhile pred
      let rest := rs.dropWhile pred
      have hrs_eq : same ++ rest = rs := List.takeWhile_append_dropWhile
      have hlen_rest : rest.length ≤ n := by
        have := congrArg List.length hrs_eq
        rw [List.length_append] at this
        simp only [List.length_cons] at hlen
        omega
      have hsame_key : ∀ u ∈ same, u.1 = a.1 := fun u hu =>
        of_decide_eq_true (List.mem_takeWhile_imp (p := pred) hu)
      have hsort_cons := List.pairwise_cons.mp hsortR
      have hsort_rest : rest.Pairwise (fun u v => u.1 ≤ v.1) := by
        rw [← hrs_eq] at hsort_cons
        exact (List.pairwise_append.mp hsort_cons.2).2.1
      rw [List.map_cons] at hndR
      have hnd_cons := List.nodup_cons.mp hndR
      have hnd_rest : (rest.map Prod.snd).Nodup := by
        have h := hnd_cons.2
        rw [← hrs_eq, List.map_append] at h
        exact (List.nodup_append.mp h).2.1
      have hrest_gt : ∀ w ∈ rest, a.1 < w.1 := by
        cases hdw : rest with
        | nil => simp
        | cons b bs =>
          have hb_not : ¬ pred b = true := by
            have hd : (rs.dropWhile pred).head? = some b := by change rest.head? = _; rw [hdw]; rfl
            exact head?_dropWhile_not pred rs hd
          have hb_ne : b.1 ≠ a.1 := by simpa [pred] using hb_not
          have hb_mem : b ∈ rs := by
            rw [← hrs_eq, hdw]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          have ha_lt_b : a.1 < b.1 := lt_of_le_of_ne (hsort_cons.1 b hb_mem) hb_ne.symm
          have hbs_ge : ∀ w ∈ bs, b.1 ≤ w.1 := by
            rw [hdw] at hsort_rest
            exact (List.pairwise_cons.mp hsort_rest).1
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw_bs
          · exact ha_lt_b
          · exact lt_of_lt_of_le ha_lt_b (hbs_ge w hw_bs)
      have hrest_head : ∀ b ∈ rest.head?, b.1 ≠ a.1 := by
        cases hdw : rest with
        | nil => simp
        | cons b bs =>
          intro x hx
          cases hx
          exact (hrest_gt b (by rw [hdw]; exact List.mem_cons_self ..)).ne'
      have ih_rest := ih rest hlen_rest hsort_rest hnd_rest
      rw [← hrs_eq]
      rcases hsame_cases : same with _ | ⟨u, us⟩
      · simp only [List.nil_append]
        have hhs : heavySorted (a :: rest) = heavySorted rest := by
          unfold heavySorted
          rw [streamList_cons]
          simp only [heavyEmit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            List.nil_append, heavyNext]
          exact streamList_heavy_reset false hrest_head
        rw [hhs, ih_rest]
        constructor
        · rintro ⟨r, hrz, y, hyz, hry⟩
          exact ⟨r, List.mem_cons_of_mem _ hrz, y, hyz, List.mem_cons_of_mem _ hry⟩
        · rintro ⟨r, hrz, y, hyz, hry⟩
          rcases List.mem_cons.mp hrz with hza | hrz_rest
          · exfalso
            have hr_eq : r = a.1 := (Prod.mk.inj hza).1
            rcases List.mem_cons.mp hry with hya | hry_rest
            · exact hyz ((Prod.mk.inj hya).2.trans (Prod.mk.inj hza).2.symm)
            · exact (hrest_gt (r, y) hry_rest).ne' hr_eq
          · rcases List.mem_cons.mp hry with hya | hry_rest
            · exfalso
              have hr_eq : r = a.1 := (Prod.mk.inj hya).1
              exact (hrest_gt (r, z) hrz_rest).ne' hr_eq
            · exact ⟨r, hrz_rest, y, hyz, hry_rest⟩
      · have hu_key : u.1 = a.1 := hsame_key u (by rw [hsame_cases]; exact List.mem_cons_self ..)
        have hus_key : ∀ v ∈ us, v.1 = a.1 := fun v hv =>
          hsame_key v (by rw [hsame_cases]; exact List.mem_cons_of_mem _ hv)
        have hhs : heavySorted (a :: (u :: us ++ rest)) =
            (a :: u :: us).map Prod.snd ++ heavySorted rest := by
          unfold heavySorted
          rw [List.cons_append, streamList_cons, streamList_cons]
          simp only [heavyEmit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            List.nil_append, heavyNext, Option.isSome_some, Option.getD_some, hu_key, decide_true,
            List.cons_append, List.map_cons]
          rw [streamList_heavy_run hus_key hrest_head hu_key]; rfl
        rw [hhs, List.mem_append, ih_rest]
        have hau_ne : a.2 ≠ u.2 := by
          intro heq
          apply hnd_cons.1
          rw [← hrs_eq, hsame_cases, List.map_append, List.map_cons, heq]
          exact List.mem_append_left _ (List.mem_cons_self ..)
        constructor
        · rintro (hz_run | ⟨r, hrz, y, hyz, hry⟩)
          · obtain ⟨v, hv_mem, rfl⟩ := List.mem_map.mp hz_run
            have hv_key : v.1 = a.1 := by
              rcases List.mem_cons.mp hv_mem with rfl | hvu
              · rfl
              · rcases List.mem_cons.mp hvu with rfl | hvus
                · exact hu_key
                · exact hus_key v hvus
            have hv_in : (a.1, v.2) ∈ a :: (u :: us ++ rest) := by
              have hveq : (a.1, v.2) = v := Prod.ext hv_key.symm rfl
              rw [hveq]
              rcases List.mem_cons.mp hv_mem with rfl | hvu
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (List.mem_append_left _ hvu)
            by_cases hva : v.2 = a.2
            · refine ⟨a.1, hv_in, u.2, fun h => hau_ne (hva.symm.trans h.symm), ?_⟩
              have hueq : (a.1, u.2) = u := Prod.ext hu_key.symm rfl
              rw [hueq]
              exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_self ..))
            · refine ⟨a.1, hv_in, a.2, Ne.symm hva, ?_⟩
              have haeq : (a.1, a.2) = a := Prod.ext rfl rfl
              rw [haeq]
              exact List.mem_cons_self ..
          · exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hrz),
              y, hyz, List.mem_cons_of_mem _ (List.mem_append_right _ hry)⟩
        · rintro ⟨r, hrz, y, hyz, hry⟩
          have split_mem : ∀ {p : ℕ × ℤ}, p ∈ a :: (u :: us ++ rest) →
              (p ∈ a :: u :: us ∧ p.1 = a.1) ∨ (p ∈ rest ∧ a.1 < p.1) := by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact Or.inl ⟨List.mem_cons_self .., rfl⟩
            · rcases List.mem_append.mp hp' with hp_run | hp_rest
              · have hk : p.1 = a.1 := by
                  rcases List.mem_cons.mp hp_run with rfl | hpus
                  · exact hu_key
                  · exact hus_key p hpus
                exact Or.inl ⟨List.mem_cons_of_mem _ hp_run, hk⟩
              · exact Or.inr ⟨hp_rest, hrest_gt p hp_rest⟩
          rcases split_mem hrz with ⟨hz_run, hrz_k⟩ | ⟨hz_rest, hrz_gt⟩
          · exact Or.inl (List.mem_map_of_mem (f := Prod.snd) hz_run)
          · rcases split_mem hry with ⟨_, hry_k⟩ | ⟨hy_rest, _⟩
            · exact absurd hry_k hrz_gt.ne'
            · exact Or.inr ⟨r, hz_rest, y, hyz, hy_rest⟩

/-- For duplicate-free `L`, `(heavyList M L).toFinset` equals `ChanHe.heavy L.toFinset M`. -/
theorem heavyList_toFinset {M : ℕ} {L : List ℤ} (hL : L.Nodup) :
    (heavyList M L).toFinset = heavy L.toFinset M := by
  ext z
  rw [List.mem_toFinset, heavy, Finset.mem_filter, List.mem_toFinset]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [heavyList_zero, List.not_mem_nil, false_iff, not_and]
    rintro _ ⟨y, _, hyz, hzy⟩
    rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at hzy
    exact hyz hzy.symm
  · unfold heavyList
    simp only [hM.ne', ↓reduceIte]
    let R := radixSortBy Prod.fst M.size (L.map fun x => (intRemNat M x, x))
    have hperm := radixSortBy_perm Prod.fst M.size (L.map fun x => (intRemNat M x, x))
    have hsort : R.Pairwise (fun a b => a.1 ≤ b.1) := by
      refine pairwise_radixSortBy Prod.fst M.size fun p hp => ?_
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      exact (intRemNat_lt hM x).trans (Nat.lt_size_self M)
    have hnd : (R.map Prod.snd).Nodup := (map_snd_radix_perm M L).nodup_iff.mpr hL
    rw [mem_heavySorted_iff hsort hnd]
    constructor
    · rintro ⟨r, hrz, y, hyz, hry⟩
      obtain ⟨z', hz'L, hz'eq⟩ := List.mem_map.mp (hperm.mem_iff.mp hrz)
      obtain ⟨y', hy'L, hy'eq⟩ := List.mem_map.mp (hperm.mem_iff.mp hry)
      have hz_eq : z' = z := (Prod.mk.inj hz'eq).2
      have hy_eq : y' = y := (Prod.mk.inj hy'eq).2
      subst hz_eq hy_eq
      have hrem : intRemNat M z' = intRemNat M y' :=
        (Prod.mk.inj hz'eq).1.trans (Prod.mk.inj hy'eq).1.symm
      exact ⟨hz'L, y', List.mem_toFinset.mpr hy'L, hyz, (intRemNat_eq_iff_dvd hM z' y').mp hrem⟩
    · rintro ⟨hzL, y, hyL, hyz, hdvd⟩
      have hrem := (intRemNat_eq_iff_dvd hM z y).mpr hdvd
      refine ⟨intRemNat M z, hperm.mem_iff.mpr (List.mem_map_of_mem hzL), y, hyz, ?_⟩
      rw [hrem]
      exact hperm.mem_iff.mpr (List.mem_map_of_mem (List.mem_toFinset.mp hyL))

/-- Bit-scale parameter for `heavyList M L`. -/
def heavyScale (p : ℕ × List ℤ) : ℕ :=
  p.1.size + listMax (fun x => (encIntBin x).length) p.2 + p.2.length.size + 1

/-- Componentwise upper bound on `heavyScale`. -/
theorem heavyScale_le {p : ℕ × List ℤ} {bM bL blen : ℕ}
    (hM : p.1.size ≤ bM) (hL : listMax (fun x => (encIntBin x).length) p.2 ≤ bL)
    (hlen : p.2.length.size ≤ blen) :
    heavyScale p ≤ bM + bL + blen + 1 := by
  dsimp only [heavyScale]; omega

private theorem computableInPolyTime_heavyNext :
    ComputableInPolyTime heavyNext
      (encPair encHeavyState (encPair encNat encIntBin)) encHeavyState := by
  unfold heavyNext encHeavyState
  fun_prop

private theorem computableInPolyTime_heavyEmit :
    ComputableInPolyTime heavyEmit
      (encPair encHeavyState (encPair encNat encIntBin)) (encList encIntBin) := by
  unfold heavyEmit encHeavyState
  fun_prop

private theorem computableInPolyTime_remPair :
    ComputableInPolyTime (fun q : ℕ × ℤ => (intRemNat q.1 q.2, q.2))
      (encPair encNat encIntBin) (encPair encNat encIntBin) := by fun_prop

private theorem computableInO_heavySorted :
    ∃ d, ComputableInO heavySorted (encList (encPair encNat encIntBin)) (encList encIntBin)
      (fun R => (R.length + 1) *
        (listMax (fun a => (encPair encNat encIntBin a).length) R + 4) ^ d)
      (fun R => (R.length + 1) *
        (listMax (fun a => (encPair encNat encIntBin a).length) R + 4) ^ d) := by
  let encItem := encPair encNat encIntBin
  let lMax : HeavyState × List (ℕ × ℤ) → ℕ :=
    fun p => (encHeavyState p.1).length + 2 * listMax (fun a => (encItem a).length) p.2 + 4
  have hst_mem : ∀ (t : List (ℕ × ℤ)) (st : HeavyState),
      let r := t.foldl (fun s a => heavyNext (s, a)) st
      r.1 = st.1 ∨ ∃ a ∈ t, r.1 = some a := by
    intro t
    induction t with
    | nil => intro st; exact Or.inl rfl
    | cons a ts ih =>
      intro st
      dsimp only
      rw [List.foldl_cons]
      have hnext : (heavyNext (st, a)).1 = some a := by
        unfold heavyNext; split_ifs <;> rfl
      rcases ih (heavyNext (st, a)) with h0 | ⟨b, hb, hsome⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h0.trans hnext⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hsome⟩
  have hblen : ∀ b : Bool, (encBool b).length = 1 := by rintro (_ | _) <;> rfl
  obtain ⟨dh, hstr⟩ := computableInO_streamList (lMax := lMax)
    Prod.fst Prod.snd (fun _ => rfl) computableInPolyTime_heavyNext computableInPolyTime_heavyEmit
    (fun _ => rfl)
    (fun p j _ => by
      simp only [streamState]
      rcases hst_mem (p.2.take j) p.1 with h0 | ⟨a, ha, hsome⟩
      · simp only [encHeavyState, length_encPair, hblen]
        rw [h0]
        dsimp only [lMax, encHeavyState]
        rw [length_encPair, hblen]
        omega
      · have ha_le := le_listMax (f := fun x => (encItem x).length) (List.mem_of_mem_take ha)
        simp only [encHeavyState, length_encPair, hblen]
        rw [hsome, encOption_some, List.length_cons]
        dsimp only [lMax, encItem] at *
        omega)
    (fun p j hj => by
      have := le_listMax (f := fun x => (encItem x).length) (List.getElem_mem hj)
      dsimp only [lMax, encItem] at *; omega)
  have hinit : ComputableInO (fun R : List (ℕ × ℤ) => ((none, false), R))
      (encList encItem) (encPair encHeavyState (encList encItem))
      (fun R => (encList encItem R).length) (fun R => (encList encItem R).length) :=
    ((ComputableInO.constZero (none, false)).prod (ComputableInO.of_eq fun _ => rfl)).mono 4
      (fun _ => by omega) (fun _ => by omega)
  have hst0 : (encHeavyState (none, false)).length = 2 := by
    simp [encHeavyState]
  have hcomp := (hstr.comp hinit).of_enc_eq (g := heavySorted) fun _ => rfl
  refine ⟨dh + 1, hcomp.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (16 + 4 ^ dh) 0 fun R => ?_
    let S := listMax (fun a => (encItem a).length) R + 4
    have hS1 : 1 ≤ S := by dsimp only [S]; omega
    have hSD : S ≤ S ^ (dh + 1) := Nat.le_self_pow (by omega) S
    have hlenR : (encList encItem R).length ≤ 3 * ((R.length + 1) * S ^ (dh + 1)) := by
      have h1 := length_encList_le_mul encItem R
        (b := listMax (fun a => (encItem a).length) R)
        fun a ha => le_listMax (f := fun x => (encItem x).length) ha
      have h2 : 2 * listMax (fun a => (encItem a).length) R + 1 ≤ 3 * S := by
        dsimp only [S]; omega
      calc _ ≤ R.length * (3 * S) := h1.trans (Nat.mul_le_mul_left _ h2)
        _ ≤ 3 * ((R.length + 1) * S ^ (dh + 1)) := by
          nlinarith [Nat.mul_le_mul (Nat.le_succ R.length) hSD]
    have hpair : (encPair encHeavyState (encList encItem) ((none, false), R)).length ≤
        8 * ((R.length + 1) * S ^ (dh + 1)) := by
      rw [length_encPair, hst0]
      dsimp only
      have h1 : 1 ≤ (R.length + 1) * S ^ (dh + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ hS1)
      omega
    have hlmax : lMax ((none, false), R) + 1 ≤ 4 * S := by
      dsimp only [lMax, S]; rw [hst0]; omega
    have hpow : (lMax ((none, false), R) + 1) ^ dh ≤ 4 ^ dh * S ^ (dh + 1) :=
      calc _ ≤ (4 * S) ^ dh := Nat.pow_le_pow_left hlmax dh
        _ = 4 ^ dh * S ^ dh := Nat.mul_pow 4 S dh
        _ ≤ 4 ^ dh * S ^ (dh + 1) := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right hS1 (Nat.le_succ dh))
    have hmul : (R.length + 1) * (lMax ((none, false), R) + 1) ^ dh ≤
        4 ^ dh * ((R.length + 1) * S ^ (dh + 1)) :=
      (Nat.mul_le_mul_left (R.length + 1) hpow).trans_eq (Nat.mul_left_comm _ _ _)
    change (encList encItem R).length +
        ((encPair encHeavyState (encList encItem) ((none, false), R)).length +
          (R.length + 1) * (lMax ((none, false), R) + 1) ^ dh) ≤
      (16 + 4 ^ dh) * ((R.length + 1) * S ^ (dh + 1)) + 0
    rw [Nat.add_mul 16 (4 ^ dh)]
    omega

/-- `heavyList M L` runs in quasi-linear time `O((L.length + 1) * heavyScale (M, L) ^ d)`. -/
theorem computableInO_heavyList :
    ∃ d, ComputableInO (fun p : ℕ × List ℤ => heavyList p.1 p.2)
      (encPair encNat (encList encIntBin)) (encList encIntBin)
      (fun p => (p.2.length + 1) * heavyScale p ^ d)
      (fun p => (p.2.length + 1) * heavyScale p ^ d) := by
  let encIn := encPair encNat (encList encIntBin)
  let encItem := encPair encNat encIntBin
  obtain ⟨dm, hmap⟩ := computableInO_streamMapWith
    (f := fun q : ℕ × ℤ => (intRemNat q.1 q.2, q.2)) computableInPolyTime_remPair
    (lMax := heavyScale)
    (fun p => by rw [length_encNat]; dsimp only [heavyScale]; omega)
    (fun p j hj => by
      have := le_listMax (f := fun x => (encIntBin x).length) (List.getElem_mem hj)
      dsimp only [heavyScale]; omega)
  have hsizePt : ComputableInPolyTime Nat.size encNat encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_size
  obtain ⟨dsz, _, hsizeDeg⟩ := hsizePt.exists_degree
  have hlenIn_le (p : ℕ × List ℤ) : (encIn p).length ≤ 6 * ((p.2.length + 1) * heavyScale p) := by
    rw [length_encPair, length_encNat]
    have hL := length_encList_le_mul encIntBin p.2
      (b := listMax (fun x => (encIntBin x).length) p.2)
      fun x hx => le_listMax (f := fun x => (encIntBin x).length) hx
    have h2 : 2 * listMax (fun x => (encIntBin x).length) p.2 + 1 ≤ 3 * heavyScale p := by
      dsimp only [heavyScale]; omega
    have hL' : (encList encIntBin p.2).length ≤ 3 * (p.2.length * heavyScale p) :=
      (hL.trans (Nat.mul_le_mul_left _ h2)).trans_eq (Nat.mul_left_comm _ _ _)
    have hM : p.1.size ≤ heavyScale p := by dsimp only [heavyScale]; omega
    nlinarith
  have hb : ComputableInO (fun p : ℕ × List ℤ => p.1.size) encIn encNat
      (fun p => (p.2.length + 1) * heavyScale p ^ (dsz + 1))
      (fun p => (p.2.length + 1) * heavyScale p ^ (dsz + 1)) := by
    refine (hsizeDeg.inO.comp (ComputableInO.fst encNat (encList encIntBin))).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (6 + 2 ^ dsz) 0 fun p => ?_
      have hS0 : 1 ≤ heavyScale p := by dsimp only [heavyScale]; omega
      have hS1 : heavyScale p ≤ heavyScale p ^ (dsz + 1) := Nat.le_self_pow (by omega) _
      have hin : (encIn p).length ≤ 6 * ((p.2.length + 1) * heavyScale p ^ (dsz + 1)) :=
        (hlenIn_le p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS1])
      have hM : p.1.size + 1 ≤ 2 * heavyScale p := by dsimp only [heavyScale]; omega
      have hpow : (p.1.size + 1) ^ dsz ≤ 2 ^ dsz * ((p.2.length + 1) * heavyScale p ^ (dsz + 1)) :=
        calc _ ≤ (2 * heavyScale p) ^ dsz := Nat.pow_le_pow_left hM dsz
          _ = 2 ^ dsz * heavyScale p ^ dsz := Nat.mul_pow 2 _ dsz
          _ ≤ 2 ^ dsz * heavyScale p ^ (dsz + 1) := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS0 (Nat.le_succ dsz))
          _ ≤ 2 ^ dsz * ((p.2.length + 1) * heavyScale p ^ (dsz + 1)) :=
              Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      change (encIn p).length + ((encNat p.1).length + 1) ^ dsz ≤ _
      rw [length_encNat, Nat.add_mul 6 (2 ^ dsz)]
      omega
  have hmap' : ComputableInO (fun p : ℕ × List ℤ => p.2.map fun x => (intRemNat p.1 x, x))
      encIn (encList encItem)
      (fun p => (p.2.length + 1) * heavyScale p ^ (dm + 1))
      (fun p => (p.2.length + 1) * heavyScale p ^ (dm + 1)) := by
    refine hmap.weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (6 + 2 ^ dm) 0 fun p => ?_
      have hS0 : 1 ≤ heavyScale p := by dsimp only [heavyScale]; omega
      have hS1 : heavyScale p ≤ heavyScale p ^ (dm + 1) := Nat.le_self_pow (by omega) _
      have hin : (encIn p).length ≤ 6 * ((p.2.length + 1) * heavyScale p ^ (dm + 1)) :=
        (hlenIn_le p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS1])
      have hpow : (heavyScale p + 1) ^ dm ≤ 2 ^ dm * heavyScale p ^ (dm + 1) :=
        calc _ ≤ (2 * heavyScale p) ^ dm :=
              Nat.pow_le_pow_left (by dsimp only [heavyScale]; omega) dm
          _ = 2 ^ dm * heavyScale p ^ dm := Nat.mul_pow 2 _ dm
          _ ≤ 2 ^ dm * heavyScale p ^ (dm + 1) := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS0 (Nat.le_succ dm))
      have hmul : (p.2.length + 1) * (heavyScale p + 1) ^ dm ≤
          2 ^ dm * ((p.2.length + 1) * heavyScale p ^ (dm + 1)) :=
        (Nat.mul_le_mul_left (p.2.length + 1) hpow).trans_eq (Nat.mul_left_comm _ _ _)
      change (encIn p).length + (p.2.length + 1) * (heavyScale p + 1) ^ dm ≤ _
      rw [Nat.add_mul 6 (2 ^ dm)]
      omega
  have hkeyPt : ComputableInPolyTime (Prod.fst : ℕ × ℤ → ℕ) encItem encNat := by fun_prop
  obtain ⟨dr, hsort⟩ := computableInO_radixSortBy (key := Prod.fst) hkeyPt
    (lMax := fun p => 3 * heavyScale p) hb hmap'
    (fun p => by
      rw [length_encNat]
      have := size_le_self p.1.size
      dsimp only [heavyScale]; omega)
    (fun p a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [length_encPair, length_encNat]
      have hr := Nat.size_le_size (intRemNat_le p.1 x)
      have hx' := le_listMax (f := fun z => (encIntBin z).length) hx
      dsimp only [heavyScale]; omega)
  have hlen_rem (p : ℕ × List ℤ) :
      (encList encItem (p.2.map fun x => (intRemNat p.1 x, x))).length ≤
        7 * ((p.2.length + 1) * heavyScale p) := by
    have h1 := length_encList_le_mul encItem (p.2.map fun x => (intRemNat p.1 x, x))
      (b := 3 * heavyScale p) fun a ha => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [length_encPair, length_encNat]
        have := Nat.size_le_size (intRemNat_le p.1 x)
        have := le_listMax (f := fun z => (encIntBin z).length) hx
        dsimp only [heavyScale]; omega
    rw [List.length_map] at h1
    have hS0 : 1 ≤ heavyScale p := by dsimp only [heavyScale]; omega
    calc _ ≤ p.2.length * (7 * heavyScale p) := h1.trans (Nat.mul_le_mul_left _ (by omega))
      _ ≤ 7 * ((p.2.length + 1) * heavyScale p) := by nlinarith
  let D₁ := dsz + dm + dr + 4
  have hsort' : ComputableInO
      (fun p : ℕ × List ℤ =>
        radixSortBy Prod.fst p.1.size (p.2.map fun x => (intRemNat p.1 x, x)))
      encIn (encList encItem)
      (fun p => (p.2.length + 1) * heavyScale p ^ D₁)
      (fun p => (p.2.length + 1) * heavyScale p ^ D₁) := by
    refine hsort.weaken ?_ ?_
    · refine BigOLe.add (BigOLe.add ?_ ?_) ?_
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [heavyScale]; omega) (by dsimp only [D₁]; omega))
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [heavyScale]; omega) (by dsimp only [D₁]; omega))
      · refine BigOLe.of_le_linear (12 + 4 ^ dr) 0 fun p => ?_
        let S := heavyScale p
        have hS1 : 1 ≤ S := by dsimp only [S, heavyScale]; omega
        have hSD : S * S ^ (D₁ - 1) = S ^ D₁ := (pow_succ' S (D₁ - 1)).symm
        have hSpow : S ≤ S ^ (D₁ - 1) := Nat.le_self_pow (by dsimp only [D₁]; omega) S
        have ha : (encList encItem (p.2.map fun x => (intRemNat p.1 x, x))).length ≤
            7 * ((p.2.length + 1) * S ^ (D₁ - 1)) :=
          (hlen_rem p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hSpow])
        have hb' : ((p.2.map fun x => (intRemNat p.1 x, x)).length + 1) * (3 * S + 1) ^ dr ≤
            4 ^ dr * ((p.2.length + 1) * S ^ (D₁ - 1)) := by
          rw [List.length_map]
          have hpow : (3 * S + 1) ^ dr ≤ 4 ^ dr * S ^ (D₁ - 1) :=
            calc _ ≤ (4 * S) ^ dr := Nat.pow_le_pow_left (by omega) dr
              _ = 4 ^ dr * S ^ dr := Nat.mul_pow 4 S dr
              _ ≤ 4 ^ dr * S ^ (D₁ - 1) := Nat.mul_le_mul_left _
                  (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
          exact (Nat.mul_le_mul_left (p.2.length + 1) hpow).trans_eq (Nat.mul_left_comm _ _ _)
        have hc : ((encNat p.1.size).length + 1) ^ 2 ≤ 4 * ((p.2.length + 1) * S ^ (D₁ - 1)) := by
          rw [length_encNat]
          have h1 : p.1.size.size + 1 ≤ 2 * S := by
            have := size_le_self p.1.size; dsimp only [S, heavyScale]; omega
          have hsq : (p.1.size.size + 1) ^ 2 ≤ 4 * S ^ (D₁ - 1) :=
            calc _ ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left h1 2
              _ = 4 * S ^ 2 := Nat.mul_pow 2 S 2
              _ ≤ 4 * S ^ (D₁ - 1) := Nat.mul_le_mul_left 4
                  (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
          exact hsq.trans (by nlinarith [Nat.one_le_pow (D₁ - 1) S hS1])
        have hsum : (encList encItem (p.2.map fun x => (intRemNat p.1 x, x))).length +
            ((p.2.map fun x => (intRemNat p.1 x, x)).length + 1) * (3 * S + 1) ^ dr +
            ((encNat p.1.size).length + 1) ^ 2 ≤
            (12 + 4 ^ dr) * ((p.2.length + 1) * S ^ (D₁ - 1)) := by
          rw [Nat.add_mul 12 (4 ^ dr)]; omega
        have hbp1 : p.1.size + 1 ≤ S := by dsimp only [S, heavyScale]; omega
        calc (p.1.size + 1) * _ ≤ S * ((12 + 4 ^ dr) * ((p.2.length + 1) * S ^ (D₁ - 1))) :=
              Nat.mul_le_mul hbp1 hsum
          _ = (12 + 4 ^ dr) * ((p.2.length + 1) * (S * S ^ (D₁ - 1))) := by
              rw [Nat.mul_left_comm, ← Nat.mul_assoc ((p.2.length + 1)),
                Nat.mul_left_comm S (p.2.length + 1), Nat.mul_assoc]
          _ = (12 + 4 ^ dr) * ((p.2.length + 1) * S ^ D₁) + 0 := by rw [hSD, add_zero]
    · refine BigOLe.add (BigOLe.add (BigOLe.add (BigOLe.add ?_ ?_) ?_) ?_) ?_
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [heavyScale]; omega) (by dsimp only [D₁]; omega))
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [heavyScale]; omega) (by dsimp only [D₁]; omega))
      · refine BigOLe.of_le_linear 7 0 fun p => ?_
        have hS : heavyScale p ≤ heavyScale p ^ D₁ := Nat.le_self_pow (by dsimp only [D₁]; omega) _
        exact (hlen_rem p).trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS])
      · refine BigOLe.of_le_linear (4 ^ dr) 0 fun p => ?_
        rw [List.length_map]
        have hS1 : 1 ≤ heavyScale p := by dsimp only [heavyScale]; omega
        have hpow : (3 * heavyScale p + 1) ^ dr ≤ 4 ^ dr * heavyScale p ^ D₁ :=
          calc _ ≤ (4 * heavyScale p) ^ dr := Nat.pow_le_pow_left (by omega) dr
            _ = 4 ^ dr * heavyScale p ^ dr := Nat.mul_pow 4 _ dr
            _ ≤ 4 ^ dr * heavyScale p ^ D₁ := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
        exact ((Nat.mul_le_mul_left (p.2.length + 1) hpow).trans_eq
          (Nat.mul_left_comm _ _ _)).trans_eq (add_zero _).symm
      · refine BigOLe.of_le fun p => ?_
        rw [length_encNat]
        have h1 : p.1.size.size ≤ heavyScale p :=
          (size_le_self p.1.size).trans (by dsimp only [heavyScale]; omega)
        have h2 : heavyScale p ≤ heavyScale p ^ D₁ := Nat.le_self_pow (by dsimp only [D₁]; omega) _
        exact (h1.trans h2).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  obtain ⟨dh, hhs⟩ := computableInO_heavySorted
  let D := D₁ + dh + 2
  have hmain : ComputableInO
      (fun p : ℕ × List ℤ =>
        heavySorted (radixSortBy Prod.fst p.1.size (p.2.map fun x => (intRemNat p.1 x, x))))
      encIn (encList encIntBin)
      (fun p => (p.2.length + 1) * heavyScale p ^ D)
      (fun p => (p.2.length + 1) * heavyScale p ^ D) := by
    refine (hhs.comp hsort').weaken ?_ ?_
    all_goals
      refine BigOLe.add ?_ ?_
      · exact BigOLe.of_le fun p => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [heavyScale]; omega) (by dsimp only [D]; omega))
      · refine BigOLe.of_le_linear (8 ^ dh) 0 fun p => ?_
        let R := radixSortBy Prod.fst p.1.size (p.2.map fun x => (intRemNat p.1 x, x))
        have hlm : listMax (fun a => (encItem a).length) R ≤ 3 * heavyScale p := by
          refine listMax_le fun a ha => ?_
          rw [mem_radixSortBy] at ha
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
          rw [length_encPair, length_encNat]
          have := Nat.size_le_size (intRemNat_le p.1 x)
          have := le_listMax (f := fun z => (encIntBin z).length) hx
          dsimp only [heavyScale]; omega
        have hbase : listMax (fun a => (encItem a).length) R + 4 ≤ 8 * heavyScale p := by
          have : 1 ≤ heavyScale p := by dsimp only [heavyScale]; omega
          omega
        have hpow : (listMax (fun a => (encItem a).length) R + 4) ^ dh ≤
            8 ^ dh * heavyScale p ^ D :=
          calc _ ≤ (8 * heavyScale p) ^ dh := Nat.pow_le_pow_left hbase dh
            _ = 8 ^ dh * heavyScale p ^ dh := Nat.mul_pow 8 _ dh
            _ ≤ 8 ^ dh * heavyScale p ^ D := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right (by dsimp only [heavyScale]; omega)
                  (by dsimp only [D]; omega))
        have hmul : (p.2.length + 1) * (listMax (fun a => (encItem a).length) R + 4) ^ dh ≤
            8 ^ dh * ((p.2.length + 1) * heavyScale p ^ D) :=
          (Nat.mul_le_mul_left (p.2.length + 1) hpow).trans_eq (Nat.mul_left_comm _ _ _)
        change (R.length + 1) * (listMax (fun a => (encItem a).length) R + 4) ^ dh ≤
          8 ^ dh * ((p.2.length + 1) * heavyScale p ^ D) + 0
        rw [show R.length = p.2.length by
          dsimp only [R]; rw [length_radixSortBy, List.length_map], add_zero]
        exact hmul
  have hcond : ComputableInO (fun p : ℕ × List ℤ => decide (p.1 = 0)) encIn encBool
      (fun p => (encIn p).length) (fun p => (encIn p).length) :=
    (ComputableInO.fst encNat (encList encIntBin)).natIsZero'
  have hnil : ComputableInO (fun _ : ℕ × List ℤ => ([] : List ℤ)) encIn (encList encIntBin)
      (fun p => (encIn p).length) (fun _ => 0) := ComputableInO.constZero []
  have hite := (hcond.iteDecide hnil hmain).of_enc_eq (g := fun p => heavyList p.1 p.2)
    fun p => congrArg (encList encIntBin) (by unfold heavyList; split_ifs <;> rfl)
  refine ⟨D, hite.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear 16 0 fun p => ?_
    have hin := hlenIn_le p
    have hS : heavyScale p ≤ heavyScale p ^ D :=
      Nat.le_self_pow (by dsimp only [D, D₁]; omega) _
    have hin' : (encIn p).length ≤ 6 * ((p.2.length + 1) * heavyScale p ^ D) :=
      hin.trans (by nlinarith [Nat.mul_le_mul_left (p.2.length + 1) hS])
    split_ifs <;> omega

end CslibFrontier.Complexity
