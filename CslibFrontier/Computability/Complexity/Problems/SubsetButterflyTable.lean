/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bit-Reversed Subset Tables and Streaming Butterfly Carry Propagation

This module constructs least-significant-bit interleaved subset tables (`tabulateLSB`,
`setOfBits`) over finite ground sets `Fin q` together with a streaming bit-rotation carry
butterfly (`butterflyPass`) on deterministic multi-tape Turing machines. Across `q` single-pass
even/odd rotations for a Boolean mask `A_r`, the carry slot at every subset `T ⊆ Fin q` evaluates
to the previous dynamic-programming value at `T \ A_r` whenever `A_r ⊆ T` (and `none` otherwise),
avoiding random-access indexing on tapes and achieving linear overhead in the table size $2^q$.

## Main definitions

* `CslibFrontier.ParameterizedComplexity.SubsetDPCell`,
  `CslibFrontier.ParameterizedComplexity.encSubsetDPCell`,
  `CslibFrontier.ParameterizedComplexity.SubsetDPFlags`,
  `CslibFrontier.ParameterizedComplexity.encSubsetDPFlags`: cell and control-flag encodings for
  streaming subset dynamic programming.
* `CslibFrontier.ParameterizedComplexity.tabulateLSB`,
  `CslibFrontier.ParameterizedComplexity.setOfBits`: least-significant-bit interleaved subset table
  of
  length $2^q$ and characteristic-mask decoding into `Finset (Fin q)`.
* `CslibFrontier.ParameterizedComplexity.subsetDPPrefix`,
  `CslibFrontier.ParameterizedComplexity.subsetDPExpectedCarry`: exact prefix recurrences and
  intermediate carry invariants for maximum disjoint subset packing (`mode = true`) and minimum
  exact subset partition (`mode = false`).
* `CslibFrontier.ParameterizedComplexity.butterflyPass`: single bit-rotation carry pass splitting
  even
  and odd table cells and concatenating the resulting halves.

## Main results

* `CslibFrontier.ParameterizedComplexity.subsetDPPrefix_true_spec`,
  `CslibFrontier.ParameterizedComplexity.subsetDPPrefix_false_spec`: semantic characterization of
  `subsetDPPrefix` as maximum disjoint packing cardinality (`IsGreatest`) and minimum exact
  partition cardinality (`IsLeast`).
* `CslibFrontier.ParameterizedComplexity.butterflyPass_tabulateLSB_step`: exact rotated-table
  invariant
  across one pass of `butterflyPass`.
* `CslibFrontier.ParameterizedComplexity.computableInO_butterflyPass`,
  `CslibFrontier.ParameterizedComplexity.computableInO_lastSubsetCell`: linear-in-table-length
  `ComputableInO` bounds on multi-tape Turing machines via `streamFold`.
-/

public section

namespace CslibFrontier.ParameterizedComplexity

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Subset Cells, Interleaved Tabulation, and Rotated Carry Recurrence -/

/-- A subset dynamic-programming cell `(dp, carry)` storing the current stage optimum and the
propagating complement carry. -/
abbrev SubsetDPCell := Option ℕ × Option ℕ

/-- Framed multi-tape encoding of `SubsetDPCell`. -/
abbrev encSubsetDPCell : SubsetDPCell ↪ List Bool :=
  encPair (encOption encNat) (encOption encNat)

/-- Control flags `((mode, isLast), bit)` governing a single butterfly pass. -/
abbrev SubsetDPFlags := (Bool × Bool) × Bool

/-- Framed multi-tape encoding of `SubsetDPFlags`. -/
abbrev encSubsetDPFlags : SubsetDPFlags ↪ List Bool :=
  encPair (encPair encBool encBool) encBool

private def combineCell (mode : Bool) (cur carry : Option ℕ) : Option ℕ :=
  if mode then
    match cur, carry with
    | some a, some b => some (max a (b + 1))
    | a, _ => a
  else
    match carry with
    | none => cur
    | some b =>
      match cur with
      | none => some (b + 1)
      | some a => some (min a (b + 1))

private def finalizeCell (mode isLast : Bool) (dp carry : Option ℕ) : SubsetDPCell :=
  if isLast then
    let v := combineCell mode dp carry
    (v, v)
  else
    (dp, carry)

private def evenCellMap (mode isLast bit : Bool) (c : SubsetDPCell) : SubsetDPCell :=
  finalizeCell mode isLast c.1 (if bit then none else c.2)

private def oddCellMap (mode isLast bit : Bool) (c₀ c₁ : SubsetDPCell) : SubsetDPCell :=
  finalizeCell mode isLast c₁.1 (if bit then c₀.2 else c₁.2)

private def evensMap {α : Type*} (f : α → α) : List α → List α
  | [] => []
  | [a] => [f a]
  | a :: _ :: rest => f a :: evensMap f rest

private def passOddsMap {α : Type*} (f : α → α → α) : List α → List α
  | a :: b :: rest => f a b :: passOddsMap f rest
  | _ => []

/-- Single bit-rotation butterfly pass over a table `L` of `SubsetDPCell` values. -/
def butterflyPass (mode isLast bit : Bool) (L : List SubsetDPCell) : List SubsetDPCell :=
  evensMap (evenCellMap mode isLast bit) L ++ passOddsMap (oddCellMap mode isLast bit) L

private def interleave {α : Type*} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: interleave ys xs
termination_by xs ys => xs.length + ys.length
decreasing_by
  simp_wf
  omega

private theorem length_interleave {α : Type*} (xs ys : List α) :
    (interleave xs ys).length = xs.length + ys.length := by
  fun_induction interleave xs ys <;> simp [*]
  omega

private theorem mem_interleave {α : Type*} {xs ys : List α} {z : α} :
    z ∈ interleave xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  fun_induction interleave xs ys <;> simp [*]
  tauto

private theorem evensMap_interleave {α : Type*} (f : α → α) (xs ys : List α)
    (h : xs.length = ys.length) :
    evensMap f (interleave xs ys) = xs.map f := by
  induction xs generalizing ys <;> cases ys <;> simp_all [interleave, evensMap]

private theorem passOddsMap_interleave {α : Type*} (f : α → α → α) (xs ys : List α)
    (h : xs.length = ys.length) :
    passOddsMap f (interleave xs ys) = List.zipWith f xs ys := by
  induction xs generalizing ys <;> cases ys <;> simp_all [interleave, passOddsMap]

private theorem interleave_append {α : Type*} (xs₁ ys₁ xs₂ ys₂ : List α)
    (h : xs₁.length = ys₁.length) :
    interleave xs₁ ys₁ ++ interleave xs₂ ys₂ = interleave (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction xs₁ generalizing ys₁ <;> cases ys₁ <;> simp_all [interleave]

/-- Tabulate `f : List Bool → α` over all Boolean bitstrings of length `m` in least-significant-bit
interleaved order. -/
def tabulateLSB {α : Type*} : ℕ → (List Bool → α) → List α
  | 0, f => [f []]
  | m + 1, f => interleave (tabulateLSB m (fun bs => f (false :: bs)))
      (tabulateLSB m (fun bs => f (true :: bs)))

/-- Base case of `tabulateLSB` at `m = 0`. -/
@[simp]
theorem tabulateLSB_zero {α : Type*} (f : List Bool → α) : tabulateLSB 0 f = [f []] := by
  rfl

/-- `tabulateLSB m f` has exact length $2^m$. -/
theorem length_tabulateLSB {α : Type*} (m : ℕ) (f : List Bool → α) :
    (tabulateLSB m f).length = 2 ^ m := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [tabulateLSB, length_interleave, ih, pow_succ]
    omega

/-- Congruence of `tabulateLSB m` on functions agreeing on all bitstrings of length `m`. -/
theorem tabulateLSB_congr {α : Type*} {m : ℕ} {f g : List Bool → α}
    (h : ∀ bs, bs.length = m → f bs = g bs) :
    tabulateLSB m f = tabulateLSB m g := by
  induction m generalizing f g with
  | zero => simp [tabulateLSB, h [] rfl]
  | succ m ih =>
    simp only [tabulateLSB]
    congr 1
    · exact ih fun bs hbs => h (false :: bs) (by simp [hbs])
    · exact ih fun bs hbs => h (true :: bs) (by simp [hbs])

/-- Every entry of `tabulateLSB m f` has the form `f bs` for some `bs` of length `m`. -/
theorem mem_tabulateLSB_exists {α : Type*} {m : ℕ} {f : List Bool → α} {x : α}
    (hx : x ∈ tabulateLSB m f) : ∃ bs, bs.length = m ∧ x = f bs := by
  induction m generalizing f with
  | zero => exact ⟨[], rfl, List.mem_singleton.mp hx⟩
  | succ m ih =>
    rcases mem_interleave.mp hx with h | h <;> obtain ⟨bs, hbs, hfx⟩ := ih h
    exacts [⟨false :: bs, by simp [hbs], hfx⟩, ⟨true :: bs, by simp [hbs], hfx⟩]

private theorem interleave_replicate {α : Type*} (m : ℕ) (b : α) :
    interleave (List.replicate m b) (List.replicate m b) = List.replicate (2 * m) b := by
  induction m with
  | zero => simp [interleave]
  | succ m ih =>
    rw [List.replicate_succ, interleave, interleave, ih,
      show 2 * (m + 1) = (2 * m + 1) + 1 by omega, List.replicate_succ, List.replicate_succ]

/-- Tabulating a function that returns `a` on `replicate q false` and `b` everywhere else yields
`[a] ++ replicate (2 ^ q - 1) b`. -/
theorem tabulateLSB_eq_single_false {α : Type*} (a b : α) (q : ℕ) :
    tabulateLSB q (fun bs => if bs = List.replicate q false then a else b) =
      [a] ++ List.replicate (2 ^ q - 1) b := by
  induction q with
  | zero => rfl
  | succ n ih =>
    rw [tabulateLSB]
    have h1 : tabulateLSB n
        (fun bs => if false :: bs = List.replicate (n + 1) false then a else b) =
        [a] ++ List.replicate (2 ^ n - 1) b := by
      simpa [List.replicate_succ] using ih
    have h2 : tabulateLSB n
        (fun bs => if true :: bs = List.replicate (n + 1) false then a else b) =
        List.replicate (2 ^ n) b := by
      have hconst : tabulateLSB n
          (fun bs => if true :: bs = List.replicate (n + 1) false then a else b) =
          tabulateLSB n (fun _ => b) :=
        tabulateLSB_congr fun bs _ => by simp [List.replicate_succ]
      rw [hconst]
      clear h1 hconst ih
      induction n with
      | zero => rfl
      | succ k ihk =>
        rw [tabulateLSB, ihk, interleave_replicate, Nat.pow_succ, Nat.mul_comm]
    rw [h1, h2]
    obtain ⟨p, hp⟩ : ∃ p, 2 ^ n = p + 1 := ⟨2 ^ n - 1, by have := @Nat.one_le_two_pow n; omega⟩
    rw [hp, show p + 1 - 1 = p by omega, List.replicate_succ, List.singleton_append, interleave,
      interleave, interleave_replicate, pow_succ, hp,
      show (p + 1) * 2 = (2 * p + 1) + 1 by omega, Nat.add_sub_cancel, List.replicate_succ]
    rfl

private theorem map_tabulateLSB {α β : Type*} (m : ℕ) (f : α → β) (g : List Bool → α) :
    (tabulateLSB m g).map f = tabulateLSB m (fun bs => f (g bs)) := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
    have hmap : ∀ (xs ys : List α), xs.length = ys.length →
        (interleave xs ys).map f = interleave (xs.map f) (ys.map f) := by
      intro xs ys h
      induction xs generalizing ys <;> cases ys <;> simp_all [interleave]
    rw [tabulateLSB, tabulateLSB, hmap _ _ (by simp [length_tabulateLSB]), ih, ih]

private theorem zipWith_tabulateLSB {α : Type*} (m : ℕ) (f : α → α → α)
    (g₁ g₂ : List Bool → α) :
    List.zipWith f (tabulateLSB m g₁) (tabulateLSB m g₂) =
      tabulateLSB m fun bs => f (g₁ bs) (g₂ bs) := by
  induction m generalizing g₁ g₂ with
  | zero => rfl
  | succ m ih =>
    have key : ∀ (a₁ b₁ a₂ b₂ : List α), a₁.length = b₁.length → a₂.length = b₂.length →
        a₁.length = a₂.length →
        List.zipWith f (interleave a₁ b₁) (interleave a₂ b₂) =
          interleave (List.zipWith f a₁ a₂) (List.zipWith f b₁ b₂) := by
      intro a₁ b₁ a₂ b₂ h1 h2 h12
      induction a₁ generalizing b₁ a₂ b₂ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;>
        simp only [List.length_cons, List.length_nil] at h1 h2 h12 <;> try omega
      · simp [interleave]
      · simp only [interleave, List.zipWith_cons_cons, List.cons.injEq, true_and]
        apply_assumption <;> omega
    rw [tabulateLSB, tabulateLSB, tabulateLSB,
      key _ _ _ _ (by simp [length_tabulateLSB])
        (by simp [length_tabulateLSB]) (by simp [length_tabulateLSB]), ih, ih]

private theorem tabulateLSB_append_eq {α : Type*} (m : ℕ) (g : List Bool → α) :
    tabulateLSB m (fun bs => g (bs ++ [false])) ++
        tabulateLSB m (fun bs => g (bs ++ [true])) =
      tabulateLSB (m + 1) g := by
  induction m generalizing g with
  | zero => simp [tabulateLSB, interleave]
  | succ m ih =>
    rw [tabulateLSB, tabulateLSB, interleave_append _ _ _ _ (by simp [length_tabulateLSB])]
    simp only [List.cons_append]
    rw [ih (fun bs => g (false :: bs)), ih (fun bs => g (true :: bs))]
    rfl

private theorem getLast?_interleave {α : Type*} (xs ys : List α)
    (h : xs.length = ys.length) (hne : ys ≠ []) :
    (interleave xs ys).getLast? = ys.getLast? := by
  match xs, ys with
  | _, [] => exact absurd rfl hne
  | [], _ :: _ | [_], _ :: _ :: _ | _ :: _ :: _, [_] => simp at h
  | [_], [_] => simp [interleave]
  | _ :: x' :: xs', _ :: y' :: ys' =>
    have hlen : (x' :: xs').length = (y' :: ys').length := by
      simp only [List.length_cons] at h ⊢; omega
    simpa [interleave] using getLast?_interleave (x' :: xs') (y' :: ys') hlen (List.cons_ne_nil _ _)

/-- The final element of `tabulateLSB m g` evaluates `g` at `List.replicate m true`. -/
theorem foldl_last_tabulateLSB {α : Type*} (m : ℕ) (g : List Bool → α) (d : α) :
    (tabulateLSB m g).foldl (fun _ x => x) d = g (List.replicate m true) := by
  have hlast : (tabulateLSB m g).getLast? = some (g (List.replicate m true)) := by
    induction m generalizing g with
    | zero => rfl
    | succ m ih =>
      rw [tabulateLSB, getLast?_interleave _ _ (by simp [length_tabulateLSB])
        (by intro he; simpa [length_tabulateLSB] using congrArg List.length he),
        ih fun bs => g (true :: bs), List.replicate_succ]
  have hfl (l : List α) : ∀ a₀, l ≠ [] → some (l.foldl (fun _ x => x) a₀) = l.getLast? := by
    induction l with
    | nil => exact fun _ hne => absurd rfl hne
    | cons a t ih =>
      cases t with
      | nil => exact fun _ _ => rfl
      | cons b t => exact fun _ _ => ih a (List.cons_ne_nil _ _)
  refine Option.some.inj ((hfl (tabulateLSB m g) d ?_).trans hlast)
  intro he
  simpa [length_tabulateLSB] using congrArg List.length he

/-- Subset of `Fin q` decoded from a Boolean characteristic mask `bs`. -/
@[expose]
def setOfBits (q : ℕ) (bs : List Bool) : Finset (Fin q) :=
  Finset.univ.filter fun j => bs.getD j.1 false = true

/-- Membership characterization for `setOfBits`. -/
theorem mem_setOfBits_iff {q : ℕ} {bs : List Bool} {j : Fin q} :
    j ∈ setOfBits q bs ↔ bs.getD j.1 false = true := by
  simp [setOfBits]

/-- Decoding `replicate q true` yields `Finset.univ`. -/
theorem setOfBits_replicate_true (q : ℕ) :
    setOfBits q (List.replicate q true) = Finset.univ := by
  ext j; simp [setOfBits]

/-- Decoding `replicate q false` yields `∅`. -/
theorem setOfBits_replicate_false (q : ℕ) :
    setOfBits q (List.replicate q false) = ∅ := by
  ext j
  simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_replicate]
  decide

private theorem rotate_cons_rotate_sub {α : Type*} {q i : ℕ} (_hi : i < q) (b : α)
    (r : List α) (hr : r.length + 1 = q) :
    (r ++ [b]).rotate (q - (i + 1)) = (b :: r).rotate (q - i) := by
  have h1 : r ++ [b] = (b :: r).rotate 1 := by simp [List.rotate_cons_succ]
  rw [h1, List.rotate_rotate]
  congr 1; omega

private theorem getD_rotate_cons {q i : ℕ} (_hi : i < q) (b : Bool)
    (r : List Bool) (hr : r.length + 1 = q) (d : Bool) (j : Fin q) :
    ((b :: r).rotate (q - i)).getD j.1 d =
      if j.1 = i then b else ((false :: r).rotate (q - i)).getD j.1 d := by
  have hlen : (b :: r).length = q := by simp [hr]
  have hlenf : (false :: r).length = q := by simp [hr]
  have hj : j.1 < ((b :: r).rotate (q - i)).length := by
    rw [List.length_rotate, hlen]; exact j.isLt
  have hjf : j.1 < ((false :: r).rotate (q - i)).length := by
    rw [List.length_rotate, hlenf]; exact j.isLt
  rw [List.getD_eq_getElem _ _ hj, List.getElem_rotate]
  by_cases hji : j.1 = i
  · subst hji
    simp only [hlen, Nat.add_sub_of_le j.isLt.le, Nat.mod_self, List.getElem_cons_zero, ↓reduceIte]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hji),
      List.getD_eq_getElem _ _ hjf, List.getElem_rotate]
    have hnz : (j.1 + (q - i)) % q ≠ 0 := by
      intro h0
      rcases Nat.lt_or_ge j.1 i with hlt | hgt
      · rw [Nat.mod_eq_of_lt (by omega)] at h0; omega
      · have hsum : j.1 + (q - i) = (j.1 - i) + q := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h0; omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnz
    simp only [hlen, hlenf, hk, List.getElem_cons_succ]

private theorem setOfBits_rotate_true_erase {q i : ℕ} (hi : i < q) (r : List Bool)
    (hr : r.length + 1 = q) :
    (setOfBits q ((true :: r).rotate (q - i))).erase ⟨i, hi⟩ =
      setOfBits q ((false :: r).rotate (q - i)) := by
  have hins : setOfBits q ((true :: r).rotate (q - i)) =
      insert ⟨i, hi⟩ (setOfBits q ((false :: r).rotate (q - i))) := by
    ext j
    simp only [setOfBits, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.ext_iff, getD_rotate_cons hi true r hr false j]
    by_cases hji : j.1 = i <;> simp [hji]
  rw [hins, Finset.erase_insert]
  simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and,
    getD_rotate_cons hi false r hr false ⟨i, hi⟩, ↓reduceIte, Bool.false_eq_true, not_false_eq_true]

private theorem butterflyPass_tabulateLSB_rotate {q i : ℕ} (hq : 0 < q) (hi : i < q)
    (mode isLast bit : Bool) (G : Finset (Fin q) → SubsetDPCell) :
    butterflyPass mode isLast bit
        (tabulateLSB q fun bs => G (setOfBits q (bs.rotate (q - i)))) =
      tabulateLSB q fun bs =>
        let S := setOfBits q (bs.rotate (q - (i + 1)))
        if ⟨i, hi⟩ ∈ S then oddCellMap mode isLast bit (G (S.erase ⟨i, hi⟩)) (G S)
        else evenCellMap mode isLast bit (G S) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  rw [butterflyPass, tabulateLSB,
    evensMap_interleave _ _ _ (by simp [length_tabulateLSB]),
    passOddsMap_interleave _ _ _ (by simp [length_tabulateLSB]),
    map_tabulateLSB, zipWith_tabulateLSB, ← tabulateLSB_append_eq]
  refine congrArg₂ (· ++ ·) (tabulateLSB_congr fun r hr => ?_) (tabulateLSB_congr fun r hr => ?_)
  · rw [rotate_cons_rotate_sub hi false r (by omega)]
    have hnot : (⟨i, hi⟩ : Fin (m + 1)) ∉ setOfBits (m + 1) ((false :: r).rotate (m + 1 - i)) := by
      simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and,
        getD_rotate_cons hi false r (by omega) false ⟨i, hi⟩, ↓reduceIte, Bool.false_eq_true,
        not_false_eq_true]
    simp [hnot]
  · rw [rotate_cons_rotate_sub hi true r (by omega)]
    have hmem : (⟨i, hi⟩ : Fin (m + 1)) ∈ setOfBits (m + 1) ((true :: r).rotate (m + 1 - i)) := by
      simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and,
        getD_rotate_cons hi true r (by omega) false ⟨i, hi⟩, ↓reduceIte]
    simp [hmem, setOfBits_rotate_true_erase hi r (by omega)]

/-- Carry value after `i` bit-passes of `mask` starting from DP function `dp`. -/
def subsetDPExpectedCarry {q : ℕ} (dp : Finset (Fin q) → Option ℕ) (mask : List Bool)
    (i : ℕ) (S : Finset (Fin q)) : Option ℕ :=
  if ∀ j : Fin q, j.1 < i → mask.getD j.1 false = true → j ∈ S then
    dp (S.filter fun j => !(decide (j.1 < i) && mask.getD j.1 false))
  else
    none

/-- At pass `i = 0`, `subsetDPExpectedCarry` coincides with `dp`. -/
theorem subsetDPExpectedCarry_zero {q : ℕ} (dp : Finset (Fin q) → Option ℕ) (mask : List Bool)
    (S : Finset (Fin q)) :
    subsetDPExpectedCarry dp mask 0 S = dp S := by
  simp [subsetDPExpectedCarry]

private theorem expectedCarry_full {q : ℕ} (dp : Finset (Fin q) → Option ℕ) (mask : List Bool)
    (S : Finset (Fin q)) :
    subsetDPExpectedCarry dp mask q S =
      if setOfBits q mask ⊆ S then dp (S \ setOfBits q mask) else none := by
  unfold subsetDPExpectedCarry
  have hcond : (∀ j : Fin q, j.1 < q → mask.getD j.1 false = true → j ∈ S) ↔
      setOfBits q mask ⊆ S := by
    simp [Finset.subset_iff, setOfBits]
  have hset : (S.filter fun j : Fin q => !(decide (j.1 < q) && mask.getD j.1 false)) =
      S \ setOfBits q mask := by
    ext j
    simp [setOfBits]
  split_ifs with h1 h2 h3
  · exact congrArg dp hset
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h3) h1
  · rfl

private theorem cell_pass_step {q i : ℕ} (hi : i < q) (mode : Bool)
    (dp : Finset (Fin q) → Option ℕ) (mask : List Bool) (S : Finset (Fin q)) :
    let G : Finset (Fin q) → SubsetDPCell := fun T => (dp T, subsetDPExpectedCarry dp mask i T)
    let isLast := decide (i + 1 = q)
    let bit := mask.getD i false
    (if ⟨i, hi⟩ ∈ S then oddCellMap mode isLast bit (G (S.erase ⟨i, hi⟩)) (G S)
     else evenCellMap mode isLast bit (G S)) =
      finalizeCell mode isLast (dp S) (subsetDPExpectedCarry dp mask (i + 1) S) := by
  intro G isLast bit
  by_cases hmem : (⟨i, hi⟩ : Fin q) ∈ S
  · simp only [hmem, ↓reduceIte, oddCellMap, G]
    congr 1
    cases hbit : mask.getD i false
    · simp only [bit, hbit, Bool.false_eq_true, ↓reduceIte, subsetDPExpectedCarry]
      have hcond : (∀ j : Fin q, j.1 < i → mask.getD j.1 false = true → j ∈ S) ↔
          (∀ j : Fin q, j.1 < i + 1 → mask.getD j.1 false = true → j ∈ S) := by
        refine ⟨fun h j hj hm => ?_, fun h j hj => h j (by omega)⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
        · exact h j hlt hm
        · rw [hbit] at hm; cases hm
      have hfilt : (S.filter fun j : Fin q => !(decide (j.1 < i) && mask.getD j.1 false)) =
          (S.filter fun j : Fin q => !(decide (j.1 < i + 1) && mask.getD j.1 false)) := by
        ext j
        simp only [Finset.mem_filter]
        by_cases hji : j.1 = i
        · rw [hji, hbit]; simp
        · have hlt_eq : decide (j.1 < i) = decide (j.1 < i + 1) := by simp; omega
          rw [hlt_eq]
      split_ifs with h1 h2 h3
      · exact congrArg dp hfilt
      · exact absurd (hcond.mp h1) h2
      · exact absurd (hcond.mpr h3) h1
      · rfl
    · simp only [bit, hbit, ↓reduceIte, subsetDPExpectedCarry]
      have hcond : (∀ j : Fin q, j.1 < i → mask.getD j.1 false = true → j ∈ S.erase ⟨i, hi⟩) ↔
          (∀ j : Fin q, j.1 < i + 1 → mask.getD j.1 false = true → j ∈ S) := by
        refine ⟨fun h j hj hm => ?_, fun h j hj hm => ?_⟩
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
          · exact Finset.mem_of_mem_erase (h j hlt hm)
          · exact (Fin.ext heq : j = ⟨i, hi⟩) ▸ hmem
        · exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp; omega), h j (by omega) hm⟩
      have hfilt : ((S.erase ⟨i, hi⟩).filter fun j : Fin q =>
            !(decide (j.1 < i) && mask.getD j.1 false)) =
          (S.filter fun j : Fin q => !(decide (j.1 < i + 1) && mask.getD j.1 false)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_erase]
        by_cases hji : j = ⟨i, hi⟩
        · subst hji; dsimp; rw [hbit]; simp
        · have hne : j.1 ≠ i := Fin.val_ne_of_ne hji
          have hlt_eq : decide (j.1 < i) = decide (j.1 < i + 1) := by simp; omega
          simp [hji, hlt_eq]
      split_ifs with h1 h2 h3
      · exact congrArg dp hfilt
      · exact absurd (hcond.mp h1) h2
      · exact absurd (hcond.mpr h3) h1
      · rfl
  · simp only [hmem, ↓reduceIte, evenCellMap, G]
    congr 1
    cases hbit : mask.getD i false
    · simp only [bit, hbit, Bool.false_eq_true, ↓reduceIte, subsetDPExpectedCarry]
      have hcond : (∀ j : Fin q, j.1 < i → mask.getD j.1 false = true → j ∈ S) ↔
          (∀ j : Fin q, j.1 < i + 1 → mask.getD j.1 false = true → j ∈ S) := by
        refine ⟨fun h j hj hm => ?_, fun h j hj => h j (by omega)⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
        · exact h j hlt hm
        · rw [hbit] at hm; cases hm
      have hfilt : (S.filter fun j : Fin q => !(decide (j.1 < i) && mask.getD j.1 false)) =
          (S.filter fun j : Fin q => !(decide (j.1 < i + 1) && mask.getD j.1 false)) := by
        ext j
        simp only [Finset.mem_filter]
        by_cases hji : j.1 = i
        · rw [hji, hbit]; simp
        · have hlt_eq : decide (j.1 < i) = decide (j.1 < i + 1) := by simp; omega
          rw [hlt_eq]
      split_ifs with h1 h2 h3
      · exact congrArg dp hfilt
      · exact absurd (hcond.mp h1) h2
      · exact absurd (hcond.mpr h3) h1
      · rfl
    · simp only [bit, hbit, ↓reduceIte, subsetDPExpectedCarry]
      split_ifs with hc
      · exact absurd (hc ⟨i, hi⟩ (Nat.lt_succ_self i) hbit) hmem
      · rfl

private def stageTransition {q : ℕ} (mode : Bool) (mask : List Bool)
    (dp : Finset (Fin q) → Option ℕ) (S : Finset (Fin q)) : Option ℕ :=
  combineCell mode (dp S) (if setOfBits q mask ⊆ S then dp (S \ setOfBits q mask) else none)

/-- Dynamic-programming table after processing the first `r` masks of `masks` (`mode = true` for
maximum disjoint subset packing, `mode = false` for minimum exact subset partition). -/
def subsetDPPrefix {q : ℕ} (mode : Bool) (masks : List (List Bool)) :
    ℕ → Finset (Fin q) → Option ℕ
  | 0 => fun S => if mode then some 0 else (if S = ∅ then some 0 else none)
  | r + 1 => stageTransition mode (masks.getD r []) (subsetDPPrefix mode masks r)

/-- Base case `r = 0` of `subsetDPPrefix`. -/
theorem subsetDPPrefix_zero {q : ℕ} (mode : Bool) (masks : List (List Bool)) (S : Finset (Fin q)) :
    subsetDPPrefix mode masks 0 S =
      if mode then some 0 else (if S = ∅ then some 0 else none) := by
  rfl

/-- Exact rotated-table transition across pass `i < q` of stage `r`. -/
theorem butterflyPass_tabulateLSB_step {q r i : ℕ} (hq : 0 < q) (hi : i < q)
    (mode : Bool) (masks : List (List Bool)) :
    butterflyPass mode (decide (i + 1 = q)) ((masks.getD r []).getD i false)
        (tabulateLSB q fun bs =>
          let T := setOfBits q (bs.rotate (q - i))
          (subsetDPPrefix mode masks r T,
           subsetDPExpectedCarry (subsetDPPrefix mode masks r) (masks.getD r []) i T)) =
      if i + 1 = q then
        tabulateLSB q fun bs =>
          let v := subsetDPPrefix mode masks (r + 1) (setOfBits q bs)
          (v, v)
      else
        tabulateLSB q fun bs =>
          let T := setOfBits q (bs.rotate (q - (i + 1)))
          (subsetDPPrefix mode masks r T,
           subsetDPExpectedCarry (subsetDPPrefix mode masks r) (masks.getD r []) (i + 1) T) := by
  rw [butterflyPass_tabulateLSB_rotate hq hi mode (decide (i + 1 = q))
    ((masks.getD r []).getD i false)
    (fun T => (subsetDPPrefix mode masks r T,
      subsetDPExpectedCarry (subsetDPPrefix mode masks r) (masks.getD r []) i T))]
  by_cases hlast : i + 1 = q
  · simp only [hlast, decide_true, ↓reduceIte]
    refine tabulateLSB_congr fun bs _ => ?_
    have hstep := cell_pass_step hi mode (subsetDPPrefix mode masks r) (masks.getD r [])
      (setOfBits q (bs.rotate (q - (i + 1))))
    dsimp only at hstep
    simp only [hlast, decide_true, Nat.sub_self, List.rotate_zero] at hstep ⊢
    rw [hstep, finalizeCell]
    simp only [↓reduceIte, expectedCarry_full]
    rfl
  · simp only [hlast, decide_false, ↓reduceIte]
    refine tabulateLSB_congr fun bs _ => ?_
    have hstep := cell_pass_step hi mode (subsetDPPrefix mode masks r) (masks.getD r [])
      (setOfBits q (bs.rotate (q - (i + 1))))
    dsimp only at hstep
    simp only [hlast, decide_false] at hstep
    rw [hstep, finalizeCell]
    simp

/-- Every finite value stored in `subsetDPPrefix mode masks r` is bounded by `r`. -/
theorem subsetDPPrefix_bound {q : ℕ} (mode : Bool) (masks : List (List Bool)) :
    ∀ (r : ℕ) (S : Finset (Fin q)) (v : ℕ), subsetDPPrefix mode masks r S = some v → v ≤ r
  | 0, S, v, hv => by
    dsimp [subsetDPPrefix] at hv
    split_ifs at hv
    all_goals obtain rfl := Option.some.inj hv.symm; exact le_rfl
  | r + 1, S, v, hv => by
    dsimp [subsetDPPrefix, stageTransition, combineCell] at hv
    cases mode
    · dsimp at hv
      split at hv
      · have ih := subsetDPPrefix_bound false masks r S v hv; omega
      · rename_i b hcarry
        split_ifs at hcarry with hsub
        have ihb := subsetDPPrefix_bound false masks r (S \ setOfBits q (masks.getD r [])) b hcarry
        cases hcur : subsetDPPrefix false masks r S with
        | none => rw [hcur] at hv; simp at hv; omega
        | some a =>
          rw [hcur] at hv; simp at hv
          have iha := subsetDPPrefix_bound false masks r S a hcur
          omega
    · dsimp at hv
      cases hcur : subsetDPPrefix true masks r S with
      | none => rw [hcur] at hv; cases hv
      | some a =>
        rw [hcur] at hv
        have iha := subsetDPPrefix_bound true masks r S a hcur
        cases hcarry : (if setOfBits q (masks.getD r []) ⊆ S then
            subsetDPPrefix true masks r (S \ setOfBits q (masks.getD r [])) else none) with
        | none => rw [hcarry] at hv; simp at hv; omega
        | some b =>
          rw [hcarry] at hv; simp at hv
          split_ifs at hcarry with hsub
          have ihb := subsetDPPrefix_bound true masks r _ b hcarry
          omega

/-- Every finite carry value in `subsetDPExpectedCarry (subsetDPPrefix mode masks r)` is bounded
by `r`. -/
theorem subsetDPExpectedCarry_bound {q : ℕ} (mode : Bool) (masks : List (List Bool))
    (r i : ℕ) (mask : List Bool) (S : Finset (Fin q)) (v : ℕ)
    (hv : subsetDPExpectedCarry (subsetDPPrefix mode masks r) mask i S = some v) :
    v ≤ r := by
  dsimp only [subsetDPExpectedCarry] at hv
  split_ifs at hv with hcond
  exact subsetDPPrefix_bound mode masks r _ v hv

/-- **Semantic correctness of `subsetDPPrefix true`**: computes the greatest cardinality of a
pairwise-disjoint subfamily among the first `r` masks contained in `T`. -/
theorem subsetDPPrefix_true_spec {q : ℕ} (masks : List (List Bool)) :
    ∀ (r : ℕ) (_hr : r ≤ masks.length) (T : Finset (Fin q)),
      ∃ v : ℕ, subsetDPPrefix true masks r T = some v ∧
        IsGreatest {k : ℕ | ∃ C : Finset (Fin masks.length),
          (∀ j ∈ C, j.1 < r) ∧ C.card = k ∧
          (C : Set (Fin masks.length)).Pairwise
            (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])) ∧
          ∀ j ∈ C, setOfBits q masks[j] ⊆ T} v
  | 0, _, T => by
    refine ⟨0, rfl, ⟨∅, by simp, rfl, by simp, by simp⟩, ?_⟩
    rintro k ⟨C, hlt, rfl, _, _⟩
    have : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun j hj => by have := hlt j hj; omega
    simp [this]
  | r + 1, hr, T => by
    have hr_lt : r < masks.length := hr
    let rFin : Fin masks.length := ⟨r, hr_lt⟩
    have hget : masks.getD r [] = masks[rFin] := List.getD_eq_getElem _ _ hr_lt
    obtain ⟨v₀, hv₀, hv₀_gt⟩ := subsetDPPrefix_true_spec masks r hr_lt.le T
    obtain ⟨v₁, hv₁, hv₁_gt⟩ :=
      subsetDPPrefix_true_spec masks r hr_lt.le (T \ setOfBits q masks[rFin])
    dsimp only [subsetDPPrefix, stageTransition, combineCell, ↓reduceIte]
    rw [hget, hv₀]
    by_cases hsub : setOfBits q masks[rFin] ⊆ T
    · simp only [hsub, ↓reduceIte]
      rw [hv₁]
      refine ⟨max v₀ (v₁ + 1), rfl, ?_, ?_⟩
      · rcases le_total v₀ (v₁ + 1) with hle | hle
        · rw [max_eq_right hle]
          obtain ⟨C₁, hlt₁, hcard₁, hdisj₁, hsub₁⟩ := hv₁_gt.1
          have hr_nmem : rFin ∉ C₁ := fun hm => (lt_irrefl r) (hlt₁ rFin hm)
          refine ⟨insert rFin C₁, fun j hj => ?_, ?_, ?_, fun j hj => ?_⟩
          · rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact Nat.lt_succ_self r
            · exact Nat.lt_succ_of_lt (hlt₁ j hj')
          · rw [Finset.card_insert_of_notMem hr_nmem, hcard₁]
          · rw [Finset.coe_insert]
            refine Set.Pairwise.insert hdisj₁ fun j hj _ => ?_
            have hjsub := hsub₁ j hj
            exact ⟨Finset.disjoint_left.mpr fun x hxR hxJ =>
              (Finset.mem_sdiff.mp (hjsub hxJ)).2 hxR,
              Finset.disjoint_left.mpr fun x hxJ hxR =>
              (Finset.mem_sdiff.mp (hjsub hxJ)).2 hxR⟩
          · rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact hsub
            · exact (hsub₁ j hj').trans Finset.sdiff_subset
        · rw [max_eq_left hle]
          obtain ⟨C₀, hlt₀, hcard₀, hdisj₀, hsub₀⟩ := hv₀_gt.1
          exact ⟨C₀, fun j hj => Nat.lt_succ_of_lt (hlt₀ j hj), hcard₀, hdisj₀, hsub₀⟩
      · rintro k ⟨C, hlt, rfl, hdisj, hCsub⟩
        by_cases hr_in : rFin ∈ C
        · let C' := C.erase rFin
          have hC'_mem : C'.card ∈ {k : ℕ | ∃ D : Finset (Fin masks.length),
              (∀ j ∈ D, j.1 < r) ∧ D.card = k ∧
              (D : Set (Fin masks.length)).Pairwise
                (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])) ∧
              ∀ j ∈ D, setOfBits q masks[j] ⊆ T \ setOfBits q masks[rFin]} := by
            refine ⟨C', fun j hj => ?_, rfl,
              hdisj.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)), fun j hj => ?_⟩
            · obtain ⟨hne, hjC⟩ := Finset.mem_erase.mp hj
              have hlt' := hlt j hjC
              have hne_val : j.1 ≠ r := Fin.val_ne_of_ne hne
              omega
            · obtain ⟨hne, hjC⟩ := Finset.mem_erase.mp hj
              have hdj := hdisj hjC hr_in hne
              intro x hx
              exact Finset.mem_sdiff.mpr ⟨hCsub j hjC hx, Finset.disjoint_left.mp hdj hx⟩
          have hle_v₁ := hv₁_gt.2 hC'_mem
          have hcard_eq : C.card = C'.card + 1 := (Finset.card_erase_add_one hr_in).symm
          exact (hcard_eq ▸ Nat.add_le_add_right hle_v₁ 1).trans (le_max_right _ _)
        · have hC_mem : C.card ∈ {k : ℕ | ∃ D : Finset (Fin masks.length),
              (∀ j ∈ D, j.1 < r) ∧ D.card = k ∧
              (D : Set (Fin masks.length)).Pairwise
                (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])) ∧
              ∀ j ∈ D, setOfBits q masks[j] ⊆ T} := by
            refine ⟨C, fun j hj => ?_, rfl, hdisj, hCsub⟩
            have hlt' := hlt j hj
            have hne : j.1 ≠ r := fun he => hr_in ((Fin.ext he : j = rFin) ▸ hj)
            omega
          exact (hv₀_gt.2 hC_mem).trans (le_max_left _ _)
    · simp only [hsub, ↓reduceIte]
      refine ⟨v₀, rfl, ?_, ?_⟩
      · obtain ⟨C₀, hlt₀, hcard₀, hdisj₀, hsub₀⟩ := hv₀_gt.1
        exact ⟨C₀, fun j hj => Nat.lt_succ_of_lt (hlt₀ j hj), hcard₀, hdisj₀, hsub₀⟩
      · rintro k ⟨C, hlt, rfl, hdisj, hCsub⟩
        have hr_nin : rFin ∉ C := fun hm => hsub (hCsub rFin hm)
        refine hv₀_gt.2 ⟨C, fun j hj => ?_, rfl, hdisj, hCsub⟩
        have hlt' := hlt j hj
        have hne : j.1 ≠ r := fun he => hr_nin ((Fin.ext he : j = rFin) ▸ hj)
        omega

/-- **Semantic correctness of `subsetDPPrefix false`**: computes the least cardinality of an exact
partition of `T` among the first `r` masks (or `none` when no exact partition exists). -/
theorem subsetDPPrefix_false_spec {q : ℕ} (masks : List (List Bool)) :
    ∀ (r : ℕ) (_hr : r ≤ masks.length) (T : Finset (Fin q)),
      (∀ v, subsetDPPrefix false masks r T = some v →
        IsLeast {k : ℕ | ∃ C : Finset (Fin masks.length),
          (∀ j ∈ C, j.1 < r) ∧ C.card = k ∧
          (C : Set (Fin masks.length)).Pairwise
            (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])) ∧
          C.biUnion (fun j => setOfBits q masks[j]) = T} v) ∧
      (subsetDPPrefix false masks r T = none →
        ¬∃ C : Finset (Fin masks.length),
          (∀ j ∈ C, j.1 < r) ∧
          (C : Set (Fin masks.length)).Pairwise
            (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])) ∧
          C.biUnion (fun j => setOfBits q masks[j]) = T)
  | 0, _, T => by
    dsimp only [subsetDPPrefix, Bool.false_eq_true, ↓reduceIte]
    by_cases hT : T = ∅
    · subst hT
      refine ⟨fun v hv => ?_, fun h => by simp at h⟩
      obtain rfl : v = 0 := by simpa using hv.symm
      exact ⟨⟨∅, by simp, rfl, by simp, by simp⟩, fun _ _ => Nat.zero_le _⟩
    · simp only [hT, ↓reduceIte]
      refine ⟨(fun _ h => by simp at h), ?_⟩
      rintro _ ⟨C, hlt, _, hbi⟩
      have hC : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun j hj => by
        have := hlt j hj; omega
      rw [hC, Finset.biUnion_empty] at hbi
      exact hT hbi.symm
  | r + 1, hr, T => by
    have hr_lt : r < masks.length := hr
    let rFin : Fin masks.length := ⟨r, hr_lt⟩
    have hget : masks.getD r [] = masks[rFin] := List.getD_eq_getElem _ _ hr_lt
    obtain ⟨ih0_some, ih0_none⟩ := subsetDPPrefix_false_spec masks r hr_lt.le T
    obtain ⟨ih1_some, ih1_none⟩ :=
      subsetDPPrefix_false_spec masks r hr_lt.le (T \ setOfBits q masks[rFin])
    let validSet (r' : ℕ) (U : Finset (Fin q)) : Set ℕ :=
      {k : ℕ | ∃ C : Finset (Fin masks.length),
        (∀ j ∈ C, j.1 < r') ∧ C.card = k ∧
        (C : Set (Fin masks.length)).Pairwise
          (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])) ∧
        C.biUnion (fun j => setOfBits q masks[j]) = U}
    have hmem_of_not_in {C : Finset (Fin masks.length)}
        (hlt : ∀ j ∈ C, j.1 < r + 1)
        (hdj : (C : Set (Fin masks.length)).Pairwise
          (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])))
        (hbi : C.biUnion (fun j => setOfBits q masks[j]) = T)
        (hnin : rFin ∉ C) : C.card ∈ validSet r T := by
      refine ⟨C, fun j hj => ?_, rfl, hdj, hbi⟩
      have := hlt j hj
      have hne : j.1 ≠ r := fun he => hnin ((Fin.ext he : j = rFin) ▸ hj)
      omega
    have hmem_of_in {C : Finset (Fin masks.length)}
        (hlt : ∀ j ∈ C, j.1 < r + 1)
        (hdj : (C : Set (Fin masks.length)).Pairwise
          (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])))
        (hbi : C.biUnion (fun j => setOfBits q masks[j]) = T)
        (hin : rFin ∈ C) :
        setOfBits q masks[rFin] ⊆ T ∧
          (C.erase rFin).card ∈ validSet r (T \ setOfBits q masks[rFin]) := by
      have hsub : setOfBits q masks[rFin] ⊆ T := by
        rw [← hbi]
        exact Finset.subset_biUnion_of_mem (fun j => setOfBits q masks[j]) hin
      refine ⟨hsub, C.erase rFin, fun j hj => ?_, rfl,
        hdj.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)), ?_⟩
      · obtain ⟨hne, hjC⟩ := Finset.mem_erase.mp hj
        have := hlt j hjC
        have hne_val : j.1 ≠ r := Fin.val_ne_of_ne hne
        omega
      · ext x
        simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_sdiff]
        constructor
        · rintro ⟨j, ⟨hne, hjC⟩, hxj⟩
          refine ⟨hbi ▸ Finset.mem_biUnion.mpr ⟨j, hjC, hxj⟩, fun hxR => ?_⟩
          exact Finset.disjoint_left.mp (hdj hjC hin hne) hxj hxR
        · rintro ⟨hxT, hx_notR⟩
          rw [← hbi, Finset.mem_biUnion] at hxT
          obtain ⟨j, hjC, hxj⟩ := hxT
          have hne : j ≠ rFin := fun he => hx_notR (he ▸ hxj)
          exact ⟨j, ⟨hne, hjC⟩, hxj⟩
    have hinsert_valid {C₁ : Finset (Fin masks.length)}
        (hsub : setOfBits q masks[rFin] ⊆ T)
        (hlt₁ : ∀ j ∈ C₁, j.1 < r)
        (hdj₁ : (C₁ : Set (Fin masks.length)).Pairwise
          (fun i j => Disjoint (setOfBits q masks[i]) (setOfBits q masks[j])))
        (hbi₁ : C₁.biUnion (fun j => setOfBits q masks[j]) = T \ setOfBits q masks[rFin]) :
        (C₁.card + 1) ∈ validSet (r + 1) T := by
      have hnin : rFin ∉ C₁ := fun hm => (lt_irrefl r) (hlt₁ rFin hm)
      refine ⟨insert rFin C₁, fun j hj => ?_, Finset.card_insert_of_notMem hnin, ?_, ?_⟩
      · rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Nat.lt_succ_self r
        · exact Nat.lt_succ_of_lt (hlt₁ j hj')
      · rw [Finset.coe_insert]
        refine Set.Pairwise.insert hdj₁ fun j hj _ => ?_
        have hjsub : setOfBits q masks[j] ⊆ T \ setOfBits q masks[rFin] :=
          hbi₁ ▸ Finset.subset_biUnion_of_mem (fun i => setOfBits q masks[i]) hj
        exact ⟨Finset.disjoint_left.mpr fun x hxR hxJ => (Finset.mem_sdiff.mp (hjsub hxJ)).2 hxR,
          Finset.disjoint_left.mpr fun x hxJ hxR => (Finset.mem_sdiff.mp (hjsub hxJ)).2 hxR⟩
      · rw [Finset.biUnion_insert, hbi₁, Finset.union_sdiff_of_subset hsub]
    dsimp only [subsetDPPrefix, stageTransition, combineCell, Bool.false_eq_true, ↓reduceIte]
    rw [hget]
    by_cases hsub : setOfBits q masks[rFin] ⊆ T
    · simp only [hsub, ↓reduceIte]
      cases h1 : subsetDPPrefix false masks r (T \ setOfBits q masks[rFin]) with
      | none =>
        cases h0 : subsetDPPrefix false masks r T with
        | none =>
          refine ⟨(fun _ h => by simp at h), ?_⟩
          rintro _ ⟨C, hlt, hdj, hbi⟩
          by_cases hin : rFin ∈ C
          · obtain ⟨C', hC', _, hdj', hbi'⟩ := (hmem_of_in hlt hdj hbi hin).2
            exact ih1_none h1 ⟨C', hC', hdj', hbi'⟩
          · obtain ⟨C', hC', _, hdj', hbi'⟩ := hmem_of_not_in hlt hdj hbi hin
            exact ih0_none h0 ⟨C', hC', hdj', hbi'⟩
        | some a =>
          refine ⟨fun v hv => ?_, fun h => by simp at h⟩
          cases hv
          obtain ⟨⟨C₀, hlt₀, hcard₀, hdj₀, hbi₀⟩, ha_lb⟩ := ih0_some a h0
          refine ⟨⟨C₀, fun j hj => Nat.lt_succ_of_lt (hlt₀ j hj), hcard₀, hdj₀, hbi₀⟩, ?_⟩
          rintro k ⟨C, hlt, rfl, hdj, hbi⟩
          by_cases hin : rFin ∈ C
          · obtain ⟨C', hC', _, hdj', hbi'⟩ := (hmem_of_in hlt hdj hbi hin).2
            exact (ih1_none h1 ⟨C', hC', hdj', hbi'⟩).elim
          · exact ha_lb (hmem_of_not_in hlt hdj hbi hin)
      | some b =>
        obtain ⟨⟨C₁, hlt₁, rfl, hdj₁, hbi₁⟩, hb_lb⟩ := ih1_some b h1
        have hb_valid : (C₁.card + 1) ∈ validSet (r + 1) T := hinsert_valid hsub hlt₁ hdj₁ hbi₁
        cases h0 : subsetDPPrefix false masks r T with
        | none =>
          refine ⟨fun v hv => ?_, fun h => by simp at h⟩
          cases hv
          refine ⟨hb_valid, ?_⟩
          rintro k ⟨C, hlt, rfl, hdj, hbi⟩
          by_cases hin : rFin ∈ C
          · have hle := hb_lb (hmem_of_in hlt hdj hbi hin).2
            have := Finset.card_erase_add_one hin
            omega
          · obtain ⟨C', hC', _, hdj', hbi'⟩ := hmem_of_not_in hlt hdj hbi hin
            exact (ih0_none h0 ⟨C', hC', hdj', hbi'⟩).elim
        | some a =>
          obtain ⟨⟨C₀, hlt₀, rfl, hdj₀, hbi₀⟩, ha_lb⟩ := ih0_some a h0
          have ha_valid : C₀.card ∈ validSet (r + 1) T :=
            ⟨C₀, fun j hj => Nat.lt_succ_of_lt (hlt₀ j hj), rfl, hdj₀, hbi₀⟩
          refine ⟨fun v hv => ?_, fun h => by simp at h⟩
          cases hv
          refine ⟨by rcases min_cases C₀.card (C₁.card + 1) with ⟨he, _⟩ | ⟨he, _⟩ <;>
            exact he.symm ▸ ‹_›, ?_⟩
          rintro k ⟨C, hlt, rfl, hdj, hbi⟩
          by_cases hin : rFin ∈ C
          · have hle := hb_lb (hmem_of_in hlt hdj hbi hin).2
            have := Finset.card_erase_add_one hin
            omega
          · exact (min_le_left _ _).trans (ha_lb (hmem_of_not_in hlt hdj hbi hin))
    · simp only [hsub, ↓reduceIte]
      cases h0 : subsetDPPrefix false masks r T with
      | none =>
        refine ⟨(fun _ h => by simp at h), ?_⟩
        rintro _ ⟨C, hlt, hdj, hbi⟩
        have hnin : rFin ∉ C := fun hin => hsub (hmem_of_in hlt hdj hbi hin).1
        obtain ⟨C', hC', _, hdj', hbi'⟩ := hmem_of_not_in hlt hdj hbi hnin
        exact ih0_none h0 ⟨C', hC', hdj', hbi'⟩
      | some a =>
        obtain ⟨⟨C₀, hlt₀, rfl, hdj₀, hbi₀⟩, ha_lb⟩ := ih0_some a h0
        refine ⟨fun v hv => ?_, fun h => by simp at h⟩
        cases hv
        refine ⟨⟨C₀, fun j hj => Nat.lt_succ_of_lt (hlt₀ j hj), rfl, hdj₀, hbi₀⟩, ?_⟩
        rintro k ⟨C, hlt, rfl, hdj, hbi⟩
        have hnin : rFin ∉ C := fun hin => hsub (hmem_of_in hlt hdj hbi hin).1
        exact ha_lb (hmem_of_not_in hlt hdj hbi hnin)

/-! ### 2. Streaming Multi-Tape Realization of `butterflyPass` and Last-Cell Extraction -/

private theorem computableInO_of_bigO {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {t s T S : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (hT : t ≼ T) (hS : s ≼ S)
    (hl : (fun a => (encOut (f a)).length) ≼ S) : ComputableInO f encIn encOut T S := by
  obtain ⟨k₁, h₁⟩ := hT
  obtain ⟨k₂, h₂⟩ := hS
  obtain ⟨k₃, h₃⟩ := hl
  exact .of_bounds h (k₁ + k₂ + k₃) (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (by omega)))
    (fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (by omega)))
    (fun a => (h₃ a).trans (Nat.mul_le_mul_right _ (by omega)))

open ComputableInPolyTime in
private theorem computableInPolyTime_combineCell :
    ComputableInPolyTime (fun p : Bool × SubsetDPCell => combineCell p.1 p.2.1 p.2.2)
      (encPair encBool encSubsetDPCell) (encOption encNat) := by
  have heq : (fun p : Bool × SubsetDPCell => combineCell p.1 p.2.1 p.2.2) = fun p =>
      if p.1 then
        p.2.1.elim none fun a =>
          p.2.2.elim (some a) fun b => some (if a ≤ b + 1 then b + 1 else a)
      else
        p.2.2.elim p.2.1 fun b =>
          p.2.1.elim (some (b + 1)) fun a => some (if a ≤ b + 1 then a else b + 1) := by
    funext ⟨m, c₁, c₂⟩
    cases m <;> cases c₁ <;> cases c₂ <;> simp [combineCell, Nat.max_def, Nat.min_def]
  rw [heq]
  refine ite' (fst encBool encSubsetDPCell) ?_ ?_
  · refine optionElimWithInput (fst _ _ |>.comp (snd encBool encSubsetDPCell)) (const none) ?_
    refine optionElimWithInput
      (snd _ _ |>.comp (snd encBool encSubsetDPCell |>.comp (fst _ _)))
      ((optionSome encNat).comp (snd _ _)) ?_
    have ha : ComputableInPolyTime (fun q : ((Bool × SubsetDPCell) × ℕ) × ℕ => q.1.2)
        (encPair (encPair (encPair encBool encSubsetDPCell) encNat) encNat) encNat := by fun_prop
    have hb1 : ComputableInPolyTime (fun q : ((Bool × SubsetDPCell) × ℕ) × ℕ => q.2 + 1)
        (encPair (encPair (encPair encBool encSubsetDPCell) encNat) encNat) encNat := by fun_prop
    exact (optionSome encNat).comp ((binary_le' ha hb1).ite_decide hb1 ha)
  · refine optionElimWithInput (snd _ _ |>.comp (snd encBool encSubsetDPCell))
      (fst _ _ |>.comp (snd encBool encSubsetDPCell)) ?_
    refine optionElimWithInput
      (fst _ _ |>.comp (snd encBool encSubsetDPCell |>.comp (fst _ _)))
      ((optionSome encNat).comp (by fun_prop :
        ComputableInPolyTime (fun q : (Bool × SubsetDPCell) × ℕ => q.2 + 1) _ encNat)) ?_
    have ha : ComputableInPolyTime (fun q : ((Bool × SubsetDPCell) × ℕ) × ℕ => q.2)
        (encPair (encPair (encPair encBool encSubsetDPCell) encNat) encNat) encNat := by fun_prop
    have hb1 : ComputableInPolyTime (fun q : ((Bool × SubsetDPCell) × ℕ) × ℕ => q.1.2 + 1)
        (encPair (encPair (encPair encBool encSubsetDPCell) encNat) encNat) encNat := by fun_prop
    exact (optionSome encNat).comp ((binary_le' ha hb1).ite_decide ha hb1)

open ComputableInPolyTime in
private theorem computableInPolyTime_finalizeCell :
    ComputableInPolyTime
      (fun p : (Bool × Bool) × SubsetDPCell => finalizeCell p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encBool encBool) encSubsetDPCell) encSubsetDPCell := by
  unfold finalizeCell
  have hcomb : ComputableInPolyTime
      (fun p : (Bool × Bool) × SubsetDPCell => combineCell p.1.1 p.2.1 p.2.2)
      (encPair (encPair encBool encBool) encSubsetDPCell) (encOption encNat) :=
    computableInPolyTime_combineCell.comp
      ((fst _ _ |>.comp (fst _ _)).prod (snd _ _))
  exact ite' (snd _ _ |>.comp (fst _ _)) (hcomb.prod hcomb) (snd _ _)

open ComputableInPolyTime in
private theorem computableInPolyTime_evenCellMap :
    ComputableInPolyTime
      (fun p : SubsetDPFlags × SubsetDPCell => evenCellMap p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair encSubsetDPFlags encSubsetDPCell) encSubsetDPCell := by
  unfold evenCellMap
  have hc : ComputableInPolyTime
      (fun p : SubsetDPFlags × SubsetDPCell => (p.2.1, if p.1.2 then none else p.2.2))
      (encPair encSubsetDPFlags encSubsetDPCell) encSubsetDPCell :=
    (fst _ _ |>.comp (snd encSubsetDPFlags encSubsetDPCell)).prod
      (ite' (snd _ _ |>.comp (fst encSubsetDPFlags encSubsetDPCell)) (const none)
        (snd _ _ |>.comp (snd encSubsetDPFlags encSubsetDPCell)))
  exact computableInPolyTime_finalizeCell.comp
    ((fst _ _ |>.comp (fst encSubsetDPFlags encSubsetDPCell)).prod hc)

open ComputableInPolyTime in
private theorem computableInPolyTime_oddCellMap :
    ComputableInPolyTime
      (fun p : (SubsetDPFlags × SubsetDPCell) × SubsetDPCell =>
        oddCellMap p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair encSubsetDPFlags encSubsetDPCell) encSubsetDPCell) encSubsetDPCell := by
  unfold oddCellMap
  have hc : ComputableInPolyTime
      (fun p : (SubsetDPFlags × SubsetDPCell) × SubsetDPCell =>
        (p.2.1, if p.1.1.2 then p.1.2.2 else p.2.2))
      (encPair (encPair encSubsetDPFlags encSubsetDPCell) encSubsetDPCell) encSubsetDPCell :=
    (fst _ _ |>.comp (snd _ encSubsetDPCell)).prod
      (ite' (snd _ _ |>.comp (fst _ _ |>.comp (fst _ encSubsetDPCell)))
        (snd _ _ |>.comp (snd _ encSubsetDPCell |>.comp (fst _ encSubsetDPCell)))
        (snd _ _ |>.comp (snd _ encSubsetDPCell)))
  exact computableInPolyTime_finalizeCell.comp
    ((fst _ _ |>.comp (fst _ _ |>.comp (fst _ encSubsetDPCell))).prod hc)

private def evensFrom : Bool → SubsetDPFlags → List SubsetDPCell → List SubsetDPCell
  | _, _, [] => []
  | b, fl, [a] => if b then [evenCellMap fl.1.1 fl.1.2 fl.2 a] else []
  | b, fl, a :: b' :: rest =>
    (if b then [evenCellMap fl.1.1 fl.1.2 fl.2 a] else [evenCellMap fl.1.1 fl.1.2 fl.2 b']) ++
      evensFrom b fl rest

private theorem evensFrom_true_eq (fl : SubsetDPFlags) (L : List SubsetDPCell) :
    evensFrom true fl L = evensMap (evenCellMap fl.1.1 fl.1.2 fl.2) L := by
  match L with
  | [] => rfl
  | [a] => simp [evensFrom, evensMap]
  | a :: b' :: rest => simp [evensFrom, evensMap, evensFrom_true_eq fl rest]

private theorem evensFrom_streamEmit (fl : SubsetDPFlags) (L : List SubsetDPCell) :
    ∀ b : Bool,
      encList encSubsetDPCell (evensFrom b fl L) =
        streamEmit (fun p : (SubsetDPFlags × Bool) × SubsetDPCell => (p.1.1, !p.1.2))
          (fun p => encList encSubsetDPCell
            (if p.1.2 then [evenCellMap p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2] else []))
          (fl, b) L := by
  match L with
  | [] => intro b; cases b <;> rfl
  | [a] => intro b; cases b <;> simp [evensFrom, streamEmit, encList_cons, encList_nil]
  | a :: b' :: rest =>
    intro b
    have ih := evensFrom_streamEmit fl rest b
    cases b <;> simpa [evensFrom, streamEmit, encList_cons, encList_nil] using ih

private theorem streamState_evens_len (fl : SubsetDPFlags) (b : Bool)
    (L : List SubsetDPCell) (j : ℕ) :
    (encPair encSubsetDPFlags encBool
      (streamState (fl, b)
        (fun p : (SubsetDPFlags × Bool) × SubsetDPCell => (p.1.1, !p.1.2)) L j)).length ≤ 32 := by
  rcases streamState (fl, b)
    (fun p : (SubsetDPFlags × Bool) × SubsetDPCell => (p.1.1, !p.1.2)) L j with
    ⟨⟨⟨m₁, m₂⟩, m₃⟩, b'⟩
  simp [encSubsetDPFlags]

open ComputableInPolyTime in
private theorem computableInO_evensMap :
    ∃ d, ComputableInO
      (fun p : SubsetDPFlags × List SubsetDPCell =>
        evensMap (evenCellMap p.1.1.1 p.1.1.2 p.1.2) p.2)
      (encPair encSubsetDPFlags (encList encSubsetDPCell)) (encList encSubsetDPCell)
      (fun p => (encList encSubsetDPCell p.2).length +
        (p.2.length + 1) * (listMax (fun c => (encSubsetDPCell c).length) p.2 + 32) ^ d)
      (fun p => (encList encSubsetDPCell p.2).length +
        (p.2.length + 1) * (listMax (fun c => (encSubsetDPCell c).length) p.2 + 32) ^ d) := by
  let encSt := encPair encSubsetDPFlags encBool
  have hnext : ComputableInPolyTime
      (fun p : (SubsetDPFlags × Bool) × SubsetDPCell => (p.1.1, !p.1.2))
      (encPair encSt encSubsetDPCell) encSt := by
    unfold encSt; fun_prop
  have hemit : ComputableInPolyTime
      (fun p : (SubsetDPFlags × Bool) × SubsetDPCell =>
        if p.1.2 then [evenCellMap p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2] else [])
      (encPair encSt encSubsetDPCell) (encList encSubsetDPCell) := by
    unfold encSt
    exact ite' (snd _ _ |>.comp (fst _ encSubsetDPCell))
      ((computableInPolyTime_evenCellMap.comp
        ((fst _ _ |>.comp (fst _ encSubsetDPCell)).prod (snd _ encSubsetDPCell))).cons' (const []))
      (const [])
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encSubsetDPCell) (encS := encSt) (encB := encSubsetDPCell)
    (encIn := encPair encSt (encList encSubsetDPCell))
    (init := Prod.fst) (elems := Prod.snd)
    (fun _ => rfl) hnext hemit
    (g := fun q : (SubsetDPFlags × Bool) × List SubsetDPCell => evensFrom q.1.2 q.1.1 q.2)
    (fun q => evensFrom_streamEmit q.1.1 q.2 q.1.2)
    (lMax := fun q => listMax (fun r => (encSubsetDPCell r).length) q.2 + 32)
    (fun q j _ => (streamState_evens_len q.1.1 q.1.2 q.2 j).trans (Nat.le_add_left 32 _))
    (fun q j hj => (le_listMax (f := fun r => (encSubsetDPCell r).length)
      (List.getElem_mem hj)).trans (Nat.le_add_right _ 32))
  have hwrap : ComputableInO (fun p : SubsetDPFlags × List SubsetDPCell => ((p.1, true), p.2))
      (encPair encSubsetDPFlags (encList encSubsetDPCell))
      (encPair encSt (encList encSubsetDPCell))
      (fun p => (encList encSubsetDPCell p.2).length + 32)
      (fun p => (encList encSubsetDPCell p.2).length + 32) := by
    have hp := ((ComputableInO.fst encSubsetDPFlags (encList encSubsetDPCell)).prod
      (ComputableInO.const (encIn := encPair encSubsetDPFlags (encList encSubsetDPCell))
        (encMid := encBool) true)).prod
      (ComputableInO.snd encSubsetDPFlags (encList encSubsetDPCell))
    refine hp.mono 4 (fun p => ?_) (fun p => ?_)
    all_goals
      rcases p.1 with ⟨⟨m₁, m₂⟩, m₃⟩
      simp only [encSubsetDPFlags, length_encPair, encBool_apply, List.length_singleton]
      omega
  have haux : ComputableInO
      (fun q : (SubsetDPFlags × Bool) × List SubsetDPCell => evensFrom q.1.2 q.1.1 q.2)
      (encPair encSt (encList encSubsetDPCell)) (encList encSubsetDPCell)
      (fun q => (encList encSubsetDPCell q.2).length +
        (q.2.length + 1) * (listMax (fun r => (encSubsetDPCell r).length) q.2 + 32) ^ d)
      (fun q => (encList encSubsetDPCell q.2).length +
        (q.2.length + 1) * (listMax (fun r => (encSubsetDPCell r).length) q.2 + 32) ^ d) := by
    have hpow (L : List SubsetDPCell) :
        (listMax (fun r => (encSubsetDPCell r).length) L + 32 + 1) ^ d ≤
          2 ^ d * (listMax (fun r => (encSubsetDPCell r).length) L + 32) ^ d :=
      (Nat.pow_le_pow_left (by omega) d).trans_eq (Nat.mul_pow _ _ _)
    refine computableInO_of_bigO h ?hT
      (.const_mul c (.add ⟨2 ^ d, fun q =>
        (hpow q.2).trans (Nat.mul_le_mul_left (2 ^ d)
          ((Nat.le_mul_of_pos_left _ (show 0 < q.2.length + 1 by omega)).trans
            (by dsimp only; omega)))⟩ (.const 1 _)))
      ((BigOLe.of_le h.length_le).trans ?hT)
    refine .const_mul c (.add (.add (.of_le_linear 4 64 fun q => ?_)
      ⟨2 ^ d, fun q => ?_⟩) (.const 1 _))
    · rcases q.1 with ⟨⟨⟨m₁, m₂⟩, m₃⟩, b⟩
      simp only [encSt, encSubsetDPFlags, length_encPair, encBool_apply, List.length_singleton]
      omega
    · refine (Nat.mul_le_mul_left _ (hpow q.2)).trans ?_
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_left _ (by dsimp only; omega)
  have heq : ((fun q : (SubsetDPFlags × Bool) × List SubsetDPCell => evensFrom q.1.2 q.1.1 q.2) ∘
      fun p : SubsetDPFlags × List SubsetDPCell => ((p.1, true), p.2)) =
      fun p => evensMap (evenCellMap p.1.1.1 p.1.1.2 p.1.2) p.2 :=
    funext fun p => evensFrom_true_eq p.1 p.2
  refine ⟨d + 1, heq ▸ (haux.comp hwrap).mono 6 (fun p => ?_) (fun p => ?_)⟩
  all_goals
    dsimp only
    set M := listMax (fun r => (encSubsetDPCell r).length) p.2 + 32
    have hM32 : 32 ≤ M := Nat.le_add_left 32 _
    have hpow_le : M ^ d ≤ M ^ (d + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ d)
    have hpow_32 : 32 ≤ M ^ (d + 1) :=
      hM32.trans (Nat.le_self_pow (Nat.succ_ne_zero d) M)
    have hmul_le := Nat.mul_le_mul_left (p.2.length + 1) hpow_le
    have h32_prod : 32 ≤ (p.2.length + 1) * M ^ (d + 1) :=
      hpow_32.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    nlinarith

private abbrev OddState := SubsetDPFlags × Option SubsetDPCell

private abbrev encOddState : OddState ↪ List Bool :=
  encPair encSubsetDPFlags (encOption encSubsetDPCell)

private def oddNext (q : OddState × SubsetDPCell) : OddState :=
  (q.1.1, match q.1.2 with | none => some q.2 | some _ => none)

private def oddEmit (q : OddState × SubsetDPCell) : List SubsetDPCell :=
  match q.1.2 with
  | none => []
  | some c₀ => [oddCellMap q.1.1.1.1 q.1.1.1.2 q.1.1.2 c₀ q.2]

private def passOddsFrom : Option SubsetDPCell → SubsetDPFlags → List SubsetDPCell →
    List SubsetDPCell
  | none, _, [] => []
  | none, _, [_] => []
  | none, fl, a :: b :: rest =>
      oddCellMap fl.1.1 fl.1.2 fl.2 a b :: passOddsFrom none fl rest
  | some _, _, [] => []
  | some a, fl, b :: rest =>
      oddCellMap fl.1.1 fl.1.2 fl.2 a b :: passOddsFrom none fl rest

private theorem passOddsFrom_none_eq (fl : SubsetDPFlags) (L : List SubsetDPCell) :
    passOddsFrom none fl L = passOddsMap (oddCellMap fl.1.1 fl.1.2 fl.2) L := by
  match L with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => simp [passOddsFrom, passOddsMap, passOddsFrom_none_eq fl rest]

private theorem passOddsFrom_streamEmit (o : Option SubsetDPCell) (fl : SubsetDPFlags)
    (L : List SubsetDPCell) :
    encList encSubsetDPCell (passOddsFrom o fl L) =
      streamEmit oddNext (fun q => encList encSubsetDPCell (oddEmit q)) (fl, o) L := by
  match o, L with
  | none, [] => rfl
  | none, [a] => simp [passOddsFrom, streamEmit, oddEmit]
  | none, a :: b :: rest =>
    rw [passOddsFrom, streamEmit, oddNext, oddEmit]
    simp only [encList_nil, List.nil_append, streamEmit, oddNext, oddEmit, encList_cons,
      List.append_nil]
    exact congrArg _ (passOddsFrom_streamEmit none fl rest)
  | some c₀, [] => rfl
  | some c₀, a :: rest =>
    rw [passOddsFrom, streamEmit, oddNext, oddEmit]
    simp only [encList_cons, encList_nil, List.append_nil]
    exact congrArg _ (passOddsFrom_streamEmit none fl rest)

private theorem streamState_oddNext_mem (L : List SubsetDPCell) (j : ℕ) (fl : SubsetDPFlags)
    (o : Option SubsetDPCell) :
    (streamState (fl, o) oddNext L j).1 = fl ∧
      ((streamState (fl, o) oddNext L j).2 = none ∨
        (streamState (fl, o) oddNext L j).2 = o ∨
        ∃ r ∈ L, (streamState (fl, o) oddNext L j).2 = some r) := by
  have htake : ∀ xs : List SubsetDPCell, xs ⊆ L → ∀ s : Option SubsetDPCell,
      (xs.foldl (fun st r => oddNext (st, r)) (fl, s)).1 = fl ∧
        ((xs.foldl (fun st r => oddNext (st, r)) (fl, s)).2 = none ∨
          (xs.foldl (fun st r => oddNext (st, r)) (fl, s)).2 = s ∨
          ∃ r ∈ L, (xs.foldl (fun st r => oddNext (st, r)) (fl, s)).2 = some r) := by
    intro xs hsub s
    induction xs generalizing s with
    | nil => exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    | cons a xs ih =>
      simp only [List.foldl_cons, oddNext]
      have ha : a ∈ L := hsub List.mem_cons_self
      have hsub' : xs ⊆ L := fun z hz => hsub (List.mem_cons_of_mem _ hz)
      cases s with
      | none =>
        obtain ⟨h1, h2⟩ := ih hsub' (some a)
        exact ⟨h1, h2.imp_right fun h => h.elim (fun h => Or.inr ⟨a, ha, h⟩) Or.inr⟩
      | some _ =>
        obtain ⟨h1, h2⟩ := ih hsub' none
        exact ⟨h1, h2.elim Or.inl fun h => h.elim Or.inl (Or.inr ∘ Or.inr)⟩
  exact htake (L.take j) (List.take_subset j L) o

open ComputableInPolyTime in
private theorem computableInO_passOddsMap :
    ∃ d, ComputableInO
      (fun p : SubsetDPFlags × List SubsetDPCell =>
        passOddsMap (oddCellMap p.1.1.1 p.1.1.2 p.1.2) p.2)
      (encPair encSubsetDPFlags (encList encSubsetDPCell)) (encList encSubsetDPCell)
      (fun p => (encList encSubsetDPCell p.2).length +
        (p.2.length + 1) * (listMax (fun c => (encSubsetDPCell c).length) p.2 + 32) ^ d)
      (fun p => (encList encSubsetDPCell p.2).length +
        (p.2.length + 1) * (listMax (fun c => (encSubsetDPCell c).length) p.2 + 32) ^ d) := by
  have hnext : ComputableInPolyTime oddNext
      (encPair encOddState encSubsetDPCell) encOddState := by
    have heq : oddNext = fun q => (q.1.1, q.1.2.elim (some q.2) (fun _ => none)) := by
      funext ⟨⟨_, o⟩, _⟩; cases o <;> rfl
    rw [heq]
    refine ((fst encSubsetDPFlags (encOption encSubsetDPCell)).comp
      (fst encOddState encSubsetDPCell)).prod ?_
    exact optionElimWithInput
      ((snd encSubsetDPFlags (encOption encSubsetDPCell)).comp (fst encOddState encSubsetDPCell))
      ((optionSome encSubsetDPCell).comp (snd encOddState encSubsetDPCell))
      (const (encIn := encPair (encPair encOddState encSubsetDPCell) encSubsetDPCell)
        (encOut := encOption encSubsetDPCell) none)
  have hemit : ComputableInPolyTime oddEmit
      (encPair encOddState encSubsetDPCell) (encList encSubsetDPCell) := by
    have heq : oddEmit = fun q =>
        q.1.2.elim [] (fun c₀ => [oddCellMap q.1.1.1.1 q.1.1.1.2 q.1.1.2 c₀ q.2]) := by
      funext ⟨⟨_, o⟩, _⟩; cases o <;> rfl
    rw [heq]
    refine optionElimWithInput
      ((snd encSubsetDPFlags (encOption encSubsetDPCell)).comp (fst encOddState encSubsetDPCell))
      (const (encIn := encPair encOddState encSubsetDPCell)
        (encOut := encList encSubsetDPCell) []) ?_
    have hfl : ComputableInPolyTime
        (fun q : (OddState × SubsetDPCell) × SubsetDPCell => q.1.1.1)
        (encPair (encPair encOddState encSubsetDPCell) encSubsetDPCell) encSubsetDPFlags := by
      unfold encOddState; fun_prop
    have hc₀ : ComputableInPolyTime
        (fun q : (OddState × SubsetDPCell) × SubsetDPCell => q.2)
        (encPair (encPair encOddState encSubsetDPCell) encSubsetDPCell) encSubsetDPCell := by
      fun_prop
    have hc₁ : ComputableInPolyTime
        (fun q : (OddState × SubsetDPCell) × SubsetDPCell => q.1.2)
        (encPair (encPair encOddState encSubsetDPCell) encSubsetDPCell) encSubsetDPCell := by
      fun_prop
    exact (computableInPolyTime_oddCellMap.comp ((hfl.prod hc₀).prod hc₁)).cons'
      (const (encIn := encPair (encPair encOddState encSubsetDPCell) encSubsetDPCell)
        (encOut := encList encSubsetDPCell) [])
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encSubsetDPCell) (encS := encOddState) (encB := encSubsetDPCell)
    (encIn := encPair encOddState (encList encSubsetDPCell))
    (init := Prod.fst) (elems := Prod.snd)
    (fun _ => rfl) hnext hemit
    (g := fun q : OddState × List SubsetDPCell => passOddsFrom q.1.2 q.1.1 q.2)
    (fun q => passOddsFrom_streamEmit q.1.2 q.1.1 q.2)
    (lMax := fun q => 2 * (encOption encSubsetDPCell q.1.2).length +
      listMax (fun r => (encSubsetDPCell r).length) q.2 + 32)
    (fun q j _ => by
      obtain ⟨h1, h2⟩ := streamState_oddNext_mem q.2 j q.1.1 q.1.2
      rw [encOddState, length_encPair, h1]
      have hfl_len : (encSubsetDPFlags q.1.1).length ≤ 12 := by
        rcases q.1.1 with ⟨⟨m₁, m₂⟩, m₃⟩
        simp [encSubsetDPFlags]
      rcases h2 with h2 | h2 | ⟨r, hr, h2⟩
      · rw [h2]; simp
      · rw [h2]; omega
      · rw [h2, encOption_some, List.length_cons]
        have := le_listMax (f := fun r => (encSubsetDPCell r).length) hr
        omega)
    (fun q j hj => (le_listMax (f := fun r => (encSubsetDPCell r).length)
      (List.getElem_mem hj)).trans (by omega))
  have hwrap : ComputableInO (fun p : SubsetDPFlags × List SubsetDPCell => ((p.1, none), p.2))
      (encPair encSubsetDPFlags (encList encSubsetDPCell))
      (encPair encOddState (encList encSubsetDPCell))
      (fun p => (encList encSubsetDPCell p.2).length + 32)
      (fun p => (encList encSubsetDPCell p.2).length + 32) := by
    have hp := ((ComputableInO.fst encSubsetDPFlags (encList encSubsetDPCell)).prod
      (ComputableInO.const (encIn := encPair encSubsetDPFlags (encList encSubsetDPCell))
        (encMid := encOption encSubsetDPCell) (none : Option SubsetDPCell))).prod
      (ComputableInO.snd encSubsetDPFlags (encList encSubsetDPCell))
    refine hp.mono 4 (fun p => ?_) (fun p => ?_)
    all_goals
      rcases p.1 with ⟨⟨m₁, m₂⟩, m₃⟩
      simp only [encSubsetDPFlags, length_encPair, encBool_apply, List.length_singleton]
      omega
  have haux : ComputableInO
      (fun q : OddState × List SubsetDPCell => passOddsFrom q.1.2 q.1.1 q.2)
      (encPair encOddState (encList encSubsetDPCell)) (encList encSubsetDPCell)
      (fun q => (encOption encSubsetDPCell q.1.2).length + (encList encSubsetDPCell q.2).length +
        (q.2.length + 1) * (listMax (fun r => (encSubsetDPCell r).length) q.2 +
          (encOption encSubsetDPCell q.1.2).length + 32) ^ d)
      (fun q => (encOption encSubsetDPCell q.1.2).length + (encList encSubsetDPCell q.2).length +
        (q.2.length + 1) * (listMax (fun r => (encSubsetDPCell r).length) q.2 +
          (encOption encSubsetDPCell q.1.2).length + 32) ^ d) := by
    have hpow (q : OddState × List SubsetDPCell) :
        (2 * (encOption encSubsetDPCell q.1.2).length +
            listMax (fun r => (encSubsetDPCell r).length) q.2 + 32 + 1) ^ d ≤
          3 ^ d * (listMax (fun r => (encSubsetDPCell r).length) q.2 +
            (encOption encSubsetDPCell q.1.2).length + 32) ^ d :=
      (Nat.pow_le_pow_left (by omega) d).trans_eq (Nat.mul_pow _ _ _)
    refine computableInO_of_bigO h ?hT
      (.const_mul c (.add ⟨3 ^ d, fun q =>
        (hpow q).trans (Nat.mul_le_mul_left (3 ^ d)
          ((Nat.le_mul_of_pos_left _ (show 0 < q.2.length + 1 by omega)).trans
            (by dsimp only; omega)))⟩ (.const 1 _)))
      ((BigOLe.of_le h.length_le).trans ?hT)
    refine .const_mul c (.add (.add (.of_le_linear 4 64 fun q => ?_)
      ⟨3 ^ d, fun q => ?_⟩) (.const 1 _))
    · rcases q.1.1 with ⟨⟨m₁, m₂⟩, m₃⟩
      simp only [encOddState, encSubsetDPFlags, length_encPair, encBool_apply,
        List.length_singleton]
      omega
    · refine (Nat.mul_le_mul_left _ (hpow q)).trans ?_
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_left _ (by dsimp only; omega)
  have heq : ((fun q : OddState × List SubsetDPCell => passOddsFrom q.1.2 q.1.1 q.2) ∘
      fun p : SubsetDPFlags × List SubsetDPCell => ((p.1, none), p.2)) =
      fun p => passOddsMap (oddCellMap p.1.1.1 p.1.1.2 p.1.2) p.2 :=
    funext fun p => passOddsFrom_none_eq p.1 p.2
  refine ⟨d + 1, heq ▸ (haux.comp hwrap).mono 6 (fun p => ?_) (fun p => ?_)⟩
  all_goals
    dsimp only
    simp only [encOption_none, List.length_nil, zero_add, add_zero]
    set M := listMax (fun r => (encSubsetDPCell r).length) p.2 + 32
    have hM32 : 32 ≤ M := Nat.le_add_left 32 _
    have hpow_le : M ^ d ≤ M ^ (d + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ d)
    have hpow_32 : 32 ≤ M ^ (d + 1) :=
      hM32.trans (Nat.le_self_pow (Nat.succ_ne_zero d) M)
    have hmul_le := Nat.mul_le_mul_left (p.2.length + 1) hpow_le
    have h32_prod : 32 ≤ (p.2.length + 1) * M ^ (d + 1) :=
      hpow_32.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    nlinarith

/-- **Streaming multi-tape `ComputableInO` bound for `butterflyPass`**: runs in time and space
linear in `(encList encSubsetDPCell L).length + (L.length + 1) * (maxCellLen + 32)^d`. -/
theorem computableInO_butterflyPass :
    ∃ d, ComputableInO
      (fun p : SubsetDPFlags × List SubsetDPCell => butterflyPass p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair encSubsetDPFlags (encList encSubsetDPCell)) (encList encSubsetDPCell)
      (fun p => (encList encSubsetDPCell p.2).length +
        (p.2.length + 1) * (listMax (fun c => (encSubsetDPCell c).length) p.2 + 32) ^ d)
      (fun p => (encList encSubsetDPCell p.2).length +
        (p.2.length + 1) * (listMax (fun c => (encSubsetDPCell c).length) p.2 + 32) ^ d) := by
  obtain ⟨de, hev⟩ := computableInO_evensMap
  obtain ⟨do_, hodds⟩ := computableInO_passOddsMap
  let d := max de do_ + 1
  refine ⟨d, (ComputableInO.listAppend' hev hodds).mono 4 (fun p => ?_) (fun p => ?_)⟩
  all_goals
    set M := listMax (fun c => (encSubsetDPCell c).length) p.2 + 32
    have hM1 : 1 ≤ M := by dsimp [M]; omega
    have hde : (p.2.length + 1) * M ^ de ≤ (p.2.length + 1) * M ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM1 (by dsimp [d]; omega))
    have hdo : (p.2.length + 1) * M ^ do_ ≤ (p.2.length + 1) * M ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM1 (by dsimp [d]; omega))
    omega

private theorem foldl_last_eq_or_mem (xs : List SubsetDPCell) (acc : SubsetDPCell) :
    xs.foldl (fun _ r => r) acc = acc ∨ xs.foldl (fun _ r => r) acc ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    rcases ih a with h | h
    · exact Or.inr (by rw [h]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem length_encCell_foldl_take_le (L : List SubsetDPCell) (acc : SubsetDPCell)
    (k : ℕ) :
    (encSubsetDPCell ((L.take k).foldl (fun _ r => r) acc)).length ≤
      listMax (fun r => (encSubsetDPCell r).length) L + (encSubsetDPCell acc).length + 4 := by
  rcases foldl_last_eq_or_mem (L.take k) acc with h | h
  · rw [h]; omega
  · have := le_listMax (f := fun r => (encSubsetDPCell r).length) (List.take_subset k L h)
    omega

/-- **Streaming multi-tape `ComputableInO` bound for extracting the final cell** of a `SubsetDPCell`
table. -/
theorem computableInO_lastSubsetCell :
    ComputableInO (fun L : List SubsetDPCell => L.foldl (fun _ r => r) (none, none))
      (encList encSubsetDPCell) encSubsetDPCell
      (fun L => (encList encSubsetDPCell L).length +
        (L.length + 1) * (listMax (fun r => (encSubsetDPCell r).length) L + 5))
      (fun L => (encList encSubsetDPCell L).length +
        listMax (fun r => (encSubsetDPCell r).length) L + 5) := by
  obtain ⟨cnext, hnext⟩ := Internal.NormalForm.linear
    (PairEncoding.snd (enc₁ := encSubsetDPCell) (enc₂ := encSubsetDPCell)
      (enc := encPair encSubsetDPCell encSubsetDPCell))
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair encSubsetDPCell encSubsetDPCell) (encOut := encUnit) ()
  obtain ⟨c, hc⟩ := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun p : SubsetDPCell × List SubsetDPCell => p.2.foldl (fun _ r => r) p.1)
    (encIn := encPair encSubsetDPCell (encList encSubsetDPCell)) (encOut := encSubsetDPCell)
    (encA := encSubsetDPCell) (encS := encSubsetDPCell) (encE := encUnit) (encF := encSubsetDPCell)
    Internal.NativeCompiler.frameValueReader
    (fun r => frame (encSubsetDPCell r)) (fun r => frame_ne_nil (encSubsetDPCell r))
    (fun r rest => Internal.NativeCompiler.read_frameValueReader (encSubsetDPCell r) rest)
    Prod.fst Prod.snd
    (fun p => by
      have hfl : ∀ xs : List SubsetDPCell,
          encList encSubsetDPCell xs = xs.flatMap (fun r => frame (encSubsetDPCell r)) := by
        intro xs
        induction xs with
        | nil => simp
        | cons a as ih => simp [encList_cons, ih]
      simp [encPair_apply, hfl p.2])
    hnext he.computableTidilyInTimeAndSpace computableTidilyInTimeAndSpace_id
    (fun p => by simp [streamState, encSubsetDPCell])
    (roundCost := fun p _ =>
      (3 * cnext + 2 * ce + 6) *
        (listMax (fun r => (encSubsetDPCell r).length) p.2 + (encSubsetDPCell p.1).length + 5))
    (sMax := fun p =>
      cnext * (3 * (listMax (fun r => (encSubsetDPCell r).length) p.2 +
        (encSubsetDPCell p.1).length + 5)))
    (lMax := fun p => listMax (fun r => (encSubsetDPCell r).length) p.2 +
      (encSubsetDPCell p.1).length + 4)
    (fun p j hj => by
      have h0 := length_encCell_foldl_take_le p.2 p.1 j
      have h1 := length_encCell_foldl_take_le p.2 p.1 (j + 1)
      have ha := le_listMax (f := fun r => (encSubsetDPCell r).length) (List.getElem_mem hj)
      have hpair_j :
          (encPair encSubsetDPCell encSubsetDPCell
            (streamState p.1 Prod.snd p.2 j, p.2[j])).length + 1 ≤
          3 * (listMax (fun r => (encSubsetDPCell r).length) p.2 +
            (encSubsetDPCell p.1).length + 5) := by
        rw [length_encPair]; simp only [streamState] at h0 ⊢; omega
      have hl := Nat.mul_le_mul_left cnext hpair_j
      simp only [streamState] at h0 h1 hl ⊢
      nlinarith)
    (fun p j hj => by
      have h0 := length_encCell_foldl_take_le p.2 p.1 j
      have ha := le_listMax (f := fun r => (encSubsetDPCell r).length) (List.getElem_mem hj)
      have hpair_j :
          (encPair encSubsetDPCell encSubsetDPCell
            (streamState p.1 Prod.snd p.2 j, p.2[j])).length + 1 ≤
          3 * (listMax (fun r => (encSubsetDPCell r).length) p.2 +
            (encSubsetDPCell p.1).length + 5) := by
        rw [length_encPair]; simp only [streamState] at h0 ⊢; omega
      exact (Nat.add_zero _).trans_le (Nat.mul_le_mul_left _ hpair_j))
    (fun p j _ => by simpa [streamState] using length_encCell_foldl_take_le p.2 p.1 j)
    (fun p j hj => (le_listMax (f := fun r => (encSubsetDPCell r).length)
      (List.getElem_mem hj)).trans (by omega))
  have hwrap : ComputableInO (fun L : List SubsetDPCell => (((none, none) : SubsetDPCell), L))
      (encList encSubsetDPCell) (encPair encSubsetDPCell (encList encSubsetDPCell))
      (fun L => (encList encSubsetDPCell L).length + 8)
      (fun L => (encList encSubsetDPCell L).length + 8) := by
    have hp := (ComputableInO.const (encIn := encList encSubsetDPCell)
      (encMid := encSubsetDPCell) ((none, none) : SubsetDPCell)).prod
      (ComputableInO.id' (encMid := encList encSubsetDPCell))
    refine hp.mono 4 (fun _ => ?_) (fun _ => ?_)
    all_goals simp [encSubsetDPCell]; omega
  have hpair : ComputableInO
      (fun p : SubsetDPCell × List SubsetDPCell => p.2.foldl (fun _ r => r) p.1)
      (encPair encSubsetDPCell (encList encSubsetDPCell)) encSubsetDPCell
      (fun p => (encPair encSubsetDPCell (encList encSubsetDPCell) p).length +
        (p.2.length + 1) * (listMax (fun r => (encSubsetDPCell r).length) p.2 +
          (encSubsetDPCell p.1).length + 5))
      (fun p => listMax (fun r => (encSubsetDPCell r).length) p.2 +
        (encSubsetDPCell p.1).length + 5) := by
    have hf (p : SubsetDPCell × List SubsetDPCell) :
        (encSubsetDPCell (p.2.foldl (fun _ r => r) p.1)).length ≤
          listMax (fun r => (encSubsetDPCell r).length) p.2 + (encSubsetDPCell p.1).length + 4 := by
      simpa using length_encCell_foldl_take_le p.2 p.1 p.2.length
    refine computableInO_of_bigO hc.computableInTimeAndSpace
      (.const_mul c (.of_le_linear (3 * cnext + 2 * ce + 10) 10 fun p => ?_))
      (.const_mul c (.of_le_linear (3 * cnext + 2) (3 * cnext + 2) fun p => by nlinarith))
      (.of_le fun p => (hf p).trans (Nat.le_succ _))
    have := hf p
    simp only [streamState, List.take_length, Finset.sum_const, Finset.card_range, smul_eq_mul]
    nlinarith
  refine ((hpair.comp hwrap).mono 8 (fun L => ?_) (fun L => ?_))
  all_goals
    dsimp only
    simp only [length_encPair, encSubsetDPCell, encOption_none, List.length_nil]
    nlinarith

end CslibFrontier.ParameterizedComplexity
