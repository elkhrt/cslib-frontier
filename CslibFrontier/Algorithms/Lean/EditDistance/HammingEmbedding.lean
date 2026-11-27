/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.EditDistance.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.InformationTheory.Hamming

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Exact Isometric Embedding of Hamming Space into Edit-Distance Space

This module proves basic metric axioms for unit-cost Levenshtein edit distance
(`Cslib.Algorithms.Lean.EditDistance.editDist Costs.unit`) and constructs an explicit
zero-distortion isometric embedding of any fixed-length Hamming cube `(Σ^d, Δ)` into the
edit-distance space `(Σ^{d(d+1)}, ED)`.

Given any alphabet `α` with a distinguished separator symbol `sep : α`, padding each symbol
of a length-`d` word `x` with `d` trailing copies of `sep` produces a word of length
`d * (d + 1)` whose active positions `i * (d + 1)` are spaced `d + 1` apart. Any edit script
of cost at most `d` shifts coordinates by at most `d` positions, preventing any non-separator
symbol at active position `i * (d + 1)` from matching a different active position
`j * (d + 1)`. Every mismatching coordinate `x_i ≠ y_i` therefore incurs its own distinct
unit-cost operation, yielding the exact identity `ED(f(x), f(y)) = Δ(x, y)`.

## Main definitions

* `CslibFrontier.Algorithms.Lean.EditDistance.listHammingDist`: Hamming distance between
  equal-length lists over `α`.
* `CslibFrontier.Algorithms.Lean.EditDistance.padEditEmbed`: separator-padded embedding
  `List α → List α` of output length `d * (d + 1)` for inputs of length `d`.
* `CslibFrontier.Algorithms.Lean.EditDistance.padEditEmbedFin`: typed `Fin d → α` specialization
  of `padEditEmbed`.

## Main results

* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_self`,
  `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_eq_zero_iff`,
  `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_comm`,
  `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_triangle`: metric axioms for unit-cost
  edit distance.
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_padEditEmbed_eq`: exact isometry
  `editDist Costs.unit (padEditEmbed sep x) (padEditEmbed sep y) = listHammingDist x y` for all
  lists `x, y : List α` with `x.length = y.length`.
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_padEditEmbedFin_eq_hammingDist`: exact
  isometry into `hammingDist` on `Fin d → α`.
* `CslibFrontier.Algorithms.Lean.EditDistance.padEditEmbed_injective`: injectivity of
  `padEditEmbed sep` on lists.
* `CslibFrontier.Algorithms.Lean.EditDistance.computableInPolyTime_padEditEmbed_bool`: multi-tape
  Turing machine polynomial-time computability of `padEditEmbed false` on bitstrings.
-/

public section

namespace CslibFrontier.Algorithms.Lean.EditDistance

open Cslib.Algorithms.Lean.EditDistance
open Turing.MultiTapeTM

section Metric

variable {α : Type*} [DecidableEq α]

/-- Reverse the direction of an edit operation by swapping deletions with insertions and
flipping substitutions. -/
private def revOp : EditOp α → EditOp α
  | .del a => .ins a
  | .ins b => .del b
  | .sub a b => .sub b a

omit [DecidableEq α] in
private lemma revOp_src (o : EditOp α) : (revOp o).src = o.tgt := by
  cases o <;> rfl

omit [DecidableEq α] in
private lemma revOp_tgt (o : EditOp α) : (revOp o).tgt = o.src := by
  cases o <;> rfl

private lemma revOp_cost (o : EditOp α) : (revOp o).cost Costs.unit = o.cost Costs.unit := by
  cases o with
  | del _ => rfl
  | ins _ => rfl
  | sub a b =>
    simp only [revOp, EditOp.cost, Costs.unit_sub]
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := Ne.symm h
      simp [h, h']

private lemma map_revOp_spec (s : EditScript α) :
    EditScript.src (s.map revOp) = EditScript.tgt s ∧
      EditScript.tgt (s.map revOp) = EditScript.src s ∧
      EditScript.cost Costs.unit (s.map revOp) = EditScript.cost Costs.unit s := by
  induction s with
  | nil => simp
  | cons o s ih =>
    simp only [List.map_cons, EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
      revOp_src, revOp_tgt, revOp_cost, ih.1, ih.2.1, ih.2.2, and_self]

/-- Unit-cost edit distance of any word to itself is zero. -/
@[simp]
theorem editDist_unit_self (x : List α) : editDist Costs.unit x x = 0 := by
  induction x with
  | nil => exact editDist_nil_nil Costs.unit
  | cons a x ih =>
    refine Nat.eq_zero_of_le_zero ?_
    calc
      editDist Costs.unit (a :: x) (a :: x) ≤
          (Costs.unit : Costs α).sub a a + editDist Costs.unit x x :=
        editDist_cons_cons_le Costs.unit a a x x
      _ = 0 := by simp [ih]

private lemma src_eq_tgt_of_cost_unit_zero :
    ∀ s : EditScript α, EditScript.cost Costs.unit s = 0 → EditScript.src s = EditScript.tgt s
  | [], _ => by simp
  | o :: s, h => by
    rw [EditScript.cost_cons] at h
    have ho : o.cost Costs.unit = 0 := by omega
    have hs : EditScript.cost Costs.unit s = 0 := by omega
    rw [EditScript.src_cons, EditScript.tgt_cons, src_eq_tgt_of_cost_unit_zero s hs]
    cases o with
    | del a => simp [EditOp.cost] at ho
    | ins b => simp [EditOp.cost] at ho
    | sub a b =>
      simp only [EditOp.cost, Costs.unit_sub, ite_eq_left_iff] at ho
      have hab : a = b := by
        by_contra hne
        exact absurd (ho hne) (by decide)
      subst hab
      rfl

/-- Unit-cost edit distance vanishes if and only if the two words are equal. -/
theorem editDist_unit_eq_zero_iff (x y : List α) :
    editDist Costs.unit x y = 0 ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ editDist_unit_self x⟩
  have hcost : EditScript.cost Costs.unit (optScript Costs.unit x y) = 0 := by
    rw [cost_optScript, h]
  have heq := src_eq_tgt_of_cost_unit_zero (optScript Costs.unit x y) hcost
  rwa [src_optScript, tgt_optScript] at heq

/-- Unit-cost edit distance is symmetric. -/
theorem editDist_unit_comm (x y : List α) :
    editDist Costs.unit x y = editDist Costs.unit y x := by
  have hle : ∀ u v : List α, editDist Costs.unit u v ≤ editDist Costs.unit v u := by
    intro u v
    let r : EditScript α := (optScript Costs.unit v u).map revOp
    obtain ⟨hsrc, htgt, hcost⟩ := map_revOp_spec (optScript Costs.unit v u)
    rw [tgt_optScript] at hsrc
    rw [src_optScript] at htgt
    rw [cost_optScript] at hcost
    calc
      editDist Costs.unit u v = editDist Costs.unit (EditScript.src r) (EditScript.tgt r) := by
        rw [hsrc, htgt]
      _ ≤ EditScript.cost Costs.unit r := editDist_le_cost Costs.unit r
      _ = editDist Costs.unit v u := hcost
  exact le_antisymm (hle x y) (hle y x)

private lemma editDist_unit_triangle_script :
    ∀ (s₁ s₂ : EditScript α), EditScript.tgt s₁ = EditScript.src s₂ →
      editDist Costs.unit (EditScript.src s₁) (EditScript.tgt s₂) ≤
        EditScript.cost Costs.unit s₁ + EditScript.cost Costs.unit s₂
  | [], s₂, h => by
    rw [EditScript.tgt_nil] at h
    simpa [← h] using editDist_le_cost Costs.unit s₂
  | .del a :: s₁, s₂, h => by
    simp only [EditScript.src_cons, EditOp.src, List.singleton_append,
      EditScript.tgt_cons, EditOp.tgt, List.nil_append, EditScript.cost_cons,
      EditOp.cost, Costs.unit_del] at h ⊢
    have ih := editDist_unit_triangle_script s₁ s₂ h
    have hstep := editDist_cons_left_le Costs.unit a (EditScript.src s₁) (EditScript.tgt s₂)
    simp only [Costs.unit_del] at hstep
    omega
  | s₁, .ins b :: s₂, h => by
    simp only [EditScript.src_cons, EditOp.src, List.nil_append,
      EditScript.tgt_cons, EditOp.tgt, List.singleton_append, EditScript.cost_cons,
      EditOp.cost, Costs.unit_ins] at h ⊢
    have ih := editDist_unit_triangle_script s₁ s₂ h
    have hstep := editDist_cons_right_le Costs.unit b (EditScript.src s₁) (EditScript.tgt s₂)
    simp only [Costs.unit_ins] at hstep
    omega
  | .ins b :: s₁, [], h => by
    simp [EditScript.tgt_cons, EditOp.tgt] at h
  | .sub a b :: s₁, [], h => by
    simp [EditScript.tgt_cons, EditOp.tgt] at h
  | .ins b :: s₁, .del b' :: s₂, h => by
    simp only [EditScript.src_cons, EditOp.src, List.nil_append, List.singleton_append,
      EditScript.tgt_cons, EditOp.tgt, EditScript.cost_cons, EditOp.cost,
      Costs.unit_ins, Costs.unit_del, List.cons.injEq] at h ⊢
    have ih := editDist_unit_triangle_script s₁ s₂ h.2
    omega
  | .ins b :: s₁, .sub b' c :: s₂, h => by
    simp only [EditScript.src_cons, EditOp.src, List.nil_append, List.singleton_append,
      EditScript.tgt_cons, EditOp.tgt, EditScript.cost_cons, EditOp.cost,
      Costs.unit_ins, Costs.unit_sub, List.cons.injEq] at h ⊢
    have ih := editDist_unit_triangle_script s₁ s₂ h.2
    have hstep := editDist_cons_right_le Costs.unit c (EditScript.src s₁) (EditScript.tgt s₂)
    simp only [Costs.unit_ins] at hstep
    omega
  | .sub a b :: s₁, .del b' :: s₂, h => by
    simp only [EditScript.src_cons, EditOp.src, List.singleton_append,
      EditScript.tgt_cons, EditOp.tgt, List.nil_append, EditScript.cost_cons,
      EditOp.cost, Costs.unit_sub, Costs.unit_del, List.cons.injEq] at h ⊢
    have ih := editDist_unit_triangle_script s₁ s₂ h.2
    have hstep := editDist_cons_left_le Costs.unit a (EditScript.src s₁) (EditScript.tgt s₂)
    simp only [Costs.unit_del] at hstep
    omega
  | .sub a b :: s₁, .sub b' c :: s₂, h => by
    simp only [EditScript.src_cons, EditOp.src, List.singleton_append,
      EditScript.tgt_cons, EditOp.tgt, EditScript.cost_cons, EditOp.cost,
      Costs.unit_sub, List.cons.injEq] at h ⊢
    obtain ⟨rfl, hs⟩ := h
    have ih := editDist_unit_triangle_script s₁ s₂ hs
    have hstep :=
      editDist_cons_cons_le Costs.unit a c (EditScript.src s₁) (EditScript.tgt s₂)
    simp only [Costs.unit_sub] at hstep
    by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c
    all_goals simp only [hab, hbc, hac, ↓reduceIte] at hstep ⊢; omega

/-- Unit-cost edit distance satisfies the triangle inequality. -/
theorem editDist_unit_triangle (x y z : List α) :
    editDist Costs.unit x z ≤ editDist Costs.unit x y + editDist Costs.unit y z := by
  have h := editDist_unit_triangle_script
    (optScript Costs.unit x y) (optScript Costs.unit y z)
    (by rw [tgt_optScript, src_optScript])
  rwa [src_optScript, tgt_optScript, cost_optScript, cost_optScript] at h

/-- Hamming distance between two lists, counting coordinatewise mismatches along their common
prefix. On equal-length lists this agrees with standard `hammingDist`. -/
@[expose]
def listHammingDist : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: xs, b :: ys => (if a = b then 0 else 1) + listHammingDist xs ys

/-- Hamming distance with the empty list on the left is zero. -/
@[simp]
theorem listHammingDist_nil_left (y : List α) : listHammingDist [] y = 0 := rfl

/-- Hamming distance with the empty list on the right is zero. -/
@[simp]
theorem listHammingDist_nil_right (x : List α) : listHammingDist x [] = 0 := by
  cases x <;> rfl

/-- Single-step recurrence for `listHammingDist` on non-empty lists. -/
@[simp]
theorem listHammingDist_cons_cons (a b : α) (xs ys : List α) :
    listHammingDist (a :: xs) (b :: ys) = (if a = b then 0 else 1) + listHammingDist xs ys :=
  rfl

/-- `listHammingDist` on `List.ofFn` agrees identically with Mathlib's `hammingDist`. -/
theorem listHammingDist_ofFn {d : ℕ} (x y : Fin d → α) :
    listHammingDist (List.ofFn x) (List.ofFn y) = hammingDist x y := by
  induction d with
  | zero => simp [hammingDist]
  | succ d ih =>
    rw [List.ofFn_succ, List.ofFn_succ, listHammingDist_cons_cons, ih]
    have huniv : (Finset.univ : Finset (Fin (d + 1))) =
        insert 0 (Finset.univ.map (Fin.succEmb d)) := by
      ext i; cases i using Fin.cases <;> simp
    have hrhs : hammingDist x y =
        ((insert (0 : Fin (d + 1)) (Finset.univ.map (Fin.succEmb d))).filter
          fun i ↦ x i ≠ y i).card := by
      change (Finset.univ.filter _).card = _; rw [huniv]
    rw [hrhs, Finset.filter_insert]
    have htail : ((Finset.univ.map (Fin.succEmb d)).filter fun i ↦ x i ≠ y i).card =
        hammingDist (fun i : Fin d ↦ x i.succ) (fun i : Fin d ↦ y i.succ) := by
      rw [Finset.filter_map, Finset.card_map]; rfl
    by_cases h : x 0 = y 0
    · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, zero_add, htail]
    · have hnot : (0 : Fin (d + 1)) ∉ (Finset.univ.map (Fin.succEmb d)).filter
          (fun i ↦ x i ≠ y i) := by simp
      simp only [h, ↓reduceIte, ne_eq, not_false_eq_true]
      rw [Finset.card_insert_of_notMem hnot, htail, Nat.add_comm]

/-- Equal-length lists have `listHammingDist` equal to the cardinality of mismatching indices. -/
theorem listHammingDist_eq_card_filter {d : ℕ} {x y : List α}
    (hx : x.length = d) (hy : y.length = d) :
    listHammingDist x y =
      ((Finset.univ : Finset (Fin d)).filter fun i ↦
        x[i.1]'(hx ▸ i.2) ≠ y[i.1]'(hy ▸ i.2)).card := by
  let fx : Fin d → α := fun i ↦ x[i.1]'(hx ▸ i.2)
  let fy : Fin d → α := fun i ↦ y[i.1]'(hy ▸ i.2)
  have hox : List.ofFn fx = x := List.ext_getElem (by simp [hx]) fun i _ _ ↦ by simp [fx]
  have hoy : List.ofFn fy = y := List.ext_getElem (by simp [hy]) fun i _ _ ↦ by simp [fy]
  calc
    listHammingDist x y = listHammingDist (List.ofFn fx) (List.ofFn fy) := by rw [hox, hoy]
    _ = hammingDist fx fy := listHammingDist_ofFn fx fy
    _ = _ := rfl

/-- Unit-cost edit distance is always at most `listHammingDist` on equal-length lists. -/
theorem editDist_unit_le_listHammingDist {x y : List α} (h : x.length = y.length) :
    editDist Costs.unit x y ≤ listHammingDist x y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simp
    | cons _ _ => simp at h
  | cons a xs ih =>
    cases y with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      calc
        editDist Costs.unit (a :: xs) (b :: ys) ≤
            (Costs.unit : Costs α).sub a b + editDist Costs.unit xs ys :=
          editDist_cons_cons_le Costs.unit a b xs ys
        _ ≤ (if a = b then 0 else 1) + listHammingDist xs ys :=
          Nat.add_le_add (by simp [Costs.unit_sub]) (ih h)

/-- `listHammingDist x y` is bounded by `x.length`. -/
theorem listHammingDist_le_length (x y : List α) : listHammingDist x y ≤ x.length := by
  induction x generalizing y with
  | nil => simp
  | cons a xs ih =>
    cases y with
    | nil => simp
    | cons b ys =>
      simp only [listHammingDist_cons_cons, List.length_cons]
      have := ih ys
      split_ifs <;> omega

/-- `listHammingDist` on equal-length lists vanishes iff the lists are equal. -/
theorem listHammingDist_eq_zero_iff {x y : List α} (h : x.length = y.length) :
    listHammingDist x y = 0 ↔ x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simp
    | cons _ _ => simp at h
  | cons a xs ih =>
    cases y with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [listHammingDist_cons_cons, Nat.add_eq_zero_iff, ih h, List.cons.injEq]
      split_ifs with hab <;> simp [hab]

end Metric

section Embedding

/-- Separator-padded block `a :: sep^k` for a single symbol `a` and stride `k`. -/
private def padWithStride {α : Type*} (sep : α) (k : ℕ) (x : List α) : List α :=
  x.flatMap fun a ↦ a :: List.replicate k sep

/-- Separator-padded embedding of a length-`d` word `x : List α` into a word of length
`d * (d + 1)`, inserting `d` copies of `sep` after each character of `x`. -/
def padEditEmbed {α : Type*} (sep : α) (x : List α) : List α :=
  padWithStride sep x.length x

/-- Typed `Fin d → α` version of `padEditEmbed`. -/
def padEditEmbedFin {α : Type*} (sep : α) {d : ℕ} (x : Fin d → α) : List α :=
  padEditEmbed sep (List.ofFn x)

private lemma length_padWithStride {α : Type*} (sep : α) (k : ℕ) (x : List α) :
    (padWithStride sep k x).length = x.length * (k + 1) := by
  induction x with
  | nil => simp [padWithStride]
  | cons a xs ih =>
    simp only [padWithStride, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_replicate] at ih ⊢
    rw [ih]
    ring

/-- The padded word `padEditEmbed sep x` has length `x.length * (x.length + 1)`. -/
@[simp]
theorem length_padEditEmbed {α : Type*} (sep : α) (x : List α) :
    (padEditEmbed sep x).length = x.length * (x.length + 1) :=
  length_padWithStride sep x.length x

/-- The padded word `padEditEmbedFin sep x` has length `d * (d + 1)`. -/
@[simp]
theorem length_padEditEmbedFin {α : Type*} (sep : α) {d : ℕ} (x : Fin d → α) :
    (padEditEmbedFin sep x).length = d * (d + 1) := by
  simp [padEditEmbedFin]

private lemma getElem_padWithStride {α : Type*} (sep : α) (k : ℕ) (x : List α)
    {p : ℕ} (hp : p < (padWithStride sep k x).length) :
    (padWithStride sep k x)[p] =
      if p % (k + 1) = 0 then
        x[p / (k + 1)]'(by
          rw [length_padWithStride] at hp
          exact Nat.div_lt_of_lt_mul (by linarith))
      else sep := by
  induction x generalizing p with
  | nil => simp [padWithStride] at hp
  | cons a xs ih =>
    simp only [padWithStride, List.flatMap_cons] at hp ⊢
    have hhead : (a :: List.replicate k sep).length = k + 1 := by simp
    rcases lt_or_ge p (k + 1) with hlt | hge
    · rw [List.getElem_append_left (by omega)]
      have hdiv : p / (k + 1) = 0 := Nat.div_eq_of_lt hlt
      have hmod : p % (k + 1) = p := Nat.mod_eq_of_lt hlt
      rcases p with _ | p'
      · simp
      · simp [hmod]
    · rw [List.getElem_append_right (by omega)]
      simp only [hhead]
      have hp' : p - (k + 1) < (padWithStride sep k xs).length := by
        rw [List.length_append, hhead] at hp
        change p - (k + 1) < (xs.flatMap _).length
        omega
      have hrec := ih hp'
      simp only [padWithStride] at hrec
      rw [hrec]
      have hpeq : p = (p - (k + 1)) + (k + 1) := by omega
      have hmod : (p - (k + 1)) % (k + 1) = p % (k + 1) := by
        conv_rhs => rw [hpeq, Nat.add_mod_right]
      have hdiv : p / (k + 1) = (p - (k + 1)) / (k + 1) + 1 := by
        conv_lhs => rw [hpeq]
        exact Nat.add_div_right (p - (k + 1)) (Nat.succ_pos k)
      simp only [hmod]
      split_ifs with hm
      · simp [hdiv]
      · rfl

/-- At active index `i * (x.length + 1)`, `padEditEmbed sep x` recovers `x[i]`. -/
theorem getElem_padEditEmbed_mul {α : Type*} (sep : α) (x : List α) {i : ℕ}
    (hi : i < x.length) :
    (padEditEmbed sep x)[i * (x.length + 1)]'(by
      rw [length_padEditEmbed]
      exact Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos _)) = x[i] := by
  have hp : i * (x.length + 1) < (padWithStride sep x.length x).length := by
    rw [length_padWithStride]
    exact Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos _)
  have h := getElem_padWithStride sep x.length x hp
  simp only [Nat.mul_mod_left, ↓reduceIte,
    Nat.mul_div_cancel i (Nat.succ_pos x.length)] at h
  exact h

/-- Off the active multiples of `x.length + 1`, `padEditEmbed sep x` equals `sep`. -/
theorem getElem_padEditEmbed_of_mod_ne_zero {α : Type*} (sep : α) (x : List α) {p : ℕ}
    (hp : p < x.length * (x.length + 1)) (hm : p % (x.length + 1) ≠ 0) :
    (padEditEmbed sep x)[p]'(by rwa [length_padEditEmbed]) = sep := by
  have hp' : p < (padWithStride sep x.length x).length := by rwa [length_padWithStride]
  have h := getElem_padWithStride sep x.length x hp'
  simp only [hm, ↓reduceIte] at h
  exact h

/-- `padEditEmbed sep` is injective on all lists over `α`. -/
theorem padEditEmbed_injective {α : Type*} (sep : α) :
    Function.Injective (padEditEmbed sep : List α → List α) := by
  intro x y hxy
  have hlen_prod : x.length * (x.length + 1) = y.length * (y.length + 1) := by
    simpa only [length_padEditEmbed] using congrArg List.length hxy
  have hlen : x.length = y.length := by
    rcases lt_trichotomy x.length y.length with hlt | heq | hgt
    · exfalso; nlinarith
    · exact heq
    · exfalso; nlinarith
  refine List.ext_getElem hlen fun i hix hiy ↦ ?_
  have h1 := getElem_padEditEmbed_mul sep x hix
  have h2 := getElem_padEditEmbed_mul sep y hiy
  rw [← h1, ← h2]
  simp [hxy, hlen]

/-- `padEditEmbedFin sep` is injective on `Fin d → α`. -/
theorem padEditEmbedFin_injective {α : Type*} (sep : α) (d : ℕ) :
    Function.Injective (padEditEmbedFin sep : (Fin d → α) → List α) := by
  intro x y hxy
  have hlist := padEditEmbed_injective sep hxy
  funext i
  have := congrArg (fun l : List α ↦ l[i.1]?) hlist
  simpa using this

section LowerBound

variable {α : Type*} [DecidableEq α]

/-- Cumulative source length consumed before step `t` of an edit script. -/
private def srcPos (s : EditScript α) (t : ℕ) : ℕ :=
  (EditScript.src (s.take t)).length

/-- Cumulative target length produced before step `t` of an edit script. -/
private def tgtPos (s : EditScript α) (t : ℕ) : ℕ :=
  (EditScript.tgt (s.take t)).length

private lemma op_drift_le_cost (o : EditOp α) :
    |((o.src.length : ℤ) - (o.tgt.length : ℤ))| ≤ (o.cost Costs.unit : ℤ) := by
  cases o with
  | del _ => simp [EditOp.src, EditOp.tgt, EditOp.cost, Costs.unit_del]
  | ins _ => simp [EditOp.src, EditOp.tgt, EditOp.cost, Costs.unit_ins]
  | sub a b =>
    simp only [EditOp.src, EditOp.tgt, List.length_singleton, sub_self, abs_zero]
    exact Nat.cast_nonneg _

/-- The source-to-target index drift before any step `t` is bounded by the total unit cost of
the edit script. -/
private lemma abs_srcPos_sub_tgtPos_le (s : EditScript α) (t : ℕ) :
    |((srcPos s t : ℤ) - (tgtPos s t : ℤ))| ≤ (EditScript.cost Costs.unit s : ℤ) := by
  have hpre : ∀ u : EditScript α,
      |(((EditScript.src u).length : ℤ) - ((EditScript.tgt u).length : ℤ))| ≤
        (EditScript.cost Costs.unit u : ℤ) := by
    intro u
    induction u with
    | nil => simp
    | cons o u ih =>
      simp only [EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
        List.length_append, Nat.cast_add]
      have ho := op_drift_le_cost o
      have hsplit : (o.src.length : ℤ) + (EditScript.src u).length -
          (o.tgt.length + (EditScript.tgt u).length) =
          (o.src.length - o.tgt.length) +
            ((EditScript.src u).length - (EditScript.tgt u).length) := by ring
      rw [hsplit]
      exact (abs_add_le _ _).trans (add_le_add ho ih)
  have htake_cost : EditScript.cost Costs.unit (s.take t) ≤ EditScript.cost Costs.unit s := by
    conv_rhs => rw [← List.take_append_drop t s, EditScript.cost_append]
    omega
  exact (hpre (s.take t)).trans (by exact_mod_cast htake_cost)

omit [DecidableEq α] in
private lemma exists_src_step (s : EditScript α) {p : ℕ} (hp : p < (EditScript.src s).length) :
    ∃ t : Fin s.length, srcPos s t.1 = p ∧
      ((s[t.1] = .del ((EditScript.src s)[p])) ∨
        ∃ (b : α) (hq : tgtPos s t.1 < (EditScript.tgt s).length),
          b = (EditScript.tgt s)[tgtPos s t.1] ∧ s[t.1] = .sub ((EditScript.src s)[p]) b) := by
  induction s generalizing p with
  | nil => simp at hp
  | cons o s ih =>
    cases o with
    | del a =>
      have hp' : p < (EditScript.src s).length + 1 := by
        simpa [EditScript.src_cons, EditOp.src] using hp
      rcases p with _ | p'
      · exact ⟨⟨0, by simp⟩, by simp [srcPos],
          Or.inl (by simp [EditScript.src_cons, EditOp.src])⟩
      · obtain ⟨⟨t, ht⟩, hpos, hcase⟩ := ih (p := p') (by omega)
        refine ⟨⟨t + 1, by simp [ht]⟩, ?_, ?_⟩
        · simp only [srcPos, List.take_succ_cons, EditScript.src_cons, EditOp.src,
            List.length_append, List.length_singleton]
          simp only [srcPos] at hpos
          omega
        · rcases hcase with hdel | ⟨b, hq, hb, hsub⟩
          · left; simpa [EditScript.src_cons, EditOp.src] using hdel
          · right
            have htp : tgtPos (EditOp.del a :: s) (t + 1) = tgtPos s t := by
              simp [tgtPos, EditScript.tgt_cons, EditOp.tgt]
            refine ⟨b, by simpa [htp, EditScript.tgt_cons, EditOp.tgt] using hq, ?_, ?_⟩
            · simpa [htp, EditScript.tgt_cons, EditOp.tgt] using hb
            · simpa [EditScript.src_cons, EditOp.src] using hsub
    | ins c =>
      have hp' : p < (EditScript.src s).length := by
        simpa [EditScript.src_cons, EditOp.src] using hp
      obtain ⟨⟨t, ht⟩, hpos, hcase⟩ := ih hp'
      refine ⟨⟨t + 1, by simp [ht]⟩, ?_, ?_⟩
      · simpa [srcPos, EditScript.src_cons, EditOp.src] using hpos
      · rcases hcase with hdel | ⟨b, hq, hb, hsub⟩
        · left; simpa [EditScript.src_cons, EditOp.src] using hdel
        · right
          have htp : tgtPos (EditOp.ins c :: s) (t + 1) = tgtPos s t + 1 := by
            simp only [tgtPos, List.take_succ_cons, EditScript.tgt_cons, EditOp.tgt,
              List.singleton_append, List.length_cons]
          have hq1 : tgtPos (EditOp.ins c :: s) (t + 1) <
              (EditScript.tgt (EditOp.ins c :: s)).length := by
            rw [htp, EditScript.tgt_cons, EditOp.tgt, List.singleton_append, List.length_cons]
            exact Nat.succ_lt_succ hq
          refine ⟨b, hq1, ?_, ?_⟩
          · simp only [htp, EditScript.tgt_cons, EditOp.tgt, List.singleton_append,
              List.getElem_cons_succ, hb]
          · simpa [EditScript.src_cons, EditOp.src] using hsub
    | sub a c =>
      have hp' : p < (EditScript.src s).length + 1 := by
        simpa [EditScript.src_cons, EditOp.src] using hp
      rcases p with _ | p'
      · refine ⟨⟨0, by simp⟩, by simp [srcPos],
          Or.inr ⟨c, by simp [tgtPos, EditScript.tgt_cons, EditOp.tgt],
            by simp [tgtPos, EditScript.tgt_cons, EditOp.tgt],
            by simp [EditScript.src_cons, EditOp.src]⟩⟩
      · obtain ⟨⟨t, ht⟩, hpos, hcase⟩ := ih (p := p') (by omega)
        refine ⟨⟨t + 1, by simp [ht]⟩, ?_, ?_⟩
        · simp only [srcPos, List.take_succ_cons, EditScript.src_cons, EditOp.src,
            List.length_append, List.length_singleton]
          simp only [srcPos] at hpos
          omega
        · rcases hcase with hdel | ⟨b, hq, hb, hsub⟩
          · left; simpa [EditScript.src_cons, EditOp.src] using hdel
          · right
            have htp : tgtPos (EditOp.sub a c :: s) (t + 1) = tgtPos s t + 1 := by
              simp only [tgtPos, List.take_succ_cons, EditScript.tgt_cons, EditOp.tgt,
                List.singleton_append, List.length_cons]
            have hq1 : tgtPos (EditOp.sub a c :: s) (t + 1) <
                (EditScript.tgt (EditOp.sub a c :: s)).length := by
              rw [htp, EditScript.tgt_cons, EditOp.tgt, List.singleton_append, List.length_cons]
              exact Nat.succ_lt_succ hq
            refine ⟨b, hq1, ?_, ?_⟩
            · simp only [htp, EditScript.tgt_cons, EditOp.tgt, List.singleton_append,
                List.getElem_cons_succ, hb]
            · simpa [EditScript.src_cons, EditOp.src] using hsub

omit [DecidableEq α] in
private lemma exists_tgt_step (s : EditScript α) {q : ℕ} (hq : q < (EditScript.tgt s).length) :
    ∃ t : Fin s.length, tgtPos s t.1 = q ∧
      ((s[t.1] = .ins ((EditScript.tgt s)[q])) ∨
        ∃ (a : α) (hp : srcPos s t.1 < (EditScript.src s).length),
          a = (EditScript.src s)[srcPos s t.1] ∧ s[t.1] = .sub a ((EditScript.tgt s)[q])) := by
  classical
  have hrev := map_revOp_spec s
  have hq' : q < (EditScript.src (s.map revOp)).length := by rwa [hrev.1]
  obtain ⟨⟨t, ht⟩, hpos, hcase⟩ := exists_src_step (s.map revOp) hq'
  have ht' : t < s.length := by simpa using ht
  have hsp : srcPos (s.map revOp) t = tgtPos s t := by
    simp only [srcPos, tgtPos, ← List.map_take, (map_revOp_spec (s.take t)).1]
  have htp : tgtPos (s.map revOp) t = srcPos s t := by
    simp only [srcPos, tgtPos, ← List.map_take, (map_revOp_spec (s.take t)).2.1]
  refine ⟨⟨t, ht'⟩, hsp ▸ hpos, ?_⟩
  have hget_src : (EditScript.src (s.map revOp))[q] = (EditScript.tgt s)[q] := by simp [hrev.1]
  rcases hcase with hdel | ⟨a, hp, ha, hsub⟩
  · left
    rw [List.getElem_map, hget_src] at hdel
    cases ho : s[t] with
    | del x => simp only [ho, revOp, reduceCtorEq] at hdel
    | sub x z => simp only [ho, revOp, reduceCtorEq] at hdel
    | ins z =>
      simp only [ho, revOp, EditOp.del.injEq] at hdel
      exact hdel ▸ rfl
  · right
    have hp' : srcPos s t < (EditScript.src s).length := by
      rw [← htp, ← hrev.2.1]
      exact hp
    have ha' : a = (EditScript.src s)[srcPos s t] := by
      rw [ha]
      simp [htp, hrev.2.1]
    refine ⟨a, hp', ha', ?_⟩
    rw [List.getElem_map, hget_src] at hsub
    cases ho : s[t] with
    | del x => simp only [ho, revOp, reduceCtorEq] at hsub
    | ins z => simp only [ho, revOp, reduceCtorEq] at hsub
    | sub x z =>
      simp only [ho, revOp, EditOp.sub.injEq] at hsub
      rw [hsub.1, hsub.2]

private lemma script_cost_eq_sum (s : EditScript α) :
    EditScript.cost Costs.unit s = ∑ t : Fin s.length, s[t.1].cost Costs.unit := by
  induction s with
  | nil => simp
  | cons o s ih =>
    rw [EditScript.cost_cons, ih]
    simpa using (Fin.sum_univ_succ fun t : Fin (o :: s).length ↦ (o :: s)[t.1].cost Costs.unit).symm

/-- Exact isometry theorem on lists: padding each character of equal-length words `x, y` with
`x.length` copies of any separator symbol `sep` makes their unit-cost Levenshtein edit distance
identically equal to their Hamming distance. -/
theorem editDist_padEditEmbed_eq (sep : α) {x y : List α} (hlen : x.length = y.length) :
    editDist Costs.unit (padEditEmbed sep x) (padEditEmbed sep y) = listHammingDist x y := by
  -- Step 1: Upper bound `ED(pad x, pad y) ≤ Δ(x, y) ≤ x.length` by coordinatewise substitution.
  have hub : editDist Costs.unit (padEditEmbed sep x) (padEditEmbed sep y) ≤
      listHammingDist x y := by
    have hham_pad : listHammingDist (padEditEmbed sep x) (padEditEmbed sep y) =
        listHammingDist x y := by
      have haux : ∀ (k : ℕ) (u v : List α), u.length = v.length →
          listHammingDist (padWithStride sep k u) (padWithStride sep k v) =
            listHammingDist u v := by
        intro k u
        induction u with
        | nil => intro v hv; cases v <;> simp [padWithStride] at hv ⊢
        | cons a us ih =>
          intro v hv
          cases v with
          | nil => simp at hv
          | cons b vs =>
            simp only [List.length_cons, Nat.succ.injEq] at hv
            have hrep : ∀ (m : ℕ) (r₁ r₂ : List α),
                listHammingDist (List.replicate m sep ++ r₁) (List.replicate m sep ++ r₂) =
                  listHammingDist r₁ r₂ := by
              intro m r₁ r₂
              induction m with
              | zero => simp
              | succ m ihm => simp [List.replicate_succ, ihm]
            simp only [padWithStride, List.flatMap_cons, List.cons_append,
              listHammingDist_cons_cons, hrep k]
            exact congrArg _ (ih vs hv)
      simpa only [padEditEmbed, hlen] using haux y.length x y hlen
    calc
      editDist Costs.unit (padEditEmbed sep x) (padEditEmbed sep y) ≤
          listHammingDist (padEditEmbed sep x) (padEditEmbed sep y) :=
        editDist_unit_le_listHammingDist (by simp [hlen])
      _ = listHammingDist x y := hham_pad
  refine le_antisymm hub ?_
  -- Step 2: Lower bound via index-drift localization on an optimal edit script `s`.
  let d := x.length
  have hxlen : x.length = d := rfl
  have hylen : y.length = d := hlen.symm
  let s := optScript Costs.unit (padEditEmbed sep x) (padEditEmbed sep y)
  have hsrc : EditScript.src s = padEditEmbed sep x := src_optScript Costs.unit _ _
  have htgt : EditScript.tgt s = padEditEmbed sep y := tgt_optScript Costs.unit _ _
  have hcost : EditScript.cost Costs.unit s =
      editDist Costs.unit (padEditEmbed sep x) (padEditEmbed sep y) :=
    cost_optScript Costs.unit _ _
  have hcost_le_d : EditScript.cost Costs.unit s ≤ d :=
    hcost ▸ hub.trans (listHammingDist_le_length x y)
  have hyi : ∀ j : Fin d, j.1 < y.length := fun j ↦ by omega
  have hactive_x : ∀ p (hp : p < (EditScript.src s).length), (EditScript.src s)[p] ≠ sep →
      ∃ j : Fin d, p = j.1 * (d + 1) ∧ (EditScript.src s)[p] = x[j.1]'j.2 := by
    intro p hp hne
    have hplen : p < d * (d + 1) := by simpa [hsrc, d] using hp
    have hmod : p % (d + 1) = 0 := by
      by_contra hm
      apply hne
      have hget : (EditScript.src s)[p] = (padEditEmbed sep x)[p]'(by simpa [d] using hplen) := by
        simp [hsrc]
      rw [hget]
      exact getElem_padEditEmbed_of_mod_ne_zero sep x hplen hm
    let j : Fin d := ⟨p / (d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩
    have hpj : p = j.1 * (d + 1) := by
      have := Nat.div_add_mod p (d + 1)
      rw [hmod, add_zero, mul_comm] at this
      exact this.symm
    refine ⟨j, hpj, ?_⟩
    have hget : (EditScript.src s)[p] = (padEditEmbed sep x)[j.1 * (d + 1)]'(by
        rw [length_padEditEmbed]
        exact Nat.mul_lt_mul_of_pos_right j.2 (Nat.succ_pos d)) := by
      simp [hsrc, hpj]
    rw [hget]
    exact getElem_padEditEmbed_mul sep x j.2
  have hactive_y : ∀ q (hq : q < (EditScript.tgt s).length), (EditScript.tgt s)[q] ≠ sep →
      ∃ j : Fin d, q = j.1 * (d + 1) ∧ (EditScript.tgt s)[q] = y[j.1]'(hyi j) := by
    intro q hq hne
    have hqlen : q < y.length * (y.length + 1) := by simpa [htgt] using hq
    have hmod : q % (y.length + 1) = 0 := by
      by_contra hm
      apply hne
      have hget : (EditScript.tgt s)[q] = (padEditEmbed sep y)[q]'(by simpa using hqlen) := by
        simp [htgt]
      rw [hget]
      exact getElem_padEditEmbed_of_mod_ne_zero sep y hqlen hm
    have hqd : q < d * (d + 1) := by rwa [hylen] at hqlen
    have hmod_d : q % (d + 1) = 0 := by rwa [hylen] at hmod
    let j : Fin d := ⟨q / (d + 1), Nat.div_lt_of_lt_mul (by linarith)⟩
    have hqj : q = j.1 * (d + 1) := by
      have := Nat.div_add_mod q (d + 1)
      rw [hmod_d, add_zero, mul_comm] at this
      exact this.symm
    refine ⟨j, hqj, ?_⟩
    have hget : (EditScript.tgt s)[q] = (padEditEmbed sep y)[j.1 * (y.length + 1)]'(by
        rw [length_padEditEmbed]
        exact Nat.mul_lt_mul_of_pos_right (hyi j) (Nat.succ_pos _)) := by
      simp [htgt, hqj, hylen]
    rw [hget]
    exact getElem_padEditEmbed_mul sep y (hyi j)
  have hsame_idx : ∀ (i j : Fin d) (t : Fin s.length),
      srcPos s t.1 = i.1 * (d + 1) → tgtPos s t.1 = j.1 * (d + 1) → i = j := by
    intro i j t hsp htp
    have hdrift := abs_srcPos_sub_tgtPos_le s t.1
    rw [hsp, htp] at hdrift
    have hle : |((i.1 : ℤ) - (j.1 : ℤ)) * ((d : ℤ) + 1)| ≤ (d : ℤ) := by
      have heq : ((i.1 * (d + 1) : ℕ) : ℤ) - ((j.1 * (d + 1) : ℕ) : ℤ) =
          ((i.1 : ℤ) - (j.1 : ℤ)) * ((d : ℤ) + 1) := by push_cast; ring
      rw [← heq]
      exact hdrift.trans (by exact_mod_cast hcost_le_d)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (d : ℤ) + 1)] at hle
    by_contra hij
    have hne : (i.1 : ℤ) ≠ (j.1 : ℤ) := fun h ↦ hij (Fin.ext (Int.ofNat.inj h))
    have h1 : (1 : ℤ) ≤ |(i.1 : ℤ) - (j.1 : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hne)
    nlinarith
  -- Step 3: Assign to each mismatching coordinate `i ∈ M` a distinct unit-cost step of `s`.
  let M : Finset (Fin d) := Finset.univ.filter fun i ↦ x[i.1]'i.2 ≠ y[i.1]'(hyi i)
  have hex_step : ∀ i ∈ M, ∃ t : Fin s.length,
      1 ≤ s[t.1].cost Costs.unit ∧
        (if x[i.1]'i.2 ≠ sep then srcPos s t.1 = i.1 * (d + 1)
         else tgtPos s t.1 = i.1 * (d + 1)) := by
    intro i hiM
    have hxy_ne : x[i.1]'i.2 ≠ y[i.1]'(hyi i) := (Finset.mem_filter.mp hiM).2
    have hpi_src : i.1 * (d + 1) < (EditScript.src s).length := by
      rw [hsrc, length_padEditEmbed]
      exact Nat.mul_lt_mul_of_pos_right i.2 (Nat.succ_pos d)
    have hpi_tgt : i.1 * (d + 1) < (EditScript.tgt s).length := by
      rw [htgt, length_padEditEmbed, hylen]
      exact Nat.mul_lt_mul_of_pos_right i.2 (Nat.succ_pos d)
    have hsrc_i : (EditScript.src s)[i.1 * (d + 1)] = x[i.1]'i.2 := by
      have hg : (EditScript.src s)[i.1 * (d + 1)] = (padEditEmbed sep x)[i.1 * (d + 1)]'(by
          rwa [← hsrc]) := by simp [hsrc]
      rw [hg]
      exact getElem_padEditEmbed_mul sep x i.2
    have htgt_i : (EditScript.tgt s)[i.1 * (d + 1)] = y[i.1]'(hyi i) := by
      have hg : (EditScript.tgt s)[i.1 * (d + 1)] =
          (padEditEmbed sep y)[i.1 * (y.length + 1)]'(by
            rw [length_padEditEmbed]
            exact Nat.mul_lt_mul_of_pos_right (hyi i) (Nat.succ_pos _)) := by
        simp [htgt, hylen]
      rw [hg]
      exact getElem_padEditEmbed_mul sep y (hyi i)
    by_cases hxs : x[i.1]'i.2 ≠ sep
    · obtain ⟨t, hsp, hcase⟩ := exists_src_step s hpi_src
      refine ⟨t, ?_, by simp [hxs, hsp]⟩
      rcases hcase with hdel | ⟨b, hq, hb, hsub⟩
      · simp [hdel, EditOp.cost, Costs.unit_del]
      · rw [hsub, EditOp.cost, Costs.unit_sub, hsrc_i]
        have hne_b : x[i.1]'i.2 ≠ b := by
          intro heq
          have hb_ne : (EditScript.tgt s)[tgtPos s t.1] ≠ sep := by rw [← hb, ← heq]; exact hxs
          obtain ⟨j, hqj, hvalj⟩ := hactive_y (tgtPos s t.1) hq hb_ne
          have hij : i = j := hsame_idx i j t hsp hqj
          subst hij
          exact hxy_ne (heq.trans (hb.trans hvalj))
        simp [hne_b]
    · push Not at hxs
      have hys : y[i.1]'(hyi i) ≠ sep := fun hy ↦ hxy_ne (hxs.trans hy.symm)
      obtain ⟨t, htp, hcase⟩ := exists_tgt_step s hpi_tgt
      refine ⟨t, ?_, by simp [hxs, htp]⟩
      rcases hcase with hins | ⟨a, hp, ha, hsub⟩
      · simp [hins, EditOp.cost, Costs.unit_ins]
      · rw [hsub, EditOp.cost, Costs.unit_sub, htgt_i]
        have hne_a : a ≠ y[i.1]'(hyi i) := by
          intro heq
          have ha_ne : (EditScript.src s)[srcPos s t.1] ≠ sep := by rw [← ha, heq]; exact hys
          obtain ⟨j, hpj, hvalj⟩ := hactive_x (srcPos s t.1) hp ha_ne
          have hji : j = i := hsame_idx j i t hpj htp
          subst hji
          exact hxy_ne (hvalj.symm.trans (ha.symm.trans heq))
        simp [hne_a]
  classical
  let pick : {i // i ∈ M} → Fin s.length := fun i ↦ (hex_step i.1 i.2).choose
  have hpick_spec := fun i : {i // i ∈ M} ↦ (hex_step i.1 i.2).choose_spec
  have hpick_inj : Function.Injective pick := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    apply Subtype.ext
    have hi_sp : if x[i.1]'i.2 ≠ sep then srcPos s (pick ⟨i, hi⟩).1 = i.1 * (d + 1)
        else tgtPos s (pick ⟨i, hi⟩).1 = i.1 * (d + 1) := (hpick_spec ⟨i, hi⟩).2
    have hj_sp : if x[j.1]'j.2 ≠ sep then srcPos s (pick ⟨i, hi⟩).1 = j.1 * (d + 1)
        else tgtPos s (pick ⟨i, hi⟩).1 = j.1 * (d + 1) := by
      have h0 : if x[j.1]'j.2 ≠ sep then srcPos s (pick ⟨j, hj⟩).1 = j.1 * (d + 1)
          else tgtPos s (pick ⟨j, hj⟩).1 = j.1 * (d + 1) := (hpick_spec ⟨j, hj⟩).2
      rwa [← heq] at h0
    by_cases hxi : x[i.1]'i.2 ≠ sep <;> by_cases hxj : x[j.1]'j.2 ≠ sep
    · simp only [hxi, ne_eq, not_false_eq_true, ↓reduceIte] at hi_sp
      simp only [hxj, ne_eq, not_false_eq_true, ↓reduceIte] at hj_sp
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos d) (hi_sp.symm.trans hj_sp))
    · simp only [hxi, ne_eq, not_false_eq_true, ↓reduceIte] at hi_sp
      simp only [hxj, ↓reduceIte] at hj_sp
      exact hsame_idx i j (pick ⟨i, hi⟩) hi_sp hj_sp
    · simp only [hxi, ↓reduceIte] at hi_sp
      simp only [hxj, ne_eq, not_false_eq_true, ↓reduceIte] at hj_sp
      exact (hsame_idx j i (pick ⟨i, hi⟩) hj_sp hi_sp).symm
    · simp only [hxi, ↓reduceIte] at hi_sp
      simp only [hxj, ↓reduceIte] at hj_sp
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos d) (hi_sp.symm.trans hj_sp))
  -- Sum the unit costs over the injective image of `M`.
  let emb : {i // i ∈ M} ↪ Fin s.length := ⟨pick, hpick_inj⟩
  rw [← hcost, script_cost_eq_sum, listHammingDist_eq_card_filter hxlen hylen]
  calc
    M.card = ∑ _i : {i // i ∈ M}, 1 := by simp
    _ ≤ ∑ i : {i // i ∈ M}, s[(emb i).1].cost Costs.unit :=
      Finset.sum_le_sum fun i _ ↦ (hpick_spec i).1
    _ = ∑ t ∈ Finset.univ.map emb, s[t.1].cost Costs.unit :=
      (Finset.sum_map Finset.univ emb fun t : Fin s.length ↦ s[t.1].cost Costs.unit).symm
    _ ≤ ∑ t : Fin s.length, s[t.1].cost Costs.unit :=
      Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _

/-- Exact isometry theorem on `Fin d → α`: `padEditEmbedFin sep` embeds `(Fin d → α, hammingDist)`
isometrically into `(List α, editDist Costs.unit)` with output length `d * (d + 1)`. -/
theorem editDist_padEditEmbedFin_eq_hammingDist (sep : α) {d : ℕ} (x y : Fin d → α) :
    editDist Costs.unit (padEditEmbedFin sep x) (padEditEmbedFin sep y) = hammingDist x y := by
  rw [padEditEmbedFin, padEditEmbedFin, editDist_padEditEmbed_eq sep (by simp),
    listHammingDist_ofFn]

end LowerBound

open ComputableInPolyTime in
/-- The binary separator-padded isometric embedding `padEditEmbed false : List Bool → List Bool`
is computable in polynomial time on a deterministic multi-tape Turing machine. -/
theorem computableInPolyTime_padEditEmbed_bool :
    ComputableInPolyTime (padEditEmbed false) encBits encBits := by
  obtain ⟨toL, fromL⟩ := bits_encList_polyTime encBool
  refine fromL.comp (flatMapWithInput (encA := encBool) (encB := encBool) toL ?_)
  exact (cons encBool).comp ((snd encBits encBool).prod
    (replicate (encA := encBool) (length_bits.comp (fst encBits encBool)) (const false)))

-- Non-vacuity witness on non-degenerate 4-bit strings with Hamming distance 2.
example :
    let x : Fin 4 → Bool := ![true, false, true, false]
    let y : Fin 4 → Bool := ![true, true, false, false]
    (padEditEmbedFin false x).length = 20 ∧
      editDist Costs.unit (padEditEmbedFin false x) (padEditEmbedFin false y) = 2 ∧
      hammingDist x y = 2 := by
  refine ⟨by simp, ?_, by decide⟩
  rw [editDist_padEditEmbedFin_eq_hammingDist]
  decide

end Embedding

end CslibFrontier.Algorithms.Lean.EditDistance
