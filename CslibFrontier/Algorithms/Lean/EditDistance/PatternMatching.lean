/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.EditDistance.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Linarith

/-!
# Metric properties of Levenshtein edit distance and pattern matching distance

Establishes the metric properties and structural monotonicity laws of unit-cost Levenshtein edit
distance (`Cslib.Algorithms.Lean.EditDistance.editDist Costs.unit`), its characterization via
deletion-substitution scripts to a common target word, and the exact guard-padding reduction from
substring pattern matching distance to global edit distance:

* **Metric and subadditivity laws**: reflexivity (`editDist_unit_self`), symmetry
  (`editDist_unit_comm`), identity of indiscernibles (`editDist_unit_eq_zero_iff`), triangle
  inequality (`editDist_unit_triangle`), concatenation subadditivity (`editDist_unit_append`),
  symbol-count lower bounds (`count_sub_le_editDist_unit`), and 1-Lipschitz stability under
  `List.filter` (`editDist_unit_filter_le`).
* **Common-target deletion-substitution characterization** (`IsDelSubScript`,
  `isLeast_delSub_common_target`): `editDist Costs.unit x y` equals the least total cost over all
  common target words `z` of transforming `x` to `z` and `y` to `z` using only deletions and
  substitutions (no insertions).
* **Pattern matching distance and fresh-guard reduction** (`contiguousSubseqs`, `patternDist`,
  `isLeast_patternDist`, `editDist_unit_guard_pad_eq_patternDist`): defines the minimum edit
  distance from a pattern `p` to all contiguous substrings (`List.IsInfix`) of a text `t`, and
  proves that flanking `p` on both sides with `|t|` copies of a fresh symbol `g ∉ t` satisfies
  `editDist Costs.unit (g^{|t|} ++ p ++ g^{|t|}) t = 2 * |t| + patternDist p t`.

## Main definitions

* `CslibFrontier.Algorithms.Lean.EditDistance.IsDelSubScript`: predicate on `EditScript α`
  forbidding insertions.
* `CslibFrontier.Algorithms.Lean.EditDistance.contiguousSubseqs`: enumeration of all contiguous
  substrings of a list.
* `CslibFrontier.Algorithms.Lean.EditDistance.patternDist`: minimum unit-cost edit distance from a
  pattern word to all contiguous substrings of a text word.

## Main results

* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_self`
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_comm`
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_eq_zero_iff`
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_triangle`
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_append`
* `CslibFrontier.Algorithms.Lean.EditDistance.count_sub_le_editDist_unit`
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_filter_le`
* `CslibFrontier.Algorithms.Lean.EditDistance.isLeast_delSub_common_target`
* `CslibFrontier.Algorithms.Lean.EditDistance.isLeast_patternDist`
* `CslibFrontier.Algorithms.Lean.EditDistance.editDist_unit_guard_pad_eq_patternDist`
-/

public section

namespace CslibFrontier.Algorithms.Lean.EditDistance

open Cslib.Algorithms.Lean.EditDistance

/-! ### 1. Metric and Lipschitz properties of unit-cost edit distance -/

private def revOp {α : Type*} : EditOp α → EditOp α
  | .del a => .ins a
  | .ins b => .del b
  | .sub a b => .sub b a

private theorem src_revOp {α : Type*} (op : EditOp α) : (revOp op).src = op.tgt := by
  cases op <;> rfl

private theorem tgt_revOp {α : Type*} (op : EditOp α) : (revOp op).tgt = op.src := by
  cases op <;> rfl

private theorem cost_revOp {α : Type*} [DecidableEq α] (op : EditOp α) :
    (revOp op).cost Costs.unit = op.cost Costs.unit := by
  cases op with
  | del _ | ins _ => rfl
  | sub a b => simp only [revOp, EditOp.cost, Costs.unit_sub, eq_comm]

private theorem src_map_revOp {α : Type*} :
    ∀ s : EditScript α, EditScript.src (s.map revOp) = EditScript.tgt s
  | [] => by simp
  | op :: s => by simp [src_revOp, src_map_revOp s]

private theorem tgt_map_revOp {α : Type*} :
    ∀ s : EditScript α, EditScript.tgt (s.map revOp) = EditScript.src s
  | [] => by simp
  | op :: s => by simp [tgt_revOp, tgt_map_revOp s]

private theorem cost_map_revOp {α : Type*} [DecidableEq α] :
    ∀ s : EditScript α, EditScript.cost Costs.unit (s.map revOp) = EditScript.cost Costs.unit s
  | [] => by simp
  | op :: s => by simp [cost_revOp, cost_map_revOp s]

/-- Unit-cost edit distance from any word to itself is zero. -/
@[simp] theorem editDist_unit_self {α : Type*} [DecidableEq α] (x : List α) :
    editDist Costs.unit x x = 0 := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    have h := editDist_cons_cons_le Costs.unit a a x x
    simp only [Costs.unit_sub, ↓reduceIte, zero_add] at h
    exact Nat.eq_zero_of_le_zero (h.trans ih.le)

/-- Symmetry of unit-cost edit distance. -/
theorem editDist_unit_comm {α : Type*} [DecidableEq α] (x y : List α) :
    editDist Costs.unit x y = editDist Costs.unit y x := by
  have hle : ∀ u v : List α, editDist Costs.unit v u ≤ editDist Costs.unit u v := fun u v => by
    let sr : EditScript α := (optScript Costs.unit u v).map revOp
    have hsrc : EditScript.src sr = v :=
      (src_map_revOp _).trans (tgt_optScript Costs.unit u v)
    have htgt : EditScript.tgt sr = u :=
      (tgt_map_revOp _).trans (src_optScript Costs.unit u v)
    have hcost : EditScript.cost Costs.unit sr = editDist Costs.unit u v :=
      (cost_map_revOp _).trans (cost_optScript Costs.unit u v)
    calc editDist Costs.unit v u
        = editDist Costs.unit (EditScript.src sr) (EditScript.tgt sr) := by rw [hsrc, htgt]
      _ ≤ EditScript.cost Costs.unit sr := editDist_le_cost Costs.unit sr
      _ = editDist Costs.unit u v := hcost
  exact le_antisymm (hle y x) (hle x y)

private theorem src_eq_tgt_of_cost_zero {α : Type*} [DecidableEq α] :
    ∀ {s : EditScript α}, EditScript.cost Costs.unit s = 0 → EditScript.src s = EditScript.tgt s
  | [], _ => by simp
  | .del _ :: _, hc => by simp [EditOp.cost] at hc
  | .ins _ :: _, hc => by simp [EditOp.cost] at hc
  | .sub a b :: s, hc => by
    simp only [EditScript.cost_cons, EditOp.cost, Costs.unit_sub, Nat.add_eq_zero_iff,
      ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not] at hc
    rcases hc with ⟨rfl, hs⟩
    simp [EditOp.src, EditOp.tgt, src_eq_tgt_of_cost_zero hs]

/-- Unit-cost edit distance is zero if and only if the two words are equal. -/
theorem editDist_unit_eq_zero_iff {α : Type*} [DecidableEq α] {x y : List α} :
    editDist Costs.unit x y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ editDist_unit_self x⟩
  have hc : EditScript.cost Costs.unit (optScript Costs.unit x y) = 0 :=
    (cost_optScript Costs.unit x y).trans h
  exact (src_optScript Costs.unit x y).symm.trans
    ((src_eq_tgt_of_cost_zero hc).trans (tgt_optScript Costs.unit x y))

private theorem editDist_unit_le_one_add_cons_src {α : Type*} [DecidableEq α] :
    ∀ (t : EditScript α) (b : α) (u : List α),
      EditScript.src t = b :: u →
      editDist Costs.unit u (EditScript.tgt t) ≤ 1 + EditScript.cost Costs.unit t
  | [], _, _, h => by simp at h
  | .del a :: t, b, u, h => by
    simp only [EditScript.src_cons, EditOp.src, List.singleton_append, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hle : editDist Costs.unit (EditScript.src t) (EditScript.tgt t) ≤
        EditScript.cost Costs.unit t := editDist_le_cost Costs.unit t
    simp only [EditScript.tgt_cons, EditOp.tgt, List.nil_append,
      EditScript.cost_cons, EditOp.cost, Costs.unit_del]
    omega
  | .ins c :: t, b, u, h => by
    simp only [EditScript.src_cons, EditOp.src, List.nil_append] at h
    have ih := editDist_unit_le_one_add_cons_src t b u h
    have hstep : editDist Costs.unit u (c :: EditScript.tgt t) ≤
        1 + editDist Costs.unit u (EditScript.tgt t) :=
      editDist_cons_right_le Costs.unit c u (EditScript.tgt t)
    simp only [EditScript.tgt_cons, EditOp.tgt, List.singleton_append,
      EditScript.cost_cons, EditOp.cost, Costs.unit_ins]
    omega
  | .sub a c :: t, b, u, h => by
    simp only [EditScript.src_cons, EditOp.src, List.singleton_append, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hle : editDist Costs.unit (EditScript.src t) (EditScript.tgt t) ≤
        EditScript.cost Costs.unit t := editDist_le_cost Costs.unit t
    have hstep : editDist Costs.unit (EditScript.src t) (c :: EditScript.tgt t) ≤
        1 + editDist Costs.unit (EditScript.src t) (EditScript.tgt t) :=
      editDist_cons_right_le Costs.unit c (EditScript.src t) (EditScript.tgt t)
    simp only [EditScript.tgt_cons, EditOp.tgt, List.singleton_append,
      EditScript.cost_cons, EditOp.cost, Costs.unit_sub]
    omega

/-- Triangle inequality for unit-cost edit distance. -/
theorem editDist_unit_triangle {α : Type*} [DecidableEq α] (x y z : List α) :
    editDist Costs.unit x z ≤ editDist Costs.unit x y + editDist Costs.unit y z := by
  suffices ∀ (s : EditScript α) (w : List α),
      editDist Costs.unit (EditScript.src s) w ≤
        EditScript.cost Costs.unit s + editDist Costs.unit (EditScript.tgt s) w by
    have h := this (optScript Costs.unit x y) z
    rwa [src_optScript, tgt_optScript, cost_optScript] at h
  intro s
  induction s with
  | nil => intro w; simp
  | cons op s ih =>
    intro w
    rcases op with a | b | ⟨a, b⟩
    · simp only [EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
        EditOp.src, EditOp.tgt, EditOp.cost, Costs.unit_del, List.singleton_append, List.nil_append]
      have hstep : editDist Costs.unit (a :: EditScript.src s) w ≤
          1 + editDist Costs.unit (EditScript.src s) w :=
        editDist_cons_left_le Costs.unit a (EditScript.src s) w
      have ihw := ih w
      omega
    · simp only [EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
        EditOp.src, EditOp.tgt, EditOp.cost, Costs.unit_ins, List.singleton_append, List.nil_append]
      have hstep : editDist Costs.unit (EditScript.tgt s) w ≤
          1 + editDist Costs.unit (b :: EditScript.tgt s) w := by
        have hraw := editDist_unit_le_one_add_cons_src
          (optScript Costs.unit (b :: EditScript.tgt s) w) b (EditScript.tgt s)
            (src_optScript _ _ _)
        rwa [tgt_optScript, cost_optScript] at hraw
      have ihw := ih w
      omega
    · simp only [EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
        EditOp.src, EditOp.tgt, EditOp.cost, Costs.unit_sub, List.singleton_append]
      suffices ∀ (t : EditScript α), EditScript.src t = b :: EditScript.tgt s →
          editDist Costs.unit (a :: EditScript.src s) (EditScript.tgt t) ≤
            (if a = b then 0 else 1) + EditScript.cost Costs.unit s +
              EditScript.cost Costs.unit t by
        have hraw := this (optScript Costs.unit (b :: EditScript.tgt s) w) (src_optScript _ _ _)
        rw [tgt_optScript, cost_optScript] at hraw
        omega
      intro t ht
      induction t with
      | nil => simp at ht
      | cons op' t' iht =>
        rcases op' with d | c | ⟨d, c⟩
        · simp only [EditScript.src_cons, EditOp.src, List.singleton_append,
            List.cons.injEq] at ht
          rcases ht with ⟨rfl, ht'⟩
          have h1 : editDist Costs.unit (a :: EditScript.src s) (EditScript.tgt t') ≤
              1 + editDist Costs.unit (EditScript.src s) (EditScript.tgt t') :=
            editDist_cons_left_le Costs.unit a (EditScript.src s) (EditScript.tgt t')
          have h2 := ih (EditScript.tgt t')
          have h3 : editDist Costs.unit (EditScript.tgt s) (EditScript.tgt t') ≤
              EditScript.cost Costs.unit t' :=
            ht' ▸ editDist_le_cost Costs.unit t'
          simp only [EditScript.tgt_cons, EditOp.tgt, List.nil_append,
            EditScript.cost_cons, EditOp.cost, Costs.unit_del]
          omega
        · simp only [EditScript.src_cons, EditOp.src, List.nil_append] at ht
          have ih_t := iht ht
          have h1 : editDist Costs.unit (a :: EditScript.src s) (c :: EditScript.tgt t') ≤
              1 + editDist Costs.unit (a :: EditScript.src s) (EditScript.tgt t') :=
            editDist_cons_right_le Costs.unit c (a :: EditScript.src s) (EditScript.tgt t')
          simp only [EditScript.tgt_cons, EditOp.tgt, List.singleton_append,
            EditScript.cost_cons, EditOp.cost, Costs.unit_ins]
          omega
        · simp only [EditScript.src_cons, EditOp.src, List.singleton_append,
            List.cons.injEq] at ht
          rcases ht with ⟨hd_eq, ht'⟩
          have h1 : editDist Costs.unit (a :: EditScript.src s) (c :: EditScript.tgt t') ≤
              (if a = c then 0 else 1) +
                editDist Costs.unit (EditScript.src s) (EditScript.tgt t') :=
            editDist_cons_cons_le Costs.unit a c (EditScript.src s) (EditScript.tgt t')
          have h2 := ih (EditScript.tgt t')
          have h3 : editDist Costs.unit (EditScript.tgt s) (EditScript.tgt t') ≤
              EditScript.cost Costs.unit t' :=
            ht' ▸ editDist_le_cost Costs.unit t'
          have htri_char : (if a = c then 0 else 1) ≤
              (if a = b then 0 else 1) + (if d = c then 0 else 1) := by
            subst hd_eq
            split
            · exact Nat.zero_le _
            · next hac =>
              split
              · next hab =>
                split
                · next hdc => exact absurd (hab.trans hdc) hac
                · omega
              · omega
          simp only [EditScript.tgt_cons, EditOp.tgt, List.singleton_append,
            EditScript.cost_cons, EditOp.cost, Costs.unit_sub]
          omega

/-- Subadditivity of unit-cost edit distance across word concatenation. -/
theorem editDist_unit_append {α : Type*} [DecidableEq α] (x₁ x₂ y₁ y₂ : List α) :
    editDist Costs.unit (x₁ ++ x₂) (y₁ ++ y₂) ≤
      editDist Costs.unit x₁ y₁ + editDist Costs.unit x₂ y₂ := by
  let s := optScript Costs.unit x₁ y₁ ++ optScript Costs.unit x₂ y₂
  have hsrc : EditScript.src s = x₁ ++ x₂ := by
    rw [EditScript.src_append, src_optScript, src_optScript]
  have htgt : EditScript.tgt s = y₁ ++ y₂ := by
    rw [EditScript.tgt_append, tgt_optScript, tgt_optScript]
  have hcost : EditScript.cost Costs.unit s =
      editDist Costs.unit x₁ y₁ + editDist Costs.unit x₂ y₂ := by
    rw [EditScript.cost_append, cost_optScript, cost_optScript]
  calc editDist Costs.unit (x₁ ++ x₂) (y₁ ++ y₂)
      = editDist Costs.unit (EditScript.src s) (EditScript.tgt s) := by rw [hsrc, htgt]
    _ ≤ EditScript.cost Costs.unit s := editDist_le_cost Costs.unit s
    _ = editDist Costs.unit x₁ y₁ + editDist Costs.unit x₂ y₂ := hcost

private theorem count_src_sub_tgt_le_cost {α : Type*} [DecidableEq α] (c : α) (s : EditScript α) :
    (EditScript.src s).count c - (EditScript.tgt s).count c ≤ EditScript.cost Costs.unit s := by
  induction s with
  | nil => simp
  | cons op s ih =>
    rcases op with a | b | ⟨a, b⟩ <;>
      simp only [EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
        EditOp.src, EditOp.tgt, EditOp.cost, Costs.unit_del, Costs.unit_ins, Costs.unit_sub,
        List.singleton_append, List.nil_append, List.count_cons, beq_iff_eq]
    · split_ifs <;> omega
    · split_ifs <;> omega
    · by_cases hac : a = c <;> by_cases hbc : b = c <;> by_cases hab : a = b <;>
        subst_vars <;> simp_all <;> omega

/-- Difference in letter multiplicity is bounded by unit-cost edit distance. -/
theorem count_sub_le_editDist_unit {α : Type*} [DecidableEq α] (c : α) (x y : List α) :
    x.count c - y.count c ≤ editDist Costs.unit x y := by
  have h := count_src_sub_tgt_le_cost c (optScript Costs.unit x y)
  rwa [src_optScript, tgt_optScript, cost_optScript] at h

private def filterOp {α : Type*} (p : α → Bool) : EditOp α → EditScript α
  | .del a => if p a then [.del a] else []
  | .ins b => if p b then [.ins b] else []
  | .sub a b =>
    match p a, p b with
    | true, true => [.sub a b]
    | true, false => [.del a]
    | false, true => [.ins b]
    | false, false => []

private theorem filterOp_single {α : Type*} [DecidableEq α] (p : α → Bool) (op : EditOp α) :
    EditScript.src (filterOp p op) = op.src.filter p ∧
    EditScript.tgt (filterOp p op) = op.tgt.filter p ∧
    EditScript.cost Costs.unit (filterOp p op) ≤ op.cost Costs.unit := by
  rcases op with a | b | ⟨a, b⟩
  · cases hp : p a <;> simp [filterOp, hp, EditOp.src, EditOp.tgt, EditOp.cost]
  · cases hp : p b <;> simp [filterOp, hp, EditOp.src, EditOp.tgt, EditOp.cost]
  · cases hpa : p a <;> cases hpb : p b
    · simp [filterOp, hpa, hpb, EditOp.src, EditOp.tgt, EditOp.cost]
    · have hab : a ≠ b := fun h => by subst h; rw [hpa] at hpb; cases hpb
      simp [filterOp, hpa, hpb, hab, EditOp.src, EditOp.tgt, EditOp.cost]
    · have hab : a ≠ b := fun h => by subst h; rw [hpa] at hpb; cases hpb
      simp [filterOp, hpa, hpb, hab, EditOp.src, EditOp.tgt, EditOp.cost]
    · simp [filterOp, hpa, hpb, EditOp.src, EditOp.tgt, EditOp.cost]

private theorem filterOp_spec {α : Type*} [DecidableEq α] (p : α → Bool) :
    ∀ t : EditScript α,
      EditScript.src (t.flatMap (filterOp p)) = (EditScript.src t).filter p ∧
      EditScript.tgt (t.flatMap (filterOp p)) = (EditScript.tgt t).filter p ∧
      EditScript.cost Costs.unit (t.flatMap (filterOp p)) ≤ EditScript.cost Costs.unit t
  | [] => by simp
  | op :: t => by
    obtain ⟨s1, s2, s3⟩ := filterOp_single p op
    obtain ⟨ih1, ih2, ih3⟩ := filterOp_spec p t
    rw [List.flatMap_cons, EditScript.src_append, EditScript.tgt_append, EditScript.cost_append,
      EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons,
      List.filter_append, List.filter_append, s1, s2, ih1, ih2]
    exact ⟨rfl, rfl, Nat.add_le_add s3 ih3⟩

/-- Filtering by any Boolean predicate `p` does not increase unit-cost edit distance. -/
theorem editDist_unit_filter_le {α : Type*} [DecidableEq α] (p : α → Bool) (x y : List α) :
    editDist Costs.unit (x.filter p) (y.filter p) ≤ editDist Costs.unit x y := by
  obtain ⟨hsrc, htgt, hcost⟩ := filterOp_spec p (optScript Costs.unit x y)
  rw [src_optScript] at hsrc
  rw [tgt_optScript] at htgt
  rw [cost_optScript] at hcost
  let sf := (optScript Costs.unit x y).flatMap (filterOp p)
  calc editDist Costs.unit (x.filter p) (y.filter p)
      = editDist Costs.unit (EditScript.src sf) (EditScript.tgt sf) := by rw [hsrc, htgt]
    _ ≤ EditScript.cost Costs.unit sf := editDist_le_cost Costs.unit sf
    _ ≤ editDist Costs.unit x y := hcost

/-! ### 2. Common-target deletion-substitution characterization -/

/-- An edit script uses only deletions and substitutions (no insertions). -/
def IsDelSubScript {α : Type*} (s : EditScript α) : Prop :=
  ∀ op ∈ s, ∀ b : α, op ≠ .ins b

@[simp] private theorem isDelSubScript_nil {α : Type*} :
    IsDelSubScript ([] : EditScript α) :=
  fun _ h => nomatch h

private theorem isDelSubScript_cons {α : Type*} {op : EditOp α} {s : EditScript α} :
    IsDelSubScript (op :: s) ↔ (∀ b : α, op ≠ .ins b) ∧ IsDelSubScript s :=
  List.forall_mem_cons

private def midWord {α : Type*} : EditScript α → List α
  | [] => []
  | .del _ :: s => midWord s
  | .ins _ :: s => midWord s
  | .sub _ b :: s => b :: midWord s

private def leftDelSub {α : Type*} : EditScript α → EditScript α
  | [] => []
  | .del a :: s => .del a :: leftDelSub s
  | .ins _ :: s => leftDelSub s
  | .sub a b :: s => .sub a b :: leftDelSub s

private def rightDelSub {α : Type*} : EditScript α → EditScript α
  | [] => []
  | .del _ :: s => rightDelSub s
  | .ins b :: s => .del b :: rightDelSub s
  | .sub _ b :: s => .sub b b :: rightDelSub s

private theorem leftRightDelSub_spec {α : Type*} [DecidableEq α] :
    ∀ s : EditScript α,
      IsDelSubScript (leftDelSub s) ∧ IsDelSubScript (rightDelSub s) ∧
      EditScript.src (leftDelSub s) = EditScript.src s ∧
      EditScript.tgt (leftDelSub s) = midWord s ∧
      EditScript.src (rightDelSub s) = EditScript.tgt s ∧
      EditScript.tgt (rightDelSub s) = midWord s ∧
      EditScript.cost Costs.unit (leftDelSub s) + EditScript.cost Costs.unit (rightDelSub s) =
        EditScript.cost Costs.unit s
  | [] => by simp [leftDelSub, rightDelSub, midWord]
  | .del a :: s => by
    obtain ⟨hl, hr, hsl, htl, hsr, htr, hc⟩ := leftRightDelSub_spec s
    refine ⟨?_, hr, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [leftDelSub, isDelSubScript_cons]
      exact ⟨(fun _ h => nomatch h), hl⟩
    · simp [leftDelSub, EditOp.src, hsl]
    · simp [leftDelSub, midWord, EditOp.tgt, htl]
    · simp [rightDelSub, EditOp.tgt, hsr]
    · simp [rightDelSub, midWord, htr]
    · simp only [leftDelSub, rightDelSub, EditScript.cost_cons, EditOp.cost, Costs.unit_del]; omega
  | .ins b :: s => by
    obtain ⟨hl, hr, hsl, htl, hsr, htr, hc⟩ := leftRightDelSub_spec s
    refine ⟨hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [rightDelSub, isDelSubScript_cons]
      exact ⟨(fun _ h => nomatch h), hr⟩
    · simp [leftDelSub, EditOp.src, hsl]
    · simp [leftDelSub, midWord, htl]
    · simp [rightDelSub, EditOp.src, EditOp.tgt, hsr]
    · simp [rightDelSub, midWord, EditOp.tgt, htr]
    · simp only [leftDelSub, rightDelSub, EditScript.cost_cons, EditOp.cost,
        Costs.unit_del, Costs.unit_ins]; omega
  | .sub a b :: s => by
    obtain ⟨hl, hr, hsl, htl, hsr, htr, hc⟩ := leftRightDelSub_spec s
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [leftDelSub, isDelSubScript_cons]
      exact ⟨(fun _ h => nomatch h), hl⟩
    · simp only [rightDelSub, isDelSubScript_cons]
      exact ⟨(fun _ h => nomatch h), hr⟩
    · simp [leftDelSub, EditOp.src, hsl]
    · simp [leftDelSub, midWord, EditOp.tgt, htl]
    · simp [rightDelSub, EditOp.src, EditOp.tgt, hsr]
    · simp [rightDelSub, midWord, EditOp.tgt, htr]
    · simp only [leftDelSub, rightDelSub, EditScript.cost_cons, EditOp.cost,
        Costs.unit_sub, ↓reduceIte, zero_add]; omega

/-- Unit-cost edit distance equals the minimum over all common target words `z` of the combined cost
of deletion-substitution scripts transforming `x` to `z` and `y` to `z`. -/
theorem isLeast_delSub_common_target {α : Type*} [DecidableEq α] (x y : List α) :
    IsLeast
      {c : ℕ | ∃ (z : List α) (s₁ s₂ : EditScript α),
        IsDelSubScript s₁ ∧ IsDelSubScript s₂ ∧
        EditScript.src s₁ = x ∧ EditScript.tgt s₁ = z ∧
        EditScript.src s₂ = y ∧ EditScript.tgt s₂ = z ∧
        EditScript.cost Costs.unit s₁ + EditScript.cost Costs.unit s₂ = c}
      (editDist Costs.unit x y) := by
  refine ⟨?_, ?_⟩
  · set s := optScript Costs.unit x y
    obtain ⟨hl, hr, hsl, htl, hsr, htr, hc⟩ := leftRightDelSub_spec s
    exact ⟨midWord s, leftDelSub s, rightDelSub s, hl, hr,
      hsl.trans (src_optScript _ _ _), htl,
      hsr.trans (tgt_optScript _ _ _), htr,
      hc.trans (cost_optScript _ _ _)⟩
  · rintro c ⟨z, s₁, s₂, -, -, rfl, rfl, rfl, htz, rfl⟩
    have h₁ := editDist_le_cost (Costs.unit (α := α)) s₁
    have h₂ : editDist Costs.unit (EditScript.src s₂) (EditScript.tgt s₁) ≤
        EditScript.cost Costs.unit s₂ := htz ▸ editDist_le_cost Costs.unit s₂
    calc editDist Costs.unit (EditScript.src s₁) (EditScript.src s₂)
        ≤ editDist Costs.unit (EditScript.src s₁) (EditScript.tgt s₁) +
            editDist Costs.unit (EditScript.tgt s₁) (EditScript.src s₂) :=
          editDist_unit_triangle _ _ _
      _ = editDist Costs.unit (EditScript.src s₁) (EditScript.tgt s₁) +
            editDist Costs.unit (EditScript.src s₂) (EditScript.tgt s₁) := by
          rw [editDist_unit_comm (EditScript.tgt s₁) (EditScript.src s₂)]
      _ ≤ EditScript.cost Costs.unit s₁ + EditScript.cost Costs.unit s₂ := Nat.add_le_add h₁ h₂

/-! ### 3. Pattern matching distance and fresh-guard reduction to edit distance -/

/-- All contiguous substrings (`List.IsInfix` witnesses) `(t.drop i).take k` of a word `t`. -/
def contiguousSubseqs {α : Type*} (t : List α) : List (List α) :=
  (List.range (t.length + 1)).flatMap fun i =>
    (List.range (t.length + 1)).map fun k => (t.drop i).take k

private theorem nil_mem_contiguousSubseqs {α : Type*} (t : List α) :
    [] ∈ contiguousSubseqs t := by
  rw [contiguousSubseqs, List.mem_flatMap]
  exact ⟨0, List.mem_range.mpr (Nat.succ_pos _),
    List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), by simp⟩⟩

private theorem mem_contiguousSubseqs_iff_infix {α : Type*} {x t : List α} :
    x ∈ contiguousSubseqs t ↔ x <:+: t := by
  rw [contiguousSubseqs]
  constructor
  · rintro h
    rcases List.mem_flatMap.mp h with ⟨i, _, hk⟩
    rcases List.mem_map.mp hk with ⟨k, _, rfl⟩
    refine ⟨t.take i, (t.drop i).drop k, ?_⟩
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · rintro ⟨u, w, rfl⟩
    rw [List.mem_flatMap]
    have hu : u.length < (u ++ x ++ w).length + 1 := by simp; omega
    have hx : x.length < (u ++ x ++ w).length + 1 := by simp; omega
    refine ⟨u.length, List.mem_range.mpr hu,
      List.mem_map.mpr ⟨x.length, List.mem_range.mpr hx, ?_⟩⟩
    rw [List.append_assoc, List.drop_left, List.take_left]

/-- Pattern matching distance from a pattern `p` to a text `t`: the minimum unit-cost edit distance
`editDist Costs.unit p x` over all contiguous substrings `x <:+: t`. -/
def patternDist {α : Type*} [DecidableEq α] (p t : List α) : ℕ :=
  ((contiguousSubseqs t).map (editDist Costs.unit p)).min?.getD p.length

private theorem patternDist_le_of_infix {α : Type*} [DecidableEq α] {p t x : List α}
    (hx : x <:+: t) : patternDist p t ≤ editDist Costs.unit p x := by
  have hmem : editDist Costs.unit p x ∈ (contiguousSubseqs t).map (editDist Costs.unit p) :=
    List.mem_map.mpr ⟨x, mem_contiguousSubseqs_iff_infix.mpr hx, rfl⟩
  have hne : (contiguousSubseqs t).map (editDist Costs.unit p) ≠ [] :=
    List.ne_nil_of_mem hmem
  rcases hmin : ((contiguousSubseqs t).map (editDist Costs.unit p)).min? with _ | v
  · exact absurd (List.min?_eq_none_iff.mp hmin) hne
  · simp only [patternDist, hmin, Option.getD_some]
    exact (List.min?_eq_some_iff.mp hmin).2 _ hmem

private theorem exists_infix_editDist_eq_patternDist {α : Type*} [DecidableEq α]
    (p t : List α) : ∃ x, x <:+: t ∧ editDist Costs.unit p x = patternDist p t := by
  have hnil : editDist Costs.unit p [] ∈ (contiguousSubseqs t).map (editDist Costs.unit p) :=
    List.mem_map.mpr ⟨[], nil_mem_contiguousSubseqs t, rfl⟩
  have hne : (contiguousSubseqs t).map (editDist Costs.unit p) ≠ [] := List.ne_nil_of_mem hnil
  rcases hmin : ((contiguousSubseqs t).map (editDist Costs.unit p)).min? with _ | v
  · exact absurd (List.min?_eq_none_iff.mp hmin) hne
  · simp only [patternDist, hmin, Option.getD_some]
    obtain ⟨hmem, _⟩ := List.min?_eq_some_iff.mp hmin
    obtain ⟨x, hx, hdist⟩ := List.mem_map.mp hmem
    exact ⟨x, mem_contiguousSubseqs_iff_infix.mp hx, hdist⟩

/-- `patternDist p t` is the least value of `editDist Costs.unit p x` over `x <:+: t`. -/
theorem isLeast_patternDist {α : Type*} [DecidableEq α] (p t : List α) :
    IsLeast {c : ℕ | ∃ x : List α, x <:+: t ∧ editDist Costs.unit p x = c} (patternDist p t) := by
  refine ⟨exists_infix_editDist_eq_patternDist p t, ?_⟩
  rintro c ⟨x, hx, rfl⟩
  exact patternDist_le_of_infix hx

private def splitSrcAux {α : Type*} : ℕ → EditScript α → EditScript α × EditScript α
  | 0, s => ([], s)
  | _ + 1, [] => ([], [])
  | k + 1, .ins b :: s =>
    let p := splitSrcAux (k + 1) s
    (.ins b :: p.1, p.2)
  | k + 1, .del a :: s =>
    let p := splitSrcAux k s
    (.del a :: p.1, p.2)
  | k + 1, .sub a b :: s =>
    let p := splitSrcAux k s
    (.sub a b :: p.1, p.2)

private theorem splitSrcAux_spec {α : Type*} [DecidableEq α] :
    ∀ (s : EditScript α) (u v : List α),
      EditScript.src s = u ++ v →
      EditScript.src (splitSrcAux u.length s).1 = u ∧
      EditScript.src (splitSrcAux u.length s).2 = v ∧
      EditScript.tgt (splitSrcAux u.length s).1 ++
        EditScript.tgt (splitSrcAux u.length s).2 = EditScript.tgt s ∧
      EditScript.cost Costs.unit (splitSrcAux u.length s).1 +
        EditScript.cost Costs.unit (splitSrcAux u.length s).2 = EditScript.cost Costs.unit s
  | [], u, v, hsrc => by
    simp only [EditScript.src_nil, eq_comm, List.append_eq_nil_iff] at hsrc
    rcases hsrc with ⟨rfl, rfl⟩
    simp [splitSrcAux]
  | op :: s, [], v, hsrc => by
    simp [splitSrcAux, hsrc]
  | .del a :: s, c :: u, v, hsrc => by
    simp only [EditScript.src_cons, EditOp.src, List.cons_append, List.nil_append,
      List.cons.injEq] at hsrc
    rcases hsrc with ⟨rfl, hsrc'⟩
    obtain ⟨h1, h2, h3, h4⟩ := splitSrcAux_spec s u v hsrc'
    refine ⟨by simp [splitSrcAux, EditOp.src, h1], by simpa [splitSrcAux] using h2,
      by simp [splitSrcAux, EditOp.tgt, h3], ?_⟩
    simp only [List.length_cons, splitSrcAux, EditScript.cost_cons]; omega
  | .ins b :: s, c :: u, v, hsrc => by
    simp only [EditScript.src_cons, EditOp.src, List.nil_append] at hsrc
    obtain ⟨h1, h2, h3, h4⟩ := splitSrcAux_spec s (c :: u) v hsrc
    simp only [List.length_cons] at h1 h2 h3 h4
    refine ⟨by simp [splitSrcAux, EditOp.src, h1], by simpa [splitSrcAux] using h2,
      by simp [splitSrcAux, EditOp.tgt, h3], ?_⟩
    simp only [List.length_cons, splitSrcAux, EditScript.cost_cons]; omega
  | .sub a b :: s, c :: u, v, hsrc => by
    simp only [EditScript.src_cons, EditOp.src, List.cons_append, List.nil_append,
      List.cons.injEq] at hsrc
    rcases hsrc with ⟨rfl, hsrc'⟩
    obtain ⟨h1, h2, h3, h4⟩ := splitSrcAux_spec s u v hsrc'
    refine ⟨by simp [splitSrcAux, EditOp.src, h1], by simpa [splitSrcAux] using h2,
      by simp [splitSrcAux, EditOp.tgt, h3], ?_⟩
    simp only [List.length_cons, splitSrcAux, EditScript.cost_cons]; omega

private theorem exists_split_src_three {α : Type*} [DecidableEq α] (s : EditScript α)
    (u₁ u₂ u₃ : List α) (hsrc : EditScript.src s = u₁ ++ u₂ ++ u₃) :
    ∃ s₁ s₂ s₃ : EditScript α,
      EditScript.src s₁ = u₁ ∧ EditScript.src s₂ = u₂ ∧ EditScript.src s₃ = u₃ ∧
      EditScript.tgt s₁ ++ EditScript.tgt s₂ ++ EditScript.tgt s₃ = EditScript.tgt s ∧
      EditScript.cost Costs.unit s₁ + EditScript.cost Costs.unit s₂ +
        EditScript.cost Costs.unit s₃ = EditScript.cost Costs.unit s := by
  rw [List.append_assoc] at hsrc
  obtain ⟨h1, h23, ht1, hc1⟩ := splitSrcAux_spec s u₁ (u₂ ++ u₃) hsrc
  set s₁ := (splitSrcAux u₁.length s).1
  set s₂₃ := (splitSrcAux u₁.length s).2
  obtain ⟨h2, h3, ht2, hc2⟩ := splitSrcAux_spec s₂₃ u₂ u₃ h23
  refine ⟨s₁, (splitSrcAux u₂.length s₂₃).1, (splitSrcAux u₂.length s₂₃).2,
    h1, h2, h3, ?_, by omega⟩
  rw [List.append_assoc, ht2, ht1]

private theorem editDist_unit_replicate_le {α : Type*} [DecidableEq α] (g : α) :
    ∀ k : List α, editDist Costs.unit (List.replicate k.length g) k ≤ k.length
  | [] => by simp
  | c :: k => by
    rw [List.length_cons, List.replicate_succ]
    have h1 := editDist_cons_cons_le (Costs.unit (α := α)) g c (List.replicate k.length g) k
    have ih := editDist_unit_replicate_le g k
    simp only [Costs.unit_sub] at h1
    split_ifs at h1 <;> omega

/-- **Fresh-guard reduction from pattern matching distance to edit distance**: if a guard symbol `g`
does not occur in `t`, then flanking `p` on both sides with `|t|` copies of `g` shifts unit-cost
edit distance by `2 * |t|` above `patternDist p t`:
`editDist Costs.unit (g^{|t|} ++ p ++ g^{|t|}) t = 2 * |t| + patternDist p t`. -/
theorem editDist_unit_guard_pad_eq_patternDist {α : Type*} [DecidableEq α]
    (g : α) (p t : List α) (hg : ∀ c ∈ t, c ≠ g) :
    editDist Costs.unit (List.replicate t.length g ++ p ++ List.replicate t.length g) t =
      2 * t.length + patternDist p t := by
  set M := t.length
  apply le_antisymm
  · obtain ⟨x, ⟨u, w, ht⟩, hdist⟩ := exists_infix_editDist_eq_patternDist p t
    have hM_eq : u.length + x.length + w.length = M := by
      have := congrArg List.length ht
      simp only [List.length_append] at this
      omega
    have hu_split : List.replicate M g =
        List.replicate (M - u.length) g ++ List.replicate u.length g := by
      rw [← List.replicate_add]; congr 1; omega
    have hw_split : List.replicate M g =
        List.replicate w.length g ++ List.replicate (M - w.length) g := by
      rw [← List.replicate_add]; congr 1; omega
    have hleft_ub : editDist Costs.unit (List.replicate M g) u ≤ M := by
      rw [hu_split]
      have h1 : editDist Costs.unit
          (List.replicate (M - u.length) g ++ List.replicate u.length g) ([] ++ u) ≤
          editDist Costs.unit (List.replicate (M - u.length) g) [] +
            editDist Costs.unit (List.replicate u.length g) u :=
        editDist_unit_append _ _ _ _
      have hdel : editDist Costs.unit (List.replicate (M - u.length) g) [] = M - u.length := by
        simp [editDist_nil_right]
      have hrep := editDist_unit_replicate_le g u
      simp only [List.nil_append, hdel] at h1
      omega
    have hright_ub : editDist Costs.unit (List.replicate M g) w ≤ M := by
      rw [hw_split]
      have h1 : editDist Costs.unit
          (List.replicate w.length g ++ List.replicate (M - w.length) g) (w ++ []) ≤
          editDist Costs.unit (List.replicate w.length g) w +
            editDist Costs.unit (List.replicate (M - w.length) g) [] :=
        editDist_unit_append _ _ _ _
      have hdel : editDist Costs.unit (List.replicate (M - w.length) g) [] = M - w.length := by
        simp [editDist_nil_right]
      have hrep := editDist_unit_replicate_le g w
      simp only [List.append_nil, hdel] at h1
      omega
    have hrhs_eq : editDist Costs.unit (List.replicate M g ++ p ++ List.replicate M g) t =
        editDist Costs.unit (List.replicate M g ++ p ++ List.replicate M g) (u ++ x ++ w) :=
      congrArg _ ht.symm
    have happ1 := editDist_unit_append
      (List.replicate M g ++ p) (List.replicate M g) (u ++ x) w
    have happ2 := editDist_unit_append (List.replicate M g) p u x
    rw [hrhs_eq]
    omega
  · let s := optScript Costs.unit (List.replicate M g ++ p ++ List.replicate M g) t
    obtain ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, ht_all, hc_all⟩ :=
      exists_split_src_three s (List.replicate M g) p (List.replicate M g) (src_optScript _ _ _)
    rw [tgt_optScript] at ht_all
    rw [cost_optScript] at hc_all
    have hcnt1_0 : (EditScript.tgt s₁).count g = 0 := by
      refine List.count_eq_zero.mpr fun hmem => hg g ?_ rfl
      rw [← ht_all]
      exact List.mem_append_left _ (List.mem_append_left _ hmem)
    have hcnt3_0 : (EditScript.tgt s₃).count g = 0 := by
      refine List.count_eq_zero.mpr fun hmem => hg g ?_ rfl
      rw [← ht_all]
      exact List.mem_append_right _ hmem
    have hb1 := count_src_sub_tgt_le_cost g s₁
    rw [hs₁, List.count_replicate_self, hcnt1_0, Nat.sub_zero] at hb1
    have hb3 := count_src_sub_tgt_le_cost g s₃
    rw [hs₃, List.count_replicate_self, hcnt3_0, Nat.sub_zero] at hb3
    have hb2_pat : patternDist p t ≤ editDist Costs.unit p (EditScript.tgt s₂) :=
      patternDist_le_of_infix ⟨EditScript.tgt s₁, EditScript.tgt s₃, ht_all⟩
    have hb2_cost : editDist Costs.unit p (EditScript.tgt s₂) ≤ EditScript.cost Costs.unit s₂ := by
      simpa [hs₂] using editDist_le_cost (Costs.unit (α := α)) s₂
    omega

end CslibFrontier.Algorithms.Lean.EditDistance
