/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.StateTransition.Amortized
public import CslibFrontier.DataStructure.StateTransition.StepFunction
public import Mathlib.Data.Nat.Log

/-!
# Polymorphically Recursive 2-3 Finger Trees and Amortized Sequence Complexity

This module formalizes purely functional 2-3 finger trees
via polymorphic recursion, proves their list semantics for `cons`, `snoc`, `glue`, and `append`,
establishes constant amortized complexity (`≤ 3`) for `cons` and `snoc` (paired with an adaptive
`Cslib.DataStructure.Amortized` deque certificate), and proves logarithmic
`O(log min(|q₁|, |q₂|))` amortized complexity for three-way `glue` and binary `append` under the
digit-danger potential function.

## Main definitions

* `Digit`: 1-to-3 element end buffer with `toList` and `danger`.
* `Node`: internal 2-3 branch node (`pair` or `triple`) with `listToList` and `ofList`.
* `FingerTree`: polymorphically recursive 2-3 finger tree with `toList`, `potential`, `cons`,
  `consCost`, `snoc`, `snocCost`, `foldrCost`, `foldlCost`, `glue`, `glueCost`, `append`, and
  `appendCost`.
* `DequeOp`, `dequeSpec`, `dequeImpl`: adaptive double-ended insertion specification and verified
  finger-tree implementation.

## Main results

* `FingerNode.length_ofList_eq`, `FingerNode.listToList_ofList`: exact `⌊(n + 2) / 3⌋` node count
  and list round-trip for every `xs` with `xs.length ≠ 1`.
* `FingerTree.toList_cons`, `FingerTree.toList_snoc`, `FingerTree.toList_glue`,
  `FingerTree.toList_append`: exact list semantics for all four sequence operations.
* `FingerTree.consCost_add_potential_le`, `FingerTree.snocCost_add_potential_le`,
  `deque_amortized`, `deque_executes_total_le_of_empty`: uniform constant amortized charge `3`
  for double-ended insertions across arbitrary adaptive clients.
* `FingerTree.glueCost_add_potential_le_min`, `FingerTree.glueCost_add_potential_le`,
  `FingerTree.appendCost_add_potential_le_min`: logarithmic amortized concatenation bounds
  `Nat.log 2 (max (min |q₁| |q₂|) 1) + 14` and `Nat.log 2 (max (|q₁| + |q₂|) 2) + 14`.
-/

public section

namespace CslibFrontier.DataStructure

open Cslib.DataStructure

universe u v

/-- A prefix or suffix finger-tree digit holding one, two, or three elements. -/
inductive FingerDigit (α : Type u) : Type u where
  /-- One-element digit. -/
  | one : α → FingerDigit α
  /-- Safe two-element digit. -/
  | two : α → α → FingerDigit α
  /-- Three-element digit. -/
  | three : α → α → α → FingerDigit α
  deriving DecidableEq, Repr

namespace FingerDigit

variable {α : Type u}

/-- Underlying list of elements (length `1` to `3`). -/
@[expose] def toList : FingerDigit α → List α
  | .one x => [x]
  | .two x y => [x, y]
  | .three x y z => [x, y, z]

/-- Every digit stores between `1` and `3` elements. -/
theorem length_toList_bounds (d : FingerDigit α) : 1 ≤ d.toList.length ∧ d.toList.length ≤ 3 := by
  cases d <;> simp [toList]

/-- Digit danger (`0` on `two`, `1` on `one` or `three`). -/
@[expose] def danger : FingerDigit α → ℕ
  | .one _ => 1
  | .two _ _ => 0
  | .three _ _ _ => 1

end FingerDigit

/-- An internal 2-3 finger-tree node grouping two or three elements at the next spine depth. -/
inductive FingerNode (α : Type u) : Type u where
  /-- Binary node. -/
  | pair : α → α → FingerNode α
  /-- Ternary node. -/
  | triple : α → α → α → FingerNode α
  deriving DecidableEq, Repr

namespace FingerNode

variable {α : Type u}

/-- Flatten a list of 2-3 nodes into its list of elements. -/
@[expose] def listToList : List (FingerNode α) → List α
  | [] => []
  | .pair a b :: xs => a :: b :: listToList xs
  | .triple a b c :: xs => a :: b :: c :: listToList xs

@[simp]
theorem listToList_append (xs ys : List (FingerNode α)) :
    listToList (xs ++ ys) = listToList xs ++ listToList ys := by
  induction xs with
  | nil => rfl
  | cons t _ ih => cases t <;> simp [listToList, ih]

/-- Flattening `k` 2-3 nodes yields between `2 * k` and `3 * k` elements. -/
theorem length_listToList_bounds (xs : List (FingerNode α)) :
    2 * xs.length ≤ (listToList xs).length ∧ (listToList xs).length ≤ 3 * xs.length := by
  induction xs with
  | nil => simp [listToList]
  | cons t _ ih =>
    cases t <;> simp only [listToList, List.length_cons] <;> omega

/-- Partition any list of length `≠ 1` into 2-3 nodes (totalized to `[]` on singletons). -/
@[expose] def ofList : List α → List (FingerNode α)
  | [] => []
  | [_] => []
  | [x, y] => [.pair x y]
  | [x, y, z, w] => [.pair x y, .pair z w]
  | x :: y :: z :: xs => .triple x y z :: ofList xs

/-- Exact node count `(ofList xs).length = (xs.length + 2) / 3` whenever `xs.length ≠ 1`. -/
theorem length_ofList_eq : ∀ {xs : List α}, xs.length ≠ 1 →
    (ofList xs).length = (xs.length + 2) / 3
  | [], _ => by simp [ofList]
  | [_], h => absurd rfl h
  | [_, _], _ => by simp [ofList]
  | [_, _, _], _ => by simp [ofList]
  | [_, _, _, _], _ => by simp [ofList]
  | _ :: _ :: _ :: w :: u :: xs, _ => by
    have ih := length_ofList_eq (xs := w :: u :: xs) (by simp)
    simp only [ofList, List.length_cons] at ih ⊢
    omega

/-- Partitioning `xs` with `xs.length ≤ 9` yields at most `3` nodes. -/
theorem length_ofList_le_three {xs : List α} (h9 : xs.length ≤ 9) : (ofList xs).length ≤ 3 := by
  by_cases h1 : xs.length = 1
  · rcases xs with _ | ⟨_, _ | _⟩ <;> simp_all [ofList]
  · rw [length_ofList_eq h1]; omega

/-- Flattening `ofList xs` recovers `xs` whenever `xs.length ≠ 1`. -/
theorem listToList_ofList : ∀ {xs : List α}, xs.length ≠ 1 → listToList (ofList xs) = xs
  | [], _ => rfl
  | [_], h => absurd rfl h
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | x :: y :: z :: w :: u :: xs, _ => by
    simp only [ofList, listToList, listToList_ofList (xs := w :: u :: xs) (by simp)]

end FingerNode

/-- Polymorphically recursive 2-3 finger tree. -/
inductive FingerTree : Type u → Type (u + 1) where
  /-- Empty sequence. -/
  | nil {α : Type u} : FingerTree α
  /-- Singleton sequence. -/
  | unit {α : Type u} : α → FingerTree α
  /-- Compound tree with prefix digit, nested spine of 2-3 nodes, and suffix digit. -/
  | more {α : Type u} :
      FingerDigit α → FingerTree (FingerNode α) → FingerDigit α → FingerTree α

namespace FingerTree

instance instInhabited (α : Type u) : Inhabited (FingerTree α) := ⟨.nil⟩

/-- Sequence of elements stored in a finger tree. -/
@[expose] def toList : {α : Type u} → FingerTree α → List α
  | _, .nil => []
  | _, .unit x => [x]
  | _, .more u q v => u.toList ++ FingerNode.listToList q.toList ++ v.toList

/-- Digit-danger potential summed across all spine levels. -/
@[expose] def potential : {α : Type u} → FingerTree α → ℕ
  | _, .nil => 0
  | _, .unit _ => 0
  | _, .more pr m sf => pr.danger + m.potential + sf.danger

/-- Left insertion into a 2-3 finger tree. -/
@[expose] def cons : {α : Type u} → α → FingerTree α → FingerTree α
  | _, x, .nil => .unit x
  | _, x, .unit y => .more (.one x) .nil (.one y)
  | _, x, .more (.one y) q u => .more (.two x y) q u
  | _, x, .more (.two y z) q u => .more (.three x y z) q u
  | _, x, .more (.three y z w) q u => .more (.two x y) (cons (.pair z w) q) u

/-- Recursive step cost of `cons`. -/
@[expose] def consCost : {α : Type u} → α → FingerTree α → ℕ
  | _, _, .nil => 1
  | _, _, .unit _ => 1
  | _, _, .more (.one _) _ _ => 1
  | _, _, .more (.two _ _) _ _ => 1
  | _, _, .more (.three _ z w) q _ => 1 + consCost (.pair z w) q

@[simp]
theorem toList_cons {α : Type u} (x : α) (t : FingerTree α) :
    (cons x t).toList = x :: t.toList := by
  induction t with
  | nil => rfl
  | unit _ => rfl
  | more pr _ _ ih =>
    cases pr with
    | one _ => rfl
    | two _ _ => rfl
    | three _ z w => simp [cons, toList, FingerDigit.toList, FingerNode.listToList, ih (.pair z w)]

/-- Constant amortized cost bound (`≤ 3`) for `cons`. -/
theorem consCost_add_potential_le {α : Type u} (x : α) (t : FingerTree α) :
    consCost x t + (cons x t).potential ≤ 3 + t.potential := by
  induction t with
  | nil => simp [consCost, cons, potential]
  | unit _ => simp [consCost, cons, potential, FingerDigit.danger]
  | more pr _ _ ih =>
    cases pr with
    | one _ => simp only [consCost, cons, potential, FingerDigit.danger]; omega
    | two _ _ => simp only [consCost, cons, potential, FingerDigit.danger]; omega
    | three _ z w =>
      have hq := ih (.pair z w)
      simp only [consCost, cons, potential, FingerDigit.danger]
      omega

/-- Right insertion into a 2-3 finger tree. -/
@[expose] def snoc : {α : Type u} → FingerTree α → α → FingerTree α
  | _, .nil, x => .unit x
  | _, .unit x, y => .more (.one x) .nil (.one y)
  | _, .more u q (.one x), y => .more u q (.two x y)
  | _, .more u q (.two x y), z => .more u q (.three x y z)
  | _, .more u q (.three x y z), w => .more u (snoc q (.pair x y)) (.two z w)

/-- Recursive step cost of `snoc`. -/
@[expose] def snocCost : {α : Type u} → FingerTree α → α → ℕ
  | _, .nil, _ => 1
  | _, .unit _, _ => 1
  | _, .more _ _ (.one _), _ => 1
  | _, .more _ _ (.two _ _), _ => 1
  | _, .more _ q (.three x y _), _ => 1 + snocCost q (.pair x y)

@[simp]
theorem toList_snoc {α : Type u} (q : FingerTree α) (x : α) :
    (snoc q x).toList = q.toList ++ [x] := by
  induction q with
  | nil => rfl
  | unit _ => rfl
  | more _ _ sf ih =>
    cases sf with
    | one _ => simp [snoc, toList, FingerDigit.toList]
    | two _ _ => simp [snoc, toList, FingerDigit.toList]
    | three a b _ =>
      simp [snoc, toList, FingerDigit.toList, FingerNode.listToList, ih (.pair a b),
        List.append_assoc]

/-- Constant amortized cost bound (`≤ 3`) for `snoc`. -/
theorem snocCost_add_potential_le {α : Type u} (q : FingerTree α) (x : α) :
    snocCost q x + (snoc q x).potential ≤ 3 + q.potential := by
  induction q with
  | nil => simp [snocCost, snoc, potential]
  | unit _ => simp [snocCost, snoc, potential, FingerDigit.danger]
  | more _ _ sf ih =>
    cases sf with
    | one _ => simp only [snocCost, snoc, potential, FingerDigit.danger]; omega
    | two _ _ => simp only [snocCost, snoc, potential, FingerDigit.danger]; omega
    | three a b _ =>
      have hq := ih (.pair a b)
      simp only [snocCost, snoc, potential, FingerDigit.danger]
      omega

/-- Higher-order step cost of `List.foldr`. -/
@[expose] def foldrCost {α : Type u} {β : Type v}
    (f : α → β → β) (fT : α → β → ℕ) (b : β) : List α → ℕ
  | [] => 1
  | x :: xs => fT x (xs.foldr f b) + foldrCost f fT b xs

/-- Higher-order step cost of `List.foldl`. -/
@[expose] def foldlCost {α : Type u} {β : Type v}
    (f : β → α → β) (fT : β → α → ℕ) (a : β) : List α → ℕ
  | [] => 1
  | x :: xs => fT a x + foldlCost f fT (f a x) xs

/-- Amortized bound for right-folding `cons`. -/
theorem foldrCost_cons_add_potential_le {α : Type u} (q : FingerTree α) (xs : List α) :
    foldrCost cons consCost q xs + (xs.foldr cons q).potential ≤
      3 * xs.length + 1 + q.potential := by
  induction xs with
  | nil => simp [foldrCost]
  | cons x xs ih =>
    have hs := consCost_add_potential_le x (xs.foldr cons q)
    simp only [foldrCost, List.foldr_cons, List.length_cons]
    omega

/-- Amortized bound for left-folding `snoc`. -/
theorem foldlCost_snoc_add_potential_le {α : Type u} (q : FingerTree α) (xs : List α) :
    foldlCost snoc snocCost q xs + (xs.foldl snoc q).potential ≤
      3 * xs.length + 1 + q.potential := by
  induction xs generalizing q with
  | nil => simp [foldlCost]
  | cons x xs ih =>
    have hs := snocCost_add_potential_le q x
    have ht := ih (snoc q x)
    simp only [foldlCost, List.foldl_cons, List.length_cons]
    omega

/-- Three-way concatenation of two 2-3 finger trees across a middle list. -/
@[expose] def glue : {α : Type u} → FingerTree α → List α → FingerTree α → FingerTree α
  | _, .nil, xs, q₂ => xs.foldr cons q₂
  | _, q₁, xs, .nil => xs.foldl snoc q₁
  | _, .unit x, xs, q₂ => (x :: xs).foldr cons q₂
  | _, q₁, xs, .unit x => snoc (xs.foldl snoc q₁) x
  | _, .more u₁ q₁ v₁, xs, .more u₂ q₂ v₂ =>
    .more u₁ (glue q₁ (FingerNode.ofList (v₁.toList ++ xs ++ u₂.toList)) q₂) v₂

/-- Binary finger-tree concatenation. -/
@[expose] def append {α : Type u} (q₁ q₂ : FingerTree α) : FingerTree α := glue q₁ [] q₂

/-- Recursive step cost of `glue`. -/
@[expose] def glueCost : {α : Type u} → FingerTree α → List α → FingerTree α → ℕ
  | _, .nil, xs, q₂ => 1 + foldrCost cons consCost q₂ xs
  | _, q₁, xs, .nil => 1 + foldlCost snoc snocCost q₁ xs
  | _, .unit x, xs, q₂ => 1 + foldrCost cons consCost q₂ (x :: xs)
  | _, q₁, xs, .unit x => 1 + snocCost (xs.foldl snoc q₁) x + foldlCost snoc snocCost q₁ xs
  | _, .more _ q₁ v₁, xs, .more u₂ q₂ _ =>
    1 + glueCost q₁ (FingerNode.ofList (v₁.toList ++ xs ++ u₂.toList)) q₂

/-- Recursive step cost of `append`. -/
@[expose] def appendCost {α : Type u} (q₁ q₂ : FingerTree α) : ℕ := glueCost q₁ [] q₂

private theorem toList_foldr_cons {α : Type u} (q : FingerTree α) (xs : List α) :
    (xs.foldr cons q).toList = xs ++ q.toList := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem toList_foldl_snoc {α : Type u} (q : FingerTree α) (xs : List α) :
    (xs.foldl snoc q).toList = q.toList ++ xs := by
  induction xs generalizing q with
  | nil => simp
  | cons _ _ ih => simp [ih, List.append_assoc]

@[simp]
theorem toList_glue {α : Type u} (q₁ : FingerTree α) (xs : List α) (q₂ : FingerTree α) :
    (glue q₁ xs q₂).toList = q₁.toList ++ xs ++ q₂.toList := by
  induction q₁ with
  | nil => simp [glue, toList, toList_foldr_cons]
  | unit x => cases q₂ <;> simp [glue, toList, toList_foldr_cons, toList_foldl_snoc]
  | more u₁ m₁ v₁ ih =>
    cases q₂ with
    | nil => simp [glue, toList, toList_foldl_snoc, List.append_assoc]
    | unit y => simp [glue, toList, toList_foldl_snoc, List.append_assoc]
    | more u₂ m₂ v₂ =>
      have hv := (v₁.length_toList_bounds).1
      have hu := (u₂.length_toList_bounds).1
      let mid := v₁.toList ++ xs ++ u₂.toList
      have hne : mid.length ≠ 1 := by
        have : mid.length = v₁.toList.length + (xs.length + u₂.toList.length) := by
          simp [mid]
        omega
      change (more u₁ (glue m₁ (FingerNode.ofList mid) m₂) v₂).toList = _
      rw [toList, ih, FingerNode.listToList_append, FingerNode.listToList_append,
        FingerNode.listToList_ofList hne]
      simp [mid, toList, List.append_assoc]

@[simp]
theorem toList_append {α : Type u} (q₁ q₂ : FingerTree α) :
    (append q₁ q₂).toList = q₁.toList ++ q₂.toList := by
  simp [append]

/-- Sharp `O(log min(|q₁|, |q₂|))` amortized bound for `glue` when `xs.length ≤ 3`. -/
theorem glueCost_add_potential_le_min {α : Type u} (q₁ : FingerTree α) {xs : List α}
    (hxs : xs.length ≤ 3) (q₂ : FingerTree α) :
    glueCost q₁ xs q₂ + (glue q₁ xs q₂).potential ≤
      Nat.log 2 (max (min q₁.toList.length q₂.toList.length) 1) + 14 +
        q₁.potential + q₂.potential := by
  induction q₁ with
  | nil =>
    have hf := foldrCost_cons_add_potential_le q₂ xs
    change (1 + foldrCost cons consCost q₂ xs) + (xs.foldr cons q₂).potential ≤
      Nat.log 2 (max (min 0 q₂.toList.length) 1) + 14 + 0 + q₂.potential
    omega
  | unit x =>
    cases q₂ with
    | nil =>
      have hf := foldlCost_snoc_add_potential_le (.unit x) xs
      have hp : (unit x).potential = 0 := rfl
      change (1 + foldlCost snoc snocCost (.unit x) xs) + (xs.foldl snoc (.unit x)).potential ≤
        Nat.log 2 (max (min 1 0) 1) + 14 + (unit x).potential + 0
      omega
    | unit y =>
      have hf := foldrCost_cons_add_potential_le (.unit y) (x :: xs)
      have hp : (unit y).potential = 0 := rfl
      simp only [List.length_cons, hp] at hf
      change (1 + foldrCost cons consCost (.unit y) (x :: xs)) +
          ((x :: xs).foldr cons (.unit y)).potential ≤
        Nat.log 2 (max (min 1 1) 1) + 14 + 0 + 0
      omega
    | more u₂ m₂ v₂ =>
      let r := FingerTree.more u₂ m₂ v₂
      have hf := foldrCost_cons_add_potential_le r (x :: xs)
      simp only [List.length_cons] at hf
      change (1 + foldrCost cons consCost r (x :: xs)) + ((x :: xs).foldr cons r).potential ≤
        Nat.log 2 (max (min 1 r.toList.length) 1) + 14 + 0 + r.potential
      omega
  | more u₁ m₁ v₁ ih =>
    let l := FingerTree.more u₁ m₁ v₁
    cases q₂ with
    | nil =>
      have hf := foldlCost_snoc_add_potential_le l xs
      change (1 + foldlCost snoc snocCost l xs) + (xs.foldl snoc l).potential ≤
        Nat.log 2 (max (min l.toList.length 0) 1) + 14 + l.potential + 0
      omega
    | unit y =>
      have hf := foldlCost_snoc_add_potential_le l xs
      have hs := snocCost_add_potential_le (xs.foldl snoc l) y
      change (1 + snocCost (xs.foldl snoc l) y + foldlCost snoc snocCost l xs) +
          (snoc (xs.foldl snoc l) y).potential ≤
        Nat.log 2 (max (min l.toList.length 1) 1) + 14 + l.potential + 0
      omega
    | more u₂ m₂ v₂ =>
      let r := FingerTree.more u₂ m₂ v₂
      let mid := FingerNode.ofList (v₁.toList ++ xs ++ u₂.toList)
      have hv := v₁.length_toList_bounds
      have hu := u₂.length_toList_bounds
      have hu₁ := (u₁.length_toList_bounds).1
      have hv₂ := (v₂.length_toList_bounds).1
      have hm₁ := (FingerNode.length_listToList_bounds m₁.toList).1
      have hm₂ := (FingerNode.length_listToList_bounds m₂.toList).1
      have hmid : mid.length ≤ 3 :=
        FingerNode.length_ofList_le_three (by simp only [List.length_append]; omega)
      let k := max (min m₁.toList.length m₂.toList.length) 1
      have hrec : glueCost m₁ mid m₂ + (glue m₁ mid m₂).potential ≤
          Nat.log 2 k + 14 + m₁.potential + m₂.potential := ih hmid m₂
      have h2k : 2 ≤ 2 * k := by simp only [k]; omega
      have hdiv : 2 * k / 2 = k := by omega
      have hlog_eq : 1 + Nat.log 2 k = Nat.log 2 (2 * k) := by
        rw [Nat.log_of_one_lt_of_le (by decide) h2k, hdiv, Nat.add_comm]
      have hlen₁ : 2 + 2 * m₁.toList.length ≤ l.toList.length := by
        change 2 + 2 * m₁.toList.length ≤
          (u₁.toList ++ FingerNode.listToList m₁.toList ++ v₁.toList).length
        simp only [List.length_append]; omega
      have hlen₂ : 2 + 2 * m₂.toList.length ≤ r.toList.length := by
        change 2 + 2 * m₂.toList.length ≤
          (u₂.toList ++ FingerNode.listToList m₂.toList ++ v₂.toList).length
        simp only [List.length_append]; omega
      have hmono : Nat.log 2 (2 * k) ≤
          Nat.log 2 (max (min l.toList.length r.toList.length) 1) :=
        Nat.log_mono_right (by simp only [k]; omega)
      change (1 + glueCost m₁ mid m₂) + (u₁.danger + (glue m₁ mid m₂).potential + v₂.danger) ≤
        Nat.log 2 (max (min l.toList.length r.toList.length) 1) + 14 +
          (u₁.danger + m₁.potential + v₁.danger) + (u₂.danger + m₂.potential + v₂.danger)
      omega

/-- Combined-size logarithmic amortized bound for `glue` when `xs.length ≤ 3`. -/
theorem glueCost_add_potential_le {α : Type u} (q₁ : FingerTree α) {xs : List α}
    (hxs : xs.length ≤ 3) (q₂ : FingerTree α) :
    glueCost q₁ xs q₂ + (glue q₁ xs q₂).potential ≤
      Nat.log 2 (max (q₁.toList.length + q₂.toList.length) 2) + 14 +
        q₁.potential + q₂.potential := by
  have h := glueCost_add_potential_le_min q₁ hxs q₂
  have hmono : Nat.log 2 (max (min q₁.toList.length q₂.toList.length) 1) ≤
      Nat.log 2 (max (q₁.toList.length + q₂.toList.length) 2) :=
    Nat.log_mono_right (by omega)
  omega

/-- Sharp `O(log min(|q₁|, |q₂|))` amortized bound for finger-tree `append`. -/
theorem appendCost_add_potential_le_min {α : Type u} (q₁ q₂ : FingerTree α) :
    appendCost q₁ q₂ + (append q₁ q₂).potential ≤
      Nat.log 2 (max (min q₁.toList.length q₂.toList.length) 1) + 14 +
        q₁.potential + q₂.potential :=
  glueCost_add_potential_le_min q₁ (by simp) q₂

/-- Double-ended insertion operations on a finger tree. -/
inductive DequeOp (α : Type u) : Type u where
  /-- Left insertion (`cons`). -/
  | cons : α → DequeOp α
  /-- Right insertion (`snoc`). -/
  | snoc : α → DequeOp α
  deriving DecidableEq, Repr

/-- Deterministic list specification for double-ended sequence insertions. -/
abbrev dequeSpec (α : Type u) : StateTransitionSpec :=
  StateTransitionSpec.ofFn
    (State := List α)
    (Op := DequeOp α)
    (Result := fun _ ↦ PUnit.{u + 1})
    (fun s o ↦ match o with
      | .cons x => (x :: s, PUnit.unit)
      | .snoc x => (s ++ [x], PUnit.unit))

/-- Single-operation step on `FingerTree α` recording exact `consCost` / `snocCost`. -/
@[expose] def dequeStep {α : Type u} (q : FingerTree α) (o : DequeOp α) :
    StepResult (FingerTree α) (ULift.{u + 1} ℕ) ((dequeSpec α).Result o) :=
  match o with
  | .cons x => ⟨FingerTree.cons x q, PUnit.unit, .up (FingerTree.consCost x q)⟩
  | .snoc x => ⟨FingerTree.snoc q x, PUnit.unit, .up (FingerTree.snocCost q x)⟩

/-- Native execution relation for `dequeSpec α`. -/
abbrev DequeExec (α : Type u) :
    Execution (dequeSpec α) (FingerTree α) (ULift.{u + 1} ℕ) :=
  Execution.ofStep dequeStep

/-- Semantic realization of `dequeSpec α` by `FingerTree α`. -/
@[expose] def dequeImpl (α : Type u) :
    StateTransitionImpl (dequeSpec α) (DequeExec α) :=
  StateTransitionImpl.ofStep (D := dequeSpec α) (fun s q ↦ s = q.toList) dequeStep
    fun {_ q} o hr _ ↦ by
      subst hr
      cases o with
      | cons x => exact ⟨rfl, (q.toList_cons x).symm⟩
      | snoc x => exact ⟨rfl, (q.toList_snoc x).symm⟩

/-- Uniform constant-charge (`3`) `Amortized` certificate for finger-tree `cons` and `snoc`. -/
theorem deque_amortized (α : Type u) :
    Amortized (dequeImpl α) ULift.down (fun _ q ↦ q.potential) (fun _ _ ↦ 3) :=
  Amortized.ofFn fun {_ q o _ _ _} _ _ he ↦ by
    cases o with
    | cons x =>
      rcases he with ⟨rfl, rfl, rfl⟩
      exact FingerTree.consCost_add_potential_le x q
    | snoc x =>
      rcases he with ⟨rfl, rfl, rfl⟩
      exact FingerTree.snocCost_add_potential_le q x

/-- Every adaptive client running `m` `cons`/`snoc` operations from `.nil` takes cost `≤ 3 * m`. -/
theorem deque_executes_total_le_of_empty {α β : Type u}
    {p : (dequeSpec α).Client β} {q' : FingerTree α} {b : β} {ts : List (ULift.{u + 1} ℕ)}
    (he : Executes (DequeExec α) p .nil b q' ts) :
    total ULift.down ts ≤ ((dequeSpec α).clientHistory [] p).length * 3 := by
  have hr : (dequeImpl α).rep [] .nil := rfl
  have hv := (dequeSpec α).validHistory_of_forall_valid (fun _ _ ↦ trivial) []
    ((dequeSpec α).clientHistory [] p)
  have h := (deque_amortized α).client_const hr hv he
  simp only [FingerTree.potential, Nat.add_zero] at h
  omega

end FingerTree

end CslibFrontier.DataStructure
