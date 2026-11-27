/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.StateTransition.Amortized
public import CslibFrontier.DataStructure.StateTransition.StepFunction
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Nat.Log

/-!
# Purely Functional Binomial Heaps and Amortized Insertion

This module formalizes purely functional binomial trees and sparse little-endian binary binomial
forests, their rank (`2 ^ k` size)
and min-heap ordering invariants, logarithmic `O(log n)` worst-case insertion cost, exact constant
amortized insertion cost `2` under the root-count potential function, and an adaptive-client
`Cslib.DataStructure.Amortized` certificate over a multiset priority-queue insertion specification.

## Main definitions

* `BinomialTree`: rose-tree representation of binomial trees with `singleton`, `root`, `children`,
  `toList`, `toMultiset`, `size`, `merge`, `IsRank`, `IsDescRanks`, and `IsMinHeap`.
* `BinomialForest`: little-endian sparse-binary binomial forest (`fEnd`, `f0`, `f1`) with
  `treeCount`, `toMultiset`, `size`, `IsValidFrom`, `IsMinHeap`, `insertTree`, `insert`, and
  `insertTreeCost`.
* `insertSpec`, `impl`: deterministic multiset insertion `StateTransitionSpec` and verified
  step-cost-instrumented `StateTransitionImpl` backed by `BinomialForest`.

## Main results

* `BinomialTree.IsRank.merge`, `BinomialTree.IsRank.size_eq`, `BinomialTree.IsMinHeap.merge`,
  `BinomialTree.IsMinHeap.root_le_of_mem`: linking preserves rank (`k` to `k + 1`) and min-heap
  order; every rank-`k` tree has `2 ^ k` elements with its minimum at the root.
* `BinomialForest.insertTreeCost_le_log`: worst-case insertion cost into a valid rank-zero heap of
  size `n` is at most `Nat.log 2 (n + 1) + 1`.
* `BinomialForest.insertTreeCost_add_treeCount`: exact potential identity
  `insertTreeCost t f + (insertTree t f).treeCount = 2 + f.treeCount`.
* `amortized`, `executes_total_le_of_empty`: `Cslib.DataStructure.Amortized` certificate with
  uniform constant charge `2` across arbitrary adaptive clients.
-/

public section

namespace CslibFrontier.DataStructure.PriorityQueue.BinomialHeap

open Cslib.DataStructure

universe u

/-- Ordered rose-tree representation of a binomial tree. -/
inductive BinomialTree (α : Type u) : Type u where
  /-- Construct a binomial tree from its root key and descending-rank list of child subtrees. -/
  | mkTree (root : α) (children : List (BinomialTree α)) : BinomialTree α
  deriving Repr

namespace BinomialTree

variable {α : Type u}

instance instInhabited [Inhabited α] : Inhabited (BinomialTree α) :=
  ⟨.mkTree default []⟩

/-- Rank-zero singleton binomial tree. -/
@[expose] def singleton (x : α) : BinomialTree α := .mkTree x []

/-- Root key of a binomial tree. -/
@[expose] def root : BinomialTree α → α
  | .mkTree r _ => r

/-- Immediate child subtrees of a binomial tree. -/
@[expose] def children : BinomialTree α → List (BinomialTree α)
  | .mkTree _ cs => cs

/-- Preorder list of all elements stored in a binomial tree. -/
@[expose] def toList : BinomialTree α → List α
  | .mkTree x cs => x :: childrenToList cs
where
  /-- Concatenate preorder lists across a list of child binomial trees. -/
  childrenToList : List (BinomialTree α) → List α
    | [] => []
    | t :: ts => toList t ++ childrenToList ts

/-- Multiset of all elements stored in a binomial tree. -/
@[expose] def toMultiset (t : BinomialTree α) : Multiset α := ↑t.toList

/-- Number of elements stored in a binomial tree. -/
@[expose] def size (t : BinomialTree α) : ℕ := t.toList.length

/-- Structural induction principle for `BinomialTree`. -/
theorem recOnChildren {motive : BinomialTree α → Prop}
    (mk : ∀ (r : α) (cs : List (BinomialTree α)), (∀ c ∈ cs, motive c) → motive (.mkTree r cs)) :
    ∀ (t : BinomialTree α), motive t
  | .mkTree r cs =>
    let rec go : ∀ (xs : List (BinomialTree α)) (c : BinomialTree α), c ∈ xs → motive c
      | [], _, h => nomatch h
      | t' :: ts, c, h =>
        match List.mem_cons.mp h with
        | Or.inl heq => heq ▸ recOnChildren mk t'
        | Or.inr hmem => go ts c hmem
    mk r cs (go cs)

/-- Link two equal-rank binomial trees, keeping the smaller root on top. -/
@[expose] def merge [LinearOrder α] : BinomialTree α → BinomialTree α → BinomialTree α
  | .mkTree lr lc, .mkTree rr rc =>
    if lr ≤ rr then .mkTree lr (.mkTree rr rc :: lc)
    else .mkTree rr (.mkTree lr lc :: rc)

@[simp]
theorem root_merge [LinearOrder α] (l r : BinomialTree α) :
    (l.merge r).root = min l.root r.root := by
  cases l with
  | mkTree lr lc =>
    cases r with
    | mkTree rr rc =>
      by_cases h : lr ≤ rr
      · simp [merge, h, root]
      · simp [merge, h, root, le_of_not_ge h]

@[simp]
theorem toMultiset_merge [LinearOrder α] (l r : BinomialTree α) :
    (l.merge r).toMultiset = l.toMultiset + r.toMultiset := by
  cases l with
  | mkTree lr lc =>
    cases r with
    | mkTree rr rc =>
      by_cases h : lr ≤ rr
      · simp only [merge, h, ↓reduceIte, toMultiset, toList, toList.childrenToList,
          ← Multiset.coe_add, ← Multiset.cons_coe]
        rw [Multiset.add_comm (rr ::ₘ ↑(toList.childrenToList rc)) ↑(toList.childrenToList lc),
          ← Multiset.cons_add]
      · simp only [merge, h, ↓reduceIte, toMultiset, toList, toList.childrenToList,
          ← Multiset.coe_add, ← Multiset.cons_coe]
        rw [Multiset.add_comm (lr ::ₘ ↑(toList.childrenToList lc)) ↑(toList.childrenToList rc),
          ← Multiset.cons_add, Multiset.add_comm]

@[simp]
theorem size_merge [LinearOrder α] (l r : BinomialTree α) :
    (l.merge r).size = l.size + r.size := by
  simpa [toMultiset, size] using congrArg Multiset.card (toMultiset_merge l r)

mutual

/-- Structural rank predicate on binomial trees. -/
inductive IsRank {α : Type u} : ℕ → BinomialTree α → Prop where
  /-- A node whose children have exact descending ranks `k - 1, ..., 0` has rank `k`. -/
  | mk {k : ℕ} {x : α} {cs : List (BinomialTree α)} :
      IsDescRanks k cs → IsRank k (.mkTree x cs)

/-- Descending child-rank predicate `k - 1, ..., 0`. -/
inductive IsDescRanks {α : Type u} : ℕ → List (BinomialTree α) → Prop where
  /-- Empty list below rank `0`. -/
  | nil : IsDescRanks 0 []
  /-- Prepend a rank-`k` tree to children below rank `k`. -/
  | cons {k : ℕ} {t : BinomialTree α} {ts : List (BinomialTree α)} :
      IsRank k t → IsDescRanks k ts → IsDescRanks (k + 1) (t :: ts)

end

/-- Singleton binomial trees have rank `0`. -/
theorem IsRank.singleton (x : α) : IsRank 0 (BinomialTree.singleton x) := .mk .nil

/-- Linking two rank-`k` binomial trees produces a rank-`(k + 1)` binomial tree. -/
theorem IsRank.merge [LinearOrder α] {k : ℕ} {l r : BinomialTree α}
    (hl : IsRank k l) (hr : IsRank k r) : IsRank (k + 1) (l.merge r) := by
  cases hl with
  | @mk _ lr lc hlc =>
    cases hr with
    | @mk _ rr rc hrc =>
      by_cases h : lr ≤ rr
      · simp only [BinomialTree.merge, h, ↓reduceIte]
        exact .mk (.cons (.mk hrc) hlc)
      · simp only [BinomialTree.merge, h, ↓reduceIte]
        exact .mk (.cons (.mk hlc) hrc)

private theorem size_and_children_eq :
    ∀ (k : ℕ),
      (∀ (t : BinomialTree α), IsRank k t → t.size = 2 ^ k) ∧
      (∀ (cs : List (BinomialTree α)), IsDescRanks k cs →
        (toList.childrenToList cs).length = 2 ^ k - 1)
  | 0 =>
    ⟨fun _ ht ↦ by cases ht with | mk hcs => cases hcs; rfl,
     fun _ hcs ↦ by cases hcs; rfl⟩
  | k + 1 => by
    obtain ⟨ihT, ihC⟩ := size_and_children_eq k
    have hC : ∀ (cs : List (BinomialTree α)), IsDescRanks (k + 1) cs →
        (toList.childrenToList cs).length = 2 ^ (k + 1) - 1 := by
      intro cs hcs
      cases hcs with
      | cons ht hts =>
        have h1 := ihT _ ht
        have h2 := ihC _ hts
        have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
        simp only [toList.childrenToList, List.length_append]
        rw [show List.length _ = _ from h1, h2, Nat.pow_succ]
        omega
    refine ⟨fun t ht ↦ ?_, hC⟩
    cases ht with
    | mk hcs =>
      have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by decide)
      simp only [size, toList, List.length_cons, hC _ hcs]
      omega

/-- Every rank-`k` binomial tree contains exactly `2 ^ k` elements. -/
theorem IsRank.size_eq {k : ℕ} {t : BinomialTree α} (ht : IsRank k t) : t.size = 2 ^ k :=
  (size_and_children_eq k).1 t ht

/-- Min-heap ordering predicate on a binomial tree. -/
inductive IsMinHeap [Preorder α] : BinomialTree α → Prop where
  /-- Each child's root is bounded below by the node's root, and all children are min-heaps. -/
  | mk {r : α} {cs : List (BinomialTree α)}
      (root_le : ∀ c ∈ cs, r ≤ c.root)
      (children_heap : ∀ c ∈ cs, IsMinHeap c) :
      IsMinHeap (.mkTree r cs)

/-- Singleton trees are min-heaps. -/
theorem IsMinHeap.singleton [Preorder α] (x : α) : IsMinHeap (BinomialTree.singleton x) :=
  .mk (by simp) (by simp)

private theorem mem_childrenToList_iff :
    ∀ {cs : List (BinomialTree α)} {y : α},
      y ∈ toList.childrenToList cs ↔ ∃ c ∈ cs, y ∈ c.toList
  | [], _ => by simp [toList.childrenToList]
  | c :: cs, y => by
    simp only [toList.childrenToList, List.mem_append, mem_childrenToList_iff, List.mem_cons]
    exact ⟨fun h ↦ h.elim (fun hy ↦ ⟨c, Or.inl rfl, hy⟩) fun ⟨c', hc', hy⟩ ↦ ⟨c', Or.inr hc', hy⟩,
      fun ⟨c', hc', hy⟩ ↦ hc'.elim (fun e ↦ Or.inl (e ▸ hy)) fun h ↦ Or.inr ⟨c', h, hy⟩⟩

/-- The root of a min-heap binomial tree is less than or equal to every stored element. -/
theorem IsMinHeap.root_le_of_mem [Preorder α] {t : BinomialTree α} (ht : t.IsMinHeap)
    {y : α} (hy : y ∈ t.toMultiset) : t.root ≤ y := by
  induction t using recOnChildren with
  | mk r cs ih =>
    cases ht with
    | mk hroot hch =>
      simp only [toMultiset, toList, Multiset.mem_coe, List.mem_cons,
        mem_childrenToList_iff, root] at hy ⊢
      rcases hy with rfl | ⟨c, hcs, hyc⟩
      · exact le_rfl
      · exact (hroot c hcs).trans (ih c hcs (hch c hcs) (Multiset.mem_coe.mpr hyc))

/-- Linking two min-heap binomial trees preserves min-heap ordering. -/
theorem IsMinHeap.merge [LinearOrder α] {l r : BinomialTree α}
    (hl : l.IsMinHeap) (hr : r.IsMinHeap) : (l.merge r).IsMinHeap := by
  cases hl with
  | @mk lr lc hlr hlc =>
    cases hr with
    | @mk rr rc hrr hrc =>
      by_cases h : lr ≤ rr
      · simp only [BinomialTree.merge, h, ↓reduceIte]
        refine .mk (fun c hc ↦ ?_) (fun c hc ↦ ?_)
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact h
          · exact hlr c hc
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact .mk hrr hrc
          · exact hlc c hc
      · simp only [BinomialTree.merge, h, ↓reduceIte]
        refine .mk (fun c hc ↦ ?_) (fun c hc ↦ ?_)
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact le_of_not_ge h
          · exact hrr c hc
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact .mk hlr hlc
          · exact hrc c hc

end BinomialTree

/-- Sparse little-endian binary forest of binomial trees. -/
inductive BinomialForest (α : Type u) : Type u where
  /-- Empty binomial forest. -/
  | fEnd : BinomialForest α
  /-- Vacant slot at current rank. -/
  | f0 (rest : BinomialForest α) : BinomialForest α
  /-- Occupied slot holding a binomial tree at current rank. -/
  | f1 (tree : BinomialTree α) (rest : BinomialForest α) : BinomialForest α
  deriving Repr

namespace BinomialForest

variable {α : Type u}

instance instInhabited : Inhabited (BinomialForest α) := ⟨.fEnd⟩

/-- Root-count potential counting occupied (`f1`) slots. -/
@[expose] def treeCount : BinomialForest α → ℕ
  | .fEnd => 0
  | .f0 rest => treeCount rest
  | .f1 _ rest => 1 + treeCount rest

/-- Multiset of all elements stored in a binomial forest. -/
@[expose] def toMultiset : BinomialForest α → Multiset α
  | .fEnd => 0
  | .f0 rest => toMultiset rest
  | .f1 t rest => t.toMultiset + toMultiset rest

/-- Total element count of a binomial forest. -/
@[expose] def size : BinomialForest α → ℕ
  | .fEnd => 0
  | .f0 rest => size rest
  | .f1 t rest => t.size + size rest

/-- Rank-validity of a binomial forest starting at rank `k`. -/
inductive IsValidFrom : ℕ → BinomialForest α → Prop where
  /-- Empty forest. -/
  | fEnd (k : ℕ) : IsValidFrom k .fEnd
  /-- Vacant rank-`k` slot. -/
  | f0 {k : ℕ} {rest : BinomialForest α} : IsValidFrom (k + 1) rest → IsValidFrom k (.f0 rest)
  /-- Occupied rank-`k` slot holding a rank-`k` binomial tree. -/
  | f1 {k : ℕ} {t : BinomialTree α} {rest : BinomialForest α} :
      t.IsRank k → IsValidFrom (k + 1) rest → IsValidFrom k (.f1 t rest)

/-- Min-heap validity across all trees in a binomial forest. -/
@[expose] def IsMinHeap [Preorder α] : BinomialForest α → Prop
  | .fEnd => True
  | .f0 rest => IsMinHeap rest
  | .f1 t rest => t.IsMinHeap ∧ IsMinHeap rest

/-- Carry-propagating tree insertion into a binomial forest. -/
@[expose] def insertTree [LinearOrder α] (t : BinomialTree α) :
    BinomialForest α → BinomialForest α
  | .fEnd => .f1 t .fEnd
  | .f0 f => .f1 t f
  | .f1 t' f => .f0 (insertTree (t.merge t') f)

/-- Insert a single key into a rank-zero binomial forest. -/
@[expose] def insert [LinearOrder α] (x : α) (f : BinomialForest α) : BinomialForest α :=
  insertTree (.singleton x) f

/-- Recursive step cost of `insertTree` (`1` base step plus `1` per carry merge). -/
@[expose] def insertTreeCost [LinearOrder α] (t : BinomialTree α) : BinomialForest α → ℕ
  | .fEnd => 1
  | .f0 _ => 1
  | .f1 t' f => 1 + insertTreeCost (t.merge t') f

/-- Every insertion incurs step cost at least `1`. -/
theorem one_le_insertTreeCost [LinearOrder α] (t : BinomialTree α) (f : BinomialForest α) :
    1 ≤ insertTreeCost t f := by
  cases f <;> simp [insertTreeCost]

@[simp]
theorem toMultiset_insertTree [LinearOrder α] (t : BinomialTree α) (f : BinomialForest α) :
    (insertTree t f).toMultiset = t.toMultiset + f.toMultiset := by
  induction f generalizing t with
  | fEnd => simp [insertTree, toMultiset]
  | f0 _ => rfl
  | f1 t' _ ih => simp [insertTree, toMultiset, ih, Multiset.add_assoc]

@[simp]
theorem toMultiset_insert [LinearOrder α] (x : α) (f : BinomialForest α) :
    (insert x f).toMultiset = x ::ₘ f.toMultiset := by
  simp [insert, BinomialTree.singleton, BinomialTree.toMultiset, BinomialTree.toList,
    BinomialTree.toList.childrenToList]

/-- Inserting a rank-`k` tree preserves `IsValidFrom k`. -/
theorem IsValidFrom.insertTree [LinearOrder α] {k : ℕ} {t : BinomialTree α}
    {f : BinomialForest α} (ht : t.IsRank k) (hf : f.IsValidFrom k) :
    (insertTree t f).IsValidFrom k := by
  induction hf generalizing t with
  | fEnd k => exact .f1 ht (.fEnd (k + 1))
  | f0 hrest => exact .f1 ht hrest
  | f1 ht' _ ih => exact .f0 (ih (ht.merge ht'))

/-- Inserting a min-heap tree preserves `IsMinHeap`. -/
theorem IsMinHeap.insertTree [LinearOrder α] {t : BinomialTree α} {f : BinomialForest α}
    (ht : t.IsMinHeap) (hf : f.IsMinHeap) : (insertTree t f).IsMinHeap := by
  induction f generalizing t with
  | fEnd => exact ⟨ht, trivial⟩
  | f0 _ => exact ⟨ht, hf⟩
  | f1 _ _ ih => exact ih (ht.merge hf.1) hf.2

/-- Exponential size bound controlling carry depth in a valid binomial forest. -/
theorem IsValidFrom.pow_insertTreeCost_le [LinearOrder α] {k : ℕ} {f : BinomialForest α}
    (hf : f.IsValidFrom k) (t : BinomialTree α) :
    2 ^ k * 2 ^ (insertTreeCost t f - 1) ≤ f.size + 2 ^ k := by
  induction hf generalizing t with
  | fEnd => simp [insertTreeCost, size]
  | f0 => simp [insertTreeCost, size]
  | @f1 k t' rest ht' _ ih =>
    have hcost : 1 ≤ insertTreeCost (t.merge t') rest := one_le_insertTreeCost _ _
    have hstep := ih (t.merge t')
    simp only [insertTreeCost, Nat.add_sub_cancel_left, size, ht'.size_eq]
    calc
      2 ^ k * 2 ^ insertTreeCost (t.merge t') rest
          = 2 ^ (k + 1) * 2 ^ (insertTreeCost (t.merge t') rest - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hcost]
            rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc,
              Nat.mul_comm 2 (2 ^ (insertTreeCost (t.merge t') rest - 1)), ← Nat.mul_assoc]
      _ ≤ rest.size + 2 ^ (k + 1) := hstep
      _ = 2 ^ k + rest.size + 2 ^ k := by rw [Nat.pow_succ]; omega

/-- Logarithmic `O(log n)` worst-case bound on binomial-heap insertion cost. -/
theorem insertTreeCost_le_log [LinearOrder α] {f : BinomialForest α} (hf : f.IsValidFrom 0)
    (t : BinomialTree α) : insertTreeCost t f ≤ Nat.log 2 (f.size + 1) + 1 := by
  have hpow : 2 ^ (insertTreeCost t f - 1) ≤ f.size + 1 := by
    simpa using hf.pow_insertTreeCost_le t
  have hlog : insertTreeCost t f - 1 ≤ Nat.log 2 (f.size + 1) :=
    Nat.le_log_of_pow_le (by decide) hpow
  omega

/-- Exact constant-amortized-cost identity for binomial-heap insertion:
`insertTreeCost t f + (insertTree t f).treeCount = 2 + f.treeCount`. -/
theorem insertTreeCost_add_treeCount [LinearOrder α] (t : BinomialTree α)
    (f : BinomialForest α) :
    insertTreeCost t f + (insertTree t f).treeCount = 2 + f.treeCount := by
  induction f generalizing t with
  | fEnd => rfl
  | f0 _ => simp only [insertTreeCost, insertTree, treeCount]; omega
  | f1 t' rest ih =>
    have h := ih (t.merge t')
    simp only [insertTreeCost, insertTree, treeCount]
    omega

end BinomialForest

/-- Multiset insertion operation for a binomial heap. -/
inductive InsertOp (α : Type u) : Type u where
  /-- Insert key `x` into the priority queue. -/
  | insert (x : α) : InsertOp α
  deriving DecidableEq, Repr

/-- Deterministic multiset insertion specification. -/
abbrev insertSpec (α : Type u) : StateTransitionSpec :=
  StateTransitionSpec.ofFn
    (State := Multiset α)
    (Op := InsertOp α)
    (Result := fun _ ↦ PUnit.{u + 1})
    (fun s o ↦ match o with | .insert x => (x ::ₘ s, PUnit.unit))

/-- Representation invariant coupling multiset contents, rank validity, and min-heap ordering. -/
@[expose] def Rep {α : Type u} [LinearOrder α] (s : Multiset α) (f : BinomialForest α) : Prop :=
  f.toMultiset = s ∧ f.IsValidFrom 0 ∧ f.IsMinHeap

/-- Step execution on `BinomialForest α` emitting exact `insertTreeCost`. -/
@[expose] def step {α : Type u} [LinearOrder α] (f : BinomialForest α) (o : InsertOp α) :
    StepResult (BinomialForest α) (ULift.{u} ℕ) ((insertSpec α).Result o) :=
  match o with
  | .insert x => ⟨f.insert x, PUnit.unit, .up (f.insertTreeCost (.singleton x))⟩

/-- Native execution relation for `insertSpec α`. -/
abbrev Exec (α : Type u) [LinearOrder α] :
    Execution (insertSpec α) (BinomialForest α) (ULift.{u} ℕ) :=
  Execution.ofStep step

/-- Semantic realization of `insertSpec α` by `BinomialForest α`. -/
@[expose] def impl (α : Type u) [LinearOrder α] :
    StateTransitionImpl (insertSpec α) (Exec α) :=
  StateTransitionImpl.ofStep (D := insertSpec α) Rep step fun {_ f} o hr _ ↦ by
    obtain ⟨rfl, hv, hm⟩ := hr
    cases o with
    | insert x =>
      exact ⟨rfl, f.toMultiset_insert x, hv.insertTree (.singleton x),
        hm.insertTree (.singleton x)⟩

/-- Uniform constant-charge (`2`) `Amortized` certificate for binomial-heap insertion. -/
theorem amortized (α : Type u) [LinearOrder α] :
    Amortized (impl α) ULift.down (fun _ f ↦ f.treeCount) (fun _ _ ↦ 2) :=
  Amortized.ofFn fun {_ f o _ _ _} _ _ he ↦ by
    cases o with
    | insert x =>
      rcases he with ⟨rfl, rfl, rfl⟩
      exact le_of_eq (f.insertTreeCost_add_treeCount (.singleton x))

/-- Every adaptive client running `m` insertions from `.fEnd` takes total step cost `≤ 2 * m`. -/
theorem executes_total_le_of_empty {α β : Type u} [LinearOrder α]
    {p : (insertSpec α).Client β} {f' : BinomialForest α} {b : β} {ts : List (ULift.{u} ℕ)}
    (he : Executes (Exec α) p .fEnd b f' ts) :
    total ULift.down ts ≤ ((insertSpec α).clientHistory 0 p).length * 2 := by
  have hr : (impl α).rep 0 .fEnd := ⟨rfl, .fEnd 0, trivial⟩
  have hv := (insertSpec α).validHistory_of_forall_valid (fun _ _ ↦ trivial) 0
    ((insertSpec α).clientHistory 0 p)
  have h := (amortized α).client_const hr hv he
  simp only [BinomialForest.treeCount, Nat.add_zero] at h
  omega

end CslibFrontier.DataStructure.PriorityQueue.BinomialHeap
