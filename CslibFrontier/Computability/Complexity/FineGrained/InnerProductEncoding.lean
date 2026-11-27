/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic Binary Encoding of Bounded Integer Inner-Product Equality

This module formalizes the Chen–Williams quadratic encoding lemma
, which converts exact inner-product equality `⟨a, b⟩ = σ` on bounded integer vectors
`a, b ∈ {0, …, q}^T` and target `σ ∈ {0, …, T q^2}` into an additive inner-product gap on binary
vectors `g(a, σ), h(b, σ) ∈ {0, 1}^{5 T^2 q^4}`.

Expanding `2 T^2 q^4 - (⟨a, b⟩ - σ)^2` as a nonnegative integer bilinear sum
`∑_{i,j} (q^2 - a_i a_j)(b_i b_j) + ∑_{i,j} q^2 (q^2 - b_i b_j) + ∑_i (2 σ a_i) b_i +
 (T^2 q^4 - σ^2)` and representing each bounded product `x * y` via unary tensor blocks yields the
exact quadratic identity `⟨g(a, σ), h(b, σ)⟩ + (⟨a, b⟩ - σ)^2 = 2 T^2 q^4`. Both encoding maps
are injective on bounded vectors (when `1 ≤ q`) and uniformly computable in polynomial time on a
deterministic multi-tape Turing machine.

## Main definitions

* `CslibFrontier.Computability.Complexity.natListInnerProd`: standard inner product
  `∑_i a_i * b_i` on `List ℕ`.
* `CslibFrontier.Computability.Complexity.boolListInnerProd`: binary inner product counting shared
  `true` positions.
* `CslibFrontier.Computability.Complexity.ipGapDim`,
  `CslibFrontier.Computability.Complexity.ipGapThreshold`: output dimension `5 * T^2 * q^4` and
  target inner product `Γ = 2 * T^2 * q^4`.
* `CslibFrontier.Computability.Complexity.ipGapEncodeLeft`,
  `CslibFrontier.Computability.Complexity.ipGapEncodeRight`: the binary encodings `g(a, σ)` and
  `h(b, σ)` in `{0, 1}^{5 T^2 q^4}`.

## Main results

* `CslibFrontier.Computability.Complexity.boolListInnerProd_ipGapEncode_add_sq`: exact quadratic
  identity `⟨g(a, σ), h(b, σ)⟩ + (⟨a, b⟩ - σ)^2 = 2 T^2 q^4`.
* `CslibFrontier.Computability.Complexity.boolListInnerProd_ipGapEncode_eq_of_eq`,
  `CslibFrontier.Computability.Complexity.boolListInnerProd_ipGapEncode_lt_of_ne`: exact value `Γ`
  when `⟨a, b⟩ = σ` and strict gap `≤ Γ - 1 < Γ` when `⟨a, b⟩ ≠ σ`.
* `CslibFrontier.Computability.Complexity.ipGapEncodeLeft_injective`,
  `CslibFrontier.Computability.Complexity.ipGapEncodeRight_injective`: injectivity on
  `{0, …, q}^T` for `1 ≤ q`.
* `CslibFrontier.Computability.Complexity.computableInPolyTime_ipGapEncodeLeft`,
  `CslibFrontier.Computability.Complexity.computableInPolyTime_ipGapEncodeRight`: uniform
  polynomial-time computability in `(T, q, a, σ)` on multi-tape Turing machines.
-/

public section

namespace CslibFrontier.Computability.Complexity

open Turing.MultiTapeTM

/-- Standard nonnegative integer inner product `∑_i a_i * b_i` of two lists of natural numbers. -/
@[expose]
def natListInnerProd : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + natListInnerProd xs ys

/-- Binary inner product `⟨u, v⟩ = ∑_i 1_{u_i = v_i = true}` of two Boolean vectors. -/
@[expose]
def boolListInnerProd : List Bool → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => (if x && y then 1 else 0) + boolListInnerProd xs ys

/-- Inner product with the empty integer list on the left is zero. -/
@[simp]
theorem natListInnerProd_nil_left (b : List ℕ) : natListInnerProd [] b = 0 := rfl

/-- Inner product with the empty integer list on the right is zero. -/
@[simp]
theorem natListInnerProd_nil_right (a : List ℕ) : natListInnerProd a [] = 0 := by
  cases a <;> rfl

/-- Single-step recurrence for `natListInnerProd` on non-empty integer lists. -/
@[simp]
theorem natListInnerProd_cons_cons (x y : ℕ) (xs ys : List ℕ) :
    natListInnerProd (x :: xs) (y :: ys) = x * y + natListInnerProd xs ys := rfl

/-- Binary inner product with the empty Boolean list on the left is zero. -/
@[simp]
theorem boolListInnerProd_nil_left (v : List Bool) : boolListInnerProd [] v = 0 := rfl

/-- Binary inner product with the empty Boolean list on the right is zero. -/
@[simp]
theorem boolListInnerProd_nil_right (u : List Bool) : boolListInnerProd u [] = 0 := by
  cases u <;> rfl

/-- Single-step recurrence for `boolListInnerProd` on non-empty Boolean lists. -/
@[simp]
theorem boolListInnerProd_cons_cons (x y : Bool) (xs ys : List Bool) :
    boolListInnerProd (x :: xs) (y :: ys) =
      (if x && y then 1 else 0) + boolListInnerProd xs ys := rfl

/-- Binary inner product converts to `natListInnerProd` on `{0, 1}`-valued lists. -/
theorem boolListInnerProd_eq_natListInnerProd (u v : List Bool) :
    boolListInnerProd u v =
      natListInnerProd (u.map fun b ↦ if b then 1 else 0) (v.map fun b ↦ if b then 1 else 0) := by
  induction u generalizing v with
  | nil => simp
  | cons x xs ih =>
    cases v with
    | nil => simp
    | cons y ys => cases x <;> cases y <;> simp [ih]

/-- Binary inner product distributes over concatenation of equal-length prefixes. -/
theorem boolListInnerProd_append {u₁ u₂ v₁ v₂ : List Bool} (h : u₁.length = v₁.length) :
    boolListInnerProd (u₁ ++ u₂) (v₁ ++ v₂) =
      boolListInnerProd u₁ v₁ + boolListInnerProd u₂ v₂ := by
  induction u₁ generalizing v₁ with
  | nil =>
    cases v₁ with
    | nil => simp
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases v₁ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.cons_append, boolListInnerProd_cons_cons, ih h, Nat.add_assoc]

/-- Binary inner product distributes over `List.flatMap` with pointwise equal block lengths. -/
theorem boolListInnerProd_flatMap {ι : Type*} (l : List ι) (f g : ι → List Bool)
    (hlen : ∀ i ∈ l, (f i).length = (g i).length) :
    boolListInnerProd (l.flatMap f) (l.flatMap g) =
      (l.map fun i ↦ boolListInnerProd (f i) (g i)).sum := by
  induction l with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [boolListInnerProd_append (hlen i List.mem_cons_self),
      ih fun j hj ↦ hlen j (List.mem_cons_of_mem i hj)]

/-- `natListInnerProd` written as a sum over `List.range T` when both lists have length `T`. -/
theorem natListInnerProd_eq_sum_range {T : ℕ} {a b : List ℕ}
    (ha : a.length = T) (hb : b.length = T) :
    natListInnerProd a b = ∑ i ∈ Finset.range T, a.getD i 0 * b.getD i 0 := by
  induction T generalizing a b with
  | zero =>
    cases a with
    | nil => simp
    | cons _ _ => simp at ha
  | succ T ih =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.length_cons, Nat.succ.injEq] at ha hb
        rw [natListInnerProd_cons_cons, ih ha hb, Finset.sum_range_succ']
        simp [Nat.add_comm]

/-- Bounded integer vector `a ∈ {0, …, q}^T` has inner product with `b ∈ {0, …, q}^T` at most
`T * q^2`. -/
theorem natListInnerProd_le_mul_sq {T q : ℕ} {a b : List ℕ}
    (ha : a.length = T) (hb : b.length = T)
    (haq : ∀ x ∈ a, x ≤ q) (hbq : ∀ y ∈ b, y ≤ q) :
    natListInnerProd a b ≤ T * q ^ 2 := by
  rw [natListInnerProd_eq_sum_range ha hb]
  calc
    ∑ i ∈ Finset.range T, a.getD i 0 * b.getD i 0 ≤ ∑ _i ∈ Finset.range T, q ^ 2 := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hiT : i < T := Finset.mem_range.mp hi
      have hia : a.getD i 0 ≤ q := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (ha ▸ hiT)]
        exact haq _ (List.getElem_mem _)
      have hib : b.getD i 0 ≤ q := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hb ▸ hiT)]
        exact hbq _ (List.getElem_mem _)
      rw [sq]
      exact Nat.mul_le_mul hia hib
    _ = T * q ^ 2 := by simp

/-- Unary prefix vector `1^x 0^{U - x} ∈ {0, 1}^U` (clamped at `U`). -/
def unaryVec (U x : ℕ) : List Bool :=
  List.replicate (min x U) true ++ List.replicate (U - min x U) false

/-- The unary prefix vector `unaryVec U x` always has length `U`. -/
@[simp]
theorem length_unaryVec (U x : ℕ) : (unaryVec U x).length = U := by
  simp only [unaryVec, List.length_append, List.length_replicate]
  omega

private lemma boolListInnerProd_unaryVec_ones {U x : ℕ} (hx : x ≤ U) :
    boolListInnerProd (unaryVec U x) (List.replicate U true) = x := by
  have hsplit : List.replicate U true =
      List.replicate x true ++ List.replicate (U - x) true := by
    rw [← List.replicate_add, Nat.add_sub_of_le hx]
  simp only [unaryVec, Nat.min_eq_left hx]
  rw [hsplit, boolListInnerProd_append (by simp)]
  have h1 : ∀ m, boolListInnerProd (List.replicate m true) (List.replicate m true) = m := by
    intro m; induction m with | zero => rfl | succ m ih => simp [List.replicate_succ, ih]; omega
  have h2 : ∀ m, boolListInnerProd (List.replicate m false) (List.replicate m true) = 0 := by
    intro m; induction m with | zero => rfl | succ m ih => simp [List.replicate_succ, ih]
  rw [h1, h2, add_zero]

private lemma boolListInnerProd_ones_unaryVec {U y : ℕ} (hy : y ≤ U) :
    boolListInnerProd (List.replicate U true) (unaryVec U y) = y := by
  have hcomm : ∀ u v : List Bool, boolListInnerProd u v = boolListInnerProd v u := by
    intro u
    induction u with
    | nil => simp
    | cons x xs ih =>
      intro v
      cases v with
      | nil => simp
      | cons z zs => simp [Bool.and_comm, ih]
  rw [hcomm]
  exact boolListInnerProd_unaryVec_ones hy

/-- Unary count recovery: the number of `true` entries in `unaryVec U x` is `min x U`. -/
private lemma count_true_unaryVec {U x : ℕ} (hx : x ≤ U) :
    (unaryVec U x).count true = x := by
  simp [unaryVec, Nat.min_eq_left hx, List.count_replicate]

/-- Left tensor factor `unaryVec U x ⊗ 1^V ∈ {0, 1}^{U * V}`. -/
private def prodEncLeft (U V x : ℕ) : List Bool :=
  (unaryVec U x).flatMap fun b ↦ List.replicate V b

/-- Right tensor factor `1^U ⊗ unaryVec V y ∈ {0, 1}^{U * V}`. -/
private def prodEncRight (U V y : ℕ) : List Bool :=
  (List.replicate U ()).flatMap fun _ ↦ unaryVec V y

private lemma length_prodEncLeft (U V x : ℕ) : (prodEncLeft U V x).length = U * V := by
  have h : ∀ l : List Bool, (l.flatMap fun b ↦ List.replicate V b).length = l.length * V := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih => simp [ih, Nat.add_mul, one_mul, Nat.add_comm]
  rw [prodEncLeft, h, length_unaryVec]

private lemma length_prodEncRight (U V y : ℕ) : (prodEncRight U V y).length = U * V := by
  have h : ∀ m : ℕ, ((List.replicate m ()).flatMap fun _ ↦ unaryVec V y).length = m * V := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp [List.replicate_succ, ih, length_unaryVec, Nat.add_mul, Nat.add_comm]
  exact h U

private lemma boolListInnerProd_prodEnc {U V x y : ℕ} (hx : x ≤ U) (hy : y ≤ V) :
    boolListInnerProd (prodEncLeft U V x) (prodEncRight U V y) = x * y := by
  have haux : ∀ l : List Bool,
      boolListInnerProd (l.flatMap fun b ↦ List.replicate V b)
        ((List.replicate l.length ()).flatMap fun _ ↦ unaryVec V y) =
      l.count true * y := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      simp only [List.flatMap_cons, List.length_cons, List.replicate_succ]
      rw [boolListInnerProd_append (by simp [length_unaryVec]), ih]
      cases b
      · have h0 : ∀ v : List Bool,
            boolListInnerProd (List.replicate v.length false) v = 0 := by
          intro v; induction v with | nil => rfl | cons _ vs iv => simp [List.replicate_succ, iv]
        have hf : boolListInnerProd (List.replicate V false) (unaryVec V y) = 0 := by
          simpa [length_unaryVec] using h0 (unaryVec V y)
        simp [hf]
      · simp only [boolListInnerProd_ones_unaryVec hy, List.count_cons_self]
        ring
  calc
    boolListInnerProd (prodEncLeft U V x) (prodEncRight U V y) =
        (unaryVec U x).count true * y := by
      simpa [prodEncLeft, prodEncRight, length_unaryVec] using haux (unaryVec U x)
    _ = x * y := by rw [count_true_unaryVec hx]

/-- Output binary dimension `5 * T^2 * q^4` of the Chen–Williams inner-product encoding. -/
@[expose] def ipGapDim (T q : ℕ) : ℕ :=
  5 * T ^ 2 * q ^ 4

/-- Target inner product `Γ = 2 * T^2 * q^4` achieved iff `⟨a, b⟩ = σ`. -/
@[expose] def ipGapThreshold (T q : ℕ) : ℕ :=
  2 * T ^ 2 * q ^ 4

/-- Left binary encoding `g(a, σ) ∈ {0, 1}^{5 T^2 q^4}` for `a ∈ {0, …, q}^T` and
`σ ∈ {0, …, T q^2}`. -/
def ipGapEncodeLeft (T q : ℕ) (a : List ℕ) (σ : ℕ) : List Bool :=
  let q2 := q * q
  let block1 := (List.range T).flatMap fun i ↦
    (List.range T).flatMap fun j ↦ prodEncLeft q2 q2 (q2 - a.getD i 0 * a.getD j 0)
  let block2 := List.replicate (T * T * (q2 * q2)) true
  let block3 := (List.range T).flatMap fun i ↦
    prodEncLeft (2 * T * q2 * q) q (2 * σ * a.getD i 0)
  let block4 := unaryVec (T * T * (q2 * q2)) (T * T * (q2 * q2) - σ * σ)
  block1 ++ block2 ++ block3 ++ block4

/-- Right binary encoding `h(b, σ) ∈ {0, 1}^{5 T^2 q^4}` for `b ∈ {0, …, q}^T` and
`σ ∈ {0, …, T q^2}`. -/
def ipGapEncodeRight (T q : ℕ) (b : List ℕ) (σ : ℕ) : List Bool :=
  let q2 := q * q
  let block1 := (List.range T).flatMap fun i ↦
    (List.range T).flatMap fun j ↦ prodEncRight q2 q2 (b.getD i 0 * b.getD j 0)
  let block2 := (List.range T).flatMap fun i ↦
    (List.range T).flatMap fun j ↦ prodEncRight q2 q2 (q2 - b.getD i 0 * b.getD j 0)
  let block3 := (List.range T).flatMap fun i ↦
    prodEncRight (2 * T * q2 * q) q (b.getD i 0)
  let _ := σ
  let block4 := List.replicate (T * T * (q2 * q2)) true
  block1 ++ block2 ++ block3 ++ block4

private lemma length_flatMap_const {ι : Type*} (l : List ι) (f : ι → List Bool) (m : ℕ)
    (hf : ∀ i ∈ l, (f i).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hf i List.mem_cons_self, ih fun j hj ↦ hf j (List.mem_cons_of_mem i hj)]
    ring

/-- `ipGapEncodeLeft T q a σ` always has length `ipGapDim T q = 5 * T^2 * q^4`. -/
@[simp]
theorem length_ipGapEncodeLeft (T q : ℕ) (a : List ℕ) (σ : ℕ) :
    (ipGapEncodeLeft T q a σ).length = ipGapDim T q := by
  dsimp only [ipGapEncodeLeft, ipGapDim]
  simp only [List.length_append, List.length_replicate, length_unaryVec]
  have hb1 : ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
      prodEncLeft (q * q) (q * q) (q * q - a.getD i 0 * a.getD j 0)).length =
      T * (T * ((q * q) * (q * q))) := by
    rw [length_flatMap_const _ _ (T * ((q * q) * (q * q)))]
    · simp
    · intro i _
      rw [length_flatMap_const _ _ ((q * q) * (q * q))]
      · simp
      · intro j _; exact length_prodEncLeft _ _ _
  have hb3 : ((List.range T).flatMap fun i ↦
      prodEncLeft (2 * T * (q * q) * q) q (2 * σ * a.getD i 0)).length =
      T * (2 * T * (q * q) * q * q) := by
    rw [length_flatMap_const _ _ (2 * T * (q * q) * q * q)]
    · simp
    · intro i _; exact length_prodEncLeft _ _ _
  rw [hb1, hb3]
  ring

/-- `ipGapEncodeRight T q b σ` always has length `ipGapDim T q = 5 * T^2 * q^4`. -/
@[simp]
theorem length_ipGapEncodeRight (T q : ℕ) (b : List ℕ) (σ : ℕ) :
    (ipGapEncodeRight T q b σ).length = ipGapDim T q := by
  dsimp only [ipGapEncodeRight, ipGapDim]
  simp only [List.length_append, List.length_replicate]
  have hb1 : ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
      prodEncRight (q * q) (q * q) (b.getD i 0 * b.getD j 0)).length =
      T * (T * ((q * q) * (q * q))) := by
    rw [length_flatMap_const _ _ (T * ((q * q) * (q * q)))]
    · simp
    · intro i _
      rw [length_flatMap_const _ _ ((q * q) * (q * q))]
      · simp
      · intro j _; exact length_prodEncRight _ _ _
  have hb2 : ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
      prodEncRight (q * q) (q * q) (q * q - b.getD i 0 * b.getD j 0)).length =
      T * (T * ((q * q) * (q * q))) := by
    rw [length_flatMap_const _ _ (T * ((q * q) * (q * q)))]
    · simp
    · intro i _
      rw [length_flatMap_const _ _ ((q * q) * (q * q))]
      · simp
      · intro j _; exact length_prodEncRight _ _ _
  have hb3 : ((List.range T).flatMap fun i ↦
      prodEncRight (2 * T * (q * q) * q) q (b.getD i 0)).length =
      T * (2 * T * (q * q) * q * q) := by
    rw [length_flatMap_const _ _ (2 * T * (q * q) * q * q)]
    · simp
    · intro i _; exact length_prodEncRight _ _ _
  rw [hb1, hb2, hb3]
  ring

private lemma sum_map_range_eq (T : ℕ) (f : ℕ → ℕ) :
    ((List.range T).map f).sum = ∑ i ∈ Finset.range T, f i := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **Chen–Williams Quadratic Encoding Identity**: for `a, b ∈ {0, …, q}^T` and
`σ ∈ {0, …, T q^2}`, the binary inner product `⟨g(a, σ), h(b, σ)⟩` equals
`2 T^2 q^4 - (⟨a, b⟩ - σ)^2`. -/
theorem boolListInnerProd_ipGapEncode_add_sq {T q : ℕ} {a b : List ℕ} {σ : ℕ}
    (ha : a.length = T) (hb : b.length = T)
    (haq : ∀ x ∈ a, x ≤ q) (hbq : ∀ y ∈ b, y ≤ q)
    (hσ : σ ≤ T * q ^ 2) :
    (boolListInnerProd (ipGapEncodeLeft T q a σ) (ipGapEncodeRight T q b σ) : ℤ) +
      ((natListInnerProd a b : ℤ) - (σ : ℤ)) ^ 2 = (ipGapThreshold T q : ℤ) := by
  have hget_a : ∀ i < T, a.getD i 0 ≤ q := fun i hi ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (ha ▸ hi)]
    exact haq _ (List.getElem_mem _)
  have hget_b : ∀ i < T, b.getD i 0 ≤ q := fun i hi ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hb ▸ hi)]
    exact hbq _ (List.getElem_mem _)
  set q2 := q * q
  have hlen1L : ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
      prodEncLeft q2 q2 (q2 - a.getD i 0 * a.getD j 0)).length = T * T * (q2 * q2) := by
    rw [length_flatMap_const _ _ (T * (q2 * q2)) (fun i _ ↦ by
      rw [length_flatMap_const _ _ (q2 * q2) (fun j _ ↦ length_prodEncLeft _ _ _)]; simp)]
    simp; ring
  have hlen1R : ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
      prodEncRight q2 q2 (b.getD i 0 * b.getD j 0)).length = T * T * (q2 * q2) := by
    rw [length_flatMap_const _ _ (T * (q2 * q2)) (fun i _ ↦ by
      rw [length_flatMap_const _ _ (q2 * q2) (fun j _ ↦ length_prodEncRight _ _ _)]; simp)]
    simp; ring
  have hlen2R : ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
      prodEncRight q2 q2 (q2 - b.getD i 0 * b.getD j 0)).length = T * T * (q2 * q2) := by
    rw [length_flatMap_const _ _ (T * (q2 * q2)) (fun i _ ↦ by
      rw [length_flatMap_const _ _ (q2 * q2) (fun j _ ↦ length_prodEncRight _ _ _)]; simp)]
    simp; ring
  have hlen3L : ((List.range T).flatMap fun i ↦
      prodEncLeft (2 * T * q2 * q) q (2 * σ * a.getD i 0)).length = T * (2 * T * q2 * q * q) := by
    rw [length_flatMap_const _ _ (2 * T * q2 * q * q) (fun _ _ ↦ length_prodEncLeft _ _ _)]
    simp
  have hlen3R : ((List.range T).flatMap fun i ↦
      prodEncRight (2 * T * q2 * q) q (b.getD i 0)).length = T * (2 * T * q2 * q * q) := by
    rw [length_flatMap_const _ _ (2 * T * q2 * q * q) (fun _ _ ↦ length_prodEncRight _ _ _)]
    simp
  -- Reassociate block2 on the left as a matching nested flatMap of all-ones blocks.
  have hrep2 : List.replicate (T * T * (q2 * q2)) true =
      (List.range T).flatMap fun _i ↦ (List.range T).flatMap fun _j ↦
        prodEncLeft q2 q2 q2 := by
    have hunit : prodEncLeft q2 q2 q2 = List.replicate (q2 * q2) true := by
      have haux : ∀ m, (List.replicate m true).flatMap (fun b ↦ List.replicate q2 b) =
          List.replicate (m * q2) true := by
        intro m; induction m with
        | zero => simp
        | succ m ih =>
          rw [List.replicate_succ, List.flatMap_cons, ih, Nat.add_mul, one_mul,
            Nat.add_comm (m * q2) q2, List.replicate_add]
      simpa [prodEncLeft, unaryVec] using haux q2
    have hflat : ∀ m k, (List.range m).flatMap (fun _ ↦ List.replicate k true) =
        List.replicate (m * k) true := by
      intro m k; induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
          Nat.add_mul, one_mul, List.replicate_add]
    simp only [hunit, hflat]
    congr 1; ring
  dsimp only [ipGapEncodeLeft, ipGapEncodeRight]
  simp only [List.append_assoc]
  rw [boolListInnerProd_append (hlen1L.trans hlen1R.symm),
    boolListInnerProd_append (by rw [List.length_replicate, hlen2R]),
    boolListInnerProd_append (hlen3L.trans hlen3R.symm)]
  -- Evaluate block 1 + block 2.
  have hs1 : boolListInnerProd
      ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
        prodEncLeft q2 q2 (q2 - a.getD i 0 * a.getD j 0))
      ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
        prodEncRight q2 q2 (b.getD i 0 * b.getD j 0)) =
      ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
        (q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) := by
    rw [boolListInnerProd_flatMap _ _ _ fun i _ ↦ by
      rw [length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncLeft _ _ _),
        length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncRight _ _ _)]]
    rw [sum_map_range_eq]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [boolListInnerProd_flatMap _ _ _ fun _ _ ↦
      (length_prodEncLeft _ _ _).trans (length_prodEncRight _ _ _).symm, sum_map_range_eq]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    refine boolListInnerProd_prodEnc (Nat.sub_le _ _) ?_
    exact Nat.mul_le_mul (hget_b i (Finset.mem_range.mp hi)) (hget_b j (Finset.mem_range.mp hj))
  have hs2 : boolListInnerProd (List.replicate (T * T * (q2 * q2)) true)
      ((List.range T).flatMap fun i ↦ (List.range T).flatMap fun j ↦
        prodEncRight q2 q2 (q2 - b.getD i 0 * b.getD j 0)) =
      ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
        q2 * (q2 - b.getD i 0 * b.getD j 0) := by
    rw [hrep2, boolListInnerProd_flatMap _ _ _ fun _ _ ↦ by
      rw [length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncLeft _ _ _),
        length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncRight _ _ _)]]
    rw [sum_map_range_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [boolListInnerProd_flatMap _ _ _ fun _ _ ↦
      (length_prodEncLeft _ _ _).trans (length_prodEncRight _ _ _).symm, sum_map_range_eq]
    refine Finset.sum_congr rfl fun j _ ↦ boolListInnerProd_prodEnc le_rfl (Nat.sub_le _ _)
  have hs3 : boolListInnerProd
      ((List.range T).flatMap fun i ↦ prodEncLeft (2 * T * q2 * q) q (2 * σ * a.getD i 0))
      ((List.range T).flatMap fun i ↦ prodEncRight (2 * T * q2 * q) q (b.getD i 0)) =
      2 * σ * natListInnerProd a b := by
    rw [boolListInnerProd_flatMap _ _ _ fun _ _ ↦
      (length_prodEncLeft _ _ _).trans (length_prodEncRight _ _ _).symm, sum_map_range_eq,
      natListInnerProd_eq_sum_range ha hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hiT := Finset.mem_range.mp hi
    have hbd : 2 * σ * a.getD i 0 ≤ 2 * T * q2 * q := by
      have h1 : 2 * σ ≤ 2 * T * q2 := by dsimp [q2]; nlinarith
      calc
        2 * σ * a.getD i 0 ≤ (2 * T * q2) * q := Nat.mul_le_mul h1 (hget_a i hiT)
        _ = 2 * T * q2 * q := by ring
    rw [boolListInnerProd_prodEnc hbd (hget_b i hiT)]
    ring
  have hσ_sq : σ * σ ≤ T * T * (q2 * q2) := by
    have hσ' : σ ≤ T * q2 := by simpa [q2, sq] using hσ
    calc
      σ * σ ≤ (T * q2) * (T * q2) := Nat.mul_le_mul hσ' hσ'
      _ = T * T * (q2 * q2) := by ring
  have hs4 : boolListInnerProd
      (unaryVec (T * T * (q2 * q2)) (T * T * (q2 * q2) - σ * σ))
      (List.replicate (T * T * (q2 * q2)) true) =
      T * T * (q2 * q2) - σ * σ :=
    boolListInnerProd_unaryVec_ones (Nat.sub_le _ _)
  rw [hs1, hs2, hs3, hs4]
  -- Combine block 1 and block 2 pointwise: `(q2 - A) * B + q2 * (q2 - B) = q2^2 - A * B`.
  have hs12 : ((∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
        (q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) : ℕ) : ℤ) +
      ((∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
        q2 * (q2 - b.getD i 0 * b.getD j 0) : ℕ) : ℤ) =
      (T : ℤ) ^ 2 * (q : ℤ) ^ 4 - (natListInnerProd a b : ℤ) ^ 2 := by
    have hpt : ∀ i ∈ Finset.range T, ∀ j ∈ Finset.range T,
        (((q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) : ℕ) : ℤ) +
          ((q2 * (q2 - b.getD i 0 * b.getD j 0) : ℕ) : ℤ) =
        (q2 : ℤ) * q2 -
          ((a.getD i 0 : ℤ) * (b.getD i 0 : ℤ)) * ((a.getD j 0 : ℤ) * (b.getD j 0 : ℤ)) := by
      intro i hi j hj
      have hA : a.getD i 0 * a.getD j 0 ≤ q2 :=
        Nat.mul_le_mul (hget_a i (Finset.mem_range.mp hi)) (hget_a j (Finset.mem_range.mp hj))
      have hB : b.getD i 0 * b.getD j 0 ≤ q2 :=
        Nat.mul_le_mul (hget_b i (Finset.mem_range.mp hi)) (hget_b j (Finset.mem_range.mp hj))
      have hnat : (q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) +
            q2 * (q2 - b.getD i 0 * b.getD j 0) +
            (a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) =
          q2 * q2 := by
        calc
          (q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) +
              q2 * (q2 - b.getD i 0 * b.getD j 0) +
              (a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0)
              = (q2 - a.getD i 0 * a.getD j 0 + a.getD i 0 * a.getD j 0) *
                  (b.getD i 0 * b.getD j 0) + q2 * (q2 - b.getD i 0 * b.getD j 0) := by ring
          _ = q2 * (b.getD i 0 * b.getD j 0 + (q2 - b.getD i 0 * b.getD j 0)) := by
            rw [Nat.sub_add_cancel hA]; ring
          _ = q2 * q2 := by rw [Nat.add_sub_cancel' hB]
      have hz : (((q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) : ℕ) : ℤ) +
            ((q2 * (q2 - b.getD i 0 * b.getD j 0) : ℕ) : ℤ) +
            (((a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) : ℕ) : ℤ) =
          ((q2 * q2 : ℕ) : ℤ) := by
        simpa only [Nat.cast_add] using congrArg (Nat.cast (R := ℤ)) hnat
      have hcomm : (((a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) : ℕ) : ℤ) =
          ((a.getD i 0 : ℤ) * (b.getD i 0 : ℤ)) * ((a.getD j 0 : ℤ) * (b.getD j 0 : ℤ)) := by
        push_cast; ring
      have hqq : ((q2 * q2 : ℕ) : ℤ) = (q2 : ℤ) * q2 := Nat.cast_mul q2 q2
      linarith
    have hsum_eq :
        ((∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
            (q2 - a.getD i 0 * a.getD j 0) * (b.getD i 0 * b.getD j 0) : ℕ) : ℤ) +
        ((∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
            q2 * (q2 - b.getD i 0 * b.getD j 0) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
          ((q2 : ℤ) * q2 -
            ((a.getD i 0 : ℤ) * (b.getD i 0 : ℤ)) * ((a.getD j 0 : ℤ) * (b.getD j 0 : ℤ))) := by
      simp only [Nat.cast_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j hj ↦ hpt i hi j hj
    rw [hsum_eq]
    have hsub_sum :
        ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
          ((q2 : ℤ) * q2 -
            ((a.getD i 0 : ℤ) * (b.getD i 0 : ℤ)) * ((a.getD j 0 : ℤ) * (b.getD j 0 : ℤ))) =
        (∑ _i ∈ Finset.range T, ∑ _j ∈ Finset.range T, ((q2 : ℤ) * q2)) -
        (∑ i ∈ Finset.range T, ((a.getD i 0 : ℤ) * (b.getD i 0 : ℤ))) *
          (∑ j ∈ Finset.range T, ((a.getD j 0 : ℤ) * (b.getD j 0 : ℤ))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1; exact Finset.sum_comm
    rw [hsub_sum, natListInnerProd_eq_sum_range ha hb]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, q2]
    ring
  have h4 : ((T * T * (q2 * q2) - σ * σ : ℕ) : ℤ) + (σ : ℤ) ^ 2 = (T : ℤ) ^ 2 * (q : ℤ) ^ 4 := by
    have hnat : T * T * (q2 * q2) - σ * σ + σ * σ = T * T * (q2 * q2) := Nat.sub_add_cancel hσ_sq
    have hz : ((T * T * (q2 * q2) - σ * σ : ℕ) : ℤ) + ((σ * σ : ℕ) : ℤ) =
        ((T * T * (q2 * q2) : ℕ) : ℤ) := by
      simpa only [Nat.cast_add] using congrArg (Nat.cast (R := ℤ)) hnat
    have hs : ((σ * σ : ℕ) : ℤ) = (σ : ℤ) ^ 2 := by push_cast; ring
    have hr : ((T * T * (q2 * q2) : ℕ) : ℤ) = (T : ℤ) ^ 2 * (q : ℤ) ^ 4 := by
      dsimp only [q2]; push_cast; ring
    linarith
  have hth : (ipGapThreshold T q : ℤ) = 2 * (T : ℤ) ^ 2 * (q : ℤ) ^ 4 := by
    simp [ipGapThreshold]
  have h3 : ((2 * σ * natListInnerProd a b : ℕ) : ℤ) =
      2 * (σ : ℤ) * (natListInnerProd a b : ℤ) := by push_cast; ring
  have hsq : ((natListInnerProd a b : ℤ) - (σ : ℤ)) ^ 2 =
      (natListInnerProd a b : ℤ) ^ 2 - 2 * (σ : ℤ) * (natListInnerProd a b : ℤ) + (σ : ℤ) ^ 2 := by
    ring
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, h3]
  linarith

/-- Completeness of the Chen–Williams encoding: if `⟨a, b⟩ = σ`, then
`⟨g(a, σ), h(b, σ)⟩ = Γ`. -/
theorem boolListInnerProd_ipGapEncode_eq_of_eq {T q : ℕ} {a b : List ℕ} {σ : ℕ}
    (ha : a.length = T) (hb : b.length = T)
    (haq : ∀ x ∈ a, x ≤ q) (hbq : ∀ y ∈ b, y ≤ q)
    (hσ : σ ≤ T * q ^ 2) (heq : natListInnerProd a b = σ) :
    boolListInnerProd (ipGapEncodeLeft T q a σ) (ipGapEncodeRight T q b σ) =
      ipGapThreshold T q := by
  have h := boolListInnerProd_ipGapEncode_add_sq ha hb haq hbq hσ
  rw [heq, sub_self, zero_pow (by decide), add_zero] at h
  exact Int.ofNat.inj h

/-- Soundness of the Chen–Williams encoding: if `⟨a, b⟩ ≠ σ`, then
`⟨g(a, σ), h(b, σ)⟩ + 1 ≤ Γ` (in particular `< Γ`). -/
theorem boolListInnerProd_ipGapEncode_lt_of_ne {T q : ℕ} {a b : List ℕ} {σ : ℕ}
    (ha : a.length = T) (hb : b.length = T)
    (haq : ∀ x ∈ a, x ≤ q) (hbq : ∀ y ∈ b, y ≤ q)
    (hσ : σ ≤ T * q ^ 2) (hne : natListInnerProd a b ≠ σ) :
    boolListInnerProd (ipGapEncodeLeft T q a σ) (ipGapEncodeRight T q b σ) <
      ipGapThreshold T q := by
  have h := boolListInnerProd_ipGapEncode_add_sq ha hb haq hbq hσ
  have hdiff : (natListInnerProd a b : ℤ) - (σ : ℤ) ≠ 0 := by
    intro hz
    exact hne (Int.ofNat.inj (sub_eq_zero.mp hz))
  have hsq : (1 : ℤ) ≤ ((natListInnerProd a b : ℤ) - (σ : ℤ)) ^ 2 := by
    have habs : (1 : ℤ) ≤ |(natListInnerProd a b : ℤ) - (σ : ℤ)| := Int.one_le_abs hdiff
    nlinarith [sq_abs ((natListInnerProd a b : ℤ) - (σ : ℤ))]
  have hlt : (boolListInnerProd (ipGapEncodeLeft T q a σ) (ipGapEncodeRight T q b σ) : ℤ) <
      (ipGapThreshold T q : ℤ) := by linarith
  exact_mod_cast hlt

/-- Exact bound `⟨g(a, σ), h(b, σ)⟩ ≤ Γ` on all valid inputs. -/
theorem boolListInnerProd_ipGapEncode_le {T q : ℕ} {a b : List ℕ} {σ : ℕ}
    (ha : a.length = T) (hb : b.length = T)
    (haq : ∀ x ∈ a, x ≤ q) (hbq : ∀ y ∈ b, y ≤ q)
    (hσ : σ ≤ T * q ^ 2) :
    boolListInnerProd (ipGapEncodeLeft T q a σ) (ipGapEncodeRight T q b σ) ≤
      ipGapThreshold T q := by
  have h := boolListInnerProd_ipGapEncode_add_sq ha hb haq hbq hσ
  have hsq : (0 : ℤ) ≤ ((natListInnerProd a b : ℤ) - (σ : ℤ)) ^ 2 := sq_nonneg _
  exact_mod_cast (by linarith :
    (boolListInnerProd (ipGapEncodeLeft T q a σ) (ipGapEncodeRight T q b σ) : ℤ) ≤
      (ipGapThreshold T q : ℤ))

private lemma slice_flatMap_eq {ι : Type*} (l : List ι) (f : ι → List Bool) (m k : ℕ)
    (hf : ∀ i ∈ l, (f i).length = m) (hk : k < l.length) :
    ((l.flatMap f).drop (k * m)).take m = f l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons i is ih =>
    simp only [List.flatMap_cons]
    have hi : (f i).length = m := hf i List.mem_cons_self
    rcases k with _ | k'
    · simp [List.take_append_of_le_length hi.symm.le, hi]
    · simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      rw [show (k' + 1) * m = (f i).length + k' * m by rw [hi]; ring,
        List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append,
        Nat.add_sub_cancel_left]
      exact ih k' (fun j hj ↦ hf j (List.mem_cons_of_mem i hj)) hk

/-- `ipGapEncodeLeft T q · σ` is injective on vectors in `{0, …, q}^T`. -/
theorem ipGapEncodeLeft_injective {T q σ : ℕ} {a₁ a₂ : List ℕ}
    (ha₁ : a₁.length = T) (ha₂ : a₂.length = T)
    (hq₁ : ∀ x ∈ a₁, x ≤ q) (hq₂ : ∀ x ∈ a₂, x ≤ q)
    (heq : ipGapEncodeLeft T q a₁ σ = ipGapEncodeLeft T q a₂ σ) : a₁ = a₂ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · refine List.ext_getElem (ha₁.trans ha₂.symm) fun i h₁ h₂ ↦ ?_
    have z₁ : a₁[i] = 0 := Nat.eq_zero_of_le_zero (hq₁ _ (List.getElem_mem h₁))
    have z₂ : a₂[i] = 0 := Nat.eq_zero_of_le_zero (hq₂ _ (List.getElem_mem h₂))
    omega
  · set q2 := q * q
    have hq2_pos : 0 < q2 := Nat.mul_pos (Nat.pos_of_ne_zero hq0) (Nat.pos_of_ne_zero hq0)
    refine List.ext_getElem (ha₁.trans ha₂.symm) fun i h₁ h₂ ↦ ?_
    have hiT : i < T := ha₁ ▸ h₁
    -- Extract the first block of length `T * (T * (q2 * q2))`, then slice diagonal `(i, i)`.
    have hblk1 : ∀ a : List ℕ,
        (ipGapEncodeLeft T q a σ).take (T * (T * (q2 * q2))) =
          (List.range T).flatMap fun r ↦ (List.range T).flatMap fun c ↦
            prodEncLeft q2 q2 (q2 - a.getD r 0 * a.getD c 0) := by
      intro a
      dsimp only [ipGapEncodeLeft]
      simp only [List.append_assoc]
      have hl : ((List.range T).flatMap fun r ↦ (List.range T).flatMap fun c ↦
          prodEncLeft q2 q2 (q2 - a.getD r 0 * a.getD c 0)).length = T * (T * (q2 * q2)) := by
        rw [length_flatMap_const _ _ (T * (q2 * q2)) (fun _ _ ↦ by
          rw [length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncLeft _ _ _)]; simp)]
        simp
      rw [List.take_append_of_le_length hl.symm.le, List.take_of_length_le hl.le]
    have hdiag : ∀ a : List ℕ,
        (((((ipGapEncodeLeft T q a σ).take (T * (T * (q2 * q2)))).drop
          (i * (T * (q2 * q2)))).take (T * (q2 * q2))).drop (i * (q2 * q2))).take (q2 * q2) =
          prodEncLeft q2 q2 (q2 - a.getD i 0 * a.getD i 0) := by
      intro a
      rw [hblk1 a,
        slice_flatMap_eq (List.range T) _ (T * (q2 * q2)) i (fun _ _ ↦ by
          rw [length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncLeft _ _ _)]; simp)
          (by simpa using hiT),
        List.getElem_range,
        slice_flatMap_eq (List.range T) _ (q2 * q2) i (fun _ _ ↦ length_prodEncLeft _ _ _)
          (by simpa using hiT),
        List.getElem_range]
    have hprod_eq : prodEncLeft q2 q2 (q2 - a₁.getD i 0 * a₁.getD i 0) =
        prodEncLeft q2 q2 (q2 - a₂.getD i 0 * a₂.getD i 0) := by
      rw [← hdiag a₁, ← hdiag a₂, heq]
    have hcnt : ∀ x ≤ q2, (prodEncLeft q2 q2 x).count true = x * q2 := by
      intro x hx
      have haux : ∀ l : List Bool,
          (l.flatMap fun b ↦ List.replicate q2 b).count true = l.count true * q2 := by
        intro l; induction l with
        | nil => simp
        | cons b bs ih => cases b <;> simp [ih, List.count_replicate, Nat.add_mul, Nat.add_comm]
      rw [prodEncLeft, haux, count_true_unaryVec hx]
    have hc := congrArg (List.count true) hprod_eq
    rw [hcnt _ (Nat.sub_le _ _), hcnt _ (Nat.sub_le _ _)] at hc
    have hsub := Nat.eq_of_mul_eq_mul_right hq2_pos hc
    have hg₁ : a₁.getD i 0 = a₁[i] := by simp [List.getD_eq_getElem?_getD, h₁]
    have hg₂ : a₂.getD i 0 = a₂[i] := by simp [List.getD_eq_getElem?_getD, h₂]
    rw [hg₁, hg₂] at hsub
    have hsq₁ : a₁[i] * a₁[i] ≤ q2 :=
      Nat.mul_le_mul (hq₁ _ (List.getElem_mem h₁)) (hq₁ _ (List.getElem_mem h₁))
    have hsq₂ : a₂[i] * a₂[i] ≤ q2 :=
      Nat.mul_le_mul (hq₂ _ (List.getElem_mem h₂)) (hq₂ _ (List.getElem_mem h₂))
    have hsq_eq : a₁[i] * a₁[i] = a₂[i] * a₂[i] := by omega
    nlinarith

/-- `ipGapEncodeRight T q · σ` is injective on vectors in `{0, …, q}^T`. -/
theorem ipGapEncodeRight_injective {T q σ : ℕ} {b₁ b₂ : List ℕ}
    (hb₁ : b₁.length = T) (hb₂ : b₂.length = T)
    (hq₁ : ∀ y ∈ b₁, y ≤ q) (hq₂ : ∀ y ∈ b₂, y ≤ q)
    (heq : ipGapEncodeRight T q b₁ σ = ipGapEncodeRight T q b₂ σ) : b₁ = b₂ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · refine List.ext_getElem (hb₁.trans hb₂.symm) fun i h₁ h₂ ↦ ?_
    have z₁ : b₁[i] = 0 := Nat.eq_zero_of_le_zero (hq₁ _ (List.getElem_mem h₁))
    have z₂ : b₂[i] = 0 := Nat.eq_zero_of_le_zero (hq₂ _ (List.getElem_mem h₂))
    omega
  · set q2 := q * q
    have hq2_pos : 0 < q2 := Nat.mul_pos (Nat.pos_of_ne_zero hq0) (Nat.pos_of_ne_zero hq0)
    refine List.ext_getElem (hb₁.trans hb₂.symm) fun i h₁ h₂ ↦ ?_
    have hiT : i < T := hb₁ ▸ h₁
    have hblk1 : ∀ b : List ℕ,
        (ipGapEncodeRight T q b σ).take (T * (T * (q2 * q2))) =
          (List.range T).flatMap fun r ↦ (List.range T).flatMap fun c ↦
            prodEncRight q2 q2 (b.getD r 0 * b.getD c 0) := by
      intro b
      dsimp only [ipGapEncodeRight]
      simp only [List.append_assoc]
      have hl : ((List.range T).flatMap fun r ↦ (List.range T).flatMap fun c ↦
          prodEncRight q2 q2 (b.getD r 0 * b.getD c 0)).length = T * (T * (q2 * q2)) := by
        rw [length_flatMap_const _ _ (T * (q2 * q2)) (fun _ _ ↦ by
          rw [length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncRight _ _ _)]; simp)]
        simp
      rw [List.take_append_of_le_length hl.symm.le, List.take_of_length_le hl.le]
    have hdiag : ∀ b : List ℕ,
        (((((ipGapEncodeRight T q b σ).take (T * (T * (q2 * q2)))).drop
          (i * (T * (q2 * q2)))).take (T * (q2 * q2))).drop (i * (q2 * q2))).take (q2 * q2) =
          prodEncRight q2 q2 (b.getD i 0 * b.getD i 0) := by
      intro b
      rw [hblk1 b,
        slice_flatMap_eq (List.range T) _ (T * (q2 * q2)) i (fun _ _ ↦ by
          rw [length_flatMap_const _ _ (q2 * q2) (fun _ _ ↦ length_prodEncRight _ _ _)]; simp)
          (by simpa using hiT),
        List.getElem_range,
        slice_flatMap_eq (List.range T) _ (q2 * q2) i (fun _ _ ↦ length_prodEncRight _ _ _)
          (by simpa using hiT),
        List.getElem_range]
    have hprod_eq : prodEncRight q2 q2 (b₁.getD i 0 * b₁.getD i 0) =
        prodEncRight q2 q2 (b₂.getD i 0 * b₂.getD i 0) := by
      rw [← hdiag b₁, ← hdiag b₂, heq]
    have hcnt : ∀ y ≤ q2, (prodEncRight q2 q2 y).count true = q2 * y := by
      intro y hy
      have haux : ∀ m : ℕ,
          ((List.replicate m ()).flatMap fun _ ↦ unaryVec q2 y).count true = m * y := by
        intro m; induction m with
        | zero => simp
        | succ m ih =>
          simp [List.replicate_succ, ih, count_true_unaryVec hy, Nat.add_mul, Nat.add_comm]
      exact haux q2
    have hg₁ : b₁.getD i 0 = b₁[i] := by simp [List.getD_eq_getElem?_getD, h₁]
    have hg₂ : b₂.getD i 0 = b₂[i] := by simp [List.getD_eq_getElem?_getD, h₂]
    have hsq₁ : b₁[i] * b₁[i] ≤ q2 :=
      Nat.mul_le_mul (hq₁ _ (List.getElem_mem h₁)) (hq₁ _ (List.getElem_mem h₁))
    have hsq₂ : b₂[i] * b₂[i] ≤ q2 :=
      Nat.mul_le_mul (hq₂ _ (List.getElem_mem h₂)) (hq₂ _ (List.getElem_mem h₂))
    rw [hg₁, hg₂] at hprod_eq
    have hc := congrArg (List.count true) hprod_eq
    rw [hcnt _ hsq₁, hcnt _ hsq₂] at hc
    have hsq_eq := Nat.eq_of_mul_eq_mul_left hq2_pos hc
    nlinarith

/-- Input encoding for uniform polynomial-time computation of `ipGapEncodeLeft` and
`ipGapEncodeRight`: `(T, q)` in unary and `(vec, σ)` in standard list/binary encodings. -/
abbrev encIPGapInput : ((ℕ × ℕ) × List ℕ) × ℕ ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) (encList encNat)) encNat

open ComputableInPolyTime in
private lemma nat_of_unary : ComputableInPolyTime (fun n : ℕ ↦ n) encUnary encNat :=
  have hpb : PolyBounded (fun a : ℕ ↦ (encUnary a).length) (fun n : ℕ ↦ n) := by
    simpa [encUnary_apply] using PolyBounded.self (size := fun a : ℕ ↦ (encUnary a).length)
  ComputableInO.unaryToNat.computableInPolyTime hpb hpb

open ComputableInPolyTime in
private lemma computableInPolyTime_unaryVecL {α : Type} {enc : α ↪ List Bool}
    {u x : α → ℕ} (hu : ComputableInPolyTime u enc encUnary)
    (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun z ↦ unaryVec (u z) (x z)) enc (encList encBool) := by
  have hm : ComputableInPolyTime (fun z ↦ min (x z) (u z)) enc encUnary := by
    have heq : (fun z ↦ min (x z) (u z)) = fun z ↦
        (List.range (u z)).countP fun k ↦ decide (k < x z) := by
      funext z
      have haux : ∀ m n, ((List.range m).countP fun k ↦ decide (k < n)) = min n m := by
        intro m n; induction m with
        | zero => simp
        | succ m ih =>
          rw [List.range_succ, List.countP_append, ih, List.countP_singleton]
          by_cases h : m < n <;> simp [h] <;> omega
      exact (haux (u z) (x z)).symm
    rw [heq]
    refine countPWithInput (encA := encUnary) (unary_range' hu) ?_
    exact binary_lt.comp ((nat_of_unary.comp (snd enc encUnary)).prod
      (hx.comp (fst enc encUnary)))
  have hdiff : ComputableInPolyTime (fun z ↦ u z - min (x z) (u z)) enc encUnary :=
    unary_sub' hu hm
  exact (listAppend encBool).comp
    ((replicate (encA := encBool) hm (const true)).prod
      (replicate (encA := encBool) hdiff (const false)))

open ComputableInPolyTime in
private lemma computableInPolyTime_prodEncLeftL {α : Type} {enc : α ↪ List Bool}
    {u v x : α → ℕ} (hu : ComputableInPolyTime u enc encUnary)
    (hv : ComputableInPolyTime v enc encUnary)
    (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun z ↦ prodEncLeft (u z) (v z) (x z)) enc (encList encBool) :=
  flatMapWithInput (encA := encBool) (encB := encBool)
    (computableInPolyTime_unaryVecL hu hx)
    (replicate (encA := encBool) (hv.comp (fst enc encBool)) (snd enc encBool))

open ComputableInPolyTime in
private lemma computableInPolyTime_prodEncRightL {α : Type} {enc : α ↪ List Bool}
    {u v y : α → ℕ} (hu : ComputableInPolyTime u enc encUnary)
    (hv : ComputableInPolyTime v enc encUnary)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun z ↦ prodEncRight (u z) (v z) (y z)) enc (encList encBool) := by
  have heq : (fun z ↦ prodEncRight (u z) (v z) (y z)) =
      fun z ↦ (List.range (u z)).flatMap fun _ ↦ unaryVec (v z) (y z) := by
    funext z
    dsimp only [prodEncRight]
    have haux : ∀ m (w : List Bool),
        ((List.replicate m ()).flatMap fun _ ↦ w) = (List.range m).flatMap fun _ ↦ w := by
      intro m w; induction m with
      | zero => simp
      | succ m ih =>
        rw [List.replicate_succ, List.flatMap_cons, ih, List.range_succ, List.flatMap_append,
          List.flatMap_singleton]
        have hcomm : ∀ k : ℕ, w ++ (List.range k).flatMap (fun _ ↦ w) =
            (List.range k).flatMap (fun _ ↦ w) ++ w := by
          intro k; induction k with
          | zero => simp
          | succ k ik =>
            rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc,
              ik]
        exact hcomm m
    exact haux (u z) _
  rw [heq]
  exact flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' hu)
    (computableInPolyTime_unaryVecL (hv.comp (fst enc encUnary)) (hy.comp (fst enc encUnary)))

open ComputableInPolyTime in
private lemma nat_mul' {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encNat) (hg : ComputableInPolyTime g enc encNat) :
    ComputableInPolyTime (fun z ↦ f z * g z) enc encNat :=
  binary_mul.comp (hf.prod hg)

open ComputableInPolyTime in
private lemma nat_sub' {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encNat) (hg : ComputableInPolyTime g enc encNat) :
    ComputableInPolyTime (fun z ↦ f z - g z) enc encNat :=
  binary_sub.comp (hf.prod hg)

open ComputableInPolyTime in
private lemma listAppend' {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {u v : α → List β} (hu : ComputableInPolyTime u enc (encList encB))
    (hv : ComputableInPolyTime v enc (encList encB)) :
    ComputableInPolyTime (fun z ↦ u z ++ v z) enc (encList encB) :=
  (listAppend encB).comp (hu.prod hv)

open ComputableInPolyTime in
private lemma bitsOfList' {α : Type} {enc : α ↪ List Bool} {u : α → List Bool}
    (hu : ComputableInPolyTime u enc (encList encBool)) :
    ComputableInPolyTime u enc encBits :=
  (bits_encList_polyTime encBool).2.comp hu

open ComputableInPolyTime in
/-- **Uniform polynomial-time computability of `ipGapEncodeLeft`**: given `T` and `q` in unary,
`a : List ℕ`, and `σ : ℕ`, `ipGapEncodeLeft T q a σ` runs in time `poly(T, q, |a|, |σ|)` on a
deterministic multi-tape Turing machine. -/
theorem computableInPolyTime_ipGapEncodeLeft :
    ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
      ipGapEncodeLeft p.1.1.1 p.1.1.2 p.1.2 p.2) encIPGapInput encBits := by
  have p_tqa : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1) encIPGapInput
      (encPair (encPair encUnary encUnary) (encList encNat)) := fst _ _
  have p_tq : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1) encIPGapInput
      (encPair encUnary encUnary) := (fst _ _).comp p_tqa
  have hT : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1.1)
      encIPGapInput encUnary := (fst _ _).comp p_tq
  have hq : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1.2)
      encIPGapInput encUnary := (snd _ _).comp p_tq
  have ha : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.2)
      encIPGapInput (encList encNat) := (snd _ _).comp p_tqa
  have hσ : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.2)
      encIPGapInput encNat := snd _ _
  have hq2u := unary_mul' hq hq
  have hq2n : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1.2 * p.1.1.2)
      encIPGapInput encNat := nat_of_unary.comp hq2u
  have hT2q4u := unary_mul' (unary_mul' hT hT) (unary_mul' hq2u hq2u)
  have hT2q4n : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
        p.1.1.1 * p.1.1.1 * ((p.1.1.2 * p.1.1.2) * (p.1.1.2 * p.1.1.2)))
      encIPGapInput encNat := nat_of_unary.comp hT2q4u
  have hU3 := unary_mul' (unary_mul' (unary_mul' (const 2) hT) hq2u) hq
  have hb1 : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
        (List.range p.1.1.1).flatMap fun i ↦ (List.range p.1.1.1).flatMap fun j ↦
          prodEncLeft (p.1.1.2 * p.1.1.2) (p.1.1.2 * p.1.1.2)
            (p.1.1.2 * p.1.1.2 - p.1.2.getD i 0 * p.1.2.getD j 0))
      encIPGapInput (encList encBool) := by
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' hT) ?_
    have p1 : ComputableInPolyTime Prod.fst (encPair encIPGapInput encUnary) encIPGapInput :=
      fst _ _
    have i1 : ComputableInPolyTime Prod.snd (encPair encIPGapInput encUnary) encUnary := snd _ _
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' (hT.comp p1)) ?_
    have p2 : ComputableInPolyTime Prod.fst
        (encPair (encPair encIPGapInput encUnary) encUnary) (encPair encIPGapInput encUnary) :=
      fst _ _
    have p12 : ComputableInPolyTime (fun r : ((((ℕ × ℕ) × List ℕ) × ℕ) × ℕ) × ℕ ↦ r.1.1)
        (encPair (encPair encIPGapInput encUnary) encUnary) encIPGapInput := p1.comp p2
    have hgi := listGetDWithInput (ha.comp p12) (i1.comp p2) 0
    have hgj := listGetDWithInput (ha.comp p12) (snd _ _) 0
    exact computableInPolyTime_prodEncLeftL (hq2u.comp p12) (hq2u.comp p12)
      (nat_sub' (hq2n.comp p12) (nat_mul' hgi hgj))
  have hb2 := replicate (encA := encBool) hT2q4u (const true)
  have hb3 : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
        (List.range p.1.1.1).flatMap fun i ↦
          prodEncLeft (2 * p.1.1.1 * (p.1.1.2 * p.1.1.2) * p.1.1.2) p.1.1.2
            (2 * p.2 * p.1.2.getD i 0))
      encIPGapInput (encList encBool) := by
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' hT) ?_
    have p1 : ComputableInPolyTime Prod.fst (encPair encIPGapInput encUnary) encIPGapInput :=
      fst _ _
    exact computableInPolyTime_prodEncLeftL (hU3.comp p1) (hq.comp p1)
      (nat_mul' (nat_mul' (const 2) (hσ.comp p1))
        (listGetDWithInput (ha.comp p1) (snd _ _) 0))
  have hb4 := computableInPolyTime_unaryVecL hT2q4u (nat_sub' hT2q4n (nat_mul' hσ hσ))
  exact bitsOfList' (listAppend' (listAppend' (listAppend' hb1 hb2) hb3) hb4)

open ComputableInPolyTime in
/-- **Uniform polynomial-time computability of `ipGapEncodeRight`**: given `T` and `q` in unary,
`b : List ℕ`, and `σ : ℕ`, `ipGapEncodeRight T q b σ` runs in time `poly(T, q, |b|, |σ|)` on a
deterministic multi-tape Turing machine. -/
theorem computableInPolyTime_ipGapEncodeRight :
    ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
      ipGapEncodeRight p.1.1.1 p.1.1.2 p.1.2 p.2) encIPGapInput encBits := by
  have p_tqa : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1) encIPGapInput
      (encPair (encPair encUnary encUnary) (encList encNat)) := fst _ _
  have p_tq : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1) encIPGapInput
      (encPair encUnary encUnary) := (fst _ _).comp p_tqa
  have hT : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1.1)
      encIPGapInput encUnary := (fst _ _).comp p_tq
  have hq : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1.2)
      encIPGapInput encUnary := (snd _ _).comp p_tq
  have hb : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.2)
      encIPGapInput (encList encNat) := (snd _ _).comp p_tqa
  have hq2u := unary_mul' hq hq
  have hq2n : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦ p.1.1.2 * p.1.1.2)
      encIPGapInput encNat := nat_of_unary.comp hq2u
  have hT2q4u := unary_mul' (unary_mul' hT hT) (unary_mul' hq2u hq2u)
  have hU3 := unary_mul' (unary_mul' (unary_mul' (const 2) hT) hq2u) hq
  have hb1 : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
        (List.range p.1.1.1).flatMap fun i ↦ (List.range p.1.1.1).flatMap fun j ↦
          prodEncRight (p.1.1.2 * p.1.1.2) (p.1.1.2 * p.1.1.2)
            (p.1.2.getD i 0 * p.1.2.getD j 0))
      encIPGapInput (encList encBool) := by
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' hT) ?_
    have p1 : ComputableInPolyTime Prod.fst (encPair encIPGapInput encUnary) encIPGapInput :=
      fst _ _
    have i1 : ComputableInPolyTime Prod.snd (encPair encIPGapInput encUnary) encUnary := snd _ _
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' (hT.comp p1)) ?_
    have p2 : ComputableInPolyTime Prod.fst
        (encPair (encPair encIPGapInput encUnary) encUnary) (encPair encIPGapInput encUnary) :=
      fst _ _
    have p12 : ComputableInPolyTime (fun r : ((((ℕ × ℕ) × List ℕ) × ℕ) × ℕ) × ℕ ↦ r.1.1)
        (encPair (encPair encIPGapInput encUnary) encUnary) encIPGapInput := p1.comp p2
    exact computableInPolyTime_prodEncRightL (hq2u.comp p12) (hq2u.comp p12)
      (nat_mul' (listGetDWithInput (hb.comp p12) (i1.comp p2) 0)
        (listGetDWithInput (hb.comp p12) (snd _ _) 0))
  have hb2 : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
        (List.range p.1.1.1).flatMap fun i ↦ (List.range p.1.1.1).flatMap fun j ↦
          prodEncRight (p.1.1.2 * p.1.1.2) (p.1.1.2 * p.1.1.2)
            (p.1.1.2 * p.1.1.2 - p.1.2.getD i 0 * p.1.2.getD j 0))
      encIPGapInput (encList encBool) := by
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' hT) ?_
    have p1 : ComputableInPolyTime Prod.fst (encPair encIPGapInput encUnary) encIPGapInput :=
      fst _ _
    have i1 : ComputableInPolyTime Prod.snd (encPair encIPGapInput encUnary) encUnary := snd _ _
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' (hT.comp p1)) ?_
    have p2 : ComputableInPolyTime Prod.fst
        (encPair (encPair encIPGapInput encUnary) encUnary) (encPair encIPGapInput encUnary) :=
      fst _ _
    have p12 : ComputableInPolyTime (fun r : ((((ℕ × ℕ) × List ℕ) × ℕ) × ℕ) × ℕ ↦ r.1.1)
        (encPair (encPair encIPGapInput encUnary) encUnary) encIPGapInput := p1.comp p2
    exact computableInPolyTime_prodEncRightL (hq2u.comp p12) (hq2u.comp p12)
      (nat_sub' (hq2n.comp p12)
        (nat_mul' (listGetDWithInput (hb.comp p12) (i1.comp p2) 0)
          (listGetDWithInput (hb.comp p12) (snd _ _) 0)))
  have hb3 : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℕ) × ℕ ↦
        (List.range p.1.1.1).flatMap fun i ↦
          prodEncRight (2 * p.1.1.1 * (p.1.1.2 * p.1.1.2) * p.1.1.2) p.1.1.2 (p.1.2.getD i 0))
      encIPGapInput (encList encBool) := by
    refine flatMapWithInput (encA := encUnary) (encB := encBool) (unary_range' hT) ?_
    have p1 : ComputableInPolyTime Prod.fst (encPair encIPGapInput encUnary) encIPGapInput :=
      fst _ _
    exact computableInPolyTime_prodEncRightL (hU3.comp p1) (hq.comp p1)
      (listGetDWithInput (hb.comp p1) (snd _ _) 0)
  have hb4 := replicate (encA := encBool) hT2q4u (const true)
  exact bitsOfList' (listAppend' (listAppend' (listAppend' hb1 hb2) hb3) hb4)

-- Non-vacuity check on `T = 2, q = 2` with matching (`⟨[1, 2], [2, 1]⟩ = 4`) and mismatching
-- (`⟨[1, 2], [2, 2]⟩ = 6 ≠ 4`) pairs.
example :
    boolListInnerProd (ipGapEncodeLeft 2 2 [1, 2] 4) (ipGapEncodeRight 2 2 [2, 1] 4) =
      ipGapThreshold 2 2 ∧
    boolListInnerProd (ipGapEncodeLeft 2 2 [1, 2] 4) (ipGapEncodeRight 2 2 [2, 2] 4) <
      ipGapThreshold 2 2 :=
  ⟨boolListInnerProd_ipGapEncode_eq_of_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    boolListInnerProd_ipGapEncode_lt_of_ne (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

end CslibFrontier.Computability.Complexity
