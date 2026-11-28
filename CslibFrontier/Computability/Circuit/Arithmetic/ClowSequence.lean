/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Clows, Clow Sequences, and Cycle-Cover Determinant Expansion

This module defines closed walks with minimum-vertex heads (clows), clow sequences, and cycle
covers on `Fin n`, proving edge-multiset invariance under rotation and loop splicing and showing
that the signed weight sum over cycle-cover clow sequences equals `M.det`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Clow`: a nonempty walk `head :: tail` with `head < v` for all
  `v ∈ tail`.
* `CslibFrontier.Computability.Circuit.ClowSeq`: a sequence of clows with strictly increasing heads
  and total length `n`.
* `CslibFrontier.Computability.Circuit.ClowSeq.IsCycleCover`: nodup vertex cover condition.

## Main results

* `CslibFrontier.Computability.Circuit.cycleEdges_splice_perm`,
  `CslibFrontier.Computability.Circuit.cycleEdges_rotateTo_perm`.
* `CslibFrontier.Computability.Circuit.sum_cycleCover_eq_det`: cycle-cover clow sequences compute
  `M.det` via bijection with `Equiv.Perm (Fin n)`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open scoped Matrix

/-! ### Clows, Clow Sequences, and Cycle Covers -/

section Clows

/-- A closed walk (clow) on `Fin n`: nonempty list `head :: tail` with `head < v` for all
`v ∈ tail`. -/
@[ext]
public structure Clow (n : ℕ) where
  /-- Minimum-index starting vertex (head) of the clow. -/
  head : Fin n
  /-- Remaining vertices along the closed walk, each strictly greater than `head`. -/
  tail : List (Fin n)
  lt_tail : ∀ v ∈ tail, head < v
deriving DecidableEq

/-- Vertex list `head :: tail` of a clow. -/
@[expose]
public def Clow.verts {n : ℕ} (c : Clow n) : List (Fin n) := c.head :: c.tail

@[simp]
public theorem Clow.verts_mk {n : ℕ} (h : Fin n) (t : List (Fin n)) (hlt : ∀ v ∈ t, h < v) :
    (Clow.mk h t hlt).verts = h :: t := rfl

/-- Decomposition `c.verts = c.head :: c.tail` of the vertex list of a clow. -/
public theorem Clow.verts_eq_cons {n : ℕ} (c : Clow n) : c.verts = c.head :: c.tail := rfl

/-- Length `tail.length + 1` of a clow. -/
@[expose]
public def Clow.len {n : ℕ} (c : Clow n) : ℕ := c.tail.length + 1

@[simp]
public theorem Clow.len_mk {n : ℕ} (h : Fin n) (t : List (Fin n)) (hlt : ∀ v ∈ t, h < v) :
    (Clow.mk h t hlt).len = t.length + 1 := rfl

/-- Characterization `c.len = c.tail.length + 1`. -/
public theorem Clow.len_eq_length_tail_add_one {n : ℕ} (c : Clow n) :
    c.len = c.tail.length + 1 := rfl

/-- Every clow has positive length `0 < c.len`. -/
public theorem Clow.pos_len {n : ℕ} (c : Clow n) : 0 < c.len := Nat.succ_pos _

/-- Directed cycle edges of a list obtained by zipping with a one-step rotation. -/
@[expose]
public def cycleEdges {α : Type*} (l : List α) : List (α × α) :=
  l.zip (l.rotate 1)

/-- Directed edges of a clow around its closed walk. -/
@[expose]
public def Clow.edges {n : ℕ} (c : Clow n) : List (Fin n × Fin n) :=
  cycleEdges c.verts

/-- Characterization `c.edges = cycleEdges c.verts`. -/
public theorem Clow.edges_eq_cycleEdges_verts {n : ℕ} (c : Clow n) :
    c.edges = cycleEdges c.verts := rfl

/-- Product of matrix entries along the edges of a clow. -/
@[expose]
public noncomputable def Clow.weight {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (c : Clow n) : R :=
  (c.edges.map fun p => M p.1 p.2).prod

/-- Characterization of `c.weight M` as the product of edge entries along `c.edges`. -/
public theorem Clow.weight_eq_prod_edges {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (c : Clow n) :
    c.weight M = (c.edges.map fun p => M p.1 p.2).prod := rfl

/-- A clow sequence of total length `n`: strictly increasing heads, total length `n`. -/
@[ext]
public structure ClowSeq (n : ℕ) where
  /-- Ordered list of clows with strictly increasing heads and total length `n`. -/
  clows : List (Clow n)
  heads_strict : clows.Pairwise (fun c₁ c₂ => c₁.head < c₂.head)
  len_sum : (clows.map Clow.len).sum = n
deriving DecidableEq

/-- Signed weight `(-1)^(n + clows.length) * ∏ w.weight M` of a clow sequence. -/
@[expose]
public noncomputable def ClowSeq.signedWeight {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (w : ClowSeq n) : R :=
  (-1 : R) ^ (n + w.clows.length) * (w.clows.map (Clow.weight M)).prod

/-- Characterization of `w.signedWeight M` in terms of `w.clows.length` and `Clow.weight`. -/
public theorem ClowSeq.signedWeight_eq {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (w : ClowSeq n) :
    w.signedWeight M = (-1 : R) ^ (n + w.clows.length) * (w.clows.map (Clow.weight M)).prod := rfl

/-- A clow sequence is a cycle cover when its concatenated vertex list has no duplicates. -/
@[expose]
public def ClowSeq.IsCycleCover {n : ℕ} (w : ClowSeq n) : Prop :=
  (w.clows.flatMap Clow.verts).Nodup

public instance {n : ℕ} (w : ClowSeq n) : Decidable w.IsCycleCover :=
  inferInstanceAs (Decidable (w.clows.flatMap Clow.verts).Nodup)

/-- The type of clow sequences of length `n` is finite. -/
public theorem clowSeq_finite (n : ℕ) : Finite (ClowSeq n) := by
  have hinj : Function.Injective (fun w : ClowSeq n =>
      (w.clows.flatMap fun c => c.verts.map fun v => (c.head, v))) := by
    intro w₁ w₂ h
    suffices w₁.clows = w₂.clows by cases w₁; cases w₂; simp_all
    have hrec : ∀ (l₁ l₂ : List (Clow n)),
        l₁.Pairwise (fun c₁ c₂ => c₁.head < c₂.head) →
        l₂.Pairwise (fun c₁ c₂ => c₁.head < c₂.head) →
        (l₁.flatMap fun c => c.verts.map fun v => (c.head, v)) =
        (l₂.flatMap fun c => c.verts.map fun v => (c.head, v)) →
        l₁ = l₂ := by
      intro l₁ l₂ hp₁ hp₂ heq
      induction l₁ generalizing l₂ with
      | nil =>
        cases l₂ with
        | nil => rfl
        | cons c₂ cs₂ => simp [Clow.verts] at heq
      | cons c₁ cs₁ ih =>
        cases l₂ with
        | nil => simp [Clow.verts] at heq
        | cons c₂ cs₂ =>
          simp only [List.flatMap_cons, Clow.verts, List.map_cons, List.cons_append] at heq
          have hhead : c₁.head = c₂.head := congrArg Prod.fst (List.cons.inj heq).1
          have htail_eq := (List.cons.inj heq).2
          have hsplit : ∀ (P : (Fin n × Fin n) → Prop) (a₁ b₁ a₂ b₂ : List (Fin n × Fin n)),
              (∀ x ∈ a₁, P x) → (∀ x ∈ a₂, P x) →
              (∀ x ∈ b₁, ¬ P x) → (∀ x ∈ b₂, ¬ P x) →
              a₁ ++ b₁ = a₂ ++ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
            intro P a₁ b₁ a₂ b₂ ha₁ ha₂ hb₁ hb₂ h
            induction a₁ generalizing a₂ with
            | nil =>
              cases a₂ with
              | nil => exact ⟨rfl, h⟩
              | cons x xs =>
                simp only [List.nil_append, List.cons_append] at h
                exact absurd (ha₂ x List.mem_cons_self) (hb₁ x (h ▸ List.mem_cons_self))
            | cons x xs ih' =>
              cases a₂ with
              | nil =>
                simp only [List.nil_append, List.cons_append] at h
                exact absurd (ha₁ x List.mem_cons_self) (hb₂ x (h ▸ List.mem_cons_self))
              | cons y ys =>
                simp only [List.cons_append] at h
                obtain ⟨rfl, h'⟩ := List.cons.inj h
                obtain ⟨hxs, hbs⟩ := ih' ys (fun z hz => ha₁ z (List.mem_cons_of_mem _ hz))
                  (fun z hz => ha₂ z (List.mem_cons_of_mem _ hz)) h'
                exact ⟨congrArg _ hxs, hbs⟩
          have ⟨hm, hrest⟩ :
              (c₁.tail.map fun v => (c₁.head, v)) = (c₂.tail.map fun v => (c₂.head, v)) ∧
              (cs₁.flatMap fun c => (c.head, c.head) :: c.tail.map fun v => (c.head, v)) =
              (cs₂.flatMap fun c => (c.head, c.head) :: c.tail.map fun v => (c.head, v)) := by
            refine hsplit (fun p : Fin n × Fin n => p.1 = c₁.head) _ _ _ _ ?_ ?_ ?_ ?_ htail_eq
            · intro p hp; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp; rfl
            · intro p hp; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp; exact hhead.symm
            · intro p hp
              obtain ⟨c, hc, hp'⟩ := List.mem_flatMap.mp hp
              rcases List.mem_cons.mp hp' with rfl | hp''
              · exact ne_of_gt ((List.pairwise_cons.mp hp₁).1 c hc)
              · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp''
                exact ne_of_gt ((List.pairwise_cons.mp hp₁).1 c hc)
            · intro p hp
              obtain ⟨c, hc, hp'⟩ := List.mem_flatMap.mp hp
              rcases List.mem_cons.mp hp' with rfl | hp''
              · exact ne_of_gt (hhead ▸ (List.pairwise_cons.mp hp₂).1 c hc)
              · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp''
                exact ne_of_gt (hhead ▸ (List.pairwise_cons.mp hp₂).1 c hc)
          have htail : c₁.tail = c₂.tail := by
            have := congrArg (List.map Prod.snd) hm
            simpa [List.map_map] using this
          have hc : c₁ = c₂ := Clow.ext hhead htail
          have hrest' : cs₁.flatMap (fun c => c.verts.map fun v => (c.head, v)) =
              cs₂.flatMap (fun c => c.verts.map fun v => (c.head, v)) := hrest
          rw [hc, ih cs₂ (List.pairwise_cons.mp hp₁).2 (List.pairwise_cons.mp hp₂).2 hrest']
    exact hrec w₁.clows w₂.clows w₁.heads_strict w₂.heads_strict h
  have hlen : ∀ w : ClowSeq n,
      (w.clows.flatMap fun c => c.verts.map fun v => (c.head, v)).length = n := by
    intro w
    rw [List.length_flatMap]
    exact (congrArg List.sum (List.map_congr_left fun c _ => by
      simp [Clow.verts, Clow.len])).trans w.len_sum
  let embed : ClowSeq n → (Fin n → Fin n × Fin n) := fun w i =>
    (w.clows.flatMap fun c => c.verts.map fun v => (c.head, v)).get (i.cast (hlen w).symm)
  have hemb : Function.Injective embed := fun w₁ w₂ h => hinj <|
    List.ext_getElem ((hlen w₁).trans (hlen w₂).symm) fun i h1 _ => by
      simpa [embed] using congrFun h ⟨i, (hlen w₁) ▸ h1⟩
  exact Finite.of_injective embed hemb

/-! ### Edge Multiset Identities for Rotation and Splicing -/

/-- Successive edge pairs `(x, y₁), (y₁, y₂), ...` along a walk starting at `x`. -/
@[expose]
public def pairChain {α : Type*} : α → List α → List (α × α)
  | _, [] => []
  | x, y :: ys => (x, y) :: pairChain y ys

@[simp]
public theorem pairChain_nil {α : Type*} (x : α) : pairChain x [] = [] := rfl

@[simp]
public theorem pairChain_cons {α : Type*} (x y : α) (ys : List α) :
    pairChain x (y :: ys) = (x, y) :: pairChain y ys := rfl

public theorem pairChain_append {α : Type*} (x : α) (a : List α) (y : α) (b : List α) :
    pairChain x (a ++ y :: b) = pairChain x (a ++ [y]) ++ pairChain y b := by
  induction a generalizing x with
  | nil => simp
  | cons u us ih => simp [ih]

public theorem cycleEdges_cons_eq_pairChain {α : Type*} (x : α) (ys : List α) :
    cycleEdges (x :: ys) = pairChain x (ys ++ [x]) := by
  simp only [cycleEdges, List.rotate_cons_succ, List.rotate_zero]
  suffices ∀ (u : α) (vs : List α), (u :: vs).zip (vs ++ [x]) = pairChain u (vs ++ [x]) from
    this x ys
  intro u vs
  induction vs generalizing u with
  | nil => simp
  | cons v vs ih => simp [ih]

private theorem cycleEdges_rotate {α : Type*} (l : List α) (k : ℕ) :
    cycleEdges (l.rotate k) = (cycleEdges l).rotate k := by
  simp only [cycleEdges]
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.getElem_zip, List.getElem_rotate, List.length_zip, List.length_rotate, min_self]
  congr 1; congr 1
  rw [Nat.mod_add_mod, Nat.mod_add_mod, add_right_comm]

public theorem cycleEdges_splice_perm {α : Type*} (x v : α) (a rest b : List α) :
    (cycleEdges ((x :: a) ++ (v :: rest) ++ (v :: b))).Perm
      (cycleEdges ((x :: a) ++ (v :: b)) ++ cycleEdges (v :: rest)) := by
  have h1 : (x :: a) ++ (v :: rest) ++ (v :: b) = x :: (a ++ v :: (rest ++ v :: b)) := by
    simp [List.append_assoc]
  have h2 : (x :: a) ++ (v :: b) = x :: (a ++ v :: b) := by simp
  rw [h1, h2, cycleEdges_cons_eq_pairChain, cycleEdges_cons_eq_pairChain,
    cycleEdges_cons_eq_pairChain]
  have ha : a ++ v :: (rest ++ v :: b) ++ [x] = a ++ v :: (rest ++ v :: (b ++ [x])) := by
    simp [List.append_assoc]
  have hb : a ++ v :: b ++ [x] = a ++ v :: (b ++ [x]) := by simp [List.append_assoc]
  rw [ha, hb, pairChain_append x a v (rest ++ v :: (b ++ [x])),
    pairChain_append v rest v (b ++ [x]), pairChain_append x a v (b ++ [x])]
  have hc : pairChain x (a ++ [v]) ++ (pairChain v (rest ++ [v]) ++ pairChain v (b ++ [x])) =
      (pairChain x (a ++ [v]) ++ pairChain v (rest ++ [v])) ++ pairChain v (b ++ [x]) := by
    simp [List.append_assoc]
  rw [hc]
  have hp1 : ((pairChain x (a ++ [v]) ++ pairChain v (rest ++ [v])) ++ pairChain v (b ++ [x])).Perm
      ((pairChain v (rest ++ [v]) ++ pairChain x (a ++ [v])) ++ pairChain v (b ++ [x])) :=
    List.Perm.append_right _ List.perm_append_comm
  have hp2 : (pairChain v (rest ++ [v]) ++ (pairChain x (a ++ [v]) ++ pairChain v (b ++ [x]))).Perm
      ((pairChain x (a ++ [v]) ++ pairChain v (b ++ [x])) ++ pairChain v (rest ++ [v])) :=
    List.perm_append_comm
  exact hp1.trans (by simpa [List.append_assoc] using hp2)

/-- Rotate a list so that its first occurrence of `a` moves to the front. -/
@[expose]
public def rotateTo {α : Type*} [DecidableEq α] (l : List α) (x : α) : List α :=
  l.rotate (l.idxOf x)

@[simp]
public theorem rotateTo_cons_self {α : Type*} [DecidableEq α] (x : α) (xs : List α) :
    rotateTo (x :: xs) x = x :: xs := by
  simp [rotateTo]

public theorem rotateTo_perm {α : Type*} [DecidableEq α] (l : List α) (x : α) :
    (rotateTo l x).Perm l := List.rotate_perm l (l.idxOf x)

public theorem rotateTo_head {α : Type*} [DecidableEq α] {l : List α} {x : α} (hx : x ∈ l) :
    ∃ rest, rotateTo l x = x :: rest := by
  have hidx : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  have hne : rotateTo l x ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [rotateTo, List.length_rotate, List.length_nil] at hl
    rw [hl] at hidx; exact Nat.not_lt_zero _ hidx
  cases h : rotateTo l x with
  | nil => exact absurd h hne
  | cons y rest =>
    refine ⟨rest, ?_⟩
    have h0 : (rotateTo l x)[0]'(by rw [h]; simp) = y := by simp [h]
    have h1 : (rotateTo l x)[0]'(by simp [rotateTo]; omega) = x := by
      simp only [rotateTo, List.getElem_rotate, zero_add, Nat.mod_eq_of_lt hidx]
      exact List.getElem_idxOf hidx
    rw [h0.symm.trans h1]

public theorem rotateTo_rotateTo {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {x y : α} (_hx : x ∈ l) (hy : y ∈ l) :
    rotateTo (rotateTo l x) y = rotateTo l y := by
  have hr1 : ∃ k₁, rotateTo (rotateTo l x) y = l.rotate k₁ :=
    ⟨l.idxOf x + (rotateTo l x).idxOf y, List.rotate_rotate l _ _⟩
  have hr2 : rotateTo l y = l.rotate (l.idxOf y) := rfl
  obtain ⟨k₁, hk₁⟩ := hr1
  have hy1 : y ∈ rotateTo l x := (rotateTo_perm l x).mem_iff.mpr hy
  obtain ⟨r₁, hr₁⟩ := rotateTo_head hy1
  obtain ⟨r₂, hr₂⟩ := rotateTo_head hy
  have hlen : l.length ≠ 0 := by intro h; simp [List.eq_nil_of_length_eq_zero h] at hy
  have hhead_get : ∀ {xs : List α} {r : List α}, xs = y :: r →
      (hpos : 0 < xs.length) → xs[0]'hpos = y := by rintro _ _ rfl _; rfl
  have hk1_mod : (l.rotate k₁)[0]'(by simp; omega) = y :=
    hhead_get (hk₁.symm.trans hr₁) _
  have hk2_mod : (l.rotate (l.idxOf y))[0]'(by simp; omega) = y :=
    hhead_get (hr2.symm.trans hr₂) _
  simp only [List.getElem_rotate, zero_add] at hk1_mod hk2_mod
  have heq_idx : k₁ % l.length = l.idxOf y % l.length := by
    have hnod := (List.nodup_iff_injective_getElem).mp hnd
    exact congrArg Fin.val (hnod (a₁ := ⟨k₁ % l.length, Nat.mod_lt _ (by omega)⟩)
      (a₂ := ⟨l.idxOf y % l.length, Nat.mod_lt _ (by omega)⟩) (hk1_mod.trans hk2_mod.symm))
  rw [hk₁, hr2, ← List.rotate_mod l k₁, ← List.rotate_mod l (l.idxOf y), heq_idx]

public theorem cycleEdges_rotateTo_perm {α : Type*} [DecidableEq α] (l : List α) (x : α) :
    (cycleEdges (rotateTo l x)).Perm (cycleEdges l) := by
  rw [rotateTo, cycleEdges_rotate]; exact List.rotate_perm _ _

/-! ### Cycle-Cover Clow Sequences and `Equiv.Perm (Fin n)` -/

private def singleCyclePerm {n : ℕ} (c : Clow n) : Equiv.Perm (Fin n) :=
  (c.tail.map (Equiv.swap c.head)).reverse.prod

private theorem singleCyclePerm_sign {n : ℕ} (c : Clow n) (hc : c.verts.Nodup) :
    (Equiv.Perm.sign (singleCyclePerm c) : ℤ) = (-1 : ℤ) ^ c.tail.length := by
  have hhead : c.head ∉ c.tail := (List.nodup_cons.mp hc).1
  have hgo : ∀ (vs : List (Fin n)), c.head ∉ vs →
      (Equiv.Perm.sign ((vs.map (Equiv.swap c.head)).reverse.prod) : ℤ) = (-1 : ℤ) ^ vs.length := by
    intro vs hvs
    induction vs using List.reverseRecOn with
    | nil => simp
    | append_singleton ys y ih =>
      simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.prod_cons, map_mul, Units.val_mul,
        List.length_append, List.length_singleton]
      have hy : c.head ≠ y := fun h => hvs (by simp [h])
      have hys : c.head ∉ ys := fun h => hvs (List.mem_append_left _ h)
      rw [Equiv.Perm.sign_swap hy, ih hys]
      simp [pow_succ, mul_comm]
  exact hgo c.tail hhead

private theorem singleCyclePerm_apply {n : ℕ} (c : Clow n) (hc : c.verts.Nodup) :
    (∀ p ∈ c.edges, singleCyclePerm c p.1 = p.2) ∧
    (∀ x : Fin n, x ∉ c.verts → singleCyclePerm c x = x) := by
  have hhead : c.head ∉ c.tail := (List.nodup_cons.mp hc).1
  have htail_nd : c.tail.Nodup := (List.nodup_cons.mp hc).2
  suffices hgo : ∀ (vs : List (Fin n)), c.head ∉ vs → vs.Nodup →
      (∀ p ∈ pairChain c.head (vs ++ [c.head]),
        ((vs.map (Equiv.swap c.head)).reverse.prod) p.1 = p.2) ∧
      (∀ x : Fin n, x ∉ c.head :: vs →
        ((vs.map (Equiv.swap c.head)).reverse.prod) x = x) by
    simpa only [Clow.edges, Clow.verts, cycleEdges_cons_eq_pairChain, singleCyclePerm] using
      hgo c.tail hhead htail_nd
  intro vs hvs hnd
  induction vs using List.reverseRecOn with
  | nil => simp [pairChain]
  | append_singleton ys y ih =>
    have hys_head : c.head ∉ ys := fun h => hvs (List.mem_append_left _ h)
    have hy_head : y ≠ c.head := fun h => hvs (by simp [h])
    have hnd' : ys.Nodup ∧ y ∉ ys := by
      have := List.nodup_append.mp hnd
      exact ⟨this.1, fun hy => this.2.2 y hy y List.mem_cons_self rfl⟩
    obtain ⟨ih_edges, ih_fix⟩ := ih hys_head hnd'.1
    have hprod : (((ys ++ [y]).map (Equiv.swap c.head)).reverse.prod) =
        Equiv.swap c.head y * (ys.map (Equiv.swap c.head)).reverse.prod := by
      simp [List.map_append, List.reverse_append]
    rw [hprod]
    constructor
    · intro p hp
      have hchain : pairChain c.head ((ys ++ [y]) ++ [c.head]) =
          pairChain c.head (ys ++ [y]) ++ [(y, c.head)] := by
        rw [List.append_assoc, List.singleton_append, pairChain_append]; rfl
      rw [hchain, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · have hlast_or : (p ∈ pairChain c.head (ys ++ [c.head]) ∧ p.2 ≠ c.head) ∨
            (p.2 = y ∧ (p.1, c.head) ∈ pairChain c.head (ys ++ [c.head])) := by
          have hgen : ∀ (u : Fin n) (as : List (Fin n)), c.head ∉ as →
              ∀ q ∈ pairChain u (as ++ [y]),
                (q ∈ pairChain u (as ++ [c.head]) ∧ q.2 ≠ c.head) ∨
                (q.2 = y ∧ (q.1, c.head) ∈ pairChain u (as ++ [c.head])) := by
            intro u as hcas q hq
            induction as generalizing u with
            | nil =>
              simp only [List.nil_append, pairChain, List.mem_singleton] at hq ⊢
              right
              exact ⟨congrArg Prod.snd hq, congrArg (fun z => (z, c.head)) (congrArg Prod.fst hq)⟩
            | cons a as' ih' =>
              simp only [List.cons_append, pairChain, List.mem_cons] at hq ⊢
              rcases hq with rfl | hq
              · left; exact ⟨Or.inl rfl, fun heq => hcas (heq ▸ List.mem_cons_self)⟩
              · rcases ih' a (fun h => hcas (List.mem_cons_of_mem _ h)) hq with
                  ⟨h1, h2⟩ | ⟨h1, h2⟩
                · left; exact ⟨Or.inr h1, h2⟩
                · right; exact ⟨h1, Or.inr h2⟩
          exact hgen c.head ys hys_head p hp
        rcases hlast_or with ⟨hp', hne⟩ | ⟨rfl, hp'⟩
        · simp only [Equiv.Perm.mul_apply, ih_edges p hp']
          have hp2_in : p.2 ∈ ys := by
            have hmem : ∀ (u : Fin n) (as : List (Fin n)) (q : Fin n × Fin n),
                q ∈ pairChain u as → q.2 ∈ as := by
              intro u as q hq
              induction as generalizing u with
              | nil => simp [pairChain] at hq
              | cons a as' ih' =>
                simp only [pairChain, List.mem_cons] at hq ⊢
                rcases hq with rfl | hq
                · exact Or.inl rfl
                · exact Or.inr (ih' a hq)
            have := hmem c.head (ys ++ [c.head]) p hp'
            simp only [List.mem_append, List.mem_singleton] at this
            exact this.resolve_right hne
          exact Equiv.swap_apply_of_ne_of_ne (fun h => hys_head (h ▸ hp2_in))
            (fun h => hnd'.2 (h ▸ hp2_in))
        · simp only [Equiv.Perm.mul_apply, ih_edges (p.1, c.head) hp', Equiv.swap_apply_left]
      · simp only [Equiv.Perm.mul_apply, ih_fix y (by simp [hy_head, hnd'.2]),
          Equiv.swap_apply_right]
    · intro x hx
      have hx_ys : x ∉ c.head :: ys := fun h => hx (by simp at h ⊢; tauto)
      have hx_head : x ≠ c.head := fun h => hx (by simp [h])
      have hx_y : x ≠ y := fun h => hx (by simp [h])
      simp only [Equiv.Perm.mul_apply, ih_fix x hx_ys, Equiv.swap_apply_of_ne_of_ne hx_head hx_y]

private def clowListPerm {n : ℕ} : List (Clow n) → Equiv.Perm (Fin n)
  | [] => 1
  | c :: cs => singleCyclePerm c * clowListPerm cs

private theorem clowListPerm_sign {n : ℕ} (cs : List (Clow n))
    (hnd : (cs.flatMap Clow.verts).Nodup) :
    (Equiv.Perm.sign (clowListPerm cs) : ℤ) =
      (-1 : ℤ) ^ ((cs.map Clow.len).sum + cs.length) := by
  induction cs with
  | nil => simp [clowListPerm]
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    simp only [clowListPerm, map_mul, Units.val_mul, singleCyclePerm_sign c hnd.1, ih hnd.2.1,
      List.map_cons, List.sum_cons, List.length_cons, Clow.len]
    rw [← pow_add]
    have hpar : (c.tail.length + ((cs.map Clow.len).sum + cs.length)) % 2 =
        (c.tail.length + 1 + (cs.map Clow.len).sum + (cs.length + 1)) % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one
        (c.tail.length + ((cs.map Clow.len).sum + cs.length)) with ha | ha
    · have hb : (c.tail.length + 1 + (cs.map Clow.len).sum + (cs.length + 1)) % 2 = 0 := hpar ▸ ha
      rw [Even.neg_one_pow (Nat.even_iff.mpr ha), Even.neg_one_pow (Nat.even_iff.mpr hb)]
    · have hb : (c.tail.length + 1 + (cs.map Clow.len).sum + (cs.length + 1)) % 2 = 1 := hpar ▸ ha
      rw [Odd.neg_one_pow (Nat.odd_iff.mpr ha), Odd.neg_one_pow (Nat.odd_iff.mpr hb)]

private theorem clowListPerm_apply {n : ℕ} (cs : List (Clow n))
    (hnd : (cs.flatMap Clow.verts).Nodup) :
    (∀ c ∈ cs, ∀ p ∈ c.edges, clowListPerm cs p.1 = p.2) ∧
    (∀ x : Fin n, x ∉ cs.flatMap Clow.verts → clowListPerm cs x = x) := by
  induction cs with
  | nil => simp [clowListPerm]
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨ih_e, ih_f⟩ := ih hnd.2.1
    have hdisj : ∀ x ∈ c.verts, x ∉ cs.flatMap Clow.verts := fun x hx hm => hnd.2.2 x hx x hm rfl
    constructor
    · intro c' hc' p hp
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · have hp1_in : p.1 ∈ c'.verts := (List.of_mem_zip hp).1
        simp only [clowListPerm, Equiv.Perm.mul_apply, ih_f p.1 (hdisj p.1 hp1_in)]
        exact (singleCyclePerm_apply c' hnd.1).1 p hp
      · have hp2_in : p.2 ∈ c'.verts :=
          (List.rotate_perm c'.verts 1).subset (List.of_mem_zip hp).2
        have hp2_not_c : p.2 ∉ c.verts :=
          fun h => hdisj p.2 h (List.mem_flatMap.mpr ⟨c', hc', hp2_in⟩)
        simp only [clowListPerm, Equiv.Perm.mul_apply, ih_e c' hc' p hp]
        exact (singleCyclePerm_apply c hnd.1).2 p.2 hp2_not_c
    · intro x hx
      simp only [List.flatMap_cons, List.mem_append, not_or] at hx
      simp only [clowListPerm, Equiv.Perm.mul_apply, ih_f x hx.2]
      exact (singleCyclePerm_apply c hnd.1).2 x hx.1

private def permOrbitMin {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) : Fin n :=
  (Finset.univ.image (fun k : Fin n => (σ ^ k.1) x)).min'
    ⟨x, Finset.mem_image.mpr ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) x.2⟩, Finset.mem_univ _, by simp⟩⟩

private theorem permOrbitMin_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) (k : ℕ) :
    permOrbitMin σ x ≤ (σ ^ k) x := by
  have hclosed : ∀ y ∈ Finset.univ.image (fun j : Fin n => (σ ^ j.1) x),
      σ y ∈ Finset.univ.image (fun j : Fin n => (σ ^ j.1) x) := by
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    by_cases hj : j.1 + 1 < n
    · exact Finset.mem_image.mpr ⟨⟨j.1 + 1, hj⟩, Finset.mem_univ _, by
        rw [pow_succ', Equiv.Perm.mul_apply]⟩
    · have hne : ∃ a b : Fin (n + 1), a < b ∧ (σ ^ a.1) x = (σ ^ b.1) x := by
        by_contra h; push Not at h
        have hinj : Function.Injective (fun a : Fin (n + 1) => (σ ^ a.1) x) := by
          intro a b hab
          rcases lt_trichotomy a b with hlt | rfl | hgt
          · exact absurd hab (h a b hlt)
          · rfl
          · exact absurd hab.symm (h b a hgt)
        have := Fintype.card_le_of_injective _ hinj; simp at this
      obtain ⟨a, b, hab, hpow⟩ := hne
      have hperiod : (σ ^ (b.1 - a.1)) x = x := by
        have hba : a.1 + (b.1 - a.1) = b.1 := by have : a.1 < b.1 := hab; omega
        rw [← hba, pow_add, Equiv.Perm.mul_apply] at hpow
        exact (σ ^ a.1).injective hpow.symm
      have hd_pos : 0 < b.1 - a.1 := by have : a.1 < b.1 := hab; omega
      have hd_le : b.1 - a.1 ≤ n := by have := b.2; omega
      have hj_eq : j.1 + 1 = n := by have := j.2; omega
      have hpow_n : (σ ^ (j.1 + 1)) x = (σ ^ (n - (b.1 - a.1))) x := by
        rw [hj_eq]
        have hsplit_n : n = (n - (b.1 - a.1)) + (b.1 - a.1) := by omega
        have h1 : (σ ^ n) x = (σ ^ ((n - (b.1 - a.1)) + (b.1 - a.1))) x :=
          congrArg (fun k => (σ ^ k) x) hsplit_n
        rw [h1, pow_add, Equiv.Perm.mul_apply, hperiod]
      refine Finset.mem_image.mpr ⟨⟨n - (b.1 - a.1), by omega⟩, Finset.mem_univ _, ?_⟩
      rw [← hpow_n, pow_succ', Equiv.Perm.mul_apply]
  have hmem : ∀ m : ℕ, (σ ^ m) x ∈ Finset.univ.image (fun j : Fin n => (σ ^ j.1) x) := fun m => by
    induction m with
    | zero =>
      refine Finset.mem_image.mpr
        ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) x.2⟩, Finset.mem_univ _, by simp⟩
    | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hclosed _ ih
  exact Finset.min'_le _ _ (hmem k)

private theorem permOrbitMin_mem_orbit {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    ∃ k : ℕ, (σ ^ k) x = permOrbitMin σ x := by
  have hmem := Finset.min'_mem (Finset.univ.image (fun j : Fin n => (σ ^ j.1) x))
    ⟨x, Finset.mem_image.mpr ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) x.2⟩, Finset.mem_univ _, by simp⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
  exact ⟨j.1, hj⟩

private theorem permOrbitMin_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    permOrbitMin σ (σ x) = permOrbitMin σ x := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := permOrbitMin_mem_orbit σ x
    have hpos : 0 < orderOf σ := orderOf_pos σ
    have hpow : (σ ^ (k + (orderOf σ - 1))) (σ x) = (σ ^ k) x := by
      have hadd : k + (orderOf σ - 1) + 1 = k + orderOf σ := by omega
      have : (σ ^ (k + (orderOf σ - 1))) (σ x) = (σ ^ (k + orderOf σ)) x := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ, hadd]
      rw [this, pow_add, Equiv.Perm.mul_apply, pow_orderOf_eq_one, Equiv.Perm.one_apply]
    rw [← hk, ← hpow]; exact permOrbitMin_le σ (σ x) _
  · obtain ⟨k, hk⟩ := permOrbitMin_mem_orbit σ (σ x)
    rw [← hk, ← Equiv.Perm.mul_apply, ← pow_succ]; exact permOrbitMin_le σ x (k + 1)

private theorem permOrbitMin_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) (k : ℕ) :
    permOrbitMin σ ((σ ^ k) x) = permOrbitMin σ x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, permOrbitMin_apply, ih]

private noncomputable def permPeriod {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) : ℕ :=
  Nat.find (⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; rfl⟩ :
    ∃ k, 0 < k ∧ (σ ^ k) x = x)

private theorem permPeriod_pos {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    0 < permPeriod σ x := (Nat.find_spec (⟨orderOf σ, orderOf_pos σ, by simp⟩ :
    ∃ k, 0 < k ∧ (σ ^ k) x = x)).1

private theorem permPeriod_spec {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    (σ ^ permPeriod σ x) x = x := (Nat.find_spec (⟨orderOf σ, orderOf_pos σ, by simp⟩ :
    ∃ k, 0 < k ∧ (σ ^ k) x = x)).2

private theorem permPeriod_min {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) {k : ℕ}
    (hk0 : 0 < k) (hk : k < permPeriod σ x) : (σ ^ k) x ≠ x := fun h =>
  Nat.find_min (⟨orderOf σ, orderOf_pos σ, by simp⟩ : ∃ k, 0 < k ∧ (σ ^ k) x = x) hk ⟨hk0, h⟩

private noncomputable def orbitClow {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : Fin n)
    (hh : permOrbitMin σ h = h) : Clow n where
  head := h
  tail := (List.range (permPeriod σ h - 1)).map fun i => (σ ^ (i + 1)) h
  lt_tail := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hi
    have hle : h ≤ (σ ^ (i + 1)) h := by
      conv_lhs => rw [← hh]
      exact permOrbitMin_le σ h (i + 1)
    have hp := permPeriod_pos σ h
    exact lt_of_le_of_ne hle (permPeriod_min σ h (by omega) (by omega)).symm

private theorem orbitClow_edges {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : Fin n)
    (hh : permOrbitMin σ h = h) :
    ∀ p ∈ (orbitClow σ h hh).edges, p.2 = σ p.1 := by
  intro p hp
  simp only [Clow.edges, Clow.verts, orbitClow, cycleEdges_cons_eq_pairChain] at hp
  have hp_pos := permPeriod_pos σ h
  have hchain : ∀ (m : ℕ), m ≤ permPeriod σ h - 1 →
      ∀ q ∈ pairChain h (((List.range m).map fun i => (σ ^ (i + 1)) h) ++ [(σ ^ (m + 1)) h]),
        q.2 = σ q.1 := by
    intro m
    induction m with
    | zero =>
      intro _ q hq
      simp only [List.range_zero, List.map_nil, List.nil_append, pairChain,
        List.mem_singleton] at hq
      rw [hq]; simp
    | succ m ih =>
      intro hm q hq
      rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
        List.singleton_append, pairChain_append] at hq
      rw [List.mem_append] at hq
      rcases hq with hq | hq
      · exact ih (by omega) q hq
      · simp only [pairChain, List.mem_singleton] at hq
        rw [hq]; simp [pow_succ', Equiv.Perm.mul_apply]
  have hspec : (σ ^ ((permPeriod σ h - 1) + 1)) h = h := by
    rw [show permPeriod σ h - 1 + 1 = permPeriod σ h by omega]; exact permPeriod_spec σ h
  have hp' : p ∈ pairChain h (((List.range (permPeriod σ h - 1)).map fun i => (σ ^ (i + 1)) h) ++
      [(σ ^ ((permPeriod σ h - 1) + 1)) h]) := by rwa [hspec]
  exact hchain (permPeriod σ h - 1) le_rfl p hp'

private noncomputable def ofPermClows {n : ℕ} (σ : Equiv.Perm (Fin n)) : List (Clow n) :=
  ((List.finRange n).filter (fun h => decide (permOrbitMin σ h = h))).attach.map fun ⟨h, hh⟩ =>
    orbitClow σ h (of_decide_eq_true (List.mem_filter.mp hh).2)

private theorem ofPermClows_nodup {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((ofPermClows σ).flatMap Clow.verts).Nodup := by
  let heads := (List.finRange n).filter (fun h => decide (permOrbitMin σ h = h))
  have hheads_pw : heads.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨⟨h, hh⟩, _, rfl⟩ := List.mem_map.mp hc
    simp only [orbitClow, Clow.verts, List.nodup_cons, List.mem_map, List.mem_range, not_exists,
      not_and]
    have hp := permPeriod_pos σ h
    refine ⟨fun i hi hEq => permPeriod_min σ h (by omega) (by omega) hEq, ?_⟩
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exfalso
      have hdiff : (σ ^ (j - i)) h = h := by
        have h1 : (σ ^ (i + 1)) ((σ ^ (j - i)) h) = (σ ^ (i + 1)) h := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, show i + 1 + (j - i) = j + 1 by omega]
          exact hij.symm
        exact (σ ^ (i + 1)).injective h1
      exact permPeriod_min σ h (by omega) (by omega) hdiff
    · rfl
    · exfalso
      have hdiff : (σ ^ (i - j)) h = h := by
        have h1 : (σ ^ (j + 1)) ((σ ^ (i - j)) h) = (σ ^ (j + 1)) h := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, show j + 1 + (i - j) = i + 1 by omega]
          exact hij
        exact (σ ^ (j + 1)).injective h1
      exact permPeriod_min σ h (by omega) (by omega) hdiff
  · have hpw_att : heads.attach.Pairwise (fun a b => a.1 < b.1) :=
      (List.pairwise_map (f := Subtype.val) (R := (· < ·))).mp (by simpa using hheads_pw)
    refine List.pairwise_map.mpr (hpw_att.imp fun {a b} hab x hx₁ hx₂ => ?_)
    have hmin1 : permOrbitMin σ x = a.1 := by
      simp only [orbitClow, Clow.verts, List.mem_cons, List.mem_map] at hx₁
      rcases hx₁ with rfl | ⟨i, _, rfl⟩
      · exact of_decide_eq_true (List.mem_filter.mp a.2).2
      · rw [permOrbitMin_pow]; exact of_decide_eq_true (List.mem_filter.mp a.2).2
    have hmin2 : permOrbitMin σ x = b.1 := by
      simp only [orbitClow, Clow.verts, List.mem_cons, List.mem_map] at hx₂
      rcases hx₂ with rfl | ⟨i, _, rfl⟩
      · exact of_decide_eq_true (List.mem_filter.mp b.2).2
      · rw [permOrbitMin_pow]; exact of_decide_eq_true (List.mem_filter.mp b.2).2
    exact ne_of_lt hab (hmin1.symm.trans hmin2)

private theorem mem_ofPermClows_verts {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ (ofPermClows σ).flatMap Clow.verts := by
  let h := permOrbitMin σ x
  have hh : permOrbitMin σ h = h := by
    obtain ⟨k, hk⟩ := permOrbitMin_mem_orbit σ x
    dsimp only [h]; rw [← hk, permOrbitMin_pow, hk]
  have hh_mem : h ∈ (List.finRange n).filter (fun h => decide (permOrbitMin σ h = h)) :=
    List.mem_filter.mpr ⟨List.mem_finRange h, decide_eq_true hh⟩
  refine List.mem_flatMap.mpr ⟨orbitClow σ h hh,
    List.mem_map.mpr ⟨⟨h, hh_mem⟩, List.mem_attach _ _, rfl⟩, ?_⟩
  obtain ⟨k, hk⟩ := permOrbitMin_mem_orbit σ x
  have hpos := orderOf_pos σ
  let t := (k * orderOf σ - k) % permPeriod σ h
  have ht_lt : t < permPeriod σ h := Nat.mod_lt _ (permPeriod_pos σ h)
  have hpow_t : (σ ^ t) h = x := by
    have h1 : (σ ^ (k * orderOf σ - k)) h = x := by
      dsimp only [h]
      rw [← hk, ← Equiv.Perm.mul_apply, ← pow_add]
      have hadd : k * orderOf σ - k + k = k * orderOf σ := by
        have : k ≤ k * orderOf σ := Nat.le_mul_of_pos_right k hpos; omega
      rw [hadd, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]
    have hdiv : ∀ m : ℕ, (σ ^ (m % permPeriod σ h)) h = (σ ^ m) h := fun m => by
      have hstep : ∀ q r : ℕ, (σ ^ (q * permPeriod σ h + r)) h = (σ ^ r) h := fun q r => by
        induction q with
        | zero => simp
        | succ q ih =>
          rw [show (q + 1) * permPeriod σ h + r = (q * permPeriod σ h + r) + permPeriod σ h by
                ring,
            pow_add, Equiv.Perm.mul_apply, permPeriod_spec, ih]
      conv_rhs => rw [← Nat.div_add_mod m (permPeriod σ h), mul_comm]
      exact (hstep (m / permPeriod σ h) (m % permPeriod σ h)).symm
    rw [hdiv, h1]
  simp only [orbitClow, Clow.verts, List.mem_cons, List.mem_map, List.mem_range]
  by_cases ht0 : t = 0
  · left; rw [← hpow_t, ht0]; simp
  · right; exact ⟨t - 1, by omega, by rwa [show t - 1 + 1 = t by omega]⟩

private noncomputable def ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : ClowSeq n where
  clows := ofPermClows σ
  heads_strict := by
    let heads := (List.finRange n).filter (fun h => decide (permOrbitMin σ h = h))
    have hheads_pw : heads.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
    have hmap : (ofPermClows σ).map Clow.head = heads := by
      simp only [ofPermClows, List.map_map]
      apply List.ext_getElem (by simp [heads])
      intro i _ _; simp [orbitClow, heads]
    exact (List.pairwise_map (f := Clow.head) (R := (· < ·))).mp (hmap ▸ hheads_pw)
  len_sum := by
    have h1 : ((ofPermClows σ).flatMap Clow.verts).length = ((ofPermClows σ).map Clow.len).sum := by
      rw [List.length_flatMap]; rfl
    rw [← h1]
    have hperm : ((ofPermClows σ).flatMap Clow.verts).Perm (List.finRange n) :=
      (List.perm_ext_iff_of_nodup (ofPermClows_nodup σ) (List.nodup_finRange n)).mpr fun x => by
        simp [mem_ofPermClows_verts σ x]
    simpa using hperm.length_eq

private theorem clowListPerm_ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    clowListPerm (ofPerm σ).clows = σ := by
  ext x
  have hmem := mem_ofPermClows_verts σ x
  obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp hmem
  have hedge : ∃ p ∈ c.edges, p.1 = x := by
    have hzip : c.verts = c.edges.map Prod.fst :=
      (List.map_fst_zip (by simp)).symm
    rw [hzip] at hxc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxc
    exact ⟨p, hp, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hedge
  rw [(clowListPerm_apply (ofPerm σ).clows (ofPermClows_nodup σ)).1 c hc p hp]
  simp only [ofPermClows, List.mem_map] at hc
  obtain ⟨⟨h, hh⟩, _, rfl⟩ := hc
  exact congrArg Fin.val (orbitClow_edges σ h (of_decide_eq_true (List.mem_filter.mp hh).2) p hp)

private theorem ofPerm_clowListPerm {n : ℕ} {w : ClowSeq n} (hw : w.IsCycleCover) :
    ofPerm (clowListPerm w.clows) = w := by
  let σ := clowListPerm w.clows
  have hmem_all : ∀ x : Fin n, x ∈ w.clows.flatMap Clow.verts := by
    have hlen : (w.clows.flatMap Clow.verts).length = n := by
      rw [List.length_flatMap]
      exact (congrArg List.sum (List.map_congr_left fun c _ => by
        simp [Clow.verts, Clow.len])).trans w.len_sum
    have hperm : (w.clows.flatMap Clow.verts).Perm (List.finRange n) := by
      -- A nodup list of `Fin n` of length `n` contains every `x : Fin n`.
      have hcard : (w.clows.flatMap Clow.verts).toFinset.card = Fintype.card (Fin n) := by
        rw [List.toFinset_card_of_nodup hw, hlen, Fintype.card_fin]
      have huniv : (w.clows.flatMap Clow.verts).toFinset = Finset.univ :=
        Finset.eq_univ_of_card _ hcard
      refine (List.perm_ext_iff_of_nodup hw (List.nodup_finRange n)).mpr fun x => ?_
      simp only [List.mem_finRange, iff_true]
      exact List.mem_toFinset.mp (huniv ▸ Finset.mem_univ x)
    intro x; exact hperm.mem_iff.mpr (List.mem_finRange x)
  -- For any `c ∈ w.clows`, `σ` maps `c.verts` cyclically, so `c = orbitClow σ c.head _`.
  have hpow_c : ∀ c ∈ w.clows, ∀ i : ℕ, (hi : i < c.verts.length) →
      (σ ^ i) c.head = c.verts[i] := by
    intro c hc i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      have hmem_e : (c.verts[i]'(by omega), c.verts[i + 1]'hi) ∈ c.edges := by
        simp only [Clow.edges, cycleEdges]
        have hlen_e : (c.verts.zip (c.verts.rotate 1)).length = c.verts.length := by simp
        refine List.mem_iff_getElem.mpr ⟨i, by omega, ?_⟩
        simp [List.getElem_zip, List.getElem_rotate, Nat.mod_eq_of_lt hi]
      exact (clowListPerm_apply w.clows hw).1 c hc _ hmem_e
  have hper_c : ∀ c ∈ w.clows, permPeriod σ c.head = c.verts.length := by
    intro c hc
    have hnd_c : c.verts.Nodup := (List.nodup_flatMap.mp hw).1 c hc
    have hret : (σ ^ c.verts.length) c.head = c.head := by
      have hlen_pos : 0 < c.verts.length := by simp [Clow.verts]
      rw [show c.verts.length = (c.verts.length - 1) + 1 by omega, pow_succ',
        Equiv.Perm.mul_apply, hpow_c c hc (c.verts.length - 1) (by omega)]
      have hmem_e : (c.verts[c.verts.length - 1]'(by omega), c.head) ∈ c.edges := by
        simp only [Clow.edges, cycleEdges]
        refine List.mem_iff_getElem.mpr ⟨c.verts.length - 1, by simp; omega, ?_⟩
        simp only [List.getElem_zip, List.getElem_rotate]
        exact Prod.ext rfl (by simp [Clow.verts])
      exact (clowListPerm_apply w.clows hw).1 c hc _ hmem_e
    have hle : permPeriod σ c.head ≤ c.verts.length :=
      Nat.find_min' _ ⟨by simp [Clow.verts], hret⟩
    have hge : c.verts.length ≤ permPeriod σ c.head := by
      by_contra hlt; push Not at hlt
      have hpos := permPeriod_pos σ c.head
      have heq := (hpow_c c hc (permPeriod σ c.head) hlt).symm.trans (permPeriod_spec σ c.head)
      have h0 : c.verts[0]'(by simp [Clow.verts]) = c.head := rfl
      have hnod := List.nodup_iff_injective_getElem.mp hnd_c
      have hidx := congrArg Fin.val (hnod (a₁ := ⟨permPeriod σ c.head, hlt⟩)
        (a₂ := ⟨0, by simp [Clow.verts]⟩) (heq.trans h0.symm))
      simp only at hidx; omega
    exact le_antisymm hle hge
  have hmin_c : ∀ c ∈ w.clows, permOrbitMin σ c.head = c.head := by
    intro c hc
    apply le_antisymm (permOrbitMin_le σ c.head 0)
    obtain ⟨k, hk⟩ := permOrbitMin_mem_orbit σ c.head
    rw [← hk]
    have hdiv : ∀ m : ℕ, (σ ^ m) c.head = (σ ^ (m % c.verts.length)) c.head := fun m => by
      have hret : (σ ^ c.verts.length) c.head = c.head := by
        rw [← hper_c c hc]; exact permPeriod_spec σ c.head
      have hstep : ∀ q r : ℕ, (σ ^ (q * c.verts.length + r)) c.head = (σ ^ r) c.head :=
          fun q r => by
        induction q with
        | zero => simp
        | succ q ih =>
          rw [show (q + 1) * c.verts.length + r = (q * c.verts.length + r) + c.verts.length by
                ring,
            pow_add, Equiv.Perm.mul_apply, hret, ih]
      conv_lhs => rw [← Nat.div_add_mod m c.verts.length, mul_comm]
      exact hstep _ _
    rw [hdiv k, hpow_c c hc (k % c.verts.length) (Nat.mod_lt _ (by simp [Clow.verts]))]
    have hmem_v : c.verts[k % c.verts.length]'(Nat.mod_lt _ (by simp [Clow.verts])) ∈ c.verts :=
      List.getElem_mem _
    simp only [Clow.verts, List.mem_cons] at hmem_v
    rcases hmem_v with h | h
    · exact le_of_eq h.symm
    · exact le_of_lt (c.lt_tail _ h)
  have hheads_eq : (ofPerm σ).clows.map Clow.head = w.clows.map Clow.head := by
    have h1 : (ofPerm σ).clows.map Clow.head =
        (List.finRange n).filter (fun h => decide (permOrbitMin σ h = h)) := by
      simp only [ofPerm, ofPermClows, List.map_map]
      apply List.ext_getElem (by simp)
      intro i _ _; simp [orbitClow]
    rw [h1]
    have hpw1 : ((List.finRange n).filter
        (fun h => decide (permOrbitMin σ h = h))).Pairwise (· < ·) :=
      (List.pairwise_lt_finRange n).filter _
    have hpw2 : (w.clows.map Clow.head).Pairwise (· < ·) :=
      (List.pairwise_map (f := Clow.head) (R := (· < ·))).mpr w.heads_strict
    have hperm : ((List.finRange n).filter (fun h => decide (permOrbitMin σ h = h))).Perm
        (w.clows.map Clow.head) := by
      refine (List.perm_ext_iff_of_nodup hpw1.nodup hpw2.nodup).mpr fun h => ?_
      simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_map]
      constructor
      · intro hh
        obtain ⟨c, hc, hhc⟩ := List.mem_flatMap.mp (hmem_all h)
        have hmin_h : permOrbitMin σ h = c.head := by
          obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hhc
          rw [← hget, ← hpow_c c hc i hi, permOrbitMin_pow, hmin_c c hc]
        exact ⟨c, hc, hmin_h.symm.trans hh⟩
      · rintro ⟨c, hc, rfl⟩; exact hmin_c c hc
    have hsort : ∀ (l₁ l₂ : List (Fin n)), l₁.Perm l₂ → l₁.Pairwise (· < ·) →
        l₂.Pairwise (· < ·) → l₁ = l₂ := by
      intro l₁; induction l₁ with
      | nil => intro l₂ hp _ _; exact hp.nil_eq
      | cons a as ih =>
        intro l₂ hp h1' h2'
        cases l₂ with
        | nil => exact absurd hp.symm.nil_eq (by simp)
        | cons b bs =>
          have ha_mem : a ∈ b :: bs := hp.mem_iff.mp List.mem_cons_self
          have hb_mem : b ∈ a :: as := hp.symm.mem_iff.mp List.mem_cons_self
          have hab : a ≤ b := by
            rcases List.mem_cons.mp hb_mem with rfl | hb'
            · exact le_rfl
            · exact le_of_lt ((List.pairwise_cons.mp h1').1 b hb')
          have hba : b ≤ a := by
            rcases List.mem_cons.mp ha_mem with rfl | ha'
            · exact le_rfl
            · exact le_of_lt ((List.pairwise_cons.mp h2').1 a ha')
          have heq : a = b := le_antisymm hab hba
          subst heq
          exact congrArg (a :: ·) (ih bs (hp.cons_inv) (List.pairwise_cons.mp h1').2
            (List.pairwise_cons.mp h2').2)
    exact hsort _ _ hperm hpw1 hpw2
  suffices hcl : (ofPerm σ).clows = w.clows by
    cases w
    dsimp only [ofPerm, σ] at hcl ⊢
    simp [hcl]
  have hlen_eq : (ofPerm σ).clows.length = w.clows.length := by
    have := congrArg List.length hheads_eq; simpa using this
  apply List.ext_getElem hlen_eq
  intro i hi1 hi2
  have hhead_i : ((ofPerm σ).clows[i]'hi1).head = (w.clows[i]'hi2).head := by
    have h := List.getElem_of_eq hheads_eq (i := i) (by simp [hi1])
    simpa using h
  have hc_mem : w.clows[i]'hi2 ∈ w.clows := List.getElem_mem hi2
  have h1 : (ofPerm σ).clows[i]'hi1 = orbitClow σ (w.clows[i]'hi2).head (hmin_c _ hc_mem) := by
    have hmem_i : (ofPerm σ).clows[i]'hi1 ∈ (ofPerm σ).clows := List.getElem_mem hi1
    simp only [ofPerm, ofPermClows, List.mem_map] at hmem_i
    obtain ⟨⟨h', hh'⟩, _, heq⟩ := hmem_i
    have hhh : h' = (w.clows[i]'hi2).head := by
      have := congrArg Clow.head heq; exact this.trans hhead_i
    subst hhh
    exact heq.symm
  rw [h1]
  apply Clow.ext
  · rfl
  · change ((List.range (permPeriod σ (w.clows[i]'hi2).head - 1)).map fun j =>
        (σ ^ (j + 1)) (w.clows[i]'hi2).head) = (w.clows[i]'hi2).tail
    have hper' : permPeriod σ (w.clows[i]'hi2).head = (w.clows[i]'hi2).tail.length + 1 :=
      hper_c _ hc_mem
    apply List.ext_getElem (by simp [hper'])
    intro j hj1 hj2
    simp only [List.getElem_map, List.getElem_range]
    rw [hpow_c _ hc_mem (j + 1) (by simp [Clow.verts]; omega)]
    rfl

/-- The sum of signed weights over cycle-cover clow sequences equals `M.det`. -/
public theorem sum_cycleCover_eq_det {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    let _ : Fintype (ClowSeq n) := @Fintype.ofFinite _ (clowSeq_finite n)
    ∑ w ∈ Finset.univ.filter (fun w : ClowSeq n => w.IsCycleCover), w.signedWeight M = M.det := by
  let _ : Fintype (ClowSeq n) := @Fintype.ofFinite _ (clowSeq_finite n)
  rw [← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_bij (fun w _ => clowListPerm w.clows) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro w₁ hw₁ w₂ hw₂ heq
    have h1 := (Finset.mem_filter.mp hw₁).2
    have h2 := (Finset.mem_filter.mp hw₂).2
    rw [← ofPerm_clowListPerm h1, ← ofPerm_clowListPerm h2, heq]
  · intro σ _
    exact ⟨ofPerm σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ofPermClows_nodup σ⟩,
      clowListPerm_ofPerm σ⟩
  · intro w hw
    have hnd : w.IsCycleCover := (Finset.mem_filter.mp hw).2
    simp only [ClowSeq.signedWeight, Matrix.transpose_apply]
    congr 1
    · have hs := clowListPerm_sign w.clows hnd
      rw [w.len_sum] at hs
      have hcast : ((Equiv.Perm.sign (clowListPerm w.clows) : ℤ) : R) =
          ((-1 : ℤ) ^ (n + w.clows.length) : ℤ) := congrArg Int.cast hs
      simpa using hcast.symm
    · let σ := clowListPerm w.clows
      have hflat : (w.clows.map (Clow.weight M)).prod =
          ((w.clows.flatMap Clow.edges).map fun p => M p.1 p.2).prod := by
        induction w.clows with
        | nil => simp
        | cons c cs ih =>
          simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
            List.prod_append, ih, Clow.weight]
      rw [hflat]
      have hmap_edges : (w.clows.flatMap Clow.edges).map (fun p => M p.1 p.2) =
          (w.clows.flatMap Clow.verts).map (fun i => M i (σ i)) := by
        have hgen : ∀ cs : List (Clow n), (∀ c ∈ cs, ∀ p ∈ c.edges, σ p.1 = p.2) →
            (cs.flatMap Clow.edges).map (fun p => M p.1 p.2) =
            (cs.flatMap Clow.verts).map (fun i => M i (σ i)) := by
          intro cs hcs
          induction cs with
          | nil => rfl
          | cons c cs ih =>
            simp only [List.flatMap_cons, List.map_append]
            rw [ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))]
            congr 1
            have hzip : c.verts = c.edges.map Prod.fst := (List.map_fst_zip (by simp)).symm
            conv_rhs => rw [hzip, List.map_map]
            refine List.map_congr_left fun p hp => ?_
            simp [Function.comp_apply, hcs c List.mem_cons_self p hp]
        exact hgen w.clows (clowListPerm_apply w.clows hnd).1
      rw [hmap_edges]
      have hlen : (w.clows.flatMap Clow.verts).length = n := by
        rw [List.length_flatMap]
        exact (congrArg List.sum (List.map_congr_left fun c _ => by
          simp [Clow.verts, Clow.len])).trans w.len_sum
      have hperm : (w.clows.flatMap Clow.verts).Perm (List.finRange n) := by
        have hcard : (w.clows.flatMap Clow.verts).toFinset.card = Fintype.card (Fin n) := by
          rw [List.toFinset_card_of_nodup hnd, hlen, Fintype.card_fin]
        have huniv := Finset.eq_univ_of_card _ hcard
        exact (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange n)).mpr fun x => by
          simp [List.mem_toFinset.mp (huniv ▸ Finset.mem_univ x)]
      rw [(hperm.map (fun i => M i (σ i))).prod_eq]
      rw [← List.prod_ofFn]
      congr 1
      apply List.ext_getElem (by simp)
      intro i _ _; simp [σ]


end Clows

end CslibFrontier.Computability.Circuit
