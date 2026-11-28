/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Logic.Relation

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD

/-!
# Polynomial-Time Accessors, Builders, and Reachability for `DigraphInstance`

This module provides reusable polynomial-time combinators for `Cslib.Complexity.DigraphInstance`
under the standard encoding `Cslib.Complexity.encDigraph`:

## Main definitions

* `Cslib.Complexity.digraphAdjNat`: totalized adjacency-matrix lookup on natural-number indices.
* `Cslib.Complexity.reachStep`, `Cslib.Complexity.reachMatrix`: row-major all-pairs reachability
  (transitive-closure) matrix computed by `G.n` Boolean matrix-multiplication steps.

## Main results

* `Cslib.Complexity.computableInPolyTime_digraph_n`: extracting `G.n` in unary is polynomial time.
* `Cslib.Complexity.computableInPolyTime_digraphAdjNat`: `digraphAdjNat` is polynomial time.
* `Cslib.Complexity.computableInPolyTime_digraphInstance`: building a `DigraphInstance` from a
  unary vertex count and polynomial-time adjacency predicate is polynomial time.
* `Cslib.Complexity.reachMatrix_spec`, `Cslib.Complexity.computableInPolyTime_reachMatrix`:
  exactness and polynomial-time computability of `reachMatrix`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- Extract the vertex count `G.n` of a `DigraphInstance` in unary polynomial time. -/
theorem computableInPolyTime_digraph_n :
    ComputableInPolyTime (fun G : DigraphInstance ↦ G.n) encDigraph encUnary := by
  have hbits : ComputableInPolyTime (fun G : DigraphInstance ↦ encDigraph G) encDigraph encBits :=
    of_eq fun _ ↦ rfl
  have hlist : ComputableInPolyTime (fun G : DigraphInstance ↦ encDigraph G) encDigraph
      (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp hbits
  have htake : ComputableInPolyTime
      (fun G : DigraphInstance ↦ ((encDigraph G).takeWhile fun b ↦ b).length)
      encDigraph encUnary := by
    have htw : ComputableInPolyTime
        (fun G : DigraphInstance ↦ (encDigraph G).takeWhile fun b ↦ b)
        encDigraph (encList encBool) :=
      takeWhileWithInput hlist (snd encDigraph encBool)
    exact (length_list encBool).comp htw
  have heq : (fun G : DigraphInstance ↦ ((encDigraph G).takeWhile fun b ↦ b).length) =
      fun G ↦ G.n := by
    funext G
    simp only [encDigraph_apply, DigraphInstance.encode]
    rw [List.takeWhile_append_of_pos (by intro x hx; simpa using List.eq_of_mem_replicate hx)]
    simp
  rwa [heq] at htake

/-- Read entry `(u, w)` of a `DigraphInstance`'s adjacency matrix (defaulting to `false` out of
bounds). -/
@[expose] def digraphAdjNat (G : DigraphInstance) (u w : ℕ) : Bool :=
  if hu : u < G.n then
    if hw : w < G.n then G.adj ⟨u, hu⟩ ⟨w, hw⟩ else false
  else false

/-- `digraphAdjNat` is computable in polynomial time under `encDigraph` and `encUnary`. -/
theorem computableInPolyTime_digraphAdjNat :
    ComputableInPolyTime (fun p : (DigraphInstance × ℕ) × ℕ ↦ digraphAdjNat p.1.1 p.1.2 p.2)
      (encPair (encPair encDigraph encUnary) encUnary) encBool := by
  have hG : ComputableInPolyTime (fun p : (DigraphInstance × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair encDigraph encUnary) encUnary) encDigraph := by fun_prop
  have hu : ComputableInPolyTime (fun p : (DigraphInstance × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair encDigraph encUnary) encUnary) encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun p : (DigraphInstance × ℕ) × ℕ ↦ p.2)
      (encPair (encPair encDigraph encUnary) encUnary) encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun p : (DigraphInstance × ℕ) × ℕ ↦ p.1.1.n)
      (encPair (encPair encDigraph encUnary) encUnary) encUnary :=
    computableInPolyTime_digraph_n.comp hG
  have hraw : ComputableInPolyTime (fun p : (DigraphInstance × ℕ) × ℕ ↦ encDigraph p.1.1)
      (encPair (encPair encDigraph encUnary) encUnary) encBits :=
    (of_eq (f := encDigraph) (encOut := encBits) fun _ ↦ rfl).comp hG
  have hget : ComputableInPolyTime
      (fun p : (DigraphInstance × ℕ) × ℕ ↦
        if decide (p.1.2 < p.1.1.n) && decide (p.2 < p.1.1.n) then
          (encDigraph p.1.1).getD (p.1.1.n + 1 + (p.1.2 * p.1.1.n + p.2)) false
        else false)
      (encPair (encPair encDigraph encUnary) encUnary) encBool := by
    have hidx : ComputableInPolyTime
        (fun p : (DigraphInstance × ℕ) × ℕ ↦ p.1.1.n + 1 + (p.1.2 * p.1.1.n + p.2))
        (encPair (encPair encDigraph encUnary) encUnary) encUnary := by fun_prop
    have hbit := bitsGetDWithInput hraw hidx false
    have hcond : ComputableInPolyTime
        (fun p : (DigraphInstance × ℕ) × ℕ ↦ decide (p.1.2 < p.1.1.n) && decide (p.2 < p.1.1.n))
        (encPair (encPair encDigraph encUnary) encUnary) encBool := by fun_prop
    exact hcond.ite hbit (const false)
  have heq :
      (fun p : (DigraphInstance × ℕ) × ℕ ↦
        if decide (p.1.2 < p.1.1.n) && decide (p.2 < p.1.1.n) then
          (encDigraph p.1.1).getD (p.1.1.n + 1 + (p.1.2 * p.1.1.n + p.2)) false
        else false) =
      fun p ↦ digraphAdjNat p.1.1 p.1.2 p.2 := by
    funext ⟨⟨G, u⟩, w⟩
    by_cases hu' : u < G.n <;> by_cases hw' : w < G.n
    · simp only [digraphAdjNat, hu', hw', ↓reduceDIte, decide_true, Bool.and_self, ↓reduceIte,
        encDigraph_apply, List.getD_eq_getElem?_getD, G.getElem?_encode_matrix hu' hw']
      rfl
    · simp [digraphAdjNat, hu', hw']
    · simp [digraphAdjNat, hu', hw']
    · simp [digraphAdjNat, hu', hw']
  rwa [heq] at hget

/-- Any `DigraphInstance` whose vertex count (in unary) and adjacency predicate are computable in
polynomial time is computable in polynomial time under `encDigraph`. -/
theorem computableInPolyTime_digraphInstance {α : Type} {encA : α ↪ List Bool}
    {nFn : α → ℕ} {adjFn : α → ℕ → ℕ → Bool}
    (hn : ComputableInPolyTime nFn encA encUnary)
    (hadj : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ adjFn p.1.1 p.1.2 p.2)
      (encPair (encPair encA encUnary) encUnary) encBool) :
    ComputableInPolyTime (fun a ↦ (⟨nFn a, fun u w ↦ adjFn a u.val w.val⟩ : DigraphInstance))
      encA encDigraph := by
  have hmat : ComputableInPolyTime
      (fun a ↦ (List.range (nFn a)).flatMap fun u ↦ (List.range (nFn a)).map (adjFn a u))
      encA encBits :=
    flatMapToBitsWithInput (range.comp hn)
      (mapToBitsWithInput (range.comp (hn.comp (fst _ _))) hadj)
  have hrep : ComputableInPolyTime (fun a ↦ List.replicate (nFn a) true) encA encBits :=
    (bitsReplicate true).comp hn
  have hbits : ComputableInPolyTime
      (fun a ↦ List.replicate (nFn a) true ++
        false :: ((List.range (nFn a)).flatMap fun u ↦ (List.range (nFn a)).map (adjFn a u)))
      encA encBits := by
    fun_prop
  refine hbits.of_enc_eq fun a ↦ ?_
  simp only [encDigraph_apply, DigraphInstance.encode, encBits_apply]
  rw [adjacencyMatrix_eq_flatMap _ (adjFn a) (fun _ _ ↦ rfl)]

/-- One Boolean matrix-multiplication step for transitive closure on `DigraphInstance`. -/
def reachStep (G : DigraphInstance) (mat : List Bool) : List Bool :=
  (List.range G.n).flatMap fun u ↦
    (List.range G.n).map fun w ↦
      mat.getD (u * G.n + w) false ||
      (List.range G.n).any fun z ↦ mat.getD (u * G.n + z) false && digraphAdjNat G z w

/-- `G.n`-step Boolean reachability matrix of `G` (row-major `List Bool` of length `G.n * G.n`). -/
def reachMatrix (G : DigraphInstance) : List Bool :=
  (List.range G.n).foldl (fun mat _ ↦ reachStep G mat)
    ((List.range G.n).flatMap fun u ↦ (List.range G.n).map fun w ↦ u == w)

private def ReachLe (G : DigraphInstance) : ℕ → Fin G.n → Fin G.n → Prop
  | 0, u, w => u = w
  | k + 1, u, w => ReachLe G k u w ∨ ∃ z : Fin G.n, ReachLe G k u z ∧ G.Adj z w

private theorem length_reachStep (G : DigraphInstance) (mat : List Bool) :
    (reachStep G mat).length = G.n * G.n := by
  simp [reachStep, List.length_flatMap]

private theorem getD_flatMap_range_map (n : ℕ) (f : ℕ → ℕ → Bool) {u w : ℕ}
    (hu : u < n) (hw : w < n) :
    ((List.range n).flatMap fun a ↦ (List.range n).map (f a)).getD (u * n + w) false = f u w := by
  have hsplit : List.range n = List.range u ++ u :: (List.range n).drop (u + 1) := by
    have := List.take_append_drop u (List.range n)
    rw [List.take_range, Nat.min_eq_left (le_of_lt hu),
      List.drop_eq_getElem_cons (by simp [hu]), List.getElem_range] at this
    exact this.symm
  have hfm : ((List.range n).flatMap fun a ↦ (List.range n).map (f a)) =
      ((List.range u).flatMap fun a ↦ (List.range n).map (f a)) ++
      ((List.range n).map (f u) ++
        ((List.range n).drop (u + 1)).flatMap fun a ↦ (List.range n).map (f a)) := by
    conv_lhs => arg 2; rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons]
  have hpre : ((List.range u).flatMap fun a ↦ (List.range n).map (f a)).length = u * n := by
    simp [List.length_flatMap]
  rw [hfm, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hpre,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simp [hw])]
  simp [hw]

private theorem reachLe_mono {G : DigraphInstance} {k m : ℕ} (hkm : k ≤ m) {u w : Fin G.n}
    (h : ReachLe G k u w) : ReachLe G m u w := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact Or.inl ih

private theorem reachLe_to_reflTransGen {G : DigraphInstance} {k : ℕ} {u w : Fin G.n}
    (h : ReachLe G k u w) : Relation.ReflTransGen G.Adj u w := by
  induction k generalizing w with
  | zero => exact h ▸ Relation.ReflTransGen.refl
  | succ k ih =>
    rcases h with h | ⟨z, hz, hzw⟩
    · exact ih h
    · exact (ih hz).tail hzw

private theorem reflTransGen_to_exists_reachLe {G : DigraphInstance} {u w : Fin G.n}
    (h : Relation.ReflTransGen G.Adj u w) : ∃ k, ReachLe G k u w := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hzw ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, Or.inr ⟨_, hk, hzw⟩⟩

private theorem reachLe_exists_seq {G : DigraphInstance} {k : ℕ} {u w : Fin G.n}
    (h : ReachLe G k u w) :
    ∃ a : Fin (k + 1) → Fin G.n, a 0 = u ∧ a ⟨k, Nat.lt_succ_self k⟩ = w ∧
      ∀ i : Fin k, a i.castSucc = a i.succ ∨ G.Adj (a i.castSucc) (a i.succ) := by
  induction k generalizing w with
  | zero => exact ⟨fun _ ↦ u, rfl, h, fun i ↦ Fin.elim0 i⟩
  | succ k ih =>
    rcases h with hk | ⟨z, hz, hzw⟩
    · obtain ⟨a, ha0, hak, hstep⟩ := ih hk
      let a' : Fin (k + 2) → Fin G.n := fun i ↦
        if hi : i.val ≤ k then a ⟨i.val, Nat.lt_succ_of_le hi⟩ else w
      refine ⟨a', by simp [a', ha0], by simp [a'], fun i ↦ ?_⟩
      by_cases hi : i.val < k
      · have h1 : a' i.castSucc = a ⟨i.val, Nat.lt_succ_of_le (le_of_lt hi)⟩ := by
          simp [a', le_of_lt hi]
        have h2 : a' i.succ = a ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := by
          simp [a', Nat.succ_le_of_lt hi]
        rw [h1, h2]; exact hstep ⟨i.val, hi⟩
      · have hik : i.val = k := by omega
        have h1 : a' i.castSucc = w := by
          simp only [a', Fin.val_castSucc, hik, le_refl, ↓reduceDIte]; exact hak
        have h2 : a' i.succ = w := by simp [a', hik]
        exact Or.inl (h1.trans h2.symm)
    · obtain ⟨a, ha0, hak, hstep⟩ := ih hz
      let a' : Fin (k + 2) → Fin G.n := fun i ↦
        if hi : i.val ≤ k then a ⟨i.val, Nat.lt_succ_of_le hi⟩ else w
      refine ⟨a', by simp [a', ha0], by simp [a'], fun i ↦ ?_⟩
      by_cases hi : i.val < k
      · have h1 : a' i.castSucc = a ⟨i.val, Nat.lt_succ_of_le (le_of_lt hi)⟩ := by
          simp [a', le_of_lt hi]
        have h2 : a' i.succ = a ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := by
          simp [a', Nat.succ_le_of_lt hi]
        rw [h1, h2]; exact hstep ⟨i.val, hi⟩
      · have hik : i.val = k := by omega
        have h1 : a' i.castSucc = z := by
          simp only [a', Fin.val_castSucc, hik, le_refl, ↓reduceDIte]; exact hak
        have h2 : a' i.succ = w := by simp [a', hik]
        rw [h1, h2]; exact Or.inr hzw

private theorem reachLe_of_seq {G : DigraphInstance} {k : ℕ} (a : Fin (k + 1) → Fin G.n)
    (hstep : ∀ i : Fin k, a i.castSucc = a i.succ ∨ G.Adj (a i.castSucc) (a i.succ)) :
    ReachLe G k (a 0) (a ⟨k, Nat.lt_succ_self k⟩) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev := ih (fun i ↦ a i.castSucc) (fun i ↦ hstep i.castSucc)
    rcases hstep (Fin.last k) with heq | hadj
    · left
      have heq' : a ⟨k, by omega⟩ = a ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := heq
      exact heq' ▸ hprev
    · right; exact ⟨a ⟨k, by omega⟩, hprev, hadj⟩

private theorem reachLe_of_reflTransGen {G : DigraphInstance} {u w : Fin G.n}
    (h : Relation.ReflTransGen G.Adj u w) : ReachLe G G.n u w := by
  classical
  have hex := reflTransGen_to_exists_reachLe h
  let m := Nat.find hex
  have hm : ReachLe G m u w := Nat.find_spec hex
  by_cases hle : m ≤ G.n
  · exact reachLe_mono hle hm
  · exfalso
    obtain ⟨a, ha0, ham, hstep⟩ := reachLe_exists_seq hm
    have hcard : Fintype.card (Fin G.n) < Fintype.card (Fin (m + 1)) := by
      simp; omega
    obtain ⟨i, j, hij, haij⟩ := Fintype.exists_ne_map_eq_of_card_lt a hcard
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm haij.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
    let m' := m - (j.val - i.val)
    have hm'_lt : m' < m := by omega
    let b : Fin (m' + 1) → Fin G.n := fun r ↦
      if r.val ≤ i.val then a ⟨r.val, by omega⟩
      else a ⟨r.val + (j.val - i.val), by omega⟩
    have hb0 : b 0 = u := by simp [b, ha0]
    have hbm' : b ⟨m', Nat.lt_succ_self m'⟩ = w := by
      simp only [b]
      split_ifs with h1
      · have hjlt := j.isLt
        have hilt := i.isLt
        have hjm : j = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (by dsimp [m'] at h1 ⊢; omega)
        have him' : (⟨m', by omega⟩ : Fin (m + 1)) = i := Fin.ext (by dsimp [m'] at h1 ⊢; omega)
        rw [him', haij, hjm, ham]
      · convert ham using 2; ext; dsimp; omega
    have hb_step : ∀ r : Fin m', b r.castSucc = b r.succ ∨ G.Adj (b r.castSucc) (b r.succ) := by
      intro r
      simp only [b, Fin.val_castSucc, Fin.val_succ]
      by_cases hr1 : r.val + 1 ≤ i.val
      · have hr0 : r.val ≤ i.val := by omega
        simp only [hr0, hr1, ↓reduceIte]
        exact hstep ⟨r.val, by omega⟩
      · by_cases hr0 : r.val ≤ i.val
        · have hri : r.val = i.val := by omega
          simp only [hr0, hr1, ↓reduceIte]
          have h1 : (⟨r.val, by omega⟩ : Fin (m + 1)) = i := Fin.ext hri
          have h2 : (⟨r.val + 1 + (j.val - i.val), by omega⟩ : Fin (m + 1)) =
              (⟨j.val, by omega⟩ : Fin m).succ := by ext; dsimp; omega
          have h3 : (⟨j.val, by omega⟩ : Fin m).castSucc = j := by ext; rfl
          rw [h1, haij, h2]
          have hs := hstep ⟨j.val, by omega⟩
          rw [h3] at hs
          exact hs
        · simp only [hr0, hr1, ↓reduceIte]
          have h1 : (⟨r.val + (j.val - i.val), by omega⟩ : Fin (m + 1)) =
              (⟨r.val + (j.val - i.val), by omega⟩ : Fin m).castSucc := by ext; rfl
          have h2 : (⟨r.val + 1 + (j.val - i.val), by omega⟩ : Fin (m + 1)) =
              (⟨r.val + (j.val - i.val), by omega⟩ : Fin m).succ := by ext; dsimp; omega
          rw [h1, h2]
          exact hstep ⟨r.val + (j.val - i.val), by omega⟩
    have hreach' : ReachLe G m' u w := by
      have := reachLe_of_seq b hb_step
      rwa [hb0, hbm'] at this
    exact Nat.find_min hex hm'_lt hreach'

/-- Exact semantic specification of `reachMatrix`. -/
theorem reachMatrix_spec (G : DigraphInstance) (u w : Fin G.n) :
    (reachMatrix G).getD (u.val * G.n + w.val) false = true ↔
      Relation.ReflTransGen G.Adj u w := by
  have hfold : ∀ (k : ℕ) (a b : Fin G.n),
      ((List.range k).foldl (fun mat _ ↦ reachStep G mat)
        ((List.range G.n).flatMap fun i ↦ (List.range G.n).map fun j ↦ i == j)).getD
          (a.val * G.n + b.val) false = true ↔ ReachLe G k a b := by
    intro k
    induction k with
    | zero =>
      intro a b
      rw [List.range_zero, List.foldl_nil, getD_flatMap_range_map G.n _ a.isLt b.isLt]
      simp [ReachLe, Fin.ext_iff]
    | succ k ih =>
      intro a b
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, reachStep,
        getD_flatMap_range_map G.n _ a.isLt b.isLt]
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, ih, ReachLe]
      constructor
      · rintro (h | ⟨z, hz, hz_reach, hz_adj⟩)
        · exact Or.inl h
        · refine Or.inr ⟨⟨z, hz⟩, (ih a ⟨z, hz⟩).1 hz_reach, ?_⟩
          simpa [digraphAdjNat, hz, b.isLt, DigraphInstance.Adj] using hz_adj
      · rintro (h | ⟨z, hz_reach, hz_adj⟩)
        · exact Or.inl h
        · refine Or.inr ⟨z.val, z.isLt, (ih a z).2 hz_reach, ?_⟩
          simpa [digraphAdjNat, z.isLt, b.isLt, DigraphInstance.Adj] using hz_adj
  rw [reachMatrix, hfold G.n u w]
  exact ⟨reachLe_to_reflTransGen, reachLe_of_reflTransGen⟩

/-- `reachMatrix` is computable in polynomial time under `encDigraph`. -/
theorem computableInPolyTime_reachMatrix :
    ComputableInPolyTime reachMatrix encDigraph encBits := by
  have hstep : ComputableInPolyTime
      (fun q : (DigraphInstance × List Bool) × ℕ ↦ reachStep q.1.1 q.1.2)
      (encPair (encPair encDigraph encBits) encUnary) encBits := by
    unfold reachStep
    let encP1 := encPair (encPair (encPair encDigraph encBits) encUnary) encUnary
    let encP2 := encPair encP1 encUnary
    have hinner : ComputableInPolyTime
        (fun p : ((DigraphInstance × List Bool) × ℕ) × ℕ ↦
          p.1.1.2.getD (p.1.2 * p.1.1.1.n + p.2) false ||
          (List.range p.1.1.1.n).any fun z ↦
            p.1.1.2.getD (p.1.2 * p.1.1.1.n + z) false && digraphAdjNat p.1.1.1 z p.2)
        encP1 encBool := by
      have hG : ComputableInPolyTime
          (fun p : ((DigraphInstance × List Bool) × ℕ) × ℕ ↦ p.1.1.1) encP1 encDigraph := by
        fun_prop
      have hmat : ComputableInPolyTime
          (fun p : ((DigraphInstance × List Bool) × ℕ) × ℕ ↦ p.1.1.2) encP1 encBits := by
        fun_prop
      have hn : ComputableInPolyTime
          (fun p : ((DigraphInstance × List Bool) × ℕ) × ℕ ↦ p.1.1.1.n) encP1 encUnary :=
        computableInPolyTime_digraph_n.comp hG
      have hbit1 : ComputableInPolyTime
          (fun p : ((DigraphInstance × List Bool) × ℕ) × ℕ ↦
            p.1.1.2.getD (p.1.2 * p.1.1.1.n + p.2) false) encP1 encBool :=
        bitsGetDWithInput hmat (by fun_prop) false
      have hany : ComputableInPolyTime
          (fun p : ((DigraphInstance × List Bool) × ℕ) × ℕ ↦
            (List.range p.1.1.1.n).any fun z ↦
              p.1.1.2.getD (p.1.2 * p.1.1.1.n + z) false &&
                digraphAdjNat p.1.1.1 z p.2) encP1 encBool := by
        refine anyWithInput (range.comp hn) ?_
        have hG' : ComputableInPolyTime (fun q : (((DigraphInstance × List Bool) × ℕ) × ℕ) × ℕ ↦
            q.1.1.1.1) encP2 encDigraph := by fun_prop
        have hn' : ComputableInPolyTime (fun q : (((DigraphInstance × List Bool) × ℕ) × ℕ) × ℕ ↦
            q.1.1.1.1.n) encP2 encUnary := computableInPolyTime_digraph_n.comp hG'
        have hmat' : ComputableInPolyTime
            (fun q : (((DigraphInstance × List Bool) × ℕ) × ℕ) × ℕ ↦ q.1.1.1.2) encP2 encBits := by
          fun_prop
        have hb : ComputableInPolyTime (fun q : (((DigraphInstance × List Bool) × ℕ) × ℕ) × ℕ ↦
            q.1.1.1.2.getD (q.1.1.2 * q.1.1.1.1.n + q.2) false) encP2 encBool :=
          bitsGetDWithInput hmat' (by fun_prop) false
        have hadj : ComputableInPolyTime (fun q : (((DigraphInstance × List Bool) × ℕ) × ℕ) × ℕ ↦
            digraphAdjNat q.1.1.1.1 q.2 q.1.2) encP2 encBool :=
          computableInPolyTime_digraphAdjNat.comp
            (by fun_prop : ComputableInPolyTime
              (fun q : (((DigraphInstance × List Bool) × ℕ) × ℕ) × ℕ ↦ ((q.1.1.1.1, q.2), q.1.2))
              encP2 (encPair (encPair encDigraph encUnary) encUnary))
        exact hb.bool_and' hadj
      exact hbit1.bool_or' hany
    have hn1 : ComputableInPolyTime (fun q : (DigraphInstance × List Bool) × ℕ ↦ q.1.1.n)
        (encPair (encPair encDigraph encBits) encUnary) encUnary :=
      computableInPolyTime_digraph_n.comp (by fun_prop)
    have hrow : ComputableInPolyTime
        (fun q : (DigraphInstance × List Bool) × ℕ ↦
          (List.range q.1.1.n).map fun w ↦
            q.1.2.getD (q.2 * q.1.1.n + w) false ||
            (List.range q.1.1.n).any fun z ↦
              q.1.2.getD (q.2 * q.1.1.n + z) false && digraphAdjNat q.1.1 z w)
        (encPair (encPair encDigraph encBits) encUnary) encBits :=
      mapToBitsWithInput (range.comp hn1) hinner
    have hn0 : ComputableInPolyTime (fun q : DigraphInstance × List Bool ↦ q.1.n)
        (encPair encDigraph encBits) encUnary :=
      computableInPolyTime_digraph_n.comp (fst _ _)
    have hflat := flatMapToBitsWithInput
      (f := fun (q : DigraphInstance × List Bool) (u : ℕ) ↦
        (List.range q.1.n).map fun w ↦
          q.2.getD (u * q.1.n + w) false ||
          (List.range q.1.n).any fun z ↦
            q.2.getD (u * q.1.n + z) false && digraphAdjNat q.1 z w)
      (range.comp hn0) hrow
    exact hflat.comp (fst _ _)
  have hinit : ComputableInPolyTime
      (fun G : DigraphInstance ↦
        (List.range G.n).flatMap fun u ↦ (List.range G.n).map fun w ↦ u == w)
      encDigraph encBits := by
    have hrow : ComputableInPolyTime
        (fun p : DigraphInstance × ℕ ↦ (List.range p.1.n).map fun w ↦ p.2 == w)
        (encPair encDigraph encUnary) encBits :=
      mapToBitsWithInput (range.comp (computableInPolyTime_digraph_n.comp (fst _ _)))
        (unary_beq' ((snd _ _).comp (fst _ _)) (snd _ _))
    exact flatMapToBitsWithInput (range.comp computableInPolyTime_digraph_n) hrow
  have hB : PolyBounded (fun G : DigraphInstance ↦ (encDigraph G).length) (fun G ↦ G.n * G.n) := by
    have h := (unary_mul.comp
      (computableInPolyTime_digraph_n.prod computableInPolyTime_digraph_n)).polyBounded_length
    simpa only [encUnary_apply, List.length_replicate, Function.comp_def] using h
  refine foldlWith (encA := encUnary) (encL := encList encUnary) (par := id)
    (step := fun (G : DigraphInstance) (mat : List Bool) (_ : ℕ) ↦ reachStep G mat)
    id' (range.comp computableInPolyTime_digraph_n) hinit hstep hB ?_
  intro G i _
  have hlen : ∀ (k : ℕ),
      ((List.range k).foldl (fun mat _ ↦ reachStep G mat)
        ((List.range G.n).flatMap fun u ↦ (List.range G.n).map fun w ↦ u == w)).length =
      G.n * G.n := by
    intro k; induction k with
    | zero => simp [List.length_flatMap]
    | succ k _ =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact length_reachStep G _
  simp only [encBits_apply, List.take_range, id]
  rw [hlen]

end Cslib.Complexity
