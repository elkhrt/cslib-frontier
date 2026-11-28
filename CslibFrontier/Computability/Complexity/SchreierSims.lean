/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import CslibFrontier.Algorithms.Perm.SchreierSims

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Complexity of the Schreier–Sims Algorithm

This module certifies native multi-tape Turing-machine polynomial-time computability
(`Turing.MultiTapeTM.ComputableInPolyTime`) for the deterministic Schreier–Sims permutation group
order algorithm defined in `CslibFrontier.Algorithms.Perm.SchreierSims`.

## Main definitions

* `CslibFrontier.Computability.Complexity.SchreierSims.encTable`: framed list encoding of an
  `n × n` sift table.

## Main results

* `CslibFrontier.Computability.Complexity.SchreierSims.computableInPolyTime_siftOne`:
  single-element sifting into a permutation sift table is computable in native polynomial time.
* `CslibFrontier.Computability.Complexity.SchreierSims.computableInPolyTime_schreierSimsOrder`:
  computing the order of a permutation group given by generators on `Fin n` is computable in native
  polynomial time.
-/

public section

namespace CslibFrontier.Computability.Complexity.SchreierSims

open Turing.MultiTapeTM CslibFrontier.Algorithms.Perm.SchreierSims

/-! ### 5. Native Polynomial-Time Computability Certificate -/

/-- Encoding of an `n × n` sift table as a framed list of framed lists of framed lists of unary
naturals. -/
abbrev encTable : List (List (List ℕ)) ↪ List Bool :=
  encList (encList (encList encUnary))

private theorem listGetDComputed {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {l : γ → List α} {idx : γ → ℕ} {fallback : γ → α}
    (hl : ComputableInPolyTime l encIn (encList encA))
    (hidx : ComputableInPolyTime idx encIn encUnary)
    (hfb : ComputableInPolyTime fallback encIn encA) :
    ComputableInPolyTime (fun x => (l x).getD (idx x) (fallback x)) encIn encA := by
  simp_rw [List.getD_eq_getElem?_getD]
  fun_prop

private theorem map_fst_zipIdx {α : Type*} (l : List α) (k : ℕ) :
    (l.zipIdx k).map Prod.fst = l := by
  induction l generalizing k with
  | nil => rfl
  | cons _ _ ih => simp [List.zipIdx_cons, ih]

private theorem listSet_poly {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {l : γ → List α} {idx : γ → ℕ} {val : γ → α}
    (hl : ComputableInPolyTime l encIn (encList encA))
    (hidx : ComputableInPolyTime idx encIn encUnary)
    (hval : ComputableInPolyTime val encIn encA) :
    ComputableInPolyTime (fun x => listSet (l x) (idx x) (val x)) encIn (encList encA) := by
  change ComputableInPolyTime
    (fun x => (l x).zipIdx.map (fun p => if p.2 == idx x then val x else p.1)) _ _
  apply ComputableInPolyTime.mapWithInput ((ComputableInPolyTime.zipIdx encA).comp hl)
  have hpar := ComputableInPolyTime.fst encIn (encPair encA encUnary)
  have hcur := ComputableInPolyTime.snd encIn (encPair encA encUnary)
  exact ComputableInPolyTime.ite'
    (ComputableInPolyTime.beq (hcur.snd') (hidx.comp hpar))
    (hval.comp hpar) (hcur.fst')

private theorem isPermList_poly :
    ComputableInPolyTime (fun p : ℕ × List ℕ => isPermList p.1 p.2)
      (encPair encUnary (encList encUnary)) encBool := by
  change ComputableInPolyTime (fun p : ℕ × List ℕ =>
    (p.2.length == p.1) &&
      (List.range p.1).all (fun i => decide (p.2.getD i p.1 < p.1)) &&
      (List.range p.1).all (fun j => (List.range p.1).any (fun i => p.2.getD i p.1 == j))) _ _
  have hn := ComputableInPolyTime.fst encUnary (encList encUnary)
  have hp := ComputableInPolyTime.snd encUnary (encList encUnary)
  have h1 : ComputableInPolyTime (fun x : ℕ × List ℕ => x.2.length == x.1)
      (encPair encUnary (encList encUnary)) encBool :=
    ComputableInPolyTime.beq ((ComputableInPolyTime.length encUnary).comp hp) hn
  have h2 : ComputableInPolyTime (fun x : ℕ × List ℕ =>
      (List.range x.1).all (fun i => decide (x.2.getD i x.1 < x.1)))
      (encPair encUnary (encList encUnary)) encBool := by
    apply ComputableInPolyTime.allWithInput (ComputableInPolyTime.range.comp hn)
    have hpar := ComputableInPolyTime.fst (encPair encUnary (encList encUnary)) encUnary
    have hi := ComputableInPolyTime.snd (encPair encUnary (encList encUnary)) encUnary
    exact ComputableInPolyTime.unary_lt'
      (listGetDComputed (hp.comp hpar) hi (hn.comp hpar))
      (hn.comp hpar)
  have h3 : ComputableInPolyTime (fun x : ℕ × List ℕ =>
      (List.range x.1).all (fun j => (List.range x.1).any (fun i => x.2.getD i x.1 == j)))
      (encPair encUnary (encList encUnary)) encBool := by
    apply ComputableInPolyTime.allWithInput (ComputableInPolyTime.range.comp hn)
    have hpar := ComputableInPolyTime.fst (encPair encUnary (encList encUnary)) encUnary
    have hj := ComputableInPolyTime.snd (encPair encUnary (encList encUnary)) encUnary
    apply ComputableInPolyTime.anyWithInput (ComputableInPolyTime.range.comp (hn.comp hpar))
    have hpar2 := ComputableInPolyTime.fst (encPair (encPair encUnary (encList encUnary)) encUnary)
      encUnary
    have hi := ComputableInPolyTime.snd (encPair (encPair encUnary (encList encUnary)) encUnary)
      encUnary
    exact ComputableInPolyTime.beq
      (listGetDComputed (hp.comp (hpar.comp hpar2)) hi (hn.comp (hpar.comp hpar2)))
      (hj.comp hpar2)
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' h1 h2) h3

private theorem permMul_poly :
    ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ => permMul x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair (encList encUnary) (encList encUnary))) (encList encUnary) := by
  change ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ =>
    (List.range x.1).map (fun i => x.2.1.getD (x.2.2.getD i x.1) x.1)) _ _
  have hn := ComputableInPolyTime.fst encUnary (encPair (encList encUnary) (encList encUnary))
  have hpq := ComputableInPolyTime.snd encUnary (encPair (encList encUnary) (encList encUnary))
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have hpar := ComputableInPolyTime.fst
    (encPair encUnary (encPair (encList encUnary) (encList encUnary))) encUnary
  have hi := ComputableInPolyTime.snd
    (encPair encUnary (encPair (encList encUnary) (encList encUnary))) encUnary
  have hq_i := listGetDComputed (hpq.snd'.comp hpar) hi (hn.comp hpar)
  exact listGetDComputed (hpq.fst'.comp hpar) hq_i (hn.comp hpar)

private theorem permInv_poly :
    ComputableInPolyTime (fun x : ℕ × List ℕ => permInv x.1 x.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  change ComputableInPolyTime (fun x : ℕ × List ℕ =>
    (List.range x.1).map (fun j => x.2.idxOf j)) _ _
  have hn := ComputableInPolyTime.fst encUnary (encList encUnary)
  have hp := ComputableInPolyTime.snd encUnary (encList encUnary)
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have hpar := ComputableInPolyTime.fst (encPair encUnary (encList encUnary)) encUnary
  have hj := ComputableInPolyTime.snd (encPair encUnary (encList encUnary)) encUnary
  exact ComputableInPolyTime.idxOfWithInput (hp.comp hpar) hj

private theorem tableSet_poly {γ : Type} {encIn : γ ↪ List Bool}
    {T : γ → List (List (List ℕ))} {i j : γ → ℕ} {val : γ → List ℕ}
    (hT : ComputableInPolyTime T encIn encTable)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hval : ComputableInPolyTime val encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => tableSet (T x) (i x) (j x) (val x)) encIn encTable := by
  change ComputableInPolyTime
    (fun x => listSet (T x) (i x) (listSet ((T x).getD (i x) []) (j x) (val x))) _ _
  exact listSet_poly hT hi
    (listSet_poly (ComputableInPolyTime.listGetDWithInput hT hi []) hj hval)

/-- Uniform upper bound on the encoded length of any valid `n × n` list table:
every valid table has `n` rows of `n` lists of at most `n` numbers `< n`. -/
private theorem length_encTable_le_of_valid {n : ℕ} {T : List (List (List ℕ))}
    (hT : ValidListTable n T) :
    (encTable T).length ≤ 8 * (n + 1) * (n + 1) * (n + 1) * (n + 1) + 16 := by
  have h_entry : ∀ row ∈ T, ∀ e ∈ row,
      (encList encUnary e).length ≤ n * (2 * n + 1) := by
    intro row hrow e he
    have he_len : e.length ≤ n := by
      rcases (hT.2 row hrow).2 e he with rfl | ⟨σ, rfl⟩
      · exact Nat.zero_le n
      · rw [length_permToList]
    have he_el : ∀ x ∈ e, (encUnary x).length ≤ n := by
      intro x hx
      rcases (hT.2 row hrow).2 e he with rfl | ⟨σ, rfl⟩
      · cases hx
      · obtain ⟨k, hk, rfl⟩ := (mem_permToList σ).mp hx
        simp only [encUnary_apply, List.length_replicate]
        exact le_of_lt (σ ⟨k, hk⟩).isLt
    exact (length_encList_le encUnary e he_el).trans (Nat.mul_le_mul_right _ he_len)
  have h_row : ∀ row ∈ T,
      (encList (encList encUnary) row).length ≤ n * (2 * (n * (2 * n + 1)) + 1) := by
    intro row hrow
    have hlen := (hT.2 row hrow).1
    have := length_encList_le (encList encUnary) row (h_entry row hrow)
    rwa [hlen] at this
  have h1 := length_encList_le (encList (encList encUnary)) T h_row
  rw [hT.1] at h1
  dsimp only [encTable]
  have h2' : 2 * (n * (2 * n + 1)) + 1 ≤ 4 * (n + 1) * (n + 1) := by nlinarith
  have h3' : n * (2 * (n * (2 * n + 1)) + 1) ≤ 4 * n * (n + 1) * (n + 1) := by
    calc n * (2 * (n * (2 * n + 1)) + 1) ≤ n * (4 * (n + 1) * (n + 1)) :=
          Nat.mul_le_mul_left n h2'
      _ = 4 * n * (n + 1) * (n + 1) := by ring
  have h4' : 2 * (n * (2 * (n * (2 * n + 1)) + 1)) + 1 ≤
      8 * (n + 1) * (n + 1) * (n + 1) := by
    have hsq : 1 ≤ (n + 1) * (n + 1) := by nlinarith
    calc 2 * (n * (2 * (n * (2 * n + 1)) + 1)) + 1
        ≤ 2 * (4 * n * (n + 1) * (n + 1)) + 1 := by omega
      _ ≤ 2 * (4 * n * (n + 1) * (n + 1)) + 8 * (n + 1) * (n + 1) := by nlinarith
      _ = 8 * (n + 1) * (n + 1) * (n + 1) := by ring
  have h5' : n * (2 * (n * (2 * (n * (2 * n + 1)) + 1)) + 1) ≤
      8 * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by
    calc n * (2 * (n * (2 * (n * (2 * n + 1)) + 1)) + 1)
        ≤ (n + 1) * (8 * (n + 1) * (n + 1) * (n + 1)) :=
          Nat.mul_le_mul (Nat.le_succ n) h4'
      _ = 8 * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by ring
  exact h1.trans (h5'.trans (Nat.le_add_right _ _))

/-- Encoded length bound for `listSet`: replacing one entry adds at most `2 * |enc val| + 1`. -/
private theorem length_encList_listSet_le {α : Type} (enc : α ↪ List Bool)
    (l : List α) (idx : ℕ) (val : α) :
    (encList enc (listSet l idx val)).length ≤
      (encList enc l).length + l.length * (2 * (enc val).length + 1) := by
  -- Use direct induction via `length_encList_le`? Even sharper: induction on `l.zipIdx`!
  -- Actually `length_encList_le` with `b = max (encList enc l).length (enc val).length` gives
  -- `l.length * (2 * (|l| + |val|) + 1)` — wait, let's prove the sharp additive bound directly!
  have haux : ∀ (xs : List (α × ℕ)),
      (encList enc (xs.map (fun p => if p.2 == idx then val else p.1))).length ≤
        (encList enc (xs.map Prod.fst)).length + xs.length * (2 * (enc val).length + 1) := by
    intro xs
    induction xs with
    | nil => simp
    | cons p xs ih =>
      simp only [List.map_cons, encList_cons, List.length_append, length_frame, List.length_cons]
      split <;> nlinarith
  have h1 := haux l.zipIdx
  rw [listSet_eq_map]
  simpa [map_fst_zipIdx] using h1

private theorem length_encList_listSet_le' {α : Type} (enc : α ↪ List Bool)
    (l : List α) (idx : ℕ) (val : α) :
    (encList enc (listSet l idx val)).length ≤
      (encList enc l).length + (encList enc l).length * (2 * (enc val).length + 1) :=
  (length_encList_listSet_le enc l idx val).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (SizedListEncoding.length_le (encA := enc) (encL := encList enc) l)) _)

private theorem length_encTable_tableSet_le (T : List (List (List ℕ))) (i j : ℕ) (val : List ℕ) :
    (encTable (tableSet T i j val)).length ≤
      ((encTable T).length + 1) * ((encTable T).length + 1) *
        (4 * (encList encUnary val).length + 8) + 8 := by
  have hrow : (encList (encList encUnary) (T.getD i [])).length ≤ (encTable T).length := by
    by_cases hi : i < T.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact SizedListEncoding.length_elem_le (encA := encList (encList encUnary))
        (encL := encTable) T _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  have h1 := length_encList_listSet_le' (encList encUnary) (T.getD i []) j val
  have h2 := length_encList_listSet_le' (encList (encList encUnary)) T i
    (listSet (T.getD i []) j val)
  rw [tableSet_eq_listSet]
  dsimp only [encTable] at hrow h1 h2 ⊢
  nlinarith

/-- `siftOne` is computable in polynomial time on all inputs `(n, T, g)`. -/
theorem computableInPolyTime_siftOne :
    ComputableInPolyTime (fun x : (ℕ × List (List (List ℕ))) × List ℕ =>
      siftOne x.1.1 x.1.2 x.2)
      (encPair (encPair encUnary encTable) (encList encUnary)) encTable := by
  change ComputableInPolyTime (fun x : (ℕ × List (List (List ℕ))) × List ℕ =>
    ((List.range x.1.1).foldl (fun (st : List (List (List ℕ)) × List ℕ × Bool) (i : ℕ) =>
      if st.2.2 then st
      else
        let j := st.2.1.getD i x.1.1
        let h := (st.1.getD i []).getD j []
        if h.isEmpty then (tableSet st.1 i j st.2.1, st.2.1, true)
        else (st.1, permMul x.1.1 (permInv x.1.1 h) st.2.1, false))
      (x.1.2, x.2, false)).1) _ _
  let encSt := encPair encTable (encPair (encList encUnary) encBool)
  let step := fun (n : ℕ) (st : List (List (List ℕ)) × List ℕ × Bool) (i : ℕ) =>
    if st.2.2 then st
    else
      let j := st.2.1.getD i n
      let h := (st.1.getD i []).getD j []
      if h.isEmpty then (tableSet st.1 i j st.2.1, st.2.1, true)
      else (st.1, permMul n (permInv n h) st.2.1, false)
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × (List (List (List ℕ)) × List ℕ × Bool)) × ℕ => step p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encSt) encUnary) encSt := by
    dsimp only [step]
    have hpar := ComputableInPolyTime.fst (encPair encUnary encSt) encUnary
    have hi := ComputableInPolyTime.snd (encPair encUnary encSt) encUnary
    have hn := hpar.fst'
    have hst := hpar.snd'
    have hT := hst.fst'
    have hg := hst.snd'.fst'
    have hdone := hst.snd'.snd'
    have hj := listGetDComputed hg hi hn
    have hrow := ComputableInPolyTime.listGetDWithInput hT hi []
    have hh := ComputableInPolyTime.listGetDWithInput hrow hj []
    have hnewT := tableSet_poly hT hi hj hg
    have hinv := permInv_poly.comp (hn.prod hh)
    have hmul := permMul_poly.comp (hn.prod (hinv.prod hg))
    exact ComputableInPolyTime.ite' hdone hst
      (ComputableInPolyTime.ite' ((ComputableInPolyTime.listIsEmpty' encUnary).comp hh)
        (hnewT.prod (hg.prod (.const true)))
        (hT.prod (hmul.prod (.const false))))
  -- Prove polynomial size bound on every reachable prefix state of `siftOne`
  have hinv_prefix : ∀ (x : (ℕ × List (List (List ℕ))) × List ℕ) (k : ℕ),
      let st := ((List.range x.1.1).take k).foldl (step x.1.1) (x.1.2, x.2, false)
      (st.2.2 = false → st.1 = x.1.2 ∧
        (encList encUnary st.2.1).length ≤
          (encList encUnary x.2).length +
            x.1.1 * (2 * (x.1.1 + (encTable x.1.2).length) + 1)) ∧
      (encSt st).length ≤
        2 * (((encTable x.1.2).length + 1) * ((encTable x.1.2).length + 1) *
          (4 * ((encList encUnary x.2).length +
            x.1.1 * (2 * (x.1.1 + (encTable x.1.2).length) + 1)) + 8) + 8) +
        2 * ((encList encUnary x.2).length +
          x.1.1 * (2 * (x.1.1 + (encTable x.1.2).length) + 1)) + 8 := by
    intro x k
    set n := x.1.1
    set T := x.1.2
    set g := x.2
    set B := (encList encUnary g).length + n * (2 * (n + (encTable T).length) + 1)
    induction k with
    | zero =>
      simp only [List.take_zero, List.foldl_nil]
      refine ⟨fun _ => ⟨trivial, ?_⟩, ?_⟩
      · dsimp only [B]; omega
      · simp only [encSt, length_encPair, encBool_apply, List.length_singleton]
        have hB : (encList encUnary g).length ≤ B := by omega
        nlinarith
    | succ k ih =>
      by_cases hk : k < (List.range n).length
      · rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
        set st := ((List.range n).take k).foldl (step n) (T, g, false)
        cases hdone : st.2.2 with
        | true =>
          have hst_eq : step n st ((List.range n)[k]) = st := by simp [step, hdone]
          rw [hst_eq]
          exact ⟨(fun h => by rw [hdone] at h; cases h), ih.2⟩
        | false =>
          obtain ⟨hT_eq, hg_le⟩ := ih.1 hdone
          set i := (List.range n)[k]
          set j := st.2.1.getD i n
          set h := (st.1.getD i []).getD j []
          simp only [step, hdone, Bool.false_eq_true, ↓reduceIte]
          cases hemp : h.isEmpty with
          | true =>
            simp only [↓reduceIte]
            refine ⟨(fun h => by cases h), ?_⟩
            simp only [encSt, length_encPair, encBool_apply, List.length_singleton]
            rw [hT_eq]
            have hts := length_encTable_tableSet_le T i j st.2.1
            nlinarith
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hmul_le : (encList encUnary (permMul n (permInv n h) st.2.1)).length ≤
                n * (2 * (n + (encTable T).length) + 1) := by
              apply (length_encList_le encUnary _ (b := n + (encTable T).length) ?_).trans
              · rw [length_permMul]
              · intro z hz
                obtain ⟨m, _, rfl⟩ := (mem_permMul n _ _).mp hz
                simp only [encUnary_apply, List.length_replicate]
                set q := st.2.1.getD m n
                by_cases hq : q < (permInv n h).length
                · rw [List.getD_eq_getElem _ _ hq, getElem_permInv n h hq]
                  have hidx : h.idxOf q ≤ h.length := List.idxOf_le_length
                  have hlen_h : h.length ≤ (encList encUnary h).length :=
                    SizedListEncoding.length_le (encA := encUnary) (encL := encList encUnary) h
                  have hrow_le : (encList (encList encUnary) (T.getD i [])).length ≤
                      (encTable T).length := by
                    by_cases hi : i < T.length
                    · rw [List.getD_eq_getElem _ _ hi]
                      exact SizedListEncoding.length_elem_le (encA := encList (encList encUnary))
                        (encL := encTable) T _ (List.getElem_mem hi)
                    · rw [List.getD_eq_default _ _ (by omega)]; simp
                  have hh_le : (encList encUnary h).length ≤
                      (encList (encList encUnary) (T.getD i [])).length := by
                    dsimp [h]; rw [hT_eq]
                    by_cases hj : j < (T.getD i []).length
                    · rw [List.getD_eq_getElem _ _ hj]
                      exact SizedListEncoding.length_elem_le (encA := encList encUnary)
                        (encL := encList (encList encUnary)) (T.getD i []) _ (List.getElem_mem hj)
                    · rw [List.getD_eq_default _ _ (by omega)]; simp
                  omega
                · rw [List.getD_eq_default _ _ (by omega)]; omega
            have hmul_le' : (encList encUnary
                (permMul n (permInv n ((T.getD i []).getD (st.2.1.getD i n) [])) st.2.1)).length ≤
                n * (2 * (n + (encTable T).length) + 1) := by
              simpa only [h, j, hT_eq] using hmul_le
            refine ⟨fun _ => ⟨hT_eq, ?_⟩, ?_⟩
            · rw [hT_eq]; dsimp only [B]; omega
            · simp only [encSt, length_encPair, encBool_apply, List.length_singleton, hT_eq]
              dsimp only [B] at hmul_le' ⊢
              nlinarith
      · have htake : (List.range n).take (k + 1) = (List.range n).take k := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [htake]; exact ih
  have hfold : ComputableInPolyTime
      (fun x : (ℕ × List (List (List ℕ))) × List ℕ =>
        (List.range x.1.1).foldl (step x.1.1) (x.1.2, x.2, false))
      (encPair (encPair encUnary encTable) (encList encUnary)) encSt := by
    let encIn := encPair (encPair encUnary encTable) (encList encUnary)
    have hpar := (ComputableInPolyTime.fst (encPair encUnary encTable) (encList encUnary)).fst'
    have hT := (ComputableInPolyTime.fst (encPair encUnary encTable) (encList encUnary)).snd'
    have hg := ComputableInPolyTime.snd (encPair encUnary encTable) (encList encUnary)
    let bound (x : (ℕ × List (List (List ℕ))) × List ℕ) :=
      2 * (((encTable x.1.2).length + 1) * ((encTable x.1.2).length + 1) *
        (4 * ((encList encUnary x.2).length +
          x.1.1 * (2 * (x.1.1 + (encTable x.1.2).length) + 1)) + 8) + 8) +
      2 * ((encList encUnary x.2).length +
        x.1.1 * (2 * (x.1.1 + (encTable x.1.2).length) + 1)) + 8
    have hbound : PolyBounded (fun x => (encIn x).length) bound := by
      have h1 : PolyBounded (fun x => (encIn x).length) (fun x => x.1.1) := hpar.polyBounded
      have h2 : PolyBounded (fun x => (encIn x).length) (fun x => (encTable x.1.2).length) :=
        hT.polyBounded_length
      have h3 : PolyBounded (fun x => (encIn x).length) (fun x => (encList encUnary x.2).length) :=
        hg.polyBounded_length
      have hB : PolyBounded (fun x => (encIn x).length)
          (fun x => (encList encUnary x.2).length +
            x.1.1 * (2 * (x.1.1 + (encTable x.1.2).length) + 1)) :=
        h3.add (h1.mul (((PolyBounded.const 2).mul (h1.add h2)).add (PolyBounded.const 1)))
      have hT1 := h2.add (PolyBounded.const 1)
      have hinner := (hT1.mul hT1).mul (((PolyBounded.const 4).mul hB).add (PolyBounded.const 8))
      exact (((PolyBounded.const 2).mul (hinner.add (PolyBounded.const 8))).add
        ((PolyBounded.const 2).mul hB)).add (PolyBounded.const 8)
    exact ComputableInPolyTime.foldlWith (encA := encUnary) (encB := encSt)
      (encL := encList encUnary) hpar (ComputableInPolyTime.range.comp hpar)
      (hT.prod (hg.prod (.const false))) hstep hbound (fun x k _ => (hinv_prefix x k).2)
  exact hfold.fst'

private theorem isValidTable_poly :
    ComputableInPolyTime (fun p : ℕ × List (List (List ℕ)) => isValidTable p.1 p.2)
      (encPair encUnary encTable) encBool := by
  change ComputableInPolyTime (fun p : ℕ × List (List (List ℕ)) =>
    (p.2.length == p.1) &&
      p.2.all (fun row => (row.length == p.1) && row.all (fun e => e.isEmpty || isPermList p.1 e)))
    _ _
  have hn := ComputableInPolyTime.fst encUnary encTable
  have hT := ComputableInPolyTime.snd encUnary encTable
  have h1 := ComputableInPolyTime.beq
    ((ComputableInPolyTime.length_list (encList (encList encUnary))).comp hT) hn
  have h2 : ComputableInPolyTime (fun p : ℕ × List (List (List ℕ)) =>
      p.2.all (fun row => (row.length == p.1) &&
        row.all (fun e => e.isEmpty || isPermList p.1 e)))
      (encPair encUnary encTable) encBool := by
    apply ComputableInPolyTime.allWithInput hT
    have hpar := ComputableInPolyTime.fst (encPair encUnary encTable) (encList (encList encUnary))
    have hrow := ComputableInPolyTime.snd (encPair encUnary encTable) (encList (encList encUnary))
    have ha := ComputableInPolyTime.beq
      ((ComputableInPolyTime.length_list (encList encUnary)).comp hrow) (hn.comp hpar)
    have hb : ComputableInPolyTime (fun q : (ℕ × List (List (List ℕ))) × List (List ℕ) =>
        q.2.all (fun e => e.isEmpty || isPermList q.1.1 e))
        (encPair (encPair encUnary encTable) (encList (encList encUnary))) encBool := by
      apply ComputableInPolyTime.allWithInput hrow
      have hpar2 := ComputableInPolyTime.fst
        (encPair (encPair encUnary encTable) (encList (encList encUnary))) (encList encUnary)
      have he := ComputableInPolyTime.snd
        (encPair (encPair encUnary encTable) (encList (encList encUnary))) (encList encUnary)
      exact ComputableInPolyTime.bool_or'
        ((ComputableInPolyTime.listIsEmpty' encUnary).comp he)
        (isPermList_poly.comp ((hn.comp (hpar.comp hpar2)).prod he))
    exact ComputableInPolyTime.bool_and' ha hb
  exact ComputableInPolyTime.bool_and' h1 h2

private theorem closeOnceSafe_poly :
    ComputableInPolyTime (fun p : ℕ × List (List (List ℕ)) => closeOnceSafe p.1 p.2)
      (encPair encUnary encTable) encTable := by
  change ComputableInPolyTime (fun p : ℕ × List (List (List ℕ)) =>
    if isValidTable p.1 p.2 then closeOnce p.1 p.2 else p.2) _ _
  have hn := ComputableInPolyTime.fst encUnary encTable
  have hT := ComputableInPolyTime.snd encUnary encTable
  -- On valid tables, every intermediate `siftAll` step preserves `ValidListTable`.
  have hclose_on_valid : ComputableInPolyTime
      (fun p : ℕ × List (List (List ℕ)) =>
        if isValidTable p.1 p.2 then closeOnce p.1 p.2 else p.2)
      (encPair encUnary encTable) encTable := by
    let entries (p : ℕ × List (List (List ℕ))) :=
      (p.2.flatten).filter (fun e => !e.isEmpty)
    let prods (p : ℕ × List (List (List ℕ))) :=
      if isValidTable p.1 p.2 then
        (entries p).flatMap (fun g => (entries p).map (fun h => permMul p.1 g h))
      else []
    have hentries : ComputableInPolyTime entries (encPair encUnary encTable)
        (encList (encList encUnary)) := by
      dsimp only [entries]
      apply ComputableInPolyTime.filterWithInput ((ComputableInPolyTime.flatten _).comp hT)
      have he := ComputableInPolyTime.snd (encPair encUnary encTable) (encList encUnary)
      exact ComputableInPolyTime.bool_not.comp
        ((ComputableInPolyTime.listIsEmpty' encUnary).comp he)
    have hprods : ComputableInPolyTime prods (encPair encUnary encTable)
        (encList (encList encUnary)) := by
      dsimp only [prods]
      refine ComputableInPolyTime.ite' isValidTable_poly ?_ (.const [])
      apply ComputableInPolyTime.flatMapWithInput hentries
      have hpar := ComputableInPolyTime.fst (encPair encUnary encTable) (encList encUnary)
      have hg := ComputableInPolyTime.snd (encPair encUnary encTable) (encList encUnary)
      apply ComputableInPolyTime.mapWithInput (hentries.comp hpar)
      have hpar2 := ComputableInPolyTime.fst
        (encPair (encPair encUnary encTable) (encList encUnary)) (encList encUnary)
      have hh := ComputableInPolyTime.snd
        (encPair (encPair encUnary encTable) (encList encUnary)) (encList encUnary)
      exact permMul_poly.comp ((hn.comp (hpar.comp hpar2)).prod ((hg.comp hpar2).prod hh))
    have hsiftAll : ComputableInPolyTime
        (fun p : ℕ × List (List (List ℕ)) => siftAll p.1 p.2 (prods p))
        (encPair encUnary encTable) encTable := by
      let encIn := encPair encUnary encTable
      let bound (p : ℕ × List (List (List ℕ))) :=
        (encTable p.2).length + 8 * (p.1 + 1) * (p.1 + 1) * (p.1 + 1) * (p.1 + 1) + 16
      have hbound : PolyBounded (fun p => (encIn p).length) bound := by
        have h1 := hn.polyBounded
        have h2 := hT.polyBounded_length
        have hp1 := h1.add (PolyBounded.const 1)
        exact (h2.add (((((PolyBounded.const 8).mul hp1).mul hp1).mul hp1).mul hp1)).add
          (PolyBounded.const 16)
      exact ComputableInPolyTime.foldlWith (encA := encList encUnary) (encB := encTable)
        (encL := encList (encList encUnary)) hn hprods hT computableInPolyTime_siftOne hbound
        (fun p k _ => by
          by_cases hv : isValidTable p.1 p.2 = true
          · have hTv : ValidListTable p.1 p.2 := (isValidTable_eq_true_iff p.1 p.2).mp hv
            have hall_valid : ∀ g ∈ (prods p).take k,
                ∃ σ : Equiv.Perm (Fin p.1), permToList σ = g := by
              intro g hg
              have hmem := List.mem_of_mem_take hg
              dsimp only [prods] at hmem
              simp only [hv, ↓reduceIte] at hmem
              obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hmem
              obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hb
              have hget : ∀ e ∈ entries p, ∃ σ : Equiv.Perm (Fin p.1), permToList σ = e := by
                intro e he
                obtain ⟨hfl, hne⟩ := List.mem_filter.mp he
                obtain ⟨row, hrow, herow⟩ := List.mem_flatten.mp hfl
                rcases (hTv.2 row hrow).2 e herow with rfl | h
                · simp at hne
                · exact h
              obtain ⟨σ₁, rfl⟩ := hget a ha
              obtain ⟨σ₂, rfl⟩ := hget b hb'
              exact ⟨σ₁ * σ₂, permToList_mul σ₁ σ₂⟩
            have hstep_v : ∀ (A : List (List (List ℕ))) (gs : List (List ℕ)),
                ValidListTable p.1 A →
                (∀ g ∈ gs, ∃ σ : Equiv.Perm (Fin p.1), permToList σ = g) →
                ValidListTable p.1 (gs.foldl (siftOne p.1) A) := by
              intro A gs
              induction gs generalizing A with
              | nil => intro hA _; exact hA
              | cons g gs ihgs =>
                intro hA hgs
                obtain ⟨σ, rfl⟩ := hgs g List.mem_cons_self
                exact ihgs _ (decodeTable_siftOne A hA σ).1
                  (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
            have hcur := hstep_v p.2 ((prods p).take k) hTv hall_valid
            exact (length_encTable_le_of_valid hcur).trans (by dsimp [bound]; omega)
          · simp only [prods, hv, Bool.false_eq_true, ↓reduceIte, List.take_nil, List.foldl_nil]
            dsimp [bound]; omega)
    refine hsiftAll.of_enc_eq fun p => ?_
    congr 1
    by_cases hv : isValidTable p.1 p.2 = true
    · simp only [hv, ↓reduceIte, prods, closeOnce_eq_siftAll, entries]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, prods, siftAll_nil]
  exact hclose_on_valid

private theorem initTable_poly :
    ComputableInPolyTime initTable encUnary encTable := by
  change ComputableInPolyTime (fun n : ℕ =>
    (List.range n).map (fun i => (List.range n).map (fun j => if i == j then List.range n else [])))
    _ _
  apply ComputableInPolyTime.mapWithInput ComputableInPolyTime.range
  have hn := ComputableInPolyTime.fst encUnary encUnary
  have hi := ComputableInPolyTime.snd encUnary encUnary
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have hpar := ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary
  have hj := ComputableInPolyTime.snd (encPair encUnary encUnary) encUnary
  exact ComputableInPolyTime.ite'
    (ComputableInPolyTime.beq (hi.comp hpar) hj)
    (ComputableInPolyTime.range.comp (hn.comp hpar))
    (.const [])

/-- **Schreier–Sims / Furst–Hopcroft–Luks in Native Polynomial Time**: `schreierSimsOrder` is
computable in polynomial time (`Turing.MultiTapeTM.ComputableInPolyTime`) from `(n, gens)` (with
`n` in unary and `gens` as a framed list of permutation lists) to `ℕ` in binary (`encNat`). -/
theorem computableInPolyTime_schreierSimsOrder :
    ComputableInPolyTime (fun p : ℕ × List (List ℕ) => schreierSimsOrder p.1 p.2)
      (encPair encUnary (encList (encList encUnary))) encNat := by
  let encIn := encPair encUnary (encList (encList encUnary))
  have hn := ComputableInPolyTime.fst encUnary (encList (encList encUnary))
  have hgens := ComputableInPolyTime.snd encUnary (encList (encList encUnary))
  have hvalid : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => p.2.filter (isPermList p.1))
      encIn (encList (encList encUnary)) := by
    apply ComputableInPolyTime.filterWithInput hgens
    exact isPermList_poly.comp
      ((hn.comp (ComputableInPolyTime.fst encIn (encList encUnary))).prod
        (ComputableInPolyTime.snd encIn (encList encUnary)))
  have hT0 : ComputableInPolyTime
      (fun p : ℕ × List (List ℕ) => siftAll p.1 (initTable p.1) (p.2.filter (isPermList p.1)))
      encIn encTable := by
    let bound (p : ℕ × List (List ℕ)) :=
      8 * (p.1 + 1) * (p.1 + 1) * (p.1 + 1) * (p.1 + 1) + 16
    have hbound : PolyBounded (fun p => (encIn p).length) bound := by
      have h1 := hn.polyBounded
      have hp1 := h1.add (PolyBounded.const 1)
      exact (((((PolyBounded.const 8).mul hp1).mul hp1).mul hp1).mul hp1).add
        (PolyBounded.const 16)
    exact ComputableInPolyTime.foldlWith (encA := encList encUnary) (encB := encTable)
      (encL := encList (encList encUnary)) hn hvalid (initTable_poly.comp hn)
      computableInPolyTime_siftOne hbound (fun p k _ => by
        have hstep_v : ∀ (A : List (List (List ℕ))) (gs : List (List ℕ)),
            ValidListTable p.1 A →
            (∀ g ∈ gs, ∃ σ : Equiv.Perm (Fin p.1), permToList σ = g) →
            ValidListTable p.1 (gs.foldl (siftOne p.1) A) := by
          intro A gs
          induction gs generalizing A with
          | nil => intro hA _; exact hA
          | cons g gs ihgs =>
            intro hA hgs
            obtain ⟨σ, rfl⟩ := hgs g List.mem_cons_self
            exact ihgs _ (decodeTable_siftOne A hA σ).1
              (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
        have hall : ∀ g ∈ (p.2.filter (isPermList p.1)).take k,
            ∃ σ : Equiv.Perm (Fin p.1), permToList σ = g := fun g hg =>
          (isPermList_eq_true_iff p.1 g).mp (List.mem_filter.mp (List.mem_of_mem_take hg)).2
        exact length_encTable_le_of_valid (hstep_v _ _ (initTable_valid p.1) hall))
  have hcloseTable : ComputableInPolyTime
      (fun p : ℕ × List (List ℕ) => closeTable p.1 p.2) encIn encTable := by
    change ComputableInPolyTime (fun p : ℕ × List (List ℕ) =>
      (closeOnceSafe p.1)^[p.1 * p.1] (siftAll p.1 (initTable p.1) (p.2.filter (isPermList p.1))))
      _ _
    let bound (p : ℕ × List (List ℕ)) :=
      8 * (p.1 + 1) * (p.1 + 1) * (p.1 + 1) * (p.1 + 1) + 16
    have hbound : PolyBounded (fun p => (encIn p).length) bound := by
      have h1 := hn.polyBounded
      have hp1 := h1.add (PolyBounded.const 1)
      exact (((((PolyBounded.const 8).mul hp1).mul hp1).mul hp1).mul hp1).add
        (PolyBounded.const 16)
    have hcount : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => p.1 * p.1) encIn encUnary :=
      ComputableInPolyTime.unary_mul.comp (hn.prod hn)
    exact ComputableInPolyTime.iterateWith hn hcount hT0 closeOnceSafe_poly hbound
      (fun p k _ => by
        -- Prove every iterate of `closeOnceSafe p.1` from `T₀` satisfies `ValidListTable p.1`
        have hT0_v : ValidListTable p.1 (siftAll p.1 (initTable p.1)
            (p.2.filter (isPermList p.1))) := by
          have hstep_v : ∀ (A : List (List (List ℕ))) (gs : List (List ℕ)),
              ValidListTable p.1 A →
              (∀ g ∈ gs, ∃ σ : Equiv.Perm (Fin p.1), permToList σ = g) →
              ValidListTable p.1 (gs.foldl (siftOne p.1) A) := by
            intro A gs
            induction gs generalizing A with
            | nil => intro hA _; exact hA
            | cons g gs ihgs =>
              intro hA hgs
              obtain ⟨σ, rfl⟩ := hgs g List.mem_cons_self
              exact ihgs _ (decodeTable_siftOne A hA σ).1
                (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
          exact hstep_v _ _ (initTable_valid p.1) fun g hg =>
            (isPermList_eq_true_iff p.1 g).mp (List.mem_filter.mp hg).2
        have hiter_v : ∀ m, ValidListTable p.1 ((closeOnceSafe p.1)^[m]
            (siftAll p.1 (initTable p.1) (p.2.filter (isPermList p.1)))) := by
          intro m
          induction m with
          | zero => exact hT0_v
          | succ m ihm =>
            rw [Function.iterate_succ_apply']
            have hvt : isValidTable p.1 ((closeOnceSafe p.1)^[m]
                (siftAll p.1 (initTable p.1) (p.2.filter (isPermList p.1)))) = true :=
              (isValidTable_eq_true_iff p.1 _).mpr ihm
            rw [closeOnceSafe_eq_of_valid hvt, closeOnce_eq_siftAll]
            have hstep_v : ∀ (A : List (List (List ℕ))) (gs : List (List ℕ)),
                ValidListTable p.1 A →
                (∀ g ∈ gs, ∃ σ : Equiv.Perm (Fin p.1), permToList σ = g) →
                ValidListTable p.1 (gs.foldl (siftOne p.1) A) := by
              intro A gs
              induction gs generalizing A with
              | nil => intro hA _; exact hA
              | cons g gs ihgs =>
                intro hA hgs
                obtain ⟨σ, rfl⟩ := hgs g List.mem_cons_self
                exact ihgs _ (decodeTable_siftOne A hA σ).1
                  (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
            refine hstep_v _ _ ihm fun g hg => ?_
            obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hg
            obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hb
            have hget : ∀ e ∈ ((closeOnceSafe p.1)^[m]
                (siftAll p.1 (initTable p.1) (p.2.filter (isPermList p.1)))).flatten.filter
                  (fun e => !e.isEmpty),
                ∃ σ : Equiv.Perm (Fin p.1), permToList σ = e := by
              intro e he
              obtain ⟨hfl, hne⟩ := List.mem_filter.mp he
              obtain ⟨row, hrow, herow⟩ := List.mem_flatten.mp hfl
              rcases (ihm.2 row hrow).2 e herow with rfl | h
              · simp at hne
              · exact h
            obtain ⟨σ₁, rfl⟩ := hget a ha
            obtain ⟨σ₂, rfl⟩ := hget b hb'
            exact ⟨σ₁ * σ₂, permToList_mul σ₁ σ₂⟩
        exact length_encTable_le_of_valid (hiter_v k))
  -- Finally map each row to its non-empty count in binary and take `binary_prod`
  have hrowCounts : ComputableInPolyTime
      (fun p : ℕ × List (List ℕ) =>
        (closeTable p.1 p.2).map (fun row => row.countP (fun entry => !entry.isEmpty)))
      encIn (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput hcloseTable
    have hrow := ComputableInPolyTime.snd encIn (encList (encList encUnary))
    have hcnt : ComputableInPolyTime
        (fun q : (ℕ × List (List ℕ)) × List (List ℕ) =>
          q.2.countP (fun entry => !entry.isEmpty))
        (encPair encIn (encList (encList encUnary))) encUnary := by
      apply ComputableInPolyTime.countPWithInput hrow
      have he := ComputableInPolyTime.snd
        (encPair encIn (encList (encList encUnary))) (encList encUnary)
      exact ComputableInPolyTime.bool_not.comp
        ((ComputableInPolyTime.listIsEmpty' encUnary).comp he)
    exact ComputableInPolyTime.unary_to_binary.comp hcnt
  exact ComputableInPolyTime.binary_prod.comp hrowCounts

end CslibFrontier.Computability.Complexity.SchreierSims
