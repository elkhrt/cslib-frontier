/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Problems.BackAndForthPaths.Basic
public import CslibFrontier.Computability.Complexity.Problems.BackAndForthPaths.Soundness
public import CslibFrontier.Computability.Complexity.Problems.BackAndForthPaths.Switch

import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Reduction.Guard
import Mathlib.Data.List.GetD

/-!
# NP-Completeness of Back-and-Forth Paths

This module proves that Back-and-Forth Paths (`BFP`) is `NP`-complete
 via a polynomial-time reduction from `SAT` and `ThreeSAT`.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL
open Turing.MultiTapeTM ComputableInPolyTime

namespace BackAndForthPaths

private lemma nodup_swNode4 (k : ℕ) {r₁ r₂ r₃ r₄ : ℕ}
    (hr : r₁ < 14 ∧ r₂ < 14 ∧ r₃ < 14 ∧ r₄ < 14)
    (hnd : ([r₁, r₂, r₃, r₄] : List ℕ).Nodup) :
    ([swNode k r₁, swNode k r₂, swNode k r₃, swNode k r₄] : List ℕ).Nodup := by
  have hinj : ∀ a ∈ ([r₁, r₂, r₃, r₄] : List ℕ), ∀ b ∈ ([r₁, r₂, r₃, r₄] : List ℕ),
      swNode k a = swNode k b → a = b := fun a ha b hb h ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have ha' : a < 14 := by rcases ha with rfl | rfl | rfl | rfl <;> omega
    have hb' : b < 14 := by rcases hb with rfl | rfl | rfl | rfl <;> omega
    exact (swNode_inj ha' hb' h).2
  simpa only [List.map_cons, List.map_nil] using List.Nodup.map_on hinj hnd

private lemma swNode_k_eq_of_mem4 {k₁ k₂ r₁ r₂ r₃ r₄ s₁ s₂ s₃ s₄ v : ℕ}
    (hr : r₁ < 14 ∧ r₂ < 14 ∧ r₃ < 14 ∧ r₄ < 14)
    (hs : s₁ < 14 ∧ s₂ < 14 ∧ s₃ < 14 ∧ s₄ < 14)
    (h1 : v = swNode k₁ r₁ ∨ v = swNode k₁ r₂ ∨ v = swNode k₁ r₃ ∨ v = swNode k₁ r₄)
    (h2 : v = swNode k₂ s₁ ∨ v = swNode k₂ s₂ ∨ v = swNode k₂ s₃ ∨ v = swNode k₂ s₄) :
    k₁ = k₂ := by
  have ha : ∃ r < 14, v = swNode k₁ r := by
    rcases h1 with rfl | rfl | rfl | rfl <;> exact ⟨_, by omega, rfl⟩
  have hb : ∃ s < 14, v = swNode k₂ s := by
    rcases h2 with rfl | rfl | rfl | rfl <;> exact ⟨_, by omega, rfl⟩
  obtain ⟨r, hr', hvr⟩ := ha
  obtain ⟨s, hs', hvs⟩ := hb
  exact (swNode_inj hr' hs' (hvr.symm.trans hvs)).1

private lemma swNode_disj4 {k₁ k₂ r₁ r₂ r₃ r₄ s₁ s₂ s₃ s₄ v : ℕ}
    (hr : r₁ < 14 ∧ r₂ < 14 ∧ r₃ < 14 ∧ r₄ < 14)
    (hs : s₁ < 14 ∧ s₂ < 14 ∧ s₃ < 14 ∧ s₄ < 14)
    (hd : ∀ r ∈ ([r₁, r₂, r₃, r₄] : List ℕ), r ∉ ([s₁, s₂, s₃, s₄] : List ℕ))
    (h1 : v = swNode k₁ r₁ ∨ v = swNode k₁ r₂ ∨ v = swNode k₁ r₃ ∨ v = swNode k₁ r₄)
    (h2 : v = swNode k₂ s₁ ∨ v = swNode k₂ s₂ ∨ v = swNode k₂ s₃ ∨ v = swNode k₂ s₄) :
    False := by
  have ha : ∃ r ∈ ([r₁, r₂, r₃, r₄] : List ℕ), r < 14 ∧ v = swNode k₁ r := by
    rcases h1 with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, by omega, rfl⟩
  have hb : ∃ s ∈ ([s₁, s₂, s₃, s₄] : List ℕ), s < 14 ∧ v = swNode k₂ s := by
    rcases h2 with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, by omega, rfl⟩
  obtain ⟨r, hrm, hr', hvr⟩ := ha
  obtain ⟨s, hsm, hs', hvs⟩ := hb
  have hrs := (swNode_inj hr' hs' (hvr.symm.trans hvs)).2
  exact hd r hrm (hrs ▸ hsm)

private lemma isChain_range_flatMap {E : ℕ → ℕ → Prop} (node : ℕ → ℕ) (f : ℕ → List ℕ) :
    ∀ n, (∀ i < n, (f i).IsChain E ∧ (f i).head? = some (node i) ∧
        ∀ u, u ∈ (f i).getLast? → E u (node (i + 1))) →
      ((List.range n).flatMap f).IsChain E ∧
        (n = 0 ∨ ((List.range n).flatMap f).head? = some (node 0)) ∧
        (∀ u, u ∈ ((List.range n).flatMap f).getLast? → E u (node n)) := by
  intro n
  induction n with
  | zero =>
    intro _; exact ⟨List.IsChain.nil, Or.inl rfl, fun _ h ↦ by simp at h⟩
  | succ n ih =>
    intro h
    obtain ⟨ih_ch, ih_hd, ih_lst⟩ := ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)
    obtain ⟨hfn_ch, hfn_hd, hfn_lst⟩ := h n (Nat.lt_succ_self n)
    have hfn_ne : f n ≠ [] := by intro he; rw [he] at hfn_hd; simp at hfn_hd
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨List.isChain_append.mpr ⟨ih_ch, hfn_ch, fun u hu v hv ↦ ?_⟩, Or.inr ?_, fun u hu ↦ ?_⟩
    · rw [hfn_hd] at hv
      rw [Option.mem_def, Option.some.injEq] at hv
      exact hv ▸ ih_lst u hu
    · rcases ih_hd with rfl | hhd
      · simpa using hfn_hd
      · have hne : (List.range n).flatMap f ≠ [] := by
          intro he; rw [he] at hhd; simp at hhd
        rw [List.head?_append_of_ne_nil _ hne, hhd]
    · rw [List.getLast?_append_of_ne_nil _ hfn_ne] at hu
      exact hfn_lst u hu

private lemma complete_of_sat {φ : CNF ℕ} (hφ : φ ∈ SAT) : toBFP φ ∈ BFP := by
  classical
  obtain ⟨σ, hσ⟩ := hφ
  set N := φ.vars.length
  set M := φ.length
  set lits := litList φ
  set K := lits.length
  let dir : ℕ → Bool := fun i ↦ σ (φ.vars.getD i 0)
  let isTrue : ℕ → Bool := fun k ↦
    let lit := lits.getD k ((0, 0), false)
    decide (dir lit.1.2 = lit.2)
  have hpick_ex : ∀ j, j < M → ∃ k < K,
      (lits.getD k ((0, 0), false)).1.1 = j ∧ isTrue k = true := by
    intro j hj
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).mp
      ((CNF.eval_eq_true_iff _ _).mp hσ φ[j] (List.getElem_mem hj))
    have hmem_lit : ((j, φ.vars.idxOf l.1), l.2) ∈ lits :=
      mem_litList_of_mem_clause hj hl
    obtain ⟨k, hk, hk_eq⟩ := List.getElem_of_mem hmem_lit
    refine ⟨k, hk, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hk, hk_eq]
    · simp only [isTrue, List.getD_eq_getElem _ _ hk, hk_eq, decide_eq_true_eq]
      have hl_var : l.1 ∈ φ.vars :=
        List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hl⟩, rfl⟩
      have hi : φ.vars.idxOf l.1 < φ.vars.length := List.idxOf_lt_length_iff.mpr hl_var
      simp only [dir, List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi]
      exact hσl
  let pick : ℕ → ℕ := fun j ↦ if hj : j < M then (hpick_ex j hj).choose else 0
  have hpick : ∀ j (hj : j < M), pick j < K ∧
      (lits.getD (pick j) ((0, 0), false)).1.1 = j ∧ isTrue (pick j) = true :=
    fun j hj ↦ by simpa [pick, hj] using (hpick_ex j hj).choose_spec
  let E : ℕ → ℕ → Prop := fun u v ↦ (u, v) ∈ bfpEdges φ
  have hmem_sw : ∀ k < K, ∀ e ∈ switchArcs k, e ∈ bfpEdges φ := fun k hk _ he ↦
    mem_bfpEdges_switchArcs hk he
  have hmem_var : ∀ i < N, ∀ val : Bool, ∀ e ∈ chainArcs (varNode i) (varNode (i + 1))
      (varOccs φ i val), e ∈ bfpEdges φ := fun _ hi val _ he ↦
    mem_bfpEdges_varChain hi val he
  have hmem_cl : ∀ k < K,
      E (clauseNode (lits.getD k ((0, 0), false)).1.1) (swNode k swRin) ∧
      E (swNode k swRout) (clauseNode ((lits.getD k ((0, 0), false)).1.1 + 1)) := fun _ hk ↦
    mem_bfpEdges_clause hk
  let varSeg (i : ℕ) : List ℕ :=
    varNode i :: (varOccs φ i (dir i)).flatMap fun k ↦
      [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]
  let clauseSeg (j : ℕ) : List ℕ :=
    let k := pick j
    [clauseNode j, swNode k swRin, swNode k swX2, swNode k swX, swNode k swRout]
  let swP1 (k : ℕ) : List ℕ :=
    if isTrue k then [swNode k swC, swNode k swY, swNode k swV, swNode k swA]
    else [swNode k swC, swNode k swX, swNode k swU, swNode k swA]
  let swP2 (k : ℕ) : List ℕ :=
    if isTrue k then [swNode k swB, swNode k swU, swNode k swY2, swNode k swD]
    else [swNode k swB, swNode k swV, swNode k swX2, swNode k swD]
  let Vseg : List ℕ := (List.range N).flatMap varSeg ++ [varNode N]
  let Cseg : List ℕ := (List.range M).flatMap clauseSeg ++ [clauseNode M]
  let Sseg : List ℕ := (List.range K).reverse.flatMap swP1
  let P₁ : List ℕ := s1Node :: (Vseg ++ Cseg ++ Sseg ++ [t1Node])
  let P₂ : List ℕ := s2Node :: ((List.range K).flatMap swP2 ++ [t2Node])
  -- 1. `IsChain` for `P₂`
  have hP₂_ch : P₂.IsChain E := by
    have hsw2 : ∀ k < K, (swP2 k).IsChain E ∧ (swP2 k).head? = some (swNode k swB) ∧
        ∀ u, u ∈ (swP2 k).getLast? → E u (if k + 1 < K then swNode (k + 1) swB else t2Node) := by
      intro k hk
      refine ⟨?_, ?_, ?_⟩
      · simp only [swP2]
        split_ifs <;>
          exact List.IsChain.cons_cons (hmem_sw k hk _ (by simp [mem_switchArcs_iff]))
            (List.IsChain.cons_cons (hmem_sw k hk _ (by simp [mem_switchArcs_iff]))
              (List.IsChain.cons_cons (hmem_sw k hk _ (by simp [mem_switchArcs_iff]))
                (List.IsChain.singleton _)))
      · simp only [swP2]; split_ifs <;> rfl
      · intro u hu
        have hu_eq : u = swNode k swD := by
          simp only [swP2] at hu; split_ifs at hu <;> simpa [eq_comm] using hu
        subst hu_eq
        split_ifs with hlt
        · exact (mem_bfpEdges_stack_mid hlt).1
        · have hk_eq : k = K - 1 := by omega
          subst hk_eq
          exact (mem_bfpEdges_stack_head (show K ≠ 0 by omega)).2.1
    have hrange := isChain_range_flatMap (fun k ↦ if k < K then swNode k swB else t2Node) swP2 K
      fun k hk ↦ by
        obtain ⟨h1, h2, h3⟩ := hsw2 k hk
        exact ⟨h1, by simpa [hk] using h2, h3⟩
    have hmid_lst : ∀ u, u ∈ ((List.range K).flatMap swP2).getLast? → E u t2Node := by
      intro u hu
      simpa using hrange.2.2 u hu
    have htail : ((List.range K).flatMap swP2 ++ [t2Node]).IsChain E :=
      List.isChain_append.mpr ⟨hrange.1, List.IsChain.singleton _, fun u hu v hv ↦ by
        simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hv
        exact hv ▸ hmid_lst u hu⟩
    refine List.isChain_cons.mpr ⟨fun b hb ↦ ?_, htail⟩
    rcases hrange.2.1 with hK0 | hhd
    · simp only [hK0, List.range_zero, List.flatMap_nil, List.nil_append, List.head?_singleton,
        Option.mem_def, Option.some.injEq] at hb
      subst hb
      exact mem_bfpEdges_stack_nil hK0
    · have hne : (List.range K).flatMap swP2 ≠ [] := by intro h; simp [h] at hhd
      have hKpos : 0 < K := by
        by_contra h; have : K = 0 := by omega
        simp [this] at hne
      rw [List.head?_append_of_ne_nil _ hne, hhd] at hb
      simp only [hKpos, ↓reduceIte, Option.mem_def, Option.some.injEq] at hb
      subst hb
      exact (mem_bfpEdges_stack_head (show K ≠ 0 by omega)).1
  -- 2. `IsChain` for `Vseg`, `Cseg`, `Sseg`, and `P₁`
  have hVseg : Vseg.IsChain E ∧ Vseg.head? = some (varNode 0) ∧
      Vseg.getLast? = some (varNode N) := by
    have hstep : ∀ i < N, (varSeg i).IsChain E ∧ (varSeg i).head? = some (varNode i) ∧
        ∀ u, u ∈ (varSeg i).getLast? → E u (varNode (i + 1)) := by
      intro i hi
      set ks := varOccs φ i (dir i)
      have hch_all : ∀ e ∈ chainArcs (varNode i) (varNode (i + 1)) ks, E e.1 e.2 :=
        fun e he ↦ hmem_var i hi (dir i) e he
      have hwing : ∀ k ∈ ks, ([swNode k swLin, swNode k swY2, swNode k swY,
        swNode k swLout]).IsChain E :=
        fun k hk ↦
          have hklt : k < K := (mem_varOccs_iff.mp hk).1
          List.IsChain.cons_cons (hmem_sw k hklt _ (by simp [mem_switchArcs_iff]))
            (List.IsChain.cons_cons (hmem_sw k hklt _ (by simp [mem_switchArcs_iff]))
              (List.IsChain.cons_cons (hmem_sw k hklt _ (by simp [mem_switchArcs_iff]))
                (List.IsChain.singleton _)))
      refine ⟨?_, rfl, ?_⟩
      · cases hks : ks with
        | nil =>
          dsimp only [varSeg]
          rw [show varOccs φ i (dir i) = [] from hks]
          exact List.IsChain.singleton _
        | cons k₀ rest =>
          have hfm_ne : ∀ m : List ℕ, m ≠ [] →
              (m.flatMap fun k ↦ [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]) ≠
                [] := by
            intro m hm; cases m with | nil => exact absurd rfl hm | cons _ _ => simp
          have hlink : ∀ m : List ℕ,
              (∀ k ∈ m, ([swNode k swLin, swNode k swY2, swNode k swY,
                swNode k swLout]).IsChain E) →
              (∀ j, j + 1 < m.length →
                E (swNode (m.getD j 0) swLout) (swNode (m.getD (j + 1) 0) swLin)) →
              (m.flatMap fun k ↦
                [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]).IsChain E ∧
              (m ≠ [] → (m.flatMap fun k ↦
                [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]).head? =
                some (swNode (m.headD 0) swLin)) ∧
              (m ≠ [] → (m.flatMap fun k ↦
                [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]).getLast? =
                some (swNode (m.getD (m.length - 1) 0) swLout)) := by
            intro m
            induction m with
            | nil => intro _ _; exact ⟨List.IsChain.nil, fun h ↦ absurd rfl h, fun h ↦ absurd rfl h⟩
            | cons a l ih =>
              intro hw hcon
              cases l with
              | nil =>
                refine ⟨by simpa using hw a List.mem_cons_self, fun _ ↦ rfl, fun _ ↦ rfl⟩
              | cons b l' =>
                obtain ⟨ih_ch, ih_hd, ih_lst⟩ := ih (fun k hk ↦ hw k (List.mem_cons_of_mem _ hk))
                  fun j hj ↦ by
                    have := hcon (j + 1) (by simp only [List.length_cons] at hj ⊢; omega)
                    simpa [List.getD_cons_succ] using this
                have hne' : (b :: l') ≠ [] := List.cons_ne_nil _ _
                refine ⟨?_, fun _ ↦ rfl, fun _ ↦ ?_⟩
                · rw [List.flatMap_cons]
                  refine List.isChain_append.mpr ⟨hw a List.mem_cons_self, ih_ch,
                    fun u hu v hv ↦ ?_⟩
                  have hu_eq : u = swNode a swLout := by simpa [eq_comm] using hu
                  rw [ih_hd hne'] at hv
                  have hv_eq : v = swNode b swLin := by simpa [eq_comm] using hv
                  subst hu_eq; subst hv_eq
                  simpa using hcon 0 (by simp)
                · rw [List.flatMap_cons, List.getLast?_append_of_ne_nil _ (hfm_ne _ hne'),
                    ih_lst hne']
                  simp
          obtain ⟨hfm_ch, hfm_hd, _⟩ := hlink (k₀ :: rest) (fun k hk ↦ hwing k (hks ▸ hk))
            fun j hj ↦ hch_all _ (by
              rw [hks]
              exact mem_chainArcs_cons_iff.mpr (Or.inr (Or.inl ⟨j, by omega, rfl, rfl⟩)))
          dsimp only [varSeg]
          rw [show varOccs φ i (dir i) = k₀ :: rest from hks]
          refine List.isChain_cons.mpr ⟨fun b hb ↦ ?_, hfm_ch⟩
          rw [hfm_hd (List.cons_ne_nil _ _)] at hb
          simp only [Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact hch_all (varNode i, swNode k₀ swLin)
            (by rw [hks]; exact mem_chainArcs_cons_iff.mpr (Or.inl ⟨rfl, rfl⟩))
      · intro u hu
        cases hks : ks with
        | nil =>
          have hu_eq : u = varNode i := by simpa [varSeg, ks, hks, eq_comm] using hu
          subst hu_eq
          exact hch_all (varNode i, varNode (i + 1)) (by rw [hks]; exact mem_chainArcs_nil _ _)
        | cons k₀ rest =>
          have hfm_lst : ∀ m : List ℕ, m ≠ [] →
              (m.flatMap fun k ↦
                [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]).getLast? =
              some (swNode (m.getD (m.length - 1) 0) swLout) := by
            intro m
            induction m with
            | nil => intro h; exact absurd rfl h
            | cons a l ih =>
              intro _
              cases l with
              | nil => rfl
              | cons b l' =>
                have hne' : (b :: l') ≠ [] := List.cons_ne_nil _ _
                have hfm_ne : (List.flatMap (fun k ↦
                    [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]) (b :: l')) ≠
                      [] := by
                  simp
                rw [List.flatMap_cons, List.getLast?_append_of_ne_nil _ hfm_ne, ih hne']
                simp
          have hne : (k₀ :: rest) ≠ [] := List.cons_ne_nil _ _
          have hfm_ne : (List.flatMap (fun k ↦
              [swNode k swLin, swNode k swY2, swNode k swY, swNode k swLout]) (k₀ :: rest)) ≠
                [] := by
            simp
          have hu_eq : u = swNode ((k₀ :: rest).getD ((k₀ :: rest).length - 1) 0) swLout := by
            dsimp only [varSeg] at hu
            rw [show varOccs φ i (dir i) = k₀ :: rest from hks,
              List.getLast?_cons_of_ne_nil hfm_ne, hfm_lst _ hne] at hu
            simpa [eq_comm] using hu
          subst hu_eq
          exact hch_all (swNode ((k₀ :: rest).getD ((k₀ :: rest).length - 1) 0) swLout,
              varNode (i + 1))
            (by rw [hks]; exact mem_chainArcs_cons_iff.mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    have hr := isChain_range_flatMap varNode varSeg N hstep
    refine ⟨List.isChain_append.mpr ⟨hr.1, List.IsChain.singleton _, fun u hu v hv ↦ by
      simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hv
      exact hv ▸ hr.2.2 u hu⟩, ?_, by simp [Vseg]⟩
    rcases hr.2.1 with hN0 | hhd
    · simp [Vseg, hN0]
    · have hne : (List.range N).flatMap varSeg ≠ [] := by intro h; simp [h] at hhd
      rw [List.head?_append_of_ne_nil _ hne, hhd]
  have hCseg : Cseg.IsChain E ∧ Cseg.head? = some (clauseNode 0) ∧
      Cseg.getLast? = some (clauseNode M) := by
    have hstep : ∀ j < M, (clauseSeg j).IsChain E ∧ (clauseSeg j).head? = some (clauseNode j) ∧
        ∀ u, u ∈ (clauseSeg j).getLast? → E u (clauseNode (j + 1)) := by
      intro j hj
      obtain ⟨hpk_lt, hpk_j, _⟩ := hpick j hj
      refine ⟨?_, rfl, ?_⟩
      · have hcl1 := (hmem_cl (pick j) hpk_lt).1
        rw [hpk_j] at hcl1
        exact List.IsChain.cons_cons hcl1
          (List.IsChain.cons_cons (hmem_sw _ hpk_lt _ (by simp [mem_switchArcs_iff]))
            (List.IsChain.cons_cons (hmem_sw _ hpk_lt _ (by simp [mem_switchArcs_iff]))
              (List.IsChain.cons_cons (hmem_sw _ hpk_lt _ (by simp [mem_switchArcs_iff]))
                (List.IsChain.singleton _))))
      · intro u hu
        have hu_eq : u = swNode (pick j) swRout := by simpa [clauseSeg, eq_comm] using hu
        subst hu_eq
        have hcl2 := (hmem_cl (pick j) hpk_lt).2
        rw [hpk_j] at hcl2
        exact hcl2
    have hr := isChain_range_flatMap clauseNode clauseSeg M hstep
    refine ⟨List.isChain_append.mpr ⟨hr.1, List.IsChain.singleton _, fun u hu v hv ↦ by
      simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hv
      exact hv ▸ hr.2.2 u hu⟩, ?_, by simp [Cseg]⟩
    rcases hr.2.1 with hM0 | hhd
    · simp [Cseg, hM0]
    · have hne : (List.range M).flatMap clauseSeg ≠ [] := by intro h; simp [h] at hhd
      rw [List.head?_append_of_ne_nil _ hne, hhd]
  have hSseg : ∀ n ≤ K,
      ((List.range n).reverse.flatMap swP1).IsChain E ∧
      (n = 0 ∨ ((List.range n).reverse.flatMap swP1).head? = some (swNode (n - 1) swC)) ∧
      (n = 0 ∨ ((List.range n).reverse.flatMap swP1).getLast? = some (swNode 0 swA)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨List.IsChain.nil, Or.inl rfl, Or.inl rfl⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih_ch, ih_hd, ih_lst⟩ := ih (by omega)
      have hsw1 : (swP1 n).IsChain E := by
        simp only [swP1]; split_ifs <;>
          exact List.IsChain.cons_cons (hmem_sw n (by omega) _ (by simp [mem_switchArcs_iff]))
            (List.IsChain.cons_cons (hmem_sw n (by omega) _ (by simp [mem_switchArcs_iff]))
              (List.IsChain.cons_cons (hmem_sw n (by omega) _ (by simp [mem_switchArcs_iff]))
                (List.IsChain.singleton _)))
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.flatMap_cons]
      have hne_sw1 : swP1 n ≠ [] := by simp only [swP1]; split_ifs <;> simp
      refine ⟨List.isChain_append.mpr ⟨hsw1, ih_ch, fun u hu v hv ↦ ?_⟩, Or.inr ?_, Or.inr ?_⟩
      · rcases ih_hd with rfl | hhd
        · simp at hv
        · have hu_eq : u = swNode n swA := by
            simp only [swP1] at hu; split_ifs at hu <;> simpa [eq_comm] using hu
          rw [hhd] at hv
          have hv_eq : v = swNode (n - 1) swC := by simpa [eq_comm] using hv
          subst hu_eq; subst hv_eq
          have hnk : n - 1 + 1 = n := by
            have hn0 : n ≠ 0 := by intro h; simp [h] at hhd
            omega
          have hmid := (mem_bfpEdges_stack_mid (φ := φ) (k := n - 1)
            (show n - 1 + 1 < K by omega)).2
          rwa [hnk] at hmid
      · rw [List.head?_append_of_ne_nil _ hne_sw1]
        simp only [swP1, Nat.add_sub_cancel]; split_ifs <;> rfl
      · rcases ih_lst with rfl | hlst
        · simp only [List.range_zero, List.reverse_nil, List.flatMap_nil, List.append_nil, swP1]
          split_ifs <;> rfl
        · have hne_rest : (List.range n).reverse.flatMap swP1 ≠ [] := by
            intro h; simp [h] at hlst
          rw [List.getLast?_append_of_ne_nil _ hne_rest, hlst]
  have hP₁_ch : P₁.IsChain E := by
    have hV_ne : Vseg ≠ [] := by simp [Vseg]
    have hC_ne : Cseg ≠ [] := by simp [Cseg]
    have hSt1 : (Sseg ++ [t1Node]).IsChain E ∧
        (Sseg ++ [t1Node]).head? = some (if K = 0 then t1Node else swNode (K - 1) swC) := by
      obtain ⟨hS_ch, hS_hd, hS_lst⟩ := hSseg K le_rfl
      refine ⟨List.isChain_append.mpr ⟨hS_ch, List.IsChain.singleton _, fun u hu v hv ↦ ?_⟩, ?_⟩
      · rcases hS_lst with hK0 | hlst
        · simp [Sseg, hK0] at hu
        · rw [hlst] at hu
          have hu_eq : u = swNode 0 swA := by simpa [eq_comm] using hu
          have hv_eq : v = t1Node := by simpa [eq_comm] using hv
          subst hu_eq; subst hv_eq
          have hK0 : K ≠ 0 := by intro h; simp [h] at hlst
          exact (mem_bfpEdges_stack_head hK0).2.2
      · rcases hS_hd with hK0 | hhd
        · simp [Sseg, hK0]
        · have hne : Sseg ≠ [] := by intro h; dsimp only [Sseg] at h; rw [h] at hhd; simp at hhd
          have hK0 : K ≠ 0 := by intro h; simp [Sseg, h] at hne
          rw [List.head?_append_of_ne_nil _ hne, hhd]; simp [hK0]
    have hCSt1 : (Cseg ++ (Sseg ++ [t1Node])).IsChain E := by
      refine List.isChain_append.mpr ⟨hCseg.1, hSt1.1, fun u hu v hv ↦ ?_⟩
      rw [hCseg.2.2] at hu; rw [hSt1.2] at hv
      have hu_eq : u = clauseNode M := by simpa [eq_comm] using hu
      have hv_eq : v = if K = 0 then t1Node else swNode (K - 1) swC := by
        simpa [eq_comm] using hv
      subst hu_eq; subst hv_eq
      exact (mem_bfpEdges_terminals φ).2.2.1
    have hVCSt1 : (Vseg ++ (Cseg ++ (Sseg ++ [t1Node]))).IsChain E := by
      refine List.isChain_append.mpr ⟨hVseg.1, hCSt1, fun u hu v hv ↦ ?_⟩
      rw [hVseg.2.2] at hu
      rw [List.head?_append_of_ne_nil _ hC_ne, hCseg.2.1] at hv
      have hu_eq : u = varNode N := by simpa [eq_comm] using hu
      have hv_eq : v = clauseNode 0 := by simpa [eq_comm] using hv
      subst hu_eq; subst hv_eq
      exact (mem_bfpEdges_terminals φ).2.1
    have hbody_eq : Vseg ++ Cseg ++ Sseg ++ [t1Node] = Vseg ++ (Cseg ++ (Sseg ++ [t1Node])) := by
      simp [List.append_assoc]
    rw [show P₁ = s1Node :: (Vseg ++ (Cseg ++ (Sseg ++ [t1Node]))) by rw [← hbody_eq]]
    refine List.isChain_cons.mpr ⟨fun b hb ↦ ?_, hVCSt1⟩
    rw [List.head?_append_of_ne_nil _ hV_ne, hVseg.2.1] at hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact (mem_bfpEdges_terminals φ).1
  -- 3. Membership in `bfpVertices φ`
  have hmem_varNode : ∀ i ≤ N, varNode i ∈ bfpVertices φ := fun _ hi ↦
    mem_bfpVertices_varNode hi
  have hmem_clauseNode : ∀ j ≤ M, clauseNode j ∈ bfpVertices φ := fun _ hj ↦
    mem_bfpVertices_clauseNode hj
  have hmem_swNode : ∀ k < K, ∀ r < 14, swNode k r ∈ bfpVertices φ := fun _ hk _ hr ↦
    mem_bfpVertices_swNode hk hr
  have hmem_term : s1Node ∈ bfpVertices φ ∧ t1Node ∈ bfpVertices φ ∧
      s2Node ∈ bfpVertices φ ∧ t2Node ∈ bfpVertices φ :=
    mem_bfpVertices_term φ
  -- 4. Node classification for `P₁` and `P₂` (gives `Nodup`, `∈ bfpVertices`, and disjointness!)
  have hvarSeg_mem : ∀ i < N, ∀ v ∈ varSeg i,
      v = varNode i ∨ ∃ k ∈ varOccs φ i (dir i),
        k < K ∧ isTrue k = false ∧
          (v = swNode k swLin ∨ v = swNode k swY2 ∨ v = swNode k swY ∨ v = swNode k swLout) := by
    intro i _ v hv
    simp only [varSeg, List.mem_cons, List.mem_flatMap] at hv
    rcases hv with rfl | ⟨k, hk, hvk⟩
    · exact Or.inl rfl
    · have hkm := mem_varOccs_iff.mp hk
      have hfalse : isTrue k = false := by
        simp only [isTrue, lits, decide_eq_false_iff_not, hkm.2.1]
        exact fun h ↦ hkm.2.2 h.symm
      exact Or.inr ⟨k, hk, hkm.1, hfalse, by simpa using hvk⟩
  have hclauseSeg_mem : ∀ j < M, ∀ v ∈ clauseSeg j,
      v = clauseNode j ∨ (v = swNode (pick j) swRin ∨ v = swNode (pick j) swX2 ∨
        v = swNode (pick j) swX ∨ v = swNode (pick j) swRout) := by
    intro j _ v hv
    simp only [clauseSeg, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h
  have hswP1_mem : ∀ k < K, ∀ v ∈ swP1 k,
      (isTrue k = true ∧
        (v = swNode k swC ∨ v = swNode k swY ∨ v = swNode k swV ∨ v = swNode k swA)) ∨
      (isTrue k = false ∧
        (v = swNode k swC ∨ v = swNode k swX ∨ v = swNode k swU ∨ v = swNode k swA)) := by
    intro k _ v hv
    simp only [swP1] at hv
    cases htk : isTrue k
    · simp only [htk, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hv
      exact Or.inr ⟨rfl, hv⟩
    · simp only [htk, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hv
      exact Or.inl ⟨rfl, hv⟩
  have hswP2_mem : ∀ k < K, ∀ v ∈ swP2 k,
      (isTrue k = true ∧
        (v = swNode k swB ∨ v = swNode k swU ∨ v = swNode k swY2 ∨ v = swNode k swD)) ∨
      (isTrue k = false ∧
        (v = swNode k swB ∨ v = swNode k swV ∨ v = swNode k swX2 ∨ v = swNode k swD)) := by
    intro k _ v hv
    simp only [swP2] at hv
    cases htk : isTrue k
    · simp only [htk, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hv
      exact Or.inr ⟨rfl, hv⟩
    · simp only [htk, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hv
      exact Or.inl ⟨rfl, hv⟩
  have hP₁_V : ∀ v ∈ P₁, v ∈ bfpVertices φ := by
    intro v hv
    simp only [P₁, Vseg, Cseg, Sseg, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | (((⟨i, hi, hvi⟩ | rfl) | (⟨j, hj, hvj⟩ | rfl)) | ⟨k, hk, hvk⟩) | rfl
    · exact hmem_term.1
    · rcases hvarSeg_mem i hi v hvi with rfl | ⟨k, _, hk, _, h | h | h | h⟩
      · exact hmem_varNode i (le_of_lt hi)
      all_goals (subst h; exact hmem_swNode k hk _ (by decide))
    · exact hmem_varNode N le_rfl
    · rcases hclauseSeg_mem j hj v hvj with rfl | (h | h | h | h)
      · exact hmem_clauseNode j (le_of_lt hj)
      all_goals (subst h; exact hmem_swNode (pick j) (hpick j hj).1 _ (by decide))
    · exact hmem_clauseNode M le_rfl
    · rcases hswP1_mem k hk v hvk with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;> subst h <;>
        exact hmem_swNode k hk _ (by decide)
    · exact hmem_term.2.1
  have hP₂_V : ∀ v ∈ P₂, v ∈ bfpVertices φ := by
    intro v hv
    simp only [P₂, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | ⟨k, hk, hvk⟩ | rfl
    · exact hmem_term.2.2.1
    · rcases hswP2_mem k hk v hvk with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;> subst h <;>
        exact hmem_swNode k hk _ (by decide)
    · exact hmem_term.2.2.2
  have hP₁_nd : P₁.Nodup := by
    have hV_nd : ((List.range N).flatMap varSeg).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun i hi ↦ ?_, ?_⟩
      · have hi' : i < N := List.mem_range.mp hi
        refine List.nodup_cons.mpr ⟨?_, ?_⟩
        · intro hmem
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hmem
          obtain ⟨k, _, h | h | h | h⟩ := hmem <;> exact varNode_ne_swNode _ _ _ h
        · rw [List.nodup_flatMap]
          refine ⟨fun k _ ↦ nodup_swNode4 k (by decide) (by decide), ?_⟩
          refine (List.nodup_range.filter _).pairwise_of_forall_ne fun k₁ _ k₂ _ hne v hv₁ hv₂ ↦ ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv₁ hv₂
          exact hne (swNode_k_eq_of_mem4 (by decide) (by decide) hv₁ hv₂)
      · refine List.nodup_range.pairwise_of_forall_ne fun i₁ hi₁ i₂ hi₂ hne v hv₁ hv₂ ↦ ?_
        have hi₁' := List.mem_range.mp hi₁
        have hi₂' := List.mem_range.mp hi₂
        rcases hvarSeg_mem i₁ hi₁' v hv₁ with rfl | ⟨k₁, hk₁, _, _, h1⟩ <;>
          rcases hvarSeg_mem i₂ hi₂' _ hv₂ with h2 | ⟨k₂, hk₂, _, _, h2⟩
        · exact hne (varNode_inj h2)
        · rcases h2 with h | h | h | h <;> exact varNode_ne_swNode _ _ _ h
        · rcases h1 with rfl | rfl | rfl | rfl <;> exact varNode_ne_swNode _ _ _ h2.symm
        · have hk_eq : k₁ = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
          subst hk_eq
          exact hne ((mem_varOccs_iff.mp hk₁).2.1.symm.trans (mem_varOccs_iff.mp hk₂).2.1)
    have hC_nd : ((List.range M).flatMap clauseSeg).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun j _ ↦ ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, nodup_swNode4 (pick j) (by decide) (by decide)⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h | h) <;> exact clauseNode_ne_swNode _ _ _ h
      · refine List.nodup_range.pairwise_of_forall_ne fun j₁ hj₁ j₂ hj₂ hne v hv₁ hv₂ ↦ ?_
        have hj₁' := List.mem_range.mp hj₁
        have hj₂' := List.mem_range.mp hj₂
        rcases hclauseSeg_mem j₁ hj₁' v hv₁ with rfl | h1 <;>
          rcases hclauseSeg_mem j₂ hj₂' _ hv₂ with h2 | h2
        · exact hne (clauseNode_inj h2)
        · rcases h2 with h | h | h | h <;> exact clauseNode_ne_swNode _ _ _ h
        · rcases h1 with rfl | rfl | rfl | rfl <;> exact clauseNode_ne_swNode _ _ _ h2.symm
        · have hk_eq : pick j₁ = pick j₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
          exact hne ((hpick j₁ hj₁').2.1.symm.trans (by rw [hk_eq]; exact (hpick j₂ hj₂').2.1))
    have hS_nd : Sseg.Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun k _ ↦ by
        simp only [swP1]; split_ifs <;> exact nodup_swNode4 k (by decide) (by decide), ?_⟩
      refine (List.nodup_reverse.mpr List.nodup_range).pairwise_of_forall_ne
        fun k₁ hk₁ k₂ hk₂ hne v hv₁ hv₂ ↦ ?_
      have hk₁' := List.mem_range.mp (List.mem_reverse.mp hk₁)
      have hk₂' := List.mem_range.mp (List.mem_reverse.mp hk₂)
      rcases hswP1_mem k₁ hk₁' v hv₁ with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
        rcases hswP1_mem k₂ hk₂' v hv₂ with ⟨_, h2⟩ | ⟨_, h2⟩ <;>
        exact hne (swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2)
    have hVseg_nd : Vseg.Nodup := by
      refine List.nodup_append.mpr ⟨hV_nd, List.nodup_singleton _, fun v hv w hw hvw ↦ ?_⟩
      rw [List.mem_singleton] at hw; subst hw; subst hvw
      obtain ⟨i, hi, hvi⟩ := List.mem_flatMap.mp hv
      have hi' := List.mem_range.mp hi
      rcases hvarSeg_mem i hi' _ hvi with h | ⟨_, _, _, _, h | h | h | h⟩
      · have := varNode_inj h; omega
      all_goals exact varNode_ne_swNode _ _ _ h
    have hCseg_nd : Cseg.Nodup := by
      refine List.nodup_append.mpr ⟨hC_nd, List.nodup_singleton _, fun v hv w hw hvw ↦ ?_⟩
      rw [List.mem_singleton] at hw; subst hw; subst hvw
      obtain ⟨j, hj, hvj⟩ := List.mem_flatMap.mp hv
      have hj' := List.mem_range.mp hj
      rcases hclauseSeg_mem j hj' _ hvj with h | (h | h | h | h)
      · have := clauseNode_inj h; omega
      all_goals exact clauseNode_ne_swNode _ _ _ h
    have hVC_disj : ∀ v ∈ Vseg, v ∉ Cseg := by
      intro v hv hc
      simp only [Vseg, Cseg, List.mem_append, List.mem_flatMap, List.mem_range,
        List.mem_singleton] at hv hc
      have hv_class : (∃ i, v = varNode i) ∨
          (∃ k, isTrue k = false ∧
            (v = swNode k swLin ∨ v = swNode k swY2 ∨ v = swNode k swY ∨ v = swNode k swLout)) := by
        rcases hv with ⟨i, hi, hvi⟩ | rfl
        · rcases hvarSeg_mem i hi v hvi with rfl | ⟨k, _, _, hf, h⟩
          · exact Or.inl ⟨i, rfl⟩
          · exact Or.inr ⟨k, hf, h⟩
        · exact Or.inl ⟨N, rfl⟩
      have hc_class : (∃ j, v = clauseNode j) ∨
          (∃ k, isTrue k = true ∧
            (v = swNode k swRin ∨ v = swNode k swX2 ∨ v = swNode k swX ∨ v = swNode k swRout)) := by
        rcases hc with ⟨j, hj, hvj⟩ | rfl
        · rcases hclauseSeg_mem j hj v hvj with rfl | h
          · exact Or.inl ⟨j, rfl⟩
          · exact Or.inr ⟨pick j, (hpick j hj).2.2, h⟩
        · exact Or.inl ⟨M, rfl⟩
      rcases hv_class with ⟨i, rfl⟩ | ⟨k₁, hf, h1⟩ <;> rcases hc_class with ⟨j, h⟩ | ⟨k₂, ht, h2⟩
      · exact varNode_ne_clauseNode i j h
      · rcases h2 with h | h | h | h <;> exact varNode_ne_swNode _ _ _ h
      · rcases h1 with rfl | rfl | rfl | rfl <;> exact clauseNode_ne_swNode _ _ _ h.symm
      · have hk_eq : k₁ = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
        subst hk_eq; simp [hf] at ht
    have hVC_S_disj : ∀ v ∈ Vseg ++ Cseg, v ∉ Sseg := by
      intro v hvc hs
      obtain ⟨k₂, hk₂, hvk₂⟩ := List.mem_flatMap.mp hs
      have hk₂' := List.mem_range.mp (List.mem_reverse.mp hk₂)
      rcases List.mem_append.mp hvc with hv | hc
      · simp only [Vseg, List.mem_append, List.mem_flatMap, List.mem_range,
          List.mem_singleton] at hv
        rcases hv with ⟨i, hi, hvi⟩ | rfl
        · rcases hvarSeg_mem i hi v hvi with rfl | ⟨k₁, _, _, hf, h1⟩
          · rcases hswP1_mem k₂ hk₂' _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
              exact varNode_ne_swNode _ _ _ h
          · rcases hswP1_mem k₂ hk₂' v hvk₂ with ⟨ht, h2⟩ | ⟨_, h2⟩
            · have hk_eq : k₁ = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
              subst hk_eq; simp [hf] at ht
            · exact swNode_disj4 (by decide) (by decide) (by decide) h1 h2
        · rcases hswP1_mem k₂ hk₂' _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
            exact varNode_ne_swNode _ _ _ h
      · simp only [Cseg, List.mem_append, List.mem_flatMap, List.mem_range,
          List.mem_singleton] at hc
        rcases hc with ⟨j, hj, hvj⟩ | rfl
        · rcases hclauseSeg_mem j hj v hvj with rfl | h1
          · rcases hswP1_mem k₂ hk₂' _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
              exact clauseNode_ne_swNode _ _ _ h
          · rcases hswP1_mem k₂ hk₂' v hvk₂ with ⟨_, h2⟩ | ⟨hf, h2⟩
            · exact swNode_disj4 (by decide) (by decide) (by decide) h1 h2
            · have hk_eq : pick j = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
              subst hk_eq; have := (hpick j hj).2.2; simp [hf] at this
        · rcases hswP1_mem k₂ hk₂' _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
            exact clauseNode_ne_swNode _ _ _ h
    have hbody_nd : (Vseg ++ Cseg ++ Sseg).Nodup := by
      refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hVseg_nd, hCseg_nd,
        fun v hv w hw hvw ↦ hVC_disj v hv (hvw ▸ hw)⟩, hS_nd,
        fun v hv w hw hvw ↦ hVC_S_disj v hv (hvw ▸ hw)⟩
    have hno_term : ∀ t ∈ [s1Node, t1Node, s2Node, t2Node], t ∉ Vseg ++ Cseg ++ Sseg := by
      intro t ht hmem
      have hts : t = s1Node ∨ t = t1Node ∨ t = s2Node ∨ t = t2Node := by simpa using ht
      have hne : ∀ x, (∃ i, x = varNode i) ∨ (∃ j, x = clauseNode j) ∨
          (∃ k r, x = swNode k r) → x ≠ t := by
        rintro x (⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨k, r, rfl⟩)
        · have := varNode_ne_term i; rcases hts with rfl | rfl | rfl | rfl <;> tauto
        · have := clauseNode_ne_term j; rcases hts with rfl | rfl | rfl | rfl <;> tauto
        · have := swNode_ne_term k r; rcases hts with rfl | rfl | rfl | rfl <;> tauto
      simp only [Vseg, Cseg, Sseg, List.mem_append, List.mem_flatMap, List.mem_reverse,
        List.mem_range, List.mem_singleton] at hmem
      rcases hmem with ((⟨i, hi, hvi⟩ | h) | (⟨j, hj, hvj⟩ | h)) | ⟨k, hk, hvk⟩
      · rcases hvarSeg_mem i hi t hvi with h | ⟨k, _, _, _, h | h | h | h⟩
        · exact hne t (Or.inl ⟨i, h⟩) rfl
        all_goals exact hne t (Or.inr (Or.inr ⟨k, _, h⟩)) rfl
      · exact hne t (Or.inl ⟨N, h⟩) rfl
      · rcases hclauseSeg_mem j hj t hvj with h | (h | h | h | h)
        · exact hne t (Or.inr (Or.inl ⟨j, h⟩)) rfl
        all_goals exact hne t (Or.inr (Or.inr ⟨pick j, _, h⟩)) rfl
      · exact hne t (Or.inr (Or.inl ⟨M, h⟩)) rfl
      · rcases hswP1_mem k hk t hvk with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
          exact hne t (Or.inr (Or.inr ⟨k, _, h⟩)) rfl
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hbody_nd, List.nodup_singleton _,
      fun v hv w hw hvw ↦ by
        rw [List.mem_singleton] at hw; subst hw; subst hvw
        exact hno_term t1Node (by simp) hv⟩⟩
    intro hs1
    rcases List.mem_append.mp hs1 with h | h
    · exact hno_term s1Node (by simp) h
    · simp at h
  have hP₂_nd : P₂.Nodup := by
    have hmid_nd : ((List.range K).flatMap swP2).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun k _ ↦ by
        simp only [swP2]; split_ifs <;> exact nodup_swNode4 k (by decide) (by decide), ?_⟩
      refine List.nodup_range.pairwise_of_forall_ne fun k₁ hk₁ k₂ hk₂ hne v hv₁ hv₂ ↦ ?_
      rcases hswP2_mem k₁ (List.mem_range.mp hk₁) v hv₁ with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
        rcases hswP2_mem k₂ (List.mem_range.mp hk₂) v hv₂ with ⟨_, h2⟩ | ⟨_, h2⟩ <;>
        exact hne (swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2)
    have hno_t : ∀ t ∈ [s1Node, t1Node, s2Node, t2Node], t ∉ (List.range K).flatMap swP2 := by
      intro t ht hm
      obtain ⟨k, hk, hvk⟩ := List.mem_flatMap.mp hm
      have hts : t = s1Node ∨ t = t1Node ∨ t = s2Node ∨ t = t2Node := by simpa using ht
      have hsw_ne : ∀ r, swNode k r ≠ t := fun r ↦ by
        have := swNode_ne_term k r; rcases hts with rfl | rfl | rfl | rfl <;> tauto
      rcases hswP2_mem k (List.mem_range.mp hk) t hvk with ⟨_, h | h | h | h⟩ | ⟨_,
        h | h | h | h⟩ <;>
        exact hsw_ne _ h.symm
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hmid_nd, List.nodup_singleton _,
      fun v hv w hw hvw ↦ by
        rw [List.mem_singleton] at hw; subst hw; subst hvw
        exact hno_t t2Node (by simp) hv⟩⟩
    intro hs2
    rcases List.mem_append.mp hs2 with h | h
    · exact hno_t s2Node (by simp) h
    · simp at h
  have hdisj : ∀ v, v ∈ P₁ → v ∈ P₂ → False := by
    intro v hv₁ hv₂
    simp only [P₂, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at hv₂
    have hv₂_sw : ∃ k₂ < K, v ∈ swP2 k₂ := by
      rcases hv₂ with rfl | ⟨k₂, hk₂, hvk₂⟩ | rfl
      · exfalso
        simp only [P₁, Vseg, Cseg, Sseg, List.mem_cons, List.mem_append, List.mem_flatMap,
          List.mem_reverse, List.mem_range, List.not_mem_nil, or_false] at hv₁
        rcases hv₁ with h | (((⟨i, hi, hvi⟩ | h) | (⟨j, hj, hvj⟩ | h)) | ⟨k, hk, hvk⟩) | h
        · exact absurd h (by decide)
        · rcases hvarSeg_mem i hi _ hvi with h' | ⟨k, _, _, _, h' | h' | h' | h'⟩
          · exact (varNode_ne_term i).2.2.1 h'.symm
          all_goals exact (swNode_ne_term k _).2.2.1 h'.symm
        · exact (varNode_ne_term N).2.2.1 h.symm
        · rcases hclauseSeg_mem j hj _ hvj with h' | (h' | h' | h' | h')
          · exact (clauseNode_ne_term j).2.2.1 h'.symm
          all_goals exact (swNode_ne_term (pick j) _).2.2.1 h'.symm
        · exact (clauseNode_ne_term M).2.2.1 h.symm
        · rcases hswP1_mem k hk _ hvk with ⟨_, h' | h' | h' | h'⟩ | ⟨_, h' | h' | h' | h'⟩ <;>
            exact (swNode_ne_term k _).2.2.1 h'.symm
        · exact absurd h (by decide)
      · exact ⟨k₂, hk₂, hvk₂⟩
      · exfalso
        simp only [P₁, Vseg, Cseg, Sseg, List.mem_cons, List.mem_append, List.mem_flatMap,
          List.mem_reverse, List.mem_range, List.not_mem_nil, or_false] at hv₁
        rcases hv₁ with h | (((⟨i, hi, hvi⟩ | h) | (⟨j, hj, hvj⟩ | h)) | ⟨k, hk, hvk⟩) | h
        · exact absurd h (by decide)
        · rcases hvarSeg_mem i hi _ hvi with h' | ⟨k, _, _, _, h' | h' | h' | h'⟩
          · exact (varNode_ne_term i).2.2.2 h'.symm
          all_goals exact (swNode_ne_term k _).2.2.2 h'.symm
        · exact (varNode_ne_term N).2.2.2 h.symm
        · rcases hclauseSeg_mem j hj _ hvj with h' | (h' | h' | h' | h')
          · exact (clauseNode_ne_term j).2.2.2 h'.symm
          all_goals exact (swNode_ne_term (pick j) _).2.2.2 h'.symm
        · exact (clauseNode_ne_term M).2.2.2 h.symm
        · rcases hswP1_mem k hk _ hvk with ⟨_, h' | h' | h' | h'⟩ | ⟨_, h' | h' | h' | h'⟩ <;>
            exact (swNode_ne_term k _).2.2.2 h'.symm
        · exact absurd h (by decide)
    obtain ⟨k₂, hk₂, hvk₂⟩ := hv₂_sw
    simp only [P₁, Vseg, Cseg, Sseg, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_reverse, List.mem_range, List.not_mem_nil, or_false] at hv₁
    rcases hv₁ with rfl | (((⟨i, hi, hvi⟩ | rfl) | (⟨j, hj, hvj⟩ | rfl)) | ⟨k₁, hk₁, hvk₁⟩) | rfl
    · rcases hswP2_mem k₂ hk₂ _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
        exact (swNode_ne_term k₂ _).1 h.symm
    · rcases hvarSeg_mem i hi v hvi with rfl | ⟨k₁, _, _, hf, h1⟩
      · rcases hswP2_mem k₂ hk₂ _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
          exact varNode_ne_swNode i k₂ _ h
      · rcases hswP2_mem k₂ hk₂ v hvk₂ with ⟨ht, h2⟩ | ⟨_, h2⟩
        · have hk_eq : k₁ = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
          subst hk_eq; simp [hf] at ht
        · exact swNode_disj4 (by decide) (by decide) (by decide) h1 h2
    · rcases hswP2_mem k₂ hk₂ _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
        exact varNode_ne_swNode N k₂ _ h
    · rcases hclauseSeg_mem j hj v hvj with rfl | h1
      · rcases hswP2_mem k₂ hk₂ _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
          exact clauseNode_ne_swNode j k₂ _ h
      · rcases hswP2_mem k₂ hk₂ v hvk₂ with ⟨_, h2⟩ | ⟨hf, h2⟩
        · exact swNode_disj4 (by decide) (by decide) (by decide) h1 h2
        · have hk_eq : pick j = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
          subst hk_eq; have := (hpick j hj).2.2; simp [hf] at this
    · rcases hswP2_mem k₂ hk₂ _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
        exact clauseNode_ne_swNode M k₂ _ h
    · rcases hswP1_mem k₁ hk₁ v hvk₁ with ⟨ht1, h1⟩ | ⟨hf1, h1⟩ <;>
        rcases hswP2_mem k₂ hk₂ v hvk₂ with ⟨ht2, h2⟩ | ⟨hf2, h2⟩
      · exact swNode_disj4 (by decide) (by decide) (by decide) h1 h2
      · have hk_eq : k₁ = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
        subst hk_eq; simp [ht1] at hf2
      · have hk_eq : k₁ = k₂ := swNode_k_eq_of_mem4 (by decide) (by decide) h1 h2
        subst hk_eq; simp [hf1] at ht2
      · exact swNode_disj4 (by decide) (by decide) (by decide) h1 h2
    · rcases hswP2_mem k₂ hk₂ _ hvk₂ with ⟨_, h | h | h | h⟩ | ⟨_, h | h | h | h⟩ <;>
        exact (swNode_ne_term k₂ _).2.1 h.symm
  -- 5. Assemble `t1Node :: P₂` (`t1 → t2`) and `t2Node :: P₁` (`t2 → t1`) in `BFP`.
  have ht1_not_P₂ : t1Node ∉ P₂ := fun h ↦ by
    have ht1_P₁ : t1Node ∈ P₁ := by simp [P₁]
    exact hdisj t1Node ht1_P₁ h
  have ht2_not_P₁ : t2Node ∉ P₁ := fun h ↦ by
    have ht2_P₂ : t2Node ∈ P₂ := by simp [P₂]
    exact hdisj t2Node h ht2_P₂
  have h12 : E t1Node s2Node := (mem_bfpEdges_terminals φ).2.2.2.1
  have h21 : E t2Node s1Node := (mem_bfpEdges_terminals φ).2.2.2.2
  refine ⟨by rw [toBFP_source, toBFP_target]; decide, t1Node :: P₂, t2Node :: P₁, ?_, ?_, ?_⟩
  · refine ⟨List.nodup_cons.mpr ⟨ht1_not_P₂, hP₂_nd⟩, fun v hv ↦ ?_, rfl, ?_,
      List.IsChain.cons_cons h12 hP₂_ch⟩
    · rcases List.mem_cons.mp hv with rfl | h
      · exact hmem_term.2.1
      · exact hP₂_V v h
    · rw [toBFP_target]
      dsimp only [P₂]
      rw [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _),
        List.getLast?_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
        List.getLast?_concat]
  · refine ⟨List.nodup_cons.mpr ⟨ht2_not_P₁, hP₁_nd⟩, fun v hv ↦ ?_, rfl, ?_,
      List.IsChain.cons_cons h21 hP₁_ch⟩
    · rcases List.mem_cons.mp hv with rfl | h
      · exact hmem_term.2.2.2
      · exact hP₁_V v h
    · rw [toBFP_source]
      dsimp only [P₁]
      rw [List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _),
        List.getLast?_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
        List.getLast?_concat]
  · intro v hv1 hv2
    rcases List.mem_cons.mp hv1 with rfl | h1
    · exact Or.inl rfl
    · rcases List.mem_cons.mp hv2 with rfl | h2
      · exact Or.inr rfl
      · exact absurd h1 (fun h ↦ hdisj v h2 h)

/-- Correctness of the FHW reduction `toBFP`. -/
theorem toBFP_mem_iff (φ : CNF ℕ) : toBFP φ ∈ BFP ↔ φ ∈ SAT := by
  constructor
  · rintro ⟨_, p, q, hp, hq, hdisj⟩
    rcases hp with ⟨hp_nd, hp_V, hp_hd, hp_lst, hp_ch⟩
    rcases hq with ⟨hq_nd, hq_V, hq_hd, hq_lst, hq_ch⟩
    simp only [toBFP_source, toBFP_target] at hp_hd hp_lst hq_hd hq_lst hdisj
    cases p with
    | nil => simp at hp_hd
    | cons a p' =>
      have ha : a = t1Node := Option.some.inj hp_hd
      subst ha
      cases q with
      | nil => simp at hq_hd
      | cons b q' =>
        have hb : b = t2Node := Option.some.inj hq_hd
        subst hb
        cases p' with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hp_lst
          exact absurd hp_lst (by decide)
        | cons a2 p'' =>
          have ha2 : a2 = s2Node := out_t1Node (List.isChain_cons_cons.mp hp_ch).1
          subst ha2
          cases q' with
          | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hq_lst
            exact absurd hq_lst (by decide)
          | cons b2 q'' =>
            have hb2 : b2 = s1Node := out_t2Node (List.isChain_cons_cons.mp hq_ch).1
            subst hb2
            have hP₂ : IsDirPath (toBFP φ).graph s2Node t2Node (s2Node :: p'') :=
              ⟨(List.nodup_cons.mp hp_nd).2, fun v hv ↦ hp_V v (List.mem_cons_of_mem _ hv), rfl,
                by simpa using hp_lst, (List.isChain_cons_cons.mp hp_ch).2⟩
            have hP₁ : IsDirPath (toBFP φ).graph s1Node t1Node (s1Node :: q'') :=
              ⟨(List.nodup_cons.mp hq_nd).2, fun v hv ↦ hq_V v (List.mem_cons_of_mem _ hv), rfl,
                by simpa using hq_lst, (List.isChain_cons_cons.mp hq_ch).2⟩
            refine sound_of_paths hP₁ hP₂ fun v hv1 hv2 ↦ ?_
            rcases hdisj v (List.mem_cons_of_mem _ hv2) (List.mem_cons_of_mem _ hv1) with rfl | rfl
            · exact (List.nodup_cons.mp hp_nd).1 hv2
            · exact (List.nodup_cons.mp hq_nd).1 hv1
  · exact complete_of_sat

end BackAndForthPaths

/-- `SAT` reduces to `BFP` in polynomial time. -/
theorem polyTimeReducible_SAT_BFP :
    PolyTimeReducible encCNF encPathInstance SAT BFP :=
  ⟨BackAndForthPaths.toBFP, BackAndForthPaths.computableInPolyTime_toBFP,
    fun φ ↦ (BackAndForthPaths.toBFP_mem_iff φ).symm⟩

/-- `ThreeSAT` reduces to `BFP` in polynomial time. -/
theorem polyTimeReducible_ThreeSAT_BFP :
    PolyTimeReducible encCNF encPathInstance ThreeSAT BFP :=
  .of_guard (g := fun φ ↦ φ.all fun c ↦ decide (c.length ≤ 3)) (BackAndForthPaths.toBFP [[]])
    (by fun_prop) BackAndForthPaths.computableInPolyTime_toBFP
    (by simp [BackAndForthPaths.toBFP_mem_iff, mem_SAT, CNF.Satisfiable, CNF.eval, Clause.eval])
    fun φ ↦ by simp [ThreeSAT, BackAndForthPaths.toBFP_mem_iff, mem_SAT]

/-- Back-and-Forth Paths (`BFP`) is `NP`-complete. -/
theorem BFP_npComplete : NPComplete encPathInstance BFP :=
  ⟨BFP_mem_NP, CookLevin.SAT_npHard.trans polyTimeReducible_SAT_BFP⟩

/-- Non-degenerate witness for `BFP`: the 4-vertex directed cycle `0 → 1 → 2 → 3 → 0` belongs to
`BFP` with terminals `0` and `2`. -/
theorem witness_BFP :
    (⟨⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)]⟩, 0, 2⟩ : PathInstance) ∈ BFP := by
  refine ⟨by decide, [0, 1, 2], [2, 3, 0], ?_, ?_, ?_⟩
  · exact ⟨by decide, by decide, rfl, rfl, by decide⟩
  · exact ⟨by decide, by decide, rfl, rfl, by decide⟩
  · intro v hv1 hv2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv1 hv2
    dsimp only
    omega

end Cslib.Complexity
