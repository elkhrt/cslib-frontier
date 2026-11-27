/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Problems.RestrictedExactCoverDefs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Data.List.GetD

/-!
# NP-Completeness of Restricted Exact Cover by 3-Sets (RXC3)

This module proves that `CslibFrontier.Complexity.RXC3` and its scaled restriction
`CslibFrontier.Complexity.RXC3Scaled k N₀` (`1 ≤ k`) are `NP`-complete
under standard Lean axioms, building on the definitions and well-formedness lemmas in
`CslibFrontier.Computability.Complexity.Problems.RestrictedExactCoverDefs`.

## Main results

* `CslibFrontier.Complexity.RXC3_mem_NP`: `RXC3 ∈ NP encRXC3`.
* `CslibFrontier.Complexity.RXC3_npHard`: `NPHard encRXC3 RXC3`.
* `CslibFrontier.Complexity.RXC3_npComplete`: `NPComplete encRXC3 RXC3`.
* `CslibFrontier.Complexity.RXC3Scaled_npComplete`: `NPComplete encRXC3 (RXC3Scaled k N₀)` for
  `1 ≤ k`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

namespace RXC3

private theorem list_eq_one_of_length {l : List ℕ} (h : l.length = 1) :
    l = [l.getD 0 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all

private theorem list_eq_two_of_length {l : List ℕ} (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp_all

private theorem list_eq_three_of_length {l : List ℕ} (h : l.length = 3) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> simp_all

private theorem filter_mem_length_eq_sum (L : List (List ℕ)) (u : ℕ) :
    (L.filter (fun c => decide (u ∈ c))).length =
      (L.map fun c => if u ∈ c then 1 else 0).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h : u ∈ a <;> simp [h, ih, Nat.add_comm]

private theorem filter_pos_clause (τ : ℕ → Bool) (c : Clause ℕ) (hpc : ∀ l ∈ c, l.2 = true) :
    (c.filter (fun l => Literal.eval τ l)).map Prod.fst =
      (c.map Prod.fst).filter (fun v => τ v) := by
  induction c with
  | nil => simp
  | cons l ls ih =>
    have hl : l.2 = true := hpc l (List.mem_cons_self ..)
    have hls : ∀ l' ∈ ls, l'.2 = true := fun l' hl' => hpc l' (List.mem_cons_of_mem _ hl')
    have hlt : Literal.eval τ l = τ l.1 := by simp [Literal.eval, hl]
    simp only [List.filter_cons, List.map_cons, hlt]
    cases htv : τ l.1 <;> simp [ih hls]

private def selVarAux (_m base : ℕ) (occ : List ℕ) (τv : Bool) : List (List ℕ) :=
  if τv then
    if occ.length = 1 then
      let i0 := occ.getD 0 0
      [[3 * i0, base, base + 6], [3 * i0 + 1, base + 1, base + 7],
       [3 * i0 + 2, base + 2, base + 8],
       [base + 3, base + 4, base + 5], [base + 9, base + 10, base + 11]]
    else if occ.length = 2 then
      let i0 := occ.getD 0 0
      let i1 := occ.getD 1 0
      [[3 * i0, 3 * i1, base], [3 * i0 + 1, 3 * i1 + 1, base + 1],
       [3 * i0 + 2, 3 * i1 + 2, base + 2], [base + 3, base + 4, base + 5]]
    else if occ.length = 3 then
      let i0 := occ.getD 0 0
      let i1 := occ.getD 1 0
      let i2 := occ.getD 2 0
      [[3 * i0, 3 * i1, base], [3 * i2, base + 1, base + 2],
       [3 * i0 + 1, 3 * i1 + 1, base + 6], [3 * i2 + 1, base + 7, base + 8],
       [3 * i0 + 2, 3 * i1 + 2, base + 12], [3 * i2 + 2, base + 13, base + 14],
       [base + 3, base + 4, base + 5], [base + 9, base + 10, base + 11],
       [base + 15, base + 16, base + 17]]
    else []
  else
    if occ.length = 1 then
      [[base, base + 1, base + 2], [base + 3, base + 4, base + 5],
       [base + 6, base + 7, base + 8], [base + 9, base + 10, base + 11]]
    else if occ.length = 2 then
      [[base, base + 1, base + 2], [base + 3, base + 4, base + 5]]
    else if occ.length = 3 then
      [[base, base + 1, base + 2], [base + 3, base + 4, base + 5],
       [base + 6, base + 7, base + 8], [base + 9, base + 10, base + 11],
       [base + 12, base + 13, base + 14], [base + 15, base + 16, base + 17]]
    else []

private theorem selVar_clause_count (m base i r : ℕ) (occ : List ℕ) (τv : Bool)
    (hnd : occ.Nodup) (hlo : 1 ≤ occ.length) (hhi : occ.length ≤ 3)
    (hocc_lt : ∀ j ∈ occ, j < m) (hi : i < m) (hr : r < 3) (hbase : 3 * m ≤ base) :
    ((selVarAux m base occ τv).filter (fun c => decide (3 * i + r ∈ c))).length =
      if τv ∧ i ∈ occ then 1 else 0 := by
  unfold selVarAux
  cases τv
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, filter_mem_length_eq_sum]
    split_ifs <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.mem_cons,
        List.not_mem_nil, or_false] <;> grind
  · simp only [↓reduceIte, true_and, filter_mem_length_eq_sum]
    have hlen : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by omega
    rcases hlen with hl | hl | hl
    · have hget := list_eq_one_of_length hl
      have hi0 : occ.getD 0 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hmem : i ∈ occ ↔ i = occ.getD 0 0 := by nth_rw 1 [hget]; exact List.mem_singleton
      simp only [hl, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.mem_cons, List.not_mem_nil, or_false]
      grind
    · have hget := list_eq_two_of_length hl
      have hi0 : occ.getD 0 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hi1 : occ.getD 1 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hne01 : occ.getD 0 0 ≠ occ.getD 1 0 := by rw [hget] at hnd; simpa using hnd
      have hmem : i ∈ occ ↔ i = occ.getD 0 0 ∨ i = occ.getD 1 0 := by
        nth_rw 1 [hget]; rw [List.mem_cons, List.mem_singleton]
      simp only [hl, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.mem_cons, List.not_mem_nil, or_false]
      grind
    · have hget := list_eq_three_of_length hl
      have hi0 : occ.getD 0 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hi1 : occ.getD 1 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hi2 : occ.getD 2 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hne01 : occ.getD 0 0 ≠ occ.getD 1 0 := by
        rw [hget] at hnd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hnd; exact hnd.1.1
      have hne02 : occ.getD 0 0 ≠ occ.getD 2 0 := by
        rw [hget] at hnd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hnd; exact hnd.1.2
      have hne12 : occ.getD 1 0 ≠ occ.getD 2 0 := by
        rw [hget] at hnd; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hnd; exact hnd.2.1
      have hmem : i ∈ occ ↔ i = occ.getD 0 0 ∨ i = occ.getD 1 0 ∨ i = occ.getD 2 0 := by
        nth_rw 1 [hget]; rw [List.mem_cons, List.mem_cons, List.mem_singleton]
      simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.mem_cons, List.not_mem_nil,
        or_false]
      have h3i : 3 * i + 2 < base := by omega
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr3 with rfl | rfl | rfl <;> grind (splits := 16)

private theorem selVar_dummy_count (m base u : ℕ) (occ : List ℕ) (τv : Bool)
    (hlo : 1 ≤ occ.length) (hhi : occ.length ≤ 3)
    (hocc_lt : ∀ j ∈ occ, j < m) (hbase : 3 * m ≤ base)
    (hu_lo : base ≤ u) (hu_hi : u < base + 6 * gadgetCount occ.length) :
    ((selVarAux m base occ τv).filter (fun c => decide (u ∈ c))).length = 1 := by
  unfold selVarAux
  have hlen : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by omega
  cases τv
  · simp only [Bool.false_eq_true, ↓reduceIte, filter_mem_length_eq_sum]
    rcases hlen with hl | hl | hl
    · simp only [hl, gadgetCount, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.mem_cons, List.not_mem_nil, or_false] at hu_hi ⊢
      grind
    · simp only [hl, gadgetCount, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hu_hi ⊢
      grind
    · simp only [hl, gadgetCount, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
        ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu_hi ⊢
      grind
  · simp only [↓reduceIte, filter_mem_length_eq_sum]
    rcases hlen with hl | hl | hl
    · have hi0 : occ.getD 0 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      simp only [hl, gadgetCount, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.mem_cons, List.not_mem_nil, or_false] at hu_hi ⊢
      grind
    · have hi0 : occ.getD 0 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hi1 : occ.getD 1 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      simp only [hl, gadgetCount, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hu_hi ⊢
      grind
    · have hi0 : occ.getD 0 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hi1 : occ.getD 1 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have hi2 : occ.getD 2 0 < m := hocc_lt _ (getD_mem_of_lt (by omega))
      have h0 : 3 * occ.getD 0 0 + 2 < base := by omega
      have h1 : 3 * occ.getD 1 0 + 2 < base := by omega
      have h2 : 3 * occ.getD 2 0 + 2 < base := by omega
      simp only [hl, gadgetCount, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
        ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu_hi ⊢
      grind (splits := 16)

private theorem mem_of_oneSatisfiable {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) (h : φ.OneSatisfiable) :
    reduce φ ∈ RXC3 := by
  by_cases hne : φ.isEmpty = true
  · have hred0 : reduce φ = yesInstance := by simp [reduce, hs, hne]
    rw [hred0]; exact yesInstance_mem
  · simp only [Bool.not_eq_true] at hne
    refine ⟨reduce_isWellFormed hs hne, ?_⟩
    obtain ⟨τ, hτ⟩ := h
    rw [CNF.evalOne_eq_true_iff] at hτ
    have ⟨hexact, hpos, hcnt⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
    set vs := distinctVars φ with hvs_def
    set m := φ.length with hm_def
    set G := gadgetPrefix φ vs vs.length with hG_def
    have hred : reduce φ = ⟨m + 2 * G, (List.range vs.length).flatMap fun k =>
        varClauses m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0))⟩ := by
      simp [reduce, hs, hne, hvs_def, hm_def, hG_def]
    -- Define the selected clauses per variable k
    let selVar (k : ℕ) : List (List ℕ) :=
      selVarAux m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0)) (τ (vs.getD k 0))
    let selList := (List.range vs.length).flatMap selVar
    refine ⟨selList.toFinset, ?_, ?_⟩
    · -- Subset of (reduce φ).clauses
      rw [hred]
      intro c hc
      rw [List.mem_toFinset] at hc
      obtain ⟨k, hk, hck⟩ := List.mem_flatMap.mp hc
      refine List.mem_flatMap.mpr ⟨k, hk, ?_⟩
      dsimp only [selVar, selVarAux] at hck
      unfold varClauses choiceGadget
      split_ifs at hck ⊢ <;>
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hck ⊢ <;>
        tauto
    · -- Every u < 3 * (m + 2 * G) is covered by exactly one selected clause
      have hvs_mem : ∀ k < vs.length, vs.getD k 0 ∈ φ.vars := fun k hk =>
        List.mem_eraseDupsBy_eq.mp (getD_mem_of_lt hk)
      have hocc_bounds : ∀ k < vs.length,
          1 ≤ (occIndices φ (vs.getD k 0)).length ∧ (occIndices φ (vs.getD k 0)).length ≤ 3 := by
        intro k hk
        rw [count_occIndices_eq φ _ (fun c hc => (hexact c hc).2)]
        exact ⟨Nat.succ_le_of_lt (List.count_pos_iff.mpr (hvs_mem k hk)), hcnt _⟩
      have hocc_lt : ∀ k, ∀ i ∈ occIndices φ (vs.getD k 0), i < m := fun k i hi =>
        (mem_occIndices_iff.mp hi).1
      -- Prove selList is Nodup (sublist-like of (reduce φ).clauses, which is Nodup!)
      -- Actually, even simpler: every element in selList appears in `selList.filter (u ∈ ·)`
      -- with length 1, and selList is Nodup because every c ∈ selVar k is in varClauses k!
      have hsel_sub_k : ∀ k, ∀ c ∈ selVar k,
          c ∈ varClauses m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0)) := by
        intro k c hck
        dsimp only [selVar, selVarAux] at hck
        unfold varClauses choiceGadget
        split_ifs at hck ⊢ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hck ⊢ <;>
          tauto
      have hsel_nd_k : ∀ k < vs.length, (selVar k).Nodup := by
        intro k hk
        have hi_lt : ∀ i ∈ occIndices φ (vs.getD k 0), i < m := hocc_lt k
        have hb := hocc_bounds k hk
        dsimp only [selVar, selVarAux]
        split_ifs with hτk h1 h2 h3 h1' h2' h3'
        · have hi0 : (occIndices φ (vs.getD k 0)).getD 0 0 < m :=
            hi_lt _ (getD_mem_of_lt (by omega))
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
            and_true, not_or, List.nodup_nil, not_false_eq_true]
          grind
        · have hi0 : (occIndices φ (vs.getD k 0)).getD 0 0 < m :=
            hi_lt _ (getD_mem_of_lt (by omega))
          have hi1 : (occIndices φ (vs.getD k 0)).getD 1 0 < m :=
            hi_lt _ (getD_mem_of_lt (by omega))
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
            and_true, not_or, List.nodup_nil, not_false_eq_true]
          grind
        · have hi0 : (occIndices φ (vs.getD k 0)).getD 0 0 < m :=
            hi_lt _ (getD_mem_of_lt (by omega))
          have hi1 : (occIndices φ (vs.getD k 0)).getD 1 0 < m :=
            hi_lt _ (getD_mem_of_lt (by omega))
          have hi2 : (occIndices φ (vs.getD k 0)).getD 2 0 < m :=
            hi_lt _ (getD_mem_of_lt (by omega))
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
            and_true, not_or, List.nodup_nil, not_false_eq_true]
          grind
        · exact List.nodup_nil
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
            and_true, not_or, List.nodup_nil, not_false_eq_true]
          grind
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
            and_true, List.nodup_nil, not_false_eq_true]
          grind
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
            and_true, not_or, List.nodup_nil, not_false_eq_true]
          grind
        · exact List.nodup_nil
      have hred_wf := reduce_isWellFormed hs hne
      have hred_nd : ((List.range vs.length).flatMap fun k =>
          varClauses m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0))).Nodup := by
        rw [hred] at hred_wf; exact hred_wf.2.2.1
      have hsel_nd : selList.Nodup := by
        rw [List.nodup_flatMap]
        refine ⟨fun k hk => hsel_nd_k k (List.mem_range.mp hk), ?_⟩
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.getElem_range]
        intro c hc1 hc2
        have hpw := (List.nodup_flatMap.mp hred_nd).2
        rw [List.pairwise_iff_getElem] at hpw
        have hdisj := hpw i j (by simpa using hi) (by simpa using hj) hij
        simp only [List.getElem_range] at hdisj
        exact hdisj (hsel_sub_k i c hc1) (hsel_sub_k j c hc2)
      -- Now check (selList.filter (u ∈ ·)).length = 1 for every u < 3 * (m + 2 * G)
      intro u hu
      rw [hred] at hu
      dsimp only at hu
      have hset_sel : selList.toFinset.filter (u ∈ ·) =
          (selList.filter (fun c => decide (u ∈ c))).toFinset := by
        ext c; simp
      rw [hset_sel, List.toFinset_card_of_nodup (hsel_nd.filter _)]
      have hflat_filter :
          (selList.filter (fun c => decide (u ∈ c))).length =
            ((List.range vs.length).map fun k =>
              ((selVar k).filter (fun c => decide (u ∈ c))).length).sum := by
        dsimp only [selList]
        clear hsel_nd
        induction (List.range vs.length) with
        | nil => simp
        | cons a t ih => simp [List.filter_append, ih]
      rw [hflat_filter]
      by_cases hum : u < 3 * m
      · set i := u / 3
        set r := u % 3
        have hi : i < m := by omega
        have hr : r < 3 := by omega
        have hu_eq : u = 3 * i + r := by omega
        rw [hu_eq]
        have hsel_clause_cnt : ∀ k < vs.length,
            ((selVar k).filter (fun c => decide (3 * i + r ∈ c))).length =
              if τ (vs.getD k 0) ∧ i ∈ occIndices φ (vs.getD k 0) then 1 else 0 := fun k hk =>
          selVar_clause_count m (3 * m + 6 * gadgetPrefix φ vs k) i r
            (occIndices φ (vs.getD k 0)) (τ (vs.getD k 0)) (nodup_occIndices φ _)
            (hocc_bounds k hk).1 (hocc_bounds k hk).2 (hocc_lt k) hi hr (by omega)
        have hmap_eq :
            ((List.range vs.length).map fun k =>
              ((selVar k).filter (fun c => decide (3 * i + r ∈ c))).length) =
            (List.range vs.length).map fun k =>
              if τ (vs.getD k 0) ∧ i ∈ occIndices φ (vs.getD k 0) then 1 else 0 :=
          List.map_congr_left fun k hk => hsel_clause_cnt k (List.mem_range.mp hk)
        rw [hmap_eq]
        -- Clause i has exactly one true variable in φ
        have hci : φ.getD i [] ∈ φ := getD_mem_of_lt hi
        have hsat_i := hτ (φ.getD i []) hci
        rw [Clause.evalOne_eq_true_iff] at hsat_i
        have hpos_i : ∀ l ∈ φ.getD i [], l.2 = true := fun l hl =>
          (OneSAT.positiveCheck_iff φ).mp hpos _ hci l hl
        have hnd_ci : ((φ.getD i []).map Prod.fst).Nodup := (hexact _ hci).2
        have htrue_cnt : (((φ.getD i []).map Prod.fst).filter (fun v => τ v)).length = 1 := by
          have hmap_f := filter_pos_clause τ (φ.getD i []) hpos_i
          rw [← hmap_f, List.length_map]
          simpa [List.countP_eq_length_filter] using hsat_i
        have hsub_ci : ∀ v ∈ ((φ.getD i []).map Prod.fst).filter (fun v => τ v), v ∈ vs := by
          intro v hv
          rw [hvs_def, distinctVars, List.mem_eraseDupsBy_eq]
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hv).1
          exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨_, hci, hl⟩, rfl⟩
        set tgt := ((φ.getD i []).map Prod.fst).filter (fun v => τ v)
        have hmap_simp :
            ((List.range vs.length).map fun k =>
              if τ (vs.getD k 0) ∧ i ∈ occIndices φ (vs.getD k 0) then 1 else 0) =
            vs.map fun v => if v ∈ tgt then 1 else 0 := by
          conv_rhs => rw [← map_getD_range vs 0, List.map_map]
          refine List.map_congr_left fun k _ => ?_
          dsimp only [Function.comp_apply]
          have hiff : (τ (vs.getD k 0) = true ∧ i ∈ occIndices φ (vs.getD k 0)) ↔
              vs.getD k 0 ∈ tgt := by
            dsimp only [tgt]
            rw [List.mem_filter, mem_occIndices_iff]
            exact ⟨fun ⟨h1, _, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, hi, h2⟩⟩
          simp only [hiff]
        rw [hmap_simp]
        have hfilt : (vs.map fun v => if v ∈ tgt then 1 else 0).sum =
            (vs.filter (fun v => decide (v ∈ tgt))).length := by
          clear hsub_ci htrue_cnt hmap_simp
          induction vs with
          | nil => simp
          | cons x xs ih => by_cases hx : x ∈ tgt <;> simp [hx, ih, Nat.add_comm]
        rw [hfilt]
        have hset : (vs.filter (fun v => decide (v ∈ tgt))).toFinset = tgt.toFinset := by
          ext v
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
          exact hsub_ci v
        have h1 : (vs.filter (fun v => decide (v ∈ tgt))).toFinset.card =
            (vs.filter (fun v => decide (v ∈ tgt))).length :=
          List.toFinset_card_of_nodup
            ((List.nodup_eraseDupsBy_eq φ.vars).filter (fun v => decide (v ∈ tgt)))
        have h2 := List.toFinset_card_of_nodup (hnd_ci.filter (fun v => τ v))
        rw [← h1, hset, h2, htrue_cnt]
      · -- Dummy element u ∈ [3 * m, 3 * m + 6 * G)
        have hexists_k : ∃ k < vs.length,
            3 * m + 6 * gadgetPrefix φ vs k ≤ u ∧
              u < 3 * m + 6 * gadgetPrefix φ vs (k + 1) := by
          have hfind : ∀ n ≤ vs.length, 3 * m ≤ u → u < 3 * m + 6 * gadgetPrefix φ vs n →
              ∃ k < n, 3 * m + 6 * gadgetPrefix φ vs k ≤ u ∧
                u < 3 * m + 6 * gadgetPrefix φ vs (k + 1) := by
            intro n
            induction n with
            | zero => simp [gadgetPrefix]
            | succ n' ih =>
              intro hn' hlo hhi
              by_cases hlt : u < 3 * m + 6 * gadgetPrefix φ vs n'
              · obtain ⟨k, hk, h1, h2⟩ := ih (by omega) hlo hlt
                exact ⟨k, by omega, h1, h2⟩
              · exact ⟨n', Nat.lt_succ_self _, by omega, hhi⟩
          exact hfind vs.length le_rfl (by omega) (by omega)
        obtain ⟨k₀, hk₀, hlo₀, hhi₀⟩ := hexists_k
        have honly : ∀ k < vs.length, k ≠ k₀ →
            ((selVar k).filter (fun c => decide (u ∈ c))).length = 0 := by
          intro k hk hne
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro c hc; simp only [decide_eq_true_eq]; intro huc
          rcases varClauses_elem_lt (hocc_lt k) (hsel_sub_k k c hc) huc with hlt | ⟨hlo, hhi⟩
          · omega
          · by_cases hlt_k : k < k₀
            · have := gadgetPrefix_mono φ vs (show k + 1 ≤ k₀ by omega)
              simp only [gadgetPrefix] at this; omega
            · have := gadgetPrefix_mono φ vs (show k₀ + 1 ≤ k by omega)
              omega
        have hsum_single : ∀ (n : ℕ) (f : ℕ → ℕ), k₀ < n → (∀ k < n, k ≠ k₀ → f k = 0) →
            ((List.range n).map f).sum = f k₀ := by
          intro n f hk0 hz
          induction n with
          | zero => omega
          | succ n' ih =>
            rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
              List.sum_singleton]
            by_cases heq : k₀ = n'
            · subst heq
              have h0 : ((List.range k₀).map f).sum = 0 :=
                List.sum_eq_zero fun x hx => by
                  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
                  exact hz j (by rw [List.mem_range] at hj; omega)
                    (by rw [List.mem_range] at hj; omega)
              omega
            · rw [hz n' (Nat.lt_succ_self _) (Ne.symm heq),
                ih (by omega) (fun k hk => hz k (by omega))]
              omega
        rw [hsum_single vs.length _ hk₀ honly]
        dsimp only [selVar]
        exact selVar_dummy_count m (3 * m + 6 * gadgetPrefix φ vs k₀) u
          (occIndices φ (vs.getD k₀ 0)) (τ (vs.getD k₀ 0)) (hocc_bounds k₀ hk₀).1
          (hocc_bounds k₀ hk₀).2 (hocc_lt k₀) (by omega) hlo₀
          (by simp only [gadgetPrefix] at hhi₀; omega)

/-- Backward direction: an exact cover of `reduce φ` induces a 1-in-3 satisfying assignment
of `φ` (by restricting to copy 0 of the clause elements). -/
private theorem oneSatisfiable_of_mem {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) (h : reduce φ ∈ RXC3) :
    φ.OneSatisfiable := by
  by_cases hne : φ.isEmpty = true
  · cases hφ : φ with
    | nil => exact ⟨fun _ => false, rfl⟩
    | cons _ _ => simp [hφ] at hne
  · simp only [Bool.not_eq_true] at hne
    have ⟨hexact, hpos, hcnt⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
    set vs := distinctVars φ with hvs_def
    set m := φ.length with hm_def
    set G := gadgetPrefix φ vs vs.length with hG_def
    have hred : reduce φ = ⟨m + 2 * G, (List.range vs.length).flatMap fun k =>
        varClauses m (3 * m + 6 * gadgetPrefix φ vs k) (occIndices φ (vs.getD k 0))⟩ := by
      simp [reduce, hs, hne, hvs_def, hm_def, hG_def]
    obtain ⟨hwf, D, hDsub, hDcov⟩ := h
    rw [hred] at hDsub hDcov
    have hvs_mem : ∀ k < vs.length, vs.getD k 0 ∈ φ.vars := fun k hk =>
      List.mem_eraseDupsBy_eq.mp (getD_mem_of_lt hk)
    have hocc_bounds : ∀ k < vs.length,
        1 ≤ (occIndices φ (vs.getD k 0)).length ∧ (occIndices φ (vs.getD k 0)).length ≤ 3 := by
      intro k hk
      rw [count_occIndices_eq φ _ (fun c hc => (hexact c hc).2)]
      exact ⟨Nat.succ_le_of_lt (List.count_pos_iff.mpr (hvs_mem k hk)), hcnt _⟩
    have hocc_lt : ∀ k, ∀ i ∈ occIndices φ (vs.getD k 0), i < m := fun k i hi =>
      (mem_occIndices_iff.mp hi).1
    -- Define the assignment: τ(v) = true iff the copy-0 clause for v's first occurrence is in D
    let τ : ℕ → Bool := fun v =>
      let occ := occIndices φ v
      decide (∃ k < vs.length, vs.getD k 0 = v ∧
        ∃ c ∈ D, c ∈ varClauses m (3 * m + 6 * gadgetPrefix φ vs k) occ ∧
          3 * (occ.getD 0 0) ∈ c)
    -- Helper: for any k < vs.length, the copy-0 clauses of variable k are synchronized
    -- (either all of them are in D, or none of them are in D).
    have hsync : ∀ k < vs.length, ∀ i ∈ occIndices φ (vs.getD k 0),
        (∃ c ∈ D, c ∈ varClauses m (3 * m + 6 * gadgetPrefix φ vs k)
          (occIndices φ (vs.getD k 0)) ∧ 3 * i ∈ c) ↔
        τ (vs.getD k 0) = true := by
      intro k hk i hi
      set occ := occIndices φ (vs.getD k 0)
      set base := 3 * m + 6 * gadgetPrefix φ vs k
      have hsub_u : ∀ c ∈ D, ∀ u, base ≤ u → u < base + 6 → u ∈ c →
          c ∈ varClauses m base occ := by
        intro c hcD u hlo hhi huc
        obtain ⟨k', hk', hck'⟩ := List.mem_flatMap.mp (hDsub c hcD)
        rw [List.mem_range] at hk'
        by_cases heq : k' = k
        · subst heq; exact hck'
        · exfalso
          rcases varClauses_elem_lt (hocc_lt k') hck' huc with hlt | ⟨hlo', hhi'⟩
          · omega
          · by_cases hlt_k : k' < k
            · have := gadgetPrefix_mono φ vs (show k' + 1 ≤ k by omega)
              simp only [gadgetPrefix] at this; omega
            · have := gadgetPrefix_mono φ vs (show k + 1 ≤ k' by omega)
              have hgc : 1 ≤ gadgetCount occ.length := by
                have hb := hocc_bounds k hk
                unfold gadgetCount
                have : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by
                  dsimp only [occ]; omega
                rcases this with h | h | h <;> simp [h]
              simp only [gadgetPrefix] at this; dsimp only [occ, base] at *; omega
      have hτ_iff : τ (vs.getD k 0) = true ↔
          ∃ c ∈ D, c ∈ varClauses m base occ ∧ 3 * (occ.getD 0 0) ∈ c := by
        simp only [τ, decide_eq_true_eq]
        constructor
        · rintro ⟨k', hk', hveq, h⟩
          have heq : k' = k := by
            have hnd := List.nodup_eraseDupsBy_eq φ.vars
            have h1 : vs[k'] = vs[k] := by
              simpa [List.getD_eq_getElem?_getD, hk', hk] using hveq
            exact congrArg Fin.val
              ((List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨k', hk'⟩) (a₂ := ⟨k, hk⟩) h1)
          subst heq; exact h
        · intro h; exact ⟨k, hk, rfl, h⟩
      rw [hτ_iff]
      have hb := hocc_bounds k hk
      have hbase_end : base + 6 * gadgetCount occ.length ≤ 3 * (m + 2 * G) := by
        have := gadgetPrefix_succ_le φ vs hk; dsimp only [occ, base] at *; omega
      have hlen : occ.length = 1 ∨ occ.length = 2 ∨ occ.length = 3 := by
        dsimp only [occ]; omega
      rcases hlen with hl | hl | hl
      · have hget := list_eq_one_of_length hl
        rw [hget, List.mem_singleton] at hi; subst hi; rfl
      · have hget := list_eq_two_of_length hl
        have hi0 : occ.getD 0 0 < m :=
          hocc_lt k _ (getD_mem_of_lt (show 0 < occ.length by omega))
        have hi1 : occ.getD 1 0 < m :=
          hocc_lt k _ (getD_mem_of_lt (show 1 < occ.length by omega))
        have hvc_eq : ∀ c ∈ varClauses m base occ,
            3 * occ.getD 0 0 ∈ c ↔ 3 * occ.getD 1 0 ∈ c := by
          intro c hc
          unfold varClauses at hc
          simp only [hl, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with (rfl | rfl | rfl) | hcg
          · simp only [List.mem_cons, List.not_mem_nil, or_false]; grind
          · simp only [List.mem_cons, List.not_mem_nil, or_false]; grind
          · simp only [List.mem_cons, List.not_mem_nil, or_false]; grind
          · exact ⟨fun h => by have := (choiceGadget_elem_range hcg h).1; omega,
              fun h => by have := (choiceGadget_elem_range hcg h).1; omega⟩
        rw [hget, List.mem_cons, List.mem_singleton] at hi
        rcases hi with rfl | rfl
        · rfl
        · constructor
          · rintro ⟨c, hcD, hcv, h1⟩; exact ⟨c, hcD, hcv, (hvc_eq c hcv).mpr h1⟩
          · rintro ⟨c, hcD, hcv, h0⟩; exact ⟨c, hcD, hcv, (hvc_eq c hcv).mp h0⟩
      · -- occ.length = 3: the two copy-0 clauses share the H₃ gadget at `base`!
        have hget := list_eq_three_of_length hl
        have hi0 : occ.getD 0 0 < m :=
          hocc_lt k _ (getD_mem_of_lt (show 0 < occ.length by omega))
        have hi1 : occ.getD 1 0 < m :=
          hocc_lt k _ (getD_mem_of_lt (show 1 < occ.length by omega))
        have hi2 : occ.getD 2 0 < m :=
          hocc_lt k _ (getD_mem_of_lt (show 2 < occ.length by omega))
        have hnd_occ : occ.Nodup := nodup_occIndices φ (vs.getD k 0)
        have hne01 : occ.getD 0 0 ≠ occ.getD 1 0 := by
          rw [hget] at hnd_occ; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            or_false, not_or] at hnd_occ; exact hnd_occ.1.1
        have hne02 : occ.getD 0 0 ≠ occ.getD 2 0 := by
          rw [hget] at hnd_occ; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            or_false, not_or] at hnd_occ; exact hnd_occ.1.2
        have hne12 : occ.getD 1 0 ≠ occ.getD 2 0 := by
          rw [hget] at hnd_occ; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
            or_false, not_or] at hnd_occ; exact hnd_occ.2.1
        have hbase_6 : base + 6 ≤ 3 * (m + 2 * G) := by
          simp only [gadgetCount, hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
            ↓reduceIte] at hbase_end; omega
        -- Use choiceGadget_sync on Dg = D.filter (· ∈ choiceGadget base)!
        have hport_le : ∀ r < 3,
            ((D.filter (· ∈ choiceGadget base)).filter (base + r ∈ ·)).card ≤ 1 := by
          intro r hr
          rw [← hDcov (base + r) (by dsimp only [base] at *; omega)]
          exact Finset.card_le_card (fun c hc => by
            simp only [Finset.mem_filter] at hc ⊢; exact ⟨hc.1.1, hc.2⟩)
        have hint_eq : ∀ r < 3,
            ((D.filter (· ∈ choiceGadget base)).filter (base + 3 + r ∈ ·)).card = 1 := by
          intro r hr
          rw [← hDcov (base + 3 + r) (by dsimp only [base] at *; omega)]
          congr 1; ext c; simp only [Finset.mem_filter]
          refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
          have hcv := hsub_u c h.1 (base + 3 + r) (by omega) (by omega) h.2
          unfold varClauses at hcv
          simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcv
          rcases hcv with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          · exact hcg
          · have := (choiceGadget_elem_range hcg h.2).1; omega
          · have := (choiceGadget_elem_range hcg h.2).1; omega
        have hsync_cg := choiceGadget_sync (b := base) (D := D) hport_le hint_eq
        -- Helper: port `base + 0` is NOT in `choiceGadget base` in D iff `[3*i0, 3*i1, base] ∈ D`
        let cA := [3 * occ.getD 0 0, 3 * occ.getD 1 0, base]
        let cB := [3 * occ.getD 2 0, base + 1, base + 2]
        have hport0 : ((D.filter (· ∈ choiceGadget base)).filter (base + 0 ∈ ·)).card = 0 ↔
            cA ∈ D := by
          have hcov0 := hDcov (base + 0) (by dsimp only [base] at *; omega)
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcov0
          have hm0 : c ∈ D.filter (fun c => base + 0 ∈ c) := hc ▸ Finset.mem_singleton_self c
          have hcD : c ∈ D := (Finset.mem_filter.mp hm0).1
          have hbc : base ∈ c := by simpa using (Finset.mem_filter.mp hm0).2
          have hc_eq : c = cA ∨ c ∈ choiceGadget base := by
            have hcv := hsub_u c hcD base le_rfl (by omega) hbc
            unfold varClauses at hcv
            simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcv
            rcases hcv with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
            · exact Or.inl rfl
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · exact Or.inr hcg
            · have := (choiceGadget_elem_range hcg hbc).1; omega
            · have := (choiceGadget_elem_range hcg hbc).1; omega
          have hcA_not_cg : cA ∉ choiceGadget base := by
            intro hmem
            have := (choiceGadget_elem_range hmem (by simp [cA] : 3 * occ.getD 0 0 ∈ cA)).1
            omega
          constructor
          · intro h0
            rcases hc_eq with rfl | hcg
            · exact hcD
            · exfalso
              have hmem : c ∈ (D.filter (· ∈ choiceGadget base)).filter (base + 0 ∈ ·) := by
                simp [hcD, hcg, hbc]
              rw [Finset.card_eq_zero.mp h0] at hmem; simp at hmem
          · intro hcAD
            have heq : cA = c := by
              have : cA ∈ D.filter (base + 0 ∈ ·) := Finset.mem_filter.mpr ⟨hcAD, by simp [cA]⟩
              rw [hc] at this; exact Finset.mem_singleton.mp this
            rw [Finset.card_eq_zero]
            ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro hx hx0
            have hx_eq : x = c := by
              have : x ∈ D.filter (base + 0 ∈ ·) := Finset.mem_filter.mpr ⟨hx.1, hx0⟩
              rw [hc] at this; exact Finset.mem_singleton.mp this
            rw [hx_eq, ← heq] at hx; exact hcA_not_cg hx.2
        have hport1 : ((D.filter (· ∈ choiceGadget base)).filter (base + 1 ∈ ·)).card = 0 ↔
            cB ∈ D := by
          have hcov1 := hDcov (base + 1) (by dsimp only [base] at *; omega)
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcov1
          have hm1 : c ∈ D.filter (fun c => base + 1 ∈ c) := hc ▸ Finset.mem_singleton_self c
          have hcD : c ∈ D := (Finset.mem_filter.mp hm1).1
          have hbc : base + 1 ∈ c := (Finset.mem_filter.mp hm1).2
          have hc_eq : c = cB ∨ c ∈ choiceGadget base := by
            have hcv := hsub_u c hcD (base + 1) (by omega) (by omega) hbc
            unfold varClauses at hcv
            simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcv
            rcases hcv with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · exact Or.inl rfl
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc; omega
            · exact Or.inr hcg
            · have := (choiceGadget_elem_range hcg hbc).1; omega
            · have := (choiceGadget_elem_range hcg hbc).1; omega
          have hcB_not_cg : cB ∉ choiceGadget base := by
            intro hmem
            have := (choiceGadget_elem_range hmem (by simp [cB] : 3 * occ.getD 2 0 ∈ cB)).1
            omega
          constructor
          · intro h0
            rcases hc_eq with rfl | hcg
            · exact hcD
            · exfalso
              have hmem : c ∈ (D.filter (· ∈ choiceGadget base)).filter (base + 1 ∈ ·) := by
                simp [hcD, hcg, hbc]
              rw [Finset.card_eq_zero.mp h0] at hmem; simp at hmem
          · intro hcBD
            have heq : cB = c := by
              have : cB ∈ D.filter (base + 1 ∈ ·) := Finset.mem_filter.mpr ⟨hcBD, by simp [cB]⟩
              rw [hc] at this; exact Finset.mem_singleton.mp this
            rw [Finset.card_eq_zero]
            ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro hx hx1
            have hx_eq : x = c := by
              have : x ∈ D.filter (base + 1 ∈ ·) := Finset.mem_filter.mpr ⟨hx.1, hx1⟩
              rw [hc] at this; exact Finset.mem_singleton.mp this
            rw [hx_eq, ← heq] at hx; exact hcB_not_cg hx.2
        have hAB_iff : cA ∈ D ↔ cB ∈ D := by
          rw [← hport0, ← hport1]
          rcases hsync_cg with h1 | h0
          · rw [h1 0 (by omega), h1 1 (by omega)]
          · rw [h0 0 (by omega), h0 1 (by omega)]
        have hmem_cA : cA ∈ varClauses m base occ := by
          unfold varClauses
          simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
            List.mem_append, List.mem_cons, true_or, cA]
        have hmem_cB : cB ∈ varClauses m base occ := by
          unfold varClauses
          simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
            List.mem_append, List.mem_cons, true_or, or_true, cB]
        have h0_iff : (∃ c ∈ D, c ∈ varClauses m base occ ∧ 3 * occ.getD 0 0 ∈ c) ↔ cA ∈ D := by
          constructor
          · rintro ⟨c, hcD, hcv, h0⟩
            unfold varClauses at hcv
            simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcv
            rcases hcv with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
            · exact hcD
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; omega
            · have := (choiceGadget_elem_range hcg h0).1; omega
            · have := (choiceGadget_elem_range hcg h0).1; omega
            · have := (choiceGadget_elem_range hcg h0).1; omega
          · intro h; exact ⟨cA, h, hmem_cA, by simp [cA]⟩
        have h1_iff : (∃ c ∈ D, c ∈ varClauses m base occ ∧ 3 * occ.getD 1 0 ∈ c) ↔ cA ∈ D := by
          constructor
          · rintro ⟨c, hcD, hcv, h1⟩
            unfold varClauses at hcv
            simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcv
            rcases hcv with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
            · exact hcD
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1; omega
            · have := (choiceGadget_elem_range hcg h1).1; omega
            · have := (choiceGadget_elem_range hcg h1).1; omega
            · have := (choiceGadget_elem_range hcg h1).1; omega
          · intro h; exact ⟨cA, h, hmem_cA, by simp [cA]⟩
        have h2_iff : (∃ c ∈ D, c ∈ varClauses m base occ ∧ 3 * occ.getD 2 0 ∈ c) ↔ cB ∈ D := by
          constructor
          · rintro ⟨c, hcD, hcv, h2⟩
            unfold varClauses at hcv
            simp only [hl, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcv
            rcases hcv with (((rfl | rfl | rfl | rfl | rfl | rfl) | hcg) | hcg) | hcg
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; omega
            · exact hcD
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; omega
            · have := (choiceGadget_elem_range hcg h2).1; omega
            · have := (choiceGadget_elem_range hcg h2).1; omega
            · have := (choiceGadget_elem_range hcg h2).1; omega
          · intro h; exact ⟨cB, h, hmem_cB, by simp [cB]⟩
        rw [hget, List.mem_cons, List.mem_cons, List.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · rfl
        · rw [h1_iff, h0_iff]
        · rw [h2_iff, h0_iff, hAB_iff]
    -- Now verify τ satisfies every clause of φ with exactly one true literal!
    refine ⟨τ, (CNF.evalOne_eq_true_iff τ φ).mpr fun c hc => ?_⟩
    obtain ⟨i, hi, hci⟩ : ∃ i < m, φ.getD i [] = c := by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi]⟩
    have hcov_i := hDcov (3 * i) (by dsimp only; omega)
    obtain ⟨cl, hcl⟩ := Finset.card_eq_one.mp hcov_i
    have hm_cl : cl ∈ D.filter (fun c => 3 * i ∈ c) := hcl ▸ Finset.mem_singleton_self cl
    have hclD : cl ∈ D := (Finset.mem_filter.mp hm_cl).1
    have h3i_cl : 3 * i ∈ cl := (Finset.mem_filter.mp hm_cl).2
    obtain ⟨k0, hk0, hcl_k0⟩ := List.mem_flatMap.mp (hDsub cl hclD)
    rw [List.mem_range] at hk0
    have hi_in_occ0 : i ∈ occIndices φ (vs.getD k0 0) := by
      have hcnt1 := varClauses_clause_count (m := m) (base := 3 * m + 6 * gadgetPrefix φ vs k0)
        (by omega) (nodup_occIndices φ _) (hocc_lt k0) (hocc_bounds k0 hk0).1
        (hocc_bounds k0 hk0).2 hi (by omega : 0 < 3)
      by_contra hnot
      simp only [hnot, ↓reduceIte, Nat.add_zero] at hcnt1
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hcnt1
      exact (by simpa using hcnt1 cl hcl_k0 : ¬ 3 * i ∈ cl) h3i_cl
    have hτ_k0 : τ (vs.getD k0 0) = true :=
      (hsync k0 hk0 i hi_in_occ0).mp ⟨cl, hclD, hcl_k0, h3i_cl⟩
    -- Any other variable in clause i must be false
    have huniq : ∀ v ∈ c.map Prod.fst, τ v = true → v = vs.getD k0 0 := by
      intro v hv hτv
      have hv_vs : v ∈ vs := by
        rw [hvs_def, distinctVars, List.mem_eraseDupsBy_eq]
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv_vs
      have hgetk : vs.getD k 0 = vs[k] := by simp [List.getD_eq_getElem?_getD, hk]
      rw [← hgetk] at hτv ⊢
      have hi_in_occk : i ∈ occIndices φ (vs.getD k 0) := by
        rw [mem_occIndices_iff, hci]; exact ⟨hi, by rwa [hgetk]⟩
      obtain ⟨cl', hcl'D, hcl'_k, h3i_cl'⟩ := (hsync k hk i hi_in_occk).mpr hτv
      have hcl'_eq : cl' = cl := by
        have : cl' ∈ D.filter (3 * i ∈ ·) := Finset.mem_filter.mpr ⟨hcl'D, h3i_cl'⟩
        rw [hcl] at this; exact Finset.mem_singleton.mp this
      subst hcl'_eq
      by_contra hne_k
      have hred_wf := reduce_isWellFormed hs hne
      have hred_nd : ((List.range vs.length).flatMap fun j =>
          varClauses m (3 * m + 6 * gadgetPrefix φ vs j) (occIndices φ (vs.getD j 0))).Nodup := by
        rw [hred] at hred_wf; exact hred_wf.2.2.1
      have hpw := (List.nodup_flatMap.mp hred_nd).2
      rw [List.pairwise_iff_getElem] at hpw
      have hne_idx : k ≠ k0 := fun h => hne_k (by rw [h])
      rcases Nat.lt_or_gt_of_ne hne_idx with hlt | hgt
      · have hdisj := hpw k k0 (by simpa using hk) (by simpa using hk0) hlt
        simp only [List.getElem_range] at hdisj
        exact hdisj hcl'_k hcl_k0
      · have hdisj := hpw k0 k (by simpa using hk0) (by simpa using hk) hgt
        simp only [List.getElem_range] at hdisj
        exact hdisj hcl_k0 hcl'_k
    have hv0_mem : vs.getD k0 0 ∈ c.map Prod.fst := by
      have := (mem_occIndices_iff.mp hi_in_occ0).2
      rwa [hci] at this
    rw [Clause.evalOne_eq_true_iff]
    have hpos_c : ∀ l ∈ c, l.2 = true := fun l hl =>
      (OneSAT.positiveCheck_iff φ).mp hpos c hc l hl
    have hnd_c : (c.map Prod.fst).Nodup := (hexact c hc).2
    have hmap_f : (c.filter (fun l => Literal.eval τ l)).map Prod.fst =
        (c.map Prod.fst).filter (fun v => τ v) := filter_pos_clause τ c hpos_c
    have hfilt_eq : (c.map Prod.fst).filter (fun v => τ v) = [vs.getD k0 0] := by
      have hmem_filt : ∀ v, v ∈ (c.map Prod.fst).filter (fun v => τ v) ↔ v = vs.getD k0 0 := by
        intro v
        simp only [List.mem_filter]
        exact ⟨fun ⟨hv, htv⟩ => huniq v hv htv, fun h => h ▸ ⟨hv0_mem, hτ_k0⟩⟩
      have hnd_f : ((c.map Prod.fst).filter (fun v => τ v)).Nodup := hnd_c.filter _
      have htoF : ((c.map Prod.fst).filter (fun v => τ v)).toFinset = {vs.getD k0 0} := by
        ext v; simp only [List.mem_toFinset, Finset.mem_singleton, hmem_filt]
      have hcard1 : ((c.map Prod.fst).filter (fun v => τ v)).length = 1 := by
        rw [← List.toFinset_card_of_nodup hnd_f, htoF, Finset.card_singleton]
      rcases hL : (c.map Prod.fst).filter (fun v => τ v) with _ | ⟨a, _ | ⟨b, t⟩⟩
      · rw [hL] at hcard1; simp at hcard1
      · have ha : a = vs.getD k0 0 := (hmem_filt a).mp (by rw [hL]; simp)
        rw [ha]
      · rw [hL] at hcard1; simp at hcard1
    have hlen1 : (c.filter (fun l => Literal.eval τ l)).length = 1 := by
      have := congrArg List.length hmap_f
      rw [List.length_map, hfilt_eq, List.length_singleton] at this
      exact this
    simpa [List.countP_eq_length_filter] using hlen1

theorem reduce_mem_iff (φ : CNF ℕ) :
    reduce φ ∈ RXC3 ↔ φ ∈ PositiveOneInExactThreeSATThree := by
  rw [PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck]
  by_cases hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · exact ⟨fun h => ⟨hs, oneSatisfiable_of_mem hs h⟩, fun h => mem_of_oneSatisfiable hs h.2⟩
  · simp only [reduce, hs, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    exact noInstance_notMem

/-! ### Polynomial-time computability of `reduce` -/

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_choiceGadget :
    ComputableInPolyTime choiceGadget encNat (encList (encList encNat)) := by
  unfold choiceGadget
  fun_prop

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_varClauses :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List ℕ => varClauses p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) (encList encNat))
      (encList (encList encNat)) := by
  unfold varClauses choiceGadget
  fun_prop

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_occIndices :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => occIndices p.1 p.2)
      (encPair encCNF encNat) (encList encNat) := by
  have hrange : ComputableInPolyTime (fun p : CNF ℕ × ℕ => List.range p.1.length)
      (encPair encCNF encNat) (encList encUnary) := by fun_prop
  have hstep : ComputableInPolyTime
      (fun q : (CNF ℕ × ℕ) × ℕ =>
        decide (q.1.2 ∈ ((q.1.1.getD q.2 []).map Prod.fst)))
      (encPair (encPair encCNF encNat) encUnary) encBool := by
    have hget : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ => q.1.1.getD q.2 [])
        (encPair (encPair encCNF encNat) encUnary) (encClause encNat) :=
      ComputableInPolyTime.listGetDWithInput (encA := encClause encNat)
        ((ComputableInPolyTime.fst encCNF encNat).comp'
          (ComputableInPolyTime.fst (encPair encCNF encNat) encUnary))
        (ComputableInPolyTime.snd (encPair encCNF encNat) encUnary) []
    have hmap : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ => (q.1.1.getD q.2 []).map Prod.fst)
        (encPair (encPair encCNF encNat) encUnary) (encList encNat) :=
      (ComputableInPolyTime.map (encA := encPair encNat encBool) (encB := encNat)
        (ComputableInPolyTime.fst encNat encBool)).comp' hget
    have hv : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ => q.1.2)
        (encPair (encPair encCNF encNat) encUnary) encNat :=
      (ComputableInPolyTime.snd encCNF encNat).comp'
        (ComputableInPolyTime.fst (encPair encCNF encNat) encUnary)
    exact ComputableInPolyTime.decide_mem hmap hv
  have hfilt := ComputableInPolyTime.filterWith hstep ComputableInPolyTime.id' hrange
  exact ((ComputableInPolyTime.map (encA := encUnary) (encB := encNat)
    ComputableInPolyTime.unary_to_binary).comp' hfilt).of_enc_eq fun p => by
    simp only [List.map_id', occIndices]

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_distinctVars :
    ComputableInPolyTime distinctVars encCNF (encList encNat) := by
  have hvars : ComputableInPolyTime CNF.vars encCNF (encList encNat) := by
    unfold CNF.vars
    have hflat : ComputableInPolyTime (fun φ : CNF ℕ => φ.flatten) encCNF
        (encList (encPair encNat encBool)) :=
      ComputableInPolyTime.flatten (encPair encNat encBool)
    have hmap : ComputableInPolyTime (fun l : List (Literal ℕ) => l.map Prod.fst)
        (encList (encPair encNat encBool)) (encList encNat) :=
      ComputableInPolyTime.map (ComputableInPolyTime.fst encNat encBool)
    exact hmap.comp hflat
  unfold distinctVars
  exact ComputableInPolyTime.eraseDupsByWithInput hvars (by fun_prop)

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_gadgetPrefix :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List ℕ) × ℕ => gadgetPrefix p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF (encList encNat)) encUnary) encUnary := by
  have hfold : ComputableInPolyTime
      (fun p : (CNF ℕ × List ℕ) × ℕ =>
        (List.range p.2).foldl
          (fun acc k => acc + gadgetCount (occIndices p.1.1 (p.1.2.getD k 0)).length) 0)
      (encPair (encPair encCNF (encList encNat)) encUnary) encUnary := by
    have hlist : ComputableInPolyTime
        (fun p : (CNF ℕ × List ℕ) × ℕ => List.range p.2)
        (encPair (encPair encCNF (encList encNat)) encUnary) (encList encUnary) := by fun_prop
    have hstep : ComputableInPolyTime
        (fun q : ((CNF ℕ × List ℕ) × ℕ) × ℕ =>
          q.1.2 + gadgetCount (occIndices q.1.1.1 (q.1.1.2.getD q.2 0)).length)
        (encPair (encPair (encPair encCNF (encList encNat)) encUnary) encUnary) encUnary := by
      have hget : ComputableInPolyTime
          (fun q : ((CNF ℕ × List ℕ) × ℕ) × ℕ => q.1.1.2.getD q.2 0)
          (encPair (encPair (encPair encCNF (encList encNat)) encUnary) encUnary) encNat := by
        have hg := ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0
        exact hg.comp (((ComputableInPolyTime.snd encCNF (encList encNat)).comp
          ((ComputableInPolyTime.fst (encPair encCNF (encList encNat)) encUnary).comp
            (ComputableInPolyTime.fst
              (encPair (encPair encCNF (encList encNat)) encUnary) encUnary))).prod
          (ComputableInPolyTime.snd
            (encPair (encPair encCNF (encList encNat)) encUnary) encUnary))
      have hφ : ComputableInPolyTime
          (fun q : ((CNF ℕ × List ℕ) × ℕ) × ℕ => q.1.1.1)
          (encPair (encPair (encPair encCNF (encList encNat)) encUnary) encUnary) encCNF :=
        (ComputableInPolyTime.fst encCNF (encList encNat)).comp
          ((ComputableInPolyTime.fst (encPair encCNF (encList encNat)) encUnary).comp
            (ComputableInPolyTime.fst
              (encPair (encPair encCNF (encList encNat)) encUnary) encUnary))
      have hocc : ComputableInPolyTime
          (fun q : ((CNF ℕ × List ℕ) × ℕ) × ℕ => occIndices q.1.1.1 (q.1.1.2.getD q.2 0))
          (encPair (encPair (encPair encCNF (encList encNat)) encUnary) encUnary) (encList encNat)
            :=
        computableInPolyTime_occIndices.comp (hφ.prod hget)
      have hlen : ComputableInPolyTime
          (fun q : ((CNF ℕ × List ℕ) × ℕ) × ℕ =>
            (occIndices q.1.1.1 (q.1.1.2.getD q.2 0)).length)
          (encPair (encPair (encPair encCNF (encList encNat)) encUnary) encUnary) encUnary :=
        (ComputableInPolyTime.length_list encNat).comp hocc
      have hgc : ComputableInPolyTime gadgetCount encUnary encUnary := by
        unfold gadgetCount; fun_prop
      have hgc' := hgc.comp hlen
      have hacc : ComputableInPolyTime
          (fun q : ((CNF ℕ × List ℕ) × ℕ) × ℕ => q.1.2)
          (encPair (encPair (encPair encCNF (encList encNat)) encUnary) encUnary) encUnary :=
        (ComputableInPolyTime.snd (encPair encCNF (encList encNat)) encUnary).comp
          (ComputableInPolyTime.fst
            (encPair (encPair encCNF (encList encNat)) encUnary) encUnary)
      exact ComputableInPolyTime.unary_add.comp (hacc.prod hgc')
    have hB : PolyBounded
        (fun p : (CNF ℕ × List ℕ) × ℕ =>
          (encPair (encPair encCNF (encList encNat)) encUnary p).length)
        (fun p => 3 * p.2) := by
      have hlen : ComputableInPolyTime (fun p : (CNF ℕ × List ℕ) × ℕ => 3 * p.2)
          (encPair (encPair encCNF (encList encNat)) encUnary) encUnary := by fun_prop
      simpa only [encUnary_apply, List.length_replicate] using hlen.polyBounded_length
    refine ComputableInPolyTime.foldlWith (encA := encUnary) (encL := encList encUnary)
      (encB := encUnary) (encP := encPair encCNF (encList encNat))
      (step := fun par acc k => acc + gadgetCount (occIndices par.1 (par.2.getD k 0)).length)
      (ComputableInPolyTime.fst (encPair encCNF (encList encNat)) encUnary)
      hlist (ComputableInPolyTime.const 0) hstep hB (fun p i hi => ?_)
    have hfold_le : ∀ n, ((List.range n).foldl
        (fun acc k => acc + gadgetCount (occIndices p.1.1 (p.1.2.getD k 0)).length) 0) ≤
        3 * n := by
      intro n
      induction n with
      | zero => simp
      | succ n' ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        have : gadgetCount (occIndices p.1.1 (p.1.2.getD n' 0)).length ≤ 3 := by
          unfold gadgetCount; split_ifs <;> omega
        omega
    have htake : (List.range p.2).take i = List.range i := by
      rw [List.length_range] at hi
      rw [List.take_range, Nat.min_eq_left hi]
    rw [htake, encUnary_apply, List.length_replicate]
    exact (hfold_le i).trans (by rw [List.length_range] at hi; omega)
  exact hfold.of_enc_eq fun p => by
    congr 1
    induction p.2 with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ← ih]
      rfl

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_varClauses_comp {α : Type} {enc : α ↪ List Bool}
    {m base : α → ℕ} {occ : α → List ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hbase : ComputableInPolyTime base enc encNat)
    (hocc : ComputableInPolyTime occ enc (encList encNat)) :
    ComputableInPolyTime (fun x => varClauses (m x) (base x) (occ x)) enc
      (encList (encList encNat)) :=
  computableInPolyTime_varClauses.comp' ((hm.prod hbase).prod hocc)

attribute [local irreducible] encRXC3 encNat encUnary in
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encCNF encRXC3 := by
  have hvs := computableInPolyTime_distinctVars
  have hm : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary := by fun_prop
  have hvs_len : ComputableInPolyTime (fun φ : CNF ℕ => (distinctVars φ).length) encCNF encUnary :=
    (ComputableInPolyTime.length_list encNat).comp' hvs
  have hG : ComputableInPolyTime totalGadgets encCNF encUnary := by
    unfold totalGadgets
    exact computableInPolyTime_gadgetPrefix.comp'
      ((ComputableInPolyTime.id'.prod hvs).prod hvs_len)
  have hclauses : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        (List.range (distinctVars φ).length).flatMap fun k =>
          varClauses φ.length (3 * φ.length + 6 * gadgetPrefix φ (distinctVars φ) k)
            (occIndices φ ((distinctVars φ).getD k 0)))
      encCNF (encList (encList encNat)) := by
    have hrange : ComputableInPolyTime
        (fun φ : CNF ℕ => List.range (distinctVars φ).length) encCNF (encList encUnary) :=
      ComputableInPolyTime.range.comp' hvs_len
    refine ComputableInPolyTime.flatMapWithInput hrange ?_
    have hm_q : ComputableInPolyTime (fun q : CNF ℕ × ℕ => q.1.length)
        (encPair encCNF encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp'
        (hm.comp' (ComputableInPolyTime.fst encCNF encUnary))
    have hvs_q : ComputableInPolyTime (fun q : CNF ℕ × ℕ => distinctVars q.1)
        (encPair encCNF encUnary) (encList encNat) :=
      hvs.comp' (ComputableInPolyTime.fst encCNF encUnary)
    have hgp_q : ComputableInPolyTime
        (fun q : CNF ℕ × ℕ => gadgetPrefix q.1 (distinctVars q.1) q.2)
        (encPair encCNF encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp'
        (computableInPolyTime_gadgetPrefix.comp'
          (((ComputableInPolyTime.fst encCNF encUnary).prod hvs_q).prod
            (ComputableInPolyTime.snd encCNF encUnary)))
    have hbase_q : ComputableInPolyTime
        (fun q : CNF ℕ × ℕ => 3 * q.1.length + 6 * gadgetPrefix q.1 (distinctVars q.1) q.2)
        (encPair encCNF encUnary) encNat := by fun_prop
    have hget : ComputableInPolyTime (fun q : CNF ℕ × ℕ => (distinctVars q.1).getD q.2 0)
        (encPair encCNF encUnary) encNat :=
      ComputableInPolyTime.listGetDWithInput hvs_q (ComputableInPolyTime.snd encCNF encUnary) 0
    have hocc : ComputableInPolyTime
        (fun q : CNF ℕ × ℕ => occIndices q.1 ((distinctVars q.1).getD q.2 0))
        (encPair encCNF encUnary) (encList encNat) :=
      computableInPolyTime_occIndices.comp' ((ComputableInPolyTime.fst encCNF encUnary).prod hget)
    exact computableInPolyTime_varClauses_comp hm_q hbase_q hocc
  have hmain : ComputableInPolyTime
      (fun φ : CNF ℕ =>
        ⟨φ.length + 2 * totalGadgets φ,
          (List.range (distinctVars φ).length).flatMap fun k =>
            varClauses φ.length (3 * φ.length + 6 * gadgetPrefix φ (distinctVars φ) k)
              (occIndices φ ((distinctVars φ).getD k 0))⟩)
      encCNF encRXC3 := by
    have hn_bin : ComputableInPolyTime (fun φ : CNF ℕ => φ.length + 2 * totalGadgets φ)
        encCNF encNat := by
      have hu : ComputableInPolyTime (fun φ : CNF ℕ => φ.length + 2 * totalGadgets φ)
          encCNF encUnary := by fun_prop
      exact ComputableInPolyTime.unary_to_binary.comp hu
    exact encRXC3_mk_polyTime hn_bin hclauses
  have hsyn := PositiveOneInExactThreeSATThree.computableInPolyTime_syntaxCheck
  have hemp : ComputableInPolyTime (fun φ : CNF ℕ => φ.isEmpty) encCNF encBool := by fun_prop
  unfold reduce
  exact (ComputableInPolyTime.ite hsyn
    (ComputableInPolyTime.ite hemp (ComputableInPolyTime.const yesInstance) hmain)
    (ComputableInPolyTime.const noInstance)).of_enc_eq fun φ => by
    simp [totalGadgets]

/-! ### Disjoint-copy scaling for arbitrary `k ∣ n` and `N₀ ≤ n` -/

/-- Shift every element in every clause by `offset`. -/
def shiftClauses (offset : ℕ) (cs : List (List ℕ)) : List (List ℕ) :=
  cs.map fun c => c.map (· + offset)

/-- Duplicate an `RXC3Instance` into `k` disjoint copies (`1 ≤ k`). -/
def duplicate (k : ℕ) (x : RXC3Instance) : RXC3Instance :=
  if wellFormedBool x then
    ⟨k * x.n, (List.range k).flatMap fun r => shiftClauses (r * (3 * x.n)) x.clauses⟩
  else
    noInstance

theorem duplicate_mem_iff {k : ℕ} (hk : 1 ≤ k) (x : RXC3Instance) :
    duplicate k x ∈ RXC3 ↔ x ∈ RXC3 := by
  by_cases hw : wellFormedBool x = true
  · have hwf : x.IsWellFormed := (wellFormedBool_eq_true_iff x).mp hw
    have hdup : duplicate k x =
        ⟨k * x.n, (List.range k).flatMap fun r => shiftClauses (r * (3 * x.n)) x.clauses⟩ := by
      simp [duplicate, hw]
    constructor
    · rintro ⟨_, D, hDsub, hDcov⟩
      rw [hdup] at hDsub hDcov
      refine ⟨hwf, D.filter (· ∈ x.clauses), fun c hc => (Finset.mem_filter.mp hc).2, ?_⟩
      intro u hu
      have hcov_u := hDcov u (by
        have : 3 * x.n ≤ 3 * (k * x.n) := Nat.mul_le_mul_left 3 (Nat.le_mul_of_pos_left _ hk)
        nlinarith)
      rw [← hcov_u]
      congr 1; ext c; simp only [Finset.mem_filter]
      refine ⟨fun ⟨⟨hcD, _⟩, huc⟩ => ⟨hcD, huc⟩, fun ⟨hcD, huc⟩ => ⟨⟨hcD, ?_⟩, huc⟩⟩
      obtain ⟨r, hr, hcr⟩ := List.mem_flatMap.mp (hDsub c hcD)
      rw [List.mem_range] at hr
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hcr
      rcases r with _ | r'
      · simpa using hc0
      · exfalso
        obtain ⟨u0, _, hu0⟩ := List.mem_map.mp huc
        have : 3 * x.n ≤ u0 + (r' + 1) * (3 * x.n) := by
          have := Nat.mul_le_mul_right (3 * x.n) (Nat.succ_le_succ (Nat.zero_le r'))
          nlinarith
        nlinarith
    · rintro ⟨_, D, hDsub, hDcov⟩
      rw [hdup]
      -- Well-formedness + cover of k disjoint copies
      have hshift_nd : ∀ r, (shiftClauses (r * (3 * x.n)) x.clauses).Nodup := fun r => by
        refine hwf.2.2.1.map ?_
        intro c1 c2 h
        exact List.map_injective_iff.mpr (add_left_injective _) h
      have hdup_wf : (duplicate k x).IsWellFormed := by
        rw [hdup]
        refine ⟨by have := hwf.1; nlinarith, ?_, ?_, ?_, ?_⟩
        · rw [List.length_flatMap]
          have : ((List.range k).map fun r =>
              (shiftClauses (r * (3 * x.n)) x.clauses).length) =
              (List.range k).map fun _ => 3 * x.n :=
            List.map_congr_left fun _ _ => by simp [shiftClauses, hwf.2.1]
          rw [this]
          have hsum_c : ∀ (l : List ℕ) (c : ℕ), (l.map fun _ => c).sum = l.length * c := by
            intro l c; induction l with
            | nil => simp
            | cons _ t ih => simp [Nat.succ_mul, Nat.add_comm]
          rw [hsum_c, List.length_range]; ring
        · rw [List.nodup_flatMap]
          refine ⟨fun r _ => hshift_nd r, ?_⟩
          rw [List.pairwise_iff_getElem]
          intro r1 r2 hr1 hr2 hlt
          simp only [List.getElem_range]
          intro c hc1 hc2
          obtain ⟨c1, hc1', rfl⟩ := List.mem_map.mp hc1
          obtain ⟨c2, hc2', heq⟩ := List.mem_map.mp hc2
          have hne0 : c1 ≠ [] := by
            have := (hwf.2.2.2.1 c1 hc1').1; cases c1 <;> simp_all
          obtain ⟨u1, hu1⟩ := List.exists_mem_of_ne_nil c1 hne0
          have hu1_lt := (hwf.2.2.2.1 c1 hc1').2.2 u1 hu1
          have hmem : u1 + r1 * (3 * x.n) ∈ c2.map (· + r2 * (3 * x.n)) := by
            rw [heq]; exact List.mem_map_of_mem hu1
          obtain ⟨u2, hu2, hu2_eq⟩ := List.mem_map.mp hmem
          have hu2_lt := (hwf.2.2.2.1 c2 hc2').2.2 u2 hu2
          have h1 : (r1 + 1) * (3 * x.n) ≤ r2 * (3 * x.n) :=
            Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
          nlinarith
        · intro c hc
          obtain ⟨r, hr, hcr⟩ := List.mem_flatMap.mp hc
          rw [List.mem_range] at hr
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hcr
          have h0 := hwf.2.2.2.1 c0 hc0
          refine ⟨by simp [h0.1], h0.2.1.map (add_left_injective _), fun u hu => ?_⟩
          obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
          have hu0_lt := h0.2.2 u0 hu0
          have hle : (r + 1) * (3 * x.n) ≤ k * (3 * x.n) :=
            Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr)
          nlinarith
        · intro u hu
          have hflat : ∀ (L : List ℕ),
              (((L.flatMap fun r => shiftClauses (r * (3 * x.n)) x.clauses).filter
                (fun c => decide (u ∈ c))).length) =
              (L.map fun r => ((shiftClauses (r * (3 * x.n)) x.clauses).filter
                (fun c => decide (u ∈ c))).length).sum := by
            intro L; induction L with
            | nil => simp
            | cons a t ih => simp [List.filter_append, ih]
          rw [hflat]
          set q := u / (3 * x.n)
          set rem := u % (3 * x.n)
          have hpos3n : 0 < 3 * x.n := by have := hwf.1; omega
          have hq : q < k := Nat.div_lt_of_lt_mul (by nlinarith)
          have hrem : rem < 3 * x.n := Nat.mod_lt u hpos3n
          have hu_eq : u = rem + q * (3 * x.n) := by
            have := Nat.div_add_mod u (3 * x.n); rw [Nat.mul_comm] at this
            dsimp only [q, rem]; omega
          have honly : ∀ r < k, r ≠ q →
              ((shiftClauses (r * (3 * x.n)) x.clauses).filter
                (fun c => decide (u ∈ c))).length = 0 := by
            intro r hr hne
            rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro c hc; simp only [decide_eq_true_eq]; intro huc
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
            obtain ⟨u0, hu0, hu0_eq⟩ := List.mem_map.mp huc
            have hu0_lt := (hwf.2.2.2.1 c0 hc0).2.2 u0 hu0
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · have : (r + 1) * (3 * x.n) ≤ q * (3 * x.n) :=
                Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
              nlinarith
            · have : (q + 1) * (3 * x.n) ≤ r * (3 * x.n) :=
                Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hgt)
              nlinarith
          have hsum_single : ∀ (n q' : ℕ) (f : ℕ → ℕ), q' < n → (∀ r < n, r ≠ q' → f r = 0) →
              ((List.range n).map f).sum = f q' := by
            intro n q' f hqn hz
            induction n with
            | zero => omega
            | succ n' ih =>
              rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                List.sum_singleton]
              by_cases heq : q' = n'
              · subst heq
                have h0 : ((List.range q').map f).sum = 0 :=
                  List.sum_eq_zero fun y hy => by
                    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
                    exact hz j (by rw [List.mem_range] at hj; omega)
                      (by rw [List.mem_range] at hj; omega)
                omega
              · rw [hz n' (Nat.lt_succ_self _) (Ne.symm heq),
                  ih (by omega) (fun r hr => hz r (by omega))]
                omega
          rw [hsum_single k q _ hq honly]
          have hfilt_shift :
              ((shiftClauses (q * (3 * x.n)) x.clauses).filter (fun c => decide (u ∈ c))).length =
              (x.clauses.filter (fun c => decide (rem ∈ c))).length := by
            unfold shiftClauses
            rw [List.filter_map, List.length_map]
            congr 1
            refine List.filter_congr fun c _ => ?_
            simp only [Function.comp_apply, decide_eq_decide, List.mem_map]
            exact ⟨fun ⟨a, ha, heq⟩ => (show a = rem by omega) ▸ ha,
              fun h => ⟨rem, h, hu_eq.symm⟩⟩
          rw [hfilt_shift]
          exact hwf.2.2.2.2 rem hrem
      rw [hdup] at hdup_wf
      refine ⟨hdup_wf, (Finset.range k).biUnion fun r =>
          D.image (fun c => c.map (· + r * (3 * x.n))), ?_, ?_⟩
      · intro c hc
        obtain ⟨r, hr, c0, hc0, rfl⟩ := by
          simpa only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] using hc
        exact List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
          List.mem_map.mpr ⟨c0, hDsub c0 hc0, rfl⟩⟩
      · intro u hu
        have hpos3n : 0 < 3 * x.n := by have := hwf.1; omega
        set q := u / (3 * x.n)
        set rem := u % (3 * x.n)
        have hq : q < k := Nat.div_lt_of_lt_mul (by nlinarith)
        have hrem : rem < 3 * x.n := Nat.mod_lt u hpos3n
        have hu_eq : u = rem + q * (3 * x.n) := by
          have := Nat.div_add_mod u (3 * x.n); rw [Nat.mul_comm] at this
          dsimp only [q, rem]; omega
        have hcov_rem := hDcov rem hrem
        obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp hcov_rem
        have hm0 : c0 ∈ D.filter (fun c => rem ∈ c) := hc0 ▸ Finset.mem_singleton_self c0
        have hc0D : c0 ∈ D := (Finset.mem_filter.mp hm0).1
        have hrem_c0 : rem ∈ c0 := (Finset.mem_filter.mp hm0).2
        rw [Finset.card_eq_one]
        refine ⟨c0.map (· + q * (3 * x.n)), ?_⟩
        ext c
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨r, hr, c1, hc1D, rfl⟩, huc⟩
          obtain ⟨u1, hu1, hu1_eq⟩ := List.mem_map.mp huc
          have hu1_lt := (hwf.2.2.2.1 c1 (hDsub c1 hc1D)).2.2 u1 hu1
          have hrq : r = q := by
            by_contra hne
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · have := Nat.mul_le_mul_right (3 * x.n) (Nat.succ_le_of_lt hlt); nlinarith
            · have := Nat.mul_le_mul_right (3 * x.n) (Nat.succ_le_of_lt hgt); nlinarith
          subst hrq
          have hu1_rem : u1 = rem := by omega
          subst hu1_rem
          have hc1_eq : c1 = c0 := by
            have : c1 ∈ D.filter (rem ∈ ·) := Finset.mem_filter.mpr ⟨hc1D, hu1⟩
            rw [hc0] at this; exact Finset.mem_singleton.mp this
          rw [hc1_eq]
        · rintro rfl
          exact ⟨⟨q, hq, c0, hc0D, rfl⟩, List.mem_map.mpr ⟨rem, hrem_c0, hu_eq.symm⟩⟩
  · have hwf : ¬ x.IsWellFormed := by rwa [← wellFormedBool_eq_true_iff]
    simp only [duplicate, hw]
    exact ⟨fun h => absurd h noInstance_notMem, fun h => absurd h.1 hwf⟩

attribute [local irreducible] encRXC3 encNat encUnary in
private theorem computableInPolyTime_duplicate (k : ℕ) :
    ComputableInPolyTime (duplicate k) encRXC3 encRXC3 := by
  have hshift : ComputableInPolyTime
      (fun p : ℕ × List (List ℕ) => shiftClauses p.1 p.2)
      (encPair encNat (encList (encList encNat))) (encList (encList encNat)) := by
    unfold shiftClauses
    have hinner : ComputableInPolyTime (fun q : ℕ × List ℕ => q.2.map (· + q.1))
        (encPair encNat (encList encNat)) (encList encNat) := by
      have hadd : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 + p.1)
          (encPair encNat encNat) encNat := by fun_prop
      exact ComputableInPolyTime.mapWith hadd
        (ComputableInPolyTime.fst encNat (encList encNat))
        (ComputableInPolyTime.snd encNat (encList encNat))
    exact ComputableInPolyTime.mapWith hinner
      (ComputableInPolyTime.fst encNat (encList (encList encNat)))
      (ComputableInPolyTime.snd encNat (encList (encList encNat)))
  have hflat : ComputableInPolyTime
      (fun x : RXC3Instance =>
        (List.range k).flatMap fun r => shiftClauses (r * (3 * x.n)) x.clauses)
      encRXC3 (encList (encList encNat)) := by
    have hstep : ComputableInPolyTime
        (fun p : RXC3Instance × ℕ => shiftClauses (p.2 * (3 * p.1.n)) p.1.clauses)
        (encPair encRXC3 encNat) (encList (encList encNat)) := by
      have h1 : ComputableInPolyTime (fun p : RXC3Instance × ℕ => p.2 * (3 * p.1.n))
          (encPair encRXC3 encNat) encNat := by fun_prop
      have h2 : ComputableInPolyTime (fun p : RXC3Instance × ℕ => p.1.clauses)
          (encPair encRXC3 encNat) (encList (encList encNat)) :=
        encRXC3_clauses_polyTime (ComputableInPolyTime.fst encRXC3 encNat)
      exact hshift.comp (h1.prod h2)
    exact ComputableInPolyTime.flatMapWith hstep ComputableInPolyTime.id'
      (ComputableInPolyTime.const (List.range k))
  have hmain : ComputableInPolyTime
      (fun x : RXC3Instance =>
        ⟨k * x.n, (List.range k).flatMap fun r => shiftClauses (r * (3 * x.n)) x.clauses⟩)
      encRXC3 encRXC3 := by
    have h1 : ComputableInPolyTime (fun x : RXC3Instance => k * x.n) encRXC3 encNat := by
      fun_prop
    exact encRXC3_mk_polyTime h1 hflat
  unfold duplicate
  exact ComputableInPolyTime.ite computableInPolyTime_wellFormedBool hmain
    (ComputableInPolyTime.const noInstance)

end RXC3

open RXC3 in
/-- **RXC3 is in NP**: a certificate selects the clauses of an exact cover. -/
theorem RXC3_mem_NP : RXC3 ∈ NP encRXC3 := by
  convert mem_NP_of_subsetWitness (enc := encRXC3) (encγ := encList encNat)
    (vs := fun x => x.clauses) (check := checkCover)
    (P := fun x D => x.IsWellFormed ∧ ∀ u < 3 * x.n, (D.filter (u ∈ ·)).card = 1)
    (by fun_prop) computableInPolyTime_checkCover (fun x l hl _ => checkCover_iff x l hl) using 1
  ext x
  simp only [RXC3, RXC3Instance.IsExactCover, Set.mem_ofPred_eq]
  tauto

open RXC3 in
/-- `PositiveOneInExactThreeSATThree` reduces to `RXC3` in polynomial time. -/
theorem polyTimeReducible_PositiveOneInExactThreeSATThree_RXC3 :
    PolyTimeReducible encCNF encRXC3 PositiveOneInExactThreeSATThree RXC3 :=
  ⟨reduce, computableInPolyTime_reduce, fun φ => (reduce_mem_iff φ).symm⟩

/-- **RXC3 is NP-hard**. -/
theorem RXC3_npHard : NPHard encRXC3 RXC3 :=
  PositiveOneInExactThreeSATThree_npHard.trans
    polyTimeReducible_PositiveOneInExactThreeSATThree_RXC3

/-- **RXC3 is NP-complete**. -/
theorem RXC3_npComplete : NPComplete encRXC3 RXC3 :=
  ⟨RXC3_mem_NP, RXC3_npHard⟩

/-- **Scaled RXC3 is NP-complete** for any fixed modulus `k ≥ 1` and threshold `N₀`. -/
theorem RXC3Scaled_npComplete {k : ℕ} (hk : 1 ≤ k) (N₀ : ℕ) :
    NPComplete encRXC3 (RXC3Scaled k N₀) := by
  set K := k * (N₀ + 1) with hK_def
  have hK : 1 ≤ K := by nlinarith
  have hmem : RXC3Scaled k N₀ ∈ NP encRXC3 := by
    have hcheck : ComputableInPolyTime
        (fun x : RXC3Instance => decide (x.n % k = 0) && decide (N₀ ≤ x.n))
        encRXC3 encBool := by
      have hmod : ComputableInPolyTime (fun x : RXC3Instance => x.n % k) encRXC3 encNat :=
        ComputableInPolyTime.binary_mod.comp
          ((by fun_prop : ComputableInPolyTime (fun x : RXC3Instance => x.n) encRXC3 encNat).prod
            (ComputableInPolyTime.const k))
      have hd1 : ComputableInPolyTime (fun x : RXC3Instance => decide (x.n % k = 0))
          encRXC3 encBool :=
        ComputableInPolyTime.decide_eq' hmod (ComputableInPolyTime.const 0)
      have hd2 : ComputableInPolyTime (fun x : RXC3Instance => decide (N₀ ≤ x.n))
          encRXC3 encBool := by fun_prop
      exact ComputableInPolyTime.bool_and.comp (hd1.prod hd2)
    have ⟨p, V, hV, hisV⟩ := RXC3_mem_NP
    refine ⟨p, fun q => (decide (q.1.n % k = 0) && decide (N₀ ≤ q.1.n)) && V q, ?_, ?_⟩
    · have hc := hcheck.comp (ComputableInPolyTime.fst encRXC3 encBits)
      fun_prop
    · intro x
      simp only [RXC3Scaled, Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq,
        Nat.dvd_iff_mod_eq_zero, hisV x]
      constructor
      · rintro ⟨⟨w, hw, hVw⟩, hmod, hle⟩
        exact ⟨w, hw, ⟨hmod, hle⟩, hVw⟩
      · rintro ⟨w, hw, ⟨hmod, hle⟩, hVw⟩
        exact ⟨⟨w, hw, hVw⟩, hmod, hle⟩
  refine ⟨hmem, RXC3_npHard.trans ⟨RXC3.duplicate K, RXC3.computableInPolyTime_duplicate K, ?_⟩⟩
  intro x
  constructor
  · intro hx
    refine ⟨(RXC3.duplicate_mem_iff hK x).mpr hx, ?_, ?_⟩
    · have hw : RXC3.wellFormedBool x = true :=
        (RXC3.wellFormedBool_eq_true_iff x).mpr hx.1
      simp only [RXC3.duplicate, hw, ↓reduceIte, hK_def, mul_assoc]
      exact dvd_mul_right k _
    · have hw : RXC3.wellFormedBool x = true :=
        (RXC3.wellFormedBool_eq_true_iff x).mpr hx.1
      simp only [RXC3.duplicate, hw, ↓reduceIte, hK_def]
      have hx1 : 1 ≤ x.n := hx.1.1
      nlinarith
  · intro hx
    exact (RXC3.duplicate_mem_iff hK x).mp hx.1

end CslibFrontier.Complexity
