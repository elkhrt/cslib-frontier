/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.Complexity.Problems.SAT

import CslibFrontier.Computability.Complexity.Classes.BPP.Reduction
import CslibFrontier.Computability.Complexity.Classes.NP.SelfReduction
import CslibFrontier.Computability.Complexity.Classes.RP.Reduction
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith

/-!
# Self-reducibility collapse of `NP ∩ BPP` to `RP`

If `SAT` belongs to `BPP`, then `SAT` belongs to `RP`, and consequently `RP = NP` on every encoded
instance type. The proof runs the
deterministic polynomial-time downward self-reduction `Cslib.Complexity.SAT.search` against an
exponentially amplified `BPP` decider for `SAT`, and then verifies the candidate truth assignment
deterministically via `Cslib.Complexity.SAT.verifier` so that unsatisfiable formulas have zero
acceptance probability.

## Main results

* `Cslib.Complexity.sat_mem_RP_of_mem_BPP`: if `SAT ∈ BPP encCNF`, then `SAT ∈ RP encCNF`.
* `Cslib.Complexity.RP_eq_NP_of_SAT_mem_BPP`: if `SAT ∈ BPP encCNF`, then `RP enc = NP enc`
  for every injective binary encoding `enc`.
* `Cslib.Complexity.RP_eq_NP_of_NP_subset_BPP`: if `NP encCNF ⊆ BPP encCNF`, then
  `RP enc = NP enc` for every injective binary encoding `enc`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM
open scoped BigOperators

private lemma polynomial_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a b hab
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add (hp hab) (hq hab)
  | monomial d c =>
    intro a b hab
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab d)

private noncomputable def satQueryBoundPoly : Polynomial ℕ :=
  Polynomial.X + (Polynomial.X + 1) * (8 * Polynomial.X + 11)

private lemma eval_satQueryBoundPoly (L : ℕ) :
    satQueryBoundPoly.eval L = SAT.queryBound L := by
  simp [satQueryBoundPoly, SAT.queryBound]

private def prefixAnswers (φ : CNF ℕ) (k : ℕ) (bits : Fin k → Bool) : List (Literal ℕ) :=
  List.ofFn fun i : Fin k => (φ.vars.getD i.1 0, bits i)

private def branchQuery (φ : CNF ℕ) (k : Fin φ.vars.length) (bits : Fin k.1 → Bool) : CNF ℕ :=
  φ ++ SAT.units (prefixAnswers φ k.1 bits) ++ [[(φ.vars[k.1], true)]]

private lemma length_encCNF_le_branchQuery (φ : CNF ℕ) (k : Fin φ.vars.length)
    (bits : Fin k.1 → Bool) :
    (encCNF φ).length ≤ (encCNF (branchQuery φ k bits)).length := by
  simp only [branchQuery, SAT.length_encCNF_append]
  omega

private lemma length_branchQuery_le (φ : CNF ℕ) (k : Fin φ.vars.length)
    (bits : Fin k.1 → Bool) :
    (encCNF (branchQuery φ k bits)).length ≤ SAT.queryBound (encCNF φ).length := by
  have hmem : ∀ l ∈ prefixAnswers φ k.1 bits, l.1 ∈ φ.vars := by
    intro l hl
    simp only [prefixAnswers, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    have hi : i.1 < φ.vars.length := i.2.trans k.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hunits := SAT.length_encCNF_units_le hmem
  have hv := SAT.length_encCNF_unit_le (φ := φ) (l := (φ.vars[k.1], true)) (List.getElem_mem k.2)
  have hlen : (prefixAnswers φ k.1 bits).length ≤ (encCNF φ).length := by
    simp only [prefixAnswers, List.length_ofFn]
    exact k.2.le.trans (SAT.length_vars_le φ)
  have hmul := Nat.mul_le_mul_right (8 * (encCNF φ).length + 11) hlen
  simp only [branchQuery, SAT.length_encCNF_append, SAT.queryBound]
  nlinarith

private lemma card_branchIndex_lt_two_pow (m : ℕ) :
    Fintype.card (Σ k : Fin m, (Fin k.1 → Bool)) < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fintype.card_sigma, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
    have ih' : (∑ i : Fin m, 2 ^ i.1) < 2 ^ m := by
      simpa [Fintype.card_sigma] using ih
    rw [pow_succ']
    omega

private lemma card_filter_take_eq_mul {n m : ℕ} (hnm : n ≤ m) (P : List Bool → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun r : Fin m → Bool => P ((List.ofFn r).take n)).card =
      2 ^ (m - n) * (Finset.univ.filter fun u : Fin n → Bool => P (List.ofFn u)).card := by
  let splitEquiv : (Fin m → Bool) ≃ (Fin n → Bool) × (Fin (m - n) → Bool) :=
    { toFun := fun r => (fun i => r ⟨i.1, i.2.trans_le hnm⟩,
        fun j => r ⟨n + j.1, by omega⟩)
      invFun := fun pq i =>
        if hi : i.1 < n then pq.1 ⟨i.1, hi⟩ else pq.2 ⟨i.1 - n, by omega⟩
      left_inv := fun r => by
        ext i
        by_cases hi : i.1 < n
        · simp [hi]
        · simp only [hi, ↓reduceDIte]
          congr 1
          ext
          dsimp
          omega
      right_inv := fun ⟨p, q⟩ => by
        ext i
        · simp [i.2]
        · have hn : ¬ (n + i.1 < n) := by omega
          simp [hn] }
  have htake : ∀ r : Fin m → Bool, (List.ofFn r).take n = List.ofFn (splitEquiv r).1 := by
    intro r
    apply List.ext_getElem
    · simp [Nat.min_eq_left hnm]
    · intro i hi1 hi2
      simp [splitEquiv]
  have hbij :
      (Finset.univ.filter fun r : Fin m → Bool => P ((List.ofFn r).take n)).card =
        (Finset.univ.filter fun pq : (Fin n → Bool) × (Fin (m - n) → Bool) =>
          P (List.ofFn pq.1)).card := by
    refine Finset.card_bij (fun r _ => splitEquiv r) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rwa [← htake r]
    · intro r₁ _ r₂ _ heq
      exact splitEquiv.injective heq
    · intro pq hpq
      refine ⟨splitEquiv.symm pq, ?_, splitEquiv.apply_symm_apply pq⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpq ⊢
      rwa [htake, splitEquiv.apply_symm_apply]
  rw [hbij]
  have hprod :
      (Finset.univ.filter fun pq : (Fin n → Bool) × (Fin (m - n) → Bool) =>
        P (List.ofFn pq.1)) =
        (Finset.univ.filter fun u : Fin n → Bool => P (List.ofFn u)) ×ˢ
          (Finset.univ : Finset (Fin (m - n) → Bool)) := by
    ext ⟨u, v⟩
    simp
  rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.mul_comm]

private lemma satisfiable_selfReduce_of_branchQueries {D : CNF ℕ → Bool} {φ : CNF ℕ}
    (hD : ∀ (k : Fin φ.vars.length) (bits : Fin k.1 → Bool),
      D (branchQuery φ k bits) = true ↔ branchQuery φ k bits ∈ SAT)
    (hφ : φ ∈ SAT) :
    SAT.verifier (φ, SAT.search D φ) = true := by
  have hfold : ∀ j : ℕ, j ≤ φ.vars.length →
      (φ ++ SAT.units ((φ.vars.take j).foldl (SAT.selfReduceStep D φ) [])).Satisfiable := by
    intro j hj
    induction j with
    | zero => simpa [SAT, SAT.units] using hφ
    | succ j ih =>
      have hj_lt : j < φ.vars.length := Nat.lt_of_succ_le hj
      have hsat_prev := ih hj_lt.le
      set ans := (φ.vars.take j).foldl (SAT.selfReduceStep D φ) []
      have hfst : ans.map Prod.fst = φ.vars.take j := by
        simpa using SAT.map_fst_foldl_selfReduceStep D φ (φ.vars.take j) []
      have hans_len : ans.length = j := by
        have hlen := congrArg List.length hfst
        simpa [Nat.min_eq_left hj_lt.le] using hlen
      let bits : Fin j → Bool := fun i => (ans[i.1]'(by omega)).2
      have hans_eq : ans = prefixAnswers φ j bits := by
        apply List.ext_getElem
        · simp [prefixAnswers, hans_len]
        · intro i hi1 hi2
          have hi_lt : i < j := by omega
          have hi_vars : i < φ.vars.length := hi_lt.trans hj_lt
          have hfst_i : (ans[i]).1 = φ.vars[i] := by
            have h := congrArg (·[i]?) hfst
            simpa [List.getElem?_eq_getElem hi1,
              List.getElem?_take_of_lt hi_lt, List.getElem?_eq_getElem hi_vars] using h
          ext
          · simp [prefixAnswers, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_vars,
              hfst_i]
          · simp [prefixAnswers, bits]
      have htake_succ : φ.vars.take (j + 1) = φ.vars.take j ++ [φ.vars[j]] :=
        List.take_succ_eq_append_getElem hj_lt
      rw [htake_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (φ ++ SAT.units (ans ++ [(φ.vars[j],
        D (φ ++ SAT.units ans ++ [[(φ.vars[j], true)]]))])).Satisfiable
      have hq_eq : φ ++ SAT.units ans ++ [[(φ.vars[j], true)]] = branchQuery φ ⟨j, hj_lt⟩ bits := by
        rw [branchQuery, hans_eq]
      have hiff := hD ⟨j, hj_lt⟩ bits
      rw [← hq_eq] at hiff
      have hunits_app : ∀ b : Bool,
          SAT.units (ans ++ [(φ.vars[j], b)]) = SAT.units ans ++ [[(φ.vars[j], b)]] :=
        fun _ => List.map_append ..
      rw [hunits_app, ← List.append_assoc]
      cases hb : D (φ ++ SAT.units ans ++ [[(φ.vars[j], true)]])
      · obtain ⟨σ, hσ⟩ := hsat_prev
        have hσv : σ φ.vars[j] = false := by
          apply Bool.eq_false_iff.2 fun htrue => Bool.false_ne_true <| hb.symm.trans <| hiff.2 ⟨σ,
            ?_⟩
          rw [CNF.eval_append]
          simp [hσ, htrue]
        exact ⟨σ, by rw [CNF.eval_append]; simp [hσ, hσv]⟩
      · exact hiff.1 hb
  have hfull : (φ ++ SAT.units (SAT.selfReduce D φ)).Satisfiable := by
    simpa [SAT.selfReduce] using hfold φ.vars.length le_rfl
  obtain ⟨σ, hσ⟩ := hfull
  rw [SAT.eval_append_units] at hσ
  have hfst_all : (SAT.selfReduce D φ).map Prod.fst = φ.vars := by
    simpa [SAT.selfReduce] using SAT.map_fst_foldl_selfReduceStep D φ φ.vars []
  refine (CNF.eval_congr fun v hv => ?_).trans hσ.1
  have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.2 hv
  have hlt' : φ.vars.idxOf v < (SAT.selfReduce D φ).length := by
    simpa [← hfst_all] using hlt
  have hfst_v : ((SAT.selfReduce D φ)[φ.vars.idxOf v]).1 = v := by
    have h := congrArg (·[φ.vars.idxOf v]?) hfst_all
    simpa [List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt,
      List.getElem_idxOf hlt] using h
  have hmap_len : φ.vars.idxOf v < ((SAT.selfReduce D φ).map Prod.snd).length := by
    simpa using hlt'
  rw [SAT.assignment, SAT.search, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hmap_len, Option.getD_some,
    List.getElem_map, ← hσ.2 _ (List.getElem_mem hlt'), hfst_v]

/-- **Ko's self-reducibility lemma for `SAT`**: if `SAT` belongs to `BPP`, then `SAT` belongs to
`RP`. Running the downward self-reduction `SAT.search` against an amplified `BPP` procedure with
error `2 ^ (-(|ψ| + 2))` and checking the resulting assignment via `SAT.verifier` eliminates all
false positives while succeeding on at least three quarters (hence at least half) of random tapes
on every satisfiable formula. -/
theorem sat_mem_RP_of_mem_BPP (hSAT : SAT ∈ BPP encCNF) : SAT ∈ RP encCNF := by
  classical
  obtain ⟨p₀, V₀, hV₀, herr⟩ :=
    mem_BPP_iff_forall_decidesWithErrorExponent.1 hSAT (Polynomial.X + 2)
  let p : Polynomial ℕ := p₀.comp satQueryBoundPoly
  let D : List Bool → CNF ℕ → Bool := fun r ψ =>
    V₀ (ψ, r.take (p₀.eval (encCNF ψ).length))
  let V : CNF ℕ × List Bool → Bool := fun x =>
    SAT.verifier (x.1, SAT.search (D x.2) x.1)
  have hD_poly : ComputableInPolyTime
      (fun q : (CNF ℕ × List Bool) × CNF ℕ => D q.1.2 q.2)
      (encPair (encPair encCNF encBits) encCNF) encBool := by
    have hψ : ComputableInPolyTime
        (fun q : (CNF ℕ × List Bool) × CNF ℕ => q.2)
        (encPair (encPair encCNF encBits) encCNF) encCNF := ComputableInPolyTime.snd _ _
    have hlen : ComputableInPolyTime
        (fun q : (CNF ℕ × List Bool) × CNF ℕ => p₀.eval (encCNF q.2).length)
        (encPair (encPair encCNF encBits) encCNF) encUnary :=
      (ComputableInPolyTime.unary_eval p₀).comp
        ((ComputableInPolyTime.encoding_length encCNF).comp hψ)
    have htake : ComputableInPolyTime
        (fun q : (CNF ℕ × List Bool) × CNF ℕ => q.1.2.take (p₀.eval (encCNF q.2).length))
        (encPair (encPair encCNF encBits) encCNF) encBits :=
      ComputableInPolyTime.bitsTakeWithInput
        ((ComputableInPolyTime.snd encCNF encBits).comp (ComputableInPolyTime.fst _ _)) hlen
    exact hV₀.comp (hψ.prod htake)
  have hsearch_poly : ComputableInPolyTime
      (fun x : CNF ℕ × List Bool => SAT.search (D x.2) x.1)
      (encPair encCNF encBits) encBits :=
    SAT.computableInPolyTime_search (D := fun x : CNF ℕ × List Bool => D x.2)
      (φ := Prod.fst) hD_poly (ComputableInPolyTime.fst encCNF encBits)
  have hV_poly : ComputableInPolyTime V (encPair encCNF encBits) encBool :=
    SAT.computableInPolyTime_verifier.comp
      ((ComputableInPolyTime.fst encCNF encBits).prod hsearch_poly)
  refine ⟨p, V, hV_poly, fun φ => ⟨fun hφ => ?_, fun hφ r => ?_⟩⟩
  · set L := (encCNF φ).length
    set N := p.eval L
    let Idx := Σ k : Fin φ.vars.length, (Fin k.1 → Bool)
    let badAt (idx : Idx) : Finset (Fin N → Bool) :=
      Finset.univ.filter fun r : Fin N → Bool =>
        D (List.ofFn r) (branchQuery φ idx.1 idx.2) !=
          decide (branchQuery φ idx.1 idx.2 ∈ SAT)
    have hbad_single : ∀ idx : Idx, 4 * 2 ^ L * (badAt idx).card ≤ 2 ^ N := by
      intro idx
      set ψ := branchQuery φ idx.1 idx.2
      have hL_le : L ≤ (encCNF ψ).length := length_encCNF_le_branchQuery φ idx.1 idx.2
      have hψ_le : (encCNF ψ).length ≤ SAT.queryBound L := length_branchQuery_le φ idx.1 idx.2
      have hp_le : p₀.eval (encCNF ψ).length ≤ N := by
        dsimp only [N, p]
        rw [Polynomial.eval_comp, eval_satQueryBoundPoly]
        exact polynomial_eval_mono p₀ hψ_le
      have hcard_eq : (badAt idx).card =
          2 ^ (N - p₀.eval (encCNF ψ).length) *
            (Finset.univ.filter fun u : Fin (p₀.eval (encCNF ψ).length) → Bool =>
              V₀ (ψ, List.ofFn u) = !decide (ψ ∈ SAT)).card := by
        have hbne : ∀ a b : Bool, ((a != b) = true) ↔ (a = !b) := by decide
        have h := card_filter_take_eq_mul hp_le
          (fun w => V₀ (ψ, w) = !decide (ψ ∈ SAT))
        dsimp only [badAt, D]
        simp_rw [hbne]
        exact h
      have herr_ψ : 2 ^ ((Polynomial.X + 2 : Polynomial ℕ).eval (encCNF ψ).length) *
          (Finset.univ.filter fun u : Fin (p₀.eval (encCNF ψ).length) → Bool =>
            V₀ (ψ, List.ofFn u) = !decide (ψ ∈ SAT)).card ≤
          2 ^ p₀.eval (encCNF ψ).length := by
        by_cases hsat : ψ ∈ SAT
        · simpa [hsat] using (herr ψ).1 hsat
        · simpa [hsat] using (herr ψ).2 hsat
      have hpow_le : 4 * 2 ^ L ≤
        2 ^ ((Polynomial.X + 2 : Polynomial ℕ).eval (encCNF ψ).length) := by
        have h1 : L + 2 ≤ (Polynomial.X + 2 : Polynomial ℕ).eval (encCNF ψ).length := by
          simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
          omega
        calc 4 * 2 ^ L = 2 ^ (L + 2) := by ring
          _ ≤ 2 ^ ((Polynomial.X + 2 : Polynomial ℕ).eval (encCNF ψ).length) :=
              Nat.pow_le_pow_right (by norm_num) h1
      calc 4 * 2 ^ L * (badAt idx).card
          = 2 ^ (N - p₀.eval (encCNF ψ).length) *
              ((4 * 2 ^ L) * (Finset.univ.filter fun u : Fin (p₀.eval (encCNF ψ).length) → Bool =>
                V₀ (ψ, List.ofFn u) = !decide (ψ ∈ SAT)).card) := by
              rw [hcard_eq]
              ring
        _ ≤ 2 ^ (N - p₀.eval (encCNF ψ).length) *
              (2 ^ ((Polynomial.X + 2 : Polynomial ℕ).eval (encCNF ψ).length) *
                (Finset.univ.filter fun u : Fin (p₀.eval (encCNF ψ).length) → Bool =>
                  V₀ (ψ, List.ofFn u) = !decide (ψ ∈ SAT)).card) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow_le)
        _ ≤ 2 ^ (N - p₀.eval (encCNF ψ).length) * 2 ^ p₀.eval (encCNF ψ).length :=
              Nat.mul_le_mul_left _ herr_ψ
        _ = 2 ^ N := by rw [← pow_add, Nat.sub_add_cancel hp_le]
    let badAll : Finset (Fin N → Bool) := Finset.univ.biUnion badAt
    have hsum_le : 4 * 2 ^ L * badAll.card ≤ Fintype.card Idx * 2 ^ N := by
      calc 4 * 2 ^ L * badAll.card
          ≤ 4 * 2 ^ L * ∑ idx : Idx, (badAt idx).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ idx : Idx, 4 * 2 ^ L * (badAt idx).card := by rw [Finset.mul_sum]
        _ ≤ ∑ _idx : Idx, 2 ^ N := Finset.sum_le_sum fun idx _ => hbad_single idx
        _ = Fintype.card Idx * 2 ^ N := by simp
    have hcard_idx : Fintype.card Idx < 2 ^ L :=
      (card_branchIndex_lt_two_pow φ.vars.length).trans_le
        (Nat.pow_le_pow_right (by norm_num) (SAT.length_vars_le φ))
    have hbad_lt : 2 * badAll.card ≤ 2 ^ N := by
      have hmul : Fintype.card Idx * 2 ^ N ≤ 2 ^ L * 2 ^ N :=
        Nat.mul_le_mul_right _ hcard_idx.le
      have hpos : 0 < 2 ^ L := Nat.pos_of_ne_zero (by positivity)
      have h4 : 4 * badAll.card * 2 ^ L ≤ 1 * 2 ^ N * 2 ^ L := by
        nlinarith [hsum_le, hmul]
      have h4' : 4 * badAll.card ≤ 2 ^ N := by
        simpa using Nat.le_of_mul_le_mul_right h4 hpos
      omega
    have hsub : (Finset.univ.filter fun r : Fin N → Bool => V (φ, List.ofFn r) = false) ⊆
        badAll := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      by_contra hnot
      simp only [badAll, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists, badAt,
        Finset.mem_filter] at hnot
      have hexact : ∀ (k : Fin φ.vars.length) (bits : Fin k.1 → Bool),
          D (List.ofFn r) (branchQuery φ k bits) = true ↔
            branchQuery φ k bits ∈ SAT := by
        intro k bits
        have h := hnot ⟨k, bits⟩
        cases hDval : D (List.ofFn r) (branchQuery φ k bits) <;>
          by_cases hsat : branchQuery φ k bits ∈ SAT <;> simp_all
      have hv := satisfiable_selfReduce_of_branchQueries hexact hφ
      exact Bool.false_ne_true (hr.symm.trans hv)
    have hfalse_le : 2 * (Finset.univ.filter fun r : Fin N → Bool =>
        V (φ, List.ofFn r) = false).card ≤ 2 ^ N :=
      (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans hbad_lt
    have hpart := acceptCount_add_card_filter_eq_false (V := V) (a := φ) (n := N)
    omega
  · by_contra htrue
    have hv : V (φ, List.ofFn r) = true := Bool.eq_true_of_not_eq_false htrue
    exact hφ ⟨_, hv⟩

/-- **Collapse of `NP` to `RP` from `SAT ∈ BPP`**: if `SAT` admits a `BPP` algorithm, then
`RP enc = NP enc` for every type `α` and injective encoding `enc : α ↪ List Bool`. -/
theorem RP_eq_NP_of_SAT_mem_BPP (hSAT : SAT ∈ BPP encCNF) {α : Type} (enc : α ↪ List Bool) :
    RP enc = NP enc := by
  have hSAT_RP : SAT ∈ RP encCNF := sat_mem_RP_of_mem_BPP hSAT
  refine Set.Subset.antisymm RP_subset_NP fun A hA => ?_
  exact (CookLevin.SAT_npHard enc A hA).mem_RP hSAT_RP

/-- **Ko's Theorem (`NP ⊆ BPP → RP = NP`)**: if every `NP` problem over CNF formulas lies in
`BPP`, then `RP enc = NP enc` for every type `α` and injective encoding `enc : α ↪ List Bool`. -/
theorem RP_eq_NP_of_NP_subset_BPP (hsub : NP encCNF ⊆ BPP encCNF) {α : Type}
    (enc : α ↪ List Bool) : RP enc = NP enc :=
  RP_eq_NP_of_SAT_mem_BPP (hsub CookLevin.SAT_npComplete.1) enc

end Cslib.Complexity
