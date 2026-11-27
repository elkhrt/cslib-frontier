/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ExistsReal
public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Logics.RealArithmetic.Basic
public import CslibFrontier.Logics.RealArithmetic.Encoding
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.CircuitCompilation
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.HardnessGates
import CslibFrontier.Logics.RealArithmetic.FormulaTokenDecoding
import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
import CslibFrontier.Logics.RealArithmetic.TermTokenDecoding
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ETR-to-Circuit Compilation and `ARM(3)` Many-One Reduction

Equisatisfiability and polynomial size bounds for the stack compiler from `ETR` formula
words to arithmetic circuits, and the many-one reduction `etrWordToARM3 : List Bool → ARMInstance`.
-/

public section

namespace Cslib.Complexity

open Matrix Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM

private def FormulaCompileSpec (n : ℕ) (p : Formula n) (stack zeros : List ℕ)
    (gates : List ArithGate) (nextSlack : ℕ) (hn : n ≤ nextSlack)
    (res : FormulaCompileState) : Prop :=
  ∃ (bp : ℕ) (newZeros : List ℕ) (hslack : nextSlack ≤ res.2.2.2),
    res.1 = bp :: stack ∧
    res.2.1 = newZeros ++ zeros ∧
    bp < res.2.2.1.length ∧
    (∀ g ∈ newZeros, g < res.2.2.1.length) ∧
    gates <+: res.2.2.1 ∧
    (∀ k (hk : k < res.2.2.1.length), res.2.2.1[k].WellFormed res.2.2.2 k) ∧
    (∀ (x : Fin n → ℝ),
      (∃ ext : Fin (res.2.2.2 - nextSlack) → ℝ,
        ∀ (y : Fin res.2.2.2 → ℝ),
          (∀ i : Fin n, y ⟨i.1, i.2.trans_le (hn.trans hslack)⟩ = x i) →
          (∀ j : Fin (res.2.2.2 - nextSlack), y ⟨nextSlack + j.1, by omega⟩ = ext j) →
          (∀ g ∈ newZeros, (evalGatesList y res.2.2.1).getD g 0 = 0) ∧
          (x ∈ p.solutionSet → (evalGatesList y res.2.2.1).getD bp 0 = 1) ∧
          (x ∉ p.solutionSet → (evalGatesList y res.2.2.1).getD bp 0 = 0))) ∧
    (∀ (y : Fin res.2.2.2 → ℝ),
      (∀ g ∈ newZeros, (evalGatesList y res.2.2.1).getD g 0 = 0) →
        let x := fun i : Fin n ↦ y ⟨i.1, i.2.trans_le (hn.trans hslack)⟩
        (x ∈ p.solutionSet → (evalGatesList y res.2.2.1).getD bp 0 = 1) ∧
        (x ∉ p.solutionSet → (evalGatesList y res.2.2.1).getD bp 0 = 0))

private theorem formula_compile_correct {n : ℕ} (p : Formula n)
    (stack zeros : List ℕ) (gates : List ArithGate) (nextSlack : ℕ)
    (hn : n ≤ nextSlack)
    (hwf : ∀ k (hk : k < gates.length), gates[k].WellFormed nextSlack k)
    (hstack : ∀ g ∈ stack, g < gates.length)
    (hzeros : ∀ g ∈ zeros, g < gates.length) :
    FormulaCompileSpec n p stack zeros gates nextSlack hn
      (((encFormula_tokens n p).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack)) := by
  induction p generalizing stack zeros gates nextSlack with
  | false =>
    have hfold : ((encFormula_tokens n .false).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack) =
        (gates.length :: stack, zeros, gates ++ [.const 0], nextSlack) := by
      simp only [encFormula_tokens, List.map_singleton, List.reverse_singleton,
        List.foldl_cons, List.foldl_nil, compileFormulaTokenStep_false]
    rw [hfold]
    dsimp only [FormulaCompileSpec]
    refine ⟨gates.length, [], le_rfl, rfl, rfl, by simp, fun _ h ↦ by simp at h,
      by simp, ?_, ?_, ?_⟩
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      by_cases hlt : k < gates.length
      · rw [List.getElem_append_left hlt]; exact hwf k hlt
      · have heq : k = gates.length := by omega
        subst heq; simp
    · intro x
      refine ⟨fun _ ↦ 0, fun y _ _ ↦ ⟨fun _ h ↦ by simp at h,
        fun h ↦ by simp [Formula.solutionSet] at h,
        fun _ ↦ by rw [evalGatesList_snoc_last]; simp⟩⟩
    · intro y _
      exact ⟨fun h ↦ by simp [Formula.solutionSet] at h,
        fun _ ↦ by rw [evalGatesList_snoc_last]; simp⟩
  | eqZero t =>
    obtain ⟨gt, hst, hgt_lt, hpref_t, hwf_t, heval_t⟩ :=
      compileTermTokens_correct hn t [] gates hwf (fun _ h ↦ by simp at h)
    set resT := ((encTerm_tokens n t).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep ([], gates)
    set k := resT.2.length
    have hgt_eq : resT.1.headD 0 = gt := by rw [hst]; rfl
    have hfold : ((encFormula_tokens n (.eqZero t)).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack) =
        (k :: stack, [k + 5, k + 6, k + 10] ++ zeros,
          resT.2 ++ eqZeroGateBlock k gt nextSlack, nextSlack + 2) := by
      simp only [encFormula_tokens, List.map_singleton, List.reverse_singleton,
        List.foldl_cons, List.foldl_nil, compileFormulaTokenStep_eqZero,
        termTokensDecoder_decode_encTerm, Option.getD_some, compileTermTokens_eq_foldl]
      change (resT.2.length :: stack,
          [resT.2.length + 5, resT.2.length + 6, resT.2.length + 10] ++ zeros,
          resT.2 ++ eqZeroGateBlock resT.2.length (resT.1.headD 0) nextSlack, nextSlack + 2) = _
      rw [hgt_eq]
    rw [hfold]
    dsimp only [FormulaCompileSpec]
    refine ⟨k, [k + 5, k + 6, k + 10], by omega, rfl, rfl,
      by simp only [eqZeroGateBlock_length, List.length_append]; omega,
      ?_, hpref_t.trans (List.prefix_append _ _), ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;>
        (simp only [eqZeroGateBlock_length, List.length_append]; omega)
    · intro j hj
      simp only [List.length_append] at hj ⊢
      by_cases hlt : j < k
      · rw [List.getElem_append_left hlt]
        have h := hwf_t j hlt
        cases hg : resT.2[j] with
        | input idx => rw [hg] at h; simp at h ⊢; omega
        | const _ => simp
        | add _ _ => rw [hg] at h; exact h
        | mul _ _ => rw [hg] at h; exact h
        | neg _ => rw [hg] at h; exact h
      · rw [List.getElem_append_right (Nat.le_of_not_lt hlt)]
        have hblen : (eqZeroGateBlock k gt nextSlack).length = 11 := rfl
        have : ∀ idx (hidx : idx < 11), j = k + idx →
            (eqZeroGateBlock k gt nextSlack)[idx].WellFormed (nextSlack + 2) j := by
          intro idx hidx hjk
          subst hjk; exact eqZeroGateBlock_wellFormed hgt_lt idx hidx
        exact this (j - k) (by omega) (by omega)
    · intro x
      classical
      let tv : ℝ := t.eval x
      let bv : ℝ := if tv = 0 then 1 else 0
      let vv : ℝ := if tv = 0 then 0 else tv⁻¹
      refine ⟨fun j ↦ if j.1 = 0 then bv else vv, fun y hy hext ↦ ?_⟩
      have hyx : (fun i : Fin n ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) = x := funext hy
      have hyb : y ⟨nextSlack, by omega⟩ = bv := by simpa using hext ⟨0, by omega⟩
      have hyv : y ⟨nextSlack + 1, by omega⟩ = vv := by simpa using hext ⟨1, by omega⟩
      obtain ⟨h0, h5, h6, h10⟩ :=
        eval_eqZeroGateBlock y resT.2 hgt_lt (by omega : nextSlack + 1 < _)
      have htv : (evalGatesList y resT.2).getD gt 0 = tv := by
        rw [evalGatesList_restrict_eq (by omega : nextSlack ≤ nextSlack + 2) y resT.2 hwf_t,
          heval_t, hyx]
      refine ⟨fun g hg ↦ ?_, fun hx ↦ ?_, fun hx ↦ ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl
        · rw [h5, hyb]; dsimp [bv]; split_ifs <;> ring
        · rw [h6, hyb, htv]; dsimp [bv]; split_ifs with h <;> simp [h]
        · rw [h10, hyb, hyv, htv]; dsimp [bv, vv]; split_ifs with h
          · ring
          · rw [mul_inv_cancel₀ h]; ring
      · have htv0 : tv = 0 := hx
        rw [h0, hyb]; simp [bv, htv0]
      · have htv0 : tv ≠ 0 := hx
        rw [h0, hyb]; simp [bv, htv0]
    · intro y hz
      obtain ⟨h0, h5, h6, h10⟩ :=
        eval_eqZeroGateBlock y resT.2 hgt_lt (by omega : nextSlack + 1 < _)
      have hz5 : y ⟨nextSlack, by omega⟩ * (1 - y ⟨nextSlack, by omega⟩) = 0 := by
        rw [← h5]; exact hz (k + 5) (by simp)
      have hz6 : y ⟨nextSlack, by omega⟩ * (evalGatesList y resT.2).getD gt 0 = 0 := by
        rw [← h6]; exact hz (k + 6) (by simp)
      have hz10 : (1 - y ⟨nextSlack, by omega⟩) *
          ((evalGatesList y resT.2).getD gt 0 * y ⟨nextSlack + 1, by omega⟩ - 1) = 0 := by
        rw [← h10]; exact hz (k + 10) (by simp)
      have htv : (evalGatesList y resT.2).getD gt 0 =
          t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) := by
        rw [evalGatesList_restrict_eq (by omega : nextSlack ≤ nextSlack + 2) y resT.2 hwf_t,
          heval_t]
      rw [htv] at hz6 hz10
      rw [h0]
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · have htv0 : t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) = 0 := hx
        rcases mul_eq_zero.mp hz5 with hb0 | hb1
        · rw [hb0, htv0] at hz10; norm_num at hz10
        · linarith
      · have htv0 : t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) ≠ 0 := hx
        rcases mul_eq_zero.mp hz5 with hb0 | hb1
        · exact hb0
        · exfalso; apply htv0; nlinarith
  | ltZero t =>
    obtain ⟨gt, hst, hgt_lt, hpref_t, hwf_t, heval_t⟩ :=
      compileTermTokens_correct hn t [] gates hwf (fun _ h ↦ by simp at h)
    set resT := ((encTerm_tokens n t).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep ([], gates)
    set k := resT.2.length
    have hgt_eq : resT.1.headD 0 = gt := by rw [hst]; rfl
    have hfold : ((encFormula_tokens n (.ltZero t)).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack) =
        (k :: stack, [k + 7, k + 10, k + 14, k + 18] ++ zeros,
          resT.2 ++ ltZeroGateBlock k gt nextSlack, nextSlack + 4) := by
      simp only [encFormula_tokens, List.map_singleton, List.reverse_singleton,
        List.foldl_cons, List.foldl_nil, compileFormulaTokenStep_ltZero,
        termTokensDecoder_decode_encTerm, Option.getD_some, compileTermTokens_eq_foldl]
      change (resT.2.length :: stack,
          [resT.2.length + 7, resT.2.length + 10, resT.2.length + 14, resT.2.length + 18] ++ zeros,
          resT.2 ++ ltZeroGateBlock resT.2.length (resT.1.headD 0) nextSlack, nextSlack + 4) = _
      rw [hgt_eq]
    rw [hfold]
    dsimp only [FormulaCompileSpec]
    refine ⟨k, [k + 7, k + 10, k + 14, k + 18], by omega, rfl, rfl,
      by simp only [ltZeroGateBlock_length, List.length_append]; omega,
      ?_, hpref_t.trans (List.prefix_append _ _), ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;>
        (simp only [ltZeroGateBlock_length, List.length_append]; omega)
    · intro j hj
      simp only [List.length_append] at hj ⊢
      by_cases hlt : j < k
      · rw [List.getElem_append_left hlt]
        have h := hwf_t j hlt
        cases hg : resT.2[j] with
        | input idx => rw [hg] at h; simp at h ⊢; omega
        | const _ => simp
        | add _ _ => rw [hg] at h; exact h
        | mul _ _ => rw [hg] at h; exact h
        | neg _ => rw [hg] at h; exact h
      · rw [List.getElem_append_right (Nat.le_of_not_lt hlt)]
        have hblen : (ltZeroGateBlock k gt nextSlack).length = 19 := rfl
        have : ∀ idx (hidx : idx < 19), j = k + idx →
            (ltZeroGateBlock k gt nextSlack)[idx].WellFormed (nextSlack + 4) j := by
          intro idx hidx hjk
          subst hjk; exact ltZeroGateBlock_wellFormed hgt_lt idx hidx
        exact this (j - k) (by omega) (by omega)
    · intro x
      classical
      let tv : ℝ := t.eval x
      let bv : ℝ := if tv < 0 then 1 else 0
      let uv : ℝ := if tv < 0 then Real.sqrt (-tv) else 0
      let vv : ℝ := if tv < 0 then (Real.sqrt (-tv))⁻¹ else 0
      let wv : ℝ := if tv < 0 then 0 else Real.sqrt tv
      refine ⟨fun j ↦ if j.1 = 0 then bv else if j.1 = 1 then uv else if j.1 = 2 then vv else wv,
        fun y hy hext ↦ ?_⟩
      have hyx : (fun i : Fin n ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) = x := funext hy
      have hyb : y ⟨nextSlack, by omega⟩ = bv := by simpa using hext ⟨0, by omega⟩
      have hyu : y ⟨nextSlack + 1, by omega⟩ = uv := by simpa using hext ⟨1, by omega⟩
      have hyv : y ⟨nextSlack + 2, by omega⟩ = vv := by simpa using hext ⟨2, by omega⟩
      have hyw : y ⟨nextSlack + 3, by omega⟩ = wv := by simpa using hext ⟨3, by omega⟩
      obtain ⟨h0, h7, h10, h14, h18⟩ :=
        eval_ltZeroGateBlock y resT.2 hgt_lt (by omega : nextSlack + 3 < _)
      have htv : (evalGatesList y resT.2).getD gt 0 = tv := by
        rw [evalGatesList_restrict_eq (by omega : nextSlack ≤ nextSlack + 4) y resT.2 hwf_t,
          heval_t, hyx]
      refine ⟨fun g hg ↦ ?_, fun hx ↦ ?_, fun hx ↦ ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · rw [h7, hyb]; dsimp [bv]; split_ifs <;> ring
        · rw [h10, hyb, hyu, htv]; dsimp [bv, uv]; split_ifs with h
          · rw [Real.mul_self_sqrt (by linarith)]; ring
          · ring
        · rw [h14, hyb, hyu, hyv]; dsimp [bv, uv, vv]; split_ifs with h
          · rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (by linarith)).ne']; ring
          · ring
        · rw [h18, hyb, hyw, htv]; dsimp [bv, wv]; split_ifs with h
          · ring
          · rw [Real.mul_self_sqrt (by linarith)]; ring
      · have htv0 : tv < 0 := hx
        rw [h0, hyb]; simp [bv, htv0]
      · have htv0 : ¬tv < 0 := hx
        rw [h0, hyb]; simp [bv, htv0]
    · intro y hz
      obtain ⟨h0, h7, h10, h14, h18⟩ :=
        eval_ltZeroGateBlock y resT.2 hgt_lt (by omega : nextSlack + 3 < _)
      have hz7 : y ⟨nextSlack, by omega⟩ * (1 - y ⟨nextSlack, by omega⟩) = 0 := by
        rw [← h7]; exact hz (k + 7) (by simp)
      have hz10 : y ⟨nextSlack, by omega⟩ *
          ((evalGatesList y resT.2).getD gt 0 +
            y ⟨nextSlack + 1, by omega⟩ * y ⟨nextSlack + 1, by omega⟩) = 0 := by
        rw [← h10]; exact hz (k + 10) (by simp)
      have hz14 : y ⟨nextSlack, by omega⟩ *
          (y ⟨nextSlack + 1, by omega⟩ * y ⟨nextSlack + 2, by omega⟩ - 1) = 0 := by
        rw [← h14]; exact hz (k + 14) (by simp)
      have hz18 : (1 - y ⟨nextSlack, by omega⟩) *
          ((evalGatesList y resT.2).getD gt 0 -
            y ⟨nextSlack + 3, by omega⟩ * y ⟨nextSlack + 3, by omega⟩) = 0 := by
        rw [← h18]; exact hz (k + 18) (by simp)
      have htv : (evalGatesList y resT.2).getD gt 0 =
          t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) := by
        rw [evalGatesList_restrict_eq (by omega : nextSlack ≤ nextSlack + 4) y resT.2 hwf_t,
          heval_t]
      rw [htv] at hz10 hz18
      rw [h0]
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · have hlt : t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) < 0 := hx
        rcases mul_eq_zero.mp hz7 with hb0 | hb1
        · rw [hb0] at hz18
          have hge : 0 ≤ t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) := by
            have : t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) =
                y ⟨nextSlack + 3, by omega⟩ * y ⟨nextSlack + 3, by omega⟩ := by linarith
            rw [this]; exact mul_self_nonneg _
          linarith
        · linarith
      · have hge : ¬t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) < 0 := hx
        rcases mul_eq_zero.mp hz7 with hb0 | hb1
        · exact hb0
        · exfalso; apply hge
          have hb : y ⟨nextSlack, by omega⟩ = 1 := by linarith
          rw [hb] at hz10 hz14
          have hu : y ⟨nextSlack + 1, by omega⟩ ≠ 0 :=
            (inv_gadget (y := y ⟨nextSlack + 2, by omega⟩) (by linarith)).1
          have : t.eval (fun i ↦ y ⟨i.1, i.2.trans_le (hn.trans (by omega))⟩) =
              -(y ⟨nextSlack + 1, by omega⟩ * y ⟨nextSlack + 1, by omega⟩) := by linarith
          rw [this]; nlinarith [mul_self_pos.mpr hu]
  | not p ih =>
    obtain ⟨bp, newZ, hslack_p, hsp, hzp, hbp_lt, hnewZ_lt, hpref_p, hwf_p, hex_p, hall_p⟩ :=
      ih stack zeros gates nextSlack hn hwf hstack hzeros
    set resP := ((encFormula_tokens n p).map FormulaToken.encodeTerms).reverse.foldl
      compileFormulaTokenStep (stack, zeros, gates, nextSlack)
    set k := resP.2.2.1.length
    have hbp_eq : resP.1.headD 0 = bp := by rw [hsp]; rfl
    have hfold : ((encFormula_tokens n (.not p)).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack) =
        ((k + 2) :: resP.1.tail, resP.2.1,
          resP.2.2.1 ++ [.const 1, .neg bp, .add k (k + 1)], resP.2.2.2) := by
      have htok : encFormula_tokens n (.not p) =
          .inr (.inr (.inr (.inl ()))) :: encFormula_tokens n p := by
        simp [encFormula_tokens]
      rw [htok, List.map_cons, List.reverse_cons, List.foldl_append, List.foldl_cons,
        List.foldl_nil, compileFormulaTokenStep_not, hbp_eq]
    rw [hfold]
    dsimp only [FormulaCompileSpec]
    refine ⟨k + 2, newZ, hslack_p, by rw [hsp]; rfl, hzp,
      by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
      fun g hg ↦ (hnewZ_lt g hg).trans
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      hpref_p.trans (List.prefix_append _ _), ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj ⊢
      by_cases hlt : j < k
      · rw [List.getElem_append_left hlt]; exact hwf_p j hlt
      · rw [List.getElem_append_right (Nat.le_of_not_lt hlt)]
        have : ∀ idx (hidx : idx < 3), j = k + idx →
            ([.const 1, .neg bp, .add k (k + 1)] : List ArithGate)[idx].WellFormed
              resP.2.2.2 j := by
          intro idx hidx hjk
          interval_cases idx <;> simp [ArithGate.wellFormed_add] <;> omega
        exact this (j - k) (by omega) (by omega)
    · intro x
      obtain ⟨ext, hext⟩ := hex_p x
      refine ⟨ext, fun y hy hext' ↦ ?_⟩
      obtain ⟨hz, hbp1, hbp0⟩ := hext y hy hext'
      refine ⟨fun g hg ↦ ?_, fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rw [evalGatesList_append_getD y _ _ (hnewZ_lt g hg), hz g hg]
      · rw [eval_notGateBlock y resP.2.2.1 hbp_lt, hbp0 hx]; norm_num
      · rw [eval_notGateBlock y resP.2.2.1 hbp_lt,
          hbp1 (by simpa [Formula.solutionSet] using hx)]; norm_num
    · intro y hz
      have hz' : ∀ g ∈ newZ, (evalGatesList y resP.2.2.1).getD g 0 = 0 := fun g hg ↦ by
        have := hz g hg
        rwa [evalGatesList_append_getD y _ _ (hnewZ_lt g hg)] at this
      obtain ⟨hbp1, hbp0⟩ := hall_p y hz'
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rw [eval_notGateBlock y resP.2.2.1 hbp_lt, hbp0 hx]; norm_num
      · rw [eval_notGateBlock y resP.2.2.1 hbp_lt,
          hbp1 (by simpa [Formula.solutionSet] using hx)]; norm_num
  | and p q ihp ihq =>
    set resQ := ((encFormula_tokens n q).map FormulaToken.encodeTerms).reverse.foldl
      compileFormulaTokenStep (stack, zeros, gates, nextSlack)
    have hihq : FormulaCompileSpec n q stack zeros gates nextSlack hn resQ :=
      ihq stack zeros gates nextSlack hn hwf hstack hzeros
    obtain ⟨bq, zq, hslack_q, hsq, hzq, hbq_lt, hzq_lt, hpref_q, hwf_q, hex_q, hall_q⟩ := hihq
    have hsq_mem : ∀ g ∈ bq :: stack, g < resQ.2.2.1.length := fun g hg ↦ by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hbq_lt
      · exact (hstack g hg).trans_le hpref_q.length_le
    have hzq_mem : ∀ g ∈ zq ++ zeros, g < resQ.2.2.1.length := fun g hg ↦ by
      rcases List.mem_append.mp hg with hg | hg
      · exact hzq_lt g hg
      · exact (hzeros g hg).trans_le hpref_q.length_le
    have hresQ_eq : resQ = (bq :: stack, zq ++ zeros, resQ.2.2.1, resQ.2.2.2) :=
      Prod.ext hsq (Prod.ext hzq rfl)
    set resP := ((encFormula_tokens n p).map FormulaToken.encodeTerms).reverse.foldl
      compileFormulaTokenStep resQ
    have hihp : FormulaCompileSpec n p (bq :: stack) (zq ++ zeros) resQ.2.2.1 resQ.2.2.2
        (hn.trans hslack_q) resP := by
      have h := ihp (bq :: stack) (zq ++ zeros) resQ.2.2.1 resQ.2.2.2 (hn.trans hslack_q)
        hwf_q hsq_mem hzq_mem
      rwa [← hresQ_eq] at h
    obtain ⟨bp, zp, hslack_p, hsp, hzp, hbp_lt, hzp_lt, hpref_p, hwf_p, hex_p, hall_p⟩ := hihp
    set k := resP.2.2.1.length
    have hbp_eq : resP.1.headD 0 = bp := by rw [hsp]; rfl
    have hbq_eq : resP.1.tail.headD 0 = bq := by rw [hsp]; rfl
    have hbq_lt' : bq < k := hbq_lt.trans_le hpref_p.length_le
    have hresQ_eval : ∀ (y : Fin resP.2.2.2 → ℝ) (g : ℕ), g < resQ.2.2.1.length →
        (evalGatesList y resP.2.2.1).getD g 0 =
          (evalGatesList (fun i ↦ y ⟨i.1, i.2.trans_le hslack_p⟩) resQ.2.2.1).getD g 0 := by
      intro y g hg
      obtain ⟨extG, hextG⟩ := hpref_p
      rw [← hextG, evalGatesList_append_getD y _ _ hg, evalGatesList_restrict_eq hslack_p y _ hwf_q]
    have hfold : ((encFormula_tokens n (.and p q)).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack) =
        (k :: resP.1.tail.tail, resP.2.1, resP.2.2.1 ++ [.mul bp bq], resP.2.2.2) := by
      have htok : encFormula_tokens n (.and p q) =
          .inr (.inr (.inr (.inr (.inl ())))) ::
            (encFormula_tokens n p ++ encFormula_tokens n q) := by
        simp [encFormula_tokens]
      rw [htok, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append,
        List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
        compileFormulaTokenStep_and, hbp_eq, hbq_eq]
    rw [hfold]
    dsimp only [FormulaCompileSpec]
    refine ⟨k, zp ++ zq, hslack_q.trans hslack_p, by rw [hsp]; rfl,
      by rw [hzp, List.append_assoc],
      by simp only [List.length_append, List.length_singleton]; omega,
      fun g hg ↦ by
        rcases List.mem_append.mp hg with hg | hg
        · exact (hzp_lt g hg).trans
            (by simp only [List.length_append, List.length_singleton]; omega)
        · exact ((hzq_lt g hg).trans_le hpref_p.length_le).trans
            (by simp only [List.length_append, List.length_singleton]; omega),
      hpref_q.trans (hpref_p.trans (List.prefix_append _ _)), ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj ⊢
      by_cases hlt : j < k
      · rw [List.getElem_append_left hlt]; exact hwf_p j hlt
      · have heq : j = k := by omega
        subst heq
        dsimp only [k]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero,
          ArithGate.wellFormed_mul]
        exact ⟨hbp_lt, hbq_lt'⟩
    · intro x
      obtain ⟨extQ, hextQ⟩ := hex_q x
      obtain ⟨extP, hextP⟩ := hex_p x
      let ext : Fin (resP.2.2.2 - nextSlack) → ℝ := fun j ↦
        if h : j.1 < resQ.2.2.2 - nextSlack then extQ ⟨j.1, h⟩
        else extP ⟨j.1 - (resQ.2.2.2 - nextSlack), by omega⟩
      refine ⟨ext, fun y hy hext' ↦ ?_⟩
      obtain ⟨hzQ, hbq1, hbq0⟩ := hextQ (fun i ↦ y ⟨i.1, i.2.trans_le hslack_p⟩) hy fun j ↦ by
        simpa [ext, j.2] using hext' ⟨j.1, by omega⟩
      obtain ⟨hzP, hbp1, hbp0⟩ := hextP y (fun i ↦ hy i) fun j ↦ by
        have hnot : ¬ ((resQ.2.2.2 - nextSlack) + j.1 < resQ.2.2.2 - nextSlack) := by omega
        have hsub : (resQ.2.2.2 - nextSlack) + j.1 - (resQ.2.2.2 - nextSlack) = j.1 := by omega
        have hadd : nextSlack + ((resQ.2.2.2 - nextSlack) + j.1) = resQ.2.2.2 + j.1 := by omega
        simpa [ext, hnot, hsub, hadd] using hext' ⟨(resQ.2.2.2 - nextSlack) + j.1, by omega⟩
      refine ⟨fun g hg ↦ ?_, fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rcases List.mem_append.mp hg with hg | hg
        · rw [evalGatesList_append_getD y _ _ (hzp_lt g hg), hzP g hg]
        · rw [evalGatesList_append_getD y _ _ ((hzq_lt g hg).trans_le hpref_p.length_le),
            hresQ_eval y g (hzq_lt g hg), hzQ g hg]
      · dsimp only [k]; rw [evalGatesList_snoc_last]
        simp only [evalGateStep_mul, hbp1 hx.1, hresQ_eval y bq hbq_lt, hbq1 hx.2, mul_one]
      · dsimp only [k]; rw [evalGatesList_snoc_last]
        simp only [evalGateStep_mul, hresQ_eval y bq hbq_lt]
        by_cases hp : x ∈ p.solutionSet
        · have hq : x ∉ q.solutionSet := fun hq ↦ hx ⟨hp, hq⟩
          rw [hbp1 hp, hbq0 hq]; ring
        · rw [hbp0 hp]; ring
    · intro y hz
      have hzP : ∀ g ∈ zp, (evalGatesList y resP.2.2.1).getD g 0 = 0 := fun g hg ↦ by
        have := hz g (List.mem_append_left _ hg)
        rwa [evalGatesList_append_getD y _ _ (hzp_lt g hg)] at this
      have hzQ : ∀ g ∈ zq,
          (evalGatesList (fun i ↦ y ⟨i.1, i.2.trans_le hslack_p⟩) resQ.2.2.1).getD g 0 = 0 := by
        intro g hg
        have := hz g (List.mem_append_right _ hg)
        rwa [evalGatesList_append_getD y _ _ ((hzq_lt g hg).trans_le hpref_p.length_le),
          hresQ_eval y g (hzq_lt g hg)] at this
      obtain ⟨hbp1, hbp0⟩ := hall_p y hzP
      obtain ⟨hbq1, hbq0⟩ := hall_q _ hzQ
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · dsimp only [k]; rw [evalGatesList_snoc_last]
        simp only [evalGateStep_mul, hbp1 hx.1, hresQ_eval y bq hbq_lt, hbq1 hx.2, mul_one]
      · dsimp only [k]; rw [evalGatesList_snoc_last]
        simp only [evalGateStep_mul, hresQ_eval y bq hbq_lt]
        by_cases hp : (fun i : Fin n ↦ y ⟨i.1, i.2.trans_le (hn.trans (hslack_q.trans hslack_p))⟩)
            ∈ p.solutionSet
        · have hq : (fun i : Fin n ↦ y ⟨i.1, i.2.trans_le (hn.trans (hslack_q.trans hslack_p))⟩)
              ∉ q.solutionSet := fun hq ↦ hx ⟨hp, hq⟩
          rw [hbp1 hp, hbq0 hq]; ring
        · rw [hbp0 hp]; ring
  | or p q ihp ihq =>
    set resQ := ((encFormula_tokens n q).map FormulaToken.encodeTerms).reverse.foldl
      compileFormulaTokenStep (stack, zeros, gates, nextSlack)
    have hihq : FormulaCompileSpec n q stack zeros gates nextSlack hn resQ :=
      ihq stack zeros gates nextSlack hn hwf hstack hzeros
    obtain ⟨bq, zq, hslack_q, hsq, hzq, hbq_lt, hzq_lt, hpref_q, hwf_q, hex_q, hall_q⟩ := hihq
    have hsq_mem : ∀ g ∈ bq :: stack, g < resQ.2.2.1.length := fun g hg ↦ by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hbq_lt
      · exact (hstack g hg).trans_le hpref_q.length_le
    have hzq_mem : ∀ g ∈ zq ++ zeros, g < resQ.2.2.1.length := fun g hg ↦ by
      rcases List.mem_append.mp hg with hg | hg
      · exact hzq_lt g hg
      · exact (hzeros g hg).trans_le hpref_q.length_le
    have hresQ_eq : resQ = (bq :: stack, zq ++ zeros, resQ.2.2.1, resQ.2.2.2) :=
      Prod.ext hsq (Prod.ext hzq rfl)
    set resP := ((encFormula_tokens n p).map FormulaToken.encodeTerms).reverse.foldl
      compileFormulaTokenStep resQ
    have hihp : FormulaCompileSpec n p (bq :: stack) (zq ++ zeros) resQ.2.2.1 resQ.2.2.2
        (hn.trans hslack_q) resP := by
      have h := ihp (bq :: stack) (zq ++ zeros) resQ.2.2.1 resQ.2.2.2 (hn.trans hslack_q)
        hwf_q hsq_mem hzq_mem
      rwa [← hresQ_eq] at h
    obtain ⟨bp, zp, hslack_p, hsp, hzp, hbp_lt, hzp_lt, hpref_p, hwf_p, hex_p, hall_p⟩ := hihp
    set k := resP.2.2.1.length
    have hbp_eq : resP.1.headD 0 = bp := by rw [hsp]; rfl
    have hbq_eq : resP.1.tail.headD 0 = bq := by rw [hsp]; rfl
    have hbq_lt' : bq < k := hbq_lt.trans_le hpref_p.length_le
    have hresQ_eval : ∀ (y : Fin resP.2.2.2 → ℝ) (g : ℕ), g < resQ.2.2.1.length →
        (evalGatesList y resP.2.2.1).getD g 0 =
          (evalGatesList (fun i ↦ y ⟨i.1, i.2.trans_le hslack_p⟩) resQ.2.2.1).getD g 0 := by
      intro y g hg
      obtain ⟨extG, hextG⟩ := hpref_p
      rw [← hextG, evalGatesList_append_getD y _ _ hg, evalGatesList_restrict_eq hslack_p y _ hwf_q]
    have hfold : ((encFormula_tokens n (.or p q)).map FormulaToken.encodeTerms).reverse.foldl
        compileFormulaTokenStep (stack, zeros, gates, nextSlack) =
        ((k + 3) :: resP.1.tail.tail, resP.2.1,
          resP.2.2.1 ++ [.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)], resP.2.2.2) := by
      have htok : encFormula_tokens n (.or p q) =
          .inr (.inr (.inr (.inr (.inr ())))) ::
            (encFormula_tokens n p ++ encFormula_tokens n q) := by
        simp [encFormula_tokens]
      rw [htok, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append,
        List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
        compileFormulaTokenStep_or, hbp_eq, hbq_eq]
    rw [hfold]
    dsimp only [FormulaCompileSpec]
    refine ⟨k + 3, zp ++ zq, hslack_q.trans hslack_p, by rw [hsp]; rfl,
      by rw [hzp, List.append_assoc],
      by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
      fun g hg ↦ by
        rcases List.mem_append.mp hg with hg | hg
        · exact (hzp_lt g hg).trans
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        · exact ((hzq_lt g hg).trans_le hpref_p.length_le).trans
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      hpref_q.trans (hpref_p.trans (List.prefix_append _ _)), ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj ⊢
      by_cases hlt : j < k
      · rw [List.getElem_append_left hlt]; exact hwf_p j hlt
      · rw [List.getElem_append_right (Nat.le_of_not_lt hlt)]
        have : ∀ idx (hidx : idx < 4), j = k + idx →
            ([.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)] :
              List ArithGate)[idx].WellFormed resP.2.2.2 j := by
          intro idx hidx hjk
          interval_cases idx <;> simp [ArithGate.wellFormed_add, ArithGate.wellFormed_mul] <;> omega
        exact this (j - k) (by omega) (by omega)
    · intro x
      obtain ⟨extQ, hextQ⟩ := hex_q x
      obtain ⟨extP, hextP⟩ := hex_p x
      let ext : Fin (resP.2.2.2 - nextSlack) → ℝ := fun j ↦
        if h : j.1 < resQ.2.2.2 - nextSlack then extQ ⟨j.1, h⟩
        else extP ⟨j.1 - (resQ.2.2.2 - nextSlack), by omega⟩
      refine ⟨ext, fun y hy hext' ↦ ?_⟩
      obtain ⟨hzQ, hbq1, hbq0⟩ := hextQ (fun i ↦ y ⟨i.1, i.2.trans_le hslack_p⟩) hy fun j ↦ by
        simpa [ext, j.2] using hext' ⟨j.1, by omega⟩
      obtain ⟨hzP, hbp1, hbp0⟩ := hextP y (fun i ↦ hy i) fun j ↦ by
        have hnot : ¬ ((resQ.2.2.2 - nextSlack) + j.1 < resQ.2.2.2 - nextSlack) := by omega
        have hsub : (resQ.2.2.2 - nextSlack) + j.1 - (resQ.2.2.2 - nextSlack) = j.1 := by omega
        have hadd : nextSlack + ((resQ.2.2.2 - nextSlack) + j.1) = resQ.2.2.2 + j.1 := by omega
        simpa [ext, hnot, hsub, hadd] using hext' ⟨(resQ.2.2.2 - nextSlack) + j.1, by omega⟩
      refine ⟨fun g hg ↦ ?_, fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rcases List.mem_append.mp hg with hg | hg
        · rw [evalGatesList_append_getD y _ _ (hzp_lt g hg), hzP g hg]
        · rw [evalGatesList_append_getD y _ _ ((hzq_lt g hg).trans_le hpref_p.length_le),
            hresQ_eval y g (hzq_lt g hg), hzQ g hg]
      · rw [eval_orGateBlock y resP.2.2.1 hbp_lt hbq_lt', hresQ_eval y bq hbq_lt]
        rcases hx with hp | hq
        · rw [hbp1 hp]; ring
        · rw [hbq1 hq]; ring
      · rw [eval_orGateBlock y resP.2.2.1 hbp_lt hbq_lt', hresQ_eval y bq hbq_lt,
          hbp0 (fun hp ↦ hx (Or.inl hp)), hbq0 (fun hq ↦ hx (Or.inr hq))]; ring
    · intro y hz
      have hzP : ∀ g ∈ zp, (evalGatesList y resP.2.2.1).getD g 0 = 0 := fun g hg ↦ by
        have := hz g (List.mem_append_left _ hg)
        rwa [evalGatesList_append_getD y _ _ (hzp_lt g hg)] at this
      have hzQ : ∀ g ∈ zq,
          (evalGatesList (fun i ↦ y ⟨i.1, i.2.trans_le hslack_p⟩) resQ.2.2.1).getD g 0 = 0 := by
        intro g hg
        have := hz g (List.mem_append_right _ hg)
        rwa [evalGatesList_append_getD y _ _ ((hzq_lt g hg).trans_le hpref_p.length_le),
          hresQ_eval y g (hzq_lt g hg)] at this
      obtain ⟨hbp1, hbp0⟩ := hall_p y hzP
      obtain ⟨hbq1, hbq0⟩ := hall_q _ hzQ
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rw [eval_orGateBlock y resP.2.2.1 hbp_lt hbq_lt', hresQ_eval y bq hbq_lt]
        rcases hx with hp | hq
        · rw [hbp1 hp]; ring
        · rw [hbq1 hq]; ring
      · rw [eval_orGateBlock y resP.2.2.1 hbp_lt hbq_lt', hresQ_eval y bq hbq_lt,
          hbp0 (fun hp ↦ hx (Or.inl hp)), hbq0 (fun hq ↦ hx (Or.inr hq))]; ring

/-- Compile a raw ETR formula word into a well-formed `ArithCircuit`. -/
@[expose] def etrWordToCircuit (word : List Bool) : ArithCircuit where
  numInputs := (etrWordToRawCircuit word).1
  gates := (etrWordToRawCircuit word).2.1
  output := (etrWordToRawCircuit word).2.2
  gates_wf := by
    have htok := formulaWordTokens_eq word
    have hcorrect := formula_compile_correct (Formula.ofWord word) [] [] [] word.length le_rfl
      (fun _ hk ↦ by simp at hk) (fun _ h ↦ by simp at h) (fun _ h ↦ by simp at h)
    set st := (formulaWordTokens word).reverse.foldl compileFormulaTokenStep
      ([], [], [], word.length)
    have hst_eq : st = ((encFormula_tokens word.length (Formula.ofWord word)).map
        FormulaToken.encodeTerms).reverse.foldl compileFormulaTokenStep
        ([], [], [], word.length) := by dsimp only [st]; rw [htok]
    rw [← hst_eq] at hcorrect
    obtain ⟨bp, newZ, _, hsp, hzp, hbp_lt, hnewZ_lt, _, hwf_p, _, _⟩ := hcorrect
    have hbp_eq : st.1.headD 0 = bp := by rw [hsp]; rfl
    have hzp_eq : st.2.1 = newZ := by rw [hzp, List.append_nil]
    set k := st.2.2.1.length
    let gates₁ := st.2.2.1 ++ [.const 1, .neg k, .add (st.1.headD 0) (k + 1)]
    have hwf1 : ∀ j (hj : j < gates₁.length), gates₁[j].WellFormed st.2.2.2 j := by
      intro j hj
      simp only [gates₁, List.length_append, List.length_cons, List.length_nil] at hj ⊢
      by_cases hlt : j < k
      · rw [List.getElem_append_left hlt]; exact hwf_p j hlt
      · rw [List.getElem_append_right (Nat.le_of_not_lt hlt)]
        have hbp_lt' : st.1.headD 0 < k := by rw [hbp_eq]; exact hbp_lt
        have : ∀ idx (hidx : idx < 3), j = k + idx →
            ([.const 1, .neg k, .add (st.1.headD 0) (k + 1)] : List ArithGate)[idx].WellFormed
              st.2.2.2 j := by
          intro idx hidx hjk
          interval_cases idx <;>
            simp only [List.getElem_cons_zero, List.getElem_cons_succ, ArithGate.wellFormed_const,
              ArithGate.wellFormed_neg, ArithGate.wellFormed_add] <;>
            omega
        exact this (j - k) (by omega) (by omega)
    let gates₂ := gates₁ ++ [.const 0]
    have hwf2 : ∀ j (hj : j < gates₂.length), gates₂[j].WellFormed st.2.2.2 j := by
      intro j hj
      simp only [gates₂, List.length_append, List.length_singleton] at hj ⊢
      by_cases hlt : j < gates₁.length
      · rw [List.getElem_append_left hlt]; exact hwf1 j hlt
      · have heq : j = gates₁.length := by omega
        subst heq; simp
    have hallZ : ∀ g ∈ (k + 2) :: newZ, g < gates₂.length := fun g hg ↦ by
      rcases List.mem_cons.mp hg with rfl | hg
      · simp only [gates₂, gates₁, List.length_append, List.length_cons, List.length_nil]; omega
      · exact (hnewZ_lt g hg).trans
          (by simp only [gates₂, gates₁, List.length_append, List.length_cons, List.length_nil, k]
              omega)
    have hsos := sumOfSquares_eval_zero_iff (n := st.2.2.2) (fun _ ↦ 0) ((k + 2) :: newZ)
      gates₁.length gates₂ (by simp [gates₂]) hallZ
    change ∀ j (hj : j < ((((k + 2) :: st.2.1).foldl sumOfSquaresStep
      (gates₁.length, gates₂)).2).length),
      ((((k + 2) :: st.2.1).foldl sumOfSquaresStep
        (gates₁.length, gates₂)).2)[j].WellFormed st.2.2.2 j
    rw [hzp_eq]
    exact fun j hj ↦ hsos.2.2.2.1 j hj hwf2
  output_lt := by
    have htok := formulaWordTokens_eq word
    have hcorrect := formula_compile_correct (Formula.ofWord word) [] [] [] word.length le_rfl
      (fun _ hk ↦ by simp at hk) (fun _ h ↦ by simp at h) (fun _ h ↦ by simp at h)
    set st := (formulaWordTokens word).reverse.foldl compileFormulaTokenStep
      ([], [], [], word.length)
    have hst_eq : st = ((encFormula_tokens word.length (Formula.ofWord word)).map
        FormulaToken.encodeTerms).reverse.foldl compileFormulaTokenStep
        ([], [], [], word.length) := by dsimp only [st]; rw [htok]
    rw [← hst_eq] at hcorrect
    obtain ⟨bp, newZ, _, hsp, hzp, hbp_lt, hnewZ_lt, _, _, _, _⟩ := hcorrect
    have hzp_eq : st.2.1 = newZ := by rw [hzp, List.append_nil]
    set k := st.2.2.1.length
    let gates₁ := st.2.2.1 ++ [.const 1, .neg k, .add (st.1.headD 0) (k + 1)]
    let gates₂ := gates₁ ++ [.const 0]
    have hallZ : ∀ g ∈ (k + 2) :: newZ, g < gates₂.length := fun g hg ↦ by
      rcases List.mem_cons.mp hg with rfl | hg
      · simp only [gates₂, gates₁, List.length_append, List.length_cons, List.length_nil]; omega
      · exact (hnewZ_lt g hg).trans
          (by simp only [gates₂, gates₁, List.length_append, List.length_cons, List.length_nil, k]
              omega)
    have hsos := sumOfSquares_eval_zero_iff (n := st.2.2.2) (fun _ ↦ 0) ((k + 2) :: newZ)
      gates₁.length gates₂ (by simp [gates₂]) hallZ
    change (((k + 2) :: st.2.1).foldl sumOfSquaresStep (gates₁.length, gates₂)).1 <
      (((k + 2) :: st.2.1).foldl sumOfSquaresStep (gates₁.length, gates₂)).2.length
    rw [hzp_eq]
    exact hsos.2.1

/-- Equisatisfiability of `etrWordToCircuit`: `word ∈ ETR ↔ (etrWordToCircuit word).Satisfiable`. -/
theorem etrWordToCircuit_sat_iff (word : List Bool) :
    word ∈ ETR ↔ (etrWordToCircuit word).Satisfiable := by
  rw [mem_ETR_iff_ofWord]
  have htok := formulaWordTokens_eq word
  have hcorrect := formula_compile_correct (Formula.ofWord word) [] [] [] word.length le_rfl
    (fun _ hk ↦ by simp at hk) (fun _ h ↦ by simp at h) (fun _ h ↦ by simp at h)
  set st := (formulaWordTokens word).reverse.foldl compileFormulaTokenStep
    ([], [], [], word.length)
  have hst_eq : st = ((encFormula_tokens word.length (Formula.ofWord word)).map
      FormulaToken.encodeTerms).reverse.foldl compileFormulaTokenStep
      ([], [], [], word.length) := by dsimp only [st]; rw [htok]
  rw [← hst_eq] at hcorrect
  obtain ⟨bp, newZ, hslack, hsp, hzp, hbp_lt, hnewZ_lt, _, hwf_p, hex_p, hall_p⟩ := hcorrect
  have hbp_eq : st.1.headD 0 = bp := by rw [hsp]; rfl
  have hzp_eq : st.2.1 = newZ := by rw [hzp, List.append_nil]
  set k := st.2.2.1.length
  let gates₁ := st.2.2.1 ++ [.const 1, .neg k, .add (st.1.headD 0) (k + 1)]
  let gates₂ := gates₁ ++ [.const 0]
  have hallZ : ∀ g ∈ (k + 2) :: newZ, g < gates₂.length := fun g hg ↦ by
    rcases List.mem_cons.mp hg with rfl | hg
    · simp only [gates₂, gates₁, List.length_append, List.length_cons, List.length_nil]; omega
    · exact (hnewZ_lt g hg).trans
        (by simp only [gates₂, gates₁, List.length_append, List.length_cons, List.length_nil, k]
            omega)
  have heval_out : ∀ y : Fin st.2.2.2 → ℝ,
      (etrWordToCircuit word).eval y =
        (((evalGatesList y gates₂).getD (k + 2) 0) ^ 2 +
          (newZ.map fun g ↦ ((evalGatesList y gates₂).getD g 0) ^ 2).sum) := by
    intro y
    have hsos := sumOfSquares_eval_zero_iff (n := st.2.2.2) y ((k + 2) :: newZ)
      gates₁.length gates₂ (by simp [gates₂]) hallZ
    change (evalGatesList y (((k + 2) :: st.2.1).foldl sumOfSquaresStep
      (gates₁.length, gates₂)).2).getD
      (((k + 2) :: st.2.1).foldl sumOfSquaresStep (gates₁.length, gates₂)).1 0 = _
    rw [hzp_eq, hsos.2.2.2.2]
    have hg2 : (evalGatesList y gates₂).getD gates₁.length 0 = 0 := by
      dsimp [gates₂]; rw [evalGatesList_snoc_last]; simp
    rw [hg2, zero_add, List.map_cons, List.sum_cons]
  have hk2_eval : ∀ y : Fin st.2.2.2 → ℝ,
      (evalGatesList y gates₂).getD (k + 2) 0 =
        (evalGatesList y st.2.2.1).getD bp 0 - 1 := by
    intro y
    have hsplit : gates₂ = st.2.2.1 ++ [.const 1, .neg k, .add bp (k + 1), .const 0] := by
      simp only [gates₂, gates₁, List.append_assoc, List.cons_append, List.nil_append, hbp_eq]
    rw [hsplit]
    have h0 : (evalGatesList y (st.2.2.1 ++ [.const 1, .neg k, .add bp (k + 1), .const 0])).getD
        (k + 0) 0 = 1 := by
      rw [evalGatesList_at_const y st.2.2.1 [.const 1, .neg k, .add bp (k + 1), .const 0]
        (idx := 0) (by simp) rfl]
      norm_num
    have h1 := evalGatesList_at_neg y st.2.2.1 [.const 1, .neg k, .add bp (k + 1), .const 0]
      (idx := 1) (by simp) rfl (by omega)
    have h2 := evalGatesList_at_add y st.2.2.1 [.const 1, .neg k, .add bp (k + 1), .const 0]
      (idx := 2) (by simp) rfl (by omega) (by omega)
    have hbp' := evalGatesList_append_getD y st.2.2.1
      [.const 1, .neg k, .add bp (k + 1), .const 0] hbp_lt
    simp only [Nat.add_zero] at h0
    rw [h2, hbp', h1, h0]; ring
  have hnewZ_eval : ∀ (y : Fin st.2.2.2 → ℝ) (g : ℕ), g ∈ newZ →
      (evalGatesList y gates₂).getD g 0 = (evalGatesList y st.2.2.1).getD g 0 := by
    intro y g hg
    have hsplit : gates₂ = st.2.2.1 ++ [.const 1, .neg k, .add bp (k + 1), .const 0] := by
      simp only [gates₂, gates₁, List.append_assoc, List.cons_append, List.nil_append, hbp_eq]
    rw [hsplit, evalGatesList_append_getD y _ _ (hnewZ_lt g hg)]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨ext, hext⟩ := hex_p x
    let y : Fin st.2.2.2 → ℝ := fun idx ↦
      if h1 : idx.1 < word.length then x ⟨idx.1, h1⟩
      else ext ⟨idx.1 - word.length, by omega⟩
    obtain ⟨hz, hbp1, _⟩ := hext y
      (fun i ↦ by simp [y, i.2]) (fun j ↦ by
        have hnot : ¬ (word.length + j.1 < word.length) := by omega
        have hsub : word.length + j.1 - word.length = j.1 := by omega
        simp [y, hnot, hsub])
    refine ⟨y, ?_⟩
    rw [heval_out y, hk2_eval y]
    have hsum0 : (newZ.map fun g ↦ ((evalGatesList y gates₂).getD g 0) ^ 2).sum = 0 := by
      have hsq := (sum_sq_eq_zero_iff (newZ.map fun g ↦ (evalGatesList y gates₂).getD g 0)).mpr
      rw [List.map_map] at hsq
      exact hsq fun v hv ↦ by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
        rw [hnewZ_eval y g hg, hz g hg]
    rw [hbp1 hx, hsum0]; norm_num
  · rintro ⟨(y : Fin st.2.2.2 → ℝ), hy⟩
    rw [heval_out y] at hy
    have hnonneg : 0 ≤ (newZ.map fun g ↦ ((evalGatesList y gates₂).getD g 0) ^ 2).sum :=
      List.sum_nonneg fun v hv ↦ by obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv; exact sq_nonneg _
    have hroot : (evalGatesList y gates₂).getD (k + 2) 0 = 0 :=
      sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ((evalGatesList y gates₂).getD (k + 2) 0)])
    have hsum0 : (newZ.map fun g ↦ ((evalGatesList y gates₂).getD g 0) ^ 2).sum = 0 := by
      linarith [sq_nonneg ((evalGatesList y gates₂).getD (k + 2) 0)]
    have hz : ∀ g ∈ newZ, (evalGatesList y st.2.2.1).getD g 0 = 0 := fun g hg ↦ by
      rw [← hnewZ_eval y g hg]
      have hsq := (sum_sq_eq_zero_iff (newZ.map fun g ↦ (evalGatesList y gates₂).getD g 0)).mp
      rw [List.map_map] at hsq
      exact hsq hsum0 _ (List.mem_map_of_mem hg)
    obtain ⟨_, hbp0⟩ := hall_p y hz
    rw [hk2_eval y] at hroot
    have hbp1 : (evalGatesList y st.2.2.1).getD bp 0 = 1 := by linarith
    refine ⟨fun i ↦ y ⟨i.1, i.2.trans_le hslack⟩, ?_⟩
    by_contra hnot
    linarith [hbp0 hnot]

/-- every ETR sentence `word` reduces to an
equisatisfiable arithmetic-circuit equality system `etrWordToCircuit word` (`p_C(x) = 0`) with
polynomially bounded size. -/
theorem etr_to_equalities (word : List Bool) :
    (word ∈ ETR ↔ (etrWordToCircuit word).Satisfiable) ∧
    (etrWordToCircuit word).numInputs ≤ 5 * max 1 word.length + word.length ∧
    (etrWordToCircuit word).size ≤ 30 * (max 1 word.length) * (word.length + 1) + 10 := by
  refine ⟨etrWordToCircuit_sat_iff word, ?_, ?_⟩
  · have hlen := formulaWordTokens_length_le word
    suffices ∀ (ts : List FormulaToken) (st : FormulaCompileState),
        (ts.foldl compileFormulaTokenStep st).2.2.2 ≤ st.2.2.2 + 4 * ts.length by
      have h := this (formulaWordTokens word).reverse ([], [], [], word.length)
      simp only [List.length_reverse] at h
      dsimp only [etrWordToCircuit]; rw [etrWordToRawCircuit_eq]; dsimp only
      omega
    intro ts
    induction ts with
    | nil => intro st; simp
    | cons tok rest ih =>
      intro st
      simp only [List.foldl_cons, List.length_cons]
      have h1 := ih (compileFormulaTokenStep st tok)
      have hstep : (compileFormulaTokenStep st tok).2.2.2 ≤ st.2.2.2 + 4 := by
        rcases tok with ⟨⟩ | _ | _ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;> simp
      omega
  · have hlen := formulaWordTokens_length_le word
    have hterm_len : ∀ tok ∈ formulaWordTokens word,
        (match tok with
          | .inr (.inl tw) | .inr (.inr (.inl tw)) => ((termTokensDecoder.decode tw).getD []).length
          | _ => 0) ≤ word.length := by
      intro tok htok
      rcases tok with _ | tw | tw | _ | _ | _ <;> try exact Nat.zero_le _
      · dsimp only
        cases hd : termTokensDecoder.decode tw with
        | none => simp
        | some ts =>
          have hsub : ts.length ≤ tw.length :=
            (SizedListEncoding.length_le encTermToken (encL := encList encTermToken) ts).trans
              (by rw [(termTokensDecoder.decode_eq_some_iff _ _).mp hd])
          have htw : tw.length < word.length := by
            by_cases hv : validFormulaWord word = true
            · have hdec := formulaTokensDecoder_decode_encFormula (Formula.ofWord word)
              rw [encFormula_ofWord, normalizeFormulaWord, ite_eq_left hv,
                ← formulaWordTokens_eq] at hdec
              exact formulaTermWord_length_lt_of_decode hdec (Or.inl htok)
            · rw [formulaWordTokens_eq, Formula.ofWord_of_not_valid hv] at htok
              simp [encFormula_tokens, FormulaToken.encodeTerms] at htok
          simp only [Option.getD_some]; omega
      · dsimp only
        cases hd : termTokensDecoder.decode tw with
        | none => simp
        | some ts =>
          have hsub : ts.length ≤ tw.length :=
            (SizedListEncoding.length_le encTermToken (encL := encList encTermToken) ts).trans
              (by rw [(termTokensDecoder.decode_eq_some_iff _ _).mp hd])
          have htw : tw.length < word.length := by
            by_cases hv : validFormulaWord word = true
            · have hdec := formulaTokensDecoder_decode_encFormula (Formula.ofWord word)
              rw [encFormula_ofWord, normalizeFormulaWord, ite_eq_left hv,
                ← formulaWordTokens_eq] at hdec
              exact formulaTermWord_length_lt_of_decode hdec (Or.inr htok)
            · rw [formulaWordTokens_eq, Formula.ofWord_of_not_valid hv] at htok
              simp [encFormula_tokens, FormulaToken.encodeTerms] at htok
          simp only [Option.getD_some]; omega
    have hcompile_gates : ∀ (ts : List FormulaToken) (st : FormulaCompileState),
        (∀ tok ∈ ts, (match tok with
          | .inr (.inl tw) | .inr (.inr (.inl tw)) => ((termTokensDecoder.decode tw).getD []).length
          | _ => 0) ≤ word.length) →
        (ts.foldl compileFormulaTokenStep st).2.2.1.length ≤
          st.2.2.1.length + ts.length * (word.length + 19) ∧
        (ts.foldl compileFormulaTokenStep st).2.1.length ≤ st.2.1.length + 4 * ts.length := by
      intro ts
      induction ts with
      | nil => intro st _; simp
      | cons tok rest ih =>
        intro st hall
        simp only [List.foldl_cons, List.length_cons]
        obtain ⟨hg, hz⟩ := ih (compileFormulaTokenStep st tok)
          (fun t ht ↦ hall t (List.mem_cons_of_mem _ ht))
        have htok_bound := hall tok (List.mem_cons_self ..)
        have hterm_fold : ∀ (tts : List TermToken) (gs : List ArithGate) (s : List ℕ),
            (tts.foldl compileTermTokenStep (s, gs)).2.length = gs.length + tts.length := by
          intro tts; induction tts with
          | nil => intro gs s; simp
          | cons tt rtt ih' =>
            intro gs s; simp only [List.foldl_cons, List.length_cons]
            rw [ih', (compileTermTokenStep_length (s, gs) tt).1]; dsimp; omega
        have hstep_g : (compileFormulaTokenStep st tok).2.2.1.length ≤
            st.2.2.1.length + (word.length + 19) := by
          rcases tok with ⟨⟩ | tw | tw | ⟨⟩ | ⟨⟩ | ⟨⟩
          · simp
          · simp only [compileFormulaTokenStep_eqZero_raw, compileTermTokens_eq_foldl,
              eqZeroGateBlock_length, List.length_append]
            rw [hterm_fold, List.length_reverse]; dsimp at htok_bound; omega
          · simp only [compileFormulaTokenStep_ltZero_raw, compileTermTokens_eq_foldl,
              ltZeroGateBlock_length, List.length_append]
            rw [hterm_fold, List.length_reverse]; dsimp at htok_bound; omega
          · simp
          · simp
          · simp
        have hstep_z : (compileFormulaTokenStep st tok).2.1.length ≤ st.2.1.length + 4 := by
          rcases tok with ⟨⟩ | _ | _ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;> simp
        refine ⟨?_, by omega⟩
        calc
          _ ≤ (compileFormulaTokenStep st tok).2.2.1.length + rest.length * (word.length + 19) :=
            hg
          _ ≤ st.2.2.1.length + (word.length + 19) + rest.length * (word.length + 19) := by omega
          _ = st.2.2.1.length + (rest.length + 1) * (word.length + 19) := by ring
    have hsos_len : ∀ (zs : List ℕ) (st : ℕ × List ArithGate),
        (zs.foldl sumOfSquaresStep st).2.length = st.2.length + 2 * zs.length := by
      intro zs; induction zs with
      | nil => intro st; simp
      | cons z zs ih =>
        intro st; simp only [List.foldl_cons, List.length_cons]
        rw [ih]; simp; omega
    obtain ⟨hg, hz⟩ := hcompile_gates (formulaWordTokens word).reverse ([], [], [], word.length)
      (fun tok htok ↦ hterm_len tok (List.mem_reverse.mp htok))
    simp only [List.length_reverse, List.length_nil, Nat.zero_add] at hg hz
    rw [ArithCircuit.size_eq_length]; dsimp only [etrWordToCircuit]
    rw [etrWordToRawCircuit_eq]; dsimp only
    rw [hsos_len]
    simp only [List.length_cons, List.length_append, List.length_nil]
    nlinarith

/-! ### Reduction Map `etrWordToARM3` -/

/-- **Polynomial-time many-one reduction `etrWordToARM3`** from `ETR` to `ARM(3)`. -/
@[expose] def etrWordToARM3 (word : List Bool) : ARMInstance :=
  compileCircuit (etrWordToCircuit word)

/-- Equisatisfiability of `etrWordToARM3`: `word ∈ ETR ↔ etrWordToARM3 word ∈ ARM 3`. -/
theorem etrWordToARM3_mem_iff (word : List Bool) :
    word ∈ ETR ↔ etrWordToARM3 word ∈ ARM 3 :=
  (etrWordToCircuit_sat_iff word).trans (circuit_iff_arm3 (etrWordToCircuit word))

end Cslib.Complexity
