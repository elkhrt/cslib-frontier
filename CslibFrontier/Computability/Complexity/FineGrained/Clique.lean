/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CliqueReduction
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Fine-Grained $n^{o(k)}$ Lower Bound for $k$-Clique under ETH

This module proves the fine-grained $n^{o(q)}$ ETH lower bound for parameterized `Clique`
using the block-coloring reduction `threeColoringToClique` from `CliqueReduction.lean`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

private theorem exists_computableInO_validBlockColorings :
    ∃ Cv Dv : ℕ, 2 ≤ Cv ∧
      ComputableInO (fun p : Graph × List ℕ => validBlockColorings p.1 p.2)
        (encPair encGraph (encList encNat)) (encList encNat)
        (fun p => 2 ^ (Cv * p.2.length) * ((encPair encGraph (encList encNat) p).length + 1) ^ Dv)
        (fun p => 2 ^ (Cv * p.2.length) * ((encPair encGraph (encList encNat) p).length +
          1) ^ Dv) := by
  let encGB := encPair encGraph (encList encNat)
  let encSt := encPair encGB (encPair encNat (encList encNat))
  let vStep : ((Graph × List ℕ) × (ℕ × List ℕ)) → ((Graph × List ℕ) × (ℕ × List ℕ)) :=
    fun s => (s.1, (s.2.1 +
      1, if isProperBlockColoring s.1.1 s.1.2 s.2.1 then s.2.1 :: s.2.2 else s.2.2))
  have hvStep : ComputableInPolyTime vStep encSt encSt := by
    have hgb := fst encGB (encPair encNat (encList encNat))
    have hc := (fst encNat (encList encNat)).comp (snd encGB (encPair encNat (encList encNat)))
    have hacc := (snd encNat (encList encNat)).comp (snd encGB (encPair encNat (encList encNat)))
    exact hgb.prod ((binary_add.comp (hc.prod (const 1))).prod
      ((computableInPolyTime_isProperBlockColoring.comp (hgb.prod hc)).ite'
        ((cons encNat).comp (hc.prod hacc)) hacc))
  obtain ⟨dS, _, hvStep_deg⟩ := hvStep.exists_degree
  let nFun : Graph × List ℕ → ℕ := fun p => 2 ^ (2 * p.2.length)
  have hn_poly : ComputableInPolyTime nFun encGB encNat :=
    binary_two_pow.comp (unary_mul.comp ((const 2).prod ((length_list encNat).comp (snd _ _))))
  let initFun : Graph × List ℕ → (Graph × List ℕ) × (ℕ × List ℕ) := fun p => (p, (0, []))
  have hinit_poly : ComputableInPolyTime initFun encGB encSt :=
    ComputableInPolyTime.id'.prod ((const 0).prod (const []))
  obtain ⟨dn, _, hn_deg⟩ := hn_poly.exists_degree
  obtain ⟨di, _, hi_deg⟩ := hinit_poly.exists_degree
  have hread : ComputableInPolyTime (fun s : (Graph × List ℕ) × (ℕ × List ℕ) => s.2.2)
      encSt (encList encNat) := (snd _ _).comp (snd _ _)
  obtain ⟨dr, _, hr_deg⟩ := hread.exists_degree
  have hstep_inv : ∀ (p : Graph × List ℕ) (k : ℕ),
      (vStep^[k] (initFun p)).1 = p ∧ (vStep^[k] (initFun p)).2.1 = k ∧
      (vStep^[k] (initFun p)).2.2.length ≤ k ∧ ∀ x ∈ (vStep^[k] (initFun p)).2.2, x < k := by
    intro p k; induction k with
    | zero => simp [initFun]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨ih.1, by simp [vStep, ih.2.1], ?_, fun x hx => ?_⟩
      · set s := vStep^[k] (initFun p)
        have hlen := ih.2.2.1
        dsimp only [vStep]
        split_ifs
        · simp only [List.length_cons]; omega
        · omega
      · simp only [vStep, ih.2.1] at hx
        split_ifs at hx with h
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact Nat.lt_succ_self x
          · exact (ih.2.2.2 x hx').trans (Nat.lt_succ_self _)
        · exact (ih.2.2.2 x hx).trans (Nat.lt_succ_self _)
  let Bbound : Graph × List ℕ → ℕ :=
    fun p => 4 * (encGB p).length + 2 ^ (2 * p.2.length) * (10 * p.2.length + 10) + 20
  have hB : ∀ p k, k ≤ nFun p → (encSt (vStep^[k] (initFun p))).length ≤ Bbound p := by
    intro p k hk
    have hinv := hstep_inv p k
    have hk_len : (encNat k).length ≤ 2 * p.2.length + 1 :=
      length_encNat_le_of_lt_two_pow
        (hk.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have hacc_elem : ∀ x ∈ (vStep^[k] (initFun p)).2.2, (encNat x).length ≤ 2 * p.2.length + 1 :=
      fun x hx => length_encNat_le_of_lt_two_pow
        (((hinv.2.2.2 x hx).trans_le hk).trans
          (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have hacc_len := (length_encList_le encNat
      (vStep^[k] (initFun p)).2.2 hacc_elem).trans
      (Nat.mul_le_mul_right _ (hinv.2.2.1.trans hk))
    dsimp only [nFun] at hacc_len
    have hacc_len' : (encList encNat (vStep^[k] (initFun p)).2.2).length ≤
        2 ^ (2 * p.2.length) * (4 * p.2.length + 3) :=
      hacc_len.trans_eq (by ring)
    have h2p : 1 ≤ 2 ^ (2 * p.2.length) := Nat.one_le_two_pow
    simp only [encNat_apply] at hk_len
    simp only [encSt, length_encPair, hinv.1, hinv.2.1]
    dsimp [Bbound]; nlinarith
  have hit := hr_deg.inO.comp (ComputableInO.iterate hn_deg.inO hi_deg.inO hvStep_deg.inO
    (R := fun p => (Bbound p + 1) ^ dS) (Q := fun p => (Bbound p + 1) ^ dS) (B := Bbound)
    (fun p k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hB p k hk) 1) dS)
    (fun p k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hB p k hk) 1) dS) hB)
  have hB_le : ∀ p, Bbound p + 1 ≤ 40 * 2 ^ (2 * p.2.length) * ((encGB p).length + 1) ^ 2 := by
    intro p
    have hbl : p.2.length ≤ (encGB p).length := by
      have := length_le_length_encList encNat p.2; simp only [encGB, length_encPair]; omega
    have h2p : 1 ≤ 2 ^ (2 * p.2.length) := Nat.one_le_two_pow
    have h1 : 4 * (encGB p).length + 21 ≤ 21 * ((encGB p).length + 1) ^ 2 := by nlinarith
    have h2 : 21 * ((encGB p).length + 1) ^ 2 ≤
        21 * 2 ^ (2 * p.2.length) * ((encGB p).length + 1) ^ 2 := by nlinarith
    have hlin : 10 * p.2.length + 10 ≤ 10 * ((encGB p).length + 1) ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_left (2 ^ (2 * p.2.length)) hlin
    dsimp [Bbound]; nlinarith
  let Cv := 2 * (dS + dr + 4)
  let Dv := 2 * (dS + dr + dn + di + 4)
  have hvbc_bound : ∀ p : Graph × List ℕ,
      let t := (nFun p + 1) * (Bbound p + 1) ^ dS + (nFun p + 1) * Bbound p +
        (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2 +
        ((encGB p).length + 1) ^ dn + ((encGB p).length + 1) ^ di +
        (Bbound p + 1) ^ dr + Bbound p
      t ≤ 40 ^ (dS + dr + 4) * 16 * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv := by
    intro p
    have h1 := hB_le p
    have h2 : (encNat (nFun p)).length ≤ 2 * p.2.length + 1 := by
      change (encNat (2 ^ (2 * p.2.length))).length ≤ _; rw [length_encNat_two_pow]
    have h3 : p.2.length ≤ (encGB p).length := by
      have := length_le_length_encList encNat p.2; simp only [encGB, length_encPair]; omega
    have hpow_B : (Bbound p + 1) ^ dS ≤
        (40 ^ dS) * 2 ^ (2 * dS * p.2.length) * ((encGB p).length + 1) ^ (2 * dS) :=
      (Nat.pow_le_pow_left h1 dS).trans_eq (by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring_nf)
    have hpow_R : (Bbound p + 1) ^ dr ≤
        (40 ^ dr) * 2 ^ (2 * dr * p.2.length) * ((encGB p).length + 1) ^ (2 * dr) :=
      (Nat.pow_le_pow_left h1 dr).trans_eq (by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring_nf)
    have h2p : 1 ≤ 2 ^ (2 * p.2.length) := Nat.one_le_two_pow
    have hL1 : 1 ≤ (encGB p).length + 1 := by omega
    have hmono_L : ∀ a ≤ Dv, ((encGB p).length + 1) ^ a ≤ ((encGB p).length + 1) ^ Dv :=
      fun a ha => Nat.pow_le_pow_right hL1 ha
    have hmono_2 : ∀ a ≤ Cv, 2 ^ (a * p.2.length) ≤ 2 ^ (Cv * p.2.length) :=
      fun a ha => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ha)
    have h40_1 : 40 ^ dS ≤ 40 ^ (dS + dr + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h40_2 : 40 ^ dr ≤ 40 ^ (dS + dr + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h40_3 : 1 ≤ 40 ^ (dS + dr + 4) := Nat.one_le_pow _ _ (by norm_num)
    have h40le : 40 ≤ 40 ^ (dS + dr + 4) :=
      (show 40 = 40 ^ 1 by norm_num).symm ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
    have hDn := hmono_L dn (by dsimp [Dv]; omega); have hDi := hmono_L di (by dsimp [Dv]; omega)
    have hD2 := hmono_L 2 (by dsimp [Dv]; omega); have hD2s :=
      hmono_L (2 * dS) (by dsimp [Dv]; omega)
    have hD2r := hmono_L (2 * dr) (by dsimp [Dv]; omega); have hC2 :=
      hmono_2 2 (by dsimp [Cv]; omega)
    have hC2r := hmono_2 (2 * dr) (by dsimp [Cv]; omega)
    have hC2s : 2 ^ (2 * p.2.length) * 2 ^ (2 * dS * p.2.length) ≤ 2 ^ (Cv * p.2.length) := by
      rw [← pow_add, show 2 * p.2.length + 2 * dS * p.2.length = (2 * dS + 2) * p.2.length by ring]
      exact hmono_2 (2 * dS + 2) (by dsimp [Cv]; omega)
    have hC4 : 2 ^ (2 * p.2.length) * 2 ^ (2 * p.2.length) ≤ 2 ^ (Cv * p.2.length) := by
      rw [← pow_add, show 2 * p.2.length + 2 * p.2.length = 4 * p.2.length by ring]
      exact hmono_2 4 (by dsimp [Cv]; omega)
    have h12 : (2 * p.2.length + 1 + 1) ^ 2 ≤ 16 * ((encGB p).length + 1) ^ 2 := by nlinarith
    have hBB : Bbound p ≤ 40 * 2 ^ (2 * p.2.length) * ((encGB p).length + 1) ^ 2 := by omega
    have h2C : 1 ≤ 2 ^ (Cv * p.2.length) := Nat.one_le_two_pow
    have hLD : 1 ≤ ((encGB p).length + 1) ^ Dv := Nat.one_le_pow _ _ hL1
    have hnp1 : nFun p + 1 ≤ 2 * 2 ^ (2 * p.2.length) := by dsimp [nFun]; omega
    have hmul1 : (nFun p + 1) * (Bbound p + 1) ^ dS ≤
        2 * 40 ^ (dS + dr + 4) * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv := by
      calc (nFun p + 1) * (Bbound p + 1) ^ dS
          ≤ 2 * 40 ^ dS * (2 ^ (2 * p.2.length) * 2 ^ (2 * dS * p.2.length)) *
              ((encGB p).length + 1) ^ (2 * dS) := (Nat.mul_le_mul hnp1 hpow_B).trans_eq (by ring)
        _ ≤ _ := by gcongr
    have hmul2 : (nFun p + 1) * Bbound p ≤
        2 * 40 ^ (dS + dr + 4) * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv := by
      calc (nFun p + 1) * Bbound p
          ≤ 2 * 40 * (2 ^ (2 * p.2.length) * 2 ^ (2 * p.2.length)) *
              ((encGB p).length + 1) ^ 2 := (Nat.mul_le_mul hnp1 hBB).trans_eq (by ring)
        _ ≤ _ := by gcongr
    have hmul3 : (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2 ≤
        2 * 16 * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv := by
      calc (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2
          ≤ 2 * 16 * 2 ^ (2 * p.2.length) * ((encGB p).length + 1) ^ 2 :=
            (Nat.mul_le_mul hnp1 ((Nat.pow_le_pow_left (by omega) 2).trans h12)).trans_eq (by ring)
        _ ≤ _ := by gcongr
    have hmulR : (Bbound p + 1) ^ dr ≤
        40 ^ (dS + dr + 4) * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv :=
      hpow_R.trans (by gcongr)
    have hmulB : Bbound p ≤
        40 ^ (dS + dr + 4) * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv :=
      hBB.trans (by gcongr)
    have hmuln : ((encGB p).length + 1) ^ dn ≤
        40 ^ (dS + dr + 4) * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv := by
      have := Nat.mul_le_mul (Nat.mul_le_mul h40_3 h2C) hDn; linarith
    have hmuli : ((encGB p).length + 1) ^ di ≤
        40 ^ (dS + dr + 4) * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv := by
      have := Nat.mul_le_mul (Nat.mul_le_mul h40_3 h2C) hDi; linarith
    have h16 : 40 ^ (dS + dr + 4) ≤ 40 ^ (dS + dr + 4) * 16 := by omega
    nlinarith
  refine ⟨Cv, Dv, by dsimp [Cv]; omega,
    (hit.mono (40 ^ (dS + dr + 4) * 16) (fun p => ?_) (fun p => ?_)).of_enc_eq fun p => ?_⟩
  · have hvb := hvbc_bound p
    have hB_end : ((encSt (vStep^[nFun p] (initFun p))).length + 1) ^ dr ≤ (Bbound p + 1) ^ dr :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (hB p (nFun p) le_rfl) 1) dr
    have hdist : (nFun p + 1) * ((Bbound p + 1) ^ dS + Bbound p + ((encNat (nFun p)).length +
      1) ^ 2) =
        (nFun p + 1) * (Bbound p + 1) ^ dS + (nFun p + 1) * Bbound p +
          (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2 := by ring
    have hsucc : 40 ^ (dS + dr + 4) * 16 * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv ≤
        40 ^ (dS + dr + 4) * 16 * (2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv + 1) := by
      rw [mul_assoc (40 ^ (dS + dr + 4) * 16)]
      exact Nat.mul_le_mul_left _ (Nat.le_succ _)
    dsimp only [encGB] at hvb hsucc ⊢; linarith
  · have hvb := hvbc_bound p
    have hB_end : ((encSt (vStep^[nFun p] (initFun p))).length + 1) ^ dr ≤ (Bbound p + 1) ^ dr :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (hB p (nFun p) le_rfl) 1) dr
    have hB1 : (Bbound p + 1) ^ dS ≤ (nFun p + 1) * (Bbound p + 1) ^ dS :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hlen_sq : (encNat (nFun p)).length ≤
      (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2 := by
      have h1 : (encNat (nFun p)).length ≤ ((encNat (nFun p)).length + 1) ^ 2 := by nlinarith
      exact h1.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hsucc : 40 ^ (dS + dr + 4) * 16 * 2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv ≤
        40 ^ (dS + dr + 4) * 16 * (2 ^ (Cv * p.2.length) * ((encGB p).length + 1) ^ Dv + 1) := by
      rw [mul_assoc (40 ^ (dS + dr + 4) * 16)]
      exact Nat.mul_le_mul_left _ (Nat.le_succ _)
    dsimp only [encGB] at hvb hsucc ⊢
    calc ((encPair encGraph (encList encNat) p).length + 1) ^ dn +
            ((encPair encGraph (encList encNat) p).length + 1) ^ di +
            (Bbound p + 1) ^ dS + Bbound p + (encNat (nFun p)).length +
            ((encSt (vStep^[nFun p] (initFun p))).length + 1) ^ dr
        ≤ ((encPair encGraph (encList encNat) p).length + 1) ^ dn +
            ((encPair encGraph (encList encNat) p).length + 1) ^ di +
            (nFun p + 1) * (Bbound p + 1) ^ dS + Bbound p +
            (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2 + (Bbound p + 1) ^ dr := by
          linarith [hB1, hlen_sq, hB_end]
      _ ≤ (nFun p + 1) * (Bbound p + 1) ^ dS + (nFun p + 1) * Bbound p +
            (nFun p + 1) * ((encNat (nFun p)).length + 1) ^ 2 +
            ((encPair encGraph (encList encNat) p).length + 1) ^ dn +
            ((encPair encGraph (encList encNat) p).length + 1) ^ di +
            (Bbound p + 1) ^ dr + Bbound p := by omega
      _ ≤ 40 ^ (dS + dr + 4) * 16 *
            (2 ^ (Cv * p.2.length) * ((encPair encGraph (encList encNat) p).length + 1) ^ Dv + 1) :=
          hvb.trans hsucc
  · have hEq : ∀ (k : ℕ), (vStep^[k] (initFun p)).2 =
        ((fun st : ℕ × List ℕ =>
          (st.1 + 1, if isProperBlockColoring p.1 p.2 st.1 then st.1 :: st.2 else st.2))^[k] (0,
            [])) := by
      intro k; induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        simp [vStep, (hstep_inv p k).1]
    simp [validBlockColorings, hEq, nFun]

private theorem hlen_bv_le (G : Graph) (q r : ℕ) :
    let b := blockSize G.distinctVertices.length q
    (encPair encUnary (encList encNat)
      (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).length ≤
      2 * r + 2 ^ (2 * b) * (4 * b + 4) + 4 := by
  intro b
  have hbl' : (vertexBlock G.distinctVertices q r).length ≤ b := List.length_take_le _ _
  have h1 : ∀ c ∈ validBlockColorings G (vertexBlock G.distinctVertices q r),
      (encNat c).length ≤ 2 * b := fun c hc =>
    length_encNat_le_of_lt_two_pow ((((validBlockColorings_mem_iff G _ c).mp hc).1).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hlen_l : (validBlockColorings G (vertexBlock G.distinctVertices q r)).length ≤
      2 ^ (2 * b) := (validBlockColorings_length_le G _).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hl := (length_encList_le encNat _ h1).trans (Nat.mul_le_mul_right _ hlen_l)
  have h4 : 2 * (2 * b) + 1 ≤ 4 * b + 4 := by omega
  have hl' := hl.trans (Nat.mul_le_mul_left _ h4)
  simp only [length_encPair, encUnary_apply, List.length_replicate]; omega

private theorem exists_computableInO_buildRev (Cv Dv : ℕ) (hCv2 : 2 ≤ Cv)
    (hvbc : ComputableInO (fun p : Graph × List ℕ => validBlockColorings p.1 p.2)
      (encPair encGraph (encList encNat)) (encList encNat)
      (fun p => 2 ^ (Cv * p.2.length) * ((encPair encGraph (encList encNat) p).length + 1) ^ Dv)
      (fun p => 2 ^ (Cv * p.2.length) * ((encPair encGraph (encList encNat) p).length + 1) ^ Dv)) :
    ∃ Drev : ℕ, Dv ≤ Drev ∧ 2 ≤ Drev ∧ ∀ (q : ℕ) (_hq : 1 ≤ q) (m : ℕ), ∃ Km : ℕ,
      ComputableInO
        (fun G : Graph =>
          ((List.range m).map fun r =>
            (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)
        encGraph (encList (encPair encUnary (encList encNat)))
        (fun G => Km * 2 ^ (Cv * blockSize G.distinctVertices.length q) *
          ((encGraph G).length + 1) ^ Drev)
        (fun G => Km * 2 ^ (Cv * blockSize G.distinctVertices.length q) *
          ((encGraph G).length + 1) ^ Drev) := by
  let encGB := encPair encGraph (encList encNat)
  let encBV := encPair encUnary (encList encNat)
  obtain ⟨dV, _, hV_deg⟩ := Graph.computableInPolyTime_distinctVertices.exists_degree
  have hcons_inO := (ComputableInDegree.cons encBV).inO_one
  obtain ⟨dVB, _, hVB_deg⟩ := computableInPolyTime_vertexBlock.exists_degree
  let Drev := max Dv 2 + (dVB + 1) * max dV 1 + 4
  refine ⟨Drev, by dsimp [Drev]; omega, by dsimp [Drev]; omega, fun q hq m => ?_⟩
  induction m with
  | zero =>
    refine ⟨1, (ComputableInO.const ([] : List (ℕ × List ℕ))).mono 1 (fun G => ?_)
      (fun G => ?_)⟩ <;>
    · simp only [one_mul]
      have : 1 ≤ 2 ^ (Cv * blockSize G.distinctVertices.length q) := Nat.one_le_two_pow
      have : (encGraph G).length ≤ ((encGraph G).length + 1) ^ Drev :=
        (Nat.le_succ _).trans (Nat.le_self_pow (by dsimp [Drev]; omega) _)
      nlinarith
  | succ m ihm =>
    obtain ⟨Km, hKm⟩ := ihm
    have hG_V : ∀ G : Graph, (encList encNat G.distinctVertices).length ≤ (encGraph G).length :=
      fun G =>
      (length_encList_le_of_nodup_subset G.nodup_distinctVertices
        (fun _ hx => G.mem_distinctVertices.mp hx)).trans
        (by simp [encGraph_apply]; omega)
    have hrm_len : ∀ G : Graph,
        (encGB (G, vertexBlock G.distinctVertices q m)).length ≤
          12 * ((encGraph G).length + 1) := by
      intro G
      have hsub : (vertexBlock G.distinctVertices q m).Sublist G.distinctVertices :=
        (List.take_sublist _ _).trans (List.drop_sublist _ _)
      have h1 := (length_encList_mono_sublist hsub).trans (hG_V G)
      simp only [encGB, length_encPair]; omega
    have hpair_qm : ComputableInO (fun G : Graph => ((G.distinctVertices, q), m))
        encGraph (encPair (encPair (encList encNat) encUnary) encUnary)
        (fun G => (q + m + 4) * ((encGraph G).length + 1) ^ (max dV 1))
        (fun G => (q + m + 4) * ((encGraph G).length + 1) ^ (max dV 1)) := by
      have h := ((hV_deg.inO.prod (ComputableInO.const (encMid := encUnary) q)).prod
        (ComputableInO.const (encMid := encUnary) m))
      refine h.mono 4 (fun G => ?_) (fun G => ?_) <;>
      · have : ((encGraph G).length + 1) ^ dV ≤ ((encGraph G).length + 1) ^ (max dV 1) :=
          Nat.pow_le_pow_right (by omega) (le_max_left _ _)
        have : (encGraph G).length ≤ ((encGraph G).length + 1) ^ (max dV 1) :=
          (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
        have : 1 ≤ ((encGraph G).length + 1) ^ (max dV 1) := Nat.one_le_pow _ _ (by omega)
        nlinarith
    have hvb_m := hVB_deg.inO.comp hpair_qm
    have hgb_m := (ComputableInO.id' (encMid := encGraph)).prod hvb_m
    have hsingle := hvbc.comp hgb_m
    have hpair_m := (ComputableInO.const (encMid := encUnary) m).prod hsingle
    have hcons_m := hcons_inO.comp (hpair_m.prod hKm)
    have hpair_len : ∀ G : Graph,
        (encPair (encPair (encList encNat) encUnary) encUnary ((G.distinctVertices, q), m)).length ≤
          (4 * q + 4 * m + 12) * ((encGraph G).length + 1) := fun G => by
      have := hG_V G; simp only [length_encPair, encUnary_apply, List.length_replicate]; nlinarith
    let K_next := 2 * (4 * q + 4 * m + 16) ^ (dVB + 1) + 13 ^ (Dv + 1) + Km +
      (4 * q + 20 * m ^ 2 + 21 * m + 60)
    have hstep_bound : ∀ G : Graph,
        let b := blockSize G.distinctVertices.length q
        let L := (encGraph G).length
        (q + m + 4) * (L + 1) ^ max dV 1 +
          ((encPair (encPair (encList encNat) encUnary) encUnary
            ((G.distinctVertices, q), m)).length + 1) ^ dVB +
          (L + 2 ^ (Cv * (vertexBlock G.distinctVertices q m).length) *
            ((encGB (G, vertexBlock G.distinctVertices q m)).length + 1) ^ Dv) +
          (L + m) + Km * 2 ^ (Cv * b) * (L + 1) ^ Drev +
          (encPair encBV (encList encBV)
            ((m, validBlockColorings G (vertexBlock G.distinctVertices q m)),
              ((List.range m).map fun r =>
                (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length ≤
          K_next * 2 ^ (Cv * b) * (L + 1) ^ Drev := by
      intro G b L
      have hbl : (vertexBlock G.distinctVertices q m).length ≤ b := List.length_take_le _ _
      have h2b : 2 ^ (Cv * (vertexBlock G.distinctVertices q m).length) ≤ 2 ^ (Cv * b) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left Cv hbl)
      have h2b1 : 1 ≤ 2 ^ (Cv * b) := Nat.one_le_two_pow
      have hL1 : 1 ≤ (L + 1) ^ Drev := Nat.one_le_pow _ _ (by omega)
      have hLDv : ((encGB (G, vertexBlock G.distinctVertices q m)).length + 1) ^ Dv ≤
          13 ^ (Dv + 1) * (L + 1) ^ Drev := by
        calc _ ≤ (13 * (L + 1)) ^ Dv := Nat.pow_le_pow_left (by have := hrm_len G; omega) Dv
          _ = 13 ^ Dv * (L + 1) ^ Dv := mul_pow _ _ _
          _ ≤ 13 ^ (Dv + 1) * (L + 1) ^ Drev :=
              Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
                (Nat.pow_le_pow_right (by omega) (by dsimp [Drev]; omega))
      have hLVB : ((encPair (encPair (encList encNat) encUnary) encUnary
            ((G.distinctVertices, q), m)).length + 1) ^ dVB ≤
          (4 * q + 4 * m + 16) ^ dVB * (L + 1) ^ Drev := by
        have h1 : (encPair (encPair (encList encNat) encUnary) encUnary
              ((G.distinctVertices, q), m)).length + 1 ≤
            (4 * q + 4 * m + 16) * (L + 1) := by have := hpair_len G; nlinarith
        have hdVB : dVB ≤ Drev := by
          have : dVB ≤ (dVB + 1) * max dV 1 := by
            have := Nat.le_mul_of_pos_right (dVB + 1) (show 0 < max dV 1 by omega); omega
          dsimp [Drev]; omega
        calc _ ≤ ((4 * q + 4 * m + 16) * (L + 1)) ^ dVB := Nat.pow_le_pow_left h1 dVB
          _ = (4 * q + 4 * m + 16) ^ dVB * (L + 1) ^ dVB := mul_pow _ _ _
          _ ≤ (4 * q + 4 * m + 16) ^ dVB * (L + 1) ^ Drev :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdVB)
      have hL_le : L ≤ (L + 1) ^ Drev :=
        (Nat.le_succ L).trans (Nat.le_self_pow (by dsimp [Drev]; omega) _)
      have hmax_le : max dV 1 ≤ Drev := by
        have : max dV 1 ≤ (dVB + 1) * max dV 1 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        dsimp [Drev]; omega
      have hqm_le : (q + m + 4) * (L + 1) ^ (max dV 1) ≤ (4 * q + 4 * m + 16) * (L + 1) ^ Drev :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hmax_le)
      have hpow_qm : (4 * q + 4 * m + 16) ^ dVB ≤ (4 * q + 4 * m + 16) ^ (dVB + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hmul_vbc : 2 ^ (Cv * (vertexBlock G.distinctVertices q m).length) *
          ((encGB (G, vertexBlock G.distinctVertices q m)).length + 1) ^ Dv ≤
          13 ^ (Dv + 1) * 2 ^ (Cv * b) * (L + 1) ^ Drev :=
        (Nat.mul_le_mul h2b hLDv).trans_eq (by ring)
      have hcons_len : (encPair encBV (encList encBV)
          ((m, validBlockColorings G (vertexBlock G.distinctVertices q m)),
            ((List.range m).map fun r =>
              (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length ≤
          (4 * q + 20 * m ^ 2 + 20 * m + 40) * 2 ^ (Cv * b) * (L + 1) ^ Drev := by
        have hlist_le : (encList encBV (((List.range m).map fun r =>
              (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length ≤
            m * (2 * (2 * m + 2 ^ (2 * b) * (4 * b + 4) + 4) + 2) := by
          have hall : ∀ x ∈ (((List.range m).map fun r =>
              (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse),
              (encBV x).length ≤ 2 * m + 2 ^ (2 * b) * (4 * b + 4) + 4 := by
            intro x hx; simp only [List.mem_reverse, List.mem_map, List.mem_range] at hx
            obtain ⟨r, hr, rfl⟩ := hx
            have hrb : (encBV (r,
              validBlockColorings G (vertexBlock G.distinctVertices q r))).length ≤
                2 * r + 2 ^ (2 * b) * (4 * b + 4) + 4 := hlen_bv_le G q r
            omega
          have hl := length_encList_le encBV _ hall
          simp only [List.length_reverse, List.length_map, List.length_range] at hl
          exact hl.trans (Nat.mul_le_mul_left m (by omega))
        have hbl_L : b ≤ L + 1 := blockSize_le_encGraph_succ hq G
        have h2_Cv : 2 ^ (2 * b) ≤ 2 ^ (Cv * b) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right b hCv2)
        have hL2 : (L + 1) ^ 2 ≤ (L + 1) ^ Drev :=
          Nat.pow_le_pow_right (by omega) (by dsimp [Drev]; omega)
        have h1m : (encBV (m, validBlockColorings G (vertexBlock G.distinctVertices q m))).length ≤
            2 * m + 2 ^ (2 * b) * (4 * b + 4) + 4 := hlen_bv_le G q m
        have h4b : 4 * b + 4 ≤ 8 * (L + 1) ^ 2 := by nlinarith
        have hmul_b : 2 ^ (2 * b) * (4 * b + 4) ≤ 8 * 2 ^ (Cv * b) * (L + 1) ^ Drev := by
          calc 2 ^ (2 * b) * (4 * b + 4) ≤ 2 ^ (Cv * b) * (8 * (L + 1) ^ 2) :=
            Nat.mul_le_mul h2_Cv h4b
            _ ≤ 2 ^ (Cv * b) * (8 * (L + 1) ^ Drev) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 8 hL2)
            _ = 8 * 2 ^ (Cv * b) * (L + 1) ^ Drev := by ring
        have hmul_m : m * (2 * (2 * m + 2 ^ (2 * b) * (4 * b + 4) + 4) + 2) =
            m * (2 * (2 ^ (2 * b) * (4 * b + 4))) + (4 * m ^ 2 + 10 * m) := by ring
        have hmul_mb : m * (2 * (2 ^ (2 * b) * (4 * b + 4))) ≤
            16 * m * (2 ^ (Cv * b) * (L + 1) ^ Drev) := by
          have := Nat.mul_le_mul_left (2 * m) hmul_b; linarith
        have hmul_m2 : 4 * m ^ 2 + 10 * m + 4 * m + 9 ≤
            (4 * m ^ 2 + 14 * m + 16) * (2 ^ (Cv * b) * (L + 1) ^ Drev) :=
          (show 4 * m ^ 2 + 10 * m + 4 * m + 9 ≤ 4 * m ^ 2 + 14 * m + 16 by omega).trans
            (Nat.le_mul_of_pos_right _ (Nat.mul_pos h2b1 hL1))
        simp only [length_encPair]; nlinarith
      have hK1 : (q + m + 4) * (L + 1) ^ max dV 1 ≤
          (4 * q + 4 * m + 16) * (2 ^ (Cv * b) * (L + 1) ^ Drev) := by
        have := Nat.mul_le_mul hqm_le h2b1; linarith
      have hK2 : ((encPair (encPair (encList encNat) encUnary) encUnary
          ((G.distinctVertices, q), m)).length + 1) ^ dVB ≤
          (4 * q + 4 * m + 16) ^ (dVB + 1) * (2 ^ (Cv * b) * (L + 1) ^ Drev) := by
        have h := hLVB.trans (Nat.mul_le_mul_right _ hpow_qm)
        have h' := Nat.mul_le_mul h h2b1; linarith
      have hK3 : 2 * L + m ≤ (m + 20) * (2 ^ (Cv * b) * (L + 1) ^ Drev) := by
        have h2L : 2 * L + m ≤ (m + 2) * (L + 1) ^ Drev := by nlinarith
        have := Nat.mul_le_mul h2L h2b1; nlinarith
      have hKsum : (4 * q + 4 * m + 16) + (4 * q + 4 * m + 16) ^ (dVB + 1) + 13 ^ (Dv + 1) +
          (m + 20) + Km + (4 * q + 20 * m ^ 2 + 20 * m + 40) ≤ K_next := by
        have h1 : 4 * q + 4 * m + 16 ≤ (4 * q + 4 * m + 16) ^ (dVB + 1) :=
          Nat.le_self_pow (by omega) _
        dsimp [K_next]; omega
      have hKmul := Nat.mul_le_mul_right (2 ^ (Cv * b) * (L + 1) ^ Drev) hKsum
      linarith [hmul_vbc, hcons_len, hK1, hK2, hK3, hKmul]
    refine ⟨4 * K_next, (hcons_m.mono 4 (fun G => ?_) (fun G => ?_)).of_enc_eq fun G => ?_⟩
    · have hsb := hstep_bound G
      have h4 : K_next * 2 ^ (Cv * blockSize G.distinctVertices.length q) *
            ((encGraph G).length + 1) ^ Drev ≤
          4 * (4 * K_next * 2 ^ (Cv * blockSize G.distinctVertices.length q) *
            ((encGraph G).length + 1) ^ Drev + 1) := by
        have := Nat.mul_le_mul_right
          (2 ^ (Cv * blockSize G.distinctVertices.length q) * ((encGraph G).length + 1) ^ Drev)
          (show K_next ≤ 16 * K_next by omega)
        linarith
      simp only [Function.comp_apply] at hsb ⊢; linarith
    · have hsb := hstep_bound G
      have h4 : K_next * 2 ^ (Cv * blockSize G.distinctVertices.length q) *
            ((encGraph G).length + 1) ^ Drev ≤
          4 * (4 * K_next * 2 ^ (Cv * blockSize G.distinctVertices.length q) *
            ((encGraph G).length + 1) ^ Drev + 1) := by
        have := Nat.mul_le_mul_right
          (2 ^ (Cv * blockSize G.distinctVertices.length q) * ((encGraph G).length + 1) ^ Drev)
          (show K_next ≤ 16 * K_next by omega)
        linarith
      simp only [Function.comp_apply] at hsb ⊢; linarith
    · exact congrArg (encList encBV)
        (by simp [List.range_succ, List.map_append, List.reverse_append])

/-- For each fixed constant `q ≥ 1`, `threeColoringToClique q` is computable in time
`O(2 ^ (C * blockSize |V| q) * (|G| + 1) ^ D)` for universal constants `C, D` independent of `q`! -/
theorem exists_computableInO_threeColoringToClique :
    ∃ C D : ℕ, ∀ (q : ℕ), 1 ≤ q →
      ∃ K : ℕ,
        ComputableInO (threeColoringToClique q) encGraph encCliqueInstance
          (fun G => K * 2 ^ (C * blockSize G.distinctVertices.length q) *
            ((encGraph G).length + 1) ^ D)
          (fun G => K * 2 ^ (C * blockSize G.distinctVertices.length q) *
            ((encGraph G).length + 1) ^ D) := by
  let encBV := encPair encUnary (encList encNat)
  obtain ⟨dP, _, hPdeg⟩ := computableInPolyTime_postClique.exists_degree
  obtain ⟨Cv, Dv, hCv2, hvbc⟩ := exists_computableInO_validBlockColorings
  obtain ⟨Drev, hDv_le, hDrev2, hbuild_rev⟩ := exists_computableInO_buildRev Cv Dv hCv2 hvbc
  have hrev_bv : ComputableInPolyTime (List.reverse (α := ℕ × List ℕ))
      (encList encBV) (encList encBV) := listReverse encBV
  obtain ⟨dRev, _, hRev_deg⟩ := hrev_bv.exists_degree
  obtain ⟨dV, _, hV_deg⟩ := Graph.computableInPolyTime_distinctVertices.exists_degree
  let C := max Cv (2 * (max dRev dP) + 4) * (max dRev dP + 2)
  let D := Drev + dV + 2 * (max dRev dP + 2) + 2
  refine ⟨C, D, fun q hq => ?_⟩
  obtain ⟨Kq, hKq⟩ := hbuild_rev q hq q
  have hbv := hRev_deg.inO.comp hKq
  have harg := (((ComputableInO.id' (encMid := encGraph)).prod hV_deg.inO).prod
    ((ComputableInO.const (encMid := encUnary) q).prod hbv))
  have hfin := hPdeg.inO.comp harg
  have hbv_enc_le : ∀ G : Graph,
      (encList encBV ((List.range q).map fun r =>
        (r, validBlockColorings G (vertexBlock G.distinctVertices q r)))).length ≤
        (32 * q ^ 2 + 32 * q + 32) * 2 ^ (2 * blockSize G.distinctVertices.length q) *
          ((encGraph G).length + 1) ^ 2 := by
    intro G
    set b := blockSize G.distinctVertices.length q
    have hbl_L : b ≤ (encGraph G).length + 1 := blockSize_le_encGraph_succ hq G
    have hall : ∀ x ∈ ((List.range q).map fun r =>
        (r, validBlockColorings G (vertexBlock G.distinctVertices q r))),
        (encBV x).length ≤ 2 * q + 2 ^ (2 * b) * (4 * b + 4) + 4 := by
      intro x hx; simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hrb : (encBV (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).length ≤
          2 * r + 2 ^ (2 * b) * (4 * b + 4) + 4 := hlen_bv_le G q r
      omega
    have h1 := length_encList_le encBV _ hall
    have h2b1 : 1 ≤ 2 ^ (2 * b) := Nat.one_le_two_pow
    have hsq : (encGraph G).length + 1 ≤ ((encGraph G).length + 1) ^ 2 := by nlinarith
    have h1sq : 1 ≤ ((encGraph G).length + 1) ^ 2 := by nlinarith
    simp only [List.length_map, List.length_range] at h1
    have h2 : q * (2 * (2 * q + 2 ^ (2 * b) * (4 * b + 4) + 4) + 1) =
        2 ^ (2 * b) * (8 * q * b + 8 * q) + (4 * q ^ 2 + 9 * q) := by ring
    have hqb : q * b ≤ q * ((encGraph G).length + 1) := Nat.mul_le_mul_left q hbl_L
    have h3 : 8 * q * b + 8 * q ≤ (16 * q + 16) * ((encGraph G).length + 1) ^ 2 := by
      have : 8 * q * b + 8 * q ≤ 16 * q * ((encGraph G).length + 1) := by nlinarith
      have := Nat.mul_le_mul_left (16 * q) hsq
      nlinarith
    have h4 : 2 ^ (2 * b) * (8 * q * b + 8 * q) ≤
        2 ^ (2 * b) * ((16 * q + 16) * ((encGraph G).length + 1) ^ 2) :=
      Nat.mul_le_mul_left _ h3
    have h5 : 4 * q ^ 2 + 9 * q ≤
        (32 * q ^ 2 + 16 * q + 16) * 2 ^ (2 * b) * ((encGraph G).length + 1) ^ 2 := by
      have hqsq : 4 * q ^ 2 + 9 * q ≤ 32 * q ^ 2 + 16 * q + 16 := by nlinarith
      have hprod := Nat.mul_le_mul hqsq (Nat.mul_le_mul h2b1 h1sq)
      linarith
    linarith
  let Kfin := (Kq + (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) + 20) * 16
  have hfin_bound : ∀ G : Graph,
      let b := blockSize G.distinctVertices.length q
      let L := (encGraph G).length
      L + (L + 1) ^ dV + (L + q) + (Kq * 2 ^ (Cv * b) * (L + 1) ^ Drev +
        ((encList encBV (((List.range q).map fun r =>
          (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length +
            1) ^ dRev) +
      ((encPair (encPair encGraph (encList encNat)) (encPair encUnary (encList encBV))
        ((G, G.distinctVertices), (q, (List.range q).map fun r =>
          (r, validBlockColorings G (vertexBlock G.distinctVertices q r))))).length + 1) ^ dP ≤
      Kfin * 2 ^ (C * b) * (L + 1) ^ D := by
    intro G b L
    have hbv_L := hbv_enc_le G
    have hrev_len : (encList encBV (((List.range q).map fun r =>
        (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length =
        (encList encBV ((List.range q).map fun r =>
          (r, validBlockColorings G (vertexBlock G.distinctVertices q r)))).length := by
      simp [length_encList]
    have harg_len : (encPair (encPair encGraph (encList encNat)) (encPair encUnary (encList encBV))
        ((G, G.distinctVertices), (q, (List.range q).map fun r =>
          (r, validBlockColorings G (vertexBlock G.distinctVertices q r))))).length + 1 ≤
        (32 * q ^ 2 + 64 * q + 64) * 2 ^ (2 * b) * (L + 1) ^ 2 := by
      have h2 := length_encList_le_of_nodup_subset (enc := encNat) G.nodup_distinctVertices
        (fun _ hx => G.mem_distinctVertices.mp hx)
      have h3 : (encList encNat G.vertices).length ≤ L := by
        simp [L, encGraph_apply]; omega
      have h2b1 : 1 ≤ 2 ^ (2 * b) := Nat.one_le_two_pow
      have hL1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h6L : 6 * L + 5 ≤ 32 * (L + 1) ^ 2 := by nlinarith
      have h2q : 2 * q ≤ 32 * q * (L + 1) ^ 2 := by
        have := Nat.mul_le_mul_left (32 * q) hL1; omega
      have hlin : 6 * L + 2 * q + 5 ≤ (32 * q + 32) * (L + 1) ^ 2 := by linarith
      have hlin2 : 6 * L + 2 * q + 5 ≤ (32 * q + 32) * 2 ^ (2 * b) * (L + 1) ^ 2 := by
        calc 6 * L + 2 * q + 5 ≤ (32 * q + 32) * (L + 1) ^ 2 := hlin
          _ = (32 * q + 32) * 1 * (L + 1) ^ 2 := by ring
          _ ≤ (32 * q + 32) * 2 ^ (2 * b) * (L + 1) ^ 2 := by gcongr
      have hsum : (32 * q + 32) * 2 ^ (2 * b) * (L + 1) ^ 2 +
            (32 * q ^ 2 + 32 * q + 32) * 2 ^ (2 * b) * (L + 1) ^ 2 =
          (32 * q ^ 2 + 64 * q + 64) * 2 ^ (2 * b) * (L + 1) ^ 2 := by ring
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [L, b] at hbv_L h3 hlin2 hsum ⊢
      linarith [h2, h3, hbv_L, hlin2, hsum]
    have hpow_rev : ((encList encBV (((List.range q).map fun r =>
        (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length +
          1) ^ dRev ≤
        (32 * q ^ 2 + 64 * q + 64) ^ dRev * 2 ^ (2 * dRev * b) * (L + 1) ^ (2 * dRev) := by
      have h1 : (encList encBV (((List.range q).map fun r =>
          (r, validBlockColorings G (vertexBlock G.distinctVertices q r))).reverse)).length + 1 ≤
          (32 * q ^ 2 + 64 * q + 64) * 2 ^ (2 * b) * (L + 1) ^ 2 := by
        rw [hrev_len]
        have h2b1 : 1 ≤ 2 ^ (2 * b) := Nat.one_le_two_pow
        have hL1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        have h32 : 1 ≤ 32 * 2 ^ (2 * b) * (L + 1) ^ 2 := by nlinarith
        dsimp only [L, b] at hbv_L h32 ⊢; nlinarith
      exact (Nat.pow_le_pow_left h1 dRev).trans_eq
        (by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring_nf)
    have hpow_P : ((encPair (encPair encGraph (encList encNat)) (encPair encUnary (encList encBV))
        ((G, G.distinctVertices), (q, (List.range q).map fun r =>
          (r, validBlockColorings G (vertexBlock G.distinctVertices q r))))).length + 1) ^ dP ≤
        (32 * q ^ 2 + 64 * q + 64) ^ dP * 2 ^ (2 * dP * b) * (L + 1) ^ (2 * dP) :=
      (Nat.pow_le_pow_left harg_len dP).trans_eq
        (by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring_nf)
    have h2_C1 : 2 ^ (Cv * b) ≤ 2 ^ (C * b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right b
        ((le_max_left _ _).trans (Nat.le_mul_of_pos_right _ (by omega))))
    have h2_C2 : 2 ^ (2 * dRev * b) ≤ 2 ^ (C * b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right b
        (((show 2 * dRev ≤ 2 * max dRev dP + 4 by omega).trans (le_max_right _ _)).trans
          (Nat.le_mul_of_pos_right _ (by omega))))
    have h2_C3 : 2 ^ (2 * dP * b) ≤ 2 ^ (C * b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right b
        (((show 2 * dP ≤ 2 * max dRev dP + 4 by omega).trans (le_max_right _ _)).trans
          (Nat.le_mul_of_pos_right _ (by omega))))
    have h2C1 : 1 ≤ 2 ^ (C * b) := Nat.one_le_two_pow
    have hLD1 : (L + 1) ^ Drev ≤ (L + 1) ^ D :=
      Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega)
    have hLD2 : (L + 1) ^ (2 * dRev) ≤ (L + 1) ^ D :=
      Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega)
    have hLD3 : (L + 1) ^ (2 * dP) ≤ (L + 1) ^ D :=
      Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega)
    have hLD4 : (L + 1) ^ dV ≤ (L + 1) ^ D := Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega)
    have hL_D : L ≤ (L + 1) ^ D := (Nat.le_succ L).trans (Nat.le_self_pow (by dsimp [D]; omega) _)
    have h1_D : 1 ≤ (L + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    have hKp1 : (32 * q ^ 2 + 64 * q + 64) ^ dRev ≤
      (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hKp2 : (32 * q ^ 2 + 64 * q + 64) ^ dP ≤ (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hKp3 : q ≤ (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) :=
      (by omega : q ≤ 32 * q ^ 2 + 64 * q + 64).trans (Nat.le_self_pow (by omega) _)
    have hKq_le : Kq * 2 ^ (Cv * b) * (L + 1) ^ Drev ≤ Kq * 2 ^ (C * b) * (L + 1) ^ D := by gcongr
    have hrev_le : (32 * q ^ 2 + 64 * q + 64) ^ dRev * 2 ^ (2 * dRev * b) * (L + 1) ^ (2 * dRev) ≤
        (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) * 2 ^ (C * b) * (L + 1) ^ D := by gcongr
    have hP_le : (32 * q ^ 2 + 64 * q + 64) ^ dP * 2 ^ (2 * dP * b) * (L + 1) ^ (2 * dP) ≤
        (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) * 2 ^ (C * b) * (L + 1) ^ D := by gcongr
    have hV_le : (L + 1) ^ dV ≤ 2 ^ (C * b) * (L + 1) ^ D :=
      (Nat.le_mul_of_pos_left _ h2C1).trans (Nat.mul_le_mul_left _ hLD4)
    have hL_le' : L ≤ 2 ^ (C * b) * (L + 1) ^ D :=
      (Nat.le_mul_of_pos_left _ h2C1).trans (Nat.mul_le_mul_left _ hL_D)
    have hq_le : q ≤
      (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) * 2 ^ (C * b) * (L + 1) ^ D := by
      have := Nat.mul_le_mul (Nat.mul_le_mul hKp3 h2C1) h1_D; linarith
    have hX : Kq * 2 ^ (C * b) * (L + 1) ^ D +
        3 * ((32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) * 2 ^ (C * b) * (L + 1) ^ D) +
        3 * (2 ^ (C * b) * (L + 1) ^ D) ≤ Kfin * 2 ^ (C * b) * (L + 1) ^ D := by
      have h20 : Kq + 3 * (32 * q ^ 2 + 64 * q + 64) ^ (max dRev dP + 1) + 3 ≤ Kfin := by
        dsimp [Kfin]; omega
      have hmul := Nat.mul_le_mul_right (2 ^ (C * b) * (L + 1) ^ D) h20
      linarith
    linarith [hKq_le, hrev_le, hP_le, hV_le, hL_le', hq_le, hpow_rev, hpow_P, hX]
  refine ⟨Kfin, (hfin.mono 4 (fun G => ?_) (fun G => ?_)).of_enc_eq fun G => ?_⟩
  · have hfb := hfin_bound G
    have h4 : Kfin * 2 ^ (C * blockSize G.distinctVertices.length q) * ((encGraph G).length +
      1) ^ D ≤
        4 * (Kfin * 2 ^ (C * blockSize G.distinctVertices.length q) * ((encGraph G).length +
          1) ^ D + 1) := by
      have := Nat.mul_le_mul_right
        (2 ^ (C * blockSize G.distinctVertices.length q) * ((encGraph G).length + 1) ^ D)
        (show Kfin ≤ 4 * Kfin by omega)
      linarith
    simp only [Function.comp_apply, List.reverse_reverse] at hfb ⊢; linarith
  · have hfb := hfin_bound G
    have h4 : Kfin * 2 ^ (C * blockSize G.distinctVertices.length q) * ((encGraph G).length +
      1) ^ D ≤
        4 * (Kfin * 2 ^ (C * blockSize G.distinctVertices.length q) * ((encGraph G).length +
          1) ^ D + 1) := by
      have := Nat.mul_le_mul_right
        (2 ^ (C * blockSize G.distinctVertices.length q) * ((encGraph G).length + 1) ^ D)
        (show Kfin ≤ 4 * Kfin by omega)
      linarith
    simp only [Function.comp_apply, List.reverse_reverse] at hfb ⊢; linarith
  · simp [threeColoringToClique, threeColoringToCliqueGraph]

/-- **Unconditional transfer**: if `Clique` is decidable in time
`f(q) · (N + 2)^{o(q)} · L^{O(1)}` (for every `ε > 0`, some `f : ℕ → ℕ` and `e : ℕ` achieve
`DecidableInTimeO Clique encCliqueInstance (fun x => f x.m * (N + 2)^(ε * x.m) * (L + 1)^e)`),
then `ThreeColoring` is decidable in subexponential time `2^{o(|V| + |E|)}`.
-/
theorem decidableInSubexpTime_ThreeColoring_of_clique_noq
    (hClique : ∀ ε : ℝ, 0 < ε → ∃ (f : ℕ → ℕ) (e : ℕ),
      DecidableInTimeO Clique encCliqueInstance
        fun x => (f x.m : ℝ) * ((x.graph.vertices.length : ℝ) + 2) ^ (ε * (x.m : ℝ)) *
          (((encCliqueInstance x).length : ℝ) + 1) ^ e) :
    DecidableInSubexpTime ThreeColoring encGraph
      fun G => G.vertices.length + G.edges.length := by
  obtain ⟨C, D, hRed⟩ := exists_computableInO_threeColoringToClique
  intro δ hδ
  -- Step 1: choose `ε := δ / 4` to fix `f` and `e`!
  obtain ⟨f, e, hDec⟩ := hClique (δ / 4) (by positivity)
  obtain ⟨g, t, kC, hg, hgClq, ht⟩ := hDec.exists_computableInO
  -- Step 2: choose fixed constant `q ≥ 1` large enough that `(C + 4 * e + 8) / q ≤ δ / 2`!
  let q : ℕ := ⌈((C + 4 * e + 8 : ℕ) : ℝ) / (δ / 2)⌉₊ + 1
  have hq : 1 ≤ q := by omega
  obtain ⟨K, hRed_q⟩ := hRed q hq
  -- Compose `g` with `threeColoringToClique q`!
  have hcomp := hg.comp hRed_q
  have hcorr : ∀ G : Graph, G ∈ ThreeColoring ↔ g (threeColoringToClique q G) = true :=
    fun G => (threeColoringToClique_mem_iff hq G).symm.trans (hgClq _)
  -- Bound the composed runtime by `K' * 2 ^ (δ * (|V| + |E|)) * (L_G + 1) ^ (D + e + 2)`!
  have hbq : ∀ G : Graph, (blockSize G.distinctVertices.length q : ℝ) ≤
      ((G.vertices.length + G.edges.length : ℕ) : ℝ) / (q : ℝ) + 1 := by
    intro G
    have hV : G.distinctVertices.length ≤ G.vertices.length :=
      G.length_distinctVertices.le.trans (List.toFinset_card_le G.vertices)
    have h1 : blockSize G.distinctVertices.length q ≤ G.vertices.length / q + 1 := by
      unfold blockSize
      have hdiv := Nat.div_le_div_right (c :=
        q) (show G.distinctVertices.length + q - 1 ≤ G.vertices.length + q by omega)
      have hadd : (G.vertices.length + q) / q = G.vertices.length / q + 1 :=
        Nat.add_div_right _ (by omega)
      omega
    have h2 : ((G.vertices.length / q : ℕ) : ℝ) ≤ (G.vertices.length : ℝ) / (q : ℝ) :=
      Nat.cast_div_le
    have h3 : (G.vertices.length : ℝ) / (q : ℝ) ≤
        ((G.vertices.length + G.edges.length : ℕ) : ℝ) / (q : ℝ) := by
      gcongr; exact_mod_cast Nat.le_add_right _ _
    have h1r : (blockSize G.distinctVertices.length q : ℝ) ≤
        ((G.vertices.length / q : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hdiv_le : ((C + 4 * e + 8 : ℕ) : ℝ) / (q : ℝ) ≤ δ / 2 := by
    have hq_ge : ((C + 4 * e + 8 : ℕ) : ℝ) / (δ / 2) ≤ (q : ℝ) :=
      (Nat.le_ceil _).trans (by dsimp [q]; push_cast; linarith)
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    rw [div_le_iff₀ hq_pos]
    have h := (div_le_iff₀ (show (0 : ℝ) < δ / 2 by positivity)).mp hq_ge
    linarith
  -- Compute explicit constant `K'` absorbing all `q`-dependent factors!
  set Bq : ℝ := 48 * ((q : ℝ) + 1) ^ 2 * 16 * (2 * (q : ℝ) + 4) + 48 * ((q : ℝ) + 1) +
    1 with hBq_def
  set Aq : ℝ := ((q : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) * (2 : ℝ) ^ (δ / 2 * (q : ℝ)) *
    (2 : ℝ) ^ (4 * (e : ℝ)) * Bq ^ e with hAq_def
  have hBq_pos : 0 < Bq := by rw [hBq_def]; positivity
  have hAq_nonneg : 0 ≤ Aq := by rw [hAq_def]; positivity
  let K' : ℕ := ⌈(K : ℝ) * (2 : ℝ) ^ (C : ℝ) + (kC : ℝ) * (f q : ℝ) * Aq + (kC : ℝ) + 4⌉₊
  refine ⟨D + e + 2, DecidableInTimeO.of_computableInO hcomp hcorr
    (T := fun G => (K' : ℝ) * ((2 : ℝ) ^ (δ * ((G.vertices.length + G.edges.length : ℕ) : ℝ)) *
      (((encGraph G).length : ℝ) + 1) ^ (D + e + 2)))
    (fun G => ?_) |>.mono K' (fun G => le_add_of_le_of_nonneg le_rfl (Nat.cast_nonneg _))
    (fun G => by positivity)⟩
  set n := G.vertices.length + G.edges.length
  set b := blockSize G.distinctVertices.length q
  set L := (encGraph G).length
  have hred_t : ((K * 2 ^ (C * b) * (L + 1) ^ D : ℕ) : ℝ) ≤
      ((K : ℝ) * (2 : ℝ) ^ (C : ℝ)) * ((2 : ℝ) ^ (δ * (n : ℝ)) * ((L : ℝ) + 1) ^ (D + e + 2)) := by
    have hCb : (C : ℝ) * (b : ℝ) ≤ (C : ℝ) + (δ / 2) * (n : ℝ) := by
      have hCq : (C : ℝ) / (q : ℝ) ≤ δ / 2 :=
        (div_le_div_of_nonneg_right (by exact_mod_cast (show C ≤ C + 4 * e + 8 by omega))
          (by positivity)).trans hdiv_le
      have hmul : (C : ℝ) * (b : ℝ) ≤ (C : ℝ) * ((n : ℝ) / (q : ℝ)) + (C : ℝ) := by
        have := mul_le_mul_of_nonneg_left (hbq G) (Nat.cast_nonneg C); linarith
      have hmul2 : ((C : ℝ) / (q : ℝ)) * (n : ℝ) ≤ (δ / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hCq (Nat.cast_nonneg n)
      linarith [hmul, hmul2, show (C : ℝ) * ((n : ℝ) / (q : ℝ)) =
        ((C : ℝ) / (q : ℝ)) * (n : ℝ) by ring]
    have hpow : (2 : ℝ) ^ (C * b) ≤ (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ (δ * (n : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (C * b), ← Real.rpow_add (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      push_cast; linarith [hCb, mul_nonneg (show (0 : ℝ) ≤ δ / 2 by linarith) (Nat.cast_nonneg (α :=
        ℝ) n)]
    have hLp : ((L : ℝ) + 1) ^ D ≤ ((L : ℝ) + 1) ^ (D + e + 2) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) L]) (by omega)
    push_cast
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg K)) hLp (by positivity)
      (by positivity)).trans_eq (by ring)
  have hdec_t : (t (threeColoringToClique q G) : ℝ) ≤
      ((kC : ℝ) * (f q : ℝ) * Aq + (kC : ℝ)) *
        ((2 : ℝ) ^ (δ * (n : ℝ)) * ((L : ℝ) + 1) ^ (D + e + 2)) := by
    have ht1 : (t (threeColoringToClique q G) : ℝ) ≤
        (kC : ℝ) * ((f q : ℝ) *
          (((threeColoringToClique q G).graph.vertices.length : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) *
          (((encCliqueInstance (threeColoringToClique q G)).length : ℝ) + 1) ^ e) + (kC : ℝ) :=
      ht (threeColoringToClique q G)
    have hN : (((threeColoringToClique q G).graph.vertices.length : ℝ) + 2) ≤
        ((q : ℝ) + 2) * (2 : ℝ) ^ (2 * b) := by
      have h1r : ((threeColoringToCliqueGraph q G).vertices.length : ℝ) ≤
        (q : ℝ) * (2 : ℝ) ^ (2 * b) := by
        exact_mod_cast length_threeColoringToCliqueGraph_vertices_le q G
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * b) := by exact_mod_cast Nat.one_le_two_pow
      dsimp [threeColoringToClique]; linarith
    have hLH : (((encCliqueInstance (threeColoringToClique q G)).length : ℝ) + 1) ≤
        Bq * (2 : ℝ) ^ (4 * b) * ((L : ℝ) + 1) := by
      have h1 := length_encCliqueInstance_threeColoringToClique_le q G
      have hb_le_L : (b : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast blockSize_le_encGraph_succ hq G
      have h1r : ((encCliqueInstance (threeColoringToClique q G)).length : ℝ) ≤
          48 * ((q : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (4 * b) * ((b : ℝ) + (q : ℝ) + 2) + 48 * ((q : ℝ) +
            1) := by
        have hpow4 : ((2 ^ (2 * b)) ^ 2 : ℕ) = 2 ^ (4 * b) := by rw [← pow_mul]; ring_nf
        rw [hpow4] at h1; exact_mod_cast h1
      have h2 : (b : ℝ) + (q : ℝ) + 2 ≤ (2 * (q : ℝ) + 4) * ((L : ℝ) + 1) := by
        have hqL : (q : ℝ) ≤ (q : ℝ) * ((L : ℝ) + 1) :=
          le_mul_of_one_le_right (Nat.cast_nonneg q) (by linarith [Nat.cast_nonneg (α := ℝ) L])
        linarith
      have h24b : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * b) := by exact_mod_cast Nat.one_le_two_pow
      have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) L]
      have h12 : 48 * ((q : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (4 * b) * ((b : ℝ) + (q : ℝ) + 2) ≤
          48 * ((q : ℝ) + 1) ^ 2 * 16 * (2 * (q : ℝ) + 4) * ((2 : ℝ) ^ (4 * b) * ((L : ℝ) +
            1)) := by
        have hA : (0 : ℝ) ≤ 48 * ((q : ℝ) + 1) ^ 2 * (2 * (q : ℝ) + 4) *
            ((2 : ℝ) ^ (4 * b) * ((L : ℝ) + 1)) := by positivity
        have hmul : 48 * ((q : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (4 * b) * ((b : ℝ) + (q : ℝ) + 2) ≤
            48 * ((q : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (4 * b) * ((2 * (q : ℝ) + 4) * ((L : ℝ) + 1)) := by
              gcongr
        linarith
      have h48q : 48 * ((q : ℝ) + 1) + 1 ≤
          (48 * ((q : ℝ) + 1) + 1) * ((2 : ℝ) ^ (4 * b) * ((L : ℝ) + 1)) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le h24b hL1)
      rw [hBq_def]; linarith
    have hexp_N : ((2 : ℝ) ^ (2 * b)) ^ ((δ / 4) * (q : ℝ)) ≤
        (2 : ℝ) ^ (δ / 2 * (q : ℝ)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * b), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_add (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hbq_mul : (b : ℝ) * (q : ℝ) ≤ (n : ℝ) + (q : ℝ) := by
        have := mul_le_mul_of_nonneg_right (hbq G) (le_of_lt hqpos)
        rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hqpos), one_mul] at this
      have hmul := mul_le_mul_of_nonneg_left hbq_mul (show (0 : ℝ) ≤ δ / 2 by linarith)
      push_cast; linarith [hmul, show (2 * (b : ℝ)) * ((δ / 4) * (q : ℝ)) =
        (δ / 2) * ((b : ℝ) * (q : ℝ)) by ring]
    have hexp_L : ((2 : ℝ) ^ (4 * b)) ^ e ≤
      (2 : ℝ) ^ (4 * (e : ℝ)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ)) := by
      rw [← pow_mul, ← Real.rpow_natCast (2 : ℝ) (4 * b * e), ← Real.rpow_add (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h4eq : ((4 * e : ℕ) : ℝ) / (q : ℝ) ≤ δ / 2 :=
        (div_le_div_of_nonneg_right (by exact_mod_cast (show 4 * e ≤ C + 4 * e + 8 by omega))
          (by positivity)).trans hdiv_le
      push_cast
      have hmul1 : (4 * (e : ℝ)) * (b : ℝ) ≤ (4 * (e : ℝ)) * ((n : ℝ) / (q : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (hbq G) (by positivity)
      have hmul2 : ((4 * (e : ℝ)) / (q : ℝ)) * (n : ℝ) ≤ (δ / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by push_cast at h4eq; exact h4eq) (Nat.cast_nonneg n)
      linarith [hmul1, hmul2, show (4 : ℝ) * (b : ℝ) * (e : ℝ) = (4 * (e : ℝ)) * (b : ℝ) by ring,
        show (4 * (e : ℝ)) * ((n : ℝ) / (q : ℝ) + 1) =
          ((4 * (e : ℝ)) / (q : ℝ)) * (n : ℝ) + 4 * (e : ℝ) by ring]
    have hpow_comb :
        (((threeColoringToClique q G).graph.vertices.length : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) *
          (((encCliqueInstance (threeColoringToClique q G)).length : ℝ) + 1) ^ e ≤
        Aq * ((2 : ℝ) ^ (δ * (n : ℝ)) * ((L : ℝ) + 1) ^ (D + e + 2)) := by
      have hNpow : (((threeColoringToClique q G).graph.vertices.length : ℝ) +
        2) ^ ((δ / 4) * (q : ℝ)) ≤
          ((q : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) * ((2 : ℝ) ^ (2 * b)) ^ ((δ / 4) * (q : ℝ)) :=
        (Real.rpow_le_rpow (by positivity) hN (by positivity)).trans_eq
          (Real.mul_rpow (by positivity) (by positivity))
      have hLpow : (((encCliqueInstance (threeColoringToClique q G)).length : ℝ) + 1) ^ e ≤
          Bq ^ e * ((2 : ℝ) ^ (4 * b)) ^ e * ((L : ℝ) + 1) ^ e :=
        (pow_le_pow_left₀ (by positivity) hLH e).trans_eq (by rw [mul_pow, mul_pow])
      have h2split : (2 : ℝ) ^ ((δ / 2) * (n : ℝ)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ)) =
          (2 : ℝ) ^ (δ * (n : ℝ)) := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      have hLe : ((L : ℝ) + 1) ^ e ≤ ((L : ℝ) + 1) ^ (D + e + 2) :=
        pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) L]) (by omega)
      calc _ ≤ (((q : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) * ((2 : ℝ) ^ (2 * b)) ^ ((δ / 4) * (q : ℝ))) *
            (Bq ^ e * ((2 : ℝ) ^ (4 * b)) ^ e * ((L : ℝ) + 1) ^ e) := by gcongr
        _ ≤ (((q : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) *
              ((2 : ℝ) ^ (δ / 2 * (q : ℝ)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ)))) *
            (Bq ^ e * ((2 : ℝ) ^ (4 * (e : ℝ)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ))) * ((L : ℝ) +
              1) ^ (D + e + 2)) := by
              gcongr
        _ = Aq * (((2 : ℝ) ^ ((δ / 2) * (n : ℝ)) * (2 : ℝ) ^ ((δ / 2) * (n : ℝ))) * ((L : ℝ) +
          1) ^ (D + e + 2)) := by
              rw [hAq_def]; ring
        _ = _ := by rw [h2split]
    have h1env : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)) * ((L : ℝ) + 1) ^ (D + e + 2) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
        (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) L]))
    have hmul_kC := mul_le_mul_of_nonneg_left hpow_comb
      (show (0 : ℝ) ≤ (kC : ℝ) * (f q : ℝ) by positivity)
    have hkC1 : (kC : ℝ) ≤ (kC : ℝ) * ((2 : ℝ) ^ (δ * (n : ℝ)) * ((L : ℝ) + 1) ^ (D + e + 2)) :=
      le_mul_of_one_le_right (Nat.cast_nonneg kC) h1env
    linarith [ht1, hmul_kC, hkC1, show (kC : ℝ) * ((f q : ℝ) *
        (((threeColoringToClique q G).graph.vertices.length : ℝ) + 2) ^ ((δ / 4) * (q : ℝ)) *
        (((encCliqueInstance (threeColoringToClique q G)).length : ℝ) + 1) ^ e) =
      (kC : ℝ) * (f q : ℝ) * ((((threeColoringToClique q G).graph.vertices.length : ℝ) +
        2) ^ ((δ / 4) * (q : ℝ)) *
        (((encCliqueInstance (threeColoringToClique q G)).length : ℝ) + 1) ^ e) by ring]
  have hK' := Nat.le_ceil ((K : ℝ) * (2 : ℝ) ^ (C : ℝ) + (kC : ℝ) * (f q : ℝ) * Aq + (kC : ℝ) + 4)
  have hpos_env : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)) * ((L : ℝ) + 1) ^ (D + e + 2) := by positivity
  have hmul_K' := mul_le_mul_of_nonneg_right hK' hpos_env
  push_cast at hred_t ⊢
  dsimp only [K'] at hK' hmul_K' ⊢
  linarith [hred_t, hdec_t, hmul_K']

/-- **ETH Lower Bound for $k$-Clique**:
Under `ETH`, `Clique` has no `f(q) · (N + 2)^{o(q)} · L^{O(1)}` algorithm.
-/
theorem ETH.not_decidableInTimeO_Clique_noq (hETH : ETH) :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ (f : ℕ → ℕ) (e : ℕ),
      DecidableInTimeO Clique encCliqueInstance
        fun x => (f x.m : ℝ) * ((x.graph.vertices.length : ℝ) + 2) ^ (ε * (x.m : ℝ)) *
          (((encCliqueInstance x).length : ℝ) + 1) ^ e :=
  fun h => hETH.not_decidableInSubexpTime_ThreeColoring
    (decidableInSubexpTime_ThreeColoring_of_clique_noq h)

end Cslib.Complexity

