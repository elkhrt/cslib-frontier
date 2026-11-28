/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP

import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Closure Properties of `NEXP`

This module proves that `NEXP` is closed under intersection with `P`.

## Main results

* `Cslib.Complexity.inter_mem_NEXP_of_mem_P`: if `A ∈ P enc` and `B ∈ NEXP enc`, then
  `A ∩ B ∈ NEXP enc`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- `NEXP` is closed under intersection with `P`. -/
theorem inter_mem_NEXP_of_mem_P {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hA : A ∈ P enc) (hB : B ∈ NEXP enc) : A ∩ B ∈ NEXP enc := by
  obtain ⟨decA, hdecA, hA_iff⟩ := hA
  obtain ⟨k, hBk⟩ := mem_NEXP_iff.1 hB
  obtain ⟨V, c, hVO, hViff⟩ := exists_verifier_of_mem_NTIME hBk
  have hV_pt : ComputableInPolyTime V (encPair enc encBits) encBool :=
    hVO.computableInPolyTime id'.polyBounded_length id'.polyBounded_length
  have hV'_pt : ComputableInPolyTime (fun p : α × List Bool ↦ decA p.1 && V p)
      (encPair enc encBits) encBool :=
    (hdecA.comp (fst _ _)).bool_and' hV_pt
  obtain ⟨TV, SV, hTV, -, hV'O⟩ := hV'_pt.exists_computableInO
  obtain ⟨CV, DV, hCV⟩ := hTV.exists_le
  have hExp_pt : ComputableInPolyTime
      (fun a : α ↦ c + (enc a).length ^ k + (enc a).length + 1) enc encUnary := by
    have h1 := (unary_pow k).comp (encoding_length enc)
    have h2 := encoding_length enc
    fun_prop
  obtain ⟨CL, hℓO⟩ := hExp_pt.exists_computableInO_unary_two_pow
  let K : ℕ := 2 * DV + 2
  have hge : ∀ a : α, c * 2 ^ (enc a).length ^ k + c ≤
      2 ^ (c + (enc a).length ^ k + (enc a).length + 1) := fun a ↦ by
    have h1 : 2 * c ≤ 2 ^ (c + 1) := by
      have := c.lt_two_pow_self; rw [pow_succ]; omega
    have h2 : c * 2 ^ (enc a).length ^ k + c ≤ (2 * c) * 2 ^ (enc a).length ^ k := by
      have := Nat.one_le_two_pow (n := (enc a).length ^ k); nlinarith
    calc c * 2 ^ (enc a).length ^ k + c
        ≤ (2 * c) * 2 ^ (enc a).length ^ k := h2
      _ ≤ 2 ^ (c + 1) * 2 ^ (enc a).length ^ k := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (c + 1 + (enc a).length ^ k) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (c + (enc a).length ^ k + (enc a).length + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hchar : A ∩ B =
      { a | ∃ w : List Bool, w.length = 2 ^ (c + (enc a).length ^ k + (enc a).length + 1) ∧
        (decA a && V (a, w)) = true } := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Bool.and_eq_true, hA_iff]
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨w, hw, hVw⟩ := (hViff a _ (hge a)).1 hb
      exact ⟨w, hw, ha, hVw⟩
    · rintro ⟨w, hw, ha, hVw⟩
      exact ⟨ha, (hViff a _ (hge a)).2 ⟨w, hw, hVw⟩⟩
  have hmem_ntime : A ∩ B ∈ NTIME enc (fun L ↦ 2 ^ (K * (c + L ^ k + L + 1))) := by
    rw [hchar]
    refine setOf_exists_mem_NTIME hℓO hV'O (C := 1 + CL + 1 + CV * 2 ^ (2 * DV)) fun a w hw ↦ ?_
    set L := (enc a).length
    set E := c + L ^ k + L + 1
    have hL_lt : L < 2 ^ E := lt_of_lt_of_le L.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
    have hL_le : L ≤ 2 ^ E := le_of_lt hL_lt
    have h2L : 2 ^ L ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega)
    have hpair_le : (encPair enc encBits (a, w)).length + 1 ≤ 2 ^ (E + 2) := by
      simp only [length_encPair, encBits_apply, hw]
      change 2 * L + 1 + 2 ^ E + 1 ≤ 2 ^ (E + 2)
      have h3 : 4 * 2 ^ E = 2 ^ (E + 2) := by rw [pow_add]; ring
      omega
    have hTV_le : TV (a, w) ≤ CV * 2 ^ (2 * DV) * 2 ^ (DV * E) := by
      calc TV (a, w) ≤ CV * ((encPair enc encBits (a, w)).length + 1) ^ DV := hCV (a, w)
        _ ≤ CV * (2 ^ (E + 2)) ^ DV := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpair_le DV)
        _ = CV * 2 ^ (DV * E + 2 * DV) := by rw [← Nat.pow_mul]; congr 2; ring
        _ = CV * (2 ^ (2 * DV) * 2 ^ (DV * E)) := by rw [← pow_add, Nat.add_comm]
        _ = CV * 2 ^ (2 * DV) * 2 ^ (DV * E) := by rw [Nat.mul_assoc]
    have h4E : 4 ^ E = 2 ^ (2 * E) := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← Nat.pow_mul]
    have hKE1 : 2 ^ E ≤ 2 ^ (K * E) := Nat.pow_le_pow_right (by omega) (by dsimp [K]; nlinarith)
    have hKE2 : 2 ^ (2 * E) ≤ 2 ^ (K * E) :=
      Nat.pow_le_pow_right (by omega) (by dsimp [K]; nlinarith)
    have hKE3 : 2 ^ (DV * E) ≤ 2 ^ (K * E) :=
      Nat.pow_le_pow_right (by omega) (by dsimp [K]; nlinarith)
    have h4E_le : 4 ^ E ≤ 2 ^ (K * E) := h4E ▸ hKE2
    have h1 : L ≤ 2 ^ (K * E) := le_trans hL_le hKE1
    have h2 : CL * 2 ^ L ≤ CL * 2 ^ (K * E) := Nat.mul_le_mul_left CL (le_trans h2L hKE1)
    have h3 : TV (a, w) ≤ CV * 2 ^ (2 * DV) * 2 ^ (K * E) :=
      le_trans hTV_le (Nat.mul_le_mul_left _ hKE3)
    dsimp only [K] at h4E_le h1 h2 h3 ⊢
    nlinarith
  have hpoly : Cslib.PolynomiallyBounded (fun L ↦ K * (c + L ^ k + L + 1)) := by
    rw [Cslib.polynomiallyBounded_iff_le]
    exact ⟨K * (c + 3), k + 1, fun L ↦ by
      have h1 : 1 ≤ (L + 1) ^ (k + 1) := Nat.one_le_pow _ _ (Nat.succ_pos L)
      have hL : L ≤ (L + 1) ^ (k + 1) :=
        le_trans (Nat.le_succ L) (Nat.le_self_pow (Nat.succ_ne_zero k) (L + 1))
      have hLk : L ^ k ≤ (L + 1) ^ (k + 1) :=
        le_trans (Nat.pow_le_pow_left (Nat.le_succ L) k)
          (Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ k))
      have hsum : c + L ^ k + L + 1 ≤ (c + 3) * (L + 1) ^ (k + 1) := by nlinarith
      calc K * (c + L ^ k + L + 1)
          ≤ K * ((c + 3) * (L + 1) ^ (k + 1)) := Nat.mul_le_mul_left K hsum
        _ = K * (c + 3) * (L + 1) ^ (k + 1) := by ring⟩
  exact NTIME_two_pow_subset_NEXP hpoly hmem_ntime

end Cslib.Complexity
