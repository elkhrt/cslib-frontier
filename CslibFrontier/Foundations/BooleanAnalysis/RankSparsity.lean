/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.BooleanAnalysis.ConstantSubspace

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted Adaptive Parity Decision Trees and Fourier Rank-Sparsity Bounds

This module proves the weighted refinement of Sanyal's Fourier rank-sparsity theorem for Boolean
functions `f : (ι → Bool) → Bool` over arbitrary finite index types `ι` under standard Lean axioms:
every Boolean function `f` with Fourier sparsity `k(f) > 1` satisfies
`r(f) = O(√(δ(f) k(f)) log₂ k(f))`, equivalently `δ(f) = Ω(r(f)^2 / (k(f) (log₂ k(f))^2))`,
recovering Sanyal's bound `r(f) = O(√(k(f)) log₂ k(f))` via `δ(f) ≤ 1`.

## Main results

* `CslibFrontier.BooleanFunction.ParityFiberBasis.exists_nonconstant_restrict_ratio_le`:
  Cheeger-ratio
  selection of a non-constant parity fiber with `δ(f|_b) / k(f|_b) ≤ 4 k(f) δ(f) / ℓ^2`.
* `CslibFrontier.BooleanFunction.ParityFiberBasis.exists_sanyal_step`: single coset-reduction step
  adjoining at most `3 √(δ(f|_b) k(f|_b))` parities while dropping the coset count by at least
  `k(f|_b) / 2`.
* `CslibFrontier.BooleanFunction.exists_parity_determining_set_from`,
  `CslibFrontier.BooleanFunction.exists_parity_determining_set`: non-adaptive parity-determining set
  of
  cardinality at most `12 √(δ(f) k(f)) log₂ k(f)`.
* `CslibFrontier.BooleanFunction.fourierRank_le_mul_sqrt_weight_sparsity_logb`: weighted Fourier
  rank
  upper bound `r(f) ≤ 12 √(δ(f) k(f)) log₂ k(f)` for `k(f) > 1`.
* `CslibFrontier.BooleanFunction.boolWeight_ge_div_sparsity_mul_sq_rank_div_logb`: Chang-type
  Boolean
  weight lower bound `r(f)^2 / (144 k(f) (log₂ k(f))^2) ≤ δ(f)` for `k(f) > 1`.
* `CslibFrontier.BooleanFunction.fourierRank_le_mul_sqrt_sparsity_logb`: unweighted Sanyal bound
  `r(f) ≤ 12 √(k(f)) log₂ k(f)` for `k(f) > 1`.
-/

public section

namespace CslibFrontier.BooleanFunction

open Cslib Cslib.BitString Finset
open scoped BigOperators

section ParityFibersAndSanyal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Cheeger-ratio fiber selection lemma**: for any Boolean function `f` and parity set `Γ` on
which `f` is not constant on all fibers, there exists an assignment `b : P.basis → Bool` such that
`f|_b` is non-constant and `δ(f|_b) / k(f|_b) ≤ 4 * k(f) * δ(f) / ℓ^2`, where
`ℓ = numSupportCosets f Γ`. -/
theorem ParityFiberBasis.exists_nonconstant_restrict_ratio_le {Γ : Finset (Finset ι)}
    (P : ParityFiberBasis Γ) (f : (ι → Bool) → Bool)
    (hnonconst : ∃ b : P.basis → Bool, ¬∃ v : Bool, ∀ z, P.restrict f b z = v) :
    ∃ b : P.basis → Bool,
      (¬∃ v : Bool, ∀ z, P.restrict f b z = v) ∧
      boolWeight (P.restrict f b) / boolSparsity (P.restrict f b) ≤
        4 * boolSparsity f * boolWeight f / (numSupportCosets f Γ : ℝ) ^ 2 := by
  classical
  set ℓ := numSupportCosets f Γ
  have hsp_f_pos : 0 < boolSparsity f := boolSparsity_pos f
  have hℓ_pos : 0 < ℓ := card_pos.2 ((card_pos.1 hsp_f_pos).image _)
  have hδ_pos : 0 < boolWeight f := by
    rcases (boolWeight_nonneg f).eq_or_lt with h0 | hp
    · exfalso
      have hf0 := boolWeight_eq_zero_iff.1 h0.symm
      obtain ⟨b, hb⟩ := hnonconst
      exact hb ⟨false, fun z ↦ by rw [P.restrict_eq]; exact hf0 _⟩
    · exact hp
  by_cases hℓ1 : ℓ = 1
  · -- Boundary case ℓ = 1: pick the given non-constant fiber b₀; its ratio ≤ 1 ≤ 4 k(f) δ(f).
    obtain ⟨b₀, hb₀⟩ := hnonconst
    refine ⟨b₀, hb₀, ?_⟩
    rw [hℓ1, Nat.cast_one, one_pow, div_one]
    have hsp1 : (1 : ℝ) ≤ boolSparsity (P.restrict f b₀) := by
      exact_mod_cast boolSparsity_pos (P.restrict f b₀)
    have hlhs : boolWeight (P.restrict f b₀) / boolSparsity (P.restrict f b₀) ≤ 1 :=
      (div_le_one (by positivity)).2 ((boolWeight_le_one _).trans hsp1)
    have hrhs : (2 : ℝ) ≤ 4 * boolSparsity f * boolWeight f := by
      by_cases hk1 : boolSparsity f = 1
      · obtain ⟨S, v, hv⟩ := boolSparsity_eq_one_iff.1 hk1
        have hSne : S ≠ ∅ := by
          intro rfl
          exact hb₀ ⟨v, fun z ↦ by simp [ParityFiberBasis.restrict_eq, hv]⟩
        have h0 : boolFourierCoeff f ∅ = 0 := by
          rw [funext hv, boolFourierCoeff_const_xor_parityOn, ite_eq_right hSne]
        rw [boolFourierCoeff_empty] at h0
        rw [hk1, Nat.cast_one]
        linarith
      · have hk2 : 1 < boolSparsity f := by have := boolSparsity_pos f; omega
        have := one_le_boolSparsity_mul_boolWeight hk2
        linarith
    linarith
  · have hℓ2 : 2 ≤ ℓ := by omega
    set R : ℝ := 4 * boolSparsity f * boolWeight f / (ℓ : ℝ) ^ 2
    let diff : (P.basis → Bool) → ℝ :=
      fun b ↦ boolWeight (P.restrict f b) - R * (boolNonemptySparsity (P.restrict f b) : ℝ)
    have hexp_nonpos : 𝔼 b : P.basis → Bool, diff b ≤ 0 := by
      dsimp [diff]
      rw [expect_sub_distrib, ← mul_expect, P.expect_boolWeight_restrict]
      have hlb := P.le_expect_boolNonemptySparsity_restrict f hℓ2
      have hR_pos : 0 < R := by dsimp [R]; positivity
      have hprod : boolWeight f = R * ((ℓ : ℝ) ^ 2 / (4 * boolSparsity f)) := by
        dsimp [R]
        have hℓne : (ℓ : ℝ) ^ 2 ≠ 0 := by positivity
        have hkne : (boolSparsity f : ℝ) ≠ 0 := by positivity
        field_simp
      have := hprod.le.trans (mul_le_mul_of_nonneg_left hlb hR_pos.le)
      linarith
    by_cases hneg : ∃ b : P.basis → Bool, diff b < 0
    · obtain ⟨b₀, hb₀⟩ := hneg
      dsimp [diff] at hb₀
      have hsp_pos : 0 < boolNonemptySparsity (P.restrict f b₀) := by
        by_contra h0
        have hz : boolNonemptySparsity (P.restrict f b₀) = 0 := by omega
        rw [hz, Nat.cast_zero, mul_zero, sub_zero] at hb₀
        linarith [boolWeight_nonneg (P.restrict f b₀)]
      have hnc : ¬∃ v : Bool, ∀ z, P.restrict f b₀ z = v := by
        rw [← boolNonemptySparsity_eq_zero_iff]
        omega
      refine ⟨b₀, hnc, ?_⟩
      have hle_sp : (boolNonemptySparsity (P.restrict f b₀) : ℝ) ≤
          boolSparsity (P.restrict f b₀) := by
        exact_mod_cast boolNonemptySparsity_le_boolSparsity _
      calc boolWeight (P.restrict f b₀) / boolSparsity (P.restrict f b₀)
          ≤ boolWeight (P.restrict f b₀) / boolNonemptySparsity (P.restrict f b₀) :=
            div_le_div_of_nonneg_left (boolWeight_nonneg _) (by positivity) hle_sp
        _ ≤ R := (div_le_iff₀ (by positivity)).2 (by linarith)
    · push Not at hneg
      have hall_zero : ∀ b : P.basis → Bool, diff b = 0 := by
        intro b
        by_contra hne
        have hpos : 0 < diff b := lt_of_le_of_ne (hneg b) (Ne.symm hne)
        have hexp_pos : 0 < 𝔼 b' : P.basis → Bool, diff b' := by
          rw [Fintype.expect_eq_sum_div_card]
          refine div_pos ?_ (by positivity)
          exact lt_of_lt_of_le hpos (single_le_sum (fun b' _ ↦ hneg b') (mem_univ b))
        linarith
      obtain ⟨b₀, hb₀⟩ := hnonconst
      have hsp_pos : 0 < boolNonemptySparsity (P.restrict f b₀) := by
        by_contra h0
        exact hb₀ (boolNonemptySparsity_eq_zero_iff.1 (by omega))
      have hz := hall_zero b₀
      dsimp [diff] at hz
      have hle_sp : (boolNonemptySparsity (P.restrict f b₀) : ℝ) ≤
          boolSparsity (P.restrict f b₀) := by
        exact_mod_cast boolNonemptySparsity_le_boolSparsity _
      refine ⟨b₀, hb₀, ?_⟩
      calc boolWeight (P.restrict f b₀) / boolSparsity (P.restrict f b₀)
          ≤ boolWeight (P.restrict f b₀) / boolNonemptySparsity (P.restrict f b₀) :=
            div_le_div_of_nonneg_left (boolWeight_nonneg _) (by positivity) hle_sp
        _ = R := (div_eq_iff (by positivity)).2 (by linarith)

/-- Single parity-query extension step of the weighted Sanyal algorithm: given `Γ`, a fiber basis
`P`, and any non-constant fiber `g = P.restrict f b` with `0 ∈ supportCosets f Γ ∨ 2 ≤ k(g)`,
extending `Γ` by a smallest parity set `Γ'` that makes `g` constant on some assignment yields:
1. `0 ∈ supportCosets f (Γ ∪ Γ')`,
2. `numSupportCosets f (Γ ∪ Γ') < numSupportCosets f Γ`, and
3. `|Γ'| / (ℓ - ℓ') ≤ 6 * √(δ(g) / k(g))` (and `|Γ'| ≤ 3 * √(δ(g) * k(g))`). -/
theorem ParityFiberBasis.exists_sanyal_step {Γ : Finset (Finset ι)}
    (P : ParityFiberBasis Γ) (f : (ι → Bool) → Bool) (b : P.basis → Bool)
    (hnc : ¬∃ v : Bool, ∀ z, P.restrict f b z = v)
    (hzero : (0 : (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) ∈ supportCosets f Γ ∨
      2 ≤ boolSparsity (P.restrict f b)) :
    ∃ Γ' : Finset (Finset ι),
      (0 : (ι → ZMod 2) ⧸ paritySpan ((Γ ∪ Γ' : Finset (Finset ι)) : Set (Finset ι))) ∈
        supportCosets f (Γ ∪ Γ') ∧
      numSupportCosets f (Γ ∪ Γ') < numSupportCosets f Γ ∧
      (#Γ' : ℝ) ≤ 3 * Real.sqrt (boolWeight (P.restrict f b) * boolSparsity (P.restrict f b)) ∧
      ((#Γ' : ℝ) / ((numSupportCosets f Γ : ℝ) - numSupportCosets f (Γ ∪ Γ')) ≤
        6 * Real.sqrt (boolWeight (P.restrict f b) / boolSparsity (P.restrict f b))) := by
  classical
  let g := P.restrict f b
  have hδg : 0 < boolWeight g := by
    rcases (boolWeight_nonneg g).eq_or_lt with h0 | hp
    · exact False.elim (hnc ⟨false, boolWeight_eq_zero_iff.1 h0.symm⟩)
    · exact hp
  obtain ⟨Δ, bΔ, hΔ_li, ⟨v, hv⟩, hΔ_card⟩ :=
    exists_constant_parity_subspace_le_three_mul_sqrt hδg
  let liftC : Finset P.FreeCoord → Finset ι := fun U ↦ U.map ⟨Subtype.val, Subtype.val_injective⟩
  let toAmbient : Finset P.FreeCoord → Finset ι :=
    fun U ↦ parityVecEquiv.symm (P.aut (parityVec (liftC U)))
  have hpv_toAmbient : ∀ U : Finset P.FreeCoord,
      parityVec (toAmbient U) = P.aut (parityVec (liftC U)) := fun U ↦ by
    change parityVecEquiv (toAmbient U) = _; simp [toAmbient]
  have htoAmbient_inj : Function.Injective toAmbient := fun U₁ U₂ h ↦ by
    have h1' := congr_arg parityVec h
    rw [hpv_toAmbient, hpv_toAmbient] at h1'
    have h1 := parityVec_injective (P.aut.injective h1')
    ext j
    have hj := Finset.ext_iff.1 h1 j.1
    simp only [liftC, mem_map, Function.Embedding.coeFn_mk, Subtype.val_injective.eq_iff,
      exists_eq_right] at hj
    exact hj
  let Γ' : Finset (Finset ι) := Δ.image toAmbient
  have hcard_Γ' : #Γ' = #Δ := card_image_of_injective _ htoAmbient_inj
  -- Key helper: P.aut.symm vanishes on P.FreeCoord for all vectors in paritySpan Γ.
  have hfree_zero_of_mem_Γ : ∀ w ∈ paritySpan (Γ : Set (Finset ι)),
      ∀ j : P.FreeCoord, P.aut.symm w j.1 = 0 := by
    intro w hw
    rw [← P.span_eq] at hw
    refine Submodule.span_induction ?_ (fun _ ↦ by simp)
      (fun a c _ _ ha hc j ↦ by simp [ha j, hc j])
      (fun c a _ ha j ↦ by simp [ha j]) hw
    rintro _ ⟨γ, hγ, rfl⟩ j
    rw [← P.aut_coord ⟨γ, hγ⟩, LinearEquiv.symm_apply_apply, parityVec_of_notMem]
    rw [mem_singleton]
    exact fun heq ↦ j.2 (heq ▸ mem_map_of_mem P.coordEmb (mem_univ (⟨γ, hγ⟩ : P.basis)))
  -- Key equivalence: toAmbient U₁ - toAmbient U₂ ∈ paritySpan (Γ ∪ Γ') ↔ U₁ - U₂ ∈ paritySpan Δ!
  have hcoset_iff : ∀ U₁ U₂ : Finset P.FreeCoord,
      (Submodule.Quotient.mk (parityVec (toAmbient U₁)) :
        (ι → ZMod 2) ⧸ paritySpan ((Γ ∪ Γ' : Finset (Finset ι)) : Set (Finset ι))) =
        Submodule.Quotient.mk (parityVec (toAmbient U₂)) ↔
      (Submodule.Quotient.mk (parityVec U₁) :
        (P.FreeCoord → ZMod 2) ⧸ paritySpan (Δ : Set (Finset P.FreeCoord))) =
        Submodule.Quotient.mk (parityVec U₂) := by
    intro U₁ U₂
    rw [Submodule.Quotient.eq, Submodule.Quotient.eq]
    have hdiff1 : parityVec (toAmbient U₁) - parityVec (toAmbient U₂) =
        P.aut (parityVec (liftC (symmDiff U₁ U₂))) := by
      have hsub_add : ∀ a c : ι → ZMod 2, a - c = a + c := fun a c ↦ by
        ext i; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, CharTwo.neg_eq]
      have hlift_sd : liftC (symmDiff U₁ U₂) = symmDiff (liftC U₁) (liftC U₂) :=
        by
        ext i; simp only [liftC, mem_symmDiff, mem_map, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨j, ⟨h1, h2⟩ | ⟨h1, h2⟩, rfl⟩
          · exact Or.inl ⟨⟨j, h1, rfl⟩, fun ⟨k, hk, heq⟩ ↦ h2 (Subtype.ext heq ▸ hk)⟩
          · exact Or.inr ⟨⟨j, h1, rfl⟩, fun ⟨k, hk, heq⟩ ↦ h2 (Subtype.ext heq ▸ hk)⟩
        · rintro (⟨⟨j, hj, rfl⟩, hn⟩ | ⟨⟨j, hj, rfl⟩, hn⟩)
          · exact ⟨j, Or.inl ⟨hj, fun h2 ↦ hn ⟨j, h2, rfl⟩⟩, rfl⟩
          · exact ⟨j, Or.inr ⟨hj, fun h1 ↦ hn ⟨j, h1, rfl⟩⟩, rfl⟩
      rw [hsub_add, hlift_sd, parityVec_symmDiff, map_add, hpv_toAmbient, hpv_toAmbient]
    have hdiff2 : parityVec U₁ - parityVec U₂ = parityVec (symmDiff U₁ U₂) := by
      rw [parityVec_symmDiff]
      ext j; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, CharTwo.neg_eq]
    rw [hdiff1, hdiff2]
    let resMap : (ι → ZMod 2) →ₗ[ZMod 2] (P.FreeCoord → ZMod 2) :=
      { toFun := fun w j ↦ P.aut.symm w j.1
        map_add' := fun a c ↦ by ext j; simp
        map_smul' := fun c a ↦ by ext j; simp }
    have hres_lift : ∀ W : Finset P.FreeCoord,
        resMap (P.aut (parityVec (liftC W))) = parityVec W := by
      intro W; ext j
      simp only [resMap, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply,
        parityVec_apply, liftC, mem_map, Function.Embedding.coeFn_mk, Subtype.val_injective.eq_iff,
        exists_eq_right]
    constructor
    · intro hmem
      have hres_span : ∀ w ∈ paritySpan ((Γ ∪ Γ' : Finset (Finset ι)) : Set (Finset ι)),
          resMap w ∈ paritySpan (Δ : Set (Finset P.FreeCoord)) := by
        intro w hw
        refine Submodule.span_induction ?_ (by simp)
          (fun a c _ _ ha hc ↦ by rw [map_add]; exact Submodule.add_mem _ ha hc)
          (fun c a _ ha ↦ by rw [map_smul]; exact Submodule.smul_mem _ c ha) hw
        rintro _ ⟨S, hS, rfl⟩
        rcases mem_union.1 hS with hSΓ | hSΓ'
        · have : resMap (parityVec S) = 0 := by
            ext j; exact hfree_zero_of_mem_Γ _ (mem_paritySpan_of_mem hSΓ) j
          rw [this]; exact Submodule.zero_mem _
        · obtain ⟨U, hU, rfl⟩ := mem_image.1 hSΓ'
          have : resMap (parityVec (toAmbient U)) = parityVec U := by
            rw [hpv_toAmbient]; exact hres_lift U
          rw [this]; exact mem_paritySpan_of_mem hU
      simpa [hres_lift] using hres_span _ hmem
    · intro hmem
      let embMap : (P.FreeCoord → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
        { toFun := fun v ↦ P.aut fun i ↦
            if h : i ∈ univ.map P.coordEmb then 0 else v ⟨i, h⟩
          map_add' := fun a c ↦ by
            rw [← map_add]; apply congr_arg P.aut; ext i
            simp only [Pi.add_apply]; split_ifs <;> simp
          map_smul' := fun c a ↦ by
            rw [← map_smul]; apply congr_arg P.aut; ext i
            simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp }
      have hemb_vec : ∀ W : Finset P.FreeCoord,
          embMap (parityVec W) = P.aut (parityVec (liftC W)) := by
        intro W; apply congr_arg P.aut; funext i
        split_ifs with hm
        · symm; apply parityVec_of_notMem
          simp only [liftC, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
          intro j _ heq; exact j.2 (heq ▸ hm)
        · have hiff : i ∈ liftC W ↔ (⟨i, hm⟩ : P.FreeCoord) ∈ W := by
            simp only [liftC, mem_map, Function.Embedding.coeFn_mk]
            exact ⟨fun ⟨j, hj, heq⟩ ↦ (show j = ⟨i, hm⟩ from Subtype.ext heq) ▸ hj,
              fun h ↦ ⟨⟨i, hm⟩, h, rfl⟩⟩
          by_cases hw : (⟨i, hm⟩ : P.FreeCoord) ∈ W
          · rw [parityVec_of_mem hw, parityVec_of_mem (hiff.2 hw)]
          · rw [parityVec_of_notMem hw, parityVec_of_notMem (mt hiff.1 hw)]
      rw [← hemb_vec]
      refine Submodule.span_induction ?_ (by simp)
        (fun a c _ _ ha hc ↦ by rw [map_add]; exact Submodule.add_mem _ ha hc)
        (fun c a _ ha ↦ by rw [map_smul]; exact Submodule.smul_mem _ c ha) hmem
      rintro _ ⟨U, hU, rfl⟩
      rw [hemb_vec]
      have : P.aut (parityVec (liftC U)) = parityVec (toAmbient U) := (hpv_toAmbient U).symm
      rw [this]
      exact mem_paritySpan_of_mem (mem_union_right Γ (mem_image_of_mem toAmbient hU))
  -- Every U ∈ boolSupport g gives a distinct coset q_U ∈ supportCosets f Γ!
  let qΓ : Finset P.FreeCoord → (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι)) :=
    fun U ↦ Submodule.Quotient.mk (parityVec (toAmbient U))
  have hqΓ_mem : ∀ U ∈ boolSupport g, qΓ U ∈ supportCosets f Γ := by
    intro U hU
    rw [mem_boolSupport] at hU
    rw [P.boolFourierCoeff_restrict] at hU
    obtain ⟨V, _, hVne⟩ := exists_ne_zero_of_sum_ne_zero hU
    have hfc_ne := left_ne_zero_of_mul hVne
    rw [boolFourierCoeff_fourierBasisChange] at hfc_ne
    let S := parityVecEquiv.symm (P.aut (parityVec (V.map P.coordEmb ∪ liftC U)))
    refine mem_supportCosets.2 ⟨S, mem_boolSupport.2 hfc_ne, ?_⟩
    rw [Submodule.Quotient.eq]
    have hdisj : Disjoint (V.map P.coordEmb) (liftC U) := by
      rw [disjoint_left]; intro i hiV hiU
      obtain ⟨γ, _, rfl⟩ := mem_map.1 hiV
      obtain ⟨j, _, hj⟩ := mem_map.1 hiU
      dsimp only [Function.Embedding.coeFn_mk] at hj
      exact j.2 (hj ▸ mem_map_of_mem P.coordEmb (mem_univ γ))
    have hdiff : parityVec S - parityVec (toAmbient U) =
        P.aut (parityVec (V.map P.coordEmb)) := by
      have h1 : parityVec S = P.aut (parityVec (V.map P.coordEmb)) +
          P.aut (parityVec (liftC U)) := by
        change parityVecEquiv S = _
        simp only [S, Equiv.apply_symm_apply, ← Disjoint.symmDiff_eq_sup hdisj,
          parityVec_symmDiff, map_add]
      rw [h1, hpv_toAmbient U, add_sub_cancel_right]
    rw [hdiff, ← P.span_eq, parityVec_map, map_sum]
    exact Submodule.sum_mem _ fun γ _ ↦ P.aut_coord γ ▸ mem_paritySpan_of_mem γ.2
  have hqΓ_inj : Function.Injective qΓ := by
    intro U₁ U₂ heq
    rw [Submodule.Quotient.eq] at heq
    have hdiff : parityVec (toAmbient U₁) - parityVec (toAmbient U₂) =
        P.aut (parityVec (liftC (symmDiff U₁ U₂))) := by
      have hlift_sd : liftC (symmDiff U₁ U₂) = symmDiff (liftC U₁) (liftC U₂) :=
        by
        ext i; simp only [liftC, mem_symmDiff, mem_map, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨j, ⟨h1, h2⟩ | ⟨h1, h2⟩, rfl⟩
          · exact Or.inl ⟨⟨j, h1, rfl⟩, fun ⟨k, hk, heq⟩ ↦ h2 (Subtype.ext heq ▸ hk)⟩
          · exact Or.inr ⟨⟨j, h1, rfl⟩, fun ⟨k, hk, heq⟩ ↦ h2 (Subtype.ext heq ▸ hk)⟩
        · rintro (⟨⟨j, hj, rfl⟩, hn⟩ | ⟨⟨j, hj, rfl⟩, hn⟩)
          · exact ⟨j, Or.inl ⟨hj, fun h2 ↦ hn ⟨j, h2, rfl⟩⟩, rfl⟩
          · exact ⟨j, Or.inr ⟨hj, fun h1 ↦ hn ⟨j, h1, rfl⟩⟩, rfl⟩
      rw [hlift_sd, parityVec_symmDiff, map_add, hpv_toAmbient, hpv_toAmbient]
      ext i; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, CharTwo.neg_eq]
    rw [hdiff] at heq
    have hz := hfree_zero_of_mem_Γ _ heq
    simp only [LinearEquiv.symm_apply_apply] at hz
    ext j
    have hj := hz j
    simp only [parityVec_apply, mem_symmDiff, liftC, mem_map, Function.Embedding.coeFn_mk,
      Subtype.val_injective.eq_iff, exists_eq_right] at hj
    split_ifs at hj with h
    · exact False.elim (one_ne_zero hj)
    · push Not at h; exact ⟨h.1, h.2⟩
  -- General drop inequality: for π : Q₁ → Q₂, #S - #(S.image π) ≥ #A - #(A.image π) when A ⊆ S!
  have hsub_union : paritySpan (Γ : Set (Finset ι)) ≤
      paritySpan ((Γ ∪ Γ' : Finset (Finset ι)) : Set (Finset ι)) :=
    paritySpan_mono (by simp)
  let π := Submodule.factor hsub_union
  have hcoset_img : supportCosets f (Γ ∪ Γ') = (supportCosets f Γ).image π := by
    ext q; simp only [mem_supportCosets, mem_image]
    exact ⟨fun ⟨S, hS, hq⟩ ↦ ⟨Submodule.Quotient.mk (parityVec S), ⟨S, hS, rfl⟩, hq⟩,
      fun ⟨_, ⟨S, hS, rfl⟩, hq⟩ ↦ ⟨S, hS, hq⟩⟩
  have hdrop_general : ∀ A : Finset ((ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))),
      A ⊆ supportCosets f Γ →
      #A - #(A.image π) ≤ numSupportCosets f Γ - numSupportCosets f (Γ ∪ Γ') := by
    intro A hA
    rw [← card_supportCosets, ← card_supportCosets, hcoset_img]
    have hunion : (supportCosets f Γ).image π = A.image π ∪ (supportCosets f Γ \ A).image π := by
      rw [← image_union, union_sdiff_of_subset hA]
    have hle : #((supportCosets f Γ).image π) ≤ #(A.image π) + #(supportCosets f Γ \ A) := by
      rw [hunion]
      exact (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
    have hsplit : #(supportCosets f Γ) = #A + #(supportCosets f Γ \ A) := by
      rw [card_sdiff_of_subset hA]; exact (Nat.add_sub_of_le (card_le_card hA)).symm
    have hAi : #(A.image π) ≤ #A := card_image_le
    omega
  -- On the restricted function g, (Δ, bΔ) is a constant fiber with Δ linearly independent!
  -- Therefore: (a) supportCosets g Δ contains 0! (b) if k(g) ≥ 2, EVERY coset of boolSupport g mod
  -- Δ
  -- has cardinality ≥ 2!!
  let PΔ : ParityFiberBasis Δ := by
    have h2 := exists_linearEquiv_extending_finset hΔ_li
    let BΔ := Classical.choose h2
    have hBΔ := Classical.choose_spec h2
    let embΔ := Classical.choose hBΔ
    have hembΔ := Classical.choose_spec hBΔ
    exact ⟨Δ, Subset.rfl, rfl, hΔ_li, BΔ, embΔ, hembΔ.1⟩
  let bΔ_sub : PΔ.basis → Bool := fun u ↦ bΔ u.1
  have hg_const : ∀ z : PΔ.FreeCoord → Bool, PΔ.restrict g bΔ_sub z = v := by
    intro z
    rw [PΔ.restrict_eq]
    exact hv (PΔ.fiberPoint bΔ_sub z) fun U hU ↦ PΔ.parityOn_fiberPoint bΔ_sub z ⟨U, hU⟩
  -- Key property of g's cosets modulo Δ:
  -- 1) ∃ U₀ ∈ boolSupport g, parityVec U₀ ∈ paritySpan Δ (since g|_{bΔ} ≡ v has ĝ|_{bΔ}(∅) = ±1 ≠
  -- 0!).
  have hzero_g : (0 : (P.FreeCoord → ZMod 2) ⧸ paritySpan (Δ : Set (Finset P.FreeCoord))) ∈
      supportCosets g Δ := by
    have hfc0 : boolFourierCoeff (PΔ.restrict g bΔ_sub) ∅ = signVal v := by
      rw [funext hg_const, boolFourierCoeff_const, ite_eq_left rfl]
    have hfc0_ne : boolFourierCoeff (PΔ.restrict g bΔ_sub) ∅ ≠ 0 := by
      rw [hfc0]; cases v <;> simp [signVal]
    rw [PΔ.boolFourierCoeff_restrict] at hfc0_ne
    simp only [map_empty, union_empty] at hfc0_ne
    obtain ⟨V, _, hVne⟩ := exists_ne_zero_of_sum_ne_zero hfc0_ne
    have hl := left_ne_zero_of_mul hVne
    rw [boolFourierCoeff_fourierBasisChange] at hl
    let U₀ := parityVecEquiv.symm (PΔ.aut (parityVec (V.map PΔ.coordEmb)))
    have hU₀_mem : U₀ ∈ boolSupport g := by
      apply mem_boolSupport.2
      simpa [U₀] using hl
    refine mem_supportCosets.2 ⟨U₀, hU₀_mem, ?_⟩
    rw [Submodule.Quotient.mk_eq_zero]
    change parityVecEquiv U₀ ∈ _
    simp only [U₀, Equiv.apply_symm_apply]
    rw [parityVec_map, map_sum, ← PΔ.span_eq]
    exact Submodule.sum_mem _ fun u _ ↦ PΔ.aut_coord u ▸ mem_paritySpan_of_mem u.2
  have hzero_new : (0 : (ι → ZMod 2) ⧸ paritySpan ((Γ ∪ Γ' : Finset (Finset ι)) : Set (Finset ι))) ∈
      supportCosets f (Γ ∪ Γ') := by
    obtain ⟨U₀, hU₀_mem, hU₀_zero⟩ := mem_supportCosets.1 hzero_g
    have hq_mem : π (qΓ U₀) ∈ supportCosets f (Γ ∪ Γ') := by
      rw [hcoset_img]; exact mem_image_of_mem π (hqΓ_mem U₀ hU₀_mem)
    have hq_zero : π (qΓ U₀) = 0 := by
      have hpv0 : parityVec (toAmbient ∅) = 0 := by
        rw [hpv_toAmbient]; simp only [liftC, map_empty, parityVec_empty, map_zero]
      have hiff := (hcoset_iff U₀ ∅).2
        (by rw [hU₀_zero, parityVec_empty, Submodule.Quotient.mk_zero])
      rw [hpv0, Submodule.Quotient.mk_zero] at hiff
      exact hiff
    rwa [hq_zero] at hq_mem
  -- 2) Bound the coset drop ℓ - ℓ' ≥ k(g) / 2!
  have hdrop_kg : boolSparsity g ≤
      2 * (numSupportCosets f Γ - numSupportCosets f (Γ ∪ Γ')) ∧
      numSupportCosets f (Γ ∪ Γ') < numSupportCosets f Γ := by
    by_cases hkg1 : boolSparsity g = 1
    · -- k(g) = 1: since g is non-constant, boolSupport g = {U₀} with U₀ ≠ ∅, and U₀ ∈ span(Δ).
      -- By hzero, 0 ∈ supportCosets f Γ, while qΓ U₀ ≠ 0 (since U₀ ≠ ∅), and π(qΓ U₀) = 0 = π(0)!
      have hzΓ : (0 : (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) ∈ supportCosets f Γ :=
        hzero.resolve_right (by change ¬2 ≤ boolSparsity g; omega)
      obtain ⟨U₀, hU₀_mem, hU₀_zero⟩ := mem_supportCosets.1 hzero_g
      have hU₀_ne : U₀ ≠ ∅ := by
        intro rfl
        have hsupp : boolSupport g = {∅} :=
          (eq_of_subset_of_card_le (singleton_subset_iff.2 hU₀_mem)
            (by rw [card_singleton]; change boolSparsity g ≤ 1; omega)).symm
        have hbn : boolNonemptySparsity g = 0 := by
          rw [← card_erase_empty_boolSupport, hsupp]; simp
        exact hnc (boolNonemptySparsity_eq_zero_iff.1 hbn)
      have hpv0 : parityVec (toAmbient ∅) = 0 := by
        rw [hpv_toAmbient]; simp only [liftC, map_empty, parityVec_empty, map_zero]
      have hq_ne0 : qΓ U₀ ≠ 0 := fun h0 ↦ hU₀_ne (hqΓ_inj (by
        dsimp only [qΓ]; rw [hpv0, Submodule.Quotient.mk_zero]; exact h0))
      have hπ_eq : π (qΓ U₀) = π 0 := by
        have hiff := (hcoset_iff U₀ ∅).2
          (by rw [hU₀_zero, parityVec_empty, Submodule.Quotient.mk_zero])
        rw [hpv0, Submodule.Quotient.mk_zero] at hiff
        simpa [π, qΓ] using hiff
      let A : Finset ((ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) := {0, qΓ U₀}
      have hA_sub : A ⊆ supportCosets f Γ := by
        intro q hq
        rcases mem_insert.1 hq with rfl | hq'
        · exact hzΓ
        · rw [mem_singleton.1 hq']; exact hqΓ_mem U₀ hU₀_mem
      have hA_card : #A = 2 := card_pair hq_ne0.symm
      have hAi_card : #(A.image π) = 1 := by
        have : A.image π = {π 0} := by
          ext y; simp [A, hπ_eq]
        rw [this, card_singleton]
      have hd := hdrop_general A hA_sub
      omega
    · -- k(g) ≥ 2: EVERY coset q ∈ supportCosets g Δ has cardinality ≥ 2!
      have hkg2 : 2 ≤ boolSparsity g := by have := boolSparsity_pos g; omega
      have hpair : ∀ q ∈ supportCosets g Δ,
          2 ≤ #{U ∈ boolSupport g | (Submodule.Quotient.mk (parityVec U) :
            (P.FreeCoord → ZMod 2) ⧸ paritySpan (Δ : Set (Finset P.FreeCoord))) = q} := by
        intro q hq
        by_contra hlt2
        obtain ⟨U₁, hU₁s, rfl⟩ := mem_supportCosets.1 hq
        set cls := {U ∈ boolSupport g | (Submodule.Quotient.mk (parityVec U) :
          (P.FreeCoord → ZMod 2) ⧸ paritySpan (Δ : Set (Finset P.FreeCoord))) =
            Submodule.Quotient.mk (parityVec U₁)}
        have hU₁_cls : U₁ ∈ cls := mem_filter.2 ⟨hU₁s, rfl⟩
        have hcls_eq : cls = {U₁} :=
          (eq_of_subset_of_card_le (singleton_subset_iff.2 hU₁_cls) (by
            rw [card_singleton]; have : 0 < #cls := card_pos.2 ⟨U₁, hU₁_cls⟩; omega)).symm
        -- Decompose PΔ.aut.symm (parityVec U₁) into V₁ on PΔ.basis and W₁ on PΔ.FreeCoord.
        let T₁ := parityVecEquiv.symm (PΔ.aut.symm (parityVec U₁))
        let V₁ : Finset PΔ.basis := univ.filter fun u ↦ PΔ.coordEmb u ∈ T₁
        let W₁ : Finset PΔ.FreeCoord := univ.filter fun j ↦ j.1 ∈ T₁
        let liftΔ : Finset PΔ.FreeCoord → Finset P.FreeCoord :=
          fun W ↦ W.map ⟨Subtype.val, Subtype.val_injective⟩
        have hT₁_eq : V₁.map PΔ.coordEmb ∪ liftΔ W₁ = T₁ := by
          ext j
          simp only [V₁, W₁, mem_union, mem_map, mem_filter, mem_univ, true_and, liftΔ,
            Function.Embedding.coeFn_mk]
          exact ⟨by rintro (⟨u, hu, rfl⟩ | ⟨k, hk, rfl⟩) <;> assumption, fun hj ↦
            if hm : j ∈ univ.map PΔ.coordEmb then
              let ⟨u, _, hu⟩ := mem_map.1 hm; Or.inl ⟨u, hu ▸ hj, hu⟩
            else Or.inr ⟨⟨j, hm⟩, hj, rfl⟩⟩
        have hU₁_eq : parityVecEquiv.symm (PΔ.aut (parityVec (V₁.map PΔ.coordEmb ∪ liftΔ W₁))) =
            U₁ := by
          rw [hT₁_eq]; change parityVecEquiv.symm (PΔ.aut (parityVecEquiv T₁)) = U₁
          simp only [T₁, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          exact parityVecEquiv.symm_apply_apply U₁
        -- In boolFourierCoeff (PΔ.restrict g bΔ_sub) W₁, ONLY V = V₁ is nonzero!
        have hfc_W₁ : boolFourierCoeff (PΔ.restrict g bΔ_sub) W₁ =
            boolFourierCoeff g U₁ * chi ℝ V₁ bΔ_sub := by
          rw [PΔ.boolFourierCoeff_restrict]
          refine (sum_eq_single V₁ (fun V _ hVne ↦ ?_) (by simp)).trans ?_
          · rw [boolFourierCoeff_fourierBasisChange]
            set U' := parityVecEquiv.symm (PΔ.aut (parityVec (V.map PΔ.coordEmb ∪ liftΔ W₁)))
            suffices h0 : boolFourierCoeff g U' = 0 by rw [h0, zero_mul]
            by_contra hne0
            have hU'_cls : U' ∈ cls := by
              refine mem_filter.2 ⟨mem_boolSupport.2 hne0, ?_⟩
              rw [Submodule.Quotient.eq]
              have hdiff : parityVec U' - parityVec U₁ =
                  PΔ.aut (parityVec (symmDiff (V.map PΔ.coordEmb) (V₁.map PΔ.coordEmb))) := by
                have hd1 : Disjoint (V.map PΔ.coordEmb) (liftΔ W₁) := by
                  rw [disjoint_left]; intro j h1 h2
                  obtain ⟨u, _, rfl⟩ := mem_map.1 h1; obtain ⟨k, _, hk⟩ := mem_map.1 h2
                  dsimp only [Function.Embedding.coeFn_mk] at hk
                  exact k.2 (hk ▸ mem_map_of_mem PΔ.coordEmb (mem_univ u))
                have hd2 : Disjoint (V₁.map PΔ.coordEmb) (liftΔ W₁) := by
                  rw [disjoint_left]; intro j h1 h2
                  obtain ⟨u, _, rfl⟩ := mem_map.1 h1; obtain ⟨k, _, hk⟩ := mem_map.1 h2
                  dsimp only [Function.Embedding.coeFn_mk] at hk
                  exact k.2 (hk ▸ mem_map_of_mem PΔ.coordEmb (mem_univ u))
                have hU'v : parityVec U' =
                    PΔ.aut (parityVec (V.map PΔ.coordEmb)) + PΔ.aut (parityVec (liftΔ W₁)) := by
                  have h1 : parityVec U' = PΔ.aut (parityVec (V.map PΔ.coordEmb ∪ liftΔ W₁)) := by
                    change parityVecEquiv U' = _; simp [U']
                  rw [h1, ← Disjoint.symmDiff_eq_sup hd1, parityVec_symmDiff, map_add]
                have hU₁v : parityVec U₁ =
                    PΔ.aut (parityVec (V₁.map PΔ.coordEmb)) + PΔ.aut (parityVec (liftΔ W₁)) := by
                  have h1 : parityVec U₁ = PΔ.aut (parityVec (V₁.map PΔ.coordEmb ∪ liftΔ W₁)) := by
                    rw [← hU₁_eq]; change parityVecEquiv _ = _; simp
                  rw [h1, ← Disjoint.symmDiff_eq_sup hd2, parityVec_symmDiff, map_add]
                rw [hU'v, hU₁v, parityVec_symmDiff, map_add]
                ext j; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, CharTwo.neg_eq]
                have hc : ∀ x y z : ZMod 2, (x + z) + (y + z) = x + y := by decide
                exact hc _ _ _
              rw [hdiff, ← PΔ.span_eq]
              let SD := symmDiff V V₁
              have hmap_sd : symmDiff (V.map PΔ.coordEmb) (V₁.map PΔ.coordEmb) =
                  SD.map PΔ.coordEmb := by
                ext j; simp only [SD, mem_symmDiff, mem_map]
                constructor
                · rintro (⟨⟨u, hu, rfl⟩, hn⟩ | ⟨⟨u, hu, rfl⟩, hn⟩)
                  · exact ⟨u, Or.inl ⟨hu, fun h2 ↦ hn ⟨u, h2, rfl⟩⟩, rfl⟩
                  · exact ⟨u, Or.inr ⟨hu, fun h1 ↦ hn ⟨u, h1, rfl⟩⟩, rfl⟩
                · rintro ⟨u, hu, rfl⟩
                  simpa [PΔ.coordEmb.injective.eq_iff] using hu
              rw [hmap_sd, parityVec_map, map_sum]
              exact Submodule.sum_mem _ fun u _ ↦ PΔ.aut_coord u ▸ mem_paritySpan_of_mem u.2
            have hU'eq : U' = U₁ := mem_singleton.1 (hcls_eq ▸ hU'_cls)
            rw [← hU₁_eq] at hU'eq
            have hset' := congr_arg parityVecEquiv hU'eq
            simp only [U', Equiv.apply_symm_apply] at hset'
            have hset := parityVec_injective (PΔ.aut.injective hset')
            apply hVne
            ext u
            have hu := Finset.ext_iff.1 hset (PΔ.coordEmb u)
            have hnl : PΔ.coordEmb u ∉ liftΔ W₁ := by
              simp only [liftΔ, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
              intro k _ hk; exact k.2 (hk ▸ mem_map_of_mem PΔ.coordEmb (mem_univ u))
            simpa [hnl] using hu
          · rw [boolFourierCoeff_fourierBasisChange, hU₁_eq]
        -- Since PΔ.restrict g bΔ_sub ≡ v is constant:
        have hconst_fn : PΔ.restrict g bΔ_sub = fun _ ↦ v := funext hg_const
        by_cases hW₁ : W₁ = ∅
        · rw [hconst_fn, hW₁] at hfc_W₁
          have habs_lhs : |boolFourierCoeff (fun _ : PΔ.FreeCoord → Bool ↦ v) ∅| = 1 := by
            rw [boolFourierCoeff_const, ite_eq_left rfl, abs_signVal]
          have habs_rhs : |boolFourierCoeff g U₁ * chi ℝ V₁ bΔ_sub| = |boolFourierCoeff g U₁| := by
            rw [abs_mul, abs_chi, mul_one]
          have hsq1 : boolFourierCoeff g U₁ ^ 2 = 1 := by
            rw [← sq_abs (boolFourierCoeff g U₁), ← habs_rhs, ← hfc_W₁, habs_lhs, one_pow]
          -- By Parseval, all other U ≠ U₁ have ĝ(U) = 0, contradicting k(g) ≥ 2!
          obtain ⟨U₂, hU₂⟩ := card_pos.1 (show 0 < #((boolSupport g).erase U₁) by
            rw [card_erase_of_mem hU₁s]; change 0 < boolSparsity g - 1; omega)
          have hU₂_ne : U₂ ≠ U₁ := (mem_erase.1 hU₂).1
          have hU₂_pos : 0 < boolFourierCoeff g U₂ ^ 2 :=
            sq_pos_of_ne_zero (mem_boolSupport.1 (mem_erase.1 hU₂).2)
          have hle1 : boolFourierCoeff g U₁ ^ 2 + boolFourierCoeff g U₂ ^ 2 ≤ 1 := by
            rw [← sum_pair (f := fun U ↦ boolFourierCoeff g U ^ 2) hU₂_ne.symm,
              ← sum_boolFourierCoeff_sq g]
            exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
          linarith
        · rw [hconst_fn] at hfc_W₁
          have h0 : boolFourierCoeff (fun _ : PΔ.FreeCoord → Bool ↦ v) W₁ = 0 := by
            rw [boolFourierCoeff_const, ite_eq_right hW₁]
          rw [h0] at hfc_W₁
          have habs := congr_arg abs hfc_W₁.symm
          rw [abs_mul, abs_chi, mul_one, abs_zero] at habs
          exact mem_boolSupport.1 hU₁s (abs_eq_zero.1 habs)
      have hnum_g : 2 * numSupportCosets g Δ ≤ boolSparsity g := by
        calc 2 * numSupportCosets g Δ = ∑ _ ∈ supportCosets g Δ, 2 := by
              rw [← card_supportCosets]; simp [mul_comm]
          _ ≤ ∑ q ∈ supportCosets g Δ,
              #{U ∈ boolSupport g | (Submodule.Quotient.mk (parityVec U) :
                (P.FreeCoord → ZMod 2) ⧸ paritySpan (Δ : Set (Finset P.FreeCoord))) = q} :=
              sum_le_sum hpair
          _ = boolSparsity g := sum_card_supportCoset_eq_boolSparsity g Δ
      let A := (boolSupport g).image qΓ
      have hA_sub : A ⊆ supportCosets f Γ := by
        intro q hq
        obtain ⟨U, hU, rfl⟩ := mem_image.1 hq
        exact hqΓ_mem U hU
      have hA_card : #A = boolSparsity g := card_image_of_injective _ hqΓ_inj
      have hAi_card : #(A.image π) = numSupportCosets g Δ := by
        rw [image_image, ← card_supportCosets]
        refine card_bij
          (fun q hq ↦ by
            let U := Classical.choose (mem_image.1 hq)
            exact Submodule.Quotient.mk (parityVec U))
          (fun q hq ↦ by
            have hspec := Classical.choose_spec (mem_image.1 hq)
            exact mem_supportCosets.2 ⟨_, hspec.1, rfl⟩)
          (fun q₁ h₁ q₂ h₂ heq ↦ by
            have hs₁ := Classical.choose_spec (mem_image.1 h₁)
            have hs₂ := Classical.choose_spec (mem_image.1 h₂)
            rw [← hs₁.2, ← hs₂.2]
            exact (hcoset_iff _ _).2 heq)
          fun r hr ↦ by
            obtain ⟨U, hU, rfl⟩ := mem_image.1 hr
            have hmem : (π ∘ qΓ) U ∈ (boolSupport g).image (π ∘ qΓ) := mem_image_of_mem _ hU
            refine ⟨(π ∘ qΓ) U, hmem, ?_⟩
            have hspec := Classical.choose_spec (mem_image.1 hmem)
            exact (hcoset_iff _ _).1 hspec.2
      have hd := hdrop_general A hA_sub
      rw [hA_card, hAi_card] at hd
      omega
  refine ⟨Γ', hzero_new, hdrop_kg.2, hcard_Γ' ▸ hΔ_card, ?_⟩
  have hdiff_pos : (0 : ℝ) < (numSupportCosets f Γ : ℝ) - numSupportCosets f (Γ ∪ Γ') := by
    have : (numSupportCosets f (Γ ∪ Γ') : ℝ) < numSupportCosets f Γ := by
      exact_mod_cast hdrop_kg.2
    linarith
  have hkg_half : (boolSparsity g : ℝ) / 2 ≤
      (numSupportCosets f Γ : ℝ) - numSupportCosets f (Γ ∪ Γ') := by
    have h1 : (boolSparsity g : ℝ) ≤
        2 * ((numSupportCosets f Γ - numSupportCosets f (Γ ∪ Γ') : ℕ) : ℝ) := by
      exact_mod_cast hdrop_kg.1
    rw [Nat.cast_sub hdrop_kg.2.le] at h1
    linarith
  have hkg_pos : (0 : ℝ) < boolSparsity g := Nat.cast_pos.2 (boolSparsity_pos g)
  calc (#Γ' : ℝ) / ((numSupportCosets f Γ : ℝ) - numSupportCosets f (Γ ∪ Γ'))
      ≤ (3 * Real.sqrt (boolWeight g * boolSparsity g)) / ((boolSparsity g : ℝ) / 2) := by
        calc (#Γ' : ℝ) / ((numSupportCosets f Γ : ℝ) - numSupportCosets f (Γ ∪ Γ'))
            ≤ (3 * Real.sqrt (boolWeight g * boolSparsity g)) /
                ((numSupportCosets f Γ : ℝ) - numSupportCosets f (Γ ∪ Γ')) :=
              div_le_div_of_nonneg_right (hcard_Γ' ▸ hΔ_card) hdiff_pos.le
          _ ≤ (3 * Real.sqrt (boolWeight g * boolSparsity g)) / ((boolSparsity g : ℝ) / 2) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hkg_half
    _ = 6 * Real.sqrt (boolWeight g / boolSparsity g) := by
        rw [Real.sqrt_mul hδg.le, Real.sqrt_div hδg.le]
        set s := Real.sqrt (boolSparsity g)
        have hs : s ≠ 0 := (Real.sqrt_pos.2 hkg_pos).ne'
        have hsq : (boolSparsity g : ℝ) = s * s := (Real.mul_self_sqrt hkg_pos.le).symm
        rw [hsq]; field_simp; ring

/-- Discrete harmonic-sum inequality: `(a - b) / a ≤ ∑ j ∈ Ioc b a, 1 / j` for `0 < b ≤ a`. -/
private theorem sub_div_le_harmonic_Ioc {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    ((a : ℝ) - b) / a ≤ ∑ j ∈ Ioc b a, (1 : ℝ) / j := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le hb hba)
  calc ((a : ℝ) - b) / a = ((a - b : ℕ) : ℝ) * ((1 : ℝ) / a) := by
        rw [Nat.cast_sub hba]; ring
    _ = ∑ _ ∈ Ioc b a, (1 : ℝ) / a := by simp
    _ ≤ ∑ j ∈ Ioc b a, (1 : ℝ) / j := by
        refine sum_le_sum fun j hj ↦ ?_
        have hj_pos : (0 : ℝ) < j := by
          have := (mem_Ioc.1 hj).1; exact_mod_cast (by omega : 0 < j)
        have hj_le : (j : ℝ) ≤ a := by exact_mod_cast (mem_Ioc.1 hj).2
        exact one_div_le_one_div_of_le hj_pos hj_le

/-- Harmonic bound `∑ j ∈ Ioc 1 k, 1 / j ≤ ln k` for `k ≥ 1`. -/
private theorem harmonic_Ioc_one_le_log : ∀ k : ℕ, 1 ≤ k →
    ∑ j ∈ Ioc 1 k, (1 : ℝ) / j ≤ Real.log k := by
  intro k hk
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0; simp
    have hm1 : 1 ≤ m := by omega
    have hIoc : Ioc 1 (m + 1) = insert (m + 1) (Ioc 1 m) := by
      ext j; simp only [mem_Ioc, mem_insert]; omega
    rw [hIoc, sum_insert (by simp)]
    have hstep : (1 : ℝ) / (m + 1) ≤ Real.log (m + 1 : ℕ) - Real.log m := by
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hm1_pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have h := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
      rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at h
      have hsub : 1 - (m : ℝ) / ((m : ℝ) + 1) = (1 : ℝ) / ((m : ℝ) + 1) := by
        field_simp; ring
      push_cast at h ⊢
      linarith
    have hih := ih hm1
    push_cast at hstep ⊢
    linarith

/-- Iterative existence of a small parity set making `f` constant on all fibers: for every `Γ`
satisfying `0 ∈ supportCosets f Γ ∨ Γ = ∅` (with `k(f) ≥ 2`), there exists `Γ_end ⊇ Γ` making `f`
constant on all fibers with
`#(Γ_end \ Γ) ≤ 12 * √(δ(f) * k(f)) * ∑ j ∈ Ioc 1 (numSupportCosets f Γ), 1 / j`. -/
theorem exists_parity_determining_set_from {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) :
    ∀ (ℓ : ℕ) (Γ : Finset (Finset ι)),
      numSupportCosets f Γ = ℓ →
      ((0 : (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) ∈ supportCosets f Γ ∨ Γ = ∅) →
      ∃ Γ_end : Finset (Finset ι),
        Γ ⊆ Γ_end ∧
        (∀ b : Finset ι → Bool, IsConstantOnParityFiber f Γ_end b) ∧
        ((#(Γ_end \ Γ) : ℝ) ≤
          12 * Real.sqrt (boolWeight f * boolSparsity f) *
            ∑ j ∈ Ioc 1 ℓ, (1 : ℝ) / j) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | ind ℓ ih =>
    classical
    intro Γ hℓ hz
    let P := mkParityFiberBasis Γ
    by_cases hall : ∀ b : P.basis → Bool, ∃ v : Bool, ∀ z, P.restrict f b z = v
    · -- Every consistent fiber is constant; inconsistent fibers are vacuously constant.
      refine ⟨Γ, Subset.rfl, fun b ↦ ?_, ?_⟩
      · by_cases hne : ∃ x : ι → Bool, ∀ γ ∈ Γ, parityOn γ x = b γ
        · obtain ⟨x₀, hx₀⟩ := hne
          let b₀ : P.basis → Bool := fun γ ↦ b γ.1
          obtain ⟨v, hv⟩ := (P.isConst_restrict_iff f b₀).1 (hall b₀)
          refine ⟨v, fun x hx ↦ hv x fun γ hγ ↦ ?_⟩
          have hx₀_mem : ∀ γ' ∈ Γ, parityOn γ' x₀ = P.extAssign b₀ γ' :=
            (P.mem_fiber_iff b₀ x₀).2
              (P.exists_fiberPoint b₀ fun γ' ↦ hx₀ γ'.1 (P.basis_subset γ'.2))
          rw [hx γ hγ, ← hx₀ γ hγ, hx₀_mem γ hγ]
        · push Not at hne
          exact ⟨false, fun x hx ↦ by
            obtain ⟨γ, hγ, hne'⟩ := hne x
            exact False.elim (hne' (hx γ hγ))⟩
      · rw [sdiff_self, bot_eq_empty, card_empty, Nat.cast_zero]
        exact mul_nonneg (by have := boolWeight_nonneg f; positivity)
          (sum_nonneg fun _ _ ↦ by positivity)
    · obtain ⟨bstar, hb_nc, hb_ratio⟩ :=
        P.exists_nonconstant_restrict_ratio_le f (not_forall.1 hall)
      have hzero_step :
          (0 : (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) ∈ supportCosets f Γ ∨
            2 ≤ boolSparsity (P.restrict f bstar) := by
        rcases hz with h0 | rfl
        · exact Or.inl h0
        · right
          -- When Γ = ∅, P.basis = ∅, so P.restrict f bstar has sparsity = boolSparsity f ≥ 2!
          have hbasis_empty : P.basis = ∅ := by
            have := P.basis_subset; simpa using this
          have hsp_eq : boolSparsity (P.restrict f bstar) = boolSparsity f := by
            let eCoord : P.FreeCoord ≃ ι :=
              { toFun := Subtype.val
                invFun := fun i ↦ ⟨i, by simp [hbasis_empty]⟩
                left_inv := fun ⟨_, _⟩ ↦ rfl
                right_inv := fun _ ↦ rfl }
            have hfc : ∀ U : Finset P.FreeCoord,
                boolFourierCoeff (P.restrict f bstar) U =
                  boolFourierCoeff (fourierBasisChange P.aut f) (U.map eCoord.toEmbedding) := by
              intro U
              rw [P.boolFourierCoeff_restrict]
              have huniv : (univ : Finset (Finset P.basis)) = {∅} := by
                ext V
                simp only [mem_univ, mem_singleton, true_iff]
                apply eq_empty_of_forall_notMem
                intro γ _
                have := γ.2
                simp [hbasis_empty] at this
              rw [huniv, sum_singleton, map_empty, empty_union, chi_empty, mul_one]; rfl
            rw [← boolSparsity_fourierBasisChange P.aut f]
            refine card_bij (fun U _ ↦ U.map eCoord.toEmbedding)
              (fun U hU ↦ mem_boolSupport.2 (by rw [← hfc U]; exact mem_boolSupport.1 hU))
              (fun _ _ _ _ h ↦ Finset.map_injective eCoord.toEmbedding h)
              fun S hS ↦ ⟨S.map eCoord.symm.toEmbedding, mem_boolSupport.2 (by
                rw [hfc]
                have hmap : (S.map eCoord.symm.toEmbedding).map eCoord.toEmbedding = S := by
                  ext i; simp [eCoord]
                rw [hmap]; exact mem_boolSupport.1 hS), by ext i; simp [eCoord]⟩
          rw [hsp_eq]
          omega
      obtain ⟨Γ', hzero_new, hℓ_lt, _, hq_ratio⟩ := P.exists_sanyal_step f bstar hb_nc hzero_step
      set ℓ' := numSupportCosets f (Γ ∪ Γ')
      have hℓ'_pos : 0 < ℓ' := card_pos.2 ⟨0, hzero_new⟩
      have hℓ_pos : (0 : ℝ) < ℓ := by
        rw [← hℓ]; exact_mod_cast (lt_of_lt_of_le hℓ'_pos hℓ_lt.le)
      have hstep_bound : (#Γ' : ℝ) ≤
          12 * Real.sqrt (boolWeight f * boolSparsity f) * (((ℓ : ℝ) - ℓ') / ℓ) := by
        have hsqrt_ratio :
            Real.sqrt (boolWeight (P.restrict f bstar) / boolSparsity (P.restrict f bstar)) ≤
              2 * Real.sqrt (boolWeight f * boolSparsity f) / ℓ := by
          calc Real.sqrt (boolWeight (P.restrict f bstar) / boolSparsity (P.restrict f bstar))
              ≤ Real.sqrt (4 * boolSparsity f * boolWeight f / (numSupportCosets f Γ : ℝ) ^ 2) :=
                Real.sqrt_le_sqrt hb_ratio
            _ = 2 * Real.sqrt (boolWeight f * boolSparsity f) / ℓ := by
                rw [hℓ, Real.sqrt_div (by have := boolWeight_nonneg f; positivity),
                  Real.sqrt_sq hℓ_pos.le,
                  show 4 * (boolSparsity f : ℝ) * boolWeight f =
                    4 * (boolWeight f * boolSparsity f) by ring,
                  Real.sqrt_mul (by norm_num),
                  show Real.sqrt 4 = 2 by
                    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        have hdiff_pos : (0 : ℝ) < (ℓ : ℝ) - ℓ' := by
          have : (ℓ' : ℝ) < ℓ := by rw [← hℓ]; exact_mod_cast hℓ_lt
          linarith
        have h1 : (#Γ' : ℝ) / ((ℓ : ℝ) - ℓ') ≤
            12 * Real.sqrt (boolWeight f * boolSparsity f) / ℓ := by
          rw [hℓ] at hq_ratio
          refine hq_ratio.trans ?_
          calc 6 * Real.sqrt (boolWeight (P.restrict f bstar) / boolSparsity (P.restrict f bstar))
              ≤ 6 * (2 * Real.sqrt (boolWeight f * boolSparsity f) / ℓ) :=
                mul_le_mul_of_nonneg_left hsqrt_ratio (by norm_num)
            _ = 12 * Real.sqrt (boolWeight f * boolSparsity f) / ℓ := by ring
        have h2 := (div_le_iff₀ hdiff_pos).1 h1
        calc (#Γ' : ℝ) ≤ (12 * Real.sqrt (boolWeight f * boolSparsity f) / ℓ) * ((ℓ : ℝ) - ℓ') := h2
          _ = 12 * Real.sqrt (boolWeight f * boolSparsity f) * (((ℓ : ℝ) - ℓ') / ℓ) := by ring
      obtain ⟨Γ_end, hsub_end, hconst_end, hcard_end⟩ :=
        ih ℓ' (hℓ ▸ hℓ_lt) (Γ ∪ Γ') rfl (Or.inl hzero_new)
      refine ⟨Γ_end, subset_union_left.trans hsub_end, hconst_end, ?_⟩
      have hsdiff_card : (#(Γ_end \ Γ) : ℝ) ≤ (#Γ' : ℝ) + (#(Γ_end \ (Γ ∪ Γ')) : ℝ) := by
        have hsub_sd : Γ_end \ Γ ⊆ Γ' ∪ (Γ_end \ (Γ ∪ Γ')) := by
          intro γ hγ
          obtain ⟨h1, h2⟩ := mem_sdiff.1 hγ
          by_cases h3 : γ ∈ Γ'
          · exact mem_union_left _ h3
          · exact mem_union_right _ (mem_sdiff.2 ⟨h1, fun hu ↦
              (mem_union.1 hu).elim h2 h3⟩)
        exact_mod_cast (card_le_card hsub_sd).trans (card_union_le _ _)
      have hharm : (((ℓ : ℝ) - ℓ') / ℓ) + ∑ j ∈ Ioc 1 ℓ', (1 : ℝ) / j ≤
          ∑ j ∈ Ioc 1 ℓ, (1 : ℝ) / j := by
        have h1 := sub_div_le_harmonic_Ioc hℓ'_pos (hℓ ▸ hℓ_lt.le)
        have hdisj : Disjoint (Ioc 1 ℓ') (Ioc ℓ' ℓ) := by
          rw [disjoint_left]; intro j hj1 hj2; simp only [mem_Ioc] at hj1 hj2; omega
        have hunion : Ioc 1 ℓ' ∪ Ioc ℓ' ℓ = Ioc 1 ℓ := by
          ext j; simp only [mem_union, mem_Ioc]; have := hℓ ▸ hℓ_lt.le; omega
        rw [← hunion, sum_union hdisj]
        linarith
      calc (#(Γ_end \ Γ) : ℝ) ≤ (#Γ' : ℝ) + (#(Γ_end \ (Γ ∪ Γ')) : ℝ) := hsdiff_card
        _ ≤ 12 * Real.sqrt (boolWeight f * boolSparsity f) * (((ℓ : ℝ) - ℓ') / ℓ) +
              12 * Real.sqrt (boolWeight f * boolSparsity f) *
                ∑ j ∈ Ioc 1 ℓ', (1 : ℝ) / j := add_le_add hstep_bound hcard_end
        _ = 12 * Real.sqrt (boolWeight f * boolSparsity f) *
              ((((ℓ : ℝ) - ℓ') / ℓ) + ∑ j ∈ Ioc 1 ℓ', (1 : ℝ) / j) := by ring
        _ ≤ 12 * Real.sqrt (boolWeight f * boolSparsity f) *
              ∑ j ∈ Ioc 1 ℓ, (1 : ℝ) / j :=
            mul_le_mul_of_nonneg_left hharm
              (by have := boolWeight_nonneg f; positivity)

/-- Existence of a parity set `Γ` of size at most `12 * √(δ(f) * k(f)) * log₂ k(f)` making `f`
constant under every assignment of parities in `Γ`. -/
theorem exists_parity_determining_set {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) :
    ∃ Γ : Finset (Finset ι),
      (∀ b : Finset ι → Bool, IsConstantOnParityFiber f Γ b) ∧
      (#Γ : ℝ) ≤ 12 * Real.sqrt (boolWeight f * boolSparsity f) *
        Real.logb 2 (boolSparsity f) := by
  obtain ⟨Γ, _, hconst, hcard⟩ :=
    exists_parity_determining_set_from hk (boolSparsity f) ∅ (numSupportCosets_empty f) (Or.inr rfl)
  simp only [sdiff_empty] at hcard
  refine ⟨Γ, hconst, hcard.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (by have := boolWeight_nonneg f; positivity)
  have hharm := harmonic_Ioc_one_le_log (boolSparsity f) (by omega)
  have hln2_lt1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlog_nn : 0 ≤ Real.log (boolSparsity f) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ boolSparsity f))
  have hlog_le_logb : Real.log (boolSparsity f) ≤ Real.logb 2 (boolSparsity f) := by
    rw [Real.logb]
    exact le_div_self hlog_nn (Real.log_pos (by norm_num)) hln2_lt1
  exact hharm.trans hlog_le_logb

/-- **Weighted Fourier rank-sparsity bound**: every Boolean function `f` with `k(f) > 1` satisfies
`r(f) ≤ 12 * √(δ(f) * k(f)) * log₂ k(f)`. -/
theorem fourierRank_le_mul_sqrt_weight_sparsity_logb {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) :
    (fourierRank f : ℝ) ≤
      12 * Real.sqrt (boolWeight f * boolSparsity f) * Real.logb 2 (boolSparsity f) := by
  obtain ⟨Γ, hconst, hcard⟩ := exists_parity_determining_set hk
  have hr : (fourierRank f : ℝ) ≤ #Γ := by
    exact_mod_cast fourierRank_le_card_of_constant_on_all_fibers hconst
  exact hr.trans hcard

/-- **Boolean weight lower bound from Fourier rank and sparsity**: every Boolean function `f` with
`k(f) > 1` satisfies `(1 / 144) * (1 / k(f)) * (r(f) / log₂ k(f))^2 ≤ δ(f)`. -/
theorem boolWeight_ge_div_sparsity_mul_sq_rank_div_logb {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) :
    (1 / 144 : ℝ) * ((1 / (boolSparsity f : ℝ)) *
      ((fourierRank f : ℝ) / Real.logb 2 (boolSparsity f)) ^ 2) ≤ boolWeight f := by
  have hr := fourierRank_le_mul_sqrt_weight_sparsity_logb hk
  have hk_pos : (0 : ℝ) < boolSparsity f := by exact_mod_cast (by omega : 0 < boolSparsity f)
  have hlog_pos : 0 < Real.logb 2 (boolSparsity f) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hk)
  have hδ_nn : 0 ≤ boolWeight f := boolWeight_nonneg f
  have hsq : (fourierRank f : ℝ) ^ 2 ≤
      144 * (boolWeight f * boolSparsity f) * Real.logb 2 (boolSparsity f) ^ 2 := by
    have := sq_le_sq' (by linarith [show (0 : ℝ) ≤ fourierRank f by positivity]) hr
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at this
    linarith
  rw [div_pow]
  have hkne := hk_pos.ne'
  have hlne := hlog_pos.ne'
  have : (1 / 144 : ℝ) * (1 / (boolSparsity f : ℝ) *
      ((fourierRank f : ℝ) ^ 2 / Real.logb 2 (boolSparsity f) ^ 2)) =
      (fourierRank f : ℝ) ^ 2 /
        (144 * boolSparsity f * Real.logb 2 (boolSparsity f) ^ 2) := by ring
  rw [this, div_le_iff₀ (by positivity)]
  linarith

/-- **Sanyal's Fourier rank-sparsity theorem**: every Boolean function
`f` with `k(f) > 1` satisfies `r(f) ≤ 12 * √(k(f)) * log₂ k(f)`.
-/
theorem fourierRank_le_mul_sqrt_sparsity_logb {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) :
    (fourierRank f : ℝ) ≤ 12 * Real.sqrt (boolSparsity f) * Real.logb 2 (boolSparsity f) := by
  refine (fourierRank_le_mul_sqrt_weight_sparsity_logb hk).trans ?_
  have hlog_nn : 0 ≤ Real.logb 2 (boolSparsity f) :=
    (Real.logb_pos (by norm_num) (by exact_mod_cast hk)).le
  have hsqrt : Real.sqrt (boolWeight f * boolSparsity f) ≤ Real.sqrt (boolSparsity f) :=
    Real.sqrt_le_sqrt (by
      calc boolWeight f * boolSparsity f ≤ 1 * boolSparsity f :=
            mul_le_mul_of_nonneg_right (boolWeight_le_one f) (Nat.cast_nonneg _)
        _ = boolSparsity f := one_mul _)
  nlinarith

end ParityFibersAndSanyal

end CslibFrontier.BooleanFunction
