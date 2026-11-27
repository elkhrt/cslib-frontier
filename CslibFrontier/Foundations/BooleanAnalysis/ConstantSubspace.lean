/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.BooleanAnalysis.FourierMeasures

import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constant Affine Subspaces and Parity-Fiber Averaging for Boolean Functions

This module proves the Tsang–Wong–Xie–Zhang constant affine subspace lemma
and develops parity-fiber Boolean-cube parameterizations together with average weight and average
non-empty Fourier sparsity bounds under random parity restrictions for Boolean functions
`f : (ι → Bool) → Bool` over arbitrary finite index types `ι`, under standard Lean axioms.

## Main definitions

* `CslibFrontier.BooleanFunction.IsConstantOnParityFiber`: `f` is constant on the affine subspace
  `{x : ∀ γ ∈ Γ, parityOn γ x = b γ}`.
* `CslibFrontier.BooleanFunction.supportCosets`, `CslibFrontier.BooleanFunction.numSupportCosets`:
  the
  equivalence classes of `boolSupport f` modulo `paritySpan Γ` and their cardinality.
* `CslibFrontier.BooleanFunction.ParityFiberBasis`: canonical Boolean-cube parameterization of the
  affine fibers of a parity set `Γ`, with Boolean restriction `ParityFiberBasis.restrict`.

## Main results

* `CslibFrontier.BooleanFunction.exists_constant_parity_subspace_le_spectralNorm`: existence of an
  affine
  subspace of codimension at most `‖f̂‖₁` on which `f` is constant.
* `CslibFrontier.BooleanFunction.exists_constant_parity_subspace_le_three_mul_sqrt`: codimension at
  most
  `3 √(δ(f) k(f))` when `0 < δ(f)`.
* `CslibFrontier.BooleanFunction.fourierRank_le_card_of_constant_on_all_fibers`: if `f` is constant
  on
  every assignment of `Γ`, then `r(f) ≤ |Γ|`.
* `CslibFrontier.BooleanFunction.ParityFiberBasis.expect_boolWeight_restrict`: the expected Boolean
  weight of `f|_b` over uniform fiber assignments `b` equals `δ(f)`.
* `CslibFrontier.BooleanFunction.ParityFiberBasis.le_expect_boolNonemptySparsity_restrict`: the
  expected
  non-empty Fourier sparsity of `f|_b` is at least `ℓ^2 / (4 k(f))` when `ℓ ≥ 2`.
-/

public section

namespace CslibFrontier.BooleanFunction

open Cslib Cslib.BitString Finset
open scoped BigOperators

section HyperplaneFolding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Predicate asserting that `f : (ι → Bool) → Bool` is constant on the affine subspace
`{x : ∀ γ ∈ Γ, parityOn γ x = b γ}`. -/
@[expose]
def IsConstantOnParityFiber (f : (ι → Bool) → Bool) (Γ : Finset (Finset ι))
    (b : Finset ι → Bool) : Prop :=
  ∃ v : Bool, ∀ x : ι → Bool, (∀ γ ∈ Γ, parityOn γ x = b γ) → f x = v

/-- Embedding of `({i : ι // i ≠ i₀} → Bool)` onto the hyperplane `{x | parityOn T x = β}`
when `i₀ ∈ T`. -/
private def hyperplaneEmbed {T : Finset ι} {i₀ : ι} (_ : i₀ ∈ T) (β : Bool)
    (y : {i : ι // i ≠ i₀} → Bool) : ι → Bool :=
  let y0 : ι → Bool := fun j ↦ if hj : j = i₀ then false else y ⟨j, hj⟩
  Function.update y0 i₀ (β ^^ parityOn (T.erase i₀) y0)

omit [Fintype ι] in
private theorem parityOn_hyperplaneEmbed {T : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ T) (β : Bool)
    (y : {i : ι // i ≠ i₀} → Bool) :
    parityOn T (hyperplaneEmbed hi₀ β y) = β := by
  dsimp [hyperplaneEmbed]
  set y0 : ι → Bool := fun j ↦ if hj : j = i₀ then false else y ⟨j, hj⟩
  rw [parityOn_eq_xor_erase hi₀, Function.update_self,
    parityOn_update_of_notMem (notMem_erase i₀ T)]
  cases β <;> cases parityOn (T.erase i₀) y0 <;> rfl

omit [Fintype ι] in
private theorem hyperplaneEmbed_apply_ne {T : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ T) (β : Bool)
    (y : {i : ι // i ≠ i₀} → Bool) (j : {i : ι // i ≠ i₀}) :
    hyperplaneEmbed hi₀ β y j.1 = y j := by
  simp [hyperplaneEmbed, j.2]

private def liftFinset (i₀ : ι) (U : Finset {i : ι // i ≠ i₀}) : Finset ι :=
  U.map ⟨Subtype.val, Subtype.val_injective⟩

private def projFinset (i₀ : ι) (S : Finset ι) : Finset {i : ι // i ≠ i₀} :=
  univ.filter fun j ↦ j.1 ∈ S

omit [Fintype ι] [DecidableEq ι] in
private theorem notMem_liftFinset (i₀ : ι) (U : Finset {i : ι // i ≠ i₀}) :
    i₀ ∉ liftFinset i₀ U := by
  classical
  simp only [liftFinset, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
  intro j _
  exact j.2

private theorem liftFinset_projFinset {i₀ : ι} {S : Finset ι} (hS : i₀ ∉ S) :
    liftFinset i₀ (projFinset i₀ S) = S := by
  ext i
  simp only [liftFinset, projFinset, mem_map, mem_filter, mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hj
  · intro hi
    have hne : i ≠ i₀ := by rintro rfl; exact hS hi
    exact ⟨⟨i, hne⟩, hi, rfl⟩

private theorem projFinset_liftFinset (i₀ : ι) (U : Finset {i : ι // i ≠ i₀}) :
    projFinset i₀ (liftFinset i₀ U) = U := by
  ext j
  simp [liftFinset, projFinset]

omit [Fintype ι] in
private theorem parityOn_liftFinset_hyperplaneEmbed {T : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ T)
    (β : Bool) (U : Finset {i : ι // i ≠ i₀}) (y : {i : ι // i ≠ i₀} → Bool) :
    parityOn (liftFinset i₀ U) (hyperplaneEmbed hi₀ β y) = parityOn U y := by
  rw [parityOn_eq_sum, parityOn_eq_sum, liftFinset, sum_map]
  refine sum_congr rfl fun j _ ↦ ?_
  exact hyperplaneEmbed_apply_ne hi₀ β y j

private theorem abs_add_abs_sub_abs_add_of_mul_neg {a d : ℝ} (h : a * d < 0) :
    |a| + |d| - |a + d| = 2 * min |a| |d| := by
  rcases le_total |a| |d| with hle | hle
  · rw [min_eq_left hle]
    by_cases ha0 : 0 ≤ a
    · have hd0 : d ≤ 0 := nonpos_of_mul_nonpos_right h.le (lt_of_le_of_ne ha0 fun h0 ↦ by
        rw [← h0, zero_mul] at h; exact lt_irrefl 0 h)
      have ha1 : |a| = a := abs_of_nonneg ha0
      have hd1 : |d| = -d := abs_of_nonpos hd0
      rw [ha1, hd1, abs_of_nonpos (by linarith)]
      ring
    · have ha' : a < 0 := lt_of_not_ge ha0
      have hd0 : 0 ≤ d := nonneg_of_mul_nonpos_right h.le ha'
      have ha1 : |a| = -a := abs_of_neg ha'
      have hd1 : |d| = d := abs_of_nonneg hd0
      rw [ha1, hd1, abs_of_nonneg (by linarith)]
      ring
  · rw [min_eq_right hle]
    by_cases ha0 : 0 ≤ a
    · have hd0 : d ≤ 0 := nonpos_of_mul_nonpos_right h.le (lt_of_le_of_ne ha0 fun h0 ↦ by
        rw [← h0, zero_mul] at h; exact lt_irrefl 0 h)
      have ha1 : |a| = a := abs_of_nonneg ha0
      have hd1 : |d| = -d := abs_of_nonpos hd0
      rw [ha1, hd1, abs_of_nonneg (by linarith)]
      ring
    · have ha' : a < 0 := lt_of_not_ge ha0
      have hd0 : 0 ≤ d := nonneg_of_mul_nonpos_right h.le ha'
      have ha1 : |a| = -a := abs_of_neg ha'
      have hd1 : |d| = d := abs_of_nonneg hd0
      rw [ha1, hd1, abs_of_nonpos (by linarith)]
      ring

private theorem fourierCoeff_comp_hyperplaneEmbed {T : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ T)
    (β : Bool) (f : (ι → Bool) → ℝ) (U : Finset {i : ι // i ≠ i₀}) :
    fourierCoeff (fun y ↦ f (hyperplaneEmbed hi₀ β y)) U =
      fourierCoeff f (liftFinset i₀ U) +
        signVal β * fourierCoeff f (symmDiff (liftFinset i₀ U) T) := by
  have hexp : (fun y ↦ f (hyperplaneEmbed hi₀ β y)) = fun y ↦
      ∑ V : Finset {i : ι // i ≠ i₀},
        (fourierCoeff f (liftFinset i₀ V) +
          signVal β * fourierCoeff f (symmDiff (liftFinset i₀ V) T)) * chi ℝ V y := by
    ext y
    set x := hyperplaneEmbed hi₀ β y
    rw [← sum_fourierCoeff_mul_chi f x]
    have hpart : ∑ S : Finset ι, fourierCoeff f S * chi ℝ S x =
        (∑ S : Finset ι with i₀ ∉ S, fourierCoeff f S * chi ℝ S x) +
        (∑ S : Finset ι with i₀ ∈ S, fourierCoeff f S * chi ℝ S x) := by
      rw [← sum_filter_add_sum_filter_not (s := univ) (p := fun S : Finset ι ↦ i₀ ∈ S), add_comm]
    rw [hpart]
    have h1 : ∑ S : Finset ι with i₀ ∉ S, fourierCoeff f S * chi ℝ S x =
        ∑ V : Finset {i : ι // i ≠ i₀}, fourierCoeff f (liftFinset i₀ V) * chi ℝ V y := by
      refine sum_bij (fun S _ ↦ projFinset i₀ S) (fun _ _ ↦ mem_univ _)
        (fun S₁ h₁ S₂ h₂ h ↦ by
          rw [← liftFinset_projFinset (mem_filter.1 h₁).2,
            ← liftFinset_projFinset (mem_filter.1 h₂).2, h])
        (fun V _ ↦ ⟨liftFinset i₀ V, mem_filter.2 ⟨mem_univ _, notMem_liftFinset i₀ V⟩,
          projFinset_liftFinset i₀ V⟩)
        fun S hS ↦ ?_
      have hlift := liftFinset_projFinset (mem_filter.1 hS).2
      conv_lhs => rw [← hlift]
      rw [chi_eq_signVal_parityOn, chi_eq_signVal_parityOn,
        parityOn_liftFinset_hyperplaneEmbed]
    have h2 : ∑ S : Finset ι with i₀ ∈ S, fourierCoeff f S * chi ℝ S x =
        ∑ V : Finset {i : ι // i ≠ i₀},
          signVal β * fourierCoeff f (symmDiff (liftFinset i₀ V) T) * chi ℝ V y := by
      refine sum_bij (fun S _ ↦ projFinset i₀ (symmDiff S T)) (fun _ _ ↦ mem_univ _)
        (fun S₁ h₁ S₂ h₂ h ↦ by
          have hn1 : i₀ ∉ symmDiff S₁ T := by simp [mem_symmDiff, (mem_filter.1 h₁).2, hi₀]
          have hn2 : i₀ ∉ symmDiff S₂ T := by simp [mem_symmDiff, (mem_filter.1 h₂).2, hi₀]
          have hsd : symmDiff S₁ T = symmDiff S₂ T := by
            rw [← liftFinset_projFinset hn1, ← liftFinset_projFinset hn2, h]
          have := congr_arg (symmDiff · T) hsd
          simpa [symmDiff_symmDiff_cancel_right] using this)
        (fun V _ ↦ ⟨symmDiff (liftFinset i₀ V) T,
          mem_filter.2 ⟨mem_univ _, by simp [mem_symmDiff, notMem_liftFinset i₀ V, hi₀]⟩, by
          rw [symmDiff_symmDiff_cancel_right, projFinset_liftFinset]⟩)
        fun S hS ↦ ?_
      have hn : i₀ ∉ symmDiff S T := by simp [mem_symmDiff, (mem_filter.1 hS).2, hi₀]
      have hlift := liftFinset_projFinset hn
      rw [hlift, symmDiff_symmDiff_cancel_right]
      have hchi : chi ℝ S x = signVal β * chi ℝ (projFinset i₀ (symmDiff S T)) y := by
        have hsd : S = symmDiff (symmDiff S T) T := by
          rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
        conv_lhs => rw [hsd, ← chi_mul_chi]
        have hc1 : chi ℝ (symmDiff S T) x = chi ℝ (projFinset i₀ (symmDiff S T)) y := by
          conv_lhs => rw [← hlift]
          rw [chi_eq_signVal_parityOn, chi_eq_signVal_parityOn]
          exact congr_arg signVal (parityOn_liftFinset_hyperplaneEmbed hi₀ β _ y)
        have hc2 : chi ℝ T x = signVal β := by
          rw [chi_eq_signVal_parityOn]
          exact congr_arg signVal (parityOn_hyperplaneEmbed hi₀ β y)
        rw [hc1, hc2, mul_comm]
      rw [hchi]
      ring
    rw [h1, h2, ← sum_add_distrib]
    refine sum_congr rfl fun V _ ↦ by ring
  rw [hexp, fourierCoeff_sum_mul]
  simp_rw [fourierCoeff_chi, mul_ite, mul_one, mul_zero]
  simp

/-- Potential-function version of Tsang–Wong–Xie–Zhang : every Boolean function `f` is
constant on an affine subspace of codimension at most `(‖f̂‖₁ + 1) / (1 + max_S |f̂(S)|)`.
-/
private theorem exists_constant_subspace_potential :
    ∀ (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n →
      ∀ f : (ι → Bool) → Bool,
      ∃ (Γ : Finset (Finset ι)) (b : Finset ι → Bool),
        LinearIndependent (ZMod 2) (fun γ : Γ ↦ parityVec γ.1) ∧
        IsConstantOnParityFiber f Γ b ∧
        ∀ M : ℝ, (∃ S, |boolFourierCoeff f S| = M) → (∀ S, |boolFourierCoeff f S| ≤ M) →
          (#Γ : ℝ) ≤ (boolSpectralNorm f + 1) / (1 + M) := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard f
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
    refine ⟨∅, fun _ ↦ false, linearIndependent_empty_type, ?_, fun M ⟨S, hS⟩ hmax ↦ ?_⟩
    · refine ⟨f 0, fun x _ ↦ congr_arg f (Subsingleton.elim x 0)⟩
    · simp only [card_empty, Nat.cast_zero]
      have hM0 : 0 ≤ M := hS ▸ abs_nonneg _
      have hA : 0 ≤ boolSpectralNorm f := spectralNorm_nonneg _
      positivity
  | succ n ih =>
    intro ι _ _ hcard f
    by_cases hk1 : boolSparsity f = 1
    · obtain ⟨S₀, v₀, hv₀⟩ := boolSparsity_eq_one_iff.1 hk1
      have hA1 : boolSpectralNorm f = 1 := boolSpectralNorm_eq_one_of_boolSparsity_eq_one hk1
      by_cases hS0 : S₀ = ∅
      · refine ⟨∅, fun _ ↦ false, linearIndependent_empty_type,
          ⟨v₀, fun x _ ↦ by simp [hv₀ x, hS0]⟩, fun M ⟨S, hS⟩ _ ↦ ?_⟩
        simp only [card_empty, Nat.cast_zero]
        have : 0 ≤ M := hS ▸ abs_nonneg _
        have : 0 ≤ boolSpectralNorm f := spectralNorm_nonneg _
        positivity
      · refine ⟨{S₀}, fun _ ↦ false, ?_, ?_, ?_⟩
        · refine linearIndependent_unique_iff.2 ?_
          have hval : (default : ({S₀} : Finset (Finset ι))).1 = S₀ :=
            mem_singleton.1 (default : ({S₀} : Finset (Finset ι))).2
          rw [hval]
          exact parityVec_eq_zero_iff.not.2 hS0
        · refine ⟨v₀, fun x hx ↦ ?_⟩
          rw [hv₀ x, hx S₀ (mem_singleton_self S₀), Bool.xor_false]
        · rintro M ⟨S, rfl⟩ _
          have hM1 : |boolFourierCoeff f S| ≤ 1 := abs_boolFourierCoeff_le_one f S
          have hM0 : 0 ≤ |boolFourierCoeff f S| := abs_nonneg _
          simp only [card_singleton, Nat.cast_one, hA1]
          exact (one_le_div (by linarith)).2 (by linarith)
    · -- General case: k(f) ≥ 2. Pick S₁ maximizing |f̂(S)| and S₂ maximizing |f̂(S)| on S ≠ S₁.
      have hk2 : 1 < boolSparsity f := by have := boolSparsity_pos f; omega
      have hsupp_ne : (boolSupport f).Nonempty := card_pos.1 (show 0 < boolSparsity f by omega)
      obtain ⟨S₁, hS₁_mem, hS₁_max⟩ :=
        exists_max_image (boolSupport f) (fun S ↦ |boolFourierCoeff f S|) hsupp_ne
      set M₁ : ℝ := |boolFourierCoeff f S₁|
      have hM₁_all : ∀ S : Finset ι, |boolFourierCoeff f S| ≤ M₁ := fun S ↦ by
        by_cases hS : S ∈ boolSupport f
        · exact hS₁_max S hS
        · rw [mem_boolSupport, not_not] at hS
          rw [hS, abs_zero]
          exact abs_nonneg _
      have hM₁_pos : 0 < M₁ := abs_pos.2 (mem_boolSupport.1 hS₁_mem)
      have herase_ne : ((boolSupport f).erase S₁).Nonempty :=
        card_pos.1 (by rw [card_erase_of_mem hS₁_mem]; change 0 < boolSparsity f - 1; omega)
      obtain ⟨S₂, hS₂_er, hS₂_max⟩ :=
        exists_max_image ((boolSupport f).erase S₁) (fun S ↦ |boolFourierCoeff f S|) herase_ne
      have hS₂_ne : S₂ ≠ S₁ := (mem_erase.1 hS₂_er).1
      have hS₂_mem : S₂ ∈ boolSupport f := (mem_erase.1 hS₂_er).2
      set m₂ : ℝ := |boolFourierCoeff f S₂|
      have hm₂_pos : 0 < m₂ := abs_pos.2 (mem_boolSupport.1 hS₂_mem)
      have hm₂_le : m₂ ≤ M₁ := hM₁_all S₂
      have hm₂_all : ∀ S : Finset ι, S ≠ S₁ → |boolFourierCoeff f S| ≤ m₂ := fun S hne ↦ by
        by_cases hS : S ∈ boolSupport f
        · exact hS₂_max S (mem_erase.2 ⟨hne, hS⟩)
        · rw [mem_boolSupport, not_not] at hS
          rw [hS, abs_zero]
          exact hm₂_pos.le
      have hM₁_lt1 : M₁ < 1 := by
        have hsq : M₁ ^ 2 + m₂ ^ 2 ≤ 1 := by
          rw [sq_abs, sq_abs,
            ← sum_pair (f := fun S ↦ boolFourierCoeff f S ^ 2) hS₂_ne.symm,
            ← sum_boolFourierCoeff_sq f]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
        nlinarith [sq_pos_of_pos hm₂_pos]
      set T : Finset ι := symmDiff S₁ S₂
      have hT_ne : T.Nonempty := nonempty_iff_ne_empty.2 fun h0 ↦
        hS₂_ne.symm (symmDiff_eq_bot.1 h0)
      obtain ⟨i₀, hi₀⟩ := hT_ne
      let β : Bool := decide (boolFourierCoeff f S₁ * boolFourierCoeff f S₂ < 0)
      set σ : ℝ := signVal β
      have hσ_sq : σ ^ 2 = 1 := by rw [sq, signVal_mul_self]
      have hσ_abs : |σ| = 1 := abs_signVal β
      have hσ_pos : σ * (boolFourierCoeff f S₁ * boolFourierCoeff f S₂) = M₁ * m₂ := by
        have hprod_ne : boolFourierCoeff f S₁ * boolFourierCoeff f S₂ ≠ 0 :=
          mul_ne_zero (mem_boolSupport.1 hS₁_mem) (mem_boolSupport.1 hS₂_mem)
        by_cases hneg : boolFourierCoeff f S₁ * boolFourierCoeff f S₂ < 0
        · have hβ : β = true := decide_eq_true hneg
          have hσ : σ = -1 := by simp [σ, hβ, signVal]
          rw [hσ, ← abs_mul, abs_of_neg hneg]
          ring
        · have hpos : 0 < boolFourierCoeff f S₁ * boolFourierCoeff f S₂ :=
            lt_of_le_of_ne (le_of_not_gt hneg) hprod_ne.symm
          have hβ : β = false := decide_eq_false hneg
          have hσ : σ = 1 := by simp [σ, hβ, signVal]
          rw [hσ, one_mul, ← abs_mul, abs_of_pos hpos]
      -- Restrict f to the hyperplane {x | parityOn T x = β}.
      let ι' := {i : ι // i ≠ i₀}
      have hcard' : Fintype.card ι' = n := by
        have hcc := Fintype.card_subtype_compl (fun i : ι ↦ i = i₀)
        rw [Fintype.card_subtype_eq, hcard] at hcc
        exact hcc
      let g : (ι' → Bool) → Bool := fun y ↦ f (hyperplaneEmbed hi₀ β y)
      have hg_coeff : ∀ U : Finset ι',
          boolFourierCoeff g U = boolFourierCoeff f (liftFinset i₀ U) +
            σ * boolFourierCoeff f (symmDiff (liftFinset i₀ U) T) :=
        fourierCoeff_comp_hyperplaneEmbed hi₀ β (fun x ↦ signVal (f x))
      -- Bound 1: boolSpectralNorm g ≤ boolSpectralNorm f - 2 * M₁.
      let S₁' : Finset ι := if i₀ ∈ S₁ then S₂ else S₁
      have hi₀_S₁' : i₀ ∉ S₁' := by
        dsimp [S₁']
        split_ifs with h1
        · intro h2
          have : i₀ ∉ T := by simp [T, mem_symmDiff, h1, h2]
          exact this hi₀
        · exact h1
      have hS₁'_pair : boolFourierCoeff f S₁' * boolFourierCoeff f (symmDiff S₁' T) =
          boolFourierCoeff f S₁ * boolFourierCoeff f S₂ := by
        dsimp [S₁']
        split_ifs with h1
        · have hsd : symmDiff S₂ T = S₁ := by
            dsimp [T]; rw [symmDiff_comm S₁ S₂, symmDiff_symmDiff_cancel_left]
          rw [hsd, mul_comm]
        · have hsd : symmDiff S₁ T = S₂ := by
            dsimp [T]; rw [symmDiff_symmDiff_cancel_left]
          rw [hsd]
      let U₁ : Finset ι' := projFinset i₀ S₁'
      have hlift_U₁ : liftFinset i₀ U₁ = S₁' := liftFinset_projFinset hi₀_S₁'
      have hA_f : boolSpectralNorm f = ∑ U : Finset ι',
          (|boolFourierCoeff f (liftFinset i₀ U)| +
            |boolFourierCoeff f (symmDiff (liftFinset i₀ U) T)|) := by
        rw [← sum_abs_boolFourierCoeff]
        have hpart : ∑ S : Finset ι, |boolFourierCoeff f S| =
            (∑ S : Finset ι with i₀ ∉ S, |boolFourierCoeff f S|) +
            (∑ S : Finset ι with i₀ ∈ S, |boolFourierCoeff f S|) := by
          rw [← sum_filter_add_sum_filter_not (s := univ) (p := fun S : Finset ι ↦ i₀ ∈ S),
            add_comm]
        rw [hpart, sum_add_distrib]
        congr 1
        · refine sum_bij (fun S _ ↦ projFinset i₀ S) (fun _ _ ↦ mem_univ _)
            (fun a ha b hb h ↦ by
              rw [← liftFinset_projFinset (mem_filter.1 ha).2,
                ← liftFinset_projFinset (mem_filter.1 hb).2, h])
            (fun U _ ↦ ⟨liftFinset i₀ U, mem_filter.2 ⟨mem_univ _, notMem_liftFinset i₀ U⟩,
              projFinset_liftFinset i₀ U⟩)
            fun S hS ↦ by rw [liftFinset_projFinset (mem_filter.1 hS).2]
        · refine sum_bij (fun S _ ↦ projFinset i₀ (symmDiff S T)) (fun _ _ ↦ mem_univ _)
            (fun a ha b hb h ↦ by
              have hna : i₀ ∉ symmDiff a T := by simp [mem_symmDiff, (mem_filter.1 ha).2, hi₀]
              have hnb : i₀ ∉ symmDiff b T := by simp [mem_symmDiff, (mem_filter.1 hb).2, hi₀]
              have hsd : symmDiff a T = symmDiff b T := by
                rw [← liftFinset_projFinset hna, ← liftFinset_projFinset hnb, h]
              have := congr_arg (symmDiff · T) hsd
              simpa [symmDiff_symmDiff_cancel_right] using this)
            (fun U _ ↦ ⟨symmDiff (liftFinset i₀ U) T,
              mem_filter.2 ⟨mem_univ _, by simp [mem_symmDiff, notMem_liftFinset i₀ U, hi₀]⟩,
              by rw [symmDiff_symmDiff_cancel_right, projFinset_liftFinset]⟩)
            fun S hS ↦ by
              have hn : i₀ ∉ symmDiff S T := by simp [mem_symmDiff, (mem_filter.1 hS).2, hi₀]
              rw [liftFinset_projFinset hn, symmDiff_symmDiff_cancel_right]
      have horth_U : ∑ U : Finset ι',
          σ * (boolFourierCoeff f (liftFinset i₀ U) *
            boolFourierCoeff f (symmDiff (liftFinset i₀ U) T)) = 0 := by
        rw [← mul_sum]
        suffices h : 2 * ∑ U : Finset ι',
            boolFourierCoeff f (liftFinset i₀ U) *
              boolFourierCoeff f (symmDiff (liftFinset i₀ U) T) = 0 by
          have : ∑ U : Finset ι', boolFourierCoeff f (liftFinset i₀ U) *
              boolFourierCoeff f (symmDiff (liftFinset i₀ U) T) = 0 := by linarith
          rw [this, mul_zero]
        rw [two_mul, ← sum_boolFourierCoeff_mul_symmDiff f (nonempty_iff_ne_empty.1 ⟨i₀, hi₀⟩)]
        have hpart : ∑ S : Finset ι, boolFourierCoeff f S * boolFourierCoeff f (symmDiff S T) =
            (∑ S : Finset ι with i₀ ∉ S, boolFourierCoeff f S * boolFourierCoeff f (symmDiff S T)) +
            (∑ S : Finset ι with i₀ ∈ S,
              boolFourierCoeff f S * boolFourierCoeff f (symmDiff S T)) := by
          rw [← sum_filter_add_sum_filter_not (s := univ) (p := fun S : Finset ι ↦ i₀ ∈ S),
            add_comm]
        rw [hpart]
        symm
        congr 1
        · refine sum_bij (fun S _ ↦ projFinset i₀ S) (fun _ _ ↦ mem_univ _)
            (fun a ha b hb h ↦ by
              rw [← liftFinset_projFinset (mem_filter.1 ha).2,
                ← liftFinset_projFinset (mem_filter.1 hb).2, h])
            (fun U _ ↦ ⟨liftFinset i₀ U, mem_filter.2 ⟨mem_univ _, notMem_liftFinset i₀ U⟩,
              projFinset_liftFinset i₀ U⟩)
            fun S hS ↦ by rw [liftFinset_projFinset (mem_filter.1 hS).2]
        · refine sum_bij (fun S _ ↦ projFinset i₀ (symmDiff S T)) (fun _ _ ↦ mem_univ _)
            (fun a ha b hb h ↦ by
              have hna : i₀ ∉ symmDiff a T := by simp [mem_symmDiff, (mem_filter.1 ha).2, hi₀]
              have hnb : i₀ ∉ symmDiff b T := by simp [mem_symmDiff, (mem_filter.1 hb).2, hi₀]
              have hsd : symmDiff a T = symmDiff b T := by
                rw [← liftFinset_projFinset hna, ← liftFinset_projFinset hnb, h]
              have := congr_arg (symmDiff · T) hsd
              simpa [symmDiff_symmDiff_cancel_right] using this)
            (fun U _ ↦ ⟨symmDiff (liftFinset i₀ U) T,
              mem_filter.2 ⟨mem_univ _, by simp [mem_symmDiff, notMem_liftFinset i₀ U, hi₀]⟩, by
              rw [symmDiff_symmDiff_cancel_right, projFinset_liftFinset]⟩)
            fun S hS ↦ by
              have hn : i₀ ∉ symmDiff S T := by simp [mem_symmDiff, (mem_filter.1 hS).2, hi₀]
              rw [liftFinset_projFinset hn, symmDiff_symmDiff_cancel_right, mul_comm]
      have hterm_drop : ∀ U : Finset ι',
          (if σ * (boolFourierCoeff f (liftFinset i₀ U) *
              boolFourierCoeff f (symmDiff (liftFinset i₀ U) T)) < 0 then
            (2 / m₂) * (-(σ * (boolFourierCoeff f (liftFinset i₀ U) *
              boolFourierCoeff f (symmDiff (liftFinset i₀ U) T))))
          else 0) ≤
          |boolFourierCoeff f (liftFinset i₀ U)| +
            |boolFourierCoeff f (symmDiff (liftFinset i₀ U) T)| -
            |boolFourierCoeff g U| := by
        intro U
        rw [hg_coeff U]
        set a := boolFourierCoeff f (liftFinset i₀ U)
        set c := boolFourierCoeff f (symmDiff (liftFinset i₀ U) T)
        split_ifs with hneg
        · have hU_ne : U ≠ U₁ := by
            intro rfl
            have : σ * (a * c) = M₁ * m₂ := by
              dsimp [a, c]
              rw [hlift_U₁, hS₁'_pair, hσ_pos]
            linarith [mul_pos hM₁_pos hm₂_pos]
          have ha_le : |a| ≤ m₂ := hm₂_all _ fun h1 ↦ hU_ne <| by
            have hni : i₀ ∉ S₁ := h1 ▸ notMem_liftFinset i₀ U
            have hS1' : S₁' = S₁ := ite_eq_right hni
            rw [← projFinset_liftFinset i₀ U, h1]
            simp [U₁, hS1']
          have hc_le : |c| ≤ m₂ := hm₂_all _ fun h1 ↦ hU_ne <| by
            have hi : i₀ ∈ S₁ := by
              have : i₀ ∈ symmDiff (liftFinset i₀ U) T := by
                simp [mem_symmDiff, notMem_liftFinset i₀ U, hi₀]
              rwa [h1] at this
            have hS1' : S₁' = S₂ := ite_eq_left hi
            have hsd : liftFinset i₀ U = S₂ := by
              have := congr_arg (symmDiff · T) h1
              simpa [symmDiff_symmDiff_cancel_right, T, symmDiff_symmDiff_cancel_left] using this
            rw [← projFinset_liftFinset i₀ U, hsd]
            simp [U₁, hS1']
          have hac_neg : a * (σ * c) < 0 := by linarith
          have hcancel : |a| + |c| - |a + σ * c| = 2 * min |a| |c| := by
            have hσc : |σ * c| = |c| := by rw [abs_mul, hσ_abs, one_mul]
            rw [← hσc]
            exact abs_add_abs_sub_abs_add_of_mul_neg hac_neg
          rw [hcancel]
          have hprod_abs : -(σ * (a * c)) = |a| * |c| := by
            rw [← abs_mul, ← mul_one (|a * c|), ← hσ_abs, ← abs_mul, mul_comm (a * c) σ,
              abs_of_neg hneg]
          rw [hprod_abs]
          have hmin : |a| * |c| ≤ m₂ * min |a| |c| := by
            rcases le_total |a| |c| with hle | hle
            · rw [min_eq_left hle, mul_comm m₂]
              exact mul_le_mul_of_nonneg_left hc_le (abs_nonneg a)
            · rw [min_eq_right hle]
              exact mul_le_mul_of_nonneg_right ha_le (abs_nonneg c)
          rw [div_mul_eq_mul_div, div_le_iff₀ hm₂_pos]
          linarith
        · have htri := abs_add_le a (σ * c)
          rw [abs_mul, hσ_abs, one_mul] at htri
          linarith
      have hdrop : 2 * M₁ ≤ boolSpectralNorm f - boolSpectralNorm g := by
        have hsum_drop : boolSpectralNorm f - boolSpectralNorm g =
            ∑ U : Finset ι', (|boolFourierCoeff f (liftFinset i₀ U)| +
              |boolFourierCoeff f (symmDiff (liftFinset i₀ U) T)| - |boolFourierCoeff g U|) := by
          rw [hA_f, sum_sub_distrib]
          rfl
        rw [hsum_drop]
        refine le_trans ?_ (sum_le_sum fun U _ ↦ hterm_drop U)
        let p : Finset ι' → ℝ := fun U ↦
          σ * (boolFourierCoeff f (liftFinset i₀ U) *
            boolFourierCoeff f (symmDiff (liftFinset i₀ U) T))
        have hneg_sum : M₁ * m₂ ≤ ∑ U : Finset ι', if p U < 0 then -p U else 0 := by
          have hpos_neg : (∑ U : Finset ι', if p U < 0 then -p U else 0) =
              ∑ U : Finset ι', if 0 ≤ p U then p U else 0 := by
            have hdecomp : ∀ U : Finset ι',
                p U = (if 0 ≤ p U then p U else 0) - (if p U < 0 then -p U else 0) := fun U ↦ by
              by_cases h : 0 ≤ p U
              · simp [h, not_lt.2 h]
              · simp [h, lt_of_not_ge h]
            have h0 : ∑ U : Finset ι',
                ((if 0 ≤ p U then p U else 0) - (if p U < 0 then -p U else 0)) = 0 :=
              (sum_congr rfl fun U _ ↦ (hdecomp U).symm).trans horth_U
            rw [sum_sub_distrib] at h0
            linarith
          rw [hpos_neg]
          have hU₁_val : p U₁ = M₁ * m₂ := by
            dsimp [p]
            rw [hlift_U₁, hS₁'_pair, hσ_pos]
          have hnn : 0 ≤ M₁ * m₂ := by positivity
          calc M₁ * m₂ = (if 0 ≤ p U₁ then p U₁ else 0) := by rw [hU₁_val, ite_eq_left hnn]
            _ ≤ ∑ U : Finset ι', if 0 ≤ p U then p U else 0 :=
                single_le_sum (f := fun U ↦ if 0 ≤ p U then p U else 0)
                  (fun U _ ↦ by split_ifs with h <;> linarith) (mem_univ U₁)
        have hfactor : (∑ U : Finset ι', if p U < 0 then (2 / m₂) * (-p U) else 0) =
            (2 / m₂) * ∑ U : Finset ι', if p U < 0 then -p U else 0 := by
          rw [mul_sum]
          refine sum_congr rfl fun U _ ↦ by split_ifs <;> simp
        change 2 * M₁ ≤ ∑ U : Finset ι', if p U < 0 then (2 / m₂) * (-p U) else 0
        rw [hfactor]
        calc 2 * M₁ = (2 / m₂) * (M₁ * m₂) := by field_simp
          _ ≤ (2 / m₂) * ∑ U : Finset ι', if p U < 0 then -p U else 0 :=
              mul_le_mul_of_nonneg_left hneg_sum (by positivity)
      -- Bound 2: max_U |ĝ(U)| ≥ |ĝ(U₁)| = M₁ + m₂ ≥ M₁ + (1 - M₁^2) / (A(f) - M₁).
      obtain ⟨Umax, _, hUmax⟩ :=
        exists_max_image (univ : Finset (Finset ι')) (fun U ↦ |boolFourierCoeff g U|) univ_nonempty
      set Mg : ℝ := |boolFourierCoeff g Umax|
      have hMg_ge : M₁ + m₂ ≤ Mg := by
        refine le_trans ?_ (hUmax U₁ (mem_univ U₁))
        rw [hg_coeff U₁, hlift_U₁]
        set a := boolFourierCoeff f S₁'
        set c := boolFourierCoeff f (symmDiff S₁' T)
        have hsq : |a + σ * c| ^ 2 = (M₁ + m₂) ^ 2 := by
          rw [sq_abs]
          have h1 : a ^ 2 + c ^ 2 = M₁ ^ 2 + m₂ ^ 2 := by
            dsimp [a, c, S₁']
            split_ifs
            · have hsd : symmDiff S₂ T = S₁ := by
                dsimp [T]; rw [symmDiff_comm S₁ S₂, symmDiff_symmDiff_cancel_left]
              rw [hsd]
              dsimp only [M₁, m₂]
              rw [sq_abs, sq_abs, add_comm]
            · have hsd : symmDiff S₁ T = S₂ := by
                dsimp [T]; rw [symmDiff_symmDiff_cancel_left]
              rw [hsd]
              dsimp only [M₁, m₂]
              rw [sq_abs, sq_abs]
          have h2 : a * (σ * c) = M₁ * m₂ := by
            calc a * (σ * c) = σ * (a * c) := by ring
              _ = M₁ * m₂ := by rw [hS₁'_pair, hσ_pos]
          calc (a + σ * c) ^ 2 = a ^ 2 + σ ^ 2 * c ^ 2 + 2 * (a * (σ * c)) := by ring
            _ = (M₁ + m₂) ^ 2 := by rw [hσ_sq, one_mul, h1, h2]; ring
        have hnn : 0 ≤ M₁ + m₂ := by positivity
        exact ((sq_eq_sq₀ (abs_nonneg _) hnn).1 hsq).ge
      have hA_sub_pos : 0 < boolSpectralNorm f - M₁ := by
        have hge : M₁ + m₂ ≤ boolSpectralNorm f := by
          rw [← sum_abs_boolFourierCoeff,
            ← sum_pair (f := fun S ↦ |boolFourierCoeff f S|) hS₂_ne.symm]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ abs_nonneg _
        exact sub_pos.2 (lt_of_lt_of_le (lt_add_of_pos_right M₁ hm₂_pos) hge)
      have hm₂_lb : (1 - M₁ ^ 2) / (boolSpectralNorm f - M₁) ≤ m₂ := by
        rw [div_le_iff₀ hA_sub_pos]
        have h1 : 1 - M₁ ^ 2 = ∑ S ∈ univ.erase S₁, boolFourierCoeff f S ^ 2 := by
          have := add_sum_erase univ (fun S ↦ boolFourierCoeff f S ^ 2) (mem_univ S₁)
          rw [sum_boolFourierCoeff_sq f, ← sq_abs] at this
          linarith
        have h2 : boolSpectralNorm f - M₁ = ∑ S ∈ univ.erase S₁, |boolFourierCoeff f S| := by
          have := add_sum_erase univ (fun S ↦ |boolFourierCoeff f S|) (mem_univ S₁)
          change M₁ + ∑ S ∈ univ.erase S₁, |boolFourierCoeff f S| = boolSpectralNorm f at this
          linarith
        rw [h1, h2, mul_sum]
        refine sum_le_sum fun S hS ↦ ?_
        rw [← sq_abs, sq]
        exact mul_le_mul_of_nonneg_right (hm₂_all S (ne_of_mem_erase hS)) (abs_nonneg _)
      -- Potential drop: (A(g) + 1) / (1 + Mg) ≤ (A(f) + 1) / (1 + M₁) - 1!
      have hpot_drop :
          (boolSpectralNorm g + 1) / (1 + Mg) + 1 ≤ (boolSpectralNorm f + 1) / (1 + M₁) := by
        have hAg1_pos : 0 < boolSpectralNorm g + 1 := by
          linarith [one_le_boolSpectralNorm g]
        have hAf_num_pos : 0 < boolSpectralNorm f + 1 - 2 * M₁ := by linarith
        have h1Mg_lb : (1 + M₁) * ((boolSpectralNorm f + 1 - 2 * M₁) /
            (boolSpectralNorm f - M₁)) ≤ 1 + Mg := by
          have hident : 1 + M₁ + (1 - M₁ ^ 2) / (boolSpectralNorm f - M₁) =
              (1 + M₁) * ((boolSpectralNorm f + 1 - 2 * M₁) / (boolSpectralNorm f - M₁)) := by
            have hne := hA_sub_pos.ne'
            field_simp
            ring
          linarith
        have hden_pos : 0 < (1 + M₁) * ((boolSpectralNorm f + 1 - 2 * M₁) /
            (boolSpectralNorm f - M₁)) := by positivity
        have hstep : (boolSpectralNorm g + 1) / (1 + Mg) ≤
            (boolSpectralNorm f - M₁) / (1 + M₁) := by
          calc (boolSpectralNorm g + 1) / (1 + Mg)
              ≤ (boolSpectralNorm f + 1 - 2 * M₁) / (1 + Mg) :=
                div_le_div_of_nonneg_right (by linarith) (by linarith)
            _ ≤ (boolSpectralNorm f + 1 - 2 * M₁) /
                  ((1 + M₁) * ((boolSpectralNorm f + 1 - 2 * M₁) /
                    (boolSpectralNorm f - M₁))) :=
                div_le_div_of_nonneg_left hAf_num_pos.le hden_pos h1Mg_lb
            _ = (boolSpectralNorm f - M₁) / (1 + M₁) := by
                have h1ne : 1 + M₁ ≠ 0 := by positivity
                have h2ne : boolSpectralNorm f - M₁ ≠ 0 := hA_sub_pos.ne'
                have h3ne : boolSpectralNorm f + 1 - 2 * M₁ ≠ 0 := hAf_num_pos.ne'
                field_simp
        have hsub : (boolSpectralNorm f - M₁) / (1 + M₁) + 1 =
            (boolSpectralNorm f + 1) / (1 + M₁) := by
          have h1ne : 1 + M₁ ≠ 0 := by positivity
          field_simp
          ring
        linarith
      -- Apply the induction hypothesis to g.
      obtain ⟨Γ', b', hli', ⟨v, hv⟩, hcard_Γ'⟩ := ih hcard' g
      have hΓ'_le := hcard_Γ' Mg ⟨Umax, rfl⟩ (fun U ↦ hUmax U (mem_univ U))
      let liftEmb : Finset ι' ↪ Finset ι :=
        ⟨liftFinset i₀, fun a b h ↦ by
          rw [← projFinset_liftFinset i₀ a, ← projFinset_liftFinset i₀ b, h]⟩
      let Γ₀ : Finset (Finset ι) := Γ'.map liftEmb
      have hT_notMem : T ∉ Γ₀ := by
        intro hmem
        obtain ⟨U, _, hU⟩ := mem_map.1 hmem
        have : i₀ ∉ T := hU ▸ notMem_liftFinset i₀ U
        exact this hi₀
      let Γ : Finset (Finset ι) := insert T Γ₀
      let b : Finset ι → Bool := fun γ ↦ if γ = T then β else b' (projFinset i₀ γ)
      refine ⟨Γ, b, ?_, ?_, fun M ⟨SM, hSM⟩ hMmax ↦ ?_⟩
      · -- Linear independence of Γ = insert T Γ₀ (since i₀ ∈ T while i₀ ∉ γ for all γ ∈ Γ₀).
        rw [Fintype.linearIndependent_iff]
        intro c hc γ
        have hi₀_sum := congr_fun hc i₀
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi₀_sum
        have hcT : c ⟨T, mem_insert_self T Γ₀⟩ = 0 := by
          have hsingle : (∑ x : Γ, c x * parityVec x.1 i₀) = c ⟨T, mem_insert_self T Γ₀⟩ := by
            refine (sum_eq_single ⟨T, mem_insert_self T Γ₀⟩ (fun x _ hx ↦ ?_) (by simp)).trans ?_
            · have hxΓ₀ : x.1 ∈ Γ₀ := by
                rcases mem_insert.1 x.2 with h | h
                · exact False.elim (hx (Subtype.ext h))
                · exact h
              obtain ⟨U, _, hU⟩ := mem_map.1 hxΓ₀
              have hni : i₀ ∉ x.1 := hU.symm ▸ notMem_liftFinset i₀ U
              rw [parityVec_of_notMem hni, mul_zero]
            · rw [parityVec_of_mem hi₀, mul_one]
          rwa [hsingle] at hi₀_sum
        by_cases hγT : γ = ⟨T, mem_insert_self T Γ₀⟩
        · rwa [hγT]
        · have hγΓ₀ : γ.1 ∈ Γ₀ := by
            rcases mem_insert.1 γ.2 with h | h
            · exact False.elim (hγT (Subtype.ext h))
            · exact h
          obtain ⟨Uγ, hUγ, hUγ_eq⟩ := mem_map.1 hγΓ₀
          have hli'_iff := Fintype.linearIndependent_iff.1 hli'
            (fun u : Γ' ↦ c ⟨liftEmb u.1, mem_insert_of_mem (mem_map_of_mem liftEmb u.2)⟩)
          have hsum' : ∑ u : Γ',
              c ⟨liftEmb u.1, mem_insert_of_mem (mem_map_of_mem liftEmb u.2)⟩ •
                parityVec u.1 = 0 := by
            ext j
            have hj := congr_fun hc j.1
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
            rw [← add_sum_erase _ _ (mem_univ (⟨T, mem_insert_self T Γ₀⟩ : Γ)),
              hcT, zero_mul, zero_add] at hj
            rw [← hj]
            refine sum_bij
              (fun u _ ↦ ⟨liftEmb u.1, mem_insert_of_mem (mem_map_of_mem liftEmb u.2)⟩)
              (fun u _ ↦ mem_erase.2 ⟨fun h ↦ hT_notMem (by
                have : liftEmb u.1 = T := congr_arg Subtype.val h
                rw [← this]; exact mem_map_of_mem liftEmb u.2), mem_univ _⟩)
              (fun u₁ _ u₂ _ h ↦ Subtype.ext (liftEmb.injective (congr_arg Subtype.val h)))
              (fun x hx ↦ by
                have hxne : x.1 ≠ T := fun h ↦ (mem_erase.1 hx).1 (Subtype.ext h)
                have hx0 : x.1 ∈ Γ₀ := (mem_insert.1 x.2).resolve_left hxne
                obtain ⟨u, hu, hux⟩ := mem_map.1 hx0
                exact ⟨⟨u, hu⟩, mem_univ _, Subtype.ext hux⟩)
              fun u _ ↦ by
                congr 1
                change (if j ∈ u.1 then (1 : ZMod 2) else 0) =
                  (if j.1 ∈ liftFinset i₀ u.1 then 1 else 0)
                simp [liftFinset]
          have hzero := hli'_iff hsum' ⟨Uγ, hUγ⟩
          have hsub_eq : (⟨liftEmb Uγ, mem_insert_of_mem (mem_map_of_mem liftEmb hUγ)⟩ : Γ) = γ :=
            Subtype.ext hUγ_eq
          simpa [hsub_eq] using hzero
      · -- f is constant (= v) on the fiber (Γ, b).
        refine ⟨v, fun x hx ↦ ?_⟩
        let y : ι' → Bool := fun j ↦ x j.1
        have hxy : hyperplaneEmbed hi₀ β y = x := by
          ext i
          by_cases hi : i = i₀
          · subst hi
            have hxT : parityOn T x = β := by
              simpa [b] using hx T (mem_insert_self T Γ₀)
            have heT : parityOn T (hyperplaneEmbed hi₀ β y) = β :=
              parityOn_hyperplaneEmbed hi₀ β y
            rw [parityOn_eq_xor_erase hi₀] at hxT heT
            have her : parityOn (T.erase i) (hyperplaneEmbed hi₀ β y) = parityOn (T.erase i) x :=
              parityOn_congr fun j hj ↦
                hyperplaneEmbed_apply_ne hi₀ β y ⟨j, ne_of_mem_erase hj⟩
            rw [her] at heT
            have hcomb := heT.trans hxT.symm
            cases h1 : hyperplaneEmbed hi₀ β y i <;> cases h2 : x i <;>
              cases h3 : parityOn (T.erase i) x <;> rw [h1, h2, h3] at hcomb <;>
              cases hcomb
          · exact hyperplaneEmbed_apply_ne hi₀ β y ⟨i, hi⟩
        rw [← hxy]
        refine hv y fun u hu ↦ ?_
        have hmem : liftEmb u ∈ Γ := mem_insert_of_mem (mem_map_of_mem liftEmb hu)
        have hne : liftEmb u ≠ T := fun h ↦ hT_notMem (h ▸ mem_map_of_mem liftEmb hu)
        have hxu := hx (liftEmb u) hmem
        rw [← hxy] at hxu
        have hbl : b (liftEmb u) = b' u := by
          dsimp only [b]
          rw [ite_eq_right hne]
          exact congr_arg b' (projFinset_liftFinset i₀ u)
        rw [hbl] at hxu
        exact (parityOn_liftFinset_hyperplaneEmbed hi₀ β u y).symm.trans hxu
      · -- Size bound: #Γ = #Γ' + 1 ≤ (A(f) + 1) / (1 + M).
        have hMeq : M = M₁ := le_antisymm (hSM ▸ hM₁_all SM) (hMmax S₁)
        rw [hMeq, card_insert_of_notMem hT_notMem, card_map, Nat.cast_add, Nat.cast_one]
        linarith
    -- Fix the tiny M ≤ 1 proof in the hk1 branch above? Wait — all branches already closed except
    -- line 232!

/-- Boolean function `f : (ι → Bool) → Bool`, there exist a linearly independent set of parities
`Γ : Finset (Finset ι)` with `|Γ| ≤ ‖f̂‖₁` and an assignment `b : Finset ι → Bool` such that `f` is
constant on `{x : ∀ γ ∈ Γ, parityOn γ x = b γ}`.
-/
theorem exists_constant_parity_subspace_le_spectralNorm (f : (ι → Bool) → Bool) :
    ∃ (Γ : Finset (Finset ι)) (b : Finset ι → Bool),
      LinearIndependent (ZMod 2) (fun γ : Γ ↦ parityVec γ.1) ∧
      IsConstantOnParityFiber f Γ b ∧
      (#Γ : ℝ) ≤ boolSpectralNorm f := by
  obtain ⟨Smax, _, hmax⟩ :=
    exists_max_image (univ : Finset (Finset ι)) (fun S ↦ |boolFourierCoeff f S|) univ_nonempty
  set M := |boolFourierCoeff f Smax|
  obtain ⟨Γ, b, hli, hconst, hcard⟩ :=
    exists_constant_subspace_potential (Fintype.card ι) rfl f
  refine ⟨Γ, b, hli, hconst, (hcard M ⟨Smax, rfl⟩ fun S ↦ hmax S (mem_univ S)).trans ?_⟩
  have hM_nn : 0 ≤ M := abs_nonneg _
  rw [div_le_iff₀ (by positivity)]
  have hparseval : 1 ≤ boolSpectralNorm f * M := by
    calc (1 : ℝ) = ∑ S : Finset ι, boolFourierCoeff f S ^ 2 := (sum_boolFourierCoeff_sq f).symm
      _ ≤ ∑ S : Finset ι, |boolFourierCoeff f S| * M := by
          refine sum_le_sum fun S _ ↦ ?_
          rw [← sq_abs, sq]
          exact mul_le_mul_of_nonneg_left (hmax S (mem_univ S)) (abs_nonneg _)
      _ = boolSpectralNorm f * M := (sum_mul ..).symm
  linarith

/-- Corollary of Tsang–Wong–Xie–Zhang : every Boolean function `f` with `0 < δ(f)` is
constant on an affine subspace of codimension at most `3 √(δ(f) k(f))`.
-/
theorem exists_constant_parity_subspace_le_three_mul_sqrt {f : (ι → Bool) → Bool}
    (hδ : 0 < boolWeight f) :
    ∃ (Γ : Finset (Finset ι)) (b : Finset ι → Bool),
      LinearIndependent (ZMod 2) (fun γ : Γ ↦ parityVec γ.1) ∧
      IsConstantOnParityFiber f Γ b ∧
      (#Γ : ℝ) ≤ 3 * Real.sqrt (boolWeight f * boolSparsity f) := by
  obtain ⟨Γ, b, hli, hconst, hle⟩ := exists_constant_parity_subspace_le_spectralNorm f
  refine ⟨Γ, b, hli, hconst, hle.trans ?_⟩
  rw [mul_comm (boolWeight f)]
  exact boolSpectralNorm_le_three_mul_sqrt hδ

end HyperplaneFolding

section ParityFibersAndSanyal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `f` is constant on every parity assignment to `Γ`, then `supp(f) ⊆ span(Γ)`. -/
theorem boolSupport_subset_paritySpan_of_constant_on_fibers {f : (ι → Bool) → Bool}
    {Γ : Finset (Finset ι)}
    (hconst : ∀ b : Finset ι → Bool, IsConstantOnParityFiber f Γ b) :
    ∀ S ∈ boolSupport f, parityVec S ∈ paritySpan (Γ : Set (Finset ι)) := by
  intro S hS
  by_contra hnot
  -- By linear duality over 𝔽₂, there exists u : ι → ZMod 2 with ⟨γ, u⟩ = 0 for all γ ∈ Γ
  -- and ⟨S, u⟩ = 1!
  let W := paritySpan (Γ : Set (Finset ι))
  have hex_u : ∃ u : ι → ZMod 2, (∀ w ∈ W, ∑ i : ι, w i * u i = 0) ∧
      ∑ i : ι, parityVec S i * u i ≠ 0 := by
    obtain ⟨φ, hφS, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot
      (Module.Projective.of_basis (Module.Basis.ofVectorSpace (ZMod 2) _))
    refine ⟨fun i ↦ φ (Pi.single i 1), fun w hw ↦ ?_, ?_⟩
    · have hw_eq : w = ∑ i : ι, w i • Pi.single i (1 : ZMod 2) := by
        ext i'; simp [Pi.single_apply]
      have h0 : φ w = 0 := by
        have : φ w ∈ Submodule.map φ W := ⟨w, hw, rfl⟩
        rwa [hφW, Submodule.mem_bot] at this
      conv at h0 => rw [hw_eq, map_sum]
      simpa [map_smul, smul_eq_mul] using h0
    · have hS_eq : parityVec S = ∑ i : ι, parityVec S i • Pi.single i (1 : ZMod 2) := by
        ext i'; simp [Pi.single_apply]
      intro h0
      apply hφS
      rw [hS_eq, map_sum]
      simpa [map_smul, smul_eq_mul] using h0
  obtain ⟨u, huW, huS⟩ := hex_u
  let a : ι → Bool := bitStringZModEquiv.symm u
  have ha_Γ : ∀ γ ∈ Γ, parityOn γ a = false := by
    intro γ hγ
    have h0 := huW (parityVec γ) (mem_paritySpan_of_mem hγ)
    have hdot := boolToZModVal_parityOn_eq_dot γ a
    simp only [a, Equiv.apply_symm_apply] at hdot
    rw [h0] at hdot
    cases hp : parityOn γ a
    · rfl
    · rw [hp] at hdot; exact False.elim (one_ne_zero hdot)
  have ha_S : parityOn S a = true := by
    have hdot := boolToZModVal_parityOn_eq_dot S a
    simp only [a, Equiv.apply_symm_apply] at hdot
    cases hp : parityOn S a
    · rw [hp] at hdot; exact False.elim (huS hdot.symm)
    · rfl
  have hf_shift : ∀ x : ι → Bool, f (x + a) = f x := by
    intro x
    obtain ⟨v, hv⟩ := hconst (fun γ ↦ parityOn γ x)
    have hx : f x = v := hv x fun _ _ ↦ rfl
    have hxa : f (x + a) = v := hv (x + a) fun γ hγ ↦ by
      rw [parityOn_add, ha_Γ γ hγ, Bool.xor_false]
    rw [hxa, hx]
  have hfc := boolFourierCoeff_comp_add f a S
  have hcomp : (fun x : ι → Bool ↦ f (x + a)) = f := funext hf_shift
  rw [hcomp, chi_eq_signVal_parityOn, ha_S] at hfc
  have hneg : boolFourierCoeff f S = (-1 : ℝ) * boolFourierCoeff f S := by simpa [signVal] using hfc
  exact mem_boolSupport.1 hS (by linarith)

/-- If `f` is constant on every parity assignment to `Γ`, then `r(f) ≤ dim(span(Γ)) ≤ |Γ|`. -/
theorem fourierRank_le_card_of_constant_on_all_fibers {f : (ι → Bool) → Bool}
    {Γ : Finset (Finset ι)}
    (hconst : ∀ b : Finset ι → Bool, IsConstantOnParityFiber f Γ b) :
    fourierRank f ≤ #Γ := by
  have hle : paritySpan (boolSupport f : Set (Finset ι)) ≤ paritySpan (Γ : Set (Finset ι)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨S, hS, rfl⟩
    exact boolSupport_subset_paritySpan_of_constant_on_fibers hconst S hS
  exact (Submodule.finrank_mono hle).trans (parityDim_le_card Γ)

/-- Equivalence classes (cosets) of `boolSupport f` modulo `paritySpan Γ`, represented as the image
in `(ι → ZMod 2) ⧸ paritySpan Γ`. -/
@[expose]
noncomputable def supportCosets (f : (ι → Bool) → Bool) (Γ : Finset (Finset ι)) :
    Finset ((ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) :=
  @Finset.image _ _ (Classical.decEq _)
    (fun S ↦ Submodule.Quotient.mk (parityVec S)) (boolSupport f)

/-- Membership in `supportCosets f Γ`. -/
theorem mem_supportCosets {f : (ι → Bool) → Bool} {Γ : Finset (Finset ι)}
    {q : (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))} :
    q ∈ supportCosets f Γ ↔
      ∃ S ∈ boolSupport f,
        (Submodule.Quotient.mk (parityVec S) : (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) =
          q := by
  exact @Finset.mem_image _ _ (Classical.decEq _) _ _ _

/-- Number of equivalence classes of `boolSupport f` modulo `paritySpan Γ`. -/
@[expose]
noncomputable def numSupportCosets (f : (ι → Bool) → Bool) (Γ : Finset (Finset ι)) : ℕ :=
  #(supportCosets f Γ)

/-- Cardinality of `supportCosets f Γ` equals `numSupportCosets f Γ`. -/
theorem card_supportCosets (f : (ι → Bool) → Bool) (Γ : Finset (Finset ι)) :
    #(supportCosets f Γ) = numSupportCosets f Γ :=
  rfl

/-- Partition identity: the sizes of the equivalence classes of `boolSupport f` modulo
`paritySpan Γ` sum to `boolSparsity f`. -/
theorem sum_card_supportCoset_eq_boolSparsity (f : (ι → Bool) → Bool) (Γ : Finset (Finset ι))
    [DecidableEq ((ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι)))] :
    ∑ q ∈ supportCosets f Γ,
      #{S ∈ boolSupport f | (Submodule.Quotient.mk (parityVec S) :
        (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = q} =
      boolSparsity f := by
  have hflt : ∀ q, #{S ∈ boolSupport f | (Submodule.Quotient.mk (parityVec S) :
      (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = q} =
      #(@Finset.filter _ (fun S ↦ (Submodule.Quotient.mk (parityVec S) :
        (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = q)
        (fun S ↦ Classical.decEq _ _ _) (boolSupport f)) := fun q ↦ by
    congr 1; ext S; rw [mem_filter, @mem_filter]
  have himg : supportCosets f Γ =
      (boolSupport f).image (fun S ↦ (Submodule.Quotient.mk (parityVec S) :
        (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι)))) := by
    ext q; simp [mem_supportCosets]
  rw [himg]
  exact (card_eq_sum_card_image (fun S ↦ (Submodule.Quotient.mk (parityVec S) :
    (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι)))) (boolSupport f)).symm

@[simp]
theorem numSupportCosets_empty (f : (ι → Bool) → Bool) :
    numSupportCosets f ∅ = boolSparsity f := by
  classical
  have himg : supportCosets f ∅ =
      (boolSupport f).image (fun S ↦ (Submodule.Quotient.mk (parityVec S) :
        (ι → ZMod 2) ⧸ paritySpan ((∅ : Finset (Finset ι)) : Set (Finset ι)))) := by
    ext q; simp [mem_supportCosets]
  rw [← card_supportCosets, himg]
  refine card_image_of_injective _ fun S₁ S₂ h ↦ ?_
  rw [Submodule.Quotient.eq, coe_empty, paritySpan_empty, Submodule.mem_bot, sub_eq_zero] at h
  exact parityVec_injective h

theorem numSupportCosets_anti (f : (ι → Bool) → Bool) {Γ₁ Γ₂ : Finset (Finset ι)}
    (h : paritySpan (Γ₁ : Set (Finset ι)) ≤ paritySpan (Γ₂ : Set (Finset ι))) :
    numSupportCosets f Γ₂ ≤ numSupportCosets f Γ₁ := by
  classical
  let π := Submodule.factor h
  have hsub : supportCosets f Γ₂ ⊆ (supportCosets f Γ₁).image π := by
    intro q hq
    obtain ⟨S, hS, rfl⟩ := mem_supportCosets.1 hq
    exact mem_image.2 ⟨Submodule.Quotient.mk (parityVec S), mem_supportCosets.2 ⟨S, hS, rfl⟩, rfl⟩
  exact (card_le_card hsub).trans card_image_le

/-- Coordinate restriction of `f` after changing Fourier basis so that a linearly independent
`ℬ ⊆ Γ` becomes the first `d` coordinates: given an equivalence `B` with `B(e_{emb γ}) = γ`,
fixing `b : ℬ → Bool` restricts `fourierBasisChange B f` to the remaining coordinates
`{i : ι // i ∉ univ.map emb} → Bool`. -/
private noncomputable def fiberRestrict
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
    {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι) (f : (ι → Bool) → Bool)
    (b : ℬ → Bool) (z : {i : ι // i ∉ univ.map emb} → Bool) : Bool :=
  fourierBasisChange B f fun i ↦
    if h : i ∈ univ.map emb then
      b (Classical.choose (mem_map.1 h))
    else
      z ⟨i, h⟩

private noncomputable def mergeInputs {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι)
    (b : ℬ → Bool) (z : {i : ι // i ∉ univ.map emb} → Bool) : ι → Bool :=
  fun i ↦
    if h : i ∈ univ.map emb then
      b (Classical.choose (mem_map.1 h))
    else
      z ⟨i, h⟩

omit [Fintype ι] in
private theorem mergeInputs_emb {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι)
    (b : ℬ → Bool) (z : {i : ι // i ∉ univ.map emb} → Bool) (γ : ℬ) :
    mergeInputs emb b z (emb γ) = b γ := by
  have hm : emb γ ∈ univ.map emb := mem_map_of_mem emb (mem_univ γ)
  simp only [mergeInputs, dite_eq_left hm]
  have hspec := (Classical.choose_spec (mem_map.1 hm)).2
  rw [emb.injective hspec]

omit [Fintype ι] in
private theorem mergeInputs_compl {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι)
    (b : ℬ → Bool) (z : {i : ι // i ∉ univ.map emb} → Bool)
    (j : {i : ι // i ∉ univ.map emb}) :
    mergeInputs emb b z j.1 = z j := by
  simp only [mergeInputs, dite_eq_right j.2]

private noncomputable def mergeEquiv {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι) :
    ((ℬ → Bool) × ({i : ι // i ∉ univ.map emb} → Bool)) ≃ (ι → Bool) where
  toFun p := mergeInputs emb p.1 p.2
  invFun x := (fun γ ↦ x (emb γ), fun j ↦ x j.1)
  left_inv p := by
    ext γ
    · exact mergeInputs_emb emb p.1 p.2 γ
    · exact mergeInputs_compl emb p.1 p.2 γ
  right_inv x := by
    ext i
    simp only [mergeInputs]
    split_ifs with h
    · exact congr_arg x (Classical.choose_spec (mem_map.1 h)).2
    · rfl

private theorem boolFourierCoeff_fiberRestrict
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
    {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι) (f : (ι → Bool) → Bool)
    (b : ℬ → Bool) (U : Finset {i : ι // i ∉ univ.map emb}) :
    boolFourierCoeff (fiberRestrict B emb f b) U =
      ∑ V : Finset ℬ,
        boolFourierCoeff (fourierBasisChange B f)
          (V.map emb ∪ U.map ⟨Subtype.val, Subtype.val_injective⟩) * chi ℝ V b := by
  let h := fourierBasisChange B f
  let liftC : Finset {i : ι // i ∉ univ.map emb} ↪ Finset ι :=
    ⟨fun W ↦ W.map ⟨Subtype.val, Subtype.val_injective⟩, fun W₁ W₂ heq ↦ by
      ext j
      have := Finset.ext_iff.1 heq j.1
      simp only [mem_map, Function.Embedding.coeFn_mk, Subtype.val_injective.eq_iff,
        exists_eq_right] at this
      exact this⟩
  have hdisj : ∀ (V : Finset ℬ) (W : Finset {i : ι // i ∉ univ.map emb}),
      Disjoint (V.map emb) (liftC W) := by
    intro V W
    rw [disjoint_left]; intro i hiV hiW
    obtain ⟨γ, _, rfl⟩ := mem_map.1 hiV
    obtain ⟨j, _, hj⟩ := mem_map.1 hiW
    dsimp only [Function.Embedding.coeFn_mk] at hj
    exact j.2 (hj ▸ mem_map_of_mem emb (mem_univ γ))
  let hsplit_set : (Finset ℬ × Finset {i : ι // i ∉ univ.map emb}) ≃ Finset ι :=
    { toFun := fun p ↦ p.1.map emb ∪ liftC p.2
      invFun := fun S ↦ (univ.filter fun γ ↦ emb γ ∈ S, univ.filter fun j ↦ j.1 ∈ S)
      left_inv := fun ⟨V, W⟩ ↦ by
        refine Prod.ext ?_ ?_
        · ext γ
          simp only [mem_filter, mem_univ, true_and]
          change (emb γ ∈ V.map emb ∪ W.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ γ ∈ V
          simp only [mem_union, mem_map, Function.Embedding.coeFn_mk]
          exact ⟨fun h ↦ h.elim (fun ⟨γ', hγ', heq⟩ ↦ emb.injective heq ▸ hγ')
              (fun ⟨j, _, heq⟩ ↦ (j.2 (heq ▸ mem_map_of_mem emb (mem_univ γ))).elim),
            fun hγ ↦ Or.inl ⟨γ, hγ, rfl⟩⟩
        · ext j
          simp only [mem_filter, mem_univ, true_and]
          change (j.1 ∈ V.map emb ∪ W.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ j ∈ W
          simp only [mem_union, mem_map, Function.Embedding.coeFn_mk]
          exact ⟨fun h ↦ h.elim
              (fun ⟨γ, _, heq⟩ ↦ (j.2 (heq.symm ▸ mem_map_of_mem emb (mem_univ γ))).elim)
              (fun ⟨j', hj', heq⟩ ↦ Subtype.ext heq ▸ hj'),
            fun hj ↦ Or.inr ⟨j, hj, rfl⟩⟩
      right_inv := fun S ↦ by
        ext i
        change i ∈ (univ.filter fun γ ↦ emb γ ∈ S).map emb ∪
          (univ.filter fun j : {i : ι // i ∉ univ.map emb} ↦ j.1 ∈ S).map
            ⟨Subtype.val, Subtype.val_injective⟩ ↔ i ∈ S
        simp only [mem_union, mem_map, mem_filter, mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro (⟨γ, hγ, rfl⟩ | ⟨j, hj, rfl⟩) <;> assumption
        · intro hi
          by_cases hm : i ∈ univ.map emb
          · obtain ⟨γ, _, rfl⟩ := mem_map.1 hm
            exact Or.inl ⟨γ, hi, rfl⟩
          · exact Or.inr ⟨⟨i, hm⟩, hi, rfl⟩ }
  have hexp : (fun z ↦ signVal (fiberRestrict B emb f b z)) =
      fun z ↦ ∑ W : Finset {i : ι // i ∉ univ.map emb},
        (∑ V : Finset ℬ, boolFourierCoeff h (V.map emb ∪ liftC W) * chi ℝ V b) * chi ℝ W z := by
    ext z
    change signVal (h (mergeInputs emb b z)) = _
    rw [boolFourierExpansion h, ← Equiv.sum_comp hsplit_set, Fintype.sum_prod_type_right]
    refine sum_congr rfl fun W _ ↦ ?_
    rw [sum_mul]
    refine sum_congr rfl fun V _ ↦ ?_
    change boolFourierCoeff h (V.map emb ∪ liftC W) *
      chi ℝ (V.map emb ∪ liftC W) (mergeInputs emb b z) = _
    rw [chi_union (hdisj V W)]
    have hc1 : chi ℝ (V.map emb) (mergeInputs emb b z) = chi ℝ V b := by
      rw [chi_eq_prod_signVal, chi_eq_prod_signVal, prod_map]
      exact prod_congr rfl fun γ _ ↦ by rw [mergeInputs_emb]
    have hc2 : chi ℝ (liftC W) (mergeInputs emb b z) = chi ℝ W z := by
      rw [chi_eq_prod_signVal, chi_eq_prod_signVal]
      change ∏ i ∈ W.map ⟨Subtype.val, Subtype.val_injective⟩, signVal (mergeInputs emb b z i) = _
      rw [prod_map]
      exact prod_congr rfl fun j _ ↦ congr_arg signVal (mergeInputs_compl emb b z j)
    rw [hc1, hc2]
    ring
  change fourierCoeff _ U = _
  rw [hexp, fourierCoeff_sum_mul]
  simp_rw [fourierCoeff_chi, mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  rfl

private theorem parityOn_fiber_iff
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
    {ℬ : Finset (Finset ι)} (emb : ℬ ↪ ι)
    (hB : ∀ γ : ℬ, B (parityVec {emb γ}) = parityVec γ.1)
    (y : ι → Bool) (γ : ℬ) :
    parityOn γ.1 (applyF2Linear (transposeF2Equiv B.symm).toLinearMap y) = y (emb γ) := by
  rw [parityOn_applyF2Linear]
  have hdual : dualParitySet (transposeF2Equiv B.symm).toLinearMap γ.1 = {emb γ} := by
    apply parityVec_injective
    rw [parityVec_dualParitySet, transposeF2Equiv_toLinearMap, transposeF2Linear_transposeF2Linear,
      LinearEquiv.coe_coe, ← hB γ, LinearEquiv.symm_apply_apply]
  rw [hdual, parityOn_singleton]

/-- Canonical fiber representation data for a parity set `Γ`: selects a basis `ℬ ⊆ Γ` of
`paritySpan Γ` and an `𝔽₂`-automorphism `B` sending singleton coordinates to `ℬ`, yielding
for every `b : ℬ → Bool` a Boolean function on a cube of codimension `parityDim Γ`. -/
structure ParityFiberBasis (Γ : Finset (Finset ι)) where
  /-- Selected basis subset `ℬ ⊆ Γ` of `paritySpan Γ`. -/
  basis : Finset (Finset ι)
  /-- `basis` is contained in `Γ`. -/
  basis_subset : basis ⊆ Γ
  /-- `basis` has the same `𝔽₂`-span as `Γ`. -/
  span_eq : paritySpan (basis : Set (Finset ι)) = paritySpan (Γ : Set (Finset ι))
  /-- `basis` is `𝔽₂`-linearly independent. -/
  linearIndep : LinearIndependent (ZMod 2) (fun γ : basis ↦ parityVec γ.1)
  /-- Ambient `𝔽₂`-linear automorphism extending `basis`. -/
  aut : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)
  /-- Coordinate embedding indexing `basis`. -/
  coordEmb : basis ↪ ι
  /-- `aut` maps each singleton `{coordEmb γ}` to `γ`. -/
  aut_coord : ∀ γ : basis, aut (parityVec {coordEmb γ}) = parityVec γ.1

/-- Construct a `ParityFiberBasis` for any finite set of parities `Γ`. -/
noncomputable def mkParityFiberBasis (Γ : Finset (Finset ι)) : ParityFiberBasis Γ := by
  have h1 := exists_basis_subset_of_parityDim Γ
  let ℬ := Classical.choose h1
  have hℬ := Classical.choose_spec h1
  have h2 := exists_linearEquiv_extending_finset hℬ.2.2.2
  let B := Classical.choose h2
  have hB := Classical.choose_spec h2
  let emb := Classical.choose hB
  have hemb := Classical.choose_spec hB
  exact ⟨ℬ, hℬ.1, hℬ.2.2.1, hℬ.2.2.2, B, emb, hemb.1⟩

/-- Index type of free coordinates for a `ParityFiberBasis`. -/
abbrev ParityFiberBasis.FreeCoord {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ) : Type _ :=
  {i : ι // i ∉ univ.map P.coordEmb}

/-- The restricted Boolean function `f|_{(Γ, b)}` represented on the free cube
`P.FreeCoord → Bool`. -/
noncomputable def ParityFiberBasis.restrict {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (f : (ι → Bool) → Bool) (b : P.basis → Bool) : (P.FreeCoord → Bool) → Bool :=
  fiberRestrict P.aut P.coordEmb f b

/-- Bijection between the free cube `P.FreeCoord → Bool` and the affine fiber
`{x : ι → Bool // ∀ γ : P.basis, parityOn γ.1 x = b γ}`. -/
noncomputable def ParityFiberBasis.fiberPoint {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (b : P.basis → Bool) (z : P.FreeCoord → Bool) : ι → Bool :=
  applyF2Linear (transposeF2Equiv P.aut.symm).toLinearMap (mergeInputs P.coordEmb b z)

theorem ParityFiberBasis.restrict_eq {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (f : (ι → Bool) → Bool) (b : P.basis → Bool) (z : P.FreeCoord → Bool) :
    P.restrict f b z = f (P.fiberPoint b z) := by
  unfold restrict fiberRestrict fiberPoint
  rfl

/-- Walsh–Fourier expansion of a parity-fiber restriction `P.restrict f b`. -/
theorem ParityFiberBasis.boolFourierCoeff_restrict {Γ : Finset (Finset ι)}
    (P : ParityFiberBasis Γ) (f : (ι → Bool) → Bool) (b : P.basis → Bool)
    (U : Finset P.FreeCoord) :
    boolFourierCoeff (P.restrict f b) U =
      ∑ V : Finset P.basis,
        boolFourierCoeff (fourierBasisChange P.aut f)
          (V.map P.coordEmb ∪ U.map ⟨Subtype.val, Subtype.val_injective⟩) * chi ℝ V b :=
  boolFourierCoeff_fiberRestrict P.aut P.coordEmb f b U

/-- Every point `x` realizing an assignment `b` on `P.basis` lies in the range of `P.fiberPoint`. -/
theorem ParityFiberBasis.exists_fiberPoint {Γ : Finset (Finset ι)}
    (P : ParityFiberBasis Γ) (b : P.basis → Bool) {x : ι → Bool}
    (hx : ∀ γ : P.basis, parityOn γ.1 x = b γ) :
    ∃ z : P.FreeCoord → Bool, P.fiberPoint b z = x := by
  let E := transposeF2Equiv P.aut.symm
  let y : ι → Bool := applyF2Equiv E.symm x
  have hxy : applyF2Linear E.toLinearMap y = x := by
    change applyF2Equiv E (applyF2Equiv E.symm x) = x
    exact Equiv.apply_symm_apply (applyF2Equiv E) x
  refine ⟨fun j ↦ y j.1, ?_⟩
  unfold fiberPoint; rw [← hxy]; congr 1; ext i
  simp only [mergeInputs]
  split_ifs with hm
  · set γ := Classical.choose (mem_map.1 hm)
    have hγ : P.coordEmb γ = i := (Classical.choose_spec (mem_map.1 hm)).2
    rw [← hγ, ← parityOn_fiber_iff P.aut P.coordEmb P.aut_coord y γ, hxy, hx γ]
  · rfl

theorem ParityFiberBasis.parityOn_fiberPoint {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (b : P.basis → Bool) (z : P.FreeCoord → Bool) (γ : P.basis) :
    parityOn γ.1 (P.fiberPoint b z) = b γ := by
  rw [fiberPoint, parityOn_fiber_iff P.aut P.coordEmb P.aut_coord, mergeInputs_emb]

/-- Every assignment `b : P.basis → Bool` extends uniquely to a consistent assignment
`extAssign P b : Finset ι → Bool` on `Γ` matching `parityOn γ (P.fiberPoint b 0)`. -/
noncomputable def ParityFiberBasis.extAssign {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (b : P.basis → Bool) (γ : Finset ι) : Bool :=
  parityOn γ (P.fiberPoint b 0)

theorem ParityFiberBasis.mem_fiber_iff {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (b : P.basis → Bool) (x : ι → Bool) :
    (∀ γ ∈ Γ, parityOn γ x = P.extAssign b γ) ↔ ∃ z : P.FreeCoord → Bool, P.fiberPoint b z = x := by
  constructor
  · intro hx
    refine P.exists_fiberPoint b fun γ ↦ ?_
    rw [hx γ.1 (P.basis_subset γ.2), extAssign, parityOn_fiberPoint]
  · rintro ⟨z, rfl⟩ γ hγ
    unfold extAssign
    have hmem : parityVec γ ∈ paritySpan (P.basis : Set (Finset ι)) := by
      rw [P.span_eq]; exact mem_paritySpan_of_mem hγ
    have hsame : ∀ v ∈ paritySpan (P.basis : Set (Finset ι)),
        parityOn (parityVecEquiv.symm v) (P.fiberPoint b z) =
          parityOn (parityVecEquiv.symm v) (P.fiberPoint b 0) := by
      intro v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨δ, hδ, rfl⟩
        have hsym : parityVecEquiv.symm (parityVec δ) = δ := parityVecEquiv.symm_apply_apply δ
        rw [hsym, P.parityOn_fiberPoint b z ⟨δ, hδ⟩, P.parityOn_fiberPoint b 0 ⟨δ, hδ⟩]
      · simp [parityVecEquiv_symm_zero]
      · intro u₁ u₂ _ _ h₁ h₂
        rw [parityVecEquiv_symm_add, parityOn_symmDiff, parityOn_symmDiff, h₁, h₂]
      · intro c u _ hu
        rcases ZMod2_eq_zero_or_one c with rfl | rfl
        · simp [parityVecEquiv_symm_zero]
        · rwa [one_smul]
    have hsym : parityVecEquiv.symm (parityVec γ) = γ := parityVecEquiv.symm_apply_apply γ
    simpa [hsym] using hsame (parityVec γ) hmem

/-- `P.restrict f b` is constant iff `f` is constant on the affine fiber `(Γ, P.extAssign b)`. -/
theorem ParityFiberBasis.isConst_restrict_iff {Γ : Finset (Finset ι)} (P : ParityFiberBasis Γ)
    (f : (ι → Bool) → Bool) (b : P.basis → Bool) :
    (∃ v : Bool, ∀ z, P.restrict f b z = v) ↔ IsConstantOnParityFiber f Γ (P.extAssign b) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, fun x hx ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (P.mem_fiber_iff b x).1 hx
    exact hv z
  · rintro ⟨v, hv⟩
    exact ⟨v, fun z ↦ hv (P.fiberPoint b z) ((P.mem_fiber_iff b _).2 ⟨z, rfl⟩)⟩

/-- Expectation of restricted Boolean weight over uniform assignments equals `boolWeight f`. -/
theorem ParityFiberBasis.expect_boolWeight_restrict {Γ : Finset (Finset ι)}
    (P : ParityFiberBasis Γ) (f : (ι → Bool) → Bool) :
    (𝔼 b : P.basis → Bool, boolWeight (P.restrict f b)) = boolWeight f := by
  simp_rw [boolWeight_eq_expect_bitVal]
  let h := fourierBasisChange P.aut f
  have hwt : (𝔼 x : ι → Bool, bitVal ℝ (f x)) = 𝔼 y : ι → Bool, bitVal ℝ (h y) := by
    rw [← boolWeight_eq_expect_bitVal, ← boolWeight_eq_expect_bitVal, boolWeight_fourierBasisChange]
  conv_rhs => rw [hwt]
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  simp_rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, ← sum_mul]
  rw [mul_assoc, ← mul_inv,
    ← Fintype.sum_prod_type (f := fun q : (P.basis → Bool) × (P.FreeCoord → Bool) ↦
      bitVal ℝ (P.restrict f q.1 q.2)),
    ← Equiv.sum_comp (mergeEquiv P.coordEmb)]
  have hcard : Fintype.card (P.FreeCoord → Bool) * Fintype.card (P.basis → Bool) =
      Fintype.card (ι → Bool) := by
    rw [mul_comm, ← Fintype.card_prod];     exact Fintype.card_congr (mergeEquiv P.coordEmb)
  rw [← Nat.cast_mul, hcard]
  rfl

/-- Lower bound on the expected non-empty Fourier sparsity across affine fibers:
if `ℓ = numSupportCosets f Γ ≥ 2`, then `ℓ^2 / (4 * k(f)) ≤ 𝔼_b [k_{∅ᶜ}(f|_b)]`. -/
theorem ParityFiberBasis.le_expect_boolNonemptySparsity_restrict {Γ : Finset (Finset ι)}
    (P : ParityFiberBasis Γ) (f : (ι → Bool) → Bool)
    (hℓ : 2 ≤ numSupportCosets f Γ) :
    (numSupportCosets f Γ : ℝ) ^ 2 / (4 * boolSparsity f) ≤
      𝔼 b : P.basis → Bool, (boolNonemptySparsity (P.restrict f b) : ℝ) := by
  classical
  -- Define the coset projection U ↦ coset of aut (liftC U) in (ι → ZMod 2) ⧸ paritySpan Γ.
  let h := fourierBasisChange P.aut f
  let liftC : Finset P.FreeCoord → Finset ι := fun U ↦ U.map ⟨Subtype.val, Subtype.val_injective⟩
  let cosetPoly : Finset P.FreeCoord → (P.basis → Bool) → ℝ :=
    fun U b ↦ boolFourierCoeff (P.restrict f b) U
  have hpoly_fc : ∀ (U : Finset P.FreeCoord) (V : Finset P.basis),
      fourierCoeff (cosetPoly U) V =
        boolFourierCoeff f
          (parityVecEquiv.symm (P.aut (parityVec (V.map P.coordEmb ∪ liftC U)))) := by
    intro U V
    have hfun : cosetPoly U = fun b ↦
        ∑ W : Finset P.basis, boolFourierCoeff h (W.map P.coordEmb ∪ liftC U) * chi ℝ W b := by
      ext b
      exact boolFourierCoeff_fiberRestrict P.aut P.coordEmb f b U
    rw [hfun, fourierCoeff_sum_mul]
    simp_rw [fourierCoeff_chi, mul_ite, mul_one, mul_zero]
    simp [h, boolFourierCoeff_fourierBasisChange]
  -- Bijection between supportCosets f Γ and active U : Finset P.FreeCoord with cosetPoly U ≠ 0.
  let toCoset : Finset P.FreeCoord → (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι)) :=
    fun U ↦ Submodule.Quotient.mk (P.aut (parityVec (liftC U)))
  have htoCoset_union : ∀ (V : Finset P.basis) (U : Finset P.FreeCoord),
      (Submodule.Quotient.mk (P.aut (parityVec (V.map P.coordEmb ∪ liftC U))) :
        (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = toCoset U := by
    intro V U
    have hdisj : Disjoint (V.map P.coordEmb) (liftC U) := by
      rw [disjoint_left]; intro i hiV hiU
      obtain ⟨γ, _, rfl⟩ := mem_map.1 hiV
      obtain ⟨j, _, hj⟩ := mem_map.1 hiU
      dsimp only [Function.Embedding.coeFn_mk] at hj
      exact j.2 (hj ▸ mem_map_of_mem P.coordEmb (mem_univ γ))
    have hunion : V.map P.coordEmb ∪ liftC U = symmDiff (V.map P.coordEmb) (liftC U) :=
      (Disjoint.symmDiff_eq_sup hdisj).symm
    rw [hunion, parityVec_symmDiff, map_add, Submodule.Quotient.mk_add]
    suffices hv : P.aut (parityVec (V.map P.coordEmb)) ∈ paritySpan (Γ : Set (Finset ι)) by
      rw [(Submodule.Quotient.mk_eq_zero _).2 hv, zero_add]
    rw [← P.span_eq, parityVec_map, map_sum]
    exact Submodule.sum_mem _ fun γ _ ↦ P.aut_coord γ ▸ mem_paritySpan_of_mem γ.2
  have htoCoset_inj : Function.Injective toCoset := by
    intro U₁ U₂ heq
    rw [Submodule.Quotient.eq, ← P.span_eq] at heq
    have hsub : P.aut (parityVec (symmDiff (liftC U₁) (liftC U₂))) ∈
        paritySpan (P.basis : Set (Finset ι)) := by
      rw [parityVec_symmDiff, map_add]
      have : P.aut (parityVec (liftC U₁)) - P.aut (parityVec (liftC U₂)) =
          P.aut (parityVec (liftC U₁)) + P.aut (parityVec (liftC U₂)) := by
        ext i
        simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, CharTwo.neg_eq]
      rwa [← this]
    -- Every element of paritySpan P.basis is P.aut(w) with w supported on univ.map P.coordEmb.
    have hsupp_basis : ∀ v ∈ paritySpan (P.basis : Set (Finset ι)),
        ∀ j : P.FreeCoord, P.aut.symm v j.1 = 0 := by
      intro v hv
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨γ, hγ, rfl⟩ j
        rw [← P.aut_coord ⟨γ, hγ⟩, LinearEquiv.symm_apply_apply, parityVec_of_notMem]
        rw [mem_singleton]
        exact fun heq ↦ j.2 (heq ▸ mem_map_of_mem P.coordEmb (mem_univ (⟨γ, hγ⟩ : P.basis)))
      · intro _; simp
      · intro a b _ _ ha hb j; simp [ha j, hb j]
      · intro c a _ ha j; simp [ha j]
    have hzero := hsupp_basis _ hsub
    simp only [LinearEquiv.symm_apply_apply] at hzero
    ext j
    have hj := hzero j
    simp only [parityVec_apply, mem_symmDiff, liftC, mem_map, Function.Embedding.coeFn_mk,
      Subtype.val_injective.eq_iff, exists_eq_right] at hj
    split_ifs at hj with h
    · exact False.elim (one_ne_zero hj)
    · push Not at h
      exact ⟨h.1, h.2⟩
  let active : Finset (Finset P.FreeCoord) := univ.filter fun U ↦ U ≠ ∅ ∧ cosetPoly U ≠ 0
  -- Each U ∈ active has fourierSparsity (cosetPoly U) equal to the size of its coset in boolSupport
  -- f.
  have hsp_coset : ∀ U : Finset P.FreeCoord,
      fourierSparsity (cosetPoly U) =
        #{S ∈ boolSupport f | (Submodule.Quotient.mk (parityVec S) :
          (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = toCoset U} := by
    intro U
    let φ : Finset P.basis → Finset ι :=
      fun V ↦ parityVecEquiv.symm (P.aut (parityVec (V.map P.coordEmb ∪ liftC U)))
    refine card_bij (fun V _ ↦ φ V) ?_ ?_ ?_
    · intro V hV
      rw [mem_fourierSupport, hpoly_fc] at hV
      refine mem_filter.2 ⟨mem_boolSupport.2 hV, ?_⟩
      change Submodule.Quotient.mk (parityVecEquiv (φ V)) = toCoset U
      simp only [φ, Equiv.apply_symm_apply, htoCoset_union]
    · intro V₁ _ V₂ _ heq
      have h1' := congr_arg parityVecEquiv heq
      simp only [φ, Equiv.apply_symm_apply] at h1'
      have h1 := parityVec_injective (P.aut.injective h1')
      ext γ
      have h2 := Finset.ext_iff.1 h1 (P.coordEmb γ)
      have hnot : P.coordEmb γ ∉ liftC U := by
        simp only [liftC, mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
        intro j _ heq'
        exact j.2 (heq' ▸ mem_map_of_mem P.coordEmb (mem_univ γ))
      simpa [hnot] using h2
    · intro S hS
      obtain ⟨hSs, hSq⟩ := mem_filter.1 hS
      let T : Finset ι := parityVecEquiv.symm (P.aut.symm (parityVec S))
      let V : Finset P.basis := univ.filter fun γ ↦ P.coordEmb γ ∈ T
      let U' : Finset P.FreeCoord := univ.filter fun j ↦ j.1 ∈ T
      have hT_eq : V.map P.coordEmb ∪ liftC U' = T := by
        ext i
        simp only [V, U', mem_union, mem_map, mem_filter, mem_univ, true_and, liftC]
        constructor
        · rintro (⟨γ, hγ, rfl⟩ | ⟨j, hj, rfl⟩) <;> assumption
        · intro hi
          by_cases hm : i ∈ univ.map P.coordEmb
          · obtain ⟨γ, _, rfl⟩ := mem_map.1 hm
            exact Or.inl ⟨γ, hi, rfl⟩
          · exact Or.inr ⟨⟨i, hm⟩, hi, rfl⟩
      have hS_phi : parityVec S = P.aut (parityVec (V.map P.coordEmb ∪ liftC U')) := by
        rw [hT_eq]; change _ = P.aut (parityVecEquiv T); simp [T]
      have hU'_eq : U' = U := htoCoset_inj <| by
        rw [← htoCoset_union V U', ← hS_phi, hSq]
      subst hU'_eq
      refine ⟨V, ?_, ?_⟩
      · rw [mem_fourierSupport, hpoly_fc]
        change boolFourierCoeff f (φ V) ≠ 0
        have hφS : φ V = S := parityVecEquiv.injective (by simp [φ, hS_phi])
        rw [hφS]
        exact mem_boolSupport.1 hSs
      · exact parityVecEquiv.injective (by simp [φ, hS_phi])
  -- Cardinality of active is at least ℓ - 1 (every coset in supportCosets f Γ except possibly 0).
  have hactive_card : numSupportCosets f Γ - 1 ≤ #active := by
    have hsub : (supportCosets f Γ).erase 0 ⊆ active.image toCoset := by
      intro q hq
      obtain ⟨hq0, hqmem⟩ := mem_erase.1 hq
      obtain ⟨S, hSs, rfl⟩ := mem_supportCosets.1 hqmem
      let T : Finset ι := parityVecEquiv.symm (P.aut.symm (parityVec S))
      let V : Finset P.basis := univ.filter fun γ ↦ P.coordEmb γ ∈ T
      let U : Finset P.FreeCoord := univ.filter fun j ↦ j.1 ∈ T
      have hT_eq : V.map P.coordEmb ∪ liftC U = T := by
        ext i
        simp only [V, U, mem_union, mem_map, mem_filter, mem_univ, true_and, liftC]
        constructor
        · rintro (⟨γ, hγ, rfl⟩ | ⟨j, hj, rfl⟩) <;> assumption
        · intro hi
          by_cases hm : i ∈ univ.map P.coordEmb
          · obtain ⟨γ, _, rfl⟩ := mem_map.1 hm
            exact Or.inl ⟨γ, hi, rfl⟩
          · exact Or.inr ⟨⟨i, hm⟩, hi, rfl⟩
      have hSq : (Submodule.Quotient.mk (parityVec S) :
          (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = toCoset U := by
        have hS_eq : parityVec S = P.aut (parityVec (V.map P.coordEmb ∪ liftC U)) := by
          rw [hT_eq]; change _ = P.aut (parityVecEquiv T); simp [T]
        rw [hS_eq, htoCoset_union]
      have hUne : U ≠ ∅ := by
        intro hU0
        apply hq0
        rw [hSq, hU0]
        simp only [toCoset, liftC, map_empty, parityVec_empty, map_zero, Submodule.Quotient.mk_zero]
      have hpoly_ne : cosetPoly U ≠ 0 := by
        intro h0
        have hfc0 : fourierCoeff (cosetPoly U) V = 0 := by simp [h0, fourierCoeff]
        rw [hpoly_fc, hT_eq] at hfc0
        have hTsym : parityVecEquiv.symm (P.aut (parityVec T)) = S := by
          change parityVecEquiv.symm (P.aut (parityVecEquiv T)) = S
          simp only [T, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          exact parityVecEquiv.symm_apply_apply S
        rw [hTsym] at hfc0
        exact mem_boolSupport.1 hSs hfc0
      exact mem_image.2 ⟨U, mem_filter.2 ⟨mem_univ _, hUne, hpoly_ne⟩, hSq.symm⟩
    calc numSupportCosets f Γ - 1 ≤ #((supportCosets f Γ).erase 0) := pred_card_le_card_erase
      _ ≤ #(active.image toCoset) := card_le_card hsub
      _ = #active := card_image_of_injective _ htoCoset_inj
  -- Sum of coset sparsities over active is at most boolSparsity f.
  have hsum_sp : (∑ U ∈ active, (fourierSparsity (cosetPoly U) : ℝ)) ≤ boolSparsity f := by
    have hnat : ∑ U ∈ active, fourierSparsity (cosetPoly U) ≤ boolSparsity f := by
      simp_rw [hsp_coset]
      rw [← sum_image (f := fun q ↦ #{S ∈ boolSupport f |
          (Submodule.Quotient.mk (parityVec S) :
            (ι → ZMod 2) ⧸ paritySpan (Γ : Set (Finset ι))) = q})
        (fun a _ b _ h ↦ htoCoset_inj h), ← sum_card_supportCoset_eq_boolSparsity f Γ]
      refine sum_le_sum_of_subset fun q hq ↦ ?_
      obtain ⟨U, hU, rfl⟩ := mem_image.1 hq
      have hne : cosetPoly U ≠ 0 := (mem_filter.1 hU).2.2
      have hpos : 0 < fourierSparsity (cosetPoly U) := fourierSparsity_pos_of_ne_zero hne
      rw [hsp_coset, card_pos] at hpos
      obtain ⟨S, hS⟩ := hpos
      exact mem_supportCosets.2 ⟨S, (mem_filter.1 hS).1, (mem_filter.1 hS).2⟩
    exact_mod_cast hnat
  -- Linearity of expectation + uncertainty principle + Cauchy–Schwarz!
  have hexp_eq : (𝔼 b : P.basis → Bool, (boolNonemptySparsity (P.restrict f b) : ℝ)) =
      ∑ U ∈ active, (dens {b : P.basis → Bool | cosetPoly U b ≠ 0} : ℝ) := by
    have hpt : ∀ b : P.basis → Bool,
        (boolNonemptySparsity (P.restrict f b) : ℝ) =
          ∑ U ∈ active, if cosetPoly U b ≠ 0 then (1 : ℝ) else 0 := by
      intro b
      rw [← card_erase_empty_boolSupport]
      have hset : (boolSupport (P.restrict f b)).erase ∅ =
          active.filter fun U ↦ cosetPoly U b ≠ 0 := by
        ext U
        simp only [mem_erase, mem_boolSupport, mem_filter, active, mem_univ, true_and, cosetPoly]
        constructor
        · rintro ⟨hne, hfc⟩
          exact ⟨⟨hne, fun h0 ↦ hfc (congr_fun h0 b)⟩, hfc⟩
        · rintro ⟨⟨hne, _⟩, hfc⟩
          exact ⟨hne, hfc⟩
      rw [hset, sum_boole]
    simp_rw [hpt]
    rw [expect_sum_comm]
    refine sum_congr rfl fun U _ ↦ ?_
    rw [Fintype.expect_eq_sum_div_card, sum_boole, nnratCast_dens]
  rw [hexp_eq]
  have hsum_inv : ∑ U ∈ active, (1 : ℝ) / fourierSparsity (cosetPoly U) ≤
      ∑ U ∈ active, (dens {b : P.basis → Bool | cosetPoly U b ≠ 0} : ℝ) :=
    sum_le_sum fun U hU ↦ uncertainty_principle (mem_filter.1 hU).2.2
  refine le_trans ?_ hsum_inv
  have hcs : (#active : ℝ) ^ 2 ≤
      (∑ U ∈ active, (1 : ℝ) / fourierSparsity (cosetPoly U)) *
        (∑ U ∈ active, (fourierSparsity (cosetPoly U) : ℝ)) := by
    have hterm : ∀ U ∈ active, (1 : ℝ) =
        Real.sqrt (1 / fourierSparsity (cosetPoly U)) *
          Real.sqrt (fourierSparsity (cosetPoly U)) := by
      intro U hU
      have hp : (0 : ℝ) < fourierSparsity (cosetPoly U) :=
        Nat.cast_pos.2 (fourierSparsity_pos_of_ne_zero (mem_filter.1 hU).2.2)
      rw [← Real.sqrt_mul (by positivity), one_div_mul_cancel hp.ne', Real.sqrt_one]
    have h1 : (#active : ℝ) = ∑ U ∈ active,
        Real.sqrt (1 / fourierSparsity (cosetPoly U)) *
          Real.sqrt (fourierSparsity (cosetPoly U)) := by
      calc (#active : ℝ) = ∑ _ ∈ active, (1 : ℝ) := by simp
        _ = _ := sum_congr rfl hterm
    rw [h1]
    refine (sum_mul_sq_le_sq_mul_sq active _ _).trans_eq ?_
    congr 1 <;> refine sum_congr rfl fun U _ ↦ Real.sq_sqrt (by positivity)
  have hsp_pos : (0 : ℝ) < boolSparsity f := Nat.cast_pos.2 (boolSparsity_pos f)
  have hℓ_sub : (numSupportCosets f Γ : ℝ) / 2 ≤ #active := by
    have h1 : ((numSupportCosets f Γ - 1 : ℕ) : ℝ) ≤ #active := by exact_mod_cast hactive_card
    have h2 : (2 : ℝ) ≤ numSupportCosets f Γ := by exact_mod_cast hℓ
    rw [Nat.cast_sub (by omega), Nat.cast_one] at h1
    linarith
  have hact_sq : (numSupportCosets f Γ : ℝ) ^ 2 / 4 ≤ (#active : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hℓ_sub 2
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc (numSupportCosets f Γ : ℝ) ^ 2
      ≤ 4 * (#active : ℝ) ^ 2 := by linarith
    _ ≤ 4 * ((∑ U ∈ active, (1 : ℝ) / fourierSparsity (cosetPoly U)) *
          (∑ U ∈ active, (fourierSparsity (cosetPoly U) : ℝ))) := by linarith
    _ ≤ 4 * ((∑ U ∈ active, (1 : ℝ) / fourierSparsity (cosetPoly U)) * boolSparsity f) := by
        gcongr
    _ = (∑ U ∈ active, (1 : ℝ) / fourierSparsity (cosetPoly U)) * (4 * boolSparsity f) := by ring

end ParityFibersAndSanyal

end CslibFrontier.BooleanFunction
