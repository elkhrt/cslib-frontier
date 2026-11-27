/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Analysis.Fourier.FiniteProduct

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Efron–Stein Decomposition, Noise Operators, and Coordinate Influences

This module develops the Efron–Stein orthogonal decomposition, degree truncations, level and tail
Fourier weights, the Bonami–Beckner noise operator `T_ρ`, junta-averaging tail bounds, and
coordinate influences on finite weighted product spaces `(ι → A, ν^⊗ι)` under standard Lean axioms.

## Main definitions

* `CslibFrontier.Analysis.Fourier.efronProj`, `degPart`, `levelPart`, `levelWeight`, `tailWeight`:
  Efron–Stein projections `f^{=S}`, degree-`≤ d` truncation `f^{≤ d}`, pure degree parts `f^{=d}`,
  level weights `W^{=d}`, and tail weights `W^{≥ d}`.
* `CslibFrontier.Analysis.Fourier.subsetProb`, `noiseOp`:
  Bernoulli subset probability `I ⊆_ε ι` and noise operator `T_ρ`.
* `CslibFrontier.Analysis.Fourier.coordInf`, `degCoordInf`:
  coordinate influence `I_i[f]` and degree-`d` influence `I_i^{≤ d}[f]`.

## Main results

* `CslibFrontier.Analysis.Fourier.sum_efronProj`: Efron–Stein decomposition `f = ∑_S f^{=S}`.
* `CslibFrontier.Analysis.Fourier.piInner_efronProj_eq_zero`: orthogonality of Efron–Stein parts.
* `CslibFrontier.Analysis.Fourier.parseval_efronProj`: Parseval identity `‖f‖₂² = ∑_S ‖f^{=S}‖₂²`.
* `CslibFrontier.Analysis.Fourier.mem_degSubspace_iff`: characterization of `V_{≤ d}` by vanishing
  high-degree Efron–Stein projections.
* `CslibFrontier.Analysis.Fourier.noiseOp_efronProj`: `T_ρ f^{=S} = ρ^{|S|} f^{=S}`.
* `CslibFrontier.Analysis.Fourier.tailWeight_avg_of_juntas_le`: averaging `Iᶜ`-juntas over `I ⊆_ε ι`
  gives `W^{≥ d}[f] ≤ (1 - ε)^d B`.
* `CslibFrontier.Analysis.Fourier.coordInf_eq_two_mul_sum_efronProj`:
  `I_i[f] = 2 ∑_{S ∋ i} ‖f^{=S}‖₂²`.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Analysis.Fourier

section EfronStein

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Efron–Stein projection onto subset `S : Finset ι` via inclusion–exclusion:
`f^{=S} = ∑_{J ⊆ S} (-1)^{|S| - |J|} T_{Jᶜ} f`. -/
@[expose] noncomputable def efronProj (ν : PMF A) (S : Finset ι)
    (f : (ι → A) → ℂ) (x : ι → A) : ℂ :=
  ∑ J ∈ S.powerset, ((-1 : ℂ) ^ (S.card - J.card)) * subsetResampleOp ν Jᶜ f x

/-- Degree-`≤ d` truncation `f^{≤ d} = ∑_{|S| ≤ d} f^{=S}`. -/
@[expose] noncomputable def degPart (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) (x : ι → A) : ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d), efronProj ν S f x

/-- Pure degree-`d` part `f^{=d} = ∑_{|S| = d} f^{=S}`. -/
@[expose] noncomputable def levelPart (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) (x : ι → A) : ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card = d), efronProj ν S f x

/-- Level-`d` Fourier weight `W^{=d}[f] = ∑_{|S| = d} ‖f^{=S}‖₂²`. -/
@[expose] noncomputable def levelWeight (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card = d), l2NormSq ν (efronProj ν S f)

/-- Tail Fourier weight `W^{≥ d}[f] = ∑_{|S| ≥ d} ‖f^{=S}‖₂²`. -/
@[expose] noncomputable def tailWeight (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ d ≤ S.card), l2NormSq ν (efronProj ν S f)

@[simp]
lemma efronProj_zero (ν : PMF A) (S : Finset ι) : efronProj ν S (0 : (ι → A) → ℂ) = 0 := by
  ext x; unfold efronProj; simp [subsetResampleOp_zero]

lemma efronProj_add (ν : PMF A) (S : Finset ι) (f g : (ι → A) → ℂ) :
    efronProj ν S (f + g) = efronProj ν S f + efronProj ν S g := by
  ext x
  unfold efronProj
  simp only [Pi.add_apply, subsetResampleOp_add, mul_add, Finset.sum_add_distrib]

lemma efronProj_sub (ν : PMF A) (S : Finset ι) (f g : (ι → A) → ℂ) :
    efronProj ν S (f - g) = efronProj ν S f - efronProj ν S g := by
  ext x
  unfold efronProj
  simp only [Pi.sub_apply, subsetResampleOp_sub, mul_sub, Finset.sum_sub_distrib]

lemma efronProj_smul (ν : PMF A) (S : Finset ι) (c : ℂ) (f : (ι → A) → ℂ) :
    efronProj ν S (fun x ↦ c * f x) = fun x ↦ c * efronProj ν S f x := by
  ext x
  unfold efronProj
  simp_rw [subsetResampleOp_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ ↦ ?_
  ring

lemma efronProj_sum {κ : Type*} (ν : PMF A) (S : Finset ι) (s : Finset κ) (f : κ → (ι → A) → ℂ) :
    efronProj ν S (fun x ↦ ∑ k ∈ s, f k x) = fun x ↦ ∑ k ∈ s, efronProj ν S (f k) x := by
  ext x
  unfold efronProj
  simp_rw [subsetResampleOp_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `f^{=S}` is always an `S`-junta. -/
lemma efronProj_isJunta (ν : PMF A) (S : Finset ι) (f : (ι → A) → ℂ) :
    IsJunta S (efronProj ν S f) := by
  refine isJunta_sum S.powerset fun J hJ ↦ ?_
  refine isJunta_smul _ ?_
  have hsub : J ⊆ S := Finset.mem_powerset.mp hJ
  have hJ' : IsJunta Jᶜᶜ (subsetResampleOp ν Jᶜ f) := subsetResampleOp_isJunta ν Jᶜ f
  rw [compl_compl] at hJ'
  exact isJunta_mono hsub hJ'

/-- Resampling any coordinate `i ∈ S` annihilates `f^{=S}`: `T_I (f^{=S}) = 0` when `I ∩ S ≠ ∅`. -/
lemma subsetResampleOp_efronProj_eq_zero (ν : PMF A) {I S : Finset ι} (hIS : (I ∩ S).Nonempty)
    (f : (ι → A) → ℂ) : subsetResampleOp ν I (efronProj ν S f) = 0 := by
  obtain ⟨i, hi⟩ := hIS
  have hiI : i ∈ I := (Finset.mem_inter.mp hi).1
  have hiS : i ∈ S := (Finset.mem_inter.mp hi).2
  have h1 : subsetResampleOp ν I (efronProj ν S f) =
      subsetResampleOp ν I (subsetResampleOp ν {i} (efronProj ν S f)) := by
    rw [subsetResampleOp_comp]
    have : I ∪ {i} = I := Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hiI)
    rw [this]
  rw [h1]
  suffices h0 : subsetResampleOp ν {i} (efronProj ν S f) = 0 by
    rw [h0, subsetResampleOp_zero]
  ext x
  unfold efronProj
  rw [subsetResampleOp_sum]
  simp_rw [subsetResampleOp_smul, subsetResampleOp_comp]
  -- Pair each `J ⊆ S \ {i}` with `insert i J`!
  let T := (S.erase i).powerset
  have hpart : S.powerset = T ∪ T.image (insert i) := by
    ext J
    simp only [T, Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hJS
      by_cases hiJ : i ∈ J
      · right; refine ⟨J.erase i, ?_, Finset.insert_erase hiJ⟩
        exact Finset.erase_subset_erase i hJS
      · left; exact Finset.subset_erase.mpr ⟨hJS, hiJ⟩
    · rintro (h | ⟨K, hK, rfl⟩)
      · exact h.trans (Finset.erase_subset i S)
      · exact Finset.insert_subset hiS (hK.trans (Finset.erase_subset i S))
  have hdisj : Disjoint T (T.image (insert i)) := by
    rw [Finset.disjoint_left]
    intro J hJT hJimg
    simp only [T, Finset.mem_powerset, Finset.mem_image] at hJT hJimg
    obtain ⟨K, _, rfl⟩ := hJimg
    exact (Finset.subset_erase.mp hJT).2 (Finset.mem_insert_self i K)
  rw [hpart, Finset.sum_union hdisj, Finset.sum_image]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun J hJT ↦ ?_
    have hJS : J ⊆ S := (Finset.mem_powerset.mp hJT).trans (Finset.erase_subset i S)
    have hiJ : i ∉ J := (Finset.subset_erase.mp (Finset.mem_powerset.mp hJT)).2
    have hunion : {i} ∪ Jᶜ = Jᶜ :=
      Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hiJ))
    have hunion2 : {i} ∪ (insert i J)ᶜ = Jᶜ := by
      ext j; by_cases hj : j = i <;> simp [hj, hiJ]
    rw [hunion, hunion2, Finset.card_insert_of_notMem hiJ]
    have hlt : J.card + 1 ≤ S.card := by
      have := Finset.card_le_card (Finset.insert_subset hiS hJS)
      rwa [Finset.card_insert_of_notMem hiJ] at this
    have hpow : (-1 : ℂ) ^ (S.card - J.card) = -((-1 : ℂ) ^ (S.card - (J.card + 1))) := by
      have heq : S.card - J.card = (S.card - (J.card + 1)) + 1 := by omega
      rw [heq, pow_succ]; ring
    rw [hpow]; ring
  · intro A hA B hB hAB
    have hiA : i ∉ A := (Finset.subset_erase.mp (Finset.mem_powerset.mp hA)).2
    have hiB : i ∉ B := (Finset.subset_erase.mp (Finset.mem_powerset.mp hB)).2
    have := congr_arg (fun s ↦ s.erase i) hAB
    simpa [Finset.erase_insert hiA, Finset.erase_insert hiB] using this

/-- Resampling outside `S` preserves `f^{=S}`: `T_I (f^{=S}) = f^{=S}` when `Disjoint I S`. -/
lemma subsetResampleOp_efronProj_of_disjoint (ν : PMF A) {I S : Finset ι} (hIS : Disjoint I S)
    (f : (ι → A) → ℂ) : subsetResampleOp ν I (efronProj ν S f) = efronProj ν S f :=
  subsetResampleOp_of_isJunta ν
    (isJunta_mono (Finset.subset_compl_iff_disjoint_left.mpr hIS) (efronProj_isJunta ν S f))

/-- `T_I` commutes with `efronProj`: `T_I (f^{=S}) = (T_I f)^{=S}` (and equals `f^{=S}` if
`Disjoint I S`, `0` otherwise). -/
lemma efronProj_subsetResampleOp (ν : PMF A) (I S : Finset ι) (f : (ι → A) → ℂ) :
    efronProj ν S (subsetResampleOp ν I f) =
      if Disjoint I S then efronProj ν S f else 0 := by
  have hcomm : efronProj ν S (subsetResampleOp ν I f) = subsetResampleOp ν I (efronProj ν S f) := by
    ext x
    unfold efronProj
    rw [subsetResampleOp_sum]
    refine Finset.sum_congr rfl fun J _ ↦ ?_
    rw [subsetResampleOp_smul, subsetResampleOp_comp, subsetResampleOp_comp, Finset.union_comm]
  rw [hcomm]
  split_ifs with h
  · exact subsetResampleOp_efronProj_of_disjoint ν h f
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨i, hiI, hiS⟩ := h
    exact subsetResampleOp_efronProj_eq_zero ν ⟨i, Finset.mem_inter.mpr ⟨hiI, hiS⟩⟩ f

/-- If `f` is a `J`-junta and `¬ S ⊆ J`, then `f^{=S} = 0`. -/
lemma efronProj_eq_zero_of_isJunta (ν : PMF A) {J S : Finset ι} {f : (ι → A) → ℂ}
    (hf : IsJunta J f) (hSJ : ¬ S ⊆ J) : efronProj ν S f = 0 := by
  have hJ : subsetResampleOp ν Jᶜ f = f := by
    apply subsetResampleOp_of_isJunta; rwa [compl_compl]
  rw [← hJ, efronProj_subsetResampleOp]
  have hnd : ¬ Disjoint Jᶜ S := by
    intro hd
    exact hSJ (Finset.compl_subset_compl.mp (Finset.subset_compl_iff_disjoint_right.mpr hd))
  simp [hnd]

/-- Möbius inversion / Efron–Stein decomposition: `∑_{S ⊆ J} f^{=S} = T_{Jᶜ} f`. -/
lemma sum_efronProj_powerset (ν : PMF A) (J : Finset ι) (f : (ι → A) → ℂ) (x : ι → A) :
    ∑ S ∈ J.powerset, efronProj ν S f x = subsetResampleOp ν Jᶜ f x := by
  unfold efronProj
  rw [Finset.sum_sigma']
  have hswap : (∑ p ∈ J.powerset.sigma Finset.powerset,
      (-1 : ℂ) ^ (p.1.card - p.2.card) * subsetResampleOp ν p.2ᶜ f x) =
      ∑ K ∈ J.powerset, (∑ S ∈ J.powerset.filter (fun S ↦ K ⊆ S),
        (-1 : ℂ) ^ (S.card - K.card)) * subsetResampleOp ν Kᶜ f x := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij (fun p ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hp ⊢
      exact ⟨hp.2.trans hp.1, hp.1, hp.2⟩
    · intro p₁ _ p₂ _ h
      cases p₁; cases p₂; simp only [Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h2⟩ := h; cases eq_of_heq h2; rfl
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powerset, Finset.mem_filter] at hq
      refine ⟨⟨q.2, q.1⟩, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powerset]
      exact ⟨hq.2.1, hq.2.2⟩
    · intro _ _; rfl
  rw [hswap]
  rw [Finset.sum_eq_single J]
  · have hfilt : J.powerset.filter (fun S ↦ J ⊆ S) = {J} := by
      ext S; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      exact ⟨fun ⟨h1, h2⟩ ↦ Finset.Subset.antisymm h1 h2, fun h ↦ h ▸ ⟨Subset.rfl, Subset.rfl⟩⟩
    rw [hfilt, Finset.sum_singleton, Nat.sub_self, pow_zero, one_mul]
  · intro K hKJ hne
    have hlt : K ⊂ J := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hKJ, hne⟩
    -- Biject `S ∈ J.powerset` with `K ⊆ S` against `L ⊆ J \ K` via `L ↦ K ∪ L`.
    have hsum0 : ∑ S ∈ J.powerset.filter (fun S ↦ K ⊆ S), (-1 : ℂ) ^ (S.card - K.card) = 0 := by
      have hbij : ∑ S ∈ J.powerset.filter (fun S ↦ K ⊆ S), (-1 : ℂ) ^ (S.card - K.card) =
          ∑ L ∈ (J \ K).powerset, (-1 : ℂ) ^ L.card := by
        refine Finset.sum_nbij (fun S ↦ S \ K) ?_ ?_ ?_ ?_
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
          exact Finset.sdiff_subset_sdiff hS.1 Subset.rfl
        · intro S₁ hS₁ S₂ hS₂ h
          dsimp only at h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
          rw [← Finset.union_sdiff_of_subset hS₁.2, ← Finset.union_sdiff_of_subset hS₂.2, h]
        · intro L hL
          simp only [Finset.mem_coe, Finset.mem_powerset] at hL
          refine ⟨K ∪ L, ?_, ?_⟩
          · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.union_subset hlt.subset (hL.trans Finset.sdiff_subset),
              Finset.subset_union_left⟩
          · have hdisj : Disjoint K L :=
              Disjoint.mono_right hL disjoint_sdiff_self_right
            exact Finset.union_sdiff_cancel_left hdisj
        · intro S hS
          simp only [Finset.mem_filter] at hS
          rw [Finset.card_sdiff_of_subset hS.2]
      rw [hbij]
      have hne' : (J \ K).Nonempty := Finset.sdiff_nonempty.mpr (not_subset.mpr <| by
        obtain ⟨a, haJ, haK⟩ := Finset.exists_of_ssubset hlt; exact ⟨a, haJ, haK⟩)
      -- Direct elementary proof via `neg_one_pow_card` on nonempty finset `J \ K`.
      obtain ⟨a, ha⟩ := hne'
      let U := ((J \ K).erase a).powerset
      have hp : (J \ K).powerset = U ∪ U.image (insert a) := by
        ext L; simp only [U, Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
        constructor
        · intro hL
          by_cases haL : a ∈ L
          · right; exact ⟨L.erase a, Finset.erase_subset_erase a hL, Finset.insert_erase haL⟩
          · left; exact Finset.subset_erase.mpr ⟨hL, haL⟩
        · rintro (h | ⟨M, hM, rfl⟩)
          · exact h.trans (Finset.erase_subset a _)
          · exact Finset.insert_subset ha (hM.trans (Finset.erase_subset a _))
      have hd : Disjoint U (U.image (insert a)) := by
        rw [Finset.disjoint_left]; intro L hLU hLi
        simp only [U, Finset.mem_powerset, Finset.mem_image] at hLU hLi
        obtain ⟨M, _, rfl⟩ := hLi
        exact (Finset.subset_erase.mp hLU).2 (Finset.mem_insert_self a M)
      rw [hp, Finset.sum_union hd, Finset.sum_image]
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun L hL ↦ ?_
        have haL : a ∉ L := (Finset.subset_erase.mp (Finset.mem_powerset.mp hL)).2
        rw [Finset.card_insert_of_notMem haL, pow_succ]; ring
      · intro M₁ hM₁ M₂ hM₂ h
        have ha1 : a ∉ M₁ := (Finset.subset_erase.mp (Finset.mem_powerset.mp hM₁)).2
        have ha2 : a ∉ M₂ := (Finset.subset_erase.mp (Finset.mem_powerset.mp hM₂)).2
        have := congr_arg (fun s ↦ s.erase a) h
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
    rw [hsum0, zero_mul]
  · intro hJ; exact absurd (Finset.mem_powerset.mpr Subset.rfl) hJ

/-- Full Efron–Stein decomposition: `f(x) = ∑_{S : Finset ι} f^{=S}(x)`. -/
theorem sum_efronProj (ν : PMF A) (f : (ι → A) → ℂ) (x : ι → A) :
    ∑ S : Finset ι, efronProj ν S f x = f x := by
  have h := sum_efronProj_powerset ν Finset.univ f x
  rw [Finset.powerset_univ, compl_univ, subsetResampleOp_empty] at h
  exact h

/-- Orthogonality of Efron–Stein projections: `⟨f^{=S}, g^{=T}⟩ = 0` for `S ≠ T`. -/
theorem piInner_efronProj_eq_zero (ν : PMF A) {S T : Finset ι} (hST : S ≠ T)
    (f g : (ι → A) → ℂ) : piInner ν (efronProj ν S f) (efronProj ν T g) = 0 := by
  have hex : (∃ i, i ∈ S ∧ i ∉ T) ∨ (∃ i, i ∈ T ∧ i ∉ S) := by
    by_contra h
    push Not at h
    exact hST (Finset.Subset.antisymm h.1 h.2)
  rcases hex with ⟨i, hiS, hiT⟩ | ⟨i, hiT, hiS⟩
  · have hT : subsetResampleOp ν {i} (efronProj ν T g) = efronProj ν T g :=
      subsetResampleOp_efronProj_of_disjoint ν (Finset.disjoint_singleton_left.mpr hiT) g
    have hS : subsetResampleOp ν {i} (efronProj ν S f) = 0 :=
      subsetResampleOp_efronProj_eq_zero ν
        ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, hiS⟩⟩ f
    rw [← hT, ← piInner_subsetResampleOp_left, hS, piInner_zero_left]
  · have hS : subsetResampleOp ν {i} (efronProj ν S f) = efronProj ν S f :=
      subsetResampleOp_efronProj_of_disjoint ν (Finset.disjoint_singleton_left.mpr hiS) f
    have hT : subsetResampleOp ν {i} (efronProj ν T g) = 0 :=
      subsetResampleOp_efronProj_eq_zero ν
        ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, hiT⟩⟩ g
    rw [← hS, piInner_subsetResampleOp_left, hT, piInner_zero_right]

/-- Parseval identity for the Efron–Stein decomposition: `‖f‖₂² = ∑_S ‖f^{=S}‖₂²`. -/
theorem parseval_efronProj (ν : PMF A) (f : (ι → A) → ℂ) :
    l2NormSq ν f = ∑ S : Finset ι, l2NormSq ν (efronProj ν S f) := by
  have hfun : f = fun x ↦ ∑ S : Finset ι, efronProj ν S f x := by
    ext x; exact (sum_efronProj ν f x).symm
  conv_lhs => rw [hfun]
  exact l2NormSq_sum_of_pairwise_orth ν Finset.univ (fun S ↦ efronProj ν S f)
    fun S _ T _ hST ↦ piInner_efronProj_eq_zero ν hST f f

/-- `l2NormSq ν (f^{=S}) ≤ l2NormSq ν f`. -/
lemma l2NormSq_efronProj_le (ν : PMF A) (S : Finset ι) (f : (ι → A) → ℂ) :
    l2NormSq ν (efronProj ν S f) ≤ l2NormSq ν f := by
  conv_rhs => rw [parseval_efronProj]
  exact Finset.single_le_sum (fun T _ ↦ l2NormSq_nonneg ν (efronProj ν T f)) (Finset.mem_univ S)

/-- `f^{=S}` is idempotent: `(f^{=S})^{=S} = f^{=S}` and `(f^{=S})^{=T} = 0` for `T ≠ S`. -/
lemma efronProj_efronProj (ν : PMF A) (S T : Finset ι) (f : (ι → A) → ℂ) :
    efronProj ν T (efronProj ν S f) = if T = S then efronProj ν S f else 0 := by
  ext x
  unfold efronProj
  -- Actually simpler via `efronProj_subsetResampleOp`? Even cleaner: expand `efronProj ν T`!
  change ∑ J ∈ T.powerset, (-1 : ℂ) ^ (T.card - J.card) *
      subsetResampleOp ν Jᶜ (efronProj ν S f) x = _
  have hterm : ∀ J ∈ T.powerset, subsetResampleOp ν Jᶜ (efronProj ν S f) =
      if S ⊆ J then efronProj ν S f else 0 := by
    intro J _
    by_cases hSJ : S ⊆ J
    · simp only [hSJ, ↓reduceIte]
      exact subsetResampleOp_efronProj_of_disjoint ν
        (Finset.disjoint_left.mpr fun i hi hiS ↦ (Finset.mem_compl.mp hi) (hSJ hiS)) f
    · simp only [hSJ, ↓reduceIte]
      have hne : (Jᶜ ∩ S).Nonempty := by
        obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hSJ
        exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hiJ, hiS⟩⟩
      exact subsetResampleOp_efronProj_eq_zero ν hne f
  rw [Finset.sum_congr rfl fun J hJ ↦ by rw [hterm J hJ]]
  by_cases hTS : T = S
  · subst hTS
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single T]
    · simp only [Subset.rfl, ↓reduceIte, Nat.sub_self, pow_zero, one_mul]; rfl
    · intro J hJT hne
      have hnd : ¬ T ⊆ J := fun h ↦ hne (Finset.Subset.antisymm (Finset.mem_powerset.mp hJT) h)
      simp [hnd]
    · intro h; exact absurd (Finset.mem_powerset.mpr Subset.rfl) h
  · simp only [hTS, ↓reduceIte]
    by_cases hST : S ⊆ T
    · have hlt : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, Ne.symm hTS⟩
      have h1 : (∑ J ∈ T.powerset, (-1 : ℂ) ^ (T.card - J.card) *
          (if S ⊆ J then efronProj ν S f else 0) x) =
          (∑ J ∈ T.powerset.filter (fun J ↦ S ⊆ J), (-1 : ℂ) ^ (T.card - J.card)) *
            efronProj ν S f x := by
        rw [Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun J _ ↦ by
          by_cases h : S ⊆ J <;> simp [h]
      rw [h1]
      -- Sum over `S ⊆ J ⊆ T` of `(-1)^{|T| - |J|} = 0` since `S ⊂ T`.
      have hzero : ∑ J ∈ T.powerset.filter (fun J ↦ S ⊆ J), (-1 : ℂ) ^ (T.card - J.card) = 0 := by
        have hbij : ∑ J ∈ T.powerset.filter (fun J ↦ S ⊆ J), (-1 : ℂ) ^ (T.card - J.card) =
            ∑ K ∈ (T \ S).powerset, (-1 : ℂ) ^ K.card := by
          refine Finset.sum_nbij (fun J ↦ T \ J) ?_ ?_ ?_ ?_
          · intro J hJ
            simp only [Finset.mem_filter, Finset.mem_powerset] at hJ ⊢
            exact Finset.sdiff_subset_sdiff Subset.rfl hJ.2
          · intro J₁ hJ₁ J₂ hJ₂ h
            dsimp only at h
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hJ₁ hJ₂
            have h1' : J₁ = T \ (T \ J₁) := (Finset.sdiff_sdiff_eq_self hJ₁.1).symm
            have h2' : J₂ = T \ (T \ J₂) := (Finset.sdiff_sdiff_eq_self hJ₂.1).symm
            rw [h1', h2', h]
          · intro K hK
            simp only [Finset.mem_coe, Finset.mem_powerset] at hK
            refine ⟨T \ K, ?_, ?_⟩
            · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
              refine ⟨Finset.sdiff_subset, ?_⟩
              intro a haS
              exact Finset.mem_sdiff.mpr ⟨hST haS, fun haK ↦ (Finset.mem_sdiff.mp (hK haK)).2 haS⟩
            · exact Finset.sdiff_sdiff_eq_self (hK.trans Finset.sdiff_subset)
          · intro J hJ
            simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
            rw [Finset.card_sdiff_of_subset hJ.1]
        rw [hbij]
        obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr (not_subset.mpr <| by
          obtain ⟨a, haT, haS⟩ := Finset.exists_of_ssubset hlt; exact ⟨a, haT, haS⟩)
        let U := ((T \ S).erase a).powerset
        have hp : (T \ S).powerset = U ∪ U.image (insert a) := by
          ext K; simp only [U, Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
          constructor
          · intro hK
            by_cases haK : a ∈ K
            · right; exact ⟨K.erase a, Finset.erase_subset_erase a hK, Finset.insert_erase haK⟩
            · left; exact Finset.subset_erase.mpr ⟨hK, haK⟩
          · rintro (h | ⟨L, hL, rfl⟩)
            · exact h.trans (Finset.erase_subset a _)
            · exact Finset.insert_subset ha (hL.trans (Finset.erase_subset a _))
        have hd : Disjoint U (U.image (insert a)) := by
          rw [Finset.disjoint_left]; intro K hKU hKi
          simp only [U, Finset.mem_powerset, Finset.mem_image] at hKU hKi
          obtain ⟨L, _, rfl⟩ := hKi
          exact (Finset.subset_erase.mp hKU).2 (Finset.mem_insert_self a L)
        rw [hp, Finset.sum_union hd, Finset.sum_image]
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_eq_zero fun K hK ↦ ?_
          have haK : a ∉ K := (Finset.subset_erase.mp (Finset.mem_powerset.mp hK)).2
          rw [Finset.card_insert_of_notMem haK, pow_succ]; ring
        · intro L₁ hL₁ L₂ hL₂ h
          have ha1 : a ∉ L₁ := (Finset.subset_erase.mp (Finset.mem_powerset.mp hL₁)).2
          have ha2 : a ∉ L₂ := (Finset.subset_erase.mp (Finset.mem_powerset.mp hL₂)).2
          have := congr_arg (fun s ↦ s.erase a) h
          simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [hzero, zero_mul]; rfl
    · refine Finset.sum_eq_zero fun J hJT ↦ ?_
      have hnd : ¬ S ⊆ J := fun h ↦ hST (h.trans (Finset.mem_powerset.mp hJT))
      simp [hnd]

/-- `f ∈ degSubspace d` iff `f^{=S} = 0` for all `|S| > d`. -/
theorem mem_degSubspace_iff (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) :
    f ∈ degSubspace d ↔ ∀ S : Finset ι, d < S.card → efronProj ν S f = 0 := by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨I, hI, hg⟩ S hS
      have hSI : ¬ S ⊆ I := fun h ↦ absurd (Finset.card_le_card h) (not_le.mpr (hI.trans_lt hS))
      exact efronProj_eq_zero_of_isJunta ν hg hSI
    · intro S _
      exact efronProj_zero ν S
    · intro g₁ g₂ _ _ ih₁ ih₂ S hS
      rw [efronProj_add, ih₁ S hS, ih₂ S hS, add_zero]
    · intro c g _ ih S hS
      change efronProj ν S (fun x ↦ c * g x) = 0
      rw [efronProj_smul, ih S hS]; ext x; simp
  · intro h
    have hfun : f = ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
        efronProj ν S f := by
      ext x
      rw [← sum_efronProj ν f x, Finset.sum_apply]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun S _ hS ↦ ?_
      have hgt : d < S.card := Nat.lt_of_not_ge (by simpa using hS)
      rw [h S hgt]; rfl
    rw [hfun]
    refine Submodule.sum_mem _ fun S hS ↦ ?_
    refine Submodule.subset_span ?_
    exact ⟨S, (Finset.mem_filter.mp hS).2, efronProj_isJunta ν S f⟩

/-- `f ∈ degSubspace d` iff `f = degPart ν d f`. -/
lemma eq_degPart_of_mem_degSubspace (ν : PMF A) {d : ℕ} {f : (ι → A) → ℂ}
    (hf : f ∈ degSubspace d) : degPart ν d f = f := by
  ext x
  unfold degPart
  rw [← sum_efronProj ν f x]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun S _ hS ↦ ?_
  have hgt : d < S.card := Nat.lt_of_not_ge (by simpa using hS)
  rw [(mem_degSubspace_iff ν d f).mp hf S hgt]; rfl

lemma degPart_mem_degSubspace (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) :
    degPart ν d f ∈ degSubspace d := by
  have h : degPart ν d f = ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
      efronProj ν S f := by ext x; simp [degPart]
  rw [h]
  refine Submodule.sum_mem _ fun S hS ↦ Submodule.subset_span ?_
  exact ⟨S, (Finset.mem_filter.mp hS).2, efronProj_isJunta ν S f⟩

lemma levelWeight_eq_l2NormSq_levelPart (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) :
    levelWeight ν d f = l2NormSq ν (levelPart ν d f) := by
  symm
  exact l2NormSq_sum_of_pairwise_orth ν _ (fun S ↦ efronProj ν S f)
    fun S _ T _ hST ↦ piInner_efronProj_eq_zero ν hST f f

lemma sum_levelWeight_eq_l2NormSq (ν : PMF A) (f : (ι → A) → ℂ) :
    ∑ d ∈ Finset.range (Fintype.card ι + 1), levelWeight ν d f = l2NormSq ν f := by
  rw [parseval_efronProj]
  unfold levelWeight
  rw [← Finset.sum_biUnion]
  · congr 1; ext S
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    exact ⟨S.card, Nat.lt_succ_of_le (Finset.card_le_univ S), rfl⟩
  · intro d₁ _ d₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro S h₁ h₂
    exact hne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)

lemma tailWeight_nonneg (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) : 0 ≤ tailWeight ν d f :=
  Finset.sum_nonneg fun S _ ↦ l2NormSq_nonneg ν (efronProj ν S f)

lemma tailWeight_le_l2NormSq (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) :
    tailWeight ν d f ≤ l2NormSq ν f := by
  rw [parseval_efronProj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun S _ _ ↦ l2NormSq_nonneg ν _

lemma l2NormSq_sub_degPart (ν : PMF A) (d : ℕ) (f : (ι → A) → ℂ) :
    l2NormSq ν (f - degPart ν d f) = tailWeight ν (d + 1) f := by
  have hsub : f - degPart ν d f =
      fun x ↦ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ d + 1 ≤ S.card),
        efronProj ν S f x := by
    ext x
    simp only [Pi.sub_apply, degPart]
    rw [← sum_efronProj ν f x, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S : Finset ι ↦ S.card ≤ d)]
    have hnot : (Finset.univ.filter fun S : Finset ι ↦ ¬ S.card ≤ d) =
        Finset.univ.filter fun S : Finset ι ↦ d + 1 ≤ S.card := by
      ext S; simp
    rw [hnot]; ring
  rw [hsub]
  exact l2NormSq_sum_of_pairwise_orth ν _ (fun S ↦ efronProj ν S f)
    fun S _ T _ hST ↦ piInner_efronProj_eq_zero ν hST f f

end EfronStein

section NoiseAndInfluences

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Bernoulli subset probability `Pr[I ⊆_ε ι] = ε^{|I|} (1 - ε)^{|Iᶜ|}`. -/
@[expose] noncomputable def subsetProb (ε : ℝ) (I : Finset ι) : ℝ :=
  ε ^ I.card * (1 - ε) ^ (Fintype.card ι - I.card)

omit [DecidableEq ι] in
lemma subsetProb_eq_mul_pow (ε : ℝ) (I : Finset ι) :
    subsetProb ε I = ε ^ I.card * (1 - ε) ^ (Fintype.card ι - I.card) :=
  rfl

omit [DecidableEq ι] in
lemma subsetProb_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (I : Finset ι) :
    0 ≤ subsetProb ε I :=
  mul_nonneg (pow_nonneg hε0 _) (pow_nonneg (sub_nonneg.mpr hε1) _)

omit [DecidableEq ι] in
lemma sum_subsetProb (ε : ℝ) : ∑ I : Finset ι, subsetProb ε I = 1 := by
  classical
  unfold subsetProb
  have h := Finset.prod_add (fun _ : ι ↦ ε) (fun _ : ι ↦ 1 - ε) (Finset.univ : Finset ι)
  simp only [add_sub_cancel, Finset.prod_const_one, Finset.powerset_univ, Finset.prod_const] at h
  have h' : (1 : ℝ) = ∑ I : Finset ι, ε ^ I.card * (1 - ε) ^ (Fintype.card ι - I.card) := by
    refine h.trans (Finset.sum_congr rfl fun I _ ↦ ?_)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ]
  exact h'.symm

/-- Probability that a random subset `I ⊆_ε ι` is disjoint from a fixed `S`:
`Pr[I ⊆ Sᶜ] = (1 - ε)^{|S|}`. -/
lemma sum_subsetProb_disjoint (ε : ℝ) (S : Finset ι) :
    ∑ I ∈ Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S), subsetProb ε I =
      (1 - ε) ^ S.card := by
  have h := Finset.prod_add (fun _ : ι ↦ ε) (fun _ : ι ↦ 1 - ε) Sᶜ
  simp only [add_sub_cancel, Finset.prod_const_one, Finset.prod_const] at h
  have hfilt : Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S) = Sᶜ.powerset := by
    ext I
    simp [Finset.subset_compl_iff_disjoint_right]
  rw [hfilt]
  calc ∑ I ∈ Sᶜ.powerset, subsetProb ε I
      = ∑ I ∈ Sᶜ.powerset, (ε ^ I.card * (1 - ε) ^ (Sᶜ \ I).card) * (1 - ε) ^ S.card := by
        refine Finset.sum_congr rfl fun I hI ↦ ?_
        unfold subsetProb
        have hISc : I ⊆ Sᶜ := Finset.mem_powerset.mp hI
        rw [Finset.card_sdiff_of_subset hISc, Finset.card_compl, mul_assoc, ← pow_add]
        have hle : I.card ≤ Fintype.card ι - S.card := by
          have := Finset.card_le_card hISc; rwa [Finset.card_compl] at this
        have hS : S.card ≤ Fintype.card ι := Finset.card_le_univ S
        have hexp : Fintype.card ι - S.card - I.card + S.card = Fintype.card ι - I.card := by omega
        rw [hexp]
    _ = (∑ I ∈ Sᶜ.powerset, ε ^ I.card * (1 - ε) ^ (Sᶜ \ I).card) * (1 - ε) ^ S.card := by
        rw [← Finset.sum_mul]
    _ = (1 - ε) ^ S.card := by rw [← h, one_mul]

/-- The standard noise operator `T_ρ f(x) = E_{I ⊆_{1-ρ} ι}[T_I f(x)]`. -/
@[expose] noncomputable def noiseOp (ν : PMF A) (ρ : ℝ) (f : (ι → A) → ℂ) (x : ι → A) : ℂ :=
  ∑ I : Finset ι, (subsetProb (1 - ρ) I : ℂ) * subsetResampleOp ν I f x

lemma noiseOp_eq_sum_subsetProb (ν : PMF A) (ρ : ℝ) (f : (ι → A) → ℂ) (x : ι → A) :
    noiseOp ν ρ f x = ∑ I : Finset ι, (subsetProb (1 - ρ) I : ℂ) * subsetResampleOp ν I f x :=
  rfl

@[simp]
lemma noiseOp_zero (ν : PMF A) (ρ : ℝ) : noiseOp ν ρ (0 : (ι → A) → ℂ) = 0 := by
  ext x; unfold noiseOp; simp [subsetResampleOp_zero]

lemma noiseOp_add (ν : PMF A) (ρ : ℝ) (f g : (ι → A) → ℂ) :
    noiseOp ν ρ (f + g) = noiseOp ν ρ f + noiseOp ν ρ g := by
  ext x; unfold noiseOp
  simp only [Pi.add_apply, subsetResampleOp_add, mul_add, Finset.sum_add_distrib]

lemma noiseOp_sub (ν : PMF A) (ρ : ℝ) (f g : (ι → A) → ℂ) :
    noiseOp ν ρ (f - g) = noiseOp ν ρ f - noiseOp ν ρ g := by
  ext x; unfold noiseOp
  simp only [Pi.sub_apply, subsetResampleOp_sub, mul_sub, Finset.sum_sub_distrib]

lemma noiseOp_smul (ν : PMF A) (ρ : ℝ) (c : ℂ) (f : (ι → A) → ℂ) :
    noiseOp ν ρ (fun x ↦ c * f x) = fun x ↦ c * noiseOp ν ρ f x := by
  ext x; unfold noiseOp
  simp_rw [subsetResampleOp_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ ↦ ?_; ring

lemma noiseOp_sum {κ : Type*} (ν : PMF A) (ρ : ℝ) (s : Finset κ) (f : κ → (ι → A) → ℂ) :
    noiseOp ν ρ (fun x ↦ ∑ k ∈ s, f k x) = fun x ↦ ∑ k ∈ s, noiseOp ν ρ (f k) x := by
  ext x; unfold noiseOp
  simp_rw [subsetResampleOp_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Eigenvalue action of `T_ρ` on Efron–Stein projections: `T_ρ(f^{=S}) = ρ^{|S|} f^{=S}`. -/
theorem noiseOp_efronProj (ν : PMF A) (ρ : ℝ) (S : Finset ι) (f : (ι → A) → ℂ) :
    noiseOp ν ρ (efronProj ν S f) = fun x ↦ (ρ ^ S.card : ℂ) * efronProj ν S f x := by
  ext x
  unfold noiseOp
  have h : ∀ I : Finset ι, subsetResampleOp ν I (efronProj ν S f) x =
      if Disjoint I S then efronProj ν S f x else 0 := by
    intro I
    by_cases hd : Disjoint I S
    · simp only [hd, ↓reduceIte]
      rw [subsetResampleOp_efronProj_of_disjoint ν hd]
    · simp only [hd, ↓reduceIte]
      rw [Finset.not_disjoint_iff] at hd
      obtain ⟨i, hiI, hiS⟩ := hd
      rw [subsetResampleOp_efronProj_eq_zero ν ⟨i, Finset.mem_inter.mpr ⟨hiI, hiS⟩⟩]
      rfl
  simp_rw [h, mul_ite, mul_zero, ← Finset.sum_filter, ← Finset.sum_mul]
  have hsum : (∑ I ∈ Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S),
      (subsetProb (1 - ρ) I : ℂ)) = (ρ ^ S.card : ℂ) := by
    have hreal := sum_subsetProb_disjoint (1 - ρ) S
    simp only [sub_sub_cancel] at hreal
    exact_mod_cast hreal
  rw [hsum]

/-- Explicit Efron–Stein formula for `T_ρ`: `T_ρ f = ∑_S ρ^{|S|} f^{=S}`. -/
theorem noiseOp_eq_sum_efronProj (ν : PMF A) (ρ : ℝ) (f : (ι → A) → ℂ) (x : ι → A) :
    noiseOp ν ρ f x = ∑ S : Finset ι, (ρ ^ S.card : ℂ) * efronProj ν S f x := by
  have hfun : f = fun y ↦ ∑ S : Finset ι, efronProj ν S f y := by
    ext y; exact (sum_efronProj ν f y).symm
  conv_lhs => rw [hfun]
  rw [noiseOp_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [noiseOp_efronProj]

/-- Self-adjointness of `T_ρ`. -/
lemma piInner_noiseOp_left (ν : PMF A) (ρ : ℝ) (f g : (ι → A) → ℂ) :
    piInner ν (noiseOp ν ρ f) g = piInner ν f (noiseOp ν ρ g) := by
  unfold noiseOp
  rw [piInner_sum_left, piInner_sum_right]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [piInner_smul_left, piInner_smul_right, Complex.conj_ofReal, piInner_subsetResampleOp_left]

/-- `⟨f, T_ρ f⟩ = ∑_S ρ^{|S|} ‖f^{=S}‖₂²`. -/
lemma piInner_noiseOp_self (ν : PMF A) (ρ : ℝ) (f : (ι → A) → ℂ) :
    piInner ν f (noiseOp ν ρ f) =
      ∑ S : Finset ι, ((ρ ^ S.card * l2NormSq ν (efronProj ν S f) : ℝ) : ℂ) := by
  have hf : f = fun x ↦ ∑ S : Finset ι, efronProj ν S f x := by
    ext x; exact (sum_efronProj ν f x).symm
  have hTf : noiseOp ν ρ f = fun x ↦ ∑ S : Finset ι, (ρ ^ S.card : ℂ) * efronProj ν S f x := by
    ext x; exact noiseOp_eq_sum_efronProj ν ρ f x
  rw [hTf]
  conv_lhs => arg 2; rw [hf]
  rw [piInner_sum_left]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [piInner_sum_right, Finset.sum_eq_single S]
  · rw [piInner_smul_right, piInner_self]
    simp [Complex.conj_ofReal]
  · intro T _ hTS
    rw [piInner_smul_right, piInner_efronProj_eq_zero ν (Ne.symm hTS), mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h

/-- For degree-`d` functions `f` and `0 ≤ ε ≤ 1`, `‖f - T_{1-ε} f‖₂² ≤ 2 d ε ‖f‖₂²`
(and in fact `E_{x, y ~ T_{1-ε} x}[‖f(x) - f(y)‖²] = 2(‖f‖₂² - ⟨f, T_{1-ε} f⟩) ≤ 2 d ε ‖f‖₂²`). -/
theorem two_mul_sub_piInner_noiseOp_le (ν : PMF A) {d : ℕ} {f : (ι → A) → ℂ}
    (hf : f ∈ degSubspace d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * (l2NormSq ν f - (piInner ν f (noiseOp ν (1 - ε) f)).re) ≤
      2 * (d : ℝ) * ε * l2NormSq ν f := by
  have hre : (piInner ν f (noiseOp ν (1 - ε) f)).re =
      ∑ S : Finset ι, (1 - ε) ^ S.card * l2NormSq ν (efronProj ν S f) := by
    rw [piInner_noiseOp_self, Complex.re_sum]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    exact Complex.ofReal_re _
  rw [hre, parseval_efronProj ν f, ← Finset.sum_sub_distrib]
  have hterm : ∀ S : Finset ι,
      (l2NormSq ν (efronProj ν S f) - (1 - ε) ^ S.card * l2NormSq ν (efronProj ν S f)) ≤
        (d : ℝ) * ε * l2NormSq ν (efronProj ν S f) := by
    intro S
    by_cases hS : S.card ≤ d
    · have hber : 1 - (S.card : ℝ) * ε ≤ (1 - ε) ^ S.card := by
        have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -ε) S.card
        simpa [sub_eq_add_neg, mul_neg] using this
      have hsub : 1 - (1 - ε) ^ S.card ≤ (d : ℝ) * ε := by
        have : (S.card : ℝ) * ε ≤ (d : ℝ) * ε :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hε0
        linarith
      nlinarith [l2NormSq_nonneg ν (efronProj ν S f)]
    · have hgt : d < S.card := Nat.lt_of_not_ge hS
      rw [(mem_degSubspace_iff ν d f).mp hf S hgt, l2NormSq_zero]
      simp
  have hsum : ∑ S : Finset ι,
      (l2NormSq ν (efronProj ν S f) - (1 - ε) ^ S.card * l2NormSq ν (efronProj ν S f)) ≤
      ∑ S : Finset ι, (d : ℝ) * ε * l2NormSq ν (efronProj ν S f) :=
    Finset.sum_le_sum fun S _ ↦ hterm S
  rw [← Finset.mul_sum] at hsum
  linarith

omit [Fintype A] [DecidableEq ι] in
/-- Averaging `Iᶜ`-juntas over `I ⊆_ε ι` (Lemma `lem:avg_of_juntas_low_deg`):
1. If each `f_I` is `1`-bounded, then `f(x) = E_{I ⊆_ε ι}[f_I(x)]` is `1`-bounded.
2. If `‖f_I‖₂ ≤ 1` for each `I`, then `W^{≥ d}[f] ≤ (1 - ε)^d`. -/
theorem avg_of_juntas_isBoundedBy (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {B : ℝ} (fI : Finset ι → (ι → A) → ℂ) (hfI : ∀ I, IsBoundedBy B (fI I)) :
    IsBoundedBy B (fun x ↦ ∑ I : Finset ι, (subsetProb ε I : ℂ) * fI I x) := by
  intro x
  refine (norm_sum_le _ _).trans ?_
  calc ∑ I : Finset ι, ‖(subsetProb ε I : ℂ) * fI I x‖
      = ∑ I : Finset ι, subsetProb ε I * ‖fI I x‖ := by
        refine Finset.sum_congr rfl fun I _ ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (subsetProb_nonneg hε0 hε1 I)]
    _ ≤ ∑ I : Finset ι, subsetProb ε I * B :=
        Finset.sum_le_sum fun I _ ↦
          mul_le_mul_of_nonneg_left (hfI I x) (subsetProb_nonneg hε0 hε1 I)
    _ = (∑ I : Finset ι, subsetProb ε I) * B := by rw [← Finset.sum_mul]
    _ = B := by rw [sum_subsetProb, one_mul]

/-- Part 2 of Lemma `lem:avg_of_juntas_low_deg`: if each `f_I` is an `Iᶜ`-junta with `‖f_I‖₂² ≤ B`,
then `f(x) = E_{I ⊆_ε ι}[f_I(x)]` satisfies `W^{≥ d}[f] ≤ (1 - ε)^d * B`. -/
theorem tailWeight_avg_of_juntas_le (ν : PMF A) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (d : ℕ) {B : ℝ} (fI : Finset ι → (ι → A) → ℂ)
    (hjunta : ∀ I, IsJunta Iᶜ (fI I)) (hnorm : ∀ I, l2NormSq ν (fI I) ≤ B) :
    tailWeight ν d (fun x ↦ ∑ I : Finset ι, (subsetProb ε I : ℂ) * fI I x) ≤
      (1 - ε) ^ d * B := by
  set f : (ι → A) → ℂ := fun x ↦ ∑ I : Finset ι, (subsetProb ε I : ℂ) * fI I x
  have hSbound : ∀ S : Finset ι,
      l2NormSq ν (efronProj ν S f) ≤
        (1 - ε) ^ S.card * ∑ I : Finset ι, subsetProb ε I * l2NormSq ν (efronProj ν S (fI I)) := by
    intro S
    have hproj : efronProj ν S f =
        fun x ↦ ∑ I ∈ Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S),
          (subsetProb ε I : ℂ) * efronProj ν S (fI I) x := by
      ext x
      change efronProj ν S (fun y ↦ ∑ I : Finset ι, (subsetProb ε I : ℂ) * fI I y) x = _
      rw [efronProj_sum]
      simp_rw [efronProj_smul]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun I _ ↦ ?_
      by_cases hd : Disjoint I S
      · simp [hd]
      · simp only [hd, ↓reduceIte]
        have hnot : ¬ S ⊆ Iᶜ := fun h ↦
          hd (Finset.disjoint_left.mpr fun i hiI hiS ↦ (Finset.mem_compl.mp (h hiS)) hiI)
        rw [efronProj_eq_zero_of_isJunta ν (hjunta I) hnot]; simp
    rw [hproj]
    have hpt : ∀ x : ι → A,
        ‖∑ I ∈ Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S),
            (subsetProb ε I : ℂ) * efronProj ν S (fI I) x‖ ^ 2 ≤
          (1 - ε) ^ S.card *
            ∑ I : Finset ι, subsetProb ε I * ‖efronProj ν S (fI I) x‖ ^ 2 := by
      intro x
      set s := Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S)
      have h1 : ‖∑ I ∈ s, (subsetProb ε I : ℂ) * efronProj ν S (fI I) x‖ ≤
          ∑ I ∈ s, √(subsetProb ε I) * (√(subsetProb ε I) * ‖efronProj ν S (fI I) x‖) := by
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun I _ ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (subsetProb_nonneg hε0 hε1 I)]
        have hw := Real.mul_self_sqrt (subsetProb_nonneg hε0 hε1 I)
        exact le_of_eq (by rw [← mul_assoc, hw])
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
        (fun I ↦ √(subsetProb ε I)) (fun I ↦ √(subsetProb ε I) * ‖efronProj ν S (fI I) x‖)
      have h2 := h1.trans hcs
      have hsq : (√(∑ I ∈ s, (√(subsetProb ε I)) ^ 2) *
          √(∑ I ∈ s, (√(subsetProb ε I) * ‖efronProj ν S (fI I) x‖) ^ 2)) ^ 2 =
          (∑ I ∈ s, subsetProb ε I) *
            ∑ I ∈ s, subsetProb ε I * ‖efronProj ν S (fI I) x‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
        congr 1
        · refine Finset.sum_congr rfl fun I _ ↦ Real.sq_sqrt (subsetProb_nonneg hε0 hε1 I)
        · refine Finset.sum_congr rfl fun I _ ↦ ?_
          rw [mul_pow, Real.sq_sqrt (subsetProb_nonneg hε0 hε1 I)]
      have hle_sq : ‖∑ I ∈ s, (subsetProb ε I : ℂ) * efronProj ν S (fI I) x‖ ^ 2 ≤
          (∑ I ∈ s, subsetProb ε I) *
            ∑ I ∈ s, subsetProb ε I * ‖efronProj ν S (fI I) x‖ ^ 2 := by
        rw [← hsq]
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      refine hle_sq.trans ?_
      rw [sum_subsetProb_disjoint ε S]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (sub_nonneg.mpr hε1) _)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun I _ _ ↦ mul_nonneg (subsetProb_nonneg hε0 hε1 I) (sq_nonneg _)
    calc l2NormSq ν (fun x ↦ ∑ I ∈ Finset.univ.filter (fun I : Finset ι ↦ Disjoint I S),
            (subsetProb ε I : ℂ) * efronProj ν S (fI I) x)
        ≤ piExpectReal ν (fun x ↦ (1 - ε) ^ S.card *
            ∑ I : Finset ι, subsetProb ε I * ‖efronProj ν S (fI I) x‖ ^ 2) :=
          piExpectReal_mono ν hpt
      _ = (1 - ε) ^ S.card *
            ∑ I : Finset ι, subsetProb ε I * l2NormSq ν (efronProj ν S (fI I)) := by
          rw [piExpectReal_smul, piExpectReal_sum]
          congr 1
          refine Finset.sum_congr rfl fun I _ ↦ ?_
          rw [piExpectReal_smul]; rfl
  have hB0 : 0 ≤ B := (l2NormSq_nonneg ν (fI ∅)).trans (hnorm ∅)
  calc tailWeight ν d f
      ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ d ≤ S.card),
          (1 - ε) ^ S.card *
            ∑ I : Finset ι, subsetProb ε I * l2NormSq ν (efronProj ν S (fI I)) :=
        Finset.sum_le_sum fun S _ ↦ hSbound S
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ d ≤ S.card),
          (1 - ε) ^ d *
            ∑ I : Finset ι, subsetProb ε I * l2NormSq ν (efronProj ν S (fI I)) := by
        refine Finset.sum_le_sum fun S hS ↦ ?_
        have hdS : d ≤ S.card := (Finset.mem_filter.mp hS).2
        refine mul_le_mul_of_nonneg_right ?_
          (Finset.sum_nonneg fun I _ ↦
            mul_nonneg (subsetProb_nonneg hε0 hε1 I) (l2NormSq_nonneg ν _))
        exact pow_le_pow_of_le_one (sub_nonneg.mpr hε1) (by linarith) hdS
    _ = (1 - ε) ^ d * ∑ I : Finset ι, subsetProb ε I * tailWeight ν d (fI I) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun I _ ↦ ?_
        rw [← Finset.mul_sum]; rfl
    _ ≤ (1 - ε) ^ d * ∑ I : Finset ι, subsetProb ε I * B := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (sub_nonneg.mpr hε1) _)
        refine Finset.sum_le_sum fun I _ ↦
          mul_le_mul_of_nonneg_left
            ((tailWeight_le_l2NormSq ν d (fI I)).trans (hnorm I))
            (subsetProb_nonneg hε0 hε1 I)
    _ = (1 - ε) ^ d * B := by
        rw [← Finset.sum_mul, sum_subsetProb, one_mul]

/-- Coordinate influence `I_i[f] = E_{x ~ ν^⊗ι, y ~ T_{i} x}[‖f(x) - f(y)‖²]`. -/
@[expose] noncomputable def coordInf (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) : ℝ :=
  piExpectReal ν (fun x ↦ piExpectReal ν (fun y ↦ ‖f x - f (splice {i} x y)‖ ^ 2))

lemma coordInf_eq_piExpectReal (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) :
    coordInf ν i f =
      piExpectReal ν (fun x ↦ piExpectReal ν (fun y ↦ ‖f x - f (splice {i} x y)‖ ^ 2)) :=
  rfl

/-- Degree-`d` coordinate influence `I_i^{≤ d}[f] = I_i[f^{≤ d}]`. -/
@[expose] noncomputable def degCoordInf (ν : PMF A) (d : ℕ) (i : ι) (f : (ι → A) → ℂ) : ℝ :=
  coordInf ν i (degPart ν d f)

lemma coordInf_nonneg (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) : 0 ≤ coordInf ν i f :=
  piExpectReal_nonneg ν fun _ ↦ piExpectReal_nonneg ν fun _ ↦ sq_nonneg _

/-- Identity `I_i[f] = 2 * ‖f - E_i f‖₂² = 2 ∑_{S ∋ i} ‖f^{=S}‖₂²`. -/
theorem coordInf_eq_two_mul_l2NormSq_sub (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) :
    coordInf ν i f = 2 * l2NormSq ν (f - coordCondExpect ν i f) := by
  have h1 : coordInf ν i f = 2 * (l2NormSq ν f - (piInner ν f (coordCondExpect ν i f)).re) := by
    have hexp : (coordInf ν i f : ℂ) =
        (l2NormSq ν f : ℂ) - piInner ν f (coordCondExpect ν i f) -
          piInner ν (coordCondExpect ν i f) f + (l2NormSq ν f : ℂ) := by
      have hl2 : (l2NormSq ν f : ℂ) =
          ∑ x : ι → A, (piWeight ν x : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
        rw [← piInner_self]; exact piInner_eq_sum ν f f
      rw [hl2]
      unfold coordInf
      rw [coordCondExpect_eq_subsetResampleOp, piInner_eq_sum, piInner_eq_sum]
      simp_rw [piExpectReal_eq_sum, subsetResampleOp_eq_sum]
      rw [Complex.ofReal_sum]
      simp_rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
      have hnorm : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := fun z ↦ by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp
      simp_rw [hnorm]
      simp only [map_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
      have hA : (∑ x : ι → A, (piWeight ν x : ℂ) *
          ∑ y : ι → A, (piWeight ν y : ℂ) * (f x * (starRingEnd ℂ) (f x))) =
          ∑ x : ι → A, (piWeight ν x : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [← Finset.sum_mul]
        have hw : (∑ y : ι → A, (piWeight ν y : ℂ)) = 1 := by exact_mod_cast sum_piWeight ν
        rw [hw, one_mul]
      have hD : (∑ x : ι → A, (piWeight ν x : ℂ) *
          ∑ y : ι → A, (piWeight ν y : ℂ) *
            (f (splice {i} x y) * (starRingEnd ℂ) (f (splice {i} x y)))) =
          ∑ x : ι → A, (piWeight ν x : ℂ) * (f x * (starRingEnd ℂ) (f x)) := by
        have hst := piExpect_subsetResampleOp ν {i} (fun x ↦ f x * starRingEnd ℂ (f x))
        simpa only [subsetResampleOp_eq_sum, piExpect_eq_sum] using hst
      have hB : (∑ x : ι → A, (piWeight ν x : ℂ) *
          ∑ y : ι → A, (piWeight ν y : ℂ) * (f x * (starRingEnd ℂ) (f (splice {i} x y)))) =
          ∑ x : ι → A, (piWeight ν x : ℂ) * (f x *
            (starRingEnd ℂ) (∑ y : ι → A, (piWeight ν y : ℂ) * f (splice {i} x y))) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        congr 1
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        simp [Complex.conj_ofReal]; ring
      have hC : (∑ x : ι → A, (piWeight ν x : ℂ) *
          ∑ y : ι → A, (piWeight ν y : ℂ) * (f (splice {i} x y) * (starRingEnd ℂ) (f x))) =
          ∑ x : ι → A, (piWeight ν x : ℂ) *
            ((∑ y : ι → A, (piWeight ν y : ℂ) * f (splice {i} x y)) * (starRingEnd ℂ) (f x)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        congr 1
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ ↦ ?_; ring
      rw [hA, hD, hB, hC]
      ring
    have hconj : piInner ν (coordCondExpect ν i f) f =
        starRingEnd ℂ (piInner ν f (coordCondExpect ν i f)) :=
      (piInner_conj_symm ν f (coordCondExpect ν i f)).symm
    rw [hconj] at hexp
    have hre := congr_arg Complex.re hexp
    simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.conj_re] at hre
    linarith
  have h2 : l2NormSq ν (f - coordCondExpect ν i f) =
      l2NormSq ν f - (piInner ν f (coordCondExpect ν i f)).re := by
    rw [l2NormSq_sub_eq]
    have hsq : l2NormSq ν (coordCondExpect ν i f) =
        (piInner ν f (coordCondExpect ν i f)).re := by
      have hc : (l2NormSq ν (coordCondExpect ν i f) : ℂ) =
          piInner ν f (coordCondExpect ν i f) := by
        rw [coordCondExpect_eq_subsetResampleOp, ← piInner_self, piInner_subsetResampleOp_left,
          subsetResampleOp_comp, Finset.union_idempotent]
      exact_mod_cast congr_arg Complex.re hc
    linarith
  linarith

/-- Efron–Stein formula for coordinate influence: `I_i[f] = 2 ∑_{S ∋ i} ‖f^{=S}‖₂²`. -/
theorem coordInf_eq_two_mul_sum_efronProj (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) :
    coordInf ν i f =
      2 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ i ∈ S),
        l2NormSq ν (efronProj ν S f) := by
  rw [coordInf_eq_two_mul_l2NormSq_sub]
  congr 1
  have hsub : f - coordCondExpect ν i f =
      fun x ↦ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ i ∈ S), efronProj ν S f x := by
    ext x
    simp only [Pi.sub_apply, coordCondExpect_eq_subsetResampleOp]
    have h1 : f x = ∑ S : Finset ι, efronProj ν S f x := (sum_efronProj ν f x).symm
    have h2 : subsetResampleOp ν {i} f x =
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ i ∉ S), efronProj ν S f x := by
      conv_lhs => rw [show f = fun y ↦ ∑ S : Finset ι, efronProj ν S f y by
        ext y; exact (sum_efronProj ν f y).symm]
      rw [subsetResampleOp_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ ↦ ?_
      by_cases hi : i ∈ S
      · simp only [hi, not_true_eq_false, ↓reduceIte]
        rw [subsetResampleOp_efronProj_eq_zero ν
          ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, hi⟩⟩]; rfl
      · simp only [hi, not_false_eq_true, ↓reduceIte]
        rw [subsetResampleOp_efronProj_of_disjoint ν (Finset.disjoint_singleton_left.mpr hi)]
    rw [h1, h2, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset ι ↦ i ∈ S)]
    ring
  rw [hsub]
  exact l2NormSq_sum_of_pairwise_orth ν _ (fun S ↦ efronProj ν S f)
    fun S _ T _ hST ↦ piInner_efronProj_eq_zero ν hST f f

/-- `∑_i I_i[f] = 2 ∑_S |S| ‖f^{=S}‖₂² ≤ 2 d ‖f‖₂²` for degree-`d` functions. -/
theorem sum_coordInf_le_of_deg (ν : PMF A) {d : ℕ} {f : (ι → A) → ℂ}
    (hf : f ∈ degSubspace d) :
    ∑ i : ι, coordInf ν i f ≤ 2 * (d : ℝ) * l2NormSq ν f := by
  simp_rw [coordInf_eq_two_mul_sum_efronProj]
  rw [← Finset.mul_sum]
  have hswap : (∑ i : ι, ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ i ∈ S),
      l2NormSq ν (efronProj ν S f)) =
      ∑ S : Finset ι, (S.card : ℝ) * l2NormSq ν (efronProj ν S f) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp
  rw [hswap, parseval_efronProj ν f, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ ↦ ?_
  by_cases hS : S.card ≤ d
  · have h1 : (S.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hS
    nlinarith [l2NormSq_nonneg ν (efronProj ν S f)]
  · have hgt : d < S.card := Nat.lt_of_not_ge hS
    rw [(mem_degSubspace_iff ν d f).mp hf S hgt, l2NormSq_zero]; simp

end NoiseAndInfluences


end CslibFrontier.Analysis.Fourier
