/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations
public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.Communication.Rank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Rank

import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Nisan–Wigderson Rectangle-Partition Reduction and Spira Tree Rebalancing

This module formalizes the classical Nisan–Wigderson reduction from large monochromatic
submatrices in low-rank binary matrices to deterministic communication protocols, together with
Spira's binary-tree rebalancing for `Cslib.Communication.Protocol`.

1. **Row and column deduplication (`exists_dedup_submatrix`)**: every `m × n` `{0, 1}`-valued real
   matrix of rank at most `r` reduces via row and column representatives to an induced submatrix of
   dimensions at most `2 ^ r × 2 ^ r`.
2. **Rank-halving around monochromatic submatrices (`rank_add_rank_le_of_zero_submatrix`,
   `min_rank_le_half_succ_of_monochromatic`)**: around any all-`0` or all-`1` submatrix `M[X × Y]`
   inside `M[S × T]` of rank at most `r`, at least one of the two off-diagonal blocks
   `M[X × (T \ Y)]` or `M[(S \ X) × Y]` has rank at most `(r + 1) / 2`.
3. **Nisan–Wigderson rectangle-partition tree (`RectTree`,
   `exists_rectTree_of_rank_le_of_monochromatic_sqrt`)**: given any universal monochromatic
   submatrix guarantee of side-length factor `2 ^ (-c₁ * √r)`, every rank-`r` binary matrix with
   at most `2 ^ r` rows and columns admits a valid binary rectangle-partition tree `t` with
   `Nat.log 2 t.leafCount ≤ C * Real.sqrt r + C`.
4. **Spira rebalancing (`exists_protocol_of_rectTree`)**: any valid `RectTree` covering
   `Finset.univ ×ˢ Finset.univ` compiles to a `Cslib.Communication.Protocol` of depth at most
   `2 * (2 * Nat.log 2 t.leafCount + 2)`.
5. **Communication complexity upper bound (`ecomplexityFun_le_sqrt_rank_of_monochromatic`)**:
   combining the above yields `O(√r)` bounds on `Cslib.Communication.Protocol.ecomplexityFun` for
   all Boolean functions on finite domains from any `2 ^ (-c₁ * √r)` monochromatic submatrix bound.

## Main definitions

* `Cslib.Communication.NisanWigderson.RectTree`: binary rectangle-partition tree.
* `Cslib.Communication.NisanWigderson.RectTree.Valid`: disjoint rectangle-partition validity.

## Main results

* `Cslib.Communication.NisanWigderson.exists_dedup_submatrix`
* `Cslib.Communication.NisanWigderson.rank_add_rank_le_of_zero_submatrix`
* `Cslib.Communication.NisanWigderson.min_rank_le_half_succ_of_monochromatic`
* `Cslib.Communication.NisanWigderson.exists_rectTree_of_rank_le_of_monochromatic_sqrt`
* `Cslib.Communication.NisanWigderson.exists_protocol_of_rectTree`
* `Cslib.Communication.NisanWigderson.ecomplexityFun_le_sqrt_rank_of_monochromatic`
-/

public section

open scoped Matrix

namespace Cslib.Communication.NisanWigderson

/-! ### 1. Basic Submatrix and Monochromatic Helpers -/

private def submatrixOfFinset {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (X : Finset (Fin m)) (Y : Finset (Fin n)) : Matrix (Fin X.card) (Fin Y.card) ℝ :=
  M.submatrix (X.orderEmbOfFin rfl) (Y.orderEmbOfFin rfl)

private lemma orderEmb_orderIso_symm {k : ℕ} (S : Finset (Fin k)) {x : Fin k} (hx : x ∈ S) :
    S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩) = x := by
  simp [← S.coe_orderIsoOfFin_apply rfl]

private lemma rank_submatrixOfFinset_le_of_subset {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    {S S' : Finset (Fin m)} {T T' : Finset (Fin n)} (hS : S' ⊆ S) (hT : T' ⊆ T) :
    (submatrixOfFinset M S' T').rank ≤ (submatrixOfFinset M S T).rank := by
  let f : Fin S'.card → Fin S.card := fun i ↦
    (S.orderIsoOfFin rfl).symm ⟨S'.orderEmbOfFin rfl i, hS (Finset.orderEmbOfFin_mem S' rfl i)⟩
  let g : Fin T'.card → Fin T.card := fun j ↦
    (T.orderIsoOfFin rfl).symm ⟨T'.orderEmbOfFin rfl j, hT (Finset.orderEmbOfFin_mem T' rfl j)⟩
  rw [show submatrixOfFinset M S' T' = (submatrixOfFinset M S T).submatrix f g by
    ext i j; simp [submatrixOfFinset, f, g, orderEmb_orderIso_symm]]
  exact Matrix.rank_submatrix_le _ f g

private lemma lift_mono {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {c : ℝ}
    {A : Finset (Fin m)} {B : Finset (Fin n)} {X : Finset (Fin A.card)} {Y : Finset (Fin B.card)}
    (h : ∀ i ∈ X, ∀ j ∈ Y, submatrixOfFinset M A B i j = c) :
    ∃ (X' : Finset (Fin m)) (Y' : Finset (Fin n)),
      X' ⊆ A ∧ Y' ⊆ B ∧ X'.card = X.card ∧ Y'.card = Y.card ∧
      ∀ i ∈ X', ∀ j ∈ Y', M i j = c := by
  refine ⟨X.map (A.orderEmbOfFin rfl).toEmbedding, Y.map (B.orderEmbOfFin rfl).toEmbedding,
    ?_, ?_, Finset.card_map _, Finset.card_map _, ?_⟩
  · intro i hi
    obtain ⟨i₀, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.orderEmbOfFin_mem A rfl i₀
  · intro j hj
    obtain ⟨j₀, _, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.orderEmbOfFin_mem B rfl j₀
  · intro i hi j hj
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_map.mp hj
    simpa [submatrixOfFinset] using h i₀ hi₀ j₀ hj₀

/-! ### 2. Row and Column Deduplication -/

private lemma exists_row_dedup {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hr : A.rank ≤ r) :
    ∃ (S₀ : Finset (Fin p)) (rowRep : Fin p → Fin S₀.card),
      S₀.card ≤ 2 ^ r ∧ ∀ i j, A i j = A (S₀.orderEmbOfFin rfl (rowRep i)) j := by
  classical
  obtain ⟨b, hb_sub, hb_span, hli⟩ := exists_linearIndependent ℝ (Set.range A.col)
  have hb_fin : b.Finite := (Set.finite_range A.col).subset hb_sub
  let bFin : Finset (Fin p → ℝ) := hb_fin.toFinset
  let e : bFin ↪ b := ⟨fun x ↦ ⟨x.1, hb_fin.mem_toFinset.mp x.2⟩,
    fun _ _ h ↦ Subtype.ext (congr_arg (Subtype.val : b → (Fin p → ℝ)) h)⟩
  have hcard_bFin : bFin.card ≤ r := by
    have hcard_eq := linearIndependent_iff_card_eq_finrank_span.mp (hli.comp e e.injective)
    have hrange_eq : Set.range ((Subtype.val : b → (Fin p → ℝ)) ∘ e) = b := by
      ext v; exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ (e x).2, fun hv ↦ ⟨⟨v, hb_fin.mem_toFinset.mpr hv⟩, rfl⟩⟩
    rw [hrange_eq] at hcard_eq
    have hfinrank : Set.finrank ℝ b = A.rank := by
      rw [Matrix.rank_eq_finrank_span_cols A, ← hb_span]; rfl
    rw [Fintype.card_coe, hfinrank] at hcard_eq; exact hcard_eq.le.trans hr
  let B : Finset (Fin q) := Finset.univ.image fun v : bFin ↦
    Classical.choose (hb_sub (hb_fin.mem_toFinset.mp v.2))
  have hB_card : B.card ≤ r := (Finset.card_image_le.trans (by simp)).trans hcard_bFin
  have hspan_B :
      Submodule.span ℝ (Set.range A.col) ≤ Submodule.span ℝ (A.col '' (B : Set (Fin q))) := by
    rw [← hb_span]; exact Submodule.span_mono fun v hv ↦
      ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ
        (⟨v, hb_fin.mem_toFinset.mpr hv⟩ : bFin))), Classical.choose_spec (hb_sub hv)⟩
  have hagree : ∀ i₁ i₂ : Fin p, (∀ j ∈ B, A i₁ j = A i₂ j) → ∀ j : Fin q, A i₁ j = A i₂ j := by
    intro i₁ i₂ hB j
    let φ : (Fin p → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin p ↦ ℝ) i₁ -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin p ↦ ℝ) i₂
    have hker : Submodule.span ℝ (A.col '' (B : Set (Fin q))) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]; rintro v ⟨j', hj', rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]; simp [φ, hB j' (Finset.mem_coe.mp hj')]
    have hmem := hker (hspan_B (Submodule.subset_span (Set.mem_range_self j)))
    exact sub_eq_zero.mp (by simpa [φ, LinearMap.mem_ker] using hmem)
  let sig : Fin p → (B → Bool) := fun i b ↦ decide (A i b.1 = 1)
  have hsig_eq : ∀ i₁ i₂ : Fin p, sig i₁ = sig i₂ → ∀ j : Fin q, A i₁ j = A i₂ j := by
    intro i₁ i₂ hs; refine hagree i₁ i₂ fun j hj ↦ ?_
    have hdec := congr_fun hs ⟨j, hj⟩; dsimp [sig] at hdec
    rcases hA i₁ j with h1 | h1 <;> rcases hA i₂ j with h2 | h2 <;> simp_all
  let K : Finset (B → Bool) := Finset.univ.image sig
  let repFun : {k : B → Bool // k ∈ K} → Fin p := fun k ↦ Classical.choose (Finset.mem_image.mp k.2)
  let S₀ : Finset (Fin p) := K.attach.image repFun
  have hS₀_card : S₀.card ≤ 2 ^ r := (Finset.card_image_le.trans Finset.card_attach.le).trans
    ((Finset.card_le_univ K).trans (by simpa using Nat.pow_le_pow_right (by norm_num) hB_card))
  let rowRep : Fin p → Fin S₀.card := fun i ↦ (S₀.orderIsoOfFin rfl).symm
    ⟨repFun ⟨sig i, Finset.mem_image_of_mem sig (Finset.mem_univ i)⟩,
      Finset.mem_image_of_mem repFun (Finset.mem_attach K _)⟩
  refine ⟨S₀, rowRep, hS₀_card, fun i j ↦ ?_⟩
  let k : {k : B → Bool // k ∈ K} := ⟨sig i, Finset.mem_image_of_mem sig (Finset.mem_univ i)⟩
  dsimp [rowRep]; rw [orderEmb_orderIso_symm S₀]
  exact (hsig_eq (repFun k) i (Classical.choose_spec (Finset.mem_image.mp k.2)).2 j).symm

/-- Every `m × n` `{0, 1}`-valued real matrix `M` of rank at most `r` reduces via row and column
representatives to an induced submatrix on `S₀ × T₀` with `S₀.card ≤ 2 ^ r` and
`T₀.card ≤ 2 ^ r`. -/
theorem exists_dedup_submatrix {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, M i j = 0 ∨ M i j = 1) (hr : M.rank ≤ r) :
    ∃ (S₀ : Finset (Fin m)) (T₀ : Finset (Fin n))
      (rowRep : Fin m → Fin S₀.card) (colRep : Fin n → Fin T₀.card),
      S₀.card ≤ 2 ^ r ∧ T₀.card ≤ 2 ^ r ∧
      ∀ i j, M i j =
        M (S₀.orderEmbOfFin rfl (rowRep i)) (T₀.orderEmbOfFin rfl (colRep j)) := by
  obtain ⟨S₀, rowRep, hS₀, hrow⟩ := exists_row_dedup M hM hr
  let M₁ : Matrix (Fin S₀.card) (Fin n) ℝ := M.submatrix (S₀.orderEmbOfFin rfl) id
  have hM₁_bin : ∀ j i, M₁ᵀ j i = 0 ∨ M₁ᵀ j i = 1 :=
    fun j i ↦ hM (S₀.orderEmbOfFin rfl i) j
  have hM₁_rank : M₁ᵀ.rank ≤ r := by
    rw [Matrix.rank_transpose]; exact (Matrix.rank_submatrix_le M _ _).trans hr
  obtain ⟨T₀, colRep, hT₀, hcol⟩ := exists_row_dedup M₁ᵀ hM₁_bin hM₁_rank
  refine ⟨S₀, T₀, rowRep, colRep, hS₀, hT₀, fun i j ↦ ?_⟩
  have h1 : M i j = M₁ (rowRep i) j := hrow i j
  have h2 : M₁ (rowRep i) j = M₁ (rowRep i) (T₀.orderEmbOfFin rfl (colRep j)) := hcol j (rowRep i)
  rw [h1, h2]; rfl

/-! ### 3. Rank-Halving Around Monochromatic Submatrices -/

private def equivSumSdiff {k : ℕ} {S X : Finset (Fin k)} (hX : X ⊆ S) :
    X ⊕ (S \ X : Finset (Fin k)) ≃ S where
  toFun := Sum.elim (fun x ↦ ⟨x.1, hX x.2⟩) (fun x ↦ ⟨x.1, Finset.sdiff_subset x.2⟩)
  invFun x := if hx : x.1 ∈ X then Sum.inl ⟨x.1, hx⟩
    else Sum.inr ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩ | ⟨x, hx⟩
    · simp [hx]
    · simp [(Finset.mem_sdiff.mp hx).2]
  right_inv x := by by_cases hx : x.1 ∈ X <;> simp [hx]

private lemma submatrixOfFinset_reindex_fromBlocks {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    {S X : Finset (Fin m)} {T Y : Finset (Fin n)} (hX : X ⊆ S) (hY : Y ⊆ T) :
    ∃ (eRow : Fin X.card ⊕ Fin (S \ X).card ≃ Fin S.card)
      (eCol : Fin Y.card ⊕ Fin (T \ Y).card ≃ Fin T.card),
      (submatrixOfFinset M S T).submatrix eRow eCol =
        Matrix.fromBlocks (submatrixOfFinset M X Y) (submatrixOfFinset M X (T \ Y))
          (submatrixOfFinset M (S \ X) Y) (submatrixOfFinset M (S \ X) (T \ Y)) := by
  let eRow := ((X.orderIsoOfFin rfl).toEquiv.sumCongr ((S \ X).orderIsoOfFin rfl).toEquiv).trans
    ((equivSumSdiff hX).trans (S.orderIsoOfFin rfl).toEquiv.symm)
  let eCol := ((Y.orderIsoOfFin rfl).toEquiv.sumCongr ((T \ Y).orderIsoOfFin rfl).toEquiv).trans
    ((equivSumSdiff hY).trans (T.orderIsoOfFin rfl).toEquiv.symm)
  refine ⟨eRow, eCol, ?_⟩; ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [submatrixOfFinset, eRow, eCol, equivSumSdiff, orderEmb_orderIso_symm]

private lemma span_row_lift_ker {m₁ m₂ n₁ n₂ : ℕ}
    (A : Matrix (Fin m₁ ⊕ Fin m₂) (Fin n₁ ⊕ Fin n₂) ℝ) (S : Set (Fin n₂ → ℝ))
    (hS : ∀ w ∈ S, ∃ v ∈ Submodule.span ℝ (Set.range A.row),
      (∀ j, v (Sum.inl j) = 0) ∧ (fun j ↦ v (Sum.inr j)) = w) :
    ∀ w ∈ Submodule.span ℝ S, ∃ v ∈ Submodule.span ℝ (Set.range A.row),
      (∀ j, v (Sum.inl j) = 0) ∧ (fun j ↦ v (Sum.inr j)) = w := by
  intro w hw; induction hw using Submodule.span_induction with
  | mem w hw => exact hS w hw
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ ↦ rfl, rfl⟩
  | add _ _ _ _ ihx ihy =>
    obtain ⟨vx, hxR, hx0, hxw⟩ := ihx; obtain ⟨vy, hyR, hy0, hyw⟩ := ihy
    exact ⟨vx + vy, Submodule.add_mem _ hxR hyR, fun j ↦ by simp [hx0 j, hy0 j],
      by ext j; simp [← hxw, ← hyw]⟩
  | smul a _ _ ihx =>
    obtain ⟨vx, hxR, hx0, hxw⟩ := ihx
    exact ⟨a • vx, Submodule.smul_mem _ a hxR, fun j ↦ by simp [hx0 j], by ext j; simp [← hxw]⟩

private lemma rank_add_finrank_le_fromBlocks {m₁ m₂ n₁ n₂ : ℕ}
    (A₁₁ : Matrix (Fin m₁) (Fin n₁) ℝ) (B : Matrix (Fin m₁) (Fin n₂) ℝ)
    (C : Matrix (Fin m₂) (Fin n₁) ℝ) (D : Matrix (Fin m₂) (Fin n₂) ℝ)
    (W : Submodule ℝ (Fin n₂ → ℝ))
    (hW : ∀ w ∈ W, ∃ v ∈ Submodule.span ℝ (Set.range (Matrix.fromBlocks A₁₁ B C D).row),
      (∀ j, v (Sum.inl j) = 0) ∧ (fun j ↦ v (Sum.inr j)) = w) :
    C.rank + Module.finrank ℝ W ≤ (Matrix.fromBlocks A₁₁ B C D).rank := by
  let A := Matrix.fromBlocks A₁₁ B C D; let R_A := Submodule.span ℝ (Set.range A.row)
  let π : (Fin n₁ ⊕ Fin n₂ → ℝ) →ₗ[ℝ] (Fin n₁ → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inl
  let ρ : (Fin n₁ ⊕ Fin n₂ → ℝ) →ₗ[ℝ] (Fin n₂ → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inr
  let π' := π.domRestrict R_A
  have hC_le : C.rank ≤ Module.finrank ℝ (LinearMap.range π') := by
    rw [Matrix.rank_eq_finrank_span_row C]; refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩; exact ⟨⟨A.row (Sum.inr i), Submodule.subset_span ⟨Sum.inr i, rfl⟩⟩, rfl⟩
  have hW_le : Module.finrank ℝ W ≤ Module.finrank ℝ (LinearMap.ker π') := by
    refine (Submodule.finrank_mono fun w hw ↦ ?_).trans
      ((Submodule.finrank_map_le ρ _).trans (Submodule.finrank_map_le R_A.subtype _))
    obtain ⟨v, hvR, hv0, rfl⟩ := hW w hw
    exact ⟨v, ⟨⟨v, hvR⟩, by change π' ⟨v, hvR⟩ = 0; ext j; exact hv0 j, rfl⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker π'
  have hRA : Module.finrank ℝ R_A = A.rank := (Matrix.rank_eq_finrank_span_row A).symm
  dsimp only [A] at hRA; omega

/-- Around any all-`0` submatrix `M[X × Y]` inside `M[S × T]`, the sum of the ranks of the two
off-diagonal submatrices `M[X × (T \ Y)]` and `M[(S \ X) × Y]` is at most the rank of
`M[S × T]`. -/
theorem rank_add_rank_le_of_zero_submatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    {S X : Finset (Fin m)} {T Y : Finset (Fin n)} (hX : X ⊆ S) (hY : Y ⊆ T)
    (hzero : ∀ i ∈ X, ∀ j ∈ Y, M i j = 0) :
    (M.submatrix (X.orderEmbOfFin rfl) ((T \ Y).orderEmbOfFin rfl)).rank +
      (M.submatrix ((S \ X).orderEmbOfFin rfl) (Y.orderEmbOfFin rfl)).rank ≤
      (M.submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin rfl)).rank := by
  obtain ⟨eRow, eCol, hblocks⟩ := submatrixOfFinset_reindex_fromBlocks M hX hY
  have hA11 : submatrixOfFinset M X Y = 0 := by
    ext i j
    exact hzero _ (Finset.orderEmbOfFin_mem X rfl i) _ (Finset.orderEmbOfFin_mem Y rfl j)
  rw [hA11] at hblocks
  let B := submatrixOfFinset M X (T \ Y); let C := submatrixOfFinset M (S \ X) Y
  let D := submatrixOfFinset M (S \ X) (T \ Y)
  let A := Matrix.fromBlocks (0 : Matrix (Fin X.card) (Fin Y.card) ℝ) B C D
  have hW := span_row_lift_ker A (Set.range B.row) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨A.row (Sum.inl i), Submodule.subset_span ⟨Sum.inl i, rfl⟩, fun _ ↦ rfl, rfl⟩)
  have hle := rank_add_finrank_le_fromBlocks (0 : Matrix (Fin X.card) (Fin Y.card) ℝ) B C D _ hW
  rw [← Matrix.rank_eq_finrank_span_row B] at hle
  dsimp only [B, C, D] at hle; rw [← hblocks, Matrix.rank_submatrix] at hle
  dsimp only [submatrixOfFinset] at hle; omega

/-- Around any `0`- or `1`-monochromatic submatrix `M[X × Y]` inside `M[S × T]` of rank at most
`r`, at least one of the two off-diagonal submatrices `M[X × (T \ Y)]` or `M[(S \ X) × Y]` has
rank at most `(r + 1) / 2`. -/
theorem min_rank_le_half_succ_of_monochromatic {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    {S X : Finset (Fin m)} {T Y : Finset (Fin n)} (hX : X ⊆ S) (hY : Y ⊆ T)
    (hmono : (∀ i ∈ X, ∀ j ∈ Y, M i j = 0) ∨ (∀ i ∈ X, ∀ j ∈ Y, M i j = 1))
    (hr : (M.submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin rfl)).rank ≤ r) :
    (M.submatrix (X.orderEmbOfFin rfl) ((T \ Y).orderEmbOfFin rfl)).rank ≤ (r + 1) / 2 ∨
      (M.submatrix ((S \ X).orderEmbOfFin rfl) (Y.orderEmbOfFin rfl)).rank ≤ (r + 1) / 2 := by
  rcases hmono with hzero | hone
  · have hsum := (rank_add_rank_le_of_zero_submatrix M hX hY hzero).trans hr; omega
  · rcases X.eq_empty_or_nonempty with rfl | hXne
    · left; have h0 : (submatrixOfFinset M ∅ (T \ Y)).rank ≤ 0 := by
        simpa using (submatrixOfFinset M ∅ (T \ Y)).rank_le_height
      dsimp only [submatrixOfFinset] at h0; omega
    · obtain ⟨eRow, eCol, hblocks⟩ := submatrixOfFinset_reindex_fromBlocks M hX hY
      let A₁₁ : Matrix (Fin X.card) (Fin Y.card) ℝ := Matrix.of fun _ _ ↦ 1
      let B := submatrixOfFinset M X (T \ Y); let C := submatrixOfFinset M (S \ X) Y
      let D := submatrixOfFinset M (S \ X) (T \ Y)
      have hA11 : submatrixOfFinset M X Y = A₁₁ := by
        ext i j
        exact hone _ (Finset.orderEmbOfFin_mem X rfl i) _ (Finset.orderEmbOfFin_mem Y rfl j)
      rw [hA11] at hblocks
      let i₀ : Fin X.card := ⟨0, Finset.card_pos.mpr hXne⟩
      let A := Matrix.fromBlocks A₁₁ B C D
      let S₀ : Set (Fin (T \ Y).card → ℝ) := Set.range fun i : Fin X.card ↦ B.row i - B.row i₀
      have hW := span_row_lift_ker A S₀ (by
        rintro _ ⟨i, rfl⟩
        exact ⟨A.row (Sum.inl i) - A.row (Sum.inl i₀), Submodule.sub_mem _
          (Submodule.subset_span ⟨Sum.inl i, rfl⟩) (Submodule.subset_span ⟨Sum.inl i₀, rfl⟩),
          fun j ↦ by simp [A, A₁₁], funext fun _ ↦ rfl⟩)
      have hB_sub : Submodule.span ℝ (Set.range B.row) ≤
          Submodule.span ℝ S₀ ⊔ Submodule.span ℝ {B.row i₀} := by
        rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
        rw [show B.row i = (B.row i - B.row i₀) + B.row i₀ from (sub_add_cancel _ _).symm]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
          (Submodule.mem_sup_right (Submodule.subset_span rfl))
      have hB_le : B.rank ≤ Module.finrank ℝ (Submodule.span ℝ S₀) + 1 := by
        rw [Matrix.rank_eq_finrank_span_row B]
        have h1 := Submodule.finrank_mono hB_sub
        have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span ℝ S₀)
          (Submodule.span ℝ {B.row i₀})
        have h3 : Module.finrank ℝ (Submodule.span ℝ {B.row i₀}) ≤ 1 := by
          simpa using finrank_span_le_card ({B.row i₀} : Set (Fin (T \ Y).card → ℝ))
        omega
      have hle := rank_add_finrank_le_fromBlocks A₁₁ B C D (Submodule.span ℝ S₀) hW
      dsimp only [B, C, D] at hle hB_le; rw [← hblocks, Matrix.rank_submatrix] at hle
      dsimp only [submatrixOfFinset] at hle hB_le; omega

/-! ### 4. Binary Rectangle-Partition Trees and Nisan–Wigderson Leaf Bound -/

/-- Binary rectangle-partition tree over `Fin m × Fin n`, with monochromatic rectangle leaves and
internal nodes labeled by the union rectangle of their children. -/
inductive RectTree (m n : ℕ) where
  /-- A monochromatic rectangle leaf covering `rows ×ˢ cols` with constant matrix value `val`. -/
  | leaf (rows : Finset (Fin m)) (cols : Finset (Fin n)) (val : ℝ)
  /-- An internal rectangle split covering `rows ×ˢ cols` via subtrees `left` and `right`. -/
  | node (rows : Finset (Fin m)) (cols : Finset (Fin n)) (left right : RectTree m n)

/-- Row subset associated to the root of a `RectTree`. -/
def RectTree.rows {m n : ℕ} : RectTree m n → Finset (Fin m)
  | .leaf R _ _ => R | .node R _ _ _ => R

/-- Column subset associated to the root of a `RectTree`. -/
def RectTree.cols {m n : ℕ} : RectTree m n → Finset (Fin n)
  | .leaf _ C _ => C | .node _ C _ _ => C

/-- Number of leaves in a `RectTree`. -/
def RectTree.leafCount {m n : ℕ} : RectTree m n → ℕ
  | .leaf _ _ _ => 1 | .node _ _ l r => l.leafCount + r.leafCount

@[simp] lemma RectTree.rows_leaf {m n : ℕ} (R : Finset (Fin m)) (C : Finset (Fin n)) (v : ℝ) :
    (RectTree.leaf R C v).rows = R := by rfl

@[simp] lemma RectTree.rows_node {m n : ℕ} (R : Finset (Fin m)) (C : Finset (Fin n))
    (l r : RectTree m n) : (RectTree.node R C l r).rows = R := by rfl

@[simp] lemma RectTree.cols_leaf {m n : ℕ} (R : Finset (Fin m)) (C : Finset (Fin n)) (v : ℝ) :
    (RectTree.leaf R C v).cols = C := by rfl

@[simp] lemma RectTree.cols_node {m n : ℕ} (R : Finset (Fin m)) (C : Finset (Fin n))
    (l r : RectTree m n) : (RectTree.node R C l r).cols = C := by rfl

@[simp] lemma RectTree.leafCount_leaf {m n : ℕ} (R : Finset (Fin m)) (C : Finset (Fin n))
    (v : ℝ) : (RectTree.leaf R C v).leafCount = 1 := by rfl

@[simp] lemma RectTree.leafCount_node {m n : ℕ} (R : Finset (Fin m)) (C : Finset (Fin n))
    (l r : RectTree m n) : (RectTree.node R C l r).leafCount = l.leafCount + r.leafCount := by rfl

/-- Every `RectTree` has strictly positive leaf count. -/
lemma RectTree.leafCount_pos {m n : ℕ} (t : RectTree m n) : 0 < t.leafCount := by
  induction t with | leaf => simp | node _ _ _ _ ihl ihr => simp; omega

/-- Validity of a `RectTree` for a matrix `M`: every internal node partitions its rectangle into
two disjoint child rectangles, and every leaf rectangle is `M`-monochromatic. -/
def RectTree.Valid {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : RectTree m n → Prop
  | .leaf R C v => ∀ i ∈ R, ∀ j ∈ C, M i j = v
  | .node R C l r => l.rows ×ˢ l.cols ∪ r.rows ×ˢ r.cols = R ×ˢ C ∧
      Disjoint (l.rows ×ˢ l.cols) (r.rows ×ˢ r.cols) ∧ RectTree.Valid M l ∧ RectTree.Valid M r

lemma RectTree.valid_leaf {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (R : Finset (Fin m)) (C : Finset (Fin n)) (v : ℝ) :
    RectTree.Valid M (.leaf R C v) ↔ ∀ i ∈ R, ∀ j ∈ C, M i j = v := by rfl

lemma RectTree.valid_node {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (R : Finset (Fin m)) (C : Finset (Fin n)) (l r : RectTree m n) :
    RectTree.Valid M (.node R C l r) ↔ l.rows ×ˢ l.cols ∪ r.rows ×ˢ r.cols = R ×ˢ C ∧
      Disjoint (l.rows ×ˢ l.cols) (r.rows ×ˢ r.cols) ∧ RectTree.Valid M l ∧ RectTree.Valid M r := by
  rfl

private lemma rectTree_base_zero {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (hr : (submatrixOfFinset M S T).rank = 0) :
    ∃ t : RectTree m n, t.rows = S ∧ t.cols = T ∧ RectTree.Valid M t ∧ t.leafCount ≤ 4 := by
  refine ⟨.leaf S T 0, rfl, rfl, (RectTree.valid_leaf M S T 0).mpr fun i hi j hj ↦ ?_, by simp⟩
  by_contra hne
  let Q : Matrix (Fin 1) (Fin 1) ℝ := (submatrixOfFinset M S T).submatrix
    (fun _ ↦ (S.orderIsoOfFin rfl).symm ⟨i, hi⟩) (fun _ ↦ (T.orderIsoOfFin rfl).symm ⟨j, hj⟩)
  have hdet : Q.det ≠ 0 := by
    simpa [Q, Matrix.det_fin_one, submatrixOfFinset, orderEmb_orderIso_symm] using hne
  have hrank1 : Q.rank = 1 := by simpa using Matrix.rank_of_det_ne_zero hdet
  have hle : Q.rank ≤ (submatrixOfFinset M S T).rank := Matrix.rank_submatrix_le _ _ _
  omega

private lemma rectTree_base_one {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, M i j = 0 ∨ M i j = 1)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (hr : (submatrixOfFinset M S T).rank ≤ 1) :
    ∃ t : RectTree m n, t.rows = S ∧ t.cols = T ∧ RectTree.Valid M t ∧ t.leafCount ≤ 4 := by
  by_cases hzero : ∀ i ∈ S, ∀ j ∈ T, M i j = 0
  · exact ⟨.leaf S T 0, rfl, rfl, (RectTree.valid_leaf M S T 0).mpr hzero, by simp⟩
  · push Not at hzero; obtain ⟨i₀, hi₀, j₀, hj₀, hMne⟩ := hzero
    have hMone : M i₀ j₀ = 1 := (hM i₀ j₀).resolve_left hMne
    have hprod : ∀ i ∈ S, ∀ j ∈ T, M i j = M i j₀ * M i₀ j := by
      intro i hi j hj
      let Q : Matrix (Fin 2) (Fin 2) ℝ := (submatrixOfFinset M S T).submatrix
        ![(S.orderIsoOfFin rfl).symm ⟨i₀, hi₀⟩, (S.orderIsoOfFin rfl).symm ⟨i, hi⟩]
        ![(T.orderIsoOfFin rfl).symm ⟨j₀, hj₀⟩, (T.orderIsoOfFin rfl).symm ⟨j, hj⟩]
      have hdet : Q.det = 0 := by
        by_contra hne; have hrank2 : Q.rank = 2 := by simpa using Matrix.rank_of_det_ne_zero hne
        have hle : Q.rank ≤ (submatrixOfFinset M S T).rank := Matrix.rank_submatrix_le _ _ _
        omega
      rw [Matrix.det_fin_two] at hdet
      simp only [Q, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        submatrixOfFinset, orderEmb_orderIso_symm, hMone, one_mul] at hdet; linarith
    let S₁ := S.filter (fun i ↦ M i j₀ = 1); let T₁ := T.filter (fun j ↦ M i₀ j = 1)
    let t₁ := RectTree.node S₁ T (.leaf S₁ T₁ 1) (.leaf S₁ (T \ T₁) 0)
    refine ⟨RectTree.node S T t₁ (.leaf (S \ S₁) T 0), rfl, rfl, ?_, by simp [t₁]⟩
    rw [RectTree.valid_node]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [t₁, RectTree.rows_node, RectTree.cols_node, RectTree.rows_leaf,
        RectTree.cols_leaf, ← Finset.union_product]
      rw [Finset.union_sdiff_of_subset (Finset.filter_subset _ S)]
    · simpa [t₁] using Finset.disjoint_product.mpr
        (Or.inl (disjoint_sdiff_self_right (x := S₁) (y := S)))
    · rw [RectTree.valid_node]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [RectTree.rows_leaf, RectTree.cols_leaf, ← Finset.product_union]
        rw [Finset.union_sdiff_of_subset (Finset.filter_subset _ T)]
      · exact Finset.disjoint_product.mpr (Or.inr (disjoint_sdiff_self_right (x := T₁) (y := T)))
      · rw [RectTree.valid_leaf]
        intro i hi j hj
        rw [hprod i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1,
          (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2, mul_one]
      · rw [RectTree.valid_leaf]
        intro i hi j hj
        have hj0 := (hM i₀ j).resolve_right fun h1 ↦
          (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, h1⟩)
        rw [hprod i (Finset.mem_filter.mp hi).1 j (Finset.mem_sdiff.mp hj).1, hj0, mul_zero]
    · rw [RectTree.valid_leaf]
      intro i hi j hj
      have hi0 := (hM i j₀).resolve_right fun h1 ↦
        (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, h1⟩)
      rw [hprod i (Finset.mem_sdiff.mp hi).1 j hj, hi0, zero_mul]

private noncomputable def rectPotential (A : ℕ) : ℝ :=
  (Nat.log 2 A : ℝ) + (A : ℝ) / (2 : ℝ) ^ Nat.log 2 A - 1

private lemma rectPotential_nonneg {A : ℕ} (hA : 0 < A) : 0 ≤ rectPotential A := by
  have hdiv : 1 ≤ (A : ℝ) / (2 : ℝ) ^ Nat.log 2 A :=
    (one_le_div (by positivity)).mpr (by exact_mod_cast Nat.pow_log_le_self 2 hA.ne')
  dsimp [rectPotential]; linarith [show (0 : ℝ) ≤ (Nat.log 2 A : ℝ) from Nat.cast_nonneg _]

private lemma rectPotential_le_of_le_pow {A s : ℕ} (hA : 0 < A) (hAs : A ≤ 2 ^ s) :
    rectPotential A ≤ (s : ℝ) := by
  by_cases heq : A = 2 ^ s
  · subst heq; dsimp [rectPotential]; rw [Nat.log_pow (by norm_num) s]
    have hne : ((2 : ℝ) ^ s) ≠ 0 := by positivity
    push_cast; rw [div_self hne]; ring_nf; rfl
  · have hlog_le : (Nat.log 2 A : ℝ) ≤ (s : ℝ) - 1 := by
      have : ((Nat.log 2 A + 1 : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.log_lt_of_lt_pow hA.ne' (lt_of_le_of_ne hAs heq)
      push_cast at this; linarith
    have hA_lt : (A : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 A := by
      have h2 : (A : ℝ) < (2 : ℝ) ^ (Nat.log 2 A + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self (b := 2) (by norm_num) A
      simpa [pow_succ'] using h2
    have hdiv_lt : (A : ℝ) / (2 : ℝ) ^ Nat.log 2 A < 2 := (div_lt_iff₀ (by positivity)).mpr hA_lt
    dsimp [rectPotential]; linarith

private lemma rectPotential_sub_ge {A A' : ℕ} {D : ℝ} (hA : 0 < A) (hD : 1 ≤ D)
    (hle : A' ≤ A) (hdec : (A' : ℝ) ≤ (A : ℝ) * (1 - 1 / D)) :
    1 / D ≤ rectPotential A - rectPotential A' := by
  set k := Nat.log 2 A; set k' := Nat.log 2 A'
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hdiff_A : (A : ℝ) / D ≤ (A : ℝ) - (A' : ℝ) := by
    have h1 : (A' : ℝ) ≤ (A : ℝ) - (A : ℝ) / D := hdec.trans_eq (by ring); linarith
  have hA_div : 1 ≤ (A : ℝ) / (2 : ℝ) ^ k :=
    (one_le_div hpow_pos).mpr (by exact_mod_cast Nat.pow_log_le_self 2 hA.ne')
  have hstep : 1 / D ≤ ((A : ℝ) - (A' : ℝ)) / (2 : ℝ) ^ k :=
    (div_le_div_of_nonneg_right hA_div (by linarith)).trans <|
      (by ring : ((A : ℝ) / (2 : ℝ) ^ k) / D = ((A : ℝ) / D) / (2 : ℝ) ^ k).trans_le
        (div_le_div_of_nonneg_right hdiff_A hpow_pos.le)
  simp only [rectPotential]
  change 1 / D ≤ (k : ℝ) + (A : ℝ) / (2 : ℝ) ^ k - 1 - ((k' : ℝ) + (A' : ℝ) / (2 : ℝ) ^ k' - 1)
  rcases Nat.eq_or_lt_of_le (Nat.log_mono_right (b := 2) hle) with hk_eq | hk_lt
  · rw [congrArg Nat.cast hk_eq, congrArg ((2 : ℝ) ^ ·) hk_eq]
    linarith [show (k : ℝ) + (A : ℝ) / (2 : ℝ) ^ k - 1 -
      ((k : ℝ) + (A' : ℝ) / (2 : ℝ) ^ k - 1) = ((A : ℝ) - (A' : ℝ)) / (2 : ℝ) ^ k by ring]
  · by_cases hk_succ : k = k' + 1
    · have hA'_lt : (A' : ℝ) < (2 : ℝ) ^ k := by
        have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) A'
        rw [Nat.succ_eq_add_one, ← hk_succ] at h1; exact_mod_cast h1
      have hpow'_ne : (2 : ℝ) ^ k' ≠ 0 := by positivity
      have hexpr : (k : ℝ) + (A : ℝ) / (2 : ℝ) ^ k - 1 - ((k' : ℝ) + (A' : ℝ) / (2 : ℝ) ^ k' - 1) =
          ((2 : ℝ) ^ k + (A : ℝ) - 2 * (A' : ℝ)) / (2 : ℝ) ^ k := by
        rw [(by exact_mod_cast hk_succ : (k : ℝ) = (k' : ℝ) + 1), hk_succ, pow_succ']
        field_simp; ring
      have := div_le_div_of_nonneg_right
        (by linarith : (A : ℝ) - (A' : ℝ) ≤ (2 : ℝ) ^ k + (A : ℝ) - 2 * (A' : ℝ)) hpow_pos.le
      linarith
    · have hA'_lt : (A' : ℝ) < 2 * (2 : ℝ) ^ k' := by
        have h2 : (A' : ℝ) < (2 : ℝ) ^ (k' + 1) := by
          exact_mod_cast Nat.lt_pow_succ_log_self (b := 2) (by norm_num) A'
        simpa [pow_succ'] using h2
      have hdiv'_lt : (A' : ℝ) / (2 : ℝ) ^ k' < 2 := (div_lt_iff₀ (by positivity)).mpr hA'_lt
      have hk'_real : (k' : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast (by omega : k' + 2 ≤ k)
      have h1D : 1 / D ≤ 1 := div_le_one_of_le₀ hD (by positivity)
      linarith

private def rankDepth : ℕ → ℕ | 0 => 0 | 1 => 0 | r + 2 => rankDepth ((r + 3) / 2) + 1
decreasing_by omega

private lemma rankDepth_le_log_add_one (r : ℕ) : rankDepth r ≤ Nat.log 2 r + 1 := by
  have haux : ∀ s : ℕ, 2 ≤ s → rankDepth s ≤ Nat.log 2 (s - 1) + 1 := by
    intro s; induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro hs; rcases s with _ | _ | s
      · omega
      · omega
      · simp only [rankDepth, Nat.add_sub_cancel]
        by_cases hlt : (s + 3) / 2 < 2
        · rcases (by omega : (s + 3) / 2 = 0 ∨ (s + 3) / 2 = 1) with h | h <;> simp [rankDepth, h]
        · have hih := ih ((s + 3) / 2) (by omega) (by omega)
          have hlog : Nat.log 2 ((s + 3) / 2 - 1) = Nat.log 2 (s + 1) - 1 := by
            rw [show (s + 3) / 2 - 1 = (s + 1) / 2 by omega, Nat.log_div_base]
          have hpos := Nat.log_pos (b := 2) (n := s + 1) (by norm_num) (by omega)
          rw [hlog] at hih; omega
  rcases r with _ | _ | r
  · simp [rankDepth]
  · simp [rankDepth]
  · exact (haux (r + 2) (by omega)).trans (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)

private lemma area_shrink_real {a b x : ℕ} {D : ℝ} (hxa : x ≤ a) (hcard : (a : ℝ) / D ≤ (x : ℝ)) :
    (((a - x) * b : ℕ) : ℝ) ≤ ((a * b : ℕ) : ℝ) * (1 - 1 / D) := by
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hxa]
  have h1 : (a : ℝ) - (x : ℝ) ≤ (a : ℝ) * (1 - 1 / D) := by
    linarith [show (a : ℝ) * (1 - 1 / D) = (a : ℝ) - (a : ℝ) / D by ring]
  calc ((a : ℝ) - (x : ℝ)) * (b : ℝ) ≤ ((a : ℝ) * (1 - 1 / D)) * (b : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
    _ = ((a : ℝ) * (b : ℝ)) * (1 - 1 / D) := by ring

private lemma rectTree_valid_branch {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {S₁ X : Finset (Fin m)} {T₁ Y : Finset (Fin n)} {val : ℝ} {t_ar t_rk : RectTree m n}
    (hXS : X ⊆ S₁) (hYT : Y ⊆ T₁) (hmono : ∀ i ∈ X, ∀ j ∈ Y, M i j = val)
    (rowSplit : Bool) :
    (rowSplit = true → t_ar.rows = S₁ \ X ∧ t_ar.cols = T₁ ∧ RectTree.Valid M t_ar ∧
      t_rk.rows = X ∧ t_rk.cols = T₁ \ Y ∧ RectTree.Valid M t_rk →
      RectTree.Valid M (.node S₁ T₁ t_ar (.node X T₁ (.leaf X Y val) t_rk))) ∧
    (rowSplit = false → t_ar.rows = S₁ ∧ t_ar.cols = T₁ \ Y ∧ RectTree.Valid M t_ar ∧
      t_rk.rows = S₁ \ X ∧ t_rk.cols = Y ∧ RectTree.Valid M t_rk →
      RectTree.Valid M (.node S₁ T₁ t_ar (.node S₁ Y (.leaf X Y val) t_rk))) := by
  refine ⟨fun _ ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ?_, fun _ ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ?_⟩
  · rw [RectTree.valid_node]
    refine ⟨?_, ?_, h3, ?_⟩
    · simp [h1, h2, ← Finset.union_product, Finset.sdiff_union_of_subset hXS]
    · simpa [h1, h2] using
        Finset.disjoint_product.mpr (Or.inl (disjoint_sdiff_self_left (x := X) (y := S₁)))
    · rw [RectTree.valid_node]
      refine ⟨?_, ?_, hmono, h6⟩
      · simp [h4, h5, ← Finset.product_union, Finset.union_sdiff_of_subset hYT]
      · simpa [h4, h5] using
          Finset.disjoint_product.mpr (Or.inr (disjoint_sdiff_self_right (x := Y) (y := T₁)))
  · rw [RectTree.valid_node]
    refine ⟨?_, ?_, h3, ?_⟩
    · simp [h1, h2, ← Finset.product_union, Finset.sdiff_union_of_subset hYT]
    · simpa [h1, h2] using
        Finset.disjoint_product.mpr (Or.inr (disjoint_sdiff_self_left (x := Y) (y := T₁)))
    · rw [RectTree.valid_node]
      refine ⟨?_, ?_, hmono, h6⟩
      · simp [h4, h5, ← Finset.union_product, Finset.union_sdiff_of_subset hXS]
      · simpa [h4, h5] using
          Finset.disjoint_product.mpr (Or.inl (disjoint_sdiff_self_right (x := X) (y := S₁)))

private lemma rectTree_outer_step {r r₀ : ℕ} {c₁ : ℝ} (hr₀ : 1 ≤ r₀) (hc₁ : 0 ≤ c₁) (hr2 : 2 ≤ r)
    {A : ℕ} (hA_le : A ≤ 2 ^ (2 * r₀)) {leaf : ℕ}
    (hle : (leaf : ℝ) + 1 ≤ 2 + (if A = 0 then 0 else
      (rectPotential A * (2 : ℝ) ^ (c₁ * Real.sqrt r) + 1) *
        (5 * (4 * (r₀ : ℝ)) ^ rankDepth ((r + 1) / 2) *
          (2 : ℝ) ^ (8 * c₁ * Real.sqrt (((r + 1) / 2 : ℕ) : ℝ))))) :
    (leaf : ℝ) + 1 ≤ 5 * (4 * (r₀ : ℝ)) ^ rankDepth r * (2 : ℝ) ^ (8 * c₁ * Real.sqrt r) := by
  let r' := (r + 1) / 2; let D_r := (2 : ℝ) ^ (c₁ * Real.sqrt r)
  let B_prev := 5 * (4 * (r₀ : ℝ)) ^ rankDepth r' * (2 : ℝ) ^ (8 * c₁ * Real.sqrt (r' : ℝ))
  have hD_r_ge : 1 ≤ D_r := Real.one_le_rpow (by norm_num) (by positivity)
  have hr₀_ge : (1 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have hB_prev_ge : 2 ≤ B_prev := by
    have h4r₀ : 1 ≤ (4 * (r₀ : ℝ)) ^ rankDepth r' := one_le_pow₀ (by linarith)
    have h2pow : 1 ≤ (2 : ℝ) ^ (8 * c₁ * Real.sqrt r') :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have : 5 ≤ B_prev := by dsimp [B_prev]; nlinarith
    linarith
  have hsqrt_le : Real.sqrt (r' : ℝ) ≤ (7 / 8 : ℝ) * Real.sqrt (r : ℝ) := by
    refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    have : 4 * (r' : ℝ) ≤ 3 * (r : ℝ) := by exact_mod_cast (by dsimp [r']; omega : 4 * r' ≤ 3 * r)
    linarith
  have hrdepth : rankDepth r = rankDepth r' + 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr2; simp [rankDepth, r']
  have hrpow_mul : D_r * (2 : ℝ) ^ (8 * c₁ * Real.sqrt r') ≤ (2 : ℝ) ^ (8 * c₁ * Real.sqrt r) := by
    dsimp [D_r]; rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have := mul_le_mul_of_nonneg_left hsqrt_le (by positivity : 0 ≤ 8 * c₁); linarith)
  have hbound : 2 + (if A = 0 then 0 else (rectPotential A * D_r + 1) * B_prev) ≤
      (4 * (r₀ : ℝ) * D_r) * B_prev := by
    by_cases hA0 : A = 0
    · simp only [hA0, ↓reduceIte, add_zero]; have : 1 ≤ 4 * (r₀ : ℝ) * D_r := by nlinarith
      nlinarith
    · simp only [hA0, ↓reduceIte]
      have hpot : rectPotential A ≤ 2 * (r₀ : ℝ) := by
        simpa using rectPotential_le_of_le_pow (Nat.pos_of_ne_zero hA0) hA_le
      have hcoef : rectPotential A * D_r + 1 ≤ 2 * (r₀ : ℝ) * D_r + 1 := by nlinarith
      have h2le : (2 : ℝ) ≤ 2 * (r₀ : ℝ) * D_r := by nlinarith
      calc 2 + (rectPotential A * D_r + 1) * B_prev
          ≤ B_prev + (2 * (r₀ : ℝ) * D_r + 1) * B_prev := by nlinarith
        _ = (2 * (r₀ : ℝ) * D_r + 2) * B_prev := by ring
        _ ≤ (4 * (r₀ : ℝ) * D_r) * B_prev := by nlinarith
  calc (leaf : ℝ) + 1 ≤ 2 + (if A = 0 then 0 else (rectPotential A * D_r + 1) * B_prev) := hle
    _ ≤ (4 * (r₀ : ℝ) * D_r) * B_prev := hbound
    _ = 5 * (4 * (r₀ : ℝ)) ^ rankDepth r * (D_r * (2 : ℝ) ^ (8 * c₁ * Real.sqrt r')) := by
        dsimp [B_prev]; rw [hrdepth, pow_succ']; ring
    _ ≤ 5 * (4 * (r₀ : ℝ)) ^ rankDepth r * (2 : ℝ) ^ (8 * c₁ * Real.sqrt r) := by gcongr

private lemma log_add_three_sq_le_sqrt (r : ℕ) (hr : 1 ≤ r) :
    ((Nat.log 2 r + 3 : ℕ) : ℝ) ^ 2 ≤ 64 * Real.sqrt r := by
  have h1 : ∀ k : ℕ, ((k + 3 : ℕ) : ℝ) ^ 2 ≤ 64 * Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
    intro k
    have hpow : (((k + 3 : ℕ) : ℝ) ^ 2) ^ 2 ≤ (64 * Real.sqrt ((2 ^ k : ℕ) : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have hnat : (k + 3) ^ 4 ≤ 4096 * 2 ^ k := by
        induction k with
        | zero => norm_num
        | succ k ih =>
          rcases k with _ | _ | _ | k
          · norm_num
          · norm_num
          · norm_num
          · have hstep : (k + 7) ^ 4 ≤ 2 * (k + 6) ^ 4 := by
              have : 2 * (k + 6) ^ 4 =
                  (k + 7) ^ 4 + (k ^ 4 + 20 * k ^ 3 + 138 * k ^ 2 + 356 * k + 191) := by ring
              omega
            calc (k + 3 + 1 + 3) ^ 4 = (k + 7) ^ 4 := by ring_nf
              _ ≤ 2 * (k + 6) ^ 4 := hstep
              _ ≤ 2 * (4096 * 2 ^ (k + 3)) := Nat.mul_le_mul_left 2 ih
              _ = 4096 * 2 ^ (k + 3 + 1) := by ring
      have : (((k + 3 : ℕ) : ℝ) ^ 4) ≤ (4096 : ℝ) * ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith [show (((k + 3 : ℕ) : ℝ) ^ 2) ^ 2 = ((k + 3 : ℕ) : ℝ) ^ 4 by ring,
        show (64 : ℝ) ^ 2 = 4096 by norm_num]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hpow
  exact (h1 (Nat.log 2 r)).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : r ≠ 0)))
    (by norm_num))

private lemma exists_rectTree_ind {m n r₀ : ℕ} (hr₀ : 1 ≤ r₀) (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : ∀ i j, M i j = 0 ∨ M i j = 1) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hmono_bound : ∀ {a b s : ℕ} (N : Matrix (Fin a) (Fin b) ℝ),
      (∀ i j, N i j = 0 ∨ N i j = 1) → N.rank ≤ s →
      ∃ (X : Finset (Fin a)) (Y : Finset (Fin b)),
        (a : ℝ) / (2 : ℝ) ^ (c₁ * Real.sqrt s) ≤ (X.card : ℝ) ∧
        (b : ℝ) / (2 : ℝ) ^ (c₁ * Real.sqrt s) ≤ (Y.card : ℝ) ∧
        ((∀ i ∈ X, ∀ j ∈ Y, N i j = 0) ∨ (∀ i ∈ X, ∀ j ∈ Y, N i j = 1))) :
    ∀ (r : ℕ) (S : Finset (Fin m)) (T : Finset (Fin n)),
      S.card * T.card ≤ 2 ^ (2 * r₀) → (submatrixOfFinset M S T).rank ≤ r →
      ∃ t : RectTree m n, t.rows = S ∧ t.cols = T ∧ RectTree.Valid M t ∧
        (t.leafCount : ℝ) + 1 ≤
          5 * (4 * (r₀ : ℝ)) ^ rankDepth r * (2 : ℝ) ^ (8 * c₁ * Real.sqrt r) := by
  intro r; induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro S T harea hr
    by_cases hr1 : r ≤ 1
    · obtain ⟨t, htR, htC, htV, htL⟩ :=
        (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with rfl | rfl
            · exact rectTree_base_zero M S T (Nat.eq_zero_of_le_zero hr)
            · exact rectTree_base_one M hM S T hr :
          ∃ t : RectTree m n, t.rows = S ∧ t.cols = T ∧ RectTree.Valid M t ∧ t.leafCount ≤ 4)
      have hrdepth : rankDepth r = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with rfl | rfl <;> simp [rankDepth]
      refine ⟨t, htR, htC, htV, ?_⟩; rw [hrdepth, pow_zero, mul_one]
      have hpow_ge : 1 ≤ (2 : ℝ) ^ (8 * c₁ * Real.sqrt r) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have htL_real : (t.leafCount : ℝ) + 1 ≤ 5 := by exact_mod_cast Nat.add_le_add_right htL 1
      linarith
    · have hr2 : 2 ≤ r := by omega
      let r' := (r + 1) / 2; have hr'_lt : r' < r := by omega
      let D_r := (2 : ℝ) ^ (c₁ * Real.sqrt r)
      let B_prev := 5 * (4 * (r₀ : ℝ)) ^ rankDepth r' * (2 : ℝ) ^ (8 * c₁ * Real.sqrt (r' : ℝ))
      have hD_r_ge : 1 ≤ D_r := Real.one_le_rpow (by norm_num) (by positivity)
      have hD_r_pos : 0 < D_r := by positivity
      have hB_prev_nn : 0 ≤ B_prev := by positivity
      have hinner : ∀ (A : ℕ) (S₁ : Finset (Fin m)) (T₁ : Finset (Fin n)),
          S₁.card * T₁.card = A → A ≤ 2 ^ (2 * r₀) → (submatrixOfFinset M S₁ T₁).rank ≤ r →
          ∃ t : RectTree m n, t.rows = S₁ ∧ t.cols = T₁ ∧ RectTree.Valid M t ∧
            (t.leafCount : ℝ) + 1 ≤ 2 + (if A = 0 then 0 else
              (rectPotential A * D_r + 1) * B_prev) := by
        intro A; induction A using Nat.strong_induction_on with
        | ind A ihA =>
          intro S₁ T₁ hA hA_le hr₁
          by_cases hA0 : A = 0
          · subst hA0; simp only [↓reduceIte, add_zero]
            have hST0 : S₁ = ∅ ∨ T₁ = ∅ := by
              rcases mul_eq_zero.mp hA with hS | hT
              · exact Or.inl (Finset.card_eq_zero.mp hS)
              · exact Or.inr (Finset.card_eq_zero.mp hT)
            refine ⟨.leaf S₁ T₁ 0, rfl, rfl, (RectTree.valid_leaf M S₁ T₁ 0).mpr fun i hi j hj ↦ ?_,
              by norm_num⟩
            rcases hST0 with rfl | rfl <;> simp at hi hj
          · have hA_pos : 0 < A := Nat.pos_of_ne_zero hA0
            have hS₁_pos : 0 < S₁.card := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hA; omega
            have hT₁_pos : 0 < T₁.card := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hA; omega
            obtain ⟨X₀, Y₀, hX₀, hY₀, hmono₀⟩ := hmono_bound (submatrixOfFinset M S₁ T₁)
              (fun i j ↦ hM _ _) hr₁
            obtain ⟨X, Y, val, hXS, hYT, hXpos, hYpos, hXcard, hYcard, hmono, hmono01⟩ :
                ∃ (X : Finset (Fin m)) (Y : Finset (Fin n)) (val : ℝ), X ⊆ S₁ ∧ Y ⊆ T₁ ∧
                  0 < X.card ∧ 0 < Y.card ∧ (S₁.card : ℝ) / D_r ≤ (X.card : ℝ) ∧
                  (T₁.card : ℝ) / D_r ≤ (Y.card : ℝ) ∧ (∀ i ∈ X, ∀ j ∈ Y, M i j = val) ∧
                  ((∀ i ∈ X, ∀ j ∈ Y, M i j = 0) ∨ (∀ i ∈ X, ∀ j ∈ Y, M i j = 1)) := by
              rcases hmono₀ with h0 | h1
              · obtain ⟨X, Y, hXS, hYT, hXc, hYc, hm⟩ := lift_mono h0
                have hXc' : (S₁.card : ℝ) / D_r ≤ (X.card : ℝ) := by rwa [hXc]
                have hYc' : (T₁.card : ℝ) / D_r ≤ (Y.card : ℝ) := by rwa [hYc]
                exact ⟨X, Y, 0, hXS, hYT,
                  Nat.cast_pos.mp (lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr hS₁_pos) hD_r_pos)
                    hXc'),
                  Nat.cast_pos.mp (lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr hT₁_pos) hD_r_pos)
                    hYc'),
                  hXc', hYc', hm, Or.inl hm⟩
              · obtain ⟨X, Y, hXS, hYT, hXc, hYc, hm⟩ := lift_mono h1
                have hXc' : (S₁.card : ℝ) / D_r ≤ (X.card : ℝ) := by rwa [hXc]
                have hYc' : (T₁.card : ℝ) / D_r ≤ (Y.card : ℝ) := by rwa [hYc]
                exact ⟨X, Y, 1, hXS, hYT,
                  Nat.cast_pos.mp (lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr hS₁_pos) hD_r_pos)
                    hXc'),
                  Nat.cast_pos.mp (lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr hT₁_pos) hD_r_pos)
                    hYc'),
                  hXc', hYc', hm, Or.inr hm⟩
            have hstep_sub : ∀ {A' : ℕ} (hA'_le : A' ≤ A)
                (hdec : (A' : ℝ) ≤ (A : ℝ) * (1 - 1 / D_r)),
                (if A' = 0 then (0 : ℝ) else (rectPotential A' * D_r + 1) * B_prev) + B_prev ≤
                  (rectPotential A * D_r + 1) * B_prev := fun {A'} hA'_le hdec ↦ by
              by_cases hA'0 : A' = 0
              · simp only [hA'0, ↓reduceIte, zero_add]
                have hnn : 0 ≤ rectPotential A * D_r := mul_nonneg (rectPotential_nonneg hA_pos)
                  hD_r_pos.le
                nlinarith
              · simp only [hA'0, ↓reduceIte]
                have hpot_diff := rectPotential_sub_ge hA_pos hD_r_ge hA'_le hdec
                have hmul : 1 ≤ (rectPotential A - rectPotential A') * D_r := by
                  have h := mul_le_mul_of_nonneg_right hpot_diff hD_r_pos.le
                  rwa [one_div_mul_cancel hD_r_pos.ne'] at h
                nlinarith
            rcases min_rank_le_half_succ_of_monochromatic M hXS hYT hmono01 hr₁ with hrow | hcol
            · let A' := (S₁ \ X).card * T₁.card
              have hA'_lt : A' < A := by
                have h1 : (S₁ \ X).card < S₁.card := by
                  rw [Finset.card_sdiff_of_subset hXS]; omega
                exact hA ▸ Nat.mul_lt_mul_of_pos_right h1 hT₁_pos
              obtain ⟨t_ar, h1, h2, h3, h4⟩ := ihA A' hA'_lt (S₁ \ X) T₁ rfl
                (hA'_lt.le.trans hA_le) ((rank_submatrixOfFinset_le_of_subset M
                  Finset.sdiff_subset (Finset.Subset.refl T₁)).trans hr₁)
              obtain ⟨t_rk, h5, h6, h7, h8⟩ := ih r' hr'_lt X (T₁ \ Y)
                ((Nat.mul_le_mul (Finset.card_le_card hXS)
                  (Finset.card_le_card Finset.sdiff_subset)).trans (hA ▸ hA_le)) hrow
              have hdec : (A' : ℝ) ≤ (A : ℝ) * (1 - 1 / D_r) := by
                dsimp [A']; rw [Finset.card_sdiff_of_subset hXS, ← hA]
                exact area_shrink_real (Finset.card_le_card hXS) hXcard
              refine ⟨.node S₁ T₁ t_ar (.node X T₁ (.leaf X Y val) t_rk), rfl, rfl,
                (rectTree_valid_branch hXS hYT hmono true).1 rfl ⟨h1, h2, h3, h5, h6, h7⟩, ?_⟩
              simp only [hA0, ↓reduceIte, RectTree.leafCount_node, RectTree.leafCount_leaf,
                Nat.cast_add, Nat.cast_one]
              linarith [hstep_sub hA'_lt.le hdec]
            · let A' := S₁.card * (T₁ \ Y).card
              have hA'_lt : A' < A := by
                have h1 : (T₁ \ Y).card < T₁.card := by
                  rw [Finset.card_sdiff_of_subset hYT]; omega
                exact hA ▸ Nat.mul_lt_mul_of_pos_left h1 hS₁_pos
              obtain ⟨t_ar, h1, h2, h3, h4⟩ := ihA A' hA'_lt S₁ (T₁ \ Y) rfl
                (hA'_lt.le.trans hA_le) ((rank_submatrixOfFinset_le_of_subset M
                  (Finset.Subset.refl S₁) Finset.sdiff_subset).trans hr₁)
              obtain ⟨t_rk, h5, h6, h7, h8⟩ := ih r' hr'_lt (S₁ \ X) Y
                ((Nat.mul_le_mul (Finset.card_le_card Finset.sdiff_subset)
                  (Finset.card_le_card hYT)).trans (hA ▸ hA_le)) hcol
              have hdec : (A' : ℝ) ≤ (A : ℝ) * (1 - 1 / D_r) := by
                dsimp [A']; rw [Finset.card_sdiff_of_subset hYT, ← hA, mul_comm S₁.card,
                  mul_comm S₁.card]
                exact area_shrink_real (Finset.card_le_card hYT) hYcard
              refine ⟨.node S₁ T₁ t_ar (.node S₁ Y (.leaf X Y val) t_rk), rfl, rfl,
                (rectTree_valid_branch hXS hYT hmono false).2 rfl ⟨h1, h2, h3, h5, h6, h7⟩, ?_⟩
              simp only [hA0, ↓reduceIte, RectTree.leafCount_node, RectTree.leafCount_leaf,
                Nat.cast_add, Nat.cast_one]
              linarith [hstep_sub hA'_lt.le hdec]
      obtain ⟨t, htR, htC, htV, htL⟩ := hinner (S.card * T.card) S T rfl harea hr
      exact ⟨t, htR, htC, htV, rectTree_outer_step hr₀ hc₁.le hr2 harea htL⟩

/-- **Nisan–Wigderson leaf-count bound**: given any universal constant `c₁ > 0` such that every
`a × b` binary matrix of rank at most `s` has a monochromatic submatrix of dimensions at least
`a / 2 ^ (c₁ * √s)` by `b / 2 ^ (c₁ * √s)`, there exists `C > 0` such that every `m × n` binary
matrix `M` with `m ≤ 2 ^ r`, `n ≤ 2 ^ r`, and `M.rank ≤ r` admits a valid `RectTree` with
`Nat.log 2 t.leafCount ≤ C * Real.sqrt r + C`. -/
theorem exists_rectTree_of_rank_le_of_monochromatic_sqrt {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hmono_bound : ∀ {a b s : ℕ} (N : Matrix (Fin a) (Fin b) ℝ),
      (∀ i j, N i j = 0 ∨ N i j = 1) → N.rank ≤ s →
      ∃ (X : Finset (Fin a)) (Y : Finset (Fin b)),
        (a : ℝ) / (2 : ℝ) ^ (c₁ * Real.sqrt s) ≤ (X.card : ℝ) ∧
        (b : ℝ) / (2 : ℝ) ^ (c₁ * Real.sqrt s) ≤ (Y.card : ℝ) ∧
        ((∀ i ∈ X, ∀ j ∈ Y, N i j = 0) ∨ (∀ i ∈ X, ∀ j ∈ Y, N i j = 1))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℝ),
        (∀ i j, M i j = 0 ∨ M i j = 1) → m ≤ 2 ^ r → n ≤ 2 ^ r → M.rank ≤ r →
        ∃ t : RectTree m n, t.rows = Finset.univ ∧ t.cols = Finset.univ ∧
          RectTree.Valid M t ∧ (Nat.log 2 t.leafCount : ℝ) ≤ C * Real.sqrt r + C := by
  refine ⟨8 * c₁ + 64, by positivity, fun {m n r₀} M hM hm hn hr₀ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos r₀ with rfl | hr₀_pos
  · obtain ⟨t, htR, htC, htV, htL⟩ := rectTree_base_zero M Finset.univ Finset.univ
      (Nat.eq_zero_of_le_zero ((Matrix.rank_submatrix_le M _ _).trans hr₀))
    refine ⟨t, htR, htC, htV, ?_⟩
    have hlog : Nat.log 2 t.leafCount ≤ 2 :=
      (Nat.log_mono_right htL).trans (by decide : Nat.log 2 4 ≤ 2)
    have hlogR : (Nat.log 2 t.leafCount : ℝ) ≤ 2 := by exact_mod_cast hlog
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add]; linarith
  · have harea : (Finset.univ : Finset (Fin m)).card * (Finset.univ : Finset (Fin n)).card ≤
        2 ^ (2 * r₀) := by
      simp only [Finset.card_univ, Fintype.card_fin]
      exact (Nat.mul_le_mul hm hn).trans (by rw [two_mul, pow_add])
    obtain ⟨t, htR, htC, htV, htL⟩ := exists_rectTree_ind hr₀_pos M hM hc₁ hmono_bound
      r₀ Finset.univ Finset.univ harea ((Matrix.rank_submatrix_le M _ _).trans hr₀)
    have h4r₀ : 4 * r₀ ≤ 2 ^ (Nat.log 2 r₀ + 3) := by
      have h1 := (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) r₀).le
      calc 4 * r₀ ≤ 4 * 2 ^ (Nat.log 2 r₀ + 1) := Nat.mul_le_mul_left 4 h1
        _ = 2 ^ (Nat.log 2 r₀ + 3) := by rw [pow_add, pow_add]; norm_num; ring
    have hpow_d : (4 * (r₀ : ℝ)) ^ rankDepth r₀ ≤ (2 : ℝ) ^ (64 * Real.sqrt r₀) := by
      have h1 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast h4r₀ :
        4 * (r₀ : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 r₀ + 3)) (rankDepth r₀)
      have h2 : ((2 : ℝ) ^ (Nat.log 2 r₀ + 3)) ^ rankDepth r₀ =
          (2 : ℝ) ^ (((Nat.log 2 r₀ + 3) * rankDepth r₀ : ℕ) : ℝ) := by
        rw [← pow_mul, Real.rpow_natCast]
      have hmul_le : (Nat.log 2 r₀ + 3) * rankDepth r₀ ≤ (Nat.log 2 r₀ + 3) ^ 2 := by
        have hd_le := (rankDepth_le_log_add_one r₀).trans
          (by omega : Nat.log 2 r₀ + 1 ≤ Nat.log 2 r₀ + 3)
        exact (Nat.mul_le_mul_left _ hd_le).trans_eq (by ring)
      have hexp_le : (((Nat.log 2 r₀ + 3) * rankDepth r₀ : ℕ) : ℝ) ≤ 64 * Real.sqrt r₀ :=
        (by exact_mod_cast hmul_le : (((Nat.log 2 r₀ + 3) * rankDepth r₀ : ℕ) : ℝ) ≤
          ((Nat.log 2 r₀ + 3 : ℕ) : ℝ) ^ 2).trans (log_add_three_sq_le_sqrt r₀ hr₀_pos)
      exact h1.trans (h2 ▸ Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
    have hleaf_rpow : (t.leafCount : ℝ) ≤ (2 : ℝ) ^ ((8 * c₁ + 64) * Real.sqrt r₀ + 3) := by
      calc (t.leafCount : ℝ) ≤ (t.leafCount : ℝ) + 1 := by linarith
        _ ≤ 5 * (4 * (r₀ : ℝ)) ^ rankDepth r₀ * (2 : ℝ) ^ (8 * c₁ * Real.sqrt r₀) := htL
        _ ≤ (2 : ℝ) ^ (3 : ℝ) * (2 : ℝ) ^ (64 * Real.sqrt r₀) *
            (2 : ℝ) ^ (8 * c₁ * Real.sqrt r₀) := by gcongr; norm_num
        _ = (2 : ℝ) ^ ((8 * c₁ + 64) * Real.sqrt r₀ + 3) := by
            rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; congr 1; ring
    have hlog_pow : (2 : ℝ) ^ (Nat.log 2 t.leafCount : ℝ) ≤ (t.leafCount : ℝ) := by
      rw [Real.rpow_natCast]; exact_mod_cast Nat.pow_log_le_self 2 t.leafCount_pos.ne'
    have hfinal : (Nat.log 2 t.leafCount : ℝ) ≤ (8 * c₁ + 64) * Real.sqrt r₀ + (8 * c₁ + 64) := by
      by_contra! hgt
      linarith [Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (by linarith : (8 * c₁ + 64) * Real.sqrt r₀ + 3 < (Nat.log 2 t.leafCount : ℝ))]
    exact ⟨t, htR, htC, htV, hfinal⟩

/-! ### 5. Spira Rebalancing to `Cslib.Communication.Protocol` -/

private def RectTree.leafPaths {m n : ℕ} : RectTree m n → Finset (List Bool)
  | .leaf _ _ _ => {[]}
  | .node _ _ l r => (l.leafPaths.image (false :: ·)) ∪ (r.leafPaths.image (true :: ·))

private lemma RectTree.card_leafPaths {m n : ℕ} (t : RectTree m n) :
    t.leafPaths.card = t.leafCount := by
  induction t with
  | leaf => simp [RectTree.leafPaths]
  | node _ _ l r ihl ihr =>
    rw [RectTree.leafPaths, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ List.cons_injective,
        Finset.card_image_of_injective _ List.cons_injective, ihl, ihr, RectTree.leafCount_node]
    · rw [Finset.disjoint_left]; rintro q hql hqr; rw [Finset.mem_image] at hql hqr
      obtain ⟨_, _, rfl⟩ := hql; obtain ⟨_, _, h⟩ := hqr; exact Bool.noConfusion (List.cons.inj h).1

private def RectTree.lookupLeaf {m n : ℕ} :
    RectTree m n → List Bool → Finset (Fin m) × Finset (Fin n) × ℝ
  | .leaf R C v, _ => (R, C, v) | .node _ _ l _, false :: rest => l.lookupLeaf rest
  | .node _ _ _ r, true :: rest => r.lookupLeaf rest | .node R C _ _, [] => (R, C, 0)

private def RectTree.subtree {m n : ℕ} : RectTree m n → List Bool → RectTree m n
  | t, [] => t | .leaf R C v, _ => .leaf R C v
  | .node _ _ l _, false :: rest => l.subtree rest | .node _ _ _ r, true :: rest => r.subtree rest

private lemma RectTree.exists_mem_lookupLeaf_of_valid {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t) {x : Fin m} {y : Fin n}
    (hx : x ∈ t.rows) (hy : y ∈ t.cols) :
    ∃ q ∈ t.leafPaths, x ∈ (t.lookupLeaf q).1 ∧ y ∈ (t.lookupLeaf q).2.1 := by
  induction t with
  | leaf => exact ⟨[], Finset.mem_singleton_self [], hx, hy⟩
  | node R C l r ihl ihr =>
    rw [RectTree.valid_node] at ht
    have hxy : (x, y) ∈ R ×ˢ C := Finset.mem_product.mpr ⟨hx, hy⟩
    rw [← ht.1, Finset.mem_union] at hxy
    rcases hxy with hxyL | hxyR
    · obtain ⟨hxL, hyL⟩ := Finset.mem_product.mp hxyL
      obtain ⟨q, hq, hxq, hyq⟩ := ihl ht.2.2.1 hxL hyL
      exact ⟨false :: q, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq), hxq, hyq⟩
    · obtain ⟨hxR, hyR⟩ := Finset.mem_product.mp hxyR
      obtain ⟨q, hq, hxq, hyq⟩ := ihr ht.2.2.2 hxR hyR
      exact ⟨true :: q, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq), hxq, hyq⟩

private lemma RectTree.valid_lookupLeaf {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t) {q : List Bool} (hq : q ∈ t.leafPaths) :
    ∀ i ∈ (t.lookupLeaf q).1, ∀ j ∈ (t.lookupLeaf q).2.1, M i j = (t.lookupLeaf q).2.2 := by
  induction t generalizing q with
  | leaf => simpa [RectTree.lookupLeaf, RectTree.valid_leaf] using ht
  | node _ _ l r ihl ihr =>
    rw [RectTree.valid_node] at ht; simp only [RectTree.leafPaths, Finset.mem_union,
      Finset.mem_image] at hq
    rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · exact ihl ht.2.2.1 hq'
    · exact ihr ht.2.2.2 hq'

private lemma RectTree.lookupLeaf_subset_root {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t) {q : List Bool} (hq : q ∈ t.leafPaths) :
    (t.lookupLeaf q).1 ×ˢ (t.lookupLeaf q).2.1 ⊆ t.rows ×ˢ t.cols := by
  induction t generalizing q with
  | leaf => simp [RectTree.lookupLeaf]
  | node _ _ l r ihl ihr =>
    rw [RectTree.valid_node] at ht; simp only [RectTree.leafPaths, Finset.mem_union,
      Finset.mem_image] at hq
    rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · exact (ihl ht.2.2.1 hq').trans (ht.1 ▸ Finset.subset_union_left)
    · exact (ihr ht.2.2.2 hq').trans (ht.1 ▸ Finset.subset_union_right)

private lemma RectTree.subtree_subset_root {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t) (p : List Bool) :
    (t.subtree p).rows ×ˢ (t.subtree p).cols ⊆ t.rows ×ˢ t.cols := by
  induction t generalizing p with
  | leaf => cases p <;> simp [RectTree.subtree]
  | node _ _ l r ihl ihr =>
    rw [RectTree.valid_node] at ht; cases p with
    | nil => simp [RectTree.subtree]
    | cons b rest =>
      cases b
      · exact (ihl ht.2.2.1 rest).trans (ht.1 ▸ Finset.subset_union_left)
      · exact (ihr ht.2.2.2 rest).trans (ht.1 ▸ Finset.subset_union_right)

private lemma RectTree.rect_prefix_and_disjoint {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t) {p : List Bool}
    (hp : ∃ q₀ ∈ t.leafPaths, p <+: q₀) {q : List Bool} (hq : q ∈ t.leafPaths) :
    (p <+: q →
      (t.lookupLeaf q).1 ×ˢ (t.lookupLeaf q).2.1 ⊆ (t.subtree p).rows ×ˢ (t.subtree p).cols) ∧
    (¬ p <+: q → Disjoint ((t.lookupLeaf q).1 ×ˢ (t.lookupLeaf q).2.1)
      ((t.subtree p).rows ×ˢ (t.subtree p).cols)) := by
  induction t generalizing p q with
  | leaf =>
    obtain ⟨q₀, hq₀, hpq₀⟩ := hp; simp only [RectTree.leafPaths, Finset.mem_singleton] at hq₀ hq
    subst hq₀; subst hq; obtain rfl : p = [] := List.eq_nil_of_prefix_nil hpq₀
    simp [RectTree.subtree, RectTree.lookupLeaf]
  | node R C l r ihl ihr =>
    rw [RectTree.valid_node] at ht; rcases ht with ⟨hcov, hdisj, hvl, hvr⟩
    cases p with
    | nil => exact ⟨fun _ ↦ RectTree.lookupLeaf_subset_root
        (by rw [RectTree.valid_node]; exact ⟨hcov, hdisj, hvl, hvr⟩) hq,
        fun hnot ↦ False.elim (hnot List.nil_prefix)⟩
    | cons b p' =>
      obtain ⟨q₀, hq₀, hpq₀⟩ := hp
      simp only [RectTree.leafPaths, Finset.mem_union, Finset.mem_image] at hq₀ hq
      cases b
      · have hp'_l : ∃ q₀' ∈ l.leafPaths, p' <+: q₀' := by
          rcases hq₀ with ⟨q₀', hq₀', rfl⟩ | ⟨_, _, rfl⟩
          · exact ⟨q₀', hq₀', (List.cons_prefix_cons.mp hpq₀).2⟩
          · exact False.elim (Bool.noConfusion (List.cons_prefix_cons.mp hpq₀).1)
        rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
        · obtain ⟨h1, h2⟩ := ihl hvl hp'_l hq'
          exact ⟨fun hp ↦ h1 (List.cons_prefix_cons.mp hp).2,
            fun hn ↦ h2 fun h ↦ hn (List.cons_prefix_cons.mpr ⟨rfl, h⟩)⟩
        · exact ⟨fun hp ↦ False.elim (Bool.noConfusion (List.cons_prefix_cons.mp hp).1),
            fun _ ↦ hdisj.symm.mono (RectTree.lookupLeaf_subset_root hvr hq')
              (RectTree.subtree_subset_root hvl p')⟩
      · have hp'_r : ∃ q₀' ∈ r.leafPaths, p' <+: q₀' := by
          rcases hq₀ with ⟨_, _, rfl⟩ | ⟨q₀', hq₀', rfl⟩
          · exact False.elim (Bool.noConfusion (List.cons_prefix_cons.mp hpq₀).1)
          · exact ⟨q₀', hq₀', (List.cons_prefix_cons.mp hpq₀).2⟩
        rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
        · exact ⟨fun hp ↦ False.elim (Bool.noConfusion (List.cons_prefix_cons.mp hp).1),
            fun _ ↦ hdisj.mono (RectTree.lookupLeaf_subset_root hvl hq')
              (RectTree.subtree_subset_root hvr p')⟩
        · obtain ⟨h1, h2⟩ := ihr hvr hp'_r hq'
          exact ⟨fun hp ↦ h1 (List.cons_prefix_cons.mp hp).2,
            fun hn ↦ h2 fun h ↦ hn (List.cons_prefix_cons.mpr ⟨rfl, h⟩)⟩

private def RectTree.centroidAux {m n : ℕ} :
    RectTree m n → List Bool → Finset (List Bool) → ℕ → List Bool
  | .leaf _ _ _, acc, _, _ => acc
  | .node _ _ l r, acc, K, bound =>
      let pl := acc ++ [false]; let pr := acc ++ [true]
      let cl := (K.filter (fun q ↦ pl <+: q)).card; let cr := (K.filter (fun q ↦ pr <+: q)).card
      if cr ≤ cl then if cl ≤ bound then pl else l.centroidAux pl K bound
      else if cr ≤ bound then pr else r.centroidAux pr K bound

private lemma RectTree.centroidAux_spec {m n : ℕ} (w : RectTree m n) (acc : List Bool)
    (K : Finset (List Bool)) (bound : ℕ)
    (hK : ∀ q ∈ K, acc <+: q → ∃ q' ∈ w.leafPaths, q = acc ++ q')
    (hb1 : 1 ≤ bound) (hKgt : bound < (K.filter (fun q ↦ acc <+: q)).card) :
    let p := w.centroidAux acc K bound
    (∃ q ∈ K, p <+: q) ∧ (K.filter (fun q ↦ p <+: q)).card ≤ bound ∧
    bound + 1 ≤ 2 * (K.filter (fun q ↦ p <+: q)).card := by
  induction w generalizing acc with
  | leaf =>
    have hsub : K.filter (fun q ↦ acc <+: q) ⊆ {acc} := fun q hq ↦ by
      obtain ⟨hqK, hpref⟩ := Finset.mem_filter.mp hq
      obtain ⟨q', hq', rfl⟩ := hK q hqK hpref
      simp only [RectTree.leafPaths, Finset.mem_singleton] at hq'; simp [hq']
    have hle := (Finset.card_le_card hsub).trans (Finset.card_singleton acc).le; omega
  | node _ _ l r ihl ihr =>
    let pl := acc ++ [false]; let pr := acc ++ [true]
    let Kl := K.filter (fun q ↦ pl <+: q); let Kr := K.filter (fun q ↦ pr <+: q)
    have hdisj : Disjoint Kl Kr := by
      rw [Finset.disjoint_left]; intro q hl hr
      obtain ⟨_, ht₁⟩ := (Finset.mem_filter.mp hl).2; obtain ⟨_, ht₂⟩ := (Finset.mem_filter.mp hr).2
      have heq := ht₁.trans ht₂.symm; simp [pl, pr, List.append_assoc] at heq
    have hunion : Kl ∪ Kr = K.filter (fun q ↦ acc <+: q) := by
      ext q; simp only [Finset.mem_union, Finset.mem_filter, Kl, pr, pl, Kr]
      refine ⟨fun h ↦ h.elim (fun ⟨h1, h2⟩ ↦ ⟨h1, (List.prefix_append _ _).trans h2⟩)
        (fun ⟨h1, h2⟩ ↦ ⟨h1, (List.prefix_append _ _).trans h2⟩), fun ⟨hqK, hpref⟩ ↦ ?_⟩
      obtain ⟨q', hq', rfl⟩ := hK q hqK hpref
      simp only [RectTree.leafPaths, Finset.mem_union, Finset.mem_image] at hq'
      rcases hq' with ⟨q'', _, rfl⟩ | ⟨q'', _, rfl⟩
      · exact Or.inl ⟨hqK, ⟨q'', by simp [List.append_assoc]⟩⟩
      · exact Or.inr ⟨hqK, ⟨q'', by simp [List.append_assoc]⟩⟩
    have hsum : Kl.card + Kr.card = (K.filter (fun q ↦ acc <+: q)).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hKl : ∀ q ∈ K, pl <+: q → ∃ q'' ∈ l.leafPaths, q = pl ++ q'' := by
      intro q hqK ⟨t, ht⟩
      obtain ⟨q', hq', hqeq⟩ := hK q hqK ⟨[false] ++ t, by simpa [pl, List.append_assoc] using ht⟩
      have hqt : q' = false :: t := by simpa [pl, List.append_assoc] using hqeq.symm.trans ht.symm
      subst hqt; simp only [RectTree.leafPaths, Finset.mem_union, Finset.mem_image] at hq'
      rcases hq' with ⟨q'', hq'', h⟩ | ⟨_, _, h⟩
      · exact ⟨t, by simpa [List.cons.inj h] using hq'',
          by simpa [pl, List.append_assoc] using ht.symm⟩
      · exact False.elim (Bool.noConfusion (List.cons.inj h).1)
    have hKr : ∀ q ∈ K, pr <+: q → ∃ q'' ∈ r.leafPaths, q = pr ++ q'' := by
      intro q hqK ⟨t, ht⟩
      obtain ⟨q', hq', hqeq⟩ := hK q hqK ⟨[true] ++ t, by simpa [pr, List.append_assoc] using ht⟩
      have hqt : q' = true :: t := by simpa [pr, List.append_assoc] using hqeq.symm.trans ht.symm
      subst hqt; simp only [RectTree.leafPaths, Finset.mem_union, Finset.mem_image] at hq'
      rcases hq' with ⟨_, _, h⟩ | ⟨q'', hq'', h⟩
      · exact False.elim (Bool.noConfusion (List.cons.inj h).1)
      · exact ⟨t, by simpa [List.cons.inj h] using hq'',
          by simpa [pr, List.append_assoc] using ht.symm⟩
    dsimp only [RectTree.centroidAux]
    by_cases hcmp : Kr.card ≤ Kl.card
    · rw [ite_eq_left hcmp]; by_cases hle : Kl.card ≤ bound
      · rw [ite_eq_left hle]
        obtain ⟨q, hq⟩ := Finset.card_pos.mp (by dsimp only [Kl, Kr] at *; omega : 0 < Kl.card)
        exact ⟨⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩, hle,
          by dsimp only [Kl, Kr, pl, pr] at *; omega⟩
      · rw [ite_eq_right hle]; exact ihl pl hKl (Nat.lt_of_not_ge hle)
    · rw [ite_eq_right hcmp]; by_cases hle : Kr.card ≤ bound
      · rw [ite_eq_left hle]
        obtain ⟨q, hq⟩ := Finset.card_pos.mp (by dsimp only [Kl, Kr] at *; omega : 0 < Kr.card)
        exact ⟨⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩, hle,
          by dsimp only [Kl, Kr, pl, pr] at *; omega⟩
      · rw [ite_eq_right hle]; exact ihr pr hKr (Nat.lt_of_not_ge hle)

private lemma RectTree.centroidPath_spec {m n : ℕ} (t : RectTree m n) (K : Finset (List Bool))
    (hK : K ⊆ t.leafPaths) (hK2 : 2 ≤ K.card) :
    let p := t.centroidAux [] K (2 * K.card / 3)
    (∃ q ∈ K, p <+: q) ∧ (K.filter (fun q ↦ p <+: q)).card ≤ 2 * K.card / 3 ∧
    (K.filter (fun q ↦ ¬ p <+: q)).card ≤ 2 * K.card / 3 := by
  have hspec := t.centroidAux_spec [] K (2 * K.card / 3)
    (fun q hq _ ↦ ⟨q, hK hq, rfl⟩) (by omega) (by simpa using (by omega : 2 * K.card / 3 < K.card))
  dsimp only at hspec
  have hcompl := Finset.card_filter_add_card_filter_not (s := K)
    (p := fun q ↦ t.centroidAux [] K (2 * K.card / 3) <+: q)
  exact ⟨hspec.1, hspec.2.1, by omega⟩

private def spiraStep (k : ℕ) : ℕ := if k ≤ 1 then k else 2 * k / 3

private lemma spiraStep_mono {a b : ℕ} (h : a ≤ b) : spiraStep a ≤ spiraStep b := by
  dsimp [spiraStep]; split_ifs <;> omega

private lemma spiraStep_iter_le_one (k : ℕ) : (spiraStep^[2 * Nat.log 2 k + 2]) k ≤ 1 := by
  have hbound : ∀ j : ℕ, (spiraStep^[2 * j]) k ≤ max 1 (k / 2 ^ j) := by
    intro j; induction j with
    | zero => simp
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply,
        Function.iterate_succ_apply, Function.iterate_one]
      rcases le_or_gt (spiraStep^[2 * j] k) 1 with hle1 | hge2
      · have h1 := spiraStep_mono (spiraStep_mono hle1)
        have hs1 : spiraStep (spiraStep 1) = 1 := by simp [spiraStep]
        omega
      · have h2 : spiraStep (spiraStep (spiraStep^[2 * j] k)) ≤ (spiraStep^[2 * j] k) / 2 := by
          dsimp [spiraStep]; split_ifs <;> omega
        have hdiv : (spiraStep^[2 * j] k) / 2 ≤ max 1 (k / 2 ^ j) / 2 := Nat.div_le_div_right ih
        rw [show k / 2 ^ (j + 1) = (k / 2 ^ j) / 2 by rw [pow_succ, Nat.div_div_eq_div_mul]]
        omega
  have hfin := hbound (Nat.log 2 k + 1)
  have hdiv0 : k / 2 ^ (Nat.log 2 k + 1) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k)
  rw [hdiv0] at hfin; rw [show 2 * Nat.log 2 k + 2 = 2 * (Nat.log 2 k + 1) by ring]
  simpa using hfin

private noncomputable def compileProtocolAux {m n : ℕ} (t : RectTree m n) :
    ℕ → Finset (List Bool) → Protocol (Fin m) (Fin n) ℝ
  | 0, K =>
      if hK : K.Nonempty then Protocol.output (t.lookupLeaf hK.choose).2.2
      else Protocol.output 0
  | s + 1, K =>
      if _hK : K.card ≤ 1 then
        if hne : K.Nonempty then Protocol.output (t.lookupLeaf hne.choose).2.2
        else Protocol.output 0
      else
        let p := t.centroidAux [] K (2 * K.card / 3)
        let K_in := K.filter (fun q ↦ p <+: q)
        let K_out := K.filter (fun q ↦ ¬ p <+: q)
        let protIn := compileProtocolAux t s K_in
        let protOut := compileProtocolAux t s K_out
        Protocol.alice (fun x ↦ decide (x ∈ (t.subtree p).rows))
          protOut
          (Protocol.bob (fun y ↦ decide (y ∈ (t.subtree p).cols)) protOut protIn)

private lemma compileProtocolAux_depth_le {m n : ℕ} (t : RectTree m n) :
    ∀ (s : ℕ) (K : Finset (List Bool)), (compileProtocolAux t s K).depth ≤ 2 * s := by
  intro s
  induction s with
  | zero =>
    intro K
    dsimp [compileProtocolAux]
    split_ifs <;> simp
  | succ s ih =>
    intro K
    dsimp only [compileProtocolAux]
    split_ifs
    · simp
    · simp
    · simp only [Protocol.depth_alice, Protocol.depth_bob]
      have h1 := ih (K.filter (fun q ↦ t.centroidAux [] K (2 * K.card / 3) <+: q))
      have h2 := ih (K.filter (fun q ↦ ¬ t.centroidAux [] K (2 * K.card / 3) <+: q))
      omega

private lemma compileProtocolAux_run {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t)
    {x : Fin m} {y : Fin n} {q₀ : List Bool} (hq₀ : q₀ ∈ t.leafPaths)
    (hxq₀ : x ∈ (t.lookupLeaf q₀).1) (hyq₀ : y ∈ (t.lookupLeaf q₀).2.1) :
    ∀ (s : ℕ) (K : Finset (List Bool)) (k : ℕ),
      K ⊆ t.leafPaths → q₀ ∈ K → K.card ≤ k → (spiraStep^[s] k) ≤ 1 →
      (compileProtocolAux t s K).run x y = (t.lookupLeaf q₀).2.2 := by
  intro s
  induction s with
  | zero =>
    intro K k _ hq₀K hKk hk1
    simp only [Function.iterate_zero, id_eq] at hk1
    have hcard : K.card ≤ 1 := hKk.trans hk1
    have hne : K.Nonempty := ⟨q₀, hq₀K⟩
    have hch : hne.choose = q₀ :=
      Finset.card_le_one.mp hcard hne.choose (Exists.choose_spec hne) q₀ hq₀K
    simp only [compileProtocolAux, hne, ↓reduceDIte, Protocol.run_output, hch]
  | succ s ih =>
    intro K k hsub hq₀K hKk hk1
    dsimp only [compileProtocolAux]
    by_cases hle1 : K.card ≤ 1
    · have hne : K.Nonempty := ⟨q₀, hq₀K⟩
      have hch : hne.choose = q₀ :=
        Finset.card_le_one.mp hle1 hne.choose (Exists.choose_spec hne) q₀ hq₀K
      simp only [hle1, ↓reduceDIte, hne, Protocol.run_output, hch]
    · have hge2 : 2 ≤ K.card := by omega
      simp only [hle1, ↓reduceDIte]
      set p := t.centroidAux [] K (2 * K.card / 3)
      obtain ⟨⟨q_wit, hq_wit, hp_wit⟩, hc_le, hcompl_le⟩ :=
        RectTree.centroidPath_spec t K hsub hge2
      obtain ⟨hsub_rect, hdisj_rect⟩ :=
        RectTree.rect_prefix_and_disjoint ht ⟨q_wit, hsub hq_wit, hp_wit⟩ hq₀
      have hstep : spiraStep K.card = 2 * K.card / 3 := by simp [spiraStep, hle1]
      have hstep_le : 2 * K.card / 3 ≤ spiraStep k := hstep ▸ spiraStep_mono hKk
      have hiter : (spiraStep^[s] (spiraStep k)) ≤ 1 := by
        simpa [Function.iterate_succ_apply] using hk1
      have hxy_q₀ : (x, y) ∈ (t.lookupLeaf q₀).1 ×ˢ (t.lookupLeaf q₀).2.1 :=
        Finset.mem_product.mpr ⟨hxq₀, hyq₀⟩
      simp only [Protocol.run_alice, Protocol.run_bob]
      by_cases hx : x ∈ (t.subtree p).rows
      · simp only [hx, decide_true, Bool.cond_true]
        by_cases hy : y ∈ (t.subtree p).cols
        · simp only [hy, decide_true, Bool.cond_true]
          have hpref_q₀ : p <+: q₀ := by
            by_contra hnot
            rw [Finset.disjoint_left] at hdisj_rect
            exact hdisj_rect hnot hxy_q₀ (Finset.mem_product.mpr ⟨hx, hy⟩)
          exact ih (K.filter (fun q ↦ p <+: q)) (spiraStep k)
            ((Finset.filter_subset _ K).trans hsub)
            (Finset.mem_filter.mpr ⟨hq₀K, hpref_q₀⟩)
            (hc_le.trans hstep_le) hiter
        · simp only [hy, decide_false, Bool.cond_false]
          have hnot_q₀ : ¬ p <+: q₀ := fun hpref ↦
            hy (Finset.mem_product.mp (hsub_rect hpref hxy_q₀)).2
          exact ih (K.filter (fun q ↦ ¬ p <+: q)) (spiraStep k)
            ((Finset.filter_subset _ K).trans hsub)
            (Finset.mem_filter.mpr ⟨hq₀K, hnot_q₀⟩)
            (hcompl_le.trans hstep_le) hiter
      · simp only [hx, decide_false, Bool.cond_false]
        have hnot_q₀ : ¬ p <+: q₀ := fun hpref ↦
          hx (Finset.mem_product.mp (hsub_rect hpref hxy_q₀)).1
        exact ih (K.filter (fun q ↦ ¬ p <+: q)) (spiraStep k)
          ((Finset.filter_subset _ K).trans hsub)
          (Finset.mem_filter.mpr ⟨hq₀K, hnot_q₀⟩)
          (hcompl_le.trans hstep_le) hiter

/-- **Spira rebalancing**: any valid rectangle-partition tree `t` for `M` covering
`Finset.univ ×ˢ Finset.univ` compiles to a deterministic `Cslib.Communication.Protocol` of depth at
most `2 * (2 * Nat.log 2 t.leafCount + 2)` computing `M`. -/
theorem exists_protocol_of_rectTree {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    {t : RectTree m n} (ht : RectTree.Valid M t)
    (htR : t.rows = Finset.univ) (htC : t.cols = Finset.univ) :
    ∃ P : Protocol (Fin m) (Fin n) ℝ,
      P.run = (fun x y ↦ M x y) ∧ P.depth ≤ 2 * (2 * Nat.log 2 t.leafCount + 2) := by
  classical
  let R := 2 * Nat.log 2 t.leafCount + 2
  refine ⟨compileProtocolAux t R t.leafPaths, funext fun x ↦ funext fun y ↦ ?_,
    compileProtocolAux_depth_le t R t.leafPaths⟩
  obtain ⟨q₀, hq₀, hxq₀, hyq₀⟩ := RectTree.exists_mem_lookupLeaf_of_valid (x := x) (y := y) ht
    (by simp [htR]) (by simp [htC])
  rw [compileProtocolAux_run ht hq₀ hxq₀ hyq₀ R t.leafPaths t.leafCount
    (Finset.Subset.refl _) hq₀ (t.card_leafPaths.le) (spiraStep_iter_le_one t.leafCount)]
  exact (RectTree.valid_lookupLeaf ht hq₀ x hxq₀ y hyq₀).symm

/-! ### 6. Communication Complexity Upper Bound from Monochromatic Submatrices -/

/-- **Nisan–Wigderson reduction**: any universal `2 ^ (-c₁ * √r)` monochromatic submatrix bound on
low-rank binary matrices implies an `O(√r)` upper bound on deterministic communication complexity
`Cslib.Communication.Protocol.ecomplexityFun` for all Boolean functions on finite domains. -/
theorem ecomplexityFun_le_sqrt_rank_of_monochromatic {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hmono_bound : ∀ {a b s : ℕ} (N : Matrix (Fin a) (Fin b) ℝ),
      (∀ i j, N i j = 0 ∨ N i j = 1) → N.rank ≤ s →
      ∃ (X : Finset (Fin a)) (Y : Finset (Fin b)),
        (a : ℝ) / (2 : ℝ) ^ (c₁ * Real.sqrt s) ≤ (X.card : ℝ) ∧
        (b : ℝ) / (2 : ℝ) ^ (c₁ * Real.sqrt s) ≤ (Y.card : ℝ) ∧
        ((∀ i ∈ X, ∀ j ∈ Y, N i j = 0) ∨ (∀ i ∈ X, ∀ j ∈ Y, N i j = 1))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → Bool),
        ∃ k : ℕ, (k : ℝ) ≤ c * Real.sqrt (communicationMatrix ℝ f).rank + c ∧
          Protocol.ecomplexityFun f ≤ k := by
  obtain ⟨C, hC, htree⟩ := exists_rectTree_of_rank_le_of_monochromatic_sqrt hc₁ hmono_bound
  refine ⟨4 * C + 4, by positivity, fun {X Y} _ _ f ↦ ?_⟩
  classical
  let eX := Fintype.equivFin X; let eY := Fintype.equivFin Y
  let r := (communicationMatrix ℝ f).rank
  let M : Matrix (Fin (Fintype.card X)) (Fin (Fintype.card Y)) ℝ :=
    (communicationMatrix ℝ f).submatrix eX.symm eY.symm
  have hM_bin : ∀ i j, M i j = 0 ∨ M i j = 1 := fun i j ↦ by
    simp only [M, Matrix.submatrix_apply, communicationMatrix_apply]
    cases f (eX.symm i) (eY.symm j) <;> simp
  have hM_rank : M.rank ≤ r := by simp [M, r]
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hX0 | hXpos
  · refine ⟨0, by simp only [Nat.cast_zero]; positivity,
      Protocol.ecomplexityFun_le_depth (p := Protocol.output false) ?_⟩
    funext x; exact (Fintype.card_eq_zero_iff.mp hX0).elim x
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hY0 | hYpos
  · refine ⟨0, by simp only [Nat.cast_zero]; positivity,
      Protocol.ecomplexityFun_le_depth (p := Protocol.output false) ?_⟩
    funext _ y; exact (Fintype.card_eq_zero_iff.mp hY0).elim y
  obtain ⟨S₀, T₀, rowRep, colRep, hS₀, hT₀, hrep⟩ := exists_dedup_submatrix M hM_bin hM_rank
  let M₀ := submatrixOfFinset M S₀ T₀
  have hM₀_bin : ∀ i j, M₀ i j = 0 ∨ M₀ i j = 1 := fun i j ↦ hM_bin _ _
  have hM₀_rank : M₀.rank ≤ r := (Matrix.rank_submatrix_le M _ _).trans hM_rank
  obtain ⟨t, htR, htC, htV, htL⟩ := htree M₀ hM₀_bin hS₀ hT₀ hM₀_rank
  obtain ⟨P₀, hP₀_run, hP₀_depth⟩ := exists_protocol_of_rectTree htV htR htC
  let P : Protocol X Y Bool := ((P₀.comap rowRep colRep).comap eX eY).map (fun z ↦ decide (z = 1))
  have hP_run : P.run = f := by
    funext x y
    simp only [P, Protocol.run_map, Protocol.run_comap, hP₀_run]
    have := hrep (eX x) (eY y)
    simp only [M₀, submatrixOfFinset, Matrix.submatrix_apply] at this ⊢
    rw [← this]
    simp only [M, Matrix.submatrix_apply, communicationMatrix_apply, Equiv.symm_apply_apply]
    cases f x y <;> norm_num
  have hP_depth : (P.depth : ℝ) ≤ (4 * C + 4) * Real.sqrt r + (4 * C + 4) := by
    simp only [P, Protocol.depth_map, Protocol.depth_comap]
    have hcast : (P₀.depth : ℝ) ≤ ((2 * (2 * Nat.log 2 t.leafCount + 2) : ℕ) : ℝ) := by
      exact_mod_cast hP₀_depth
    push_cast at hcast
    have hsqrt_nn : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
    linarith
  exact ⟨P.depth, hP_depth, Protocol.ecomplexityFun_le_depth hP_run⟩

end Cslib.Communication.NisanWigderson
