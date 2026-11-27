/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rank Factorization, Canonical-Gauge Fixing, and Determinant-Forcing Gadgets

Matrix-rank primitives over `ℝ`: rank-factorization equivalence, vanishing minors,
canonical-gauge fixing (existence and global uniqueness), rank obstruction and
determinant-forcing gadgets, and affine/rank-3 arithmetic gate gadgets.
-/

public section

namespace Cslib.Complexity

open Matrix

/-! ### Rank Factorization, Monotonicity, and Vanishing Minors -/

private lemma frobeniusInner_entryMatrix_map {m n : ℕ} (r : Fin m) (c : Fin n)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((entryMatrix m n r c).map ((↑) : ℚ → ℝ)) X = X r c := by
  have hmap : (entryMatrix m n r c).map ((↑) : ℚ → ℝ) = entryMatrixReal m n r c :=
    entryMatrix_map_cast m n r c
  rw [hmap, frobeniusInner_entryMatrixReal]

private lemma exists_linearIndependent_submatrix_rows {p q d : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (hd : d ≤ M.rank) :
    ∃ r : Fin d ↪ Fin p, LinearIndependent ℝ (M.submatrix r id).row := by
  classical
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℝ (Set.range M.row)
  have hs_fin : s.Finite := (Set.finite_range M.row).subset hs_sub
  let _ : Fintype s := hs_fin.fintype
  have hcard : Fintype.card s = M.rank := by
    rw [M.rank_eq_finrank_span_row, ← hs_span]
    have hli := linearIndependent_iff_card_eq_finrank_span.mp hs_li
    have hrange : Set.range (Subtype.val : s → Fin q → ℝ) = s := Subtype.range_coe
    rw [Set.finrank, hrange] at hli
    exact hli
  have hd_card : d ≤ Fintype.card s := hd.trans_eq hcard.symm
  let e : Fin d ↪ s :=
    (Fin.castLEOrderEmb hd_card).toEmbedding.trans (Fintype.equivFin s).symm.toEmbedding
  have hmem : ∀ t : Fin d, ∃ i : Fin p, M.row i = (e t : Fin q → ℝ) := fun t ↦
    hs_sub (e t).2
  choose r hr using hmem
  have hli_r : LinearIndependent ℝ (M.row ∘ r) := by
    have hcomp : M.row ∘ r = Subtype.val ∘ e := funext hr
    rw [hcomp]
    exact hs_li.comp e e.injective
  have hr_inj : Function.Injective r := by
    intro a b hab
    exact hli_r.injective (by simp [Function.comp, hab])
  exact ⟨⟨r, hr_inj⟩, hli_r⟩

/-- a real `m × n` matrix `X` has
`rank(X) ≤ k` if and only if it admits a bilinear factorization `X = U * V` with
`U ∈ ℝ^{m × k}` and `V ∈ ℝ^{k × n}`. -/
theorem rank_factorization_equiv {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    X.rank ≤ k ↔ ∃ (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ), X = U * V := by
  constructor
  · intro hX
    have hcol : ∀ j, X.col j ∈ LinearMap.range X.mulVecLin := fun j ↦ by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    let b : Module.Basis (Fin X.rank) ℝ (LinearMap.range X.mulVecLin) :=
      Module.finBasisOfFinrankEq ℝ _ rfl
    let U₀ : Matrix (Fin m) (Fin X.rank) ℝ := Matrix.of fun i s ↦ (b s : Fin m → ℝ) i
    let V₀ : Matrix (Fin X.rank) (Fin n) ℝ := Matrix.of fun s j ↦ b.repr ⟨X.col j, hcol j⟩ s
    have hX0 : X = U₀ * V₀ := by
      ext i j
      have hrepr := b.sum_repr ⟨X.col j, hcol j⟩
      have hval := congrArg (fun v : LinearMap.range X.mulVecLin ↦ (v : Fin m → ℝ) i) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hval
      change X.col j i = (U₀ * V₀) i j
      rw [← hval]
      simp [U₀, V₀, Matrix.mul_apply, mul_comm]
    let U : Matrix (Fin m) (Fin k) ℝ := Matrix.of fun i t ↦
      if ht : t.1 < X.rank then U₀ i ⟨t.1, ht⟩ else 0
    let V : Matrix (Fin k) (Fin n) ℝ := Matrix.of fun t j ↦
      if ht : t.1 < X.rank then V₀ ⟨t.1, ht⟩ j else 0
    refine ⟨U, V, ?_⟩
    rw [hX0]
    ext i j
    simp only [Matrix.mul_apply]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hX)))]
    · rw [Finset.sum_image (fun a _ b _ h ↦ Fin.castLE_injective hX h)]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      simp [U, V, Fin.castLE]
    · intro t _ ht
      have hge : ¬ t.1 < X.rank := fun hlt ↦
        ht (Finset.mem_image.mpr ⟨⟨t.1, hlt⟩, Finset.mem_univ _, rfl⟩)
      simp [U, V, hge]
  · rintro ⟨U, V, rfl⟩
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)

/-- every submatrix `Y = X.submatrix r c` satisfies
`rank(Y) ≤ rank(X)`. -/
theorem rank_monotone {m n p q : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin p → Fin m) (c : Fin q → Fin n) :
    (X.submatrix r c).rank ≤ X.rank :=
  Matrix.rank_submatrix_le X r c

/-- if `rank(X) ≤ 3`, then every `4 × 4` minor of
`X` vanishes. -/
theorem rank3_minors {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} (hX : X.rank ≤ 3)
    (r : Fin 4 → Fin m) (c : Fin 4 → Fin n) :
    (X.submatrix r c).det = 0 := by
  by_contra hdet
  have h4 : (X.submatrix r c).rank = 4 := Matrix.rank_of_det_ne_zero hdet
  have hle : (X.submatrix r c).rank ≤ 3 := (rank_monotone X r c).trans hX
  omega

/-- `rank(X) ≤ k` if and only if every
`(k + 1) × (k + 1)` minor of `X` has determinant zero. -/
theorem rank_via_minors {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    X.rank ≤ k ↔
      ∀ (r : Fin (k + 1) ↪ Fin m) (c : Fin (k + 1) ↪ Fin n), (X.submatrix r c).det = 0 := by
  constructor
  · intro hX r c
    by_contra hdet
    have hrank : (X.submatrix r c).rank = k + 1 := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    have hle : (X.submatrix r c).rank ≤ k := (rank_monotone X r c).trans hX
    omega
  · intro hdet
    by_contra hgt
    have hk : k + 1 ≤ X.rank := by omega
    obtain ⟨r, hr_li⟩ := exists_linearIndependent_submatrix_rows X hk
    have hBrank : (X.submatrix r id).rank = k + 1 := by
      simpa using hr_li.rank_matrix
    have hBtrank : k + 1 ≤ (X.submatrix r id)ᵀ.rank := by
      rw [Matrix.rank_transpose, hBrank]
    obtain ⟨c, hc_li⟩ := exists_linearIndependent_submatrix_rows (X.submatrix r id)ᵀ hBtrank
    have hCrank : (X.submatrix r c).rank = k + 1 := by
      have hCeq : ((X.submatrix r id)ᵀ.submatrix c id) = (X.submatrix r c)ᵀ := by
        ext i j; rfl
      have hCtr : (X.submatrix r c)ᵀ.rank = k + 1 := by
        rw [← hCeq]; simpa using hc_li.rank_matrix
      rwa [Matrix.rank_transpose] at hCtr
    have hsurj : (X.submatrix r c).mulVec.Surjective :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hCrank)
    choose V hV using fun j : Fin (k + 1) ↦ hsurj (Pi.single j 1)
    have hmul : (X.submatrix r c) * Matrix.of (fun i j ↦ V j i) = 1 := by
      ext i j
      have := congrFun (hV j) i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
        Pi.single_apply, eq_comm] using this
    have hdet1 := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hdet r c, zero_mul, Matrix.det_one] at hdet1
    exact zero_ne_one hdet1

/-! ### Gauge Fixing and Canonical Factors (, ) -/

/-- if `rank(X) ≤ 3`
and `X[I₀, J₀] = B` for an invertible `3 × 3` matrix `B`, then there exist factors `U, V` with
`X = U * V`, `U[I₀, :] = I₃`, and `V[:, J₀] = B`. -/
theorem gauge_fixing_exists {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B.det ≠ 0) (hrank : X.rank ≤ 3) (hpin : X.submatrix I₀ J₀ = B) :
    ∃ (U : Matrix (Fin m) (Fin 3) ℝ) (V : Matrix (Fin 3) (Fin n) ℝ),
      X = U * V ∧ U.submatrix I₀ id = 1 ∧ V.submatrix id J₀ = B := by
  obtain ⟨U₀, V₀, rfl⟩ := (rank_factorization_equiv X 3).mp hrank
  have hsub : (U₀ * V₀).submatrix I₀ J₀ = U₀.submatrix I₀ id * V₀.submatrix id J₀ := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [hsub] at hpin
  have hdet_mul : (U₀.submatrix I₀ id).det * (V₀.submatrix id J₀).det = B.det := by
    rw [← Matrix.det_mul, hpin]
  have hUdet : (U₀.submatrix I₀ id).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet_mul
    exact hB hdet_mul.symm
  have hUunit : IsUnit (U₀.submatrix I₀ id).det := isUnit_iff_ne_zero.mpr hUdet
  let G : Matrix (Fin 3) (Fin 3) ℝ := (U₀.submatrix I₀ id)⁻¹
  refine ⟨U₀ * G, (U₀.submatrix I₀ id) * V₀, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, Matrix.nonsing_inv_mul _ hUunit, Matrix.one_mul]
  · ext a b
    have hmul : (U₀ * G).submatrix I₀ id = U₀.submatrix I₀ id * G := by
      ext i j; simp [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [hmul, Matrix.mul_nonsing_inv _ hUunit]
  · ext a b
    have hmul : ((U₀.submatrix I₀ id) * V₀).submatrix id J₀ =
        U₀.submatrix I₀ id * V₀.submatrix id J₀ := by
      ext i j; simp [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [hmul, hpin]

/-- any two rank-3
factorizations of `X` satisfying `U[I₀, :] = I₃` and `V[:, J₀] = B` (with `det(B) ≠ 0`) are
globally identical (`U₁ = U₂` and `V₁ = V₂`). -/
theorem gauge_fixing_unique {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B.det ≠ 0) {U₁ U₂ : Matrix (Fin m) (Fin 3) ℝ} {V₁ V₂ : Matrix (Fin 3) (Fin n) ℝ}
    (hX₁ : X = U₁ * V₁) (hX₂ : X = U₂ * V₂)
    (hU₁ : U₁.submatrix I₀ id = 1) (hU₂ : U₂.submatrix I₀ id = 1)
    (hV₁ : V₁.submatrix id J₀ = B) (hV₂ : V₂.submatrix id J₀ = B) :
    U₁ = U₂ ∧ V₁ = V₂ := by
  have hV : V₁ = V₂ := by
    have h1 : X.submatrix I₀ id = U₁.submatrix I₀ id * V₁ := by
      rw [hX₁]; ext a b; simp [Matrix.submatrix_apply, Matrix.mul_apply]
    have h2 : X.submatrix I₀ id = U₂.submatrix I₀ id * V₂ := by
      rw [hX₂]; ext a b; simp [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [hU₁, Matrix.one_mul] at h1
    rw [hU₂, Matrix.one_mul] at h2
    exact h1.symm.trans h2
  have hU : U₁ = U₂ := by
    have h1 : X.submatrix id J₀ = U₁ * V₁.submatrix id J₀ := by
      rw [hX₁]; ext a b; simp [Matrix.submatrix_apply, Matrix.mul_apply]
    have h2 : X.submatrix id J₀ = U₂ * V₂.submatrix id J₀ := by
      rw [hX₂]; ext a b; simp [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [hV₁] at h1
    rw [hV₂] at h2
    have hBunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
    have hEq : U₁ * B = U₂ * B := h1.symm.trans h2
    calc
      U₁ = U₁ * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hBunit, Matrix.mul_one]
      _ = (U₁ * B) * B⁻¹ := (Matrix.mul_assoc U₁ B B⁻¹).symm
      _ = (U₂ * B) * B⁻¹ := by rw [hEq]
      _ = U₂ * (B * B⁻¹) := Matrix.mul_assoc U₂ B B⁻¹
      _ = U₂ := by rw [Matrix.mul_nonsing_inv _ hBunit, Matrix.mul_one]
  exact ⟨hU, hV⟩

/-- and combined: under
`rank(X) ≤ 3` and `X[I₀, J₀] = B` with `det(B) ≠ 0`, there exists a unique canonical-gauge
factorization `(U, V)` of `X`. -/
theorem gauge_fixing_canonical {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B.det ≠ 0) (hrank : X.rank ≤ 3) (hpin : X.submatrix I₀ J₀ = B) :
    ∃! p : Matrix (Fin m) (Fin 3) ℝ × Matrix (Fin 3) (Fin n) ℝ,
      X = p.1 * p.2 ∧ p.1.submatrix I₀ id = 1 ∧ p.2.submatrix id J₀ = B := by
  obtain ⟨U, V, hUV, hU, hV⟩ := gauge_fixing_exists hB hrank hpin
  refine ⟨(U, V), ⟨hUV, hU, hV⟩, ?_⟩
  rintro ⟨U', V'⟩ ⟨hUV', hU', hV'⟩
  obtain ⟨rfl, rfl⟩ := gauge_fixing_unique hB hUV' hUV hU' hU hV' hV
  rfl

/-- for any feasible matrix `X` and any
rank-3 factorization `X = U * V` in canonical gauge, the decoded designated entries coincide
with `X r_i c_i` and are invariant across factorizations. -/
theorem well_defined_decoding {m n N : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (carriers : Fin N → Fin m × Fin n)
    {U₁ U₂ : Matrix (Fin m) (Fin 3) ℝ} {V₁ V₂ : Matrix (Fin 3) (Fin n) ℝ}
    (hX₁ : X = U₁ * V₁) (hX₂ : X = U₂ * V₂) :
    (fun i ↦ (U₁ * V₁) (carriers i).1 (carriers i).2) =
      (fun i ↦ (U₂ * V₂) (carriers i).1 (carriers i).2) ∧
    (fun i ↦ (U₁ * V₁) (carriers i).1 (carriers i).2) =
      (fun i ↦ designatedEntry X (carriers i).1 (carriers i).2) := by
  rw [← hX₁, ← hX₂]
  exact ⟨rfl, rfl⟩

/-- if `X` satisfies a collection of affine
constraints on designated entries (constants, copies, additions, negations), then the decoded
values `x_i = X r_i c_i` satisfy those exact algebraic relations. -/
theorem semantic_correctness {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    (∀ r c (val : ℚ),
      frobeniusInner (entryMatrixReal m n r c) X = (val : ℝ) →
        designatedEntry X r c = (val : ℝ)) ∧
    (∀ r₁ c₁ r₂ c₂,
      frobeniusInner ((entryDiffMatrix m n r₁ c₁ r₂ c₂).map ((↑) : ℚ → ℝ)) X = 0 →
        designatedEntry X r₁ c₁ = designatedEntry X r₂ c₂) ∧
    (∀ rₓ cₓ rᵧ cᵧ r_z c_z,
      frobeniusInner ((entryMatrix m n r_z c_z - entryMatrix m n rₓ cₓ -
        entryMatrix m n rᵧ cᵧ).map ((↑) : ℚ → ℝ)) X = 0 →
        designatedEntry X r_z c_z = designatedEntry X rₓ cₓ + designatedEntry X rᵧ cᵧ) ∧
    (∀ rₓ cₓ r_z c_z,
      frobeniusInner ((entryMatrix m n r_z c_z + entryMatrix m n rₓ cₓ).map ((↑) : ℚ → ℝ)) X = 0 →
        designatedEntry X r_z c_z = -designatedEntry X rₓ cₓ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c val h
    simpa using h
  · intro r₁ c₁ r₂ c₂ h
    rw [frobeniusInner_entryDiffMatrix, sub_eq_zero] at h
    exact h
  · intro rₓ cₓ rᵧ cᵧ r_z c_z h
    have hmap : (entryMatrix m n r_z c_z - entryMatrix m n rₓ cₓ -
        entryMatrix m n rᵧ cᵧ).map ((↑) : ℚ → ℝ) =
        entryMatrixReal m n r_z c_z - entryMatrixReal m n rₓ cₓ -
          entryMatrixReal m n rᵧ cᵧ := by
      ext i j
      simp only [Matrix.map_apply, Matrix.sub_apply, Rat.cast_sub, entryMatrix_apply,
        entryMatrixReal_apply]
      split_ifs <;> norm_num
    rw [hmap, frobeniusInner_sub_left, frobeniusInner_sub_left,
      frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal,
      frobeniusInner_entryMatrixReal] at h
    simp only [designatedEntry_apply]
    linarith
  · intro rₓ cₓ r_z c_z h
    have hmap : (entryMatrix m n r_z c_z + entryMatrix m n rₓ cₓ).map ((↑) : ℚ → ℝ) =
        entryMatrixReal m n r_z c_z + entryMatrixReal m n rₓ cₓ := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Rat.cast_add, entryMatrix_apply,
        entryMatrixReal_apply]
      split_ifs <;> norm_num
    rw [hmap, frobeniusInner_add_left, frobeniusInner_entryMatrixReal,
      frobeniusInner_entryMatrixReal] at h
    simp only [designatedEntry_apply]
    linarith

/-! ### Formalization Note 1: Counterexamples to Literal -/

/-- Counterexample showing that the literal statement of 
(`main.tex:1058-1091`) fails when the off-diagonal blocks between the gauge block and the `2 × 2`
gadget block are left unconstrained: the `5 × 5` matrix `X` below satisfies `X[0..2, 0..2] = I₃`
and `X[3..4, 3..4] = [[1, 0], [0, 1]]` (`c = 1 ≠ 0 = a * b`), yet `rank(X) ≤ 3` (in fact `= 3`). -/
theorem rank_obstruction_counterexample_without_offdiag :
    let I₀ : Fin 3 ↪ Fin 5 := ⟨fun i ↦ ⟨i.1, by omega⟩, fun a b h ↦ by
      exact Fin.ext (by simpa using congrArg Fin.val h)⟩
    let X : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j ↦
      if i.1 = j.1 ∧ i.1 < 3 then 1
      else if i.1 = 3 ∧ j.1 = 0 then 1
      else if i.1 = 4 ∧ j.1 = 1 then 1
      else if i.1 = 0 ∧ j.1 = 3 then 1
      else if i.1 = 1 ∧ j.1 = 4 then 1
      else if i.1 = 3 ∧ j.1 = 3 then 1
      else if i.1 = 4 ∧ j.1 = 4 then 1
      else 0
    X.submatrix I₀ I₀ = (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    X ⟨3, by omega⟩ ⟨3, by omega⟩ = 1 ∧
    X ⟨3, by omega⟩ ⟨4, by omega⟩ = 0 ∧
    X ⟨4, by omega⟩ ⟨3, by omega⟩ = 0 ∧
    X ⟨4, by omega⟩ ⟨4, by omega⟩ = 1 ∧
    X ⟨4, by omega⟩ ⟨4, by omega⟩ ≠ X ⟨3, by omega⟩ ⟨4, by omega⟩ * X ⟨4, by omega⟩ ⟨3, by omega⟩ ∧
    X.rank ≤ 3 := by
  intro I₀ X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hI₀ : ∀ k : Fin 3, I₀ k = ⟨k.1, by omega⟩ := fun _ ↦ rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, hI₀]
  · simp [X]
  · simp [X]
  · simp [X]
  · simp [X]
  · simp [X]
  · rw [rank_factorization_equiv]
    let U : Matrix (Fin 5) (Fin 3) ℝ := Matrix.of fun i k ↦
      if i.1 = k.1 then 1
      else if i.1 = 3 ∧ k.1 = 0 then 1
      else if i.1 = 4 ∧ k.1 = 1 then 1
      else 0
    let V : Matrix (Fin 3) (Fin 5) ℝ := Uᵀ
    refine ⟨U, V, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, U, V, Matrix.mul_apply, Fin.sum_univ_three]

/-- Counterexample showing that for an invertible `3 × 3` matrix `B`, not every `2 × 2` submatrix
`B[{i₁, i₂}, {j₁, j₂}]` has nonzero determinant (`main.tex:1070-1082`). -/
theorem rank_obstruction_counterexample_submatrix_choice :
    let B : Matrix (Fin 3) (Fin 3) ℝ := 1
    let r : Fin 2 → Fin 3 := ![0, 1]
    let c : Fin 2 → Fin 3 := ![1, 2]
    B.det ≠ 0 ∧ (B.submatrix r c).det = 0 := by
  intro B r c
  refine ⟨by simp [B], ?_⟩
  rw [Matrix.det_fin_two]
  simp [B, r, c, Matrix.one_apply]

/-! ### Repaired and Determinant-Forcing Gadget () -/

/-- Existence of an invertible `2 × 2` submatrix inside any invertible `3 × 3` matrix `B`
(proved by Laplace expansion along row `0`). -/
theorem exists_invertible_two_by_two_of_det_three_ne_zero
    {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.det ≠ 0) :
    ∃ (i₁ i₂ j₁ j₂ : Fin 3), i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
      (B.submatrix ![i₁, i₂] ![j₁, j₂]).det ≠ 0 := by
  by_contra hall
  push Not at hall
  have h01_01 := hall 1 2 1 2 (by decide) (by decide)
  have h01_02 := hall 1 2 0 2 (by decide) (by decide)
  have h01_12 := hall 1 2 0 1 (by decide) (by decide)
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h01_01 h01_02 h01_12
  apply hB
  have hlap : B.det =
      B 0 0 * (B 1 1 * B 2 2 - B 1 2 * B 2 1) -
      B 0 1 * (B 1 0 * B 2 2 - B 1 2 * B 2 0) +
      B 0 2 * (B 1 0 * B 2 1 - B 1 1 * B 2 0) := by
    rw [Matrix.det_fin_three]; ring
  rw [hlap, h01_01, h01_02, h01_12]
  ring

/-- (repaired with explicit off-diagonal zero constraints and a
nonvanishing `2 × 2` minor of `B`): if `X[I₀, J₀] = B`, `det(B[{i₁, i₂}, {j₁, j₂}]) ≠ 0`, the
eight off-diagonal entries `X[I₀{i₁, i₂}, {c₁, c₂}]` and `X[{r₁, r₂}, J₀{j₁, j₂}]` vanish, and
`X[{r₁, r₂}, {c₁, c₂}] = [[1, a], [b, c]]` with `c ≠ a * b`, then `rank(X) ≥ 4`. -/
theorem rank_obstruction {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    {i₁ i₂ j₁ j₂ : Fin 3} {r₁ r₂ : Fin m} {c₁ c₂ : Fin n}
    (hpin : X.submatrix I₀ J₀ = B)
    (hB2 : (B.submatrix ![i₁, i₂] ![j₁, j₂]).det ≠ 0)
    (hzero_top : ∀ (a : Fin 2) (b : Fin 2), X (I₀ (![i₁, i₂] a)) (![c₁, c₂] b) = 0)
    (hzero_bot : ∀ (a : Fin 2) (b : Fin 2), X (![r₁, r₂] a) (J₀ (![j₁, j₂] b)) = 0)
    (h11 : X r₁ c₁ = 1) (hneq : X r₂ c₂ ≠ X r₁ c₂ * X r₂ c₁) :
    4 ≤ X.rank := by
  let rows : Fin 4 → Fin m := fun t ↦
    match t with
    | ⟨0, _⟩ => I₀ i₁
    | ⟨1, _⟩ => I₀ i₂
    | ⟨2, _⟩ => r₁
    | ⟨3, _⟩ => r₂
  let cols : Fin 4 → Fin n := fun t ↦
    match t with
    | ⟨0, _⟩ => J₀ j₁
    | ⟨1, _⟩ => J₀ j₂
    | ⟨2, _⟩ => c₁
    | ⟨3, _⟩ => c₂
  let Y : Matrix (Fin 4) (Fin 4) ℝ := X.submatrix rows cols
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  have hblock : Y.submatrix e e =
      Matrix.fromBlocks (B.submatrix ![i₁, i₂] ![j₁, j₂]) 0 0
        (X.submatrix ![r₁, r₂] ![c₁, c₂]) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> rw [← hpin] <;> rfl
    · fin_cases a <;> fin_cases b
      · exact hzero_top 0 0
      · exact hzero_top 0 1
      · exact hzero_top 1 0
      · exact hzero_top 1 1
    · fin_cases a <;> fin_cases b
      · exact hzero_bot 0 0
      · exact hzero_bot 0 1
      · exact hzero_bot 1 0
      · exact hzero_bot 1 1
    · fin_cases a <;> fin_cases b <;> rfl
  have hdetY : Y.det = (B.submatrix ![i₁, i₂] ![j₁, j₂]).det *
      (X r₂ c₂ - X r₁ c₂ * X r₂ c₁) := by
    have h1 : (Y.submatrix e e).det = Y.det := Matrix.det_submatrix_equiv_self e Y
    rw [← h1, hblock, Matrix.det_fromBlocks_zero₂₁]
    have h2 : (X.submatrix ![r₁, r₂] ![c₁, c₂]).det = X r₂ c₂ - X r₁ c₂ * X r₂ c₁ := by
      simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, h11]
      ring
    rw [h2]
  have hYne : Y.det ≠ 0 := by
    rw [hdetY]
    exact mul_ne_zero hB2 (sub_ne_zero.mpr hneq)
  have hYrank : Y.rank = 4 := Matrix.rank_of_det_ne_zero hYne
  calc
    4 = Y.rank := hYrank.symm
    _ ≤ X.rank := rank_monotone X rows cols

/-- ** (Soundness)** and under the pinned
gauge block, the nine constant-size affine constraints of the determinant-forcing gadget (fixing
`X r₁ c₁ = 1` plus the eight off-diagonal zeros), and `rank(X) ≤ 3`, we must have
`X r₂ c₂ = X r₁ c₂ * X r₂ c₁`. -/
theorem det_forcing_soundness {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    {i₁ i₂ j₁ j₂ : Fin 3} {r₁ r₂ : Fin m} {c₁ c₂ : Fin n}
    (hrank : X.rank ≤ 3) (hpin : X.submatrix I₀ J₀ = B)
    (hB2 : (B.submatrix ![i₁, i₂] ![j₁, j₂]).det ≠ 0)
    (hzero_top : ∀ (a : Fin 2) (b : Fin 2), X (I₀ (![i₁, i₂] a)) (![c₁, c₂] b) = 0)
    (hzero_bot : ∀ (a : Fin 2) (b : Fin 2), X (![r₁, r₂] a) (J₀ (![j₁, j₂] b)) = 0)
    (h11 : X r₁ c₁ = 1) :
    X r₂ c₂ = X r₁ c₂ * X r₂ c₁ := by
  by_contra hneq
  have h4 := rank_obstruction hpin hB2 hzero_top hzero_bot h11 hneq
  omega

/-- ** (Constructive Completeness in Canonical Gauge)**: for any invertible
`3 × 3` gauge block `B`, any disjoint fresh gadget indices `{r₁, r₂}` and `{c₁, c₂}`, and any
reals `a, b, c` with `c = a * b`, there exist canonical-gauge local factors `(U, V)` such that
`X = U * V` satisfies `X[I₀, J₀] = B`, all eight off-diagonal zero constraints, and
`X[{r₁, r₂}, {c₁, c₂}] = [[1, a], [b, c]]`. -/
theorem det_forcing_completeness_canonical_gauge {m n : ℕ}
    (I₀ : Fin 3 ↪ Fin m) (J₀ : Fin 3 ↪ Fin n) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (i₁ i₂ j₁ j₂ : Fin 3) (hi : i₁ ≠ i₂)
    (hB2 : (B.submatrix ![i₁, i₂] ![j₁, j₂]).det ≠ 0)
    (r₁ r₂ : Fin m) (c₁ c₂ : Fin n) (hr : r₁ ≠ r₂) (hc : c₁ ≠ c₂)
    (hrI : r₁ ∉ Set.range I₀ ∧ r₂ ∉ Set.range I₀)
    (hcJ : c₁ ∉ Set.range J₀ ∧ c₂ ∉ Set.range J₀)
    (a b c : ℝ) (hmul : c = a * b) :
    ∃ (U : Matrix (Fin m) (Fin 3) ℝ) (V : Matrix (Fin 3) (Fin n) ℝ),
      U.submatrix I₀ id = 1 ∧
      V.submatrix id J₀ = B ∧
      (∀ (p q : Fin 2), (U * V) (I₀ (![i₁, i₂] p)) (![c₁, c₂] q) = 0) ∧
      (∀ (p q : Fin 2), (U * V) (![r₁, r₂] p) (J₀ (![j₁, j₂] q)) = 0) ∧
      (U * V) r₁ c₁ = 1 ∧ (U * V) r₁ c₂ = a ∧ (U * V) r₂ c₁ = b ∧ (U * V) r₂ c₂ = c := by
  classical
 -- Find the third gauge indices `i₃ ∈ Fin 3 \ {i₁, i₂}` and `j₃ ∈ Fin 3 \ {j₁, j₂}`.
  obtain ⟨i₃, hi₃₁, hi₃₂⟩ : ∃ i₃ : Fin 3, i₃ ≠ i₁ ∧ i₃ ≠ i₂ := by
    fin_cases i₁ <;> fin_cases i₂ <;> first | exact absurd rfl hi | decide
 -- Solve `w · B[:, {j₁, j₂}] = 0` with `w i₃ = 1` using invertibility of `B[{i₁, i₂}, {j₁, j₂}]`.
  let B₂ : Matrix (Fin 2) (Fin 2) ℝ := B.submatrix ![i₁, i₂] ![j₁, j₂]
  have hB₂unit : IsUnit B₂.det := isUnit_iff_ne_zero.mpr hB2
  have hB₂T : IsUnit B₂ᵀ.det := by rwa [Matrix.det_transpose]
  let rhs : Fin 2 → ℝ := fun q ↦ -B i₃ (![j₁, j₂] q)
  let sol : Fin 2 → ℝ := B₂ᵀ⁻¹ *ᵥ rhs
  have hsol : B₂ᵀ *ᵥ sol = rhs := by
    simp only [sol, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB₂T, Matrix.one_mulVec]
  let w : Fin 3 → ℝ := fun k ↦
    if k = i₁ then sol 0 else if k = i₂ then sol 1 else 1
  have hw_i₃ : w i₃ = 1 := by
    simp [w, hi₃₁, hi₃₂]
  have hw_orth : ∀ q : Fin 2, (∑ k : Fin 3, w k * B k (![j₁, j₂] q)) = 0 := by
    intro q
    have hsum : (∑ k : Fin 3, w k * B k (![j₁, j₂] q)) =
        w i₁ * B i₁ (![j₁, j₂] q) + w i₂ * B i₂ (![j₁, j₂] q) + w i₃ * B i₃ (![j₁, j₂] q) := by
      have hperm : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by
        ext t
        fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> fin_cases t <;>
          simp_all
      rw [hperm, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      · ring
      · simp [hi₃₂.symm]
      · simp [hi, hi₃₁.symm]
    rw [hsum, hw_i₃]
    have hwi₁ : w i₁ = sol 0 := by simp [w]
    have hwi₂ : w i₂ = sol 1 := by simp [w, hi.symm]
    rw [hwi₁, hwi₂]
    have hq := congrFun hsol q
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two, B₂,
      Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, rhs] at hq
    linarith
  let e₃ : Fin 3 → ℝ := fun k ↦ if k = i₃ then 1 else 0
  let U : Matrix (Fin m) (Fin 3) ℝ := Matrix.of fun i k ↦
    if h : ∃ t : Fin 3, I₀ t = i then (if h.choose = k then 1 else 0)
    else if i = r₁ then w k
    else if i = r₂ then b * w k
    else 0
  let V : Matrix (Fin 3) (Fin n) ℝ := Matrix.of fun k j ↦
    if h : ∃ t : Fin 3, J₀ t = j then B k h.choose
    else if j = c₁ then e₃ k
    else if j = c₂ then a * e₃ k
    else 0
  have hU_gauge : U.submatrix I₀ id = 1 := by
    ext t k
    have hex : ∃ s : Fin 3, I₀ s = I₀ t := ⟨t, rfl⟩
    have hch : hex.choose = t := I₀.injective hex.choose_spec
    simp only [Matrix.submatrix_apply, id_eq, U, Matrix.of_apply, hex, ↓reduceDIte, hch,
      Matrix.one_apply]
  have hV_gauge : V.submatrix id J₀ = B := by
    ext k t
    have hex : ∃ s : Fin 3, J₀ s = J₀ t := ⟨t, rfl⟩
    have hch : hex.choose = t := J₀.injective hex.choose_spec
    simp only [Matrix.submatrix_apply, id_eq, V, Matrix.of_apply, hex, ↓reduceDIte, hch]
  have hU_r₁ : ∀ k, U r₁ k = w k := by
    intro k
    have hnot : ¬∃ t : Fin 3, I₀ t = r₁ := hrI.1
    simp [U, hnot]
  have hU_r₂ : ∀ k, U r₂ k = b * w k := by
    intro k
    have hnot : ¬∃ t : Fin 3, I₀ t = r₂ := hrI.2
    simp [U, hnot, hr.symm]
  have hV_c₁ : ∀ k, V k c₁ = e₃ k := by
    intro k
    have hnot : ¬∃ t : Fin 3, J₀ t = c₁ := hcJ.1
    simp [V, hnot]
  have hV_c₂ : ∀ k, V k c₂ = a * e₃ k := by
    intro k
    have hnot : ¬∃ t : Fin 3, J₀ t = c₂ := hcJ.2
    simp [V, hnot, hc.symm]
  have hU_I₀ : ∀ t k, U (I₀ t) k = if t = k then 1 else 0 := fun t k ↦ by
    have := congrFun (congrFun hU_gauge t) k
    simpa [Matrix.one_apply] using this
  have hV_J₀ : ∀ k t, V k (J₀ t) = B k t := fun k t ↦
    congrFun (congrFun hV_gauge k) t
  have hwe₃ : (∑ k : Fin 3, w k * e₃ k) = 1 := by
    rw [Finset.sum_eq_single i₃]
    · simp [e₃, hw_i₃]
    · intro k _ hk; simp [e₃, hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨U, V, hU_gauge, hV_gauge, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    simp only [Matrix.mul_apply, hU_I₀]
    rw [Finset.sum_eq_single (![i₁, i₂] p)]
    · fin_cases p <;> fin_cases q <;> simp [hV_c₁, hV_c₂, e₃, hi₃₁.symm, hi₃₂.symm]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p q
    simp only [Matrix.mul_apply, hV_J₀]
    fin_cases p
    · simpa [hU_r₁] using hw_orth q
    · simpa [hU_r₂, mul_assoc, ← Finset.mul_sum] using Or.inr (hw_orth q)
  · simp only [Matrix.mul_apply, hU_r₁, hV_c₁, hwe₃]
  · simp only [Matrix.mul_apply, hU_r₁, hV_c₂]
    calc
      (∑ k : Fin 3, w k * (a * e₃ k)) = a * (∑ k : Fin 3, w k * e₃ k) := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
      _ = a := by rw [hwe₃, mul_one]
  · simp only [Matrix.mul_apply, hU_r₂, hV_c₁]
    calc
      (∑ k : Fin 3, b * w k * e₃ k) = b * (∑ k : Fin 3, w k * e₃ k) := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
      _ = b := by rw [hwe₃, mul_one]
  · simp only [Matrix.mul_apply, hU_r₂, hV_c₂]
    calc
      (∑ k : Fin 3, b * w k * (a * e₃ k)) = a * b * (∑ k : Fin 3, w k * e₃ k) := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
      _ = c := by rw [hwe₃, mul_one, hmul]

/-- for the standard
canonical gauge `B = I₃` on `I₀ = J₀ = {0, 1, 2}`: there exists a constant-size system of 9
affine constraints with `{0, 1}` coefficients on `X ∈ ℝ^{m × n}` (`5 ≤ m, n`) enforcing `c = a * b`
under `rank(X) ≤ 3`. -/
theorem det_forcing {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) :
    let I₀ : Fin 3 ↪ Fin m := ⟨fun i ↦ ⟨i.1, by omega⟩, fun a b h ↦
      Fin.ext (by simpa using congrArg Fin.val h)⟩
    let J₀ : Fin 3 ↪ Fin n := ⟨fun j ↦ ⟨j.1, by omega⟩, fun a b h ↦
      Fin.ext (by simpa using congrArg Fin.val h)⟩
    let r₁ : Fin m := ⟨3, by omega⟩
    let r₂ : Fin m := ⟨4, by omega⟩
    let c₁ : Fin n := ⟨3, by omega⟩
    let c₂ : Fin n := ⟨4, by omega⟩
    ∃ (cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ)),
      cs.length = 9 ∧
      (∀ p ∈ cs, ∀ i j, p.1 i j ∈ ({0, 1} : Set ℚ)) ∧
      (∀ X : Matrix (Fin m) (Fin n) ℝ,
        X.submatrix I₀ J₀ = 1 →
        (ARMInstance.ofMatrices cs).Satisfies X →
        X.rank ≤ 3 →
        X r₂ c₂ = X r₁ c₂ * X r₂ c₁) ∧
      (∀ (a b c : ℝ), c = a * b →
        ∃ X : Matrix (Fin m) (Fin n) ℝ,
          X.submatrix I₀ J₀ = 1 ∧
          (ARMInstance.ofMatrices cs).Satisfies X ∧
          X.rank ≤ 3 ∧
          X r₁ c₂ = a ∧ X r₂ c₁ = b ∧ X r₂ c₂ = c) := by
  intro I₀ J₀ r₁ r₂ c₁ c₂
  let cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ) :=
    [ (entryMatrix m n r₁ c₁, 1),
      (entryMatrix m n (I₀ 0) c₁, 0), (entryMatrix m n (I₀ 0) c₂, 0),
      (entryMatrix m n (I₀ 1) c₁, 0), (entryMatrix m n (I₀ 1) c₂, 0),
      (entryMatrix m n r₁ (J₀ 0), 0), (entryMatrix m n r₁ (J₀ 1), 0),
      (entryMatrix m n r₂ (J₀ 0), 0), (entryMatrix m n r₂ (J₀ 1), 0) ]
  have hB2 : ((1 : Matrix (Fin 3) (Fin 3) ℝ).submatrix ![0, 1] ![0, 1]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [Matrix.one_apply]
  refine ⟨cs, rfl, ?_, ?_, ?_⟩
  · intro p hp i j
    simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [entryMatrix_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
        split_ifs <;> simp
  · intro X hpin hsat hrank
    rw [ARMInstance.satisfies_ofMatrices_iff] at hsat
    have h11 : X r₁ c₁ = 1 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix m n r₁ c₁, 1) (by simp [cs])
    have hztop : ∀ p q : Fin 2, X (I₀ (![0, 1] p)) (![c₁, c₂] q) = 0 := by
      intro p q
      fin_cases p <;> fin_cases q
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n (I₀ 0) c₁, 0) (by simp [cs])
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n (I₀ 0) c₂, 0) (by simp [cs])
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n (I₀ 1) c₁, 0) (by simp [cs])
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n (I₀ 1) c₂, 0) (by simp [cs])
    have hzbot : ∀ p q : Fin 2, X (![r₁, r₂] p) (J₀ (![0, 1] q)) = 0 := by
      intro p q
      fin_cases p <;> fin_cases q
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n r₁ (J₀ 0), 0) (by simp [cs])
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n r₁ (J₀ 1), 0) (by simp [cs])
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n r₂ (J₀ 0), 0) (by simp [cs])
      · simpa [frobeniusInner_entryMatrix_map] using
          hsat (entryMatrix m n r₂ (J₀ 1), 0) (by simp [cs])
    exact det_forcing_soundness hrank hpin hB2 hztop hzbot h11
  · intro a b c hmul
    have hI₀v : ∀ t : Fin 3, (I₀ t).1 = t.1 := fun _ ↦ rfl
    have hJ₀v : ∀ t : Fin 3, (J₀ t).1 = t.1 := fun _ ↦ rfl
    have hrI : r₁ ∉ Set.range I₀ ∧ r₂ ∉ Set.range I₀ := by
      refine ⟨?_, ?_⟩ <;> rintro ⟨t, ht⟩
      · have hval := congrArg Fin.val ht; rw [hI₀v] at hval; change t.1 = 3 at hval; omega
      · have hval := congrArg Fin.val ht; rw [hI₀v] at hval; change t.1 = 4 at hval; omega
    have hcJ : c₁ ∉ Set.range J₀ ∧ c₂ ∉ Set.range J₀ := by
      refine ⟨?_, ?_⟩ <;> rintro ⟨t, ht⟩
      · have hval := congrArg Fin.val ht; rw [hJ₀v] at hval; change t.1 = 3 at hval; omega
      · have hval := congrArg Fin.val ht; rw [hJ₀v] at hval; change t.1 = 4 at hval; omega
    obtain ⟨U, V, hU, hV, hztop, hzbot, h11, h12, h21, h22⟩ :=
      det_forcing_completeness_canonical_gauge I₀ J₀ 1 0 1 0 1 (by decide) hB2
        r₁ r₂ c₁ c₂ (by simp [r₁, r₂, Fin.ext_iff]) (by simp [c₁, c₂, Fin.ext_iff]) hrI hcJ a b c
        hmul
    refine ⟨U * V, ?_, ?_, ?_, h12, h21, h22⟩
    · ext i j
      have hsub : (U * V).submatrix I₀ J₀ = U.submatrix I₀ id * V.submatrix id J₀ := by
        ext x y; simp [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [hsub, hU, hV, Matrix.one_mul]
    · rw [ARMInstance.satisfies_ofMatrices_iff]
      intro p hp
      simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [frobeniusInner_entryMatrix_map] using h11
      · simpa [frobeniusInner_entryMatrix_map] using hztop 0 0
      · simpa [frobeniusInner_entryMatrix_map] using hztop 0 1
      · simpa [frobeniusInner_entryMatrix_map] using hztop 1 0
      · simpa [frobeniusInner_entryMatrix_map] using hztop 1 1
      · simpa [frobeniusInner_entryMatrix_map] using hzbot 0 0
      · simpa [frobeniusInner_entryMatrix_map] using hzbot 0 1
      · simpa [frobeniusInner_entryMatrix_map] using hzbot 1 0
      · simpa [frobeniusInner_entryMatrix_map] using hzbot 1 1
    · exact (rank_factorization_equiv (U * V) 3).mpr ⟨U, V, rfl⟩

/-- under the gauge-fixing and determinant-forcing
constraints, there is no feasible matrix `X` with `rank(X) ≤ 3` and `c ≠ a * b`. -/
theorem no_spurious {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    {i₁ i₂ j₁ j₂ : Fin 3} {r₁ r₂ : Fin m} {c₁ c₂ : Fin n}
    (hpin : X.submatrix I₀ J₀ = B)
    (hB2 : (B.submatrix ![i₁, i₂] ![j₁, j₂]).det ≠ 0)
    (hzero_top : ∀ (a : Fin 2) (b : Fin 2), X (I₀ (![i₁, i₂] a)) (![c₁, c₂] b) = 0)
    (hzero_bot : ∀ (a : Fin 2) (b : Fin 2), X (![r₁, r₂] a) (J₀ (![j₁, j₂] b)) = 0)
    (h11 : X r₁ c₁ = 1) :
    ¬ (X.rank ≤ 3 ∧ X r₂ c₂ ≠ X r₁ c₂ * X r₂ c₁) := by
  rintro ⟨hrank, hneq⟩
  exact hneq (det_forcing_soundness hrank hpin hB2 hzero_top hzero_bot h11)

/-- each determinant-forcing gadget uses
constant auxiliary rows and columns (2 each), 9 affine constraints with coefficients in `{0, 1}`
(1 fixing `X r₁ c₁ = 1` plus 8 off-diagonal zeros), and 3 designated-entry carriers. -/
theorem primitive_complexity {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) :
    ∃ (auxRows auxCols numConstraints : ℕ),
      auxRows = 2 ∧ auxCols = 2 ∧ numConstraints = 9 ∧
      ∃ (cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ)),
        cs.length = numConstraints ∧
        ∀ p ∈ cs, ∀ i j, p.1 i j ∈ ({0, 1} : Set ℚ) := by
  obtain ⟨cs, hlen, hcoeff, _, _⟩ := det_forcing hm hn
  exact ⟨2, 2, 9, rfl, rfl, rfl, cs, hlen, hcoeff⟩

/-! ### Arithmetic Gate Gadgets -/

/-- constant and copy affine constraints enforce
`x = c` and `x = y` independently of any rank bound. -/
theorem const_copy_correct {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (rₓ rᵧ : Fin m) (cₓ cᵧ : Fin n) (c : ℚ) :
    (frobeniusInner (entryMatrixReal m n rₓ cₓ) X = (c : ℝ) ↔ X rₓ cₓ = (c : ℝ)) ∧
    (frobeniusInner ((entryDiffMatrix m n rₓ cₓ rᵧ cᵧ).map ((↑) : ℚ → ℝ)) X = 0 ↔
      X rₓ cₓ = X rᵧ cᵧ) := by
  rw [frobeniusInner_entryMatrixReal, frobeniusInner_entryDiffMatrix, sub_eq_zero]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- a single affine constraint enforces `z = x + y`
independently of the rank bound. -/
theorem add_gadget {m n : ℕ} (rₓ rᵧ r_z : Fin m) (cₓ cᵧ c_z : Fin n) :
    ∃ A : Matrix (Fin m) (Fin n) ℚ,
      ∀ X : Matrix (Fin m) (Fin n) ℝ,
        frobeniusInner (A.map ((↑) : ℚ → ℝ)) X = 0 ↔ X r_z c_z = X rₓ cₓ + X rᵧ cᵧ := by
  refine ⟨entryMatrix m n r_z c_z - entryMatrix m n rₓ cₓ - entryMatrix m n rᵧ cᵧ, fun X ↦ ?_⟩
  have hmap : (entryMatrix m n r_z c_z - entryMatrix m n rₓ cₓ -
      entryMatrix m n rᵧ cᵧ).map ((↑) : ℚ → ℝ) =
      entryMatrixReal m n r_z c_z - entryMatrixReal m n rₓ cₓ -
        entryMatrixReal m n rᵧ cᵧ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Rat.cast_sub, entryMatrix_apply,
      entryMatrixReal_apply]
    split_ifs <;> norm_num
  rw [hmap, frobeniusInner_sub_left, frobeniusInner_sub_left,
    frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal,
    frobeniusInner_entryMatrixReal]
  constructor <;> intro h <;> linarith

/-- a single affine constraint enforces `z = -x`
independently of the rank bound. -/
theorem neg_gadget {m n : ℕ} (rₓ r_z : Fin m) (cₓ c_z : Fin n) :
    ∃ A : Matrix (Fin m) (Fin n) ℚ,
      ∀ X : Matrix (Fin m) (Fin n) ℝ,
        frobeniusInner (A.map ((↑) : ℚ → ℝ)) X = 0 ↔ X r_z c_z = -X rₓ cₓ := by
  refine ⟨entryMatrix m n r_z c_z + entryMatrix m n rₓ cₓ, fun X ↦ ?_⟩
  have hmap : (entryMatrix m n r_z c_z + entryMatrix m n rₓ cₓ).map ((↑) : ℚ → ℝ) =
      entryMatrixReal m n r_z c_z + entryMatrixReal m n rₓ cₓ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Rat.cast_add, entryMatrix_apply,
      entryMatrixReal_apply]
    split_ifs <;> norm_num
  rw [hmap, frobeniusInner_add_left, frobeniusInner_entryMatrixReal,
    frobeniusInner_entryMatrixReal]
  constructor <;> intro h <;> linarith

/-- a constant-size affine system enforces `z = x * y` under
`rank(X) ≤ 3` (soundness and completeness). -/
theorem mul_gadget {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) :
    ∃ (cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ)),
      cs.length = 9 ∧
      let I₀ : Fin 3 ↪ Fin m := ⟨fun i ↦ ⟨i.1, by omega⟩, fun a b h ↦
        Fin.ext (by simpa using congrArg Fin.val h)⟩
      let J₀ : Fin 3 ↪ Fin n := ⟨fun j ↦ ⟨j.1, by omega⟩, fun a b h ↦
        Fin.ext (by simpa using congrArg Fin.val h)⟩
      let r₁ : Fin m := ⟨3, by omega⟩
      let r₂ : Fin m := ⟨4, by omega⟩
      let c₁ : Fin n := ⟨3, by omega⟩
      let c₂ : Fin n := ⟨4, by omega⟩
      (∀ X : Matrix (Fin m) (Fin n) ℝ,
        X.submatrix I₀ J₀ = 1 → (ARMInstance.ofMatrices cs).Satisfies X → X.rank ≤ 3 →
          X r₂ c₂ = X r₁ c₂ * X r₂ c₁) ∧
      (∀ x y z : ℝ, z = x * y →
        ∃ X : Matrix (Fin m) (Fin n) ℝ,
          X.submatrix I₀ J₀ = 1 ∧ (ARMInstance.ofMatrices cs).Satisfies X ∧ X.rank ≤ 3 ∧
            X r₁ c₂ = x ∧ X r₂ c₁ = y ∧ X r₂ c₂ = z) := by
  obtain ⟨cs, hlen, _, hsound, hcomp⟩ := det_forcing hm hn
  exact ⟨cs, hlen, hsound, hcomp⟩

/-- enforcing `x * y = 1` via the multiplication gadget and a
constant constraint forces `x ≠ 0` and `y = x⁻¹`. -/
theorem inv_gadget {x y : ℝ} (h : x * y = 1) : x ≠ 0 ∧ y = x⁻¹ := by
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  refine ⟨hx, ?_⟩
  exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm])

/-- `x ≥ 0` over `ℝ` iff `∃ s : ℝ, x = s ^ 2`. -/
theorem nonneg_iff_exists_sq (x : ℝ) : 0 ≤ x ↔ ∃ s : ℝ, x = s ^ 2 := by
  constructor
  · intro hx
    exact ⟨Real.sqrt x, (Real.sq_sqrt hx).symm⟩
  · rintro ⟨s, rfl⟩
    exact sq_nonneg s

/-- `x > 0` over `ℝ` iff `∃ s t : ℝ, x = s ^ 2 ∧ s * t = 1`. -/
theorem pos_iff_exists_sq_inv (x : ℝ) : 0 < x ↔ ∃ s t : ℝ, x = s ^ 2 ∧ s * t = 1 := by
  constructor
  · intro hx
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    exact ⟨Real.sqrt x, (Real.sqrt x)⁻¹, (Real.sq_sqrt hx.le).symm, mul_inv_cancel₀ hs⟩
  · rintro ⟨s, t, rfl, hst⟩
    have hs : s ≠ 0 := (inv_gadget hst).1
    exact sq_pos_of_ne_zero hs

/-- every primitive arithmetic relation
(constant, copy, addition, negation, multiplication, inversion, nonnegativity, strict positivity)
is enforced by `O(1)` affine constraints under `rank(X) ≤ 3` (with `5 ≤ m, n`). -/
theorem gate_complete {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) :
    (∀ (rₓ : Fin m) (cₓ : Fin n) (c : ℚ) (X : Matrix (Fin m) (Fin n) ℝ),
      frobeniusInner (entryMatrixReal m n rₓ cₓ) X = (c : ℝ) ↔ X rₓ cₓ = (c : ℝ)) ∧
    (∀ (rₓ rᵧ : Fin m) (cₓ cᵧ : Fin n) (X : Matrix (Fin m) (Fin n) ℝ),
      frobeniusInner ((entryDiffMatrix m n rₓ cₓ rᵧ cᵧ).map ((↑) : ℚ → ℝ)) X = 0 ↔
        X rₓ cₓ = X rᵧ cᵧ) ∧
    (∀ (rₓ rᵧ r_z : Fin m) (cₓ cᵧ c_z : Fin n),
      ∃ A : Matrix (Fin m) (Fin n) ℚ, ∀ X : Matrix (Fin m) (Fin n) ℝ,
        frobeniusInner (A.map ((↑) : ℚ → ℝ)) X = 0 ↔ X r_z c_z = X rₓ cₓ + X rᵧ cᵧ) ∧
    (∀ (rₓ r_z : Fin m) (cₓ c_z : Fin n),
      ∃ A : Matrix (Fin m) (Fin n) ℚ, ∀ X : Matrix (Fin m) (Fin n) ℝ,
        frobeniusInner (A.map ((↑) : ℚ → ℝ)) X = 0 ↔ X r_z c_z = -X rₓ cₓ) ∧
    (∃ cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ), cs.length = 9 ∧
      let I₀ : Fin 3 ↪ Fin m := ⟨fun i ↦ ⟨i.1, by omega⟩, fun a b h ↦
        Fin.ext (by simpa using congrArg Fin.val h)⟩
      let J₀ : Fin 3 ↪ Fin n := ⟨fun j ↦ ⟨j.1, by omega⟩, fun a b h ↦
        Fin.ext (by simpa using congrArg Fin.val h)⟩
      let r₁ : Fin m := ⟨3, by omega⟩
      let r₂ : Fin m := ⟨4, by omega⟩
      let c₁ : Fin n := ⟨3, by omega⟩
      let c₂ : Fin n := ⟨4, by omega⟩
      (∀ X : Matrix (Fin m) (Fin n) ℝ,
        X.submatrix I₀ J₀ = 1 → (ARMInstance.ofMatrices cs).Satisfies X → X.rank ≤ 3 →
          X r₂ c₂ = X r₁ c₂ * X r₂ c₁) ∧
      (∀ x y z : ℝ, z = x * y →
        ∃ X : Matrix (Fin m) (Fin n) ℝ,
          X.submatrix I₀ J₀ = 1 ∧ (ARMInstance.ofMatrices cs).Satisfies X ∧ X.rank ≤ 3 ∧
            X r₁ c₂ = x ∧ X r₂ c₁ = y ∧ X r₂ c₂ = z)) ∧
    (∀ x y : ℝ, x * y = 1 → x ≠ 0 ∧ y = x⁻¹) ∧
    (∀ x : ℝ, 0 ≤ x ↔ ∃ s : ℝ, x = s ^ 2) ∧
    (∀ x : ℝ, 0 < x ↔ ∃ s t : ℝ, x = s ^ 2 ∧ s * t = 1) :=
  ⟨fun rₓ cₓ c X ↦ (const_copy_correct X rₓ rₓ cₓ cₓ c).1,
   fun rₓ rᵧ cₓ cᵧ X ↦ (const_copy_correct X rₓ rᵧ cₓ cᵧ 0).2,
   fun rₓ rᵧ r_z cₓ cᵧ c_z ↦ add_gadget rₓ rᵧ r_z cₓ cᵧ c_z,
   fun rₓ r_z cₓ c_z ↦ neg_gadget rₓ r_z cₓ c_z,
   mul_gadget hm hn,
   fun _ _ h ↦ inv_gadget h,
   nonneg_iff_exists_sq,
   pos_iff_exists_sq_inv⟩

/-! ### Formalization Note 2: (True Parts and Counterexample) -/

/-- ** (valid minor-vanishing part)**: if `rank(X) ≤ 2`, then every
`3 × 3` and every `4 × 4` minor of `X` vanishes, and `X` cannot contain an invertible `3 × 3`
gauge block. -/
theorem rank_le_two_minors_vanish {m n : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} (hX : X.rank ≤ 2) :
    (∀ (r : Fin 3 → Fin m) (c : Fin 3 → Fin n), (X.submatrix r c).det = 0) ∧
    (∀ (r : Fin 4 → Fin m) (c : Fin 4 → Fin n), (X.submatrix r c).det = 0) ∧
    (∀ (I₀ : Fin 3 → Fin m) (J₀ : Fin 3 → Fin n) (B : Matrix (Fin 3) (Fin 3) ℝ),
      B.det ≠ 0 → X.submatrix I₀ J₀ ≠ B) := by
  refine ⟨fun r c ↦ ?_, fun r c ↦ rank3_minors (hX.trans (by omega)) r c, fun I₀ J₀ B hB hEq ↦ ?_⟩
  · by_contra hdet
    have h3 : (X.submatrix r c).rank = 3 := Matrix.rank_of_det_ne_zero hdet
    have hle : (X.submatrix r c).rank ≤ 2 := (rank_monotone X r c).trans hX
    omega
  · have h3 : (X.submatrix I₀ J₀).rank = 3 := by
      rw [hEq]
      exact Matrix.rank_of_det_ne_zero hB
    have hle : (X.submatrix I₀ J₀).rank ≤ 2 := (rank_monotone X I₀ J₀).trans hX
    omega

/-- **Formalization Note on ** (`main.tex:1467-1482`): counterexample
refuting the second sentence ("Consequently, no construction that relies on a nonzero `3 × 3` or
`4 × 4` minor as an obstruction can enforce `z = x * y` under `rank(X) ≤ 2`"). The explicit
`3 × 3` affine system pinning `X = [[1, 0, 0], [0, 1, x], [0, y, z]]` uses its `3 × 3` minor
`det(X) = z - x * y` as an obstruction to `rank(X) ≤ 2`, proving BOTH soundness (`rank(X) ≤ 2`
implies `z = x * y`) and completeness (`z = x * y` admits a feasible `X` with `rank(X) ≤ 2`). -/
theorem rank2_det_forcing_counterexample :
    let cs : List (Matrix (Fin 3) (Fin 3) ℚ × ℚ) :=
      [ (entryMatrix 3 3 0 0, 1), (entryMatrix 3 3 0 1, 0), (entryMatrix 3 3 0 2, 0),
        (entryMatrix 3 3 1 0, 0), (entryMatrix 3 3 2 0, 0), (entryMatrix 3 3 1 1, 1) ]
    (∀ X : Matrix (Fin 3) (Fin 3) ℝ,
      (ARMInstance.ofMatrices cs).Satisfies X → X.rank ≤ 2 →
        X 2 2 = X 1 2 * X 2 1) ∧
    (∀ x y z : ℝ, z = x * y →
      ∃ X : Matrix (Fin 3) (Fin 3) ℝ,
        (ARMInstance.ofMatrices cs).Satisfies X ∧ X.rank ≤ 2 ∧
          X 1 2 = x ∧ X 2 1 = y ∧ X 2 2 = z) := by
  intro cs
  constructor
  · intro X hsat hrank
    rw [ARMInstance.satisfies_ofMatrices_iff] at hsat
    have h00 : X 0 0 = 1 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix 3 3 0 0, 1) (by simp [cs])
    have h01 : X 0 1 = 0 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix 3 3 0 1, 0) (by simp [cs])
    have h02 : X 0 2 = 0 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix 3 3 0 2, 0) (by simp [cs])
    have h10 : X 1 0 = 0 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix 3 3 1 0, 0) (by simp [cs])
    have h20 : X 2 0 = 0 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix 3 3 2 0, 0) (by simp [cs])
    have h11 : X 1 1 = 1 := by
      simpa [frobeniusInner_entryMatrix_map] using hsat (entryMatrix 3 3 1 1, 1) (by simp [cs])
    have hdet0 : X.det = 0 := by
      simpa using (rank_le_two_minors_vanish hrank).1 id id
    rw [Matrix.det_fin_three] at hdet0
    rw [h00, h01, h02, h10, h20, h11] at hdet0
    linarith
  · intro x y z hmul
    let U : Matrix (Fin 3) (Fin 2) ℝ := Matrix.of fun i k ↦
      match i, k with
      | 0, 0 => 1
      | 1, 1 => 1
      | 2, 1 => y
      | _, _ => 0
    let V : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of fun k j ↦
      match k, j with
      | 0, 0 => 1
      | 1, 1 => 1
      | 1, 2 => x
      | _, _ => 0
    refine ⟨U * V, ?_, (rank_factorization_equiv (U * V) 2).mpr ⟨U, V, rfl⟩, ?_, ?_, ?_⟩
    · rw [ARMInstance.satisfies_ofMatrices_iff]
      intro p hp
      simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [frobeniusInner_entryMatrix_map, U, V, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [U, V, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [U, V, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [U, V, Matrix.mul_apply, Fin.sum_univ_two, hmul, mul_comm]

end Cslib.Complexity
