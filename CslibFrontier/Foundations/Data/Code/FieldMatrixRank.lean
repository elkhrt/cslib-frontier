module

public import CslibFrontier.Foundations.Data.Code.EmpiricalRowTypes
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-Field Matrix Rank, Column/Row Spans, and Full-Rank Counting

This module provides reusable finite-field linear-algebraic definitions and counting lemmas for
matrices over a finite field `F`: column and row spans, full column/row rank, empirical support
dimension `distDim`, fiber cardinalities of left-multiplication maps `G ↦ U * G` and pairs
`G ↦ (U₁ * G, U₂ * G)`, and cardinality bounds on full-row-rank matrices and pairs with a given
row-span intersection dimension. All results are proved under standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Foundations.Data.Code.colSpan`: column span of `A : Matrix (Fin n) (Fin b) F`.
* `CslibFrontier.Foundations.Data.Code.rowSpan`: row span of `G : Matrix (Fin k) (Fin n) F`.
* `CslibFrontier.Foundations.Data.Code.MatrixContainedIn`: all columns of `A` belong to `C`.
* `CslibFrontier.Foundations.Data.Code.HasFullColRank`, `HasFullRowRank`: linear independence of
  columns or rows.
* `CslibFrontier.Foundations.Data.Code.distDim`, `IsFullRankDist`: dimension of `span(supp(τ))`
  and full-rank empirical distributions.
* `CslibFrontier.Foundations.Data.Code.numFullRowRank`: number of full-row-rank `b × k` matrices.

## Main results

* `CslibFrontier.Foundations.Data.Code.distDim_empDist`:
  `distDim (empDist hn A) = finrank (colSpan A)` over a finite field.
* `CslibFrontier.Foundations.Data.Code.card_matrix_mul_eq_of_fullRowRank`: for full-row-rank `U`,
  `#{G | U * G = M} = q ^ ((k - b) * n)`.
* `CslibFrontier.Foundations.Data.Code.card_pair_matrix_mul_eq`: for full-row-rank `U₁, U₂` with
  `d = finrank (rowSpan U₁ ⊓ rowSpan U₂)`, every nonempty fiber of `G ↦ (U₁ * G, U₂ * G)` has
  cardinality `q ^ ((k - (2 * a - d)) * n)`.
* `CslibFrontier.Foundations.Data.Code.numFullRowRank_ge_half`: for `b + 1 ≤ k`,
  `q ^ (b * k) ≤ 2 * numFullRowRank F b k`.
* `CslibFrontier.Foundations.Data.Code.card_fullRowRank_inter_le`: upper bound on the number of
  full-row-rank `U₂` sharing a `d`-dimensional row-span intersection with `U₁`.

## Tags

finite field, matrix rank, full row rank, linear codes, subspace counting
-/

public section

namespace CslibFrontier.Foundations.Data.Code

section MatrixRankBase

variable {F : Type*} [Field F]

/-- Column span of a matrix `A : Matrix (Fin n) (Fin b) F`. -/
def colSpan {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) : Submodule F (Fin n → F) :=
  Submodule.span F (Set.range fun j : Fin b ↦ fun i : Fin n ↦ A i j)

/-- Row span of a matrix `G : Matrix (Fin k) (Fin n) F`. -/
def rowSpan {k n : ℕ} (G : Matrix (Fin k) (Fin n) F) : Submodule F (Fin n → F) :=
  Submodule.span F (Set.range fun i : Fin k ↦ G i)

theorem colSpan_eq_span_range {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) :
    colSpan A = Submodule.span F (Set.range fun j : Fin b ↦ fun i : Fin n ↦ A i j) := by rfl

theorem rowSpan_eq_span_range {k n : ℕ} (G : Matrix (Fin k) (Fin n) F) :
    rowSpan G = Submodule.span F (Set.range fun i : Fin k ↦ G i) := by rfl

@[simp]
theorem colSpan_zero {n b : ℕ} : colSpan (0 : Matrix (Fin n) (Fin b) F) = ⊥ := by
  unfold colSpan
  rw [Submodule.span_eq_bot]
  rintro _ ⟨j, rfl⟩
  rfl

@[simp]
theorem rowSpan_zero {k n : ℕ} : rowSpan (0 : Matrix (Fin k) (Fin n) F) = ⊥ := by
  unfold rowSpan
  rw [Submodule.span_eq_bot]
  rintro _ ⟨i, rfl⟩
  rfl

@[simp]
theorem colSpan_fin_zero {n : ℕ} (A : Matrix (Fin n) (Fin 0) F) : colSpan A = ⊥ := by
  unfold colSpan
  have h : Set.range (fun j : Fin 0 ↦ fun i : Fin n ↦ A i j) = ∅ := by ext v; simp
  rw [h, Submodule.span_empty]

@[simp]
theorem rowSpan_fin_zero {n : ℕ} (G : Matrix (Fin 0) (Fin n) F) : rowSpan G = ⊥ := by
  unfold rowSpan
  have h : Set.range (fun i : Fin 0 ↦ G i) = ∅ := by ext v; simp
  rw [h, Submodule.span_empty]

theorem mem_colSpan_iff_exists_mulVec {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) (v : Fin n → F) :
    v ∈ colSpan A ↔ ∃ c : Fin b → F, A.mulVec c = v := by
  simp only [colSpan, Submodule.mem_span_range_iff_exists_fun]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩ <;> ext i <;>
    simpa [Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply] using congrFun hc i

theorem mem_rowSpan_iff_exists_vecMul {k n : ℕ} (G : Matrix (Fin k) (Fin n) F) (v : Fin n → F) :
    v ∈ rowSpan G ↔ ∃ c : Fin k → F, Matrix.vecMul c G = v := by
  simp only [rowSpan, Submodule.mem_span_range_iff_exists_fun]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩ <;> ext j <;>
    simpa [Matrix.vecMul, dotProduct, Finset.sum_apply] using congrFun hc j

/-- A matrix `A` is contained in a code `C` if every column of `A` lies in `C`. -/
def MatrixContainedIn {n b : ℕ} (A : Matrix (Fin n) (Fin b) F)
    (C : Submodule F (Fin n → F)) : Prop :=
  ∀ j : Fin b, (fun i : Fin n ↦ A i j) ∈ C

@[simp]
theorem matrixContainedIn_iff_colSpan_le {n b : ℕ} (A : Matrix (Fin n) (Fin b) F)
    (C : Submodule F (Fin n → F)) :
    MatrixContainedIn A C ↔ colSpan A ≤ C := by
  simp [MatrixContainedIn, colSpan, Submodule.span_le, Set.range_subset_iff]

/-- A matrix `A : Matrix (Fin n) (Fin b) F` has full column rank if its columns are linearly
independent. -/
def HasFullColRank {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) : Prop :=
  LinearIndependent F (fun j : Fin b ↦ fun i : Fin n ↦ A i j)

/-- A matrix `U : Matrix (Fin b) (Fin k) F` has full row rank if its rows are linearly
independent. -/
def HasFullRowRank {b k : ℕ} (U : Matrix (Fin b) (Fin k) F) : Prop :=
  LinearIndependent F (fun i : Fin b ↦ U i)

theorem hasFullColRank_iff_linearIndependent {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) :
    HasFullColRank A ↔ LinearIndependent F (fun j : Fin b ↦ fun i : Fin n ↦ A i j) := Iff.rfl

theorem hasFullRowRank_iff_linearIndependent {b k : ℕ} (U : Matrix (Fin b) (Fin k) F) :
    HasFullRowRank U ↔ LinearIndependent F (fun i : Fin b ↦ U i) := Iff.rfl

theorem hasFullColRank_iff_finrank {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) :
    HasFullColRank A ↔ Module.finrank F (colSpan A) = b := by
  constructor
  · intro h
    unfold colSpan
    rw [finrank_span_eq_card h, Fintype.card_fin]
  · intro h
    unfold HasFullColRank
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    exact h.symm

theorem hasFullRowRank_iff_finrank {b k : ℕ} (U : Matrix (Fin b) (Fin k) F) :
    HasFullRowRank U ↔ Module.finrank F (rowSpan U) = b := by
  constructor
  · intro h
    unfold rowSpan
    rw [finrank_span_eq_card h, Fintype.card_fin]
  · intro h
    unfold HasFullRowRank
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    exact h.symm

theorem hasFullColRank_iff_mulVec_injective {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) :
    HasFullColRank A ↔ Function.Injective A.mulVec := by
  rw [HasFullColRank, Fintype.linearIndependent_iff]
  constructor
  · intro h v w hvw
    have hdiff : A.mulVec (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    have h0 : ∀ j, (v - w) j = 0 := h (v - w) (by
      ext i
      have hi := congrFun hdiff i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hi)
    exact sub_eq_zero.mp (funext h0)
  · intro hinj v hv
    have hmv : A.mulVec v = 0 := by
      ext i
      have hi := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hi
    have hv0 : v = 0 := hinj (hmv.trans (Matrix.mulVec_zero A).symm)
    intro j; rw [hv0]; rfl

theorem hasFullRowRank_iff_vecMul_injective {b k : ℕ} (U : Matrix (Fin b) (Fin k) F) :
    HasFullRowRank U ↔ Function.Injective (fun c ↦ Matrix.vecMul c U) := by
  rw [HasFullRowRank, Fintype.linearIndependent_iff]
  constructor
  · intro h v w hvw
    dsimp only at hvw
    have hdiff : Matrix.vecMul (v - w) U = 0 := by rw [Matrix.sub_vecMul, hvw, sub_self]
    have h0 : ∀ i, (v - w) i = 0 := h (v - w) (by
      ext j
      have hj := congrFun hdiff j
      simpa [Matrix.vecMul, dotProduct] using hj)
    exact sub_eq_zero.mp (funext h0)
  · intro hinj v hv
    have hvm : Matrix.vecMul v U = 0 := by
      ext j
      have hj := congrFun hv j
      simpa [Matrix.vecMul, dotProduct] using hj
    have hv0 : v = 0 := hinj (hvm.trans (Matrix.zero_vecMul U).symm)
    intro i; rw [hv0]; rfl

theorem hasFullColRank_mul {n b a : ℕ} {A : Matrix (Fin n) (Fin b) F}
    {D : Matrix (Fin b) (Fin a) F} (hA : HasFullColRank A) (hD : HasFullColRank D) :
    HasFullColRank (A * D) := by
  rw [hasFullColRank_iff_mulVec_injective] at hA hD ⊢
  intro u v huv
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at huv
  exact hD (hA huv)

theorem rank_eq_finrank_colSpan {n b : ℕ} (A : Matrix (Fin n) (Fin b) F) :
    A.rank = Module.finrank F (colSpan A) := by
  rw [Matrix.rank]
  have hrange : LinearMap.range A.mulVecLin = colSpan A := by
    ext v
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, colSpan,
      Submodule.mem_span_range_iff_exists_fun]
    constructor <;> rintro ⟨w, rfl⟩ <;>
      exact ⟨w, by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]⟩
  rw [hrange]

theorem rank_eq_finrank_rowSpan {k n : ℕ} (G : Matrix (Fin k) (Fin n) F) :
    G.rank = Module.finrank F (rowSpan G) := by
  rw [← Matrix.rank_transpose, rank_eq_finrank_colSpan]
  rfl

/-- Dimension of the linear span of the support of a distribution `τ` over `Fin b → F`. -/
noncomputable def distDim {b : ℕ} (τ : PMF (Fin b → F)) : ℕ :=
  Module.finrank F (Submodule.span F τ.support)

/-- A distribution `τ` over `Fin b → F` is full-rank if `dim(supp(τ)) = b`. -/
def IsFullRankDist {b : ℕ} (τ : PMF (Fin b → F)) : Prop :=
  distDim τ = b

theorem isFullRankDist_iff {b : ℕ} (τ : PMF (Fin b → F)) :
    IsFullRankDist τ ↔ distDim τ = b := by rfl

theorem distDim_empDist {n b : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin b) F) :
    distDim (empDist hn A) = Module.finrank F (colSpan A) := by
  unfold distDim
  rw [support_empDist (A := (A : Fin n → Fin b → F))]
  change Module.finrank F (rowSpan A) = Module.finrank F (colSpan A)
  rw [← rank_eq_finrank_rowSpan, rank_eq_finrank_colSpan]

theorem isFullRankDist_empDist_iff {n b : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin b) F) :
    IsFullRankDist (empDist hn A) ↔ HasFullColRank A := by
  rw [IsFullRankDist, distDim_empDist, hasFullColRank_iff_finrank]

end MatrixRankBase

section MatrixRankCounting

variable {F : Type*} [Field F] [Fintype F]

/-- Exact cardinality of any nonempty fiber of left multiplication `G ↦ V * G`. -/
theorem card_matrix_mul_eq_of_exists [DecidableEq F] {m k n : ℕ} (V : Matrix (Fin m) (Fin k) F)
    (M : Matrix (Fin m) (Fin n) F) (hex : ∃ G₀ : Matrix (Fin k) (Fin n) F, V * G₀ = M) :
    (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ V * G = M).card =
      Fintype.card F ^ ((k - V.rank) * n) := by
  classical
  let L : Matrix (Fin k) (Fin n) F →ₗ[F] Matrix (Fin m) (Fin n) F :=
    { toFun := fun G ↦ V * G
      map_add' := fun G₁ G₂ ↦ Matrix.mul_add V G₁ G₂
      map_smul' := fun c G ↦ Matrix.mul_smul V c G }
  obtain ⟨G₀, hG₀⟩ := hex
  have hfiber :
      (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ V * G = M).card =
        Fintype.card (LinearMap.ker L) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun ⟨G, hG⟩ ↦ ⟨G - G₀, by
          simp only [LinearMap.mem_ker, L, LinearMap.coe_mk, AddHom.coe_mk]
          rw [Matrix.mul_sub, hG, hG₀, sub_self]⟩
        invFun := fun ⟨H, hH⟩ ↦ ⟨H + G₀, by
          simp only [LinearMap.mem_ker, L, LinearMap.coe_mk, AddHom.coe_mk] at hH
          rw [Matrix.mul_add, hH, hG₀, zero_add]⟩
        left_inv := fun ⟨G, _⟩ ↦ by ext i j; simp
        right_inv := fun ⟨H, _⟩ ↦ by ext i j; simp }
  rw [hfiber]
  -- `ker L` is linearly isomorphic to `Fin n → ker V.mulVecLin`.
  let eKer : LinearMap.ker L ≃ₗ[F] (Fin n → LinearMap.ker V.mulVecLin) :=
    { toFun := fun ⟨G, hG⟩ j ↦ ⟨fun i ↦ G i j, by
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        ext r
        have h := congrFun (congrFun hG r) j
        simpa [L, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h⟩
      invFun := fun f ↦ ⟨fun i j ↦ (f j : Fin k → F) i, by
        change L (fun i j ↦ (f j : Fin k → F) i) = 0
        ext r j
        have h : V.mulVec (f j).1 r = 0 := congrFun (LinearMap.mem_ker.mp (f j).2) r
        let Fmat : Matrix (Fin k) (Fin n) F := fun i j ↦ (f j : Fin k → F) i
        change (V * Fmat) r j = 0
        rw [Matrix.mul_apply]
        simpa [Fmat, Matrix.mulVec, dotProduct] using h⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun ⟨G, _⟩ ↦ rfl
      right_inv := fun f ↦ rfl }
  have hker_dim : Module.finrank F (LinearMap.ker L) = (k - V.rank) * n := by
    rw [LinearEquiv.finrank_eq eKer, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    congr 1
    have hrn := LinearMap.finrank_range_add_finrank_ker V.mulVecLin
    have hdom : Module.finrank F (Fin k → F) = k := by simp
    rw [hdom] at hrn
    change V.rank + Module.finrank F (LinearMap.ker V.mulVecLin) = k at hrn
    omega
  rw [Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker L), hker_dim]

/-- For a full-row-rank `U : Matrix (Fin b) (Fin k) F` and any `M : Matrix (Fin b) (Fin n) F`,
there are `q ^ ((k - b) * n)` matrices `G` with `U * G = M`. -/
theorem card_matrix_mul_eq_of_fullRowRank [DecidableEq F] {b k n : ℕ} {U : Matrix (Fin b) (Fin k) F}
    (hU : HasFullRowRank U) (M : Matrix (Fin b) (Fin n) F) :
    (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U * G = M).card =
      Fintype.card F ^ ((k - b) * n) := by
  have hrank : U.rank = b := by
    rw [rank_eq_finrank_rowSpan, (hasFullRowRank_iff_finrank U).mp hU]
  have htop : LinearMap.range U.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    change U.rank = Module.finrank F (Fin b → F)
    rw [hrank, Module.finrank_pi, Fintype.card_fin]
  have hex : ∃ G₀ : Matrix (Fin k) (Fin n) F, U * G₀ = M := by
    have hcol : ∀ j : Fin n, ∃ g : Fin k → F, U.mulVec g = fun i ↦ M i j := fun j ↦ by
      have : (fun i ↦ M i j) ∈ LinearMap.range U.mulVecLin := htop.symm ▸ trivial
      exact this
    choose g hg using hcol
    refine ⟨fun r j ↦ g j r, ?_⟩
    ext i j
    have hij := congrFun (hg j) i
    change ∑ x, U i x * g j x = M i j
    simpa [Matrix.mulVec, dotProduct] using hij
  simpa [hrank] using card_matrix_mul_eq_of_exists U M hex

/-- For full-row-rank `U₁, U₂ : Matrix (Fin a) (Fin k) F` with intersection dimension `d`,
every nonempty fiber of `G ↦ (U₁ * G, U₂ * G)` has cardinality `q ^ ((k - (2 * a - d)) * n)`. -/
theorem card_pair_matrix_mul_eq [DecidableEq F] {a k n : ℕ} {U₁ U₂ : Matrix (Fin a) (Fin k) F}
    (hU₁ : HasFullRowRank U₁) (hU₂ : HasFullRowRank U₂)
    (M₁ M₂ : Matrix (Fin a) (Fin n) F)
    (hex : ∃ G₀ : Matrix (Fin k) (Fin n) F, U₁ * G₀ = M₁ ∧ U₂ * G₀ = M₂) :
    (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U₁ * G = M₁ ∧ U₂ * G = M₂).card =
      Fintype.card F ^
        ((k - (2 * a - Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂))) * n) := by
  classical
  let V : Matrix (Fin (a + a)) (Fin k) F := fun r ↦ Sum.elim U₁ U₂ (finSumFinEquiv.symm r)
  let M : Matrix (Fin (a + a)) (Fin n) F := fun r ↦ Sum.elim M₁ M₂ (finSumFinEquiv.symm r)
  have hiff : ∀ G : Matrix (Fin k) (Fin n) F, V * G = M ↔ U₁ * G = M₁ ∧ U₂ * G = M₂ := by
    intro G
    constructor
    · intro h
      constructor <;> ext i j
      · have h1 := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j
        rw [Matrix.mul_apply] at h1 ⊢
        dsimp only [V, M] at h1
        rw [Equiv.symm_apply_apply] at h1
        exact h1
      · have h2 := congrFun (congrFun h (finSumFinEquiv (Sum.inr i))) j
        rw [Matrix.mul_apply] at h2 ⊢
        dsimp only [V, M] at h2
        rw [Equiv.symm_apply_apply] at h2
        exact h2
    · rintro ⟨h1, h2⟩
      ext r j
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective r
      cases s with
      | inl i =>
        have hi := congrFun (congrFun h1 i) j
        rw [Matrix.mul_apply] at hi ⊢
        dsimp only [V, M]
        rw [Equiv.symm_apply_apply]
        exact hi
      | inr i =>
        have hi := congrFun (congrFun h2 i) j
        rw [Matrix.mul_apply] at hi ⊢
        dsimp only [V, M]
        rw [Equiv.symm_apply_apply]
        exact hi
  have hrowV : rowSpan V = rowSpan U₁ ⊔ rowSpan U₂ := by
    unfold rowSpan
    rw [← Submodule.span_union]
    congr 1
    ext v
    simp only [Set.mem_range, Set.mem_union]
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective r
      cases s with
      | inl i => left; exact ⟨i, by dsimp only [V]; rw [Equiv.symm_apply_apply]; rfl⟩
      | inr i => right; exact ⟨i, by dsimp only [V]; rw [Equiv.symm_apply_apply]; rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨finSumFinEquiv (Sum.inl i), by dsimp only [V]; rw [Equiv.symm_apply_apply]; rfl⟩
      · exact ⟨finSumFinEquiv (Sum.inr i), by dsimp only [V]; rw [Equiv.symm_apply_apply]; rfl⟩
  have hrankV : V.rank = 2 * a - Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) := by
    rw [rank_eq_finrank_rowSpan, hrowV]
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (rowSpan U₁) (rowSpan U₂)
    rw [(hasFullRowRank_iff_finrank U₁).mp hU₁, (hasFullRowRank_iff_finrank U₂).mp hU₂] at hsup
    omega
  have hfilt : (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ U₁ * G = M₁ ∧ U₂ * G = M₂) =
      (Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ V * G = M) := by
    ext G; simp [hiff]
  rw [hfilt, ← hrankV]
  refine card_matrix_mul_eq_of_exists V M ?_
  obtain ⟨G₀, h1, h2⟩ := hex
  exact ⟨G₀, (hiff G₀).mpr ⟨h1, h2⟩⟩

end MatrixRankCounting

section NumFullRowRank

/-- Number of full-row-rank matrices in `Matrix (Fin b) (Fin k) F`. -/
noncomputable def numFullRowRank (F : Type*) [Field F] [Fintype F] (b k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun U : Matrix (Fin b) (Fin k) F ↦ HasFullRowRank U).card

theorem numFullRowRank_eq_card (F : Type*) [Field F] [Fintype F] (b k : ℕ) :
    numFullRowRank F b k =
      (by classical
          exact (Finset.univ.filter fun U : Matrix (Fin b) (Fin k) F ↦ HasFullRowRank U).card) := by
  rfl

@[simp]
theorem numFullRowRank_zero (F : Type*) [Field F] [Fintype F] (k : ℕ) :
    numFullRowRank F 0 k = 1 := by
  classical
  unfold numFullRowRank
  simp only [HasFullRowRank, linearIndependent_empty_type, Finset.filter_true, Finset.card_univ]
  change Fintype.card (Fin 0 → Fin k → F) = 1
  rw [Fintype.card_fun, Fintype.card_fin, pow_zero]

end NumFullRowRank

section MatrixRank

variable {F : Type*} [Field F] [Fintype F]

theorem numFullRowRank_eq_prod (b k : ℕ) :
    numFullRowRank F b k = ∏ i : Fin b, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
  classical
  induction b with
  | zero =>
    simp
  | succ b ih =>
    unfold numFullRowRank at ih ⊢
    have hcard_eq :
        (Finset.univ.filter fun U : Matrix (Fin (b + 1)) (Fin k) F ↦ HasFullRowRank U).card =
          ∑ U' ∈ Finset.univ.filter (fun U' : Matrix (Fin b) (Fin k) F ↦ HasFullRowRank U'),
            (Finset.univ.filter fun u : Fin k → F ↦ u ∉ rowSpan U').card := by
      have hbij :
          (Finset.univ.filter fun U : Matrix (Fin (b + 1)) (Fin k) F ↦ HasFullRowRank U).card =
            ((Finset.univ.filter fun U' : Matrix (Fin b) (Fin k) F ↦ HasFullRowRank U').sigma
              fun U' ↦ Finset.univ.filter fun u : Fin k → F ↦ u ∉ rowSpan U').card := by
        refine Finset.card_bij
          (fun U _ ↦ ⟨(fun i ↦ U i.castSucc : Matrix (Fin b) (Fin k) F), U (Fin.last b)⟩)
          ?_ ?_ ?_
        · intro U hU
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
          rw [Finset.mem_sigma]
          have hli : LinearIndependent F (fun i : Fin b ↦ U i.castSucc) :=
            hU.comp Fin.castSucc (Fin.castSucc_injective b)
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          intro hmem
          have hspan : U (Fin.last b) ∈ Submodule.span F
              (Set.range fun i : Fin b ↦ U i.castSucc) := hmem
          rw [Submodule.mem_span_range_iff_exists_fun] at hspan
          obtain ⟨c, hc⟩ := hspan
          let c' : Fin (b + 1) → F := Fin.snoc c (-1)
          have hsum0 : ∑ i : Fin (b + 1), c' i • U i = 0 := by
            rw [Fin.sum_univ_castSucc]
            simp only [c', Fin.snoc_castSucc, Fin.snoc_last, neg_one_smul, hc]
            exact add_neg_cancel _
          have h0 := Fintype.linearIndependent_iff.mp hU c' hsum0 (Fin.last b)
          simp [c'] at h0
        · intro U₁ _ U₂ _ h
          have h1 : (fun i : Fin b ↦ U₁ i.castSucc) = (fun i : Fin b ↦ U₂ i.castSucc) :=
            congrArg Sigma.fst h
          have h2 : U₁ (Fin.last b) = U₂ (Fin.last b) := by
            have := congrArg Sigma.snd h
            simpa using this
          ext i j
          refine Fin.lastCases ?_ ?_ i
          · exact congrFun h2 j
          · intro r; exact congrFun (congrFun h1 r) j
        · rintro ⟨U', u⟩ h
          simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
          let U : Matrix (Fin (b + 1)) (Fin k) F := Fin.snoc (α := fun _ ↦ Fin k → F) U' u
          have hU_cast : ∀ i : Fin b, U i.castSucc = U' i := fun i ↦
            Fin.snoc_castSucc (α := fun _ ↦ Fin k → F) u U' i
          have hU_last : U (Fin.last b) = u :=
            Fin.snoc_last (α := fun _ ↦ Fin k → F) u U'
          refine ⟨U, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [HasFullRowRank, Fintype.linearIndependent_iff]
            intro c hc
            have hlast : c (Fin.last b) = 0 := by
              by_contra hne
              apply h.2
              rw [rowSpan, Submodule.mem_span_range_iff_exists_fun]
              refine ⟨fun i ↦ -(c (Fin.last b))⁻¹ * c i.castSucc, ?_⟩
              have hsum : ∑ i : Fin b, c i.castSucc • U' i + c (Fin.last b) • u = 0 := by
                rw [Fin.sum_univ_castSucc] at hc
                simpa only [hU_cast, hU_last] using hc
              have hu : u = -(c (Fin.last b))⁻¹ • ∑ i : Fin b, c i.castSucc • U' i := by
                have h1 : c (Fin.last b) • u = -(∑ i : Fin b, c i.castSucc • U' i) :=
                  eq_neg_of_add_eq_zero_right hsum
                calc
                  u = (c (Fin.last b))⁻¹ • (c (Fin.last b) • u) := by
                    rw [inv_smul_smul₀ hne]
                  _ = (c (Fin.last b))⁻¹ • (-(∑ i : Fin b, c i.castSucc • U' i)) := by rw [h1]
                  _ = -(c (Fin.last b))⁻¹ • ∑ i : Fin b, c i.castSucc • U' i := by
                    rw [smul_neg, neg_smul]
              rw [hu, Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [smul_smul]
            have hinit : ∀ i : Fin b, c i.castSucc = 0 := by
              rw [Fin.sum_univ_castSucc] at hc
              simp only [hU_cast, hU_last, hlast, zero_smul, add_zero] at hc
              exact Fintype.linearIndependent_iff.mp h.1 (fun i ↦ c i.castSucc) hc
            intro i
            exact Fin.lastCases hlast hinit i
          · refine Sigma.ext ?_ ?_
            · funext i j; exact congrFun (hU_cast i) j
            · simp only [heq_eq_eq]; exact hU_last
      rw [hbij, Finset.card_sigma]
    rw [hcard_eq]
    have hfiber_card : ∀ U' ∈ Finset.univ.filter (fun U' : Matrix (Fin b) (Fin k) F ↦
        HasFullRowRank U'),
        (Finset.univ.filter fun u : Fin k → F ↦ u ∉ rowSpan U').card =
          Fintype.card F ^ k - Fintype.card F ^ b := by
      intro U' hU'
      have hli : HasFullRowRank U' := (Finset.mem_filter.mp hU').2
      have hcard_span : (Finset.univ.filter fun u : Fin k → F ↦ u ∈ rowSpan U').card =
          Fintype.card F ^ b := by
        rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := F) (V := rowSpan U')]
        congr 1
        unfold rowSpan
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      have hcompl := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun u : Fin k → F ↦ u ∈ rowSpan U')
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard_span] at hcompl
      omega
    rw [Finset.sum_congr rfl hfiber_card, Finset.sum_const, smul_eq_mul, ih,
      Fin.prod_univ_castSucc]
    simp

theorem numFullRowRank_ge_half (b k : ℕ) (hbk : b + 1 ≤ k) :
    (Fintype.card F : ℝ) ^ (b * k) ≤ 2 * (numFullRowRank F b k : ℝ) := by
  have hq : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.one_lt_card
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hprod : (numFullRowRank F b k : ℝ) =
      (Fintype.card F : ℝ) ^ (b * k) *
        ∏ i : Fin b, (1 - (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ))) := by
    rw [numFullRowRank_eq_prod]
    push_cast
    have hmul : (Fintype.card F : ℝ) ^ (b * k) = ∏ _i : Fin b, (Fintype.card F : ℝ) ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    rw [hmul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hik : i.val ≤ k := by omega
    rw [mul_sub, mul_one, zpow_sub₀ hq_pos.ne', zpow_natCast, zpow_natCast,
      mul_div_cancel₀ _ (pow_ne_zero _ hq_pos.ne')]
    have hle : (Fintype.card F) ^ i.val ≤ (Fintype.card F) ^ k :=
      Nat.pow_le_pow_right Fintype.card_pos hik
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  rw [hprod]
  have hone_sub : ∀ (s : Finset (Fin b)) (f : Fin b → ℝ),
      (∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) →
      1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have ha0 : 0 ≤ f a := (hf a (Finset.mem_insert_self a s)).1
      have ha1 : f a ≤ 1 := (hf a (Finset.mem_insert_self a s)).2
      have hih := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hprod_nn : 0 ≤ ∏ i ∈ s, (1 - f i) :=
        Finset.prod_nonneg fun i hi ↦ sub_nonneg.mpr (hf i (Finset.mem_insert_of_mem hi)).2
      nlinarith [mul_nonneg ha0
        (Finset.sum_nonneg fun i hi ↦ (hf i (Finset.mem_insert_of_mem hi)).1)]
  have hsum_geom :
      ∑ i : Fin b, (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ)) ≤
        (Fintype.card F : ℝ) ^ ((b : ℤ) - (k : ℤ)) := by
    have h1 :
        ((Fintype.card F : ℝ) - 1) *
            ∑ i : Fin b, (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ)) =
          (Fintype.card F : ℝ) ^ ((b : ℤ) - (k : ℤ)) -
            (Fintype.card F : ℝ) ^ (-(k : ℤ)) := by
      have hsum_nat :
          ((Fintype.card F : ℝ) - 1) * ∑ i : Fin b, (Fintype.card F : ℝ) ^ i.val =
            (Fintype.card F : ℝ) ^ b - 1 := by
        have h := geom_sum_mul (Fintype.card F : ℝ) b
        rw [Fin.sum_univ_eq_sum_range]
        linarith
      have hfactor :
          ∑ i : Fin b, (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ)) =
            (∑ i : Fin b, (Fintype.card F : ℝ) ^ i.val) * (Fintype.card F : ℝ) ^ (-(k : ℤ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [sub_eq_add_neg, zpow_add₀ hq_pos.ne', zpow_natCast]
      rw [hfactor, ← mul_assoc, hsum_nat, sub_mul, one_mul,
        ← zpow_natCast (Fintype.card F : ℝ) b, ← zpow_add₀ hq_pos.ne', ← sub_eq_add_neg]
    have hge1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) - 1 := by linarith
    have hnn : 0 ≤ ∑ i : Fin b, (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ)) :=
      Finset.sum_nonneg fun i _ ↦ zpow_nonneg hq_pos.le _
    have hpos_neg : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ (-(k : ℤ)) := zpow_nonneg hq_pos.le _
    nlinarith
  have hprod_ge : (1 / 2 : ℝ) ≤
      ∏ i : Fin b, (1 - (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ))) := by
    have h1 := hone_sub Finset.univ
      (fun i : Fin b ↦ (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ)))
      (fun i _ ↦ ⟨zpow_nonneg hq_pos.le _, by
        have hle : ((i.val : ℤ) - (k : ℤ)) ≤ 0 := by omega
        calc
          (Fintype.card F : ℝ) ^ ((i.val : ℤ) - (k : ℤ)) ≤ (Fintype.card F : ℝ) ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (by linarith) hle
          _ = 1 := zpow_zero _⟩)
    have hbk_z : ((b : ℤ) - (k : ℤ)) ≤ (-1 : ℤ) := by omega
    have hqbk : (Fintype.card F : ℝ) ^ ((b : ℤ) - (k : ℤ)) ≤ (1 / 2 : ℝ) := by
      calc
        (Fintype.card F : ℝ) ^ ((b : ℤ) - (k : ℤ)) ≤ (Fintype.card F : ℝ) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ (by linarith) hbk_z
        _ = (Fintype.card F : ℝ)⁻¹ := zpow_neg_one _
        _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
        _ = 1 / 2 := by norm_num
    linarith
  have hpow_nn : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ (b * k) := by positivity
  nlinarith

/-- Upper bound on the number of full-row-rank `U₂` whose row span intersects `rowSpan U₁` in
dimension `d`. -/
theorem card_fullRowRank_inter_le {a k d : ℕ} {U₁ : Matrix (Fin a) (Fin k) F}
    (hU₁ : HasFullRowRank U₁) (_hd : d ≤ a) :
    {U₂ : Matrix (Fin a) (Fin k) F |
      HasFullRowRank U₂ ∧ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d}.ncard ≤
      Fintype.card F ^ (2 * a * d + (a - d) * k) := by
  classical
  let S_C : Finset (Matrix (Fin d) (Fin a) F) :=
    Finset.univ.filter fun C : Matrix (Fin d) (Fin a) F ↦ HasFullRowRank C
  let S_B : Finset (Matrix (Fin d) (Fin k) F) :=
    Finset.univ.filter fun B : Matrix (Fin d) (Fin k) F ↦ ∀ r : Fin d, B r ∈ rowSpan U₁
  have hcov :
      (Finset.univ.filter fun U₂ : Matrix (Fin a) (Fin k) F ↦
        HasFullRowRank U₂ ∧ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d) ⊆
      (S_C ×ˢ S_B).biUnion fun p ↦
        Finset.univ.filter fun U₂ : Matrix (Fin a) (Fin k) F ↦ p.1 * U₂ = p.2 := by
    intro U₂ hU₂
    obtain ⟨hU₂_rank, hdim⟩ := (Finset.mem_filter.mp hU₂).2
    let W := rowSpan U₁ ⊓ rowSpan U₂
    let bW := Module.finBasis F W
    let B : Matrix (Fin d) (Fin k) F := fun r ↦ (bW (r.cast hdim.symm) : Fin k → F)
    have hB_mem : ∀ r : Fin d, B r ∈ rowSpan U₁ ∧ B r ∈ rowSpan U₂ := fun r ↦
      (bW (r.cast hdim.symm)).2
    have hexC : ∀ r : Fin d, ∃ c : Fin a → F, Matrix.vecMul c U₂ = B r := fun r ↦ by
      have hr := (hB_mem r).2
      rw [rowSpan, Submodule.mem_span_range_iff_exists_fun] at hr
      obtain ⟨c, hc⟩ := hr
      refine ⟨c, ?_⟩
      ext j
      have hj := congrFun hc j
      simpa [Matrix.vecMul, dotProduct] using hj
    choose C_fun hC using hexC
    let C : Matrix (Fin d) (Fin a) F := C_fun
    have hCU₂ : C * U₂ = B := by
      ext r j
      have hj := congrFun (hC r) j
      rw [Matrix.mul_apply]
      simpa [C, Matrix.vecMul, dotProduct] using hj
    have hB_li : HasFullRowRank B := by
      unfold HasFullRowRank
      have hsub := bW.linearIndependent.comp (Fin.cast hdim.symm)
        (Fin.cast_injective hdim.symm)
      exact (W.subtype.linearIndependent_iff_of_injOn
        (Submodule.injective_subtype W).injOn).mpr hsub
    have hC_li : HasFullRowRank C := by
      rw [hasFullRowRank_iff_vecMul_injective] at hB_li ⊢
      intro u v huv
      apply hB_li
      dsimp only at huv
      change Matrix.vecMul u B = Matrix.vecMul v B
      rw [← hCU₂, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, huv]
    refine Finset.mem_biUnion.mpr ⟨(C, B), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_li⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r ↦ (hB_mem r).1⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCU₂⟩
  have h1 := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have h2 :
      ∑ p ∈ S_C ×ˢ S_B,
          (Finset.univ.filter fun U₂ : Matrix (Fin a) (Fin k) F ↦ p.1 * U₂ = p.2).card =
        S_C.card * S_B.card * Fintype.card F ^ ((a - d) * k) := by
    have hconst : ∀ p ∈ S_C ×ˢ S_B,
        (Finset.univ.filter fun U₂ : Matrix (Fin a) (Fin k) F ↦ p.1 * U₂ = p.2).card =
          Fintype.card F ^ ((a - d) * k) := fun p hp ↦
      card_matrix_mul_eq_of_fullRowRank (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2 p.2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, Finset.card_product]
  rw [h2] at h1
  have hC_le : S_C.card ≤ Fintype.card F ^ (d * a) := by
    calc
      S_C.card ≤ Fintype.card (Matrix (Fin d) (Fin a) F) := Finset.card_filter_le _ _
      _ = Fintype.card F ^ (d * a) := by
          change Fintype.card (Fin d → Fin a → F) = Fintype.card F ^ (d * a)
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            ← pow_mul, mul_comm]
  have hB_le : S_B.card ≤ Fintype.card F ^ (a * d) := by
    have hcard_row : Fintype.card (rowSpan U₁) = Fintype.card F ^ a := by
      rw [Module.card_eq_pow_finrank (K := F) (V := rowSpan U₁),
        (hasFullRowRank_iff_finrank U₁).mp hU₁]
    have hB_eq : S_B.card = Fintype.card (Fin d → rowSpan U₁) := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr
        { toFun := fun ⟨B, hB⟩ r ↦ ⟨B r, hB r⟩
          invFun := fun f ↦ ⟨fun r ↦ (f r : Fin k → F), fun r ↦ (f r).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    rw [hB_eq, Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard_row,
      ← pow_mul]
  have hncard :
      {U₂ : Matrix (Fin a) (Fin k) F |
        HasFullRowRank U₂ ∧ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d}.ncard =
      (Finset.univ.filter fun U₂ : Matrix (Fin a) (Fin k) F ↦
        HasFullRowRank U₂ ∧ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d).card := by
    rw [← Set.ncard_coe_finset]
    congr 1; ext U₂; simp
  rw [hncard]
  calc
    (Finset.univ.filter fun U₂ : Matrix (Fin a) (Fin k) F ↦
        HasFullRowRank U₂ ∧ Module.finrank F ↥(rowSpan U₁ ⊓ rowSpan U₂) = d).card
        ≤ S_C.card * S_B.card * Fintype.card F ^ ((a - d) * k) := h1
    _ ≤ Fintype.card F ^ (d * a) * Fintype.card F ^ (a * d) *
          Fintype.card F ^ ((a - d) * k) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hC_le hB_le)
    _ = Fintype.card F ^ (2 * a * d + (a - d) * k) := by
      rw [← pow_add, ← pow_add]
      congr 1; ring

end MatrixRank

end CslibFrontier.Foundations.Data.Code
