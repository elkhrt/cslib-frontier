module

public import CslibFrontier.Foundations.Data.Code.FieldMatrixRank
public import Mathlib.Data.Set.Card

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local, Row-Symmetric, and Scalar-Invariant Properties of Linear Codes

This module develops the framework of monotone-increasing, `b`-local, row-symmetric, and
scalar-invariant properties of linear codes over finite fields, minimal sets and minimal types,
implied distributions, and the Mosheiff–Resch–Ron-Zewi–Silas–Wootters (MRRSW) Random Linear Code
(RLC) Threshold Theorem with both first-moment upper bounds and Chebyshev second-moment lower
bounds. All results are proved under standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Main definitions

* `CslibFrontier.Foundations.Data.Code.permuteCode`, `scaleCode`: coordinate-permutation and
  diagonal-scaling actions on linear codes.
* `CslibFrontier.Foundations.Data.Code.IsMonotoneIncreasing`, `IsBLocal`, `IsRowSymmetric`,
  `IsScalarInvariant`: structural properties of linear-code families.
* `CslibFrontier.Foundations.Data.Code.IsMinimalMatrix`, `IsMinimalType`, `minimalTypesFinset`:
  minimal matrices `ℳ_𝒫` and minimal types `𝒯_𝒫`.
* `CslibFrontier.Foundations.Data.Code.IsImpliedDist`: implied distributions `ℐ_τ`.
* `CslibFrontier.Foundations.Data.Code.rlcProb`, `rlcThreshold`, `mrrswRate`: RLC probability,
  threshold rate `R_RLC(𝒫)`, and the MRRSW variational rate `min_{τ ∈ 𝒯_𝒫} max_{τ' ∈ ℐ_τ}`.

## Main results

* `CslibFrontier.Foundations.Data.Code.exists_isMinimalMatrix_of_sat`: every code satisfying a
  monotone-increasing `b`-local property contains a minimal matrix with at most `b` columns.
* `CslibFrontier.Foundations.Data.Code.card_minimalTypesFinset_le`: `|𝒯_𝒫| ≤ (n + 1) ^ (q ^ b)`.
* `CslibFrontier.Foundations.Data.Code.mrrswRate_nonneg`, `mrrswRate_le_one`,
  `le_mrrswRate_of_forall_minimalType`, `exists_implied_of_mem_minimalTypes`: variational bounds.
* `CslibFrontier.Foundations.Data.Code.rlcThreshold_mono`: monotonicity of `rlcThreshold`.

## Tags

random linear codes, threshold theorem, local properties, coding theory
-/

public section

namespace CslibFrontier.Foundations.Data.Code

section CodePropertiesBase

variable {F : Type*} [Field F]

/-- Coordinate-permutation image of a linear code `C` under `π : Equiv.Perm (Fin n)`. -/
def permuteCode {n : ℕ} (C : Submodule F (Fin n → F)) (π : Equiv.Perm (Fin n)) :
    Submodule F (Fin n → F) :=
  C.map (LinearEquiv.funCongrLeft F F π).toLinearMap

/-- Diagonal-scaling image of a linear code `C` under `Λ : Fin n → Fˣ`. -/
def scaleCode {n : ℕ} (C : Submodule F (Fin n → F)) (Λ : Fin n → Fˣ) :
    Submodule F (Fin n → F) :=
  C.map
    ({ toFun := fun u i ↦ (Λ i : F) * u i
       map_add' := fun u v ↦ funext fun i ↦ mul_add _ _ _
       map_smul' := fun c u ↦ funext fun i ↦ by
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         ring } : (Fin n → F) →ₗ[F] (Fin n → F))

theorem permuteCode_eq_map {n : ℕ} (C : Submodule F (Fin n → F)) (π : Equiv.Perm (Fin n)) :
    permuteCode C π = C.map (LinearEquiv.funCongrLeft F F π).toLinearMap := by rfl

@[simp]
theorem mem_permuteCode {n : ℕ} {C : Submodule F (Fin n → F)} {π : Equiv.Perm (Fin n)}
    {u : Fin n → F} :
    u ∈ permuteCode C π ↔ (fun i ↦ u (π⁻¹ i)) ∈ C := by
  simp only [permuteCode, Submodule.mem_map, LinearEquiv.coe_coe,
    LinearEquiv.funCongrLeft_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    convert hv using 1
    ext i; simp
  · intro hu
    exact ⟨fun i ↦ u (π⁻¹ i), hu, funext fun i ↦ by simp⟩

@[simp]
theorem mem_scaleCode {n : ℕ} {C : Submodule F (Fin n → F)} {Λ : Fin n → Fˣ} {u : Fin n → F} :
    u ∈ scaleCode C Λ ↔ (fun i ↦ ((Λ i)⁻¹ : Fˣ) * u i) ∈ C := by
  simp only [scaleCode, Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · rintro ⟨v, hv, rfl⟩
    convert hv using 1
    ext i; simp
  · intro hu
    exact ⟨fun i ↦ ((Λ i)⁻¹ : Fˣ) * u i, hu, funext fun i ↦ by simp⟩

@[simp]
theorem permuteCode_one {n : ℕ} (C : Submodule F (Fin n → F)) : permuteCode C 1 = C := by
  ext u; simp

@[simp]
theorem scaleCode_one {n : ℕ} (C : Submodule F (Fin n → F)) : scaleCode C 1 = C := by
  ext u; simp

/-- A linear-code property `P` is monotone-increasing if `C₁ ≤ C₂ → P C₁ → P C₂`. -/
def IsMonotoneIncreasing {n : ℕ} (P : Submodule F (Fin n → F) → Prop) : Prop :=
  ∀ C₁ C₂ : Submodule F (Fin n → F), C₁ ≤ C₂ → P C₁ → P C₂

theorem isMonotoneIncreasing_iff {n : ℕ} {P : Submodule F (Fin n → F) → Prop} :
    IsMonotoneIncreasing P ↔
      ∀ C₁ C₂ : Submodule F (Fin n → F), C₁ ≤ C₂ → P C₁ → P C₂ := by rfl

/-- A linear-code property `P` is `b`-local if it is witnessed by sets of size `≤ b`. -/
def IsBLocal {n : ℕ} (b : ℕ) (P : Submodule F (Fin n → F) → Prop) : Prop :=
  ∃ ℬ : Set (Set (Fin n → F)), (∀ B ∈ ℬ, B.ncard ≤ b) ∧
    ∀ C : Submodule F (Fin n → F), P C ↔ ∃ B ∈ ℬ, B ⊆ (C : Set (Fin n → F))

theorem isBLocal_iff {n : ℕ} {b : ℕ} {P : Submodule F (Fin n → F) → Prop} :
    IsBLocal b P ↔
      ∃ ℬ : Set (Set (Fin n → F)), (∀ B ∈ ℬ, B.ncard ≤ b) ∧
        ∀ C : Submodule F (Fin n → F), P C ↔ ∃ B ∈ ℬ, B ⊆ (C : Set (Fin n → F)) := by rfl

/-- A linear-code property `P` is row-symmetric if it is invariant under coordinate permutations. -/
def IsRowSymmetric {n : ℕ} (P : Submodule F (Fin n → F) → Prop) : Prop :=
  ∀ (C : Submodule F (Fin n → F)) (π : Equiv.Perm (Fin n)), P C → P (permuteCode C π)

theorem isRowSymmetric_iff {n : ℕ} {P : Submodule F (Fin n → F) → Prop} :
    IsRowSymmetric P ↔
      ∀ (C : Submodule F (Fin n → F)) (π : Equiv.Perm (Fin n)), P C → P (permuteCode C π) := by
  rfl

/-- A linear-code property `P` is scalar-invariant if it is invariant under diagonal scalings. -/
def IsScalarInvariant {n : ℕ} (P : Submodule F (Fin n → F) → Prop) : Prop :=
  ∀ (C : Submodule F (Fin n → F)) (Λ : Fin n → Fˣ), P C → P (scaleCode C Λ)

theorem isScalarInvariant_iff {n : ℕ} {P : Submodule F (Fin n → F) → Prop} :
    IsScalarInvariant P ↔
      ∀ (C : Submodule F (Fin n → F)) (Λ : Fin n → Fˣ), P C → P (scaleCode C Λ) := by rfl

/-- A full-column-rank matrix `A` belongs to the minimal set `ℳ_𝒫` if `colSpan A` satisfies `P`
and no proper subspace of `colSpan A` satisfies `P`. -/
def IsMinimalMatrix {n : ℕ} (P : Submodule F (Fin n → F) → Prop) {b : ℕ}
    (A : Matrix (Fin n) (Fin b) F) : Prop :=
  HasFullColRank A ∧ P (colSpan A) ∧ ∀ W : Submodule F (Fin n → F), W < colSpan A → ¬ P W

theorem isMinimalMatrix_iff {n : ℕ} {P : Submodule F (Fin n → F) → Prop} {b : ℕ}
    {A : Matrix (Fin n) (Fin b) F} :
    IsMinimalMatrix P A ↔
      HasFullColRank A ∧ P (colSpan A) ∧ ∀ W : Submodule F (Fin n → F), W < colSpan A → ¬ P W := by
  rfl

/-- A distribution `τ` over `Fin b → F` is a minimal type of `P` (`τ ∈ 𝒯_𝒫`) if `τ = empDist A`
for some minimal matrix `A ∈ ℳ_𝒫`. -/
def IsMinimalType {n : ℕ} (hn : 0 < n) (P : Submodule F (Fin n → F) → Prop) {b : ℕ}
    (τ : PMF (Fin b → F)) : Prop :=
  ∃ A : Matrix (Fin n) (Fin b) F, IsMinimalMatrix P A ∧ empDist hn A = τ

theorem isMinimalType_iff {n : ℕ} {hn : 0 < n} {P : Submodule F (Fin n → F) → Prop} {b : ℕ}
    {τ : PMF (Fin b → F)} :
    IsMinimalType hn P τ ↔
      ∃ A : Matrix (Fin n) (Fin b) F, IsMinimalMatrix P A ∧ empDist hn A = τ := by rfl

/-- A distribution `τ'` over `Fin a → F` is `τ`-implied (`τ' ∈ ℐ_τ`) if `τ'` is the law of `x D`
for `x ~ τ` and some full-column-rank `D : Matrix (Fin b) (Fin a) F`. -/
def IsImpliedDist {b a : ℕ} (τ : PMF (Fin b → F)) (τ' : PMF (Fin a → F)) : Prop :=
  ∃ D : Matrix (Fin b) (Fin a) F, HasFullColRank D ∧ τ.map (fun x ↦ Matrix.vecMul x D) = τ'

theorem isImpliedDist_iff {b a : ℕ} {τ : PMF (Fin b → F)} {τ' : PMF (Fin a → F)} :
    IsImpliedDist τ τ' ↔
      ∃ D : Matrix (Fin b) (Fin a) F, HasFullColRank D ∧
        τ.map (fun x ↦ Matrix.vecMul x D) = τ' := by rfl

theorem isFullRankDist_of_isImpliedDist {n b a : ℕ} (hn : 0 < n)
    {τ : PMF (Fin b → F)} {τ' : PMF (Fin a → F)} (hfe : IsFeasibleType n hn τ)
    (hfull : IsFullRankDist τ) (himp : IsImpliedDist τ τ') :
    IsFullRankDist τ' := by
  obtain ⟨A₀, hA⟩ := isFeasibleType_iff.mp hfe
  let A : Matrix (Fin n) (Fin b) F := A₀
  obtain ⟨D, hD, hmap⟩ := himp
  have hfullA : HasFullColRank A := (isFullRankDist_empDist_iff hn A).mp (hA.symm ▸ hfull)
  have hAD : empDist hn (A * D) = τ' := by
    have hm : empDist hn (A * D) = (empDist hn A).map (fun x ↦ Matrix.vecMul x D) := by
      rw [empDist_map]
      congr 1
    rw [hm, hA, hmap]
  rw [← hAD, isFullRankDist_empDist_iff]
  exact hasFullColRank_mul hfullA hD

/-- Any code satisfying a monotone-increasing `b`-local property `P` contains a minimal matrix
with at most `b` columns. -/
theorem exists_isMinimalMatrix_of_sat [Finite F] {n b : ℕ}
    {P : Submodule F (Fin n → F) → Prop}
    (_hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    {C : Submodule F (Fin n → F)} (hC : P C) :
    ∃ a ≤ b, ∃ A : Matrix (Fin n) (Fin a) F, IsMinimalMatrix P A ∧ MatrixContainedIn A C := by
  classical
  let S : Set ℕ := {d | ∃ W : Submodule F (Fin n → F), W ≤ C ∧ P W ∧ Module.finrank F W = d}
  have hSne : S.Nonempty := ⟨Module.finrank F C, C, le_refl C, hC, rfl⟩
  let d₀ := Nat.find hSne
  obtain ⟨W, hWC, hPW, hWdim⟩ := Nat.find_spec hSne
  have hWmin : ∀ U : Submodule F (Fin n → F), U < W → ¬ P U := by
    intro U hUW hPU
    have hlt : Module.finrank F U < d₀ := by
      dsimp only [d₀]; rw [← hWdim]
      exact Submodule.finrank_lt_finrank_of_lt hUW
    exact Nat.find_min hSne hlt ⟨U, le_trans hUW.le hWC, hPU, rfl⟩
  obtain ⟨ℬ, hℬcard, hℬiff⟩ := hloc
  obtain ⟨B, hBmem, hBW⟩ := (hℬiff W).mp hPW
  have hspan_le : Submodule.span F B ≤ W := Submodule.span_le.mpr hBW
  have hPspan : P (Submodule.span F B) := (hℬiff _).mpr ⟨B, hBmem, Submodule.subset_span⟩
  have hspan_eq : Submodule.span F B = W := by
    by_contra hne
    exact hWmin (Submodule.span F B) (lt_of_le_of_ne hspan_le hne) hPspan
  have hWle_b : Module.finrank F W ≤ b := by
    rw [← hspan_eq]
    have hfin : B.Finite := Set.toFinite B
    have h1 : Module.finrank F (Submodule.span F B) ≤ B.ncard := by
      rw [Set.ncard_eq_toFinset_card B hfin]
      have h2 := finrank_span_le_card (R := F) (hfin.toFinset : Set (Fin n → F))
      have hcard : (hfin.toFinset : Set (Fin n → F)).toFinset = hfin.toFinset := by
        ext x; simp
      rw [hcard] at h2
      rwa [hfin.coe_toFinset] at h2
    exact h1.trans (hℬcard B hBmem)
  let basis := Module.finBasis F W
  let A : Matrix (Fin n) (Fin d₀) F :=
    fun i j ↦ (basis (j.cast hWdim.symm) : Fin n → F) i
  have hA_colSpan : colSpan A = W := by
    apply le_antisymm
    · rw [colSpan_eq_span_range, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (basis (j.cast hWdim.symm)).2
    · intro v hv
      have hv' : (⟨v, hv⟩ : W) ∈ Submodule.span F (Set.range basis) := by
        rw [basis.span_eq]; trivial
      have hmap : (Submodule.span F (Set.range basis)).map W.subtype ≤ colSpan A := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        rw [colSpan_eq_span_range]
        exact Submodule.subset_span ⟨j.cast hWdim, rfl⟩
      exact hmap ⟨⟨v, hv⟩, hv', rfl⟩
  have hA_rank : HasFullColRank A := by
    rw [hasFullColRank_iff_finrank, hA_colSpan, hWdim]
  refine ⟨d₀, by dsimp only [d₀]; rw [← hWdim]; exact hWle_b, A,
    ⟨hA_rank, hA_colSpan ▸ hPW, hA_colSpan ▸ hWmin⟩, ?_⟩
  rw [matrixContainedIn_iff_colSpan_le, hA_colSpan]
  exact hWC

/-- If `P` is row-symmetric, then `IsMinimalMatrix P A` depends only on `empDist hn A`. -/
theorem isMinimalMatrix_of_empDist_eq {n b : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} (hrow : IsRowSymmetric P)
    {A B : Matrix (Fin n) (Fin b) F} (hA : IsMinimalMatrix P A)
    (heq : empDist hn A = empDist hn B) :
    IsMinimalMatrix P B := by
  obtain ⟨π, hπ⟩ := (empDist_eq_iff_exists_perm hn A B).mp heq
  have hBcol : colSpan B = permuteCode (colSpan A) π := by
    ext v
    rw [mem_permuteCode]
    have hcomp : ∀ j : Fin b, (fun i : Fin n ↦ B i j) = (fun i ↦ A (π i) j) := fun j ↦ by
      ext i; exact congrFun (congrFun hπ.symm i) j
    rw [colSpan_eq_span_range, colSpan_eq_span_range]
    rw [Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_range_iff_exists_fun]
    constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩
    · ext i
      have hi := congrFun hc (π⁻¹ i)
      simpa [hcomp, Finset.sum_apply] using hi
    · ext i
      have hi := congrFun hc (π i)
      simpa [hcomp, Finset.sum_apply] using hi
  refine ⟨?_, ?_, ?_⟩
  · rw [hasFullColRank_iff_finrank, hBcol, permuteCode, LinearEquiv.finrank_map_eq]
    exact (hasFullColRank_iff_finrank A).mp hA.1
  · rw [hBcol]
    exact hrow (colSpan A) π hA.2.1
  · intro W hW hPW
    have hlt : permuteCode W π⁻¹ < colSpan A := by
      have hle : permuteCode W π⁻¹ ≤ colSpan A := by
        intro v hv
        have h1 : (fun i ↦ v (π i)) ∈ W := by simpa using mem_permuteCode.mp hv
        have h2 : (fun i ↦ v (π i)) ∈ permuteCode (colSpan A) π := hBcol ▸ hW.le h1
        have h3 := mem_permuteCode.mp h2
        simpa using h3
      refine lt_of_le_of_ne hle ?_
      intro heq'
      apply hW.ne
      rw [hBcol]
      ext v
      rw [mem_permuteCode, ← heq', mem_permuteCode]
      simp
    exact hA.2.2 (permuteCode W π⁻¹) hlt (hrow W π⁻¹ hPW)

theorem isFeasibleType_of_isImpliedDist {n b a : ℕ} (hn : 0 < n)
    {τ : PMF (Fin b → F)} {τ' : PMF (Fin a → F)} (hfe : IsFeasibleType n hn τ)
    (himp : IsImpliedDist τ τ') : IsFeasibleType n hn τ' := by
  obtain ⟨A₀, hA⟩ := isFeasibleType_iff.mp hfe
  let A : Matrix (Fin n) (Fin b) F := A₀
  obtain ⟨D, _, hD⟩ := himp
  rw [isFeasibleType_iff]
  refine ⟨A * D, ?_⟩
  have hmap : empDist hn (A * D) = (empDist hn A).map (fun x ↦ Matrix.vecMul x D) := by
    rw [empDist_map]
    congr 1
  rw [hmap, hA, hD]

end CodePropertiesBase

section CodeProperties

variable {F : Type*} [Field F] [Fintype F]

/-- Observation (Implied motivation): if `τ' ∈ ℐ_τ` and a linear code `C` contains a matrix in
`ℳ_{n,τ}`, then `C` contains a matrix in `ℳ_{n,τ'}`. -/
theorem exists_mem_typeClass_of_isImpliedDist {n b a : ℕ} (hn : 0 < n)
    {τ : PMF (Fin b → F)} {τ' : PMF (Fin a → F)} (himp : IsImpliedDist τ τ')
    {C : Submodule F (Fin n → F)} {A : Matrix (Fin n) (Fin b) F}
    (hA : A ∈ typeClassFinset n hn τ) (hAC : MatrixContainedIn A C) :
    ∃ A' : Matrix (Fin n) (Fin a) F,
      A' ∈ typeClassFinset n hn τ' ∧ MatrixContainedIn A' C := by
  obtain ⟨D, _, hD⟩ := himp
  refine ⟨A * D, ?_, ?_⟩
  · refine mem_typeClassFinset.mpr ?_
    have hmap : empDist hn (fun i j ↦ (A * D) i j) =
        (empDist hn (fun i j ↦ A i j)).map (fun x ↦ Matrix.vecMul x D) :=
      (empDist_map hn (fun i j ↦ A i j) (fun x ↦ Matrix.vecMul x D)).symm
    change empDist hn (fun i j ↦ (A * D) i j) = τ'
    rw [hmap, mem_typeClassFinset.mp hA, hD]
  · rw [matrixContainedIn_iff_colSpan_le, colSpan_eq_span_range, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hcolA : ∀ k : Fin b, (fun i : Fin n ↦ A i k) ∈ C := fun k ↦
      (matrixContainedIn_iff_colSpan_le A C).mp hAC (by
        rw [colSpan_eq_span_range]; exact Submodule.subset_span ⟨k, rfl⟩)
    have hcol : (fun i : Fin n ↦ (A * D) i j) =
        ∑ k : Fin b, D k j • (fun i : Fin n ↦ A i k) := by
      ext i
      simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
    dsimp only
    rw [hcol]
    exact C.sum_mem fun k _ ↦ C.smul_mem _ (hcolA k)

/-- Finite set of all minimal types of `P` with at most `b` columns. -/
noncomputable def minimalTypesFinset {n : ℕ} (hn : 0 < n) (b : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    Finset (Σ a : Fin (b + 1), PMF (Fin a.val → F)) := by
  classical
  exact Finset.univ.sigma (fun a : Fin (b + 1) ↦
    (feasibleTypesFinset (Fin a.val → F) n hn).filter fun τ ↦ IsMinimalType hn P τ)

theorem mem_minimalTypesFinset_iff {n : ℕ} (hn : 0 < n) (b : ℕ)
    (P : Submodule F (Fin n → F) → Prop) (p : Σ a : Fin (b + 1), PMF (Fin a.val → F)) :
    p ∈ minimalTypesFinset hn b P ↔ IsFeasibleType n hn p.2 ∧ IsMinimalType hn P p.2 := by
  classical
  simp only [minimalTypesFinset, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter, mem_feasibleTypesFinset]

/-- Fact (`fact:PropertyDecomposition`): the set of minimal types of a `b`-local property has
cardinality at most `(n + 1) ^ (q ^ b)`. -/
theorem card_minimalTypesFinset_le {n : ℕ} (hn : 0 < n) (b : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    (minimalTypesFinset hn b P).card ≤ (n + 1) ^ (Fintype.card F ^ b) := by
  classical
  let padVec : (a : Fin (b + 1)) → (Fin a.val → F) → (Fin b → F) := fun a x i ↦
    if h : i.val < a.val then x ⟨i.val, h⟩ else 0
  let pad : (Σ a : Fin (b + 1), PMF (Fin a.val → F)) → PMF (Fin b → F) :=
    fun p ↦ p.2.map (padVec p.1)
  have hmem : ∀ p ∈ minimalTypesFinset hn b P,
      pad p ∈ feasibleTypesFinset (Fin b → F) n hn := by
    intro ⟨a, τ⟩ hp
    rw [mem_minimalTypesFinset_iff] at hp
    dsimp only at hp
    obtain ⟨A, _, rfl⟩ := hp.2
    rw [mem_feasibleTypesFinset, isFeasibleType_iff]
    exact ⟨fun i ↦ padVec a (A i), (empDist_map hn A (padVec a)).symm⟩
  have hinj : Set.InjOn pad (minimalTypesFinset hn b P : Set _) := by
    intro ⟨a₁, τ₁⟩ h₁ ⟨a₂, τ₂⟩ h₂ hpad
    rw [Finset.mem_coe, mem_minimalTypesFinset_iff] at h₁ h₂
    dsimp only at h₁ h₂
    obtain ⟨A₁, hA₁, rfl⟩ := h₁.2
    obtain ⟨A₂, hA₂, rfl⟩ := h₂.2
    have hdim : ∀ (a : Fin (b + 1)) (A : Matrix (Fin n) (Fin a.val) F),
        HasFullColRank A → distDim ((empDist hn A).map (padVec a)) = a.val := by
      intro a A hA
      let B : Matrix (Fin n) (Fin b) F := fun i j ↦ padVec a (A i) j
      have heq : (empDist hn A).map (padVec a) = empDist hn B :=
        empDist_map hn A (padVec a)
      rw [heq, distDim_empDist]
      have hcol_eq : colSpan B = colSpan A := by
        apply le_antisymm
        · rw [colSpan_eq_span_range, Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          dsimp only
          by_cases hj : j.val < a.val
          · have hcol : (fun i : Fin n ↦ B i j) = fun i ↦ A i ⟨j.val, hj⟩ := by
              ext i; simp [B, padVec, hj]
            rw [hcol, colSpan_eq_span_range]
            exact Submodule.subset_span ⟨⟨j.val, hj⟩, rfl⟩
          · have hcol : (fun i : Fin n ↦ B i j) = 0 := by
              ext i; simp [B, padVec, hj]
            rw [hcol]
            exact (colSpan A).zero_mem
        · rw [colSpan_eq_span_range, Submodule.span_le]
          rintro _ ⟨k, rfl⟩
          dsimp only
          have hk : k.val < b := Nat.lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ a.isLt)
          have hcol : (fun i : Fin n ↦ A i k) = fun i ↦ B i ⟨k.val, hk⟩ := by
            ext i; simp [B, padVec, k.isLt]
          rw [hcol, colSpan_eq_span_range]
          exact Submodule.subset_span ⟨⟨k.val, hk⟩, rfl⟩
      rw [hcol_eq]
      exact (hasFullColRank_iff_finrank A).mp hA
    have ha : a₁ = a₂ := Fin.ext (by
      have h1 := hdim a₁ A₁ hA₁.1
      have h2 := hdim a₂ A₂ hA₂.1
      dsimp only [pad] at hpad
      rw [hpad] at h1
      omega)
    subst ha
    refine Sigma.ext rfl (heq_of_eq ?_)
    have hpad_inj : Function.Injective (padVec a₁) := by
      intro x y hxy
      ext ⟨k, hk⟩
      have := congrFun hxy ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_of_lt_succ a₁.isLt)⟩
      simpa [padVec, hk] using this
    ext x
    have hx := congrArg (fun p : PMF (Fin b → F) ↦ p (padVec a₁ x)) hpad
    dsimp only [pad] at hx
    simpa [PMF.map_apply, hpad_inj.eq_iff] using hx
  calc
    (minimalTypesFinset hn b P).card
        = ((minimalTypesFinset hn b P).image pad).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (feasibleTypesFinset (Fin b → F) n hn).card :=
      Finset.card_le_card (Finset.image_subset_iff.mpr hmem)
    _ ≤ (n + 1) ^ Fintype.card (Fin b → F) := card_feasibleTypesFinset_le _ n hn
    _ = (n + 1) ^ (Fintype.card F ^ b) := by simp [Fintype.card_pi]

end CodeProperties

/-! ### Random Linear Code Probability, Threshold, and the MRRSW Theorem -/

section RLC

/-- Random Linear Code (RLC) probability: the uniform probability over
`G : Matrix (Fin k) (Fin n) F` that `rowSpan G` satisfies `P`. -/
noncomputable def rlcProb (F : Type*) [Field F] [Fintype F] (n k : ℕ)
    (P : Submodule F (Fin n → F) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦ P (rowSpan G)).card : ℝ) /
    (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)

theorem rlcProb_eq_card_div (F : Type*) [Field F] [Fintype F] (n k : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    rlcProb F n k P =
      (by classical
          exact ((Finset.univ.filter fun G : Matrix (Fin k) (Fin n) F ↦
            P (rowSpan G)).card : ℝ) /
            (Fintype.card (Matrix (Fin k) (Fin n) F) : ℝ)) := by rfl

theorem rlcProb_nonneg (F : Type*) [Field F] [Fintype F] (n k : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    0 ≤ rlcProb F n k P := by
  unfold rlcProb
  positivity

theorem rlcProb_le_one (F : Type*) [Field F] [Fintype F] (n k : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    rlcProb F n k P ≤ 1 := by
  classical
  unfold rlcProb
  rw [div_le_one (Nat.cast_pos.mpr Fintype.card_pos)]
  exact_mod_cast Finset.card_filter_le _ _

@[gcongr]
theorem rlcProb_mono {F : Type*} [Field F] [Fintype F] {n k : ℕ}
    {P Q : Submodule F (Fin n → F) → Prop} (h : ∀ C, P C → Q C) :
    rlcProb F n k P ≤ rlcProb F n k Q := by
  classical
  unfold rlcProb
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right _ fun G _ ↦ h (rowSpan G))

/-- The RLC threshold rate `R_RLC(𝒫) = min { R = k/n ∈ [0,1] | Pr[RLC(R) ∈ 𝒫] ≥ 1/2 }`
(with `1` inserted so the infimum is well-defined even if `Pr[RLC(n/n) ∈ 𝒫] < 1/2`). -/
noncomputable def rlcThreshold (F : Type*) [Field F] [Fintype F] (n : ℕ)
    (P : Submodule F (Fin n → F) → Prop) : ℝ :=
  sInf (insert (1 : ℝ) {R : ℝ | ∃ k ≤ n, R = (k : ℝ) / (n : ℝ) ∧ (1 / 2 : ℝ) ≤ rlcProb F n k P})

theorem rlcThreshold_le_one (F : Type*) [Field F] [Fintype F] (n : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    rlcThreshold F n P ≤ 1 := by
  refine csInf_le ?_ (Set.mem_insert 1 _)
  refine ⟨0, ?_⟩
  rintro R (rfl | ⟨k, _, rfl, _⟩)
  · norm_num
  · positivity

theorem rlcThreshold_nonneg (F : Type*) [Field F] [Fintype F] (n : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    0 ≤ rlcThreshold F n P := by
  refine le_csInf (Set.insert_nonempty 1 _) ?_
  rintro R (rfl | ⟨k, _, rfl, _⟩)
  · norm_num
  · positivity

theorem rlcThreshold_le_of_prob_ge {F : Type*} [Field F] [Fintype F] {n k : ℕ}
    {P : Submodule F (Fin n → F) → Prop} (hk : k ≤ n) (hprob : (1 / 2 : ℝ) ≤ rlcProb F n k P) :
    rlcThreshold F n P ≤ (k : ℝ) / (n : ℝ) := by
  refine csInf_le ?_ (Set.mem_insert_of_mem _ ⟨k, hk, rfl, hprob⟩)
  refine ⟨0, ?_⟩
  rintro R (rfl | ⟨k', _, rfl, _⟩)
  · norm_num
  · positivity

theorem le_rlcThreshold_of_forall_lt {F : Type*} [Field F] [Fintype F] {n : ℕ}
    {P : Submodule F (Fin n → F) → Prop} {r : ℝ} (hr : r ≤ 1)
    (h : ∀ k ≤ n, (k : ℝ) / (n : ℝ) < r → rlcProb F n k P < 1 / 2) :
    r ≤ rlcThreshold F n P := by
  refine le_csInf (Set.insert_nonempty 1 _) ?_
  rintro R (rfl | ⟨k, hk, rfl, hprob⟩)
  · exact hr
  · by_contra hlt
    exact not_lt_of_ge hprob (h k hk (not_le.mp hlt))

theorem rlcThreshold_mono {F : Type*} [Field F] [Fintype F] {n : ℕ}
    {P Q : Submodule F (Fin n → F) → Prop} (h : ∀ C, P C → Q C) :
    rlcThreshold F n Q ≤ rlcThreshold F n P := by
  refine le_csInf (Set.insert_nonempty 1 _) ?_
  rintro R (rfl | ⟨k, hk, rfl, hprob⟩)
  · exact rlcThreshold_le_one F n Q
  · exact rlcThreshold_le_of_prob_ge hk (hprob.trans (rlcProb_mono h))

/-- The MRRSW variational rate `min_{τ ∈ 𝒯_𝒫} max_{τ' ∈ ℐ_τ, dim(τ') ≥ 1} (1 - H_q(τ') / dim(τ'))`.
-/
noncomputable def mrrswRate (F : Type*) [Field F] [Fintype F] {n : ℕ} (hn : 0 < n) (b : ℕ)
    (P : Submodule F (Fin n → F) → Prop) : ℝ :=
  sInf {r : ℝ | ∃ (a : ℕ) (_ : 1 ≤ a) (_ : a ≤ b) (τ : PMF (Fin a → F)),
    IsMinimalType hn P τ ∧
    r = sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
      IsImpliedDist τ τ' ∧ s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}}

theorem mrrswRate_eq_sInf (F : Type*) [Field F] [Fintype F] {n : ℕ} (hn : 0 < n) (b : ℕ)
    (P : Submodule F (Fin n → F) → Prop) :
    mrrswRate F hn b P =
      sInf {r : ℝ | ∃ (a : ℕ) (_ : 1 ≤ a) (_ : a ≤ b) (τ : PMF (Fin a → F)),
        IsMinimalType hn P τ ∧
        r = sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
          IsImpliedDist τ τ' ∧
            s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}} := by rfl

end RLC

section MRRSW

variable {F : Type*} [Field F] [Fintype F]

private lemma innerRateSet_bddAbove_and_nonempty {n a : ℕ} (hn : 0 < n) (ha : 1 ≤ a)
    {τ : PMF (Fin a → F)} (_hfe : IsFeasibleType n hn τ) (hfull : IsFullRankDist τ) :
    let S := {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
      IsImpliedDist τ τ' ∧ s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}
    BddAbove S ∧ S.Nonempty ∧ S.Finite ∧ 0 ≤ sSup S ∧ sSup S ≤ 1 := by
  intro S
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hbdd : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro s ⟨_, _, τ', _, rfl⟩
    linarith [div_nonneg (pmfEntropyBase_nonneg hq τ') (Nat.cast_nonneg (distDim τ'))]
  have hself_mem : (1 - pmfEntropyBase (Fintype.card F) τ / (distDim τ : ℝ)) ∈ S := by
    refine ⟨a, ha, τ, ⟨1, ?_, by simp only [Matrix.vecMul_one]; exact PMF.map_id τ⟩, rfl⟩
    rw [hasFullColRank_iff_mulVec_injective]; intro u v huv; simpa using huv
  have hne : S.Nonempty := ⟨_, hself_mem⟩
  have hfin : S.Finite := by
    let T : Finset (Σ a' : Fin (a + 1), Matrix (Fin a) (Fin a'.val) F) := Finset.univ
    let g : (Σ a' : Fin (a + 1), Matrix (Fin a) (Fin a'.val) F) → ℝ := fun ⟨a', D⟩ ↦
      let τ' := τ.map (fun x ↦ Matrix.vecMul x D)
      1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)
    refine (T.image g).finite_toSet.subset ?_
    rintro s ⟨a', _, τ', ⟨D, hD, hmap⟩, rfl⟩
    have ha'_le : a' ≤ a := by
      rw [hasFullColRank_iff_linearIndependent] at hD
      have := LinearIndependent.fintype_card_le_finrank hD
      simpa [Module.finrank_pi, Fintype.card_fin] using this
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨⟨⟨a', Nat.lt_succ_of_le ha'_le⟩, D⟩, Finset.mem_univ _, by simp [g, hmap]⟩)
  have hge0 : 0 ≤ sSup S := by
    have hle : pmfEntropyBase (Fintype.card F) τ ≤ (a : ℝ) := by
      have h := pmfEntropyBase_le_logb_card (α := Fin a → F) hq τ
      have hlog : Real.logb (Fintype.card F) (Fintype.card (Fin a → F)) = (a : ℝ) := by
        simp [Fintype.card_pi, Real.logb_pow, Real.logb_self_eq_one hq]
      rwa [hlog] at h
    have h0 : 0 ≤ 1 - pmfEntropyBase (Fintype.card F) τ / (distDim τ : ℝ) := by
      rw [(isFullRankDist_iff τ).mp hfull]
      have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
      rw [sub_nonneg, div_le_one haR]
      exact hle
    exact h0.trans (le_csSup hbdd hself_mem)
  have hle1 : sSup S ≤ 1 := csSup_le hne fun s hs ↦ by
    rcases hs with ⟨_, _, τ', _, rfl⟩
    linarith [div_nonneg (pmfEntropyBase_nonneg hq τ') (Nat.cast_nonneg (distDim τ'))]
  exact ⟨hbdd, hne, hfin, hge0, hle1⟩

theorem mrrswRate_nonneg {n b : ℕ} (hn : 0 < n) {P : Submodule F (Fin n → F) → Prop} :
    0 ≤ mrrswRate F hn b P := by
  unfold mrrswRate
  by_cases hne :
      {r : ℝ | ∃ (a : ℕ) (_ : 1 ≤ a) (_ : a ≤ b) (τ : PMF (Fin a → F)),
        IsMinimalType hn P τ ∧
        r = sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
          IsImpliedDist τ τ' ∧
            s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}}.Nonempty
  · refine le_csInf hne ?_
    rintro r ⟨a, ha, _, τ, ⟨A, hAmin, hAeq⟩, rfl⟩
    have hfull : IsFullRankDist τ := hAeq ▸ (isFullRankDist_empDist_iff hn A).mpr hAmin.1
    exact (innerRateSet_bddAbove_and_nonempty hn ha
      (isFeasibleType_iff.mpr ⟨A, hAeq⟩) hfull).2.2.2.1
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

theorem mrrswRate_le_one {n b : ℕ} (hn : 0 < n) {P : Submodule F (Fin n → F) → Prop}
    (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P) (hbot : ¬ P ⊥) (htop : P ⊤) :
    mrrswRate F hn b P ≤ 1 := by
  obtain ⟨a, hab, A, hAmin, _⟩ := exists_isMinimalMatrix_of_sat hmono hloc htop
  have ha : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    have hcol : colSpan A = ⊥ := by
      subst ha0
      exact colSpan_fin_zero A
    exact hbot (hcol ▸ hAmin.2.1)
  let τ := empDist hn A
  have hfull : IsFullRankDist τ := (isFullRankDist_empDist_iff hn A).mpr hAmin.1
  have hle1 := (innerRateSet_bddAbove_and_nonempty hn ha (isFeasibleType_iff.mpr ⟨A, rfl⟩)
    hfull).2.2.2.2
  have hbddL : BddBelow {r : ℝ | ∃ (a : ℕ) (_ : 1 ≤ a) (_ : a ≤ b) (τ : PMF (Fin a → F)),
      IsMinimalType hn P τ ∧
      r = sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
        IsImpliedDist τ τ' ∧
          s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}} := by
    refine ⟨0, ?_⟩
    rintro r ⟨a₁, ha₁, _, τ₁, ⟨A₁, hA₁, hA₁eq⟩, rfl⟩
    exact (innerRateSet_bddAbove_and_nonempty hn ha₁ (isFeasibleType_iff.mpr ⟨A₁, hA₁eq⟩)
      (hA₁eq ▸ (isFullRankDist_empDist_iff hn A₁).mpr hA₁.1)).2.2.2.1
  exact (csInf_le hbddL ⟨a, ha, hab, τ, ⟨A, hAmin, rfl⟩, rfl⟩).trans hle1


theorem mem_minimalTypesFinset_of_isMinimalMatrix {n b a : ℕ} (hn : 0 < n) (hab : a ≤ b)
    {P : Submodule F (Fin n → F) → Prop} {A : Matrix (Fin n) (Fin a) F}
    (hmin : IsMinimalMatrix P A) :
    (⟨⟨a, Nat.lt_succ_of_le hab⟩, empDist hn A⟩ : Σ i : Fin (b + 1), PMF (Fin i.val → F)) ∈
      minimalTypesFinset hn b P := by
  classical
  simp only [minimalTypesFinset, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter]
  exact ⟨mem_feasibleTypesFinset.mpr (isFeasibleType_iff.mpr ⟨A, rfl⟩), A, hmin, rfl⟩

theorem isMinimalMatrix_of_mem_minimalTypes {n b : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} (hrow : IsRowSymmetric P)
    {p : Σ a : Fin (b + 1), PMF (Fin a.val → F)} (hp : p ∈ minimalTypesFinset hn b P)
    {A : Matrix (Fin n) (Fin p.1.val) F} (hA : A ∈ typeClassFinset n hn p.2) :
    IsMinimalMatrix P A := by
  classical
  simp only [minimalTypesFinset, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter] at hp
  obtain ⟨A₀, hA₀_min, hA₀_eq⟩ := hp.2
  exact isMinimalMatrix_of_empDist_eq hn hrow hA₀_min
    (hA₀_eq.trans (mem_typeClassFinset.mp hA).symm)

theorem isFeasibleType_of_mem_minimalTypes {n b : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} {p : Σ a : Fin (b + 1), PMF (Fin a.val → F)}
    (hp : p ∈ minimalTypesFinset hn b P) : IsFeasibleType n hn p.2 := by
  classical
  simp only [minimalTypesFinset, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter] at hp
  exact mem_feasibleTypesFinset.mp hp.1

theorem isFullRankDist_of_mem_minimalTypes {n b : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} {p : Σ a : Fin (b + 1), PMF (Fin a.val → F)}
    (hp : p ∈ minimalTypesFinset hn b P) : IsFullRankDist p.2 := by
  classical
  simp only [minimalTypesFinset, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter] at hp
  obtain ⟨A₀, hA₀_min, hA₀_eq⟩ := hp.2
  exact hA₀_eq ▸ (isFullRankDist_empDist_iff hn A₀).mpr hA₀_min.1

theorem le_mrrswRate_of_forall_minimalType {n b : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} (hmono : IsMonotoneIncreasing P) (hloc : IsBLocal b P)
    (hbot : ¬ P ⊥) (htop : P ⊤) {r : ℝ}
    (h : ∀ (a : ℕ), 1 ≤ a → a ≤ b → ∀ (τ : PMF (Fin a → F)),
      IsMinimalType hn P τ →
      ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
        IsImpliedDist τ τ' ∧
        r ≤ 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)) :
    r ≤ mrrswRate F hn b P := by
  unfold mrrswRate
  obtain ⟨a₀, ha₀b, A₀, hA₀min, _⟩ := exists_isMinimalMatrix_of_sat hmono hloc htop
  have ha₀1 : 1 ≤ a₀ := by
    by_contra h0
    have hz : a₀ = 0 := by omega
    have hcol : colSpan A₀ = ⊥ := by
      subst hz
      exact colSpan_fin_zero A₀
    exact hbot (hcol ▸ hA₀min.2.1)
  have hne : {v : ℝ | ∃ (a : ℕ) (_ : 1 ≤ a) (_ : a ≤ b) (τ : PMF (Fin a → F)),
      IsMinimalType hn P τ ∧
      v = sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
        IsImpliedDist τ τ' ∧
          s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}}.Nonempty :=
    ⟨_, a₀, ha₀1, ha₀b, empDist hn A₀, ⟨A₀, hA₀min, rfl⟩, rfl⟩
  refine le_csInf hne ?_
  rintro v ⟨a, ha1, hab, τ, hτmin, rfl⟩
  obtain ⟨a', ha'1, τ', himp, hrle⟩ := h a ha1 hab τ hτmin
  obtain ⟨A, hAmin, hAeq⟩ := hτmin
  have hfull : IsFullRankDist τ := hAeq ▸ (isFullRankDist_empDist_iff hn A).mpr hAmin.1
  have hbdd := (innerRateSet_bddAbove_and_nonempty hn ha1 (isFeasibleType_iff.mpr ⟨A, hAeq⟩)
    hfull).1
  exact hrle.trans (le_csSup hbdd ⟨a', ha'1, τ', himp, rfl⟩)

theorem exists_implied_of_mem_minimalTypes {n b : ℕ} (hn : 0 < n)
    {P : Submodule F (Fin n → F) → Prop} (hbot : ¬ P ⊥)
    {p : Σ a : Fin (b + 1), PMF (Fin a.val → F)} (hp : p ∈ minimalTypesFinset hn b P) :
    ∃ (a' : ℕ), 1 ≤ a' ∧ a' ≤ p.1.val ∧ ∃ τ' : PMF (Fin a' → F),
      IsImpliedDist p.2 τ' ∧
      IsFeasibleType n hn τ' ∧
      IsFullRankDist τ' ∧
      mrrswRate F hn b P ≤ 1 - pmfEntropyBase (Fintype.card F) τ' / (a' : ℝ) := by
  classical
  simp only [minimalTypesFinset, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter] at hp
  obtain ⟨A₀, hA₀min, hA₀eq⟩ := hp.2
  have ha1 : 1 ≤ p.1.val := by
    by_contra h0
    have hz : p.1.val = 0 := by omega
    have hcol : colSpan A₀ = ⊥ := by
      rw [colSpan_eq_span_range]
      have : Set.range (fun j : Fin p.1.val ↦ fun i : Fin n ↦ A₀ i j) = ∅ := by ext v; simp [hz]
      rw [this, Submodule.span_empty]
    exact hbot (hcol ▸ hA₀min.2.1)
  have hab : p.1.val ≤ b := Nat.le_of_lt_succ p.1.isLt
  have hfull : IsFullRankDist p.2 := hA₀eq ▸ (isFullRankDist_empDist_iff hn A₀).mpr hA₀min.1
  have hfe : IsFeasibleType n hn p.2 := isFeasibleType_iff.mpr ⟨A₀, hA₀eq⟩
  obtain ⟨_, hne, hfin, _, _⟩ := innerRateSet_bddAbove_and_nonempty hn ha1 hfe hfull
  obtain ⟨s, hs_mem_f, hs_eq⟩ := Finset.exists_max_image hfin.toFinset id
    (hfin.toFinset_nonempty.mpr hne)
  have hs_mem := hfin.mem_toFinset.mp hs_mem_f
  have hsSup : sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
      IsImpliedDist p.2 τ' ∧
      s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)} = s :=
    le_antisymm (csSup_le hne fun x hx ↦ hs_eq x (hfin.mem_toFinset.mpr hx))
      (le_csSup hfin.bddAbove hs_mem)
  rcases hs_mem with ⟨a', ha'1, τ', himp, rfl⟩
  have hfe' : IsFeasibleType n hn τ' := isFeasibleType_of_isImpliedDist hn hfe himp
  have hfull' : IsFullRankDist τ' := isFullRankDist_of_isImpliedDist hn hfe hfull himp
  have ha'_le : a' ≤ p.1.val := by
    obtain ⟨D, hD, _⟩ := himp
    rw [hasFullColRank_iff_linearIndependent] at hD
    have := LinearIndependent.fintype_card_le_finrank hD
    simpa [Module.finrank_pi, Fintype.card_fin] using this
  have hbddL : BddBelow {r : ℝ | ∃ (a : ℕ) (_ : 1 ≤ a) (_ : a ≤ b) (τ : PMF (Fin a → F)),
      IsMinimalType hn P τ ∧
      r = sSup {s : ℝ | ∃ (a' : ℕ) (_ : 1 ≤ a') (τ' : PMF (Fin a' → F)),
        IsImpliedDist τ τ' ∧ s = 1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ)}} := by
    refine ⟨0, ?_⟩
    rintro r ⟨a₁, ha₁, _, τ₁, ⟨A₁, hA₁, hA₁eq⟩, rfl⟩
    exact (innerRateSet_bddAbove_and_nonempty hn ha₁ (isFeasibleType_iff.mpr ⟨A₁, hA₁eq⟩)
      (hA₁eq ▸ (isFullRankDist_empDist_iff hn A₁).mpr hA₁.1)).2.2.2.1
  have hm_le : mrrswRate F hn b P ≤
      1 - pmfEntropyBase (Fintype.card F) τ' / (distDim τ' : ℝ) := by
    rw [← hsSup]
    exact csInf_le hbddL ⟨p.1.val, ha1, hab, p.2, ⟨A₀, hA₀min, hA₀eq⟩, rfl⟩
  have hdim_eq : distDim τ' = a' := (isFullRankDist_iff τ').mp hfull'
  rw [hdim_eq] at hm_le
  exact ⟨a', ha'1, ha'_le, τ', himp, hfe', hfull', hm_le⟩

end MRRSW

end CslibFrontier.Foundations.Data.Code
