module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.ModEq

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Sort
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

/-!
# Skew-Symmetric Matrices, Pfaffians, and Pfaffian Sums

Combinatorial theory of alternating (skew-symmetric zero-diagonal) matrices, perfect matchings,
Pfaffians, principal-submatrix Pfaffians, and Pfaffian sums over arbitrary commutative rings.

## Main definitions

* `CslibFrontier.Foundations.LinearAlgebra.IsAlternating`: alternating (skew-symmetric with zero
  diagonal) matrices over a ring.
* `CslibFrontier.Foundations.LinearAlgebra.ofUpperTri`: alternating matrix determined by its
  strictly upper-triangular entries.
* `CslibFrontier.Foundations.LinearAlgebra.PerfectMatching`: fixed-point-free involutions on a
  finite type, with crossing/overlap count, sign, and matching weight.
* `CslibFrontier.Foundations.LinearAlgebra.pfaffian`: Pfaffian of a matrix on a finite linearly
  ordered index type, defined as the overlap-signed sum over perfect matchings.
* `CslibFrontier.Foundations.LinearAlgebra.pfaffianSubmatrix`: Pfaffian of the principal submatrix
  indexed by a finite subset.
* `CslibFrontier.Foundations.LinearAlgebra.pfaffianSum` and
  `CslibFrontier.Foundations.LinearAlgebra.pfaffianSumSet`: Pfaffian sum weighted by vertex
  indeterminates and over a subset of omittable vertices.

## Main results

* `CslibFrontier.Foundations.LinearAlgebra.pfaffian_eq_zero_of_odd`: the Pfaffian vanishes on
  odd-cardinality domains.
* `CslibFrontier.Foundations.LinearAlgebra.pfaffian_orderIso`: invariance of the Pfaffian under
  order isomorphisms.
* `CslibFrontier.Foundations.LinearAlgebra.pfaffianSubmatrix_eq_sum_min`: Laplace expansion of a
  principal-submatrix Pfaffian along the minimum vertex.
* `CslibFrontier.Foundations.LinearAlgebra.pfaffianSubmatrix_allOnesAlt`: the Pfaffian of the
  all-ones strictly upper-triangular alternating matrix equals `1` on even subsets and `0` on odd
  subsets.
-/

public section

namespace CslibFrontier.Foundations.LinearAlgebra

/-! ### Alternating matrices -/

/-- A square matrix `M` over a ring `R` is alternating (skew-symmetric with zero diagonal) if
`M i i = 0` and `M j i = -M i j` for all indices `i, j`. -/
def IsAlternating {ι R : Type*} [Ring R] (M : Matrix ι ι R) : Prop :=
  (∀ i, M i i = 0) ∧ ∀ i j, M j i = -M i j

namespace IsAlternating

variable {ι κ R : Type*} [Ring R]

/-- The diagonal entries of an alternating matrix are zero. -/
theorem diag {M : Matrix ι ι R} (hM : IsAlternating M) (i : ι) : M i i = 0 :=
  hM.1 i

/-- Swapping indices negates an entry of an alternating matrix. -/
theorem skew {M : Matrix ι ι R} (hM : IsAlternating M) (i j : ι) : M j i = -M i j :=
  hM.2 i j

/-- Any principal submatrix of an alternating matrix is alternating. -/
theorem submatrix {M : Matrix ι ι R} (hM : IsAlternating M) (f : κ → ι) :
    IsAlternating (M.submatrix f f) :=
  ⟨fun i ↦ hM.1 (f i), fun i j ↦ hM.2 (f i) (f j)⟩

/-- The zero matrix is alternating. -/
theorem zero : IsAlternating (0 : Matrix ι ι R) :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ by simp⟩

/-- The negation of an alternating matrix is alternating. -/
theorem neg {M : Matrix ι ι R} (hM : IsAlternating M) : IsAlternating (-M) :=
  ⟨fun i ↦ by simp [hM.1 i], fun i j ↦ by simp [hM.2 i j]⟩

/-- The sum of two alternating matrices is alternating. -/
theorem add {M N : Matrix ι ι R} (hM : IsAlternating M) (hN : IsAlternating N) :
    IsAlternating (M + N) :=
  ⟨fun i ↦ by simp [hM.1 i, hN.1 i], fun i j ↦ by simp [hM.2 i j, hN.2 i j, add_comm]⟩

end IsAlternating

/-- Construct an alternating matrix on a linearly ordered index type from its strictly
upper-triangular edge weights `w i j` (for `i < j`). -/
def ofUpperTri {ι R : Type*} [LinearOrder ι] [Ring R] (w : ι → ι → R) : Matrix ι ι R :=
  Matrix.of fun i j ↦ if i < j then w i j else if j < i then -w j i else 0

/-- `ofUpperTri w` is always alternating. -/
theorem isAlternating_ofUpperTri {ι R : Type*} [LinearOrder ι] [Ring R] (w : ι → ι → R) :
    IsAlternating (ofUpperTri w) := by
  refine ⟨fun i ↦ by simp [ofUpperTri], fun i j ↦ ?_⟩
  simp only [ofUpperTri, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_right h.not_gt, ite_eq_left h, ite_eq_left h]
  · simp
  · rw [ite_eq_left h, ite_eq_right h.not_gt, ite_eq_left h, neg_neg]

/-- Upper-triangular entry of `ofUpperTri w`. -/
@[simp]
theorem ofUpperTri_apply_of_lt {ι R : Type*} [LinearOrder ι] [Ring R] (w : ι → ι → R)
    {i j : ι} (h : i < j) : ofUpperTri w i j = w i j := by
  simp [ofUpperTri, h]

/-- Lower-triangular entry of `ofUpperTri w`. -/
@[simp]
theorem ofUpperTri_apply_of_gt {ι R : Type*} [LinearOrder ι] [Ring R] (w : ι → ι → R)
    {i j : ι} (h : j < i) : ofUpperTri w i j = -w j i := by
  simp [ofUpperTri, h, h.not_gt]

/-- Diagonal entry of `ofUpperTri w`. -/
@[simp]
theorem ofUpperTri_apply_diag {ι R : Type*} [LinearOrder ι] [Ring R] (w : ι → ι → R) (i : ι) :
    ofUpperTri w i i = 0 := by
  simp [ofUpperTri]

/-- The all-`1` strictly upper-triangular alternating matrix on a linearly ordered type. -/
def allOnesAlt (ι R : Type*) [LinearOrder ι] [Ring R] : Matrix ι ι R :=
  ofUpperTri (fun _ _ ↦ (1 : R))

/-- Upper-triangular entry of `allOnesAlt`. -/
theorem allOnesAlt_apply_of_lt (ι R : Type*) [LinearOrder ι] [Ring R] {i j : ι} (h : i < j) :
    allOnesAlt ι R i j = 1 :=
  ofUpperTri_apply_of_lt _ h

/-- `allOnesAlt` is alternating. -/
theorem isAlternating_allOnesAlt (ι R : Type*) [LinearOrder ι] [Ring R] :
    IsAlternating (allOnesAlt ι R) :=
  isAlternating_ofUpperTri _

/-! ### Perfect matchings and Pfaffians -/

/-- A perfect matching of a type `α` is a fixed-point-free involution of `α`. -/
@[ext]
structure PerfectMatching (α : Type*) where
  /-- Underlying permutation pairing each vertex with its matched partner. -/
  toPerm : Equiv.Perm α
  /-- Pairing is symmetric (involutive). -/
  involutive : ∀ x, toPerm (toPerm x) = x
  /-- No vertex is matched to itself. -/
  ne_self : ∀ x, toPerm x ≠ x

namespace PerfectMatching

variable {α β : Type*}

/-- Equivalence between `PerfectMatching α` and the subtype of fixed-point-free involutions. -/
def equivSubtype (α : Type*) :
    PerfectMatching α ≃ { f : Equiv.Perm α // (∀ x, f (f x) = x) ∧ ∀ x, f x ≠ x } where
  toFun m := ⟨m.toPerm, m.involutive, m.ne_self⟩
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instDecidableEq [DecidableEq α] [Fintype α] : DecidableEq (PerfectMatching α) :=
  fun a b ↦ decidable_of_iff (a.toPerm = b.toPerm) ⟨fun h ↦ PerfectMatching.ext h, congrArg toPerm⟩

instance instFinite [Finite α] : Finite (PerfectMatching α) :=
  Finite.of_equiv _ (equivSubtype α).symm

noncomputable instance instFintype [Finite α] : Fintype (PerfectMatching α) :=
  Fintype.ofFinite (PerfectMatching α)

/-- The empty type has a unique perfect matching. -/
instance instUniqueOfIsEmpty [IsEmpty α] : Unique (PerfectMatching α) where
  default := ⟨1, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  uniq _ := PerfectMatching.ext (Equiv.ext fun x ↦ isEmptyElim x)

/-- Apply a perfect matching twice to recover the original vertex. -/
@[simp]
theorem apply_apply (m : PerfectMatching α) (x : α) : m.toPerm (m.toPerm x) = x :=
  m.involutive x

/-- A perfect matching has no fixed points. -/
@[simp]
theorem apply_ne (m : PerfectMatching α) (x : α) : m.toPerm x ≠ x :=
  m.ne_self x

/-- Symmetry of being matched partners. -/
theorem apply_eq_iff (m : PerfectMatching α) {x y : α} : m.toPerm x = y ↔ m.toPerm y = x :=
  ⟨fun h ↦ by rw [← h, m.apply_apply], fun h ↦ by rw [← h, m.apply_apply]⟩

/-- Transport a perfect matching along an equivalence. -/
def congr (e : α ≃ β) (m : PerfectMatching α) : PerfectMatching β where
  toPerm := e.permCongr m.toPerm
  involutive y := by simp [Equiv.permCongr_apply]
  ne_self y h := by
    simp only [Equiv.permCongr_apply] at h
    exact m.ne_self (e.symm y) (e.injective (by simpa using h))

/-- Transporting along an equivalence is an equivalence on perfect matchings. -/
def congrEquiv (e : α ≃ β) : PerfectMatching α ≃ PerfectMatching β where
  toFun := congr e
  invFun := congr e.symm
  left_inv m := by ext x; simp [congr, Equiv.permCongr_apply]
  right_inv m := by ext y; simp [congr, Equiv.permCongr_apply]

/-- For a linearly ordered finite type `α`, the lower endpoints `x < m x` of all matched edges. -/
def lowerVerts [Fintype α] [LinearOrder α] (m : PerfectMatching α) : Finset α :=
  Finset.univ.filter fun x ↦ x < m.toPerm x

/-- Every vertex is either a lower endpoint or matched to a lower endpoint. -/
theorem mem_lowerVerts_iff [Fintype α] [LinearOrder α] (m : PerfectMatching α) (x : α) :
    x ∈ m.lowerVerts ↔ x < m.toPerm x := by
  simp [lowerVerts]

/-- Mapping lower endpoints to their partners gives the complement of `lowerVerts`. -/
theorem image_toPerm_lowerVerts [Fintype α] [LinearOrder α] (m : PerfectMatching α) :
    m.lowerVerts.image m.toPerm = m.lowerVertsᶜ := by
  ext y
  simp only [Finset.mem_image, Finset.mem_compl, mem_lowerVerts_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [m.apply_apply]
    exact not_lt.mpr hx.le
  · intro hy
    refine ⟨m.toPerm y, ?_, m.apply_apply y⟩
    rw [m.apply_apply]
    exact lt_of_le_of_ne (not_lt.mp hy) (m.ne_self y)

/-- A finite type with a perfect matching has even cardinality equal to `2 * m.lowerVerts.card`. -/
theorem card_eq_two_mul_card_lowerVerts [Fintype α] [LinearOrder α] (m : PerfectMatching α) :
    Fintype.card α = 2 * m.lowerVerts.card := by
  have h1 : (m.lowerVerts.image m.toPerm).card = m.lowerVerts.card :=
    Finset.card_image_of_injective _ m.toPerm.injective
  have h2 : m.lowerVerts.card + m.lowerVertsᶜ.card = Fintype.card α :=
    Finset.card_add_card_compl m.lowerVerts
  rw [← image_toPerm_lowerVerts, h1] at h2
  omega

/-- A finite type admitting a perfect matching has even cardinality. -/
theorem even_card [Fintype α] (m : PerfectMatching α) : Even (Fintype.card α) := by
  classical
  let e := Fintype.equivFin α
  have h := (m.congr e).card_eq_two_mul_card_lowerVerts
  rw [Fintype.card_fin] at h
  exact ⟨(m.congr e).lowerVerts.card, by omega⟩

/-- Number of overlapping edge pairs `((a, m a), (b, m b))` with `a < b < m a < m b`. -/
def overlapCount [Fintype α] [LinearOrder α] (m : PerfectMatching α) : ℕ :=
  ((m.lowerVerts ×ˢ m.lowerVerts).filter
    fun p ↦ p.1 < p.2 ∧ p.2 < m.toPerm p.1 ∧ m.toPerm p.1 < m.toPerm p.2).card

/-- The sign `(-1)^(overlapCount m)` of a perfect matching in a commutative ring `R`. -/
def sign (R : Type*) [CommRing R] [Fintype α] [LinearOrder α] (m : PerfectMatching α) : R :=
  (-1 : R) ^ m.overlapCount

/-- The product of upper-triangular edge weights `∏_{x < m x} M x (m x)` of a perfect matching. -/
def weight {R : Type*} [CommRing R] [Fintype α] [LinearOrder α]
    (M : Matrix α α R) (m : PerfectMatching α) : R :=
  ∏ x ∈ m.lowerVerts, M x (m.toPerm x)

/-- Equation lemma for `overlapCount`. -/
theorem overlapCount_eq_card [Fintype α] [LinearOrder α] (m : PerfectMatching α) :
    m.overlapCount =
      ((m.lowerVerts ×ˢ m.lowerVerts).filter
        fun p ↦ p.1 < p.2 ∧ p.2 < m.toPerm p.1 ∧ m.toPerm p.1 < m.toPerm p.2).card := by
  rfl

/-- Equation lemma for `sign`. -/
theorem sign_eq_neg_one_pow (R : Type*) [CommRing R] [Fintype α] [LinearOrder α]
    (m : PerfectMatching α) : m.sign R = (-1 : R) ^ m.overlapCount := by
  rfl

/-- Equation lemma for `weight`. -/
theorem weight_eq_prod {R : Type*} [CommRing R] [Fintype α] [LinearOrder α]
    (M : Matrix α α R) (m : PerfectMatching α) :
    m.weight M = ∏ x ∈ m.lowerVerts, M x (m.toPerm x) := by
  rfl

end PerfectMatching

/-- The Pfaffian of a matrix `M` indexed by a finite linearly ordered type `α`, defined as the
overlap-signed sum of edge-weight products over all perfect matchings of `α`. -/
noncomputable def pfaffian {α R : Type*} [Fintype α] [LinearOrder α] [CommRing R]
    (M : Matrix α α R) : R :=
  ∑ m : PerfectMatching α, m.sign R * m.weight M

/-- Equation lemma for `pfaffian`. -/
theorem pfaffian_eq_sum {α R : Type*} [Fintype α] [LinearOrder α] [CommRing R]
    (M : Matrix α α R) : pfaffian M = ∑ m : PerfectMatching α, m.sign R * m.weight M := by
  rfl

/-- The Pfaffian of the principal submatrix of `M` indexed by a finite subset `U : Finset α`. -/
noncomputable def pfaffianSubmatrix {α R : Type*} [LinearOrder α] [CommRing R]
    (M : Matrix α α R) (U : Finset α) : R :=
  pfaffian (M.submatrix (Subtype.val : U → α) Subtype.val)

/-- Equation lemma for `pfaffianSubmatrix`. -/
theorem pfaffianSubmatrix_eq_sum {α R : Type*} [LinearOrder α] [CommRing R]
    (M : Matrix α α R) (U : Finset α) :
    pfaffianSubmatrix M U =
      ∑ m : PerfectMatching U,
        m.sign R * m.weight (M.submatrix (Subtype.val : U → α) Subtype.val) := by
  rfl

/-- Valiant's Pfaffian Sum `PfS(M, λ) = ∑_A (∏_{i ∈ A} λ i) Pf(M[A])`, where `M[A]` deletes
rows and columns in `A`. -/
noncomputable def pfaffianSum {α R : Type*} [Fintype α] [LinearOrder α] [CommRing R]
    (M : Matrix α α R) (lam : α → R) : R :=
  ∑ A : Finset α, (∏ i ∈ A, lam i) * pfaffianSubmatrix M Aᶜ

/-- The Pfaffian Sum for a set `T` of omittable vertices (`λ_i = 1` if `i ∈ T`, else `0`). -/
noncomputable def pfaffianSumSet {α R : Type*} [Fintype α] [LinearOrder α] [CommRing R]
    (M : Matrix α α R) (T : Finset α) : R :=
  ∑ A ∈ T.powerset, pfaffianSubmatrix M Aᶜ

/-- Equation lemma for `pfaffianSumSet`. -/
theorem pfaffianSumSet_eq_sum {α R : Type*} [Fintype α] [LinearOrder α] [CommRing R]
    (M : Matrix α α R) (T : Finset α) :
    pfaffianSumSet M T = ∑ A ∈ T.powerset, pfaffianSubmatrix M Aᶜ := by
  rfl

/-- Specializing `pfaffianSum` to the `{0, 1}`-indicator of `T` equals `pfaffianSumSet M T`. -/
theorem pfaffianSum_indicator_eq_pfaffianSumSet {α R : Type*} [Fintype α] [LinearOrder α]
    [CommRing R] (M : Matrix α α R) (T : Finset α) :
    pfaffianSum M (fun i ↦ if i ∈ T then (1 : R) else 0) = pfaffianSumSet M T := by
  unfold pfaffianSum pfaffianSumSet
  rw [← Finset.sum_subset (Finset.subset_univ T.powerset)]
  · refine Finset.sum_congr rfl fun A hA ↦ ?_
    have hsub : A ⊆ T := Finset.mem_powerset.mp hA
    have hprod : ∏ i ∈ A, (if i ∈ T then (1 : R) else 0) = 1 :=
      Finset.prod_eq_one fun i hi ↦ ite_eq_left (hsub hi)
    rw [hprod, one_mul]
  · intro A _ hA
    rw [Finset.mem_powerset] at hA
    have ⟨i, hiA, hiT⟩ := Finset.not_subset.mp hA
    have hprod : ∏ j ∈ A, (if j ∈ T then (1 : R) else 0) = 0 :=
      Finset.prod_eq_zero hiA (ite_eq_right hiT)
    rw [hprod, zero_mul]

/-- The Pfaffian of a matrix on an empty index type is `1`. -/
theorem pfaffian_of_isEmpty {α R : Type*} [Fintype α] [LinearOrder α] [IsEmpty α] [CommRing R]
    (M : Matrix α α R) : pfaffian M = 1 := by
  unfold pfaffian
  rw [Fintype.sum_unique]
  have hlv : (default : PerfectMatching α).lowerVerts = ∅ := by
    ext x; exact isEmptyElim x
  simp [PerfectMatching.sign, PerfectMatching.weight, PerfectMatching.overlapCount, hlv]

/-- The Pfaffian of the empty principal submatrix is `1`. -/
@[simp]
theorem pfaffianSubmatrix_empty {α R : Type*} [LinearOrder α] [CommRing R] (M : Matrix α α R) :
    pfaffianSubmatrix M ∅ = 1 :=
  pfaffian_of_isEmpty _

/-- The Pfaffian vanishes on any finite type of odd cardinality. -/
theorem pfaffian_eq_zero_of_odd {α R : Type*} [Fintype α] [LinearOrder α] [CommRing R]
    (hodd : Odd (Fintype.card α)) (M : Matrix α α R) : pfaffian M = 0 := by
  unfold pfaffian
  apply Finset.sum_eq_zero
  intro m _
  exact absurd m.even_card (Nat.not_even_iff_odd.mpr hodd)

/-- The Pfaffian of an odd-cardinality principal submatrix is `0`. -/
theorem pfaffianSubmatrix_eq_zero_of_odd {α R : Type*} [LinearOrder α] [CommRing R]
    {U : Finset α} (hodd : Odd U.card) (M : Matrix α α R) : pfaffianSubmatrix M U = 0 := by
  unfold pfaffianSubmatrix
  apply pfaffian_eq_zero_of_odd
  simpa using hodd

/-- Transporting `lowerVerts` along an order isomorphism. -/
theorem PerfectMatching.lowerVerts_congr {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃o β) (m : PerfectMatching α) :
    (m.congr e.toEquiv).lowerVerts = m.lowerVerts.map e.toEmbedding := by
  ext y
  simp only [PerfectMatching.mem_lowerVerts_iff, Finset.mem_map, RelIso.coe_toEmbedding]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have : e (e.symm y) < e (m.toPerm (e.symm y)) := by
      simpa [PerfectMatching.congr, Equiv.permCongr_apply] using hy
    exact e.lt_iff_lt.mp this
  · rintro ⟨x, hx, rfl⟩
    simpa [PerfectMatching.congr, Equiv.permCongr_apply] using e.lt_iff_lt.mpr hx

/-- Transporting `overlapCount` along an order isomorphism preserves it. -/
theorem PerfectMatching.overlapCount_congr {α β : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] (e : α ≃o β) (m : PerfectMatching α) :
    (m.congr e.toEquiv).overlapCount = m.overlapCount := by
  unfold PerfectMatching.overlapCount
  rw [m.lowerVerts_congr e]
  refine Finset.card_bij (fun p _ ↦ (e.symm p.1, e.symm p.2)) ?_ ?_ ?_
  · rintro ⟨y₁, y₂⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
      RelIso.coe_toEmbedding] at hp ⊢
    rcases hp with ⟨⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, rfl⟩⟩, h1, h2, h3⟩
    have he₁ : (m.congr e.toEquiv).toPerm (e x₁) = e (m.toPerm x₁) := by
      simp [PerfectMatching.congr, Equiv.permCongr_apply]
    have he₂ : (m.congr e.toEquiv).toPerm (e x₂) = e (m.toPerm x₂) := by
      simp [PerfectMatching.congr, Equiv.permCongr_apply]
    rw [he₁] at h2 h3
    rw [he₂] at h3
    simp only [OrderIso.symm_apply_apply]
    exact ⟨⟨hx₁, hx₂⟩, e.lt_iff_lt.mp h1, e.lt_iff_lt.mp h2, e.lt_iff_lt.mp h3⟩
  · rintro ⟨y₁, y₂⟩ _ ⟨z₁, z₂⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (e.symm.injective h.1) (e.symm.injective h.2)
  · rintro ⟨x₁, x₂⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product] at hx
    refine ⟨(e x₁, e x₂), ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_map.mpr ⟨x₁, hx.1.1, rfl⟩, Finset.mem_map.mpr ⟨x₂, hx.1.2, rfl⟩⟩, ?_⟩
    have he₁ : (m.congr e.toEquiv).toPerm (e x₁) = e (m.toPerm x₁) := by
      simp [PerfectMatching.congr, Equiv.permCongr_apply]
    have he₂ : (m.congr e.toEquiv).toPerm (e x₂) = e (m.toPerm x₂) := by
      simp [PerfectMatching.congr, Equiv.permCongr_apply]
    rw [he₁, he₂]
    exact ⟨e.lt_iff_lt.mpr hx.2.1, e.lt_iff_lt.mpr hx.2.2.1, e.lt_iff_lt.mpr hx.2.2.2⟩

/-- Transporting `weight` along an order isomorphism pulls back `M`. -/
theorem PerfectMatching.weight_congr {α β R : Type*} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] [CommRing R] (e : α ≃o β) (M : Matrix β β R)
    (m : PerfectMatching α) :
    (m.congr e.toEquiv).weight M = m.weight (M.submatrix e e) := by
  unfold PerfectMatching.weight
  rw [m.lowerVerts_congr e, Finset.prod_map]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  simp [PerfectMatching.congr, Equiv.permCongr_apply]

/-- The Pfaffian is invariant under order isomorphisms of the index type. -/
theorem pfaffian_orderIso {α β R : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    [CommRing R] (e : α ≃o β) (M : Matrix β β R) :
    pfaffian (M.submatrix e e) = pfaffian M := by
  unfold pfaffian
  refine Fintype.sum_equiv (PerfectMatching.congrEquiv e.toEquiv) _ _ fun m ↦ ?_
  simp only [PerfectMatching.congrEquiv, Equiv.coe_fn_mk, PerfectMatching.sign,
    m.overlapCount_congr e, m.weight_congr e M]

/-- The Pfaffian of a principal submatrix depends only on the entries of `M` on `U`. -/
theorem pfaffianSubmatrix_congr {α R : Type*} [LinearOrder α] [CommRing R]
    {M N : Matrix α α R} {U : Finset α} (h : ∀ x ∈ U, ∀ y ∈ U, M x y = N x y) :
    pfaffianSubmatrix M U = pfaffianSubmatrix N U := by
  unfold pfaffianSubmatrix
  have hsub : M.submatrix (Subtype.val : U → α) (Subtype.val : U → α) =
      N.submatrix (Subtype.val : U → α) (Subtype.val : U → α) := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    exact h x hx y hy
  rw [hsub]

/-- Transporting a principal-submatrix Pfaffian along an order embedding `f : α ↪o β`. -/
theorem pfaffianSubmatrix_map {α β R : Type*} [LinearOrder α] [LinearOrder β] [CommRing R]
    (f : α ↪o β) (M : Matrix β β R) (U : Finset α) :
    pfaffianSubmatrix (M.submatrix f f) U = pfaffianSubmatrix M (U.map f.toEmbedding) := by
  unfold pfaffianSubmatrix
  let e : U ≃o (U.map f.toEmbedding) :=
    { toFun := fun x ↦ ⟨f x.1, Finset.mem_map_of_mem f.toEmbedding x.2⟩
      invFun := fun y ↦
        ⟨(Finset.mem_map.mp y.2).choose, (Finset.mem_map.mp y.2).choose_spec.1⟩
      left_inv := fun ⟨x, hx⟩ ↦ by
        ext
        have hs := (Finset.mem_map.mp (Finset.mem_map_of_mem f.toEmbedding hx)).choose_spec.2
        exact f.injective hs
      right_inv := fun ⟨y, hy⟩ ↦ by
        ext
        exact (Finset.mem_map.mp hy).choose_spec.2
      map_rel_iff' := fun {x y} ↦ by
        simp [Subtype.mk_le_mk] }
  have hsub : (M.submatrix f f).submatrix (Subtype.val : U → α) Subtype.val =
      (M.submatrix (Subtype.val : U.map f.toEmbedding → β) Subtype.val).submatrix e e := by
    ext x y
    rfl
  rw [hsub, pfaffian_orderIso e]

/-- The unique perfect matching on a `2`-element subset `{a, b}` (`a ≠ b`). -/
def PerfectMatching.pair {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) :
    PerfectMatching ({a, b} : Finset α) where
  toPerm := Equiv.swap ⟨a, by simp⟩ ⟨b, by simp⟩
  involutive x := Equiv.swap_apply_self _ _ x
  ne_self x := by
    rcases x with ⟨x, hx⟩
    have hx' : x = a ∨ x = b := by simpa using hx
    rcases hx' with hxa | hxb
    · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = ⟨a, by simp⟩ := Subtype.ext hxa
      rw [hsub, Equiv.swap_apply_left]
      exact fun h ↦ hab (congrArg Subtype.val h).symm
    · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = ⟨b, by simp⟩ := Subtype.ext hxb
      rw [hsub, Equiv.swap_apply_right]
      exact fun h ↦ hab (congrArg Subtype.val h)

theorem PerfectMatching.pair_unique {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (m : PerfectMatching ({a, b} : Finset α)) : m = PerfectMatching.pair hab := by
  ext ⟨x, hx⟩
  let pa : ({a, b} : Finset α) := ⟨a, by simp⟩
  let pb : ({a, b} : Finset α) := ⟨b, by simp⟩
  have hx' : x = a ∨ x = b := by simpa using hx
  rcases hx' with hxa | hxb
  · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = pa := Subtype.ext hxa
    rw [hsub]
    have hm : (m.toPerm pa).1 = a ∨ (m.toPerm pa).1 = b := by
      have hp := (m.toPerm pa).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp
    rcases hm with h1 | h1
    · exfalso; exact m.ne_self pa (Subtype.ext h1)
    · change (m.toPerm pa).1 = (Equiv.swap pa pb pa).1
      rw [Equiv.swap_apply_left]; exact h1
  · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = pb := Subtype.ext hxb
    rw [hsub]
    have hm : (m.toPerm pb).1 = a ∨ (m.toPerm pb).1 = b := by
      have hp := (m.toPerm pb).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp
    rcases hm with h1 | h1
    · change (m.toPerm pb).1 = (Equiv.swap pa pb pb).1
      rw [Equiv.swap_apply_right]; exact h1
    · exfalso; exact m.ne_self pb (Subtype.ext h1)

theorem PerfectMatching.pair_lowerVerts {α : Type*} [LinearOrder α] {a b : α} (hab : a < b) :
    (PerfectMatching.pair hab.ne).lowerVerts = {⟨a, by simp⟩} := by
  ext ⟨x, hx⟩
  let pa : ({a, b} : Finset α) := ⟨a, by simp⟩
  let pb : ({a, b} : Finset α) := ⟨b, by simp⟩
  simp only [PerfectMatching.mem_lowerVerts_iff, Finset.mem_singleton]
  have hx' : x = a ∨ x = b := by simpa using hx
  rcases hx' with hxa | hxb
  · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = pa := Subtype.ext hxa
    rw [hsub]
    change pa < Equiv.swap pa pb pa ↔ pa = pa
    rw [Equiv.swap_apply_left]
    exact ⟨fun _ ↦ rfl, fun _ ↦ hab⟩
  · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = pb := Subtype.ext hxb
    rw [hsub]
    change pb < Equiv.swap pa pb pb ↔ pb = pa
    rw [Equiv.swap_apply_right]
    exact ⟨fun h ↦ absurd h (not_lt_of_gt hab), fun h ↦ absurd (congrArg Subtype.val h) hab.ne'⟩

theorem PerfectMatching.pair_overlapCount {α : Type*} [LinearOrder α] {a b : α} (hab : a < b) :
    (PerfectMatching.pair hab.ne).overlapCount = 0 := by
  unfold PerfectMatching.overlapCount
  rw [PerfectMatching.pair_lowerVerts hab]
  simp

theorem PerfectMatching.pair_weight {α R : Type*} [LinearOrder α] [CommRing R]
    (M : Matrix α α R) {a b : α} (hab : a < b) :
    (PerfectMatching.pair hab.ne).weight
      (M.submatrix (Subtype.val : ({a, b} : Finset α) → α) Subtype.val) = M a b := by
  unfold PerfectMatching.weight
  rw [PerfectMatching.pair_lowerVerts hab, Finset.prod_singleton]
  change M a (Equiv.swap (⟨a, by simp⟩ : ({a, b} : Finset α)) ⟨b, by simp⟩ ⟨a, by simp⟩).1 = M a b
  rw [Equiv.swap_apply_left]

/-- The Pfaffian of a `2`-element principal submatrix `{a, b}` (`a < b`) is `M a b`. -/
theorem pfaffianSubmatrix_pair {α R : Type*} [LinearOrder α] [CommRing R]
    (M : Matrix α α R) {a b : α} (hab : a < b) :
    pfaffianSubmatrix M {a, b} = M a b := by
  unfold pfaffianSubmatrix pfaffian
  calc
    ∑ m : PerfectMatching ({a, b} : Finset α),
        m.sign R * m.weight (M.submatrix (Subtype.val : ({a, b} : Finset α) → α) Subtype.val)
      = (PerfectMatching.pair hab.ne).sign R *
          (PerfectMatching.pair hab.ne).weight
            (M.submatrix (Subtype.val : ({a, b} : Finset α) → α) Subtype.val) :=
        Fintype.sum_eq_single (PerfectMatching.pair hab.ne)
          (fun m hm ↦ absurd (PerfectMatching.pair_unique hab.ne m) hm)
    _ = M a b := by
        unfold PerfectMatching.sign
        rw [PerfectMatching.pair_overlapCount hab, PerfectMatching.pair_weight M hab]
        simp

/-! ### Decomposition of a perfect matching across an invariant subset -/

/-- The cross-overlap count between two perfect matchings on disjoint subsets `B` and `C` of a
linearly ordered type `α`: the number of pairs of edges `(u, mB u)` in `B` and `(v, mC v)` in `C`
that overlap in `α`. -/
def crossOverlapCount {α : Type*} [LinearOrder α] {B C : Finset α}
    (mB : PerfectMatching B) (mC : PerfectMatching C) : ℕ :=
  ((mB.lowerVerts ×ˢ mC.lowerVerts).filter fun p ↦
    ((p.1 : α) < (p.2 : α) ∧ (p.2 : α) < (mB.toPerm p.1 : α) ∧
      (mB.toPerm p.1 : α) < (mC.toPerm p.2 : α)) ∨
    ((p.2 : α) < (p.1 : α) ∧ (p.1 : α) < (mC.toPerm p.2 : α) ∧
      (mC.toPerm p.2 : α) < (mB.toPerm p.1 : α))).card

/-- Equation lemma for `crossOverlapCount`. -/
theorem crossOverlapCount_eq_card {α : Type*} [LinearOrder α] {B C : Finset α}
    (mB : PerfectMatching B) (mC : PerfectMatching C) :
    crossOverlapCount mB mC =
      ((mB.lowerVerts ×ˢ mC.lowerVerts).filter fun p ↦
        ((p.1 : α) < (p.2 : α) ∧ (p.2 : α) < (mB.toPerm p.1 : α) ∧
          (mB.toPerm p.1 : α) < (mC.toPerm p.2 : α)) ∨
        ((p.2 : α) < (p.1 : α) ∧ (p.1 : α) < (mC.toPerm p.2 : α) ∧
          (mC.toPerm p.2 : α) < (mB.toPerm p.1 : α))).card := by
  rfl

/-- `PerfectMatching.pair` sends `a` to `b`. -/
theorem PerfectMatching.pair_apply_left {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ((PerfectMatching.pair hab).toPerm ⟨a, by simp⟩).1 = b := by
  simp [PerfectMatching.pair]

/-- `PerfectMatching.pair` sends `b` to `a`. -/
theorem PerfectMatching.pair_apply_right {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ((PerfectMatching.pair hab).toPerm ⟨b, by simp⟩).1 = a := by
  simp [PerfectMatching.pair]

/-- Restrict a perfect matching `m` of `U` to an `m`-invariant subset `B ⊆ U`. -/
def PerfectMatching.restrict {α : Type*} {U B : Finset α}
    (m : PerfectMatching U) (hBU : B ⊆ U)
    (hinv : ∀ x : U, (x : α) ∈ B → (m.toPerm x : α) ∈ B) : PerfectMatching B where
  toPerm :=
    { toFun := fun x ↦ ⟨(m.toPerm ⟨x.1, hBU x.2⟩).1, hinv ⟨x.1, hBU x.2⟩ x.2⟩
      invFun := fun x ↦ ⟨(m.toPerm ⟨x.1, hBU x.2⟩).1, hinv ⟨x.1, hBU x.2⟩ x.2⟩
      left_inv := fun x ↦ Subtype.ext (by simp)
      right_inv := fun x ↦ Subtype.ext (by simp) }
  involutive x := Subtype.ext (by simp)
  ne_self x h := by
    have h' : m.toPerm ⟨x.1, hBU x.2⟩ = ⟨x.1, hBU x.2⟩ :=
      Subtype.ext (by simpa using congrArg Subtype.val h)
    exact m.ne_self ⟨x.1, hBU x.2⟩ h'

/-- Evaluation of `PerfectMatching.restrict` on subtype values. -/
theorem PerfectMatching.restrict_apply {α : Type*} {U B : Finset α}
    (m : PerfectMatching U) (hBU : B ⊆ U)
    (hinv : ∀ x : U, (x : α) ∈ B → (m.toPerm x : α) ∈ B) (x : B) :
    ((m.restrict hBU hinv).toPerm x).1 = (m.toPerm ⟨x.1, hBU x.2⟩).1 := by
  rfl

/-- Combine perfect matchings on disjoint `B, C : Finset α` into a perfect matching on `B ∪ C`. -/
def PerfectMatching.unionDisj {α : Type*} [DecidableEq α] {B C : Finset α}
    (hdisj : Disjoint B C) (mB : PerfectMatching B) (mC : PerfectMatching C) :
    PerfectMatching (B ∪ C : Finset α) where
  toPerm :=
    { toFun := fun x ↦
        if hx : (x : α) ∈ B then
          ⟨(mB.toPerm ⟨x.1, hx⟩).1, Finset.mem_union_left C (mB.toPerm ⟨x.1, hx⟩).2⟩
        else
          have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
          ⟨(mC.toPerm ⟨x.1, hxC⟩).1, Finset.mem_union_right B (mC.toPerm ⟨x.1, hxC⟩).2⟩
      invFun := fun x ↦
        if hx : (x : α) ∈ B then
          ⟨(mB.toPerm ⟨x.1, hx⟩).1, Finset.mem_union_left C (mB.toPerm ⟨x.1, hx⟩).2⟩
        else
          have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
          ⟨(mC.toPerm ⟨x.1, hxC⟩).1, Finset.mem_union_right B (mC.toPerm ⟨x.1, hxC⟩).2⟩
      left_inv := fun x ↦ by
        by_cases hx : (x : α) ∈ B
        · simp only [dite_eq_left hx]
          have h2 : (mB.toPerm ⟨x.1, hx⟩).1 ∈ B := (mB.toPerm ⟨x.1, hx⟩).2
          simp only [dite_eq_left h2]
          exact Subtype.ext (by simp)
        · simp only [dite_eq_right hx]
          have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
          have h2 : (mC.toPerm ⟨x.1, hxC⟩).1 ∉ B :=
            Finset.disjoint_right.mp hdisj (mC.toPerm ⟨x.1, hxC⟩).2
          simp only [dite_eq_right h2]
          exact Subtype.ext (by simp)
      right_inv := fun x ↦ by
        by_cases hx : (x : α) ∈ B
        · simp only [dite_eq_left hx]
          have h2 : (mB.toPerm ⟨x.1, hx⟩).1 ∈ B := (mB.toPerm ⟨x.1, hx⟩).2
          simp only [dite_eq_left h2]
          exact Subtype.ext (by simp)
        · simp only [dite_eq_right hx]
          have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
          have h2 : (mC.toPerm ⟨x.1, hxC⟩).1 ∉ B :=
            Finset.disjoint_right.mp hdisj (mC.toPerm ⟨x.1, hxC⟩).2
          simp only [dite_eq_right h2]
          exact Subtype.ext (by simp) }
  involutive x := by
    by_cases hx : (x : α) ∈ B
    · simp only [Equiv.coe_fn_mk, dite_eq_left hx]
      have h2 : (mB.toPerm ⟨x.1, hx⟩).1 ∈ B := (mB.toPerm ⟨x.1, hx⟩).2
      simp only [dite_eq_left h2]
      exact Subtype.ext (by simp)
    · simp only [Equiv.coe_fn_mk, dite_eq_right hx]
      have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
      have h2 : (mC.toPerm ⟨x.1, hxC⟩).1 ∉ B :=
        Finset.disjoint_right.mp hdisj (mC.toPerm ⟨x.1, hxC⟩).2
      simp only [dite_eq_right h2]
      exact Subtype.ext (by simp)
  ne_self x h := by
    by_cases hx : (x : α) ∈ B
    · simp only [Equiv.coe_fn_mk, dite_eq_left hx] at h
      exact mB.ne_self ⟨x.1, hx⟩ (Subtype.ext (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) h))
    · simp only [Equiv.coe_fn_mk, dite_eq_right hx] at h
      have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
      exact mC.ne_self ⟨x.1, hxC⟩ (Subtype.ext (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) h))

/-- Evaluation of `PerfectMatching.unionDisj` on the left component `B`. -/
theorem PerfectMatching.unionDisj_apply_left {α : Type*} [DecidableEq α] {B C : Finset α}
    (hdisj : Disjoint B C) (mB : PerfectMatching B) (mC : PerfectMatching C) (x : B) :
    ((mB.unionDisj hdisj mC).toPerm ⟨x.1, Finset.mem_union_left C x.2⟩).1 = (mB.toPerm x).1 := by
  change (if hx : x.1 ∈ B then _ else _ : (B ∪ C : Finset α)).1 = _
  simp only [x.2, ↓reduceDIte]

/-- Evaluation of `PerfectMatching.unionDisj` on the right component `C`. -/
theorem PerfectMatching.unionDisj_apply_right {α : Type*} [DecidableEq α] {B C : Finset α}
    (hdisj : Disjoint B C) (mB : PerfectMatching B) (mC : PerfectMatching C) (x : C) :
    ((mB.unionDisj hdisj mC).toPerm ⟨x.1, Finset.mem_union_right B x.2⟩).1 = (mC.toPerm x).1 := by
  have hxB : x.1 ∉ B := Finset.disjoint_right.mp hdisj x.2
  change (if hx : x.1 ∈ B then _ else _ : (B ∪ C : Finset α)).1 = _
  simp only [hxB, ↓reduceDIte]

/-- Evaluation of `PerfectMatching.congr`. -/
theorem PerfectMatching.congr_apply {α β : Type*} (e : α ≃ β) (m : PerfectMatching α) (y : β) :
    (m.congr e).toPerm y = e (m.toPerm (e.symm y)) := by
  rfl

/-- Weight of `unionDisj mB mC` factors as the product of weights of `mB` and `mC`. -/
theorem PerfectMatching.weight_unionDisj {α R : Type*} [LinearOrder α] [CommRing R]
    {B C : Finset α} (hdisj : Disjoint B C) (M : Matrix α α R)
    (mB : PerfectMatching B) (mC : PerfectMatching C) :
    (mB.unionDisj hdisj mC).weight (M.submatrix Subtype.val Subtype.val) =
      mB.weight (M.submatrix Subtype.val Subtype.val) *
        mC.weight (M.submatrix Subtype.val Subtype.val) := by
  unfold PerfectMatching.weight
  let incB : B ↪ (B ∪ C : Finset α) :=
    ⟨fun x ↦ ⟨x.1, Finset.mem_union_left C x.2⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) h)⟩
  let incC : C ↪ (B ∪ C : Finset α) :=
    ⟨fun x ↦ ⟨x.1, Finset.mem_union_right B x.2⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) h)⟩
  have hpart : (mB.unionDisj hdisj mC).lowerVerts =
      mB.lowerVerts.map incB ∪ mC.lowerVerts.map incC := by
    ext x
    simp only [PerfectMatching.mem_lowerVerts_iff, Finset.mem_union, Finset.mem_map, incB, incC]
    by_cases hx : (x : α) ∈ B
    · have hxC : (x : α) ∉ C := Finset.disjoint_left.mp hdisj hx
      have hmx : ((mB.unionDisj hdisj mC).toPerm x).1 = (mB.toPerm ⟨x.1, hx⟩).1 := by
        simp [PerfectMatching.unionDisj, hx]
      constructor
      · intro hlt
        left
        refine ⟨⟨x.1, hx⟩, ?_, Subtype.ext rfl⟩
        change x.1 < (mB.toPerm ⟨x.1, hx⟩).1
        rw [← hmx]; exact hlt
      · rintro (⟨y, hy, hyx⟩ | ⟨y, _, hyx⟩)
        · have : y = ⟨x.1, hx⟩ := Subtype.ext (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) hyx)
          subst this
          change x.1 < ((mB.unionDisj hdisj mC).toPerm x).1
          rw [hmx]; exact hy
        · exact absurd (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) hyx ▸ y.2) hxC
    · have hxC : (x : α) ∈ C := (Finset.mem_union.mp x.2).resolve_left hx
      have hmx : ((mB.unionDisj hdisj mC).toPerm x).1 = (mC.toPerm ⟨x.1, hxC⟩).1 := by
        simp [PerfectMatching.unionDisj, hx]
      constructor
      · intro hlt
        right
        refine ⟨⟨x.1, hxC⟩, ?_, Subtype.ext rfl⟩
        change x.1 < (mC.toPerm ⟨x.1, hxC⟩).1
        rw [← hmx]; exact hlt
      · rintro (⟨y, _, hyx⟩ | ⟨y, hy, hyx⟩)
        · exact absurd (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) hyx ▸ y.2) hx
        · have : y = ⟨x.1, hxC⟩ := Subtype.ext (congrArg (fun z : (B ∪ C : Finset α) ↦ z.1) hyx)
          subst this
          change x.1 < ((mB.unionDisj hdisj mC).toPerm x).1
          rw [hmx]; exact hy
  have hdisjMap : Disjoint (mB.lowerVerts.map incB) (mC.lowerVerts.map incC) := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    rcases Finset.mem_map.mp hxB with ⟨y, _, rfl⟩
    rcases Finset.mem_map.mp hxC with ⟨z, _, hzy⟩
    have hyz : z.1 = y.1 := congrArg (fun w : (B ∪ C : Finset α) ↦ w.1) hzy
    exact Finset.disjoint_left.mp hdisj y.2 (hyz ▸ z.2)
  rw [hpart, Finset.prod_union hdisjMap, Finset.prod_map, Finset.prod_map]
  congr 1
  · refine Finset.prod_congr rfl fun x _ ↦ ?_
    change M x.1 ((mB.unionDisj hdisj mC).toPerm (incB x)).1 = M x.1 (mB.toPerm x).1
    have hval : (incB x).1 = x.1 := rfl
    have hmx : ((mB.unionDisj hdisj mC).toPerm (incB x)).1 = (mB.toPerm x).1 := by
      change (if h : (incB x).1 ∈ B then _ else _ : (B ∪ C : Finset α)).1 = _
      simp only [hval, dite_eq_left x.2]
    rw [hmx]
  · refine Finset.prod_congr rfl fun x _ ↦ ?_
    change M x.1 ((mB.unionDisj hdisj mC).toPerm (incC x)).1 = M x.1 (mC.toPerm x).1
    have hxB : x.1 ∉ B := Finset.disjoint_right.mp hdisj x.2
    have hval : (incC x).1 = x.1 := rfl
    have hmx : ((mB.unionDisj hdisj mC).toPerm (incC x)).1 = (mC.toPerm x).1 := by
      change (if h : (incC x).1 ∈ B then _ else _ : (B ∪ C : Finset α)).1 = _
      simp only [hval, dite_eq_right hxB]
    rw [hmx]

/-- Overlap count of `unionDisj mB mC` equals
`mB.overlapCount + mC.overlapCount + crossOverlapCount`. -/
theorem PerfectMatching.overlapCount_unionDisj {α : Type*} [LinearOrder α]
    {B C : Finset α} (hdisj : Disjoint B C)
    (mB : PerfectMatching B) (mC : PerfectMatching C) :
    (mB.unionDisj hdisj mC).overlapCount =
      mB.overlapCount + mC.overlapCount + crossOverlapCount mB mC := by
  let m := mB.unionDisj hdisj mC
  let S := (m.lowerVerts ×ˢ m.lowerVerts).filter
    fun p ↦ p.1 < p.2 ∧ p.2 < m.toPerm p.1 ∧ m.toPerm p.1 < m.toPerm p.2
  have hcard : S.card =
      (S.filter fun p ↦ (p.1 : α) ∈ B ∧ (p.2 : α) ∈ B).card +
      (S.filter fun p ↦ (p.1 : α) ∉ B ∧ (p.2 : α) ∉ B).card +
      (S.filter fun p ↦ ((p.1 : α) ∈ B ∧ (p.2 : α) ∉ B) ∨
        ((p.1 : α) ∉ B ∧ (p.2 : α) ∈ B)).card := by
    have h1 := (Finset.card_filter_add_card_filter_not (s := S)
      (p := fun p ↦ (p.1 : α) ∈ B ∧ (p.2 : α) ∈ B)).symm
    have h2 := (Finset.card_filter_add_card_filter_not
      (s := S.filter fun p ↦ ¬((p.1 : α) ∈ B ∧ (p.2 : α) ∈ B))
      (p := fun p ↦ (p.1 : α) ∉ B ∧ (p.2 : α) ∉ B)).symm
    have heq1 : (S.filter fun p ↦ ¬((p.1 : α) ∈ B ∧ (p.2 : α) ∈ B)).filter
        (fun p ↦ (p.1 : α) ∉ B ∧ (p.2 : α) ∉ B) =
        S.filter (fun p ↦ (p.1 : α) ∉ B ∧ (p.2 : α) ∉ B) := by
      ext p; simp only [Finset.mem_filter]; tauto
    have heq2 : (S.filter fun p ↦ ¬((p.1 : α) ∈ B ∧ (p.2 : α) ∈ B)).filter
        (fun p ↦ ¬((p.1 : α) ∉ B ∧ (p.2 : α) ∉ B)) =
        S.filter (fun p ↦ ((p.1 : α) ∈ B ∧ (p.2 : α) ∉ B) ∨
          ((p.1 : α) ∉ B ∧ (p.2 : α) ∈ B)) := by
      ext p; simp only [Finset.mem_filter]; tauto
    rw [heq1, heq2] at h2
    omega
  change S.card = _
  rw [hcard]
  have hBB : (S.filter fun p ↦ (p.1 : α) ∈ B ∧ (p.2 : α) ∈ B).card = mB.overlapCount := by
    unfold PerfectMatching.overlapCount
    refine Finset.card_bij
      (fun p hp ↦ (⟨p.1.1, (Finset.mem_filter.mp hp).2.1⟩, ⟨p.2.1, (Finset.mem_filter.mp hp).2.2⟩))
      ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, S, Finset.mem_product,
        PerfectMatching.mem_lowerVerts_iff] at hp ⊢
      rcases hp with ⟨⟨⟨hx, hy⟩, h1, h2, h3⟩, hxB, hyB⟩
      have hmx : (m.toPerm x).1 = (mB.toPerm ⟨x.1, hxB⟩).1 := by
        simp [m, PerfectMatching.unionDisj, hxB]
      have hmy : (m.toPerm y).1 = (mB.toPerm ⟨y.1, hyB⟩).1 := by
        simp [m, PerfectMatching.unionDisj, hyB]
      refine ⟨⟨?_, ?_⟩, h1, ?_, ?_⟩
      · change x.1 < (mB.toPerm ⟨x.1, hxB⟩).1; rw [← hmx]; exact hx
      · change y.1 < (mB.toPerm ⟨y.1, hyB⟩).1; rw [← hmy]; exact hy
      · change y.1 < (mB.toPerm ⟨x.1, hxB⟩).1; rw [← hmx]; exact h2
      · change (mB.toPerm ⟨x.1, hxB⟩).1 < (mB.toPerm ⟨y.1, hyB⟩).1
        rw [← hmx, ← hmy]; exact h3
    · rintro ⟨x₁, y₁⟩ _ ⟨x₂, y₂⟩ _ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff] at hp
      refine ⟨(⟨x.1, Finset.mem_union_left C x.2⟩, ⟨y.1, Finset.mem_union_left C y.2⟩), ?_, by simp⟩
      simp only [Finset.mem_filter, S, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff,
        m, PerfectMatching.unionDisj, Equiv.coe_fn_mk, dite_eq_left x.2, dite_eq_left y.2]
      exact ⟨⟨⟨hp.1.1, hp.1.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2⟩, x.2, y.2⟩
  have hCC : (S.filter fun p ↦ (p.1 : α) ∉ B ∧ (p.2 : α) ∉ B).card = mC.overlapCount := by
    unfold PerfectMatching.overlapCount
    refine Finset.card_bij
      (fun p hp ↦
        (⟨p.1.1, (Finset.mem_union.mp p.1.2).resolve_left (Finset.mem_filter.mp hp).2.1⟩,
         ⟨p.2.1, (Finset.mem_union.mp p.2.2).resolve_left (Finset.mem_filter.mp hp).2.2⟩))
      ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, S, Finset.mem_product,
        PerfectMatching.mem_lowerVerts_iff] at hp ⊢
      rcases hp with ⟨⟨⟨hx, hy⟩, h1, h2, h3⟩, hxB, hyB⟩
      have hxC : x.1 ∈ C := (Finset.mem_union.mp x.2).resolve_left hxB
      have hyC : y.1 ∈ C := (Finset.mem_union.mp y.2).resolve_left hyB
      have hmx : (m.toPerm x).1 = (mC.toPerm ⟨x.1, hxC⟩).1 := by
        simp [m, PerfectMatching.unionDisj, hxB]
      have hmy : (m.toPerm y).1 = (mC.toPerm ⟨y.1, hyC⟩).1 := by
        simp [m, PerfectMatching.unionDisj, hyB]
      refine ⟨⟨?_, ?_⟩, h1, ?_, ?_⟩
      · change x.1 < (mC.toPerm ⟨x.1, hxC⟩).1; rw [← hmx]; exact hx
      · change y.1 < (mC.toPerm ⟨y.1, hyC⟩).1; rw [← hmy]; exact hy
      · change y.1 < (mC.toPerm ⟨x.1, hxC⟩).1; rw [← hmx]; exact h2
      · change (mC.toPerm ⟨x.1, hxC⟩).1 < (mC.toPerm ⟨y.1, hyC⟩).1
        rw [← hmx, ← hmy]; exact h3
    · rintro ⟨x₁, y₁⟩ _ ⟨x₂, y₂⟩ _ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff] at hp
      have hxB : x.1 ∉ B := Finset.disjoint_right.mp hdisj x.2
      have hyB : y.1 ∉ B := Finset.disjoint_right.mp hdisj y.2
      refine ⟨(⟨x.1, Finset.mem_union_right B x.2⟩, ⟨y.1, Finset.mem_union_right B y.2⟩), ?_,
        by simp⟩
      simp only [Finset.mem_filter, S, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff,
        m, PerfectMatching.unionDisj, Equiv.coe_fn_mk, dite_eq_right hxB, dite_eq_right hyB]
      exact ⟨⟨⟨hp.1.1, hp.1.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2⟩, hxB, hyB⟩
  have hBC : (S.filter fun p ↦ ((p.1 : α) ∈ B ∧ (p.2 : α) ∉ B) ∨
      ((p.1 : α) ∉ B ∧ (p.2 : α) ∈ B)).card = crossOverlapCount mB mC := by
    unfold crossOverlapCount
    refine Finset.card_bij
      (fun p hp ↦
        if h : (p.1 : α) ∈ B then
          (⟨p.1.1, h⟩, ⟨p.2.1, (Finset.mem_union.mp p.2.2).resolve_left
            (((Finset.mem_filter.mp hp).2).elim And.right fun h' ↦ absurd h h'.1)⟩)
        else
          (⟨p.2.1, ((Finset.mem_filter.mp hp).2).elim (fun h' ↦ absurd h'.1 h) And.right⟩,
           ⟨p.1.1, (Finset.mem_union.mp p.1.2).resolve_left h⟩))
      ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, S, Finset.mem_product,
        PerfectMatching.mem_lowerVerts_iff] at hp
      rcases hp with ⟨⟨⟨hx, hy⟩, h1, h2, h3⟩, hcase⟩
      by_cases hxB : x.1 ∈ B
      · have hyB : y.1 ∉ B := hcase.elim And.right (fun h' ↦ absurd hxB h'.1)
        have hyC : y.1 ∈ C := (Finset.mem_union.mp y.2).resolve_left hyB
        have hmx : (m.toPerm x).1 = (mB.toPerm ⟨x.1, hxB⟩).1 := by
          simp [m, PerfectMatching.unionDisj, hxB]
        have hmy : (m.toPerm y).1 = (mC.toPerm ⟨y.1, hyC⟩).1 := by
          simp [m, PerfectMatching.unionDisj, hyB]
        simp only [dite_eq_left hxB, Finset.mem_filter, Finset.mem_product,
          PerfectMatching.mem_lowerVerts_iff]
        refine ⟨⟨?_, ?_⟩, Or.inl ⟨h1, ?_, ?_⟩⟩
        · change x.1 < (mB.toPerm ⟨x.1, hxB⟩).1; rw [← hmx]; exact hx
        · change y.1 < (mC.toPerm ⟨y.1, hyC⟩).1; rw [← hmy]; exact hy
        · rw [← hmx]; exact h2
        · rw [← hmx, ← hmy]; exact h3
      · have hyB : y.1 ∈ B := hcase.elim (fun h' ↦ absurd h'.1 hxB) And.right
        have hxC : x.1 ∈ C := (Finset.mem_union.mp x.2).resolve_left hxB
        have hmx : (m.toPerm x).1 = (mC.toPerm ⟨x.1, hxC⟩).1 := by
          simp [m, PerfectMatching.unionDisj, hxB]
        have hmy : (m.toPerm y).1 = (mB.toPerm ⟨y.1, hyB⟩).1 := by
          simp [m, PerfectMatching.unionDisj, hyB]
        simp only [dite_eq_right hxB, Finset.mem_filter, Finset.mem_product,
          PerfectMatching.mem_lowerVerts_iff]
        refine ⟨⟨?_, ?_⟩, Or.inr ⟨h1, ?_, ?_⟩⟩
        · change y.1 < (mB.toPerm ⟨y.1, hyB⟩).1; rw [← hmy]; exact hy
        · change x.1 < (mC.toPerm ⟨x.1, hxC⟩).1; rw [← hmx]; exact hx
        · rw [← hmx]; exact h2
        · rw [← hmx, ← hmy]; exact h3
    · rintro ⟨x₁, y₁⟩ hp₁ ⟨x₂, y₂⟩ hp₂ h
      simp only [Finset.mem_filter, S] at hp₁ hp₂
      by_cases h1 : x₁.1 ∈ B <;> by_cases h2 : x₂.1 ∈ B
      · simp only [dite_eq_left h1, dite_eq_left h2, Prod.mk.injEq, Subtype.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
      · simp only [dite_eq_left h1, dite_eq_right h2, Prod.mk.injEq, Subtype.mk.injEq] at h
        have hlt1 : x₁.1 < y₁.1 := hp₁.1.2.1
        have hlt2 : x₂.1 < y₂.1 := hp₂.1.2.1
        have hlt1' : y₂.1 < x₂.1 := by rw [← h.1, ← h.2]; exact hlt1
        exact absurd hlt1' (not_lt_of_gt hlt2)
      · simp only [dite_eq_right h1, dite_eq_left h2, Prod.mk.injEq, Subtype.mk.injEq] at h
        have hlt1 : x₁.1 < y₁.1 := hp₁.1.2.1
        have hlt2 : x₂.1 < y₂.1 := hp₂.1.2.1
        have hlt2' : y₁.1 < x₁.1 := by rw [h.1, h.2]; exact hlt2
        exact absurd hlt2' (not_lt_of_gt hlt1)
      · simp only [dite_eq_right h1, dite_eq_right h2, Prod.mk.injEq, Subtype.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.2) (Subtype.ext h.1)
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff] at hp
      have hyB : y.1 ∉ B := Finset.disjoint_right.mp hdisj y.2
      rcases hp.2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · refine ⟨(⟨x.1, Finset.mem_union_left C x.2⟩, ⟨y.1, Finset.mem_union_right B y.2⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, S, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff,
            m, PerfectMatching.unionDisj, Equiv.coe_fn_mk, dite_eq_left x.2, dite_eq_right hyB]
          exact ⟨⟨⟨hp.1.1, hp.1.2⟩, h1, h2, h3⟩, Or.inl ⟨x.2, hyB⟩⟩
        · simp [x.2]
      · refine ⟨(⟨y.1, Finset.mem_union_right B y.2⟩, ⟨x.1, Finset.mem_union_left C x.2⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, S, Finset.mem_product, PerfectMatching.mem_lowerVerts_iff,
            m, PerfectMatching.unionDisj, Equiv.coe_fn_mk, dite_eq_left x.2, dite_eq_right hyB]
          exact ⟨⟨⟨hp.1.2, hp.1.1⟩, h1, h2, h3⟩, Or.inr ⟨hyB, x.2⟩⟩
        · simp [hyB]
  rw [hBB, hCC, hBC]

/-- Master Overlap Parity Lemma: the number of edges of a perfect matching `m` on `C : Finset α`
that overlap a single arc `(a, b)` (`a < b`, disjoint from `C`) has the same parity as the number
of vertices of `C` strictly between `a` and `b`. -/
theorem crossOverlapCount_pair_mod_two {α : Type*} [LinearOrder α]
    {a b : α} (hab : a < b) {C : Finset α} (ha : a ∉ C) (hb : b ∉ C)
    (mPair : PerfectMatching ({a, b} : Finset α)) (mC : PerfectMatching C) :
    crossOverlapCount mPair mC ≡ (C.filter fun x ↦ a < x ∧ x < b).card [MOD 2] := by
  let pa : ({a, b} : Finset α) := ⟨a, by simp⟩
  let pb : ({a, b} : Finset α) := ⟨b, by simp⟩
  have hmPair_a : mPair.toPerm pa = pb := by
    have hm := (mPair.toPerm pa).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact absurd (Subtype.ext h) (mPair.ne_self pa)
    · exact Subtype.ext h
  have hlv : mPair.lowerVerts = {pa} := by
    ext ⟨x, hx⟩
    simp only [PerfectMatching.mem_lowerVerts_iff, Finset.mem_singleton]
    have hx' : x = a ∨ x = b := by simpa using hx
    rcases hx' with hxa | hxb
    · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = pa := Subtype.ext hxa
      rw [hsub]
      change pa < mPair.toPerm pa ↔ pa = pa
      rw [hmPair_a]; exact ⟨fun _ ↦ rfl, fun _ ↦ hab⟩
    · have hsub : (⟨x, hx⟩ : ({a, b} : Finset α)) = pb := Subtype.ext hxb
      rw [hsub]
      have hmPair_b : mPair.toPerm pb = pa := mPair.apply_eq_iff.mp hmPair_a
      change pb < mPair.toPerm pb ↔ pb = pa
      rw [hmPair_b]
      exact ⟨fun h ↦ absurd h (not_lt_of_gt hab), fun h ↦ absurd (congrArg Subtype.val h) hab.ne'⟩
  have hcross : crossOverlapCount mPair mC =
      (mC.lowerVerts.filter fun (v : C) ↦
        (a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
        ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b)).card := by
    unfold crossOverlapCount
    rw [hlv]
    refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
    · rintro ⟨u, v⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp ⊢
      rcases hp with ⟨⟨rfl, hv⟩, h⟩
      rw [hmPair_a] at h
      exact ⟨hv, h⟩
    · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp₁ hp₂
      exact Prod.ext (hp₁.1.1.trans hp₂.1.1.symm) h
    · intro v hv
      simp only [Finset.mem_filter] at hv
      refine ⟨(pa, v), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, hmPair_a]
      exact ⟨⟨trivial, hv.1⟩, hv.2⟩
  -- Count vertices in `C ∩ (a, b)` by grouping into edges `(v, mC v)` of `mC`:
  -- each edge has 0, 1, or 2 endpoints in `(a, b)`, and has 1 endpoint iff it overlaps `(a, b)`.
  let ind (x : C) : ℕ := if a < (x : α) ∧ (x : α) < b then 1 else 0
  have hsum_all : (C.filter fun x ↦ a < x ∧ x < b).card = ∑ x : C, ind x := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_bij (fun x hx ↦ ⟨x, (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.2
    · intro x₁ _ x₂ _ h; exact congrArg (fun z : C ↦ z.1) h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩, Subtype.ext rfl⟩
  have hsum_pairs : ∑ x : C, ind x = ∑ v ∈ mC.lowerVerts, (ind v + ind (mC.toPerm v)) := by
    have hsplit : ∑ v ∈ Finset.univ \ mC.lowerVerts, ind v + ∑ v ∈ mC.lowerVerts, ind v =
        ∑ x : C, ind x :=
      Finset.sum_sdiff (Finset.subset_univ mC.lowerVerts)
    rw [← hsplit, add_comm, Finset.sum_add_distrib]
    congr 1
    have himg : Finset.univ \ mC.lowerVerts = mC.lowerVerts.image mC.toPerm := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image,
        PerfectMatching.mem_lowerVerts_iff]
      constructor
      · intro hy
        refine ⟨mC.toPerm y, ?_, mC.apply_apply y⟩
        rw [mC.apply_apply]
        exact lt_of_le_of_ne (not_lt.mp hy) (mC.ne_self y)
      · rintro ⟨x, hx, rfl⟩
        rw [mC.apply_apply]
        exact not_lt.mpr hx.le
    rw [himg, Finset.sum_image (fun x _ y _ h ↦ mC.toPerm.injective h)]
  have hterm : ∀ v ∈ mC.lowerVerts,
      ind v + ind (mC.toPerm v) ≡
        (if (a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
            ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b)
          then 1 else 0) [MOD 2] := by
    intro v hv
    have hlt : (v : α) < (mC.toPerm v : α) := (mC.mem_lowerVerts_iff v).mp hv
    have hva : (v : α) ≠ a := fun h ↦ ha (h ▸ v.2)
    have hwb : (mC.toPerm v : α) ≠ b := fun h ↦ hb (h ▸ (mC.toPerm v).2)
    by_cases h1 : a < (v : α) ∧ (v : α) < b <;>
      by_cases h2 : a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b
    · have hno : ¬((a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
          ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b)) := by
        rintro (⟨_, _, h⟩ | ⟨h, _, _⟩)
        · exact not_lt_of_gt h h2.2
        · exact not_lt_of_gt h h1.1
      rw [ite_eq_right hno]
      simp [ind, h1, h2, Nat.ModEq]
    · have hbw : b < (mC.toPerm v : α) := by
        rcases lt_or_gt_of_ne hwb with h | h
        · exact absurd ⟨lt_trans h1.1 hlt, h⟩ h2
        · exact h
      have hyes : (a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
          ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b) :=
        Or.inl ⟨h1.1, h1.2, hbw⟩
      rw [ite_eq_left hyes]
      simp [ind, h1, h2, Nat.ModEq]
    · have hva' : (v : α) < a := by
        rcases lt_or_gt_of_ne hva with h | h
        · exact h
        · exact absurd ⟨h, lt_trans hlt h2.2⟩ h1
      have hyes : (a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
          ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b) :=
        Or.inr ⟨hva', h2.1, h2.2⟩
      rw [ite_eq_left hyes]
      simp [ind, h1, h2, Nat.ModEq]
    · have hno : ¬((a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
          ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b)) := by
        rintro (⟨h1a, h1b, _⟩ | ⟨_, h2a, h2b⟩)
        · exact h1 ⟨h1a, h1b⟩
        · exact h2 ⟨h2a, h2b⟩
      rw [ite_eq_right hno]
      simp [ind, h1, h2, Nat.ModEq]
  rw [hcross, hsum_all, hsum_pairs]
  have hcard_sum :
      (mC.lowerVerts.filter fun (v : C) ↦
        (a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
        ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b)).card =
      ∑ v ∈ mC.lowerVerts,
        if (a < (v : α) ∧ (v : α) < b ∧ b < (mC.toPerm v : α)) ∨
           ((v : α) < a ∧ a < (mC.toPerm v : α) ∧ (mC.toPerm v : α) < b)
        then 1 else 0 := by
    rw [Finset.sum_boole, Nat.cast_id]
  rw [hcard_sum]
  have hmod_sum : ∀ (s : Finset C) (f g : C → ℕ),
      (∀ v ∈ s, f v ≡ g v [MOD 2]) → ∑ v ∈ s, f v ≡ ∑ v ∈ s, g v [MOD 2] := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp; rfl
    | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact (hfg x (Finset.mem_insert_self x s)).add
        (ih fun v hv ↦ hfg v (Finset.mem_insert_of_mem hv))
  exact (hmod_sum mC.lowerVerts _ _ hterm).symm

/-- Even-parity helper: `(-1)^a = (-1)^b` whenever `a ≡ b [MOD 2]`. -/
theorem neg_one_pow_eq_of_modEq {R : Type*} [Ring R] {a b : ℕ} (h : a ≡ b [MOD 2]) :
    (-1 : R) ^ a = (-1 : R) ^ b := by
  have h1 : (-1 : R) ^ a = (-1 : R) ^ (a % 2) := by
    conv_lhs => rw [← Nat.div_add_mod a 2, pow_add, pow_mul]
    simp
  have h2 : (-1 : R) ^ b = (-1 : R) ^ (b % 2) := by
    conv_lhs => rw [← Nat.div_add_mod b 2, pow_add, pow_mul]
    simp
  rw [h1, h2, h]

/-- The Pfaffian of an alternating matrix on a nonempty `U : Finset α` expands along its minimum
vertex `a = U.min' hU`. -/
theorem pfaffianSubmatrix_eq_sum_min {α R : Type*} [LinearOrder α] [CommRing R]
    (M : Matrix α α R) {U : Finset α} (hU : U.Nonempty) :
    let a := U.min' hU
    pfaffianSubmatrix M U =
      ∑ b ∈ U.erase a,
        (-1 : R) ^ ((U.filter fun x ↦ a < x ∧ x < b).card) *
          M a b * pfaffianSubmatrix M ((U.erase a).erase b) := by
  intro a
  have haU : a ∈ U := Finset.min'_mem U hU
  have ha_le : ∀ x ∈ U, a ≤ x := fun x hx ↦ Finset.min'_le U x hx
  unfold pfaffianSubmatrix pfaffian
  let pa : U := ⟨a, haU⟩
  -- Partition `PerfectMatching U` by the partner `b = (m.toPerm pa).1 ∈ U.erase a`
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m : PerfectMatching U ↦ (m.toPerm pa).1)
    (t := U.erase a) (fun m _ ↦ Finset.mem_erase.mpr
      ⟨fun h ↦ m.ne_self pa (Subtype.ext h), (m.toPerm pa).2⟩)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbU : b ∈ U := (Finset.mem_erase.mp hb).2
  have hab : a < b := lt_of_le_of_ne (ha_le b hbU) hba.symm
  let B : Finset α := {a, b}
  let C : Finset α := (U.erase a).erase b
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hxB
    simp only [C, Finset.mem_erase] at hxC
    rcases hxB with rfl | rfl
    · exact hxC.2.1 rfl
    · exact hxC.1 rfl
  have hBC : B ∪ C = U := by
    ext x
    simp only [B, C, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ((rfl | rfl) | ⟨_, _, hx⟩)
      · exact haU
      · exact hbU
      · exact hx
    · intro hx
      by_cases h1 : x = a
      · left; left; exact h1
      · by_cases h2 : x = b
        · left; right; exact h2
        · right; exact ⟨h2, h1, hx⟩
  -- Canonical matching on `{a, b}`
  let mPair : PerfectMatching B := PerfectMatching.pair hab.ne
  have hmPair_ov : mPair.overlapCount = 0 := PerfectMatching.pair_overlapCount hab
  have hmPair_wt : mPair.weight (M.submatrix (Subtype.val : B → α) Subtype.val) = M a b :=
    PerfectMatching.pair_weight M hab
  rw [Finset.mul_sum]
  let eU : (B ∪ C : Finset α) ≃o U :=
    { toFun := fun x ↦ ⟨x.1, hBC ▸ x.2⟩
      invFun := fun x ↦ ⟨x.1, hBC.symm ▸ x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }
  refine Finset.sum_bij
    (fun m hm ↦ m.restrict (fun x hx ↦ (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2)
      (fun x hxC ↦ by
        have hma : (m.toPerm pa).1 = b := (Finset.mem_filter.mp hm).2
        have hmb : (m.toPerm ⟨b, hbU⟩).1 = a := by
          have : m.toPerm pa = ⟨b, hbU⟩ := Subtype.ext hma
          exact congrArg Subtype.val (m.apply_eq_iff.mp this)
        simp only [Finset.mem_erase] at hxC ⊢
        refine ⟨?_, ?_, (m.toPerm x).2⟩
        · intro h
          have hx_eq : x = pa := m.toPerm.injective (Subtype.ext (h.trans hma.symm))
          exact hxC.2.1 (congrArg Subtype.val hx_eq)
        · intro h
          have hx_eq : x = ⟨b, hbU⟩ := m.toPerm.injective (Subtype.ext (h.trans hmb.symm))
          exact hxC.1 (congrArg Subtype.val hx_eq)))
    (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro m₁ hm₁ m₂ hm₂ heq
    have hma₁ : (m₁.toPerm pa).1 = b := (Finset.mem_filter.mp hm₁).2
    have hma₂ : (m₂.toPerm pa).1 = b := (Finset.mem_filter.mp hm₂).2
    ext x
    by_cases hxa : x.1 = a
    · have : x = pa := Subtype.ext hxa
      subst this; exact hma₁.trans hma₂.symm
    · by_cases hxb : x.1 = b
      · have h1 : m₁.toPerm pa = x := Subtype.ext (hma₁.trans hxb.symm)
        have h2 : m₂.toPerm pa = x := Subtype.ext (hma₂.trans hxb.symm)
        rw [m₁.apply_eq_iff.mp h1, m₂.apply_eq_iff.mp h2]
      · have hxC : x.1 ∈ C := Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, x.2⟩⟩
        exact congrArg (fun k : PerfectMatching C ↦ (k.toPerm ⟨x.1, hxC⟩).1) heq
  · intro mC _
    let mBC : PerfectMatching (B ∪ C : Finset α) := mPair.unionDisj hdisj mC
    let m : PerfectMatching U := mBC.congr eU.toEquiv
    refine ⟨m, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, m, mBC, PerfectMatching.congr,
        Equiv.permCongr_apply, eU, Equiv.coe_fn_mk, PerfectMatching.unionDisj]
      have haB : a ∈ B := by simp [B]
      simp [pa, haB, mPair, PerfectMatching.pair]
    · ext x
      have hxB : x.1 ∉ B := Finset.disjoint_right.mp hdisj x.2
      simp [PerfectMatching.restrict, m, mBC, PerfectMatching.congr, Equiv.permCongr_apply, eU,
        PerfectMatching.unionDisj, hxB]
  · intro m hm
    let mC : PerfectMatching C := m.restrict
      (fun x hx ↦ (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2)
      (fun x hxC ↦ by
        have hma : (m.toPerm pa).1 = b := (Finset.mem_filter.mp hm).2
        have hmb : (m.toPerm ⟨b, hbU⟩).1 = a := by
          have : m.toPerm pa = ⟨b, hbU⟩ := Subtype.ext hma
          exact congrArg Subtype.val (m.apply_eq_iff.mp this)
        simp only [C, Finset.mem_erase] at hxC ⊢
        refine ⟨?_, ?_, (m.toPerm x).2⟩
        · intro h
          have hx_eq : x = pa := m.toPerm.injective (Subtype.ext (h.trans hma.symm))
          exact hxC.2.1 (congrArg Subtype.val hx_eq)
        · intro h
          have hx_eq : x = ⟨b, hbU⟩ := m.toPerm.injective (Subtype.ext (h.trans hmb.symm))
          exact hxC.1 (congrArg Subtype.val hx_eq))
    let mBC : PerfectMatching (B ∪ C : Finset α) := mPair.unionDisj hdisj mC
    have hm_eq : m = mBC.congr eU.toEquiv := by
      have hma : (m.toPerm pa).1 = b := (Finset.mem_filter.mp hm).2
      ext x
      have heval : (eU.toEquiv.symm x).1 = x.1 := rfl
      have hcongr : ((mBC.congr eU.toEquiv).toPerm x).1 = (mBC.toPerm (eU.toEquiv.symm x)).1 := rfl
      rw [hcongr]
      by_cases hxB : x.1 ∈ B
      · have hval : (mBC.toPerm (eU.toEquiv.symm x)).1 = (mPair.toPerm ⟨x.1, hxB⟩).1 := by
          change (if h : (eU.toEquiv.symm x).1 ∈ B then _ else _ : (B ∪ C : Finset α)).1 = _
          simp only [heval, dite_eq_left hxB]
        rw [hval]
        have hx' : x.1 = a ∨ x.1 = b := by simpa [B] using hxB
        rcases hx' with hx1 | hx2
        · have hxpa : x = pa := Subtype.ext hx1
          subst hxpa
          have hsub : (⟨a, hxB⟩ : B) = ⟨a, by simp [B]⟩ := rfl
          rw [hsub]
          change (m.toPerm pa).1 =
            (Equiv.swap (⟨a, by simp [B]⟩ : B) ⟨b, by simp [B]⟩ ⟨a, by simp [B]⟩).1
          rw [Equiv.swap_apply_left, hma]
        · have h1 : m.toPerm pa = x := Subtype.ext (hma.trans hx2.symm)
          have h2 : m.toPerm x = pa := m.apply_eq_iff.mp h1
          have hsub : (⟨x.1, hxB⟩ : B) = ⟨b, by simp [B]⟩ := Subtype.ext hx2
          rw [h2, hsub]
          change a = (Equiv.swap (⟨a, by simp [B]⟩ : B) ⟨b, by simp [B]⟩ ⟨b, by simp [B]⟩).1
          rw [Equiv.swap_apply_right]
      · have hxC : x.1 ∈ C := (Finset.mem_union.mp (eU.toEquiv.symm x).2).resolve_left hxB
        have hval : (mBC.toPerm (eU.toEquiv.symm x)).1 = (mC.toPerm ⟨x.1, hxC⟩).1 := by
          change (if h : (eU.toEquiv.symm x).1 ∈ B then _ else _ : (B ∪ C : Finset α)).1 = _
          simp only [heval, dite_eq_right hxB]
        rw [hval]
        rfl
    have hov_eq : m.overlapCount = mBC.overlapCount := by
      rw [hm_eq, mBC.overlapCount_congr eU]
    have hwt_eq : m.weight (M.submatrix Subtype.val Subtype.val) =
        mBC.weight (M.submatrix Subtype.val Subtype.val) := by
      rw [hm_eq, mBC.weight_congr eU]
      rfl
    have hfilt : C.filter (fun x ↦ a < x ∧ x < b) = U.filter (fun x ↦ a < x ∧ x < b) := by
      ext x
      simp only [C, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, _, hx⟩, h⟩; exact ⟨hx, h⟩
      · rintro ⟨hx, h1, h2⟩; exact ⟨⟨h2.ne, h1.ne', hx⟩, h1, h2⟩
    have haC : a ∉ C := by simp [C]
    have hbC : b ∉ C := by simp [C]
    have hmod := crossOverlapCount_pair_mod_two hab haC hbC mPair mC
    rw [hfilt] at hmod
    have hsign_cross : (-1 : R) ^ crossOverlapCount mPair mC =
        (-1 : R) ^ (U.filter fun x ↦ a < x ∧ x < b).card :=
      neg_one_pow_eq_of_modEq hmod
    have hsign_m : m.sign R =
        (-1 : R) ^ (U.filter fun x ↦ a < x ∧ x < b).card * mC.sign R := by
      unfold PerfectMatching.sign
      rw [hov_eq, mPair.overlapCount_unionDisj hdisj mC, hmPair_ov, zero_add, pow_add,
        hsign_cross, mul_comm]
    have hwt_m : m.weight (M.submatrix Subtype.val Subtype.val) =
        M a b * mC.weight (M.submatrix Subtype.val Subtype.val) := by
      rw [hwt_eq, mPair.weight_unionDisj hdisj M mC, hmPair_wt]
    rw [hsign_m, hwt_m]
    ring

/-- The Pfaffian of the all-`1` strictly upper-triangular alternating matrix on `U` is `1` if
`U.card` is even and `0` if `U.card` is odd. -/
theorem pfaffianSubmatrix_allOnesAlt {α R : Type*} [LinearOrder α] [CommRing R] (U : Finset α) :
    pfaffianSubmatrix (allOnesAlt α R) U = if Even U.card then 1 else 0 := by
  induction hn : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [Finset.card_eq_zero.mp hn]
      simp
    · by_cases heven : Even n
      · rw [ite_eq_left heven]
        have hU : U.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero (hn.symm ▸ hn0))
        rw [pfaffianSubmatrix_eq_sum_min _ hU]
        set a := U.min' hU
        have hterms : ∀ b ∈ U.erase a,
            (-1 : R) ^ (U.filter fun x ↦ a < x ∧ x < b).card *
              allOnesAlt α R a b * pfaffianSubmatrix (allOnesAlt α R) ((U.erase a).erase b) =
            (-1 : R) ^ ((U.erase a).filter fun x ↦ x < b).card := by
          intro b hb
          have haU : a ∈ U := Finset.min'_mem U hU
          have hab : a < b := lt_of_le_of_ne (Finset.min'_le U b (Finset.mem_erase.mp hb).2)
            (Finset.mem_erase.mp hb).1.symm
          have hcard2 : ((U.erase a).erase b).card = n - 2 := by
            rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem haU, hn]
            omega
          have hlt2 : n - 2 < n := by omega
          have heven2 : Even (n - 2) := by
            rcases heven with ⟨k, hk⟩
            refine ⟨k - 1, ?_⟩
            omega
          rw [ih (n - 2) hlt2 ((U.erase a).erase b) hcard2, ite_eq_left (hcard2 ▸ heven2)]
          have hfilt : U.filter (fun x ↦ a < x ∧ x < b) =
              (U.erase a).filter (fun x ↦ x < b) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨hx, h1, h2⟩; exact ⟨⟨h1.ne', hx⟩, h2⟩
            · rintro ⟨⟨h1, hx⟩, h2⟩
              exact ⟨hx, lt_of_le_of_ne (Finset.min'_le U x hx) (Ne.symm h1), h2⟩
          rw [hfilt, allOnesAlt, ofUpperTri_apply_of_lt _ hab, mul_one, mul_one]
        rw [Finset.sum_congr rfl hterms]
        -- The exponents `((U.erase a).filter (· < b)).card` range bijectively over `0 .. n - 2`
        have hcard1 : (U.erase a).card = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.min'_mem U hU), hn]
        let f := (U.erase a).orderIsoOfFin hcard1
        rw [← Finset.sum_coe_sort (U.erase a), ← Equiv.sum_comp f.toEquiv]
        have hpos : ∀ i : Fin (n - 1),
            ((U.erase a).filter fun x ↦ x < (f i : α)).card = i.1 := by
          intro i
          have hbij : ((U.erase a).filter fun x ↦ x < (f i : α)).card =
              (Finset.univ.filter fun j : Fin (n - 1) ↦ j < i).card := by
            refine Finset.card_bij
              (fun x hx ↦ f.symm ⟨x, (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
            · intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              have hlt' : (⟨x, hx.1⟩ : (U.erase a : Finset α)) < f i := hx.2
              have hlt'' : f (f.symm ⟨x, hx.1⟩) < f i := by simpa using hlt'
              exact f.lt_iff_lt.mp hlt''
            · intro x₁ hx₁ x₂ hx₂ h
              have := f.symm.injective h
              exact congrArg Subtype.val this
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine ⟨(f j).1, Finset.mem_filter.mpr ⟨(f j).2, f.lt_iff_lt.mpr hj⟩, by simp⟩
          rw [hbij]
          have : (Finset.univ.filter fun j : Fin (n - 1) ↦ j < i) = Finset.Iio i := by
            ext j; simp
          rw [this, Fin.card_Iio]
        simp_rw [OrderIso.coe_toEquiv, hpos]
        -- Alternating sum of `(-1)^i` for `i = 0 .. 2m` equals `1`
        rcases heven with ⟨k, hk⟩
        have hkpos : 1 ≤ k := by omega
        have hnm : n - 1 = 2 * (k - 1) + 1 := by omega
        have halt : ∀ m : ℕ, ∑ i : Fin (2 * m + 1), (-1 : R) ^ (i : ℕ) = 1 := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by omega,
              Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            rw [ihm]
            have h1 : (-1 : R) ^ (2 * m + 1) = -1 := by
              rw [pow_add, pow_mul]; simp
            have h2 : (-1 : R) ^ (2 * m + 2) = 1 := by
              rw [show 2 * m + 2 = 2 * (m + 1) from by omega, pow_mul]; simp
            rw [h1, h2]
            ring
        have hsum_cast : ∀ {a b : ℕ} (h : a = b),
            (∑ i : Fin a, (-1 : R) ^ (i : ℕ)) = ∑ i : Fin b, (-1 : R) ^ (i : ℕ) := by
          rintro a _ rfl; rfl
        rw [hsum_cast hnm, halt]
      · rw [ite_eq_right heven]
        exact pfaffianSubmatrix_eq_zero_of_odd (hn ▸ Nat.not_even_iff_odd.mp heven) _


end CslibFrontier.Foundations.LinearAlgebra
