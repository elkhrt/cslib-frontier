/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Matrix Immanants, Irreducibility, Projections, and Generalized Laplace Expansion

This module develops general algebraic properties of matrix immanants over commutative rings and
fields, unifying the determinant and the permanent for arbitrary functions
`χ : Equiv.Perm (Fin n) → R`, together with generalized Laplace expansion of determinants along
arbitrary row partitions.

## Main definitions

* `CslibFrontier.Matrix.immanant`: the immanant `∑ σ, χ σ * ∏ i, M i (σ i)`.
* `CslibFrontier.Matrix.immanantMinor`: the `(i₀, j₀)`-th immanant minor
  `∑ σ with σ i₀ = j₀, χ σ * ∏ k ≠ i₀, M k (σ k)`.
* `CslibFrontier.Matrix.genericMatrix`: the symbolic `n × n` matrix of indeterminates `X (i, j)`.
* `CslibFrontier.Matrix.principalMinor`: the principal minor obtained by deleting rows and columns
  in a finite index set `B`.
* `CslibFrontier.Matrix.laplaceBasePerm`: canonical permutation sending the first `s` indices in
  order to an `s`-element subset `U` and the remaining `t` indices to `Uᶜ`.

## Main results

* `CslibFrontier.Matrix.immanant_sign_eq_det` and `CslibFrontier.Matrix.immanant_one_eq_permanent`:
  specialization to the determinant and the permanent.
* `CslibFrontier.Matrix.immanant_eq_sum_row`, `CslibFrontier.Matrix.immanant_submatrix_perm`, and
  `CslibFrontier.Matrix.immanant_upperTriangular`: row expansion, row/column permutation reindexing,
  and upper-triangular evaluation.
* `CslibFrontier.Matrix.immanant_ne_zero_of_corrupted_lt`: over an integral domain, replacing
  strictly fewer than `n` entries of the symbolic `n × n` matrix by arbitrary polynomials cannot
  annihilate any nowhere-zero immanant.
* `CslibFrontier.Matrix.immanantMinor_eq_immanant_submatrix` and
  `CslibFrontier.Matrix.immanantMinor_sign_eq_principalMinor`: submatrix reduction of immanant
  minors and equality with principal minors for the sign character.
* `CslibFrontier.Matrix.irreducible_immanant`: for every `n ≥ 1`, every field `F`, and every
  nowhere-zero `χ : Equiv.Perm (Fin n) → F`, the symbolic immanant is irreducible in
  `MvPolynomial (Fin n × Fin n) F`.
* `CslibFrontier.Matrix.det_eq_sum_submatrix_mul_compl`: generalized Laplace expansion of an
  `(s + t) × (s + t)` determinant over all `s`-element column subsets.
-/

public section

namespace CslibFrontier.Matrix

open Finset MvPolynomial Function

/-- The immanant of an `n × n` matrix `M` with respect to `χ : Equiv.Perm (Fin n) → R`. -/
@[expose] def immanant {R : Type*} [CommRing R] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → R) (M : Matrix (Fin n) (Fin n) R) : R :=
  ∑ σ : Equiv.Perm (Fin n), χ σ * ∏ i : Fin n, M i (σ i)

/-- The immanant with the sign character equals the determinant. -/
theorem immanant_sign_eq_det {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    immanant (fun σ ↦ (Equiv.Perm.sign σ : R)) M = M.det := by
  rw [immanant, Matrix.det_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ ↦ ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Units.smul_def, zsmul_eq_mul]
  congr 1
  refine Fintype.prod_equiv σ _ _ fun i ↦ ?_
  simp

/-- The immanant with the constant `1` character equals the permanent. -/
theorem immanant_one_eq_permanent {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    immanant (fun _ ↦ (1 : R)) M = M.permanent := by
  rw [immanant, Matrix.permanent]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ ↦ ?_
  rw [one_mul]
  refine Fintype.prod_equiv σ _ _ fun i ↦ ?_
  simp

/-- Ring homomorphisms commute with `immanant`. -/
theorem map_immanant {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (χ : Equiv.Perm (Fin n) → R) (M : Matrix (Fin n) (Fin n) R) :
    φ (immanant χ M) = immanant (φ ∘ χ) (M.map φ) := by
  simp [immanant, map_sum, map_mul, map_prod]

/-- The `(i₀, j₀)`-th minor of `immanant χ M`. -/
@[expose] def immanantMinor {R : Type*} [CommRing R] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → R) (M : Matrix (Fin n) (Fin n) R) (i₀ j₀ : Fin n) : R :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) ↦ σ i₀ = j₀),
    χ σ * ∏ k ∈ Finset.univ.erase i₀, M k (σ k)

/-- The generic `n × n` symbolic matrix whose `(i, j)` entry is `X (i, j)`. -/
@[expose] noncomputable def genericMatrix (F : Type*) [CommSemiring F] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) F) :=
  Matrix.of fun i j ↦ X (i, j)

/-- The principal minor of `M` obtained by deleting the pivot rows and columns in `B`. -/
@[expose] noncomputable def principalMinor {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (B : Finset (Fin n)) : R :=
  (M.submatrix (Subtype.val : {i : Fin n // i ∉ B} → Fin n)
    (Subtype.val : {i : Fin n // i ∉ B} → Fin n)).det

/-- Row expansion of `immanant χ M` along any fixed row `i₀`. -/
theorem immanant_eq_sum_row {R : Type*} [CommRing R] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → R) (M : Matrix (Fin n) (Fin n) R) (i₀ : Fin n) :
    immanant χ M = ∑ j : Fin n, M i₀ j * immanantMinor χ M i₀ j := by
  classical
  rw [immanant]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := fun σ : Equiv.Perm (Fin n) ↦ σ i₀) (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [immanantMinor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  have hσj : σ i₀ = j := (Finset.mem_filter.mp hσ).2
  rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ M k (σ k)) (Finset.mem_univ i₀), hσj]
  ring

/-- Permuting rows by `σr` and columns by `σc` reindexes the immanant character by
`τ ↦ χ (σc⁻¹ * τ * σr)`. -/
theorem immanant_submatrix_perm {R : Type*} [CommRing R] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → R) (M : Matrix (Fin n) (Fin n) R)
    (σr σc : Equiv.Perm (Fin n)) :
    immanant χ (M.submatrix σr σc) = immanant (fun τ ↦ χ (σc⁻¹ * τ * σr)) M := by
  rw [immanant, immanant]
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := {
    toFun := fun ρ ↦ σc * ρ * σr⁻¹
    invFun := fun τ ↦ σc⁻¹ * τ * σr
    left_inv := fun ρ ↦ by group
    right_inv := fun τ ↦ by group
  }
  refine Fintype.sum_equiv e _ _ fun ρ ↦ ?_
  have he_symm : σc⁻¹ * e ρ * σr = ρ := by
    simp only [e, Equiv.coe_fn_mk]; group
  rw [he_symm]
  congr 1
  refine Fintype.prod_equiv σr _ _ fun i ↦ ?_
  simp only [Matrix.submatrix_apply, e, Equiv.coe_fn_mk, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- The immanant of an upper-triangular matrix equals `χ 1 * ∏ i, M i i`. -/
theorem immanant_upperTriangular {R : Type*} [CommRing R] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → R) (M : Matrix (Fin n) (Fin n) R)
    (hupper : ∀ i j : Fin n, j < i → M i j = 0) :
    immanant χ M = χ 1 * ∏ i : Fin n, M i i := by
  classical
  rw [immanant, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp
  · intro σ _ hσ1
    have hex_lt : ∃ i : Fin n, σ i < i := by
      let moved : Finset (Fin n) := Finset.univ.filter fun i ↦ σ i ≠ i
      have hne : moved.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        apply hσ1
        refine Equiv.ext fun i ↦ ?_
        by_contra h
        have hi : i ∈ moved := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
        rw [hemp] at hi
        exact Finset.notMem_empty i hi
      let iMax := moved.max' hne
      have hiMax_mem : iMax ∈ moved := Finset.max'_mem moved hne
      have hiMax_ne : σ iMax ≠ iMax := (Finset.mem_filter.mp hiMax_mem).2
      refine ⟨iMax, lt_of_le_of_ne ?_ hiMax_ne⟩
      by_contra hgt
      push Not at hgt
      have hnot_moved : σ iMax ∉ moved := fun hm ↦
        not_lt_of_ge (Finset.le_max' moved (σ iMax) hm) hgt
      have hfix : σ (σ iMax) = σ iMax := by
        by_contra h
        exact hnot_moved (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact hiMax_ne (σ.injective hfix)
    obtain ⟨i, hi⟩ := hex_lt
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hupper i (σ i) hi), mul_zero]
  · intro h1; exact absurd (Finset.mem_univ 1) h1

/-- Any strictly fewer than `n` marked positions in an `n × n` grid can be moved strictly above
the main diagonal by permuting rows and columns. -/
theorem exists_perm_corrupted_above_diag :
    ∀ {n : ℕ} (S : Finset (Fin n × Fin n)), S.card < n →
      ∃ σr σc : Equiv.Perm (Fin n), ∀ p ∈ S, (σr.symm p.1 : ℕ) < (σc.symm p.2 : ℕ) := by
  intro n
  induction n with
  | zero =>
    intro S hS; omega
  | succ n ih =>
    intro S hS
    classical
    by_cases hSemp : S = ∅
    · subst hSemp
      exact ⟨1, 1, fun _ hp ↦ (Finset.notMem_empty _ hp).elim⟩
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSemp
      have hex_col : ∃ j₀ : Fin (n + 1), ∀ i : Fin (n + 1), (i, j₀) ∉ S := by
        have hlt : (S.image Prod.snd).card < (Finset.univ : Finset (Fin (n + 1))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact Finset.card_image_le.trans_lt hS
        obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        exact ⟨j₀, fun i hi ↦ hj₀ (Finset.mem_image.mpr ⟨(i, j₀), hi, rfl⟩)⟩
      obtain ⟨j₀, hj₀_free⟩ := hex_col
      obtain ⟨⟨i₀, j₁⟩, hp₀⟩ := hSne
      let sr : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i₀
      let sc : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j₀
      let S' : Finset (Fin n × Fin n) :=
        Finset.univ.filter fun q ↦ (sr q.1.succ, sc q.2.succ) ∈ S
      have hS'_card : S'.card < n := by
        have hcard_le : S'.card ≤ (S.erase (i₀, j₁)).card := by
          refine Finset.card_le_card_of_injOn (fun q ↦ (sr q.1.succ, sc q.2.succ)) ?_ ?_
          · intro q hq
            have hmem : (sr q.1.succ, sc q.2.succ) ∈ S := (Finset.mem_filter.mp hq).2
            refine Finset.mem_erase.mpr ⟨?_, hmem⟩
            intro heq
            have h1 : sr q.1.succ = i₀ := (Prod.ext_iff.mp heq).1
            have h2 : sr (0 : Fin (n + 1)) = i₀ := Equiv.swap_apply_left 0 i₀
            exact Fin.succ_ne_zero q.1 (sr.injective (h1.trans h2.symm))
          · intro q₁ _ q₂ _ heq
            rcases Prod.ext_iff.mp heq with ⟨h1, h2⟩
            exact Prod.ext (Fin.succ_injective _ (sr.injective h1))
              (Fin.succ_injective _ (sc.injective h2))
        have herase : (S.erase (i₀, j₁)).card = S.card - 1 := Finset.card_erase_of_mem hp₀
        have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨(i₀, j₁), hp₀⟩
        omega
      obtain ⟨τr, τc, hτ⟩ := ih S' hS'_card
      let lift (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) := {
        toFun := Fin.cases 0 (fun k ↦ (τ k).succ)
        invFun := Fin.cases 0 (fun k ↦ (τ.symm k).succ)
        left_inv := fun x ↦ by cases x using Fin.cases <;> simp
        right_inv := fun x ↦ by cases x using Fin.cases <;> simp
      }
      refine ⟨sr * lift τr, sc * lift τc, fun p hp ↦ ?_⟩
      have hp2_ne : p.2 ≠ j₀ := fun h ↦ hj₀_free p.1 (h ▸ hp)
      have hsc_ne : sc.symm p.2 ≠ 0 := by
        intro h0
        apply hp2_ne
        have : p.2 = sc 0 := (Equiv.symm_apply_eq sc).mp h0
        simpa [sc] using this
      obtain ⟨b, hb⟩ := Fin.exists_succ_eq_of_ne_zero hsc_ne
      have hcol_val : ((sc * lift τc).symm p.2 : ℕ) = (τc.symm b : ℕ) + 1 := by
        change ((lift τc).symm (sc.symm p.2) : ℕ) = (τc.symm b : ℕ) + 1
        rw [← hb]
        simp [lift]
      by_cases hp1 : p.1 = i₀
      · have hsr0 : sr.symm p.1 = 0 := by simp [sr, hp1]
        have hrow_val : ((sr * lift τr).symm p.1 : ℕ) = 0 := by
          change ((lift τr).symm (sr.symm p.1) : ℕ) = 0
          rw [hsr0]; simp [lift]
        omega
      · have hsr_ne : sr.symm p.1 ≠ 0 := by
          intro h0
          apply hp1
          have : p.1 = sr 0 := (Equiv.symm_apply_eq sr).mp h0
          simpa [sr] using this
        obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero hsr_ne
        have hrow_val : ((sr * lift τr).symm p.1 : ℕ) = (τr.symm a : ℕ) + 1 := by
          change ((lift τr).symm (sr.symm p.1) : ℕ) = (τr.symm a : ℕ) + 1
          rw [← ha]
          simp [lift]
        have hab : (a, b) ∈ S' := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have h1 : sr a.succ = p.1 := by rw [ha, Equiv.apply_symm_apply]
          have h2 : sc b.succ = p.2 := by rw [hb, Equiv.apply_symm_apply]
          rw [h1, h2]; exact hp
        have hlt : (τr.symm a : ℕ) < (τc.symm b : ℕ) := hτ (a, b) hab
        rw [hrow_val, hcol_val]
        omega

/-- Over an integral domain `F`, for any nowhere-zero `χ : Equiv.Perm (Fin n) → F`, if an
`n × n` polynomial matrix agrees with distinct indeterminates outside strictly fewer than `n`
entries, then its immanant is nonzero. -/
theorem immanant_ne_zero_of_corrupted_lt {F σ : Type*} [CommRing F] [IsDomain F] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → F) (hχ : ∀ τ, χ τ ≠ 0)
    (emb : Fin n × Fin n ↪ σ)
    (corrupted : Finset (Fin n × Fin n)) (hcard : corrupted.card < n)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ F))
    (hfree : ∀ i j, (i, j) ∉ corrupted → M i j = X (emb (i, j))) :
    immanant (C ∘ χ) M ≠ 0 := by
  classical
  obtain ⟨σr, σc, habove⟩ := exists_perm_corrupted_above_diag corrupted hcard
  let N := M.submatrix σr σc
  have hN_free : ∀ i j : Fin n, j ≤ i → N i j = X (emb (σr i, σc j)) := by
    intro i j hji
    refine hfree (σr i) (σc j) fun hmem ↦ ?_
    have hlt := habove (σr i, σc j) hmem
    simp only [Equiv.symm_apply_apply] at hlt
    exact not_lt_of_ge hji hlt
  let belowSet : Finset σ :=
    (Finset.univ.filter fun q : Fin n × Fin n ↦ q.2 < q.1).image fun q ↦ emb (σr q.1, σc q.2)
  let φ : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
    aeval fun v ↦ if v ∈ belowSet then 0 else X v
  have hbelow_iff : ∀ i j : Fin n, emb (σr i, σc j) ∈ belowSet ↔ j < i := by
    intro i j
    simp only [belowSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a, b⟩, hba, heq⟩
      have hpair := emb.injective heq
      rcases Prod.ext_iff.mp hpair with ⟨h1, h2⟩
      rw [← σr.injective h1, ← σc.injective h2]
      exact hba
    · intro hji
      exact ⟨(i, j), hji, rfl⟩
  let χ' : Equiv.Perm (Fin n) → F := fun τ ↦ χ (σc * τ * σr⁻¹)
  have hM_eq_N : immanant (C ∘ χ) M = immanant (C ∘ χ') N := by
    rw [immanant_submatrix_perm]
    congr 1
    ext τ
    simp only [comp_apply, χ']
    congr 1; group
  intro h0
  have hφ0 : φ.toRingHom (immanant (C ∘ χ') N) = 0 := by
    change φ (immanant (C ∘ χ') N) = 0
    rw [← hM_eq_N, h0, map_zero]
  rw [map_immanant] at hφ0
  have hcomp_C : (φ.toRingHom ∘ (C ∘ χ')) = (C ∘ χ') := by
    ext τ; simp [φ]
  rw [hcomp_C] at hφ0
  have hupper : ∀ i j : Fin n, j < i → (N.map φ.toRingHom) i j = 0 := by
    intro i j hji
    simp only [Matrix.map_apply, hN_free i j (le_of_lt hji)]
    change φ (X (emb (σr i, σc j))) = 0
    simp only [φ, aeval_X, (hbelow_iff i j).mpr hji, ↓reduceIte]
  rw [immanant_upperTriangular _ _ hupper] at hφ0
  have hdiag : ∀ i : Fin n, (N.map φ.toRingHom) i i = X (emb (σr i, σc i)) := fun i ↦ by
    simp only [Matrix.map_apply, hN_free i i le_rfl]
    change φ (X (emb (σr i, σc i))) = X (emb (σr i, σc i))
    have hnot : emb (σr i, σc i) ∉ belowSet := mt (hbelow_iff i i).mp (lt_irrefl i)
    simp only [φ, aeval_X, hnot, ↓reduceIte]
  simp_rw [hdiag] at hφ0
  have hne : (C (χ' 1) : MvPolynomial σ F) * ∏ i : Fin n, X (emb (σr i, σc i)) ≠ 0 :=
    mul_ne_zero (by rw [ne_eq, C_eq_zero]; exact hχ _)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_ne_zero _)
  exact hne hφ0

/-- The symbolic immanant of `genericMatrix F n` is nonzero over any integral domain for every
nowhere-zero character `χ`. -/
theorem immanant_genericMatrix_ne_zero {F : Type*} [CommRing F] [IsDomain F] {n : ℕ}
    (χ : Equiv.Perm (Fin n) → F) (hχ : ∀ τ, χ τ ≠ 0) :
    immanant (C ∘ χ) (genericMatrix F n) ≠ 0 := by
  cases n with
  | zero =>
    rw [immanant_upperTriangular _ _ (fun i ↦ Fin.elim0 i)]
    simp [hχ]
  | succ m =>
    exact immanant_ne_zero_of_corrupted_lt χ hχ (Function.Embedding.refl _) ∅
      (by simp) (genericMatrix F (m + 1)) (fun _ _ _ ↦ rfl)

/-- Lift `τ : Equiv.Perm (Fin n)` to `Equiv.Perm (Fin (n + 1))` fixing `0`. -/
private def liftPermZero {n : ℕ} (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun k ↦ (τ k).succ)
  invFun := Fin.cases 0 (fun k ↦ (τ.symm k).succ)
  left_inv x := by cases x using Fin.cases <;> simp
  right_inv x := by cases x using Fin.cases <;> simp

/-- Lift `τ : Equiv.Perm (Fin n)` to `Equiv.Perm (Fin (n + 1))` sending `i₀ ↦ j₀`. -/
def liftPermAt {n : ℕ} (i₀ j₀ : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap 0 j₀ * liftPermZero τ * Equiv.swap 0 i₀

private theorem sign_liftPermZero {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (liftPermZero τ) = Equiv.Perm.sign τ := by
  induction τ using Equiv.Perm.swap_induction_on with
  | one =>
    have h1 : liftPermZero (1 : Equiv.Perm (Fin n)) = 1 := by
      ext x; cases x using Fin.cases <;> simp [liftPermZero]
    rw [h1, map_one, map_one]
  | swap_mul f x y hxy ih =>
    have hcomp : liftPermZero (Equiv.swap x y * f) =
        Equiv.swap x.succ y.succ * liftPermZero f := by
      ext z
      cases z using Fin.cases with
      | zero =>
        simp [liftPermZero, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero x).symm
          (Fin.succ_ne_zero y).symm]
      | succ k =>
        simp only [liftPermZero, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, Fin.cases_succ]
        by_cases h1 : f k = x
        · rw [h1, Equiv.swap_apply_left, Equiv.swap_apply_left]
        · by_cases h2 : f k = y
          · rw [h2, Equiv.swap_apply_right, Equiv.swap_apply_right]
          · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
              Equiv.swap_apply_of_ne_of_ne (fun h ↦ h1 (Fin.succ_injective _ h))
                (fun h ↦ h2 (Fin.succ_injective _ h))]
    rw [hcomp, map_mul, map_mul, Equiv.Perm.sign_swap hxy,
      Equiv.Perm.sign_swap (fun h ↦ hxy (Fin.succ_injective _ h)), ih]

/-- Every `(i₀, j₀)`-th immanant minor of an `(n + 1) × (n + 1)` matrix equals the `n × n`
immanant of the complementary submatrix with character `τ ↦ χ (liftPermAt i₀ j₀ τ)`. -/
theorem immanantMinor_eq_immanant_submatrix {R : Type*} [CommRing R] {n : ℕ}
    (χ : Equiv.Perm (Fin (n + 1)) → R) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (i₀ j₀ : Fin (n + 1)) :
    immanantMinor χ M i₀ j₀ =
      immanant (fun τ ↦ χ (liftPermAt i₀ j₀ τ))
        (M.submatrix (fun k : Fin n ↦ Equiv.swap 0 i₀ k.succ)
          (fun k : Fin n ↦ Equiv.swap 0 j₀ k.succ)) := by
  classical
  rw [immanantMinor, immanant]
  refine Finset.sum_bij (fun σ hσ ↦ (by
    let ρ := Equiv.swap 0 j₀ * σ * Equiv.swap 0 i₀
    have hρ0 : ρ 0 = 0 := by
      have hσj : σ i₀ = j₀ := (Finset.mem_filter.mp hσ).2
      simp [ρ, hσj]
    have hρinv0 : ρ.symm 0 = 0 := by
      have := congrArg ρ.symm hρ0
      simpa using this.symm
    exact {
      toFun := fun k ↦ (ρ k.succ).pred (fun h0 ↦
        Fin.succ_ne_zero k (ρ.injective (h0.trans hρ0.symm)))
      invFun := fun k ↦ (ρ.symm k.succ).pred (fun h0 ↦
        Fin.succ_ne_zero k (ρ.symm.injective (h0.trans hρinv0.symm)))
      left_inv := fun k ↦ by
        simp only [Fin.succ_pred, Equiv.symm_apply_apply, Fin.pred_succ]
      right_inv := fun k ↦ by
        simp only [Fin.succ_pred, Equiv.apply_symm_apply, Fin.pred_succ]
    } : Equiv.Perm (Fin n))) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro σ₁ hσ₁ σ₂ hσ₂ heq
    have hσ₁j : σ₁ i₀ = j₀ := (Finset.mem_filter.mp hσ₁).2
    have hσ₂j : σ₂ i₀ = j₀ := (Finset.mem_filter.mp hσ₂).2
    have hρeq : Equiv.swap 0 j₀ * σ₁ * Equiv.swap 0 i₀ =
        Equiv.swap 0 j₀ * σ₂ * Equiv.swap 0 i₀ := by
      ext x
      cases x using Fin.cases with
      | zero => simp [hσ₁j, hσ₂j]
      | succ k =>
        have hk := congrArg (fun τ : Equiv.Perm (Fin n) ↦ (τ k).succ) heq
        simpa [Fin.succ_pred] using congrArg Fin.val hk
    have h1 := congrArg (fun ρ ↦ Equiv.swap 0 j₀ * ρ * Equiv.swap 0 i₀) hρeq
    simpa [mul_assoc] using h1
  · intro τ _
    refine ⟨liftPermAt i₀ j₀ τ, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [liftPermAt, liftPermZero]
    · ext k
      simp [liftPermAt, liftPermZero, mul_assoc]
  · intro σ hσ
    have hσj : σ i₀ = j₀ := (Finset.mem_filter.mp hσ).2
    have hlift : liftPermAt i₀ j₀
        (by
          let ρ := Equiv.swap 0 j₀ * σ * Equiv.swap 0 i₀
          have hρ0 : ρ 0 = 0 := by simp [ρ, hσj]
          have hρinv0 : ρ.symm 0 = 0 := by
            have := congrArg ρ.symm hρ0; simpa using this.symm
          exact {
            toFun := fun k ↦ (ρ k.succ).pred (fun h0 ↦
              Fin.succ_ne_zero k (ρ.injective (h0.trans hρ0.symm)))
            invFun := fun k ↦ (ρ.symm k.succ).pred (fun h0 ↦
              Fin.succ_ne_zero k (ρ.symm.injective (h0.trans hρinv0.symm)))
            left_inv := fun k ↦ by simp
            right_inv := fun k ↦ by simp
          } : Equiv.Perm (Fin n)) = σ := by
      have hmid : liftPermZero
          (by
            let ρ := Equiv.swap 0 j₀ * σ * Equiv.swap 0 i₀
            have hρ0 : ρ 0 = 0 := by simp [ρ, hσj]
            have hρinv0 : ρ.symm 0 = 0 := by
              have := congrArg ρ.symm hρ0; simpa using this.symm
            exact {
              toFun := fun k ↦ (ρ k.succ).pred (fun h0 ↦
                Fin.succ_ne_zero k (ρ.injective (h0.trans hρ0.symm)))
              invFun := fun k ↦ (ρ.symm k.succ).pred (fun h0 ↦
                Fin.succ_ne_zero k (ρ.symm.injective (h0.trans hρinv0.symm)))
              left_inv := fun k ↦ by simp
              right_inv := fun k ↦ by simp
            } : Equiv.Perm (Fin n)) = Equiv.swap 0 j₀ * σ * Equiv.swap 0 i₀ := by
        ext x
        cases x using Fin.cases with
        | zero => simp [liftPermZero, hσj]
        | succ k => simp [liftPermZero]
      rw [liftPermAt, hmid]
      ext x; simp [mul_assoc]
    rw [hlift]
    congr 1
    refine Finset.prod_bij (fun k hk ↦ (Equiv.swap 0 i₀ k).pred (fun h0 ↦ by
      have hk_ne : k ≠ i₀ := (Finset.mem_erase.mp hk).1
      apply hk_ne
      have := congrArg (Equiv.swap 0 i₀) h0
      simpa using this)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro k₁ hk₁ k₂ hk₂ heq
      have h1 := congrArg Fin.succ heq
      simp only [Fin.succ_pred] at h1
      exact (Equiv.swap 0 i₀).injective h1
    · intro k _
      refine ⟨Equiv.swap 0 i₀ k.succ, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, by simp⟩
      intro heq
      exact Fin.succ_ne_zero k
        ((Equiv.swap 0 i₀).injective (heq.trans (Equiv.swap_apply_left 0 i₀).symm))
    · intro k hk
      simp only [Matrix.submatrix_apply, Fin.succ_pred, Equiv.swap_apply_self]
      congr 1
      have h1 : (Equiv.swap 0 j₀) ((Equiv.swap 0 j₀ * σ * Equiv.swap 0 i₀)
          (Equiv.swap 0 i₀ k)) = σ k := by simp
      simp only [Equiv.coe_fn_mk, Fin.succ_pred]
      exact h1.symm

/-- For the sign character, the `(i₀, i₀)`-th immanant minor equals `principalMinor M {i₀}`. -/
theorem immanantMinor_sign_eq_principalMinor {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ : Fin (n + 1)) :
    immanantMinor (fun σ ↦ (Equiv.Perm.sign σ : R)) M i₀ i₀ = principalMinor M {i₀} := by
  classical
  rw [immanantMinor_eq_immanant_submatrix]
  have hχ_eq : (fun τ : Equiv.Perm (Fin n) ↦
      ((Equiv.Perm.sign (liftPermAt i₀ i₀ τ) : ℤˣ) : R)) =
      fun τ ↦ ((Equiv.Perm.sign τ : ℤˣ) : R) := by
    ext τ
    simp only [liftPermAt, map_mul, sign_liftPermZero]
    have hsq : Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i₀) *
        Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i₀) = 1 := by
      rw [← map_mul, Equiv.swap_mul_self, map_one]
    have : Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i₀) * Equiv.Perm.sign τ *
        Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i₀) = Equiv.Perm.sign τ := by
      rw [mul_comm _ (Equiv.Perm.sign τ), mul_assoc, hsq, mul_one]
    rw [this]
  rw [hχ_eq, immanant_sign_eq_det, principalMinor]
  let e : Fin n ≃ {i : Fin (n + 1) // i ∉ ({i₀} : Finset (Fin (n + 1)))} := {
    toFun := fun k ↦ ⟨Equiv.swap 0 i₀ k.succ, by
      simp only [Finset.mem_singleton]
      intro h
      exact Fin.succ_ne_zero k ((Equiv.swap 0 i₀).injective
        (h.trans (Equiv.swap_apply_left 0 i₀).symm))⟩
    invFun := fun x ↦ (Equiv.swap 0 i₀ x.1).pred (fun h0 ↦ by
      have hx : x.1 ≠ i₀ := Finset.notMem_singleton.mp x.2
      exact hx (by have := congrArg (Equiv.swap 0 i₀) h0; simpa using this))
    left_inv := fun k ↦ by simp
    right_inv := fun x ↦ by ext; simp
  }
  have hsub : M.submatrix (fun k : Fin n ↦ Equiv.swap 0 i₀ k.succ)
      (fun k : Fin n ↦ Equiv.swap 0 i₀ k.succ) =
      (M.submatrix (Subtype.val : {i : Fin (n + 1) // i ∉ ({i₀} : Finset (Fin (n + 1)))} → _)
        (Subtype.val : {i : Fin (n + 1) // i ∉ ({i₀} : Finset (Fin (n + 1)))} → _)).submatrix
        e e := by
    ext a b; rfl
  rw [hsub, Matrix.det_submatrix_equiv_self e]

private noncomputable def rowScaleHom (F : Type*) [CommSemiring F] {n : ℕ} (i₀ : Fin n) :
    MvPolynomial (Fin n × Fin n) F →ₐ[F] Polynomial (MvPolynomial (Fin n × Fin n) F) :=
  aeval fun p ↦ if p.1 = i₀ then Polynomial.C (X p) * Polynomial.X else Polynomial.C (X p)

private noncomputable def colScaleHom (F : Type*) [CommSemiring F] {n : ℕ} (j₀ : Fin n) :
    MvPolynomial (Fin n × Fin n) F →ₐ[F] Polynomial (MvPolynomial (Fin n × Fin n) F) :=
  aeval fun p ↦ if p.2 = j₀ then Polynomial.C (X p) * Polynomial.X else Polynomial.C (X p)

private theorem eval_one_rowScaleHom {F : Type*} [CommSemiring F] {n : ℕ} (i₀ : Fin n)
    (P : MvPolynomial (Fin n × Fin n) F) : (rowScaleHom F i₀ P).eval 1 = P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [rowScaleHom, aeval_C,
      IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n × Fin n) F),
      Polynomial.algebraMap_eq, Polynomial.eval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, Polynomial.eval_mul, hp]
    simp only [rowScaleHom, aeval_X]
    split_ifs <;> simp

private theorem eval_one_colScaleHom {F : Type*} [CommSemiring F] {n : ℕ} (j₀ : Fin n)
    (P : MvPolynomial (Fin n × Fin n) F) : (colScaleHom F j₀ P).eval 1 = P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [colScaleHom, aeval_C,
      IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n × Fin n) F),
      Polynomial.algebraMap_eq, Polynomial.eval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, Polynomial.eval_mul, hp]
    simp only [colScaleHom, aeval_X]
    split_ifs <;> simp

private theorem natDegree_rowScaleHom_eq_zero_iff {F : Type*} [CommRing F] {n : ℕ}
    (i₀ : Fin n) (P : MvPolynomial (Fin n × Fin n) F) :
    (rowScaleHom F i₀ P).natDegree = 0 ↔ ∀ j : Fin n, (i₀, j) ∉ P.vars := by
  classical
  have hexp : rowScaleHom F i₀ P =
      ∑ m ∈ P.support, Polynomial.C (monomial m (P.coeff m)) *
        Polynomial.X ^ (∑ j : Fin n, m (i₀, j)) := by
    conv_lhs => rw [P.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [monomial_eq, map_mul, map_finsuppProd]
    have hC : rowScaleHom F i₀ (C (P.coeff m)) = Polynomial.C (C (P.coeff m)) := by
      rw [rowScaleHom, aeval_C,
        IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n × Fin n) F),
        Polynomial.algebraMap_eq, algebraMap_eq]
    rw [hC]
    have hprod : (m.prod fun p e ↦ rowScaleHom F i₀ (X p ^ e)) =
        Polynomial.C (m.prod fun p e ↦ X p ^ e) *
          Polynomial.X ^ (∑ j : Fin n, m (i₀, j)) := by
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ by simp), Finsupp.prod_fintype _ _ (fun _ ↦ by simp)]
      have hterm : ∀ p : Fin n × Fin n,
          rowScaleHom F i₀ (X p ^ m p) =
          Polynomial.C (X p ^ m p) *
            Polynomial.X ^ (if p.1 = i₀ then m p else 0) := fun p ↦ by
        rw [map_pow]
        simp only [rowScaleHom, aeval_X]
        split_ifs <;> simp [mul_pow, map_pow]
      simp_rw [hterm, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
      congr 2
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [hprod, ← mul_assoc, ← map_mul, ← monomial_eq]
  have hcoeff : ∀ d : ℕ, (rowScaleHom F i₀ P).coeff d =
      ∑ m ∈ P.support.filter (fun m ↦ (∑ j : Fin n, m (i₀, j)) = d),
        monomial m (P.coeff m) := fun d ↦ by
    rw [hexp, ← Polynomial.lcoeff_apply, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
    by_cases h : (∑ j : Fin n, m (i₀, j)) = d
    · simp [h]
    · have h' : d ≠ ∑ j : Fin n, m (i₀, j) := Ne.symm h
      simp [h, h']
  constructor
  · intro h0 j hj
    rw [vars_def, Multiset.mem_toFinset, mem_degrees] at hj
    obtain ⟨m, hm_ne, hmj⟩ := hj
    have hm_supp : m ∈ P.support := mem_support_iff.mpr hm_ne
    have hpos : 0 < ∑ j' : Fin n, m (i₀, j') :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmj))
        (Finset.single_le_sum (f := fun j' ↦ m (i₀, j')) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ j))
    set d := ∑ j' : Fin n, m (i₀, j')
    have hcd_zero : (rowScaleHom F i₀ P).coeff d = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff d] at hcd_zero
    have hcm := congrArg (fun q : MvPolynomial (Fin n × Fin n) F ↦ q.coeff m) hcd_zero
    rw [coeff_sum, Finset.sum_eq_single m] at hcm
    · simp only [coeff_monomial, ↓reduceIte, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] at hcm
      exact hm_ne hcm
    · intro m' _ hm'ne; simp [coeff_monomial, hm'ne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_filter.mpr ⟨hm_supp, rfl⟩))
  · intro hnone
    have hdeg0 : ∀ m ∈ P.support, ∑ j : Fin n, m (i₀, j) = 0 := fun m hm ↦ by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_contra hne
      apply hnone j
      rw [vars_def, Multiset.mem_toFinset, mem_degrees]
      exact ⟨m, mem_support_iff.mp hm, Finsupp.mem_support_iff.mpr hne⟩
    have hCeq : rowScaleHom F i₀ P = Polynomial.C P := by
      rw [hexp]
      conv_rhs => rw [P.as_sum, map_sum]
      refine Finset.sum_congr rfl fun m hm ↦ by rw [hdeg0 m hm, pow_zero, mul_one]
    rw [hCeq, Polynomial.natDegree_C]

private theorem natDegree_colScaleHom_eq_zero_iff {F : Type*} [CommRing F] {n : ℕ}
    (j₀ : Fin n) (P : MvPolynomial (Fin n × Fin n) F) :
    (colScaleHom F j₀ P).natDegree = 0 ↔ ∀ i : Fin n, (i, j₀) ∉ P.vars := by
  classical
  have hexp : colScaleHom F j₀ P =
      ∑ m ∈ P.support, Polynomial.C (monomial m (P.coeff m)) *
        Polynomial.X ^ (∑ i : Fin n, m (i, j₀)) := by
    conv_lhs => rw [P.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [monomial_eq, map_mul, map_finsuppProd]
    have hC : colScaleHom F j₀ (C (P.coeff m)) = Polynomial.C (C (P.coeff m)) := by
      rw [colScaleHom, aeval_C,
        IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n × Fin n) F),
        Polynomial.algebraMap_eq, algebraMap_eq]
    rw [hC]
    have hprod : (m.prod fun p e ↦ colScaleHom F j₀ (X p ^ e)) =
        Polynomial.C (m.prod fun p e ↦ X p ^ e) *
          Polynomial.X ^ (∑ i : Fin n, m (i, j₀)) := by
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ by simp), Finsupp.prod_fintype _ _ (fun _ ↦ by simp)]
      have hterm : ∀ p : Fin n × Fin n,
          colScaleHom F j₀ (X p ^ m p) =
          Polynomial.C (X p ^ m p) *
            Polynomial.X ^ (if p.2 = j₀ then m p else 0) := fun p ↦ by
        rw [map_pow]
        simp only [colScaleHom, aeval_X]
        split_ifs <;> simp [mul_pow, map_pow]
      simp_rw [hterm, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
      congr 2
      rw [Fintype.sum_prod_type_right]
      rw [Finset.sum_eq_single j₀]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ j₀) h
    rw [hprod, ← mul_assoc, ← map_mul, ← monomial_eq]
  have hcoeff : ∀ d : ℕ, (colScaleHom F j₀ P).coeff d =
      ∑ m ∈ P.support.filter (fun m ↦ (∑ i : Fin n, m (i, j₀)) = d),
        monomial m (P.coeff m) := fun d ↦ by
    rw [hexp, ← Polynomial.lcoeff_apply, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
    by_cases h : (∑ i : Fin n, m (i, j₀)) = d
    · simp [h]
    · have h' : d ≠ ∑ i : Fin n, m (i, j₀) := Ne.symm h
      simp [h, h']
  constructor
  · intro h0 i hi
    rw [vars_def, Multiset.mem_toFinset, mem_degrees] at hi
    obtain ⟨m, hm_ne, hmi⟩ := hi
    have hm_supp : m ∈ P.support := mem_support_iff.mpr hm_ne
    have hpos : 0 < ∑ i' : Fin n, m (i', j₀) :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmi))
        (Finset.single_le_sum (f := fun i' ↦ m (i', j₀)) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ i))
    set d := ∑ i' : Fin n, m (i', j₀)
    have hcd_zero : (colScaleHom F j₀ P).coeff d = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff d] at hcd_zero
    have hcm := congrArg (fun q : MvPolynomial (Fin n × Fin n) F ↦ q.coeff m) hcd_zero
    rw [coeff_sum, Finset.sum_eq_single m] at hcm
    · simp only [coeff_monomial, ↓reduceIte, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] at hcm
      exact hm_ne hcm
    · intro m' _ hm'ne; simp [coeff_monomial, hm'ne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_filter.mpr ⟨hm_supp, rfl⟩))
  · intro hnone
    have hdeg0 : ∀ m ∈ P.support, ∑ i : Fin n, m (i, j₀) = 0 := fun m hm ↦ by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      by_contra hne
      apply hnone i
      rw [vars_def, Multiset.mem_toFinset, mem_degrees]
      exact ⟨m, mem_support_iff.mp hm, Finsupp.mem_support_iff.mpr hne⟩
    have hCeq : colScaleHom F j₀ P = Polynomial.C P := by
      rw [hexp]
      conv_rhs => rw [P.as_sum, map_sum]
      refine Finset.sum_congr rfl fun m hm ↦ by rw [hdeg0 m hm, pow_zero, mul_one]
    rw [hCeq, Polynomial.natDegree_C]

/-- For every `n ≥ 1`, every field `F`, and every nowhere-zero `χ : Equiv.Perm (Fin n) → F`,
the symbolic immanant `immanant (C ∘ χ) (genericMatrix F n)` is irreducible in
`MvPolynomial (Fin n × Fin n) F`. -/
theorem irreducible_immanant {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n)
    (χ : Equiv.Perm (Fin n) → F) (hχ : ∀ τ, χ τ ≠ 0) :
    Irreducible (immanant (C ∘ χ) (genericMatrix F n)) := by
  classical
  set P := immanant (C ∘ χ) (genericMatrix F n)
  have hP_ne : P ≠ 0 := immanant_genericMatrix_ne_zero χ hχ
  have hsum_eval : ∀ (f : Fin n → Fin n × Fin n →₀ ℕ) (p : Fin n × Fin n),
      (∑ a : Fin n, f a) p = ∑ a : Fin n, f a p := fun f p ↦
    map_sum (Finsupp.applyAddHom p : (Fin n × Fin n →₀ ℕ) →+ ℕ) f Finset.univ
  have hcoeff_perm : ∀ σ : Equiv.Perm (Fin n),
      P.coeff (∑ i : Fin n, Finsupp.single (i, σ i) 1) = χ σ := by
    intro σ
    rw [show P = ∑ τ : Equiv.Perm (Fin n),
        monomial (∑ i : Fin n, Finsupp.single (i, τ i) 1) (χ τ) by
      simp only [P, immanant, comp_apply, genericMatrix, Matrix.of_apply]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      have hprod : ∏ i : Fin n, (X (i, τ i) : MvPolynomial (Fin n × Fin n) F) =
          monomial (∑ i : Fin n, Finsupp.single (i, τ i) 1) 1 := by
        have h1 : ∀ s : Finset (Fin n),
            ∏ i ∈ s, (X (i, τ i) : MvPolynomial (Fin n × Fin n) F) =
            monomial (∑ i ∈ s, Finsupp.single (i, τ i) 1) 1 := fun s ↦ by
          induction s using Finset.induction_on with
          | empty => simp [monomial_zero']
          | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X, monomial_mul_monomial, one_mul]
        exact h1 Finset.univ
      rw [hprod, C_mul_monomial, mul_one]]
    rw [coeff_sum, Finset.sum_eq_single σ]
    · simp [coeff_monomial]
    · intro τ _ hτσ
      have hm_ne : (∑ i : Fin n, Finsupp.single (i, τ i) 1) ≠
          (∑ i : Fin n, Finsupp.single (i, σ i) 1) := by
        intro heq
        apply hτσ
        ext i
        have hi := congrArg (fun m : Fin n × Fin n →₀ ℕ ↦ m (i, τ i)) heq
        rw [hsum_eval, hsum_eval] at hi
        have hl : ∑ a : Fin n, (Finsupp.single (a, τ a) 1 : Fin n × Fin n →₀ ℕ) (i, τ i) = 1 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro a _ hai
            simp [hai]
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [hl] at hi
        have hr : ∑ a : Fin n, (Finsupp.single (a, σ a) 1 : Fin n × Fin n →₀ ℕ) (i, τ i) =
            if σ i = τ i then 1 else 0 := by
          rw [Finset.sum_eq_single i]
          · simp [Finsupp.single_apply]
          · intro a _ hai
            simp [hai]
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [hr] at hi
        by_cases h : σ i = τ i
        · exact congrArg Fin.val h.symm
        · simp [h] at hi
      simp [coeff_monomial, hm_ne]
    · intro h; exact absurd (Finset.mem_univ σ) h
  have hrow_P : ∀ i₀ : Fin n, rowScaleHom F i₀ P = Polynomial.C P * Polynomial.X := by
    intro i₀
    simp only [P, immanant, map_sum, map_mul, map_prod, comp_apply, genericMatrix, Matrix.of_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    have hC : rowScaleHom F i₀ (C (χ σ)) = Polynomial.C (C (χ σ)) := by
      rw [rowScaleHom, aeval_C,
        IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n × Fin n) F),
        Polynomial.algebraMap_eq, algebraMap_eq]
    rw [hC, mul_assoc]
    congr 1
    conv_rhs => rw [← map_prod]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ (fun i ↦ (X (i, σ i) : MvPolynomial _ F))
        (Finset.mem_univ i₀)]
    have h1 : rowScaleHom F i₀ (X (i₀, σ i₀)) = Polynomial.C (X (i₀, σ i₀)) * Polynomial.X := by
      simp [rowScaleHom]
    have h2 : ∏ i ∈ Finset.univ.erase i₀, rowScaleHom F i₀ (X (i, σ i)) =
        Polynomial.C (∏ i ∈ Finset.univ.erase i₀, X (i, σ i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      simp [rowScaleHom, hne]
    rw [h1, h2, map_mul]
    ring
  have hcol_P : ∀ j₀ : Fin n, colScaleHom F j₀ P = Polynomial.C P * Polynomial.X := by
    intro j₀
    simp only [P, immanant, map_sum, map_mul, map_prod, comp_apply, genericMatrix, Matrix.of_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    have hC : colScaleHom F j₀ (C (χ σ)) = Polynomial.C (C (χ σ)) := by
      rw [colScaleHom, aeval_C,
        IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n × Fin n) F),
        Polynomial.algebraMap_eq, algebraMap_eq]
    rw [hC, mul_assoc]
    congr 1
    let i₀ := σ.symm j₀
    conv_rhs => rw [← map_prod]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ (fun i ↦ (X (i, σ i) : MvPolynomial _ F))
        (Finset.mem_univ i₀)]
    have h1 : colScaleHom F j₀ (X (i₀, σ i₀)) = Polynomial.C (X (i₀, σ i₀)) * Polynomial.X := by
      simp [colScaleHom, i₀]
    have h2 : ∏ i ∈ Finset.univ.erase i₀, colScaleHom F j₀ (X (i, σ i)) =
        Polynomial.C (∏ i ∈ Finset.univ.erase i₀, X (i, σ i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hne : σ i ≠ j₀ := fun h ↦ (Finset.mem_erase.mp hi).1 (by simp [i₀, ← h])
      simp [colScaleHom, hne]
    rw [h1, h2, map_mul]
    ring
  have hnot_unit : ¬ IsUnit P := by
    intro hu
    obtain ⟨Q, hQ⟩ := isUnit_iff_exists_inv.mp hu
    have h1 : rowScaleHom F ⟨0, hn⟩ P * rowScaleHom F ⟨0, hn⟩ Q = 1 := by
      rw [← map_mul, hQ, map_one]
    have hPr_ne : rowScaleHom F ⟨0, hn⟩ P ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hQr_ne : rowScaleHom F ⟨0, hn⟩ Q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    have hdeg := Polynomial.natDegree_mul hPr_ne hQr_ne
    rw [h1, Polynomial.natDegree_one, hrow_P ⟨0, hn⟩, Polynomial.natDegree_C_mul_X _ hP_ne] at hdeg
    omega
  refine ⟨hnot_unit, fun A B hAB ↦ ?_⟩
  by_contra hneither
  push Not at hneither
  rcases hneither with ⟨hAnu, hBnu⟩
  have hAne : A ≠ 0 := fun h0 ↦ hP_ne (by rw [hAB, h0, zero_mul])
  have hBne : B ≠ 0 := fun h0 ↦ hP_ne (by rw [hAB, h0, mul_zero])
  have hA_var : A.vars.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdeg0 : A.totalDegree = 0 := by
      refine Nat.eq_zero_of_le_zero ?_
      rw [totalDegree]
      refine Finset.sup_le fun m hm ↦ ?_
      by_contra hpos
      have hne0 : m ≠ 0 := fun h0 ↦ by simp [h0] at hpos
      obtain ⟨p, hp⟩ := DFunLike.ne_iff.mp hne0
      have hpv : p ∈ A.vars :=
        (vars_def A).symm ▸ Multiset.mem_toFinset.mpr
          (mem_degrees.mpr ⟨m, mem_support_iff.mp hm, Finsupp.mem_support_iff.mpr hp⟩)
      rw [hemp] at hpv; exact Finset.notMem_empty _ hpv
    have hAC := totalDegree_eq_zero_iff_eq_C.mp hdeg0
    have hc0 : A.coeff 0 ≠ 0 := fun h ↦ hAne (by rw [hAC, h, map_zero])
    exact hAnu (hAC ▸ (IsUnit.mk0 (A.coeff 0) hc0).map C)
  have hB_var : B.vars.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdeg0 : B.totalDegree = 0 := by
      refine Nat.eq_zero_of_le_zero ?_
      rw [totalDegree]
      refine Finset.sup_le fun m hm ↦ ?_
      by_contra hpos
      have hne0 : m ≠ 0 := fun h0 ↦ by simp [h0] at hpos
      obtain ⟨p, hp⟩ := DFunLike.ne_iff.mp hne0
      have hpv : p ∈ B.vars :=
        (vars_def B).symm ▸ Multiset.mem_toFinset.mpr
          (mem_degrees.mpr ⟨m, mem_support_iff.mp hm, Finsupp.mem_support_iff.mpr hp⟩)
      rw [hemp] at hpv; exact Finset.notMem_empty _ hpv
    have hBC := totalDegree_eq_zero_iff_eq_C.mp hdeg0
    have hc0 : B.coeff 0 ≠ 0 := fun h ↦ hBne (by rw [hBC, h, map_zero])
    exact hBnu (hBC ▸ (IsUnit.mk0 (B.coeff 0) hc0).map C)
  obtain ⟨⟨i₁, j₁⟩, hAij⟩ := hA_var
  obtain ⟨⟨i₂, j₂⟩, hBij⟩ := hB_var
  have hrow_disj : ∀ i : Fin n, (∃ j, (i, j) ∈ A.vars) → ∀ j, (i, j) ∉ B.vars := by
    intro i ⟨j, hjA⟩
    have hAr_ne : rowScaleHom F i A ≠ 0 := fun h0 ↦ hAne (by
      have := congrArg (Polynomial.eval 1) h0
      rwa [eval_one_rowScaleHom, Polynomial.eval_zero] at this)
    have hBr_ne : rowScaleHom F i B ≠ 0 := fun h0 ↦ hBne (by
      have := congrArg (Polynomial.eval 1) h0
      rwa [eval_one_rowScaleHom, Polynomial.eval_zero] at this)
    have hdeg_sum : (rowScaleHom F i A).natDegree + (rowScaleHom F i B).natDegree = 1 := by
      rw [← Polynomial.natDegree_mul hAr_ne hBr_ne, ← map_mul, ← hAB, hrow_P i,
        Polynomial.natDegree_C_mul_X _ hP_ne]
    have hA_pos : 0 < (rowScaleHom F i A).natDegree := by
      by_contra h0
      exact (natDegree_rowScaleHom_eq_zero_iff i A).mp (by omega) j hjA
    exact (natDegree_rowScaleHom_eq_zero_iff i B).mp (by omega)
  have hcol_disj : ∀ j : Fin n, (∃ i, (i, j) ∈ B.vars) → ∀ i, (i, j) ∉ A.vars := by
    intro j ⟨i, hiB⟩
    have hAc_ne : colScaleHom F j A ≠ 0 := fun h0 ↦ hAne (by
      have := congrArg (Polynomial.eval 1) h0
      rwa [eval_one_colScaleHom, Polynomial.eval_zero] at this)
    have hBc_ne : colScaleHom F j B ≠ 0 := fun h0 ↦ hBne (by
      have := congrArg (Polynomial.eval 1) h0
      rwa [eval_one_colScaleHom, Polynomial.eval_zero] at this)
    have hdeg_sum : (colScaleHom F j A).natDegree + (colScaleHom F j B).natDegree = 1 := by
      rw [← Polynomial.natDegree_mul hAc_ne hBc_ne, ← map_mul, ← hAB, hcol_P j,
        Polynomial.natDegree_C_mul_X _ hP_ne]
    have hB_pos : 0 < (colScaleHom F j B).natDegree := by
      by_contra h0
      exact (natDegree_colScaleHom_eq_zero_iff j B).mp (by omega) i hiB
    exact (natDegree_colScaleHom_eq_zero_iff j A).mp (by omega)
  let σ : Equiv.Perm (Fin n) := Equiv.swap i₁ j₂
  let mσ : Fin n × Fin n →₀ ℕ := ∑ i : Fin n, Finsupp.single (i, σ i) 1
  have hmσ_supp : mσ ∈ (A * B).support := by
    rw [← hAB, mem_support_iff, hcoeff_perm σ]
    exact hχ σ
  obtain ⟨mA, hmA, mB, hmB, hadd⟩ := Finset.mem_add.mp (support_mul A B hmσ_supp)
  have hmσ_entry : mσ (i₁, j₂) = 1 := by
    rw [hsum_eval]
    rw [Finset.sum_eq_single i₁]
    · simp [σ]
    · intro a _ hai; simp [hai]
    · intro h; exact absurd (Finset.mem_univ i₁) h
  have hsum_entry : mA (i₁, j₂) + mB (i₁, j₂) = 1 := by
    have := congrArg (fun m : Fin n × Fin n →₀ ℕ ↦ m (i₁, j₂)) hadd
    simpa [hmσ_entry] using this
  rcases (by omega : 0 < mA (i₁, j₂) ∨ 0 < mB (i₁, j₂)) with hApos | hBpos
  · have hvA : (i₁, j₂) ∈ A.vars :=
      (vars_def A).symm ▸ Multiset.mem_toFinset.mpr
        (mem_degrees.mpr ⟨mA, mem_support_iff.mp hmA, Finsupp.mem_support_iff.mpr (by omega)⟩)
    exact hcol_disj j₂ ⟨i₂, hBij⟩ i₁ hvA
  · have hvB : (i₁, j₂) ∈ B.vars :=
      (vars_def B).symm ▸ Multiset.mem_toFinset.mpr
        (mem_degrees.mpr ⟨mB, mem_support_iff.mp hmB, Finsupp.mem_support_iff.mpr (by omega)⟩)
    exact hrow_disj i₁ ⟨j₁, hAij⟩ j₂ hvB

/-- Canonical permutation on `Fin (s + t)` sending the first `s` indices in order to `U` and the
last `t` indices in order to `Uᶜ`. -/
noncomputable def laplaceBasePerm {s t : ℕ} (U : Finset (Fin (s + t))) (hU : U.card = s) :
    Equiv.Perm (Fin (s + t)) :=
  have hUc : Uᶜ.card = t := by
    have h1 := Finset.card_compl U
    rw [Fintype.card_fin] at h1
    omega
  let toSum : Fin s ⊕ Fin t → Fin (s + t) :=
    Sum.elim (U.orderEmbOfFin hU) (Uᶜ.orderEmbOfFin hUc)
  have htoSum_inj : Function.Injective toSum := by
    rintro (a₁ | b₁) (a₂ | b₂) h
    · simp only [toSum, Sum.elim_inl] at h
      exact congrArg Sum.inl ((U.orderEmbOfFin hU).injective h)
    · exfalso
      simp only [toSum, Sum.elim_inl, Sum.elim_inr] at h
      have h1 : U.orderEmbOfFin hU a₁ ∈ U := Finset.orderEmbOfFin_mem U hU a₁
      have h2 : Uᶜ.orderEmbOfFin hUc b₂ ∈ Uᶜ := Finset.orderEmbOfFin_mem Uᶜ hUc b₂
      rw [h] at h1
      exact (Finset.mem_compl.mp h2) h1
    · exfalso
      simp only [toSum, Sum.elim_inl, Sum.elim_inr] at h
      have h1 : Uᶜ.orderEmbOfFin hUc b₁ ∈ Uᶜ := Finset.orderEmbOfFin_mem Uᶜ hUc b₁
      have h2 : U.orderEmbOfFin hU a₂ ∈ U := Finset.orderEmbOfFin_mem U hU a₂
      rw [h] at h1
      exact (Finset.mem_compl.mp h1) h2
    · simp only [toSum, Sum.elim_inr] at h
      exact congrArg Sum.inr ((Uᶜ.orderEmbOfFin hUc).injective h)
  have htoSum_bij : Function.Bijective toSum := by
    have hcard : Fintype.card (Fin s ⊕ Fin t) = Fintype.card (Fin (s + t)) := by simp
    exact (Fintype.bijective_iff_injective_and_card toSum).mpr ⟨htoSum_inj, hcard⟩
  finSumFinEquiv.symm.trans (Equiv.ofBijective toSum htoSum_bij)

/-- Action of `laplaceBasePerm` on the first `s` indices. -/
theorem laplaceBasePerm_castAdd {s t : ℕ} (U : Finset (Fin (s + t))) (hU : U.card = s)
    (a : Fin s) :
    laplaceBasePerm U hU (Fin.castAdd t a) = U.orderEmbOfFin hU a := by
  simp [laplaceBasePerm]

/-- Action of `laplaceBasePerm` on the last `t` indices. -/
theorem laplaceBasePerm_natAdd {s t : ℕ} (U : Finset (Fin (s + t))) (hU : U.card = s)
    (b : Fin t) :
    laplaceBasePerm U hU (Fin.natAdd s b) =
      Uᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, hU]; omega) b := by
  simp [laplaceBasePerm]

/-- Generalized Laplace expansion of an `(s + t) × (s + t)` determinant along the top `s` rows
and bottom `t` rows. -/
theorem det_eq_sum_submatrix_mul_compl {R : Type*} [CommRing R] {s t : ℕ}
    (A : Matrix (Fin (s + t)) (Fin (s + t)) R) :
    A.det = ∑ U ∈ (Finset.univ : Finset (Fin (s + t))).powersetCard s,
      if hU : U.card = s then
        (Equiv.Perm.sign (laplaceBasePerm U hU) : R) *
          (A.submatrix (Fin.castAdd t) (U.orderEmbOfFin hU)).det *
          (A.submatrix (Fin.natAdd s)
            (Uᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, hU]; omega))).det
      else 0 := by
  classical
  rw [← immanant_sign_eq_det (M := A), immanant]
  let imgRows : Equiv.Perm (Fin (s + t)) → Finset (Fin (s + t)) := fun σ ↦
    Finset.univ.image fun a : Fin s ↦ σ (Fin.castAdd t a)
  have himg_mem : ∀ σ : Equiv.Perm (Fin (s + t)),
      imgRows σ ∈ (Finset.univ : Finset (Fin (s + t))).powersetCard s := fun σ ↦ by
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    dsimp only [imgRows]
    rw [Finset.card_image_of_injective _
        (fun a₁ a₂ h ↦ Fin.castAdd_injective s t (σ.injective h)),
      Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := (Finset.univ : Finset (Fin (s + t))).powersetCard s) (g := imgRows)
    (fun σ _ ↦ himg_mem σ)]
  refine Finset.sum_congr rfl fun U hU_mem ↦ ?_
  have hU : U.card = s := (Finset.mem_powersetCard.mp hU_mem).2
  have hUc : Uᶜ.card = t := by
    have h1 := Finset.card_compl U
    rw [Fintype.card_fin] at h1
    omega
  by_cases hU' : U.card = s
  · simp only [hU', ↓reduceDIte]
    have hRHS :
        (Equiv.Perm.sign (laplaceBasePerm U hU') : R) *
          (A.submatrix (Fin.castAdd t) (U.orderEmbOfFin hU')).det *
          (A.submatrix (Fin.natAdd s) (Uᶜ.orderEmbOfFin hUc)).det =
        ∑ p : Equiv.Perm (Fin s) × Equiv.Perm (Fin t),
          (Equiv.Perm.sign (laplaceBasePerm U hU') : R) *
            ((Equiv.Perm.sign p.1 : R) * ∏ a : Fin s,
              A.submatrix (Fin.castAdd t) (U.orderEmbOfFin hU') a (p.1 a)) *
            ((Equiv.Perm.sign p.2 : R) * ∏ b : Fin t,
              A.submatrix (Fin.natAdd s) (Uᶜ.orderEmbOfFin hUc) b (p.2 b)) := by
      rw [← immanant_sign_eq_det, ← immanant_sign_eq_det, immanant, immanant]
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun σ₁ _ ↦ ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ₂ _ ↦ by ring
    rw [hRHS]
    let base := laplaceBasePerm U hU'
    let Φ : Equiv.Perm (Fin s) × Equiv.Perm (Fin t) → Equiv.Perm (Fin (s + t)) := fun p ↦
      base * finSumFinEquiv.permCongr (Equiv.Perm.sumCongr p.1 p.2)
    have hΦ_cast : ∀ (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin t)) (a : Fin s),
        Φ p (Fin.castAdd t a) = U.orderEmbOfFin hU' (p.1 a) := fun p a ↦ by
      change base (finSumFinEquiv (Equiv.Perm.sumCongr p.1 p.2 (finSumFinEquiv.symm
        (Fin.castAdd t a)))) = _
      simp [base, laplaceBasePerm_castAdd]
    have hΦ_nat : ∀ (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin t)) (b : Fin t),
        Φ p (Fin.natAdd s b) = Uᶜ.orderEmbOfFin hUc (p.2 b) := fun p b ↦ by
      change base (finSumFinEquiv (Equiv.Perm.sumCongr p.1 p.2 (finSumFinEquiv.symm
        (Fin.natAdd s b)))) = _
      simp [base, laplaceBasePerm_natAdd]
    symm
    refine Finset.sum_bij (fun p _ ↦ Φ p) ?_ ?_ ?_ ?_
    · intro p _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      ext x
      simp only [imgRows, Finset.mem_image, Finset.mem_univ, true_and, hΦ_cast]
      constructor
      · rintro ⟨a, rfl⟩
        exact Finset.orderEmbOfFin_mem U hU' (p.1 a)
      · intro hx
        have hx' : x ∈ Set.range (U.orderEmbOfFin hU') := by
          rw [Finset.range_orderEmbOfFin]; exact hx
        obtain ⟨a, ha⟩ := hx'
        exact ⟨p.1.symm a, by simpa using ha⟩
    · intro p₁ _ p₂ _ heq
      refine Prod.ext (Equiv.ext fun a ↦ ?_) (Equiv.ext fun b ↦ ?_)
      · have h := congrArg (fun σ : Equiv.Perm (Fin (s + t)) ↦ σ (Fin.castAdd t a)) heq
        rw [hΦ_cast, hΦ_cast] at h
        exact (U.orderEmbOfFin hU').injective h
      · have h := congrArg (fun σ : Equiv.Perm (Fin (s + t)) ↦ σ (Fin.natAdd s b)) heq
        rw [hΦ_nat, hΦ_nat] at h
        exact (Uᶜ.orderEmbOfFin hUc).injective h
    · intro σ hσ
      have hσU : imgRows σ = U := (Finset.mem_filter.mp hσ).2
      let ρ : Equiv.Perm (Fin (s + t)) := base⁻¹ * σ
      let ψ : Equiv.Perm (Fin s ⊕ Fin t) := finSumFinEquiv.symm.permCongr ρ
      have hψ_inl : ∀ a : Fin s, ∃ a' : Fin s, ψ (Sum.inl a) = Sum.inl a' := fun a ↦ by
        have hmem : σ (Fin.castAdd t a) ∈ U := by
          rw [← hσU]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
        have hr : σ (Fin.castAdd t a) ∈ Set.range (U.orderEmbOfFin hU') := by
          rw [Finset.range_orderEmbOfFin]; exact hmem
        obtain ⟨a', ha'⟩ := hr
        refine ⟨a', ?_⟩
        change finSumFinEquiv.symm (base⁻¹ (σ (Fin.castAdd t a))) = Sum.inl a'
        rw [← ha', ← laplaceBasePerm_castAdd U hU' a']
        change finSumFinEquiv.symm (base.symm (base (Fin.castAdd t a'))) = _
        simp
      have hψ_inr : ∀ b : Fin t, ∃ b' : Fin t, ψ (Sum.inr b) = Sum.inr b' := fun b ↦ by
        have hnot : σ (Fin.natAdd s b) ∉ U := by
          intro hmem
          rw [← hσU] at hmem
          obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
          have heq := σ.injective ha
          have hlt : (Fin.castAdd t a : ℕ) < s := a.2
          have hge : s ≤ (Fin.natAdd s b : ℕ) := by simp
          have hval := congrArg Fin.val heq
          omega
        have hr : σ (Fin.natAdd s b) ∈ Set.range (Uᶜ.orderEmbOfFin hUc) := by
          rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hnot
        obtain ⟨b', hb'⟩ := hr
        refine ⟨b', ?_⟩
        change finSumFinEquiv.symm (base⁻¹ (σ (Fin.natAdd s b))) = Sum.inr b'
        rw [← hb', ← laplaceBasePerm_natAdd U hU' b']
        change finSumFinEquiv.symm (base.symm (base (Fin.natAdd s b'))) = _
        simp
      choose τ₁Fn hτ₁Fn using hψ_inl
      choose τ₂Fn hτ₂Fn using hψ_inr
      have hτ₁_inj : Function.Injective τ₁Fn := fun a₁ a₂ h ↦ by
        have h1 : ψ (Sum.inl a₁) = ψ (Sum.inl a₂) := by rw [hτ₁Fn, hτ₁Fn, h]
        exact Sum.inl.inj (ψ.injective h1)
      have hτ₂_inj : Function.Injective τ₂Fn := fun b₁ b₂ h ↦ by
        have h1 : ψ (Sum.inr b₁) = ψ (Sum.inr b₂) := by rw [hτ₂Fn, hτ₂Fn, h]
        exact Sum.inr.inj (ψ.injective h1)
      let τ₁ : Equiv.Perm (Fin s) :=
        Equiv.ofBijective τ₁Fn (Finite.injective_iff_bijective.mp hτ₁_inj)
      let τ₂ : Equiv.Perm (Fin t) :=
        Equiv.ofBijective τ₂Fn (Finite.injective_iff_bijective.mp hτ₂_inj)
      have hψ_eq : ψ = Equiv.Perm.sumCongr τ₁ τ₂ := by
        ext x
        cases x with
        | inl a => exact hτ₁Fn a
        | inr b => exact hτ₂Fn b
      refine ⟨(τ₁, τ₂), Finset.mem_univ _, ?_⟩
      change base * finSumFinEquiv.permCongr (Equiv.Perm.sumCongr τ₁ τ₂) = σ
      rw [← hψ_eq]
      have hcong : finSumFinEquiv.permCongr (finSumFinEquiv.symm.permCongr ρ) = ρ := by
        ext x; simp
      rw [hcong]
      simp [ρ]
    · intro p _
      have hsign : (Equiv.Perm.sign (Φ p) : R) =
          (Equiv.Perm.sign base : R) * (Equiv.Perm.sign p.1 : R) * (Equiv.Perm.sign p.2 : R) := by
        simp only [Φ, map_mul, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Units.val_mul,
          Int.cast_mul]
        ring
      have hprod : (∏ i : Fin (s + t), A i (Φ p i)) =
          (∏ a : Fin s, A (Fin.castAdd t a) (U.orderEmbOfFin hU' (p.1 a))) *
          (∏ b : Fin t, A (Fin.natAdd s b) (Uᶜ.orderEmbOfFin hUc (p.2 b))) := by
        rw [Fin.prod_univ_add]
        congr 1
        · exact Finset.prod_congr rfl fun a _ ↦ by rw [hΦ_cast]
        · exact Finset.prod_congr rfl fun b _ ↦ by rw [hΦ_nat]
      rw [hsign, hprod]
      simp only [Matrix.submatrix_apply]
      ring
  · exact absurd hU hU'

end CslibFrontier.Matrix
