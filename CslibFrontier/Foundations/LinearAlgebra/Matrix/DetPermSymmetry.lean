module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Symmetry Characterizations of Determinant, Permanent, and Padded Permanent

Proves that the determinant, permanent, and padded permanent polynomials over $\mathbb{C}$ are
uniquely characterized (up to scalar multiples) by their linear symmetry groups, under standard
Lean axioms.

## Main definitions

- `detPoly`, `permPoly`, `paddedPerm`: the multivariate determinant, permanent, and padded
  permanent polynomials on $M_m(\mathbb{C})$.
- `matSubst`: left-right matrix substitution $(A, B) \cdot f(X) = f(A X B)$.
- `diagSubst`: diagonal variable scaling on multivariate polynomials.

## Main results

- `sl_hom_units_eq_one`: every group homomorphism $SL_m(\mathbb{C}) \to \mathbb{C}^\times$ is
  trivial (perfectness of $SL_m(\mathbb{C})$).
- `det_characterized_by_sl_stabilizer`: every homogeneous degree-$m$ polynomial fixed
  projectively by $SL_m(\mathbb{C}) \times SL_m(\mathbb{C})$ is a scalar multiple of $\det_m$.
- `perm_characterized_by_affine_stabilizer`: every homogeneous degree-$n$ polynomial fixed
  affinely by unit-product diagonal left-right scalings and left permutation matrices is a scalar
  multiple of $\mathrm{perm}_n$.
- `det_fixed_projectively_by_perm_monomial_group`: for every $n \ge 2$, the projective monomial
  and transpose group also stabilizes $[\det_n]$, demonstrating necessity of affine stabilization.
- `padded_perm_characterized_by_affine_stabilizer`: affine stabilizer characterization of the
  padded permanent $y^{m-n}\mathrm{perm}_n(X)$ for $1 \le n < m$.
-/

public section

namespace CslibFrontier

open Finset MvPolynomial
open scoped Matrix

/-- The determinant polynomial $\det_m(X) \in \mathbb{C}[M_m(\mathbb{C})]$. -/
noncomputable def detPoly (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ :=
  (Matrix.of fun i j : Fin m ↦ (X (i, j) : MvPolynomial (Fin m × Fin m) ℂ)).det

/-- The permanent polynomial $\mathrm{perm}_n(X) \in \mathbb{C}[M_n(\mathbb{C})]$. -/
noncomputable def permPoly (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.of fun i j : Fin n ↦ (X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent

/-- The padded permanent polynomial $y^{m-n} \mathrm{perm}_n(X) \in \mathbb{C}[M_m(\mathbb{C})]$
where $X$ occupies the top-left $n \times n$
block and $y = X_{m-1, m-1}$ is the bottom-right coordinate (for $n < m$). -/
noncomputable def paddedPerm (m n : ℕ) (hnm : n < m) : MvPolynomial (Fin m × Fin m) ℂ :=
  let y : MvPolynomial (Fin m × Fin m) ℂ := X (⟨m - 1, by omega⟩, ⟨m - 1, by omega⟩)
  let Xblock : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ) :=
    Matrix.of fun i j ↦ X (Fin.castLE (le_of_lt hnm) i, Fin.castLE (le_of_lt hnm) j)
  y ^ (m - n) * Xblock.permanent

/-- Evaluation of `detPoly m` at a matrix $M \in M_m(\mathbb{C})$ equals $\det M$. -/
theorem eval_detPoly {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    MvPolynomial.eval (fun p : Fin m × Fin m ↦ M p.1 p.2) (detPoly m) = M.det := by
  unfold detPoly
  rw [RingHom.map_det (MvPolynomial.eval (fun p : Fin m × Fin m ↦ M p.1 p.2))]
  congr 1
  ext i j
  simp

/-- Evaluation of `permPoly n` at a matrix $M \in M_n(\mathbb{C})$ equals $\mathrm{perm}\, M$. -/
theorem eval_permPoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n ↦ M p.1 p.2) (permPoly n) = M.permanent := by
  unfold permPoly Matrix.permanent
  simp [map_sum, map_prod]

/-- `detPoly m` is homogeneous of degree $m$. -/
theorem detPoly_isHomogeneous (m : ℕ) : (detPoly m).IsHomogeneous m := by
  rw [detPoly, Matrix.det_apply]
  refine IsHomogeneous.sum (univ : Finset (Equiv.Perm (Fin m))) _ _ fun σ _ ↦ ?_
  have hprod : (∏ i : Fin m, (X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ)).IsHomogeneous m := by
    have h := IsHomogeneous.prod (univ : Finset (Fin m))
      (fun i : Fin m ↦ (X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ))
      (fun _ ↦ 1) (fun i _ ↦ isHomogeneous_X ℂ (σ i, i))
    simpa using h
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, MvPolynomial.smul_eq_C_mul]
  simpa using (isHomogeneous_C (Fin m × Fin m) ((Equiv.Perm.sign σ : ℤ) : ℂ)).mul hprod

/-- `permPoly n` is homogeneous of degree $n$. -/
theorem permPoly_isHomogeneous (n : ℕ) : (permPoly n).IsHomogeneous n := by
  unfold permPoly Matrix.permanent
  refine IsHomogeneous.sum univ _ _ fun σ _ ↦ ?_
  have h := IsHomogeneous.prod (univ : Finset (Fin n))
    (fun i : Fin n ↦ (X (σ i, i) : MvPolynomial (Fin n × Fin n) ℂ))
    (fun _ ↦ 1) (fun i _ ↦ isHomogeneous_X ℂ (σ i, i))
  simpa using h

/-- `paddedPerm m n hnm` is homogeneous of degree $m$. -/
theorem paddedPerm_isHomogeneous {m n : ℕ} (hnm : n < m) :
    (paddedPerm m n hnm).IsHomogeneous m := by
  unfold paddedPerm
  have hy : ((X (⟨m - 1, by omega⟩, ⟨m - 1, by omega⟩) :
      MvPolynomial (Fin m × Fin m) ℂ) ^ (m - n)).IsHomogeneous (m - n) := by
    simpa using (isHomogeneous_X ℂ _).pow (m - n)
  have hp : ((Matrix.of fun i j : Fin n ↦
      (X (Fin.castLE (le_of_lt hnm) i, Fin.castLE (le_of_lt hnm) j) :
        MvPolynomial (Fin m × Fin m) ℂ)).permanent).IsHomogeneous n := by
    unfold Matrix.permanent
    refine IsHomogeneous.sum univ _ _ fun σ _ ↦ ?_
    have h := IsHomogeneous.prod (univ : Finset (Fin n))
      (fun i : Fin n ↦ (X (Fin.castLE (le_of_lt hnm) (σ i),
        Fin.castLE (le_of_lt hnm) i) : MvPolynomial (Fin m × Fin m) ℂ))
      (fun _ ↦ 1) (fun i _ ↦ isHomogeneous_X ℂ _)
    simpa using h
  have hmul := hy.mul hp
  rwa [Nat.sub_add_cancel (le_of_lt hnm)] at hmul


/-- Left-right matrix substitution algebra endomorphism on $\mathbb{C}[M_m(\mathbb{C})]$:
`(matSubst A B f)(X) = f(A * X * B)`. -/
noncomputable def matSubst {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    MvPolynomial (Fin m × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin m × Fin m) ℂ :=
  MvPolynomial.aeval fun p : Fin m × Fin m ↦
    ∑ k : Fin m, ∑ l : Fin m, C (A p.1 k * B l p.2) * X (k, l)

/-- Evaluation law for `matSubst`: `(matSubst A B f)(M) = f(A * M * B)`. -/
theorem eval_matSubst {m : ℕ} (A B M : Matrix (Fin m) (Fin m) ℂ)
    (f : MvPolynomial (Fin m × Fin m) ℂ) :
    MvPolynomial.eval (fun p : Fin m × Fin m ↦ M p.1 p.2) (matSubst A B f) =
      MvPolynomial.eval (fun p : Fin m × Fin m ↦ (A * M * B) p.1 p.2) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [matSubst]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [matSubst, aeval_X, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    ring

/-- Composition law for `matSubst`:
`matSubst A₁ B₁ (matSubst A₂ B₂ f) = matSubst (A₂ * A₁) (B₁ * B₂) f`. -/
theorem matSubst_comp {m : ℕ} (A₁ B₁ A₂ B₂ : Matrix (Fin m) (Fin m) ℂ)
    (f : MvPolynomial (Fin m × Fin m) ℂ) :
    matSubst A₁ B₁ (matSubst A₂ B₂ f) = matSubst (A₂ * A₁) (B₁ * B₂) f := by
  apply MvPolynomial.funext
  intro M
  let Mmat : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j ↦ M (i, j)
  have hM : M = fun p : Fin m × Fin m ↦ Mmat p.1 p.2 := rfl
  rw [hM, eval_matSubst, eval_matSubst, eval_matSubst]
  have hmat : A₂ * (A₁ * Mmat * B₁) * B₂ = A₂ * A₁ * Mmat * (B₁ * B₂) := by
    simp [Matrix.mul_assoc]
  rw [hmat]

/-- Identity law for `matSubst`. -/
theorem matSubst_one {m : ℕ} (f : MvPolynomial (Fin m × Fin m) ℂ) :
    matSubst (1 : Matrix (Fin m) (Fin m) ℂ) 1 f = f := by
  apply MvPolynomial.funext
  intro M
  let Mmat : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j ↦ M (i, j)
  have hM : M = fun p : Fin m × Fin m ↦ Mmat p.1 p.2 := rfl
  rw [hM, eval_matSubst]
  simp [Mmat]

private lemma diag_mul_single {m : ℕ} (d : Fin m → ℂ) (i j : Fin m) (x : ℂ) :
    Matrix.diagonal d * Matrix.single i j x = Matrix.single i j (d i * x) := by
  ext r s; simp only [Matrix.diagonal_mul, Matrix.single_apply]; split_ifs <;> simp_all

private lemma single_mul_diag {m : ℕ} (i j : Fin m) (x : ℂ) (d : Fin m → ℂ) :
    Matrix.single i j x * Matrix.diagonal d = Matrix.single i j (x * d j) := by
  ext r s; simp only [Matrix.mul_diagonal, Matrix.single_apply]; split_ifs <;> simp_all

private lemma single_mul_single' {m : ℕ} (a b c d : Fin m) (x y : ℂ) :
    Matrix.single a b x * Matrix.single c d y =
      if b = c then Matrix.single a d (x * y) else 0 := by
  ext r s; simp only [Matrix.mul_apply, Matrix.single_apply]
  by_cases hbc : b = c
  · subst hbc; simp only [↓reduceIte]; rw [sum_eq_single b]
    · by_cases hra : a = r <;> by_cases hds : d = s <;> simp [hra, hds]
    · intro k _ hkb; simp [Ne.symm hkb]
    · intro h; exact absurd (mem_univ b) h
  · simp only [hbc, ↓reduceIte, Matrix.zero_apply]
    exact sum_eq_zero fun k _ ↦ by
      by_cases hbk : b = k
      · subst hbk; simp [Ne.symm hbc]
      · simp [hbk]

/-- Helper: every `SL_m(ℂ)` transvection is a commutator of `diag2n` and a transvection. -/
private lemma sl_transvection_commutator {m : ℕ} {i j : Fin m} (hij : i ≠ j) (a : ℂ) :
    Matrix.SpecialLinearGroup.diag2n hij (2 : ℂ) (by norm_num) *
      Matrix.SpecialLinearGroup.transvection hij (a / 3) *
      (Matrix.SpecialLinearGroup.diag2n hij (2 : ℂ) (by norm_num))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection hij (a / 3))⁻¹ =
    Matrix.SpecialLinearGroup.transvection hij a := by
  have hdiag_inv : (Matrix.SpecialLinearGroup.diag2n hij (2 : ℂ) (by norm_num))⁻¹ =
      Matrix.SpecialLinearGroup.diag2n hij (2⁻¹ : ℂ) (by norm_num) := by
    apply inv_eq_of_mul_eq_one_right; ext r s
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.diagonal_mul_diagonal, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply,
      Matrix.diagonal_apply]
    split_ifs <;> norm_num
  rw [hdiag_inv, Matrix.SpecialLinearGroup.transvection_inv]
  ext r s
  have hD : (Matrix.SpecialLinearGroup.diag2n hij (2 : ℂ) (by norm_num)).1 *
      (Matrix.SpecialLinearGroup.transvection hij (a / 3)).1 *
      (Matrix.SpecialLinearGroup.diag2n hij (2⁻¹ : ℂ) (by norm_num)).1 =
      (Matrix.SpecialLinearGroup.transvection hij (4 * (a / 3))).1 := by
    simp only [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      diag_mul_single, single_mul_diag, ↓reduceIte, hij.symm, inv_inv]
    have hd1 : (fun k : Fin m ↦
        (if k = i then (2 : ℂ) else if k = j then 2⁻¹ else 1) *
        (if k = i then 2⁻¹ else if k = j then 2 else 1)) = fun _ ↦ 1 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    have hdiag_eq : Matrix.diagonal (fun k : Fin m ↦
        (if k = i then (2 : ℂ) else if k = j then 2⁻¹ else 1) *
        (if k = i then 2⁻¹ else if k = j then 2 else 1)) = 1 := by
      rw [hd1, Matrix.diagonal_one]
    have hsc : (2 : ℂ) * (a / 3) * 2 = 4 * (a / 3) := by ring
    change Matrix.diagonal (fun k : Fin m ↦
        (if k = i then (2 : ℂ) else if k = j then 2⁻¹ else 1) *
        (if k = i then 2⁻¹ else if k = j then 2 else 1)) +
      Matrix.single i j ((2 : ℂ) * (a / 3) * 2) = 1 + Matrix.single i j (4 * (a / 3))
    rw [hdiag_eq, hsc]
  change ((Matrix.SpecialLinearGroup.diag2n hij (2 : ℂ) (by norm_num)).1 *
      (Matrix.SpecialLinearGroup.transvection hij (a / 3)).1 *
      (Matrix.SpecialLinearGroup.diag2n hij (2⁻¹ : ℂ) (by norm_num)).1 *
      (Matrix.SpecialLinearGroup.transvection hij (-(a / 3))).1) r s =
    (Matrix.SpecialLinearGroup.transvection hij a).1 r s
  rw [hD, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.transvection_add]
  have hsc : 4 * (a / 3) + -(a / 3) = a := by ring
  rw [hsc]

/-- Helper: every `diag2n hij c hc` in `SL_m(ℂ)` factors into 6 transvections. -/
private lemma sl_diag2n_eq_transvections {m : ℕ} {i j : Fin m} (hij : i ≠ j) {c : ℂ} (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij c hc =
      Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij (-1) *
      Matrix.SpecialLinearGroup.transvection hij.symm 1 *
      Matrix.SpecialLinearGroup.transvection hij (-1) := by
  have hW : ∀ (x : ℂ) (hx : x ≠ 0),
      (Matrix.SpecialLinearGroup.transvection hij x *
        Matrix.SpecialLinearGroup.transvection hij.symm (-x⁻¹) *
        Matrix.SpecialLinearGroup.transvection hij x).1 =
      (1 : Matrix (Fin m) (Fin m) ℂ) + Matrix.single i i (-1) + Matrix.single j j (-1) +
        Matrix.single i j x + Matrix.single j i (-x⁻¹) := by
    intro x hx
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, single_mul_single',
      hij.symm, ↓reduceIte, add_zero]
    ext r s
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases hri : i = r
    · rw [← hri]
      by_cases hsi : i = s
      · rw [← hsi]; simp [hij.symm]; field_simp [hx]; ring
      · by_cases hsj : j = s
        · rw [← hsj]; simp [hij, hij.symm]
        · simp [hij.symm, hsi, hsj]
    · by_cases hrj : j = r
      · rw [← hrj]
        by_cases hsi : i = s
        · rw [← hsi]; simp [hij, hij.symm]
        · by_cases hsj : j = s
          · rw [← hsj]; simp [hij]; field_simp [hx]; ring
          · simp [hij, hsi, hsj]
      · simp [hri, hrj]
  have hrhs : (Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij (-1) *
      Matrix.SpecialLinearGroup.transvection hij.symm 1 *
      Matrix.SpecialLinearGroup.transvection hij (-1)).1 =
    (Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij c).1 *
    (Matrix.SpecialLinearGroup.transvection hij (-1) *
      Matrix.SpecialLinearGroup.transvection hij.symm (-((-1 : ℂ)⁻¹)) *
      Matrix.SpecialLinearGroup.transvection hij (-1)).1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    have hneg1 : -((-1 : ℂ)⁻¹) = 1 := by norm_num
    rw [hneg1]
  apply Subtype.ext
  rw [hrhs, hW c hc, hW (-1) (by norm_num)]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, single_mul_single',
    hij, hij.symm, ↓reduceIte, add_zero]
  ext r s
  simp only [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hri : i = r
  · rw [← hri]
    by_cases hsi : i = s
    · rw [← hsi]; simp [hij.symm]
    · by_cases hsj : j = s
      · rw [← hsj]; simp [hij, hij.symm]
      · simp [hij.symm, hsi, hsj]
  · by_cases hrj : j = r
    · rw [← hrj]
      by_cases hsi : i = s
      · rw [← hsi]; simp [hij, hij.symm]
      · by_cases hsj : j = s
        · rw [← hsj]; simp [hij, hij.symm]
        · simp [hij, hsi, hsj]
    · simp [hri, hrj, Ne.symm hri, Ne.symm hrj]

/-- Perfectness of $SL_m(\mathbb{C})$: every multiplicative homomorphism
$SL_m(\mathbb{C}) \to \mathbb{C}^\times$ is trivial. -/
theorem sl_hom_units_eq_one {m : ℕ} (χ : Matrix.SpecialLinearGroup (Fin m) ℂ →* ℂˣ)
    (A : Matrix.SpecialLinearGroup (Fin m) ℂ) : χ A = 1 := by
  by_cases hm : 2 ≤ m
  · have : Nontrivial (Fin m) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
    have htr : ∀ (i j : Fin m) (hij : i ≠ j) (a : ℂ),
        χ (Matrix.SpecialLinearGroup.transvection hij a) = 1 := fun i j hij a ↦ by
      rw [← sl_transvection_commutator hij a]
      simp only [map_mul, map_inv]
      simp [mul_comm]
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun M ↦ χ M = 1) A
      (fun i j hij c hc ↦ ?_) htr (fun M₁ M₂ h₁ h₂ ↦ by rw [map_mul, h₁, h₂, mul_one])
    rw [sl_diag2n_eq_transvections hij hc]
    simp only [map_mul, htr, mul_one]
  · have hA1 : A = 1 := by
      ext i j
      have hm0 : m = 0 ∨ m = 1 := by omega
      rcases hm0 with rfl | rfl
      · exact Fin.elim0 i
      · fin_cases i; fin_cases j
        have hdet := A.2
        simpa [Matrix.det_fin_one] using hdet
    rw [hA1, map_one]

/-- Every homogeneous degree-$m$
polynomial on $M_m(\mathbb{C})$ fixed projectively by $SL_m(\mathbb{C}) \times SL_m(\mathbb{C})$
is a scalar multiple of $\det_m$. -/
theorem det_characterized_by_sl_stabilizer {m : ℕ} (hm : 0 < m)
    (f : MvPolynomial (Fin m × Fin m) ℂ) (hf_hom : f.IsHomogeneous m)
    (hstab : ∀ A B : Matrix.SpecialLinearGroup (Fin m) ℂ,
      ∃ c : ℂˣ, matSubst A.1 B.1 f = C (c : ℂ) * f) :
    f = C (MvPolynomial.eval (fun p : Fin m × Fin m ↦ (1 : Matrix (Fin m) (Fin m) ℂ) p.1 p.2) f) *
      detPoly m := by
  by_cases hf0 : f = 0
  · simp [hf0]
  · have hfixed_left : ∀ A : Matrix.SpecialLinearGroup (Fin m) ℂ, matSubst A.1 1 f = f := by
      have hch_ex : ∀ A : Matrix.SpecialLinearGroup (Fin m) ℂ,
          ∃ c : ℂˣ, matSubst A.1 1 f = C (c : ℂ) * f := fun A ↦ hstab A 1
      choose χ hχ using hch_ex
      have hχ_one : χ 1 = 1 := by
        have h1 := hχ 1
        rw [Matrix.SpecialLinearGroup.coe_one, matSubst_one] at h1
        have h2 : C ((χ 1 : ℂ) - 1) * f = 0 := by
          rw [map_sub, map_one, sub_mul, one_mul, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with hc | h0
        · exact Units.ext (sub_eq_zero.mp (MvPolynomial.C_eq_zero.mp hc))
        · exact absurd h0 hf0
      have hχ_mul : ∀ A B : Matrix.SpecialLinearGroup (Fin m) ℂ, χ (A * B) = χ A * χ B := by
        intro A B
        have hAB : matSubst (A * B).1 1 f = C ((χ (A * B) : ℂ)) * f := hχ (A * B)
        have hstep : matSubst (A * B).1 1 f = C ((χ A : ℂ) * (χ B : ℂ)) * f := by
          have h1 : matSubst (A * B).1 1 f = matSubst B.1 1 (matSubst A.1 1 f) := by
            rw [matSubst_comp, Matrix.one_mul]; rfl
          rw [h1, hχ A, map_mul,
            show matSubst B.1 1 (C (χ A : ℂ)) = C (χ A : ℂ) from by simp [matSubst],
            hχ B, ← mul_assoc, ← map_mul, mul_comm (χ A : ℂ)]
        rw [hAB] at hstep
        have h2 : C ((χ (A * B) : ℂ) - (χ A : ℂ) * (χ B : ℂ)) * f = 0 := by
          rw [map_sub, sub_mul, hstep, sub_self]
        rcases mul_eq_zero.mp h2 with hc | h0
        · exact Units.ext (sub_eq_zero.mp (MvPolynomial.C_eq_zero.mp hc))
        · exact absurd h0 hf0
      let χHom : Matrix.SpecialLinearGroup (Fin m) ℂ →* ℂˣ :=
        { toFun := χ, map_one' := hχ_one, map_mul' := hχ_mul }
      intro A
      have h1 : χ A = 1 := sl_hom_units_eq_one χHom A
      simpa [h1] using hχ A
    let c0 : ℂ := MvPolynomial.eval
      (fun p : Fin m × Fin m ↦ (1 : Matrix (Fin m) (Fin m) ℂ) p.1 p.2) f
    have hprod_zero : detPoly m * (f - C c0 * detPoly m) = 0 := by
      apply MvPolynomial.funext
      intro M
      let Mmat : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j ↦ M (i, j)
      have hM : M = fun p : Fin m × Fin m ↦ Mmat p.1 p.2 := rfl
      rw [hM, map_mul, map_sub, map_mul, eval_C, eval_detPoly, map_zero]
      by_cases hdet : Mmat.det = 0
      · simp [hdet]
      · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq Mmat.det hm
        have ht_ne : t ≠ 0 := by
          intro h0; rw [h0, zero_pow (ne_of_gt hm)] at ht; exact hdet ht.symm
        let A : Matrix.SpecialLinearGroup (Fin m) ℂ :=
          ⟨t⁻¹ • Mmat, by
            rw [Matrix.det_smul, Fintype.card_fin, inv_pow, ht, inv_mul_cancel₀ hdet]⟩
        have hM_eq : Mmat = t • A.1 := by
          ext i j
          simp only [A, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht_ne, one_mul]
        have heval_f : MvPolynomial.eval (fun p : Fin m × Fin m ↦ Mmat p.1 p.2) f =
            Mmat.det * c0 := by
          have hscale : (fun p : Fin m × Fin m ↦ Mmat p.1 p.2) =
              t • (fun p : Fin m × Fin m ↦ A.1 p.1 p.2) := by
            funext p; simp [hM_eq]
          rw [hscale, hf_hom.eval_smul, ht]
          congr 1
          have hA : (fun p : Fin m × Fin m ↦ A.1 p.1 p.2) =
              fun p : Fin m × Fin m ↦
                ((A.1 * (1 : Matrix (Fin m) (Fin m) ℂ) * 1 : Matrix (Fin m)
                  (Fin m) ℂ)) p.1 p.2 := by
            simp
          rw [hA, ← eval_matSubst, hfixed_left A]
        rw [heval_f]
        ring
    have hdet_ne : detPoly m ≠ 0 := by
      intro h0
      have h1 := congrArg (MvPolynomial.eval
        (fun p : Fin m × Fin m ↦ (1 : Matrix (Fin m) (Fin m) ℂ) p.1 p.2)) h0
      rw [eval_detPoly, Matrix.det_one, map_zero] at h1
      exact one_ne_zero h1
    rcases mul_eq_zero.mp hprod_zero with hd | hsub
    · exact absurd hd hdet_ne
    · exact sub_eq_zero.mp hsub

/-- Diagonal scaling substitution on `MvPolynomial σ ℂ`: scales each variable `X s` by `w s`. -/
noncomputable def diagSubst {σ : Type*} (w : σ → ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.aeval fun s ↦ C (w s) * X s

/-- Coefficient formula for `diagSubst`: multiplies each monomial `e` by `∏ s, (w s) ^ (e s)`. -/
theorem coeff_diagSubst {σ : Type*} [Fintype σ] (w : σ → ℂ)
    (f : MvPolynomial σ ℂ) (e : σ →₀ ℕ) :
    (diagSubst w f).coeff e = (∏ s : σ, (w s) ^ (e s)) * f.coeff e := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have hmon : diagSubst w (monomial d a) = monomial d (a * ∏ s : σ, (w s) ^ (d s)) := by
      rw [monomial_eq, map_mul, diagSubst, aeval_C, Finsupp.prod, map_prod]
      have hprod : (∏ s ∈ d.support,
            (MvPolynomial.aeval (R := ℂ) (fun s : σ ↦ C (w s) * X s)) (X s ^ d s)) =
          C (∏ s : σ, (w s) ^ (d s)) * ∏ s ∈ d.support, X s ^ d s := by
        simp only [map_pow, aeval_X, mul_pow, prod_mul_distrib]
        congr 1
        simp_rw [← map_pow]
        rw [← map_prod]
        congr 1
        refine prod_subset (subset_univ _) fun s _ hs ↦ ?_
        rw [Finsupp.notMem_support_iff.mp hs, pow_zero]
      rw [hprod, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_C_mul,
        ← mul_assoc, ← map_mul, monomial_eq, Finsupp.prod]
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with hde
    · subst hde; ring
    · simp
  | add p q hp hq =>
    simp [map_add, hp, hq, mul_add]

/-- Relation between `matSubst (diagonal t) (diagonal s)` and `diagSubst`. -/
theorem matSubst_diagonal {m : ℕ} (t s : Fin m → ℂ) (f : MvPolynomial (Fin m × Fin m) ℂ) :
    matSubst (Matrix.diagonal t) (Matrix.diagonal s) f =
      diagSubst (fun p : Fin m × Fin m ↦ t p.1 * s p.2) f := by
  apply MvPolynomial.funext
  intro M
  let Mmat : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j ↦ M (i, j)
  have hM : M = fun p : Fin m × Fin m ↦ Mmat p.1 p.2 := rfl
  rw [hM, eval_matSubst]
  have hev : ∀ g : MvPolynomial (Fin m × Fin m) ℂ,
      MvPolynomial.eval (fun p : Fin m × Fin m ↦ Mmat p.1 p.2)
        (diagSubst (fun p : Fin m × Fin m ↦ t p.1 * s p.2) g) =
      MvPolynomial.eval (fun p : Fin m × Fin m ↦ (t p.1 * s p.2) * Mmat p.1 p.2) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [diagSubst]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p ij hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [diagSubst]
  rw [hev]
  have hfn : (fun p : Fin m × Fin m ↦
      (Matrix.diagonal t * Mmat * Matrix.diagonal s) p.1 p.2) =
      fun p : Fin m × Fin m ↦ (t p.1 * s p.2) * Mmat p.1 p.2 := by
    funext ⟨i, j⟩
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [hfn]

private lemma finsupp_sum_apply {α β : Type*} [AddCommMonoid β] {ι : Type*}
    (s : Finset ι) (f : ι → α →₀ β) (a : α) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, Finsupp.add_apply, ih, sum_insert hi]

private lemma sum_eq_degree_of_isHomogeneous {σ : Type*} [Fintype σ] {d : ℕ}
    {f : MvPolynomial σ ℂ} (hf : f.IsHomogeneous d) {e : σ →₀ ℕ} (he : f.coeff e ≠ 0) :
    ∑ s : σ, e s = d := by
  have h := hf he
  simpa [Finsupp.weight_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype] using h

/-- Helper: a Finsupp exponent `e : Fin n × Fin n →₀ ℕ` with every row sum and column sum
equal to `1` is the permutation monomial `∑ i, single (σ i, i) 1` of a unique `σ ∈ S_n`. -/
private lemma exists_perm_of_row_col_sum_eq_one {n : ℕ} (e : Fin n × Fin n →₀ ℕ)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, e (i, j) = 1)
    (hcol : ∀ j : Fin n, ∑ i : Fin n, e (i, j) = 1) :
    ∃ σ : Equiv.Perm (Fin n), e = ∑ j : Fin n, Finsupp.single (σ j, j) 1 := by
  have hex : ∀ j : Fin n, ∃! i : Fin n, e (i, j) = 1 := by
    intro j
    have h1 := hcol j
    have hne : ∃ i : Fin n, e (i, j) ≠ 0 := by
      by_contra hall
      push Not at hall
      have : ∑ i : Fin n, e (i, j) = 0 := sum_eq_zero fun i _ ↦ hall i
      omega
    obtain ⟨i₀, hi₀⟩ := hne
    have hle : e (i₀, j) ≤ 1 := by
      have := single_le_sum (f := fun i : Fin n ↦ e (i, j)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i₀)
      omega
    have hi₀_eq : e (i₀, j) = 1 := by omega
    refine ⟨i₀, hi₀_eq, fun i hi ↦ ?_⟩
    by_contra hne_i
    have hpair : e (i₀, j) + e (i, j) ≤ ∑ k : Fin n, e (k, j) := by
      have hsub : ({i₀, i} : Finset (Fin n)) ⊆ univ := subset_univ _
      have := sum_le_sum_of_subset (f := fun k : Fin n ↦ e (k, j)) hsub
      rwa [sum_pair (Ne.symm hne_i)] at this
    omega
  choose f hf hf_uniq using hex
  have hfinj : Function.Injective f := by
    intro j₁ j₂ heq
    by_contra hne_j
    have hpair : e (f j₁, j₁) + e (f j₁, j₂) ≤ ∑ j : Fin n, e (f j₁, j) := by
      have hsub : ({j₁, j₂} : Finset (Fin n)) ⊆ univ := subset_univ _
      have := sum_le_sum_of_subset (f := fun j : Fin n ↦ e (f j₁, j)) hsub
      rwa [sum_pair hne_j] at this
    have h1 := hf j₁
    have h2 : e (f j₁, j₂) = 1 := by rw [heq]; exact hf j₂
    have hr := hrow (f j₁)
    omega
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  refine ⟨σ, ?_⟩
  ext ⟨i, j⟩
  rw [finsupp_sum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  have hsum_ite : (∑ k : Fin n, if σ k = i ∧ k = j then (1 : ℕ) else 0) =
      if σ j = i then 1 else 0 := by
    rw [sum_eq_single j]
    · simp
    · intro k _ hkj; simp [hkj]
    · intro hj; exact absurd (mem_univ j) hj
  rw [hsum_ite]
  by_cases hi : σ j = i
  · subst hi; simpa [σ] using hf j
  · simp only [hi, ↓reduceIte]
    have hne1 : e (i, j) ≠ 1 := fun h1 ↦ hi (hf_uniq j i h1).symm
    have hle : e (i, j) ≤ 1 := by
      have := single_le_sum (f := fun k : Fin n ↦ e (k, j)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
      have hc := hcol j
      omega
    omega

private lemma prod_X_eq_finsupp_prod {σ ι : Type*} (s : Finset ι) (g : ι → σ) :
    (∏ i ∈ s, (X (g i) : MvPolynomial σ ℂ)) =
      (∑ i ∈ s, Finsupp.single (g i) 1).prod fun p k ↦ X p ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, ih, sum_insert ha,
      Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
    congr 1
    simp [Finsupp.prod_single_index]

/-- Monomial expansion of `permPoly n` as the sum over all permutation monomials. -/
theorem permPoly_eq_sum_monomial (n : ℕ) :
    permPoly n = ∑ σ : Equiv.Perm (Fin n),
      monomial (∑ j : Fin n, Finsupp.single (σ j, j) 1) (1 : ℂ) := by
  unfold permPoly Matrix.permanent
  refine sum_congr rfl fun σ _ ↦ ?_
  simp only [Matrix.of_apply]
  rw [monomial_eq, map_one, one_mul]
  exact prod_X_eq_finsupp_prod univ fun j ↦ (σ j, j)

/-- Every homogeneous degree-$n$
polynomial on $M_n(\mathbb{C})$ fixed strictly (affinely) by all diagonal left-right scalings
with $\det(D_1)\det(D_2) = 1$ and all left permutation matrices is a scalar multiple of
$\mathrm{perm}_n$. -/
theorem perm_characterized_by_affine_stabilizer {n : ℕ}
    (f : MvPolynomial (Fin n × Fin n) ℂ) (hf_hom : f.IsHomogeneous n)
    (hdiag : ∀ t s : Fin n → ℂ, (∏ i, t i) * (∏ j, s j) = 1 →
      matSubst (Matrix.diagonal t) (Matrix.diagonal s) f = f)
    (hperm : ∀ σ : Equiv.Perm (Fin n),
      matSubst (Equiv.Perm.permMatrix ℂ σ) 1 f = f) :
    ∃ c : ℂ, f = C c * permPoly n := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨f.coeff 0, ?_⟩
    have h1 : permPoly 0 = 1 := by simp [permPoly, Matrix.permanent]
    rw [h1, mul_one]
    ext e
    have he0 : e = 0 := by ext ⟨i, _⟩; exact Fin.elim0 i
    subst he0
    simp
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hrow_col : ∀ e ∈ f.support,
      (∀ i : Fin n, ∑ j : Fin n, e (i, j) = 1) ∧ (∀ j : Fin n, ∑ i : Fin n, e (i, j) = 1) := by
    intro e he
    have hcoeff_ne : f.coeff e ≠ 0 := mem_support_iff.mp he
    have hdeg : ∑ p : Fin n × Fin n, e p = n := sum_eq_degree_of_isHomogeneous hf_hom hcoeff_ne
    have hrow_eq_col : ∀ i j : Fin n, ∑ k : Fin n, e (i, k) = ∑ k : Fin n, e (k, j) := by
      intro i j
      let t : Fin n → ℂ := fun k ↦ if k = i then (2 : ℂ) else 1
      let s : Fin n → ℂ := fun k ↦ if k = j then (2⁻¹ : ℂ) else 1
      have hts : (∏ k, t k) * (∏ k, s k) = 1 := by
        simp [t, s, Finset.prod_ite_eq']
      have hinv := congrArg (fun p : MvPolynomial (Fin n × Fin n) ℂ ↦ p.coeff e) (hdiag t s hts)
      rw [matSubst_diagonal, coeff_diagSubst] at hinv
      have hprod_one : (∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ (e p)) = 1 := by
        have h1 : ((∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ (e p)) - 1) * f.coeff e = 0 := by
          rw [sub_mul, one_mul, hinv, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hcoeff_ne)
      have hsplit : (∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ (e p)) =
          (2 : ℂ) ^ (∑ k : Fin n, e (i, k)) * (2⁻¹ : ℂ) ^ (∑ k : Fin n, e (k, j)) := by
        simp_rw [mul_pow, prod_mul_distrib]
        congr 1
        · rw [Fintype.prod_prod_type]
          calc (∏ a : Fin n, ∏ b : Fin n, t a ^ e (a, b))
              = ∏ a : Fin n, t a ^ (∑ b : Fin n, e (a, b)) :=
                  prod_congr rfl fun a _ ↦ prod_pow_eq_pow_sum univ _ _
            _ = (2 : ℂ) ^ (∑ k : Fin n, e (i, k)) := by
                  rw [prod_eq_single i]
                  · simp [t]
                  · intro a _ hai; simp [t, hai]
                  · intro hi; exact absurd (mem_univ i) hi
        · rw [Fintype.prod_prod_type_right]
          calc (∏ b : Fin n, ∏ a : Fin n, s b ^ e (a, b))
              = ∏ b : Fin n, s b ^ (∑ a : Fin n, e (a, b)) :=
                  prod_congr rfl fun b _ ↦ prod_pow_eq_pow_sum univ _ _
            _ = (2⁻¹ : ℂ) ^ (∑ k : Fin n, e (k, j)) := by
                  rw [prod_eq_single j]
                  · simp [s]
                  · intro b _ hbj; simp [s, hbj]
                  · intro hj; exact absurd (mem_univ j) hj
      rw [hsplit] at hprod_one
      have hpow_eq : (2 : ℂ) ^ (∑ k : Fin n, e (i, k)) = (2 : ℂ) ^ (∑ k : Fin n, e (k, j)) := by
        have h2ne : (2 : ℂ) ^ (∑ k : Fin n, e (k, j)) ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [inv_pow] at hprod_one
        have hmul := congrArg (· * (2 : ℂ) ^ (∑ k : Fin n, e (k, j))) hprod_one
        field_simp at hmul
        simpa [one_mul] using hmul
      have hpow_nat : (2 : ℕ) ^ (∑ k : Fin n, e (i, k)) = (2 : ℕ) ^ (∑ k : Fin n, e (k, j)) := by
        exact_mod_cast hpow_eq
      exact Nat.pow_right_injective (by omega) hpow_nat
    let i0 : Fin n := ⟨0, hn_pos⟩
    have hsum_rows : n * (∑ k : Fin n, e (k, i0)) = n := by
      have h1 : (∑ i : Fin n, ∑ j : Fin n, e (i, j)) = n := by
        rwa [← Fintype.sum_prod_type]
      have h2 : (∑ i : Fin n, ∑ j : Fin n, e (i, j)) =
          ∑ _i : Fin n, ∑ k : Fin n, e (k, i0) :=
        sum_congr rfl fun i _ ↦ hrow_eq_col i i0
      rw [h2, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
      exact h1
    have hcol0 : ∑ k : Fin n, e (k, i0) = 1 :=
      Nat.eq_of_mul_eq_mul_left hn_pos (by simpa using hsum_rows)
    refine ⟨fun i ↦ (hrow_eq_col i i0).trans hcol0, fun j ↦ ?_⟩
    rw [← hrow_eq_col i0 j, hrow_eq_col i0 i0, hcol0]
  let eOf : Equiv.Perm (Fin n) → (Fin n × Fin n →₀ ℕ) :=
    fun σ ↦ ∑ j : Fin n, Finsupp.single (σ j, j) 1
  have heOf_inj : Function.Injective eOf := by
    intro σ τ h
    ext j
    have h1 := congrArg (fun d : Fin n × Fin n →₀ ℕ ↦ d (σ j, j)) h
    simp only [eOf, finsupp_sum_apply, Finsupp.single_apply, Prod.mk.injEq] at h1
    have hlhs : (∑ k : Fin n, if σ k = σ j ∧ k = j then (1 : ℕ) else 0) = 1 := by
      rw [sum_eq_single j] <;> simp
    have hrhs : (∑ k : Fin n, if τ k = σ j ∧ k = j then (1 : ℕ) else 0) =
        if τ j = σ j then 1 else 0 := by
      rw [sum_eq_single j]
      · simp
      · intro k _ hkj; simp [hkj]
      · intro hj; exact absurd (mem_univ j) hj
    rw [hlhs, hrhs] at h1
    by_contra hne
    have hne' : τ j ≠ σ j := fun heq ↦ hne (congrArg Fin.val heq.symm)
    simp [hne'] at h1
  let c : ℂ := f.coeff (eOf 1)
  have hcoeff_perm : ∀ σ : Equiv.Perm (Fin n), f.coeff (eOf σ) = c := by
    intro σ
    have hsubst_perm : matSubst (Equiv.Perm.permMatrix ℂ σ) 1 f =
        MvPolynomial.rename (fun p : Fin n × Fin n ↦ (σ p.1, p.2)) f := by
      apply MvPolynomial.funext
      intro M
      let Mmat : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j ↦ M (i, j)
      have hM : M = fun p : Fin n × Fin n ↦ Mmat p.1 p.2 := rfl
      rw [hM, eval_matSubst, eval_rename]
      have hfn : (fun p : Fin n × Fin n ↦
            ((Equiv.Perm.permMatrix ℂ σ * Mmat * 1 : Matrix (Fin n) (Fin n) ℂ)) p.1 p.2) =
          (fun p : Fin n × Fin n ↦ Mmat p.1 p.2) ∘ fun p : Fin n × Fin n ↦ (σ p.1, p.2) := by
        funext ⟨i, j⟩
        rw [Matrix.mul_one]
        simp only [Function.comp_apply, Matrix.mul_apply, Equiv.Perm.permMatrix]
        rw [sum_eq_single (σ i)]
        · simp
        · intro k _ hk; simp [Ne.symm hk]
        · intro h; exact absurd (mem_univ (σ i)) h
      rw [hfn]
    have h2 := congrArg (fun p : MvPolynomial (Fin n × Fin n) ℂ ↦ p.coeff (eOf σ)) (hperm σ)
    rw [hsubst_perm] at h2
    have hmap : Finsupp.mapDomain (fun p : Fin n × Fin n ↦ (σ p.1, p.2)) (eOf 1) = eOf σ := by
      dsimp only [eOf]
      change Finsupp.mapDomain.addMonoidHom (fun p : Fin n × Fin n ↦ (σ p.1, p.2))
        (∑ j : Fin n, Finsupp.single (j, j) 1) = ∑ j : Fin n, Finsupp.single (σ j, j) 1
      rw [map_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      simp [Finsupp.mapDomain.addMonoidHom]
    rw [← hmap] at h2
    rw [MvPolynomial.coeff_rename_mapDomain _
      (fun ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h ↦ by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (σ.injective h.1) h.2) f (eOf 1)] at h2
    rw [hmap] at h2
    exact h2.symm
  refine ⟨c, ?_⟩
  rw [permPoly_eq_sum_monomial]
  ext e
  rw [coeff_C_mul, coeff_sum]
  simp only [coeff_monomial]
  by_cases he : e ∈ f.support
  · obtain ⟨hrow, hcol⟩ := hrow_col e he
    obtain ⟨σ, rfl⟩ := exists_perm_of_row_col_sum_eq_one e hrow hcol
    change f.coeff (eOf σ) = c * ∑ τ : Equiv.Perm (Fin n), if eOf τ = eOf σ then 1 else 0
    rw [hcoeff_perm σ, sum_eq_single σ]
    · simp
    · intro τ _ hτσ; simp [heOf_inj.ne hτσ]
    · intro hσ; exact absurd (mem_univ σ) hσ
  · have hf0 : f.coeff e = 0 := notMem_support_iff.mp he
    rw [hf0]
    by_cases hperm_e : ∃ σ : Equiv.Perm (Fin n), eOf σ = e
    · obtain ⟨σ, rfl⟩ := hperm_e
      have hc0 : c = 0 := by rw [← hcoeff_perm σ]; exact hf0
      simp [hc0]
    · push Not at hperm_e
      change (0 : ℂ) = c * ∑ τ : Equiv.Perm (Fin n), if eOf τ = e then 1 else 0
      have hsum0 : (∑ τ : Equiv.Perm (Fin n), if eOf τ = e then (1 : ℂ) else 0) = 0 :=
        sum_eq_zero fun τ _ ↦ by simp [hperm_e τ]
      rw [hsum0, mul_zero]

/-- For every $n \ge 2$, the projective monomial and transpose group fixes $[\det_n]$ projectively
as well as $[\mathrm{perm}_n]$, even though $\det_n$ is not a scalar multiple of
$\mathrm{perm}_n$. -/
theorem det_fixed_projectively_by_perm_monomial_group {n : ℕ} (hn : 2 ≤ n) :
    (∀ (t s : Fin n → ℂˣ) (σ τ : Equiv.Perm (Fin n)),
      ∃ c : ℂˣ,
        matSubst (Matrix.diagonal (fun i ↦ (t i : ℂ)) * Equiv.Perm.permMatrix ℂ σ)
          (Equiv.Perm.permMatrix ℂ τ * Matrix.diagonal (fun j ↦ (s j : ℂ))) (detPoly n) =
        C (c : ℂ) * detPoly n) ∧
    (MvPolynomial.rename Prod.swap (detPoly n) = detPoly n) ∧
    (∀ c : ℂ, detPoly n ≠ C c * permPoly n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t s σ τ
    let D₁ : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i ↦ (t i : ℂ)
    let D₂ : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j ↦ (s j : ℂ)
    let P₁ : Matrix (Fin n) (Fin n) ℂ := Equiv.Perm.permMatrix ℂ σ
    let P₂ : Matrix (Fin n) (Fin n) ℂ := Equiv.Perm.permMatrix ℂ τ
    let cval : ℂ := (D₁ * P₁).det * (P₂ * D₂).det
    have hperm_det_ne : ∀ ρ : Equiv.Perm (Fin n), (Equiv.Perm.permMatrix ℂ ρ).det ≠ 0 := fun ρ ↦ by
      have hinv : Equiv.Perm.permMatrix ℂ ρ * Equiv.Perm.permMatrix ℂ ρ⁻¹ = 1 := by
        ext i j
        simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, Matrix.one_apply]
        rw [sum_eq_single (ρ i)]
        · simp
        · intro k _ hk; simp [Ne.symm hk]
        · intro h; exact absurd (mem_univ (ρ i)) h
      intro h0
      have := congrArg Matrix.det hinv
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hc_ne : cval ≠ 0 := by
      have hd1 : D₁.det ≠ 0 := by
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (t i).ne_zero
      have hd2 : D₂.det ≠ 0 := by
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ (s j).ne_zero
      simp only [cval, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero hd1 (hperm_det_ne σ)) (mul_ne_zero (hperm_det_ne τ) hd2)
    refine ⟨Units.mk0 cval hc_ne, ?_⟩
    apply MvPolynomial.funext
    intro M
    let Mmat : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j ↦ M (i, j)
    have hM : M = fun p : Fin n × Fin n ↦ Mmat p.1 p.2 := rfl
    rw [hM, eval_matSubst, eval_detPoly, map_mul, eval_C, eval_detPoly]
    simp only [Units.val_mk0, cval, Matrix.det_mul]
    ring
  · apply MvPolynomial.funext
    intro M
    let Mmat : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j ↦ M (i, j)
    have hM : M = fun p : Fin n × Fin n ↦ Mmat p.1 p.2 := rfl
    rw [hM, eval_rename, eval_detPoly]
    change MvPolynomial.eval (fun p : Fin n × Fin n ↦ Mmatᵀ p.1 p.2) (detPoly n) = Mmat.det
    rw [eval_detPoly, Matrix.det_transpose]
  · intro c hEq
    let J : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun _ _ ↦ (1 : ℂ)
    have hdetJ : J.det = 0 := by
      refine Matrix.det_zero_of_row_eq (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (by simp [Fin.ext_iff]) ?_
      ext k; simp [J]
    have hpermJ : J.permanent = (n.factorial : ℂ) := by
      simp [J, Matrix.permanent, Fintype.card_perm]
    have hvalJ := congrArg (MvPolynomial.eval (fun p : Fin n × Fin n ↦ J p.1 p.2)) hEq
    rw [eval_detPoly, map_mul, eval_C, eval_permPoly, hdetJ, hpermJ] at hvalJ
    have hfac_ne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hc0 : c = 0 := (mul_eq_zero.mp hvalJ.symm).resolve_right hfac_ne
    rw [hc0, map_zero, zero_mul] at hEq
    have hvalI := congrArg (MvPolynomial.eval
      (fun p : Fin n × Fin n ↦ (1 : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)) hEq
    rw [eval_detPoly, Matrix.det_one, map_zero] at hvalI
    exact one_ne_zero hvalI

/-- Affine stabilizer characterization
of the padded permanent $y^{m-n}\mathrm{perm}_n(X) \in \mathbb{C}[M_m(\mathbb{C})]$ for
$1 \le n < m$. -/
theorem padded_perm_characterized_by_affine_stabilizer {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (f : MvPolynomial (Fin m × Fin m) ℂ) (hf_hom : f.IsHomogeneous m)
    (hunused : ∀ p : Fin m × Fin m, ¬ (p.1.1 < n ∧ p.2.1 < n) →
      p ≠ (⟨m - 1, by omega⟩, ⟨m - 1, by omega⟩) →
      diagSubst (fun q ↦ if q = p then (2 : ℂ) else 1) f = f)
    (hdiag : ∀ (t s : Fin n → ℂ) (u : ℂ),
      (∏ i, t i) * (∏ j, s j) * u ^ (m - n) = 1 →
      diagSubst (fun q : Fin m × Fin m ↦
        if h : q.1.1 < n ∧ q.2.1 < n then t ⟨q.1.1, h.1⟩ * s ⟨q.2.1, h.2⟩
        else if q = (⟨m - 1, by omega⟩, ⟨m - 1, by omega⟩) then u else 1) f = f)
    (hperm : ∀ σ : Equiv.Perm (Fin n),
      MvPolynomial.rename (fun q : Fin m × Fin m ↦
        if h : q.1.1 < n ∧ q.2.1 < n then
          (Fin.castLE (le_of_lt hnm) (σ ⟨q.1.1, h.1⟩), q.2)
        else q) f = f) :
    ∃ c : ℂ, f = C c * paddedPerm m n hnm := by
  let yIdx : Fin m × Fin m := (⟨m - 1, by omega⟩, ⟨m - 1, by omega⟩)
  let inBlock : Fin m × Fin m → Prop := fun q ↦ q.1.1 < n ∧ q.2.1 < n
  let emb : Fin n × Fin n → Fin m × Fin m := fun p ↦
    (Fin.castLE (le_of_lt hnm) p.1, Fin.castLE (le_of_lt hnm) p.2)
  have hemb_inj : Function.Injective emb := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    simp only [emb, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  have hy_not_block : ¬ inBlock yIdx := by simp only [inBlock, yIdx]; omega
  have hsupp : ∀ e ∈ f.support,
      (∀ q : Fin m × Fin m, ¬ inBlock q → q ≠ yIdx → e q = 0) ∧
      e yIdx = m - n ∧
      (∀ i : Fin n, ∑ j : Fin n, e (emb (i, j)) = 1) ∧
      (∀ j : Fin n, ∑ i : Fin n, e (emb (i, j)) = 1) := by
    intro e he
    have hcoeff_ne : f.coeff e ≠ 0 := mem_support_iff.mp he
    have hdeg : ∑ q : Fin m × Fin m, e q = m := sum_eq_degree_of_isHomogeneous hf_hom hcoeff_ne
    have hout : ∀ q : Fin m × Fin m, ¬ inBlock q → q ≠ yIdx → e q = 0 := by
      intro q hnb hny
      have hinv := congrArg (fun p : MvPolynomial (Fin m × Fin m) ℂ ↦ p.coeff e) (hunused q hnb hny)
      rw [coeff_diagSubst] at hinv
      have hprod_one : (∏ r : Fin m × Fin m, (if r = q then (2 : ℂ) else 1) ^ e r) = 1 := by
        have h1 : ((∏ r : Fin m × Fin m, (if r = q then (2 : ℂ) else 1) ^ e r) - 1) *
            f.coeff e = 0 := by
          rw [sub_mul, one_mul, hinv, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hcoeff_ne)
      rw [prod_eq_single q] at hprod_one
      · simp only [↓reduceIte] at hprod_one
        have hnat : (2 : ℕ) ^ e q = (2 : ℕ) ^ 0 := by exact_mod_cast hprod_one
        exact Nat.pow_right_injective (by omega) hnat
      · intro r _ hrq; simp [hrq]
      · intro hq; exact absurd (mem_univ q) hq
    have hrow_eq_col : ∀ i j : Fin n,
        ∑ k : Fin n, e (emb (i, k)) = ∑ k : Fin n, e (emb (k, j)) := by
      intro i j
      let t : Fin n → ℂ := fun k ↦ if k = i then (2 : ℂ) else 1
      let s : Fin n → ℂ := fun k ↦ if k = j then (2⁻¹ : ℂ) else 1
      have hts : (∏ k, t k) * (∏ k, s k) * (1 : ℂ) ^ (m - n) = 1 := by
        simp [t, s, Finset.prod_ite_eq']
      have hinv := congrArg (fun p : MvPolynomial (Fin m × Fin m) ℂ ↦ p.coeff e) (hdiag t s 1 hts)
      rw [coeff_diagSubst] at hinv
      let w : Fin m × Fin m → ℂ := fun q ↦
        if h : q.1.1 < n ∧ q.2.1 < n then t ⟨q.1.1, h.1⟩ * s ⟨q.2.1, h.2⟩
        else if q = yIdx then 1 else 1
      have hprod_one : (∏ q : Fin m × Fin m, w q ^ e q) = 1 := by
        have h1 : ((∏ q : Fin m × Fin m, w q ^ e q) - 1) * f.coeff e = 0 := by
          rw [sub_mul, one_mul, hinv, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hcoeff_ne)
      have hblock_prod : (∏ q : Fin m × Fin m, w q ^ e q) =
          ∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ e (emb p) := by
        rw [← prod_subset (subset_univ (univ.image emb)) fun q _ hq ↦ ?_,
          prod_image (fun a _ b _ h ↦ hemb_inj h)]
        · refine prod_congr rfl fun p _ ↦ ?_
          simp [w, emb, p.1.2, p.2.2]
        · by_cases hb : inBlock q
          · exfalso; apply hq; rw [mem_image]
            refine ⟨(⟨q.1.1, hb.1⟩, ⟨q.2.1, hb.2⟩), mem_univ _, ?_⟩; ext <;> rfl
          · dsimp only [inBlock] at hb
            simp [w, hb]
      rw [hblock_prod] at hprod_one
      have hsplit : (∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ e (emb p)) =
          (2 : ℂ) ^ (∑ k : Fin n, e (emb (i, k))) *
          (2⁻¹ : ℂ) ^ (∑ k : Fin n, e (emb (k, j))) := by
        simp_rw [mul_pow, prod_mul_distrib]
        congr 1
        · rw [Fintype.prod_prod_type]
          calc (∏ a : Fin n, ∏ b : Fin n, t a ^ e (emb (a, b)))
              = ∏ a : Fin n, t a ^ (∑ b : Fin n, e (emb (a, b))) :=
                  prod_congr rfl fun a _ ↦ prod_pow_eq_pow_sum univ _ _
            _ = (2 : ℂ) ^ (∑ k : Fin n, e (emb (i, k))) := by
                  rw [prod_eq_single i]
                  · simp [t]
                  · intro a _ hai; simp [t, hai]
                  · intro hi; exact absurd (mem_univ i) hi
        · rw [Fintype.prod_prod_type_right]
          calc (∏ b : Fin n, ∏ a : Fin n, s b ^ e (emb (a, b)))
              = ∏ b : Fin n, s b ^ (∑ a : Fin n, e (emb (a, b))) :=
                  prod_congr rfl fun b _ ↦ prod_pow_eq_pow_sum univ _ _
            _ = (2⁻¹ : ℂ) ^ (∑ k : Fin n, e (emb (k, j))) := by
                  rw [prod_eq_single j]
                  · simp [s]
                  · intro b _ hbj; simp [s, hbj]
                  · intro hj; exact absurd (mem_univ j) hj
      rw [hsplit] at hprod_one
      have hpow_eq : (2 : ℂ) ^ (∑ k : Fin n, e (emb (i, k))) =
          (2 : ℂ) ^ (∑ k : Fin n, e (emb (k, j))) := by
        have h2ne : (2 : ℂ) ^ (∑ k : Fin n, e (emb (k, j))) ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [inv_pow] at hprod_one
        have hmul := congrArg (· * (2 : ℂ) ^ (∑ k : Fin n, e (emb (k, j)))) hprod_one
        field_simp at hmul
        simpa [one_mul] using hmul
      have hpow_nat : (2 : ℕ) ^ (∑ k : Fin n, e (emb (i, k))) =
          (2 : ℕ) ^ (∑ k : Fin n, e (emb (k, j))) := by exact_mod_cast hpow_eq
      exact Nat.pow_right_injective (by omega) hpow_nat
    let i0 : Fin n := ⟨0, hn⟩
    let r0 : ℕ := ∑ k : Fin n, e (emb (i0, k))
    have hy_eq : e yIdx = (m - n) * r0 := by
      let t : Fin n → ℂ := fun k ↦ if k = i0 then (2⁻¹ : ℂ) ^ (m - n) else 1
      let s : Fin n → ℂ := fun _ ↦ 1
      have hts : (∏ k, t k) * (∏ k, s k) * (2 : ℂ) ^ (m - n) = 1 := by
        simp only [t, s, prod_const_one, mul_one, Finset.prod_ite_eq', mem_univ, ↓reduceIte]
        rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
      have hinv := congrArg (fun p : MvPolynomial (Fin m × Fin m) ℂ ↦ p.coeff e) (hdiag t s 2 hts)
      rw [coeff_diagSubst] at hinv
      let w : Fin m × Fin m → ℂ := fun q ↦
        if h : q.1.1 < n ∧ q.2.1 < n then t ⟨q.1.1, h.1⟩ * s ⟨q.2.1, h.2⟩
        else if q = yIdx then (2 : ℂ) else 1
      have hprod_one : (∏ q : Fin m × Fin m, w q ^ e q) = 1 := by
        have h1 : ((∏ q : Fin m × Fin m, w q ^ e q) - 1) * f.coeff e = 0 := by
          rw [sub_mul, one_mul, hinv, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hcoeff_ne)
      have hy_not_img : yIdx ∉ univ.image emb := by
        intro hmem; rw [mem_image] at hmem; obtain ⟨p, _, hp⟩ := hmem
        exact hy_not_block (by rw [← hp]; exact ⟨p.1.2, p.2.2⟩)
      have hdecomp : (∏ q : Fin m × Fin m, w q ^ e q) =
          w yIdx ^ e yIdx * ∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ e (emb p) := by
        rw [← prod_subset (subset_univ (insert yIdx (univ.image emb))) fun q _ hq ↦ ?_,
          prod_insert hy_not_img, prod_image (fun a _ b _ h ↦ hemb_inj h)]
        · congr 1; refine prod_congr rfl fun p _ ↦ ?_; simp [w, emb, p.1.2, p.2.2]
        · simp only [mem_insert, mem_image, mem_univ, true_and, not_or] at hq
          have hnb : ¬ (q.1.1 < n ∧ q.2.1 < n) :=
            fun hb ↦ hq.2 ⟨(⟨q.1.1, hb.1⟩, ⟨q.2.1, hb.2⟩), by ext <;> rfl⟩
          simp [w, hnb, hq.1]
      rw [hdecomp] at hprod_one
      have hwy : w yIdx = 2 := by
        have hnb : ¬ (yIdx.1.1 < n ∧ yIdx.2.1 < n) := hy_not_block
        simp [w, hnb]
      have hblock_val : (∏ p : Fin n × Fin n, (t p.1 * s p.2) ^ e (emb p)) =
          (2⁻¹ : ℂ) ^ ((m - n) * r0) := by
        simp only [s, mul_one]; rw [Fintype.prod_prod_type]
        calc (∏ a : Fin n, ∏ b : Fin n, t a ^ e (emb (a, b)))
            = ∏ a : Fin n, t a ^ (∑ b : Fin n, e (emb (a, b))) :=
                prod_congr rfl fun a _ ↦ prod_pow_eq_pow_sum univ _ _
          _ = ((2⁻¹ : ℂ) ^ (m - n)) ^ r0 := by
                rw [prod_eq_single i0]
                · simp [t, r0]
                · intro a _ hai; simp [t, hai]
                · intro hi; exact absurd (mem_univ i0) hi
          _ = (2⁻¹ : ℂ) ^ ((m - n) * r0) := (pow_mul _ _ _).symm
      rw [hwy, hblock_val, inv_pow] at hprod_one
      have hpow_eq : (2 : ℂ) ^ e yIdx = (2 : ℂ) ^ ((m - n) * r0) := by
        have h2ne : (2 : ℂ) ^ ((m - n) * r0) ≠ 0 := pow_ne_zero _ (by norm_num)
        have hmul := congrArg (· * (2 : ℂ) ^ ((m - n) * r0)) hprod_one
        field_simp at hmul; simpa [one_mul] using hmul
      have hpow_nat : (2 : ℕ) ^ e yIdx = (2 : ℕ) ^ ((m - n) * r0) := by exact_mod_cast hpow_eq
      exact Nat.pow_right_injective (by omega) hpow_nat
    have hsum_all : ∑ q : Fin m × Fin m, e q = e yIdx + ∑ p : Fin n × Fin n, e (emb p) := by
      have hy_not_img : yIdx ∉ univ.image emb := by
        intro hmem; rw [mem_image] at hmem; obtain ⟨p, _, hp⟩ := hmem
        exact hy_not_block (by rw [← hp]; exact ⟨p.1.2, p.2.2⟩)
      rw [← sum_subset (subset_univ (insert yIdx (univ.image emb))) fun q _ hq ↦ ?_,
        sum_insert hy_not_img, sum_image (fun a _ b _ h ↦ hemb_inj h)]
      simp only [mem_insert, mem_image, mem_univ, true_and, not_or] at hq
      have hnb : ¬ inBlock q := fun hb ↦ hq.2 ⟨(⟨q.1.1, hb.1⟩, ⟨q.2.1, hb.2⟩), by ext <;> rfl⟩
      exact hout q hnb hq.1
    have hblock_sum : ∑ p : Fin n × Fin n, e (emb p) = n * r0 := by
      rw [Fintype.sum_prod_type]
      have h1 : ∀ i : Fin n, ∑ j : Fin n, e (emb (i, j)) = r0 := fun i ↦ by
        rw [hrow_eq_col i i0, ← hrow_eq_col i0 i0]
      simp_rw [h1]; simp
    have hmr : m * r0 = m := by
      have h1 : (m - n) * r0 + n * r0 = m := by rw [← hy_eq, ← hblock_sum, ← hsum_all, hdeg]
      have h2 : (m - n) * r0 + n * r0 = m * r0 := by
        rw [← add_mul, Nat.sub_add_cancel (le_of_lt hnm)]
      omega
    have hm_pos : 0 < m := by omega
    have hr0 : r0 = 1 := Nat.eq_of_mul_eq_mul_left hm_pos (by simpa using hmr)
    refine ⟨hout, by rw [hy_eq, hr0, mul_one], fun i ↦ ?_, fun j ↦ ?_⟩
    · rw [hrow_eq_col i i0, ← hrow_eq_col i0 i0]; exact hr0
    · rw [← hrow_eq_col i0 j]; exact hr0
  let ePad : Equiv.Perm (Fin n) → (Fin m × Fin m →₀ ℕ) := fun σ ↦
    Finsupp.single yIdx (m - n) + ∑ j : Fin n, Finsupp.single (emb (σ j, j)) 1
  have hePad_inj : Function.Injective ePad := by
    intro σ τ h
    ext j
    have h1 := congrArg (fun d : Fin m × Fin m →₀ ℕ ↦ d (emb (σ j, j))) h
    have hny : yIdx ≠ emb (σ j, j) := fun heq ↦ hy_not_block (by rw [heq]; exact ⟨(σ j).2, j.2⟩)
    simp only [ePad, Finsupp.add_apply, Finsupp.single_apply, hny, ↓reduceIte, zero_add,
      finsupp_sum_apply] at h1
    have hlhs : (∑ k : Fin n, if emb (σ k, k) = emb (σ j, j) then (1 : ℕ) else 0) = 1 := by
      rw [sum_eq_single j]
      · simp
      · intro k _ hkj
        have : emb (σ k, k) ≠ emb (σ j, j) := fun heq ↦ hkj (congrArg Prod.snd (hemb_inj heq))
        simp [this]
      · intro hj; exact absurd (mem_univ j) hj
    have hrhs : (∑ k : Fin n, if emb (τ k, k) = emb (σ j, j) then (1 : ℕ) else 0) =
        if τ j = σ j then 1 else 0 := by
      rw [sum_eq_single j]
      · by_cases hEq : τ j = σ j
        · simp [hEq]
        · have : emb (τ j, j) ≠ emb (σ j, j) := fun heq ↦ hEq (congrArg Prod.fst (hemb_inj heq))
          simp [hEq, this]
      · intro k _ hkj
        have : emb (τ k, k) ≠ emb (σ j, j) := fun heq ↦ hkj (congrArg Prod.snd (hemb_inj heq))
        simp [this]
      · intro hj; exact absurd (mem_univ j) hj
    rw [hlhs, hrhs] at h1
    by_contra hne
    have hne' : τ j ≠ σ j := fun heq ↦ hne (congrArg Fin.val heq.symm)
    simp [hne'] at h1
  let c : ℂ := f.coeff (ePad 1)
  have hcoeff_pad : ∀ σ : Equiv.Perm (Fin n), f.coeff (ePad σ) = c := by
    intro σ
    let g : Fin m × Fin m → Fin m × Fin m := fun q ↦
      if h : q.1.1 < n ∧ q.2.1 < n then (Fin.castLE (le_of_lt hnm) (σ ⟨q.1.1, h.1⟩), q.2) else q
    have hg_inj : Function.Injective g := by
      intro q₁ q₂ hq
      by_cases h1 : q₁.1.1 < n ∧ q₁.2.1 < n <;> by_cases h2 : q₂.1.1 < n ∧ q₂.2.1 < n
      · have hq' : (Fin.castLE (le_of_lt hnm) (σ ⟨q₁.1.1, h1.1⟩), q₁.2) =
            (Fin.castLE (le_of_lt hnm) (σ ⟨q₂.1.1, h2.1⟩), q₂.2) := by
          simpa [g, h1, h2] using hq
        have hfst : σ ⟨q₁.1.1, h1.1⟩ = σ ⟨q₂.1.1, h2.1⟩ := by
          apply Fin.ext
          simpa [Fin.val_castLE] using congrArg (fun p : Fin m × Fin m ↦ p.1.1) hq'
        have h12 := congrArg Fin.val (σ.injective hfst)
        exact Prod.ext (Fin.ext h12) (Prod.mk.inj hq').2
      · exfalso; apply h2
        have hq' : (Fin.castLE (le_of_lt hnm) (σ ⟨q₁.1.1, h1.1⟩), q₁.2) = q₂ := by
          simpa [g, h1, h2] using hq
        rw [← hq']; exact ⟨(σ ⟨q₁.1.1, h1.1⟩).2, h1.2⟩
      · exfalso; apply h1
        have hq' : q₁ = (Fin.castLE (le_of_lt hnm) (σ ⟨q₂.1.1, h2.1⟩), q₂.2) := by
          simpa [g, h1, h2] using hq
        rw [hq']; exact ⟨(σ ⟨q₂.1.1, h2.1⟩).2, h2.2⟩
      · simpa [g, h1, h2] using hq
    have hmap : Finsupp.mapDomain g (ePad 1) = ePad σ := by
      dsimp only [ePad]
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      have hgy : g yIdx = yIdx := by simp [g, yIdx]; omega
      rw [hgy]
      congr 1
      change Finsupp.mapDomain.addMonoidHom g (∑ j : Fin n, Finsupp.single (emb (j, j)) 1) =
        ∑ j : Fin n, Finsupp.single (emb (σ j, j)) 1
      rw [map_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      simp [Finsupp.mapDomain.addMonoidHom, g, emb, j.2]
    have h2 := congrArg (fun p : MvPolynomial (Fin m × Fin m) ℂ ↦ p.coeff (ePad σ)) (hperm σ)
    rw [← hmap] at h2
    rw [MvPolynomial.coeff_rename_mapDomain g hg_inj f (ePad 1)] at h2
    rw [hmap] at h2
    exact h2.symm
  have hpad_exp : paddedPerm m n hnm = ∑ σ : Equiv.Perm (Fin n), monomial (ePad σ) (1 : ℂ) := by
    unfold paddedPerm Matrix.permanent
    rw [mul_sum]
    refine sum_congr rfl fun σ _ ↦ ?_
    simp only [Matrix.of_apply]
    change (X yIdx : MvPolynomial (Fin m × Fin m) ℂ) ^ (m - n) *
        (∏ j : Fin n, X (emb (σ j, j))) = monomial (ePad σ) 1
    rw [prod_X_eq_finsupp_prod univ (fun j ↦ emb (σ j, j)), monomial_eq, map_one, one_mul]
    simp only [ePad, Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
    congr 1
    have hsing : (Finsupp.single yIdx (m - n)).prod
        (fun p k ↦ (X p : MvPolynomial (Fin m × Fin m) ℂ) ^ k) = X yIdx ^ (m - n) :=
      Finsupp.prod_single_index (pow_zero _)
    exact hsing.symm
  refine ⟨c, ?_⟩
  rw [hpad_exp]
  ext e
  rw [coeff_C_mul, coeff_sum]
  simp only [coeff_monomial]
  by_cases he : e ∈ f.support
  · obtain ⟨hout, hy_val, hrow, hcol⟩ := hsupp e he
    let eB : Fin n × Fin n →₀ ℕ := Finsupp.onFinset univ (fun p ↦ e (emb p)) (fun _ _ ↦ mem_univ _)
    have heB_apply : ∀ p : Fin n × Fin n, eB p = e (emb p) := fun _ ↦ rfl
    obtain ⟨σ, hσ⟩ := exists_perm_of_row_col_sum_eq_one eB hrow hcol
    have he_eq : e = ePad σ := by
      ext q
      by_cases hq_y : q = yIdx
      · subst hq_y
        simp only [ePad, Finsupp.add_apply, Finsupp.single_apply, ↓reduceIte, finsupp_sum_apply]
        have h0 : (∑ j : Fin n, if emb (σ j, j) = yIdx then (1 : ℕ) else 0) = 0 :=
          sum_eq_zero fun j _ ↦ by
            have hne : emb (σ j, j) ≠ yIdx :=
              fun h ↦ hy_not_block (by rw [← h]; exact ⟨(σ j).2, j.2⟩)
            simp [hne]
        rw [h0, add_zero, hy_val]
      · by_cases hq_b : inBlock q
        · let p : Fin n × Fin n := (⟨q.1.1, hq_b.1⟩, ⟨q.2.1, hq_b.2⟩)
          have hq_emb : q = emb p := by ext <;> rfl
          rw [hq_emb]
          have hny : yIdx ≠ emb p := fun h ↦ hq_y (hq_emb.trans h.symm)
          simp only [ePad, Finsupp.add_apply, Finsupp.single_apply, hny, ↓reduceIte, zero_add,
            finsupp_sum_apply]
          have h1 := congrArg (fun d : Fin n × Fin n →₀ ℕ ↦ d p) hσ
          simp only [heB_apply, finsupp_sum_apply, Finsupp.single_apply] at h1
          rw [h1]
          refine sum_congr rfl fun j _ ↦ ?_
          by_cases hEq : (σ j, j) = p
          · simp [hEq]
          · have : emb (σ j, j) ≠ emb p := hemb_inj.ne hEq
            simp [hEq, this]
        · rw [hout q hq_b hq_y]
          simp only [ePad, Finsupp.add_apply, Finsupp.single_apply, Ne.symm hq_y, ↓reduceIte,
            zero_add, finsupp_sum_apply]
          symm
          exact sum_eq_zero fun j _ ↦ by
            have hne : emb (σ j, j) ≠ q := fun h ↦ hq_b (by rw [← h]; exact ⟨(σ j).2, j.2⟩)
            simp [hne]
    rw [he_eq, hcoeff_pad σ, sum_eq_single σ]
    · simp
    · intro τ _ hτσ; simp [hePad_inj.ne hτσ]
    · intro hσ; exact absurd (mem_univ σ) hσ
  · have hf0 : f.coeff e = 0 := notMem_support_iff.mp he
    rw [hf0]
    by_cases hperm_e : ∃ σ : Equiv.Perm (Fin n), ePad σ = e
    · obtain ⟨σ, rfl⟩ := hperm_e
      have hc0 : c = 0 := by rw [← hcoeff_pad σ]; exact hf0
      simp [hc0]
    · push Not at hperm_e
      have hsum0 : (∑ τ : Equiv.Perm (Fin n), if ePad τ = e then (1 : ℂ) else 0) = 0 :=
        sum_eq_zero fun τ _ ↦ by simp [hperm_e τ]
      simp [hsum0]



end CslibFrontier
