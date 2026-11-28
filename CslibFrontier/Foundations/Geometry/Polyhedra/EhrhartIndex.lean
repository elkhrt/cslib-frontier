module

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Foundations.Combinatorics.Quasipolynomial
public import CslibFrontier.Foundations.Geometry.Polyhedra.Polytope
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unimodular Smith Normal Form, Ehrhart Lattice Index, and Saturated Integer Feasibility

Develops unimodular Smith normal form diagonalization over `ℤ`, Ehrhart lattice-point counting
functions for subsets of `ℝ^d` with rational affine spans, and exact feasibility criteria for
saturated dilations:

- `UnimodularSNF` and `exists_unimodularSNF`: unimodular diagonalization `A * C * B = D` over `ℤ`
  via PID module bases;
- `ehrCount`, `ehrSeries`, `IsRationalAffineSpan`, and `snfIndex`, together with the intrinsic
  lattice characterization `snfIndex_dvd_iff_exists_intPoint_mem_affineSpan`;
- Dilation reduction (`ehrCount_eq_zero_of_not_dvd`, `ehrCount_mul_dilation`,
  `coeff_ehrSeries_eq_ite_dilation`);
- Relative-interior lattice density (`exists_intPoint_mem_dilation_mul`,
  `exists_pos_ehrCount_of_dvd`) and exact index/period identification
  (`ehrQuasipolynomial_index_eq_snfIndex`);
- Exact feasibility criterion above the saturation threshold
  (`ehrCount_pos_iff_index_dvd_of_saturated`), one-sided index test (`ehrCount_one_index_test`),
  and `#P` membership for polynomially encoded lattice-point counting families
  (`ehrCount_mem_sharpP`).
-/

public section

namespace CslibFrontier.Polyhedra

open CslibFrontier.Combinatorics
open scoped BigOperators Pointwise Polynomial PowerSeries

/-- A unimodular diagonalization `A * C * B = D` of an integer matrix
`C : Matrix (Fin m) (Fin d) ℤ` with `A ∈ GL_m(ℤ)` and `B ∈ GL_d(ℤ)`. -/
structure UnimodularSNF {m d : ℕ} (C : Matrix (Fin m) (Fin d) ℤ) where
  /-- Left unimodular factor `A ∈ GL_m(ℤ)`. -/
  A : Matrix (Fin m) (Fin m) ℤ
  /-- Inverse `A⁻¹ ∈ GL_m(ℤ)`. -/
  AInv : Matrix (Fin m) (Fin m) ℤ
  /-- Left-inverse identity `A * A⁻¹ = 1`. -/
  A_mul_AInv : A * AInv = 1
  /-- Right-inverse identity `A⁻¹ * A = 1`. -/
  AInv_mul_A : AInv * A = 1
  /-- Right unimodular factor `B ∈ GL_d(ℤ)`. -/
  B : Matrix (Fin d) (Fin d) ℤ
  /-- Inverse `B⁻¹ ∈ GL_d(ℤ)`. -/
  BInv : Matrix (Fin d) (Fin d) ℤ
  /-- Left-inverse identity `B * B⁻¹ = 1`. -/
  B_mul_BInv : B * BInv = 1
  /-- Right-inverse identity `B⁻¹ * B = 1`. -/
  BInv_mul_B : BInv * B = 1
  /-- Number of nonzero diagonal entries (rank of `C`). -/
  rank : ℕ
  /-- `rank ≤ m`. -/
  rank_le_m : rank ≤ m
  /-- `rank ≤ d`. -/
  rank_le_d : rank ≤ d
  /-- Nonzero diagonal entries `c_0, ..., c_{rank - 1} ∈ ℤ \ {0}`. -/
  diag : Fin rank → ℤ
  /-- Every diagonal entry is nonzero. -/
  diag_ne_zero : ∀ i, diag i ≠ 0
  /-- Diagonal form `(A * C * B)_{i, j}`. -/
  eq_diag : ∀ (i : Fin m) (j : Fin d),
    (A * C * B) i j = if h : i.1 = j.1 ∧ i.1 < rank then diag ⟨i.1, h.2⟩ else 0

private noncomputable def extendFinEmbedding {r m : ℕ} (hr_m : r ≤ m) (f : Fin r ↪ Fin m) :
    {σ : Equiv.Perm (Fin m) // ∀ i : Fin r, σ (Fin.castLE hr_m i) = f i} := by
  classical
  let p : Fin m → Prop := fun x ↦ x.1 < r
  let q : Fin m → Prop := fun y ↦ y ∈ Set.range f
  let e₁ : {x : Fin m // p x} ≃ {y : Fin m // q y} :=
    { toFun := fun x ↦ ⟨f ⟨x.1.1, x.2⟩, ⟨⟨x.1.1, x.2⟩, rfl⟩⟩
      invFun := fun y ↦ ⟨Fin.castLE hr_m (Classical.choose y.2), (Classical.choose y.2).2⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        apply Fin.ext
        dsimp only [Fin.val_castLE]
        have hch := Classical.choose_spec (⟨⟨x.1.1, x.2⟩, rfl⟩ : f ⟨x.1.1, x.2⟩ ∈ Set.range f)
        exact congrArg Fin.val (f.injective hch)
      right_inv := fun y ↦ by
        apply Subtype.ext
        exact Classical.choose_spec y.2 }
  have hcard_p : Fintype.card {x : Fin m // p x} = r := by
    refine Fintype.card_congr
      { toFun := fun x ↦ ⟨x.1.1, x.2⟩
        invFun := fun i ↦ ⟨Fin.castLE hr_m i, i.2⟩
        left_inv := fun x ↦ by ext; rfl
        right_inv := fun i ↦ by ext; rfl } |>.trans (Fintype.card_fin r)
  have hcard_q : Fintype.card {y : Fin m // q y} = r := by
    refine (Fintype.card_congr e₁.symm).trans hcard_p
  have hcard_compl : Fintype.card {x : Fin m // ¬ p x} = Fintype.card {y : Fin m // ¬ q y} := by
    have h1 := Fintype.card_subtype_compl p
    have h2 := Fintype.card_subtype_compl q
    omega
  let e₂ : {x : Fin m // ¬ p x} ≃ {y : Fin m // ¬ q y} := Fintype.equivOfCardEq hcard_compl
  let σ : Equiv.Perm (Fin m) :=
    (Equiv.sumCompl p).symm.trans ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl q))
  refine ⟨σ, fun i ↦ ?_⟩
  have hp : p (Fin.castLE hr_m i) := i.2
  change (Equiv.sumCompl q)
    ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl p).symm (Fin.castLE hr_m i))) = f i
  have hsymm : (Equiv.sumCompl p).symm (Fin.castLE hr_m i) = Sum.inl ⟨Fin.castLE hr_m i, hp⟩ := by
    apply (Equiv.sumCompl p).injective
    simp
  rw [hsymm]
  simp [e₁]

/-- Every integer matrix `C : Matrix (Fin m) (Fin d) ℤ` has a unimodular diagonalization
`A * C * B = D` with `A ∈ GL_m(ℤ)` and `B ∈ GL_d(ℤ)`. -/
theorem exists_unimodularSNF {m d : ℕ} (C : Matrix (Fin m) (Fin d) ℤ) :
    Nonempty (UnimodularSNF C) := by
  classical
  let e_m : Module.Basis (Fin m) ℤ (Fin m → ℤ) := Pi.basisFun ℤ (Fin m)
  let e_d : Module.Basis (Fin d) ℤ (Fin d → ℤ) := Pi.basisFun ℤ (Fin d)
  let f : (Fin d → ℤ) →ₗ[ℤ] (Fin m → ℤ) := C.mulVecLin
  let N : Submodule ℤ (Fin m → ℤ) := LinearMap.range f
  obtain ⟨r, snf⟩ := Submodule.smithNormalForm e_m N
  have hr_m : r ≤ m := by
    simpa using Fintype.card_le_of_injective snf.f snf.f.injective
  obtain ⟨σ, hσ⟩ := extendFinEmbedding hr_m snf.f
  let bM' : Module.Basis (Fin m) ℤ (Fin m → ℤ) := snf.bM.reindex σ.symm
  have hsnf' : ∀ i : Fin r, (snf.bN i : Fin m → ℤ) = snf.a i • bM' (Fin.castLE hr_m i) := by
    intro i
    have hre : bM' (Fin.castLE hr_m i) = snf.bM (σ (Fin.castLE hr_m i)) := by
      simp [bM']
    rw [hre, hσ i]
    exact snf.snf i
  have hdiag_ne : ∀ i : Fin r, snf.a i ≠ 0 := by
    intro i h0
    have hzero : (snf.bN i : Fin m → ℤ) = 0 := by rw [hsnf' i, h0, zero_smul]
    have hzeroN : snf.bN i = 0 := Subtype.ext hzero
    exact snf.bN.ne_zero i hzeroN
  have hu_ex : ∀ i : Fin r, ∃ u : Fin d → ℤ, f u = (snf.bN i : Fin m → ℤ) := fun i ↦ (snf.bN i).2
  choose u hu using hu_ex
  obtain ⟨k, bK⟩ := Submodule.basisOfPid e_d (LinearMap.ker f)
  let v : Fin r ⊕ Fin k → (Fin d → ℤ) := Sum.elim u (fun j ↦ (bK j : Fin d → ℤ))
  have hv_li : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : ∑ i : Fin r, g (Sum.inl i) • u i +
        ∑ j : Fin k, g (Sum.inr j) • (bK j : Fin d → ℤ) = 0 := by
      simpa [Fintype.sum_sum_type, v] using hg
    have hfsum : f (∑ i : Fin r, g (Sum.inl i) • u i +
        ∑ j : Fin k, g (Sum.inr j) • (bK j : Fin d → ℤ)) = 0 := by
      rw [hsum, map_zero]
    rw [map_add, map_sum, map_sum] at hfsum
    have hker0 : ∑ j : Fin k, f (g (Sum.inr j) • (bK j : Fin d → ℤ)) = 0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [map_smul, LinearMap.mem_ker.1 (bK j).2, smul_zero]
    rw [hker0, add_zero] at hfsum
    have hfN : ∑ i : Fin r, g (Sum.inl i) • snf.bN i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      simp_rw [map_smul, hu] at hfsum
      exact hfsum
    have hginl : ∀ i : Fin r, g (Sum.inl i) = 0 :=
      Fintype.linearIndependent_iff.1 snf.bN.linearIndependent _ hfN
    have hker_sum : ∑ j : Fin k, g (Sum.inr j) • bK j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      have h1 : ∑ i : Fin r, g (Sum.inl i) • u i = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by rw [hginl i, zero_smul]
      rw [h1, zero_add] at hsum
      exact hsum
    have hginr : ∀ j : Fin k, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.1 bK.linearIndependent _ hker_sum
    intro x
    rcases x with i | j
    · exact hginl i
    · exact hginr j
  have hv_span : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    let fxN : N := ⟨f x, ⟨x, rfl⟩⟩
    let c : Fin r → ℤ := fun i ↦ snf.bN.repr fxN i
    let y : Fin d → ℤ := x - ∑ i : Fin r, c i • u i
    have hy_ker : y ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, map_sum]
      have hrep : ∑ i : Fin r, f (c i • u i) = f x := by
        have h1 : ∑ i : Fin r, c i • snf.bN i = fxN := snf.bN.sum_repr fxN
        have h2 := congrArg Subtype.val h1
        simp only [Submodule.coe_sum, SetLike.val_smul] at h2
        simp_rw [map_smul, hu]
        exact h2
      rw [hrep, sub_self]
    let d_coeff : Fin k → ℤ := fun j ↦ bK.repr ⟨y, hy_ker⟩ j
    have hy_eq : y = ∑ j : Fin k, d_coeff j • (bK j : Fin d → ℤ) := by
      have h1 := congrArg Subtype.val (bK.sum_repr ⟨y, hy_ker⟩)
      simp only [Submodule.coe_sum, SetLike.val_smul] at h1
      exact h1.symm
    have hx_eq : x = ∑ i : Fin r, c i • v (Sum.inl i) + ∑ j : Fin k, d_coeff j • v (Sum.inr j) := by
      have : x = (∑ i : Fin r, c i • u i) + y := by simp [y]
      rw [this, hy_eq]
      rfl
    rw [hx_eq]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    · exact Submodule.sum_mem _ fun j _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  let bSum : Module.Basis (Fin r ⊕ Fin k) ℤ (Fin d → ℤ) := Module.Basis.mk hv_li hv_span
  have hrk : r + k = d := by
    have h1 := Module.finrank_eq_card_basis bSum
    have h2 := Module.finrank_eq_card_basis e_d
    simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
    omega
  have hr_d : r ≤ d := by omega
  let eSum : Fin r ⊕ Fin k ≃ Fin d :=
    { toFun := Sum.elim (Fin.castLE hr_d) (fun j ↦ ⟨r + j.1, by omega⟩)
      invFun := fun i ↦ if h : i.1 < r then Sum.inl ⟨i.1, h⟩ else Sum.inr ⟨i.1 - r, by omega⟩
      left_inv := fun x ↦ by
        rcases x with i | j
        · simp [i.2]
        · have hnot : ¬ r + j.1 < r := by omega
          simp only [Sum.elim_inr, hnot, ↓reduceDIte]
          congr 1; ext; dsimp; omega
      right_inv := fun i ↦ by
        by_cases h : i.1 < r
        · simp [h]
        · simp only [h, ↓reduceDIte, Sum.elim_inr]
          ext; dsimp; omega }
  let bD : Module.Basis (Fin d) ℤ (Fin d → ℤ) := bSum.reindex eSum
  let A : Matrix (Fin m) (Fin m) ℤ := bM'.toMatrix e_m
  let AInv : Matrix (Fin m) (Fin m) ℤ := e_m.toMatrix bM'
  let B : Matrix (Fin d) (Fin d) ℤ := e_d.toMatrix bD
  let BInv : Matrix (Fin d) (Fin d) ℤ := bD.toMatrix e_d
  refine ⟨{
    A := A
    AInv := AInv
    A_mul_AInv := bM'.toMatrix_mul_toMatrix_flip e_m
    AInv_mul_A := e_m.toMatrix_mul_toMatrix_flip bM'
    B := B
    BInv := BInv
    B_mul_BInv := e_d.toMatrix_mul_toMatrix_flip bD
    BInv_mul_B := bD.toMatrix_mul_toMatrix_flip e_d
    rank := r
    rank_le_m := hr_m
    rank_le_d := hr_d
    diag := snf.a
    diag_ne_zero := hdiag_ne
    eq_diag := fun i j ↦ ?_ }⟩
  have hcol : (A * C * B) i j = ((A * C * B).mulVec (Pi.single j 1)) i := by
    simp [Matrix.mulVec_single]
  rw [hcol, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hBcol : B.mulVec (Pi.single j 1) = bD j := by
    have hrepr : bD.repr (bD j) = Finsupp.single j (1 : ℤ) := bD.repr_self j
    have hmul := bD.toMatrix_mulVec_repr e_d (bD j)
    have hfun : (bD.repr (bD j) : Fin d → ℤ) = Pi.single j 1 := by
      ext t
      rw [hrepr]
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    have hed : (e_d.repr (bD j) : Fin d → ℤ) = bD j := by
      ext t; simp [e_d]
    rw [hfun, hed] at hmul
    exact hmul
  have hAapply : ∀ w : Fin m → ℤ, A.mulVec w = (bM'.repr w : Fin m → ℤ) := by
    intro w
    have hmul := e_m.toMatrix_mulVec_repr bM' w
    have hem : (e_m.repr w : Fin m → ℤ) = w := by
      ext t; simp [e_m]
    rw [hem] at hmul
    exact hmul
  rw [hBcol, hAapply]
  by_cases hj : j.1 < r
  · have hbDj : bD j = u ⟨j.1, hj⟩ := by
      have hs : eSum.symm j = Sum.inl ⟨j.1, hj⟩ := by simp [eSum, hj]
      simp [bD, bSum, hs, v]
    have hCbD : C.mulVec (bD j) = snf.a ⟨j.1, hj⟩ • bM' ⟨j.1, lt_of_lt_of_le hj hr_m⟩ := by
      rw [hbDj]
      change f (u ⟨j.1, hj⟩) = _
      rw [hu ⟨j.1, hj⟩, hsnf' ⟨j.1, hj⟩]
      rfl
    rw [hCbD, map_smul, bM'.repr_self]
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases hij : i.1 = j.1
    · have hfeq : (⟨j.1, lt_of_lt_of_le hj hr_m⟩ : Fin m) = i := by ext; exact hij.symm
      rw [ite_eq_left_iff.2 (fun h ↦ absurd hfeq h), mul_one]
      split_ifs
      · congr 1; ext; exact hij.symm
      · omega
    · have hfne : (⟨j.1, lt_of_lt_of_le hj hr_m⟩ : Fin m) ≠ i := by
        intro h; exact hij (congrArg Fin.val h).symm
      simp [hfne, hij]
  · have hbDj : bD j = (bK ⟨j.1 - r, by omega⟩ : Fin d → ℤ) := by
      have hs : eSum.symm j = Sum.inr ⟨j.1 - r, by omega⟩ := by simp [eSum, hj]
      simp [bD, bSum, hs, v]
    have hCbD : C.mulVec (bD j) = 0 := by
      rw [hbDj]
      exact LinearMap.mem_ker.1 (bK ⟨j.1 - r, by omega⟩).2
    rw [hCbD, map_zero]
    have hcond : ¬ (i.1 = j.1 ∧ i.1 < r) := by omega
    simp [hcond]

/-- Cast an integer lattice vector `z : Fin d → ℤ` into `Fin d → ℝ`. -/
def intPoint {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ :=
  fun i ↦ (z i : ℝ)

theorem intPoint_apply {d : ℕ} (z : Fin d → ℤ) (i : Fin d) :
    intPoint z i = (z i : ℝ) := by
  rfl

theorem intPoint_injective {d : ℕ} : Function.Injective (intPoint (d := d)) := by
  intro z₁ z₂ h
  ext i
  exact Int.cast_injective (congrFun h i)

theorem intPoint_zero {d : ℕ} : intPoint (0 : Fin d → ℤ) = 0 := by
  ext i; simp [intPoint]

theorem intPoint_add {d : ℕ} (z₁ z₂ : Fin d → ℤ) :
    intPoint (z₁ + z₂) = intPoint z₁ + intPoint z₂ := by
  ext i; simp [intPoint]

theorem intPoint_smul {d : ℕ} (k : ℤ) (z : Fin d → ℤ) :
    intPoint (k • z) = (k : ℝ) • intPoint z := by
  ext i; simp [intPoint]

theorem intPoint_nsmul {d : ℕ} (k : ℕ) (z : Fin d → ℤ) :
    intPoint (k • z) = (k : ℝ) • intPoint z := by
  ext i; simp [intPoint]

theorem intPoint_mulVec {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℤ) (z : Fin d → ℤ) :
    intPoint (M.mulVec z) = (M.map (Int.cast : ℤ → ℝ)).mulVec (intPoint z) := by
  ext i
  simp [intPoint, Matrix.mulVec, dotProduct]

/-- The Ehrhart lattice-point counting function `n ↦ |(n • P) ∩ ℤ^d|`. -/
noncomputable def ehrCount {d : ℕ} (P : Set (Fin d → ℝ)) (n : ℕ) : ℕ :=
  Nat.card {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • P}

theorem ehrCount_empty {d : ℕ} (n : ℕ) : ehrCount (∅ : Set (Fin d → ℝ)) n = 0 := by
  have hempty : IsEmpty {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • (∅ : Set (Fin d → ℝ))} := by
    refine ⟨fun ⟨_, hz⟩ ↦ ?_⟩
    rcases hz with ⟨_, hq, _⟩
    exact hq
  exact Nat.card_eq_zero.2 (Or.inl hempty)

/-- The formal Ehrhart generating series `∑_{n ≥ 0} ehrCount P n * X^n ∈ ℚ⟦X⟧`. -/
noncomputable def ehrSeries {d : ℕ} (P : Set (Fin d → ℝ)) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ (ehrCount P n : ℚ)

@[simp]
theorem coeff_ehrSeries {d : ℕ} (P : Set (Fin d → ℝ)) (n : ℕ) :
    PowerSeries.coeff n (ehrSeries P) = (ehrCount P n : ℚ) := by
  simp [ehrSeries]

/-- A bounded subset `P ⊆ ℝ^d` has finitely many integer lattice points in each dilation
`n • P`. -/
theorem finite_intPoints_of_isBounded {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : Bornology.IsBounded P) (n : ℕ) :
    Finite {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • P} := by
  obtain ⟨R, hR⟩ := hP.subset_closedBall (0 : Fin d → ℝ)
  set M : ℤ := Int.ceil ((n : ℝ) * max R 0)
  have hsub : ∀ z : {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • P},
      ∀ i : Fin d, z.1 i ∈ Set.Icc (-M) M := by
    intro ⟨z, hz⟩ i
    rcases hz with ⟨p, hp, hpeq⟩
    have hpR : ‖p‖ ≤ max R 0 := by
      have := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact le_trans this (le_max_left R 0)
    have hnorm : ‖intPoint z‖ ≤ (n : ℝ) * max R 0 := by
      rw [← hpeq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
      exact mul_le_mul_of_nonneg_left hpR (Nat.cast_nonneg n)
    have hi_le : |(z i : ℝ)| ≤ (n : ℝ) * max R 0 := by
      have hcoord := norm_le_pi_norm (intPoint z) i
      simpa [intPoint, Real.norm_eq_abs] using le_trans hcoord hnorm
    have hi_M : |(z i : ℝ)| ≤ (M : ℝ) := le_trans hi_le (Int.le_ceil _)
    have hpair := abs_le.1 hi_M
    exact ⟨by exact_mod_cast hpair.1, by exact_mod_cast hpair.2⟩
  let ι : {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • P} → (Fin d → Set.Icc (-M) M) :=
    fun z i ↦ ⟨z.1 i, hsub z i⟩
  have hinj : Function.Injective ι := by
    intro z₁ z₂ h
    ext i
    exact congrArg Subtype.val (congrFun h i)
  exact Finite.of_injective ι hinj

theorem ehrCount_pos_iff_exists {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : Bornology.IsBounded P) (n : ℕ) :
    0 < ehrCount P n ↔ ∃ z : Fin d → ℤ, intPoint z ∈ (n : ℝ) • P := by
  have hfin : Finite {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • P} :=
    finite_intPoints_of_isBounded hP n
  rw [ehrCount, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨z, hz⟩, _⟩; exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩; exact ⟨⟨⟨z, hz⟩⟩, hfin⟩

/-- `P ⊆ ℝ^d` has a rational affine span cut out by integer linear equations `C x = b`. -/
def IsRationalAffineSpan {m d : ℕ} (P : Set (Fin d → ℝ))
    (C : Matrix (Fin m) (Fin d) ℤ) (b : Fin m → ℤ) : Prop :=
  (affineSpan ℝ P : Set (Fin d → ℝ)) =
    {x : Fin d → ℝ | (C.map (Int.cast : ℤ → ℝ)).mulVec x = fun i ↦ (b i : ℝ)}

theorem isRationalAffineSpan_of_iff {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (h : ∀ x : Fin d → ℝ,
      x ∈ affineSpan ℝ P ↔ (C.map (Int.cast : ℤ → ℝ)).mulVec x = fun i ↦ (b i : ℝ)) :
    IsRationalAffineSpan P C b := by
  ext x
  exact h x

theorem mem_affineSpan_iff_of_isRationalAffineSpan {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (h : IsRationalAffineSpan P C b) (x : Fin d → ℝ) :
    x ∈ affineSpan ℝ P ↔ (C.map (Int.cast : ℤ → ℝ)).mulVec x = fun i ↦ (b i : ℝ) := by
  rw [← SetLike.mem_coe, h]
  rfl

/-- The Smith-normal-form lattice index `lcm_i (|c_i| / gcd(|c_i|, |(A b)_i|))`. -/
def snfIndex {m d : ℕ} {C : Matrix (Fin m) (Fin d) ℤ}
    (snf : UnimodularSNF C) (b : Fin m → ℤ) : ℕ :=
  Finset.univ.lcm fun i : Fin snf.rank ↦
    let ci := (snf.diag i).natAbs
    let di := (snf.A.mulVec b ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩).natAbs
    ci / Nat.gcd ci di

theorem snfIndex_pos {m d : ℕ} {C : Matrix (Fin m) (Fin d) ℤ}
    (snf : UnimodularSNF C) (b : Fin m → ℤ) : 0 < snfIndex snf b := by
  refine Nat.pos_of_ne_zero fun h0 ↦ ?_
  unfold snfIndex at h0
  rw [Finset.lcm_eq_zero_iff] at h0
  rcases h0 with ⟨i, _, hi⟩
  have hci : 0 < (snf.diag i).natAbs := Int.natAbs_pos.2 (snf.diag_ne_zero i)
  have hgcd_pos : 0 < Nat.gcd (snf.diag i).natAbs
      (snf.A.mulVec b ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩).natAbs :=
    Nat.gcd_pos_of_pos_left _ hci
  have hgcd_le : Nat.gcd (snf.diag i).natAbs
      (snf.A.mulVec b ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩).natAbs ≤ (snf.diag i).natAbs :=
    Nat.le_of_dvd hci (Nat.gcd_dvd_left _ _)
  have hdiv_pos : 0 < (snf.diag i).natAbs / Nat.gcd (snf.diag i).natAbs
      (snf.A.mulVec b ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩).natAbs :=
    Nat.div_pos hgcd_le hgcd_pos
  exact Nat.ne_of_gt hdiv_pos hi

private lemma int_dvd_nat_mul_iff {c d : ℤ} (hc : c ≠ 0) (n : ℕ) :
    c ∣ (n : ℤ) * d ↔ (c.natAbs / Nat.gcd c.natAbs d.natAbs) ∣ n := by
  have hc_pos : 0 < c.natAbs := Int.natAbs_pos.2 hc
  set g := Nat.gcd c.natAbs d.natAbs
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hc_pos
  have hcop : Nat.Coprime (c.natAbs / g) (d.natAbs / g) :=
    Nat.coprime_div_gcd_div_gcd hg_pos
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
  have hce : c.natAbs = g * (c.natAbs / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hde : d.natAbs = g * (d.natAbs / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  calc
    c.natAbs ∣ n * d.natAbs
        ↔ g * (c.natAbs / g) ∣ g * (n * (d.natAbs / g)) := by
          rw [← hce, ← mul_assoc, mul_comm g n, mul_assoc, ← hde]
    _ ↔ (c.natAbs / g) ∣ n * (d.natAbs / g) := mul_dvd_mul_iff_left (Nat.ne_of_gt hg_pos)
    _ ↔ (c.natAbs / g) ∣ n := by
      constructor
      · intro h
        exact hcop.dvd_of_dvd_mul_right h
      · intro h
        exact dvd_mul_of_dvd_left h _

private lemma map_cast_mul {m k n : ℕ} (M : Matrix (Fin m) (Fin k) ℤ)
    (N : Matrix (Fin k) (Fin n) ℤ) :
    (M * N).map (Int.cast : ℤ → ℝ) = M.map (Int.cast : ℤ → ℝ) * N.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [Matrix.mul_apply]

private lemma map_cast_one {m : ℕ} :
    ((1 : Matrix (Fin m) (Fin m) ℤ)).map (Int.cast : ℤ → ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma snf_A_mulVec_b_eq_zero_of_ge {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (haff : IsRationalAffineSpan P C b)
    (snf : UnimodularSNF C) {i : Fin m} (hi : snf.rank ≤ i.1) :
    snf.A.mulVec b i = 0 := by
  rcases hPne with ⟨x, hxP⟩
  have hx_aff : x ∈ (affineSpan ℝ P : Set (Fin d → ℝ)) := subset_affineSpan ℝ P hxP
  rw [haff] at hx_aff
  have hx_eq : (C.map (Int.cast : ℤ → ℝ)).mulVec x = intPoint b := hx_aff
  let A_R := snf.A.map (Int.cast : ℤ → ℝ)
  let B_R := snf.B.map (Int.cast : ℤ → ℝ)
  let BInv_R := snf.BInv.map (Int.cast : ℤ → ℝ)
  let C_R := C.map (Int.cast : ℤ → ℝ)
  have hBB : B_R * BInv_R = 1 := by
    rw [← map_cast_mul, snf.B_mul_BInv, map_cast_one]
  have hACB : (A_R * C_R * B_R).mulVec (BInv_R.mulVec x) = intPoint (snf.A.mulVec b) := by
    calc
      (A_R * C_R * B_R).mulVec (BInv_R.mulVec x)
          = (A_R * C_R * B_R * BInv_R).mulVec x := by rw [Matrix.mulVec_mulVec]
      _ = (A_R * C_R * (B_R * BInv_R)).mulVec x := by rw [Matrix.mul_assoc (A_R * C_R)]
      _ = (A_R * C_R).mulVec x := by rw [hBB, Matrix.mul_one]
      _ = A_R.mulVec (C_R.mulVec x) := by rw [← Matrix.mulVec_mulVec]
      _ = intPoint (snf.A.mulVec b) := by rw [hx_eq, ← intPoint_mulVec]
  have hi_eq := congrFun hACB i
  have hlhs0 : ((A_R * C_R * B_R).mulVec (BInv_R.mulVec x)) i = 0 := by
    have hmap : A_R * C_R * B_R = (snf.A * C * snf.B).map (Int.cast : ℤ → ℝ) := by
      simp only [A_R, B_R, C_R, ← map_cast_mul]
    rw [hmap, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hnot : ¬ (i.1 = j.1 ∧ i.1 < snf.rank) := by omega
    simp [snf.eq_diag i j, hnot]
  rw [hlhs0] at hi_eq
  simpa [intPoint] using hi_eq.symm

/-- Intrinsic lattice characterization: `snfIndex snf b ∣ n` if and only if the dilated affine
span `n • aff(P)` contains an integer lattice point `z ∈ ℤ^d`. -/
theorem snfIndex_dvd_iff_exists_intPoint_mem_affineSpan {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (haff : IsRationalAffineSpan P C b)
    (snf : UnimodularSNF C) (n : ℕ) :
    snfIndex snf b ∣ n ↔
      ∃ z : Fin d → ℤ, intPoint z ∈ (n : ℝ) • (affineSpan ℝ P : Set (Fin d → ℝ)) := by
  by_cases hn0 : n = 0
  · subst hn0
    constructor
    · intro _
      rcases hPne with ⟨x, hx⟩
      exact ⟨0, x, subset_affineSpan ℝ P hx, by simp [intPoint_zero]⟩
    · intro _; exact dvd_zero _
  · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hmem_iff : ∀ z : Fin d → ℤ,
        intPoint z ∈ (n : ℝ) • (affineSpan ℝ P : Set (Fin d → ℝ)) ↔ C.mulVec z = (n : ℤ) • b := by
      intro z
      constructor
      · rintro ⟨x, hx, hxeq⟩
        rw [haff] at hx
        have hCx : (C.map (Int.cast : ℤ → ℝ)).mulVec x = intPoint b := hx
        have hCz : (C.map (Int.cast : ℤ → ℝ)).mulVec (intPoint z) = (n : ℝ) • intPoint b := by
          rw [← hxeq, Matrix.mulVec_smul, hCx]
        rw [← intPoint_mulVec, ← intPoint_nsmul] at hCz
        have hz_eq := intPoint_injective hCz
        simpa using hz_eq
      · intro hCz
        refine ⟨(n : ℝ)⁻¹ • intPoint z, ?_, by dsimp; rw [smul_inv_smul₀ hn_ne]⟩
        rw [haff]
        change (C.map (Int.cast : ℤ → ℝ)).mulVec ((n : ℝ)⁻¹ • intPoint z) = intPoint b
        rw [Matrix.mulVec_smul, ← intPoint_mulVec, hCz, intPoint_smul]
        ext i
        simp [intPoint, inv_mul_cancel_left₀ hn_ne]
    simp_rw [hmem_iff]
    constructor
    · intro hdvd
      unfold snfIndex at hdvd
      have hall : ∀ i : Fin snf.rank,
          snf.diag i ∣ (n : ℤ) * snf.A.mulVec b ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩ := by
        intro i
        rw [int_dvd_nat_mul_iff (snf.diag_ne_zero i) n]
        have hstep : (snf.diag i).natAbs / Nat.gcd (snf.diag i).natAbs
            (snf.A.mulVec b ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩).natAbs ∣
            Finset.univ.lcm (fun t : Fin snf.rank ↦
              (snf.diag t).natAbs / Nat.gcd (snf.diag t).natAbs
                (snf.A.mulVec b ⟨t.1, lt_of_lt_of_le t.2 snf.rank_le_m⟩).natAbs) :=
          Finset.dvd_lcm (f := fun t : Fin snf.rank ↦
            (snf.diag t).natAbs / Nat.gcd (snf.diag t).natAbs
              (snf.A.mulVec b ⟨t.1, lt_of_lt_of_le t.2 snf.rank_le_m⟩).natAbs) (Finset.mem_univ i)
        exact dvd_trans hstep hdvd
      choose q hq using hall
      let y : Fin d → ℤ := fun j ↦ if h : j.1 < snf.rank then q ⟨j.1, h⟩ else 0
      refine ⟨snf.B.mulVec y, ?_⟩
      have hACBy : (snf.A * C * snf.B).mulVec y = (n : ℤ) • snf.A.mulVec b := by
        ext i
        rw [Matrix.mulVec, dotProduct]
        by_cases hi : i.1 < snf.rank
        · have hj_mem : (⟨i.1, lt_of_lt_of_le hi snf.rank_le_d⟩ : Fin d) ∈ Finset.univ :=
            Finset.mem_univ _
          rw [Finset.sum_eq_single (⟨i.1, lt_of_lt_of_le hi snf.rank_le_d⟩ : Fin d)]
          · simp only [snf.eq_diag, hi, and_self, ↓reduceDIte, y, Pi.smul_apply, smul_eq_mul]
            exact (hq ⟨i.1, hi⟩).symm
          · intro j _ hjne
            have hne : i.1 ≠ j.1 := fun heq ↦ hjne (by ext; exact heq.symm)
            simp [snf.eq_diag, hne]
          · intro hnot; exact absurd hj_mem hnot
        · have hzero : snf.A.mulVec b i = 0 :=
            snf_A_mulVec_b_eq_zero_of_ge hPne haff snf (Nat.le_of_not_lt hi)
          simp only [Pi.smul_apply, smul_eq_mul, hzero, mul_zero]
          refine Finset.sum_eq_zero fun j _ ↦ ?_
          have hnot : ¬ (i.1 = j.1 ∧ i.1 < snf.rank) := by omega
          simp [snf.eq_diag, hnot]
      calc
        C.mulVec (snf.B.mulVec y)
            = (snf.AInv * (snf.A * C * snf.B)).mulVec y := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, snf.AInv_mul_A, Matrix.one_mul,
                Matrix.mulVec_mulVec]
        _ = snf.AInv.mulVec ((snf.A * C * snf.B).mulVec y) := by rw [← Matrix.mulVec_mulVec]
        _ = snf.AInv.mulVec ((n : ℤ) • snf.A.mulVec b) := by rw [hACBy]
        _ = (n : ℤ) • (snf.AInv * snf.A).mulVec b := by
              rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        _ = (n : ℤ) • b := by rw [snf.AInv_mul_A, Matrix.one_mulVec]
    · rintro ⟨z, hz⟩
      unfold snfIndex
      refine Finset.lcm_dvd fun i _ ↦ ?_
      rw [← int_dvd_nat_mul_iff (snf.diag_ne_zero i) n]
      let y : Fin d → ℤ := snf.BInv.mulVec z
      have hACBy : (snf.A * C * snf.B).mulVec y = (n : ℤ) • snf.A.mulVec b := by
        calc
          (snf.A * C * snf.B).mulVec y
              = (snf.A * C * (snf.B * snf.BInv)).mulVec z := by
                simp only [y, Matrix.mulVec_mulVec, Matrix.mul_assoc]
          _ = (snf.A * C).mulVec z := by rw [snf.B_mul_BInv, Matrix.mul_one]
          _ = snf.A.mulVec (C.mulVec z) := by rw [← Matrix.mulVec_mulVec]
          _ = (n : ℤ) • snf.A.mulVec b := by rw [hz, Matrix.mulVec_smul]
      let im : Fin m := ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_m⟩
      let id_fin : Fin d := ⟨i.1, lt_of_lt_of_le i.2 snf.rank_le_d⟩
      have hrow := congrFun hACBy im
      have hlhs : ((snf.A * C * snf.B).mulVec y) im = snf.diag i * y id_fin := by
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single id_fin]
        · simp [snf.eq_diag, im, id_fin, i.2]
        · intro j _ hjne
          have hne : im.1 ≠ j.1 := fun heq ↦ hjne (by ext; exact heq.symm)
          simp [snf.eq_diag, hne]
        · intro hnot; exact absurd (Finset.mem_univ id_fin) hnot
      rw [hlhs] at hrow
      exact ⟨y id_fin, by simpa [im] using hrow.symm⟩

/-- If `snfIndex snf b` does not divide `n`, then `n • P` contains no integer lattice points. -/
theorem ehrCount_eq_zero_of_not_dvd {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (haff : IsRationalAffineSpan P C b)
    (snf : UnimodularSNF C) {n : ℕ} (hndvd : ¬ snfIndex snf b ∣ n) :
    ehrCount P n = 0 := by
  have hempty : IsEmpty {z : Fin d → ℤ // intPoint z ∈ (n : ℝ) • P} := by
    refine ⟨fun ⟨z, hz⟩ ↦ hndvd ?_⟩
    rw [snfIndex_dvd_iff_exists_intPoint_mem_affineSpan hPne haff snf n]
    refine ⟨z, Set.smul_set_mono (subset_affineSpan ℝ P) hz⟩
  exact Nat.card_eq_zero.2 (Or.inl hempty)

/-- Dilation scaling of lattice-point counts: `ehrCount P (k * j) = ehrCount (j • P) k`. -/
theorem ehrCount_mul_dilation {d : ℕ} (P : Set (Fin d → ℝ)) (j k : ℕ) :
    ehrCount P (k * j) = ehrCount ((j : ℝ) • P) k := by
  unfold ehrCount
  have hset : ((k * j : ℕ) : ℝ) • P = (k : ℝ) • ((j : ℝ) • P) := by
    rw [Nat.cast_mul, mul_smul]
  rw [hset]

/-- Power-series dilation reduction: `ehrSeries P` is supported on multiples of `j = snfIndex snf b`
and equals `ehrSeries (j • P)` evaluated at `X^j`. -/
theorem coeff_ehrSeries_eq_ite_dilation {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (haff : IsRationalAffineSpan P C b)
    (snf : UnimodularSNF C) (n : ℕ) :
    PowerSeries.coeff n (ehrSeries P) =
      if snfIndex snf b ∣ n then
        PowerSeries.coeff (n / snfIndex snf b) (ehrSeries ((snfIndex snf b : ℝ) • P))
      else 0 := by
  simp only [coeff_ehrSeries]
  by_cases hd : snfIndex snf b ∣ n
  · simp only [hd, ↓reduceIte]
    have hmul : n / snfIndex snf b * snfIndex snf b = n := Nat.div_mul_cancel hd
    rw [← ehrCount_mul_dilation P (snfIndex snf b) (n / snfIndex snf b), hmul]
  · simp only [hd, ↓reduceIte, ehrCount_eq_zero_of_not_dvd hPne haff snf hd, Nat.cast_zero]

/-- For any nonempty convex `P ⊆ ℝ^d` with rational affine span `C x = b` and
`j = snfIndex snf b`, all sufficiently large multiples `k * j` contain an integer point in
`(k * j) • P`. -/
theorem exists_intPoint_mem_dilation_mul {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (haff : IsRationalAffineSpan P C b)
    (snf : UnimodularSNF C) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∃ z : Fin d → ℤ, intPoint z ∈ ((k * snfIndex snf b : ℕ) : ℝ) • P := by
  set j := snfIndex snf b
  have hj_pos : 0 < j := snfIndex_pos snf b
  have hj_real : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj_pos
  have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_real
  obtain ⟨z₀, hz₀⟩ :=
    (snfIndex_dvd_iff_exists_intPoint_mem_affineSpan hPne haff snf j).1 (dvd_refl j)
  have hCz₀ : (C.map (Int.cast : ℤ → ℝ)).mulVec (intPoint z₀) = (j : ℝ) • intPoint b := by
    rcases hz₀ with ⟨x, hx, hxeq⟩
    rw [haff] at hx
    have hCx : (C.map (Int.cast : ℤ → ℝ)).mulVec x = intPoint b := hx
    rw [← hxeq, Matrix.mulVec_smul, hCx]
  let A_R := snf.A.map (Int.cast : ℤ → ℝ)
  let AInv_R := snf.AInv.map (Int.cast : ℤ → ℝ)
  let B_R := snf.B.map (Int.cast : ℤ → ℝ)
  let BInv_R := snf.BInv.map (Int.cast : ℤ → ℝ)
  let C_R := C.map (Int.cast : ℤ → ℝ)
  have hAAInv : A_R * AInv_R = 1 := by rw [← map_cast_mul, snf.A_mul_AInv, map_cast_one]
  have hAInvA : AInv_R * A_R = 1 := by rw [← map_cast_mul, snf.AInv_mul_A, map_cast_one]
  have hBBInv : B_R * BInv_R = 1 := by rw [← map_cast_mul, snf.B_mul_BInv, map_cast_one]
  have hBInvB : BInv_R * B_R = 1 := by rw [← map_cast_mul, snf.BInv_mul_B, map_cast_one]
  have hACB_map : A_R * C_R * B_R = (snf.A * C * snf.B).map (Int.cast : ℤ → ℝ) := by
    simp only [A_R, B_R, C_R, ← map_cast_mul]
  set r := snf.rank
  have hr_d : r ≤ d := snf.rank_le_d
  let projLin : (Fin d → ℝ) →ₗ[ℝ] (Fin (d - r) → ℝ) :=
    { toFun := fun x t ↦ (BInv_R.mulVec x) ⟨r + t.1, by omega⟩
      map_add' := fun x y ↦ by ext t; simp [Matrix.mulVec_add]
      map_smul' := fun c x ↦ by ext t; simp [Matrix.mulVec_smul] }
  let φ : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d - r) → ℝ) :=
    { toFun := fun x ↦ projLin (x - intPoint z₀)
      linear := projLin
      map_vadd' := fun x v ↦ by
        simp only [vadd_eq_add, add_sub_assoc, map_add] }
  let Pbar : Set (Fin d → ℝ) := (j : ℝ) • P
  let Q₂ : Set (Fin (d - r) → ℝ) := φ '' Pbar
  have hPbar_conv : Convex ℝ Pbar := hPconv.smul (j : ℝ)
  have hQ₂_conv : Convex ℝ Q₂ := hPbar_conv.affine_image φ
  have hQ₂_span : affineSpan ℝ Q₂ = ⊤ := by
    rw [eq_top_iff]
    intro w _
    let y : Fin d → ℝ := fun i ↦ if h : r ≤ i.1 then w ⟨i.1 - r, by omega⟩ else 0
    let x : Fin d → ℝ := B_R.mulVec y + intPoint z₀
    have hCBy : C_R.mulVec (B_R.mulVec y) = 0 := by
      have hACBy : (A_R * C_R * B_R).mulVec y = 0 := by
        ext i
        rw [hACB_map, Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun t _ ↦ ?_
        by_cases htr : t.1 < r
        · have hy0 : y t = 0 := by
            have : ¬ r ≤ t.1 := by omega
            simp [y, this]
          simp [hy0]
        · have hnot : ¬ (i.1 = t.1 ∧ i.1 < snf.rank) := by omega
          simp [snf.eq_diag, hnot]
      calc
        C_R.mulVec (B_R.mulVec y)
            = (AInv_R * (A_R * C_R * B_R)).mulVec y := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAInvA, Matrix.one_mul,
                Matrix.mulVec_mulVec]
        _ = AInv_R.mulVec ((A_R * C_R * B_R).mulVec y) := by rw [← Matrix.mulVec_mulVec]
        _ = 0 := by rw [hACBy, Matrix.mulVec_zero]
    have hCx : C_R.mulVec ((j : ℝ)⁻¹ • x) = intPoint b := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_add, hCBy, zero_add, hCz₀, inv_smul_smul₀ hj_ne]
    have hx_mem_affP : (j : ℝ)⁻¹ • x ∈ affineSpan ℝ P := by
      change (j : ℝ)⁻¹ • x ∈ (affineSpan ℝ P : Set (Fin d → ℝ))
      rw [haff]
      exact hCx
    let ψ : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d - r) → ℝ) :=
      φ.comp (AffineMap.homothety (0 : Fin d → ℝ) (j : ℝ))
    have hψ_im : ψ '' P = Q₂ := by
      ext u
      simp only [Set.mem_image, ψ, Q₂, Pbar, AffineMap.coe_comp, Function.comp_apply,
        AffineMap.homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]
      constructor
      · rintro ⟨p, hp, rfl⟩; exact ⟨(j : ℝ) • p, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨p, hp, rfl⟩
    have hmap : ψ ((j : ℝ)⁻¹ • x) ∈ (affineSpan ℝ P).map ψ :=
      AffineSubspace.mem_map.2 ⟨(j : ℝ)⁻¹ • x, hx_mem_affP, rfl⟩
    rw [AffineSubspace.map_span, hψ_im] at hmap
    have hψ_eq : ψ ((j : ℝ)⁻¹ • x) = w := by
      have hhom : AffineMap.homothety (0 : Fin d → ℝ) (j : ℝ) ((j : ℝ)⁻¹ • x) = x := by
        simp [AffineMap.homothety_apply, smul_inv_smul₀ hj_ne]
      change φ (AffineMap.homothety (0 : Fin d → ℝ) (j : ℝ) ((j : ℝ)⁻¹ • x)) = w
      rw [hhom]
      ext t
      have hsub : x - intPoint z₀ = B_R.mulVec y := by simp [x]
      simp only [φ, AffineMap.coe_mk, projLin, LinearMap.coe_mk, AddHom.coe_mk, hsub,
        Matrix.mulVec_mulVec, hBInvB, Matrix.one_mulVec]
      have hge : r ≤ r + t.1 := Nat.le_add_right r t.1
      simp only [y, hge, ↓reduceDIte]
      congr 1; ext; dsimp; omega
    rwa [hψ_eq] at hmap
  have hint : (interior Q₂).Nonempty :=
    (hQ₂_conv.interior_nonempty_iff_affineSpan_eq_top).2 hQ₂_span
  rcases hint with ⟨y₀, hy₀⟩
  obtain ⟨ε, hε_pos, hball_int⟩ := Metric.isOpen_iff.1 isOpen_interior y₀ hy₀
  have hball : Metric.ball y₀ ε ⊆ Q₂ := hball_int.trans interior_subset
  refine ⟨Nat.ceil (1 / ε) + 1, fun k hk ↦ ?_⟩
  have hk_pos : 0 < k := by omega
  have hk_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_real
  have h1k_lt : (1 : ℝ) / (k : ℝ) < ε := by
    have hceil : 1 / ε < (k : ℝ) := by
      have h1 : (Nat.ceil (1 / ε) : ℝ) < (k : ℝ) := by
        exact_mod_cast (show Nat.ceil (1 / ε) < k by omega)
      exact lt_of_le_of_lt (Nat.le_ceil _) h1
    rw [div_lt_iff₀ hk_real]
    have := (div_lt_iff₀ hε_pos).1 hceil
    linarith
  let wZ : Fin (d - r) → ℤ := fun t ↦ Int.floor ((k : ℝ) * y₀ t)
  let wR : Fin (d - r) → ℝ := (k : ℝ)⁻¹ • intPoint wZ
  have hwR_mem : wR ∈ Q₂ := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε_pos]
    intro t
    rw [Real.dist_eq]
    have hfl1 : (wZ t : ℝ) ≤ (k : ℝ) * y₀ t := Int.floor_le _
    have hfl2 : (k : ℝ) * y₀ t < (wZ t : ℝ) + 1 := Int.lt_floor_add_one _
    have habs : |(wZ t : ℝ) / (k : ℝ) - y₀ t| < 1 / (k : ℝ) := by
      rw [abs_lt]
      have hsub1 : -(1 : ℝ) < (wZ t : ℝ) - (k : ℝ) * y₀ t := by linarith
      have hsub2 : (wZ t : ℝ) - (k : ℝ) * y₀ t ≤ 0 := by linarith
      have hdiv1 : -(1 : ℝ) / (k : ℝ) < ((wZ t : ℝ) - (k : ℝ) * y₀ t) / (k : ℝ) :=
        div_lt_div_of_pos_right hsub1 hk_real
      have hdiv2 : ((wZ t : ℝ) - (k : ℝ) * y₀ t) / (k : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hsub2 (le_of_lt hk_real)
      have heq : ((wZ t : ℝ) - (k : ℝ) * y₀ t) / (k : ℝ) = (wZ t : ℝ) / (k : ℝ) - y₀ t := by
        rw [sub_div, mul_div_cancel_left₀ _ hk_ne]
      rw [heq] at hdiv1 hdiv2
      rw [neg_div] at hdiv1
      have hpos1k : (0 : ℝ) < 1 / (k : ℝ) := div_pos zero_lt_one hk_real
      constructor <;> linarith
    have hwRt : wR t = (wZ t : ℝ) / (k : ℝ) := by
      simp [wR, intPoint, div_eq_inv_mul]
    rw [hwRt]
    exact lt_trans habs h1k_lt
  rcases hwR_mem with ⟨q, ⟨p, hpP, rfl⟩, hφq⟩
  let yZ : Fin d → ℤ := fun i ↦ if h : r ≤ i.1 then wZ ⟨i.1 - r, by omega⟩ else 0
  let z : Fin d → ℤ := snf.B.mulVec yZ + k • z₀
  have hu0 : BInv_R.mulVec ((j : ℝ) • p - intPoint z₀) = (k : ℝ)⁻¹ • intPoint yZ := by
    have hdiffC : C_R.mulVec ((j : ℝ) • p - intPoint z₀) = 0 := by
      have hp_aff : p ∈ (affineSpan ℝ P : Set (Fin d → ℝ)) := subset_affineSpan ℝ P hpP
      rw [haff] at hp_aff
      have hCp : C_R.mulVec p = intPoint b := hp_aff
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hCp, hCz₀, sub_self]
    have hACB_zero :
        (A_R * C_R * B_R).mulVec (BInv_R.mulVec ((j : ℝ) • p - intPoint z₀)) = 0 := by
      calc
        (A_R * C_R * B_R).mulVec (BInv_R.mulVec ((j : ℝ) • p - intPoint z₀))
            = (A_R * C_R * B_R * BInv_R).mulVec ((j : ℝ) • p - intPoint z₀) := by
              rw [Matrix.mulVec_mulVec]
        _ = (A_R * C_R * (B_R * BInv_R)).mulVec ((j : ℝ) • p - intPoint z₀) := by
              rw [Matrix.mul_assoc (A_R * C_R)]
        _ = (A_R * C_R).mulVec ((j : ℝ) • p - intPoint z₀) := by
              rw [hBBInv, Matrix.mul_one]
        _ = A_R.mulVec (C_R.mulVec ((j : ℝ) • p - intPoint z₀)) := by
              rw [← Matrix.mulVec_mulVec]
        _ = 0 := by rw [hdiffC, Matrix.mulVec_zero]
    ext i
    by_cases hir : i.1 < r
    · have hyZ0 : yZ i = 0 := by
        have : ¬ r ≤ i.1 := by omega
        simp [yZ, this]
      simp only [Pi.smul_apply, smul_eq_mul, intPoint, hyZ0, Int.cast_zero, mul_zero]
      let im : Fin m := ⟨i.1, lt_of_lt_of_le hir snf.rank_le_m⟩
      have hrow := congrFun hACB_zero im
      have hlhs : ((A_R * C_R * B_R).mulVec (BInv_R.mulVec ((j : ℝ) • p - intPoint z₀))) im =
          (snf.diag ⟨i.1, hir⟩ : ℝ) * (BInv_R.mulVec ((j : ℝ) • p - intPoint z₀)) i := by
        rw [hACB_map, Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
        · have hir' : i.1 < snf.rank := hir
          simp [snf.eq_diag, im, hir']
        · intro t _ hti
          have hne : im.1 ≠ t.1 := fun h ↦ hti (by ext; exact h.symm)
          simp [snf.eq_diag, hne]
        · intro hnot; exact absurd (Finset.mem_univ i) hnot
      rw [hlhs] at hrow
      have hdiag_ne : (snf.diag ⟨i.1, hir⟩ : ℝ) ≠ 0 := by
        exact_mod_cast snf.diag_ne_zero ⟨i.1, hir⟩
      exact (mul_eq_zero.1 hrow).resolve_left hdiag_ne
    · have hge : r ≤ i.1 := Nat.le_of_not_lt hir
      let t : Fin (d - r) := ⟨i.1 - r, by omega⟩
      have hrow := congrFun hφq t
      have hi_eq : (⟨r + t.1, by omega⟩ : Fin d) = i := by ext; simp [t]; omega
      simpa [φ, projLin, wR, yZ, hge, t, hi_eq, intPoint] using hrow
  have hjp : (j : ℝ) • p = B_R.mulVec ((k : ℝ)⁻¹ • intPoint yZ) + intPoint z₀ := by
    have hmul := congrArg B_R.mulVec hu0
    rw [Matrix.mulVec_mulVec, hBBInv, Matrix.one_mulVec] at hmul
    rw [← hmul]
    abel
  refine ⟨z, p, hpP, ?_⟩
  calc
    ((k * j : ℕ) : ℝ) • p = (k : ℝ) • ((j : ℝ) • p) := by rw [Nat.cast_mul, mul_smul]
    _ = (k : ℝ) • (B_R.mulVec ((k : ℝ)⁻¹ • intPoint yZ) + intPoint z₀) := by rw [hjp]
    _ = B_R.mulVec (intPoint yZ) + (k : ℝ) • intPoint z₀ := by
      rw [smul_add, ← Matrix.mulVec_smul, smul_inv_smul₀ hk_ne]
    _ = intPoint z := by
      simp only [z, intPoint_add, intPoint_mulVec, intPoint_nsmul, B_R]

/-- Bounded convex version: `0 < ehrCount P (k * snfIndex snf b)` for all sufficiently large `k`. -/
theorem exists_pos_ehrCount_of_dvd {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPbdd : Bornology.IsBounded P)
    (haff : IsRationalAffineSpan P C b) (snf : UnimodularSNF C) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → 0 < ehrCount P (k * snfIndex snf b) := by
  obtain ⟨K₀, hK₀⟩ := exists_intPoint_mem_dilation_mul hPne hPconv haff snf
  exact ⟨K₀, fun k hk ↦ (ehrCount_pos_iff_exists hPbdd _).2 (hK₀ k hk)⟩

/-- For any nonempty bounded convex `P ⊆ ℝ^d` with rational affine span `C x = b` whose Ehrhart
counting function agrees with a quasipolynomial `f`, `snfIndex snf b ∣ f.period`,
`f.constituentMod i ≠ 0 ↔ snfIndex snf b ∣ i`, and `f.index = snfIndex snf b`. -/
theorem ehrQuasipolynomial_index_eq_snfIndex {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPbdd : Bornology.IsBounded P)
    (haff : IsRationalAffineSpan P C b) (snf : UnimodularSNF C)
    {f : Quasipolynomial} (hf : ∀ n : ℕ, f.eval n = (ehrCount P n : ℚ)) :
    snfIndex snf b ∣ f.period ∧
      (∀ i : ℕ, f.constituentMod i ≠ 0 ↔ snfIndex snf b ∣ i) ∧
      f.index = snfIndex snf b := by
  set j := snfIndex snf b
  have hj_pos : 0 < j := snfIndex_pos snf b
  obtain ⟨K₀, hK₀⟩ := exists_pos_ehrCount_of_dvd hPne hPconv hPbdd haff snf
  have hconst_ne_of_dvd : ∀ i : ℕ, j ∣ i → f.constituentMod i ≠ 0 := by
    intro i ⟨q, hq⟩ h0
    have hall := (f.constituentMod_eq_zero_iff_forall_eval_eq_zero i).1 h0
    set t := (K₀ + 1) * j
    have hev0 : f.eval (i + t * f.period) = 0 := hall t
    have hmul : i + t * f.period = (q + (K₀ + 1) * f.period) * j := by
      rw [hq]; simp only [t]; ring
    have hge : K₀ ≤ q + (K₀ + 1) * f.period := by
      have : 1 ≤ f.period := f.period_pos
      nlinarith
    have hpos : 0 < ehrCount P ((q + (K₀ + 1) * f.period) * j) := hK₀ _ hge
    rw [hf, hmul] at hev0
    have : (0 : ℚ) < (ehrCount P ((q + (K₀ + 1) * f.period) * j) : ℚ) := by exact_mod_cast hpos
    linarith
  have hdvd_period : j ∣ f.period := by
    by_contra hndvd
    have hconst0 : f.constituentMod 0 = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine Set.Infinite.mono
        (s := Set.range fun k : ℕ ↦ ((f.period + k * (j * f.period) : ℕ) : ℚ)) ?_ ?_
      · rintro _ ⟨k, rfl⟩
        change (f.constituentMod 0).eval ((f.period + k * (j * f.period) : ℕ) : ℚ) =
          (0 : ℚ[X]).eval ((f.period + k * (j * f.period) : ℕ) : ℚ)
        rw [Polynomial.eval_zero]
        have hmod : (f.period + k * (j * f.period)) % f.period = 0 % f.period := by
          have : f.period + k * (j * f.period) = (1 + k * j) * f.period := by ring
          rw [this, Nat.mul_mod_left, Nat.zero_mod]
        have hev : (f.constituentMod 0).eval ((f.period + k * (j * f.period) : ℕ) : ℚ) =
            f.eval (f.period + k * (j * f.period)) := by
          rw [Quasipolynomial.eval_eq_constituentMod_eval,
            f.constituentMod_eq_of_mod_eq hmod.symm]
        rw [hev, hf]
        have hndvd_k : ¬ j ∣ (f.period + k * (j * f.period)) := by
          intro hdiv
          have hd2 : j ∣ k * (j * f.period) := by
            refine ⟨k * f.period, by ring⟩
          exact hndvd ((Nat.dvd_add_left hd2).1 hdiv)
        rw [ehrCount_eq_zero_of_not_dvd hPne haff snf hndvd_k, Nat.cast_zero]
      · refine Set.infinite_range_of_injective fun k₁ k₂ hk ↦ ?_
        have hnat : f.period + k₁ * (j * f.period) = f.period + k₂ * (j * f.period) :=
          Nat.cast_injective hk
        have hpos : 0 < j * f.period := Nat.mul_pos hj_pos f.period_pos
        exact Nat.eq_of_mul_eq_mul_right hpos (Nat.add_left_cancel hnat)
    exact hconst_ne_of_dvd 0 (dvd_zero j) hconst0
  have hconst_iff : ∀ i : ℕ, f.constituentMod i ≠ 0 ↔ j ∣ i := by
    intro i
    constructor
    · intro hne
      by_contra hndvd
      apply hne
      rw [f.constituentMod_eq_zero_iff_forall_eval_eq_zero]
      intro k
      have hndvd_k : ¬ j ∣ (i + k * f.period) := by
        intro hdiv
        exact hndvd ((Nat.dvd_add_left (dvd_mul_of_dvd_right hdvd_period k)).1 hdiv)
      rw [hf, ehrCount_eq_zero_of_not_dvd hPne haff snf hndvd_k, Nat.cast_zero]
    · exact hconst_ne_of_dvd i
  have hindex_eq : f.index = j := by
    have hle : f.index ≤ j :=
      f.index_le_of_constituentMod_ne_zero hj_pos (hconst_ne_of_dvd j (dvd_refl j))
    have hpos : 0 < f.index := by
      refine f.index_pos_of_exists_eval_ne_zero ⟨K₀ * j, ?_⟩
      rw [hf]
      exact_mod_cast Nat.ne_of_gt (hK₀ K₀ (le_refl K₀))
    have hdvd_idx : j ∣ f.index := (hconst_iff f.index).1 (f.index_spec hpos)
    exact le_antisymm hle (Nat.le_of_dvd hpos hdvd_idx)
  exact ⟨hdvd_period, hconst_iff, hindex_eq⟩

/-- Exact feasibility criterion for saturated dilations: for any dilation `c > s` above a
saturation threshold `s` of the Ehrhart quasipolynomial `f`, `c • P` contains an integer lattice
point if and only if `f.index ∣ c`. -/
theorem ehrCount_pos_iff_index_dvd_of_saturated {m d : ℕ} {P : Set (Fin d → ℝ)}
    {C : Matrix (Fin m) (Fin d) ℤ} {b : Fin m → ℤ}
    (hPne : P.Nonempty) (hPconv : Convex ℝ P) (hPbdd : Bornology.IsBounded P)
    (haff : IsRationalAffineSpan P C b) (snf : UnimodularSNF C)
    {f : Quasipolynomial} (hf : ∀ n : ℕ, f.eval n = (ehrCount P n : ℚ))
    {s : ℕ} (hs : (f.shift s).IsStrictlySaturated) {c : ℕ} (hc : s < c) :
    0 < ehrCount P c ↔ f.index ∣ c := by
  obtain ⟨_, hconst_iff, hindex_eq⟩ :=
    ehrQuasipolynomial_index_eq_snfIndex hPne hPconv hPbdd haff snf hf
  constructor
  · intro hpos
    by_contra hndvd
    rw [hindex_eq] at hndvd
    have h0 := ehrCount_eq_zero_of_not_dvd hPne haff snf hndvd
    omega
  · intro hdvd
    rw [hindex_eq] at hdvd
    have hne : f.constituentMod c ≠ 0 := (hconst_iff c).2 hdvd
    have hqpos : 0 < f.eval c := Quasipolynomial.eval_pos_of_gt_saturationIndex hs hc hne
    rw [hf] at hqpos
    exact_mod_cast hqpos

/-- Testing feasibility of `P ∩ ℤ^d` via `f.index = 1` has zero false negatives, is exact whenever
`f` is strictly saturated, and can err only on non-strictly-saturated instances. -/
theorem ehrCount_one_index_test {d : ℕ} {P : Set (Fin d → ℝ)}
    {f : Quasipolynomial} (hf : ∀ n : ℕ, f.eval n = (ehrCount P n : ℚ)) :
    (0 < ehrCount P 1 → f.index = 1) ∧
      (f.IsStrictlySaturated → (0 < ehrCount P 1 ↔ f.index = 1)) ∧
      (f.index = 1 ∧ ehrCount P 1 = 0 →
        ¬ f.IsStrictlySaturated ∧ (f.HasSaturationIndex → 1 ≤ f.saturationIndex)) := by
  have hnofn : 0 < ehrCount P 1 → f.index = 1 := by
    intro hpos
    apply Quasipolynomial.index_eq_one_of_eval_one_ne_zero
    rw [hf]
    exact_mod_cast Nat.ne_of_gt hpos
  have hsat_iff : f.IsStrictlySaturated → (0 < ehrCount P 1 ↔ f.index = 1) := by
    intro hsat
    refine ⟨hnofn, fun hind ↦ ?_⟩
    have hpos_idx : 0 < f.index := by omega
    have hne1 : f.constituentMod 1 ≠ 0 := by
      rw [← hind]
      exact f.index_spec hpos_idx
    have hq : 0 < f.eval 1 := (f.isStrictlySaturated_iff.1 hsat) 1 (le_refl 1) hne1
    rw [hf] at hq
    exact_mod_cast hq
  refine ⟨hnofn, hsat_iff, ?_⟩
  rintro ⟨hind, h0⟩
  have hnot : ¬ f.IsStrictlySaturated := by
    intro hsat
    have hpos := (hsat_iff hsat).2 hind
    omega
  refine ⟨hnot, fun hhas ↦ ?_⟩
  refine Nat.pos_of_ne_zero fun hs0 ↦ hnot ((f.saturationIndex_eq_zero_iff hhas).1 hs0)

/-- Any family of bounded sets `P a ⊆ ℝ^{dim a}` whose integer lattice points possess an
injective
polynomial-length bitstring encoding with a poly-time membership verifier has its lattice-point
counting function `a ↦ ehrCount (P a) 1` in `Cslib.Complexity.SharpP`. -/
theorem ehrCount_mem_sharpP {α : Type} (enc : α ↪ List Bool)
    (dim : α → ℕ) (P : ∀ a : α, Set (Fin (dim a) → ℝ))
    (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (hVpoly : Turing.MultiTapeTM.ComputableInPolyTime V
      (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBool)
    (decode : ∀ a : α, (Fin (p.eval (enc a).length) → Bool) → Option (Fin (dim a) → ℤ))
    (hdecode_inj : ∀ a w₁ w₂ z,
      decode a w₁ = some z → decode a w₂ = some z → w₁ = w₂)
    (hdecode_surj : ∀ a (z : Fin (dim a) → ℤ),
      intPoint z ∈ P a → ∃ w, decode a w = some z)
    (hV_iff : ∀ a w,
      V (a, List.ofFn w) = true ↔ ∃ z, decode a w = some z ∧ intPoint z ∈ P a) :
    (fun a ↦ ehrCount (P a) 1) ∈ Cslib.Complexity.SharpP enc := by
  rw [Cslib.Complexity.mem_SharpP]
  refine ⟨p, V, hVpoly, fun a ↦ ?_⟩
  set n := p.eval (enc a).length
  have h1P : (1 : ℝ) • P a = P a := one_smul ℝ (P a)
  rw [ehrCount, Nat.cast_one, h1P, Cslib.Complexity.acceptCount]
  let S : Finset (Fin n → Bool) := Finset.univ.filter fun w ↦ V (a, List.ofFn w) = true
  have hbij : Nonempty ({z : Fin (dim a) → ℤ // intPoint z ∈ P a} ≃ {w // w ∈ S}) := by
    classical
    refine ⟨{
      toFun := fun ⟨z, hz⟩ ↦
        ⟨Classical.choose (hdecode_surj a z hz), by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _,
            (hV_iff a _).2 ⟨z, Classical.choose_spec (hdecode_surj a z hz), hz⟩⟩⟩
      invFun := fun ⟨w, hw⟩ ↦
        let h := (hV_iff a w).1 (Finset.mem_filter.1 hw).2
        ⟨Classical.choose h, (Classical.choose_spec h).2⟩
      left_inv := fun ⟨z, hz⟩ ↦ by
        ext
        set w := Classical.choose (hdecode_surj a z hz)
        have hw_dec : decode a w = some z := Classical.choose_spec (hdecode_surj a z hz)
        have hw_mem : w ∈ S := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (hV_iff a w).2 ⟨z, hw_dec, hz⟩⟩
        have hch := (Classical.choose_spec ((hV_iff a w).1 (Finset.mem_filter.1 hw_mem).2)).1
        have hopt : some (Classical.choose ((hV_iff a w).1 (Finset.mem_filter.1 hw_mem).2)) =
            some z := hch.symm.trans hw_dec
        exact congrFun (Option.some.inj hopt) _
      right_inv := fun ⟨w, hw⟩ ↦ by
        ext
        have h := (hV_iff a w).1 (Finset.mem_filter.1 hw).2
        set z := Classical.choose h
        have hz_dec : decode a w = some z := (Classical.choose_spec h).1
        have hz_P : intPoint z ∈ P a := (Classical.choose_spec h).2
        have hw'_dec : decode a (Classical.choose (hdecode_surj a z hz_P)) = some z :=
          Classical.choose_spec (hdecode_surj a z hz_P)
        exact congrFun (hdecode_inj a _ w z hw'_dec hz_dec) _ }⟩
  rcases hbij with ⟨e⟩
  have hcard : Nat.card {z : Fin (dim a) → ℤ // intPoint z ∈ P a} = Nat.card {w // w ∈ S} :=
    Nat.card_congr e
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe]

end CslibFrontier.Polyhedra
