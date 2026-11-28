module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Finite-Dimensional C⋆-Subalgebra Structure and Commutant Decomposition

This module develops the structure theory of finite-dimensional unital `C⋆`-subalgebras
`𝒜 ⊆ 𝔹(H)` on finite-dimensional complex Hilbert spaces `H`, culminating in the simultaneous
block-diagonal tensor-product decomposition of `𝒜` and its commutant.

## Main definitions

* `CslibFrontier.Foundations.Quantum.Algebra.IsOrthProj`: orthogonal projections (`star p = p` and
  `p * p = p`) in `H →L[ℂ] H`.

## Main results

* `CslibFrontier.Foundations.Quantum.Algebra.schur_center_matrix` and
  `CslibFrontier.Foundations.Quantum.Algebra.schur_center_clm`: Schur lemma for the center of
  complex matrix algebras and `𝔹(H)` on finite-dimensional complex Hilbert spaces.
* `CslibFrontier.Foundations.Quantum.Algebra.commutant_one_kronecker_matrix`: any matrix on
  `ι × κ` commuting with all `1_ι ⊗ B` has the form `A ⊗ 1_κ`.
* `CslibFrontier.Foundations.Quantum.Algebra.isSimpleRing_iff_trivial_center`: a
  finite-dimensional unital `C⋆`-subalgebra `𝒜 ⊆ 𝔹(H)` on a nontrivial finite-dimensional Hilbert
  space is simple if and only if its center consists of scalar multiples of the identity.
* `CslibFrontier.Foundations.Quantum.Algebra.exists_central_orthProj_decomp`: every
  finite-dimensional unital `C⋆`-subalgebra `𝒜 ⊆ 𝔹(H)` decomposes orthogonally into simple
  unital `C⋆`-subalgebras via minimal central orthogonal projections.
* `CslibFrontier.Foundations.Quantum.Algebra.exists_tensorFactor_of_isSimpleRing`: every simple
  unital `C⋆`-subalgebra `𝒜 ⊆ 𝔹(H)` on a nontrivial finite-dimensional Hilbert space induces a
  unitary isomorphism `ℂ^{d₁} ⊗ ℂ^{d₂} ≃ₗᵢ[ℂ] H` identifying `𝒜` with `M_{d₁}(ℂ) ⊗ 1_{d₂}`.
* `CslibFrontier.Foundations.Quantum.Algebra.exists_commutant_tensor_decomp`: simultaneous
  block-diagonal tensor-product decomposition of a finite-dimensional unital `C⋆`-subalgebra `𝒜`
  and its commutant on `H ≃ₗᵢ[ℂ] ⊕_j (ℂ^{d₁ j} ⊗ ℂ^{d₂ j})`.
-/

public section

noncomputable section

namespace CslibFrontier.Foundations.Quantum.Algebra

open scoped ComplexOrder InnerProductSpace Kronecker Matrix

/-! ### Center of Matrix Algebras and Commutant of `1 ⊗ M_κ(ℂ)` -/

/-- Schur lemma for complex matrices: any matrix commuting with all matrices is a scalar
multiple of the identity matrix `1`. -/
theorem schur_center_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (hC : ∀ M : Matrix ι ι ℂ, Commute C M) :
    ∃ c : ℂ, C = c • (1 : Matrix ι ι ℂ) := by
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    refine ⟨C i₀ i₀, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hij : i = j
    · subst hij
      have hentry := congrFun (congrFun (hC (Matrix.single i i₀ 1)).eq i) i₀
      simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_mul,
        one_mul, zero_mul, and_true, true_and] at hentry
      simpa using hentry
    · simp only [hij, ↓reduceIte]
      have hentry := congrFun (congrFun (hC (Matrix.single j j 1)).eq i) j
      simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero,
        zero_mul, and_true, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
        Ne.symm hij, false_and, Finset.sum_const_zero] at hentry
      exact hentry
  · have : IsEmpty ι := not_nonempty_iff.mp hne
    exact ⟨0, by ext i; exact IsEmpty.elim this i⟩

/-- Schur lemma for bounded linear operators: the center of `𝔹(H)` on a finite-dimensional
complex Hilbert space `H` consists of scalar multiples of the identity. -/
theorem schur_center_clm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (C : H →L[ℂ] H) (hC : ∀ M : H →L[ℂ] H, Commute C M) :
    ∃ c : ℂ, C = c • (1 : H →L[ℂ] H) := by
  let b := stdOrthonormalBasis ℂ H
  let e : (H →L[ℂ] H) ≃ₐ[ℂ] Matrix (Fin (Module.finrank ℂ H)) (Fin (Module.finrank ℂ H)) ℂ :=
    { toFun T := LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap
      invFun M := (Matrix.toLin b.toBasis b.toBasis M).toContinuousLinearMap
      left_inv T := by ext x; simp
      right_inv M := by ext i j; simp
      map_mul' T₁ T₂ := LinearMap.toMatrix_mul b.toBasis T₁.toLinearMap T₂.toLinearMap
      map_add' T₁ T₂ := map_add (LinearMap.toMatrix b.toBasis b.toBasis) _ _
      commutes' c := by ext i j; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply] }
  have hM : ∀ M, Commute (e C) M := fun M ↦ by
    simpa [Commute, SemiconjBy, map_mul] using congrArg e (hC (e.symm M)).eq
  obtain ⟨c, hc⟩ := schur_center_matrix (e C) hM
  exact ⟨c, e.injective (by rw [hc, map_smul, map_one])⟩

/-- Commutant of `1_ι ⊗ M_κ(ℂ)`: if `C ∈ M_{ι × κ}(ℂ)` commutes with `1_ι ⊗ B` for every
`B ∈ M_κ(ℂ)`, then `C = A ⊗ 1_κ` for some `A ∈ M_ι(ℂ)`. -/
theorem commutant_one_kronecker_matrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (C : Matrix (ι × κ) (ι × κ) ℂ)
    (hC : ∀ B : Matrix κ κ ℂ, Commute C ((1 : Matrix ι ι ℂ) ⊗ₖ B)) :
    ∃ A : Matrix ι ι ℂ, C = A ⊗ₖ (1 : Matrix κ κ ℂ) := by
  have hblock : ∀ i j : ι, ∃ a : ℂ,
      Matrix.of (fun k l : κ ↦ C (i, k) (j, l)) = a • (1 : Matrix κ κ ℂ) := by
    intro i j
    refine schur_center_matrix (Matrix.of fun k l ↦ C (i, k) (j, l)) fun B ↦ ?_
    ext k l
    have hcomm := congrFun (congrFun (hC B).eq (i, k)) (j, l)
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero] at hcomm ⊢
    rw [Finset.sum_eq_single j (fun x _ hx ↦ by simp [hx]) (fun h ↦ absurd (Finset.mem_univ j) h),
      Finset.sum_eq_single i (fun x _ hx ↦ by simp [Ne.symm hx])
        (fun h ↦ absurd (Finset.mem_univ i) h)] at hcomm
    simpa [Matrix.of_apply] using hcomm
  choose a ha using hblock
  refine ⟨Matrix.of a, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  have hij := congrFun (congrFun (ha i j) k) l
  simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using hij

/-! ### Spectral Projections and Finite-Dimensional C⋆-Subalgebra Structure -/

section FinDimCStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An element `p : H →L[ℂ] H` is an orthogonal projection if it is self-adjoint and idempotent. -/
def IsOrthProj (p : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint p ∧ p * p = p

private theorem isOrthProj_zero : IsOrthProj (0 : H →L[ℂ] H) :=
  ⟨IsSelfAdjoint.zero _, mul_zero _⟩

private theorem isOrthProj_one : IsOrthProj (1 : H →L[ℂ] H) :=
  ⟨IsSelfAdjoint.one _, mul_one _⟩

private theorem IsOrthProj.one_sub {p : H →L[ℂ] H} (hp : IsOrthProj p) : IsOrthProj (1 - p) :=
  ⟨(IsSelfAdjoint.one _).sub hp.1,
    by rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hp.2]; abel⟩

private theorem IsOrthProj.add_of_mul_zero {p q : H →L[ℂ] H} (hp : IsOrthProj p)
    (hq : IsOrthProj q) (hpq : p * q = 0) : IsOrthProj (p + q) := by
  have hqp : q * p = 0 := by
    have h := congrArg star hpq
    rwa [star_mul, hp.1.star_eq, hq.1.star_eq, star_zero] at h
  exact ⟨hp.1.add hq.1, by rw [add_mul, mul_add, mul_add, hp.2, hq.2, hpq, hqp, add_zero, zero_add]⟩

private theorem IsOrthProj.nonneg {p : H →L[ℂ] H} (hp : IsOrthProj p) : 0 ≤ p := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint hp.2).mpr hp.1

variable [FiniteDimensional ℂ H]

/-- Spectral projection onto the `μ`-eigenspace of a self-adjoint operator `T` via Lagrange
interpolation, proving that every spectral projection of `T ∈ 𝒜` lies in `𝒜`. -/
private theorem exists_spectral_proj_of_selfAdjoint (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT_mem : T ∈ 𝒜) (hT_sa : IsSelfAdjoint T) (hT_ne : T ≠ 0) :
    ∃ (μ : ℝ) (q : H →L[ℂ] H), μ ≠ 0 ∧ q ∈ 𝒜 ∧ IsOrthProj q ∧ q ≠ 0 ∧
      T * q = (μ : ℂ) • q ∧
      (∀ B : H →L[ℂ] H, Commute T B → Commute q B) ∧
      ∃ r : H →L[ℂ] H, r ∈ 𝒜 ∧ q = T * r := by
  classical
  have hsym : (T : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT_sa
  let n := Module.finrank ℂ H
  let ev : Fin n → ℝ := hsym.eigenvalues rfl
  let eb : OrthonormalBasis (Fin n) ℂ H := hsym.eigenvectorBasis rfl
  have heig : ∀ k : Fin n, T (eb k) = (ev k : ℂ) • eb k := fun k ↦
    hsym.apply_eigenvectorBasis rfl k
  have hex_nz : ∃ k₀ : Fin n, ev k₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hT_ne
    ext x
    rw [← eb.sum_repr' x, map_sum, zero_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [map_smul, heig k, hall k, Complex.ofReal_zero, zero_smul, smul_zero]
  obtain ⟨k₀, hk₀⟩ := hex_nz
  let μ : ℝ := ev k₀
  let S : Finset ℝ := (Finset.univ.image ev).erase μ
  -- Lagrange polynomial L(X) = ∏_{λ ∈ S} (μ - λ)⁻¹ • (X - λ)
  let q : H →L[ℂ] H :=
    (S.toList.map fun lam ↦ ((μ - lam : ℝ)⁻¹ : ℂ) • (T - (lam : ℂ) • 1)).prod
  have hq_mem : q ∈ 𝒜 := by
    refine list_prod_mem fun x hx ↦ ?_
    rcases List.mem_map.mp hx with ⟨lam, _, rfl⟩
    exact Subalgebra.smul_mem 𝒜.toSubalgebra
      (sub_mem hT_mem (Subalgebra.smul_mem 𝒜.toSubalgebra (one_mem 𝒜) _)) _
  have hq_comm : ∀ B : H →L[ℂ] H, Commute T B → Commute q B := fun B hB ↦ by
    refine Commute.list_prod_left _ B fun x hx ↦ ?_
    rcases List.mem_map.mp hx with ⟨lam, _, rfl⟩
    exact (hB.sub_left ((Commute.one_left B).smul_left _)).smul_left _
  have hq_eig : ∀ k : Fin n, q (eb k) = if ev k = μ then eb k else 0 := by
    intro k
    have hact : ∀ (l : List ℝ),
        (l.map fun lam ↦ ((μ - lam : ℝ)⁻¹ : ℂ) • (T - (lam : ℂ) • 1)).prod (eb k) =
        (l.map fun lam ↦ (((μ - lam : ℝ)⁻¹ : ℂ) * ((ev k : ℂ) - (lam : ℂ)))).prod • eb k := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [mul_apply_eq_comp, ih, map_smul, smul_apply, sub_apply,
          heig k, smul_apply, one_apply_eq_self, ← sub_smul, smul_smul, smul_smul]
        congr 1
        ring
    rw [hact S.toList]
    by_cases hk : ev k = μ
    · simp only [hk, ↓reduceIte]
      have hprod1 : (S.toList.map fun lam ↦
          (((μ - lam : ℝ)⁻¹ : ℂ) * ((μ : ℂ) - (lam : ℂ)))).prod = 1 := by
        refine List.prod_eq_one fun x hx ↦ ?_
        rcases List.mem_map.mp hx with ⟨lam, hlam, rfl⟩
        have hlam' : lam ∈ S := Finset.mem_toList.mp hlam
        have hne : μ - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hlam').1)
        rw [← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
          inv_mul_cancel₀ hne, Complex.ofReal_one]
      rw [hprod1, one_smul]
    · simp only [hk, ↓reduceIte]
      have hmemS : ev k ∈ S.toList := Finset.mem_toList.mpr
        (Finset.mem_erase.mpr ⟨hk, Finset.mem_image_of_mem ev (Finset.mem_univ k)⟩)
      have h0mem : (0 : ℂ) ∈ S.toList.map fun lam ↦
          (((μ - lam : ℝ)⁻¹ : ℂ) * ((ev k : ℂ) - (lam : ℂ))) :=
        List.mem_map.mpr ⟨ev k, hmemS, by simp⟩
      rw [List.prod_eq_zero h0mem, zero_smul]
  have hq_proj : q * q = q := by
    ext x
    rw [← eb.sum_repr' x]
    simp only [mul_apply_eq_comp, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, map_smul, hq_eig k]
    split_ifs with h
    · rw [hq_eig k]
      simp [h]
    · simp
  have hq_sa : IsSelfAdjoint q := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    rw [← eb.sum_repr' x, ← eb.sum_repr' y]
    simp only [ContinuousLinearMap.coe_coe, map_sum, map_smul, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hq_eig]
    refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    split_ifs with hi hj hj'
    · rfl
    · simp [eb.orthonormal.inner_eq_zero (fun (h : j = i) ↦ hj (h ▸ hi))]
    · simp [eb.orthonormal.inner_eq_zero (fun (h : j = i) ↦ hi (h.symm ▸ hj'))]
    · simp
  have hq_ne : q ≠ 0 := by
    intro h0
    have h1 := congrFun (congrArg DFunLike.coe h0) (eb k₀)
    simp only [hq_eig k₀, μ, ↓reduceIte, zero_apply] at h1
    have hnorm := congrArg norm h1
    rw [eb.orthonormal.1 k₀, norm_zero] at hnorm
    norm_num at hnorm
  have hTq : T * q = (μ : ℂ) • q := by
    ext x
    rw [← eb.sum_repr' x]
    simp only [mul_apply_eq_comp, smul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, hq_eig k]
    split_ifs with h
    · rw [map_smul, heig k, h, smul_comm]
    · simp
  refine ⟨μ, q, hk₀, hq_mem, ⟨hq_sa, hq_proj⟩, hq_ne, hTq, hq_comm,
    ((μ⁻¹ : ℝ) : ℂ) • q, Subalgebra.smul_mem 𝒜.toSubalgebra hq_mem _, ?_⟩
  rw [mul_smul_comm, hTq, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hk₀,
    Complex.ofReal_one, one_smul]

/-- Rank of an orthogonal projection (the dimension of its range). -/
private def projRank (p : H →L[ℂ] H) : ℕ :=
  Module.finrank ℂ (LinearMap.range p.toLinearMap)

omit [CompleteSpace H] in
private theorem projRank_pos_of_ne_zero {p : H →L[ℂ] H} (hp : p ≠ 0) : 0 < projRank p := by
  by_contra h0
  have hr : Module.finrank ℂ (LinearMap.range p.toLinearMap) = 0 := Nat.eq_zero_of_not_pos h0
  have hbot : LinearMap.range p.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hr
  apply hp
  ext x
  have hx : p x ∈ (⊥ : Submodule ℂ H) := hbot ▸ ⟨x, rfl⟩
  simpa using hx

private theorem projRank_add_of_mul_zero {p q : H →L[ℂ] H} (hp : IsOrthProj p) (hq : IsOrthProj q)
    (hpq : p * q = 0) : projRank (p + q) = projRank p + projRank q := by
  have hqp : q * p = 0 := by
    have h := congrArg star hpq
    rwa [star_mul, hp.1.star_eq, hq.1.star_eq, star_zero] at h
  have hsup : LinearMap.range (p + q).toLinearMap =
      LinearMap.range p.toLinearMap ⊔ LinearMap.range q.toLinearMap := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, rfl⟩
        refine ⟨p x, ?_⟩
        change p (p x) + q (p x) = p x
        have h1 : p (p x) = p x := congrFun (congrArg DFunLike.coe hp.2) x
        have h2 : q (p x) = 0 := congrFun (congrArg DFunLike.coe hqp) x
        rw [h1, h2, add_zero]
      · rintro _ ⟨x, rfl⟩
        refine ⟨q x, ?_⟩
        change p (q x) + q (q x) = q x
        have h1 : p (q x) = 0 := congrFun (congrArg DFunLike.coe hpq) x
        have h2 : q (q x) = q x := congrFun (congrArg DFunLike.coe hq.2) x
        rw [h1, h2, zero_add]
  have hinf : LinearMap.range p.toLinearMap ⊓ LinearMap.range q.toLinearMap = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    have h1 : p (q z) = 0 := congrFun (congrArg DFunLike.coe hpq) z
    have h2 : p (p y) = p y := congrFun (congrArg DFunLike.coe hp.2) y
    change q z = p y at hz
    rw [hz] at h1
    rw [h1] at h2
    simpa using h2.symm
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range p.toLinearMap) (LinearMap.range q.toLinearMap)
  rw [hinf, finrank_bot, add_zero] at hdim
  rw [projRank, projRank, projRank, hsup]
  exact hdim

/-- If `p` is an orthogonal projection in `𝒜`, `T ∈ 𝒜` is self-adjoint with `p * T * p = T` and
`T ≠ 0`, then there exist a nonzero real eigenvalue `μ` and a nonzero orthogonal projection `q ∈ 𝒜`
with `p * q = q`, `q * p = q`, `T * q = μ • q`, and `q = T * r` for some `r ∈ 𝒜`. -/
private theorem exists_proj_in_corner (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H))
    {p T : H →L[ℂ] H} (hp : IsOrthProj p) (hT_mem : T ∈ 𝒜) (hT_sa : IsSelfAdjoint T)
    (hcorner : p * T * p = T) (hT_ne : T ≠ 0) :
    ∃ (μ : ℝ) (q : H →L[ℂ] H), μ ≠ 0 ∧ q ∈ 𝒜 ∧ IsOrthProj q ∧ q ≠ 0 ∧
      p * q = q ∧ q * p = q ∧ T * q = (μ : ℂ) • q ∧
      (∀ B : H →L[ℂ] H, Commute T B → Commute q B) ∧
      ∃ r : H →L[ℂ] H, r ∈ 𝒜 ∧ q = T * r := by
  obtain ⟨μ, q, hμ, hq_mem, hq_proj, hq_ne, hTq, hq_comm, r, hr_mem, hq_eq⟩ :=
    exists_spectral_proj_of_selfAdjoint 𝒜 hT_mem hT_sa hT_ne
  have hpq : p * q = q := by
    have h1 : p * (T * q) = T * q := by
      calc p * (T * q) = p * ((p * T * p) * q) := by rw [hcorner]
        _ = ((p * p) * T * p) * q := by simp only [mul_assoc]
        _ = (p * T * p) * q := by rw [hp.2]
        _ = T * q := by rw [hcorner]
    rw [hTq, mul_smul_comm] at h1
    have h2 := congrArg (((μ⁻¹ : ℝ) : ℂ) • ·) h1
    simp only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hμ, Complex.ofReal_one,
      one_smul] at h2
    exact h2
  have hqp : q * p = q := by
    have h := congrArg star hpq
    rwa [star_mul, hp.1.star_eq, hq_proj.1.star_eq] at h
  exact ⟨μ, q, hμ, hq_mem, hq_proj, hq_ne, hpq, hqp, hTq, hq_comm, r, hr_mem, hq_eq⟩

/-- Corner algebra of a minimal nonzero orthogonal projection in `𝒜` is scalar (`p 𝒜 p = ℂ p`). -/
private theorem corner_eq_scalars_of_minimal_proj (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H))
    {p : H →L[ℂ] H} (hp_mem : p ∈ 𝒜) (hp : IsOrthProj p)
    (hmin : ∀ q, q ∈ 𝒜 → IsOrthProj q → q ≠ 0 → q * p = q → q = p)
    {a : H →L[ℂ] H} (ha : a ∈ 𝒜) : ∃ α : ℂ, p * a * p = α • p := by
  have hsa_case : ∀ T : H →L[ℂ] H, T ∈ 𝒜 → IsSelfAdjoint T → p * T * p = T →
      ∃ r : ℝ, T = (r : ℂ) • p := by
    intro T hT_mem hT_sa hcorner
    by_cases hT0 : T = 0
    · exact ⟨0, by simp [hT0]⟩
    · obtain ⟨μ, q, _, hq_mem, hq_proj, hq_ne, _, hqp, hTq, _, _, _, _⟩ :=
        exists_proj_in_corner 𝒜 hp hT_mem hT_sa hcorner hT0
      have hq_eq : q = p := hmin q hq_mem hq_proj hq_ne hqp
      rw [hq_eq] at hTq
      have hTp : T * p = T := by rw [← hcorner, mul_assoc, hp.2]
      rw [hTp] at hTq
      exact ⟨μ, hTq⟩
  let x := p * a * p
  have hx_mem : x ∈ 𝒜 := mul_mem (mul_mem hp_mem ha) hp_mem
  have hx_corner : p * x * p = x := by
    simp only [x, mul_assoc, hp.2]
    rw [← mul_assoc p p, hp.2]
  let T₁ := (2 : ℂ)⁻¹ • (x + star x)
  let T₂ := (2 * Complex.I)⁻¹ • (x - star x)
  have hsx_mem : star x ∈ 𝒜 := star_mem hx_mem
  have hT₁_mem : T₁ ∈ 𝒜 := Subalgebra.smul_mem 𝒜.toSubalgebra (add_mem hx_mem hsx_mem) _
  have hT₂_mem : T₂ ∈ 𝒜 := Subalgebra.smul_mem 𝒜.toSubalgebra (sub_mem hx_mem hsx_mem) _
  have hT₁_sa : IsSelfAdjoint T₁ := by
    change star ((2 : ℂ)⁻¹ • (x + star x)) = (2 : ℂ)⁻¹ • (x + star x)
    simp [star_smul, star_add, add_comm]
  have hT₂_sa : IsSelfAdjoint T₂ := by
    change star ((2 * Complex.I)⁻¹ • (x - star x)) = (2 * Complex.I)⁻¹ • (x - star x)
    have hstar : star ((2 * Complex.I)⁻¹ : ℂ) = -((2 * Complex.I)⁻¹) := by simp
    rw [star_smul, star_sub, star_star, hstar, neg_smul, ← smul_neg, neg_sub]
  have hsx_corner : p * star x * p = star x := by
    have h := congrArg star hx_corner
    simpa [star_mul, hp.1.star_eq, mul_assoc] using h
  have hT₁_corner : p * T₁ * p = T₁ := by
    simp only [T₁, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hx_corner, hsx_corner]
  have hT₂_corner : p * T₂ * p = T₂ := by
    simp only [T₂, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hx_corner, hsx_corner]
  obtain ⟨r₁, hr₁⟩ := hsa_case T₁ hT₁_mem hT₁_sa hT₁_corner
  obtain ⟨r₂, hr₂⟩ := hsa_case T₂ hT₂_mem hT₂_sa hT₂_corner
  refine ⟨(r₁ : ℂ) + Complex.I * (r₂ : ℂ), ?_⟩
  have hx_eq : x = T₁ + Complex.I • T₂ := by
    have h1 : Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by field_simp [Complex.I_ne_zero]
    simp only [T₁, T₂, smul_smul, h1, ← smul_add]
    have h2 : x + star x + (x - star x) = (2 : ℂ) • x := by rw [two_smul]; abel
    rw [h2, smul_smul]
    simp
  change x = _
  rw [hx_eq, hr₁, hr₂, smul_smul, add_smul]

/-- Every two-sided ideal of a finite-dimensional unital `C⋆`-subalgebra `𝒜 ⊆ 𝔹(H)` is generated
by a central orthogonal projection `e ∈ 𝒜`. -/
private theorem twoSidedIdeal_exists_central_proj (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H))
    (I : Ideal 𝒜) (hI : I.IsTwoSided) :
    ∃ e : 𝒜, IsOrthProj (e : H →L[ℂ] H) ∧ (∀ a : 𝒜, Commute e a) ∧ e ∈ I ∧
      ∀ x ∈ I, e * x = x := by
  classical
  let Pset : Set ℕ :=
    { k | ∃ e : 𝒜, e ∈ I ∧ IsOrthProj (e : H →L[ℂ] H) ∧ projRank (e : H →L[ℂ] H) = k }
  have hPne : Pset.Nonempty := ⟨0, ⟨0, I.zero_mem, isOrthProj_zero, by simp [projRank]⟩⟩
  have hPbdd : BddAbove Pset := by
    refine ⟨Module.finrank ℂ H, ?_⟩
    rintro k ⟨e, _, _, rfl⟩
    exact Submodule.finrank_le _
  let kmax := sSup Pset
  have hkmax_mem : kmax ∈ Pset := Nat.sSup_mem hPne hPbdd
  obtain ⟨e, he_I, he_proj, he_rank⟩ := hkmax_mem
  have hex : ∀ x ∈ I, e * x = x := by
    intro x hx
    set y : 𝒜 := (1 - e) * x
    have hy_I : y ∈ I := I.mul_mem_left (1 - e) hx
    have hzz_I : y * star y ∈ I := hI.1 (star y) hy_I
    have hzz_sa : IsSelfAdjoint (y * star y : H →L[ℂ] H) := by
      change IsSelfAdjoint ((y : H →L[ℂ] H) * star (y : H →L[ℂ] H))
      simp [IsSelfAdjoint]
    have hcorner : ((1 - (e : H →L[ℂ] H)) * ((y : H →L[ℂ] H) * star (y : H →L[ℂ] H)) *
        (1 - (e : H →L[ℂ] H))) = (y : H →L[ℂ] H) * star (y : H →L[ℂ] H) := by
      have h1e_y : (1 - (e : H →L[ℂ] H)) * (y : H →L[ℂ] H) = (y : H →L[ℂ] H) := by
        change (1 - (e : H →L[ℂ] H)) * ((1 - (e : H →L[ℂ] H)) * (x : H →L[ℂ] H)) =
          (1 - (e : H →L[ℂ] H)) * (x : H →L[ℂ] H)
        rw [← mul_assoc, he_proj.one_sub.2]
      have hy_1e : star (y : H →L[ℂ] H) * (1 - (e : H →L[ℂ] H)) = star (y : H →L[ℂ] H) := by
        have h := congrArg star h1e_y
        rwa [star_mul, he_proj.one_sub.1.star_eq] at h
      rw [← mul_assoc (1 - (e : H →L[ℂ] H)), h1e_y, mul_assoc (y : H →L[ℂ] H), hy_1e]
    by_cases hy0 : (y : H →L[ℂ] H) * star (y : H →L[ℂ] H) = 0
    · have hy_zero : (y : H →L[ℂ] H) = 0 := by
        have h := CStarRing.norm_star_mul_self (x := star (y : H →L[ℂ] H))
        rw [star_star, hy0, norm_zero] at h
        have hsy : star (y : H →L[ℂ] H) = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp h.symm)
        simpa using congrArg star hsy
      have h1 : (1 - e) * x = 0 := Subtype.ext hy_zero
      rw [sub_mul, one_mul, sub_eq_zero] at h1
      exact h1.symm
    · exfalso
      obtain ⟨_, q, _, hq_mem, hq_proj, hq_ne, h1q, _, _, _, r, hr_mem, hq_eq⟩ :=
        exists_proj_in_corner 𝒜 he_proj.one_sub (y * star y).2 hzz_sa hcorner hy0
      let qA : 𝒜 := ⟨q, hq_mem⟩
      let rA : 𝒜 := ⟨r, hr_mem⟩
      have hqA_eq : qA = (y * star y) * rA := Subtype.ext hq_eq
      have hqA_I : qA ∈ I := hqA_eq ▸ hI.1 rA hzz_I
      have heq_mul : (e : H →L[ℂ] H) * q = 0 := by
        calc (e : H →L[ℂ] H) * q = (e : H →L[ℂ] H) * ((1 - (e : H →L[ℂ] H)) * q) := by rw [h1q]
          _ = ((e : H →L[ℂ] H) * (1 - (e : H →L[ℂ] H))) * q := by rw [mul_assoc]
          _ = 0 * q := by rw [mul_sub, mul_one, he_proj.2, sub_self]
          _ = 0 := zero_mul q
      have hsum_proj : IsOrthProj ((e + qA : 𝒜) : H →L[ℂ] H) :=
        he_proj.add_of_mul_zero hq_proj heq_mul
      have hsum_I : e + qA ∈ I := I.add_mem he_I hqA_I
      have hrank : projRank ((e + qA : 𝒜) : H →L[ℂ] H) = projRank (e : H →L[ℂ] H) + projRank q :=
        projRank_add_of_mul_zero he_proj hq_proj heq_mul
      have hle_max : projRank ((e + qA : 𝒜) : H →L[ℂ] H) ≤ kmax :=
        le_csSup hPbdd ⟨e + qA, hsum_I, hsum_proj, rfl⟩
      have hq_pos : 0 < projRank q := projRank_pos_of_ne_zero hq_ne
      omega
  have hcomm : ∀ a : 𝒜, Commute e a := by
    intro a
    have h1 : e * (a * e) = a * e := hex (a * e) (I.mul_mem_left a he_I)
    have h2 : e * (star a * e) = star a * e := hex (star a * e) (I.mul_mem_left (star a) he_I)
    have h2s := congrArg star h2
    have he_star : star e = e := Subtype.ext he_proj.1.star_eq
    simp only [star_mul, he_star, star_star, mul_assoc] at h2s
    exact h2s.symm.trans h1
  exact ⟨e, he_proj, hcomm, he_I, hex⟩

/-- A finite-dimensional unital `C⋆`-subalgebra `𝒜 ⊆ 𝔹(H)` (on nontrivial `H`) is simple if and
only if its center is trivial (`{c·1 | c ∈ ℂ}`). -/
theorem isSimpleRing_iff_trivial_center [Nontrivial H] (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsSimpleRing 𝒜 ↔ ∀ z : 𝒜, (∀ a : 𝒜, Commute z a) → ∃ c : ℂ, z = c • (1 : 𝒜) := by
  have : Nontrivial 𝒜 := ⟨⟨1, 0, fun h ↦ by
    have h1 : (1 : H →L[ℂ] H) = 0 := congrArg Subtype.val h
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have := congrFun (congrArg DFunLike.coe h1) v
    exact hv (by simpa using this)⟩⟩
  rw [isSimpleRing_iff_isTwoSided_imp]
  constructor
  · rintro ⟨_, hsimp⟩ z hz
    have hsplit_sa : ∀ w : 𝒜, IsSelfAdjoint (w : H →L[ℂ] H) → (∀ a : 𝒜, Commute w a) →
        ∃ r : ℝ, w = (r : ℂ) • (1 : 𝒜) := by
      intro w hw_sa hw_comm
      by_cases hw0 : (w : H →L[ℂ] H) = 0
      · exact ⟨0, Subtype.ext (by simpa using hw0)⟩
      · obtain ⟨μ, q, _, hq_mem, hq_proj, hq_ne, hwq, hq_comm, _, _, _⟩ :=
          exists_spectral_proj_of_selfAdjoint 𝒜 w.2 hw_sa hw0
        let qA : 𝒜 := ⟨q, hq_mem⟩
        have hqA_comm : ∀ a : 𝒜, Commute qA a := fun a ↦
          Subtype.ext (hq_comm a (congrArg Subtype.val (hw_comm a)))
        let Iq : Ideal 𝒜 := Ideal.span {qA}
        have hIq_two : Iq.IsTwoSided := by
          constructor
          intro a b ha
          rcases Submodule.mem_span_singleton.mp ha with ⟨c, rfl⟩
          exact Submodule.mem_span_singleton.mpr
            ⟨c * b, by simp only [smul_eq_mul, mul_assoc, (hqA_comm b).eq]⟩
        have hIq_ne : Iq ≠ ⊥ := by
          intro hbot
          have hmem : qA ∈ (⊥ : Ideal 𝒜) := hbot ▸ Ideal.subset_span rfl
          exact hq_ne (congrArg Subtype.val (Ideal.mem_bot.mp hmem))
        have hIq_top : Iq = ⊤ := (hsimp Iq hIq_two).resolve_left hIq_ne
        have h1_mem : (1 : 𝒜) ∈ Iq := hIq_top ▸ Submodule.mem_top
        rcases Submodule.mem_span_singleton.mp h1_mem with ⟨c, hc⟩
        simp only [smul_eq_mul] at hc
        have hq1 : q = 1 := by
          have hmul : (c * qA) * qA = (1 : 𝒜) * qA := congrArg (· * qA) hc
          rw [one_mul, mul_assoc, show qA * qA = qA from Subtype.ext hq_proj.2, hc] at hmul
          exact congrArg Subtype.val hmul.symm
        rw [hq1, mul_one] at hwq
        exact ⟨μ, Subtype.ext (by simpa using hwq)⟩
    let w₁ : 𝒜 := (2 : ℂ)⁻¹ • (z + star z)
    let w₂ : 𝒜 := (2 * Complex.I)⁻¹ • (z - star z)
    have hw₁_sa : IsSelfAdjoint (w₁ : H →L[ℂ] H) := by
      change star ((2 : ℂ)⁻¹ • ((z : H →L[ℂ] H) + star (z : H →L[ℂ] H))) =
        (2 : ℂ)⁻¹ • ((z : H →L[ℂ] H) + star (z : H →L[ℂ] H))
      simp [star_smul, star_add, add_comm]
    have hw₂_sa : IsSelfAdjoint (w₂ : H →L[ℂ] H) := by
      change star ((2 * Complex.I)⁻¹ • ((z : H →L[ℂ] H) - star (z : H →L[ℂ] H))) =
        (2 * Complex.I)⁻¹ • ((z : H →L[ℂ] H) - star (z : H →L[ℂ] H))
      have hstar : star ((2 * Complex.I)⁻¹ : ℂ) = -((2 * Complex.I)⁻¹) := by simp
      rw [star_smul, star_sub, star_star, hstar, neg_smul, ← smul_neg, neg_sub]
    have hsz_comm : ∀ a : 𝒜, Commute (star z) a := fun a ↦ by
      rw [Commute, SemiconjBy]
      have h := congrArg star (hz (star a)).eq
      simpa [star_mul, star_star] using h.symm
    have hw₁_comm : ∀ a : 𝒜, Commute w₁ a := fun a ↦
      ((hz a).add_left (hsz_comm a)).smul_left _
    have hw₂_comm : ∀ a : 𝒜, Commute w₂ a := fun a ↦
      ((hz a).sub_left (hsz_comm a)).smul_left _
    obtain ⟨r₁, hr₁⟩ := hsplit_sa w₁ hw₁_sa hw₁_comm
    obtain ⟨r₂, hr₂⟩ := hsplit_sa w₂ hw₂_sa hw₂_comm
    refine ⟨(r₁ : ℂ) + Complex.I * (r₂ : ℂ), ?_⟩
    have hz_eq : z = w₁ + Complex.I • w₂ := by
      have h1 : Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
        field_simp [Complex.I_ne_zero]
      simp only [w₁, w₂, smul_smul, h1, ← smul_add]
      have h2 : z + star z + (z - star z) = (2 : ℂ) • z := by rw [two_smul]; abel
      rw [h2, smul_smul]
      simp
    rw [hz_eq, hr₁, hr₂, smul_smul, add_smul]
  · intro htriv
    refine ⟨inferInstance, fun I hI ↦ ?_⟩
    obtain ⟨e, he_proj, he_comm, he_I, hex⟩ := twoSidedIdeal_exists_central_proj 𝒜 I hI
    obtain ⟨c, hc⟩ := htriv e he_comm
    have hc_sq : c * c = c := by
      have hsq : e * e = e := Subtype.ext he_proj.2
      rw [hc, smul_mul_smul_comm, mul_one] at hsq
      have h1 : (c * c - c) • (1 : 𝒜) = 0 := by rw [sub_smul, hsq, sub_self]
      by_contra hne
      have h10 : (1 : 𝒜) = 0 := by
        have h := congrArg ((c * c - c)⁻¹ • ·) h1
        simp [smul_smul, sub_ne_zero.mpr hne] at h
      exact one_ne_zero h10
    have hc_cases : c = 0 ∨ c = 1 := by
      have : c * (c - 1) = 0 := by linear_combination hc_sq
      rcases mul_eq_zero.mp this with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    rcases hc_cases with rfl | rfl
    · left
      rw [eq_bot_iff]
      intro x hx
      have := hex x hx
      rw [hc, zero_smul, zero_mul] at this
      simpa using this.symm
    · right
      rw [eq_top_iff]
      intro x _
      rw [hc, one_smul] at he_I
      simpa using I.mul_mem_left x he_I

/-- Orthogonal decomposition of a projection `p ∈ 𝒜` into minimal nonzero projections in a
subalgebra `ℬ ⊆ 𝒜` (used both for central projections in `Z(𝒜)` and minimal projections in a
simple `𝒜`). -/
private theorem exists_minimal_proj_decomp
    (ℬ : StarSubalgebra ℂ (H →L[ℂ] H)) (p : H →L[ℂ] H) (hp_mem : p ∈ ℬ) (hp : IsOrthProj p) :
    ∃ (m : ℕ) (z : Fin m → (H →L[ℂ] H)),
      (∀ j, z j ∈ ℬ) ∧
      (∀ j, IsOrthProj (z j)) ∧
      (∀ j, z j ≠ 0) ∧
      (∀ i j, i ≠ j → z i * z j = 0) ∧
      (∑ j : Fin m, z j = p) ∧
      (∀ j q, q ∈ ℬ → IsOrthProj q → q ≠ 0 → q * z j = q → q = z j) := by
  classical
  suffices ∀ (k : ℕ) (p : H →L[ℂ] H), p ∈ ℬ → IsOrthProj p → projRank p ≤ k →
      ∃ (m : ℕ) (z : Fin m → (H →L[ℂ] H)),
        (∀ j, z j ∈ ℬ) ∧ (∀ j, IsOrthProj (z j)) ∧ (∀ j, z j ≠ 0) ∧
        (∀ i j, i ≠ j → z i * z j = 0) ∧ (∑ j : Fin m, z j = p) ∧
        (∀ j q, q ∈ ℬ → IsOrthProj q → q ≠ 0 → q * z j = q → q = z j) by
    exact this (projRank p) p hp_mem hp le_rfl
  intro k
  induction k with
  | zero =>
    intro p _ _ hrk
    have hp0 : p = 0 := by
      by_contra hne
      have := projRank_pos_of_ne_zero hne
      omega
    exact ⟨0, Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0,
      fun i ↦ i.elim0, by simp [hp0], fun j ↦ j.elim0⟩
  | succ k ih =>
    intro p hp_mem hp hrk
    by_cases hp0 : p = 0
    · exact ⟨0, Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0,
        fun i ↦ i.elim0, by simp [hp0], fun j ↦ j.elim0⟩
    · by_cases hmin : ∀ q, q ∈ ℬ → IsOrthProj q → q ≠ 0 → q * p = q → q = p
      · refine ⟨1, fun _ ↦ p, fun _ ↦ hp_mem, fun _ ↦ hp, fun _ ↦ hp0,
          fun i j hij ↦ absurd (Subsingleton.elim i j) hij, by simp, fun _ ↦ hmin⟩
      · push Not at hmin
        obtain ⟨q, hq_mem, hq_proj, hq_ne, hqp, hq_ne_p⟩ := hmin
        have hpq : p * q = q := by
          have h := congrArg star hqp
          rwa [star_mul, hp.1.star_eq, hq_proj.1.star_eq] at h
        let r : H →L[ℂ] H := p - q
        have hr_mem : r ∈ ℬ := sub_mem hp_mem hq_mem
        have hr_proj : IsOrthProj r :=
          ⟨hp.1.sub hq_proj.1, by
            change (p - q) * (p - q) = p - q
            rw [sub_mul, mul_sub, mul_sub, hp.2, hq_proj.2, hpq, hqp]; abel⟩
        have hqr : q * r = 0 := by rw [mul_sub, hq_proj.2, hqp, sub_self]
        have hr_ne : r ≠ 0 := fun h0 ↦ hq_ne_p (sub_eq_zero.mp h0).symm
        have hsum_rk : projRank p = projRank q + projRank r := by
          have heq : q + r = p := by simp [r]
          rw [← heq]
          exact projRank_add_of_mul_zero hq_proj hr_proj hqr
        have hq_pos : 0 < projRank q := projRank_pos_of_ne_zero hq_ne
        have hr_pos : 0 < projRank r := projRank_pos_of_ne_zero hr_ne
        obtain ⟨m₁, z₁, hz₁_m, hz₁_p, hz₁_ne, hz₁_o, hz₁_s, hz₁_min⟩ :=
          ih q hq_mem hq_proj (by omega)
        obtain ⟨m₂, z₂, hz₂_m, hz₂_p, hz₂_ne, hz₂_o, hz₂_s, hz₂_min⟩ :=
          ih r hr_mem hr_proj (by omega)
        let e : Fin (m₁ + m₂) ≃ Fin m₁ ⊕ Fin m₂ := finSumFinEquiv.symm
        let z : Fin (m₁ + m₂) → (H →L[ℂ] H) := fun j ↦
          match e j with
          | Sum.inl i => z₁ i
          | Sum.inr i => z₂ i
        have hz₁_q : ∀ i, z₁ i * q = z₁ i := fun i ↦ by
          rw [← hz₁_s, Finset.mul_sum, Finset.sum_eq_single i]
          · exact (hz₁_p i).2
          · intro j _ hji; exact hz₁_o i j (Ne.symm hji)
          · intro h; exact absurd (Finset.mem_univ i) h
        have hz₂_r : ∀ i, r * z₂ i = z₂ i := fun i ↦ by
          rw [← hz₂_s, Finset.sum_mul, Finset.sum_eq_single i]
          · exact (hz₂_p i).2
          · intro j _ hji; exact hz₂_o j i hji
          · intro h; exact absurd (Finset.mem_univ i) h
        refine ⟨m₁ + m₂, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j; dsimp only [z]
          cases e j with | inl i => exact hz₁_m i | inr i => exact hz₂_m i
        · intro j; dsimp only [z]
          cases e j with | inl i => exact hz₁_p i | inr i => exact hz₂_p i
        · intro j; dsimp only [z]
          cases e j with | inl i => exact hz₁_ne i | inr i => exact hz₂_ne i
        · intro i j hij
          dsimp only [z]
          have hene : e i ≠ e j := fun h ↦ hij (e.injective h)
          cases hi : e i with
          | inl a =>
            cases hj : e j with
            | inl b => exact hz₁_o a b (fun h ↦ hene (by rw [hi, hj, h]))
            | inr b =>
              change z₁ a * z₂ b = 0
              rw [← hz₁_q a, ← hz₂_r b, mul_assoc, ← mul_assoc q r, hqr, zero_mul, mul_zero]
          | inr a =>
            cases hj : e j with
            | inl b =>
              change z₂ a * z₁ b = 0
              have hrq : r * q = 0 := by
                have h := congrArg star hqr
                rwa [star_mul, hq_proj.1.star_eq, hr_proj.1.star_eq, star_zero] at h
              have hq_z₁ : q * z₁ b = z₁ b := by
                have h := congrArg star (hz₁_q b)
                rwa [star_mul, hq_proj.1.star_eq, (hz₁_p b).1.star_eq] at h
              have hz₂_r' : z₂ a * r = z₂ a := by
                have h := congrArg star (hz₂_r a)
                rwa [star_mul, hr_proj.1.star_eq, (hz₂_p a).1.star_eq] at h
              rw [← hz₂_r', ← hq_z₁, mul_assoc, ← mul_assoc r q, hrq, zero_mul, mul_zero]
            | inr b => exact hz₂_o a b (fun h ↦ hene (by rw [hi, hj, h]))
        · rw [show ∑ j : Fin (m₁ + m₂), z j =
              ∑ x : Fin m₁ ⊕ Fin m₂, (match x with | Sum.inl i => z₁ i | Sum.inr i => z₂ i) from
            e.sum_comp (fun x ↦ match x with | Sum.inl i => z₁ i | Sum.inr i => z₂ i)]
          rw [Fintype.sum_sum_type, hz₁_s, hz₂_s]
          simp [r]
        · intro j
          dsimp only [z]
          cases e j with
          | inl i => exact hz₁_min i
          | inr i => exact hz₂_min i

/-- Central projection decomposition: every finite-dimensional unital `C⋆`-subalgebra
`𝒜 ⊆ 𝔹(H)` admits a finite family of pairwise orthogonal nonzero central orthogonal projections
`z : Fin m → 𝒜` summing to `1`, such that on each block `H_j = ran (z j)`, the restricted
`C⋆`-subalgebra `𝒜_j` has trivial center (and is therefore simple). -/
theorem exists_central_orthProj_decomp (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∃ (m : ℕ) (z : Fin m → (H →L[ℂ] H)),
      (∀ j, z j ∈ 𝒜) ∧
      (∀ j, IsOrthProj (z j)) ∧
      (∀ j, z j ≠ 0) ∧
      (∀ j, ∀ a ∈ 𝒜, Commute (z j) a) ∧
      (∀ i j, i ≠ j → z i * z j = 0) ∧
      (∑ j : Fin m, z j = 1) ∧
      (∀ j c, c ∈ 𝒜 → (∀ a ∈ 𝒜, Commute c a) → ∃ α : ℂ, c * z j = α • z j) := by
  let Z : StarSubalgebra ℂ (H →L[ℂ] H) :=
    { carrier := { c | c ∈ 𝒜 ∧ ∀ a ∈ 𝒜, Commute c a }
      mul_mem' := fun ha hb ↦ ⟨mul_mem ha.1 hb.1, fun x hx ↦ (ha.2 x hx).mul_left (hb.2 x hx)⟩
      one_mem' := ⟨one_mem 𝒜, fun x _ ↦ Commute.one_left x⟩
      add_mem' := fun ha hb ↦ ⟨add_mem ha.1 hb.1, fun x hx ↦ (ha.2 x hx).add_left (hb.2 x hx)⟩
      zero_mem' := ⟨zero_mem 𝒜, fun x _ ↦ Commute.zero_left x⟩
      algebraMap_mem' := fun r ↦ ⟨algebraMap_mem 𝒜 r, fun x _ ↦ Algebra.commutes r x⟩
      star_mem' := fun {c} hc ↦ ⟨star_mem hc.1, fun x hx ↦ by
        rw [Commute, SemiconjBy]
        have h := congrArg star (hc.2 (star x) (star_mem hx)).eq
        simpa [star_mul, star_star] using h.symm⟩ }
  obtain ⟨m, z, hz_Z, hz_proj, hz_ne, hz_orth, hz_sum, hz_min⟩ :=
    exists_minimal_proj_decomp Z 1 (one_mem Z) isOrthProj_one
  refine ⟨m, z, fun j ↦ (hz_Z j).1, hz_proj, hz_ne, fun j ↦ (hz_Z j).2, hz_orth, hz_sum, ?_⟩
  intro j c hc_mem hc_comm
  have hc_Z : c ∈ Z := ⟨hc_mem, hc_comm⟩
  obtain ⟨α, hα⟩ := corner_eq_scalars_of_minimal_proj Z (hz_Z j) (hz_proj j) (hz_min j) hc_Z
  refine ⟨α, ?_⟩
  have hcomm_cz : z j * c * z j = c * z j := by
    rw [(hc_comm (z j) (hz_Z j).1).eq.symm, mul_assoc, (hz_proj j).2]
  rwa [hcomm_cz] at hα

/-- Representation of a simple finite-dimensional `C⋆`-subalgebra: if `𝒜 ⊆ 𝔹(H)` is simple on
a nontrivial finite-dimensional complex Hilbert space `H`, then there exist positive dimensions
`d₁, d₂` and a unitary isomorphism `U : EuclideanSpace ℂ (Fin d₁ × Fin d₂) ≃ₗᵢ[ℂ] H` such that
conjugation by `U` identifies `𝒜` with `{A ⊗ 1_{d₂} | A ∈ M_{d₁}(ℂ)}`. -/
theorem exists_tensorFactor_of_isSimpleRing [Nontrivial H] (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsSimpleRing 𝒜] :
    ∃ (d₁ d₂ : ℕ) (_ : 0 < d₁) (_ : 0 < d₂)
      (U : EuclideanSpace ℂ (Fin d₁ × Fin d₂) ≃ₗᵢ[ℂ] H),
      ∀ T : H →L[ℂ] H, T ∈ 𝒜 ↔
        ∃ A : Matrix (Fin d₁) (Fin d₁) ℂ,
          U.symm.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap =
            (A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)).toEuclideanLin.toContinuousLinearMap := by
  classical
  obtain ⟨d₁, p, hp_mem, hp_proj, hp_ne, hp_orth, hp_sum, hp_min⟩ :=
    exists_minimal_proj_decomp 𝒜 1 (one_mem 𝒜) isOrthProj_one
  have hd₁ : 0 < d₁ := by
    by_contra h0
    have hd0 : d₁ = 0 := Nat.eq_zero_of_not_pos h0
    subst hd0
    have h10 : (1 : H →L[ℂ] H) = 0 := by simpa using hp_sum.symm
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have := congrFun (congrArg DFunLike.coe h10) v
    exact hv (by simpa using this)
  let i₀ : Fin d₁ := ⟨0, hd₁⟩
  -- For each `i : Fin d₁`, construct partial isometry `v i ∈ p i * 𝒜 * p i₀` with `v⋆ v = p i₀`
  -- and `v v⋆ = p i`.
  have hex_v : ∀ i : Fin d₁, ∃ v : H →L[ℂ] H, v ∈ 𝒜 ∧
      p i * v = v ∧ v * p i₀ = v ∧ star v * v = p i₀ ∧ v * star v = p i := by
    intro i
    -- The two-sided ideal generated by `p i₀` in `𝒜` equals `⊤` by simplicity of `𝒜`.
    let p₀A : 𝒜 := ⟨p i₀, hp_mem i₀⟩
    let I : Ideal 𝒜 :=
      { carrier := { x | ∃ l : List (𝒜 × 𝒜), x = (l.map fun ab ↦ ab.1 * p₀A * ab.2).sum }
        add_mem' := by
          rintro x y ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
          exact ⟨l₁ ++ l₂, by simp⟩
        zero_mem' := ⟨[], by simp⟩
        smul_mem' := by
          rintro c x ⟨l, rfl⟩
          refine ⟨l.map fun ab ↦ (c * ab.1, ab.2), ?_⟩
          induction l with
          | nil => simp
          | cons ab t ih =>
            simp only [List.map_cons, List.sum_cons, smul_eq_mul, mul_add]
            rw [← ih]
            simp only [smul_eq_mul, mul_assoc] }
    have hI_two : I.IsTwoSided := by
      constructor
      rintro x b ⟨l, rfl⟩
      refine ⟨l.map fun ab ↦ (ab.1, ab.2 * b), ?_⟩
      induction l with
      | nil => simp
      | cons ab t ih =>
        simp only [List.map_cons, List.sum_cons, add_mul]
        rw [← ih]
        simp only [mul_assoc]
    have hI_ne : I ≠ ⊥ := by
      intro hbot
      have hmem : p₀A ∈ I := ⟨[(1, 1)], by simp⟩
      have h0 : p₀A = 0 := Ideal.mem_bot.mp (hbot ▸ hmem)
      exact hp_ne i₀ (congrArg Subtype.val h0)
    have hI_top : I = ⊤ :=
      ((isSimpleRing_iff_isTwoSided_imp.mp inferInstance).2 I hI_two).resolve_left hI_ne
    have h1I : (1 : 𝒜) ∈ I := hI_top ▸ Submodule.mem_top
    rcases h1I with ⟨l, hl⟩
    have hex_a : ∃ a : H →L[ℂ] H, a ∈ 𝒜 ∧ p i * a * p i₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      have hpi0 : p i = 0 := by
        have h1 : (p i : H →L[ℂ] H) = p i * (1 : 𝒜) := by simp
        rw [h1, hl]
        have hsum0 : ∀ xs : List (𝒜 × 𝒜),
            p i * ((xs.map fun ab ↦ ab.1 * p₀A * ab.2).sum : 𝒜) = 0 := by
          intro xs
          induction xs with
          | nil => simp
          | cons ab t ih =>
            simp only [List.map_cons, List.sum_cons]
            change p i * (((ab.1.1 * p i₀) * ab.2.1) +
              ((t.map fun ab ↦ ab.1 * p₀A * ab.2).sum : 𝒜)) = 0
            rw [mul_add, ih, add_zero, ← mul_assoc, ← mul_assoc, hall ab.1.1 ab.1.2, zero_mul]
        exact hsum0 l
      exact hp_ne i hpi0
    obtain ⟨a, ha_mem, hxa_ne⟩ := hex_a
    let x := p i * a * p i₀
    have hx_mem : x ∈ 𝒜 := mul_mem (mul_mem (hp_mem i) ha_mem) (hp_mem i₀)
    have hpx : p i * x = x := by simp only [x, ← mul_assoc, (hp_proj i).2]
    have hxp : x * p i₀ = x := by simp only [x, mul_assoc, (hp_proj i₀).2]
    have hxx_mem : star x * x ∈ 𝒜 := mul_mem (star_mem hx_mem) hx_mem
    have hxx_corner : p i₀ * (star x * x) * p i₀ = star x * x := by
      have hsx : p i₀ * star x = star x := by
        have h := congrArg star hxp
        rwa [star_mul, (hp_proj i₀).1.star_eq] at h
      rw [← mul_assoc, hsx, mul_assoc, hxp]
    obtain ⟨c, hc⟩ :=
      corner_eq_scalars_of_minimal_proj 𝒜 (hp_mem i₀) (hp_proj i₀) (hp_min i₀) hxx_mem
    rw [hxx_corner] at hc
    -- Show `c` is a positive real number!
    have hxx_ne : star x * x ≠ 0 := by
      intro h0
      have h := CStarRing.norm_star_mul_self (x := x)
      rw [h0, norm_zero] at h
      exact hxa_ne (norm_eq_zero.mp (mul_self_eq_zero.mp h.symm))
    have hex_w : ∃ w : H, p i₀ w ≠ 0 := by
      by_contra h0; push Not at h0; exact hp_ne i₀ (by ext w; exact h0 w)
    obtain ⟨w, hw⟩ := hex_w
    let u := p i₀ w
    have hu_ne : u ≠ 0 := hw
    have hp₀u : p i₀ u = u := congrFun (congrArg DFunLike.coe (hp_proj i₀).2) w
    have hinner : ⟪u, (star x * x) u⟫_ℂ = c * ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [hc, smul_apply, hp₀u, inner_smul_right, inner_self_eq_norm_sq_to_K]
      change c * ((‖u‖ : ℂ) ^ 2) = c * ((‖u‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.ofReal_pow]
    have hinner_nn : (0 : ℂ) ≤ ⟪u, (star x * x) u⟫_ℂ :=
      (ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg x)).inner_nonneg_right u
    have hnorm_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu_ne)
    have hc_im : c.im = 0 := by
      rw [hinner] at hinner_nn
      have him := (Complex.nonneg_iff.mp hinner_nn).2
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him
      exact (mul_eq_zero.mp him.symm).resolve_right hnorm_pos.ne'
    have hc_re_nn : 0 ≤ c.re := by
      rw [hinner] at hinner_nn
      have hre := (Complex.nonneg_iff.mp hinner_nn).1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
      nlinarith
    have hc_eq : c = (c.re : ℂ) := Complex.ext rfl (by simp [hc_im])
    have hc_pos : 0 < c.re := by
      rcases hc_re_nn.eq_or_lt with h0 | hpos
      · exfalso
        have hc0 : c = 0 := by rw [hc_eq, ← h0]; simp
        rw [hc0, zero_smul] at hc
        exact hxx_ne hc
      · exact hpos
    let v : H →L[ℂ] H := (((Real.sqrt c.re)⁻¹ : ℝ) : ℂ) • x
    have hv_mem : v ∈ 𝒜 := Subalgebra.smul_mem 𝒜.toSubalgebra hx_mem _
    have hpv : p i * v = v := by simp only [v, mul_smul_comm, hpx]
    have hvp : v * p i₀ = v := by simp only [v, smul_mul_assoc, hxp]
    have hvv0 : star v * v = p i₀ := by
      have hc' : star x * x = (c.re : ℂ) • p i₀ := hc_eq ▸ hc
      rw [show v = (((Real.sqrt c.re)⁻¹ : ℝ) : ℂ) • x from rfl, star_smul, smul_mul_assoc,
        mul_smul_comm, smul_smul, hc', smul_smul]
      have hinv : (((Real.sqrt c.re)⁻¹ : ℝ) : ℂ) *
          (star (((Real.sqrt c.re)⁻¹ : ℝ) : ℂ) * (c.re : ℂ)) = 1 := by
        simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
        have hreal : (Real.sqrt c.re)⁻¹ * ((Real.sqrt c.re)⁻¹ * c.re) = 1 := by
          have hs : Real.sqrt c.re ≠ 0 := (Real.sqrt_pos.mpr hc_pos).ne'
          field_simp [hs]
          exact (Real.sq_sqrt hc_pos.le).symm
        rw [hreal, Complex.ofReal_one]
      rw [mul_comm (star _), mul_assoc, hinv, one_smul]
    have hvv_proj : IsOrthProj (v * star v) := by
      refine ⟨by simp [IsSelfAdjoint], ?_⟩
      calc (v * star v) * (v * star v) = v * (star v * v) * star v := by simp only [mul_assoc]
        _ = v * p i₀ * star v := by rw [hvv0]
        _ = v * star v := by rw [hvp]
    have hvv_ne : v * star v ≠ 0 := by
      intro h0
      have h1 := CStarRing.norm_star_mul_self (x := star v)
      have h2 := CStarRing.norm_star_mul_self (x := v)
      rw [star_star, h0, norm_zero] at h1
      rw [hvv0] at h2
      have hsv0 : star v = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp h1.symm)
      have hv0 : v = 0 := by simpa using congrArg star hsv0
      rw [hv0, norm_zero, mul_zero] at h2
      exact hp_ne i₀ (norm_eq_zero.mp h2)
    have hvv_pi : (v * star v) * p i = v * star v := by
      have hsv : star v * p i = star v := by
        have h := congrArg star hpv
        rwa [star_mul, (hp_proj i).1.star_eq] at h
      rw [mul_assoc, hsv]
    have hvv1 : v * star v = p i :=
      hp_min i (v * star v) (mul_mem hv_mem (star_mem hv_mem)) hvv_proj hvv_ne hvv_pi
    exact ⟨v, hv_mem, hpv, hvp, hvv0, hvv1⟩
  choose v hv_mem hpv hvp hvv0 hvv1 using hex_v
  -- Matrix units `e i j = v i * star (v j)`
  let e : Fin d₁ → Fin d₁ → (H →L[ℂ] H) := fun i j ↦ v i * star (v j)
  have he_mem : ∀ i j, e i j ∈ 𝒜 := fun i j ↦ mul_mem (hv_mem i) (star_mem (hv_mem j))
  have hv_orth : ∀ i j, star (v i) * v j = if i = j then p i₀ else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [hvv0 i]
    · simp only [hij, ↓reduceIte]
      have hsv : star (v i) * p i = star (v i) := by
        have h := congrArg star (hpv i)
        rwa [star_mul, (hp_proj i).1.star_eq] at h
      calc star (v i) * v j = (star (v i) * p i) * (p j * v j) := by rw [hsv, hpv j]
        _ = star (v i) * (p i * p j) * v j := by simp only [mul_assoc]
        _ = 0 := by rw [hp_orth i j hij, mul_zero, zero_mul]
  let H₂ : Submodule ℂ H := LinearMap.range (p i₀).toLinearMap
  let d₂ : ℕ := Module.finrank ℂ H₂
  have hd₂ : 0 < d₂ := projRank_pos_of_ne_zero (hp_ne i₀)
  let b₂ : OrthonormalBasis (Fin d₂) ℂ H₂ := stdOrthonormalBasis ℂ H₂
  have hb₂_fix : ∀ k : Fin d₂, p i₀ (b₂ k : H) = (b₂ k : H) := by
    intro k
    rcases (b₂ k).2 with ⟨y, hy⟩
    change p i₀ y = (b₂ k : H) at hy
    have h1 : p i₀ (p i₀ y) = p i₀ y := congrFun (congrArg DFunLike.coe (hp_proj i₀).2) y
    simpa [hy] using h1
  -- Build unitary `U : ℂ^{d₁ × d₂} ≃ₗᵢ[ℂ] H` from the orthonormal basis `ψ (i, k) = v i (b₂ k)`.
  let ψ : Fin d₁ × Fin d₂ → H := fun ik ↦ v ik.1 (b₂ ik.2 : H)
  have hψ_ortho : Orthonormal ℂ ψ := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, k⟩ ⟨j, l⟩
    simp only [ψ]
    have hadj : ⟪v i (b₂ k : H), v j (b₂ l : H)⟫_ℂ =
        ⟪(b₂ k : H), (star (v i) * v j) (b₂ l : H)⟫_ℂ := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    rw [hadj, hv_orth i j]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, hb₂_fix l]
      have hbk : ⟪(b₂ k : H), (b₂ l : H)⟫_ℂ = ⟪b₂ k, b₂ l⟫_ℂ := rfl
      rw [hbk, orthonormal_iff_ite.mp b₂.orthonormal k l]
      simp
    · simp [hij]
  have hψ_span : Submodule.span ℂ (Set.range ψ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx_sum : x = ∑ i : Fin d₁, v i (star (v i) x) := by
      have h1 : x = (∑ i : Fin d₁, p i) x := by rw [hp_sum]; rfl
      conv_lhs => rw [h1, FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hvv1 i]; rfl
    rw [hx_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hmem2 : star (v i) x ∈ H₂ := by
      have hvp' : p i₀ * star (v i) = star (v i) := by
        have h := congrArg star (hvp i)
        rwa [star_mul, (hp_proj i₀).1.star_eq] at h
      exact ⟨star (v i) x, congrFun (congrArg DFunLike.coe hvp') x⟩
    let w : H₂ := ⟨star (v i) x, hmem2⟩
    have hw_exp : (w : H) = ∑ k : Fin d₂, ⟪b₂ k, w⟫_ℂ • (b₂ k : H) := by
      have := congrArg Subtype.val (b₂.sum_repr' w).symm
      simpa using this
    change v i (w : H) ∈ _
    rw [hw_exp, map_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)
  let U : EuclideanSpace ℂ (Fin d₁ × Fin d₂) ≃ₗᵢ[ℂ] H :=
    { toFun f := ∑ q : Fin d₁ × Fin d₂, f.ofLp q • ψ q
      invFun x := WithLp.toLp 2 fun q ↦ ⟪ψ q, x⟫_ℂ
      map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' c f := by simp [mul_smul, Finset.smul_sum]
      left_inv f := by
        ext q
        change ⟪ψ q, ∑ r : Fin d₁ × Fin d₂, f.ofLp r • ψ r⟫_ℂ = f.ofLp q
        rw [inner_sum, Finset.sum_eq_single q]
        · rw [inner_smul_right, orthonormal_iff_ite.mp hψ_ortho q q]; simp
        · intro r _ hr
          rw [inner_smul_right, orthonormal_iff_ite.mp hψ_ortho q r]; simp [Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ q) h
      right_inv x := by
        set y : H := ∑ q : Fin d₁ × Fin d₂, ⟪ψ q, x⟫_ℂ • ψ q
        have horth : ∀ z ∈ Submodule.span ℂ (Set.range ψ), ⟪z, x - y⟫_ℂ = 0 := by
          intro z hz
          refine Submodule.span_induction (p := fun z _ ↦ ⟪z, x - y⟫_ℂ = 0) ?_ (by simp)
            (fun u v _ _ hu hv ↦ by rw [inner_add_left, hu, hv, add_zero])
            (fun c u _ hu ↦ by rw [inner_smul_left, hu, mul_zero]) hz
          rintro _ ⟨q, rfl⟩
          rw [inner_sub_right, inner_sum, Finset.sum_eq_single q]
          · rw [inner_smul_right, orthonormal_iff_ite.mp hψ_ortho q q]; simp
          · intro r _ hr
            rw [inner_smul_right, orthonormal_iff_ite.mp hψ_ortho q r]; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ q) h
        have hself : ⟪x - y, x - y⟫_ℂ = 0 := horth (x - y) (hψ_span ▸ Submodule.mem_top)
        exact (sub_eq_zero.mp (inner_self_eq_zero.mp hself)).symm
      norm_map' f := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [PiLp.norm_sq_eq_of_L2, norm_sq_eq_re_inner (𝕜 := ℂ)]
        change (⟪∑ q : Fin d₁ × Fin d₂, f.ofLp q • ψ q,
          ∑ r : Fin d₁ × Fin d₂, f.ofLp r • ψ r⟫_ℂ).re = ∑ q : Fin d₁ × Fin d₂, ‖f.ofLp q‖ ^ 2
        rw [sum_inner]
        have hdiag : ∀ q : Fin d₁ × Fin d₂,
            ⟪f.ofLp q • ψ q, ∑ r : Fin d₁ × Fin d₂, f.ofLp r • ψ r⟫_ℂ =
            ((‖f.ofLp q‖ ^ 2 : ℝ) : ℂ) := by
          intro q
          rw [inner_sum, Finset.sum_eq_single q]
          · rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hψ_ortho q q]
            simp only [↓reduceIte, mul_one]
            rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          · intro r _ hr
            rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hψ_ortho q r]
            simp only [Ne.symm hr, ↓reduceIte, mul_zero]
          · intro h; exact absurd (Finset.mem_univ q) h
        simp_rw [hdiag, ← Complex.ofReal_sum, Complex.ofReal_re] }
  have hconj_sum : ∀ A : Matrix (Fin d₁) (Fin d₁) ℂ,
      U.symm.toContinuousLinearMap ∘L (∑ i : Fin d₁, ∑ j : Fin d₁, A i j • e i j) ∘L
        U.toContinuousLinearMap =
      (A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)).toEuclideanLin.toContinuousLinearMap := by
    intro A
    ext x ⟨a, b⟩
    change ⟪ψ (a, b), (∑ i : Fin d₁, ∑ j : Fin d₁, A i j • e i j)
      (∑ q : Fin d₁ × Fin d₂, x.ofLp q • ψ q)⟫_ℂ =
      ((A ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) *ᵥ x.ofLp) (a, b)
    have he_act : ∀ (i j r : Fin d₁) (l : Fin d₂),
        e i j (ψ (r, l)) = if j = r then ψ (i, l) else 0 := by
      intro i j r l
      change (v i * (star (v j) * v r)) (b₂ l : H) = _
      rw [hv_orth j r]
      split_ifs
      · simp only [mul_apply_eq_comp, hb₂_fix l]; rfl
      · simp
    have he_inner : ∀ i j : Fin d₁,
        ⟪ψ (a, b), e i j (∑ q : Fin d₁ × Fin d₂, x.ofLp q • ψ q)⟫_ℂ =
        if i = a then x.ofLp (j, b) else 0 := by
      intro i j
      rw [map_sum, inner_sum, Fintype.sum_prod_type]
      simp_rw [map_smul, inner_smul_right, he_act]
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single b]
        · simp only [↓reduceIte, orthonormal_iff_ite.mp hψ_ortho (a, b) (i, b), Prod.mk.injEq,
            and_true, mul_ite, mul_one, mul_zero, eq_comm]
        · intro l _ hl
          simp [orthonormal_iff_ite.mp hψ_ortho (a, b) (i, l), Ne.symm hl]
        · intro h; exact absurd (Finset.mem_univ b) h
      · intro r _ hr
        refine Finset.sum_eq_zero fun l _ ↦ ?_
        simp [Ne.symm hr]
      · intro h; exact absurd (Finset.mem_univ j) h
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, inner_sum,
      inner_smul_right, he_inner]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a (fun i _ hi ↦ by simp [hi]) (fun h ↦ absurd (Finset.mem_univ a) h)]
    simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_eq_single b (fun l _ hl ↦ by simp [Ne.symm hl])
      (fun h ↦ absurd (Finset.mem_univ b) h)]
    simp
  refine ⟨d₁, d₂, hd₁, hd₂, U, fun T ↦ ?_⟩
  constructor
  · intro hT
    have hex_c : ∀ i j : Fin d₁, ∃ c : ℂ, star (v i) * T * v j = c • p i₀ := by
      intro i j
      have hmem : star (v i) * T * v j ∈ 𝒜 := mul_mem (mul_mem (star_mem (hv_mem i)) hT) (hv_mem j)
      have hcor : p i₀ * (star (v i) * T * v j) * p i₀ = star (v i) * T * v j := by
        have hsv : p i₀ * star (v i) = star (v i) := by
          have h := congrArg star (hvp i)
          rwa [star_mul, (hp_proj i₀).1.star_eq] at h
        rw [← mul_assoc (p i₀), ← mul_assoc (p i₀), hsv, mul_assoc (star (v i) * T), hvp j]
      obtain ⟨c, hc⟩ :=
        corner_eq_scalars_of_minimal_proj 𝒜 (hp_mem i₀) (hp_proj i₀) (hp_min i₀) hmem
      exact ⟨c, hcor ▸ hc⟩
    choose c hc using hex_c
    have hT_eq : T = ∑ i : Fin d₁, ∑ j : Fin d₁, c i j • e i j := by
      calc T = (∑ i : Fin d₁, p i) * T * (∑ j : Fin d₁, p j) := by rw [hp_sum, one_mul, mul_one]
        _ = ∑ i : Fin d₁, ∑ j : Fin d₁, p i * T * p j := by
            simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
        _ = ∑ i : Fin d₁, ∑ j : Fin d₁, v i * (star (v i) * T * v j) * star (v j) := by
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
            rw [← hvv1 i, ← hvv1 j]; simp only [mul_assoc]
        _ = ∑ i : Fin d₁, ∑ j : Fin d₁, c i j • e i j := by
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hc i j, mul_smul_comm, smul_mul_assoc, hvp i]
    refine ⟨Matrix.of c, ?_⟩
    rw [hT_eq]
    exact hconj_sum (Matrix.of c)
  · rintro ⟨A, hA⟩
    have hT_eq : T = ∑ i : Fin d₁, ∑ j : Fin d₁, A i j • e i j := by
      have hconj_eq : U.symm.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap =
          U.symm.toContinuousLinearMap ∘L (∑ i : Fin d₁, ∑ j : Fin d₁, A i j • e i j) ∘L
            U.toContinuousLinearMap := by
        rw [hA, hconj_sum A]
      ext x
      have hx := congrFun (congrArg DFunLike.coe hconj_eq) (U.symm x)
      change U.symm (T (U (U.symm x))) =
        U.symm ((∑ i : Fin d₁, ∑ j : Fin d₁, A i j • e i j) (U (U.symm x))) at hx
      rw [LinearIsometryEquiv.apply_symm_apply] at hx
      exact U.symm.injective hx
    rw [hT_eq]
    exact sum_mem fun i _ ↦ sum_mem fun j _ ↦ Subalgebra.smul_mem 𝒜.toSubalgebra (he_mem i j) _

/-- Simultaneous commutant decomposition: for any finite-dimensional unital `C⋆`-subalgebra
`𝒜 ⊆ 𝔹(H)` on a finite-dimensional complex Hilbert space `H`, there exist `m : ℕ`, positive block
dimensions `dA, dB : Fin m → ℕ`, and a unitary isomorphism
`U : PiLp 2 (fun j : Fin m ↦ EuclideanSpace ℂ (Fin (dA j) × Fin (dB j))) ≃ₗᵢ[ℂ] H` such that:
1. `T ∈ 𝒜` if and only if `U⁻¹ T U` is block-diagonal with `j`-th block `A_j ⊗ 1_{dB j}`;
2. `X` commutes with every `T ∈ 𝒜` if and only if `U⁻¹ X U` is block-diagonal with `j`-th block
   `1_{dA j} ⊗ B_j`. -/
theorem exists_commutant_tensor_decomp (𝒜 : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∃ (m : ℕ) (dA dB : Fin m → ℕ) (_ : ∀ j, 0 < dA j) (_ : ∀ j, 0 < dB j)
      (U : PiLp 2 (fun j : Fin m ↦ EuclideanSpace ℂ (Fin (dA j) × Fin (dB j))) ≃ₗᵢ[ℂ] H),
      (∀ T : H →L[ℂ] H, T ∈ 𝒜 ↔
        ∃ A : ∀ j : Fin m, Matrix (Fin (dA j)) (Fin (dA j)) ℂ,
          ∀ f j, (U.symm (T (U f))).ofLp j =
            (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin (f.ofLp j)) ∧
      (∀ X : H →L[ℂ] H, (∀ T ∈ 𝒜, Commute X T) ↔
        ∃ B : ∀ j : Fin m, Matrix (Fin (dB j)) (Fin (dB j)) ℂ,
          ∀ f j, (U.symm (X (U f))).ofLp j =
            ((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B j).toEuclideanLin (f.ofLp j)) := by
  classical
  obtain ⟨m, z, hz_mem, hz_proj, hz_ne, hz_comm, hz_orth, hz_sum, hz_scalar⟩ :=
    exists_central_orthProj_decomp 𝒜
  -- On each block `H_j = ran (z j)`, build the restricted simple `C⋆`-subalgebra `𝒜_j`.
  let Hj : Fin m → Submodule ℂ H := fun j ↦ LinearMap.range (z j).toLinearMap
  have : ∀ j, CompleteSpace (Hj j) := fun j ↦ FiniteDimensional.completeSpace ℂ (Hj j)
  have hHj_nt : ∀ j, Nontrivial (Hj j) := fun j ↦
    Module.nontrivial_of_finrank_pos (projRank_pos_of_ne_zero (hz_ne j))
  let restr : ∀ (j : Fin m) (T : H →L[ℂ] H), Commute T (z j) → (Hj j →L[ℂ] Hj j) :=
    fun j T hT ↦
      (LinearMap.codRestrict (Hj j) (T.toLinearMap.comp (Hj j).subtype) fun ⟨x, hx⟩ ↦ by
        rcases hx with ⟨y, rfl⟩
        exact ⟨T y, (congrFun (congrArg DFunLike.coe hT.eq) y).symm⟩).toContinuousLinearMap
  have hrestr_coe : ∀ (j : Fin m) (T : H →L[ℂ] H) (hT : Commute T (z j)) (x : Hj j),
      (restr j T hT x : H) = T (x : H) := fun _ _ _ _ ↦ rfl
  let 𝒜j : ∀ j : Fin m, StarSubalgebra ℂ (Hj j →L[ℂ] Hj j) := fun j ↦
    { carrier := { S | ∃ a, ∃ ha : a ∈ 𝒜, S = restr j a (hz_comm j a ha).symm }
      mul_mem' := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a * b, mul_mem ha hb, rfl⟩
      one_mem' := ⟨1, one_mem 𝒜, rfl⟩
      add_mem' := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, add_mem ha hb, rfl⟩
      zero_mem' := ⟨0, zero_mem 𝒜, rfl⟩
      algebraMap_mem' := fun c ↦ ⟨algebraMap ℂ _ c, algebraMap_mem 𝒜 c, by
        ext x; simp [Algebra.algebraMap_eq_smul_one, hrestr_coe]⟩
      star_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨star a, star_mem ha, ?_⟩
        apply ContinuousLinearMap.ext; intro x
        refine ext_inner_left ℂ fun y ↦ ?_
        have h1 : ⟪y, star (restr j a (hz_comm j a ha).symm) x⟫_ℂ =
            ⟪restr j a (hz_comm j a ha).symm y, x⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
        change ⟪y, star (restr j a (hz_comm j a ha).symm) x⟫_ℂ = ⟪(y : H), (star a) (x : H)⟫_ℂ
        rw [h1]
        change ⟪a (y : H), (x : H)⟫_ℂ = ⟪(y : H), (star a) (x : H)⟫_ℂ
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] }
  have h𝒜j_simple : ∀ j : Fin m, IsSimpleRing (𝒜j j) := fun j ↦ by
    have := hHj_nt j
    rw [isSimpleRing_iff_trivial_center (𝒜j j)]
    rintro ⟨S, a, ha, rfl⟩ hS_comm
    let c := a * z j
    have hc_mem : c ∈ 𝒜 := mul_mem ha (hz_mem j)
    have hc_comm : ∀ b ∈ 𝒜, Commute c b := fun b hb ↦ by
      have hcomm_j : Commute (restr j a (hz_comm j a ha).symm)
          (restr j b (hz_comm j b hb).symm) :=
        congrArg Subtype.val (hS_comm ⟨restr j b (hz_comm j b hb).symm, b, hb, rfl⟩)
      apply ContinuousLinearMap.ext; intro x
      have hact : ((restr j a (hz_comm j a ha).symm)
          ((restr j b (hz_comm j b hb).symm) ⟨z j x, ⟨x, rfl⟩⟩) : H) =
          ((restr j b (hz_comm j b hb).symm)
          ((restr j a (hz_comm j a ha).symm) ⟨z j x, ⟨x, rfl⟩⟩) : H) :=
        congrArg Subtype.val (congrFun (congrArg DFunLike.coe hcomm_j.eq) ⟨z j x, ⟨x, rfl⟩⟩)
      have h1 : (c * b) x = a (b (z j x)) := by
        change ((a * z j) * b) x = _
        rw [mul_assoc, (hz_comm j b hb).eq]; rfl
      exact h1.trans hact
    obtain ⟨α, hα⟩ := hz_scalar j c hc_mem hc_comm
    refine ⟨α, Subtype.ext ?_⟩
    ext ⟨x, y, rfl⟩
    have hzx : z j (z j y) = z j y := congrFun (congrArg DFunLike.coe (hz_proj j).2) y
    have h1 := congrFun (congrArg DFunLike.coe hα) y
    simp only [c, mul_apply_eq_comp, smul_apply, hzx] at h1
    exact h1
  have hblock : ∀ j : Fin m, ∃ (dA dB : ℕ) (_ : 0 < dA) (_ : 0 < dB)
      (Uj : EuclideanSpace ℂ (Fin dA × Fin dB) ≃ₗᵢ[ℂ] Hj j),
      ∀ S : Hj j →L[ℂ] Hj j, S ∈ 𝒜j j ↔
        ∃ A : Matrix (Fin dA) (Fin dA) ℂ,
          Uj.symm.toContinuousLinearMap ∘L S ∘L Uj.toContinuousLinearMap =
            (A ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)).toEuclideanLin.toContinuousLinearMap :=
    fun j ↦ by
      have := hHj_nt j
      have := h𝒜j_simple j
      exact exists_tensorFactor_of_isSimpleRing (𝒜j j)
  choose dA dB hdA hdB Uj hUj using hblock
  -- Assemble the direct-sum unitary `U : PiLp 2 (fun j ↦ ℂ^{dA j × dB j}) ≃ₗᵢ[ℂ] H`.
  let U : PiLp 2 (fun j : Fin m ↦ EuclideanSpace ℂ (Fin (dA j) × Fin (dB j))) ≃ₗᵢ[ℂ] H :=
    { toFun f := ∑ j : Fin m, (Uj j (f.ofLp j) : H)
      invFun x := WithLp.toLp 2 fun j ↦ (Uj j).symm ⟨z j x, ⟨x, rfl⟩⟩
      map_add' f g := by
        simp only [WithLp.ofLp_add, Pi.add_apply, map_add, Submodule.coe_add,
          Finset.sum_add_distrib]
      map_smul' c f := by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, map_smul, SetLike.val_smul, Finset.smul_sum]
        rfl
      left_inv f := by
        ext j p
        have hzf : z j (∑ k : Fin m, (Uj k (f.ofLp k) : H)) = (Uj j (f.ofLp j) : H) := by
          rw [map_sum, Finset.sum_eq_single j]
          · rcases (Uj j (f.ofLp j)).2 with ⟨y, hy⟩
            change z j y = (Uj j (f.ofLp j) : H) at hy
            have h1 := congrFun (congrArg DFunLike.coe (hz_proj j).2) y
            simpa [hy] using h1
          · intro k _ hkj
            rcases (Uj k (f.ofLp k)).2 with ⟨y, hy⟩
            change z k y = (Uj k (f.ofLp k) : H) at hy
            have h1 := congrFun (congrArg DFunLike.coe (hz_orth j k hkj.symm)) y
            simpa [hy] using h1
          · intro h; exact absurd (Finset.mem_univ j) h
        have hsub : (⟨z j (∑ k : Fin m, (Uj k (f.ofLp k) : H)), ⟨_, rfl⟩⟩ : Hj j) =
            Uj j (f.ofLp j) := Subtype.ext hzf
        change ((Uj j).symm ⟨z j (∑ k : Fin m, (Uj k (f.ofLp k) : H)), ⟨_, rfl⟩⟩).ofLp p =
          (f.ofLp j).ofLp p
        rw [hsub, LinearIsometryEquiv.symm_apply_apply]
      right_inv x := by
        simp only [LinearIsometryEquiv.apply_symm_apply]
        have := congrFun (congrArg DFunLike.coe hz_sum) x
        simpa [FunLike.coe_sum, Finset.sum_apply] using this
      norm_map' f := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [PiLp.norm_sq_eq_of_L2, norm_sq_eq_re_inner (𝕜 := ℂ)]
        change (⟪∑ j : Fin m, (Uj j (f.ofLp j) : H),
          ∑ k : Fin m, (Uj k (f.ofLp k) : H)⟫_ℂ).re = ∑ j : Fin m, ‖f.ofLp j‖ ^ 2
        rw [sum_inner]
        simp_rw [inner_sum]
        have horth_inner : ∀ j k : Fin m, j ≠ k →
            ⟪(Uj j (f.ofLp j) : H), (Uj k (f.ofLp k) : H)⟫_ℂ = 0 := by
          intro j k hjk
          rcases (Uj j (f.ofLp j)).2 with ⟨y₁, hy₁⟩
          rcases (Uj k (f.ofLp k)).2 with ⟨y₂, hy₂⟩
          change z j y₁ = (Uj j (f.ofLp j) : H) at hy₁
          change z k y₂ = (Uj k (f.ofLp k) : H) at hy₂
          rw [← hy₁, ← hy₂]
          have hsym :=
            ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hz_proj j).1 y₁ (z k y₂)
          simp only [ContinuousLinearMap.coe_coe] at hsym
          rw [hsym]
          have h0 : z j (z k y₂) = 0 := congrFun (congrArg DFunLike.coe (hz_orth j k hjk)) y₂
          rw [h0, inner_zero_right]
        have hdiag : ∀ j : Fin m,
            ∑ k : Fin m, ⟪(Uj j (f.ofLp j) : H), (Uj k (f.ofLp k) : H)⟫_ℂ =
            ((‖f.ofLp j‖ ^ 2 : ℝ) : ℂ) := by
          intro j
          rw [Finset.sum_eq_single j]
          · change ⟪Uj j (f.ofLp j), Uj j (f.ofLp j)⟫_ℂ = _
            rw [LinearIsometryEquiv.inner_map_map, inner_self_eq_norm_sq_to_K]
            change ((‖f.ofLp j‖ : ℂ) ^ 2) = ((‖f.ofLp j‖ ^ 2 : ℝ) : ℂ)
            rw [Complex.ofReal_pow]
          · intro k _ hkj; exact horth_inner j k hkj.symm
          · intro h; exact absurd (Finset.mem_univ j) h
        simp_rw [hdiag, ← Complex.ofReal_sum, Complex.ofReal_re] }
  have hU_apply : ∀ f, U f = ∑ j : Fin m, (Uj j (f.ofLp j) : H) := fun _ ↦ rfl
  have hU_symm_apply : ∀ x j, (U.symm x).ofLp j = (Uj j).symm ⟨z j x, ⟨x, rfl⟩⟩ := fun _ _ ↦ rfl
  have hblk : ∀ (T : H →L[ℂ] H) (hcomm : ∀ j, Commute T (z j))
      (f : PiLp 2 fun j : Fin m ↦ EuclideanSpace ℂ (Fin (dA j) × Fin (dB j))) (j : Fin m),
      (U.symm (T (U f))).ofLp j =
        (Uj j).symm (restr j T (hcomm j) (Uj j (f.ofLp j))) := by
    intro T hcomm f j
    rw [hU_symm_apply, hU_apply]
    have hzk : ∀ k : Fin m, z j (T (Uj k (f.ofLp k) : H)) =
        if k = j then T (Uj j (f.ofLp j) : H) else 0 := by
      intro k
      rcases (Uj k (f.ofLp k)).2 with ⟨y, hy⟩
      change z k y = (Uj k (f.ofLp k) : H) at hy
      have h1 : z j (T (z k y)) = T (z j (z k y)) :=
        congrFun (congrArg DFunLike.coe (hcomm j).eq.symm) (z k y)
      rw [← hy, h1]
      change T ((z j * z k) y) = _
      by_cases hkj : k = j
      · subst hkj
        rw [(hz_proj k).2, hy]
        simp
      · simp [hkj, hz_orth j k (Ne.symm hkj)]
    have hsub : (⟨z j (T (∑ k : Fin m, (Uj k (f.ofLp k) : H))),
        ⟨T (∑ k : Fin m, (Uj k (f.ofLp k) : H)), rfl⟩⟩ : Hj j) =
        restr j T (hcomm j) (Uj j (f.ofLp j)) := by
      apply Subtype.ext
      change z j (T (∑ k : Fin m, (Uj k (f.ofLp k) : H))) = T (Uj j (f.ofLp j) : H)
      rw [map_sum, map_sum, Finset.sum_eq_single j]
      · simp [hzk j]
      · intro k _ hkj; simp [hzk k, hkj]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsub]
  have hpart1 : ∀ T : H →L[ℂ] H, T ∈ 𝒜 ↔
      ∃ A : ∀ j : Fin m, Matrix (Fin (dA j)) (Fin (dA j)) ℂ,
        ∀ f j, (U.symm (T (U f))).ofLp j =
          (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin (f.ofLp j) := by
    intro T
    constructor
    · intro hT
      have hcomm : ∀ j, Commute T (z j) := fun j ↦ (hz_comm j T hT).symm
      have hblock_A : ∀ j, ∃ A : Matrix (Fin (dA j)) (Fin (dA j)) ℂ,
          (Uj j).symm.toContinuousLinearMap ∘L restr j T (hcomm j) ∘L
            (Uj j).toContinuousLinearMap =
            (A ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin.toContinuousLinearMap :=
        fun j ↦ (hUj j (restr j T (hcomm j))).mp ⟨T, hT, rfl⟩
      choose A hA using hblock_A
      refine ⟨A, fun f j ↦ ?_⟩
      rw [hblk T hcomm f j]
      exact congrFun (congrArg DFunLike.coe (hA j)) (f.ofLp j)
    · rintro ⟨A, hA⟩
      have hAj : ∀ j : Fin m, ∃ a ∈ 𝒜, ∀ x : Hj j,
          (Uj j).symm ⟨z j (a x), ⟨a x, rfl⟩⟩ =
            (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin ((Uj j).symm x) := by
        intro j
        let Sj : Hj j →L[ℂ] Hj j := (Uj j).toContinuousLinearMap ∘L
          (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin.toContinuousLinearMap ∘L
          (Uj j).symm.toContinuousLinearMap
        have hSj : Sj ∈ 𝒜j j := (hUj j Sj).mpr ⟨A j, by ext v; simp [Sj]⟩
        rcases hSj with ⟨a, ha, hSj_eq⟩
        refine ⟨a, ha, fun x ↦ ?_⟩
        have h1 : (⟨z j (a (x : H)), ⟨a (x : H), rfl⟩⟩ : Hj j) = Sj x := by
          apply Subtype.ext
          change z j (a (x : H)) = (Sj x : H)
          rcases x.2 with ⟨y, hy⟩
          change z j y = (x : H) at hy
          have h2 : z j (a (x : H)) = a (z j (x : H)) :=
            congrFun (congrArg DFunLike.coe (hz_comm j a ha).eq) (x : H)
          have hzx : z j (x : H) = (x : H) := by
            simpa [hy] using congrFun (congrArg DFunLike.coe (hz_proj j).2) y
          rw [h2, hzx, hSj_eq]; rfl
        rw [h1]; simp [Sj]
      choose a ha_mem ha_act using hAj
      have hT_eq : T = ∑ j : Fin m, a j * z j := by
        ext x
        apply U.symm.injective
        ext j p
        have hfx := hA (U.symm x) j
        rw [LinearIsometryEquiv.apply_symm_apply] at hfx
        rw [hfx, FunLike.coe_sum, Finset.sum_apply,
          hU_symm_apply (∑ k : Fin m, (a k * z k) x) j]
        have hsum_z : z j (∑ k : Fin m, (a k * z k) x) = z j (a j (z j x)) := by
          rw [map_sum, Finset.sum_eq_single j]
          · rfl
          · intro k _ hkj
            calc z j (a k (z k x)) = a k (z j (z k x)) :=
                  congrFun (congrArg DFunLike.coe (hz_comm j (a k) (ha_mem k)).eq) (z k x)
              _ = a k ((z j * z k) x) := rfl
              _ = 0 := by rw [hz_orth j k (Ne.symm hkj)]; simp
          · intro h; exact absurd (Finset.mem_univ j) h
        have hsub : (⟨z j (∑ k : Fin m, (a k * z k) x),
            ⟨∑ k : Fin m, (a k * z k) x, rfl⟩⟩ : Hj j) =
            ⟨z j (a j (⟨z j x, ⟨x, rfl⟩⟩ : Hj j)), ⟨a j (z j x), rfl⟩⟩ := Subtype.ext hsum_z
        rw [hsub, ha_act j ⟨z j x, ⟨x, rfl⟩⟩, ← hU_symm_apply]
      rw [hT_eq]
      exact sum_mem fun j _ ↦ mul_mem (ha_mem j) (hz_mem j)
  refine ⟨m, dA, dB, hdA, hdB, U, hpart1, ?_⟩
  intro X
  constructor
  · intro hX
    have hcomm_z : ∀ j, Commute X (z j) := fun j ↦ hX (z j) (hz_mem j)
    have hblock_B : ∀ j : Fin m, ∃ B : Matrix (Fin (dB j)) (Fin (dB j)) ℂ,
        (Uj j).symm.toContinuousLinearMap ∘L restr j X (hcomm_z j) ∘L
          (Uj j).toContinuousLinearMap =
          ((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B).toEuclideanLin.toContinuousLinearMap := by
      intro j
      let b := (EuclideanSpace.basisFun (Fin (dA j) × Fin (dB j)) ℂ).toBasis
      let Cclm := (Uj j).symm.toContinuousLinearMap ∘L restr j X (hcomm_z j) ∘L
        (Uj j).toContinuousLinearMap
      let Cmat := LinearMap.toMatrix b b Cclm.toLinearMap
      let Cswap := Cmat.submatrix Prod.swap Prod.swap
      have hCswap_comm : ∀ A : Matrix (Fin (dA j)) (Fin (dA j)) ℂ,
          Commute Cswap ((1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ) ⊗ₖ A) := by
        intro A
        let MA :=
          (A ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin.toContinuousLinearMap
        let Sj : Hj j →L[ℂ] Hj j :=
          (Uj j).toContinuousLinearMap ∘L MA ∘L (Uj j).symm.toContinuousLinearMap
        rcases (hUj j Sj).mpr ⟨A, by ext v; simp [Sj, MA]⟩ with ⟨a, ha, hSj_eq⟩
        have hXSj : Commute (restr j X (hcomm_z j)) Sj := by
          rw [hSj_eq]; ext ⟨y, _⟩; exact congrFun (congrArg DFunLike.coe (hX a ha).eq) y
        have hCclm_comm : Commute Cclm MA := by
          apply ContinuousLinearMap.ext; intro v
          have h1 := congrFun (congrArg DFunLike.coe hXSj.eq) (Uj j v)
          simpa [Cclm, Sj] using congrArg (Uj j).symm h1
        have hCmat_comm : Commute Cmat (A ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)) := by
          have htoM : LinearMap.toMatrix b b MA.toLinearMap =
              A ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ) := LinearMap.toMatrix_toLin b b _
          have h := congrArg (LinearMap.toMatrix b b)
            (congrArg ContinuousLinearMap.toLinearMap hCclm_comm.eq)
          rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
            LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, htoM] at h
          exact h
        ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
        have h := congrFun (congrFun hCmat_comm.eq (a₁, b₁)) (a₂, b₂)
        simp only [Matrix.mul_apply, Cswap, Matrix.submatrix_apply, Prod.swap_prod_mk,
          Fintype.sum_prod_type, Matrix.kroneckerMap_apply] at h ⊢
        rw [Finset.sum_comm]
        have hrhs : ∑ x : Fin (dB j), ∑ y : Fin (dA j),
            ((1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ) b₁ x * A a₁ y) * Cmat (y, x) (a₂, b₂) =
            ∑ y : Fin (dA j), ∑ x : Fin (dB j),
            (A a₁ y * (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ) b₁ x) * Cmat (y, x) (a₂, b₂) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
        rw [hrhs, ← h]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
      obtain ⟨B, hB⟩ := commutant_one_kronecker_matrix Cswap hCswap_comm
      refine ⟨B, ?_⟩
      have hCmat_eq : Cmat = (1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B := by
        ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        simpa [Cswap, Matrix.kroneckerMap_apply, mul_comm] using
          congrFun (congrFun hB (b₁, a₁)) (b₂, a₂)
      ext v p
      have hlin : Cclm.toLinearMap =
          ((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B).toEuclideanLin := by
        apply (LinearMap.toMatrix b b).injective
        have htoM : LinearMap.toMatrix b b
            (((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B).toEuclideanLin) =
            (1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B := LinearMap.toMatrix_toLin b b _
        change Cmat = _
        rw [htoM, hCmat_eq]
      exact congrArg (fun f : _ →ₗ[ℂ] _ ↦ (f v).ofLp p) hlin
    choose B hB using hblock_B
    refine ⟨B, fun f j ↦ ?_⟩
    rw [hblk X hcomm_z f j]
    exact congrFun (congrArg DFunLike.coe (hB j)) (f.ofLp j)
  · rintro ⟨B, hB⟩ T hT
    obtain ⟨A, hT_blk⟩ := (hpart1 T).mp hT
    ext x
    apply U.symm.injective
    ext j p
    have h1 : (U.symm (X (T x))).ofLp j =
        ((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B j).toEuclideanLin
          ((A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin
            ((U.symm x).ofLp j)) := by
      have htx : T x = U (U.symm (T (U (U.symm x)))) := by simp
      conv_lhs => rw [htx]
      rw [hB, hT_blk]
    have h2 : (U.symm (T (X x))).ofLp j =
        (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)).toEuclideanLin
          (((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B j).toEuclideanLin
            ((U.symm x).ofLp j)) := by
      have hxx : X x = U (U.symm (X (U (U.symm x)))) := by simp
      conv_lhs => rw [hxx]
      rw [hT_blk, hB]
    change (U.symm (X (T x))).ofLp j p = (U.symm (T (X x))).ofLp j p
    rw [h1, h2]
    have hkm : ((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B j) *
        (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)) =
        (A j ⊗ₖ (1 : Matrix (Fin (dB j)) (Fin (dB j)) ℂ)) *
        ((1 : Matrix (Fin (dA j)) (Fin (dA j)) ℂ) ⊗ₖ B j) := by
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
    have hcomp : ∀ M₁ M₂ : Matrix (Fin (dA j) × Fin (dB j)) (Fin (dA j) × Fin (dB j)) ℂ,
        M₁.toEuclideanLin (M₂.toEuclideanLin ((U.symm x).ofLp j)) =
        (M₁ * M₂).toEuclideanLin ((U.symm x).ofLp j) := fun M₁ M₂ ↦
      (congrFun (congrArg DFunLike.coe (Matrix.toLin_mul
        (EuclideanSpace.basisFun _ ℂ).toBasis (EuclideanSpace.basisFun _ ℂ).toBasis
        (EuclideanSpace.basisFun _ ℂ).toBasis M₁ M₂)) ((U.symm x).ofLp j)).symm
    rw [hcomp, hcomp, hkm]

end FinDimCStar

end CslibFrontier.Foundations.Quantum.Algebra
