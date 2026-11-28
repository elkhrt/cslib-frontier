module

public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

import CslibFrontier.Foundations.Data.ENat.IInf
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import CslibFrontier.Foundations.LinearAlgebra.Matrix.FourierMotzkin
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pair Extension Complexity and Approximate Extended Formulations

This module extends the extended-formulation and nonnegative-rank foundations with recession cones,
slack-form extended formulations, pair extension complexity `xc(P, Q)` for nested polyhedra
`P ⊆ Q`, the vertex-and-ray pair slack matrix `S^{P, Q}`, the pair factorization theorem
`rank₊(S^{P, Q}) - 1 ≤ xc(P, Q) ≤ rank₊(S^{P, Q})` together with exact equality criteria, and the
characterization of `ρ`-approximate extended formulations for linear encodings of combinatorial
optimization problems.

## Main definitions

* `CslibFrontier.ExtendedFormulation.recessionCone`: recession cone of a set `Q ⊆ K ^ ι`.
* `CslibFrontier.ExtendedFormulation.IsSlackExtendedFormulation`, `HasSlackExtendedFormulation`:
  extended formulations in slack form `E *ᵥ x + F *ᵥ y = g`, `0 ≤ y`.
* `CslibFrontier.ExtendedFormulation.HasPairExtendedFormulation`, `pairExtensionComplexity`:
  extended formulations and extension complexity `xc(P, Q)` of a nested pair `P ⊆ Q`.
* `CslibFrontier.ExtendedFormulation.pairSlackMatrix`: vertex-and-ray slack matrix `S^{P, Q}`.
* `CslibFrontier.ExtendedFormulation.LinearEncoding`, `IsApproxMaxRelaxation`,
  `IsApproxMinRelaxation`, `maxApproxEFComplexity`, `minApproxEFComplexity`: linear encodings and
  approximate extended-formulation complexity.

## Main results

* `hasSlackExtendedFormulation_iff_hasExtendedFormulation`: equivalence of slack-form and general
  extended formulations over linearly ordered fields.
* `pairExtensionComplexity_bounds`, `pairExtensionComplexity_eq_zero_iff`: unconditional two-sided
  factorization bounds `rank₊(S^{P, Q}) - 1 ≤ xc(P, Q) ≤ rank₊(S^{P, Q})` and the `xc = 0`
  characterization `affineSpan K P ⊆ Q`.
* `pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_nonconst_perp`,
  `pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_bounded`,
  `pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_fullDim`: exact equality
  `xc(P, Q) = rank₊(S^{P, Q})` when `dir(aff(P)) ⊄ span(rec(Q))`.
* `isApproxMaxRelaxation_iff_subset`, `isApproxMinRelaxation_iff_subset`,
  `framework_max_bounds`, `framework_min_bounds`: equivalence between approximate relaxations and
  sandwiched polyhedra, yielding two-sided slack-matrix nonnegative-rank bounds.
-/

public section

namespace CslibFrontier.ExtendedFormulation

open Matrix
open scoped Pointwise

/-! ### Recession cones and polyhedral helpers -/

section RecessionCone

variable {K ι μ : Type*}

/-- The **recession cone** `rec(Q)` of a set `Q ⊆ K ^ ι`: directions `v` such that `p + t • v ∈ Q`
for every `p ∈ Q` and every scalar `t ≥ 0`. -/
def recessionCone (K : Type*) [Semiring K] [PartialOrder K] (Q : Set (ι → K)) : Set (ι → K) :=
  {v | ∀ p ∈ Q, ∀ t : K, 0 ≤ t → p + t • v ∈ Q}

theorem mem_recessionCone_iff [Semiring K] [PartialOrder K] {Q : Set (ι → K)} {v : ι → K} :
    v ∈ recessionCone K Q ↔ ∀ p ∈ Q, ∀ t : K, 0 ≤ t → p + t • v ∈ Q :=
  Iff.rfl

theorem zero_mem_recessionCone [Semiring K] [PartialOrder K] (Q : Set (ι → K)) :
    (0 : ι → K) ∈ recessionCone K Q := fun p hp t _ => by
  simpa only [smul_zero, add_zero] using hp

/-- For a nonempty H-polyhedron `{x | A *ᵥ x ≤ b}` over a linearly ordered field, the recession
cone is `{v | A *ᵥ v ≤ 0}`. -/
theorem recessionCone_setOf_mulVec_le [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype ι] {A : Matrix μ ι K} {b : μ → K} (hne : {x : ι → K | A *ᵥ x ≤ b}.Nonempty) :
    recessionCone K {x : ι → K | A *ᵥ x ≤ b} = {v : ι → K | A *ᵥ v ≤ 0} := by
  ext v
  simp only [mem_recessionCone_iff, Set.mem_ofPred_eq]
  constructor
  · intro hv i
    obtain ⟨p, hp⟩ := hne
    by_contra hpos
    push Not at hpos
    rw [Pi.zero_apply] at hpos
    set t : K := (b i - (A *ᵥ p) i + 1) / (A *ᵥ v) i
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hp i]) hpos.le
    have hpt := hv p hp t ht0 i
    rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hpos.ne'] at hpt
    linarith
  · intro hv p hp t ht i
    rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have htv : t * (A *ᵥ v) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hv i)
    linarith [hp i]

/-- A linear functional `u` vanishing on the recession cone of a nonempty H-polyhedron
`Q = {x | A *ᵥ x ≤ b}` is bounded both above and below on `Q`. -/
theorem exists_bounds_on_setOf_mulVec_le_of_dotProduct_recessionCone_eq_zero
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι] [Finite μ]
    {A : Matrix μ ι K} {b : μ → K} (hne : {x : ι → K | A *ᵥ x ≤ b}.Nonempty) {u : ι → K}
    (hu : ∀ v ∈ recessionCone K {x : ι → K | A *ᵥ x ≤ b}, u ⬝ᵥ v = 0) :
    ∃ β' β : K, ∀ x, A *ᵥ x ≤ b → β' ≤ u ⬝ᵥ x ∧ u ⬝ᵥ x ≤ β := by
  have := Fintype.ofFinite μ
  have hrec := recessionCone_setOf_mulVec_le hne
  have h0 : ∃ v : ι → K, A *ᵥ v ≤ 0 := ⟨0, by simp⟩
  have hpos : ∀ v : ι → K, A *ᵥ v ≤ 0 → u ⬝ᵥ v ≤ 0 := fun v hv =>
    (hu v (hrec.symm ▸ hv)).le
  have hneg : ∀ v : ι → K, A *ᵥ v ≤ 0 → (-u) ⬝ᵥ v ≤ 0 := fun v hv => by
    rw [neg_dotProduct, hu v (hrec.symm ▸ hv), neg_zero]
  obtain ⟨y₁, hy₁, hy₁A, -⟩ := Matrix.exists_dual_le_of_forall_le A 0 u 0 h0 hpos
  obtain ⟨y₂, hy₂, hy₂A, -⟩ := Matrix.exists_dual_le_of_forall_le A 0 (-u) 0 h0 hneg
  refine ⟨-(y₂ ⬝ᵥ b), y₁ ⬝ᵥ b, fun x hx => ⟨?_, ?_⟩⟩
  · have h := Matrix.dotProduct_le_dotProduct_of_mulVec_le hx hy₂ hy₂A
    rw [neg_dotProduct] at h
    linarith
  · exact Matrix.dotProduct_le_dotProduct_of_mulVec_le hx hy₁ hy₁A

end RecessionCone

/-! ### Slack-form extended formulations and equivalence with `HasExtendedFormulation` -/

section SlackForm

variable {K ι σ τ : Type*}

/-- A system `E *ᵥ x + F *ᵥ y = g`, `0 ≤ y` is a **slack-form extended formulation** of `P`
. Its size is the number of nonnegative variables
`y: σ → K`. -/
def IsSlackExtendedFormulation [Semiring K] [PartialOrder K] [Fintype ι] [Fintype σ]
    (P : Set (ι → K)) (E : Matrix τ ι K) (F : Matrix τ σ K) (g : τ → K) : Prop :=
  ∀ x, x ∈ P ↔ ∃ y : σ → K, 0 ≤ y ∧ E *ᵥ x + F *ᵥ y = g

/-- Characterization of `IsSlackExtendedFormulation` without unfolding across modules. -/
theorem isSlackExtendedFormulation_iff [Semiring K] [PartialOrder K] [Fintype ι] [Fintype σ]
    {P : Set (ι → K)} {E : Matrix τ ι K} {F : Matrix τ σ K} {g : τ → K} :
    IsSlackExtendedFormulation P E F g ↔
      ∀ x, x ∈ P ↔ ∃ y : σ → K, 0 ≤ y ∧ E *ᵥ x + F *ᵥ y = g :=
  Iff.rfl

/-- `P` has a slack-form extended formulation of size `r` (`r` nonnegative auxiliary variables and
finitely many linear equations). -/
def HasSlackExtendedFormulation [Semiring K] [PartialOrder K] [Fintype ι]
    (P : Set (ι → K)) (r : ℕ) : Prop :=
  ∃ (e : ℕ) (E : Matrix (Fin e) ι K) (F : Matrix (Fin e) (Fin r) K) (g : Fin e → K),
    IsSlackExtendedFormulation P E F g

/-- Characterization of `HasSlackExtendedFormulation` without unfolding across modules. -/
theorem hasSlackExtendedFormulation_iff [Semiring K] [PartialOrder K] [Fintype ι]
    {P : Set (ι → K)} {r : ℕ} :
    HasSlackExtendedFormulation P r ↔
      ∃ (e : ℕ) (E : Matrix (Fin e) ι K) (F : Matrix (Fin e) (Fin r) K) (g : Fin e → K),
        IsSlackExtendedFormulation P E F g :=
  Iff.rfl

/-- Every slack-form extended formulation is an extended formulation in the sense of
`CslibFrontier`'s `IsExtendedFormulation`, with the same size `|σ|`. -/
theorem IsSlackExtendedFormulation.toIsExtendedFormulation [Ring K] [PartialOrder K]
    [IsOrderedAddMonoid K] [Fintype ι] [Fintype σ] [DecidableEq σ] {P : Set (ι → K)}
    {E : Matrix τ ι K} {F : Matrix τ σ K} {g : τ → K}
    (h : IsSlackExtendedFormulation P E F g) :
    IsExtendedFormulation P (0 : Matrix σ ι K) (-1 : Matrix σ σ K) 0 E F g := fun x => by
  simp only [h x, zero_mulVec, zero_add, neg_mulVec, one_mulVec, Left.neg_nonpos_iff]

/-- Over a linearly ordered field, slack-form extended formulations of size `r` (`E x + F y = g`,
`y ≥ 0`, `y ∈ K^r`) are equivalent to general inequality/equality extended formulations of size `r`
(`HasExtendedFormulation P r`). -/
theorem hasSlackExtendedFormulation_iff_hasExtendedFormulation
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    {P : Set (ι → K)} {r : ℕ} :
    HasSlackExtendedFormulation P r ↔ HasExtendedFormulation P r := by
  classical
  constructor
  · rintro ⟨e, E, F, g, h⟩
    exact ⟨r, e, 0, -1, 0, E, F, g, h.toIsExtendedFormulation⟩
  · rintro ⟨d, e, E, F, g, E', F', g', hEF⟩
    let B : Matrix (Fin r ⊕ Fin e) (Fin d) K := fromRows F F'
    let R : Submodule K (Fin r ⊕ Fin e → K) := LinearMap.range B.mulVecLin
    let Q := (Fin r ⊕ Fin e → K) ⧸ R
    let bQ := Module.finBasis K Q
    let m : ℕ := Module.finrank K Q
    let Wlin : (Fin r ⊕ Fin e → K) →ₗ[K] (Fin m → K) := bQ.equivFun.toLinearMap.comp R.mkQ
    have hWker : ∀ v : Fin r ⊕ Fin e → K, Wlin v = 0 ↔ ∃ y : Fin d → K, B *ᵥ y = v := by
      intro v
      change bQ.equivFun (R.mkQ v) = 0 ↔ v ∈ LinearMap.range B.mulVecLin
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    let Wmat : Matrix (Fin m) (Fin r ⊕ Fin e) K := LinearMap.toMatrix' Wlin
    let W₁ : Matrix (Fin m) (Fin r) K := Wmat.submatrix id Sum.inl
    let W₂ : Matrix (Fin m) (Fin e) K := Wmat.submatrix id Sum.inr
    have hWsplit : ∀ (v₁ : Fin r → K) (v₂ : Fin e → K),
        Wlin (Sum.elim v₁ v₂) = W₁ *ᵥ v₁ + W₂ *ᵥ v₂ := by
      intro v₁ v₂
      rw [← LinearMap.toMatrix'_mulVec Wlin]
      ext i
      simp only [Wmat, W₁, W₂, mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, submatrix_apply, id_eq, Pi.add_apply]
    refine ⟨m, W₁ * E + W₂ * E', W₁, W₁ *ᵥ g + W₂ *ᵥ g', fun x => ?_⟩
    rw [hEF x]
    constructor
    · rintro ⟨y, hy, hy'⟩
      refine ⟨g - (E *ᵥ x + F *ᵥ y), sub_nonneg.2 hy, ?_⟩
      have hBy : B *ᵥ y = Sum.elim (g - E *ᵥ x - (g - (E *ᵥ x + F *ᵥ y))) (g' - E' *ᵥ x) := by
        ext (i | j)
        · simp only [B, fromRows_mulVec, Sum.elim_inl, Pi.sub_apply, Pi.add_apply]; ring
        · simp only [B, fromRows_mulVec, Sum.elim_inr, Pi.sub_apply]
          have := congrFun hy' j
          simp only [Pi.add_apply] at this
          linarith
      have hW0 := (hWker _).2 ⟨y, hBy⟩
      rw [hWsplit] at hW0
      rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
      ext k
      have hk := congrFun hW0 k
      simp only [mulVec_sub, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hk ⊢
      linarith
    · rintro ⟨s, hs, hxs⟩
      have hW0 : Wlin (Sum.elim (g - E *ᵥ x - s) (g' - E' *ᵥ x)) = 0 := by
        rw [hWsplit]
        rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at hxs
        ext k
        have hk := congrFun hxs k
        simp only [mulVec_sub, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hk ⊢
        linarith
      obtain ⟨y, hy⟩ := (hWker _).1 hW0
      refine ⟨y, fun i => ?_, funext fun j => ?_⟩
      · have hi := congrFun hy (.inl i)
        simp only [B, fromRows_mulVec, Sum.elim_inl, Pi.sub_apply] at hi
        have hsi : 0 ≤ s i := hs i
        simp only [Pi.add_apply]
        linarith
      · have hj := congrFun hy (.inr j)
        simp only [B, fromRows_mulVec, Sum.elim_inr, Pi.sub_apply] at hj
        simp only [Pi.add_apply]
        linarith

end SlackForm

/-! ### Pair extension complexity and pair slack matrices -/

section PairEF

variable {K ι μ ν ρ σ κ τ : Type*}

/-- The pair `P, Q` has an **extended formulation of size `r`** if there exists a set `K_set`
sandwiched between `P` and `Q` (`P ⊆ K_set ⊆ Q`) with an extended formulation of size `r`
. -/
def HasPairExtendedFormulation [Semiring K] [PartialOrder K] [Fintype ι]
    (P Q : Set (ι → K)) (r : ℕ) : Prop :=
  ∃ K_set : Set (ι → K), P ⊆ K_set ∧ K_set ⊆ Q ∧ HasExtendedFormulation K_set r

/-- Characterization of `HasPairExtendedFormulation` without unfolding across modules. -/
theorem hasPairExtendedFormulation_iff [Semiring K] [PartialOrder K] [Fintype ι]
    {P Q : Set (ι → K)} {r : ℕ} :
    HasPairExtendedFormulation P Q r ↔
      ∃ K_set : Set (ι → K), P ⊆ K_set ∧ K_set ⊆ Q ∧ HasExtendedFormulation K_set r :=
  Iff.rfl

/-- The **extension complexity `xc(P, Q)` of a pair of nested sets** `P, Q`: the minimum size of
an extended formulation of a polyhedron `K_set` with `P ⊆ K_set ⊆ Q`, or `⊤` if none exists. -/
noncomputable def pairExtensionComplexity [Semiring K] [PartialOrder K] [Fintype ι]
    (P Q : Set (ι → K)) : ℕ∞ :=
  ⨅ r : {r : ℕ // HasPairExtendedFormulation P Q r}, (r.1 : ℕ∞)

/-- `pairExtensionComplexity P Q ≤ r` iff there exists a pair EF of size `s ≤ r`. -/
theorem pairExtensionComplexity_le_natCast_iff [Semiring K] [PartialOrder K] [Fintype ι]
    {P Q : Set (ι → K)} {r : ℕ} :
    pairExtensionComplexity P Q ≤ (r : ℕ∞) ↔
      ∃ s : ℕ, s ≤ r ∧ HasPairExtendedFormulation P Q s := by
  rw [pairExtensionComplexity, ENat.iInf_natCast_le_natCast_iff]
  exact ⟨fun ⟨⟨s, hs⟩, hsr⟩ => ⟨s, hsr, hs⟩, fun ⟨s, hsr, hs⟩ => ⟨⟨s, hs⟩, hsr⟩⟩

/-- The **slack matrix `S^{P, Q}`** of an inner description `conv(V) + cone(R)` and an outer
description `A *ᵥ x ≤ b`: its vertex block has entries `b i - A i ⬝ᵥ V j` and its ray block has
entries `-(A i ⬝ᵥ R l)`. -/
def pairSlackMatrix [Ring K] [Fintype ι] (A : Matrix μ ι K) (b : μ → K)
    (V : ν → ι → K) (R : ρ → ι → K) : Matrix μ (ν ⊕ ρ) K :=
  Matrix.of fun i => Sum.elim (fun j => b i - A i ⬝ᵥ V j) (fun l => -(A i ⬝ᵥ R l))

@[simp]
theorem pairSlackMatrix_inl [Ring K] [Fintype ι] (A : Matrix μ ι K) (b : μ → K)
    (V : ν → ι → K) (R : ρ → ι → K) (i : μ) (j : ν) :
    pairSlackMatrix A b V R i (.inl j) = b i - A i ⬝ᵥ V j := by
  rw [pairSlackMatrix]; rfl

@[simp]
theorem pairSlackMatrix_inr [Ring K] [Fintype ι] (A : Matrix μ ι K) (b : μ → K)
    (V : ν → ι → K) (R : ρ → ι → K) (i : μ) (l : ρ) :
    pairSlackMatrix A b V R i (.inr l) = -(A i ⬝ᵥ R l) := by
  rw [pairSlackMatrix]; rfl

/-- Lower bounds on `pairExtensionComplexity P Q` are lower bounds on the size of every pair EF. -/
theorem le_pairExtensionComplexity_iff [Semiring K] [PartialOrder K] [Fintype ι]
    {P Q : Set (ι → K)} {c : ℕ∞} :
    c ≤ pairExtensionComplexity P Q ↔ ∀ r, HasPairExtendedFormulation P Q r → c ≤ r := by
  simp only [pairExtensionComplexity, le_iInf_iff, Subtype.forall]

/-- A pair extended formulation of size `r` upper-bounds `pairExtensionComplexity P Q` by `r`. -/
theorem HasPairExtendedFormulation.pairExtensionComplexity_le [Semiring K] [PartialOrder K]
    [Fintype ι] {P Q : Set (ι → K)} {r : ℕ} (h : HasPairExtendedFormulation P Q r) :
    pairExtensionComplexity P Q ≤ r :=
  iInf_le (fun s : {s : ℕ // HasPairExtendedFormulation P Q s} => (s.1 : ℕ∞)) ⟨r, h⟩

/-- Monotonicity of `pairExtensionComplexity`: shrinking `P` or enlarging `Q` cannot increase
`xc(P, Q)`. -/
theorem pairExtensionComplexity_mono [Semiring K] [PartialOrder K] [Fintype ι]
    {P₁ P₂ Q₁ Q₂ : Set (ι → K)} (hP : P₁ ⊆ P₂) (hQ : Q₂ ⊆ Q₁) :
    pairExtensionComplexity P₁ Q₁ ≤ pairExtensionComplexity P₂ Q₂ :=
  le_pairExtensionComplexity_iff.2 fun _ ⟨K_set, hPK, hKQ, hEF⟩ =>
    HasPairExtendedFormulation.pairExtensionComplexity_le
      ⟨K_set, hP.trans hPK, hKQ.trans hQ, hEF⟩

/-- `pairExtensionComplexity P Q` is bounded above by `extensionComplexity K_set` for any
sandwiched set `P ⊆ K_set ⊆ Q`. -/
theorem pairExtensionComplexity_le_extensionComplexity [Semiring K] [PartialOrder K] [Fintype ι]
    {P K_set Q : Set (ι → K)} (hPK : P ⊆ K_set) (hKQ : K_set ⊆ Q) :
    pairExtensionComplexity P Q ≤ extensionComplexity K_set :=
  le_extensionComplexity_iff.2 fun _ hEF =>
    HasPairExtendedFormulation.pairExtensionComplexity_le ⟨K_set, hPK, hKQ, hEF⟩

/-- For a single set `P`, `pairExtensionComplexity P P = extensionComplexity P`. -/
theorem pairExtensionComplexity_self [Semiring K] [PartialOrder K] [Fintype ι]
    (P : Set (ι → K)) : pairExtensionComplexity P P = extensionComplexity P :=
  le_antisymm (pairExtensionComplexity_le_extensionComplexity Set.Subset.rfl Set.Subset.rfl)
    (le_pairExtensionComplexity_iff.2 fun _ ⟨K_set, hPK, hKP, hEF⟩ => by
      have hEq : K_set = P := Set.Subset.antisymm hKP hPK
      rw [← hEq]
      obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hEF
      simpa only [Fintype.card_fin] using h.extensionComplexity_le)

end PairEF

/-! ### Factorization theorem for pairs of nested polyhedra -/

section SandwichTheorem

variable {K ι μ ν ρ σ κ τ : Type*}
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Fintype ι]

/-- **Pair factorization theorem (upper bound)**: `xc(P, Q) ≤ rank₊(S^{P, Q})`. -/
theorem pairExtensionComplexity_le_nonnegRank_pairSlackMatrix [Finite μ]
    {P Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} {R : ρ → ι → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b}) :
    pairExtensionComplexity P Q ≤ (pairSlackMatrix A b V R).nonnegRank := by
  classical
  refine Matrix.le_nonnegRank_iff.2 fun r ⟨T, U, hT, hU, hTU⟩ => ?_
  let K_set : Set (ι → K) := {x | ∃ y : Fin r → K, 0 ≤ y ∧ A *ᵥ x + T *ᵥ y = b}
  have hKEF : IsExtendedFormulation K_set (0 : Matrix (Fin r) ι K) (-1 : Matrix (Fin r) (Fin r) K)
      0 A T b := fun x => by
    simp only [K_set, Set.mem_ofPred_eq, zero_mulVec, zero_add, neg_mulVec, one_mulVec,
      Left.neg_nonpos_iff]
  have hKQ : K_set ⊆ Q := by
    rintro x ⟨y, hy, hxy⟩
    rw [hQ, Set.mem_ofPred_eq, ← hxy]
    exact le_add_of_nonneg_right fun i => dotProduct_nonneg_of_nonneg (fun k => hT i k) hy
  have hV_mem : convexHull K (Set.range V) ⊆ K_set := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨j, rfl⟩
      refine ⟨fun k => U k (.inl j), fun k => hU k (.inl j), funext fun i => ?_⟩
      have hij := congrFun (congrFun hTU i) (.inl j)
      simp only [Matrix.mul_apply, pairSlackMatrix_inl, Pi.add_apply, mulVec, dotProduct] at hij ⊢
      linarith
    · rintro x₁ ⟨y₁, hy₁, hxy₁⟩ x₂ ⟨y₂, hy₂, hxy₂⟩ a c ha hc hac
      refine ⟨a • y₁ + c • y₂, add_nonneg (smul_nonneg ha hy₁) (smul_nonneg hc hy₂), ?_⟩
      rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
        add_add_add_comm, ← smul_add, ← smul_add, hxy₁, hxy₂, ← add_smul, hac, one_smul]
  let C_ray : PointedCone K (ι → K) :=
    PointedCone.ofConeComb {v | ∃ z : Fin r → K, 0 ≤ z ∧ A *ᵥ v + T *ᵥ z = 0}
      ⟨0, 0, le_rfl, by simp⟩
      (by
        rintro v₁ ⟨z₁, hz₁, hv₁⟩ v₂ ⟨z₂, hz₂, hv₂⟩ a ha c hc
        refine ⟨a • z₁ + c • z₂, add_nonneg (smul_nonneg ha hz₁) (smul_nonneg hc hz₂), ?_⟩
        rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
          add_add_add_comm, ← smul_add, ← smul_add, hv₁, hv₂, smul_zero, smul_zero, add_zero])
  have hR_le : PointedCone.hull K (Set.range R) ≤ C_ray := by
    rw [PointedCone.hull, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    refine ⟨fun k => U k (.inr l), fun k => hU k (.inr l), funext fun i => ?_⟩
    have hil := congrFun (congrFun hTU i) (.inr l)
    simp only [Matrix.mul_apply, pairSlackMatrix_inr, Pi.add_apply, Pi.zero_apply, mulVec,
      dotProduct] at hil ⊢
    linarith
  have hPK : P ⊆ K_set := by
    rw [hP]
    rintro _ ⟨x, hx, v, hv, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hV_mem hx
    obtain ⟨z, hz, hvz⟩ := hR_le hv
    exact ⟨y + z, add_nonneg hy hz, by rw [mulVec_add, mulVec_add, add_add_add_comm, hxy, hvz,
      add_zero]⟩
  have hhas : HasPairExtendedFormulation P Q r :=
    ⟨K_set, hPK, hKQ, by simpa only [Fintype.card_fin] using hKEF.hasExtendedFormulation⟩
  exact hhas.pairExtensionComplexity_le

/-- If `K_set` has an extended formulation `E x + F y ≤ g, E' x + F' y = g'` and
`v₀ + t • r ∈ K_set` for all `t ≥ 0`, then `r` lifts to a recession ray `(r, z)` of the
extended system. -/
theorem exists_ray_lift_of_isExtendedFormulation [Finite σ] [Fintype κ] [Finite τ]
    {K_set : Set (ι → K)} {E : Matrix σ ι K} {F : Matrix σ κ K} {g : σ → K}
    {E' : Matrix τ ι K} {F' : Matrix τ κ K} {g' : τ → K}
    (hEF : IsExtendedFormulation K_set E F g E' F' g')
    {v₀ r : ι → K} (hray : ∀ t : K, 0 ≤ t → v₀ + t • r ∈ K_set) :
    ∃ z : κ → K, E *ᵥ r + F *ᵥ z ≤ 0 ∧ E' *ᵥ r + F' *ᵥ z = 0 := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite τ
  let M : Matrix (σ ⊕ (τ ⊕ τ)) κ K := fromRows F (fromRows F' (-F'))
  let rhs : σ ⊕ (τ ⊕ τ) → K := Sum.elim (-(E *ᵥ r)) (Sum.elim (-(E' *ᵥ r)) (E' *ᵥ r))
  have hiff (z : κ → K) : M *ᵥ z ≤ rhs ↔ E *ᵥ r + F *ᵥ z ≤ 0 ∧ E' *ᵥ r + F' *ᵥ z = 0 := by
    constructor
    · intro h
      refine ⟨fun i => ?_, funext fun j => ?_⟩
      · have hi := h (.inl i)
        simp only [M, rhs, fromRows_mulVec, Sum.elim_inl, Pi.neg_apply] at hi
        simp only [Pi.add_apply, Pi.zero_apply]; linarith
      · have h1 := h (.inr (.inl j))
        have h2 := h (.inr (.inr j))
        simp only [M, rhs, fromRows_mulVec, neg_mulVec, Sum.elim_inr, Sum.elim_inl,
          Pi.neg_apply] at h1 h2
        simp only [Pi.add_apply, Pi.zero_apply]; linarith
    · rintro ⟨h1, h2⟩ (i | j | j)
      · simp only [M, rhs, fromRows_mulVec, Sum.elim_inl, Pi.neg_apply]
        have hi := h1 i; simp only [Pi.add_apply, Pi.zero_apply] at hi; linarith
      · simp only [M, rhs, fromRows_mulVec, Sum.elim_inr, Sum.elim_inl, Pi.neg_apply]
        have hj := congrFun h2 j; simp only [Pi.add_apply, Pi.zero_apply] at hj; linarith
      · simp only [M, rhs, fromRows_mulVec, neg_mulVec, Sum.elim_inr, Pi.neg_apply]
        have hj := congrFun h2 j; simp only [Pi.add_apply, Pi.zero_apply] at hj; linarith
  by_contra hno
  have hno' : ¬∃ z, M *ᵥ z ≤ rhs := fun ⟨z, hz⟩ => hno ⟨z, (hiff z).1 hz⟩
  obtain ⟨u, hu0, huM, hurhs⟩ := (Matrix.not_exists_mulVec_le_iff M rhs).1 hno'
  let u₁ : σ → K := u ∘ Sum.inl
  let u₂ : τ → K := (u ∘ Sum.inr) ∘ Sum.inl
  let u₃ : τ → K := (u ∘ Sum.inr) ∘ Sum.inr
  have hu₁ : 0 ≤ u₁ := fun i => hu0 (.inl i)
  have huF : u₁ ᵥ* F + (u₂ - u₃) ᵥ* F' = 0 := by
    dsimp only [M] at huM
    rw [vecMul_fromRows, vecMul_fromRows, vecMul_neg, ← sub_eq_add_neg, ← sub_vecMul] at huM
    exact huM
  have hpos : 0 < u₁ ⬝ᵥ (E *ᵥ r) + (u₂ - u₃) ⬝ᵥ (E' *ᵥ r) := by
    rw [← Sum.elim_comp_inl_inr u, ← Sum.elim_comp_inl_inr (u ∘ Sum.inr)] at hurhs
    simp only [rhs, sumElim_dotProduct_sumElim, dotProduct_neg] at hurhs
    have hurhs' : -(u₁ ⬝ᵥ (E *ᵥ r)) + (-(u₂ ⬝ᵥ (E' *ᵥ r)) + u₃ ⬝ᵥ (E' *ᵥ r)) < 0 := hurhs
    rw [sub_dotProduct]
    linarith
  set c : K := u₁ ⬝ᵥ (E *ᵥ r) + (u₂ - u₃) ⬝ᵥ (E' *ᵥ r)
  set C : K := u₁ ⬝ᵥ g + (u₂ - u₃) ⬝ᵥ g'
  set base : K := u₁ ⬝ᵥ (E *ᵥ v₀) + (u₂ - u₃) ⬝ᵥ (E' *ᵥ v₀)
  set t : K := max 0 ((C - base + 1) / c)
  have ht0 : 0 ≤ t := le_max_left _ _
  obtain ⟨yt, hyt1, hyt2⟩ := (hEF (v₀ + t • r)).1 (hray t ht0)
  have hub : u₁ ⬝ᵥ (E *ᵥ (v₀ + t • r) + F *ᵥ yt) +
      (u₂ - u₃) ⬝ᵥ (E' *ᵥ (v₀ + t • r) + F' *ᵥ yt) ≤ C := by
    have h1 := dotProduct_le_dotProduct_of_nonneg_left hyt1 hu₁
    rw [hyt2]
    linarith
  have hval : u₁ ⬝ᵥ (E *ᵥ (v₀ + t • r) + F *ᵥ yt) +
      (u₂ - u₃) ⬝ᵥ (E' *ᵥ (v₀ + t • r) + F' *ᵥ yt) = base + t * c := by
    simp only [dotProduct_add, mulVec_add, mulVec_smul, dotProduct_smul, smul_eq_mul,
      dotProduct_mulVec]
    have hcancel : (u₁ ᵥ* F) ⬝ᵥ yt + ((u₂ - u₃) ᵥ* F') ⬝ᵥ yt = 0 := by
      rw [← add_dotProduct, huF, zero_dotProduct]
    simp only [base, c, dotProduct_mulVec]
    linarith
  have htc : C - base + 1 ≤ t * c := by
    have h1 : (C - base + 1) / c ≤ t := le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

/-- Helper: given an extended formulation of `K_set` with `P ⊆ K_set ⊆ Q`, we obtain a nonnegative
factorization of `pairSlackMatrix A b V R` of size `|σ| + 1`. -/
private theorem hasNonnegFactorization_pairSlackMatrix_option [Fintype σ] [Fintype κ] [Finite τ]
    [Nonempty ν] {P K_set Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K}
    {V : ν → ι → K} {R : ρ → ι → K}
    {E : Matrix σ ι K} {F : Matrix σ κ K} {g : σ → K}
    {E' : Matrix τ ι K} {F' : Matrix τ κ K} {g' : τ → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b}) (hPK : P ⊆ K_set) (hKQ : K_set ⊆ Q)
    (hEF : IsExtendedFormulation K_set E F g E' F' g') :
    (pairSlackMatrix A b V R).HasNonnegFactorization (Option σ) := by
  have hVP : ∀ j, V j ∈ K_set := fun j => hPK <| hP ▸ ⟨V j, subset_convexHull K _ ⟨j, rfl⟩,
    0, (PointedCone.hull K (Set.range R)).zero_mem, add_zero _⟩
  choose w hw using fun j => (hEF (V j)).1 (hVP j)
  obtain ⟨j₀⟩ := ‹Nonempty ν›
  have hRray : ∀ l : ρ, ∀ t : K, 0 ≤ t → V j₀ + t • R l ∈ K_set := fun l t ht =>
    hPK <| hP ▸ ⟨V j₀, subset_convexHull K _ ⟨j₀, rfl⟩, t • R l,
      (PointedCone.hull K (Set.range R)).smul_mem ht
        (PointedCone.subset_hull ⟨l, rfl⟩), rfl⟩
  choose z hz using fun l => exists_ray_lift_of_isExtendedFormulation hEF (hRray l)
  have hrow : ∀ i : μ, ∃ l : σ → K, 0 ≤ l ∧ ∃ δ' ≤ b i, ∀ x y, E' *ᵥ x + F' *ᵥ y = g' →
      l ⬝ᵥ (g - (E *ᵥ x + F *ᵥ y)) = δ' - A i ⬝ᵥ x := fun i =>
    hEF.exists_nonneg_dotProduct_eq ⟨V j₀, hVP j₀⟩ (A i) (b i) fun x hx => (hQ ▸ hKQ hx) i
  choose l hl δ' hδ' hlrow using hrow
  refine ⟨Matrix.of fun i o => o.elim (b i - δ' i) (l i),
    Matrix.of fun o c => o.elim (c.elim (fun _ => 1) (fun _ => 0))
      (fun k => c.elim (fun j => (g - (E *ᵥ V j + F *ᵥ w j)) k)
        (fun r => -(E *ᵥ R r + F *ᵥ z r) k)),
    ?_, ?_, Matrix.ext fun i c => ?_⟩
  · intro i o; cases o with
    | none => exact sub_nonneg.2 (hδ' i)
    | some k => exact hl i k
  · intro o c; cases o with
    | none => cases c <;> simp
    | some k => cases c with
      | inl j => exact sub_nonneg.2 (hw j).1 k
      | inr r => exact neg_nonneg.2 (hz r).1 k
  · cases c with
    | inl j =>
      simp only [Matrix.mul_apply, Fintype.sum_option, of_apply, Option.elim_none, Option.elim_some,
        Sum.elim_inl, mul_one, pairSlackMatrix_inl]
      have heq := hlrow i (V j) (w j) (hw j).2
      change b i - δ' i + l i ⬝ᵥ (g - (E *ᵥ V j + F *ᵥ w j)) = b i - A i ⬝ᵥ V j
      linarith
    | inr r =>
      simp only [Matrix.mul_apply, Fintype.sum_option, of_apply, Option.elim_none, Option.elim_some,
        Sum.elim_inr, mul_zero, zero_add, pairSlackMatrix_inr]
      have hsum : E' *ᵥ (V j₀ + R r) + F' *ᵥ (w j₀ + z r) = g' := by
        rw [mulVec_add, mulVec_add, add_add_add_comm, (hw j₀).2, (hz r).2, add_zero]
      have h1 := hlrow i (V j₀) (w j₀) (hw j₀).2
      have h2 := hlrow i (V j₀ + R r) (w j₀ + z r) hsum
      have hsub : (g - (E *ᵥ (V j₀ + R r) + F *ᵥ (w j₀ + z r))) -
          (g - (E *ᵥ V j₀ + F *ᵥ w j₀)) = -(E *ᵥ R r + F *ᵥ z r) := by
        ext k; simp only [mulVec_add, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring
      change l i ⬝ᵥ (-(E *ᵥ R r + F *ᵥ z r)) = -(A i ⬝ᵥ R r)
      rw [← hsub, dotProduct_sub, h2, h1, dotProduct_add]
      ring

/-- **Pair factorization theorem (lower bound)**: `rank₊(S^{P, Q}) ≤ xc(P, Q) + 1` (equivalently
`rank₊(S^{P, Q}) - 1 ≤ xc(P, Q)`), for every nonempty polyhedron `P ⊆ Q`. -/
theorem nonnegRank_pairSlackMatrix_le_pairExtensionComplexity_add_one [Nonempty ν]
    {P Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} {R : ρ → ι → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b}) :
    (pairSlackMatrix A b V R).nonnegRank ≤ pairExtensionComplexity P Q + 1 := by
  have hle : ∀ r : ℕ, HasPairExtendedFormulation P Q r →
      (pairSlackMatrix A b V R).nonnegRank ≤ (r : ℕ∞) + 1 := by
    rintro r ⟨K_set, hPK, hKQ, _, _, _, _, _, _, _, _, hEF⟩
    have hfac := hasNonnegFactorization_pairSlackMatrix_option hP hQ hPK hKQ hEF
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      hfac.nonnegRank_le
  cases hxc : pairExtensionComplexity P Q using ENat.recTopCoe with
  | top => simp
  | coe r =>
    obtain ⟨⟨s, hs⟩, hsr⟩ := ENat.iInf_natCast_le_natCast_iff.mp hxc.le
    exact (hle s hs).trans (by exact_mod_cast Nat.add_le_add_right hsr 1)

/-- **Pair factorization theorem (two-sided bound)** for every nonempty polyhedron `P ⊆ Q`:
`rank₊(S^{P, Q}) - 1 ≤ xc(P, Q) ≤ rank₊(S^{P, Q})`. -/
theorem pairExtensionComplexity_bounds [Finite μ] [Nonempty ν]
    {P Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} {R : ρ → ι → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b}) :
    (pairSlackMatrix A b V R).nonnegRank - 1 ≤ pairExtensionComplexity P Q ∧
      pairExtensionComplexity P Q ≤ (pairSlackMatrix A b V R).nonnegRank :=
  ⟨tsub_le_iff_right.2 (nonnegRank_pairSlackMatrix_le_pairExtensionComplexity_add_one hP hQ),
    pairExtensionComplexity_le_nonnegRank_pairSlackMatrix hP hQ⟩

/-- Degenerate case of pair extension complexity: `xc(P, Q) = 0` iff `affineSpan K P ⊆ Q`. -/
theorem pairExtensionComplexity_eq_zero_iff {P Q : Set (ι → K)} (hPQ : P ⊆ Q) :
    pairExtensionComplexity P Q = 0 ↔ (affineSpan K P : Set (ι → K)) ⊆ Q := by
  classical
  constructor
  · intro h0
    have hhas : HasPairExtendedFormulation P Q 0 := by
      obtain ⟨⟨s, hs⟩, hs0⟩ := ENat.iInf_natCast_le_natCast_iff.mp h0.le
      have : s = 0 := Nat.le_zero.1 hs0
      exact this ▸ hs
    obtain ⟨K_set, hPK, hKQ, d, e, E, F, g, E', F', g', hEF⟩ := hhas
    have hKaff : ∀ x₁ ∈ K_set, ∀ x₂ ∈ K_set, ∀ x₃ ∈ K_set, ∀ t : K,
        t • (x₁ - x₂) + x₃ ∈ K_set := by
      intro x₁ hx₁ x₂ hx₂ x₃ hx₃ t
      obtain ⟨y₁, -, hy₁⟩ := (hEF x₁).1 hx₁
      obtain ⟨y₂, -, hy₂⟩ := (hEF x₂).1 hx₂
      obtain ⟨y₃, -, hy₃⟩ := (hEF x₃).1 hx₃
      refine (hEF _).2 ⟨t • (y₁ - y₂) + y₃, fun i => i.elim0, ?_⟩
      simp only [mulVec_add, mulVec_smul, mulVec_sub]
      calc t • (E' *ᵥ x₁ - E' *ᵥ x₂) + E' *ᵥ x₃ + (t • (F' *ᵥ y₁ - F' *ᵥ y₂) + F' *ᵥ y₃)
          = t • ((E' *ᵥ x₁ + F' *ᵥ y₁) - (E' *ᵥ x₂ + F' *ᵥ y₂)) + (E' *ᵥ x₃ + F' *ᵥ y₃) := by
            ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        _ = g' := by rw [hy₁, hy₂, hy₃, sub_self, smul_zero, zero_add]
    rcases P.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
    · simp
    · let S : AffineSubspace K (ι → K) :=
        { carrier := K_set
          smul_vsub_vadd_mem' := fun t x₁ x₂ x₃ h₁ h₂ h₃ => hKaff x₁ h₁ x₂ h₂ x₃ h₃ t }
      exact (SetLike.coe_subset_coe.2 ((affineSpan_le (s := P) (Q := S)).2 hPK)).trans hKQ
  · intro haff
    rcases P.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
    · have hEF : IsExtendedFormulation (∅ : Set (ι → K)) (0 : Matrix (Fin 0) ι K)
          (0 : Matrix (Fin 0) (Fin 0) K) 0 (0 : Matrix (Fin 1) ι K)
          (0 : Matrix (Fin 1) (Fin 0) K) (fun _ => 1) := fun x => by
        simp only [Set.mem_empty_iff_false, zero_mulVec, add_zero, false_iff, not_exists, not_and]
        intro _ _ h
        exact zero_ne_one (congrFun h 0)
      have hhas : HasPairExtendedFormulation (∅ : Set (ι → K)) Q 0 :=
        ⟨∅, Set.Subset.rfl, Set.empty_subset Q, by simpa using hEF.hasExtendedFormulation⟩
      exact le_antisymm (by simpa using hhas.pairExtensionComplexity_le) bot_le
    · let dir : Submodule K (ι → K) := vectorSpan K P
      let Qmod := (ι → K) ⧸ dir
      let bQ := Module.finBasis K Qmod
      let e : ℕ := Module.finrank K Qmod
      let Wlin : (ι → K) →ₗ[K] (Fin e → K) := bQ.equivFun.toLinearMap.comp dir.mkQ
      let E' : Matrix (Fin e) ι K := LinearMap.toMatrix' Wlin
      have hEF : IsExtendedFormulation (affineSpan K P : Set (ι → K))
          (0 : Matrix (Fin 0) ι K) (0 : Matrix (Fin 0) (Fin 0) K) 0
          E' (0 : Matrix (Fin e) (Fin 0) K) (E' *ᵥ p₀) := fun x => by
        simp only [zero_mulVec, add_zero, exists_const, SetLike.mem_coe]
        have hmem : x ∈ affineSpan K P ↔ x - p₀ ∈ dir := by
          rw [← vsub_eq_sub, ← AffineSubspace.vsub_right_mem_direction_iff_mem
            (subset_affineSpan K P hp₀), direction_affineSpan]
        rw [hmem]
        constructor
        · intro hx
          refine ⟨fun i => i.elim0, ?_⟩
          rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, ← sub_eq_zero, ← map_sub]
          change bQ.equivFun (dir.mkQ (x - p₀)) = 0
          rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero dir).2 hx, map_zero]
        · rintro ⟨-, hEx⟩
          rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, ← sub_eq_zero, ← map_sub]
            at hEx
          change bQ.equivFun (dir.mkQ (x - p₀)) = 0 at hEx
          rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero] at hEx
          exact hEx
      have hle := HasPairExtendedFormulation.pairExtensionComplexity_le
        ⟨(affineSpan K P : Set (ι → K)), subset_affineSpan K P, haff,
          by simpa using hEF.hasExtendedFormulation⟩
      exact le_antisymm (by simpa using hle) bot_le

/-- **Pair factorization theorem (exact equality)**: if there exists a linear functional
`u` vanishing on `rec(Q)` that is non-constant on `P` (equivalently `dir(aff(P)) ⊄ span(rec(Q))`),
then `xc(P, Q) = rank₊(S^{P, Q})`. -/
theorem pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_nonconst_perp
    [Finite μ] [Nonempty ν]
    {P Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} {R : ρ → ι → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b})
    (hPQ : P ⊆ Q)
    {u : ι → K} (hu_rec : ∀ v ∈ recessionCone K Q, u ⬝ᵥ v = 0)
    {x₁ x₂ : ι → K} (hx₁ : x₁ ∈ P) (hx₂ : x₂ ∈ P) (hlt : u ⬝ᵥ x₁ < u ⬝ᵥ x₂) :
    pairExtensionComplexity P Q = (pairSlackMatrix A b V R).nonnegRank := by
  refine le_antisymm (pairExtensionComplexity_le_nonnegRank_pairSlackMatrix hP hQ) ?_
  have hQne : {x : ι → K | A *ᵥ x ≤ b}.Nonempty := ⟨x₁, hQ ▸ hPQ hx₁⟩
  obtain ⟨β', β, hbdd⟩ :=
    exists_bounds_on_setOf_mulVec_le_of_dotProduct_recessionCone_eq_zero hQne (hQ ▸ hu_rec)
  refine le_pairExtensionComplexity_iff.2 fun r
      ⟨K_set, hPK, hKQ, d, e, E, F, g, E', F', g', hEF⟩ => ?_
  have hVP : ∀ j, V j ∈ K_set := fun j => hPK <| hP ▸ ⟨V j, subset_convexHull K _ ⟨j, rfl⟩,
    0, (PointedCone.hull K (Set.range R)).zero_mem, add_zero _⟩
  choose w hw using fun j => (hEF (V j)).1 (hVP j)
  obtain ⟨j₀⟩ := ‹Nonempty ν›
  have hRray : ∀ l : ρ, ∀ t : K, 0 ≤ t → V j₀ + t • R l ∈ K_set := fun l t ht =>
    hPK <| hP ▸ ⟨V j₀, subset_convexHull K _ ⟨j₀, rfl⟩, t • R l,
      (PointedCone.hull K (Set.range R)).smul_mem ht
        (PointedCone.subset_hull ⟨l, rfl⟩), rfl⟩
  choose z hz using fun l => exists_ray_lift_of_isExtendedFormulation hEF (hRray l)
  have hrow : ∀ i : μ, ∃ l : Fin r → K, 0 ≤ l ∧ ∀ x y, E' *ᵥ x + F' *ᵥ y = g' →
      l ⬝ᵥ (g - (E *ᵥ x + F *ᵥ y)) = b i - A i ⬝ᵥ x := fun i =>
    hEF.exists_nonneg_dotProduct_eq_sub u
      (fun x hx => (hbdd x (by simpa [hQ] using hKQ hx)).2)
      (fun x hx => (hbdd x (by simpa [hQ] using hKQ hx)).1)
      (hPK hx₁) (hPK hx₂) hlt (A i) (b i) fun x hx => (hQ ▸ hKQ hx) i
  choose l hl hlrow using hrow
  have hfac : (pairSlackMatrix A b V R).HasNonnegFactorization (Fin r) := by
    refine ⟨Matrix.of fun i k => l i k,
      Matrix.of fun k c => c.elim (fun j => (g - (E *ᵥ V j + F *ᵥ w j)) k)
        (fun s => -(E *ᵥ R s + F *ᵥ z s) k),
      fun i k => hl i k, ?_, Matrix.ext fun i c => ?_⟩
    · intro k c; cases c with
      | inl j => exact sub_nonneg.2 (hw j).1 k
      | inr s => exact neg_nonneg.2 (hz s).1 k
    · cases c with
      | inl j =>
        rw [Matrix.mul_apply', pairSlackMatrix_inl, ← hlrow i (V j) (w j) (hw j).2]; rfl
      | inr s =>
        have hsum : E' *ᵥ (V j₀ + R s) + F' *ᵥ (w j₀ + z s) = g' := by
          rw [mulVec_add, mulVec_add, add_add_add_comm, (hw j₀).2, (hz s).2, add_zero]
        have h1 := hlrow i (V j₀) (w j₀) (hw j₀).2
        have h2 := hlrow i (V j₀ + R s) (w j₀ + z s) hsum
        have hsub : (g - (E *ᵥ (V j₀ + R s) + F *ᵥ (w j₀ + z s))) -
            (g - (E *ᵥ V j₀ + F *ᵥ w j₀)) = -(E *ᵥ R s + F *ᵥ z s) := by
          ext k; simp only [mulVec_add, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring
        rw [Matrix.mul_apply', pairSlackMatrix_inr]
        change l i ⬝ᵥ (-(E *ᵥ R s + F *ᵥ z s)) = -(A i ⬝ᵥ R s)
        rw [← hsub, dotProduct_sub, h2, h1, dotProduct_add]
        ring
  simpa only [Fintype.card_fin] using hfac.nonnegRank_le

/-- **Pair factorization theorem (bounded polytope case)**: when `P` and `Q` are polytopes of
dimension at least `1` (more generally, `P` is nontrivial and `rec(Q) = {0}`),
`xc(P, Q) = rank₊(S^{P, Q})`. -/
theorem pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_bounded
    [Finite μ] [Nonempty ν]
    {P Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} {R : ρ → ι → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b}) (hPQ : P ⊆ Q)
    (hrec : recessionCone K Q = {0}) (hPnt : P.Nontrivial) :
    pairExtensionComplexity P Q = (pairSlackMatrix A b V R).nonnegRank := by
  classical
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hPnt
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · exact pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_nonconst_perp hP hQ hPQ
      (u := Pi.single k 1)
      (fun v hv => by rw [hrec, Set.mem_singleton_iff] at hv; rw [hv, dotProduct_zero])
      hx₁ hx₂ (by simpa [single_dotProduct] using hlt)
  · exact pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_nonconst_perp hP hQ hPQ
      (u := Pi.single k 1)
      (fun v hv => by rw [hrec, Set.mem_singleton_iff] at hv; rw [hv, dotProduct_zero])
      hx₂ hx₁ (by simpa [single_dotProduct] using hgt)

/-- Full-dimensional corollary: if `P` is full-dimensional (`vectorSpan K P = ⊤`) and `rec(Q)`
is not full-dimensional (`Submodule.span K (recessionCone K Q) ≠ ⊤`), then
`xc(P, Q) = rank₊(S^{P, Q})`. -/
theorem pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_fullDim
    [Finite μ] [Nonempty ν]
    {P Q : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} {R : ρ → ι → K}
    (hP : P = convexHull K (Set.range V) + (PointedCone.hull K (Set.range R) : Set (ι → K)))
    (hQ : Q = {x | A *ᵥ x ≤ b}) (hPQ : P ⊆ Q)
    (hPfull : vectorSpan K P = ⊤) (hQrec : Submodule.span K (recessionCone K Q) ≠ ⊤) :
    pairExtensionComplexity P Q = (pairSlackMatrix A b V R).nonnegRank := by
  classical
  let S : Submodule K (ι → K) := Submodule.span K (recessionCone K Q)
  obtain ⟨w, hw⟩ : ∃ w : ι → K, w ∉ S := by
    by_contra! hall
    exact hQrec (eq_top_iff.2 fun x _ => hall x)
  let Qmod := (ι → K) ⧸ S
  have hne0 : S.mkQ w ≠ 0 := by
    rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hw
  let bQ := Module.finBasis K Qmod
  obtain ⟨idx, hidx⟩ : ∃ idx, bQ.equivFun (S.mkQ w) idx ≠ 0 := by
    by_contra! hall
    exact hne0 (bQ.equivFun.injective (by rw [map_zero]; exact funext hall))
  let φ : (ι → K) →ₗ[K] K := (LinearMap.proj idx).comp (bQ.equivFun.toLinearMap.comp S.mkQ)
  let u : ι → K := fun i => φ (Pi.single i 1)
  have hu_dot : ∀ x : ι → K, u ⬝ᵥ x = φ x := fun x => by
    conv_rhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, u, mul_comm]
  have hu_rec : ∀ v ∈ recessionCone K Q, u ⬝ᵥ v = 0 := fun v hv => by
    rw [hu_dot]
    change (bQ.equivFun (S.mkQ v)) idx = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span hv),
      map_zero, Pi.zero_apply]
  obtain ⟨j₀⟩ := ‹Nonempty ν›
  have hp₀ : V j₀ ∈ P := hP ▸ ⟨V j₀, subset_convexHull K _ ⟨j₀, rfl⟩,
    0, (PointedCone.hull K (Set.range R)).zero_mem, add_zero _⟩
  have hnonconst : ∃ x₁ ∈ P, ∃ x₂ ∈ P, u ⬝ᵥ x₁ ≠ u ⬝ᵥ x₂ := by
    by_contra! hconst
    have hker : ∀ v ∈ vectorSpan K P, φ v = 0 := by
      intro v hv
      rw [vectorSpan_def] at hv
      refine Submodule.span_induction ?_ (map_zero φ) (fun x y _ _ hx hy => by simp [hx, hy])
        (fun a x _ hx => by simp [hx]) hv
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      dsimp only
      rw [vsub_eq_sub, map_sub, ← hu_dot, ← hu_dot, hconst x₁ hx₁ x₂ hx₂, sub_self]
    have hφw : φ w = 0 := hker w (hPfull ▸ Submodule.mem_top)
    exact hidx hφw
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hnonconst
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_nonconst_perp hP hQ hPQ
      hu_rec hx₁ hx₂ hlt
  · exact pairExtensionComplexity_eq_nonnegRank_pairSlackMatrix_of_nonconst_perp hP hQ hPQ
      hu_rec hx₂ hx₁ hgt

end SandwichTheorem

/-! ### Linear encodings and approximate extended formulations -/

section Framework

variable {ι : Type*} [Fintype ι]

/-- A fixed-dimension **linear encoding** `(L, O)` of a combinatorial optimization problem
: a nonempty finite set of feasible `0/1` solutions
`feasible ⊆ {0, 1}^ι` and a set `objectives ⊆ ℝ^ι` of admissible objective vectors. -/
@[ext] structure LinearEncoding (ι : Type*) where
  /-- The feasible solutions `L ∩ {0, 1}^ι`. -/
  feasible : Finset (ι → ℝ)
  /-- Every feasible solution is a `0/1` vector. -/
  feasible_zero_one : ∀ x ∈ feasible, ∀ i, x i = 0 ∨ x i = 1
  /-- There is at least one feasible solution. -/
  feasible_nonempty : feasible.Nonempty
  /-- The set `O ∩ ℝ^ι` of admissible objective functions. -/
  objectives : Set (ι → ℝ)

/-- The inner `0/1`-polytope `P = conv(L)` of a linear encoding. -/
def LinearEncoding.innerPolytope (E : LinearEncoding ι) : Set (ι → ℝ) :=
  convexHull ℝ (E.feasible : Set (ι → ℝ))

omit [Fintype ι] in
/-- `E.innerPolytope` is the convex hull of `E.feasible`. -/
theorem LinearEncoding.innerPolytope_eq_convexHull (E : LinearEncoding ι) :
    E.innerPolytope = convexHull ℝ (E.feasible : Set (ι → ℝ)) := by
  rw [LinearEncoding.innerPolytope]

/-- The optimal maximization value `max {w ⬝ᵥ z | z ∈ P} = max_{z ∈ L} w ⬝ᵥ z`. -/
noncomputable def LinearEncoding.optMax (E : LinearEncoding ι) (w : ι → ℝ) : ℝ :=
  (E.feasible.image (fun z => w ⬝ᵥ z)).max' (E.feasible_nonempty.image _)

/-- The optimal minimization value `min {w ⬝ᵥ z | z ∈ P} = min_{z ∈ L} w ⬝ᵥ z`. -/
noncomputable def LinearEncoding.optMin (E : LinearEncoding ι) (w : ι → ℝ) : ℝ :=
  (E.feasible.image (fun z => w ⬝ᵥ z)).min' (E.feasible_nonempty.image _)

/-- The outer convex set `Q` for a maximization problem:
`{x | ∀ w ∈ O, w ⬝ᵥ x ≤ max {w ⬝ᵥ z | z ∈ P}}`. -/
def LinearEncoding.outerMaxSet (E : LinearEncoding ι) : Set (ι → ℝ) :=
  {x | ∀ w ∈ E.objectives, w ⬝ᵥ x ≤ E.optMax w}

/-- Membership characterization for `E.outerMaxSet`. -/
theorem LinearEncoding.mem_outerMaxSet_iff (E : LinearEncoding ι) {x : ι → ℝ} :
    x ∈ E.outerMaxSet ↔ ∀ w ∈ E.objectives, w ⬝ᵥ x ≤ E.optMax w :=
  Iff.rfl

/-- The outer convex set `Q` for a minimization problem:
`{x | ∀ w ∈ O, w ⬝ᵥ x ≥ min {w ⬝ᵥ z | z ∈ P}}`. -/
def LinearEncoding.outerMinSet (E : LinearEncoding ι) : Set (ι → ℝ) :=
  {x | ∀ w ∈ E.objectives, E.optMin w ≤ w ⬝ᵥ x}

/-- Membership characterization for `E.outerMinSet`. -/
theorem LinearEncoding.mem_outerMinSet_iff (E : LinearEncoding ι) {x : ι → ℝ} :
    x ∈ E.outerMinSet ↔ ∀ w ∈ E.objectives, E.optMin w ≤ w ⬝ᵥ x :=
  Iff.rfl

/-- `optMax E w` is the exact upper bound of `w ⬝ᵥ z` over `z ∈ E.innerPolytope`. -/
theorem LinearEncoding.dotProduct_le_optMax (E : LinearEncoding ι) (w : ι → ℝ) {z : ι → ℝ}
    (hz : z ∈ E.innerPolytope) : w ⬝ᵥ z ≤ E.optMax w := by
  refine convexHull_min (fun x hx => ?_)
    (convex_halfSpace_le ⟨fun a b => dotProduct_add w a b, fun c a => dotProduct_smul c w a⟩ _) hz
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hx)

/-- `optMax E w` is attained by some feasible point in `E.innerPolytope`. -/
theorem LinearEncoding.exists_mem_innerPolytope_eq_optMax (E : LinearEncoding ι) (w : ι → ℝ) :
    ∃ z ∈ E.innerPolytope, w ⬝ᵥ z = E.optMax w := by
  have hmem := Finset.max'_mem (E.feasible.image (fun z => w ⬝ᵥ z)) (E.feasible_nonempty.image _)
  obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hmem
  exact ⟨z, subset_convexHull ℝ _ hz, hzw⟩

/-- `optMin E w` is the exact lower bound of `w ⬝ᵥ z` over `z ∈ E.innerPolytope`. -/
theorem LinearEncoding.optMin_le_dotProduct (E : LinearEncoding ι) (w : ι → ℝ) {z : ι → ℝ}
    (hz : z ∈ E.innerPolytope) : E.optMin w ≤ w ⬝ᵥ z := by
  have h : (-w) ⬝ᵥ z ≤ -(E.optMin w) := by
    refine convexHull_min (fun x hx => ?_)
      (convex_halfSpace_le ⟨fun a b => dotProduct_add (-w) a b,
        fun c a => dotProduct_smul c (-w) a⟩ _) hz
    change (-w) ⬝ᵥ x ≤ -(E.optMin w)
    rw [neg_dotProduct, neg_le_neg_iff]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)
  rw [neg_dotProduct] at h
  linarith

/-- `optMin E w` is attained by some feasible point in `E.innerPolytope`. -/
theorem LinearEncoding.exists_mem_innerPolytope_eq_optMin (E : LinearEncoding ι) (w : ι → ℝ) :
    ∃ z ∈ E.innerPolytope, w ⬝ᵥ z = E.optMin w := by
  have hmem := Finset.min'_mem (E.feasible.image (fun z => w ⬝ᵥ z)) (E.feasible_nonempty.image _)
  obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hmem
  exact ⟨z, subset_convexHull ℝ _ hz, hzw⟩

/-- `K_set` is a **`ρ`-approximate relaxation for a maximization problem** (`ρ ≥ 1`) in objective
form: for every `w ∈ ℝ^ι`, `sup_{K} w⬝x ≥ optMax w`
(realized by some `x ∈ K_set`), and for every admissible `w ∈ O`, `w ⬝ᵥ x ≤ ρ * optMax w` for all
`x ∈ K_set`. -/
def IsApproxMaxRelaxation (E : LinearEncoding ι) (ρ : ℝ) (K_set : Set (ι → ℝ)) : Prop :=
  (∀ w : ι → ℝ, ∃ x ∈ K_set, E.optMax w ≤ w ⬝ᵥ x) ∧
    (∀ w ∈ E.objectives, ∀ x ∈ K_set, w ⬝ᵥ x ≤ ρ * E.optMax w)

/-- Characterization of `IsApproxMaxRelaxation` without unfolding across modules. -/
theorem isApproxMaxRelaxation_iff (E : LinearEncoding ι) {ρ : ℝ} {K_set : Set (ι → ℝ)} :
    IsApproxMaxRelaxation E ρ K_set ↔
      (∀ w : ι → ℝ, ∃ x ∈ K_set, E.optMax w ≤ w ⬝ᵥ x) ∧
        (∀ w ∈ E.objectives, ∀ x ∈ K_set, w ⬝ᵥ x ≤ ρ * E.optMax w) :=
  Iff.rfl

/-- `K_set` is a **`ρ`-approximate relaxation for a minimization problem** (`ρ ≥ 1`) in objective
form. -/
def IsApproxMinRelaxation (E : LinearEncoding ι) (ρ : ℝ) (K_set : Set (ι → ℝ)) : Prop :=
  (∀ w : ι → ℝ, ∃ x ∈ K_set, w ⬝ᵥ x ≤ E.optMin w) ∧
    (∀ w ∈ E.objectives, ∀ x ∈ K_set, ρ⁻¹ * E.optMin w ≤ w ⬝ᵥ x)

/-- Characterization of `IsApproxMinRelaxation` without unfolding across modules. -/
theorem isApproxMinRelaxation_iff (E : LinearEncoding ι) {ρ : ℝ} {K_set : Set (ι → ℝ)} :
    IsApproxMinRelaxation E ρ K_set ↔
      (∀ w : ι → ℝ, ∃ x ∈ K_set, w ⬝ᵥ x ≤ E.optMin w) ∧
        (∀ w ∈ E.objectives, ∀ x ∈ K_set, ρ⁻¹ * E.optMin w ≤ w ⬝ᵥ x) :=
  Iff.rfl

/-- Every set admitting an extended formulation is an H-polyhedron `{x | M *ᵥ x ≤ d}`
(via Fourier–Motzkin elimination). -/
theorem exists_mulVec_le_of_hasExtendedFormulation {K_set : Set (ι → ℝ)} {r : ℕ}
    (hEF : HasExtendedFormulation K_set r) :
    ∃ (m : ℕ) (M : Matrix (Fin m) ι ℝ) (d : Fin m → ℝ), K_set = {x | M *ᵥ x ≤ d} := by
  classical
  obtain ⟨d, e, E, F, g, E', F', g', h⟩ := hEF
  let A' : Matrix (Fin r ⊕ (Fin e ⊕ Fin e)) (Fin d) ℝ := fromRows F (fromRows F' (-F'))
  let B' : Matrix (Fin r ⊕ (Fin e ⊕ Fin e)) ι ℝ := fromRows E (fromRows E' (-E'))
  let b' : Fin r ⊕ (Fin e ⊕ Fin e) → ℝ := Sum.elim g (Sum.elim g' (-g'))
  obtain ⟨τ, _, T, -, -, hproj⟩ := Matrix.FourierMotzkin.exists_projection A' B' b'
  have hiff : ∀ x : ι → ℝ, x ∈ K_set ↔ (T * B') *ᵥ x ≤ T *ᵥ b' := fun x => by
    rw [h x, ← hproj x]
    refine exists_congr fun y => ?_
    constructor
    · rintro ⟨h1, h2⟩ (i | j | j)
      · have h1i := h1 i
        simp only [Pi.add_apply] at h1i
        simp only [A', B', b', fromRows_mulVec, Sum.elim_inl, Pi.add_apply]; linarith
      · have h2j := congrFun h2 j
        simp only [Pi.add_apply] at h2j
        simp only [A', B', b', fromRows_mulVec, Sum.elim_inr, Sum.elim_inl, Pi.add_apply]
        linarith
      · have h2j := congrFun h2 j
        simp only [Pi.add_apply] at h2j
        simp only [A', B', b', fromRows_mulVec, neg_mulVec, Sum.elim_inr, Pi.add_apply,
          Pi.neg_apply]
        linarith
    · intro hall
      refine ⟨fun i => ?_, funext fun j => ?_⟩
      · have hi := hall (.inl i)
        simp only [A', B', b', fromRows_mulVec, Sum.elim_inl, Pi.add_apply] at hi
        simp only [Pi.add_apply]; linarith
      · have h1 := hall (.inr (.inl j))
        have h2 := hall (.inr (.inr j))
        simp only [A', B', b', fromRows_mulVec, neg_mulVec, Sum.elim_inr, Sum.elim_inl,
          Pi.add_apply, Pi.neg_apply] at h1 h2
        simp only [Pi.add_apply]; linarith
  let eτ := Fintype.equivFin τ
  refine ⟨Fintype.card τ, (T * B').submatrix eτ.symm id, (T *ᵥ b') ∘ eτ.symm, Set.ext fun x => ?_⟩
  rw [hiff x, Set.mem_ofPred_eq]
  constructor
  · intro hx i; simpa [mulVec, dotProduct] using hx (eτ.symm i)
  · intro hx i; simpa [mulVec, dotProduct] using hx (eτ i)

/-- **Objective-value vs. sandwich characterization (maximization)**
: for a polyhedron `K_set` (any set with an
extended formulation) and `ρ > 0`, `IsApproxMaxRelaxation E ρ K_set` is equivalent to
`E.innerPolytope ⊆ K_set ∧ K_set ⊆ ρ • E.outerMaxSet`. -/
theorem isApproxMaxRelaxation_iff_subset (E : LinearEncoding ι) {ρ : ℝ} (hρ : 0 < ρ)
    {K_set : Set (ι → ℝ)} {r : ℕ} (hEF : HasExtendedFormulation K_set r) :
    IsApproxMaxRelaxation E ρ K_set ↔
      E.innerPolytope ⊆ K_set ∧ K_set ⊆ ρ • E.outerMaxSet := by
  constructor
  · rintro ⟨hlb, hub⟩
    obtain ⟨m, M, d, hK⟩ := exists_mulVec_le_of_hasExtendedFormulation hEF
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [hK, Set.mem_ofPred_eq]
      intro i
      obtain ⟨x, hx, hopt⟩ := hlb (M i)
      have hxle : M i ⬝ᵥ x ≤ d i := (hK ▸ hx) i
      exact (E.dotProduct_le_optMax (M i) hz).trans (hopt.trans hxle)
    · intro x hx
      refine ⟨ρ⁻¹ • x, fun w hw => ?_,
        by dsimp only; rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]⟩
      rw [dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hρ]
      exact hub w hw x hx
  · rintro ⟨hPK, hKQ⟩
    refine ⟨fun w => ?_, fun w hw x hx => ?_⟩
    · obtain ⟨z, hz, hzw⟩ := E.exists_mem_innerPolytope_eq_optMax w
      exact ⟨z, hPK hz, hzw.ge⟩
    · obtain ⟨y, hy, rfl⟩ := hKQ hx
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hy w hw) hρ.le

/-- **Objective-value vs. sandwich characterization (minimization)**
: for a polyhedron `K_set` and `ρ > 0`,
`IsApproxMinRelaxation E ρ K_set` is equivalent to
`E.innerPolytope ⊆ K_set ∧ K_set ⊆ ρ⁻¹ • E.outerMinSet`. -/
theorem isApproxMinRelaxation_iff_subset (E : LinearEncoding ι) {ρ : ℝ} (hρ : 0 < ρ)
    {K_set : Set (ι → ℝ)} {r : ℕ} (hEF : HasExtendedFormulation K_set r) :
    IsApproxMinRelaxation E ρ K_set ↔
      E.innerPolytope ⊆ K_set ∧ K_set ⊆ ρ⁻¹ • E.outerMinSet := by
  constructor
  · rintro ⟨hub, hlb⟩
    obtain ⟨m, M, d, hK⟩ := exists_mulVec_le_of_hasExtendedFormulation hEF
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [hK, Set.mem_ofPred_eq]
      intro i
      obtain ⟨x, hx, hopt⟩ := hub (-M i)
      have hxle : M i ⬝ᵥ x ≤ d i := (hK ▸ hx) i
      have hzge := E.optMin_le_dotProduct (-M i) hz
      rw [neg_dotProduct] at hopt hzge
      change M i ⬝ᵥ z ≤ d i
      linarith
    · intro x hx
      refine ⟨ρ • x, fun w hw => ?_,
        by dsimp only; rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]⟩
      rw [dotProduct_smul, smul_eq_mul]
      have h := hlb w hw x hx
      have h' := mul_le_mul_of_nonneg_left h hρ.le
      rwa [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at h'
  · rintro ⟨hPK, hKQ⟩
    refine ⟨fun w => ?_, fun w hw x hx => ?_⟩
    · obtain ⟨z, hz, hzw⟩ := E.exists_mem_innerPolytope_eq_optMin w
      exact ⟨z, hPK hz, hzw.le⟩
    · obtain ⟨y, hy, rfl⟩ := hKQ hx
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hy w hw) (inv_nonneg.2 hρ.le)

/-- Dilating an H-polyhedron `{x | A *ᵥ x ≤ b}` by `ρ > 0` scales the right-hand side to `ρ • b`. -/
theorem smul_setOf_mulVec_le {μ : Type*} {A : Matrix μ ι ℝ} {b : μ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) :
    ρ • {x : ι → ℝ | A *ᵥ x ≤ b} = {x : ι → ℝ | A *ᵥ x ≤ ρ • b} := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hy i) hρ.le
  · intro hx
    refine ⟨ρ⁻¹ • x, fun i => ?_, by rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]⟩
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hρ]
    exact hx i

/-- Slack-matrix shift identity under dilation:
`S^{P, ρQ}_vertex(i, j) = S^{P, Q}_vertex(i, j) + (ρ - 1) * b i`. -/
theorem pairSlackMatrix_smul_inl {μ ν ρ_idx : Type*} (A : Matrix μ ι ℝ) (b : μ → ℝ)
    (V : ν → ι → ℝ) (R : ρ_idx → ι → ℝ) (ρ : ℝ) (i : μ) (j : ν) :
    pairSlackMatrix A (ρ • b) V R i (.inl j) =
      pairSlackMatrix A b V R i (.inl j) + (ρ - 1) * b i := by
  simp only [pairSlackMatrix_inl, Pi.smul_apply, smul_eq_mul]
  ring

/-- Slack-matrix ray invariance under dilation:
`S^{P, ρQ}_ray(i, l) = S^{P, Q}_ray(i, l)`. -/
theorem pairSlackMatrix_smul_inr {μ ν ρ_idx : Type*} (A : Matrix μ ι ℝ) (b : μ → ℝ)
    (V : ν → ι → ℝ) (R : ρ_idx → ι → ℝ) (ρ : ℝ) (i : μ) (l : ρ_idx) :
    pairSlackMatrix A (ρ • b) V R i (.inr l) = pairSlackMatrix A b V R i (.inr l) := by
  simp only [pairSlackMatrix_inr]

/-- Minimum size of a `ρ`-approximate EF for a maximization linear encoding. -/
noncomputable def maxApproxEFComplexity (E : LinearEncoding ι) (ρ : ℝ) : ℕ∞ :=
  ⨅ r : {r : ℕ // ∃ K_set, IsApproxMaxRelaxation E ρ K_set ∧ HasExtendedFormulation K_set r},
    (r.1 : ℕ∞)

/-- An explicit `ρ`-approximate EF of size `r` upper-bounds `maxApproxEFComplexity E ρ`. -/
theorem maxApproxEFComplexity_le {E : LinearEncoding ι} {ρ : ℝ} {K_set : Set (ι → ℝ)} {r : ℕ}
    (hrelax : IsApproxMaxRelaxation E ρ K_set) (hEF : HasExtendedFormulation K_set r) :
    maxApproxEFComplexity E ρ ≤ r := by
  rw [maxApproxEFComplexity]
  exact iInf_le (fun s : {s : ℕ // _} => (s.1 : ℕ∞)) ⟨r, K_set, hrelax, hEF⟩

/-- Minimum size of a `ρ`-approximate EF for a minimization linear encoding. -/
noncomputable def minApproxEFComplexity (E : LinearEncoding ι) (ρ : ℝ) : ℕ∞ :=
  ⨅ r : {r : ℕ // ∃ K_set, IsApproxMinRelaxation E ρ K_set ∧ HasExtendedFormulation K_set r},
    (r.1 : ℕ∞)

/-- An explicit `ρ`-approximate EF of size `r` upper-bounds `minApproxEFComplexity E ρ`. -/
theorem minApproxEFComplexity_le {E : LinearEncoding ι} {ρ : ℝ} {K_set : Set (ι → ℝ)} {r : ℕ}
    (hrelax : IsApproxMinRelaxation E ρ K_set) (hEF : HasExtendedFormulation K_set r) :
    minApproxEFComplexity E ρ ≤ r := by
  rw [minApproxEFComplexity]
  exact iInf_le (fun s : {s : ℕ // _} => (s.1 : ℕ∞)) ⟨r, K_set, hrelax, hEF⟩

/-- For `ρ > 0`, `maxApproxEFComplexity E ρ` equals `xc(P, ρ • Q)`. -/
theorem maxApproxEFComplexity_eq_pairExtensionComplexity (E : LinearEncoding ι) {ρ : ℝ}
    (hρ : 0 < ρ) :
    maxApproxEFComplexity E ρ =
      pairExtensionComplexity E.innerPolytope (ρ • E.outerMaxSet) := by
  have heq : ∀ r : ℕ, (∃ K_set, IsApproxMaxRelaxation E ρ K_set ∧ HasExtendedFormulation K_set r) ↔
      HasPairExtendedFormulation E.innerPolytope (ρ • E.outerMaxSet) r := fun r =>
    exists_congr fun K_set => ⟨fun ⟨h1, h2⟩ =>
      let ⟨hP, hQ⟩ := (isApproxMaxRelaxation_iff_subset E hρ h2).1 h1; ⟨hP, hQ, h2⟩,
      fun ⟨hP, hQ, h2⟩ => ⟨(isApproxMaxRelaxation_iff_subset E hρ h2).2 ⟨hP, hQ⟩, h2⟩⟩
  refine le_antisymm ?_ ?_
  · refine le_pairExtensionComplexity_iff.2 fun r hr => ?_
    obtain ⟨K_set, h1, h2⟩ := (heq r).2 hr
    exact maxApproxEFComplexity_le h1 h2
  · rw [maxApproxEFComplexity]
    refine le_iInf fun ⟨r, hr⟩ => ?_
    exact HasPairExtendedFormulation.pairExtensionComplexity_le ((heq r).1 hr)

/-- For `ρ > 0`, `minApproxEFComplexity E ρ` equals `xc(P, ρ⁻¹ • Q)`. -/
theorem minApproxEFComplexity_eq_pairExtensionComplexity (E : LinearEncoding ι) {ρ : ℝ}
    (hρ : 0 < ρ) :
    minApproxEFComplexity E ρ =
      pairExtensionComplexity E.innerPolytope (ρ⁻¹ • E.outerMinSet) := by
  have heq : ∀ r : ℕ, (∃ K_set, IsApproxMinRelaxation E ρ K_set ∧ HasExtendedFormulation K_set r) ↔
      HasPairExtendedFormulation E.innerPolytope (ρ⁻¹ • E.outerMinSet) r := fun r =>
    exists_congr fun K_set => ⟨fun ⟨h1, h2⟩ =>
      let ⟨hP, hQ⟩ := (isApproxMinRelaxation_iff_subset E hρ h2).1 h1; ⟨hP, hQ, h2⟩,
      fun ⟨hP, hQ, h2⟩ => ⟨(isApproxMinRelaxation_iff_subset E hρ h2).2 ⟨hP, hQ⟩, h2⟩⟩
  refine le_antisymm ?_ ?_
  · refine le_pairExtensionComplexity_iff.2 fun r hr => ?_
    obtain ⟨K_set, h1, h2⟩ := (heq r).2 hr
    exact minApproxEFComplexity_le h1 h2
  · rw [minApproxEFComplexity]
    refine le_iInf fun ⟨r, hr⟩ => ?_
    exact HasPairExtendedFormulation.pairExtensionComplexity_le ((heq r).1 hr)

/-- **Approximate extended formulation characterization (maximization)**:
if `Q = {x | A *ᵥ x ≤ b}` is the outer polyhedron of a linear encoding `E` and `ρ ≥ 1`, then the
minimum size of a `ρ`-approximate EF satisfies
`rank₊(S^{P, ρQ}) - 1 ≤ maxApproxEFComplexity E ρ ≤ rank₊(S^{P, ρQ})`. -/
theorem framework_max_bounds {μ ν ρ_idx : Type*} [Finite μ] [Nonempty ν]
    (E : LinearEncoding ι) {ρ : ℝ} (hρ : 1 ≤ ρ)
    {A : Matrix μ ι ℝ} {b : μ → ℝ} {V : ν → ι → ℝ} {R : ρ_idx → ι → ℝ}
    (hP : E.innerPolytope =
      convexHull ℝ (Set.range V) + (PointedCone.hull ℝ (Set.range R) : Set (ι → ℝ)))
    (hQ : E.outerMaxSet = {x | A *ᵥ x ≤ b}) :
    (pairSlackMatrix A (ρ • b) V R).nonnegRank - 1 ≤ maxApproxEFComplexity E ρ ∧
      maxApproxEFComplexity E ρ ≤ (pairSlackMatrix A (ρ • b) V R).nonnegRank := by
  have hρpos : 0 < ρ := by linarith
  rw [maxApproxEFComplexity_eq_pairExtensionComplexity E hρpos]
  exact pairExtensionComplexity_bounds hP (by rw [hQ, smul_setOf_mulVec_le hρpos])

/-- **Approximate extended formulation characterization (minimization)**:
for `ρ ≥ 1`, the minimum size of a `ρ`-approximate EF satisfies
`rank₊(S^{P, ρ⁻¹Q}) - 1 ≤ minApproxEFComplexity E ρ ≤ rank₊(S^{P, ρ⁻¹Q})`. -/
theorem framework_min_bounds {μ ν ρ_idx : Type*} [Finite μ] [Nonempty ν]
    (E : LinearEncoding ι) {ρ : ℝ} (hρ : 1 ≤ ρ)
    {A : Matrix μ ι ℝ} {b : μ → ℝ} {V : ν → ι → ℝ} {R : ρ_idx → ι → ℝ}
    (hP : E.innerPolytope =
      convexHull ℝ (Set.range V) + (PointedCone.hull ℝ (Set.range R) : Set (ι → ℝ)))
    (hQ : E.outerMinSet = {x | A *ᵥ x ≤ b}) :
    (pairSlackMatrix A (ρ⁻¹ • b) V R).nonnegRank - 1 ≤ minApproxEFComplexity E ρ ∧
      minApproxEFComplexity E ρ ≤ (pairSlackMatrix A (ρ⁻¹ • b) V R).nonnegRank := by
  have hρpos : 0 < ρ⁻¹ := inv_pos.2 (by linarith)
  rw [minApproxEFComplexity_eq_pairExtensionComplexity E (by linarith)]
  exact pairExtensionComplexity_bounds hP (by rw [hQ, smul_setOf_mulVec_le hρpos])

end Framework

end CslibFrontier.ExtendedFormulation
