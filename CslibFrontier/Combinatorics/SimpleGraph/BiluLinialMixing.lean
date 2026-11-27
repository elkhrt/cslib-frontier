/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bilu–Linial Edge-Signed 2-Lifts and Converse Expander Mixing Lemma

This module defines graph covering lifts, Bilu–Linial edge-signed `2`-lifts on `V × ℤˣ`, and their
signed normalized adjacency operators on finite simple graphs, proves unconditional `ℓ²` operator
contraction, and establishes the Bilu–Linial converse expander mixing lemma
 with explicit universal constant `C = 128` via symmetric bipartition averaging, Abel
summation, and dyadic level-set decomposition, under standard Lean axioms.

## Main definitions

- `CslibFrontier.SimpleGraph.IsGraphLift`: graph covering lifts (local neighbor-set bijections).
- `CslibFrontier.SimpleGraph.signedLift`, `CslibFrontier.SimpleGraph.signedLiftHom`:
  Bilu–Linial edge-signed `2`-lift of a simple graph and its projection homomorphism.
- `CslibFrontier.SimpleGraph.signedNormAdjMatrix`: signed normalized adjacency operator `M_f(G)`.

## Main results

- `CslibFrontier.SimpleGraph.isGraphLift_signedLift`,
  `CslibFrontier.SimpleGraph.signedLift_isRegularOfDegree`: covering and regularity preservation.
- `CslibFrontier.SimpleGraph.sum_sq_signedNormAdjMatrix_mulVec_le`,
  `CslibFrontier.SimpleGraph.opNorm_signedNormAdjMatrix_le_one`: `ℓ²` contraction `‖M_f(G)‖ ≤ 1`.
- `CslibFrontier.SimpleGraph.biluLinial_converse_mixing_explicit`,
  `CslibFrontier.SimpleGraph.biluLinial_converse_mixing`: any `d`-regular finite graph (`1 ≤ d`)
  with disjoint-set signed discrepancy bounded by `α √(|S| |T|)` satisfies
  `‖M_f(G) x‖₂ ≤ 128 α (1 + max 0 (log₂ (1 / α))) ‖x‖₂`.
-/

public section

open Finset Matrix
open scoped BigOperators

namespace CslibFrontier.SimpleGraph

/-! ### 1. Graph Covering Lifts and Edge-Signed 2-Lifts -/

section SignedLift

/-- A map `π : V → W` is a graph lift (covering map) from `G` to `H` if `π` is a graph homomorphism
that induces a bijection from `G.neighborSet x` onto `H.neighborSet (π x)` at every vertex `x`. -/
def IsGraphLift {V W : Type*} (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W) (π : V → W) :
    Prop :=
  (∀ ⦃x y : V⦄, G.Adj x y → H.Adj (π x) (π y)) ∧
    ∀ (x : V) (w : W), H.Adj (π x) w → ∃! y : V, G.Adj x y ∧ π y = w

/-- Precomposing a graph lift `π` from `G'` to `H` with a graph isomorphism `e : G ≃g G'` yields a
graph lift from `G` to `H`. -/
theorem IsGraphLift.comp_iso {U V W : Type*} {G : _root_.SimpleGraph U}
    {G' : _root_.SimpleGraph V} {H : _root_.SimpleGraph W} {π : V → W}
    (hπ : IsGraphLift G' H π) (e : G ≃g G') :
    IsGraphLift G H (π ∘ e) := by
  refine ⟨fun _ _ h ↦ hπ.1 (e.map_rel_iff.mpr h), fun x w hxw ↦ ?_⟩
  obtain ⟨y', ⟨hadj', heq'⟩, hunique'⟩ := hπ.2 (e x) w hxw
  refine ⟨e.symm y', ⟨by simpa using e.symm.map_rel_iff.mpr hadj', by simp [heq']⟩,
    fun z ⟨hadj, heq⟩ ↦ ?_⟩
  have hzy := hunique' (e z) ⟨e.map_rel_iff.mpr hadj, heq⟩
  exact e.injective (by simpa using hzy)

/-- The Bilu–Linial edge-signed `2`-lift of `G` determined by an edge signing `f : Sym2 V → ℤˣ` on
vertex set `V × ℤˣ`. -/
def signedLift {V : Type*} (G : _root_.SimpleGraph V) (f : Sym2 V → ℤˣ) :
    _root_.SimpleGraph (V × ℤˣ) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 * y.2 = f s(x.1, y.1)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [mul_comm, h.2, Sym2.eq_swap]⟩⟩
  loopless := ⟨fun x h ↦ G.loopless.irrefl x.1 h.1⟩

instance instDecidableRelSignedLiftAdj {V : Type*} (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V → ℤˣ) : DecidableRel (signedLift G f).Adj :=
  fun x y ↦ inferInstanceAs (Decidable (G.Adj x.1 y.1 ∧ x.2 * y.2 = f s(x.1, y.1)))

/-- Adjacency characterization in `signedLift G f`. -/
@[simp, grind =]
theorem signedLift_adj {V : Type*} (G : _root_.SimpleGraph V) (f : Sym2 V → ℤˣ) (x y : V × ℤˣ) :
    (signedLift G f).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 * y.2 = f s(x.1, y.1) := Iff.rfl

/-- Canonical first-coordinate graph homomorphism from `signedLift G f` to `G`. -/
def signedLiftHom {V : Type*} (G : _root_.SimpleGraph V) (f : Sym2 V → ℤˣ) :
    signedLift G f →g G where
  toFun := Prod.fst
  map_rel' h := h.1

/-- First-coordinate projection `Prod.fst : V × ℤˣ → V` is a graph lift (covering map) from
`signedLift G f` to `G`. -/
theorem isGraphLift_signedLift {V : Type*} (G : _root_.SimpleGraph V) (f : Sym2 V → ℤˣ) :
    IsGraphLift (signedLift G f) G Prod.fst := by
  refine ⟨fun _ _ h ↦ h.1, fun x u hxu ↦ ?_⟩
  refine ⟨(u, x.2 * f s(x.1, u)), ⟨⟨hxu, ?_⟩, rfl⟩, fun y ⟨⟨_, hy2⟩, hy1⟩ ↦ Prod.ext hy1 ?_⟩
  · rw [← mul_assoc, Int.units_mul_self, one_mul]
  · calc y.2 = x.2 * (x.2 * y.2) := by rw [← mul_assoc, Int.units_mul_self, one_mul]
      _ = x.2 * f s(x.1, u) := by rw [hy2, hy1]

/-- Every vertex `(u, s)` in `signedLift G f` has degree `G.degree u`. -/
theorem degree_signedLift {V : Type*} [Fintype V] (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V → ℤˣ) (x : V × ℤˣ) : (signedLift G f).degree x = G.degree x.1 := by
  rw [← _root_.SimpleGraph.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun y _ ↦ y.1)
    (fun y hy ↦ (G.mem_neighborFinset x.1 y.1).mpr
      ((signedLift_adj G f x y).mp ((_root_.SimpleGraph.mem_neighborFinset _ _ _).mp hy)).1)
    (fun y₁ hy₁ y₂ hy₂ h12 ↦ Prod.ext h12 (by
      have h1 := ((signedLift_adj G f x y₁).mp
        ((_root_.SimpleGraph.mem_neighborFinset _ _ _).mp hy₁)).2
      have h2 := ((signedLift_adj G f x y₂).mp
        ((_root_.SimpleGraph.mem_neighborFinset _ _ _).mp hy₂)).2
      calc y₁.2 = x.2 * (x.2 * y₁.2) := by rw [← mul_assoc, Int.units_mul_self, one_mul]
        _ = x.2 * f s(x.1, y₁.1) := by rw [h1]
        _ = x.2 * (x.2 * y₂.2) := by rw [h12, h2]
        _ = y₂.2 := by rw [← mul_assoc, Int.units_mul_self, one_mul]))
    (fun u hu ↦ ⟨(u, x.2 * f s(x.1, u)), (_root_.SimpleGraph.mem_neighborFinset _ _ _).mpr
      ⟨(G.mem_neighborFinset x.1 u).mp hu,
        by rw [← mul_assoc, Int.units_mul_self, one_mul]⟩, rfl⟩)

/-- If `G` is `d`-regular, then `signedLift G f` is `d`-regular. -/
theorem signedLift_isRegularOfDegree {V : Type*} [Fintype V] {G : _root_.SimpleGraph V}
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    (signedLift G f).IsRegularOfDegree d := fun x ↦ by
  rw [degree_signedLift G f x, hreg.degree_eq x.1]

/-- Signed normalized adjacency matrix `M_f(G)` of a graph `G` with edge signing `f`. -/
noncomputable def signedNormAdjMatrix {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) : Matrix V V ℝ :=
  Matrix.of fun u v ↦
    if G.Adj u v then ((f s(u, v) : ℤ) : ℝ) * (Real.sqrt ((G.degree u : ℝ) * G.degree v))⁻¹
    else 0

/-- Entrywise evaluation of `signedNormAdjMatrix G f`. -/
theorem signedNormAdjMatrix_apply {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) (u v : V) :
    signedNormAdjMatrix G f u v =
      if G.Adj u v then ((f s(u, v) : ℤ) : ℝ) * (Real.sqrt ((G.degree u : ℝ) * G.degree v))⁻¹
      else 0 := by simp [signedNormAdjMatrix]

/-- Diagonal entries of `signedNormAdjMatrix G f` vanish. -/
@[simp]
theorem signedNormAdjMatrix_apply_self {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) (u : V) : signedNormAdjMatrix G f u u = 0 := by
  simp [signedNormAdjMatrix_apply]

/-- Off-diagonal entries of `signedNormAdjMatrix G f` vanish on non-adjacent pairs. -/
theorem signedNormAdjMatrix_apply_of_not_adj {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) {u v : V} (h : ¬ G.Adj u v) :
    signedNormAdjMatrix G f u v = 0 := by
  simp [signedNormAdjMatrix_apply, h]

/-- `signedNormAdjMatrix G f` is symmetric. -/
theorem isSymm_signedNormAdjMatrix {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) : (signedNormAdjMatrix G f).IsSymm := by
  ext u v
  simp only [Matrix.transpose_apply, signedNormAdjMatrix_apply, G.adj_comm u v, Sym2.eq_swap,
    mul_comm (G.degree u : ℝ) (G.degree v)]

/-- `signedNormAdjMatrix G f` is Hermitian over `ℝ`. -/
theorem isHermitian_signedNormAdjMatrix {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) : (signedNormAdjMatrix G f).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (isSymm_signedNormAdjMatrix G f)

/-- Entrywise formula for `signedNormAdjMatrix G f` on a `d`-regular graph. -/
theorem signedNormAdjMatrix_apply_of_regular {V : Type*} [Fintype V] {G : _root_.SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hreg : G.IsRegularOfDegree d) (f : Sym2 V → ℤˣ) (u v : V) :
    signedNormAdjMatrix G f u v = if G.Adj u v then ((f s(u, v) : ℤ) : ℝ) / d else 0 := by
  rw [signedNormAdjMatrix_apply]
  split_ifs with hadj
  · rw [hreg.degree_eq u, hreg.degree_eq v, Real.sqrt_mul_self (Nat.cast_nonneg d), div_eq_mul_inv]
  · rfl

/-- Unconditional `ℓ²`-contraction inequality for `signedNormAdjMatrix G f`. -/
theorem sum_sq_signedNormAdjMatrix_mulVec_le {V : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) (x : V → ℝ) :
    ∑ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2 ≤ ∑ u : V, x u ^ 2 := by
  have hrow : ∀ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2 ≤
      ∑ v ∈ G.neighborFinset u, x v ^ 2 / (G.degree v : ℝ) := fun u ↦ by
    have hmul_eq : (signedNormAdjMatrix G f *ᵥ x) u =
        ∑ v ∈ G.neighborFinset u, (Real.sqrt (G.degree u))⁻¹ *
          (((f s(u, v) : ℤ) : ℝ) * (Real.sqrt (G.degree v))⁻¹ * x v) := by
      simp only [Matrix.mulVec, dotProduct, signedNormAdjMatrix_apply, ite_mul, zero_mul]
      rw [← Finset.sum_filter, show Finset.univ.filter (fun v ↦ G.Adj u v) = G.neighborFinset u
        from Finset.ext fun v ↦ by simp [_root_.SimpleGraph.mem_neighborFinset]]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]; ring
    rw [hmul_eq]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (G.neighborFinset u)
      (fun _ ↦ (Real.sqrt (G.degree u))⁻¹)
      (fun v ↦ ((f s(u, v) : ℤ) : ℝ) * (Real.sqrt (G.degree v))⁻¹ * x v)
    have hfirst : ∑ _v ∈ G.neighborFinset u, ((Real.sqrt (G.degree u))⁻¹) ^ 2 ≤ 1 := by
      rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul, inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
      by_cases hu : G.degree u = 0 <;> simp [hu]
    have hsecond : ∑ v ∈ G.neighborFinset u,
        (((f s(u, v) : ℤ) : ℝ) * (Real.sqrt (G.degree v))⁻¹ * x v) ^ 2 =
          ∑ v ∈ G.neighborFinset u, x v ^ 2 / (G.degree v : ℝ) := by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      have hf2 : (((f s(u, v) : ℤ) : ℝ) ^ 2) = 1 := by
        rcases Int.units_eq_one_or (f s(u, v)) with h1 | h1 <;> simp [h1]
      calc (((f s(u, v) : ℤ) : ℝ) * (Real.sqrt (G.degree v))⁻¹ * x v) ^ 2
          = (((f s(u, v) : ℤ) : ℝ) ^ 2) * (((Real.sqrt (G.degree v))⁻¹) ^ 2 * x v ^ 2) := by ring
        _ = x v ^ 2 / (G.degree v : ℝ) := by
            rw [hf2, one_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_eq_inv_mul]
    exact (hcs.trans (mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      hfirst)).trans_eq hsecond
  calc ∑ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2
      ≤ ∑ u : V, ∑ v ∈ G.neighborFinset u, x v ^ 2 / (G.degree v : ℝ) :=
        Finset.sum_le_sum fun u _ ↦ hrow u
    _ = ∑ v : V, ∑ _u ∈ G.neighborFinset v, x v ^ 2 / (G.degree v : ℝ) := by
        simp_rw [_root_.SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
          simp only [G.adj_comm]
    _ = ∑ v : V, (G.degree v : ℝ) * (x v ^ 2 / (G.degree v : ℝ)) :=
        Finset.sum_congr rfl fun v _ ↦ by
          rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    _ ≤ ∑ v : V, x v ^ 2 := Finset.sum_le_sum fun v _ ↦ by
        by_cases hv : G.degree v = 0
        · simp [hv, sq_nonneg]
        · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hv)]

open scoped Matrix.Norms.L2Operator in
/-- The Euclidean operator norm of `signedNormAdjMatrix G f` is at most `1`. -/
theorem opNorm_signedNormAdjMatrix_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) :
    ‖signedNormAdjMatrix G f‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul]; refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  exact sum_sq_signedNormAdjMatrix_mulVec_le G f x.ofLp

end SignedLift

/-! ### 2. Bilu–Linial Converse Expander Mixing Lemma -/

section ConverseMixing

private def flipAt {U : Type*} [DecidableEq U] (x : U) : (U → Bool) ≃ (U → Bool) where
  toFun σ w := if w = x then !σ x else σ w
  invFun σ w := if w = x then !σ x else σ w
  left_inv σ := funext fun w ↦ by by_cases hw : w = x <;> simp [hw]
  right_inv σ := funext fun w ↦ by by_cases hw : w = x <;> simp [hw]

private lemma four_mul_sum_bipartition_eq {U : Type*} [Fintype U] [DecidableEq U]
    {u v : U} (huv : u ≠ v) :
    (4 : ℝ) * ∑ σ : U → Bool, (if σ u = true ∧ σ v = false then (1 : ℝ) else 0) =
      (2 : ℝ) ^ Fintype.card U := by
  let g : (U → Bool) → ℝ := fun σ ↦ if σ u = true ∧ σ v = false then 1 else 0
  have h1 := Fintype.sum_equiv (flipAt u) (fun σ ↦ g (flipAt u σ)) g fun _ ↦ rfl
  have h2 := Fintype.sum_equiv (flipAt v) (fun σ ↦ g (flipAt v σ)) g fun _ ↦ rfl
  have h3 := Fintype.sum_equiv ((flipAt v).trans (flipAt u))
    (fun σ ↦ g (flipAt u (flipAt v σ))) g fun _ ↦ rfl
  have h4 : (4 : ℝ) * ∑ σ : U → Bool, g σ =
      ∑ σ : U → Bool, (g σ + g (flipAt u σ) + g (flipAt v σ) + g (flipAt u (flipAt v σ))) := by
    simp only [Finset.sum_add_distrib, h1, h2, h3]; ring
  have hpt : ∀ σ : U → Bool,
      g σ + g (flipAt u σ) + g (flipAt v σ) + g (flipAt u (flipAt v σ)) = 1 := fun σ ↦ by
    dsimp only [g, flipAt]
    by_cases h1 : σ u = true <;> by_cases h2 : σ v = false <;> simp [h1, h2, huv, huv.symm]
  rw [h4]; simp only [hpt, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]

private lemma abs_sum_signedNormAdjMatrix_le_four_mul {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℤˣ) {α : ℝ} (hα : 0 ≤ α)
    (hdisj : ∀ S T : Finset V, Disjoint S T →
      |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤ α * Real.sqrt (S.card * T.card))
    (S T : Finset V) :
    |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤ (4 * α) * Real.sqrt (S.card * T.card) := by
  classical
  let U : Finset V := S ∪ T
  let Sσ : (U → Bool) → Finset V := fun σ ↦ S.filter fun u ↦ ∃ hu : u ∈ U, σ ⟨u, hu⟩ = true
  let Tσ : (U → Bool) → Finset V := fun σ ↦ T.filter fun v ↦ ∃ hv : v ∈ U, σ ⟨v, hv⟩ = false
  have hdisj_σ : ∀ σ : U → Bool, Disjoint (Sσ σ) (Tσ σ) := fun σ ↦
    Finset.disjoint_left.mpr fun x hxS hxT ↦ by
      obtain ⟨_, hu, htrue⟩ := Finset.mem_filter.mp hxS
      obtain ⟨_, hv, hfalse⟩ := Finset.mem_filter.mp hxT
      rw [(Subtype.ext rfl : (⟨x, hu⟩ : U) = ⟨x, hv⟩), hfalse] at htrue
      exact Bool.false_ne_true htrue
  have hsum_id : (2 : ℝ) ^ U.card * ∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v =
      4 * ∑ σ : U → Bool, ∑ u ∈ Sσ σ, ∑ v ∈ Tσ σ, signedNormAdjMatrix G f u v := by
    have hterm : ∀ σ : U → Bool,
        ∑ u ∈ Sσ σ, ∑ v ∈ Tσ σ, signedNormAdjMatrix G f u v =
          ∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v *
            (if ∃ hu : u ∈ U, ∃ hv : v ∈ U, σ ⟨u, hu⟩ = true ∧ σ ⟨v, hv⟩ = false then
              (1 : ℝ) else 0) := fun σ ↦ by
      simp only [Sσ, Tσ, Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      by_cases hu : ∃ hu : u ∈ U, σ ⟨u, hu⟩ = true
      · simp only [hu, ↓reduceIte]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        by_cases hv : ∃ hv : v ∈ U, σ ⟨v, hv⟩ = false <;> simp [hu, hv]
      · simp [hu]
    simp_rw [hterm]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u huS ↦ ?_
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hvT ↦ ?_
    rw [← Finset.mul_sum]
    by_cases huv : u = v
    · subst huv; simp
    · have huU : u ∈ U := Finset.mem_union_left T huS
      have hvU : v ∈ U := Finset.mem_union_right S hvT
      have h4 := four_mul_sum_bipartition_eq
        (show (⟨u, huU⟩ : U) ≠ ⟨v, hvU⟩ from fun h ↦ huv (Subtype.ext_iff.mp h))
      rw [Fintype.card_coe] at h4
      have hcond : ∀ σ : U → Bool,
          (∃ hu : u ∈ U, ∃ hv : v ∈ U, σ ⟨u, hu⟩ = true ∧ σ ⟨v, hv⟩ = false) ↔
            σ ⟨u, huU⟩ = true ∧ σ ⟨v, hvU⟩ = false := fun _ ↦
        ⟨fun ⟨_, _, h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨huU, hvU, h1, h2⟩⟩
      simp_rw [hcond]
      calc (2 : ℝ) ^ U.card * signedNormAdjMatrix G f u v
          = signedNormAdjMatrix G f u v * (2 : ℝ) ^ U.card := mul_comm _ _
        _ = signedNormAdjMatrix G f u v *
              (4 * ∑ σ : U → Bool, if σ ⟨u, huU⟩ = true ∧ σ ⟨v, hvU⟩ = false then 1 else 0) := by
            rw [h4]
        _ = 4 * (signedNormAdjMatrix G f u v *
              ∑ σ : U → Bool, if σ ⟨u, huU⟩ = true ∧ σ ⟨v, hvU⟩ = false then 1 else 0) := by ring
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ U.card := pow_pos zero_lt_two _
  have habs_mul : (2 : ℝ) ^ U.card * |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤
      (2 : ℝ) ^ U.card * ((4 * α) * Real.sqrt (S.card * T.card)) := by
    conv_lhs => rw [← abs_of_pos h2pos]
    rw [← abs_mul, hsum_id, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc 4 * |∑ σ : U → Bool, ∑ u ∈ Sσ σ, ∑ v ∈ Tσ σ, signedNormAdjMatrix G f u v|
        ≤ 4 * ∑ σ : U → Bool, |∑ u ∈ Sσ σ, ∑ v ∈ Tσ σ, signedNormAdjMatrix G f u v| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
      _ ≤ 4 * ∑ _σ : U → Bool, α * Real.sqrt (S.card * T.card) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ ↦
            (hdisj (Sσ σ) (Tσ σ) (hdisj_σ σ)).trans (mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (mul_le_mul (Nat.cast_le.mpr (Finset.card_filter_le _ _))
                (Nat.cast_le.mpr (Finset.card_filter_le _ _))
                (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hα)) (by norm_num)
      _ = (2 : ℝ) ^ U.card * ((4 * α) * Real.sqrt (S.card * T.card)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; ring
  exact le_of_mul_le_mul_left habs_mul h2pos

private lemma sum_filter_lt_fin_sub {m : ℕ} (f : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ (k : ℕ) < (j : ℕ)),
      (f k.succ - f k.castSucc)) = f j - f 0 := by
  let f' : ℕ → ℝ := fun n ↦ if hn : n < m + 1 then f ⟨n, hn⟩ else 0
  have h1 : (∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ (k : ℕ) < (j : ℕ)),
      (f k.succ - f k.castSucc)) = ∑ n ∈ Finset.range (j : ℕ), (f' (n + 1) - f' n) :=
    Finset.sum_bij (fun k _ ↦ (k : ℕ))
      (fun k hk ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
      (fun _ _ _ _ h ↦ Fin.ext h)
      (fun n hn ↦ ⟨⟨n, Nat.lt_of_lt_of_le (Finset.mem_range.mp hn)
        (Nat.le_of_lt_succ j.isLt)⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.mem_range.mp hn⟩, rfl⟩)
      (fun k _ ↦ by
        simp only [f', Nat.succ_lt_succ k.isLt, Nat.lt_succ_of_lt k.isLt, ↓reduceDIte]; rfl)
  rw [h1, Finset.sum_range_sub f' (j : ℕ)]
  simp only [f', j.isLt, ↓reduceDIte, Nat.zero_lt_succ]; rfl

private lemma abs_sum_mul_le_of_le {V : Type*} (S : Finset V) (g a : V → ℝ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : ∀ u ∈ S, 0 ≤ a u ∧ a u ≤ A)
    (hg : ∀ S' ⊆ S, |∑ u ∈ S', g u| ≤ C * Real.sqrt S'.card) :
    |∑ u ∈ S, g u * a u| ≤ A * C * Real.sqrt S.card := by
  classical
  let P : Finset ℝ := insert 0 (S.image a)
  have h0P : (0 : ℝ) ∈ P := Finset.mem_insert_self 0 _
  let m : ℕ := P.card - 1
  have hm : P.card = m + 1 := (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨0, h0P⟩)).symm
  let f : Fin (m + 1) ↪o ℝ := P.orderEmbOfFin hm
  have hrange : Set.range f = (P : Set ℝ) := P.range_orderEmbOfFin hm
  have hf_nn : ∀ j : Fin (m + 1), 0 ≤ f j := fun j ↦ by
    rcases Finset.mem_insert.mp (P.orderEmbOfFin_mem hm j) with h0 | him
    · exact h0.symm ▸ le_rfl
    · obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp him; rw [← hu_eq]; exact (ha u hu).1
  have hf_le_A : ∀ j : Fin (m + 1), f j ≤ A := fun j ↦ by
    rcases Finset.mem_insert.mp (P.orderEmbOfFin_mem hm j) with h0 | him
    · exact h0.symm ▸ hA
    · obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp him; rw [← hu_eq]; exact (ha u hu).2
  have hf0 : f 0 = 0 := by
    obtain ⟨j₀, hj₀⟩ := hrange.symm ▸ Finset.mem_coe.mpr h0P
    exact le_antisymm (hj₀ ▸ f.monotone (Fin.zero_le j₀)) (hf_nn 0)
  have ha_eq : ∀ u ∈ S,
      a u = ∑ k : Fin m, (f k.succ - f k.castSucc) * if f k.succ ≤ a u then (1 : ℝ) else 0 := by
    intro u hu
    obtain ⟨j, hj⟩ := hrange.symm ▸
      Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hu))
    have hfilt : (Finset.univ.filter fun k : Fin m ↦ f k.succ ≤ a u) =
        Finset.univ.filter fun k : Fin m ↦ (k : ℕ) < (j : ℕ) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hj, f.le_iff_le]
      exact Nat.succ_le_iff
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, hfilt, sum_filter_lt_fin_sub f j, hj, hf0, sub_zero]
  let Sk : Fin m → Finset V := fun k ↦ S.filter fun u ↦ f k.succ ≤ a u
  have hsum_split :
      ∑ u ∈ S, g u * a u = ∑ k : Fin m, (f k.succ - f k.castSucc) * ∑ u ∈ Sk k, g u := by
    calc ∑ u ∈ S, g u * a u
        = ∑ u ∈ S, ∑ k : Fin m,
            g u * ((f k.succ - f k.castSucc) * if f k.succ ≤ a u then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun u hu ↦ by conv_lhs => rw [ha_eq u hu]; rw [Finset.mul_sum]
      _ = ∑ k : Fin m, (f k.succ - f k.castSucc) * ∑ u ∈ Sk k, g u := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.mul_sum]; simp only [Sk, Finset.sum_filter]
          exact Finset.sum_congr rfl fun u _ ↦ by split_ifs <;> ring
  have hdiff_nn : ∀ k : Fin m, 0 ≤ f k.succ - f k.castSucc := fun k ↦
    sub_nonneg.mpr (f.monotone (Fin.castSucc_le_succ k))
  have hsum_diff_le : ∑ k : Fin m, (f k.succ - f k.castSucc) ≤ A := by
    have hfilt : (Finset.univ.filter fun k : Fin m ↦ (k : ℕ) < (⟨m, Nat.lt_succ_self m⟩ :
        Fin (m + 1)).val) = Finset.univ := by ext k; simp
    have hsub := sum_filter_lt_fin_sub f ⟨m, Nat.lt_succ_self m⟩
    rw [hfilt, hf0, sub_zero] at hsub
    exact hsub.le.trans (hf_le_A ⟨m, Nat.lt_succ_self m⟩)
  rw [hsum_split]
  calc |∑ k : Fin m, (f k.succ - f k.castSucc) * ∑ u ∈ Sk k, g u|
      ≤ ∑ k : Fin m, (f k.succ - f k.castSucc) * |∑ u ∈ Sk k, g u| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ by
          rw [abs_mul, abs_of_nonneg (hdiff_nn k)])
    _ ≤ ∑ k : Fin m, (f k.succ - f k.castSucc) * (C * Real.sqrt S.card) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left
          ((hg (Sk k) (Finset.filter_subset _ _)).trans (mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Finset.card_filter_le _ _))) hC)) (hdiff_nn k)
    _ = (∑ k : Fin m, (f k.succ - f k.castSucc)) * (C * Real.sqrt S.card) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ A * C * Real.sqrt S.card :=
        (mul_le_mul_of_nonneg_right hsum_diff_le (mul_nonneg hC (Real.sqrt_nonneg _))).trans_eq
          (by ring)

private lemma abs_sum_mul_mul_le {V : Type*} (M : V → V → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hrect : ∀ S' T' : Finset V, |∑ u ∈ S', ∑ v ∈ T', M u v| ≤ β * Real.sqrt (S'.card * T'.card))
    (S T : Finset V) (a b : V → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ u ∈ S, 0 ≤ a u ∧ a u ≤ A) (hb : ∀ v ∈ T, 0 ≤ b v ∧ b v ≤ B) :
    |∑ u ∈ S, ∑ v ∈ T, M u v * a u * b v| ≤ β * A * B * Real.sqrt (S.card * T.card) := by
  have h1 : ∀ T' : Finset V,
      |∑ u ∈ S, (∑ v ∈ T', M u v) * a u| ≤ (β * A * Real.sqrt S.card) * Real.sqrt T'.card :=
    fun T' ↦ by
      have hstep := abs_sum_mul_le_of_le S (fun u ↦ ∑ v ∈ T', M u v) a hA
        (mul_nonneg hβ (Real.sqrt_nonneg _)) ha fun S' _ ↦ by
          simpa [Real.sqrt_mul (Nat.cast_nonneg _), mul_assoc, mul_comm] using hrect S' T'
      linarith
  have h2 := abs_sum_mul_le_of_le T (fun v ↦ ∑ u ∈ S, M u v * a u) b hB
    (mul_nonneg (mul_nonneg hβ hA) (Real.sqrt_nonneg _)) hb fun T' _ ↦ by
      have hswap : ∑ v ∈ T', ∑ u ∈ S, M u v * a u = ∑ u ∈ S, (∑ v ∈ T', M u v) * a u := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun u _ ↦ (Finset.sum_mul _ _ _).symm
      exact hswap ▸ h1 T'
  have hswap2 : ∑ u ∈ S, ∑ v ∈ T, M u v * a u * b v = ∑ v ∈ T, (∑ u ∈ S, M u v * a u) * b v := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun v _ ↦ (Finset.sum_mul _ _ _).symm
  rw [hswap2, Real.sqrt_mul (Nat.cast_nonneg _)]
  exact h2.trans_eq (by ring)

private lemma sum_Icc_filter_lt_zpow_le (K L i : ℕ) :
    (∑ j ∈ Finset.Icc 1 L,
      if i + K < j then (2 : ℝ) ^ (-((j - i : ℕ) : ℤ)) else 0) ≤
        (2 : ℝ) ^ (-(K : ℤ)) := by
  rw [← Finset.sum_filter]
  have hle : (∑ j ∈ (Finset.Icc 1 L).filter (fun j ↦ i + K < j),
      (2 : ℝ) ^ (-((j - i : ℕ) : ℤ))) ≤
      ∑ m ∈ Finset.Ico (K + 1) (L + 1), (2 : ℝ) ^ (-(m : ℤ)) := by
    refine Finset.sum_le_sum_of_injOn (fun j ↦ j - i)
      (fun j₁ hj₁ j₂ hj₂ heq ↦ by
        have h1' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
        have h2' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
        dsimp only at heq
        omega)
      (Finset.image_subset_iff.mpr fun j hj ↦ by
        obtain ⟨hj_mem, hij⟩ := Finset.mem_filter.mp hj
        have hjL : j ≤ L := (Finset.mem_Icc.mp hj_mem).2
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ zpow_nonneg zero_le_two _)
  refine hle.trans ?_
  by_cases hKL : K + 1 ≤ L + 1
  · rw [Finset.sum_Ico_eq_sum_range]
    let g : ℕ → ℝ := fun t ↦ -(2 : ℝ) ^ (-((K + t : ℕ) : ℤ))
    have hterm : ∀ t : ℕ, (2 : ℝ) ^ (-((K + 1 + t : ℕ) : ℤ)) = g (t + 1) - g t := fun t ↦ by
      simp only [g]
      have h1 : -((K + 1 + t : ℕ) : ℤ) = -((K + t : ℕ) : ℤ) + -1 := by omega
      have h2 : -((K + (t + 1) : ℕ) : ℤ) = -((K + t : ℕ) : ℤ) + -1 := by omega
      rw [h1, h2, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num; ring
    simp_rw [hterm, Finset.sum_range_sub g (L + 1 - (K + 1))]
    simp only [g, add_zero, sub_neg_eq_add]
    linarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (-((K + (L + 1 - (K + 1)) : ℕ) : ℤ))]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact zpow_nonneg zero_le_two _

private lemma sum_shift_Icc_mul_le (k L : ℕ) (p q : ℕ → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ j, 0 ≤ q j)
    (hp_sum : ∑ i ∈ Finset.Icc 1 L, p i ^ 2 ≤ 1)
    (hq_sum : ∑ j ∈ Finset.Icc 1 L, q j ^ 2 ≤ 1) :
    (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if j = i + k then p i * q j else 0) ≤ 1 := by
  let q' : ℕ → ℝ := fun i ↦ if i + k ∈ Finset.Icc 1 L then q (i + k) else 0
  have hterm : ∀ i ∈ Finset.Icc 1 L,
      (∑ j ∈ Finset.Icc 1 L, if j = i + k then p i * q j else 0) = p i * q' i := fun i _ ↦ by
    dsimp only [q']; split_ifs with hik
    · rw [Finset.sum_eq_single (i + k)]
      · simp
      · intro j _ hj; split_ifs with h
        · exact absurd h hj
        · rfl
      · intro hmem; exact absurd hik hmem
    · rw [mul_zero]; refine Finset.sum_eq_zero fun j hj ↦ ?_
      split_ifs with h
      · exact absurd (h ▸ hj) hik
      · rfl
  rw [Finset.sum_congr rfl hterm]
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 L) p q'
  have hq' : ∑ i ∈ Finset.Icc 1 L, q' i ^ 2 ≤ 1 := by
    have hterm_q : ∀ i ∈ Finset.Icc 1 L,
        q' i ^ 2 = ∑ j ∈ Finset.Icc 1 L, if j = i + k then q j ^ 2 else 0 := fun i _ ↦ by
      dsimp only [q']; split_ifs with hik
      · rw [Finset.sum_eq_single (i + k)]
        · simp
        · intro j _ hj; split_ifs with h
          · exact absurd h hj
          · rfl
        · intro hmem; exact absurd hik hmem
      · rw [sq_eq_zero_iff.mpr rfl]; refine (Finset.sum_eq_zero fun j hj ↦ ?_).symm
        split_ifs with h
        · exact absurd (h ▸ hj) hik
        · rfl
    rw [Finset.sum_congr rfl hterm_q]; rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun j _ ↦ ?_).trans hq_sum
    by_cases hjk : j - k ∈ Finset.Icc 1 L ∧ j = (j - k) + k
    · have hsingle : (∑ i ∈ Finset.Icc 1 L, if j = i + k then q j ^ 2 else 0) = q j ^ 2 := by
        rw [Finset.sum_eq_single (j - k)]
        · exact ite_eq_left_iff.mpr fun h ↦ absurd hjk.2 h
        · intro i _ hik; split_ifs with heq
          · exact absurd (by omega) hik
          · rfl
        · intro hmem; exact absurd hjk.1 hmem
      exact hsingle.le
    · have hzero : (∑ i ∈ Finset.Icc 1 L, if j = i + k then q j ^ 2 else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_; split_ifs with heq
        · have hsub : j - k = i := by omega
          exact absurd ⟨hsub.symm ▸ hi, by omega⟩ hjk
        · rfl
      rw [hzero]; exact sq_nonneg _
  have hmul1 : (∑ i ∈ Finset.Icc 1 L, p i * q' i) ^ 2 ≤ 1 :=
    (hsq.trans
      (mul_le_mul hp_sum hq' (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) zero_le_one)).trans_eq
      (mul_one 1)
  have hnn : 0 ≤ ∑ i ∈ Finset.Icc 1 L, p i * q' i :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nn i) (by dsimp [q']; split_ifs <;> simp [hq_nn])
  nlinarith

private lemma sum_abs_signedNormAdjMatrix_row_le {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 1 ≤ d)
    (hreg : G.IsRegularOfDegree d) (f : Sym2 V → ℤˣ) (u : V) :
    ∑ v : V, |signedNormAdjMatrix G f u v| ≤ 1 := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hterm : ∀ v : V, |signedNormAdjMatrix G f u v| =
      if v ∈ G.neighborFinset u then (1 : ℝ) / d else 0 := fun v ↦ by
    rw [signedNormAdjMatrix_apply_of_regular hreg f u v]
    simp only [_root_.SimpleGraph.mem_neighborFinset]
    split_ifs with hadj
    · rw [abs_div, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      rcases Int.units_eq_one_or (f s(u, v)) with h | h <;> simp [h]
    · simp
  simp_rw [hterm]
  rw [Finset.sum_ite_mem Finset.univ (G.neighborFinset u) (fun _ ↦ (1 : ℝ) / d),
    Finset.univ_inter, Finset.sum_const, G.card_neighborFinset_eq_degree, hreg.degree_eq u,
    nsmul_eq_mul, mul_one_div_cancel hd_pos.ne']

private lemma dyadicBucket_disjoint {V : Type*} [Fintype V] (a : V → ℝ) :
    ∀ i₁ i₂ : ℕ, i₁ ≠ i₂ →
      Disjoint
        (Finset.univ.filter fun u ↦
          (2 : ℝ) ^ (-(i₁ : ℤ)) < a u ∧ a u ≤ (2 : ℝ) ^ (-((i₁ - 1 : ℕ) : ℤ)))
        (Finset.univ.filter fun u ↦
          (2 : ℝ) ^ (-(i₂ : ℤ)) < a u ∧ a u ≤ (2 : ℝ) ^ (-((i₂ - 1 : ℕ) : ℤ))) :=
  fun i₁ i₂ hne12 ↦ Finset.disjoint_left.mpr fun u hu1 hu2 ↦ by
    obtain ⟨_, hlt1, hle1⟩ := Finset.mem_filter.mp hu1
    obtain ⟨_, hlt2, hle2⟩ := Finset.mem_filter.mp hu2
    rcases lt_or_gt_of_ne hne12 with h12 | h21
    · have hle_pow : (2 : ℝ) ^ (-((i₂ - 1 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-(i₁ : ℤ)) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      linarith
    · have hle_pow : (2 : ℝ) ^ (-((i₁ - 1 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-(i₂ : ℤ)) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      linarith

private lemma dyadicBucket_cover {V : Type*} [Fintype V] (a : V → ℝ) (ha1 : ∀ u, a u ≤ 1)
    (L : ℕ) (u : V) :
    u ∈ (Finset.univ.filter fun u ↦ a u ≤ (2 : ℝ) ^ (-(L : ℤ))) ∨
      ∃ i ∈ Finset.Icc 1 L,
        u ∈ Finset.univ.filter fun u ↦
          (2 : ℝ) ^ (-(i : ℤ)) < a u ∧ a u ≤ (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ)) := by
  classical
  by_cases hut : a u ≤ (2 : ℝ) ^ (-(L : ℤ))
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hut⟩)
  · push Not at hut
    have hex : ∃ k : ℕ, (2 : ℝ) ^ (-(k : ℤ)) < a u := ⟨L, hut⟩
    let i := Nat.find hex
    have hi_lt : (2 : ℝ) ^ (-(i : ℤ)) < a u := Nat.find_spec hex
    have hi_pos : 1 ≤ i := by
      by_contra hi0
      have hi_eq0 : i = 0 := by omega
      rw [hi_eq0, Nat.cast_zero, neg_zero, zpow_zero] at hi_lt; linarith [ha1 u]
    have hi_le : a u ≤ (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ)) := by
      by_contra hgt; push Not at hgt
      exact Nat.find_min hex (show i - 1 < i by omega) hgt
    exact Or.inr ⟨i, Finset.mem_Icc.mpr ⟨hi_pos, Nat.find_le hut⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ u, hi_lt, hi_le⟩⟩

private lemma sum_univ_eq_tail_add_Icc {V : Type*} [Fintype V]
    (a : V → ℝ) (ha1 : ∀ u, a u ≤ 1) (L : ℕ) (F : V → ℝ) :
    let Stail := Finset.univ.filter fun u ↦ a u ≤ (2 : ℝ) ^ (-(L : ℤ))
    let S : ℕ → Finset V := fun i ↦
      Finset.univ.filter fun u ↦ (2 : ℝ) ^ (-(i : ℤ)) < a u ∧ a u ≤ (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ))
    ∑ u : V, F u = (∑ u ∈ Stail, F u) + ∑ i ∈ Finset.Icc 1 L, ∑ u ∈ S i, F u := by
  classical
  intro Stail S
  have hpt : ∀ u : V,
      F u = (if u ∈ Stail then F u else 0) +
        ∑ i ∈ Finset.Icc 1 L, if u ∈ S i then F u else 0 := fun u ↦ by
    rcases dyadicBucket_cover a ha1 L u with hut | ⟨i, hi, huS⟩
    · have hzero : ∑ k ∈ Finset.Icc 1 L, (if u ∈ S k then F u else 0) = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_; split_ifs with huSk
        · have hpow : (2 : ℝ) ^ (-(L : ℤ)) ≤ (2 : ℝ) ^ (-(k : ℤ)) :=
            zpow_le_zpow_right₀ one_le_two (by have := (Finset.mem_Icc.mp hk).2; omega)
          dsimp only [Stail, S] at hut huSk
          linarith [(Finset.mem_filter.mp hut).2, (Finset.mem_filter.mp huSk).2.1]
        · rfl
      rw [ite_eq_left_iff.mpr fun h ↦ absurd hut h, hzero, add_zero]
    · have hnot : u ∉ Stail := fun hut ↦ by
        have hpow : (2 : ℝ) ^ (-(L : ℤ)) ≤ (2 : ℝ) ^ (-(i : ℤ)) :=
          zpow_le_zpow_right₀ one_le_two (by have := (Finset.mem_Icc.mp hi).2; omega)
        dsimp only [Stail, S] at hut huS
        linarith [(Finset.mem_filter.mp hut).2, (Finset.mem_filter.mp huS).2.1]
      have hsingle : (∑ k ∈ Finset.Icc 1 L, if u ∈ S k then F u else 0) = F u := by
        rw [Finset.sum_eq_single i]
        · exact ite_eq_left_iff.mpr fun h ↦ absurd huS h
        · intro k _ hki; split_ifs with huSk
          · dsimp only [S] at huSk huS
            exact False.elim (Finset.disjoint_left.mp (dyadicBucket_disjoint a k i hki) huSk huS)
          · rfl
        · exact fun hmem ↦ absurd hi hmem
      rw [ite_eq_right_iff.mpr fun h ↦ absurd h hnot, zero_add, hsingle]
  have hsum1 : ∑ u : V, F u =
      (∑ u : V, if u ∈ Stail then F u else 0) +
      ∑ u : V, ∑ i ∈ Finset.Icc 1 L, if u ∈ S i then F u else 0 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun u _ ↦ hpt u
  rw [hsum1, Finset.sum_ite_mem Finset.univ Stail F, Finset.univ_inter]
  congr 1; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Finset.sum_ite_mem Finset.univ (S i) F, Finset.univ_inter]

private lemma dyadic_l2_sum_le {V : Type*} [Fintype V] (a : V → ℝ)
    (ha1 : ∀ u, a u ≤ 1) (ha_norm : ∑ u : V, a u ^ 2 = 1) (L : ℕ) :
    let S : ℕ → Finset V := fun i ↦
      Finset.univ.filter fun u ↦
        (2 : ℝ) ^ (-(i : ℤ)) < a u ∧ a u ≤ (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ))
    ∑ i ∈ Finset.Icc 1 L, ((2 : ℝ) ^ (-(i : ℤ)) * Real.sqrt (S i).card) ^ 2 ≤ 1 := by
  classical
  intro S
  have hterm : ∀ i : ℕ,
      ((2 : ℝ) ^ (-(i : ℤ)) * Real.sqrt (S i).card) ^ 2 ≤ ∑ u ∈ S i, a u ^ 2 := fun i ↦ by
    have hsq : ((2 : ℝ) ^ (-(i : ℤ)) * Real.sqrt (S i).card) ^ 2 =
        (S i).card * ((2 : ℝ) ^ (-(i : ℤ))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_comm]
    rw [hsq, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun u hu ↦
      pow_le_pow_left₀ (zpow_nonneg zero_le_two _) (Finset.mem_filter.mp hu).2.1.le 2
  have hpart := sum_univ_eq_tail_add_Icc a ha1 L (fun u ↦ a u ^ 2)
  have htail_nn : 0 ≤ ∑ u ∈ Finset.univ.filter (fun u ↦ a u ≤ (2 : ℝ) ^ (-(L : ℤ))), a u ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  calc ∑ i ∈ Finset.Icc 1 L, ((2 : ℝ) ^ (-(i : ℤ)) * Real.sqrt (S i).card) ^ 2
      ≤ ∑ i ∈ Finset.Icc 1 L, ∑ u ∈ S i, a u ^ 2 := Finset.sum_le_sum fun i _ ↦ hterm i
    _ ≤ ∑ u : V, a u ^ 2 := by linarith
    _ = 1 := ha_norm

private lemma dyadic_bucket_row_bound {V : Type*} [Fintype V] (M : V → V → ℝ)
    (hrow_one : ∀ u : V, ∑ v : V, |M u v| ≤ 1) (a b : V → ℝ)
    (ha_nn : ∀ u, 0 ≤ a u) (hb_nn : ∀ v, 0 ≤ b v)
    (Si Tj : Finset V) {i j : ℕ} (hi1 : 1 ≤ i) (hj1 : 1 ≤ j) (hij : i ≤ j)
    (haSi : ∀ u ∈ Si, a u ≤ (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ)))
    (hbTj : ∀ v ∈ Tj, b v ≤ (2 : ℝ) ^ (-((j - 1 : ℕ) : ℤ))) :
    |∑ u ∈ Si, ∑ v ∈ Tj, M u v * a u * b v| ≤
      4 * ((2 : ℝ) ^ (-(i : ℤ)) * Real.sqrt Si.card) ^ 2 * (2 : ℝ) ^ (-((j - i : ℕ) : ℤ)) := by
  have hpow_i : (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ)) = 2 * (2 : ℝ) ^ (-(i : ℤ)) := by
    have hsub : -((i - 1 : ℕ) : ℤ) = 1 + -(i : ℤ) := by omega
    rw [hsub, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hpow_j : (2 : ℝ) ^ (-((j - 1 : ℕ) : ℤ)) = 2 * (2 : ℝ) ^ (-(j : ℤ)) := by
    have hsub : -((j - 1 : ℕ) : ℤ) = 1 + -(j : ℤ) := by omega
    rw [hsub, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hle_sum :
      |∑ u ∈ Si, ∑ v ∈ Tj, M u v * a u * b v| ≤
        4 * (2 : ℝ) ^ (-(i : ℤ)) * (2 : ℝ) ^ (-(j : ℤ)) * Si.card := by
    calc |∑ u ∈ Si, ∑ v ∈ Tj, M u v * a u * b v|
        ≤ ∑ u ∈ Si, ∑ v ∈ Tj, |M u v * a u * b v| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ u ∈ Si, ∑ v ∈ Tj,
            |M u v| * (2 * (2 : ℝ) ^ (-(i : ℤ))) * (2 * (2 : ℝ) ^ (-(j : ℤ))) := by
          refine Finset.sum_le_sum fun u hu ↦ Finset.sum_le_sum fun v hv ↦ ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (ha_nn u), abs_of_nonneg (hb_nn v)]
          exact mul_le_mul (mul_le_mul_of_nonneg_left ((haSi u hu).trans_eq hpow_i) (abs_nonneg _))
            ((hbTj v hv).trans_eq hpow_j) (hb_nn v) (by positivity)
      _ = 4 * (2 : ℝ) ^ (-(i : ℤ)) * (2 : ℝ) ^ (-(j : ℤ)) * ∑ u ∈ Si, ∑ v ∈ Tj, |M u v| := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ ↦ ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ 4 * (2 : ℝ) ^ (-(i : ℤ)) * (2 : ℝ) ^ (-(j : ℤ)) * Si.card :=
          mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun u _ ↦
            Finset.sum_le_univ_sum_of_nonneg fun v ↦ abs_nonneg _).trans
            ((Finset.sum_le_sum fun u _ ↦ hrow_one u).trans_eq (by simp))) (by positivity)
  refine hle_sum.trans ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hsub : -(i : ℤ) + -(j : ℤ) = (-(i : ℤ) + -(i : ℤ)) + -((j - i : ℕ) : ℤ) := by
    rw [Int.ofNat_sub hij]; omega
  have hzp : (2 : ℝ) ^ (-(i : ℤ)) * (2 : ℝ) ^ (-(j : ℤ)) =
      ((2 : ℝ) ^ (-(i : ℤ))) ^ 2 * (2 : ℝ) ^ (-((j - i : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hsub,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sq]
  rw [mul_assoc 4 ((2 : ℝ) ^ (-(i : ℤ))) ((2 : ℝ) ^ (-(j : ℤ))), hzp]
  exact le_of_eq (by ring)

private lemma dyadic_diag_band_bound (k₀ K L : ℕ) {α : ℝ} (hα : 0 ≤ α)
    (p q : ℕ → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hq_nn : ∀ j, 0 ≤ q j)
    (hp_sum : ∑ i ∈ Finset.Icc 1 L, p i ^ 2 ≤ 1)
    (hq_sum : ∑ j ∈ Finset.Icc 1 L, q j ^ 2 ≤ 1)
    (R : ℕ → ℕ → ℝ) (hR : ∀ i ∈ Finset.Icc 1 L, ∀ j ∈ Finset.Icc 1 L, R i j ≤ 16 * α * p i * q j) :
    (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
      ∑ k ∈ Finset.Icc k₀ K, if j = i + k then R i j else 0) ≤
        16 * α * ((Finset.Icc k₀ K).card : ℝ) := by
  have hswap :
      (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
        ∑ k ∈ Finset.Icc k₀ K, if j = i + k then R i j else 0) =
          ∑ k ∈ Finset.Icc k₀ K, ∑ i ∈ Finset.Icc 1 L,
            ∑ j ∈ Finset.Icc 1 L, if j = i + k then R i j else 0 :=
    (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans Finset.sum_comm
  rw [hswap]
  have hshift : ∀ k ∈ Finset.Icc k₀ K,
      (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if j = i + k then R i j else 0) ≤ 16 * α :=
    fun k _ ↦ by
      calc (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if j = i + k then R i j else 0)
          ≤ ∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
              if j = i + k then 16 * α * (p i * q j) else 0 :=
            Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ by
              split_ifs
              · exact (hR i hi j hj).trans_eq (by ring)
              · exact le_rfl
        _ = 16 * α * ∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
              if j = i + k then p i * q j else 0 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring
        _ ≤ 16 * α * 1 := mul_le_mul_of_nonneg_left
            (sum_shift_Icc_mul_le k L p q hp_nn hq_nn hp_sum hq_sum) (by positivity)
        _ = 16 * α := mul_one _
  exact (Finset.sum_le_sum hshift).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul, mul_comm])

private lemma dyadic_offdiag_bound (K L : ℕ) {α : ℝ} (hα : 0 ≤ α)
    (h2K : (2 : ℝ) ^ (-(K : ℤ)) ≤ α) (p : ℕ → ℝ)
    (hp_sum : ∑ i ∈ Finset.Icc 1 L, p i ^ 2 ≤ 1) (R : ℕ → ℕ → ℝ)
    (hR_row : ∀ i ∈ Finset.Icc 1 L, ∀ j ∈ Finset.Icc 1 L, i ≤ j →
      R i j ≤ 4 * p i ^ 2 * (2 : ℝ) ^ (-((j - i : ℕ) : ℤ))) :
    (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if i + K < j then R i j else 0) ≤ 4 * α := by
  calc (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if i + K < j then R i j else 0)
      ≤ ∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
          if i + K < j then 4 * p i ^ 2 * (2 : ℝ) ^ (-((j - i : ℕ) : ℤ)) else 0 :=
        Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ by
          split_ifs with hlt
          · exact hR_row i hi j hj (by omega)
          · exact le_rfl
    _ = ∑ i ∈ Finset.Icc 1 L, 4 * p i ^ 2 *
          ∑ j ∈ Finset.Icc 1 L, if i + K < j then (2 : ℝ) ^ (-((j - i : ℕ) : ℤ)) else 0 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring
    _ ≤ ∑ i ∈ Finset.Icc 1 L, 4 * p i ^ 2 * α :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
          ((sum_Icc_filter_lt_zpow_le K L i).trans h2K) (by positivity)
    _ = 4 * α * ∑ i ∈ Finset.Icc 1 L, p i ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ 4 * α := (mul_le_mul_of_nonneg_left hp_sum (by positivity)).trans_eq (mul_one _)

private lemma quad_nonneg_unit_le_of_rect {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 1 ≤ d)
    (hreg : G.IsRegularOfDegree d) (f : Sym2 V → ℤˣ) {α : ℝ} (hα_pos : 0 < α)
    (hα_le : α ≤ 1 / 2)
    (hrect : ∀ S T : Finset V,
      |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤
        (4 * α) * Real.sqrt (S.card * T.card))
    (a b : V → ℝ) (ha_nn : ∀ u, 0 ≤ a u) (hb_nn : ∀ v, 0 ≤ b v)
    (ha_norm : ∑ u : V, a u ^ 2 = 1) (hb_norm : ∑ v : V, b v ^ 2 = 1) :
    |∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * a u * b v| ≤
      64 * α * (1 + Real.logb 2 (1 / α)) := by
  classical
  have hne : Nonempty V := by
    by_contra hemp; rw [not_nonempty_iff] at hemp; simp at ha_norm
  have hn_pos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have ha_le1 : ∀ u : V, a u ≤ 1 := fun u ↦ by
    have hsq := ha_norm ▸ Finset.single_le_sum (fun w _ ↦ sq_nonneg (a w)) (Finset.mem_univ u)
    nlinarith [ha_nn u]
  have hb_le1 : ∀ v : V, b v ≤ 1 := fun v ↦ by
    have hsq := hb_norm ▸ Finset.single_le_sum (fun w _ ↦ sq_nonneg (b w)) (Finset.mem_univ v)
    nlinarith [hb_nn v]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (2 : ℝ) ^ (-(L : ℤ)) ≤ α / Fintype.card V := by
    obtain ⟨L, hL'⟩ := exists_pow_lt_of_lt_one (div_pos hα_pos hn_pos)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨L, hL'.le.trans_eq' ?_⟩
    rw [one_div, inv_pow, ← zpow_natCast, ← _root_.zpow_neg]
  let S : ℕ → Finset V := fun i ↦
    Finset.univ.filter fun u ↦ (2 : ℝ) ^ (-(i : ℤ)) < a u ∧ a u ≤ (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ))
  let Stail : Finset V := Finset.univ.filter fun u ↦ a u ≤ (2 : ℝ) ^ (-(L : ℤ))
  let T : ℕ → Finset V := fun j ↦
    Finset.univ.filter fun v ↦ (2 : ℝ) ^ (-(j : ℤ)) < b v ∧ b v ≤ (2 : ℝ) ^ (-((j - 1 : ℕ) : ℤ))
  let Ttail : Finset V := Finset.univ.filter fun v ↦ b v ≤ (2 : ℝ) ^ (-(L : ℤ))
  let Q : V → V → ℝ := fun u v ↦ signedNormAdjMatrix G f u v * a u * b v
  have hsplit_all :
      ∑ u : V, ∑ v : V, Q u v =
        (∑ u ∈ Stail, ∑ v : V, Q u v) +
        (∑ u ∈ Finset.univ \ Stail, ∑ v ∈ Ttail, Q u v) +
        ∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, ∑ u ∈ S i, ∑ v ∈ T j, Q u v := by
    have h1 := sum_univ_eq_tail_add_Icc a ha_le1 L (fun u ↦ ∑ v : V, Q u v)
    have h2 : ∑ i ∈ Finset.Icc 1 L, ∑ u ∈ S i, ∑ v : V, Q u v =
        (∑ i ∈ Finset.Icc 1 L, ∑ u ∈ S i, ∑ v ∈ Ttail, Q u v) +
        ∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, ∑ u ∈ S i, ∑ v ∈ T j, Q u v := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp_rw [sum_univ_eq_tail_add_Icc b hb_le1 L (fun v ↦ Q _ v), Finset.sum_add_distrib]
      congr 1; exact Finset.sum_comm
    have h4 := sum_univ_eq_tail_add_Icc a ha_le1 L (fun u ↦ ∑ v ∈ Ttail, Q u v)
    have h5 : ∑ u : V, ∑ v ∈ Ttail, Q u v =
        (∑ u ∈ Stail, ∑ v ∈ Ttail, Q u v) + ∑ u ∈ Finset.univ \ Stail, ∑ v ∈ Ttail, Q u v := by
      rw [← Finset.sum_sdiff (Finset.subset_univ Stail), add_comm]
    linarith
  have htail_bd : ∀ A' B' : Finset V, ∀ cA cB : ℝ,
      0 ≤ cA → 0 ≤ cB → cA * cB ≤ α / Fintype.card V →
      (∀ u ∈ A', 0 ≤ a u ∧ a u ≤ cA) → (∀ v ∈ B', 0 ≤ b v ∧ b v ≤ cB) →
      |∑ u ∈ A', ∑ v ∈ B', Q u v| ≤ 4 * α := fun A' B' cA cB hcA hcB hprod haA hbB ↦ by
    have hst := abs_sum_mul_mul_le (signedNormAdjMatrix G f) (by positivity) hrect A' B'
      a b hcA hcB haA hbB
    have hcard_le : Real.sqrt (A'.card * B'.card) ≤ Fintype.card V :=
      (Real.sqrt_le_sqrt (mul_le_mul (Nat.cast_le.mpr (Finset.card_le_univ A'))
        (Nat.cast_le.mpr (Finset.card_le_univ B')) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))).trans_eq (Real.sqrt_mul_self (Nat.cast_nonneg (Fintype.card V)))
    calc |∑ u ∈ A', ∑ v ∈ B', Q u v|
        ≤ 4 * α * cA * cB * Real.sqrt (A'.card * B'.card) := hst
      _ = 4 * α * (cA * cB) * Real.sqrt (A'.card * B'.card) := by ring
      _ ≤ 4 * α * (α / Fintype.card V) * Fintype.card V :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) hcard_le
            (Real.sqrt_nonneg _) (by positivity)
      _ = 4 * α * α := by field_simp [hn_pos.ne']
      _ ≤ 4 * α := (mul_le_mul_of_nonneg_left (hα_le.trans (by norm_num))
          (by positivity)).trans_eq (mul_one _)
  have htail1 := htail_bd Stail Finset.univ ((2 : ℝ) ^ (-(L : ℤ))) 1 (zpow_nonneg zero_le_two _)
    zero_le_one (by simpa using hL) (fun u hu ↦ ⟨ha_nn u, (Finset.mem_filter.mp hu).2⟩)
    (fun v _ ↦ ⟨hb_nn v, hb_le1 v⟩)
  have htail2 := htail_bd (Finset.univ \ Stail) Ttail 1 ((2 : ℝ) ^ (-(L : ℤ))) zero_le_one
    (zpow_nonneg zero_le_two _) (by simpa using hL) (fun u _ ↦ ⟨ha_nn u, ha_le1 u⟩)
    (fun v hv ↦ ⟨hb_nn v, (Finset.mem_filter.mp hv).2⟩)
  let p : ℕ → ℝ := fun i ↦ (2 : ℝ) ^ (-(i : ℤ)) * Real.sqrt (S i).card
  let q : ℕ → ℝ := fun j ↦ (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (T j).card
  have hp_nn : ∀ i, 0 ≤ p i := fun i ↦ mul_nonneg (zpow_nonneg zero_le_two _) (Real.sqrt_nonneg _)
  have hq_nn : ∀ j, 0 ≤ q j := fun j ↦ mul_nonneg (zpow_nonneg zero_le_two _) (Real.sqrt_nonneg _)
  have hp_sum : ∑ i ∈ Finset.Icc 1 L, p i ^ 2 ≤ 1 := dyadic_l2_sum_le a ha_le1 ha_norm L
  have hq_sum : ∑ j ∈ Finset.Icc 1 L, q j ^ 2 ≤ 1 := dyadic_l2_sum_le b hb_le1 hb_norm L
  let R : ℕ → ℕ → ℝ := fun i j ↦ |∑ u ∈ S i, ∑ v ∈ T j, Q u v|
  have hR_rect : ∀ i ∈ Finset.Icc 1 L, ∀ j ∈ Finset.Icc 1 L, R i j ≤ 16 * α * p i * q j := by
    intro i hi j hj
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpow_i : (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ)) = 2 * (2 : ℝ) ^ (-(i : ℤ)) := by
      have hsub : -((i - 1 : ℕ) : ℤ) = 1 + -(i : ℤ) := by omega
      rw [hsub, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    have hpow_j : (2 : ℝ) ^ (-((j - 1 : ℕ) : ℤ)) = 2 * (2 : ℝ) ^ (-(j : ℤ)) := by
      have hsub : -((j - 1 : ℕ) : ℤ) = 1 + -(j : ℤ) := by omega
      rw [hsub, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    have hst := abs_sum_mul_mul_le (signedNormAdjMatrix G f) (by positivity) hrect (S i) (T j)
      a b (zpow_nonneg zero_le_two _) (zpow_nonneg zero_le_two _)
      (fun u hu ↦ ⟨ha_nn u, (Finset.mem_filter.mp hu).2.2⟩)
      (fun v hv ↦ ⟨hb_nn v, (Finset.mem_filter.mp hv).2.2⟩)
    calc R i j
        ≤ 4 * α * (2 : ℝ) ^ (-((i - 1 : ℕ) : ℤ)) * (2 : ℝ) ^ (-((j - 1 : ℕ) : ℤ)) *
            Real.sqrt ((S i).card * (T j).card) := hst
      _ = 16 * α * p i * q j := by
          rw [hpow_i, hpow_j, Real.sqrt_mul (Nat.cast_nonneg _)]; dsimp only [p, q]; ring
  have hR_row : ∀ i ∈ Finset.Icc 1 L, ∀ j ∈ Finset.Icc 1 L, i ≤ j →
      R i j ≤ 4 * p i ^ 2 * (2 : ℝ) ^ (-((j - i : ℕ) : ℤ)) := fun i hi j hj hij ↦
    dyadic_bucket_row_bound (signedNormAdjMatrix G f)
      (sum_abs_signedNormAdjMatrix_row_le G hd hreg f) a b ha_nn hb_nn (S i) (T j)
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
      (fun u hu ↦ (Finset.mem_filter.mp hu).2.2) (fun v hv ↦ (Finset.mem_filter.mp hv).2.2)
  have hR_col : ∀ i ∈ Finset.Icc 1 L, ∀ j ∈ Finset.Icc 1 L, j ≤ i →
      R i j ≤ 4 * q j ^ 2 * (2 : ℝ) ^ (-((i - j : ℕ) : ℤ)) := fun i hi j hj hji ↦ by
    have hswap_R : R i j = |∑ v ∈ T j, ∑ u ∈ S i, signedNormAdjMatrix G f v u * b v * a u| := by
      dsimp only [R, Q]; rw [Finset.sum_comm]; congr 1
      exact Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun u _ ↦ by
        simp only [signedNormAdjMatrix_apply, G.adj_comm u v, Sym2.eq_swap,
          mul_comm (G.degree u : ℝ) (G.degree v)]; ring
    rw [hswap_R]
    exact dyadic_bucket_row_bound (signedNormAdjMatrix G f)
      (sum_abs_signedNormAdjMatrix_row_le G hd hreg f) b a hb_nn ha_nn (T j) (S i)
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hi).1 hji
      (fun v hv ↦ (Finset.mem_filter.mp hv).2.2) (fun u hu ↦ (Finset.mem_filter.mp hu).2.2)
  let K : ℕ := Nat.ceil (Real.logb 2 (1 / α))
  have hlog_nn : 0 ≤ Real.logb 2 (1 / α) :=
    (Real.le_logb_iff_rpow_le one_lt_two (one_div_pos.mpr hα_pos)).mpr
      (by rw [Real.rpow_zero]; exact one_le_one_div hα_pos (hα_le.trans (by norm_num)))
  have hK_le : (K : ℝ) ≤ Real.logb 2 (1 / α) + 1 := (Nat.ceil_lt_add_one hlog_nn).le
  have h2K_le : (2 : ℝ) ^ (-(K : ℤ)) ≤ α := by
    have hle_rpow : 1 / α ≤ (2 : ℝ) ^ (K : ℝ) :=
      (Real.logb_le_iff_le_rpow one_lt_two (one_div_pos.mpr hα_pos)).mp (Nat.le_ceil _)
    rw [Real.rpow_natCast] at hle_rpow
    rw [_root_.zpow_neg, zpow_natCast]
    exact (inv_anti₀ (one_div_pos.mpr hα_pos) hle_rpow).trans_eq (by simp)
  have hR_split : ∀ i j : ℕ,
      R i j ≤
        (∑ k ∈ Finset.Icc 0 K, if j = i + k then R i j else 0) +
        (∑ k ∈ Finset.Icc 1 K, if i = j + k then R i j else 0) +
        (if i + K < j then R i j else 0) +
        (if j + K < i then R i j else 0) := fun i j ↦ by
    have hRnn : 0 ≤ R i j := abs_nonneg _
    have h1nn : 0 ≤ ∑ k ∈ Finset.Icc 0 K, if j = i + k then R i j else 0 :=
      Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> simp [hRnn]
    have h2nn : 0 ≤ ∑ k ∈ Finset.Icc 1 K, if i = j + k then R i j else 0 :=
      Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> simp [hRnn]
    have h3nn : 0 ≤ if i + K < j then R i j else 0 := by split_ifs <;> simp [hRnn]
    have h4nn : 0 ≤ if j + K < i then R i j else 0 := by split_ifs <;> simp [hRnn]
    by_cases h1 : i ≤ j ∧ j ≤ i + K
    · have hs := Finset.single_le_sum (f := fun k ↦ if j = i + k then R i j else 0)
        (fun _ _ ↦ by split_ifs <;> simp [hRnn])
        (Finset.mem_Icc.mpr ⟨Nat.zero_le (j - i), Nat.sub_le_of_le_add (by omega : j ≤ K + i)⟩)
      simp [Nat.add_sub_cancel' h1.1] at hs; linarith
    · by_cases h2 : j < i ∧ i ≤ j + K
      · have hs := Finset.single_le_sum (f := fun k ↦ if i = j + k then R i j else 0)
          (fun _ _ ↦ by split_ifs <;> simp [hRnn])
          (Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt h2.1, Nat.sub_le_of_le_add (by omega : i ≤ K + j)⟩)
        simp [Nat.add_sub_cancel' h2.1.le] at hs; linarith
      · by_cases h3 : i + K < j
        · have hle : R i j ≤ if i + K < j then R i j else 0 := by simp [h3]
          linarith
        · have h4 : j + K < i := by omega
          have hle : R i j ≤ if j + K < i then R i j else 0 := by simp [h4]
          linarith
  have hdiag1 :
      (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
        ∑ k ∈ Finset.Icc 0 K, if j = i + k then R i j else 0) ≤ 16 * α * ((K : ℝ) + 1) := by
    simpa using dyadic_diag_band_bound 0 K L hα_pos.le p q hp_nn hq_nn hp_sum hq_sum R hR_rect
  have hdiag2 :
      (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L,
        ∑ k ∈ Finset.Icc 1 K, if i = j + k then R i j else 0) ≤ 16 * α * (K : ℝ) := by
    rw [Finset.sum_comm]
    have hbd := dyadic_diag_band_bound 1 K L hα_pos.le q p hq_nn hp_nn hq_sum hp_sum
      (fun j i ↦ R i j) (fun j hj i hi ↦ (hR_rect i hi j hj).trans_eq (by ring))
    have hcard : ((Finset.Icc 1 K).card : ℝ) = (K : ℝ) := by simp
    rw [hcard] at hbd; exact hbd
  have hoff1 := dyadic_offdiag_bound K L hα_pos.le h2K_le p hp_sum R hR_row
  have hoff2 :
      (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if j + K < i then R i j else 0) ≤ 4 * α := by
    rw [Finset.sum_comm]
    exact dyadic_offdiag_bound K L hα_pos.le h2K_le q hq_sum (fun j i ↦ R i j)
      fun j hj i hi hji ↦ hR_col i hi j hj hji
  have hαlog : 0 ≤ α * Real.logb 2 (1 / α) := mul_nonneg hα_pos.le hlog_nn
  have hmain_sum :
      |∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, ∑ u ∈ S i, ∑ v ∈ T j, Q u v| ≤
        56 * α * (1 + Real.logb 2 (1 / α)) := by
    have htri :
        |∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, ∑ u ∈ S i, ∑ v ∈ T j, Q u v| ≤
          ∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, R i j :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
        Finset.abs_sum_le_sum_abs _ _)
    have hR_sum :
        (∑ i ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, R i j) ≤
          16 * α * ((K : ℝ) + 1) + 16 * α * (K : ℝ) + 4 * α + 4 * α := by
      have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.Icc 1 L) ↦
        Finset.sum_le_sum fun j (_ : j ∈ Finset.Icc 1 L) ↦ hR_split i j
      simp only [Finset.sum_add_distrib] at h1; linarith
    have hK_alg :
        16 * α * ((K : ℝ) + 1) + 16 * α * (K : ℝ) + 4 * α + 4 * α ≤
          56 * α * (1 + Real.logb 2 (1 / α)) := by
      have h1 : 16 * α * ((K : ℝ) + 1) + 16 * α * (K : ℝ) + 4 * α + 4 * α =
          32 * α * (K : ℝ) + 24 * α := by ring
      have h2 : 32 * α * (K : ℝ) ≤ 32 * α * (Real.logb 2 (1 / α) + 1) :=
        mul_le_mul_of_nonneg_left hK_le (by positivity)
      linarith
    exact htri.trans (hR_sum.trans hK_alg)
  rw [hsplit_all]
  have h64 : 4 * α + 4 * α + 56 * α * (1 + Real.logb 2 (1 / α)) ≤
      64 * α * (1 + Real.logb 2 (1 / α)) := by nlinarith
  exact (abs_add_le _ _).trans
    ((add_le_add ((abs_add_le _ _).trans (add_le_add htail1 htail2)) hmain_sum).trans h64)

private lemma quad_nonneg_le_of_rect {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 1 ≤ d)
    (hreg : G.IsRegularOfDegree d) (f : Sym2 V → ℤˣ) {α : ℝ} (hα_pos : 0 < α)
    (hα_le : α ≤ 1 / 2)
    (hrect : ∀ S T : Finset V,
      |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤
        (4 * α) * Real.sqrt (S.card * T.card))
    (a b : V → ℝ) (ha_nn : ∀ u, 0 ≤ a u) (hb_nn : ∀ v, 0 ≤ b v) :
    |∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * a u * b v| ≤
      64 * α * (1 + Real.logb 2 (1 / α)) *
        Real.sqrt (∑ u : V, a u ^ 2) * Real.sqrt (∑ v : V, b v ^ 2) := by
  by_cases ha0 : ∑ u : V, a u ^ 2 = 0
  · have ha_zero : ∀ u : V, a u = 0 := fun u ↦ sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ sq_nonneg (a w)).mp ha0 u (Finset.mem_univ u))
    simp [ha_zero]
  · by_cases hb0 : ∑ v : V, b v ^ 2 = 0
    · have hb_zero : ∀ v : V, b v = 0 := fun v ↦ sq_eq_zero_iff.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ sq_nonneg (b w)).mp hb0 v (Finset.mem_univ v))
      simp [hb_zero]
    · have ha_pos : 0 < ∑ u : V, a u ^ 2 :=
        (Finset.sum_nonneg fun w _ ↦ sq_nonneg (a w)).lt_of_ne' ha0
      have hb_pos : 0 < ∑ v : V, b v ^ 2 :=
        (Finset.sum_nonneg fun w _ ↦ sq_nonneg (b w)).lt_of_ne' hb0
      set na : ℝ := Real.sqrt (∑ u : V, a u ^ 2)
      set nb : ℝ := Real.sqrt (∑ v : V, b v ^ 2)
      have hna_pos : 0 < na := Real.sqrt_pos.mpr ha_pos
      have hnb_pos : 0 < nb := Real.sqrt_pos.mpr hb_pos
      let a' : V → ℝ := fun u ↦ a u / na
      let b' : V → ℝ := fun v ↦ b v / nb
      have ha'_norm : ∑ u : V, a' u ^ 2 = 1 := by
        calc ∑ u : V, a' u ^ 2
            = ∑ u : V, a u ^ 2 / na ^ 2 := Finset.sum_congr rfl fun u _ ↦ div_pow _ _ _
          _ = (∑ u : V, a u ^ 2) / na ^ 2 := (Finset.sum_div _ _ _).symm
          _ = 1 := by rw [Real.sq_sqrt ha_pos.le, div_self ha_pos.ne']
      have hb'_norm : ∑ v : V, b' v ^ 2 = 1 := by
        calc ∑ v : V, b' v ^ 2
            = ∑ v : V, b v ^ 2 / nb ^ 2 := Finset.sum_congr rfl fun v _ ↦ div_pow _ _ _
          _ = (∑ v : V, b v ^ 2) / nb ^ 2 := (Finset.sum_div _ _ _).symm
          _ = 1 := by rw [Real.sq_sqrt hb_pos.le, div_self hb_pos.ne']
      have hunit := quad_nonneg_unit_le_of_rect G hd hreg f hα_pos hα_le hrect a' b'
        (fun u ↦ div_nonneg (ha_nn u) hna_pos.le) (fun v ↦ div_nonneg (hb_nn v) hnb_pos.le)
        ha'_norm hb'_norm
      have hscale :
          ∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * a u * b v =
            (na * nb) * ∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * a' u * b' v := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ ↦ ?_
        dsimp only [a', b']; field_simp [hna_pos.ne', hnb_pos.ne']
      rw [hscale, abs_mul, abs_of_pos (mul_pos hna_pos hnb_pos)]
      exact (mul_le_mul_of_nonneg_left hunit (mul_pos hna_pos hnb_pos).le).trans_eq (by ring)

private lemma sqrt_pos_part_sum_le {V : Type*} [Fintype V] (x : V → ℝ) :
    Real.sqrt (∑ u : V, max (x u) 0 ^ 2) + Real.sqrt (∑ u : V, max (-x u) 0 ^ 2) ≤
      Real.sqrt 2 * Real.sqrt (∑ u : V, x u ^ 2) := by
  have hx_sq : ∀ u : V, x u ^ 2 = max (x u) 0 ^ 2 + max (-x u) 0 ^ 2 := fun u ↦ by
    rcases le_total 0 (x u) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), zero_pow (by decide), add_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_pow (by decide), zero_add, neg_sq]
  have hsum_x :
      (∑ u : V, max (x u) 0 ^ 2) + (∑ u : V, max (-x u) 0 ^ 2) = ∑ u : V, x u ^ 2 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun u _ ↦ (hx_sq u).symm
  have hnn1 : 0 ≤ ∑ u : V, max (x u) 0 ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hnn2 : 0 ≤ ∑ u : V, max (-x u) 0 ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [← Real.sqrt_mul zero_le_two, ← hsum_x]
  refine (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp ?_
  rw [Real.sq_sqrt (by positivity), add_sq, Real.sq_sqrt hnn1, Real.sq_sqrt hnn2]
  nlinarith [sq_nonneg
    (Real.sqrt (∑ u : V, max (x u) 0 ^ 2) - Real.sqrt (∑ u : V, max (-x u) 0 ^ 2)),
    Real.sq_sqrt hnn1, Real.sq_sqrt hnn2]

private lemma abs_quad_le_of_rect {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 1 ≤ d)
    (hreg : G.IsRegularOfDegree d) (f : Sym2 V → ℤˣ) {α : ℝ} (hα_pos : 0 < α)
    (hα_le : α ≤ 1 / 2)
    (hrect : ∀ S T : Finset V,
      |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤
        (4 * α) * Real.sqrt (S.card * T.card))
    (x y : V → ℝ) :
    |∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * x u * y v| ≤
      128 * α * (1 + Real.logb 2 (1 / α)) *
        Real.sqrt (∑ u : V, x u ^ 2) * Real.sqrt (∑ v : V, y v ^ 2) := by
  let xp : V → ℝ := fun u ↦ max (x u) 0
  let xm : V → ℝ := fun u ↦ max (-x u) 0
  let yp : V → ℝ := fun v ↦ max (y v) 0
  let ym : V → ℝ := fun v ↦ max (-y v) 0
  have hx_eq : ∀ u : V, x u = xp u - xm u := fun u ↦ by
    dsimp only [xp, xm]; rcases le_total 0 (x u) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  have hy_eq : ∀ v : V, y v = yp v - ym v := fun v ↦ by
    dsimp only [yp, ym]; rcases le_total 0 (y v) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  let Q : (V → ℝ) → (V → ℝ) → ℝ := fun a b ↦
    ∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * a u * b v
  have hQ_split : Q x y = Q xp yp - Q xp ym - Q xm yp + Q xm ym := by
    simp only [Q, hx_eq, hy_eq, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ by ring
  let B : ℝ := 64 * α * (1 + Real.logb 2 (1 / α))
  have hB_nn : 0 ≤ B := by
    have hlog_nn : 0 ≤ Real.logb 2 (1 / α) :=
      (Real.le_logb_iff_rpow_le one_lt_two (one_div_pos.mpr hα_pos)).mpr
        (by rw [Real.rpow_zero]; exact one_le_one_div hα_pos (hα_le.trans (by norm_num)))
    positivity
  have hpp := quad_nonneg_le_of_rect G hd hreg f hα_pos hα_le hrect xp yp
    (fun _ ↦ le_max_right _ _) (fun _ ↦ le_max_right _ _)
  have hpm := quad_nonneg_le_of_rect G hd hreg f hα_pos hα_le hrect xp ym
    (fun _ ↦ le_max_right _ _) (fun _ ↦ le_max_right _ _)
  have hmp := quad_nonneg_le_of_rect G hd hreg f hα_pos hα_le hrect xm yp
    (fun _ ↦ le_max_right _ _) (fun _ ↦ le_max_right _ _)
  have hmm := quad_nonneg_le_of_rect G hd hreg f hα_pos hα_le hrect xm ym
    (fun _ ↦ le_max_right _ _) (fun _ ↦ le_max_right _ _)
  have htri : |Q x y| ≤ |Q xp yp| + |Q xp ym| + |Q xm yp| + |Q xm ym| := by
    rw [hQ_split]
    have h1 := abs_add_le (Q xp yp - Q xp ym - Q xm yp) (Q xm ym)
    have h2 := abs_sub (Q xp yp - Q xp ym) (Q xm yp)
    have h3 := abs_sub (Q xp yp) (Q xp ym)
    linarith
  calc |Q x y|
      ≤ B * Real.sqrt (∑ u : V, xp u ^ 2) * Real.sqrt (∑ v : V, yp v ^ 2) +
        B * Real.sqrt (∑ u : V, xp u ^ 2) * Real.sqrt (∑ v : V, ym v ^ 2) +
        B * Real.sqrt (∑ u : V, xm u ^ 2) * Real.sqrt (∑ v : V, yp v ^ 2) +
        B * Real.sqrt (∑ u : V, xm u ^ 2) * Real.sqrt (∑ v : V, ym v ^ 2) := by linarith
    _ = B * ((Real.sqrt (∑ u : V, xp u ^ 2) + Real.sqrt (∑ u : V, xm u ^ 2)) *
          (Real.sqrt (∑ v : V, yp v ^ 2) + Real.sqrt (∑ v : V, ym v ^ 2))) := by ring
    _ ≤ B * ((Real.sqrt 2 * Real.sqrt (∑ u : V, x u ^ 2)) *
          (Real.sqrt 2 * Real.sqrt (∑ v : V, y v ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (sqrt_pos_part_sum_le x)
            (sqrt_pos_part_sum_le y) (by positivity) (by positivity)) hB_nn
    _ = 128 * α * (1 + Real.logb 2 (1 / α)) *
          Real.sqrt (∑ u : V, x u ^ 2) * Real.sqrt (∑ v : V, y v ^ 2) := by
          rw [show B * ((Real.sqrt 2 * Real.sqrt (∑ u : V, x u ^ 2)) *
            (Real.sqrt 2 * Real.sqrt (∑ v : V, y v ^ 2))) =
            (Real.sqrt 2 * Real.sqrt 2 * B) *
              Real.sqrt (∑ u : V, x u ^ 2) * Real.sqrt (∑ v : V, y v ^ 2) by ring,
            Real.mul_self_sqrt zero_le_two]
          dsimp only [B]; ring

/-- **Bilu–Linial Converse Expander Mixing Lemma (explicit constant `128`)**: on any `d`-regular
finite simple graph (`1 ≤ d`), if every pair of disjoint vertex subsets `S, T` has signed
normalized discrepancy at most `α √(|S| |T|)` (`0 ≤ α`), then
`‖signedNormAdjMatrix G f *ᵥ x‖₂ ≤ 128 α (1 + max 0 (log₂ (1 / α))) ‖x‖₂`. -/
theorem biluLinial_converse_mixing_explicit {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} {α : ℝ} (f : Sym2 V → ℤˣ)
    (hd : 1 ≤ d) (hreg : G.IsRegularOfDegree d) (hα : 0 ≤ α)
    (hdisj : ∀ S T : Finset V, Disjoint S T →
      |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤ α * Real.sqrt (S.card * T.card))
    (x : V → ℝ) :
    ∑ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2 ≤
      (128 * α * (1 + max 0 (Real.logb 2 (1 / α)))) ^ 2 * ∑ u : V, x u ^ 2 := by
  classical
  let B : ℝ := 128 * α * (1 + max 0 (Real.logb 2 (1 / α)))
  have hB_nn : 0 ≤ B := by
    have h1 : 0 ≤ 1 + max 0 (Real.logb 2 (1 / α)) := by
      linarith [le_max_left (0 : ℝ) (Real.logb 2 (1 / α))]
    positivity
  rcases eq_or_lt_of_le hα with rfl | hα_pos
  · have hM0 : ∀ u v : V, signedNormAdjMatrix G f u v = 0 := fun u v ↦ by
      by_cases huv : u = v
      · subst huv; simp
      · simpa using hdisj {u} {v} (Finset.disjoint_singleton.mpr huv)
    have hMx0 : signedNormAdjMatrix G f *ᵥ x = 0 := by
      ext u; simp only [Matrix.mulVec, dotProduct, hM0, zero_mul, Finset.sum_const_zero,
        Pi.zero_apply]
    simp [hMx0]
  · by_cases hα_le : α ≤ 1 / 2
    · have hrect := abs_sum_signedNormAdjMatrix_le_four_mul G f hα_pos.le hdisj
      let y : V → ℝ := signedNormAdjMatrix G f *ᵥ x
      have hquad_eq :
          ∑ u : V, y u ^ 2 = ∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * y u * x v := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        simp only [y, Matrix.mulVec, dotProduct, sq, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun w _ ↦ by ring
      have hquad_le := abs_quad_le_of_rect G hd hreg f hα_pos hα_le hrect y x
      have hmax_eq : max 0 (Real.logb 2 (1 / α)) = Real.logb 2 (1 / α) :=
        max_eq_right ((Real.le_logb_iff_rpow_le one_lt_two (one_div_pos.mpr hα_pos)).mpr
          (by rw [Real.rpow_zero]; exact one_le_one_div hα_pos (hα_le.trans (by norm_num))))
      have hB_eq : B = 128 * α * (1 + Real.logb 2 (1 / α)) := by dsimp only [B]; rw [hmax_eq]
      have hy_nn : 0 ≤ ∑ u : V, y u ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have hy_le : ∑ u : V, y u ^ 2 ≤
          B * Real.sqrt (∑ u : V, y u ^ 2) * Real.sqrt (∑ v : V, x v ^ 2) := by
        calc ∑ u : V, y u ^ 2
            = |∑ u : V, ∑ v : V, signedNormAdjMatrix G f u v * y u * x v| := by
              rw [← hquad_eq, abs_of_nonneg hy_nn]
          _ ≤ B * Real.sqrt (∑ u : V, y u ^ 2) * Real.sqrt (∑ v : V, x v ^ 2) :=
              hB_eq ▸ hquad_le
      by_cases hy0 : ∑ u : V, y u ^ 2 = 0
      · change ∑ u : V, y u ^ 2 ≤ B ^ 2 * ∑ u : V, x u ^ 2
        rw [hy0]; exact mul_nonneg (sq_nonneg B) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      · have hroot_pos : 0 < Real.sqrt (∑ u : V, y u ^ 2) :=
          Real.sqrt_pos.mpr (hy_nn.lt_of_ne' hy0)
        have hstep : Real.sqrt (∑ u : V, y u ^ 2) ≤ B * Real.sqrt (∑ v : V, x v ^ 2) := by
          have h1 : Real.sqrt (∑ u : V, y u ^ 2) * Real.sqrt (∑ u : V, y u ^ 2) ≤
              (B * Real.sqrt (∑ v : V, x v ^ 2)) * Real.sqrt (∑ u : V, y u ^ 2) := by
            rw [Real.mul_self_sqrt hy_nn]; exact hy_le.trans_eq (by ring)
          exact le_of_mul_le_mul_right h1 hroot_pos
        have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hstep 2
        rw [Real.sq_sqrt hy_nn, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
          at hsq
        exact hsq
    · push Not at hα_le
      have h1B : 1 ≤ B := by
        have hmax : (1 : ℝ) ≤ 1 + max 0 (Real.logb 2 (1 / α)) := by
          linarith [le_max_left (0 : ℝ) (Real.logb 2 (1 / α))]
        dsimp only [B]; nlinarith
      have h1B2 : 1 ≤ B ^ 2 := by nlinarith
      change ∑ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2 ≤ B ^ 2 * ∑ u : V, x u ^ 2
      calc ∑ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2
          ≤ ∑ u : V, x u ^ 2 := sum_sq_signedNormAdjMatrix_mulVec_le G f x
        _ = 1 * ∑ u : V, x u ^ 2 := (one_mul _).symm
        _ ≤ B ^ 2 * ∑ u : V, x u ^ 2 :=
            mul_le_mul_of_nonneg_right h1B2 (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- **Bilu–Linial Converse Expander Mixing Lemma**. -/
theorem biluLinial_converse_mixing :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
      [DecidableRel G.Adj] {d : ℕ} {α : ℝ} (f : Sym2 V → ℤˣ),
      1 ≤ d → G.IsRegularOfDegree d → 0 ≤ α →
      (∀ S T : Finset V, Disjoint S T →
        |∑ u ∈ S, ∑ v ∈ T, signedNormAdjMatrix G f u v| ≤ α * Real.sqrt (S.card * T.card)) →
      ∀ x : V → ℝ,
        ∑ u : V, (signedNormAdjMatrix G f *ᵥ x) u ^ 2 ≤
          (C * α * (1 + max 0 (Real.logb 2 (1 / α)))) ^ 2 * ∑ u : V, x u ^ 2 :=
  ⟨128, by norm_num, fun {V} _ _ G _ {d} {α} f hd hreg hα hdisj x ↦
    biluLinial_converse_mixing_explicit G f hd hreg hα hdisj x⟩

end ConverseMixing

end CslibFrontier.SimpleGraph
