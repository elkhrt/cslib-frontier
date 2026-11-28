module

public import CslibFrontier.Computability.Communication.Rank
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `γ₂`, `γ₂*`, and `γ₂^α` Factorization Norms

This module defines the `γ₂` factorization norm, its dual norm `γ₂*`, and the approximate
factorization norm `γ₂^α`, and establishes their basic norm and duality properties.

## Main definitions

* `CslibFrontier.Matrix.entryL1Norm`: entrywise `ℓ₁` norm `∑_{x,y} |B(x,y)|`.
* `CslibFrontier.Matrix.matInner`: Frobenius inner product `∑_{x,y} A(x,y) B(x,y)`.
* `CslibFrontier.Matrix.IsSignMatrix`: sign matrices with entries in `{+1, -1}`.
* `CslibFrontier.Matrix.Gamma2Factorization`, `gamma2`, `gamma2Dual`, `gamma2Alpha`.
-/

public section

namespace CslibFrontier.Matrix

open Finset Cslib Cslib.Communication Filter
open scoped BigOperators Topology

/-! ### Basic Matrix Operations and `γ₂` Factorization Norm -/

section Gamma2Defs

variable {X Y : Type*}

/-- Entrywise `ℓ₁` norm `‖B‖₁ = ∑_{x,y} |B(x,y)|`. -/
@[expose]
def entryL1Norm [Fintype X] [Fintype Y] (B : Matrix X Y ℝ) : ℝ :=
  ∑ x : X, ∑ y : Y, |B x y|

/-- Frobenius inner product `⟨A, B⟩ = ∑_{x,y} A(x,y) B(x,y)`. -/
@[expose]
def matInner [Fintype X] [Fintype Y] (A B : Matrix X Y ℝ) : ℝ :=
  ∑ x : X, ∑ y : Y, A x y * B x y

/-- A sign matrix has every entry in `{+1, -1}`. -/
@[expose]
def IsSignMatrix (A : Matrix X Y ℝ) : Prop :=
  ∀ x y, A x y = 1 ∨ A x y = -1

/-- A `γ₂`-factorization of `A` with value bound `t ≥ 0`: finite-dimensional vectors
`u : X → Fin d → ℝ` and `v : Y → Fin d → ℝ` with `⟨u_x, v_y⟩ = A x y`,
`‖u_x‖₂² ≤ t`, and `‖v_y‖₂² ≤ t`. By rescaling `u, v`, this is equivalent to
`∃ U V, U * V = A ∧ r(U) * c(V) ≤ t`. -/
@[expose]
def Gamma2Factorization (A : Matrix X Y ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (d : ℕ) (u : X → Fin d → ℝ) (v : Y → Fin d → ℝ),
    (∀ x y, ∑ k : Fin d, u x k * v y k = A x y) ∧
    (∀ x, ∑ k : Fin d, (u x k) ^ 2 ≤ t) ∧
    (∀ y, ∑ k : Fin d, (v y k) ^ 2 ≤ t)

/-- The `γ₂` factorization norm of a real matrix `A`. -/
@[expose]
noncomputable def gamma2 (A : Matrix X Y ℝ) : ℝ :=
  sInf {t : ℝ | Gamma2Factorization A t}

/-- The dual norm `γ₂*(B) = sup {⟨B, M⟩ | γ₂(M) ≤ 1}`. -/
@[expose]
noncomputable def gamma2Dual [Fintype X] [Fintype Y] (B : Matrix X Y ℝ) : ℝ :=
  sSup {r : ℝ | ∃ M : Matrix X Y ℝ, Gamma2Factorization M 1 ∧ r = matInner B M}

/-- The approximate factorization norm `γ₂^α(A)` for a sign matrix `A` and `α ≥ 1`. -/
@[expose]
noncomputable def gamma2Alpha (A : Matrix X Y ℝ) (α : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ B : Matrix X Y ℝ,
    (∀ x y, 1 ≤ A x y * B x y ∧ A x y * B x y ≤ α) ∧ Gamma2Factorization B t}

theorem isSignMatrix_signMatrix (f : X → Y → Bool) : IsSignMatrix (signMatrix ℝ f) := fun x y => by
  cases h : f x y <;> simp [signMatrix, h]

theorem entryL1Norm_nonneg [Fintype X] [Fintype Y] (B : Matrix X Y ℝ) : 0 ≤ entryL1Norm B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem entryL1Norm_eq_zero_iff [Fintype X] [Fintype Y] {B : Matrix X Y ℝ} :
    entryL1Norm B = 0 ↔ B = 0 := by
  constructor
  · intro h
    ext x y
    have hx : ∑ y' : Y, |B x y'| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun x' _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _).1 h x (mem_univ x)
    have hxy : |B x y| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 hx y (mem_univ y)
    exact abs_eq_zero.1 hxy
  · rintro rfl; simp [entryL1Norm]

theorem entryL1Norm_smul [Fintype X] [Fintype Y] (c : ℝ) (B : Matrix X Y ℝ) :
    entryL1Norm (c • B) = |c| * entryL1Norm B := by
  simp only [entryL1Norm, Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem matInner_comm [Fintype X] [Fintype Y] (A B : Matrix X Y ℝ) :
    matInner A B = matInner B A := by
  simp only [matInner, mul_comm]

theorem matInner_smul_left [Fintype X] [Fintype Y] (c : ℝ) (A B : Matrix X Y ℝ) :
    matInner (c • A) B = c * matInner A B := by
  simp only [matInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem matInner_smul_right [Fintype X] [Fintype Y] (c : ℝ) (A B : Matrix X Y ℝ) :
    matInner A (c • B) = c * matInner A B := by
  rw [matInner_comm, matInner_smul_left, matInner_comm]

theorem matInner_add_left [Fintype X] [Fintype Y] (A₁ A₂ B : Matrix X Y ℝ) :
    matInner (A₁ + A₂) B = matInner A₁ B + matInner A₂ B := by
  simp only [matInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem matInner_neg_right [Fintype X] [Fintype Y] (A B : Matrix X Y ℝ) :
    matInner A (-B) = -matInner A B := by
  simp only [matInner, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- Every matrix admits a `γ₂`-factorization (using the canonical basis of `ℝ^X`). -/
theorem exists_gamma2Factorization [Finite X] [Finite Y] (A : Matrix X Y ℝ) :
    ∃ t : ℝ, Gamma2Factorization A t := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let t : ℝ := max 1 (∑ x : X, ∑ y : Y, (A x y) ^ 2)
  refine ⟨t, le_trans zero_le_one (le_max_left _ _), Fintype.card X,
    fun x k => if e x = k then 1 else 0,
    fun y k => A (e.symm k) y, ?_, ?_, ?_⟩
  · intro x y
    simp
  · intro x
    simp [t]
  · intro y
    have hsum : ∑ k : Fin (Fintype.card X), (A (e.symm k) y) ^ 2 = ∑ x : X, (A x y) ^ 2 :=
      Equiv.sum_comp e.symm (fun x => (A x y) ^ 2)
    rw [hsum]
    refine le_trans ?_ (le_max_right _ _)
    refine Finset.sum_le_sum fun x _ => ?_
    exact Finset.single_le_sum (fun y' _ => sq_nonneg (A x y')) (mem_univ y)

/-- Entrywise Cauchy–Schwarz bound: if `Gamma2Factorization A t`, then `|A x y| ≤ t`. -/
theorem abs_entry_le_of_factorization {A : Matrix X Y ℝ} {t : ℝ}
    (h : Gamma2Factorization A t) (x : X) (y : Y) : |A x y| ≤ t := by
  obtain ⟨ht, d, u, v, huv, hu, hv⟩ := h
  rw [← huv x y]
  have hcs : (∑ k : Fin d, u x k * v y k) ^ 2 ≤
      (∑ k : Fin d, (u x k) ^ 2) * (∑ k : Fin d, (v y k) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (u x) (v y)
  have hsq : (∑ k : Fin d, u x k * v y k) ^ 2 ≤ t ^ 2 :=
    hcs.trans (by
      rw [sq]
      exact mul_le_mul (hu x) (hv y) (Finset.sum_nonneg fun _ _ => sq_nonneg _) ht)
  nlinarith [sq_abs (∑ k : Fin d, u x k * v y k), abs_nonneg (∑ k : Fin d, u x k * v y k)]

theorem gamma2Factorization_mono {A : Matrix X Y ℝ} {t₁ t₂ : ℝ}
    (h : Gamma2Factorization A t₁) (hle : t₁ ≤ t₂) : Gamma2Factorization A t₂ := by
  obtain ⟨ht, d, u, v, huv, hu, hv⟩ := h
  exact ⟨ht.trans hle, d, u, v, huv, fun x => (hu x).trans hle, fun y => (hv y).trans hle⟩

theorem gamma2Factorization_zero : Gamma2Factorization (0 : Matrix X Y ℝ) 0 :=
  ⟨le_rfl, 0, fun _ => Fin.elim0, fun _ => Fin.elim0, fun _ _ => by simp,
    fun _ => by simp, fun _ => by simp⟩

theorem gamma2Factorization_neg {A : Matrix X Y ℝ} {t : ℝ} (h : Gamma2Factorization A t) :
    Gamma2Factorization (-A) t := by
  obtain ⟨ht, d, u, v, huv, hu, hv⟩ := h
  refine ⟨ht, d, fun x k => -u x k, v, fun x y => ?_, fun x => ?_, hv⟩
  · simp [← huv x y]
  · simpa using hu x

theorem gamma2Factorization_smul {A : Matrix X Y ℝ} {t c : ℝ}
    (h : Gamma2Factorization A t) (hc : 0 ≤ c) :
    Gamma2Factorization (c • A) (c * t) := by
  obtain ⟨ht, d, u, v, huv, hu, hv⟩ := h
  refine ⟨mul_nonneg hc ht, d, fun x k => Real.sqrt c * u x k, fun y k => Real.sqrt c * v y k,
    fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · calc ∑ k : Fin d, (Real.sqrt c * u x k) * (Real.sqrt c * v y k)
        = (Real.sqrt c * Real.sqrt c) * ∑ k : Fin d, u x k * v y k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ = c * A x y := by rw [Real.mul_self_sqrt hc, huv x y]
  · calc ∑ k : Fin d, (Real.sqrt c * u x k) ^ 2
        = (Real.sqrt c) ^ 2 * ∑ k : Fin d, (u x k) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ = c * ∑ k : Fin d, (u x k) ^ 2 := by rw [Real.sq_sqrt hc]
      _ ≤ c * t := mul_le_mul_of_nonneg_left (hu x) hc
  · calc ∑ k : Fin d, (Real.sqrt c * v y k) ^ 2
        = (Real.sqrt c) ^ 2 * ∑ k : Fin d, (v y k) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ = c * ∑ k : Fin d, (v y k) ^ 2 := by rw [Real.sq_sqrt hc]
      _ ≤ c * t := mul_le_mul_of_nonneg_left (hv y) hc

theorem gamma2Factorization_add {A B : Matrix X Y ℝ} {t₁ t₂ : ℝ}
    (hA : Gamma2Factorization A t₁) (hB : Gamma2Factorization B t₂) :
    Gamma2Factorization (A + B) (t₁ + t₂) := by
  obtain ⟨ht₁, d₁, u₁, v₁, huv₁, hu₁, hv₁⟩ := hA
  obtain ⟨ht₂, d₂, u₂, v₂, huv₂, hu₂, hv₂⟩ := hB
  let e : Fin d₁ ⊕ Fin d₂ ≃ Fin (d₁ + d₂) := finSumFinEquiv
  refine ⟨add_nonneg ht₁ ht₂, d₁ + d₂,
    fun x k => Sum.elim (u₁ x) (u₂ x) (e.symm k),
    fun y k => Sum.elim (v₁ y) (v₂ y) (e.symm k), ?_, ?_, ?_⟩
  · intro x y
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    simp [huv₁ x y, huv₂ x y]
  · intro x
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    exact add_le_add (hu₁ x) (hu₂ x)
  · intro y
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    exact add_le_add (hv₁ y) (hv₂ y)

/-- Hadamard product submultiplicativity for `γ₂`-factorizations via Kronecker product. -/
theorem gamma2Factorization_hadamard {A B : Matrix X Y ℝ} {t₁ t₂ : ℝ}
    (hA : Gamma2Factorization A t₁) (hB : Gamma2Factorization B t₂) :
    Gamma2Factorization (A.hadamard B) (t₁ * t₂) := by
  obtain ⟨ht₁, d₁, u₁, v₁, huv₁, hu₁, hv₁⟩ := hA
  obtain ⟨ht₂, d₂, u₂, v₂, huv₂, hu₂, hv₂⟩ := hB
  let e : Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂) := finProdFinEquiv
  refine ⟨mul_nonneg ht₁ ht₂, d₁ * d₂,
    fun x k => u₁ x (e.symm k).1 * u₂ x (e.symm k).2,
    fun y k => v₁ y (e.symm k).1 * v₂ y (e.symm k).2, ?_, ?_, ?_⟩
  · intro x y
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, Matrix.hadamard_apply]
    calc ∑ k₁ : Fin d₁, ∑ k₂ : Fin d₂, (u₁ x k₁ * u₂ x k₂) * (v₁ y k₁ * v₂ y k₂)
        = (∑ k₁ : Fin d₁, u₁ x k₁ * v₁ y k₁) * (∑ k₂ : Fin d₂, u₂ x k₂ * v₂ y k₂) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k₂ _ => by ring
      _ = A x y * B x y := by rw [huv₁ x y, huv₂ x y]
  · intro x
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    calc ∑ k₁ : Fin d₁, ∑ k₂ : Fin d₂, (u₁ x k₁ * u₂ x k₂) ^ 2
        = (∑ k₁ : Fin d₁, (u₁ x k₁) ^ 2) * (∑ k₂ : Fin d₂, (u₂ x k₂) ^ 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k₂ _ => by ring
      _ ≤ t₁ * t₂ := mul_le_mul (hu₁ x) (hu₂ x) (Finset.sum_nonneg fun _ _ => sq_nonneg _) ht₁
  · intro y
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    calc ∑ k₁ : Fin d₁, ∑ k₂ : Fin d₂, (v₁ y k₁ * v₂ y k₂) ^ 2
        = (∑ k₁ : Fin d₁, (v₁ y k₁) ^ 2) * (∑ k₂ : Fin d₂, (v₂ y k₂) ^ 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k₂ _ => by ring
      _ ≤ t₁ * t₂ := mul_le_mul (hv₁ y) (hv₂ y) (Finset.sum_nonneg fun _ _ => sq_nonneg _) ht₁

/-- Indicator matrix of a rectangle has `γ₂`-factorization of value `1`. -/
theorem gamma2Factorization_rect [DecidableEq X] [DecidableEq Y] (A : Finset X) (B : Finset Y) :
    Gamma2Factorization (Matrix.of fun x y => if x ∈ A ∧ y ∈ B then (1 : ℝ) else 0) 1 := by
  refine ⟨zero_le_one, 1,
    fun x _ => if x ∈ A then 1 else 0,
    fun y _ => if y ∈ B then 1 else 0, ?_, ?_, ?_⟩
  · intro x y
    simp only [Fin.sum_univ_one, Matrix.of_apply]
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;> simp [hx, hy]
  · intro x; simp; split_ifs <;> norm_num
  · intro y; simp; split_ifs <;> norm_num

/-- Every `γ₂`-factorization in arbitrary dimension `d` compresses to fixed dimension
`Fintype.card X` by orthogonal projection onto `span {u_x | x : X}`. -/
private theorem gamma2Factorization_fixedDim [Fintype X] {A : Matrix X Y ℝ} {t : ℝ}
    (h : Gamma2Factorization A t) :
    0 ≤ t ∧ ∃ (u : X → Fin (Fintype.card X) → ℝ) (v : Y → Fin (Fintype.card X) → ℝ),
      (∀ x y, ∑ k, u x k * v y k = A x y) ∧
      (∀ x, ∑ k, (u x k) ^ 2 ≤ t) ∧
      (∀ y, ∑ k, (v y k) ^ 2 ≤ t) := by
  classical
  obtain ⟨ht, d, u, v, huv, hu, hv⟩ := h
  let uE : X → EuclideanSpace ℝ (Fin d) := fun x => (WithLp.equiv 2 (Fin d → ℝ)).symm (u x)
  let vE : Y → EuclideanSpace ℝ (Fin d) := fun y => (WithLp.equiv 2 (Fin d → ℝ)).symm (v y)
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ (Set.range uE)
  have hdimW : Module.finrank ℝ W ≤ Fintype.card X := by
    have hcard : (Set.range uE).toFinset.card ≤ Fintype.card X :=
      (Set.toFinset_range uE ▸ Finset.card_image_le)
    have hspan : W =
      Submodule.span ℝ ((Set.range uE).toFinset : Set (EuclideanSpace ℝ (Fin d))) := by
      simp [W]
    rw [hspan]
    exact (finrank_span_le_card _).trans (by simpa using hcard)
  let b : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ W := stdOrthonormalBasis ℝ W
  let emb : Fin (Module.finrank ℝ W) ↪ Fin (Fintype.card X) :=
    ⟨Fin.castLE hdimW, Fin.castLE_injective hdimW⟩
  let u' : X → Fin (Fintype.card X) → ℝ := fun x k =>
    if hk : k.1 < Module.finrank ℝ W then
      b.repr ⟨uE x, Submodule.subset_span ⟨x, rfl⟩⟩ ⟨k.1, hk⟩
    else 0
  let v' : Y → Fin (Fintype.card X) → ℝ := fun y k =>
    if hk : k.1 < Module.finrank ℝ W then
      b.repr (W.orthogonalProjectionOnto (vE y)) ⟨k.1, hk⟩
    else 0
  have hsum_cut (f : Fin (Fintype.card X) → ℝ) (hf : ∀ k, ¬ k.1 < Module.finrank ℝ W → f k = 0) :
      ∑ k : Fin (Fintype.card X), f k =
        ∑ j : Fin (Module.finrank ℝ W), f (Fin.castLE hdimW j) := by
    rw [← Finset.sum_image (f := f) (g := Fin.castLE hdimW)
      (fun a _ b _ h => Fin.castLE_injective hdimW h)]
    refine (Finset.sum_subset (subset_univ _) fun k _ hk => ?_).symm
    apply hf k
    intro hlt
    exact hk (Finset.mem_image.2 ⟨⟨k.1, hlt⟩, mem_univ _, by ext; rfl⟩)
  refine ⟨ht, u', v', ?_, ?_, ?_⟩
  · intro x y
    rw [hsum_cut _ (fun k hk => by simp [u', hk])]
    have hinner : ∑ j : Fin (Module.finrank ℝ W),
        u' x (Fin.castLE hdimW j) * v' y (Fin.castLE hdimW j) =
        @inner ℝ W _ ⟨uE x, Submodule.subset_span ⟨x, rfl⟩⟩
          (W.orthogonalProjectionOnto (vE y)) := by
      have := b.repr.inner_map_map ⟨uE x, Submodule.subset_span ⟨x, rfl⟩⟩
        (W.orthogonalProjectionOnto (vE y))
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      simp only [star_trivial, dotProduct] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [u', v', Fin.val_castLE, j.2, ↓reduceDIte]
      exact mul_comm _ _
    rw [hinner]
    have horth : @inner ℝ (EuclideanSpace ℝ (Fin d)) _
        (vE y - W.starProjection (vE y)) (uE x) = 0 :=
      Submodule.starProjection_inner_eq_zero (vE y) (uE x) (Submodule.subset_span ⟨x, rfl⟩)
    have hproj_in : @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (uE x) (W.starProjection (vE y)) =
        @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (uE x) (vE y) := by
      rw [inner_sub_left, real_inner_comm (uE x) (vE y),
        real_inner_comm (uE x) (W.starProjection (vE y))] at horth
      linarith
    change @inner ℝ (EuclideanSpace ℝ (Fin d)) _ (uE x) (W.starProjection (vE y)) = _
    rw [hproj_in, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct, uE, vE]
    simpa [mul_comm] using huv x y
  · intro x
    rw [hsum_cut _ (fun k hk => by simp [u', hk])]
    have hnorm : ∑ j : Fin (Module.finrank ℝ W), (u' x (Fin.castLE hdimW j)) ^ 2 =
        ‖uE x‖ ^ 2 := by
      have h1 := b.repr.norm_map ⟨uE x, Submodule.subset_span ⟨x, rfl⟩⟩
      have hsq : ‖b.repr ⟨uE x, Submodule.subset_span ⟨x, rfl⟩⟩‖ ^ 2 = ‖uE x‖ ^ 2 := by
        rw [h1]; rfl
      rw [EuclideanSpace.norm_sq_eq] at hsq
      simp only [Real.norm_eq_abs, sq_abs] at hsq
      rw [← hsq]
      refine Finset.sum_congr rfl fun j _ => by simp [u', j.2]
    rw [hnorm, EuclideanSpace.norm_sq_eq]
    simpa [uE] using hu x
  · intro y
    rw [hsum_cut _ (fun k hk => by simp [v', hk])]
    have hnorm : ∑ j : Fin (Module.finrank ℝ W), (v' y (Fin.castLE hdimW j)) ^ 2 =
        ‖W.orthogonalProjectionOnto (vE y)‖ ^ 2 := by
      have h1 := b.repr.norm_map (W.orthogonalProjectionOnto (vE y))
      have hsq : ‖b.repr (W.orthogonalProjectionOnto (vE y))‖ ^ 2 =
          ‖W.orthogonalProjectionOnto (vE y)‖ ^ 2 := by rw [h1]
      rw [EuclideanSpace.norm_sq_eq] at hsq
      simp only [Real.norm_eq_abs, sq_abs] at hsq
      rw [← hsq]
      refine Finset.sum_congr rfl fun j _ => by simp [v', j.2]
    rw [hnorm]
    have hproj : ‖W.orthogonalProjectionOnto (vE y)‖ ≤ ‖vE y‖ :=
      W.norm_orthogonalProjectionOnto_apply_le (vE y)
    have hnn1 : 0 ≤ ‖W.orthogonalProjectionOnto (vE y)‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖vE y‖ := norm_nonneg _
    have hsq_le : ‖W.orthogonalProjectionOnto (vE y)‖ ^ 2 ≤ ‖vE y‖ ^ 2 :=
      sq_le_sq' (by linarith) hproj
    refine hsq_le.trans ?_
    rw [EuclideanSpace.norm_sq_eq]
    simpa [vE] using hv y

/-- The `γ₂`-ball `{M | Gamma2Factorization M t}` is compact for every `t ≥ 0`. -/
theorem isCompact_gamma2Ball [Finite X] [Finite Y] {t : ℝ} (ht : 0 ≤ t) :
    IsCompact {M : Matrix X Y ℝ | Gamma2Factorization M t} := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  let d := Fintype.card X
  let S : Set ((X → Fin d → ℝ) × (Y → Fin d → ℝ)) :=
    {p | (∀ x, ∑ k, (p.1 x k) ^ 2 ≤ t) ∧ (∀ y, ∑ k, (p.2 y k) ^ 2 ≤ t)}
  let φ : (X → Fin d → ℝ) × (Y → Fin d → ℝ) → Matrix X Y ℝ :=
    fun p => Matrix.of fun x y => ∑ k : Fin d, p.1 x k * p.2 y k
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {p : (X → Fin d → ℝ) × (Y → Fin d → ℝ) |
        ∀ x, ∑ k, (p.1 x k) ^ 2 ≤ t} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const
    have h2 : IsClosed {p : (X → Fin d → ℝ) × (Y → Fin d → ℝ) |
        ∀ y, ∑ k, (p.2 y k) ^ 2 ≤ t} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun y => isClosed_le (by fun_prop) continuous_const
    exact h1.inter h2
  have hS_bdd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt t, fun p hp => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Prod.norm_def, max_le_iff]
    constructor
    · rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg t)]
      intro x
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg t)]
      intro k
      have hsq : (p.1 x k) ^ 2 ≤ t :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (p.1 x j)) (mem_univ k)).trans (hp.1 x)
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    · rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg t)]
      intro y
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg t)]
      intro k
      have hsq : (p.2 y k) ^ 2 ≤ t :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (p.2 y j)) (mem_univ k)).trans (hp.2 y)
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  have hcont : Continuous φ :=
    continuous_pi fun x => continuous_pi fun y => by fun_prop
  have himg : φ '' S = {M : Matrix X Y ℝ | Gamma2Factorization M t} := by
    ext M
    constructor
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
      exact ⟨ht, d, u, v, fun _ _ => rfl, hu, hv⟩
    · intro hM
      obtain ⟨_, u, v, huv, hu, hv⟩ := gamma2Factorization_fixedDim hM
      exact ⟨⟨u, v⟩, ⟨hu, hv⟩, Matrix.ext fun x y => huv x y⟩
  rw [← himg]
  exact hS_compact.image hcont

theorem convex_gamma2Ball {t : ℝ} (ht : 0 ≤ t) :
    Convex ℝ {M : Matrix X Y ℝ | Gamma2Factorization M t} := by
  intro A hA B hB a b ha hb hab
  have h1 := gamma2Factorization_smul hA ha
  have h2 := gamma2Factorization_smul hB hb
  have h3 := gamma2Factorization_add h1 h2
  have hsum : a * t + b * t = t := by nlinarith
  simpa [hsum] using h3

theorem gamma2_nonneg (A : Matrix X Y ℝ) : 0 ≤ gamma2 A :=
  Real.sInf_nonneg fun _ h => h.1

theorem gamma2_le_of_factorization {A : Matrix X Y ℝ} {t : ℝ} (h : Gamma2Factorization A t) :
    gamma2 A ≤ t :=
  csInf_le ⟨0, fun _ h' => h'.1⟩ h

/-- The infimum `gamma2 A` is attained by a factorization. -/
theorem gamma2Factorization_gamma2 [Finite X] [Finite Y] (A : Matrix X Y ℝ) :
    Gamma2Factorization A (gamma2 A) := by
  have hne : {t : ℝ | Gamma2Factorization A t}.Nonempty := exists_gamma2Factorization A
  have hbdd : BddBelow {t : ℝ | Gamma2Factorization A t} := ⟨0, fun _ h => h.1⟩
  have hnn : 0 ≤ gamma2 A := gamma2_nonneg A
  by_cases h0 : gamma2 A = 0
  · have hA0 : A = 0 := by
      ext x y
      by_contra hne_xy
      have hpos : 0 < |A x y| := abs_pos.2 hne_xy
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt hne (by linarith : gamma2 A < |A x y|)
      linarith [abs_entry_le_of_factorization ht x y]
    rw [h0, hA0]
    exact gamma2Factorization_zero
  · have hpos : 0 < gamma2 A := lt_of_le_of_ne hnn (Ne.symm h0)
    -- `A ∈ (gamma2 A) • B₁` since `((1 + 1/(n+1))⁻¹ • A) ∈ B₁` and `B₁` is closed!
    have hcl : IsClosed {M : Matrix X Y ℝ | Gamma2Factorization M (gamma2 A)} :=
      (isCompact_gamma2Ball hnn).isClosed
    have hseq : ∀ n : ℕ, ((gamma2 A / (gamma2 A + 1 / ((n : ℝ) + 1))) • A) ∈
        {M : Matrix X Y ℝ | Gamma2Factorization M (gamma2 A)} := by
      intro n
      have hlt : gamma2 A < gamma2 A + 1 / ((n : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
      obtain ⟨t, ht, ht_lt⟩ := exists_lt_of_csInf_lt hne hlt
      have ht' := gamma2Factorization_mono ht ht_lt.le
      have hc : 0 ≤ gamma2 A / (gamma2 A + 1 / ((n : ℝ) + 1)) := by positivity
      have hsm := gamma2Factorization_smul ht' hc
      have hcancel : gamma2 A / (gamma2 A + 1 / ((n : ℝ) + 1)) *
          (gamma2 A + 1 / ((n : ℝ) + 1)) = gamma2 A := by
        field_simp [(by positivity : gamma2 A + 1 / ((n : ℝ) + 1) ≠ 0)]
      rw [hcancel] at hsm
      exact hsm
    have htend : Tendsto (fun n : ℕ =>
        (gamma2 A / (gamma2 A + 1 / ((n : ℝ) + 1))) • A) atTop (𝓝 A) := by
      have h1 : Tendsto (fun n : ℕ => gamma2 A / (gamma2 A + 1 / ((n : ℝ) + 1)))
          atTop (𝓝 (gamma2 A / (gamma2 A + 0))) :=
        tendsto_const_nhds.div
          (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat))
          (by linarith)
      rw [add_zero, div_self hpos.ne'] at h1
      simpa [one_smul] using h1.smul (tendsto_const_nhds (x := A))
    exact hcl.mem_of_tendsto htend (Eventually.of_forall hseq)

theorem gamma2_le_iff [Finite X] [Finite Y] {A : Matrix X Y ℝ} {t : ℝ} :
    gamma2 A ≤ t ↔ Gamma2Factorization A t :=
  ⟨fun h => gamma2Factorization_mono (gamma2Factorization_gamma2 A) h,
    gamma2_le_of_factorization⟩

theorem gamma2_hadamard_le [Finite X] [Finite Y] (A B : Matrix X Y ℝ) :
    gamma2 (A.hadamard B) ≤ gamma2 A * gamma2 B :=
  gamma2_le_of_factorization
    (gamma2Factorization_hadamard (gamma2Factorization_gamma2 A) (gamma2Factorization_gamma2 B))

theorem gamma2_add_le [Finite X] [Finite Y] (A B : Matrix X Y ℝ) :
    gamma2 (A + B) ≤ gamma2 A + gamma2 B :=
  gamma2_le_of_factorization
    (gamma2Factorization_add (gamma2Factorization_gamma2 A) (gamma2Factorization_gamma2 B))

theorem gamma2_smul_nonneg [Finite X] [Finite Y] {c : ℝ} (hc : 0 ≤ c) (A : Matrix X Y ℝ) :
    gamma2 (c • A) = c * gamma2 A := by
  refine le_antisymm (gamma2_le_of_factorization
    (gamma2Factorization_smul (gamma2Factorization_gamma2 A) hc)) ?_
  rcases hc.eq_or_lt with rfl | hpos
  · simp [gamma2_nonneg]
  · have h := gamma2Factorization_smul (gamma2Factorization_gamma2 (c • A))
      (inv_nonneg.2 hpos.le)
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] at h
    have hle := gamma2_le_of_factorization h
    have := mul_le_mul_of_nonneg_left hle hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this

theorem gamma2_neg [Finite X] [Finite Y] (A : Matrix X Y ℝ) : gamma2 (-A) = gamma2 A := by
  refine le_antisymm
    (gamma2_le_of_factorization (gamma2Factorization_neg (gamma2Factorization_gamma2 A))) ?_
  simpa using gamma2_le_of_factorization
    (gamma2Factorization_neg (gamma2Factorization_gamma2 (-A)))

theorem gamma2_eq_zero_iff [Finite X] [Finite Y] {A : Matrix X Y ℝ} : gamma2 A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext x y
    exact abs_nonpos_iff.1
      ((abs_entry_le_of_factorization (gamma2Factorization_gamma2 A) x y).trans_eq h)
  · rintro rfl
    exact le_antisymm (gamma2_le_of_factorization gamma2Factorization_zero) (gamma2_nonneg 0)

/-- Properties of the dual norm `γ₂*`. -/
theorem gamma2Dual_bddAbove [Fintype X] [Fintype Y] (B : Matrix X Y ℝ) :
    BddAbove {r : ℝ | ∃ M : Matrix X Y ℝ, Gamma2Factorization M 1 ∧ r = matInner B M} := by
  refine ⟨entryL1Norm B, ?_⟩
  rintro _ ⟨M, hM, rfl⟩
  unfold matInner entryL1Norm
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  calc B x y * M x y ≤ |B x y * M x y| := le_abs_self _
    _ = |B x y| * |M x y| := abs_mul _ _
    _ ≤ |B x y| * 1 :=
      mul_le_mul_of_nonneg_left (abs_entry_le_of_factorization hM x y) (abs_nonneg _)
    _ = |B x y| := mul_one _

theorem le_gamma2Dual [Fintype X] [Fintype Y] {B M : Matrix X Y ℝ} (hM : Gamma2Factorization M 1) :
    matInner B M ≤ gamma2Dual B :=
  le_csSup (gamma2Dual_bddAbove B) ⟨M, hM, rfl⟩

theorem gamma2Dual_nonneg [Fintype X] [Fintype Y] (B : Matrix X Y ℝ) : 0 ≤ gamma2Dual B := by
  have h0 : Gamma2Factorization (0 : Matrix X Y ℝ) 1 :=
    gamma2Factorization_mono gamma2Factorization_zero zero_le_one
  have := le_gamma2Dual (B := B) h0
  simpa [matInner] using this

theorem matInner_le_gamma2Dual_mul_gamma2 [Fintype X] [Fintype Y] (B M : Matrix X Y ℝ) :
    matInner B M ≤ gamma2Dual B * gamma2 M := by
  by_cases hM0 : gamma2 M = 0
  · rw [hM0, gamma2_eq_zero_iff.1 hM0, mul_zero]; simp [matInner]
  · have hpos : 0 < gamma2 M := lt_of_le_of_ne (gamma2_nonneg M) (Ne.symm hM0)
    have h1 : Gamma2Factorization ((gamma2 M)⁻¹ • M) 1 := by
      have hsm := gamma2Factorization_smul (gamma2Factorization_gamma2 M) (inv_nonneg.2 hpos.le)
      rwa [inv_mul_cancel₀ hpos.ne'] at hsm
    have hle := le_gamma2Dual (B := B) h1
    rw [matInner_smul_right] at hle
    have := mul_le_mul_of_nonneg_right hle hpos.le
    rw [mul_comm _ (gamma2 M), ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith

theorem gamma2Dual_pos_of_ne_zero [Fintype X] [Fintype Y] {B : Matrix X Y ℝ} (hB : B ≠ 0) :
    0 < gamma2Dual B := by
  classical
  have hex : ∃ x y, B x y ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hB (Matrix.ext hall)
  obtain ⟨x0, y0, hxy⟩ := hex
  let M : Matrix X Y ℝ := Matrix.of fun x y =>
    if x = x0 ∧ y = y0 then (if 0 ≤ B x0 y0 then 1 else -1) else 0
  have hM : Gamma2Factorization M 1 := by
    refine ⟨zero_le_one, 1,
      fun x _ => if x = x0 then (if 0 ≤ B x0 y0 then 1 else -1) else 0,
      fun y _ => if y = y0 then 1 else 0, ?_, ?_, ?_⟩
    · intro x y
      simp only [Fin.sum_univ_one, M, Matrix.of_apply]
      by_cases hx : x = x0 <;> by_cases hy : y = y0 <;> simp [hx, hy]
    · intro x; simp; split_ifs <;> norm_num
    · intro y; simp; split_ifs <;> norm_num
  have hval : matInner B M = |B x0 y0| := by
    unfold matInner
    rw [Finset.sum_eq_single x0, Finset.sum_eq_single y0]
    · simp only [M, Matrix.of_apply, and_self, ↓reduceIte]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]
    · intro y _ hy; simp [M, hy]
    · intro h; exact False.elim (h (mem_univ _))
    · intro x _ hx; refine Finset.sum_eq_zero fun y _ => by simp [M, hx]
    · intro h; exact False.elim (h (mem_univ _))
  exact lt_of_lt_of_le (abs_pos.2 hxy) (hval ▸ le_gamma2Dual hM)

theorem gamma2Dual_smul_nonneg [Fintype X] [Fintype Y] {c : ℝ} (hc : 0 ≤ c) (B : Matrix X Y ℝ) :
    gamma2Dual (c • B) = c * gamma2Dual B := by
  refine le_antisymm ?_ ?_
  · refine Real.sSup_le ?_ (mul_nonneg hc (gamma2Dual_nonneg B))
    rintro _ ⟨M, hM, rfl⟩
    rw [matInner_smul_left]
    exact mul_le_mul_of_nonneg_left (le_gamma2Dual hM) hc
  · rcases hc.eq_or_lt with rfl | hpos
    · simp [gamma2Dual_nonneg]
    · rw [← le_div_iff₀' hpos]
      refine Real.sSup_le ?_ (div_nonneg (gamma2Dual_nonneg _) hpos.le)
      rintro _ ⟨M, hM, rfl⟩
      rw [le_div_iff₀' hpos, ← matInner_smul_left]
      exact le_gamma2Dual hM

theorem gamma2Dual_add_le [Fintype X] [Fintype Y] (B₁ B₂ : Matrix X Y ℝ) :
    gamma2Dual (B₁ + B₂) ≤ gamma2Dual B₁ + gamma2Dual B₂ := by
  refine Real.sSup_le ?_ (add_nonneg (gamma2Dual_nonneg B₁) (gamma2Dual_nonneg B₂))
  rintro _ ⟨M, hM, rfl⟩
  rw [matInner_add_left]
  exact add_le_add (le_gamma2Dual hM) (le_gamma2Dual hM)

theorem gamma2Dual_le_entryL1Norm [Fintype X] [Fintype Y] (B : Matrix X Y ℝ) :
    gamma2Dual B ≤ entryL1Norm B :=
  Real.sSup_le (fun _ ⟨M, hM, hr⟩ => hr ▸ by
    unfold matInner entryL1Norm
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    calc B x y * M x y ≤ |B x y| * |M x y| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |B x y| * 1 :=
        mul_le_mul_of_nonneg_left (abs_entry_le_of_factorization hM x y) (abs_nonneg _)
      _ = |B x y| := mul_one _) (entryL1Norm_nonneg B)

theorem continuous_gamma2Dual [Fintype X] [Fintype Y] :
    Continuous (gamma2Dual (X := X) (Y := Y)) := by
  change Continuous (fun B : X → Y → ℝ => gamma2Dual (Matrix.of B))
  rw [Metric.continuous_iff]
  intro B ε hε
  let C : ℝ := (Fintype.card X * Fintype.card Y : ℝ) + 1
  have hC : 0 < C := by positivity
  refine ⟨ε / C, div_pos hε hC, fun B' hdist => ?_⟩
  have hdiff (D : Matrix X Y ℝ) : |gamma2Dual (Matrix.of B + D) - gamma2Dual (Matrix.of B)| ≤
      entryL1Norm D := by
    have h1 : gamma2Dual (Matrix.of B + D) - gamma2Dual (Matrix.of B) ≤ gamma2Dual D := by
      linarith [gamma2Dual_add_le (Matrix.of B) D]
    have h2 : gamma2Dual (Matrix.of B) - gamma2Dual (Matrix.of B + D) ≤ gamma2Dual (-D) := by
      have heq : Matrix.of B = (Matrix.of B + D) + (-D) := by abel
      have := gamma2Dual_add_le (Matrix.of B + D) (-D)
      rw [← heq] at this
      linarith
    have hneg : gamma2Dual (-D) = gamma2Dual D := by
      have hle (E : Matrix X Y ℝ) : gamma2Dual (-E) ≤ gamma2Dual E := by
        refine Real.sSup_le ?_ (gamma2Dual_nonneg E)
        rintro _ ⟨M, hM, rfl⟩
        have heq : matInner (-E) M = matInner E (-M) := by
          simp [matInner, mul_neg, neg_mul]
        rw [heq]
        exact le_gamma2Dual (gamma2Factorization_neg hM)
      exact le_antisymm (hle D) (by simpa using hle (-D))
    rw [abs_le]
    exact ⟨by linarith [gamma2Dual_le_entryL1Norm D], by linarith [gamma2Dual_le_entryL1Norm D]⟩
  have hsub : Matrix.of B' = Matrix.of B + Matrix.of (B' - B) := by ext x y; simp
  rw [Real.dist_eq, hsub]
  refine (hdiff (Matrix.of (B' - B))).trans_lt ?_
  have hl1 : entryL1Norm (Matrix.of (B' - B)) ≤
      (Fintype.card X * Fintype.card Y : ℝ) * dist B' B := by
    unfold entryL1Norm
    calc ∑ x : X, ∑ y : Y, |(Matrix.of (B' - B)) x y|
        ≤ ∑ _x : X, ∑ _y : Y, dist B' B := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          have h1 : dist (B' x) (B x) ≤ dist B' B := dist_le_pi_dist B' B x
          have h2 : dist (B' x y) (B x y) ≤ dist (B' x) (B x) := dist_le_pi_dist (B' x) (B x) y
          simpa [Real.dist_eq] using h2.trans h1
      _ = (Fintype.card X * Fintype.card Y : ℝ) * dist B' B := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hlt : (Fintype.card X * Fintype.card Y : ℝ) * dist B' B < C * (ε / C) := by
    have hnn : 0 ≤ dist B' B := dist_nonneg
    have hlt1 : (Fintype.card X * Fintype.card Y : ℝ) * dist B' B ≤
        (Fintype.card X * Fintype.card Y : ℝ) * (ε / C) :=
      mul_le_mul_of_nonneg_left hdist.le (by positivity)
    have hlt2 : (Fintype.card X * Fintype.card Y : ℝ) * (ε / C) < C * (ε / C) :=
      mul_lt_mul_of_pos_right (by dsimp [C]; linarith) (div_pos hε hC)
    linarith
  rw [mul_div_cancel₀ _ hC.ne'] at hlt
  exact hl1.trans_lt hlt

theorem gamma2Alpha_le_gamma2 [Finite X] [Finite Y] {A : Matrix X Y ℝ} (hA : IsSignMatrix A)
    {α : ℝ} (hα : 1 ≤ α) : gamma2Alpha A α ≤ gamma2 A := by
  refine csInf_le ⟨0, fun _ ⟨_, _, h⟩ => h.1⟩ ⟨A, fun x y => ?_, gamma2Factorization_gamma2 A⟩
  rcases hA x y with h | h <;> simp [h, hα]

theorem one_le_gamma2Alpha [Finite X] [Finite Y] [Nonempty X] [Nonempty Y] {A : Matrix X Y ℝ}
    (hA : IsSignMatrix A) {α : ℝ} (hα : 1 ≤ α) : 1 ≤ gamma2Alpha A α := by
  have hne : {t : ℝ | ∃ B : Matrix X Y ℝ,
      (∀ x y, 1 ≤ A x y * B x y ∧ A x y * B x y ≤ α) ∧ Gamma2Factorization B t}.Nonempty :=
    ⟨gamma2 A, A, fun x y => by rcases hA x y with h | h <;> simp [h, hα],
      gamma2Factorization_gamma2 A⟩
  refine le_csInf hne ?_
  rintro t ⟨B, hB, hfac⟩
  let x0 : X := Classical.arbitrary X
  let y0 : Y := Classical.arbitrary Y
  have h1 := (hB x0 y0).1
  have habs : 1 ≤ |B x0 y0| := by
    rcases hA x0 y0 with h | h
    · rw [h, one_mul] at h1; exact h1.trans (le_abs_self _)
    · rw [h, neg_one_mul] at h1; exact h1.trans (neg_le_abs _)
  exact habs.trans (abs_entry_le_of_factorization hfac x0 y0)

end Gamma2Defs

end CslibFrontier.Matrix
