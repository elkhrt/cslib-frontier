module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Computability.Circuit.Formula

import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Formula
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Projection
import CslibFrontier.Computability.Circuit.Bird
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BranchingProgramDeterminant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Single
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebraic Branching Programs, Formula Classes, and Determinantal Universality

Let `K` be a commutative ring. In Valiant's algebraic complexity hierarchy
$$\mathsf{VP}_{\mathrm{ws}}(K) \subseteq \mathsf{VBP}(K) \subseteq \mathsf{VP}(K) \subseteq
\mathsf{VNP}(K),$$
`VPws K` consists of polynomial families computed by polynomially sized arithmetic formulas, and
`VBP K` consists of polynomial families computed by polynomially sized algebraic branching programs
(directed acyclic graphs whose edge weights are affine-linear polynomials of total degree at most
`1`), proved under standard Lean axioms.

## Main definitions

* `CslibFrontier.IsAffineABP`: predicate that `P : MvPolynomial σ K` is computed by a topological
  algebraic branching program on `k + 2` vertices with affine-linear edge weights
  (`totalDegree ≤ 1`).
* `CslibFrontier.VPws`: Valiant's formula class $\mathsf{VP}_{\mathrm{ws}}(K)$ of
  `PolynomialFamily K` computed by polynomially sized arithmetic `Formula`s.
* `CslibFrontier.VBP`: Valiant's algebraic branching program class $\mathsf{VBP}(K)$ of
  `PolynomialFamily K` computed by polynomially sized affine algebraic branching programs.
* `CslibFrontier.ValiantVBPNeVNPConjecture`: Valiant's separation conjecture
  $\mathsf{VBP}(K) \neq \mathsf{VNP}(K)$.
* `CslibFrontier.ValiantDeterminantalConjecture`: Valiant's superpolynomial
  determinantal-complexity conjecture for the permanent family $\mathrm{per}_m$ over `K`.

## Main results

* `CslibFrontier.hasDeterminantalRepresentation_of_isAffineABP`,
  `CslibFrontier.determinantalComplexity_le_of_isAffineABP`: an affine ABP on `k + 2` vertices
  yields a `(k + 1) × (k + 1)` determinantal representation (`dc(P) ≤ k + 1`).
* `CslibFrontier.isAffineABP_det_of_totalDegree_le_one`,
  `CslibFrontier.isAffineABP_of_hasDeterminantalRepresentation`,
  `CslibFrontier.isAffineABP_of_isProjection_det`: Bird's division-free determinant iteration
  simulates any `m × m` affine-linear determinant by an affine ABP of size `m ^ 3 + 2`.
* `CslibFrontier.exists_isProjection_det_of_isAffineABP`: every `(k + 2)`-vertex affine ABP over
  `Fin n` variables subdivides into a projection of `(genericMatrix K m).det` of polynomial
  size.
* `CslibFrontier.mem_VBP_iff_determinantalComplexity`,
  `CslibFrontier.mem_VBP_iff_isPProjection_detFamily`: **universality of the determinant for
  `VBP`** — `f ∈ VBP K` if and only if `f.vars` and `determinantalComplexity (f.poly ·)` are
  polynomially bounded, and if and only if `f.vars` is polynomially bounded and `f` is a
  `p`-projection of `detFamily K`.
* `CslibFrontier.VPws_subset_VBP`, `CslibFrontier.VBP_subset_VP`, `CslibFrontier.VPws_subset_VP`,
  `CslibFrontier.detFamily_mem_VBP`: the hierarchy inclusions
  `VPws K ⊆ VBP K ⊆ VP K ⊆ VNP K` and membership `detFamily K ∈ VBP K`.
* `CslibFrontier.valiantVBPNeVNPConjecture_iff_of_isVNPComplete`: when `permFamily K` is
  `VNP`-complete, `ValiantVBPNeVNPConjecture K ↔ ValiantDeterminantalConjecture K`.

## Tags

algebraic complexity, algebraic branching program, VBP, determinantal complexity, permanent
-/

public section

open MvPolynomial Cslib Cslib.Circuits Cslib.Circuits.Arithmetic
open scoped Matrix

namespace CslibFrontier

universe u

section AffineABP

variable {K : Type u} [CommRing K] {σ : Type*}

private theorem fin_last_ne_zero (m : ℕ) : Fin.last (m + 1) ≠ 0 :=
  fun h ↦ Nat.succ_ne_zero m (congrArg Fin.val h)

/-- A multivariate polynomial `P : MvPolynomial σ K` is computed by an *affine algebraic branching
program* of internal budget `k` (total vertex count `k + 2`) if there is a strictly
upper-triangular `(k + 2) × (k + 2)` matrix `N` of affine-linear polynomials (`totalDegree ≤ 1`)
whose source-to-vertex path-sum vector `q = Pi.single 0 1 + q ᵥ* N` evaluates to `P` at the sink
`Fin.last (k + 1)`. -/
def IsAffineABP (k : ℕ) (P : MvPolynomial σ K) : Prop :=
  ∃ (N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial σ K))
    (q : Fin (k + 2) → MvPolynomial σ K),
    (∀ i j, (N i j).totalDegree ≤ 1) ∧ (∀ i j, j ≤ i → N i j = 0) ∧
      q = Pi.single 0 1 + q ᵥ* N ∧ q (Fin.last (k + 1)) = P

/-- Explicit characterization of `IsAffineABP`. -/
theorem isAffineABP_iff {k : ℕ} {P : MvPolynomial σ K} :
    IsAffineABP k P ↔
      ∃ (N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial σ K))
        (q : Fin (k + 2) → MvPolynomial σ K),
        (∀ i j, (N i j).totalDegree ≤ 1) ∧ (∀ i j, j ≤ i → N i j = 0) ∧
          q = Pi.single 0 1 + q ᵥ* N ∧ q (Fin.last (k + 1)) = P :=
  Iff.rfl

/-- Every single affine-linear polynomial (`totalDegree ≤ 1`) is computed by a `2`-vertex affine
algebraic branching program (`k = 0`). -/
theorem isAffineABP_zero_of_totalDegree_le_one {P : MvPolynomial σ K} (hP : P.totalDegree ≤ 1) :
    IsAffineABP 0 P := by
  refine ⟨Matrix.of fun i j ↦ if i = 0 ∧ j = 1 then P else 0,
    fun i ↦ if i = 0 then 1 else P, fun i j ↦ ?_, fun i j hji ↦ ?_, ?_, rfl⟩
  · simp only [Matrix.of_apply]
    split_ifs
    · exact hP
    · simp
  · simp only [Matrix.of_apply, ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    exact absurd hji (by decide)
  · refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
      simp [Matrix.vecMul, dotProduct]

/-- Monotonicity of `IsAffineABP` in the vertex budget `k`: padding with isolated vertices before
the sink preserves the computed polynomial. -/
theorem IsAffineABP.mono {k₁ k₂ : ℕ} {P : MvPolynomial σ K} (h : IsAffineABP k₁ P)
    (hle : k₁ ≤ k₂) : IsAffineABP k₂ P := by
  obtain ⟨N, q, hdeg, htri, hq, rfl⟩ := h
  let emb : Fin (k₁ + 2) → Fin (k₂ + 2) := fun i ↦
    if hi : i.val ≤ k₁ then ⟨i.val, by omega⟩ else Fin.last (k₂ + 1)
  let emb₀ : Fin (k₁ + 1) ↪ Fin (k₂ + 2) :=
    ⟨fun u ↦ ⟨u.val, by omega⟩, fun a b hab ↦ Fin.ext (by simpa using congrArg Fin.val hab)⟩
  let N' : Matrix (Fin (k₂ + 2)) (Fin (k₂ + 2)) (MvPolynomial σ K) :=
    Matrix.of fun u v ↦
      if hu : u.val ≤ k₁ then
        if hv : v.val ≤ k₁ then N ⟨u.val, by omega⟩ ⟨v.val, by omega⟩
        else if v = Fin.last (k₂ + 1) then N ⟨u.val, by omega⟩ (Fin.last (k₁ + 1))
        else 0
      else 0
  let q' : Fin (k₂ + 2) → MvPolynomial σ K := fun u ↦
    if hu : u.val ≤ k₁ then q ⟨u.val, by omega⟩
    else if u = Fin.last (k₂ + 1) then q (Fin.last (k₁ + 1))
    else 0
  refine ⟨N', q', fun u v ↦ ?_, fun u v hvu ↦ ?_, ?_, ?_⟩
  · simp only [N', Matrix.of_apply]
    split_ifs <;> first | exact hdeg _ _ | simp
  · simp only [N', Matrix.of_apply]
    split_ifs with hu hv hlast
    · exact htri ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ (Fin.le_iff_val_le_val.mpr hvu)
    · exfalso; have hv_val : v.val = k₂ + 1 := by simp [hlast]
      have : v.val ≤ u.val := hvu; omega
    · rfl
    · rfl
  · funext v
    have hvm : ∀ w : Fin (k₁ + 2), (q' ᵥ* N') (emb w) = (q ᵥ* N) w := by
      intro w
      rw [Matrix.vecMul, dotProduct, Matrix.vecMul, dotProduct]
      have hsplit : ∑ u : Fin (k₂ + 2), q' u * N' u (emb w) =
          ∑ u : Fin (k₁ + 1), q' (emb₀ u) * N' (emb₀ u) (emb w) := by
        rw [← Finset.sum_map Finset.univ emb₀ (fun u ↦ q' u * N' u (emb w))]
        refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb ↦ ?_).symm
        have hnot : ¬ b.val ≤ k₁ := by
          intro hle'
          apply hb
          rw [Finset.mem_map]
          exact ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
        simp [N', hnot]
      rw [hsplit, Fin.sum_univ_castSucc (n := k₁ + 1)]
      rw [htri (Fin.last (k₁ + 1)) w (Fin.le_last w), mul_zero, add_zero]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      have hu : u.val ≤ k₁ := Nat.lt_succ_iff.mp u.isLt
      have hemb₀ : emb₀ u = ⟨u.val, by omega⟩ := rfl
      have hcast : u.castSucc = ⟨u.val, by omega⟩ := rfl
      rw [hemb₀, hcast]
      by_cases hw : w.val ≤ k₁
      · simp [q', N', hu, emb, hw]
      · have hw_eq : w = Fin.last (k₁ + 1) := Fin.ext (by simp; omega)
        subst hw_eq
        have hnot1 : ¬ (k₁ + 1 ≤ k₁) := by omega
        have hnot2 : ¬ (k₂ + 1 ≤ k₁) := by omega
        simp only [q', N', Matrix.of_apply, emb, Fin.val_last, hu, hnot1, hnot2, ↓reduceDIte,
          ↓reduceIte]
    by_cases hv : v.val ≤ k₁
    · have hv_emb : v = emb ⟨v.val, by omega⟩ := by ext; simp [emb, hv]
      rw [Pi.add_apply, hv_emb, hvm]
      have hq_at := congrFun hq ⟨v.val, by omega⟩
      simp only [Pi.add_apply] at hq_at
      have hsingle : (Pi.single 0 1 : Fin (k₂ + 2) → MvPolynomial σ K) (emb ⟨v.val, by omega⟩) =
          (Pi.single 0 1 : Fin (k₁ + 2) → MvPolynomial σ K) ⟨v.val, by omega⟩ := by
        by_cases hv0 : v.val = 0
        · have h1 : emb ⟨v.val, by omega⟩ = 0 := by ext; simp [emb, hv0]
          have h2 : (⟨v.val, by omega⟩ : Fin (k₁ + 2)) = 0 := by ext; exact hv0
          rw [h1, h2, Pi.single_eq_same, Pi.single_eq_same]
        · have hne1 : emb ⟨v.val, by omega⟩ ≠ 0 := by
            intro h
            exact hv0 (by simpa [emb, hv] using congrArg Fin.val h)
          have hne2 : (⟨v.val, by omega⟩ : Fin (k₁ + 2)) ≠ 0 := by
            intro h
            exact hv0 (congrArg Fin.val h)
          rw [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2]
      have hq'_emb : q' (emb ⟨v.val, by omega⟩) = q ⟨v.val, by omega⟩ := by
        simp [q', emb, hv]
      rw [hq'_emb, hsingle, hq_at]
    · by_cases hlast : v = Fin.last (k₂ + 1)
      · subst hlast
        have hemb_last : Fin.last (k₂ + 1) = emb (Fin.last (k₁ + 1)) := by
          ext; simp [emb]
        have hnot : ¬ (Fin.last (k₂ + 1) : Fin (k₂ + 2)).val ≤ k₁ := by simp; omega
        rw [Pi.add_apply, Pi.single_eq_of_ne (fin_last_ne_zero _), zero_add]
        rw [hemb_last, hvm]
        have hq_last := congrFun hq (Fin.last (k₁ + 1))
        simp only [Pi.add_apply, Pi.single_eq_of_ne (fin_last_ne_zero _), zero_add] at hq_last
        have hq'_last : q' (emb (Fin.last (k₁ + 1))) = q (Fin.last (k₁ + 1)) := by
          rw [← hemb_last]
          simp only [q', hnot, ↓reduceDIte, ↓reduceIte]
        rw [hq'_last, hq_last]
      · rw [Pi.add_apply, Pi.single_eq_of_ne (by intro h; subst h; simp at hv), zero_add]
        simp only [q', hv, ↓reduceDIte, hlast, ↓reduceIte]
        rw [Matrix.vecMul, dotProduct]
        refine (Finset.sum_eq_zero fun u _ ↦ ?_).symm
        simp [N', hv, hlast]
  · have hnot : ¬ (Fin.last (k₂ + 1) : Fin (k₂ + 2)).val ≤ k₁ := by simp; omega
    simp only [q', hnot, ↓reduceDIte, ↓reduceIte]

/-- **Affine ABPs yield determinantal representations**: if `P` is computed by an affine algebraic
branching program on `k + 2` vertices, then `P` is the determinant of a `(k + 1) × (k + 1)` matrix
of affine-linear polynomials. -/
theorem hasDeterminantalRepresentation_of_isAffineABP {k : ℕ} {P : MvPolynomial σ K}
    (h : IsAffineABP k P) : HasDeterminantalRepresentation P (k + 1) := by
  obtain ⟨N, q, hdeg, htri, hq, rfl⟩ := h
  refine ⟨(N - 1).submatrix Fin.castSucc Fin.succ, fun a b ↦ ?_,
    (Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul N htri hq).symm⟩
  simp only [Matrix.submatrix_apply, Matrix.sub_apply]
  by_cases hab : a.castSucc = b.succ
  · rw [htri a.castSucc b.succ hab.symm.le, hab, Matrix.one_apply_eq, zero_sub,
      show (-1 : MvPolynomial σ K) = C (-1 : K) by simp, totalDegree_C]
    exact Nat.zero_le 1
  · rw [Matrix.one_apply_ne hab, sub_zero]
    exact hdeg a.castSucc b.succ

/-- An affine algebraic branching program on `k + 2` vertices bounds `determinantalComplexity P`
by `k + 1`. -/
theorem determinantalComplexity_le_of_isAffineABP {k : ℕ} {P : MvPolynomial σ K}
    (h : IsAffineABP k P) : determinantalComplexity P ≤ k + 1 :=
  determinantalComplexity_le (hasDeterminantalRepresentation_of_isAffineABP h)

/-- Helper: any `T`-step layered linear transition of width `W` with affine-linear initial vector
`s`, affine-linear transition matrices `M t`, and scalar output vector `c` is computed by an
`IsAffineABP` of internal budget `(T + 1) * W`. -/
private theorem isAffineABP_of_layered (T W : ℕ)
    (s : Fin W → MvPolynomial σ K) (hs : ∀ j, (s j).totalDegree ≤ 1)
    (M : Fin T → Matrix (Fin W) (Fin W) (MvPolynomial σ K))
    (hM : ∀ t i j, (M t i j).totalDegree ≤ 1)
    (c : Fin W → K) :
    let layerVec : ℕ → Fin W → MvPolynomial σ K := fun t ↦
      Nat.rec s (fun r vr ↦ if hr : r < T then vr ᵥ* M ⟨r, hr⟩ else 0) t
    IsAffineABP ((T + 1) * W) (∑ j : Fin W, layerVec T j * C (c j)) := by
  intro layerVec
  cases W with
  | zero =>
    simp only [Nat.mul_zero, Finset.univ_eq_empty, Finset.sum_empty]
    exact isAffineABP_zero_of_totalDegree_le_one (by simp)
  | succ w =>
    have hWpos : 0 < w + 1 := Nat.succ_pos w
    let N : Matrix (Fin ((T + 1) * (w + 1) + 2)) (Fin ((T + 1) * (w + 1) + 2))
        (MvPolynomial σ K) :=
      Matrix.of fun u v ↦
        if u = 0 then
          if hv : 1 ≤ v.val ∧ v.val ≤ w + 1 then
            s ⟨v.val - 1, by omega⟩
          else 0
        else if hu : u.val ≤ (T + 1) * (w + 1) then
          if htu : (u.val - 1) / (w + 1) < T then
            if hv : 1 + ((u.val - 1) / (w + 1) + 1) * (w + 1) ≤ v.val ∧
                v.val ≤ ((u.val - 1) / (w + 1) + 2) * (w + 1) then
              M ⟨(u.val - 1) / (w + 1), htu⟩
                ⟨(u.val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩
                ⟨(v.val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩
            else 0
          else
            if v.val = (T + 1) * (w + 1) + 1 then
              C (c ⟨(u.val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩)
            else 0
        else 0
    let q : Fin ((T + 1) * (w + 1) + 2) → MvPolynomial σ K := fun u ↦
      if u = 0 then 1
      else if hu : u.val ≤ (T + 1) * (w + 1) then
        layerVec ((u.val - 1) / (w + 1)) ⟨(u.val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩
      else ∑ j : Fin (w + 1), layerVec T j * C (c j)
    refine ⟨N, q, fun u v ↦ ?_, fun u v hvu ↦ ?_, ?_, ?_⟩
    · simp only [N, Matrix.of_apply]
      split_ifs <;> first | exact hs _ | exact hM _ _ _ | simp
    · simp only [N, Matrix.of_apply]
      split_ifs with hu0 hv0 hu1 htu hv1 hlast
      · exfalso; subst hu0; have : v.val ≤ 0 := hvu; omega
      · rfl
      · exfalso
        have hlt_u : u.val - 1 < ((u.val - 1) / (w + 1) + 1) * (w + 1) :=
          (Nat.div_lt_iff_lt_mul hWpos).mp (Nat.lt_add_one _)
        have : v.val ≤ u.val := hvu; omega
      · rfl
      · exfalso; have : v.val ≤ u.val := hvu; omega
      · rfl
      · rfl
    · funext v
      by_cases hv0 : v = 0
      · subst hv0
        have hzero : (q ᵥ* N) 0 = 0 := by
          rw [Matrix.vecMul, dotProduct]
          refine Finset.sum_eq_zero fun u _ ↦ ?_
          have hN0 : N u 0 = 0 := by
            simp only [N, Matrix.of_apply, Fin.val_zero]
            split_ifs <;> first | rfl | (exfalso; omega)
          rw [hN0, mul_zero]
        rw [Pi.add_apply, Pi.single_eq_same, hzero, add_zero]
        simp only [q, ↓reduceIte]
      · have hv_ge1 : 1 ≤ v.val :=
          Nat.pos_iff_ne_zero.mpr (fun h ↦ hv0 (Fin.ext h))
        rw [Pi.add_apply, Pi.single_eq_of_ne hv0, zero_add]
        by_cases hv1 : v.val ≤ (T + 1) * (w + 1)
        · have hv_decomp :
              ((v.val - 1) / (w + 1)) * (w + 1) + (v.val - 1) % (w + 1) = v.val - 1 :=
            Nat.div_add_mod' (v.val - 1) (w + 1)
          have hv_mod_lt : (v.val - 1) % (w + 1) < w + 1 := Nat.mod_lt _ hWpos
          have htv_le : (v.val - 1) / (w + 1) ≤ T := by
            have hmul_lt : ((v.val - 1) / (w + 1)) * (w + 1) < (T + 1) * (w + 1) := by omega
            exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right hWpos).mp hmul_lt)
          have hq_v : q v = layerVec ((v.val - 1) / (w + 1))
              ⟨(v.val - 1) % (w + 1), hv_mod_lt⟩ := by
            simp only [q, hv0, ↓reduceIte, hv1, ↓reduceDIte]
          rw [hq_v]
          cases htv_eq : (v.val - 1) / (w + 1) with
          | zero =>
            rw [htv_eq] at hv_decomp
            have hv_leW : v.val ≤ w + 1 := by omega
            have hjv_eq : (⟨v.val - 1, by omega⟩ : Fin (w + 1)) =
                ⟨(v.val - 1) % (w + 1), hv_mod_lt⟩ := by
              ext; dsimp; omega
            rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single 0]
            · simp only [q, N, Matrix.of_apply, ↓reduceIte, hv_ge1, hv_leW, and_self,
                ↓reduceDIte, one_mul, hjv_eq, layerVec]
              rfl
            · intro u _ hu0'
              have hu_pos : 1 ≤ u.val :=
                Nat.pos_iff_ne_zero.mpr (fun h ↦ hu0' (Fin.ext h))
              have hN0 : N u v = 0 := by
                simp only [N, Matrix.of_apply, hu0', ↓reduceIte]
                split_ifs with h1 h2 h3 h4
                · exfalso
                  have : 1 + (w + 1) ≤ 1 + ((u.val - 1) / (w + 1) + 1) * (w + 1) := by
                    have := Nat.succ_pos ((u.val - 1) / (w + 1)); nlinarith
                  omega
                · rfl
                · exfalso; have := Nat.succ_pos T; nlinarith
                · rfl
                · rfl
              rw [hN0, mul_zero]
            · intro h; exact absurd (Finset.mem_univ _) h
          | succ t' =>
            rw [htv_eq] at hv_decomp htv_le
            have ht'_lt : t' < T := Nat.lt_of_succ_le htv_le
            let jv : Fin (w + 1) := ⟨(v.val - 1) % (w + 1), hv_mod_lt⟩
            have hlayer : layerVec (t' + 1) jv =
                ∑ i : Fin (w + 1), layerVec t' i * M ⟨t', ht'_lt⟩ i jv := by
              change (if hr : t' < T then layerVec t' ᵥ* M ⟨t', hr⟩ else 0) jv = _
              simp only [ht'_lt, ↓reduceDIte, Matrix.vecMul, dotProduct]
            rw [hlayer, Matrix.vecMul, dotProduct]
            let embLayer : Fin (w + 1) ↪ Fin ((T + 1) * (w + 1) + 2) :=
              ⟨fun i ↦ ⟨1 + t' * (w + 1) + i.val, by
                have := i.isLt
                have := Nat.mul_le_mul_right (w + 1) ht'_lt; nlinarith⟩,
               fun a b hab ↦ Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)⟩
            have hembLayer_val : ∀ i : Fin (w + 1),
                (embLayer i).val = 1 + t' * (w + 1) + i.val := fun _ ↦ rfl
            have hv_lo : 1 + (t' + 1) * (w + 1) ≤ v.val := by omega
            have hv_hi : v.val ≤ (t' + 2) * (w + 1) := by
              have hstep_mul : (t' + 2) * (w + 1) = (t' + 1) * (w + 1) + (w + 1) := by ring
              omega
            have hsum_sub : ∑ u : Fin ((T + 1) * (w + 1) + 2), q u * N u v =
                ∑ i : Fin (w + 1), q (embLayer i) * N (embLayer i) v := by
              rw [← Finset.sum_map Finset.univ embLayer (fun u ↦ q u * N u v)]
              refine (Finset.sum_subset (Finset.subset_univ _) fun u _ hu_not ↦ ?_).symm
              by_cases hu0' : u = 0
              · subst hu0'
                have hv_gt : ¬ (1 ≤ v.val ∧ v.val ≤ w + 1) := fun ⟨_, _⟩ ↦ by nlinarith [hv_lo]
                simp only [N, Matrix.of_apply, ↓reduceIte, hv_gt, ↓reduceDIte, mul_zero]
              · have hu_pos : 1 ≤ u.val := Nat.pos_iff_ne_zero.mpr (fun h ↦ hu0' (Fin.ext h))
                by_cases hu_le : u.val ≤ (T + 1) * (w + 1)
                · by_cases htu_eq : (u.val - 1) / (w + 1) = t'
                  · exfalso; apply hu_not; rw [Finset.mem_map]
                    refine ⟨⟨(u.val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩,
                      Finset.mem_univ _, Fin.ext ?_⟩
                    rw [hembLayer_val]; dsimp only
                    have hu_d := Nat.div_add_mod' (u.val - 1) (w + 1)
                    rw [htu_eq] at hu_d; omega
                  · have hN0 : N u v = 0 := by
                      simp only [N, Matrix.of_apply, hu0', ↓reduceIte, hu_le, ↓reduceDIte]
                      split_ifs with htu_lt hv_band hv_end
                      · exfalso
                        have h1' := (Nat.mul_lt_mul_right hWpos).mp
                          (show ((u.val - 1) / (w + 1) + 1) * (w + 1) < (t' + 2) * (w + 1) by
                            have := hv_band.1; omega)
                        have h2' := (Nat.mul_lt_mul_right hWpos).mp
                          (show (t' + 1) * (w + 1) < ((u.val - 1) / (w + 1) + 2) * (w + 1) by
                            have := hv_band.2; omega)
                        omega
                      · rfl
                      · exfalso; omega
                      · rfl
                    rw [hN0, mul_zero]
                · simp only [N, Matrix.of_apply, hu0', ↓reduceIte, hu_le, ↓reduceDIte, mul_zero]
            rw [hsum_sub]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have hemb_ne0 : embLayer i ≠ 0 := by
              intro h; have h0 := congrArg Fin.val h; rw [hembLayer_val] at h0; simp at h0
            have hemb_le : (embLayer i).val ≤ (T + 1) * (w + 1) := by
              rw [hembLayer_val]
              have := i.isLt
              have : (t' + 1) * (w + 1) ≤ T * (w + 1) := Nat.mul_le_mul_right (w + 1) ht'_lt
              nlinarith
            have hdiv_i : ((embLayer i).val - 1) / (w + 1) = t' := by
              rw [hembLayer_val]
              have hrew : 1 + t' * (w + 1) + i.val - 1 = i.val + t' * (w + 1) := by omega
              rw [hrew, Nat.add_mul_div_right _ _ hWpos, Nat.div_eq_zero_iff.mpr (Or.inr i.isLt),
                zero_add]
            have hmod_i : ((embLayer i).val - 1) % (w + 1) = i.val := by
              rw [hembLayer_val]
              have hrew : 1 + t' * (w + 1) + i.val - 1 = i.val + t' * (w + 1) := by omega
              rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
            have hq_i : q (embLayer i) = layerVec t' i := by
              simp only [q, hemb_ne0, ↓reduceIte, hemb_le, ↓reduceDIte, hdiv_i]
              congr 1; ext; exact hmod_i
            have hv_in : 1 + (t' + 1) * (w + 1) ≤ v.val ∧ v.val ≤ (t' + 2) * (w + 1) :=
              ⟨hv_lo, hv_hi⟩
            have hN_i : N (embLayer i) v = M ⟨t', ht'_lt⟩ i jv := by
              have htu_i : ((embLayer i).val - 1) / (w + 1) < T := hdiv_i.symm ▸ ht'_lt
              have hv_band_i : 1 + (((embLayer i).val - 1) / (w + 1) + 1) * (w + 1) ≤ v.val ∧
                  v.val ≤ (((embLayer i).val - 1) / (w + 1) + 2) * (w + 1) := by
                rwa [hdiv_i]
              simp only [N, Matrix.of_apply, hemb_ne0, ↓reduceIte, hemb_le, htu_i, hv_band_i,
                and_self, ↓reduceDIte]
              have htu_eq' : (⟨((embLayer i).val - 1) / (w + 1), htu_i⟩ : Fin T) =
                  ⟨t', ht'_lt⟩ := by ext; exact hdiv_i
              have hiu_eq' :
                  (⟨((embLayer i).val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩ : Fin (w + 1)) =
                  i := by ext; exact hmod_i
              rw [htu_eq', hiu_eq']
            rw [hq_i, hN_i]
        · have hv_last : v.val = (T + 1) * (w + 1) + 1 := by
            have := v.isLt; omega
          have hq_v : q v = ∑ j : Fin (w + 1), layerVec T j * C (c j) := by
            simp only [q, hv0, ↓reduceIte, hv1, ↓reduceDIte]
          rw [hq_v, Matrix.vecMul, dotProduct]
          let embTop : Fin (w + 1) ↪ Fin ((T + 1) * (w + 1) + 2) :=
            ⟨fun i ↦ ⟨1 + T * (w + 1) + i.val, by have := i.isLt; nlinarith⟩,
             fun a b hab ↦ Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)⟩
          have hembTop_val : ∀ i : Fin (w + 1),
              (embTop i).val = 1 + T * (w + 1) + i.val := fun _ ↦ rfl
          have hsum_top : ∑ u : Fin ((T + 1) * (w + 1) + 2), q u * N u v =
              ∑ i : Fin (w + 1), q (embTop i) * N (embTop i) v := by
            rw [← Finset.sum_map Finset.univ embTop (fun u ↦ q u * N u v)]
            refine (Finset.sum_subset (Finset.subset_univ _) fun u _ hu_not ↦ ?_).symm
            by_cases hu0' : u = 0
            · subst hu0'
              have hv_gt : ¬ (1 ≤ v.val ∧ v.val ≤ w + 1) := fun ⟨_, hle_w⟩ ↦ by
                have hmul1 : 1 * (w + 1) ≤ (T + 1) * (w + 1) :=
                  Nat.mul_le_mul_right (w + 1) (Nat.succ_pos T)
                omega
              simp only [N, Matrix.of_apply, ↓reduceIte, hv_gt, ↓reduceDIte, mul_zero]
            · have hu_pos : 1 ≤ u.val :=
                Nat.pos_iff_ne_zero.mpr (fun h ↦ hu0' (Fin.ext h))
              by_cases hu_le : u.val ≤ (T + 1) * (w + 1)
              · by_cases htu_lt : (u.val - 1) / (w + 1) < T
                · have hv_out : ¬ (1 + ((u.val - 1) / (w + 1) + 1) * (w + 1) ≤ v.val ∧
                      v.val ≤ ((u.val - 1) / (w + 1) + 2) * (w + 1)) := by
                    have : ((u.val - 1) / (w + 1) + 2) * (w + 1) ≤ (T + 1) * (w + 1) :=
                      Nat.mul_le_mul_right (w + 1) (by omega)
                    omega
                  simp only [N, Matrix.of_apply, hu0', ↓reduceIte, hu_le, htu_lt, hv_out,
                    ↓reduceDIte, mul_zero]
                · exfalso
                  have htu_le : (u.val - 1) / (w + 1) ≤ T := by
                    have hmul_lt : ((u.val - 1) / (w + 1)) * (w + 1) < (T + 1) * (w + 1) := by
                      have := Nat.div_mul_le_self (u.val - 1) (w + 1)
                      omega
                    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right hWpos).mp hmul_lt)
                  have htu_eq : (u.val - 1) / (w + 1) = T := by omega
                  apply hu_not
                  rw [Finset.mem_map]
                  refine ⟨⟨(u.val - 1) % (w + 1), Nat.mod_lt _ hWpos⟩,
                    Finset.mem_univ _, Fin.ext ?_⟩
                  rw [hembTop_val]
                  dsimp only
                  have hu_d := Nat.div_add_mod' (u.val - 1) (w + 1)
                  rw [htu_eq] at hu_d
                  omega
              · simp only [N, Matrix.of_apply, hu0', ↓reduceIte, hu_le, ↓reduceDIte, mul_zero]
          rw [hsum_top]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hemb_ne0 : embTop i ≠ 0 := by
            intro h; have h0 := congrArg Fin.val h; rw [hembTop_val] at h0; simp at h0
          have hemb_le : (embTop i).val ≤ (T + 1) * (w + 1) := by
            rw [hembTop_val]; have := i.isLt; nlinarith
          have hdiv_i : ((embTop i).val - 1) / (w + 1) = T := by
            rw [hembTop_val]
            have hrew : 1 + T * (w + 1) + i.val - 1 = i.val + T * (w + 1) := by omega
            rw [hrew, Nat.add_mul_div_right _ _ hWpos, Nat.div_eq_zero_iff.mpr (Or.inr i.isLt),
              zero_add]
          have hmod_i : ((embTop i).val - 1) % (w + 1) = i.val := by
            rw [hembTop_val]
            have hrew : 1 + T * (w + 1) + i.val - 1 = i.val + T * (w + 1) := by omega
            rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
          have hq_i : q (embTop i) = layerVec T i := by
            simp only [q, hemb_ne0, ↓reduceIte, hemb_le, ↓reduceDIte, hdiv_i]
            congr 1; ext; exact hmod_i
          have hnot_lt : ¬ ((embTop i).val - 1) / (w + 1) < T := by
            rw [hdiv_i]; exact Nat.lt_irrefl T
          have hN_i : N (embTop i) v = C (c i) := by
            simp only [N, Matrix.of_apply, hemb_ne0, ↓reduceIte, hemb_le, ↓reduceDIte,
              hnot_lt, hv_last]
            congr 2; ext; exact hmod_i
          rw [hq_i, hN_i]
    · have hne0 : Fin.last ((T + 1) * (w + 1) + 1) ≠ 0 := fin_last_ne_zero _
      have hnot_le : ¬ (Fin.last ((T + 1) * (w + 1) + 1)).val ≤ (T + 1) * (w + 1) := by simp
      simp only [q, hne0, ↓reduceIte, hnot_le, ↓reduceDIte]

/-- **Bird's division-free determinant as an affine ABP**: every `m × m` matrix `A` of
affine-linear polynomials (`totalDegree ≤ 1`) over any commutative ring `K` has determinant
computed by an affine algebraic branching program of internal budget `m ^ 3`. -/
theorem isAffineABP_det_of_totalDegree_le_one {m : ℕ}
    {A : Matrix (Fin m) (Fin m) (MvPolynomial σ K)} (hA : ∀ i j, (A i j).totalDegree ≤ 1) :
    IsAffineABP (m ^ 3) A.det := by
  cases m with
  | zero =>
    simpa only [Matrix.det_fin_zero, Nat.zero_pow (by decide : 0 < 3)] using
      isAffineABP_zero_of_totalDegree_le_one (K := K) (σ := σ) (P := 1) (by simp)
  | succ k =>
    let n := k + 1
    let W := n * n
    let e_v : Fin n × Fin n ≃ Fin W := finProdFinEquiv
    let s : Fin W → MvPolynomial σ K := fun e ↦ A (e_v.symm e).1 (e_v.symm e).2
    let B : Matrix (Fin W) (Fin W) (MvPolynomial σ K) := fun e₁ e₂ ↦
      let p₁ := e_v.symm e₁
      let p₂ := e_v.symm e₂
      if p₁.1 = p₁.2 ∧ p₂.1 < p₁.1 then -A p₂.1 p₂.2
      else if p₁.1 = p₂.1 ∧ p₂.1 < p₁.2 then A p₁.2 p₂.2
      else 0
    let c : Fin W → K := fun e ↦ if e = e_v (0, 0) then (-1) ^ k else 0
    have hs : ∀ e, (s e).totalDegree ≤ 1 := fun e ↦ hA _ _
    have hB : ∀ (_ : Fin k) e₁ e₂, (B e₁ e₂).totalDegree ≤ 1 := by
      intro _ e₁ e₂
      dsimp only [B]
      split_ifs
      · rw [show -A (e_v.symm e₂).1 (e_v.symm e₂).2 =
            C (-1 : K) * A (e_v.symm e₂).1 (e_v.symm e₂).2 by simp]
        exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hA _ _)
      · exact hA _ _
      · simp
    have hlay := isAffineABP_of_layered (K := K) (σ := σ) k W s hs (fun _ ↦ B) hB c
    dsimp only at hlay
    set layerVec : ℕ → Fin W → MvPolynomial σ K := fun t ↦
      Nat.rec s (fun r vr ↦ if hr : r < k then vr ᵥ* B else 0) t
    have hbird : ∀ t ≤ k, ∀ i j : Fin n,
        layerVec t (e_v (i, j)) = ((BirdDet.Spec.stepEntry A)^[t] A) i j := by
      intro t ht
      induction t with
      | zero =>
        intro i j
        simp [layerVec, s]
      | succ t ih =>
        intro i j
        have htk : t < k := Nat.lt_of_succ_le ht
        let M_t : Matrix (Fin n) (Fin n) (MvPolynomial σ K) := (BirdDet.Spec.stepEntry A)^[t] A
        have ih' : ∀ a b : Fin n, layerVec t (e_v (a, b)) = M_t a b := ih (Nat.le_of_lt htk)
        have hstep : layerVec (t + 1) (e_v (i, j)) = (layerVec t ᵥ* B) (e_v (i, j)) := by
          change (if hr : t < k then layerVec t ᵥ* B else 0) (e_v (i, j)) = _
          simp only [htk, ↓reduceDIte]
        rw [hstep, Matrix.vecMul, dotProduct, ← e_v.sum_comp, Fintype.sum_prod_type]
        have hrew : ∀ r s' : Fin n,
            layerVec t (e_v (r, s')) * B (e_v (r, s')) (e_v (i, j)) =
              M_t r s' *
                (if r = s' ∧ i < r then -A i j else if r = i ∧ i < s' then A s' j else 0) := by
          intro r s'
          rw [ih' r s']
          have hBeval : B (e_v (r, s')) (e_v (i, j)) =
              if r = s' ∧ i < r then -A i j else if r = i ∧ i < s' then A s' j else 0 := by
            change (if (e_v.symm (e_v (r, s'))).1 = (e_v.symm (e_v (r, s'))).2 ∧
                (e_v.symm (e_v (i, j))).1 < (e_v.symm (e_v (r, s'))).1 then
                -A (e_v.symm (e_v (i, j))).1 (e_v.symm (e_v (i, j))).2
              else if (e_v.symm (e_v (r, s'))).1 = (e_v.symm (e_v (i, j))).1 ∧
                (e_v.symm (e_v (i, j))).1 < (e_v.symm (e_v (r, s'))).2 then
                A (e_v.symm (e_v (r, s'))).2 (e_v.symm (e_v (i, j))).2
              else 0) = _
            simp only [Equiv.symm_apply_apply]
          rw [hBeval]
        have hsum_rew :
            (∑ r : Fin n, ∑ s' : Fin n,
              layerVec t (e_v (r, s')) * B (e_v (r, s')) (e_v (i, j))) =
              ∑ r : Fin n, ∑ s' : Fin n, M_t r s' *
                (if r = s' ∧ i < r then -A i j else if r = i ∧ i < s' then A s' j else 0) :=
          Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s' _ ↦ hrew r s'
        rw [hsum_rew]
        have hinner : ∀ r : Fin n,
            (∑ s' : Fin n, M_t r s' *
              (if r = s' ∧ i < r then -A i j else if r = i ∧ i < s' then A s' j else 0)) =
              (if i < r then -(M_t r r) * A i j else 0) +
              (if r = i then ∑ s' ∈ Finset.Ioi i, M_t i s' * A s' j else 0) := by
          intro r
          by_cases hri : r = i
          · subst hri
            simp only [lt_irrefl, and_false, ↓reduceIte, true_and, zero_add, mul_ite, mul_zero,
              ← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
          · simp only [hri, false_and, ↓reduceIte, add_zero]
            by_cases hir : i < r
            · simp only [hir, ↓reduceIte]
              rw [Finset.sum_eq_single r]
              · simp [neg_mul]
              · intro s' _ hs'r
                simp [hs'r.symm]
              · intro h; exact absurd (Finset.mem_univ _) h
            · simp only [hir, ↓reduceIte]
              exact Finset.sum_eq_zero fun _ _ ↦ by simp
        simp_rw [hinner, Finset.sum_add_distrib]
        have hsum1 : (∑ r : Fin n, if i < r then -(M_t r r) * A i j else 0) =
            (-∑ r ∈ Finset.Ioi i, M_t r r) * A i j := by
          rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, ← Finset.sum_mul,
            Finset.sum_neg_distrib]
        have hsum2 : (∑ r : Fin n, if r = i then
            ∑ s' ∈ Finset.Ioi i, M_t i s' * A s' j else 0) =
            ∑ s' ∈ Finset.Ioi i, M_t i s' * A s' j := by
          simp
        rw [hsum1, hsum2, Function.iterate_succ_apply', BirdDet.Spec.stepEntry_eq, Matrix.of_apply]
    have hout : (∑ e : Fin W, layerVec k e * C (c e)) = A.det := by
      rw [Finset.sum_eq_single (e_v (0, 0))]
      · simp only [c, ↓reduceIte, map_pow, map_neg, map_one, hbird k le_rfl 0 0]
        rw [mul_comm, ← Bird.spec_eq_det A, BirdDet.Spec.birdDetSpec_succ]
      · intro e _ he
        simp [c, he]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hpow : (k + 1) * W = (k + 1) ^ 3 := by dsimp [W, n]; ring
    rw [hout, hpow] at hlay
    exact hlay

/-- Every determinantal representation of size `m` gives an affine algebraic branching program of
internal budget `m ^ 3`. -/
theorem isAffineABP_of_hasDeterminantalRepresentation {m : ℕ} {P : MvPolynomial σ K}
    (h : HasDeterminantalRepresentation P m) : IsAffineABP (m ^ 3) P := by
  obtain ⟨A, hA, rfl⟩ := h
  exact isAffineABP_det_of_totalDegree_le_one hA

/-- Every projection of `(genericMatrix K m).det` is computed by an affine algebraic branching
program of internal budget `m ^ 3`. -/
theorem isAffineABP_of_isProjection_det {m : ℕ} {P : MvPolynomial σ K}
    (h : IsProjection P (genericMatrix K m).det) : IsAffineABP (m ^ 3) P :=
  isAffineABP_of_hasDeterminantalRepresentation (hasDeterminantalRepresentation_of_isProjection h)

private theorem eq_C_add_sum_X_of_totalDegree_le_one {n : ℕ} {p : MvPolynomial (Fin n) K}
    (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) +
      ∑ i : Fin n, C (p.coeff (Finsupp.single i 1)) * X i := by
  ext d
  have hadd : (C (p.coeff 0) + ∑ i : Fin n, C (p.coeff (Finsupp.single i 1)) * X i).coeff d =
      (C (p.coeff 0)).coeff d + (∑ i : Fin n, C (p.coeff (Finsupp.single i 1)) * X i).coeff d := by
    simpa only [lcoeff_apply] using
      map_add (lcoeff K d) (C (p.coeff 0)) (∑ i : Fin n, C (p.coeff (Finsupp.single i 1)) * X i)
  rw [hadd, coeff_C, coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  by_cases hd0 : d = 0
  · subst hd0
    simp only [↓reduceIte]
    have hsum0 : (∑ x : Fin n, p.coeff (Finsupp.single x 1) *
        if Finsupp.single x 1 = (0 : Fin n →₀ ℕ) then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      have hne : Finsupp.single x (1 : ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
      simp [hne]
    rw [hsum0, add_zero]
  · have h0d : (0 : Fin n →₀ ℕ) ≠ d := Ne.symm hd0
    simp only [h0d, ↓reduceIte, zero_add]
    by_cases hmem : d ∈ p.support
    · have hdeg : d.sum (fun _ e ↦ e) ≤ 1 := (le_totalDegree hmem).trans hp
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, d i₀ ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hd0 (Finsupp.ext hall)
      have hi₀_mem : i₀ ∈ d.support := Finsupp.mem_support_iff.mpr hi₀
      have hi₀_le : d i₀ ≤ d.sum (fun _ e ↦ e) :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi₀_mem
      have hi₀_eq : d i₀ = 1 := by omega
      have hd_eq : d = Finsupp.single i₀ 1 := by
        ext j
        by_cases hj : j = i₀
        · subst hj; simp [hi₀_eq]
        · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hj)]
          by_contra hj_ne
          have hj_mem : j ∈ d.support := Finsupp.mem_support_iff.mpr hj_ne
          have hpair : d i₀ + d j ≤ d.sum (fun _ e ↦ e) := by
            rw [Finsupp.sum, ← Finset.sum_pair (Ne.symm hj)]
            exact Finset.sum_le_sum_of_subset
              (Finset.insert_subset_iff.mpr ⟨hi₀_mem, Finset.singleton_subset_iff.mpr hj_mem⟩)
          omega
      subst hd_eq
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hji
        have hne : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i₀ 1 := by
          intro heq
          have hval : (Finsupp.single j (1 : ℕ)) j = (Finsupp.single i₀ 1) j :=
            congrArg (· j) heq
          rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hji] at hval
          exact one_ne_zero hval
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [notMem_support_iff.mp hmem]
      symm
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      by_cases heq : Finsupp.single i 1 = d
      · rw [heq, notMem_support_iff.mp hmem, zero_mul]
      · simp [heq]

private noncomputable def subdivEdgeCoeff {n V : ℕ}
    (N : Matrix (Fin V) (Fin V) (MvPolynomial (Fin n) K))
    (u v : Fin V) (t : Fin (n + 1)) : MvPolynomial (Fin n) K :=
  if ht0 : t.val = 0 then C ((N u v).coeff 0)
  else C ((N u v).coeff (Finsupp.single ⟨t.val - 1, by omega⟩ 1))

private noncomputable def subdivEdgeVar {n : ℕ} (t : Fin (n + 1)) : MvPolynomial (Fin n) K :=
  if ht0 : t.val = 0 then 1 else X ⟨t.val - 1, by omega⟩

private abbrev subdivB (n V : ℕ) : ℕ := 1 + V * (n + 1)

private abbrev subdivS (n V : ℕ) : ℕ := V * subdivB n V

private def subdivMainNode (n V : ℕ) (u : Fin V) : Fin (subdivS n V + 2) :=
  ⟨1 + u.val * subdivB n V, by
    have : (u.val + 1) * subdivB n V ≤ subdivS n V := Nat.mul_le_mul_right _ u.isLt
    nlinarith⟩

private def subdivMidNode (n V : ℕ) (u v : Fin V) (t : Fin (n + 1)) : Fin (subdivS n V + 2) :=
  ⟨1 + u.val * subdivB n V + (1 + v.val * (n + 1) + t.val), by
    have h1 : v.val * (n + 1) + t.val < V * (n + 1) := by
      have : (v.val + 1) * (n + 1) ≤ V * (n + 1) := Nat.mul_le_mul_right (n + 1) v.isLt
      have := t.isLt; nlinarith
    have h2 : (u.val + 1) * subdivB n V ≤ subdivS n V := Nat.mul_le_mul_right _ u.isLt
    dsimp [subdivB, subdivS] at *; nlinarith⟩

private noncomputable def subdivMat {n k : ℕ}
    (N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial (Fin n) K)) :
    Matrix (Fin (subdivS n (k + 2) + 2)) (Fin (subdivS n (k + 2) + 2)) (MvPolynomial (Fin n) K) :=
  have hBpos : 0 < subdivB n (k + 2) := Nat.succ_pos _
  Matrix.of fun x y ↦
    if x = 0 ∧ y = subdivMainNode n (k + 2) 0 then 1
    else if x = subdivMainNode n (k + 2) (Fin.last (k + 1)) ∧
        y = Fin.last (subdivS n (k + 2) + 1) then 1
    else if hx : ∃ u : Fin (k + 2), x = subdivMainNode n (k + 2) u then
      let u : Fin (k + 2) := ⟨(x.val - 1) / subdivB n (k + 2), by
        rcases hx with ⟨u', rfl⟩; dsimp [subdivMainNode]
        rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hBpos]; exact u'.isLt⟩
      if hy : (1 + u.val * subdivB n (k + 2) < y.val) ∧
          (y.val < 1 + (u.val + 1) * subdivB n (k + 2)) then
        let rem := y.val - (1 + u.val * subdivB n (k + 2)) - 1
        let v : Fin (k + 2) := ⟨rem / (n + 1), by
          have hlt_y : y.val < 1 + u.val * subdivB n (k + 2) + subdivB n (k + 2) := by
            have := Nat.succ_mul u.val (subdivB n (k + 2)); linarith [hy.2]
          have : rem < (k + 2) * (n + 1) := by
            change y.val - (1 + u.val * subdivB n (k + 2)) - 1 < (k + 2) * (n + 1)
            dsimp [subdivB] at *; omega
          exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr this⟩
        let t : Fin (n + 1) := ⟨rem % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
        if u < v then subdivEdgeCoeff N u v t else 0
      else 0
    else if hx2 : 1 ≤ x.val ∧ x.val ≤ subdivS n (k + 2) ∧
        (x.val - 1) % subdivB n (k + 2) ≠ 0 then
      let u : Fin (k + 2) := ⟨(x.val - 1) / subdivB n (k + 2),
        (Nat.div_lt_iff_lt_mul hBpos).mpr (by dsimp [subdivS] at *; omega)⟩
      let rem := (x.val - 1) % subdivB n (k + 2) - 1
      let v : Fin (k + 2) := ⟨rem / (n + 1), by
        have hmod := Nat.mod_lt (x.val - 1) hBpos
        have hmod_pos := Nat.pos_iff_ne_zero.mpr hx2.2.2
        have : rem < (k + 2) * (n + 1) := by
          change (x.val - 1) % subdivB n (k + 2) - 1 < (k + 2) * (n + 1)
          dsimp [subdivB] at *; omega
        exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr this⟩
      let t : Fin (n + 1) := ⟨rem % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
      if u < v ∧ y = subdivMainNode n (k + 2) v then subdivEdgeVar t else 0
    else 0

private noncomputable def subdivVec {n k : ℕ}
    (N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial (Fin n) K))
    (q : Fin (k + 2) → MvPolynomial (Fin n) K) :
    Fin (subdivS n (k + 2) + 2) → MvPolynomial (Fin n) K :=
  have hBpos : 0 < subdivB n (k + 2) := Nat.succ_pos _
  fun x ↦
    if x = 0 then 1
    else if x = Fin.last (subdivS n (k + 2) + 1) then q (Fin.last (k + 1))
    else if hx : 1 ≤ x.val ∧ x.val ≤ subdivS n (k + 2) then
      let u : Fin (k + 2) := ⟨(x.val - 1) / subdivB n (k + 2),
        (Nat.div_lt_iff_lt_mul hBpos).mpr (by dsimp [subdivS] at *; omega)⟩
      if hmod0 : (x.val - 1) % subdivB n (k + 2) = 0 then q u
      else
        let rem := (x.val - 1) % subdivB n (k + 2) - 1
        let v : Fin (k + 2) := ⟨rem / (n + 1), by
          have hmod := Nat.mod_lt (x.val - 1) hBpos
          have hmod_pos := Nat.pos_iff_ne_zero.mpr hmod0
          have : rem < (k + 2) * (n + 1) := by
            change (x.val - 1) % subdivB n (k + 2) - 1 < (k + 2) * (n + 1)
            dsimp [subdivB] at *; omega
          exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr this⟩
        let t : Fin (n + 1) := ⟨rem % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
        if u < v then q u * subdivEdgeCoeff N u v t else 0
    else 0

/-- **Subdivision from affine ABPs to determinant projections**: every `(k + 2)`-vertex affine ABP
on `Fin n` variables subdivides (replacing each affine-linear edge by `n + 1` length-`2`
scalar/variable paths) into a projection of `(genericMatrix K m).det` with
`m = (k + 2) * (1 + (k + 2) * (n + 1)) + 1`. -/
theorem exists_isProjection_det_of_isAffineABP {n k : ℕ} {P : MvPolynomial (Fin n) K}
    (h : IsAffineABP k P) :
    ∃ m ≤ (k + 2) * (1 + (k + 2) * (n + 1)) + 1,
      IsProjection P (genericMatrix K m).det := by
  obtain ⟨N, q, hdeg, htri, hq, rfl⟩ := h
  have hBpos : 0 < subdivB n (k + 2) := Nat.succ_pos _
  have hSubstCoeff : ∀ u v t, IsSubstEntry (subdivEdgeCoeff N u v t) := fun u v t ↦ by
    dsimp [subdivEdgeCoeff]; split_ifs <;> exact .C _
  have hSubstVar : ∀ t, IsSubstEntry (subdivEdgeVar (K := K) (n := n) t) := fun t ↦ by
    dsimp [subdivEdgeVar]; split_ifs <;> [exact .one; exact .X _]
  have hq0 : q 0 = 1 := by
    have h0 : (q ᵥ* N) 0 = 0 := by
      rw [Matrix.vecMul, dotProduct]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [htri i 0 (Fin.zero_le i), mul_zero]
    simpa only [Pi.add_apply, Pi.single_eq_same, h0, add_zero] using congrFun hq 0
  have hmain_div : ∀ u : Fin (k + 2),
      ((subdivMainNode n (k + 2) u).val - 1) / subdivB n (k + 2) = u.val := fun u ↦ by
    dsimp [subdivMainNode]; rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hBpos]
  have hmain_mod : ∀ u : Fin (k + 2),
      ((subdivMainNode n (k + 2) u).val - 1) % subdivB n (k + 2) = 0 := fun u ↦ by
    dsimp [subdivMainNode]; rw [Nat.add_sub_cancel_left, Nat.mul_mod_left]
  have hmain_bounds : ∀ u : Fin (k + 2),
      1 ≤ (subdivMainNode n (k + 2) u).val ∧
        (subdivMainNode n (k + 2) u).val ≤ subdivS n (k + 2) := fun u ↦ by
    refine ⟨by dsimp [subdivMainNode]; omega, ?_⟩
    have : (u.val + 1) * subdivB n (k + 2) ≤ subdivS n (k + 2) :=
      Nat.mul_le_mul_right _ u.isLt
    dsimp [subdivMainNode, subdivS] at *; nlinarith
  have hmain_ne0 : ∀ u : Fin (k + 2), subdivMainNode n (k + 2) u ≠ 0 := fun u h ↦ by
    have := (hmain_bounds u).1; rw [h] at this; simp at this
  have hmain_ne_last : ∀ u : Fin (k + 2),
      subdivMainNode n (k + 2) u ≠ Fin.last (subdivS n (k + 2) + 1) := fun u h ↦ by
    have := (hmain_bounds u).2; rw [h] at this; simp at this
  have hmid_div : ∀ u v : Fin (k + 2), ∀ t : Fin (n + 1),
      ((subdivMidNode n (k + 2) u v t).val - 1) / subdivB n (k + 2) = u.val := by
    intro u v t; dsimp [subdivMidNode]
    have hlt : 1 + v.val * (n + 1) + t.val < subdivB n (k + 2) := by
      have := Nat.mul_le_mul_right (n + 1) v.isLt; have := t.isLt; dsimp [subdivB]; nlinarith
    have hrew : 1 + u.val * subdivB n (k + 2) + (1 + v.val * (n + 1) + t.val) - 1 =
        (1 + v.val * (n + 1) + t.val) + u.val * subdivB n (k + 2) := by omega
    rw [hrew, Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_zero_iff.mpr (Or.inr hlt), zero_add]
  have hmid_mod : ∀ u v : Fin (k + 2), ∀ t : Fin (n + 1),
      ((subdivMidNode n (k + 2) u v t).val - 1) % subdivB n (k + 2) =
        1 + v.val * (n + 1) + t.val := by
    intro u v t; dsimp [subdivMidNode]
    have hlt : 1 + v.val * (n + 1) + t.val < subdivB n (k + 2) := by
      have := Nat.mul_le_mul_right (n + 1) v.isLt; have := t.isLt; dsimp [subdivB]; nlinarith
    have hrew : 1 + u.val * subdivB n (k + 2) + (1 + v.val * (n + 1) + t.val) - 1 =
        (1 + v.val * (n + 1) + t.val) + u.val * subdivB n (k + 2) := by omega
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  have hmid_bounds : ∀ u v : Fin (k + 2), ∀ t : Fin (n + 1),
      1 ≤ (subdivMidNode n (k + 2) u v t).val ∧
        (subdivMidNode n (k + 2) u v t).val ≤ subdivS n (k + 2) ∧
        ((subdivMidNode n (k + 2) u v t).val - 1) % subdivB n (k + 2) ≠ 0 := by
    intro u v t
    refine ⟨by dsimp [subdivMidNode]; omega, ?_, by rw [hmid_mod]; omega⟩
    have h1 : v.val * (n + 1) + t.val < (k + 2) * (n + 1) := by
      have := Nat.mul_le_mul_right (n + 1) v.isLt; have := t.isLt; nlinarith
    have h2 : (u.val + 1) * subdivB n (k + 2) ≤ subdivS n (k + 2) :=
      Nat.mul_le_mul_right _ u.isLt
    dsimp [subdivMidNode, subdivB, subdivS] at *; nlinarith
  have hq_main : ∀ u : Fin (k + 2), subdivVec N q (subdivMainNode n (k + 2) u) = q u := fun u ↦ by
    simp only [subdivVec, hmain_ne0 u, hmain_ne_last u, ↓reduceIte, hmain_bounds u, and_self,
      ↓reduceDIte, hmain_mod u]
    exact congrArg q (Fin.ext (hmain_div u))
  have hN'_subst : IsSubstMatrix (subdivMat N) := by
    intro x y; simp only [subdivMat, Matrix.of_apply]
    split_ifs <;> first | exact .one | exact .zero | exact hSubstCoeff _ _ _ | exact hSubstVar _
  have hN'_tri : ∀ x y, y ≤ x → subdivMat N x y = 0 := by
    intro x y hyx; simp only [subdivMat, Matrix.of_apply]
    split_ifs with h0 hlast hx hy huv hx2 huv2
    · exfalso; rcases h0 with ⟨rfl, rfl⟩
      have h0le : (subdivMainNode n (k + 2) 0).val ≤ 0 := by
        simpa only [Fin.le_iff_val_le_val, Fin.val_zero] using hyx
      dsimp [subdivMainNode] at h0le; omega
    · exfalso; rcases hlast with ⟨rfl, rfl⟩
      have hb := (hmain_bounds (Fin.last (k + 1))).2
      have hle : subdivS n (k + 2) + 1 ≤ (subdivMainNode n (k + 2) (Fin.last (k + 1))).val := by
        simpa only [Fin.le_iff_val_le_val, Fin.val_last] using hyx
      omega
    · exfalso; rcases hx with ⟨u', rfl⟩; rw [hmain_div u'] at hy
      have : (subdivMainNode n (k + 2) u').val < y.val := hy.1
      have : y.val ≤ (subdivMainNode n (k + 2) u').val := hyx; omega
    · rfl
    · rfl
    · exfalso; rcases huv2 with ⟨huv_lt, rfl⟩
      have hu_lt_v : (x.val - 1) / subdivB n (k + 2) + 1 ≤
          ((x.val - 1) % subdivB n (k + 2) - 1) / (n + 1) := huv_lt
      have hx_lt : x.val - 1 < ((x.val - 1) / subdivB n (k + 2) + 1) * subdivB n (k + 2) :=
        (Nat.div_lt_iff_lt_mul hBpos).mp (Nat.lt_add_one _)
      have hle_v : ((x.val - 1) / subdivB n (k + 2) + 1) * subdivB n (k + 2) ≤
          (((x.val - 1) % subdivB n (k + 2) - 1) / (n + 1)) * subdivB n (k + 2) :=
        Nat.mul_le_mul_right (subdivB n (k + 2)) hu_lt_v
      have hhyx : 1 + (((x.val - 1) % subdivB n (k + 2) - 1) / (n + 1)) *
          subdivB n (k + 2) ≤ x.val := hyx
      have hx1 : 1 ≤ x.val := hx2.1
      omega
    · rfl
    · rfl
  have hq'_eq : subdivVec N q = Pi.single 0 1 + subdivVec N q ᵥ* subdivMat N := by
    funext y
    by_cases hy0 : y = 0
    · subst hy0
      have hvm0 : (subdivVec N q ᵥ* subdivMat N) 0 = 0 := by
        rw [Matrix.vecMul, dotProduct]; refine Finset.sum_eq_zero fun x _ ↦ ?_
        have hN0 : subdivMat N x 0 = 0 := by
          simp only [subdivMat, Matrix.of_apply]
          split_ifs with h1 h2 hx hy _ hx2 huv2
          · exact absurd h1.2 (hmain_ne0 0).symm
          · exact absurd h2.2 (fin_last_ne_zero _).symm
          · exfalso; simp at hy
          · rfl
          · rfl
          · exact absurd huv2.2 (hmain_ne0 _).symm
          · rfl
          · rfl
        rw [hN0, mul_zero]
      rw [Pi.add_apply, Pi.single_eq_same, hvm0, add_zero]; simp only [subdivVec, ↓reduceIte]
    · rw [Pi.add_apply, Pi.single_eq_of_ne hy0, zero_add]
      by_cases hylast : y = Fin.last (subdivS n (k + 2) + 1)
      · subst hylast
        have hqlast : subdivVec N q (Fin.last (subdivS n (k + 2) + 1)) = q (Fin.last (k + 1)) := by
          simp only [subdivVec, hy0, ↓reduceIte]
        rw [hqlast, Matrix.vecMul, dotProduct,
          Finset.sum_eq_single (subdivMainNode n (k + 2) (Fin.last (k + 1)))]
        · have hN_m : subdivMat N (subdivMainNode n (k + 2) (Fin.last (k + 1)))
              (Fin.last (subdivS n (k + 2) + 1)) = 1 := by
            simp only [subdivMat, Matrix.of_apply, hmain_ne0 _, false_and, and_self, ↓reduceIte]
          rw [hq_main (Fin.last (k + 1)), hN_m, mul_one]
        · intro x _ hx_ne
          have hN0 : subdivMat N x (Fin.last (subdivS n (k + 2) + 1)) = 0 := by
            simp only [subdivMat, Matrix.of_apply]
            split_ifs with h1 h2 hx hy _ hx2 huv2
            · exact absurd h1.2 (hmain_ne_last 0).symm
            · exact absurd h2.1 hx_ne
            · exfalso
              have hu_lt : (x.val - 1) / subdivB n (k + 2) < k + 2 := by
                rcases hx with ⟨u', rfl⟩; rw [hmain_div]; exact u'.isLt
              have hmul := Nat.mul_le_mul_right (subdivB n (k + 2)) hu_lt
              simp only [Fin.val_last] at hy; linarith [hy.2, hmul]
            · rfl
            · rfl
            · exact absurd huv2.2 (hmain_ne_last _).symm
            · rfl
            · rfl
          rw [hN0, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hy_in : 1 ≤ y.val ∧ y.val ≤ subdivS n (k + 2) := by
          have hy_lt : y.val < subdivS n (k + 2) + 2 := y.isLt
          have hne_val : y.val ≠ subdivS n (k + 2) + 1 := fun h ↦ hylast (Fin.ext h)
          have hne0_val : y.val ≠ 0 := fun h ↦ hy0 (Fin.ext h)
          omega
        by_cases hymod : (y.val - 1) % subdivB n (k + 2) = 0
        · let v : Fin (k + 2) := ⟨(y.val - 1) / subdivB n (k + 2),
            (Nat.div_lt_iff_lt_mul hBpos).mpr (by dsimp [subdivS] at *; omega)⟩
          have hy_eq : y = subdivMainNode n (k + 2) v := by
            apply Fin.ext
            change y.val = 1 + ((y.val - 1) / subdivB n (k + 2)) * subdivB n (k + 2)
            have hdm := Nat.div_add_mod' (y.val - 1) (subdivB n (k + 2))
            rw [hymod, add_zero] at hdm; omega
          rw [hy_eq, hq_main v]
          by_cases hv0 : v = 0
          · rw [hv0, hq0, Matrix.vecMul, dotProduct, Finset.sum_eq_single 0]
            · have hq00 : subdivVec N q 0 = 1 := by simp only [subdivVec, ↓reduceIte]
              have hN00 : subdivMat N 0 (subdivMainNode n (k + 2) 0) = 1 := by
                simp only [subdivMat, Matrix.of_apply, and_self, ↓reduceIte]
              rw [hq00, hN00, one_mul]
            · intro x _ hx0
              have hN0 : subdivMat N x (subdivMainNode n (k + 2) 0) = 0 := by
                simp only [subdivMat, Matrix.of_apply]
                split_ifs with h1 h2 hx hy _ hx2 huv2
                · exact absurd h1.1 hx0
                · exact absurd h2.2 (hmain_ne_last 0)
                · exfalso; dsimp [subdivMainNode] at hy; omega
                · rfl
                · rfl
                · exfalso
                  have hlt_u : (x.val - 1) / subdivB n (k + 2) <
                      ((x.val - 1) % subdivB n (k + 2) - 1) / (n + 1) := huv2.1
                  have hval := congrArg Fin.val huv2.2
                  dsimp only [subdivMainNode] at hval
                  rw [Fin.val_zero, zero_mul, add_zero] at hval
                  have hmul : (((x.val - 1) % subdivB n (k + 2) - 1) / (n + 1)) *
                      subdivB n (k + 2) = 0 := by omega
                  have hv0_eq : ((x.val - 1) % subdivB n (k + 2) - 1) / (n + 1) = 0 :=
                    (Nat.mul_eq_zero.mp hmul).resolve_right (Nat.ne_of_gt hBpos)
                  rw [hv0_eq] at hlt_u
                  exact Nat.not_lt_zero _ hlt_u
                · rfl
                · rfl
              rw [hN0, mul_zero]
            · intro h; exact absurd (Finset.mem_univ _) h
          · have hqv_eq : q v = ∑ u : Fin (k + 2), if u < v then q u * N u v else 0 := by
              have h1 := congrFun hq v
              simp only [Pi.add_apply, Pi.single_eq_of_ne hv0, zero_add, Matrix.vecMul,
                dotProduct] at h1
              rw [h1]; refine Finset.sum_congr rfl fun u _ ↦ ?_
              split_ifs with huv <;> [rfl; rw [htri u v (not_lt.mp huv), mul_zero]]
            rw [hqv_eq, Matrix.vecMul, dotProduct]
            have hterm : ∀ u : Fin (k + 2), (if u < v then q u * N u v else 0) =
                ∑ t : Fin (n + 1),
                  subdivVec N q (subdivMidNode n (k + 2) u v t) *
                    subdivMat N (subdivMidNode n (k + 2) u v t) (subdivMainNode n (k + 2) v) := by
              intro u
              have hmid_eval : ∀ t : Fin (n + 1),
                  subdivVec N q (subdivMidNode n (k + 2) u v t) *
                    subdivMat N (subdivMidNode n (k + 2) u v t) (subdivMainNode n (k + 2) v) =
                    if u < v then q u * (subdivEdgeCoeff N u v t * subdivEdgeVar t) else 0 := by
                intro t
                have mb := hmid_bounds u v t
                have m0 : subdivMidNode n (k + 2) u v t ≠ 0 := fun h ↦ by
                  have := mb.1; rw [h] at this; simp at this
                have ml : subdivMidNode n (k + 2) u v t ≠ Fin.last (subdivS n (k + 2) + 1) :=
                  fun h ↦ by have := mb.2.1; rw [h] at this; simp at this
                have mnot_main : ¬ ∃ u' : Fin (k + 2),
                    subdivMidNode n (k + 2) u v t = subdivMainNode n (k + 2) u' := by
                  rintro ⟨u', heq⟩; have := mb.2.2; rw [heq, hmain_mod] at this; exact this rfl
                have hrem_div : (((subdivMidNode n (k + 2) u v t).val - 1) %
                    subdivB n (k + 2) - 1) / (n + 1) = v.val := by
                  rw [hmid_mod]
                  have hrew : 1 + v.val * (n + 1) + t.val - 1 = t.val + v.val * (n + 1) := by omega
                  rw [hrew, Nat.add_mul_div_right _ _ (Nat.succ_pos n),
                    Nat.div_eq_zero_iff.mpr (Or.inr t.isLt), zero_add]
                have hrem_mod : (((subdivMidNode n (k + 2) u v t).val - 1) %
                    subdivB n (k + 2) - 1) % (n + 1) = t.val := by
                  rw [hmid_mod]
                  have hrew : 1 + v.val * (n + 1) + t.val - 1 = t.val + v.val * (n + 1) := by omega
                  rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t.isLt]
                have hd_mid := hmid_div u v t
                have hq_mid : subdivVec N q (subdivMidNode n (k + 2) u v t) =
                    if u < v then q u * subdivEdgeCoeff N u v t else 0 := by
                  simp only [subdivVec, m0, ml, ↓reduceIte, mb.1, mb.2.1, and_self, ↓reduceDIte,
                    mb.2.2]
                  have hu_eq : ∀ h,
                      (⟨((subdivMidNode n (k + 2) u v t).val - 1) / subdivB n (k + 2), h⟩ :
                        Fin (k + 2)) = u := fun _ ↦ Fin.ext hd_mid
                  have hv_eq : ∀ h,
                      (⟨(((subdivMidNode n (k + 2) u v t).val - 1) % subdivB n (k + 2) - 1) /
                        (n + 1), h⟩ : Fin (k + 2)) = v := fun _ ↦ Fin.ext hrem_div
                  have ht_eq : ∀ h,
                      (⟨(((subdivMidNode n (k + 2) u v t).val - 1) % subdivB n (k + 2) - 1) %
                        (n + 1), h⟩ : Fin (n + 1)) = t := fun _ ↦ Fin.ext hrem_mod
                  simp only [hu_eq, hv_eq, ht_eq]
                have hN_mid : subdivMat N (subdivMidNode n (k + 2) u v t)
                    (subdivMainNode n (k + 2) v) =
                    if u < v then subdivEdgeVar t else 0 := by
                  have hnot1 : ¬ (subdivMidNode n (k + 2) u v t = 0 ∧
                      subdivMainNode n (k + 2) v = subdivMainNode n (k + 2) 0) := fun h ↦ m0 h.1
                  have hnot2 : ¬ (subdivMidNode n (k + 2) u v t =
                      subdivMainNode n (k + 2) (Fin.last (k + 1)) ∧
                      subdivMainNode n (k + 2) v = Fin.last (subdivS n (k + 2) + 1)) :=
                    fun h ↦ hmain_ne_last v h.2
                  simp only [subdivMat, Matrix.of_apply, hnot1, hnot2, ↓reduceIte, mnot_main,
                    ↓reduceDIte]
                  rw [dite_eq_left mb]
                  have hu_eq : ∀ h,
                      (⟨((subdivMidNode n (k + 2) u v t).val - 1) / subdivB n (k + 2), h⟩ :
                        Fin (k + 2)) = u := fun _ ↦ Fin.ext hd_mid
                  have hv_eq : ∀ h,
                      (⟨(((subdivMidNode n (k + 2) u v t).val - 1) % subdivB n (k + 2) - 1) /
                        (n + 1), h⟩ : Fin (k + 2)) = v := fun _ ↦ Fin.ext hrem_div
                  have ht_eq : ∀ h,
                      (⟨(((subdivMidNode n (k + 2) u v t).val - 1) % subdivB n (k + 2) - 1) %
                        (n + 1), h⟩ : Fin (n + 1)) = t := fun _ ↦ Fin.ext hrem_mod
                  simp only [hu_eq, hv_eq, ht_eq, and_true]
                rw [hq_mid, hN_mid]
                by_cases huv : u < v <;> [simp [huv, mul_assoc]; simp [huv]]
              simp_rw [hmid_eval]
              by_cases huv : u < v
              · simp only [huv, ↓reduceIte, ← Finset.mul_sum]; congr 1
                rw [Fin.sum_univ_succ]
                simp only [subdivEdgeCoeff, subdivEdgeVar, Fin.val_zero, ↓reduceDIte, mul_one,
                  Fin.val_succ, Nat.succ_ne_zero, Nat.add_sub_cancel, Fin.eta]
                exact eq_C_add_sum_X_of_totalDegree_le_one (hdeg u v)
              · simp [huv]
            simp_rw [hterm]; rw [← Fintype.sum_prod_type']
            let embMid : Fin (k + 2) × Fin (n + 1) ↪ Fin (subdivS n (k + 2) + 2) :=
              ⟨fun p ↦ subdivMidNode n (k + 2) p.1 v p.2, fun a b hab ↦ by
                dsimp only at hab
                have h1 : a.1 = b.1 := Fin.ext (by
                  have := hmid_div a.1 v a.2; rw [hab, hmid_div] at this; exact this.symm)
                have h2 : a.2 = b.2 := Fin.ext (by
                  have := hmid_mod a.1 v a.2; rw [hab, hmid_mod] at this; omega)
                exact Prod.ext h1 h2⟩
            change (∑ x : Fin (k + 2) × Fin (n + 1), subdivVec N q (embMid x) *
              subdivMat N (embMid x) (subdivMainNode n (k + 2) v)) = _
            rw [← Finset.sum_map Finset.univ embMid
              (fun x ↦ subdivVec N q x * subdivMat N x (subdivMainNode n (k + 2) v))]
            refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx_not ↦ ?_
            have hN0 : subdivMat N x (subdivMainNode n (k + 2) v) = 0 := by
              have hnot1 : ¬ (x = 0 ∧
                  subdivMainNode n (k + 2) v = subdivMainNode n (k + 2) 0) := by
                rintro ⟨_, hmv⟩; apply hv0; apply Fin.ext
                have hval := congrArg Fin.val hmv
                change 1 + v.val * subdivB n (k + 2) = 1 + 0 * subdivB n (k + 2) at hval
                have hmul : v.val * subdivB n (k + 2) = 0 := by omega
                exact (Nat.mul_eq_zero.mp hmul).resolve_right (Nat.ne_of_gt hBpos)
              have hnot2 : ¬ (x = subdivMainNode n (k + 2) (Fin.last (k + 1)) ∧
                  subdivMainNode n (k + 2) v = Fin.last (subdivS n (k + 2) + 1)) :=
                fun h ↦ hmain_ne_last v h.2
              simp only [subdivMat, Matrix.of_apply, hnot1, hnot2, ↓reduceIte]
              split_ifs with hx hy _ hx2 huv2
              · exfalso
                have hv_sub : (subdivMainNode n (k + 2) v).val - 1 = v.val * subdivB n (k + 2) := by
                  dsimp [subdivMainNode]; omega
                have hlt1 : ((x.val - 1) / subdivB n (k + 2)) * subdivB n (k + 2) <
                    v.val * subdivB n (k + 2) := by omega
                have hlt2 : v.val * subdivB n (k + 2) <
                    ((x.val - 1) / subdivB n (k + 2) + 1) * subdivB n (k + 2) := by omega
                have := (Nat.mul_lt_mul_right hBpos).mp hlt1
                have := (Nat.mul_lt_mul_right hBpos).mp hlt2; omega
              · rfl
              · rfl
              · exfalso
                let u' : Fin (k + 2) := ⟨(x.val - 1) / subdivB n (k + 2),
                  (Nat.div_lt_iff_lt_mul hBpos).mpr (by
                    have h1 := hx2.1; have h2 := hx2.2.1; dsimp [subdivS] at h2; omega)⟩
                let rem := (x.val - 1) % subdivB n (k + 2) - 1
                let v' : Fin (k + 2) := ⟨rem / (n + 1), by
                  have hmod := Nat.mod_lt (x.val - 1) hBpos
                  have hmod_pos := Nat.pos_iff_ne_zero.mpr hx2.2.2
                  have : rem < (k + 2) * (n + 1) := by
                    change (x.val - 1) % subdivB n (k + 2) - 1 < (k + 2) * (n + 1)
                    dsimp [subdivB] at *; omega
                  exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr this⟩
                let t' : Fin (n + 1) := ⟨rem % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
                have hv_eq : v' = v := by
                  apply Fin.ext
                  have hval := congrArg Fin.val huv2.2
                  change 1 + v.val * subdivB n (k + 2) = 1 + v'.val * subdivB n (k + 2) at hval
                  exact Nat.eq_of_mul_eq_mul_right hBpos (by omega)
                have hx_mid : embMid (u', t') = x := by
                  change subdivMidNode n (k + 2) u' v t' = x; rw [← hv_eq]; apply Fin.ext
                  change 1 + u'.val * subdivB n (k + 2) + (1 + v'.val * (n + 1) + t'.val) = x.val
                  have h1 := Nat.div_add_mod' rem (n + 1)
                  have h2 := Nat.div_add_mod' (x.val - 1) (subdivB n (k + 2))
                  have h3 := Nat.pos_iff_ne_zero.mpr hx2.2.2
                  have hrem_def : rem = (x.val - 1) % subdivB n (k + 2) - 1 := rfl
                  have hu'_val : u'.val = (x.val - 1) / subdivB n (k + 2) := rfl
                  have hv'_val : v'.val = rem / (n + 1) := rfl
                  have ht'_val : t'.val = rem % (n + 1) := rfl
                  rw [hu'_val, hv'_val, ht'_val]; omega
                exact hx_not (Finset.mem_map.mpr ⟨(u', t'), Finset.mem_univ _, hx_mid⟩)
              · rfl
              · rfl
            rw [hN0, mul_zero]
        · let u : Fin (k + 2) := ⟨(y.val - 1) / subdivB n (k + 2),
            (Nat.div_lt_iff_lt_mul hBpos).mpr (by dsimp [subdivS] at *; omega)⟩
          let rem := (y.val - 1) % subdivB n (k + 2) - 1
          let v : Fin (k + 2) := ⟨rem / (n + 1), by
            have hmod := Nat.mod_lt (y.val - 1) hBpos
            have hmod_pos := Nat.pos_iff_ne_zero.mpr hymod
            have : rem < (k + 2) * (n + 1) := by
              change (y.val - 1) % subdivB n (k + 2) - 1 < (k + 2) * (n + 1)
              dsimp [subdivB] at *; omega
            exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr this⟩
          let t : Fin (n + 1) := ⟨rem % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
          have hnot_ymain : ∀ w : Fin (k + 2), y ≠ subdivMainNode n (k + 2) w := by
            intro w hw; rw [hw, hmain_mod] at hymod; exact hymod rfl
          rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single (subdivMainNode n (k + 2) u)]
          · have hqy : subdivVec N q y = if u < v then q u * subdivEdgeCoeff N u v t else 0 := by
              simp only [subdivVec, hy0, hylast, ↓reduceIte, hy_in, and_self, ↓reduceDIte, hymod]
              rfl
            have hy_range : 1 + u.val * subdivB n (k + 2) < y.val ∧
                y.val < 1 + (u.val + 1) * subdivB n (k + 2) := by
              have h2 := Nat.div_add_mod' (y.val - 1) (subdivB n (k + 2))
              have h3 := Nat.pos_iff_ne_zero.mpr hymod
              have h4 := Nat.mod_lt (y.val - 1) hBpos
              have hsucc := Nat.add_one_mul u.val (subdivB n (k + 2))
              have hu_val : u.val = (y.val - 1) / subdivB n (k + 2) := rfl
              rw [hu_val] at hsucc ⊢; omega
            have hrem_eq : y.val - (1 + u.val * subdivB n (k + 2)) - 1 = rem := by
              have h2 := Nat.div_add_mod' (y.val - 1) (subdivB n (k + 2))
              have hu_val : u.val = (y.val - 1) / subdivB n (k + 2) := rfl
              have hrem_def : rem = (y.val - 1) % subdivB n (k + 2) - 1 := rfl
              rw [hu_val, hrem_def]; omega
            have hNm : subdivMat N (subdivMainNode n (k + 2) u) y =
                if u < v then subdivEdgeCoeff N u v t else 0 := by
              have hnot1 : ¬ (subdivMainNode n (k + 2) u = 0 ∧
                  y = subdivMainNode n (k + 2) 0) := fun h ↦ hmain_ne0 u h.1
              have hnot2 : ¬ (subdivMainNode n (k + 2) u =
                  subdivMainNode n (k + 2) (Fin.last (k + 1)) ∧
                  y = Fin.last (subdivS n (k + 2) + 1)) := fun h ↦ hylast h.2
              have hex : ∃ u' : Fin (k + 2),
                  subdivMainNode n (k + 2) u = subdivMainNode n (k + 2) u' := ⟨u, rfl⟩
              simp only [subdivMat, Matrix.of_apply, hnot1, hnot2, ↓reduceIte, hex, ↓reduceDIte]
              simp only [hmain_div u]
              rw [dite_eq_left hy_range]
              have hv_eq : ∀ h,
                  (⟨(y.val - (1 + u.val * subdivB n (k + 2)) - 1) / (n + 1), h⟩ :
                    Fin (k + 2)) = v := fun _ ↦ Fin.ext (by simp [v, hrem_eq])
              have ht_eq : ∀ h,
                  (⟨(y.val - (1 + u.val * subdivB n (k + 2)) - 1) % (n + 1), h⟩ :
                    Fin (n + 1)) = t := fun _ ↦ Fin.ext (by simp [t, hrem_eq])
              simp only [hv_eq, ht_eq]
            rw [hqy, hq_main u, hNm]; split_ifs <;> simp
          · intro x _ hx_ne
            have hN0 : subdivMat N x y = 0 := by
              have hnot1 : ¬ (x = 0 ∧ y = subdivMainNode n (k + 2) 0) := fun h ↦ hnot_ymain 0 h.2
              have hnot2 : ¬ (x = subdivMainNode n (k + 2) (Fin.last (k + 1)) ∧
                  y = Fin.last (subdivS n (k + 2) + 1)) := fun h ↦ hylast h.2
              simp only [subdivMat, Matrix.of_apply, hnot1, hnot2, ↓reduceIte]
              split_ifs with hx hy_r _ hx2 huv2
              · exfalso; rcases hx with ⟨u', rfl⟩; rw [hmain_div u'] at hy_r
                have hu'_eq : u' = u := Fin.ext (by
                  have h2 := Nat.div_add_mod' (y.val - 1) (subdivB n (k + 2))
                  have h3 := Nat.pos_iff_ne_zero.mpr hymod
                  have h4 := Nat.mod_lt (y.val - 1) hBpos
                  have hu_val : u.val = (y.val - 1) / subdivB n (k + 2) := rfl
                  have hsucc := Nat.add_one_mul u.val (subdivB n (k + 2))
                  have hlt1 : u'.val * subdivB n (k + 2) < (u.val + 1) * subdivB n (k + 2) := by
                    rw [hu_val] at hsucc ⊢; omega
                  have hlt2 : u.val * subdivB n (k + 2) < (u'.val + 1) * subdivB n (k + 2) := by
                    rw [hu_val]; omega
                  have := (Nat.mul_lt_mul_right hBpos).mp hlt1
                  have := (Nat.mul_lt_mul_right hBpos).mp hlt2; omega)
                exact hx_ne (congrArg (subdivMainNode n (k + 2)) hu'_eq)
              · rfl
              · rfl
              · exact absurd huv2.2 (hnot_ymain _)
              · rfl
              · rfl
            rw [hN0, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
  have hqlast_eq : subdivVec N q (Fin.last (subdivS n (k + 2) + 1)) = q (Fin.last (k + 1)) := by
    have h0last : (Fin.last (subdivS n (k + 2) + 1) : Fin (subdivS n (k + 2) + 2)) ≠ 0 :=
      fin_last_ne_zero _
    simp only [subdivVec, h0last, ↓reduceIte]
  refine ⟨subdivS n (k + 2) + 1, le_rfl, isProjection_det_iff_exists_isSubstMatrix.mpr
    ⟨(subdivMat N - 1).submatrix Fin.castSucc Fin.succ, fun a b ↦ ?_,
      (Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul (subdivMat N) hN'_tri
        hq'_eq).symm.trans hqlast_eq⟩⟩
  simp only [Matrix.submatrix_apply, Matrix.sub_apply]
  by_cases hab : a.castSucc = b.succ
  · rw [hN'_tri a.castSucc b.succ hab.symm.le, hab, Matrix.one_apply_eq, zero_sub]
    exact .neg_one
  · rw [Matrix.one_apply_ne hab, sub_zero]
    exact hN'_subst a.castSucc b.succ

end AffineABP

section ComplexityClasses

variable (K : Type u) [CommRing K]

/-- Valiant's formula class $\mathsf{VP}_{\mathrm{ws}}(K)$: families of polynomials with
polynomially bounded variable counts computed by polynomially sized arithmetic `Formula`s. -/
def VPws : Set (PolynomialFamily K) :=
  {f | PolynomiallyBounded f.vars ∧
    ∃ F : ∀ n, Formula (arithSignature K) (f.vars n),
      PolynomiallyBounded (fun n ↦ (F n).size) ∧
      ∀ n, (F n).toCircuit.polynomial 0 = f.poly n}

/-- Valiant's algebraic branching program class $\mathsf{VBP}(K)$: families of polynomials with
polynomially bounded variable counts computed by polynomially sized affine algebraic branching
programs. -/
def VBP : Set (PolynomialFamily K) :=
  {f | PolynomiallyBounded f.vars ∧
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, IsAffineABP (s n) (f.poly n)}

variable {K}

/-- Explicit characterization of `VPws K`. -/
theorem mem_VPws_iff {f : PolynomialFamily K} :
    f ∈ VPws K ↔
      PolynomiallyBounded f.vars ∧
        ∃ F : ∀ n, Formula (arithSignature K) (f.vars n),
          PolynomiallyBounded (fun n ↦ (F n).size) ∧
          ∀ n, (F n).toCircuit.polynomial 0 = f.poly n :=
  Iff.rfl

/-- Explicit characterization of `VBP K`. -/
theorem mem_VBP_iff {f : PolynomialFamily K} :
    f ∈ VBP K ↔
      PolynomiallyBounded f.vars ∧
        ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, IsAffineABP (s n) (f.poly n) :=
  Iff.rfl

/-- **Universality of the determinant for `VBP`**: a polynomial family `f` belongs to `VBP K` if
and only if `f.vars` is polynomially bounded and `determinantalComplexity (f.poly n)` is bounded by
a polynomially bounded function of `n`. -/
theorem mem_VBP_iff_determinantalComplexity {f : PolynomialFamily K} :
    f ∈ VBP K ↔
      PolynomiallyBounded f.vars ∧
        ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧
          ∀ n, determinantalComplexity (f.poly n) ≤ s n := by
  constructor
  · rintro ⟨hvars, s, hs, habp⟩
    refine ⟨hvars, fun n ↦ s n + 1, hs.add (PolynomiallyBounded.const 1), fun n ↦ ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using determinantalComplexity_le_of_isAffineABP (habp n)
  · rintro ⟨hvars, s, hs, hdc⟩
    have hex : ∀ n, ∃ m ≤ s n, HasDeterminantalRepresentation (f.poly n) m := by
      intro n
      obtain ⟨m, hm_rep, hm_eq⟩ := exists_hasDeterminantalRepresentation_eq_determinantalComplexity
        (f.poly n)
      have hm_le : (m : ℕ∞) ≤ (s n : ℕ∞) := hm_eq.trans_le (hdc n)
      exact ⟨m, Nat.cast_le.mp hm_le, hm_rep⟩
    refine ⟨hvars, fun n ↦ s n ^ 3, hs.pow 3, fun n ↦ ?_⟩
    obtain ⟨m, hms, hrep⟩ := hex n
    exact (isAffineABP_of_hasDeterminantalRepresentation hrep).mono (Nat.pow_le_pow_left hms 3)

/-- Every family in `VBP K` is a `p`-projection of `detFamily K`. -/
theorem isPProjection_detFamily_of_mem_VBP {f : PolynomialFamily K} (hf : f ∈ VBP K) :
    f.IsPProjection (detFamily K) := by
  obtain ⟨hvars, s, hs, habp⟩ := hf
  let B : ℕ → ℕ := fun n ↦ (s n + 2) * (1 + (s n + 2) * (f.vars n + 1)) + 1
  have hB : PolynomiallyBounded B :=
    ((hs.add (.const 2)).mul ((PolynomiallyBounded.const 1).add
      ((hs.add (.const 2)).mul (hvars.add (.const 1))))).add (.const 1)
  refine ⟨B, hB, fun n ↦ ?_⟩
  obtain ⟨m, hm_le, hproj⟩ := exists_isProjection_det_of_isAffineABP (habp n)
  exact isProjection_det_mono hm_le hproj

/-- Characterization of `VBP K` via `p`-projections of `detFamily K`. -/
theorem mem_VBP_iff_isPProjection_detFamily {f : PolynomialFamily K} :
    f ∈ VBP K ↔ PolynomiallyBounded f.vars ∧ f.IsPProjection (detFamily K) := by
  refine ⟨fun hf ↦ ⟨hf.1, isPProjection_detFamily_of_mem_VBP hf⟩, ?_⟩
  rintro ⟨hvars, t, ht, hproj⟩
  exact ⟨hvars, fun n ↦ t n ^ 3, ht.pow 3, fun n ↦ isAffineABP_of_isProjection_det (hproj n)⟩

/-- Every family in `VPws K` belongs to `VBP K` (`VPws K ⊆ VBP K`). -/
theorem VPws_subset_VBP : VPws K ⊆ VBP K := by
  rintro f ⟨hvars, F, hF, hpoly⟩
  rw [mem_VBP_iff_determinantalComplexity]
  refine ⟨hvars, fun n ↦ (F n).size + 1, hF.add (.const 1), fun n ↦ ?_⟩
  rw [← hpoly n]
  simpa only [Nat.cast_add, Nat.cast_one] using Formula.determinantalComplexity_toCircuit_le (F n)

/-- Every family in `VBP K` belongs to `VP K` (`VBP K ⊆ VP K`). -/
theorem VBP_subset_VP : VBP K ⊆ VP K := by
  intro f hf
  exact VP.of_isPProjection detFamily_mem_VP (isPProjection_detFamily_of_mem_VBP hf) hf.1

/-- Every family in `VBP K` is a `p`-family (polynomially bounded variables and degrees). -/
theorem isPFamily_of_mem_VBP {f : PolynomialFamily K} (hf : f ∈ VBP K) : f.IsPFamily :=
  VP.isPFamily (VBP_subset_VP hf)

/-- Every family in `VPws K` belongs to `VP K` (`VPws K ⊆ VP K`). -/
theorem VPws_subset_VP : VPws K ⊆ VP K :=
  VPws_subset_VBP.trans VBP_subset_VP

/-- Every family in `VBP K` belongs to `VNP K` (`VBP K ⊆ VNP K`). -/
theorem VBP_subset_VNP : VBP K ⊆ VNP K :=
  VBP_subset_VP.trans VP_subset_VNP

/-- The generic determinant family `detFamily K` belongs to `VBP K`. -/
@[simp]
theorem detFamily_mem_VBP : detFamily K ∈ VBP K := by
  rw [mem_VBP_iff_determinantalComplexity]
  refine ⟨(PolynomiallyBounded.id).mul PolynomiallyBounded.id, fun n ↦ n,
    PolynomiallyBounded.id, fun n ↦ determinantalComplexity_det_le n⟩

variable (K) in
/-- **Valiant's algebraic separation conjecture** ($\mathsf{VBP}_K \neq \mathsf{VNP}_K$). -/
def ValiantVBPNeVNPConjecture : Prop :=
  VBP K ≠ VNP K

/-- Explicit characterization of `ValiantVBPNeVNPConjecture`. -/
theorem valiantVBPNeVNPConjecture_iff :
    ValiantVBPNeVNPConjecture K ↔ VBP K ≠ VNP K :=
  Iff.rfl

variable (K) in
/-- **Valiant's superpolynomial determinantal-complexity conjecture** for the permanent family: no
polynomially bounded function `s : ℕ → ℕ` upper-bounds `determinantalComplexity` of the `m × m`
generic permanent `(genericMatrix K m).permanent` for all `m`. -/
def ValiantDeterminantalConjecture : Prop :=
  ¬ ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧
    ∀ m, determinantalComplexity (genericMatrix K m).permanent ≤ s m

/-- Explicit characterization of `ValiantDeterminantalConjecture`. -/
theorem valiantDeterminantalConjecture_iff :
    ValiantDeterminantalConjecture K ↔
      ¬ ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧
        ∀ m, determinantalComplexity (genericMatrix K m).permanent ≤ s m :=
  Iff.rfl

/-- `permFamily K ∈ VBP K` holds if and only if `determinantalComplexity` of the generic `m × m`
permanent is polynomially bounded (`¬ ValiantDeterminantalConjecture K`). -/
theorem permFamily_mem_VBP_iff :
    permFamily K ∈ VBP K ↔
      ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧
        ∀ m, determinantalComplexity (genericMatrix K m).permanent ≤ s m := by
  rw [mem_VBP_iff_determinantalComplexity]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨isPFamily_permFamily.1, h⟩⟩

/-- If `permFamily K` is `VNP`-complete (`IsVNPComplete (permFamily K)`), then separating `VBP K`
from `VNP K` is equivalent to `ValiantDeterminantalConjecture K` (superpolynomial determinantal
complexity of the permanent). -/
theorem valiantVBPNeVNPConjecture_iff_of_isVNPComplete
    (hperm : IsVNPComplete (permFamily K)) :
    ValiantVBPNeVNPConjecture K ↔ ValiantDeterminantalConjecture K := by
  rw [valiantVBPNeVNPConjecture_iff, valiantDeterminantalConjecture_iff, ← permFamily_mem_VBP_iff]
  refine not_congr ⟨fun h_eq ↦ ?_, fun h_mem ↦ ?_⟩
  · rw [h_eq]
    exact hperm.1
  · refine Set.Subset.antisymm VBP_subset_VNP fun g hg ↦ ?_
    have hproj_det : g.IsPProjection (detFamily K) :=
      (hperm.2 g hg).trans (isPProjection_detFamily_of_mem_VBP h_mem)
    obtain ⟨t, ht, hpt⟩ := hproj_det
    rw [mem_VBP_iff_determinantalComplexity]
    refine ⟨(VNP.isPFamily hg).1, t, ht, fun n ↦ ?_⟩
    exact determinantalComplexity_le (hasDeterminantalRepresentation_of_isProjection (hpt n))

private example : detFamily ℤ ∈ VBP ℤ := detFamily_mem_VBP

end ComplexityClasses

end CslibFrontier
