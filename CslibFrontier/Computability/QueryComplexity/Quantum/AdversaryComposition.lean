/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.SpectralAdversary
import Mathlib.Analysis.Matrix.Spectrum
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm

/-!
# General Adversary Bound Composition for Partial Boolean Functions

This module proves that the negative-weight quantum adversary bound $\mathrm{ADV}^{\pm}$
(`Cslib.Quantum.generalAdversary`) composes multiplicatively for arbitrary partial (promise)
Boolean functions: if $f : \mathcal{D}_f \to \alpha$ with $\mathcal{D}_f \subseteq \{0, 1\}^n$ and
$g_j : \mathcal{D}_{g_j} \to \{0, 1\}$ with $\mathcal{D}_{g_j} \subseteq \{0, 1\}^{k_j}$ for
$j \in \{0, \dots, n - 1\}$, then the composed partial function
$h = f \circ (g_0, \dots, g_{n-1})$ on
$\mathcal{D}_h = \{x : (\forall j,\, x^{(j)} \in \mathcal{D}_{g_j}) \land
(g_0(x^{(0)}), \dots, g_{n-1}(x^{(n-1)})) \in \mathcal{D}_f\}$ satisfies
\[
  \mathrm{ADV}^{\pm}(h) \ge
    \mathrm{ADV}^{\pm}(f) \cdot \min_j \mathrm{ADV}^{\pm}(g_j)
\]
(when $n > 0$, or more generally
$\mathrm{ADV}^{\pm}(h) \ge \mathrm{ADV}^{\pm}(f) \cdot c$
whenever $\mathrm{ADV}^{\pm}(g_j) \ge c \ge 0$ for all $j$).

## Main definitions

* `CslibFrontier.Quantum.blockBitEquiv`: canonical equivalence between flat indices
  `Fin (∑ j, k j)` and pairs `(j : Fin n, q : Fin (k j))`.
* `CslibFrontier.Quantum.inputBlock`, `CslibFrontier.Quantum.evalInnerBlocks`: extraction of the
  $j$-th input block $x^{(j)} \in \{0, 1\}^{k_j}$ and the tuple of inner outputs
  $(g_j(x^{(j)}))_{j < n}$.
* `CslibFrontier.Quantum.composedPromise`, `CslibFrontier.Quantum.composedFunc`: promise predicate
  $\mathcal{D}_h$ and value map $h(x) = f(g_0(x^{(0)}), \dots, g_{n-1}(x^{(n-1)}))$ of the
  composed partial function.
* `CslibFrontier.Quantum.composedAdversaryMatrix`: the Høyer–Lee–Špalek composed adversary matrix
  $\gamma(\Gamma_f, \Gamma_{g_0}, \dots, \Gamma_{g_{n-1}})$.

## Main results

* `CslibFrontier.Quantum.isAdversaryMatrix_composedAdversaryMatrix`: $\gamma(\Gamma_f, \Gamma_g)$
  is a valid symmetric adversary matrix for `(composedPromise P_f P_g g, composedFunc f g)`.
* `CslibFrontier.Quantum.opNorm_composedAdversaryMatrix`: exact spectral norm multiplicativity
  $\|\gamma(\Gamma_f, \Gamma_g)\| = \|\Gamma_f\| \prod_{j < n} \|\Gamma_{g_j}\|$.
* `CslibFrontier.Quantum.composedAdversaryMatrix_hadamard_diffMatrix`: compatibility of $\gamma$
  with coordinate disagreement masks $D_\ell$.
* `CslibFrontier.Quantum.generalAdversary_composed_ge`: lower bound
  $\mathrm{ADV}^{\pm}(h) \ge \mathrm{ADV}^{\pm}(f) \cdot c$ whenever
  $\mathrm{ADV}^{\pm}(g_j) \ge c \ge 0$ for all $j$.
-/

public section

namespace CslibFrontier.Quantum

open Cslib Cslib.Quantum Finset Matrix
open scoped Matrix.Norms.L2Operator

section BlockIndexing

/-- Canonical equivalence `(Σ j : Fin n, Fin (k j)) ≃ Fin (∑ j : Fin n, k j)` splitting a
concatenated bitstring into `n` blocks of lengths `k 0, …, k (n - 1)`. -/
def blockBitEquiv : ∀ {n : ℕ} (k : Fin n → ℕ), (Σ j : Fin n, Fin (k j)) ≃ Fin (∑ j : Fin n, k j)
  | 0, _ =>
      { toFun := fun p => Fin.elim0 p.1
        invFun := fun i => Fin.elim0 (Fin.cast (by simp) i)
        left_inv := fun p => Fin.elim0 p.1
        right_inv := fun i => Fin.elim0 (Fin.cast (by simp) i) }
  | n + 1, k =>
      let eInit := blockBitEquiv (fun j : Fin n => k j.castSucc)
      let eSplit : (Σ j : Fin (n + 1), Fin (k j)) ≃
          (Σ j : Fin n, Fin (k j.castSucc)) ⊕ Fin (k (Fin.last n)) :=
        { toFun := fun ⟨j, q⟩ =>
            if h : j.1 < n then Sum.inl ⟨⟨j.1, h⟩, q⟩
            else
              have hj : j = Fin.last n := Fin.ext (by have := j.isLt; simp [Fin.val_last]; omega)
              Sum.inr (Fin.cast (by rw [hj]) q)
          invFun := fun
            | Sum.inl ⟨j, q⟩ => ⟨j.castSucc, q⟩
            | Sum.inr q => ⟨Fin.last n, q⟩
          left_inv := fun ⟨j, q⟩ => by
            by_cases h : j.1 < n
            · simp only [h, ↓reduceDIte]
              rfl
            · have hlast : j = Fin.last n :=
                Fin.ext (by have := j.isLt; simp [Fin.val_last]; omega)
              subst hlast
              simp
          right_inv := fun s => by
            cases s with
            | inl p =>
                rcases p with ⟨j, q⟩
                simp [j.isLt]
            | inr q =>
                simp }
      eSplit.trans ((Equiv.sumCongr eInit (Equiv.refl _)).trans
        (finSumFinEquiv.trans (finCongr (Fin.sum_univ_castSucc k).symm)))

/-- Extracts the `j`-th block `x^{(j)} : BitString (k j)` of `x : BitString (∑ j, k j)`. -/
def inputBlock {n : ℕ} {k : Fin n → ℕ} (x : BitString (∑ j : Fin n, k j)) (j : Fin n) :
    BitString (k j) :=
  fun q => x (blockBitEquiv k ⟨j, q⟩)

/-- Reassembles a family of blocks `(x^{(j)})_{j < n}` into a single `BitString (∑ j, k j)`. -/
def concatBlocks {n : ℕ} {k : Fin n → ℕ} (xb : ∀ j : Fin n, BitString (k j)) :
    BitString (∑ j : Fin n, k j) :=
  fun idx =>
    let p := (blockBitEquiv k).symm idx
    xb p.1 p.2

/-- Equivalence between `BitString (∑ j, k j)` and block families
`∀ j : Fin n, BitString (k j)`. -/
def bitStringBlockEquiv {n : ℕ} (k : Fin n → ℕ) :
    BitString (∑ j : Fin n, k j) ≃ (∀ j : Fin n, BitString (k j)) where
  toFun := inputBlock
  invFun := concatBlocks
  left_inv x := by
    funext idx
    simp [inputBlock, concatBlocks]
  right_inv xb := by
    funext j q
    dsimp only [inputBlock, concatBlocks]
    rw [(blockBitEquiv k).symm_apply_apply]

@[simp]
theorem inputBlock_concatBlocks {n : ℕ} {k : Fin n → ℕ}
    (xb : ∀ j : Fin n, BitString (k j)) (j : Fin n) :
    inputBlock (concatBlocks xb) j = xb j :=
  congrFun ((bitStringBlockEquiv k).right_inv xb) j

/-- Evaluates the `n` inner Boolean functions `g_0, …, g_{n-1}` on their blocks of `x`. -/
def evalInnerBlocks {n : ℕ} {k : Fin n → ℕ}
    (g : ∀ j : Fin n, BitString (k j) → Bool)
    (x : BitString (∑ j : Fin n, k j)) : BitString n :=
  fun j => g j (inputBlock x j)

/-- Promise domain of the composed function `f ∘ (g_0, …, g_{n-1})`: every block `x^{(j)}` satisfies
`P_g j`, and the inner output vector satisfies `P_f`. -/
def composedPromise {n : ℕ} {k : Fin n → ℕ}
    (P_f : BitString n → Prop)
    (P_g : ∀ j : Fin n, BitString (k j) → Prop)
    (g : ∀ j : Fin n, BitString (k j) → Bool)
    (x : BitString (∑ j : Fin n, k j)) : Prop :=
  (∀ j : Fin n, P_g j (inputBlock x j)) ∧ P_f (evalInnerBlocks g x)

/-- Composed function `h(x) = f(g_0(x^{(0)}), …, g_{n-1}(x^{(n-1)}))`. -/
def composedFunc {α : Type*} {n : ℕ} {k : Fin n → ℕ}
    (f : BitString n → α)
    (g : ∀ j : Fin n, BitString (k j) → Bool)
    (x : BitString (∑ j : Fin n, k j)) : α :=
  f (evalInnerBlocks g x)

end BlockIndexing

section ComposedMatrix

private noncomputable def opNormR {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

private noncomputable def hatAdversary {m : ℕ}
    (P : BitString m → Prop) [DecidablePred P]
    (Γ : Matrix (BitString m) (BitString m) ℝ) :
    Matrix (BitString m) (BitString m) ℝ :=
  Matrix.of fun u v =>
    Γ u v + if u = v ∧ P u then opNormR Γ else 0

/-- The composed adversary matrix `γ(Γ_f, Γ_g)` on `BitString (∑ j, k j)` for a partial outer
function `(P_f, f)` and partial inner Boolean functions `(P_g j, g j)`. -/
noncomputable def composedAdversaryMatrix {n : ℕ} {k : Fin n → ℕ}
    (P_g : ∀ j : Fin n, BitString (k j) → Prop)
    (g : ∀ j : Fin n, BitString (k j) → Bool)
    (Γ_f : Matrix (BitString n) (BitString n) ℝ)
    (Γ_g : ∀ j : Fin n, Matrix (BitString (k j)) (BitString (k j)) ℝ) :
    Matrix (BitString (∑ j : Fin n, k j)) (BitString (∑ j : Fin n, k j)) ℝ := by
  classical
  exact Matrix.of fun x y =>
    Γ_f (evalInnerBlocks g x) (evalInnerBlocks g y) *
      ∏ j : Fin n, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j)

theorem isSymm_composedAdversaryMatrix {n : ℕ} {k : Fin n → ℕ}
    (P_g : ∀ j : Fin n, BitString (k j) → Prop)
    (g : ∀ j : Fin n, BitString (k j) → Bool)
    {Γ_f : Matrix (BitString n) (BitString n) ℝ}
    {Γ_g : ∀ j : Fin n, Matrix (BitString (k j)) (BitString (k j)) ℝ}
    (hSym_f : Γ_f.IsSymm) (hSym_g : ∀ j, (Γ_g j).IsSymm) :
    (composedAdversaryMatrix P_g g Γ_f Γ_g).IsSymm := by
  classical
  ext x y
  simp only [Matrix.transpose_apply, composedAdversaryMatrix, Matrix.of_apply]
  have hf : Γ_f (evalInnerBlocks g y) (evalInnerBlocks g x) =
      Γ_f (evalInnerBlocks g x) (evalInnerBlocks g y) := by
    simpa [Matrix.transpose_apply] using
      congrFun (congrFun hSym_f.eq (evalInnerBlocks g x)) (evalInnerBlocks g y)
  rw [hf]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [hatAdversary, Matrix.of_apply]
  have hg : Γ_g j (inputBlock y j) (inputBlock x j) =
      Γ_g j (inputBlock x j) (inputBlock y j) := by
    simpa [Matrix.transpose_apply] using
      congrFun (congrFun (hSym_g j).eq (inputBlock x j)) (inputBlock y j)
  rw [hg]
  by_cases hxy : inputBlock x j = inputBlock y j
  · simp [hxy]
  · have hyx : inputBlock y j ≠ inputBlock x j := Ne.symm hxy
    simp [hxy, hyx]

/-- If `Γ_f` is an adversary matrix for `(P_f, f)` and each `Γ_g j` is an adversary matrix for
`(P_g j, g j)`, then `composedAdversaryMatrix P_g g Γ_f Γ_g` is an adversary matrix for
`(composedPromise P_f P_g g, composedFunc f g)`. -/
theorem isAdversaryMatrix_composedAdversaryMatrix {α : Type*} {n : ℕ} {k : Fin n → ℕ}
    {P_f : BitString n → Prop} {f : BitString n → α}
    {P_g : ∀ j : Fin n, BitString (k j) → Prop}
    {g : ∀ j : Fin n, BitString (k j) → Bool}
    {Γ_f : Matrix (BitString n) (BitString n) ℝ}
    {Γ_g : ∀ j : Fin n, Matrix (BitString (k j)) (BitString (k j)) ℝ}
    (hAdv_f : IsAdversaryMatrix P_f f Γ_f)
    (hAdv_g : ∀ j, IsAdversaryMatrix (P_g j) (g j) (Γ_g j)) :
    IsAdversaryMatrix (composedPromise P_f P_g g) (composedFunc f g)
      (composedAdversaryMatrix P_g g Γ_f Γ_g) := by
  classical
  intro x y hne
  simp only [composedAdversaryMatrix, Matrix.of_apply] at hne
  have hf_ne : Γ_f (evalInnerBlocks g x) (evalInnerBlocks g y) ≠ 0 :=
    left_ne_zero_of_mul hne
  have hprod_ne : ∏ j : Fin n,
      hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) ≠ 0 :=
    right_ne_zero_of_mul hne
  obtain ⟨hPf_x, hPf_y, hf_diff⟩ := hAdv_f _ _ hf_ne
  have hPg_xy : ∀ j : Fin n, P_g j (inputBlock x j) ∧ P_g j (inputBlock y j) := by
    intro j
    have hj_ne : hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) ≠ 0 := by
      intro hz
      exact hprod_ne (Finset.prod_eq_zero (Finset.mem_univ j) hz)
    simp only [hatAdversary, Matrix.of_apply] at hj_ne
    by_cases hΓ : Γ_g j (inputBlock x j) (inputBlock y j) ≠ 0
    · obtain ⟨h1, h2, _⟩ := hAdv_g j _ _ hΓ
      exact ⟨h1, h2⟩
    · push Not at hΓ
      rw [hΓ, zero_add] at hj_ne
      by_cases hcond : inputBlock x j = inputBlock y j ∧ P_g j (inputBlock x j)
      · exact ⟨hcond.2, hcond.1 ▸ hcond.2⟩
      · simp [hcond] at hj_ne
  exact ⟨⟨fun j => (hPg_xy j).1, hPf_x⟩, ⟨fun j => (hPg_xy j).2, hPf_y⟩, hf_diff⟩

section OrthogonalDilation

private theorem toEuclideanCLM_apply_ofLp {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℝ) (v : EuclideanSpace ℝ κ) :
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) v).ofLp = M *ᵥ v.ofLp :=
  rfl

private theorem exists_orth_involution_dilation {κ : Type*} [Fintype κ] [DecidableEq κ]
    {T : Matrix κ κ ℝ} (hSym : T.IsSymm) (hNorm : opNormR T ≤ 1) :
    ∃ W : Matrix (κ × Bool) (κ × Bool) ℝ,
      W.IsSymm ∧ Wᵀ * W = 1 ∧ ∀ u v : κ, W (u, false) (v, false) = T u v := by
  have hH : T.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hSym.eq
  set U : Matrix κ κ ℝ := (hH.eigenvectorUnitary : Matrix κ κ ℝ)
  have hUtU : Uᵀ * U = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hUUt : U * Uᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hspec : T = U * diagonal hH.eigenvalues * Uᵀ := by
    simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using hH.spectral_theorem
  have hev_le : ∀ i : κ, |hH.eigenvalues i| ≤ 1 := by
    intro i
    have hvi_norm : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    have hmul : Matrix.toEuclideanCLM (𝕜 := ℝ) T (hH.eigenvectorBasis i) =
        hH.eigenvalues i • hH.eigenvectorBasis i := by
      ext j
      exact congrFun (hH.mulVec_eigenvectorBasis i) j
    have hle := (Matrix.toEuclideanCLM (𝕜 := ℝ) T).le_opNorm (hH.eigenvectorBasis i)
    rw [hmul, norm_smul, Real.norm_eq_abs, hvi_norm, mul_one, mul_one] at hle
    exact hle.trans hNorm
  let sDiag : κ → ℝ := fun i => Real.sqrt (1 - (hH.eigenvalues i) ^ 2)
  let S : Matrix κ κ ℝ := U * diagonal sDiag * Uᵀ
  have hSSym : S.IsSymm := by
    simp only [IsSymm, S, Matrix.transpose_mul, Matrix.transpose_transpose,
      diagonal_transpose, Matrix.mul_assoc]
  have hTS_comm : T * S = S * T := by
    have hd : diagonal hH.eigenvalues * diagonal sDiag =
        diagonal sDiag * diagonal hH.eigenvalues := by
      simp only [diagonal_mul_diagonal]
      congr 1; ext i; ring
    calc T * S = U * (diagonal hH.eigenvalues * (Uᵀ * U) * diagonal sDiag) * Uᵀ := by
          simp only [hspec, S, Matrix.mul_assoc]
      _ = U * (diagonal sDiag * (Uᵀ * U) * diagonal hH.eigenvalues) * Uᵀ := by
          rw [hUtU, Matrix.mul_one, hd, Matrix.mul_one]
      _ = S * T := by simp only [hspec, S, Matrix.mul_assoc]
  have hT2_add_S2 : T * T + S * S = 1 := by
    have hTT : T * T = U * diagonal (fun i => (hH.eigenvalues i) ^ 2) * Uᵀ := by
      calc T * T = U * (diagonal hH.eigenvalues * (Uᵀ * U) * diagonal hH.eigenvalues) * Uᵀ := by
            simp only [hspec, Matrix.mul_assoc]
        _ = U * diagonal (fun i => (hH.eigenvalues i) ^ 2) * Uᵀ := by
            rw [hUtU, Matrix.mul_one, diagonal_mul_diagonal]
            congr 3; ext i; exact (sq (hH.eigenvalues i)).symm
    have hSS : S * S = U * diagonal (fun i => sDiag i ^ 2) * Uᵀ := by
      calc S * S = U * (diagonal sDiag * (Uᵀ * U) * diagonal sDiag) * Uᵀ := by
            simp only [S, Matrix.mul_assoc]
        _ = U * diagonal (fun i => sDiag i ^ 2) * Uᵀ := by
            rw [hUtU, Matrix.mul_one, diagonal_mul_diagonal]
            congr 3; ext i; exact (sq (sDiag i)).symm
    rw [hTT, hSS, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    have h1 : (fun i : κ => (hH.eigenvalues i) ^ 2 + sDiag i ^ 2) = fun _ => (1 : ℝ) := by
      ext i
      have habs := abs_le.mp (hev_le i)
      have hsq : (hH.eigenvalues i) ^ 2 ≤ 1 := by nlinarith
      simp only [sDiag, Real.sq_sqrt (sub_nonneg.mpr hsq)]
      ring
    rw [h1, diagonal_one, Matrix.mul_one, hUUt]
  let W : Matrix (κ × Bool) (κ × Bool) ℝ := Matrix.of fun p q =>
    match p.2, q.2 with
    | false, false => T p.1 q.1
    | false, true => S p.1 q.1
    | true, false => S p.1 q.1
    | true, true => -T p.1 q.1
  have hWSym : W.IsSymm := by
    ext ⟨u, bu⟩ ⟨v, bv⟩
    have hTuv : T v u = T u v := by
      simpa [Matrix.transpose_apply] using congrFun (congrFun hSym.eq u) v
    have hSuv : S v u = S u v := by
      simpa [Matrix.transpose_apply] using congrFun (congrFun hSSym.eq u) v
    cases bu <;> cases bv <;> simp [W, hTuv, hSuv]
  have hWW : Wᵀ * W = 1 := by
    rw [hWSym.eq]
    ext ⟨u, bu⟩ ⟨v, bv⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply,
      Prod.mk.injEq]
    cases bu <;> cases bv
    · simp only [W, of_apply, and_true, Finset.sum_add_distrib]
      have h := congrFun (congrFun hT2_add_S2 u) v
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply] at h
      linarith
    · simp only [W, of_apply, Bool.false_eq_true, and_false, ite_false, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have h := congrFun (congrFun hTS_comm u) v
      simp only [Matrix.mul_apply] at h
      linarith
    · simp only [W, of_apply, Bool.true_eq_false, and_false, ite_false, neg_mul,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have h := congrFun (congrFun hTS_comm u) v
      simp only [Matrix.mul_apply] at h
      linarith
    · simp only [W, of_apply, and_true, neg_mul_neg, Finset.sum_add_distrib]
      have h := congrFun (congrFun hT2_add_S2 u) v
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply] at h
      linarith
  exact ⟨W, hWSym, hWW, fun _ _ => rfl⟩

private theorem exists_pos_eigenvector_of_bipartite {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : κ → Prop} [DecidablePred P] {g : κ → Bool} {Γ : Matrix κ κ ℝ}
    (hSym : Γ.IsSymm)
    (hBip : ∀ u v, Γ u v ≠ 0 → P u ∧ P v ∧ g u ≠ g v)
    (hPos : 0 < opNormR Γ) :
    ∃ δ : κ → ℝ,
      (∑ u, δ u ^ 2 = 1) ∧
      (∀ u, ¬ P u → δ u = 0) ∧
      (Γ *ᵥ δ = opNormR Γ • δ) ∧
      (∀ b : Bool, ∑ u with P u ∧ g u = b, δ u ^ 2 = 1 / 2) := by
  have hH : Γ.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hSym.eq
  have hne : Nonempty κ := by
    by_contra hempty
    have : IsEmpty κ := not_nonempty_iff.mp hempty
    have h0 : Matrix.toEuclideanCLM (𝕜 := ℝ) Γ = 0 := Subsingleton.elim _ _
    simp [opNormR, h0] at hPos
  have hmul_eig (j : κ) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (hH.eigenvectorBasis j) =
        hH.eigenvalues j • hH.eigenvectorBasis j := by
    ext k
    exact congrFun (hH.mulVec_eigenvectorBasis j) k
  have hex_i : ∃ i : κ, |hH.eigenvalues i| = opNormR Γ := by
    have hmax : ∃ i : κ, ∀ j : κ, |hH.eigenvalues j| ≤ |hH.eigenvalues i| :=
      Finite.exists_max (fun j => |hH.eigenvalues j|)
    rcases hmax with ⟨i₀, hi₀⟩
    refine ⟨i₀, le_antisymm ?_ ?_⟩
    · have hvi : ‖hH.eigenvectorBasis i₀‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i₀
      have hle := (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ).le_opNorm (hH.eigenvectorBasis i₀)
      rw [hmul_eig i₀, norm_smul, Real.norm_eq_abs, hvi, mul_one, mul_one] at hle
      exact hle
    · refine Matrix.opNorm_toEuclideanCLM_le_of_inner Γ (abs_nonneg _) fun u v hu hv => ?_
      have hexp : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) =
          ∑ j : κ, hH.eigenvalues j *
            inner ℝ (hH.eigenvectorBasis j) u * inner ℝ (hH.eigenvectorBasis j) v := by
        have hu_sum := hH.eigenvectorBasis.sum_repr u
        have hv_sum := hH.eigenvectorBasis.sum_repr v
        conv_lhs => rw [← hu_sum, ← hv_sum]
        simp only [OrthonormalBasis.repr_apply_apply, map_sum, map_smul, inner_sum, sum_inner,
          inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
        refine Finset.sum_congr rfl fun j₁ _ => ?_
        rw [Finset.sum_eq_single j₁]
        · rw [hmul_eig j₁, inner_smul_right,
            real_inner_self_eq_norm_sq, hH.eigenvectorBasis.orthonormal.1 j₁]
          ring
        · intro j₂ _ hj₂
          rw [hmul_eig j₁, inner_smul_right,
            hH.eigenvectorBasis.orthonormal.2 hj₂]
          ring
        · simp
      rw [hexp]
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ
        (fun j => |inner ℝ (hH.eigenvectorBasis j) u|)
        (fun j => |inner ℝ (hH.eigenvectorBasis j) v|)
      have hparseval (w : EuclideanSpace ℝ κ) (hw : ‖w‖ ≤ 1) :
          ∑ j : κ, |inner ℝ (hH.eigenvectorBasis j) w| ^ 2 ≤ 1 := by
        have hp := hH.eigenvectorBasis.sum_inner_mul_inner w w
        simp only [real_inner_comm w, ← sq, real_inner_self_eq_norm_sq] at hp
        have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
        calc ∑ j : κ, |inner ℝ (hH.eigenvectorBasis j) w| ^ 2
            = ∑ j : κ, inner ℝ w (hH.eigenvectorBasis j) ^ 2 := by simp [real_inner_comm, sq_abs]
          _ = ‖w‖ ^ 2 := hp
          _ ≤ 1 := hw2
      calc ∑ j : κ, hH.eigenvalues j *
            inner ℝ (hH.eigenvectorBasis j) u * inner ℝ (hH.eigenvectorBasis j) v
          ≤ ∑ j : κ, |hH.eigenvalues i₀| *
              (|inner ℝ (hH.eigenvectorBasis j) u| * |inner ℝ (hH.eigenvectorBasis j) v|) := by
              refine sum_le_sum fun j _ => ?_
              calc hH.eigenvalues j * inner ℝ (hH.eigenvectorBasis j) u *
                    inner ℝ (hH.eigenvectorBasis j) v
                  ≤ |hH.eigenvalues j * inner ℝ (hH.eigenvectorBasis j) u *
                      inner ℝ (hH.eigenvectorBasis j) v| := le_abs_self _
                _ = |hH.eigenvalues j| *
                    (|inner ℝ (hH.eigenvectorBasis j) u| *
                      |inner ℝ (hH.eigenvectorBasis j) v|) := by
                    rw [abs_mul, abs_mul]; ring
                _ ≤ |hH.eigenvalues i₀| *
                    (|inner ℝ (hH.eigenvectorBasis j) u| *
                      |inner ℝ (hH.eigenvectorBasis j) v|) :=
                    mul_le_mul_of_nonneg_right (hi₀ j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |hH.eigenvalues i₀| *
            ∑ j : κ, |inner ℝ (hH.eigenvectorBasis j) u| *
              |inner ℝ (hH.eigenvectorBasis j) v| := (mul_sum _ _ _).symm
        _ ≤ |hH.eigenvalues i₀| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            calc ∑ j : κ, |inner ℝ (hH.eigenvectorBasis j) u| *
                  |inner ℝ (hH.eigenvectorBasis j) v|
                ≤ √(∑ j, |inner ℝ (hH.eigenvectorBasis j) u| ^ 2) *
                    √(∑ j, |inner ℝ (hH.eigenvectorBasis j) v| ^ 2) := hcs
              _ ≤ √1 * √1 := mul_le_mul (Real.sqrt_le_sqrt (hparseval u hu))
                    (Real.sqrt_le_sqrt (hparseval v hv)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
              _ = 1 := by simp
        _ = |hH.eigenvalues i₀| := mul_one _
  rcases hex_i with ⟨i₀, hi₀⟩
  let v₀ : κ → ℝ := (hH.eigenvectorBasis i₀).ofLp
  have hv₀_sq : ∑ u, v₀ u ^ 2 = 1 := by
    have hn : ‖hH.eigenvectorBasis i₀‖ ^ 2 = 1 := by
      rw [hH.eigenvectorBasis.orthonormal.1 i₀]; norm_num
    rwa [EuclideanSpace.real_norm_sq_eq] at hn
  have hv₀_eig : Γ *ᵥ v₀ = hH.eigenvalues i₀ • v₀ := hH.mulVec_eigenvectorBasis i₀
  let δ : κ → ℝ :=
    if 0 ≤ hH.eigenvalues i₀ then v₀
    else fun u => (if g u then -1 else 1) * v₀ u
  have hδ_sq : ∑ u, δ u ^ 2 = 1 := by
    by_cases hsign : 0 ≤ hH.eigenvalues i₀
    · simp [δ, hsign, hv₀_sq]
    · simp only [δ, hsign, ↓reduceIte]
      have hsq_eq : (fun u : κ => ((if g u then (-1 : ℝ) else 1) * v₀ u) ^ 2) =
          fun u => v₀ u ^ 2 := by
        ext u; cases g u <;> simp
      rw [hsq_eq, hv₀_sq]
  have hδ_eig : Γ *ᵥ δ = opNormR Γ • δ := by
    by_cases hsign : 0 ≤ hH.eigenvalues i₀
    · have hev : hH.eigenvalues i₀ = opNormR Γ := by rwa [abs_of_nonneg hsign] at hi₀
      have hδ_eq : δ = v₀ := by simp [δ, hsign]
      rw [hδ_eq, hv₀_eig, hev]
    · push Not at hsign
      have hev : hH.eigenvalues i₀ = -opNormR Γ := by
        have := abs_of_neg hsign; linarith
      ext u
      simp only [δ, hsign.not_ge, ↓reduceIte, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      have hterm : ∑ w : κ, Γ u w * ((if g w then -1 else 1) * v₀ w) =
          -(if g u then -1 else 1) * ∑ w : κ, Γ u w * v₀ w := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun w _ => ?_
        by_cases hΓ0 : Γ u w = 0
        · simp [hΓ0]
        · have hdiff := (hBip u w hΓ0).2.2
          cases hgu : g u <;> cases hgw : g w <;> simp_all
      rw [hterm]
      have hv_u := congrFun hv₀_eig u
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hev] at hv_u
      rw [hv_u]
      ring
  have hδ_supp : ∀ u, ¬ P u → δ u = 0 := by
    intro u hnotP
    have h1 := congrFun hδ_eig u
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    have h0 : ∑ w : κ, Γ u w * δ w = 0 := sum_eq_zero fun w _ => by
      by_cases hΓ0 : Γ u w = 0
      · simp [hΓ0]
      · exact (hnotP (hBip u w hΓ0).1).elim
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hPos.ne'
  let δ_flip : κ → ℝ := fun u => (if g u then -1 else 1) * δ u
  have hflip_eig : Γ *ᵥ δ_flip = (-opNormR Γ) • δ_flip := by
    ext u
    simp only [δ_flip, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have hterm : ∑ w : κ, Γ u w * ((if g w then -1 else 1) * δ w) =
        -(if g u then -1 else 1) * ∑ w : κ, Γ u w * δ w := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun w _ => ?_
      by_cases hΓ0 : Γ u w = 0
      · simp [hΓ0]
      · have hdiff := (hBip u w hΓ0).2.2
        cases hgu : g u <;> cases hgw : g w <;> simp_all
    rw [hterm]
    have h1 := congrFun hδ_eig u
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]; ring
  have horth : ∑ u : κ, δ u * δ_flip u = 0 := by
    have hsym_dot : (Γ *ᵥ δ) ⬝ᵥ δ_flip = δ ⬝ᵥ (Γ *ᵥ δ_flip) := by
      simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
      have hΓuw : Γ w u = Γ u w := by
        simpa [Matrix.transpose_apply] using congrFun (congrFun hSym.eq u) w
      rw [hΓuw]; ring
    rw [hδ_eig, hflip_eig, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hsym_dot
    have h2 : (2 * opNormR Γ) * (δ ⬝ᵥ δ_flip) = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left (by linarith)
  have hpart_sum :
      (∑ u with P u ∧ g u = false, δ u ^ 2) + (∑ u with P u ∧ g u = true, δ u ^ 2) = 1 := by
    rw [← hδ_sq]
    have hP_only : ∑ u : κ, δ u ^ 2 = ∑ u with P u, δ u ^ 2 := by
      rw [sum_filter]
      refine sum_congr rfl fun u _ => ?_
      by_cases hPu : P u
      · simp [hPu]
      · simp [hPu, hδ_supp u hPu]
    rw [hP_only, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    cases g u <;> simp
  have hpart_diff :
      (∑ u with P u ∧ g u = false, δ u ^ 2) - (∑ u with P u ∧ g u = true, δ u ^ 2) = 0 := by
    rw [← horth, sum_filter, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ => ?_
    by_cases hPu : P u
    · cases hgu : g u <;> simp [δ_flip, hPu, hgu] <;> ring
    · simp [δ_flip, hPu, hδ_supp u hPu]
  refine ⟨δ, hδ_sq, hδ_supp, hδ_eig, fun b => ?_⟩
  cases b <;> linarith

end OrthogonalDilation

/-- **Spectral Norm Multiplicativity (`lem:mnorm`)**: for symmetric adversary matrices `Γ_f` of
`(P_f, f)` and `Γ_g j` of `(P_g j, g j)`,
`‖composedAdversaryMatrix P_g g Γ_f Γ_g‖ = ‖Γ_f‖ * ∏ j, ‖Γ_g j‖`. -/
theorem opNorm_composedAdversaryMatrix {n : ℕ} {k : Fin n → ℕ}
    {P_f : BitString n → Prop} {f : BitString n → Bool}
    {P_g : ∀ j : Fin n, BitString (k j) → Prop}
    {g : ∀ j : Fin n, BitString (k j) → Bool}
    {Γ_f : Matrix (BitString n) (BitString n) ℝ}
    {Γ_g : ∀ j : Fin n, Matrix (BitString (k j)) (BitString (k j)) ℝ}
    (hSym_f : Γ_f.IsSymm) (hAdv_f : IsAdversaryMatrix P_f f Γ_f)
    (hSym_g : ∀ j, (Γ_g j).IsSymm) (hAdv_g : ∀ j, IsAdversaryMatrix (P_g j) (g j) (Γ_g j)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (composedAdversaryMatrix P_g g Γ_f Γ_g)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ *
        ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ := by
  classical
  change opNormR (composedAdversaryMatrix P_g g Γ_f Γ_g) =
    opNormR Γ_f * ∏ j : Fin n, opNormR (Γ_g j)
  set Γ_h := composedAdversaryMatrix P_g g Γ_f Γ_g
  by_cases hzero : opNormR Γ_f = 0 ∨ ∃ j : Fin n, opNormR (Γ_g j) = 0
  · have hrhs0 : opNormR Γ_f * ∏ j : Fin n, opNormR (Γ_g j) = 0 := by
      rcases hzero with hf0 | ⟨j, hj0⟩
      · rw [hf0, zero_mul]
      · rw [Finset.prod_eq_zero (Finset.mem_univ j) hj0, mul_zero]
    have hΓh0 : Γ_h = 0 := by
      ext x y
      simp only [Γ_h, composedAdversaryMatrix, Matrix.of_apply, Matrix.zero_apply]
      rcases hzero with hf0 | ⟨j, hj0⟩
      · have hΓf0 : Γ_f = 0 := by
          have hclm0 : Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f = 0 := norm_eq_zero.mp hf0
          ext a b
          have := Matrix.abs_entry_le_norm_toEuclideanCLM Γ_f a b
          rw [hclm0, norm_zero] at this
          exact abs_nonpos_iff.mp this
        simp [hΓf0]
      · have hΓgj0 : Γ_g j = 0 := by
          have hclm0 : Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j) = 0 := norm_eq_zero.mp hj0
          ext a b
          have := Matrix.abs_entry_le_norm_toEuclideanCLM (Γ_g j) a b
          rw [hclm0, norm_zero] at this
          exact abs_nonpos_iff.mp this
        have h0op : opNormR (0 : Matrix (BitString (k j)) (BitString (k j)) ℝ) = 0 := by
          simp [opNormR]
        have hhat0 : hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) = 0 := by
          simp [hatAdversary, hΓgj0, h0op]
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hhat0, mul_zero]
    rw [hΓh0, hrhs0]
    simp [opNormR]
  push Not at hzero
  rcases hzero with ⟨hf_ne, hg_ne⟩
  have hf_pos : 0 < opNormR Γ_f := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf_ne)
  have hg_pos : ∀ j : Fin n, 0 < opNormR (Γ_g j) :=
    fun j => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hg_ne j))
  refine le_antisymm ?_ ?_
  · have hdil : ∀ j : Fin n,
        ∃ W : Matrix (BitString (k j) × Bool) (BitString (k j) × Bool) ℝ,
          W.IsSymm ∧ Wᵀ * W = 1 ∧
            ∀ u v, W (u, false) (v, false) = ((opNormR (Γ_g j))⁻¹ • Γ_g j) u v := by
      intro j
      have hsym_scaled : (((opNormR (Γ_g j))⁻¹ : ℝ) • Γ_g j).IsSymm := by
        ext u v
        have hvu : Γ_g j v u = Γ_g j u v := by
          simpa [Matrix.transpose_apply] using congrFun (congrFun (hSym_g j).eq u) v
        simp [hvu]
      have hnorm_scaled : opNormR (((opNormR (Γ_g j))⁻¹ : ℝ) • Γ_g j) ≤ 1 := by
        have hnn : 0 ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖)⁻¹ :=
          inv_nonneg.mpr (norm_nonneg _)
        have hne_clm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ ≠ 0 := hg_ne j
        dsimp only [opNormR]
        rw [map_smul, norm_smul, Real.norm_of_nonneg hnn, inv_mul_cancel₀ hne_clm]
      exact exists_orth_involution_dilation hsym_scaled hnorm_scaled
    choose W hW_sym hW_orth hW_corner using hdil
    let V : ∀ j : Fin n, Bool → Matrix (BitString (k j) × Bool) (BitString (k j) × Bool) ℝ :=
      fun j b => if b then W j else 1
    have hVtV : ∀ (j : Fin n) (b₁ b₂ : Bool) (u v : BitString (k j)),
        P_g j u → P_g j v → g j u = b₁ → g j v = b₂ →
          (((V j b₁)ᵀ * V j b₂) (u, false) (v, false)) =
            (opNormR (Γ_g j))⁻¹ * hatAdversary (P_g j) (Γ_g j) u v := by
      intro j b₁ b₂ u v hPu hPv hgu hgv
      cases b₁ <;> cases b₂
      · simp only [V, Bool.false_eq_true, ↓reduceIte, transpose_one, Matrix.mul_one,
          Matrix.one_apply, Prod.mk.injEq, and_true, hatAdversary, Matrix.of_apply]
        have hΓ0 : Γ_g j u v = 0 := by
          by_contra hne0
          exact (hAdv_g j u v hne0).2.2 (hgu.trans hgv.symm)
        rw [hΓ0, zero_add]
        by_cases huv : u = v
        · subst huv; simp [hPu, inv_mul_cancel₀ (hg_ne j)]
        · simp [huv]
      · simp only [V, Bool.false_eq_true, ↓reduceIte, transpose_one, Matrix.one_mul, hW_corner,
          Matrix.smul_apply, smul_eq_mul, hatAdversary, Matrix.of_apply]
        have huv : u ≠ v := fun h => by subst h; rw [hgu] at hgv; cases hgv
        simp [huv]
      · simp only [V, Bool.false_eq_true, ↓reduceIte, Matrix.mul_one, (hW_sym j).eq, hW_corner,
          Matrix.smul_apply, smul_eq_mul, hatAdversary, Matrix.of_apply]
        have huv : u ≠ v := fun h => by subst h; rw [hgu] at hgv; cases hgv
        simp [huv]
      · simp only [V, ↓reduceIte, hW_orth j, Matrix.one_apply, Prod.mk.injEq, and_true,
          hatAdversary, Matrix.of_apply]
        have hΓ0 : Γ_g j u v = 0 := by
          by_contra hne0
          exact (hAdv_g j u v hne0).2.2 (hgu.trans hgv.symm)
        rw [hΓ0, zero_add]
        by_cases huv : u = v
        · subst huv; simp [hPu, inv_mul_cancel₀ (hg_ne j)]
        · simp [huv]
    let Ω := ∀ j : Fin n, BitString (k j) × Bool
    let P_all : BitString (∑ j : Fin n, k j) → Prop := fun x => ∀ j : Fin n, P_g j (inputBlock x j)
    let ψVec (u : EuclideanSpace ℝ (BitString (∑ j : Fin n, k j)))
        (z : BitString n) : EuclideanSpace ℝ Ω :=
      WithLp.toLp 2 fun ω =>
        ∑ x with P_all x ∧ evalInnerBlocks g x = z,
          u.ofLp x * ∏ j : Fin n, V j (z j) (ω j) (inputBlock x j, false)
    have hinner_ψ : ∀ (u v : EuclideanSpace ℝ (BitString (∑ j : Fin n, k j)))
        (z₁ z₂ : BitString n),
        inner ℝ (ψVec u z₁) (ψVec v z₂) =
          (∏ j : Fin n, (opNormR (Γ_g j))⁻¹) *
            ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
              ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
                u.ofLp x * v.ofLp y *
                  ∏ j : Fin n, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) := by
      intro u v z₁ z₂
      rw [PiLp.inner_apply]
      simp only [ψVec, RCLike.inner_apply, conj_trivial]
      calc ∑ ω : Ω,
            (∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
              v.ofLp y * ∏ j, V j (z₂ j) (ω j) (inputBlock y j, false)) *
            (∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
              u.ofLp x * ∏ j, V j (z₁ j) (ω j) (inputBlock x j, false))
          = ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
              ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
                u.ofLp x * v.ofLp y *
                  ∑ ω : Ω, ∏ j : Fin n,
                    (V j (z₁ j) (ω j) (inputBlock x j, false) *
                      V j (z₂ j) (ω j) (inputBlock y j, false)) := by
              simp only [sum_mul, mul_sum]
              rw [Finset.sum_comm]
              refine sum_congr rfl fun x _ => ?_
              rw [Finset.sum_comm]
              refine sum_congr rfl fun y _ => sum_congr rfl fun ω _ => ?_
              calc (v.ofLp y * ∏ j, V j (z₂ j) (ω j) (inputBlock y j, false)) *
                    (u.ofLp x * ∏ j, V j (z₁ j) (ω j) (inputBlock x j, false))
                  = u.ofLp x * v.ofLp y *
                      ((∏ j, V j (z₁ j) (ω j) (inputBlock x j, false)) *
                        (∏ j, V j (z₂ j) (ω j) (inputBlock y j, false))) := by ring
                _ = u.ofLp x * v.ofLp y *
                      ∏ j, (V j (z₁ j) (ω j) (inputBlock x j, false) *
                        V j (z₂ j) (ω j) (inputBlock y j, false)) := by
                    rw [← Finset.prod_mul_distrib]
        _ = ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
              ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
                u.ofLp x * v.ofLp y *
                  ∏ j : Fin n,
                    (((V j (z₁ j))ᵀ * V j (z₂ j)) (inputBlock x j, false) (inputBlock y j,
                      false)) := by
              refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
              congr 1
              let fprod (j : Fin n) (ωj : BitString (k j) × Bool) : ℝ :=
                V j (z₁ j) ωj (inputBlock x j, false) * V j (z₂ j) ωj (inputBlock y j, false)
              have hpi := (Finset.prod_univ_sum
                (t := fun _ : Fin n => (Finset.univ : Finset (BitString (k _) × Bool))) fprod).symm
              rw [Fintype.piFinset_univ] at hpi
              exact hpi
        _ = (∏ j : Fin n, (opNormR (Γ_g j))⁻¹) *
              ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
                ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
                  u.ofLp x * v.ofLp y *
                    ∏ j : Fin n,
                      hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) := by
              rw [Finset.mul_sum]
              refine sum_congr rfl fun x hx => ?_
              rw [Finset.mul_sum]
              refine sum_congr rfl fun y hy => ?_
              obtain ⟨hPx, hzx⟩ := (Finset.mem_filter.mp hx).2
              obtain ⟨hPy, hzy⟩ := (Finset.mem_filter.mp hy).2
              have hprod_eq :
                  ∏ j : Fin n,
                    (((V j (z₁ j))ᵀ * V j (z₂ j)) (inputBlock x j, false) (inputBlock y j, false)) =
                  (∏ j : Fin n, (opNormR (Γ_g j))⁻¹) *
                    ∏ j : Fin n,
                      hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) := by
                rw [← Finset.prod_mul_distrib]
                refine Finset.prod_congr rfl fun j _ =>
                  hVtV j (z₁ j) (z₂ j) (inputBlock x j) (inputBlock y j)
                    (hPx j) (hPy j) (congrFun hzx j) (congrFun hzy j)
              rw [hprod_eq]
              ring
    have hnorm_ψ : ∀ u : EuclideanSpace ℝ (BitString (∑ j : Fin n, k j)),
        ∑ z : BitString n, ‖ψVec u z‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      intro u
      have h_z (z : BitString n) :
          ‖ψVec u z‖ ^ 2 = ∑ x with P_all x ∧ evalInnerBlocks g x = z, u.ofLp x ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hinner_ψ u u z z]
        have hdiag :
            ∑ x with P_all x ∧ evalInnerBlocks g x = z,
              ∑ y with P_all y ∧ evalInnerBlocks g y = z,
                u.ofLp x * u.ofLp y *
                  ∏ j : Fin n, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j) =
            (∏ j : Fin n, opNormR (Γ_g j)) *
              ∑ x with P_all x ∧ evalInnerBlocks g x = z, u.ofLp x ^ 2 := by
          rw [Finset.mul_sum]
          refine sum_congr rfl fun x hx => ?_
          obtain ⟨hPx, hzx⟩ := (Finset.mem_filter.mp hx).2
          rw [Finset.sum_eq_single x]
          · have hself : ∏ j : Fin n,
                hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock x j) =
                ∏ j : Fin n, opNormR (Γ_g j) := by
              refine Finset.prod_congr rfl fun j _ => ?_
              have h0 : Γ_g j (inputBlock x j) (inputBlock x j) = 0 := by
                by_contra hne0
                exact (hAdv_g j _ _ hne0).2.2 rfl
              simp [hatAdversary, h0, hPx j]
            rw [hself]; ring
          · intro y hy hyx
            obtain ⟨_, hzy⟩ := (Finset.mem_filter.mp hy).2
            have hdiff_blk : ∃ j : Fin n, inputBlock x j ≠ inputBlock y j := by
              by_contra hall
              push Not at hall
              exact hyx ((bitStringBlockEquiv k).injective (funext hall)).symm
            rcases hdiff_blk with ⟨j₀, hj₀⟩
            have hhat0 : hatAdversary (P_g j₀) (Γ_g j₀) (inputBlock x j₀) (inputBlock y j₀) =
              0 := by
              have h0 : Γ_g j₀ (inputBlock x j₀) (inputBlock y j₀) = 0 := by
                by_contra hne0
                exact (hAdv_g j₀ _ _ hne0).2.2
                  ((congrFun hzx j₀).trans (congrFun hzy j₀).symm)
              simp [hatAdversary, h0, hj₀]
            rw [Finset.prod_eq_zero (Finset.mem_univ j₀) hhat0, mul_zero]
          · intro hnot; exact (hnot hx).elim
        rw [hdiag, ← mul_assoc, ← Finset.prod_mul_distrib]
        have h1 : ∏ j : Fin n, ((opNormR (Γ_g j))⁻¹ * opNormR (Γ_g j)) = 1 :=
          Finset.prod_eq_one fun j _ => inv_mul_cancel₀ (hg_ne j)
        rw [h1, one_mul]
      simp only [h_z, EuclideanSpace.real_norm_sq_eq]
      have hcollapse :
          ∑ z : BitString n, ∑ x with P_all x ∧ evalInnerBlocks g x = z, u.ofLp x ^ 2 =
            ∑ x with P_all x, u.ofLp x ^ 2 := by
        simp only [sum_filter]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun x _ => ?_
        by_cases hPx : P_all x
        · simp [hPx]
        · simp [hPx]
      rw [hcollapse]
      exact Finset.sum_le_univ_sum_of_nonneg fun x => sq_nonneg (u.ofLp x)
    refine Matrix.opNorm_toEuclideanCLM_le_of_inner Γ_h
      (mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _ => norm_nonneg _)) fun u v hu hv => ?_
    have hbilin :
        inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_h v) =
          (∏ j : Fin n, opNormR (Γ_g j)) *
            ∑ z₁ : BitString n, ∑ z₂ : BitString n,
              Γ_f z₁ z₂ * inner ℝ (ψVec u z₁) (ψVec v z₂) := by
      simp only [hinner_ψ]
      have h1 : (∏ j : Fin n, opNormR (Γ_g j)) * (∏ j : Fin n, (opNormR (Γ_g j))⁻¹) = 1 := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (hg_ne j)
      have hcancel :
          (∏ j : Fin n, opNormR (Γ_g j)) *
            ∑ z₁ : BitString n, ∑ z₂ : BitString n,
              Γ_f z₁ z₂ * ((∏ j : Fin n, (opNormR (Γ_g j))⁻¹) *
                ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
                  ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
                    u.ofLp x * v.ofLp y *
                      ∏ j : Fin n,
                        hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j)) =
          ∑ z₁ : BitString n, ∑ z₂ : BitString n,
            ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
              ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
                Γ_f z₁ z₂ * (u.ofLp x * v.ofLp y *
                  ∏ j : Fin n,
                    hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j)) := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun z₁ _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun z₂ _ => ?_
        set S_xy := ∑ x with P_all x ∧ evalInnerBlocks g x = z₁,
          ∑ y with P_all y ∧ evalInnerBlocks g y = z₂,
            u.ofLp x * v.ofLp y *
              ∏ j : Fin n, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j)
        have hscalar :
            (∏ j, opNormR (Γ_g j)) * (Γ_f z₁ z₂ * ((∏ j, (opNormR (Γ_g j))⁻¹) * S_xy)) =
              Γ_f z₁ z₂ * S_xy := by
          calc (∏ j, opNormR (Γ_g j)) * (Γ_f z₁ z₂ * ((∏ j, (opNormR (Γ_g j))⁻¹) * S_xy))
              = Γ_f z₁ z₂ * (((∏ j, opNormR (Γ_g j)) * (∏ j, (opNormR (Γ_g j))⁻¹)) * S_xy) := by
                ring
            _ = Γ_f z₁ z₂ * S_xy := by rw [h1, one_mul]
        rw [hscalar]
        simp only [S_xy, Finset.mul_sum]
      rw [hcancel, Matrix.inner_toEuclideanCLM, dotProduct]
      simp only [mulVec, dotProduct, mul_sum, sum_filter]
      have hrhs_swap :
          (∑ z₁ : BitString n, ∑ z₂ : BitString n,
            ∑ x : BitString (∑ j, k j),
              if P_all x ∧ evalInnerBlocks g x = z₁ then
                ∑ y : BitString (∑ j, k j),
                  if P_all y ∧ evalInnerBlocks g y = z₂ then
                    Γ_f z₁ z₂ * (u.ofLp x * v.ofLp y *
                      ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j))
                  else 0
              else 0) =
          ∑ x : BitString (∑ j, k j), ∑ y : BitString (∑ j, k j),
            ∑ z₁ : BitString n, ∑ z₂ : BitString n,
              if P_all x ∧ evalInnerBlocks g x = z₁ then
                if P_all y ∧ evalInnerBlocks g y = z₂ then
                  Γ_f z₁ z₂ * (u.ofLp x * v.ofLp y *
                    ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j))
                else 0
              else 0 := by
        have hstep1 : ∀ z₁ z₂ : BitString n,
            (∑ x : BitString (∑ j, k j),
              if P_all x ∧ evalInnerBlocks g x = z₁ then
                ∑ y : BitString (∑ j, k j),
                  if P_all y ∧ evalInnerBlocks g y = z₂ then
                    Γ_f z₁ z₂ * (u.ofLp x * v.ofLp y *
                      ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j))
                  else 0
              else 0) =
            ∑ x, ∑ y,
              if P_all x ∧ evalInnerBlocks g x = z₁ then
                if P_all y ∧ evalInnerBlocks g y = z₂ then
                  Γ_f z₁ z₂ * (u.ofLp x * v.ofLp y *
                    ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (inputBlock y j))
                else 0
              else 0 := by
          intro z₁ z₂
          refine sum_congr rfl fun x _ => ?_
          by_cases hx : P_all x ∧ evalInnerBlocks g x = z₁ <;> simp [hx]
        simp_rw [hstep1]
        conv_lhs =>
          enter [2, z₁]
          rw [Finset.sum_comm]
        conv_lhs =>
          enter [2, z₁, 2, x]
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        conv_lhs =>
          enter [2, x]
          rw [Finset.sum_comm]
      rw [hrhs_swap]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      by_cases hPxy : P_all x ∧ P_all y
      · rcases hPxy with ⟨hPx, hPy⟩
        simp only [hPx, hPy, true_and]
        rw [Finset.sum_eq_single (evalInnerBlocks g x)]
        · rw [Finset.sum_eq_single (evalInnerBlocks g y)]
          · simp only [↓reduceIte, Γ_h, composedAdversaryMatrix, Matrix.of_apply]
            ring
          · intro z₂ _ hz₂; simp [Ne.symm hz₂]
          · simp
        · intro z₁ _ hz₁; simp [Ne.symm hz₁]
        · simp
      · have hzero_entry : Γ_h x y = 0 := by
          by_contra hne0
          have hadv := isAdversaryMatrix_composedAdversaryMatrix hAdv_f hAdv_g x y hne0
          exact hPxy ⟨hadv.1.1, hadv.2.1.1⟩
        rw [hzero_entry, zero_mul, mul_zero]
        refine (sum_eq_zero fun z₁ _ => sum_eq_zero fun z₂ _ => ?_).symm
        by_cases hx1 : P_all x ∧ evalInnerBlocks g x = z₁
        · by_cases hy2 : P_all y ∧ evalInnerBlocks g y = z₂
          · exact (hPxy ⟨hx1.1, hy2.1⟩).elim
          · simp [hx1, hy2]
        · simp [hx1]
    rw [hbilin]
    have hcoord_bound :
        |∑ z₁ : BitString n, ∑ z₂ : BitString n,
            Γ_f z₁ z₂ * inner ℝ (ψVec u z₁) (ψVec v z₂)| ≤ opNormR Γ_f := by
      have hexp_ω :
          (∑ z₁ : BitString n, ∑ z₂ : BitString n,
            Γ_f z₁ z₂ * inner ℝ (ψVec u z₁) (ψVec v z₂)) =
          ∑ ω : Ω, ∑ z₁ : BitString n, ∑ z₂ : BitString n,
            (ψVec u z₁).ofLp ω * Γ_f z₁ z₂ * (ψVec v z₂).ofLp ω := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_sum]
        conv_lhs => enter [2, z₁]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        exact sum_congr rfl fun ω _ => sum_congr rfl fun z₁ _ =>
          sum_congr rfl fun z₂ _ => by ring
      rw [hexp_ω]
      have hnorm_eq : ‖Γ_f‖ = opNormR Γ_f := (Matrix.l2_opNorm_toEuclideanCLM Γ_f).symm
      calc |∑ ω : Ω, ∑ z₁ : BitString n, ∑ z₂ : BitString n,
              (ψVec u z₁).ofLp ω * Γ_f z₁ z₂ * (ψVec v z₂).ofLp ω|
          ≤ ∑ ω : Ω, ‖Γ_f‖ * √(∑ z₁, (ψVec u z₁).ofLp ω ^ 2) *
              √(∑ z₂, (ψVec v z₂).ofLp ω ^ 2) :=
            (abs_sum_le_sum_abs _ _).trans
              (sum_le_sum fun ω _ => Matrix.abs_sum_mul_le_l2_opNorm Γ_f _ _)
        _ = opNormR Γ_f * ∑ ω : Ω,
              √(∑ z₁, (ψVec u z₁).ofLp ω ^ 2) * √(∑ z₂, (ψVec v z₂).ofLp ω ^ 2) := by
            rw [hnorm_eq]; simp only [mul_assoc, ← mul_sum]
        _ ≤ opNormR Γ_f *
              (√(∑ ω : Ω, ∑ z₁, (ψVec u z₁).ofLp ω ^ 2) *
                √(∑ ω : Ω, ∑ z₂, (ψVec v z₂).ofLp ω ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (Real.sum_sqrt_mul_sqrt_le univ
                (fun _ => sum_nonneg fun _ _ => sq_nonneg _)
                (fun _ => sum_nonneg fun _ _ => sq_nonneg _))
              (norm_nonneg _)
        _ ≤ opNormR Γ_f * (√(‖u‖ ^ 2) * √(‖v‖ ^ 2)) := by
            have hswap (w : EuclideanSpace ℝ (BitString (∑ j : Fin n, k j))) :
                ∑ ω : Ω, ∑ z : BitString n, (ψVec w z).ofLp ω ^ 2 ≤ ‖w‖ ^ 2 := by
              rw [Finset.sum_comm]
              simpa [EuclideanSpace.real_norm_sq_eq] using hnorm_ψ w
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.sqrt_le_sqrt (hswap u)) (Real.sqrt_le_sqrt (hswap v))
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
              (norm_nonneg _)
        _ ≤ opNormR Γ_f * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg v)]
            exact (mul_le_mul hu hv (norm_nonneg v) zero_le_one).trans_eq (one_mul 1)
        _ = opNormR Γ_f := mul_one _
    calc (∏ j : Fin n, opNormR (Γ_g j)) *
          ∑ z₁, ∑ z₂, Γ_f z₁ z₂ * inner ℝ (ψVec u z₁) (ψVec v z₂)
        ≤ (∏ j : Fin n, opNormR (Γ_g j)) * opNormR Γ_f :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcoord_bound)
            (prod_nonneg fun _ _ => norm_nonneg _)
      _ = opNormR Γ_f * ∏ j : Fin n, opNormR (Γ_g j) := mul_comm _ _
  · obtain ⟨δ_f, hδf_sq, hδf_supp, hδf_eig, _⟩ :=
      exists_pos_eigenvector_of_bipartite hSym_f hAdv_f hf_pos
    have hex_g := fun j : Fin n =>
      exists_pos_eigenvector_of_bipartite (hSym_g j) (hAdv_g j) (hg_pos j)
    choose δ_g hδg_sq hδg_supp hδg_eig hδg_half using hex_g
    let δ_h : EuclideanSpace ℝ (BitString (∑ j : Fin n, k j)) :=
      WithLp.toLp 2 fun x => δ_f (evalInnerBlocks g x) * ∏ j : Fin n, δ_g j (inputBlock x j)
    have hδh_norm_sq : ‖δ_h‖ ^ 2 = (1 / 2 : ℝ) ^ n := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [δ_h, mul_pow, ← Finset.prod_pow]
      have hby_P :
          ∑ x : BitString (∑ j : Fin n, k j),
              δ_f (evalInnerBlocks g x) ^ 2 * ∏ j, δ_g j (inputBlock x j) ^ 2 =
          ∑ z : BitString n, δ_f z ^ 2 *
            ∏ j : Fin n, ∑ u with P_g j u ∧ g j u = z j, δ_g j u ^ 2 := by
        have hreindex :
            ∑ x : BitString (∑ j : Fin n, k j),
                δ_f (evalInnerBlocks g x) ^ 2 * ∏ j, δ_g j (inputBlock x j) ^ 2 =
            ∑ xb : ∀ j : Fin n, BitString (k j),
                δ_f (fun j => g j (xb j)) ^ 2 * ∏ j, δ_g j (xb j) ^ 2 :=
          Fintype.sum_equiv (bitStringBlockEquiv k) _ _ fun _ => rfl
        rw [hreindex]
        have hpart :
            ∑ xb : ∀ j : Fin n, BitString (k j),
                δ_f (fun j => g j (xb j)) ^ 2 * ∏ j, δ_g j (xb j) ^ 2 =
            ∑ z : BitString n,
              ∑ xb : ∀ j : Fin n, BitString (k j),
                if (fun j => g j (xb j)) = z then
                  δ_f z ^ 2 * ∏ j, δ_g j (xb j) ^ 2
                else 0 := by
          rw [Finset.sum_comm]
          refine sum_congr rfl fun xb _ => ?_
          rw [Finset.sum_eq_single (fun j => g j (xb j))]
          · simp
          · intro z _ hz; simp [Ne.symm hz]
          · simp
        rw [hpart]
        refine sum_congr rfl fun z _ => ?_
        have hpull :
            (∑ xb : ∀ j : Fin n, BitString (k j),
              if (fun j => g j (xb j)) = z then
                δ_f z ^ 2 * ∏ j, δ_g j (xb j) ^ 2
              else 0) =
            δ_f z ^ 2 *
              ∑ xb : ∀ j : Fin n, BitString (k j),
                if (fun j => g j (xb j)) = z then ∏ j, δ_g j (xb j) ^ 2 else 0 := by
          rw [Finset.mul_sum]
          refine sum_congr rfl fun xb _ => ?_
          split_ifs <;> ring
        rw [hpull]
        congr 1
        simp only [sum_filter]
        have hpi :
            (∑ xb : ∀ j : Fin n, BitString (k j),
              if (fun j => g j (xb j)) = z then ∏ j, δ_g j (xb j) ^ 2 else 0) =
            ∑ xb : ∀ j : Fin n, BitString (k j),
              ∏ j : Fin n, (if P_g j (xb j) ∧ g j (xb j) = z j then δ_g j (xb j) ^ 2 else 0) := by
          refine sum_congr rfl fun xb _ => ?_
          by_cases hPxb : ∀ j, P_g j (xb j)
          · by_cases hgz : (fun j => g j (xb j)) = z
            · simp only [hgz, ↓reduceIte]
              exact Finset.prod_congr rfl fun j _ => by simp [hPxb j, congrFun hgz j]
            · simp only [hgz, ↓reduceIte]
              rcases Function.ne_iff.mp hgz with ⟨j₀, hj₀⟩
              exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm
          · push Not at hPxb
            rcases hPxb with ⟨j₀, hj₀⟩
            have h0 : δ_g j₀ (xb j₀) ^ 2 = 0 := by simp [hδg_supp j₀ _ hj₀]
            have hlhs0 : (if (fun j => g j (xb j)) = z then ∏ j, δ_g j (xb j) ^ 2 else 0) = 0 := by
              split_ifs
              · exact Finset.prod_eq_zero (Finset.mem_univ j₀) h0
              · rfl
            rw [hlhs0]
            exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm
        rw [hpi]
        let f_sq (j : Fin n) (u : BitString (k j)) : ℝ :=
          if P_g j u ∧ g j u = z j then δ_g j u ^ 2 else 0
        have hprod_sq := (Finset.prod_univ_sum
          (t := fun j : Fin n => (Finset.univ : Finset (BitString (k j)))) f_sq).symm
        rw [Fintype.piFinset_univ] at hprod_sq
        exact hprod_sq
      rw [hby_P]
      have hhalf_prod : ∀ z : BitString n,
          ∏ j : Fin n, (∑ u with P_g j u ∧ g j u = z j, δ_g j u ^ 2) = (1 / 2 : ℝ) ^ n := by
        intro z
        have hterm : ∀ j : Fin n,
            (∑ u with P_g j u ∧ g j u = z j, δ_g j u ^ 2) = (1 / 2 : ℝ) :=
          fun j => hδg_half j (z j)
        simp only [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp only [hhalf_prod, ← Finset.sum_mul, hδf_sq, one_mul]
    have hδh_pos : 0 < ‖δ_h‖ := by
      have hsq_pos : 0 < ‖δ_h‖ ^ 2 := by rw [hδh_norm_sq]; positivity
      nlinarith [norm_nonneg δ_h]
    have hinner_block : ∀ (j : Fin n) (u : BitString (k j)) (b : Bool),
        P_g j u →
          ∑ v with P_g j v ∧ g j v = b,
            hatAdversary (P_g j) (Γ_g j) u v * δ_g j v =
          opNormR (Γ_g j) * δ_g j u := by
      intro j u b hPu
      have heig_u := congrFun (hδg_eig j) u
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at heig_u
      by_cases hgu : g j u = b
      · rw [Finset.sum_eq_single u]
        · have h0 : Γ_g j u u = 0 := by
            by_contra hne0; exact (hAdv_g j u u hne0).2.2 rfl
          simp [hatAdversary, h0, hPu]
        · intro v hv hvu
          obtain ⟨_, hgv⟩ := (Finset.mem_filter.mp hv).2
          have h0 : Γ_g j u v = 0 := by
            by_contra hne0; exact (hAdv_g j u v hne0).2.2 (hgu.trans hgv.symm)
          simp [hatAdversary, h0, Ne.symm hvu]
        · intro hnot
          exact (hnot (Finset.mem_filter.mpr ⟨mem_univ u, hPu, hgu⟩)).elim
      · rw [← heig_u, sum_filter]
        refine sum_congr rfl fun v _ => ?_
        by_cases hPv : P_g j v ∧ g j v = b
        · have huv : u ≠ v := fun h => hgu (h ▸ hPv.2)
          simp [hPv, hatAdversary, huv]
        · simp only [hPv, ↓reduceIte]
          by_cases hΓ0 : Γ_g j u v = 0
          · simp [hΓ0]
          · obtain ⟨_, hPv1, hdiff⟩ := hAdv_g j u v hΓ0
            have hgvb : g j v = b := by
              cases h1 : g j u <;> cases h2 : g j v <;> cases b <;> simp_all
            exact (hPv ⟨hPv1, hgvb⟩).elim
    have hδh_eig : Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_h δ_h =
        (opNormR Γ_f * ∏ j : Fin n, opNormR (Γ_g j)) • δ_h := by
      ext x
      change (Γ_h *ᵥ δ_h.ofLp) x = (opNormR Γ_f * ∏ j : Fin n, opNormR (Γ_g j)) * δ_h.ofLp x
      simp only [mulVec, dotProduct]
      by_cases hPx : ∀ j : Fin n, P_g j (inputBlock x j)
      · have hreindex :
            ∑ y : BitString (∑ j, k j), Γ_h x y * δ_h.ofLp y =
            ∑ yb : ∀ j : Fin n, BitString (k j),
              (Γ_f (evalInnerBlocks g x) (fun j => g j (yb j)) *
                ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j)) *
              (δ_f (fun j => g j (yb j)) * ∏ j, δ_g j (yb j)) :=
          Fintype.sum_equiv (bitStringBlockEquiv k) _ _ fun _ => rfl
        rw [hreindex]
        have hgroup :
            ∑ yb : ∀ j : Fin n, BitString (k j),
              (Γ_f (evalInnerBlocks g x) (fun j => g j (yb j)) *
                ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j)) *
              (δ_f (fun j => g j (yb j)) * ∏ j, δ_g j (yb j)) =
            ∑ z : BitString n,
              Γ_f (evalInnerBlocks g x) z * δ_f z *
                ∏ j : Fin n,
                  ∑ v with P_g j v ∧ g j v = z j,
                    hatAdversary (P_g j) (Γ_g j) (inputBlock x j) v * δ_g j v := by
          have hpart :
              ∑ yb : ∀ j : Fin n, BitString (k j),
                (Γ_f (evalInnerBlocks g x) (fun j => g j (yb j)) *
                  ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j)) *
                (δ_f (fun j => g j (yb j)) * ∏ j, δ_g j (yb j)) =
              ∑ z : BitString n,
                Γ_f (evalInnerBlocks g x) z * δ_f z *
                  ∑ yb : ∀ j : Fin n, BitString (k j),
                    if (fun j => g j (yb j)) = z then
                      ∏ j, (hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j) * δ_g j (yb j))
                    else 0 := by
            have hrw : ∀ yb : ∀ j : Fin n, BitString (k j),
                (Γ_f (evalInnerBlocks g x) (fun j => g j (yb j)) *
                  ∏ j, hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j)) *
                (δ_f (fun j => g j (yb j)) * ∏ j, δ_g j (yb j)) =
                ∑ z : BitString n,
                  Γ_f (evalInnerBlocks g x) z * δ_f z *
                    (if (fun j => g j (yb j)) = z then
                      ∏ j, (hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j) * δ_g j (yb j))
                    else 0) := by
              intro yb
              rw [Finset.sum_eq_single (fun j => g j (yb j))]
              · simp only [↓reduceIte, Finset.prod_mul_distrib]; ring
              · intro z _ hz; simp [Ne.symm hz]
              · simp
            simp_rw [hrw]
            rw [Finset.sum_comm]
            exact sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm
          rw [hpart]
          refine sum_congr rfl fun z _ => ?_
          congr 1
          simp only [sum_filter]
          have hpi2 :
              (∑ yb : ∀ j : Fin n, BitString (k j),
                if (fun j => g j (yb j)) = z then
                  ∏ j, (hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j) * δ_g j (yb j))
                else 0) =
              ∑ yb : ∀ j : Fin n, BitString (k j),
                ∏ j : Fin n,
                  (if P_g j (yb j) ∧ g j (yb j) = z j then
                    hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j) * δ_g j (yb j)
                  else 0) := by
            refine sum_congr rfl fun yb _ => ?_
            by_cases hPyb : ∀ j, P_g j (yb j)
            · by_cases hgz : (fun j => g j (yb j)) = z
              · simp only [hgz, ↓reduceIte]
                exact Finset.prod_congr rfl fun j _ => by simp [hPyb j, congrFun hgz j]
              · simp only [hgz, ↓reduceIte]
                rcases Function.ne_iff.mp hgz with ⟨j₀, hj₀⟩
                exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm
            · push Not at hPyb
              rcases hPyb with ⟨j₀, hj₀⟩
              have h0 : δ_g j₀ (yb j₀) = 0 := hδg_supp j₀ _ hj₀
              have hlhs0 :
                  (if (fun j => g j (yb j)) = z then
                    ∏ j, (hatAdversary (P_g j) (Γ_g j) (inputBlock x j) (yb j) * δ_g j (yb j))
                  else 0) = 0 := by
                split_ifs
                · exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [h0])
                · rfl
              rw [hlhs0]
              exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm
          rw [hpi2]
          let f_eig (j : Fin n) (u : BitString (k j)) : ℝ :=
            if P_g j u ∧ g j u = z j then
              hatAdversary (P_g j) (Γ_g j) (inputBlock x j) u * δ_g j u
            else 0
          have hprod_eig := (Finset.prod_univ_sum
            (t := fun j : Fin n => (Finset.univ : Finset (BitString (k j)))) f_eig).symm
          rw [Fintype.piFinset_univ] at hprod_eig
          exact hprod_eig
        rw [hgroup]
        have hprod_eval : ∀ z : BitString n,
            ∏ j : Fin n,
              (∑ v with P_g j v ∧ g j v = z j,
                hatAdversary (P_g j) (Γ_g j) (inputBlock x j) v * δ_g j v) =
            (∏ j : Fin n, opNormR (Γ_g j)) * ∏ j : Fin n, δ_g j (inputBlock x j) := by
          intro z
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun j _ => hinner_block j (inputBlock x j) (z j) (hPx j)
        simp only [hprod_eval, ← Finset.sum_mul]
        have heig_f := congrFun hδf_eig (evalInnerBlocks g x)
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at heig_f
        rw [heig_f]
        change opNormR Γ_f * δ_f (evalInnerBlocks g x) *
            ((∏ j, opNormR (Γ_g j)) * ∏ j, δ_g j (inputBlock x j)) =
          (opNormR Γ_f * ∏ j, opNormR (Γ_g j)) *
            (δ_f (evalInnerBlocks g x) * ∏ j, δ_g j (inputBlock x j))
        ring
      · push Not at hPx
        rcases hPx with ⟨j₀, hj₀⟩
        have hrhs0 : δ_h.ofLp x = 0 := by
          change δ_f (evalInnerBlocks g x) * ∏ j, δ_g j (inputBlock x j) = 0
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) (hδg_supp j₀ _ hj₀), mul_zero]
        have hlhs0 : ∑ y, Γ_h x y * δ_h.ofLp y = 0 := sum_eq_zero fun y _ => by
          have h0 : Γ_h x y = 0 := by
            by_contra hne0
            exact hj₀ ((isAdversaryMatrix_composedAdversaryMatrix hAdv_f hAdv_g x y hne0).1.1 j₀)
          rw [h0, zero_mul]
        rw [hlhs0, hrhs0, mul_zero]
    have hle := (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_h).le_opNorm δ_h
    have hprod_nonneg : 0 ≤ opNormR Γ_f * ∏ j : Fin n, opNormR (Γ_g j) :=
      mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _ => norm_nonneg _)
    rw [hδh_eig, norm_smul, Real.norm_of_nonneg hprod_nonneg] at hle
    exact le_of_mul_le_mul_right hle hδh_pos

/-- **Coordinate-Disagreement Compatibility**: masking `composedAdversaryMatrix P_g g Γ_f Γ_g`
by `diffMatrix ℓ` where `(blockBitEquiv k).symm ℓ = ⟨p, q⟩` equals `composedAdversaryMatrix`
applied to `Γ_f ∘ diffMatrix p` and `Function.update Γ_g p (Γ_g p ∘ diffMatrix q)`. -/
theorem composedAdversaryMatrix_hadamard_diffMatrix {n : ℕ} {k : Fin n → ℕ}
    {P_g : ∀ j : Fin n, BitString (k j) → Prop}
    {g : ∀ j : Fin n, BitString (k j) → Bool}
    {Γ_f : Matrix (BitString n) (BitString n) ℝ}
    {Γ_g : ∀ j : Fin n, Matrix (BitString (k j)) (BitString (k j)) ℝ}
    (hAdv_g : ∀ j, IsAdversaryMatrix (P_g j) (g j) (Γ_g j))
    (ℓ : Fin (∑ j : Fin n, k j)) :
    (composedAdversaryMatrix P_g g Γ_f Γ_g).hadamard (diffMatrix ℓ) =
      let pq := (blockBitEquiv k).symm ℓ
      composedAdversaryMatrix P_g g
        (Γ_f.hadamard (diffMatrix pq.1))
        (Function.update Γ_g pq.1 ((Γ_g pq.1).hadamard (diffMatrix pq.2))) := by
  classical
  rcases h_pq : (blockBitEquiv k).symm ℓ with ⟨p, q⟩
  have hℓ : blockBitEquiv k ⟨p, q⟩ = ℓ := by
    rw [← h_pq]; exact (blockBitEquiv k).apply_symm_apply ℓ
  ext x y
  dsimp only
  simp only [Matrix.hadamard_apply, composedAdversaryMatrix, Matrix.of_apply, diffMatrix_apply]
  by_cases hbit : inputBlock x p q ≠ inputBlock y p q
  · have hbit' : x ℓ ≠ y ℓ := by simpa [inputBlock, hℓ] using hbit
    have hite1 : (if x ℓ ≠ y ℓ then (1 : ℝ) else 0) = 1 := by split_ifs; rfl
    rw [hite1, mul_one]
    by_cases hout : evalInnerBlocks g x p ≠ evalInnerBlocks g y p
    · have hite2 : (if evalInnerBlocks g x p ≠ evalInnerBlocks g y p then (1 : ℝ) else 0) = 1 := by
        split_ifs; rfl
      rw [hite2, mul_one]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hjp : j = p
      · subst hjp
        have hblk_ne : inputBlock x j ≠ inputBlock y j := fun h => hbit (congrFun h q)
        simp [Function.update_self, hatAdversary, hblk_ne, hbit]
      · simp [Function.update_of_ne hjp]
    · have hite2 : (if evalInnerBlocks g x p ≠ evalInnerBlocks g y p then (1 : ℝ) else 0) = 0 := by
        split_ifs; rfl
      rw [hite2, mul_zero, zero_mul]
      push Not at hout
      have hblk_ne : inputBlock x p ≠ inputBlock y p := fun h => hbit (congrFun h q)
      have hΓ0 : Γ_g p (inputBlock x p) (inputBlock y p) = 0 := by
        by_contra hne0
        exact (hAdv_g p _ _ hne0).2.2 hout
      have hhat0 : hatAdversary (P_g p) (Γ_g p) (inputBlock x p) (inputBlock y p) = 0 := by
        simp [hatAdversary, hΓ0, hblk_ne]
      rw [Finset.prod_eq_zero (Finset.mem_univ p) hhat0, mul_zero]
  · have hbit_neg : ¬ (x ℓ ≠ y ℓ) := by simpa [inputBlock, hℓ] using hbit
    have hite1 : (if x ℓ ≠ y ℓ then (1 : ℝ) else 0) = 0 := by split_ifs; rfl
    rw [hite1, mul_zero]
    push Not at hbit
    by_cases hout : evalInnerBlocks g x p ≠ evalInnerBlocks g y p
    · have hblk_ne : inputBlock x p ≠ inputBlock y p := fun h =>
        hout (by simp [evalInnerBlocks, h])
      have hhat0 :
          hatAdversary (P_g p) ((Γ_g p).hadamard (diffMatrix q))
            (inputBlock x p) (inputBlock y p) = 0 := by
        simp [hatAdversary, hblk_ne, hbit]
      have hprod0 :
          ∏ j : Fin n,
            hatAdversary (P_g j)
              (Function.update Γ_g p ((Γ_g p).hadamard (diffMatrix q)) j)
              (inputBlock x j) (inputBlock y j) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ p) ?_
        simpa [Function.update_self] using hhat0
      rw [hprod0, mul_zero]
    · have hite2 : (if evalInnerBlocks g x p ≠ evalInnerBlocks g y p then (1 : ℝ) else 0) = 0 := by
        split_ifs; rfl
      rw [hite2, mul_zero, zero_mul]

/-- **General Adversary Composition Theorem (`thm:adv`)**: for any partial outer Boolean function
`(P_f, f)` on `n` bits and partial inner Boolean functions `(P_g j, g j)` on `k j` bits satisfying
`generalAdversary (P_g j) (g j) ≥ c` for all `j` (with `0 ≤ c`), the composed partial function
`h = f ∘ (g_0, …, g_{n-1})` satisfies
`generalAdversary (composedPromise P_f P_g g) (composedFunc f g) ≥ generalAdversary P_f f * c`. -/
theorem generalAdversary_composed_ge {n : ℕ} {k : Fin n → ℕ}
    (P_f : BitString n → Prop) (f : BitString n → Bool)
    (P_g : ∀ j : Fin n, BitString (k j) → Prop)
    (g : ∀ j : Fin n, BitString (k j) → Bool)
    {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ j : Fin n, c ≤ generalAdversary (P_g j) (g j)) :
    generalAdversary P_f f * c ≤
      generalAdversary (composedPromise P_f P_g g) (composedFunc f g) := by
  by_cases hc0 : c = 0
  · subst hc0; rw [mul_zero]; exact generalAdversary_nonneg _ _
  have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  rw [← le_div_iff₀ hc_pos]
  refine (generalAdversary_le_iff (div_nonneg (generalAdversary_nonneg _ _) hc_pos.le)).mpr ?_
  intro Γ_f hSym_f hAdv_f
  rw [div_mul_eq_mul_div, le_div_iff₀ hc_pos]
  by_cases hΓf0 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ = 0
  · rw [hΓf0, zero_mul]; exact mul_nonneg (generalAdversary_nonneg _ _) (maxDiffNorm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := min (c / 2) (ε / (2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ + 1)))
  have hδ_pos : 0 < δ := lt_min (half_pos hc_pos) (by positivity)
  have hc'_pos : 0 < c - δ := by
    have : δ ≤ c / 2 := min_le_left _ _
    linarith
  have hex_gj : ∀ j : Fin n,
      ∃ Γ : Matrix (BitString (k j)) (BitString (k j)) ℝ,
        Γ.IsSymm ∧ IsAdversaryMatrix (P_g j) (g j) Γ ∧
          (c - δ) * maxDiffNorm Γ < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
    intro j
    by_contra! hall
    have hle : generalAdversary (P_g j) (g j) ≤ c - δ :=
      (generalAdversary_le_iff hc'_pos.le).mpr hall
    linarith [hg j, hδ_pos]
  choose Γ_g hSym_g hAdv_g hStrict_g using hex_gj
  have hnorm_g_ge : ∀ j : Fin n,
      (c - δ) * maxDiffNorm (Γ_g j) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ :=
    fun j => (hStrict_g j).le
  have hnorm_g_pos : ∀ j : Fin n, 0 < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ :=
    fun j => (mul_nonneg hc'_pos.le (maxDiffNorm_nonneg _)).trans_lt (hStrict_g j)
  let Γ_h := composedAdversaryMatrix P_g g Γ_f Γ_g
  have hSym_h := isSymm_composedAdversaryMatrix P_g g hSym_f hSym_g
  have hAdv_h := isAdversaryMatrix_composedAdversaryMatrix hAdv_f hAdv_g
  have hNorm_h := opNorm_composedAdversaryMatrix hSym_f hAdv_f hSym_g hAdv_g
  have hmd_h : (c - δ) * maxDiffNorm Γ_h ≤
      maxDiffNorm Γ_f * ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ := by
    rw [← le_div_iff₀' hc'_pos, maxDiffNorm_le_iff
      (div_nonneg (mul_nonneg (maxDiffNorm_nonneg _) (prod_nonneg fun _ _ => norm_nonneg _))
        hc'_pos.le)]
    intro ℓ
    rw [le_div_iff₀' hc'_pos]
    dsimp only [Γ_h]
    rw [composedAdversaryMatrix_hadamard_diffMatrix hAdv_g ℓ]
    dsimp only
    rcases h_pq : (blockBitEquiv k).symm ℓ with ⟨p, q⟩
    have hSym_fp : (Γ_f.hadamard (diffMatrix p)).IsSymm := by
      ext u v
      have h1 : Γ_f v u = Γ_f u v := by
        simpa [Matrix.transpose_apply] using congrFun (congrFun hSym_f.eq u) v
      have h2 : diffMatrix p v u = diffMatrix p u v := by
        simpa [Matrix.transpose_apply] using congrFun (congrFun (diffMatrix_transpose p) u) v
      simp only [Matrix.transpose_apply, Matrix.hadamard_apply, h1, h2]
    have hAdv_fp : IsAdversaryMatrix P_f f (Γ_f.hadamard (diffMatrix p)) := by
      intro u v hne
      exact hAdv_f u v (left_ne_zero_of_mul hne)
    let Γ_g' : ∀ j : Fin n, Matrix (BitString (k j)) (BitString (k j)) ℝ := by
      classical
      exact Function.update Γ_g p ((Γ_g p).hadamard (diffMatrix q))
    have hSym_g' : ∀ j, (Γ_g' j).IsSymm := by
      classical
      intro j
      by_cases hjp : j = p
      · subst hjp
        ext u v
        have h1 : Γ_g j v u = Γ_g j u v := by
          simpa [Matrix.transpose_apply] using congrFun (congrFun (hSym_g j).eq u) v
        have h2 : diffMatrix q v u = diffMatrix q u v := by
          simpa [Matrix.transpose_apply] using congrFun (congrFun (diffMatrix_transpose q) u) v
        simp only [Γ_g', Function.update_self, Matrix.transpose_apply, Matrix.hadamard_apply,
          h1, h2]
      · simpa [Γ_g', Function.update_of_ne hjp] using hSym_g j
    have hAdv_g' : ∀ j, IsAdversaryMatrix (P_g j) (g j) (Γ_g' j) := by
      classical
      intro j u v hne
      by_cases hjp : j = p
      · subst hjp
        simp only [Γ_g', Function.update_self, Matrix.hadamard_apply] at hne
        exact hAdv_g j u v (left_ne_zero_of_mul hne)
      · simp only [Γ_g', Function.update_of_ne hjp] at hne
        exact hAdv_g j u v hne
    have hNorm_step := opNorm_composedAdversaryMatrix hSym_fp hAdv_fp hSym_g' hAdv_g'
    dsimp only [Γ_g'] at hNorm_step
    rw [hNorm_step]
    classical
    have hprod_split :
        ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (Function.update Γ_g p ((Γ_g p).hadamard (diffMatrix q)) j)‖ =
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((Γ_g p).hadamard (diffMatrix q))‖ *
            ∏ j ∈ univ.erase p, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ p)]
      refine congrArg₂ _ (by simp [Function.update_self]) (Finset.prod_congr rfl fun j hj => ?_)
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hprod_orig : ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ =
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g p)‖ *
          ∏ j ∈ univ.erase p, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ :=
      (Finset.mul_prod_erase univ _ (mem_univ p)).symm
    rw [hprod_split, hprod_orig]
    have hfp_le :
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_f.hadamard (diffMatrix p))‖ ≤ maxDiffNorm Γ_f :=
      norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ_f p
    have hgp_le : (c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((Γ_g p).hadamard (diffMatrix q))‖ ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g p)‖ := by
      calc (c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((Γ_g p).hadamard (diffMatrix q))‖
          ≤ (c - δ) * maxDiffNorm (Γ_g p) :=
            mul_le_mul_of_nonneg_left
              (norm_toEuclideanCLM_hadamard_le_maxDiffNorm (Γ_g p) q) hc'_pos.le
        _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g p)‖ := hnorm_g_ge p
    calc (c - δ) * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_f.hadamard (diffMatrix p))‖ *
            (‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((Γ_g p).hadamard (diffMatrix q))‖ *
              ∏ j ∈ univ.erase p, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖))
        = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_f.hadamard (diffMatrix p))‖ *
            ((c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((Γ_g p).hadamard (diffMatrix q))‖) *
            ∏ j ∈ univ.erase p, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ := by ring
      _ ≤ maxDiffNorm Γ_f * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g p)‖ *
            ∏ j ∈ univ.erase p, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hfp_le hgp_le (by positivity) (maxDiffNorm_nonneg _))
            (prod_nonneg fun _ _ => norm_nonneg _)
      _ = maxDiffNorm Γ_f * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g p)‖ *
            ∏ j ∈ univ.erase p, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖) := by ring
  have hle_adv_h :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_h‖ ≤
        generalAdversary (composedPromise P_f P_g g) (composedFunc f g) * maxDiffNorm Γ_h := by
    have hdiv := le_generalAdversary hSym_h hAdv_h
    rcases (maxDiffNorm_nonneg Γ_h).eq_or_lt with h0 | hm_pos
    · have hΓh_zero : Γ_h = 0 := eq_zero_of_maxDiffNorm_eq_zero hAdv_h h0.symm
      rw [← h0, mul_zero, hΓh_zero, map_zero, norm_zero]
    · exact (div_le_iff₀ hm_pos).mp hdiv
  have hprod_pos : 0 < ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖ :=
    prod_pos fun j _ => hnorm_g_pos j
  have hkey : (c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ ≤
      generalAdversary (composedPromise P_f P_g g) (composedFunc f g) * maxDiffNorm Γ_f := by
    have h1 : (c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_h‖ ≤
        generalAdversary (composedPromise P_f P_g g) (composedFunc f g) *
          (maxDiffNorm Γ_f * ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖) := by
      calc (c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_h‖
          ≤ (c - δ) * (generalAdversary (composedPromise P_f P_g g) (composedFunc f g) *
              maxDiffNorm Γ_h) := mul_le_mul_of_nonneg_left hle_adv_h hc'_pos.le
        _ = generalAdversary (composedPromise P_f P_g g) (composedFunc f g) *
              ((c - δ) * maxDiffNorm Γ_h) := by ring
        _ ≤ generalAdversary (composedPromise P_f P_g g) (composedFunc f g) *
              (maxDiffNorm Γ_f * ∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖) :=
            mul_le_mul_of_nonneg_left hmd_h (generalAdversary_nonneg _ _)
    dsimp only [Γ_h] at h1
    rw [hNorm_h] at h1
    have h2 : ((c - δ) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖) *
        (∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖) ≤
        (generalAdversary (composedPromise P_f P_g g) (composedFunc f g) * maxDiffNorm Γ_f) *
        (∏ j : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ_g j)‖) := by linarith
    exact le_of_mul_le_mul_right h2 hprod_pos
  have hδ_err : δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ ≤ ε := by
    have hδ_le : δ ≤ ε / (2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ + 1)) := min_le_right _ _
    have hdenom_pos : 0 < 2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ + 1) := by positivity
    calc δ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖
        ≤ (ε / (2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ + 1))) *
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ :=
          mul_le_mul_of_nonneg_right hδ_le (norm_nonneg _)
      _ ≤ (ε / (2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ + 1))) *
            (2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f‖ + 1)) :=
          mul_le_mul_of_nonneg_left
            (by linarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ_f)])
            (by positivity)
      _ = ε := div_mul_cancel₀ ε hdenom_pos.ne'
  linarith

-- Non-vacuity sanity check on 1-bit identity composed with 1-bit identity
example :
    generalAdversary (fun _ : BitString 1 => True) (fun x => x 0) * 0 ≤
      generalAdversary
        (composedPromise (k := fun _ : Fin 1 => 1) (fun _ => True) (fun _ _ => True)
          (fun _ u => u 0))
        (composedFunc (k := fun _ : Fin 1 => 1) (fun x => x 0) (fun _ u => u 0)) :=
  generalAdversary_composed_ge _ _ _ _ le_rfl (fun _ => generalAdversary_nonneg _ _)

end ComposedMatrix

end CslibFrontier.Quantum

end
