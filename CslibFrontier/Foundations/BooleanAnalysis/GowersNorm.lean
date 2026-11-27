/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gowers Uniformity Norms on Finite Abelian Groups

This module defines multiplicative discrete derivatives, cubical Gowers box inner products, and the
Gowers uniformity norms $\|f\|_{U^d(G)}$ for complex-valued functions on finite additive
commutative groups $G$, proving the Gowers–Cauchy–Schwarz and Gowers–Minkowski inequalities
together with inductive derivative, scaling, boundedness, and positivity properties under standard
Lean axioms.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.parityConj`: alternating complex conjugation
  $\mathcal{C}^k(z)$, equal
  to $z$ for even $k$ and $\overline{z}$ for odd $k$.
* `CslibFrontier.Foundations.BooleanAnalysis.mulDeriv`: multiplicative discrete derivative
  $(\Delta_h f)(x) = f(x + h)\overline{f(x)}$.
* `CslibFrontier.Foundations.BooleanAnalysis.iterMulDeriv`: iterated multiplicative derivative
  $\Delta_{h_{d-1}} \cdots \Delta_{h_0} f$.
* `CslibFrontier.Foundations.BooleanAnalysis.cubeWeight`,
  `CslibFrontier.Foundations.BooleanAnalysis.cubeShift`: Hamming weight
  $|\omega|$ and shift $\omega \cdot h = \sum_i \omega_i h_i$ for a cube vertex
  $\omega \in \{0, 1\}^d$.
* `CslibFrontier.Foundations.BooleanAnalysis.gowersInner`: cubical Gowers box inner product
  $\langle (F_\omega)_\omega \rangle_{U^d(G)}$.
* `CslibFrontier.Foundations.BooleanAnalysis.gowersBoxDiag`: diagonal Gowers box average
  $\mathbb{E}_{x, h} \prod_{\omega \in \{0, 1\}^d} \mathcal{C}^{|\omega|} f(x + \omega \cdot h)$.
* `CslibFrontier.Foundations.BooleanAnalysis.gowersNorm`: Gowers uniformity norm
  $\|f\|_{U^d(G)} = (\mathrm{Re}\,\langle f \rangle_{U^d(G)})^{2^{-d}}$.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.gowersBoxDiag_succ_eq_expect_norm_sq`,
  `CslibFrontier.Foundations.BooleanAnalysis.ofReal_gowersBoxDiag_re`,
  `CslibFrontier.Foundations.BooleanAnalysis.gowersBoxDiag_re_nonneg`: reality and nonnegativity of
  `gowersBoxDiag d f` for $d \ge 1$.
* `CslibFrontier.Foundations.BooleanAnalysis.expect_iterMulDeriv_eq_parityConj_gowersBoxDiag`,
  `CslibFrontier.Foundations.BooleanAnalysis.expect_iterMulDeriv_eq_gowersBoxDiag`,
  `CslibFrontier.Foundations.BooleanAnalysis.gowersBoxDiag_succ_eq_expect_mulDeriv`: equivalence
  between cubical and
  iterated-derivative averages and the inductive derivative formula.
* `CslibFrontier.Foundations.BooleanAnalysis.norm_gowersInner_pow_le`: the Gowers–Cauchy–Schwarz
  inequality
  $|\langle (F_\omega) \rangle_{U^d}|^{2^d} \le \prod_\omega \mathrm{Re}\,\langle F_\omega
  \rangle_{U^d}$.
* `CslibFrontier.Foundations.BooleanAnalysis.gowersNorm_add_le`,
  `CslibFrontier.Foundations.BooleanAnalysis.gowersNorm_sub_le`,
  `CslibFrontier.Foundations.BooleanAnalysis.gowersNorm_le_of_norm_le`,
  `CslibFrontier.Foundations.BooleanAnalysis.gowersNorm_le_one_of_norm_le_one`,
  `CslibFrontier.Foundations.BooleanAnalysis.gowersNorm_eq_zero_iff`: triangle inequality,
  $L^\infty$ domination, and
  definiteness of $\|f\|_{U^d(G)}$ for $d \ge 2$.
-/

public section

open Finset
open scoped BigOperators

namespace CslibFrontier.Foundations.BooleanAnalysis

/-! ### Alternating Complex Conjugation -/

section ParityConj

/-- Alternating complex conjugation $\mathcal{C}^k(z)$, equal to $z$ if $k$ is even and
$\overline{z}$ if $k$ is odd. -/
def parityConj (k : ℕ) (z : ℂ) : ℂ :=
  if k % 2 = 0 then z else starRingEnd ℂ z

/-- At exponent `0`, `parityConj` is the identity. -/
@[simp]
theorem parityConj_zero (z : ℂ) : parityConj 0 z = z := by
  rfl

/-- At exponent `1`, `parityConj` is complex conjugation. -/
@[simp]
theorem parityConj_one (z : ℂ) : parityConj 1 z = starRingEnd ℂ z := by
  rfl

/-- For even `k`, `parityConj k z = z`. -/
theorem parityConj_of_even {k : ℕ} (hk : Even k) (z : ℂ) : parityConj k z = z := by
  rcases hk with ⟨m, rfl⟩
  have hmod : (m + m) % 2 = 0 := by omega
  simp [parityConj, hmod]

/-- For odd `k`, `parityConj k z = conj z`. -/
theorem parityConj_of_odd {k : ℕ} (hk : Odd k) (z : ℂ) : parityConj k z = starRingEnd ℂ z := by
  rcases hk with ⟨m, rfl⟩
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  simp [parityConj, hmod]

/-- Shifting the exponent by `1` composes `parityConj` with complex conjugation. -/
theorem parityConj_succ (k : ℕ) (z : ℂ) :
    parityConj (k + 1) z = starRingEnd ℂ (parityConj k z) := by
  by_cases h : k % 2 = 0
  · have h1 : (k + 1) % 2 = 1 := by omega
    simp [parityConj, h, h1]
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [parityConj, h, h1]

/-- `parityConj` preserves addition. -/
theorem parityConj_add (k : ℕ) (z w : ℂ) :
    parityConj k (z + w) = parityConj k z + parityConj k w := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h]

/-- `parityConj` preserves multiplication. -/
theorem parityConj_mul (k : ℕ) (z w : ℂ) :
    parityConj k (z * w) = parityConj k z * parityConj k w := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h]

/-- `parityConj` distributes over finite sums. -/
theorem parityConj_sum {ι : Type*} (k : ℕ) (s : Finset ι) (g : ι → ℂ) :
    parityConj k (∑ i ∈ s, g i) = ∑ i ∈ s, parityConj k (g i) := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h, map_sum]

/-- `parityConj` distributes over finite products. -/
theorem parityConj_prod {ι : Type*} (k : ℕ) (s : Finset ι) (g : ι → ℂ) :
    parityConj k (∏ i ∈ s, g i) = ∏ i ∈ s, parityConj k (g i) := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h, map_prod]

/-- `parityConj` distributes over finite expectations. -/
theorem parityConj_expect {ι : Type*} (k : ℕ) (s : Finset ι) (g : ι → ℂ) :
    parityConj k (𝔼 i ∈ s, g i) = 𝔼 i ∈ s, parityConj k (g i) := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h, map_expect]

/-- `parityConj` preserves complex modulus. -/
@[simp]
theorem norm_parityConj (k : ℕ) (z : ℂ) : ‖parityConj k z‖ = ‖z‖ := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h]

/-- `parityConj` fixes real numbers embedded in `ℂ`. -/
@[simp]
theorem parityConj_ofReal (k : ℕ) (r : ℝ) : parityConj k (r : ℂ) = (r : ℂ) := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h]

private lemma parityConj_conj (k : ℕ) (z : ℂ) :
    parityConj k (starRingEnd ℂ z) = starRingEnd ℂ (parityConj k z) := by
  by_cases h : k % 2 = 0 <;> simp [parityConj, h]

private lemma parityConj_one_val (k : ℕ) : parityConj k 1 = 1 := by
  simpa using parityConj_ofReal k 1

end ParityConj

/-! ### Multiplicative Discrete Derivatives and Discrete Cubes -/

section DerivativesAndCubes

variable {G : Type*} [AddCommGroup G]

/-- Multiplicative discrete derivative $(\Delta_h f)(x) = f(x + h)\overline{f(x)}$ of a function
$f : G \to \mathbb{C}$ in direction $h \in G$. -/
def mulDeriv (h : G) (f : G → ℂ) (x : G) : ℂ :=
  f (x + h) * starRingEnd ℂ (f x)

/-- Pointwise evaluation formula for `mulDeriv`. -/
theorem mulDeriv_apply (h : G) (f : G → ℂ) (x : G) :
    mulDeriv h f x = f (x + h) * starRingEnd ℂ (f x) := by
  rfl

/-- At shift `0`, $(\Delta_0 f)(x) = |f(x)|^2$. -/
@[simp]
theorem mulDeriv_zero_step (f : G → ℂ) (x : G) :
    mulDeriv 0 f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
  simp [mulDeriv, Complex.mul_conj']

/-- Complex modulus of a multiplicative discrete derivative. -/
theorem norm_mulDeriv (h : G) (f : G → ℂ) (x : G) :
    ‖mulDeriv h f x‖ = ‖f (x + h)‖ * ‖f x‖ := by
  simp [mulDeriv]

/-- Scaling law $\Delta_h (c \cdot f) = |c|^2 \cdot \Delta_h f$. -/
theorem mulDeriv_smul (h : G) (c : ℂ) (f : G → ℂ) (x : G) :
    mulDeriv h (c • f) x = ((‖c‖ ^ 2 : ℝ) : ℂ) * mulDeriv h f x := by
  simp only [mulDeriv, Pi.smul_apply, smul_eq_mul, map_mul, Complex.ofReal_pow,
    ← Complex.mul_conj']
  ring

/-- Multiplicative discrete derivatives in any two directions commute. -/
theorem mulDeriv_comm (h₁ h₂ : G) (f : G → ℂ) :
    mulDeriv h₁ (mulDeriv h₂ f) = mulDeriv h₂ (mulDeriv h₁ f) := by
  ext x
  simp only [mulDeriv, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hadd : x + h₁ + h₂ = x + h₂ + h₁ := by abel
  rw [hadd]
  ring

/-- Iterated multiplicative discrete derivative
$\Delta_{h_{d-1}} \cdots \Delta_{h_0} f : G \to \mathbb{C}$. -/
def iterMulDeriv : {d : ℕ} → (Fin d → G) → (G → ℂ) → G → ℂ
  | 0, _, f => f
  | d + 1, h, f => mulDeriv (h (Fin.last d)) (iterMulDeriv (Fin.init h) f)

/-- Order-`0` iterated derivative is the identity. -/
@[simp]
theorem iterMulDeriv_zero (h : Fin 0 → G) (f : G → ℂ) : iterMulDeriv h f = f := by
  rfl

/-- Order-`(d + 1)` iterated derivative peels off the last direction `h (Fin.last d)`. -/
@[simp]
theorem iterMulDeriv_succ {d : ℕ} (h : Fin (d + 1) → G) (f : G → ℂ) :
    iterMulDeriv h f = mulDeriv (h (Fin.last d)) (iterMulDeriv (Fin.init h) f) := by
  rfl

/-- Hamming weight $|\omega| = |\{i \in \mathrm{Fin}\,d : \omega_i = \mathrm{true}\}|$ of a cube
vertex $\omega \in \{0, 1\}^d$. -/
def cubeWeight {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin d ↦ ω i = true).card

/-- The unique vertex of the `0`-dimensional cube has weight `0`. -/
@[simp]
theorem cubeWeight_zero (ω : Fin 0 → Bool) : cubeWeight ω = 0 := by
  simp [cubeWeight]

/-- Cube displacement $\omega \cdot h = \sum_{i < d} \omega_i h_i \in G$. -/
def cubeShift {d : ℕ} (h : Fin d → G) (ω : Fin d → Bool) : G :=
  ∑ i : Fin d, if ω i then h i else 0

/-- The unique vertex of the `0`-dimensional cube gives zero shift. -/
@[simp]
theorem cubeShift_zero (h : Fin 0 → G) (ω : Fin 0 → Bool) : cubeShift h ω = 0 := by
  simp [cubeShift]

private def cubeSnocEquiv (d : ℕ) : (Fin d → Bool) × Bool ≃ (Fin (d + 1) → Bool) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (Fin.init ω, ω (Fin.last d))
  left_inv p := by
    ext i
    · simp [Fin.init_snoc]
    · simp [Fin.snoc_last]
  right_inv ω := Fin.snoc_init_self ω

private def cubeConsEquiv (d : ℕ) : Bool × (Fin d → Bool) ≃ (Fin (d + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun ω := (ω 0, Fin.tail ω)
  left_inv p := by
    ext i <;> simp
  right_inv ω := Fin.cons_self_tail ω

private lemma cubeWeight_snoc {d : ℕ} (ω : Fin d → Bool) (b : Bool) :
    cubeWeight (Fin.snoc ω b) = cubeWeight ω + if b then 1 else 0 := by
  simp only [cubeWeight]
  have hsum :
      (∑ i : Fin (d + 1), if Fin.snoc (α := fun _ ↦ Bool) ω b i = true then (1 : ℕ) else 0) =
        (∑ i : Fin d, if ω i = true then (1 : ℕ) else 0) + if b = true then 1 else 0 := by
    rw [Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  simpa [Finset.sum_boole] using hsum

private lemma cubeShift_snoc {d : ℕ} (h : Fin (d + 1) → G) (ω : Fin d → Bool) (b : Bool) :
    cubeShift h (Fin.snoc ω b) =
      cubeShift (Fin.init h) ω + if b then h (Fin.last d) else 0 := by
  simp only [cubeShift, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init]

private lemma cubeWeight_cons {d : ℕ} (b : Bool) (ω : Fin d → Bool) :
    cubeWeight (Fin.cons b ω) = (if b then 1 else 0) + cubeWeight ω := by
  simp only [cubeWeight]
  have hsum :
      (∑ i : Fin (d + 1), if Fin.cons (α := fun _ ↦ Bool) b ω i = true then (1 : ℕ) else 0) =
        (if b = true then 1 else 0) + (∑ i : Fin d, if ω i = true then (1 : ℕ) else 0) := by
    rw [Fin.sum_univ_succ]
    simp
  simpa [Finset.sum_boole] using hsum

private lemma cubeShift_cons {d : ℕ} (h : Fin (d + 1) → G) (b : Bool) (ω : Fin d → Bool) :
    cubeShift h (Fin.cons b ω) =
      (if b then h 0 else 0) + cubeShift (Fin.tail h) ω := by
  simp only [cubeShift, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

private lemma prod_cube_snoc {M : Type*} [CommMonoid M] {d : ℕ}
    (Φ : (Fin (d + 1) → Bool) → M) :
    (∏ ω : Fin (d + 1) → Bool, Φ ω) =
      (∏ ω : Fin d → Bool, Φ (Fin.snoc ω false)) *
        (∏ ω : Fin d → Bool, Φ (Fin.snoc ω true)) := by
  rw [← Fintype.prod_equiv (cubeSnocEquiv d) (fun p ↦ Φ (Fin.snoc p.1 p.2)) Φ (fun _ ↦ rfl),
    Fintype.prod_prod_type_right]
  have hbool : ∀ ψ : Bool → M, (∏ b : Bool, ψ b) = ψ false * ψ true := fun ψ ↦ by
    simp [Fintype.univ_bool, mul_comm]
  rw [hbool]

private lemma prod_cube_cons {M : Type*} [CommMonoid M] {d : ℕ}
    (Φ : (Fin (d + 1) → Bool) → M) :
    (∏ ω : Fin (d + 1) → Bool, Φ ω) =
      (∏ ω : Fin d → Bool, Φ (Fin.cons false ω)) *
        (∏ ω : Fin d → Bool, Φ (Fin.cons true ω)) := by
  rw [← Fintype.prod_equiv (cubeConsEquiv d) (fun p ↦ Φ (Fin.cons p.1 p.2)) Φ (fun _ ↦ rfl),
    Fintype.prod_prod_type]
  have hbool : ∀ ψ : Bool → M, (∏ b : Bool, ψ b) = ψ false * ψ true := fun ψ ↦ by
    simp [Fintype.univ_bool, mul_comm]
  rw [hbool]

/-- Pointwise cubical expansion of `iterMulDeriv`:
$(\Delta_{h_{d-1}} \cdots \Delta_{h_0} f)(x) =
\mathcal{C}^d \bigl(\prod_{\omega \in \{0, 1\}^d} \mathcal{C}^{|\omega|}
f(x + \omega \cdot h)\bigr)$. -/
theorem iterMulDeriv_eq_parityConj_prod_cube {d : ℕ} (h : Fin d → G) (f : G → ℂ) (x : G) :
    iterMulDeriv h f x =
      parityConj d (∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))) := by
  induction d generalizing x with
  | zero =>
    simp
  | succ d ih =>
    rw [iterMulDeriv_succ, mulDeriv_apply, ih, ih, prod_cube_snoc]
    simp only [cubeWeight_snoc, cubeShift_snoc, Bool.false_eq_true, ↓reduceIte, add_zero]
    simp_rw [parityConj_succ (cubeWeight _), ← map_prod]
    rw [parityConj_succ d, parityConj_mul, map_mul, parityConj_conj,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    have hshift : ∀ ω : Fin d → Bool,
        x + (cubeShift (Fin.init h) ω + h (Fin.last d)) =
          x + h (Fin.last d) + cubeShift (Fin.init h) ω := fun ω ↦ by abel
    simp_rw [hshift]
    ring

end DerivativesAndCubes

/-! ### Gowers Box Inner Product, Diagonal Box Average, and Gowers–Cauchy–Schwarz -/

section GowersBox

variable {G : Type*} [AddCommGroup G] [Fintype G]

private def piSnocEquiv (d : ℕ) : (Fin d → G) × G ≃ (Fin (d + 1) → G) where
  toFun p := Fin.snoc p.1 p.2
  invFun h := (Fin.init h, h (Fin.last d))
  left_inv p := by
    ext i
    · simp [Fin.init_snoc]
    · simp [Fin.snoc_last]
  right_inv h := Fin.snoc_init_self h

private def piConsEquiv (d : ℕ) : G × (Fin d → G) ≃ (Fin (d + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun h := (h 0, Fin.tail h)
  left_inv p := by
    ext i <;> simp
  right_inv h := Fin.cons_self_tail h

private lemma expect_add_pair (Φ : G → G → ℂ) :
    (𝔼 x : G, 𝔼 t : G, Φ x (x + t)) = 𝔼 x : G, 𝔼 y : G, Φ x y :=
  Finset.expect_congr rfl fun x _ ↦
    Fintype.expect_equiv (Equiv.addLeft x) _ (fun y ↦ Φ x y) fun _ ↦ rfl

private lemma expect_ofReal_re {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    (𝔼 i : ι, (g i : ℂ)).re = 𝔼 i : ι, g i := by
  simp only [Fintype.expect_eq_sum_div_card]
  have hcast :
      (∑ i : ι, (g i : ℂ)) / (Fintype.card ι : ℂ) =
        (((∑ i : ι, g i) / (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]

private lemma re_expect {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (𝔼 i : ι, g i).re = 𝔼 i : ι, (g i).re := by
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [show ((Fintype.card ι : ℂ)⁻¹) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.re_sum]

private lemma expect_prod_type_complex {α β : Type*} [Fintype α] [Fintype β] (g : α × β → ℂ) :
    (𝔼 p : α × β, g p) = 𝔼 a : α, 𝔼 b : β, g (a, b) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_prod, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div, Nat.cast_mul, mul_comm (Fintype.card α : ℂ)]

/-- Cubical Gowers box inner product
$\langle (F_\omega)_\omega \rangle_{U^d(G)} =
\mathbb{E}_{x \in G}\,\mathbb{E}_{h \in G^d}
\prod_{\omega \in \{0, 1\}^d} \mathcal{C}^{|\omega|} F_\omega(x + \omega \cdot h)$. -/
noncomputable def gowersInner {d : ℕ} (F : (Fin d → Bool) → G → ℂ) : ℂ :=
  𝔼 x : G, 𝔼 h : Fin d → G,
    ∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (F ω (x + cubeShift h ω))

/-- Diagonal Gowers box average
$\langle f \rangle_{U^d(G)} = \mathbb{E}_{x \in G}\,\mathbb{E}_{h \in G^d}
\prod_{\omega \in \{0, 1\}^d} \mathcal{C}^{|\omega|} f(x + \omega \cdot h)$. -/
noncomputable def gowersBoxDiag (d : ℕ) (f : G → ℂ) : ℂ :=
  gowersInner (d := d) fun _ ↦ f

/-- Order-`0` diagonal Gowers box average is $\mathbb{E}_{x \in G} f(x)$. -/
@[simp]
theorem gowersBoxDiag_zero (f : G → ℂ) : gowersBoxDiag 0 f = 𝔼 x : G, f x := by
  simp [gowersBoxDiag, gowersInner]

/-- Splitting the last cube coordinate expresses `gowersInner` as a `G^d`-average of products of
two independent `G`-averages. -/
theorem gowersInner_succ_eq_expect_mul {d : ℕ} (F : (Fin (d + 1) → Bool) → G → ℂ) :
    gowersInner F =
      𝔼 h : Fin d → G,
        (𝔼 x : G, ∏ ω : Fin d → Bool,
            parityConj (cubeWeight ω) (F (Fin.snoc ω false) (x + cubeShift h ω))) *
          starRingEnd ℂ
            (𝔼 y : G, ∏ ω : Fin d → Bool,
              parityConj (cubeWeight ω) (F (Fin.snoc ω true) (y + cubeShift h ω))) := by
  simp only [gowersInner]
  rw [Finset.expect_comm, ← Fintype.expect_equiv (piSnocEquiv d) _ _ (fun _ ↦ rfl),
    expect_prod_type_complex]
  refine Finset.expect_congr rfl fun h _ ↦ ?_
  rw [Finset.expect_comm]
  have hterm : ∀ x t : G,
      (∏ ω : Fin (d + 1) → Bool,
          parityConj (cubeWeight ω) (F ω (x + cubeShift (Fin.snoc h t) ω))) =
        (∏ ω : Fin d → Bool,
            parityConj (cubeWeight ω) (F (Fin.snoc ω false) (x + cubeShift h ω))) *
          starRingEnd ℂ
            (∏ ω : Fin d → Bool,
              parityConj (cubeWeight ω) (F (Fin.snoc ω true) ((x + t) + cubeShift h ω))) := by
    intro x t
    rw [prod_cube_snoc, map_prod]
    have hinit : Fin.init (Fin.snoc (α := fun _ ↦ G) h t) = h := by
      ext i; simp [Fin.init, Fin.snoc_castSucc]
    simp only [cubeWeight_snoc, cubeShift_snoc, hinit, Fin.snoc_last, Bool.false_eq_true,
      ↓reduceIte, add_zero, parityConj_succ]
    congr 2
    ext ω
    have hadd : x + (cubeShift h ω + t) = x + t + cubeShift h ω := by abel
    rw [hadd]
  change (𝔼 x : G, 𝔼 t : G,
      ∏ ω : Fin (d + 1) → Bool,
        parityConj (cubeWeight ω) (F ω (x + cubeShift (Fin.snoc h t) ω))) = _
  simp_rw [hterm]
  rw [expect_add_pair (fun x y ↦
    (∏ ω : Fin d → Bool,
        parityConj (cubeWeight ω) (F (Fin.snoc ω false) (x + cubeShift h ω))) *
      starRingEnd ℂ
        (∏ ω : Fin d → Bool,
          parityConj (cubeWeight ω) (F (Fin.snoc ω true) (y + cubeShift h ω))))]
  simp_rw [← Finset.mul_expect, ← map_expect]
  rw [← Finset.expect_mul]

/-- Nonnegative squared-modulus representation of `gowersBoxDiag (d + 1) f`. -/
theorem gowersBoxDiag_succ_eq_expect_norm_sq (d : ℕ) (f : G → ℂ) :
    gowersBoxDiag (d + 1) f =
      𝔼 h : Fin d → G,
        ((‖𝔼 x : G, ∏ ω : Fin d → Bool,
            parityConj (cubeWeight ω) (f (x + cubeShift h ω))‖ ^ 2 : ℝ) : ℂ) := by
  rw [gowersBoxDiag, gowersInner_succ_eq_expect_mul]
  exact Finset.expect_congr rfl fun _ _ ↦ by rw [Complex.mul_conj', Complex.ofReal_pow]

/-- Order-`1` diagonal Gowers box average is $|\mathbb{E}_{x \in G} f(x)|^2$. -/
theorem gowersBoxDiag_one (f : G → ℂ) :
    gowersBoxDiag 1 f = ((‖𝔼 x : G, f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [gowersBoxDiag_succ_eq_expect_norm_sq 0 f]
  simp

/-- Order-`2` diagonal Gowers box average is
$\mathbb{E}_{h \in G} |\mathbb{E}_{x \in G} (\Delta_h f)(x)|^2$. -/
theorem gowersBoxDiag_two (f : G → ℂ) :
    gowersBoxDiag 2 f = 𝔼 h : G, ((‖𝔼 x : G, mulDeriv h f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [gowersBoxDiag_succ_eq_expect_norm_sq 1 f]
  refine Fintype.expect_equiv (Equiv.funUnique (Fin 1) G) _ _ fun h ↦ ?_
  congr 2
  have hprod : ∀ x : G,
      (∏ ω : Fin 1 → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))) =
        starRingEnd ℂ (mulDeriv (h 0) f x) := fun x ↦ by
    rw [prod_cube_snoc]
    simp [cubeWeight_snoc, cubeShift_snoc, mulDeriv, mul_comm]
  simp_rw [hprod, ← map_expect, RCLike.norm_conj]
  rfl

/-- Real part of `gowersBoxDiag (d + 1) f` as a nonnegative real expectation. -/
theorem gowersBoxDiag_succ_re (d : ℕ) (f : G → ℂ) :
    (gowersBoxDiag (d + 1) f).re =
      𝔼 h : Fin d → G,
        ‖𝔼 x : G, ∏ ω : Fin d → Bool,
          parityConj (cubeWeight ω) (f (x + cubeShift h ω))‖ ^ 2 := by
  rw [gowersBoxDiag_succ_eq_expect_norm_sq, expect_ofReal_re]

/-- For every `d ≥ 1`, `gowersBoxDiag d f` is a real number embedded in `ℂ`. -/
theorem ofReal_gowersBoxDiag_re {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    ((gowersBoxDiag d f).re : ℂ) = gowersBoxDiag d f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
  rw [gowersBoxDiag_succ_re, gowersBoxDiag_succ_eq_expect_norm_sq,
    Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  push_cast
  rfl

/-- For every `d ≥ 1`, `(gowersBoxDiag d f).re ≥ 0`. -/
theorem gowersBoxDiag_re_nonneg {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    0 ≤ (gowersBoxDiag d f).re := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
  rw [gowersBoxDiag_succ_re]
  exact Finset.expect_nonneg fun _ _ ↦ sq_nonneg _

/-- Expectation of the iterated multiplicative derivative equals
`parityConj d (gowersBoxDiag d f)`. -/
theorem expect_iterMulDeriv_eq_parityConj_gowersBoxDiag (d : ℕ) (f : G → ℂ) :
    (𝔼 x : G, 𝔼 h : Fin d → G, iterMulDeriv h f x) = parityConj d (gowersBoxDiag d f) := by
  simp only [gowersBoxDiag, gowersInner, parityConj_expect]
  refine Finset.expect_congr rfl fun x _ ↦
    Finset.expect_congr rfl fun h _ ↦ iterMulDeriv_eq_parityConj_prod_cube h f x

/-- For every `d ≥ 1`, the expectation of `iterMulDeriv h f x` equals `gowersBoxDiag d f`. -/
theorem expect_iterMulDeriv_eq_gowersBoxDiag {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    (𝔼 x : G, 𝔼 h : Fin d → G, iterMulDeriv h f x) = gowersBoxDiag d f := by
  rw [expect_iterMulDeriv_eq_parityConj_gowersBoxDiag, ← ofReal_gowersBoxDiag_re hd,
    parityConj_ofReal]

/-- Splitting the first direction yields the inductive derivative identity
$\langle F \rangle_{U^{d+1}} = \mathbb{E}_{t \in G}
\overline{\langle (\Delta_t F_\omega)_\omega \rangle_{U^d}}$ when $F$ does not depend on the
first cube coordinate. -/
private lemma expect_norm_sq_cube_eq_expect_gowersInner {d : ℕ}
    (Φ : (Fin d → Bool) → G → ℂ) :
    (𝔼 h : Fin d → G,
        ((‖𝔼 x : G, ∏ ω : Fin d → Bool,
          parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))‖ ^ 2 : ℝ) : ℂ)) =
      𝔼 t : G, starRingEnd ℂ (gowersInner fun ω ↦ mulDeriv t (Φ ω)) := by
  have hnorm : ∀ h : Fin d → G,
      ((‖𝔼 x : G, ∏ ω : Fin d → Bool,
          parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))‖ ^ 2 : ℝ) : ℂ) =
        𝔼 t : G, starRingEnd ℂ
          (𝔼 x : G, ∏ ω : Fin d → Bool,
            parityConj (cubeWeight ω) (mulDeriv t (Φ ω) (x + cubeShift h ω))) := by
    intro h
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_expect, Finset.expect_mul]
    have hmul :
        (𝔼 x : G, (∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))) *
            𝔼 y : G, starRingEnd ℂ
              (∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (Φ ω (y + cubeShift h ω)))) =
          𝔼 x : G, 𝔼 t : G,
            (∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))) *
              starRingEnd ℂ
                (∏ ω : Fin d → Bool,
                  parityConj (cubeWeight ω) (Φ ω ((x + t) + cubeShift h ω))) := by
      simp_rw [Finset.mul_expect]
      exact (expect_add_pair _).symm
    rw [hmul, Finset.expect_comm]
    refine Finset.expect_congr rfl fun t _ ↦ ?_
    rw [map_expect]
    refine Finset.expect_congr rfl fun x _ ↦ ?_
    rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ω _ ↦ ?_
    have hadd : x + t + cubeShift h ω = x + cubeShift h ω + t := by abel
    rw [hadd, mulDeriv_apply, parityConj_mul, map_mul, parityConj_conj,
      RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
  simp_rw [hnorm]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun t _ ↦ ?_
  rw [← map_expect]
  congr 1
  simp only [gowersInner]
  exact Finset.expect_comm _ _ _

/-- Inductive derivative formula
$\langle f \rangle_{U^{d+1}} = \mathbb{E}_{h \in G} \langle \Delta_h f \rangle_{U^d}$ for
$d \ge 1$. -/
theorem gowersBoxDiag_succ_eq_expect_mulDeriv {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    gowersBoxDiag (d + 1) f = 𝔼 h : G, gowersBoxDiag d (mulDeriv h f) := by
  rw [gowersBoxDiag_succ_eq_expect_norm_sq,
    expect_norm_sq_cube_eq_expect_gowersInner (fun _ : Fin d → Bool ↦ f)]
  refine Finset.expect_congr rfl fun t _ ↦ ?_
  change starRingEnd ℂ (gowersBoxDiag d (mulDeriv t f)) = gowersBoxDiag d (mulDeriv t f)
  rw [← ofReal_gowersBoxDiag_re hd, Complex.conj_ofReal]

private lemma expect_norm_mul_sq_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖𝔼 i : ι, u i * v i‖ ^ 2 ≤ (𝔼 i : ι, ‖u i‖ ^ 2) * (𝔼 i : ι, ‖v i‖ ^ 2) := by
  have htri : ‖𝔼 i : ι, u i * v i‖ ≤ 𝔼 i : ι, ‖u i‖ * ‖v i‖ := by
    simp only [Fintype.expect_eq_sum_div_card, norm_div, Complex.norm_natCast]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _))
  refine (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans ?_
  simp only [Fintype.expect_eq_sum_div_card]
  by_cases hc : Fintype.card ι = 0
  · simp [hc]
  · have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) ^ 2 := by positivity
    rw [div_pow, div_mul_div_comm, ← sq, div_le_div_iff_of_pos_right hpos]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ ‖u i‖) (fun i ↦ ‖v i‖)

private lemma expect_geom_mean_pow_le {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ] (g : κ → ι → ℝ) (hg : ∀ k i, 0 ≤ g k i) :
    (𝔼 i : ι, ∏ k : κ, (g k i) ^ ((Fintype.card κ : ℝ)⁻¹)) ^ Fintype.card κ ≤
      ∏ k : κ, 𝔼 i : ι, g k i := by
  set m := Fintype.card κ
  have hm_pos : 0 < m := Fintype.card_pos
  have hm_rpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hexp_nn : ∀ k, 0 ≤ 𝔼 i : ι, g k i := fun k ↦ Finset.expect_nonneg fun i _ ↦ hg k i
  by_cases hzero : ∃ k : κ, (𝔼 i : ι, g k i) = 0
  · obtain ⟨k₀, hk₀⟩ := hzero
    have hgk₀ : ∀ i : ι, g k₀ i = 0 := by
      rw [Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hk₀
      have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hsum := hk₀.resolve_right hcard
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hg k₀ j).mp hsum i (Finset.mem_univ i)
    have hlhs : (𝔼 i : ι, ∏ k : κ, (g k i) ^ ((m : ℝ)⁻¹)) = 0 := by
      refine Finset.expect_eq_zero fun i _ ↦ Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
      rw [hgk₀ i, Real.zero_rpow (inv_ne_zero hm_rpos.ne')]
    rw [hlhs, zero_pow hm_pos.ne']
    exact Finset.prod_nonneg fun k _ ↦ hexp_nn k
  · push Not at hzero
    have hexp_pos : ∀ k : κ, 0 < 𝔼 i : ι, g k i := fun k ↦
      lt_of_le_of_ne (hexp_nn k) (Ne.symm (hzero k))
    let u (k : κ) (i : ι) : ℝ := g k i / 𝔼 j : ι, g k j
    have hu_nn : ∀ k i, 0 ≤ u k i := fun k i ↦ div_nonneg (hg k i) (hexp_pos k).le
    have hu_exp : ∀ k : κ, (𝔼 i : ι, u k i) = 1 := fun k ↦ by
      simp only [u, div_eq_mul_inv, ← Finset.expect_mul, mul_inv_cancel₀ (hexp_pos k).ne']
    have hpt : ∀ i : ι, ∏ k : κ, (u k i) ^ ((m : ℝ)⁻¹) ≤ ∑ k : κ, (m : ℝ)⁻¹ * u k i := by
      intro i
      refine Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ ↦ (m : ℝ)⁻¹)
        (fun k ↦ u k i) (fun _ _ ↦ by positivity) ?_ (fun k _ ↦ hu_nn k i)
      simp [m]
    have havg_le_one : (𝔼 i : ι, ∏ k : κ, (u k i) ^ ((m : ℝ)⁻¹)) ≤ 1 := by
      calc 𝔼 i : ι, ∏ k : κ, (u k i) ^ ((m : ℝ)⁻¹)
          ≤ 𝔼 i : ι, ∑ k : κ, (m : ℝ)⁻¹ * u k i := Finset.expect_le_expect fun i _ ↦ hpt i
        _ = ∑ k : κ, (m : ℝ)⁻¹ * 𝔼 i : ι, u k i := by
            rw [Finset.expect_sum_comm]
            exact Finset.sum_congr rfl fun k _ ↦ (Finset.mul_expect _ _ _).symm
        _ = 1 := by simp [hu_exp, m]
    set P : ℝ := ∏ k : κ, (𝔼 j : ι, g k j) ^ ((m : ℝ)⁻¹)
    have hP_nn : 0 ≤ P := Finset.prod_nonneg fun k _ ↦ Real.rpow_nonneg (hexp_nn k) _
    have hP_pow : P ^ m = ∏ k : κ, 𝔼 j : ι, g k j := by
      simp only [P, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hexp_nn k), inv_mul_cancel₀ hm_rpos.ne',
        Real.rpow_one]
    have hscale : (𝔼 i : ι, ∏ k : κ, (g k i) ^ ((m : ℝ)⁻¹)) =
        P * 𝔼 i : ι, ∏ k : κ, (u k i) ^ ((m : ℝ)⁻¹) := by
      rw [Finset.mul_expect]
      refine Finset.expect_congr rfl fun i _ ↦ ?_
      simp only [P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← Real.mul_rpow (hexp_nn k) (hu_nn k i)]
      simp only [u, mul_div_cancel₀ _ (hexp_pos k).ne']
    have hle_P : (𝔼 i : ι, ∏ k : κ, (g k i) ^ ((m : ℝ)⁻¹)) ≤ P := by
      rw [hscale]
      exact (mul_le_mul_of_nonneg_left havg_le_one hP_nn).trans (by rw [mul_one])
    have hlhs_nn : 0 ≤ 𝔼 i : ι, ∏ k : κ, (g k i) ^ ((m : ℝ)⁻¹) :=
      Finset.expect_nonneg fun i _ ↦ Finset.prod_nonneg fun k _ ↦ Real.rpow_nonneg (hg k i) _
    exact (pow_le_pow_left₀ hlhs_nn hle_P m).trans (le_of_eq hP_pow)

/-- **Gowers–Cauchy–Schwarz inequality**: for every $d \ge 1$ and every cube-indexed family
$F : (\mathrm{Fin}\,d \to \mathrm{Bool}) \to G \to \mathbb{C}$,
$|\langle F \rangle_{U^d(G)}|^{2^d} \le \prod_{\omega \in \{0, 1\}^d}
\mathrm{Re}\,\langle F_\omega \rangle_{U^d(G)}$. -/
theorem norm_gowersInner_pow_le {d : ℕ} (hd : 1 ≤ d) (F : (Fin d → Bool) → G → ℂ) :
    ‖gowersInner F‖ ^ (2 ^ d) ≤
      ∏ ω : Fin d → Bool, (gowersBoxDiag d (F ω)).re := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases hd0 : d = 0
    · subst hd0
      rw [gowersInner_succ_eq_expect_mul, prod_cube_snoc]
      simp [gowersBoxDiag_one, mul_pow, -Complex.ofReal_pow]
    · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
      let A (h : Fin d → G) : ℂ :=
        𝔼 x : G, ∏ ω : Fin d → Bool,
          parityConj (cubeWeight ω) (F (Fin.snoc ω false) (x + cubeShift h ω))
      let B (h : Fin d → G) : ℂ :=
        starRingEnd ℂ (𝔼 y : G, ∏ ω : Fin d → Bool,
          parityConj (cubeWeight ω) (F (Fin.snoc ω true) (y + cubeShift h ω)))
      have hcs : ‖gowersInner F‖ ^ 2 ≤
          (𝔼 h : Fin d → G, ‖A h‖ ^ 2) * (𝔼 h : Fin d → G, ‖B h‖ ^ 2) := by
        rw [gowersInner_succ_eq_expect_mul]
        exact expect_norm_mul_sq_le A B
      have hhalf : ∀ Φ : (Fin d → Bool) → G → ℂ,
          (𝔼 h : Fin d → G,
              ‖𝔼 x : G, ∏ ω : Fin d → Bool,
                parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))‖ ^ 2) ^ (2 ^ d) ≤
            ∏ ω : Fin d → Bool, (gowersBoxDiag (d + 1) (Φ ω)).re := by
        intro Φ
        have heq_c := expect_norm_sq_cube_eq_expect_gowersInner Φ
        have heq_r := congrArg Complex.re heq_c
        rw [expect_ofReal_re, re_expect] at heq_r
        have hcard_cube : Fintype.card (Fin d → Bool) = 2 ^ d := by simp
        have hstep1 :
            (𝔼 h : Fin d → G,
              ‖𝔼 x : G, ∏ ω : Fin d → Bool,
                parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))‖ ^ 2) ≤
              𝔼 t : G, ∏ ω : Fin d → Bool,
                ((gowersBoxDiag d (mulDeriv t (Φ ω))).re) ^
                  ((Fintype.card (Fin d → Bool) : ℝ)⁻¹) := by
          rw [heq_r]
          refine Finset.expect_le_expect fun t _ ↦ ?_
          have hre_le :
              (starRingEnd ℂ (gowersInner fun ω ↦ mulDeriv t (Φ ω))).re ≤
                ‖gowersInner fun ω ↦ mulDeriv t (Φ ω)‖ := by
            simpa using Complex.re_le_norm (gowersInner fun ω ↦ mulDeriv t (Φ ω))
          refine hre_le.trans ?_
          have hih := ih hd1 (fun ω ↦ mulDeriv t (Φ ω))
          have h2d_pos : (0 : ℝ) < (2 ^ d : ℝ) := by positivity
          have hrpow := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hih
            (inv_nonneg.mpr h2d_pos.le)
          have hprod_rpow : ∀ (s : Finset (Fin d → Bool)) (u : (Fin d → Bool) → ℝ) (r : ℝ),
              (∀ ω ∈ s, 0 ≤ u ω) → (∏ ω ∈ s, u ω) ^ r = ∏ ω ∈ s, u ω ^ r := by
            classical
            intro s u r
            induction s using Finset.induction_on with
            | empty => intro _; simp
            | insert a s ha ihs =>
              intro hu
              rw [Finset.prod_insert ha, Finset.prod_insert ha,
                Real.mul_rpow (hu a (Finset.mem_insert_self a s))
                  (Finset.prod_nonneg fun b hb ↦ hu b (Finset.mem_insert_of_mem hb)),
                ihs (fun b hb ↦ hu b (Finset.mem_insert_of_mem hb))]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow,
            Nat.cast_ofNat, mul_inv_cancel₀ h2d_pos.ne', Real.rpow_one,
            hprod_rpow _ _ _ (fun ω _ ↦ gowersBoxDiag_re_nonneg hd1 _)] at hrpow
          simpa [hcard_cube] using hrpow
        have hlhs_nn :
            0 ≤ 𝔼 h : Fin d → G,
              ‖𝔼 x : G, ∏ ω : Fin d → Bool,
                parityConj (cubeWeight ω) (Φ ω (x + cubeShift h ω))‖ ^ 2 :=
          Finset.expect_nonneg fun _ _ ↦ sq_nonneg _
        have hholder := expect_geom_mean_pow_le
          (fun (ω : Fin d → Bool) (t : G) ↦ (gowersBoxDiag d (mulDeriv t (Φ ω))).re)
          (fun ω t ↦ gowersBoxDiag_re_nonneg hd1 _)
        have hstep2 :=
          (pow_le_pow_left₀ hlhs_nn hstep1 (Fintype.card (Fin d → Bool))).trans hholder
        rw [hcard_cube] at hstep2
        refine hstep2.trans (le_of_eq ?_)
        refine Finset.prod_congr rfl fun ω _ ↦ ?_
        rw [gowersBoxDiag_succ_eq_expect_mulDeriv hd1, re_expect]
      have hA := hhalf (fun ω ↦ F (Fin.snoc ω false))
      have hB : (𝔼 h : Fin d → G, ‖B h‖ ^ 2) ^ (2 ^ d) ≤
          ∏ ω : Fin d → Bool, (gowersBoxDiag (d + 1) (F (Fin.snoc ω true))).re := by
        simpa [B] using hhalf (fun ω ↦ F (Fin.snoc ω true))
      have hAnn : 0 ≤ (𝔼 h : Fin d → G, ‖A h‖ ^ 2) ^ (2 ^ d) :=
        pow_nonneg (Finset.expect_nonneg fun _ _ ↦ sq_nonneg _) _
      have hBnn : 0 ≤ ∏ ω : Fin d → Bool, (gowersBoxDiag (d + 1) (F (Fin.snoc ω true))).re :=
        Finset.prod_nonneg fun _ _ ↦ gowersBoxDiag_re_nonneg (by omega) _
      calc ‖gowersInner F‖ ^ (2 ^ (d + 1))
          = (‖gowersInner F‖ ^ 2) ^ (2 ^ d) := by rw [← pow_mul, mul_comm, pow_succ]
        _ ≤ ((𝔼 h : Fin d → G, ‖A h‖ ^ 2) * (𝔼 h : Fin d → G, ‖B h‖ ^ 2)) ^ (2 ^ d) :=
            pow_le_pow_left₀ (sq_nonneg _) hcs (2 ^ d)
        _ = (𝔼 h : Fin d → G, ‖A h‖ ^ 2) ^ (2 ^ d) *
              (𝔼 h : Fin d → G, ‖B h‖ ^ 2) ^ (2 ^ d) := mul_pow _ _ _
        _ ≤ (∏ ω : Fin d → Bool, (gowersBoxDiag (d + 1) (F (Fin.snoc ω false))).re) *
              (∏ ω : Fin d → Bool, (gowersBoxDiag (d + 1) (F (Fin.snoc ω true))).re) :=
            mul_le_mul hA hB (pow_nonneg (Finset.expect_nonneg fun _ _ ↦ sq_nonneg _) _)
              (hAnn.trans hA)
        _ = ∏ ω : Fin (d + 1) → Bool, (gowersBoxDiag (d + 1) (F ω)).re :=
            (prod_cube_snoc (fun ω ↦ (gowersBoxDiag (d + 1) (F ω)).re)).symm

end GowersBox

/-! ### The Gowers Uniformity Norm and Its Seminorm/Norm Properties -/

section GowersNorm

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The Gowers uniformity norm $\|f\|_{U^d(G)} = (\mathrm{Re}\,\langle f \rangle_{U^d(G)})^{2^{-d}}$
of order $d$ on a finite additive abelian group $G$. -/
noncomputable def gowersNorm (d : ℕ) (f : G → ℂ) : ℝ :=
  (gowersBoxDiag d f).re ^ ((1 : ℝ) / (2 ^ d : ℝ))

/-- Nonnegativity $\|f\|_{U^d(G)} \ge 0$ for every $d \ge 1$. -/
theorem gowersNorm_nonneg {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) : 0 ≤ gowersNorm d f :=
  Real.rpow_nonneg (gowersBoxDiag_re_nonneg hd f) _

/-- Exact $2^d$-th power identity $\|f\|_{U^d(G)}^{2^d} = \mathrm{Re}\,\langle f \rangle_{U^d(G)}$
for $d \ge 1$. -/
theorem gowersNorm_pow_two_pow {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    gowersNorm d f ^ (2 ^ d) = (gowersBoxDiag d f).re := by
  have hpos : (0 : ℝ) < (2 ^ d : ℝ) := by positivity
  rw [gowersNorm, ← Real.rpow_natCast, ← Real.rpow_mul (gowersBoxDiag_re_nonneg hd f),
    Nat.cast_pow, Nat.cast_ofNat, one_div_mul_cancel hpos.ne', Real.rpow_one]

/-- Restated Gowers–Cauchy–Schwarz inequality in terms of `gowersNorm`:
$|\langle F \rangle_{U^d(G)}| \le \prod_{\omega \in \{0, 1\}^d} \|F_\omega\|_{U^d(G)}$. -/
theorem norm_gowersInner_le {d : ℕ} (hd : 1 ≤ d) (F : (Fin d → Bool) → G → ℂ) :
    ‖gowersInner F‖ ≤ ∏ ω : Fin d → Bool, gowersNorm d (F ω) := by
  have hpow : ‖gowersInner F‖ ^ (2 ^ d) ≤ (∏ ω : Fin d → Bool, gowersNorm d (F ω)) ^ (2 ^ d) := by
    rw [← Finset.prod_pow]
    simp_rw [gowersNorm_pow_two_pow hd]
    exact norm_gowersInner_pow_le hd F
  have hrhs_nn : 0 ≤ ∏ ω : Fin d → Bool, gowersNorm d (F ω) :=
    Finset.prod_nonneg fun _ _ ↦ gowersNorm_nonneg hd _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hrhs_nn (by positivity : 2 ^ d ≠ 0)).mp hpow

/-- Two functions with identical real box averages have equal Gowers norms. -/
theorem gowersNorm_eq_of_gowersBoxDiag_re_eq {d : ℕ} {f g : G → ℂ}
    (h : (gowersBoxDiag d f).re = (gowersBoxDiag d g).re) :
    gowersNorm d f = gowersNorm d g := by
  simp only [gowersNorm, h]

/-- The Gowers norm of the zero function is `0` for `d ≥ 1`. -/
@[simp]
theorem gowersNorm_zero {d : ℕ} (hd : 1 ≤ d) : gowersNorm d (0 : G → ℂ) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have hbox : (gowersBoxDiag (k + 1) (0 : G → ℂ)).re = 0 := by
    rw [gowersBoxDiag_succ_re]
    refine Finset.expect_eq_zero fun h _ ↦ ?_
    have hprod : ∀ x : G,
        (∏ ω : Fin k → Bool, parityConj (cubeWeight ω) ((0 : G → ℂ) (x + cubeShift h ω))) = 0 :=
      fun _ ↦ Finset.prod_eq_zero (Finset.mem_univ (fun _ ↦ false)) (by simp [parityConj])
    simp_rw [hprod]
    simp
  rw [gowersNorm, hbox, Real.zero_rpow (by positivity)]

/-- Order-`1` Gowers uniformity seminorm equals $|\mathbb{E}_{x \in G} f(x)|$. -/
theorem gowersNorm_one_eq_norm_expect (f : G → ℂ) :
    gowersNorm 1 f = ‖𝔼 x : G, f x‖ := by
  rw [gowersNorm, gowersBoxDiag_one, Complex.ofReal_re]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

/-- Absolute homogeneity $\|c \cdot f\|_{U^d(G)} = |c| \cdot \|f\|_{U^d(G)}$ for $d \ge 1$. -/
theorem gowersNorm_smul {d : ℕ} (hd : 1 ≤ d) (c : ℂ) (f : G → ℂ) :
    gowersNorm d (c • f) = ‖c‖ * gowersNorm d f := by
  have hpow : gowersNorm d (c • f) ^ (2 ^ d) = (‖c‖ * gowersNorm d f) ^ (2 ^ d) := by
    rw [gowersNorm_pow_two_pow hd, mul_pow, gowersNorm_pow_two_pow hd]
    have hbox : gowersBoxDiag d (c • f) = ((‖c‖ ^ (2 ^ d) : ℝ) : ℂ) * gowersBoxDiag d f := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
      rw [gowersBoxDiag_succ_eq_expect_norm_sq, gowersBoxDiag_succ_eq_expect_norm_sq,
        Finset.mul_expect]
      refine Finset.expect_congr rfl fun h _ ↦ ?_
      have hprod : ∀ x : G,
          (∏ ω : Fin k → Bool, parityConj (cubeWeight ω) (c * f (x + cubeShift h ω))) =
            (∏ ω : Fin k → Bool, parityConj (cubeWeight ω) c) *
              (∏ ω : Fin k → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))) := by
        intro x
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun ω _ ↦ parityConj_mul _ _ _
      have hnorm_c : ‖∏ ω : Fin k → Bool, parityConj (cubeWeight ω) c‖ = ‖c‖ ^ (2 ^ k) := by
        rw [norm_prod]
        simp
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [hprod, ← Finset.mul_expect, norm_mul, hnorm_c, mul_pow]
      push_cast
      rw [← pow_mul, ← pow_succ]
    rw [hbox, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact (pow_left_inj₀ (gowersNorm_nonneg hd _)
    (mul_nonneg (norm_nonneg c) (gowersNorm_nonneg hd f)) (by positivity)).mp hpow

/-- Symmetry $\|-f\|_{U^d(G)} = \|f\|_{U^d(G)}$ for $d \ge 1$. -/
@[simp]
theorem gowersNorm_neg {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    gowersNorm d (-f) = gowersNorm d f := by
  have h : -f = (-1 : ℂ) • f := by ext x; simp
  rw [h, gowersNorm_smul hd]
  simp

private lemma prod_add_eq_sum_finset {α R : Type*} [Fintype α] [DecidableEq α] [CommSemiring R]
    (a b : α → R) :
    (∏ i : α, (a i + b i)) = ∑ S : Finset α, ∏ i : α, if i ∈ S then a i else b i := by
  have hpowset : Finset.univ.powerset = (Finset.univ : Finset (Finset α)) := by ext S; simp
  rw [Finset.prod_add, ← Finset.sum_congr hpowset (fun _ _ ↦ rfl)]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset α))
    (p := (· ∈ S)) (f := fun i ↦ if i ∈ S then a i else b i)
  refine Eq.trans ?_ hsplit
  congr 1
  · rw [show Finset.univ.filter (· ∈ S) = S by ext i; simp]
    exact Finset.prod_congr rfl fun i hi ↦ by simp [hi]
  · rw [show Finset.univ.filter (fun i ↦ ¬ i ∈ S) = Finset.univ \ S by ext i; simp]
    exact Finset.prod_congr rfl fun i hi ↦ by simp [Finset.mem_sdiff.mp hi]

/-- **Gowers–Minkowski triangle inequality**:
$\|f + g\|_{U^d(G)} \le \|f\|_{U^d(G)} + \|g\|_{U^d(G)}$ for every $d \ge 1$. -/
theorem gowersNorm_add_le {d : ℕ} (hd : 1 ≤ d) (f g : G → ℂ) :
    gowersNorm d (f + g) ≤ gowersNorm d f + gowersNorm d g := by
  let term (S : Finset (Fin d → Bool)) (ω : Fin d → Bool) : G → ℂ := if ω ∈ S then f else g
  have hexpand : gowersBoxDiag d (f + g) =
      ∑ S : Finset (Fin d → Bool), gowersInner (term S) := by
    simp only [gowersBoxDiag, gowersInner, ← Finset.expect_sum_comm]
    refine Finset.expect_congr rfl fun x _ ↦ Finset.expect_congr rfl fun h _ ↦ ?_
    simp_rw [Pi.add_apply, parityConj_add]
    rw [prod_add_eq_sum_finset]
    refine Finset.sum_congr rfl fun S _ ↦ Finset.prod_congr rfl fun ω _ ↦ ?_
    by_cases hω : ω ∈ S <;> simp [term, hω]
  have hbinom :
      ∑ S : Finset (Fin d → Bool), ∏ ω : Fin d → Bool, gowersNorm d (term S ω) =
        (gowersNorm d f + gowersNorm d g) ^ (2 ^ d) := by
    have hstep := prod_add_eq_sum_finset (α := Fin d → Bool)
      (fun _ ↦ gowersNorm d f) (fun _ ↦ gowersNorm d g)
    have hprod :
        (∏ _ω : Fin d → Bool, (gowersNorm d f + gowersNorm d g)) =
          (gowersNorm d f + gowersNorm d g) ^ (2 ^ d) := by simp
    rw [← hprod, hstep]
    refine Finset.sum_congr rfl fun S _ ↦ Finset.prod_congr rfl fun ω _ ↦ ?_
    by_cases hω : ω ∈ S <;> simp [term, hω]
  have hpow : gowersNorm d (f + g) ^ (2 ^ d) ≤ (gowersNorm d f + gowersNorm d g) ^ (2 ^ d) := by
    rw [gowersNorm_pow_two_pow hd, hexpand, Complex.re_sum, ← hbinom]
    refine Finset.sum_le_sum fun S _ ↦ ?_
    exact (Complex.re_le_norm _).trans (norm_gowersInner_le hd _)
  exact (pow_le_pow_iff_left₀ (gowersNorm_nonneg hd _)
    (add_nonneg (gowersNorm_nonneg hd f) (gowersNorm_nonneg hd g)) (by positivity)).mp hpow

/-- Difference triangle inequality $\|f - g\|_{U^d(G)} \le \|f\|_{U^d(G)} + \|g\|_{U^d(G)}$ for
$d \ge 1$. -/
theorem gowersNorm_sub_le {d : ℕ} (hd : 1 ≤ d) (f g : G → ℂ) :
    gowersNorm d (f - g) ≤ gowersNorm d f + gowersNorm d g := by
  simpa [sub_eq_add_neg, gowersNorm_neg hd] using gowersNorm_add_le hd f (-g)

/-- Pointwise $L^\infty$ domination: if $|f(x)| \le B$ for all $x \in G$ (with $B \ge 0$), then
$\|f\|_{U^d(G)} \le B$ for every $d \ge 1$. -/
theorem gowersNorm_le_of_norm_le {d : ℕ} (hd : 1 ≤ d) {f : G → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : G, ‖f x‖ ≤ B) : gowersNorm d f ≤ B := by
  have hpow : gowersNorm d f ^ (2 ^ d) ≤ B ^ (2 ^ d) := by
    rw [gowersNorm_pow_two_pow hd]
    refine (Complex.re_le_norm _).trans ?_
    simp only [gowersBoxDiag, gowersInner, Fintype.expect_eq_sum_div_card]
    have hprod_le : ∀ x : G, ∀ h : Fin d → G,
        ‖∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))‖ ≤ B ^ (2 ^ d) := by
      intro x h
      rw [norm_prod]
      calc ∏ ω : Fin d → Bool, ‖parityConj (cubeWeight ω) (f (x + cubeShift h ω))‖
          ≤ ∏ _ω : Fin d → Bool, B := by
            gcongr with ω
            simpa using hf (x + cubeShift h ω)
        _ = B ^ (2 ^ d) := by simp
    have hinner : ∀ x : G,
        ‖(∑ h : Fin d → G,
            ∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))) /
          (Fintype.card (Fin d → G) : ℂ)‖ ≤ B ^ (2 ^ d) := by
      intro x
      rw [norm_div, Complex.norm_natCast]
      have hcard_pos : (0 : ℝ) < (Fintype.card (Fin d → G) : ℝ) := by positivity
      rw [div_le_iff₀ hcard_pos]
      calc ‖∑ h : Fin d → G,
              ∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))‖
          ≤ ∑ h : Fin d → G,
              ‖∏ ω : Fin d → Bool, parityConj (cubeWeight ω) (f (x + cubeShift h ω))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _h : Fin d → G, B ^ (2 ^ d) := Finset.sum_le_sum fun h _ ↦ hprod_le x h
        _ = B ^ (2 ^ d) * (Fintype.card (Fin d → G) : ℝ) := by simp [mul_comm]
    rw [norm_div, Complex.norm_natCast]
    have hG_pos : (0 : ℝ) < (Fintype.card G : ℝ) := by positivity
    rw [div_le_iff₀ hG_pos]
    calc ‖∑ x : G, _‖ ≤ ∑ x : G, ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ _x : G, B ^ (2 ^ d) := Finset.sum_le_sum fun x _ ↦ hinner x
      _ = B ^ (2 ^ d) * (Fintype.card G : ℝ) := by simp [mul_comm]
  exact (pow_le_pow_iff_left₀ (gowersNorm_nonneg hd f) hB (by positivity)).mp hpow

/-- Every pointwise `1`-bounded function satisfies $\|f\|_{U^d(G)} \le 1$ for $d \ge 1$. -/
theorem gowersNorm_le_one_of_norm_le_one {d : ℕ} (hd : 1 ≤ d) {f : G → ℂ}
    (hf : ∀ x : G, ‖f x‖ ≤ 1) : gowersNorm d f ≤ 1 :=
  gowersNorm_le_of_norm_le hd zero_le_one hf

/-- Monotonicity $\|f\|_{U^d(G)} \le \|f\|_{U^{d+1}(G)}$ for every $d \ge 1$. -/
theorem gowersNorm_mono {d : ℕ} (hd : 1 ≤ d) (f : G → ℂ) :
    gowersNorm d f ≤ gowersNorm (d + 1) f := by
  let F : (Fin (d + 1) → Bool) → G → ℂ := fun ω ↦ if ω (Fin.last d) then 1 else f
  have hinner : gowersInner F = gowersBoxDiag d f := by
    rw [gowersInner_succ_eq_expect_mul]
    simp only [F, Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, Pi.one_apply, parityConj_one_val,
      Finset.prod_const_one, Finset.expect_const Finset.univ_nonempty, map_one, mul_one]
    exact Finset.expect_comm _ _ _
  have h1 : gowersNorm (d + 1) (1 : G → ℂ) ≤ 1 :=
    gowersNorm_le_one_of_norm_le_one (by omega) fun _ ↦ by simp
  have hle := norm_gowersInner_le (d := d + 1) (by omega) F
  rw [hinner, ← ofReal_gowersBoxDiag_re hd, Complex.norm_real,
    Real.norm_of_nonneg (gowersBoxDiag_re_nonneg hd f), ← gowersNorm_pow_two_pow hd,
    prod_cube_snoc] at hle
  simp only [F, Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hle
  have h1pow : gowersNorm (d + 1) (1 : G → ℂ) ^ (2 ^ d) ≤ 1 :=
    pow_le_one₀ (gowersNorm_nonneg (by omega) _) h1
  have hpow : gowersNorm d f ^ (2 ^ d) ≤ gowersNorm (d + 1) f ^ (2 ^ d) :=
    hle.trans ((mul_le_mul_of_nonneg_left h1pow
      (pow_nonneg (gowersNorm_nonneg (by omega) f) _)).trans (by rw [mul_one]))
  exact (pow_le_pow_iff_left₀ (gowersNorm_nonneg hd f) (gowersNorm_nonneg (by omega) f)
    (by positivity)).mp hpow

/-- Positivity (definiteness) of `gowersNorm` for order $d \ge 2$:
$\|f\|_{U^d(G)} = 0 \iff f = 0$. -/
theorem gowersNorm_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) (f : G → ℂ) :
    gowersNorm d f = 0 ↔ f = 0 := by
  constructor
  · intro h0
    have hle2 : gowersNorm 2 f ≤ gowersNorm d f := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
      clear hd h0
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact ih.trans (gowersNorm_mono (by omega) f)
    have h2_zero : gowersNorm 2 f = 0 :=
      le_antisymm (hle2.trans (le_of_eq h0)) (gowersNorm_nonneg (by decide) f)
    have hbox2 : (gowersBoxDiag 2 f).re = 0 := by
      rw [← gowersNorm_pow_two_pow (by decide : 1 ≤ 2) f, h2_zero]
      norm_num
    rw [gowersBoxDiag_two, expect_ofReal_re, Fintype.expect_eq_sum_div_card,
      div_eq_zero_iff] at hbox2
    have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hsum := hbox2.resolve_right hcard
    have h0step := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hsum 0
      (Finset.mem_univ 0)
    have hexp0 : 𝔼 x : G, mulDeriv 0 f x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h0step)
    have hre0 := congrArg Complex.re hexp0
    rw [Complex.zero_re] at hre0
    simp_rw [mulDeriv_zero_step] at hre0
    rw [expect_ofReal_re, Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hre0
    have hsum0 := hre0.resolve_right hcard
    ext x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hsum0 x
      (Finset.mem_univ x)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · rintro rfl
    exact gowersNorm_zero (by omega)

/-- On any subsingleton group (such as `Fin 0 → ZMod 2`), $\|f\|_{U^d(G)} = |f(x)|$ for all
$d \ge 1$ and $x \in G$. -/
theorem gowersNorm_subsingleton {d : ℕ} (hd : 1 ≤ d) [Subsingleton G] (f : G → ℂ) (x : G) :
    gowersNorm d f = ‖f x‖ := by
  have hpow : gowersNorm d f ^ (2 ^ d) = ‖f x‖ ^ (2 ^ d) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
    rw [gowersNorm_pow_two_pow (by omega), gowersBoxDiag_succ_re]
    have hpt : ∀ (h : Fin k → G) (y : G) (ω : Fin k → Bool), f (y + cubeShift h ω) = f x :=
      fun _ _ _ ↦ congrArg f (Subsingleton.elim _ _)
    simp_rw [hpt]
    simp only [Finset.expect_const Finset.univ_nonempty, norm_prod, norm_parityConj,
      Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    rw [← pow_mul, mul_comm (2 ^ k) 2, pow_succ']
  exact (pow_left_inj₀ (gowersNorm_nonneg hd f) (norm_nonneg _) (by positivity)).mp hpow

end GowersNorm

end CslibFrontier.Foundations.BooleanAnalysis
