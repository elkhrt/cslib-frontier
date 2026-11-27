/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ROABP
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Saxena's Duality Reduction from Powered Sums of Univariates to Any-Order ROABPs

Saxena's binomial-transition duality embedding showing that every powered sum of univariate
polynomials `α * (c₀ + ∑ j, u_j(X_j)) ^ e` (and therefore every `Σ∧Σ∧` circuit) is computed by an
any-order read-once oblivious algebraic branching program
(`Cslib.Circuits.Arithmetic.IsAnyOrderROABP`)
of width `e + 1` (respectively `∑_q (e_q + 1)`).

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.SumUnivariateGate`: syntactic `Σ∧` gate
  `c₀ + ∑ j : Fin n, u_j(X_j)`.
* `CslibFrontier.Computability.Circuit.Arithmetic.binomialTransition`: upper-triangular
  `(e + 1) × (e + 1)` binomial transition matrix `(P_e(p))_{r, c} = C(c, r) * p ^ (c - r)`.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.binomialTransition_add`: homomorphism law
  `P_e(p) * P_e(q) = P_e(p + q)`.
* `CslibFrontier.Computability.Circuit.Arithmetic.isAnyOrderROABP_singlePow`: for `n ≥ 1`, every
  powered `Σ∧` gate `C α * g.evalPoly ^ e` satisfies
  `Cslib.Circuits.Arithmetic.IsAnyOrderROABP (e + 1)`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open MvPolynomial

/-- A syntactic `Σ∧` gate `c₀ + ∑ j : Fin n, u_j(X_j)` in `n` variables over `R`. -/
@[ext]
structure SumUnivariateGate (n : ℕ) (R : Type*) [CommSemiring R] where
  /-- Constant wire `c₀`. -/
  constTerm : R
  /-- Univariate polynomial `u_j` on each coordinate `j : Fin n`. -/
  terms : Fin n → Polynomial R

/-- Multivariate polynomial computed by a `SumUnivariateGate`. -/
@[expose]
noncomputable def SumUnivariateGate.evalPoly {n : ℕ} {R : Type*} [CommSemiring R]
    (g : SumUnivariateGate n R) : MvPolynomial (Fin n) R :=
  MvPolynomial.C g.constTerm +
    ∑ j : Fin n, Polynomial.aeval (MvPolynomial.X j : MvPolynomial (Fin n) R) (g.terms j)

/-- Upper-triangular `(e + 1) × (e + 1)` binomial transition matrix
`(P_e(p))_{r, c} = C(c, r) * p ^ (c - r)` for `r ≤ c` and `0` otherwise. -/
@[expose]
def binomialTransition {R : Type*} [CommSemiring R] (e : ℕ) (p : R) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) R :=
  Matrix.of fun r c ↦
    if (r : ℕ) ≤ c then (Nat.choose c r : R) * p ^ ((c : ℕ) - r) else 0

@[simp]
theorem binomialTransition_apply {R : Type*} [CommSemiring R] (e : ℕ) (p : R)
    (r c : Fin (e + 1)) :
    binomialTransition e p r c =
      if (r : ℕ) ≤ c then (Nat.choose c r : R) * p ^ ((c : ℕ) - r) else 0 := rfl

@[simp]
theorem binomialTransition_zero {R : Type*} [CommSemiring R] (e : ℕ) :
    binomialTransition e (0 : R) = 1 := by
  ext r c
  rw [binomialTransition_apply, Matrix.one_apply]
  rcases eq_or_ne r c with rfl | hne
  · simp
  · have hval : (r : ℕ) ≠ c := fun h ↦ hne (Fin.ext h)
    split_ifs with hle
    · have hsub : (c : ℕ) - r ≠ 0 := by omega
      simp [zero_pow hsub]
    · rfl

/-- Multiplicative homomorphism law `P_e(p) * P_e(q) = P_e(p + q)` for binomial transition
matrices. -/
theorem binomialTransition_add {R : Type*} [CommSemiring R] (e : ℕ) (p q : R) :
    binomialTransition e p * binomialTransition e q = binomialTransition e (p + q) := by
  ext r d
  rw [Matrix.mul_apply, binomialTransition_apply]
  by_cases hrd : (r : ℕ) ≤ d
  · simp only [hrd, ite_true]
    have hterm (c : Fin (e + 1)) :
        binomialTransition e p r c * binomialTransition e q c d =
          if (r : ℕ) ≤ c ∧ (c : ℕ) ≤ d then
            (Nat.choose d r : R) * ((Nat.choose ((d : ℕ) - r) ((c : ℕ) - r) : R) *
              p ^ ((c : ℕ) - r) * q ^ (((d : ℕ) - r) - ((c : ℕ) - r)))
          else 0 := by
      rw [binomialTransition_apply, binomialTransition_apply]
      by_cases h1 : (r : ℕ) ≤ c <;> by_cases h2 : (c : ℕ) ≤ d
      · simp only [h1, h2, ite_true]
        have hchoose : Nat.choose d r * Nat.choose ((d : ℕ) - r) ((c : ℕ) - r) =
            Nat.choose c r * Nat.choose d c := by
          have hchoose1 := Nat.choose_mul (n := d) (k := c) (s := r) h1
          rw [mul_comm (Nat.choose d c)] at hchoose1
          exact hchoose1.symm
        have hsub : (d : ℕ) - c = ((d : ℕ) - r) - ((c : ℕ) - r) := by omega
        calc
          (Nat.choose c r : R) * p ^ ((c : ℕ) - r) *
              ((Nat.choose d c : R) * q ^ ((d : ℕ) - c)) =
              ((Nat.choose c r * Nat.choose d c : ℕ) : R) * p ^ ((c : ℕ) - r) *
                q ^ (((d : ℕ) - r) - ((c : ℕ) - r)) := by
            rw [Nat.cast_mul, hsub]; ring
          _ = (Nat.choose d r : R) * ((Nat.choose ((d : ℕ) - r) ((c : ℕ) - r) : R) *
                p ^ ((c : ℕ) - r) * q ^ (((d : ℕ) - r) - ((c : ℕ) - r))) := by
            rw [← hchoose, Nat.cast_mul]; ring
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    simp_rw [hterm]
    have hbij :
        (∑ c : Fin (e + 1), if (r : ℕ) ≤ c ∧ (c : ℕ) ≤ d then
            (Nat.choose d r : R) * ((Nat.choose ((d : ℕ) - r) ((c : ℕ) - r) : R) *
              p ^ ((c : ℕ) - r) * q ^ (((d : ℕ) - r) - ((c : ℕ) - r)))
          else 0) =
          (Nat.choose d r : R) * ∑ k ∈ Finset.range ((d : ℕ) - r + 1),
            p ^ k * q ^ (((d : ℕ) - r) - k) * (Nat.choose ((d : ℕ) - r) k : R) := by
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_bij (fun c _ ↦ (c : ℕ) - r) ?_ ?_ ?_ ?_
      · intro c hc
        rw [Finset.mem_filter] at hc
        exact Finset.mem_range.mpr (by omega)
      · intro c₁ hc₁ c₂ hc₂ heq
        rw [Finset.mem_filter] at hc₁ hc₂
        exact Fin.ext (by omega)
      · intro k hk
        rw [Finset.mem_range] at hk
        have hd_lt : (d : ℕ) < e + 1 := d.isLt
        have hlt : (r : ℕ) + k < e + 1 := by omega
        refine ⟨⟨(r : ℕ) + k, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        dsimp; omega
      · intro c _; ring
    rw [hbij, ← add_pow]
  · simp only [hrd, ite_false]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    rw [binomialTransition_apply, binomialTransition_apply]
    split_ifs with hrc hcd
    · omega
    · simp
    · simp
    · simp

private lemma list_prod_binomialTransition {R : Type*} [CommSemiring R] (e : ℕ) (L : List R) :
    (L.map (binomialTransition e)).prod = binomialTransition e L.sum := by
  induction L with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.prod_cons, ih, binomialTransition_add, List.sum_cons]

private lemma list_sum_eq_finset_sum {α β : Type*} [AddCommMonoid β] [Fintype α] [DecidableEq α]
    (l : List α) (hl_nodup : l.Nodup) (hl_mem : ∀ i : α, i ∈ l) (f : α → β) :
    (l.map f).sum = ∑ i : α, f i := by
  let s : Finset α := ⟨↑l, Multiset.coe_nodup.mpr hl_nodup⟩
  have hs : s = Finset.univ := by ext i; simp [s, hl_mem i]
  rw [← hs, Finset.sum_mk, Multiset.map_coe, Multiset.sum_coe]

/-- **Saxena's duality for a single powered `Σ∧` gate**: for `n ≥ 1` over any field `F`,
`C α * g.evalPoly ^ e` is computed in every variable order by a width-`(e + 1)` ROABP
(`Cslib.Circuits.Arithmetic.IsAnyOrderROABP`). -/
theorem isAnyOrderROABP_singlePow {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n)
    (α : F) (g : SumUnivariateGate n F) (e : ℕ) :
    Cslib.Circuits.Arithmetic.IsAnyOrderROABP (e + 1) (MvPolynomial.C α * g.evalPoly ^ e) := by
  classical
  intro l hl_nodup hl_mem
  rcases l with _ | ⟨i₀, ls⟩
  · exfalso; exact List.not_mem_nil (hl_mem ⟨0, hn⟩)
  have hi₀_not_mem : i₀ ∉ ls := (List.nodup_cons.mp hl_nodup).1
  let baseLayer (i : Fin n) : Matrix (Fin (e + 1)) (Fin (e + 1)) (Polynomial F) :=
    binomialTransition e (g.terms i)
  let U : Matrix (Fin (e + 1)) (Fin (e + 1)) (Polynomial F) :=
    Matrix.of fun r c ↦ if (r : ℕ) = 0 then Polynomial.C (α * g.constTerm ^ (c : ℕ)) else 0
  let M : Fin n → Matrix (Fin (e + 1)) (Fin (e + 1)) (Polynomial F) := fun i ↦
    if i = i₀ then U * baseLayer i₀ else baseLayer i
  refine ⟨M, 0, ⟨e, Nat.lt_succ_self e⟩, ?_⟩
  have hmap_base (i : Fin n) :
      (baseLayer i).map (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F)) =
        binomialTransition e
          (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (g.terms i)) := by
    ext r c
    simp only [baseLayer, Matrix.map_apply, binomialTransition_apply]
    split_ifs <;> simp
  have hmap_U :
      (U * baseLayer i₀).map (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial (Fin n) F)) =
        U.map (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial (Fin n) F)) *
          binomialTransition e
            (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial (Fin n) F) (g.terms i₀)) := by
    rw [← hmap_base i₀, ← Matrix.map_mul]
  have htail :
      (ls.map fun i ↦ (M i).map (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F))) =
        (ls.map fun i ↦
          Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (g.terms i)).map
          (binomialTransition e) := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi ↦ ?_
    have hne : i ≠ i₀ := fun h ↦ hi₀_not_mem (h ▸ hi)
    simp [M, hne, hmap_base]
  rw [Cslib.Circuits.Arithmetic.roabpProd, List.map_cons, List.prod_cons]
  have hM0 : M i₀ = U * baseLayer i₀ := by simp [M]
  rw [hM0, hmap_U, htail, list_prod_binomialTransition, Matrix.mul_assoc,
    binomialTransition_add]
  have hsum :
      Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial (Fin n) F) (g.terms i₀) +
        (ls.map fun i ↦
          Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (g.terms i)).sum =
        ∑ j : Fin n, Polynomial.aeval (MvPolynomial.X j : MvPolynomial (Fin n) F) (g.terms j) := by
    simpa [List.map_cons, List.sum_cons] using
      list_sum_eq_finset_sum (i₀ :: ls) hl_nodup hl_mem
        (fun i ↦ Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) F) (g.terms i))
  rw [hsum]
  let S : MvPolynomial (Fin n) F :=
    ∑ j : Fin n, Polynomial.aeval (MvPolynomial.X j : MvPolynomial (Fin n) F) (g.terms j)
  rw [Matrix.mul_apply]
  have hU_row (c : Fin (e + 1)) :
      (U.map (Polynomial.aeval (MvPolynomial.X i₀ : MvPolynomial (Fin n) F))) 0 c =
        MvPolynomial.C α * MvPolynomial.C g.constTerm ^ (c : ℕ) := by
    simp [U]
  simp_rw [hU_row, binomialTransition_apply]
  have hle_all (c : Fin (e + 1)) : (c : ℕ) ≤ e := Nat.lt_succ_iff.mp c.isLt
  have hsimp :
      (∑ c : Fin (e + 1),
        MvPolynomial.C α * MvPolynomial.C g.constTerm ^ (c : ℕ) *
          (if (c : ℕ) ≤ (⟨e, Nat.lt_succ_self e⟩ : Fin (e + 1)) then
            (Nat.choose e c : MvPolynomial (Fin n) F) * S ^ (e - (c : ℕ))
          else 0)) =
      MvPolynomial.C α * ∑ k ∈ Finset.range (e + 1),
        MvPolynomial.C g.constTerm ^ k * S ^ (e -
          k) * (Nat.choose e k : MvPolynomial (Fin n) F) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun c _ ↦ (c : ℕ)) ?_ ?_ ?_ ?_
    · intro c _; exact Finset.mem_range.mpr c.isLt
    · intro c₁ _ c₂ _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro c _
      have hc : (c : ℕ) ≤ e := hle_all c
      simp only [hc, ite_true]
      ring
  rw [hsimp, SumUnivariateGate.evalPoly, add_pow]

end CslibFrontier.Computability.Circuit.Arithmetic
