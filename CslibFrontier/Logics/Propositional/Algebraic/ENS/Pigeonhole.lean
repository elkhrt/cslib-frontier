/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.ENS.Basic
public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Propositional Pigeonhole Polynomial System $\neg \mathrm{PHP}_n$

This module formalizes the algebraic encoding $\neg \mathrm{PHP}_n$ of the negation of the
pigeonhole principle over $\mathbb{F}_p$, with its bounded-degree space
$S(n, d) = \mathbb{F}_p^{\le d}[\mathrm{Var}]$, truncated Nullstellensatz ideal span $V(n, d)$,
semantic unsatisfiability, low-degree base and sharpness cases, and the cubic step-count lower
bound for $F_\ell(\mathrm{MOD}_p)$-refutations, verified under standard Lean axioms.

## Main definitions

- `CslibFrontier.Logic.PL.ENS.PhpVar`: propositional variables $x_{i, j}$ for
  $(i, j) \in [n+1] \times [n]$.
- `CslibFrontier.Logic.PL.ENS.negPhpFinset`, `CslibFrontier.Logic.PL.ENS.negPhpSet`: the polynomial
  system $\neg \mathrm{PHP}_n$ over $\mathbb{F}_p$.
- `CslibFrontier.Logic.PL.ENS.PhpPolySpace`, `CslibFrontier.Logic.PL.ENS.phpIdealSpan`: the
  bounded-degree space $S(n, d)$ and low-degree ideal span $V(n, d)$.
- `CslibFrontier.Logic.PL.ENS.negPhpFormulaSet`: depth-`≤ 2` $F(\mathrm{MOD}_p)$ formula encoding
  of $\neg \mathrm{PHP}_n$.

## Main results

- `CslibFrontier.Logic.PL.ENS.negPhpSet_unsatisfiable`: unsatisfiability of $\neg \mathrm{PHP}_n$
  over $\mathbb{F}_p$.
- `CslibFrontier.Logic.PL.ENS.one_notMem_phpIdealSpan_zero`,
  `CslibFrontier.Logic.PL.ENS.one_notMem_phpIdealSpan_one`,
  `CslibFrontier.Logic.PL.ENS.one_mem_phpIdealSpan_one_two`: unconditional degree-$0$/$1$
  non-membership and the $n = 1, d = 2$ refutation identity $1 \in V(1, 2)$.
- `CslibFrontier.Logic.PL.ENS.n_sq_mul_succ_add_two_le_two_mul_length_of_phpRefutation`,
  `CslibFrontier.Logic.PL.ENS.n_cube_lt_two_mul_length_of_phpRefutation`: cubic step-count lower
  bound $n^3 < 2 k$ for any $F_\ell(\mathrm{MOD}_p)$-refutation of $\neg \mathrm{PHP}_n$.
-/

public section

namespace CslibFrontier.Logic.PL.ENS

section NegPhp

/-- Propositional variables $x_{i, j}$ ($i \in [n+1], j \in [n]$) of the pigeonhole system
$\neg \mathrm{PHP}_n$. -/
abbrev PhpVar (n : ℕ) : Type :=
  Fin (n + 1) × Fin n

/-- Collision polynomial $Q_{i_1, i_2; j} := x_{i_1, j} x_{i_2, j}$ for two pigeons $i_1, i_2$
mapped to the same hole $j$. -/
noncomputable def phpRowDisjointPoly (n p : ℕ) (i₁ i₂ : Fin (n + 1)) (j : Fin n) :
    MvPolynomial (PhpVar n) (ZMod p) :=
  MvPolynomial.X (i₁, j) * MvPolynomial.X (i₂, j)

theorem phpRowDisjointPoly_def (n p : ℕ) (i₁ i₂ : Fin (n + 1)) (j : Fin n) :
    phpRowDisjointPoly n p i₁ i₂ j = MvPolynomial.X (i₁, j) * MvPolynomial.X (i₂, j) := by
  unfold phpRowDisjointPoly; rfl

@[simp]
theorem eval_phpRowDisjointPoly {n p : ℕ} (α : PhpVar n → ZMod p) (i₁ i₂ : Fin (n + 1))
    (j : Fin n) :
    MvPolynomial.eval α (phpRowDisjointPoly n p i₁ i₂ j) = α (i₁, j) * α (i₂, j) := by
  simp [phpRowDisjointPoly_def]

/-- Multi-hole polynomial $Q_{i; j_1, j_2} := x_{i, j_1} x_{i, j_2}$ for one pigeon $i$ mapped to
two holes $j_1, j_2$. -/
noncomputable def phpColDisjointPoly (n p : ℕ) (i : Fin (n + 1)) (j₁ j₂ : Fin n) :
    MvPolynomial (PhpVar n) (ZMod p) :=
  MvPolynomial.X (i, j₁) * MvPolynomial.X (i, j₂)

theorem phpColDisjointPoly_def (n p : ℕ) (i : Fin (n + 1)) (j₁ j₂ : Fin n) :
    phpColDisjointPoly n p i j₁ j₂ = MvPolynomial.X (i, j₁) * MvPolynomial.X (i, j₂) := by
  unfold phpColDisjointPoly; rfl

@[simp]
theorem eval_phpColDisjointPoly {n p : ℕ} (α : PhpVar n → ZMod p) (i : Fin (n + 1))
    (j₁ j₂ : Fin n) :
    MvPolynomial.eval α (phpColDisjointPoly n p i j₁ j₂) = α (i, j₁) * α (i, j₂) := by
  simp [phpColDisjointPoly_def]

/-- Pigeon-totality polynomial $Q_i := 1 - \sum_{j \in [n]} x_{i, j}$ for pigeon $i$. -/
noncomputable def phpPigeonPoly (n p : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (PhpVar n) (ZMod p) :=
  1 - ∑ j : Fin n, MvPolynomial.X (i, j)

theorem phpPigeonPoly_def (n p : ℕ) (i : Fin (n + 1)) :
    phpPigeonPoly n p i = 1 - ∑ j : Fin n, MvPolynomial.X (i, j) := by
  unfold phpPigeonPoly; rfl

@[simp]
theorem eval_phpPigeonPoly {n p : ℕ} (α : PhpVar n → ZMod p) (i : Fin (n + 1)) :
    MvPolynomial.eval α (phpPigeonPoly n p i) = 1 - ∑ j : Fin n, α (i, j) := by
  simp [phpPigeonPoly_def]

/-- Boolean axiom polynomial $x_{i, j}^2 - x_{i, j}$ for variable $(i, j)$. -/
noncomputable def phpBoolPoly (n p : ℕ) (v : PhpVar n) :
    MvPolynomial (PhpVar n) (ZMod p) :=
  MvPolynomial.X v ^ 2 - MvPolynomial.X v

theorem phpBoolPoly_def (n p : ℕ) (v : PhpVar n) :
    phpBoolPoly n p v = MvPolynomial.X v ^ 2 - MvPolynomial.X v := by
  unfold phpBoolPoly; rfl

@[simp]
theorem eval_phpBoolPoly {n p : ℕ} (α : PhpVar n → ZMod p) (v : PhpVar n) :
    MvPolynomial.eval α (phpBoolPoly n p v) = α v ^ 2 - α v := by
  simp [phpBoolPoly_def]

/-- Finite set of polynomials constituting $\neg \mathrm{PHP}_n$ over $\mathbb{F}_p$. -/
noncomputable def negPhpFinset (n p : ℕ) : Finset (MvPolynomial (PhpVar n) (ZMod p)) :=
  (((Finset.univ : Finset ((Fin (n + 1) × Fin (n + 1)) × Fin n)).filter
        fun t => t.1.1 ≠ t.1.2).image
      fun t => phpRowDisjointPoly n p t.1.1 t.1.2 t.2) ∪
    (((Finset.univ : Finset (Fin (n + 1) × (Fin n × Fin n))).filter
          fun t => t.2.1 ≠ t.2.2).image
        fun t => phpColDisjointPoly n p t.1 t.2.1 t.2.2) ∪
    ((Finset.univ : Finset (Fin (n + 1))).image (phpPigeonPoly n p)) ∪
    ((Finset.univ : Finset (PhpVar n)).image (phpBoolPoly n p))

theorem negPhpFinset_def (n p : ℕ) :
    negPhpFinset n p =
      (((Finset.univ : Finset ((Fin (n + 1) × Fin (n + 1)) × Fin n)).filter
            fun t => t.1.1 ≠ t.1.2).image
          fun t => phpRowDisjointPoly n p t.1.1 t.1.2 t.2) ∪
        (((Finset.univ : Finset (Fin (n + 1) × (Fin n × Fin n))).filter
              fun t => t.2.1 ≠ t.2.2).image
            fun t => phpColDisjointPoly n p t.1 t.2.1 t.2.2) ∪
        ((Finset.univ : Finset (Fin (n + 1))).image (phpPigeonPoly n p)) ∪
        ((Finset.univ : Finset (PhpVar n)).image (phpBoolPoly n p)) := by
  unfold negPhpFinset; rfl

/-- Set view of $\neg \mathrm{PHP}_n$ over $\mathbb{F}_p$. -/
noncomputable def negPhpSet (n p : ℕ) : Set (MvPolynomial (PhpVar n) (ZMod p)) :=
  ↑(negPhpFinset n p)

theorem negPhpSet_def (n p : ℕ) :
    negPhpSet n p = ↑(negPhpFinset n p) := by
  unfold negPhpSet; rfl

/-- Every collision polynomial $x_{i_1, j} x_{i_2, j}$ with $i_1 \neq i_2$ belongs to
$\neg \mathrm{PHP}_n$. -/
theorem phpRowDisjointPoly_mem_negPhpSet {n p : ℕ} {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂)
    (j : Fin n) :
    phpRowDisjointPoly n p i₁ i₂ j ∈ negPhpSet n p := by
  simp only [negPhpSet, Finset.mem_coe, negPhpFinset, Finset.mem_union]
  left; left; left
  exact Finset.mem_image.mpr
    ⟨((i₁, i₂), j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩

/-- Every multi-hole polynomial $x_{i, j_1} x_{i, j_2}$ with $j_1 \neq j_2$ belongs to
$\neg \mathrm{PHP}_n$. -/
theorem phpColDisjointPoly_mem_negPhpSet {n p : ℕ} (i : Fin (n + 1)) {j₁ j₂ : Fin n}
    (hne : j₁ ≠ j₂) :
    phpColDisjointPoly n p i j₁ j₂ ∈ negPhpSet n p := by
  simp only [negPhpSet, Finset.mem_coe, negPhpFinset, Finset.mem_union]
  left; left; right
  exact Finset.mem_image.mpr
    ⟨(i, (j₁, j₂)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩

/-- Every pigeon-totality polynomial $1 - \sum_j x_{i, j}$ belongs to $\neg \mathrm{PHP}_n$. -/
theorem phpPigeonPoly_mem_negPhpSet {n p : ℕ} (i : Fin (n + 1)) :
    phpPigeonPoly n p i ∈ negPhpSet n p := by
  simp only [negPhpSet, Finset.mem_coe, negPhpFinset, Finset.mem_union]
  left; right
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- Every Boolean polynomial $x_{i, j}^2 - x_{i, j}$ belongs to $\neg \mathrm{PHP}_n$. -/
theorem phpBoolPoly_mem_negPhpSet {n p : ℕ} (v : PhpVar n) :
    phpBoolPoly n p v ∈ negPhpSet n p := by
  simp only [negPhpSet, Finset.mem_coe, negPhpFinset, Finset.mem_union]
  right
  exact Finset.mem_image_of_mem _ (Finset.mem_univ v)

/-- Unsatisfiability of $\neg \mathrm{PHP}_n$ over $\mathbb{F}_p$ for any prime $p$ and $n \ge 0$:
no assignment $\alpha : \mathrm{PhpVar}(n) \to \mathbb{F}_p$ simultaneously vanishes on every
polynomial in $\neg \mathrm{PHP}_n$. -/
theorem negPhpSet_unsatisfiable (n p : ℕ) [Fact p.Prime] (α : PhpVar n → ZMod p) :
    ¬ ∀ f ∈ negPhpSet n p, MvPolynomial.eval α f = 0 := by
  intro hall
  have hex_hole : ∀ i : Fin (n + 1), ∃ j : Fin n, α (i, j) = 1 := fun i => by
    have hqi := hall _ (phpPigeonPoly_mem_negPhpSet i)
    simp only [eval_phpPigeonPoly, sub_eq_zero] at hqi
    by_contra hno; push Not at hno
    have hzero : ∀ j : Fin n, α (i, j) = 0 := fun j => by
      have hb := hall _ (phpBoolPoly_mem_negPhpSet (i, j))
      simp only [eval_phpBoolPoly] at hb
      have hmul : α (i, j) * (α (i, j) - 1) = 0 :=
        (by ring : α (i, j) * (α (i, j) - 1) = α (i, j) ^ 2 - α (i, j)).trans hb
      exact (mul_eq_zero.mp hmul).elim id fun h1 => False.elim (hno j (sub_eq_zero.mp h1))
    rw [Finset.sum_eq_zero fun j _ => hzero j] at hqi
    exact one_ne_zero hqi
  choose f hf using hex_hole
  have hfinj : Function.Injective f := fun i₁ i₂ heq => by
    by_contra hne
    have hrow := hall _ (phpRowDisjointPoly_mem_negPhpSet hne (f i₁))
    rw [eval_phpRowDisjointPoly, hf i₁, heq, hf i₂, one_mul] at hrow
    exact one_ne_zero hrow
  have hcard := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_fin] at hcard; omega

end NegPhp

section SpaceAndIdeal

/-- The $\mathbb{F}_p$-vector space $S(n, d) := \mathbb{F}_p^{\le d}[\mathrm{PhpVar}(n)]$ of
polynomials of total degree at most $d$. -/
abbrev PhpPolySpace (n p d : ℕ) : Type :=
  PolyBoundedDeg (PhpVar n) p d

/-- The $\mathbb{F}_p$-subspace $V(n, d) := \mathrm{Span}\{ g \cdot f \mid f \in \neg
\mathrm{PHP}_n \wedge \deg(f g) \le d \} \le S(n, d)$. -/
noncomputable def phpIdealSpan (n p d : ℕ) : Submodule (ZMod p) (PhpPolySpace n p d) :=
  Submodule.span (ZMod p)
    { q : PhpPolySpace n p d | ∃ f ∈ negPhpSet n p, ∃ g : PhpPolySpace n p d, q.1 = g.1 * f }

theorem phpIdealSpan_def (n p d : ℕ) :
    phpIdealSpan n p d =
      Submodule.span (ZMod p)
        { q : PhpPolySpace n p d |
          ∃ f ∈ negPhpSet n p, ∃ g : PhpPolySpace n p d, q.1 = g.1 * f } := by
  unfold phpIdealSpan; rfl

/-- Every degree-`≤ d` multiple $f \cdot g$ of $f \in \neg \mathrm{PHP}_n$ by $g \in S(n, d)$ lies
in $V(n, d)$. -/
theorem mem_phpIdealSpan_of_mul {n p d : ℕ} {f : MvPolynomial (PhpVar n) (ZMod p)}
    (hf : f ∈ negPhpSet n p) (g : PhpPolySpace n p d)
    (hdeg : (f * g.1).totalDegree ≤ d) :
    (⟨f * g.1, (MvPolynomial.mem_restrictTotalDegree (PhpVar n) d (f * g.1)).mpr hdeg⟩ :
        PhpPolySpace n p d) ∈ phpIdealSpan n p d := by
  refine Submodule.subset_span ?_
  exact ⟨f, hf, g, mul_comm f g.1⟩

/-- An $\mathbb{F}_p$-linear functional on $S(n, d)$ vanishes on all degree-`≤ d` ideal multiples
$f \cdot g$ ($f \in \neg \mathrm{PHP}_n$) if and only if it vanishes on $V(n, d)$. -/
theorem vanishes_phpIdealSpan_iff {n p d : ℕ} (L : PhpPolySpace n p d →ₗ[ZMod p] ZMod p) :
    (∀ q ∈ phpIdealSpan n p d, L q = 0) ↔
      ∀ f ∈ negPhpSet n p, ∀ g : PhpPolySpace n p d,
        ∀ hdeg : (f * g.1).totalDegree ≤ d,
          L ⟨f * g.1,
            (MvPolynomial.mem_restrictTotalDegree (PhpVar n) d (f * g.1)).mpr hdeg⟩ = 0 := by
  constructor
  · intro hV f hf g hdeg
    exact hV _ (mem_phpIdealSpan_of_mul hf g hdeg)
  · intro hgen q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨f, hf, g, hxeq⟩
      have hdeg : (f * g.1).totalDegree ≤ d := by
        rw [mul_comm, ← hxeq]
        exact x.totalDegree_le
      have hsub :
          x = ⟨f * g.1, (MvPolynomial.mem_restrictTotalDegree (PhpVar n) d (f * g.1)).mpr hdeg⟩ :=
        Subtype.ext (hxeq.trans (mul_comm g.1 f))
      rw [hsub]
      exact hgen f hf g hdeg
    | zero => exact map_zero L
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul a x _ ihx => rw [map_smul, ihx, smul_zero]

private theorem eq_C_of_totalDegree_zero {V : Type*} {p : ℕ}
    {P : MvPolynomial V (ZMod p)} (hP : P.totalDegree = 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · have hnot : m ∉ P.support := by
      intro hmem
      have hle : (m.sum fun _ e => e) ≤ P.totalDegree :=
        Finset.le_sup (f := fun s : V →₀ ℕ => s.sum fun _ e => e) hmem
      rw [hP] at hle
      apply hm; ext v
      by_cases hv : v ∈ m.support
      · have hv_le : m v ≤ m.sum fun _ e => e :=
          Finset.single_le_sum (f := fun x => m x) (fun _ _ => Nat.zero_le _) hv
        rw [Finsupp.zero_apply]; omega
      · rw [Finsupp.notMem_support_iff.mp hv, Finsupp.zero_apply]
    rw [MvPolynomial.notMem_support_iff.mp hnot, MvPolynomial.coeff_C, ite_eq_right (Ne.symm hm)]

private theorem eval_const_of_totalDegree_zero {V : Type*} {p : ℕ}
    {P : MvPolynomial V (ZMod p)} (hP : P.totalDegree = 0)
    (a b : V → ZMod p) : MvPolynomial.eval a P = MvPolynomial.eval b P := by
  rw [eq_C_of_totalDegree_zero hP, MvPolynomial.eval_C, MvPolynomial.eval_C]

private theorem totalDegree_ge_two_of_rowDisjoint {n p : ℕ} [Fact p.Prime]
    (i₁ i₂ : Fin (n + 1)) (j : Fin n) :
    2 ≤ (phpRowDisjointPoly n p i₁ i₂ j).totalDegree := by
  rw [phpRowDisjointPoly_def,
    MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _),
    MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]

private theorem totalDegree_ge_two_of_colDisjoint {n p : ℕ} [Fact p.Prime]
    (i : Fin (n + 1)) (j₁ j₂ : Fin n) :
    2 ≤ (phpColDisjointPoly n p i j₁ j₂).totalDegree := by
  rw [phpColDisjointPoly_def,
    MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _),
    MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]

private theorem totalDegree_ge_two_of_boolPoly {n p : ℕ} [Fact p.Prime] (v : PhpVar n) :
    2 ≤ (phpBoolPoly n p v).totalDegree := by
  have hcoeff : (phpBoolPoly n p v).coeff (Finsupp.single v 2) = 1 := by
    simp [phpBoolPoly_def, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  have hle : ((Finsupp.single v 2).sum fun _ e => e) ≤ (phpBoolPoly n p v).totalDegree :=
    Finset.le_sup (f := fun s : PhpVar n →₀ ℕ => s.sum fun _ e => e)
      (MvPolynomial.mem_support_iff.mpr (by rw [hcoeff]; exact one_ne_zero))
  rwa [Finsupp.sum_single_index rfl] at hle

private theorem mul_totalDegree_ge_two {n p : ℕ} [Fact p.Prime]
    {P Q : MvPolynomial (PhpVar n) (ZMod p)} (hP : 2 ≤ P.totalDegree) (hQ : Q ≠ 0) :
    2 ≤ (P * Q).totalDegree := by
  have hP0 : P ≠ 0 := fun h0 => by rw [h0, MvPolynomial.totalDegree_zero] at hP; omega
  rw [MvPolynomial.totalDegree_mul_of_isDomain hP0 hQ]
  omega

/-- Unconditional degree-$0$ base case: for $n \ge 1$ and prime $p$, $V(n, 0) = \bot$, and in
particular $1 \notin V(n, 0)$. -/
theorem one_notMem_phpIdealSpan_zero {n p : ℕ} [Fact p.Prime] (hn : 1 ≤ n) :
    PolyBoundedDeg.one (PhpVar n) p 0 ∉ phpIdealSpan n p 0 := by
  have hbot : phpIdealSpan n p 0 = ⊥ := by
    rw [phpIdealSpan_def, Submodule.span_eq_bot]
    rintro q ⟨f, hf, g, hq⟩
    have hf_deg_pos : 1 ≤ f.totalDegree := by
      simp only [negPhpSet_def, Finset.mem_coe, negPhpFinset_def, Finset.mem_union] at hf
      rcases hf with ((hf | hf) | hf) | hf
      · rcases Finset.mem_image.mp hf with ⟨⟨⟨i₁, i₂⟩, j⟩, _, rfl⟩
        exact le_trans (by omega) (totalDegree_ge_two_of_rowDisjoint (p := p) i₁ i₂ j)
      · rcases Finset.mem_image.mp hf with ⟨⟨i, ⟨j₁, j₂⟩⟩, _, rfl⟩
        exact le_trans (by omega) (totalDegree_ge_two_of_colDisjoint (p := p) i j₁ j₂)
      · rcases Finset.mem_image.mp hf with ⟨i, _, rfl⟩
        by_contra hlt
        have heq :=
          eval_const_of_totalDegree_zero (by omega : (phpPigeonPoly n p i).totalDegree = 0)
            (0 : PhpVar n → ZMod p) (fun v => if v = (i, ⟨0, hn⟩) then 1 else 0)
        simp [phpPigeonPoly_def] at heq
      · rcases Finset.mem_image.mp hf with ⟨v, _, rfl⟩
        exact le_trans (by omega) (totalDegree_ge_two_of_boolPoly (p := p) v)
    have hg0 : g.1 = 0 := by
      by_contra hg_ne
      have hf_ne : f ≠ 0 := fun h0 => by
        rw [h0, MvPolynomial.totalDegree_zero] at hf_deg_pos; omega
      have hle : (g.1 * f).totalDegree ≤ 0 := hq ▸ q.totalDegree_le
      rw [MvPolynomial.totalDegree_mul_of_isDomain hg_ne hf_ne] at hle; omega
    exact Subtype.ext (by rw [hq, hg0, zero_mul]; rfl)
  rw [hbot, Submodule.mem_bot]
  intro h10
  have h1 : (1 : MvPolynomial (PhpVar n) (ZMod p)) = 0 := by
    simpa [PolyBoundedDeg.coe_one] using congrArg Subtype.val h10
  exact one_ne_zero h1

/-- Unconditional degree-$1$ base case: for $n \ge 1$ and prime $p$, $1 \notin V(n, 1)$. -/
theorem one_notMem_phpIdealSpan_one {n p : ℕ} [Fact p.Prime] (hn : 1 ≤ n) :
    PolyBoundedDeg.one (PhpVar n) p 1 ∉ phpIdealSpan n p 1 := by
  let j₀ : Fin n := ⟨0, hn⟩
  let L : PhpPolySpace n p 1 →ₗ[ZMod p] ZMod p :=
    (MvPolynomial.lcoeff (ZMod p) 0 +
        ∑ i : Fin (n + 1), MvPolynomial.lcoeff (ZMod p) (Finsupp.single (i, j₀) 1)).comp
      (MvPolynomial.restrictTotalDegree (PhpVar n) (ZMod p) 1).subtype
  have hL_apply : ∀ q : PhpPolySpace n p 1,
      L q = q.1.coeff 0 + ∑ i : Fin (n + 1), q.1.coeff (Finsupp.single (i, j₀) 1) :=
    fun q => by simp [L]
  have hL_one : L (PolyBoundedDeg.one (PhpVar n) p 1) = 1 := by
    rw [hL_apply, PolyBoundedDeg.coe_one]
    have hsum0 : (∑ i : Fin (n + 1), (1 : MvPolynomial (PhpVar n) (ZMod p)).coeff
        (Finsupp.single (i, j₀) 1)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [MvPolynomial.coeff_one, ite_eq_right]
        exact fun h0 => by have := Finsupp.ext_iff.mp h0 (i, j₀); simp at this
    rw [MvPolynomial.coeff_one, ite_eq_left rfl, hsum0, add_zero]
  have hL_van : ∀ q ∈ phpIdealSpan n p 1, L q = 0 := by
    rw [vanishes_phpIdealSpan_iff]
    intro f hf g hdeg
    by_cases hg0 : g.1 = 0
    · exact (congrArg L (Subtype.ext (by simp [hg0]) : _ = (0 : PhpPolySpace n p 1))).trans
        (map_zero L)
    · simp only [negPhpSet_def, Finset.mem_coe, negPhpFinset_def, Finset.mem_union] at hf
      rcases hf with ((hf | hf) | hf) | hf
      · rcases Finset.mem_image.mp hf with ⟨⟨⟨i₁, i₂⟩, j⟩, _, rfl⟩
        exact absurd (mul_totalDegree_ge_two (totalDegree_ge_two_of_rowDisjoint i₁ i₂ j) hg0)
          (by dsimp only at hdeg; omega)
      · rcases Finset.mem_image.mp hf with ⟨⟨i, ⟨j₁, j₂⟩⟩, _, rfl⟩
        exact absurd (mul_totalDegree_ge_two (totalDegree_ge_two_of_colDisjoint i j₁ j₂) hg0)
          (by dsimp only at hdeg; omega)
      · rcases Finset.mem_image.mp hf with ⟨i₀, _, rfl⟩
        have hfp_ne : phpPigeonPoly n p i₀ ≠ 0 := fun h0 => by
          have hev := congrArg (MvPolynomial.eval (0 : PhpVar n → ZMod p)) h0
          simp [phpPigeonPoly_def] at hev
        have hfp_pos : 1 ≤ (phpPigeonPoly n p i₀).totalDegree := by
          by_contra hlt
          have heq := eval_const_of_totalDegree_zero
            (by omega : (phpPigeonPoly n p i₀).totalDegree = 0)
            (0 : PhpVar n → ZMod p) (fun v => if v = (i₀, j₀) then 1 else 0)
          simp [phpPigeonPoly_def] at heq
        have hg_deg0 : g.1.totalDegree = 0 := by
          rw [MvPolynomial.totalDegree_mul_of_isDomain hfp_ne hg0] at hdeg; omega
        rw [hL_apply]
        change (phpPigeonPoly n p i₀ * g.1).coeff 0 +
            ∑ i : Fin (n + 1), (phpPigeonPoly n p i₀ * g.1).coeff
              (Finsupp.single (i, j₀) 1) = 0
        rw [eq_C_of_totalDegree_zero hg_deg0, mul_comm, MvPolynomial.C_mul']
        simp only [MvPolynomial.coeff_smul, smul_eq_mul, ← Finset.mul_sum]
        have h0_coeff : (phpPigeonPoly n p i₀).coeff 0 = 1 := by
          rw [phpPigeonPoly_def, MvPolynomial.coeff_sub, MvPolynomial.coeff_one, ite_eq_left rfl,
            MvPolynomial.coeff_sum, Finset.sum_eq_zero fun x _ => by
              rw [MvPolynomial.coeff_X, ite_eq_right]
              exact fun h0 => by have := Finsupp.ext_iff.mp h0 (i₀, x); simp at this, sub_zero]
        have hsum_coeff :
            (∑ i : Fin (n + 1), (phpPigeonPoly n p i₀).coeff (Finsupp.single (i, j₀) 1)) = -1 := by
          have hterm : ∀ i : Fin (n + 1),
              (phpPigeonPoly n p i₀).coeff (Finsupp.single (i, j₀) 1) =
                if i = i₀ then -1 else 0 := fun i => by
            rw [phpPigeonPoly_def, MvPolynomial.coeff_sub, MvPolynomial.coeff_one,
              ite_eq_right (fun h => by have := Finsupp.ext_iff.mp h.symm (i, j₀); simp at this),
              zero_sub, MvPolynomial.coeff_sum]
            by_cases hi : i = i₀
            · subst hi
              rw [ite_eq_left rfl, neg_inj, Finset.sum_eq_single j₀]
              · simp [MvPolynomial.coeff_X]
              · intro j _ hj
                rw [MvPolynomial.coeff_X, ite_eq_right]
                exact fun heq => by have := Finsupp.ext_iff.mp heq (i, j); simp [hj] at this
              · exact fun hj₀ => False.elim (hj₀ (Finset.mem_univ j₀))
            · rw [ite_eq_right hi, neg_eq_zero]
              exact Finset.sum_eq_zero fun j _ => by
                rw [MvPolynomial.coeff_X, ite_eq_right]
                exact fun heq => by
                  have := Finsupp.ext_iff.mp heq (i₀, j); simp [Ne.symm hi] at this
          simp [hterm]
        rw [h0_coeff, hsum_coeff]; ring
      · rcases Finset.mem_image.mp hf with ⟨v, _, rfl⟩
        exact absurd (mul_totalDegree_ge_two (totalDegree_ge_two_of_boolPoly v) hg0) (by omega)
  exact fun hmem => one_ne_zero (hL_one.symm.trans (hL_van _ hmem))

/-- Sharpness of the degree bound $d \le n / 2$: when $n = 1$ and $d = 2$ (violating $2 d \le n$),
the unit $1$ belongs to $V(1, 2)$ over $\mathbb{F}_p$ via the identity
$1 = (1 - x_{0, 0}) + x_{0, 0}(1 - x_{1, 0}) + x_{0, 0} x_{1, 0}$. -/
theorem one_mem_phpIdealSpan_one_two (p : ℕ) :
    PolyBoundedDeg.one (PhpVar 1) p 2 ∈ phpIdealSpan 1 p 2 := by
  let i₀ : Fin 2 := 0
  let i₁ : Fin 2 := 1
  let j₀ : Fin 1 := 0
  have hdeg_var : ∀ v : PhpVar 1,
      (MvPolynomial.X v : MvPolynomial (PhpVar 1) (ZMod p)).totalDegree ≤ 1 := by
    intro v
    rcases subsingleton_or_nontrivial (ZMod p) with _ | _
    · rw [Subsingleton.elim (MvPolynomial.X v : MvPolynomial (PhpVar 1) (ZMod p)) 0]; simp
    · exact (MvPolynomial.totalDegree_X _).le
  have hdeg_x :
      (MvPolynomial.X (i₀, j₀) : MvPolynomial (PhpVar 1) (ZMod p)).totalDegree ≤ 2 :=
    (hdeg_var (i₀, j₀)).trans (by omega)
  let gx : PhpPolySpace 1 p 2 :=
    ⟨MvPolynomial.X (i₀, j₀), (MvPolynomial.mem_restrictTotalDegree _ 2 _).mpr hdeg_x⟩
  let g1 : PhpPolySpace 1 p 2 := PolyBoundedDeg.one (PhpVar 1) p 2
  have hq0_deg : (phpPigeonPoly 1 p i₀ * g1.1).totalDegree ≤ 2 := by
    rw [PolyBoundedDeg.coe_one, mul_one, phpPigeonPoly_def, Fin.sum_univ_one]
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by simp) ((hdeg_var (i₀, 0)).trans (by omega)))
  have hq1_deg : (phpPigeonPoly 1 p i₁ * gx.1).totalDegree ≤ 2 := by
    have hgx_eq : gx.1 = MvPolynomial.X (i₀, j₀) := rfl
    rw [hgx_eq, phpPigeonPoly_def, Fin.sum_univ_one, sub_mul, one_mul]
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le hdeg_x ?_)
    have h1 := hdeg_var (i₁, 0)
    have h0 := hdeg_var (i₀, j₀)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have hrow_deg : (phpRowDisjointPoly 1 p i₀ i₁ j₀ * g1.1).totalDegree ≤ 2 := by
    rw [PolyBoundedDeg.coe_one, mul_one, phpRowDisjointPoly_def]
    have h0 := hdeg_var (i₀, j₀)
    have h1 := hdeg_var (i₁, j₀)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have hm0 := mem_phpIdealSpan_of_mul (phpPigeonPoly_mem_negPhpSet i₀) g1 hq0_deg
  have hm1 := mem_phpIdealSpan_of_mul (phpPigeonPoly_mem_negPhpSet i₁) gx hq1_deg
  have hm2 :=
    mem_phpIdealSpan_of_mul
      (phpRowDisjointPoly_mem_negPhpSet (by decide : i₀ ≠ i₁) j₀) g1 hrow_deg
  have hsum := Submodule.add_mem _ (Submodule.add_mem _ hm0 hm1) hm2
  have heq :
      (⟨phpPigeonPoly 1 p i₀ * g1.1,
          (MvPolynomial.mem_restrictTotalDegree _ 2 _).mpr hq0_deg⟩ : PhpPolySpace 1 p 2) +
        ⟨phpPigeonPoly 1 p i₁ * gx.1,
          (MvPolynomial.mem_restrictTotalDegree _ 2 _).mpr hq1_deg⟩ +
        ⟨phpRowDisjointPoly 1 p i₀ i₁ j₀ * g1.1,
          (MvPolynomial.mem_restrictTotalDegree _ 2 _).mpr hrow_deg⟩ =
        PolyBoundedDeg.one (PhpVar 1) p 2 := by
    apply Subtype.ext
    have hj0_eq : (0 : Fin 1) = j₀ := rfl
    simp only [Submodule.coe_add, PolyBoundedDeg.coe_one, g1, gx, phpPigeonPoly_def,
      phpRowDisjointPoly_def, Fin.sum_univ_one, hj0_eq]
    ring
  rwa [heq] at hsum

end SpaceAndIdeal

section FregeStepLowerBound

/-- Encoding of the polynomial system $\neg \mathrm{PHP}_n$ as depth-`≤ 2` formulas
$\Phi_{f = 0}$ in $F(\mathrm{MOD}_p)$. -/
noncomputable def negPhpFormulaSet (n p : ℕ) [Fact p.Prime] :
    Set (ModFregeFormula (PhpVar n) p) :=
  polyEqZeroFormula '' negPhpSet n p

theorem mem_negPhpFormulaSet_of_mem {n p : ℕ} [Fact p.Prime]
    {f : MvPolynomial (PhpVar n) (ZMod p)} (hf : f ∈ negPhpSet n p) :
    polyEqZeroFormula f ∈ negPhpFormulaSet n p :=
  ⟨f, hf, rfl⟩

private noncomputable def singleCollisionHole {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n) : Fin (n + 1) → Fin n := by
  classical
  let remPigeons : Finset (Fin (n + 1)) := (Finset.univ.erase i₁).erase i₂
  let remHoles : Finset (Fin n) := Finset.univ.erase j₀
  have hi₂_mem : i₂ ∈ Finset.univ.erase i₁ :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i₂⟩
  have hcard_P : remPigeons.card = n - 1 := by
    rw [Finset.card_erase_of_mem hi₂_mem, Finset.card_erase_of_mem (Finset.mem_univ i₁),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hcard_H : remHoles.card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
  have heq_card : Fintype.card remPigeons = Fintype.card remHoles := by
    rw [Fintype.card_coe, Fintype.card_coe, hcard_P, hcard_H]
  let e : remPigeons ≃ remHoles := Fintype.equivOfCardEq heq_card
  exact fun i =>
    if h1 : i = i₁ then j₀
    else if h2 : i = i₂ then j₀
    else (e ⟨i, Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ i⟩⟩⟩).1

private theorem singleCollisionHole_first {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n) :
    singleCollisionHole hn hne j₀ i₁ = j₀ := by
  simp [singleCollisionHole]

private theorem singleCollisionHole_second {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n) :
    singleCollisionHole hn hne j₀ i₂ = j₀ := by
  simp [singleCollisionHole, hne.symm]

private theorem singleCollisionHole_ne_of_ne {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ a : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n)
    (ha1 : a ≠ i₁) (ha2 : a ≠ i₂) :
    singleCollisionHole hn hne j₀ a ≠ j₀ := by
  dsimp only [singleCollisionHole]
  rw [dite_eq_right ha1, dite_eq_right ha2]
  exact (Finset.mem_erase.mp (Subtype.prop _)).1

private theorem singleCollisionHole_inj_of_ne {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ a b : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n)
    (ha1 : a ≠ i₁) (ha2 : a ≠ i₂) (hb1 : b ≠ i₁) (hb2 : b ≠ i₂)
    (heq : singleCollisionHole hn hne j₀ a = singleCollisionHole hn hne j₀ b) :
    a = b := by
  dsimp only [singleCollisionHole] at heq
  rw [dite_eq_right ha1, dite_eq_right ha2, dite_eq_right hb1, dite_eq_right hb2] at heq
  exact congrArg Subtype.val (Equiv.injective _ (Subtype.ext heq))

private noncomputable def singleCollisionAssign {n : ℕ} (hn : 1 ≤ n)
    {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n) (v : PhpVar n) : Bool :=
  decide (v.2 = singleCollisionHole hn hne j₀ v.1)

private theorem eval_singleCollisionAssign_row {n p : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n) :
    (polyEqZeroFormula (phpRowDisjointPoly n p i₁ i₂ j₀)).evalBool
      (singleCollisionAssign hn hne j₀) = false := by
  rw [Bool.eq_false_iff, ne_eq, evalBool_polyEqZeroFormula_iff]
  simp [phpRowDisjointPoly_def, singleCollisionAssign,
    singleCollisionHole_first hn hne j₀, singleCollisionHole_second hn hne j₀]

private theorem eval_singleCollisionAssign_other {n p : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    {i₁ i₂ : Fin (n + 1)} (hne : i₁ ≠ i₂) (j₀ : Fin n)
    {f : MvPolynomial (PhpVar n) (ZMod p)} (hf : f ∈ negPhpSet n p)
    (hf_ne : f ≠ phpRowDisjointPoly n p i₁ i₂ j₀) :
    (polyEqZeroFormula f).evalBool (singleCollisionAssign hn hne j₀) = true := by
  rw [evalBool_polyEqZeroFormula_iff]
  let hfn := singleCollisionHole hn hne j₀
  let αZ : PhpVar n → ZMod p := fun v => boolToZMod p (singleCollisionAssign hn hne j₀ v)
  have hαZ : ∀ i j, αZ (i, j) = if j = hfn i then 1 else 0 := by
    intro i j
    change boolToZMod p (decide (j = hfn i)) = if j = hfn i then 1 else 0
    by_cases h : j = hfn i <;> simp [h]
  change MvPolynomial.eval αZ f = 0
  simp only [negPhpSet_def, Finset.mem_coe, negPhpFinset_def, Finset.mem_union] at hf
  rcases hf with ((hf | hf) | hf) | hf
  · rcases Finset.mem_image.mp hf with ⟨⟨⟨a, b⟩, j⟩, hab, rfl⟩
    dsimp only at hf_ne ⊢
    have hab_ne : a ≠ b := (Finset.mem_filter.mp hab).2
    rw [phpRowDisjointPoly_def, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
      hαZ a j, hαZ b j]
    by_cases hja : j = hfn a
    · by_cases hjb : j = hfn b
      · exfalso
        apply hf_ne
        by_cases ha1 : a = i₁
        · have hj_eq : j = j₀ := hja.trans (ha1 ▸ singleCollisionHole_first hn hne j₀)
          by_cases hb2 : b = i₂
          · rw [ha1, hb2, hj_eq]
          · have hb1 : b ≠ i₁ := ha1 ▸ hab_ne.symm
            exact False.elim
              (singleCollisionHole_ne_of_ne hn hne j₀ hb1 hb2 (hjb.symm.trans hj_eq))
        · by_cases ha2 : a = i₂
          · have hj_eq : j = j₀ := hja.trans (ha2 ▸ singleCollisionHole_second hn hne j₀)
            by_cases hb1 : b = i₁
            · rw [ha2, hb1, hj_eq, phpRowDisjointPoly_def, phpRowDisjointPoly_def, mul_comm]
            · have hb2 : b ≠ i₂ := ha2 ▸ hab_ne.symm
              exact False.elim
                (singleCollisionHole_ne_of_ne hn hne j₀ hb1 hb2 (hjb.symm.trans hj_eq))
          · have ha_ne_j0 : hfn a ≠ j₀ := singleCollisionHole_ne_of_ne hn hne j₀ ha1 ha2
            have hb1 : b ≠ i₁ := fun h =>
              ha_ne_j0 (hja.symm.trans (hjb.trans (h ▸ singleCollisionHole_first hn hne j₀)))
            have hb2 : b ≠ i₂ := fun h =>
              ha_ne_j0 (hja.symm.trans (hjb.trans (h ▸ singleCollisionHole_second hn hne j₀)))
            exact False.elim
              (hab_ne (singleCollisionHole_inj_of_ne hn hne j₀ ha1 ha2 hb1 hb2
                (hja.symm.trans hjb)))
      · simp [hjb]
    · simp [hja]
  · rcases Finset.mem_image.mp hf with ⟨⟨i, ⟨j₁, j₂⟩⟩, hj12, rfl⟩
    have hj_ne : j₁ ≠ j₂ := (Finset.mem_filter.mp hj12).2
    rw [phpColDisjointPoly_def, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
      hαZ i j₁, hαZ i j₂]
    by_cases hj1 : j₁ = hfn i
    · subst hj1; simp [Ne.symm hj_ne]
    · simp [hj1]
  · rcases Finset.mem_image.mp hf with ⟨i, _, rfl⟩
    rw [phpPigeonPoly_def, map_sub, map_one, map_sum]
    simp_rw [MvPolynomial.eval_X, hαZ i]
    simp
  · rcases Finset.mem_image.mp hf with ⟨⟨i, j⟩, _, rfl⟩
    rw [phpBoolPoly_def, map_sub, map_pow, MvPolynomial.eval_X, hαZ i j]
    by_cases hj : j = hfn i <;> simp [hj]

/-- Every $F_\ell(\mathrm{MOD}_p)$-refutation of $\neg \mathrm{PHP}_n$ ($n \ge 1$) must explicitly
include all $\binom{n+1}{2} n$ collision formulas $\Phi_{Q_{i_1, i_2; j} = 0}$ ($i_1 < i_2$) plus
the terminal $\bot$ line, hence satisfies $n^2 (n + 1) + 2 \le 2 k$. -/
theorem n_sq_mul_succ_add_two_le_two_mul_length_of_phpRefutation
    {n p ℓ : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    {F : ModFregeFormula.FregeCalculus p}
    (D : ModFregeFormula.FregeDerivation F (negPhpFormulaSet n p) ℓ)
    (href : D.isRefutation) :
    n ^ 2 * (n + 1) + 2 ≤ 2 * D.length := by
  classical
  let pairs : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter fun q => q.1 < q.2
  let S_idx : Finset ((Fin (n + 1) × Fin (n + 1)) × Fin n) :=
    pairs ×ˢ Finset.univ
  have h2pairs : 2 * pairs.card = (n + 1) * n := by
    let pairsGt : Finset (Fin (n + 1) × Fin (n + 1)) :=
      Finset.univ.filter fun q => q.2 < q.1
    let diag : Finset (Fin (n + 1) × Fin (n + 1)) :=
      Finset.univ.filter fun q => q.1 = q.2
    have hbij_gt : pairsGt.card = pairs.card := by
      refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
      · intro q hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
      · intro q₁ _ q₂ _ h
        exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
      · intro q hq
        exact ⟨(q.2, q.1),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩, rfl⟩
    have hdiag : diag.card = n + 1 := by
      have h_img : diag = (Finset.univ : Finset (Fin (n + 1))).image (fun i => (i, i)) := by
        ext ⟨a, b⟩; simp [diag, eq_comm]
      rw [h_img, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
        Finset.card_univ, Fintype.card_fin]
    have hdisj1 : Disjoint pairs pairsGt := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hdisj2 : Disjoint (pairs ∪ pairsGt) diag := by
      rw [Finset.disjoint_left]
      intro q h12 hd
      have heq := (Finset.mem_filter.mp hd).2
      rcases Finset.mem_union.mp h12 with h1 | h2
      · exact (ne_of_lt (Finset.mem_filter.mp h1).2) heq
      · exact (ne_of_gt (Finset.mem_filter.mp h2).2) heq
    have huniv : pairs ∪ pairsGt ∪ diag = Finset.univ := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
        pairs, pairsGt, diag]
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact Or.inl (Or.inl hlt)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr hgt)
    have htot : (pairs ∪ pairsGt ∪ diag).card = (n + 1) * (n + 1) := by
      rw [huniv, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      hbij_gt, hdiag] at htot
    have hsq : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
    omega
  let φMap : ((Fin (n + 1) × Fin (n + 1)) × Fin n) → ModFregeFormula (PhpVar n) p :=
    fun t => polyEqZeroFormula (phpRowDisjointPoly n p t.1.1 t.1.2 t.2)
  have hmem_steps : ∀ t ∈ S_idx, φMap t ∈ D.steps := by
    intro t ht
    have hlt : t.1.1 < t.1.2 := (Finset.mem_filter.mp (Finset.mem_product.mp ht).1).2
    have hne : t.1.1 ≠ t.1.2 := ne_of_lt hlt
    obtain ⟨ψ, hψ_hyp, hψ_step, hψ_false⟩ :=
      D.exists_step_hyp_evalBool_false_of_isRefutation href (singleCollisionAssign hn hne t.2)
    rcases hψ_hyp with ⟨f, hf, rfl⟩
    by_cases hfeq : f = phpRowDisjointPoly n p t.1.1 t.1.2 t.2
    · subst hfeq; exact hψ_step
    · have htrue := eval_singleCollisionAssign_other (p := p) hn hne t.2 hf hfeq
      rw [htrue] at hψ_false
      exact False.elim (Bool.false_ne_true hψ_false.symm)
  have hinj_on : Set.InjOn φMap ↑S_idx := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hlt₁ : t₁.1.1 < t₁.1.2 := (Finset.mem_filter.mp (Finset.mem_product.mp ht₁).1).2
    have hne₁ : t₁.1.1 ≠ t₁.1.2 := ne_of_lt hlt₁
    have hlt₂ : t₂.1.1 < t₂.1.2 := (Finset.mem_filter.mp (Finset.mem_product.mp ht₂).1).2
    have hne₂ : t₂.1.1 ≠ t₂.1.2 := ne_of_lt hlt₂
    by_contra hne_t
    have hf_ne :
        phpRowDisjointPoly n p t₂.1.1 t₂.1.2 t₂.2 ≠
          phpRowDisjointPoly n p t₁.1.1 t₁.1.2 t₁.2 := by
      intro hpoly_eq
      let β : PhpVar n → ZMod p :=
        fun v => if v = (t₁.1.1, t₁.2) ∨ v = (t₁.1.2, t₁.2) then 1 else 0
      have hev1 : MvPolynomial.eval β (phpRowDisjointPoly n p t₁.1.1 t₁.1.2 t₁.2) = 1 := by
        simp [phpRowDisjointPoly_def, β]
      have hev2 := congrArg (MvPolynomial.eval β) hpoly_eq
      rw [hev1, phpRowDisjointPoly_def, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X] at hev2
      have hv1 : (t₂.1.1, t₂.2) = (t₁.1.1, t₁.2) ∨ (t₂.1.1, t₂.2) = (t₁.1.2, t₁.2) := by
        by_contra hnot
        have h0 : β (t₂.1.1, t₂.2) = 0 := ite_eq_right hnot
        rw [h0, zero_mul] at hev2
        exact one_ne_zero hev2.symm
      have hv2 : (t₂.1.2, t₂.2) = (t₁.1.1, t₁.2) ∨ (t₂.1.2, t₂.2) = (t₁.1.2, t₁.2) := by
        by_contra hnot
        have h0 : β (t₂.1.2, t₂.2) = 0 := ite_eq_right hnot
        rw [h0, mul_zero] at hev2
        exact one_ne_zero hev2.symm
      rcases hv1 with h11 | h12 <;> rcases hv2 with h21 | h22
      · exact hne₂ ((Prod.mk.inj h11).1.trans (Prod.mk.inj h21).1.symm)
      · exact hne_t
          (Prod.ext (Prod.ext (Prod.mk.inj h11).1.symm (Prod.mk.inj h22).1.symm)
            (Prod.mk.inj h11).2.symm)
      · have ha : t₂.1.1 = t₁.1.2 := (Prod.mk.inj h12).1
        have hb : t₂.1.2 = t₁.1.1 := (Prod.mk.inj h21).1
        rw [ha, hb] at hlt₂
        exact lt_asymm hlt₁ hlt₂
      · exact hne₂ ((Prod.mk.inj h12).1.trans (Prod.mk.inj h22).1.symm)
    have hfalse := eval_singleCollisionAssign_row (p := p) hn hne₁ t₁.2
    have htrue :=
      eval_singleCollisionAssign_other (p := p) hn hne₁ t₁.2
        (phpRowDisjointPoly_mem_negPhpSet hne₂ t₂.2) hf_ne
    change (φMap t₁).evalBool _ = false at hfalse
    change (φMap t₂).evalBool _ = true at htrue
    rw [heq, htrue] at hfalse
    exact Bool.false_ne_true hfalse.symm
  have hsub :
      insert (ModFregeFormula.const false) (S_idx.image φMap) ⊆ D.steps.toFinset := by
    intro ψ hψ
    rw [List.mem_toFinset]
    rcases Finset.mem_insert.mp hψ with rfl | himg
    · rw [← href]
      exact List.getLast_mem D.nonempty_steps
    · rcases Finset.mem_image.mp himg with ⟨t, ht, rfl⟩
      exact hmem_steps t ht
  have hnot_mem_img : ModFregeFormula.const false ∉ S_idx.image φMap := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨t, _, heq⟩
    have hev := congrArg (ModFregeFormula.evalBool (fun _ : PhpVar n => false)) heq
    have htrue : (φMap t).evalBool (fun _ => false) = true :=
      (evalBool_polyEqZeroFormula_iff _ _).mpr (by simp [phpRowDisjointPoly_def])
    rw [htrue, ModFregeFormula.evalBool_const] at hev
    exact Bool.false_ne_true hev.symm
  have hcard_le : (S_idx.image φMap).card + 1 ≤ D.length := by
    calc
      (S_idx.image φMap).card + 1 =
          (insert (ModFregeFormula.const false) (S_idx.image φMap)).card :=
        (Finset.card_insert_of_notMem hnot_mem_img).symm
      _ ≤ D.steps.toFinset.card := Finset.card_le_card hsub
      _ ≤ D.steps.length := List.toFinset_card_le D.steps
      _ = D.length := rfl
  rw [Finset.card_image_of_injOn hinj_on] at hcard_le
  have hS_card : 2 * S_idx.card = n ^ 2 * (n + 1) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, ← Nat.mul_assoc, h2pairs]
    ring
  omega

/-- Cubic step-count lower bound for $F_\ell(\mathrm{MOD}_p)$-refutations of $\neg \mathrm{PHP}_n$:
for every $n \ge 1$, every refutation $D$ satisfies $n^3 < 2 \cdot D.\mathrm{length}$ (i.e.
$k > n^3 / 2$). -/
theorem n_cube_lt_two_mul_length_of_phpRefutation
    {n p ℓ : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    {F : ModFregeFormula.FregeCalculus p}
    (D : ModFregeFormula.FregeDerivation F (negPhpFormulaSet n p) ℓ)
    (href : D.isRefutation) :
    n ^ 3 < 2 * D.length := by
  have h := n_sq_mul_succ_add_two_le_two_mul_length_of_phpRefutation hn D href
  have hcube : n ^ 3 < n ^ 2 * (n + 1) + 2 := by
    calc
      n ^ 3 < n ^ 3 + (n ^ 2 + 2) := by omega
      _ = n ^ 2 * (n + 1) + 2 := by ring
  exact lt_of_lt_of_le hcube h

end FregeStepLowerBound

end CslibFrontier.Logic.PL.ENS
