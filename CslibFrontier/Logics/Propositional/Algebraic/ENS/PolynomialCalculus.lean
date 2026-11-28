/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.ENS.Pigeonhole

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Degree-Bounded Polynomial Calculus and Linear-Design Duality

This module formalizes degree-bounded Polynomial Calculus derivability (`PCDerivable`) over
$\mathbb{F}_p^{\le d}[V]$, its $\mathbb{F}_p$-submodule structure, closure under degree-bounded
polynomial multiplication over prime fields, unconditional inclusion of the truncated pigeonhole
ideal span $V(n, d) \subseteq \mathrm{PC}_d(\neg \mathrm{PHP}_n)$, and quotient-duality
characterization of linear designs on $\mathbb{F}_p^{\le d}[V]$, verified under standard Lean
axioms.

## Main definitions

- `CslibFrontier.Logic.PL.ENS.PCDerivable`, `CslibFrontier.Logic.PL.ENS.pcSubmodule`: degree-`≤ d`
  Polynomial Calculus derivability from a polynomial system $F \subseteq \mathbb{F}_p[V]$ and its
  $\mathbb{F}_p$-linear subspace inside `PolyBoundedDeg V p d`.

## Main results

- `CslibFrontier.Logic.PL.ENS.PCDerivable.mul_poly`: unconditional closure of `PCDerivable` under
  arbitrary degree-`≤ d` polynomial multiplication over prime fields $\mathbb{F}_p$.
- `CslibFrontier.Logic.PL.ENS.pcDerivable_of_mem_phpIdealSpan`: unconditional inclusion
  $V(n, d) \subseteq \mathrm{PC}_d(\neg \mathrm{PHP}_n)$.
- `CslibFrontier.Logic.PL.ENS.exists_linearMap_one_eq_one_vanishes_iff`: duality equivalence
  between linear functionals satisfying $L(1) = 1$ and $L|_W = 0$ and unit non-membership
  $1 \notin W$.
-/

public section

namespace CslibFrontier.Logic.PL.ENS

section PolynomialCalculus

/-- Degree-`≤ d` Polynomial Calculus derivability over $\mathbb{F}_p$ from an axiom set
$F \subseteq \mathbb{F}_p[V]$: closure inside `PolyBoundedDeg V p d` under initial axioms of
degree at most `d`, `0`, addition, scalar multiplication, and multiplication by single variables
preserving total degree `≤ d`. -/
inductive PCDerivable {V : Type*} {p : ℕ}
    (F : Set (MvPolynomial V (ZMod p))) (d : ℕ) : PolyBoundedDeg V p d → Prop where
  | axiom_mem {f : MvPolynomial V (ZMod p)} (hf : f ∈ F) (hdeg : f.totalDegree ≤ d) :
      PCDerivable F d ⟨f, (MvPolynomial.mem_restrictTotalDegree V d f).mpr hdeg⟩
  | zero : PCDerivable F d 0
  | add {g₁ g₂ : PolyBoundedDeg V p d} :
      PCDerivable F d g₁ → PCDerivable F d g₂ → PCDerivable F d (g₁ + g₂)
  | smul (c : ZMod p) {g : PolyBoundedDeg V p d} :
      PCDerivable F d g → PCDerivable F d (c • g)
  | mul_var {g : PolyBoundedDeg V p d} (v : V) (hg : PCDerivable F d g)
      (hdeg : (g.1 * MvPolynomial.X v).totalDegree ≤ d) :
      PCDerivable F d
        ⟨g.1 * MvPolynomial.X v,
          (MvPolynomial.mem_restrictTotalDegree V d (g.1 * MvPolynomial.X v)).mpr hdeg⟩

@[simp]
theorem PCDerivable.zero_mem {V : Type*} {p : ℕ}
    (F : Set (MvPolynomial V (ZMod p))) (d : ℕ) :
    PCDerivable F d 0 :=
  PCDerivable.zero

theorem PCDerivable.neg {V : Type*} {p : ℕ} {F : Set (MvPolynomial V (ZMod p))} {d : ℕ}
    {g : PolyBoundedDeg V p d} (hg : PCDerivable F d g) :
    PCDerivable F d (-g) := by
  have hEq : (-1 : ZMod p) • g = -g := by
    apply Subtype.ext
    change (-1 : ZMod p) • g.1 = -g.1
    rw [neg_one_smul]
  exact hEq ▸ PCDerivable.smul (-1 : ZMod p) hg

theorem PCDerivable.sub {V : Type*} {p : ℕ} {F : Set (MvPolynomial V (ZMod p))} {d : ℕ}
    {g₁ g₂ : PolyBoundedDeg V p d} (hg₁ : PCDerivable F d g₁) (hg₂ : PCDerivable F d g₂) :
    PCDerivable F d (g₁ - g₂) := by
  rw [sub_eq_add_neg]
  exact PCDerivable.add hg₁ hg₂.neg

/-- The $\mathbb{F}_p$-subspace of `PolyBoundedDeg V p d` consisting of polynomials derivable from
`F` in degree-`≤ d` Polynomial Calculus. -/
def pcSubmodule {V : Type*} {p : ℕ}
    (F : Set (MvPolynomial V (ZMod p))) (d : ℕ) : Submodule (ZMod p) (PolyBoundedDeg V p d) where
  carrier := { q | PCDerivable F d q }
  zero_mem' := PCDerivable.zero
  add_mem' ha hb := PCDerivable.add ha hb
  smul_mem' c _ hx := PCDerivable.smul c hx

theorem pcSubmodule_def {V : Type*} {p : ℕ}
    (F : Set (MvPolynomial V (ZMod p))) (d : ℕ) :
    pcSubmodule F d =
      { carrier := { q | PCDerivable F d q }
        zero_mem' := PCDerivable.zero
        add_mem' := fun ha hb => PCDerivable.add ha hb
        smul_mem' := fun c _ hx => PCDerivable.smul c hx } := by
  unfold pcSubmodule; rfl

@[simp]
theorem mem_pcSubmodule_iff {V : Type*} {p : ℕ}
    {F : Set (MvPolynomial V (ZMod p))} {d : ℕ} {q : PolyBoundedDeg V p d} :
    q ∈ pcSubmodule F d ↔ PCDerivable F d q :=
  Iff.rfl

private theorem totalDegree_X_le_one {V : Type*} (p : ℕ) (v : V) :
    (MvPolynomial.X v : MvPolynomial V (ZMod p)).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial (ZMod p) with _ | _
  · rw [Subsingleton.elim (MvPolynomial.X v : MvPolynomial V (ZMod p)) 0]
    simp
  · exact (MvPolynomial.totalDegree_X v).le

private theorem totalDegree_monomial_le {V : Type*} {p : ℕ} (m : V →₀ ℕ) (c : ZMod p) :
    (MvPolynomial.monomial m c : MvPolynomial V (ZMod p)).totalDegree ≤ m.sum fun _ e => e := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun s hs => ?_
  have hsm : s = m := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
  rw [hsm]

private theorem pcDerivable_mul_X_pow {V : Type*} {p d : ℕ}
    {F : Set (MvPolynomial V (ZMod p))} {g : PolyBoundedDeg V p d}
    (hg : PCDerivable F d g) (v : V) :
    ∀ (k : ℕ) (hdeg : g.1.totalDegree + k ≤ d),
      PCDerivable F d
        ⟨g.1 * MvPolynomial.X v ^ k,
          (MvPolynomial.mem_restrictTotalDegree V d (g.1 * MvPolynomial.X v ^ k)).mpr
            ((MvPolynomial.totalDegree_mul _ _).trans
              (by
                rw [MvPolynomial.X_pow_eq_monomial]
                have hm := totalDegree_monomial_le (p := p) (Finsupp.single v k) 1
                rw [Finsupp.sum_single_index rfl] at hm
                omega))⟩
  | 0, _ => by convert hg using 1; ext; simp
  | k + 1, hdeg => by
    have ih := pcDerivable_mul_X_pow hg v k (by omega)
    have hstep_deg : ((g.1 * MvPolynomial.X v ^ k) * MvPolynomial.X v).totalDegree ≤ d := by
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 : (g.1 * MvPolynomial.X v ^ k).totalDegree ≤ g.1.totalDegree + k := by
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.X_pow_eq_monomial]
        have hm := totalDegree_monomial_le (p := p) (Finsupp.single v k) 1
        rw [Finsupp.sum_single_index rfl] at hm; omega
      have h2 := totalDegree_X_le_one p v; omega
    convert PCDerivable.mul_var v ih hstep_deg using 1; ext; simp [pow_succ, mul_assoc]

private theorem pcDerivable_mul_monomial_one {V : Type*} {p d : ℕ}
    {F : Set (MvPolynomial V (ZMod p))} {g : PolyBoundedDeg V p d}
    (hg : PCDerivable F d g) (m : V →₀ ℕ)
    (hdeg : g.1.totalDegree + (m.sum fun _ e => e) ≤ d) :
    PCDerivable F d
      ⟨g.1 * MvPolynomial.monomial m 1,
        (MvPolynomial.mem_restrictTotalDegree V d (g.1 * MvPolynomial.monomial m 1)).mpr
          ((MvPolynomial.totalDegree_mul _ _).trans
            ((Nat.add_le_add_left (totalDegree_monomial_le m 1) _).trans hdeg))⟩ := by
  classical
  induction m using Finsupp.induction with
  | zero => convert hg using 1; ext; simp
  | single_add v k m' _ _ ih =>
    have hsum :
        ((Finsupp.single v k + m').sum fun _ e => e) = k + (m'.sum fun _ e => e) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [hsum] at hdeg
    have ihm := ih (by omega)
    have hgm_deg : (g.1 * MvPolynomial.monomial m' 1).totalDegree + k ≤ d := by
      have hle : (g.1 * MvPolynomial.monomial m' 1).totalDegree ≤
          g.1.totalDegree + (m'.sum fun _ e => e) :=
        (MvPolynomial.totalDegree_mul _ _).trans
          (Nat.add_le_add_left (totalDegree_monomial_le m' 1) _)
      omega
    convert pcDerivable_mul_X_pow ihm v k hgm_deg using 1
    ext; simp [MvPolynomial.X_pow_eq_monomial, mul_assoc, add_comm]

/-- Over a prime field $\mathbb{F}_p$, if $g \in \mathbb{F}_p^{\le d}[V]$ is derivable in
degree-`≤ d` Polynomial Calculus and $\deg(g \cdot h) \le d$, then $g \cdot h$ is also derivable in
degree-`≤ d` Polynomial Calculus. -/
theorem PCDerivable.mul_poly {V : Type*} {p d : ℕ} [Fact p.Prime]
    {F : Set (MvPolynomial V (ZMod p))} {g : PolyBoundedDeg V p d}
    (hg : PCDerivable F d g) (h : MvPolynomial V (ZMod p))
    (hdeg : (g.1 * h).totalDegree ≤ d) :
    PCDerivable F d
      ⟨g.1 * h, (MvPolynomial.mem_restrictTotalDegree V d (g.1 * h)).mpr hdeg⟩ := by
  classical
  by_cases hg0 : g.1 = 0
  · convert PCDerivable.zero (F := F) (d := d) using 1; ext; simp [hg0]
  by_cases hh0 : h = 0
  · convert PCDerivable.zero (F := F) (d := d) using 1; ext; simp [hh0]
  have hsum_deg : g.1.totalDegree + h.totalDegree ≤ d := by
    rwa [← MvPolynomial.totalDegree_mul_of_isDomain hg0 hh0]
  have hmem_term :
      ∀ m ∈ h.support,
        ∃ hm : (g.1 * MvPolynomial.monomial m 1).totalDegree ≤ d,
          PCDerivable F d
            ⟨g.1 * MvPolynomial.monomial m 1,
              (MvPolynomial.mem_restrictTotalDegree V d _).mpr hm⟩ := by
    intro m hm
    have hm_le : (m.sum fun _ e => e) ≤ h.totalDegree :=
      Finset.le_sup (f := fun s : V →₀ ℕ => s.sum fun _ e => e) hm
    have hgm : g.1.totalDegree + (m.sum fun _ e => e) ≤ d := by omega
    exact ⟨(MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add_left (totalDegree_monomial_le m 1) _).trans hgm),
      pcDerivable_mul_monomial_one hg m hgm⟩
  rw [← mem_pcSubmodule_iff]
  have hdecomp :
      (⟨g.1 * h, (MvPolynomial.mem_restrictTotalDegree V d (g.1 * h)).mpr hdeg⟩ :
        PolyBoundedDeg V p d) =
        ∑ m ∈ h.support.attach,
          (h.coeff m.1) •
            (⟨g.1 * MvPolynomial.monomial m.1 1,
                (MvPolynomial.mem_restrictTotalDegree V d _).mpr (hmem_term m.1 m.2).1⟩ :
              PolyBoundedDeg V p d) := by
    apply Subtype.ext; rw [Submodule.coe_sum]; change g.1 * h = _
    conv_lhs => rw [h.as_sum, Finset.mul_sum]
    rw [← Finset.sum_attach h.support (fun m => g.1 * MvPolynomial.monomial m (h.coeff m))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [SetLike.val_smul]
    calc
      g.1 * MvPolynomial.monomial m.1 (h.coeff m.1) =
          g.1 * (h.coeff m.1 • MvPolynomial.monomial m.1 1) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      _ = h.coeff m.1 • (g.1 * MvPolynomial.monomial m.1 1) := by rw [mul_smul_comm]
  rw [hdecomp]
  exact Submodule.sum_mem (pcSubmodule F d) fun m _ =>
    Submodule.smul_mem (pcSubmodule F d) (h.coeff m.1) (hmem_term m.1 m.2).2

/-- Every element of the truncated Nullstellensatz span $V(n, d)$ is derivable in degree-`≤ d`
Polynomial Calculus from $\neg \mathrm{PHP}_n$ over $\mathbb{F}_p$. -/
theorem pcDerivable_of_mem_phpIdealSpan {n p d : ℕ} [Fact p.Prime]
    {q : PhpPolySpace n p d} (hq : q ∈ phpIdealSpan n p d) :
    PCDerivable (negPhpSet n p) d q := by
  rw [phpIdealSpan_def] at hq
  rw [← mem_pcSubmodule_iff]
  refine Submodule.span_le.mpr ?_ hq
  rintro x ⟨f, hf, g, hxeq⟩
  change PCDerivable (negPhpSet n p) d x
  by_cases hf0 : f = 0
  · convert PCDerivable.zero (F := negPhpSet n p) (d := d) using 1; ext; simp [hxeq, hf0]
  by_cases hg0 : g.1 = 0
  · convert PCDerivable.zero (F := negPhpSet n p) (d := d) using 1; ext; simp [hxeq, hg0]
  have hprod_deg : (f * g.1).totalDegree ≤ d := by rw [mul_comm, ← hxeq]; exact x.totalDegree_le
  have hf_deg : f.totalDegree ≤ d := by
    have hadd : f.totalDegree + g.1.totalDegree ≤ d := by
      rwa [← MvPolynomial.totalDegree_mul_of_isDomain hf0 hg0]
    omega
  convert (PCDerivable.axiom_mem hf hf_deg).mul_poly g.1 hprod_deg using 1
  exact Subtype.ext (hxeq.trans (mul_comm g.1 f))

end PolynomialCalculus

section Duality

/-- Over a prime field $\mathbb{F}_p$, an $\mathbb{F}_p$-linear functional on
$\mathbb{F}_p^{\le d}[V]$ sending $1$ to $1$ and vanishing on a subspace $W$ exists if and only if
$1 \notin W$. -/
theorem exists_linearMap_one_eq_one_vanishes_iff {V : Type*} {p d : ℕ} [Fact p.Prime]
    (W : Submodule (ZMod p) (PolyBoundedDeg V p d)) :
    (∃ L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p,
      L (PolyBoundedDeg.one V p d) = 1 ∧ ∀ q ∈ W, L q = 0) ↔
      PolyBoundedDeg.one V p d ∉ W := by
  constructor
  · rintro ⟨L, hL1, hLW⟩ hmem
    exact one_ne_zero (hL1.symm.trans (hLW _ hmem))
  · intro hnot
    have hx : W.mkQ (PolyBoundedDeg.one V p d) ≠ 0 := by
      rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
      exact hnot
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hx
    refine ⟨f.comp W.mkQ, hf, fun q hq => ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero W).mpr hq, map_zero]

end Duality

end CslibFrontier.Logic.PL.ENS
