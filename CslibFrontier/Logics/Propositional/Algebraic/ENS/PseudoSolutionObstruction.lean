/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.ENS.Refutation
public import CslibFrontier.Logics.Propositional.Algebraic.ENS.PolyDecisionTree
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Log

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Fintype.Pi
import Mathlib.FieldTheory.Finite.Basic

/-!
# Extended Nullstellensatz Obstruction to Pseudo-Solutions

This module formalizes indexed $(d, e, \gamma)$-pseudo-solutions of polynomial systems over prime
fields $\mathbb{F}_p$, the Nullstellensatz obstruction to bounded-degree linear designs, and
Krajíček's obstruction from low-degree stratified Extended Nullstellensatz refutations to the
existence of pseudo-solutions, verified under standard Lean axioms.

## Main definitions

- `CslibFrontier.Logic.PL.ENS.IsIndexedPseudoSolution`: indexed families of linear designs resisting
  bounded decision-tree conflict search.

## Main results

- `CslibFrontier.Logic.PL.ENS.isPseudoSolution_iff_isIndexedPseudoSolution`,
  `CslibFrontier.Logic.PL.ENS.IsIndexedPseudoSolution.mono`,
  `CslibFrontier.Logic.PL.ENS.IsPseudoSolution.mono`: equivalence with unindexed pseudo-solutions
  and
  parameter monotonicity.
- `CslibFrontier.Logic.PL.ENS.ns_no_linearDesign`,
  `CslibFrontier.Logic.PL.ENS.ns_no_indexed_pseudoSolution`,
  `CslibFrontier.Logic.PL.ENS.ns_no_pseudoSolution`: low-degree Nullstellensatz refutations rule out
  degree-$d$ linear designs and pseudo-solutions.
- `CslibFrontier.Logic.PL.ENS.ens_no_indexed_pseudoSolution`,
  `CslibFrontier.Logic.PL.ENS.ens_no_pseudoSolution`: stratified Extended Nullstellensatz
  refutations of degree at most $d$, size $S$, and accuracy $h$ satisfying
  $2 S^2 \le \exp(h / p)$ rule out $(d, h + \lceil \log_2 S \rceil, 1 / S)$-pseudo-solutions.
-/

public section

namespace CslibFrontier.Logic.PL.ENS

section IndexedPseudoSolution

/-- An indexed `(d, e, γ)`-pseudo-solution of a polynomial system `F` over `ZMod p`: a nonempty
finite index set `s` and family `ω` of degree-`d` linear designs of `F` on `s` such that every
polynomial query decision tree of height at most `e` fails to output a conflict pair on at least a
`γ`-fraction of indices in `s`. -/
@[expose] noncomputable def IsIndexedPseudoSolution {V ι : Type*} {p : ℕ} [NeZero p]
    (F : Set (MvPolynomial V (ZMod p))) (d e : ℕ) (γ : ℚ)
    (s : Finset ι) (ω : ι → PolyBoundedDeg V p d → ZMod p) : Prop :=
  s.Nonempty ∧ (∀ i ∈ s, IsLinearDesign F (ω i)) ∧
    ∀ T : PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d), T.height ≤ e →
      let _ : DecidablePred fun i => ¬ IsConflictPair (ω i) (T.eval (ω i)) := Classical.decPred _
      γ ≤ ((s.filter fun i => ¬ IsConflictPair (ω i) (T.eval (ω i))).card : ℚ) / (s.card : ℚ)

theorem isIndexedPseudoSolution_iff {V ι : Type*} {p : ℕ} [NeZero p]
    (F : Set (MvPolynomial V (ZMod p))) (d e : ℕ) (γ : ℚ)
    (s : Finset ι) (ω : ι → PolyBoundedDeg V p d → ZMod p) :
    IsIndexedPseudoSolution F d e γ s ω ↔
      s.Nonempty ∧ (∀ i ∈ s, IsLinearDesign F (ω i)) ∧
        ∀ T : PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d), T.height ≤ e →
          let _ : DecidablePred fun i => ¬ IsConflictPair (ω i) (T.eval (ω i)) :=
            Classical.decPred _
          γ ≤ ((s.filter fun i => ¬ IsConflictPair (ω i) (T.eval (ω i))).card : ℚ) /
              (s.card : ℚ) := by
  unfold IsIndexedPseudoSolution; rfl

/-- An unindexed finite set `Ω` of functionals is a `(d, e, γ)`-pseudo-solution if and only if
`Ω` indexed by the identity map is an indexed `(d, e, γ)`-pseudo-solution. -/
theorem isPseudoSolution_iff_isIndexedPseudoSolution {V : Type*} {p : ℕ} [NeZero p]
    (F : Set (MvPolynomial V (ZMod p))) (d e : ℕ) (γ : ℚ)
    (Ω : Finset (PolyBoundedDeg V p d → ZMod p)) :
    IsPseudoSolution F d e γ Ω ↔ IsIndexedPseudoSolution F d e γ Ω id := by
  rw [isIndexedPseudoSolution_iff]; exact Iff.rfl

/-- Monotonicity of `IsIndexedPseudoSolution` under decreasing tree height and survival ratio. -/
theorem IsIndexedPseudoSolution.mono {V ι : Type*} {p d e₁ e₂ : ℕ} [NeZero p]
    {F : Set (MvPolynomial V (ZMod p))} {γ₁ γ₂ : ℚ}
    {s : Finset ι} {ω : ι → PolyBoundedDeg V p d → ZMod p}
    (he : e₁ ≤ e₂) (hγ : γ₂ ≤ γ₁) (h : IsIndexedPseudoSolution F d e₂ γ₁ s ω) :
    IsIndexedPseudoSolution F d e₁ γ₂ s ω := by
  rw [isIndexedPseudoSolution_iff] at h ⊢
  exact ⟨h.1, h.2.1, fun T hT => hγ.trans (h.2.2 T (hT.trans he))⟩

/-- Monotonicity of `IsPseudoSolution` under decreasing tree height and survival ratio. -/
theorem IsPseudoSolution.mono {V : Type*} {p d e₁ e₂ : ℕ} [NeZero p]
    {F : Set (MvPolynomial V (ZMod p))} {γ₁ γ₂ : ℚ} {Ω : Finset (PolyBoundedDeg V p d → ZMod p)}
    (he : e₁ ≤ e₂) (hγ : γ₂ ≤ γ₁) (h : IsPseudoSolution F d e₂ γ₁ Ω) :
    IsPseudoSolution F d e₁ γ₂ Ω := by
  rw [isPseudoSolution_iff_isIndexedPseudoSolution] at h ⊢
  exact h.mono he hγ

end IndexedPseudoSolution

section NullstellensatzObstruction

private noncomputable def ofDegLe {V : Type*} {p d : ℕ}
    (q : MvPolynomial V (ZMod p)) (hq : q.totalDegree ≤ d) : PolyBoundedDeg V p d :=
  ⟨q, (MvPolynomial.mem_restrictTotalDegree V d q).mpr hq⟩

private theorem coe_ofDegLe {V : Type*} {p d : ℕ}
    (q : MvPolynomial V (ZMod p)) (hq : q.totalDegree ≤ d) : (ofDegLe (p := p) q hq).1 = q := rfl

private noncomputable def truncBounded {V : Type*} (p d : ℕ)
    (q : MvPolynomial V (ZMod p)) : PolyBoundedDeg V p d := by
  classical exact if hq : q.totalDegree ≤ d then ofDegLe q hq else 0

private theorem truncBounded_eq_ofDegLe {V : Type*} {p d : ℕ}
    {q : MvPolynomial V (ZMod p)} (hq : q.totalDegree ≤ d) :
    truncBounded p d q = ofDegLe q hq := by
  unfold truncBounded; exact dite_eq_left hq

private theorem vanishes_of_isLinearDesign_mul {V : Type*} {p d : ℕ} [Fact p.Prime]
    {F : Set (MvPolynomial V (ZMod p))} {ω : PolyBoundedDeg V p d → ZMod p}
    (hω : IsLinearDesign F ω) {f c : MvPolynomial V (ZMod p)} (hf : f ∈ F)
    (hdeg : (c * f).totalDegree ≤ d) : ω (ofDegLe (c * f) hdeg) = 0 := by
  classical
  let c' : MvPolynomial V (ZMod p) := if f = 0 then 0 else c
  have hc'_deg : c'.totalDegree ≤ d := by
    by_cases hf0 : f = 0
    · simp [c', hf0]
    · by_cases hc0 : c = 0
      · simp [c', hf0, hc0]
      · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hc0 hf0
        simpa [c', hf0] using (by omega : c.totalDegree ≤ d)
  have hprod_eq : f * c' = c * f := by by_cases hf0 : f = 0 <;> simp [c', hf0, mul_comm]
  have hdeg' : (f * c').totalDegree ≤ d := hprod_eq ▸ hdeg
  have hzero := hω.2 f hf (ofDegLe c' hc'_deg) hdeg'
  have hsub : ofDegLe (f * c') hdeg' = ofDegLe (c * f) hdeg := Subtype.ext hprod_eq
  rwa [← hsub]

/-- A Nullstellensatz refutation of `F` over a prime field `ZMod p` of degree at most `d`
precludes any degree-`d` linear design of `F`. -/
theorem ns_no_linearDesign {V : Type*} {p d : ℕ} [Fact p.Prime]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (hd : R.degree ≤ d)
    (ω : PolyBoundedDeg V p d → ZMod p) :
    ¬ IsLinearDesign (↑F : Set (MvPolynomial V (ZMod p))) ω := by
  rintro hω
  rcases hω.1 with ⟨L, hLω, hL1⟩
  have hsum_one : ∑ f ∈ F, truncBounded p d (R.coeff f * f) = PolyBoundedDeg.one V p d := by
    apply Subtype.ext
    rw [Submodule.coe_sum, PolyBoundedDeg.coe_one, ← R.refutes]
    exact Finset.sum_congr rfl fun f hf => by
      rw [truncBounded_eq_ofDegLe ((R.degree_mul_le hf).trans hd), coe_ofDegLe]
  have hsum_zero : L (∑ f ∈ F, truncBounded p d (R.coeff f * f)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [truncBounded_eq_ofDegLe ((R.degree_mul_le hf).trans hd), ← hLω]
    exact vanishes_of_isLinearDesign_mul hω hf ((R.degree_mul_le hf).trans hd)
  rw [hsum_one, hL1] at hsum_zero
  exact one_ne_zero hsum_zero

/-- A Nullstellensatz refutation of `F` of degree at most `d` precludes any indexed
`(d, e, γ)`-pseudo-solution of `F`. -/
theorem ns_no_indexed_pseudoSolution {V ι : Type*} {p d e : ℕ} [Fact p.Prime]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (hd : R.degree ≤ d)
    (γ : ℚ) (s : Finset ι) (ω : ι → PolyBoundedDeg V p d → ZMod p) :
    ¬ IsIndexedPseudoSolution (↑F) d e γ s ω := by
  intro hps; rcases (isIndexedPseudoSolution_iff _ _ _ _ _ _).mp hps with ⟨⟨i, hi⟩, hlin, _⟩
  exact ns_no_linearDesign R hd (ω i) (hlin i hi)

/-- A Nullstellensatz refutation of `F` of degree at most `d` precludes any
`(d, e, γ)`-pseudo-solution of `F`. -/
theorem ns_no_pseudoSolution {V : Type*} {p d e : ℕ} [Fact p.Prime]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (hd : R.degree ≤ d)
    (γ : ℚ) (Ω : Finset (PolyBoundedDeg V p d → ZMod p)) : ¬ IsPseudoSolution (↑F) d e γ Ω := by
  rw [isPseudoSolution_iff_isIndexedPseudoSolution]
  exact ns_no_indexed_pseudoSolution R hd γ Ω id

end NullstellensatzObstruction

section SpecializationAndDegrees

private noncomputable def blockFactor {W : Type*} {p h : ℕ}
    (B : ExtensionBlock W p h) (u : Fin h) : MvPolynomial W (ZMod p) :=
  1 - ∑ j : Fin B.basePolys.length, MvPolynomial.X (B.extVar u j) * B.basePolys[j]

private theorem extPoly_eq_mul_prod_blockFactor {W : Type*} {p h : ℕ}
    (B : ExtensionBlock W p h) (i : Fin B.basePolys.length) :
    B.extPoly i = B.basePolys[i] * ∏ u : Fin h, blockFactor B u := by
  rw [ExtensionBlock.extPoly_def]; rfl

private theorem blockFactor_ne_zero {W : Type*} {p h : ℕ} [Fact p.Prime]
    (B : ExtensionBlock W p h) (u : Fin h) : blockFactor B u ≠ 0 := fun h0 => by
  have hev := congrArg (MvPolynomial.eval (fun _ : W => (0 : ZMod p))) h0
  simp [blockFactor] at hev

private theorem prod_ne_zero_and_totalDegree {W α : Type*} {p : ℕ} [Fact p.Prime]
    (s : Finset α) (f : α → MvPolynomial W (ZMod p)) (hf : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 ∧ (∏ x ∈ s, f x).totalDegree = ∑ x ∈ s, (f x).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha0 := hf a (Finset.mem_insert_self a s)
    obtain ⟨hp0, hdeg⟩ := ih fun x hx => hf x (Finset.mem_insert_of_mem hx)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 hp0,
      (MvPolynomial.totalDegree_mul_of_isDomain ha0 hp0).trans
        (congrArg (f a).totalDegree.add hdeg)⟩

private theorem extVar_notMem_basePoly_vars {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (t : Fin R.numLevels) (b : Fin (R.levels t).length)
    (u : Fin R.accuracy) (j j' : Fin (R.levels t)[b].basePolys.length) :
    (R.levels t)[b].extVar u j ∉ (R.levels t)[b].basePolys[j'].vars := fun hw => by
  rcases R.stratified t b _ (List.getElem_mem _) _ hw with ⟨v, hv⟩ | ⟨s, hst, _, _, _, heq⟩
  · obtain ⟨k, hk⟩ := R.extVar_is_inr t b u j; rw [hk] at hv; cases hv
  · exact (ne_of_lt hst) (R.extVar_disjoint heq).1.symm

private theorem totalDegree_basePoly_le_blockFactor {V : Type*} {p : ℕ} [Fact p.Prime]
    [DecidableEq V] {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (t : Fin R.numLevels) (b : Fin (R.levels t).length)
    (u : Fin R.accuracy) (j : Fin (R.levels t)[b].basePolys.length) :
    (R.levels t)[b].basePolys[j].totalDegree ≤
      (blockFactor (R.levels t)[b] u).totalDegree := by
  let B := (R.levels t)[b]
  let g : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p) := B.basePolys[j]
  change g.totalDegree ≤ (blockFactor B u).totalDegree
  by_cases hg0 : g = 0
  · rw [hg0]; simp
  · obtain ⟨m, hm_mem, hm_sup⟩ := Finset.exists_mem_eq_sup g.support
      (MvPolynomial.support_nonempty.mpr hg0) fun d => d.sum fun _ e => e
    let w₀ := B.extVar u j
    have hnot_supp_var : ∀ j' : Fin B.basePolys.length, m (B.extVar u j') = 0 := fun j' => by
      by_contra hne
      exact extVar_notMem_basePoly_vars R t b u j' j
        ((MvPolynomial.mem_vars_iff_mem_support _).mpr
          ⟨m, hm_mem, Finsupp.mem_support_iff.mpr hne⟩)
    let m' := Finsupp.single w₀ 1 + m
    have hm'_ne : m' ≠ 0 := fun h0 => by
      have h1 : m' w₀ = 1 := by simp [m', w₀, hnot_supp_var j]
      rw [h0] at h1; exact Nat.one_ne_zero h1.symm
    have hcoeff_sum :
        (∑ j' : Fin B.basePolys.length,
          MvPolynomial.X (B.extVar u j') * B.basePolys[j']).coeff m' = g.coeff m := by
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j]
      · exact MvPolynomial.coeff_X_mul m w₀ g
      · intro j' _ hj'ne
        rw [MvPolynomial.coeff_X_mul']
        have hw_ne : B.extVar u j' ≠ w₀ := fun heq => hj'ne (congrArg Prod.snd (B.extVar_inj
          (show Function.uncurry B.extVar (u, j') = Function.uncurry B.extVar (u, j) from heq)))
        have hns : B.extVar u j' ∉ m'.support := by
          rw [Finsupp.mem_support_iff, not_not, Finsupp.add_apply,
            Finsupp.single_eq_of_ne hw_ne, hnot_supp_var j', zero_add]
        exact ite_eq_right hns
      · intro hj_abs; exact absurd (Finset.mem_univ j) hj_abs
    have hcoeff_bf : (blockFactor B u).coeff m' = - g.coeff m := by
      change (1 - ∑ j' : Fin B.basePolys.length,
        MvPolynomial.X (B.extVar u j') * B.basePolys[j']).coeff m' = - g.coeff m
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, ite_eq_right hm'_ne.symm,
        hcoeff_sum, zero_sub]
    have hm'_mem : m' ∈ (blockFactor B u).support := by
      rw [MvPolynomial.mem_support_iff, hcoeff_bf, neg_ne_zero]
      exact MvPolynomial.mem_support_iff.mp hm_mem
    have hm'_sum : g.totalDegree ≤ m'.sum fun _ e => e := by
      rw [MvPolynomial.totalDegree, hm_sup,
        Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      exact Nat.le_add_left _ _
    exact hm'_sum.trans (MvPolynomial.le_totalDegree hm'_mem)

private noncomputable def specAlgHom (V : Type*) {p M : ℕ} (β : Fin M → ZMod p) :
    MvPolynomial (V ⊕ Fin M) (ZMod p) →ₐ[ZMod p] MvPolynomial V (ZMod p) :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun k => MvPolynomial.C (β k))

private theorem specAlgHom_X_inl {V : Type*} {p M : ℕ} (β : Fin M → ZMod p) (v : V) :
    specAlgHom V β (MvPolynomial.X (Sum.inl v)) = MvPolynomial.X v := by simp [specAlgHom]

private theorem specAlgHom_X_inr (V : Type*) {p M : ℕ} (β : Fin M → ZMod p) (k : Fin M) :
    specAlgHom V β (MvPolynomial.X (Sum.inr k)) = MvPolynomial.C (β k) := by simp [specAlgHom]

private theorem specAlgHom_rename_inl {V : Type*} {p M : ℕ}
    (β : Fin M → ZMod p) (f : MvPolynomial V (ZMod p)) :
    specAlgHom V β (MvPolynomial.rename Sum.inl f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [specAlgHom]
  | add f g ihf ihg => simp [ihf, ihg]
  | mul_X f v ih => simp [specAlgHom_X_inl, ih]

private theorem totalDegree_specAlgHom_le {V : Type*} {p M : ℕ}
    (β : Fin M → ZMod p) (Q : MvPolynomial (V ⊕ Fin M) (ZMod p)) :
    (specAlgHom V β Q).totalDegree ≤ Q.totalDegree := by
  let φ : V ⊕ Fin M → MvPolynomial V (ZMod p) :=
    Sum.elim MvPolynomial.X fun k => MvPolynomial.C (β k)
  change (MvPolynomial.aeval φ Q).totalDegree ≤ Q.totalDegree
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  have hvar : ∀ w : V ⊕ Fin M, (φ w).totalDegree ≤ 1 := by
    rintro (v | _)
    · dsimp only [φ, Sum.elim_inl]
      rcases subsingleton_or_nontrivial (ZMod p) with _ | _
      · rw [Subsingleton.elim (MvPolynomial.X v : MvPolynomial V (ZMod p)) 0]; simp
      · exact (MvPolynomial.totalDegree_X v).le
    · simp [φ]
  have hprod : ∀ (a : (V ⊕ Fin M) →₀ ℕ) (t : Finset (V ⊕ Fin M)),
      (∏ w ∈ t, φ w ^ a w).totalDegree ≤ ∑ w ∈ t, a w := fun a t => by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert w t hw ih =>
      rw [Finset.prod_insert hw, Finset.sum_insert hw]
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add
        ((MvPolynomial.totalDegree_pow _ _).trans
          ((Nat.mul_le_mul_left _ (hvar w)).trans_eq (Nat.mul_one _))) ih)
  have hsum : ∀ s : Finset ((V ⊕ Fin M) →₀ ℕ),
      (∑ m ∈ s, MvPolynomial.C (Q.coeff m) * ∏ w ∈ m.support, φ w ^ m w).totalDegree ≤
        s.sup fun m => m.sum fun _ e => e := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (MvPolynomial.totalDegree_add _ _).trans (max_le
        (((MvPolynomial.totalDegree_mul _ _).trans
          (by rw [MvPolynomial.totalDegree_C, zero_add]; exact hprod a a.support)).trans
          (le_max_left _ _)) (ih.trans (le_max_right _ _)))
  exact hsum Q.support

private noncomputable def specBounded {V : Type*} {p d M : ℕ}
    (β : Fin M → ZMod p) (Q : MvPolynomial (V ⊕ Fin M) (ZMod p))
    (hQ : Q.totalDegree ≤ d) : PolyBoundedDeg V p d :=
  ofDegLe (specAlgHom V β Q) ((totalDegree_specAlgHom_le β Q).trans hQ)

private theorem coe_specBounded {V : Type*} {p d M : ℕ}
    (β : Fin M → ZMod p) (Q : MvPolynomial (V ⊕ Fin M) (ZMod p)) (hQ : Q.totalDegree ≤ d) :
    (specBounded β Q hQ).1 = specAlgHom V β Q := rfl

private theorem specAlgHom_eq_of_vars {V : Type*} {p M : ℕ}
    {β₁ β₂ : Fin M → ZMod p} {Q : MvPolynomial (V ⊕ Fin M) (ZMod p)}
    (hβ : ∀ k : Fin M, Sum.inr k ∈ Q.vars → β₁ k = β₂ k) :
    specAlgHom V β₁ Q = specAlgHom V β₂ Q := by
  simp only [specAlgHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m hm => congrArg _ (Finset.prod_congr rfl fun w hw => ?_)
  cases w with
  | inl _ => rfl
  | inr k => simp [hβ k ((MvPolynomial.mem_vars_iff_mem_support _).mpr ⟨m, hm, hw⟩)]

private theorem specAlgHom_frobenius_eq_zero {V : Type*} {p : ℕ} [Fact p.Prime]
    [DecidableEq V] {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (β : Fin R.numExtVars → ZMod p) {P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)}
    (hP : P ∈ (Finset.univ : Finset (Fin R.numLevels)).biUnion fun t =>
      ((R.levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset) :
    specAlgHom V β P = 0 := by
  rcases Finset.mem_biUnion.mp hP with ⟨t, _, ht⟩
  rcases List.mem_flatMap.mp (List.mem_toFinset.mp ht) with ⟨B, hB, hfrob⟩
  obtain ⟨b, hb_lt, rfl⟩ := List.getElem_of_mem hB
  rw [ExtensionBlock.frobeniusList_def, List.mem_flatMap] at hfrob
  rcases hfrob with ⟨u, _, hj_mem⟩
  rcases List.mem_map.mp hj_mem with ⟨j, _, rfl⟩
  obtain ⟨k, hk⟩ := R.extVar_is_inr t ⟨b, hb_lt⟩ u j
  have hk' : (R.levels t)[b].extVar u j = Sum.inr k := hk
  rw [hk', map_sub, map_pow, specAlgHom_X_inr, ← map_pow, ZMod.pow_card, sub_self]

private theorem extPoly_degree_split {W : Type*} {p h d : ℕ} [Fact p.Prime]
    {B : ExtensionBlock W p h} {idx : Fin B.basePolys.length} {c : MvPolynomial W (ZMod p)}
    (hcP : c * B.extPoly idx ≠ 0) (hcdeg : (c * B.extPoly idx).totalDegree ≤ d) :
    c.totalDegree + B.basePolys[idx].totalDegree +
      ∑ u : Fin h, (blockFactor B u).totalDegree ≤ d := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcP
  have hE0 : B.basePolys[idx] * ∏ u : Fin h, blockFactor B u ≠ 0 := by
    rw [← extPoly_eq_mul_prod_blockFactor]; exact right_ne_zero_of_mul hcP
  have hg0 : B.basePolys[idx] ≠ 0 := left_ne_zero_of_mul hE0
  obtain ⟨hp0, hp_deg⟩ := prod_ne_zero_and_totalDegree Finset.univ
    (fun u : Fin h => blockFactor B u) (fun u _ => blockFactor_ne_zero B u)
  have hd' : (c * (B.basePolys[idx] * ∏ u : Fin h, blockFactor B u)).totalDegree ≤ d := by
    rwa [← extPoly_eq_mul_prod_blockFactor]
  rw [MvPolynomial.totalDegree_mul_of_isDomain hc0 (mul_ne_zero hg0 hp0),
    MvPolynomial.totalDegree_mul_of_isDomain hg0 hp0, hp_deg] at hd'
  omega

end SpecializationAndDegrees

section SearchDecisionTree

private noncomputable def binSearchTree {V α I : Type*} {p d : ℕ}
    (q : α → PolyBoundedDeg V p d) (cont : α → PolyDecisionTree V p d I)
    (defaultTree : PolyDecisionTree V p d I) : List α → PolyDecisionTree V p d I
  | [] => defaultTree
  | [x] => cont x
  | x₁ :: x₂ :: rest =>
    let xs := x₁ :: x₂ :: rest
    .node ((xs.take (xs.length / 2) |>.map q).sum) fun ans =>
      if ans = 0 then binSearchTree q cont defaultTree (xs.drop (xs.length / 2))
      else binSearchTree q cont defaultTree (xs.take (xs.length / 2))
termination_by xs => xs.length
decreasing_by
  · simp only [List.length_drop, List.length_cons]; omega
  · simp only [List.length_take, List.length_cons]; omega

private theorem height_binSearchTree_le {V α I : Type*} {p d H : ℕ} [NeZero p]
    (q : α → PolyBoundedDeg V p d) (cont : α → PolyDecisionTree V p d I)
    (defaultTree : PolyDecisionTree V p d I) (xs : List α) (hne : xs ≠ [])
    (hcont : ∀ x ∈ xs, (cont x).height ≤ H) :
    (binSearchTree q cont defaultTree xs).height ≤ H + Nat.clog 2 xs.length := by
  suffices ∀ n (ys : List α), ys.length = n → ys ≠ [] → (∀ x ∈ ys, (cont x).height ≤ H) →
      (binSearchTree q cont defaultTree ys).height ≤ H + Nat.clog 2 ys.length from
    this xs.length xs rfl hne hcont
  intro n; induction n using Nat.strong_induction_on with
  | ind n ih =>
    rintro (_ | ⟨x₁, _ | ⟨x₂, rest⟩⟩) rfl hys hc
    · exact absurd rfl hys
    · have hc1 : Nat.clog 2 1 = 0 := by decide
      simp only [binSearchTree, List.length_singleton, hc1, Nat.add_zero]
      exact hc x₁ (List.mem_singleton_self x₁)
    · let ys := x₁ :: x₂ :: rest
      let k := ys.length / 2
      have hlen : 2 ≤ ys.length := by simp [ys]
      have hys_len : (x₁ :: x₂ :: rest).length = ys.length := rfl
      have htk_len : (ys.take k).length = k := List.length_take_of_le (by omega)
      have hdp_len : (ys.drop k).length = ys.length - k := List.length_drop
      have htk_ne : ys.take k ≠ [] := by rw [← List.length_pos_iff_ne_nil, htk_len]; omega
      have hdp_ne : ys.drop k ≠ [] := by rw [← List.length_pos_iff_ne_nil, hdp_len]; omega
      have iht := ih k (by omega) (ys.take k) htk_len htk_ne
        fun x hx => hc x (List.mem_of_mem_take hx)
      have ihd := ih (ys.length - k) (by omega) (ys.drop k) hdp_len hdp_ne
        fun x hx => hc x (List.mem_of_mem_drop hx)
      have hclog : Nat.clog 2 ys.length = Nat.clog 2 (ys.length - k) + 1 := by
        rw [Nat.clog_of_one_lt (by omega) (by omega)]
        exact congrArg (· + 1) (congrArg (Nat.clog 2) (by omega))
      have hsup :
          (Finset.univ.sup fun ans : ZMod p =>
            (if ans = 0 then binSearchTree q cont defaultTree (ys.drop k)
             else binSearchTree q cont defaultTree (ys.take k)).height) ≤
            H + Nat.clog 2 (ys.length - k) := by
        refine Finset.sup_le fun ans _ => ?_
        split_ifs
        · rwa [hdp_len] at ihd
        · exact (htk_len ▸ iht).trans (Nat.add_le_add_left (Nat.clog_mono_right 2 (by omega)) H)
      rw [binSearchTree, PolyDecisionTree.height_node]
      change 1 + (Finset.univ.sup fun ans : ZMod p =>
        (if ans = 0 then binSearchTree q cont defaultTree (ys.drop k)
         else binSearchTree q cont defaultTree (ys.take k)).height) ≤
        H + Nat.clog 2 ys.length
      omega

private theorem eval_binSearchTree_exists {V α I : Type*} {p d : ℕ}
    (q : α → PolyBoundedDeg V p d) (cont : α → PolyDecisionTree V p d I)
    (defaultTree : PolyDecisionTree V p d I) {ω : PolyBoundedDeg V p d → ZMod p}
    {L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p} (hLω : ∀ g, ω g = L g)
    (xs : List α) (hsum : (xs.map fun x => L (q x)).sum ≠ 0) :
    ∃ x ∈ xs, L (q x) ≠ 0 ∧
      (binSearchTree q cont defaultTree xs).eval ω = (cont x).eval ω := by
  suffices ∀ n (ys : List α), ys.length = n → (ys.map fun x => L (q x)).sum ≠ 0 →
      ∃ x ∈ ys, L (q x) ≠ 0 ∧
        (binSearchTree q cont defaultTree ys).eval ω = (cont x).eval ω from
    this xs.length xs rfl hsum
  intro n; induction n using Nat.strong_induction_on with
  | ind n ih =>
    rintro (_ | ⟨x₁, _ | ⟨x₂, rest⟩⟩) rfl hys
    · simp at hys
    · rw [binSearchTree]
      exact ⟨x₁, List.mem_singleton_self x₁, by simpa using hys, rfl⟩
    · let ys := x₁ :: x₂ :: rest
      let k := ys.length / 2
      have hsum_split : (ys.map fun x => L (q x)).sum =
          ((ys.take k).map fun x => L (q x)).sum + ((ys.drop k).map fun x => L (q x)).sum := by
        conv_lhs => rw [← List.take_append_drop k ys, List.map_append, List.sum_append]
      have hans_eq : ω ((ys.take k |>.map q).sum) = ((ys.take k).map fun x => L (q x)).sum := by
        rw [hLω, map_list_sum, List.map_map]; rfl
      rw [binSearchTree, PolyDecisionTree.eval_node]
      change ∃ x ∈ ys, L (q x) ≠ 0 ∧
        (if ω ((ys.take k |>.map q).sum) = 0 then binSearchTree q cont defaultTree (ys.drop k)
         else binSearchTree q cont defaultTree (ys.take k)).eval ω = (cont x).eval ω
      by_cases hans : ω ((ys.take k |>.map q).sum) = 0
      · rw [ite_eq_left hans]
        have hdp_nz : ((ys.drop k).map fun x => L (q x)).sum ≠ 0 := fun h0 =>
          hys (by rw [hsum_split, ← hans_eq, hans, h0, add_zero])
        obtain ⟨x, hx, hLx, hev⟩ :=
          ih (ys.drop k).length (by simp [ys, k]; omega) (ys.drop k) rfl hdp_nz
        exact ⟨x, List.mem_of_mem_drop hx, hLx, hev⟩
      · rw [ite_eq_right hans]
        obtain ⟨x, hx, hLx, hev⟩ :=
          ih (ys.take k).length (by simp [ys, k]; omega) (ys.take k) rfl (hans_eq ▸ hans)
        exact ⟨x, List.mem_of_mem_take hx, hLx, hev⟩

private noncomputable def firstZeroOrLastTree {V : Type*} {p d : ℕ} :
    List (PolyBoundedDeg V p d × PolyBoundedDeg V p d) →
      PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d)
  | [] => .leaf (0, 0)
  | [pair] => .leaf pair
  | pair :: a :: rest =>
    .node pair.2 fun ans => if ans = 0 then .leaf pair else firstZeroOrLastTree (a :: rest)

private theorem height_firstZeroOrLastTree_le {V : Type*} {p d : ℕ} [NeZero p] :
    ∀ (pairs : List (PolyBoundedDeg V p d × PolyBoundedDeg V p d)),
      (firstZeroOrLastTree pairs).height ≤ pairs.length - 1
  | [] => by simp [firstZeroOrLastTree]
  | [pair] => by simp [firstZeroOrLastTree]
  | pair :: a :: rest => by
    rw [firstZeroOrLastTree, PolyDecisionTree.height_node]
    have ih := height_firstZeroOrLastTree_le (a :: rest)
    have hsup : (Finset.univ.sup fun ans : ZMod p =>
        (if ans = 0 then PolyDecisionTree.leaf pair
         else firstZeroOrLastTree (a :: rest)).height) ≤ rest.length :=
      Finset.sup_le fun _ _ => by split_ifs <;> [simp; simpa using ih]
    simp only [List.length_cons]; omega

private theorem conflict_of_mul_eq_of_snd_zero {V : Type*} {p d : ℕ}
    {ω : PolyBoundedDeg V p d → ZMod p} {q : PolyBoundedDeg V p d} (hq : ω q ≠ 0)
    {pair : PolyBoundedDeg V p d × PolyBoundedDeg V p d}
    (hmul : pair.1.1 * pair.2.1 = q.1) (h0 : ω pair.2 = 0) : IsConflictPair ω pair := by
  have hdeg : (pair.1.1 * pair.2.1).totalDegree ≤ d := hmul ▸ q.totalDegree_le
  refine ⟨hdeg, ?_⟩
  change ω pair.1 * ω pair.2 ≠ ω (ofDegLe (pair.1.1 * pair.2.1) hdeg)
  rw [show ofDegLe (pair.1.1 * pair.2.1) hdeg = q from Subtype.ext hmul, h0, mul_zero]
  exact hq.symm

private theorem forall_snd_ne_zero_of_not_conflict {V : Type*} {p d : ℕ}
    {ω : PolyBoundedDeg V p d → ZMod p} {q : PolyBoundedDeg V p d} (hq : ω q ≠ 0) :
    ∀ (pairs : List (PolyBoundedDeg V p d × PolyBoundedDeg V p d)),
      pairs ≠ [] → (∀ pair ∈ pairs, pair.1.1 * pair.2.1 = q.1) →
      ¬ IsConflictPair ω ((firstZeroOrLastTree pairs).eval ω) →
      ∀ pair ∈ pairs, ω pair.2 ≠ 0
  | [], hne, _, _ => absurd rfl hne
  | [pair], _, hprod, hnc => fun p' hp' => by
    rcases List.mem_singleton.mp hp' with rfl
    rw [firstZeroOrLastTree, PolyDecisionTree.eval_leaf] at hnc
    exact fun h0 => hnc (conflict_of_mul_eq_of_snd_zero hq
      (hprod p' (List.mem_singleton_self p')) h0)
  | pair :: a :: rest, _, hprod, hnc => by
    rw [firstZeroOrLastTree, PolyDecisionTree.eval_node] at hnc
    have hpair_nz : ω pair.2 ≠ 0 := fun h0 => by
      rw [ite_eq_left h0, PolyDecisionTree.eval_leaf] at hnc
      exact hnc (conflict_of_mul_eq_of_snd_zero hq (hprod pair List.mem_cons_self) h0)
    rw [ite_eq_right hpair_nz] at hnc
    have ih := forall_snd_ne_zero_of_not_conflict hq (a :: rest) (List.cons_ne_nil a rest)
      (fun p' hp' => hprod p' (List.mem_cons_of_mem pair hp')) hnc
    intro p' hp'; rcases List.mem_cons.mp hp' with rfl | hmem
    · exact hpair_nz
    · exact ih p' hmem

private noncomputable def blockSearchPairs {V : Type*} {p d h M : ℕ} [Fact p.Prime]
    (B : ExtensionBlock (V ⊕ Fin M) p h) (idx : Fin B.basePolys.length)
    (c : MvPolynomial (V ⊕ Fin M) (ZMod p)) (hcP : c * B.extPoly idx ≠ 0)
    (hcdeg : (c * B.extPoly idx).totalDegree ≤ d) (β : Fin M → ZMod p) :
    List (PolyBoundedDeg V p d × PolyBoundedDeg V p d) :=
  have htot := extPoly_degree_split hcP hcdeg
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcP
  have hE0 : B.basePolys[idx] * ∏ u : Fin h, blockFactor B u ≠ 0 := by
    rw [← extPoly_eq_mul_prod_blockFactor]; exact right_ne_zero_of_mul hcP
  have hg0 : B.basePolys[idx] ≠ 0 := left_ne_zero_of_mul hE0
  have hW_deg : (c * ∏ u : Fin h, blockFactor B u).totalDegree ≤ d := by
    obtain ⟨hp0, hp_deg⟩ := prod_ne_zero_and_totalDegree Finset.univ
      (fun u : Fin h => blockFactor B u) (fun u _ => blockFactor_ne_zero B u)
    rw [MvPolynomial.totalDegree_mul_of_isDomain hc0 hp0, hp_deg]; omega
  (specBounded β (c * ∏ u : Fin h, blockFactor B u) hW_deg,
    specBounded β B.basePolys[idx] (by omega)) ::
  (List.finRange h).map fun u =>
    have hbu : (blockFactor B u).totalDegree ≤ ∑ v : Fin h, (blockFactor B v).totalDegree :=
      Finset.single_le_sum (f := fun v : Fin h => (blockFactor B v).totalDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    have hU_deg :
        (c * B.basePolys[idx] * ∏ v ∈ Finset.univ.erase u, blockFactor B v).totalDegree ≤ d := by
      obtain ⟨her0, her_deg⟩ := prod_ne_zero_and_totalDegree (Finset.univ.erase u)
        (fun v => blockFactor B v) (fun v _ => blockFactor_ne_zero B v)
      have her_le := Finset.sum_le_sum_of_subset
        (f := fun v : Fin h => (blockFactor B v).totalDegree) (Finset.erase_subset u Finset.univ)
      rw [MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero hc0 hg0) her0,
        MvPolynomial.totalDegree_mul_of_isDomain hc0 hg0, her_deg]; omega
    (specBounded β (c * B.basePolys[idx] * ∏ v ∈ Finset.univ.erase u, blockFactor B v) hU_deg,
      specBounded β (blockFactor B u) (by omega))

private noncomputable def blockSearchTree {V : Type*} {p d h M : ℕ} [Fact p.Prime]
    (B : ExtensionBlock (V ⊕ Fin M) p h) (idx : Fin B.basePolys.length)
    (c : MvPolynomial (V ⊕ Fin M) (ZMod p)) (hcdeg : (c * B.extPoly idx).totalDegree ≤ d)
    (β : Fin M → ZMod p) :
    PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d) := by
  classical exact
    if hcP : c * B.extPoly idx = 0 then .leaf (0, 0)
    else firstZeroOrLastTree (blockSearchPairs B idx c hcP hcdeg β)

private theorem height_blockSearchTree_le {V : Type*} {p d h M : ℕ} [Fact p.Prime]
    (B : ExtensionBlock (V ⊕ Fin M) p h) (idx : Fin B.basePolys.length)
    (c : MvPolynomial (V ⊕ Fin M) (ZMod p)) (hcdeg : (c * B.extPoly idx).totalDegree ≤ d)
    (β : Fin M → ZMod p) : (blockSearchTree B idx c hcdeg β).height ≤ h := by
  unfold blockSearchTree
  by_cases hcP : c * B.extPoly idx = 0
  · rw [dite_eq_left hcP]; simp
  · rw [dite_eq_right hcP]
    exact (height_firstZeroOrLastTree_le _).trans (by simp [blockSearchPairs])

private def IsBadBlockAssign {V : Type*} {p d : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p)
    (t : Fin R.numLevels) (b : Fin (R.levels t).length)
    (hdeg_all : ∀ j : Fin (R.levels t)[b].basePolys.length,
      (R.levels t)[b].basePolys[j].totalDegree ≤ d)
    (β : Fin R.numExtVars → ZMod p) : Prop :=
  (∃ idx : Fin (R.levels t)[b].basePolys.length,
    L (specBounded β (R.levels t)[b].basePolys[idx] (hdeg_all idx)) ≠ 0) ∧
  ∀ u : Fin R.accuracy,
    (∑ j : Fin (R.levels t)[b].basePolys.length,
      β (Classical.choose (R.extVar_is_inr t b u j)) *
        L (specBounded β (R.levels t)[b].basePolys[j] (hdeg_all j))) ≠ 1

private theorem blockSearchTree_spec_of_not_conflict {V : Type*} {p d : ℕ} [Fact p.Prime]
    [DecidableEq V] {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (t : Fin R.numLevels) (b : Fin (R.levels t).length)
    (idx : Fin (R.levels t)[b].basePolys.length)
    (c : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p))
    (hcdeg : (c * (R.levels t)[b].extPoly idx).totalDegree ≤ d)
    (β : Fin R.numExtVars → ZMod p) {ω : PolyBoundedDeg V p d → ZMod p}
    {L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p}
    (hLω : ∀ g, ω g = L g) (hL1 : L (PolyBoundedDeg.one V p d) = 1)
    (hq_nz : L (specBounded β (c * (R.levels t)[b].extPoly idx) hcdeg) ≠ 0)
    (hnc : ¬ IsConflictPair ω ((blockSearchTree (R.levels t)[b] idx c hcdeg β).eval ω)) :
    ∃ hdeg_all : ∀ j : Fin (R.levels t)[b].basePolys.length,
        (R.levels t)[b].basePolys[j].totalDegree ≤ d,
      IsBadBlockAssign R L t b hdeg_all β := by
  have hcP : c * (R.levels t)[b].extPoly idx ≠ 0 := fun h0 => hq_nz <| by
    have hq0 : specBounded β (c * (R.levels t)[b].extPoly idx) hcdeg = 0 :=
      Subtype.ext (by rw [coe_specBounded, h0, map_zero]; rfl)
    rw [hq0, map_zero]
  have htot := extPoly_degree_split hcP hcdeg
  let u₀ : Fin R.accuracy := ⟨0, R.accuracy_pos⟩
  have hu₀_le : (blockFactor (R.levels t)[b] u₀).totalDegree ≤
      ∑ u : Fin R.accuracy, (blockFactor (R.levels t)[b] u).totalDegree :=
    Finset.single_le_sum
      (f := fun u : Fin R.accuracy => (blockFactor (R.levels t)[b] u).totalDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u₀)
  have hdeg_all : ∀ j : Fin (R.levels t)[b].basePolys.length,
      (R.levels t)[b].basePolys[j].totalDegree ≤ d := fun j =>
    (totalDegree_basePoly_le_blockFactor R t b u₀ j).trans (hu₀_le.trans (by omega))
  unfold blockSearchTree at hnc
  rw [dite_eq_right hcP] at hnc
  have hω_q : ω (specBounded β (c * (R.levels t)[b].extPoly idx) hcdeg) ≠ 0 := by rwa [hLω]
  have hpairs_prod : ∀ pair ∈ blockSearchPairs (R.levels t)[b] idx c hcP hcdeg β,
      pair.1.1 * pair.2.1 = (specBounded β (c * (R.levels t)[b].extPoly idx) hcdeg).1 := by
    intro pair hmem; unfold blockSearchPairs at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem_rest
    · simp only [coe_specBounded, ← map_mul, extPoly_eq_mul_prod_blockFactor]; congr 1; ring
    · rcases List.mem_map.mp hmem_rest with ⟨u, _, rfl⟩
      simp only [coe_specBounded, ← map_mul, extPoly_eq_mul_prod_blockFactor]
      rw [mul_assoc (c * (R.levels t)[b].basePolys[idx]),
        Finset.prod_erase_mul Finset.univ (fun v => blockFactor (R.levels t)[b] v)
          (Finset.mem_univ u), mul_assoc]
  have hall_nz := forall_snd_ne_zero_of_not_conflict hω_q _
    (by unfold blockSearchPairs; exact List.cons_ne_nil _ _) hpairs_prod hnc
  refine ⟨hdeg_all, ⟨idx, ?_⟩, fun u => ?_⟩
  · have hg_nz := hall_nz _ (by unfold blockSearchPairs; exact List.mem_cons_self)
    rwa [hLω] at hg_nz
  · have hBu_nz := hall_nz _
      (by unfold blockSearchPairs
          exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange u)))
    rw [hLω] at hBu_nz
    have hbu_le : (blockFactor (R.levels t)[b] u).totalDegree ≤ d :=
      (Finset.single_le_sum
        (f := fun v : Fin R.accuracy => (blockFactor (R.levels t)[b] v).totalDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)).trans (by omega)
    have hBu_eq :
        specBounded β (blockFactor (R.levels t)[b] u) hbu_le =
          PolyBoundedDeg.one V p d -
            ∑ j : Fin (R.levels t)[b].basePolys.length,
              β (Classical.choose (R.extVar_is_inr t b u j)) •
                specBounded β (R.levels t)[b].basePolys[j] (hdeg_all j) := by
      apply Subtype.ext
      rw [coe_specBounded, Submodule.coe_sub, PolyBoundedDeg.coe_one, Submodule.coe_sum]
      dsimp only [blockFactor]
      rw [map_sub, map_one, map_sum]
      refine congrArg (1 - ·) (Finset.sum_congr rfl fun j _ => ?_)
      let k := Classical.choose (R.extVar_is_inr t b u j)
      have hk : (R.levels t)[b].extVar u j = Sum.inr k :=
        Classical.choose_spec (R.extVar_is_inr t b u j)
      change specAlgHom V β
          (MvPolynomial.X ((R.levels t)[b].extVar u j) * (R.levels t)[b].basePolys[j]) =
        (β k • specBounded β (R.levels t)[b].basePolys[j] (hdeg_all j)).1
      rw [hk, map_mul, specAlgHom_X_inr, MvPolynomial.C_eq_algebraMap,
        Submodule.coe_smul_of_tower, Algebra.smul_def, coe_specBounded]
    dsimp only at hBu_nz
    rw [hBu_eq, map_sub, hL1, map_sum] at hBu_nz
    exact fun hsum_eq => hBu_nz <| by
      have hsum_eq' :
          (∑ j : Fin (R.levels t)[b].basePolys.length,
            L (β (Classical.choose (R.extVar_is_inr t b u j)) •
              specBounded β (R.levels t)[b].basePolys[j] (hdeg_all j))) = 1 := by
        simpa [map_smul, smul_eq_mul] using hsum_eq
      rw [hsum_eq', sub_self]

end SearchDecisionTree

section FiberCounting

private theorem card_affineHyperplaneCompl_eq {p m : ℕ} [Fact p.Prime]
    {v : Fin m → ZMod p} (j₀ : Fin m) (hv : v j₀ ≠ 0) :
    (Finset.univ.filter fun δ : Fin m → ZMod p => ∑ j : Fin m, δ j * v j ≠ 1).card =
      (p - 1) * p ^ (m - 1) := by
  classical
  let Rest := { j : Fin m // j ≠ j₀ } → ZMod p
  let δ₀ : Rest → Fin m → ZMod p := fun r j => if h : j = j₀ then 0 else r ⟨j, h⟩
  let equiv : (Fin m → ZMod p) ≃ ZMod p × Rest :=
    { toFun := fun δ => (∑ j : Fin m, δ j * v j, fun j => δ j.1)
      invFun := fun cr =>
        Function.update (δ₀ cr.2) j₀ ((cr.1 - ∑ j : Fin m, δ₀ cr.2 j * v j) * (v j₀)⁻¹)
      left_inv := fun δ => by
        funext j; dsimp only
        by_cases hj : j = j₀
        · subst hj; rw [Function.update_self]
          have hsum_er :
              ∑ i : Fin m, δ₀ (fun k : { k : Fin m // k ≠ j } => δ k.1) i * v i =
                ∑ i ∈ Finset.univ.erase j, δ i * v i := by
            rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
            have h0 : δ₀ (fun k : { k : Fin m // k ≠ j } => δ k.1) j * v j = 0 := by simp [δ₀]
            rw [h0, add_zero]
            exact Finset.sum_congr rfl fun i hi => by simp [δ₀, Finset.ne_of_mem_erase hi]
          rw [hsum_er, ← Finset.sum_erase_add Finset.univ (fun i => δ i * v i) (Finset.mem_univ j),
            add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ hv, mul_one]
        · rw [Function.update_of_ne hj]; simp [δ₀, hj]
      right_inv := fun ⟨c, r⟩ => by
        apply Prod.ext
        · dsimp only; rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j₀)]
          have her :
              ∑ i ∈ Finset.univ.erase j₀,
                Function.update (δ₀ r) j₀ ((c - ∑ j : Fin m, δ₀ r j * v j) * (v j₀)⁻¹) i * v i =
                ∑ j : Fin m, δ₀ r j * v j := by
            conv_rhs => rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j₀)]
            have h0 : δ₀ r j₀ * v j₀ = 0 := by simp [δ₀]
            rw [h0, add_zero]
            exact Finset.sum_congr rfl fun i hi => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          rw [her, Function.update_self, mul_assoc, inv_mul_cancel₀ hv, mul_one, add_sub_cancel]
        · funext ⟨j, hj⟩; dsimp only; rw [Function.update_of_ne hj]; simp [δ₀, hj] }
  have hcard_rest : Fintype.card Rest = p ^ (m - 1) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_fin]; simp
  have hbij :
      (Finset.univ.filter fun δ : Fin m → ZMod p => ∑ j : Fin m, δ j * v j ≠ 1).card =
        ((Finset.univ.erase (1 : ZMod p)) ×ˢ (Finset.univ : Finset Rest)).card := by
    refine Finset.card_bij (fun δ _ => equiv δ)
      (fun δ hδ => Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hδ).2, Finset.mem_univ _⟩, Finset.mem_univ _⟩)
      (fun _ _ _ _ h => equiv.injective h) fun cr hcr =>
      ⟨equiv.symm cr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, equiv.apply_symm_apply cr⟩
    change (equiv (equiv.symm cr)).1 ≠ 1
    rw [equiv.apply_symm_apply]
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hcr).1).1
  rw [hbij, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ (1 : ZMod p)),
    Finset.card_univ, ZMod.card, Finset.card_univ, hcard_rest]

private theorem card_badBlockAssign_mul_pow_le {V : Type*} {p d : ℕ} [Fact p.Prime]
    [DecidableEq V] {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p)
    (t : Fin R.numLevels) (b : Fin (R.levels t).length)
    (hdeg_all : ∀ j : Fin (R.levels t)[b].basePolys.length,
      (R.levels t)[b].basePolys[j].totalDegree ≤ d)
    {s_bad : Finset (Fin R.numExtVars → ZMod p)}
    (hs_bad : ∀ β ∈ s_bad, IsBadBlockAssign R L t b hdeg_all β) :
    s_bad.card * p ^ R.accuracy ≤
      Fintype.card (Fin R.numExtVars → ZMod p) * (p - 1) ^ R.accuracy := by
  classical
  by_cases hm0 : (R.levels t)[b].basePolys.length = 0
  · have hemp : s_bad = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun β hβ => by
      rcases (hs_bad β hβ).1 with ⟨idx, _⟩
      exact absurd hm0 (Nat.ne_of_gt (Nat.zero_lt_of_lt idx.isLt))
    rw [hemp, Finset.card_empty, zero_mul]; exact Nat.zero_le _
  · let m := (R.levels t)[b].basePolys.length
    have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
    let ι : Fin R.accuracy × Fin m → Fin R.numExtVars :=
      fun uj => Classical.choose (R.extVar_is_inr t b uj.1 uj.2)
    have hι_inj : Function.Injective ι := fun q₁ q₂ heq => by
      have h1 : (R.levels t)[b].extVar q₁.1 q₁.2 = Sum.inr (ι q₁) :=
        Classical.choose_spec (R.extVar_is_inr t b q₁.1 q₁.2)
      have h2 : (R.levels t)[b].extVar q₂.1 q₂.2 = Sum.inr (ι q₂) :=
        Classical.choose_spec (R.extVar_is_inr t b q₂.1 q₂.2)
      apply (R.levels t)[b].extVar_inj
      change (R.levels t)[b].extVar q₁.1 q₁.2 = (R.levels t)[b].extVar q₂.1 q₂.2
      rw [h1, h2, heq]
    let IsBlkVar : Fin R.numExtVars → Prop := fun k => ∃ q : Fin R.accuracy × Fin m, ι q = k
    let Out := { k : Fin R.numExtVars // ¬ IsBlkVar k } → ZMod p
    let In := Fin R.accuracy → Fin m → ZMod p
    let splitEquiv : (Fin R.numExtVars → ZMod p) ≃ Out × In :=
      { toFun := fun β => (fun k => β k.1, fun u j => β (ι (u, j)))
        invFun := fun fg k =>
          if hk : IsBlkVar k then fg.2 (Classical.choose hk).1 (Classical.choose hk).2
          else fg.1 ⟨k, hk⟩
        left_inv := fun β => by
          funext k; dsimp only
          by_cases hk : IsBlkVar k
          · rw [dite_eq_left hk]; exact congrArg β (Classical.choose_spec hk)
          · rw [dite_eq_right hk]
        right_inv := fun ⟨f, g⟩ => Prod.ext
          (by funext ⟨k, hk⟩; dsimp only; rw [dite_eq_right hk])
          (by funext u j; dsimp only
              have hk : IsBlkVar (ι (u, j)) := ⟨(u, j), rfl⟩
              rw [dite_eq_left hk, hι_inj (Classical.choose_spec hk)]) }
    let vOfOut : Out → Fin m → ZMod p := fun α j =>
      L (specBounded (splitEquiv.symm (α, 0)) (R.levels t)[b].basePolys[j] (hdeg_all j))
    have hv_indep : ∀ (β : Fin R.numExtVars → ZMod p) (j : Fin m),
        L (specBounded β (R.levels t)[b].basePolys[j] (hdeg_all j)) =
          vOfOut (splitEquiv β).1 j := fun β j => by
      dsimp only [vOfOut]; congr 1; apply Subtype.ext
      refine specAlgHom_eq_of_vars fun k hk_vars => ?_
      have hnot_blk : ¬ IsBlkVar k := by
        rintro ⟨⟨u, j'⟩, rfl⟩
        have hnot := extVar_notMem_basePoly_vars R t b u j' j
        rw [Classical.choose_spec (R.extVar_is_inr t b u j')] at hnot
        exact hnot hk_vars
      change _ = (if hk : IsBlkVar k then _ else _)
      rw [dite_eq_right hnot_blk]; rfl
    let fiberSet : Out → Finset In := fun α =>
      if _ : ∃ j₀ : Fin m, vOfOut α j₀ ≠ 0 then
        Fintype.piFinset fun _ : Fin R.accuracy =>
          Finset.univ.filter fun δ : Fin m → ZMod p => ∑ j : Fin m, δ j * vOfOut α j ≠ 1
      else ∅
    have hfiber_card : ∀ α : Out, (fiberSet α).card ≤ ((p - 1) * p ^ (m - 1)) ^ R.accuracy := by
      intro α; dsimp only [fiberSet]; split_ifs with hnz
      · obtain ⟨j₀, hj₀⟩ := hnz
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          card_affineHyperplaneCompl_eq j₀ hj₀]
      · simp
    let badPairSet : Finset (Out × In) := (Finset.univ : Finset Out).sigma fiberSet
      |>.map ⟨fun p => (p.1, p.2), fun p₁ p₂ h => Sigma.ext (Prod.ext_iff.mp h).1
        (heq_of_eq (Prod.ext_iff.mp h).2)⟩
    have hbad_le : s_bad.card ≤ badPairSet.card := by
      refine Finset.card_le_card_of_injOn splitEquiv (fun β hβ => ?_)
        fun _ _ _ _ h => splitEquiv.injective h
      rcases hs_bad β (Finset.mem_coe.mp hβ) with ⟨⟨idx, hidx⟩, hall_u⟩
      rw [hv_indep β idx] at hidx
      have hnz : ∃ j₀ : Fin m, vOfOut (splitEquiv β).1 j₀ ≠ 0 := ⟨idx, hidx⟩
      rw [Finset.mem_coe, Finset.mem_map]
      refine ⟨⟨(splitEquiv β).1, (splitEquiv β).2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩,
        rfl⟩
      dsimp only [fiberSet]
      rw [dite_eq_left hnz, Fintype.mem_piFinset]
      intro u
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hsum_eq : (∑ j : Fin m, (splitEquiv β).2 u j * vOfOut (splitEquiv β).1 j) =
          ∑ j : Fin m, β (Classical.choose (R.extVar_is_inr t b u j)) *
            L (specBounded β (R.levels t)[b].basePolys[j] (hdeg_all j)) :=
        Finset.sum_congr rfl fun j _ => by rw [hv_indep β j]; rfl
      rw [hsum_eq]; exact hall_u u
    have hbadPair_card :
        badPairSet.card ≤ Fintype.card Out * ((p - 1) * p ^ (m - 1)) ^ R.accuracy := by
      rw [Finset.card_map, Finset.card_sigma]
      exact (Finset.sum_le_sum fun α _ => hfiber_card α).trans_eq
        (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul])
    have htot_card :
        Fintype.card (Fin R.numExtVars → ZMod p) = Fintype.card Out * (p ^ m) ^ R.accuracy := by
      rw [Fintype.card_congr splitEquiv, Fintype.card_prod]
      congr 1
      rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]
    have hpow_m : p ^ m = p * p ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ']
    calc
      s_bad.card * p ^ R.accuracy
        ≤ (Fintype.card Out * ((p - 1) * p ^ (m - 1)) ^ R.accuracy) * p ^ R.accuracy :=
          Nat.mul_le_mul_right _ (hbad_le.trans hbadPair_card)
      _ = Fintype.card Out * ((p - 1) ^ R.accuracy * (p * p ^ (m - 1)) ^ R.accuracy) := by
          rw [mul_assoc, ← mul_pow]
          exact congrArg (Fintype.card Out * ·)
            (by rw [show (p - 1) * p ^ (m - 1) * p = (p - 1) * (p * p ^ (m - 1)) by ring, mul_pow])
      _ = Fintype.card (Fin R.numExtVars → ZMod p) * (p - 1) ^ R.accuracy := by
          rw [← hpow_m, show Fintype.card Out * ((p - 1) ^ R.accuracy * (p ^ m) ^ R.accuracy) =
            (Fintype.card Out * (p ^ m) ^ R.accuracy) * (p - 1) ^ R.accuracy by ring, htot_card]

private theorem list_sum_map_eq_fin_sum {α : Type*} (L : List α) (f : α → ℕ) :
    (L.map f).sum = ∑ b : Fin L.length, f L[b] := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact ((Fin.sum_univ_succ fun b : Fin (a :: rest).length => f (a :: rest)[b]).trans
      (by simp)).symm

private theorem card_nonemptyBlocks_le_numExtPolys {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) :
    ((Finset.univ : Finset (Σ t : Fin R.numLevels, Fin (R.levels t).length)).filter
      fun tb => 1 ≤ (R.levels tb.1)[tb.2].basePolys.length).card ≤ R.numExtPolys := by
  let allBlocks : Finset (Σ t : Fin R.numLevels, Fin (R.levels t).length) := Finset.univ
  have h1 : (allBlocks.filter fun tb => 1 ≤ (R.levels tb.1)[tb.2].basePolys.length).card ≤
      ∑ tb ∈ allBlocks, (R.levels tb.1)[tb.2].basePolys.length :=
    (Finset.card_eq_sum_ones _).trans_le <|
      (Finset.sum_le_sum fun _ htb => (Finset.mem_filter.mp htb).2).trans
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  have h2 : ∑ tb ∈ allBlocks, (R.levels tb.1)[tb.2].basePolys.length = R.numExtPolys := by
    rw [ENSRefutation.numExtPolys_def]
    have huniv : allBlocks = (Finset.univ : Finset (Fin R.numLevels)).sigma
        fun t => (Finset.univ : Finset (Fin (R.levels t).length)) := by
      ext ⟨t, b⟩; simp [allBlocks]
    rw [huniv, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun t _ =>
      (list_sum_map_eq_fin_sum (R.levels t) fun B => B.basePolys.length).symm
  exact h1.trans_eq h2

private theorem mul_lt_of_exp_bound {p h S N badCard : ℕ} [Fact p.Prime]
    (hS : 1 ≤ S) (hN : 0 < N) (hexp : 2 * (S : ℝ) ^ 2 ≤ Real.exp ((h : ℝ) / (p : ℝ)))
    (hbad : badCard * p ^ h ≤ S * N * (p - 1) ^ h) : badCard * S < N := by
  have hp_prime : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hS_pos : (0 : ℝ) < (S : ℝ) := Nat.cast_pos.mpr hS
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hbad_real : (badCard : ℝ) * (p : ℝ) ^ h ≤ (S : ℝ) * (N : ℝ) * ((p - 1 : ℕ) : ℝ) ^ h := by
    exact_mod_cast hbad
  have hdiv_le : (badCard : ℝ) ≤ (S : ℝ) * (N : ℝ) * (((p - 1 : ℕ) : ℝ) / (p : ℝ)) ^ h := by
    rw [div_pow, ← mul_div_assoc]; exact (le_div_iff₀ (pow_pos hp_pos h)).mpr hbad_real
  have hbase_exp : ((p - 1 : ℕ) : ℝ) / (p : ℝ) ≤ Real.exp (-(1 / (p : ℝ))) := by
    rw [show ((p - 1 : ℕ) : ℝ) / (p : ℝ) = -(1 / (p : ℝ)) + 1 by
      rw [Nat.cast_sub hp_prime.one_lt.le, Nat.cast_one, sub_div, div_self hp_pos.ne']; ring]
    exact Real.add_one_le_exp _
  have hpow_exp : (((p - 1 : ℕ) : ℝ) / (p : ℝ)) ^ h ≤ (2 * (S : ℝ) ^ 2)⁻¹ :=
    ((pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hp_pos.le) hbase_exp h).trans_eq
      (by rw [← Real.exp_nat_mul, show (h : ℝ) * -(1 / (p : ℝ)) = -((h : ℝ) / (p : ℝ)) by ring,
        Real.exp_neg])).trans (inv_anti₀ (by positivity) hexp)
  have hupper : (badCard : ℝ) * (S : ℝ) ≤ (N : ℝ) / 2 := by
    calc (badCard : ℝ) * (S : ℝ)
        ≤ ((S : ℝ) * (N : ℝ) * (2 * (S : ℝ) ^ 2)⁻¹) * (S : ℝ) :=
          mul_le_mul_of_nonneg_right
            (hdiv_le.trans (mul_le_mul_of_nonneg_left hpow_exp (by positivity))) hS_pos.le
      _ = (N : ℝ) / 2 := by have hS_ne := hS_pos.ne'; field_simp [hS_ne]
  exact Nat.cast_lt.mp (by rw [Nat.cast_mul]; linarith : ((badCard * S : ℕ) : ℝ) < (N : ℝ))

end FiberCounting

section MainTheorem

private noncomputable def extAxiomFinset {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) :
    Finset (MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)) :=
  (Finset.univ : Finset (Fin R.numLevels)).biUnion fun t =>
    ((R.levels t).flatMap ExtensionBlock.extPolyList).toFinset

private theorem extAxiomFinset_witness {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    {P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)} (hP : P ∈ extAxiomFinset R) :
    ∃ (t : Fin R.numLevels) (b : Fin (R.levels t).length)
      (idx : Fin (R.levels t)[b].basePolys.length), (R.levels t)[b].extPoly idx = P := by
  rcases Finset.mem_biUnion.mp hP with ⟨t, _, ht⟩
  rcases List.mem_flatMap.mp (List.mem_toFinset.mp ht) with ⟨B, hB, hpoly⟩
  obtain ⟨b, hb_lt, rfl⟩ := List.getElem_of_mem hB
  rw [ExtensionBlock.extPolyList_def, List.mem_map] at hpoly
  rcases hpoly with ⟨idx, _, hEq⟩
  exact ⟨t, ⟨b, hb_lt⟩, idx, hEq⟩

private noncomputable def extWitness {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    {P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)} (hP : P ∈ extAxiomFinset R) :
    (t : Fin R.numLevels) × (b : Fin (R.levels t).length) ×
      Fin (R.levels t)[b].basePolys.length :=
  let w := extAxiomFinset_witness R hP
  let t := Classical.choose w
  let w₁ := Classical.choose_spec w
  let b := Classical.choose w₁
  ⟨t, b, Classical.choose (Classical.choose_spec w₁)⟩

private theorem extWitness_eq {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    {P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)} (hP : P ∈ extAxiomFinset R) :
    (R.levels (extWitness R hP).1)[(extWitness R hP).2.1].extPoly (extWitness R hP).2.2 = P :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (extAxiomFinset_witness R hP)))

private theorem extWitness_coeff_deg {V : Type*} {p d : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    {P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)} (hP : P ∈ extAxiomFinset R) :
    (R.nsRefutation.coeff P *
      (R.levels (extWitness R hP).1)[(extWitness R hP).2.1].extPoly
        (extWitness R hP).2.2).totalDegree ≤ d := by
  have hmem : P ∈ F.image (MvPolynomial.rename Sum.inl) ∪ extAxiomFinset R ∪
      ((Finset.univ : Finset (Fin R.numLevels)).biUnion fun s =>
        ((R.levels s).flatMap (ExtensionBlock.frobeniusList p)).toFinset) :=
    Finset.mem_union_left _ (Finset.mem_union_right _ hP)
  rw [extWitness_eq R hP]
  exact (R.nsRefutation.degree_mul_le hmem).trans (R.degree_def ▸ hd)

private noncomputable def ensContTree {V : Type*} {p d : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    (β : Fin R.numExtVars → ZMod p)
    (P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)) :
    PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d) := by
  classical
  exact if hP : P ∈ extAxiomFinset R then
    blockSearchTree (R.levels (extWitness R hP).1)[(extWitness R hP).2.1]
      (extWitness R hP).2.2 (R.nsRefutation.coeff P) (extWitness_coeff_deg R hd hP) β
  else .leaf (0, 0)

private theorem ensContTree_spec {V : Type*} {p d : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    (β : Fin R.numExtVars → ZMod p) {P : MvPolynomial (V ⊕ Fin R.numExtVars) (ZMod p)}
    (hP : P ∈ extAxiomFinset R) {ω : PolyBoundedDeg V p d → ZMod p}
    {L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p}
    (hLω : ∀ g, ω g = L g) (hL1 : L (PolyBoundedDeg.one V p d) = 1)
    (hLP_nz : L (truncBounded p d (specAlgHom V β (R.nsRefutation.coeff P * P))) ≠ 0)
    (hnc : ¬ IsConflictPair ω ((ensContTree R hd β P).eval ω)) :
    ∃ (t : Fin R.numLevels) (b : Fin (R.levels t).length)
      (hdeg_all : ∀ j : Fin (R.levels t)[b].basePolys.length,
        (R.levels t)[b].basePolys[j].totalDegree ≤ d),
      1 ≤ (R.levels t)[b].basePolys.length ∧ IsBadBlockAssign R L t b hdeg_all β := by
  unfold ensContTree at hnc
  rw [dite_eq_left hP] at hnc
  have hEq := extWitness_eq R hP
  have hcdeg := extWitness_coeff_deg R hd hP
  have hq_nz : L (specBounded β
      (R.nsRefutation.coeff P *
        (R.levels (extWitness R hP).1)[(extWitness R hP).2.1].extPoly (extWitness R hP).2.2)
      hcdeg) ≠ 0 := by
    have hdeg_P : (specAlgHom V β (R.nsRefutation.coeff P * P)).totalDegree ≤ d :=
      (totalDegree_specAlgHom_le β _).trans
        (by rw [congrArg (R.nsRefutation.coeff P * ·) hEq.symm]; exact hcdeg)
    have hsub : specBounded β _ hcdeg =
        truncBounded p d (specAlgHom V β (R.nsRefutation.coeff P * P)) := by
      rw [truncBounded_eq_ofDegLe hdeg_P]
      exact Subtype.ext (by rw [coe_specBounded, coe_ofDegLe, hEq])
    rwa [hsub]
  obtain ⟨hdeg_all, hbad⟩ :=
    blockSearchTree_spec_of_not_conflict R (extWitness R hP).1 (extWitness R hP).2.1
      (extWitness R hP).2.2 (R.nsRefutation.coeff P) hcdeg β hLω hL1 hq_nz hnc
  have hpos : 1 ≤ (R.levels (extWitness R hP).1)[(extWitness R hP).2.1].basePolys.length :=
    Nat.zero_lt_of_lt (extWitness R hP).2.2.isLt
  exact ⟨(extWitness R hP).1, (extWitness R hP).2.1, hdeg_all, hpos, hbad⟩

private noncomputable def ensTree {V : Type*} {p d : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    (β : Fin R.numExtVars → ZMod p) :
    PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d) :=
  binSearchTree
    (fun P => truncBounded p d (specAlgHom V β (R.nsRefutation.coeff P * P)))
    (ensContTree R hd β) (.leaf (0, 0)) (extAxiomFinset R).toList

private theorem list_sum_map_toList {α M : Type*} [AddCommMonoid M]
    (s : Finset α) (f : α → M) : (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl

private theorem sum_extAxiomFinset_eq_one {V : Type*} {p d : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    (β : Fin R.numExtVars → ZMod p) {ω₀ : PolyBoundedDeg V p d → ZMod p}
    (hω₀ : IsLinearDesign (↑F) ω₀) {L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p}
    (hLω : ∀ g, ω₀ g = L g) (hL1 : L (PolyBoundedDeg.one V p d) = 1) :
    ∑ P ∈ extAxiomFinset R,
      L (truncBounded p d (specAlgHom V β (R.nsRefutation.coeff P * P))) = 1 := by
  classical
  have hd_ns : R.nsRefutation.degree ≤ d := R.degree_def ▸ hd
  let All_ax := F.image (MvPolynomial.rename (Sum.inl : V → V ⊕ Fin R.numExtVars)) ∪
    extAxiomFinset R ∪
    ((Finset.univ : Finset (Fin R.numLevels)).biUnion fun t =>
      ((R.levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset)
  have hE_sub : extAxiomFinset R ⊆ All_ax := fun _ hx =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have htot_one :
      ∑ Q ∈ All_ax, truncBounded p d (specAlgHom V β (R.nsRefutation.coeff Q * Q)) =
        PolyBoundedDeg.one V p d := by
    apply Subtype.ext
    rw [Submodule.coe_sum, PolyBoundedDeg.coe_one]
    have hcongr :
        ∑ Q ∈ All_ax, (truncBounded p d (specAlgHom V β (R.nsRefutation.coeff Q * Q))).1 =
          ∑ Q ∈ All_ax, specAlgHom V β (R.nsRefutation.coeff Q * Q) :=
      Finset.sum_congr rfl fun Q hQ => by
        rw [truncBounded_eq_ofDegLe ((totalDegree_specAlgHom_le β _).trans
          ((R.nsRefutation.degree_mul_le hQ).trans hd_ns)), coe_ofDegLe]
    rw [hcongr, ← map_sum]
    dsimp only [All_ax, extAxiomFinset]
    rw [R.nsRefutation.refutes, map_one]
  have hsub_sum :
      ∑ P ∈ extAxiomFinset R,
        L (truncBounded p d (specAlgHom V β (R.nsRefutation.coeff P * P))) =
      ∑ Q ∈ All_ax,
        L (truncBounded p d (specAlgHom V β (R.nsRefutation.coeff Q * Q))) := by
    refine Finset.sum_subset hE_sub fun Q hQ hnot_E => ?_
    have hdeg_Q : (specAlgHom V β (R.nsRefutation.coeff Q * Q)).totalDegree ≤ d :=
      (totalDegree_specAlgHom_le β _).trans ((R.nsRefutation.degree_mul_le hQ).trans hd_ns)
    rcases Finset.mem_union.mp hQ with hFE | hR
    · rcases Finset.mem_union.mp hFE with hF | hE
      · rcases Finset.mem_image.mp hF with ⟨f, hf, hEq⟩
        have hmul_eq : specAlgHom V β (R.nsRefutation.coeff Q * Q) =
            specAlgHom V β (R.nsRefutation.coeff Q) * f := by
          rw [map_mul, ← hEq, specAlgHom_rename_inl]
        have hdeg_f : (specAlgHom V β (R.nsRefutation.coeff Q) * f).totalDegree ≤ d :=
          hmul_eq ▸ hdeg_Q
        rw [truncBounded_eq_ofDegLe hdeg_Q,
          show ofDegLe _ hdeg_Q = ofDegLe _ hdeg_f from Subtype.ext hmul_eq, ← hLω]
        exact vanishes_of_isLinearDesign_mul hω₀ hf hdeg_f
      · exact absurd hE hnot_E
    · rw [map_mul, specAlgHom_frobenius_eq_zero R β hR, mul_zero,
        truncBounded_eq_ofDegLe (by simp),
        show ofDegLe (0 : MvPolynomial V _) _ = 0 from rfl, map_zero]
  rw [hsub_sum, ← map_sum, htot_one, hL1]

/-- An Extended Nullstellensatz refutation `R` of `F` over `ZMod p` of degree at most `d`,
extension size `S = R.numExtPolys`, and accuracy `h = R.accuracy` satisfying
`2 * S ^ 2 ≤ exp (h / p)` rules out any indexed `(d, h + Nat.clog 2 S, S⁻¹)`-pseudo-solution
of `F`. -/
theorem ens_no_indexed_pseudoSolution {V ι : Type*} {p d : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    (hexp : 2 * (R.numExtPolys : ℝ) ^ 2 ≤ Real.exp ((R.accuracy : ℝ) / (p : ℝ)))
    (s : Finset ι) (ω : ι → PolyBoundedDeg V p d → ZMod p) :
    ¬ IsIndexedPseudoSolution (↑F) d
        (R.accuracy + Nat.clog 2 R.numExtPolys) ((R.numExtPolys : ℚ)⁻¹) s ω := by
  classical
  by_cases hS0 : R.numExtPolys = 0
  · exact ns_no_indexed_pseudoSolution (R.toNSRefutationOfZero hS0)
      ((R.degree_toNSRefutationOfZero_le hS0).trans hd) _ s ω
  · intro hps
    rcases (isIndexedPseudoSolution_iff _ _ _ _ _ _).mp hps with ⟨hs_ne, hlin, htree⟩
    have hS_pos : 1 ≤ R.numExtPolys := Nat.pos_of_ne_zero hS0
    have hE_card_le : (extAxiomFinset R).card ≤ R.numExtPolys := by
      rw [ENSRefutation.numExtPolys_def]
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t _ =>
        (List.toFinset_card_le _).trans_eq (by simp [List.length_flatMap]))
    have hextList_ne : (extAxiomFinset R).toList ≠ [] := fun hnil => by
      rcases hs_ne with ⟨i₀, hi₀⟩
      rcases (hlin i₀ hi₀).1 with ⟨L₀, hL₀, hL₀1⟩
      have h1 := sum_extAxiomFinset_eq_one R hd 0 (hlin i₀ hi₀) hL₀ hL₀1
      rw [Finset.toList_eq_nil.mp hnil, Finset.sum_empty] at h1
      exact one_ne_zero h1.symm
    have htree_height : ∀ β, (ensTree R hd β).height ≤ R.accuracy + Nat.clog 2 R.numExtPolys := by
      intro β
      refine (height_binSearchTree_le _ _ _ _ hextList_ne fun P _ => ?_).trans
        (Nat.add_le_add_left (Nat.clog_mono_right 2 (by simpa using hE_card_le)) _)
      unfold ensContTree
      by_cases hP : P ∈ extAxiomFinset R
      · rw [dite_eq_left hP]; exact height_blockSearchTree_le _ _ _ _ β
      · rw [dite_eq_right hP]; simp
    let N_β := Fintype.card (Fin R.numExtVars → ZMod p)
    have hN_pos : 0 < N_β := by
      dsimp only [N_β]; rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      exact pow_pos (Fact.out : p.Prime).pos _
    let badBeta : ι → Finset (Fin R.numExtVars → ZMod p) := fun i =>
      Finset.univ.filter fun β => ¬ IsConflictPair (ω i) ((ensTree R hd β).eval (ω i))
    have hbad_lt : ∀ i ∈ s, (badBeta i).card * R.numExtPolys < N_β := fun i hi => by
      rcases (hlin i hi).1 with ⟨L, hLω, hL1⟩
      let nonemptyBlocks :=
        (Finset.univ : Finset (Σ t : Fin R.numLevels, Fin (R.levels t).length)).filter
          fun tb => 1 ≤ (R.levels tb.1)[tb.2].basePolys.length
      let blockBad : (Σ t : Fin R.numLevels, Fin (R.levels t).length) →
          Finset (Fin R.numExtVars → ZMod p) := fun tb =>
        if hdeg_all : ∀ j : Fin (R.levels tb.1)[tb.2].basePolys.length,
            (R.levels tb.1)[tb.2].basePolys[j].totalDegree ≤ d then
          Finset.univ.filter (IsBadBlockAssign R L tb.1 tb.2 hdeg_all)
        else ∅
      have hbad_sub : badBeta i ⊆ nonemptyBlocks.biUnion blockBad := fun β hβ => by
        have hnc : ¬ IsConflictPair (ω i) ((ensTree R hd β).eval (ω i)) :=
          (Finset.mem_filter.mp hβ).2
        have hlist_sum :
            ((extAxiomFinset R).toList.map fun P =>
              L (truncBounded p d (specAlgHom V β (R.nsRefutation.coeff P * P)))).sum ≠ 0 := by
          rw [list_sum_map_toList, sum_extAxiomFinset_eq_one R hd β (hlin i hi) hLω hL1]
          exact one_ne_zero
        obtain ⟨P, hP_list, hLP_nz, heval_eq⟩ :=
          eval_binSearchTree_exists _ (ensContTree R hd β) (.leaf (0, 0)) hLω _ hlist_sum
        unfold ensTree at hnc; rw [heval_eq] at hnc
        obtain ⟨t, b, hdeg_all, hm1, hbad⟩ :=
          ensContTree_spec R hd β (Finset.mem_toList.mp hP_list) hLω hL1 hLP_nz hnc
        refine Finset.mem_biUnion.mpr ⟨⟨t, b⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm1⟩, ?_⟩
        dsimp only [blockBad]
        rw [dite_eq_left hdeg_all, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hbad⟩
      have hcard_mul :
          (badBeta i).card * p ^ R.accuracy ≤ R.numExtPolys * N_β * (p - 1) ^ R.accuracy := by
        calc (badBeta i).card * p ^ R.accuracy
            ≤ (∑ tb ∈ nonemptyBlocks, (blockBad tb).card) * p ^ R.accuracy :=
              Nat.mul_le_mul_right _
                ((Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le)
          _ = ∑ tb ∈ nonemptyBlocks, (blockBad tb).card * p ^ R.accuracy := Finset.sum_mul _ _ _
          _ ≤ ∑ _tb ∈ nonemptyBlocks, N_β * (p - 1) ^ R.accuracy := by
              refine Finset.sum_le_sum fun tb _ => ?_
              dsimp only [blockBad]; split_ifs with hdeg_all
              · exact card_badBlockAssign_mul_pow_le R L tb.1 tb.2 hdeg_all
                  fun _ h => (Finset.mem_filter.mp h).2
              · simp
          _ ≤ R.numExtPolys * N_β * (p - 1) ^ R.accuracy := by
              rw [Finset.sum_const, smul_eq_mul, mul_assoc]
              exact Nat.mul_le_mul_right _ (card_nonemptyBlocks_le_numExtPolys R)
      exact mul_lt_of_exp_bound hS_pos hN_pos hexp hcard_mul
    let goodIdx : (Fin R.numExtVars → ZMod p) → Finset ι := fun β =>
      s.filter fun i => ¬ IsConflictPair (ω i) ((ensTree R hd β).eval (ω i))
    have hsum_lt :
        ∑ β : Fin R.numExtVars → ZMod p, (goodIdx β).card * R.numExtPolys <
          ∑ _β : Fin R.numExtVars → ZMod p, s.card := by
      have hswap :
          ∑ i ∈ s, (badBeta i).card = ∑ β : Fin R.numExtVars → ZMod p, (goodIdx β).card := by
        simp only [badBeta, goodIdx, Finset.card_filter]; exact Finset.sum_comm
      calc ∑ β : Fin R.numExtVars → ZMod p, (goodIdx β).card * R.numExtPolys
          = ∑ i ∈ s, (badBeta i).card * R.numExtPolys := by
            rw [← Finset.sum_mul, ← hswap, Finset.sum_mul]
        _ < ∑ _i ∈ s, N_β := Finset.sum_lt_sum_of_nonempty hs_ne hbad_lt
        _ = ∑ _β : Fin R.numExtVars → ZMod p, s.card := by
            rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, smul_eq_mul,
              smul_eq_mul, mul_comm]
    have hex_beta :
        ∃ β₀ : Fin R.numExtVars → ZMod p, (goodIdx β₀).card * R.numExtPolys < s.card := by
      by_contra hall; push Not at hall
      exact (not_le_of_gt hsum_lt) (Finset.sum_le_sum fun β _ => hall β)
    obtain ⟨β₀, hβ₀_lt⟩ := hex_beta
    have htree_β₀ := htree (ensTree R hd β₀) (htree_height β₀)
    have hfilter_eq :
        @Finset.filter ι (fun i => ¬ IsConflictPair (ω i) ((ensTree R hd β₀).eval (ω i)))
          (Classical.decPred _) s = goodIdx β₀ := Finset.filter_congr_decidable _ _ _
    dsimp only at htree_β₀; rw [hfilter_eq] at htree_β₀
    have hs_pos : (0 : ℚ) < (s.card : ℚ) := Nat.cast_pos.mpr hs_ne.card_pos
    have hS_qpos : (0 : ℚ) < (R.numExtPolys : ℚ) := Nat.cast_pos.mpr hS_pos
    have hle_q : (s.card : ℚ) ≤ ((goodIdx β₀).card : ℚ) * (R.numExtPolys : ℚ) := by
      have h1 := (inv_le_iff_one_le_mul₀' hS_qpos).mp htree_β₀
      rwa [mul_div_assoc', one_le_div hs_pos, mul_comm] at h1
    have hle_nat : s.card ≤ (goodIdx β₀).card * R.numExtPolys := by exact_mod_cast hle_q
    omega

/-- An Extended Nullstellensatz refutation `R` of `F` over `ZMod p` of degree at most `d`,
extension size `S = R.numExtPolys`, and accuracy `h = R.accuracy` satisfying
`2 * S ^ 2 ≤ exp (h / p)` rules out any `(d, h + Nat.clog 2 S, S⁻¹)`-pseudo-solution of `F`. -/
theorem ens_no_pseudoSolution {V : Type*} {p d : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (hd : R.degree ≤ d)
    (hexp : 2 * (R.numExtPolys : ℝ) ^ 2 ≤ Real.exp ((R.accuracy : ℝ) / (p : ℝ)))
    (Ω : Finset (PolyBoundedDeg V p d → ZMod p)) :
    ¬ IsPseudoSolution (↑F) d
        (R.accuracy + Nat.clog 2 R.numExtPolys) ((R.numExtPolys : ℚ)⁻¹) Ω := by
  rw [isPseudoSolution_iff_isIndexedPseudoSolution]
  exact ens_no_indexed_pseudoSolution R hd hexp Ω id

end MainTheorem

end CslibFrontier.Logic.PL.ENS
