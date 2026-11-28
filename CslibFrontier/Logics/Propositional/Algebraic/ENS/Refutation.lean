/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.ENS.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

import Mathlib.FieldTheory.Finite.Basic

/-!
# Extended Nullstellensatz (ENS) Proof Systems

This module formalizes Nullstellensatz (`NSRefutation`) and stratified Extended Nullstellensatz
(`ENSRefutation`) proof systems over prime fields $\mathbb{F}_p$, including variable renaming,
extension-block padding, zero-level embedding, zero-extension projection, and semantic soundness,
verified under standard Lean axioms.

## Main definitions

- `CslibFrontier.Logic.PL.ENS.NSRefutation`, `CslibFrontier.Logic.PL.ENS.NSRefutation.degree`,
  `CslibFrontier.Logic.PL.ENS.NSRefutation.renameEquiv`,
  `CslibFrontier.Logic.PL.ENS.NSRefutation.toENSRefutation`: Nullstellensatz refutations, degree,
  variable renaming, and canonical embedding into zero-level ENS refutations.
- `CslibFrontier.Logic.PL.ENS.ExtensionBlock`, `CslibFrontier.Logic.PL.ENS.ExtensionBlock.extPoly`,
  `CslibFrontier.Logic.PL.ENS.ExtensionBlock.frobeniusList`: extension polynomial blocks
  $E_{i, \overline{g}} = g_i \prod_{u < h} (1 - \sum_{j < m} r_{u, j} g_j)$ of accuracy $h \ge 1$
  and Frobenius axioms $r^p - r$.
- `CslibFrontier.Logic.PL.ENS.ENSRefutation`,
  `CslibFrontier.Logic.PL.ENS.ENSRefutation.numExtPolys`,
  `CslibFrontier.Logic.PL.ENS.ENSRefutation.degree`,
  `CslibFrontier.Logic.PL.ENS.ENSRefutation.padExtPolys`,
  `CslibFrontier.Logic.PL.ENS.ENSRefutation.toNSRefutationOfZero`: $\ell$-level stratified Extended
  Nullstellensatz refutations, size, degree, padding, and zero-extension projection.

## Main results

- `CslibFrontier.Logic.PL.ENS.NSRefutation.degree_renameEquiv_le`,
  `CslibFrontier.Logic.PL.ENS.NSRefutation.degree_toENSRefutation_le`: degree bounds for NS renaming
  and zero-level ENS embedding.
- `CslibFrontier.Logic.PL.ENS.ENSRefutation.numExtPolys_padExtPolys`,
  `CslibFrontier.Logic.PL.ENS.ENSRefutation.degree_padExtPolys_le`,
  `CslibFrontier.Logic.PL.ENS.ENSRefutation.degree_toNSRefutationOfZero_le`: exact padded extension
  size and degree preservation under padding and zero-extension projection.
- `CslibFrontier.Logic.PL.ENS.ensRefutation_unsatisfiable`,
  `CslibFrontier.Logic.PL.ENS.no_ensRefutation_of_satisfiable_in_field`: semantic soundness of
  stratified ENS refutations over prime fields $\mathbb{F}_p$.
-/

public section

namespace CslibFrontier.Logic.PL.ENS

section NSRefutation

/-- A Nullstellensatz refutation of a finite set of polynomials `F` over `ZMod p` in variables
`V`: a multiplier assignment `coeff` such that `∑ f ∈ F, coeff f * f = 1`. -/
structure NSRefutation {V : Type*} {p : ℕ} (F : Finset (MvPolynomial V (ZMod p))) where
  /-- Polynomial multiplier $h_f \in \mathbb{F}_p[V]$ assigned to each $f \in \mathcal{F}$. -/
  coeff : MvPolynomial V (ZMod p) → MvPolynomial V (ZMod p)
  refutes : ∑ f ∈ F, coeff f * f = 1

namespace NSRefutation

/-- The degree of an NS-refutation, defined as $\max_{f \in \mathcal{F}} \deg(h_f f)$. -/
noncomputable def degree {V : Type*} {p : ℕ} {F : Finset (MvPolynomial V (ZMod p))}
    (R : NSRefutation F) : ℕ :=
  F.sup fun f => (R.coeff f * f).totalDegree

theorem degree_def {V : Type*} {p : ℕ} {F : Finset (MvPolynomial V (ZMod p))}
    (R : NSRefutation F) :
    R.degree = F.sup fun f => (R.coeff f * f).totalDegree := by
  unfold degree; rfl

theorem degree_mul_le {V : Type*} {p : ℕ} {F : Finset (MvPolynomial V (ZMod p))}
    (R : NSRefutation F) {f : MvPolynomial V (ZMod p)} (hf : f ∈ F) :
    (R.coeff f * f).totalDegree ≤ R.degree :=
  Finset.le_sup (f := fun g => (R.coeff g * g).totalDegree) hf

/-- Renaming variables along an equivalence `V ≃ W` preserves NS-refutations and degree. -/
noncomputable def renameEquiv {V W : Type*} {p : ℕ} [DecidableEq W]
    {F : Finset (MvPolynomial V (ZMod p))} (e : V ≃ W) (R : NSRefutation F) :
    NSRefutation (F.image (MvPolynomial.rename e)) where
  coeff g := MvPolynomial.rename e (R.coeff (MvPolynomial.rename e.symm g))
  refutes := by
    rw [Finset.sum_image]
    · have hmap :
          (∑ x ∈ F, MvPolynomial.rename e (R.coeff (MvPolynomial.rename e.symm
            (MvPolynomial.rename e x))) * MvPolynomial.rename e x) =
          MvPolynomial.rename e (∑ x ∈ F, R.coeff x * x) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id,
          AlgHom.id_apply, map_mul]
      rw [hmap, R.refutes, map_one]
    · intro x _ y _ hxy
      exact (MvPolynomial.renameEquiv (ZMod p) e).injective hxy

theorem degree_renameEquiv_le {V W : Type*} {p : ℕ} [DecidableEq W]
    {F : Finset (MvPolynomial V (ZMod p))} (e : V ≃ W) (R : NSRefutation F) :
    (R.renameEquiv e).degree ≤ R.degree := by
  rw [degree, Finset.sup_le_iff]
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨f, hf, rfl⟩
  simp only [renameEquiv]
  rw [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id, AlgHom.id_apply,
    ← map_mul]
  exact (MvPolynomial.totalDegree_rename_le e _).trans (R.degree_mul_le hf)

end NSRefutation

end NSRefutation

section ENSRefutation

/-- A block of companion extension polynomials $E_{i, \overline{g}} := g_i \prod_{u < h}
(1 - \sum_{j < m} r_{u, j} g_j)$ of accuracy `h` with pairwise distinct extension variables
`extVar u j`. -/
structure ExtensionBlock (W : Type*) (p h : ℕ) where
  /-- Base polynomials $\overline{g} = (g_0, \dots, g_{m-1})$ defining the block. -/
  basePolys : List (MvPolynomial W (ZMod p))
  /-- Fresh extension variables $r_{u, j} \in W$ indexed by accuracy $u < h$ and $j < m$. -/
  extVar : Fin h → Fin basePolys.length → W
  extVar_inj : Function.Injective (Function.uncurry extVar)

namespace ExtensionBlock

/-- The `i`-th extension polynomial $E_{i, \overline{g}}$ of a block. -/
noncomputable def extPoly {W : Type*} {p h : ℕ} (B : ExtensionBlock W p h)
    (i : Fin B.basePolys.length) : MvPolynomial W (ZMod p) :=
  B.basePolys[i] *
    ∏ u : Fin h, (1 - ∑ j : Fin B.basePolys.length, MvPolynomial.X (B.extVar u j) * B.basePolys[j])

theorem extPoly_def {W : Type*} {p h : ℕ} (B : ExtensionBlock W p h)
    (i : Fin B.basePolys.length) :
    B.extPoly i =
      B.basePolys[i] *
        ∏ u : Fin h,
          (1 - ∑ j : Fin B.basePolys.length, MvPolynomial.X (B.extVar u j) * B.basePolys[j]) := by
  unfold extPoly; rfl

/-- List of all companion extension polynomials $E_{0, \overline{g}}, \dots, E_{m-1, \overline{g}}$
of a block. -/
noncomputable def extPolyList {W : Type*} {p h : ℕ} (B : ExtensionBlock W p h) :
    List (MvPolynomial W (ZMod p)) :=
  (List.finRange B.basePolys.length).map B.extPoly

theorem extPolyList_def {W : Type*} {p h : ℕ} (B : ExtensionBlock W p h) :
    B.extPolyList = (List.finRange B.basePolys.length).map B.extPoly := by
  unfold extPolyList; rfl

@[simp]
theorem length_extPolyList {W : Type*} {p h : ℕ} (B : ExtensionBlock W p h) :
    B.extPolyList.length = B.basePolys.length := by
  simp [extPolyList]

/-- List of Frobenius polynomials $r_{u, j}^p - r_{u, j}$ for all extension variables in `B`. -/
noncomputable def frobeniusList {W : Type*} (p : ℕ) {h : ℕ} (B : ExtensionBlock W p h) :
    List (MvPolynomial W (ZMod p)) :=
  (List.finRange h).flatMap fun u =>
    (List.finRange B.basePolys.length).map fun j =>
      MvPolynomial.X (B.extVar u j) ^ p - MvPolynomial.X (B.extVar u j)

theorem frobeniusList_def {W : Type*} (p : ℕ) {h : ℕ} (B : ExtensionBlock W p h) :
    B.frobeniusList p =
      (List.finRange h).flatMap fun u =>
        (List.finRange B.basePolys.length).map fun j =>
          MvPolynomial.X (B.extVar u j) ^ p - MvPolynomial.X (B.extVar u j) := by
  unfold frobeniusList; rfl

/-- Map an `ExtensionBlock` along an injective variable map `f : W₁ → W₂`. -/
noncomputable def mapVars {W₁ W₂ : Type*} {p h : ℕ} (f : W₁ → W₂)
    (hf : Function.Injective f) (B : ExtensionBlock W₁ p h) : ExtensionBlock W₂ p h where
  basePolys := B.basePolys.map (MvPolynomial.rename f)
  extVar u j := f (B.extVar u ⟨j.1, by simpa using j.2⟩)
  extVar_inj := by
    rintro ⟨u₁, j₁⟩ ⟨u₂, j₂⟩ hp
    dsimp only [Function.uncurry] at hp
    have heq := B.extVar_inj
      (show Function.uncurry B.extVar (u₁, ⟨j₁.1, by simpa using j₁.2⟩) =
          Function.uncurry B.extVar (u₂, ⟨j₂.1, by simpa using j₂.2⟩) from hf hp)
    exact Prod.ext
      (congrArg (fun x : Fin h × Fin B.basePolys.length => x.1) heq)
      (Fin.ext (congrArg (fun x : Fin h × Fin B.basePolys.length => x.2.1) heq))

@[simp]
theorem length_mapVars_basePolys {W₁ W₂ : Type*} {p h : ℕ} (f : W₁ → W₂)
    (hf : Function.Injective f) (B : ExtensionBlock W₁ p h) :
    (B.mapVars f hf).basePolys.length = B.basePolys.length := by
  simp [mapVars]

theorem extPoly_mapVars {W₁ W₂ : Type*} {p h : ℕ} (f : W₁ → W₂)
    (hf : Function.Injective f) (B : ExtensionBlock W₁ p h)
    (i : Fin (B.mapVars f hf).basePolys.length) :
    (B.mapVars f hf).extPoly i =
      MvPolynomial.rename f (B.extPoly ⟨i.1, (length_mapVars_basePolys f hf B) ▸ i.2⟩) := by
  let i' : Fin B.basePolys.length := ⟨i.1, (length_mapVars_basePolys f hf B) ▸ i.2⟩
  have hi_eq : (B.mapVars f hf).basePolys[i] = MvPolynomial.rename f B.basePolys[i'] := by
    change ((B.mapVars f hf).basePolys)[i.1] = MvPolynomial.rename f B.basePolys[i'.1]
    simp [mapVars, i']
  rw [extPoly, extPoly, hi_eq, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [map_sub, map_one, map_sum]
  congr 1
  refine Finset.sum_bij (fun j _ => (⟨j.1, (length_mapVars_basePolys f hf B) ▸ j.2⟩ :
      Fin B.basePolys.length)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro j₁ _ j₂ _ hjeq
    exact Fin.ext (Fin.mk.inj hjeq)
  · intro j' _
    refine ⟨⟨j'.1, (length_mapVars_basePolys f hf B).symm ▸ j'.2⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro j _
    change MvPolynomial.X (f (B.extVar u ⟨j.1, _⟩)) *
        ((B.mapVars f hf).basePolys)[j.1] =
      MvPolynomial.rename f (MvPolynomial.X (B.extVar u ⟨j.1, _⟩) * B.basePolys[j.1])
    simp [mapVars]

theorem extPolyList_mapVars {W₁ W₂ : Type*} {p h : ℕ} (f : W₁ → W₂)
    (hf : Function.Injective f) (B : ExtensionBlock W₁ p h) :
    (B.mapVars f hf).extPolyList = B.extPolyList.map (MvPolynomial.rename f) := by
  apply List.ext_getElem
  · simp [extPolyList]
  · intro n hn₁ hn₂
    simp only [extPolyList, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    exact extPoly_mapVars f hf B ⟨n, by simpa using hn₁⟩

theorem frobeniusList_mapVars {W₁ W₂ : Type*} (p : ℕ) {h : ℕ} (f : W₁ → W₂)
    (hf : Function.Injective f) (B : ExtensionBlock W₁ p h) :
    (B.mapVars f hf).frobeniusList p = (B.frobeniusList p).map (MvPolynomial.rename f) := by
  simp only [frobeniusList, List.map_flatMap]
  congr 1
  funext u
  simp only [List.map_map]
  have hlen :
      ((List.finRange (B.mapVars f hf).basePolys.length).map fun j =>
          (MvPolynomial.X ((B.mapVars f hf).extVar u j) : MvPolynomial W₂ (ZMod p)) ^ p -
            MvPolynomial.X ((B.mapVars f hf).extVar u j)).length =
      ((List.finRange B.basePolys.length).map
          (MvPolynomial.rename f ∘ fun j =>
            (MvPolynomial.X (B.extVar u j) : MvPolynomial W₁ (ZMod p)) ^ p -
              MvPolynomial.X (B.extVar u j))).length := by
    rw [List.length_map, List.length_finRange, List.length_map, List.length_finRange,
      length_mapVars_basePolys]
  refine List.ext_getElem hlen fun j hj₁ hj₂ => ?_
  rw [List.getElem_map, List.getElem_finRange, List.getElem_map, List.getElem_finRange,
    Function.comp_apply, map_sub, map_pow, MvPolynomial.rename_X]
  rfl

end ExtensionBlock

/-- An Extended Nullstellensatz (ENS) refutation of a finite polynomial system `F` over `ZMod p`,
stratified into `numLevels` levels with accuracy `accuracy ≥ 1` and `numExtVars` extension
variables. -/
structure ENSRefutation {V : Type*} {p : ℕ} [DecidableEq V]
    (F : Finset (MvPolynomial V (ZMod p))) where
  /-- Accuracy parameter $h \ge 1$ of the extension polynomials. -/
  accuracy : ℕ
  accuracy_pos : 1 ≤ accuracy
  /-- Number of stratification levels $\ell$. -/
  numLevels : ℕ
  /-- Total number of extension variable slots $M$. -/
  numExtVars : ℕ
  /-- Stratified lists of extension blocks $\mathcal{E}_0, \dots, \mathcal{E}_{\ell-1}$. -/
  levels : Fin numLevels → List (ExtensionBlock (V ⊕ Fin numExtVars) p accuracy)
  extVar_is_inr :
    ∀ (t : Fin numLevels) (b : Fin (levels t).length)
      (u : Fin accuracy) (j : Fin (levels t)[b].basePolys.length),
      ∃ k : Fin numExtVars, (levels t)[b].extVar u j = Sum.inr k
  extVar_disjoint :
    ∀ {t₁ t₂ : Fin numLevels} {b₁ : Fin (levels t₁).length} {b₂ : Fin (levels t₂).length}
      {u₁ u₂ : Fin accuracy}
      {j₁ : Fin (levels t₁)[b₁].basePolys.length} {j₂ : Fin (levels t₂)[b₂].basePolys.length},
      (levels t₁)[b₁].extVar u₁ j₁ = (levels t₂)[b₂].extVar u₂ j₂ →
        t₁ = t₂ ∧ HEq b₁ b₂ ∧ u₁ = u₂ ∧ HEq j₁ j₂
  stratified :
    ∀ (t : Fin numLevels) (b : Fin (levels t).length)
      (g : MvPolynomial (V ⊕ Fin numExtVars) (ZMod p)),
      g ∈ (levels t)[b].basePolys →
        ∀ w ∈ g.vars,
          (∃ v : V, w = Sum.inl v) ∨
          ∃ (s : Fin numLevels), s < t ∧
            ∃ (b' : Fin (levels s).length) (u : Fin accuracy)
              (j : Fin (levels s)[b'].basePolys.length),
              w = (levels s)[b'].extVar u j
  /-- Underlying Nullstellensatz refutation of
  $F \cup \mathcal{E} \cup \mathcal{R}(\mathcal{E})$. -/
  nsRefutation :
    NSRefutation
      (F.image (MvPolynomial.rename Sum.inl) ∪
        ((Finset.univ : Finset (Fin numLevels)).biUnion fun t =>
          ((levels t).flatMap ExtensionBlock.extPolyList).toFinset) ∪
        ((Finset.univ : Finset (Fin numLevels)).biUnion fun t =>
          ((levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset))

namespace ENSRefutation

/-- Total number of extension polynomials $S$ across all levels of an ENS-refutation. -/
def numExtPolys {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) : ℕ :=
  ∑ t : Fin E.numLevels, ((E.levels t).map fun B => B.basePolys.length).sum

theorem numExtPolys_def {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    E.numExtPolys = ∑ t : Fin E.numLevels, ((E.levels t).map fun B => B.basePolys.length).sum := by
  unfold numExtPolys; rfl

/-- Degree of an ENS-refutation, equal to the degree of its underlying NS-refutation. -/
noncomputable def degree {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) : ℕ :=
  E.nsRefutation.degree

theorem degree_def {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    E.degree = E.nsRefutation.degree := by
  unfold degree; rfl

private def liftExtVar {V : Type*} (M k : ℕ) : V ⊕ Fin M → V ⊕ Fin (M + k)
  | Sum.inl v => Sum.inl v
  | Sum.inr i => Sum.inr (Fin.castAdd k i)

private theorem liftExtVar_injective {V : Type*} (M k : ℕ) :
    Function.Injective (liftExtVar (V := V) M k) := by
  rintro (v₁ | i₁) (v₂ | i₂) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · cases h
  · cases h
  · exact congrArg Sum.inr (Fin.castAdd_injective M k (Sum.inr.inj h))

private theorem liftExtVar_comp_inl {V : Type*} (M k : ℕ) :
    liftExtVar (V := V) M k ∘ Sum.inl = Sum.inl :=
  rfl

private noncomputable def dummyOneBlock (V : Type*) (p M h : ℕ) :
    ExtensionBlock (V ⊕ Fin (M + h)) p h where
  basePolys := [1]
  extVar u _ := Sum.inr ⟨M + u.1, Nat.add_lt_add_left u.2 M⟩
  extVar_inj := by
    rintro ⟨u₁, j₁⟩ ⟨u₂, j₂⟩ heq
    change (Sum.inr ⟨M + u₁.1, _⟩ : V ⊕ Fin (M + h)) = Sum.inr ⟨M + u₂.1, _⟩ at heq
    have hu : M + u₁.1 = M + u₂.1 := Fin.mk.inj (Sum.inr.inj heq)
    have hj₁ : j₁.1 = 0 := by
      have := j₁.2
      simp only [List.length_singleton] at this
      omega
    have hj₂ : j₂.1 = 0 := by
      have := j₂.2
      simp only [List.length_singleton] at this
      omega
    exact Prod.ext (Fin.ext (Nat.add_left_cancel hu)) (Fin.ext (hj₁.trans hj₂.symm))

private noncomputable def addOneLevels {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    Fin (E.numLevels + 1) →
      List (ExtensionBlock (V ⊕ Fin (E.numExtVars + E.accuracy)) p E.accuracy) :=
  Fin.cases [dummyOneBlock V p E.numExtVars E.accuracy]
    fun t =>
      (E.levels t).map
        (ExtensionBlock.mapVars (liftExtVar E.numExtVars E.accuracy)
          (liftExtVar_injective E.numExtVars E.accuracy))

private theorem addOneLevels_zero {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    addOneLevels E 0 = [dummyOneBlock V p E.numExtVars E.accuracy] :=
  rfl

private theorem addOneLevels_succ {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (t : Fin E.numLevels) :
    addOneLevels E t.succ =
      (E.levels t).map
        (ExtensionBlock.mapVars (liftExtVar E.numExtVars E.accuracy)
          (liftExtVar_injective E.numExtVars E.accuracy)) :=
  rfl

private theorem addOneLevels_zero_getElem {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F)
    (b : ℕ) (hb : b < (addOneLevels E 0).length) :
    b = 0 ∧ (addOneLevels E 0)[b] = dummyOneBlock V p E.numExtVars E.accuracy := by
  have hb0 : b = 0 := by rw [addOneLevels_zero, List.length_singleton] at hb; omega
  exact ⟨hb0, by simp [addOneLevels_zero, hb0]⟩

private theorem addOneLevels_succ_getElem {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F)
    (t : Fin E.numLevels) (b : ℕ) (hb : b < (addOneLevels E t.succ).length) :
    ∃ hb' : b < (E.levels t).length,
      (addOneLevels E t.succ)[b] =
        (E.levels t)[b].mapVars (liftExtVar E.numExtVars E.accuracy)
          (liftExtVar_injective E.numExtVars E.accuracy) :=
  ⟨by rwa [addOneLevels_succ, List.length_map] at hb, by simp [addOneLevels_succ]⟩

private theorem extBlock_extVar_congr {W : Type*} {p h : ℕ}
    {B₁ B₂ : ExtensionBlock W p h} (hB : B₁ = B₂)
    (u : Fin h) (j : Fin B₁.basePolys.length) :
    B₁.extVar u j = B₂.extVar u ⟨j.1, hB ▸ j.2⟩ := by
  subst hB; rfl

/-- Appends a single unit-base extension block `[1]` at a fresh bottom level `0` (with zero
multiplier in the NS-refutation), increasing `numExtPolys` by `1` while preserving `accuracy` and
`degree`. -/
noncomputable def addOneExtPoly {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) : ENSRefutation F :=
  let f := liftExtVar (V := V) E.numExtVars E.accuracy
  let hf := liftExtVar_injective (V := V) E.numExtVars E.accuracy
  let oldAxioms :=
    F.image (MvPolynomial.rename Sum.inl) ∪
      ((Finset.univ : Finset (Fin E.numLevels)).biUnion fun t =>
        ((E.levels t).flatMap ExtensionBlock.extPolyList).toFinset) ∪
      ((Finset.univ : Finset (Fin E.numLevels)).biUnion fun t =>
        ((E.levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset)
  let newAxioms :=
    F.image (MvPolynomial.rename Sum.inl) ∪
      ((Finset.univ : Finset (Fin (E.numLevels + 1))).biUnion fun t =>
        ((addOneLevels E t).flatMap ExtensionBlock.extPolyList).toFinset) ∪
      ((Finset.univ : Finset (Fin (E.numLevels + 1))).biUnion fun t =>
        ((addOneLevels E t).flatMap (ExtensionBlock.frobeniusList p)).toFinset)
  have himg_old : oldAxioms.image (MvPolynomial.rename f) ⊆ newAxioms := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    simp only [oldAxioms, Finset.mem_union] at ha
    rcases ha with (ha | ha) | ha
    · rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
      rw [MvPolynomial.rename_rename, liftExtVar_comp_inl E.numExtVars E.accuracy]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
    · rcases Finset.mem_biUnion.mp ha with ⟨t, _, ht⟩
      rw [List.mem_toFinset, List.mem_flatMap] at ht; rcases ht with ⟨B, hB, hpoly⟩
      refine Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨t.succ, Finset.mem_univ _, ?_⟩))
      rw [List.mem_toFinset, List.mem_flatMap, addOneLevels_succ]
      exact ⟨B.mapVars f hf, List.mem_map_of_mem hB,
        (ExtensionBlock.extPolyList_mapVars f hf B).symm ▸ List.mem_map_of_mem hpoly⟩
    · rcases Finset.mem_biUnion.mp ha with ⟨t, _, ht⟩
      rw [List.mem_toFinset, List.mem_flatMap] at ht; rcases ht with ⟨B, hB, hpoly⟩
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t.succ, Finset.mem_univ _, ?_⟩)
      rw [List.mem_toFinset, List.mem_flatMap, addOneLevels_succ]
      exact ⟨B.mapVars f hf, List.mem_map_of_mem hB,
        (ExtensionBlock.frobeniusList_mapVars p f hf B).symm ▸ List.mem_map_of_mem hpoly⟩
  { accuracy := E.accuracy
    accuracy_pos := E.accuracy_pos
    numLevels := E.numLevels + 1
    numExtVars := E.numExtVars + E.accuracy
    levels := addOneLevels E
    extVar_is_inr := by
      refine Fin.cases ?_ ?_
      · intro b u j
        obtain ⟨_, hget⟩ := addOneLevels_zero_getElem E b.1 b.2
        exact ⟨⟨E.numExtVars + u.1, Nat.add_lt_add_left u.2 E.numExtVars⟩,
          extBlock_extVar_congr hget u j⟩
      · intro t b u j
        obtain ⟨hb', hget⟩ := addOneLevels_succ_getElem E t b.1 b.2
        have hj' : j.1 < (E.levels t)[b.1].basePolys.length := by
          have := j.2
          simp only [Fin.getElem_fin, hget, ExtensionBlock.length_mapVars_basePolys] at this
          exact this
        obtain ⟨k, hk⟩ := E.extVar_is_inr t ⟨b.1, hb'⟩ u ⟨j.1, hj'⟩
        refine ⟨Fin.castAdd E.accuracy k, (extBlock_extVar_congr hget u j).trans ?_⟩
        have hk' : (E.levels t)[b.1].extVar u ⟨j.1, hj'⟩ = Sum.inr k := hk
        change liftExtVar E.numExtVars E.accuracy ((E.levels t)[b.1].extVar u ⟨j.1, hj'⟩) = _
        rw [hk']; rfl
    extVar_disjoint := by
      have helper :
          ∀ (t : Fin (E.numLevels + 1)) (b : Fin (addOneLevels E t).length) (u : Fin E.accuracy)
            (j : Fin (addOneLevels E t)[b].basePolys.length),
            (t = 0 ∧ b.1 = 0 ∧
              (addOneLevels E t)[b].extVar u j =
                Sum.inr ⟨E.numExtVars + u.1, Nat.add_lt_add_left u.2 E.numExtVars⟩) ∨
            (∃ (t' : Fin E.numLevels) (hb' : b.1 < (E.levels t').length)
              (hj' : j.1 < (E.levels t')[b.1].basePolys.length),
              t = t'.succ ∧
              (addOneLevels E t)[b].extVar u j =
                f ((E.levels t')[b.1].extVar u ⟨j.1, hj'⟩)) := by
        refine Fin.cases ?_ ?_
        · intro b u j
          obtain ⟨hb0, hget⟩ := addOneLevels_zero_getElem E b.1 b.2
          exact Or.inl ⟨rfl, hb0, extBlock_extVar_congr hget u j⟩
        · intro t' b u j
          obtain ⟨hb', hget⟩ := addOneLevels_succ_getElem E t' b.1 b.2
          have hj' : j.1 < (E.levels t')[b.1].basePolys.length := by
            have := j.2
            simp only [Fin.getElem_fin, hget, ExtensionBlock.length_mapVars_basePolys] at this
            exact this
          exact Or.inr ⟨t', hb', hj', rfl, extBlock_extVar_congr hget u j⟩
      intro t₁ t₂ b₁ b₂ u₁ u₂ j₁ j₂ heq
      rcases helper t₁ b₁ u₁ j₁ with ⟨ht₁0, hb₁0, h₁⟩ | ⟨t₁', hb₁', hj₁', ht₁s, h₁⟩ <;>
        rcases helper t₂ b₂ u₂ j₂ with ⟨ht₂0, hb₂0, h₂⟩ | ⟨t₂', hb₂', hj₂', ht₂s, h₂⟩
      · rw [h₁, h₂] at heq
        have hu_val : u₁.1 = u₂.1 := Nat.add_left_cancel (Fin.mk.inj (Sum.inr.inj heq))
        subst ht₁0; subst ht₂0
        have hb_fin : b₁ = b₂ := Fin.ext (hb₁0.trans hb₂0.symm); subst hb_fin
        have hu_fin : u₁ = u₂ := Fin.ext hu_val; subst hu_fin
        obtain ⟨_, hget⟩ := addOneLevels_zero_getElem E b₁.1 b₁.2
        have hj1 : j₁.1 = 0 := by
          have := j₁.2
          simp only [Fin.getElem_fin, hget, dummyOneBlock, List.length_singleton] at this; omega
        have hj2 : j₂.1 = 0 := by
          have := j₂.2
          simp only [Fin.getElem_fin, hget, dummyOneBlock, List.length_singleton] at this; omega
        have hj_fin : j₁ = j₂ := Fin.ext (hj1.trans hj2.symm); subst hj_fin
        exact ⟨rfl, HEq.rfl, rfl, HEq.rfl⟩
      · rw [h₁, h₂] at heq
        obtain ⟨k₂, hk₂⟩ := E.extVar_is_inr t₂' ⟨b₂.1, hb₂'⟩ u₂ ⟨j₂.1, hj₂'⟩
        have hk₂' : (E.levels t₂')[b₂.1].extVar u₂ ⟨j₂.1, hj₂'⟩ = Sum.inr k₂ := hk₂
        rw [hk₂'] at heq; simp only [f, liftExtVar] at heq
        have := Fin.mk.inj (Sum.inr.inj heq); omega
      · rw [h₁, h₂] at heq
        obtain ⟨k₁, hk₁⟩ := E.extVar_is_inr t₁' ⟨b₁.1, hb₁'⟩ u₁ ⟨j₁.1, hj₁'⟩
        have hk₁' : (E.levels t₁')[b₁.1].extVar u₁ ⟨j₁.1, hj₁'⟩ = Sum.inr k₁ := hk₁
        rw [hk₁'] at heq; simp only [f, liftExtVar] at heq
        have := Fin.mk.inj (Sum.inr.inj heq); omega
      · rw [h₁, h₂] at heq
        have heq_inner :
            (E.levels t₁')[(⟨b₁.1, hb₁'⟩ : Fin (E.levels t₁').length)].extVar u₁ ⟨j₁.1, hj₁'⟩ =
              (E.levels t₂')[(⟨b₂.1, hb₂'⟩ : Fin (E.levels t₂').length)].extVar u₂ ⟨j₂.1, hj₂'⟩ :=
          hf heq
        obtain ⟨ht_eq, hb_heq, hu_eq, hj_heq⟩ := E.extVar_disjoint heq_inner
        subst ht₁s; subst ht₂s; subst ht_eq
        have hb_fin : b₁ = b₂ := Fin.ext (Fin.mk.inj (eq_of_heq hb_heq :
          (⟨b₁.1, hb₁'⟩ : Fin (E.levels t₁').length) = ⟨b₂.1, hb₂'⟩)); subst hb_fin
        subst hu_eq
        have hj_fin : j₁ = j₂ := Fin.ext (Fin.mk.inj (eq_of_heq hj_heq :
          (⟨j₁.1, hj₁'⟩ : Fin (E.levels t₁')[b₁.1].basePolys.length) = ⟨j₂.1, hj₂'⟩)); subst hj_fin
        exact ⟨rfl, HEq.rfl, rfl, HEq.rfl⟩
    stratified := by
      refine Fin.cases ?_ ?_
      · intro b g hg w hw
        obtain ⟨_, hget⟩ := addOneLevels_zero_getElem E b.1 b.2
        simp only [Fin.getElem_fin, hget, dummyOneBlock, List.mem_singleton] at hg
        subst hg
        simp at hw
      · intro t' b g hg w hw
        obtain ⟨hb', hget⟩ := addOneLevels_succ_getElem E t' b.1 b.2
        rw [Fin.getElem_fin, hget] at hg
        change g ∈ List.map (MvPolynomial.rename f) (E.levels t')[b.1].basePolys at hg
        rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
        obtain ⟨w₀, hw₀, rfl⟩ := MvPolynomial.mem_vars_rename f g₀ hw
        rcases E.stratified t' ⟨b.1, hb'⟩ g₀ hg₀ w₀ hw₀ with
          ⟨v, rfl⟩ | ⟨s', hst', b', u, j, rfl⟩
        · exact Or.inl ⟨v, rfl⟩
        · right
          have hb'_len : b'.1 < (addOneLevels E s'.succ).length := by
            rw [addOneLevels_succ, List.length_map]
            exact b'.2
          obtain ⟨_, hgets⟩ := addOneLevels_succ_getElem E s' b'.1 hb'_len
          have hj'_len :
              j.1 < (addOneLevels E s'.succ)[b'.1].basePolys.length := by
            simp only [hgets, ExtensionBlock.length_mapVars_basePolys]
            exact j.2
          refine ⟨s'.succ, Fin.succ_lt_succ_iff.mpr hst', ⟨b'.1, hb'_len⟩, u, ⟨j.1, hj'_len⟩, ?_⟩
          symm
          exact extBlock_extVar_congr hgets u ⟨j.1, hj'_len⟩
    nsRefutation :=
      have hren_inj : Function.Injective (MvPolynomial.rename f :
          MvPolynomial (V ⊕ Fin E.numExtVars) (ZMod p) →
          MvPolynomial (V ⊕ Fin (E.numExtVars + E.accuracy)) (ZMod p)) :=
        MvPolynomial.rename_injective f hf
      { coeff := fun q =>
          if hq : ∃ a ∈ oldAxioms, MvPolynomial.rename f a = q then
            MvPolynomial.rename f (E.nsRefutation.coeff (Classical.choose hq))
          else
            0
        refutes := by
          rw [← Finset.sum_subset himg_old]
          · rw [Finset.sum_image (fun a _ b _ hab => hren_inj hab)]
            have hterm :
                ∀ a ∈ oldAxioms,
                  (if hq : ∃ a' ∈ oldAxioms, MvPolynomial.rename f a' = MvPolynomial.rename f a then
                    MvPolynomial.rename f (E.nsRefutation.coeff (Classical.choose hq))
                  else 0) * MvPolynomial.rename f a =
                  MvPolynomial.rename f (E.nsRefutation.coeff a * a) := by
              intro a ha
              have hex : ∃ a' ∈ oldAxioms, MvPolynomial.rename f a' = MvPolynomial.rename f a :=
                ⟨a, ha, rfl⟩
              rw [dite_eq_left hex]
              have hch : Classical.choose hex = a :=
                hren_inj (Classical.choose_spec hex).2
              rw [hch, map_mul]
            rw [Finset.sum_congr rfl hterm, ← map_sum, E.nsRefutation.refutes, map_one]
          · intro q _ hq_not
            have hnot : ¬ ∃ a ∈ oldAxioms, MvPolynomial.rename f a = q := by
              rintro ⟨a, ha, rfl⟩
              exact hq_not (Finset.mem_image_of_mem _ ha)
            rw [dite_eq_right hnot, zero_mul] } }

theorem accuracy_addOneExtPoly {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    E.addOneExtPoly.accuracy = E.accuracy := by
  rw [addOneExtPoly]

theorem numExtPolys_addOneExtPoly {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    E.addOneExtPoly.numExtPolys = E.numExtPolys + 1 := by
  rw [numExtPolys, addOneExtPoly, Fin.sum_univ_succ]
  have hzero : ((addOneLevels E 0).map fun B => B.basePolys.length).sum = 1 := by
    simp [addOneLevels_zero, dummyOneBlock]
  have hsucc :
      (∑ t : Fin E.numLevels, ((addOneLevels E t.succ).map fun B => B.basePolys.length).sum) =
        E.numExtPolys := by
    rw [numExtPolys]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [addOneLevels_succ, List.map_map]
    congr 1
    ext B
    simp
  rw [hzero, hsucc, Nat.add_comm]

theorem degree_addOneExtPoly_le {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) :
    E.addOneExtPoly.degree ≤ E.degree := by
  rw [degree, addOneExtPoly, NSRefutation.degree, Finset.sup_le_iff]
  intro q _
  dsimp only
  split_ifs with hq
  · obtain ⟨ha_mem, ha_eq⟩ := Classical.choose_spec hq
    have hprod :
        MvPolynomial.rename (liftExtVar E.numExtVars E.accuracy)
            (E.nsRefutation.coeff (Classical.choose hq)) * q =
          MvPolynomial.rename (liftExtVar E.numExtVars E.accuracy)
            (E.nsRefutation.coeff (Classical.choose hq) * Classical.choose hq) := by
      rw [map_mul]
      exact congrArg _ ha_eq.symm
    rw [hprod]
    exact (MvPolynomial.totalDegree_rename_le _ _).trans (E.nsRefutation.degree_mul_le ha_mem)
  · simp

/-- Pads an ENS-refutation to have `E.numExtPolys + k` extension polynomials by appending `k`
unit-base extension blocks without changing `accuracy` or increasing `degree`. -/
noncomputable def padExtPolysAdd {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) : ℕ → ENSRefutation F
  | 0 => E
  | k + 1 => (E.padExtPolysAdd k).addOneExtPoly

@[simp]
theorem accuracy_padExtPolysAdd {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (k : ℕ) :
    (E.padExtPolysAdd k).accuracy = E.accuracy := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padExtPolysAdd, accuracy_addOneExtPoly, ih]

@[simp]
theorem numExtPolys_padExtPolysAdd {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (k : ℕ) :
    (E.padExtPolysAdd k).numExtPolys = E.numExtPolys + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [padExtPolysAdd, numExtPolys_addOneExtPoly, ih, Nat.add_assoc]

theorem degree_padExtPolysAdd_le {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (k : ℕ) :
    (E.padExtPolysAdd k).degree ≤ E.degree := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (degree_addOneExtPoly_le _).trans ih

/-- Pads an ENS-refutation to have `M` extension polynomials for any `E.numExtPolys ≤ M`. -/
noncomputable def padExtPolys {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (M : ℕ) :
    ENSRefutation F :=
  E.padExtPolysAdd (M - E.numExtPolys)

theorem accuracy_padExtPolys {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (M : ℕ) :
    (E.padExtPolys M).accuracy = E.accuracy :=
  accuracy_padExtPolysAdd E (M - E.numExtPolys)

theorem numExtPolys_padExtPolys {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F)
    {M : ℕ} (hM : E.numExtPolys ≤ M) :
    (E.padExtPolys M).numExtPolys = M := by
  rw [padExtPolys, numExtPolys_padExtPolysAdd, Nat.add_sub_of_le hM]

theorem degree_padExtPolys_le {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F) (M : ℕ) :
    (E.padExtPolys M).degree ≤ E.degree :=
  degree_padExtPolysAdd_le E (M - E.numExtPolys)

/-- Projects an ENS-refutation with `0` extension polynomials onto an `NSRefutation F` of at most
the same degree. -/
noncomputable def toNSRefutationOfZero {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F)
    (hzero : E.numExtPolys = 0) : NSRefutation F :=
  let proj : MvPolynomial (V ⊕ Fin E.numExtVars) (ZMod p) →ₐ[ZMod p] MvPolynomial V (ZMod p) :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X fun _ => 0)
  have hproj_inl : ∀ f : MvPolynomial V (ZMod p), proj (MvPolynomial.rename Sum.inl f) = f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [proj]
    | add f g ihf ihg => simp [ihf, ihg]
    | mul_X f v ih => simp [proj, ih]
  have hzero_len : ∀ (t : Fin E.numLevels) (B : ExtensionBlock (V ⊕ Fin E.numExtVars) p E.accuracy),
      B ∈ E.levels t → B.basePolys.length = 0 := by
    intro t B hB
    have hsum_t : ((E.levels t).map fun B => B.basePolys.length).sum = 0 := by
      have hle : ((E.levels t).map fun B => B.basePolys.length).sum ≤ E.numExtPolys :=
        Finset.single_le_sum (f := fun s : Fin E.numLevels =>
          ((E.levels s).map fun B => B.basePolys.length).sum)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    have hmem_le : B.basePolys.length ≤ ((E.levels t).map fun B => B.basePolys.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hB)
    omega
  have hext_empty :
      ((Finset.univ : Finset (Fin E.numLevels)).biUnion fun t =>
        ((E.levels t).flatMap ExtensionBlock.extPolyList).toFinset) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨t, _, ht⟩
    rw [List.mem_toFinset, List.mem_flatMap] at ht
    rcases ht with ⟨B, hB, hpoly⟩
    have hlen := hzero_len t B hB
    simp [ExtensionBlock.extPolyList, hlen] at hpoly
  have hfrob_empty :
      ((Finset.univ : Finset (Fin E.numLevels)).biUnion fun t =>
        ((E.levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨t, _, ht⟩
    rw [List.mem_toFinset, List.mem_flatMap] at ht
    rcases ht with ⟨B, hB, hpoly⟩
    have hlen := hzero_len t B hB
    simp [ExtensionBlock.frobeniusList, hlen] at hpoly
  have href_F :
      ∑ f ∈ F.image (MvPolynomial.rename Sum.inl), E.nsRefutation.coeff f * f = 1 := by
    have href := E.nsRefutation.refutes
    simpa [hext_empty, hfrob_empty] using href
  { coeff := fun f => proj (E.nsRefutation.coeff (MvPolynomial.rename Sum.inl f))
    refutes := by
      have href_proj := congrArg proj href_F
      rw [map_one, map_sum, Finset.sum_image] at href_proj
      · refine (Finset.sum_congr rfl fun f _ => ?_).trans href_proj
        rw [map_mul, hproj_inl f]
      · intro f₁ _ f₂ _ hfeq
        exact MvPolynomial.rename_injective Sum.inl Sum.inl_injective hfeq }

theorem degree_toNSRefutationOfZero_le {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (E : ENSRefutation F)
    (hzero : E.numExtPolys = 0) :
    (E.toNSRefutationOfZero hzero).degree ≤ E.degree := by
  let proj : MvPolynomial (V ⊕ Fin E.numExtVars) (ZMod p) →ₐ[ZMod p] MvPolynomial V (ZMod p) :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X fun _ => 0)
  have hproj_inl : ∀ f : MvPolynomial V (ZMod p), proj (MvPolynomial.rename Sum.inl f) = f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [proj]
    | add f g ihf ihg => simp [ihf, ihg]
    | mul_X f v ih => simp [proj, ih]
  have hdeg_proj : ∀ Q : MvPolynomial (V ⊕ Fin E.numExtVars) (ZMod p),
      (proj Q).totalDegree ≤ Q.totalDegree := by
    intro Q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    have hvar : ∀ w : V ⊕ Fin E.numExtVars,
        ((Sum.elim MvPolynomial.X (fun _ => 0) w : MvPolynomial V (ZMod p))).totalDegree ≤ 1 := by
      rintro (v | _)
      · dsimp only [Sum.elim_inl]
        rcases subsingleton_or_nontrivial (ZMod p) with _ | _
        · rw [Subsingleton.elim (MvPolynomial.X v : MvPolynomial V (ZMod p)) 0]; simp
        · exact (MvPolynomial.totalDegree_X v).le
      · simp
    have hprod : ∀ (a : (V ⊕ Fin E.numExtVars) →₀ ℕ) (t : Finset (V ⊕ Fin E.numExtVars)),
        (∏ w ∈ t, (Sum.elim MvPolynomial.X (fun _ => 0) w :
          MvPolynomial V (ZMod p)) ^ a w).totalDegree ≤ ∑ w ∈ t, a w := by
      intro a t; classical
      induction t using Finset.induction_on with
      | empty => simp
      | insert w t hw ih =>
        rw [Finset.prod_insert hw, Finset.sum_insert hw]
        exact (MvPolynomial.totalDegree_mul _ _).trans
          (Nat.add_le_add ((MvPolynomial.totalDegree_pow _ _).trans
            ((Nat.mul_le_mul_left _ (hvar w)).trans_eq (Nat.mul_one _))) ih)
    have hsum : ∀ s : Finset ((V ⊕ Fin E.numExtVars) →₀ ℕ),
        (∑ m ∈ s, MvPolynomial.C (Q.coeff m) *
          ∏ w ∈ m.support, (Sum.elim MvPolynomial.X (fun _ => 0) w :
            MvPolynomial V (ZMod p)) ^ m w).totalDegree ≤
          s.sup fun m => m.sum fun _ e => e := by
      intro s; classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sup_insert]
        refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ (ih.trans (le_max_right _ _)))
        refine le_trans ?_ (le_max_left _ _)
        exact (MvPolynomial.totalDegree_mul _ _).trans
          (by rw [MvPolynomial.totalDegree_C, zero_add]; exact hprod a a.support)
    exact hsum Q.support
  rw [NSRefutation.degree_def, degree_def, Finset.sup_le_iff]
  intro f hf
  have hmem : MvPolynomial.rename Sum.inl f ∈
      F.image (MvPolynomial.rename Sum.inl) ∪
        ((Finset.univ : Finset (Fin E.numLevels)).biUnion fun t =>
          ((E.levels t).flatMap ExtensionBlock.extPolyList).toFinset) ∪
        ((Finset.univ : Finset (Fin E.numLevels)).biUnion fun t =>
          ((E.levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset) :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf))
  calc
    (proj (E.nsRefutation.coeff (MvPolynomial.rename Sum.inl f)) * f).totalDegree =
        (proj (E.nsRefutation.coeff (MvPolynomial.rename Sum.inl f) *
          MvPolynomial.rename Sum.inl f)).totalDegree := by
      rw [map_mul, hproj_inl f]
    _ ≤ (E.nsRefutation.coeff (MvPolynomial.rename Sum.inl f) *
          MvPolynomial.rename Sum.inl f).totalDegree := hdeg_proj _
    _ ≤ E.nsRefutation.degree := E.nsRefutation.degree_mul_le hmem

end ENSRefutation

end ENSRefutation

section EmbeddingAndSoundness

/-- Embeds a Nullstellensatz refutation `R : NSRefutation F` as a $0$-level, $0$-extension
`ENSRefutation F` of accuracy `h ≥ 1` and at most the same degree. -/
noncomputable def NSRefutation.toENSRefutation {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (h : ℕ) (hh : 1 ≤ h) :
    ENSRefutation F :=
  let e : V ≃ V ⊕ Fin 0 := (Equiv.sumEmpty V (Fin 0)).symm
  have he : (⇑e : V → V ⊕ Fin 0) = Sum.inl := by ext v; simp [e]
  have hset :
      F.image (MvPolynomial.rename Sum.inl) ∪
          ((Finset.univ : Finset (Fin 0)).biUnion fun t =>
            ((Fin.elim0 t : List (ExtensionBlock (V ⊕ Fin 0) p h)).flatMap
              ExtensionBlock.extPolyList).toFinset) ∪
          ((Finset.univ : Finset (Fin 0)).biUnion fun t =>
            ((Fin.elim0 t : List (ExtensionBlock (V ⊕ Fin 0) p h)).flatMap
              (ExtensionBlock.frobeniusList p)).toFinset) =
        F.image (MvPolynomial.rename e) := by simp [he]
  { accuracy := h, accuracy_pos := hh, numLevels := 0, numExtVars := 0, levels := Fin.elim0
    extVar_is_inr := fun t => Fin.elim0 t
    extVar_disjoint := fun {t₁} => Fin.elim0 t₁
    stratified := fun t => Fin.elim0 t
    nsRefutation :=
      { coeff := (R.renameEquiv e).coeff
        refutes := by rw [hset]; exact (R.renameEquiv e).refutes } }

@[simp]
theorem NSRefutation.accuracy_toENSRefutation {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (h : ℕ) (hh : 1 ≤ h) :
    (R.toENSRefutation h hh).accuracy = h := by
  unfold toENSRefutation; rfl

@[simp]
theorem NSRefutation.numLevels_toENSRefutation {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (h : ℕ) (hh : 1 ≤ h) :
    (R.toENSRefutation h hh).numLevels = 0 := by
  unfold toENSRefutation; rfl

@[simp]
theorem NSRefutation.numExtPolys_toENSRefutation {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (h : ℕ) (hh : 1 ≤ h) :
    (R.toENSRefutation h hh).numExtPolys = 0 := by
  rw [ENSRefutation.numExtPolys_def]; change (∑ t : Fin 0, _) = 0; simp

theorem NSRefutation.degree_toENSRefutation_le {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : NSRefutation F) (h : ℕ) (hh : 1 ≤ h) :
    (R.toENSRefutation h hh).degree ≤ R.degree := by
  let e : V ≃ V ⊕ Fin 0 := (Equiv.sumEmpty V (Fin 0)).symm
  have he : (⇑e : V → V ⊕ Fin 0) = Sum.inl := by ext v; simp [e]
  rw [ENSRefutation.degree_def]; unfold toENSRefutation; dsimp only
  rw [NSRefutation.degree_def, Finset.sup_le_iff]
  intro q hq
  simp only [Finset.univ_eq_empty, Finset.biUnion_empty, Finset.union_empty, ← he] at hq
  exact ((R.renameEquiv e).degree_mul_le hq).trans (R.degree_renameEquiv_le e)

private theorem eval_congr_vars {W : Type*} {p : ℕ}
    (g : MvPolynomial W (ZMod p)) {β₁ β₂ : W → ZMod p}
    (h : ∀ w ∈ g.vars, β₁ w = β₂ w) :
    MvPolynomial.eval β₁ g = MvPolynomial.eval β₂ g := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  exact congrArg (· ^ m w) (h w ((MvPolynomial.mem_vars_iff_mem_support w).mpr ⟨m, hm, hw⟩))

private noncomputable def blockExtVal {W : Type*} {p h : ℕ} [Fact p.Prime]
    (B : ExtensionBlock W p h) (prev : W → ZMod p)
    (j : Fin B.basePolys.length) : ZMod p := by
  classical
  exact
    if hnz : ∃ j₀ : Fin B.basePolys.length, MvPolynomial.eval prev B.basePolys[j₀] ≠ 0 then
      if j = Classical.choose hnz then
        (MvPolynomial.eval prev B.basePolys[Classical.choose hnz])⁻¹
      else 0
    else 0

private theorem blockExtVal_congr {W : Type*} {p h : ℕ} [Fact p.Prime]
    {B₁ B₂ : ExtensionBlock W p h} (hB : B₁ = B₂) (prev : W → ZMod p)
    {j₁ : Fin B₁.basePolys.length} {j₂ : Fin B₂.basePolys.length} (hj : HEq j₁ j₂) :
    blockExtVal B₁ prev j₁ = blockExtVal B₂ prev j₂ := by
  cases hB; cases hj; rfl

private theorem eval_extPoly_eq_zero_of_blockExtVal {W : Type*} {p h : ℕ} [Fact p.Prime]
    (hh : 1 ≤ h) (B : ExtensionBlock W p h) (prev β : W → ZMod p)
    (hbase : ∀ j : Fin B.basePolys.length,
      MvPolynomial.eval β B.basePolys[j] = MvPolynomial.eval prev B.basePolys[j])
    (hext : ∀ (u : Fin h) (j : Fin B.basePolys.length),
      β (B.extVar u j) = blockExtVal B prev j)
    (i : Fin B.basePolys.length) :
    MvPolynomial.eval β (B.extPoly i) = 0 := by
  classical
  rw [ExtensionBlock.extPoly_def, map_mul, hbase i]
  by_cases hnz : ∃ j₀ : Fin B.basePolys.length, MvPolynomial.eval prev B.basePolys[j₀] ≠ 0
  · let j₀ : Fin B.basePolys.length := Classical.choose hnz
    have hv₀ : MvPolynomial.eval prev B.basePolys[j₀] ≠ 0 := Classical.choose_spec hnz
    let u₀ : Fin h := ⟨0, hh⟩
    rw [map_prod, Finset.prod_eq_zero (Finset.mem_univ u₀)]
    · simp
    · rw [map_sub, map_one, map_sum]
      have hsum_one :
          (∑ j : Fin B.basePolys.length,
              MvPolynomial.eval β (MvPolynomial.X (B.extVar u₀ j) * B.basePolys[j])) = 1 := by
        rw [Finset.sum_eq_single j₀]
        · rw [map_mul, MvPolynomial.eval_X, hext u₀ j₀, hbase j₀]
          simp only [blockExtVal, dite_eq_left hnz, ite_true, j₀]
          exact inv_mul_cancel₀ hv₀
        · intro j _ hj; rw [map_mul, MvPolynomial.eval_X, hext u₀ j, hbase j]
          simp [blockExtVal, hj, j₀]
        · exact fun hj₀ => False.elim (hj₀ (Finset.mem_univ j₀))
      rw [hsum_one, sub_self]
  · push Not at hnz; rw [hnz i, zero_mul]

private def IsLevelExtVar {V : Type*} {p : ℕ} [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (t : Fin R.numLevels) (w : V ⊕ Fin R.numExtVars) : Prop :=
  ∃ (b : Fin (R.levels t).length) (u : Fin R.accuracy)
    (j : Fin (R.levels t)[b].basePolys.length),
    w = (R.levels t)[b].extVar u j

private noncomputable def extStep {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (t : Fin R.numLevels) (prev : V ⊕ Fin R.numExtVars → ZMod p)
    (w : V ⊕ Fin R.numExtVars) : ZMod p := by
  classical
  exact
    if hw : IsLevelExtVar R t w then
      blockExtVal (R.levels t)[Classical.choose hw] prev
        (Classical.choose (Classical.choose_spec (Classical.choose_spec hw)))
    else prev w

private theorem extStep_self {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F)
    (t : Fin R.numLevels) (prev : V ⊕ Fin R.numExtVars → ZMod p)
    (b : Fin (R.levels t).length) (u : Fin R.accuracy)
    (j : Fin (R.levels t)[b].basePolys.length) :
    extStep R t prev ((R.levels t)[b].extVar u j) =
      blockExtVal (R.levels t)[b] prev j := by
  classical
  have hw : IsLevelExtVar R t ((R.levels t)[b].extVar u j) := ⟨b, u, j, rfl⟩
  dsimp only [extStep]; rw [dite_eq_left hw]
  obtain ⟨_, hb_heq, _, hj_heq⟩ :=
    R.extVar_disjoint (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hw)))
  exact (blockExtVal_congr (congrArg (fun idx => (R.levels t)[idx]) (eq_of_heq hb_heq))
    prev hj_heq).symm

private noncomputable def extAssignUpTo {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (α : V → ZMod p) :
    ℕ → V ⊕ Fin R.numExtVars → ZMod p
  | 0 => Sum.elim α fun _ => 0
  | k + 1 =>
      if hk : k < R.numLevels then extStep R ⟨k, hk⟩ (extAssignUpTo R α k)
      else extAssignUpTo R α k

private theorem extAssignUpTo_inl {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (α : V → ZMod p)
    (k : ℕ) (v : V) :
    extAssignUpTo R α k (Sum.inl v) = α v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [extAssignUpTo]; split_ifs with hk
    · have hnot : ¬ IsLevelExtVar R ⟨k, hk⟩ (Sum.inl v) := by
        rintro ⟨b, u, j, heq⟩; obtain ⟨r, hr⟩ := R.extVar_is_inr ⟨k, hk⟩ b u j
        rw [hr] at heq; cases heq
      dsimp only [extStep]; rw [dite_eq_right hnot, ih]
    · exact ih

private theorem extAssignUpTo_succ_of_ne {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (α : V → ZMod p)
    (s : Fin R.numLevels) (b : Fin (R.levels s).length) (u : Fin R.accuracy)
    (j : Fin (R.levels s)[b].basePolys.length) {m : ℕ} (hms : m ≠ s.1) :
    extAssignUpTo R α (m + 1) ((R.levels s)[b].extVar u j) =
      extAssignUpTo R α m ((R.levels s)[b].extVar u j) := by
  rw [extAssignUpTo]; split_ifs with hm_lv
  · have hnot : ¬ IsLevelExtVar R ⟨m, hm_lv⟩ ((R.levels s)[b].extVar u j) :=
      fun ⟨_, _, _, heq⟩ => hms (congrArg Fin.val (R.extVar_disjoint heq).1).symm
    dsimp only [extStep]; rw [dite_eq_right hnot]
  · rfl

private theorem extAssignUpTo_eq_of_gt {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (α : V → ZMod p)
    (s : Fin R.numLevels) (b : Fin (R.levels s).length) (u : Fin R.accuracy)
    (j : Fin (R.levels s)[b].basePolys.length) :
    ∀ {m : ℕ}, s.1 < m →
      extAssignUpTo R α m ((R.levels s)[b].extVar u j) =
        extAssignUpTo R α (s.1 + 1) ((R.levels s)[b].extVar u j)
  | 0, hm => by omega
  | m + 1, hm => by
    by_cases hms : m = s.1
    · subst hms; rfl
    · exact (extAssignUpTo_succ_of_ne R α s b u j hms).trans
        (extAssignUpTo_eq_of_gt R α s b u j (by omega))

/-- Semantic soundness of Extended Nullstellensatz refutations over a prime field $\mathbb{F}_p$:
if `F` admits an `ENSRefutation`, then no valuation `α : V → ZMod p` vanishes simultaneously on
every polynomial in `F`. -/
theorem ensRefutation_unsatisfiable {V : Type*} {p : ℕ} [Fact p.Prime] [DecidableEq V]
    {F : Finset (MvPolynomial V (ZMod p))} (R : ENSRefutation F) (α : V → ZMod p) :
    ¬ ∀ f ∈ F, MvPolynomial.eval α f = 0 := by
  intro hall
  let β : V ⊕ Fin R.numExtVars → ZMod p := extAssignUpTo R α R.numLevels
  have hβ_inl : ∀ v : V, β (Sum.inl v) = α v := extAssignUpTo_inl R α R.numLevels
  have hβ_ext :
      ∀ (t : Fin R.numLevels) (b : Fin (R.levels t).length) (u : Fin R.accuracy)
        (j : Fin (R.levels t)[b].basePolys.length),
        β ((R.levels t)[b].extVar u j) =
          blockExtVal (R.levels t)[b] (extAssignUpTo R α t.1) j := fun t b u j => by
    rw [show β ((R.levels t)[b].extVar u j) =
        extAssignUpTo R α (t.1 + 1) ((R.levels t)[b].extVar u j) from
      extAssignUpTo_eq_of_gt R α t b u j t.2, extAssignUpTo, dite_eq_left t.2]
    exact extStep_self R t (extAssignUpTo R α t.1) b u j
  have hβ_base :
      ∀ (t : Fin R.numLevels) (b : Fin (R.levels t).length)
        (j : Fin (R.levels t)[b].basePolys.length),
        MvPolynomial.eval β (R.levels t)[b].basePolys[j] =
          MvPolynomial.eval (extAssignUpTo R α t.1) (R.levels t)[b].basePolys[j] := fun t b j => by
    refine eval_congr_vars _ fun w hw => ?_
    rcases R.stratified t b _ (List.getElem_mem j.2) w hw with ⟨v, rfl⟩ | ⟨s, hst, b', u', j', rfl⟩
    · rw [hβ_inl, extAssignUpTo_inl]
    · exact (extAssignUpTo_eq_of_gt R α s b' u' j' s.2).trans
        (extAssignUpTo_eq_of_gt R α s b' u' j' (Fin.lt_def.mp hst)).symm
  let allAxioms :=
    F.image (MvPolynomial.rename Sum.inl) ∪
      ((Finset.univ : Finset (Fin R.numLevels)).biUnion fun t =>
        ((R.levels t).flatMap ExtensionBlock.extPolyList).toFinset) ∪
      ((Finset.univ : Finset (Fin R.numLevels)).biUnion fun t =>
        ((R.levels t).flatMap (ExtensionBlock.frobeniusList p)).toFinset)
  have hvanish : ∀ q ∈ allAxioms, MvPolynomial.eval β q = 0 := by
    intro q hq; simp only [allAxioms, Finset.mem_union] at hq
    rcases hq with (hq | hq) | hq
    · rcases Finset.mem_image.mp hq with ⟨f, hf, rfl⟩
      rw [MvPolynomial.eval_rename, show β ∘ Sum.inl = α from funext hβ_inl]; exact hall f hf
    · rcases Finset.mem_biUnion.mp hq with ⟨t, _, ht⟩
      rw [List.mem_toFinset, List.mem_flatMap] at ht
      rcases ht with ⟨B, hB, hpoly⟩
      obtain ⟨b_idx, hb_idx, rfl⟩ := List.getElem_of_mem hB
      rw [ExtensionBlock.extPolyList_def, List.mem_map] at hpoly
      rcases hpoly with ⟨i, _, rfl⟩
      exact eval_extPoly_eq_zero_of_blockExtVal R.accuracy_pos (R.levels t)[(⟨b_idx, hb_idx⟩ :
        Fin (R.levels t).length)] (extAssignUpTo R α t.1) β
        (hβ_base t ⟨b_idx, hb_idx⟩) (hβ_ext t ⟨b_idx, hb_idx⟩) i
    · rcases Finset.mem_biUnion.mp hq with ⟨_, _, ht⟩
      rw [List.mem_toFinset, List.mem_flatMap] at ht
      rcases ht with ⟨B, _, hpoly⟩
      rw [ExtensionBlock.frobeniusList_def, List.mem_flatMap] at hpoly
      rcases hpoly with ⟨_, _, hj⟩
      rcases List.mem_map.mp hj with ⟨_, _, rfl⟩
      rw [map_sub, map_pow, MvPolynomial.eval_X, ZMod.pow_card, sub_self]
  have href := congrArg (MvPolynomial.eval β) R.nsRefutation.refutes
  rw [map_one, map_sum, Finset.sum_eq_zero (fun q hq => by rw [map_mul, hvanish q hq, mul_zero])]
    at href
  exact zero_ne_one href

/-- If a finite polynomial system `F` over $\mathbb{F}_p$ has a common root in $\mathbb{F}_p$,
then `F` admits no `ENSRefutation`. -/
theorem no_ensRefutation_of_satisfiable_in_field {V : Type*} {p : ℕ} [Fact p.Prime]
    [DecidableEq V] {F : Finset (MvPolynomial V (ZMod p))}
    (hsat : ∃ α : V → ZMod p, ∀ f ∈ F, MvPolynomial.eval α f = 0) :
    IsEmpty (ENSRefutation F) :=
  ⟨fun R =>
    let ⟨α, hα⟩ := hsat
    ensRefutation_unsatisfiable R α hα⟩

end EmbeddingAndSoundness

end CslibFrontier.Logic.PL.ENS
