/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.ENS.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs

/-!
# Polynomial Query Decision Trees and Pseudo-Solutions

This module formalizes $p$-ary query decision trees over the bounded-degree polynomial space
$\mathbb{F}_p^{\le d}[V]$, root-to-leaf path combinatorics, uniform-height padding, conflict pairs,
linear designs, and $(d, e, \gamma)$-pseudo-solutions of polynomial systems over $\mathbb{F}_p$,
verified under standard Lean axioms.

## Main definitions

- `CslibFrontier.Logic.PL.ENS.PolyDecisionTree`,
  `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.height`,
  `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.IsUniformHeight`,
  `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.eval`,
  `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.padToHeight`: finite $p$-ary query trees over
  `PolyBoundedDeg V p d`, height, uniform-height predicate, evaluation, and uniform-height padding.
- `CslibFrontier.Logic.PL.ENS.TreePath`, `CslibFrontier.Logic.PL.ENS.TreePath.label`,
  `CslibFrontier.Logic.PL.ENS.TreePath.length`,
  `CslibFrontier.Logic.PL.ENS.TreePath.constraintPolys`,
  `CslibFrontier.Logic.PL.ENS.TreePath.follows`: root-to-leaf paths, leaf labels, edge lengths,
  query-constraint polynomials, and path-following predicate.
- `CslibFrontier.Logic.PL.ENS.IsConflictPair`, `CslibFrontier.Logic.PL.ENS.IsLinearDesign`,
  `CslibFrontier.Logic.PL.ENS.IsPseudoSolution`: conflict pairs, linear designs, and
  $(d, e, \gamma)$-pseudo-solutions of polynomial systems.

## Main results

- `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.height_eq_of_isUniformHeight`,
  `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.eval_padToHeight`,
  `CslibFrontier.Logic.PL.ENS.PolyDecisionTree.isUniformHeight_padToHeight`: height and padding
  properties of polynomial decision trees.
- `CslibFrontier.Logic.PL.ENS.TreePath.existsUnique_follows`,
  `CslibFrontier.Logic.PL.ENS.TreePath.follows_iff_vanishes_constraintPolys`,
  `CslibFrontier.Logic.PL.ENS.TreePath.card_eq_pow_of_isUniformHeight`: unique path realization,
  linear-constraint equivalence, and exact path count $p^e$ for uniform-height trees.
-/

public section

namespace CslibFrontier.Logic.PL.ENS

section PolyDecisionTree

/-- A finite $p$-ary decision tree querying polynomials in `PolyBoundedDeg V p d` with leaf
labels in `I`. -/
inductive PolyDecisionTree (V : Type*) (p d : ℕ) (I : Type*) : Type _ where
  | leaf (label : I) : PolyDecisionTree V p d I
  | node (query : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I) :
      PolyDecisionTree V p d I

namespace PolyDecisionTree

/-- Height of a polynomial decision tree, defined as the maximum number of edges on a root-to-leaf
path. -/
def height {V : Type*} {p d : ℕ} [NeZero p] {I : Type*} :
    PolyDecisionTree V p d I → ℕ
  | .leaf _ => 0
  | .node _ branch => 1 + Finset.univ.sup fun a => (branch a).height

@[simp]
theorem height_leaf {V : Type*} {p d : ℕ} [NeZero p] {I : Type*} (l : I) :
    (leaf l : PolyDecisionTree V p d I).height = 0 := by
  rfl

@[simp]
theorem height_node {V : Type*} {p d : ℕ} [NeZero p] {I : Type*}
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I) :
    (node g branch).height = 1 + Finset.univ.sup fun a => (branch a).height := by
  rfl

/-- Predicate asserting that every root-to-leaf path in `T` has length `e`. -/
def IsUniformHeight {V : Type*} {p d : ℕ} {I : Type*} (e : ℕ) :
    PolyDecisionTree V p d I → Prop
  | .leaf _ => e = 0
  | .node _ branch => ∃ e', e = e' + 1 ∧ ∀ a : ZMod p, (branch a).IsUniformHeight e'

@[simp]
theorem isUniformHeight_leaf_iff {V : Type*} {p d : ℕ} {I : Type*} (e : ℕ) (l : I) :
    (leaf l : PolyDecisionTree V p d I).IsUniformHeight e ↔ e = 0 :=
  Iff.rfl

theorem isUniformHeight_node_iff {V : Type*} {p d : ℕ} {I : Type*} (e : ℕ)
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I) :
    (node g branch).IsUniformHeight e ↔
      ∃ e', e = e' + 1 ∧ ∀ a : ZMod p, (branch a).IsUniformHeight e' :=
  Iff.rfl

theorem height_eq_of_isUniformHeight {V : Type*} {p d : ℕ} [NeZero p] {I : Type*}
    {T : PolyDecisionTree V p d I} {e : ℕ} (hT : T.IsUniformHeight e) :
    T.height = e := by
  induction T generalizing e with
  | leaf l =>
    rw [isUniformHeight_leaf_iff] at hT
    rw [height_leaf, hT]
  | node g branch ih =>
    rcases hT with ⟨e', rfl, hbr⟩
    rw [height_node]
    have hsup : (Finset.univ.sup fun a : ZMod p => (branch a).height) = e' := by
      apply le_antisymm
      · refine Finset.sup_le fun a _ => ?_
        exact le_of_eq (ih a (hbr a))
      · exact le_trans (le_of_eq (ih 0 (hbr 0)).symm)
          (Finset.le_sup (f := fun a : ZMod p => (branch a).height) (Finset.mem_univ (0 : ZMod p)))
    rw [hsup, Nat.add_comm]

/-- Leaf label reached in `T` by answering every polynomial query according to `ω`. -/
def eval {V : Type*} {p d : ℕ} {I : Type*} (ω : PolyBoundedDeg V p d → ZMod p) :
    PolyDecisionTree V p d I → I
  | .leaf l => l
  | .node g branch => (branch (ω g)).eval ω

@[simp]
theorem eval_leaf {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p) (l : I) :
    (leaf l : PolyDecisionTree V p d I).eval ω = l := by
  rfl

@[simp]
theorem eval_node {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p)
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I) :
    (node g branch).eval ω = (branch (ω g)).eval ω := by
  rfl

private noncomputable def dummyTree (V : Type*) (p d : ℕ) {I : Type*} (l : I) :
    ℕ → PolyDecisionTree V p d I
  | 0 => .leaf l
  | k + 1 => .node (PolyBoundedDeg.one V p d) fun _ => dummyTree V p d l k

private theorem eval_dummyTree {V : Type*} {p d : ℕ} {I : Type*} (l : I)
    (ω : PolyBoundedDeg V p d → ZMod p) :
    ∀ k : ℕ, (dummyTree V p d l k).eval ω = l
  | 0 => rfl
  | k + 1 => eval_dummyTree l ω k

private theorem isUniformHeight_dummyTree {V : Type*} {p d : ℕ} {I : Type*} (l : I) :
    ∀ k : ℕ, (dummyTree V p d l k).IsUniformHeight k
  | 0 => rfl
  | k + 1 => ⟨k, rfl, fun _ => isUniformHeight_dummyTree l k⟩

/-- Pads a polynomial decision tree `T` with dummy unit queries so that every root-to-leaf path of
length at most `e'` is extended to exact length `e'`. -/
noncomputable def padToHeight {V : Type*} {p d : ℕ} {I : Type*} :
    ℕ → PolyDecisionTree V p d I → PolyDecisionTree V p d I
  | e', .leaf l => dummyTree V p d l e'
  | 0, .node g br => .node g br
  | e' + 1, .node g br => .node g fun a => padToHeight e' (br a)

@[simp]
theorem eval_padToHeight {V : Type*} {p d : ℕ} {I : Type*} (e' : ℕ)
    (T : PolyDecisionTree V p d I) (ω : PolyBoundedDeg V p d → ZMod p) :
    (padToHeight e' T).eval ω = T.eval ω := by
  induction T generalizing e' with
  | leaf l => rw [padToHeight, eval_leaf]; exact eval_dummyTree l ω e'
  | node g br ih =>
    cases e' with
    | zero => rw [padToHeight]
    | succ k => rw [padToHeight, eval_node]; exact ih (ω g) k

/-- Every polynomial decision tree `T` of height at most `e'` becomes uniform of height `e'`
after `padToHeight e' T`. -/
theorem isUniformHeight_padToHeight {V : Type*} {p d : ℕ} [NeZero p] {I : Type*}
    {T : PolyDecisionTree V p d I} {e' : ℕ} (hT : T.height ≤ e') :
    (padToHeight e' T).IsUniformHeight e' := by
  induction T generalizing e' with
  | leaf l => rw [padToHeight]; exact isUniformHeight_dummyTree l e'
  | node g br ih =>
    cases e' with
    | zero => rw [height_node] at hT; omega
    | succ k =>
      rw [height_node] at hT; rw [padToHeight]
      refine ⟨k, rfl, fun a => ih a ?_⟩
      have ha := Finset.le_sup (f := fun x : ZMod p => (br x).height) (Finset.mem_univ a)
      omega

end PolyDecisionTree

end PolyDecisionTree

/-- A root-to-leaf path in a polynomial decision tree `T`. -/
inductive TreePath {V : Type*} {p d : ℕ} {I : Type*} :
    PolyDecisionTree V p d I → Type _ where
  | nil (label : I) : TreePath (.leaf label)
  | cons (query : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I)
      (ans : ZMod p) (rest : TreePath (branch ans)) :
      TreePath (.node query branch)

namespace TreePath

/-- The leaf label at the end of a root-to-leaf path `P`. -/
def label {V : Type*} {p d : ℕ} {I : Type*} :
    {T : PolyDecisionTree V p d I} → TreePath T → I
  | _, .nil l => l
  | _, .cons _ _ _ rest => rest.label

@[simp]
theorem label_nil {V : Type*} {p d : ℕ} {I : Type*} (l : I) :
    (nil l : TreePath (.leaf l : PolyDecisionTree V p d I)).label = l := by
  rfl

@[simp]
theorem label_cons {V : Type*} {p d : ℕ} {I : Type*}
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I)
    (a : ZMod p) (rest : TreePath (branch a)) :
    (cons g branch a rest).label = rest.label := by
  rfl

/-- Number of edges along a root-to-leaf path `P`. -/
def length {V : Type*} {p d : ℕ} {I : Type*} :
    {T : PolyDecisionTree V p d I} → TreePath T → ℕ
  | _, .nil _ => 0
  | _, .cons _ _ _ rest => rest.length + 1

@[simp]
theorem length_nil {V : Type*} {p d : ℕ} {I : Type*} (l : I) :
    (nil l : TreePath (.leaf l : PolyDecisionTree V p d I)).length = 0 := by
  rfl

@[simp]
theorem length_cons {V : Type*} {p d : ℕ} {I : Type*}
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I)
    (a : ZMod p) (rest : TreePath (branch a)) :
    (cons g branch a rest).length = rest.length + 1 := by
  rfl

theorem length_le_height {V : Type*} {p d : ℕ} [NeZero p] {I : Type*} :
    {T : PolyDecisionTree V p d I} → (P : TreePath T) → P.length ≤ T.height
  | _, .nil _ => le_rfl
  | _, .cons _ branch a rest => by
    rw [length_cons, PolyDecisionTree.height_node]
    have h1 := length_le_height rest
    have h2 : (branch a).height ≤ Finset.univ.sup fun x : ZMod p => (branch x).height :=
      Finset.le_sup (f := fun x : ZMod p => (branch x).height) (Finset.mem_univ a)
    omega

theorem length_eq_of_isUniformHeight {V : Type*} {p d : ℕ} {I : Type*} :
    {T : PolyDecisionTree V p d I} → {e : ℕ} → T.IsUniformHeight e →
      (P : TreePath T) → P.length = e
  | _, _, hT, .nil _ => by
    rw [PolyDecisionTree.isUniformHeight_leaf_iff] at hT
    exact hT.symm
  | _, _, hT, .cons _ _ a rest => by
    rcases hT with ⟨e', rfl, hbr⟩
    rw [length_cons, length_eq_of_isUniformHeight (hbr a) rest]

/-- The list of constraint polynomials `g - C a` collected along the edges of `P`. -/
noncomputable def constraintPolys {V : Type*} {p d : ℕ} {I : Type*} :
    {T : PolyDecisionTree V p d I} → TreePath T → List (PolyBoundedDeg V p d)
  | _, .nil _ => []
  | _, .cons g _ a rest => (g - PolyBoundedDeg.const V p d a) :: rest.constraintPolys

@[simp]
theorem constraintPolys_nil {V : Type*} {p d : ℕ} {I : Type*} (l : I) :
    (nil l : TreePath (.leaf l : PolyDecisionTree V p d I)).constraintPolys = [] := by
  rfl

@[simp]
theorem constraintPolys_cons {V : Type*} {p d : ℕ} {I : Type*}
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I)
    (a : ZMod p) (rest : TreePath (branch a)) :
    (cons g branch a rest).constraintPolys =
      (g - PolyBoundedDeg.const V p d a) :: rest.constraintPolys := by
  rfl

@[simp]
theorem length_constraintPolys {V : Type*} {p d : ℕ} {I : Type*} :
    {T : PolyDecisionTree V p d I} → (P : TreePath T) → P.constraintPolys.length = P.length
  | _, .nil _ => rfl
  | _, .cons _ _ _ rest => by
    rw [constraintPolys_cons, List.length_cons, length_cons, length_constraintPolys rest]

/-- Predicate asserting that assignment `ω` follows every query-answer edge of path `P`. -/
def follows {V : Type*} {p d : ℕ} {I : Type*} (ω : PolyBoundedDeg V p d → ZMod p) :
    {T : PolyDecisionTree V p d I} → TreePath T → Prop
  | _, .nil _ => True
  | _, .cons g _ a rest => ω g = a ∧ rest.follows ω

@[simp]
theorem follows_nil {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p) (l : I) :
    (nil l : TreePath (.leaf l : PolyDecisionTree V p d I)).follows ω :=
  trivial

theorem follows_cons_iff {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p)
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I)
    (a : ZMod p) (rest : TreePath (branch a)) :
    (cons g branch a rest).follows ω ↔ ω g = a ∧ rest.follows ω :=
  Iff.rfl

/-- Canonical path in `T` induced by answering queries with `ω`. -/
def ofMap {V : Type*} {p d : ℕ} {I : Type*} (ω : PolyBoundedDeg V p d → ZMod p) :
    (T : PolyDecisionTree V p d I) → TreePath T
  | .leaf l => .nil l
  | .node g branch => .cons g branch (ω g) (ofMap ω (branch (ω g)))

theorem follows_ofMap {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p) (T : PolyDecisionTree V p d I) :
    (ofMap ω T).follows ω := by
  induction T with
  | leaf _ => exact trivial
  | node g _ ih => exact ⟨rfl, ih (ω g)⟩

theorem label_ofMap {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p) (T : PolyDecisionTree V p d I) :
    (ofMap ω T).label = T.eval ω := by
  induction T with
  | leaf _ => rfl
  | node g _ ih => exact ih (ω g)

theorem eq_ofMap_of_follows {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p) :
    {T : PolyDecisionTree V p d I} → {P : TreePath T} → P.follows ω → P = ofMap ω T
  | _, .nil _, _ => rfl
  | _, .cons g branch a rest, hP => by
    rcases hP with ⟨ha, hrest⟩
    subst ha
    rw [ofMap, eq_ofMap_of_follows ω hrest]

theorem existsUnique_follows {V : Type*} {p d : ℕ} {I : Type*}
    (ω : PolyBoundedDeg V p d → ZMod p) (T : PolyDecisionTree V p d I) :
    ∃! P : TreePath T, P.follows ω :=
  ⟨ofMap ω T, follows_ofMap ω T, fun _ hP => eq_ofMap_of_follows ω hP⟩

theorem follows_iff_vanishes_constraintPolys {V : Type*} {p d : ℕ} {I : Type*}
    (L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p)
    (hL1 : L (PolyBoundedDeg.one V p d) = 1) :
    {T : PolyDecisionTree V p d I} → (P : TreePath T) →
      (P.follows L ↔ ∀ q ∈ P.constraintPolys, L q = 0)
  | _, .nil _ => by simp
  | _, .cons g _ a rest => by
    rw [follows_cons_iff, constraintPolys_cons, List.forall_mem_cons,
      follows_iff_vanishes_constraintPolys L hL1 rest, and_congr_left_iff]
    intro _
    rw [map_sub, PolyBoundedDeg.const_eq_smul_one, map_smul, hL1, smul_eq_mul, mul_one,
      sub_eq_zero]

/-- Decomposition equivalence for paths in a branching node. -/
def consEquiv {V : Type*} {p d : ℕ} {I : Type*}
    (g : PolyBoundedDeg V p d) (branch : ZMod p → PolyDecisionTree V p d I) :
    TreePath (.node g branch) ≃ Σ a : ZMod p, TreePath (branch a) where
  toFun
    | .cons _ _ a rest => ⟨a, rest⟩
  invFun p := .cons g branch p.1 p.2
  left_inv
    | .cons _ _ _ _ => rfl
  right_inv _ := rfl

/-- Equivalence identifying paths in a leaf tree with `Unit`. -/
def leafEquiv {V : Type*} {p d : ℕ} {I : Type*} (l : I) :
    TreePath (.leaf l : PolyDecisionTree V p d I) ≃ Unit where
  toFun
    | .nil _ => ()
  invFun _ := .nil l
  left_inv
    | .nil _ => rfl
  right_inv _ := rfl

noncomputable instance instFintype {V : Type*} {p d : ℕ} [NeZero p] {I : Type*} :
    (T : PolyDecisionTree V p d I) → Fintype (TreePath T)
  | .leaf l => Fintype.ofEquiv Unit (leafEquiv l).symm
  | .node g branch =>
    let _ : ∀ a : ZMod p, Fintype (TreePath (branch a)) := fun a => instFintype (branch a)
    Fintype.ofEquiv (Σ a : ZMod p, TreePath (branch a)) (consEquiv g branch).symm

/-- Every `p`-ary polynomial decision tree of uniform height `e` has exactly `p ^ e` root-to-leaf
paths. -/
theorem card_eq_pow_of_isUniformHeight {V : Type*} {p d : ℕ} [NeZero p] {I : Type*} :
    (T : PolyDecisionTree V p d I) → {e : ℕ} → T.IsUniformHeight e →
      Fintype.card (TreePath T) = p ^ e
  | .leaf l, e, hT => by
    rw [PolyDecisionTree.isUniformHeight_leaf_iff] at hT
    subst hT
    rw [Fintype.card_congr (leafEquiv l), Fintype.card_unit, pow_zero]
  | .node g branch, e, hT => by
    rcases hT with ⟨e', rfl, hbr⟩
    let _ : ∀ a : ZMod p, Fintype (TreePath (branch a)) := fun a => instFintype (branch a)
    rw [Fintype.card_congr (consEquiv g branch), Fintype.card_sigma]
    have hcard : ∀ a : ZMod p, Fintype.card (TreePath (branch a)) = p ^ e' :=
      fun a => card_eq_pow_of_isUniformHeight (branch a) (hbr a)
    simp_rw [hcard]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, pow_succ']

end TreePath

section PseudoSolution

/-- A pair `(g, g')` of polynomials in `PolyBoundedDeg V p d` is a *conflict pair* for `ω` if
`deg(g * g') ≤ d` yet `ω(g) * ω(g') ≠ ω(g * g')`. -/
@[expose] def IsConflictPair {V : Type*} {p d : ℕ}
    (ω : PolyBoundedDeg V p d → ZMod p)
    (pair : PolyBoundedDeg V p d × PolyBoundedDeg V p d) : Prop :=
  ∃ hdeg : (pair.1.1 * pair.2.1).totalDegree ≤ d,
    ω pair.1 * ω pair.2 ≠
      ω ⟨pair.1.1 * pair.2.1,
        (MvPolynomial.mem_restrictTotalDegree V d (pair.1.1 * pair.2.1)).mpr hdeg⟩

/-- An $\mathbb{F}_p$-linear design on `PolyBoundedDeg V p d` vanishing on all degree-`≤ d` ideal
multiples `f * g` of a polynomial system `F`. -/
@[expose] def IsLinearDesign {V : Type*} {p d : ℕ}
    (F : Set (MvPolynomial V (ZMod p)))
    (ω : PolyBoundedDeg V p d → ZMod p) : Prop :=
  (∃ L : PolyBoundedDeg V p d →ₗ[ZMod p] ZMod p,
    (∀ g, ω g = L g) ∧ L (PolyBoundedDeg.one V p d) = 1) ∧
  ∀ f ∈ F, ∀ g : PolyBoundedDeg V p d,
    ∀ hdeg : (f * g.1).totalDegree ≤ d,
      ω ⟨f * g.1, (MvPolynomial.mem_restrictTotalDegree V d (f * g.1)).mpr hdeg⟩ = 0

/-- A `(d, e, γ)`-pseudo-solution of a polynomial system `F` over `ZMod p`: a nonempty finite set
`Ω` of linear designs of `F` such that every `(d, e)`-tree fails to output a conflict pair on at
least a `γ`-fraction of `Ω`. -/
@[expose] noncomputable def IsPseudoSolution {V : Type*} {p : ℕ} [NeZero p]
    (F : Set (MvPolynomial V (ZMod p))) (d e : ℕ) (γ : ℚ)
    (Ω : Finset (PolyBoundedDeg V p d → ZMod p)) : Prop :=
  Ω.Nonempty ∧
  (∀ ω ∈ Ω, IsLinearDesign F ω) ∧
  ∀ T : PolyDecisionTree V p d (PolyBoundedDeg V p d × PolyBoundedDeg V p d),
    T.height ≤ e →
      let _ : DecidablePred fun ω => ¬ IsConflictPair ω (T.eval ω) := Classical.decPred _
      γ ≤ ((Ω.filter fun ω => ¬ IsConflictPair ω (T.eval ω)).card : ℚ) / (Ω.card : ℚ)

end PseudoSolution

end CslibFrontier.Logic.PL.ENS
