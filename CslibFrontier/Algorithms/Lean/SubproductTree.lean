/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Log

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Subproduct Trees and Fast Multipoint Evaluation over Commutative Rings

Balanced subproduct trees, top-down monic remainder tree traversal, fast multipoint polynomial
evaluation, and fast bivariate difference products over an arbitrary commutative ring `R`,
following Moenck and Borodin and von zur Gathen and Gerhard, *Modern Computer Algebra*
.

Because every internal polynomial stored in a multiplicative subproduct tree is monic, Euclidean
division with remainder by monic polynomials (`Polynomial.modByMonic`, written `%ₘ`) is exact over
any commutative ring `R` without requiring `R` to be a field, an integral domain, or even
nontrivial. In particular, all algebraic identities apply directly to composite residue rings
`ZMod d` and quotient algebras `AdjoinRoot h` for reducible monic polynomials `h`.

## Main definitions

* `CslibFrontier.Algorithms.Lean.SubproductTree`: binary tree storing monic subproduct polynomials
  over a commutative ring `R`, with projections `rootPoly`, `points`, `depth`, functorial
  pushforward `map`, and multiplicative consistency invariant `IsMultiplicative`.
* `CslibFrontier.Algorithms.Lean.buildSubproductTree`: balanced divide-and-conquer subproduct tree
  construction over `pts : List R`.
* `CslibFrontier.Algorithms.Lean.remainderTreeEval`,
  `CslibFrontier.Algorithms.Lean.fastMultipointEval`: top-down monic remainder tree traversal and
  fast multipoint evaluation `[p.eval a | a ← pts]`.
* `CslibFrontier.Algorithms.Lean.fastBivariateDiffProd`: fast bivariate pairwise difference product
  `∏_{s ∈ sPts} ∏_{t ∈ tPts} (s - t)` via `buildSubproductTree` and `fastMultipointEval`.
* `CslibFrontier.Algorithms.Lean.buildSubproductTreeDegSum`,
  `CslibFrontier.Algorithms.Lean.remainderTreeDegSum`: total degree weights of internal
  multiplications and monic divisions across the tree.

## Main results

* `CslibFrontier.Algorithms.Lean.monic_rootPoly_buildSubproductTree`,
  `CslibFrontier.Algorithms.Lean.rootPoly_buildSubproductTree_eq_prod`,
  `CslibFrontier.Algorithms.Lean.natDegree_rootPoly_buildSubproductTree`: monicity, product
  factorization, and exact degree of `(buildSubproductTree pts).rootPoly`.
* `CslibFrontier.Algorithms.Lean.fastMultipointEval_eq_map_eval`,
  `CslibFrontier.Algorithms.Lean.map_fastMultipointEval`: exact agreement of
  `fastMultipointEval pts p` with `pts.map p.eval` over every commutative ring `R` and naturality
  under ring homomorphisms.
* `CslibFrontier.Algorithms.Lean.fastBivariateDiffProd_eq_prod`,
  `CslibFrontier.Algorithms.Lean.fastBivariateDiffProd_eq_zero_of_mem`,
  `CslibFrontier.Algorithms.Lean.fastBivariateDiffProd_eq_zero_iff`: algebraic product identity and
  vanishing characterization for `fastBivariateDiffProd`.
* `CslibFrontier.Algorithms.Lean.depth_buildSubproductTree_le`,
  `CslibFrontier.Algorithms.Lean.buildSubproductTreeDegSum_le_mul_clog`,
  `CslibFrontier.Algorithms.Lean.remainderTreeDegSum_buildSubproductTree_le_mul_clog`,
  `CslibFrontier.Algorithms.Lean.buildSubproductTreeDegSum_eq_of_length_eq_pow`: logarithmic tree
  depth and sharp `|pts| * ⌈log₂ (max |pts| 1)⌉` degree-weight bounds.
-/

public section

namespace CslibFrontier.Algorithms.Lean

open _root_.Polynomial

/-- Binary tree storing monic subproduct polynomials over a commutative ring `R`: `empty`
represents the empty point list with polynomial `1`, `leaf a` represents a singleton point `[a]`
with linear polynomial `X - C a`, and `node poly left right` caches the product polynomial `poly`
above two subtrees `left` and `right`. -/
inductive SubproductTree (R : Type*) [CommRing R] where
  /-- Empty subproduct tree associated with `[]` and root polynomial `1`. -/
  | empty : SubproductTree R
  /-- Singleton leaf associated with `[a]` and root polynomial `X - C a`. -/
  | leaf (a : R) : SubproductTree R
  /-- Internal binary node storing a cached polynomial `poly` over `left` and `right`. -/
  | node (poly : R[X]) (left right : SubproductTree R) : SubproductTree R

/-- Canonical inhabited instance for `SubproductTree R` given by `SubproductTree.empty`. -/
instance instInhabitedSubproductTree {R : Type*} [CommRing R] : Inhabited (SubproductTree R) :=
  ⟨.empty⟩

/-- Root polynomial associated with a `SubproductTree R`: `1` on `empty`, `X - C a` on `leaf a`,
and the stored polynomial `p` on `node p l r`. -/
noncomputable def SubproductTree.rootPoly {R : Type*} [CommRing R] : SubproductTree R → R[X]
  | .empty => 1
  | .leaf a => X - C a
  | .node p _ _ => p

@[simp, grind =]
theorem SubproductTree.rootPoly_empty {R : Type*} [CommRing R] :
    (SubproductTree.empty : SubproductTree R).rootPoly = 1 := by rfl

@[simp, grind =]
theorem SubproductTree.rootPoly_leaf {R : Type*} [CommRing R] (a : R) :
    (SubproductTree.leaf a).rootPoly = X - C a := by rfl

@[simp, grind =]
theorem SubproductTree.rootPoly_node {R : Type*} [CommRing R] (p : R[X])
    (l r : SubproductTree R) : (SubproductTree.node p l r).rootPoly = p := by rfl

/-- Ordered list of evaluation points stored at the leaves of a `SubproductTree R`. -/
def SubproductTree.points {R : Type*} [CommRing R] : SubproductTree R → List R
  | .empty => []
  | .leaf a => [a]
  | .node _ l r => l.points ++ r.points

@[simp, grind =]
theorem SubproductTree.points_empty {R : Type*} [CommRing R] :
    (SubproductTree.empty : SubproductTree R).points = [] := by rfl

@[simp, grind =]
theorem SubproductTree.points_leaf {R : Type*} [CommRing R] (a : R) :
    (SubproductTree.leaf a).points = [a] := by rfl

@[simp, grind =]
theorem SubproductTree.points_node {R : Type*} [CommRing R] (p : R[X])
    (l r : SubproductTree R) : (SubproductTree.node p l r).points = l.points ++ r.points := by rfl

/-- Node height of a `SubproductTree R`: `0` on `empty`, `1` on `leaf a`, and
`max l.depth r.depth + 1` on `node p l r`. -/
def SubproductTree.depth {R : Type*} [CommRing R] : SubproductTree R → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .node _ l r => max l.depth r.depth + 1

@[simp, grind =]
theorem SubproductTree.depth_empty {R : Type*} [CommRing R] :
    (SubproductTree.empty : SubproductTree R).depth = 0 := by rfl

@[simp, grind =]
theorem SubproductTree.depth_leaf {R : Type*} [CommRing R] (a : R) :
    (SubproductTree.leaf a).depth = 1 := by rfl

@[simp, grind =]
theorem SubproductTree.depth_node {R : Type*} [CommRing R] (p : R[X])
    (l r : SubproductTree R) :
    (SubproductTree.node p l r).depth = max l.depth r.depth + 1 := by rfl

/-- Multiplicative consistency predicate on `SubproductTree R`: every internal node stores the
exact product `l.rootPoly * r.rootPoly` of its left and right subtree root polynomials. -/
def SubproductTree.IsMultiplicative {R : Type*} [CommRing R] : SubproductTree R → Prop
  | .empty => True
  | .leaf _ => True
  | .node p l r => p = l.rootPoly * r.rootPoly ∧ l.IsMultiplicative ∧ r.IsMultiplicative

@[simp]
theorem SubproductTree.isMultiplicative_empty {R : Type*} [CommRing R] :
    (SubproductTree.empty : SubproductTree R).IsMultiplicative := by trivial

@[simp]
theorem SubproductTree.isMultiplicative_leaf {R : Type*} [CommRing R] (a : R) :
    (SubproductTree.leaf a).IsMultiplicative := by trivial

/-- Recursive characterization of `SubproductTree.IsMultiplicative` on an internal node. -/
theorem SubproductTree.isMultiplicative_node {R : Type*} [CommRing R] (p : R[X])
    (l r : SubproductTree R) :
    (SubproductTree.node p l r).IsMultiplicative ↔
      p = l.rootPoly * r.rootPoly ∧ l.IsMultiplicative ∧ r.IsMultiplicative := by rfl

/-- Pushforward of a `SubproductTree R` along a ring homomorphism `f : R →+* S`. -/
noncomputable def SubproductTree.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    SubproductTree R → SubproductTree S
  | .empty => .empty
  | .leaf a => .leaf (f a)
  | .node p l r => .node (p.map f) (l.map f) (r.map f)

@[simp, grind =]
theorem SubproductTree.map_empty {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (SubproductTree.empty : SubproductTree R).map f = .empty := by rfl

@[simp, grind =]
theorem SubproductTree.map_leaf {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    (SubproductTree.leaf a).map f = .leaf (f a) := by rfl

@[simp, grind =]
theorem SubproductTree.map_node {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X])
    (l r : SubproductTree R) :
    (SubproductTree.node p l r).map f = .node (p.map f) (l.map f) (r.map f) := by rfl

@[simp, grind =]
theorem SubproductTree.points_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : SubproductTree R) : (t.map f).points = t.points.map f := by
  induction t with
  | empty => rfl
  | leaf a => rfl
  | node p l r ihl ihr => simp [ihl, ihr]

@[simp, grind =]
theorem SubproductTree.rootPoly_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : SubproductTree R) : (t.map f).rootPoly = t.rootPoly.map f := by
  cases t <;> simp

@[simp, grind =]
theorem SubproductTree.depth_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : SubproductTree R) : (t.map f).depth = t.depth := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ _ ihl ihr => simp [ihl, ihr]

/-- Every multiplicative subproduct tree over a commutative ring has a monic root polynomial. -/
theorem SubproductTree.IsMultiplicative.monic_rootPoly {R : Type*} [CommRing R]
    {t : SubproductTree R} (ht : t.IsMultiplicative) : t.rootPoly.Monic := by
  induction t with
  | empty => exact monic_one
  | leaf a => exact monic_X_sub_C a
  | node p l r ihl ihr =>
    rcases ht with ⟨rfl, hl, hr⟩
    exact (ihl hl).mul (ihr hr)

/-- The root polynomial of any multiplicative subproduct tree equals the ordered product
`∏_{a ∈ t.points} (X - C a)`. -/
theorem SubproductTree.IsMultiplicative.rootPoly_eq_prod {R : Type*} [CommRing R]
    {t : SubproductTree R} (ht : t.IsMultiplicative) :
    t.rootPoly = (t.points.map fun a ↦ X - C a).prod := by
  induction t with
  | empty => simp
  | leaf a => simp
  | node p l r ihl ihr =>
    rcases ht with ⟨rfl, hl, hr⟩
    simp [ihl hl, ihr hr, List.prod_append]

private lemma monic_prod_map_X_sub_C {R : Type*} [CommRing R] (pts : List R) :
    (pts.map fun a ↦ X - C a).prod.Monic := by
  induction pts with
  | nil => exact monic_one
  | cons a rest ih =>
    simpa only [List.map_cons, List.prod_cons] using (monic_X_sub_C a).mul ih

private lemma natDegree_prod_map_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (pts : List R) :
    (pts.map fun a ↦ X - C a).prod.natDegree = pts.length := by
  induction pts with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.prod_cons,
      (monic_X_sub_C a).natDegree_mul (monic_prod_map_X_sub_C rest),
      natDegree_X_sub_C, ih, List.length_cons, add_comm]

/-- Over a nontrivial commutative ring, the root polynomial of any multiplicative subproduct tree
has `natDegree` equal to `t.points.length`. -/
theorem SubproductTree.IsMultiplicative.natDegree_rootPoly {R : Type*} [CommRing R] [Nontrivial R]
    {t : SubproductTree R} (ht : t.IsMultiplicative) :
    t.rootPoly.natDegree = t.points.length := by
  rw [ht.rootPoly_eq_prod, natDegree_prod_map_X_sub_C]

/-- Pushing a multiplicative subproduct tree forward along a ring homomorphism preserves
multiplicativity. -/
theorem SubproductTree.IsMultiplicative.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {t : SubproductTree R} (ht : t.IsMultiplicative) : (t.map f).IsMultiplicative := by
  induction t with
  | empty => trivial
  | leaf _ => trivial
  | node p l r ihl ihr =>
    rcases ht with ⟨rfl, hl, hr⟩
    exact ⟨by simp [_root_.Polynomial.map_mul], ihl hl, ihr hr⟩

/-- Balanced binary divide-and-conquer construction of the subproduct tree over a point list
`pts : List R`, splitting lists of length at least `2` at `pts.length / 2`. -/
noncomputable def buildSubproductTree {R : Type*} [CommRing R] : List R → SubproductTree R
  | [] => .empty
  | [a] => .leaf a
  | a :: b :: rest =>
    let pts := a :: b :: rest
    let m := pts.length / 2
    let tl := buildSubproductTree (pts.take m)
    let tr := buildSubproductTree (pts.drop m)
    .node (tl.rootPoly * tr.rootPoly) tl tr
termination_by pts => pts.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_take, List.length_drop]
    omega

@[simp, grind =]
theorem buildSubproductTree_nil {R : Type*} [CommRing R] :
    buildSubproductTree ([] : List R) = .empty := by
  rw [buildSubproductTree]

@[simp, grind =]
theorem buildSubproductTree_singleton {R : Type*} [CommRing R] (a : R) :
    buildSubproductTree [a] = .leaf a := by
  rw [buildSubproductTree]

/-- Recursive split equation for `buildSubproductTree` on any list of length at least `2`. -/
theorem buildSubproductTree_of_two_le_length {R : Type*} [CommRing R] (pts : List R)
    (h : 2 ≤ pts.length) :
    buildSubproductTree pts =
      let m := pts.length / 2
      let tl := buildSubproductTree (pts.take m)
      let tr := buildSubproductTree (pts.drop m)
      .node (tl.rootPoly * tr.rootPoly) tl tr := by
  match pts, h with
  | a :: b :: rest, _ =>
    rw [buildSubproductTree]

/-- `buildSubproductTree pts` recovers the exact input point list `pts` in order. -/
@[simp, grind =]
theorem points_buildSubproductTree {R : Type*} [CommRing R] (pts : List R) :
    (buildSubproductTree pts).points = pts := by
  induction pts using buildSubproductTree.induct with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest all m ihl ihr =>
    rw [buildSubproductTree]
    change (buildSubproductTree (all.take m)).points ++
        (buildSubproductTree (all.drop m)).points = all
    rw [ihl, ihr, List.take_append_drop]

/-- Every tree built by `buildSubproductTree` satisfies `SubproductTree.IsMultiplicative`. -/
theorem isMultiplicative_buildSubproductTree {R : Type*} [CommRing R] (pts : List R) :
    (buildSubproductTree pts).IsMultiplicative := by
  induction pts using buildSubproductTree.induct with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest all m ihl ihr =>
    rw [buildSubproductTree]
    exact ⟨rfl, ihl, ihr⟩

/-- The root polynomial of `buildSubproductTree pts` is monic over any commutative ring `R`. -/
theorem monic_rootPoly_buildSubproductTree {R : Type*} [CommRing R] (pts : List R) :
    (buildSubproductTree pts).rootPoly.Monic :=
  (isMultiplicative_buildSubproductTree pts).monic_rootPoly

/-- The root polynomial of `buildSubproductTree pts` equals `∏_{a ∈ pts} (X - C a)`. -/
theorem rootPoly_buildSubproductTree_eq_prod {R : Type*} [CommRing R] (pts : List R) :
    (buildSubproductTree pts).rootPoly = (pts.map fun a ↦ X - C a).prod := by
  rw [(isMultiplicative_buildSubproductTree pts).rootPoly_eq_prod, points_buildSubproductTree]

/-- Over any nontrivial commutative ring `R`, `(buildSubproductTree pts).rootPoly` has degree
`pts.length`. -/
theorem natDegree_rootPoly_buildSubproductTree {R : Type*} [CommRing R] [Nontrivial R]
    (pts : List R) : (buildSubproductTree pts).rootPoly.natDegree = pts.length := by
  rw [rootPoly_buildSubproductTree_eq_prod, natDegree_prod_map_X_sub_C]

/-- `buildSubproductTree` commutes with every ring homomorphism `f : R →+* S`. -/
theorem map_buildSubproductTree {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (pts : List R) :
    (buildSubproductTree pts).map f = buildSubproductTree (pts.map f) := by
  induction pts using buildSubproductTree.induct with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest all m ihl ihr =>
    have hlen : 2 ≤ (all.map f).length := by simp [all]
    rw [show a :: b :: rest = all from rfl,
      buildSubproductTree_of_two_le_length all (by simp [all]),
      buildSubproductTree_of_two_le_length (all.map f) hlen]
    have hm : (all.map f).length / 2 = m := by simp [m]
    simp only [SubproductTree.map_node, _root_.Polynomial.map_mul, hm,
      ← List.map_take, ← List.map_drop, ← ihl, ← ihr, SubproductTree.rootPoly_map]
    rfl

/-- Reducing `p` modulo an arbitrary polynomial `q` and then modulo a monic divisor `q₁ ∣ q`
equals reducing `p` directly modulo `q₁`. -/
theorem modByMonic_of_dvd {R : Type*} [CommRing R] (p : R[X]) {q₁ q : R[X]}
    (hq₁ : q₁.Monic) (hdvd : q₁ ∣ q) : (p %ₘ q) %ₘ q₁ = p %ₘ q₁ := by
  apply _root_.Polynomial.modByMonic_eq_of_dvd_sub hq₁
  rcases hdvd with ⟨r, rfl⟩
  refine ⟨-(r * (p /ₘ (q₁ * r))), ?_⟩
  rw [_root_.Polynomial.modByMonic_eq_sub_mul_div]
  ring

/-- Monic remainder reduction is idempotent over any commutative ring. -/
theorem modByMonic_idem {R : Type*} [CommRing R] (p : R[X]) {q : R[X]} (hq : q.Monic) :
    (p %ₘ q) %ₘ q = p %ₘ q :=
  modByMonic_of_dvd p hq dvd_rfl

/-- Iterated remainder modulo `q₁ * q₂` followed by a monic left factor `q₁` collapses to `p %ₘ q₁`
over any commutative ring `R`. -/
theorem modByMonic_mul_modByMonic_left {R : Type*} [CommRing R] (p : R[X]) {q₁ : R[X]}
    (hq₁ : q₁.Monic) (q₂ : R[X]) : (p %ₘ (q₁ * q₂)) %ₘ q₁ = p %ₘ q₁ :=
  modByMonic_of_dvd p hq₁ (dvd_mul_right q₁ q₂)

/-- Iterated remainder modulo `q₁ * q₂` followed by a monic right factor `q₂` collapses to `p %ₘ q₂`
over any commutative ring `R`. -/
theorem modByMonic_mul_modByMonic_right {R : Type*} [CommRing R] (p q₁ : R[X]) {q₂ : R[X]}
    (hq₂ : q₂.Monic) : (p %ₘ (q₁ * q₂)) %ₘ q₂ = p %ₘ q₂ :=
  modByMonic_of_dvd p hq₂ (dvd_mul_left q₂ q₁)

private lemma coeff_zero_modByMonic_X_sub_C {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (p %ₘ (X - C a)).coeff 0 = p.eval a := by
  rw [_root_.Polynomial.modByMonic_X_sub_C_eq_C_eval, coeff_C_zero]

/-- Top-down monic remainder tree evaluation of `p : R[X]` across a `SubproductTree R`. -/
noncomputable def remainderTreeEval {R : Type*} [CommRing R] :
    SubproductTree R → R[X] → List R
  | .empty, _ => []
  | .leaf a, p => [(p %ₘ (X - C a)).coeff 0]
  | .node q l r, p =>
    let rem := p %ₘ q
    remainderTreeEval l rem ++ remainderTreeEval r rem

@[simp, grind =]
theorem remainderTreeEval_empty {R : Type*} [CommRing R] (p : R[X]) :
    remainderTreeEval (.empty : SubproductTree R) p = [] := by rfl

/-- Equation for `remainderTreeEval` on a singleton leaf. -/
theorem remainderTreeEval_leaf {R : Type*} [CommRing R] (a : R) (p : R[X]) :
    remainderTreeEval (.leaf a) p = [(p %ₘ (X - C a)).coeff 0] := by rfl

@[simp, grind =]
theorem remainderTreeEval_leaf_eq_eval {R : Type*} [CommRing R] (a : R) (p : R[X]) :
    remainderTreeEval (.leaf a) p = [p.eval a] := by
  rw [remainderTreeEval_leaf, coeff_zero_modByMonic_X_sub_C]

@[simp, grind =]
theorem remainderTreeEval_node {R : Type*} [CommRing R] (q : R[X]) (l r : SubproductTree R)
    (p : R[X]) :
    remainderTreeEval (.node q l r) p =
      remainderTreeEval l (p %ₘ q) ++ remainderTreeEval r (p %ₘ q) := by rfl

@[simp, grind =]
theorem length_remainderTreeEval {R : Type*} [CommRing R] (t : SubproductTree R) (p : R[X]) :
    (remainderTreeEval t p).length = t.points.length := by
  induction t generalizing p with
  | empty => rfl
  | leaf _ => rfl
  | node q l r ihl ihr => simp [ihl, ihr]

/-- Pre-reducing `p` modulo `t.rootPoly` leaves `remainderTreeEval t` unchanged on any
multiplicative subproduct tree. -/
theorem SubproductTree.IsMultiplicative.remainderTreeEval_modByMonic_rootPoly
    {R : Type*} [CommRing R] {t : SubproductTree R} (ht : t.IsMultiplicative) (p : R[X]) :
    remainderTreeEval t (p %ₘ t.rootPoly) = remainderTreeEval t p := by
  cases t with
  | empty => rfl
  | leaf a => simp
  | node q l r =>
    have hq : q.Monic := ht.monic_rootPoly
    simp [modByMonic_idem p hq]

/-- On any multiplicative subproduct tree `t`, top-down remainder tree traversal computes the exact
list of polynomial evaluations `t.points.map p.eval` over any commutative ring `R`. -/
theorem SubproductTree.IsMultiplicative.remainderTreeEval_eq_map_eval
    {R : Type*} [CommRing R] {t : SubproductTree R} (ht : t.IsMultiplicative) (p : R[X]) :
    remainderTreeEval t p = t.points.map p.eval := by
  induction t generalizing p with
  | empty => rfl
  | leaf a => simp
  | node q l r ihl ihr =>
    rcases ht with ⟨rfl, hl, hr⟩
    have hleft : remainderTreeEval l (p %ₘ (l.rootPoly * r.rootPoly)) = l.points.map p.eval := by
      rw [← hl.remainderTreeEval_modByMonic_rootPoly,
        modByMonic_mul_modByMonic_left p hl.monic_rootPoly r.rootPoly,
        hl.remainderTreeEval_modByMonic_rootPoly, ihl hl]
    have hright : remainderTreeEval r (p %ₘ (l.rootPoly * r.rootPoly)) = r.points.map p.eval := by
      rw [← hr.remainderTreeEval_modByMonic_rootPoly,
        modByMonic_mul_modByMonic_right p l.rootPoly hr.monic_rootPoly,
        hr.remainderTreeEval_modByMonic_rootPoly, ihr hr]
    simp [hleft, hright]

/-- Fast multipoint evaluation of `p : R[X]` at `pts : List R` via balanced subproduct tree
construction followed by top-down monic remainder traversal. -/
noncomputable def fastMultipointEval {R : Type*} [CommRing R]
    (pts : List R) (p : R[X]) : List R :=
  remainderTreeEval (buildSubproductTree pts) p

/-- Fast multipoint evaluation agrees identically with `[p.eval a | a ← pts]` over every
commutative ring `R`. -/
@[simp, grind =]
theorem fastMultipointEval_eq_map_eval {R : Type*} [CommRing R] (pts : List R) (p : R[X]) :
    fastMultipointEval pts p = pts.map p.eval := by
  rw [fastMultipointEval,
    (isMultiplicative_buildSubproductTree pts).remainderTreeEval_eq_map_eval,
    points_buildSubproductTree]

/-- Output length of `fastMultipointEval pts p` equals `pts.length`. -/
theorem length_fastMultipointEval {R : Type*} [CommRing R] (pts : List R) (p : R[X]) :
    (fastMultipointEval pts p).length = pts.length := by
  simp

/-- Pointwise indexing into `fastMultipointEval pts p` recovers `p.eval pts[i]`. -/
theorem getElem_fastMultipointEval {R : Type*} [CommRing R] (pts : List R) (p : R[X]) (i : ℕ)
    (hi : i < (fastMultipointEval pts p).length) :
    (fastMultipointEval pts p)[i] =
      p.eval (pts[i]'(by simpa [length_fastMultipointEval] using hi)) := by
  simp

/-- Fast multipoint evaluation commutes with every ring homomorphism `f : R →+* S`. -/
theorem map_fastMultipointEval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (pts : List R) (p : R[X]) :
    (fastMultipointEval pts p).map f = fastMultipointEval (pts.map f) (p.map f) := by
  simp [List.map_map, Function.comp_def, _root_.Polynomial.eval_map_apply]

/-- Fast evaluation of the bivariate pairwise difference product
`∏_{s ∈ sPts} ∏_{t ∈ tPts} (s - t)` over a commutative ring `R`, computed by evaluating the root
polynomial of `buildSubproductTree tPts` at `sPts` via `fastMultipointEval` and multiplying the
resulting values. -/
noncomputable def fastBivariateDiffProd {R : Type*} [CommRing R] (sPts tPts : List R) : R :=
  let p := (buildSubproductTree tPts).rootPoly
  (fastMultipointEval sPts p).prod

/-- Evaluating `(buildSubproductTree tPts).rootPoly` at `s : R` yields `∏_{t ∈ tPts} (s - t)`. -/
@[simp, grind =]
theorem eval_rootPoly_buildSubproductTree {R : Type*} [CommRing R] (tPts : List R) (s : R) :
    (buildSubproductTree tPts).rootPoly.eval s = (tPts.map fun t ↦ s - t).prod := by
  rw [rootPoly_buildSubproductTree_eq_prod, _root_.Polynomial.eval_list_prod, List.map_map]
  congr 1
  ext t
  simp

/-- `fastBivariateDiffProd sPts tPts` equals the exact iterated product
`∏_{s ∈ sPts} ∏_{t ∈ tPts} (s - t)` over every commutative ring `R`. -/
theorem fastBivariateDiffProd_eq_prod {R : Type*} [CommRing R] (sPts tPts : List R) :
    fastBivariateDiffProd sPts tPts =
      (sPts.map fun s ↦ (tPts.map fun t ↦ s - t).prod).prod := by
  simp [fastBivariateDiffProd]

@[simp, grind =]
theorem fastBivariateDiffProd_nil_left {R : Type*} [CommRing R] (tPts : List R) :
    fastBivariateDiffProd ([] : List R) tPts = 1 := by
  simp [fastBivariateDiffProd_eq_prod]

@[simp, grind =]
theorem fastBivariateDiffProd_nil_right {R : Type*} [CommRing R] (sPts : List R) :
    fastBivariateDiffProd sPts ([] : List R) = 1 := by
  simp [fastBivariateDiffProd_eq_prod]

/-- Multiplicativity of `fastBivariateDiffProd` in its left point list. -/
theorem fastBivariateDiffProd_append_left {R : Type*} [CommRing R] (s₁ s₂ tPts : List R) :
    fastBivariateDiffProd (s₁ ++ s₂) tPts =
      fastBivariateDiffProd s₁ tPts * fastBivariateDiffProd s₂ tPts := by
  simp [fastBivariateDiffProd_eq_prod, List.prod_append]

/-- Multiplicativity of `fastBivariateDiffProd` in its right point list. -/
theorem fastBivariateDiffProd_append_right {R : Type*} [CommRing R] (sPts t₁ t₂ : List R) :
    fastBivariateDiffProd sPts (t₁ ++ t₂) =
      fastBivariateDiffProd sPts t₁ * fastBivariateDiffProd sPts t₂ := by
  simp only [fastBivariateDiffProd_eq_prod, List.map_append, List.prod_append]
  induction sPts with
  | nil => simp
  | cons s rest ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    ring

/-- Over any commutative ring `R`, a shared element `x ∈ sPts` and `x ∈ tPts` forces
`fastBivariateDiffProd sPts tPts = 0`. -/
theorem fastBivariateDiffProd_eq_zero_of_mem {R : Type*} [CommRing R] {sPts tPts : List R} {x : R}
    (hs : x ∈ sPts) (ht : x ∈ tPts) : fastBivariateDiffProd sPts tPts = 0 := by
  rw [fastBivariateDiffProd_eq_prod]
  apply List.prod_eq_zero
  rw [List.mem_map]
  refine ⟨x, hs, List.prod_eq_zero ?_⟩
  rw [List.mem_map]
  exact ⟨x, ht, sub_self x⟩

/-- Over an integral domain `R`, `fastBivariateDiffProd sPts tPts = 0` if and only if `sPts` and
`tPts` share a common element. -/
theorem fastBivariateDiffProd_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (sPts tPts : List R) :
    fastBivariateDiffProd sPts tPts = 0 ↔ ∃ x ∈ sPts, x ∈ tPts := by
  constructor
  · intro h
    rw [fastBivariateDiffProd_eq_prod, List.prod_eq_zero_iff, List.mem_map] at h
    rcases h with ⟨s, hs, hprod⟩
    rw [List.prod_eq_zero_iff, List.mem_map] at hprod
    rcases hprod with ⟨t, ht, hsub⟩
    exact ⟨s, hs, by simpa [sub_eq_zero.mp hsub] using ht⟩
  · rintro ⟨x, hs, ht⟩
    exact fastBivariateDiffProd_eq_zero_of_mem hs ht

private lemma clog_two_max_one (n : ℕ) : Nat.clog 2 (max n 1) = Nat.clog 2 n := by
  rcases le_or_gt n 1 with hn | hn
  · have hmax : max n 1 = 1 := by omega
    rw [hmax, Nat.clog_one_right, Nat.clog_of_right_le_one hn]
  · have hmax : max n 1 = n := by omega
    rw [hmax]

private lemma clog_two_half_lt {n : ℕ} (hn : 2 ≤ n) :
    Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n ∧ Nat.clog 2 (n - n / 2) + 1 ≤ Nat.clog 2 n := by
  have hrec : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    simpa using Nat.clog_of_two_le (b := 2) (by decide) hn
  rw [hrec]
  exact ⟨Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1,
    Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1⟩

/-- The depth of `buildSubproductTree pts` is at most `⌈log₂ (max |pts| 1)⌉ + 1`. -/
theorem depth_buildSubproductTree_le {R : Type*} [CommRing R] (pts : List R) :
    (buildSubproductTree pts).depth ≤ Nat.clog 2 (max pts.length 1) + 1 := by
  rw [clog_two_max_one]
  induction pts using buildSubproductTree.induct with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest all m ihl ihr =>
    have hn : 2 ≤ all.length := by simp [all]
    have ⟨hleft, hright⟩ := clog_two_half_lt hn
    rw [show a :: b :: rest = all from rfl, buildSubproductTree_of_two_le_length all hn]
    simp only [SubproductTree.depth_node]
    have htl : (buildSubproductTree (all.take m)).depth ≤ Nat.clog 2 all.length := by
      have hlen : (all.take m).length = all.length / 2 := by simp [all, m]; omega
      exact (ihl.trans (by rw [hlen])).trans hleft
    have htr : (buildSubproductTree (all.drop m)).depth ≤ Nat.clog 2 all.length := by
      have hlen : (all.drop m).length = all.length - all.length / 2 := by simp [all, m]
      exact (ihr.trans (by rw [hlen])).trans hright
    exact Nat.add_le_add_right (max_le htl htr) 1

/-- When `pts.length = 2 ^ k`, `buildSubproductTree pts` has exact depth `k + 1`, demonstrating
sharpness of the `+ 1` term in `depth_buildSubproductTree_le`. -/
theorem depth_buildSubproductTree_eq_of_length_eq_pow {R : Type*} [CommRing R] :
    ∀ {k : ℕ} {pts : List R}, pts.length = 2 ^ k → (buildSubproductTree pts).depth = k + 1
  | 0, pts, h => by
    rcases List.length_eq_one_iff.mp (by simpa using h) with ⟨a, rfl⟩
    simp
  | k + 1, pts, h => by
    have h2 : 2 ≤ pts.length := by
      rw [h, pow_succ]
      have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      omega
    have htake : (pts.take (pts.length / 2)).length = 2 ^ k := by
      rw [List.length_take, h, pow_succ]
      omega
    have hdrop : (pts.drop (pts.length / 2)).length = 2 ^ k := by
      rw [List.length_drop, h, pow_succ]
      omega
    rw [buildSubproductTree_of_two_le_length pts h2]
    simp [depth_buildSubproductTree_eq_of_length_eq_pow htake,
      depth_buildSubproductTree_eq_of_length_eq_pow hdrop]

/-- Total degree weight of internal polynomial multiplications across `buildSubproductTree pts`,
summing `tl.points.length + tr.points.length` over all internal `.node`s. -/
noncomputable def buildSubproductTreeDegSum {R : Type*} [CommRing R] : List R → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    let pts := a :: b :: rest
    let m := pts.length / 2
    let tl := buildSubproductTree (pts.take m)
    let tr := buildSubproductTree (pts.drop m)
    tl.points.length + tr.points.length +
      buildSubproductTreeDegSum (pts.take m) + buildSubproductTreeDegSum (pts.drop m)
termination_by pts => pts.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_take, List.length_drop]
    omega

@[simp, grind =]
theorem buildSubproductTreeDegSum_nil {R : Type*} [CommRing R] :
    buildSubproductTreeDegSum ([] : List R) = 0 := by
  rw [buildSubproductTreeDegSum]

@[simp, grind =]
theorem buildSubproductTreeDegSum_singleton {R : Type*} [CommRing R] (a : R) :
    buildSubproductTreeDegSum [a] = 0 := by
  rw [buildSubproductTreeDegSum]

private theorem buildSubproductTreeDegSum_of_two_le_length {R : Type*} [CommRing R] (pts : List R)
    (h : 2 ≤ pts.length) :
    buildSubproductTreeDegSum pts =
      let m := pts.length / 2
      (buildSubproductTree (pts.take m)).points.length +
        (buildSubproductTree (pts.drop m)).points.length +
        buildSubproductTreeDegSum (pts.take m) +
        buildSubproductTreeDegSum (pts.drop m) := by
  match pts, h with
  | a :: b :: rest, _ => rw [buildSubproductTreeDegSum]

/-- Total degree weight of internal monic divisions across a `SubproductTree R`, summing
`l.points.length + r.points.length` over all internal `.node`s. -/
def remainderTreeDegSum {R : Type*} [CommRing R] : SubproductTree R → ℕ
  | .empty => 0
  | .leaf _ => 0
  | .node _ l r => l.points.length + r.points.length + remainderTreeDegSum l + remainderTreeDegSum r

@[simp, grind =]
theorem remainderTreeDegSum_empty {R : Type*} [CommRing R] :
    remainderTreeDegSum (.empty : SubproductTree R) = 0 := by rfl

@[simp, grind =]
theorem remainderTreeDegSum_leaf {R : Type*} [CommRing R] (a : R) :
    remainderTreeDegSum (.leaf a) = 0 := by rfl

@[simp, grind =]
theorem remainderTreeDegSum_node {R : Type*} [CommRing R] (p : R[X]) (l r : SubproductTree R) :
    remainderTreeDegSum (.node p l r) =
      l.points.length + r.points.length + remainderTreeDegSum l + remainderTreeDegSum r := by rfl

/-- The top-down remainder degree-weight sum on `buildSubproductTree pts` coincides identically
with the bottom-up multiplication degree-weight sum `buildSubproductTreeDegSum pts`. -/
@[simp, grind =]
theorem remainderTreeDegSum_buildSubproductTree {R : Type*} [CommRing R] (pts : List R) :
    remainderTreeDegSum (buildSubproductTree pts) = buildSubproductTreeDegSum pts := by
  induction pts using buildSubproductTree.induct with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest all m ihl ihr =>
    have hn : 2 ≤ all.length := by simp [all]
    rw [show a :: b :: rest = all from rfl,
      buildSubproductTree_of_two_le_length all hn,
      buildSubproductTreeDegSum_of_two_le_length all hn]
    dsimp only
    rw [remainderTreeDegSum_node, ihl, ihr]

/-- Sharp quasi-linear bound on the total degree weight of internal polynomial multiplications in
`buildSubproductTree pts`: at most `|pts| * ⌈log₂ (max |pts| 1)⌉`. -/
theorem buildSubproductTreeDegSum_le_mul_clog {R : Type*} [CommRing R] (pts : List R) :
    buildSubproductTreeDegSum pts ≤ pts.length * Nat.clog 2 (max pts.length 1) := by
  rw [clog_two_max_one]
  induction pts using buildSubproductTree.induct with
  | case1 => simp
  | case2 a => simp
  | case3 a b rest all m ihl ihr =>
    have hn : 2 ≤ all.length := by simp [all]
    have hrec : Nat.clog 2 all.length = Nat.clog 2 ((all.length + 1) / 2) + 1 := by
      simpa using Nat.clog_of_two_le (b := 2) (by decide) hn
    have htl_len : (all.take m).length = all.length / 2 := by
      simp [all, m]; omega
    have htr_len : (all.drop m).length = all.length - all.length / 2 := by
      simp [all, m]
    have hcl_l : Nat.clog 2 (all.length / 2) ≤ Nat.clog 2 ((all.length + 1) / 2) :=
      Nat.clog_mono_right 2 (by omega)
    have hcl_r : Nat.clog 2 (all.length - all.length / 2) ≤ Nat.clog 2 ((all.length + 1) / 2) :=
      Nat.clog_mono_right 2 (by omega)
    have hsum_len : all.length / 2 + (all.length - all.length / 2) = all.length := by omega
    rw [show a :: b :: rest = all from rfl, buildSubproductTreeDegSum_of_two_le_length all hn]
    dsimp only
    rw [points_buildSubproductTree, points_buildSubproductTree, htl_len, htr_len]
    have ihl' : buildSubproductTreeDegSum (all.take m) ≤
        (all.length / 2) * Nat.clog 2 ((all.length + 1) / 2) := by
      rw [htl_len] at ihl
      exact ihl.trans (Nat.mul_le_mul_left _ hcl_l)
    have ihr' : buildSubproductTreeDegSum (all.drop m) ≤
        (all.length - all.length / 2) * Nat.clog 2 ((all.length + 1) / 2) := by
      rw [htr_len] at ihr
      exact ihr.trans (Nat.mul_le_mul_left _ hcl_r)
    calc
      all.length / 2 + (all.length - all.length / 2) +
          buildSubproductTreeDegSum (all.take m) +
          buildSubproductTreeDegSum (all.drop m)
        ≤ all.length +
            ((all.length / 2) * Nat.clog 2 ((all.length + 1) / 2) +
              (all.length - all.length / 2) * Nat.clog 2 ((all.length + 1) / 2)) := by
          omega
      _ = all.length + all.length * Nat.clog 2 ((all.length + 1) / 2) := by
          rw [← Nat.add_mul, hsum_len]
      _ = all.length * (Nat.clog 2 ((all.length + 1) / 2) + 1) := by ring
      _ = all.length * Nat.clog 2 all.length := by rw [← hrec]

/-- Sharp quasi-linear bound on the total degree weight of internal monic divisions across
`buildSubproductTree pts`: at most `|pts| * ⌈log₂ (max |pts| 1)⌉`. -/
theorem remainderTreeDegSum_buildSubproductTree_le_mul_clog {R : Type*} [CommRing R]
    (pts : List R) :
    remainderTreeDegSum (buildSubproductTree pts) ≤
      pts.length * Nat.clog 2 (max pts.length 1) := by
  rw [remainderTreeDegSum_buildSubproductTree]
  exact buildSubproductTreeDegSum_le_mul_clog pts

/-- Total multiplication degree-weight bound across `buildSubproductTree pts` matching the tree
height factor `⌈log₂ (max |pts| 1)⌉ + 1`. -/
theorem buildSubproductTreeDegSum_le {R : Type*} [CommRing R] (pts : List R) :
    buildSubproductTreeDegSum pts ≤ pts.length * (Nat.clog 2 (max pts.length 1) + 1) :=
  (buildSubproductTreeDegSum_le_mul_clog pts).trans
    (Nat.mul_le_mul_left pts.length (Nat.le_succ _))

/-- Total remainder degree-weight bound across `buildSubproductTree pts` matching the tree height
factor `⌈log₂ (max |pts| 1)⌉ + 1`. -/
theorem remainderTreeDegSum_buildSubproductTree_le {R : Type*} [CommRing R] (pts : List R) :
    remainderTreeDegSum (buildSubproductTree pts) ≤
      pts.length * (Nat.clog 2 (max pts.length 1) + 1) := by
  rw [remainderTreeDegSum_buildSubproductTree]
  exact buildSubproductTreeDegSum_le pts

/-- When `pts.length = 2 ^ k`, the total degree weight of internal multiplications in
`buildSubproductTree pts` equals `k * 2 ^ k` identically, establishing tightness of
`buildSubproductTreeDegSum_le_mul_clog`. -/
theorem buildSubproductTreeDegSum_eq_of_length_eq_pow {R : Type*} [CommRing R] :
    ∀ {k : ℕ} {pts : List R}, pts.length = 2 ^ k → buildSubproductTreeDegSum pts = k * 2 ^ k
  | 0, pts, h => by
    rcases List.length_eq_one_iff.mp (by simpa using h) with ⟨a, rfl⟩
    simp
  | k + 1, pts, h => by
    have h2 : 2 ≤ pts.length := by
      rw [h, pow_succ]
      have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      omega
    have htake : (pts.take (pts.length / 2)).length = 2 ^ k := by
      rw [List.length_take, h, pow_succ]
      omega
    have hdrop : (pts.drop (pts.length / 2)).length = 2 ^ k := by
      rw [List.length_drop, h, pow_succ]
      omega
    rw [buildSubproductTreeDegSum_of_two_le_length pts h2]
    dsimp only
    rw [points_buildSubproductTree, points_buildSubproductTree, htake, hdrop,
      buildSubproductTreeDegSum_eq_of_length_eq_pow htake,
      buildSubproductTreeDegSum_eq_of_length_eq_pow hdrop, pow_succ]
    ring

private theorem not_isDomain_zmod_six : ¬ IsDomain (ZMod 6) := by
  intro hDom
  have hzero : ((2 : ZMod 6) * 3) = 0 := by decide
  rcases mul_eq_zero.mp hzero with h2 | h3
  · revert h2; decide
  · revert h3; decide

private theorem zmod_six_fastMultipointEval_example :
    fastMultipointEval ([0, 1, 2, 3] : List (ZMod 6))
      (X ^ 3 + C 2 * X ^ 2 + C 3 * X + C 1) = [1, 1, 5, 1] := by
  rw [fastMultipointEval_eq_map_eval]
  simp only [List.map_cons, List.map_nil, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  decide

private theorem zmod_six_fastBivariateDiffProd_nonzero :
    fastBivariateDiffProd ([0, 2, 4] : List (ZMod 6)) [1, 3, 5] = 3 := by
  rw [fastBivariateDiffProd_eq_prod]
  decide

private theorem zmod_six_fastBivariateDiffProd_zero_disjoint :
    List.Disjoint ([0, 1, 2] : List (ZMod 6)) [3, 4, 5] ∧
      fastBivariateDiffProd ([0, 1, 2] : List (ZMod 6)) [3, 4, 5] = 0 := by
  refine ⟨fun x hx₁ hx₂ ↦ ?_, ?_⟩
  · revert x hx₁ hx₂; decide
  · rw [fastBivariateDiffProd_eq_prod]
    decide

end CslibFrontier.Algorithms.Lean
