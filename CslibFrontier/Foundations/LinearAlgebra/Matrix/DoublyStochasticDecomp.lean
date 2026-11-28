module

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-!
# Irreducible Block Decomposition of Doubly Stochastic and Nonnegative Matrices

This module develops the block-diagonal decomposition of symmetric nonnegative matrices and the
block-related partition theory of rectangular nonnegative and doubly stochastic matrices over
finite index sets.

## Main definitions

* `CslibFrontier.Foundations.LinearAlgebra.Matrix.IsRectDoublyStochastic`: rectangular doubly
  stochastic real matrices.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.IsIrreducibleMatrix`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.inducedSetoid`: support-graph irreducibility and
  the component partition induced by a symmetric nonnegative matrix.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.IsGoodSymmMatrix`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.IsGoodMatrix`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.IsBlockPositiveMatrix`: matrices positive on
  every diagonal or matching block of their induced partitions.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.AreMatrixRelated`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.charVec`: partitions related by a nonnegative
  matrix and indicator vectors.

## Main results

* `CslibFrontier.Foundations.LinearAlgebra.Matrix.pow_apply_pos_of_isIrreducibleMatrix`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.isIrreducibleMatrix_pow`: strict positivity of
  high powers of irreducible nonnegative matrices with positive diagonal.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.symm_nonneg_block_diag_exists`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.symm_nonneg_block_diag_unique`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.symm_nonneg_perm_similarity`: existence and
  uniqueness of the irreducible block-diagonal decomposition of a symmetric matrix.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.inducedSetoid_pow_eq`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.pow_apply_pos_iff_inducedSetoid`: invariance of
  the induced partition under positive powers.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.rectDoublyStochastic_related_card_and_charVec`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.doublyStochastic_related_card_and_charVec`:
  block cardinality equality and indicator-vector preservation for doubly stochastic matrices.
* `CslibFrontier.Foundations.LinearAlgebra.Matrix.mul_transpose_related_partitions`,
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.mul_transpose_pow_mul_blockPositive`:
  canonical bijection between the partitions induced by `X * Xᵀ` and `Xᵀ * X`, and block-positivity
  of `(X * Xᵀ) ^ ℓ * X` for `ℓ ≥ |V| - 1`.
-/

public section

open scoped BigOperators
open Matrix Finset

namespace CslibFrontier.Foundations.LinearAlgebra.Matrix

/-! ### Nonnegative rectangular doubly stochastic matrices -/

/-- A rectangular real matrix `X : Matrix V W ℝ` is rectangular doubly stochastic if all entries
are nonnegative and every row sum and column sum equals `1`. -/
def IsRectDoublyStochastic {V W : Type*} [Fintype V] [Fintype W] (X : Matrix V W ℝ) : Prop :=
  (∀ a b, 0 ≤ X a b) ∧ (∀ a, ∑ b, X a b = 1) ∧ (∀ b, ∑ a, X a b = 1)

theorem IsRectDoublyStochastic.nonneg {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) (a : V) (b : W) : 0 ≤ X a b :=
  hX.1 a b

theorem IsRectDoublyStochastic.row_sum {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) (a : V) : ∑ b, X a b = 1 :=
  hX.2.1 a

theorem IsRectDoublyStochastic.col_sum {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) (b : W) : ∑ a, X a b = 1 :=
  hX.2.2 b

theorem IsRectDoublyStochastic.of_parts {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hnn : ∀ a b, 0 ≤ X a b)
    (hrow : ∀ a, ∑ b, X a b = 1) (hcol : ∀ b, ∑ a, X a b = 1) :
    IsRectDoublyStochastic X :=
  ⟨hnn, hrow, hcol⟩

theorem isRectDoublyStochastic_iff_mem_doublyStochastic {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} : IsRectDoublyStochastic X ↔ X ∈ doublyStochastic ℝ V := by
  rw [IsRectDoublyStochastic, mem_doublyStochastic_iff_sum]

theorem IsRectDoublyStochastic.transpose {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) : IsRectDoublyStochastic Xᵀ :=
  ⟨fun b a => hX.1 a b, fun b => hX.2.2 b, fun a => hX.2.1 a⟩

theorem IsRectDoublyStochastic.mul {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    {X : Matrix U V ℝ} {Y : Matrix V W ℝ}
    (hX : IsRectDoublyStochastic X) (hY : IsRectDoublyStochastic Y) :
    IsRectDoublyStochastic (X * Y) := by
  refine ⟨fun u w => Finset.sum_nonneg fun v _ => mul_nonneg (hX.1 u v) (hY.1 v w), ?_, ?_⟩
  · intro u
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hY.2.1, mul_one, hX.2.1]
  · intro w
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hX.2.2, one_mul, hY.2.2]

theorem IsRectDoublyStochastic.card_eq {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) : Fintype.card V = Fintype.card W := by
  have h1 : (Fintype.card V : ℝ) = ∑ a : V, ∑ b : W, X a b := by simp [hX.2.1]
  have h2 : (Fintype.card W : ℝ) = ∑ b : W, ∑ a : V, X a b := by simp [hX.2.2]
  rw [Finset.sum_comm] at h2
  exact Nat.cast_injective (h1.trans h2.symm)

theorem IsRectDoublyStochastic.no_null_rows {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) (a : V) : ∃ b, 0 < X a b := by
  by_contra h
  push Not at h
  have h0 : ∑ b : W, X a b = 0 :=
    Finset.sum_eq_zero fun b _ => le_antisymm (h b) (hX.1 a b)
  linarith [hX.2.1 a]

theorem IsRectDoublyStochastic.no_null_cols {V W : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X) (b : W) : ∃ a, 0 < X a b :=
  hX.transpose.no_null_rows b

/-! ### Exact-length walks in finite directed graphs -/

/-- Existence of a directed walk of exact length `ℓ` from `u` to `v` in a relation `R`. -/
inductive ExactWalk {V : Type*} (R : V → V → Prop) : ℕ → V → V → Prop
  /-- The zero-length walk from a vertex to itself. -/
  | zero (v : V) : ExactWalk R 0 v v
  /-- Appending one `R`-step to an `n`-step walk. -/
  | step {n : ℕ} {u v w : V} : ExactWalk R n u v → R v w → ExactWalk R (n + 1) u w

theorem ExactWalk.toReflTransGen {V : Type*} {R : V → V → Prop} {k : ℕ} {u v : V}
    (hw : ExactWalk R k u v) : Relation.ReflTransGen R u v := by
  induction hw with
  | zero _ => exact .refl
  | step _ hs ih => exact ih.tail hs

theorem ExactWalk.pad {V : Type*} (R : V → V → Prop) (hrefl : ∀ v, R v v)
    {m ℓ : ℕ} {u v : V} (hm : m ≤ ℓ) (hw : ExactWalk R m u v) : ExactWalk R ℓ u v := by
  induction ℓ, hm using Nat.le_induction with
  | base => exact hw
  | succ _ _ ih => exact ih.step (hrefl v)

theorem exactWalk_of_reflTransGen_bound {V : Type*} [Fintype V] {R : V → V → Prop}
    {u v : V} (h : Relation.ReflTransGen R u v) :
    ∃ m ≤ Fintype.card V - 1, ExactWalk R m u v := by
  classical
  have hex : ∃ m, ExactWalk R m u v := by
    induction h with
    | refl => exact ⟨0, .zero _⟩
    | tail _ hstep ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, hm.step hstep⟩
  let m := Nat.find hex
  have hm : ExactWalk R m u v := Nat.find_spec hex
  refine ⟨m, ?_, hm⟩
  by_contra hgt
  push Not at hgt
  have hverts : ∀ {k : ℕ} {a b : V}, ExactWalk R k a b →
      ∃ f : Fin (k + 1) → V, f 0 = a ∧ f (Fin.last k) = b ∧
        ∀ i : Fin k, R (f i.castSucc) (f i.succ) := by
    intro k a b hw
    induction hw with
    | zero x =>
      exact ⟨fun _ => x, rfl, rfl, fun i => Fin.elim0 i⟩
    | @step n x y z _ hstep ih =>
      obtain ⟨f, hf0, hflast, hfstep⟩ := ih
      refine ⟨Fin.snoc f z, by simp [hf0], by simp, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Fin.snoc_castSucc, hflast, hstep]
      · rw [Fin.snoc_castSucc]
        have h : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
        rw [h, Fin.snoc_castSucc]
        exact hfstep j
  obtain ⟨f, hf0, hflast, hfstep⟩ := hverts hm
  have hcard : Fintype.card V < Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
    omega
  obtain ⟨i, j, hij, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hfeq.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
  have walk_seg : ∀ (p q : Fin (m + 1)), p ≤ q → ExactWalk R (q.val - p.val) (f p) (f q) := by
    intro p q hpq
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hpq
    have hd_sub : q.val - p.val = d := by omega
    rw [hd_sub]
    induction d generalizing q with
    | zero =>
      have hpq' : p = q := Fin.ext (by omega)
      subst hpq'
      exact .zero _
    | succ d ih =>
      have hq' : p.val + d < m + 1 := by omega
      let q' : Fin (m + 1) := ⟨p.val + d, hq'⟩
      have hw' : ExactWalk R d (f p) (f q') :=
        ih q' (Fin.mk_le_mk.2 (Nat.le_add_right _ _)) (by simp [q']) (by simp [q'])
      have hstep' : R (f q') (f q) := by
        have hlt_m : p.val + d < m := by omega
        let idx : Fin m := ⟨p.val + d, hlt_m⟩
        have h1 : idx.castSucc = q' := Fin.ext rfl
        have h2 : idx.succ = q := Fin.ext (by change p.val + d + 1 = q.val; omega)
        simpa [h1, h2] using hfstep idx
      exact hw'.step hstep'
  have walk_trans : ∀ {k₁ k₂ : ℕ} {a b c : V},
      ExactWalk R k₁ a b → ExactWalk R k₂ b c → ExactWalk R (k₁ + k₂) a c := by
    intro k₁ k₂ a b c w1 w2
    induction w2 with
    | zero _ => simpa using w1
    | step _ hs ih => exact (ih w1).step hs
  have w1 : ExactWalk R i.val u (f i) := by
    simpa [hf0] using walk_seg 0 i (Fin.zero_le i)
  have w2 : ExactWalk R (m - j.val) (f j) v := by
    simpa [hflast] using walk_seg j (Fin.last m) (Fin.le_last j)
  rw [← hfeq] at w2
  have wshort : ExactWalk R (i.val + (m - j.val)) u v := walk_trans w1 w2
  have hlt_m : i.val + (m - j.val) < m := by
    have : i.val < j.val := hlt
    have : j.val ≤ m := Nat.le_of_lt_succ j.isLt
    omega
  exact Nat.find_min hex hlt_m wshort

private theorem reflTransGen_mono {V : Type*} {R S : V → V → Prop}
    (hsub : ∀ u v, R u v → S u v) {a b : V} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen S a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hsub _ _ hs)

/-! ### Support-graph reachability and irreducibility -/

/-- Support relation of a real matrix: `i` has a directed edge to `j` iff `X i j ≠ 0`. -/
@[expose] def supportRel {V : Type*} (X : Matrix V V ℝ) (i j : V) : Prop :=
  X i j ≠ 0

/-- A square matrix `X : Matrix V V ℝ` is irreducible if its
directed support graph is strongly connected. -/
def IsIrreducibleMatrix {V : Type*} (X : Matrix V V ℝ) : Prop :=
  ∀ i j : V, Relation.ReflTransGen (supportRel X) i j

/-- Irreducibility is invariant under permutation similarity. -/
theorem isIrreducibleMatrix_reindex_iff {V W : Type*} (e : V ≃ W) (X : Matrix V V ℝ) :
    IsIrreducibleMatrix (X.reindex e e) ↔ IsIrreducibleMatrix X := by
  have hstep : ∀ u v : V,
      Relation.ReflTransGen (supportRel (X.reindex e e)) (e u) (e v) ↔
        Relation.ReflTransGen (supportRel X) u v := by
    intro u v
    constructor
    · intro h
      have hback : ∀ x y : W, Relation.ReflTransGen (supportRel (X.reindex e e)) x y →
          Relation.ReflTransGen (supportRel X) (e.symm x) (e.symm y) := by
        intro x y hxy
        induction hxy with
        | refl => exact .refl
        | tail _ hstep ih =>
          exact ih.tail (by simpa [supportRel, Matrix.reindex_apply] using hstep)
      simpa using hback (e u) (e v) h
    · intro h
      induction h with
      | refl => exact .refl
      | tail _ hstep ih =>
        exact ih.tail (by simpa [supportRel, Matrix.reindex_apply] using hstep)
  constructor
  · intro h u v
    exact (hstep u v).1 (h (e u) (e v))
  · intro h x y
    simpa using (hstep (e.symm x) (e.symm y)).2 (h (e.symm x) (e.symm y))

/-- For a nonnegative matrix with strictly positive diagonal entries, `IsIrreducibleMatrix`
coincides with Mathlib's `Matrix.IsIrreducible`. -/
theorem isIrreducibleMatrix_iff_matrix_isIrreducible {V : Type*} {X : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ X i j) (hdiag : ∀ i, 0 < X i i) :
    IsIrreducibleMatrix X ↔ X.IsIrreducible := by
  constructor
  · intro hirr
    refine ⟨hnn, fun i j => ?_⟩
    let _ : Quiver V := Matrix.toQuiver X
    have hpath : ∀ u v : V, Relation.ReflTransGen (supportRel X) u v →
        Nonempty (Quiver.Path u v) := by
      intro u v huv
      induction huv with
      | refl => exact ⟨.nil⟩
      | @tail b c _ hbc ih =>
        obtain ⟨p⟩ := ih
        have hpos : 0 < X b c := lt_of_le_of_ne (hnn b c) (Ne.symm hbc)
        exact ⟨p.cons (PLift.up hpos)⟩
    obtain ⟨p⟩ := hpath i j (hirr i j)
    refine ⟨p.cons (PLift.up (hdiag j)), by simp⟩
  · intro hirr i j
    let _ : Quiver V := Matrix.toQuiver X
    obtain ⟨p, _⟩ := hirr.connected i j
    have hwalk : ∀ {a b : V} (q : Quiver.Path a b), Relation.ReflTransGen (supportRel X) a b := by
      intro a b q
      induction q with
      | nil => exact .refl
      | @cons _ _ _ e ih => exact ih.tail (ne_of_gt e.down)
    exact hwalk p

private theorem pow_apply_nonneg_of_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ X i j) (ℓ : ℕ) (i j : V) :
    0 ≤ (X ^ ℓ) i j := by
  induction ℓ generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun t _ => mul_nonneg (ih i t) (hnn t j)

private theorem pow_apply_pos_iff_exactWalk {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ X i j) (ℓ : ℕ) (i j : V) :
    0 < (X ^ ℓ) i j ↔ ExactWalk (supportRel X) ℓ i j := by
  induction ℓ generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    constructor
    · intro h
      by_cases hij : i = j
      · subst hij; exact .zero _
      · simp [hij] at h
    · intro hw
      cases hw
      simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    constructor
    · intro hpos
      have hterm : ∃ t ∈ (Finset.univ : Finset V), 0 < (X ^ k) i t * X t j :=
        (Finset.sum_pos_iff_of_nonneg fun t _ =>
          mul_nonneg (pow_apply_nonneg_of_nonneg hnn k i t) (hnn t j)).1 hpos
      obtain ⟨t, -, ht⟩ := hterm
      have h1 : 0 < (X ^ k) i t := by
        by_contra hle; push Not at hle
        have h0 : (X ^ k) i t = 0 := le_antisymm hle (pow_apply_nonneg_of_nonneg hnn k i t)
        simp [h0] at ht
      have h2 : 0 < X t j := by
        by_contra hle; push Not at hle
        have h0 : X t j = 0 := le_antisymm hle (hnn t j)
        simp [h0] at ht
      exact ((ih i t).1 h1).step (ne_of_gt h2)
    · intro hw
      cases hw with
      | @step _ _ t _ hw' hstep =>
        have h1 : 0 < (X ^ k) i t := (ih i t).2 hw'
        have h2 : 0 < X t j := lt_of_le_of_ne (hnn t j) (Ne.symm hstep)
        exact (Finset.sum_pos_iff_of_nonneg fun s _ =>
          mul_nonneg (pow_apply_nonneg_of_nonneg hnn k i s) (hnn s j)).2
          ⟨t, Finset.mem_univ t, mul_pos h1 h2⟩

/-- If a nonnegative matrix `X` has strictly positive
diagonal entries and is irreducible, then every power `X ^ ℓ` for `ℓ ≥ |V| - 1` has strictly
positive entries throughout. -/
theorem pow_apply_pos_of_isIrreducibleMatrix {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ X i j) (hdiag : ∀ i, 0 < X i i)
    (hirr : IsIrreducibleMatrix X) {ℓ : ℕ} (hℓ : Fintype.card V - 1 ≤ ℓ) (i j : V) :
    0 < (X ^ ℓ) i j := by
  obtain ⟨m, hm, hw⟩ := exactWalk_of_reflTransGen_bound (hirr i j)
  have hpad : ExactWalk (supportRel X) ℓ i j :=
    hw.pad (supportRel X) (fun v => ne_of_gt (hdiag v)) (hm.trans hℓ)
  exact (pow_apply_pos_iff_exactWalk hnn ℓ i j).2 hpad

/-- If a nonnegative matrix `X` has strictly positive
diagonal entries and is irreducible, then `X ^ ℓ` is irreducible for every `ℓ ≥ 1`. -/
theorem isIrreducibleMatrix_pow {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ X i j) (hdiag : ∀ i, 0 < X i i)
    (hirr : IsIrreducibleMatrix X) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    IsIrreducibleMatrix (X ^ ℓ) := by
  intro i j
  have hsub : ∀ u v, supportRel X u v → supportRel (X ^ ℓ) u v := by
    intro u v huv
    have hw : ExactWalk (supportRel X) 1 u v := (ExactWalk.zero u).step huv
    have hpad := hw.pad (supportRel X) (fun w => ne_of_gt (hdiag w)) hℓ
    exact ne_of_gt ((pow_apply_pos_iff_exactWalk hnn ℓ u v).2 hpad)
  exact reflTransGen_mono hsub (hirr i j)

/-! ### Block-diagonal decomposition of symmetric nonnegative matrices -/

/-- The equivalence relation induced by a symmetric real matrix `Z`: connected components of
its support graph `G(Z)`. -/
@[expose] def inducedSetoid {V : Type*} (Z : Matrix V V ℝ) (hZ : Z.IsSymm) : Setoid V where
  r i j := Relation.ReflTransGen (supportRel Z) i j
  iseqv :=
    { refl := fun _ => .refl
      symm := fun {x y} h => by
        induction h with
        | refl => exact .refl
        | @tail b c _ hbc ih =>
          have hcb : supportRel Z c b := by
            simpa [supportRel, hZ.apply b c] using hbc
          exact Relation.ReflTransGen.head hcb ih
      trans := fun h1 h2 => h1.trans h2 }

theorem inducedSetoid_r_iff {V : Type*} {Z : Matrix V V ℝ} (hZ : Z.IsSymm) (i j : V) :
    (inducedSetoid Z hZ).r i j ↔ Relation.ReflTransGen (supportRel Z) i j :=
  Iff.rfl

theorem inducedSetoid_eq_of_eq {V : Type*} {Z₁ Z₂ : Matrix V V ℝ}
    (hZ₁ : Z₁.IsSymm) (hZ₂ : Z₂.IsSymm) (h : Z₁ = Z₂) :
    inducedSetoid Z₁ hZ₁ = inducedSetoid Z₂ hZ₂ := by
  subst h
  rfl

/-- Off-diagonal entries between distinct blocks of `inducedSetoid Z` vanish
of its induced partition. -/
theorem inducedSetoid_off_diag_zero {V : Type*} {Z : Matrix V V ℝ} (hZ : Z.IsSymm)
    {i j : V} (hne : ¬ (inducedSetoid Z hZ).r i j) : Z i j = 0 := by
  by_contra hnz
  exact hne (Relation.ReflTransGen.single hnz)

/-- Every principal block of a symmetric matrix `Z` on a class of `inducedSetoid Z` is
irreducible. -/
theorem inducedSetoid_block_isIrreducible {V : Type*} {Z : Matrix V V ℝ} (hZ : Z.IsSymm)
    (q : Quotient (inducedSetoid Z hZ)) :
    IsIrreducibleMatrix
      (Z.submatrix (Subtype.val : {v : V // Quotient.mk (inducedSetoid Z hZ) v = q} → V)
        Subtype.val) := by
  intro ⟨u, hu⟩ ⟨v, hv⟩
  have huv : Relation.ReflTransGen (supportRel Z) u v :=
    Quotient.exact (hu.trans hv.symm)
  have hlift : ∀ {a b : V}, Relation.ReflTransGen (supportRel Z) a b →
      ∀ (ha : Quotient.mk (inducedSetoid Z hZ) a = q)
        (hb : Quotient.mk (inducedSetoid Z hZ) b = q),
        Relation.ReflTransGen
          (supportRel (Z.submatrix
            (Subtype.val : {x : V // Quotient.mk (inducedSetoid Z hZ) x = q} → V) Subtype.val))
          ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b hab
    induction hab with
    | refl => intro _ _; exact .refl
    | @tail b c hab hbc ih =>
      intro ha hc
      have hb : Quotient.mk (inducedSetoid Z hZ) b = q :=
        (Quotient.sound hab).symm.trans ha
      exact (ih ha hb).tail (by simpa [supportRel] using hbc)
  exact hlift huv hu hv

/-- A block decomposition of a symmetric matrix `Z : Matrix V V ℝ` into nonempty pairwise
disjoint blocks whose off-diagonal blocks vanish and whose diagonal blocks are irreducible. -/
structure IsIrreducibleBlockDecomp {V I : Type*} (Z : Matrix V V ℝ) (D : I → Set V) : Prop where
  /-- Each block is nonempty. -/
  nonempty : ∀ i, (D i).Nonempty
  /-- Distinct blocks are disjoint. -/
  pairwiseDisjoint : Pairwise fun i j => Disjoint (D i) (D j)
  /-- The blocks cover `V`. -/
  cover : ∀ v : V, ∃ i, v ∈ D i
  /-- Off-diagonal blocks of `Z` vanish. -/
  offDiagZero : ∀ i j, i ≠ j → ∀ u ∈ D i, ∀ v ∈ D j, Z u v = 0
  /-- Each diagonal block of `Z` is irreducible. -/
  diagIrred : ∀ i, IsIrreducibleMatrix (Z.submatrix (Subtype.val : D i → V) Subtype.val)

/-- Existence of the irreducible block-diagonal decomposition: every symmetric matrix `Z`
admits a block-diagonal decomposition into irreducible blocks indexed by
`Quotient (inducedSetoid Z hZ)`. -/
theorem symm_nonneg_block_diag_exists {V : Type*} {Z : Matrix V V ℝ} (hZ : Z.IsSymm) :
    IsIrreducibleBlockDecomp Z
      (fun q : Quotient (inducedSetoid Z hZ) => {v : V | Quotient.mk (inducedSetoid Z hZ) v = q}) :=
  { nonempty := fun q => Quotient.inductionOn q fun v => ⟨v, rfl⟩
    pairwiseDisjoint := fun _ _ hij => Set.disjoint_left.2 fun _ hi hj => hij (hi.symm.trans hj)
    cover := fun v => ⟨Quotient.mk _ v, rfl⟩
    offDiagZero := fun _ _ hij _ hu _ hv =>
      inducedSetoid_off_diag_zero hZ fun h => hij (hu.symm.trans ((Quotient.sound h).trans hv))
    diagIrred := fun q => inducedSetoid_block_isIrreducible hZ q }

/-- Uniqueness of the irreducible block-diagonal decomposition: the partition underlying any
irreducible block-diagonal decomposition of a symmetric matrix `Z` is uniquely determined by
`Z` and coincides with the equivalence classes of `inducedSetoid Z hZ`. -/
theorem symm_nonneg_block_diag_unique {V I : Type*} {Z : Matrix V V ℝ} (hZ : Z.IsSymm)
    {D : I → Set V} (hD : IsIrreducibleBlockDecomp Z D) :
    (∀ i u v, u ∈ D i → (v ∈ D i ↔ (inducedSetoid Z hZ).r u v)) ∧
      ∃ e : I ≃ Quotient (inducedSetoid Z hZ),
        ∀ i, D i = {v : V | Quotient.mk (inducedSetoid Z hZ) v = e i} := by
  have hsame : ∀ i u v, u ∈ D i → (v ∈ D i ↔ (inducedSetoid Z hZ).r u v) := by
    intro i u v hu
    constructor
    · intro hv
      have hirr := hD.diagIrred i ⟨u, hu⟩ ⟨v, hv⟩
      have hproj : ∀ {x y : D i},
          Relation.ReflTransGen (supportRel (Z.submatrix Subtype.val Subtype.val)) x y →
            Relation.ReflTransGen (supportRel Z) x.1 y.1 := by
        intro x y hxy
        induction hxy with
        | refl => exact .refl
        | tail _ hstep ih => exact ih.tail hstep
      exact hproj hirr
    · intro huv
      change Relation.ReflTransGen (supportRel Z) u v at huv
      induction huv with
      | refl => exact hu
      | @tail b c _ hbc ih =>
        obtain ⟨j, hj⟩ := hD.cover c
        by_cases hij : i = j
        · exact hij ▸ hj
        · exact absurd (hD.offDiagZero i j hij b ih c hj) hbc
  refine ⟨hsame, ?_⟩
  let toQ : I → Quotient (inducedSetoid Z hZ) := fun i =>
    Quotient.mk _ (hD.nonempty i).choose
  have hblock : ∀ i, D i = {v : V | Quotient.mk (inducedSetoid Z hZ) v = toQ i} := by
    intro i
    ext v
    simp only [Set.mem_ofPred_eq, toQ, Quotient.eq]
    exact (hsame i _ v (hD.nonempty i).choose_spec).trans
      ⟨fun h => (inducedSetoid Z hZ).symm h, fun h => (inducedSetoid Z hZ).symm h⟩
  have hinj : Function.Injective toQ := by
    intro i j hij
    have hmem : (hD.nonempty i).choose ∈ D j := by rw [hblock j]; exact hij
    by_contra hne
    exact Set.disjoint_left.1 (hD.pairwiseDisjoint hne) (hD.nonempty i).choose_spec hmem
  have hsurj : Function.Surjective toQ := by
    intro q
    refine Quotient.inductionOn q fun v => ?_
    obtain ⟨i, hi⟩ := hD.cover v
    refine ⟨i, ?_⟩
    rw [hblock i] at hi
    exact hi.symm
  exact ⟨Equiv.ofBijective toQ ⟨hinj, hsurj⟩, hblock⟩

/-- Permutation-similarity form of the irreducible block-diagonal decomposition. -/
theorem symm_nonneg_perm_similarity {V : Type*} {Z : Matrix V V ℝ} (hZ : Z.IsSymm) :
    ∃ (e : (q : Quotient (inducedSetoid Z hZ)) ×
        {v : V // Quotient.mk (inducedSetoid Z hZ) v = q} ≃ V),
      (∀ q₁ q₂ (u : {v // Quotient.mk (inducedSetoid Z hZ) v = q₁})
        (v : {v // Quotient.mk (inducedSetoid Z hZ) v = q₂}),
        q₁ ≠ q₂ → Z.reindex e.symm e.symm ⟨q₁, u⟩ ⟨q₂, v⟩ = 0) ∧
      (∀ q, IsIrreducibleMatrix
        ((Z.reindex e.symm e.symm).submatrix (fun u => ⟨q, u⟩) (fun u => ⟨q, u⟩))) := by
  let e : (q : Quotient (inducedSetoid Z hZ)) ×
      {v : V // Quotient.mk (inducedSetoid Z hZ) v = q} ≃ V :=
    { toFun := fun p => p.2.1
      invFun := fun v => ⟨Quotient.mk _ v, ⟨v, rfl⟩⟩
      left_inv := fun ⟨q, ⟨v, hv⟩⟩ => by subst hv; rfl
      right_inv := fun _ => rfl }
  refine ⟨e, ?_, ?_⟩
  · intro q₁ q₂ u v hne
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply, e, Equiv.coe_fn_mk]
    exact inducedSetoid_off_diag_zero hZ fun h =>
      hne (u.2.symm.trans ((Quotient.sound h).trans v.2))
  · intro q
    exact inducedSetoid_block_isIrreducible hZ q

/-- If `Z ≥ 0` is symmetric
with strictly positive diagonal entries, then `Z ^ ℓ` induces the same partition as `Z` for
every `ℓ ≥ 1`. -/
theorem inducedSetoid_pow_eq {V : Type*} [Fintype V] [DecidableEq V]
    {Z : Matrix V V ℝ} (hZ : Z.IsSymm) (hnn : ∀ i j, 0 ≤ Z i j) (hdiag : ∀ i, 0 < Z i i)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    inducedSetoid (Z ^ ℓ) (hZ.pow ℓ) = inducedSetoid Z hZ := by
  ext i j
  constructor
  · intro h
    change Relation.ReflTransGen (supportRel (Z ^ ℓ)) i j at h
    induction h with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
      have hpos : 0 < (Z ^ ℓ) b c :=
        lt_of_le_of_ne (pow_apply_nonneg_of_nonneg hnn ℓ b c) (Ne.symm hbc)
      exact ih.trans ((pow_apply_pos_iff_exactWalk hnn ℓ b c).1 hpos).toReflTransGen
  · intro h
    have hsub : ∀ u v, supportRel Z u v → supportRel (Z ^ ℓ) u v := by
      intro u v huv
      have hw : ExactWalk (supportRel Z) 1 u v := (ExactWalk.zero u).step huv
      have hpad := hw.pad (supportRel Z) (fun w => ne_of_gt (hdiag w)) hℓ
      exact ne_of_gt ((pow_apply_pos_iff_exactWalk hnn ℓ u v).2 hpad)
    exact reflTransGen_mono hsub h

/-- For `ℓ ≥ |V| - 1`,
`(Z ^ ℓ) i j > 0` iff `i` and `j` belong to the same connected component of `G(Z)`. -/
theorem pow_apply_pos_iff_inducedSetoid {V : Type*} [Fintype V] [DecidableEq V]
    {Z : Matrix V V ℝ} (hZ : Z.IsSymm) (hnn : ∀ i j, 0 ≤ Z i j) (hdiag : ∀ i, 0 < Z i i)
    {ℓ : ℕ} (hℓ : Fintype.card V - 1 ≤ ℓ) (i j : V) :
    0 < (Z ^ ℓ) i j ↔ (inducedSetoid Z hZ).r i j := by
  rw [pow_apply_pos_iff_exactWalk hnn ℓ i j]
  refine ⟨ExactWalk.toReflTransGen, fun h => ?_⟩
  obtain ⟨m, hm, hw⟩ := exactWalk_of_reflTransGen_bound h
  exact hw.pad (supportRel Z) (fun w => ne_of_gt (hdiag w)) (hm.trans hℓ)

/-! ### Block-positive matrices and matrix-related partitions -/

/-- A symmetric nonnegative matrix `Z` with strictly positive diagonal is *good symmetric*
if every entry within a diagonal block of its induced
partition is strictly positive. -/
@[expose] def IsGoodSymmMatrix {V : Type*} (Z : Matrix V V ℝ) : Prop :=
  ∃ (hZ : Z.IsSymm), (∀ i j, 0 ≤ Z i j) ∧ (∀ i, 0 < Z i i) ∧
    ∀ i j, (inducedSetoid Z hZ).r i j → 0 < Z i j

/-- A nonnegative matrix `X : Matrix V W ℝ` without null rows or columns is *good*
if `X * Xᵀ` and `Xᵀ * X` are good symmetric. -/
@[expose] def IsGoodMatrix {V W : Type*} [Fintype V] [Fintype W] (X : Matrix V W ℝ) : Prop :=
  (∀ a b, 0 ≤ X a b) ∧ (∀ a, ∃ b, 0 < X a b) ∧ (∀ b, ∃ a, 0 < X a b) ∧
    IsGoodSymmMatrix (X * Xᵀ) ∧ IsGoodSymmMatrix (Xᵀ * X)

/-- Two indexed partitions `D : I → Set V` and `D' : I → Set W` are *`X`-related*
if `X ≥ 0` has no null rows or columns and `X a b = 0` whenever
`a ∈ D i` and `b ∈ D' j` with `i ≠ j`. -/
structure AreMatrixRelated {V W I : Type*} (X : Matrix V W ℝ)
    (D : I → Set V) (D' : I → Set W) : Prop where
  /-- Nonnegativity of `X`. -/
  nonneg : ∀ a b, 0 ≤ X a b
  /-- No null rows. -/
  noNullRows : ∀ a, ∃ b, 0 < X a b
  /-- No null columns. -/
  noNullCols : ∀ b, ∃ a, 0 < X a b
  /-- `D` is a partition of `V` into nonempty blocks. -/
  nonemptyLeft : ∀ i, (D i).Nonempty
  /-- Distinct blocks of `D` are disjoint. -/
  disjointLeft : Pairwise fun i j => Disjoint (D i) (D j)
  /-- `D` covers `V`. -/
  coverLeft : ∀ a, ∃ i, a ∈ D i
  /-- `D'` is a partition of `W` into nonempty blocks. -/
  nonemptyRight : ∀ i, (D' i).Nonempty
  /-- Distinct blocks of `D'` are disjoint. -/
  disjointRight : Pairwise fun i j => Disjoint (D' i) (D' j)
  /-- `D'` covers `W`. -/
  coverRight : ∀ b, ∃ i, b ∈ D' i
  /-- Off-diagonal blocks of `X` vanish. -/
  offDiagZero : ∀ i j, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D' j, X a b = 0

/-- Recovery of `D' i` from `D i` via positive entries of `X`. -/
theorem AreMatrixRelated.mem_right_iff {V W I : Type*} {X : Matrix V W ℝ}
    {D : I → Set V} {D' : I → Set W} (h : AreMatrixRelated X D D') (i : I) (b : W) :
    b ∈ D' i ↔ ∃ a ∈ D i, 0 < X a b := by
  constructor
  · intro hb
    obtain ⟨a, ha_pos⟩ := h.noNullCols b
    obtain ⟨j, haj⟩ := h.coverLeft a
    by_cases hji : j = i
    · exact ⟨a, hji ▸ haj, ha_pos⟩
    · exact absurd (h.offDiagZero j i hji a haj b hb) (ne_of_gt ha_pos)
  · rintro ⟨a, ha, hpos⟩
    obtain ⟨j, hbj⟩ := h.coverRight b
    by_cases hij : i = j
    · exact hij ▸ hbj
    · exact absurd (h.offDiagZero i j hij a ha b hbj) (ne_of_gt hpos)

/-- Symmetric recovery of `D i` from `D' i` via `X`. -/
theorem AreMatrixRelated.mem_left_iff {V W I : Type*} {X : Matrix V W ℝ}
    {D : I → Set V} {D' : I → Set W} (h : AreMatrixRelated X D D') (i : I) (a : V) :
    a ∈ D i ↔ ∃ b ∈ D' i, 0 < X a b := by
  constructor
  · intro ha
    obtain ⟨b, hb_pos⟩ := h.noNullRows a
    obtain ⟨j, hbj⟩ := h.coverRight b
    by_cases hij : i = j
    · exact ⟨b, hij ▸ hbj, hb_pos⟩
    · exact absurd (h.offDiagZero i j hij a ha b hbj) (ne_of_gt hb_pos)
  · rintro ⟨b, hb, hpos⟩
    obtain ⟨j, haj⟩ := h.coverLeft a
    by_cases hji : j = i
    · exact hji ▸ haj
    · exact absurd (h.offDiagZero j i hji a haj b hb) (ne_of_gt hpos)

/-- Characteristic vector of a subset `S ⊆ V` over `ℝ`. -/
noncomputable def charVec {V : Type*} (S : Set V) : V → ℝ :=
  fun v => by classical exact if v ∈ S then 1 else 0

theorem charVec_apply_of_mem {V : Type*} {S : Set V} {v : V} (hv : v ∈ S) :
    charVec S v = 1 := by
  classical simp [charVec, hv]

theorem charVec_apply_of_notMem {V : Type*} {S : Set V} {v : V} (hv : v ∉ S) :
    charVec S v = 0 := by
  classical simp [charVec, hv]

theorem mulVec_charVec_apply {V W : Type*} [Fintype W] (X : Matrix V W ℝ) (S : Set W) (a : V) :
    (X *ᵥ charVec S) a = ∑ b : W, by classical exact if b ∈ S then X a b else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, charVec, mul_ite, mul_one, mul_zero]

/-- The cardinality of `{x | x ∈ S}` in `Finset.univ` equals `S.ncard`. -/
theorem sum_charVec_filter_eq_ncard {V : Type*} [Fintype V] (S : Set V)
    [DecidablePred (· ∈ S)] :
    ((Finset.univ.filter (· ∈ S)).card : ℝ) = (S.ncard : ℝ) := by
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

/-- Rectangular doubly stochastic block preservation: if two
partitions `D` of `V` and `D'` of `W` are `X`-related for a rectangular doubly stochastic
matrix `X`, then corresponding blocks have equal cardinalities and their characteristic vectors
satisfy `charVec (D i) = X *ᵥ charVec (D' i)` and `charVec (D' i) = Xᵀ *ᵥ charVec (D i)`. -/
theorem rectDoublyStochastic_related_card_and_charVec {V W I : Type*} [Fintype V] [Fintype W]
    {X : Matrix V W ℝ} (hX : IsRectDoublyStochastic X)
    {D : I → Set V} {D' : I → Set W} (hrel : AreMatrixRelated X D D') (i : I) :
    (D i).ncard = (D' i).ncard ∧
      X *ᵥ charVec (D' i) = charVec (D i) ∧
      Xᵀ *ᵥ charVec (D i) = charVec (D' i) := by
  classical
  have hboundL : ∀ a : V, 0 ≤ (X *ᵥ charVec (D' i)) a ∧ (X *ᵥ charVec (D' i)) a ≤ 1 := by
    intro a
    rw [mulVec_charVec_apply]
    refine ⟨Finset.sum_nonneg fun b _ => by split_ifs <;> [exact hX.1 a b; rfl], ?_⟩
    calc ∑ b : W, (if b ∈ D' i then X a b else 0)
        ≤ ∑ b : W, X a b := Finset.sum_le_sum fun b _ => by split_ifs <;> [rfl; exact hX.1 a b]
      _ = 1 := hX.2.1 a
  have hzeroL : ∀ a : V, a ∉ D i → (X *ᵥ charVec (D' i)) a = 0 := by
    intro a ha
    rw [mulVec_charVec_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · obtain ⟨j, haj⟩ := hrel.coverLeft a
      have hji : j ≠ i := fun h => ha (h ▸ haj)
      exact hrel.offDiagZero j i hji a haj b hb
    · rfl
  have hsumL : ∑ a : V, (X *ᵥ charVec (D' i)) a = ((D' i).ncard : ℝ) := by
    simp_rw [mulVec_charVec_apply]
    rw [Finset.sum_comm]
    have hinner : ∀ b : W, (∑ a : V, if b ∈ D' i then X a b else 0) =
        if b ∈ D' i then 1 else 0 := by
      intro b
      split_ifs with hb
      · exact hX.2.2 b
      · simp
    simp_rw [hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact sum_charVec_filter_eq_ncard (D' i)
  have hsumL_D : ∑ a ∈ Finset.univ.filter (· ∈ D i), (X *ᵥ charVec (D' i)) a =
      ((D' i).ncard : ℝ) := by
    rw [← hsumL]
    exact Finset.sum_subset (Finset.filter_subset _ _) fun a _ ha =>
      hzeroL a (fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  have hle1 : ((D' i).ncard : ℝ) ≤ ((D i).ncard : ℝ) := by
    rw [← hsumL_D]
    calc ∑ a ∈ Finset.univ.filter (· ∈ D i), (X *ᵥ charVec (D' i)) a
        ≤ ∑ _a ∈ Finset.univ.filter (· ∈ D i), (1 : ℝ) :=
          Finset.sum_le_sum fun a _ => (hboundL a).2
      _ = ((Finset.univ.filter (· ∈ D i)).card : ℝ) := by simp
      _ = ((D i).ncard : ℝ) := sum_charVec_filter_eq_ncard (D i)
  have hboundR : ∀ b : W, 0 ≤ (Xᵀ *ᵥ charVec (D i)) b ∧ (Xᵀ *ᵥ charVec (D i)) b ≤ 1 := by
    intro b
    rw [mulVec_charVec_apply]
    simp only [Matrix.transpose_apply]
    refine ⟨Finset.sum_nonneg fun a _ => by split_ifs <;> [exact hX.1 a b; rfl], ?_⟩
    calc ∑ a : V, (if a ∈ D i then X a b else 0)
        ≤ ∑ a : V, X a b := Finset.sum_le_sum fun a _ => by split_ifs <;> [rfl; exact hX.1 a b]
      _ = 1 := hX.2.2 b
  have hzeroR : ∀ b : W, b ∉ D' i → (Xᵀ *ᵥ charVec (D i)) b = 0 := by
    intro b hb
    rw [mulVec_charVec_apply]
    simp only [Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with ha
    · obtain ⟨j, hbj⟩ := hrel.coverRight b
      have hij : i ≠ j := fun h => hb (h ▸ hbj)
      exact hrel.offDiagZero i j hij a ha b hbj
    · rfl
  have hsumR : ∑ b : W, (Xᵀ *ᵥ charVec (D i)) b = ((D i).ncard : ℝ) := by
    simp_rw [mulVec_charVec_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    have hinner : ∀ a : V, (∑ b : W, if a ∈ D i then X a b else 0) =
        if a ∈ D i then 1 else 0 := by
      intro a
      split_ifs with ha
      · exact hX.2.1 a
      · simp
    simp_rw [hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact sum_charVec_filter_eq_ncard (D i)
  have hsumR_D : ∑ b ∈ Finset.univ.filter (· ∈ D' i), (Xᵀ *ᵥ charVec (D i)) b =
      ((D i).ncard : ℝ) := by
    rw [← hsumR]
    exact Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb =>
      hzeroR b (fun h => hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  have hle2 : ((D i).ncard : ℝ) ≤ ((D' i).ncard : ℝ) := by
    rw [← hsumR_D]
    calc ∑ b ∈ Finset.univ.filter (· ∈ D' i), (Xᵀ *ᵥ charVec (D i)) b
        ≤ ∑ _b ∈ Finset.univ.filter (· ∈ D' i), (1 : ℝ) :=
          Finset.sum_le_sum fun b _ => (hboundR b).2
      _ = ((Finset.univ.filter (· ∈ D' i)).card : ℝ) := by simp
      _ = ((D' i).ncard : ℝ) := sum_charVec_filter_eq_ncard (D' i)
  have hcard_eq : (D i).ncard = (D' i).ncard :=
    Nat.cast_injective (le_antisymm hle2 hle1)
  have heqL : X *ᵥ charVec (D' i) = charVec (D i) := by
    ext a
    by_cases ha : a ∈ D i
    · rw [charVec_apply_of_mem ha]
      have hdiff : ∑ x ∈ Finset.univ.filter (· ∈ D i), (1 - (X *ᵥ charVec (D' i)) x) = 0 := by
        rw [Finset.sum_sub_distrib, hsumL_D, ← hcard_eq]
        simp [sum_charVec_filter_eq_ncard (D i)]
      have hnonneg : ∀ x ∈ Finset.univ.filter (· ∈ D i), 0 ≤ 1 - (X *ᵥ charVec (D' i)) x :=
        fun x _ => sub_nonneg.2 (hboundL x).2
      have ha0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hdiff a (by simp [ha])
      linarith
    · rw [charVec_apply_of_notMem ha, hzeroL a ha]
  have heqR : Xᵀ *ᵥ charVec (D i) = charVec (D' i) := by
    ext b
    by_cases hb : b ∈ D' i
    · rw [charVec_apply_of_mem hb]
      have hdiff : ∑ y ∈ Finset.univ.filter (· ∈ D' i), (1 - (Xᵀ *ᵥ charVec (D i)) y) = 0 := by
        rw [Finset.sum_sub_distrib, hsumR_D, hcard_eq]
        simp [sum_charVec_filter_eq_ncard (D' i)]
      have hnonneg : ∀ y ∈ Finset.univ.filter (· ∈ D' i), 0 ≤ 1 - (Xᵀ *ᵥ charVec (D i)) y :=
        fun y _ => sub_nonneg.2 (hboundR y).2
      have hb0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hdiff b (by simp [hb])
      linarith
    · rw [charVec_apply_of_notMem hb, hzeroR b hb]
  exact ⟨hcard_eq, heqL, heqR⟩

/-- Square doubly stochastic block preservation: matching blocks have equal cardinality and
preserved indicator vectors. -/
theorem doublyStochastic_related_card_and_charVec {V I : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hX : X ∈ doublyStochastic ℝ V)
    {D D' : I → Set V} (hrel : AreMatrixRelated X D D') (i : I) :
    (D i).ncard = (D' i).ncard ∧
      X *ᵥ charVec (D' i) = charVec (D i) ∧
      Xᵀ *ᵥ charVec (D i) = charVec (D' i) :=
  rectDoublyStochastic_related_card_and_charVec
    (isRectDoublyStochastic_iff_mem_doublyStochastic.2 hX) hrel i

/-- `X * Xᵀ` is symmetric with nonnegative entries and positive diagonal when `X ≥ 0` has no
null rows. -/
theorem mul_transpose_isSymm_nonneg_pos_diag {V W : Type*} [Fintype W] {X : Matrix V W ℝ}
    (hnn : ∀ a b, 0 ≤ X a b) (hrow : ∀ a, ∃ b, 0 < X a b) :
    (X * Xᵀ).IsSymm ∧ (∀ a₁ a₂, 0 ≤ (X * Xᵀ) a₁ a₂) ∧ (∀ a, 0 < (X * Xᵀ) a a) := by
  refine ⟨?_, ?_, ?_⟩
  · ext a₁ a₂
    simp only [Matrix.transpose_apply, Matrix.mul_apply, mul_comm]
  · intro a₁ a₂
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hnn a₁ b) (hnn a₂ b)
  · intro a
    obtain ⟨b, hb⟩ := hrow a
    exact (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn a c) (hnn a c)).2
      ⟨b, Finset.mem_univ b, mul_pos hb hb⟩

/-- For `X : Matrix V W ℝ` nonnegative
without null rows or columns, `Z = X * Xᵀ` and `Z' = Xᵀ * X` are symmetric with strictly
positive diagonals, and their induced partitions are `X`-related via a canonical bijection. -/
theorem mul_transpose_related_partitions {V W : Type*} [Fintype V] [Fintype W] {X : Matrix V W ℝ}
    (hnn : ∀ a b, 0 ≤ X a b) (hrow : ∀ a, ∃ b, 0 < X a b) (hcol : ∀ b, ∃ a, 0 < X a b) :
    ∃ (hZ : (X * Xᵀ).IsSymm) (hZ' : (Xᵀ * X).IsSymm)
      (e : Quotient (inducedSetoid (X * Xᵀ) hZ) ≃ Quotient (inducedSetoid (Xᵀ * X) hZ')),
      (∀ a, 0 < (X * Xᵀ) a a) ∧
      (∀ b, 0 < (Xᵀ * X) b b) ∧
      AreMatrixRelated X
        (fun q => {a : V | Quotient.mk (inducedSetoid (X * Xᵀ) hZ) a = q})
        (fun q => {b : W | Quotient.mk (inducedSetoid (Xᵀ * X) hZ') b = e q}) := by
  obtain ⟨hZ, hZnn, hZdiag⟩ := mul_transpose_isSymm_nonneg_pos_diag hnn hrow
  obtain ⟨hZ', hZ'nn, hZ'diag⟩ :=
    mul_transpose_isSymm_nonneg_pos_diag (X := Xᵀ) (fun b a => hnn a b) hcol
  have hZ'_eq : Xᵀ * (Xᵀ)ᵀ = Xᵀ * X := by rw [Matrix.transpose_transpose]
  rw [hZ'_eq] at hZ' hZ'nn hZ'diag
  have hstepL : ∀ {a₁ a₂ : V}, supportRel (X * Xᵀ) a₁ a₂ →
      ∀ {b₁ b₂ : W}, 0 < X a₁ b₁ → 0 < X a₂ b₂ →
        (inducedSetoid (Xᵀ * X) hZ').r b₁ b₂ := by
    intro a₁ a₂ ha b₁ b₂ hb₁ hb₂
    have hpos : 0 < (X * Xᵀ) a₁ a₂ := lt_of_le_of_ne (hZnn a₁ a₂) (Ne.symm ha)
    obtain ⟨b, -, hbm⟩ := (Finset.sum_pos_iff_of_nonneg fun c _ =>
      mul_nonneg (hnn a₁ c) (hnn a₂ c)).1 hpos
    have h1 : 0 < X a₁ b := by
      by_contra hle; push Not at hle
      have h0 : X a₁ b = 0 := le_antisymm hle (hnn a₁ b)
      simp [h0] at hbm
    have h2 : 0 < X a₂ b := by
      by_contra hle; push Not at hle
      have h0 : X a₂ b = 0 := le_antisymm hle (hnn a₂ b)
      simp [h0] at hbm
    have r1 : supportRel (Xᵀ * X) b₁ b := ne_of_gt <|
      (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn c b₁) (hnn c b)).2
        ⟨a₁, Finset.mem_univ a₁, mul_pos hb₁ h1⟩
    have r2 : supportRel (Xᵀ * X) b b₂ := ne_of_gt <|
      (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn c b) (hnn c b₂)).2
        ⟨a₂, Finset.mem_univ a₂, mul_pos h2 hb₂⟩
    exact (Relation.ReflTransGen.single r1).trans (Relation.ReflTransGen.single r2)
  have hmapL : ∀ {a₁ a₂ : V}, (inducedSetoid (X * Xᵀ) hZ).r a₁ a₂ →
      ∀ {b₁ b₂ : W}, 0 < X a₁ b₁ → 0 < X a₂ b₂ →
        (inducedSetoid (Xᵀ * X) hZ').r b₁ b₂ := by
    intro a₁ a₂ ha
    induction ha with
    | refl =>
      intro b₁ b₂ hb₁ hb₂
      have r12 : supportRel (Xᵀ * X) b₁ b₂ := ne_of_gt <|
        (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn c b₁) (hnn c b₂)).2
          ⟨a₁, Finset.mem_univ a₁, mul_pos hb₁ hb₂⟩
      exact Relation.ReflTransGen.single r12
    | @tail x y _ hxy ih =>
      intro b₁ b₂ hb₁ hb₂
      obtain ⟨bx, hbx⟩ := hrow x
      exact (ih hb₁ hbx).trans (hstepL hxy hbx hb₂)
  have hstepR : ∀ {b₁ b₂ : W}, supportRel (Xᵀ * X) b₁ b₂ →
      ∀ {a₁ a₂ : V}, 0 < X a₁ b₁ → 0 < X a₂ b₂ →
        (inducedSetoid (X * Xᵀ) hZ).r a₁ a₂ := by
    intro b₁ b₂ hb a₁ a₂ ha₁ ha₂
    have hpos : 0 < (Xᵀ * X) b₁ b₂ := lt_of_le_of_ne (hZ'nn b₁ b₂) (Ne.symm hb)
    obtain ⟨a, -, ham⟩ := (Finset.sum_pos_iff_of_nonneg fun c _ =>
      mul_nonneg (hnn c b₁) (hnn c b₂)).1 hpos
    have h1 : 0 < X a b₁ := by
      by_contra hle; push Not at hle
      have h0 : X a b₁ = 0 := le_antisymm hle (hnn a b₁)
      simp [h0] at ham
    have h2 : 0 < X a b₂ := by
      by_contra hle; push Not at hle
      have h0 : X a b₂ = 0 := le_antisymm hle (hnn a b₂)
      simp [h0] at ham
    have r1 : supportRel (X * Xᵀ) a₁ a := ne_of_gt <|
      (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn a₁ c) (hnn a c)).2
        ⟨b₁, Finset.mem_univ b₁, mul_pos ha₁ h1⟩
    have r2 : supportRel (X * Xᵀ) a a₂ := ne_of_gt <|
      (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn a c) (hnn a₂ c)).2
        ⟨b₂, Finset.mem_univ b₂, mul_pos h2 ha₂⟩
    exact (Relation.ReflTransGen.single r1).trans (Relation.ReflTransGen.single r2)
  have hmapR : ∀ {b₁ b₂ : W}, (inducedSetoid (Xᵀ * X) hZ').r b₁ b₂ →
      ∀ {a₁ a₂ : V}, 0 < X a₁ b₁ → 0 < X a₂ b₂ →
        (inducedSetoid (X * Xᵀ) hZ).r a₁ a₂ := by
    intro b₁ b₂ hb
    induction hb with
    | refl =>
      intro a₁ a₂ ha₁ ha₂
      have r12 : supportRel (X * Xᵀ) a₁ a₂ := ne_of_gt <|
        (Finset.sum_pos_iff_of_nonneg fun c _ => mul_nonneg (hnn a₁ c) (hnn a₂ c)).2
          ⟨b₁, Finset.mem_univ b₁, mul_pos ha₁ ha₂⟩
      exact Relation.ReflTransGen.single r12
    | @tail x y _ hxy ih =>
      intro a₁ a₂ ha₁ ha₂
      obtain ⟨ax, hax⟩ := hcol x
      exact (ih ha₁ hax).trans (hstepR hxy hax ha₂)
  let e : Quotient (inducedSetoid (X * Xᵀ) hZ) ≃ Quotient (inducedSetoid (Xᵀ * X) hZ') :=
    { toFun := Quotient.lift (fun a => Quotient.mk _ (hrow a).choose) fun a₁ a₂ ha =>
        Quotient.sound (hmapL ha (hrow a₁).choose_spec (hrow a₂).choose_spec)
      invFun := Quotient.lift (fun b => Quotient.mk _ (hcol b).choose) fun b₁ b₂ hb =>
        Quotient.sound (hmapR hb (hcol b₁).choose_spec (hcol b₂).choose_spec)
      left_inv := fun q => Quotient.inductionOn q fun a =>
        Quotient.sound (hmapR .refl (hcol (hrow a).choose).choose_spec (hrow a).choose_spec)
      right_inv := fun q => Quotient.inductionOn q fun b =>
        Quotient.sound (hmapL .refl (hrow (hcol b).choose).choose_spec (hcol b).choose_spec) }
  refine ⟨hZ, hZ', e, hZdiag, hZ'diag, ?_⟩
  refine
    { nonneg := hnn
      noNullRows := hrow
      noNullCols := hcol
      nonemptyLeft := fun q => Quotient.inductionOn q fun a => ⟨a, rfl⟩
      disjointLeft := fun _ _ hne => Set.disjoint_left.2 fun _ h1 h2 => hne (h1.symm.trans h2)
      coverLeft := fun a => ⟨Quotient.mk _ a, rfl⟩
      nonemptyRight := fun q => Quotient.inductionOn (e q) fun b => ⟨b, rfl⟩
      disjointRight := fun _ _ hne =>
        Set.disjoint_left.2 fun _ h1 h2 => hne (e.injective (h1.symm.trans h2))
      coverRight := fun b => ⟨e.symm (Quotient.mk _ b), by simp⟩
      offDiagZero := fun q₁ q₂ hne a ha b hb => by
        by_contra hnz
        have hpos : 0 < X a b := lt_of_le_of_ne (hnn a b) (Ne.symm hnz)
        have heq : e (Quotient.mk _ a) = Quotient.mk _ b :=
          Quotient.sound (hmapL .refl (hrow a).choose_spec hpos)
        exact hne (e.injective (by rw [← ha, heq, hb])) }

/-- A nonnegative matrix `X` is *block-positive* if it has no null rows or columns and is
strictly positive on every pair `(a, b)` in matching blocks of the `X`-related partitions
induced by `X * Xᵀ` and `Xᵀ * X`. -/
@[expose] def IsBlockPositiveMatrix {V W : Type*} [Fintype V] [Fintype W]
    (X : Matrix V W ℝ) : Prop :=
  ∃ (hZ : (X * Xᵀ).IsSymm) (hZ' : (Xᵀ * X).IsSymm)
    (e : Quotient (inducedSetoid (X * Xᵀ) hZ) ≃ Quotient (inducedSetoid (Xᵀ * X) hZ')),
    AreMatrixRelated X
      (fun q => {a : V | Quotient.mk (inducedSetoid (X * Xᵀ) hZ) a = q})
      (fun q => {b : W | Quotient.mk (inducedSetoid (Xᵀ * X) hZ') b = e q}) ∧
    (∀ a b, e (Quotient.mk (inducedSetoid (X * Xᵀ) hZ) a) =
        Quotient.mk (inducedSetoid (Xᵀ * X) hZ') b → 0 < X a b)

/-- Matrix identity `(X * Xᵀ) ^ ℓ * X = X * (Xᵀ * X) ^ ℓ`. -/
theorem mul_transpose_pow_mul {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (X : Matrix V W ℝ) (ℓ : ℕ) : (X * Xᵀ) ^ ℓ * X = X * (Xᵀ * X) ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ k ih =>
    calc (X * Xᵀ) ^ (k + 1) * X
        = (X * Xᵀ) * ((X * Xᵀ) ^ k * X) := by rw [pow_succ', Matrix.mul_assoc]
      _ = (X * Xᵀ) * (X * (Xᵀ * X) ^ k) := by rw [ih]
      _ = X * ((Xᵀ * X) * (Xᵀ * X) ^ k) := by simp only [Matrix.mul_assoc]
      _ = X * (Xᵀ * X) ^ (k + 1) := by rw [pow_succ']

/-- For nonnegative `X : Matrix V W ℝ`
without null rows or columns, `Z = X * Xᵀ`, `Z' = Xᵀ * X`, and `ℓ ≥ |V| - 1`, the matrix
`X̂ = Z ^ ℓ * X = X * (Z') ^ ℓ` is good (and block-positive), relates the partitions induced by
`Z` and `Z'`, is strictly positive on every matching block pair `D_i × D'_i`, and vanishes on
non-matching block pairs `D_i × D'_j` (`i ≠ j`). -/
theorem mul_transpose_pow_mul_blockPositive {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {X : Matrix V W ℝ} (hnn : ∀ a b, 0 ≤ X a b)
    (hrow : ∀ a, ∃ b, 0 < X a b) (hcol : ∀ b, ∃ a, 0 < X a b)
    {ℓ : ℕ} (hℓ : Fintype.card V - 1 ≤ ℓ) :
    let Z := X * Xᵀ
    let Z' := Xᵀ * X
    let Xhat := Z ^ ℓ * X
    Xhat = X * Z' ^ ℓ ∧
      IsGoodMatrix Xhat ∧
      IsBlockPositiveMatrix Xhat ∧
      ∃ (hZ : Z.IsSymm) (hZ' : Z'.IsSymm)
        (e : Quotient (inducedSetoid Z hZ) ≃ Quotient (inducedSetoid Z' hZ')),
        AreMatrixRelated Xhat
          (fun q => {a : V | Quotient.mk (inducedSetoid Z hZ) a = q})
          (fun q => {b : W | Quotient.mk (inducedSetoid Z' hZ') b = e q}) ∧
        (∀ q a b, Quotient.mk (inducedSetoid Z hZ) a = q →
          Quotient.mk (inducedSetoid Z' hZ') b = e q → 0 < Xhat a b) ∧
        (∀ q₁ q₂, q₁ ≠ q₂ → ∀ a b, Quotient.mk (inducedSetoid Z hZ) a = q₁ →
          Quotient.mk (inducedSetoid Z' hZ') b = e q₂ → Xhat a b = 0) := by
  intro Z Z' Xhat
  have hcomm : Xhat = X * Z' ^ ℓ := mul_transpose_pow_mul X ℓ
  obtain ⟨hZ, hZ', e, hZdiag, hZ'diag, hrel⟩ := mul_transpose_related_partitions hnn hrow hcol
  have hZnn : ∀ a₁ a₂, 0 ≤ Z a₁ a₂ := (mul_transpose_isSymm_nonneg_pos_diag hnn hrow).2.1
  have hZℓnn : ∀ a₁ a₂, 0 ≤ (Z ^ ℓ) a₁ a₂ := pow_apply_nonneg_of_nonneg hZnn ℓ
  have hXhat_nn : ∀ a b, 0 ≤ Xhat a b := fun a b =>
    Finset.sum_nonneg fun c _ => mul_nonneg (hZℓnn a c) (hnn c b)
  have hpos_match : ∀ q a b, Quotient.mk (inducedSetoid Z hZ) a = q →
      Quotient.mk (inducedSetoid Z' hZ') b = e q → 0 < Xhat a b := by
    intro q a b ha hb
    obtain ⟨c, hc_mem, hc_pos⟩ := (hrel.mem_right_iff q b).1 hb
    have hac : (inducedSetoid Z hZ).r a c := Quotient.exact (ha.trans hc_mem.symm)
    have hZℓpos : 0 < (Z ^ ℓ) a c :=
      (pow_apply_pos_iff_inducedSetoid hZ hZnn hZdiag hℓ a c).2 hac
    exact (Finset.sum_pos_iff_of_nonneg fun t _ => mul_nonneg (hZℓnn a t) (hnn t b)).2
      ⟨c, Finset.mem_univ c, mul_pos hZℓpos hc_pos⟩
  have hzero_off : ∀ q₁ q₂, q₁ ≠ q₂ → ∀ a b, Quotient.mk (inducedSetoid Z hZ) a = q₁ →
      Quotient.mk (inducedSetoid Z' hZ') b = e q₂ → Xhat a b = 0 := by
    intro q₁ q₂ hne a b ha hb
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : Quotient.mk (inducedSetoid Z hZ) c = q₁
    · have hX0 : X c b = 0 := hrel.offDiagZero q₁ q₂ hne c hc b hb
      simp [hX0]
    · have hnot : ¬ (inducedSetoid Z hZ).r a c := fun h =>
        hc ((Quotient.sound h).symm.trans ha)
      have hZ0 : (Z ^ ℓ) a c = 0 := by
        by_contra hnz
        exact hnot ((pow_apply_pos_iff_inducedSetoid hZ hZnn hZdiag hℓ a c).1
          (lt_of_le_of_ne (hZℓnn a c) (Ne.symm hnz)))
      simp [hZ0]
  have hXhat_row : ∀ a, ∃ b, 0 < Xhat a b := by
    intro a
    let q := Quotient.mk (inducedSetoid Z hZ) a
    obtain ⟨b, hb⟩ := hrel.nonemptyRight q
    exact ⟨b, hpos_match q a b rfl hb⟩
  have hXhat_col : ∀ b, ∃ a, 0 < Xhat a b := by
    intro b
    let q := e.symm (Quotient.mk (inducedSetoid Z' hZ') b)
    obtain ⟨a, ha⟩ := hrel.nonemptyLeft q
    exact ⟨a, hpos_match q a b ha (by simp [q])⟩
  have hXhat_rel : AreMatrixRelated Xhat
      (fun q => {a : V | Quotient.mk (inducedSetoid Z hZ) a = q})
      (fun q => {b : W | Quotient.mk (inducedSetoid Z' hZ') b = e q}) :=
    { nonneg := hXhat_nn
      noNullRows := hXhat_row
      noNullCols := hXhat_col
      nonemptyLeft := hrel.nonemptyLeft
      disjointLeft := hrel.disjointLeft
      coverLeft := hrel.coverLeft
      nonemptyRight := hrel.nonemptyRight
      disjointRight := hrel.disjointRight
      coverRight := hrel.coverRight
      offDiagZero := fun q₁ q₂ hne a ha b hb => hzero_off q₁ q₂ hne a b ha hb }
  have hXXt : Xhat * Xhatᵀ = Z ^ (2 * ℓ + 1) := by
    calc Xhat * Xhatᵀ = (Z ^ ℓ * X) * (Xᵀ * (Z ^ ℓ)ᵀ) := by
          simp only [Xhat, Matrix.transpose_mul]
      _ = Z ^ ℓ * (X * Xᵀ) * Z ^ ℓ := by
          rw [(hZ.pow ℓ).eq, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Z ^ ℓ * Z * Z ^ ℓ := rfl
      _ = Z ^ (ℓ + 1 + ℓ) := by rw [← pow_succ, ← pow_add]
      _ = Z ^ (2 * ℓ + 1) := by congr 1; omega
  have hsymL : (Xhat * Xhatᵀ).IsSymm := hXXt ▸ hZ.pow (2 * ℓ + 1)
  have hsetL : inducedSetoid (Xhat * Xhatᵀ) hsymL = inducedSetoid Z hZ := by
    simpa only [hXXt] using inducedSetoid_pow_eq hZ hZnn hZdiag (by omega : 1 ≤ 2 * ℓ + 1)
  have hgoodL : IsGoodSymmMatrix (Xhat * Xhatᵀ) := by
    refine ⟨hsymL, ?_, ?_, ?_⟩
    · intro a₁ a₂; rw [hXXt]; exact pow_apply_nonneg_of_nonneg hZnn _ a₁ a₂
    · intro a
      rw [hXXt]
      exact (pow_apply_pos_iff_inducedSetoid hZ hZnn hZdiag (by omega) a a).2 .refl
    · intro a₁ a₂ hr
      rw [hsetL] at hr
      rw [hXXt]
      exact (pow_apply_pos_iff_inducedSetoid hZ hZnn hZdiag (by omega) a₁ a₂).2 hr
  have hsymR : (Xhatᵀ * Xhat).IsSymm := by
    have h := (mul_transpose_isSymm_nonneg_pos_diag (X := Xhatᵀ) (fun b a => hXhat_nn a b)
      hXhat_col).1
    rwa [Matrix.transpose_transpose] at h
  have hRnn : ∀ b₁ b₂, 0 ≤ (Xhatᵀ * Xhat) b₁ b₂ := fun b₁ b₂ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (hXhat_nn a b₁) (hXhat_nn a b₂)
  have hRpos_iff : ∀ b₁ b₂, 0 < (Xhatᵀ * Xhat) b₁ b₂ ↔ (inducedSetoid Z' hZ').r b₁ b₂ := by
    intro b₁ b₂
    constructor
    · intro hpos
      obtain ⟨a, -, ha⟩ := (Finset.sum_pos_iff_of_nonneg fun a _ =>
        mul_nonneg (hXhat_nn a b₁) (hXhat_nn a b₂)).1 hpos
      have ha1 : 0 < Xhat a b₁ := by
        by_contra hle; push Not at hle
        have h0 : Xhat a b₁ = 0 := le_antisymm hle (hXhat_nn a b₁)
        simp [h0] at ha
      have ha2 : 0 < Xhat a b₂ := by
        by_contra hle; push Not at hle
        have h0 : Xhat a b₂ = 0 := le_antisymm hle (hXhat_nn a b₂)
        simp [h0] at ha
      have hb1 := (hXhat_rel.mem_right_iff (Quotient.mk _ a) b₁).2 ⟨a, rfl, ha1⟩
      have hb2 := (hXhat_rel.mem_right_iff (Quotient.mk _ a) b₂).2 ⟨a, rfl, ha2⟩
      exact Quotient.exact (hb1.trans hb2.symm)
    · intro hr
      let q := e.symm (Quotient.mk (inducedSetoid Z' hZ') b₁)
      obtain ⟨a, ha⟩ := hrel.nonemptyLeft q
      have hb1 : Quotient.mk (inducedSetoid Z' hZ') b₁ = e q := by simp [q]
      have hb2 : Quotient.mk (inducedSetoid Z' hZ') b₂ = e q :=
        (Quotient.sound hr).symm.trans hb1
      exact (Finset.sum_pos_iff_of_nonneg fun c _ =>
        mul_nonneg (hXhat_nn c b₁) (hXhat_nn c b₂)).2
        ⟨a, Finset.mem_univ a, mul_pos (hpos_match q a b₁ ha hb1) (hpos_match q a b₂ ha hb2)⟩
  have hsetR : inducedSetoid (Xhatᵀ * Xhat) hsymR = inducedSetoid Z' hZ' := by
    ext b₁ b₂
    constructor
    · intro h
      induction h with
      | refl => exact .refl
      | @tail x y _ hxy ih =>
        exact ih.trans ((hRpos_iff x y).1 (lt_of_le_of_ne (hRnn x y) (Ne.symm hxy)))
    · intro h
      exact Relation.ReflTransGen.single (ne_of_gt ((hRpos_iff b₁ b₂).2 h))
  have hgoodR : IsGoodSymmMatrix (Xhatᵀ * Xhat) :=
    ⟨hsymR, hRnn, fun b => (hRpos_iff b b).2 .refl,
      fun b₁ b₂ hr => (hRpos_iff b₁ b₂).2 (hsetR ▸ hr)⟩
  have hbp : IsBlockPositiveMatrix Xhat := by
    let eL : Quotient (inducedSetoid (Xhat * Xhatᵀ) hsymL) ≃ Quotient (inducedSetoid Z hZ) :=
      Quotient.congrRight fun _ _ => by rw [hsetL]
    let eR : Quotient (inducedSetoid Z' hZ') ≃ Quotient (inducedSetoid (Xhatᵀ * Xhat) hsymR) :=
      Quotient.congrRight fun _ _ => by rw [hsetR]
    let e' := (eL.trans e).trans eR
    have heL_mk : ∀ a : V, eL (Quotient.mk _ a) = Quotient.mk (inducedSetoid Z hZ) a :=
      fun _ => rfl
    have heR_mk : ∀ b : W,
        eR (Quotient.mk (inducedSetoid Z' hZ') b) = Quotient.mk _ b :=
      fun _ => rfl
    refine ⟨hsymL, hsymR, e', ?_, ?_⟩
    · refine
        { nonneg := hXhat_nn
          noNullRows := hXhat_row
          noNullCols := hXhat_col
          nonemptyLeft := fun q => Quotient.inductionOn q fun a => ⟨a, rfl⟩
          disjointLeft := fun _ _ hne =>
            Set.disjoint_left.2 fun _ h1 h2 => hne (h1.symm.trans h2)
          coverLeft := fun a => ⟨Quotient.mk _ a, rfl⟩
          nonemptyRight := fun q => Quotient.inductionOn (e' q) fun b => ⟨b, rfl⟩
          disjointRight := fun _ _ hne =>
            Set.disjoint_left.2 fun _ h1 h2 => hne (e'.injective (h1.symm.trans h2))
          coverRight := fun b => ⟨e'.symm (Quotient.mk _ b), by simp⟩
          offDiagZero := fun q₁ q₂ hne a ha b hb => by
            have ha' : Quotient.mk (inducedSetoid Z hZ) a = eL q₁ := by
              rw [← heL_mk a, ha]
            have hb' : Quotient.mk (inducedSetoid Z' hZ') b = e (eL q₂) := by
              apply eR.injective
              rw [heR_mk b]
              exact hb
            exact hzero_off (eL q₁) (eL q₂) (fun h => hne (eL.injective h)) a b ha' hb' }
    · intro a b hab
      have hb' : Quotient.mk (inducedSetoid Z' hZ') b =
          e (Quotient.mk (inducedSetoid Z hZ) a) := by
        apply eR.injective
        rw [heR_mk b, ← heL_mk a]
        exact hab.symm
      exact hpos_match (Quotient.mk _ a) a b rfl hb'
  exact ⟨hcomm, ⟨hXhat_nn, hXhat_row, hXhat_col, hgoodL, hgoodR⟩, hbp,
    hZ, hZ', e, hXhat_rel, hpos_match, hzero_off⟩

end CslibFrontier.Foundations.LinearAlgebra.Matrix
