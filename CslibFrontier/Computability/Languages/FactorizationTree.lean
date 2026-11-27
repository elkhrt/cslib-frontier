module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG

/-!
# Factorization Trees, Group Factorization Forests, and Green's Relations

This module defines word evaluation in monoids, factorization trees and their validity, and
establishes the two foundational algebraic layers of Imre Simon's Factorization Forest Theorem:
finite-group factorization forests (height at most `4 * r`) and Green's relations, stability,
and Green's theorem in finite subsemigroups of a monoid.

## Main definitions

* `CslibFrontier.Computability.Languages.evalWord`: evaluation of a word `List α` in a monoid `M`
  under `f : α → M`.
* `CslibFrontier.Computability.Languages.FactorizationTree`: unlabelled factorization trees with
  leaves, binary nodes, and multi-way idempotent nodes.
* `CslibFrontier.Computability.Languages.FactorizationTree.IsWellFormed`: validity of a
  factorization tree under `f : α → M`, requiring every idempotent node to have at least two
  children all evaluating to the same idempotent element of `M`.
* `CslibFrontier.Computability.Languages.GreenRLe`,
  `CslibFrontier.Computability.Languages.GreenLLe`,
  `CslibFrontier.Computability.Languages.GreenJLe`,
  `CslibFrontier.Computability.Languages.GreenREq`,
  `CslibFrontier.Computability.Languages.GreenLEq`,
  `CslibFrontier.Computability.Languages.GreenHEq`,
  `CslibFrontier.Computability.Languages.GreenJEq`: Green's preorders and equivalence relations
  relative to a finite multiplicative subset `S ⊆ M`.
* `CslibFrontier.Computability.Languages.GreenHClass`: the `H`-class of an element `x₀` in a finite
  subsemigroup `S`.

## Main results

* `CslibFrontier.Computability.Languages.FactorizationTree.isWellFormed_subst_of_mul_map`: leaf
  substitution along any multiplicative map preserves factorization-tree validity.
* `CslibFrontier.Computability.Languages.exists_factorizationTree_group`: every nonempty word over
  a group `G` with at most `r` distinct prefix products admits a valid factorization tree of
  height `≤ 4 * r`.
* `CslibFrontier.Computability.Languages.greenREq_of_rLe_of_jEq` and
  `CslibFrontier.Computability.Languages.greenLEq_of_lLe_of_jEq`: finite-semigroup stability for
  Green's `R`- and `L`-relations.
* `CslibFrontier.Computability.Languages.exists_greenHClass_group_ops`: Green's Theorem — an
  `H`-class containing `x₀, y₀` with `x₀ * y₀` in the same `J`-class forms a group under the
  ambient monoid multiplication.
-/

public section

namespace CslibFrontier.Computability.Languages

universe u v

/-- Evaluate a word `w : List α` in a monoid `M` using letter map `f : α → M`. -/
def evalWord {α : Type u} {M : Type v} [Monoid M] (f : α → M) (w : List α) : M :=
  (w.map f).prod

/-- Evaluating the empty word yields `1`. -/
@[simp]
theorem evalWord_nil {α : Type u} {M : Type v} [Monoid M] (f : α → M) :
    evalWord f [] = 1 := by
  simp [evalWord]

/-- Evaluating a singleton word `[a]` yields `f a`. -/
theorem evalWord_singleton {α : Type u} {M : Type v} [Monoid M] (f : α → M) (a : α) :
    evalWord f [a] = f a := by
  simp [evalWord]

/-- Evaluating `a :: w` multiplies `f a` with the evaluation of `w`. -/
@[simp]
theorem evalWord_cons {α : Type u} {M : Type v} [Monoid M] (f : α → M) (a : α) (w : List α) :
    evalWord f (a :: w) = f a * evalWord f w := by
  simp [evalWord]

/-- Evaluating `u ++ v` multiplies the evaluations of `u` and `v`. -/
@[simp]
theorem evalWord_append {α : Type u} {M : Type v} [Monoid M] (f : α → M) (u v : List α) :
    evalWord f (u ++ v) = evalWord f u * evalWord f v := by
  simp [evalWord]

/-- Evaluating a flattened list of words equals the product of their evaluations. -/
theorem evalWord_flatten {α : Type u} {M : Type v} [Monoid M] (f : α → M) (ws : List (List α)) :
    evalWord f ws.flatten = (ws.map (evalWord f)).prod := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [ih]

/-- Flattening a nonempty list of words that all evaluate to an idempotent `e` evaluates to `e`. -/
theorem evalWord_eq_of_forall_eq {α : Type u} {M : Type v} [Monoid M] (f : α → M)
    {ws : List (List α)} {e : M} (he : e * e = e) (hpos : 1 ≤ ws.length)
    (hall : ∀ w ∈ ws, evalWord f w = e) :
    evalWord f ws.flatten = e := by
  induction ws with
  | nil => simp at hpos
  | cons w ws ih =>
    cases ws with
    | nil =>
      simpa using hall w (by simp)
    | cons w' ws' =>
      have hw : evalWord f w = e := hall w (by simp)
      have htail : evalWord f (w' :: ws').flatten = e :=
        ih (by simp) (fun u hu ↦ hall u (List.mem_cons_of_mem _ hu))
      rw [List.flatten_cons, evalWord_append, hw, htail, he]

/-- A factorization tree over an alphabet `α`, with leaves, binary products, and multi-way
idempotent nodes. -/
inductive FactorizationTree (α : Type u) : Type u
  /-- A single-letter leaf. -/
  | leaf (a : α) : FactorizationTree α
  /-- A binary product of two factorization trees. -/
  | bin (t₁ t₂ : FactorizationTree α) : FactorizationTree α
  /-- A multi-way idempotent product of a list of factorization trees. -/
  | idem (ts : List (FactorizationTree α)) : FactorizationTree α

namespace FactorizationTree

/-- The word yielded by reading the leaves of a factorization tree from left to right. -/
def word {α : Type u} : FactorizationTree α → List α
  | .leaf a => [a]
  | .bin t₁ t₂ => t₁.word ++ t₂.word
  | .idem ts => (ts.map word).flatten

/-- The height of a factorization tree (`0` for leaves). -/
def height {α : Type u} : FactorizationTree α → ℕ
  | .leaf _ => 0
  | .bin t₁ t₂ => max t₁.height t₂.height + 1
  | .idem ts => (ts.map height).foldr max 0 + 1

/-- Validity of a factorization tree with respect to `f : α → M`: every idempotent node has at
least two children, all evaluating to the same idempotent element `e ∈ M`. -/
def IsWellFormed {α : Type u} {M : Type v} [Monoid M] (f : α → M) : FactorizationTree α → Prop
  | .leaf _ => True
  | .bin t₁ t₂ => IsWellFormed f t₁ ∧ IsWellFormed f t₂
  | .idem ts =>
      2 ≤ ts.length ∧ (∀ t ∈ ts, IsWellFormed f t) ∧
        ∃ e : M, e * e = e ∧ ∀ t ∈ ts, evalWord f t.word = e

/-- Substitute a factorization tree `g a` for every leaf `a` of a factorization tree `t`. -/
def subst {α : Type u} {β : Type v} (g : α → FactorizationTree β) :
    FactorizationTree α → FactorizationTree β
  | .leaf a => g a
  | .bin t₁ t₂ => .bin (subst g t₁) (subst g t₂)
  | .idem ts => .idem (ts.map (subst g))

/-- The yield of a leaf is the singleton word. -/
@[simp]
theorem word_leaf {α : Type u} (a : α) : (leaf a).word = [a] := by
  simp [word]

/-- The yield of a binary node is the concatenation of its children's yields. -/
@[simp]
theorem word_bin {α : Type u} (t₁ t₂ : FactorizationTree α) :
    (bin t₁ t₂).word = t₁.word ++ t₂.word := by
  simp [word]

/-- The yield of an idempotent node is the flattened yields of its children. -/
@[simp]
theorem word_idem {α : Type u} (ts : List (FactorizationTree α)) :
    (idem ts).word = (ts.map word).flatten := by
  simp [word]

/-- The height of a leaf is `0`. -/
@[simp]
theorem height_leaf {α : Type u} (a : α) : (leaf a).height = 0 := by
  simp [height]

/-- The height of a binary node is `max t₁.height t₂.height + 1`. -/
@[simp]
theorem height_bin {α : Type u} (t₁ t₂ : FactorizationTree α) :
    (bin t₁ t₂).height = max t₁.height t₂.height + 1 := by
  simp [height]

/-- The height of an idempotent node is one plus the maximum height of its children. -/
@[simp]
theorem height_idem {α : Type u} (ts : List (FactorizationTree α)) :
    (idem ts).height = (ts.map height).foldr max 0 + 1 := by
  simp [height]

/-- Every leaf is valid. -/
@[simp]
theorem isWellFormed_leaf {α : Type u} {M : Type v} [Monoid M] (f : α → M) (a : α) :
    (leaf a).IsWellFormed f := by
  simp [IsWellFormed]

/-- Characterization of validity for a binary node. -/
theorem isWellFormed_bin_iff {α : Type u} {M : Type v} [Monoid M] {f : α → M}
    {t₁ t₂ : FactorizationTree α} :
    (bin t₁ t₂).IsWellFormed f ↔ t₁.IsWellFormed f ∧ t₂.IsWellFormed f := by
  simp [IsWellFormed]

/-- Characterization of validity for an idempotent node. -/
theorem isWellFormed_idem_iff {α : Type u} {M : Type v} [Monoid M] {f : α → M}
    {ts : List (FactorizationTree α)} :
    (idem ts).IsWellFormed f ↔
      2 ≤ ts.length ∧ (∀ t ∈ ts, t.IsWellFormed f) ∧
        ∃ e : M, e * e = e ∧ ∀ t ∈ ts, evalWord f t.word = e := by
  simp [IsWellFormed]

/-- Substituting into a leaf returns the substituted tree. -/
@[simp]
theorem subst_leaf {α : Type u} {β : Type v} (g : α → FactorizationTree β) (a : α) :
    (leaf a).subst g = g a := by
  simp [subst]

/-- Substituting into a binary node recurses into both children. -/
@[simp]
theorem subst_bin {α : Type u} {β : Type v} (g : α → FactorizationTree β)
    (t₁ t₂ : FactorizationTree α) :
    (bin t₁ t₂).subst g = bin (t₁.subst g) (t₂.subst g) := by
  simp [subst]

/-- Substituting into an idempotent node maps over the child list. -/
@[simp]
theorem subst_idem {α : Type u} {β : Type v} (g : α → FactorizationTree β)
    (ts : List (FactorizationTree α)) :
    (idem ts).subst g = idem (ts.map (subst g)) := by
  simp [subst]

private theorem foldr_max_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) :
    l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact max_le (h x (by simp)) (ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)))

private theorem le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_max_left _ _
    · exact le_trans (ih hmem) (le_max_right _ _)

/-- Every child of an idempotent node has height strictly smaller than the node's height. -/
theorem height_lt_of_mem_idem {α : Type u} {ts : List (FactorizationTree α)}
    {t : FactorizationTree α} (ht : t ∈ ts) :
    t.height < (idem ts).height := by
  have hle : t.height ≤ (ts.map height).foldr max 0 :=
    le_foldr_max (List.mem_map.mpr ⟨t, ht, rfl⟩)
  rw [height_idem]
  omega

/-- Every valid factorization tree yields a nonempty word. -/
theorem word_ne_nil_of_isWellFormed {α : Type u} {M : Type v} [Monoid M] {f : α → M}
    {t : FactorizationTree α} (ht : t.IsWellFormed f) : t.word ≠ [] := by
  match t with
  | .leaf a => simp
  | .bin t₁ t₂ =>
    rw [isWellFormed_bin_iff] at ht
    simp [word_ne_nil_of_isWellFormed ht.1]
  | .idem ts =>
    rw [isWellFormed_idem_iff] at ht
    rcases ht with ⟨hlen, hval, _⟩
    cases ts with
    | nil => simp at hlen
    | cons t₁ ts' =>
      have h1 : t₁.word ≠ [] := word_ne_nil_of_isWellFormed (hval t₁ (by simp))
      simp [h1]

/-- The yield of a substituted tree is the flattened yields of the substituted leaves. -/
theorem word_subst {α : Type u} {β : Type v} (g : α → FactorizationTree β)
    (t : FactorizationTree α) :
    (t.subst g).word = (t.word.map (fun a ↦ (g a).word)).flatten := by
  match t with
  | .leaf a => simp
  | .bin t₁ t₂ => simp [word_subst g t₁, word_subst g t₂]
  | .idem ts =>
    simp only [subst_idem, word_idem, List.map_map]
    have haux : ∀ (l : List (FactorizationTree α)),
        (∀ t₁ ∈ l, (t₁.subst g).word = (t₁.word.map (fun a ↦ (g a).word)).flatten) →
        (l.map (fun t₁ ↦ (t₁.subst g).word)).flatten =
          ((l.map word).flatten.map (fun a ↦ (g a).word)).flatten := by
      intro l hl
      induction l with
      | nil => simp
      | cons t₁ ts' ih_ts =>
        simp only [List.map_cons, List.flatten_cons, List.map_append, List.flatten_append]
        rw [hl t₁ (by simp), ih_ts (fun t ht ↦ hl t (List.mem_cons_of_mem _ ht))]
    exact haux ts (fun t₁ _ ↦ word_subst g t₁)

/-- Leaf substitution increases tree height by at most the maximum height of the substituted
trees. -/
theorem height_subst_le {α : Type u} {β : Type v} (g : α → FactorizationTree β)
    (t : FactorizationTree α) {B : ℕ} (hg : ∀ a ∈ t.word, (g a).height ≤ B) :
    (t.subst g).height ≤ t.height + B := by
  match t with
  | .leaf a =>
    simpa using hg a (by simp)
  | .bin t₁ t₂ =>
    simp only [subst_bin, height_bin]
    have h1 := height_subst_le g t₁ (fun a ha ↦ hg a (by simp [ha]))
    have h2 := height_subst_le g t₂ (fun a ha ↦ hg a (by simp [ha]))
    omega
  | .idem ts =>
    simp only [subst_idem, height_idem, List.map_map]
    have hfold : (ts.map (fun t₁ ↦ (t₁.subst g).height)).foldr max 0 ≤
        (ts.map height).foldr max 0 + B := by
      refine foldr_max_le ?_
      intro x hx
      rcases List.mem_map.mp hx with ⟨t₁, ht₁, rfl⟩
      have hstep := height_subst_le g t₁ (fun a ha ↦ hg a (by
        simp only [word_idem, List.mem_flatten, List.mem_map]
        exact ⟨t₁.word, ⟨t₁, ht₁, rfl⟩, ha⟩))
      have hle : t₁.height ≤ (ts.map height).foldr max 0 :=
        le_foldr_max (List.mem_map.mpr ⟨t₁, ht₁, rfl⟩)
      omega
    have hfold' : (ts.map (height ∘ subst g)).foldr max 0 ≤
        (ts.map height).foldr max 0 + B := hfold
    omega

private theorem evalWord_flatten_map_of_mul_map {α : Type u} {β : Type v} {M₁ M₂ : Type*}
    [Monoid M₁] [Monoid M₂] {f₁ : α → M₁} {f₂ : β → M₂} (φ : M₁ → M₂)
    (hφ_mul : ∀ x y, φ (x * y) = φ x * φ y) (g : α → List β)
    {w : List α} (hw : w ≠ []) (hg : ∀ a ∈ w, evalWord f₂ (g a) = φ (f₁ a)) :
    evalWord f₂ (w.map g).flatten = φ (evalWord f₁ w) := by
  induction w with
  | nil => contradiction
  | cons a ws ih =>
    cases ws with
    | nil =>
      simpa using hg a (by simp)
    | cons b bs =>
      have ha : evalWord f₂ (g a) = φ (f₁ a) := hg a (by simp)
      have htail : evalWord f₂ ((b :: bs).map g).flatten = φ (evalWord f₁ (b :: bs)) :=
        ih (by simp) (fun x hx ↦ hg x (List.mem_cons_of_mem _ hx))
      rw [List.map_cons, List.flatten_cons, evalWord_append, ha, htail, ← hφ_mul, ← evalWord_cons]

/-- Validity is preserved under leaf substitution whenever the substituted trees evaluate along a
multiplicative map `φ : M₁ → M₂` (which need not preserve `1`). -/
theorem isWellFormed_subst_of_mul_map {α : Type u} {β : Type v} {M₁ M₂ : Type*}
    [Monoid M₁] [Monoid M₂] {f₁ : α → M₁} {f₂ : β → M₂} (φ : M₁ → M₂)
    (hφ_mul : ∀ x y, φ (x * y) = φ x * φ y)
    (g : α → FactorizationTree β) {t : FactorizationTree α} (ht : t.IsWellFormed f₁)
    (hg : ∀ a ∈ t.word, (g a).IsWellFormed f₂ ∧ evalWord f₂ (g a).word = φ (f₁ a)) :
    (t.subst g).IsWellFormed f₂ := by
  match t with
  | .leaf a => simpa using (hg a (by simp)).1
  | .bin t₁ t₂ =>
    rw [isWellFormed_bin_iff] at ht
    rw [subst_bin, isWellFormed_bin_iff]
    exact ⟨isWellFormed_subst_of_mul_map φ hφ_mul g ht.1 (fun a ha ↦ hg a (by simp [ha])),
      isWellFormed_subst_of_mul_map φ hφ_mul g ht.2 (fun a ha ↦ hg a (by simp [ha]))⟩
  | .idem ts =>
    rw [isWellFormed_idem_iff] at ht
    rcases ht with ⟨hlen, hval, e, he, heval⟩
    have hmem : ∀ t₁ ∈ ts, ∀ a ∈ t₁.word, a ∈ (idem ts).word := by
      intro t₁ ht₁ a ha
      simp only [word_idem, List.mem_flatten, List.mem_map]
      exact ⟨t₁.word, ⟨t₁, ht₁, rfl⟩, ha⟩
    rw [subst_idem, isWellFormed_idem_iff]
    refine ⟨by simpa using hlen, ?_, φ e, by rw [← hφ_mul, he], ?_⟩
    · intro x hx
      rcases List.mem_map.mp hx with ⟨t₁, ht₁, rfl⟩
      exact isWellFormed_subst_of_mul_map φ hφ_mul g (hval t₁ ht₁)
        (fun a ha ↦ hg a (hmem t₁ ht₁ a ha))
    · intro x hx
      rcases List.mem_map.mp hx with ⟨t₁, ht₁, rfl⟩
      rw [word_subst,
        evalWord_flatten_map_of_mul_map φ hφ_mul (fun a ↦ (g a).word)
          (word_ne_nil_of_isWellFormed (hval t₁ ht₁))
          (fun a ha ↦ (hg a (hmem t₁ ht₁ a ha)).2),
        heval t₁ ht₁]

/-- Validity is preserved under leaf substitution when each substituted tree evaluates to the
replaced letter's value in the same monoid `M`. -/
theorem isWellFormed_subst_of_eval_eq {α : Type u} {β : Type v} {M : Type*} [Monoid M]
    {f : α → M} {f' : β → M} (g : α → FactorizationTree β)
    {t : FactorizationTree α} (ht : t.IsWellFormed f)
    (hg : ∀ a ∈ t.word, (g a).IsWellFormed f' ∧ evalWord f' (g a).word = f a) :
    (t.subst g).IsWellFormed f' :=
  isWellFormed_subst_of_mul_map id (fun _ _ ↦ rfl) g ht hg

end FactorizationTree

/-! ### Stage 1: Finite Groups -/

section GroupStage

/-- The finite set of prefix evaluations of a word `w` in a group `G`. -/
def groupPrefixes {α G : Type*} [Group G] [DecidableEq G] (f : α → G) (w : List α) :
    Finset G :=
  (Finset.range (w.length + 1)).image (fun i ↦ evalWord f (w.take i))

/-- Membership characterization for `groupPrefixes`. -/
theorem mem_groupPrefixes_iff {α G : Type*} [Group G] [DecidableEq G] (f : α → G) (w : List α)
    (x : G) : x ∈ groupPrefixes f w ↔ ∃ i ≤ w.length, evalWord f (w.take i) = x := by
  simp only [groupPrefixes, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

private lemma one_mem_groupPrefixes {α G : Type*} [Group G] [DecidableEq G]
    (f : α → G) (w : List α) : (1 : G) ∈ groupPrefixes f w := by
  simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by omega, by simp⟩

private lemma groupPrefixes_card_pos {α G : Type*} [Group G] [DecidableEq G]
    (f : α → G) (w : List α) : 1 ≤ (groupPrefixes f w).card :=
  Finset.one_le_card.mpr ⟨1, one_mem_groupPrefixes f w⟩

private lemma group_split_first_one {α G : Type*} [Group G] (f : α → G) :
    ∀ (w : List α), w ≠ [] → evalWord f w = 1 →
      ∃ us : List (List α),
        us.flatten = w ∧
        (∀ u ∈ us, u ≠ [] ∧ evalWord f u = 1 ∧
          ∀ i, 0 < i → i < u.length → evalWord f (u.take i) ≠ 1) := by
  intro w
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    intro hw hval
    classical
    by_cases hex : ∃ i, 0 < i ∧ i < w.length ∧ evalWord f (w.take i) = 1
    · let k := Nat.find hex
      have hk_spec : 0 < k ∧ k < w.length ∧ evalWord f (w.take k) = 1 := Nat.find_spec hex
      rcases hk_spec with ⟨hk1, hk2, hk3⟩
      have hk_min : ∀ i, 0 < i → i < k → evalWord f (w.take i) ≠ 1 := by
        intro i hi1 hi2 heq
        exact Nat.find_min hex hi2 ⟨hi1, by omega, heq⟩
      let u := w.take k
      let v := w.drop k
      have hu_ne : u ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [List.length_take, Nat.min_eq_left (by omega)] at this
        simp at this
        omega
      have hv_ne : v ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [v] at this
        omega
      have hv_val : evalWord f v = 1 := by
        have hcat := congrArg (evalWord f) (List.take_append_drop k w)
        rw [evalWord_append, hk3, one_mul] at hcat
        exact hcat.trans hval
      have hv_len : v.length < n := by
        simp [v, ← hlen]
        omega
      obtain ⟨us, hus_flat, hus_prop⟩ := ih v.length hv_len v rfl hv_ne hv_val
      refine ⟨u :: us, ?_, ?_⟩
      · simp [hus_flat, u, v]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · refine ⟨hu_ne, hk3, ?_⟩
          intro i hi1 hi2
          have hlen_u : u.length = k := by simp [u]; omega
          rw [hlen_u] at hi2
          rw [List.take_take, Nat.min_eq_left (by omega)]
          exact hk_min i hi1 hi2
        · exact hus_prop x hx'
    · refine ⟨[w], by simp, ?_⟩
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      refine ⟨hw, hval, ?_⟩
      intro i hi1 hi2 heq
      exact hex ⟨i, hi1, hi2, heq⟩

private lemma group_tree_of_no_one_prefix {α G : Type*} [Group G] [DecidableEq G]
    (f : α → G) {w : List α} (hw : w ≠ [])
    (hno : ∀ i, 0 < i → i < w.length + 1 → evalWord f (w.take i) ≠ 1)
    {r : ℕ} (hr : (groupPrefixes f w).card ≤ r)
    (ih : ∀ u : List α, u ≠ [] → (groupPrefixes f u).card ≤ r - 1 →
      ∃ t : FactorizationTree α, t.IsWellFormed f ∧ t.word = u ∧ t.height ≤ 4 * (r - 1)) :
    ∃ t : FactorizationTree α, t.IsWellFormed f ∧ t.word = w ∧ t.height ≤ 4 * (r - 1) + 1 := by
  cases w with
  | nil => contradiction
  | cons a w' =>
    cases w' with
    | nil =>
      exact ⟨.leaf a, FactorizationTree.isWellFormed_leaf f a,
        FactorizationTree.word_leaf a, by simp⟩
    | cons b bs =>
      let w' := b :: bs
      have hw'_ne : w' ≠ [] := by simp [w']
      have hsub : (groupPrefixes f w').image (fun x ↦ f a * x) ⊆
          (groupPrefixes f (a :: w')).erase 1 := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · have heq : f a * evalWord f (w'.take j) = evalWord f ((a :: w').take (j + 1)) := by
            simp [List.take_succ_cons]
          rw [heq]
          exact hno (j + 1) (by omega) (by simp; omega)
        · simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
          exact ⟨j + 1, by simp [w']; omega, by simp [List.take_succ_cons]⟩
      have hcard' : (groupPrefixes f w').card ≤ r - 1 := by
        have h1 : (groupPrefixes f w').card =
            ((groupPrefixes f w').image (fun x ↦ f a * x)).card :=
          (Finset.card_image_of_injective _ (mul_right_injective (f a))).symm
        have h2 := Finset.card_le_card hsub
        have h3 : ((groupPrefixes f (a :: w')).erase 1).card =
            (groupPrefixes f (a :: w')).card - 1 :=
          Finset.card_erase_of_mem (one_mem_groupPrefixes f (a :: w'))
        have h4 : (groupPrefixes f (a :: w')).card ≤ r := hr
        have h5 := groupPrefixes_card_pos f (a :: w')
        omega
      obtain ⟨t', ht'v, ht'w, ht'h⟩ := ih w' hw'_ne hcard'
      exact ⟨.bin (.leaf a) t',
        FactorizationTree.isWellFormed_bin_iff.mpr ⟨FactorizationTree.isWellFormed_leaf f a, ht'v⟩,
        by simp [ht'w, w'], by simp; omega⟩

/-- **Group Factorization Forest Theorem**: any nonempty word `w` over a group `G` whose prefix
products take at most `r` distinct values admits a valid factorization tree of height at most
`4 * r`. -/
theorem exists_factorizationTree_group {α G : Type*} [Group G] [DecidableEq G]
    (f : α → G) :
    ∀ (r : ℕ) (w : List α), w ≠ [] → (groupPrefixes f w).card ≤ r →
      ∃ t : FactorizationTree α, t.IsWellFormed f ∧ t.word = w ∧ t.height ≤ 4 * r := by
  intro r
  induction r with
  | zero =>
    intro w _ hr
    have := groupPrefixes_card_pos f w
    omega
  | succ r ih =>
    intro w hw hr
    by_cases hbase : r = 0
    · subst hbase
      have hall1 : ∀ i, i < w.length + 1 → evalWord f (w.take i) = 1 := by
        intro i hi
        have hmem : evalWord f (w.take i) ∈ groupPrefixes f w := by
          simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
          exact ⟨i, hi, rfl⟩
        have hcard1 : (groupPrefixes f w).card = 1 := by
          have := groupPrefixes_card_pos f w; omega
        have heq_s : groupPrefixes f w = {1} :=
          Finset.eq_singleton_iff_unique_mem.mpr
            ⟨one_mem_groupPrefixes f w, fun x hx ↦ by
              have hcard_le := Finset.card_le_card
                (Finset.insert_subset_iff.mpr ⟨hx,
                  Finset.singleton_subset_iff.mpr (one_mem_groupPrefixes f w)⟩)
              by_contra hne
              rw [Finset.card_pair hne] at hcard_le
              omega⟩
        rw [heq_s, Finset.mem_singleton] at hmem
        exact hmem
      have hletters : ∀ a ∈ w, f a = 1 := by
        intro a ha
        rcases List.mem_iff_getElem.mp ha with ⟨i, hi, rfl⟩
        have h1 := hall1 i (by omega)
        have h2 := hall1 (i + 1) (by omega)
        have htake : w.take (i + 1) = w.take i ++ [w[i]'hi] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
        rw [htake, evalWord_append, h1, one_mul, evalWord_singleton] at h2
        exact h2
      cases w with
      | nil => contradiction
      | cons a w' =>
        cases w' with
        | nil =>
          exact ⟨.leaf a, FactorizationTree.isWellFormed_leaf f a, FactorizationTree.word_leaf a,
            by simp⟩
        | cons b bs =>
          refine ⟨.idem ((a :: b :: bs).map .leaf), ?_, ?_, ?_⟩
          · rw [FactorizationTree.isWellFormed_idem_iff]
            refine ⟨by simp, by intro t ht; rcases List.mem_map.mp ht with ⟨x, _, rfl⟩; simp,
              1, mul_one 1, ?_⟩
            intro t ht
            rcases List.mem_map.mp ht with ⟨x, hx, rfl⟩
            simpa using hletters x hx
          · simp only [FactorizationTree.word_idem, List.map_map, Function.comp_def,
              FactorizationTree.word_leaf]
            have hflat_s : ∀ l : List α, (l.map (fun x ↦ [x])).flatten = l := by
              intro l; induction l with | nil => rfl | cons x xs ih => simp [ih]
            exact hflat_s (a :: b :: bs)
          · simp only [FactorizationTree.height_idem, List.map_map]
            have h0 : ((a :: b :: bs).map (fun x ↦ (FactorizationTree.leaf x).height)).foldr
                max 0 ≤ 0 :=
              FactorizationTree.foldr_max_le (by
                intro x hx; rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; simp)
            have h0' : (List.map (FactorizationTree.height ∘ FactorizationTree.leaf)
                (a :: b :: bs)).foldr max 0 ≤ 0 := h0
            omega
    · have hmin_piece : ∀ u : List α, u ≠ [] → evalWord f u = 1 →
          (∀ i, 0 < i → i < u.length → evalWord f (u.take i) ≠ 1) →
          (groupPrefixes f u).card ≤ r + 1 →
          ∃ t : FactorizationTree α, t.IsWellFormed f ∧ t.word = u ∧ t.height ≤ 4 * r + 2 := by
        intro u hu hu_val hu_min hu_card
        by_cases hlen : u.length ≤ 2
        · cases u with
          | nil => contradiction
          | cons a u' =>
            cases u' with
            | nil =>
              exact ⟨.leaf a, FactorizationTree.isWellFormed_leaf f a,
                FactorizationTree.word_leaf a, by simp⟩
            | cons b u'' =>
              cases u'' with
              | nil =>
                exact ⟨.bin (.leaf a) (.leaf b),
                  FactorizationTree.isWellFormed_bin_iff.mpr
                    ⟨FactorizationTree.isWellFormed_leaf f a,
                      FactorizationTree.isWellFormed_leaf f b⟩,
                  by simp, by simp⟩
              | cons _ _ => simp at hlen
        · have hlen3 : 3 ≤ u.length := by omega
          cases u with
          | nil => contradiction
          | cons a u_tail =>
            have htail_ne : u_tail ≠ [] := by
              intro h; simp [h] at hlen3
            let b := u_tail.getLast htail_ne
            let u'' := u_tail.dropLast
            have hu_eq : a :: u_tail = a :: (u'' ++ [b]) := by
              simp [u'', b, List.dropLast_append_getLast htail_ne]
            have hu''_ne : u'' ≠ [] := by
              intro h
              have hlen_tail : u_tail.length = 1 := by
                have := congrArg List.length (List.dropLast_append_getLast htail_ne)
                simp [u'', h] at this
                omega
              simp [hlen_tail] at hlen3
            have hsub : (groupPrefixes f u'').image (fun x ↦ f a * x) ⊆
                (groupPrefixes f (a :: u_tail)).erase 1 := by
              intro y hy
              rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
              rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
              rw [Finset.mem_range] at hj
              have hlen_u'' : u''.length = u_tail.length - 1 := List.length_dropLast
              have htail_len : 2 ≤ u_tail.length := by simp at hlen3; omega
              have hj_lt : j + 1 < (a :: u_tail).length := by
                simp only [List.length_cons]; omega
              have heq_take : u''.take j = u_tail.take j := by
                have h1 := List.dropLast_append_getLast htail_ne
                calc u''.take j = (u'' ++ [b]).take j := by
                      rw [List.take_append_of_le_length (by omega)]
                  _ = u_tail.take j := by rw [h1]
              have heq : f a * evalWord f (u''.take j) =
                  evalWord f ((a :: u_tail).take (j + 1)) := by
                rw [heq_take]; simp [List.take_succ_cons]
              rw [Finset.mem_erase]
              refine ⟨?_, ?_⟩
              · rw [heq]
                exact hu_min (j + 1) (by omega) hj_lt
              · simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
                exact ⟨j + 1, by omega, heq.symm⟩
            have hcard'' : (groupPrefixes f u'').card ≤ r := by
              have h1 : (groupPrefixes f u'').card =
                  ((groupPrefixes f u'').image (fun x ↦ f a * x)).card :=
                (Finset.card_image_of_injective _ (mul_right_injective (f a))).symm
              have h2 := Finset.card_le_card hsub
              have h3 : ((groupPrefixes f (a :: u_tail)).erase 1).card =
                  (groupPrefixes f (a :: u_tail)).card - 1 :=
                Finset.card_erase_of_mem (one_mem_groupPrefixes f (a :: u_tail))
              omega
            obtain ⟨t'', ht''v, ht''w, ht''h⟩ := ih u'' hu''_ne hcard''
            refine ⟨.bin (.leaf a) (.bin t'' (.leaf b)),
              FactorizationTree.isWellFormed_bin_iff.mpr
                ⟨FactorizationTree.isWellFormed_leaf f a,
                  FactorizationTree.isWellFormed_bin_iff.mpr
                    ⟨ht''v, FactorizationTree.isWellFormed_leaf f b⟩⟩, ?_, ?_⟩
            · simp [ht''w, hu_eq]
            · simp; omega
      classical
      by_cases hex : ∃ i, 0 < i ∧ i < w.length + 1 ∧ evalWord f (w.take i) = 1
      · let idxs := (Finset.range (w.length + 1)).filter
          (fun i ↦ 0 < i ∧ evalWord f (w.take i) = 1)
        have hidxs_ne : idxs.Nonempty := by
          rcases hex with ⟨i, hi1, hi2, hi3⟩
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi2, hi1, hi3⟩⟩
        let k := idxs.max' hidxs_ne
        have hk_mem := Finset.mem_filter.mp (Finset.max'_mem idxs hidxs_ne)
        have hk_pos : 0 < k := hk_mem.2.1
        have hk_le : k ≤ w.length := by
          have := Finset.mem_range.mp hk_mem.1; omega
        have hk_val : evalWord f (w.take k) = 1 := hk_mem.2.2
        have hk_max : ∀ i, k < i → i < w.length + 1 → evalWord f (w.take i) ≠ 1 := by
          intro i hi1 hi2 heq
          have hmem : i ∈ idxs := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi2, by omega, heq⟩
          have hle := Finset.le_max' idxs i hmem
          omega
        let w_pre := w.take k
        let w_suf := w.drop k
        have hw_pre_ne : w_pre ≠ [] := by
          intro h
          have := congrArg List.length h
          rw [List.length_take, Nat.min_eq_left hk_le] at this
          simp at this
          omega
        have hpref_pre : groupPrefixes f w_pre ⊆ groupPrefixes f w := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
          rw [Finset.mem_range] at hi
          simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
          have hlen_pre : w_pre.length = k := by simp [w_pre]; omega
          refine ⟨min i k, by omega, ?_⟩
          simp [w_pre, List.take_take]
        obtain ⟨us, hus_flat, hus_prop⟩ := group_split_first_one f w_pre hw_pre_ne hk_val
        have hus_trees : ∀ u ∈ us,
            ∃ t : FactorizationTree α, t.IsWellFormed f ∧ t.word = u ∧ t.height ≤ 4 * r + 2 := by
          intro u hu
          have hpref_u : groupPrefixes f u ⊆ groupPrefixes f w_pre := by
            have hdecomp : ∃ a b : List α, a ++ u ++ b = w_pre ∧ evalWord f a = 1 := by
              rcases List.append_of_mem hu with ⟨l₁, l₂, rfl⟩
              refine ⟨l₁.flatten, l₂.flatten, by simpa [List.append_assoc] using hus_flat, ?_⟩
              rw [evalWord_flatten]
              have hprod1 : ∀ (l : List (List α)), (∀ x ∈ l, evalWord f x = 1) →
                  (l.map (evalWord f)).prod = 1 := by
                intro l hl
                induction l with
                | nil => simp
                | cons x xs ihx =>
                  simp [hl x (by simp), ihx (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy))]
              exact hprod1 l₁ (fun x hx ↦ (hus_prop x (by simp [hx])).2.1)
            rcases hdecomp with ⟨a, b, hab, ha_val⟩
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
            rw [Finset.mem_range] at hi
            simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
            refine ⟨a.length + i, ?_, ?_⟩
            · have := congrArg List.length hab
              simp at this; omega
            · rw [← hab]
              have htake : (a ++ u ++ b).take (a.length + i) = a ++ u.take i := by
                rw [List.take_append_of_le_length (by simp; omega), List.take_add]
                simp
              rw [htake, evalWord_append, ha_val, one_mul]
          have hcard_u : (groupPrefixes f u).card ≤ r + 1 :=
            le_trans (Finset.card_le_card (hpref_u.trans hpref_pre)) hr
          rcases hus_prop u hu with ⟨hu_ne, hu_val, hu_min⟩
          exact hmin_piece u hu_ne hu_val hu_min hcard_u
        have hpre_tree : ∃ t_pre : FactorizationTree α,
            t_pre.IsWellFormed f ∧ t_pre.word = w_pre ∧ t_pre.height ≤ 4 * r + 3 := by
          choose F hF using hus_trees
          let ts : List (FactorizationTree α) := us.pmap F (fun u hu ↦ hu)
          have hts_word : (ts.map FactorizationTree.word).flatten = w_pre := by
            have hmap : ts.map FactorizationTree.word = us := by
              simp only [ts, List.map_pmap]
              have : ∀ (l : List (List α)) (hl : ∀ u ∈ l, u ∈ us),
                  l.pmap (fun u hu ↦ (F u hu).word) hl = l := by
                intro l hl
                induction l with
                | nil => rfl
                | cons u l' ihl =>
                  simp [(hF u (hl u (by simp))).2.1,
                    ihl (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx))]
              exact this us (fun _ h ↦ h)
            rw [hmap, hus_flat]
          cases hts : ts with
          | nil =>
            have : w_pre = [] := by rw [← hts_word, hts]; simp
            contradiction
          | cons t₁ ts' =>
            cases ts' with
            | nil =>
              have ht₁_mem : t₁ ∈ ts := by rw [hts]; simp
              rcases List.mem_pmap.mp ht₁_mem with ⟨u, hu, rfl⟩
              have hw1 : (F u hu).word = w_pre := by
                have := hts_word; rw [hts] at this; simpa using this
              exact ⟨F u hu, (hF u hu).1, hw1, by have := (hF u hu).2.2; omega⟩
            | cons t₂ ts'' =>
              refine ⟨.idem (t₁ :: t₂ :: ts''), ?_,
                by rw [FactorizationTree.word_idem, ← hts, hts_word], ?_⟩
              · rw [FactorizationTree.isWellFormed_idem_iff]
                refine ⟨by simp, ?_, 1, mul_one 1, ?_⟩
                · intro t ht
                  rw [← hts] at ht
                  rcases List.mem_pmap.mp ht with ⟨u, hu, rfl⟩
                  exact (hF u hu).1
                · intro t ht
                  rw [← hts] at ht
                  rcases List.mem_pmap.mp ht with ⟨u, hu, rfl⟩
                  rw [(hF u hu).2.1]
                  exact (hus_prop u hu).2.1
              · simp only [FactorizationTree.height_idem]
                have hfold : ((t₁ :: t₂ :: ts'').map FactorizationTree.height).foldr max 0 ≤
                    4 * r + 2 := by
                  refine FactorizationTree.foldr_max_le ?_
                  intro x hx
                  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
                  rw [← hts] at ht
                  rcases List.mem_pmap.mp ht with ⟨u, hu, rfl⟩
                  exact (hF u hu).2.2
                omega
        obtain ⟨t_pre, ht_pre_v, ht_pre_w, ht_pre_h⟩ := hpre_tree
        by_cases hsuf : w_suf = []
        · have hw_eq : w_pre = w := by
            have := List.take_append_drop k w
            simpa [w_pre, w_suf, hsuf] using this
          exact ⟨t_pre, ht_pre_v, ht_pre_w.trans hw_eq, by omega⟩
        · have hsuf_no : ∀ i, 0 < i → i < w_suf.length + 1 → evalWord f (w_suf.take i) ≠ 1 := by
            intro i hi1 hi2 heq
            have hlen_suf : w_suf.length = w.length - k := by simp [w_suf]
            have htake : w.take (k + i) = w_pre ++ w_suf.take i := by
              simp [w_pre, w_suf, List.take_add]
            have heval_ki : evalWord f (w.take (k + i)) = 1 := by
              rw [htake, evalWord_append, hk_val, heq, one_mul]
            exact hk_max (k + i) (by omega) (by omega) heval_ki
          have hpref_suf : groupPrefixes f w_suf ⊆ groupPrefixes f w := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
            rw [Finset.mem_range] at hi
            have hlen_suf : w_suf.length = w.length - k := by simp [w_suf]
            simp only [groupPrefixes, Finset.mem_image, Finset.mem_range]
            refine ⟨k + i, by omega, ?_⟩
            have htake : w.take (k + i) = w_pre ++ w_suf.take i := by
              simp [w_pre, w_suf, List.take_add]
            rw [htake, evalWord_append, hk_val, one_mul]
          have hcard_suf : (groupPrefixes f w_suf).card ≤ r + 1 :=
            le_trans (Finset.card_le_card hpref_suf) hr
          obtain ⟨t_suf, ht_suf_v, ht_suf_w, ht_suf_h⟩ :=
            group_tree_of_no_one_prefix f hsuf hsuf_no hcard_suf ih
          refine ⟨.bin t_pre t_suf,
            FactorizationTree.isWellFormed_bin_iff.mpr ⟨ht_pre_v, ht_suf_v⟩, ?_, ?_⟩
          · simp [ht_pre_w, ht_suf_w, w_pre, w_suf]
          · simp; omega
      · have hno' : ∀ i, 0 < i → i < w.length + 1 → evalWord f (w.take i) ≠ 1 := by
          intro i hi1 hi2 heq
          exact hex ⟨i, hi1, hi2, heq⟩
        obtain ⟨t, htv, htw, hth⟩ := group_tree_of_no_one_prefix f hw hno' hr ih
        exact ⟨t, htv, htw, by omega⟩

/-- Corollary of `exists_factorizationTree_group` for any finite group `G`. -/
theorem exists_factorizationTree_group_of_finite {α G : Type*} [Group G] [Fintype G]
    (f : α → G) (w : List α) (hw : w ≠ []) :
    ∃ t : FactorizationTree α,
      t.IsWellFormed f ∧ t.word = w ∧ t.height ≤ 4 * Fintype.card G := by
  classical
  exact exists_factorizationTree_group f (Fintype.card G) w hw (Finset.card_le_univ _)

end GroupStage

/-! ### Green's Relations, Stability, and Green's Theorem in Finite Subsemigroups -/

section GreenRelations

variable {M : Type v} [Monoid M]

/-- The monoid extension `S¹ = {1} ∪ S` of a finite subset `S ⊆ M`. -/
def subsemigroupUnit (S : Finset M) : Set M := insert 1 (S : Set M)

/-- Membership characterization for `subsemigroupUnit`. -/
theorem mem_subsemigroupUnit_iff (S : Finset M) (x : M) :
    x ∈ subsemigroupUnit S ↔ x = 1 ∨ x ∈ S := Iff.rfl

/-- `1` always belongs to `subsemigroupUnit S`. -/
theorem one_mem_subsemigroupUnit (S : Finset M) : (1 : M) ∈ subsemigroupUnit S :=
  Set.mem_insert 1 _

/-- Every element of `S` belongs to `subsemigroupUnit S`. -/
theorem mem_subsemigroupUnit_of_mem {S : Finset M} {x : M} (hx : x ∈ S) :
    x ∈ subsemigroupUnit S :=
  Set.mem_insert_of_mem 1 hx

/-- `subsemigroupUnit S` is closed under multiplication when `S` is a subsemigroup. -/
theorem subsemigroupUnit_mul {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {x y : M} (hx : x ∈ subsemigroupUnit S) (hy : y ∈ subsemigroupUnit S) :
    x * y ∈ subsemigroupUnit S := by
  rcases hx with rfl | hx
  · simpa using hy
  · rcases hy with rfl | hy
    · simpa using mem_subsemigroupUnit_of_mem hx
    · exact mem_subsemigroupUnit_of_mem (hS x hx y hy)

/-- `subsemigroupUnit S` is closed under natural powers when `S` is a subsemigroup. -/
theorem subsemigroupUnit_pow {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {x : M} (hx : x ∈ subsemigroupUnit S) (m : ℕ) : x ^ m ∈ subsemigroupUnit S := by
  induction m with
  | zero => simpa using one_mem_subsemigroupUnit S
  | succ m ih => rw [pow_succ]; exact subsemigroupUnit_mul hS ih hx

/-- Every element of `subsemigroupUnit S` in a finite subsemigroup `S` has a positive idempotent
power. -/
theorem exists_idempotent_pow_subsemigroupUnit {S : Finset M}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) {x : M} (hx : x ∈ subsemigroupUnit S) :
    ∃ m : ℕ, 1 ≤ m ∧ x ^ m * x ^ m = x ^ m := by
  classical
  let T : Finset M := insert 1 S
  have hmem : ∀ k : ℕ, x ^ (k + 1) ∈ T := by
    intro k
    have h := subsemigroupUnit_pow hS hx (k + 1)
    rcases h with heq | hmem
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · exact Finset.mem_insert_of_mem hmem
  have hnotinj : ¬ Function.Injective (fun k : Fin (T.card + 1) ↦ (⟨x ^ (k.val +
    1), hmem k.val⟩ : T)) := by
    intro hinj
    have hcard := Fintype.card_le_of_injective _ hinj
    simp at hcard
  rw [Function.Injective] at hnotinj
  push Not at hnotinj
  rcases hnotinj with ⟨i, j, heq, hne⟩
  have hval_eq : x ^ (i.val + 1) = x ^ (j.val + 1) := congrArg Subtype.val heq
  wlog hlt : i.val < j.val generalizing i j
  · have hgt : j.val < i.val := by
      have : i.val ≠ j.val := fun h ↦ hne (Fin.ext h)
      omega
    exact this j i heq.symm hne.symm hval_eq.symm hgt
  let p := j.val - i.val
  have hp : 1 ≤ p := by omega
  have hstep : ∀ k : ℕ, x ^ (i.val + 1 + k * p) = x ^ (i.val + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      have : i.val + 1 + (k + 1) * p = (i.val + 1 + k * p) + p := by ring
      rw [this, pow_add, ihk, ← pow_add]
      have : i.val + 1 + p = j.val + 1 := by omega
      rw [this, ← hval_eq]
  have hshift : ∀ a q : ℕ, i.val + 1 ≤ a → x ^ (a + q * p) = x ^ a := by
    intro a q ha
    have : a + q * p = (a - (i.val + 1)) + (i.val + 1 + q * p) := by omega
    rw [this, pow_add, hstep q, ← pow_add]
    congr 1; omega
  let m := (i.val + 1) * p
  have hm_ge : i.val + 1 ≤ m := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨m, by omega, ?_⟩
  rw [← pow_add]
  exact hshift m (i.val + 1) hm_ge

/-- Green's `R`-preorder relative to `S`: `a ≤_R b` iff `a = b * y` for some `y ∈ S¹`. -/
def GreenRLe (S : Finset M) (a b : M) : Prop := ∃ y ∈ subsemigroupUnit S, a = b * y

/-- Green's `L`-preorder relative to `S`: `a ≤_L b` iff `a = x * b` for some `x ∈ S¹`. -/
def GreenLLe (S : Finset M) (a b : M) : Prop := ∃ x ∈ subsemigroupUnit S, a = x * b

/-- Green's `J`-preorder relative to `S`: `a ≤_J b` iff `a = x * b * y` for some `x, y ∈ S¹`. -/
def GreenJLe (S : Finset M) (a b : M) : Prop :=
  ∃ x ∈ subsemigroupUnit S, ∃ y ∈ subsemigroupUnit S, a = x * b * y

/-- Green's `R`-equivalence relative to `S`. -/
def GreenREq (S : Finset M) (a b : M) : Prop := GreenRLe S a b ∧ GreenRLe S b a

/-- Green's `L`-equivalence relative to `S`. -/
def GreenLEq (S : Finset M) (a b : M) : Prop := GreenLLe S a b ∧ GreenLLe S b a

/-- Green's `H`-equivalence relative to `S`. -/
def GreenHEq (S : Finset M) (a b : M) : Prop := GreenREq S a b ∧ GreenLEq S a b

/-- Green's `J`-equivalence relative to `S`. -/
def GreenJEq (S : Finset M) (a b : M) : Prop := GreenJLe S a b ∧ GreenJLe S b a

/-- Unfolding characterization of `GreenRLe`. -/
theorem greenRLe_iff (S : Finset M) (a b : M) :
    GreenRLe S a b ↔ ∃ y ∈ subsemigroupUnit S, a = b * y := Iff.rfl

/-- Unfolding characterization of `GreenLLe`. -/
theorem greenLLe_iff (S : Finset M) (a b : M) :
    GreenLLe S a b ↔ ∃ x ∈ subsemigroupUnit S, a = x * b := Iff.rfl

/-- Unfolding characterization of `GreenJLe`. -/
theorem greenJLe_iff (S : Finset M) (a b : M) :
    GreenJLe S a b ↔ ∃ x ∈ subsemigroupUnit S, ∃ y ∈ subsemigroupUnit S, a = x * b * y := Iff.rfl

/-- Unfolding characterization of `GreenREq`. -/
theorem greenREq_iff (S : Finset M) (a b : M) :
    GreenREq S a b ↔ GreenRLe S a b ∧ GreenRLe S b a := Iff.rfl

/-- Unfolding characterization of `GreenLEq`. -/
theorem greenLEq_iff (S : Finset M) (a b : M) :
    GreenLEq S a b ↔ GreenLLe S a b ∧ GreenLLe S b a := Iff.rfl

/-- Unfolding characterization of `GreenHEq`. -/
theorem greenHEq_iff (S : Finset M) (a b : M) :
    GreenHEq S a b ↔ GreenREq S a b ∧ GreenLEq S a b := Iff.rfl

/-- Unfolding characterization of `GreenJEq`. -/
theorem greenJEq_iff (S : Finset M) (a b : M) :
    GreenJEq S a b ↔ GreenJLe S a b ∧ GreenJLe S b a := Iff.rfl

/-- Reflexivity of `GreenRLe`. -/
theorem greenRLe_refl (S : Finset M) (a : M) : GreenRLe S a a :=
  ⟨1, one_mem_subsemigroupUnit S, (mul_one a).symm⟩

/-- Reflexivity of `GreenLLe`. -/
theorem greenLLe_refl (S : Finset M) (a : M) : GreenLLe S a a :=
  ⟨1, one_mem_subsemigroupUnit S, (one_mul a).symm⟩

/-- Reflexivity of `GreenJLe`. -/
theorem greenJLe_refl (S : Finset M) (a : M) : GreenJLe S a a :=
  ⟨1, one_mem_subsemigroupUnit S, 1, one_mem_subsemigroupUnit S, by simp⟩

/-- Transitivity of `GreenRLe` in a subsemigroup. -/
theorem greenRLe_trans {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b c : M} (h1 : GreenRLe S a b) (h2 : GreenRLe S b c) : GreenRLe S a c := by
  rcases h1 with ⟨y₁, hy₁, rfl⟩
  rcases h2 with ⟨y₂, hy₂, rfl⟩
  exact ⟨y₂ * y₁, subsemigroupUnit_mul hS hy₂ hy₁, by rw [mul_assoc]⟩

/-- Transitivity of `GreenLLe` in a subsemigroup. -/
theorem greenLLe_trans {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b c : M} (h1 : GreenLLe S a b) (h2 : GreenLLe S b c) : GreenLLe S a c := by
  rcases h1 with ⟨x₁, hx₁, rfl⟩
  rcases h2 with ⟨x₂, hx₂, rfl⟩
  exact ⟨x₁ * x₂, subsemigroupUnit_mul hS hx₁ hx₂, by rw [mul_assoc]⟩

/-- Transitivity of `GreenJLe` in a subsemigroup. -/
theorem greenJLe_trans {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b c : M} (h1 : GreenJLe S a b) (h2 : GreenJLe S b c) : GreenJLe S a c := by
  rcases h1 with ⟨x₁, hx₁, y₁, hy₁, rfl⟩
  rcases h2 with ⟨x₂, hx₂, y₂, hy₂, rfl⟩
  refine ⟨x₁ * x₂, subsemigroupUnit_mul hS hx₁ hx₂, y₂ * y₁, subsemigroupUnit_mul hS hy₂ hy₁, ?_⟩
  simp [mul_assoc]

/-- Reflexivity of `GreenREq`. -/
theorem greenREq_refl (S : Finset M) (a : M) : GreenREq S a a :=
  ⟨greenRLe_refl S a, greenRLe_refl S a⟩

/-- Symmetry of `GreenREq`. -/
theorem greenREq_symm {S : Finset M} {a b : M} (h : GreenREq S a b) : GreenREq S b a :=
  ⟨h.2, h.1⟩

/-- Transitivity of `GreenREq` in a subsemigroup. -/
theorem greenREq_trans {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b c : M} (h1 : GreenREq S a b) (h2 : GreenREq S b c) : GreenREq S a c :=
  ⟨greenRLe_trans hS h1.1 h2.1, greenRLe_trans hS h2.2 h1.2⟩

/-- Reflexivity of `GreenLEq`. -/
theorem greenLEq_refl (S : Finset M) (a : M) : GreenLEq S a a :=
  ⟨greenLLe_refl S a, greenLLe_refl S a⟩

/-- Symmetry of `GreenLEq`. -/
theorem greenLEq_symm {S : Finset M} {a b : M} (h : GreenLEq S a b) : GreenLEq S b a :=
  ⟨h.2, h.1⟩

/-- Transitivity of `GreenLEq` in a subsemigroup. -/
theorem greenLEq_trans {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b c : M} (h1 : GreenLEq S a b) (h2 : GreenLEq S b c) : GreenLEq S a c :=
  ⟨greenLLe_trans hS h1.1 h2.1, greenLLe_trans hS h2.2 h1.2⟩

/-- Symmetry of `GreenHEq`. -/
theorem greenHEq_symm {S : Finset M} {a b : M} (h : GreenHEq S a b) : GreenHEq S b a :=
  ⟨greenREq_symm h.1, greenLEq_symm h.2⟩

/-- Reflexivity of `GreenJEq`. -/
theorem greenJEq_refl (S : Finset M) (a : M) : GreenJEq S a a :=
  ⟨greenJLe_refl S a, greenJLe_refl S a⟩

/-- Symmetry of `GreenJEq`. -/
theorem greenJEq_symm {S : Finset M} {a b : M} (h : GreenJEq S a b) : GreenJEq S b a :=
  ⟨h.2, h.1⟩

/-- Transitivity of `GreenJEq` in a subsemigroup. -/
theorem greenJEq_trans {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b c : M} (h1 : GreenJEq S a b) (h2 : GreenJEq S b c) : GreenJEq S a c :=
  ⟨greenJLe_trans hS h1.1 h2.1, greenJLe_trans hS h2.2 h1.2⟩

/-- Green's `R`-preorder refines the `J`-preorder. -/
theorem greenJLe_of_rLe {S : Finset M} {a b : M} (h : GreenRLe S a b) : GreenJLe S a b := by
  rcases h with ⟨y, hy, rfl⟩
  exact ⟨1, one_mem_subsemigroupUnit S, y, hy, by simp⟩

/-- Green's `L`-preorder refines the `J`-preorder. -/
theorem greenJLe_of_lLe {S : Finset M} {a b : M} (h : GreenLLe S a b) : GreenJLe S a b := by
  rcases h with ⟨x, hx, rfl⟩
  exact ⟨x, hx, 1, one_mem_subsemigroupUnit S, by simp⟩

/-- Multiplying on the right by an element of `S¹` goes down in the `R`-preorder. -/
theorem greenRLe_mul_left {S : Finset M} {a b : M} (hb : b ∈ subsemigroupUnit S) :
    GreenRLe S (a * b) a :=
  ⟨b, hb, rfl⟩

/-- Multiplying on the left by an element of `S¹` goes down in the `L`-preorder. -/
theorem greenLLe_mul_right {S : Finset M} {a b : M} (ha : a ∈ subsemigroupUnit S) :
    GreenLLe S (a * b) b :=
  ⟨a, ha, rfl⟩

/-- Stability for Green's `R`-relation in a finite subsemigroup: `a ≤_R b` and `a ≡_J b` imply
`a ≡_R b`. -/
theorem greenREq_of_rLe_of_jEq {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b : M} (hr : GreenRLe S a b) (hj : GreenJEq S a b) : GreenREq S a b := by
  refine ⟨hr, ?_⟩
  rcases hr with ⟨z, hz, rfl⟩
  rcases hj.2 with ⟨u, hu, v, hv, hbuv⟩
  have hstep : ∀ m : ℕ, b = u ^ m * b * (z * v) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [pow_succ', pow_succ]
      calc b = u * (b * z) * v := hbuv
        _ = u * (u ^ m * b * (z * v) ^ m) * (z * v) := by
            conv_lhs => rw [ihm]
            simp [mul_assoc]
        _ = u * u ^ m * b * ((z * v) ^ m * (z * v)) := by simp [mul_assoc]
  obtain ⟨m, hm1, hidem⟩ := exists_idempotent_pow_subsemigroupUnit hS hu
  have hbm := hstep m
  have hub : u ^ m * b = b := by
    calc u ^ m * b = u ^ m * (u ^ m * b * (z * v) ^ m) := by conv_lhs => rw [hbm]
      _ = (u ^ m * u ^ m) * b * (z * v) ^ m := by simp [mul_assoc]
      _ = u ^ m * b * (z * v) ^ m := by rw [hidem]
      _ = b := hbm.symm
  have hzv_mem : z * v ∈ subsemigroupUnit S := subsemigroupUnit_mul hS hz hv
  have hpow_zv : v * (z * v) ^ (m - 1) ∈ subsemigroupUnit S :=
    subsemigroupUnit_mul hS hv (subsemigroupUnit_pow hS hzv_mem (m - 1))
  refine ⟨v * (z * v) ^ (m - 1), hpow_zv, ?_⟩
  have hm_eq : m = 1 + (m - 1) := by omega
  calc b = u ^ m * b * (z * v) ^ m := hbm
    _ = b * (z * v) ^ m := by rw [hub]
    _ = b * ((z * v) * (z * v) ^ (m - 1)) := by
        conv_lhs => rw [hm_eq, pow_add, pow_one]
    _ = b * z * (v * (z * v) ^ (m - 1)) := by simp [mul_assoc]

/-- Stability for Green's `L`-relation in a finite subsemigroup: `a ≤_L b` and `a ≡_J b` imply
`a ≡_L b`. -/
theorem greenLEq_of_lLe_of_jEq {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b : M} (hl : GreenLLe S a b) (hj : GreenJEq S a b) : GreenLEq S a b := by
  refine ⟨hl, ?_⟩
  rcases hl with ⟨z, hz, rfl⟩
  rcases hj.2 with ⟨u, hu, v, hv, hbuv⟩
  have hstep : ∀ m : ℕ, b = (u * z) ^ m * b * v ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [pow_succ', pow_succ]
      calc b = u * (z * b) * v := hbuv
        _ = (u * z) * ((u * z) ^ m * b * v ^ m) * v := by
            conv_lhs => rw [ihm]
            simp [mul_assoc]
        _ = (u * z) * (u * z) ^ m * b * (v ^ m * v) := by simp [mul_assoc]
  obtain ⟨m, hm1, hidem⟩ := exists_idempotent_pow_subsemigroupUnit hS hv
  have hbm := hstep m
  have hbv : b * v ^ m = b := by
    calc b * v ^ m = ((u * z) ^ m * b * v ^ m) * v ^ m := by conv_lhs => rw [hbm]
      _ = (u * z) ^ m * b * (v ^ m * v ^ m) := by simp [mul_assoc]
      _ = (u * z) ^ m * b * v ^ m := by rw [hidem]
      _ = b := hbm.symm
  have huz_mem : u * z ∈ subsemigroupUnit S := subsemigroupUnit_mul hS hu hz
  have hpow_uz : (u * z) ^ (m - 1) * u ∈ subsemigroupUnit S :=
    subsemigroupUnit_mul hS (subsemigroupUnit_pow hS huz_mem (m - 1)) hu
  refine ⟨(u * z) ^ (m - 1) * u, hpow_uz, ?_⟩
  have hm_eq : m = (m - 1) + 1 := by omega
  calc b = (u * z) ^ m * b * v ^ m := hbm
    _ = (u * z) ^ m * b := by
        rw [mul_assoc, hbv]
    _ = ((u * z) ^ (m - 1) * (u * z)) * b := by
        conv_lhs => rw [hm_eq, pow_add, pow_one]
    _ = ((u * z) ^ (m - 1) * u) * (z * b) := by simp [mul_assoc]

/-- Left cancellation in a finite subsemigroup along a `J`-preserving `R`-class: if
`p * q₁ = p * q₂` with `q₁ ≡_J p * q₁` and `q₁ ≡_R q₂`, then `q₁ = q₂`. -/
theorem eq_of_mul_eq_of_greenREq {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {p q₁ q₂ : M} (hp : p ∈ S)
    (heq : p * q₁ = p * q₂) (hj : GreenJEq S q₁ (p * q₁)) (hr : GreenREq S q₁ q₂) :
    q₁ = q₂ := by
  have hl : GreenLEq S (p * q₁) q₁ :=
    greenLEq_of_lLe_of_jEq hS (greenLLe_mul_right (mem_subsemigroupUnit_of_mem hp)) ⟨hj.2, hj.1⟩
  rcases hl.2 with ⟨s, _, hs⟩
  rcases hr.2 with ⟨y, _, hy⟩
  calc q₁ = s * (p * q₁) := hs
    _ = s * (p * q₂) := by rw [heq]
    _ = s * (p * (q₁ * y)) := by rw [hy]
    _ = (s * (p * q₁)) * y := by simp [mul_assoc]
    _ = q₁ * y := by rw [← hs]
    _ = q₂ := hy.symm

/-- Elements of the Green `H`-class of `x₀` inside a finite subsemigroup `S`. -/
@[ext]
structure GreenHClass (S : Finset M) (x₀ : M) where
  /-- The underlying monoid element. -/
  val : M
  /-- Membership in the ambient finite subsemigroup `S`. -/
  mem_S : val ∈ S
  /-- Green `H`-equivalence to the basepoint `x₀`. -/
  hEq : GreenHEq S val x₀

/-- **Green's Theorem**: an `H`-class of a finite subsemigroup `S` containing `x₀` and `y₀` such
that `x₀ * y₀` lies in the same `J`-class forms a group under the ambient monoid multiplication. -/
theorem exists_greenHClass_group_ops {S : Finset M} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {x₀ y₀ : M} (hx₀ : x₀ ∈ S) (hy₀ : y₀ ∈ S)
    (hH : GreenHEq S x₀ y₀) (hJ : GreenJEq S x₀ (x₀ * y₀)) :
    ∃ e : GreenHClass S x₀,
      (∀ a : GreenHClass S x₀, a.val * e.val = a.val ∧ e.val * a.val = a.val) ∧
      (∀ a b : GreenHClass S x₀, a.val * b.val ∈ S ∧ GreenHEq S (a.val * b.val) x₀) ∧
      (∀ a : GreenHClass S x₀, ∃ b : GreenHClass S x₀,
        a.val * b.val = e.val ∧ b.val * a.val = e.val) := by
  have hS_S1 : ∀ x ∈ S, x ∈ subsemigroupUnit S := fun _ hx ↦ mem_subsemigroupUnit_of_mem hx
  have hJ_y : GreenJEq S y₀ (x₀ * y₀) :=
    ⟨greenJLe_trans hS (greenJLe_of_rLe hH.1.2) hJ.1,
     greenJLe_trans hS hJ.2 (greenJLe_of_rLe hH.1.1)⟩
  have hR_x_xy : GreenREq S (x₀ * y₀) x₀ :=
    greenREq_of_rLe_of_jEq hS (greenRLe_mul_left (hS_S1 y₀ hy₀)) ⟨hJ.2, hJ.1⟩
  rcases hR_x_xy.2 with ⟨z, hz, hxz⟩
  let e_val : M := y₀ * z
  have he_S : e_val ∈ S := by
    rcases hz with rfl | hzS
    · simpa [e_val] using hy₀
    · exact hS y₀ hy₀ z hzS
  have hye : y₀ * e_val = y₀ := by
    rcases hH.2.2 with ⟨s, _, hs⟩
    calc y₀ * e_val = (s * x₀) * (y₀ * z) := by rw [← hs]
      _ = s * (x₀ * y₀ * z) := by simp [mul_assoc]
      _ = s * x₀ := by rw [← hxz]
      _ = y₀ := hs.symm
  have he_J : GreenJEq S e_val y₀ :=
    ⟨greenJLe_of_rLe (greenRLe_mul_left hz),
     ⟨y₀, hS_S1 y₀ hy₀, 1, one_mem_subsemigroupUnit S, by simpa using hye.symm⟩⟩
  have he_R : GreenREq S e_val y₀ := greenREq_of_rLe_of_jEq hS (greenRLe_mul_left hz) he_J
  have he_L : GreenLEq S e_val y₀ := by
    have h1 : GreenLEq S (y₀ * e_val) e_val :=
      greenLEq_of_lLe_of_jEq hS (greenLLe_mul_right (hS_S1 y₀ hy₀))
        ⟨by rw [hye]; exact he_J.2, by rw [hye]; exact he_J.1⟩
    rw [hye] at h1
    exact ⟨h1.2, h1.1⟩
  have he_H : GreenHEq S e_val x₀ :=
    ⟨⟨greenRLe_trans hS he_R.1 hH.1.2, greenRLe_trans hS hH.1.1 he_R.2⟩,
     ⟨greenLLe_trans hS he_L.1 hH.2.2, greenLLe_trans hS hH.2.1 he_L.2⟩⟩
  have hright_id : ∀ a : GreenHClass S x₀, a.val * e_val = a.val := by
    intro a
    rcases a.hEq.2.1 with ⟨s, _, hs⟩
    calc a.val * e_val = (s * x₀) * (y₀ * z) := by rw [hs]
      _ = s * (x₀ * y₀ * z) := by simp [mul_assoc]
      _ = s * x₀ := by rw [← hxz]
      _ = a.val := hs.symm
  have hL_y_xy : GreenLEq S (x₀ * y₀) y₀ :=
    greenLEq_of_lLe_of_jEq hS (greenLLe_mul_right (hS_S1 x₀ hx₀)) ⟨hJ_y.2, hJ_y.1⟩
  rcases hL_y_xy.2 with ⟨w, hw, hyw⟩
  let e'_val : M := w * x₀
  have he'_S : e'_val ∈ S := by
    rcases hw with rfl | hwS
    · simpa [e'_val] using hx₀
    · exact hS w hwS x₀ hx₀
  have he'x : e'_val * x₀ = x₀ := by
    rcases hH.1.1 with ⟨t, _, ht⟩
    calc e'_val * x₀ = (w * x₀) * (y₀ * t) := by rw [← ht]
      _ = (w * (x₀ * y₀)) * t := by simp [mul_assoc]
      _ = y₀ * t := by rw [← hyw]
      _ = x₀ := ht.symm
  have hleft_id : ∀ a : GreenHClass S x₀, e'_val * a.val = a.val := by
    intro a
    rcases a.hEq.1.1 with ⟨t, _, ht⟩
    calc e'_val * a.val = e'_val * (x₀ * t) := by rw [ht]
      _ = (e'_val * x₀) * t := by rw [← mul_assoc]
      _ = x₀ * t := by rw [he'x]
      _ = a.val := ht.symm
  have he'_J : GreenJEq S e'_val x₀ :=
    ⟨greenJLe_of_lLe (greenLLe_mul_right hw),
     ⟨1, one_mem_subsemigroupUnit S, x₀, hS_S1 x₀ hx₀, by simpa [mul_assoc] using he'x.symm⟩⟩
  have he'_L : GreenLEq S e'_val x₀ := greenLEq_of_lLe_of_jEq hS (greenLLe_mul_right hw) he'_J
  have he'_R : GreenREq S e'_val x₀ := by
    have h1 : GreenREq S (e'_val * x₀) e'_val :=
      greenREq_of_rLe_of_jEq hS (greenRLe_mul_left (hS_S1 x₀ hx₀))
        ⟨by rw [he'x]; exact he'_J.2, by rw [he'x]; exact he'_J.1⟩
    rw [he'x] at h1
    exact ⟨h1.2, h1.1⟩
  have he'_H : GreenHEq S e'_val x₀ := ⟨he'_R, he'_L⟩
  let e : GreenHClass S x₀ := ⟨e_val, he_S, he_H⟩
  let e' : GreenHClass S x₀ := ⟨e'_val, he'_S, he'_H⟩
  have hee' : e'_val = e_val := by
    have h1 := hright_id e'
    have h2 := hleft_id e
    exact h1.symm.trans h2
  have hboth_id : ∀ a : GreenHClass S x₀, a.val * e.val = a.val ∧ e.val * a.val = a.val := by
    intro a
    exact ⟨hright_id a, by rw [show e.val = e'_val from hee'.symm]; exact hleft_id a⟩
  have hclosed : ∀ a b : GreenHClass S x₀, a.val * b.val ∈ S ∧ GreenHEq S (a.val * b.val) x₀ := by
    intro a b
    have hab_S : a.val * b.val ∈ S := hS a.val a.mem_S b.val b.mem_S
    have hLae : GreenLEq S a.val e.val :=
      ⟨greenLLe_trans hS a.hEq.2.1 he_H.2.2, greenLLe_trans hS he_H.2.1 a.hEq.2.2⟩
    rcases hLae.2 with ⟨u, hu, hu_eq⟩
    have hJ_ab_b : GreenJEq S (a.val * b.val) b.val := by
      refine ⟨greenJLe_of_lLe (greenLLe_mul_right (hS_S1 a.val a.mem_S)), ?_⟩
      refine ⟨u, hu, 1, one_mem_subsemigroupUnit S, ?_⟩
      calc b.val = e.val * b.val := (hboth_id b).2.symm
        _ = (u * a.val) * b.val := by rw [hu_eq]
        _ = u * (a.val * b.val) * 1 := by simp [mul_assoc]
    have hR_ab_a : GreenREq S (a.val * b.val) a.val := by
      have hJ_ab_a : GreenJEq S (a.val * b.val) a.val :=
        ⟨greenJLe_of_rLe (greenRLe_mul_left (hS_S1 b.val b.mem_S)),
         greenJLe_trans hS
          (greenJLe_trans hS (greenJLe_of_rLe a.hEq.1.1) (greenJLe_of_rLe b.hEq.1.2))
          hJ_ab_b.2⟩
      exact greenREq_of_rLe_of_jEq hS (greenRLe_mul_left (hS_S1 b.val b.mem_S)) hJ_ab_a
    have hL_ab_b : GreenLEq S (a.val * b.val) b.val :=
      greenLEq_of_lLe_of_jEq hS (greenLLe_mul_right (hS_S1 a.val a.mem_S)) hJ_ab_b
    refine ⟨hab_S, ⟨⟨greenRLe_trans hS hR_ab_a.1 a.hEq.1.1,
      greenRLe_trans hS a.hEq.1.2 hR_ab_a.2⟩,
      ⟨greenLLe_trans hS hL_ab_b.1 b.hEq.2.1, greenLLe_trans hS b.hEq.2.2 hL_ab_b.2⟩⟩⟩
  have hinv : ∀ a : GreenHClass S x₀, ∃ b : GreenHClass S x₀,
      a.val * b.val = e.val ∧ b.val * a.val = e.val := by
    intro a
    have hRae : GreenREq S a.val e.val :=
      ⟨greenRLe_trans hS a.hEq.1.1 he_H.1.2, greenRLe_trans hS he_H.1.1 a.hEq.1.2⟩
    rcases hRae.2 with ⟨v, hv, hv_eq⟩
    let b_val : M := e.val * v * e.val
    have hb_S : b_val ∈ S := by
      have hev : e.val * v ∈ S := by
        rcases hv with rfl | hvS
        · simpa using e.mem_S
        · exact hS e.val e.mem_S v hvS
      exact hS _ hev e.val e.mem_S
    have hab : a.val * b_val = e.val := by
      calc a.val * b_val = (a.val * e.val) * v * e.val := by simp [b_val, mul_assoc]
        _ = (a.val * v) * e.val := by rw [(hboth_id a).1]
        _ = e.val * e.val := by rw [← hv_eq]
        _ = e.val := (hboth_id e).1
    have hb_J : GreenJEq S b_val e.val :=
      ⟨greenJLe_of_rLe ⟨v * e.val, subsemigroupUnit_mul hS hv (hS_S1 e.val e.mem_S),
        by simp [b_val, mul_assoc]⟩,
       ⟨a.val, hS_S1 a.val a.mem_S, 1, one_mem_subsemigroupUnit S, by simpa using hab.symm⟩⟩
    have hb_R : GreenREq S b_val e.val :=
      greenREq_of_rLe_of_jEq hS
        ⟨v * e.val, subsemigroupUnit_mul hS hv (hS_S1 e.val e.mem_S), by simp [b_val, mul_assoc]⟩
        hb_J
    have hb_L : GreenLEq S b_val e.val :=
      greenLEq_of_lLe_of_jEq hS
        ⟨e.val * v, subsemigroupUnit_mul hS (hS_S1 e.val e.mem_S) hv, by simp [b_val, mul_assoc]⟩
        hb_J
    have hb_H : GreenHEq S b_val x₀ :=
      ⟨⟨greenRLe_trans hS hb_R.1 e.hEq.1.1, greenRLe_trans hS e.hEq.1.2 hb_R.2⟩,
       ⟨greenLLe_trans hS hb_L.1 e.hEq.2.1, greenLLe_trans hS e.hEq.2.2 hb_L.2⟩⟩
    let b : GreenHClass S x₀ := ⟨b_val, hb_S, hb_H⟩
    have hLae : GreenLEq S a.val e.val :=
      ⟨greenLLe_trans hS a.hEq.2.1 he_H.2.2, greenLLe_trans hS he_H.2.1 a.hEq.2.2⟩
    rcases hLae.2 with ⟨u, hu, hu_eq⟩
    let b'_val : M := e.val * u * e.val
    have hb'a : b'_val * a.val = e.val := by
      calc b'_val * a.val = e.val * (u * (e.val * a.val)) := by simp [b'_val, mul_assoc]
        _ = e.val * (u * a.val) := by rw [(hboth_id a).2]
        _ = e.val * e.val := by rw [← hu_eq]
        _ = e.val := (hboth_id e).1
    have hb'e : b'_val * e.val = b'_val := by
      calc b'_val * e.val = e.val * u * (e.val * e.val) := by simp [b'_val, mul_assoc]
        _ = b'_val := by rw [(hboth_id e).1]
    have hbb' : b'_val = b_val := by
      calc b'_val = b'_val * e.val := hb'e.symm
        _ = b'_val * (a.val * b_val) := by rw [hab]
        _ = (b'_val * a.val) * b_val := by rw [← mul_assoc]
        _ = e.val * b_val := by rw [hb'a]
        _ = b_val := (hboth_id b).2
    refine ⟨b, hab, ?_⟩
    change b_val * a.val = e.val
    rw [← hbb']
    exact hb'a
  exact ⟨e, hboth_id, hclosed, hinv⟩

end GreenRelations

end CslibFrontier.Computability.Languages
