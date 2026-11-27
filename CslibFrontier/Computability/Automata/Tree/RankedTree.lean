module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.Linarith

/-!
# Ranked Trees, Tree Homomorphisms, and Regular Tree Languages

This module develops ranked alphabets, terms/trees over variables, ground trees, tree
positions, simultaneous substitution, non-deleting and linear tree homomorphisms, the
generic word-to-tree encoding, and bottom-up deterministic/nondeterministic finite tree
automata recognizing regular tree languages.

## Main definitions

* `PaperLib.RankedTree`: terms over a ranked alphabet `(Γ, rank)` and variable type `X`.
* `PaperLib.GroundTree`: ground trees (`RankedTree Γ rank PEmpty`).
* `PaperLib.TreeHom`: tree homomorphisms between ranked alphabets, with `TreeHom.eval`,
  `TreeHom.IsNonDeleting`, and `TreeHom.IsLinear`.
* `PaperLib.wordRank`, `PaperLib.genericTree`, `PaperLib.wordTreeEquiv`,
  `PaperLib.genericTreeHom`: word-to-tree encodings `Alph* → T_{Alph_#^r}`.
* `PaperLib.DFTA`, `PaperLib.NFTA`, `PaperLib.IsRegularTreeLang`: bottom-up finite tree
  automata and regular tree languages.

## Main results

* `PaperLib.TreeHom.finite_preimage_of_isNonDeleting`: every non-deleting tree homomorphism
  has finite fibers on ground trees over a finite ranked alphabet.
* `PaperLib.IsRegularTreeLang.compl`, `PaperLib.IsRegularTreeLang.inter`,
  `PaperLib.IsRegularTreeLang.union`, `PaperLib.IsRegularTreeLang.preimage_treeHom`:
  closure of regular tree languages under Boolean operations and inverse tree homomorphisms.
* `PaperLib.isRegularTreeLang_iff_nfta`: equivalence of deterministic and nondeterministic
  bottom-up finite tree automata.
* `PaperLib.IsRegularTreeLang.image_of_isLinear`: closure of regular tree languages under
  linear tree homomorphisms.
-/

public section

universe u v w

namespace CslibFrontier

open Finset

/-- Terms (trees) over a ranked alphabet `(Γ, rank)` with variables from `X`. -/
inductive RankedTree (Γ : Type u) (rank : Γ → ℕ) (X : Type v) : Type (max u v) where
  /-- A variable leaf. -/
  | var (x : X) : RankedTree Γ rank X
  /-- An internal or constant node labeled by `g : Γ` with `rank g` children. -/
  | node (g : Γ) (children : Fin (rank g) → RankedTree Γ rank X) : RankedTree Γ rank X

/-- Ground trees over a ranked alphabet `(Γ, rank)` (no variables). -/
abbrev GroundTree (Γ : Type u) (rank : Γ → ℕ) : Type u :=
  RankedTree Γ rank PEmpty.{1}

namespace RankedTree

variable {Γ : Type u} {rank : Γ → ℕ} {X : Type v} {Y : Type w}

/-- Eliminate variables from a ground tree; useful for structural recursion. -/
theorem no_var (x : PEmpty.{1}) : False := x.elim

/-- Number of ranked-alphabet nodes in a tree (variables contribute `0`). -/
@[expose] def size : RankedTree Γ rank X → ℕ
  | var _ => 0
  | node _ ch => 1 + ∑ i, (ch i).size

@[simp] theorem size_var (x : X) : (var x : RankedTree Γ rank X).size = 0 := rfl

@[simp] theorem size_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).size = 1 + ∑ i, (ch i).size := rfl

/-- Every ground tree has size at least `1`. -/
theorem one_le_size_ground (t : GroundTree Γ rank) : 1 ≤ t.size := by
  cases t with
  | var x => exact x.elim
  | node g ch =>
    rw [size_node]
    omega

/-- Total number of variable occurrences `ra(t)` in a tree. -/
@[expose] def varCount : RankedTree Γ rank X → ℕ
  | var _ => 1
  | node _ ch => ∑ i, (ch i).varCount

@[simp] theorem varCount_var (x : X) : (var x : RankedTree Γ rank X).varCount = 1 := rfl

@[simp] theorem varCount_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).varCount = ∑ i, (ch i).varCount := rfl

/-- Number of occurrences of a specific variable `x` in `t`. -/
@[expose] def varOccurrences [DecidableEq X] : RankedTree Γ rank X → X → ℕ
  | var y, x => if y = x then 1 else 0
  | node _ ch, x => ∑ i, (ch i).varOccurrences x

@[simp] theorem varOccurrences_var [DecidableEq X] (y x : X) :
    (var y : RankedTree Γ rank X).varOccurrences x = if y = x then 1 else 0 := rfl

@[simp] theorem varOccurrences_node [DecidableEq X] (g : Γ)
    (ch : Fin (rank g) → RankedTree Γ rank X) (x : X) :
    (node g ch).varOccurrences x = ∑ i, (ch i).varOccurrences x := rfl

/-- Whether a tree contains at least one symbol from `Γ`. -/
@[expose] def hasSymbol : RankedTree Γ rank X → Prop
  | var _ => False
  | node _ _ => True

@[simp] theorem hasSymbol_var (x : X) : ¬ (var x : RankedTree Γ rank X).hasSymbol := id

@[simp] theorem hasSymbol_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).hasSymbol := trivial

/-- Simultaneous substitution of variables in a ranked tree. -/
@[expose] def subst (f : X → RankedTree Γ rank Y) : RankedTree Γ rank X → RankedTree Γ rank Y
  | var x => f x
  | node g ch => node g (fun i => (ch i).subst f)

@[simp] theorem subst_var (f : X → RankedTree Γ rank Y) (x : X) :
    (var x : RankedTree Γ rank X).subst f = f x := rfl

@[simp] theorem subst_node (f : X → RankedTree Γ rank Y) (g : Γ)
    (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).subst f = node g (fun i => (ch i).subst f) := rfl

/-- Substitution by `var` is the identity. -/
@[simp] theorem subst_id (t : RankedTree Γ rank X) : t.subst var = t := by
  induction t with
  | var x => rfl
  | node g ch ih =>
    rw [subst_node]
    congr
    funext i
    exact ih i

/-- Composition of simultaneous substitutions. -/
theorem subst_subst {Z : Type*} (f : X → RankedTree Γ rank Y)
    (g : Y → RankedTree Γ rank Z) (t : RankedTree Γ rank X) :
    (t.subst f).subst g = t.subst (fun x => (f x).subst g) := by
  induction t with
  | var x => rfl
  | node a ch ih =>
    simp only [subst_node]
    congr
    funext i
    exact ih i

/-- Map variables along a function `f : X → Y`. -/
@[expose] def mapVar (f : X → Y) (t : RankedTree Γ rank X) : RankedTree Γ rank Y :=
  t.subst (fun x => var (f x))

@[simp] theorem mapVar_var (f : X → Y) (x : X) :
    (var x : RankedTree Γ rank X).mapVar f = var (f x) := rfl

@[simp] theorem mapVar_node (f : X → Y) (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).mapVar f = node g (fun i => (ch i).mapVar f) := rfl

/-- Embed a ground tree into terms over any variable type `X`. -/
@[expose] def ofGround (t : GroundTree Γ rank) : RankedTree Γ rank X :=
  t.mapVar PEmpty.elim

/-- Size of a substituted tree when variables range over `Fin l`. -/
theorem size_subst_fin {l : ℕ} (f : Fin l → RankedTree Γ rank Y)
    (t : RankedTree Γ rank (Fin l)) :
    (t.subst f).size = t.size + ∑ x : Fin l, t.varOccurrences x * (f x).size := by
  induction t with
  | var y =>
    simp only [subst_var, size_var, zero_add, varOccurrences_var]
    rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hxy
      simp [Ne.symm hxy]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  | node g ch ih =>
    simp only [subst_node, size_node, varOccurrences_node]
    have hsum : ∑ i, (ch i).size + ∑ x : Fin l, (∑ i, (ch i).varOccurrences x) * (f x).size =
        ∑ i, ((ch i).size + ∑ x : Fin l, (ch i).varOccurrences x * (f x).size) := by
      simp_rw [Finset.sum_mul, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl (fun i _ => ih i), ← hsum, Nat.add_assoc]

/-- Set of tree positions `Pos(t) ⊆ ℕ*` as a finite set of lists of natural numbers. -/
@[expose] def positions : RankedTree Γ rank X → Finset (List ℕ)
  | var _ => {[]}
  | node _ ch =>
    insert [] (Finset.univ.biUnion (fun i => (ch i).positions.image (fun v => (i : ℕ) :: v)))

@[simp] theorem positions_var (x : X) :
    (var x : RankedTree Γ rank X).positions = {[]} := rfl

theorem positions_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).positions =
      insert [] (Finset.univ.biUnion (fun i => (ch i).positions.image (fun v => (i : ℕ) :: v))) :=
  rfl

theorem mem_positions_node {g : Γ} {ch : Fin (rank g) → RankedTree Γ rank X} {w : List ℕ} :
    w ∈ (node g ch).positions ↔ w = [] ∨ ∃ (i : Fin (rank g)) (v : List ℕ),
      v ∈ (ch i).positions ∧ (i : ℕ) :: v = w := by
  simp only [positions, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_image, true_and]

@[simp] theorem nil_mem_positions (t : RankedTree Γ rank X) : [] ∈ t.positions := by
  cases t <;> simp [positions]

/-- Total label lookup at a position in a tree. -/
@[expose] def label? : RankedTree Γ rank X → List ℕ → Option (Γ ⊕ X)
  | var x, [] => some (Sum.inr x)
  | var _, _ :: _ => none
  | node g _, [] => some (Sum.inl g)
  | node g ch, i :: v =>
    if h : i < rank g then (ch ⟨i, h⟩).label? v else none

@[simp] theorem label?_nil_var (x : X) :
    (var x : RankedTree Γ rank X).label? [] = some (Sum.inr x) := rfl

@[simp] theorem label?_cons_var (x : X) (i : ℕ) (v : List ℕ) :
    (var x : RankedTree Γ rank X).label? (i :: v) = none := rfl

@[simp] theorem label?_nil_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) :
    (node g ch).label? [] = some (Sum.inl g) := rfl

theorem label?_cons_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) (i : ℕ) (v : List ℕ) :
    (node g ch).label? (i :: v) =
      if h : i < rank g then (ch ⟨i, h⟩).label? v else none := rfl

/-- Subtree of `t` at position `w`, returning `none` outside `Pos(t)`. -/
@[expose] def subtree? : RankedTree Γ rank X → List ℕ → Option (RankedTree Γ rank X)
  | t, [] => some t
  | var _, _ :: _ => none
  | node g ch, i :: v =>
    if h : i < rank g then (ch ⟨i, h⟩).subtree? v else none

@[simp] theorem subtree?_nil (t : RankedTree Γ rank X) : t.subtree? [] = some t := by
  cases t <;> rfl

@[simp] theorem subtree?_cons_var (x : X) (i : ℕ) (v : List ℕ) :
    (var x : RankedTree Γ rank X).subtree? (i :: v) = none := rfl

theorem subtree?_cons_node (g : Γ) (ch : Fin (rank g) → RankedTree Γ rank X) (i : ℕ) (v : List ℕ) :
    (node g ch).subtree? (i :: v) =
      if h : i < rank g then (ch ⟨i, h⟩).subtree? v else none := rfl

/-- A term `t ∈ T_Γ[X_l]` is non-deleting in `l` variables if it contains at least one symbol
from `Γ` and every variable `x_i` (`i : Fin l`) occurs at least once. -/
@[expose] def IsNonDeleting {l : ℕ} (t : RankedTree Γ rank (Fin l)) : Prop :=
  t.hasSymbol ∧ ∀ i : Fin l, 1 ≤ t.varOccurrences i

/-- A term `t ∈ T_Γ[X_l]` is linear in `l` variables if it contains at least one symbol
from `Γ` and every variable `x_i` (`i : Fin l`) occurs exactly once. -/
@[expose] def IsLinear {l : ℕ} (t : RankedTree Γ rank (Fin l)) : Prop :=
  t.hasSymbol ∧ ∀ i : Fin l, t.varOccurrences i = 1

/-- Every linear term is non-deleting. -/
theorem IsLinear.isNonDeleting {l : ℕ} {t : RankedTree Γ rank (Fin l)} (h : t.IsLinear) :
    t.IsNonDeleting :=
  ⟨h.1, fun i => le_of_eq (h.2 i).symm⟩

/-- Every linear term has `varCount = l`. -/
theorem IsLinear.varCount_eq {l : ℕ} {t : RankedTree Γ rank (Fin l)} (h : t.IsLinear) :
    t.varCount = l := by
  have hsum : ∀ (s : RankedTree Γ rank (Fin l)),
      s.varCount = ∑ i : Fin l, s.varOccurrences i := by
    intro s
    induction s with
    | var y =>
      simp only [varCount_var, varOccurrences_var]
      rw [Finset.sum_eq_single y]
      · simp
      · intro i _ hiy
        simp [Ne.symm hiy]
      · intro hy
        exact absurd (Finset.mem_univ y) hy
    | node g ch ih =>
      simp only [varCount_node, varOccurrences_node]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => ih i)
  rw [hsum t]
  simp [h.2]

/-- A non-deleting term has size at least `1`. -/
theorem IsNonDeleting.one_le_size {l : ℕ} {t : RankedTree Γ rank (Fin l)}
    (h : t.IsNonDeleting) : 1 ≤ t.size := by
  cases t with
  | var _ => exact False.elim h.1
  | node g ch =>
    rw [size_node]
    omega

/-- Decidable equality on ranked trees when `Γ` and `X` have decidable equality. -/
def decEq [DecidableEq Γ] [DecidableEq X] :
    (t₁ t₂ : RankedTree Γ rank X) → Decidable (t₁ = t₂)
  | var x₁, var x₂ =>
      if h : x₁ = x₂ then isTrue (h ▸ rfl)
      else isFalse (fun heq => h (var.inj heq))
  | var _, node _ _ => isFalse (fun h => nomatch h)
  | node _ _, var _ => isFalse (fun h => nomatch h)
  | node g₁ ch₁, node g₂ ch₂ =>
      if hg : g₁ = g₂ then by
        subst hg
        have : ∀ i, Decidable (ch₁ i = ch₂ i) := fun i => decEq (ch₁ i) (ch₂ i)
        by_cases hch : ∀ i, ch₁ i = ch₂ i
        · exact isTrue (by congr; funext i; exact hch i)
        · exact isFalse (fun heq => hch (fun i => by cases heq; rfl))
      else isFalse (fun heq => hg (by cases heq; rfl))

instance instDecidableEq [DecidableEq Γ] [DecidableEq X] :
    DecidableEq (RankedTree Γ rank X) :=
  decEq

/-- For a finite ranked alphabet, the set of ground trees of size at most `k` is finite. -/
theorem finite_groundTree_size_le [Finite Γ] (k : ℕ) :
    {t : GroundTree Γ rank | t.size ≤ k}.Finite := by
  let _ : Fintype Γ := Fintype.ofFinite Γ
  induction k with
  | zero =>
    have hempty : {t : GroundTree Γ rank | t.size ≤ 0} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact one_le_size_ground t
    rw [hempty]
    exact Set.finite_empty
  | succ k ih =>
    let _ : Fintype {t : GroundTree Γ rank | t.size ≤ k} := ih.fintype
    let S := Σ g : Γ, Fin (rank g) → {t : GroundTree Γ rank | t.size ≤ k}
    let f : S → GroundTree Γ rank := fun p => node p.1 (fun i => (p.2 i).1)
    refine (Set.finite_range f).subset ?_
    intro t ht
    cases t with
    | var x => exact x.elim
    | node g ch =>
      have hch : ∀ i, (ch i).size ≤ k := by
        intro i
        have hi : (ch i).size ≤ ∑ j, (ch j).size :=
          Finset.single_le_sum (f := fun j => (ch j).size) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
        simp only [Set.mem_ofPred_eq, size_node] at ht
        omega
      exact ⟨⟨g, fun i => ⟨ch i, hch i⟩⟩, rfl⟩

/-- `GroundTree Γ rank` is countable whenever `Γ` is finite. -/
theorem countable_groundTree [Finite Γ] : Countable (GroundTree Γ rank) := by
  have h : (Set.univ : Set (GroundTree Γ rank)) =
      ⋃ k : ℕ, {t : GroundTree Γ rank | t.size ≤ k} := by
    ext t
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨t.size, le_rfl⟩
  have hcount : (Set.univ : Set (GroundTree Γ rank)).Countable := by
    rw [h]
    exact Set.countable_iUnion (fun k => (finite_groundTree_size_le (rank := rank) k).countable)
  exact Set.countable_univ_iff.mp hcount

/-- `subst` depends only on variables that actually occur in the tree. -/
theorem subst_congr [DecidableEq X] {f₁ f₂ : X → RankedTree Γ rank Y}
    {t : RankedTree Γ rank X} (h : ∀ x, 0 < t.varOccurrences x → f₁ x = f₂ x) :
    t.subst f₁ = t.subst f₂ := by
  induction t with
  | var x => exact h x (by simp)
  | node g ch ih =>
    simp only [subst_node]
    congr
    funext i
    refine ih i (fun x hx => h x ?_)
    rw [varOccurrences_node]
    exact lt_of_lt_of_le hx
      (Finset.single_le_sum (f := fun j => (ch j).varOccurrences x)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

/-- Every position in `t.positions` yields a subterm via `subtree?`. -/
theorem exists_subtree?_of_mem_positions (t : RankedTree Γ rank X) {u : List ℕ}
    (hu : u ∈ t.positions) : ∃ s, t.subtree? u = some s := by
  induction t generalizing u with
  | var x =>
    simp only [positions, Finset.mem_singleton] at hu
    exact ⟨.var x, hu ▸ rfl⟩
  | node a ch ih =>
    simp only [positions, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_image, true_and] at hu
    rcases hu with rfl | ⟨i, v, hv, rfl⟩
    · exact ⟨.node a ch, rfl⟩
    · simp only [subtree?, i.isLt, ↓reduceDIte]
      exact ih i hv

/-- Appending a position inside a subterm stays inside `positions`. -/
theorem append_mem_positions_of_subtree? (t : RankedTree Γ rank X) {u : List ℕ} {s : _}
    (hs : t.subtree? u = some s) {v : List ℕ} (hv : v ∈ s.positions) :
    u ++ v ∈ t.positions := by
  induction t generalizing u with
  | var x =>
    cases u with
    | nil =>
      simp only [subtree?_nil, Option.some.injEq] at hs
      exact hs ▸ hv
    | cons _ _ => simp [subtree?] at hs
  | node b chb ihb =>
    cases u with
    | nil =>
      simp only [subtree?_nil, Option.some.injEq] at hs
      exact hs ▸ hv
    | cons k ks =>
      simp only [subtree?] at hs
      split_ifs at hs with hk
      simp only [List.cons_append, positions, Finset.mem_insert, Finset.mem_biUnion,
        Finset.mem_univ, Finset.mem_image, true_and]
      exact Or.inr ⟨⟨k, hk⟩, ks ++ v, ihb ⟨k, hk⟩ hs, rfl⟩

/-- `subtree?` composes over list concatenation. -/
theorem subtree?_append (t : RankedTree Γ rank X) {u : List ℕ} {s : _}
    (hs : t.subtree? u = some s) (v : List ℕ) :
    t.subtree? (u ++ v) = s.subtree? v := by
  induction t generalizing u with
  | var x =>
    cases u with
    | nil =>
      simp only [subtree?_nil, Option.some.injEq] at hs
      exact hs ▸ rfl
    | cons _ _ => simp [subtree?] at hs
  | node b chb ihb =>
    cases u with
    | nil =>
      simp only [subtree?_nil, Option.some.injEq] at hs
      exact hs ▸ rfl
    | cons k ks =>
      simp only [subtree?] at hs
      split_ifs at hs with hk
      simp only [List.cons_append, subtree?, hk, ↓reduceDIte]
      exact ihb ⟨k, hk⟩ hs

/-- Variable occurrences in a subterm are bounded by those in the ambient tree. -/
theorem varOccurrences_le_of_subtree? [DecidableEq X] (t : RankedTree Γ rank X) {u : List ℕ}
    {s : _} (hs : t.subtree? u = some s) (x : X) :
    s.varOccurrences x ≤ t.varOccurrences x := by
  induction t generalizing u with
  | var y =>
    cases u with
    | nil =>
      simp only [subtree?_nil, Option.some.injEq] at hs
      exact hs ▸ le_rfl
    | cons _ _ => simp [subtree?] at hs
  | node b chb ihb =>
    cases u with
    | nil =>
      simp only [subtree?_nil, Option.some.injEq] at hs
      exact hs ▸ le_rfl
    | cons k ks =>
      simp only [subtree?] at hs
      split_ifs at hs with hk
      exact (ihb ⟨k, hk⟩ hs).trans
        (Finset.single_le_sum (f := fun j => (chb j).varOccurrences x)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨k, hk⟩ : Fin (rank b))))

/-- Every ground tree over `Γ` has a `Finite` set of positions (already a `Finset`). -/
theorem positions_nonempty (t : RankedTree Γ rank X) : t.positions.Nonempty :=
  ⟨[], nil_mem_positions t⟩

end RankedTree

/-! ### Tree Homomorphisms -/

/-- A tree homomorphism `h : T_Γ → T_Λ` maps each symbol `g ∈ Γ` of rank `r` to a term
`h(g) ∈ T_Λ[X_r]` and extends inductively by simultaneous substitution. -/
@[ext]
structure TreeHom (Γ : Type u) (rankΓ : Γ → ℕ) (Λ : Type v) (rankΛ : Λ → ℕ) where
  /-- Image term `h(g) ∈ T_Λ[X_{rank g}]` for each symbol `g ∈ Γ`. -/
  toFun : (g : Γ) → RankedTree Λ rankΛ (Fin (rankΓ g))

namespace TreeHom

variable {Γ : Type u} {rankΓ : Γ → ℕ} {Λ : Type v} {rankΛ : Λ → ℕ}
variable {Δ : Type w} {rankΔ : Δ → ℕ}

/-- Evaluation of a tree homomorphism on terms over any variable type `X`. -/
@[expose] def evalTerm (h : TreeHom Γ rankΓ Λ rankΛ) {X : Type*} :
    RankedTree Γ rankΓ X → RankedTree Λ rankΛ X
  | .var x => .var x
  | .node g ch => (h.toFun g).subst (fun i => h.evalTerm (ch i))

/-- Evaluation of a tree homomorphism on ground trees `T_Γ → T_Λ`. -/
@[expose] def eval (h : TreeHom Γ rankΓ Λ rankΛ) : GroundTree Γ rankΓ → GroundTree Λ rankΛ :=
  h.evalTerm

@[simp] theorem evalTerm_var (h : TreeHom Γ rankΓ Λ rankΛ) {X : Type*} (x : X) :
    h.evalTerm (.var x) = .var x := rfl

@[simp] theorem evalTerm_node (h : TreeHom Γ rankΓ Λ rankΛ) {X : Type*} (g : Γ)
    (ch : Fin (rankΓ g) → RankedTree Γ rankΓ X) :
    h.evalTerm (.node g ch) = (h.toFun g).subst (fun i => h.evalTerm (ch i)) := rfl

@[simp] theorem eval_node (h : TreeHom Γ rankΓ Λ rankΛ) (g : Γ)
    (ch : Fin (rankΓ g) → GroundTree Γ rankΓ) :
    h.eval (.node g ch) = (h.toFun g).subst (fun i => h.eval (ch i)) := rfl

/-- Evaluation commutes with simultaneous substitution. -/
theorem evalTerm_subst (h : TreeHom Γ rankΓ Λ rankΛ) {X Y : Type*}
    (f : X → RankedTree Γ rankΓ Y) (t : RankedTree Γ rankΓ X) :
    h.evalTerm (t.subst f) = (h.evalTerm t).subst (fun x => h.evalTerm (f x)) := by
  induction t with
  | var x => rfl
  | node g ch ih =>
    simp only [RankedTree.subst_node, evalTerm_node, RankedTree.subst_subst]
    congr
    funext i
    exact ih i

/-- Identity tree homomorphism. -/
def id (Γ : Type u) (rankΓ : Γ → ℕ) : TreeHom Γ rankΓ Γ rankΓ where
  toFun g := .node g (fun i => .var i)

@[simp] theorem evalTerm_id {X : Type*} (t : RankedTree Γ rankΓ X) :
    (id Γ rankΓ).evalTerm t = t := by
  induction t with
  | var x => rfl
  | node g ch ih =>
    simp only [evalTerm_node, id, RankedTree.subst_node, RankedTree.subst_var]
    congr
    funext i
    exact ih i

@[simp] theorem eval_id (t : GroundTree Γ rankΓ) : (id Γ rankΓ).eval t = t :=
  evalTerm_id t

/-- Composition of tree homomorphisms. -/
def comp (h₂ : TreeHom Λ rankΛ Δ rankΔ) (h₁ : TreeHom Γ rankΓ Λ rankΛ) :
    TreeHom Γ rankΓ Δ rankΔ where
  toFun g := h₂.evalTerm (h₁.toFun g)

@[simp] theorem evalTerm_comp (h₂ : TreeHom Λ rankΛ Δ rankΔ) (h₁ : TreeHom Γ rankΓ Λ rankΛ)
    {X : Type*} (t : RankedTree Γ rankΓ X) :
    (h₂.comp h₁).evalTerm t = h₂.evalTerm (h₁.evalTerm t) := by
  induction t with
  | var x => rfl
  | node g ch ih =>
    simp only [evalTerm_node, comp, evalTerm_subst]
    congr
    funext i
    exact ih i

@[simp] theorem eval_comp (h₂ : TreeHom Λ rankΛ Δ rankΔ) (h₁ : TreeHom Γ rankΓ Λ rankΛ)
    (t : GroundTree Γ rankΓ) :
    (h₂.comp h₁).eval t = h₂.eval (h₁.eval t) :=
  evalTerm_comp h₂ h₁ t

/-- A tree homomorphism is non-deleting if every `h(g)` is non-deleting in `rank g` variables. -/
@[expose] def IsNonDeleting (h : TreeHom Γ rankΓ Λ rankΛ) : Prop :=
  ∀ g : Γ, (h.toFun g).IsNonDeleting

/-- A tree homomorphism is linear if every `h(g)` is linear in `rank g` variables. -/
@[expose] def IsLinear (h : TreeHom Γ rankΓ Λ rankΛ) : Prop :=
  ∀ g : Γ, (h.toFun g).IsLinear

/-- Every linear tree homomorphism is non-deleting. -/
theorem IsLinear.isNonDeleting {h : TreeHom Γ rankΓ Λ rankΛ} (hh : h.IsLinear) :
    h.IsNonDeleting :=
  fun g => (hh g).isNonDeleting

/-- Non-deleting tree homomorphisms do not decrease tree size. -/
theorem size_le_eval_of_isNonDeleting {h : TreeHom Γ rankΓ Λ rankΛ} (hh : h.IsNonDeleting)
    (t : GroundTree Γ rankΓ) : t.size ≤ (h.eval t).size := by
  induction t with
  | var x => exact x.elim
  | node g ch ih =>
    rw [eval_node, RankedTree.size_subst_fin, RankedTree.size_node]
    have h1 : 1 ≤ (h.toFun g).size := (hh g).one_le_size
    have h2 : ∑ i : Fin (rankΓ g), (ch i).size ≤
        ∑ i : Fin (rankΓ g), (h.toFun g).varOccurrences i * (h.eval (ch i)).size := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hocc : 1 ≤ (h.toFun g).varOccurrences i := (hh g).2 i
      calc (ch i).size
          = 1 * (ch i).size := (Nat.one_mul _).symm
        _ ≤ (h.toFun g).varOccurrences i * (h.eval (ch i)).size :=
          Nat.mul_le_mul hocc (ih i)
    omega

/-- Every non-deleting tree homomorphism from a finite ranked alphabet has finite fibers. -/
theorem finite_preimage_of_isNonDeleting [Finite Γ] {h : TreeHom Γ rankΓ Λ rankΛ}
    (hh : h.IsNonDeleting) (t : GroundTree Λ rankΛ) :
    (h.eval ⁻¹' {t}).Finite := by
  refine (RankedTree.finite_groundTree_size_le (rank := rankΓ) t.size).subset ?_
  intro t' ht'
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ht'
  simp only [Set.mem_ofPred_eq]
  rw [← ht']
  exact size_le_eval_of_isNonDeleting hh t'

end TreeHom

/-! ### Generic Word-to-Tree Encoding -/

/-- The ranked alphabet `Σ_#^r` extending `Σ` with a nullary end-marker `none` (`#`) and giving
every letter `some a` rank `r`. -/
abbrev wordRank {Alph : Type u} (r : ℕ) : Option Alph → ℕ
  | none => 0
  | some _ => r

/-- Generic word-to-tree map `h^r : Σ* → T_{Σ_#^r}` mapping `ε ↦ #` and
`a :: v ↦ a(t_v^r, ..., t_v^r)`. -/
@[expose] def genericTree {Alph : Type u} (r : ℕ) :
    List Alph → GroundTree (Option Alph) (wordRank r)
  | [] => .node none Fin.elim0
  | a :: v => .node (some a) (fun _ => genericTree r v)

@[simp] theorem genericTree_nil {Alph : Type u} (r : ℕ) :
    genericTree r ([] : List Alph) = .node none Fin.elim0 := rfl

@[simp] theorem genericTree_cons {Alph : Type u} (r : ℕ) (a : Alph) (v : List Alph) :
    genericTree r (a :: v) = .node (some a) (fun _ => genericTree r v) := rfl

/-- Inverse of `genericTree 1`, reading a unary tree back into a word. -/
def treeToWord {Alph : Type u} : GroundTree (Option Alph) (wordRank 1) → List Alph
  | .var x => x.elim
  | .node none _ => []
  | .node (some a) ch => a :: treeToWord (ch ⟨0, Nat.zero_lt_one⟩)

@[simp] theorem treeToWord_genericTree {Alph : Type u} (w : List Alph) :
    treeToWord (genericTree 1 w) = w := by
  induction w with
  | nil => rfl
  | cons a v ih =>
    simp [genericTree, treeToWord, ih]

@[simp] theorem genericTree_treeToWord {Alph : Type u} (t : GroundTree (Option Alph) (wordRank 1)) :
    genericTree 1 (treeToWord t) = t := by
  induction t with
  | var x => exact x.elim
  | node g ch ih =>
    cases g with
    | none =>
      simp only [treeToWord, genericTree]
      congr
      funext i
      exact Fin.elim0 i
    | some a =>
      simp only [treeToWord, genericTree]
      congr
      funext i
      have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.eq_zero i
      rw [hi]
      exact ih ⟨0, Nat.zero_lt_one⟩

/-- Canonical bijection between words `List Σ` and unary trees `T_{Σ_#^1}`. -/
def wordTreeEquiv (Alph : Type u) : List Alph ≃ GroundTree (Option Alph) (wordRank 1) where
  toFun := genericTree 1
  invFun := treeToWord
  left_inv := treeToWord_genericTree
  right_inv := genericTree_treeToWord

/-- A word-to-tree homomorphism `h : Σ* → T_Γ` is a tree homomorphism from `Σ_#^1` to `Γ`. -/
abbrev WordTreeHom (Alph : Type u) (Γ : Type v) (rank : Γ → ℕ) :=
  TreeHom (Option Alph) (wordRank 1) Γ rank

/-- Evaluate a word-to-tree homomorphism on a word `w ∈ Σ*`. -/
@[expose] def WordTreeHom.evalWord {Alph : Type u} {Γ : Type v} {rank : Γ → ℕ}
    (h : WordTreeHom Alph Γ rank) (w : List Alph) : GroundTree Γ rank :=
  h.eval (genericTree 1 w)

theorem WordTreeHom.evalWord_eq {Alph : Type u} {Γ : Type v} {rank : Γ → ℕ}
    (h : WordTreeHom Alph Γ rank) (w : List Alph) :
    h.evalWord w = h.eval (genericTree 1 w) := rfl

/-- The generic tree homomorphism `h^r : Σ* → T_{Σ_#^r}` as a `WordTreeHom`. -/
def genericTreeHom (Alph : Type u) (r : ℕ) : WordTreeHom Alph (Option Alph) (wordRank r) where
  toFun
    | none => .node none Fin.elim0
    | some a => .node (some a) (fun _ => .var ⟨0, Nat.zero_lt_one⟩)

@[simp] theorem genericTreeHom_evalWord {Alph : Type u} (r : ℕ) (w : List Alph) :
    (genericTreeHom Alph r).evalWord w = genericTree r w := by
  induction w with
  | nil =>
    dsimp [WordTreeHom.evalWord, genericTree, TreeHom.eval, TreeHom.evalTerm, genericTreeHom,
      RankedTree.subst]
    congr
    funext i
    exact Fin.elim0 i
  | cons a v ih =>
    rw [WordTreeHom.evalWord, genericTree_cons, TreeHom.eval_node]
    simp only [genericTreeHom, RankedTree.subst_node, RankedTree.subst_var, genericTree_cons]
    congr
    funext i
    exact ih

/-- Helper converting a word into a unary tree context with hole `x_0`. -/
def wordHomToTreeHomGo {Alph : Type v} :
    List Alph → RankedTree (Option Alph) (wordRank 1) (Fin 1)
  | [] => .var ⟨0, Nat.zero_lt_one⟩
  | b :: bs => .node (some b) (fun _ => wordHomToTreeHomGo bs)

/-- Lift a word homomorphism `f : Λ* → Σ*` (specified by `f : Λ → List Σ`) to a tree
homomorphism `T_{Λ_#^1} → T_{Alph_#^1}`. -/
def wordHomToTreeHom {Λ : Type u} {Alph : Type v} (f : Λ → List Alph) :
    WordTreeHom Λ (Option Alph) (wordRank 1) where
  toFun
    | none => .node none Fin.elim0
    | some a => wordHomToTreeHomGo (f a)

private theorem wordHomToTreeHomGo_subst {Alph : Type v} (u v : List Alph) :
    (wordHomToTreeHomGo u).subst (fun _ => genericTree 1 v) = genericTree 1 (u ++ v) := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    simp only [wordHomToTreeHomGo, RankedTree.subst_node, List.cons_append, genericTree_cons]
    congr
    funext i
    exact ih

@[simp] theorem wordHomToTreeHom_evalWord {Λ : Type u} {Alph : Type v} (f : Λ → List Alph)
    (w : List Λ) :
    (wordHomToTreeHom f).evalWord w = genericTree 1 (w.flatMap f) := by
  induction w with
  | nil =>
    dsimp [WordTreeHom.evalWord, genericTree, TreeHom.eval, TreeHom.evalTerm, wordHomToTreeHom,
      RankedTree.subst]
    congr
    funext i
    exact Fin.elim0 i
  | cons a v ih =>
    simp only [WordTreeHom.evalWord, genericTree_cons, TreeHom.eval_node, List.flatMap_cons]
    change (wordHomToTreeHomGo (f a)).subst (fun _ => (wordHomToTreeHom f).evalWord v) = _
    rw [ih, wordHomToTreeHomGo_subst]

/-! ### Bottom-Up Finite Tree Automata and Regular Tree Languages -/

/-- A deterministic bottom-up finite tree automaton (DFTA) over ranked alphabet `(Γ, rank)`
with state type `Q`. -/
@[ext]
structure DFTA (Q : Type w) (Γ : Type u) (rank : Γ → ℕ) where
  /-- Bottom-up transition function `δ_g : Q^{rank g} → Q`. -/
  δ : (g : Γ) → (Fin (rank g) → Q) → Q
  /-- Set of accepting (root) states. -/
  final : Set Q

namespace DFTA

variable {Q : Type w} {Q' : Type*} {Γ : Type u} {rank : Γ → ℕ}

/-- Run a DFTA bottom-up on a term `t ∈ T_Γ[X]` given leaf states `env : X → Q`. -/
@[expose] def runTerm (A : DFTA Q Γ rank) {X : Type*} (env : X → Q) : RankedTree Γ rank X → Q
  | .var x => env x
  | .node g ch => A.δ g (fun i => A.runTerm env (ch i))

/-- Run a DFTA bottom-up on a ground tree `t ∈ T_Γ`. -/
@[expose] def run (A : DFTA Q Γ rank) : GroundTree Γ rank → Q :=
  A.runTerm PEmpty.elim

@[simp] theorem runTerm_var (A : DFTA Q Γ rank) {X : Type*} (env : X → Q) (x : X) :
    A.runTerm env (.var x) = env x := rfl

@[simp] theorem runTerm_node (A : DFTA Q Γ rank) {X : Type*} (env : X → Q) (g : Γ)
    (ch : Fin (rank g) → RankedTree Γ rank X) :
    A.runTerm env (.node g ch) = A.δ g (fun i => A.runTerm env (ch i)) := rfl

@[simp] theorem run_node (A : DFTA Q Γ rank) (g : Γ) (ch : Fin (rank g) → GroundTree Γ rank) :
    A.run (.node g ch) = A.δ g (fun i => A.run (ch i)) := rfl

/-- `runTerm` commutes with simultaneous substitution. -/
theorem runTerm_subst (A : DFTA Q Γ rank) {X Y : Type*} (env : Y → Q)
    (f : X → RankedTree Γ rank Y) (t : RankedTree Γ rank X) :
    A.runTerm env (t.subst f) = A.runTerm (fun x => A.runTerm env (f x)) t := by
  induction t with
  | var x => rfl
  | node g ch ih =>
    simp only [RankedTree.subst_node, runTerm_node]
    congr
    funext i
    exact ih i

/-- The tree language recognized by a DFTA. -/
@[expose] def language (A : DFTA Q Γ rank) : Set (GroundTree Γ rank) :=
  {t | A.run t ∈ A.final}

@[simp] theorem mem_language_iff (A : DFTA Q Γ rank) (t : GroundTree Γ rank) :
    t ∈ A.language ↔ A.run t ∈ A.final := Iff.rfl

/-- Transfer a DFTA across an equivalence of state types. -/
def mapStates (A : DFTA Q Γ rank) (e : Q ≃ Q') : DFTA Q' Γ rank where
  δ g q := e (A.δ g (fun i => e.symm (q i)))
  final := e.symm ⁻¹' A.final

@[simp] theorem run_mapStates (A : DFTA Q Γ rank) (e : Q ≃ Q') (t : GroundTree Γ rank) :
    (A.mapStates e).run t = e (A.run t) := by
  induction t with
  | var x => exact x.elim
  | node g ch ih =>
    rw [run_node, run_node]
    have hδ : (A.mapStates e).δ g = fun q => e (A.δ g (fun i => e.symm (q i))) := rfl
    rw [hδ]
    simp [ih]

@[simp] theorem language_mapStates (A : DFTA Q Γ rank) (e : Q ≃ Q') :
    (A.mapStates e).language = A.language := by
  ext t
  rw [language, language]
  simp only [Set.mem_ofPred_eq, run_mapStates]
  have hf : (A.mapStates e).final = e.symm ⁻¹' A.final := rfl
  rw [hf]
  simp

/-- Complement DFTA. -/
@[expose] def compl (A : DFTA Q Γ rank) : DFTA Q Γ rank where
  δ := A.δ
  final := A.finalᶜ

@[simp] theorem language_compl (A : DFTA Q Γ rank) : A.compl.language = A.languageᶜ := by
  have hrun : ∀ t, A.compl.run t = A.run t := by
    intro t; induction t with
    | var x => exact x.elim
    | node g ch ih =>
      rw [run_node, run_node]
      have hδ : A.compl.δ = A.δ := rfl
      rw [hδ]; congr; funext i; exact ih i
  ext t
  rw [language, Set.mem_compl_iff, language]
  simp only [Set.mem_ofPred_eq, hrun]
  rfl

/-- Product DFTA recognizing the intersection of two languages. -/
def prod (A : DFTA Q Γ rank) (B : DFTA Q' Γ rank) : DFTA (Q × Q') Γ rank where
  δ g q := (A.δ g (fun i => (q i).1), B.δ g (fun i => (q i).2))
  final := A.final ×ˢ B.final

@[simp] theorem run_prod (A : DFTA Q Γ rank) (B : DFTA Q' Γ rank) (t : GroundTree Γ rank) :
    (A.prod B).run t = (A.run t, B.run t) := by
  induction t with
  | var x => exact x.elim
  | node g ch ih =>
    rw [run_node, run_node, run_node]
    have hδ : (A.prod B).δ g = fun q => (A.δ g (fun i => (q i).1), B.δ g (fun i => (q i).2)) := rfl
    rw [hδ]
    simp [ih]

@[simp] theorem language_prod (A : DFTA Q Γ rank) (B : DFTA Q' Γ rank) :
    (A.prod B).language = A.language ∩ B.language := by
  ext t
  rw [language, Set.mem_inter_iff, language, language]
  simp only [Set.mem_ofPred_eq, run_prod]
  have hf : (A.prod B).final = A.final ×ˢ B.final := rfl
  rw [hf]
  rfl

/-- Pullback of a DFTA along a tree homomorphism. -/
def pullback {Λ : Type v} {rankΛ : Λ → ℕ} (A : DFTA Q Γ rank)
    (h : TreeHom Λ rankΛ Γ rank) : DFTA Q Λ rankΛ where
  δ g q := A.runTerm q (h.toFun g)
  final := A.final

@[simp] theorem run_pullback {Λ : Type v} {rankΛ : Λ → ℕ} (A : DFTA Q Γ rank)
    (h : TreeHom Λ rankΛ Γ rank) (t : GroundTree Λ rankΛ) :
    (A.pullback h).run t = A.run (h.eval t) := by
  induction t with
  | var x => exact x.elim
  | node g ch ih =>
    rw [run_node, TreeHom.eval_node]
    dsimp only [run]
    rw [runTerm_subst]
    have hδ : (A.pullback h).δ g = fun q => A.runTerm q (h.toFun g) := rfl
    rw [hδ]
    congr 1
    funext i
    exact ih i

@[simp] theorem language_pullback {Λ : Type v} {rankΛ : Λ → ℕ} (A : DFTA Q Γ rank)
    (h : TreeHom Λ rankΛ Γ rank) :
    (A.pullback h).language = h.eval ⁻¹' A.language := by
  ext t
  rw [language, Set.mem_preimage, language]
  simp only [Set.mem_ofPred_eq, run_pullback]
  rfl

end DFTA

/-- A nondeterministic bottom-up finite tree automaton (NFTA) over `(Γ, rank)`. -/
@[ext]
structure NFTA (Q : Type w) (Γ : Type u) (rank : Γ → ℕ) where
  /-- Nondeterministic transition relation `δ g p̄ q`. -/
  δ : (g : Γ) → (Fin (rank g) → Q) → Q → Prop
  /-- Accepting root states. -/
  final : Set Q

namespace NFTA

variable {Q : Type w} {Γ : Type u} {rank : Γ → ℕ}

/-- Reachability of state `q` at the root of ground tree `t` in an NFTA. -/
inductive Reaches (A : NFTA Q Γ rank) : GroundTree Γ rank → Q → Prop where
  | node (g : Γ) (ch : Fin (rank g) → GroundTree Γ rank) (p : Fin (rank g) → Q) (q : Q)
      (hch : ∀ i, A.Reaches (ch i) (p i)) (hδ : A.δ g p q) :
      A.Reaches (.node g ch) q

/-- The tree language recognized by an NFTA. -/
def language (A : NFTA Q Γ rank) : Set (GroundTree Γ rank) :=
  {t | ∃ q ∈ A.final, A.Reaches t q}

/-- Subset construction determinizing an NFTA into an equivalent DFTA on `Set Q`. -/
def determinize (A : NFTA Q Γ rank) : DFTA (Set Q) Γ rank where
  δ g S := {q | ∃ p : Fin (rank g) → Q, (∀ i, p i ∈ S i) ∧ A.δ g p q}
  final := {S | ∃ q ∈ A.final, q ∈ S}

theorem mem_run_determinize_iff (A : NFTA Q Γ rank) (t : GroundTree Γ rank) (q : Q) :
    q ∈ A.determinize.run t ↔ A.Reaches t q := by
  induction t generalizing q with
  | var x => exact x.elim
  | node g ch ih =>
    constructor
    · rintro ⟨p, hp, hδ⟩
      exact Reaches.node g ch p q (fun i => (ih i (p i)).mp (hp i)) hδ
    · intro hr
      cases hr with
      | node _ _ p _ hch hδ =>
        exact ⟨p, fun i => (ih i (p i)).mpr (hch i), hδ⟩

@[simp] theorem language_determinize (A : NFTA Q Γ rank) :
    A.determinize.language = A.language := by
  ext t
  rw [DFTA.language, language]
  have hf : A.determinize.final = {S | ∃ q ∈ A.final, q ∈ S} := rfl
  rw [hf]
  simp [mem_run_determinize_iff]

end NFTA

/-- A tree language `L ⊆ T_Γ` is regular (recognizable) if it is recognized by some DFTA
with a finite state space. -/
@[expose] def IsRegularTreeLang {Γ : Type u} {rank : Γ → ℕ} (L : Set (GroundTree Γ rank)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (A : DFTA Q Γ rank), A.language = L

namespace IsRegularTreeLang

variable {Γ : Type u} {rank : Γ → ℕ}

/-- Any DFTA with a finite state space in any universe recognizes a regular tree language. -/
theorem of_dfta {Q : Type w} [Finite Q] (A : DFTA Q Γ rank) :
    IsRegularTreeLang A.language := by
  have := Fintype.ofFinite Q
  exact ⟨Fin (Fintype.card Q), inferInstance, A.mapStates (Fintype.equivFin Q),
    A.language_mapStates _⟩

/-- Any NFTA with a finite state space in any universe recognizes a regular tree language. -/
theorem of_nfta {Q : Type w} [Finite Q] (A : NFTA Q Γ rank) :
    IsRegularTreeLang A.language := by
  have := Fintype.ofFinite Q
  rw [← A.language_determinize]
  exact of_dfta A.determinize

/-- Regular tree languages are characterized by finite NFTAs. -/
theorem iff_nfta (L : Set (GroundTree Γ rank)) :
    IsRegularTreeLang L ↔ ∃ (Q : Type) (_ : Fintype Q) (A : NFTA Q Γ rank), A.language = L := by
  constructor
  · rintro ⟨Q, hQ, A, rfl⟩
    let B : NFTA Q Γ rank :=
      { δ := fun g p q => A.δ g p = q
        final := A.final }
    refine ⟨Q, hQ, B, ?_⟩
    have hreach : ∀ t q, B.Reaches t q ↔ A.run t = q := by
      intro t
      induction t with
      | var x => exact x.elim
      | node g ch ih =>
        intro q
        constructor
        · intro hr
          cases hr with
          | node _ _ p _ hch hδ =>
            rw [DFTA.run_node, ← hδ]
            congr
            funext i
            exact (ih i (p i)).mp (hch i)
        · intro hq
          exact NFTA.Reaches.node g ch (fun i => A.run (ch i)) q
            (fun i => (ih i _).mpr rfl) hq
    ext t
    simp [NFTA.language, DFTA.language, B, hreach]
  · rintro ⟨Q, hQ, A, rfl⟩
    exact of_nfta A

/-- The empty tree language is regular. -/
theorem empty : IsRegularTreeLang (∅ : Set (GroundTree Γ rank)) := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), ∅⟩, ?_⟩
  ext t
  simp [DFTA.language]

/-- The universal tree language is regular. -/
theorem univ : IsRegularTreeLang (Set.univ : Set (GroundTree Γ rank)) := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), Set.univ⟩, ?_⟩
  ext t
  simp [DFTA.language]

/-- Regular tree languages are closed under complement. -/
theorem compl {L : Set (GroundTree Γ rank)} (hL : IsRegularTreeLang L) :
    IsRegularTreeLang Lᶜ := by
  obtain ⟨Q, _, A, rfl⟩ := hL
  exact ⟨Q, inferInstance, A.compl, A.language_compl⟩

/-- Regular tree languages are closed under intersection. -/
theorem inter {L₁ L₂ : Set (GroundTree Γ rank)} (h₁ : IsRegularTreeLang L₁)
    (h₂ : IsRegularTreeLang L₂) : IsRegularTreeLang (L₁ ∩ L₂) := by
  obtain ⟨Q₁, _, A₁, rfl⟩ := h₁
  obtain ⟨Q₂, _, A₂, rfl⟩ := h₂
  exact ⟨Q₁ × Q₂, inferInstance, A₁.prod A₂, A₁.language_prod A₂⟩

/-- Regular tree languages are closed under union. -/
theorem union {L₁ L₂ : Set (GroundTree Γ rank)} (h₁ : IsRegularTreeLang L₁)
    (h₂ : IsRegularTreeLang L₂) : IsRegularTreeLang (L₁ ∪ L₂) := by
  have h : L₁ ∪ L₂ = (L₁ᶜ ∩ L₂ᶜ)ᶜ := by simp
  rw [h]
  exact (h₁.compl.inter h₂.compl).compl

/-- Regular tree languages are closed under finite intersections. -/
theorem biInter {ι : Type*} (s : Finset ι) (L : ι → Set (GroundTree Γ rank))
    (h : ∀ i ∈ s, IsRegularTreeLang (L i)) :
    IsRegularTreeLang (⋂ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using univ
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self _ _)).inter
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Regular tree languages are closed under finite unions. -/
theorem biUnion {ι : Type*} (s : Finset ι) (L : ι → Set (GroundTree Γ rank))
    (h : ∀ i ∈ s, IsRegularTreeLang (L i)) :
    IsRegularTreeLang (⋃ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using empty
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self _ _)).union
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Regular tree languages are closed under inverse tree homomorphisms. -/
theorem preimage_treeHom {Λ : Type v} {rankΛ : Λ → ℕ}
    (h : TreeHom Λ rankΛ Γ rank) {L : Set (GroundTree Γ rank)} (hL : IsRegularTreeLang L) :
    IsRegularTreeLang (h.eval ⁻¹' L) := by
  obtain ⟨Q, _, A, rfl⟩ := hL
  exact ⟨Q, inferInstance, A.pullback h, A.language_pullback h⟩

/-- A regular tree language is closed under any linear tree homomorphism. -/
theorem image_of_isLinear {Λ : Type v} {rankΛ : Λ → ℕ} [Finite Λ]
    {h : TreeHom Λ rankΛ Γ rank} (hh : h.IsLinear)
    {L : Set (GroundTree Λ rankΛ)} (hL : IsRegularTreeLang L) :
    IsRegularTreeLang (h.eval '' L) := by
  classical
  have := Fintype.ofFinite Λ
  by_cases hneG : Nonempty (GroundTree Λ rankΛ)
  swap
  · have hempty : L = ∅ := Set.eq_empty_of_forall_notMem (fun t _ => hneG ⟨t⟩)
    rw [hempty, Set.image_empty]
    exact empty
  obtain ⟨tDefault⟩ := hneG
  obtain ⟨Q, _, A, rfl⟩ := hL
  let Pos (g : Λ) := {w : List ℕ // w ∈ (h.toFun g).positions}
  let St : Type v := Q ⊕ (Σ g : Λ, Pos g × (Fin (rankΛ g) → Q))
  have : ∀ g : Λ, Fintype (Pos g) := fun _ => inferInstance
  let subterm (g : Λ) (w : Pos g) : RankedTree Γ rank (Fin (rankΛ g)) :=
    (RankedTree.exists_subtree?_of_mem_positions (h.toFun g) w.2).choose
  have hsubterm (g : Λ) (w : Pos g) : (h.toFun g).subtree? w.1 = some (subterm g w) :=
    (RankedTree.exists_subtree?_of_mem_positions (h.toFun g) w.2).choose_spec
  let δ : (a : Γ) → (Fin (rank a) → St) → St → Prop := fun a chSt s =>
    match s with
    | .inl q =>
      ∃ (g : Λ) (p : Fin (rankΛ g) → Q), A.δ g p = q ∧
        match h.toFun g with
        | .var _ => False
        | .node a' ch' =>
          ∃ ha : a' = a, ∀ j : Fin (rank a),
            match ch' (ha ▸ j) with
            | .var i => chSt j = .inl (p i)
            | .node _ _ =>
              ∃ (w : Pos g), subterm g w = ch' (ha ▸ j) ∧ chSt j = .inr ⟨g, w, p⟩
    | .inr ⟨g, w, p⟩ =>
      match subterm g w with
      | .var _ => False
      | .node a' ch' =>
        ∃ ha : a' = a, ∀ j : Fin (rank a),
          match ch' (ha ▸ j) with
          | .var i => chSt j = .inl (p i)
          | .node _ _ =>
            ∃ (w' : Pos g), subterm g w' = ch' (ha ▸ j) ∧ chSt j = .inr ⟨g, w', p⟩
  let B : NFTA St Γ rank :=
    { δ := δ
      final := {s | ∃ q ∈ A.final, s = .inl q} }
  have hchild_pos : ∀ (g : Λ) (w : Pos g) (a' : Γ) (ch' : Fin (rank a') → _)
      (_ : subterm g w = .node a' ch') (j : Fin (rank a')),
      ∃ w' : Pos g, subterm g w' = ch' j := by
    intro g w a' ch' hsw j
    have hpos : [(j : ℕ)] ∈ (subterm g w).positions := by
      rw [hsw]
      simp only [RankedTree.positions, Finset.mem_insert, Finset.mem_biUnion,
        Finset.mem_univ, Finset.mem_image, true_and]
      exact Or.inr ⟨j, [], RankedTree.nil_mem_positions _, rfl⟩
    have hmem := RankedTree.append_mem_positions_of_subtree? (h.toFun g) (hsubterm g w) hpos
    refine ⟨⟨w.1 ++ [(j : ℕ)], hmem⟩, ?_⟩
    have hsub' := hsubterm g ⟨w.1 ++ [(j : ℕ)], hmem⟩
    rw [RankedTree.subtree?_append (h.toFun g) (hsubterm g w) [(j : ℕ)], hsw] at hsub'
    simp only [RankedTree.subtree?, j.isLt, ↓reduceDIte, RankedTree.subtree?_nil,
      Option.some.injEq] at hsub'
    exact hsub'.symm
  let Matches (t : GroundTree Γ rank) : St → Prop
    | .inl q => ∃ t₀ : GroundTree Λ rankΛ, A.run t₀ = q ∧ h.eval t₀ = t
    | .inr ⟨g, w, p⟩ =>
      ∃ sub : Fin (rankΛ g) → GroundTree Λ rankΛ,
        (∀ i, 0 < (subterm g w).varOccurrences i → A.run (sub i) = p i) ∧
        (subterm g w).subst (fun i => h.eval (sub i)) = t
  have hbuild_children : ∀ (g : Λ) (p : Fin (rankΛ g) → Q) (a' : Γ)
      (ch' : Fin (rank a') → RankedTree Γ rank (Fin (rankΛ g)))
      (ch : Fin (rank a') → GroundTree Γ rank)
      (hdisj : ∀ (i : Fin (rankΛ g)) (j₁ j₂ : Fin (rank a')),
        0 < (ch' j₁).varOccurrences i → 0 < (ch' j₂).varOccurrences i → j₁ = j₂)
      (hmatch : ∀ j : Fin (rank a'), ∃ sub : Fin (rankΛ g) → GroundTree Λ rankΛ,
        (∀ i, 0 < (ch' j).varOccurrences i → A.run (sub i) = p i) ∧
        (ch' j).subst (fun i => h.eval (sub i)) = ch j),
      ∃ sub : Fin (rankΛ g) → GroundTree Λ rankΛ,
        (∀ i, 0 < (RankedTree.node a' ch').varOccurrences i → A.run (sub i) = p i) ∧
        ∀ j, (ch' j).subst (fun i => h.eval (sub i)) = ch j := by
    intro g p a' ch' ch hdisj hmatch
    let sub_j (j : Fin (rank a')) := (hmatch j).choose
    have hsub_j (j : Fin (rank a')) := (hmatch j).choose_spec
    let sub (i : Fin (rankΛ g)) : GroundTree Λ rankΛ :=
      if hji : ∃ j, 0 < (ch' j).varOccurrences i then sub_j hji.choose i else tDefault
    refine ⟨sub, ?_, ?_⟩
    · intro i hi
      rw [RankedTree.varOccurrences_node] at hi
      have hex : ∃ j, 0 < (ch' j).varOccurrences i := by
        by_contra hall
        push Not at hall
        have hzero : ∀ j, (ch' j).varOccurrences i = 0 := fun j => Nat.eq_zero_of_le_zero (hall j)
        simp [hzero] at hi
      simp only [sub, hex, ↓reduceDIte]
      exact (hsub_j hex.choose).1 i hex.choose_spec
    · intro j
      rw [RankedTree.subst_congr (f₂ := fun i => h.eval (sub_j j i))]
      · exact (hsub_j j).2
      · intro i hi
        have hex : ∃ k, 0 < (ch' k).varOccurrences i := ⟨j, hi⟩
        simp only [sub, hex, ↓reduceDIte]
        rw [hdisj i hex.choose j hex.choose_spec hi]
  have hsound : ∀ t s, B.Reaches t s → Matches t s := by
    intro t s hr
    induction hr with
    | node a ch chSt s hch hδ ih =>
      cases s with
      | inl q =>
        rcases hδ with ⟨g, p, hpq, hfg⟩
        cases hto : h.toFun g with
        | var _ => rw [hto] at hfg; exact False.elim hfg
        | node a' ch' =>
          rw [hto] at hfg
          rcases hfg with ⟨rfl, hchild⟩
          have hdisj : ∀ (i : Fin (rankΛ g)) (j₁ j₂ : Fin (rank a')),
              0 < (ch' j₁).varOccurrences i → 0 < (ch' j₂).varOccurrences i → j₁ = j₂ := by
            intro i j₁ j₂ h₁ h₂
            by_contra hne
            have hlin := (hh g).2 i
            rw [hto, RankedTree.varOccurrences_node] at hlin
            have hsum := Finset.add_le_sum (f := fun j => (ch' j).varOccurrences i)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₁) (Finset.mem_univ j₂) hne
            omega
          have hmatch : ∀ j : Fin (rank a'), ∃ sub : Fin (rankΛ g) → GroundTree Λ rankΛ,
              (∀ i, 0 < (ch' j).varOccurrences i → A.run (sub i) = p i) ∧
              (ch' j).subst (fun i => h.eval (sub i)) = ch j := by
            intro j
            specialize hchild j
            specialize ih j
            cases hchj : ch' j with
            | var i =>
              rw [hchj] at hchild
              rw [hchild] at ih
              obtain ⟨t₀, ht₀, hteq⟩ := ih
              refine ⟨fun _ => t₀, ?_, by simp [hteq]⟩
              intro k hk
              simp only [RankedTree.varOccurrences_var] at hk
              split_ifs at hk with hki
              · exact hki ▸ ht₀
              · omega
            | node b chb =>
              rw [hchj] at hchild
              rcases hchild with ⟨w', hw', hst⟩
              rw [hst] at ih
              obtain ⟨sub, hsub, hsubeq⟩ := ih
              rw [hw'] at hsub hsubeq
              exact ⟨sub, hsub, hsubeq⟩
          obtain ⟨sub, hrun, hsubst⟩ := hbuild_children g p a' ch' ch hdisj hmatch
          have hrun_all : ∀ i, A.run (sub i) = p i := fun i =>
            hrun i (by rw [← hto, (hh g).2 i]; exact Nat.zero_lt_one)
          refine ⟨.node g sub, ?_, ?_⟩
          · simp only [DFTA.run_node, hrun_all, hpq]
          · simp only [TreeHom.eval_node, hto, RankedTree.subst_node, hsubst]
      | inr x =>
        rcases x with ⟨g, w, p⟩
        change (match subterm g w with
          | .var _ => False
          | .node a' ch' => ∃ ha : a' = a, ∀ j : Fin (rank a),
              match ch' (ha ▸ j) with
              | .var i => chSt j = .inl (p i)
              | .node _ _ => ∃ w' : Pos g, subterm g w' = ch' (ha ▸ j) ∧
                  chSt j = .inr ⟨g, w', p⟩) at hδ
        cases hsw : subterm g w with
        | var _ => rw [hsw] at hδ; exact False.elim hδ
        | node a' ch' =>
          rw [hsw] at hδ
          rcases hδ with ⟨rfl, hchild⟩
          have hdisj : ∀ (i : Fin (rankΛ g)) (j₁ j₂ : Fin (rank a')),
              0 < (ch' j₁).varOccurrences i → 0 < (ch' j₂).varOccurrences i → j₁ = j₂ := by
            intro i j₁ j₂ h₁ h₂
            by_contra hne
            have hsum_le : (ch' j₁).varOccurrences i + (ch' j₂).varOccurrences i ≤
                (subterm g w).varOccurrences i := by
              rw [hsw, RankedTree.varOccurrences_node]
              exact Finset.add_le_sum (f := fun j => (ch' j).varOccurrences i)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ _) (Finset.mem_univ _) hne
            have h1 := RankedTree.varOccurrences_le_of_subtree? (h.toFun g) (hsubterm g w) i
            have hlin := (hh g).2 i
            omega
          have hmatch : ∀ j : Fin (rank a'), ∃ sub : Fin (rankΛ g) → GroundTree Λ rankΛ,
              (∀ i, 0 < (ch' j).varOccurrences i → A.run (sub i) = p i) ∧
              (ch' j).subst (fun i => h.eval (sub i)) = ch j := by
            intro j
            specialize hchild j
            specialize ih j
            cases hchj : ch' j with
            | var i =>
              rw [hchj] at hchild
              rw [hchild] at ih
              obtain ⟨t₀, ht₀, hteq⟩ := ih
              refine ⟨fun _ => t₀, ?_, by simp [hteq]⟩
              intro k hk
              simp only [RankedTree.varOccurrences_var] at hk
              split_ifs at hk with hki
              · exact hki ▸ ht₀
              · omega
            | node b chb =>
              rw [hchj] at hchild
              rcases hchild with ⟨w', hw', hst⟩
              rw [hst] at ih
              obtain ⟨sub, hsub, hsubeq⟩ := ih
              rw [hw'] at hsub hsubeq
              exact ⟨sub, hsub, hsubeq⟩
          obtain ⟨sub, hrun, hsubst⟩ := hbuild_children g p a' ch' ch hdisj hmatch
          refine ⟨sub, ?_, ?_⟩
          · rw [hsw]; exact hrun
          · rw [hsw, RankedTree.subst_node]
            congr
            funext j
            exact hsubst j
  -- Key property 2 (Completeness): every `t₀` reaches `.inl (A.run t₀)` at `h.eval t₀`.
  have hcomplete : ∀ t₀ : GroundTree Λ rankΛ, B.Reaches (h.eval t₀) (.inl (A.run t₀)) := by
    intro t₀
    induction t₀ with
    | var x => exact x.elim
    | node g sub ih =>
      -- Prove by induction on any subterm `subterm g w` that it reaches `.inr ⟨g, w, p⟩`
      have hterm : ∀ (w : Pos g),
          (∀ a' ch', subterm g w = .node a' ch' →
            B.Reaches ((subterm g w).subst (fun i => h.eval (sub i)))
              (.inr ⟨g, w, fun i => A.run (sub i)⟩)) := by
        intro ⟨w, hw⟩
        suffices ∀ (s : RankedTree Γ rank (Fin (rankΛ g))) (u : Pos g),
            subterm g u = s →
            (∀ a' ch', s = .node a' ch' →
              B.Reaches (s.subst (fun i => h.eval (sub i)))
                (.inr ⟨g, u, fun i => A.run (sub i)⟩)) from
          this (subterm g ⟨w, hw⟩) ⟨w, hw⟩ rfl
        intro s
        induction s with
        | var _ => intro _ _ a' ch' hne; exact absurd hne (by simp)
        | node a' ch' ihs =>
          intro u hu _ _ heq
          have hch_reach : ∀ j : Fin (rank a'),
              ∃ st : St,
                B.Reaches ((ch' j).subst (fun i => h.eval (sub i))) st ∧
                match ch' j with
                | .var i => st = .inl (A.run (sub i))
                | .node _ _ =>
                  ∃ w' : Pos g, subterm g w' = ch' j ∧
                    st = .inr ⟨g, w', fun i => A.run (sub i)⟩ := by
            intro j
            cases hchj : ch' j with
            | var i => exact ⟨.inl (A.run (sub i)), ih i, rfl⟩
            | node b chb =>
              obtain ⟨w', hw'⟩ := hchild_pos g u a' ch' hu j
              have hr := ihs j w' hw' b chb hchj
              rw [hchj] at hr hw'
              exact ⟨.inr ⟨g, w', fun i => A.run (sub i)⟩, hr, w', hw', rfl⟩
          refine NFTA.Reaches.node a' (fun j => (ch' j).subst (fun i => h.eval (sub i)))
            (fun j => (hch_reach j).choose) _ (fun j => (hch_reach j).choose_spec.1) ?_
          dsimp only [B, δ]
          rw [hu]
          exact ⟨rfl, fun j => (hch_reach j).choose_spec.2⟩
      -- Apply the exact same step at the root `h.toFun g = .node a' ch'`
      have hroot : (h.toFun g).hasSymbol := (hh g).1
      cases hto : h.toFun g with
      | var _ => rw [hto] at hroot; exact False.elim hroot
      | node a' ch' =>
        let hroot_pos : Pos g := ⟨[], RankedTree.nil_mem_positions _⟩
        have hsub0 : subterm g hroot_pos = .node a' ch' := by
          have := hsubterm g hroot_pos
          dsimp only [hroot_pos] at this
          rw [RankedTree.subtree?_nil, Option.some.injEq] at this
          exact this.symm.trans hto
        have hch_reach : ∀ j : Fin (rank a'),
            ∃ st : St,
              B.Reaches ((ch' j).subst (fun i => h.eval (sub i))) st ∧
              match ch' j with
              | .var i => st = .inl (A.run (sub i))
              | .node _ _ =>
                ∃ w' : Pos g, subterm g w' = ch' j ∧
                  st = .inr ⟨g, w', fun i => A.run (sub i)⟩ := by
          intro j
          cases hchj : ch' j with
          | var i => exact ⟨.inl (A.run (sub i)), ih i, rfl⟩
          | node b chb =>
            obtain ⟨w', hw'⟩ := hchild_pos g hroot_pos a' ch' hsub0 j
            rw [hchj] at hw'
            have hr := hterm w' b chb (by rw [hw'])
            rw [hw'] at hr
            exact ⟨.inr ⟨g, w', fun i => A.run (sub i)⟩, hr, w', hw', rfl⟩
        rw [TreeHom.eval_node, hto, RankedTree.subst_node, DFTA.run_node]
        refine NFTA.Reaches.node a' (fun j => (ch' j).subst (fun i => h.eval (sub i)))
          (fun j => (hch_reach j).choose) _ (fun j => (hch_reach j).choose_spec.1) ?_
        refine ⟨g, fun i => A.run (sub i), rfl, ?_⟩
        rw [hto]
        refine ⟨rfl, fun j => ?_⟩
        have hspec := (hch_reach j).choose_spec.2
        cases hchj : ch' j with
        | var i => simpa [hchj] using hspec
        | node b chb => simpa [hchj] using hspec
  have hlang : B.language = h.eval '' A.language := by
    ext t
    constructor
    · rintro ⟨s, ⟨q, hqf, rfl⟩, hr⟩
      obtain ⟨t₀, rfl, rfl⟩ := hsound t (.inl q) hr
      exact ⟨t₀, hqf, rfl⟩
    · rintro ⟨t₀, ht₀, rfl⟩
      exact ⟨.inl (A.run t₀), ⟨A.run t₀, ht₀, rfl⟩, hcomplete t₀⟩
  rw [← hlang]
  exact of_nfta B

end IsRegularTreeLang

end CslibFrontier

