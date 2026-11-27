/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Foundations.Combinatorics.Words.Zimin
public import Mathlib.Logic.Relation

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Data.Finset.Card

/-!
# Bipartite `2`-Factor Graph Characterization and Polynomial-Time Free-Set Testing

A letter `x` occurring in a finite word pattern `α` fails to be free if and only if the directed
bipartite `2`-factor adjacency graph `G_α` admits a directed path from a left-side vertex with
first
component `x` to a right-side vertex with second component `x`. Iterating `SameRightNeighbor`
breadth-first reachability on bitmasks aligned with `α` decides both `IsFreeSet` and
`IsFreeLetter`
in polynomial time on multi-tape Turing machines.

## Main definitions

* `PatternGraphVertex`, `PatternGraphAdj`, `PatternGraphPath`: directed bipartite `2`-factor graph
  of a word pattern `α`.
* `encWord`: binary list encoding `encList encNat` of words over `ℕ`.
* `isFreeSetBool`, `isFreeLetterBool`: Boolean decision procedures for free sets and free letters.

## Main results

* `not_isFreeLetter_iff_exists_patternGraphPath`: graph-reachability characterization of non-free
  letters.
* `isFreeSetBool_eq_true_iff`, `isFreeLetterBool_eq_true_iff`: soundness and completeness of
  `isFreeSetBool` and `isFreeLetterBool`.
* `computableInPolyTime_isFreeSetBool`, `computableInPolyTime_isFreeLetterBool`: polynomial-time
  computability on multi-tape Turing machines.
-/

public section

namespace CslibFrontier.Complexity

open CslibFrontier.Word Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- A vertex `(side, fstLetter, sndLetter)` (`side = false` for left part, `side = true` for right
part) of the directed bipartite `2`-factor graph `G_α` associated to a contiguous `2`-factor
`[fstLetter, sndLetter]` of `α`. -/
@[ext]
structure PatternGraphVertex {A : Type*} (α : List A) where
  /-- Bipartition side: `false` for the first-letter side, `true` for the second-letter side. -/
  side : Bool
  /-- First component `a` of the `2`-factor `[a, b]`. -/
  fstLetter : A
  /-- Second component `b` of the `2`-factor `[a, b]`. -/
  sndLetter : A
  /-- Witness that `[fstLetter, sndLetter]` is a contiguous `2`-factor of `α`. -/
  is_factor : [fstLetter, sndLetter] <:+: α

/-- Directed edge relation of the bipartite `2`-factor graph `G_α`: left-to-right edges share the
second component, and right-to-left edges share the first component. -/
@[expose]
def PatternGraphAdj {A : Type*} (α : List A) (u v : PatternGraphVertex α) : Prop :=
  (u.side = false ∧ v.side = true ∧ u.sndLetter = v.sndLetter) ∨
  (u.side = true ∧ v.side = false ∧ u.fstLetter = v.fstLetter)

/-- Directed path (reflexive-transitive walk) in the bipartite `2`-factor graph `G_α`. -/
@[expose]
def PatternGraphPath {A : Type*} (α : List A) (u v : PatternGraphVertex α) : Prop :=
  Relation.ReflTransGen (PatternGraphAdj α) u v

section GraphCharacterization

variable {A : Type*}

private theorem reflTransGen_sameRightNeighbor_of_patternGraphPath {α : List A}
    {u w : PatternGraphVertex α} (hpath : PatternGraphPath α u w) :
    Relation.ReflTransGen (SameRightNeighbor α) u.fstLetter w.fstLetter := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w₁ w₂ _ hadj ih =>
    rcases hadj with ⟨_, _, hsnd⟩ | ⟨_, _, hfst⟩
    · refine ih.tail (sameRightNeighbor_iff.mpr ⟨w₁.sndLetter, w₁.is_factor, ?_⟩)
      rw [hsnd]
      exact w₂.is_factor
    · rwa [← hfst]

private theorem exists_patternGraphPath_false_of_reflTransGen {α : List A} {x b : A}
    (hxb : Relation.ReflTransGen (SameRightNeighbor α) x b) :
    ∀ {c : A} (hbc : [b, c] <:+: α),
      ∃ u : PatternGraphVertex α,
        u.side = false ∧ u.fstLetter = x ∧
          PatternGraphPath α u ⟨false, b, c, hbc⟩ := by
  induction hxb with
  | refl =>
    intro c hxc
    exact ⟨⟨false, x, c, hxc⟩, rfl, rfl, Relation.ReflTransGen.refl⟩
  | @tail b₁ b₂ _ hstep ih =>
    intro c hb₂c
    rcases sameRightNeighbor_iff.mp hstep with ⟨d, hb₁d, hb₂d⟩
    obtain ⟨u, huside, hufst, hpath⟩ := ih hb₁d
    let mid : PatternGraphVertex α := ⟨true, b₂, d, hb₂d⟩
    let tgt : PatternGraphVertex α := ⟨false, b₂, c, hb₂c⟩
    have hadj₁ : PatternGraphAdj α ⟨false, b₁, d, hb₁d⟩ mid :=
      Or.inl ⟨rfl, rfl, rfl⟩
    have hadj₂ : PatternGraphAdj α mid tgt :=
      Or.inr ⟨rfl, rfl, rfl⟩
    exact ⟨u, huside, hufst, (hpath.tail hadj₁).tail hadj₂⟩

/-- An alternating `2`-factor chain from `x` to `y` in `α` exists if and only if `G_α` contains a
directed path from a `^0`-vertex with first letter `x` to a `^1`-vertex with second letter `y`. -/
theorem hasAlternatingChain_iff_exists_patternGraphPath {α : List A} {x y : A} :
    HasAlternatingChain α x y ↔
      ∃ u v : PatternGraphVertex α,
        u.side = false ∧ u.fstLetter = x ∧ v.side = true ∧ v.sndLetter = y ∧
          PatternGraphPath α u v := by
  rw [hasAlternatingChain_iff_reflTransGen]
  constructor
  · rintro ⟨b, hxb, hby⟩
    obtain ⟨u, huside, hufst, hpath⟩ := exists_patternGraphPath_false_of_reflTransGen hxb hby
    let v : PatternGraphVertex α := ⟨true, b, y, hby⟩
    have hadj : PatternGraphAdj α ⟨false, b, y, hby⟩ v := Or.inl ⟨rfl, rfl, rfl⟩
    exact ⟨u, v, huside, hufst, rfl, rfl, hpath.tail hadj⟩
  · rintro ⟨u, v, _, rfl, _, rfl, hpath⟩
    exact ⟨v.fstLetter, reflTransGen_sameRightNeighbor_of_patternGraphPath hpath, v.is_factor⟩

/-- A letter `x` occurring in a pattern `α` fails to be free for `α` if and only if the
bipartite `2`-factor graph `G_α` contains a directed path from a left-side vertex with first
component `x` to a right-side vertex with second component `x`. -/
theorem not_isFreeLetter_iff_exists_patternGraphPath {α : List A} {x : A} (hx : x ∈ α) :
    ¬ IsFreeLetter α x ↔
      ∃ u v : PatternGraphVertex α,
        u.side = false ∧ u.fstLetter = x ∧ v.side = true ∧ v.sndLetter = x ∧
          PatternGraphPath α u v := by
  rw [isFreeLetter_iff, not_and, not_not]
  exact ⟨fun h ↦ hasAlternatingChain_iff_exists_patternGraphPath.mp (h hx),
    fun h _ ↦ hasAlternatingChain_iff_exists_patternGraphPath.mpr h⟩

end GraphCharacterization

section PolyTimeFreeTesting

/-- Canonical binary list encoding of a word `α : List ℕ` over a finite subset of `ℕ`. -/
abbrev encWord : List ℕ ↪ List Bool := encList encNat

/-- List of contiguous `2`-factors `(α[i], α[i + 1])` of `α : List ℕ`. -/
def wordPairs (α : List ℕ) : List (ℕ × ℕ) :=
  α.zip α.tail

/-- Membership in `wordPairs α` coincides with contiguous `2`-factor containment `[a, b] <:+: α`.
-/
theorem mem_wordPairs_iff_infix {α : List ℕ} {a b : ℕ} :
    (a, b) ∈ wordPairs α ↔ [a, b] <:+: α := by
  induction α with
  | nil =>
    simp [wordPairs]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [wordPairs, List.tail_cons, List.zip_nil_right, List.not_mem_nil, false_iff]
      rintro ⟨s, t, h⟩
      have hlen := congrArg List.length h
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    | cons y ys =>
      have hcons : wordPairs (x :: y :: ys) = (x, y) :: wordPairs (y :: ys) := rfl
      rw [hcons, List.mem_cons, Prod.mk.injEq, ih]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨s, t, hst⟩)
        · exact ⟨[], ys, rfl⟩
        · exact ⟨x :: s, t, by simp [hst]⟩
      · rintro ⟨s, t, hst⟩
        cases s with
        | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
          exact Or.inl ⟨hst.1, hst.2.1⟩
        | cons z zs =>
          simp only [List.cons_append, List.cons.injEq] at hst
          exact Or.inr ⟨zs, t, hst.2⟩

private def memNatListBool (p : List ℕ × ℕ) : Bool :=
  p.1.any fun u ↦ u == p.2

private def pairFromCurWithRightBool (p : (List ℕ × List (ℕ × ℕ)) × ℕ) : Bool :=
  p.1.2.any fun r ↦ memNatListBool (p.1.1, r.1) && (r.2 == p.2)

private def stepVertexPredBool (p : (List ℕ × List (ℕ × ℕ)) × ℕ) : Bool :=
  memNatListBool (p.1.1, p.2) ||
    p.1.2.any fun q ↦ (q.1 == p.2) && pairFromCurWithRightBool (p.1, q.2)

/-- One breadth-first step of `SameRightNeighbor` expansion on bitmasks aligned with `par.1 = α`,
using `par.2 = wordPairs α`. -/
def stepReachMask (par : List ℕ × List (ℕ × ℕ)) (m : List Bool) : List Bool :=
  par.1.map fun v ↦ stepVertexPredBool ((selectDistinct par.1 m, par.2), v)

/-- Fixed-point reachability bitmask after `α.length` breadth-first steps from `X`. -/
def reachMask (α X : List ℕ) : List Bool :=
  (stepReachMask (α, wordPairs α))^[α.length] (α.map fun v ↦ memNatListBool (X, v))

private def chainPairHitBool (p : (List ℕ × List ℕ) × (ℕ × ℕ)) : Bool :=
  memNatListBool (p.1.1, p.2.1) && memNatListBool (p.1.2, p.2.2)

/-- Boolean check for existence of an alternating `2`-factor chain between occurrences of `X` in
`α`. -/
def hasChainSetBool (p : List ℕ × List ℕ) : Bool :=
  (wordPairs p.1).any fun q ↦ chainPairHitBool ((selectDistinct p.1 (reachMask p.1 p.2), p.2), q)

/-- Polynomial-time Boolean decision procedure for `IsFreeSet p.1 {x | x ∈ p.2}`. -/
def isFreeSetBool (p : List ℕ × List ℕ) : Bool :=
  !hasChainSetBool p

/-- Polynomial-time Boolean decision procedure for `IsFreeLetter p.1 p.2`. -/
def isFreeLetterBool (p : List ℕ × ℕ) : Bool :=
  memNatListBool p && isFreeSetBool (p.1, [p.2])

private theorem mem_selectDistinct_map (α : List ℕ) (pred : ℕ → Bool) (v : ℕ) :
    v ∈ selectDistinct α (α.map pred) ↔ v ∈ α ∧ pred v = true := by
  rw [mem_selectDistinct]
  constructor
  · rintro ⟨hv, hget⟩
    have hlt : α.idxOf v < α.length := List.idxOf_lt_length_iff.mpr hv
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hlt] at hget
    simp only [Option.map_some, Option.getD_some, List.getElem_idxOf] at hget
    exact ⟨hv, hget⟩
  · rintro ⟨hv, hpv⟩
    refine ⟨hv, ?_⟩
    have hlt : α.idxOf v < α.length := List.idxOf_lt_length_iff.mpr hv
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
    simp [hpv]

private theorem mem_selectDistinct_stepReachMask (α : List ℕ) (m : List Bool) (v : ℕ) :
    v ∈ selectDistinct α (stepReachMask (α, wordPairs α) m) ↔
      v ∈ α ∧ (v ∈ selectDistinct α m ∨
        ∃ u ∈ selectDistinct α m, SameRightNeighbor α u v) := by
  dsimp only [stepReachMask, stepVertexPredBool, pairFromCurWithRightBool, memNatListBool]
  rw [mem_selectDistinct_map]
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, Prod.exists]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · rintro (⟨u, hu, huv⟩ | ⟨q₁, q₂, hq, hqv, p₁, p₂, hp, ⟨u, hu, hup⟩, hpq⟩)
    · subst huv
      exact Or.inl hu
    · subst hqv hup hpq
      exact Or.inr ⟨u, hu, sameRightNeighbor_iff.mpr
        ⟨p₂, mem_wordPairs_iff_infix.mp hp, mem_wordPairs_iff_infix.mp hq⟩⟩
  · rintro (hcur | ⟨u, hu, hsr⟩)
    · exact Or.inl ⟨v, hcur, rfl⟩
    · rcases sameRightNeighbor_iff.mp hsr with ⟨c, huc, hvc⟩
      exact Or.inr ⟨v, c, mem_wordPairs_iff_infix.mpr hvc, rfl,
        u, c, mem_wordPairs_iff_infix.mpr huc, ⟨u, hu, rfl⟩, rfl⟩

private theorem iter_stepReachMask_sound (α X : List ℕ) (k : ℕ) :
    ∀ v ∈ selectDistinct α
        ((stepReachMask (α, wordPairs α))^[k] (α.map fun v ↦ memNatListBool (X, v))),
      v ∈ α ∧ ∃ x ∈ X, x ∈ α ∧ Relation.ReflTransGen (SameRightNeighbor α) x v := by
  induction k with
  | zero =>
    intro v hv
    simp only [Function.iterate_zero, id_eq, mem_selectDistinct_map, memNatListBool,
      List.any_eq_true, beq_iff_eq] at hv
    rcases hv with ⟨hvα, x, hxX, hxv⟩
    subst hxv
    exact ⟨hvα, x, hxX, hvα, Relation.ReflTransGen.refl⟩
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply', mem_selectDistinct_stepReachMask] at hv
    rcases hv with ⟨hvα, hprev | ⟨u, hu, hstep⟩⟩
    · exact ih v hprev
    · obtain ⟨_, x, hxX, hxα, hpath⟩ := ih u hu
      exact ⟨hvα, x, hxX, hxα, hpath.tail hstep⟩

private theorem mem_reachMask_iff (α X : List ℕ) (v : ℕ) :
    v ∈ selectDistinct α (reachMask α X) ↔
      v ∈ α ∧ ∃ x ∈ X, x ∈ α ∧ Relation.ReflTransGen (SameRightNeighbor α) x v := by
  let mAt : ℕ → List Bool := fun k ↦
    (stepReachMask (α, wordPairs α))^[k] (α.map fun v ↦ memNatListBool (X, v))
  let SAt : ℕ → Finset ℕ := fun k ↦ (selectDistinct α (mAt k)).toFinset
  have hsub_α : ∀ k, SAt k ⊆ α.toFinset := by
    intro k u hu
    rw [List.mem_toFinset] at hu ⊢
    exact (mem_selectDistinct.mp hu).1
  have hmono : ∀ k, SAt k ⊆ SAt (k + 1) := by
    intro k u hu
    simp only [SAt, mAt, List.mem_toFinset, Function.iterate_succ_apply',
      mem_selectDistinct_stepReachMask] at hu ⊢
    exact ⟨(mem_selectDistinct.mp hu).1, Or.inl hu⟩
  have hclosed_at : ∃ k ≤ α.length, SAt (k + 1) = SAt k := by
    by_contra hstrict
    push Not at hstrict
    have hcard : ∀ k ≤ α.length, k + 1 ≤ (SAt (k + 1)).card := by
      intro k hk
      induction k with
      | zero =>
        have hlt : (SAt 0).card < (SAt (0 + 1)).card :=
          Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hmono 0,
            (hstrict 0 (Nat.zero_le _)).symm⟩)
        omega
      | succ k ihk =>
        have hk' := ihk (Nat.le_of_succ_le hk)
        have hlt : (SAt (k + 1)).card < (SAt ((k + 1) + 1)).card :=
          Finset.card_lt_card
            (ssubset_iff_subset_ne.mpr ⟨hmono (k + 1), (hstrict (k + 1) hk).symm⟩)
        omega
    have h1 := hcard α.length (Nat.le_refl _)
    have h2 : (SAt (α.length + 1)).card ≤ α.toFinset.card := Finset.card_le_card (hsub_α _)
    have h3 : α.toFinset.card ≤ α.length := List.toFinset_card_le α
    omega
  obtain ⟨k₀, hk₀_le, hfix⟩ := hclosed_at
  have hclosed_k₀ : ∀ u ∈ selectDistinct α (mAt k₀), ∀ w : ℕ,
      SameRightNeighbor α u w → w ∈ selectDistinct α (mAt k₀) := by
    intro u hu w hsr
    have hwα : w ∈ α := by
      rcases sameRightNeighbor_iff.mp hsr with ⟨c, _, hwc⟩
      exact hwc.subset (by simp)
    have hw_next : w ∈ SAt (k₀ + 1) := by
      simp only [SAt, mAt, List.mem_toFinset, Function.iterate_succ_apply',
        mem_selectDistinct_stepReachMask]
      exact ⟨hwα, Or.inr ⟨u, hu, hsr⟩⟩
    rw [hfix] at hw_next
    exact List.mem_toFinset.mp hw_next
  have hmono_le : ∀ {i j : ℕ}, i ≤ j → SAt i ⊆ SAt j := by
    intro i j hij
    induction hij with
    | refl => exact Finset.Subset.rfl
    | step _ ih => exact ih.trans (hmono _)
  constructor
  · intro hv
    exact iter_stepReachMask_sound α X α.length v hv
  · rintro ⟨hvα, x, hxX, hxα, hpath⟩
    have hx0 : x ∈ SAt 0 := by
      simp only [SAt, mAt, List.mem_toFinset, Function.iterate_zero, id_eq,
        mem_selectDistinct_map, memNatListBool, List.any_eq_true, beq_iff_eq]
      exact ⟨hxα, x, hxX, rfl⟩
    have hxk₀ : x ∈ selectDistinct α (mAt k₀) :=
      List.mem_toFinset.mp (hmono_le (Nat.zero_le k₀) hx0)
    have hvk₀ : v ∈ selectDistinct α (mAt k₀) := by
      clear hvα
      induction hpath with
      | refl => exact hxk₀
      | tail _ hstep ihp => exact hclosed_k₀ _ ihp _ hstep
    have hvN : v ∈ SAt α.length := hmono_le hk₀_le (List.mem_toFinset.mpr hvk₀)
    exact List.mem_toFinset.mp hvN

/-- `hasChainSetBool (α, X) = true` if and only if some `x, y ∈ X` are linked by an alternating
`2`-factor chain in `α`. -/
theorem hasChainSetBool_eq_true_iff (α X : List ℕ) :
    hasChainSetBool (α, X) = true ↔ ∃ x ∈ X, ∃ y ∈ X, HasAlternatingChain α x y := by
  simp only [hasChainSetBool, chainPairHitBool, memNatListBool, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, Prod.exists]
  constructor
  · rintro ⟨b, y, hby_pair, ⟨u, hu_reach, hub⟩, ⟨y', hyX, hyy'⟩⟩
    subst hub hyy'
    obtain ⟨_, x, hxX, _, hxb⟩ := (mem_reachMask_iff α X u).mp hu_reach
    exact ⟨x, hxX, y', hyX,
      hasAlternatingChain_iff_reflTransGen.mpr ⟨u, hxb, mem_wordPairs_iff_infix.mp hby_pair⟩⟩
  · rintro ⟨x, hxX, y, hyX, hchain⟩
    rcases hasAlternatingChain_iff_reflTransGen.mp hchain with ⟨b, hxb, hby⟩
    have hxα : x ∈ α := by
      cases hxb using Relation.ReflTransGen.head_induction_on with
      | refl => exact hby.subset (by simp)
      | head hstep _ _ =>
        rcases sameRightNeighbor_iff.mp hstep with ⟨c, hxc, _⟩
        exact hxc.subset (by simp)
    have hbα : b ∈ α := hby.subset (by simp)
    have hb_reach : b ∈ selectDistinct α (reachMask α X) :=
      (mem_reachMask_iff α X b).mpr ⟨hbα, x, hxX, hxα, hxb⟩
    exact ⟨b, y, mem_wordPairs_iff_infix.mpr hby, ⟨b, hb_reach, rfl⟩, ⟨y, hyX, rfl⟩⟩

/-- `isFreeSetBool (α, X) = true` if and only if `{x | x ∈ X}` is a free set for `α`. -/
theorem isFreeSetBool_eq_true_iff (α X : List ℕ) :
    isFreeSetBool (α, X) = true ↔ IsFreeSet α {x : ℕ | x ∈ X} := by
  simp only [isFreeSetBool, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    hasChainSetBool_eq_true_iff, isFreeSet_iff, Set.mem_ofPred_eq]
  push Not
  rfl

/-- `isFreeLetterBool (α, x) = true` if and only if `x` is a free letter for `α`. -/
theorem isFreeLetterBool_eq_true_iff (α : List ℕ) (x : ℕ) :
    isFreeLetterBool (α, x) = true ↔ IsFreeLetter α x := by
  simp only [isFreeLetterBool, memNatListBool, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
    isFreeSetBool_eq_true_iff, isFreeLetter_iff_singleton_isFreeSet]
  constructor
  · rintro ⟨⟨u, hu, hux⟩, hfree⟩
    subst hux
    refine ⟨hu, ?_⟩
    simpa [Set.ofPred_mem_eq] using hfree
  · rintro ⟨hx, hfree⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simpa [Set.ofPred_mem_eq] using hfree

private theorem length_iter_stepReachMask (α X : List ℕ) (i : ℕ) :
    ((stepReachMask (α, wordPairs α))^[i] (α.map fun v ↦ memNatListBool (X, v))).length =
      α.length := by
  induction i with
  | zero => simp
  | succ i _ =>
    rw [Function.iterate_succ_apply']
    simp [stepReachMask]

@[fun_prop]
private theorem computableInPolyTime_selectDistinctWithInput {γ : Type}
    {encIn : γ ↪ List Bool} {l : γ → List ℕ} {m : γ → List Bool}
    (hl : ComputableInPolyTime l encIn encWord)
    (hm : ComputableInPolyTime m encIn encBits) :
    ComputableInPolyTime (fun x ↦ selectDistinct (l x) (m x)) encIn encWord :=
  (computableInPolyTime_selectDistinct encNat).comp (hl.prod hm)

@[fun_prop]
private theorem computableInPolyTime_memNatListBool :
    ComputableInPolyTime memNatListBool (encPair encWord encNat) encBool := by
  unfold memNatListBool
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_pairFromCurWithRightBool :
    ComputableInPolyTime pairFromCurWithRightBool
      (encPair (encPair encWord (encList (encPair encNat encNat))) encNat) encBool := by
  unfold pairFromCurWithRightBool
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_stepVertexPredBool :
    ComputableInPolyTime stepVertexPredBool
      (encPair (encPair encWord (encList (encPair encNat encNat))) encNat) encBool := by
  unfold stepVertexPredBool
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_chainPairHitBool :
    ComputableInPolyTime chainPairHitBool
      (encPair (encPair encWord encWord) (encPair encNat encNat)) encBool := by
  unfold chainPairHitBool
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_wordPairs :
    ComputableInPolyTime wordPairs encWord (encList (encPair encNat encNat)) := by
  unfold wordPairs
  fun_prop

private theorem computableInPolyTime_stepReachMask :
    ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × List Bool ↦ stepReachMask p.1 p.2)
      (encPair (encPair encWord (encList (encPair encNat encNat))) encBits) encBits := by
  have hlist : ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × List Bool ↦ stepReachMask p.1 p.2)
      (encPair (encPair encWord (encList (encPair encNat encNat))) encBits)
      (encList encBool) := by
    unfold stepReachMask
    fun_prop
  exact (bits_encList_polyTime encBool).2.comp hlist

@[fun_prop]
private theorem computableInPolyTime_reachMask :
    ComputableInPolyTime (fun p : List ℕ × List ℕ ↦ reachMask p.1 p.2)
      (encPair encWord encWord) encBits := by
  have hpar : ComputableInPolyTime (fun p : List ℕ × List ℕ ↦ (p.1, wordPairs p.1))
      (encPair encWord encWord) (encPair encWord (encList (encPair encNat encNat))) := by
    fun_prop
  have hcount : ComputableInPolyTime (fun p : List ℕ × List ℕ ↦ p.1.length)
      (encPair encWord encWord) encUnary := by
    fun_prop
  have hinit_list : ComputableInPolyTime
      (fun p : List ℕ × List ℕ ↦ p.1.map fun v ↦ memNatListBool (p.2, v))
      (encPair encWord encWord) (encList encBool) := by
    fun_prop
  have hinit : ComputableInPolyTime
      (fun p : List ℕ × List ℕ ↦ p.1.map fun v ↦ memNatListBool (p.2, v))
      (encPair encWord encWord) encBits :=
    (bits_encList_polyTime encBool).2.comp hinit_list
  refine iterateWith hpar hcount hinit computableInPolyTime_stepReachMask PolyBounded.self ?_
  intro x i _
  simp only [encBits_apply, length_iter_stepReachMask, length_encPair]
  have hle : x.1.length ≤ (encWord x.1).length := length_le_length_encList encNat x.1
  omega

/-- Checking whether a subset `X` is free for `α` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_isFreeSetBool :
    ComputableInPolyTime isFreeSetBool (encPair encWord encWord) encBool := by
  have hc : ComputableInPolyTime hasChainSetBool (encPair encWord encWord) encBool := by
    unfold hasChainSetBool
    fun_prop
  unfold isFreeSetBool
  fun_prop

/-- Deciding whether a letter `x` is free for a pattern `α` runs in polynomial time on a
multi-tape Turing machine. -/
@[fun_prop]
theorem computableInPolyTime_isFreeLetterBool :
    ComputableInPolyTime isFreeLetterBool (encPair encWord encNat) encBool := by
  unfold isFreeLetterBool
  fun_prop

end PolyTimeFreeTesting

end CslibFrontier.Complexity
