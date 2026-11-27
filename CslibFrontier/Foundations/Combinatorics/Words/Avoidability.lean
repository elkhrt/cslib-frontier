/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import CslibFrontier.Foundations.Combinatorics.Words.SquareFree

/-!
# Word Pattern Reflection, Avoidability, Free Sets, and Zimin Words

A finite pattern `u : List A` is *reflected* by a word `v : List B` (`CslibFrontier.Word.Reflects
v u`)
if there is a map `φ : A → List B` sending every letter occurring in `u` to a nonempty word over
`B`
such that `u.flatMap φ` occurs as a contiguous factor of `v`. Following Bean, Ehrenfeucht, and
McNulty, a pattern `w : List A` is *unavoidable* (`CslibFrontier.Word.IsUnavoidable`) if
for every
finite alphabet `B`, only finitely many words over `B` fail to reflect `w`; otherwise `w` is
*avoidable* (`CslibFrontier.Word.IsAvoidable`).

This module develops the foundational algebra of pattern reflection, avoidability of repeated
adjacent letters via Thue's ternary square-free words, letter deletion and identification, free
letters and free sets via alternating `2`-factor chains, the Bean–Ehrenfeucht–McNulty telescoping
morphism lift across free-set deletion, canonical Zimin words `Z_k`
(`CslibFrontier.Word.ziminWord`), the
equivalence between free-set reducibility and reflection in `Z_k`, and the unavoidability of every
`Z_k` under standard Lean axioms.

## Main definitions

* `CslibFrontier.Word.Reflects`: non-erasing morphic factor relation `u.flatMap φ <:+: v`.
* `CslibFrontier.Word.IsUnavoidableFor`: finiteness of non-reflecting words inside a language `L`.
* `CslibFrontier.Word.IsUnavoidable` / `CslibFrontier.Word.IsAvoidable`: unavoidability and
  avoidability of a
  word pattern across all finite alphabets.
* `CslibFrontier.Word.deleteLetters` / `CslibFrontier.Word.deleteLetter` /
  `CslibFrontier.Word.identifyLetters`:
  letter-set deletion `w^X`, single-letter deletion `w^x`, and letter identification `x ↦ y`.
* `CslibFrontier.Word.HasAlternatingChain` / `CslibFrontier.Word.IsFreeLetter` /
  `CslibFrontier.Word.IsFreeSet`:
  alternating `2`-factor chains, free letters, and free sets in a pattern.
* `CslibFrontier.Word.SameRightNeighbor`: shared-right-neighbor relation on left components of
  `2`-factors.
* `CslibFrontier.Word.ziminWord`: canonical Zimin words `Z_0 =`, `Z_{k+1} = Z_k ++ [k] ++ Z_k`.
* `CslibFrontier.Word.IsFreeSetReducible` / `CslibFrontier.Word.IsBEMReducible`: Sapir/Zimin
  free-set
  reducibility and Bean–Ehrenfeucht–McNulty reducibility to ``.

## Main results

* `CslibFrontier.Word.Reflects.trans`: word reflection is transitive across morphisms.
* `CslibFrontier.Word.isAvoidable_of_pair_infix`: any pattern containing `[x, x]` as a factor is
  avoidable.
* `CslibFrontier.Word.hasAlternatingChain_iff_reflTransGen`: reachability characterization of
  alternating
  `2`-factor chains.
* `CslibFrontier.Word.flatMap_telescoping`: boundary-cancelling telescoping identity for word
  morphisms.
* `CslibFrontier.Word.reflects_append_singleton_of_isFreeSet`: telescoping morphism lift across
  deletion
  of a free set.
* `CslibFrontier.Word.isFreeSetReducible_iff_exists_reflects_ziminWord`: free-set reducibility is
  equivalent to reflection in some Zimin word `ziminWord k`.
* `CslibFrontier.Word.isUnavoidable_ziminWord`: every canonical Zimin word `ziminWord k` is
  unavoidable.
-/

public section

namespace CslibFrontier.Word

section ReflectionAndAvoidability

variable {A B C : Type*}

/-- A word `v : List B` *reflects* a pattern `u : List A` if there is a map `φ : A → List B`
sending
every letter occurring in `u` to a nonempty word over `B` such that `u.flatMap φ` is a contiguous
factor (infix) of `v`. -/
def Reflects (v : List B) (u : List A) : Prop :=
  ∃ φ : A → List B, (∀ a ∈ u, φ a ≠ []) ∧ u.flatMap φ <:+: v

/-- Unfolded characterization of `Reflects`. -/
theorem reflects_iff {v : List B} {u : List A} :
    Reflects v u ↔ ∃ φ : A → List B, (∀ a ∈ u, φ a ≠ []) ∧ u.flatMap φ <:+: v := by
  rfl

/-- Over a nonempty target alphabet `B`, `Reflects v u` is equivalent to existence of a globally
non-erasing morphism `φ : A → List B` (`∀ a, φ a ≠ []`) with `u.flatMap φ <:+: v`. -/
theorem reflects_iff_exists_forall_ne_nil [Nonempty B] {v : List B} {u : List A} :
    Reflects v u ↔ ∃ φ : A → List B, (∀ a : A, φ a ≠ []) ∧ u.flatMap φ <:+: v := by
  classical
  constructor
  · rintro ⟨φ, hφ, hinf⟩
    obtain ⟨b₀⟩ := ‹Nonempty B›
    refine ⟨fun a ↦ if a ∈ u then φ a else [b₀], fun a ↦ ?_, ?_⟩
    · dsimp only
      split_ifs with ha
      · exact hφ a ha
      · exact List.cons_ne_nil _ _
    · have hcongr : u.flatMap (fun a ↦ if a ∈ u then φ a else [b₀]) = u.flatMap φ := by
        apply List.flatMap_congr
        intro a ha
        simp [ha]
      rwa [hcongr]
  · rintro ⟨φ, hφ, hinf⟩
    exact ⟨φ, fun a _ ↦ hφ a, hinf⟩

/-- Every word reflects the empty pattern. -/
@[simp]
theorem reflects_nil (v : List B) : Reflects v ([] : List A) :=
  ⟨fun _ ↦ [], by simp, List.nil_infix⟩

private theorem flatMap_singleton_eq (w : List A) : w.flatMap (fun a ↦ [a]) = w := by
  induction w with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, ih]

private theorem flatMap_flatMap (u : List A) (φ : A → List B) (ψ : B → List C) :
    (u.flatMap φ).flatMap ψ = u.flatMap (fun a ↦ (φ a).flatMap ψ) := by
  induction u with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, List.flatMap_append, ih]

private theorem isInfix_flatMap {s v : List B} (h : s <:+: v) (ψ : B → List C) :
    s.flatMap ψ <:+: v.flatMap ψ := by
  rcases h with ⟨l₁, l₂, rfl⟩
  exact ⟨l₁.flatMap ψ, l₂.flatMap ψ, by simp [List.flatMap_append]⟩

/-- Reflection is reflexive. -/
theorem Reflects.refl (w : List A) : Reflects w w :=
  ⟨fun a ↦ [a], fun _ _ ↦ List.cons_ne_nil _ _,
    (flatMap_singleton_eq w).symm ▸ List.infix_refl w⟩

/-- Reflection is preserved when extending the host word by factor containment. -/
theorem Reflects.of_infix {u : List A} {v₁ v₂ : List B} (h₁ : Reflects v₁ u) (h₂ : v₁ <:+: v₂) :
    Reflects v₂ u := by
  rcases h₁ with ⟨φ, hφ, hinf⟩
  exact ⟨φ, hφ, hinf.trans h₂⟩

/-- Every contiguous factor of `w` is reflected by `w`. -/
theorem Reflects.of_isInfix {u w : List A} (h : u <:+: w) : Reflects w u :=
  (Reflects.refl u).of_infix h

/-- Reflection is transitive across morphisms. -/
theorem Reflects.trans {u : List A} {v : List B} {w : List C} (h₁ : Reflects v u)
    (h₂ : Reflects w v) : Reflects w u := by
  rcases h₁ with ⟨φ, hφ, hinf₁⟩
  rcases h₂ with ⟨ψ, hψ, hinf₂⟩
  refine ⟨fun a ↦ (φ a).flatMap ψ, ?_, ?_⟩
  · intro a ha
    have hne := hφ a ha
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil (φ a) hne
    have hbv : b ∈ v := hinf₁.subset (List.mem_flatMap.mpr ⟨a, ha, hb⟩)
    have hψb := hψ b hbv
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil (ψ b) hψb
    exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨b, hb, hc⟩)
  · rw [← flatMap_flatMap]
    exact (isInfix_flatMap hinf₁ ψ).trans hinf₂

/-- Any letter-wise image `w.map f` reflects `w`. -/
theorem reflects_map (f : A → B) (w : List A) : Reflects (w.map f) w := by
  refine ⟨fun a ↦ [f a], fun _ _ ↦ List.cons_ne_nil _ _, ?_⟩
  have heq : w.flatMap (fun a ↦ [f a]) = w.map f := by
    induction w with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, ih]
  simp [heq]

/-- An injective letter-wise renaming reflects in both directions: `w` reflects `w.map f`. -/
theorem Reflects.of_injective_map {f : A → B} (hf : Function.Injective f) (w : List A) :
    Reflects w (w.map f) := by
  classical
  let g : B → List A := fun b ↦ if h : ∃ a, f a = b then [h.choose] else []
  refine ⟨g, ?_, ?_⟩
  · intro b hb
    rcases List.mem_map.mp hb with ⟨a, _, rfl⟩
    have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp [g, hex]
  · have heq : (w.map f).flatMap g = w := by
      induction w with
      | nil => rfl
      | cons a as ih =>
        have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
        have hch : hex.choose = a := hf hex.choose_spec
        simp [List.flatMap_cons, g, hex, hch, ih]
    simp [heq]

/-- Any word reflecting `u` has length at least `u.length`. -/
theorem Reflects.length_le {v : List B} {u : List A} (h : Reflects v u) :
    u.length ≤ v.length := by
  rcases h with ⟨φ, hφ, hinf⟩
  have hflat : ∀ l : List A, (∀ a ∈ l, φ a ≠ []) → l.length ≤ (l.flatMap φ).length := by
    intro l hl
    induction l with
    | nil => simp
    | cons a as ih =>
      have hpos : 0 < (φ a).length := List.length_pos_iff.mpr (hl a (by simp))
      have htail : as.length ≤ (as.flatMap φ).length := ih (fun x hx ↦ hl x (by simp [hx]))
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega
  exact Nat.le_trans (hflat u hφ) hinf.length_le

/-- A pattern `w : List A` is *unavoidable for* a language `L : Set (List B)` if all but finitely
many words in `L` reflect `w`. -/
def IsUnavoidableFor (L : Set (List B)) (w : List A) : Prop :=
  {v ∈ L | ¬ Reflects v w}.Finite

/-- A pattern `w : List A` is *unavoidable* if for every finite alphabet `Fin k`, all but finitely
many words over `Fin k` reflect `w`. -/
def IsUnavoidable (w : List A) : Prop :=
  ∀ k : ℕ, IsUnavoidableFor (Set.univ : Set (List (Fin k))) w

/-- A pattern `w : List A` is *avoidable* if it is not unavoidable. -/
def IsAvoidable (w : List A) : Prop :=
  ¬ IsUnavoidable w

/-- Unfolded characterization of `IsAvoidable`. -/
theorem isAvoidable_iff {w : List A} : IsAvoidable w ↔ ¬ IsUnavoidable w := by
  rfl

/-- An unavoidable pattern is unavoidable for `Set.univ : Set (List B)` over any finite alphabet
`B`. -/
theorem IsUnavoidable.isUnavoidableFor_univ [Finite B] {w : List A} (hw : IsUnavoidable w) :
    IsUnavoidableFor (Set.univ : Set (List B)) w := by
  have := Fintype.ofFinite B
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  have hinj : Function.Injective (List.map e) := List.map_injective_iff.mpr e.injective
  have hfin := hw (Fintype.card B)
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine hfin.subset ?_
  rintro _ ⟨v, ⟨_, hnv⟩, rfl⟩
  refine ⟨trivial, fun href ↦ hnv ?_⟩
  exact href.trans (Reflects.of_injective_map e.injective v)

/-- Over any finite alphabet `B` and any language `L : Set (List B)`, an unavoidable pattern is
unavoidable for `L`. -/
theorem IsUnavoidable.isUnavoidableFor [Finite B] {w : List A} (hw : IsUnavoidable w)
    (L : Set (List B)) : IsUnavoidableFor L w :=
  (hw.isUnavoidableFor_univ (B := B)).subset fun _ ⟨_, hnr⟩ ↦ ⟨trivial, hnr⟩

/-- Existence of an infinite language over a finite alphabet avoiding `w` implies
`IsAvoidable w`. -/
theorem isAvoidable_of_infinite_not_reflects [Finite B] {L : Set (List B)} {w : List A}
    (hL : L.Infinite) (hav : ∀ v ∈ L, ¬ Reflects v w) : IsAvoidable w := by
  intro hw
  exact hL ((hw.isUnavoidableFor L).subset fun v hv ↦ ⟨hv, hav v hv⟩)

private theorem exists_gt_of_finset (s : Finset ℕ) : ∃ N : ℕ, ∀ m ∈ s, m < N := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    rcases ih with ⟨N, hN⟩
    refine ⟨max (a + 1) N, fun m hm ↦ ?_⟩
    rcases Finset.mem_insert.mp hm with rfl | hms
    · omega
    · have := hN m hms
      omega

private def wordsOfLength (alph : List B) : ℕ → List (List B)
  | 0 => [[]]
  | n + 1 => alph.flatMap fun b ↦ (wordsOfLength alph n).map (b :: ·)

private theorem mem_wordsOfLength {alph : List B} (halph : ∀ b : B, b ∈ alph) :
    ∀ {n : ℕ} {v : List B}, v.length = n → v ∈ wordsOfLength alph n
  | 0, [], _ => by simp [wordsOfLength]
  | n + 1, b :: vs, hlen => by
    simp only [List.length_cons] at hlen
    have hvs : vs ∈ wordsOfLength alph n := mem_wordsOfLength halph (by omega)
    simp only [wordsOfLength, List.mem_flatMap, List.mem_map]
    exact ⟨b, halph b, vs, hvs, rfl⟩

private theorem length_wordsOfLength (alph : List B) (n : ℕ) :
    (wordsOfLength alph n).length = alph.length ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    have haux : ∀ l : List B,
        (l.flatMap fun b ↦ (wordsOfLength alph n).map (b :: ·)).length =
          l.length * (wordsOfLength alph n).length := by
      intro l
      induction l with
      | nil => simp
      | cons b bs ihb =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ihb]
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [wordsOfLength, haux, ih, Nat.pow_succ, Nat.mul_comm]

private theorem finite_words_length_lt [Finite B] (N : ℕ) :
    {v : List B | v.length < N}.Finite := by
  classical
  have := Fintype.ofFinite B
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let alph : List B := (List.finRange (Fintype.card B)).map e.symm
  have halph : ∀ b : B, b ∈ alph := by
    intro b
    simp only [alph, List.mem_map]
    exact ⟨e b, List.mem_finRange (e b), e.symm_apply_apply b⟩
  let allBounded : List (List B) := (List.range N).flatMap (wordsOfLength alph)
  refine allBounded.toFinset.finite_toSet.subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Finset.mem_coe, List.mem_toFinset, allBounded, List.mem_flatMap, List.mem_range]
  exact ⟨v.length, hv, mem_wordsOfLength halph rfl⟩

/-- Over any finite alphabet `B`, `w` is unavoidable for `Set.univ : Set (List B)` if and only if
there exists a threshold length `N` such that every word over `B` of length at least `N` reflects
`w`. -/
theorem isUnavoidableFor_univ_iff_exists_length [Finite B] {w : List A} :
    IsUnavoidableFor (Set.univ : Set (List B)) w ↔
      ∃ N : ℕ, ∀ v : List B, N ≤ v.length → Reflects v w := by
  constructor
  · intro hfin
    have hlen_fin : (List.length '' {v : List B | ¬ Reflects v w}).Finite := by
      have heq : {v : List B | ¬ Reflects v w} =
          {v ∈ (Set.univ : Set (List B)) | ¬ Reflects v w} := by
        ext v; simp
      rw [heq]
      exact hfin.image List.length
    obtain ⟨N, hN⟩ := exists_gt_of_finset hlen_fin.toFinset
    refine ⟨N, fun v hv ↦ ?_⟩
    by_contra hnr
    have hmem : v.length ∈ hlen_fin.toFinset :=
      hlen_fin.mem_toFinset.mpr ⟨v, hnr, rfl⟩
    have := hN v.length hmem
    omega
  · rintro ⟨N, hN⟩
    refine (finite_words_length_lt (B := B) N).subset ?_
    rintro v ⟨_, hnr⟩
    simp only [Set.mem_ofPred_eq]
    by_contra! hle
    exact hnr (hN v hle)

/-- Over any finite alphabet `B`, an unavoidable pattern is reflected by every sufficiently long
word over `B`. -/
theorem IsUnavoidable.exists_length_forall_reflects [Finite B] {w : List A}
    (hw : IsUnavoidable w) : ∃ N : ℕ, ∀ v : List B, N ≤ v.length → Reflects v w :=
  isUnavoidableFor_univ_iff_exists_length.mp hw.isUnavoidableFor_univ

/-- The empty word is unavoidable. -/
@[simp]
theorem isUnavoidable_nil : IsUnavoidable ([] : List A) := by
  intro k
  rw [isUnavoidableFor_univ_iff_exists_length]
  exact ⟨0, fun v _ ↦ reflects_nil v⟩

/-- Every single-letter pattern is unavoidable. -/
@[simp]
theorem isUnavoidable_singleton (x : A) : IsUnavoidable [x] := by
  intro k
  rw [isUnavoidableFor_univ_iff_exists_length]
  refine ⟨1, fun v hv ↦ ?_⟩
  match v with
  | [] => simp at hv
  | b :: bs =>
    refine ⟨fun _ ↦ [b], fun _ _ ↦ List.cons_ne_nil _ _, ?_⟩
    exact ⟨[], bs, by simp⟩

/-- If `v` reflects `u` and `v` is unavoidable, then `u` is unavoidable. -/
theorem Reflects.isUnavoidable {u : List A} {v : List B} (huv : Reflects v u)
    (hv : IsUnavoidable v) : IsUnavoidable u := by
  intro k
  refine (hv k).subset ?_
  rintro w ⟨_, hnr⟩
  exact ⟨trivial, fun hwu ↦ hnr (huv.trans hwu)⟩

/-- Injective letter renaming preserves unavoidability in both directions. -/
theorem isUnavoidable_map_iff {f : A → B} (hf : Function.Injective f) {w : List A} :
    IsUnavoidable (w.map f) ↔ IsUnavoidable w :=
  ⟨(reflects_map f w).isUnavoidable, (Reflects.of_injective_map hf w).isUnavoidable⟩

/-- Any pattern containing an adjacent repeated letter `[x, x]` is avoidable (via Thue's ternary
square-free words). -/
theorem isAvoidable_of_pair_infix {w : List A} {x : A} (hx : [x, x] <:+: w) :
    IsAvoidable w := by
  refine isAvoidable_of_infinite_not_reflects infinite_setOf_isSquareFree ?_
  intro v hv ⟨φ, hφ, hinf⟩
  have hv_sq : IsSquareFree v := hv
  have hxw : x ∈ w := hx.subset (by simp)
  have hne : φ x ≠ [] := hφ x hxw
  have hsq : φ x ++ φ x <:+: v := by
    have hpair : [x, x].flatMap φ <:+: w.flatMap φ := isInfix_flatMap hx φ
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hpair
    exact hpair.trans hinf
  rw [isSquareFree_iff] at hv_sq
  exact hv_sq (φ x) hne hsq

end ReflectionAndAvoidability

section OperationsAndFreeSets

variable {A B : Type*}

/-- Delete all occurrences of letters belonging to `X : Set A` from `w : List A` (`w^X`). -/
noncomputable def deleteLetters (X : Set A) (w : List A) : List A := by
  classical exact w.filter (fun a ↦ ¬ decide (a ∈ X))

/-- Delete all occurrences of a single letter `x : A` from `w : List A` (`w^x`). -/
noncomputable def deleteLetter (x : A) (w : List A) : List A :=
  deleteLetters {x} w

/-- Singleton-set characterization of `deleteLetter`. -/
theorem deleteLetter_eq_deleteLetters (x : A) (w : List A) :
    deleteLetter x w = deleteLetters {x} w := by
  rfl

/-- Replace every occurrence of `x` in `w` by `y` (letter identification). -/
noncomputable def identifyLetters (x y : A) (w : List A) : List A := by
  classical exact w.map (fun a ↦ if a = x then y else a)

/-- Deleting any letter set from `[]` yields `[]`. -/
@[simp]
theorem deleteLetters_nil (X : Set A) : deleteLetters X ([] : List A) = [] := by
  simp [deleteLetters]

/-- `deleteLetters` distributes over word concatenation. -/
@[simp]
theorem deleteLetters_append (X : Set A) (u v : List A) :
    deleteLetters X (u ++ v) = deleteLetters X u ++ deleteLetters X v := by
  simp [deleteLetters]

/-- `deleteLetters X` drops a head letter belonging to `X`. -/
theorem deleteLetters_cons_of_mem {X : Set A} {a : A} (ha : a ∈ X) (w : List A) :
    deleteLetters X (a :: w) = deleteLetters X w := by
  classical simp [deleteLetters, ha]

/-- `deleteLetters X` retains a head letter outside `X`. -/
theorem deleteLetters_cons_of_not_mem {X : Set A} {a : A} (ha : a ∉ X) (w : List A) :
    deleteLetters X (a :: w) = a :: deleteLetters X w := by
  classical simp [deleteLetters, ha]

/-- Membership in `deleteLetters X w` holds iff the letter lies in `w` and outside `X`. -/
@[simp]
theorem mem_deleteLetters {X : Set A} {w : List A} {a : A} :
    a ∈ deleteLetters X w ↔ a ∈ w ∧ a ∉ X := by
  classical simp [deleteLetters]

/-- Deleting letters does not increase word length. -/
theorem length_deleteLetters_le (X : Set A) (w : List A) :
    (deleteLetters X w).length ≤ w.length := by
  classical exact List.length_filter_le _ _

/-- Computable `List.filter` characterization of `deleteLetters` under `[DecidablePred (· ∈ X)]`.
-/
theorem deleteLetters_eq_filter (X : Set A) [DecidablePred (· ∈ X)] (w : List A) :
    deleteLetters X w = w.filter (fun a ↦ ¬ decide (a ∈ X)) := by
  induction w with
  | nil => simp
  | cons a as ih =>
    by_cases ha : a ∈ X
    · rw [deleteLetters_cons_of_mem ha]
      simp [ha, ih]
    · rw [deleteLetters_cons_of_not_mem ha]
      simp [ha, ih]

/-- Deleting `X` then `Y` equals deleting `X ∪ Y`. -/
theorem deleteLetters_deleteLetters (X Y : Set A) (w : List A) :
    deleteLetters Y (deleteLetters X w) = deleteLetters (X ∪ Y) w := by
  induction w with
  | nil => simp
  | cons a as ih =>
    by_cases haX : a ∈ X
    · rw [deleteLetters_cons_of_mem haX, deleteLetters_cons_of_mem (Or.inl haX), ih]
    · rw [deleteLetters_cons_of_not_mem haX]
      by_cases haY : a ∈ Y
      · rw [deleteLetters_cons_of_mem haY, deleteLetters_cons_of_mem (Or.inr haY), ih]
      · have haXY : a ∉ X ∪ Y := by simp [haX, haY]
        rw [deleteLetters_cons_of_not_mem haY, deleteLetters_cons_of_not_mem haXY, ih]

/-- If no letter of `X` occurs in `w`, `deleteLetters X w = w`. -/
theorem deleteLetters_eq_self {X : Set A} {w : List A} (h : ∀ a ∈ w, a ∉ X) :
    deleteLetters X w = w := by
  induction w with
  | nil => simp
  | cons a as ih =>
    rw [deleteLetters_cons_of_not_mem (h a (by simp)), ih (fun b hb ↦ h b (by simp [hb]))]

/-- Factor containment is preserved under `deleteLetters`. -/
theorem IsInfix.deleteLetters {u v : List A} (h : u <:+: v) (X : Set A) :
    Word.deleteLetters X u <:+: Word.deleteLetters X v := by
  rcases h with ⟨l₁, l₂, rfl⟩
  exact ⟨Word.deleteLetters X l₁, Word.deleteLetters X l₂, by simp⟩

/-- Deleting `x` from `[]` yields `[]`. -/
@[simp]
theorem deleteLetter_nil (x : A) : deleteLetter x ([] : List A) = [] :=
  deleteLetters_nil {x}

/-- `deleteLetter` distributes over word concatenation. -/
@[simp]
theorem deleteLetter_append (x : A) (u v : List A) :
    deleteLetter x (u ++ v) = deleteLetter x u ++ deleteLetter x v :=
  deleteLetters_append {x} u v

/-- `deleteLetter x` drops a matching head letter `x`. -/
theorem deleteLetter_cons_eq (x : A) (w : List A) :
    deleteLetter x (x :: w) = deleteLetter x w :=
  deleteLetters_cons_of_mem (Set.mem_singleton x) w

/-- `deleteLetter x` retains any head letter `a ≠ x`. -/
theorem deleteLetter_cons_ne {x a : A} (hne : a ≠ x) (w : List A) :
    deleteLetter x (a :: w) = a :: deleteLetter x w :=
  deleteLetters_cons_of_not_mem (by simpa using hne) w

/-- Membership in `deleteLetter x w` holds iff the letter lies in `w` and differs from `x`. -/
@[simp]
theorem mem_deleteLetter {x a : A} {w : List A} :
    a ∈ deleteLetter x w ↔ a ∈ w ∧ a ≠ x := by
  simp [deleteLetter]

/-- Computable `List.filter` characterization of `deleteLetter` under `[DecidableEq A]`. -/
theorem deleteLetter_eq_filter [DecidableEq A] (x : A) (w : List A) :
    deleteLetter x w = w.filter (· ≠ x) := by
  induction w with
  | nil => simp
  | cons a as ih =>
    by_cases hax : a = x
    · subst hax; simp [deleteLetter_cons_eq, ih]
    · simp [deleteLetter_cons_ne hax, hax, ih]

/-- Letter identification on `[]` yields `[]`. -/
@[simp]
theorem identifyLetters_nil (x y : A) : identifyLetters x y ([] : List A) = [] := by
  simp [identifyLetters]

/-- `identifyLetters` distributes over word concatenation. -/
@[simp]
theorem identifyLetters_append (x y : A) (u v : List A) :
    identifyLetters x y (u ++ v) = identifyLetters x y u ++ identifyLetters x y v := by
  simp [identifyLetters]

/-- `identifyLetters x y` replaces a head `x` by `y`. -/
theorem identifyLetters_cons_eq (x y : A) (w : List A) :
    identifyLetters x y (x :: w) = y :: identifyLetters x y w := by
  classical simp [identifyLetters]

/-- `identifyLetters x y` leaves any head `a ≠ x` unchanged. -/
theorem identifyLetters_cons_ne {x y a : A} (hne : a ≠ x) (w : List A) :
    identifyLetters x y (a :: w) = a :: identifyLetters x y w := by
  classical simp [identifyLetters, hne]

/-- Computable `List.map` characterization of `identifyLetters` under `[DecidableEq A]`. -/
theorem identifyLetters_eq_map [DecidableEq A] (x y : A) (w : List A) :
    identifyLetters x y w = w.map (fun a ↦ if a = x then y else a) := by
  induction w with
  | nil => simp
  | cons a as ih =>
    by_cases hax : a = x
    · subst hax; simp [identifyLetters_cons_eq, ih]
    · simp [identifyLetters_cons_ne hax, hax, ih]

/-- `identifyLetters x y w` always reflects `w`. -/
theorem reflects_identifyLetters (x y : A) (w : List A) :
    Reflects (identifyLetters x y w) w := by
  classical
  simpa [identifyLetters] using reflects_map (fun a ↦ if a = x then y else a) w

/-- Existence of an alternating `2`-factor chain `x a₁, b₁ a₁, b₁ a₂, …, b_{n-1} a_n, b_n a_n,
b_n y` (`n > 0`) among the contiguous `2`-factors of `w`. -/
def HasAlternatingChain (w : List A) (x y : A) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (a b : Fin n → A),
    [x, a ⟨0, hn⟩] <:+: w ∧
    (∀ i : Fin n, [b i, a i] <:+: w) ∧
    (∀ (i : ℕ) (hi : i + 1 < n), [b ⟨i, Nat.lt_of_succ_lt hi⟩, a ⟨i + 1, hi⟩] <:+: w) ∧
    [b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩, y] <:+: w

/-- A letter `x : A` is *free for* `w : List A` if `x` occurs in `w` and has no alternating
`2`-factor chain from `x` back to `x` in `w`. -/
def IsFreeLetter (w : List A) (x : A) : Prop :=
  x ∈ w ∧ ¬ HasAlternatingChain w x x

/-- Unfolded characterization of `IsFreeLetter`. -/
theorem isFreeLetter_iff {w : List A} {x : A} :
    IsFreeLetter w x ↔ x ∈ w ∧ ¬ HasAlternatingChain w x x := by
  rfl

/-- A set of letters `X : Set A` is *free for* `w : List A` if no pair `x, y ∈ X` is linked by an
alternating `2`-factor chain in `w`. -/
def IsFreeSet (w : List A) (X : Set A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ¬ HasAlternatingChain w x y

/-- Unfolded characterization of `IsFreeSet`. -/
theorem isFreeSet_iff {w : List A} {X : Set A} :
    IsFreeSet w X ↔ ∀ x ∈ X, ∀ y ∈ X, ¬ HasAlternatingChain w x y := by
  rfl

/-- A letter `x` occurring in `w` is free if and only if `{x}` is a free set for `w`. -/
theorem isFreeLetter_iff_singleton_isFreeSet {w : List A} {x : A} :
    IsFreeLetter w x ↔ x ∈ w ∧ IsFreeSet w {x} := by
  simp [IsFreeLetter, IsFreeSet]

/-- Every letter of a free set `X` that occurs in `w` is a free letter for `w`. -/
theorem IsFreeSet.isFreeLetter {w : List A} {X : Set A} (hX : IsFreeSet w X) {x : A}
    (hxX : x ∈ X) (hxw : x ∈ w) : IsFreeLetter w x :=
  ⟨hxw, hX x hxX x hxX⟩

/-- Every subset of a free set is a free set. -/
theorem IsFreeSet.mono {w : List A} {X Y : Set A} (hY : IsFreeSet w Y) (hXY : X ⊆ Y) :
    IsFreeSet w X :=
  fun x hx y hy ↦ hY x (hXY hx) y (hXY hy)

/-- Any direct `2`-factor `[x, y] <:+: w` yields a length-`1` alternating chain from `x` to `y`.
-/
theorem hasAlternatingChain_of_pair_infix {w : List A} {x y : A} (hxy : [x, y] <:+: w) :
    HasAlternatingChain w x y := by
  refine ⟨1, Nat.one_pos, fun _ ↦ y, fun _ ↦ x, hxy, fun _ ↦ hxy, ?_, hxy⟩
  intro i hi
  omega

/-- No two letters of a free set can occur adjacently in `w`. -/
theorem IsFreeSet.not_pair_infix {w : List A} {X : Set A} (hX : IsFreeSet w X) {x y : A}
    (hx : x ∈ X) (hy : y ∈ X) : ¬ ([x, y] <:+: w) :=
  fun hxy ↦ hX x hx y hy (hasAlternatingChain_of_pair_infix hxy)

/-- Shared-right-neighbor step `∃ c, [u, c] <:+: w ∧ [v, c] <:+: w` on left components of
`2`-factors of `w`. -/
def SameRightNeighbor (w : List A) (u v : A) : Prop :=
  ∃ c : A, [u, c] <:+: w ∧ [v, c] <:+: w

/-- Unfolded characterization of `SameRightNeighbor`. -/
theorem sameRightNeighbor_iff {w : List A} {u v : A} :
    SameRightNeighbor w u v ↔ ∃ c : A, [u, c] <:+: w ∧ [v, c] <:+: w := by
  rfl

/-- Graph-reachability characterization of `HasAlternatingChain`: an alternating `2`-factor chain
from `x` to `y` exists if and only if some `b` reachable from `x` via `SameRightNeighbor w` steps
satisfies `[b, y] <:+: w`. -/
theorem hasAlternatingChain_iff_reflTransGen {w : List A} {x y : A} :
    HasAlternatingChain w x y ↔
      ∃ b : A, Relation.ReflTransGen (SameRightNeighbor w) x b ∧ [b, y] <:+: w := by
  constructor
  · rintro ⟨n, hn, a, b, hxa0, hba, hstep, hby⟩
    have hreach : ∀ (j : ℕ) (hj : j < n),
        Relation.ReflTransGen (SameRightNeighbor w) x (b ⟨j, hj⟩) := by
      intro j
      induction j with
      | zero =>
        intro hj
        exact Relation.ReflTransGen.single ⟨a ⟨0, hn⟩, hxa0, hba ⟨0, hj⟩⟩
      | succ j ih =>
        intro hj
        exact (ih (Nat.lt_of_succ_lt hj)).tail ⟨a ⟨j + 1, hj⟩, hstep j hj, hba ⟨j + 1, hj⟩⟩
    exact ⟨b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩, hreach (n - 1) (Nat.sub_lt hn Nat.one_pos), hby⟩
  · rintro ⟨b, hxb, hby⟩
    induction hxb using Relation.ReflTransGen.head_induction_on with
    | refl => exact hasAlternatingChain_of_pair_infix hby
    | @head x₁ x₂ hstep _ ih =>
      rcases hstep with ⟨c, hxc, hx'c⟩
      rcases ih with ⟨n, hn, a', b', hx'a0, hba', hstep', hb'y⟩
      let aNew : Fin (n + 1) → A := Fin.cases c a'
      let bNew : Fin (n + 1) → A := Fin.cases x₂ b'
      refine ⟨n + 1, Nat.succ_pos n, aNew, bNew, ?_, ?_, ?_, ?_⟩
      · simpa [aNew] using hxc
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa [aNew, bNew] using hx'c
        · intro j
          simpa [aNew, bNew] using hba' j
      · intro i hi
        cases i with
        | zero =>
          have h0 : (⟨1, hi⟩ : Fin (n + 1)) = Fin.succ ⟨0, hn⟩ := rfl
          rw [h0]
          simpa [aNew, bNew] using hx'a0
        | succ k =>
          have hk : k + 1 < n := by omega
          have h1 : (⟨k + 1, Nat.lt_of_succ_lt hi⟩ : Fin (n + 1)) =
              Fin.succ ⟨k, Nat.lt_of_succ_lt hk⟩ := rfl
          have h2 : (⟨k + 2, hi⟩ : Fin (n + 1)) = Fin.succ ⟨k + 1, hk⟩ := rfl
          rw [h1, h2]
          simpa [aNew, bNew] using hstep' k hk
      · have hlast : (⟨n + 1 - 1, Nat.sub_lt (Nat.succ_pos n) Nat.one_pos⟩ : Fin (n + 1)) =
            Fin.succ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := by
          ext; simp; omega
        rw [hlast]
        simpa [bNew] using hb'y

/-- Boundary-cancelling telescoping identity for word morphisms along any nonempty word `v`. -/
theorem flatMap_telescoping {δR δL ψ φ₀ : A → List B} :
    ∀ (v : List A) (hv : v ≠ []),
      (∀ z ∈ v, δR z ++ ψ z = φ₀ z ++ δL z) →
      (∀ y z : A, [y, z] <:+: v → δL y = δR z) →
      δR (v.head hv) ++ v.flatMap ψ = v.flatMap φ₀ ++ δL (v.getLast hv)
  | [], hne, _, _ => absurd rfl hne
  | [z], _, hletter, _ => by
    simpa [List.flatMap_cons, List.flatMap_nil] using hletter z (by simp)
  | y :: z :: rest, _, hletter, hadj => by
    have hne' : z :: rest ≠ [] := List.cons_ne_nil _ _
    have hpair : [y, z] <:+: y :: z :: rest := ⟨[], rest, rfl⟩
    have hyz : δL y = δR z := hadj y z hpair
    have hih := flatMap_telescoping (z :: rest) hne'
      (fun u hu ↦ hletter u (List.mem_cons_of_mem y hu))
      (fun u₁ u₂ hu ↦ hadj u₁ u₂ (hu.trans ⟨[y], [], by simp⟩))
    simp only [List.head_cons, List.flatMap_cons] at hih ⊢
    have hlast : (y :: z :: rest).getLast (List.cons_ne_nil _ _) =
        (z :: rest).getLast hne' := List.getLast_cons hne'
    rw [hlast, ← List.append_assoc, hletter y (by simp), List.append_assoc, hyz, hih,
      ← List.append_assoc]

/-- **Telescoping Block-Morphism Lemma**: if `X` is a free set
for
`w : List A` and every letter `z ∈ w` outside `X` maps under `φ` to a word `a :: u z` starting
with
`a : B` of length at least `2` (`u z ≠`), then there exists a morphism `ψ : A → List B` sending
every letter of `w` to a nonempty word such that
`w.flatMap ψ <:+: (deleteLetters X w).flatMap φ ++ [a]`.
-/
theorem reflects_append_singleton_of_isFreeSet {w : List A} {X : Set A} (hX : IsFreeSet w X)
    (a : B) {φ : A → List B} (hφ : ∀ z ∈ w, z ∉ X → ∃ u : List B, u ≠ [] ∧ φ z = a :: u) :
    ∃ ψ : A → List B, (∀ z ∈ w, ψ z ≠ []) ∧
      w.flatMap ψ <:+: (deleteLetters X w).flatMap φ ++ [a] := by
  classical
  by_cases hw : w = []
  · subst hw
    exact ⟨fun _ ↦ [a], by simp, by simp⟩
  let uFn : A → List B := fun z ↦
    if hz : z ∈ w ∧ z ∉ X then (hφ z hz.1 hz.2).choose else [a]
  have hu_ne : ∀ z ∈ w, z ∉ X → uFn z ≠ [] := by
    intro z hzw hzX
    have hz : z ∈ w ∧ z ∉ X := ⟨hzw, hzX⟩
    simpa [uFn, hz] using (hφ z hzw hzX).choose_spec.1
  have hu_eq : ∀ z ∈ w, z ∉ X → φ z = a :: uFn z := by
    intro z hzw hzX
    have hz : z ∈ w ∧ z ∉ X := ⟨hzw, hzX⟩
    simpa [uFn, hz] using (hφ z hzw hzX).choose_spec.2
  let SL : Set A := {u : A | ∃ x ∈ X, Relation.ReflTransGen (SameRightNeighbor w) x u}
  let SR : Set A := {c : A | ∃ u ∈ SL, [u, c] <:+: w}
  have hX_SL : ∀ x ∈ X, x ∈ SL := fun x hx ↦ ⟨x, hx, Relation.ReflTransGen.refl⟩
  have hX_not_SR : ∀ y ∈ X, y ∉ SR := by
    rintro y hy ⟨u, ⟨x, hx, hxu⟩, huy⟩
    exact hX x hx y hy (hasAlternatingChain_iff_reflTransGen.mpr ⟨u, hxu, huy⟩)
  have hSL_iff_SR : ∀ y z : A, [y, z] <:+: w → (y ∈ SL ↔ z ∈ SR) := by
    intro y z hyz
    constructor
    · intro hy
      exact ⟨y, hy, hyz⟩
    · rintro ⟨u, ⟨x, hx, hxu⟩, huz⟩
      exact ⟨x, hx, hxu.tail ⟨z, huz, hyz⟩⟩
  let δR : A → List B := fun z ↦ if z ∈ SR then [a] else []
  let δL : A → List B := fun z ↦ if z ∈ SL then [a] else []
  let φ₀ : A → List B := fun z ↦ if z ∈ X then [] else a :: uFn z
  let ψ : A → List B := fun z ↦
    if z ∈ X then [a] else (if z ∈ SR then [] else [a]) ++ uFn z ++ δL z
  have hψ_ne : ∀ z ∈ w, ψ z ≠ [] := by
    intro z hzw
    by_cases hzX : z ∈ X
    · simp [ψ, hzX]
    · simp only [ψ, hzX, ↓reduceIte]
      have hne := hu_ne z hzw hzX
      intro hemp
      simp only [List.append_eq_nil_iff] at hemp
      exact hne hemp.1.2
  have hletter : ∀ z ∈ w, δR z ++ ψ z = φ₀ z ++ δL z := by
    intro z _
    by_cases hzX : z ∈ X
    · have h1 : z ∈ SL := hX_SL z hzX
      have h2 : z ∉ SR := hX_not_SR z hzX
      simp [δR, δL, φ₀, ψ, hzX, h1, h2]
    · by_cases hzR : z ∈ SR <;> simp [δR, φ₀, ψ, hzX, hzR]
  have hadj : ∀ y z : A, [y, z] <:+: w → δL y = δR z := by
    intro y z hyz
    simp [δL, δR, hSL_iff_SR y z hyz]
  have htel := flatMap_telescoping w hw hletter hadj
  have hflat_del : w.flatMap φ₀ = (deleteLetters X w).flatMap φ := by
    have haux : ∀ l : List A, (∀ z ∈ l, z ∈ w) →
        l.flatMap φ₀ = (deleteLetters X l).flatMap φ := by
      intro l hl
      induction l with
      | nil => simp
      | cons z zs ih =>
        by_cases hzX : z ∈ X
        · rw [deleteLetters_cons_of_mem hzX]
          simp [φ₀, hzX, ih (fun u hu ↦ hl u (by simp [hu]))]
        · rw [deleteLetters_cons_of_not_mem hzX]
          simp only [List.flatMap_cons, φ₀, hzX, ↓reduceIte]
          rw [hu_eq z (hl z (by simp)) hzX, ih (fun u hu ↦ hl u (by simp [hu]))]
    exact haux w (fun _ hz ↦ hz)
  rw [hflat_del] at htel
  refine ⟨ψ, hψ_ne, ?_⟩
  let restTail : List B := if w.getLast hw ∈ SL then [] else [a]
  have htail_a : δL (w.getLast hw) ++ restTail = [a] := by
    by_cases hlast : w.getLast hw ∈ SL <;> simp [δL, restTail, hlast]
  refine ⟨δR (w.head hw), restTail, ?_⟩
  rw [htel, List.append_assoc, htail_a]

end OperationsAndFreeSets

section ZiminAndReducibility

variable {A : Type*}

/-- Canonical Zimin words `ziminWord k : List ℕ` (`Z_0 = []`, `Z_{k+1} = Z_k ++ [k] ++ Z_k`). -/
def ziminWord : ℕ → List ℕ
  | 0 => []
  | k + 1 => ziminWord k ++ [k] ++ ziminWord k

/-- The `0`-th Zimin word is empty. -/
@[simp]
theorem ziminWord_zero : ziminWord 0 = [] := by
  rfl

/-- Recursive unfolding `ziminWord (k + 1) = ziminWord k ++ [k] ++ ziminWord k`. -/
theorem ziminWord_succ (k : ℕ) : ziminWord (k + 1) = ziminWord k ++ [k] ++ ziminWord k := by
  rfl

/-- Length of the `k`-th Zimin word is `2 ^ k - 1`. -/
@[simp]
theorem length_ziminWord (k : ℕ) : (ziminWord k).length = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ziminWord_succ, List.length_append, List.length_singleton, ih, Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    omega

/-- Every letter occurring in `ziminWord k` is strictly less than `k`. -/
theorem mem_ziminWord_lt {k m : ℕ} (hm : m ∈ ziminWord k) : m < k := by
  induction k with
  | zero => simp at hm
  | succ k ih =>
    simp only [ziminWord_succ, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | rfl) | hm
    · exact Nat.lt_succ_of_lt (ih hm)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (ih hm)

/-- Interleaved `0`-block expansion
`ziminWord (k + 1) = (ziminWord k).flatMap (fun m ↦ [0, m + 1]) ++ [0]`. -/
theorem ziminWord_succ_eq_flatMap (k : ℕ) :
    ziminWord (k + 1) = (ziminWord k).flatMap (fun m ↦ [0, m + 1]) ++ [0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      ziminWord (k + 2)
          = ziminWord (k + 1) ++ [k + 1] ++ ziminWord (k + 1) := rfl
      _ = ((ziminWord k).flatMap (fun m ↦ [0, m + 1]) ++ [0]) ++ [k + 1] ++
            ((ziminWord k).flatMap (fun m ↦ [0, m + 1]) ++ [0]) := by rw [ih]
      _ = (ziminWord k ++ [k] ++ ziminWord k).flatMap (fun m ↦ [0, m + 1]) ++ [0] := by
        simp [List.flatMap_append, List.append_assoc]
      _ = (ziminWord (k + 1)).flatMap (fun m ↦ [0, m + 1]) ++ [0] := rfl

private theorem isInfix_flatMap_zero_succ {s v : List ℕ} (h : s <:+: v) :
    s.flatMap (fun m ↦ [0, m + 1]) ++ [0] <:+: v.flatMap (fun m ↦ [0, m + 1]) ++ [0] := by
  rcases h with ⟨l₁, l₂, rfl⟩
  match l₂ with
  | [] =>
    refine ⟨l₁.flatMap (fun m ↦ [0, m + 1]), [], ?_⟩
    simp [List.flatMap_append, List.append_assoc]
  | m₂ :: l₂' =>
    refine ⟨l₁.flatMap (fun m ↦ [0, m + 1]),
      [m₂ + 1] ++ l₂'.flatMap (fun m ↦ [0, m + 1]) ++ [0], ?_⟩
    simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- If `X` is a free set for `w` and `ziminWord k` reflects `deleteLetters X w`, then
`ziminWord (k + 1)` reflects `w`. -/
theorem IsFreeSet.reflects_ziminWord_succ {w : List A} {X : Set A} (hX : IsFreeSet w X) {k : ℕ}
    (hk : Reflects (ziminWord k) (deleteLetters X w)) : Reflects (ziminWord (k + 1)) w := by
  rcases hk with ⟨φ₀, hφ₀, hinf₀⟩
  let φ : A → List ℕ := fun z ↦ (φ₀ z).flatMap (fun m ↦ [0, m + 1])
  have hφ_form : ∀ z ∈ w, z ∉ X → ∃ u : List ℕ, u ≠ [] ∧ φ z = 0 :: u := by
    intro z hzw hzX
    have hmem : z ∈ deleteLetters X w := mem_deleteLetters.mpr ⟨hzw, hzX⟩
    have hne := hφ₀ z hmem
    match h_eq : φ₀ z with
    | [] => exact absurd h_eq hne
    | m₀ :: ms =>
      refine ⟨(m₀ + 1) :: ms.flatMap (fun m ↦ [0, m + 1]), List.cons_ne_nil _ _, ?_⟩
      simp [φ, h_eq, List.flatMap_cons]
  obtain ⟨ψ, hψ, hinf⟩ := reflects_append_singleton_of_isFreeSet hX 0 hφ_form
  refine ⟨ψ, hψ, ?_⟩
  rw [ziminWord_succ_eq_flatMap]
  have hflat : (deleteLetters X w).flatMap φ =
      ((deleteLetters X w).flatMap φ₀).flatMap (fun m ↦ [0, m + 1]) :=
    (flatMap_flatMap (deleteLetters X w) φ₀ (fun m ↦ [0, m + 1])).symm
  rw [hflat] at hinf
  exact hinf.trans (isInfix_flatMap_zero_succ hinf₀)

/-- Reducibility of a pattern to `` by iteratively deleting free sets
.
-/
inductive IsFreeSetReducible : List A → Prop where
  | nil : IsFreeSetReducible []
  | delete_freeSet {w : List A} {X : Set A} :
      IsFreeSet w X → IsFreeSetReducible (deleteLetters X w) → IsFreeSetReducible w

/-- Reducibility of a pattern to `` by iteratively deleting a free letter or identifying two
distinct letters occurring in the pattern.
-/
inductive IsBEMReducible : List A → Prop where
  | nil : IsBEMReducible []
  | delete_freeLetter {w : List A} {x : A} :
      IsFreeLetter w x → IsBEMReducible (deleteLetter x w) → IsBEMReducible w
  | identify_letters {w : List A} {x y : A} :
      x ∈ w → y ∈ w → x ≠ y → IsBEMReducible (identifyLetters x y w) → IsBEMReducible w

private theorem zero_alt_in_interleaved :
    ∀ (l : List ℕ) {p q : ℕ}, [p, q] <:+: l.flatMap (fun m ↦ [0, m + 1]) ++ [0] →
      (p = 0 ↔ q ≠ 0)
  | [], p, q, h => by
    rcases h with ⟨s, t, hst⟩
    have hlen := congrArg List.length hst
    simp only [List.length_append, List.length_cons, List.length_nil, List.flatMap_nil] at hlen
    omega
  | m :: ms, p, q, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h
    rcases h with ⟨s, t, hst⟩
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
      rcases hst with ⟨rfl, rfl, _⟩
      omega
    | cons a₀ s' =>
      simp only [List.cons_append, List.cons.injEq] at hst
      rcases hst with ⟨rfl, hst'⟩
      cases s' with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst'
        rcases hst' with ⟨rfl, hst''⟩
        have hq0 : q = 0 := by
          cases ms with
          | nil =>
            simp only [List.flatMap_nil, List.nil_append, List.cons.injEq] at hst''
            exact hst''.1
          | cons m' ms' =>
            simp only [List.flatMap_cons, List.cons_append, List.cons.injEq] at hst''
            exact hst''.1
        omega
      | cons b₀ s'' =>
        simp only [List.cons_append, List.cons.injEq] at hst'
        rcases hst' with ⟨rfl, hrest⟩
        exact zero_alt_in_interleaved ms ⟨s'', t, hrest⟩

private theorem pair_getLast_head_infix {u v : List ℕ} (hu : u ≠ []) (hv : v ≠ []) :
    [u.getLast hu, v.head hv] <:+: u ++ v := by
  have hu_eq : u.dropLast ++ [u.getLast hu] = u := List.dropLast_append_getLast hu
  have hv_eq : v.head hv :: v.tail = v := List.cons_head_tail hv
  refine ⟨u.dropLast, v.tail, ?_⟩
  calc
    u.dropLast ++ [u.getLast hu, v.head hv] ++ v.tail
        = (u.dropLast ++ [u.getLast hu]) ++ (v.head hv :: v.tail) := by simp [List.append_assoc]
    _ = u ++ v := by rw [hu_eq, hv_eq]

private def unzeroWord : List ℕ → List ℕ :=
  List.filterMap fun n ↦ if n = 0 then none else some (n - 1)

private theorem unzeroWord_append (u v : List ℕ) :
    unzeroWord (u ++ v) = unzeroWord u ++ unzeroWord v :=
  List.filterMap_append

private theorem isInfix_unzeroWord {s v : List ℕ} (h : s <:+: v) :
    unzeroWord s <:+: unzeroWord v := by
  rcases h with ⟨l₁, l₂, rfl⟩
  exact ⟨unzeroWord l₁, unzeroWord l₂, by simp [unzeroWord_append]⟩

private theorem unzeroWord_ziminWord_succ (k : ℕ) :
    unzeroWord (ziminWord (k + 1)) = ziminWord k := by
  rw [ziminWord_succ_eq_flatMap, unzeroWord_append]
  have h0 : unzeroWord [0] = [] := rfl
  rw [h0, List.append_nil]
  induction ziminWord k with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.flatMap_cons, unzeroWord_append, ih]
    have hpair : unzeroWord [0, m + 1] = [m] := by simp [unzeroWord]
    rw [hpair]
    rfl

private theorem unzeroWord_flatMap (w : List A) (φ : A → List ℕ) :
    unzeroWord (w.flatMap φ) = w.flatMap (fun a ↦ unzeroWord (φ a)) := by
  induction w with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, unzeroWord_append, ih]

/-- Free-set reducibility is equivalent to reflection in some Zimin word `ziminWord k`. -/
theorem isFreeSetReducible_iff_exists_reflects_ziminWord {w : List A} :
    IsFreeSetReducible w ↔ ∃ k : ℕ, Reflects (ziminWord k) w := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨0, reflects_nil _⟩
    | delete_freeSet hX _ ih =>
      rcases ih with ⟨k, hk⟩
      exact ⟨k + 1, hX.reflects_ziminWord_succ hk⟩
  · rintro ⟨k, hk⟩
    induction k generalizing w with
    | zero =>
      have hlen := hk.length_le
      simp only [ziminWord_zero, List.length_nil] at hlen
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact IsFreeSetReducible.nil
    | succ k ih =>
      rcases hk with ⟨φ, hφ, hinf⟩
      let X : Set A := {x : A | φ x = [0]}
      have hpair_alt : ∀ u v : A, [u, v] <:+: w →
          ∀ (hu : φ u ≠ []) (hv : φ v ≠ []),
            ((φ u).getLast hu = 0 ↔ (φ v).head hv ≠ 0) := by
        intro u v huv hu hv
        have huv' : φ u ++ φ v <:+: ziminWord (k + 1) := by
          have h1 : [u, v].flatMap φ <:+: w.flatMap φ := isInfix_flatMap huv φ
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
          exact h1.trans hinf
        have h2 : [(φ u).getLast hu, (φ v).head hv] <:+: ziminWord (k + 1) :=
          (pair_getLast_head_infix hu hv).trans huv'
        rw [ziminWord_succ_eq_flatMap] at h2
        exact zero_alt_in_interleaved (ziminWord k) h2
      have hX_free : IsFreeSet w X := by
        intro x hxX y hyX hchain
        rcases hasAlternatingChain_iff_reflTransGen.mp hchain with ⟨b, hxb, hby⟩
        have hbw : b ∈ w := hby.subset (by simp)
        have hyw : y ∈ w := hby.subset (by simp)
        have hlast_zero : ∀ u : A, Relation.ReflTransGen (SameRightNeighbor w) x u →
            (u = x ∨ (u ∈ w ∧ ∀ hu : φ u ≠ [], (φ u).getLast hu = 0)) := by
          intro u hxu
          induction hxu with
          | refl => exact Or.inl rfl
          | @tail u₁ u₂ _ hstep ihu =>
            rcases hstep with ⟨c, hu₁c, hu₂c⟩
            have hu₁w : u₁ ∈ w := hu₁c.subset (by simp)
            have hu₂w : u₂ ∈ w := hu₂c.subset (by simp)
            have hcw : c ∈ w := hu₁c.subset (by simp)
            have hu₁_last : (φ u₁).getLast (hφ u₁ hu₁w) = 0 := by
              rcases ihu with rfl | ⟨_, hlast⟩
              · have hx0 : φ u₁ = [0] := hxX
                simp [hx0]
              · exact hlast (hφ u₁ hu₁w)
            have hc_head : (φ c).head (hφ c hcw) ≠ 0 :=
              (hpair_alt u₁ c hu₁c (hφ u₁ hu₁w) (hφ c hcw)).mp hu₁_last
            have hu₂_last : (φ u₂).getLast (hφ u₂ hu₂w) = 0 :=
              (hpair_alt u₂ c hu₂c (hφ u₂ hu₂w) (hφ c hcw)).mpr hc_head
            exact Or.inr ⟨hu₂w, fun _ ↦ hu₂_last⟩
        have hb_last : (φ b).getLast (hφ b hbw) = 0 := by
          rcases hlast_zero b hxb with rfl | ⟨_, hlast⟩
          · have hx0 : φ b = [0] := hxX
            simp [hx0]
          · exact hlast (hφ b hbw)
        have hy_head : (φ y).head (hφ y hyw) ≠ 0 :=
          (hpair_alt b y hby (hφ b hbw) (hφ y hyw)).mp hb_last
        have hy0 : φ y = [0] := hyX
        simp [hy0] at hy_head
      have href_del : Reflects (ziminWord k) (deleteLetters X w) := by
        refine ⟨fun a ↦ unzeroWord (φ a), ?_, ?_⟩
        · intro a ha
          rcases mem_deleteLetters.mp ha with ⟨haw, haX⟩
          have hne := hφ a haw
          intro hunz
          dsimp only at hunz
          apply haX
          have hall0 : ∀ m ∈ φ a, m = 0 := by
            intro m hm
            by_contra hm0
            have hmem : m - 1 ∈ unzeroWord (φ a) := by
              simp only [unzeroWord, List.mem_filterMap]
              exact ⟨m, hm, by simp [hm0]⟩
            rw [hunz] at hmem
            simp at hmem
          match h_eq : φ a with
          | [] => exact absurd h_eq hne
          | [m₀] =>
            have hm₀ : m₀ = 0 := hall0 m₀ (by simp [h_eq])
            simp [X, h_eq, hm₀]
          | m₀ :: m₁ :: ms =>
            have h0 : m₀ = 0 := hall0 m₀ (by simp [h_eq])
            have h1 : m₁ = 0 := hall0 m₁ (by simp [h_eq])
            have hsub : [0, 0] <:+: ziminWord (k + 1) := by
              have hp : [m₀, m₁] <:+: φ a := by
                rw [h_eq]
                exact ⟨[], ms, rfl⟩
              have hfa : φ a <:+: w.flatMap φ := by
                rcases List.append_of_mem haw with ⟨s₁, s₂, rfl⟩
                exact ⟨s₁.flatMap φ, s₂.flatMap φ, by simp [List.flatMap_append, List.flatMap_cons]⟩
              rw [h0, h1] at hp
              exact (hp.trans hfa).trans hinf
            rw [ziminWord_succ_eq_flatMap] at hsub
            have halt := zero_alt_in_interleaved (ziminWord k) hsub
            exact False.elim (halt.mp rfl rfl)
        · have heq : (deleteLetters X w).flatMap (fun a ↦ unzeroWord (φ a)) =
              unzeroWord (w.flatMap φ) := by
            rw [unzeroWord_flatMap]
            have haux : ∀ l : List A,
                (deleteLetters X l).flatMap (fun a ↦ unzeroWord (φ a)) =
                  l.flatMap (fun a ↦ unzeroWord (φ a)) := by
              intro l
              induction l with
              | nil => simp
              | cons a as ihl =>
                by_cases haX : a ∈ X
                · rw [deleteLetters_cons_of_mem haX]
                  have hz : unzeroWord (φ a) = [] := by
                    have ha0 : φ a = [0] := haX
                    rw [ha0]; rfl
                  simp [List.flatMap_cons, hz, ihl]
                · rw [deleteLetters_cons_of_not_mem haX]
                  simp [List.flatMap_cons, ihl]
            exact haux w
          rw [heq, ← unzeroWord_ziminWord_succ]
          exact isInfix_unzeroWord hinf
      exact IsFreeSetReducible.delete_freeSet hX_free (ih href_del)

private theorem nodup_length_le_of_subset {B : Type*} :
    ∀ {l₁ l₂ : List B}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l₂, hnd, hsub => by
    classical
    rcases List.nodup_cons.mp hnd with ⟨hx_xs, hnd_xs⟩
    have hx_l₂ : x ∈ l₂ := hsub x (by simp)
    have hsub_er : ∀ y ∈ xs, y ∈ l₂.erase x := by
      intro y hy
      have hne : y ≠ x := fun heq ↦ hx_xs (heq ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (by simp [hy]))
    have hle := nodup_length_le_of_subset hnd_xs hsub_er
    have her := List.length_erase_of_mem hx_l₂
    have hpos : 0 < l₂.length := List.length_pos_of_mem hx_l₂
    simp only [List.length_cons]
    omega

private theorem exists_getElem_eq_of_not_nodup {B : Type*} :
    ∀ {l : List B}, ¬ l.Nodup →
      ∃ (i₁ i₂ : ℕ) (h₁ : i₁ < i₂) (h₂ : i₂ < l.length), l[i₁]'(Nat.lt_trans h₁ h₂) = l[i₂]'h₂
  | [], h => absurd List.nodup_nil h
  | x :: xs, h => by
    classical
    by_cases hmem : x ∈ xs
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
      exact ⟨0, j + 1, Nat.succ_pos j, Nat.succ_lt_succ hj, rfl⟩
    · have hnd_xs : ¬ xs.Nodup := fun hnd ↦ h (List.nodup_cons.mpr ⟨hmem, hnd⟩)
      obtain ⟨i₁, i₂, hlt, h₂, heq⟩ := exists_getElem_eq_of_not_nodup hnd_xs
      exact ⟨i₁ + 1, i₂ + 1, Nat.succ_lt_succ hlt, Nat.succ_lt_succ h₂, heq⟩

/-- Every canonical Zimin word `ziminWord k` is unavoidable. -/
theorem isUnavoidable_ziminWord (k : ℕ) : IsUnavoidable (ziminWord k) := by
  induction k with
  | zero => exact isUnavoidable_nil
  | succ k ih =>
    intro r
    rw [isUnavoidableFor_univ_iff_exists_length]
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨1, fun v hv ↦ ?_⟩
      cases v with
      | nil => simp at hv
      | cons b _ => exact Fin.elim0 b
    · obtain ⟨M₀, hM₀⟩ := (isUnavoidableFor_univ_iff_exists_length (B := Fin r)).mp (ih r)
      let M := max M₀ 1
      have hM : ∀ u : List (Fin r), M ≤ u.length → Reflects u (ziminWord k) :=
        fun u hu ↦ hM₀ u (by omega)
      let B_cnt := r ^ M + 1
      refine ⟨(M + 1) * B_cnt, fun v hv ↦ ?_⟩
      let slices : List (List (Fin r)) :=
        (List.range B_cnt).map fun t ↦ (v.drop ((M + 1) * t)).take M
      have hslices_len : ∀ t < B_cnt, ((v.drop ((M + 1) * t)).take M).length = M := by
        intro t ht
        have hmul : (M + 1) * (t + 1) ≤ (M + 1) * B_cnt := Nat.mul_le_mul_left _ ht
        have hmul' : (M + 1) * t + M + 1 ≤ (M + 1) * B_cnt := by
          simpa [Nat.mul_succ, Nat.add_assoc] using hmul
        simp only [List.length_take, List.length_drop]
        omega
      have hnot_nd : ¬ slices.Nodup := by
        intro hnd
        let allW := wordsOfLength (List.finRange r) M
        have hall_sub : ∀ u ∈ slices, u ∈ allW := by
          intro u hu
          simp only [slices, List.mem_map, List.mem_range] at hu
          rcases hu with ⟨t, ht, rfl⟩
          exact mem_wordsOfLength List.mem_finRange (hslices_len t ht)
        have hle := nodup_length_le_of_subset hnd hall_sub
        simp only [slices, allW, List.length_map, List.length_range, length_wordsOfLength,
          List.length_finRange, B_cnt] at hle
        omega
      obtain ⟨i₁, i₂, hi_lt, hi₂_lt, hU_eq⟩ := exists_getElem_eq_of_not_nodup hnot_nd
      simp only [slices, List.length_map, List.length_range] at hi₂_lt
      simp only [slices, List.getElem_map, List.getElem_range] at hU_eq
      let U : List (Fin r) := (v.drop ((M + 1) * i₁)).take M
      have hU_len : U.length = M := hslices_len i₁ (Nat.lt_trans hi_lt hi₂_lt)
      have hU₂_eq : (v.drop ((M + 1) * i₂)).take M = U := hU_eq.symm
      let midLen := (M + 1) * i₂ - ((M + 1) * i₁ + M)
      have hmid_pos : 0 < midLen := by
        have hmul : (M + 1) * (i₁ + 1) ≤ (M + 1) * i₂ := Nat.mul_le_mul_left _ hi_lt
        have hmul' : (M + 1) * i₁ + M + 1 ≤ (M + 1) * i₂ := by
          simpa [Nat.mul_succ, Nat.add_assoc] using hmul
        omega
      let mid : List (Fin r) := (v.drop ((M + 1) * i₁ + M)).take midLen
      have hmid_ne : mid ≠ [] := by
        have hmlen : mid.length = midLen := by
          have hmul : (M + 1) * (i₂ + 1) ≤ (M + 1) * B_cnt := Nat.mul_le_mul_left _ hi₂_lt
          have hmul' : (M + 1) * i₂ + M + 1 ≤ (M + 1) * B_cnt := by
            simpa [Nat.mul_succ, Nat.add_assoc] using hmul
          simp only [mid, List.length_take, List.length_drop]
          omega
        exact List.length_pos_iff.mp (by omega)
      have hfactor : U ++ mid ++ U <:+: v := by
        have hspan : (v.drop ((M + 1) * i₁)).take (M + midLen + M) = U ++ mid ++ U := by
          have h1 : (v.drop ((M + 1) * i₁)).take (M + midLen + M) =
              (v.drop ((M + 1) * i₁)).take (M + midLen) ++
                (v.drop ((M + 1) * i₁ + (M + midLen))).take M := by
            rw [List.take_add, List.drop_drop]
          have h2 : (v.drop ((M + 1) * i₁)).take (M + midLen) = U ++ mid := by
            rw [List.take_add, List.drop_drop]
          have hidx : (M + 1) * i₁ + (M + midLen) = (M + 1) * i₂ := by
            have hmul : (M + 1) * (i₁ + 1) ≤ (M + 1) * i₂ := Nat.mul_le_mul_left _ hi_lt
            have hmul' : (M + 1) * i₁ + M + 1 ≤ (M + 1) * i₂ := by
              simpa [Nat.mul_succ, Nat.add_assoc] using hmul
            omega
          rw [h1, h2, hidx, hU₂_eq]
        rw [← hspan]
        exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
      obtain ⟨φ, hφ, ⟨s₁, s₂, hsU⟩⟩ := hM U (by omega)
      let midFull : List (Fin r) := s₂ ++ mid ++ s₁
      have hmidFull_ne : midFull ≠ [] := by
        intro hemp
        simp only [midFull, List.append_eq_nil_iff] at hemp
        exact hmid_ne hemp.1.2
      let ψ : ℕ → List (Fin r) := fun m ↦ if m = k then midFull else φ m
      have hflat_eq : (ziminWord k).flatMap ψ = (ziminWord k).flatMap φ := by
        apply List.flatMap_congr
        intro m hm
        have hlt : m ≠ k := Nat.ne_of_lt (mem_ziminWord_lt hm)
        simp [ψ, hlt]
      refine ⟨ψ, ?_, ?_⟩
      · intro m hm
        by_cases hmk : m = k
        · simp [ψ, hmk, hmidFull_ne]
        · simp only [ziminWord_succ, List.mem_append, List.mem_singleton] at hm
          rcases hm with (hm | rfl) | hm
          · simp [ψ, hmk, hφ m hm]
          · contradiction
          · simp [ψ, hmk, hφ m hm]
      · have hzim : (ziminWord (k + 1)).flatMap ψ =
            (ziminWord k).flatMap φ ++ midFull ++ (ziminWord k).flatMap φ := by
          simp [ziminWord_succ, List.flatMap_append, hflat_eq, ψ]
        rw [hzim]
        have hsub : (ziminWord k).flatMap φ ++ midFull ++ (ziminWord k).flatMap φ <:+:
            U ++ mid ++ U := by
          refine ⟨s₁, s₂, ?_⟩
          rw [← hsU]
          simp [midFull, List.append_assoc]
        exact hsub.trans hfactor

end ZiminAndReducibility

end CslibFrontier.Word
