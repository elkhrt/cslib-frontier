/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Data.Fintype.Basic

/-!
# Square-Free Words and Thue's Theorem

A finite word `w : List A` over an alphabet `A` is *square-free*
(`CslibFrontier.Word.IsSquareFree`) if
it contains no nonempty factor of the form `u ++ u`. Repeating a single letter adjacently (`[x,
x]`)
produces a square of length `2`, so square-free words have no equal consecutive letters.

Over a two-letter alphabet every word of length at least `4` contains a square, whereas Axel Thue
proved in that arbitrarily long square-free words exist over a three-letter alphabet.
Following
John Leech, we construct arbitrarily long ternary square-free words under standard Lean
axioms by iterating a `13`-uniform cyclic morphism `leechBlock : Fin 3 → List (Fin 3)`.

## Main definitions

* `CslibFrontier.Word.IsSquareFree`: predicate asserting that `w : List A` has no nonempty square
  factor
  `u ++ u <:+: w`.
* `CslibFrontier.Word.leechBlock`: Leech's `13`-uniform cyclic ternary morphism block on `Fin 3`.
* `CslibFrontier.Word.leechWord`: iterated Leech word of length `13 ^ k` over `Fin 3`.

## Main results

* `CslibFrontier.Word.IsSquareFree.of_infix`: factors of square-free words are square-free.
* `CslibFrontier.Word.IsSquareFree.map`: injective alphabet maps preserve square-freeness.
* `CslibFrontier.Word.not_isSquareFree_of_pair_infix`: any word containing `[x, x]` as a factor is
  not
  square-free.
* `CslibFrontier.Word.isSquareFree_leechWord`: every iterated Leech word `leechWord k` is
  square-free.
* `CslibFrontier.Word.exists_isSquareFree_length`: **Thue's Theorem** — for every `n : ℕ`, there
  exists
  a square-free word over `Fin 3` of length `n`.
* `CslibFrontier.Word.infinite_setOf_isSquareFree`: the set of square-free words over `Fin 3` is
  infinite.
-/

public section

namespace CslibFrontier.Word

section General

variable {A B : Type*}

/-- A word `w : List A` is *square-free* if no nonempty word `u` appears twice consecutively as a
contiguous factor `u ++ u <:+: w`. -/
def IsSquareFree (w : List A) : Prop :=
  ∀ u : List A, u ≠ [] → ¬ (u ++ u <:+: w)

/-- Unfolded characterization of `IsSquareFree`. -/
theorem isSquareFree_iff {w : List A} :
    IsSquareFree w ↔ ∀ u : List A, u ≠ [] → ¬ (u ++ u <:+: w) :=
  Iff.rfl

/-- The empty word is square-free. -/
@[simp]
theorem isSquareFree_nil : IsSquareFree ([] : List A) := by
  intro u hu hinf
  have hlen : (u ++ u).length ≤ ([] : List A).length := hinf.length_le
  simp only [List.length_append, List.length_nil] at hlen
  exact hu (List.eq_nil_of_length_eq_zero (by omega))

/-- Every single-letter word is square-free. -/
@[simp]
theorem isSquareFree_singleton (a : A) : IsSquareFree [a] := by
  intro u hu hinf
  have hlen : (u ++ u).length ≤ ([a] : List A).length := hinf.length_le
  simp only [List.length_append, List.length_singleton] at hlen
  exact hu (List.eq_nil_of_length_eq_zero (by omega))

/-- Every factor (infix) of a square-free word is square-free. -/
theorem IsSquareFree.of_infix {v w : List A} (hw : IsSquareFree w) (hvw : v <:+: w) :
    IsSquareFree v :=
  fun u hu huv ↦ hw u hu (huv.trans hvw)

/-- Every prefix of a square-free word is square-free. -/
theorem IsSquareFree.of_prefix {v w : List A} (hw : IsSquareFree w) (hvw : v <+: w) :
    IsSquareFree v :=
  hw.of_infix hvw.isInfix

/-- Every suffix of a square-free word is square-free. -/
theorem IsSquareFree.of_suffix {v w : List A} (hw : IsSquareFree w) (hvw : v <:+ w) :
    IsSquareFree v :=
  hw.of_infix hvw.isInfix

/-- Taking any prefix `w.take n` preserves square-freeness. -/
theorem IsSquareFree.take {w : List A} (hw : IsSquareFree w) (n : ℕ) :
    IsSquareFree (w.take n) :=
  hw.of_prefix (List.take_prefix n w)

/-- Dropping any prefix `w.drop n` preserves square-freeness. -/
theorem IsSquareFree.drop {w : List A} (hw : IsSquareFree w) (n : ℕ) :
    IsSquareFree (w.drop n) :=
  hw.of_suffix (List.drop_suffix n w)

/-- No square-free word contains two equal adjacent letters `[x, x]`. -/
theorem not_isSquareFree_of_pair_infix {w : List A} {x : A} (hx : [x, x] <:+: w) :
    ¬ IsSquareFree w :=
  fun hw ↦ hw [x] (List.cons_ne_nil x []) hx

/-- Adjacent letters in a square-free word are distinct. -/
theorem IsSquareFree.getElem_ne_succ {w : List A} (hw : IsSquareFree w) {i : ℕ}
    (hi : i + 1 < w.length) : w[i] ≠ w[i + 1] := by
  intro heq
  have hsub : [w[i], w[i + 1]] <:+: w := by
    refine ⟨w.take i, w.drop (i + 2), ?_⟩
    have h1 : w.take (i + 1) = w.take i ++ [w[i]] := List.take_succ_eq_append_getElem (by omega)
    have h2 : w.take (i + 2) = w.take (i + 1) ++ [w[i + 1]] :=
      List.take_succ_eq_append_getElem hi
    calc
      w.take i ++ [w[i], w[i + 1]] ++ w.drop (i + 2)
          = (w.take i ++ [w[i]] ++ [w[i + 1]]) ++ w.drop (i + 2) := by simp [List.append_assoc]
      _ = w.take (i + 2) ++ w.drop (i + 2) := by rw [← h1, ← h2]
      _ = w := List.take_append_drop (i + 2) w
  rw [← heq] at hsub
  exact not_isSquareFree_of_pair_infix hsub hw

/-- Square-freeness is preserved under injective letter maps. -/
theorem IsSquareFree.map {f : A → B} (hf : Function.Injective f) {w : List A}
    (hw : IsSquareFree w) : IsSquareFree (w.map f) := by
  intro u hu ⟨s, t, hst⟩
  set k := u.length
  set i := s.length
  have hi2 : i + 2 * k ≤ w.length := by
    have := congrArg List.length hst
    simp only [List.length_append, List.length_map] at this
    omega
  let v := (w.drop i).take k
  have hv_ne : v ≠ [] := by
    have hv_len : v.length = k := by
      simp only [v, List.length_take, List.length_drop]
      omega
    have hk : 0 < k := List.length_pos_iff.mpr hu
    exact List.length_pos_iff.mp (by omega)
  have hvv : v ++ v = (w.drop i).take (2 * k) := by
    have hmap_eq : (v ++ v).map f = ((w.drop i).take (2 * k)).map f := by
      have hdrop : (w.map f).drop i = u ++ u ++ t := by
        have : s ++ (u ++ u ++ t) = w.map f := by simpa [List.append_assoc] using hst
        rw [← this, List.drop_left' rfl]
      have htake1 : ((w.map f).drop i).take k = u := by
        rw [hdrop, List.append_assoc, List.take_left' (by simp [k])]
      have htake2 : ((w.map f).drop i).take (2 * k) = u ++ u := by
        rw [hdrop]
        have h2k : (u ++ u).length = 2 * k := by simp [k, Nat.two_mul]
        exact List.take_left' h2k
      simp only [v, List.map_append, List.map_take, List.map_drop, htake1, htake2]
    exact List.map_injective_iff.mpr hf hmap_eq
  have hinf : (w.drop i).take (2 * k) <:+: w :=
    (List.take_prefix (2 * k) (w.drop i)).isInfix.trans (List.drop_suffix i w).isInfix
  rw [← hvv] at hinf
  exact hw v hv_ne hinf

/-- Indexing characterization of `IsSquareFree`: no nonempty slice of length `k` repeats
immediately at `i` and `i + k`. -/
theorem isSquareFree_iff_forall_slice {w : List A} :
    IsSquareFree w ↔
      ∀ (i k : ℕ), 0 < k → (hik : i + 2 * k ≤ w.length) →
        ∃ j : ℕ, ∃ hj : j < k, w[i + j]'(by omega) ≠ w[i + k + j]'(by omega) := by
  constructor
  · intro hw i k hk hik
    by_contra! h
    let u := (w.drop i).take k
    have hu_len : u.length = k := by
      simp only [u, List.length_take, List.length_drop]
      omega
    have hu_ne : u ≠ [] := List.length_pos_iff.mp (by omega)
    have h2 : (w.drop i).take (2 * k) = u ++ u := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, List.length_append, hu_len]
        omega
      · intro j hj1 hj2
        have hj2k : j < 2 * k := by simp only [List.length_append, hu_len] at hj2; omega
        simp only [List.getElem_take, List.getElem_drop]
        by_cases hjk : j < k
        · rw [List.getElem_append_left (by rw [hu_len]; omega)]
          simp [u]
        · rw [List.getElem_append_right (by rw [hu_len]; omega)]
          simp only [u, List.getElem_take, List.getElem_drop, hu_len]
          have hsub : j - k < k := by omega
          have heq := h (j - k) hsub
          have hidx : i + k + (j - k) = i + j := by omega
          simpa [hidx] using heq.symm
    have hinf : u ++ u <:+: w := by
      rw [← h2]
      exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
    exact hw u hu_ne hinf
  · intro h u hu ⟨s, t, hst⟩
    set i := s.length
    set k := u.length
    have hk : 0 < k := List.length_pos_iff.mpr hu
    have hik : i + 2 * k ≤ w.length := by
      have := congrArg List.length hst
      simp only [List.length_append] at this
      omega
    obtain ⟨j, hj, hne⟩ := h i k hk hik
    apply hne
    have hst' : s ++ (u ++ (u ++ t)) = w := by simpa [List.append_assoc] using hst
    have h1 : w[i + j]'(by omega) = u[j]'(by omega) := by
      simp only [← hst']
      rw [List.getElem_append_right (by omega)]
      have hrem : i + j - s.length = j := by omega
      simp only [hrem]
      rw [List.getElem_append_left (by omega)]
    have h2 : w[i + k + j]'(by omega) = u[j]'(by omega) := by
      simp only [← hst']
      rw [List.getElem_append_right (by omega)]
      have hrem1 : i + k + j - s.length = k + j := by omega
      simp only [hrem1]
      rw [List.getElem_append_right (by omega)]
      have hrem2 : k + j - u.length = j := by omega
      simp only [hrem2]
      rw [List.getElem_append_left (by omega)]
    exact h1.trans h2.symm

end General

section LeechMorphism

private theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (a : Fin 3) : P a :=
  match a with
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨_ + 3, ha⟩ => absurd ha (by omega)

/-- Base `13`-letter palindrome block `[0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0]` of Leech's ternary
square-free morphism. -/
private def leechBase : List (Fin 3) :=
  [0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0]

private theorem length_leechBase : leechBase.length = 13 :=
  rfl

/-- Cyclic shift `(x + a) mod 3` on `Fin 3`. -/
private def shiftFin3 (a x : Fin 3) : Fin 3 :=
  ⟨(x.1 + a.1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Leech's `13`-uniform cyclic morphism block `Fin 3 → List (Fin 3)`, obtained by cyclically
shifting `0, 1, 2` by `a` in `[0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0]`. -/
def leechBlock (a : Fin 3) : List (Fin 3) :=
  leechBase.map (shiftFin3 a)

/-- Length of every `leechBlock a` is `13`. -/
@[simp]
theorem length_leechBlock (a : Fin 3) : (leechBlock a).length = 13 := by
  simp [leechBlock, leechBase]

/-- Every `leechBlock a` is nonempty. -/
theorem leechBlock_ne_nil (a : Fin 3) : leechBlock a ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

private theorem length_flatMap_leechBlock (w : List (Fin 3)) :
    (w.flatMap leechBlock).length = 13 * w.length := by
  induction w with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, length_leechBlock, List.length_cons, ih]
    omega

private theorem getElem_leechBlock_inj {a b : Fin 3} {r : ℕ} (hr : r < 13)
    (heq : (leechBlock a)[r]'(by simp [hr]) = (leechBlock b)[r]'(by simp [hr])) : a = b := by
  have hr' : r < leechBase.length := by rw [length_leechBase]; exact hr
  have hbase : ((leechBase[r]'hr').1 + a.1) % 3 = ((leechBase[r]'hr').1 + b.1) % 3 := by
    have h1 : (leechBlock a)[r]'(by simp [hr]) = shiftFin3 a (leechBase[r]'hr') := by
      simp [leechBlock]
    have h2 : (leechBlock b)[r]'(by simp [hr]) = shiftFin3 b (leechBase[r]'hr') := by
      simp [leechBlock]
    rw [h1, h2] at heq
    exact congrArg Fin.val heq
  have hx : (leechBase[r]'hr').1 < 3 := Fin.is_lt _
  have ha : a.1 < 3 := a.2
  have hb : b.1 < 3 := b.2
  ext
  omega

private theorem getElem_flatMap_leechBlock {w : List (Fin 3)} {p : ℕ}
    (hp : p < (w.flatMap leechBlock).length) :
    (w.flatMap leechBlock)[p] =
      (leechBlock (w[p / 13]'(by rw [length_flatMap_leechBlock] at hp; omega)))[p % 13]'(
        Nat.mod_lt _ (by decide)) := by
  induction w generalizing p with
  | nil => simp at hp
  | cons c cs ih =>
    simp only [List.flatMap_cons] at hp ⊢
    by_cases hp13 : p < 13
    · rw [List.getElem_append_left (by simpa using hp13)]
      have hdiv : p / 13 = 0 := Nat.div_eq_of_lt hp13
      have hmod : p % 13 = p := Nat.mod_eq_of_lt hp13
      simp [hdiv, hmod]
    · have hp' : p - 13 < (cs.flatMap leechBlock).length := by
        simp only [List.length_append, length_leechBlock] at hp
        omega
      rw [List.getElem_append_right (by simp; omega)]
      simp only [length_leechBlock]
      rw [ih hp']
      have hdiv : p / 13 = (p - 13) / 13 + 1 := by omega
      have hmod : p % 13 = (p - 13) % 13 := by omega
      have hcs_idx : (c :: cs)[p / 13]'(by rw [length_flatMap_leechBlock] at hp'; simp; omega) =
          cs[(p - 13) / 13]'(by rw [length_flatMap_leechBlock] at hp'; omega) := by
        simp [hdiv]
      simp only [hcs_idx, hmod]
      rfl

/-- Executable Boolean square-freeness test on a concrete list over a `DecidableEq` type. -/
private def isSquareFreeBool {A : Type*} [DecidableEq A] (w : List A) : Bool :=
  (List.range w.length).all fun i ↦
    (List.range (w.length + 1)).all fun k ↦
      if 0 < k ∧ i + 2 * k ≤ w.length then
        decide ((w.drop i).take k ≠ (w.drop (i + k)).take k)
      else true

private theorem isSquareFree_of_isSquareFreeBool {A : Type*} [DecidableEq A] {w : List A}
    (hb : isSquareFreeBool w = true) : IsSquareFree w := by
  rw [isSquareFree_iff_forall_slice]
  intro i k hk hik
  simp only [isSquareFreeBool, List.all_eq_true, List.mem_range] at hb
  have hi : i < w.length := by omega
  have hk' : k < w.length + 1 := by omega
  have hspec := hb i hi k hk'
  simp only [hk, hik, and_self, ↓reduceIte, decide_eq_true_eq] at hspec
  by_contra! hall
  apply hspec
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop]
    omega
  · intro j hj1 hj2
    simp only [List.length_take, List.length_drop] at hj1
    have hjk : j < k := by omega
    simpa [List.getElem_take, List.getElem_drop] using hall j hjk

private def allTriplesBool : Bool :=
  ([0, 1, 2] : List (Fin 3)).all fun a ↦
    ([0, 1, 2] : List (Fin 3)).all fun b ↦
      ([0, 1, 2] : List (Fin 3)).all fun c ↦
        if a ≠ b ∧ b ≠ c then isSquareFreeBool ([a, b, c].flatMap leechBlock) else true

private theorem allTriplesBool_eq_true : allTriplesBool = true := by
  decide

private theorem mem_fin3_list (a : Fin 3) : a ∈ ([0, 1, 2] : List (Fin 3)) :=
  fin3_cases (P := fun x ↦ x ∈ ([0, 1, 2] : List (Fin 3))) (by decide) (by decide) (by decide) a

private theorem isSquareFreeBool_leech_triple (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) :
    isSquareFreeBool ([a, b, c].flatMap leechBlock) = true := by
  have hall := allTriplesBool_eq_true
  simp only [allTriplesBool, List.all_eq_true] at hall
  have hspec := hall a (mem_fin3_list a) b (mem_fin3_list b) c (mem_fin3_list c)
  simpa [hab, hbc] using hspec

private theorem next_fin3_ne (a : Fin 3) :
    a ≠ (⟨(a.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) :=
  fin3_cases (P := fun x : Fin 3 ↦ x ≠ ⟨(x.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩)
    (by decide) (by decide) (by decide) a

private theorem isSquareFree_leech_pair (a b : Fin 3) (hab : a ≠ b) :
    IsSquareFree ([a, b].flatMap leechBlock) := by
  let c : Fin 3 := ⟨(b.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
  have hbc : b ≠ c := next_fin3_ne b
  have h3 := isSquareFree_of_isSquareFreeBool (isSquareFreeBool_leech_triple a b c hab hbc)
  refine h3.of_infix ⟨[], leechBlock c, ?_⟩
  simp [List.flatMap_cons, List.append_assoc]

private theorem isSquareFree_leech_single (a : Fin 3) :
    IsSquareFree ([a].flatMap leechBlock) := by
  let b : Fin 3 := ⟨(a.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
  have hab : a ≠ b := next_fin3_ne a
  exact (isSquareFree_leech_pair a b hab).of_infix ⟨[], leechBlock b, by simp [List.flatMap_cons]⟩

private def distinctFin3Pairs : List (Fin 3 × Fin 3) :=
  [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

private theorem mem_distinctFin3Pairs {a b : Fin 3} (hab : a ≠ b) :
    (a, b) ∈ distinctFin3Pairs := by
  revert hab
  refine fin3_cases (P := fun x ↦ x ≠ b → (x, b) ∈ distinctFin3Pairs) ?_ ?_ ?_ a
  · exact fin3_cases (P := fun y ↦ (0 : Fin 3) ≠ y → ((0 : Fin 3), y) ∈ distinctFin3Pairs)
      (fun h ↦ absurd rfl h) (fun _ ↦ by decide) (fun _ ↦ by decide) b
  · exact fin3_cases (P := fun y ↦ (1 : Fin 3) ≠ y → ((1 : Fin 3), y) ∈ distinctFin3Pairs)
      (fun _ ↦ by decide) (fun h ↦ absurd rfl h) (fun _ ↦ by decide) b
  · exact fin3_cases (P := fun y ↦ (2 : Fin 3) ≠ y → ((2 : Fin 3), y) ∈ distinctFin3Pairs)
      (fun _ ↦ by decide) (fun _ ↦ by decide) (fun h ↦ absurd rfl h) b

private def windowSyncBool : Bool :=
  distinctFin3Pairs.all fun p₁ ↦
    distinctFin3Pairs.all fun p₂ ↦
      (List.range 13).all fun r₁ ↦
        (List.range 13).all fun r₂ ↦
          let w₁ := ((leechBlock p₁.1 ++ leechBlock p₁.2).drop r₁).take 13
          let w₂ := ((leechBlock p₂.1 ++ leechBlock p₂.2).drop r₂).take 13
          if w₁ = w₂ then decide (r₁ = r₂) else true

private theorem windowSyncBool_eq_true : windowSyncBool = true := by
  decide

/-- Window synchronization for Leech's morphism: any two matching `13`-letter windows inside pairs
of distinct consecutive blocks occur at the exact same offset modulo `13`. -/
private theorem leech_window_offset_eq (a₁ b₁ a₂ b₂ : Fin 3) (h₁ : a₁ ≠ b₁) (h₂ : a₂ ≠ b₂)
    (r₁ r₂ : Fin 13)
    (heq : ∀ j : Fin 13,
      ((leechBlock a₁ ++ leechBlock b₁)[r₁.1 + j.1]'(by simp; omega)) =
        ((leechBlock a₂ ++ leechBlock b₂)[r₂.1 + j.1]'(by simp; omega))) :
    r₁ = r₂ := by
  have hall := windowSyncBool_eq_true
  simp only [windowSyncBool, List.all_eq_true, List.mem_range] at hall
  have hspec := hall (a₁, b₁) (mem_distinctFin3Pairs h₁) (a₂, b₂) (mem_distinctFin3Pairs h₂)
    r₁.1 r₁.2 r₂.1 r₂.2
  have hw_eq : ((leechBlock a₁ ++ leechBlock b₁).drop r₁.1).take 13 =
      ((leechBlock a₂ ++ leechBlock b₂).drop r₂.1).take 13 := by
    apply List.ext_getElem
    · have := r₁.2; have := r₂.2
      simp only [List.length_take, List.length_drop, List.length_append, length_leechBlock]
      omega
    · intro j hj1 hj2
      have hj13 : j < 13 := by
        simp only [List.length_take] at hj1
        omega
      simpa [List.getElem_take, List.getElem_drop] using heq ⟨j, hj13⟩
  simp only [hw_eq, ↓reduceIte, decide_eq_true_eq] at hspec
  exact Fin.ext hspec

private theorem getElem_flatMap_in_pair {w : List (Fin 3)} {q : ℕ} (hq : q + 1 < w.length)
    {r j : ℕ} (hrj : r + j < 26) :
    (w.flatMap leechBlock)[13 * q + r + j]'(by rw [length_flatMap_leechBlock]; omega) =
      (leechBlock w[q] ++ leechBlock w[q + 1])[r + j]'(by simp [hrj]) := by
  rw [getElem_flatMap_leechBlock (by rw [length_flatMap_leechBlock]; omega)]
  by_cases hlt : r + j < 13
  · rw [List.getElem_append_left (by simpa using hlt)]
    have hdiv : (13 * q + r + j) / 13 = q := by omega
    have hmod : (13 * q + r + j) % 13 = r + j := by omega
    simp [hdiv, hmod]
  · rw [List.getElem_append_right (by simp; omega)]
    have hdiv : (13 * q + r + j) / 13 = q + 1 := by omega
    have hmod : (13 * q + r + j) % 13 = r + j - 13 := by omega
    simp [hdiv, hmod]

/-- Leech's `13`-uniform morphism preserves square-freeness on `Fin 3`. -/
theorem IsSquareFree.flatMap_leechBlock {w : List (Fin 3)} (hw : IsSquareFree w) :
    IsSquareFree (w.flatMap leechBlock) := by
  rw [isSquareFree_iff_forall_slice]
  intro i k hk hik
  rw [length_flatMap_leechBlock] at hik
  by_contra! hmatch
  -- Case 1: short period `k < 13` spans at most 3 blocks of `w`.
  by_cases hk13 : k < 13
  · set q := i / 13
    set r := i % 13
    have hr : r < 13 := Nat.mod_lt i (by decide)
    let m := min 3 (w.length - q)
    let sub := (w.drop q).take m
    have hsub_sq : IsSquareFree sub :=
      (hw.drop q).take m
    have hflat_sq : IsSquareFree (sub.flatMap leechBlock) := by
      have hm : sub.length ≤ 3 := by simp only [sub, m, List.length_take, List.length_drop]; omega
      match hsub_eq : sub with
      | [] => simp
      | [a] => exact isSquareFree_leech_single a
      | [a, b] =>
        have h2 : IsSquareFree [a, b] := hsub_eq ▸ hsub_sq
        have hab : a ≠ b := by simpa using h2.getElem_ne_succ (i := 0) (by simp)
        exact isSquareFree_leech_pair a b hab
      | [a, b, c] =>
        have h3 : IsSquareFree [a, b, c] := hsub_eq ▸ hsub_sq
        have hab : a ≠ b := by simpa using h3.getElem_ne_succ (i := 0) (by simp)
        have hbc : b ≠ c := by simpa using h3.getElem_ne_succ (i := 1) (by simp)
        exact isSquareFree_of_isSquareFreeBool (isSquareFreeBool_leech_triple a b c hab hbc)
      | _ :: _ :: _ :: _ :: _ =>
        simp only [List.length_cons] at hm
        omega
    have hr_bound : r + 2 * k ≤ (sub.flatMap leechBlock).length := by
      rw [length_flatMap_leechBlock]
      have hlen_sub : sub.length = min 3 (w.length - q) := by simp [sub, m]
      rw [hlen_sub]
      omega
    obtain ⟨j, hj, hne⟩ := isSquareFree_iff_forall_slice.mp hflat_sq r k hk hr_bound
    apply hne
    have halign : ∀ (t : ℕ) (ht : t < r + 2 * k),
        (sub.flatMap leechBlock)[t]'(by omega) =
          (w.flatMap leechBlock)[13 * q + t]'(by rw [length_flatMap_leechBlock]; omega) := by
      intro t ht
      rw [getElem_flatMap_leechBlock (by omega),
        getElem_flatMap_leechBlock (by rw [length_flatMap_leechBlock]; omega)]
      have hdiv : (13 * q + t) / 13 = q + t / 13 := by omega
      have hmod : (13 * q + t) % 13 = t % 13 := by omega
      have hsub_idx : sub[t / 13]'(by rw [length_flatMap_leechBlock] at hr_bound; omega) =
          w[q + t / 13]'(by omega) := by
        simp [sub]
      simp [hdiv, hmod, hsub_idx]
    have h1 := halign (r + j) (by omega)
    have h2 := halign (r + k + j) (by omega)
    have hi_eq : 13 * q + (r + j) = i + j := by omega
    have hik_eq : 13 * q + (r + k + j) = i + k + j := by omega
    rw [h1, h2]
    simpa [hi_eq, hik_eq] using hmatch j hj
  -- Case 2: long period `k ≥ 13` synchronizes modulo `13` and projects to a square in `w`.
  · push Not at hk13
    set q₁ := i / 13
    set r₁ := i % 13
    set q₂ := (i + k) / 13
    set r₂ := (i + k) % 13
    have hr₁ : r₁ < 13 := Nat.mod_lt _ (by decide)
    have hr₂ : r₂ < 13 := Nat.mod_lt _ (by decide)
    have hr_eq : r₁ = r₂ := by
      let c_pad : Fin 3 := ⟨((w[w.length - 1]'(by omega)).1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
      let w' := w ++ [c_pad]
      have hw'_adj : ∀ (q : ℕ) (hq : q + 1 < w'.length),
          w'[q]'(Nat.lt_of_succ_lt hq) ≠ w'[q + 1]'hq := by
        intro q hq
        simp only [w', List.length_append, List.length_singleton] at hq
        by_cases hqw : q + 1 < w.length
        · rw [List.getElem_append_left (by omega), List.getElem_append_left hqw]
          exact hw.getElem_ne_succ hqw
        · have hq_eq : q = w.length - 1 := by omega
          subst hq_eq
          rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
          have hidx : w.length - 1 + 1 - w.length = 0 := by omega
          simp only [hidx, List.getElem_singleton, c_pad]
          exact next_fin3_ne (w[w.length - 1]'(by omega))
      have hq₁ : q₁ + 1 < w'.length := by simp [w']; omega
      have hq₂ : q₂ + 1 < w'.length := by simp [w']; omega
      have hwin : ∀ j : Fin 13,
          (leechBlock w'[q₁] ++ leechBlock w'[q₁ + 1])[r₁ + j.1]'(by simp; omega) =
            (leechBlock w'[q₂] ++ leechBlock w'[q₂ + 1])[r₂ + j.1]'(by simp; omega) := by
        intro j
        have hext : ∀ (p : ℕ) (hp : p < 13 * w.length),
            (w'.flatMap leechBlock)[p]'(by rw [length_flatMap_leechBlock]; simp [w']; omega) =
              (w.flatMap leechBlock)[p]'(by rw [length_flatMap_leechBlock]; omega) := by
          intro p hp
          simp only [w', List.flatMap_append]
          exact List.getElem_append_left (by rw [length_flatMap_leechBlock]; exact hp)
        have hL := getElem_flatMap_in_pair hq₁ (r := r₁) (j := j.1) (by omega)
        have hR := getElem_flatMap_in_pair hq₂ (r := r₂) (j := j.1) (by omega)
        have hi₁ : 13 * q₁ + r₁ + j.1 = i + j.1 := by omega
        have hi₂ : 13 * q₂ + r₂ + j.1 = i + k + j.1 := by omega
        rw [← hL, ← hR]
        simp only [hi₁, hi₂]
        rw [hext (i + j.1) (by omega), hext (i + k + j.1) (by omega)]
        exact hmatch j.1 (by omega)
      have hfin := leech_window_offset_eq w'[q₁] w'[q₁ + 1] w'[q₂] w'[q₂ + 1]
        (hw'_adj q₁ hq₁) (hw'_adj q₂ hq₂) ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ hwin
      exact congrArg Fin.val hfin
    set m := q₂ - q₁
    have hm_pos : 0 < m := by omega
    have hqm : q₁ + 2 * m ≤ w.length := by omega
    obtain ⟨t, ht, hne_w⟩ := isSquareFree_iff_forall_slice.mp hw q₁ m hm_pos hqm
    apply hne_w
    by_cases ht0 : t = 0
    · subst ht0
      have hm0 := hmatch 0 hk
      rw [getElem_flatMap_leechBlock (by rw [length_flatMap_leechBlock]; omega),
        getElem_flatMap_leechBlock (by rw [length_flatMap_leechBlock]; omega)] at hm0
      have hd2 : (i + k) / 13 = q₁ + m := by omega
      have hm2 : (i + k) % 13 = r₁ := by omega
      simp only [Nat.add_zero, hd2, hm2] at hm0
      exact getElem_leechBlock_inj hr₁ hm0
    · set j := 13 * t - r₁
      have hj : j < k := by omega
      have hmj := hmatch j hj
      rw [getElem_flatMap_leechBlock (by rw [length_flatMap_leechBlock]; omega),
        getElem_flatMap_leechBlock (by rw [length_flatMap_leechBlock]; omega)] at hmj
      have hd1 : (i + j) / 13 = q₁ + t := by omega
      have hm1 : (i + j) % 13 = 0 := by omega
      have hd2 : (i + k + j) / 13 = q₁ + m + t := by omega
      have hm2 : (i + k + j) % 13 = 0 := by omega
      simp only [hd1, hm1, hd2, hm2] at hmj
      exact getElem_leechBlock_inj (by decide : 0 < 13) hmj

/-- Iterated Leech ternary word `leechWord k : List (Fin 3)` of length `13 ^ k`. -/
def leechWord : ℕ → List (Fin 3)
  | 0 => [0]
  | k + 1 => (leechWord k).flatMap leechBlock

/-- Every `leechWord k` has length `13 ^ k`. -/
@[simp]
theorem length_leechWord (k : ℕ) : (leechWord k).length = 13 ^ k := by
  induction k with
  | zero => simp [leechWord]
  | succ k ih => rw [leechWord, length_flatMap_leechBlock, ih, Nat.pow_succ, Nat.mul_comm]

/-- Every iterated Leech word `leechWord k` is square-free. -/
theorem isSquareFree_leechWord (k : ℕ) : IsSquareFree (leechWord k) := by
  induction k with
  | zero => exact isSquareFree_singleton 0
  | succ k ih => exact ih.flatMap_leechBlock

/-- **Thue's Square-Free Word Theorem**: for every length `n : ℕ`, there exists a
square-free word over `Fin 3` of length `n`.
-/
theorem exists_isSquareFree_length (n : ℕ) :
    ∃ w : List (Fin 3), w.length = n ∧ IsSquareFree w := by
  have hlt : n ≤ 13 ^ n := Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 13))
  refine ⟨(leechWord n).take n, ?_, (isSquareFree_leechWord n).take n⟩
  simp [hlt]

/-- The set of square-free words over `Fin 3` is infinite. -/
theorem infinite_setOf_isSquareFree : {w : List (Fin 3) | IsSquareFree w}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n ↦ (leechWord n).take n) ?_ ?_
  · intro m n hmn
    have hm : ((leechWord m).take m).length = m := by
      simp [Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 13))]
    have hn : ((leechWord n).take n).length = n := by
      simp [Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 13))]
    calc
      m = ((leechWord m).take m).length := hm.symm
      _ = ((leechWord n).take n).length := congrArg List.length hmn
      _ = n := hn
  · intro n
    exact (isSquareFree_leechWord n).take n

end LeechMorphism

end CslibFrontier.Word
