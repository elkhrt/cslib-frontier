/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.LempelZiv.LZ77
public import CslibFrontier.Algorithms.Lean.LempelZiv.LZ78
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.InformationTheory.Hamming

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Infix
import Mathlib.Tactic.Linarith

/-!
# Non-overlapping Parsing, Optimality, and Single-Edit Sensitivity

This module develops the theory of **non-overlapping Lempel–Ziv factorization** on finite
words (`List α`), where each phrase `u` is nonempty and its strict prefix `u.dropLast` occurs as a
contiguous factor (`<:+:`) strictly inside the previously parsed prefix `h` (disallowing
self-overlapping references).

## Main definitions

* `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.subword`: half-open contiguous
  slice `w[a..b)`.
* `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.wordHammingDist`,
  `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.hammingBall`: word Hamming distance
  and Hamming ball on equal-length lists (bridged to Mathlib's `hammingDist`).
* `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.IsHistory`,
  `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.IsExhaustive`: non-overlapping
  phrase histories and greedy (exhaustive) histories.
* `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.parse`,
  `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.complexity`: greedy non-overlapping
   factorization and its phrase count.
* `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.phraseStart`,
  `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.phraseEnd`,
  `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping.phraseStartsIn`: phrase boundary
  coordinates and phrase-start counts in an interval.

## Main results

* `complexity_le_of_isHistory`: greedy optimality of the non-overlapping parse among all
  valid non-overlapping histories.
* `parse_eq_of_isExhaustive`: uniqueness of the exhaustive non-overlapping factorization.
* `cslib_complexity_le_complexity` and `complexity_le_lz78Parse_length`: exact comparison bounds
  sandwiching non-overlapping complexity between self-referencing complexity and
  phrase count.
* `parse_append_of_disjoint` and `complexity_append_of_disjoint`: exact parse decomposition and
  complexity additivity across concatenations over disjoint alphabets terminated by a fresh symbol.
* `complexity_le_two_mul_of_hammingDist_le_one`: single-edit sensitivity upper bound
  `complexity w' ≤ 2 * complexity w` for every equal-length `w'` at Hamming distance at most `1`.
-/

public section

namespace CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping

/-! ## Half-open subwords -/

section Subwords

variable {α : Type*}

/-- Half-open contiguous subword `w[a..b) = (w.take b).drop a`. -/
@[expose] def subword (w : List α) (a b : ℕ) : List α :=
  (w.take b).drop a

@[simp] theorem subword_self (w : List α) (a : ℕ) : subword w a a = [] := by
  simp [subword]

theorem subword_of_ge {w : List α} {a b : ℕ} (h : b ≤ a) : subword w a b = [] := by
  rw [subword, List.drop_eq_nil_of_le]
  exact (List.length_take_le b w).trans h

@[simp] theorem subword_zero (w : List α) (b : ℕ) : subword w 0 b = w.take b := by
  simp [subword]

theorem length_subword {w : List α} {a b : ℕ} (hb : b ≤ w.length) :
    (subword w a b).length = b - a := by
  simp [subword, Nat.min_eq_left hb]

theorem subword_take_eq {w : List α} {L a b : ℕ} (hb : b ≤ L) :
    subword (w.take L) a b = subword w a b := by
  unfold subword
  rw [List.take_take, Nat.min_eq_left hb]

theorem subword_subword_zero {w : List α} {a b len : ℕ} (h : a + len ≤ b) :
    subword (subword w a b) 0 len = subword w a (a + len) := by
  unfold subword
  simp only [List.drop_zero, List.take_drop, List.take_take]
  congr 2
  omega

theorem subword_append_subword {w : List α} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    subword w a b ++ subword w b c = subword w a c := by
  have h1 : (w.take c).take b = w.take b := by
    rw [List.take_take, Nat.min_eq_left hbc]
  have h2 : (w.take c).drop b = ((w.take c).drop a).drop (b - a) := by
    rw [List.drop_drop, Nat.add_sub_of_le hab]
  have h3 : (w.take b).drop a = ((w.take c).drop a).take (b - a) := by
    rw [← h1, List.take_drop, Nat.add_sub_of_le hab]
  rw [subword, subword, subword, h2, h3, List.take_append_drop]

theorem subword_isInfix_subword {w : List α} {a b c d : ℕ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) : subword w c d <:+: subword w a b := by
  refine ⟨subword w a c, subword w d b, ?_⟩
  rw [subword_append_subword hac hcd, subword_append_subword (hac.trans hcd) hdb]

theorem subword_isInfix (w : List α) (a b : ℕ) : subword w a b <:+: w :=
  (List.drop_suffix a (w.take b)).isInfix.trans (List.take_prefix b w).isInfix

theorem exists_subword_of_isInfix {u w : List α} (h : u <:+: w) :
    ∃ a b, a ≤ b ∧ b ≤ w.length ∧ subword w a b = u := by
  obtain ⟨s, t, rfl⟩ := h
  refine ⟨s.length, s.length + u.length, Nat.le_add_right _ _, by simp, ?_⟩
  rw [subword, ← List.length_append, List.take_left, List.drop_left]

theorem getElem_subword {w : List α} {a b i : ℕ} (hb : b ≤ w.length)
    (hi : i < (subword w a b).length) :
    (subword w a b)[i] = w[a + i]'(by rw [length_subword hb] at hi; omega) := by
  simp [subword, List.getElem_drop, List.getElem_take]

theorem dropLast_subword {w : List α} {a b : ℕ} (hab : a < b) (hb : b ≤ w.length) :
    (subword w a b).dropLast = subword w a (b - 1) := by
  have hlen : (subword w a b).length = b - a := length_subword hb
  apply List.ext_getElem
  · rw [List.length_dropLast, hlen, length_subword (by omega)]
    omega
  · intro i hi₁ hi₂
    rw [List.getElem_dropLast, getElem_subword hb, getElem_subword (by omega)]

theorem subword_eq_of_forall_getElem {w w' : List α} (hlen : w'.length = w.length)
    {a b : ℕ} (hb : b ≤ w.length)
    (heq : ∀ i (hi : i < w.length), a ≤ i → i < b → w'[i]'(hlen ▸ hi) = w[i]) :
    subword w' a b = subword w a b := by
  have hb' : b ≤ w'.length := hlen ▸ hb
  apply List.ext_getElem
  · rw [length_subword hb', length_subword hb]
  · intro i hi' hi
    rw [getElem_subword hb' hi', getElem_subword hb hi]
    rw [length_subword hb] at hi
    exact heq (a + i) (by omega) (by omega) (by omega)

end Subwords

/-! ## Word Hamming distance and Hamming balls -/

section Hamming

variable {α : Type*} [DecidableEq α]

/-- Set of 0-indexed positions `< min w.length w'.length` where `w` and `w'` differ. -/
@[expose] def mismatchPositions (w w' : List α) : Finset ℕ :=
  (Finset.range (min w.length w'.length)).filter (fun i ↦ w[i]? ≠ w'[i]?)

/-- Word Hamming distance `|{i | w[i] ≠ w'[i]}|`. -/
@[expose] def wordHammingDist (w w' : List α) : ℕ :=
  (mismatchPositions w w').card

/-- The Hamming ball `{w' | w'.length = w.length ∧ wordHammingDist w w' ≤ k}`. -/
@[expose] def hammingBall (w : List α) (k : ℕ) : Set (List α) :=
  { w' | w'.length = w.length ∧ wordHammingDist w w' ≤ k }

theorem mem_mismatchPositions_iff {w w' : List α} (hlen : w'.length = w.length) {i : ℕ} :
    i ∈ mismatchPositions w w' ↔ ∃ hi : i < w.length, w[i] ≠ w'[i]'(hlen ▸ hi) := by
  simp only [mismatchPositions, hlen, min_self, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    rwa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi), ne_eq,
      Option.some.injEq] at hne
  · rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    rwa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi), ne_eq,
      Option.some.injEq]

/-- Equivalence between `wordHammingDist` on equal-length lists and Mathlib's `hammingDist`. -/
theorem wordHammingDist_eq_hammingDist {w w' : List α} (hlen : w'.length = w.length) :
    wordHammingDist w w' =
      hammingDist (fun i : Fin w.length ↦ w[i])
        (fun i : Fin w.length ↦ w'[i.1]'(by omega)) := by
  unfold wordHammingDist hammingDist
  apply Finset.card_bij (fun i hi ↦ ⟨i, (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp |>
    fun h ↦ lt_of_lt_of_le h (min_le_left _ _)⟩)
  · intro i hi
    obtain ⟨hlt, hne⟩ := (mem_mismatchPositions_iff hlen).mp hi
    simp [hne]
  · intro _ _ _ _ h
    exact Fin.ext_iff.mp h
  · intro ⟨i, hi⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact ⟨i, (mem_mismatchPositions_iff hlen).mpr ⟨hi, hmem⟩, rfl⟩

@[simp] theorem mismatchPositions_self (w : List α) : mismatchPositions w w = ∅ := by
  ext i
  simp [mismatchPositions]

@[simp] theorem wordHammingDist_self (w : List α) : wordHammingDist w w = 0 := by
  simp [wordHammingDist]

theorem wordHammingDist_eq_zero_iff {w w' : List α} (hlen : w'.length = w.length) :
    wordHammingDist w w' = 0 ↔ w = w' := by
  rw [wordHammingDist, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    apply List.ext_getElem hlen.symm
    intro i hi _
    by_contra hne
    exact h i ((mem_mismatchPositions_iff hlen).mpr ⟨hi, hne⟩)
  · rintro rfl i hi
    simp at hi

theorem subword_eq_of_disjoint_mismatchPositions {w w' : List α} (hlen : w'.length = w.length)
    {a b : ℕ} (hb : b ≤ w.length)
    (hdisj : ∀ i ∈ mismatchPositions w w', i < a ∨ b ≤ i) :
    subword w' a b = subword w a b := by
  refine subword_eq_of_forall_getElem hlen hb fun i hi ha hbi ↦ ?_
  by_contra hne
  have hmem : i ∈ mismatchPositions w w' :=
    (mem_mismatchPositions_iff hlen).mpr ⟨hi, Ne.symm hne⟩
  rcases hdisj i hmem with hlt | hge <;> omega

end Hamming

/-! ## Non-overlapping LZ77 factorization -/

section LZ77

variable {α : Type*}

/-- A *non-overlapping LZ77 history* starting from parsed prefix `h`: each phrase `u` is nonempty
and its strict prefix `u.dropLast` occurs as a contiguous factor entirely within `h`. -/
def IsHistory : List α → List (List α) → Prop
  | _, [] => True
  | h, u :: ws => u ≠ [] ∧ u.dropLast <:+: h ∧ IsHistory (h ++ u) ws

@[simp] theorem isHistory_nil (h : List α) : IsHistory h [] := trivial

@[simp] theorem isHistory_cons (h u : List α) (ws : List (List α)) :
    IsHistory h (u :: ws) ↔ u ≠ [] ∧ u.dropLast <:+: h ∧ IsHistory (h ++ u) ws :=
  Iff.rfl

/-- An *exhaustive* (greedy) non-overlapping LZ77 history: no non-final phrase already occurs as a
contiguous factor of the parsed prefix `h`. -/
def IsExhaustive : List α → List (List α) → Prop
  | _, [] => True
  | h, u :: ws => (ws ≠ [] → ¬ (u <:+: h)) ∧ IsExhaustive (h ++ u) ws

@[simp] theorem isExhaustive_nil (h : List α) : IsExhaustive h [] := trivial

@[simp] theorem isExhaustive_cons (h u : List α) (ws : List (List α)) :
    IsExhaustive h (u :: ws) ↔ (ws ≠ [] → ¬ (u <:+: h)) ∧ IsExhaustive (h ++ u) ws :=
  Iff.rfl

theorem ne_nil_of_isHistory :
    ∀ {h : List α} {ws : List (List α)}, IsHistory h ws → ∀ u ∈ ws, u ≠ []
  | _, [], _, _, hu => nomatch hu
  | _, _ :: _, ⟨hne, _, hws⟩, _, hu =>
    (List.mem_cons.mp hu).elim (· ▸ hne) (ne_nil_of_isHistory hws _)

theorem isHistory_append :
    ∀ (h : List α) (ws₁ ws₂ : List (List α)),
      IsHistory h (ws₁ ++ ws₂) ↔ IsHistory h ws₁ ∧ IsHistory (h ++ ws₁.flatten) ws₂
  | h, [], ws₂ => by simp
  | h, u :: ws₁, ws₂ => by
    simp only [List.cons_append, isHistory_cons, isHistory_append (h ++ u) ws₁ ws₂,
      List.flatten_cons, List.append_assoc]
    tauto

/-- Every non-overlapping LZ77 history is a valid self-referencing LZ77 history in
`Cslib.Algorithms.Lean.LempelZiv.LZ77` whenever the window covers the full word. -/
theorem isHistory_cslib_of_isHistory {W : ℕ} :
    ∀ {h : List α} {ws : List (List α)},
      IsHistory h ws → (h ++ ws.flatten).length ≤ W →
        Cslib.Algorithms.Lean.LempelZiv.LZ77.IsHistory W h ws
  | h, [], _, _ => Cslib.Algorithms.Lean.LempelZiv.LZ77.isHistory_nil W h
  | h, u :: ws, ⟨hne, hinf, hws⟩, hW => by
    rw [Cslib.Algorithms.Lean.LempelZiv.LZ77.isHistory_cons]
    have hhW : h.length ≤ W := by
      simp only [List.flatten_cons, List.length_append] at hW
      omega
    refine ⟨hne, Cslib.Algorithms.Lean.LempelZiv.LZ77.reproducible_of_infix hhW hinf,
      isHistory_cslib_of_isHistory hws ?_⟩
    rwa [List.append_assoc, ← List.flatten_cons]

private theorem isHistory_of_isTreeStructured :
    ∀ (dict : List (List α)) (h : List α) (ws : List (List α)),
      Cslib.Algorithms.Lean.LempelZiv.LZ78.IsTreeStructured dict ws →
      (∀ q ∈ dict, q <:+: h) → IsHistory h ws
  | _, _, [], _, _ => trivial
  | dict, h, w :: ws, ht, hdict => by
    rw [Cslib.Algorithms.Lean.LempelZiv.LZ78.isTreeStructured_cons] at ht
    obtain ⟨⟨q, hq, a, rfl⟩, ht⟩ := ht
    rw [isHistory_cons]
    refine ⟨by simp, ?_, isHistory_of_isTreeStructured (dict ++ [q ++ [a]])
      (h ++ (q ++ [a])) ws ht fun p hp ↦ ?_⟩
    · rw [List.dropLast_concat]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact List.nil_infix
      · exact hdict q hq
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hdict p hp).trans (List.prefix_append h _).isInfix
      · rw [List.mem_singleton.mp hp]
        exact (List.suffix_append _ _).isInfix

private theorem isHistory_mono_infix :
    ∀ {h₁ h₂ : List α} {ws : List (List α)},
      h₁ <:+ h₂ → IsHistory h₁ ws → IsHistory h₂ ws
  | _, _, [], _, _ => trivial
  | _, _, u :: _, ⟨p, rfl⟩, ⟨hne, hinf, hws⟩ =>
    ⟨hne, hinf.trans (List.suffix_append p _).isInfix,
      isHistory_mono_infix ⟨p, (List.append_assoc p _ u).symm⟩ hws⟩

private theorem not_isInfix_append_of_disjoint {u h q : List α} (hq : q ≠ [])
    (hdisj : ∀ a ∈ q, a ∉ u) (hnot : ¬ (q <:+: h)) : ¬ (q <:+: u ++ h) := by
  rintro ⟨s, t, heq⟩
  obtain ⟨c, q', rfl⟩ := List.exists_cons_of_ne_nil hq
  have hc_not_u : c ∉ u := hdisj c List.mem_cons_self
  by_cases hs : s.length < u.length
  · have hget := congrArg (fun l ↦ l[s.length]?) heq
    have h1 : (s ++ (c :: q') ++ t)[s.length]? = some c := by
      rw [List.append_assoc, List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    have h2 : (u ++ h)[s.length]? = some u[s.length] := by
      rw [List.getElem?_append_left hs, List.getElem?_eq_getElem hs]
    rw [h1, h2, Option.some.injEq] at hget
    exact hc_not_u (hget ▸ List.getElem_mem hs)
  · have hle : u.length ≤ s.length := by omega
    have hdrop := congrArg (List.drop u.length) heq
    rw [List.drop_left, List.append_assoc, List.drop_append_of_le_length hle] at hdrop
    exact hnot ⟨s.drop u.length, t, by simpa [List.append_assoc] using hdrop⟩

private theorem isExhaustive_append_disjoint :
    ∀ (h : List α) (ws₁ ws₂ : List (List α)),
      IsExhaustive h ws₁ →
      (∀ p_pre p_last, ws₁ = p_pre ++ [p_last] → ¬ (p_last <:+: h ++ p_pre.flatten)) →
      IsExhaustive [] ws₂ →
      (∀ q ∈ ws₂, q ≠ [] ∧ ∀ a ∈ q, a ∉ h ++ ws₁.flatten) →
      IsExhaustive h (ws₁ ++ ws₂)
  | h, [], ws₂, _, _, hex₂, hdisj => by
    simp only [List.nil_append, List.flatten_nil, List.append_nil] at hdisj ⊢
    suffices ∀ (k : List α) (ws : List (List α)),
        IsExhaustive k ws → (∀ q ∈ ws, q ≠ [] ∧ ∀ a ∈ q, a ∉ h) → IsExhaustive (h ++ k) ws by
      simpa using this [] ws₂ hex₂ hdisj
    intro k ws hex hd
    induction ws generalizing k with
    | nil => trivial
    | cons u us ih =>
      rw [isExhaustive_cons] at hex ⊢
      refine ⟨fun hne ↦ not_isInfix_append_of_disjoint (hd u List.mem_cons_self).1
        (hd u List.mem_cons_self).2 (hex.1 hne), ?_⟩
      simpa [List.append_assoc] using ih (k ++ u) hex.2 fun q hq ↦ hd q (List.mem_cons_of_mem u hq)
  | h, u :: [], ws₂, _, hlast, hex₂, hdisj => by
    simp only [List.singleton_append, isExhaustive_cons]
    refine ⟨fun _ ↦ by simpa using hlast [] u rfl, ?_⟩
    have hdisj' : ∀ q ∈ ws₂, q ≠ [] ∧ ∀ a ∈ q, a ∉ h ++ u := by
      simpa [List.flatten_singleton] using hdisj
    simpa using isExhaustive_append_disjoint (h ++ u) [] ws₂ trivial
      (fun _ _ heq ↦ by simp at heq) hex₂ (by simpa using hdisj')
  | h, u :: v :: ws₁, ws₂, hex₁, hlast, hex₂, hdisj => by
    rw [isExhaustive_cons] at hex₁
    simp only [List.cons_append, isExhaustive_cons]
    refine ⟨fun _ ↦ hex₁.1 (by simp), ?_⟩
    refine isExhaustive_append_disjoint (h ++ u) (v :: ws₁) ws₂ hex₁.2 (fun p_pre p_last heq ↦ ?_)
      hex₂ (fun q hq ↦ ?_)
    · simpa [List.append_assoc] using hlast (u :: p_pre) p_last (by simp [heq])
    · simpa [List.flatten_cons, List.append_assoc] using hdisj q hq

section Decidable

variable [DecidableEq α]

/-- Length of the longest prefix of `r` that occurs as a contiguous factor of `h`. -/
@[expose] def copyLen (h r : List α) : ℕ :=
  Nat.findGreatest (fun ℓ ↦ r.take ℓ <:+: h) r.length

/-- Fuel-driven greedy non-overlapping LZ77 parser after parsed prefix `h`. -/
@[expose] def parseAux : ℕ → List α → List α → List (List α)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | n + 1, h, a :: r =>
    let step := copyLen h (a :: r) + 1
    (a :: r).take step :: parseAux n (h ++ (a :: r).take step) ((a :: r).drop step)

/-- Greedy non-overlapping LZ77 factorization of `w`. -/
@[expose] def parse (w : List α) : List (List α) :=
  parseAux w.length [] w

/-- Non-overlapping LZ77 complexity of `w` (number of phrases in `parse w`). -/
@[expose] def complexity (w : List α) : ℕ :=
  (parse w).length

theorem copyLen_le_length (h r : List α) : copyLen h r ≤ r.length :=
  Nat.findGreatest_le _

theorem take_copyLen_isInfix (h r : List α) : r.take (copyLen h r) <:+: h :=
  Nat.findGreatest_spec (P := fun ℓ ↦ r.take ℓ <:+: h) (Nat.zero_le _) List.nil_infix

theorem le_copyLen {h r u : List α} (hu : u <:+: h) (hur : u <+: r) : u.length ≤ copyLen h r :=
  Nat.le_findGreatest hur.length_le (List.prefix_iff_eq_take.mp hur ▸ hu)

@[simp] theorem parse_nil : parse ([] : List α) = [] := rfl

@[simp] theorem complexity_nil : complexity ([] : List α) = 0 := rfl

private theorem parseAux_nil (n : ℕ) (h : List α) : parseAux n h [] = [] := by
  cases n <;> rfl

private theorem flatten_parseAux :
    ∀ (n : ℕ) (h r : List α), r.length ≤ n → (parseAux n h r).flatten = r
  | 0, _, r, hr => by
    simp [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hr), parseAux]
  | _ + 1, _, [], _ => rfl
  | n + 1, h, a :: r, hr => by
    rw [parseAux, List.flatten_cons, flatten_parseAux n _ _
      (by simp only [List.length_drop, List.length_cons] at hr ⊢; omega),
      List.take_append_drop]

@[simp] theorem flatten_parse (w : List α) : (parse w).flatten = w :=
  flatten_parseAux _ _ _ le_rfl

private theorem isHistory_parseAux :
    ∀ (n : ℕ) (h r : List α), IsHistory h (parseAux n h r)
  | 0, _, _ => trivial
  | _ + 1, _, [] => trivial
  | n + 1, h, a :: r => by
    rw [parseAux, isHistory_cons]
    refine ⟨by simp, ?_, isHistory_parseAux n _ _⟩
    have hpre : ((a :: r).take (copyLen h (a :: r) + 1)).dropLast <+:
        (a :: r).take (copyLen h (a :: r)) := by
      refine List.prefix_of_prefix_length_le ((List.dropLast_prefix _).trans (List.take_prefix _ _))
        (List.take_prefix _ _) ?_
      simp only [List.length_dropLast, List.length_take]
      omega
    exact hpre.isInfix.trans (take_copyLen_isInfix h (a :: r))

theorem isHistory_parse (w : List α) : IsHistory [] (parse w) :=
  isHistory_parseAux _ _ _

theorem ne_nil_of_mem_parse {w u : List α} (hu : u ∈ parse w) : u ≠ [] :=
  ne_nil_of_isHistory (isHistory_parse w) u hu

private theorem isExhaustive_parseAux :
    ∀ (n : ℕ) (h r : List α), IsExhaustive h (parseAux n h r)
  | 0, _, _ => trivial
  | _ + 1, _, [] => trivial
  | n + 1, h, a :: r => by
    rw [parseAux, isExhaustive_cons]
    refine ⟨fun hne hinf ↦ ?_, isExhaustive_parseAux n _ _⟩
    have hlt : copyLen h (a :: r) + 1 < (a :: r).length :=
      lt_of_not_ge fun hge ↦ hne (by rw [List.drop_eq_nil_of_le hge, parseAux_nil])
    have hle := le_copyLen hinf (List.take_prefix _ _)
    rw [List.length_take] at hle
    omega

theorem isExhaustive_parse (w : List α) : IsExhaustive [] (parse w) :=
  isExhaustive_parseAux _ _ _

theorem length_add_length_le_copyLen {h h' r u s : List α}
    (heq : h ++ r = h' ++ (u ++ s)) (hh : h'.length ≤ h.length) (hinf : u.dropLast <:+: h') :
    h'.length + u.length ≤ h.length + min (copyLen h r + 1) r.length := by
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  obtain hle | hlt := le_or_gt (h'.length + u.length) h.length
  · omega
  generalize hk : h.length - h'.length = k
  have hku : k < u.length := by omega
  obtain ⟨rfl, rfl⟩ : h = h' ++ u.take k ∧ r = u.drop k ++ s := by
    rw [← List.take_append_drop k u, List.append_assoc (u.take k), ← List.append_assoc h'] at heq
    exact List.append_inj heq (by simp only [List.length_append, List.length_take]; omega)
  have hsub : u.dropLast.drop k <:+: h' ++ u.take k :=
    ((List.drop_suffix k u.dropLast).isInfix.trans hinf).trans (List.prefix_append _ _).isInfix
  have hpre : u.dropLast.drop k <+: u.drop k ++ s :=
    ((List.dropLast_prefix u).drop k).trans (List.prefix_append _ _)
  have hle := le_copyLen hsub hpre
  simp only [List.length_drop, List.length_dropLast, List.length_append,
    List.length_take] at hle ⊢
  omega

private theorem length_parseAux_le :
    ∀ (ws : List (List α)) (n : ℕ) (h h' r : List α), r.length ≤ n →
      h ++ r = h' ++ ws.flatten → h'.length ≤ h.length → IsHistory h' ws →
      (parseAux n h r).length ≤ ws.length
  | [], n, h, h', r, _, heq, hh, _ => by
    have hlen := congrArg List.length heq
    simp only [List.flatten_nil, List.append_nil, List.length_append] at hlen
    have hr0 : r.length = 0 := by omega
    rw [List.eq_nil_of_length_eq_zero hr0, parseAux_nil]
  | _ :: _, 0, _, _, _, _, _, _, _ => by simp [parseAux]
  | _ :: _, _ + 1, _, _, [], _, _, _, _ => by simp [parseAux]
  | u :: ws, n + 1, h, h', a :: r, hr, heq, hh, ⟨_, hinf, hws⟩ => by
    rw [List.flatten_cons] at heq
    have hstep := length_add_length_le_copyLen heq hh hinf
    rw [parseAux, List.length_cons, List.length_cons]
    refine Nat.succ_le_succ (length_parseAux_le ws n _ (h' ++ u) _
      (by simp only [List.length_drop, List.length_cons] at hr ⊢; omega) ?_ ?_ hws)
    · rw [List.append_assoc, List.take_append_drop, heq, List.append_assoc]
    · simp only [List.length_append, List.length_take] at hstep ⊢
      omega

/-- **Greedy optimality of non-overlapping LZ77**: `complexity w` is at most the phrase count of
any non-overlapping LZ77 history of `w`. -/
theorem complexity_le_of_isHistory {w : List α} {ws : List (List α)}
    (hw : ws.flatten = w) (hws : IsHistory [] ws) : complexity w ≤ ws.length :=
  length_parseAux_le ws _ [] [] w le_rfl (by simp [hw]) le_rfl hws

private theorem parseAux_eq_of_isExhaustive :
    ∀ (ws : List (List α)) (n : ℕ) (h : List α), ws.flatten.length ≤ n →
      IsHistory h ws → IsExhaustive h ws → parseAux n h ws.flatten = ws
  | [], n, h, _, _, _ => parseAux_nil n h
  | u :: ws, n, h, hn, ⟨hne, hinf, hws⟩, ⟨hnr, hex⟩ => by
    obtain ⟨a, u', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by simp only [List.flatten_cons, List.length_append, List.length_cons] at hn; omega⟩
    rw [List.flatten_cons, List.cons_append, parseAux, ← List.cons_append]
    have hlow : u'.length ≤ copyLen h ((a :: u') ++ ws.flatten) := by
      simpa using le_copyLen hinf ((List.dropLast_prefix _).trans (List.prefix_append _ _))
    have htake : ((a :: u') ++ ws.flatten).take (copyLen h ((a :: u') ++ ws.flatten) + 1) =
        a :: u' := by
      rcases eq_or_ne ws [] with rfl | hws0
      · rw [List.flatten_nil, List.append_nil] at hlow ⊢
        exact List.take_of_length_le (List.length_cons ▸ Nat.succ_le_succ hlow)
      · have hup : copyLen h ((a :: u') ++ ws.flatten) < u'.length + 1 := by
          by_contra hge
          refine hnr hws0 ?_
          have hpre : a :: u' <+: ((a :: u') ++ ws.flatten).take
              (copyLen h ((a :: u') ++ ws.flatten)) :=
            List.prefix_of_prefix_length_le (List.prefix_append _ _) (List.take_prefix _ _)
              (by simp only [List.length_take, List.length_append, List.length_cons] at hge ⊢
                  omega)
          exact hpre.isInfix.trans (take_copyLen_isInfix h ((a :: u') ++ ws.flatten))
        have heq : copyLen h ((a :: u') ++ ws.flatten) + 1 = (a :: u').length :=
          List.length_cons ▸ Nat.le_antisymm hup (Nat.succ_le_succ hlow)
        exact heq ▸ List.take_left
    have hdrop : ((a :: u') ++ ws.flatten).drop (copyLen h ((a :: u') ++ ws.flatten) + 1) =
        ws.flatten :=
      List.append_cancel_left (htake ▸ List.take_append_drop _ ((a :: u') ++ ws.flatten))
    rw [htake, hdrop, parseAux_eq_of_isExhaustive ws n _
      (by simp only [List.flatten_cons, List.length_append, List.length_cons] at hn; omega) hws hex]

/-- **Uniqueness of exhaustive non-overlapping LZ77 factorization**: any exhaustive non-overlapping
LZ77 history of `w` equals `parse w`. -/
theorem parse_eq_of_isExhaustive {w : List α} {ws : List (List α)}
    (hw : ws.flatten = w) (hws : IsHistory [] ws) (hex : IsExhaustive [] ws) :
    parse w = ws :=
  hw ▸ parseAux_eq_of_isExhaustive ws _ [] le_rfl hws hex

/-- Self-referencing LZ77 complexity is at most non-overlapping LZ77 complexity. -/
theorem cslib_complexity_le_complexity (w : List α) :
    Cslib.Algorithms.Lean.LempelZiv.LZ77.complexity w ≤ complexity w := by
  refine Cslib.Algorithms.Lean.LempelZiv.LZ77.complexity_le_of_isHistory (flatten_parse w) ?_
  refine isHistory_cslib_of_isHistory (isHistory_parse w) ?_
  simp [flatten_parse]

/-- Non-overlapping LZ77 complexity is at most the LZ78 phrase count. -/
theorem complexity_le_lz78Parse_length (w : List α) :
    complexity w ≤ (Cslib.Algorithms.Lean.LempelZiv.LZ78.parse w).length := by
  refine complexity_le_of_isHistory (Cslib.Algorithms.Lean.LempelZiv.LZ78.flatten_parse w) ?_
  exact isHistory_of_isTreeStructured [] [] _
    (Cslib.Algorithms.Lean.LempelZiv.LZ78.isTreeStructured_parse w) (by simp)

theorem complexity_le_length (w : List α) : complexity w ≤ w.length := by
  have hsingle : IsHistory [] (w.map fun c ↦ [c]) := by
    suffices ∀ h (l : List α), IsHistory h (l.map fun c ↦ [c]) from this [] w
    intro h l
    induction l generalizing h with
    | nil => trivial
    | cons c cs ih =>
      simp only [List.map_cons, isHistory_cons, ne_eq, reduceCtorEq, not_false_eq_true,
        List.dropLast_singleton, List.nil_infix, true_and]
      exact ih (h ++ [c])
  have hflat : ∀ l : List α, (l.map fun c ↦ [c]).flatten = l := by
    intro l
    induction l with
    | nil => rfl
    | cons c cs ih => simp [ih]
  exact (complexity_le_of_isHistory (hflat w) hsingle).trans (by simp)

/-- Subadditivity of non-overlapping LZ77 complexity under concatenation. -/
theorem complexity_append_le (u v : List α) :
    complexity (u ++ v) ≤ complexity u + complexity v := by
  have hfl : (parse u ++ parse v).flatten = u ++ v := by
    rw [List.flatten_append, flatten_parse, flatten_parse]
  have hhist : IsHistory [] (parse u ++ parse v) := by
    rw [isHistory_append, flatten_parse, List.nil_append]
    exact ⟨isHistory_parse u, isHistory_mono_infix ⟨u, List.append_nil u⟩ (isHistory_parse v)⟩
  simpa [complexity] using complexity_le_of_isHistory hfl hhist

/-- Parse decomposition across disjoint alphabets when `u` ends with a fresh symbol. -/
theorem parse_append_of_disjoint {u v : List α}
    (hlast : ∀ u_init c, u = u_init ++ [c] → c ∉ u_init)
    (hdisj : ∀ a ∈ v, a ∉ u) :
    parse (u ++ v) = parse u ++ parse v := by
  refine parse_eq_of_isExhaustive
    (by rw [List.flatten_append, flatten_parse, flatten_parse]) ?_ ?_
  · rw [isHistory_append, flatten_parse, List.nil_append]
    exact ⟨isHistory_parse u, isHistory_mono_infix ⟨u, List.append_nil u⟩ (isHistory_parse v)⟩
  · refine isExhaustive_append_disjoint [] (parse u) (parse v)
      (isExhaustive_parse u) ?_ (isExhaustive_parse v) ?_
    · intro p_pre p_last heq hinf
      have hp_ne : p_last ≠ [] :=
        ne_nil_of_mem_parse (heq ▸ List.mem_append_right _ (List.mem_singleton.mpr rfl))
      let c := p_last.getLast hp_ne
      let p_init := p_last.dropLast
      have hp_split : p_last = p_init ++ [c] := (List.dropLast_append_getLast hp_ne).symm
      have hu_eq : u = (p_pre.flatten ++ p_init) ++ [c] := by
        have hfl := flatten_parse u
        rw [heq, List.flatten_append, List.flatten_singleton, hp_split, ← List.append_assoc] at hfl
        exact hfl.symm
      have hc_mem : c ∈ p_pre.flatten := by
        rw [List.nil_append, hp_split] at hinf
        exact hinf.subset (by simp)
      exact hlast _ c hu_eq (List.mem_append_left _ hc_mem)
    · intro q hq
      refine ⟨ne_nil_of_mem_parse hq, fun a ha ↦ ?_⟩
      rw [List.nil_append, flatten_parse]
      have hav : a ∈ v := flatten_parse v ▸ List.mem_flatten.mpr ⟨q, hq, ha⟩
      exact hdisj a hav

/-- Complexity additivity across disjoint alphabets when `u` ends with a fresh symbol. -/
theorem complexity_append_of_disjoint {u v : List α}
    (hlast : ∀ u_init c, u = u_init ++ [c] → c ∉ u_init)
    (hdisj : ∀ a ∈ v, a ∉ u) :
    complexity (u ++ v) = complexity u + complexity v := by
  simp [complexity, parse_append_of_disjoint hlast hdisj]

end Decidable

end LZ77

/-! ## Phrase endpoints and single-edit sensitivity -/

section Sensitivity

variable {α : Type*}

/-- Starting 0-indexed position of the `j`-th phrase in `ws`. -/
@[expose] def phraseStart (ws : List (List α)) (j : ℕ) : ℕ :=
  ((ws.take j).map List.length).sum

/-- Inclusive ending 0-indexed position of the `j`-th phrase in `ws`. -/
@[expose] def phraseEnd (ws : List (List α)) (j : ℕ) : ℕ :=
  phraseStart ws (j + 1) - 1

theorem phraseStart_succ {ws : List (List α)} {j : ℕ} (hj : j < ws.length) :
    phraseStart ws (j + 1) = phraseStart ws j + ws[j].length := by
  unfold phraseStart
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton]

theorem phraseStart_mono {ws : List (List α)} {i j : ℕ} (hij : i ≤ j) :
    phraseStart ws i ≤ phraseStart ws j := by
  unfold phraseStart
  obtain ⟨t, ht⟩ := (List.take_prefix_take_left hij).map List.length
  rw [← ht, List.sum_append]
  exact Nat.le_add_right _ _

theorem phraseStart_strictMono {ws : List (List α)} (hne : ∀ u ∈ ws, u ≠ [])
    {i j : ℕ} (hij : i < j) (hj : j ≤ ws.length) :
    phraseStart ws i < phraseStart ws j := by
  have hi : i < ws.length := lt_of_lt_of_le hij hj
  have hpos : 0 < ws[i].length := List.length_pos_iff.mpr (hne ws[i] (List.getElem_mem hi))
  calc phraseStart ws i
      < phraseStart ws i + ws[i].length := by omega
    _ = phraseStart ws (i + 1) := (phraseStart_succ hi).symm
    _ ≤ phraseStart ws j := phraseStart_mono hij

theorem phraseStart_length (ws : List (List α)) :
    phraseStart ws ws.length = ws.flatten.length := by
  simp [phraseStart, List.length_flatten]

theorem phraseEnd_add_one {ws : List (List α)} (hne : ∀ u ∈ ws, u ≠ [])
    {j : ℕ} (hj : j < ws.length) : phraseEnd ws j + 1 = phraseStart ws (j + 1) := by
  have hlt : phraseStart ws j < phraseStart ws (j + 1) :=
    phraseStart_strictMono hne (by omega) (by omega)
  unfold phraseEnd
  omega

theorem phraseStart_le_phraseEnd {ws : List (List α)} (hne : ∀ u ∈ ws, u ≠ [])
    {j : ℕ} (hj : j < ws.length) : phraseStart ws j ≤ phraseEnd ws j := by
  have := phraseStart_strictMono hne (by omega : j < j + 1) (by omega)
  unfold phraseEnd
  omega

theorem phraseEnd_lt_flatten_length {ws : List (List α)} (hne : ∀ u ∈ ws, u ≠ [])
    {j : ℕ} (hj : j < ws.length) : phraseEnd ws j < ws.flatten.length := by
  have h1 := phraseEnd_add_one hne hj
  have h2 : phraseStart ws (j + 1) ≤ phraseStart ws ws.length := phraseStart_mono (by omega)
  rw [phraseStart_length] at h2
  omega

theorem subword_phraseStart_succ {ws : List (List α)} {j : ℕ} (hj : j < ws.length) :
    subword ws.flatten (phraseStart ws j) (phraseStart ws (j + 1)) = ws[j] := by
  have hsplit : ws = ws.take j ++ [ws[j]] ++ ws.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j ws, List.drop_eq_getElem_cons hj]
    simp
  have hflat : ws.flatten = (ws.take j).flatten ++ ws[j] ++ (ws.drop (j + 1)).flatten := by
    conv_lhs => rw [hsplit]
    rw [List.flatten_append, List.flatten_append, List.flatten_singleton]
  have hl1 : (ws.take j).flatten.length = phraseStart ws j := by
    simp [phraseStart, List.length_flatten]
  have hl2 : ((ws.take j).flatten ++ ws[j]).length = phraseStart ws (j + 1) := by
    rw [List.length_append, hl1, phraseStart_succ hj]
  rw [subword, hflat, ← hl2, List.take_left, ← hl1, List.drop_left]

variable [DecidableEq α]

/-- Number of phrase-starts of `parse w'` lying in the inclusive interval `[l, r]`. -/
@[expose] def phraseStartsIn (w' : List α) (l r : ℕ) : ℕ :=
  ((Finset.range (complexity w')).filter fun i ↦
    l ≤ phraseStart (parse w') i ∧ phraseStart (parse w') i ≤ r).card

theorem phraseStartsIn_split (w' : List α) {l m r : ℕ} (hlm : l ≤ m) (hmr : m + 1 ≤ r) :
    phraseStartsIn w' l r = phraseStartsIn w' l m + phraseStartsIn w' (m + 1) r := by
  unfold phraseStartsIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hi, h1, h2⟩
      by_cases hm : phraseStart (parse w') i ≤ m
      · exact Or.inl ⟨hi, h1, hm⟩
      · exact Or.inr ⟨hi, by omega, h2⟩
    · rintro (⟨hi, h1, h2⟩ | ⟨hi, h1, h2⟩) <;> exact ⟨hi, by omega, by omega⟩
  · rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

theorem sum_phraseStartsIn_parse {w w' : List α} (hlen : w'.length = w.length) :
    (∑ j ∈ Finset.range (complexity w),
      phraseStartsIn w' (phraseStart (parse w) j) (phraseEnd (parse w) j)) = complexity w' := by
  set ws := parse w
  set ws' := parse w'
  have hne : ∀ u ∈ ws, u ≠ [] := fun _ hu ↦ ne_nil_of_mem_parse hu
  have hne' : ∀ u ∈ ws', u ≠ [] := fun _ hu ↦ ne_nil_of_mem_parse hu
  have hsum : ∀ m ≤ ws.length,
      (∑ j ∈ Finset.range m, phraseStartsIn w' (phraseStart ws j) (phraseEnd ws j)) =
        ((Finset.range ws'.length).filter fun i ↦ phraseStart ws' i < phraseStart ws m).card := by
    intro m hm
    induction m with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, phraseStart, List.take_zero, List.map_nil,
        List.sum_nil, Nat.not_lt_zero, Finset.filter_false, Finset.card_empty]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have h_end := phraseEnd_add_one hne (by omega : m < ws.length)
      unfold phraseStartsIn
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        change (i < ws'.length ∧ phraseStart ws' i < phraseStart ws m) ∨
            (i < ws'.length ∧ phraseStart ws m ≤ phraseStart ws' i ∧
              phraseStart ws' i ≤ phraseEnd ws m) ↔
          i < ws'.length ∧ phraseStart ws' i < phraseStart ws (m + 1)
        constructor
        · rintro (⟨hi, hlt⟩ | ⟨hi, hge, hle⟩)
          · refine ⟨hi, lt_of_lt_of_le hlt (phraseStart_mono (by omega))⟩
          · exact ⟨hi, by omega⟩
        · rintro ⟨hi, hlt⟩
          by_cases hm' : phraseStart ws' i < phraseStart ws m
          · exact Or.inl ⟨hi, hm'⟩
          · exact Or.inr ⟨hi, by omega, by omega⟩
      · rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2
        have hlt1 : phraseStart ws' i < phraseStart ws m := h1.2
        have hge2 : phraseStart ws m ≤ phraseStart ws' i := h2.2.1
        omega
  rw [show complexity w = ws.length from rfl, hsum ws.length le_rfl]
  have htot : phraseStart ws ws.length = w.length := by
    rw [phraseStart_length, flatten_parse]
  rw [htot]
  have hall : ∀ i ∈ Finset.range ws'.length, phraseStart ws' i < w.length := by
    intro i hi
    have hlt := phraseStart_strictMono hne' (Finset.mem_range.mp hi) le_rfl
    rw [phraseStart_length, flatten_parse, hlen] at hlt
    exact hlt
  rw [Finset.filter_true_of_mem hall, Finset.card_range]
  rfl

private theorem next_phraseStart_ge_of_isInfix {w' : List α} {i₁ i₂ : ℕ}
    (h12 : i₁ < i₂) (hi₂ : i₂ < complexity w')
    (hinf : subword w' (phraseStart (parse w') i₁) (phraseStart (parse w') i₂) <:+:
      w'.take (phraseStart (parse w') i₁)) : False := by
  have hi₁ : i₁ < (parse w').length := lt_of_lt_of_le h12 hi₂.le
  have hne' : ∀ u ∈ parse w', u ≠ [] := fun _ hu ↦ ne_nil_of_mem_parse hu
  have hsucc_le : phraseStart (parse w') (i₁ + 1) ≤ phraseStart (parse w') i₂ :=
    phraseStart_mono h12
  have hphrase_eq : (parse w')[i₁] =
      subword w' (phraseStart (parse w') i₁) (phraseStart (parse w') (i₁ + 1)) := by
    have h := subword_phraseStart_succ (ws := parse w') hi₁
    rw [flatten_parse] at h
    exact h.symm
  have hsub : (parse w')[i₁] <:+: w'.take (phraseStart (parse w') i₁) := by
    rw [hphrase_eq]
    exact (subword_isInfix_subword le_rfl (phraseStart_mono (by omega)) hsucc_le).trans hinf
  have hex : ∀ (k : ℕ) (h : List α) (ps : List (List α)),
      IsExhaustive h ps → (hk : k + 1 < ps.length) →
      ¬ (ps[k]'(by omega) <:+: h ++ (ps.take k).flatten) := by
    intro k h ps hps hk
    induction k generalizing h ps with
    | zero =>
      rcases ps with _ | ⟨u, _ | ⟨v, rest⟩⟩
      · simp at hk
      · simp at hk
      · simpa using ((isExhaustive_cons h u (v :: rest)).mp hps).1 (by simp)
    | succ k ih =>
      rcases ps with _ | ⟨u, rest⟩
      · simp at hk
      · have hps' := ((isExhaustive_cons h u rest).mp hps).2
        have hrec := ih (h ++ u) rest hps' (by simp at hk; omega)
        simpa [List.take_succ_cons, List.flatten_cons, List.append_assoc] using hrec
  have hi₂_len : i₂ < (parse w').length := hi₂
  have hnot := hex i₁ [] (parse w') (isExhaustive_parse w') (by omega)
  have htake_eq : ((parse w').take i₁).flatten = w'.take (phraseStart (parse w') i₁) := by
    have hfl : w' = ((parse w').take i₁).flatten ++ ((parse w').drop i₁).flatten :=
      (flatten_parse w').symm.trans (by rw [← List.flatten_append, List.take_append_drop])
    have hlen : ((parse w').take i₁).flatten.length = phraseStart (parse w') i₁ := by
      simp [phraseStart, List.length_flatten]
    rw [← hlen]
    conv_rhs => arg 2; rw [hfl]
    rw [List.take_left]
  rw [List.nil_append, htake_eq] at hnot
  exact hnot hsub

private theorem phraseStartsIn_le_one_of_isInfix {w' : List α} {a b : ℕ}
    (hinf : subword w' a b <:+: w'.take a) : phraseStartsIn w' a b ≤ 1 := by
  unfold phraseStartsIn
  refine Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi₁ hi₂
  by_contra hne
  have hcase : ∀ u v, u < v → v < complexity w' →
      a ≤ phraseStart (parse w') u → phraseStart (parse w') v ≤ b → False := by
    intro u v huv hv ha hb
    have hle : phraseStart (parse w') u ≤ phraseStart (parse w') v := phraseStart_mono huv.le
    have hsub : subword w' (phraseStart (parse w') u) (phraseStart (parse w') v) <:+:
        w'.take (phraseStart (parse w') u) :=
      ((subword_isInfix_subword ha hle hb).trans hinf).trans
        (List.take_prefix_take_left ha).isInfix
    exact next_phraseStart_ge_of_isInfix huv hv hsub
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hcase i₁ i₂ hlt hi₂.1 hi₁.2.1 hi₂.2.2
  · exact hcase i₂ i₁ hgt hi₁.1 hi₂.2.1 hi₁.2.2

/-- Every phrase of `parse w` contains at most `2` phrase-starts of `parse w'` when
`w' ∈ hammingBall w 1`. -/
theorem phraseStartsIn_le_two_of_hammingDist_le_one {w w' : List α}
    (hw' : w' ∈ hammingBall w 1) {j : ℕ} (hj : j < complexity w) :
    phraseStartsIn w' (phraseStart (parse w) j) (phraseEnd (parse w) j) ≤ 2 := by
  obtain ⟨hlen, hdist⟩ := hw'
  set ws := parse w
  set lj := phraseStart ws j
  set rj := phraseEnd ws j
  have hne : ∀ u ∈ ws, u ≠ [] := fun _ hu ↦ ne_nil_of_mem_parse hu
  have hlj_rj : lj ≤ rj := phraseStart_le_phraseEnd hne hj
  have hrj_lt : rj < w.length := by
    have := phraseEnd_lt_flatten_length hne hj
    rwa [flatten_parse] at this
  rcases eq_or_lt_of_le hlj_rj with heq | _hstrict
  · rw [heq]
    unfold phraseStartsIn
    refine (Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ ↦ ?_).trans (by omega)
    simp only [Finset.mem_filter, Finset.mem_range] at hi₁ hi₂
    by_contra hne_i
    rcases lt_or_gt_of_ne hne_i with hlt | hgt
    · have := phraseStart_strictMono (fun _ hu ↦ ne_nil_of_mem_parse hu) hlt hi₂.1.le
      omega
    · have := phraseStart_strictMono (fun _ hu ↦ ne_nil_of_mem_parse hu) hgt hi₁.1.le
      omega
  · have hsub_phrase : subword w lj (rj + 1) = ws[j]'hj := by
      have h1 := subword_phraseStart_succ (ws := ws) hj
      rw [flatten_parse, ← phraseEnd_add_one hne hj] at h1
      exact h1
    have hdrop : (ws[j]'hj).dropLast = subword w lj rj := by
      rw [← hsub_phrase, dropLast_subword (by omega) (by omega)]
      simp
    have hoccur : subword w lj rj <:+: w.take lj := by
      rw [← hdrop]
      have hhist_at : ∀ k (h : List α) (ps : List (List α)),
          IsHistory h ps → (hk : k < ps.length) →
          ps[k].dropLast <:+: h ++ (ps.take k).flatten := by
        intro k h ps hps hk
        induction k generalizing h ps with
        | zero =>
          rcases ps with _ | ⟨u, rest⟩
          · simp at hk
          · simp only [isHistory_cons] at hps
            simpa using hps.2.1
        | succ k ih =>
          rcases ps with _ | ⟨u, rest⟩
          · simp at hk
          · simp only [isHistory_cons] at hps
            have hrec := ih (h ++ u) rest hps.2.2 (by simp at hk; omega)
            simpa [List.take_succ_cons, List.flatten_cons, List.append_assoc] using hrec
      have hinf := hhist_at j [] ws (isHistory_parse w) hj
      have htake_eq : (ws.take j).flatten = w.take lj := by
        have hfl : w = (ws.take j).flatten ++ (ws.drop j).flatten := by
          rw [← flatten_parse w, ← List.flatten_append, List.take_append_drop]
        have hlen_j : (ws.take j).flatten.length = lj := by
          simp [lj, phraseStart, List.length_flatten]
        conv_rhs => rw [hfl, ← hlen_j, List.take_left]
      rwa [List.nil_append, htake_eq] at hinf
    obtain ⟨x, y, hxy, hy_take, hsub_xy_take⟩ := exists_subword_of_isInfix hoccur
    have hyL : y ≤ lj := le_trans hy_take (List.length_take_le lj w)
    have hy_len : y ≤ w.length := (hyL.trans hlj_rj).trans hrj_lt.le
    have hsub_xy : subword w x y = subword w lj rj := by
      rw [← subword_take_eq hyL, hsub_xy_take]
    have hlen_xy : y - x = rj - lj := by
      have h1 := congrArg List.length hsub_xy
      rw [length_subword hy_len, length_subword hrj_lt.le] at h1
      exact h1
    rcases Nat.eq_zero_or_pos (wordHammingDist w w') with hd0 | hd1
    · obtain rfl := (wordHammingDist_eq_zero_iff hlen).mp hd0
      exact (phraseStartsIn_le_one_of_isInfix hoccur).trans (by omega)
    · have hcard1 : (mismatchPositions w w').card = 1 := by unfold wordHammingDist at *; omega
      obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hcard1
      by_cases he_in_xy : x ≤ e ∧ e < y
      · set mid := lj + (e - x)
        have hmid_bounds : lj ≤ mid ∧ mid < rj := by omega
        have hmid_le : mid ≤ w.length := by omega
        have he_le : e ≤ w.length := by omega
        rw [phraseStartsIn_split w' hmid_bounds.1 (by omega : mid + 1 ≤ rj)]
        have hleft : subword w' lj mid <:+: w'.take lj := by
          have h1 : subword w' lj mid = subword w lj mid :=
            subword_eq_of_disjoint_mismatchPositions hlen hmid_le fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
          have h2 : subword w lj mid = subword w x e := by
            have h3 : subword (subword w lj rj) 0 (e - x) = subword w lj mid :=
              subword_subword_zero (by omega)
            have h4 : subword (subword w x y) 0 (e - x) = subword w x e := by
              simpa [Nat.add_sub_of_le he_in_xy.1] using
                (subword_subword_zero (w := w) (a := x) (b := y) (len := e - x) (by omega))
            rw [← h3, ← hsub_xy, h4]
          have h5 : subword w x e = subword w' x e :=
            (subword_eq_of_disjoint_mismatchPositions hlen he_le fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega).symm
          rw [h1, h2, h5, ← subword_zero]
          exact subword_isInfix_subword (Nat.zero_le x) (by omega) (by omega)
        have hright : subword w' (mid + 1) rj <:+: w'.take (mid + 1) := by
          have h1 : subword w' (mid + 1) rj = subword w (mid + 1) rj :=
            subword_eq_of_disjoint_mismatchPositions hlen hrj_lt.le fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
          have h2 : subword w (mid + 1) rj = subword w (e + 1) y := by
            have hlen_l : (subword w lj (mid + 1)).length = (subword w x (e + 1)).length := by
              rw [length_subword (by omega), length_subword (by omega)]
              dsimp only [mid]
              omega
            have hcat : subword w lj (mid + 1) ++ subword w (mid + 1) rj =
                subword w x (e + 1) ++ subword w (e + 1) y := by
              rw [subword_append_subword (by omega) (by omega),
                subword_append_subword (by omega) (by omega), hsub_xy]
            exact (List.append_inj hcat hlen_l).2
          have h5 : subword w (e + 1) y = subword w' (e + 1) y :=
            (subword_eq_of_disjoint_mismatchPositions hlen hy_len fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega).symm
          rw [h1, h2, h5, ← subword_zero]
          exact subword_isInfix_subword (Nat.zero_le (e + 1)) (by omega) (by omega)
        have hl1 := phraseStartsIn_le_one_of_isInfix hleft
        have hr1 := phraseStartsIn_le_one_of_isInfix hright
        omega
      · by_cases he_in_lj : lj ≤ e ∧ e < rj
        · rw [phraseStartsIn_split w' he_in_lj.1 (by omega : e + 1 ≤ rj)]
          have hxy_clean : subword w' x y = subword w x y :=
            subword_eq_of_disjoint_mismatchPositions hlen hy_len fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
          have hleft : subword w' lj e <:+: w'.take lj := by
            have h1 : subword w' lj e = subword w lj e :=
              subword_eq_of_disjoint_mismatchPositions hlen (by omega) fun i hi ↦ by
                rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
            rw [h1, ← subword_zero]
            exact ((subword_isInfix_subword le_rfl he_in_lj.1 he_in_lj.2.le).trans
              (hsub_xy ▸ hxy_clean ▸ subword_isInfix_subword (Nat.zero_le x) hxy hyL))
          have hright : subword w' (e + 1) rj <:+: w'.take (e + 1) := by
            have h1 : subword w' (e + 1) rj = subword w (e + 1) rj :=
              subword_eq_of_disjoint_mismatchPositions hlen hrj_lt.le fun i hi ↦ by
                rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
            rw [h1, ← subword_zero]
            exact ((subword_isInfix_subword (by omega) (by omega) le_rfl).trans
              (hsub_xy ▸ hxy_clean ▸ subword_isInfix_subword (Nat.zero_le x) hxy (by omega)))
          have hl1 := phraseStartsIn_le_one_of_isInfix hleft
          have hr1 := phraseStartsIn_le_one_of_isInfix hright
          omega
        · have h1 : subword w' lj rj = subword w lj rj :=
            subword_eq_of_disjoint_mismatchPositions hlen hrj_lt.le fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
          have h2 : subword w' x y = subword w x y :=
            subword_eq_of_disjoint_mismatchPositions hlen hy_len fun i hi ↦ by
              rw [he_eq, Finset.mem_singleton] at hi; subst hi; omega
          have hinf' : subword w' lj rj <:+: w'.take lj := by
            rw [h1, ← hsub_xy, ← h2, ← subword_zero]
            exact subword_isInfix_subword (Nat.zero_le x) hxy hyL
          exact (phraseStartsIn_le_one_of_isInfix hinf').trans (by omega)

/-- **Single-edit sensitivity bound for non-overlapping LZ77**: changing at most one symbol of a
word at most doubles its non-overlapping LZ77 complexity. -/
theorem complexity_le_two_mul_of_hammingDist_le_one {w w' : List α}
    (hw' : w' ∈ hammingBall w 1) : complexity w' ≤ 2 * complexity w := by
  calc complexity w'
      = ∑ j ∈ Finset.range (complexity w),
          phraseStartsIn w' (phraseStart (parse w) j) (phraseEnd (parse w) j) :=
        (sum_phraseStartsIn_parse hw'.1).symm
    _ ≤ ∑ _j ∈ Finset.range (complexity w), 2 :=
        Finset.sum_le_sum fun j hj ↦
          phraseStartsIn_le_two_of_hammingDist_le_one hw' (Finset.mem_range.mp hj)
    _ = 2 * complexity w := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

end Sensitivity

end CslibFrontier.Algorithms.Lean.LempelZiv.LZ77NonOverlapping
