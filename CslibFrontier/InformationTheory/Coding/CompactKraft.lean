/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.InformationTheory.Coding.Kraft

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compact Prefix-Free Codes and the $D$-ary Kraft Equality

This module develops the theory of *compact* (maximal / complete) prefix-free codes over finite
alphabets under standard Lean axioms, together with the constructive $D$-ary Kraft converse and
the Kraft equality characterization of finite compact prefix-free codes.

## Main definitions

* `CslibFrontier.InformationTheory.IsCompactPrefixFree`: maximal (compact) prefix-free codes.
* `CslibFrontier.InformationTheory.digitsOfNat`, `CslibFrontier.InformationTheory.natOfDigits`:
  fixed-width most-significant-digit-first base-`D` representation over `Fin D`.

## Main results

* `CslibFrontier.InformationTheory.isCompactPrefixFree_iff_comparable`: a prefix-free code `S` is
  compact iff every word over `α` is prefix-comparable with some codeword in `S`.
* `CslibFrontier.InformationTheory.isCompactPrefixFree_iff_sum_pow_eq`: integer-scaled Kraft
  equality `∑ c ∈ S, (Fintype.card α) ^ (L - c.length) = (Fintype.card α) ^ L`.
* `CslibFrontier.InformationTheory.isCompactPrefixFree_iff_kraft_eq_one`: real Kraft equality
  `IsPrefixFree ↑S ∧ ∑ c ∈ S, (1 / (Fintype.card α : ℝ)) ^ c.length = 1`.
* `CslibFrontier.InformationTheory.exists_card_eq_one_add_mul_sub_one_of_isCompactPrefixFree`:
  every finite compact prefix-free code over an alphabet of size `D ≥ 2` has `1 + n * (D - 1)`
  codewords.
* `CslibFrontier.InformationTheory.exists_isPrefixFree_of_kraft_nat`: constructive $D$-ary Kraft
  converse.
* `CslibFrontier.InformationTheory.exists_isPrefixFree_iff_kraft_le_one_of_two_le_card`: $D$-ary
  Kraft theorem.
* `CslibFrontier.InformationTheory.exists_isCompactPrefixFree_iff_kraft_eq_one_of_two_le_card`:
  $D$-ary compact Kraft theorem.
-/

public section

namespace CslibFrontier.InformationTheory

/-- A set of words `S ⊆ List α` is a *compact* (or *maximal* / *complete*) prefix-free code if `S`
is prefix-free and no word `w ∉ S` can be added without violating prefix-freeness. -/
def IsCompactPrefixFree {α : Type*} (S : Set (List α)) : Prop :=
  _root_.InformationTheory.IsPrefixFree S ∧
    ∀ w : List α, w ∉ S → ¬ _root_.InformationTheory.IsPrefixFree (insert w S)

/-- Every compact prefix-free code is prefix-free. -/
theorem IsCompactPrefixFree.isPrefixFree {α : Type*} {S : Set (List α)}
    (hS : IsCompactPrefixFree S) : _root_.InformationTheory.IsPrefixFree S :=
  hS.1

/-- A set of words `S` is a compact prefix-free code if and only if `S` is prefix-free and every
word over `α` has a prefix in `S` or is a prefix of some word in `S`. -/
theorem isCompactPrefixFree_iff_comparable {α : Type*} {S : Set (List α)} :
    IsCompactPrefixFree S ↔
      _root_.InformationTheory.IsPrefixFree S ∧
        ∀ w : List α, ∃ c ∈ S, c <+: w ∨ w <+: c := by
  constructor
  · rintro ⟨hpf, hmax⟩
    refine ⟨hpf, fun w ↦ ?_⟩
    by_cases hw : w ∈ S
    · exact ⟨w, hw, Or.inl (List.prefix_refl w)⟩
    · have hnot := hmax w hw
      unfold _root_.InformationTheory.IsPrefixFree at hnot
      push Not at hnot
      rcases hnot with ⟨x, hx, y, hy, hxy, hne⟩
      rcases Set.mem_insert_iff.mp hx with rfl | hxS
      · rcases Set.mem_insert_iff.mp hy with rfl | hyS
        · exact absurd rfl hne
        · exact ⟨y, hyS, Or.inr hxy⟩
      · rcases Set.mem_insert_iff.mp hy with rfl | hyS
        · exact ⟨x, hxS, Or.inl hxy⟩
        · exact absurd (hpf x hxS y hyS hxy) hne
  · rintro ⟨hpf, hcomp⟩
    refine ⟨hpf, fun w hw hins ↦ ?_⟩
    rcases hcomp w with ⟨c, hcS, hcw | hwc⟩
    · have heq := hins c (Set.mem_insert_of_mem w hcS) w (Set.mem_insert w S) hcw
      exact hw (heq ▸ hcS)
    · have heq := hins w (Set.mem_insert w S) c (Set.mem_insert_of_mem w hcS) hwc
      exact hw (heq.symm ▸ hcS)

/-- The singleton code `{[]}` consisting of the empty word is compact prefix-free over any
alphabet. -/
theorem isCompactPrefixFree_singleton_nil (α : Type*) :
    IsCompactPrefixFree ({([] : List α)} : Set (List α)) := by
  rw [isCompactPrefixFree_iff_comparable]
  refine ⟨fun x hx y hy _ ↦ ?_, fun w ↦ ⟨[], Set.mem_singleton [], Or.inl List.nil_prefix⟩⟩
  rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]

private lemma prefix_or_prefix_of_prefix {α : Type*} {u v w : List α}
    (hu : u <+: w) (hv : v <+: w) :
    u <+: v ∨ v <+: u := by
  induction u generalizing v w with
  | nil => exact Or.inl List.nil_prefix
  | cons a u ih =>
    cases v with
    | nil => exact Or.inr List.nil_prefix
    | cons b v =>
      cases w with
      | nil => cases List.prefix_nil.mp hu
      | cons c w =>
        rcases List.cons_prefix_cons.mp hu with ⟨rfl, hu'⟩
        rcases List.cons_prefix_cons.mp hv with ⟨hbc, hv'⟩
        subst hbc
        rcases ih hu' hv' with h | h
        · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

section Cylinders

variable {α : Type*} [Fintype α]

private def wordCylinder [DecidableEq α] (L : ℕ) (c : List α) : Finset (Fin L → α) :=
  Finset.univ.filter fun g ↦ c <+: List.ofFn g

private lemma mem_wordCylinder [DecidableEq α] {L : ℕ} {c : List α} {g : Fin L → α} :
    g ∈ wordCylinder L c ↔ c <+: List.ofFn g := by
  simp only [wordCylinder, Finset.mem_filter, Finset.mem_univ, true_and]

private lemma card_wordCylinder [DecidableEq α] {L : ℕ} {c : List α} (hc : c.length ≤ L) :
    (wordCylinder L c).card = (Fintype.card α) ^ (L - c.length) := by
  let extFn : (Fin (L - c.length) → α) → (Fin L → α) := fun h i ↦
    if hi : (i : ℕ) < c.length then c[i.val] else
      h ⟨i.val - c.length, by omega⟩
  have hofFn_ext : ∀ h : Fin (L - c.length) → α,
      List.ofFn (extFn h) = c ++ List.ofFn h := by
    intro h
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append]
      omega
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, extFn]
      by_cases hic : i < c.length
      · rw [dite_eq_left hic, List.getElem_append_left hic]
      · rw [dite_eq_right hic, List.getElem_append_right (Nat.not_lt.mp hic), List.getElem_ofFn]
  have hinj : Function.Injective extFn := by
    intro h₁ h₂ heq
    have hlist := congrArg List.ofFn heq
    rw [hofFn_ext, hofFn_ext] at hlist
    have hlist' := List.append_cancel_left hlist
    funext j
    have hj := congrArg (fun l ↦ l[j.val]?) hlist'
    simpa only [List.getElem?_ofFn, dite_eq_left j.isLt, Option.some.injEq] using hj
  have himg : Finset.univ.image extFn = wordCylinder L c := by
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_wordCylinder]
    constructor
    · rintro ⟨h, rfl⟩
      rw [hofFn_ext]
      exact List.prefix_append c (List.ofFn h)
    · rintro ⟨rest, hrest⟩
      have hlen_rest : rest.length = L - c.length := by
        have := congrArg List.length hrest
        simp only [List.length_append, List.length_ofFn] at this
        omega
      let hfn : Fin (L - c.length) → α := fun j ↦ rest[j.val]'(by omega)
      refine ⟨hfn, ?_⟩
      apply List.ofFn_injective
      rw [hofFn_ext hfn, ← hrest]
      congr 1
      apply List.ext_getElem
      · simp only [List.length_ofFn, hlen_rest]
      · intro j hj₁ hj₂
        simp only [List.getElem_ofFn, hfn]
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]

private lemma pairwiseDisjoint_wordCylinder [DecidableEq α] {S : Finset (List α)}
    (hpf : _root_.InformationTheory.IsPrefixFree (S : Set (List α))) (L : ℕ) :
    (S : Set (List α)).PairwiseDisjoint (wordCylinder L) := by
  intro c₁ hc₁ c₂ hc₂ hne
  change Disjoint (wordCylinder L c₁) (wordCylinder L c₂)
  rw [Finset.disjoint_left]
  intro g hg₁ hg₂
  rw [mem_wordCylinder] at hg₁ hg₂
  rcases prefix_or_prefix_of_prefix hg₁ hg₂ with h | h
  · exact hne (hpf c₁ hc₁ c₂ hc₂ h)
  · exact hne (hpf c₂ hc₂ c₁ hc₁ h).symm

/-- For any finite prefix-free code `S : Finset (List α)` with codeword lengths at most `L`,
`∑ c ∈ S, (Fintype.card α) ^ (L - c.length) ≤ (Fintype.card α) ^ L`. -/
theorem sum_card_pow_sub_length_le {S : Finset (List α)} {L : ℕ}
    (hpf : _root_.InformationTheory.IsPrefixFree (S : Set (List α)))
    (hL : ∀ c ∈ S, c.length ≤ L) :
    (∑ c ∈ S, (Fintype.card α) ^ (L - c.length)) ≤ (Fintype.card α) ^ L := by
  classical
  have hcard : (S.biUnion (wordCylinder L)).card =
      ∑ c ∈ S, (Fintype.card α) ^ (L - c.length) := by
    rw [Finset.card_biUnion (pairwiseDisjoint_wordCylinder hpf L)]
    exact Finset.sum_congr rfl fun c hc ↦ card_wordCylinder (hL c hc)
  rw [← hcard]
  calc (S.biUnion (wordCylinder L)).card
      ≤ (Finset.univ : Finset (Fin L → α)).card := Finset.card_le_univ _
    _ = (Fintype.card α) ^ L := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- **Integer-Scaled Kraft Equality for Compact Prefix-Free Codes**. -/
theorem isCompactPrefixFree_iff_sum_pow_eq [Nonempty α] {S : Finset (List α)} {L : ℕ}
    (hL : ∀ c ∈ S, c.length ≤ L) :
    IsCompactPrefixFree (S : Set (List α)) ↔
      _root_.InformationTheory.IsPrefixFree (S : Set (List α)) ∧
        (∑ c ∈ S, (Fintype.card α) ^ (L - c.length)) = (Fintype.card α) ^ L := by
  classical
  rw [isCompactPrefixFree_iff_comparable]
  constructor
  · rintro ⟨hpf, hcomp⟩
    refine ⟨hpf, ?_⟩
    have huniv : S.biUnion (wordCylinder L) = Finset.univ := by
      ext g
      simp only [Finset.mem_biUnion, mem_wordCylinder, Finset.mem_univ, iff_true]
      rcases hcomp (List.ofFn g) with ⟨c, hcS, hcg | hgc⟩
      · exact ⟨c, hcS, hcg⟩
      · have hlen_le := List.IsPrefix.length_le hgc
        rw [List.length_ofFn] at hlen_le
        rcases hgc with ⟨t, ht⟩
        have htnil : t = [] := by
          have := congrArg List.length ht
          simp only [List.length_append, List.length_ofFn] at this
          have := hL c hcS
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [htnil, List.append_nil] at ht
        exact ⟨c, hcS, ht ▸ List.prefix_refl _⟩
    have hcard := congrArg Finset.card huniv
    rw [Finset.card_biUnion (pairwiseDisjoint_wordCylinder hpf L), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin] at hcard
    rw [← hcard]
    exact Finset.sum_congr rfl fun c hc ↦ (card_wordCylinder (hL c hc)).symm
  · rintro ⟨hpf, hsum⟩
    refine ⟨hpf, fun w ↦ ?_⟩
    have hcard : (S.biUnion (wordCylinder L)).card =
        (Finset.univ : Finset (Fin L → α)).card := by
      rw [Finset.card_biUnion (pairwiseDisjoint_wordCylinder hpf L), Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, ← hsum]
      exact Finset.sum_congr rfl fun c hc ↦ card_wordCylinder (hL c hc)
    have huniv : S.biUnion (wordCylinder L) = Finset.univ :=
      Finset.eq_univ_of_card _ hcard
    by_cases hw : w.length ≤ L
    · let a₀ : α := Classical.arbitrary α
      let u : List α := w ++ List.replicate (L - w.length) a₀
      have hu_len : u.length = L := by
        simp only [u, List.length_append, List.length_replicate]; omega
      let g : Fin L → α := fun i ↦ u[i.val]'(by omega)
      have hofFn_g : List.ofFn g = u := by
        apply List.ext_getElem
        · simp only [List.length_ofFn, hu_len]
        · intro i hi₁ hi₂; simp only [List.getElem_ofFn, g]
      have hg_mem : g ∈ S.biUnion (wordCylinder L) := by rw [huniv]; exact Finset.mem_univ g
      rcases Finset.mem_biUnion.mp hg_mem with ⟨c, hcS, hcg⟩
      rw [mem_wordCylinder, hofFn_g] at hcg
      exact ⟨c, hcS, prefix_or_prefix_of_prefix hcg (List.prefix_append w _)⟩
    · push Not at hw
      let u : List α := w.take L
      have hu_len : u.length = L := List.length_take_of_le (le_of_lt hw)
      let g : Fin L → α := fun i ↦ u[i.val]'(by omega)
      have hofFn_g : List.ofFn g = u := by
        apply List.ext_getElem
        · simp only [List.length_ofFn, hu_len]
        · intro i hi₁ hi₂; simp only [List.getElem_ofFn, g]
      have hg_mem : g ∈ S.biUnion (wordCylinder L) := by rw [huniv]; exact Finset.mem_univ g
      rcases Finset.mem_biUnion.mp hg_mem with ⟨c, hcS, hcg⟩
      rw [mem_wordCylinder, hofFn_g] at hcg
      exact ⟨c, hcS, Or.inl (hcg.trans (List.take_prefix L w))⟩

/-- **Kraft Equality Theorem for Finite Compact Prefix-Free Codes**. -/
theorem isCompactPrefixFree_iff_kraft_eq_one [Nonempty α] {S : Finset (List α)} :
    IsCompactPrefixFree (S : Set (List α)) ↔
      _root_.InformationTheory.IsPrefixFree (S : Set (List α)) ∧
        (∑ c ∈ S, (1 / (Fintype.card α : ℝ)) ^ c.length) = 1 := by
  let L : ℕ := S.sup List.length
  have hL : ∀ c ∈ S, c.length ≤ L := fun c hc ↦ Finset.le_sup (f := List.length) hc
  rw [isCompactPrefixFree_iff_sum_pow_eq hL]
  have hD_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hD_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hD_pos
  have hcast : ((∑ c ∈ S, (Fintype.card α) ^ (L - c.length) : ℕ) : ℝ) =
      (Fintype.card α : ℝ) ^ L * ∑ c ∈ S, (1 / (Fintype.card α : ℝ)) ^ c.length := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    rw [one_div, inv_pow]
    exact pow_sub₀ _ hD_ne (hL c hc)
  constructor
  · rintro ⟨hpf, hsum⟩
    refine ⟨hpf, ?_⟩
    have hreal : ((∑ c ∈ S, (Fintype.card α) ^ (L - c.length) : ℕ) : ℝ) =
        (Fintype.card α : ℝ) ^ L := by exact_mod_cast hsum
    rw [hcast] at hreal
    exact mul_left_cancel₀ (pow_ne_zero L hD_ne) (hreal.trans (mul_one _).symm)
  · rintro ⟨hpf, hkraft⟩
    refine ⟨hpf, ?_⟩
    have hreal : ((∑ c ∈ S, (Fintype.card α) ^ (L - c.length) : ℕ) : ℝ) =
        ((Fintype.card α ^ L : ℕ) : ℝ) := by
      rw [hcast, hkraft, mul_one]; push_cast; rfl
    exact_mod_cast hreal

/-- Every finite compact prefix-free code over an alphabet of cardinality `D ≥ 2` has
`1 + n * (D - 1)` codewords for some `n : ℕ`. -/
theorem exists_card_eq_one_add_mul_sub_one_of_isCompactPrefixFree {S : Finset (List α)}
    (hD : 2 ≤ Fintype.card α) (hS : IsCompactPrefixFree (S : Set (List α))) :
    ∃ n : ℕ, S.card = 1 + n * (Fintype.card α - 1) := by
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let L : ℕ := S.sup List.length
  have hL : ∀ c ∈ S, c.length ≤ L := fun c hc ↦ Finset.le_sup (f := List.length) hc
  have hsum := ((isCompactPrefixFree_iff_sum_pow_eq hL).mp hS).2
  set D := Fintype.card α
  set m := D - 1
  have hDm : D = m + 1 := by omega
  have h1_le_card : 1 ≤ S.card := by
    by_contra hlt
    have h0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [h0, Finset.sum_empty] at hsum
    have : 0 < D ^ L := Nat.pow_pos (by omega)
    omega
  have hdvd_pow : ∀ k : ℕ, m ∣ D ^ k - 1 := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Nat.sub_self, dvd_zero]
    | succ k ih =>
      have hk1 : 1 ≤ D ^ k := Nat.one_le_pow k D (by omega)
      have hmul : D * D ^ k = m * D ^ k + D ^ k := by
        calc D * D ^ k = (m + 1) * D ^ k := congrArg (· * D ^ k) hDm
          _ = m * D ^ k + D ^ k := add_one_mul m (D ^ k)
      have hsplit : D ^ (k + 1) - 1 = m * D ^ k + (D ^ k - 1) := by
        rw [pow_succ', hmul]
        omega
      rw [hsplit]
      exact Nat.dvd_add (dvd_mul_right m (D ^ k)) ih
  have hdvd_sum : m ∣ ∑ c ∈ S, (D ^ (L - c.length) - 1) :=
    Finset.dvd_sum fun c _ ↦ hdvd_pow (L - c.length)
  have hsum_split : (∑ c ∈ S, (D ^ (L - c.length) - 1)) + S.card = D ^ L := by
    have hcard_ones : S.card = ∑ _c ∈ S, (1 : ℕ) := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [hcard_ones, ← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    exact Nat.sub_add_cancel (Nat.one_le_pow _ D (by omega))
  have heq_sub : (∑ c ∈ S, (D ^ (L - c.length) - 1)) + (S.card - 1) = D ^ L - 1 := by
    have hDL : 1 ≤ D ^ L := Nat.one_le_pow L D (by omega)
    omega
  have hdvd_card : m ∣ S.card - 1 :=
    (Nat.dvd_add_right hdvd_sum).mp (heq_sub ▸ hdvd_pow L)
  rcases hdvd_card with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  calc S.card = (S.card - 1) + 1 := (Nat.sub_add_cancel h1_le_card).symm
    _ = m * n + 1 := by rw [hn]
    _ = 1 + n * m := by ring

end Cylinders

/-- Most-significant-digit-first `k`-digit base-`D` representation of `q % D ^ k` over `Fin D`. -/
def digitsOfNat (D : ℕ) [NeZero D] : ℕ → ℕ → List (Fin D)
  | 0, _ => []
  | k + 1, q => digitsOfNat D k (q / D) ++ [⟨q % D, Nat.mod_lt q (NeZero.pos D)⟩]

/-- Natural number represented by a most-significant-digit-first list of base-`D` digits. -/
def natOfDigits {D : ℕ} (ds : List (Fin D)) : ℕ :=
  ds.foldl (fun acc d ↦ D * acc + d.val) 0

@[simp]
theorem length_digitsOfNat (D : ℕ) [NeZero D] (k q : ℕ) :
    (digitsOfNat D k q).length = k := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => simp only [digitsOfNat, List.length_append, ih, List.length_singleton]

private theorem foldl_digitStep_eq {D : ℕ} (ds : List (Fin D)) (acc : ℕ) :
    ds.foldl (fun a (d : Fin D) ↦ D * a + d.val) acc =
      acc * D ^ ds.length + natOfDigits ds := by
  induction ds generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, pow_zero, mul_one, natOfDigits, add_zero]
  | cons d ds ih =>
    have h0 : natOfDigits (d :: ds) = d.val * D ^ ds.length + natOfDigits ds := by
      simpa only [natOfDigits, List.foldl_cons, mul_zero, zero_add] using ih d.val
    simp only [List.foldl_cons, List.length_cons, ih, h0, pow_succ]
    ring

/-- Base-`D` value of a concatenated digit string `u ++ v`. -/
theorem natOfDigits_append {D : ℕ} (u v : List (Fin D)) :
    natOfDigits (u ++ v) = natOfDigits u * D ^ v.length + natOfDigits v := by
  unfold natOfDigits
  rw [List.foldl_append]
  exact foldl_digitStep_eq v (natOfDigits u)

/-- Every base-`D` digit string `ds` of length `k` decodes to `< D ^ k`. -/
theorem natOfDigits_lt_pow {D : ℕ} (ds : List (Fin D)) :
    natOfDigits ds < D ^ ds.length := by
  induction ds with
  | nil => simp only [natOfDigits, List.foldl_nil, List.length_nil, pow_zero, zero_lt_one]
  | cons d ds ih =>
    have h0 : natOfDigits (d :: ds) = d.val * D ^ ds.length + natOfDigits ds := by
      simpa only [natOfDigits, List.foldl_cons, mul_zero, zero_add] using
        foldl_digitStep_eq ds d.val
    rw [h0, List.length_cons, pow_succ']
    have hd : d.val + 1 ≤ D := d.isLt
    calc d.val * D ^ ds.length + natOfDigits ds
        < d.val * D ^ ds.length + D ^ ds.length := Nat.add_lt_add_left ih _
      _ = (d.val + 1) * D ^ ds.length := by ring
      _ ≤ D * D ^ ds.length := Nat.mul_le_mul_right _ hd

/-- Encoding `q < D ^ k` in `k` base-`D` digits and decoding recovers `q`. -/
theorem natOfDigits_digitsOfNat {D : ℕ} [NeZero D] {k q : ℕ} (hq : q < D ^ k) :
    natOfDigits (digitsOfNat D k q) = q := by
  induction k generalizing q with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hq
    subst hq; rfl
  | succ k ih =>
    have hD : 0 < D := NeZero.pos D
    have hq_div : q / D < D ^ k := by
      rw [Nat.div_lt_iff_lt_mul hD, ← pow_succ]; exact hq
    have hsingle : natOfDigits ([⟨q % D, Nat.mod_lt q hD⟩] : List (Fin D)) = q % D := by
      simp only [natOfDigits, List.foldl_cons, List.foldl_nil, mul_zero, zero_add]
    rw [digitsOfNat, natOfDigits_append, ih hq_div, List.length_singleton, pow_one, hsingle]
    have := Nat.div_add_mod q D
    linarith

private def baseIntervalStart {D : ℕ} (L : ℕ) (c : List (Fin D)) : ℕ :=
  natOfDigits c * D ^ (L - c.length)

private theorem baseIntervalStart_bounds_of_prefix {D : ℕ} [NeZero D] {L : ℕ}
    {c₁ c₂ : List (Fin D)} (hpref : c₁ <+: c₂) (hc₂ : c₂.length ≤ L) :
    baseIntervalStart L c₁ ≤ baseIntervalStart L c₂ ∧
      baseIntervalStart L c₂ < baseIntervalStart L c₁ + D ^ (L - c₁.length) := by
  rcases hpref with ⟨t, rfl⟩
  simp only [List.length_append] at hc₂
  have hsub : L - c₁.length = t.length + (L - (c₁.length + t.length)) := by omega
  have hexp : baseIntervalStart L (c₁ ++ t) =
      baseIntervalStart L c₁ + natOfDigits t * D ^ (L - (c₁.length + t.length)) := by
    unfold baseIntervalStart
    rw [natOfDigits_append, List.length_append, hsub, pow_add]
    ring
  have hlt : natOfDigits t * D ^ (L - (c₁.length + t.length)) < D ^ (L - c₁.length) := by
    rw [hsub, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (natOfDigits_lt_pow t) (Nat.pow_pos (NeZero.pos D))
  rw [hexp]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hlt _⟩

private def kraftAssignFin {ι : Type*} (D : ℕ) [NeZero D] (L : ℕ) (ℓ : ι → ℕ) :
    ℕ → List ι → List (ι × List (Fin D))
  | _, [] => []
  | offset, a :: xs =>
    let step := D ^ (L - ℓ a)
    (a, digitsOfNat D (ℓ a) (offset / step)) :: kraftAssignFin D L ℓ (offset + step) xs

private theorem map_fst_kraftAssignFin {ι : Type*} (D : ℕ) [NeZero D] (L : ℕ) (ℓ : ι → ℕ)
    (offset : ℕ) (xs : List ι) :
    (kraftAssignFin D L ℓ offset xs).map Prod.fst = xs := by
  induction xs generalizing offset with
  | nil => rfl
  | cons a xs ih => simp only [kraftAssignFin, List.map_cons, ih]

private theorem length_snd_of_mem_kraftAssignFin {ι : Type*} {D : ℕ} [NeZero D] {L : ℕ}
    {ℓ : ι → ℕ} {offset : ℕ} {xs : List ι} {p : ι × List (Fin D)}
    (hp : p ∈ kraftAssignFin D L ℓ offset xs) :
    p.2.length = ℓ p.1 := by
  induction xs generalizing offset with
  | nil => cases hp
  | cons a xs ih =>
    rcases List.mem_cons.mp hp with rfl | htail
    · simp only [length_digitsOfNat]
    · exact ih htail

private theorem kraftAssignFin_spec {ι : Type*} {D : ℕ} [NeZero D] {L : ℕ} {ℓ : ι → ℕ}
    (xs : List ι) (offset : ℕ)
    (hL : ∀ x ∈ xs, ℓ x ≤ L)
    (hpw : xs.Pairwise (fun x y ↦ ℓ x ≤ ℓ y))
    (hdvd : ∀ x ∈ xs, D ^ (L - ℓ x) ∣ offset)
    (hsum : offset + (xs.map fun x ↦ D ^ (L - ℓ x)).sum ≤ D ^ L) :
    (∀ p ∈ kraftAssignFin D L ℓ offset xs,
      offset ≤ baseIntervalStart L p.2 ∧
        baseIntervalStart L p.2 + D ^ (L - ℓ p.1) ≤
          offset + (xs.map fun x ↦ D ^ (L - ℓ x)).sum) ∧
      ((kraftAssignFin D L ℓ offset xs).map Prod.snd).Pairwise
        (fun c₁ c₂ ↦ ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
  induction xs generalizing offset with
  | nil => exact ⟨fun _ hp ↦ False.elim (List.not_mem_nil hp), List.Pairwise.nil⟩
  | cons a xs ih =>
    simp only [List.pairwise_cons, List.map_cons, List.sum_cons] at hpw hsum
    have haL : ℓ a ≤ L := hL a List.mem_cons_self
    have ha_dvd : D ^ (L - ℓ a) ∣ offset := hdvd a List.mem_cons_self
    have hstep_pos : 0 < D ^ (L - ℓ a) := Nat.pow_pos (NeZero.pos D)
    have hq_lt : offset / D ^ (L - ℓ a) < D ^ ℓ a := by
      rw [Nat.div_lt_iff_lt_mul hstep_pos, mul_comm, ← pow_add, Nat.sub_add_cancel haL]; omega
    have hca_len : (digitsOfNat D (ℓ a) (offset / D ^ (L - ℓ a))).length = ℓ a :=
      length_digitsOfNat _ _ _
    have hca_start :
        baseIntervalStart L (digitsOfNat D (ℓ a) (offset / D ^ (L - ℓ a))) = offset := by
      unfold baseIntervalStart
      rw [hca_len, natOfDigits_digitsOfNat hq_lt, Nat.div_mul_cancel ha_dvd]
    have hL' : ∀ x ∈ xs, ℓ x ≤ L := fun x hx ↦ hL x (List.mem_cons_of_mem a hx)
    have hdvd' : ∀ x ∈ xs, D ^ (L - ℓ x) ∣ offset + D ^ (L - ℓ a) := fun x hx ↦ by
      have hle : ℓ a ≤ ℓ x := hpw.1 x hx
      exact Nat.dvd_add (hdvd x (List.mem_cons_of_mem a hx)) (Nat.pow_dvd_pow D (by omega))
    rcases ih (offset + D ^ (L - ℓ a)) hL' hpw.2 hdvd' (by omega) with ⟨hbds, hpw_tail⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [kraftAssignFin, List.mem_cons, List.map_cons, List.sum_cons] at hp ⊢
      rcases hp with rfl | htail
      · dsimp only; rw [hca_start]; exact ⟨le_rfl, by omega⟩
      · rcases hbds p htail with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
    · simp only [kraftAssignFin, List.map_cons, List.pairwise_cons, List.forall_mem_map]
      refine ⟨fun p hp ↦ ?_, hpw_tail⟩
      have hp_mem_xs : p.1 ∈ xs := by
        have := List.mem_map_of_mem (f := Prod.fst) hp
        rwa [map_fst_kraftAssignFin] at this
      have hp_L : p.2.length ≤ L :=
        (length_snd_of_mem_kraftAssignFin hp).symm ▸ hL' p.1 hp_mem_xs
      rcases hbds p hp with ⟨hp_lo, _⟩
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have hhi := (baseIntervalStart_bounds_of_prefix h hp_L).2
        rw [hca_start, hca_len] at hhi; omega
      · have hlo := (baseIntervalStart_bounds_of_prefix h (hca_len ▸ haL)).1
        rw [hca_start] at hlo; omega

private lemma pairwise_ne_rel_of_pairwise {β : Type*} {R : β → β → Prop}
    (hsym : ∀ {x y}, R x y → R y x) {l : List β} (hpw : l.Pairwise R)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) :
    R l[i] l[j] := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · exact List.pairwise_iff_getElem.mp hpw i j hi hj hij
  · exact absurd rfl hne
  · exact hsym (List.pairwise_iff_getElem.mp hpw j i hj hi hji)

/-- **Integer-Scaled $D$-ary Kraft Converse**. -/
theorem exists_isPrefixFree_of_kraft_nat {α ι : Type*} [Fintype α] [Nonempty α]
    (s : Finset ι) (ℓ : ι → ℕ) (L : ℕ)
    (hL : ∀ a ∈ s, ℓ a ≤ L)
    (hkraft : (∑ a ∈ s, (Fintype.card α) ^ (L - ℓ a)) ≤ (Fintype.card α) ^ L) :
    ∃ code : ι → List α,
      Set.InjOn code (s : Set ι) ∧
      _root_.InformationTheory.IsPrefixFree (code '' (s : Set ι)) ∧
      ∀ a ∈ s, (code a).length = ℓ a := by
  classical
  set D := Fintype.card α
  have : NeZero D := ⟨Nat.ne_of_gt Fintype.card_pos⟩
  let e : Fin D ≃ α := (Fintype.equivFin α).symm
  let sorted := s.toList.mergeSort (fun a b ↦ decide (ℓ a ≤ ℓ b))
  have hperm : sorted.Perm s.toList := List.mergeSort_perm s.toList _
  have hpw_sorted : sorted.Pairwise (fun a b ↦ ℓ a ≤ ℓ b) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b ↦ decide (ℓ a ≤ ℓ b))
        (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
        (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) s.toList
  have hL_sorted : ∀ a ∈ sorted, ℓ a ≤ L := fun a ha ↦
    hL a (Finset.mem_toList.mp (hperm.subset ha))
  have hsum_sorted : 0 + (sorted.map fun x ↦ D ^ (L - ℓ x)).sum ≤ D ^ L := by
    rw [zero_add, (hperm.map _).sum_eq, ← Multiset.sum_coe, ← Multiset.map_coe,
      Finset.coe_toList]
    exact hkraft
  let pairs := kraftAssignFin D L ℓ 0 sorted
  have hspec := (kraftAssignFin_spec sorted 0 hL_sorted hpw_sorted
    (fun _ _ ↦ Nat.dvd_zero _) hsum_sorted).2
  have hfst : pairs.map Prod.fst = sorted := map_fst_kraftAssignFin D L ℓ 0 sorted
  let codeFin : ι → List (Fin D) := fun a ↦
    match pairs.find? (fun p ↦ decide (p.1 = a)) with
    | some p => p.2
    | none => []
  have hcodeFin_idx : ∀ a ∈ s, ∃ idx : ℕ, ∃ hidx : idx < pairs.length,
      pairs[idx] = (a, codeFin a) := by
    intro a ha
    have ha_sorted : a ∈ sorted := hperm.symm.subset (Finset.mem_toList.mpr ha)
    rw [← hfst] at ha_sorted
    rcases List.mem_map.mp ha_sorted with ⟨p, hp, rfl⟩
    cases hfind : pairs.find? (fun q ↦ decide (q.1 = p.1)) with
    | none =>
      have hfalse := List.find?_eq_none.mp hfind p hp
      simp only [decide_true] at hfalse
      contradiction
    | some q =>
      have hq_mem : q ∈ pairs := List.mem_of_find?_eq_some hfind
      have hq_eq : q.1 = p.1 := by simpa only [decide_eq_true_eq] using List.find?_some hfind
      rcases List.mem_iff_getElem.mp hq_mem with ⟨idx, hidx, hget⟩
      refine ⟨idx, hidx, ?_⟩
      dsimp only [codeFin]
      rw [hfind, hget, ← hq_eq, Prod.mk.eta]
  have hncFin : ∀ {a b : ι}, a ∈ s → b ∈ s → codeFin a <+: codeFin b → a = b := by
    intro a b ha hb hpref
    by_contra hne
    rcases hcodeFin_idx a ha with ⟨i, hi, hpi⟩
    rcases hcodeFin_idx b hb with ⟨j, hj, hpj⟩
    have hij_ne : i ≠ j := fun heq ↦ by subst heq; rw [hpi] at hpj; exact hne (Prod.mk.inj hpj).1
    have hi_map : i < (pairs.map Prod.snd).length := by simpa only [List.length_map] using hi
    have hj_map : j < (pairs.map Prod.snd).length := by simpa only [List.length_map] using hj
    have hrel := pairwise_ne_rel_of_pairwise (fun h ↦ ⟨h.2, h.1⟩) hspec hi_map hj_map hij_ne
    have hpi2 : (pairs.map Prod.snd)[i]'hi_map = codeFin a := by rw [List.getElem_map, hpi]
    have hpj2 : (pairs.map Prod.snd)[j]'hj_map = codeFin b := by rw [List.getElem_map, hpj]
    rw [hpi2, hpj2] at hrel
    exact hrel.1 hpref
  let code : ι → List α := fun a ↦ (codeFin a).map e
  have hmap_prefix : ∀ {u v : List (Fin D)}, u.map e <+: v.map e ↔ u <+: v := by
    intro u v
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨v.drop u.length, ?_⟩
      have hmap_eq : (u ++ v.drop u.length).map e = v.map e := by
        rw [List.map_append]
        have htake : (v.map e).take u.length = u.map e := by
          rw [← ht, List.take_left' (by simp only [List.length_map])]
        have hdrop : (v.map e).drop u.length = (v.drop u.length).map e := List.map_drop.symm
        rw [← htake, ← hdrop, List.take_append_drop]
      exact List.map_injective_iff.mpr e.injective hmap_eq
    · rintro ⟨t, rfl⟩; exact ⟨t.map e, List.map_append.symm⟩
  refine ⟨code, ?_, ?_, ?_⟩
  · intro a ha b hb heq
    exact hncFin ha hb ((List.map_injective_iff.mpr e.injective heq) ▸ List.prefix_refl _)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hpref
    rw [hmap_prefix] at hpref
    exact congrArg code (hncFin ha hb hpref)
  · intro a ha
    rcases hcodeFin_idx a ha with ⟨i, hi, hpi⟩
    simp only [code, List.length_map]
    exact length_snd_of_mem_kraftAssignFin (hpi ▸ List.getElem_mem hi)

/-- **$D$-ary Kraft Theorem**. -/
theorem exists_isPrefixFree_iff_kraft_le_one_of_two_le_card {α ι : Type*} [Fintype α]
    (hD : 2 ≤ Fintype.card α) (s : Finset ι) (ℓ : ι → ℕ) :
    (∃ code : ι → List α,
      Set.InjOn code (s : Set ι) ∧
      _root_.InformationTheory.IsPrefixFree (code '' (s : Set ι)) ∧
      ∀ a ∈ s, (code a).length = ℓ a) ↔
      (∑ a ∈ s, (1 / (Fintype.card α : ℝ)) ^ ℓ a) ≤ 1 := by
  classical
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  constructor
  · rintro ⟨code, hinj, hpf, hlen⟩
    have hS : _root_.InformationTheory.IsPrefixFree
        ((s.image code : Finset (List α)) : Set (List α)) := by
      simpa only [Finset.coe_image] using hpf
    have hkraft := hS.finsetSum_one_div_card_pow_length_le_one
    rw [Finset.sum_image hinj] at hkraft
    exact (Finset.sum_congr rfl fun a ha ↦ by rw [hlen a ha]).symm.trans_le hkraft
  · intro hkraft
    let L : ℕ := s.sup ℓ
    have hL : ∀ a ∈ s, ℓ a ≤ L := fun _ ha ↦ Finset.le_sup ha
    refine exists_isPrefixFree_of_kraft_nat s ℓ L hL ?_
    have hD_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
    have hcast : ((∑ a ∈ s, (Fintype.card α) ^ (L - ℓ a) : ℕ) : ℝ) =
        (Fintype.card α : ℝ) ^ L * ∑ a ∈ s, (1 / (Fintype.card α : ℝ)) ^ ℓ a := by
      push_cast; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [one_div, inv_pow]
      exact pow_sub₀ _ hD_ne (hL a ha)
    have hle_real : ((∑ a ∈ s, (Fintype.card α) ^ (L - ℓ a) : ℕ) : ℝ) ≤
        ((Fintype.card α ^ L : ℕ) : ℝ) := by
      rw [hcast]; push_cast
      exact mul_le_of_le_one_right (by positivity) hkraft
    exact_mod_cast hle_real

/-- **$D$-ary Compact Kraft Theorem**. -/
theorem exists_isCompactPrefixFree_iff_kraft_eq_one_of_two_le_card {α ι : Type*} [Fintype α]
    (hD : 2 ≤ Fintype.card α) (s : Finset ι) (ℓ : ι → ℕ) :
    (∃ code : ι → List α,
      Set.InjOn code (s : Set ι) ∧
      IsCompactPrefixFree (code '' (s : Set ι)) ∧
      ∀ a ∈ s, (code a).length = ℓ a) ↔
      (∑ a ∈ s, (1 / (Fintype.card α : ℝ)) ^ ℓ a) = 1 := by
  classical
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  constructor
  · rintro ⟨code, hinj, hcomp, hlen⟩
    have himg_eq : ((s.image code : Finset (List α)) : Set (List α)) = code '' (s : Set ι) :=
      Finset.coe_image
    have hcomp' : IsCompactPrefixFree ((s.image code : Finset (List α)) : Set (List α)) :=
      himg_eq.symm ▸ hcomp
    have hkraft := (isCompactPrefixFree_iff_kraft_eq_one.mp hcomp').2
    rw [Finset.sum_image hinj] at hkraft
    exact (Finset.sum_congr rfl fun a ha ↦ by rw [hlen a ha]).trans hkraft
  · intro hkraft
    rcases (exists_isPrefixFree_iff_kraft_le_one_of_two_le_card (α := α) hD s ℓ).mpr hkraft.le with
      ⟨code, hinj, hpf, hlen⟩
    refine ⟨code, hinj, ?_, hlen⟩
    have himg_eq : ((s.image code : Finset (List α)) : Set (List α)) = code '' (s : Set ι) :=
      Finset.coe_image
    rw [← himg_eq, isCompactPrefixFree_iff_kraft_eq_one]
    refine ⟨himg_eq.symm ▸ hpf, ?_⟩
    rw [Finset.sum_image hinj]
    exact (Finset.sum_congr rfl fun a ha ↦ by rw [hlen a ha]).trans hkraft

end CslibFrontier.InformationTheory
