/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Sort
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Foundations.Data.List.SelectDistinct
public import Mathlib.Data.Finset.Sort
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Enumeration Problems and Parsimonious Reductions

An *enumeration problem* `P : α → Finset σ` assigns to every instance `a : α` a finite set of
solutions `P a`. A *parsimonious reduction* between enumeration problems `P₁` and `P₂` consists of
a polynomial-time instance transformation `f : α → β` and a polynomial-time solution-recovery map
`g : α × τ → σ` such that for every instance `a : α`, `y ↦ g (a, y)` maps `P₂ (f a)` bijectively
onto `P₁ a`.

This module develops the preorder and equivalence theory of parsimonious enumeration reductions on
multi-tape Turing machines, connects them to counting parsimonious reductions, and provides
canonical sorted-list encodings `encFinsetNat` and `encFinsetPairNat` for finite-set solution spaces
with polynomial-time sorting and deduplication certificates. All results are proved unconditionally
under standard Lean axioms.

## Main definitions

- `CslibFrontier.Complexity.EnumerationProblem`: an enumeration problem `α → Finset σ` assigning a
  finite
  solution set to each instance.
- `CslibFrontier.Complexity.EnumParsimoniousReducible`: parsimonious polynomial-time reducibility
  between
  enumeration problems via `(f, g)` with `Set.BijOn (fun y ↦ g (a, y)) (P₂ (f a)) (P₁ a)`.
- `CslibFrontier.Complexity.EnumParsimoniousEquiv`: mutual parsimonious reducibility between
  enumeration
  problems.
- `CslibFrontier.Complexity.encFinsetNat`, `CslibFrontier.Complexity.lexNatPair`,
  `CslibFrontier.Complexity.encFinsetPairNat`: canonical sorted-list binary encodings for `Finset
  ℕ` and
  `Finset (ℕ × ℕ)`.

## Main results

- `CslibFrontier.Complexity.EnumParsimoniousReducible.refl`,
  `CslibFrontier.Complexity.EnumParsimoniousReducible.trans`: parsimonious enumeration reducibility
  is a
  preorder.
- `CslibFrontier.Complexity.EnumParsimoniousEquiv.refl`,
  `CslibFrontier.Complexity.EnumParsimoniousEquiv.symm`,
  `CslibFrontier.Complexity.EnumParsimoniousEquiv.trans`: parsimonious equivalence is an equivalence
  relation.
- `CslibFrontier.Complexity.EnumParsimoniousReducible.exists_card_eq`,
  `CslibFrontier.Complexity.EnumParsimoniousReducible.parsimoniousReducible_card`: parsimonious
  enumeration reductions preserve solution counts and induce counting `ParsimoniousReducible`
  reductions.
- `CslibFrontier.Complexity.computableInPolyTime_finsetNat_sort`,
  `CslibFrontier.Complexity.computableInPolyTime_toFinsetNat`,
  `CslibFrontier.Complexity.computableInPolyTime_finsetPairNat_sort`,
  `CslibFrontier.Complexity.computableInPolyTime_toFinsetPairNat`: polynomial-time encoding and
  decoding
  between lists and canonically encoded `Finset`s.

## Tags

enumeration complexity, parsimonious reduction, output-polynomial enumeration, finite set encoding
-/

public section

open Cslib.Complexity Turing.MultiTapeTM

namespace CslibFrontier.Complexity

section Reductions

/-- An *enumeration problem* assigns to every input instance `a : α` a finite set of solutions in
`σ`. -/
abbrev EnumerationProblem (α σ : Type*) : Type _ := α → Finset σ

/-- **Parsimonious reduction between enumeration problems.** `P₁` reduces parsimoniously to `P₂`
when there exist polynomial-time computable maps `f : α → β` and `g : α × τ → σ` such that for
every instance `a : α`, `y ↦ g (a, y)` is a bijection from `P₂ (f a)` onto `P₁ a`. -/
@[expose] def EnumParsimoniousReducible {α β σ τ : Type}
    (encA : α ↪ List Bool) (encSA : σ ↪ List Bool)
    (encB : β ↪ List Bool) (encSB : τ ↪ List Bool)
    (P₁ : EnumerationProblem α σ) (P₂ : EnumerationProblem β τ) : Prop :=
  ∃ (f : α → β) (g : α × τ → σ),
    ComputableInPolyTime f encA encB ∧
    ComputableInPolyTime g (encPair encA encSB) encSA ∧
    ∀ a : α, Set.BijOn (fun y ↦ g (a, y)) (P₂ (f a) : Set τ) (P₁ a : Set σ)

/-- **Parsimonious equivalence** between two enumeration problems: mutual parsimonious
reducibility in both directions. -/
@[expose] def EnumParsimoniousEquiv {α β σ τ : Type}
    (encA : α ↪ List Bool) (encSA : σ ↪ List Bool)
    (encB : β ↪ List Bool) (encSB : τ ↪ List Bool)
    (P₁ : EnumerationProblem α σ) (P₂ : EnumerationProblem β τ) : Prop :=
  EnumParsimoniousReducible encA encSA encB encSB P₁ P₂ ∧
  EnumParsimoniousReducible encB encSB encA encSA P₂ P₁

variable {α β γ σ τ ω : Type}
  {encA : α ↪ List Bool} {encSA : σ ↪ List Bool}
  {encB : β ↪ List Bool} {encSB : τ ↪ List Bool}
  {encC : γ ↪ List Bool} {encSC : ω ↪ List Bool}
  {P₁ : EnumerationProblem α σ} {P₂ : EnumerationProblem β τ} {P₃ : EnumerationProblem γ ω}

/-- Every enumeration problem reduces parsimoniously to itself via the identity map and second
projection. -/
@[refl]
theorem EnumParsimoniousReducible.refl (encA : α ↪ List Bool) (encSA : σ ↪ List Bool)
    (P₁ : EnumerationProblem α σ) :
    EnumParsimoniousReducible encA encSA encA encSA P₁ P₁ :=
  ⟨id, Prod.snd, ComputableInPolyTime.id', ComputableInPolyTime.snd encA encSA,
    fun _ ↦ Set.bijOn_id _⟩

/-- **Parsimonious enumeration reductions compose.** -/
@[trans]
theorem EnumParsimoniousReducible.trans
    (h₁₂ : EnumParsimoniousReducible encA encSA encB encSB P₁ P₂)
    (h₂₃ : EnumParsimoniousReducible encB encSB encC encSC P₂ P₃) :
    EnumParsimoniousReducible encA encSA encC encSC P₁ P₃ := by
  obtain ⟨f₁, g₁, hf₁, hg₁, hbij₁⟩ := h₁₂
  obtain ⟨f₂, g₂, hf₂, hg₂, hbij₃⟩ := h₂₃
  refine ⟨f₂ ∘ f₁, fun p ↦ g₁ (p.1, g₂ (f₁ p.1, p.2)), hf₂.comp hf₁, ?_, fun a ↦ ?_⟩
  · have hfst := ComputableInPolyTime.fst encA encSC
    have hsnd := ComputableInPolyTime.snd encA encSC
    exact hg₁.comp (hfst.prod (hg₂.comp ((hf₁.comp hfst).prod hsnd)))
  · exact (hbij₁ a).comp (hbij₃ (f₁ a))

/-- A parsimonious enumeration reduction preserves exact solution cardinalities on every instance.
-/
theorem EnumParsimoniousReducible.exists_card_eq
    (h : EnumParsimoniousReducible encA encSA encB encSB P₁ P₂) :
    ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a : α, (P₁ a).card = (P₂ (f a)).card := by
  obtain ⟨f, g, hf, -, hbij⟩ := h
  refine ⟨f, hf, fun a ↦ ?_⟩
  exact (Finset.card_bij (fun y _ ↦ g (a, y))
    (fun y hy ↦ (hbij a).mapsTo hy)
    (fun y₁ hy₁ y₂ hy₂ heq ↦ (hbij a).injOn hy₁ hy₂ heq)
    (fun x hx ↦ let ⟨y, hy, hyx⟩ := (hbij a).surjOn hx; ⟨y, hy, hyx⟩)).symm

/-- Every parsimonious enumeration reduction induces a counting `ParsimoniousReducible` reduction on
solution cardinalities. -/
theorem EnumParsimoniousReducible.parsimoniousReducible_card
    (h : EnumParsimoniousReducible encA encSA encB encSB P₁ P₂) :
    ParsimoniousReducible encA encB (fun a ↦ (P₁ a).card) (fun b ↦ (P₂ b).card) := by
  obtain ⟨f, hf, hcard⟩ := h.exists_card_eq
  exact ⟨f, hf, hcard⟩

/-- Reflexivity of `EnumParsimoniousEquiv`. -/
@[refl]
theorem EnumParsimoniousEquiv.refl (encA : α ↪ List Bool) (encSA : σ ↪ List Bool)
    (P₁ : EnumerationProblem α σ) :
    EnumParsimoniousEquiv encA encSA encA encSA P₁ P₁ :=
  ⟨.refl encA encSA P₁, .refl encA encSA P₁⟩

/-- Symmetry of `EnumParsimoniousEquiv`. -/
@[symm]
theorem EnumParsimoniousEquiv.symm
    (h : EnumParsimoniousEquiv encA encSA encB encSB P₁ P₂) :
    EnumParsimoniousEquiv encB encSB encA encSA P₂ P₁ :=
  ⟨h.2, h.1⟩

/-- Transitivity of `EnumParsimoniousEquiv`. -/
@[trans]
theorem EnumParsimoniousEquiv.trans
    (h₁₂ : EnumParsimoniousEquiv encA encSA encB encSB P₁ P₂)
    (h₂₃ : EnumParsimoniousEquiv encB encSB encC encSC P₂ P₃) :
    EnumParsimoniousEquiv encA encSA encC encSC P₁ P₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.trans h₁₂.2⟩

end Reductions

section FinsetEncodings

/-- Canonical binary encoding of a finite set `T : Finset ℕ` as the framed list of its elements
sorted in increasing order. -/
def encFinsetNat : Finset ℕ ↪ List Bool where
  toFun T := encList encNat (T.sort (· ≤ ·))
  inj' T₁ T₂ h := by
    have hsort := (encList encNat).injective h
    have h₁ : (T₁.sort (· ≤ ·)).toFinset = T₁ := T₁.sort_toFinset (· ≤ ·)
    have h₂ : (T₂.sort (· ≤ ·)).toFinset = T₂ := T₂.sort_toFinset (· ≤ ·)
    rw [← h₁, ← h₂, hsort]

/-- Evaluating `encFinsetNat` produces the encoded sorted list of `T`. -/
@[simp]
theorem encFinsetNat_apply (T : Finset ℕ) :
    encFinsetNat T = encList encNat (T.sort (· ≤ ·)) := by
  exact rfl.trans rfl

private lemma eq_of_pairwise_perm {α : Type*} (r : α → α → Prop) [Std.Antisymm r]
    {l₁ l₂ : List α} (h₁ : l₁.Pairwise r) (h₂ : l₂.Pairwise r) (hp : l₁.Perm l₂) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact hp.nil_eq
  | cons a t₁ ih =>
    rcases l₂ with _ | ⟨b, t₂⟩
    · exact absurd hp.symm.nil_eq.symm (List.cons_ne_nil a t₁)
    · rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        by_cases h : a = b
        · exact h
        · have hb_in : b ∈ a :: t₁ := hp.symm.subset List.mem_cons_self
          have ha_in : a ∈ b :: t₂ := hp.subset List.mem_cons_self
          have hab₁ : r a b := h₁.1 b (List.mem_of_ne_of_mem (Ne.symm h) hb_in)
          have hba₁ : r b a := h₂.1 a (List.mem_of_ne_of_mem h ha_in)
          exact Std.Antisymm.antisymm a b hab₁ hba₁
      subst hab
      exact congrArg (a :: ·) (ih h₁.2 h₂.2 (List.Perm.cons_inv hp))

/-- Deduplicating and insertion-sorting a list of naturals computes `l.toFinset.sort (· ≤ ·)`. -/
theorem insertionSort_selectDistinct_eq_sort (l : List ℕ) :
    (selectDistinct l (List.replicate l.length true)).insertionSort (· ≤ ·) =
      l.toFinset.sort (· ≤ ·) := by
  set d := selectDistinct l (List.replicate l.length true)
  have hnd : (d.insertionSort (· ≤ ·)).Nodup :=
    (List.perm_insertionSort (· ≤ ·) d).nodup_iff.mpr (nodup_selectDistinct _ _)
  have hpw₁ : (d.insertionSort (· ≤ ·)).Pairwise (· ≤ ·) :=
    List.pairwise_insertionSort (· ≤ ·) d
  have hpw₂ : (l.toFinset.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    l.toFinset.pairwise_sort (· ≤ ·)
  have hnd₂ : (l.toFinset.sort (· ≤ ·)).Nodup :=
    l.toFinset.sort_nodup (· ≤ ·)
  have hperm : (d.insertionSort (· ≤ ·)).Perm (l.toFinset.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hnd hnd₂]
    intro x
    rw [List.mem_insertionSort, mem_selectDistinct_replicate, Finset.mem_sort, List.mem_toFinset]
  exact eq_of_pairwise_perm (· ≤ ·) hpw₁ hpw₂ hperm

/-- Reading a `Finset ℕ` as its sorted list `T.sort (· ≤ ·)` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_finsetNat_sort :
    ComputableInPolyTime (fun T : Finset ℕ ↦ T.sort (· ≤ ·)) encFinsetNat (encList encNat) :=
  ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl

/-- Converting a polynomial-time computed `List ℕ` into its `Finset ℕ` under `encFinsetNat` is
polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toFinsetNat {γ : Type} {encIn : γ ↪ List Bool}
    {l : γ → List ℕ} (hl : ComputableInPolyTime l encIn (encList encNat)) :
    ComputableInPolyTime (fun x ↦ (l x).toFinset) encIn encFinsetNat := by
  have hrep : ComputableInPolyTime (fun x ↦ List.replicate (l x).length true) encIn encBits :=
    ((ComputableInPolyTime.length_list encNat).comp hl).of_enc_eq fun _ ↦ rfl
  have hd : ComputableInPolyTime
      (fun x ↦ selectDistinct (l x) (List.replicate (l x).length true))
      encIn (encList encNat) :=
    (computableInPolyTime_selectDistinct encNat).comp (hl.prod hrep)
  have hcmp : ComputableInPolyTime
      (fun p : (γ × ℕ) × ℕ ↦ decide (p.1.2 ≤ p.2))
      (encCapturedComparison encIn encNat) encBool :=
    ComputableInPolyTime.binary_le'
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  have hsort : ComputableInPolyTime
      (fun x ↦ (selectDistinct (l x) (List.replicate (l x).length true)).insertionSort (· ≤ ·))
      encIn (encList encNat) :=
    ComputableInPolyTime.insertionSortWithInput (r := fun _ a b ↦ a ≤ b) hd hcmp
  refine hsort.of_enc_eq fun x ↦ ?_
  simp only [encFinsetNat_apply, insertionSort_selectDistinct_eq_sort]

/-- Lexicographic linear order on `ℕ × ℕ` used to sort finite sets of attribute pairs. -/
def lexNatPair (p q : ℕ × ℕ) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

instance instDecidableRelLexNatPair : DecidableRel lexNatPair :=
  fun p q ↦ inferInstanceAs (Decidable (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)))

instance instIsTransLexNatPair : IsTrans (ℕ × ℕ) lexNatPair where
  trans _ _ _ h₁ h₂ := by
    unfold lexNatPair at h₁ h₂ ⊢
    omega

instance instAntisymmLexNatPair : Std.Antisymm lexNatPair where
  antisymm p q h₁ h₂ := by
    unfold lexNatPair at h₁ h₂
    exact Prod.ext (by omega) (by omega)

instance instTotalLexNatPair : Std.Total lexNatPair where
  total p q := by
    unfold lexNatPair
    omega

/-- Canonical binary encoding of a finite set `G : Finset (ℕ × ℕ)` as the framed list of its pairs
sorted in lexicographic order `lexNatPair`. -/
def encFinsetPairNat : Finset (ℕ × ℕ) ↪ List Bool where
  toFun G := encList (encPair encNat encNat) (G.sort lexNatPair)
  inj' G₁ G₂ h := by
    have hsort := (encList (encPair encNat encNat)).injective h
    have h₁ : (G₁.sort lexNatPair).toFinset = G₁ := G₁.sort_toFinset lexNatPair
    have h₂ : (G₂.sort lexNatPair).toFinset = G₂ := G₂.sort_toFinset lexNatPair
    rw [← h₁, ← h₂, hsort]

/-- Evaluating `encFinsetPairNat` produces the encoded `lexNatPair`-sorted list of `G`. -/
@[simp]
theorem encFinsetPairNat_apply (G : Finset (ℕ × ℕ)) :
    encFinsetPairNat G = encList (encPair encNat encNat) (G.sort lexNatPair) := by
  exact rfl.trans rfl

/-- Deduplicating and insertion-sorting a list of `ℕ × ℕ` pairs computes `l.toFinset.sort
lexNatPair`. -/
theorem insertionSort_selectDistinct_eq_sort_pair (l : List (ℕ × ℕ)) :
    (selectDistinct l (List.replicate l.length true)).insertionSort lexNatPair =
      l.toFinset.sort lexNatPair := by
  set d := selectDistinct l (List.replicate l.length true)
  have hnd : (d.insertionSort lexNatPair).Nodup :=
    (List.perm_insertionSort lexNatPair d).nodup_iff.mpr (nodup_selectDistinct _ _)
  have hpw₁ : (d.insertionSort lexNatPair).Pairwise lexNatPair :=
    List.pairwise_insertionSort lexNatPair d
  have hpw₂ : (l.toFinset.sort lexNatPair).Pairwise lexNatPair :=
    l.toFinset.pairwise_sort lexNatPair
  have hnd₂ : (l.toFinset.sort lexNatPair).Nodup :=
    l.toFinset.sort_nodup lexNatPair
  have hperm : (d.insertionSort lexNatPair).Perm (l.toFinset.sort lexNatPair) := by
    rw [List.perm_ext_iff_of_nodup hnd hnd₂]
    intro x
    rw [List.mem_insertionSort, mem_selectDistinct_replicate, Finset.mem_sort, List.mem_toFinset]
  exact eq_of_pairwise_perm lexNatPair hpw₁ hpw₂ hperm

/-- Reading a `Finset (ℕ × ℕ)` as its `lexNatPair`-sorted list is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_finsetPairNat_sort :
    ComputableInPolyTime (fun G : Finset (ℕ × ℕ) ↦ G.sort lexNatPair)
      encFinsetPairNat (encList (encPair encNat encNat)) :=
  ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl

private theorem decide_lexNatPair_eq (p q : ℕ × ℕ) :
    decide (lexNatPair p q) =
      (decide (p.1 < q.1) || (decide (p.1 = q.1) && decide (p.2 ≤ q.2))) := by
  by_cases h : lexNatPair p q
  · rw [decide_eq_true h]
    unfold lexNatPair at h
    rcases h with hlt | ⟨heq, hle⟩
    · simp [hlt]
    · simp [heq, hle]
  · rw [decide_eq_false h]
    unfold lexNatPair at h
    symm
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨fun hlt => h (Or.inl hlt),
      if heq : p.1 = q.1 then Or.inr fun hle => h (Or.inr ⟨heq, hle⟩) else Or.inl heq⟩

/-- Converting a polynomial-time computed `List (ℕ × ℕ)` into its `Finset (ℕ × ℕ)` under
`encFinsetPairNat` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toFinsetPairNat {γ : Type} {encIn : γ ↪ List Bool}
    {l : γ → List (ℕ × ℕ)}
    (hl : ComputableInPolyTime l encIn (encList (encPair encNat encNat))) :
    ComputableInPolyTime (fun x ↦ (l x).toFinset) encIn encFinsetPairNat := by
  have hrep : ComputableInPolyTime (fun x ↦ List.replicate (l x).length true) encIn encBits :=
    ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp hl).of_enc_eq fun _ ↦ rfl
  have hd : ComputableInPolyTime
      (fun x ↦ selectDistinct (l x) (List.replicate (l x).length true))
      encIn (encList (encPair encNat encNat)) :=
    (computableInPolyTime_selectDistinct (encPair encNat encNat)).comp (hl.prod hrep)
  have hp1 : ComputableInPolyTime
      (fun p : (γ × (ℕ × ℕ)) × (ℕ × ℕ) ↦ p.1.2)
      (encCapturedComparison encIn (encPair encNat encNat)) (encPair encNat encNat) :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hp2 : ComputableInPolyTime
      (fun p : (γ × (ℕ × ℕ)) × (ℕ × ℕ) ↦ p.2)
      (encCapturedComparison encIn (encPair encNat encNat)) (encPair encNat encNat) :=
    ComputableInPolyTime.snd _ _
  have h11 := (ComputableInPolyTime.fst _ _).comp hp1
  have h12 := (ComputableInPolyTime.snd _ _).comp hp1
  have h21 := (ComputableInPolyTime.fst _ _).comp hp2
  have h22 := (ComputableInPolyTime.snd _ _).comp hp2
  have hcmp : ComputableInPolyTime
      (fun p : (γ × (ℕ × ℕ)) × (ℕ × ℕ) ↦ decide (lexNatPair p.1.2 p.2))
      (encCapturedComparison encIn (encPair encNat encNat)) encBool := by
    simp only [decide_lexNatPair_eq]
    exact ComputableInPolyTime.bool_or'
      (ComputableInPolyTime.binary_lt' h11 h21)
      (ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.decide_eq' h11 h21)
        (ComputableInPolyTime.binary_le' h12 h22))
  have hsort : ComputableInPolyTime
      (fun x ↦ (selectDistinct (l x) (List.replicate (l x).length true)).insertionSort lexNatPair)
      encIn (encList (encPair encNat encNat)) :=
    ComputableInPolyTime.insertionSortWithInput (r := fun _ a b ↦ lexNatPair a b) hd hcmp
  refine hsort.of_enc_eq fun x ↦ ?_
  simp only [encFinsetPairNat_apply, insertionSort_selectDistinct_eq_sort_pair]

end FinsetEncodings

end CslibFrontier.Complexity
