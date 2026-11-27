/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
import Mathlib.Order.Setoid.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Tauto

/-!
# Multi-Agent Epistemic Kripke Structures and Bisimulations

This module defines multi-agent S5 epistemic Kripke structures (`EpistemicKripke`), induced
submodel restrictions, `Q`-restricted and full bisimulations (`IsQBisimulation`, `Bisimilar`),
`n`-bisimulations (`IsQNBisimulation`, `NBisimilar`), and multi-agent epistemic logic syntax and
semantics (`EpistemicFormula`, `EpistemicKripke.SatisfiesEl`), proving invariance of epistemic
truth under bisimilarity and bounded `n`-bisimilarity across arbitrary state universes.
-/

public section

namespace CslibFrontier.Logics.Modal

universe u v w w₁ w₂ w₃

/-- A multi-agent S5 epistemic Kripke structure `M = (S, ~, V)` over agent type `A`, atom type `P`,
and state type `S`, equipping each agent `a : A` with an indistinguishability `Setoid S` and each
atom `p : P` with a valuation `val p : Set S`. -/
structure EpistemicKripke (A : Type u) (P : Type v) (S : Type w) where
  /-- Indistinguishability equivalence relation (`Setoid S`) for each agent `a : A`. -/
  setoid : A → Setoid S
  /-- Propositional valuation `V : P → Set S`. -/
  val : P → Set S

namespace EpistemicKripke

section Basic

variable {A : Type u} {P : Type v} {S : Type w}

/-- Accessibility relation `s ~_a t` for agent `a : A` in `M`. -/
@[expose]
def Rel (M : EpistemicKripke A P S) (a : A) (s t : S) : Prop :=
  (M.setoid a).r s t

/-- Constructor building an `EpistemicKripke` structure from explicit equivalence relations. -/
@[expose]
def ofEquiv (rel : A → S → S → Prop) (hequiv : ∀ a, Equivalence (rel a)) (val : P → Set S) :
    EpistemicKripke A P S where
  setoid a := ⟨rel a, hequiv a⟩
  val := val

@[simp]
lemma ofEquiv_rel (rel : A → S → S → Prop) (hequiv : ∀ a, Equivalence (rel a)) (val : P → Set S)
    (a : A) (s t : S) :
    (ofEquiv rel hequiv val).Rel a s t ↔ rel a s t := by rfl

@[simp]
lemma ofEquiv_val (rel : A → S → S → Prop) (hequiv : ∀ a, Equivalence (rel a)) (val : P → Set S)
    (p : P) :
    (ofEquiv rel hequiv val).val p = val p := by rfl

/-- Extensionality for `EpistemicKripke`. -/
@[ext]
lemma ext {M₁ M₂ : EpistemicKripke A P S}
    (hrel : ∀ a s t, M₁.Rel a s t ↔ M₂.Rel a s t)
    (hval : ∀ p, M₁.val p = M₂.val p) : M₁ = M₂ := by
  cases M₁ with
  | mk setoid₁ val₁ =>
    cases M₂ with
    | mk setoid₂ val₂ =>
      congr
      · funext a
        exact Setoid.ext (hrel a)
      · funext p
        exact hval p

instance instInhabited : Inhabited (EpistemicKripke A P S) :=
  ⟨ofEquiv (fun _ ↦ Eq) (fun _ ↦ ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩)
    (fun _ ↦ ∅)⟩

lemma equiv_rel (M : EpistemicKripke A P S) (a : A) : Equivalence (M.Rel a) :=
  (M.setoid a).iseqv

lemma rel_refl (M : EpistemicKripke A P S) (a : A) (s : S) : M.Rel a s s :=
  (M.setoid a).iseqv.refl s

lemma rel_symm (M : EpistemicKripke A P S) {a : A} {s t : S} (h : M.Rel a s t) : M.Rel a t s :=
  (M.setoid a).iseqv.symm h

lemma rel_trans (M : EpistemicKripke A P S) {a : A} {s t r : S}
    (h₁ : M.Rel a s t) (h₂ : M.Rel a t r) : M.Rel a s r :=
  (M.setoid a).iseqv.trans h₁ h₂

/-- Restrict an epistemic Kripke structure `M` to a subset `T : Set S` of states. -/
@[expose]
def restrict (M : EpistemicKripke A P S) (T : Set S) : EpistemicKripke A P T :=
  ofEquiv (fun a s t ↦ M.Rel a s.1 t.1)
    (fun a ↦ ⟨fun s ↦ M.rel_refl a s.1, fun h ↦ M.rel_symm h, fun h₁ h₂ ↦ M.rel_trans h₁ h₂⟩)
    (fun p ↦ {s : T | s.1 ∈ M.val p})

@[simp]
lemma restrict_rel (M : EpistemicKripke A P S) (T : Set S) (a : A) (s t : T) :
    (M.restrict T).Rel a s t ↔ M.Rel a s.1 t.1 := by rfl

@[simp]
lemma restrict_val (M : EpistemicKripke A P S) (T : Set S) (p : P) (s : T) :
    s ∈ (M.restrict T).val p ↔ s.1 ∈ M.val p := by rfl

/-- Pull back the valuation of an epistemic Kripke structure along an atom map `f : P → Q`. -/
@[expose]
def comapVal {Q : Type*} (M : EpistemicKripke A Q S) (f : P → Q) : EpistemicKripke A P S where
  setoid := M.setoid
  val p := M.val (f p)

@[simp]
lemma comapVal_rel {Q : Type*} (M : EpistemicKripke A Q S) (f : P → Q) (a : A) (s t : S) :
    (M.comapVal f).Rel a s t ↔ M.Rel a s t := by rfl

@[simp]
lemma comapVal_val {Q : Type*} (M : EpistemicKripke A Q S) (f : P → Q) (p : P) :
    (M.comapVal f).val p = M.val (f p) := by rfl

end Basic

section Bisimulation

variable {A : Type u} {P : Type v}

/-- A `Q`-restricted bisimulation between epistemic Kripke structures `M` and `N`. -/
structure IsQBisimulation {S : Type w₁} {S' : Type w₂}
    (Q : Set P) (M : EpistemicKripke A P S) (N : EpistemicKripke A P S')
    (R : S → S' → Prop) : Prop where
  nonempty : ∃ s s', R s s'
  atoms : ∀ ⦃s s'⦄, R s s' → ∀ p ∈ Q, s ∈ M.val p ↔ s' ∈ N.val p
  forth : ∀ ⦃s s'⦄, R s s' → ∀ a t, M.Rel a s t → ∃ t', N.Rel a s' t' ∧ R t t'
  back : ∀ ⦃s s'⦄, R s s' → ∀ a t', N.Rel a s' t' → ∃ t, M.Rel a s t ∧ R t t'

/-- A full bisimulation between `M` and `N`. -/
@[expose]
def IsBisimulation {S : Type w₁} {S' : Type w₂}
    (M : EpistemicKripke A P S) (N : EpistemicKripke A P S') (R : S → S' → Prop) : Prop :=
  IsQBisimulation Set.univ M N R

/-- `Q`-restricted bisimilarity `M_s ↔_Q N_{s'}`. -/
@[expose]
def QBisimilar {S : Type w₁} {S' : Type w₂}
    (Q : Set P) (M : EpistemicKripke A P S) (s : S) (N : EpistemicKripke A P S') (s' : S') : Prop :=
  ∃ R : S → S' → Prop, IsQBisimulation Q M N R ∧ R s s'

/-- Full bisimilarity `M_s ↔ N_{s'}`. -/
@[expose]
def Bisimilar {S : Type w₁} {S' : Type w₂}
    (M : EpistemicKripke A P S) (s : S) (N : EpistemicKripke A P S') (s' : S') : Prop :=
  QBisimilar Set.univ M s N s'

lemma QBisimilar.refl {S : Type w₁} (Q : Set P) (M : EpistemicKripke A P S) (s : S) :
    QBisimilar Q M s M s :=
  ⟨Eq, ⟨⟨s, s, rfl⟩,
    fun _ _ h _ _ ↦ by subst h; rfl,
    fun _ _ h _ t ht ↦ by subst h; exact ⟨t, ht, rfl⟩,
    fun _ _ h _ t' ht' ↦ by subst h; exact ⟨t', ht', rfl⟩⟩, rfl⟩

lemma QBisimilar.symm {S : Type w₁} {S' : Type w₂} {Q : Set P}
    {M : EpistemicKripke A P S} {s : S} {N : EpistemicKripke A P S'} {s' : S'}
    (h : QBisimilar Q M s N s') : QBisimilar Q N s' M s := by
  rcases h with ⟨R, hR, hrs⟩
  exact ⟨fun x y ↦ R y x, ⟨⟨s', s, hrs⟩,
    fun _ _ hxy p hp ↦ (hR.atoms hxy p hp).symm,
    fun _ _ hxy a t ht ↦ hR.back hxy a t ht,
    fun _ _ hxy a t' ht' ↦ hR.forth hxy a t' ht'⟩, hrs⟩

lemma QBisimilar.trans {S₁ : Type w₁} {S₂ : Type w₂} {S₃ : Type w₃} {Q : Set P}
    {M₁ : EpistemicKripke A P S₁} {s₁ : S₁}
    {M₂ : EpistemicKripke A P S₂} {s₂ : S₂}
    {M₃ : EpistemicKripke A P S₃} {s₃ : S₃}
    (h₁₂ : QBisimilar Q M₁ s₁ M₂ s₂) (h₂₃ : QBisimilar Q M₂ s₂ M₃ s₃) :
    QBisimilar Q M₁ s₁ M₃ s₃ := by
  rcases h₁₂ with ⟨R₁, hR₁, hr₁⟩
  rcases h₂₃ with ⟨R₂, hR₂, hr₂⟩
  refine ⟨fun x z ↦ ∃ y, R₁ x y ∧ R₂ y z, ⟨⟨s₁, s₃, s₂, hr₁, hr₂⟩, ?_, ?_, ?_⟩, s₂, hr₁, hr₂⟩
  · rintro x z ⟨y, hxy, hyz⟩ p hp
    exact (hR₁.atoms hxy p hp).trans (hR₂.atoms hyz p hp)
  · rintro x z ⟨y, hxy, hyz⟩ a x' hx'
    rcases hR₁.forth hxy a x' hx' with ⟨y', hy', hx'y'⟩
    rcases hR₂.forth hyz a y' hy' with ⟨z', hz', hy'z'⟩
    exact ⟨z', hz', y', hx'y', hy'z'⟩
  · rintro x z ⟨y, hxy, hyz⟩ a z' hz'
    rcases hR₂.back hyz a z' hz' with ⟨y', hy', hy'z'⟩
    rcases hR₁.back hxy a y' hy' with ⟨x', hx', hx'y'⟩
    exact ⟨x', hx', y', hx'y', hy'z'⟩

/-- Indexed `Q`-restricted `n`-bisimulation system `R_0, ..., R_n`. -/
@[expose, simp]
def IsQNBisimulation {S : Type w₁} {S' : Type w₂}
    (Q : Set P) (M : EpistemicKripke A P S) (N : EpistemicKripke A P S')
    (R : ℕ → S → S' → Prop) : ℕ → S → S' → Prop
  | 0, s, s' => R 0 s s' ∧ ∀ p ∈ Q, s ∈ M.val p ↔ s' ∈ N.val p
  | n + 1, s, s' =>
      R (n + 1) s s' ∧
      (∀ p ∈ Q, s ∈ M.val p ↔ s' ∈ N.val p) ∧
      (∀ a t, M.Rel a s t → ∃ t', N.Rel a s' t' ∧ IsQNBisimulation Q M N R n t t') ∧
      (∀ a t', N.Rel a s' t' → ∃ t, M.Rel a s t ∧ IsQNBisimulation Q M N R n t t')

/-- `Q`-restricted `n`-bisimilarity `M_s ↔_Q^n N_{s'}`. -/
@[expose]
def QNBisimilar {S : Type w₁} {S' : Type w₂}
    (Q : Set P) (n : ℕ) (M : EpistemicKripke A P S) (s : S)
    (N : EpistemicKripke A P S') (s' : S') : Prop :=
  ∃ R : ℕ → S → S' → Prop, IsQNBisimulation Q M N R n s s'

/-- Full `n`-bisimilarity `M_s ↔^n N_{s'}`. -/
@[expose]
def NBisimilar {S : Type w₁} {S' : Type w₂}
    (n : ℕ) (M : EpistemicKripke A P S) (s : S) (N : EpistemicKripke A P S') (s' : S') : Prop :=
  QNBisimilar Set.univ n M s N s'

end Bisimulation

end EpistemicKripke

/-- Multi-agent epistemic logic formulas (`L_EL`) over agent type `A` and atom type `P`. -/
inductive EpistemicFormula (A : Type u) (P : Type v) : Type (max u v)
  | atom (p : P)
  | neg (φ : EpistemicFormula A P)
  | and (φ ψ : EpistemicFormula A P)
  | know (a : A) (φ : EpistemicFormula A P)
  deriving DecidableEq

namespace EpistemicFormula

variable {A : Type u} {P : Type v}

/-- Set of propositional variables occurring in an epistemic formula. -/
@[expose, simp]
def varSet : EpistemicFormula A P → Set P
  | .atom p => {p}
  | .neg φ => φ.varSet
  | .and φ ψ => φ.varSet ∪ ψ.varSet
  | .know _ φ => φ.varSet

/-- Modal depth `d(φ)` of an epistemic formula. -/
@[expose, simp]
def modalDepth : EpistemicFormula A P → ℕ
  | .atom _ => 0
  | .neg φ => φ.modalDepth
  | .and φ ψ => max φ.modalDepth ψ.modalDepth
  | .know _ φ => φ.modalDepth + 1

end EpistemicFormula

namespace EpistemicKripke

section EpistemicSemantics

variable {A : Type u} {P : Type v} {S : Type w}

/-- Truth evaluation `M_s ⊨ φ` of a multi-agent epistemic formula `φ` at world `s` of `M`. -/
@[expose, simp]
def SatisfiesEl (M : EpistemicKripke A P S) (s : S) : EpistemicFormula A P → Prop
  | .atom p => s ∈ M.val p
  | .neg φ => ¬ M.SatisfiesEl s φ
  | .and φ ψ => M.SatisfiesEl s φ ∧ M.SatisfiesEl s ψ
  | .know a φ => ∀ t, M.Rel a s t → M.SatisfiesEl t φ

/-- `Q`-restricted bisimilarity preserves truth of all epistemic formulas whose occurring atoms
lie in `Q`. -/
theorem QBisimilar.satisfiesEl_iff {S' : Type w₂} {Q : Set P}
    {M : EpistemicKripke A P S} {s : S} {N : EpistemicKripke A P S'} {s' : S'}
    (h : QBisimilar Q M s N s') {φ : EpistemicFormula A P} (hQ : φ.varSet ⊆ Q) :
    M.SatisfiesEl s φ ↔ N.SatisfiesEl s' φ := by
  induction φ generalizing s s' with
  | atom p =>
    rcases h with ⟨R, hR, hrs⟩
    exact hR.atoms hrs p (hQ (Set.mem_singleton p))
  | neg _ ih =>
    simp only [SatisfiesEl]
    exact not_congr (ih h hQ)
  | and _ _ ih₁ ih₂ =>
    simp only [EpistemicFormula.varSet, Set.union_subset_iff] at hQ
    simp only [SatisfiesEl]
    exact and_congr (ih₁ h hQ.1) (ih₂ h hQ.2)
  | know a _ ih =>
    rcases h with ⟨R, hR, hrs⟩
    simp only [SatisfiesEl]
    refine ⟨fun hM t' ht' ↦ ?_, fun hN t ht ↦ ?_⟩
    · rcases hR.back hrs a t' ht' with ⟨t, ht, htt'⟩
      exact (ih ⟨R, hR, htt'⟩ hQ).mp (hM t ht)
    · rcases hR.forth hrs a t ht with ⟨t', ht', htt'⟩
      exact (ih ⟨R, hR, htt'⟩ hQ).mpr (hN t' ht')

/-- `Q`-restricted `n`-bisimilarity preserves truth of epistemic formulas of modal depth `≤ n`. -/
theorem QNBisimilar.satisfiesEl_iff {S' : Type w₂} {Q : Set P} {n : ℕ}
    {M : EpistemicKripke A P S} {s : S} {N : EpistemicKripke A P S'} {s' : S'}
    (h : QNBisimilar Q n M s N s') {φ : EpistemicFormula A P}
    (hQ : φ.varSet ⊆ Q) (hd : φ.modalDepth ≤ n) :
    M.SatisfiesEl s φ ↔ N.SatisfiesEl s' φ := by
  induction φ generalizing n s s' with
  | atom p =>
    rcases h with ⟨R, hR⟩
    cases n with
    | zero => exact hR.2 p (hQ (Set.mem_singleton p))
    | succ _ => exact hR.2.1 p (hQ (Set.mem_singleton p))
  | neg _ ih =>
    simp only [SatisfiesEl]
    exact not_congr (ih h hQ hd)
  | and _ _ ih₁ ih₂ =>
    simp only [EpistemicFormula.varSet, Set.union_subset_iff] at hQ
    simp only [EpistemicFormula.modalDepth, max_le_iff] at hd
    simp only [SatisfiesEl]
    exact and_congr (ih₁ h hQ.1 hd.1) (ih₂ h hQ.2 hd.2)
  | know a _ ih =>
    cases n with
    | zero => simp at hd
    | succ n =>
      rcases h with ⟨R, hR⟩
      have hd' : _ ≤ n := Nat.le_of_succ_le_succ hd
      simp only [SatisfiesEl]
      refine ⟨fun hM t' ht' ↦ ?_, fun hN t ht ↦ ?_⟩
      · rcases hR.2.2.2 a t' ht' with ⟨t, ht, hrec⟩
        exact (ih ⟨R, hrec⟩ hQ hd').mp (hM t ht)
      · rcases hR.2.2.1 a t ht with ⟨t', ht', hrec⟩
        exact (ih ⟨R, hrec⟩ hQ hd').mpr (hN t' ht')

end EpistemicSemantics

end EpistemicKripke

end CslibFrontier.Logics.Modal
