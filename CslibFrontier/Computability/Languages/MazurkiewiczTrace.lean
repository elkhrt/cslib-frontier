/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Computability.Language
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

/-!
# Mazurkiewicz Traces over Concurrent Alphabets

This module develops the foundational theory of Mazurkiewicz traces over a concurrent alphabet
`(Σ, I)` under standard Lean axioms, including the Cori–Perrin projection characterization,
cancellation laws in the trace monoid, and DAG-prefixes with their `(n + 1) ^ ω` and `ω n ^ ω`
antichain and trace-cut cardinality bounds.

## Main definitions

- `Cslib.Language.ConcurrentAlphabet`: a type `Σ` equipped with a
  symmetric, irreflexive independence relation `indep` and its complement `dep`.
- `Cslib.Language.ConcurrentAlphabet.width`: maximum size of a pairwise
  independent subset of `Σ`.
- `Cslib.Language.TraceEquiv`,
  `Cslib.Language.Trace`: Mazurkiewicz trace equivalence and the free
  partially commutative trace monoid.
- `Cslib.Language.DAGPrefix`: the trace-prefix relation `∃ r, u' ++ r ~ u`.

## Main results

- `Cslib.Language.traceEquiv_iff_count_and_depProj`: the Cori–Perrin
  projection theorem characterizing trace equivalence via letter counts and dependent projections.
- `Cslib.Language.TraceEquiv.cancel_left`,
  `Cslib.Language.TraceEquiv.cancel_right`: left and right cancellation.
- `Cslib.Language.card_dagPrefixTraces_le`,
  `Cslib.Language.card_traceMul_ge`: the `(n + 1) ^ ω` bound on
  DAG-prefixes and the `|S₁| * |S₂| ≤ ω * n ^ ω * |S₁ · S₂|` trace-cut cardinality bound.
-/

public section

namespace Cslib.Language

universe u v

/-- A concurrent alphabet: an alphabet `Σ` with a symmetric, irreflexive independence relation. -/
@[ext]
structure ConcurrentAlphabet (Γ : Type u) where
  /-- The independence relation on `Σ`, stored as a subset of `Σ × Σ`. -/
  indepRel : Set (Γ × Γ)
  /-- Independence is symmetric. -/
  symmRel : ∀ {a b : Γ}, (a, b) ∈ indepRel → (b, a) ∈ indepRel
  /-- Independence is irreflexive. -/
  irreflRel : ∀ a : Γ, (a, a) ∉ indepRel

namespace ConcurrentAlphabet

variable {Γ : Type u} (C : ConcurrentAlphabet Γ)

/-- The independence relation `a I b`. -/
def indep (a b : Γ) : Prop := (a, b) ∈ C.indepRel

/-- Construct a `ConcurrentAlphabet` from a symmetric, irreflexive binary relation. -/
def ofRel (r : Γ → Γ → Prop) (hsymm : ∀ {a b : Γ}, r a b → r b a) (hirrefl : ∀ a : Γ, ¬r a a) :
    ConcurrentAlphabet Γ where
  indepRel := {p | r p.1 p.2}
  symmRel := fun h => hsymm h
  irreflRel := hirrefl

@[simp]
theorem indep_ofRel {r : Γ → Γ → Prop} (hsymm : ∀ {a b : Γ}, r a b → r b a)
    (hirrefl : ∀ a : Γ, ¬r a a) (a b : Γ) : (ofRel r hsymm hirrefl).indep a b ↔ r a b :=
  Iff.rfl

theorem symm {a b : Γ} (h : C.indep a b) : C.indep b a := C.symmRel h

theorem irrefl (a : Γ) : ¬C.indep a a := C.irreflRel a

/-- The dependence relation on `Σ`, complementary to `indep`. -/
def dep (a b : Γ) : Prop := ¬C.indep a b

theorem dep_iff_not_indep (a b : Γ) : C.dep a b ↔ ¬C.indep a b := Iff.rfl

theorem dep_refl (a : Γ) : C.dep a a := C.irrefl a

theorem dep_symm {a b : Γ} (h : C.dep a b) : C.dep b a := fun hab => h (C.symm hab)

theorem indep_ne {a b : Γ} (h : C.indep a b) : a ≠ b := by
  rintro rfl
  exact C.irrefl a h

theorem dep_of_eq {a b : Γ} (h : a = b) : C.dep a b := h ▸ C.dep_refl a

instance instDecidableRelDep [DecidableRel C.indep] : DecidableRel C.dep :=
  fun a b => inferInstanceAs (Decidable (¬C.indep a b))

/-- A finite subset `S` of `Σ` is pairwise independent if all distinct pairs in `S` lie in
`indep`. -/
def IsIndepSet (S : Finset Γ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → C.indep a b

theorem isIndepSet_empty : C.IsIndepSet ∅ := by
  intro a ha
  exact absurd ha (Finset.notMem_empty a)

theorem isIndepSet_singleton (a : Γ) : C.IsIndepSet {a} := by
  intro x hx y hy hne
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hne

theorem isIndepSet_subset {S T : Finset Γ} (hT : C.IsIndepSet T) (hST : S ⊆ T) :
    C.IsIndepSet S :=
  fun a ha b hb hne => hT a (hST ha) b (hST hb) hne

/-- The width of a finite concurrent alphabet: the largest cardinality of a pairwise independent
subset of `Σ`. -/
noncomputable def width [Fintype Γ] : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset Γ)).filter (fun S => C.IsIndepSet S)).sup Finset.card

theorem card_le_width [Fintype Γ] {S : Finset Γ} (hS : C.IsIndepSet S) :
    S.card ≤ C.width := by
  classical
  unfold width
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)

theorem width_pos [Fintype Γ] [Nonempty Γ] : 1 ≤ C.width := by
  obtain ⟨a⟩ := ‹Nonempty Γ›
  simpa using C.card_le_width (C.isIndepSet_singleton a)

theorem width_le_card [Fintype Γ] : C.width ≤ Fintype.card Γ := by
  classical
  unfold width
  exact Finset.sup_le fun S _ => S.card_le_univ

theorem exists_isIndepSet_card_eq_width [Fintype Γ] :
    ∃ S : Finset Γ, C.IsIndepSet S ∧ S.card = C.width := by
  classical
  have hne : ((Finset.univ : Finset (Finset Γ)).filter (fun S => C.IsIndepSet S)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.isIndepSet_empty⟩⟩
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image _ Finset.card hne
  refine ⟨S, (Finset.mem_filter.mp hSmem).2, ?_⟩
  refine le_antisymm (C.card_le_width (Finset.mem_filter.mp hSmem).2) ?_
  unfold width
  exact Finset.sup_le fun T hT => hSmax T hT

end ConcurrentAlphabet

/-! ### Trace equivalence and the trace monoid -/

/-- One-step commutation of adjacent independent letters. -/
inductive TraceStep {Γ : Type u} (C : ConcurrentAlphabet Γ) : List Γ → List Γ → Prop
  | swap (u v : List Γ) {a b : Γ} (h : C.indep a b) :
      TraceStep C (u ++ a :: b :: v) (u ++ b :: a :: v)

/-- Mazurkiewicz trace equivalence: the reflexive-transitive closure of adjacent independent
commutations. -/
def TraceEquiv {Γ : Type u} (C : ConcurrentAlphabet Γ) : List Γ → List Γ → Prop :=
  Relation.ReflTransGen (TraceStep C)

namespace TraceStep

variable {Γ : Type u} {C : ConcurrentAlphabet Γ}

theorem symm {u v : List Γ} (h : TraceStep C u v) : TraceStep C v u := by
  cases h with
  | swap p q hab => exact TraceStep.swap p q (C.symm hab)

theorem append_left (p : List Γ) {u v : List Γ} (h : TraceStep C u v) :
    TraceStep C (p ++ u) (p ++ v) := by
  cases h with
  | swap x y hab =>
    simpa only [List.append_assoc] using TraceStep.swap (p ++ x) y hab

theorem append_right {u v : List Γ} (q : List Γ) (h : TraceStep C u v) :
    TraceStep C (u ++ q) (v ++ q) := by
  cases h with
  | swap x y hab =>
    simpa only [List.append_assoc, List.cons_append] using TraceStep.swap x (y ++ q) hab

theorem perm {u v : List Γ} (h : TraceStep C u v) : u.Perm v := by
  cases h with
  | swap p q _ =>
    exact List.Perm.append_left p ((List.Perm.swap _ _ q).symm)

end TraceStep

namespace TraceEquiv

variable {Γ : Type u} {C : ConcurrentAlphabet Γ}

theorem refl (w : List Γ) : TraceEquiv C w w := Relation.ReflTransGen.refl

theorem single {u v : List Γ} (h : TraceStep C u v) : TraceEquiv C u v :=
  Relation.ReflTransGen.single h

theorem trans {u v w : List Γ} (h₁ : TraceEquiv C u v) (h₂ : TraceEquiv C v w) :
    TraceEquiv C u w :=
  Relation.ReflTransGen.trans h₁ h₂

theorem symm {u v : List Γ} (h : TraceEquiv C u v) : TraceEquiv C v u := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans (single hstep.symm) ih

theorem equivalence (C : ConcurrentAlphabet Γ) : Equivalence (TraceEquiv C) :=
  ⟨refl, symm, trans⟩

theorem append_left (p : List Γ) {u v : List Γ} (h : TraceEquiv C u v) :
    TraceEquiv C (p ++ u) (p ++ v) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans ih (single (hstep.append_left p))

theorem append_right {u v : List Γ} (q : List Γ) (h : TraceEquiv C u v) :
    TraceEquiv C (u ++ q) (v ++ q) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans ih (single (hstep.append_right q))

theorem append {u₁ v₁ u₂ v₂ : List Γ} (h₁ : TraceEquiv C u₁ v₁) (h₂ : TraceEquiv C u₂ v₂) :
    TraceEquiv C (u₁ ++ u₂) (v₁ ++ v₂) :=
  trans (append_right u₂ h₁) (append_left v₁ h₂)

theorem cons (a : Γ) {u v : List Γ} (h : TraceEquiv C u v) :
    TraceEquiv C (a :: u) (a :: v) :=
  append_left [a] h

theorem perm {u v : List Γ} (h : TraceEquiv C u v) : u.Perm v := by
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ hstep ih => exact ih.trans hstep.perm

theorem length_eq {u v : List Γ} (h : TraceEquiv C u v) : u.length = v.length :=
  h.perm.length_eq

theorem count_eq [DecidableEq Γ] {u v : List Γ} (h : TraceEquiv C u v) (a : Γ) :
    u.count a = v.count a :=
  h.perm.count_eq a

theorem mem_iff {u v : List Γ} (h : TraceEquiv C u v) {a : Γ} : a ∈ u ↔ a ∈ v :=
  h.perm.mem_iff

theorem comm_of_forall_indep {a : Γ} {v : List Γ} (h : ∀ x ∈ v, C.indep a x) :
    TraceEquiv C (v ++ [a]) (a :: v) := by
  induction v with
  | nil => exact refl [a]
  | cons b v ih =>
    have hb : C.indep a b := h b (List.mem_cons_self ..)
    have hv : ∀ x ∈ v, C.indep a x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact trans (cons b (ih hv)) (single (by simpa using TraceStep.swap [] v (C.symm hb)))

end TraceEquiv

/-- The `Setoid` on `List Σ` induced by `TraceEquiv C`. -/
@[expose]
def traceSetoid {Γ : Type u} (C : ConcurrentAlphabet Γ) : Setoid (List Γ) where
  r := TraceEquiv C
  iseqv := TraceEquiv.equivalence C

/-- The type of Mazurkiewicz traces over `C`. -/
@[expose]
def Trace {Γ : Type u} (C : ConcurrentAlphabet Γ) : Type u :=
  Quotient (traceSetoid C)

/-- The trace equivalence class of a word. -/
def traceOf {Γ : Type u} (C : ConcurrentAlphabet Γ) (w : List Γ) : Trace C :=
  Quotient.mk (traceSetoid C) w

theorem traceOf_eq_iff {Γ : Type u} {C : ConcurrentAlphabet Γ} {u v : List Γ} :
    traceOf C u = traceOf C v ↔ TraceEquiv C u v :=
  Quotient.eq (r := traceSetoid C)

/-- The length of a trace (well-defined since trace equivalence preserves word length). -/
def Trace.length {Γ : Type u} {C : ConcurrentAlphabet Γ} : Trace C → ℕ :=
  Quotient.lift List.length fun _ _ h => TraceEquiv.length_eq h

@[simp]
theorem Trace.length_traceOf {Γ : Type u} (C : ConcurrentAlphabet Γ) (w : List Γ) :
    (traceOf C w).length = w.length := by
  rfl

/-- Concatenation of Mazurkiewicz traces. -/
def Trace.mul {Γ : Type u} {C : ConcurrentAlphabet Γ} : Trace C → Trace C → Trace C :=
  Quotient.lift₂ (fun u v => traceOf C (u ++ v)) fun _ _ _ _ h₁ h₂ =>
    Quotient.sound (TraceEquiv.append h₁ h₂)

@[simp]
theorem Trace.mul_traceOf {Γ : Type u} (C : ConcurrentAlphabet Γ) (u v : List Γ) :
    (traceOf C u).mul (traceOf C v) = traceOf C (u ++ v) := by
  rfl

instance Trace.instMonoid {Γ : Type u} (C : ConcurrentAlphabet Γ) : Monoid (Trace C) where
  mul := Trace.mul
  one := traceOf C []
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun u v w => ?_
    change traceOf C ((u ++ v) ++ w) = traceOf C (u ++ (v ++ w))
    rw [List.append_assoc]
  one_mul a := by
    refine Quotient.inductionOn a fun u => ?_
    change traceOf C ([] ++ u) = traceOf C u
    rw [List.nil_append]
  mul_one a := by
    refine Quotient.inductionOn a fun u => ?_
    change traceOf C (u ++ []) = traceOf C u
    rw [List.append_nil]

@[simp]
theorem traceOf_nil {Γ : Type u} (C : ConcurrentAlphabet Γ) :
    traceOf C [] = (1 : Trace C) := by
  rfl

@[simp]
theorem traceOf_append {Γ : Type u} (C : ConcurrentAlphabet Γ) (u v : List Γ) :
    traceOf C (u ++ v) = traceOf C u * traceOf C v := by
  rfl

/-- The trace closure `[L]_I` of a language `L`. -/
def traceClosure {Γ : Type u} (C : ConcurrentAlphabet Γ) (L : Language Γ) : Language Γ :=
  {w | ∃ u ∈ L, TraceEquiv C u w}

theorem mem_traceClosure_iff {Γ : Type u} {C : ConcurrentAlphabet Γ} {L : Language Γ}
    {w : List Γ} : w ∈ traceClosure C L ↔ ∃ u ∈ L, TraceEquiv C u w := by
  rfl

/-- The trace quotient `L / ~_I` of a set of words. -/
def traceQuotient {Γ : Type u} (C : ConcurrentAlphabet Γ) (L : Set (List Γ)) : Set (Trace C) :=
  traceOf C '' L

theorem mem_traceQuotient_iff {Γ : Type u} {C : ConcurrentAlphabet Γ} {L : Set (List Γ)}
    {t : Trace C} : t ∈ traceQuotient C L ↔ ∃ w ∈ L, traceOf C w = t :=
  Iff.rfl

/-! ### Cori–Perrin projection characterization and cancellation -/

section CoriPerrin

variable {Γ : Type u} [DecidableEq Γ]

/-- The projection of a word onto the two-letter set `{a, b}`. -/
def depProj (a b : Γ) (w : List Γ) : List Γ :=
  w.filter fun x => decide (x = a ∨ x = b)

theorem depProj_eq_filter (a b : Γ) (w : List Γ) :
    depProj a b w = w.filter fun x => decide (x = a ∨ x = b) := by
  rfl

@[simp]
theorem depProj_nil (a b : Γ) : depProj a b [] = [] := by
  rfl

theorem depProj_append (a b : Γ) (u v : List Γ) :
    depProj a b (u ++ v) = depProj a b u ++ depProj a b v := by
  exact List.filter_append u v

theorem depProj_cons (a b c : Γ) (w : List Γ) :
    depProj a b (c :: w) = if c = a ∨ c = b then c :: depProj a b w else depProj a b w := by
  simp only [depProj, List.filter_cons, decide_eq_true_eq]

theorem depProj_length (a b : Γ) (w : List Γ) :
    (depProj a b w).length = if a = b then w.count a else w.count a + w.count b := by
  induction w with
  | nil => simp [depProj_nil]
  | cons z zs ih =>
    rw [depProj_cons]
    by_cases h : a = b
    · subst h
      simp only [↓reduceIte, List.count_cons, or_self] at ih ⊢
      by_cases hza : z = a
      · subst hza; simp [ih]
      · simp [hza, ih]
    · simp only [h, ↓reduceIte, List.count_cons] at ih ⊢
      by_cases hza : z = a
      · subst hza; simp [h, ih]; omega
      · by_cases hzb : z = b
        · subst hzb; simp [Ne.symm h, ih]; omega
        · simp [hza, hzb, ih]

theorem depProj_count_of_mem {a b c : Γ} (h : c = a ∨ c = b) (w : List Γ) :
    (depProj a b w).count c = w.count c := by
  simp [depProj, List.count_filter, h]

theorem depProj_of_notMem {a b : Γ} {w : List Γ} (ha : a ∉ w) (hb : b ∉ w) :
    depProj a b w = [] := by
  rw [depProj, List.filter_eq_nil_iff]
  intro x hx
  simp only [decide_eq_true_eq, not_or]
  exact ⟨fun h => ha (h ▸ hx), fun h => hb (h ▸ hx)⟩

theorem depProj_eq_of_traceStep {C : ConcurrentAlphabet Γ} {u v : List Γ}
    (h : TraceStep C u v) {a b : Γ} (hab : C.dep a b) :
    depProj a b u = depProj a b v := by
  cases h with
  | @swap p q c d hcd =>
    simp only [depProj_append, depProj_cons]
    have hnot : ¬((c = a ∨ c = b) ∧ (d = a ∨ d = b)) := by
      rintro ⟨h1 | h1, h2 | h2⟩
      · subst h1; subst h2; exact C.irrefl _ hcd
      · exact hab (h1 ▸ h2 ▸ hcd)
      · exact hab (C.symm (h1 ▸ h2 ▸ hcd))
      · subst h1; subst h2; exact C.irrefl _ hcd
    by_cases hc : c = a ∨ c = b <;> by_cases hd : d = a ∨ d = b
    · exact absurd ⟨hc, hd⟩ hnot
    · simp [hc, hd]
    · simp [hc, hd]
    · simp [hc, hd]

theorem depProj_eq_of_traceEquiv {C : ConcurrentAlphabet Γ} {u v : List Γ}
    (h : TraceEquiv C u v) {a b : Γ} (hab : C.dep a b) :
    depProj a b u = depProj a b v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (depProj_eq_of_traceStep hstep hab)

private theorem exists_split_first_mem {α : Type u} {a : α} {w : List α} (ha : a ∈ w) :
    ∃ p q : List α, w = p ++ a :: q ∧ a ∉ p := by
  classical
  induction w with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hxa : x = a
    · subst hxa
      exact ⟨[], xs, rfl, List.not_mem_nil⟩
    · rcases List.mem_cons.mp ha with rfl | hmem
      · exact absurd rfl hxa
      · obtain ⟨p, q, rfl, hp⟩ := ih hmem
        exact ⟨x :: p, q, rfl, by simp [Ne.symm hxa, hp]⟩

/-- **Cori–Perrin projection theorem**: two words are Mazurkiewicz trace-equivalent if and only if
they have the same letter counts and the same projection onto every pair of dependent letters. -/
theorem traceEquiv_iff_count_and_depProj {C : ConcurrentAlphabet Γ} {u v : List Γ} :
    TraceEquiv C u v ↔
      (∀ a : Γ, u.count a = v.count a) ∧
      (∀ a b : Γ, C.dep a b → depProj a b u = depProj a b v) := by
  refine ⟨fun h => ⟨fun a => h.count_eq a, fun _ _ hab => depProj_eq_of_traceEquiv h hab⟩, ?_⟩
  rintro ⟨hcount, hproj⟩
  induction hn : u.length generalizing u v with
  | zero =>
    have hu : u = [] := List.eq_nil_of_length_eq_zero hn
    subst hu
    have hv : v = [] := by
      cases v with
      | nil => rfl
      | cons b bs =>
        have hc := hcount b
        simp at hc
    subst hv
    exact TraceEquiv.refl []
  | succ k ih =>
    cases u with
    | nil => simp at hn
    | cons a u' =>
      have hav : a ∈ v := List.count_pos_iff.mp (by rw [← hcount a]; simp)
      obtain ⟨p, q, rfl, hap⟩ := exists_split_first_mem hav
      have hindep : ∀ b ∈ p, C.indep a b := by
        intro b hb
        by_contra hdep
        have hpr := hproj a b hdep
        have hba : b ≠ a := fun h => hap (h ▸ hb)
        have h1 : (depProj a b (a :: u')).head? = some a := by simp [depProj_cons]
        have h2 : (depProj a b p).head? = some b := by
          obtain ⟨p₁, p₂, hp_eq, hbp₁⟩ := exists_split_first_mem hb
          have hap₁ : a ∉ p₁ := fun h => hap (hp_eq ▸ List.mem_append_left _ h)
          rw [hp_eq, depProj_append, depProj_of_notMem hap₁ hbp₁, List.nil_append, depProj_cons]
          simp
        rw [depProj_append] at hpr
        have hne_p : depProj a b p ≠ [] := by
          intro he
          rw [he] at h2
          simp at h2
        have hpr' := congrArg List.head? hpr
        rw [List.head?_append_of_ne_nil _ hne_p, h1, h2] at hpr'
        exact hba (Option.some.inj hpr').symm
      have hswap : TraceEquiv C (a :: (p ++ q)) (p ++ a :: q) := by
        have hc := (TraceEquiv.comm_of_forall_indep hindep).symm
        simpa [List.append_assoc] using TraceEquiv.append_right q hc
      have hcount' : ∀ c : Γ, u'.count c = (p ++ q).count c := by
        intro c
        have hc := hcount c
        rw [List.count_cons, List.count_append, List.count_cons] at hc
        rw [List.count_append]
        omega
      have hproj' : ∀ c d : Γ, C.dep c d → depProj c d u' = depProj c d (p ++ q) := by
        intro c d hcd
        have hp_eq := (hproj c d hcd).trans (depProj_eq_of_traceEquiv hswap.symm hcd)
        simp only [depProj_cons] at hp_eq
        by_cases ha_cd : a = c ∨ a = d
        · simp only [ha_cd, ↓reduceIte, List.cons.injEq] at hp_eq
          exact hp_eq.2
        · simp only [ha_cd, ↓reduceIte] at hp_eq
          exact hp_eq
      have hlen' : u'.length = k := by simpa using hn
      exact (TraceEquiv.cons a (ih hcount' hproj' hlen')).trans hswap

/-- Computable decidability of Mazurkiewicz trace equivalence over a finite concurrent alphabet. -/
instance TraceEquiv.instDecidableRel (C : ConcurrentAlphabet Γ) [Fintype Γ]
    [DecidableRel C.indep] : DecidableRel (TraceEquiv C) := fun _ _ =>
  decidable_of_iff _ traceEquiv_iff_count_and_depProj.symm

instance Trace.instDecidableEq (C : ConcurrentAlphabet Γ) [Fintype Γ]
    [DecidableRel C.indep] : DecidableEq (Trace C) :=
  @Quotient.decidableEq _ (traceSetoid C) (TraceEquiv.instDecidableRel C)

end CoriPerrin

/-- Left cancellation in the trace monoid. -/
theorem TraceEquiv.cancel_left {Γ : Type u} {C : ConcurrentAlphabet Γ} {p u v : List Γ}
    (h : TraceEquiv C (p ++ u) (p ++ v)) : TraceEquiv C u v := by
  classical
  rw [traceEquiv_iff_count_and_depProj] at h ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have hc := h.1 a
    simp only [List.count_append] at hc
    omega
  · have hp := h.2 a b hab
    simp only [depProj_append] at hp
    exact List.append_cancel_left hp

/-- Right cancellation in the trace monoid. -/
theorem TraceEquiv.cancel_right {Γ : Type u} {C : ConcurrentAlphabet Γ} {u v s : List Γ}
    (h : TraceEquiv C (u ++ s) (v ++ s)) : TraceEquiv C u v := by
  classical
  rw [traceEquiv_iff_count_and_depProj] at h ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have hc := h.1 a
    simp only [List.count_append] at hc
    omega
  · have hp := h.2 a b hab
    simp only [depProj_append] at hp
    exact List.append_cancel_right hp

theorem Trace.mul_left_cancel {Γ : Type u} {C : ConcurrentAlphabet Γ} {p x y : Trace C}
    (h : p * x = p * y) : x = y := by
  refine Quotient.inductionOn₃ p x y (fun p u v h => ?_) h
  exact Quotient.sound (TraceEquiv.cancel_left (traceOf_eq_iff.mp h))

theorem Trace.mul_right_cancel {Γ : Type u} {C : ConcurrentAlphabet Γ} {x y s : Trace C}
    (h : x * s = y * s) : x = y := by
  refine Quotient.inductionOn₃ x y s (fun u v s h => ?_) h
  exact Quotient.sound (TraceEquiv.cancel_right (traceOf_eq_iff.mp h))

/-! ### DAG-prefixes and trace-cut cardinality bounds -/

/-- `u'` is a DAG-prefix of `u` when `u'` can be extended on the right to a word trace-equivalent
to `u`. Equivalently, `G(⪯^{u'}_I)` is a downward-closed sub-DAG of `G(⪯^u_I)`. -/
def DAGPrefix {Γ : Type u} (C : ConcurrentAlphabet Γ) (u' u : List Γ) : Prop :=
  ∃ r : List Γ, TraceEquiv C (u' ++ r) u

section DAGPrefixBasic

variable {Γ : Type u} {C : ConcurrentAlphabet Γ}

theorem dagPrefix_nil (u : List Γ) : DAGPrefix C [] u :=
  ⟨u, TraceEquiv.refl u⟩

theorem dagPrefix_self (u : List Γ) : DAGPrefix C u u :=
  ⟨[], by simpa using TraceEquiv.refl u⟩

theorem dagPrefix_of_traceEquiv_left {u₁ u₂ u : List Γ} (heq : TraceEquiv C u₁ u₂)
    (h : DAGPrefix C u₁ u) : DAGPrefix C u₂ u := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (TraceEquiv.append_right r heq.symm).trans hr⟩

theorem dagPrefix_of_traceEquiv_right {u' u₁ u₂ : List Γ} (heq : TraceEquiv C u₁ u₂)
    (h : DAGPrefix C u' u₁) : DAGPrefix C u' u₂ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr.trans heq⟩

theorem dagPrefix_prefix {u' v u : List Γ} (h : DAGPrefix C (u' ++ v) u) :
    DAGPrefix C u' u := by
  obtain ⟨r, hr⟩ := h
  exact ⟨v ++ r, by simpa [List.append_assoc] using hr⟩

theorem dagPrefix_length_le {u' u : List Γ} (h : DAGPrefix C u' u) : u'.length ≤ u.length := by
  obtain ⟨r, hr⟩ := h
  have := hr.length_eq
  simp only [List.length_append] at this
  omega

end DAGPrefixBasic

section DAGPrefixAPI

variable {Γ : Type u} [DecidableEq Γ] {C : ConcurrentAlphabet Γ}

private theorem prefix_of_prefix_of_length_le {α : Type u} {l₁ l₂ l : List α}
    (h₁ : l₁ <+: l) (h₂ : l₂ <+: l) (hle : l₁.length ≤ l₂.length) : l₁ <+: l₂ := by
  obtain ⟨s₁, hs₁⟩ := h₁
  obtain ⟨s₂, hs₂⟩ := h₂
  have h1 : l₁ = l.take l₁.length := by
    rw [← hs₁, List.take_left]
  have h2 : l₂ = l.take l₂.length := by
    rw [← hs₂, List.take_left]
  refine ⟨l₂.drop l₁.length, ?_⟩
  have htake : l₂.take l₁.length = l₁ := by
    rw [h2, List.take_take, Nat.min_eq_left hle, ← h1]
  conv_lhs => arg 1; rw [← htake]
  exact List.take_append_drop l₁.length l₂

private theorem eq_of_prefix_of_length_eq {α : Type u} {l₁ l₂ l : List α}
    (h₁ : l₁ <+: l) (h₂ : l₂ <+: l) (heq : l₁.length = l₂.length) : l₁ = l₂ := by
  obtain ⟨s, hs⟩ := prefix_of_prefix_of_length_le h₁ h₂ (le_of_eq heq)
  have hlen : s.length = 0 := by
    have := congrArg List.length hs
    rw [List.length_append] at this
    omega
  rw [List.eq_nil_of_length_eq_zero hlen, List.append_nil] at hs
  exact hs

/-- Projection characterization of `DAGPrefix`: `u'` is a DAG-prefix of `u` iff every letter count
of `u'` is at most that of `u` and every dependent projection of `u'` is a prefix of the
corresponding projection of `u`. -/
theorem dagPrefix_iff_count_and_depProj {u' u : List Γ} :
    DAGPrefix C u' u ↔
      (∀ a : Γ, u'.count a ≤ u.count a) ∧
      (∀ a b : Γ, C.dep a b → depProj a b u' <+: depProj a b u) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hc := hr.count_eq a
      rw [List.count_append] at hc
      omega
    · exact ⟨depProj a b r, by rw [← depProj_append, depProj_eq_of_traceEquiv hr hab]⟩
  · rintro ⟨hcount, hproj⟩
    induction hn : u'.length generalizing u' u with
    | zero =>
      have hu' : u' = [] := List.eq_nil_of_length_eq_zero hn
      subst hu'
      exact dagPrefix_nil u
    | succ k ih =>
      cases u' with
      | nil => simp at hn
      | cons a v' =>
        have hau : a ∈ u := List.count_pos_iff.mp (by
          have := hcount a
          rw [List.count_cons_self] at this
          omega)
        obtain ⟨p, q, rfl, hap⟩ := exists_split_first_mem hau
        have hindep : ∀ b ∈ p, C.indep a b := by
          intro b hb
          by_contra hdep
          obtain ⟨s, hs⟩ := hproj a b hdep
          have hba : b ≠ a := fun h => hap (h ▸ hb)
          have h1 : (depProj a b (a :: v')).head? = some a := by simp [depProj_cons]
          have h2 : (depProj a b p).head? = some b := by
            obtain ⟨p₁, p₂, hp_eq, hbp₁⟩ := exists_split_first_mem hb
            have hap₁ : a ∉ p₁ := fun h => hap (hp_eq ▸ List.mem_append_left _ h)
            rw [hp_eq, depProj_append, depProj_of_notMem hap₁ hbp₁, List.nil_append, depProj_cons]
            simp
          have hne_p : depProj a b p ≠ [] := by
            intro he
            rw [he] at h2
            simp at h2
          have h3 : (depProj a b (p ++ a :: q)).head? = some b := by
            rw [depProj_append, List.head?_append_of_ne_nil _ hne_p, h2]
          have hne_a : depProj a b (a :: v') ≠ [] := by simp [depProj_cons]
          rw [← hs, List.head?_append_of_ne_nil _ hne_a, h1] at h3
          exact hba (Option.some.inj h3).symm
        have hswap : TraceEquiv C (a :: (p ++ q)) (p ++ a :: q) := by
          have hc := (TraceEquiv.comm_of_forall_indep hindep).symm
          simpa [List.append_assoc] using TraceEquiv.append_right q hc
        have hcount' : ∀ c : Γ, v'.count c ≤ (p ++ q).count c := by
          intro c
          have hc := hcount c
          rw [List.count_cons, List.count_append, List.count_cons] at hc
          rw [List.count_append]
          omega
        have hproj' : ∀ c d : Γ, C.dep c d → depProj c d v' <+: depProj c d (p ++ q) := by
          intro c d hcd
          have hp_pref := hproj c d hcd
          rw [depProj_eq_of_traceEquiv hswap.symm hcd] at hp_pref
          simp only [depProj_cons] at hp_pref
          by_cases ha_cd : a = c ∨ a = d
          · simp only [ha_cd, ↓reduceIte, List.cons_prefix_cons] at hp_pref
            exact hp_pref.2
          · simp only [ha_cd, ↓reduceIte] at hp_pref
            exact hp_pref
        obtain ⟨r, hr⟩ := ih hcount' hproj' (by simpa using hn)
        exact ⟨r, (TraceEquiv.cons a hr).trans hswap⟩

/-- Two DAG-prefixes of the same word with equal letter counts are trace-equivalent. -/
theorem traceEquiv_of_dagPrefix_of_count_eq {u₁ u₂ u : List Γ}
    (h₁ : DAGPrefix C u₁ u) (h₂ : DAGPrefix C u₂ u) (hc : ∀ a, u₁.count a = u₂.count a) :
    TraceEquiv C u₁ u₂ := by
  rw [dagPrefix_iff_count_and_depProj] at h₁ h₂
  rw [traceEquiv_iff_count_and_depProj]
  refine ⟨hc, fun a b hab => ?_⟩
  have hp₁ := h₁.2 a b hab
  have hp₂ := h₂.2 a b hab
  have hlen : (depProj a b u₁).length = (depProj a b u₂).length := by
    rw [depProj_length, depProj_length, hc a, hc b]
  exact eq_of_prefix_of_length_eq hp₁ hp₂ hlen

/-- The maximal letters of a word in its trace partial order: letters `a` occurring in `w` such
that no strictly later letter in `w` depends on `a`. -/
def maxLetters (C : ConcurrentAlphabet Γ) [Fintype Γ] [DecidableRel C.indep] (w : List Γ) :
    Finset Γ :=
  Finset.univ.filter fun a =>
    a ∈ w ∧ ∀ b : Γ, b ≠ a → C.dep a b → (depProj a b w).getLast? ≠ some b

theorem isIndepSet_maxLetters [Fintype Γ] [DecidableRel C.indep] (w : List Γ) :
    C.IsIndepSet (maxLetters C w) := by
  intro a ha b hb hne
  simp only [maxLetters, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hdep
  have hne_proj : depProj a b w ≠ [] := by
    intro he
    have ha_in : a ∈ depProj a b w := by
      simp [depProj, ha.1]
    rw [he] at ha_in
    exact List.not_mem_nil ha_in
  have hlast_mem : (depProj a b w).getLast hne_proj ∈ depProj a b w := List.getLast_mem hne_proj
  have hlast_eq : (depProj a b w).getLast? = some ((depProj a b w).getLast hne_proj) :=
    List.getLast?_eq_some_getLast hne_proj
  have hlast_mem' : (depProj a b w).getLast hne_proj = a ∨
      (depProj a b w).getLast hne_proj = b :=
    of_decide_eq_true (List.mem_filter.mp (show _ ∈ List.filter _ w from hlast_mem)).2
  rcases hlast_mem' with h1 | h1
  · have hproj_symm : depProj b a w = depProj a b w := by
      simp only [depProj, or_comm]
    exact hb.2 a hne (C.dep_symm hdep) (by rw [hproj_symm, hlast_eq, h1])
  · exact ha.2 b hne.symm hdep (by rw [hlast_eq, h1])

/-- The labeled-index frontier of a word `w`, consisting of `(a, w.count a)` for each maximal
letter `a` of `w`. -/
def maxFrontier (C : ConcurrentAlphabet Γ) [Fintype Γ] [DecidableRel C.indep] (w : List Γ) :
    Finset (Γ × ℕ) :=
  (maxLetters C w).image fun a => (a, w.count a)

theorem card_maxFrontier_le_width [Fintype Γ] [DecidableRel C.indep] (w : List Γ) :
    (maxFrontier C w).card ≤ C.width :=
  (Finset.card_image_le).trans (C.card_le_width (isIndepSet_maxLetters w))

theorem maxFrontier_nonempty_of_ne_nil [Fintype Γ] [DecidableRel C.indep] {w : List Γ}
    (hw : w ≠ []) : (maxFrontier C w).Nonempty := by
  obtain ⟨p, a, hpa⟩ : ∃ p a, w = p ++ [a] :=
    ⟨w.dropLast, w.getLast hw, (List.dropLast_append_getLast hw).symm⟩
  subst hpa
  refine ⟨(a, (p ++ [a]).count a), Finset.mem_image.mpr ⟨a, ?_, rfl⟩⟩
  simp only [maxLetters, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by simp, fun b hba _ => ?_⟩
  rw [depProj_append, depProj_cons, depProj_nil]
  simp only [true_or, ↓reduceIte]
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  simp [Ne.symm hba]

/-- Every element of `maxFrontier C u'` lies in the canonical labeled-index set `labIndSet u`. -/
def labIndSet [Fintype Γ] (u : List Γ) : Finset (Γ × ℕ) :=
  (Finset.univ : Finset Γ).biUnion fun a =>
    (Finset.Icc 1 (u.count a)).image fun k => (a, k)

theorem card_labIndSet [Fintype Γ] (u : List Γ) : (labIndSet u).card = u.length := by
  classical
  rw [labIndSet, Finset.card_biUnion]
  · simp_rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
      Nat.card_Icc, Nat.add_sub_cancel]
    induction u with
    | nil => simp
    | cons a u ih =>
      simp only [List.count_cons, List.length_cons, beq_iff_eq]
      rw [Finset.sum_add_distrib, ih]
      simp
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxa hxb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hxa
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp hxb
    exact hab (Prod.mk.inj hEq).1.symm

theorem maxFrontier_subset_labIndSet [Fintype Γ] [DecidableRel C.indep] {u' u : List Γ}
    (h : DAGPrefix C u' u) : maxFrontier C u' ⊆ labIndSet u := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hamem : a ∈ u' := (Finset.mem_filter.mp ha).2.1
  have hcount : ∀ c, u'.count c ≤ u.count c := (dagPrefix_iff_count_and_depProj.mp h).1
  refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, Finset.mem_image.mpr ⟨u'.count a, ?_, rfl⟩⟩
  exact Finset.mem_Icc.mpr ⟨List.count_pos_iff.mpr hamem, hcount a⟩

/-- If `u₁` and `u₂` are DAG-prefixes of `u` and `depProj a b u₂` ends in `b` while
`u₁.count a < u₂.count a`, then `u₁.count b < u₂.count b`. -/
private theorem count_lt_of_getLast?_depProj {a b : Γ} {u₁ u₂ u : List Γ}
    (_hab : a ≠ b) (h₁ : depProj a b u₁ <+: depProj a b u)
    (h₂ : depProj a b u₂ <+: depProj a b u)
    (hlast : (depProj a b u₂).getLast? = some b)
    (hca : u₁.count a < u₂.count a) :
    u₁.count b < u₂.count b := by
  have hcount_proj (x : Γ) (hx : x = a ∨ x = b) (w : List Γ) :
      (depProj a b w).count x = w.count x := depProj_count_of_mem hx w
  have hlt_len : (depProj a b u₁).length < (depProj a b u₂).length := by
    by_contra hge
    push Not at hge
    obtain ⟨s, hs⟩ := prefix_of_prefix_of_length_le h₂ h₁ hge
    have hc1 := hcount_proj a (Or.inl rfl) u₁
    have hc2 := hcount_proj a (Or.inl rfl) u₂
    have hcs : (depProj a b u₂).count a + s.count a = (depProj a b u₁).count a := by
      rw [← List.count_append, hs]
    omega
  obtain ⟨s, hs⟩ := prefix_of_prefix_of_length_le h₁ h₂ (le_of_lt hlt_len)
  have hs_ne : s ≠ [] := by
    intro he
    rw [he, List.append_nil] at hs
    rw [hs] at hlt_len
    exact lt_irrefl _ hlt_len
  have hs_last : s.getLast? = some b := by
    rw [← hs, List.getLast?_append_of_ne_nil _ hs_ne] at hlast
    exact hlast
  have hb_in_s : b ∈ s := by
    have h1 := List.getLast_mem hs_ne
    rw [List.getLast?_eq_some_getLast hs_ne] at hs_last
    rw [Option.some.inj hs_last] at h1
    exact h1
  have hcb1 := hcount_proj b (Or.inr rfl) u₁
  have hcb2 := hcount_proj b (Or.inr rfl) u₂
  have hcs : (depProj a b u₁).count b + s.count b = (depProj a b u₂).count b := by
    rw [← List.count_append, hs]
  have hs_pos : 0 < s.count b := List.count_pos_iff.mpr hb_in_s
  omega

/-- A DAG-prefix of `u` is uniquely determined up to trace equivalence by its maximal frontier. -/
theorem traceEquiv_of_maxFrontier_eq [Fintype Γ] [DecidableRel C.indep] {u₁ u₂ u : List Γ}
    (h₁ : DAGPrefix C u₁ u) (h₂ : DAGPrefix C u₂ u)
    (hf : maxFrontier C u₁ = maxFrontier C u₂) : TraceEquiv C u₁ u₂ := by
  have hle : ∀ u₁ u₂ : List Γ, DAGPrefix C u₁ u → DAGPrefix C u₂ u →
      maxFrontier C u₁ = maxFrontier C u₂ → ∀ a, u₁.count a ≤ u₂.count a := by
    intro v₁ v₂ hv₁ hv₂ hfeq
    by_contra hnot
    push Not at hnot
    -- Choose a letter `b` with `v₂.count b < v₁.count b` whose last occurrence in `v₁` is latest.
    let bad : Finset Γ := Finset.univ.filter fun a => v₂.count a < v₁.count a
    have hbad_ne : bad.Nonempty := by
      obtain ⟨a, ha⟩ := hnot
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
    let lastIdx (a : Γ) : ℕ := v₁.length - 1 - v₁.reverse.idxOf a
    obtain ⟨b, hb_mem, hb_max⟩ := Finset.exists_max_image bad lastIdx hbad_ne
    have hb_lt : v₂.count b < v₁.count b := (Finset.mem_filter.mp hb_mem).2
    have hb_in : b ∈ v₁ := List.count_pos_iff.mp (by omega)
    have hbm : b ∈ maxLetters C v₁ := by
      simp only [maxLetters, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hb_in, fun c hcb hdep hlast => ?_⟩
      have hproj₁ := (dagPrefix_iff_count_and_depProj.mp hv₁).2 b c hdep
      have hproj₂ := (dagPrefix_iff_count_and_depProj.mp hv₂).2 b c hdep
      have hc_lt : v₂.count c < v₁.count c :=
        count_lt_of_getLast?_depProj (Ne.symm hcb) hproj₂ hproj₁ hlast hb_lt
      have hc_mem : c ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc_lt⟩
      have hle_idx : lastIdx c ≤ lastIdx b := hb_max c hc_mem
      -- Show `lastIdx b < lastIdx c` because in `depProj b c v₁`, the last element is `c`,
      -- meaning the last occurrence of `c` in `v₁` comes strictly after the last occurrence of `b`.
      have hidx_rev : v₁.reverse.idxOf c < v₁.reverse.idxOf b := by
        -- In `v₁.reverse`, `c` appears strictly before `b` because `depProj b c v₁` ends in `c`.
        have hrev_proj : (depProj b c v₁).reverse = depProj b c v₁.reverse := by
          simp [depProj, List.filter_reverse]
        have hhead_rev : (depProj b c v₁.reverse).head? = some c := by
          rw [← hrev_proj, List.head?_reverse, hlast]
        -- Decompose `v₁.reverse` at the first occurrence of `c`.
        have hc_in : c ∈ v₁.reverse := List.mem_reverse.mpr (List.count_pos_iff.mp (by omega))
        obtain ⟨r₁, r₂, hr_eq, hcr₁⟩ := exists_split_first_mem hc_in
        have hbr₁ : b ∉ r₁ := by
          intro hbr
          obtain ⟨s₁, s₂, hs_eq, hbs₁⟩ := exists_split_first_mem hbr
          have hcs₁ : c ∉ s₁ := fun h => hcr₁ (hs_eq ▸ List.mem_append_left _ h)
          rw [hr_eq, hs_eq, List.append_assoc, depProj_append,
            depProj_of_notMem hbs₁ hcs₁, List.nil_append, List.cons_append, depProj_cons]
            at hhead_rev
          simp only [true_or, ↓reduceIte, List.head?_cons, Option.some.injEq] at hhead_rev
          exact hcb hhead_rev.symm
        have hidx_c : v₁.reverse.idxOf c = r₁.length := by
          rw [hr_eq, List.idxOf_append_of_notMem hcr₁, List.idxOf_cons_self, Nat.add_zero]
        have hidx_b : r₁.length < v₁.reverse.idxOf b := by
          rw [hr_eq, List.idxOf_append_of_notMem hbr₁, List.idxOf_cons_ne _ hcb]
          omega
        omega
      have hrb_lt : v₁.reverse.idxOf b < v₁.length := by
        rw [← List.length_reverse]
        exact List.idxOf_lt_length_of_mem (List.mem_reverse.mpr hb_in)
      dsimp only [lastIdx] at hle_idx
      omega
    have hmem_f : (b, v₁.count b) ∈ maxFrontier C v₂ := by
      rw [← hfeq]
      exact Finset.mem_image.mpr ⟨b, hbm, rfl⟩
    obtain ⟨b', _, hEq⟩ := Finset.mem_image.mp hmem_f
    have hbb' : b' = b := (Prod.mk.inj hEq).1
    have hcnt : v₂.count b = v₁.count b := by
      have h2 := (Prod.mk.inj hEq).2
      rwa [hbb'] at h2
    omega
  exact traceEquiv_of_dagPrefix_of_count_eq h₁ h₂ fun a =>
    le_antisymm (hle u₁ u₂ h₁ h₂ hf a) (hle u₂ u₁ h₂ h₁ hf.symm a)

private theorem choose_le_pow_self (n j : ℕ) : n.choose j ≤ n ^ j := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    cases n with
    | zero => simp
    | succ m =>
      have h1 : (m + 1).choose (j + 1) ≤ (m + 1) * m.choose j := by
        have hmul := Nat.add_one_mul_choose_eq m j
        have hpos : 1 ≤ j + 1 := Nat.succ_pos j
        calc (m + 1).choose (j + 1)
            ≤ (m + 1).choose (j + 1) * (j + 1) := Nat.le_mul_of_pos_right _ hpos
          _ = (m + 1) * m.choose j := by linarith
      calc (m + 1).choose (j + 1)
          ≤ (m + 1) * m.choose j := h1
        _ ≤ (m + 1) * m ^ j := Nat.mul_le_mul_left _ (ih m)
        _ ≤ (m + 1) * (m + 1) ^ j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) j)
        _ = (m + 1) ^ (j + 1) := by rw [pow_succ']

private theorem sum_choose_pos_le_mul_pow {n w : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 w, n.choose j ≤ w * n ^ w := by
  calc ∑ j ∈ Finset.Icc 1 w, n.choose j
      ≤ ∑ j ∈ Finset.Icc 1 w, n ^ j :=
        Finset.sum_le_sum fun j _ => choose_le_pow_self n j
    _ ≤ ∑ _j ∈ Finset.Icc 1 w, n ^ w :=
        Finset.sum_le_sum fun j hj => Nat.pow_le_pow_right hn (Finset.mem_Icc.mp hj).2
    _ = w * n ^ w := by simp

private theorem sum_choose_zero_to_le_pow_succ (n w : ℕ) :
    ∑ j ∈ Finset.range (w + 1), n.choose j ≤ (n + 1) ^ w := by
  induction w with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hch : n.choose (k + 1) ≤ (n + 1) ^ k * n := by
      calc n.choose (k + 1) ≤ n ^ (k + 1) := choose_le_pow_self n (k + 1)
        _ = n ^ k * n := by rw [pow_succ]
        _ ≤ (n + 1) ^ k * n := Nat.mul_le_mul_right n (Nat.pow_le_pow_left (by omega) k)
    linarith

/-- The finite set of DAG-prefix traces of a word `u`. -/
noncomputable def dagPrefixTraces [Fintype Γ] (C : ConcurrentAlphabet Γ) (u : List Γ) :
    Finset (Trace C) := by
  classical
  exact (u.sublists.toFinset.filter (fun u' => DAGPrefix C u' u)).image (traceOf C)

/-- A trace `t` belongs to `dagPrefixTraces C u` iff some word `u'` representing `t` is a
DAG-prefix of `u`. -/
theorem mem_dagPrefixTraces_iff [Fintype Γ] {u : List Γ} {t : Trace C} :
    t ∈ dagPrefixTraces C u ↔ ∃ u', traceOf C u' = t ∧ DAGPrefix C u' u := by
  classical
  unfold dagPrefixTraces
  simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨u', ⟨_, hdag⟩, rfl⟩
    exact ⟨u', rfl, hdag⟩
  · rintro ⟨u', rfl, hdag⟩
    obtain ⟨r, hr⟩ := hdag
    -- `u'` is a sublist of `u' ++ r`, and `u' ++ r ~ u`, wait: `u'` need not be a sublist of `u`!
    -- Instead, prove `u'` is trace-equivalent to a sublist of `u`!
    have hex : ∃ v, v.Sublist u ∧ TraceEquiv C v u' := by
      induction hlen : u'.length generalizing u' u with
      | zero =>
        have hu' : u' = [] := List.eq_nil_of_length_eq_zero hlen
        subst hu'
        exact ⟨[], List.nil_sublist u, TraceEquiv.refl []⟩
      | succ k ih =>
        cases u' with
        | nil => simp at hlen
        | cons a v' =>
          have hau : a ∈ u := by
            have := hr.mem_iff (a := a)
            exact this.mp (by simp)
          obtain ⟨p, q, rfl, hap⟩ := exists_split_first_mem hau
          have hindep : ∀ b ∈ p, C.indep a b := by
            intro b hb
            by_contra hdep
            have hproj := depProj_eq_of_traceEquiv hr hdep
            have hba : b ≠ a := fun h => hap (h ▸ hb)
            have h1 : (depProj a b ((a :: v') ++ r)).head? = some a := by simp [depProj_cons]
            have h2 : (depProj a b p).head? = some b := by
              obtain ⟨p₁, p₂, hp_eq, hbp₁⟩ := exists_split_first_mem hb
              have hap₁ : a ∉ p₁ := fun h => hap (hp_eq ▸ List.mem_append_left _ h)
              rw [hp_eq, depProj_append, depProj_of_notMem hap₁ hbp₁, List.nil_append, depProj_cons]
              simp
            have hne_p : depProj a b p ≠ [] := by
              intro he; rw [he] at h2; simp at h2
            rw [hproj, depProj_append, List.head?_append_of_ne_nil _ hne_p, h2] at h1
            exact hba (Option.some.inj h1)
          have hswap : TraceEquiv C (a :: (p ++ q)) (p ++ a :: q) := by
            have hc := (TraceEquiv.comm_of_forall_indep hindep).symm
            simpa [List.append_assoc] using TraceEquiv.append_right q hc
          have hr' : TraceEquiv C (v' ++ r) (p ++ q) :=
            TraceEquiv.cancel_left (p := [a]) (by simpa using hr.trans hswap.symm)
          obtain ⟨v, hvsub, hveq⟩ := ih (u' := v') (u := p ++ q) hr' (by simpa using hlen)
          -- Insert `a` into `v` at the boundary where `p` and `q` split!
          -- Wait: since `v <+ p ++ q`, `v = v₁ ++ v₂` with `v₁ <+ p` and `v₂ <+ q`!
          obtain ⟨v₁, v₂, hv_eq, hv₁, hv₂⟩ := List.sublist_append_iff.mp hvsub
          have hindep_v₁ : ∀ b ∈ v₁, C.indep a b := fun b hb => hindep b (hv₁.subset hb)
          refine ⟨v₁ ++ a :: v₂, ?_, ?_⟩
          · exact hv₁.append (List.Sublist.cons_cons a hv₂)
          · have hcomm := TraceEquiv.comm_of_forall_indep hindep_v₁
            have hstep : TraceEquiv C (v₁ ++ a :: v₂) (a :: (v₁ ++ v₂)) := by
              simpa [List.append_assoc] using TraceEquiv.append_right v₂ hcomm
            exact hstep.trans (TraceEquiv.cons a (hv_eq ▸ hveq))
    obtain ⟨v, hvsub, hveq⟩ := hex
    exact ⟨v, ⟨List.mem_sublists.mpr hvsub, dagPrefix_of_traceEquiv_left hveq.symm ⟨r, hr⟩⟩,
      Quotient.sound hveq⟩

/-- **DAG-prefix cardinality bound**: a word `u` over a finite concurrent alphabet of width `ω`
has at most `(|u| + 1) ^ ω` distinct DAG-prefix traces. -/
theorem card_dagPrefixTraces_le [Fintype Γ] (C : ConcurrentAlphabet Γ) (u : List Γ) :
    (dagPrefixTraces C u).card ≤ (u.length + 1) ^ C.width := by
  classical
  let f : Trace C → Finset (Γ × ℕ) :=
    Quotient.lift (fun w => maxFrontier C w) fun u₁ u₂ h => by
      -- Trace-equivalent words have equal `maxFrontier` because `count` and `depProj` agree!
      ext ⟨a, k⟩
      simp only [maxFrontier, Finset.mem_image, maxLetters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor <;> rintro ⟨x, ⟨hxmem, hxlast⟩, hEq⟩
      · refine ⟨x, ⟨h.mem_iff.mp hxmem, fun b hbx hdep => ?_⟩, ?_⟩
        · rw [← depProj_eq_of_traceEquiv h hdep]; exact hxlast b hbx hdep
        · rw [← h.count_eq x]; exact hEq
      · refine ⟨x, ⟨h.mem_iff.mpr hxmem, fun b hbx hdep => ?_⟩, ?_⟩
        · rw [depProj_eq_of_traceEquiv h hdep]; exact hxlast b hbx hdep
        · rw [h.count_eq x]; exact hEq
  let target : Finset (Finset (Γ × ℕ)) :=
    (labIndSet u).powerset.filter fun S => S.card ≤ C.width
  have hmaps : ∀ t ∈ dagPrefixTraces C u, f t ∈ target := by
    intro t ht
    obtain ⟨u', rfl, hdag⟩ := mem_dagPrefixTraces_iff.mp ht
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (maxFrontier_subset_labIndSet hdag), card_maxFrontier_le_width u'⟩
  have hinj : Set.InjOn f (dagPrefixTraces C u) := by
    intro t₁ ht₁ t₂ ht₂ hft
    obtain ⟨u₁, rfl, hdag₁⟩ := mem_dagPrefixTraces_iff.mp ht₁
    obtain ⟨u₂, rfl, hdag₂⟩ := mem_dagPrefixTraces_iff.mp ht₂
    exact Quotient.sound (traceEquiv_of_maxFrontier_eq hdag₁ hdag₂ hft)
  have hle_target : (dagPrefixTraces C u).card ≤ target.card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have htarget_card : target.card = ∑ j ∈ Finset.range (C.width + 1), u.length.choose j := by
    have hsplit : target =
        (Finset.range (C.width + 1)).biUnion fun j => (labIndSet u).powersetCard j := by
      ext S
      simp only [target, Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · intro ⟨hsub, hcard⟩
        exact ⟨S.card, Nat.lt_succ_of_le hcard, hsub, rfl⟩
      · rintro ⟨j, hj, hsub, hcard⟩
        exact ⟨hsub, hcard ▸ Nat.lt_succ_iff.mp hj⟩
    rw [hsplit, Finset.card_biUnion]
    · simp_rw [Finset.card_powersetCard, card_labIndSet]
    · intro i _ j _ hij
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro S hSi hSj
      exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)
  exact hle_target.trans (htarget_card ▸ sum_choose_zero_to_le_pow_succ u.length C.width)

omit [DecidableEq Γ] in
/-- **Trace-cut cardinality bound**: for sets `S₁` of length-`n₁` traces and `S₂` of length-`n₂`
traces with `n = n₁ + n₂ ≥ 1`, the set of pairwise products `S = {t₁ * t₂ | t₁ ∈ S₁, t₂ ∈ S₂}`
satisfies `|S₁| * |S₂| ≤ ω * n ^ ω * |S|`. -/
theorem card_traceMul_ge [Fintype Γ] (C : ConcurrentAlphabet Γ) [DecidableEq (Trace C)] {n₁ n₂ : ℕ}
    (hn : 1 ≤ n₁ + n₂) {S₁ S₂ : Finset (Trace C)}
    (hS₁ : ∀ t ∈ S₁, t.length = n₁) (hS₂ : ∀ t ∈ S₂, t.length = n₂) :
    S₁.card * S₂.card ≤
      C.width * (n₁ + n₂) ^ C.width *
        ((S₁.product S₂).image fun p : Trace C × Trace C => p.1 * p.2).card := by
  classical
  let S := (S₁.product S₂).image fun p : Trace C × Trace C => p.1 * p.2
  have hfiber : ∀ t ∈ S,
      ((S₁.product S₂).filter fun p => p.1 * p.2 = t).card ≤ C.width * (n₁ + n₂) ^ C.width := by
    intro t ht
    obtain ⟨⟨t₁, t₂⟩, hp, rfl⟩ := Finset.mem_image.mp ht
    refine Quotient.inductionOn t₁ (fun u₁ => Quotient.inductionOn t₂ (fun u₂ => ?_)) hp
    intro hp_mem
    have hu₁_len : u₁.length = n₁ := hS₁ _ (Finset.mem_product.mp hp_mem).1
    have hu₂_len : u₂.length = n₂ := hS₂ _ (Finset.mem_product.mp hp_mem).2
    have hu_len : (u₁ ++ u₂).length = n₁ + n₂ := by simp [hu₁_len, hu₂_len]
    by_cases hn₁ : n₁ = 0
    · -- Only one possible prefix of length 0.
      have hcard_le_one :
          ((S₁.product S₂).filter fun p => p.1 * p.2 = traceOf C (u₁ ++ u₂)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun p hp q hq => ?_
        have hp' := Finset.mem_filter.mp hp
        have hq' := Finset.mem_filter.mp hq
        have hp1 : p.1 = traceOf C [] := by
          refine Quotient.inductionOn p.1 (fun w hw => ?_) (hS₁ p.1 (Finset.mem_product.mp hp'.1).1)
          exact congrArg (traceOf C) (List.eq_nil_of_length_eq_zero (hw.trans hn₁))
        have hq1 : q.1 = traceOf C [] := by
          refine Quotient.inductionOn q.1 (fun w hw => ?_) (hS₁ q.1 (Finset.mem_product.mp hq'.1).1)
          exact congrArg (traceOf C) (List.eq_nil_of_length_eq_zero (hw.trans hn₁))
        have h1eq : p.1 = q.1 := hp1.trans hq1.symm
        have h2eq : p.2 = q.2 := Trace.mul_left_cancel (by rw [hp'.2, ← hq'.2, h1eq])
        exact Prod.ext h1eq h2eq
      have hpos : 1 ≤ C.width * (n₁ + n₂) ^ C.width := by
        have hw : 1 ≤ C.width := by
          have : (u₁ ++ u₂) ≠ [] := by intro h; simp [h] at hu_len; omega
          have hne_f := maxFrontier_nonempty_of_ne_nil (C := C) this
          exact (Finset.card_pos.mpr hne_f).trans_le (card_maxFrontier_le_width _)
        exact Nat.mul_pos hw (Nat.pow_pos (by omega))
      exact hcard_le_one.trans hpos
    · -- `n₁ ≥ 1`: every `p.1` in the fiber maps injectively to a nonempty `maxFrontier` of size
      -- between `1` and `C.width` inside `labIndSet (u₁ ++ u₂)`.
      let g : Trace C × Trace C → Finset (Γ × ℕ) :=
        fun p => Quotient.lift (fun w => maxFrontier C w) (fun v₁ v₂ h => by
          ext ⟨a, k⟩
          simp only [maxFrontier, Finset.mem_image, maxLetters, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor <;> rintro ⟨x, ⟨hxmem, hxlast⟩, hEq⟩
          · refine ⟨x, ⟨h.mem_iff.mp hxmem, fun b hbx hdep => ?_⟩, ?_⟩
            · rw [← depProj_eq_of_traceEquiv h hdep]; exact hxlast b hbx hdep
            · rw [← h.count_eq x]; exact hEq
          · refine ⟨x, ⟨h.mem_iff.mpr hxmem, fun b hbx hdep => ?_⟩, ?_⟩
            · rw [depProj_eq_of_traceEquiv h hdep]; exact hxlast b hbx hdep
            · rw [h.count_eq x]; exact hEq) p.1
      let target : Finset (Finset (Γ × ℕ)) :=
        (labIndSet (u₁ ++ u₂)).powerset.filter fun A => 1 ≤ A.card ∧ A.card ≤ C.width
      have hmaps : ∀ p ∈ (S₁.product S₂).filter (fun p => p.1 * p.2 = traceOf C (u₁ ++ u₂)),
          g p ∈ target := by
        rintro ⟨t₁', t₂'⟩ hp
        have hp' := Finset.mem_filter.mp hp
        refine Quotient.inductionOn₂ t₁' t₂' (fun v₁ v₂ hmem heq => ?_)
          (Finset.mem_product.mp hp'.1) hp'.2
        have hv₁_len : v₁.length = n₁ := hS₁ _ hmem.1
        have hdag : DAGPrefix C v₁ (u₁ ++ u₂) := ⟨v₂, traceOf_eq_iff.mp heq⟩
        have hv₁_ne : v₁ ≠ [] := by intro h; simp [h] at hv₁_len; omega
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (maxFrontier_subset_labIndSet hdag),
            Finset.card_pos.mpr (maxFrontier_nonempty_of_ne_nil hv₁_ne),
            card_maxFrontier_le_width v₁⟩
      have hinj : Set.InjOn g ((S₁.product S₂).filter (fun p => p.1 * p.2 =
        traceOf C (u₁ ++ u₂))) := by
        rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq hgpq
        have hp' := Finset.mem_filter.mp hp
        have hq' := Finset.mem_filter.mp hq
        have h1eq : p1 = q1 := by
          refine Quotient.inductionOn₂ p1 q1 (fun v₁ w₁ => Quotient.inductionOn₂ p2 q2
            (fun v₂ w₂ h1 h2 hg => ?_)) hp'.2 hq'.2 hgpq
          exact Quotient.sound (traceEquiv_of_maxFrontier_eq ⟨v₂, traceOf_eq_iff.mp h1⟩
            ⟨w₂, traceOf_eq_iff.mp h2⟩ hg)
        have h2eq : p2 = q2 := Trace.mul_left_cancel (by rw [hp'.2, ← hq'.2, h1eq])
        exact Prod.ext h1eq h2eq
      have hle_t := Finset.card_le_card_of_injOn g hmaps hinj
      have htarget_card : target.card = ∑ j ∈ Finset.Icc 1 C.width, (n₁ + n₂).choose j := by
        have hsplit : target =
            (Finset.Icc 1 C.width).biUnion fun j => (labIndSet (u₁ ++ u₂)).powersetCard j := by
          ext A
          simp only [target, Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
            Finset.mem_Icc, Finset.mem_powersetCard]
          constructor
          · intro ⟨hsub, h1, h2⟩; exact ⟨A.card, ⟨h1, h2⟩, hsub, rfl⟩
          · rintro ⟨j, ⟨h1, h2⟩, hsub, hcard⟩; exact ⟨hsub, hcard ▸ h1, hcard ▸ h2⟩
        rw [hsplit, Finset.card_biUnion]
        · simp_rw [Finset.card_powersetCard, card_labIndSet, hu_len]
        · intro i _ j _ hij
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro A hAi hAj
          exact hij ((Finset.mem_powersetCard.mp hAi).2.symm.trans
            (Finset.mem_powersetCard.mp hAj).2)
      exact hle_t.trans (htarget_card ▸ sum_choose_pos_le_mul_pow hn)
  have hsum : (S₁.product S₂).card =
      ∑ t ∈ S, ((S₁.product S₂).filter fun p => p.1 * p.2 = t).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
      exact ⟨fun hp => ⟨p.1 * p.2, ⟨p, hp, rfl⟩, hp, rfl⟩, fun ⟨_, _, hp, _⟩ => hp⟩
    · intro t₁ _ t₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      exact hne ((Finset.mem_filter.mp hp₁).2.symm.trans (Finset.mem_filter.mp hp₂).2)
  rw [show S₁.card * S₂.card = (S₁.product S₂).card from (Finset.card_product S₁ S₂).symm, hsum]
  calc ∑ t ∈ S, ((S₁.product S₂).filter fun p => p.1 * p.2 = t).card
      ≤ ∑ _t ∈ S, (C.width * (n₁ + n₂) ^ C.width) := Finset.sum_le_sum hfiber
    _ = S.card * (C.width * (n₁ + n₂) ^ C.width) := by rw [Finset.sum_const]; rfl
    _ = C.width * (n₁ + n₂) ^ C.width * S.card := Nat.mul_comm _ _

end DAGPrefixAPI

end Cslib.Language
