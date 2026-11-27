/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/

module
-- upstream: candidate

public import Cslib.Foundations.Semantics.FLTS.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import CslibFrontier.Computability.Languages.ChomskyNormalForm
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.Perm.Basic

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Formal Language Reachability on Labeled Directed Graphs

General language-theoretic and graph-reachability foundations:

1. **Finite labeled directed graphs and language reachability**:
   `FinLabeledDigraph`, `FinLabeledDigraph.Walk`, its bridge to `Cslib.LTS.MTr`, and
   `LanguageReachable`.
2. **Myhill–Nerode indistinguishability and `k`-order-oblivious languages**:
   `Indistinguishable` (bridged to `Language.leftQuotient`), `IsOrderOblivious`,
   `IsAutomatonOrderOblivious` (over `Cslib.FLTS`), and `IsAlphaOrderOblivious`, together with the
   equivalence `1`-order-oblivious `↔` order-oblivious and the hierarchy
   `k₁`-order-oblivious `⊆` `k₂`-order-oblivious for `1 ≤ k₁ ≤ k₂`.
3. **Representative-pruning reachability on graded permutation-consistent DAGs**:
   `IsGradedPermDAG`, `repTable`, and `repReach_eq_true_iff`, proving that retaining at most one
   representative path per `(vertex, controlState)` pair decides `LanguageReachable` for any
   prefix-closed automaton-order-oblivious language.
4. **Chomsky Normal Form grammar reachability on graded DAGs**:
   `cnfRuleMul`, `oneStepMatrix`, `cykDagTable`, and `mem_cykDagTable_iff`, proving exact
   soundness and completeness of dynamic-programming CYK reachability over acyclic labeled graphs.

## Main definitions

* `CslibFrontier.Computability.Languages.FinLabeledDigraph`: finite vertex and labeled-edge
  directed graph.
* `CslibFrontier.Computability.Languages.FinLabeledDigraph.Walk`: finite labeled walk `s ⇝ t`.
* `CslibFrontier.Computability.Languages.LanguageReachable`: existence of an `(s, t)`-walk with
  label in `L`.
* `CslibFrontier.Computability.Languages.Indistinguishable`: Myhill–Nerode right-extension
  equivalence.
* `CslibFrontier.Computability.Languages.IsPrefixClosed`: ` ∈ L` and prefix closure of `L`.
* `CslibFrontier.Computability.Languages.IsOrderOblivious`,
  `CslibFrontier.Computability.Languages.IsAutomatonOrderOblivious`,
  `CslibFrontier.Computability.Languages.IsAlphaOrderOblivious`: permutation-invariant language
  classes over `Cslib.FLTS`.
* `CslibFrontier.Computability.Languages.IsGradedPermDAG`: graded DAG whose `(s, u)`-walks share a
  multiset.
* `CslibFrontier.Computability.Languages.repTable`,
  `CslibFrontier.Computability.Languages.repReach`: layered representative DP.
* `CslibFrontier.Computability.Languages.cnfRuleMul`,
  `CslibFrontier.Computability.Languages.oneStepMatrix`,
  `CslibFrontier.Computability.Languages.cykDagTable`,
  `CslibFrontier.Computability.Languages.cykDagReach`: CNF reachability DP.

## Main results

* `CslibFrontier.Computability.Languages.FinLabeledDigraph.exists_walk_label_iff_mTr`: equivalence
  between `FinLabeledDigraph.Walk` labels and `Cslib.LTS.MTr`.
* `CslibFrontier.Computability.Languages.indistinguishable_of_deterministic_mTr_eq`: equal target
  states in a deterministic `Cslib.LTS` induce Myhill–Nerode indistinguishable traces.
* `CslibFrontier.Computability.Languages.isOrderOblivious_iff_one` and
  `CslibFrontier.Computability.Languages.IsAlphaOrderOblivious.mono`: the `k`-order-oblivious
  hierarchy.
* `CslibFrontier.Computability.Languages.repReach_eq_true_iff`: soundness and completeness of
  layered representative-pruning reachability.
* `CslibFrontier.Computability.Languages.mem_cykDagTable_iff` and
  `CslibFrontier.Computability.Languages.cykDagReach_eq_true_iff`: soundness and completeness of
  CNF CYK reachability on graded DAGs.
-/

public section

namespace CslibFrontier.Computability.Languages

section LabeledDigraph

variable {V α : Type*}

/-- A finite edge-labeled directed graph `G = (N, E)` with vertex finset `nodes` and labeled edge
finset `edges ⊆ N × α × N`. -/
@[ext]
structure FinLabeledDigraph (V α : Type*) where
  /-- Finite set of vertices. -/
  nodes : Finset V
  /-- Finite set of labeled directed edges `(u, a, v)`. -/
  edges : Finset (V × α × V)
  /-- Source of every edge belongs to `nodes`. -/
  source_mem : ∀ e ∈ edges, e.1 ∈ nodes
  /-- Target of every edge belongs to `nodes`. -/
  target_mem : ∀ e ∈ edges, e.2.2 ∈ nodes

instance instInhabitedFinLabeledDigraph : Inhabited (FinLabeledDigraph V α) :=
  ⟨⟨∅, ∅, fun _ h ↦ absurd h (Finset.notMem_empty _),
    fun _ h ↦ absurd h (Finset.notMem_empty _)⟩⟩

namespace FinLabeledDigraph

/-- Underlying `Cslib.LTS` associated with a finite labeled directed graph. -/
@[expose]
def toLTS (G : FinLabeledDigraph V α) : Cslib.LTS V α where
  Tr u a v := (u, a, v) ∈ G.edges

/-- Characterization of transitions in `G.toLTS`. -/
@[simp]
theorem toLTS_tr_iff (G : FinLabeledDigraph V α) (u : V) (a : α) (v : V) :
    G.toLTS.Tr u a v ↔ (u, a, v) ∈ G.edges :=
  Iff.rfl

/-- A finite walk from `s` to `t` in `G` (including `0`-step empty walks at vertices
`u ∈ G.nodes`). -/
inductive Walk (G : FinLabeledDigraph V α) : V → V → Type _ where
  /-- Empty `0`-step walk at vertex `u ∈ G.nodes`. -/
  | nil {u : V} (hu : u ∈ G.nodes) : G.Walk u u
  /-- Prepend a labeled edge `(u, a, v) ∈ G.edges` to a walk from `v` to `t`. -/
  | cons {u v t : V} {a : α} (he : (u, a, v) ∈ G.edges) (rest : G.Walk v t) : G.Walk u t

/-- Induced word `lbl(π)` along a walk `π`. -/
@[expose]
def Walk.label {G : FinLabeledDigraph V α} {s t : V} : G.Walk s t → List α
  | .nil _ => []
  | .cons (a := a) _ rest => a :: rest.label

/-- Label of an empty walk is `[]`. -/
@[simp]
theorem Walk.label_nil {G : FinLabeledDigraph V α} {u : V} (hu : u ∈ G.nodes) :
    (Walk.nil hu : G.Walk u u).label = [] :=
  rfl

/-- Label of a `cons` walk prepends the edge label. -/
@[simp]
theorem Walk.label_cons {G : FinLabeledDigraph V α} {u v t : V} {a : α}
    (he : (u, a, v) ∈ G.edges) (rest : G.Walk v t) :
    (Walk.cons he rest).label = a :: rest.label :=
  rfl

/-- Number of edges in a walk `π`. -/
@[expose]
def Walk.length {G : FinLabeledDigraph V α} {s t : V} : G.Walk s t → ℕ
  | .nil _ => 0
  | .cons _ rest => rest.length + 1

/-- Length of an empty walk is `0`. -/
@[simp]
theorem Walk.length_nil {G : FinLabeledDigraph V α} {u : V} (hu : u ∈ G.nodes) :
    (Walk.nil hu : G.Walk u u).length = 0 :=
  rfl

/-- Length of a `cons` walk increments by `1`. -/
@[simp]
theorem Walk.length_cons {G : FinLabeledDigraph V α} {u v t : V} {a : α}
    (he : (u, a, v) ∈ G.edges) (rest : G.Walk v t) :
    (Walk.cons he rest).length = rest.length + 1 :=
  rfl

/-- Length of `π.label` equals `π.length`. -/
@[simp]
theorem Walk.length_label {G : FinLabeledDigraph V α} {s t : V} (π : G.Walk s t) :
    π.label.length = π.length := by
  induction π with
  | nil _ => rfl
  | cons _ rest ih => simp [Walk.label, Walk.length, ih]

/-- Source vertex of any walk belongs to `G.nodes`. -/
theorem Walk.source_mem {G : FinLabeledDigraph V α} {s t : V} : G.Walk s t → s ∈ G.nodes
  | .nil hu => hu
  | .cons he _ => G.source_mem _ he

/-- Target vertex of any walk belongs to `G.nodes`. -/
theorem Walk.target_mem {G : FinLabeledDigraph V α} {s t : V} : G.Walk s t → t ∈ G.nodes
  | .nil hu => hu
  | .cons _ rest => rest.target_mem

/-- Concatenate two compatible walks `s ⇝ m` and `m ⇝ t`. -/
@[expose]
def Walk.append {G : FinLabeledDigraph V α} {s m t : V} :
    G.Walk s m → G.Walk m t → G.Walk s t
  | .nil _, π₂ => π₂
  | .cons he rest, π₂ => .cons he (rest.append π₂)

/-- Label of `π₁.append π₂` is `π₁.label ++ π₂.label`. -/
@[simp]
theorem Walk.label_append {G : FinLabeledDigraph V α} {s m t : V}
    (π₁ : G.Walk s m) (π₂ : G.Walk m t) :
    (π₁.append π₂).label = π₁.label ++ π₂.label := by
  induction π₁ with
  | nil _ => rfl
  | cons _ rest ih => simp [Walk.append, ih]

/-- Single-edge walk `(u, a, v)` in `G`. -/
@[expose]
def Walk.single {G : FinLabeledDigraph V α} {u v : V} {a : α}
    (he : (u, a, v) ∈ G.edges) : G.Walk u v :=
  .cons he (.nil (G.target_mem _ he))

/-- Label of a single-edge walk is `[a]`. -/
@[simp]
theorem Walk.label_single {G : FinLabeledDigraph V α} {u v : V} {a : α}
    (he : (u, a, v) ∈ G.edges) :
    (Walk.single he).label = [a] :=
  rfl

/-- Extend a walk on the right by a single edge `(u, a, t) ∈ G.edges`. -/
@[expose]
def Walk.snoc {G : FinLabeledDigraph V α} {s u t : V} {a : α}
    (π : G.Walk s u) (he : (u, a, t) ∈ G.edges) : G.Walk s t :=
  π.append (Walk.single he)

/-- Label of `π.snoc he` is `π.label ++ [a]`. -/
@[simp]
theorem Walk.label_snoc {G : FinLabeledDigraph V α} {s u t : V} {a : α}
    (π : G.Walk s u) (he : (u, a, t) ∈ G.edges) :
    (π.snoc he).label = π.label ++ [a] := by
  simp [Walk.snoc]

/-- Every walk is either empty (`s = t` and `label = []`) or decomposes at its last edge. -/
theorem Walk.eq_nil_or_snoc {G : FinLabeledDigraph V α} {s t : V} (π : G.Walk s t) :
    (s = t ∧ π.label = []) ∨
      ∃ (u : V) (a : α) (π₀ : G.Walk s u),
        (u, a, t) ∈ G.edges ∧ π.label = π₀.label ++ [a] := by
  induction π with
  | nil _ => exact Or.inl ⟨rfl, rfl⟩
  | @cons u _ _ a he rest ih =>
    rcases ih with ⟨rfl, hnil⟩ | ⟨w, b, π₀, he', hlbl⟩
    · refine Or.inr ⟨u, a, .nil (G.source_mem _ he), he, ?_⟩
      simp [hnil]
    · refine Or.inr ⟨w, b, .cons he π₀, he', ?_⟩
      simp [hlbl]

/-- Factor a walk whose label decomposes as `w₁ ++ w₂` into two sub-walks labeled `w₁` and `w₂`. -/
theorem Walk.split_of_label_append {G : FinLabeledDigraph V α} {s t : V}
    (π : G.Walk s t) {w₁ w₂ : List α} (h : π.label = w₁ ++ w₂) :
    ∃ (m : V) (π₁ : G.Walk s m) (π₂ : G.Walk m t), π₁.label = w₁ ∧ π₂.label = w₂ := by
  induction w₁ generalizing s with
  | nil =>
    exact ⟨s, .nil π.source_mem, π, rfl, by simpa using h⟩
  | cons a w₁ ih =>
    cases π with
    | nil _ => simp at h
    | @cons _ v _ b he rest =>
      simp only [Walk.label_cons, List.cons_append, List.cons.injEq] at h
      rcases h with ⟨hba, hrest⟩
      subst hba
      obtain ⟨m, π₁, π₂, h₁, h₂⟩ := ih rest hrest
      exact ⟨m, .cons he π₁, π₂, by simp [h₁], h₂⟩

/-- Bridge between `FinLabeledDigraph.Walk` and `Cslib.LTS.MTr`. -/
theorem exists_walk_label_iff_mTr (G : FinLabeledDigraph V α) (s t : V) (w : List α) :
    (∃ π : G.Walk s t, π.label = w) ↔ s ∈ G.nodes ∧ t ∈ G.nodes ∧ G.toLTS.MTr s w t := by
  constructor
  · rintro ⟨π, rfl⟩
    refine ⟨π.source_mem, π.target_mem, ?_⟩
    induction π with
    | nil _ => exact .refl
    | cons he _ ih => exact .stepL he ih
  · have hback : ∀ {u v : V} {μs : List α},
        G.toLTS.MTr u μs v → u ∈ G.nodes → ∃ π : G.Walk u v, π.label = μs := by
      intro u v μs hm
      induction hm with
      | refl => intro hu; exact ⟨.nil hu, rfl⟩
      | stepL htr _ ih =>
        intro _
        obtain ⟨π, rfl⟩ := ih (G.target_mem _ htr)
        exact ⟨.cons htr π, rfl⟩
    rintro ⟨hs, -, hm⟩
    exact hback hm hs

end FinLabeledDigraph

/-- **`L`-reachability** on a finite labeled directed graph: there exists a walk from `s` to `t`
whose induced label word belongs to `L`. -/
def LanguageReachable (G : FinLabeledDigraph V α) (L : Language α) (s t : V) : Prop :=
  ∃ π : G.Walk s t, π.label ∈ L

/-- Characterization of `LanguageReachable`. -/
theorem languageReachable_iff {G : FinLabeledDigraph V α} {L : Language α} {s t : V} :
    LanguageReachable G L s t ↔ ∃ π : G.Walk s t, π.label ∈ L :=
  Iff.rfl

/-- `LanguageReachable` is monotone in the target language `L`. -/
theorem LanguageReachable.mono {G : FinLabeledDigraph V α} {L₁ L₂ : Language α} {s t : V}
    (hL : L₁ ≤ L₂) (h : LanguageReachable G L₁ s t) : LanguageReachable G L₂ s t := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, hL hπ⟩

/-- Concatenating `L₁`-reachable `(s, m)` and `L₂`-reachable `(m, t)` yields `(L₁ * L₂)`-reachable
`(s, t)`. -/
theorem LanguageReachable.mul {G : FinLabeledDigraph V α} {L₁ L₂ : Language α} {s m t : V}
    (h₁ : LanguageReachable G L₁ s m) (h₂ : LanguageReachable G L₂ m t) :
    LanguageReachable G (L₁ * L₂) s t := by
  obtain ⟨π₁, hπ₁⟩ := h₁
  obtain ⟨π₂, hπ₂⟩ := h₂
  refine ⟨π₁.append π₂, ?_⟩
  rw [FinLabeledDigraph.Walk.label_append]
  exact Language.append_mem_mul hπ₁ hπ₂

end LabeledDigraph

section OrderOblivious

variable {α : Type*}

/-- Myhill–Nerode indistinguishability with respect to a language `L`: `w₁` and `w₂` have the exact
same legal right continuations in `L`. -/
def Indistinguishable (L : Language α) (w₁ w₂ : List α) : Prop :=
  ∀ u : List α, w₁ ++ u ∈ L ↔ w₂ ++ u ∈ L

/-- Characterization of `Indistinguishable`. -/
theorem indistinguishable_iff {L : Language α} {w₁ w₂ : List α} :
    Indistinguishable L w₁ w₂ ↔ ∀ u : List α, w₁ ++ u ∈ L ↔ w₂ ++ u ∈ L :=
  Iff.rfl

/-- `Indistinguishable L w₁ w₂` coincides with equality of Mathlib left quotients. -/
theorem indistinguishable_iff_leftQuotient_eq {L : Language α} {w₁ w₂ : List α} :
    Indistinguishable L w₁ w₂ ↔ L.leftQuotient w₁ = L.leftQuotient w₂ := by
  simp only [Indistinguishable, Language.ext_iff, Language.mem_leftQuotient]

/-- Reflexivity of `Indistinguishable`. -/
@[refl]
theorem Indistinguishable.refl (L : Language α) (w : List α) : Indistinguishable L w w :=
  fun _ ↦ Iff.rfl

/-- Symmetry of `Indistinguishable`. -/
@[symm]
theorem Indistinguishable.symm {L : Language α} {w₁ w₂ : List α}
    (h : Indistinguishable L w₁ w₂) : Indistinguishable L w₂ w₁ :=
  fun u ↦ (h u).symm

/-- Transitivity of `Indistinguishable`. -/
@[trans]
theorem Indistinguishable.trans {L : Language α} {w₁ w₂ w₃ : List α}
    (h₁₂ : Indistinguishable L w₁ w₂) (h₂₃ : Indistinguishable L w₂ w₃) :
    Indistinguishable L w₁ w₃ :=
  fun u ↦ (h₁₂ u).trans (h₂₃ u)

/-- `Indistinguishable` is a right congruence under word concatenation. -/
theorem Indistinguishable.append_right {L : Language α} {w₁ w₂ : List α}
    (h : Indistinguishable L w₁ w₂) (v : List α) :
    Indistinguishable L (w₁ ++ v) (w₂ ++ v) := by
  intro u
  simpa [List.append_assoc] using h (v ++ u)

/-- Indistinguishable words have equal membership in `L`. -/
theorem Indistinguishable.mem_iff {L : Language α} {w₁ w₂ : List α}
    (h : Indistinguishable L w₁ w₂) : w₁ ∈ L ↔ w₂ ∈ L := by
  simpa using h []

/-- In any deterministic `Cslib.LTS`, two runs from `s₀` that reach the same state `s` induce
indistinguishable words in `lts.traces s₀`. -/
theorem indistinguishable_of_deterministic_mTr_eq {State : Type*} (lts : Cslib.LTS State α)
    [lts.Deterministic] {s₀ s : State} {w₁ w₂ : List α}
    (h₁ : lts.MTr s₀ w₁ s) (h₂ : lts.MTr s₀ w₂ s) :
    Indistinguishable (lts.traces s₀) w₁ w₂ := by
  intro u
  change w₁ ++ u ∈ lts.traces s₀ ↔ w₂ ++ u ∈ lts.traces s₀
  rw [Cslib.LTS.mem_traces_iff, Cslib.LTS.mem_traces_iff]
  constructor
  · rintro ⟨s', hm⟩
    obtain ⟨m, hm₁, hmu⟩ := hm.split
    rw [← Cslib.LTS.Deterministic.eq_of_mTr h₁ hm₁] at hmu
    exact ⟨s', h₂.comp lts hmu⟩
  · rintro ⟨s', hm⟩
    obtain ⟨m, hm₂, hmu⟩ := hm.split
    rw [← Cslib.LTS.Deterministic.eq_of_mTr h₂ hm₂] at hmu
    exact ⟨s', h₁.comp lts hmu⟩

/-- A language `L` is prefix-closed (and inhabited by `[]`) if `[] ∈ L` and `u ++ v ∈ L → u ∈ L`. -/
def IsPrefixClosed (L : Language α) : Prop :=
  [] ∈ L ∧ ∀ ⦃u v : List α⦄, u ++ v ∈ L → u ∈ L

/-- Characterization of `IsPrefixClosed`. -/
theorem isPrefixClosed_iff {L : Language α} :
    IsPrefixClosed L ↔ [] ∈ L ∧ ∀ ⦃u v : List α⦄, u ++ v ∈ L → u ∈ L :=
  Iff.rfl

/-- Every `Cslib.LTS.traces s₀` specification language is non-empty and prefix-closed. -/
theorem isPrefixClosed_traces {State : Type*} (lts : Cslib.LTS State α) (s₀ : State) :
    IsPrefixClosed (lts.traces s₀) := by
  refine ⟨⟨s₀, .refl⟩, fun u v h ↦ ?_⟩
  obtain ⟨s₂, hm⟩ := h
  obtain ⟨s₁, hm₁, _⟩ := hm.split
  exact ⟨s₁, hm₁⟩

/-- A language `L` is **order-oblivious** if any two feasible words `w₁, w₂ ∈ L` that are
permutations of each other are Myhill–Nerode indistinguishable. -/
def IsOrderOblivious (L : Language α) : Prop :=
  ∀ ⦃w₁ w₂ : List α⦄, w₁ ∈ L → w₂ ∈ L → w₁.Perm w₂ → Indistinguishable L w₁ w₂

/-- Characterization of `IsOrderOblivious`. -/
theorem isOrderOblivious_iff {L : Language α} :
    IsOrderOblivious L ↔
      ∀ ⦃w₁ w₂ : List α⦄, w₁ ∈ L → w₂ ∈ L → w₁.Perm w₂ → Indistinguishable L w₁ w₂ :=
  Iff.rfl

/-- A language `L` is order-oblivious relative to a functional labeled transition system
`A : Cslib.FLTS Q α` and initial state `q₀ : Q` if any two feasible permutations `w₁, w₂ ∈ L`
reaching the same control state from `q₀` are indistinguishable. -/
def IsAutomatonOrderOblivious {Q : Type*} (A : Cslib.FLTS Q α) (q₀ : Q) (L : Language α) : Prop :=
  ∀ ⦃w₁ w₂ : List α⦄, w₁ ∈ L → w₂ ∈ L → w₁.Perm w₂ →
    A.mtr q₀ w₁ = A.mtr q₀ w₂ → Indistinguishable L w₁ w₂

/-- Characterization of `IsAutomatonOrderOblivious`. -/
theorem isAutomatonOrderOblivious_iff {Q : Type*} {A : Cslib.FLTS Q α} {q₀ : Q}
    {L : Language α} :
    IsAutomatonOrderOblivious A q₀ L ↔
      ∀ ⦃w₁ w₂ : List α⦄, w₁ ∈ L → w₂ ∈ L → w₁.Perm w₂ →
        A.mtr q₀ w₁ = A.mtr q₀ w₂ → Indistinguishable L w₁ w₂ :=
  Iff.rfl

/-- A language `L` is **`k`-order-oblivious** if there exists a finite functional labeled transition
system with `k` states and an initial state `q₀` witnessing `IsAutomatonOrderOblivious`. -/
def IsAlphaOrderOblivious (k : ℕ) (L : Language α) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (A : Cslib.FLTS Q α) (q₀ : Q),
    Fintype.card Q = k ∧ IsAutomatonOrderOblivious A q₀ L

/-- Characterization of `IsAlphaOrderOblivious`. -/
theorem isAlphaOrderOblivious_iff {k : ℕ} {L : Language α} :
    IsAlphaOrderOblivious k L ↔
      ∃ (Q : Type) (_ : Fintype Q) (A : Cslib.FLTS Q α) (q₀ : Q),
        Fintype.card Q = k ∧ IsAutomatonOrderOblivious A q₀ L :=
  Iff.rfl

/-- No language is `0`-order-oblivious because an initial state `q₀ ∈ Q` witnesses `Nonempty Q`. -/
theorem not_isAlphaOrderOblivious_zero (L : Language α) :
    ¬ IsAlphaOrderOblivious 0 L := by
  rintro ⟨Q, _, _, q₀, hcard, _⟩
  have : Nonempty Q := ⟨q₀⟩
  exact Fintype.card_ne_zero hcard

/-- Characterization of `IsAlphaOrderOblivious k L` via canonical state space `Fin k`. -/
theorem isAlphaOrderOblivious_iff_fin {k : ℕ} {L : Language α} :
    IsAlphaOrderOblivious k L ↔
      ∃ (A : Cslib.FLTS (Fin k) α) (q₀ : Fin k), IsAutomatonOrderOblivious A q₀ L := by
  constructor
  · rintro ⟨Q, _, A, q₀, hcard, hA⟩
    let e : Q ≃ Fin k := Fintype.equivFinOfCardEq hcard
    let A' : Cslib.FLTS (Fin k) α := { tr := fun q a ↦ e (A.tr (e.symm q) a) }
    have hmtr : ∀ (w : List α) (q : Q), A'.mtr (e q) w = e (A.mtr q w) := by
      intro w
      induction w with
      | nil => intro q; rfl
      | cons a w ih =>
        intro q
        change A'.mtr (A'.tr (e q) a) w = e (A.mtr (A.tr q a) w)
        simp only [A', Equiv.symm_apply_apply]
        exact ih (A.tr q a)
    refine ⟨A', e q₀, fun w₁ w₂ hw₁ hw₂ hperm heq ↦ hA hw₁ hw₂ hperm ?_⟩
    apply e.injective
    simpa [hmtr] using heq
  · rintro ⟨A, q₀, hA⟩
    exact ⟨Fin k, inferInstance, A, q₀, Fintype.card_fin k, hA⟩

/-- Construct `IsAlphaOrderOblivious k L` from any universe-polymorphic finite control-state type
`Q : Type*` with `Fintype.card Q = k`. -/
theorem IsAlphaOrderOblivious.of_fintype {Q : Type*} [Fintype Q] {k : ℕ} {L : Language α}
    (A : Cslib.FLTS Q α) (q₀ : Q) (hcard : Fintype.card Q = k)
    (hA : IsAutomatonOrderOblivious A q₀ L) : IsAlphaOrderOblivious k L := by
  rw [isAlphaOrderOblivious_iff_fin]
  let e : Q ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let A' : Cslib.FLTS (Fin k) α := { tr := fun q a ↦ e (A.tr (e.symm q) a) }
  have hmtr : ∀ (w : List α) (q : Q), A'.mtr (e q) w = e (A.mtr q w) := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a w ih =>
      intro q
      change A'.mtr (A'.tr (e q) a) w = e (A.mtr (A.tr q a) w)
      simp only [A', Equiv.symm_apply_apply]
      exact ih (A.tr q a)
  refine ⟨A', e q₀, fun w₁ w₂ hw₁ hw₂ hperm heq ↦ hA hw₁ hw₂ hperm ?_⟩
  apply e.injective
  simpa [hmtr] using heq

/-- Order-oblivious languages coincide with `1`-order-oblivious languages. -/
theorem isOrderOblivious_iff_one {L : Language α} :
    IsOrderOblivious L ↔ IsAlphaOrderOblivious 1 L := by
  rw [isAlphaOrderOblivious_iff_fin]
  constructor
  · intro h
    refine ⟨{ tr := fun _ _ ↦ 0 }, 0, fun w₁ w₂ hw₁ hw₂ hperm _ ↦ h hw₁ hw₂ hperm⟩
  · rintro ⟨A, q₀, hA⟩ w₁ w₂ hw₁ hw₂ hperm
    exact hA hw₁ hw₂ hperm (Subsingleton.elim _ _)

/-- Monotonicity of the `k`-order-oblivious hierarchy for `1 ≤ k₁ ≤ k₂`. -/
theorem IsAlphaOrderOblivious.mono {k₁ k₂ : ℕ} {L : Language α}
    (hk₁ : 1 ≤ k₁) (hle : k₁ ≤ k₂) (h : IsAlphaOrderOblivious k₁ L) :
    IsAlphaOrderOblivious k₂ L := by
  rw [isAlphaOrderOblivious_iff_fin] at h ⊢
  obtain ⟨A, q₀, hA⟩ := h
  have hk₁_pos : 0 < k₁ := hk₁
  let dflt : Fin k₁ := ⟨0, hk₁_pos⟩
  let embed (q : Fin k₁) : Fin k₂ := ⟨q.val, lt_of_lt_of_le q.isLt hle⟩
  let proj (q : Fin k₂) : Fin k₁ := if hq : q.val < k₁ then ⟨q.val, hq⟩ else dflt
  have hproj_embed : ∀ q : Fin k₁, proj (embed q) = q := by
    intro q
    simp [embed, proj, q.isLt]
  let A' : Cslib.FLTS (Fin k₂) α := { tr := fun q a ↦ embed (A.tr (proj q) a) }
  have hmtr : ∀ (w : List α) (q : Fin k₁), A'.mtr (embed q) w = embed (A.mtr q w) := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a w ih =>
      intro q
      change A'.mtr (A'.tr (embed q) a) w = embed (A.mtr (A.tr q a) w)
      simp only [A', hproj_embed]
      exact ih (A.tr q a)
  refine ⟨A', embed q₀, fun w₁ w₂ hw₁ hw₂ hperm heq ↦ hA hw₁ hw₂ hperm ?_⟩
  have hinj : Function.Injective embed := fun x y hxy ↦ Fin.ext (Fin.mk.inj hxy)
  apply hinj
  simpa [hmtr] using heq

end OrderOblivious

section LayeredRepDP

variable {V Q α : Type*}

/-- A finite labeled directed graph `G` is a **graded permutation-consistent DAG** from `s` if
`grade s = 0`, every edge increases `grade` by `1`, and any two walks from `s` to the same vertex
`u` induce labels that are permutations of each other. -/
structure IsGradedPermDAG (G : FinLabeledDigraph V α) (grade : V → ℕ) (s : V) : Prop where
  /-- Source vertex belongs to `G.nodes`. -/
  source_mem : s ∈ G.nodes
  /-- Source vertex has grade `0`. -/
  grade_source : grade s = 0
  /-- Every edge `(u, a, v)` increments `grade` by `1`. -/
  grade_edge : ∀ e ∈ G.edges, grade e.2.2 = grade e.1 + 1
  /-- Walks from `s` to `u` have permutation-equivalent labels. -/
  walk_perm : ∀ {u : V} (π₁ π₂ : G.Walk s u), π₁.label.Perm π₂.label

/-- In a graded DAG from `s`, every walk `π : G.Walk u v` satisfies
`grade v = grade u + π.length`. -/
theorem IsGradedPermDAG.grade_walk {G : FinLabeledDigraph V α} {grade : V → ℕ} {s u v : V}
    (hG : IsGradedPermDAG G grade s) (π : G.Walk u v) :
    grade v = grade u + π.length := by
  induction π with
  | nil _ => simp [FinLabeledDigraph.Walk.length]
  | cons he _ ih =>
    have hedge := hG.grade_edge _ he
    dsimp only at hedge
    rw [ih, hedge, FinLabeledDigraph.Walk.length]
    omega

/-- Single relaxation step along one edge `e = (u, a, v)` and control state `q`. -/
def relaxEdgeState [DecidableEq V] [DecidableEq Q]
    (A : Cslib.FLTS Q α) (memL : List α → Bool) (grade : V → ℕ) (lvl : ℕ)
    (rep : V → Q → Option (List α)) (e : V × α × V) (q : Q) (w : V) (r : Q) :
    Option (List α) :=
  if grade e.1 = lvl then
    match rep e.1 q with
    | none => rep w r
    | some τ =>
      if (rep e.2.2 (A.tr q e.2.1)).isNone && memL (τ ++ [e.2.1]) then
        if w = e.2.2 ∧ r = A.tr q e.2.1 then some (τ ++ [e.2.1]) else rep w r
      else
        rep w r
  else
    rep w r

/-- Existing table entries are never overwritten or erased by `relaxEdgeState`. -/
theorem relaxEdgeState_eq_of_isSome [DecidableEq V] [DecidableEq Q]
    (A : Cslib.FLTS Q α) (memL : List α → Bool) (grade : V → ℕ) (lvl : ℕ)
    (rep : V → Q → Option (List α)) (e : V × α × V) (q : Q) {w : V} {r : Q} {τ₀ : List α}
    (h : rep w r = some τ₀) :
    relaxEdgeState A memL grade lvl rep e q w r = some τ₀ := by
  unfold relaxEdgeState
  by_cases hlvl : grade e.1 = lvl
  · simp only [hlvl, ↓reduceIte]
    cases hrep : rep e.1 q with
    | none => exact h
    | some τ =>
      dsimp only
      by_cases hcond : ((rep e.2.2 (A.tr q e.2.1)).isNone && memL (τ ++ [e.2.1])) = true
      · simp only [hcond, ↓reduceIte]
        by_cases hwr : w = e.2.2 ∧ r = A.tr q e.2.1
        · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hcond
          rcases hwr with ⟨hw, hr⟩
          subst hw hr
          rw [hcond.1] at h
          cases h
        · simp [hwr, h]
      · simp [hcond, h]
  · simp [hlvl, h]

/-- If `grade e.1 = lvl`, `rep e.1 q = some τ`, and `memL (τ ++ [e.2.1]) = true`, then after
`relaxEdgeState` the target entry `(e.2.2, A.tr q e.2.1)` is populated (`isSome`). -/
theorem isSome_relaxEdgeState_target [DecidableEq V] [DecidableEq Q]
    (A : Cslib.FLTS Q α) (memL : List α → Bool) (grade : V → ℕ) (lvl : ℕ)
    (rep : V → Q → Option (List α)) (e : V × α × V) (q : Q) {τ : List α}
    (hlvl : grade e.1 = lvl) (hrep : rep e.1 q = some τ)
    (hmem : memL (τ ++ [e.2.1]) = true) :
    (relaxEdgeState A memL grade lvl rep e q e.2.2 (A.tr q e.2.1)).isSome = true := by
  cases hcur : rep e.2.2 (A.tr q e.2.1) with
  | some τ₀ =>
    rw [relaxEdgeState_eq_of_isSome A memL grade lvl rep e q hcur]
    rfl
  | none =>
    simp [relaxEdgeState, hlvl, hrep, hcur, hmem]

/-- Any newly populated entry in `relaxEdgeState` satisfies the walk, membership, and state
invariants. -/
theorem relaxEdgeState_sound [DecidableEq V] [DecidableEq Q]
    {G : FinLabeledDigraph V α} {A : Cslib.FLTS Q α} {q₀ : Q} {memL : List α → Bool}
    {L : Language α} (hmemL : ∀ w, memL w = true ↔ w ∈ L)
    {grade : V → ℕ} {s : V} {lvl : ℕ} {rep : V → Q → Option (List α)}
    {e : V × α × V} (he : e ∈ G.edges) {q : Q}
    (hinv : ∀ w r τ, rep w r = some τ →
      τ ∈ L ∧ A.mtr q₀ τ = r ∧ ∃ π : G.Walk s w, π.label = τ) :
    ∀ w r τ', relaxEdgeState A memL grade lvl rep e q w r = some τ' →
      τ' ∈ L ∧ A.mtr q₀ τ' = r ∧ ∃ π : G.Walk s w, π.label = τ' := by
  intro w r τ' hnew
  unfold relaxEdgeState at hnew
  by_cases hlvl : grade e.1 = lvl
  · simp only [hlvl, ↓reduceIte] at hnew
    cases hrep : rep e.1 q with
    | none =>
      simp only [hrep] at hnew
      exact hinv w r τ' hnew
    | some τ =>
      simp only [hrep] at hnew
      by_cases hcond : ((rep e.2.2 (A.tr q e.2.1)).isNone && memL (τ ++ [e.2.1])) = true
      · simp only [hcond, ↓reduceIte] at hnew
        by_cases hwr : w = e.2.2 ∧ r = A.tr q e.2.1
        · simp only [hwr, and_self, ↓reduceIte, Option.some.injEq] at hnew
          rcases hwr with ⟨hw, hr⟩
          subst hw hr hnew
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨_, hmtr, π, rfl⟩ := hinv e.1 q τ hrep
          refine ⟨(hmemL _).mp hcond.2, ?_, π.snoc he, by simp⟩
          rw [Cslib.FLTS.mtr_concat_eq, hmtr]
        · simp only [hwr, ↓reduceIte] at hnew
          exact hinv w r τ' hnew
      · simp only [hcond] at hnew
        exact hinv w r τ' hnew
  · simp only [hlvl, ↓reduceIte] at hnew
    exact hinv w r τ' hnew

/-- Process all `(edge, state)` pairs at grade `lvl`. -/
noncomputable def repLayer [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (G : FinLabeledDigraph V α) (A : Cslib.FLTS Q α) (memL : List α → Bool)
    (grade : V → ℕ) (lvl : ℕ) (rep : V → Q → Option (List α)) :
    V → Q → Option (List α) :=
  (G.edges ×ˢ (Finset.univ : Finset Q)).toList.foldl
    (fun acc eq ↦ relaxEdgeState A memL grade lvl acc eq.1 eq.2) rep

/-- Initial representative table: `some []` at `(s, q₀)` and `none` elsewhere. -/
def initRepTable [DecidableEq V] [DecidableEq Q] (q₀ : Q) (s : V) :
    V → Q → Option (List α) :=
  fun u q ↦ if u = s ∧ q = q₀ then some [] else none

/-- Layered representative table after `k` layers (`0, …, k - 1`). -/
noncomputable def repTable [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (G : FinLabeledDigraph V α) (A : Cslib.FLTS Q α) (q₀ : Q) (memL : List α → Bool)
    (grade : V → ℕ) (s : V) : ℕ → V → Q → Option (List α)
  | 0 => initRepTable q₀ s
  | k + 1 => repLayer G A memL grade k (repTable G A q₀ memL grade s k)

/-- Boolean decision procedure checking whether any control state `q` reaches `t` after `D`
layers. -/
noncomputable def repReach [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (G : FinLabeledDigraph V α) (A : Cslib.FLTS Q α) (q₀ : Q) (memL : List α → Bool)
    (grade : V → ℕ) (s t : V) (D : ℕ) : Bool :=
  (Finset.univ : Finset Q).toList.any fun q ↦ (repTable G A q₀ memL grade s D t q).isSome

private theorem foldl_relaxEdgeState_eq_of_isSome [DecidableEq V] [DecidableEq Q]
    (A : Cslib.FLTS Q α) (memL : List α → Bool) (grade : V → ℕ) (lvl : ℕ)
    (pairs : List ((V × α × V) × Q)) (rep : V → Q → Option (List α))
    {w : V} {r : Q} {τ₀ : List α} (h : rep w r = some τ₀) :
    pairs.foldl (fun acc eq ↦ relaxEdgeState A memL grade lvl acc eq.1 eq.2) rep w r = some τ₀ := by
  induction pairs generalizing rep with
  | nil => exact h
  | cons eq rest ih =>
    exact ih _ (relaxEdgeState_eq_of_isSome A memL grade lvl rep eq.1 eq.2 h)

private theorem repLayer_eq_of_isSome [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (G : FinLabeledDigraph V α) (A : Cslib.FLTS Q α) (memL : List α → Bool)
    (grade : V → ℕ) (lvl : ℕ) (rep : V → Q → Option (List α)) {w : V} {r : Q} {τ₀ : List α}
    (h : rep w r = some τ₀) :
    repLayer G A memL grade lvl rep w r = some τ₀ :=
  foldl_relaxEdgeState_eq_of_isSome A memL grade lvl _ rep h

private theorem repLayer_sound [DecidableEq V] [Fintype Q] [DecidableEq Q]
    {G : FinLabeledDigraph V α} {A : Cslib.FLTS Q α} {q₀ : Q} {memL : List α → Bool}
    {L : Language α} (hmemL : ∀ w, memL w = true ↔ w ∈ L)
    {grade : V → ℕ} {s : V} {lvl : ℕ} {rep : V → Q → Option (List α)}
    (hinv : ∀ w r τ, rep w r = some τ →
      τ ∈ L ∧ A.mtr q₀ τ = r ∧ ∃ π : G.Walk s w, π.label = τ) :
    ∀ w r τ', repLayer G A memL grade lvl rep w r = some τ' →
      τ' ∈ L ∧ A.mtr q₀ τ' = r ∧ ∃ π : G.Walk s w, π.label = τ' := by
  unfold repLayer
  have hmem_edges : ∀ eq ∈ (G.edges ×ˢ (Finset.univ : Finset Q)).toList, eq.1 ∈ G.edges := by
    intro eq heq
    exact (Finset.mem_product.mp (Finset.mem_toList.mp heq)).1
  generalize (G.edges ×ˢ (Finset.univ : Finset Q)).toList = pairs at hmem_edges ⊢
  induction pairs generalizing rep with
  | nil => exact hinv
  | cons eq rest ih =>
    exact ih (relaxEdgeState_sound hmemL (hmem_edges eq List.mem_cons_self) hinv)
      (fun x hx ↦ hmem_edges x (List.mem_cons_of_mem _ hx))

private theorem isSome_repLayer_of_edge [DecidableEq V] [Fintype Q] [DecidableEq Q]
    {G : FinLabeledDigraph V α} {A : Cslib.FLTS Q α} {memL : List α → Bool}
    {grade : V → ℕ} {lvl : ℕ} {rep : V → Q → Option (List α)}
    {e : V × α × V} (he : e ∈ G.edges) {q : Q} {τ : List α}
    (hlvl : grade e.1 = lvl) (hrep : rep e.1 q = some τ)
    (hmem : memL (τ ++ [e.2.1]) = true) :
    (repLayer G A memL grade lvl rep e.2.2 (A.tr q e.2.1)).isSome = true := by
  unfold repLayer
  have hpair : (e, q) ∈ (G.edges ×ˢ (Finset.univ : Finset Q)).toList :=
    Finset.mem_toList.mpr (Finset.mem_product.mpr ⟨he, Finset.mem_univ q⟩)
  generalize (G.edges ×ˢ (Finset.univ : Finset Q)).toList = pairs at hpair ⊢
  induction pairs generalizing rep with
  | nil => cases hpair
  | cons eq rest ih =>
    rcases List.mem_cons.mp hpair with rfl | hrest
    · have his : (relaxEdgeState A memL grade lvl rep e q e.2.2 (A.tr q e.2.1)).isSome = true :=
        isSome_relaxEdgeState_target A memL grade lvl rep e q hlvl hrep hmem
      obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp his
      have hfinal :=
        foldl_relaxEdgeState_eq_of_isSome A memL grade lvl rest
          (relaxEdgeState A memL grade lvl rep e q) hτ'
      rw [List.foldl_cons, hfinal]
      rfl
    · exact ih (relaxEdgeState_eq_of_isSome A memL grade lvl rep eq.1 eq.2 hrep) hrest

/-- Soundness of `repTable`: every recorded representative `τ` at `(u, q)` belongs to `L`, reaches
control state `q` from `q₀` in `A`, and labels a walk `s ⇝ u` in `G`. -/
theorem repTable_sound [DecidableEq V] [Fintype Q] [DecidableEq Q]
    {G : FinLabeledDigraph V α} {A : Cslib.FLTS Q α} {q₀ : Q} {memL : List α → Bool}
    {L : Language α} (hmemL : ∀ w, memL w = true ↔ w ∈ L) (hpref : IsPrefixClosed L)
    {grade : V → ℕ} {s : V} (hs : s ∈ G.nodes) (D : ℕ) :
    ∀ w r τ, repTable G A q₀ memL grade s D w r = some τ →
      τ ∈ L ∧ A.mtr q₀ τ = r ∧ ∃ π : G.Walk s w, π.label = τ := by
  induction D with
  | zero =>
    intro w r τ h
    simp only [repTable, initRepTable] at h
    split_ifs at h with hwr
    rcases hwr with ⟨hw, hr⟩
    subst hw hr
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hpref.1, rfl, .nil hs, rfl⟩
  | succ k ih =>
    exact repLayer_sound hmemL ih

/-- Completeness of `repTable` on any graded permutation-consistent DAG for a prefix-closed
`(A, q₀)`-order-oblivious language `L`. -/
theorem repTable_complete [DecidableEq V] [Fintype Q] [DecidableEq Q]
    {G : FinLabeledDigraph V α} {A : Cslib.FLTS Q α} {q₀ : Q} {memL : List α → Bool}
    {L : Language α} (hmemL : ∀ w, memL w = true ↔ w ∈ L) (hpref : IsPrefixClosed L)
    (hoodt : IsAutomatonOrderOblivious A q₀ L) {grade : V → ℕ} {s : V}
    (hG : IsGradedPermDAG G grade s) (D : ℕ) :
    ∀ {u : V} (π : G.Walk s u), π.length ≤ D → π.label ∈ L →
      (repTable G A q₀ memL grade s D u (A.mtr q₀ π.label)).isSome = true := by
  induction D with
  | zero =>
    intro u π hlen _
    cases π with
    | nil _ =>
      simp [repTable, initRepTable]
    | cons _ _ =>
      simp [FinLabeledDigraph.Walk.length] at hlen
  | succ k ih =>
    intro u π hlen hL
    rcases Nat.lt_or_eq_of_le hlen with hlt | heq
    · have hprev := ih π (Nat.le_of_lt_succ hlt) hL
      obtain ⟨τ₀, hτ₀⟩ := Option.isSome_iff_exists.mp hprev
      rw [repTable, repLayer_eq_of_isSome G A memL grade k _ hτ₀]
      rfl
    · rcases π.eq_nil_or_snoc with ⟨_, hnil⟩ | ⟨v, a, π₀, he, hlbl⟩
      · simp [← π.length_label, hnil] at heq
      · have hlen₀ : π₀.length = k := by
          have h1 : π.label.length = k + 1 := by rw [π.length_label, heq]
          rw [hlbl, List.length_append, List.length_singleton, π₀.length_label] at h1
          omega
        have hL₀ : π₀.label ∈ L := hpref.2 (hlbl ▸ hL)
        have his₀ := ih π₀ (le_of_eq hlen₀) hL₀
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp his₀
        obtain ⟨hτL, hτq, π_rep, rfl⟩ :=
          repTable_sound hmemL hpref hG.source_mem k v (A.mtr q₀ π₀.label) τ hτ
        have hperm : π_rep.label.Perm π₀.label := hG.walk_perm π_rep π₀
        have hind : Indistinguishable L π_rep.label π₀.label :=
          hoodt hτL hL₀ hperm hτq
        have hτ_ext : π_rep.label ++ [a] ∈ L := (hind [a]).mpr (hlbl ▸ hL)
        have hgrade_v : grade v = k := by
          have hg := hG.grade_walk π₀
          rw [hG.grade_source, zero_add, hlen₀] at hg
          exact hg
        have htr_q : A.mtr q₀ π.label = A.tr (A.mtr q₀ π₀.label) a := by
          rw [hlbl, Cslib.FLTS.mtr_concat_eq]
        rw [htr_q, repTable]
        exact isSome_repLayer_of_edge (e := (v, a, u)) he hgrade_v hτ ((hmemL _).mpr hτ_ext)

/-- **Representative-pruning reachability theorem**: on a graded permutation-consistent DAG `G` from
`s`, for any prefix-closed `(A, q₀)`-order-oblivious language `L` and depth bound `grade t ≤ D`,
`repReach G A q₀ memL grade s t D = true` iff `LanguageReachable G L s t`. -/
theorem repReach_eq_true_iff [DecidableEq V] [Fintype Q] [DecidableEq Q]
    {G : FinLabeledDigraph V α} {A : Cslib.FLTS Q α} {q₀ : Q} {memL : List α → Bool}
    {L : Language α} (hmemL : ∀ w, memL w = true ↔ w ∈ L) (hpref : IsPrefixClosed L)
    (hoodt : IsAutomatonOrderOblivious A q₀ L) {grade : V → ℕ} {s t : V}
    (hG : IsGradedPermDAG G grade s) {D : ℕ} (hD : grade t ≤ D) :
    repReach G A q₀ memL grade s t D = true ↔ LanguageReachable G L s t := by
  simp only [repReach, List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hq
    obtain ⟨hτL, _, π, rfl⟩ := repTable_sound hmemL hpref hG.source_mem D t q τ hτ
    exact ⟨π, hτL⟩
  · rintro ⟨π, hπL⟩
    have hlen : π.length ≤ D := by
      have hg := hG.grade_walk π
      rw [hG.grade_source, zero_add] at hg
      omega
    exact ⟨A.mtr q₀ π.label, repTable_complete hmemL hpref hoodt hG D π hlen hπL⟩

end LayeredRepDP

section CNFReachability

variable {V α : Type*}

/-- Non-associative binary production multiplication `X₁ ⊗ X₂` for a Chomsky Normal Form grammar
`C`: all nonterminals `A` with a rule `A → B₁ B₂` where `B₁ ∈ X₁` and `B₂ ∈ X₂`. -/
def cnfRuleMul (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    (X₁ X₂ : Finset C.NT) : Finset C.NT :=
  (C.rules.filterMap fun r ↦
    match r with
    | .leaf _ _ => none
    | .node A B₁ B₂ => if B₁ ∈ X₁ ∧ B₂ ∈ X₂ then some A else none).toFinset

/-- Membership in `cnfRuleMul C X₁ X₂` holds iff there exist `B₁ ∈ X₁` and `B₂ ∈ X₂` with
`.node A B₁ B₂ ∈ C.rules`. -/
@[simp]
theorem mem_cnfRuleMul (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    {X₁ X₂ : Finset C.NT} {A : C.NT} :
    A ∈ cnfRuleMul C X₁ X₂ ↔
      ∃ B₁ ∈ X₁, ∃ B₂ ∈ X₂, .node A B₁ B₂ ∈ C.rules := by
  simp only [cnfRuleMul, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, hmatch⟩
    cases r with
    | leaf _ _ => simp at hmatch
    | node A' B₁ B₂ =>
      dsimp only at hmatch
      split_ifs at hmatch with hcond
      simp only [Option.some.injEq] at hmatch
      subst hmatch
      exact ⟨B₁, hcond.1, B₂, hcond.2, hr⟩
  · rintro ⟨B₁, hB₁, B₂, hB₂, hr⟩
    exact ⟨.node A B₁ B₂, hr, by simp [hB₁, hB₂]⟩

/-- One-step terminal recognition matrix `M(u, v)` of a labeled graph `G` with respect to `C`. -/
def oneStepMatrix [DecidableEq V] [DecidableEq α]
    (G : FinLabeledDigraph V α) (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    (u v : V) : Finset C.NT :=
  (C.rules.filterMap fun r ↦
    match r with
    | .node _ _ _ => none
    | .leaf A a => if (u, a, v) ∈ G.edges then some A else none).toFinset

/-- Membership in `oneStepMatrix G C u v` holds iff there is an edge `(u, a, v) ∈ G.edges` and a
terminal rule `.leaf A a ∈ C.rules`. -/
@[simp]
theorem mem_oneStepMatrix [DecidableEq V] [DecidableEq α]
    {G : FinLabeledDigraph V α} (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    {u v : V} {A : C.NT} :
    A ∈ oneStepMatrix G C u v ↔ ∃ a : α, (u, a, v) ∈ G.edges ∧ .leaf A a ∈ C.rules := by
  simp only [oneStepMatrix, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, hmatch⟩
    cases r with
    | node _ _ _ => simp at hmatch
    | leaf A' a =>
      dsimp only at hmatch
      split_ifs at hmatch with he
      simp only [Option.some.injEq] at hmatch
      subst hmatch
      exact ⟨a, he, hr⟩
  · rintro ⟨a, he, hr⟩
    exact ⟨.leaf A a, hr, by simp [he]⟩

/-- Non-associative grammar matrix multiplication
`(M₁ ⊗ M₂)(u, w) = ⋃_{v ∈ G.nodes} M₁(u,v) ⊗ M₂(v,w)`. -/
def cnfMatMul (G : FinLabeledDigraph V α)
    (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    (M₁ M₂ : V → V → Finset C.NT) (u w : V) : Finset C.NT :=
  G.nodes.biUnion fun v ↦ cnfRuleMul C (M₁ u v) (M₂ v w)

/-- Membership in `(cnfMatMul G C M₁ M₂) u w`. -/
@[simp]
theorem mem_cnfMatMul {G : FinLabeledDigraph V α}
    (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    {M₁ M₂ : V → V → Finset C.NT} {u w : V} {A : C.NT} :
    A ∈ cnfMatMul G C M₁ M₂ u w ↔
      ∃ v ∈ G.nodes, ∃ B₁ ∈ M₁ u v, ∃ B₂ ∈ M₂ v w, .node A B₁ B₂ ∈ C.rules := by
  simp only [cnfMatMul, Finset.mem_biUnion, mem_cnfRuleMul C]

/-- Dynamic-programming CYK recognition table on an acyclic graph `G` strictly ordered by
`grade : V → ℕ` (`∀ e ∈ G.edges, grade e.1 < grade e.2.2`), indexed by span bound `D`. -/
def cykDagTable [DecidableEq V] [DecidableEq α]
    (G : FinLabeledDigraph V α) (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    (grade : V → ℕ) : ℕ → V → V → Finset C.NT
  | 0, u, v =>
    if u ∈ G.nodes ∧ u = v ∧ C.nilRule = true then {C.initial} else ∅
  | d + 1, u, v =>
    if grade u ≤ grade v ∧ grade v - grade u = d + 1 then
      oneStepMatrix G C u v ∪
        G.nodes.biUnion fun m ↦
          if grade u < grade m ∧ grade m < grade v then
            cnfRuleMul C (cykDagTable G C grade d u m) (cykDagTable G C grade d m v)
          else
            ∅
    else
      cykDagTable G C grade d u v

/-- Boolean decision procedure for CNF language reachability on an acyclic graph `G` with
`grade : V → ℕ`. -/
def cykDagReach [DecidableEq V] [DecidableEq α]
    (G : FinLabeledDigraph V α) (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    (grade : V → ℕ) (s t : V) : Bool :=
  decide (C.initial ∈ cykDagTable G C grade (grade t - grade s) s t)

/-- Monotonicity/stability of `cykDagTable` once `grade v - grade u ≤ d`. -/
theorem cykDagTable_eq_of_span_le [DecidableEq V] [DecidableEq α]
    (G : FinLabeledDigraph V α) (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    (grade : V → ℕ) {d D : ℕ} {u v : V}
    (hspan : grade v - grade u ≤ d) (hdD : d ≤ D) :
    cykDagTable G C grade D u v = cykDagTable G C grade d u v := by
  induction D with
  | zero =>
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hdD
    subst hd0
    rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hdD with rfl | hlt
    · rfl
    · have hk : d ≤ k := Nat.le_of_lt_succ hlt
      have hne : ¬ (grade u ≤ grade v ∧ grade v - grade u = k + 1) := by omega
      simp only [cykDagTable, hne, ↓reduceIte]
      exact ih hk

/-- In a strictly `grade`-increasing graph `G`, every non-empty walk `π : G.Walk u v`
(`π.label ≠ []`) satisfies `grade u < grade v`, and every walk satisfies `grade u ≤ grade v`. -/
theorem grade_le_and_lt_of_walk {G : FinLabeledDigraph V α} {grade : V → ℕ}
    (hstrict : ∀ e ∈ G.edges, grade e.1 < grade e.2.2) {u v : V} (π : G.Walk u v) :
    grade u ≤ grade v ∧ (π.label ≠ [] → grade u < grade v) := by
  induction π with
  | nil _ => simp
  | cons he _ ih =>
    have hlt := hstrict _ he
    exact ⟨le_of_lt (lt_of_lt_of_le hlt ih.1), fun _ ↦ lt_of_lt_of_le hlt ih.1⟩

/-- **Exact CYK-on-DAG characterization**: in any finite labeled graph `G` strictly ordered by
`grade : V → ℕ` (`∀ e ∈ G.edges, grade e.1 < grade e.2.2`), for every `D` with
`grade v - grade u ≤ D` and every nonterminal `A : C.NT`, `A ∈ cykDagTable G C grade D u v` iff
there exists a walk `π : G.Walk u v` such that `C.toCFG` derives `π.label` from `A`. -/
theorem mem_cykDagTable_iff [DecidableEq V] [DecidableEq α]
    {G : FinLabeledDigraph V α} (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    {grade : V → ℕ} (hstrict : ∀ e ∈ G.edges, grade e.1 < grade e.2.2)
    {D : ℕ} {u v : V} (hD : grade v - grade u ≤ D) {A : C.NT} :
    A ∈ cykDagTable G C grade D u v ↔
      ∃ π : G.Walk u v, C.toCFG.Derives [.nonterminal A] (π.label.map .terminal) := by
  induction D generalizing u v A with
  | zero =>
    constructor
    · intro hmem
      simp only [cykDagTable] at hmem
      split_ifs at hmem with h0
      · rcases h0 with ⟨hu, huv, hnil⟩
        subst huv
        simp only [Finset.mem_singleton] at hmem
        subst hmem
        exact ⟨.nil hu, C.derives_nil_iff.mpr ⟨hnil, rfl⟩⟩
      · exact absurd hmem (Finset.notMem_empty _)
    · rintro ⟨π, hder⟩
      obtain ⟨_, hne_lt⟩ := grade_le_and_lt_of_walk hstrict π
      have hlbl_nil : π.label = [] := by
        by_contra hne
        have hlt := hne_lt hne
        omega
      cases π with
      | nil hu =>
        rw [FinLabeledDigraph.Walk.label_nil, List.map_nil, C.derives_nil_iff] at hder
        simp [cykDagTable, hu, hder.1, hder.2]
      | cons _ _ => simp at hlbl_nil
  | succ d ih =>
    rcases lt_or_eq_of_le hD with hlt | hspan_eq
    · have hle_d : grade v - grade u ≤ d := Nat.le_of_lt_succ hlt
      rw [cykDagTable_eq_of_span_le G C grade hle_d (Nat.le_succ d)]
      exact ih hle_d
    · by_cases huv_le : grade u ≤ grade v
      · have hcond : grade u ≤ grade v ∧ grade v - grade u = d + 1 := ⟨huv_le, hspan_eq⟩
        simp only [cykDagTable, hcond, and_self, ↓reduceIte, Finset.mem_union,
          mem_oneStepMatrix C, Finset.mem_biUnion]
        constructor
        · rintro (⟨a, he, hleaf⟩ | ⟨m, _, hsplit⟩)
          · refine ⟨FinLabeledDigraph.Walk.single he, ?_⟩
            rw [FinLabeledDigraph.Walk.label_single]
            exact (C.derives_iff_of_ne_nil (by simp)).mpr (Or.inl ⟨a, rfl, hleaf⟩)
          · split_ifs at hsplit with hlt_m
            · obtain ⟨B₁, hB₁, B₂, hB₂, hnode⟩ := (mem_cnfRuleMul C).mp hsplit
              obtain ⟨π₁, hder₁⟩ := (ih (u := u) (v := m) (by omega)).mp hB₁
              obtain ⟨π₂, hder₂⟩ := (ih (u := m) (v := v) (by omega)).mp hB₂
              refine ⟨π₁.append π₂, ?_⟩
              rw [FinLabeledDigraph.Walk.label_append, List.map_append]
              have hr : (Cslib.ChomskyNormalFormRule.node (T := α) A B₁ B₂).toContextFreeRule ∈
                  C.toCFG.rules := C.mem_toCFG_rules.mpr (Or.inl ⟨_, hnode, rfl⟩)
              have hprod : C.toCFG.Produces [.nonterminal A] [.nonterminal B₁, .nonterminal B₂] :=
                ContextFreeGrammar.produces_nonterminal_iff.mpr ⟨_, hr, rfl, rfl⟩
              have happ : C.toCFG.Derives [.nonterminal B₁, .nonterminal B₂]
                  (π₁.label.map .terminal ++ π₂.label.map .terminal) := hder₁.append hder₂
              exact hprod.trans_derives happ
            · exact absurd hsplit (Finset.notMem_empty _)
        · rintro ⟨π, hder⟩
          have hne : π.label ≠ [] := by
            intro hnil
            cases π with
            | nil _ => omega
            | cons _ _ => simp at hnil
          rcases (C.derives_iff_of_ne_nil hne).mp hder with
            ⟨a, hlbl_a, hleaf⟩ | ⟨B₁, B₂, w₁, w₂, hnode, hw₁, hw₂, hlbl_app, hder₁, hder₂⟩
          · cases π with
            | nil _ => simp at hlbl_a
            | @cons _ _ _ b he rest =>
              simp only [FinLabeledDigraph.Walk.label_cons, List.cons.injEq] at hlbl_a
              rcases hlbl_a with ⟨hba, hrest_nil⟩
              rw [hba] at he
              cases rest with
              | nil _ => exact Or.inl ⟨a, he, hleaf⟩
              | cons _ _ => simp at hrest_nil
          · obtain ⟨m, π₁, π₂, hπ₁, hπ₂⟩ := π.split_of_label_append hlbl_app
            have hm_mem : m ∈ G.nodes := π₁.target_mem
            have hlt₁ : grade u < grade m :=
              (grade_le_and_lt_of_walk hstrict π₁).2 (hπ₁ ▸ hw₁)
            have hlt₂ : grade m < grade v :=
              (grade_le_and_lt_of_walk hstrict π₂).2 (hπ₂ ▸ hw₂)
            have hB₁_mem : B₁ ∈ cykDagTable G C grade d u m :=
              (ih (by omega)).mpr ⟨π₁, hπ₁ ▸ hder₁⟩
            have hB₂_mem : B₂ ∈ cykDagTable G C grade d m v :=
              (ih (by omega)).mpr ⟨π₂, hπ₂ ▸ hder₂⟩
            refine Or.inr ⟨m, hm_mem, ?_⟩
            simp only [hlt₁, hlt₂, and_self, ↓reduceIte]
            exact (mem_cnfRuleMul C).mpr ⟨B₁, hB₁_mem, B₂, hB₂_mem, hnode⟩
      · exfalso
        omega

/-- **CNF CYK-on-DAG reachability theorem**: on any finite labeled graph `G` strictly ordered by
`grade : V → ℕ`, `cykDagReach G C grade s t =
  true` iff `LanguageReachable G C.toCFG.language s t`. -/
theorem cykDagReach_eq_true_iff [DecidableEq V] [DecidableEq α]
    {G : FinLabeledDigraph V α} (C : Cslib.ChomskyNormalFormGrammar α) [DecidableEq C.NT]
    {grade : V → ℕ} (hstrict : ∀ e ∈ G.edges, grade e.1 < grade e.2.2) (s t : V) :
    cykDagReach G C grade s t = true ↔ LanguageReachable G C.toCFG.language s t := by
  simp only [cykDagReach, decide_eq_true_eq, LanguageReachable,
    ContextFreeGrammar.mem_language_iff]
  exact mem_cykDagTable_iff C hstrict le_rfl

-- Non-vacuity witness: a 2-edge graph `0 --a--> 1 --b--> 2` recognized by
-- `S -> A B, A -> a, B -> b`.
example :
    let G : FinLabeledDigraph ℕ Bool :=
      { nodes := {0, 1, 2}
        edges := {(0, true, 1), (1, false, 2)}
        source_mem := by decide
        target_mem := by decide }
    let C : Cslib.ChomskyNormalFormGrammar Bool :=
      { NT := Fin 3
        initial := 0
        rules := [.node 0 1 2, .leaf 1 true, .leaf 2 false]
        nilRule := false
        initial_notMem_output := by simp }
    cykDagReach G C id 0 2 = true := by
  intro G C
  rw [cykDagReach_eq_true_iff (G := G) (C := C) (grade := id) (by decide) 0 2]
  have he1 : (0, true, 1) ∈ G.edges := by decide
  have he2 : (1, false, 2) ∈ G.edges := by decide
  have hn2 : (2 : ℕ) ∈ G.nodes := by decide
  refine ⟨.cons he1 (.cons he2 (.nil hn2)), ?_⟩
  rw [ContextFreeGrammar.mem_language_iff]
  simp only [FinLabeledDigraph.Walk.label_cons, FinLabeledDigraph.Walk.label_nil]
  have hnode : (Cslib.ChomskyNormalFormRule.node (T := Bool) (0 : Fin 3) 1 2) ∈ C.rules := by
    simp [C]
  have hleaf1 : (Cslib.ChomskyNormalFormRule.leaf (N := Fin 3) 1 true) ∈ C.rules := by
    simp [C]
  have hleaf2 : (Cslib.ChomskyNormalFormRule.leaf (N := Fin 3) 2 false) ∈ C.rules := by
    simp [C]
  have hr0 : (Cslib.ChomskyNormalFormRule.node (T := Bool) (0 : Fin 3) 1 2).toContextFreeRule ∈
      C.toCFG.rules := C.mem_toCFG_rules.mpr (Or.inl ⟨_, hnode, rfl⟩)
  have hp0 : C.toCFG.Produces [.nonterminal (0 : Fin 3)]
      [.nonterminal (1 : Fin 3), .nonterminal (2 : Fin 3)] :=
    ContextFreeGrammar.produces_nonterminal_iff.mpr ⟨_, hr0, rfl, rfl⟩
  have hd1 : C.toCFG.Derives [.nonterminal (1 : Fin 3)] [.terminal true] :=
    (C.derives_iff_of_ne_nil (w := [true]) (by simp)).mpr (Or.inl ⟨true, rfl, hleaf1⟩)
  have hd2 : C.toCFG.Derives [.nonterminal (2 : Fin 3)] [.terminal false] :=
    (C.derives_iff_of_ne_nil (w := [false]) (by simp)).mpr (Or.inl ⟨false, rfl, hleaf2⟩)
  have happ : C.toCFG.Derives [.nonterminal (1 : Fin 3), .nonterminal (2 : Fin 3)]
      ([.terminal true] ++ [.terminal false]) := hd1.append hd2
  exact hp0.trans_derives happ

end CNFReachability

end CslibFrontier.Computability.Languages
