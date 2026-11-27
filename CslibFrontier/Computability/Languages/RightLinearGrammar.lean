/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.EpsilonNFA
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Shrink
import Mathlib.Data.List.ReduceOption
import Mathlib.Tactic.Ring

/-!
# Right-Linear Grammars and Descriptional Resource Bounds

This module develops right-linear grammars, their embedding into Mathlib's `ContextFreeGrammar`,
nonterminal cut-points across bounded intervals, their two-way equivalence with finite-state
acceptors over finite alphabets, and descriptional complexity bounds by nonterminal count
(`RL_n^V`), production-rule count (`RL_n^P`), and deterministic state count (`REG_n^Z`), including
nonterminal halving (`RL_{2n}^P ⊆ RL_n^V`) and exponential word-growth bounds.

## Main definitions

* `CslibFrontier.Computability.Languages.RightLinearRule`,
  `CslibFrontier.Computability.Languages.RightLinearGrammar`: right-linear production rules and
  grammars, together with `toContextFreeGrammar`, `Reaches`, `Generates`, `language`, `maxRuleLen`,
  and `toεNFA`.
* `CslibFrontier.Computability.Languages.DFA.toRightLinearGrammar`: canonical right-linear grammar
  on `Fin (Fintype.card σ)` associated with a finite-state `DFA`.
* `CslibFrontier.Computability.Languages.Language.IsRightLinear`,
  `HasRightLinearVarBound`, `HasRightLinearRuleBound`, `HasDFAStateBound`: right-linear languages
  and descriptional resource-bounded regular language classes.

## Main results

* `RightLinearGrammar.exists_cut_in_interval`,
  `RightLinearGrammar.language_eq_toContextFreeGrammar`,
  `RightLinearGrammar.accepts_toεNFA`,
  `DFA.language_toRightLinearGrammar`,
  `Language.isRightLinear_iff_isRegular`.
* `Language.HasDFAStateBound.hasRightLinearVarBound`,
  `Language.HasRightLinearRuleBound.hasRightLinearVarBound_of_two_mul`,
  `Language.HasRightLinearRuleBound.card_first_letters_le`,
  `Language.HasRightLinearRuleBound.card_words_of_length_le`.
-/

public section

universe u v

namespace CslibFrontier.Computability.Languages

section Rules

/-- A right-linear production rule over terminal alphabet `T` and nonterminal type `N`,
representing `lhs → prefixWord · B` when `rhs = some B`, or `lhs → prefixWord` when `rhs = none`.
-/
@[ext]
structure RightLinearRule (T N : Type*) where
  /-- Left-hand side nonterminal. -/
  lhs : N
  /-- Terminal prefix word emitted by applying the rule. -/
  prefixWord : List T
  /-- Optional trailing nonterminal (`none` for a purely terminal rule). -/
  rhs : Option N
deriving DecidableEq, Repr

namespace RightLinearRule

variable {T N : Type*}

/-- Converts a right-linear rule `r` into the corresponding `ContextFreeRule T N`. -/
def toContextFreeRule (r : RightLinearRule T N) : ContextFreeRule T N where
  input := r.lhs
  output := r.prefixWord.map Symbol.terminal ++ r.rhs.elim [] (fun B ↦ [Symbol.nonterminal B])

@[simp, grind =]
theorem toContextFreeRule_input (r : RightLinearRule T N) :
    r.toContextFreeRule.input = r.lhs := by
  rfl

@[simp, grind =]
theorem toContextFreeRule_output (r : RightLinearRule T N) :
    r.toContextFreeRule.output =
      r.prefixWord.map Symbol.terminal ++ r.rhs.elim [] (fun B ↦ [Symbol.nonterminal B]) := by
  rfl

private lemma map_terminal_append_nonterminal_inj {T N : Type*} {p₁ p₂ : List T}
    {o₁ o₂ : Option N}
    (h : p₁.map Symbol.terminal ++ o₁.elim [] (fun B ↦ [Symbol.nonterminal B]) =
      p₂.map Symbol.terminal ++ o₂.elim [] (fun B ↦ [Symbol.nonterminal B])) :
    p₁ = p₂ ∧ o₁ = o₂ := by
  induction p₁ generalizing p₂ with
  | nil =>
    cases p₂ with
    | nil => cases o₁ <;> cases o₂ <;> simp_all
    | cons _ _ => cases o₁ <;> simp at h
  | cons a p₁ ih =>
    cases p₂ with
    | nil => cases o₂ <;> simp at h
    | cons b p₂ =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Symbol.terminal.injEq] at h
      obtain ⟨rfl, hp⟩ := h; obtain ⟨rfl, ho⟩ := ih hp; exact ⟨rfl, ho⟩

/-- The embedding `RightLinearRule.toContextFreeRule` is injective. -/
theorem toContextFreeRule_injective :
    Function.Injective (toContextFreeRule : RightLinearRule T N → ContextFreeRule T N) := by
  intro r₁ r₂ h
  have h_out := congrArg ContextFreeRule.output h
  simp only [toContextFreeRule_output] at h_out
  obtain ⟨hp, ho⟩ := map_terminal_append_nonterminal_inj h_out
  exact RightLinearRule.ext (congrArg ContextFreeRule.input h) hp ho

@[simp, grind =]
theorem toContextFreeRule_inj (r₁ r₂ : RightLinearRule T N) :
    r₁.toContextFreeRule = r₂.toContextFreeRule ↔ r₁ = r₂ := toContextFreeRule_injective.eq_iff

end RightLinearRule

end Rules

section GrammarSemantics

/-- A right-linear grammar over terminal alphabet `T`, with a finite type `NT` of nonterminals,
an initial nonterminal `initial`, and a finite set `rules` of `RightLinearRule T NT`. -/
structure RightLinearGrammar (T : Type*) where
  /-- Type of nonterminal symbols. -/
  NT : Type
  /-- Finiteness witness for the nonterminal type `NT`. -/
  fintypeNT : Fintype NT
  /-- Initial nonterminal symbol. -/
  initial : NT
  /-- Finite set of right-linear production rules. -/
  rules : Finset (RightLinearRule T NT)

namespace RightLinearGrammar

instance instFintypeNT {T : Type*} (G : RightLinearGrammar T) : Fintype G.NT := G.fintypeNT

variable {T : Type*} (G : RightLinearGrammar T)

/-- Converts a right-linear grammar `G` into the underlying `ContextFreeGrammar T`. -/
@[expose]
def toContextFreeGrammar : ContextFreeGrammar T where
  NT := G.NT
  initial := G.initial
  rules :=
    G.rules.map ⟨RightLinearRule.toContextFreeRule, RightLinearRule.toContextFreeRule_injective⟩

@[simp, grind =]
theorem toContextFreeGrammar_initial : G.toContextFreeGrammar.initial = G.initial := by
  rfl

/-- Multi-step nonterminal reachability in `G`. -/
inductive Reaches (G : RightLinearGrammar T) : G.NT → List T → G.NT → Prop
  | refl (A : G.NT) : Reaches G A [] A
  | step {A B C : G.NT} {p w : List T} (hr : ⟨A, p, some B⟩ ∈ G.rules)
      (hrest : Reaches G B w C) : Reaches G A (p ++ w) C

/-- Single-step nonterminal reachability from a non-terminating rule `⟨A, p, some B⟩ ∈ G.rules`.
-/
theorem Reaches.single {G : RightLinearGrammar T} {A B : G.NT} {p : List T}
    (hr : ⟨A, p, some B⟩ ∈ G.rules) : G.Reaches A p B := by
  simpa using Reaches.step hr (Reaches.refl B)

/-- Transitivity (word concatenation) for `RightLinearGrammar.Reaches`. -/
theorem Reaches.trans {G : RightLinearGrammar T} {A B C : G.NT} {u v : List T}
    (hAB : G.Reaches A u B) (hBC : G.Reaches B v C) : G.Reaches A (u ++ v) C := by
  induction hAB with
  | refl _ => simpa using hBC
  | step hr _ ih => rw [List.append_assoc]; exact Reaches.step hr (ih hBC)

/-- Extending a `Reaches` derivation on the right by one non-terminating rule. -/
theorem reaches_append_rule {G : RightLinearGrammar T} {A B C : G.NT} {u p : List T}
    (hAB : G.Reaches A u B) (hr : ⟨B, p, some C⟩ ∈ G.rules) : G.Reaches A (u ++ p) C :=
  hAB.trans (Reaches.single hr)

/-- Terminal word generation from a nonterminal `A` in `G`. -/
inductive Generates (G : RightLinearGrammar T) : G.NT → List T → Prop
  | term {A : G.NT} {w : List T} (hr : ⟨A, w, none⟩ ∈ G.rules) : Generates G A w
  | nonterm {A B : G.NT} {p w : List T} (hr : ⟨A, p, some B⟩ ∈ G.rules)
      (hrest : Generates G B w) : Generates G A (p ++ w)

/-- Prepending a nonterminal reachability derivation to a terminal generation derivation. -/
theorem Reaches.trans_generates {G : RightLinearGrammar T} {A B : G.NT} {u v : List T}
    (hAB : G.Reaches A u B) (hBv : G.Generates B v) : G.Generates A (u ++ v) := by
  induction hAB with
  | refl _ => simpa using hBv
  | step hr _ ih => rw [List.append_assoc]; exact Generates.nonterm hr (ih hBv)

/-- A nonterminal `A` generates `w` if and only if `A` reaches some nonterminal `B` emitting `p`
followed by a terminating rule `⟨B, v, none⟩ ∈ G.rules` with `w = p ++ v`. -/
theorem generates_iff_exists_reaches (A : G.NT) (w : List T) :
    G.Generates A w ↔ ∃ B p v, G.Reaches A p B ∧ ⟨B, v, none⟩ ∈ G.rules ∧ w = p ++ v := by
  constructor
  · intro h; induction h with
    | term hr => exact ⟨_, [], _, Reaches.refl _, hr, (List.nil_append _).symm⟩
    | nonterm hr _ ih =>
      obtain ⟨C, p', v, hreach, hr', rfl⟩ := ih
      exact ⟨C, _ ++ p', v, Reaches.step hr hreach, hr', (List.append_assoc _ _ _).symm⟩
  · rintro ⟨B, p, v, hreach, hr, rfl⟩; exact hreach.trans_generates (Generates.term hr)

/-- The formal language generated by a right-linear grammar `G`. -/
@[expose]
def language (G : RightLinearGrammar T) : _root_.Language T := { w | G.Generates G.initial w }

@[simp, grind =]
theorem mem_language_iff (w : List T) : w ∈ G.language ↔ G.Generates G.initial w := Iff.rfl

/-- Maximum length of `r.prefixWord` across all production rules of `G`. -/
def maxRuleLen (G : RightLinearGrammar T) : ℕ :=
  G.rules.sup fun r ↦ r.prefixWord.length

/-- Every rule in `G.rules` has `prefixWord.length ≤ G.maxRuleLen`. -/
theorem prefixWord_length_le_maxRuleLen {G : RightLinearGrammar T}
    {r : RightLinearRule T G.NT} (hr : r ∈ G.rules) :
    r.prefixWord.length ≤ G.maxRuleLen :=
  Finset.le_sup (f := fun r ↦ r.prefixWord.length) hr

/-- Nonterminal cut-point theorem across any index interval of width at least `G.maxRuleLen`. -/
theorem exists_cut_in_interval {G : RightLinearGrammar T} {A : G.NT} {w : List T}
    (hg : G.Generates A w) {a b : ℕ} (hab : a + G.maxRuleLen ≤ b) (hbw : b < w.length) :
    ∃ (B : G.NT) (u v : List T),
      w = u ++ v ∧ a ≤ u.length ∧ u.length ≤ b ∧ G.Reaches A u B ∧ G.Generates B v := by
  induction hg generalizing a b with
  | @term A w hr =>
    have hle : w.length ≤ G.maxRuleLen := G.prefixWord_length_le_maxRuleLen hr
    omega
  | @nonterm A C p w' hr hrest ih =>
    have hplen : p.length ≤ G.maxRuleLen := G.prefixWord_length_le_maxRuleLen hr
    by_cases hap : a ≤ p.length
    · exact ⟨C, p, w', rfl, hap, by omega, Reaches.single hr, hrest⟩
    · simp only [List.length_append] at hbw
      obtain ⟨B, u', v', rfl, hau', hub', hreach, hgen⟩ :=
        ih (a := a - p.length) (b := b - p.length) (by omega) (by omega)
      refine ⟨B, p ++ u', v', by simp [List.append_assoc], ?_, ?_,
        Reaches.step hr hreach, hgen⟩
      · simp only [List.length_append]; omega
      · simp only [List.length_append]; omega

/-- If no rule in `G` has `G.initial` on the left-hand side, then `G.language = 0`. -/
theorem language_eq_zero_of_forall_lhs_ne_initial (h : ∀ r ∈ G.rules, r.lhs ≠ G.initial) :
    G.language = 0 := by
  ext w; simp only [mem_language_iff, _root_.Language.notMem_zero, iff_false]
  intro hg; cases hg with | term hr => exact h _ hr rfl | nonterm hr _ => exact h _ hr rfl

private lemma split_terminal_nonterminal {T N : Type*}
    {u : List T} {B C : N} {p q : List (Symbol T N)}
    (h : u.map Symbol.terminal ++ [Symbol.nonterminal B] =
      p ++ [Symbol.nonterminal C] ++ q) :
    p = u.map Symbol.terminal ∧ B = C ∧ q = [] := by
  induction p generalizing u with
  | nil =>
    cases u with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.singleton_append, List.cons.injEq,
        Symbol.nonterminal.injEq] at h
      exact ⟨rfl, h.1, h.2.symm⟩
    | cons _ _ => simp at h
  | cons x p ih =>
    cases u with
    | nil => simp at h
    | cons a u =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih htail
      exact ⟨rfl, rfl, rfl⟩

/-- Any `Reaches` derivation in `G` lifts to a `ContextFreeGrammar.Derives` in
`G.toContextFreeGrammar`. -/
theorem derives_toContextFreeGrammar_of_reaches {A B : G.NT} {u : List T}
    (h : G.Reaches A u B) :
    G.toContextFreeGrammar.Derives [Symbol.nonterminal A]
      (u.map Symbol.terminal ++ [Symbol.nonterminal B]) := by
  induction h with
  | refl A =>
    exact (List.nil_append _).symm ▸
      ContextFreeGrammar.Derives.refl (g := G.toContextFreeGrammar) [Symbol.nonterminal A]
  | @step A B C p w hr _ ih =>
    have hrew : (⟨A, p, some B⟩ : RightLinearRule T G.NT).toContextFreeRule.Rewrites
        [Symbol.nonterminal A] (p.map Symbol.terminal ++ [Symbol.nonterminal B]) := by
      simpa using ContextFreeRule.Rewrites.input_output
        (r := (⟨A, p, some B⟩ : RightLinearRule T G.NT).toContextFreeRule)
    have hprod : G.toContextFreeGrammar.Produces [Symbol.nonterminal A]
        (p.map Symbol.terminal ++ [Symbol.nonterminal B]) :=
      ⟨(⟨A, p, some B⟩ : RightLinearRule T G.NT).toContextFreeRule,
        Finset.mem_map.mpr ⟨_, hr, rfl⟩, hrew⟩
    have hstep := ContextFreeGrammar.Derives.append_left ih (p.map Symbol.terminal)
    have hconcat : (p ++ w).map Symbol.terminal ++ [Symbol.nonterminal C] =
        p.map Symbol.terminal ++ (w.map Symbol.terminal ++ [Symbol.nonterminal C]) := by
      simp [List.map_append, List.append_assoc]
    exact hconcat ▸ hprod.trans_derives hstep

/-- Any `Generates` derivation in `G` lifts to a `ContextFreeGrammar.Derives` in
`G.toContextFreeGrammar`. -/
theorem derives_toContextFreeGrammar_of_generates {A : G.NT} {w : List T}
    (h : G.Generates A w) :
    G.toContextFreeGrammar.Derives [Symbol.nonterminal A] (w.map Symbol.terminal) := by
  obtain ⟨B, p, v, hreach, hr, rfl⟩ := (G.generates_iff_exists_reaches A w).mp h
  have h1 := G.derives_toContextFreeGrammar_of_reaches hreach
  have hrew : (⟨B, v, none⟩ : RightLinearRule T G.NT).toContextFreeRule.Rewrites
      [Symbol.nonterminal B] (v.map Symbol.terminal) := by
    simpa using ContextFreeRule.Rewrites.input_output
      (r := (⟨B, v, none⟩ : RightLinearRule T G.NT).toContextFreeRule)
  have hprod : G.toContextFreeGrammar.Produces [Symbol.nonterminal B] (v.map Symbol.terminal) :=
    ⟨(⟨B, v, none⟩ : RightLinearRule T G.NT).toContextFreeRule,
      Finset.mem_map.mpr ⟨_, hr, rfl⟩, hrew⟩
  have h2 := hprod.single.append_left (p.map Symbol.terminal)
  rw [List.map_append]
  exact h1.trans h2

private lemma derives_toContextFreeGrammar_inv {A : G.NT} {s : List (Symbol T G.NT)}
    (h : G.toContextFreeGrammar.Derives [Symbol.nonterminal A] s) :
    (∃ u B, s = u.map Symbol.terminal ++ [Symbol.nonterminal B] ∧ G.Reaches A u B) ∨
      (∃ w, s = w.map Symbol.terminal ∧ G.Generates A w) := by
  induction h with
  | refl => exact Or.inl ⟨[], A, rfl, Reaches.refl A⟩
  | tail _ hprod ih =>
    obtain ⟨r', hr', hrew⟩ := hprod
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hr'
    change r.toContextFreeRule.Rewrites _ _ at hrew
    rw [ContextFreeRule.rewrites_iff] at hrew
    obtain ⟨p, q, hs₁, hs₂⟩ := hrew
    rcases ih with ⟨u, B, rfl, hreach⟩ | ⟨w, rfl, _⟩
    · simp only [RightLinearRule.toContextFreeRule_input] at hs₁
      obtain ⟨rfl, rfl, rfl⟩ := split_terminal_nonterminal hs₁
      rcases r with ⟨lhs, pref, rhs⟩
      cases rhs with
      | none =>
        right
        refine ⟨u ++ pref, ?_, hreach.trans_generates (Generates.term hr)⟩
        simpa [List.map_append] using hs₂
      | some C =>
        left
        refine ⟨u ++ pref, C, ?_, reaches_append_rule hreach hr⟩
        simpa [List.map_append, List.append_assoc] using hs₂
    · exfalso
      have hmem : Symbol.nonterminal r.toContextFreeRule.input ∈ w.map Symbol.terminal := by
        rw [hs₁]; simp
      simp at hmem

/-- The language generated by `G` equals the context-free language of `G.toContextFreeGrammar`. -/
theorem language_eq_toContextFreeGrammar : G.language = G.toContextFreeGrammar.language := by
  ext w
  constructor
  · intro hw; exact G.derives_toContextFreeGrammar_of_generates hw
  · intro hw
    rw [ContextFreeGrammar.mem_language_iff] at hw
    rcases derives_toContextFreeGrammar_inv G hw with ⟨u, B, hEq, _⟩ | ⟨w', hEq, hgen⟩
    · exfalso
      have hmem : (Symbol.nonterminal B : Symbol T G.NT) ∈
          u.map Symbol.terminal ++ [Symbol.nonterminal B] := by simp
      have hmem' : (Symbol.nonterminal B : Symbol T G.NT) ∈ w.map Symbol.terminal := hEq ▸ hmem
      simp at hmem'
    · have hw' : w = w' := List.map_injective_iff.mpr (fun _ _ h ↦ Symbol.terminal.inj h) hEq
      rwa [hw']

/-- Every language generated by a right-linear grammar is context-free. -/
theorem isContextFree_language : G.language.IsContextFree :=
  ⟨G.toContextFreeGrammar, G.language_eq_toContextFreeGrammar.symm⟩

end RightLinearGrammar

end GrammarSemantics

section AutomataEquivalence

namespace RightLinearGrammar

variable {T : Type u} (G : RightLinearGrammar T)

/-- Finite state space for the `εNFA` associated with a right-linear grammar `G`. -/
abbrev NFAState (G : RightLinearGrammar T) : Type u :=
  Option (G.NT ⊕ (Σ r : { r : RightLinearRule T G.NT // r ∈ G.rules },
    Fin (r.1.prefixWord.length + 1)))

/-- Epsilon nondeterministic finite automaton recognizing `G.language`. -/
def toεNFA : εNFA T G.NFAState where
  step s a :=
    match s with
    | none => ∅
    | some (Sum.inl A) =>
      { t | ∃ r : G.rules, r.1.lhs = A ∧ a = none ∧ t = some (Sum.inr ⟨r, 0⟩) }
    | some (Sum.inr ⟨r, i⟩) =>
      if h : i.val < r.1.prefixWord.length then
        { t | a = some (r.1.prefixWord[i.val]'h) ∧
          t = some (Sum.inr ⟨r, ⟨i.val + 1, Nat.succ_lt_succ h⟩⟩) }
      else
        { t | a = none ∧ t = r.1.rhs.map Sum.inl }
  start := {some (Sum.inl G.initial)}
  accept := {none}

@[simp, grind =]
theorem toεNFA_start : G.toεNFA.start = {some (Sum.inl G.initial)} := by
  rfl

@[simp, grind =]
theorem toεNFA_accept : G.toεNFA.accept = {none} := by
  rfl

private lemma reduceOption_map_some (w : List T) : (w.map some).reduceOption = w := by
  induction w <;> simp [*]

private lemma isPath_rulePos_of_ne {r : G.rules} {i : Fin (r.1.prefixWord.length + 1)}
    {s : G.NFAState} (hs : ∀ j, s ≠ some (Sum.inr ⟨r, j⟩)) {x' : List (Option T)}
    (hp : G.toεNFA.IsPath (some (Sum.inr ⟨r, i⟩)) s x') :
    ∃ y', x' = (r.1.prefixWord.drop i.val).map some ++ none :: y' ∧
      G.toεNFA.IsPath (r.1.rhs.map Sum.inl) s y' := by
  have hk : ∀ k (i : Fin (r.1.prefixWord.length + 1)) (x' : List (Option T)),
      r.1.prefixWord.length - i.val = k →
      G.toεNFA.IsPath (some (Sum.inr ⟨r, i⟩)) s x' →
      ∃ y', x' = (r.1.prefixWord.drop i.val).map some ++ none :: y' ∧
        G.toεNFA.IsPath (r.1.rhs.map Sum.inl) s y' := by
    intro k
    induction k with
    | zero =>
      intro i x' hki hp'
      have hnot : ¬ i.val < r.1.prefixWord.length := by omega
      cases hp' with
      | nil => exact absurd rfl (hs i)
      | cons t _ _ a x'' hstep hrest =>
        simp only [toεNFA, Set.mem_ofPred_eq, hnot, dite_false] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        exact ⟨x'', by simp [List.drop_of_length_le (le_of_not_gt hnot)], hrest⟩
    | succ k ih =>
      intro i x' hki hp'
      have hlt : i.val < r.1.prefixWord.length := by omega
      cases hp' with
      | nil => exact absurd rfl (hs i)
      | cons t _ _ a x'' hstep hrest =>
        simp only [toεNFA, Set.mem_ofPred_eq, hlt, dite_true] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        have hki' : r.1.prefixWord.length - (⟨i.val + 1, Nat.succ_lt_succ hlt⟩ :
            Fin (r.1.prefixWord.length + 1)).val = k := by simp; omega
        obtain ⟨y', rfl, hy'⟩ := ih ⟨i.val + 1, Nat.succ_lt_succ hlt⟩ x'' hki' hrest
        refine ⟨y', ?_, hy'⟩
        rw [(List.getElem_cons_drop hlt).symm, List.map_cons, List.cons_append]
  exact hk (r.1.prefixWord.length - i.val) i x' rfl hp

private lemma isPath_rulePos_to_end (r : G.rules) (i : Fin (r.1.prefixWord.length + 1)) :
    G.toεNFA.IsPath (some (Sum.inr ⟨r, i⟩)) (r.1.rhs.map Sum.inl)
      ((r.1.prefixWord.drop i.val).map some ++ [none]) := by
  have hk : ∀ k (i : Fin (r.1.prefixWord.length + 1)),
      r.1.prefixWord.length - i.val = k →
      G.toεNFA.IsPath (some (Sum.inr ⟨r, i⟩)) (r.1.rhs.map Sum.inl)
        ((r.1.prefixWord.drop i.val).map some ++ [none]) := by
    intro k
    induction k with
    | zero =>
      intro i hki
      have hnot : ¬ i.val < r.1.prefixWord.length := by omega
      rw [List.drop_of_length_le (le_of_not_gt hnot), List.map_nil, List.nil_append]
      exact εNFA.IsPath.cons (r.1.rhs.map Sum.inl) _ _ none [] (by simp [toεNFA, hnot])
        (εNFA.IsPath.nil _)
    | succ k ih =>
      intro i hki
      have hlt : i.val < r.1.prefixWord.length := by omega
      have hki' : r.1.prefixWord.length - (⟨i.val + 1, Nat.succ_lt_succ hlt⟩ :
          Fin (r.1.prefixWord.length + 1)).val = k := by simp; omega
      rw [(List.getElem_cons_drop hlt).symm, List.map_cons, List.cons_append]
      exact εNFA.IsPath.cons (some (Sum.inr ⟨r, ⟨i.val + 1, Nat.succ_lt_succ hlt⟩⟩)) _ _
        (some (r.1.prefixWord[i.val]'hlt)) _ (by simp [toεNFA, hlt]) (ih _ hki')
  exact hk (r.1.prefixWord.length - i.val) i rfl

private lemma generates_of_isPath_to_accept :
    ∀ n (x' : List (Option T)) (A : G.NT),
      x'.length ≤ n → G.toεNFA.IsPath (some (Sum.inl A)) none x' →
      G.Generates A x'.reduceOption := by
  intro n
  induction n with
  | zero =>
    intro x' A hlen hp
    have hxnil : x' = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hxnil; simp at hp
  | succ n ih =>
    intro x' A hlen hp
    cases hp with
    | cons t _ _ a x'' hstep hrest =>
      simp only [toεNFA, Set.mem_ofPred_eq] at hstep
      rcases hstep with ⟨r, hr_lhs, rfl, rfl⟩
      have hne : ∀ j, (none : G.NFAState) ≠ some (Sum.inr ⟨r, j⟩) := fun _ h ↦ by cases h
      obtain ⟨y', rfl, hy'⟩ := isPath_rulePos_of_ne G hne hrest
      simp only [Fin.val_zero, List.drop_zero] at hy' ⊢
      rcases r with ⟨rval, hr_mem⟩
      dsimp only at hr_lhs
      cases hr_rhs : rval.rhs with
      | none =>
        simp only [hr_rhs, Option.map_none] at hy'
        cases hy' with
        | nil =>
          have hr_eq : rval = ⟨A, rval.prefixWord, none⟩ := RightLinearRule.ext hr_lhs rfl hr_rhs
          simpa [List.reduceOption_append, reduceOption_map_some] using
            Generates.term (hr_eq ▸ hr_mem)
        | cons _ _ _ _ _ hbad _ =>
          simp only [toεNFA] at hbad; exact False.elim hbad
      | some B =>
        simp only [hr_rhs, Option.map_some] at hy'
        have hlen_y : y'.length ≤ n := by
          simp only [List.length_cons, List.length_append, List.length_map] at hlen; omega
        have hr_eq : rval = ⟨A, rval.prefixWord, some B⟩ := RightLinearRule.ext hr_lhs rfl hr_rhs
        simpa [List.reduceOption_append, reduceOption_map_some] using
          Generates.nonterm (hr_eq ▸ hr_mem) (ih y' B hlen_y hy')

private lemma exists_isPath_to_accept_of_generates {A : G.NT} {w : List T}
    (h : G.Generates A w) :
    ∃ x', x'.reduceOption = w ∧ G.toεNFA.IsPath (some (Sum.inl A)) none x' := by
  induction h with
  | @term A w hr =>
    let r : G.rules := ⟨⟨A, w, none⟩, hr⟩
    refine ⟨none :: w.map some ++ [none],
      by simp [List.reduceOption_append, reduceOption_map_some], ?_⟩
    exact εNFA.IsPath.cons (some (Sum.inr ⟨r, 0⟩)) _ _ none _ ⟨r, rfl, rfl, rfl⟩
      (by simpa [r] using isPath_rulePos_to_end G r 0)
  | @nonterm A B p w hr _ ih =>
    obtain ⟨y', hy'_red, hy'_path⟩ := ih
    let r : G.rules := ⟨⟨A, p, some B⟩, hr⟩
    refine ⟨none :: p.map some ++ none :: y',
      by simp [List.reduceOption_append, reduceOption_map_some, hy'_red], ?_⟩
    refine εNFA.IsPath.cons (some (Sum.inr ⟨r, 0⟩)) _ _ none _ ⟨r, rfl, rfl, rfl⟩ ?_
    have hmid' : G.toεNFA.IsPath (some (Sum.inr ⟨r, 0⟩)) (some (Sum.inl B))
        (p.map some ++ [none]) := by simpa [r] using isPath_rulePos_to_end G r 0
    have hfull : G.toεNFA.IsPath (some (Sum.inr ⟨r, 0⟩)) none ((p.map some ++ [none]) ++ y') :=
      (εNFA.isPath_append G.toεNFA).mpr ⟨some (Sum.inl B), hmid', hy'_path⟩
    simpa [List.append_assoc] using hfull

/-- The `εNFA` `G.toεNFA` accepts `G.language`. -/
@[simp, grind =]
theorem accepts_toεNFA : G.toεNFA.accepts = G.language := by
  ext w
  rw [εNFA.mem_accepts_iff_exists_path, mem_language_iff]
  constructor
  · rintro ⟨s₁, s₂, x', hs₁, hs₂, rfl, hp⟩
    rw [G.toεNFA_start, Set.mem_singleton_iff] at hs₁
    rw [G.toεNFA_accept, Set.mem_singleton_iff] at hs₂
    subst hs₁; subst hs₂
    exact generates_of_isPath_to_accept G x'.length x' G.initial le_rfl hp
  · intro hg
    obtain ⟨x', hx', hp⟩ := exists_isPath_to_accept_of_generates G hg
    exact ⟨some (Sum.inl G.initial), none, x', rfl, rfl, hx', hp⟩

/-- Every language generated by a right-linear grammar is regular. -/
theorem isRegular_language : G.language.IsRegular := by
  rw [← G.accepts_toεNFA, ← εNFA.toNFA_correct, ← NFA.toDFA_correct]
  exact _root_.Language.isRegular_iff.mpr
    ⟨Set G.NFAState, inferInstance, G.toεNFA.toNFA.toDFA, rfl⟩

end RightLinearGrammar

namespace DFA

private noncomputable def toRightLinearRules {T : Type*} [Fintype T] {σ : Type*} [Fintype σ]
    (M : _root_.DFA T σ) : Finset (RightLinearRule T (Fin (Fintype.card σ))) :=
  (Finset.univ.map
    ⟨fun qa : Fin (Fintype.card σ) × T ↦
      ⟨qa.1, [qa.2], some ((M.reindex (Fintype.equivFin σ)).step qa.1 qa.2)⟩,
      fun a b h ↦ by
        have hl := congrArg RightLinearRule.lhs h
        have hp := congrArg RightLinearRule.prefixWord h
        simp only [List.cons.injEq, and_true] at hp
        exact Prod.ext hl hp⟩).disjUnion
    ((@Finset.filter (Fin (Fintype.card σ))
      (fun q ↦ q ∈ (M.reindex (Fintype.equivFin σ)).accept)
      (Classical.decPred _) Finset.univ).map
      ⟨fun q ↦ ⟨q, [], none⟩, fun a b h ↦ congrArg RightLinearRule.lhs h⟩)
    (Finset.disjoint_left.mpr fun r hr₁ hr₂ ↦ by
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter] at hr₁ hr₂
      obtain ⟨_, rfl⟩ := hr₁; obtain ⟨_, _, hbad⟩ := hr₂
      cases congrArg RightLinearRule.rhs hbad)

/-- Converts a finite-state `DFA T σ` over a finite alphabet `T` into an equivalent
`RightLinearGrammar T` whose nonterminal type is `Fin (Fintype.card σ)`. -/
noncomputable def toRightLinearGrammar {T : Type*} [Fintype T] {σ : Type*} [Fintype σ]
    (M : _root_.DFA T σ) : RightLinearGrammar T where
  NT := Fin (Fintype.card σ)
  fintypeNT := inferInstance
  initial := (M.reindex (Fintype.equivFin σ)).start
  rules := toRightLinearRules M

@[simp]
theorem card_toRightLinearGrammar_NT {T : Type*} [Fintype T] {σ : Type*} [Fintype σ]
    (M : _root_.DFA T σ) : Fintype.card (toRightLinearGrammar M).NT = Fintype.card σ := by
  unfold toRightLinearGrammar
  exact Fintype.card_fin (Fintype.card σ)

private lemma mem_toRightLinearRules {T : Type*} [Fintype T] {σ : Type*} [Fintype σ]
    (M : _root_.DFA T σ) (r : RightLinearRule T (Fin (Fintype.card σ))) :
    r ∈ toRightLinearRules M ↔
      (∃ q : Fin (Fintype.card σ), ∃ a,
        r = ⟨q, [a], some ((M.reindex (Fintype.equivFin σ)).step q a)⟩) ∨
      (∃ q ∈ (M.reindex (Fintype.equivFin σ)).accept, r = ⟨q, [], none⟩) := by
  simp only [toRightLinearRules, Finset.mem_disjUnion, Finset.mem_map, Finset.mem_univ,
    Finset.mem_filter, true_and, Prod.exists]
  constructor
  · rintro (⟨q, a, h⟩ | ⟨q, hq, h⟩) <;>
      [exact Or.inl ⟨q, a, h.symm⟩; exact Or.inr ⟨q, hq, h.symm⟩]
  · rintro (⟨q, a, h⟩ | ⟨q, hq, h⟩) <;>
      [exact Or.inl ⟨q, a, h.symm⟩; exact Or.inr ⟨q, hq, h.symm⟩]

/-- The right-linear grammar `DFA.toRightLinearGrammar M` generates the exact language `M.accepts`.
-/
@[simp, grind =]
theorem language_toRightLinearGrammar {T : Type*} [Fintype T] {σ : Type*} [Fintype σ]
    (M : _root_.DFA T σ) : (toRightLinearGrammar M).language = M.accepts := by
  let M' := M.reindex (Fintype.equivFin σ)
  let G₀ : RightLinearGrammar T := ⟨Fin (Fintype.card σ), inferInstance, M'.start,
    toRightLinearRules M⟩
  have hreaches_mp : ∀ {q q' : G₀.NT} {w : List T},
      G₀.Reaches q w q' → M'.evalFrom q w = q' := by
    intro q q' w h
    induction h with
    | refl _ => rfl
    | step hr _ ih =>
      rcases (mem_toRightLinearRules M _).mp hr with ⟨q₁, a, h⟩ | ⟨_, _, h⟩
      · cases h; exact ih
      · cases h
  have hreaches_mpr : ∀ (w : List T) (q q' : Fin (Fintype.card σ)),
      M'.evalFrom q w = q' → G₀.Reaches q w q' := by
    intro w
    induction w with
    | nil =>
      intro q q' h
      change q = q' at h; subst h; exact RightLinearGrammar.Reaches.refl (G := G₀) q
    | cons a w ih =>
      intro q q' h
      change M'.evalFrom (M'.step q a) w = q' at h
      exact RightLinearGrammar.Reaches.step (G := G₀)
        ((mem_toRightLinearRules M _).mpr (Or.inl ⟨q, a, rfl⟩)) (ih (M'.step q a) q' h)
  change G₀.language = M.accepts
  rw [← M.accepts_reindex (Fintype.equivFin σ)]
  ext w
  rw [RightLinearGrammar.mem_language_iff, RightLinearGrammar.generates_iff_exists_reaches,
    _root_.DFA.mem_accepts, _root_.DFA.eval]
  constructor
  · rintro ⟨q', p, v, hreach, hr, rfl⟩
    rcases (mem_toRightLinearRules M _).mp hr with ⟨_, _, h⟩ | ⟨q₁, hq₁, h⟩
    · cases h
    · cases h
      have heval : M'.evalFrom M'.start p = q' := hreaches_mp hreach
      rw [List.append_nil]; exact heval ▸ hq₁
  · intro hw
    refine ⟨M'.evalFrom M'.start w, w, [], ?_, ?_, (List.append_nil w).symm⟩
    · exact hreaches_mpr w M'.start _ rfl
    · exact (mem_toRightLinearRules M _).mpr (Or.inr ⟨_, hw, rfl⟩)

/-- Pumping bound on minimal accepted words: if a finite-state `DFA` `M` accepts at least one word,
it accepts a word of length strictly less than `Fintype.card σ`. -/
theorem exists_mem_accepts_length_lt_card {T : Type*} {σ : Type*} [Fintype σ]
    (M : _root_.DFA T σ) {w : List T} (hw : w ∈ M.accepts) :
    ∃ u ∈ M.accepts, u.length < Fintype.card σ := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases hlt : w.length < Fintype.card σ
    · exact ⟨w, hw, hlt⟩
    · have hge : Fintype.card σ ≤ w.length := Nat.le_of_not_lt hlt
      obtain ⟨i, j, hne, hij⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun i : Fin (Fintype.card σ + 1) ↦ M.eval (w.take i.val)) (by simp)
      wlog hij_lt : i.val < j.val generalizing i j
      · exact this j i hne.symm hij.symm
          (lt_of_le_of_ne (Nat.le_of_not_lt hij_lt) (Fin.val_ne_iff.mpr hne).symm)
      let w' := w.take i.val ++ w.drop j.val
      have hw'_mem : w' ∈ M.accepts := by
        rw [_root_.DFA.mem_accepts, _root_.DFA.eval, _root_.DFA.evalFrom_of_append]
        change M.evalFrom (M.eval (w.take i.val)) (w.drop j.val) ∈ M.accept
        rw [hij, _root_.DFA.eval, ← _root_.DFA.evalFrom_of_append, List.take_append_drop]
        exact hw
      have hw'_len : w'.length < n := by
        have hi : i.val ≤ w.length := by omega
        have hj : j.val ≤ w.length := by omega
        simp only [w', List.length_append, List.length_take_of_le hi, List.length_drop]
        omega
      exact ih w'.length hw'_len hw'_mem rfl

end DFA

namespace Language

variable {T : Type*}

/-- A language `L : Language T` is right-linear if it is generated by some right-linear grammar.
-/
@[expose]
def IsRightLinear (L : _root_.Language T) : Prop :=
  ∃ G : RightLinearGrammar T, G.language = L

/-- Characterization of `Language.IsRightLinear`. -/
theorem isRightLinear_iff (L : _root_.Language T) :
    IsRightLinear L ↔ ∃ G : RightLinearGrammar T, G.language = L := Iff.rfl

/-- Every right-linear language is regular. -/
theorem IsRightLinear.isRegular {L : _root_.Language T} (h : IsRightLinear L) : L.IsRegular :=
  let ⟨G, hG⟩ := h; hG ▸ G.isRegular_language

/-- Every right-linear language is context-free. -/
theorem IsRightLinear.isContextFree {L : _root_.Language T} (h : IsRightLinear L) :
    L.IsContextFree :=
  let ⟨G, hG⟩ := h; hG ▸ G.isContextFree_language

/-- Over a finite alphabet `T`, every regular language is right-linear. -/
theorem isRightLinear_of_isRegular [Finite T] {L : _root_.Language T} (h : L.IsRegular) :
    IsRightLinear L := by
  have _ : Fintype T := Fintype.ofFinite T
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨DFA.toRightLinearGrammar M, DFA.language_toRightLinearGrammar M⟩

/-- Over a finite alphabet `T`, a language is right-linear if and only if it is regular. -/
theorem isRightLinear_iff_isRegular [Finite T] (L : _root_.Language T) :
    IsRightLinear L ↔ L.IsRegular := ⟨IsRightLinear.isRegular, isRightLinear_of_isRegular⟩

/-- `HasRightLinearVarBound n L` (`RL_n^V`) holds when `L` is generated by a right-linear grammar
with at most `n` nonterminals. -/
@[expose]
def HasRightLinearVarBound (n : ℕ) (L : _root_.Language T) : Prop :=
  ∃ G : RightLinearGrammar T, Fintype.card G.NT ≤ n ∧ G.language = L

/-- Monotonicity of `HasRightLinearVarBound` in the nonterminal bound `n`. -/
theorem HasRightLinearVarBound.mono {m n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearVarBound m L) (hmn : m ≤ n) : HasRightLinearVarBound n L :=
  let ⟨G, hc, hL⟩ := h; ⟨G, hc.trans hmn, hL⟩

/-- Any language with a right-linear nonterminal bound is regular. -/
theorem HasRightLinearVarBound.isRegular {n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearVarBound n L) : L.IsRegular :=
  let ⟨G, _, hL⟩ := h; hL ▸ G.isRegular_language

/-- No language has right-linear nonterminal bound `0`, since every grammar has an initial
nonterminal. -/
theorem not_hasRightLinearVarBound_zero (L : _root_.Language T) :
    ¬ HasRightLinearVarBound 0 L := by
  rintro ⟨G, hcard, _⟩
  have hpos : 0 < Fintype.card G.NT := Fintype.card_pos_iff.mpr ⟨G.initial⟩
  omega

/-- `HasRightLinearRuleBound n L` (`RL_n^P`) holds when `L` is generated by a right-linear grammar
with at most `n` production rules. -/
@[expose]
def HasRightLinearRuleBound (n : ℕ) (L : _root_.Language T) : Prop :=
  ∃ G : RightLinearGrammar T, G.rules.card ≤ n ∧ G.language = L

/-- Monotonicity of `HasRightLinearRuleBound` in the rule bound `n`. -/
theorem HasRightLinearRuleBound.mono {m n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearRuleBound m L) (hmn : m ≤ n) : HasRightLinearRuleBound n L :=
  let ⟨G, hc, hL⟩ := h; ⟨G, hc.trans hmn, hL⟩

/-- Any language with a right-linear rule bound is regular. -/
theorem HasRightLinearRuleBound.isRegular {n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearRuleBound n L) : L.IsRegular :=
  let ⟨G, _, hL⟩ := h; hL ▸ G.isRegular_language

/-- Mapping a language in `RL_n^P` along any function `f : T → T'` preserves the rule bound `n`. -/
theorem HasRightLinearRuleBound.map {T' : Type*} (f : T → T') {n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearRuleBound n L) :
    HasRightLinearRuleBound n (_root_.Language.map f L) := by
  classical
  obtain ⟨G, hcard, rfl⟩ := h
  let mapRule : RightLinearRule T G.NT → RightLinearRule T' G.NT :=
    fun r ↦ ⟨r.lhs, r.prefixWord.map f, r.rhs⟩
  let G' : RightLinearGrammar T' := ⟨G.NT, G.fintypeNT, G.initial, G.rules.image mapRule⟩
  refine ⟨G', Finset.card_image_le.trans hcard, ?_⟩
  ext w'
  rw [RightLinearGrammar.mem_language_iff]
  constructor
  · intro hg'
    have hinv : ∀ (A : G'.NT) (w' : List T'), G'.Generates A w' →
        ∃ w, G.Generates A w ∧ w.map f = w' := by
      intro A w' hg
      induction hg with
      | @term A w' hr =>
        obtain ⟨r, hrG, heq⟩ := Finset.mem_image.mp hr
        rcases r with ⟨lhs, p, rhs⟩
        dsimp only [mapRule] at heq
        have hlhs : lhs = A := congrArg RightLinearRule.lhs heq
        have hp : p.map f = w' := congrArg RightLinearRule.prefixWord heq
        have hrhs : rhs = none := congrArg RightLinearRule.rhs heq
        subst hlhs hrhs
        exact ⟨p, RightLinearGrammar.Generates.term hrG, hp⟩
      | @nonterm A B p' u' hr _ ih =>
        obtain ⟨r, hrG, heq⟩ := Finset.mem_image.mp hr
        rcases r with ⟨lhs, p, rhs⟩
        dsimp only [mapRule] at heq
        have hlhs : lhs = A := congrArg RightLinearRule.lhs heq
        have hp : p.map f = p' := congrArg RightLinearRule.prefixWord heq
        have hrhs : rhs = some B := congrArg RightLinearRule.rhs heq
        subst hlhs hrhs
        obtain ⟨u, huG, hu⟩ := ih
        exact ⟨p ++ u, RightLinearGrammar.Generates.nonterm hrG huG, by simp [hp, hu]⟩
    obtain ⟨w, hwG, rfl⟩ := hinv G.initial w' hg'
    exact ⟨w, (G.mem_language_iff w).mpr hwG, rfl⟩
  · rintro ⟨w, hwG, rfl⟩
    have hfwd : ∀ (A : G.NT) (w : List T), G.Generates A w → G'.Generates A (w.map f) := by
      intro A w hg
      induction hg with
      | @term A w hr =>
        exact RightLinearGrammar.Generates.term (Finset.mem_image.mpr ⟨_, hr, rfl⟩)
      | @nonterm A B p u hr _ ih =>
        rw [List.map_append]
        exact RightLinearGrammar.Generates.nonterm (Finset.mem_image.mpr ⟨_, hr, rfl⟩) ih
    exact hfwd G.initial w ((G.mem_language_iff w).mp hwG)

/-- A language has right-linear rule bound `0` if and only if it is empty (`0`). -/
@[simp]
theorem hasRightLinearRuleBound_zero_iff (L : _root_.Language T) :
    HasRightLinearRuleBound 0 L ↔ L = 0 := by
  constructor
  · rintro ⟨G, hcard, rfl⟩
    have hempty : G.rules = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact G.language_eq_zero_of_forall_lhs_ne_initial (fun r hr ↦ by simp [hempty] at hr)
  · rintro rfl
    refine ⟨⟨Unit, inferInstance, (), ∅⟩, by simp, ?_⟩
    exact RightLinearGrammar.language_eq_zero_of_forall_lhs_ne_initial _ (fun r hr ↦ by simp at hr)

private lemma exists_rule_prefixWord_nil_of_generates {G : RightLinearGrammar T}
    {A : G.NT} {w : List T} (hg : G.Generates A w) (hw : w = []) :
    ∃ r ∈ G.rules, r.prefixWord = [] := by
  induction hg with
  | term hr => subst hw; exact ⟨_, hr, rfl⟩
  | nonterm _ _ ih =>
    obtain ⟨_, hw'⟩ := List.append_eq_nil_iff.mp hw
    exact ih hw'

private lemma exists_rule_head?_eq_of_generates {G : RightLinearGrammar T}
    {A : G.NT} {w : List T} (hg : G.Generates A w) {c : T} (hw : w.head? = some c) :
    ∃ r ∈ G.rules, r.prefixWord.head? = some c := by
  induction hg with
  | term hr => exact ⟨_, hr, hw⟩
  | @nonterm A B p u hr _ ih =>
    cases p with
    | nil => exact ih (by simpa using hw)
    | cons d p' =>
      simp only [List.cons_append, List.head?_cons] at hw
      exact ⟨_, hr, hw⟩

/-- Initial-letter bound for `RL_n^P`: if `L` is generated by at most `n` right-linear rules and
every symbol `c ∈ S` starts at least one word in `L`, then `S.card ≤ n`. -/
theorem HasRightLinearRuleBound.card_first_letters_le {n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearRuleBound n L) (S : Finset T) (hS : ∀ c ∈ S, ∃ w, c :: w ∈ L) :
    S.card ≤ n := by
  classical
  obtain ⟨G, hcard, rfl⟩ := h
  have hsub : S.map ⟨some, Option.some_injective T⟩ ⊆
      G.rules.image (fun r ↦ r.prefixWord.head?) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, hw⟩ := hS c hc
    obtain ⟨r, hr, hhead⟩ :=
      exists_rule_head?_eq_of_generates ((G.mem_language_iff _).mp hw) rfl
    exact Finset.mem_image.mpr ⟨r, hr, hhead⟩
  calc S.card = (S.map ⟨some, Option.some_injective T⟩).card := (Finset.card_map _).symm
    _ ≤ (G.rules.image (fun r ↦ r.prefixWord.head?)).card := Finset.card_le_card hsub
    _ ≤ G.rules.card := Finset.card_image_le
    _ ≤ n := hcard

/-- Strengthened initial-letter bound for `RL_n^P`: if `[] ∈ L` and every symbol `c ∈ S` starts at
least one word in `L`, then `S.card + 1 ≤ n`. -/
theorem HasRightLinearRuleBound.card_first_letters_add_one_le {n : ℕ} {L : _root_.Language T}
    (h : HasRightLinearRuleBound n L) (hnil : [] ∈ L)
    (S : Finset T) (hS : ∀ c ∈ S, ∃ w, c :: w ∈ L) :
    S.card + 1 ≤ n := by
  classical
  obtain ⟨G, hcard, rfl⟩ := h
  obtain ⟨r₀, hr₀, hp₀⟩ :=
    exists_rule_prefixWord_nil_of_generates ((G.mem_language_iff []).mp hnil) rfl
  have hnone_not : (none : Option T) ∉ S.map ⟨some, Option.some_injective T⟩ := by
    intro hm
    obtain ⟨c, _, hbad⟩ := Finset.mem_map.mp hm
    cases hbad
  have hsub : insert none (S.map ⟨some, Option.some_injective T⟩) ⊆
      G.rules.image (fun r ↦ r.prefixWord.head?) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_image.mpr ⟨r₀, hr₀, by simp [hp₀]⟩
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx'
      obtain ⟨w, hw⟩ := hS c hc
      obtain ⟨r, hr, hhead⟩ :=
        exists_rule_head?_eq_of_generates ((G.mem_language_iff _).mp hw) rfl
      exact Finset.mem_image.mpr ⟨r, hr, hhead⟩
  calc S.card + 1
      = (insert none (S.map ⟨some, Option.some_injective T⟩)).card := by
          rw [Finset.card_insert_of_notMem hnone_not, Finset.card_map]
    _ ≤ (G.rules.image (fun r ↦ r.prefixWord.head?)).card := Finset.card_le_card hsub
    _ ≤ G.rules.card := Finset.card_image_le
    _ ≤ n := hcard

/-- Exponential word-count bound for `RL_n^P` (`n ≥ 2`): any finite set `S` of words in `L` each
of length at most `K` has cardinality at most `n * (K + 1) * (n - 1) ^ K`. -/
theorem HasRightLinearRuleBound.card_words_of_length_le {n : ℕ} (hn : 2 ≤ n)
    {L : _root_.Language T} (h : HasRightLinearRuleBound n L)
    (S : Finset (List T)) (K : ℕ) (hS : ∀ w ∈ S, w ∈ L ∧ w.length ≤ K) :
    S.card ≤ n * (K + 1) * (n - 1) ^ K := by
  classical
  by_cases hSemp : S = ∅
  · subst hSemp; simp
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSemp
  obtain ⟨G, hcard, rfl⟩ := h
  let Rt := G.rules.filter fun r ↦ r.rhs = none
  let Rpos := G.rules.filter fun r ↦ r.rhs ≠ none ∧ r.prefixWord ≠ []
  have hdecomp : ∀ (A : G.NT) (w : List T), G.Generates A w →
      ∃ (es : List { r // r ∈ Rpos }) (rt : { r // r ∈ Rt }),
        es.length ≤ w.length ∧
        w = (es.map fun e ↦ e.1.prefixWord).flatten ++ rt.1.prefixWord := by
    intro A w hg
    induction hg with
    | @term A w hr =>
      exact ⟨[], ⟨⟨A, w, none⟩, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩, Nat.zero_le _, rfl⟩
    | @nonterm A B p u hr _ ih =>
      obtain ⟨es, rt, hlen, rfl⟩ := ih
      by_cases hp : p = []
      · subst hp; exact ⟨es, rt, by simpa using hlen, by simp⟩
      · have hmem : (⟨A, p, some B⟩ : RightLinearRule T G.NT) ∈ Rpos :=
          Finset.mem_filter.mpr ⟨hr, by simp, hp⟩
        have hp_pos : 1 ≤ p.length := List.length_pos_iff.mpr hp
        refine ⟨⟨⟨A, p, some B⟩, hmem⟩ :: es, rt, ?_, ?_⟩
        · rw [List.length_cons, List.length_append]
          omega
        · simp [List.append_assoc]
  obtain ⟨_, rt₀, _, _⟩ := hdecomp G.initial w₀ ((G.mem_language_iff w₀).mp (hS w₀ hw₀).1)
  have hRt_pos : 1 ≤ Rt.card := Finset.card_pos.mpr ⟨rt₀.1, rt₀.2⟩
  have hdisj : Disjoint Rpos Rt := Finset.disjoint_left.mpr fun r hr₁ hr₂ ↦
    (Finset.mem_filter.mp hr₁).2.1 (Finset.mem_filter.mp hr₂).2
  have hsum_card : Rpos.card + Rt.card ≤ n :=
    (Finset.card_union_of_disjoint hdisj).symm.le.trans
      ((Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))).trans hcard)
  have hRpos_le : Rpos.card ≤ n - 1 := by omega
  have hRt_le : Rt.card ≤ n := (Finset.card_filter_le _ _).trans hcard
  let Code := Σ t : Fin (K + 1), (Fin t.val → { r // r ∈ Rpos }) × { r // r ∈ Rt }
  let decode : Code → List T := fun ⟨_, f, rt⟩ ↦
    ((List.ofFn f).map fun e ↦ e.1.prefixWord).flatten ++ rt.1.prefixWord
  have hsub : S ⊆ Finset.univ.image decode := by
    intro w hw
    obtain ⟨hwL, hwK⟩ := hS w hw
    obtain ⟨es, rt, hlen, rfl⟩ := hdecomp G.initial w ((G.mem_language_iff w).mp hwL)
    have ht : es.length < K + 1 := Nat.lt_succ_of_le (hlen.trans hwK)
    refine Finset.mem_image.mpr ⟨⟨⟨es.length, ht⟩, fun i ↦ es[i.val], rt⟩, Finset.mem_univ _, ?_⟩
    dsimp only [decode]
    rw [List.ofFn_getElem]
  have hCode_card : Fintype.card Code ≤ n * (K + 1) * (n - 1) ^ K := by
    rw [Fintype.card_sigma]
    have hterm : ∀ t : Fin (K + 1),
        Fintype.card ((Fin t.val → { r // r ∈ Rpos }) × { r // r ∈ Rt }) ≤
          n * (n - 1) ^ K := fun t ↦ by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Fintype.card_coe]
      have hp1 : Rpos.card ^ t.val ≤ (n - 1) ^ t.val := Nat.pow_le_pow_left hRpos_le _
      have hp2 : (n - 1) ^ t.val ≤ (n - 1) ^ K :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ t.isLt)
      calc Rpos.card ^ t.val * Rt.card
          ≤ (n - 1) ^ K * n := Nat.mul_le_mul (hp1.trans hp2) hRt_le
        _ = n * (n - 1) ^ K := Nat.mul_comm _ _
    calc ∑ t : Fin (K + 1), Fintype.card ((Fin t.val → { r // r ∈ Rpos }) × { r // r ∈ Rt })
        ≤ ∑ _ : Fin (K + 1), n * (n - 1) ^ K := Finset.sum_le_sum fun t _ ↦ hterm t
      _ = (K + 1) * (n * (n - 1) ^ K) := by simp
      _ = n * (K + 1) * (n - 1) ^ K := by ring
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simpa using hCode_card))

/-- `HasDFAStateBound n L` (`REG_n^Z`) holds when `L` is accepted by a finite-state `DFA` with at
most `n` states. -/
def HasDFAStateBound (n : ℕ) (L : _root_.Language T) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : _root_.DFA T σ), Fintype.card σ ≤ n ∧ M.accepts = L

private lemma hasDFAStateBound_helper.{w, w', u'} {T : Type u'} {n : ℕ} {L : _root_.Language T}
    (hL : ∃ (σ : Type w) (_ : Fintype σ) (M : _root_.DFA T σ),
      Fintype.card σ ≤ n ∧ M.accepts = L) :
    ∃ (σ' : Type w') (_ : Fintype σ') (M' : _root_.DFA T σ'),
      Fintype.card σ' ≤ n ∧ M'.accepts = L :=
  let ⟨σ, _, M, hcard, hM⟩ := hL
  let ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{w', w} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f,
    (Fintype.ofEquiv_card f).symm ▸ hcard, hM ▸ _root_.DFA.accepts_reindex M f⟩

/-- Universe-polymorphic characterization of `Language.HasDFAStateBound`. -/
theorem hasDFAStateBound_iff {T : Type u} {n : ℕ} {L : _root_.Language T} :
    HasDFAStateBound n L ↔
      ∃ (σ : Type v) (_ : Fintype σ) (M : _root_.DFA T σ), Fintype.card σ ≤ n ∧ M.accepts = L := by
  unfold HasDFAStateBound
  exact ⟨hasDFAStateBound_helper.{0, v, u}, hasDFAStateBound_helper.{v, 0, u}⟩

/-- Inclusion `REG_n^Z ⊆ RL_n^V` over any finite alphabet `T`. -/
theorem HasDFAStateBound.hasRightLinearVarBound [Finite T] {n : ℕ} {L : _root_.Language T}
    (h : HasDFAStateBound n L) : HasRightLinearVarBound n L := by
  have _ : Fintype T := Fintype.ofFinite T
  obtain ⟨σ, _, M, hcard, rfl⟩ := h
  exact ⟨DFA.toRightLinearGrammar M, by simpa using hcard, DFA.language_toRightLinearGrammar M⟩

section RuleToVarElimination

private inductive GeneratesIn (G : RightLinearGrammar T) : ℕ → G.NT → List T → Prop
  | term {A : G.NT} {w : List T} (hr : ⟨A, w, none⟩ ∈ G.rules) : GeneratesIn G 0 A w
  | nonterm {k : ℕ} {A B : G.NT} {p w : List T} (hr : ⟨A, p, some B⟩ ∈ G.rules)
      (hrest : GeneratesIn G k B w) : GeneratesIn G (k + 1) A (p ++ w)

private lemma generates_iff_exists_generatesIn (G : RightLinearGrammar T)
    (A : G.NT) (w : List T) : G.Generates A w ↔ ∃ k, GeneratesIn G k A w := by
  constructor
  · intro h; induction h with
    | term hr => exact ⟨0, GeneratesIn.term hr⟩
    | nonterm hr _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, GeneratesIn.nonterm hr hk⟩
  · rintro ⟨k, hk⟩; induction hk with
    | term hr => exact RightLinearGrammar.Generates.term hr
    | nonterm hr _ ih => exact RightLinearGrammar.Generates.nonterm hr ih

private lemma card_subtype_ne_lt {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card { x : α // x ≠ a } < Fintype.card α := by
  let e : { x : α // x ≠ a } ⊕ Unit ≃ α :=
    { toFun := Sum.elim Subtype.val (fun _ ↦ a)
      invFun := fun x ↦ if hx : x = a then Sum.inr () else Sum.inl ⟨x, hx⟩
      left_inv := by rintro (⟨x, hx⟩ | ⟨⟩) <;> simp [*]
      right_inv := fun x ↦ by by_cases hx : x = a <;> simp [hx] }
  have hcard : Fintype.card { x : α // x ≠ a } + 1 = Fintype.card α := by
    simpa using Fintype.card_congr e
  omega

private lemma card_image_attach_filter_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : { x : α // x ∈ s.filter p } → β) :
    ((s.filter p).attach.image f).card ≤ s.card :=
  Finset.card_image_le.trans ((Finset.card_attach).le.trans (Finset.card_filter_le _ _))

private def liftRule {T N : Type*} {A : N} (r : RightLinearRule T { X : N // X ≠ A }) :
    RightLinearRule T N := ⟨r.lhs.1, r.prefixWord, r.rhs.map Subtype.val⟩

private lemma elim_dead_nonterminal (G : RightLinearGrammar T) {A : G.NT}
    (hA : A ≠ G.initial) (hdead : ∀ w, ¬ G.Generates A w) :
    ∃ G' : RightLinearGrammar T, Fintype.card G'.NT < Fintype.card G.NT ∧
      G'.rules.card ≤ G.rules.card ∧ G'.language = G.language := by
  classical
  let S := G.rules.filter (fun r ↦ r.lhs ≠ A ∧ r.rhs ≠ some A)
  let proj : { r : RightLinearRule T G.NT // r ∈ S } →
      RightLinearRule T { X : G.NT // X ≠ A } :=
    fun r ↦ ⟨⟨r.1.lhs, (Finset.mem_filter.mp r.2).2.1⟩, r.1.prefixWord, match h : r.1.rhs with
      | none => none
      | some B =>
        some ⟨B, fun hBA ↦ (Finset.mem_filter.mp r.2).2.2 (h.trans (congrArg some hBA))⟩⟩
  let G' : RightLinearGrammar T :=
    ⟨{ X : G.NT // X ≠ A }, inferInstance, ⟨G.initial, hA.symm⟩, S.attach.image proj⟩
  have hmem_lift : ∀ r' ∈ G'.rules, liftRule r' ∈ G.rules := by
    rintro r' hr'; obtain ⟨⟨r, hrS⟩, _, rfl⟩ := Finset.mem_image.mp hr'
    have hlift : liftRule (proj ⟨r, hrS⟩) = r := by rcases r with ⟨_, _, _ | _⟩ <;> rfl
    have hrG := (Finset.mem_filter.mp hrS).1; rwa [← hlift] at hrG
  refine ⟨G', card_subtype_ne_lt A, card_image_attach_filter_le _ _ _, ?_⟩
  ext w; simp only [RightLinearGrammar.mem_language_iff]
  constructor
  · intro hg
    have hgen : ∀ (X' : G'.NT) (w : List T), G'.Generates X' w → G.Generates X'.1 w := by
      intro X' w hg'; induction hg' with
      | @term X' w hr => exact RightLinearGrammar.Generates.term (hmem_lift _ hr)
      | @nonterm X' Y' p w hr _ ih =>
        exact RightLinearGrammar.Generates.nonterm (hmem_lift _ hr) ih
    exact hgen ⟨G.initial, hA.symm⟩ w hg
  · intro hg
    have hgen' : ∀ (X : G.NT) (w : List T),
        G.Generates X w → (hX : X ≠ A) → G'.Generates ⟨X, hX⟩ w := by
      intro X w hg hX; induction hg with
      | @term X w hr =>
        have hrS : ⟨X, w, none⟩ ∈ S := Finset.mem_filter.mpr ⟨hr, hX, by simp⟩
        exact RightLinearGrammar.Generates.term
          (Finset.mem_image.mpr ⟨⟨⟨X, w, none⟩, hrS⟩, Finset.mem_attach _ _, rfl⟩)
      | @nonterm X Y p w hr hrest ih =>
        have hY : Y ≠ A := fun hYA ↦ hdead w (hYA ▸ hrest)
        have hrS : ⟨X, p, some Y⟩ ∈ S := Finset.mem_filter.mpr ⟨hr, hX, by simp [hY]⟩
        have hr' : ⟨⟨X, hX⟩, p, some ⟨Y, hY⟩⟩ ∈ G'.rules := by
          refine Finset.mem_image.mpr ⟨⟨⟨X, p, some Y⟩, hrS⟩, Finset.mem_attach _ _, ?_⟩
          ext <;> simp [proj]
        exact RightLinearGrammar.Generates.nonterm hr' (ih hY)
    exact hgen' G.initial w hg hA.symm

private lemma elim_unique_nonterminal (G : RightLinearGrammar T) {A : G.NT}
    (hA : A ≠ G.initial) {r₀ : RightLinearRule T G.NT} (hr₀ : r₀ ∈ G.rules)
    (hr₀_lhs : r₀.lhs = A) (hr₀_rhs : r₀.rhs ≠ some A)
    (huniq : ∀ r ∈ G.rules, r.lhs = A → r = r₀) :
    ∃ G' : RightLinearGrammar T,
      Fintype.card G'.NT < Fintype.card G.NT ∧
      G'.rules.card ≤ G.rules.card ∧ G'.language = G.language := by
  classical
  rcases r₀ with ⟨lhs₀, p₀, rhs₀⟩
  dsimp only at hr₀_lhs hr₀_rhs
  subst lhs₀
  let target : Option { X : G.NT // X ≠ A } :=
    match rhs₀ with
    | none => none
    | some C => some ⟨C, fun hCA ↦ hr₀_rhs (congrArg some hCA)⟩
  let S := G.rules.filter (fun r ↦ r.lhs ≠ A)
  let substRule : { r : RightLinearRule T G.NT // r ∈ S } →
      RightLinearRule T { X : G.NT // X ≠ A } :=
    fun r ↦
      let lhs' : { X : G.NT // X ≠ A } := ⟨r.1.lhs, (Finset.mem_filter.mp r.2).2⟩
      match r.1.rhs with
      | none => ⟨lhs', r.1.prefixWord, none⟩
      | some Y =>
        if hY : Y = A then ⟨lhs', r.1.prefixWord ++ p₀, target⟩
        else ⟨lhs', r.1.prefixWord, some ⟨Y, hY⟩⟩
  let G' : RightLinearGrammar T :=
    ⟨{ X : G.NT // X ≠ A }, inferInstance, ⟨G.initial, hA.symm⟩, S.attach.image substRule⟩
  have hrule_sound : ∀ r' ∈ G'.rules,
      (r'.rhs = none → G.Generates r'.lhs.1 r'.prefixWord) ∧
      (∀ Y' v, r'.rhs = some Y' → G.Generates Y'.1 v →
        G.Generates r'.lhs.1 (r'.prefixWord ++ v)) := by
    intro r' hr'
    obtain ⟨⟨⟨lhs, pref, rhs⟩, hrS⟩, _, rfl⟩ := Finset.mem_image.mp hr'
    have hrG : ⟨lhs, pref, rhs⟩ ∈ G.rules := (Finset.mem_filter.mp hrS).1
    rcases rhs with _ | Y
    · refine ⟨fun _ ↦ RightLinearGrammar.Generates.term hrG, fun _ _ hbad _ ↦ ?_⟩
      simp only [substRule] at hbad; cases hbad
    · by_cases hYA : Y = A
      · subst hYA
        cases rhs₀ with
        | none =>
          refine ⟨fun _ ↦ ?_, fun _ _ hbad _ ↦ ?_⟩
          · simp only [substRule, ↓reduceDIte]
            exact RightLinearGrammar.Generates.nonterm hrG (RightLinearGrammar.Generates.term hr₀)
          · simp only [substRule, ↓reduceDIte, target] at hbad; cases hbad
        | some C =>
          refine ⟨fun hbad ↦ ?_, fun Y' v hsome hv ↦ ?_⟩
          · simp only [substRule, ↓reduceDIte, target] at hbad; cases hbad
          · simp only [substRule, ↓reduceDIte, target, Option.some.injEq] at hsome
            have hCY : C = Y'.1 := congrArg Subtype.val hsome
            simp only [substRule, ↓reduceDIte]
            rw [List.append_assoc]
            exact RightLinearGrammar.Generates.nonterm hrG
              (RightLinearGrammar.Generates.nonterm hr₀ (hCY ▸ hv))
      · refine ⟨fun hbad ↦ ?_, fun Y' v hsome hv ↦ ?_⟩
        · simp only [substRule] at hbad; rw [dite_eq_right hYA] at hbad; cases hbad
        · simp only [substRule] at hsome; rw [dite_eq_right hYA] at hsome
          have hYY' : Y = Y'.1 := congrArg Subtype.val (Option.some.inj hsome)
          simp only [substRule]; rw [dite_eq_right hYA]
          exact RightLinearGrammar.Generates.nonterm hrG (hYY' ▸ hv)
  refine ⟨G', card_subtype_ne_lt A, card_image_attach_filter_le _ _ _, ?_⟩
  ext w; simp only [RightLinearGrammar.mem_language_iff]
  constructor
  · intro hg
    have hgen : ∀ (X' : G'.NT) (w : List T), G'.Generates X' w → G.Generates X'.1 w := by
      intro X' w hg'
      induction hg' with
      | term hr => exact (hrule_sound _ hr).1 rfl
      | nonterm hr _ ih => exact (hrule_sound _ hr).2 _ _ rfl ih
    exact hgen ⟨G.initial, hA.symm⟩ w hg
  · intro hg
    obtain ⟨k, hk⟩ := (generates_iff_exists_generatesIn G G.initial w).mp hg
    have hgen' : ∀ k (X : G.NT) (w : List T),
        GeneratesIn G k X w → (hX : X ≠ A) → G'.Generates ⟨X, hX⟩ w := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro X w hgin hX
        cases hgin with
        | term hr =>
          have hrS : ⟨X, w, none⟩ ∈ S := Finset.mem_filter.mpr ⟨hr, hX⟩
          exact RightLinearGrammar.Generates.term
            (Finset.mem_image.mpr ⟨⟨⟨X, w, none⟩, hrS⟩, Finset.mem_attach _ _, rfl⟩)
        | @nonterm k' _ Y p w' hr hrest =>
          have hrS : ⟨X, p, some Y⟩ ∈ S := Finset.mem_filter.mpr ⟨hr, hX⟩
          by_cases hYA : Y = A
          · subst hYA
            cases hrest with
            | term hrA =>
              have hreq := huniq _ hrA rfl
              have hw' : w' = p₀ := congrArg RightLinearRule.prefixWord hreq
              have hrhs_eq : rhs₀ = none := (congrArg RightLinearRule.rhs hreq).symm
              have htarget : target = none := by subst hrhs_eq; rfl
              have hr' : ⟨⟨X, hX⟩, p ++ p₀, none⟩ ∈ G'.rules :=
                Finset.mem_image.mpr ⟨⟨⟨X, p, some Y⟩, hrS⟩, Finset.mem_attach _ _,
                  by simp [substRule, htarget]⟩
              rw [hw']; exact RightLinearGrammar.Generates.term hr'
            | @nonterm k'' _ D pA w'' hrA hrest' =>
              have hreq := huniq _ hrA rfl
              have hpA : pA = p₀ := congrArg RightLinearRule.prefixWord hreq
              have hrhs_eq : rhs₀ = some D := (congrArg RightLinearRule.rhs hreq).symm
              have hDA : D ≠ Y := fun hD ↦ hr₀_rhs (hrhs_eq.trans (congrArg some hD))
              have htarget : target = some ⟨D, hDA⟩ := by subst hrhs_eq; rfl
              have hr' : ⟨⟨X, hX⟩, p ++ p₀, some ⟨D, hDA⟩⟩ ∈ G'.rules :=
                Finset.mem_image.mpr ⟨⟨⟨X, p, some Y⟩, hrS⟩, Finset.mem_attach _ _,
                  by simp [substRule, htarget]⟩
              rw [hpA, ← List.append_assoc]
              exact RightLinearGrammar.Generates.nonterm hr'
                (ih k'' (by omega) D w'' hrest' hDA)
          · have hr' : ⟨⟨X, hX⟩, p, some ⟨Y, hYA⟩⟩ ∈ G'.rules :=
              Finset.mem_image.mpr ⟨⟨⟨X, p, some Y⟩, hrS⟩, Finset.mem_attach _ _,
                by simp [substRule, hYA]⟩
            exact RightLinearGrammar.Generates.nonterm hr' (ih k' (by omega) Y w' hrest hYA)
    exact hgen' k G.initial w hk hA.symm

private lemma elim_nonterminal (G : RightLinearGrammar T) {A : G.NT}
    (hA : A ≠ G.initial)
    (huniq : ∀ r₁ ∈ G.rules, ∀ r₂ ∈ G.rules, r₁.lhs = A → r₂.lhs = A → r₁ = r₂) :
    ∃ G' : RightLinearGrammar T,
      Fintype.card G'.NT < Fintype.card G.NT ∧
      G'.rules.card ≤ G.rules.card ∧ G'.language = G.language := by
  by_cases hex : ∃ r₀ ∈ G.rules, r₀.lhs = A
  · obtain ⟨r₀, hr₀, hr₀_lhs⟩ := hex
    have huniq' : ∀ r ∈ G.rules, r.lhs = A → r = r₀ :=
      fun r hr hlhs ↦ huniq r hr r₀ hr₀ hlhs hr₀_lhs
    by_cases hr₀_rhs : r₀.rhs = some A
    · have hdead : ∀ w, ¬ G.Generates A w := by
        intro w hg; obtain ⟨k, hk⟩ := (generates_iff_exists_generatesIn G A w).mp hg
        have himp : ∀ k w, ¬ GeneratesIn G k A w := by
          intro k; induction k with
          | zero =>
            intro w hgin; cases hgin with | term hr =>
              have h0 := congrArg RightLinearRule.rhs (huniq' _ hr rfl)
              rw [hr₀_rhs] at h0; cases h0
          | succ k ih =>
            intro w hgin; cases hgin with | nonterm hr hrest =>
              have h0 := congrArg RightLinearRule.rhs (huniq' _ hr rfl)
              rw [hr₀_rhs] at h0; cases h0; exact ih _ hrest
        exact himp k w hk
      exact elim_dead_nonterminal G hA hdead
    · exact elim_unique_nonterminal G hA hr₀ hr₀_lhs hr₀_rhs huniq'
  · push Not at hex
    have hdead : ∀ w, ¬ G.Generates A w := fun w hg ↦ by
      cases hg with | term hr => exact hex _ hr rfl | nonterm hr _ => exact hex _ hr rfl
    exact elim_dead_nonterminal G hA hdead

end RuleToVarElimination

/-- Inclusion `RL_{2n}^P ⊆ RL_n^V` for every `1 ≤ n`. -/
theorem HasRightLinearRuleBound.hasRightLinearVarBound_of_two_mul {n : ℕ} (hn : 1 ≤ n)
    {L : _root_.Language T} (h : HasRightLinearRuleBound (2 * n) L) :
    HasRightLinearVarBound n L := by
  classical
  obtain ⟨G, hrcard, hL⟩ := h
  have hred : ∀ k (G : RightLinearGrammar T), Fintype.card G.NT = k →
      G.rules.card ≤ 2 * n → G.language = L → HasRightLinearVarBound n L := by
    intro k; induction k using Nat.strong_induction_on with | ind k ih =>
      intro G hk hrcard hlang
      by_cases hex : ∃ A : G.NT, A ≠ G.initial ∧ (G.rules.filter (fun r ↦ r.lhs = A)).card ≤ 1
      · obtain ⟨A, hA, hcardA⟩ := hex
        have huniq : ∀ r₁ ∈ G.rules, ∀ r₂ ∈ G.rules, r₁.lhs = A → r₂.lhs = A → r₁ = r₂ :=
          fun r₁ hr₁ r₂ hr₂ h₁ h₂ ↦ Finset.card_le_one.mp hcardA r₁
            (Finset.mem_filter.mpr ⟨hr₁, h₁⟩) r₂ (Finset.mem_filter.mpr ⟨hr₂, h₂⟩)
        obtain ⟨G', hlt, hrcard', hlang'⟩ := elim_nonterminal G hA huniq
        exact ih (Fintype.card G'.NT) (hk ▸ hlt) G' rfl (hrcard'.trans hrcard)
          (hlang'.trans hlang)
      · push Not at hex
        by_cases hinit : (G.rules.filter (fun r ↦ r.lhs = G.initial)).card = 0
        · have hno : ∀ r ∈ G.rules, r.lhs ≠ G.initial := fun r hr hlhs ↦ by
            have hmem : r ∈ G.rules.filter (fun r ↦ r.lhs = G.initial) :=
              Finset.mem_filter.mpr ⟨hr, hlhs⟩
            rw [Finset.card_eq_zero.mp hinit] at hmem; simp at hmem
          have hzero : L = 0 := hlang ▸ G.language_eq_zero_of_forall_lhs_ne_initial hno
          refine ⟨⟨Unit, inferInstance, (), ∅⟩, by simpa using hn, ?_⟩
          exact hzero ▸ RightLinearGrammar.language_eq_zero_of_forall_lhs_ne_initial _
            (fun _ hr ↦ by simp at hr)
        · have hinit_pos : 1 ≤ (G.rules.filter (fun r ↦ r.lhs = G.initial)).card :=
            Nat.pos_of_ne_zero hinit
          have hpart : G.rules.card = ∑ A : G.NT, (G.rules.filter (fun r ↦ r.lhs = A)).card :=
            Finset.card_eq_sum_card_fiberwise (fun r _ ↦ Finset.mem_univ r.lhs)
          have hsplit : ∑ A : G.NT, (G.rules.filter (fun r ↦ r.lhs = A)).card =
              (G.rules.filter (fun r ↦ r.lhs = G.initial)).card +
                ∑ A ∈ Finset.univ.erase G.initial, (G.rules.filter (fun r ↦ r.lhs = A)).card :=
            (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ G.initial)).symm
          have hother : 2 * (Finset.univ.erase G.initial : Finset G.NT).card ≤
              ∑ A ∈ Finset.univ.erase G.initial, (G.rules.filter (fun r ↦ r.lhs = A)).card := by
            calc 2 * (Finset.univ.erase G.initial : Finset G.NT).card
                = ∑ _ ∈ Finset.univ.erase G.initial, 2 := by
                    rw [Finset.sum_const_nat (fun _ _ ↦ rfl), mul_comm]
              _ ≤ ∑ A ∈ Finset.univ.erase G.initial,
                    (G.rules.filter (fun r ↦ r.lhs = A)).card :=
                  Finset.sum_le_sum fun A hA ↦ hex A (Finset.ne_of_mem_erase hA)
          have herase : (Finset.univ.erase G.initial : Finset G.NT).card =
              Fintype.card G.NT - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ G.initial), Finset.card_univ]
          have hposNT : 0 < Fintype.card G.NT := Fintype.card_pos_iff.mpr ⟨G.initial⟩
          exact ⟨G, by omega, hlang⟩
  exact hred (Fintype.card G.NT) G rfl hrcard hL

end Language

end AutomataEquivalence

end CslibFrontier.Computability.Languages
