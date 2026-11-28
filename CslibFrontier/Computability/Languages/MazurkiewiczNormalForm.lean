/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Lex
public import CslibFrontier.Computability.Languages.MazurkiewiczTrace

import Mathlib.Data.List.Count

/-!
# Lexicographic Normal Forms and Predictive Membership for Mazurkiewicz Traces

This module builds on `CslibFrontier.Computability.Languages.MazurkiewiczTrace` to develop:

- Lexicographic normal forms of Mazurkiewicz traces, their forbidden-factor characterization,
  prefix closure, and the Diekert–Rozenberg DFA recognizing `lexNormalFormSet C` with
  `2 ^ |Σ| + 1` states.
- The Bertoni–Mauri–Sabadini predictive membership dynamic-programming reachability predicate
  characterizing membership in the trace closure `[L(A)]_I` of a regular language.

## Main definitions

- `Cslib.Language.WordLexLt`: strict lexicographic order on words.
- `Cslib.Language.traceClassFinset`: the finite trace equivalence class of
  a word.
- `Cslib.Language.lexNormalForm`: lexicographically minimal representative
  of a trace equivalence class.
- `Cslib.Language.lexNormalFormSet`: language of all lexicographic normal
  forms over `C`.
- `Cslib.Language.lexNormalFormDFA`: recognizing DFA for
  `lexNormalFormSet C` with `2 ^ |Σ| + 1` states.
- `Cslib.Language.countVec`,
  `Cslib.Language.IsDAGPrefixCount`,
  `Cslib.Language.ReachableDAGPrefix`: letter-count vectors and the
  Bertoni–Mauri–Sabadini dynamic-programming reachability predicate.

## Main results

- `Cslib.Language.mem_lexNormalFormSet_iff_no_forbidden_factor`:
  forbidden-factor characterization of lexicographic normal forms.
- `Cslib.Language.lexNormalFormSet_prefix_closed`: prefix closure of
  lexicographic normal forms.
- `Cslib.Language.language_lexNormalFormDFA`,
  `Cslib.Language.isRegular_lexNormalFormSet`: regularity of the
  lexicographic normal-form language (Diekert–Rozenberg).
- `Cslib.Language.reachableDAGPrefix_iff_exists_dagPrefix`,
  `Cslib.Language.mem_traceClosure_iff_reachableDAGPrefix`: correctness
  of the Bertoni–Mauri–Sabadini predictive membership dynamic program.
-/

public section

namespace Cslib.Language

universe u v

/-! ### Lexicographic normal forms and Diekert–Rozenberg regularity -/

section LexNormalForm

variable {Γ : Type u} [LinearOrder Γ]

/-- The strict lexicographic order on words of equal length. -/
def WordLexLt (u v : List Γ) : Prop := List.Lex (· < ·) u v

theorem wordLexLt_iff (u v : List Γ) : WordLexLt u v ↔ List.Lex (· < ·) u v :=
  Iff.rfl

theorem wordLexLt_rel {a b : Γ} (h : a < b) (u v : List Γ) :
    WordLexLt (a :: u) (b :: v) :=
  List.Lex.rel h

theorem wordLexLt_irrefl (u : List Γ) : ¬WordLexLt u u := by
  induction u with
  | nil => intro h; cases h
  | cons a u ih =>
    intro h
    cases h with
    | rel hlt => exact lt_irrefl a hlt
    | cons h' => exact ih h'

theorem wordLexLt_trans {u v w : List Γ} (h₁ : WordLexLt u v) (h₂ : WordLexLt v w) :
    WordLexLt u w := by
  induction h₁ generalizing w with
  | nil =>
    cases h₂ with
    | cons _ => exact List.Lex.nil
    | rel _ => exact List.Lex.nil
  | rel hlt =>
    cases h₂ with
    | rel hlt' => exact List.Lex.rel (hlt.trans hlt')
    | cons _ => exact List.Lex.rel hlt
  | cons _ ih =>
    cases h₂ with
    | rel hlt' => exact List.Lex.rel hlt'
    | cons h' => exact List.Lex.cons (ih h')

private theorem wordLexLt_total_of_length_eq {u v : List Γ} (hlen : u.length = v.length) :
    WordLexLt u v ∨ u = v ∨ WordLexLt v u := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact Or.inr (Or.inl rfl)
    | cons _ _ => simp at hlen
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact Or.inl (List.Lex.rel hlt)
      · rcases ih (by simpa using hlen) with h | rfl | h
        · exact Or.inl (List.Lex.cons h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (List.Lex.cons h))
      · exact Or.inr (Or.inr (List.Lex.rel hgt))

theorem wordLexLt_append_left (p : List Γ) {u v : List Γ} (h : WordLexLt u v) :
    WordLexLt (p ++ u) (p ++ v) := by
  induction p with
  | nil => exact h
  | cons a p ih => exact List.Lex.cons ih

/-- The finite equivalence class of a word `w` under trace equivalence. -/
noncomputable def traceClassFinset {Γ : Type u} (C : ConcurrentAlphabet Γ) (w : List Γ) :
    Finset (List Γ) := by
  classical
  exact w.permutations.toFinset.filter fun u => TraceEquiv C u w

omit [LinearOrder Γ] in
theorem mem_traceClassFinset_iff {C : ConcurrentAlphabet Γ} {w u : List Γ} :
    u ∈ traceClassFinset C w ↔ TraceEquiv C u w := by
  classical
  simp only [traceClassFinset, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  exact ⟨fun h => h.2, fun h => ⟨h.perm, h⟩⟩

omit [LinearOrder Γ] in
theorem traceClassFinset_nonempty (C : ConcurrentAlphabet Γ) (w : List Γ) :
    (traceClassFinset C w).Nonempty :=
  ⟨w, mem_traceClassFinset_iff.mpr (TraceEquiv.refl w)⟩

private theorem exists_lex_min_in_finset (S : Finset (List Γ)) (hne : S.Nonempty)
    (heq_len : ∀ u ∈ S, ∀ v ∈ S, u.length = v.length) :
    ∃ m ∈ S, ∀ u ∈ S, m = u ∨ WordLexLt m u := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | @insert x s hx ih =>
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · exact ⟨x, Finset.mem_singleton_self x, fun u hu => Or.inl (Finset.mem_singleton.mp hu).symm⟩
    · obtain ⟨m, hm, hmin⟩ := ih hsne fun u hu v hv =>
        heq_len u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv)
      have hlen_xm : x.length = m.length :=
        heq_len x (Finset.mem_insert_self x s) m (Finset.mem_insert_of_mem hm)
      rcases wordLexLt_total_of_length_eq hlen_xm with hlt | rfl | hgt
      · refine ⟨x, Finset.mem_insert_self x s, fun u hu => ?_⟩
        rcases Finset.mem_insert.mp hu with rfl | hus
        · exact Or.inl rfl
        · rcases hmin u hus with rfl | hmu
          · exact Or.inr hlt
          · exact Or.inr (wordLexLt_trans hlt hmu)
      · refine ⟨x, Finset.mem_insert_self x s, fun u hu => ?_⟩
        rcases Finset.mem_insert.mp hu with rfl | hus
        · exact Or.inl rfl
        · exact hmin u hus
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun u hu => ?_⟩
        rcases Finset.mem_insert.mp hu with rfl | hus
        · exact Or.inr hgt
        · exact hmin u hus

private theorem exists_lexNormalForm (C : ConcurrentAlphabet Γ) (w : List Γ) :
    ∃ m, TraceEquiv C m w ∧ ∀ u, TraceEquiv C u w → m = u ∨ WordLexLt m u := by
  obtain ⟨m, hm, hmin⟩ := exists_lex_min_in_finset (traceClassFinset C w)
    (traceClassFinset_nonempty C w) fun u hu v hv =>
      ((mem_traceClassFinset_iff.mp hu).trans (mem_traceClassFinset_iff.mp hv).symm).length_eq
  exact ⟨m, mem_traceClassFinset_iff.mp hm, fun u hu => hmin u (mem_traceClassFinset_iff.mpr hu)⟩

/-- The lexicographic normal form of a word `w`: the lexicographically smallest word in its
Mazurkiewicz trace equivalence class. -/
noncomputable def lexNormalForm (C : ConcurrentAlphabet Γ) (w : List Γ) : List Γ :=
  (exists_lexNormalForm C w).choose

theorem lexNormalForm_equiv (C : ConcurrentAlphabet Γ) (w : List Γ) :
    TraceEquiv C (lexNormalForm C w) w :=
  (exists_lexNormalForm C w).choose_spec.1

theorem lexNormalForm_le (C : ConcurrentAlphabet Γ) {w u : List Γ} (h : TraceEquiv C u w) :
    lexNormalForm C w = u ∨ WordLexLt (lexNormalForm C w) u :=
  (exists_lexNormalForm C w).choose_spec.2 u h

theorem lexNormalForm_eq_of_equiv {C : ConcurrentAlphabet Γ} {u v : List Γ}
    (h : TraceEquiv C u v) : lexNormalForm C u = lexNormalForm C v := by
  have h1 := lexNormalForm_le C ((lexNormalForm_equiv C v).trans h.symm)
  have h2 := lexNormalForm_le C ((lexNormalForm_equiv C u).trans h)
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2.symm
    · exact absurd (wordLexLt_trans h1 h2) (wordLexLt_irrefl _)

theorem lexNormalForm_eq_iff {C : ConcurrentAlphabet Γ} {u v : List Γ} :
    lexNormalForm C u = lexNormalForm C v ↔ TraceEquiv C u v :=
  ⟨fun h => (lexNormalForm_equiv C u).symm.trans (h ▸ lexNormalForm_equiv C v),
    lexNormalForm_eq_of_equiv⟩

@[simp]
theorem lexNormalForm_nil (C : ConcurrentAlphabet Γ) : lexNormalForm C [] = [] := by
  have h := (lexNormalForm_equiv C []).length_eq
  exact List.eq_nil_of_length_eq_zero (by simpa using h)

@[simp]
theorem lexNormalForm_idempotent (C : ConcurrentAlphabet Γ) (w : List Γ) :
    lexNormalForm C (lexNormalForm C w) = lexNormalForm C w :=
  lexNormalForm_eq_of_equiv (lexNormalForm_equiv C w)

/-- The language of all lexicographic normal forms over `C`. -/
def lexNormalFormSet (C : ConcurrentAlphabet Γ) : Language Γ :=
  {w | lexNormalForm C w = w}

theorem mem_lexNormalFormSet_iff_eq {C : ConcurrentAlphabet Γ} {w : List Γ} :
    w ∈ lexNormalFormSet C ↔ lexNormalForm C w = w :=
  Iff.rfl

theorem lexNormalForm_mem_lexNormalFormSet (C : ConcurrentAlphabet Γ) (w : List Γ) :
    lexNormalForm C w ∈ lexNormalFormSet C :=
  lexNormalForm_idempotent C w

theorem mem_lexNormalFormSet_iff {C : ConcurrentAlphabet Γ} {w : List Γ} :
    w ∈ lexNormalFormSet C ↔ ∀ u, TraceEquiv C u w → w = u ∨ WordLexLt w u := by
  constructor
  · intro hw u hu
    rw [← hw]
    exact lexNormalForm_le C hu
  · intro h
    rcases h (lexNormalForm C w) (lexNormalForm_equiv C w) with heq | hlt
    · exact heq.symm
    · rcases lexNormalForm_le C (TraceEquiv.refl w) with heq' | hlt'
      · exact heq'
      · exact absurd (wordLexLt_trans hlt hlt') (wordLexLt_irrefl _)

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

/-- **Forbidden-factor characterization of lexicographic normal forms**:
`w ∈ L_NF` iff `w` contains no factor `b :: u ++ [a]` with `a < b` and `a` independent of `b`
and every letter of `u`. -/
theorem mem_lexNormalFormSet_iff_no_forbidden_factor {C : ConcurrentAlphabet Γ} {w : List Γ} :
    w ∈ lexNormalFormSet C ↔
      ∀ (p u s : List Γ) (a b : Γ),
        w = p ++ b :: u ++ a :: s → a < b → C.indep a b → (∀ x ∈ u, C.indep a x) → False := by
  classical
  constructor
  · intro hw p u s a b hEq hab hind_b hind_u
    have hcomm := TraceEquiv.comm_of_forall_indep (a := a) (v := b :: u)
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hxu
        · exact hind_b
        · exact hind_u x hxu)
    have hteq : TraceEquiv C (p ++ a :: b :: u ++ s) w := by
      rw [hEq]
      have h1 : TraceEquiv C ((b :: u) ++ [a]) (a :: b :: u) := hcomm
      have h2 := TraceEquiv.append_left p (TraceEquiv.append_right s h1.symm)
      simpa [List.append_assoc] using h2
    have hlex : WordLexLt (p ++ a :: b :: u ++ s) w := by
      rw [hEq]
      simpa [List.append_assoc] using wordLexLt_append_left p (List.Lex.rel hab)
    rcases (mem_lexNormalFormSet_iff.mp hw) _ hteq with heq | hlt
    · rw [← heq] at hlex; exact wordLexLt_irrefl _ hlex
    · exact wordLexLt_irrefl _ (wordLexLt_trans hlt hlex)
  · intro hforb
    rw [mem_lexNormalFormSet_iff]
    intro v hv
    rcases wordLexLt_total_of_length_eq hv.length_eq.symm with hlt | heq | hgt
    · exact Or.inr hlt
    · exact Or.inl heq
    · exfalso
      have hex_diff : ∃ p a b r r', v = p ++ a :: r ∧ w = p ++ b :: r' ∧ a < b := by
        have hlen := hv.length_eq
        clear hv hforb
        induction hgt with
        | nil => simp at hlen
        | rel h => exact ⟨[], _, _, _, _, rfl, rfl, h⟩
        | @cons x _ _ _ ih =>
          obtain ⟨p, a, b, r, r', hv', hw', hab⟩ := ih (by simpa using hlen)
          exact ⟨x :: p, a, b, r, r', by simp [hv'], by simp [hw'], hab⟩
      obtain ⟨p, a, b, r, r', hv_eq, hw_eq, hab⟩ := hex_diff
      have hbr : TraceEquiv C (a :: r) (b :: r') :=
        TraceEquiv.cancel_left (p := p) (hv_eq ▸ hw_eq ▸ hv)
      have ha_in : a ∈ b :: r' := hbr.mem_iff.mp (List.mem_cons_self ..)
      have ha_in_r' : a ∈ r' := by
        rcases List.mem_cons.mp ha_in with rfl | h
        · exact absurd rfl (ne_of_lt hab)
        · exact h
      obtain ⟨u, s, rfl, hau⟩ := exists_split_first_mem ha_in_r'
      have hind_all : ∀ x ∈ b :: u, C.indep a x := by
        intro x hx
        by_contra hdep
        have hproj := depProj_eq_of_traceEquiv hbr ((C.dep_iff_not_indep a x).mpr hdep)
        have h1 : (depProj a x (a :: r)).head? = some a := by simp [depProj_cons]
        have hxa : x ≠ a := by
          rcases List.mem_cons.mp hx with rfl | hxu
          · exact ne_of_gt hab
          · exact fun h => hau (h ▸ hxu)
        have h2 : (depProj a x (b :: u)).head? = some x := by
          obtain ⟨p₁, p₂, hp_eq, hxp₁⟩ := exists_split_first_mem hx
          have hap₁ : a ∉ p₁ := by
            intro ha₁
            have hmem : a ∈ b :: u := hp_eq ▸ List.mem_append_left _ ha₁
            rcases List.mem_cons.mp hmem with rfl | hu'
            · exact lt_irrefl _ hab
            · exact hau hu'
          rw [hp_eq, depProj_append, depProj_of_notMem hap₁ hxp₁, List.nil_append, depProj_cons]
          simp
        have hne_bu : depProj a x (b :: u) ≠ [] := by
          intro he; rw [he] at h2; simp at h2
        have h3 : (depProj a x (b :: (u ++ a :: s))).head? = some x := by
          have : b :: (u ++ a :: s) = (b :: u) ++ a :: s := rfl
          rw [this, depProj_append, List.head?_append_of_ne_nil _ hne_bu, h2]
        rw [hproj, h3] at h1
        exact hxa (Option.some.inj h1)
      exact hforb p u s a b (by simpa [List.append_assoc] using hw_eq) hab
        (hind_all b (List.mem_cons_self ..))
        (fun x hx => hind_all x (List.mem_cons_of_mem _ hx))

/-- **Prefix closure of lexicographic normal forms**: every prefix of a lexicographic normal form
is a lexicographic normal form. -/
theorem lexNormalFormSet_prefix_closed {C : ConcurrentAlphabet Γ} {u v : List Γ}
    (h : u ++ v ∈ lexNormalFormSet C) : u ∈ lexNormalFormSet C := by
  rw [mem_lexNormalFormSet_iff_no_forbidden_factor] at h ⊢
  intro p m s a b huEq hab hind_b hind_m
  exact h p m (s ++ v) a b (by simp [List.append_assoc, huEq]) hab hind_b hind_m

/-- The transition function of the recognizing DFA for `lexNormalFormSet C`. State `none` is the
absorbing reject state; state `some flag` records for each `a : Σ` whether a letter `b > a` has
appeared since the last letter dependent on `a`. -/
def lexNormalFormDFAStep (C : ConcurrentAlphabet Γ) [DecidableRel C.indep] :
    Option (Γ → Bool) → Γ → Option (Γ → Bool)
  | none, _ => none
  | some flag, c =>
    if flag c then none
    else some fun a => if C.dep a c then false else (flag a || decide (a < c))

/-- The recognizing DFA for `lexNormalFormSet C` with `2 ^ |Σ| + 1` states. -/
def lexNormalFormDFA (C : ConcurrentAlphabet Γ) [DecidableRel C.indep] :
    Cslib.Automata.DA.FinAcc (Option (Γ → Bool)) Γ where
  tr := lexNormalFormDFAStep C
  start := some (fun _ => false)
  accept := {s | s.isSome}

private theorem lexNormalFormDFA_mtr_spec (C : ConcurrentAlphabet Γ) [DecidableRel C.indep]
    (w : List Γ) :
    ((lexNormalFormDFA C).mtr (some (fun _ => false)) w = none ↔ w ∉ lexNormalFormSet C) ∧
    (∀ flag, (lexNormalFormDFA C).mtr (some (fun _ => false)) w = some flag →
      ∀ a : Γ, flag a = true ↔
        ∃ p u b, w = p ++ b :: u ∧ a < b ∧ C.indep a b ∧ ∀ x ∈ u, C.indep a x) := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp only [Cslib.FLTS.mtr_nil_eq, reduceCtorEq, false_iff, Classical.not_not]
      change lexNormalForm C [] = []
      exact lexNormalForm_nil C
    · intro flag hflag a
      simp only [Cslib.FLTS.mtr_nil_eq, Option.some.injEq] at hflag
      subst hflag
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro p u b hEq
      have := congrArg List.length hEq
      simp at this
  | append_singleton w c ih =>
    obtain ⟨ih_none, ih_some⟩ := ih
    rw [Cslib.FLTS.mtr_concat_eq]
    cases hst : (lexNormalFormDFA C).mtr (some (fun _ => false)) w with
    | none =>
      have hw_not : w ∉ lexNormalFormSet C := ih_none.mp hst
      refine ⟨?_, ?_⟩
      · simp only [lexNormalFormDFA, lexNormalFormDFAStep, true_iff]
        intro hwc
        exact hw_not (lexNormalFormSet_prefix_closed hwc)
      · intro flag hflag
        simp [lexNormalFormDFA, lexNormalFormDFAStep] at hflag
    | some flag =>
      have hw_mem : w ∈ lexNormalFormSet C := by
        by_contra hnot
        have := ih_none.mpr hnot
        rw [hst] at this
        exact Option.some_ne_none _ this
      have hflag_spec := ih_some flag hst
      dsimp only [lexNormalFormDFA, lexNormalFormDFAStep]
      by_cases hfc : flag c = true
      · simp only [hfc, ↓reduceIte, true_iff, reduceCtorEq, IsEmpty.forall_iff]
        refine ⟨fun hwc => ?_, fun _ => trivial⟩
        obtain ⟨p, u, b, hw_eq, hcb, hind_b, hind_u⟩ := (hflag_spec c).mp hfc
        rw [mem_lexNormalFormSet_iff_no_forbidden_factor] at hwc
        exact hwc p u [] c b (by simpa [List.append_assoc] using congrArg (· ++ [c]) hw_eq)
          hcb hind_b hind_u
      · simp only [hfc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, Classical.not_not,
          Option.some.injEq]
        refine ⟨?_, ?_⟩
        · rw [mem_lexNormalFormSet_iff_no_forbidden_factor]
          intro p u s a b hEq hab hind_b hind_u
          cases hs : s using List.reverseRecOn with
          | nil =>
            have hEq' : w ++ [c] = (p ++ b :: u) ++ [a] := by
              simpa [List.append_assoc, hs] using hEq
            obtain ⟨hw_eq, hca⟩ := List.append_inj' hEq' rfl
            have hac : a = c := (List.cons.inj hca).1.symm
            subst hac
            exact hfc ((hflag_spec a).mpr ⟨p, u, b, hw_eq, hab, hind_b, hind_u⟩)
          | append_singleton s' d =>
            have hEq' : w ++ [c] = (p ++ b :: u ++ a :: s') ++ [d] := by
              simpa [List.append_assoc, hs] using hEq
            have hw_eq : w = p ++ b :: u ++ a :: s' := (List.append_inj' hEq' rfl).1
            rw [mem_lexNormalFormSet_iff_no_forbidden_factor] at hw_mem
            exact hw_mem p u s' a b hw_eq hab hind_b hind_u
        · intro flag' hEq a
          subst hEq
          constructor
          · intro ha
            by_cases hdep : C.dep a c
            · simp [hdep] at ha
            · simp only [hdep, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at ha
              have hind_ac : C.indep a c :=
                Classical.not_not.mp ((C.dep_iff_not_indep a c).not.mp hdep)
              rcases ha with hfa | hac
              · obtain ⟨p, u, b, hw_eq, hab, hind_b, hind_u⟩ := (hflag_spec a).mp hfa
                refine ⟨p, u ++ [c], b,
                  by simpa [List.append_assoc] using congrArg (· ++ [c]) hw_eq,
                  hab, hind_b, fun x hx => ?_⟩
                rcases List.mem_append.mp hx with hxu | hxc
                · exact hind_u x hxu
                · rw [List.mem_singleton.mp hxc]; exact hind_ac
              · exact ⟨w, [], c, by simp, hac, hind_ac, fun _ h => absurd h List.not_mem_nil⟩
          · rintro ⟨p, u, b, hEq, hab, hind_b, hind_u⟩
            have hdep_false : ¬C.dep a c := by
              cases hu : u using List.reverseRecOn with
              | nil =>
                have hEq' : w ++ [c] = p ++ [b] := by simpa [List.append_assoc, hu] using hEq
                have hbc : b = c := (List.cons.inj (List.append_inj' hEq' rfl).2).1.symm
                subst hbc
                exact fun hd => (C.dep_iff_not_indep a b).mp hd hind_b
              | append_singleton u' d =>
                have hEq' : w ++ [c] = (p ++ b :: u') ++ [d] := by
                  simpa [List.append_assoc, hu] using hEq
                have hdc : d = c := (List.cons.inj (List.append_inj' hEq' rfl).2).1.symm
                subst hdc
                exact fun hd => (C.dep_iff_not_indep a d).mp hd (hind_u d (by simp [hu]))
            simp only [hdep_false, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq]
            cases hu : u using List.reverseRecOn with
            | nil =>
              have hEq' : w ++ [c] = p ++ [b] := by simpa [List.append_assoc, hu] using hEq
              have hbc : b = c := (List.cons.inj (List.append_inj' hEq' rfl).2).1.symm
              subst hbc
              exact Or.inr hab
            | append_singleton u' d =>
              have hEq' : w ++ [c] = (p ++ b :: u') ++ [d] := by
                simpa [List.append_assoc, hu] using hEq
              have hw_eq : w = p ++ b :: u' := (List.append_inj' hEq' rfl).1
              exact Or.inl ((hflag_spec a).mpr ⟨p, u', b, hw_eq, hab, hind_b,
                fun x hx => hind_u x (by simp [hu, hx])⟩)

theorem language_lexNormalFormDFA (C : ConcurrentAlphabet Γ) [DecidableRel C.indep] :
    Cslib.Automata.Acceptor.language (lexNormalFormDFA C) = lexNormalFormSet C := by
  ext w
  simp only [Cslib.Automata.Acceptor.mem_language]
  change ((lexNormalFormDFA C).mtr (some (fun _ => false)) w).isSome = true ↔ w ∈ lexNormalFormSet C
  have hnone := (lexNormalFormDFA_mtr_spec C w).1
  cases h : (lexNormalFormDFA C).mtr (some (fun _ => false)) w with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact hnone.mp h
  | some _ =>
    simp only [Option.isSome_some, true_iff]
    by_contra hnot
    have := hnone.mpr hnot
    rw [h] at this
    exact Option.some_ne_none _ this

end LexNormalForm

/-- **Diekert–Rozenberg theorem**: the set of lexicographic normal forms over a finite concurrent
alphabet is a regular language. -/
theorem isRegular_lexNormalFormSet {Γ : Type} [Finite Γ] [LinearOrder Γ]
    (C : ConcurrentAlphabet Γ) : (lexNormalFormSet C).IsRegular := by
  classical
  have := Fintype.ofFinite Γ
  rw [Cslib.Language.IsRegular.iff_dfa]
  exact ⟨Option (Γ → Bool), inferInstance, lexNormalFormDFA C, language_lexNormalFormDFA C⟩

/-! ### Bertoni–Mauri–Sabadini predictive membership dynamic programming -/

section PredictiveMembership

variable {Q : Type v} {Γ : Type u} [DecidableEq Γ]

/-- The count vector of a word `w`. -/
def countVec (w : List Γ) (a : Γ) : ℕ := w.count a

theorem countVec_eq (w : List Γ) (a : Γ) : countVec w a = w.count a := by
  rfl

/-- A count vector `c : Σ → ℕ` is a valid DAG-prefix count vector of `w` if there exists a
DAG-prefix `u'` of `w` with letter counts `c`. -/
def IsDAGPrefixCount (C : ConcurrentAlphabet Γ) (w : List Γ) (c : Γ → ℕ) : Prop :=
  ∃ u' : List Γ, DAGPrefix C u' w ∧ ∀ a, u'.count a = c a

theorem isDAGPrefixCount_iff (C : ConcurrentAlphabet Γ) (w : List Γ) (c : Γ → ℕ) :
    IsDAGPrefixCount C w c ↔ ∃ u' : List Γ, DAGPrefix C u' w ∧ ∀ a, u'.count a = c a := by
  exact Iff.rfl

/-- Dynamic-programming reachability on `(state, DAG-prefix count vector)` pairs for an NFA `A`
and target word `w`.
-/
inductive ReachableDAGPrefix (C : ConcurrentAlphabet Γ) (A : Cslib.Automata.NA.FinAcc Q Γ)
    (w : List Γ) : Q → (Γ → ℕ) → Prop
  | start {q : Q} (hq : q ∈ A.start) :
      ReachableDAGPrefix C A w q (fun _ => 0)
  | step {q q' : Q} {c : Γ → ℕ} {a : Γ}
      (hreach : ReachableDAGPrefix C A w q c)
      (htr : A.Tr q a q')
      (hvalid : IsDAGPrefixCount C w (Function.update c a (c a + 1))) :
      ReachableDAGPrefix C A w q' (Function.update c a (c a + 1))

theorem reachableDAGPrefix_iff_exists_dagPrefix (C : ConcurrentAlphabet Γ)
    (A : Cslib.Automata.NA.FinAcc Q Γ) (w : List Γ) (q : Q) (c : Γ → ℕ) :
    ReachableDAGPrefix C A w q c ↔
      ∃ q₀ ∈ A.start, ∃ u' : List Γ,
        A.MTr q₀ u' q ∧ DAGPrefix C u' w ∧ ∀ a, u'.count a = c a := by
  constructor
  · intro h
    induction h with
    | start hq => exact ⟨_, hq, [], Cslib.LTS.MTr.refl, dagPrefix_nil w, fun _ => rfl⟩
    | @step q₁ q₂ c₁ a _ htr hvalid ih =>
      obtain ⟨q₀, hq₀, u', hmtr, hdag, hcnt⟩ := ih
      obtain ⟨u'', hdag'', hcnt''⟩ := hvalid
      refine ⟨q₀, hq₀, u' ++ [a], hmtr.stepR _ htr, ?_, fun x => ?_⟩
      · rw [dagPrefix_iff_count_and_depProj]
        have hd₁ := dagPrefix_iff_count_and_depProj.mp hdag
        have hd₂ := dagPrefix_iff_count_and_depProj.mp hdag''
        have hcnt_eq : ∀ x, (u' ++ [a]).count x = u''.count x := fun x => by
          rw [hcnt'', List.count_append, hcnt x, List.count_singleton]
          by_cases hx : x = a <;> simp [hx, Ne.symm, Function.update]
        refine ⟨fun x => by rw [hcnt_eq x]; exact hd₂.1 x, fun x y hxy => ?_⟩
        by_cases ha_xy : a = x ∨ a = y
        · have hlen_lt : (depProj x y u').length + 1 = (depProj x y u'').length := by
            rw [depProj_length, depProj_length]
            have hx_eq := hcnt_eq x
            have hy_eq := hcnt_eq y
            rw [List.count_append, List.count_singleton] at hx_eq hy_eq
            rcases ha_xy with rfl | rfl <;> split_ifs <;> simp_all <;> omega
          have hpref : depProj x y u' <+: depProj x y u'' := by
            obtain ⟨s₁, hs₁⟩ := hd₁.2 x y hxy
            obtain ⟨s₂, hs₂⟩ := hd₂.2 x y hxy
            have h1 : depProj x y u' = (depProj x y w).take (depProj x y u').length := by
              rw [← hs₁, List.take_left]
            have h2 : depProj x y u'' = (depProj x y w).take (depProj x y u'').length := by
              rw [← hs₂, List.take_left]
            refine ⟨(depProj x y u'').drop (depProj x y u').length, ?_⟩
            have htake : (depProj x y u'').take (depProj x y u').length = depProj x y u' := by
              rw [h2, List.take_take, Nat.min_eq_left (by omega), ← h1]
            conv_lhs => arg 1; rw [← htake]
            exact List.take_append_drop _ _
          obtain ⟨s, hs⟩ := hpref
          have hslen : s.length = 1 := by
            have := congrArg List.length hs
            rw [List.length_append] at this
            omega
          obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hslen
          have hda : d = a := by
            have hca : (depProj x y u' ++ [d]).count a = (depProj x y u'').count a :=
              congrArg (List.count a) hs
            rw [List.count_append, depProj_count_of_mem ha_xy, depProj_count_of_mem ha_xy] at hca
            have hca' := hcnt_eq a
            rw [List.count_append, List.count_singleton] at hca'
            simp only [beq_self_eq_true, ↓reduceIte] at hca'
            have hd_cnt : [d].count a = 1 := by omega
            simp only [List.count_singleton, beq_iff_eq] at hd_cnt
            by_contra hne
            simp [hne] at hd_cnt
          rw [hda] at hs
          have hpeq : depProj x y (u' ++ [a]) = depProj x y u'' := by
            simp [depProj_append, depProj_cons, depProj_nil, ha_xy, hs]
          rw [hpeq]
          exact hd₂.2 x y hxy
        · simp only [depProj_append, depProj_cons, depProj_nil, ha_xy, ↓reduceIte,
            List.append_nil]
          exact hd₁.2 x y hxy
      · rw [List.count_append, hcnt x, List.count_singleton]
        by_cases hx : x = a <;> simp [hx, Ne.symm, Function.update]
  · rintro ⟨q₀, hq₀, u', hmtr, hdag, hcnt⟩
    induction u' using List.reverseRecOn generalizing q c with
    | nil =>
      have hc0 : c = fun _ => 0 := funext fun a => (hcnt a).symm
      subst hc0
      have hqeq : q = q₀ := hmtr.nil_eq.symm
      subst hqeq
      exact ReachableDAGPrefix.start hq₀
    | append_singleton u' a ih =>
      obtain ⟨q₁, hmtr₁, htr_sing⟩ := hmtr.split
      have htr₁ : A.Tr q₁ a q := htr_sing.single_invert
      have hdag₁ : DAGPrefix C u' w := dagPrefix_prefix hdag
      have hreach₁ := ih q₁ (countVec u') hmtr₁ hdag₁ (fun _ => rfl)
      have hupd : c = Function.update (countVec u') a (countVec u' a + 1) := by
        funext x
        rw [← hcnt x, List.count_append, List.count_singleton]
        by_cases hx : x = a <;> simp [hx, Ne.symm, countVec, Function.update]
      rw [hupd]
      exact ReachableDAGPrefix.step hreach₁ htr₁ ⟨u' ++ [a], hdag, fun x => by
        rw [List.count_append, List.count_singleton]
        by_cases hx : x = a <;> simp [hx, Ne.symm, countVec, Function.update]⟩

/-- **Bertoni–Mauri–Sabadini predictive membership characterization**:
a word `w` belongs to the trace closure `[L(A)]_I` of an NFA `A` if and only if some accepting state
is reachable at count vector `countVec w` in the DAG-prefix dynamic program. -/
theorem mem_traceClosure_iff_reachableDAGPrefix (C : ConcurrentAlphabet Γ)
    (A : Cslib.Automata.NA.FinAcc Q Γ) (w : List Γ) :
    w ∈ traceClosure C (Cslib.Automata.Acceptor.language A) ↔
      ∃ q ∈ A.accept, ReachableDAGPrefix C A w q (countVec w) := by
  rw [mem_traceClosure_iff]
  constructor
  · rintro ⟨u, hu, hteq⟩
    obtain ⟨q₀, hq₀, q, hq, hmtr⟩ := hu
    refine ⟨q, hq, (reachableDAGPrefix_iff_exists_dagPrefix C A w q (countVec w)).mpr
      ⟨q₀, hq₀, u, hmtr, dagPrefix_of_traceEquiv_left hteq.symm (dagPrefix_self w),
        fun a => hteq.count_eq a⟩⟩
  · rintro ⟨q, hq, hreach⟩
    obtain ⟨q₀, hq₀, u, hmtr, hdag, hcnt⟩ :=
      (reachableDAGPrefix_iff_exists_dagPrefix C A w q (countVec w)).mp hreach
    refine ⟨u, ⟨q₀, hq₀, q, hq, hmtr⟩, ?_⟩
    exact traceEquiv_of_dagPrefix_of_count_eq hdag (dagPrefix_self w) hcnt

end PredictiveMembership

end Cslib.Language
