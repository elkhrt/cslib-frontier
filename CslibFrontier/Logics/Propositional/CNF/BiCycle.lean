/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.TwoCNF
public import CslibFrontier.Logics.Propositional.ClauseSet.Basic
public import Mathlib.Data.Finset.Card

import Mathlib.Data.Finset.Max

/-!
# 2-SAT Implication Graphs and the Chvátal–Reed Bi-Cycle Criterion

This module develops the implication-graph theory of simple 2-CNF clause sets
(`Cslib.Logic.PL.ClauseSet V`) over an arbitrary variable type `V` under standard Lean axioms,
connecting `Cslib.Logic.PL.CNF.not_satisfiable_iff_of_width_le_two` (Aspvall–Plass–Tarjan) to
set-based 2-CNF formulas and proving the Chvátal–Reed bi-cycle criterion for 2-SAT satisfiability.

## Main definitions

* `CslibFrontier.Logics.Propositional.HasDistinctVars`,
  `CslibFrontier.Logics.Propositional.IsSimpleTwoCNF`: simple clauses without repeated variables and
  2-CNF clause sets whose clauses each have two literals on distinct variables.
* `CslibFrontier.Logics.Propositional.ClauseSetImplies`: directed implication relation `a → b`
  (`{¬a, b} ∈ ψ`) on `Cslib.Logic.PL.Literal V`.
* `CslibFrontier.Logics.Propositional.BiCycle`,
  `CslibFrontier.Logics.Propositional.BiCycle.clauses`,
  `CslibFrontier.Logics.Propositional.BiCycle.IsProper`,
  `CslibFrontier.Logics.Propositional.ContainsBiCycle`: Chvátal–Reed bi-cycles of length `l` and
  bi-cycle containment in a clause set.

## Main results

* `CslibFrontier.Logics.Propositional.exists_sat_iff_not_exists_contradictory_cycle`:
  Aspvall–Plass–Tarjan characterization for `Cslib.Logic.PL.ClauseSet V`.
* `CslibFrontier.Logics.Propositional.BiCycle.injective_clauses_iff`,
  `CslibFrontier.Logics.Propositional.BiCycle.isProper_iff_not_endpoints_match`: characterization of
  clause distinctness in a bi-cycle via endpoint non-coincidence.
* `CslibFrontier.Logics.Propositional.exists_sat_of_not_containsBiCycle`: Chvátal–Reed theorem that
  every bi-cycle-free simple 2-CNF clause set is satisfiable.
-/

public section

open Cslib.Logic.PL

namespace CslibFrontier.Logics.Propositional

section ImplicationGraph

variable {V : Type*}

/-- A finite clause `c : Finset (Literal V)` has *distinct variables* if no two distinct literals in
`c` share the same underlying variable. -/
@[expose]
def HasDistinctVars (c : Finset (Literal V)) : Prop :=
  ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.1 = l₂.1 → l₁ = l₂

/-- A finite clause set `ψ : ClauseSet V` is a *simple 2-CNF formula* if every clause `c ∈ ψ` has
cardinality `2` and distinct variables. -/
@[expose]
def IsSimpleTwoCNF (ψ : ClauseSet V) : Prop :=
  ∀ c ∈ ψ, c.card = 2 ∧ HasDistinctVars c

/-- A clause set `ψ` is a simple 2-CNF formula if and only if every clause `c ∈ ψ` has the form
`{a, b}` for two literals `a, b` on distinct variables. -/
theorem isSimpleTwoCNF_iff_exists_pair [DecidableEq V] {ψ : ClauseSet V} :
    IsSimpleTwoCNF ψ ↔ ∀ c ∈ ψ, ∃ a b : Literal V, a.1 ≠ b.1 ∧ c = {a, b} := by
  constructor
  · intro hψ c hc
    obtain ⟨hcard, hD⟩ := hψ c hc
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    refine ⟨a, b, fun hvar ↦ hab (hD a ?_ b ?_ hvar), rfl⟩ <;> simp
  · intro h c hc
    obtain ⟨a, b, hvar, rfl⟩ := h c hc
    refine ⟨Finset.card_pair fun hab ↦ hvar (congr_arg Prod.fst hab), ?_⟩
    intro l₁ hl₁ l₂ hl₂ hle
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl₁ hl₂
    rcases hl₁ with rfl | rfl <;> rcases hl₂ with rfl | rfl
    · rfl
    · exact absurd hle hvar
    · exact absurd hle.symm hvar
    · rfl

/-- Directed implication edge `a → b` in the implication graph of `ψ : ClauseSet V`, holding when
`{a.negate, b} ∈ ψ`. -/
@[expose]
def ClauseSetImplies [DecidableEq V] (ψ : ClauseSet V) (a b : Literal V) : Prop :=
  {a.negate, b} ∈ ψ

/-- Contraposition symmetry of `ClauseSetImplies`: `a → b` if and only if `¬b → ¬a`. -/
theorem clauseSetImplies_negate_iff [DecidableEq V] {ψ : ClauseSet V} {a b : Literal V} :
    ClauseSetImplies ψ a b ↔ ClauseSetImplies ψ b.negate a.negate := by
  simp only [ClauseSetImplies, negate_negate, Finset.pair_comm]

/-- Contraposition symmetry of reachability under `ClauseSetImplies`. -/
theorem reflTransGen_clauseSetImplies_negate_iff [DecidableEq V] {ψ : ClauseSet V}
    {a b : Literal V} :
    Relation.ReflTransGen (ClauseSetImplies ψ) a b ↔
      Relation.ReflTransGen (ClauseSetImplies ψ) b.negate a.negate := by
  have hfwd : ∀ {x y : Literal V},
      Relation.ReflTransGen (ClauseSetImplies ψ) x y →
        Relation.ReflTransGen (ClauseSetImplies ψ) y.negate x.negate := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.head (clauseSetImplies_negate_iff.mp hbc)
  refine ⟨hfwd, fun h ↦ ?_⟩
  simpa only [negate_negate] using hfwd h

/-- In a simple 2-CNF clause set, every implication edge `a → b` connects literals on distinct
variables. -/
theorem var_ne_of_clauseSetImplies [DecidableEq V] {ψ : ClauseSet V} (hψ : IsSimpleTwoCNF ψ)
    {a b : Literal V} (hab : ClauseSetImplies ψ a b) : a.1 ≠ b.1 := by
  obtain ⟨hcard, hD⟩ := hψ {a.negate, b} hab
  intro hvar
  have hne : a.negate ≠ b := by
    intro heq
    rw [heq, Finset.pair_eq_singleton, Finset.card_singleton] at hcard
    omega
  have hneg_var : a.negate.1 = a.1 := by
    obtain ⟨v, pol⟩ := a
    rfl
  exact hne (hD a.negate (by simp) b (by simp) (hneg_var.trans hvar))

private lemma literal_ne_negate (a : Literal V) : a ≠ a.negate := by
  obtain ⟨v, b⟩ := a
  intro h
  have hp : b = !b := congr_arg Prod.snd h
  cases b <;> simp at hp

private lemma literal_var_negate (a : Literal V) : a.negate.1 = a.1 := by
  obtain ⟨v, b⟩ := a
  rfl

private lemma eq_or_eq_negate_of_var_eq {a b : Literal V} (h : a.1 = b.1) :
    a = b ∨ a = b.negate := by
  obtain ⟨va, ba⟩ := a
  obtain ⟨vb, bb⟩ := b
  dsimp only at h
  subst h
  cases ba <;> cases bb <;> simp [Std.Sat.Literal.negate]

private lemma toCNF_implies_iff_clauseSetImplies [DecidableEq V] {ψ : ClauseSet V}
    (hψ : IsSimpleTwoCNF ψ) {a b : Literal V} :
    ψ.toCNF.Implies a b ↔ ClauseSetImplies ψ a b := by
  constructor
  · rintro ⟨c, hc, ha, hb, hsub⟩
    simp only [ClauseSet.toCNF, List.mem_map, Finset.mem_toList] at hc
    obtain ⟨C, hC, rfl⟩ := hc
    rw [Finset.mem_toList] at ha hb
    have hcard : C.card = 2 := (hψ C hC).1
    have hne : a.negate ≠ b := by
      intro heq
      have hC_eq : C = {b} := by
        ext m
        simp only [Finset.mem_singleton]
        refine ⟨fun hm ↦ ?_, fun hm ↦ hm ▸ hb⟩
        rcases hsub m (Finset.mem_toList.mpr hm) with rfl | rfl
        · exact heq
        · rfl
      rw [hC_eq, Finset.card_singleton] at hcard
      omega
    have hC_eq : C = {a.negate, b} := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun hm ↦ hsub m (Finset.mem_toList.mpr hm),
        fun hm ↦ hm.elim (fun h ↦ h ▸ ha) (fun h ↦ h ▸ hb)⟩
    unfold ClauseSetImplies
    rwa [← hC_eq]
  · intro hab
    refine ⟨({a.negate, b} : Finset (Literal V)).toList, ?_, ?_, ?_, ?_⟩
    · simp only [ClauseSet.toCNF, List.mem_map, Finset.mem_toList]
      exact ⟨{a.negate, b}, hab, rfl⟩
    · simp
    · simp
    · intro m hm
      simpa using hm

/-- **Aspvall–Plass–Tarjan characterization for simple 2-CNF clause sets**: a simple 2-CNF clause
set `ψ : ClauseSet V` is satisfiable if and only if no literal `a` reaches `a.negate` and is
simultaneously reached from `a.negate` under `ClauseSetImplies`. -/
theorem exists_sat_iff_not_exists_contradictory_cycle [DecidableEq V] {ψ : ClauseSet V}
    (hψ : IsSimpleTwoCNF ψ) :
    (∃ x : V → Bool, ψ.Sat x) ↔
      ¬ ∃ a : Literal V,
        Relation.ReflTransGen (ClauseSetImplies ψ) a a.negate ∧
        Relation.ReflTransGen (ClauseSetImplies ψ) a.negate a := by
  have hsat_iff : (∃ x : V → Bool, ψ.Sat x) ↔ ψ.toCNF.Satisfiable := by
    simp only [CNF.Satisfiable, ClauseSet.eval_toCNF_eq_true_iff]
  have hw : ∀ c ∈ ψ.toCNF, c.length ≤ 2 := fun _ hc ↦
    ClauseSet.length_le_of_mem_toCNF (fun C hC ↦ (hψ C hC).1.le) hc
  have hnil : [] ∉ ψ.toCNF := by
    simp only [ClauseSet.toCNF, List.mem_map, Finset.mem_toList, not_exists, not_and]
    intro C hC hnil
    have hlen := congr_arg List.length hnil
    rw [Finset.length_toList, List.length_nil, (hψ C hC).1] at hlen
    omega
  have hrel : ψ.toCNF.Implies = ClauseSetImplies ψ := by
    ext a b
    exact toCNF_implies_iff_clauseSetImplies hψ
  rw [hsat_iff]
  have hapt := CNF.not_satisfiable_iff_of_width_le_two hw
  rw [hrel] at hapt
  constructor
  · rintro hsat ⟨⟨v, b⟩, h1, h2⟩
    apply hapt.mpr (Or.inr ⟨v, ?_⟩) hsat
    cases b
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  · intro hno
    by_contra hunsat
    rcases hapt.mp hunsat with hnil_mem | ⟨v, h1, h2⟩
    · exact hnil hnil_mem
    · exact hno ⟨(v, true), h1, h2⟩

end ImplicationGraph

section BiCycles

/-- A *bi-cycle* of length `l` over variable type `V` consists of `l` path literals
`w_0, …, w_{l-1}` together with endpoint literals `u` and `v`, encoding the `l + 1` 2-clauses
`{u, w_0}, {¬w_0, w_1}, …, {¬w_{l-2}, w_{l-1}}, {¬w_{l-1}, v}`. -/
@[ext]
structure BiCycle (V : Type*) (l : ℕ) where
  /-- The sequence of `l` path literals `w_0, …, w_{l-1}`. -/
  lits : Fin l → Literal V
  /-- The initial endpoint literal `u` paired with `w_0`. -/
  u : Literal V
  /-- The terminal endpoint literal `v` paired with `¬w_{l-1}`. -/
  v : Literal V

namespace BiCycle

variable {V : Type*} {l : ℕ}

/-- The `(l + 1)`-tuple of 2-clauses determined by a bi-cycle `B` of length `l ≥ 1`:
clause `0` is `{u, w_0}`, clause `j` (`0 < j < l`) is `{¬w_{j-1}, w_j}`, and clause `l` is
`{¬w_{l-1}, v}`. -/
def clauses [DecidableEq V] (B : BiCycle V l) (hl : 1 ≤ l) (j : Fin (l + 1)) :
    Finset (Literal V) :=
  if _ : j.val = 0 then
    {B.u, B.lits ⟨0, hl⟩}
  else if hlt : j.val < l then
    {(B.lits ⟨j.val - 1, by omega⟩).negate, B.lits ⟨j.val, hlt⟩}
  else
    {(B.lits ⟨l - 1, by omega⟩).negate, B.v}

/-- Evaluation of `BiCycle.clauses` at index `0`. -/
@[simp]
theorem clauses_zero [DecidableEq V] (B : BiCycle V l) (hl : 1 ≤ l) :
    B.clauses hl 0 = {B.u, B.lits ⟨0, hl⟩} := by
  simp [clauses]

/-- Evaluation of `BiCycle.clauses` at an interior index `0 < j < l`. -/
theorem clauses_mid [DecidableEq V] (B : BiCycle V l) (hl : 1 ≤ l) {j : Fin (l + 1)}
    (h0 : 0 < j.val) (hlt : j.val < l) :
    B.clauses hl j = {(B.lits ⟨j.val - 1, by omega⟩).negate, B.lits ⟨j.val, hlt⟩} := by
  have hne : j.val ≠ 0 := by omega
  simp [clauses, hne, hlt]

/-- Evaluation of `BiCycle.clauses` at the terminal index `l`. -/
@[simp]
theorem clauses_last [DecidableEq V] (B : BiCycle V l) (hl : 1 ≤ l) :
    B.clauses hl (Fin.last l) = {(B.lits ⟨l - 1, by omega⟩).negate, B.v} := by
  have hne : l ≠ 0 := by omega
  simp [clauses, hne]

/-- Under `l ≥ 2` and pairwise distinct path variables, the `l + 1` clauses of a bi-cycle `B` are
pairwise distinct if and only if it is not the case that `u = ¬w_{l-1}` and `v = w_0`. -/
theorem injective_clauses_iff [DecidableEq V] {B : BiCycle V l} (hl : 2 ≤ l)
    (hinj : Function.Injective (fun i ↦ (B.lits i).1)) :
    Function.Injective (B.clauses (by omega)) ↔
      ¬ (B.u = (B.lits ⟨l - 1, by omega⟩).negate ∧ B.v = B.lits ⟨0, by omega⟩) := by
  have hl1 : 1 ≤ l := by omega
  have hne_end : B.lits ⟨0, hl1⟩ ≠ (B.lits ⟨l - 1, by omega⟩).negate := by
    intro heq
    have hvar : (B.lits ⟨0, hl1⟩).1 = (B.lits ⟨l - 1, by omega⟩).1 := by
      simpa only [literal_var_negate] using congr_arg Prod.fst heq
    have hidx : (⟨0, hl1⟩ : Fin l) = ⟨l - 1, by omega⟩ := hinj hvar
    have : 0 = l - 1 := congr_arg Fin.val hidx
    omega
  constructor
  · rintro hcl ⟨hu, hv⟩
    have heq : B.clauses hl1 0 = B.clauses hl1 (Fin.last l) := by
      rw [clauses_zero, clauses_last, hu, hv, Finset.pair_comm]
    have h0l : (0 : Fin (l + 1)) = Fin.last l := hcl heq
    have : (0 : ℕ) = l := congr_arg Fin.val h0l
    omega
  · intro hnot j₁ j₂ hcl
    have hlt_contra : ∀ {a b : Fin (l + 1)}, a.val < b.val →
        B.clauses hl1 a = B.clauses hl1 b → False := by
      intro a b hab heq
      by_cases ha0 : a.val = 0
      · have ha_eq : a = 0 := Fin.ext ha0
        rw [ha_eq, clauses_zero] at heq
        by_cases hbl : b.val < l
        · rw [clauses_mid B hl1 (by omega) hbl] at heq
          have hmem : B.lits ⟨0, hl1⟩ ∈
              ({(B.lits ⟨b.val - 1, by omega⟩).negate, B.lits ⟨b.val, hbl⟩} :
                Finset (Literal V)) :=
            heq ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h2
          · have hvar : (B.lits ⟨0, hl1⟩).1 = (B.lits ⟨b.val - 1, by omega⟩).1 := by
              simpa only [literal_var_negate] using congr_arg Prod.fst h1
            have hidx : 0 = b.val - 1 := congr_arg Fin.val (hinj hvar)
            have hidx' : (⟨b.val - 1, by omega⟩ : Fin l) = ⟨0, hl1⟩ := Fin.ext hidx.symm
            rw [hidx'] at h1
            exact literal_ne_negate _ h1
          · have hidx : 0 = b.val := congr_arg Fin.val (hinj (congr_arg Prod.fst h2))
            omega
        · have hb_val : b.val = l := by have hb_lt := b.isLt; omega
          have hb_eq : b = Fin.last l := Fin.ext hb_val
          rw [hb_eq, clauses_last] at heq
          have hw0 : B.lits ⟨0, hl1⟩ ∈
              ({(B.lits ⟨l - 1, by omega⟩).negate, B.v} : Finset (Literal V)) :=
            heq ▸ by simp
          have hwl : (B.lits ⟨l - 1, by omega⟩).negate ∈
              ({B.u, B.lits ⟨0, hl1⟩} : Finset (Literal V)) :=
            heq.symm ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw0 hwl
          have hv : B.v = B.lits ⟨0, hl1⟩ := by
            rcases hw0 with h | h
            · exact absurd h hne_end
            · exact h.symm
          have hu : B.u = (B.lits ⟨l - 1, by omega⟩).negate := by
            rcases hwl with h | h
            · exact h.symm
            · exact absurd h.symm hne_end
          exact hnot ⟨hu, hv⟩
      · have ha_pos : 0 < a.val := by omega
        have ha_lt : a.val < l := by have hb_lt := b.isLt; omega
        rw [clauses_mid B hl1 ha_pos ha_lt] at heq
        by_cases hbl : b.val < l
        · rw [clauses_mid B hl1 (by omega) hbl] at heq
          have hmem : (B.lits ⟨a.val - 1, by omega⟩).negate ∈
              ({(B.lits ⟨b.val - 1, by omega⟩).negate, B.lits ⟨b.val, hbl⟩} :
                Finset (Literal V)) :=
            heq ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h2
          · have hvar : (B.lits ⟨a.val - 1, by omega⟩).1 =
                (B.lits ⟨b.val - 1, by omega⟩).1 := by
              simpa only [literal_var_negate] using congr_arg Prod.fst h1
            have hidx : a.val - 1 = b.val - 1 := congr_arg Fin.val (hinj hvar)
            omega
          · have hvar : (B.lits ⟨a.val - 1, by omega⟩).1 = (B.lits ⟨b.val, hbl⟩).1 := by
              simpa only [literal_var_negate] using congr_arg Prod.fst h2
            have hidx : a.val - 1 = b.val := congr_arg Fin.val (hinj hvar)
            omega
        · have hb_val : b.val = l := by have hb_lt := b.isLt; omega
          have hb_eq : b = Fin.last l := Fin.ext hb_val
          rw [hb_eq, clauses_last] at heq
          have hmem : (B.lits ⟨l - 1, by omega⟩).negate ∈
              ({(B.lits ⟨a.val - 1, by omega⟩).negate, B.lits ⟨a.val, ha_lt⟩} :
                Finset (Literal V)) :=
            heq.symm ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h2
          · have hvar : (B.lits ⟨l - 1, by omega⟩).1 = (B.lits ⟨a.val - 1, by omega⟩).1 := by
              simpa only [literal_var_negate] using congr_arg Prod.fst h1
            have hidx : l - 1 = a.val - 1 := congr_arg Fin.val (hinj hvar)
            omega
          · have hvar : (B.lits ⟨l - 1, by omega⟩).1 = (B.lits ⟨a.val, ha_lt⟩).1 := by
              simpa only [literal_var_negate] using congr_arg Prod.fst h2
            have hidx : l - 1 = a.val := congr_arg Fin.val (hinj hvar)
            have hidx' : (⟨a.val, ha_lt⟩ : Fin l) = ⟨l - 1, by omega⟩ := Fin.ext hidx.symm
            rw [hidx'] at h2
            exact literal_ne_negate _ h2.symm
    rcases lt_trichotomy j₁.val j₂.val with hlt | heq | hgt
    · exact absurd hcl (hlt_contra hlt)
    · exact Fin.ext heq
    · exact absurd hcl.symm (hlt_contra hgt)

/-- A bi-cycle `B` of length `l` is *proper* if `l ≥ 2`, the path literals `w_0, …, w_{l-1}` have
pairwise distinct variables, both endpoints `u` and `v` lie on variables occurring among
`w_0, …, w_{l-1}`, and all `l + 1` clauses of `B` are pairwise distinct. -/
@[expose]
def IsProper [DecidableEq V] (B : BiCycle V l) : Prop :=
  ∃ _ : 2 ≤ l,
    Function.Injective (fun i ↦ (B.lits i).1) ∧
    (∃ i, (B.lits i).1 = B.u.1) ∧
    (∃ i, (B.lits i).1 = B.v.1) ∧
    Function.Injective (B.clauses (by omega))

/-- Every proper bi-cycle has length at least `2`. -/
theorem IsProper.two_le [DecidableEq V] {B : BiCycle V l} (hB : B.IsProper) : 2 ≤ l :=
  hB.1

/-- Every proper bi-cycle has length at least `1`. -/
theorem IsProper.one_le [DecidableEq V] {B : BiCycle V l} (hB : B.IsProper) : 1 ≤ l :=
  le_trans (by decide : 1 ≤ 2) hB.1

/-- The path literals of a proper bi-cycle have pairwise distinct variables. -/
theorem IsProper.injective_var [DecidableEq V] {B : BiCycle V l} (hB : B.IsProper) :
    Function.Injective (fun i ↦ (B.lits i).1) :=
  hB.2.1

/-- The initial endpoint literal `u` of a proper bi-cycle shares its variable with some path
literal. -/
theorem IsProper.exists_u_var [DecidableEq V] {B : BiCycle V l} (hB : B.IsProper) :
    ∃ i, (B.lits i).1 = B.u.1 :=
  hB.2.2.1

/-- The terminal endpoint literal `v` of a proper bi-cycle shares its variable with some path
literal. -/
theorem IsProper.exists_v_var [DecidableEq V] {B : BiCycle V l} (hB : B.IsProper) :
    ∃ i, (B.lits i).1 = B.v.1 :=
  hB.2.2.2.1

/-- The `l + 1` clauses of a proper bi-cycle are pairwise distinct. -/
theorem IsProper.injective_clauses [DecidableEq V] {B : BiCycle V l} (hB : B.IsProper) :
    Function.Injective (B.clauses hB.one_le) :=
  hB.2.2.2.2

/-- Equivalent characterization of `BiCycle.IsProper` replacing clause injectivity with the
endpoint non-matching condition `¬ (u = ¬w_{l-1} ∧ v = w_0)`. -/
theorem isProper_iff_not_endpoints_match [DecidableEq V] {B : BiCycle V l} :
    B.IsProper ↔
      ∃ _ : 2 ≤ l,
        Function.Injective (fun i ↦ (B.lits i).1) ∧
        (∃ i, (B.lits i).1 = B.u.1) ∧
        (∃ i, (B.lits i).1 = B.v.1) ∧
        ¬ (B.u = (B.lits ⟨l - 1, by omega⟩).negate ∧ B.v = B.lits ⟨0, by omega⟩) := by
  constructor
  · rintro ⟨hl, hinj, hu, hv, hcl⟩
    exact ⟨hl, hinj, hu, hv, (injective_clauses_iff hl hinj).mp hcl⟩
  · rintro ⟨hl, hinj, hu, hv, hnot⟩
    exact ⟨hl, hinj, hu, hv, (injective_clauses_iff hl hinj).mpr hnot⟩

end BiCycle

variable {V : Type*} [DecidableEq V]

/-- A clause set `ψ : ClauseSet V` *contains a bi-cycle* if there exist a length `l` and a proper
bi-cycle `B` of length `l` whose `l + 1` clauses all belong to `ψ`. -/
@[expose]
def ContainsBiCycle (ψ : ClauseSet V) : Prop :=
  ∃ (l : ℕ) (B : BiCycle V l) (hB : B.IsProper),
    ∀ j : Fin (l + 1), B.clauses hB.one_le j ∈ ψ

private lemma reflTransGen_iff_exists_walk {α : Type*} {r : α → α → Prop} {a b : α} :
    Relation.ReflTransGen r a b ↔
      ∃ (n : ℕ) (f : Fin (n + 1) → α),
        f 0 = a ∧ f (Fin.last n) = b ∧ ∀ i : Fin n, r (f i.castSucc) (f i.succ) := by
  constructor
  · intro h
    induction h with
    | refl =>
      exact ⟨0, fun _ ↦ a, rfl, rfl, fun i ↦ Fin.elim0 i⟩
    | @tail b c _ hbc ih =>
      obtain ⟨n, f, hf0, hflast, hfstep⟩ := ih
      refine ⟨n + 1, Fin.snoc f c, ?_, ?_, fun i ↦ ?_⟩
      · simpa [Fin.snoc] using hf0
      · exact Fin.snoc_last (α := fun _ ↦ α) c f
      · by_cases hi : i.val < n
        · have h1 : i.castSucc = (⟨i.val, hi⟩ : Fin n).castSucc.castSucc := Fin.ext rfl
          have h2 : i.succ = (⟨i.val, hi⟩ : Fin n).succ.castSucc := Fin.ext rfl
          rw [h1, h2, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hfstep ⟨i.val, hi⟩
        · have hi_lt : i.val < n + 1 := i.isLt
          have hi_eq : i = Fin.last n := Fin.ext (by simp [Fin.val_last]; omega)
          rw [hi_eq, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hflast]
          exact hbc
  · rintro ⟨n, f, hf0, hflast, hfstep⟩
    induction n generalizing b with
    | zero =>
      have : a = b := hf0.symm.trans hflast
      exact this ▸ .refl
    | succ n ih =>
      have hpre : Relation.ReflTransGen r a (f (Fin.last n).castSucc) :=
        ih (fun k ↦ f k.castSucc) hf0 rfl fun i ↦ hfstep i.castSucc
      have hlast : r (f (Fin.last n).castSucc) b := by
        rw [← hflast]
        simpa [Fin.succ_last] using hfstep (Fin.last n)
      exact hpre.tail hlast

private lemma reflTransGen_of_walk_sub {α : Type*} {r : α → α → Prop} {n : ℕ}
    {f : Fin (n + 1) → α} (hf : ∀ i : Fin n, r (f i.castSucc) (f i.succ))
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    Relation.ReflTransGen r (f i) (f j) := by
  have haux : ∀ k : ℕ, ∀ (hi : i.val + k ≤ n),
      Relation.ReflTransGen r (f i) (f ⟨i.val + k, by omega⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hi
      have hprev := ih (by omega)
      have h1 : (⟨i.val + k, by omega⟩ : Fin n).castSucc = ⟨i.val + k, by omega⟩ := rfl
      have h2 : (⟨i.val + k, by omega⟩ : Fin n).succ = ⟨i.val + (k + 1), by omega⟩ :=
        Fin.ext (by simp [Nat.add_assoc])
      have hstep : r (f ⟨i.val + k, by omega⟩) (f ⟨i.val + (k + 1), by omega⟩) := by
        rw [← h1, ← h2]
        exact hf ⟨i.val + k, by omega⟩
      exact hprev.tail hstep
  have hle : i.val ≤ j.val := hij
  have heq : (⟨i.val + (j.val - i.val), by have hj := j.isLt; omega⟩ : Fin (n + 1)) = j :=
    Fin.ext (by simp; omega)
  rw [← heq]
  exact haux (j.val - i.val) (by have hj_lt := j.isLt; omega)

private lemma exists_min_contradictory_walk {ψ : ClauseSet V}
    (hψ : IsSimpleTwoCNF ψ) (hunsat : ¬ ∃ x : V → Bool, ψ.Sat x) :
    ∃ (s : ℕ) (a : Literal V) (p : Fin (s + 1) → Literal V),
      2 ≤ s ∧
      Relation.ReflTransGen (ClauseSetImplies ψ) a.negate a ∧
      p 0 = a ∧ p (Fin.last s) = a.negate ∧
      (∀ i : Fin s, ClauseSetImplies ψ (p i.castSucc) (p i.succ)) ∧
      Function.Injective (fun i : Fin s ↦ (p i.castSucc).1) := by
  classical
  have hex : ∃ a : Literal V,
      Relation.ReflTransGen (ClauseSetImplies ψ) a a.negate ∧
      Relation.ReflTransGen (ClauseSetImplies ψ) a.negate a := by
    by_contra hno
    exact hunsat ((exists_sat_iff_not_exists_contradictory_cycle hψ).mpr hno)
  let P : ℕ → Prop := fun s ↦
    ∃ (a : Literal V) (p : Fin (s + 1) → Literal V),
      Relation.ReflTransGen (ClauseSetImplies ψ) a.negate a ∧
      p 0 = a ∧ p (Fin.last s) = a.negate ∧
      ∀ i : Fin s, ClauseSetImplies ψ (p i.castSucc) (p i.succ)
  have hP : ∃ s, P s := by
    obtain ⟨a, h1, h2⟩ := hex
    obtain ⟨s, p, hp0, hplast, hpstep⟩ := reflTransGen_iff_exists_walk.mp h1
    exact ⟨s, a, p, h2, hp0, hplast, hpstep⟩
  let s := Nat.find hP
  have hs : P s := Nat.find_spec hP
  have hmin : ∀ s' < s, ¬ P s' := fun s' hlt ↦ Nat.find_min hP hlt
  obtain ⟨a, p, hback, hp0, hplast, hpstep⟩ := hs
  have hs2 : 2 ≤ s := by
    by_contra hlt
    have hs_cases : s = 0 ∨ s = 1 := by omega
    rcases hs_cases with hs0 | hs1
    · have h0 : (0 : Fin (s + 1)) = Fin.last s := Fin.ext (by simp [hs0])
      exact literal_ne_negate a (hp0.symm.trans (h0 ▸ hplast))
    · have h01 : ClauseSetImplies ψ a a.negate := by
        have hstep := hpstep ⟨0, by omega⟩
        have h1 : (⟨0, by omega⟩ : Fin s).castSucc = 0 := Fin.ext rfl
        have h2 : (⟨0, by omega⟩ : Fin s).succ = Fin.last s := Fin.ext (by simp [hs1])
        rwa [h1, h2, hp0, hplast] at hstep
      exact var_ne_of_clauseSetImplies hψ h01 (literal_var_negate a).symm
  have hinj : Function.Injective (fun i : Fin s ↦ (p i.castSucc).1) := by
    have hlt_ne : ∀ {i j : Fin s}, i.val < j.val →
        (p i.castSucc).1 ≠ (p j.castSucc).1 := by
      intro i j hij hvar
      have hj_lt : j.val < s := j.isLt
      rcases eq_or_eq_negate_of_var_eq hvar with heq | hneg
      · let s' := s - (j.val - i.val)
        have hs'_lt : s' < s := by omega
        apply hmin s' hs'_lt
        let p' : Fin (s' + 1) → Literal V := fun k ↦
          if hk : k.val ≤ i.val then p ⟨k.val, by omega⟩
          else p ⟨k.val + (j.val - i.val), by omega⟩
        refine ⟨a, p', hback, ?_, ?_, fun k ↦ ?_⟩
        · simp only [p', Fin.val_zero, Nat.zero_le, ↓reduceDIte]
          exact hp0
        · have hgt : ¬ s' ≤ i.val := by omega
          simp only [p', Fin.val_last, hgt, ↓reduceDIte]
          have hidx : (⟨s' + (j.val - i.val), by omega⟩ : Fin (s + 1)) = Fin.last s :=
            Fin.ext (by simp [s']; omega)
          rw [hidx, hplast]
        · have hk_lt : k.val < s' := k.isLt
          by_cases hk1 : k.val + 1 ≤ i.val
          · have hk0 : k.val ≤ i.val := by omega
            simp only [p', Fin.val_castSucc, Fin.val_succ, hk0, hk1, ↓reduceDIte]
            exact hpstep ⟨k.val, by omega⟩
          · by_cases hk0 : k.val ≤ i.val
            · have hki : k.val = i.val := by omega
              simp only [p', Fin.val_castSucc, Fin.val_succ, hk0, hk1, ↓reduceDIte]
              have h1 : (⟨k.val, by omega⟩ : Fin (s + 1)) = i.castSucc := Fin.ext hki
              have h2 : (⟨k.val + 1 + (j.val - i.val), by omega⟩ : Fin (s + 1)) = j.succ :=
                Fin.ext (by simp only [Fin.val_succ]; omega)
              rw [h1, heq, h2]
              exact hpstep j
            · simp only [p', Fin.val_castSucc, Fin.val_succ, hk0, hk1, ↓reduceDIte]
              have hstep := hpstep ⟨k.val + (j.val - i.val), by omega⟩
              have h1 : (⟨k.val + (j.val - i.val), by omega⟩ : Fin s).castSucc =
                  ⟨k.val + (j.val - i.val), by omega⟩ := rfl
              have h2 : (⟨k.val + (j.val - i.val), by omega⟩ : Fin s).succ =
                  ⟨k.val + 1 + (j.val - i.val), by omega⟩ := Fin.ext (by simp; omega)
              rwa [h1, h2] at hstep
      · let s' := j.val - i.val
        have hs'_lt : s' < s := by omega
        apply hmin s' hs'_lt
        let b := p i.castSucc
        have hbn : p j.castSucc = b.negate := by
          rw [← negate_negate (p j.castSucc), ← hneg]
        have hback_b : Relation.ReflTransGen (ClauseSetImplies ψ) b.negate b := by
          have h1 : Relation.ReflTransGen (ClauseSetImplies ψ) b.negate a.negate := by
            rw [← hbn, ← hplast]
            exact reflTransGen_of_walk_sub hpstep (Fin.le_last j.castSucc)
          have h2 : Relation.ReflTransGen (ClauseSetImplies ψ) a b := by
            rw [← hp0]
            exact reflTransGen_of_walk_sub hpstep (Fin.zero_le i.castSucc)
          exact (h1.trans hback).trans h2
        let p' : Fin (s' + 1) → Literal V := fun k ↦ p ⟨i.val + k.val, by omega⟩
        refine ⟨b, p', hback_b, ?_, ?_, fun k ↦ ?_⟩
        · simp only [p', Fin.val_zero, add_zero]
          rfl
        · simp only [p', Fin.val_last]
          have hidx : (⟨i.val + s', by omega⟩ : Fin (s + 1)) = j.castSucc :=
            Fin.ext (by simp [s']; omega)
          rw [hidx, hbn]
        · have hk_lt : k.val < s' := k.isLt
          have hstep := hpstep ⟨i.val + k.val, by omega⟩
          have h1 : (⟨i.val + k.val, by omega⟩ : Fin s).castSucc =
              ⟨i.val + k.val, by omega⟩ := rfl
          have h2 : (⟨i.val + k.val, by omega⟩ : Fin s).succ =
              ⟨i.val + (k.val + 1), by omega⟩ := Fin.ext (by simp; omega)
          rwa [h1, h2] at hstep
    intro i j hvar
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact absurd hvar (hlt_ne hlt)
    · exact Fin.ext heq
    · exact absurd hvar.symm (hlt_ne hgt)
  exact ⟨s, a, p, hs2, hback, hp0, hplast, hpstep, hinj⟩

/-- **Chvátal–Reed bi-cycle criterion for 2-SAT**: every simple 2-CNF clause set `ψ : ClauseSet V`
that contains no proper bi-cycle is satisfiable. -/
theorem exists_sat_of_not_containsBiCycle {ψ : ClauseSet V}
    (hψ : IsSimpleTwoCNF ψ) (hno : ¬ ContainsBiCycle ψ) :
    ∃ x : V → Bool, ψ.Sat x := by
  classical
  by_contra hunsat
  apply hno
  obtain ⟨s, a, p, hs2, hback, hp0, hplast, hpstep, hpinj⟩ :=
    exists_min_contradictory_walk hψ hunsat
  obtain ⟨t, q, hq0, hqlast, hqstep⟩ := reflTransGen_iff_exists_walk.mp hback
  have ht1 : 1 ≤ t := by
    by_contra ht0
    have ht_eq : t = 0 := by omega
    have h0 : (0 : Fin (t + 1)) = Fin.last t := Fin.ext (by simp [ht_eq])
    exact literal_ne_negate a (hq0.symm.trans (h0 ▸ hqlast)).symm
  let I : Finset (Fin t) := Finset.univ.filter fun i : Fin t ↦
    (∃ j : Fin t, i < j ∧ (q i.castSucc).1 = (q j.castSucc).1) ∨
    (∃ k : Fin s, (q i.castSucc).1 = (p k.castSucc).1)
  have h0I : (⟨0, ht1⟩ : Fin t) ∈ I := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Or.inr ⟨⟨0, by omega⟩, ?_⟩⟩
    have hq0' : q (⟨0, ht1⟩ : Fin t).castSucc = a.negate := hq0
    have hp0' : p (⟨0, by omega⟩ : Fin s).castSucc = a := hp0
    rw [hq0', hp0', literal_var_negate]
  let i₀ : Fin t := I.max' ⟨⟨0, ht1⟩, h0I⟩
  have hi₀I : i₀ ∈ I := Finset.max'_mem I ⟨⟨0, ht1⟩, h0I⟩
  have hi₀max : ∀ j ∈ I, j ≤ i₀ := fun j hj ↦ Finset.le_max' I j hj
  have hi₀_lt : i₀.val < t := i₀.isLt
  let m : ℕ := t - (i₀.val + 1)
  let l : ℕ := m + s
  have hl2 : 2 ≤ l := by omega
  let B : BiCycle V l :=
    { lits := fun r ↦
        if hr : r.val < m then q ⟨i₀.val + 1 + r.val, by omega⟩
        else p ⟨r.val - m, by omega⟩
      u := (q i₀.castSucc).negate
      v := a.negate }
  have hnot_in_I : ∀ j : Fin t, i₀ < j → j ∉ I :=
    fun j hj hjI ↦ not_le.mpr hj (hi₀max j hjI)
  have hinj_var : Function.Injective (fun r : Fin l ↦ (B.lits r).1) := by
    have hlt_ne : ∀ {r₁ r₂ : Fin l}, r₁.val < r₂.val →
        (B.lits r₁).1 ≠ (B.lits r₂).1 := by
      intro r₁ r₂ hr hvar
      have hr₂_lt : r₂.val < l := r₂.isLt
      by_cases h1 : r₁.val < m
      · let j₁ : Fin t := ⟨i₀.val + 1 + r₁.val, by omega⟩
        have hj₁_gt : i₀ < j₁ := by change i₀.val < i₀.val + 1 + r₁.val; omega
        apply hnot_in_I j₁ hj₁_gt
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hq1 : B.lits r₁ = q j₁.castSucc := by simp only [B, h1, ↓reduceDIte, j₁]; rfl
        by_cases h2 : r₂.val < m
        · left
          let j₂ : Fin t := ⟨i₀.val + 1 + r₂.val, by omega⟩
          have hq2 : B.lits r₂ = q j₂.castSucc := by simp only [B, h2, ↓reduceDIte, j₂]; rfl
          refine ⟨j₂, by change i₀.val + 1 + r₁.val < i₀.val + 1 + r₂.val; omega, ?_⟩
          rwa [← hq1, ← hq2]
        · right
          let k₂ : Fin s := ⟨r₂.val - m, by omega⟩
          have hp2 : B.lits r₂ = p k₂.castSucc := by simp only [B, h2, ↓reduceDIte, k₂]; rfl
          refine ⟨k₂, ?_⟩
          rwa [← hq1, ← hp2]
      · have h2 : ¬ r₂.val < m := by omega
        have hpvar : (p (⟨r₁.val - m, by omega⟩ : Fin s).castSucc).1 =
            (p (⟨r₂.val - m, by omega⟩ : Fin s).castSucc).1 := by
          have hp1 : B.lits r₁ = p (⟨r₁.val - m, by omega⟩ : Fin s).castSucc := by
            simp only [B, h1, ↓reduceDIte]; rfl
          have hp2 : B.lits r₂ = p (⟨r₂.val - m, by omega⟩ : Fin s).castSucc := by
            simp only [B, h2, ↓reduceDIte]; rfl
          rwa [← hp1, ← hp2]
        have hidx : r₁.val - m = r₂.val - m := congr_arg Fin.val (hpinj hpvar)
        omega
    intro r₁ r₂ hvar
    rcases lt_trichotomy r₁.val r₂.val with hlt | heq | hgt
    · exact absurd hvar (hlt_ne hlt)
    · exact Fin.ext heq
    · exact absurd hvar.symm (hlt_ne hgt)
  have hu_var : ∃ r : Fin l, (B.lits r).1 = B.u.1 := by
    rcases (Finset.mem_filter.mp hi₀I).2 with ⟨j, hj, hvar⟩ | ⟨k, hvar⟩
    · have hj_lt : j.val < t := j.isLt
      have hj_val : i₀.val < j.val := hj
      have hj_m : j.val - (i₀.val + 1) < m := by omega
      refine ⟨⟨j.val - (i₀.val + 1), by omega⟩, ?_⟩
      simp only [B, hj_m, ↓reduceDIte, literal_var_negate]
      have hidx : (⟨i₀.val + 1 + (j.val - (i₀.val + 1)), by omega⟩ : Fin (t + 1)) = j.castSucc :=
        Fin.ext (by simp; omega)
      rw [hidx, hvar]
    · have hk_lt : k.val < s := k.isLt
      have hk_ge : ¬ m + k.val < m := by omega
      refine ⟨⟨m + k.val, by omega⟩, ?_⟩
      simp only [B, hk_ge, ↓reduceDIte, literal_var_negate]
      have hidx : (⟨m + k.val - m, by omega⟩ : Fin (s + 1)) = k.castSucc :=
        Fin.ext (by simp)
      rw [hidx, hvar]
  have hv_var : ∃ r : Fin l, (B.lits r).1 = B.v.1 := by
    have hm_ge : ¬ m < m := Nat.lt_irrefl m
    refine ⟨⟨m, by omega⟩, ?_⟩
    simp only [B, hm_ge, ↓reduceDIte, Nat.sub_self, literal_var_negate]
    have hp0' : p ⟨0, by omega⟩ = a := hp0
    rw [hp0']
  have hv_ne_lits0 : B.v ≠ B.lits ⟨0, by omega⟩ := by
    intro heq
    by_cases hm0 : 0 < m
    · let j₁ : Fin t := ⟨i₀.val + 1, by omega⟩
      have hj₁_gt : i₀ < j₁ := by change i₀.val < i₀.val + 1; omega
      apply hnot_in_I j₁ hj₁_gt
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Or.inr ⟨⟨0, by omega⟩, ?_⟩⟩
      have hbl : B.lits ⟨0, by omega⟩ = q j₁.castSucc := by
        simp only [B, hm0, ↓reduceDIte, add_zero, j₁]; rfl
      have hqeq : q j₁.castSucc = a.negate := by rw [← hbl, ← heq]
      have hp0' : p (⟨0, by omega⟩ : Fin s).castSucc = a := hp0
      rw [hqeq, hp0', literal_var_negate]
    · have hpeq : a.negate = a := by
        have h0 : p ⟨0, by omega⟩ = a := hp0
        simpa only [B, hm0, ↓reduceDIte, Nat.zero_sub, h0] using heq
      exact literal_ne_negate a hpeq.symm
  have hB : B.IsProper :=
    BiCycle.isProper_iff_not_endpoints_match.mpr
      ⟨hl2, hinj_var, hu_var, hv_var, fun ⟨_, hv⟩ ↦ hv_ne_lits0 hv⟩
  refine ⟨l, B, hB, fun j ↦ ?_⟩
  by_cases hj0 : j.val = 0
  · have hj_eq : j = 0 := Fin.ext hj0
    rw [hj_eq, BiCycle.clauses_zero]
    change ClauseSetImplies ψ (q i₀.castSucc) (B.lits ⟨0, by omega⟩)
    by_cases hm0 : 0 < m
    · have hidx : (⟨i₀.val + 1 + 0, by omega⟩ : Fin (t + 1)) = i₀.succ :=
        Fin.ext (by simp)
      have hbl : B.lits ⟨0, by omega⟩ = q i₀.succ := by
        simp only [B, hm0, ↓reduceDIte, hidx]
      rw [hbl]
      exact hqstep i₀
    · have hidx : i₀.succ = Fin.last t := Fin.ext (by simp; omega)
      have hp0' : p ⟨0, by omega⟩ = a := hp0
      have hstep : ClauseSetImplies ψ (q i₀.castSucc) a := by
        have h := hqstep i₀
        rwa [hidx, hqlast] at h
      simpa only [B, hm0, ↓reduceDIte, Nat.zero_sub, hp0'] using hstep
  · by_cases hjl : j.val < l
    · rw [BiCycle.clauses_mid B hB.one_le (by omega) hjl]
      change ClauseSetImplies ψ (B.lits ⟨j.val - 1, by omega⟩) (B.lits ⟨j.val, hjl⟩)
      by_cases hjm : j.val < m
      · have hj1m : j.val - 1 < m := by omega
        let idx : Fin t := ⟨i₀.val + j.val, by omega⟩
        have h1 : (⟨i₀.val + 1 + (j.val - 1), by omega⟩ : Fin (t + 1)) = idx.castSucc :=
          Fin.ext (by simp [idx]; omega)
        have h2 : (⟨i₀.val + 1 + j.val, by omega⟩ : Fin (t + 1)) = idx.succ :=
          Fin.ext (by simp [idx]; omega)
        have hbl1 : B.lits ⟨j.val - 1, by omega⟩ = q idx.castSucc := by
          simp only [B, hj1m, ↓reduceDIte, h1]
        have hbl2 : B.lits ⟨j.val, hjl⟩ = q idx.succ := by
          simp only [B, hjm, ↓reduceDIte, h2]
        rw [hbl1, hbl2]
        exact hqstep idx
      · by_cases hjeq : j.val = m
        · have hj1m : j.val - 1 < m := by omega
          let idx : Fin t := ⟨t - 1, by omega⟩
          have h1 : (⟨i₀.val + 1 + (j.val - 1), by omega⟩ : Fin (t + 1)) = idx.castSucc :=
            Fin.ext (by simp [idx]; omega)
          have h2 : idx.succ = Fin.last t := Fin.ext (by simp [idx]; omega)
          have hp0' : p ⟨j.val - m, by omega⟩ = a := by
            have h0 : (⟨j.val - m, by omega⟩ : Fin (s + 1)) = 0 := Fin.ext (by simp; omega)
            rw [h0, hp0]
          have hbl1 : B.lits ⟨j.val - 1, by omega⟩ = q idx.castSucc := by
            simp only [B, hj1m, ↓reduceDIte, h1]
          have hbl2 : B.lits ⟨j.val, hjl⟩ = a := by
            simp only [B, hjm, ↓reduceDIte, hp0']
          have hstep : ClauseSetImplies ψ (q idx.castSucc) a := by
            have h := hqstep idx
            rwa [h2, hqlast] at h
          rw [hbl1, hbl2]
          exact hstep
        · have hj1m : ¬ j.val - 1 < m := by omega
          let idx : Fin s := ⟨j.val - 1 - m, by omega⟩
          have h1 : (⟨j.val - 1 - m, by omega⟩ : Fin (s + 1)) = idx.castSucc := Fin.ext rfl
          have h2 : (⟨j.val - m, by omega⟩ : Fin (s + 1)) = idx.succ :=
            Fin.ext (by simp [idx]; omega)
          have hbl1 : B.lits ⟨j.val - 1, by omega⟩ = p idx.castSucc := by
            simp only [B, hj1m, ↓reduceDIte, h1]
          have hbl2 : B.lits ⟨j.val, hjl⟩ = p idx.succ := by
            simp only [B, hjm, ↓reduceDIte, h2]
          rw [hbl1, hbl2]
          exact hpstep idx
    · have hj_val : j.val = l := by have hj_lt := j.isLt; omega
      have hj_eq : j = Fin.last l := Fin.ext hj_val
      rw [hj_eq, BiCycle.clauses_last]
      change ClauseSetImplies ψ (B.lits ⟨l - 1, by omega⟩) a.negate
      have hl1m : ¬ l - 1 < m := by omega
      let idx : Fin s := ⟨s - 1, by omega⟩
      have h1 : (⟨l - 1 - m, by omega⟩ : Fin (s + 1)) = idx.castSucc :=
        Fin.ext (by simp [idx, l]; omega)
      have h2 : idx.succ = Fin.last s := Fin.ext (by simp [idx]; omega)
      have hbl1 : B.lits ⟨l - 1, by omega⟩ = p idx.castSucc := by
        simp only [B, hl1m, ↓reduceDIte, h1]
      have hstep : ClauseSetImplies ψ (p idx.castSucc) a.negate := by
        have h := hpstep idx
        rwa [h2, hplast] at h
      rw [hbl1]
      exact hstep

end BiCycles

end CslibFrontier.Logics.Propositional
