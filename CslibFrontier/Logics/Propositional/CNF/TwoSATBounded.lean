/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Logics.Propositional.CNF.Vars
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.Count
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded-occurrence `2SAT` and occurrence splitting

`CslibFrontier.Logics.Propositional.TwoSATBounded k` (`2SAT_k`) restricts `Cslib.Complexity.TwoSAT`
to conjunctive normal form formulas in which every propositional variable has at most `k` total
literal occurrences, with `TwoSATThree` denoting `2SAT_3`.

Occurrence splitting (`splitTwoSAT`) replaces the `|φ.vars|` literal occurrences of a `2CNF`
formula `φ` by fresh variables `0, …, |φ.vars| - 1` and links all occurrences of each original
variable in a directed binary implication cycle, preserving satisfiability while guaranteeing at
most `3` occurrences per variable, `(splitTwoSAT φ).numVars = φ.vars.length`, and
`(splitTwoSAT φ).length = φ.length + φ.vars.length`.
-/

public section

namespace CslibFrontier.Logics.Propositional

open Cslib.Complexity Cslib.Logic.PL

/-- **`2SAT_k`**: satisfiable `2CNF` formulas over `ℕ` in which every variable has at most `k`
total literal occurrences. -/
def TwoSATBounded (k : ℕ) : Set (CNF ℕ) :=
  {φ | (∀ c ∈ φ, c.length ≤ 2) ∧ (∀ v, φ.vars.count v ≤ k) ∧ φ.Satisfiable}

/-- **`2SAT_3`**: satisfiable `2CNF` formulas with at most `3` occurrences per variable. -/
abbrev TwoSATThree : Set (CNF ℕ) := TwoSATBounded 3

theorem mem_TwoSATBounded {k : ℕ} {φ : CNF ℕ} :
    φ ∈ TwoSATBounded k ↔
      (∀ c ∈ φ, c.length ≤ 2) ∧ (∀ v, φ.vars.count v ≤ k) ∧ φ.Satisfiable :=
  Iff.rfl

theorem twoSATBounded_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    TwoSATBounded k₁ ⊆ TwoSATBounded k₂ :=
  fun _ ⟨hw, ho, hs⟩ => ⟨hw, fun v => (ho v).trans h, hs⟩

theorem twoSATBounded_subset_TwoSAT (k : ℕ) : TwoSATBounded k ⊆ TwoSAT :=
  fun _ ⟨hw, _, hs⟩ => ⟨hw, hs⟩

/-- In any formula where every variable occurs at most `k` times, the total number of literal
occurrences is at most `k * φ.numVars`. -/
theorem length_vars_le_mul_numVars {k : ℕ} {φ : CNF ℕ} (h : ∀ v, φ.vars.count v ≤ k) :
    φ.vars.length ≤ k * φ.numVars := by
  have hp : φ.distinctVars.Perm φ.vars.dedup :=
    (List.perm_ext_iff_of_nodup (CNF.nodup_distinctVars φ) (List.nodup_dedup _)).2
      fun v => by simp [CNF.mem_distinctVars]
  have hsum : (φ.distinctVars.map fun v => φ.vars.count v).sum = φ.vars.length := by
    rw [(hp.map _).sum_eq, List.sum_map_count_dedup_eq_length]
  rw [← hsum, ← CNF.length_distinctVars]
  calc (φ.distinctVars.map fun v => φ.vars.count v).sum
      ≤ (φ.distinctVars.map fun _ => k).sum := List.sum_le_sum fun v _ => h v
    _ = k * φ.distinctVars.length := by simp [Nat.mul_comm]

/-- In any formula without the empty clause, `φ.length ≤ φ.vars.length`. -/
theorem length_le_length_vars_of_nil_notMem {φ : CNF ℕ} (hnil : [] ∉ φ) :
    φ.length ≤ φ.vars.length := by
  rw [CNF.length_vars]
  calc φ.length
      = (φ.map fun _ => 1).sum := by simp
    _ ≤ (φ.map List.length).sum :=
        List.sum_le_sum fun c hc => List.length_pos_iff.mpr fun he => hnil (he ▸ hc)

/-- Boolean test checking whether every clause of `φ` has width at most `2`. -/
def isTwoCNF (φ : CNF ℕ) : Bool :=
  (List.range φ.length).all fun i ↦ decide (((φ[i]?).getD []).length ≤ 2)

theorem isTwoCNF_eq_true_iff {φ : CNF ℕ} :
    isTwoCNF φ = true ↔ ∀ c ∈ φ, c.length ≤ 2 := by
  simp only [isTwoCNF, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨fun h c hc ↦ ?_, fun h i hi ↦ ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    simpa [List.getElem?_eq_getElem hi] using h i hi
  · rw [List.getElem?_eq_getElem hi]
    exact h φ[i] (List.getElem_mem hi)

private def occAfter (vs : List ℕ) (i : ℕ) : List ℕ :=
  (List.range vs.length).filter fun j ↦
    decide (i < j) && decide ((vs[j]?).getD 0 = (vs[i]?).getD 0)

private def occAll (vs : List ℕ) (i : ℕ) : List ℕ :=
  (List.range vs.length).filter fun j ↦ decide ((vs[j]?).getD 0 = (vs[i]?).getD 0)

/-- Cyclic successor of occurrence index `i < vs.length` among all positions sharing the variable
`(vs[i]?).getD 0`: the next occurrence strictly after `i`,
  or the first occurrence when `i` is last. -/
def nextOcc (vs : List ℕ) (i : ℕ) : ℕ :=
  if (occAfter vs i).isEmpty then (occAll vs i).headD i else (occAfter vs i).headD i

private lemma headD_mem_of_not_isEmpty {l : List ℕ} {d : ℕ} (h : l.isEmpty = false) :
    l.headD d ∈ l := by
  cases l with
  | nil => simp at h
  | cons a rest => simp

private lemma headD_le_of_mem_filter_range {n d x : ℕ} {p : ℕ → Bool}
    (hx : x ∈ (List.range n).filter p) :
    ((List.range n).filter p).headD d ≤ x := by
  have hpw : ((List.range n).filter p).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter p
  cases h : (List.range n).filter p with
  | nil => rw [h] at hx; cases hx
  | cons a rest =>
    rw [h] at hpw hx
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_rfl
    · exact (List.pairwise_cons.mp hpw).1 x hmem |>.le

private lemma nextOcc_lt_and_eq {vs : List ℕ} {i : ℕ} (hi : i < vs.length) :
    nextOcc vs i < vs.length ∧ (vs[nextOcc vs i]?).getD 0 = (vs[i]?).getD 0 := by
  unfold nextOcc
  by_cases hemp : (occAfter vs i).isEmpty = true
  · simp only [hemp, ↓reduceIte]
    have hi_mem : i ∈ occAll vs i := by
      simp [occAll, hi]
    have hne : (occAll vs i).isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr fun hnil ↦ by simp [hnil] at hi_mem
    have hmem := headD_mem_of_not_isEmpty (d := i) hne
    simp only [occAll, List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
    exact hmem
  · have hne : (occAfter vs i).isEmpty = false := Bool.eq_false_iff.mpr hemp
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hmem := headD_mem_of_not_isEmpty (d := i) hne
    simp only [occAfter, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at hmem
    exact ⟨hmem.1, hmem.2.2⟩

private lemma nextOcc_injOn_range (vs : List ℕ) :
    ∀ i₁ ∈ List.range vs.length, ∀ i₂ ∈ List.range vs.length,
      nextOcc vs i₁ = nextOcc vs i₂ → i₁ = i₂ := by
  intro i₁ hi₁ i₂ hi₂ heq
  rw [List.mem_range] at hi₁ hi₂
  have h₁ := nextOcc_lt_and_eq hi₁
  have h₂ := nextOcc_lt_and_eq hi₂
  have hv : (vs[i₁]?).getD 0 = (vs[i₂]?).getD 0 := by
    rw [← h₁.2, heq, h₂.2]
  have step_contradiction {a b : ℕ} (ha : a < vs.length) (hb : b < vs.length)
      (hab : a < b) (hvab : (vs[a]?).getD 0 = (vs[b]?).getD 0)
      (hn : nextOcc vs a = nextOcc vs b) : False := by
    have hb_after : b ∈ occAfter vs a := by
      simp [occAfter, hb, hab, hvab]
    have hne_a : (occAfter vs a).isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr fun hnil ↦ by simp [hnil] at hb_after
    have hna_eq : nextOcc vs a = (occAfter vs a).headD a := by
      simp [nextOcc, hne_a]
    have hna_mem : nextOcc vs a ∈ occAfter vs a := by
      rw [hna_eq]
      exact headD_mem_of_not_isEmpty hne_a
    have hna_gt : a < nextOcc vs a := by
      simp only [occAfter, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hna_mem
      exact hna_mem.2.1
    have hna_le : nextOcc vs a ≤ b := by
      rw [hna_eq]
      exact headD_le_of_mem_filter_range hb_after
    by_cases hemp_b : (occAfter vs b).isEmpty = true
    · have hnb_eq : nextOcc vs b = (occAll vs b).headD b := by simp [nextOcc, hemp_b]
      have ha_all : a ∈ occAll vs b := by
        rw [occAll, List.mem_filter]
        exact ⟨List.mem_range.mpr ha, decide_eq_true hvab⟩
      have hnb_le : (occAll vs b).headD b ≤ a := headD_le_of_mem_filter_range ha_all
      rw [hn, hnb_eq] at hna_gt
      omega
    · have hne_b : (occAfter vs b).isEmpty = false := Bool.eq_false_iff.mpr hemp_b
      have hnb_eq : nextOcc vs b = (occAfter vs b).headD b := by simp [nextOcc, hne_b]
      have hnb_gt : b < (occAfter vs b).headD b := by
        have hm := headD_mem_of_not_isEmpty (d := b) hne_b
        rw [occAfter, List.mem_filter] at hm
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hm.2).1
      rw [hn, hnb_eq] at hna_le
      omega
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · exact False.elim (step_contradiction hi₁ hi₂ hlt hv heq)
  · rfl
  · exact False.elim (step_contradiction hi₂ hi₁ hgt hv.symm heq.symm)

/-- Total number of literal occurrences in the first `i` clauses of `φ`. -/
def prefixLitCount (φ : CNF ℕ) (i : ℕ) : ℕ :=
  ((List.range i).flatMap fun i' ↦ (φ[i']?).getD []).length

private lemma prefixLitCount_eq_take (φ : CNF ℕ) {i : ℕ} (hi : i ≤ φ.length) :
    prefixLitCount φ i = (CNF.vars (φ.take i)).length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi_lt : i < φ.length := Nat.lt_of_succ_le hi
    have htake : φ.take (i + 1) = φ.take i ++ [φ[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi_lt]
      rfl
    rw [prefixLitCount, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.length_append, List.getElem?_eq_getElem hi_lt, Option.getD_some,
      show ((List.range i).flatMap fun i' ↦ (φ[i']?).getD []).length = prefixLitCount φ i from rfl,
      ih hi_lt.le, htake, CNF.vars_append, List.length_append]
    simp [CNF.vars]

/-- Clause `i` of `φ` with its literals replaced by fresh variables `prefixLitCount φ i + j`. -/
def replacedClause (φ : CNF ℕ) (i : ℕ) : Clause ℕ :=
  let c := (φ[i]?).getD []
  (List.range c.length).map fun j ↦ (prefixLitCount φ i + j, ((c[j]?).getD (0, false)).2)

/-- All clauses of `φ` with each literal occurrence assigned its flat index `0, …, |φ.vars| - 1`. -/
def replacedClauses (φ : CNF ℕ) : CNF ℕ :=
  (List.range φ.length).map (replacedClause φ)

/-- Binary implication clauses `(i → nextOcc vs i)` linking all occurrences of each variable. -/
def cycleClauses (vs : List ℕ) : CNF ℕ :=
  (List.range vs.length).map fun i ↦ [(i, false), (nextOcc vs i, true)]

/-- Unchecked occurrence-splitting core `replacedClauses φ ++ cycleClauses φ.vars`. -/
def splitTwoSATCore (φ : CNF ℕ) : CNF ℕ :=
  replacedClauses φ ++ cycleClauses φ.vars

/-- Total occurrence-splitting map from `TwoSAT` to `TwoSATThree`: non-`2CNF` inputs map to `[[]]`,
and `2CNF` inputs have their literal occurrences split via `splitTwoSATCore φ`. -/
def splitTwoSAT (φ : CNF ℕ) : CNF ℕ :=
  if isTwoCNF φ then splitTwoSATCore φ else [[]]

private lemma length_replacedClauses (φ : CNF ℕ) :
    (replacedClauses φ).length = φ.length := by
  simp [replacedClauses]

private lemma relabel_replacedClauses (φ : CNF ℕ) :
    (replacedClauses φ).relabel (fun idx ↦ (φ.vars[idx]?).getD 0) = φ := by
  refine List.ext_getElem (by simp [CNF.relabel, replacedClauses]) fun i hi₁ hi₂ ↦ ?_
  simp only [CNF.relabel, replacedClauses, List.getElem_map, List.getElem_range]
  have hpre : prefixLitCount φ i = (CNF.vars (φ.take i)).length := prefixLitCount_eq_take φ hi₂.le
  have hsplit : φ.vars =
      CNF.vars (φ.take i) ++ φ[i].map Prod.fst ++ CNF.vars (φ.drop (i + 1)) := by
    have hphi : φ = φ.take i ++ [φ[i]] ++ φ.drop (i + 1) := by
      conv_lhs => rw [← List.take_append_drop i φ, List.drop_eq_getElem_cons hi₂]
      simp
    conv_lhs => rw [hphi]
    rw [CNF.vars_append, CNF.vars_append]
    simp [CNF.vars]
  refine List.ext_getElem (by simp [Clause.relabel, replacedClause, List.getElem?_eq_getElem hi₂])
    fun j hj₁ hj₂ ↦ ?_
  simp only [Clause.relabel, replacedClause, List.getElem?_eq_getElem hi₂, Option.getD_some,
    List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hj₂, Prod.map_apply, id_eq]
  have hvar : φ.vars[prefixLitCount φ i + j]? = some (φ[i][j]).1 := by
    rw [hsplit, hpre, List.append_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simp [hj₂])]
    simp [List.getElem?_eq_getElem hj₂]
  rw [hvar]
  exact Prod.eta _

private lemma vars_replacedClauses (φ : CNF ℕ) :
    (replacedClauses φ).vars = List.range φ.vars.length := by
  induction φ using List.reverseRecOn with
  | nil => rfl
  | append_singleton φ c ih =>
    have hsplit : replacedClauses (φ ++ [c]) =
        replacedClauses φ ++ [replacedClause (φ ++ [c]) φ.length] := by
      simp only [replacedClauses, List.length_append, List.length_singleton, List.range_succ,
        List.map_append, List.map_singleton]
      congr 1
      refine List.map_congr_left fun i hi ↦ ?_
      have hi_lt : i < φ.length := List.mem_range.mp hi
      have hp : prefixLitCount (φ ++ [c]) i = prefixLitCount φ i := by
        rw [prefixLitCount_eq_take _ (by simp; omega), prefixLitCount_eq_take _ hi_lt.le,
          List.take_append_of_le_length hi_lt.le]
      simp [replacedClause, List.getElem?_append_left hi_lt, hp]
    have hlast : (replacedClause (φ ++ [c]) φ.length).map Prod.fst =
        (List.range c.length).map ((CNF.vars φ).length + ·) := by
      have hp : prefixLitCount (φ ++ [c]) φ.length = (CNF.vars φ).length := by
        rw [prefixLitCount_eq_take _ (by simp), List.take_append_of_le_length le_rfl,
          List.take_length]
      simp [replacedClause, hp, Function.comp_def]
    have hsingle : CNF.vars [replacedClause (φ ++ [c]) φ.length] =
        (replacedClause (φ ++ [c]) φ.length).map Prod.fst := by
      simp [CNF.vars]
    have hvars_app : (CNF.vars (φ ++ [c])).length = (CNF.vars φ).length + c.length := by
      simp [CNF.vars]
    rw [hsplit, CNF.vars_append, ih, hsingle, hlast, hvars_app, List.range_add]

private lemma count_vars_cycleClauses (vs : List ℕ) (x : ℕ) :
    (cycleClauses vs).vars.count x = if x < vs.length then 2 else 0 := by
  have hvars_eq : (cycleClauses vs).vars =
      (List.range vs.length).flatMap fun i ↦ [i, nextOcc vs i] := by
    unfold cycleClauses CNF.vars
    induction (List.range vs.length) with
    | nil => rfl
    | cons i is ih => simp [List.flatMap_cons, ← ih]
  have hcount_sum : ((List.range vs.length).flatMap fun i ↦ [i, nextOcc vs i]).count x =
      (List.range vs.length).count x + ((List.range vs.length).map (nextOcc vs)).count x := by
    induction (List.range vs.length) with
    | nil => rfl
    | cons i is ih =>
      simp only [List.flatMap_cons, List.count_append, ih, List.map_cons]
      simp only [List.count_cons, List.count_nil]
      omega
  rw [hvars_eq, hcount_sum]
  have hnodup_map : ((List.range vs.length).map (nextOcc vs)).Nodup :=
    (List.nodup_range).map_on (nextOcc_injOn_range vs)
  by_cases hx : x < vs.length
  · simp only [hx, ↓reduceIte]
    have h1 : (List.range vs.length).count x = 1 :=
      List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hx)
    have hsurj : x ∈ (List.range vs.length).map (nextOcc vs) := by
      classical
      let f : Fin vs.length → Fin vs.length := fun a ↦
        ⟨nextOcc vs a.1, (nextOcc_lt_and_eq a.2).1⟩
      have hfinj : Function.Injective f := fun a b hab ↦
        Fin.ext (nextOcc_injOn_range vs a.1 (List.mem_range.mpr a.2)
          b.1 (List.mem_range.mpr b.2) (congrArg Fin.val hab))
      obtain ⟨a, ha⟩ := Finite.surjective_of_injective hfinj ⟨x, hx⟩
      exact List.mem_map.mpr ⟨a.1, List.mem_range.mpr a.2, congrArg Fin.val ha⟩
    have h2 : ((List.range vs.length).map (nextOcc vs)).count x = 1 :=
      List.count_eq_one_of_mem hnodup_map hsurj
    omega
  · simp only [hx, ↓reduceIte]
    have h1 : (List.range vs.length).count x = 0 :=
      List.count_eq_zero.mpr (by simp [hx])
    have h2 : ((List.range vs.length).map (nextOcc vs)).count x = 0 := by
      refine List.count_eq_zero.mpr fun hmem ↦ hx ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
      exact (nextOcc_lt_and_eq (List.mem_range.mp hi)).1
    omega

private lemma count_vars_splitTwoSATCore (φ : CNF ℕ) (x : ℕ) :
    (splitTwoSATCore φ).vars.count x = if x < φ.vars.length then 3 else 0 := by
  rw [splitTwoSATCore, CNF.vars_append, List.count_append, vars_replacedClauses,
    count_vars_cycleClauses]
  by_cases hx : x < φ.vars.length
  · have h1 : (List.range φ.vars.length).count x = 1 :=
      List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hx)
    simp [hx, h1]
  · have h1 : (List.range φ.vars.length).count x = 0 :=
      List.count_eq_zero.mpr (by simp [hx])
    simp [hx, h1]

private lemma eval_cycleClauses_agree {vs : List ℕ} {τ : ℕ → Bool}
    (hτ : (cycleClauses vs).eval τ = true) {i₁ i₂ : ℕ}
    (hi₁ : i₁ < vs.length) (hi₂ : i₂ < vs.length)
    (hv : (vs[i₁]?).getD 0 = (vs[i₂]?).getD 0) :
    τ i₁ = τ i₂ := by
  have hstep : ∀ i < vs.length, τ i = true → τ (nextOcc vs i) = true := by
    intro i hi hti
    have hcl := (CNF.eval_eq_true_iff τ (cycleClauses vs)).mp hτ
      [(i, false), (nextOcc vs i, true)]
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa [Clause.eval, Literal.eval, hti] using hcl
  have hmono : ∀ d a b, b - a = d → a ≤ b → b < vs.length →
      (vs[a]?).getD 0 = (vs[b]?).getD 0 → τ a = true → τ b = true := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a b hd hab hb hvab hta
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact hta
      · have hb_after : b ∈ occAfter vs a := by
          simp [occAfter, hb, hlt, hvab]
        have hne : (occAfter vs a).isEmpty = false :=
          List.isEmpty_eq_false_iff.mpr fun hnil ↦ by simp [hnil] at hb_after
        have hna_eq : nextOcc vs a = (occAfter vs a).headD a := by simp [nextOcc, hne]
        have hna_mem : nextOcc vs a ∈ occAfter vs a := by
          rw [hna_eq]; exact headD_mem_of_not_isEmpty hne
        have hna_gt : a < nextOcc vs a := by
          simp only [occAfter, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hna_mem
          exact hna_mem.2.1
        have hna_le : nextOcc vs a ≤ b := by
          rw [hna_eq]; exact headD_le_of_mem_filter_range hb_after
        have ha_lt : a < vs.length := lt_trans hlt hb
        have hna_v := (nextOcc_lt_and_eq ha_lt).2
        exact ih (b - nextOcc vs a) (by omega) (nextOcc vs a) b rfl hna_le hb
          (hna_v.trans hvab) (hstep a ha_lt hta)
  have hex_last : ∀ d a, vs.length - a = d → a < vs.length →
      ∃ m < vs.length, a ≤ m ∧ (vs[m]?).getD 0 = (vs[a]?).getD 0 ∧
        (occAfter vs m).isEmpty = true := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a hd ha
      by_cases hemp : (occAfter vs a).isEmpty = true
      · exact ⟨a, ha, le_rfl, rfl, hemp⟩
      · have hne : (occAfter vs a).isEmpty = false := Bool.eq_false_iff.mpr hemp
        have hmem := headD_mem_of_not_isEmpty (d := a) hne
        set j := (occAfter vs a).headD a
        simp only [occAfter, List.mem_filter, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq] at hmem
        obtain ⟨m, hm_lt, hjm, hvm, hemp_m⟩ :=
          ih (vs.length - j) (by omega) j rfl hmem.1
        exact ⟨m, hm_lt, le_trans hmem.2.1.le hjm, hvm.trans hmem.2.2, hemp_m⟩
  have himp : ∀ a b, a < vs.length → b < vs.length →
      (vs[a]?).getD 0 = (vs[b]?).getD 0 → τ a = true → τ b = true := by
    intro a b ha hb hvab hta
    obtain ⟨m, hm_lt, ham, hvm, hemp_m⟩ := hex_last (vs.length - a) a rfl ha
    have htm : τ m = true := hmono (m - a) a m rfl ham hm_lt hvm.symm hta
    have hnm_eq : nextOcc vs m = (occAll vs m).headD m := by simp [nextOcc, hemp_m]
    have hb_all : b ∈ occAll vs m := by
      rw [occAll, List.mem_filter]
      exact ⟨List.mem_range.mpr hb, decide_eq_true (hvab.symm.trans hvm.symm)⟩
    have hnm_le : nextOcc vs m ≤ b := by
      rw [hnm_eq]; exact headD_le_of_mem_filter_range hb_all
    have htnm : τ (nextOcc vs m) = true := hstep m hm_lt htm
    have hvnm : (vs[nextOcc vs m]?).getD 0 = (vs[b]?).getD 0 :=
      ((nextOcc_lt_and_eq hm_lt).2).trans (hvm.trans hvab)
    exact hmono (b - nextOcc vs m) (nextOcc vs m) b rfl hnm_le hb hvnm htnm
  exact Bool.eq_iff_iff.mpr ⟨himp i₁ i₂ hi₁ hi₂ hv, himp i₂ i₁ hi₂ hi₁ hv.symm⟩

private lemma satisfiable_splitTwoSATCore_iff (φ : CNF ℕ) :
    (splitTwoSATCore φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    rw [splitTwoSATCore, CNF.eval_append, Bool.and_eq_true] at hτ
    classical
    let σ : ℕ → Bool := fun v ↦
      if h : ∃ i < φ.vars.length, (φ.vars[i]?).getD 0 = v then τ (Classical.choose h) else false
    refine ⟨σ, ?_⟩
    have hrel := relabel_replacedClauses φ
    rw [← hrel, CNF.eval_relabel]
    refine (CNF.eval_congr fun idx hidx ↦ ?_).trans hτ.1
    rw [vars_replacedClauses, List.mem_range] at hidx
    have hex : ∃ i < φ.vars.length, (φ.vars[i]?).getD 0 = (φ.vars[idx]?).getD 0 :=
      ⟨idx, hidx, rfl⟩
    change σ ((φ.vars[idx]?).getD 0) = τ idx
    simp only [σ, dite_eq_left hex]
    exact eval_cycleClauses_agree hτ.2 (Classical.choose_spec hex).1 hidx
      (Classical.choose_spec hex).2
  · rintro ⟨σ, hσ⟩
    let τ : ℕ → Bool := fun idx ↦ σ ((φ.vars[idx]?).getD 0)
    refine ⟨τ, ?_⟩
    rw [splitTwoSATCore, CNF.eval_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have hrel := relabel_replacedClauses φ
      have heval : (replacedClauses φ).eval τ = φ.eval σ := by
        conv_rhs => rw [← hrel]
        rw [CNF.eval_relabel]
        rfl
      exact heval.trans hσ
    · rw [CNF.eval_eq_true_iff]
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      rw [List.mem_range] at hi
      have hnxt := nextOcc_lt_and_eq hi
      simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval, τ, hnxt.2]
      cases σ ((φ.vars[i]?).getD 0) <;> rfl

/-- `splitTwoSAT φ` belongs to `TwoSATThree` if and only if `φ` belongs to `TwoSAT`. -/
theorem splitTwoSAT_mem_TwoSATThree_iff (φ : CNF ℕ) :
    splitTwoSAT φ ∈ TwoSATThree ↔ φ ∈ TwoSAT := by
  unfold splitTwoSAT
  by_cases hw : isTwoCNF φ = true
  · simp only [hw, ↓reduceIte]
    have hw' : ∀ c ∈ φ, c.length ≤ 2 := isTwoCNF_eq_true_iff.mp hw
    have hw_out : ∀ c ∈ splitTwoSATCore φ, c.length ≤ 2 := by
      intro c hc
      rcases List.mem_append.mp hc with hc₁ | hc₂
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc₁
        rw [List.mem_range] at hi
        simpa [replacedClause, List.getElem?_eq_getElem hi] using hw' φ[i] (List.getElem_mem hi)
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc₂
        simp
    have ho_out : ∀ v, (splitTwoSATCore φ).vars.count v ≤ 3 := by
      intro v
      rw [count_vars_splitTwoSATCore]
      split_ifs <;> omega
    exact ⟨fun ⟨_, _, hs⟩ ↦ ⟨hw', (satisfiable_splitTwoSATCore_iff φ).mp hs⟩,
           fun ⟨_, hs⟩ ↦ ⟨hw_out, ho_out, (satisfiable_splitTwoSATCore_iff φ).mpr hs⟩⟩
  · have hw_false : isTwoCNF φ = false := Bool.eq_false_iff.mpr hw
    simp only [hw_false, Bool.false_eq_true, ↓reduceIte]
    have hnot_two : φ ∉ TwoSAT := fun h ↦ hw (isTwoCNF_eq_true_iff.mpr h.1)
    have hnot_three : ([[]] : CNF ℕ) ∉ TwoSATThree :=
      fun h ↦ CNF.not_satisfiable_of_nil_mem (by simp) h.2.2
    simp [hnot_two, hnot_three]

/-- For every `2CNF` formula `φ`, `splitTwoSAT φ` has `φ.vars.length` distinct variables. -/
theorem numVars_splitTwoSAT {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 2) :
    (splitTwoSAT φ).numVars = φ.vars.length := by
  rw [splitTwoSAT, ite_eq_left (isTwoCNF_eq_true_iff.mpr hφ)]
  have hfinset : (splitTwoSATCore φ).vars.toFinset = Finset.range φ.vars.length := by
    ext x
    simp only [List.mem_toFinset, ← List.count_pos_iff, count_vars_splitTwoSATCore,
      Finset.mem_range]
    split_ifs with hx <;> omega
  rw [CNF.numVars, hfinset, Finset.card_range]

/-- For non-`2CNF` formulas, `splitTwoSAT φ = [[]]` has `0` variables. -/
theorem numVars_splitTwoSAT_le (φ : CNF ℕ) :
    (splitTwoSAT φ).numVars ≤ φ.vars.length := by
  by_cases hφ : ∀ c ∈ φ, c.length ≤ 2
  · exact (numVars_splitTwoSAT hφ).le
  · have hw : isTwoCNF φ = false :=
      Bool.eq_false_iff.mpr fun h ↦ hφ (isTwoCNF_eq_true_iff.mp h)
    simp [splitTwoSAT, hw, CNF.numVars, CNF.vars]

/-- For every `2CNF` formula `φ`, `splitTwoSAT φ` has `φ.length + φ.vars.length` clauses. -/
theorem length_splitTwoSAT {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 2) :
    (splitTwoSAT φ).length = φ.length + φ.vars.length := by
  rw [splitTwoSAT, ite_eq_left (isTwoCNF_eq_true_iff.mpr hφ), splitTwoSATCore, List.length_append,
    length_replacedClauses]
  simp [cycleClauses]

end CslibFrontier.Logics.Propositional
