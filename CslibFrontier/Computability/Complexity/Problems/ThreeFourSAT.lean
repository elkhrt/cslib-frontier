/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree

import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Logics.Propositional.CNF.ModelCount.Relabel
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Tactic.FinCases

/-!
# `(3, 4)`-SAT and Polarity-Balanced `(3, 4)`-SAT

`ThreeFourSAT` is Tovey's restricted `3-SAT` decision problem: given a CNF formula `φ`
in which every clause contains `3` distinct variables and every variable occurs in at most `4`
clauses, decide whether `φ` is satisfiable.

`BalancedThreeFourSAT` strengthens the syntactic restriction by requiring in addition that every
signed literal `(v, b)` occurs at most `3` times across `φ` (so no variable occurs `4` times with
the same polarity, since any such variable could be set to satisfy all its clauses immediately).

We construct a total polynomial-time many-one reduction `toThreeFourSAT` from `ThreeSATThree` (in
which clauses have length `≤ 3` and each variable occurs `≤ 3` times) to `BalancedThreeFourSAT` by
removing tautological clauses, deduplicating repeated literals within each clause, and padding
clauses of length `1` or `2` to exact width `3` using disjoint `6`-clause forced-false `(3, 4)`-SAT
gadgets. Consequently both `BalancedThreeFourSAT` and `ThreeFourSAT` are `NP`-complete under
`Cslib.Complexity.encCNF`.

## Main definitions

* `Cslib.Complexity.IsThreeFourCNF`, `Cslib.Complexity.IsBalancedThreeFourCNF`: syntactic predicates
  for `(3, 4)`-CNF and polarity-balanced `(3, 4)`-CNF formulas.
* `Cslib.Complexity.ThreeFourSAT`, `Cslib.Complexity.BalancedThreeFourSAT`: the corresponding
  decision problems on `CNF ℕ`.
* `Cslib.Complexity.toThreeFourSAT`: polynomial-time many-one reduction from `ThreeSATThree` to
  `BalancedThreeFourSAT`.

## Main results

* `Cslib.Complexity.threeFourSAT_mem_NP`, `Cslib.Complexity.balancedThreeFourSAT_mem_NP`: membership
  in `NP`.
* `Cslib.Complexity.toThreeFourSAT_isBalanced`,
  `Cslib.Complexity.toThreeFourSAT_mem_balancedThreeFourSAT_iff`: syntactic and semantic correctness
  of `toThreeFourSAT`.
* `Cslib.Complexity.balancedThreeFourSAT_npComplete`, `Cslib.Complexity.threeFourSAT_npComplete`:
  `NP`-completeness of `BalancedThreeFourSAT` and `ThreeFourSAT`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Syntactic predicate for `(3, 4)`-SAT: every clause contains `3` distinct variables,
and every variable appears in at most `4` literal occurrences across the formula.
-/
@[expose]
def IsThreeFourCNF (φ : CNF ℕ) : Prop :=
  (∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
    ∀ v : ℕ, φ.vars.count v ≤ 4

/-- Polarity-balanced `(3, 4)`-SAT: an `IsThreeFourCNF` formula in which every signed literal
`(v, b)` appears at most `3` times. -/
@[expose]
def IsBalancedThreeFourCNF (φ : CNF ℕ) : Prop :=
  IsThreeFourCNF φ ∧ ∀ (v : ℕ) (b : Bool), φ.flatten.count (v, b) ≤ 3

/-- Tovey's `(3, 4)`-SAT decision problem. -/
@[expose]
def ThreeFourSAT : Set (CNF ℕ) :=
  {φ | IsThreeFourCNF φ ∧ φ.Satisfiable}

/-- The polarity-balanced `(3, 4)`-SAT decision problem. -/
@[expose]
def BalancedThreeFourSAT : Set (CNF ℕ) :=
  {φ | IsBalancedThreeFourCNF φ ∧ φ.Satisfiable}

theorem balancedThreeFourSAT_subset_threeFourSAT :
    BalancedThreeFourSAT ⊆ ThreeFourSAT :=
  fun _ h ↦ ⟨h.1.1, h.2⟩

/-! ### Decidable syntactic checks and `NP` membership -/

/-- Executable Boolean check for `IsThreeFourCNF`. -/
def checkThreeFourCNF (φ : CNF ℕ) : Bool :=
  (φ.all fun c ↦ decide (c.length = 3) && decide (c.map Prod.fst).Nodup) &&
    (φ.vars.all fun v ↦ decide (φ.vars.count v ≤ 4))

theorem checkThreeFourCNF_eq_true_iff (φ : CNF ℕ) :
    checkThreeFourCNF φ = true ↔ IsThreeFourCNF φ := by
  simp only [checkThreeFourCNF, IsThreeFourCNF, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  refine ⟨fun ⟨hc, hv⟩ ↦ ⟨hc, fun v ↦ ?_⟩, fun ⟨hc, hv⟩ ↦ ⟨hc, fun v _ ↦ hv v⟩⟩
  by_cases hmem : v ∈ φ.vars
  · exact hv v hmem
  · simp [List.count_eq_zero.mpr hmem]

/-- Executable Boolean check for `IsBalancedThreeFourCNF`. -/
def checkBalancedThreeFourCNF (φ : CNF ℕ) : Bool :=
  checkThreeFourCNF φ &&
    (φ.vars.all fun v ↦
      decide (φ.flatten.count (v, true) ≤ 3) && decide (φ.flatten.count (v, false) ≤ 3))

theorem checkBalancedThreeFourCNF_eq_true_iff (φ : CNF ℕ) :
    checkBalancedThreeFourCNF φ = true ↔ IsBalancedThreeFourCNF φ := by
  simp only [checkBalancedThreeFourCNF, IsBalancedThreeFourCNF, Bool.and_eq_true,
    checkThreeFourCNF_eq_true_iff, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun ⟨h34, hlit⟩ ↦ ⟨h34, fun v b ↦ ?_⟩,
    fun ⟨h34, hlit⟩ ↦ ⟨h34, fun v _ ↦ ⟨hlit v true, hlit v false⟩⟩⟩
  by_cases hmem : v ∈ φ.vars
  · cases b
    · exact (hlit v hmem).2
    · exact (hlit v hmem).1
  · have hnot : (v, b) ∉ φ.flatten := fun hl ↦
      hmem (List.mem_map.mpr ⟨(v, b), hl, rfl⟩)
    simp [List.count_eq_zero.mpr hnot]

private lemma clauseVarsNodup_eq (c : Clause ℕ) :
    decide (c.map Prod.fst).Nodup =
      (c.zipIdx.all fun p ↦ c.zipIdx.all fun q ↦
        decide (p.2 = q.2 ∨ p.1.1 ≠ q.1.1)) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, List.nodup_iff_getElem?_ne_getElem?]
  constructor
  · intro hnd p hp q hq
    by_cases hij : p.2 = q.2
    · exact Or.inl hij
    · right
      obtain ⟨_, hp_lt0, hp_eq0⟩ := List.mem_zipIdx hp
      obtain ⟨_, hq_lt0, hq_eq0⟩ := List.mem_zipIdx hq
      have hp_lt : p.2 < c.length := by omega
      have hq_lt : q.2 < c.length := by omega
      have hp_eq : p.1 = c[p.2]'hp_lt := by simpa using hp_eq0
      have hq_eq : q.1 = c[q.2]'hq_lt := by simpa using hq_eq0
      have hp_get : (c.map Prod.fst)[p.2]? = some p.1.1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hp_lt, ← hp_eq]
        rfl
      have hq_get : (c.map Prod.fst)[q.2]? = some q.1.1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hq_lt, ← hq_eq]
        rfl
      intro hfst
      rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
      · exact hnd p.2 q.2 hlt (by simpa using hq_lt) (by rw [hp_get, hq_get, hfst])
      · exact hij heq
      · exact hnd q.2 p.2 hgt (by simpa using hp_lt) (by rw [hq_get, hp_get, hfst])
  · intro hall i j hij hj hget
    simp only [List.getElem?_map] at hget
    have hj' : j < c.length := by simpa using hj
    have hi : i < c.length := lt_trans hij hj'
    have hp : (c[i], i) ∈ c.zipIdx := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [hi], by simp⟩
    have hq : (c[j], j) ∈ c.zipIdx := by
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp [hj'], by simp⟩
    rcases hall _ hp _ hq with heq | hne
    · omega
    · simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj', Option.map_some,
        Option.some.injEq] at hget
      exact hne hget

@[fun_prop]
theorem computableInPolyTime_checkThreeFourCNF :
    ComputableInPolyTime checkThreeFourCNF encCNF encBool := by
  have heq : checkThreeFourCNF = fun φ : CNF ℕ ↦
      (φ.all fun c ↦ decide (c.length = 3) &&
        (c.zipIdx.all fun p ↦ c.zipIdx.all fun q ↦ decide (p.2 = q.2 ∨ p.1.1 ≠ q.1.1))) &&
      (φ.vars.all fun v ↦ decide (φ.vars.count v ≤ 4)) := by
    funext φ
    simp only [checkThreeFourCNF, clauseVarsNodup_eq]
  rw [heq]
  fun_prop

@[fun_prop]
theorem computableInPolyTime_checkBalancedThreeFourCNF :
    ComputableInPolyTime checkBalancedThreeFourCNF encCNF encBool := by
  unfold checkBalancedThreeFourCNF
  fun_prop

/-- NP verifier for `ThreeFourSAT`. -/
def threeFourSATVerifier (x : CNF ℕ × List Bool) : Bool :=
  checkThreeFourCNF x.1 && SAT.verifier x

/-- NP verifier for `BalancedThreeFourSAT`. -/
def balancedThreeFourSATVerifier (x : CNF ℕ × List Bool) : Bool :=
  checkBalancedThreeFourCNF x.1 && SAT.verifier x

/-- `ThreeFourSAT` belongs to `NP`. -/
theorem threeFourSAT_mem_NP : ThreeFourSAT ∈ NP encCNF := by
  have he : ThreeFourSAT = {φ | checkThreeFourCNF φ = true ∧ φ ∈ SAT} := by
    ext φ
    simp [ThreeFourSAT, checkThreeFourCNF_eq_true_iff, mem_SAT]
  refine ⟨Polynomial.X, threeFourSATVerifier, by unfold threeFourSATVerifier; fun_prop, ?_⟩
  rw [he]
  exact SAT.isVerifier.guard

/-- `BalancedThreeFourSAT` belongs to `NP`. -/
theorem balancedThreeFourSAT_mem_NP : BalancedThreeFourSAT ∈ NP encCNF := by
  have he : BalancedThreeFourSAT = {φ | checkBalancedThreeFourCNF φ = true ∧ φ ∈ SAT} := by
    ext φ
    simp [BalancedThreeFourSAT, checkBalancedThreeFourCNF_eq_true_iff, mem_SAT]
  refine ⟨Polynomial.X, balancedThreeFourSATVerifier,
    by unfold balancedThreeFourSATVerifier; fun_prop, ?_⟩
  rw [he]
  exact SAT.isVerifier.guard

/-! ### Forced-false 6-clause `(3, 4)`-SAT padding gadget -/

/-- Six-clause forced-false `(3, 4)`-SAT gadget on `6` variables `(z, a, b, c, d, e)` given by
`v : Fin 6 → V`:
1. `(¬z ∨ a ∨ b)`
2. `(¬z ∨ a ∨ ¬b)`
3. `(¬z ∨ ¬a ∨ c)`
4. `(¬c ∨ d ∨ e)`
5. `(¬c ∨ d ∨ ¬e)`
6. `(¬a ∨ ¬c ∨ ¬d)`
Every clause has `3` distinct variables, `v 0` appears `3` times (all negated, leaving `1` positive
slot free for padding a shorter clause), every `v 1 .. v 5` appears at most `4` times (and at most
`3` times per polarity), and the gadget forces `σ (v 0) = false`. -/
def forcedFalseGadget {V : Type*} (v : Fin 6 → V) : CNF V :=
  [ [(v 0, false), (v 1, true), (v 2, true)],
    [(v 0, false), (v 1, true), (v 2, false)],
    [(v 0, false), (v 1, false), (v 3, true)],
    [(v 3, false), (v 4, true), (v 5, true)],
    [(v 3, false), (v 4, true), (v 5, false)],
    [(v 1, false), (v 3, false), (v 4, false)] ]

private lemma forcedFalseGadget_eval_false_of_true {V : Type*} (v : Fin 6 → V) (σ : V → Bool)
    (hz : σ (v 0) = true) : (forcedFalseGadget v).eval σ = false := by
  simp only [forcedFalseGadget, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil,
    Literal.eval_mk, hz]
  cases σ (v 1) <;> cases σ (v 2) <;> cases σ (v 3) <;> cases σ (v 4) <;> cases σ (v 5) <;> rfl

private lemma forcedFalseGadget_eval_true_of_all_false {V : Type*} (v : Fin 6 → V) (σ : V → Bool)
    (hall : ∀ r : Fin 6, σ (v r) = false) : (forcedFalseGadget v).eval σ = true := by
  simp [forcedFalseGadget, hall]

private lemma count_forcedFalseGadget_id (x : Fin 6) :
    (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (x, true) ≤ 2 ∧
      (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (x, false) ≤ 3 ∧
      (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (x, true) +
        (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (x, false) ≤ 4 ∧
      (x = 0 →
        (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (x, true) = 0 ∧
          (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (x, false) = 3) := by
  fin_cases x <;> decide

/-- Fixed 19-clause unsatisfiable `BalancedThreeFourSAT` formula on `18` variables `0 .. 17`: three
disjoint copies of `forcedFalseGadget` forcing variables `0`, `6`, `12` to `false`, together with
the clause `(x_0 ∨ x_6 ∨ x_{12})`. -/
def unsatThreeFourCNF : CNF ℕ :=
  [(0, true), (6, true), (12, true)] ::
    (forcedFalseGadget (fun r : Fin 6 ↦ r.1) ++
      forcedFalseGadget (fun r : Fin 6 ↦ 6 + r.1) ++
      forcedFalseGadget (fun r : Fin 6 ↦ 12 + r.1))

@[local fun_prop]
private lemma computableInPolyTime_const_unsat {α : Type*} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun _ : α ↦ unsatThreeFourCNF) enc encCNF :=
  ComputableInPolyTime.const _

theorem unsatThreeFourCNF_isBalanced : IsBalancedThreeFourCNF unsatThreeFourCNF := by
  rw [← checkBalancedThreeFourCNF_eq_true_iff]
  decide

theorem not_satisfiable_unsatThreeFourCNF : ¬ unsatThreeFourCNF.Satisfiable := by
  rintro ⟨σ, hσ⟩
  simp only [unsatThreeFourCNF, CNF.eval_cons, CNF.eval_append, Bool.and_eq_true] at hσ
  rcases hσ with ⟨hcl, ⟨hg0, hg1⟩, hg2⟩
  have hz0 : σ 0 = false := by
    cases h : σ 0
    · rfl
    · rw [forcedFalseGadget_eval_false_of_true (fun r : Fin 6 ↦ r.1) σ h] at hg0
      cases hg0
  have hz6 : σ 6 = false := by
    cases h : σ 6
    · rfl
    · rw [forcedFalseGadget_eval_false_of_true (fun r : Fin 6 ↦ 6 + r.1) σ h] at hg1
      cases hg1
  have hz12 : σ 12 = false := by
    cases h : σ 12
    · rfl
    · rw [forcedFalseGadget_eval_false_of_true (fun r : Fin 6 ↦ 12 + r.1) σ h] at hg2
      cases hg2
  simp [hz0, hz6, hz12] at hcl

/-! ### Polynomial-time reduction from `ThreeSATThree` to `BalancedThreeFourSAT` -/

/-- Variable namespace for the `(3, 4)`-SAT reduction: `Sum.inl v` for an original `ThreeSATThree`
variable `v : ℕ`, and `Sum.inr (clauseIdx, (slot, role))` for the `6` variables (`role < 6`) of
padding gadget `slot ∈ {0, 1}` attached to clause `clauseIdx`. -/
abbrev PadVar := ℕ ⊕ (ℕ × (ℕ × ℕ))

/-- Framed sum encoding of `PadVar`, with original variable indices in binary (`encNat`) and
clause/slot/role coordinates in unary (`encUnary`). -/
abbrev encPadVar : PadVar ↪ List Bool :=
  encSum encNat (encPair encUnary (encPair encUnary encUnary))

/-- Injective polynomial-time codec numbering `PadVar` into `ℕ`. -/
def padVarCodec : NatCodec PadVar :=
  NatCodec.nat.sum (NatCodec.nat.pair (NatCodec.nat.pair NatCodec.nat))

theorem padVarCodec_injective : Function.Injective padVarCodec :=
  padVarCodec.injective

@[fun_prop]
theorem computableInPolyTime_padVarCodec :
    ComputableInPolyTime (fun x : PadVar ↦ padVarCodec x) encPadVar encNat := by
  unfold padVarCodec encPadVar
  fun_prop

/-- Test whether a clause `c : Clause ℕ` is tautological (contains both `(v, true)` and
`(v, false)` for some variable `v`). -/
def isTautClause (c : Clause ℕ) : Bool :=
  c.any fun l ↦ decide (l.negate ∈ c)

@[fun_prop]
private lemma computableInPolyTime_isTautClause :
    ComputableInPolyTime isTautClause (encClause encNat) encBool := by
  unfold isTautClause
  fun_prop

private lemma eval_eq_true_of_isTautClause {c : Clause ℕ} (ht : isTautClause c = true)
    (σ : ℕ → Bool) : c.eval σ = true := by
  simp only [isTautClause, List.any_eq_true, decide_eq_true_eq] at ht
  rcases ht with ⟨⟨v, b⟩, hmem, hneg⟩
  rw [Clause.eval_eq_true_iff]
  by_cases hσ : σ v = b
  · exact ⟨(v, b), hmem, hσ⟩
  · refine ⟨(v, !b), hneg, ?_⟩
    cases b <;> cases h : σ v <;> simp_all

/-- Remove duplicate literals from a clause by keeping each literal's first occurrence. -/
def dedupClause (c : Clause ℕ) : Clause ℕ :=
  (c.zipIdx.filter fun p ↦ !(c.take p.2).any (fun q ↦ decide (q = p.1))).map Prod.fst

@[fun_prop]
private lemma computableInPolyTime_dedupClause :
    ComputableInPolyTime dedupClause (encClause encNat) (encClause encNat) := by
  unfold dedupClause
  fun_prop

private lemma map_fst_zipIdx_aux {α : Type*} (L : List α) (k : ℕ) :
    (L.zipIdx k).map Prod.fst = L := by
  induction L generalizing k with
  | nil => rfl
  | cons a as ih => simp [List.zipIdx_cons, ih (k + 1)]

private lemma dedupClause_sublist (c : Clause ℕ) : (dedupClause c).Sublist c := by
  unfold dedupClause
  have hsub := (List.filter_sublist (l := c.zipIdx)
    (p := fun p ↦ !(c.take p.2).any (fun q ↦ decide (q = p.1)))).map Prod.fst
  rwa [map_fst_zipIdx_aux c 0] at hsub

private lemma mem_dedupClause_iff {c : Clause ℕ} {l : Literal ℕ} :
    l ∈ dedupClause c ↔ l ∈ c := by
  classical
  constructor
  · intro h
    exact (dedupClause_sublist c).subset h
  · intro hl
    have hex : ∃ i : ℕ, ∃ hi : i < c.length, c[i]'hi = l := List.mem_iff_getElem.mp hl
    obtain ⟨hi, hci⟩ := Nat.find_spec hex
    unfold dedupClause
    refine List.mem_map.mpr ⟨(l, Nat.find hex), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [List.mem_iff_getElem]
      exact ⟨Nat.find hex, by simpa using hi, by simp [hci]⟩
    · rw [Bool.not_eq_true', List.any_eq_false]
      intro q hq
      simp only [decide_eq_true_eq]
      rintro rfl
      obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq
      have hj_lt : j < Nat.find hex := by
        rw [List.length_take] at hj
        omega
      have hcj : c[j]'(lt_trans hj_lt hi) = q := by
        simpa [List.getElem_take] using hqj
      exact Nat.find_min hex hj_lt ⟨lt_trans hj_lt hi, hcj⟩

private lemma pairwise_lt_snd_zipIdx {α : Type*} (L : List α) (k : ℕ) :
    (L.zipIdx k).Pairwise (fun p q ↦ p.2 < q.2) := by
  induction L generalizing k with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨fun q hq ↦ ?_, ih (k + 1)⟩
    have hge := (List.mem_zipIdx hq).1
    omega

private lemma pairwise_mem_aux {R : (Literal ℕ × ℕ) → (Literal ℕ × ℕ) → Prop}
    (L : List (Literal ℕ × ℕ)) (h : L.Pairwise R) :
    L.Pairwise (fun a b ↦ a ∈ L ∧ b ∈ L ∧ R a b) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons a as ha _ ih =>
    exact List.Pairwise.cons
      (fun b hb ↦ ⟨List.mem_cons_self, List.mem_cons_of_mem a hb, ha b hb⟩)
      (ih.imp fun ⟨hx, hy, hxy⟩ ↦
        ⟨List.mem_cons_of_mem a hx, List.mem_cons_of_mem a hy, hxy⟩)

private lemma dedupClause_nodup (c : Clause ℕ) : (dedupClause c).Nodup := by
  let F := c.zipIdx.filter fun p ↦ !(c.take p.2).any (fun q ↦ decide (q = p.1))
  have hF_lt : F.Pairwise (fun p q ↦ p.2 < q.2) := (pairwise_lt_snd_zipIdx c 0).filter _
  have hF_ne : F.Pairwise (fun p q ↦ p.1 ≠ q.1) := by
    refine (pairwise_mem_aux F hF_lt).imp fun {p q} ⟨hpF, hqF, hlt⟩ heq ↦ ?_
    have hp_zip := List.mem_of_mem_filter hpF
    obtain ⟨hq_zip, hq_filt⟩ := List.mem_filter.mp hqF
    obtain ⟨_, hp_lt0, hp_eq0⟩ := List.mem_zipIdx hp_zip
    obtain ⟨_, hq_lt0, _⟩ := List.mem_zipIdx hq_zip
    have hp_lt : p.2 < c.length := by omega
    have hq_lt : q.2 < c.length := by omega
    have hp_eq : p.1 = c[p.2]'hp_lt := by simpa using hp_eq0
    have hmem_take : q.1 ∈ c.take q.2 := by
      rw [List.mem_iff_getElem]
      refine ⟨p.2, by rw [List.length_take]; omega, ?_⟩
      rw [List.getElem_take, ← hp_eq, heq]
    have hany : (c.take q.2).any (fun r ↦ decide (r = q.1)) = true :=
      List.any_eq_true.mpr ⟨q.1, hmem_take, by simp⟩
    rw [hany] at hq_filt
    cases hq_filt
  change (F.map Prod.fst).Pairwise (· ≠ ·)
  exact List.pairwise_map.mpr hF_ne

private lemma nodup_fst_dedupClause_of_not_isTautClause {c : Clause ℕ}
    (ht : isTautClause c = false) : ((dedupClause c).map Prod.fst).Nodup := by
  have hno_opp : ∀ ⦃l₁ l₂ : Literal ℕ⦄, l₁ ∈ c → l₂ ∈ c → l₁.1 = l₂.1 → l₁ = l₂ := by
    rintro ⟨v₁, b₁⟩ ⟨v₂, b₂⟩ h₁ h₂ hv
    dsimp only at hv
    subst hv
    by_cases hb : b₁ = b₂
    · subst hb; rfl
    · exfalso
      have hneg : (v₁, !b₁) = (v₁, b₂) := by cases b₁ <;> cases b₂ <;> simp_all
      have ht' : isTautClause c = true := by
        simp only [isTautClause, List.any_eq_true, decide_eq_true_eq]
        exact ⟨(v₁, b₁), h₁, by simpa [Std.Sat.Literal.negate, hneg] using h₂⟩
      rw [ht] at ht'
      cases ht'
  rw [List.nodup_map_iff_inj_on (dedupClause_nodup c)]
  intro x hx y hy hxy
  exact hno_opp (mem_dedupClause_iff.mp hx) (mem_dedupClause_iff.mp hy) hxy

/-- Clean a CNF formula by removing tautological clauses and deduplicating literals inside each
remaining clause. -/
def cleanCNF (φ : CNF ℕ) : CNF ℕ :=
  (φ.filter fun c ↦ !isTautClause c).map dedupClause

@[fun_prop]
theorem computableInPolyTime_cleanCNF :
    ComputableInPolyTime cleanCNF encCNF encCNF := by
  unfold cleanCNF
  fun_prop

private lemma satisfiable_cleanCNF_iff (φ : CNF ℕ) :
    (cleanCNF φ).Satisfiable ↔ φ.Satisfiable := by
  unfold cleanCNF
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc ↦ ?_⟩
    by_cases ht : isTautClause c = true
    · exact eval_eq_true_of_isTautClause ht σ
    · have ht' : isTautClause c = false := Bool.eq_false_iff.mpr ht
      have hmem : dedupClause c ∈ (φ.filter fun d ↦ !isTautClause d).map dedupClause :=
        List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [ht']⟩, rfl⟩
      have hcev := (CNF.eval_eq_true_iff σ _).mp hσ (dedupClause c) hmem
      rw [Clause.eval_eq_true_iff] at hcev ⊢
      rcases hcev with ⟨l, hl, hev⟩
      exact ⟨l, mem_dedupClause_iff.mp hl, hev⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, (CNF.eval_eq_true_iff σ _).mpr fun c' hc' ↦ ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    have hcev := (CNF.eval_eq_true_iff σ φ).mp hσ c (List.mem_of_mem_filter hc)
    rw [Clause.eval_eq_true_iff] at hcev ⊢
    rcases hcev with ⟨l, hl, hev⟩
    exact ⟨l, mem_dedupClause_iff.mpr hl, hev⟩

private lemma cnf_vars_cons (x : Clause ℕ) (xs : CNF ℕ) :
    CNF.vars (x :: xs) = x.map Prod.fst ++ CNF.vars xs := by
  simp [CNF.vars, List.flatten_cons]

private lemma count_vars_cleanCNF_le (φ : CNF ℕ) (v : ℕ) :
    (cleanCNF φ).vars.count v ≤ φ.vars.count v := by
  unfold cleanCNF
  induction φ with
  | nil => simp
  | cons c rest ih =>
    have hcons2 : CNF.vars (c :: rest) = (c.map Prod.fst) ++ CNF.vars rest :=
      cnf_vars_cons c rest
    cases ht : isTautClause c
    · simp only [List.filter_cons, ht, Bool.not_false, ↓reduceIte]
      rw [List.map_cons, cnf_vars_cons, hcons2, List.count_append, List.count_append]
      have hle_c : ((dedupClause c).map Prod.fst).count v ≤ (c.map Prod.fst).count v :=
        ((dedupClause_sublist c).map Prod.fst).count_le v
      omega
    · simp only [List.filter_cons, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hcons2, List.count_append]
      omega

/-- Six gadget clauses over `PadVar` for `(clauseIdx, slot)`. -/
def padGadgetBlock (clauseIdx slot : ℕ) : CNF PadVar :=
  forcedFalseGadget (fun r : Fin 6 ↦ Sum.inr (clauseIdx, (slot, r.1)))

private lemma padGadgetBlock_eval_false_of_true (i s : ℕ) (τ : PadVar → Bool)
    (hz : τ (Sum.inr (i, (s, 0))) = true) : (padGadgetBlock i s).eval τ = false :=
  forcedFalseGadget_eval_false_of_true (fun r : Fin 6 ↦ Sum.inr (i, (s, r.1))) τ hz

/-- Pad a single cleaned non-empty clause `c` of length `≤ 3` at position `clauseIdx` to exact
width `3` over `PadVar`. -/
def padClauseAt (c : Clause ℕ) (clauseIdx : ℕ) : CNF PadVar :=
  match c with
  | [l₁] =>
      [(Sum.inl l₁.1, l₁.2),
       (Sum.inr (clauseIdx, (0, 0)), true),
       (Sum.inr (clauseIdx, (1, 0)), true)] ::
      (padGadgetBlock clauseIdx 0 ++ padGadgetBlock clauseIdx 1)
  | [l₁, l₂] =>
      [(Sum.inl l₁.1, l₁.2), (Sum.inl l₂.1, l₂.2),
       (Sum.inr (clauseIdx, (0, 0)), true)] ::
      padGadgetBlock clauseIdx 0
  | l₁ :: l₂ :: l₃ :: _ =>
      [[(Sum.inl l₁.1, l₁.2), (Sum.inl l₂.1, l₂.2), (Sum.inl l₃.1, l₃.2)]]
  | [] => []

/-- Syntactic guard for `ThreeSATThree` inputs. -/
def guardThreeSATThree (φ : CNF ℕ) : Bool :=
  (φ.all fun c ↦ decide (c.length ≤ 3)) &&
    (φ.vars.all fun v ↦ decide (φ.vars.count v ≤ 3))

/-- Total polynomial-time reduction from `ThreeSATThree` to `BalancedThreeFourSAT` (and hence
`ThreeFourSAT`). Inputs outside the width-`3`, occurrence-`3` syntactic promise, or whose cleaned
formula contains the empty clause, map to `unsatThreeFourCNF`. -/
def toThreeFourSAT (φ : CNF ℕ) : CNF ℕ :=
  if guardThreeSATThree φ then
    let ψ := cleanCNF φ
    if ψ.any List.isEmpty then
      unsatThreeFourCNF
    else
      CNF.relabel padVarCodec (ψ.zipIdx.flatMap fun p ↦ padClauseAt p.1 p.2)
  else
    unsatThreeFourCNF

/-! ### Polynomial-time computability of `toThreeFourSAT` -/

private def mkInlLit (l : Literal ℕ) : Literal PadVar :=
  (Sum.inl l.1, l.2)

@[fun_prop]
private lemma computableInPolyTime_mkInlLit :
    ComputableInPolyTime mkInlLit (encPair encNat encBool) (encPair encPadVar encBool) := by
  unfold mkInlLit encPadVar
  fun_prop

private def mkInrLit (i s r : ℕ) (b : Bool) : Literal PadVar :=
  (Sum.inr (i, (s, r)), b)

@[fun_prop]
private lemma computableInPolyTime_mkInrLit (r : ℕ) (b : Bool) :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ mkInrLit p.1 p.2 r b)
      (encPair encUnary encUnary) (encPair encPadVar encBool) := by
  unfold mkInrLit encPadVar
  fun_prop

private def mkClause3 (a b c : Literal PadVar) : Clause PadVar :=
  [a, b, c]

@[fun_prop]
private lemma computableInPolyTime_mkClause3 :
    ComputableInPolyTime (fun t : Literal PadVar × (Literal PadVar × Literal PadVar) ↦
        mkClause3 t.1 t.2.1 t.2.2)
      (encPair (encPair encPadVar encBool)
        (encPair (encPair encPadVar encBool) (encPair encPadVar encBool)))
      (encClause encPadVar) := by
  unfold mkClause3
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_padGadgetBlock :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ padGadgetBlock p.1 p.2)
      (encPair encUnary encUnary) (encCNFOver encPadVar) := by
  have heq : (fun p : ℕ × ℕ ↦ padGadgetBlock p.1 p.2) = fun p ↦
      ([mkClause3 (mkInrLit p.1 p.2 0 false) (mkInrLit p.1 p.2 1 true) (mkInrLit p.1 p.2 2 true),
        mkClause3 (mkInrLit p.1 p.2 0 false) (mkInrLit p.1 p.2 1 true) (mkInrLit p.1 p.2 2 false),
        mkClause3 (mkInrLit p.1 p.2 0 false) (mkInrLit p.1 p.2 1 false)
          (mkInrLit p.1 p.2 3 true)] ++
       [mkClause3 (mkInrLit p.1 p.2 3 false) (mkInrLit p.1 p.2 4 true) (mkInrLit p.1 p.2 5 true),
        mkClause3 (mkInrLit p.1 p.2 3 false) (mkInrLit p.1 p.2 4 true) (mkInrLit p.1 p.2 5 false),
        mkClause3 (mkInrLit p.1 p.2 1 false) (mkInrLit p.1 p.2 3 false)
          (mkInrLit p.1 p.2 4 false)]) := by
    funext p
    rfl
  rw [heq]
  fun_prop

private def litAt0 (c : Clause ℕ) : Literal PadVar :=
  mkInlLit (c.headD (0, false))

private def litAt1 (c : Clause ℕ) : Literal PadVar :=
  mkInlLit (c.tail.headD (0, false))

private def litAt2 (c : Clause ℕ) : Literal PadVar :=
  mkInlLit (c.tail.tail.headD (0, false))

@[fun_prop]
private lemma computableInPolyTime_litAt0 :
    ComputableInPolyTime litAt0 (encClause encNat) (encPair encPadVar encBool) := by
  unfold litAt0
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_litAt1 :
    ComputableInPolyTime litAt1 (encClause encNat) (encPair encPadVar encBool) := by
  unfold litAt1
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_litAt2 :
    ComputableInPolyTime litAt2 (encClause encNat) (encPair encPadVar encBool) := by
  unfold litAt2
  fun_prop

private def padLen1 (c : Clause ℕ) (i : ℕ) : CNF PadVar :=
  mkClause3 (litAt0 c) (mkInrLit i 0 0 true) (mkInrLit i 1 0 true) ::
    (padGadgetBlock i 0 ++ padGadgetBlock i 1)

private def padLen2 (c : Clause ℕ) (i : ℕ) : CNF PadVar :=
  mkClause3 (litAt0 c) (litAt1 c) (mkInrLit i 0 0 true) ::
    padGadgetBlock i 0

private def padLen3 (c : Clause ℕ) : CNF PadVar :=
  [mkClause3 (litAt0 c) (litAt1 c) (litAt2 c)]

@[fun_prop]
private lemma computableInPolyTime_padLen1 :
    ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ padLen1 p.1 p.2)
      (encPair (encClause encNat) encUnary) (encCNFOver encPadVar) := by
  unfold padLen1
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_padLen2 :
    ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ padLen2 p.1 p.2)
      (encPair (encClause encNat) encUnary) (encCNFOver encPadVar) := by
  unfold padLen2
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_padLen3 :
    ComputableInPolyTime padLen3 (encClause encNat) (encCNFOver encPadVar) := by
  unfold padLen3
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_padClauseAt :
    ComputableInPolyTime (fun p : Clause ℕ × ℕ ↦ padClauseAt p.1 p.2)
      (encPair (encClause encNat) encUnary) (encCNFOver encPadVar) := by
  have heq : (fun p : Clause ℕ × ℕ ↦ padClauseAt p.1 p.2) = fun p ↦
      if decide (p.1.length = 1) then padLen1 p.1 p.2
      else if decide (p.1.length = 2) then padLen2 p.1 p.2
      else if decide (3 ≤ p.1.length) then padLen3 p.1
      else [] := by
    funext ⟨c, i⟩
    rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, rest⟩⟩⟩ <;>
      simp [padClauseAt, padLen1, padLen2, padLen3, litAt0, litAt1, litAt2, mkInlLit,
        mkClause3, mkInrLit]
  rw [heq]
  fun_prop

@[fun_prop]
private lemma computableInPolyTime_guardThreeSATThree :
    ComputableInPolyTime guardThreeSATThree encCNF encBool := by
  unfold guardThreeSATThree
  fun_prop

private def padCleanedCNF (ψ : CNF ℕ) : CNF ℕ :=
  if ψ.any List.isEmpty then
    unsatThreeFourCNF
  else
    CNF.relabel padVarCodec (ψ.zipIdx.flatMap fun p ↦ padClauseAt p.1 p.2)

@[fun_prop]
private lemma computableInPolyTime_padCleanedCNF :
    ComputableInPolyTime padCleanedCNF encCNF encCNF := by
  have hrel : ComputableInPolyTime
      (fun ψ : CNF ℕ ↦ CNF.relabel padVarCodec (ψ.zipIdx.flatMap fun p ↦ padClauseAt p.1 p.2))
      encCNF encCNF := by
    have hflat : ComputableInPolyTime
        (fun ψ : CNF ℕ ↦ ψ.zipIdx.flatMap fun p ↦ padClauseAt p.1 p.2)
        encCNF (encCNFOver encPadVar) := by
      fun_prop
    exact (CNF.computableInPolyTime_relabel computableInPolyTime_padVarCodec).comp hflat
  unfold padCleanedCNF
  fun_prop

@[fun_prop]
theorem computableInPolyTime_toThreeFourSAT :
    ComputableInPolyTime toThreeFourSAT encCNF encCNF := by
  have heq : toThreeFourSAT = fun φ : CNF ℕ ↦
      if guardThreeSATThree φ then padCleanedCNF (cleanCNF φ) else unsatThreeFourCNF := by
    rfl
  rw [heq]
  fun_prop

/-! ### Syntactic and semantic correctness of `toThreeFourSAT` -/

private lemma count_flatten_relabel_of_injective {V W : Type*}
    [BEq V] [LawfulBEq V] [BEq W] [LawfulBEq W]
    {f : V → W} (hf : Function.Injective f) (Φ : CNF V) (x : V) (b : Bool) :
    (CNF.relabel f Φ).flatten.count (f x, b) = Φ.flatten.count (x, b) := by
  have hfl : (CNF.relabel f Φ).flatten = Φ.flatten.map (Prod.map f id) := by
    rw [CNF.relabel]
    unfold Clause.relabel
    rw [← List.map_flatten]
  rw [hfl]
  have hinj : Function.Injective (Prod.map f (id : Bool → Bool)) := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (hf h1) h2
  exact List.count_map_of_injective Φ.flatten _ hinj (x, b)

private lemma padGadgetBlock_eq_relabel (i s : ℕ) :
    padGadgetBlock i s =
      CNF.relabel (fun x : Fin 6 ↦ (Sum.inr (i, (s, x.1)) : PadVar))
        (forcedFalseGadget (id : Fin 6 → Fin 6)) := by
  rfl

private lemma mem_flatten_padGadgetBlock {i s : ℕ} {l : Literal PadVar}
    (hl : l ∈ (padGadgetBlock i s).flatten) :
    ∃ r : Fin 6, l.1 = Sum.inr (i, (s, r.1)) := by
  rw [padGadgetBlock_eq_relabel, CNF.relabel] at hl
  obtain ⟨cl, hcl, hmem⟩ := List.mem_flatten.mp hl
  obtain ⟨c₀, _, rfl⟩ := List.mem_map.mp hcl
  obtain ⟨⟨r, b⟩, _, rfl⟩ := List.mem_map.mp hmem
  exact ⟨r, rfl⟩

private lemma padGadgetBlock_clauses_good (i s : ℕ) :
    ∀ c ∈ padGadgetBlock i s, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  intro c hc
  simp only [padGadgetBlock, forcedFalseGadget, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private lemma padClauseAt_clauses_good {c : Clause ℕ} {i : ℕ}
    (hlen : 1 ≤ c.length ∧ c.length ≤ 3) (hnd : (c.map Prod.fst).Nodup) :
    ∀ d ∈ padClauseAt c i, d.length = 3 ∧ (d.map Prod.fst).Nodup := by
  rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, _ | _⟩⟩⟩
  · simp at hlen
  · intro d hd
    simp only [padClauseAt, List.mem_cons, List.mem_append] at hd
    rcases hd with rfl | h0 | h1
    · simp
    · exact padGadgetBlock_clauses_good i 0 d h0
    · exact padGadgetBlock_clauses_good i 1 d h1
  · intro d hd
    have hne12 : l₁.1 ≠ l₂.1 := by simpa using hnd
    simp only [padClauseAt, List.mem_cons] at hd
    rcases hd with rfl | h0
    · simp [hne12]
    · exact padGadgetBlock_clauses_good i 0 d h0
  · intro d hd
    simp only [padClauseAt, List.mem_singleton] at hd
    subst hd
    refine ⟨rfl, ?_⟩
    have hmap :
        ([(Sum.inl l₁.1, l₁.2), (Sum.inl l₂.1, l₂.2), (Sum.inl l₃.1, l₃.2)] :
            Clause PadVar).map Prod.fst =
          ([l₁, l₂, l₃].map Prod.fst).map Sum.inl := rfl
    rw [hmap]
    exact hnd.map Sum.inl_injective
  · simp only [List.length_cons] at hlen
    omega

private lemma count_padGadgetBlock_inl (i s v : ℕ) (b : Bool) :
    (padGadgetBlock i s).flatten.count (Sum.inl v, b) = 0 := by
  apply List.count_eq_zero.mpr
  intro h
  obtain ⟨r, hr⟩ := mem_flatten_padGadgetBlock h
  cases hr

private lemma count_padGadgetBlock_inr_other {i s i' s' r : ℕ} (hne : (i', s') ≠ (i, s))
    (b : Bool) :
    (padGadgetBlock i s).flatten.count (Sum.inr (i', (s', r)), b) = 0 := by
  apply List.count_eq_zero.mpr
  intro h
  obtain ⟨x, hx⟩ := mem_flatten_padGadgetBlock h
  have h1 := Prod.mk.inj (Sum.inr.inj hx)
  have h2 := Prod.mk.inj h1.2
  exact hne (Prod.ext h1.1 h2.1)

private lemma count_padGadgetBlock_inr_ge6 {i s r : ℕ} (hr : 6 ≤ r) (b : Bool) :
    (padGadgetBlock i s).flatten.count (Sum.inr (i, (s, r)), b) = 0 := by
  apply List.count_eq_zero.mpr
  intro h
  obtain ⟨x, hx⟩ := mem_flatten_padGadgetBlock h
  obtain ⟨_, hs_eq⟩ := Prod.mk.inj (Sum.inr.inj hx)
  obtain ⟨_, hr_eq⟩ := Prod.mk.inj hs_eq
  omega

private lemma count_padGadgetBlock_inr_lt6 (i s : ℕ) {r : ℕ} (hr : r < 6) (b : Bool) :
    (padGadgetBlock i s).flatten.count (Sum.inr (i, (s, r)), b) =
      (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (⟨r, hr⟩, b) := by
  rw [padGadgetBlock_eq_relabel]
  have hinj : Function.Injective (fun x : Fin 6 ↦ (Sum.inr (i, (s, x.1)) : PadVar)) := by
    intro x y h
    obtain ⟨_, hs_eq⟩ := Prod.mk.inj (Sum.inr.inj h)
    exact Fin.ext (Prod.mk.inj hs_eq).2
  exact count_flatten_relabel_of_injective hinj _ ⟨r, hr⟩ b

private lemma count_padClauseAt_inl (c : Clause ℕ) (i : ℕ)
    (hlen : 1 ≤ c.length ∧ c.length ≤ 3) (v : ℕ) (b : Bool) :
    (padClauseAt c i).flatten.count (Sum.inl v, b) = c.count (v, b) := by
  rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, _ | _⟩⟩⟩
  · simp at hlen
  · simp only [padClauseAt, List.flatten_cons, List.flatten_append, List.count_cons,
      List.count_append, count_padGadgetBlock_inl, List.count_nil]
    have h0 : ((Sum.inr (i, (0, 0)) : PadVar), true) ≠ (Sum.inl v, b) := by simp
    have h1 : ((Sum.inr (i, (1, 0)) : PadVar), true) ≠ (Sum.inl v, b) := by simp
    rcases l₁ with ⟨w₁, b₁⟩
    by_cases hw : w₁ = v <;> by_cases hb : b₁ = b <;> simp [hw, hb, h0, h1]
  · simp only [padClauseAt, List.flatten_cons, List.count_cons, List.count_append,
      count_padGadgetBlock_inl, List.count_nil]
    have h0 : ((Sum.inr (i, (0, 0)) : PadVar), true) ≠ (Sum.inl v, b) := by simp
    rcases l₁ with ⟨w₁, b₁⟩
    rcases l₂ with ⟨w₂, b₂⟩
    by_cases hw1 : w₁ = v <;> by_cases hb1 : b₁ = b <;>
      by_cases hw2 : w₂ = v <;> by_cases hb2 : b₂ = b <;>
      simp [hw1, hb1, hw2, hb2, h0]
  · simp only [padClauseAt, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.count_cons, List.count_nil]
    rcases l₁ with ⟨w₁, b₁⟩
    rcases l₂ with ⟨w₂, b₂⟩
    rcases l₃ with ⟨w₃, b₃⟩
    by_cases hw1 : w₁ = v <;> by_cases hb1 : b₁ = b <;>
      by_cases hw2 : w₂ = v <;> by_cases hb2 : b₂ = b <;>
      by_cases hw3 : w₃ = v <;> by_cases hb3 : b₃ = b <;>
      simp [hw1, hb1, hw2, hb2, hw3, hb3]
  · simp only [List.length_cons] at hlen
    omega

private lemma count_padClauseAt_inr_diff {c : Clause ℕ} {i i' s r : ℕ} (hi : i' ≠ i) (b : Bool) :
    (padClauseAt c i).flatten.count (Sum.inr (i', (s, r)), b) = 0 := by
  have hne0 : (i', s) ≠ (i, 0) := fun h ↦ hi (Prod.mk.inj h).1
  have hne1 : (i', s) ≠ (i, 1) := fun h ↦ hi (Prod.mk.inj h).1
  apply List.count_eq_zero.mpr
  intro hmem
  rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, rest⟩⟩⟩
  · simp [padClauseAt] at hmem
  · simp only [padClauseAt, List.flatten_cons, List.flatten_append, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (heq | heq | heq) | h0 | h1
    · cases (Prod.mk.inj heq).1
    · exact hi (Prod.mk.inj (Sum.inr.inj (Prod.mk.inj heq).1)).1
    · exact hi (Prod.mk.inj (Sum.inr.inj (Prod.mk.inj heq).1)).1
    · exact List.count_eq_zero.mp (count_padGadgetBlock_inr_other hne0 b) h0
    · exact List.count_eq_zero.mp (count_padGadgetBlock_inr_other hne1 b) h1
  · simp only [padClauseAt, List.flatten_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with (heq | heq | heq) | h0
    · cases (Prod.mk.inj heq).1
    · cases (Prod.mk.inj heq).1
    · exact hi (Prod.mk.inj (Sum.inr.inj (Prod.mk.inj heq).1)).1
    · exact List.count_eq_zero.mp (count_padGadgetBlock_inr_other hne0 b) h0
  · simp only [padClauseAt, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with heq | heq | heq <;> cases (Prod.mk.inj heq).1

private lemma count_padClauseAt_inr_same (c : Clause ℕ) (i s r : ℕ) :
    (padClauseAt c i).flatten.count (Sum.inr (i, (s, r)), true) ≤ 2 ∧
      (padClauseAt c i).flatten.count (Sum.inr (i, (s, r)), false) ≤ 3 ∧
      (padClauseAt c i).flatten.count (Sum.inr (i, (s, r)), true) +
        (padClauseAt c i).flatten.count (Sum.inr (i, (s, r)), false) ≤ 4 := by
  by_cases hr6 : 6 ≤ r
  · have hne0 : ((Sum.inr (i, (0, 0)) : PadVar), true) ≠ (Sum.inr (i, (s, r)), true) := by
      intro h
      have := (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj (Prod.mk.inj h).1)).2).2
      omega
    have hne1 : ((Sum.inr (i, (1, 0)) : PadVar), true) ≠ (Sum.inr (i, (s, r)), true) := by
      intro h
      have := (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj (Prod.mk.inj h).1)).2).2
      omega
    have hg0 (b : Bool) :
        (padGadgetBlock i 0).flatten.count (Sum.inr (i, (s, r)), b) = 0 := by
      by_cases hs : s = 0
      · subst hs; exact count_padGadgetBlock_inr_ge6 hr6 b
      · exact count_padGadgetBlock_inr_other (by simp [hs]) b
    have hg1 (b : Bool) :
        (padGadgetBlock i 1).flatten.count (Sum.inr (i, (s, r)), b) = 0 := by
      by_cases hs : s = 1
      · subst hs; exact count_padGadgetBlock_inr_ge6 hr6 b
      · exact count_padGadgetBlock_inr_other (by simp [hs]) b
    rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, rest⟩⟩⟩ <;>
      simp [padClauseAt, List.flatten_cons, List.flatten_append, List.count_append,
        hg0, hg1, hne0, hne1]
  · have hr_lt : r < 6 := Nat.lt_of_not_ge hr6
    obtain ⟨ht_le, hf_le, hsum_le, hr0_eq⟩ := count_forcedFalseGadget_id ⟨r, hr_lt⟩
    rcases c with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, rest⟩⟩⟩
    · simp [padClauseAt]
    · simp only [padClauseAt, List.flatten_cons, List.flatten_append, List.cons_append,
        List.nil_append, List.count_cons, List.count_append]
      by_cases hs0 : s = 0
      · subst hs0
        have hne1 (b : Bool) :
            (padGadgetBlock i 1).flatten.count (Sum.inr (i, (0, r)), b) = 0 :=
          count_padGadgetBlock_inr_other (by simp) b
        rw [hne1 true, hne1 false, count_padGadgetBlock_inr_lt6 i 0 hr_lt true,
          count_padGadgetBlock_inr_lt6 i 0 hr_lt false]
        by_cases hr0 : r = 0
        · subst hr0
          obtain ⟨ht0, hf0⟩ := hr0_eq rfl
          change (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (0, true) = 0 at ht0
          change (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (0, false) = 3 at hf0
          simp [ht0, hf0]
        · have hr0' : 0 ≠ r := Ne.symm hr0
          simp [beq_iff_eq, hr0', ht_le, hf_le, hsum_le]
      · by_cases hs1 : s = 1
        · subst hs1
          have hne0 (b : Bool) :
              (padGadgetBlock i 0).flatten.count (Sum.inr (i, (1, r)), b) = 0 :=
            count_padGadgetBlock_inr_other (by simp) b
          rw [hne0 true, hne0 false, count_padGadgetBlock_inr_lt6 i 1 hr_lt true,
            count_padGadgetBlock_inr_lt6 i 1 hr_lt false]
          by_cases hr0 : r = 0
          · subst hr0
            obtain ⟨ht0, hf0⟩ := hr0_eq rfl
            change (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (0, true) = 0 at ht0
            change (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (0, false) = 3 at hf0
            simp [ht0, hf0]
          · have hr0' : 0 ≠ r := Ne.symm hr0
            simp [beq_iff_eq, hr0', ht_le, hf_le, hsum_le]
        · have hne0 (b : Bool) :
              (padGadgetBlock i 0).flatten.count (Sum.inr (i, (s, r)), b) = 0 :=
            count_padGadgetBlock_inr_other (by simp [hs0]) b
          have hne1 (b : Bool) :
              (padGadgetBlock i 1).flatten.count (Sum.inr (i, (s, r)), b) = 0 :=
            count_padGadgetBlock_inr_other (by simp [hs1]) b
          have hs0' : 0 ≠ s := Ne.symm hs0
          have hs1' : 1 ≠ s := Ne.symm hs1
          simp [beq_iff_eq, hne0, hne1, hs0', hs1']
    · simp only [padClauseAt, List.flatten_cons, List.cons_append, List.nil_append,
        List.count_cons]
      by_cases hs0 : s = 0
      · subst hs0
        rw [count_padGadgetBlock_inr_lt6 i 0 hr_lt true,
          count_padGadgetBlock_inr_lt6 i 0 hr_lt false]
        by_cases hr0 : r = 0
        · subst hr0
          obtain ⟨ht0, hf0⟩ := hr0_eq rfl
          change (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (0, true) = 0 at ht0
          change (forcedFalseGadget (id : Fin 6 → Fin 6)).flatten.count (0, false) = 3 at hf0
          simp [ht0, hf0]
        · have hr0' : 0 ≠ r := Ne.symm hr0
          simp [beq_iff_eq, hr0', ht_le, hf_le, hsum_le]
      · have hne0 (b : Bool) :
            (padGadgetBlock i 0).flatten.count (Sum.inr (i, (s, r)), b) = 0 :=
          count_padGadgetBlock_inr_other (by simp [hs0]) b
        have hs0' : 0 ≠ s := Ne.symm hs0
        simp [beq_iff_eq, hne0, hs0']
    · simp [padClauseAt]

private lemma eval_padClauseAt_iff {c : Clause ℕ} {i : ℕ}
    (hlen : 1 ≤ c.length ∧ c.length ≤ 3) (τ : PadVar → Bool) :
    (padClauseAt c i).eval τ = true ↔
      c.eval (τ ∘ Sum.inl) = true ∧
      (c.length = 1 → (padGadgetBlock i 0).eval τ = true ∧ (padGadgetBlock i 1).eval τ = true) ∧
      (c.length = 2 → (padGadgetBlock i 0).eval τ = true) := by
  rcases c with _ | ⟨⟨v₁, b₁⟩, _ | ⟨⟨v₂, b₂⟩, _ | ⟨⟨v₃, b₃⟩, _ | _⟩⟩⟩
  · simp at hlen
  · simp only [padClauseAt, CNF.eval_cons, CNF.eval_append, Bool.and_eq_true]
    constructor
    · rintro ⟨hcl, hg0, hg1⟩
      have hz0 : τ (Sum.inr (i, (0, 0))) = false := by
        cases h : τ (Sum.inr (i, (0, 0)))
        · rfl
        · rw [padGadgetBlock_eval_false_of_true i 0 τ h] at hg0
          cases hg0
      have hz1 : τ (Sum.inr (i, (1, 0))) = false := by
        cases h : τ (Sum.inr (i, (1, 0)))
        · rfl
        · rw [padGadgetBlock_eval_false_of_true i 1 τ h] at hg1
          cases hg1
      simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Function.comp_apply,
        hz0, hz1] at hcl ⊢
      exact ⟨hcl, fun _ ↦ ⟨hg0, hg1⟩, (fun h ↦ nomatch h)⟩
    · rintro ⟨hcl, h1, _⟩
      obtain ⟨hg0, hg1⟩ := h1 rfl
      simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Function.comp_apply,
        Bool.or_false] at hcl ⊢
      exact ⟨by simp [hcl], hg0, hg1⟩
  · simp only [padClauseAt, CNF.eval_cons, Bool.and_eq_true]
    constructor
    · rintro ⟨hcl, hg0⟩
      have hz0 : τ (Sum.inr (i, (0, 0))) = false := by
        cases h : τ (Sum.inr (i, (0, 0)))
        · rfl
        · rw [padGadgetBlock_eval_false_of_true i 0 τ h] at hg0
          cases hg0
      simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Function.comp_apply,
        hz0] at hcl ⊢
      exact ⟨hcl, (fun h ↦ nomatch h), fun _ ↦ hg0⟩
    · rintro ⟨hcl, _, h2⟩
      have hg0 := h2 rfl
      simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Function.comp_apply,
        Bool.or_false, Bool.or_eq_true] at hcl ⊢
      rcases hcl with ha | hb
      · exact ⟨Or.inl ha, hg0⟩
      · exact ⟨Or.inr (Or.inl hb), hg0⟩
  · simp [padClauseAt]
  · simp only [List.length_cons] at hlen
    omega

private lemma vars_count_eq_add_polarities (Φ : CNF ℕ) (w : ℕ) :
    Φ.vars.count w = Φ.flatten.count (w, true) + Φ.flatten.count (w, false) := by
  unfold CNF.vars
  induction Φ.flatten with
  | nil => simp
  | cons l rest ih =>
    rcases l with ⟨v, b⟩
    simp only [List.map_cons, List.count_cons]
    by_cases hv : v = w <;> cases b <;> simp [hv] <;> omega

/-- Every output of `toThreeFourSAT` satisfies `IsBalancedThreeFourCNF` (and hence
`IsThreeFourCNF`). -/
theorem toThreeFourSAT_isBalanced (φ : CNF ℕ) :
    IsBalancedThreeFourCNF (toThreeFourSAT φ) := by
  unfold toThreeFourSAT
  by_cases hguard : guardThreeSATThree φ = true
  · simp only [hguard, ↓reduceIte]
    by_cases hempty : (cleanCNF φ).any List.isEmpty = true
    · simp only [hempty, ↓reduceIte]
      exact unsatThreeFourCNF_isBalanced
    · simp only [Bool.eq_false_iff.mpr hempty, Bool.false_eq_true, ↓reduceIte]
      let ψ := cleanCNF φ
      have hguard' : (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v ∈ φ.vars, φ.vars.count v ≤ 3) := by
        simpa [guardThreeSATThree, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq] using hguard
      have hψ_nonempty : ∀ c ∈ ψ, 1 ≤ c.length ∧ c.length ≤ 3 := by
        intro c hc
        have hne : c.isEmpty = false := by
          by_contra htr
          have : ψ.any List.isEmpty = true :=
            List.any_eq_true.mpr ⟨c, hc, Bool.eq_true_of_not_eq_false htr⟩
          exact hempty this
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        have hd_len : (dedupClause d).length ≤ 3 :=
          le_trans (dedupClause_sublist d).length_le (hguard'.1 d (List.mem_of_mem_filter hd))
        have hd_pos : 1 ≤ (dedupClause d).length := by
          cases hdd : dedupClause d with
          | nil => simp [hdd] at hne
          | cons _ _ => simp
        exact ⟨hd_pos, hd_len⟩
      have hψ_nd : ∀ c ∈ ψ, (c.map Prod.fst).Nodup := by
        intro c hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        have hnt : isTautClause d = false := by
          have := (List.mem_filter.mp hd).2
          simpa using this
        exact nodup_fst_dedupClause_of_not_isTautClause hnt
      let Φ : CNF PadVar := ψ.zipIdx.flatMap fun p ↦ padClauseAt p.1 p.2
      have hclauses :
          ∀ c ∈ CNF.relabel padVarCodec Φ, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
        intro c hc
        obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
        obtain ⟨⟨d, idx⟩, hmem, hc₀_mem⟩ := List.mem_flatMap.mp hc₀
        have hd_in : d ∈ ψ := List.fst_mem_of_mem_zipIdx hmem
        obtain ⟨hlen3, hnd₀⟩ :=
          padClauseAt_clauses_good (hψ_nonempty d hd_in) (hψ_nd d hd_in) c₀ hc₀_mem
        refine ⟨by simpa [Clause.relabel] using hlen3, ?_⟩
        have hmap : (c₀.relabel padVarCodec).map Prod.fst =
            (c₀.map Prod.fst).map padVarCodec := by
          simp [Clause.relabel, List.map_map, Function.comp_def]
        rw [hmap]
        exact hnd₀.map padVarCodec_injective
      have hcounts : ∀ w : ℕ,
          ((CNF.relabel padVarCodec Φ).flatten.count (w, true) ≤ 3 ∧
            (CNF.relabel padVarCodec Φ).flatten.count (w, false) ≤ 3) ∧
          (CNF.relabel padVarCodec Φ).vars.count w ≤ 4 := by
        intro w
        rw [vars_count_eq_add_polarities]
        cases hdec : padVarCodec.decode? w with
        | none =>
          have hnot_mem : ∀ b : Bool, (w, b) ∉ (CNF.relabel padVarCodec Φ).flatten := by
            rintro b hmem
            obtain ⟨cl, hcl, hl⟩ := List.mem_flatten.mp hmem
            obtain ⟨c₀, _, rfl⟩ := List.mem_map.mp hcl
            obtain ⟨⟨x, b'⟩, _, heq⟩ := List.mem_map.mp hl
            obtain ⟨hw_eq, _⟩ := Prod.mk.inj heq
            have : padVarCodec.decode? w = some x := hw_eq ▸ padVarCodec.decode?_apply x
            rw [hdec] at this
            cases this
          have ht0 : (CNF.relabel padVarCodec Φ).flatten.count (w, true) = 0 :=
            List.count_eq_zero.mpr (hnot_mem true)
          have hf0 : (CNF.relabel padVarCodec Φ).flatten.count (w, false) = 0 :=
            List.count_eq_zero.mpr (hnot_mem false)
          omega
        | some x =>
          have hx_eq : padVarCodec x = w := padVarCodec.encode_of_decode? hdec
          subst hx_eq
          rw [count_flatten_relabel_of_injective padVarCodec_injective Φ x true,
            count_flatten_relabel_of_injective padVarCodec_injective Φ x false]
          rcases x with v | ⟨i', s, r⟩
          · have hfl_eq : ∀ (L : List (Clause ℕ)) (k : ℕ) (b : Bool),
                (∀ d ∈ L, 1 ≤ d.length ∧ d.length ≤ 3) →
                ((L.zipIdx k).flatMap fun p ↦ padClauseAt p.1 p.2).flatten.count (Sum.inl v, b) =
                  L.flatten.count (v, b) := by
              intro L
              induction L with
              | nil => intro _ _ _; simp
              | cons d ds ih =>
                intro k b hL
                simp only [List.zipIdx_cons, List.flatMap_cons, List.flatten_append,
                  List.count_append, List.flatten_cons]
                rw [count_padClauseAt_inl d k (hL d List.mem_cons_self),
                  ih (k + 1) b (fun d' hd' ↦ hL d' (List.mem_cons_of_mem d hd'))]
            have hsum_t : Φ.flatten.count (Sum.inl v, true) = ψ.flatten.count (v, true) :=
              hfl_eq ψ 0 true hψ_nonempty
            have hsum_f : Φ.flatten.count (Sum.inl v, false) = ψ.flatten.count (v, false) :=
              hfl_eq ψ 0 false hψ_nonempty
            rw [hsum_t, hsum_f]
            have hv_le : (cleanCNF φ).vars.count v ≤ 3 := by
              have h1 := count_vars_cleanCNF_le φ v
              by_cases hvin : v ∈ φ.vars
              · have h2 := hguard'.2 v hvin
                omega
              · have h2 : φ.vars.count v = 0 := List.count_eq_zero.mpr hvin
                omega
            have hsplit := vars_count_eq_add_polarities (cleanCNF φ) v
            dsimp only [ψ] at hsplit ⊢
            omega
          · have hsingle : ∀ (L : List (Clause ℕ)) (k : ℕ),
                ((L.zipIdx k).flatMap fun p ↦ padClauseAt p.1 p.2).flatten.count
                    (Sum.inr (i', (s, r)), true) ≤ 2 ∧
                ((L.zipIdx k).flatMap fun p ↦ padClauseAt p.1 p.2).flatten.count
                    (Sum.inr (i', (s, r)), false) ≤ 3 ∧
                ((L.zipIdx k).flatMap fun p ↦ padClauseAt p.1 p.2).flatten.count
                    (Sum.inr (i', (s, r)), true) +
                  ((L.zipIdx k).flatMap fun p ↦ padClauseAt p.1 p.2).flatten.count
                    (Sum.inr (i', (s, r)), false) ≤ 4 := by
              intro L
              induction L with
              | nil => intro _; simp
              | cons d ds ih =>
                intro k
                simp only [List.zipIdx_cons, List.flatMap_cons, List.flatten_append,
                  List.count_append]
                by_cases hik : i' = k
                · subst hik
                  have hzero_rest (b : Bool) :
                      ((ds.zipIdx (i' + 1)).flatMap fun p ↦ padClauseAt p.1 p.2).flatten.count
                        (Sum.inr (i', (s, r)), b) = 0 := by
                    apply List.count_eq_zero.mpr
                    intro hmem
                    simp only [List.mem_flatten, List.mem_flatMap] at hmem
                    rcases hmem with ⟨cl, ⟨p, hp, hcl⟩, hl⟩
                    have hge : i' + 1 ≤ p.2 := (List.mem_zipIdx hp).1
                    have hne : i' ≠ p.2 := by omega
                    have hc0 := count_padClauseAt_inr_diff (c := p.1) (s := s) (r := r) hne b
                    exact List.count_eq_zero.mp hc0 (List.mem_flatten.mpr ⟨cl, hcl, hl⟩)
                  rw [hzero_rest true, hzero_rest false, Nat.add_zero, Nat.add_zero]
                  exact count_padClauseAt_inr_same d i' s r
                · rw [count_padClauseAt_inr_diff hik true, count_padClauseAt_inr_diff hik false,
                    Nat.zero_add, Nat.zero_add]
                  exact ih (k + 1)
            obtain ⟨ht_le, hf_le, htot_le⟩ := hsingle ψ 0
            exact ⟨⟨Nat.le_trans ht_le (by decide), hf_le⟩, htot_le⟩
      exact ⟨⟨hclauses, fun w ↦ (hcounts w).2⟩,
        fun w b ↦ match b with | false => (hcounts w).1.2 | true => (hcounts w).1.1⟩
  · simp only [Bool.eq_false_iff.mpr hguard, Bool.false_eq_true, ↓reduceIte]
    exact unsatThreeFourCNF_isBalanced

/-- Exact membership preservation of `toThreeFourSAT` from `ThreeSATThree` into
`BalancedThreeFourSAT`. -/
theorem toThreeFourSAT_mem_balancedThreeFourSAT_iff (φ : CNF ℕ) :
    toThreeFourSAT φ ∈ BalancedThreeFourSAT ↔ φ ∈ ThreeSATThree := by
  have hbal := toThreeFourSAT_isBalanced φ
  have hlhs : (toThreeFourSAT φ ∈ BalancedThreeFourSAT) ↔ (toThreeFourSAT φ).Satisfiable :=
    ⟨fun h ↦ h.2, fun hs ↦ ⟨hbal, hs⟩⟩
  rw [hlhs]
  unfold toThreeFourSAT
  by_cases hguard : guardThreeSATThree φ = true
  · simp only [hguard, ↓reduceIte]
    have hguard' : (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v, φ.vars.count v ≤ 3) := by
      have hg : (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v ∈ φ.vars, φ.vars.count v ≤ 3) := by
        simpa [guardThreeSATThree, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq] using hguard
      refine ⟨hg.1, fun v ↦ ?_⟩
      by_cases hv : v ∈ φ.vars
      · exact hg.2 v hv
      · simp [List.count_eq_zero.mpr hv]
    have hrhs : φ ∈ ThreeSATThree ↔ φ.Satisfiable :=
      ⟨fun h ↦ h.2.2, fun hs ↦ ⟨hguard'.1, hguard'.2, hs⟩⟩
    rw [hrhs]
    by_cases hempty : (cleanCNF φ).any List.isEmpty = true
    · simp only [hempty, ↓reduceIte, not_satisfiable_unsatThreeFourCNF, false_iff]
      rw [← satisfiable_cleanCNF_iff]
      simp only [List.any_eq_true, List.isEmpty_iff] at hempty
      rcases hempty with ⟨c, hc, rfl⟩
      rintro ⟨σ, hσ⟩
      have := (CNF.eval_eq_true_iff σ _).mp hσ [] hc
      simp at this
    · simp only [Bool.eq_false_iff.mpr hempty, Bool.false_eq_true, ↓reduceIte]
      rw [CNF.satisfiable_relabel padVarCodec_injective, ← satisfiable_cleanCNF_iff]
      let ψ := cleanCNF φ
      have hψ_nonempty : ∀ c ∈ ψ, 1 ≤ c.length ∧ c.length ≤ 3 := by
        intro c hc
        have hne : c.isEmpty = false := by
          by_contra htr
          have : ψ.any List.isEmpty = true :=
            List.any_eq_true.mpr ⟨c, hc, Bool.eq_true_of_not_eq_false htr⟩
          exact hempty this
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        have hd_len : (dedupClause d).length ≤ 3 :=
          le_trans (dedupClause_sublist d).length_le (hguard'.1 d (List.mem_of_mem_filter hd))
        have hd_pos : 1 ≤ (dedupClause d).length := by
          cases hdd : dedupClause d with
          | nil => simp [hdd] at hne
          | cons _ _ => simp
        exact ⟨hd_pos, hd_len⟩
      constructor
      · rintro ⟨τ, hτ⟩
        refine ⟨τ ∘ Sum.inl, (CNF.eval_eq_true_iff _ ψ).mpr fun c hc ↦ ?_⟩
        obtain ⟨idx, hidx_lt, hget⟩ := List.mem_iff_getElem.mp hc
        have hp_mem : (c, idx) ∈ ψ.zipIdx := by
          rw [List.mem_iff_getElem]
          exact ⟨idx, by simp [hidx_lt], by simp [hget]⟩
        have hblk := (CNF.eval_flatMap_eq_true_iff τ ψ.zipIdx _).mp hτ (c, idx) hp_mem
        exact ((eval_padClauseAt_iff (hψ_nonempty c hc) τ).mp hblk).1
      · rintro ⟨σ, hσ⟩
        refine ⟨Sum.elim σ (fun _ ↦ false),
          (CNF.eval_flatMap_eq_true_iff _ ψ.zipIdx _).mpr fun p hp ↦ ?_⟩
        have hc : p.1 ∈ ψ := List.fst_mem_of_mem_zipIdx hp
        rw [eval_padClauseAt_iff (hψ_nonempty p.1 hc)]
        refine ⟨(CNF.eval_eq_true_iff σ ψ).mp hσ p.1 hc, fun _ ↦ ⟨?_, ?_⟩, fun _ ↦ ?_⟩
        · exact forcedFalseGadget_eval_true_of_all_false _ _ fun _ ↦ rfl
        · exact forcedFalseGadget_eval_true_of_all_false _ _ fun _ ↦ rfl
        · exact forcedFalseGadget_eval_true_of_all_false _ _ fun _ ↦ rfl
  · simp only [Bool.eq_false_iff.mpr hguard, Bool.false_eq_true, ↓reduceIte,
      not_satisfiable_unsatThreeFourCNF, false_iff]
    rintro ⟨h1, h2, _⟩
    apply hguard
    simp only [guardThreeSATThree, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨h1, fun v _ ↦ h2 v⟩

theorem toThreeFourSAT_mem_threeFourSAT_iff (φ : CNF ℕ) :
    toThreeFourSAT φ ∈ ThreeFourSAT ↔ φ ∈ ThreeSATThree := by
  have hbal := toThreeFourSAT_isBalanced φ
  have hiff := toThreeFourSAT_mem_balancedThreeFourSAT_iff φ
  change (IsThreeFourCNF (toThreeFourSAT φ) ∧ (toThreeFourSAT φ).Satisfiable) ↔
    φ ∈ ThreeSATThree
  change (IsBalancedThreeFourCNF (toThreeFourSAT φ) ∧ (toThreeFourSAT φ).Satisfiable) ↔
    φ ∈ ThreeSATThree at hiff
  simpa [hbal, hbal.1] using hiff

/-- `ThreeSATThree` reduces to `BalancedThreeFourSAT` in polynomial time. -/
theorem polyTimeReducible_threeSATThree_balancedThreeFourSAT :
    PolyTimeReducible encCNF encCNF ThreeSATThree BalancedThreeFourSAT :=
  ⟨toThreeFourSAT, computableInPolyTime_toThreeFourSAT,
    fun φ ↦ (toThreeFourSAT_mem_balancedThreeFourSAT_iff φ).symm⟩

/-- `ThreeSATThree` reduces to `ThreeFourSAT` in polynomial time. -/
theorem polyTimeReducible_threeSATThree_threeFourSAT :
    PolyTimeReducible encCNF encCNF ThreeSATThree ThreeFourSAT :=
  ⟨toThreeFourSAT, computableInPolyTime_toThreeFourSAT,
    fun φ ↦ (toThreeFourSAT_mem_threeFourSAT_iff φ).symm⟩

/-- Polarity-balanced `(3, 4)`-SAT is `NP`-hard. -/
theorem balancedThreeFourSAT_npHard : NPHard encCNF BalancedThreeFourSAT :=
  ThreeSATThree_npHard.trans polyTimeReducible_threeSATThree_balancedThreeFourSAT

/-- Polarity-balanced `(3, 4)`-SAT is `NP`-complete. -/
theorem balancedThreeFourSAT_npComplete : NPComplete encCNF BalancedThreeFourSAT :=
  ⟨balancedThreeFourSAT_mem_NP, balancedThreeFourSAT_npHard⟩

/-- Tovey's `(3, 4)`-SAT is `NP`-hard. -/
theorem threeFourSAT_npHard : NPHard encCNF ThreeFourSAT :=
  ThreeSATThree_npHard.trans polyTimeReducible_threeSATThree_threeFourSAT

/-- **Tovey's `(3, 4)`-SAT is `NP`-complete**. -/
theorem threeFourSAT_npComplete : NPComplete encCNF ThreeFourSAT :=
  ⟨threeFourSAT_mem_NP, threeFourSAT_npHard⟩

end Cslib.Complexity
