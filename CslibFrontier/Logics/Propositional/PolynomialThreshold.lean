/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Protocol
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Polynomial-Threshold Proof Systems `Th(k)` and NOF Clause-Search Reductions

This module formalizes degree-`deg` polynomial-threshold inequalities (`PolyThresholdIneq`) over
`{0, 1}^n`, binary bit-size, semantic entailment, exact clause translation on `Cslib.Logic.PL.CNF`,
DAG and tree-like `Th(deg)` refutations and their soundness, the pigeonhole NOF cylinder
decomposition of degree-`r` threshold inequalities, and a constructive binary-tree centroid-search
protocol reducing any tree-like `Th(r)` refutation to a deterministic `(r + 1)`-party NOF protocol
for the CNF clause-search problem.

## Main definitions

* `PolyThresholdIneq`, `PolyThresholdIneq.eval`, `PolyThresholdIneq.bitSize`,
  `PolyThresholdIneq.weightSum`, `SemanticallyEntails`, `clauseToPolyThreshold`: syntax, semantics,
  and bit/weight measures for `Th(deg)` inequalities.
* `ThDerivation`, `ThTreeDerivation`: DAG and tree-like semantic `Th(deg)` derivations.

## Main results

* `clauseToPolyThreshold_eval_iff`: exact semantic equivalence between clauses and degree-1
  threshold inequalities.
* `ThDerivation.unsatisfiable`, `thTreeDerivation_unsatisfiable`: soundness of DAG and tree-like
  `Th(deg)` refutations.
* `subset_misses_player_of_card_le`, `polyThreshold_lhsVal_eq_sum_nof_cylinders`: pigeonhole NOF
  cylinder decomposition of degree-`r` polynomial-threshold inequalities.
* `exists_nof_search_of_thTreeRefutation`: constructive deterministic `(r + 1)`-party NOF
  clause-search protocol from a tree-like `Th(r)` refutation with depth
  `O(r · log L · log W)`.
-/

public section

open scoped BigOperators
open Cslib Cslib.BitString Cslib.Communication.NOF Cslib.Logic.PL

namespace CslibFrontier.Logics.Propositional.PolynomialThreshold

section ThProofSystem

/-- Binary bit-length of an integer. -/
def intBitSize (z : ℤ) : ℕ :=
  Nat.log 2 z.natAbs + 1

/-- Degree-`deg` polynomial-threshold inequality `∑_{|S| ≤ deg} γ_S ∏_{i ∈ S} x_i ≥ threshold`
over `{0, 1}^n`. -/
structure PolyThresholdIneq (n deg : ℕ) where
  /-- Integer coefficients indexed by monomials `S ⊆ Fin n`. -/
  coeff : Finset (Fin n) → ℤ
  /-- Integer threshold on the right-hand side. -/
  threshold : ℤ

/-- Left-hand side evaluation `∑_{|S| ≤ deg} γ_S ∏_{i ∈ S} [x_i = true]`. -/
def PolyThresholdIneq.lhsVal {n deg : ℕ} (L : PolyThresholdIneq n deg) (x : BitString n) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦ S.card ≤ deg),
    L.coeff S * (if ∀ i ∈ S, x i = true then 1 else 0)

/-- Satisfaction `L.threshold ≤ L.lhsVal x` on `{0, 1}` assignment `x`. -/
def PolyThresholdIneq.eval {n deg : ℕ} (L : PolyThresholdIneq n deg) (x : BitString n) : Prop :=
  L.threshold ≤ L.lhsVal x

/-- Sum of binary sizes of all nonzero coefficients and the threshold. -/
def PolyThresholdIneq.bitSize {n deg : ℕ} (L : PolyThresholdIneq n deg) : ℕ :=
  intBitSize L.threshold +
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S ↦ S.card ≤ deg ∧ L.coeff S ≠ 0),
      intBitSize (L.coeff S)

/-- Total `ℓ₁` weight `∑_{|S| ≤ deg} |γ_S|` of a polynomial-threshold inequality. -/
def PolyThresholdIneq.weightSum {n deg : ℕ} (L : PolyThresholdIneq n deg) : ℕ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦ S.card ≤ deg),
    (L.coeff S).natAbs

/-- The contradiction inequality `0 ≥ 1`. -/
def contradictionIneq (n deg : ℕ) : PolyThresholdIneq n deg where
  coeff := fun _ ↦ 0
  threshold := 1

/-- No `{0, 1}` assignment satisfies the contradiction inequality `0 ≥ 1`. -/
theorem not_contradictionIneq_eval {n deg : ℕ} (x : BitString n) :
    ¬ (contradictionIneq n deg).eval x := by
  unfold PolyThresholdIneq.eval PolyThresholdIneq.lhsVal contradictionIneq
  simp

/-- Semantic entailment `L₁, L₂ ⊨ G` over `{0, 1}^n`. -/
def SemanticallyEntails {n deg : ℕ} (L₁ L₂ G : PolyThresholdIneq n deg) : Prop :=
  ∀ x : BitString n, L₁.eval x → L₂.eval x → G.eval x

/-- Translate a `Cslib.Logic.PL.Clause (Fin n)` into an equivalent degree-1 threshold inequality. -/
def clauseToPolyThreshold {n deg : ℕ} (C : Clause (Fin n)) : PolyThresholdIneq n deg where
  coeff := fun S ↦
    (C.map fun l : Literal (Fin n) ↦
      if l.2 then
        if S = {l.1} then (1 : ℤ) else 0
      else
        if S = ∅ then (1 : ℤ) else if S = {l.1} then (-1 : ℤ) else 0).sum
  threshold := 1

/-- Exact semantic equivalence between a clause `C` and `clauseToPolyThreshold C` when `1 ≤ deg`. -/
theorem clauseToPolyThreshold_eval_iff {n deg : ℕ} (hdeg : 1 ≤ deg)
    (C : Clause (Fin n)) (x : BitString n) :
    (clauseToPolyThreshold (deg := deg) C).eval x ↔ C.eval x = true := by
  let subSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦ S.card ≤ deg)
  have hempty_mem : (∅ : Finset (Fin n)) ∈ subSets := by simp [subSets]
  have hsing_mem : ∀ v : Fin n, ({v} : Finset (Fin n)) ∈ subSets := fun v ↦ by
    simp [subSets, hdeg]
  have hlit_val : ∀ l : Literal (Fin n),
      (∑ S ∈ subSets,
        (if l.2 then
          if S = {l.1} then (1 : ℤ) else 0
        else
          if S = ∅ then (1 : ℤ) else if S = {l.1} then (-1 : ℤ) else 0) *
          (if ∀ i ∈ S, x i = true then 1 else 0)) =
        if Literal.eval x l = true then 1 else 0 := by
    intro ⟨v, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hne_es : ({v} : Finset (Fin n)) ≠ ∅ := Finset.singleton_ne_empty v
      have hsum_split : (∑ S ∈ subSets,
          (if S = ∅ then (1 : ℤ) else if S = {v} then (-1 : ℤ) else 0) *
            (if ∀ i ∈ S, x i = true then 1 else 0)) =
          1 + (-1 : ℤ) * (if x v = true then 1 else 0) := by
        have hterm : ∀ S ∈ subSets,
            (if S = ∅ then (1 : ℤ) else if S = {v} then (-1 : ℤ) else 0) *
              (if ∀ i ∈ S, x i = true then 1 else 0) =
            (if S = ∅ then (1 : ℤ) else 0) +
              (if S = {v} then (-1 : ℤ) * (if x v = true then 1 else 0) else 0) := by
          intro S _
          by_cases h0 : S = ∅
          · subst h0; simp [hne_es.symm]
          · by_cases hv : S = {v}
            · subst hv; simp [hne_es]
            · simp [h0, hv]
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
          Finset.sum_ite_eq' subSets ∅, Finset.sum_ite_eq' subSets {v}]
        simp [hempty_mem, hsing_mem]
      rw [hsum_split, Literal.eval_mk]
      cases x v <;> simp
    · simp only [↓reduceIte]
      have hterm : ∀ S ∈ subSets,
          (if S = {v} then (1 : ℤ) else 0) * (if ∀ i ∈ S, x i = true then 1 else 0) =
            if S = {v} then (if x v = true then 1 else 0) else 0 := by
        intro S _
        by_cases hv : S = {v}
        · subst hv; simp
        · simp [hv]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' subSets {v},
        ite_eq_left (hsing_mem v), Literal.eval_mk]
      cases x v <;> simp
  have hlist_sum : ∀ L : List (Literal (Fin n)),
      (∑ S ∈ subSets,
        (L.map fun l : Literal (Fin n) ↦
          if l.2 then
            if S = {l.1} then (1 : ℤ) else 0
          else
            if S = ∅ then (1 : ℤ) else if S = {l.1} then (-1 : ℤ) else 0).sum *
          (if ∀ i ∈ S, x i = true then 1 else 0)) =
        (L.map fun l ↦ if Literal.eval x l = true then (1 : ℤ) else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [hlit_val hd, ih]
  unfold PolyThresholdIneq.eval PolyThresholdIneq.lhsVal clauseToPolyThreshold Clause.eval
  change 1 ≤ ∑ S ∈ subSets, _ ↔ C.any (Literal.eval x) = true
  rw [hlist_sum C]
  induction C with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.any_cons, Bool.or_eq_true]
    have hnn : 0 ≤ (tl.map fun l ↦ if Literal.eval x l = true then (1 : ℤ) else 0).sum :=
      List.sum_nonneg fun v hv ↦ by
        rcases List.mem_map.mp hv with ⟨l, _, rfl⟩
        split_ifs <;> omega
    cases hhd : Literal.eval x hd
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, false_or]
      exact ih
    · simp only [↓reduceIte, true_or, iff_true]
      omega

/-- **General (DAG) `Th(deg)` refutation**:
a nonempty sequence of degree-`deg` threshold inequalities where each line is either a clause axiom
or semantically entailed by two earlier lines, ending in `0 ≥ 1`. -/
structure ThDerivation {n deg : ℕ} (φ : CNF (Fin n)) where
  /-- Number of lines in the refutation (`t + 1`). -/
  len : ℕ
  /-- The sequence of `len + 1` threshold inequalities. -/
  lines : Fin (len + 1) → PolyThresholdIneq n deg
  /-- Each line is either a clause axiom of `φ` or semantically entailed by two earlier lines. -/
  valid : ∀ j : Fin (len + 1),
    (∃ C ∈ φ, lines j = clauseToPolyThreshold C) ∨
    (∃ i₁ i₂ : Fin (len + 1), i₁.val < j.val ∧ i₂.val < j.val ∧
      SemanticallyEntails (lines i₁) (lines i₂) (lines j))
  /-- The final line is the contradiction `0 ≥ 1`. -/
  concl : lines (Fin.last len) = contradictionIneq n deg

/-- Bit-size of a DAG `Th(deg)` refutation. -/
def ThDerivation.bitSize {n deg : ℕ} {φ : CNF (Fin n)} (P : ThDerivation (deg := deg) φ) : ℕ :=
  ∑ j : Fin (P.len + 1), (P.lines j).bitSize

/-- Soundness of DAG `Th(deg)` refutations (`1 ≤ deg`). -/
theorem ThDerivation.unsatisfiable {n deg : ℕ} (hdeg : 1 ≤ deg) {φ : CNF (Fin n)}
    (P : ThDerivation (deg := deg) φ) : ¬ φ.Satisfiable := by
  rintro ⟨x, hx⟩
  have hall : ∀ m : ℕ, ∀ h : m < P.len + 1, (P.lines ⟨m, h⟩).eval x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm
      rcases P.valid ⟨m, hm⟩ with ⟨C, hC, heq⟩ | ⟨i₁, i₂, hi₁, hi₂, hent⟩
      · rw [heq, clauseToPolyThreshold_eval_iff hdeg]
        exact (CNF.eval_eq_true_iff x φ).mp hx C hC
      · exact hent x (ih i₁.val hi₁ i₁.isLt) (ih i₂.val hi₂ i₂.isLt)
  have hlast := hall P.len (Nat.lt_succ_self P.len)
  have heq_last : (⟨P.len, Nat.lt_succ_self P.len⟩ : Fin (P.len + 1)) = Fin.last P.len := rfl
  rw [heq_last, P.concl] at hlast
  exact not_contradictionIneq_eval x hlast

/-- **Tree-like `Th(deg)` semantic derivation**. -/
inductive ThTreeDerivation {n deg : ℕ} (φ : CNF (Fin n)) : PolyThresholdIneq n deg → Type
  /-- Axiom leaf corresponding to a clause `C ∈ φ`. -/
  | axiomClause (C : Clause (Fin n)) (hmem : C ∈ φ) :
      ThTreeDerivation φ (clauseToPolyThreshold C)
  /-- Binary semantic entailment cut rule `L₁, L₂ ⊨ G`. -/
  | cut {L₁ L₂ G : PolyThresholdIneq n deg}
      (d₁ : ThTreeDerivation φ L₁) (d₂ : ThTreeDerivation φ L₂)
      (hentails : SemanticallyEntails L₁ L₂ G) :
      ThTreeDerivation φ G

/-- Leaf count of a tree-like `Th(deg)` derivation. -/
def ThTreeDerivation.leafCount {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → ThTreeDerivation φ G → ℕ
  | _, .axiomClause _ _ => 1
  | _, .cut d₁ d₂ _ => d₁.leafCount + d₂.leafCount

/-- Node count (tree size) of a tree-like `Th(deg)` derivation. -/
def ThTreeDerivation.treeSize {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → ThTreeDerivation φ G → ℕ
  | _, .axiomClause _ _ => 1
  | _, .cut d₁ d₂ _ => 1 + d₁.treeSize + d₂.treeSize

/-- Total binary bit-size of a tree-like `Th(deg)` derivation. -/
def ThTreeDerivation.bitSize {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → ThTreeDerivation φ G → ℕ
  | _, .axiomClause C _ => (clauseToPolyThreshold (deg := deg) C).bitSize
  | G, .cut d₁ d₂ _ => G.bitSize + d₁.bitSize + d₂.bitSize

/-- Maximum `ℓ₁` coefficient weight over all inequalities appearing in a tree-like derivation. -/
def ThTreeDerivation.maxWeight {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → ThTreeDerivation φ G → ℕ
  | _, .axiomClause C _ => (clauseToPolyThreshold (deg := deg) C).weightSum
  | G, .cut d₁ d₂ _ => max G.weightSum (max d₁.maxWeight d₂.maxWeight)

/-- Every inequality derived in a tree-like `Th(deg)` derivation (`1 ≤ deg`) holds on every
satisfying assignment of `φ`. -/
theorem ThTreeDerivation.sound_on_satisfying {n deg : ℕ} (hdeg : 1 ≤ deg)
    {φ : CNF (Fin n)} {G : PolyThresholdIneq n deg}
    (D : ThTreeDerivation φ G) {x : BitString n} (hx : φ.eval x = true) :
    G.eval x := by
  induction D with
  | axiomClause C hmem =>
    rw [clauseToPolyThreshold_eval_iff hdeg]
    exact (CNF.eval_eq_true_iff x φ).mp hx C hmem
  | cut _ _ hentails ih₁ ih₂ =>
    exact hentails x ih₁ ih₂

/-- **Soundness of tree-like `Th(deg)` refutations**:
if `φ` admits a tree-like `Th(deg)` refutation (`1 ≤ deg`), then `φ` is unsatisfiable. -/
theorem thTreeDerivation_unsatisfiable {n deg : ℕ} (hdeg : 1 ≤ deg) {φ : CNF (Fin n)}
    (D : ThTreeDerivation φ (contradictionIneq n deg)) : ¬ φ.Satisfiable := by
  rintro ⟨x, hx⟩
  exact not_contradictionIneq_eval x (D.sound_on_satisfying hdeg hx)

end ThProofSystem

section NOFSearchFromThTree

/-- **Pigeonhole Player-Visibility Lemma**: under any partition `part: Fin n → Fin (r + 1)`, every
variable subset `S ⊆ Fin n` of size `≤ r` misses at least one player `p: Fin (r + 1)`. -/
theorem subset_misses_player_of_card_le {n r : ℕ}
    (part : Fin n → Fin (r + 1)) {S : Finset (Fin n)} (hS : S.card ≤ r) :
    ∃ p : Fin (r + 1), ∀ v ∈ S, part v ≠ p := by
  have hcard_lt : (S.image part).card < (Finset.univ : Finset (Fin (r + 1))).card := by
    calc (S.image part).card ≤ S.card := Finset.card_image_le
      _ ≤ r := hS
      _ < r + 1 := Nat.lt_succ_self r
      _ = (Finset.univ : Finset (Fin (r + 1))).card := by simp
  obtain ⟨p, _, hp_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  exact ⟨p, fun v hv heq ↦ hp_not (Finset.mem_image.mpr ⟨v, hv, heq⟩)⟩

/-- Combine player-distributed assignments under `part: Fin n → Fin k` into a single `BitString n`.
-/
def joinPartition {n k : ℕ} (part : Fin n → Fin k) (x : Fin k → BitString n) : BitString n :=
  fun v ↦ x (part v) v

/-- Triangle inequality for `Int.natAbs` over finite sums. -/
private theorem natAbs_sum_le {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ a ∈ s, f a).natAbs ≤ ∑ a ∈ s, (f a).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- **NOF Cylinder Decomposition of `Th(r)` Inequalities**:
every degree-`r` `PolyThresholdIneq n r` evaluates `lhsVal (joinPartition part x)` as a sum of
`(r + 1)`-party integer shares where player `p`'s share depends only on `view p x`, with total
magnitude bounded by `L.weightSum`. -/
theorem polyThreshold_lhsVal_eq_sum_nof_cylinders {n r : ℕ}
    (L : PolyThresholdIneq n r) (part : Fin n → Fin (r + 1)) :
    ∃ share : ∀ p : Fin (r + 1), View (fun _ : Fin (r + 1) ↦ BitString n) p → ℤ,
      (∀ p x, (share p (view p x)).natAbs ≤ L.weightSum) ∧
      ∀ x : Fin (r + 1) → BitString n,
        L.lhsVal (joinPartition part x) = ∑ p : Fin (r + 1), share p (view p x) := by
  classical
  let subSets := (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦ S.card ≤ r)
  let owner : ∀ S ∈ subSets, Fin (r + 1) := fun S hS ↦
    Classical.choose (subset_misses_player_of_card_le part (Finset.mem_filter.mp hS).2)
  have howner_misses : ∀ (S : Finset (Fin n)) (hS : S ∈ subSets),
      ∀ v ∈ S, part v ≠ owner S hS := fun S hS ↦
    Classical.choose_spec (subset_misses_player_of_card_le part (Finset.mem_filter.mp hS).2)
  let share : ∀ p : Fin (r + 1), View (fun _ : Fin (r + 1) ↦ BitString n) p → ℤ := fun p v ↦
    ∑ S ∈ subSets.attach,
      if hop : owner S.1 S.2 = p then
        L.coeff S.1 * (if ∀ i : {i // i ∈ S.1},
          v ⟨part i.1, hop ▸ howner_misses S.1 S.2 i.1 i.2⟩ i.1 = true then 1 else 0)
      else 0
  refine ⟨share, ?_, ?_⟩
  · intro p x
    have hle : (share p (view p x)).natAbs ≤
        ∑ S ∈ subSets.attach, (L.coeff S.1).natAbs := by
      let term : {S // S ∈ subSets} → ℤ := fun S ↦
        if hop : owner S.1 S.2 = p then
          L.coeff S.1 * (if ∀ i : {i // i ∈ S.1},
            view p x ⟨part i.1, hop ▸ howner_misses S.1 S.2 i.1 i.2⟩ i.1 = true
          then 1 else 0)
        else 0
      change (∑ S ∈ subSets.attach, term S).natAbs ≤ _
      calc (∑ S ∈ subSets.attach, term S).natAbs
          ≤ ∑ S ∈ subSets.attach, (term S).natAbs := natAbs_sum_le subSets.attach term
        _ ≤ ∑ S ∈ subSets.attach, (L.coeff S.1).natAbs := by
            refine Finset.sum_le_sum fun S _ ↦ ?_
            dsimp only [term]
            split_ifs <;> simp
    refine hle.trans (le_of_eq ?_)
    exact Finset.sum_attach subSets (fun S ↦ (L.coeff S).natAbs)
  · intro x
    unfold share
    rw [Finset.sum_comm]
    have hterm : ∀ S : {S // S ∈ subSets},
        (∑ p : Fin (r + 1),
          if hop : owner S.1 S.2 = p then
            L.coeff S.1 * (if ∀ i : {i // i ∈ S.1},
              view p x ⟨part i.1, hop ▸ howner_misses S.1 S.2 i.1 i.2⟩ i.1 = true
            then 1 else 0)
          else 0) =
        L.coeff S.1 * (if ∀ i ∈ S.1, joinPartition part x i = true then 1 else 0) := by
      intro S
      rw [Finset.sum_eq_single (owner S.1 S.2)]
      · simp only [↓reduceDIte, view_apply]
        congr 2
        exact propext ⟨fun h i hi ↦ h ⟨i, hi⟩, fun h ⟨i, hi⟩ ↦ h i hi⟩
      · intro p _ hne
        rw [dite_eq_right (Ne.symm hne)]
      · intro h; exact (h (Finset.mem_univ _)).elim
    simp_rw [hterm]
    unfold PolyThresholdIneq.lhsVal
    exact (Finset.sum_attach subSets _).symm

/-- Encode a natural number `< 2 ^ B` into a `BitString B` (little-endian). -/
private def natToBits (B k : ℕ) : BitString B :=
  fun j ↦ decide ((k / 2 ^ j.val) % 2 = 1)

/-- Decode a `BitString B` back to a natural number. -/
private def bitsToNat {B : ℕ} (s : BitString B) : ℕ :=
  ∑ j : Fin B, if s j then 2 ^ j.val else 0

private theorem bitsToNat_natToBits (B : ℕ) {k : ℕ} (hk : k < 2 ^ B) :
    bitsToNat (natToBits B k) = k := by
  induction B generalizing k with
  | zero => simp [bitsToNat]; omega
  | succ B ih =>
    unfold bitsToNat natToBits
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, decide_eq_true_eq]
    have hdiv : k / 2 < 2 ^ B := by rw [pow_succ'] at hk; omega
    have hih := ih hdiv
    unfold bitsToNat natToBits at hih
    simp only [decide_eq_true_eq] at hih
    have htail : ∑ j : Fin B, (if (k / 2 ^ (j.val + 1)) % 2 = 1 then 2 ^ (j.val + 1) else 0) =
        2 * ∑ j : Fin B, (if ((k / 2) / 2 ^ j.val) % 2 = 1 then 2 ^ j.val else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      split_ifs <;> ring
    rw [htail, hih]
    have hmod : (if k % 2 = 1 then 1 else 0) = k % 2 := by split_ifs <;> omega
    rw [hmod]
    omega

/-- Auxiliary sequential loop broadcasting `idx` players' encoded integer shares. -/
private def evalIneqLoop {n r : ℕ} (thresh : ℤ) (W B : ℕ)
    (enc : ∀ p : Fin (r + 1), View (fun _ : Fin (r + 1) ↦ BitString n) p → BitString B) :
    ℕ → ℤ → Protocol (fun _ : Fin (r + 1) ↦ BitString n) Bool
  | 0, acc => .output (decide (thresh ≤ acc))
  | idx + 1, acc =>
    if hlt : idx < r + 1 then
      let p : Fin (r + 1) := ⟨idx, hlt⟩
      Protocol.sendBits p B (enc p) fun bits ↦
        evalIneqLoop thresh W B enc idx (acc + ((bitsToNat bits : ℤ) - (W : ℤ)))
    else
      .output false

/-- Deterministic `(r + 1)`-party NOF protocol evaluating `L.eval (joinPartition part x)`
using `(r + 1) * (Nat.log 2 (2 * W + 1) + 1)` bits whenever `L.weightSum ≤ W`. -/
private noncomputable def evalIneqProtocol {n r : ℕ} (L : PolyThresholdIneq n r)
    (part : Fin n → Fin (r + 1)) (W : ℕ) :
    Protocol (fun _ : Fin (r + 1) ↦ BitString n) Bool :=
  let B : ℕ := Nat.log 2 (2 * W + 1) + 1
  let share := Classical.choose (polyThreshold_lhsVal_eq_sum_nof_cylinders L part)
  let enc : ∀ p : Fin (r + 1), View (fun _ : Fin (r + 1) ↦ BitString n) p → BitString B :=
    fun p v ↦ natToBits B ((share p v + (W : ℤ)).toNat)
  evalIneqLoop L.threshold W B enc (r + 1) 0

private theorem evalIneqProtocol_spec {n r : ℕ} (L : PolyThresholdIneq n r)
    (part : Fin n → Fin (r + 1)) (W : ℕ) (hW : L.weightSum ≤ W) :
    (evalIneqProtocol L part W).depth ≤ (r + 1) * (Nat.log 2 (2 * W + 1) + 1) ∧
    ∀ x : Fin (r + 1) → BitString n,
      (evalIneqProtocol L part W).run x = true ↔ L.eval (joinPartition part x) := by
  classical
  let B : ℕ := Nat.log 2 (2 * W + 1) + 1
  let hcyl := polyThreshold_lhsVal_eq_sum_nof_cylinders L part
  let share := Classical.choose hcyl
  have hspec := Classical.choose_spec hcyl
  let enc : ∀ p : Fin (r + 1), View (fun _ : Fin (r + 1) ↦ BitString n) p → BitString B :=
    fun p v ↦ natToBits B ((share p v + (W : ℤ)).toNat)
  have hdec : ∀ (p : Fin (r + 1)) (x : Fin (r + 1) → BitString n),
      (bitsToNat (enc p (view p x)) : ℤ) - (W : ℤ) = share p (view p x) := by
    intro p x
    have habs : (share p (view p x)).natAbs ≤ W := (hspec.1 p x).trans hW
    have hnn : 0 ≤ share p (view p x) + (W : ℤ) := by omega
    have hle : (share p (view p x) + (W : ℤ)).toNat ≤ 2 * W := by omega
    have hlt : (share p (view p x) + (W : ℤ)).toNat < 2 ^ B := by
      have hlog : 2 * W + 1 < 2 ^ B := Nat.lt_pow_succ_log_self (by omega) (2 * W + 1)
      omega
    dsimp only [enc]
    rw [bitsToNat_natToBits B hlt]
    omega
  have hloop_depth : ∀ (idx : ℕ) (acc : ℤ),
      (evalIneqLoop L.threshold W B enc idx acc).depth ≤ idx * B := by
    intro idx
    induction idx with
    | zero => intro acc; simp [evalIneqLoop]
    | succ idx ih =>
      intro acc
      unfold evalIneqLoop
      split_ifs with hlt
      · calc (Protocol.sendBits ⟨idx, hlt⟩ B (enc ⟨idx, hlt⟩) fun bits ↦
              evalIneqLoop L.threshold W B enc idx
                (acc + ((bitsToNat bits : ℤ) - (W : ℤ)))).depth
            ≤ B + idx * B := Protocol.depth_sendBits_le (fun bits ↦ ih _)
          _ = (idx + 1) * B := by ring
      · simp [Protocol.depth]
  have hloop_run : ∀ (idx : ℕ) (hidx : idx ≤ r + 1) (acc : ℤ)
      (x : Fin (r + 1) → BitString n),
      (evalIneqLoop L.threshold W B enc idx acc).run x =
        decide (L.threshold ≤ acc + ∑ j : Fin idx, share ⟨j.val, by omega⟩ (view _ x)) := by
    intro idx
    induction idx with
    | zero =>
      intro _ acc x
      simp [evalIneqLoop]
    | succ idx ih =>
      intro hidx acc x
      have hlt : idx < r + 1 := by omega
      unfold evalIneqLoop
      rw [dite_eq_left hlt, Protocol.run_sendBits, ih (by omega)]
      congr 1
      rw [Fin.sum_univ_castSucc, hdec ⟨idx, hlt⟩ x]
      simp only [Fin.val_castSucc, Fin.val_last]
      ring_nf
  refine ⟨hloop_depth (r + 1) 0, fun x ↦ ?_⟩
  unfold evalIneqProtocol
  rw [hloop_run (r + 1) le_rfl 0 x, zero_add, decide_eq_true_eq]
  have hsum : ∑ j : Fin (r + 1), share ⟨j.val, j.isLt⟩ (view ⟨j.val, j.isLt⟩ x) =
      L.lhsVal (joinPartition part x) := (hspec.2 x).symm
  rw [hsum]
  rfl

/-- Pruned tree-like `Th(deg)` derivation allowing `.assumed` leaves used during centroid search. -/
private inductive PrunedTree {n deg : ℕ} (φ : CNF (Fin n)) : PolyThresholdIneq n deg → Type
  | axiomClause (C : Clause (Fin n)) (hmem : C ∈ φ) : PrunedTree φ (clauseToPolyThreshold C)
  | assumed (H : PolyThresholdIneq n deg) : PrunedTree φ H
  | cut {L₁ L₂ G : PolyThresholdIneq n deg}
      (d₁ : PrunedTree φ L₁) (d₂ : PrunedTree φ L₂)
      (hentails : SemanticallyEntails L₁ L₂ G) : PrunedTree φ G

private def PrunedTree.leafCount {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → PrunedTree φ G → ℕ
  | _, .axiomClause _ _ => 1
  | _, .assumed _ => 1
  | _, .cut d₁ d₂ _ => d₁.leafCount + d₂.leafCount

private theorem PrunedTree.leafCount_pos {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → (T : PrunedTree φ G) → 1 ≤ T.leafCount
  | _, .axiomClause _ _ => le_rfl
  | _, .assumed _ => le_rfl
  | _, .cut d₁ d₂ _ => by
      have h1 := d₁.leafCount_pos; have h2 := d₂.leafCount_pos
      unfold PrunedTree.leafCount; omega

private def PrunedTree.AllAssumedTrue {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → PrunedTree φ G → BitString n → Prop
  | _, .axiomClause _ _, _ => True
  | H, .assumed _, x => H.eval x
  | _, .cut d₁ d₂ _, x => d₁.AllAssumedTrue x ∧ d₂.AllAssumedTrue x

private def PrunedTree.maxWeight {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → PrunedTree φ G → ℕ
  | _, .axiomClause C _ => (clauseToPolyThreshold (deg := deg) C).weightSum
  | G, .assumed _ => G.weightSum
  | G, .cut d₁ d₂ _ => max G.weightSum (max d₁.maxWeight d₂.maxWeight)

private theorem PrunedTree.rootWeight_le_maxWeight {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → (T : PrunedTree φ G) → G.weightSum ≤ T.maxWeight
  | _, .axiomClause _ _ => le_rfl
  | _, .assumed _ => le_rfl
  | _, .cut _ _ _ => le_max_left _ _

private def ThTreeDerivation.toPruned {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → ThTreeDerivation φ G → PrunedTree φ G
  | _, .axiomClause C hmem => .axiomClause C hmem
  | _, .cut d₁ d₂ hent => .cut d₁.toPruned d₂.toPruned hent

private theorem ThTreeDerivation.leafCount_toPruned {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → (D : ThTreeDerivation φ G) →
      D.toPruned.leafCount = D.leafCount
  | _, .axiomClause _ _ => rfl
  | _, .cut d₁ d₂ _ => by
      simp [ThTreeDerivation.toPruned, PrunedTree.leafCount, ThTreeDerivation.leafCount,
        d₁.leafCount_toPruned, d₂.leafCount_toPruned]

private theorem ThTreeDerivation.maxWeight_toPruned {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → (D : ThTreeDerivation φ G) →
      D.toPruned.maxWeight = D.maxWeight
  | _, .axiomClause _ _ => rfl
  | _, .cut d₁ d₂ _ => by
      simp [ThTreeDerivation.toPruned, PrunedTree.maxWeight, ThTreeDerivation.maxWeight,
        d₁.maxWeight_toPruned, d₂.maxWeight_toPruned]

private theorem ThTreeDerivation.allAssumedTrue_toPruned {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → (D : ThTreeDerivation φ G) → (x : BitString n) →
      D.toPruned.AllAssumedTrue x
  | _, .axiomClause _ _, _ => trivial
  | _, .cut d₁ d₂ _, x => ⟨d₁.allAssumedTrue_toPruned x, d₂.allAssumedTrue_toPruned x⟩

/-- **Binary-Tree Centroid Decomposition**: for any pruned tree `T` with `3 ≤ T.leafCount`,
extracts a subtree `S` deriving some `H` and a pruned copy `T'` of `T` (with `S` replaced by
`.assumed H`) such that both `S.leafCount - 1` and `T'.leafCount - 1` are at most
`(3 / 4) * (T.leafCount - 1)`. -/
private def findCentroid {n deg : ℕ} {φ : CNF (Fin n)} :
    {G : PolyThresholdIneq n deg} → (T : PrunedTree φ G) → (m : ℕ) →
      2 ≤ m → 2 * m < 3 * T.leafCount →
      Σ (H : PolyThresholdIneq n deg),
        {p : PrunedTree φ H × PrunedTree φ G //
          m + 1 ≤ 3 * p.1.leafCount ∧
          3 * p.1.leafCount ≤ 2 * m ∧
          p.2.leafCount + p.1.leafCount = T.leafCount + 1 ∧
          p.1.maxWeight ≤ T.maxWeight ∧
          p.2.maxWeight ≤ T.maxWeight ∧
          (∀ x, T.AllAssumedTrue x → p.1.AllAssumedTrue x) ∧
          (∀ x, T.AllAssumedTrue x → H.eval x → p.2.AllAssumedTrue x)}
  | _, .axiomClause _ _, m, hm2, hm => by
      exfalso; unfold PrunedTree.leafCount at hm; omega
  | _, .assumed _, m, hm2, hm => by
      exfalso; unfold PrunedTree.leafCount at hm; omega
  | _, .cut (L₁ := L₁) (L₂ := L₂) d₁ d₂ hent, m, hm2, hm =>
      if h1 : 2 * m < 3 * d₁.leafCount then
        let ⟨H, ⟨⟨S, d₁'⟩, hlo, hhi, hsz, hwS, hw1, htrS, htr1⟩⟩ := findCentroid d₁ m hm2 h1
        ⟨H, ⟨⟨S, .cut d₁' d₂ hent⟩, hlo, hhi,
          by simp only [PrunedTree.leafCount] at hsz ⊢; omega,
          hwS.trans (le_trans (le_max_left _ _) (le_max_right _ _)),
          by
            unfold PrunedTree.maxWeight
            exact max_le (le_max_left _ _) (max_le
              (hw1.trans (le_trans (le_max_left _ _) (le_max_right _ _)))
              (le_trans (le_max_right _ _) (le_max_right _ _))),
          fun x hx ↦ htrS x hx.1,
          fun x hx hH ↦ ⟨htr1 x hx.1 hH, hx.2⟩⟩⟩
      else if h2 : 2 * m < 3 * d₂.leafCount then
        let ⟨H, ⟨⟨S, d₂'⟩, hlo, hhi, hsz, hwS, hw2, htrS, htr2⟩⟩ := findCentroid d₂ m hm2 h2
        ⟨H, ⟨⟨S, .cut d₁ d₂' hent⟩, hlo, hhi,
          by simp only [PrunedTree.leafCount] at hsz ⊢; omega,
          hwS.trans (le_trans (le_max_right _ _) (le_max_right _ _)),
          by
            unfold PrunedTree.maxWeight
            exact max_le (le_max_left _ _) (max_le
              (le_trans (le_max_left _ _) (le_max_right _ _))
              (hw2.trans (le_trans (le_max_right _ _) (le_max_right _ _)))),
          fun x hx ↦ htrS x hx.2,
          fun x hx hH ↦ ⟨hx.1, htr2 x hx.2 hH⟩⟩⟩
      else if hge : d₂.leafCount ≤ d₁.leafCount then
        ⟨L₁, ⟨⟨d₁, .cut (.assumed L₁) d₂ hent⟩,
          by dsimp only; unfold PrunedTree.leafCount at hm; omega,
          by dsimp only; omega,
          by simp [PrunedTree.leafCount]; omega,
          by dsimp only; exact le_trans (le_max_left _ _) (le_max_right _ _),
          by
            dsimp only
            unfold PrunedTree.maxWeight
            exact max_le (le_max_left _ _) (max_le
              (d₁.rootWeight_le_maxWeight.trans (le_trans (le_max_left _ _) (le_max_right _ _)))
              (le_trans (le_max_right _ _) (le_max_right _ _))),
          fun _ hx ↦ hx.1,
          fun _ hx hH ↦ ⟨hH, hx.2⟩⟩⟩
      else
        ⟨L₂, ⟨⟨d₂, .cut d₁ (.assumed L₂) hent⟩,
          by dsimp only; unfold PrunedTree.leafCount at hm; omega,
          by dsimp only; omega,
          by simp [PrunedTree.leafCount]; omega,
          by dsimp only; exact le_trans (le_max_right _ _) (le_max_right _ _),
          by
            dsimp only
            unfold PrunedTree.maxWeight
            exact max_le (le_max_left _ _) (max_le
              (le_trans (le_max_left _ _) (le_max_right _ _))
              (d₂.rootWeight_le_maxWeight.trans (le_trans (le_max_right _ _) (le_max_right _ _)))),
          fun _ hx ↦ hx.2,
          fun _ hx hH ↦ ⟨hx.1, hH⟩⟩⟩

/-- Recursive centroid-search deterministic NOF protocol finding a falsified clause of `φ`. -/
private noncomputable def centroidSearchProtocol {n r : ℕ} {φ : CNF (Fin n)}
    (part : Fin n → Fin (r + 1)) (W : ℕ) :
    ℕ → {G : PolyThresholdIneq n r} → (T : PrunedTree φ G) →
      T.maxWeight ≤ W → Protocol (fun _ : Fin (r + 1) ↦ BitString n) (Clause (Fin n))
  | _, _, .axiomClause C _, _ => .output C
  | _, _, .assumed _, _ => .output []
  | 0, _, .cut _ _ _, _ => .output []
  | rounds + 1, _, .cut (L₁ := L₁) d₁ d₂ hent, hW =>
      let T := PrunedTree.cut d₁ d₂ hent
      if h3 : 3 ≤ T.leafCount then
        let ⟨H, ⟨⟨S, T'⟩, _, _, _, hwS, hwT', _, _⟩⟩ :=
          findCentroid T T.leafCount (by omega) (by omega)
        (evalIneqProtocol H part W).bind fun b ↦
          if b then
            centroidSearchProtocol part W rounds T' (hwT'.trans hW)
          else
            centroidSearchProtocol part W rounds S (hwS.trans hW)
      else
        (evalIneqProtocol L₁ part W).bind fun b ↦
          if b then
            centroidSearchProtocol part W rounds d₂
              ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hW)
          else
            centroidSearchProtocol part W rounds d₁
              ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hW)

private theorem centroidSearchProtocol_depth {n r : ℕ} {φ : CNF (Fin n)}
    (part : Fin n → Fin (r + 1)) (W : ℕ) :
    ∀ (rounds : ℕ) {G : PolyThresholdIneq n r} (T : PrunedTree φ G) (hW : T.maxWeight ≤ W),
      (centroidSearchProtocol part W rounds T hW).depth ≤
        rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1))
  | _, _, .axiomClause _ _, _ => by simp [centroidSearchProtocol]
  | _, _, .assumed _, _ => by simp [centroidSearchProtocol]
  | 0, _, .cut _ _ _, _ => by simp [centroidSearchProtocol]
  | rounds + 1, _, .cut (L₁ := L₁) d₁ d₂ hent, hW => by
      unfold centroidSearchProtocol
      dsimp only
      split_ifs with h3
      · generalize findCentroid (d₁.cut d₂ hent) (d₁.cut d₂ hent).leafCount
          (by omega) (by omega) = res
        rcases res with ⟨H, ⟨⟨S, T'⟩, _, _, _, hwS, hwT', _, _⟩⟩
        dsimp only at hwS hwT' ⊢
        have hH_le : H.weightSum ≤ W := S.rootWeight_le_maxWeight.trans (hwS.trans hW)
        have hev := (evalIneqProtocol_spec H part W hH_le).1
        have hcont : ∀ b : Bool,
            (if b then centroidSearchProtocol part W rounds T' (hwT'.trans hW)
             else centroidSearchProtocol part W rounds S (hwS.trans hW)).depth ≤
            rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := by
          intro b; cases b
          · exact centroidSearchProtocol_depth part W rounds S (hwS.trans hW)
          · exact centroidSearchProtocol_depth part W rounds T' (hwT'.trans hW)
        calc ((evalIneqProtocol H part W).bind _).depth
            ≤ (evalIneqProtocol H part W).depth +
                rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := Protocol.depth_bind_le hcont
          _ ≤ (r + 1) * (Nat.log 2 (2 * W + 1) + 1) +
                rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := Nat.add_le_add_right hev _
          _ = (rounds + 1) * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := by ring
      · have hL1_le : L₁.weightSum ≤ W :=
          d₁.rootWeight_le_maxWeight.trans
            ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hW)
        have hev := (evalIneqProtocol_spec L₁ part W hL1_le).1
        have hcont : ∀ b : Bool,
            (if b then centroidSearchProtocol part W rounds d₂
                ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hW)
             else centroidSearchProtocol part W rounds d₁
                ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hW)).depth ≤
            rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := by
          intro b; cases b
          · exact centroidSearchProtocol_depth part W rounds d₁ _
          · exact centroidSearchProtocol_depth part W rounds d₂ _
        calc ((evalIneqProtocol L₁ part W).bind _).depth
            ≤ (evalIneqProtocol L₁ part W).depth +
                rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := Protocol.depth_bind_le hcont
          _ ≤ (r + 1) * (Nat.log 2 (2 * W + 1) + 1) +
                rounds * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := Nat.add_le_add_right hev _
          _ = (rounds + 1) * ((r + 1) * (Nat.log 2 (2 * W + 1) + 1)) := by ring

private theorem centroidSearchProtocol_correct {n r : ℕ} (hr : 1 ≤ r) {φ : CNF (Fin n)}
    (part : Fin n → Fin (r + 1)) (W : ℕ) :
    ∀ (rounds : ℕ) {G : PolyThresholdIneq n r} (T : PrunedTree φ G) (hW : T.maxWeight ≤ W),
      3 ^ rounds * (T.leafCount - 1) < 4 ^ rounds →
      ∀ x : Fin (r + 1) → BitString n,
        T.AllAssumedTrue (joinPartition part x) →
        ¬ G.eval (joinPartition part x) →
        let C := (centroidSearchProtocol part W rounds T hW).run x
        C ∈ φ ∧ C.eval (joinPartition part x) = false
  | _, _, .axiomClause C hmem, _, _, x, _, hG => by
      simp only [centroidSearchProtocol, Protocol.run]
      refine ⟨hmem, ?_⟩
      cases hc : C.eval (joinPartition part x)
      · rfl
      · exact (hG ((clauseToPolyThreshold_eval_iff hr C (joinPartition part x)).mpr hc)).elim
  | _, _, .assumed _, _, _, x, hass, hG => (hG hass).elim
  | 0, _, .cut d₁ d₂ _, _, hsize, _, _, _ => by
      exfalso
      have h1 := d₁.leafCount_pos; have h2 := d₂.leafCount_pos
      unfold PrunedTree.leafCount at hsize
      simp at hsize; omega
  | rounds + 1, _, .cut (L₁ := L₁) d₁ d₂ hent, hW, hsize, x, hass, hG => by
      unfold centroidSearchProtocol
      dsimp only
      split_ifs with h3
      · rw [Protocol.run_bind]
        generalize findCentroid (d₁.cut d₂ hent) (d₁.cut d₂ hent).leafCount
          (by omega) (by omega) = res
        rcases res with ⟨H, ⟨⟨S, T'⟩, hlo, hhi, hsz, hwS, hwT', htrS, htrT'⟩⟩
        dsimp only at hlo hhi hsz hwS hwT' htrS htrT' ⊢
        have hS_shrink : 4 * (S.leafCount - 1) ≤ 3 * ((d₁.cut d₂ hent).leafCount - 1) := by omega
        have hT'_shrink : 4 * (T'.leafCount - 1) ≤ 3 * ((d₁.cut d₂ hent).leafCount - 1) := by
          have ha2 : 2 ≤ S.leafCount := by omega
          omega
        have hS_lt : 3 ^ rounds * (S.leafCount - 1) < 4 ^ rounds := by
          have hmul : 4 * (3 ^ rounds * (S.leafCount - 1)) < 4 * 4 ^ rounds := by
            calc 4 * (3 ^ rounds * (S.leafCount - 1))
                = 3 ^ rounds * (4 * (S.leafCount - 1)) := by ring
              _ ≤ 3 ^ rounds * (3 * ((d₁.cut d₂ hent).leafCount - 1)) :=
                  Nat.mul_le_mul_left _ hS_shrink
              _ = 3 ^ (rounds + 1) * ((d₁.cut d₂ hent).leafCount - 1) := by rw [pow_succ]; ring
              _ < 4 ^ (rounds + 1) := hsize
              _ = 4 * 4 ^ rounds := by rw [pow_succ]; ring
          omega
        have hT'_lt : 3 ^ rounds * (T'.leafCount - 1) < 4 ^ rounds := by
          have hmul : 4 * (3 ^ rounds * (T'.leafCount - 1)) < 4 * 4 ^ rounds := by
            calc 4 * (3 ^ rounds * (T'.leafCount - 1))
                = 3 ^ rounds * (4 * (T'.leafCount - 1)) := by ring
              _ ≤ 3 ^ rounds * (3 * ((d₁.cut d₂ hent).leafCount - 1)) :=
                  Nat.mul_le_mul_left _ hT'_shrink
              _ = 3 ^ (rounds + 1) * ((d₁.cut d₂ hent).leafCount - 1) := by rw [pow_succ]; ring
              _ < 4 ^ (rounds + 1) := hsize
              _ = 4 * 4 ^ rounds := by rw [pow_succ]; ring
          omega
        have hH_le : H.weightSum ≤ W := S.rootWeight_le_maxWeight.trans (hwS.trans hW)
        have hev := (evalIneqProtocol_spec H part W hH_le).2 x
        cases hb : (evalIneqProtocol H part W).run x
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hH_false : ¬ H.eval (joinPartition part x) := fun h ↦ by
            have := hev.mpr h; rw [hb] at this; cases this
          exact centroidSearchProtocol_correct hr part W rounds S (hwS.trans hW) hS_lt x
            (htrS _ hass) hH_false
        · simp only [↓reduceIte]
          have hH_true : H.eval (joinPartition part x) := hev.mp hb
          exact centroidSearchProtocol_correct hr part W rounds T' (hwT'.trans hW) hT'_lt x
            (htrT' _ hass hH_true) hG
      · rw [Protocol.run_bind]
        have h1 := d₁.leafCount_pos; have h2 := d₂.leafCount_pos
        have hd1_eq : d₁.leafCount = 1 := by unfold PrunedTree.leafCount at h3; omega
        have hd2_eq : d₂.leafCount = 1 := by unfold PrunedTree.leafCount at h3; omega
        have hlt0 : 3 ^ rounds * (1 - 1) < 4 ^ rounds := by simp
        have hL1_le : L₁.weightSum ≤ W :=
          d₁.rootWeight_le_maxWeight.trans
            ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hW)
        have hev := (evalIneqProtocol_spec L₁ part W hL1_le).2 x
        cases hb : (evalIneqProtocol L₁ part W).run x
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hL1_false : ¬ L₁.eval (joinPartition part x) := fun h ↦ by
            have := hev.mpr h; rw [hb] at this; cases this
          exact centroidSearchProtocol_correct hr part W rounds d₁ _ (hd1_eq ▸ hlt0) x
            hass.1 hL1_false
        · simp only [↓reduceIte]
          have hL1_true := hev.mp hb
          have hL2_false : ¬ _ := fun h2 ↦ hG (hent (joinPartition part x) hL1_true h2)
          exact centroidSearchProtocol_correct hr part W rounds d₂ _ (hd2_eq ▸ hlt0) x
            hass.2 hL2_false

/-- **Unconditional Tree-Like `Th(r)` → Deterministic `(r + 1)`-Party NOF Search Reduction**:
any tree-like `Th(r)` refutation `D` (`1 ≤ r`) of a CNF `φ` with `L = D.leafCount` leaves and
maximum coefficient weight `W = D.maxWeight` yields a deterministic `(r + 1)`-party NOF protocol
finding a falsified clause of `φ` on `joinPartition part x` in at most
`(3 * Nat.log 2 L + 3) * (r + 1) * (Nat.log 2 (2 * W + 1) + 1)` communication bits. -/
theorem exists_nof_search_of_thTreeRefutation {n r : ℕ} (hr : 1 ≤ r) {φ : CNF (Fin n)}
    (D : ThTreeDerivation φ (contradictionIneq n r)) (part : Fin n → Fin (r + 1)) :
    ∃ P : Protocol (fun _ : Fin (r + 1) ↦ BitString n) (Clause (Fin n)),
      P.depth ≤
        (3 * Nat.log 2 D.leafCount + 3) * (r + 1) * (Nat.log 2 (2 * D.maxWeight + 1) + 1) ∧
      ∀ x : Fin (r + 1) → BitString n,
        P.run x ∈ φ ∧ (P.run x).eval (joinPartition part x) = false := by
  let rounds : ℕ := 3 * Nat.log 2 D.leafCount + 3
  have hsize : 3 ^ rounds * (D.toPruned.leafCount - 1) < 4 ^ rounds := by
    rw [D.leafCount_toPruned]
    have hlog : D.leafCount < 2 ^ (Nat.log 2 D.leafCount + 1) :=
      Nat.lt_pow_succ_log_self (by omega) D.leafCount
    have hpow2 : ∀ t : ℕ, 2 ^ t * 3 ^ (3 * t) ≤ 4 ^ (3 * t) := by
      intro t
      induction t with
      | zero => norm_num
      | succ t ih =>
        have h64 : 2 * 3 ^ 3 ≤ 4 ^ 3 := by norm_num
        calc 2 ^ (t + 1) * 3 ^ (3 * (t + 1))
            = (2 * 3 ^ 3) * (2 ^ t * 3 ^ (3 * t)) := by rw [pow_succ, mul_add, pow_add]; ring
          _ ≤ 4 ^ 3 * 4 ^ (3 * t) := Nat.mul_le_mul h64 ih
          _ = 4 ^ (3 * (t + 1)) := by rw [← pow_add, mul_add]; ring_nf
    have h1 := hpow2 (Nat.log 2 D.leafCount + 1)
    have hrounds : rounds = 3 * (Nat.log 2 D.leafCount + 1) := by dsimp only [rounds]; ring
    rw [hrounds]
    have hlt_sub : D.leafCount - 1 < 2 ^ (Nat.log 2 D.leafCount + 1) := by omega
    calc 3 ^ (3 * (Nat.log 2 D.leafCount + 1)) * (D.leafCount - 1)
        < 3 ^ (3 * (Nat.log 2 D.leafCount + 1)) * 2 ^ (Nat.log 2 D.leafCount + 1) :=
          Nat.mul_lt_mul_of_pos_left hlt_sub (pow_pos (by omega) _)
      _ = 2 ^ (Nat.log 2 D.leafCount + 1) * 3 ^ (3 * (Nat.log 2 D.leafCount + 1)) := mul_comm _ _
      _ ≤ 4 ^ (3 * (Nat.log 2 D.leafCount + 1)) := h1
  refine ⟨centroidSearchProtocol part D.maxWeight rounds D.toPruned D.maxWeight_toPruned.le,
    ?_, fun x ↦ ?_⟩
  · have hd :=
      centroidSearchProtocol_depth part D.maxWeight rounds D.toPruned D.maxWeight_toPruned.le
    simpa [mul_assoc] using hd
  · exact centroidSearchProtocol_correct hr part D.maxWeight rounds D.toPruned
      D.maxWeight_toPruned.le hsize x (D.allAssumedTrue_toPruned _)
      (not_contradictionIneq_eval _)

end NOFSearchFromThTree

end CslibFrontier.Logics.Propositional.PolynomialThreshold
