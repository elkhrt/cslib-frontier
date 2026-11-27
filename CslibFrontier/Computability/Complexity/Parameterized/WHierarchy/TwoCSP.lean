/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.TwoCSP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Pairing

/-!
# Encoded Finite Binary CSP and `W[1]`-Completeness

Canonical framed unary encoding (`FinTwoCSP`, `encFinTwoCSP`) for heterogeneous finite `2-CSP`
instances, together with polynomial-time fpt-reductions to and from `Cslib.Complexity.Clique`,
proving `W[1]`-completeness and the collapse equivalence `W_one_eq_FPT_iff_finTwoCSP`.

## Main definitions

* `Cslib.Complexity.FinTwoCSPConstraint`, `Cslib.Complexity.encFinTwoCSPConstraint`.
* `Cslib.Complexity.FinTwoCSP`, `Cslib.Complexity.encFinTwoCSP`,
  `Cslib.Complexity.FinTwoCSP.toTwoCSP`, `Cslib.Complexity.FinTwoCSP.SatisfiableSet`.
* `Cslib.Complexity.FinTwoCSP.toClique`, `Cslib.Complexity.FinTwoCSP.ofClique`.

## Main results

* `Cslib.Complexity.FinTwoCSP.toClique_mem_clique_iff`,
  `Cslib.Complexity.FinTwoCSP.computableInPolyTime_toClique`,
  `Cslib.Complexity.FinTwoCSP.fptReducible_finTwoCSP_clique`,
  `Cslib.Complexity.FinTwoCSP.finTwoCSP_mem_W_one`: membership in `W[1]`.
* `Cslib.Complexity.FinTwoCSP.ofClique_isSatisfiable_iff`,
  `Cslib.Complexity.FinTwoCSP.computableInPolyTime_ofClique`,
  `Cslib.Complexity.FinTwoCSP.fptReducible_clique_finTwoCSP`,
  `Cslib.Complexity.FinTwoCSP.finTwoCSP_wHard`,
  `Cslib.Complexity.FinTwoCSP.W_one_eq_FPT_iff_finTwoCSP`: `W[1]`-hardness and collapse
  equivalence.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A binary constraint of an encoded finite `2-CSP` instance: ordered variable indices `(fst, snd)`
and a list `rel` of allowed value pairs `(a, b)`. -/
@[ext]
structure FinTwoCSPConstraint where
  /-- First variable index. -/
  fst : ℕ
  /-- Second variable index. -/
  snd : ℕ
  /-- List of allowed value pairs `(a, b)`. -/
  rel : List (ℕ × ℕ)
deriving DecidableEq, Repr

/-- Framed unary encoding of `FinTwoCSPConstraint`. -/
enc_structure encFinTwoCSPConstraint : FinTwoCSPConstraint where
  fst : encUnary,
  snd : encUnary,
  rel : (encList (encPair encUnary encUnary))

attribute [fun_prop] encFinTwoCSPConstraint_fst_polyTime
  encFinTwoCSPConstraint_snd_polyTime encFinTwoCSPConstraint_rel_polyTime
  encFinTwoCSPConstraint_mk_polyTime

/-- Canonical encoded carrier for finite heterogeneous `2-CSP` instances: `domSizes` records the
domain cardinality of each variable `0, …, domSizes.length - 1`, and `constraints` lists the
binary constraints. -/
@[ext]
structure FinTwoCSP where
  /-- Domain cardinality of each variable. -/
  domSizes : List ℕ
  /-- Binary constraints of the instance. -/
  constraints : List FinTwoCSPConstraint
deriving DecidableEq, Repr

/-- Framed unary encoding of `FinTwoCSP` matching the explicit input size `poly(|X|, |Σ|, m)`. -/
enc_structure encFinTwoCSP : FinTwoCSP where
  domSizes : (encList encUnary),
  constraints : (encList encFinTwoCSPConstraint)

attribute [fun_prop] encFinTwoCSP_domSizes_polyTime
  encFinTwoCSP_constraints_polyTime encFinTwoCSP_mk_polyTime

namespace FinTwoCSP

/-- Number of variables `|X| = I.domSizes.length`. -/
abbrev numVars (I : FinTwoCSP) : ℕ := I.domSizes.length

/-- Rewrites `I.domSizes.length` as `I.numVars`. -/
theorem length_domSizes (I : FinTwoCSP) : I.domSizes.length = I.numVars := rfl

/-- `FinTwoCSP.numVars` is computable in polynomial time (unary output). -/
@[fun_prop]
theorem computableInPolyTime_numVars {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → FinTwoCSP} (hf : ComputableInPolyTime f encIn encFinTwoCSP) :
    ComputableInPolyTime (fun x => (f x).numVars) encIn encUnary :=
  (ComputableInPolyTime.length_list encUnary).comp (encFinTwoCSP_domSizes_polyTime hf)

/-- Alphabet size `|Σ| = max_{x} |Σ_x|` (`0` if `I.domSizes` is empty). -/
@[expose]
def alphabetSize (I : FinTwoCSP) : ℕ := I.domSizes.foldr max 0

/-- Every domain size in `I.domSizes` is at most `I.alphabetSize`. -/
theorem domSize_le_alphabetSize (I : FinTwoCSP) (x : Fin I.numVars) :
    I.domSizes[x.1] ≤ I.alphabetSize := by
  have hmem : I.domSizes[x.1] ∈ I.domSizes := List.getElem_mem x.2
  suffices ∀ l : List ℕ, ∀ d ∈ l, d ≤ l.foldr max 0 from this I.domSizes _ hmem
  intro l
  induction l with
  | nil => intro _ hd; cases hd
  | cons a ds ih =>
    intro d hd
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hd with rfl | htl
    · exact le_max_left _ _
    · exact (ih d htl).trans (le_max_right _ _)

/-- Variable domain `Fin I.domSizes[x]` for `x : Fin I.numVars`. -/
abbrev Domain (I : FinTwoCSP) (x : Fin I.numVars) : Type := Fin (I.domSizes[x.1]'x.2)

/-- Converts `I : FinTwoCSP` to its abstract `TwoCSP` over `Fin I.numVars` and `I.Domain`,
keeping all in-range constraints. -/
@[expose]
def toTwoCSP (I : FinTwoCSP) : TwoCSP (Fin I.numVars) I.Domain where
  constraints := I.constraints.filterMap fun c =>
    if h : c.fst < I.numVars ∧ c.snd < I.numVars then
      some ⟨⟨c.fst, h.1⟩, ⟨c.snd, h.2⟩,
        Finset.univ.filter fun p : Fin (I.domSizes[c.fst]'h.1) × Fin (I.domSizes[c.snd]'h.2) =>
          ((p.1 : ℕ), (p.2 : ℕ)) ∈ c.rel⟩
    else none

/-- Membership of a constraint in `I.toTwoCSP.constraints`. -/
theorem mem_toTwoCSP_constraints_iff {I : FinTwoCSP}
    {c' : BinaryConstraint (Fin I.numVars) I.Domain} :
    c' ∈ I.toTwoCSP.constraints ↔
      ∃ c ∈ I.constraints, ∃ (h₁ : c.fst < I.numVars) (h₂ : c.snd < I.numVars),
        c' = ⟨⟨c.fst, h₁⟩, ⟨c.snd, h₂⟩,
          Finset.univ.filter fun p => ((p.1 : ℕ), (p.2 : ℕ)) ∈ c.rel⟩ := by
  simp only [toTwoCSP, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hsome⟩
    by_cases h : c.fst < I.numVars ∧ c.snd < I.numVars
    · rw [dite_eq_left h, Option.some.injEq] at hsome
      exact ⟨c, hc, h.1, h.2, hsome.symm⟩
    · rw [dite_eq_right h] at hsome; cases hsome
  · rintro ⟨c, hc, h₁, h₂, rfl⟩
    exact ⟨c, hc, by simp [h₁, h₂]⟩

/-- Satisfiability of `I : FinTwoCSP` via `I.toTwoCSP`. -/
@[expose]
def IsSatisfiable (I : FinTwoCSP) : Prop := I.toTwoCSP.IsSatisfiable

/-- Worst-case `r`-list satisfiability of `I : FinTwoCSP`. -/
@[expose]
def IsListSatisfiable (I : FinTwoCSP) (r : ℕ) : Prop := I.toTwoCSP.IsListSatisfiable r

/-- Average `r`-list satisfiability of `I : FinTwoCSP`. -/
@[expose]
def IsAvgListSatisfiable (I : FinTwoCSP) (r : ℝ) : Prop := I.toTwoCSP.IsAvgListSatisfiable r

/-- Rectangularity of all constraint relations in `I : FinTwoCSP`. -/
@[expose]
def HasRectangularRelations (I : FinTwoCSP) : Prop := I.toTwoCSP.HasRectangularRelations

/-- The decision problem of satisfiable `FinTwoCSP` instances. -/
@[expose]
def SatisfiableSet : Set FinTwoCSP := {I | I.IsSatisfiable}

theorem mem_satisfiableSet_iff {I : FinTwoCSP} :
    I ∈ SatisfiableSet ↔ I.IsSatisfiable := Iff.rfl

/-- An assignment `σ` satisfies `I.toTwoCSP` iff every in-range constraint in `I.constraints` is
satisfied by `σ`. -/
theorem satisfies_toTwoCSP_iff {I : FinTwoCSP}
    {σ : ∀ x : Fin I.numVars, Fin I.domSizes[x.1]} :
    I.toTwoCSP.Satisfies σ ↔
      ∀ c ∈ I.constraints, ∀ (h₁ : c.fst < I.numVars) (h₂ : c.snd < I.numVars),
        ((σ ⟨c.fst, h₁⟩ : ℕ), (σ ⟨c.snd, h₂⟩ : ℕ)) ∈ c.rel := by
  constructor
  · intro h c hc h₁ h₂
    have hmem := (h _ (mem_toTwoCSP_constraints_iff.mpr ⟨c, hc, h₁, h₂, rfl⟩)).mem_rel
    simpa using hmem
  · intro h c' hc'
    rcases mem_toTwoCSP_constraints_iff.mp hc' with ⟨c, hc, h₁, h₂, rfl⟩
    exact BinaryConstraint.satisfies_of_mem_rel (by simpa using h c hc h₁ h₂)

/-- `I.toTwoCSP.alphabetSize` agrees with `I.alphabetSize`. -/
theorem alphabetSize_toTwoCSP (I : FinTwoCSP) : I.toTwoCSP.alphabetSize = I.alphabetSize := by
  apply le_antisymm
  · exact TwoCSP.alphabetSize_le_iff.mpr fun x => by
      simpa [Fintype.card_fin] using I.domSize_le_alphabetSize x
  · suffices ∀ l : List ℕ, (∀ i (hi : i < l.length), l[i] ≤ I.toTwoCSP.alphabetSize) →
        l.foldr max 0 ≤ I.toTwoCSP.alphabetSize by
      exact this I.domSizes fun i hi => by
        simpa [Fintype.card_fin] using I.toTwoCSP.card_domain_le_alphabetSize ⟨i, hi⟩
    intro l
    induction l with
    | nil => intro _; exact Nat.zero_le _
    | cons d ds ih =>
      intro h
      rw [List.foldr_cons]
      exact max_le (h 0 (Nat.zero_lt_succ _))
        (ih fun i hi => h (i + 1) (Nat.succ_lt_succ hi))

/-! #### Reduction `FinTwoCSP → Clique` (membership in `W[1]`) -/

private lemma mem_rel_any_iff_aux (rel : List (ℕ × ℕ)) (a b : ℕ) :
    (rel.any fun p => p.1 == a && p.2 == b) = true ↔ (a, b) ∈ rel := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨x, y⟩, hmem, hx, hy⟩ => by dsimp only at hx hy; subst hx; subst hy; exact hmem,
    fun hmem => ⟨(a, b), hmem, rfl, rfl⟩⟩

/-- Boolean check that all constraints in `I` between `x` and `y` allow `(a, b)` and `(b, a)`. -/
@[expose]
def pairAllowedBool (I : FinTwoCSP) (x a y b : ℕ) : Bool :=
  I.constraints.all fun c =>
    (!(c.fst == x && c.snd == y) || c.rel.any fun p => p.1 == a && p.2 == b) &&
      (!(c.fst == y && c.snd == x) || c.rel.any fun p => p.1 == b && p.2 == a)

private lemma pairAllowedBool_eq_true_iff (I : FinTwoCSP) (x a y b : ℕ) :
    pairAllowedBool I x a y b = true ↔
      (∀ c ∈ I.constraints, c.fst = x → c.snd = y → (a, b) ∈ c.rel) ∧
      (∀ c ∈ I.constraints, c.fst = y → c.snd = x → (b, a) ∈ c.rel) := by
  simp only [pairAllowedBool, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, mem_rel_any_iff_aux]
  constructor
  · intro h
    refine ⟨fun c hc h1 h2 => ?_, fun c hc h1 h2 => ?_⟩
    · rcases (h c hc).1 with hne | hmem
      · rcases hne with hne | hne <;> [exact absurd h1 hne; exact absurd h2 hne]
      · exact hmem
    · rcases (h c hc).2 with hne | hmem
      · rcases hne with hne | hne <;> [exact absurd h1 hne; exact absurd h2 hne]
      · exact hmem
  · rintro ⟨h1, h2⟩ c hc
    refine ⟨?_, ?_⟩
    · by_cases hx : c.fst = x
      · by_cases hy : c.snd = y
        · exact Or.inr (h1 c hc hx hy)
        · exact Or.inl (Or.inr hy)
      · exact Or.inl (Or.inl hx)
    · by_cases hy : c.fst = y
      · by_cases hx : c.snd = x
        · exact Or.inr (h2 c hc hy hx)
        · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl hy)

/-- Polynomial-time reduction from `FinTwoCSP` to `Cslib.Complexity.Clique`, preserving the
parameter `I.numVars` identically. -/
@[expose]
def toClique (I : FinTwoCSP) : CliqueInstance :=
  let vs : List (ℕ × ℕ) :=
    ((List.range I.numVars).flatMap fun x =>
      (List.range (I.domSizes.getD x 0)).map fun a => (x, a)).filter fun p =>
        pairAllowedBool I p.1 p.2 p.1 p.2
  let vertices : List ℕ := vs.map fun p => Nat.pair p.1 p.2
  let edges : List (ℕ × ℕ) :=
    vs.flatMap fun p =>
      (vs.filter fun q => decide (p.1 ≠ q.1) && pairAllowedBool I p.1 p.2 q.1 q.2).map fun q =>
        (Nat.pair p.1 p.2, Nat.pair q.1 q.2)
  ⟨⟨vertices, edges⟩, I.numVars⟩

private lemma mem_toClique_vertices_iff (I : FinTwoCSP) (v : ℕ) :
    v ∈ (toClique I).graph.vertices ↔
      ∃ (x : Fin I.numVars) (a : Fin I.domSizes[x.1]),
        v = Nat.pair x.1 a.1 ∧
        ∀ c ∈ I.constraints, c.fst = x.1 → c.snd = x.1 → (a.1, a.1) ∈ c.rel := by
  simp only [toClique, List.mem_map, List.mem_filter, List.mem_flatMap, List.mem_range,
    pairAllowedBool_eq_true_iff, and_self]
  constructor
  · rintro ⟨⟨x, a⟩, ⟨⟨x', hx', a', ha', hmk⟩, hloop⟩, rfl⟩
    cases hmk
    have ha'' : a < I.domSizes[x] := by rwa [List.getD_eq_getElem _ _ hx'] at ha'
    exact ⟨⟨x, hx'⟩, ⟨a, ha''⟩, rfl, hloop⟩
  · rintro ⟨x, a, rfl, hloop⟩
    refine ⟨(x.1, a.1), ⟨⟨x.1, x.2, a.1, ?_, rfl⟩, hloop⟩, rfl⟩
    rw [List.getD_eq_getElem _ _ x.2]; exact a.2

private lemma toClique_adj_iff (I : FinTwoCSP) (v w : ℕ) :
    (toClique I).graph.toSimpleGraph.Adj v w ↔
      v ≠ w ∧ ∃ (x y : Fin I.numVars) (a : Fin I.domSizes[x.1]) (b : Fin I.domSizes[y.1]),
        v = Nat.pair x.1 a.1 ∧ w = Nat.pair y.1 b.1 ∧ x ≠ y ∧
        (∀ c ∈ I.constraints, c.fst = x.1 → c.snd = x.1 → (a.1, a.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = y.1 → c.snd = y.1 → (b.1, b.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = x.1 → c.snd = y.1 → (a.1, b.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = y.1 → c.snd = x.1 → (b.1, a.1) ∈ c.rel) := by
  rw [Graph.toSimpleGraph_adj]
  have hedge : ∀ u₁ u₂, (u₁, u₂) ∈ (toClique I).graph.edges ↔
      ∃ (x y : Fin I.numVars) (a : Fin I.domSizes[x.1]) (b : Fin I.domSizes[y.1]),
        u₁ = Nat.pair x.1 a.1 ∧ u₂ = Nat.pair y.1 b.1 ∧ x ≠ y ∧
        (∀ c ∈ I.constraints, c.fst = x.1 → c.snd = x.1 → (a.1, a.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = y.1 → c.snd = y.1 → (b.1, b.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = x.1 → c.snd = y.1 → (a.1, b.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = y.1 → c.snd = x.1 → (b.1, a.1) ∈ c.rel) := by
    intro u₁ u₂
    simp only [toClique, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, pairAllowedBool_eq_true_iff, and_self, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨x, a⟩, ⟨⟨x', hx', a', ha', hmk1⟩, hloop1⟩,
        ⟨y, b⟩, ⟨⟨⟨y', hy', b', hb', hmk2⟩, hloop2⟩, hne, hxy, hyx⟩, rfl, rfl⟩
      cases hmk1; cases hmk2
      have ha'' : a < I.domSizes[x] := by rwa [List.getD_eq_getElem _ _ hx'] at ha'
      have hb'' : b < I.domSizes[y] := by rwa [List.getD_eq_getElem _ _ hy'] at hb'
      exact ⟨⟨x, hx'⟩, ⟨y, hy'⟩, ⟨a, ha''⟩, ⟨b, hb''⟩, rfl, rfl, fun h => hne (congrArg Fin.val h),
        hloop1, hloop2, hxy, hyx⟩
    · rintro ⟨x, y, a, b, rfl, rfl, hne, hloop1, hloop2, hxy, hyx⟩
      refine ⟨(x.1, a.1), ⟨⟨x.1, x.2, a.1, ?_, rfl⟩, hloop1⟩,
        (y.1, b.1), ⟨⟨⟨y.1, y.2, b.1, ?_, rfl⟩, hloop2⟩,
          fun h => hne (Fin.ext h), hxy, hyx⟩, ⟨rfl, rfl⟩⟩
      · rw [List.getD_eq_getElem _ _ x.2]; exact a.2
      · rw [List.getD_eq_getElem _ _ y.2]; exact b.2
  rw [hedge v w, hedge w v]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨y, x, b, a, hw, hv, hyx, hly, hlx, hyx', hxy'⟩
  · exact h
  · exact ⟨x, y, a, b, hv, hw, hyx.symm, hlx, hly, hxy', hyx'⟩

/-- Correctness of `FinTwoCSP.toClique`: `I` is satisfiable iff `I.toClique ∈ Clique`. -/
theorem toClique_mem_clique_iff (I : FinTwoCSP) :
    I.toClique ∈ Clique ↔ I.IsSatisfiable := by
  rw [mem_Clique_iff]
  constructor
  · rintro ⟨S, hSV, hclq, hcard⟩
    have hunpair : ∀ v ∈ S,
        ∃ (x : Fin I.numVars) (a : Fin I.domSizes[x.1]),
          v = Nat.pair x.1 a.1 ∧
          ∀ c ∈ I.constraints, c.fst = x.1 → c.snd = x.1 → (a.1, a.1) ∈ c.rel :=
      fun v hv => (mem_toClique_vertices_iff I v).mp (hSV v hv)
    have hinj : Set.InjOn (fun v => (Nat.unpair v).1) (S : Set ℕ) := by
      intro v₁ hv₁ v₂ hv₂ hfst
      by_contra hne
      have hadj := (toClique_adj_iff I v₁ v₂).mp (hclq hv₁ hv₂ hne)
      rcases hadj with ⟨-, x, y, a, b, rfl, rfl, hxy, -⟩
      simp only [Nat.unpair_pair] at hfst
      exact hxy (Fin.ext hfst)
    have himg_sub : S.image (fun v => (Nat.unpair v).1) ⊆ Finset.range I.numVars := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
      rcases hunpair v hv with ⟨y, a, rfl, -⟩
      simp [Nat.unpair_pair, y.2]
    have himg_eq : S.image (fun v => (Nat.unpair v).1) = Finset.range I.numVars :=
      Finset.eq_of_subset_of_card_le himg_sub
        (by rw [Finset.card_range, Finset.card_image_of_injOn hinj, hcard]; rfl)
    have hex : ∀ x : Fin I.numVars,
        ∃ v ∈ S, ∃ a : Fin I.domSizes[x.1], v = Nat.pair x.1 a.1 := by
      intro x
      have hx : x.1 ∈ S.image (fun v => (Nat.unpair v).1) :=
        himg_eq ▸ Finset.mem_range.mpr x.2
      rcases Finset.mem_image.mp hx with ⟨v, hv, hxv⟩
      rcases hunpair v hv with ⟨y, a, rfl, -⟩
      simp only [Nat.unpair_pair] at hxv
      have hy : y = x := Fin.ext hxv
      subst hy
      exact ⟨Nat.pair y.1 a.1, hv, a, rfl⟩
    let σ : ∀ x : Fin I.numVars, Fin I.domSizes[x.1] := fun x => (hex x).choose_spec.2.choose
    refine ⟨σ, satisfies_toTwoCSP_iff.mpr fun c hc h₁ h₂ => ?_⟩
    set x : Fin I.numVars := ⟨c.fst, h₁⟩
    set y : Fin I.numVars := ⟨c.snd, h₂⟩
    have hvx : Nat.pair x.1 (σ x).1 ∈ S := by
      have h1 := (hex x).choose_spec.1
      have h2 := (hex x).choose_spec.2.choose_spec
      rwa [← h2]
    have hvy : Nat.pair y.1 (σ y).1 ∈ S := by
      have h1 := (hex y).choose_spec.1
      have h2 := (hex y).choose_spec.2.choose_spec
      rwa [← h2]
    by_cases hxy : x = y
    · rcases hunpair _ hvx with ⟨x', a', heq', hloop⟩
      have hpair := Nat.pair_eq_pair.mp heq'
      have hax : (σ x).1 = a'.1 := hpair.2
      have hay : (σ y).1 = a'.1 := hxy ▸ hax
      have hxx : c.fst = x'.1 := hpair.1
      have hyy : c.snd = x'.1 := (congrArg Fin.val hxy).symm.trans hxx
      rw [hax, hay]
      exact hloop c hc hxx hyy
    · have hne : Nat.pair x.1 (σ x).1 ≠ Nat.pair y.1 (σ y).1 :=
        fun h => hxy (Fin.ext (Nat.pair_eq_pair.mp h).1)
      rcases (toClique_adj_iff I _ _).mp (hclq hvx hvy hne) with
        ⟨-, x', y', a', b', heq1, heq2, -, -, -, hrel, -⟩
      have hp1 := Nat.pair_eq_pair.mp heq1
      have hp2 := Nat.pair_eq_pair.mp heq2
      rw [hp1.2, hp2.2]
      exact hrel c hc hp1.1 hp2.1
  · rintro ⟨σ, hσ⟩
    have hsat := satisfies_toTwoCSP_iff.mp hσ
    let emb : Fin I.numVars ↪ ℕ :=
      ⟨fun x => Nat.pair x.1 (σ x).1, fun x y h => Fin.ext (Nat.pair_eq_pair.mp h).1⟩
    refine ⟨Finset.univ.map emb, ?_, ?_, by simp [toClique]⟩
    · intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, -, rfl⟩
      exact (mem_toClique_vertices_iff I _).mpr
        ⟨x, σ x, rfl, fun c hc h1 h2 => by
          have h := hsat c hc (h1.symm ▸ x.2) (h2.symm ▸ x.2)
          have hfx : (⟨c.fst, h1.symm ▸ x.2⟩ : Fin I.numVars) = x := Fin.ext h1
          have hfy : (⟨c.snd, h2.symm ▸ x.2⟩ : Fin I.numVars) = x := Fin.ext h2
          rwa [hfx, hfy] at h⟩
    · intro v₁ hv₁ v₂ hv₂ hne
      rcases Finset.mem_map.mp hv₁ with ⟨x, -, rfl⟩
      rcases Finset.mem_map.mp hv₂ with ⟨y, -, rfl⟩
      have hxy : x ≠ y := fun h => hne (congrArg emb h)
      refine (toClique_adj_iff I _ _).mpr ⟨hne, x, y, σ x, σ y, rfl, rfl, hxy,
        fun c hc h1 h2 => by
          have h := hsat c hc (h1.symm ▸ x.2) (h2.symm ▸ x.2)
          rwa [show (⟨c.fst, _⟩ : Fin I.numVars) = x from Fin.ext h1,
            show (⟨c.snd, _⟩ : Fin I.numVars) = x from Fin.ext h2] at h,
        fun c hc h1 h2 => by
          have h := hsat c hc (h1.symm ▸ y.2) (h2.symm ▸ y.2)
          rwa [show (⟨c.fst, _⟩ : Fin I.numVars) = y from Fin.ext h1,
            show (⟨c.snd, _⟩ : Fin I.numVars) = y from Fin.ext h2] at h,
        fun c hc h1 h2 => by
          have h := hsat c hc (h1.symm ▸ x.2) (h2.symm ▸ y.2)
          rwa [show (⟨c.fst, _⟩ : Fin I.numVars) = x from Fin.ext h1,
            show (⟨c.snd, _⟩ : Fin I.numVars) = y from Fin.ext h2] at h,
        fun c hc h1 h2 => by
          have h := hsat c hc (h1.symm ▸ y.2) (h2.symm ▸ x.2)
          rwa [show (⟨c.fst, _⟩ : Fin I.numVars) = y from Fin.ext h1,
            show (⟨c.snd, _⟩ : Fin I.numVars) = x from Fin.ext h2] at h⟩

/-- `FinTwoCSP.toClique` is computable in polynomial time. -/
theorem computableInPolyTime_toClique :
    ComputableInPolyTime toClique encFinTwoCSP encCliqueInstance := by
  have hpair_bin : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encUnary encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.unary_pair
  have hallow : ComputableInPolyTime
      (fun q : FinTwoCSP × ((ℕ × ℕ) × (ℕ × ℕ)) =>
        pairAllowedBool q.1 q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2)
      (encPair encFinTwoCSP (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))
      encBool := by
    unfold pairAllowedBool
    polytime
  have hvs : ComputableInPolyTime
      (fun I : FinTwoCSP =>
        ((List.range I.numVars).flatMap fun x =>
          (List.range (I.domSizes.getD x 0)).map fun a => (x, a)).filter fun p =>
            pairAllowedBool I p.1 p.2 p.1 p.2)
      encFinTwoCSP (encList (encPair encUnary encUnary)) := by
    have hraw : ComputableInPolyTime
        (fun I : FinTwoCSP =>
          (List.range I.numVars).flatMap fun x =>
            (List.range (I.domSizes.getD x 0)).map fun a => (x, a))
        encFinTwoCSP (encList (encPair encUnary encUnary)) := by
      unfold numVars
      polytime
    refine ComputableInPolyTime.filterWithInput hraw ?_
    exact hallow.comp (by
      have hI := ComputableInPolyTime.fst encFinTwoCSP (encPair encUnary encUnary)
      have hp := ComputableInPolyTime.snd encFinTwoCSP (encPair encUnary encUnary)
      exact hI.prod (hp.prod hp))
  have hverts : ComputableInPolyTime (fun I : FinTwoCSP => (toClique I).graph.vertices)
      encFinTwoCSP (encList encNat) := by
    change ComputableInPolyTime
      (fun I : FinTwoCSP =>
        (((List.range I.numVars).flatMap fun x =>
          (List.range (I.domSizes.getD x 0)).map fun a => (x, a)).filter fun p =>
            pairAllowedBool I p.1 p.2 p.1 p.2).map fun p => Nat.pair p.1 p.2)
      encFinTwoCSP (encList encNat)
    exact ComputableInPolyTime.mapWithInput hvs (hpair_bin.comp (ComputableInPolyTime.snd _ _))
  have hedges : ComputableInPolyTime (fun I : FinTwoCSP => (toClique I).graph.edges)
      encFinTwoCSP (encList (encPair encNat encNat)) := by
    change ComputableInPolyTime
      (fun I : FinTwoCSP =>
        let vs := ((List.range I.numVars).flatMap fun x =>
          (List.range (I.domSizes.getD x 0)).map fun a => (x, a)).filter fun p =>
            pairAllowedBool I p.1 p.2 p.1 p.2
        vs.flatMap fun p =>
          (vs.filter fun q => decide (p.1 ≠ q.1) && pairAllowedBool I p.1 p.2 q.1 q.2).map
            fun q => (Nat.pair p.1 p.2, Nat.pair q.1 q.2))
      encFinTwoCSP (encList (encPair encNat encNat))
    refine ComputableInPolyTime.flatMapWithInput hvs ?_
    have hflt : ComputableInPolyTime
        (fun s : FinTwoCSP × (ℕ × ℕ) =>
          (((List.range s.1.numVars).flatMap fun x =>
            (List.range (s.1.domSizes.getD x 0)).map fun a => (x, a)).filter fun p =>
              pairAllowedBool s.1 p.1 p.2 p.1 p.2).filter fun q =>
            decide (s.2.1 ≠ q.1) && pairAllowedBool s.1 s.2.1 s.2.2 q.1 q.2)
        (encPair encFinTwoCSP (encPair encUnary encUnary))
        (encList (encPair encUnary encUnary)) := by
      refine ComputableInPolyTime.filterWithInput
        (hvs.comp (ComputableInPolyTime.fst _ _)) ?_
      have hne : ComputableInPolyTime
          (fun t : (FinTwoCSP × (ℕ × ℕ)) × (ℕ × ℕ) => decide (t.1.2.1 ≠ t.2.1))
          (encPair (encPair encFinTwoCSP (encPair encUnary encUnary)) (encPair encUnary encUnary))
          encBool := by
        have hEq : ComputableInPolyTime
            (fun t : (FinTwoCSP × (ℕ × ℕ)) × (ℕ × ℕ) => !(t.1.2.1 == t.2.1))
            (encPair (encPair encFinTwoCSP (encPair encUnary encUnary)) (encPair encUnary encUnary))
            encBool := by polytime
        have hfun : (fun t : (FinTwoCSP × (ℕ × ℕ)) × (ℕ × ℕ) => !(t.1.2.1 == t.2.1)) =
            (fun t => decide (t.1.2.1 ≠ t.2.1)) := funext fun t => by
          by_cases h : t.1.2.1 = t.2.1 <;> simp [h]
        rwa [← hfun]
      have hall : ComputableInPolyTime
          (fun t : (FinTwoCSP × (ℕ × ℕ)) × (ℕ × ℕ) =>
            pairAllowedBool t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2)
          (encPair (encPair encFinTwoCSP (encPair encUnary encUnary)) (encPair encUnary encUnary))
          encBool :=
        hallow.comp (by
          have h1 := ComputableInPolyTime.fst
            (encPair encFinTwoCSP (encPair encUnary encUnary)) (encPair encUnary encUnary)
          have h2 := ComputableInPolyTime.snd
            (encPair encFinTwoCSP (encPair encUnary encUnary)) (encPair encUnary encUnary)
          exact h1.fst'.prod (h1.snd'.prod h2))
      exact ComputableInPolyTime.bool_and' hne hall
    refine ComputableInPolyTime.mapWithInput hflt ?_
    have h1 := (ComputableInPolyTime.fst (encPair encFinTwoCSP (encPair encUnary encUnary))
      (encPair encUnary encUnary)).snd'
    have h2 := ComputableInPolyTime.snd (encPair encFinTwoCSP (encPair encUnary encUnary))
      (encPair encUnary encUnary)
    exact (hpair_bin.comp h1).prod (hpair_bin.comp h2)
  have hm : ComputableInPolyTime (fun I : FinTwoCSP => I.numVars) encFinTwoCSP encNat := by
    unfold numVars
    exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hmk : toClique = fun I : FinTwoCSP =>
      (⟨⟨(toClique I).graph.vertices, (toClique I).graph.edges⟩, I.numVars⟩ : CliqueInstance) :=
    rfl
  rw [hmk]
  exact encCliqueInstance_mk_polyTime
    (encGraph_mk_polyTime hverts hedges) hm

/-- `FinTwoCSP.SatisfiableSet` fpt-reduces to `Cslib.Complexity.Clique`. -/
theorem fptReducible_finTwoCSP_clique :
    FPTReducible encFinTwoCSP encCliqueInstance FinTwoCSP.numVars (·.m)
      SatisfiableSet Clique :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_toClique
    (h := id) (fun _ => le_rfl) fun I => (toClique_mem_clique_iff I).symm

/-- `FinTwoCSP.SatisfiableSet` belongs to `W[1]`. -/
theorem finTwoCSP_mem_W_one :
    SatisfiableSet ∈ W 1 encFinTwoCSP FinTwoCSP.numVars :=
  fptReducible_finTwoCSP_clique.mem_W Clique_mem_W

/-! #### Reduction `Clique → FinTwoCSP` (`W[1]`-hardness) -/

/-- Fixed unsatisfiable `FinTwoCSP` instance (`2` variables of domain size `1`, empty relation). -/
@[expose]
def unsatInstance : FinTwoCSP :=
  ⟨[1, 1], [⟨0, 1, []⟩]⟩

theorem not_isSatisfiable_unsatInstance : ¬ unsatInstance.IsSatisfiable := by
  rintro ⟨σ, hσ⟩
  have h := satisfies_toTwoCSP_iff.mp hσ ⟨0, 1, []⟩ (by simp [unsatInstance])
    (by decide) (by decide)
  simp at h

/-- Polynomial-time reduction from `Cslib.Complexity.Clique` to `FinTwoCSP`, bounding the
number of variables by `x.m + 2`. -/
@[expose]
def ofClique (x : CliqueInstance) : FinTwoCSP :=
  let V := x.graph.distinctVertices
  let n := V.length
  if x.m ≤ n then
    let k := min n x.m
    let rel := (List.range n).flatMap fun a =>
      ((List.range n).filter fun b => x.graph.adjBool (V.getD a 0) (V.getD b 0)).map fun b =>
        (a, b)
    let constraints := (List.range k).flatMap fun i =>
      ((List.range k).filter fun j => decide (i < j)).map fun j => ⟨i, j, rel⟩
    ⟨List.replicate k n, constraints⟩
  else
    unsatInstance

theorem ofClique_numVars_le (x : CliqueInstance) : (ofClique x).numVars ≤ x.m + 2 := by
  unfold ofClique numVars
  dsimp only
  split_ifs with h
  · simp [List.length_replicate, Nat.min_eq_right h]
  · simp [unsatInstance]

/-- Correctness of `FinTwoCSP.ofClique`: `x ∈ Clique ↔ (ofClique x).IsSatisfiable`. -/
theorem ofClique_isSatisfiable_iff (x : CliqueInstance) :
    (ofClique x).IsSatisfiable ↔ x ∈ Clique := by
  rw [mem_Clique_iff]
  unfold ofClique
  dsimp only
  set V := x.graph.distinctVertices
  set n := V.length
  have hV_nodup : V.Nodup := Graph.nodup_distinctVertices x.graph
  have hV_mem : ∀ u, u ∈ V ↔ u ∈ x.graph.vertices := fun _ => Graph.mem_distinctVertices
  have hcardV : x.graph.vertices.toFinset.card = n := by
    have heq : V.toFinset = x.graph.vertices.toFinset := by
      ext u; simp [hV_mem]
    rw [← heq, List.toFinset_card_of_nodup hV_nodup]
  split_ifs with hmn
  · have hk : min n x.m = x.m := Nat.min_eq_right hmn
    rw [hk]
    set rel := (List.range n).flatMap fun a =>
      ((List.range n).filter fun b => x.graph.adjBool (V.getD a 0) (V.getD b 0)).map fun b =>
        (a, b)
    set I : FinTwoCSP :=
      ⟨List.replicate x.m n, (List.range x.m).flatMap fun i =>
        ((List.range x.m).filter fun j => decide (i < j)).map fun j => ⟨i, j, rel⟩⟩
    have hrel_mem : ∀ a b : ℕ, (a, b) ∈ rel ↔
        a < n ∧ b < n ∧ x.graph.toSimpleGraph.Adj (V.getD a 0) (V.getD b 0) := by
      intro a b
      simp only [rel, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
        Graph.adjBool_eq_true_iff, Prod.mk.injEq]
      exact ⟨fun ⟨a', ha', b', ⟨hb', hadj⟩, h1, h2⟩ => ⟨h1 ▸ ha', h2 ▸ hb', h1 ▸ h2 ▸ hadj⟩,
        fun ⟨ha, hb, hadj⟩ => ⟨a, ha, b, ⟨hb, hadj⟩, rfl, rfl⟩⟩
    constructor
    · rintro ⟨σ, hσ⟩
      have hsat := satisfies_toTwoCSP_iff.mp hσ
      have hdom : ∀ i : Fin I.numVars, I.domSizes[i.1] = n := fun i => by
        simp [I, List.getElem_replicate]
      have hnum : I.numVars = x.m := by simp [I, numVars]
      have hlt_n : ∀ i : Fin x.m, (σ ⟨i.1, hnum.symm ▸ i.2⟩ : ℕ) < n := fun i => by
        have h := (σ ⟨i.1, hnum.symm ▸ i.2⟩).2
        rw [← hdom ⟨i.1, hnum.symm ▸ i.2⟩]
        exact h
      have hadj_ij : ∀ i j : Fin x.m, i < j →
          x.graph.toSimpleGraph.Adj (V.getD (σ ⟨i.1, hnum.symm ▸ i.2⟩).1 0)
            (V.getD (σ ⟨j.1, hnum.symm ▸ j.2⟩).1 0) := fun i j hij => by
        have hc : ⟨i.1, j.1, rel⟩ ∈ I.constraints := by
          simp only [I, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
            decide_eq_true_eq]
          exact ⟨i.1, i.2, j.1, ⟨j.2, hij⟩, rfl⟩
        exact ((hrel_mem _ _).mp (hsat _ hc (hnum.symm ▸ i.2) (hnum.symm ▸ j.2))).2.2
      let f : Fin x.m → ℕ := fun i => V.getD (σ ⟨i.1, hnum.symm ▸ i.2⟩).1 0
      have hfinj : Function.Injective f := by
        intro i j hij
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact absurd hij (hadj_ij i j hlt).ne
        · exact heq
        · exact absurd hij.symm (hadj_ij j i hgt).ne
      let emb : Fin x.m ↪ ℕ := ⟨f, hfinj⟩
      refine ⟨Finset.univ.map emb, ?_, ?_, by simp⟩
      · intro v hv
        rcases Finset.mem_map.mp hv with ⟨i, -, rfl⟩
        have hi := hlt_n i
        rw [← hV_mem]
        change V.getD (σ ⟨i.1, hnum.symm ▸ i.2⟩).1 0 ∈ V
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      · intro u hu v hv huv
        rcases Finset.mem_map.mp hu with ⟨i, -, rfl⟩
        rcases Finset.mem_map.mp hv with ⟨j, -, rfl⟩
        have hij : i ≠ j := fun h => huv (congrArg emb h)
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hadj_ij i j hlt
        · exact (hadj_ij j i hgt).symm
    · rintro ⟨S, hSV, hclq, hcard⟩
      have hsub : S ⊆ V.toFinset := fun v hv => List.mem_toFinset.mpr ((hV_mem v).mpr (hSV v hv))
      have heq_f : ∃ g : Fin x.m ↪ ℕ, ∀ i, g i ∈ S := by
        have h := S.equivFinOfCardEq hcard
        exact ⟨h.symm.toEmbedding.trans (Function.Embedding.subtype _), fun i => (h.symm i).2⟩
      rcases heq_f with ⟨g, hg⟩
      have hnum : I.numVars = x.m := by simp [I, numVars]
      have hdom : ∀ i : Fin I.numVars, I.domSizes[i.1] = n := fun i => by
        simp [I, List.getElem_replicate]
      have hidx : ∀ i : Fin x.m, ∃ a : Fin n, V.getD a.1 0 = g i := fun i => by
        have hmemV : g i ∈ V := (hV_mem _).mpr (hSV _ (hg i))
        rcases List.mem_iff_getElem.mp hmemV with ⟨a, ha, hVa⟩
        exact ⟨⟨a, ha⟩, by rwa [List.getD_eq_getElem _ _ ha]⟩
      let σ : ∀ i : Fin I.numVars, Fin I.domSizes[i.1] := fun i =>
        let a := (hidx ⟨i.1, hnum ▸ i.2⟩).choose
        ⟨a.1, by rw [hdom i]; exact a.2⟩
      refine ⟨σ, satisfies_toTwoCSP_iff.mpr fun c hc h₁ h₂ => ?_⟩
      simp only [I, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at hc
      rcases hc with ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩
      dsimp only
      have ha1 : (σ ⟨i, h₁⟩).1 < n := by rw [← hdom ⟨i, h₁⟩]; exact (σ ⟨i, h₁⟩).2
      have ha2 : (σ ⟨j, h₂⟩).1 < n := by rw [← hdom ⟨j, h₂⟩]; exact (σ ⟨j, h₂⟩).2
      refine (hrel_mem _ _).mpr ⟨ha1, ha2, ?_⟩
      have hgi : V.getD (σ ⟨i, h₁⟩).1 0 = g ⟨i, hi⟩ := (hidx ⟨i, hi⟩).choose_spec
      have hgj : V.getD (σ ⟨j, h₂⟩).1 0 = g ⟨j, hj⟩ := (hidx ⟨j, hj⟩).choose_spec
      rw [hgi, hgj]
      exact hclq (hg ⟨i, hi⟩) (hg ⟨j, hj⟩) (fun heq => hij.ne (congrArg Fin.val (g.injective heq)))
  · constructor
    · intro hsat; exact absurd hsat not_isSatisfiable_unsatInstance
    · rintro ⟨S, hSV, hclq, hcard⟩
      have hle := Graph.le_card_of_mem_Clique (mem_Clique_iff.mpr ⟨S, hSV, hclq, hcard⟩)
      rw [hcardV] at hle
      exact absurd hle hmn

/-- `FinTwoCSP.ofClique` is computable in polynomial time. -/
theorem computableInPolyTime_ofClique :
    ComputableInPolyTime ofClique encCliqueInstance encFinTwoCSP := by
  have hV : ComputableInPolyTime (fun x : CliqueInstance => x.graph.distinctVertices)
      encCliqueInstance (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp (by fun_prop)
  have hn : ComputableInPolyTime (fun x : CliqueInstance => x.graph.distinctVertices.length)
      encCliqueInstance encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hV
  have hcond : ComputableInPolyTime
      (fun x : CliqueInstance => decide (x.m ≤ x.graph.distinctVertices.length))
      encCliqueInstance encBool :=
    ComputableInPolyTime.binary_le' (by fun_prop)
      (ComputableInPolyTime.unary_to_binary.comp hn)
  have hk : ComputableInPolyTime
      (fun x : CliqueInstance => min x.graph.distinctVertices.length x.m)
      encCliqueInstance encUnary :=
    ComputableInPolyTime.binary_min_unary' hn (by fun_prop)
  have hrel : ComputableInPolyTime
      (fun x : CliqueInstance =>
        let V := x.graph.distinctVertices
        let n := V.length
        (List.range n).flatMap fun a =>
          ((List.range n).filter fun b => x.graph.adjBool (V.getD a 0) (V.getD b 0)).map
            fun b => (a, b))
      encCliqueInstance (encList (encPair encUnary encUnary)) := by
    refine ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn) ?_
    have hflt : ComputableInPolyTime
        (fun p : CliqueInstance × ℕ =>
          (List.range p.1.graph.distinctVertices.length).filter fun b =>
            p.1.graph.adjBool (p.1.graph.distinctVertices.getD p.2 0)
              (p.1.graph.distinctVertices.getD b 0))
        (encPair encCliqueInstance encUnary) (encList encUnary) := by
      refine ComputableInPolyTime.filterWithInput
        (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _))) ?_
      have hG : ComputableInPolyTime (fun q : (CliqueInstance × ℕ) × ℕ => q.1.1.graph)
          (encPair (encPair encCliqueInstance encUnary) encUnary) encGraph := by fun_prop
      have hVa : ComputableInPolyTime
          (fun q : (CliqueInstance × ℕ) × ℕ => q.1.1.graph.distinctVertices.getD q.1.2 0)
          (encPair (encPair encCliqueInstance encUnary) encUnary) encNat :=
        ComputableInPolyTime.listGetDWithInput
          (hV.comp ((ComputableInPolyTime.fst _ _).fst'))
          ((ComputableInPolyTime.fst _ _).snd') 0
      have hVb : ComputableInPolyTime
          (fun q : (CliqueInstance × ℕ) × ℕ => q.1.1.graph.distinctVertices.getD q.2 0)
          (encPair (encPair encCliqueInstance encUnary) encUnary) encNat :=
        ComputableInPolyTime.listGetDWithInput
          (hV.comp ((ComputableInPolyTime.fst _ _).fst'))
          (ComputableInPolyTime.snd _ _) 0
      exact Graph.computableInPolyTime_adjBool_comp hG hVa hVb
    refine ComputableInPolyTime.mapWithInput hflt ?_
    exact (ComputableInPolyTime.fst _ _).snd'.prod (ComputableInPolyTime.snd _ _)
  have hcons : ComputableInPolyTime
      (fun x : CliqueInstance =>
        let V := x.graph.distinctVertices
        let n := V.length
        let k := min n x.m
        let rel := (List.range n).flatMap fun a =>
          ((List.range n).filter fun b => x.graph.adjBool (V.getD a 0) (V.getD b 0)).map
            fun b => (a, b)
        (List.range k).flatMap fun i =>
          ((List.range k).filter fun j => decide (i < j)).map fun j =>
            (⟨i, j, rel⟩ : FinTwoCSPConstraint))
      encCliqueInstance (encList encFinTwoCSPConstraint) := by
    refine ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hk) ?_
    have hflt : ComputableInPolyTime
        (fun p : CliqueInstance × ℕ =>
          (List.range (min p.1.graph.distinctVertices.length p.1.m)).filter fun j =>
            decide (p.2 < j))
        (encPair encCliqueInstance encUnary) (encList encUnary) := by
      refine ComputableInPolyTime.filterWithInput
        (ComputableInPolyTime.range.comp (hk.comp (ComputableInPolyTime.fst _ _))) ?_
      exact ComputableInPolyTime.unary_lt.comp
        ((ComputableInPolyTime.fst _ _).snd'.prod (ComputableInPolyTime.snd _ _))
    refine ComputableInPolyTime.mapWithInput hflt ?_
    exact encFinTwoCSPConstraint_mk_polyTime
      ((ComputableInPolyTime.fst _ _).snd')
      (ComputableInPolyTime.snd _ _)
      (hrel.comp ((ComputableInPolyTime.fst _ _).fst'))
  have hbranch : ComputableInPolyTime
      (fun x : CliqueInstance =>
        let V := x.graph.distinctVertices
        let n := V.length
        let k := min n x.m
        let rel := (List.range n).flatMap fun a =>
          ((List.range n).filter fun b => x.graph.adjBool (V.getD a 0) (V.getD b 0)).map
            fun b => (a, b)
        let constraints := (List.range k).flatMap fun i =>
          ((List.range k).filter fun j => decide (i < j)).map fun j => ⟨i, j, rel⟩
        (⟨List.replicate k n, constraints⟩ : FinTwoCSP))
      encCliqueInstance encFinTwoCSP :=
    encFinTwoCSP_mk_polyTime (ComputableInPolyTime.replicate hk hn) hcons
  have hres := ComputableInPolyTime.ite hcond hbranch (ComputableInPolyTime.const unsatInstance)
  have hfun : (fun x : CliqueInstance =>
      if decide (x.m ≤ x.graph.distinctVertices.length) = true then
        let V := x.graph.distinctVertices
        let n := V.length
        let k := min n x.m
        let rel := (List.range n).flatMap fun a =>
          ((List.range n).filter fun b => x.graph.adjBool (V.getD a 0) (V.getD b 0)).map
            fun b => (a, b)
        let constraints := (List.range k).flatMap fun i =>
          ((List.range k).filter fun j => decide (i < j)).map fun j => ⟨i, j, rel⟩
        (⟨List.replicate k n, constraints⟩ : FinTwoCSP)
      else unsatInstance) = ofClique := funext fun x => by
    unfold ofClique
    simp only [decide_eq_true_eq]
  rwa [← hfun]

/-- `Cslib.Complexity.Clique` fpt-reduces to `FinTwoCSP.SatisfiableSet`. -/
theorem fptReducible_clique_finTwoCSP :
    FPTReducible encCliqueInstance encFinTwoCSP (·.m) FinTwoCSP.numVars
      Clique SatisfiableSet :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_ofClique
    (h := fun k => k + 2) ofClique_numVars_le fun x => (ofClique_isSatisfiable_iff x).symm

/-- **`FinTwoCSP.SatisfiableSet` is `W[1]`-hard.** -/
theorem finTwoCSP_wHard :
    WHard 1 encFinTwoCSP FinTwoCSP.numVars SatisfiableSet :=
  Clique_wHard.trans fptReducible_clique_finTwoCSP

/-- **`W[1] = FPT` holds across all problems iff `FinTwoCSP.SatisfiableSet ∈ FPT`.** -/
theorem W_one_eq_FPT_iff_finTwoCSP :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 1 enc κ = FPT enc κ) ↔
      SatisfiableSet ∈ FPT encFinTwoCSP FinTwoCSP.numVars :=
  W_one_eq_FPT_iff.trans
    ⟨fptReducible_finTwoCSP_clique.mem_FPT, fptReducible_clique_finTwoCSP.mem_FPT⟩

end FinTwoCSP

end Cslib.Complexity
