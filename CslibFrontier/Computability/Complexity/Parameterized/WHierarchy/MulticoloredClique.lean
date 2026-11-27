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
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.TwoCSP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Card

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Multicolored `k`-Clique and `W[1]`-Completeness

Canonical framed unary carrier (`MulticoloredCliqueInstance`, `encMulticoloredClique`) for
`k`-partite multicolored clique instances, together with polynomial-time fpt-reductions to and
from `FinTwoCSP`, establishing `W[1]`-completeness.

## Main definitions

* `Cslib.Complexity.MulticoloredCliqueInstance`, `Cslib.Complexity.encMulticoloredClique`.
* `Cslib.Complexity.MulticoloredCliqueInstance.toSimpleGraph`,
  `Cslib.Complexity.MulticoloredCliqueInstance.HasMulticoloredClique`,
  `Cslib.Complexity.MulticoloredCliqueInstance.HasCliqueOfCard`,
  `Cslib.Complexity.MulticoloredCliqueInstance.Language`.
* `Cslib.Complexity.MulticoloredCliqueInstance.toFinTwoCSP`,
  `Cslib.Complexity.MulticoloredCliqueInstance.ofFinTwoCSP`.

## Main results

* `Cslib.Complexity.MulticoloredCliqueInstance.hasMulticoloredClique_iff_hasCliqueOfCard`,
  `Cslib.Complexity.MulticoloredCliqueInstance.not_hasCliqueOfCard_iff_cliqueNum_lt`.
* `Cslib.Complexity.fptReducible_multicoloredClique_finTwoCSP`,
  `Cslib.Complexity.fptReducible_finTwoCSP_multicoloredClique`,
  `Cslib.Complexity.multicoloredClique_wHard`,
  `Cslib.Complexity.W_one_eq_FPT_iff_multicoloredClique`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Canonical encoded carrier for multicolored `k`-clique instances: a `k`-partite graph with color
classes of cardinalities `partSizes`, and inter-color edge list `edges` where each entry
`((i, u), (j, v))` connects vertex `u` in color `i` to vertex `v` in color `j`. -/
@[ext]
structure MulticoloredCliqueInstance where
  /-- Cardinalities of the color classes `0, …, partSizes.length - 1`. -/
  partSizes : List ℕ
  /-- Inter-color edges `((i, u), (j, v))`. -/
  edges : List ((ℕ × ℕ) × (ℕ × ℕ))
deriving DecidableEq, Repr

/-- Framed unary encoding of `MulticoloredCliqueInstance`. -/
enc_structure encMulticoloredClique : MulticoloredCliqueInstance where
  partSizes : (encList encUnary),
  edges : (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))

attribute [fun_prop] encMulticoloredClique_partSizes_polyTime
  encMulticoloredClique_edges_polyTime encMulticoloredClique_mk_polyTime

namespace MulticoloredCliqueInstance

/-- Number of color classes `k = G.partSizes.length`. -/
@[expose]
def numColors (G : MulticoloredCliqueInstance) : ℕ := G.partSizes.length

/-- Disjoint-union vertex type `Σ i : Fin G.numColors, Fin G.partSizes[i]` of `G`. -/
abbrev Vertex (G : MulticoloredCliqueInstance) : Type :=
  Σ i : Fin G.numColors, Fin G.partSizes[i.1]

/-- Total number of vertices `G.partSizes.sum`. -/
@[expose]
def totalVertices (G : MulticoloredCliqueInstance) : ℕ := G.partSizes.sum

/-- Underlying `k`-partite `SimpleGraph G.Vertex`: two vertices from distinct color classes are
adjacent iff an edge between them appears in `G.edges` in either orientation. -/
@[expose]
def toSimpleGraph (G : MulticoloredCliqueInstance) : SimpleGraph G.Vertex where
  Adj x y := x.1 ≠ y.1 ∧
    ((((x.1 : ℕ), (x.2 : ℕ)), ((y.1 : ℕ), (y.2 : ℕ))) ∈ G.edges ∨
      (((y.1 : ℕ), (y.2 : ℕ)), ((x.1 : ℕ), (x.2 : ℕ))) ∈ G.edges)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Decidable adjacency on `G.toSimpleGraph`. -/
instance instDecidableRelToSimpleGraphAdj (G : MulticoloredCliqueInstance) :
    DecidableRel G.toSimpleGraph.Adj := fun x y =>
  inferInstanceAs (Decidable (x.1 ≠ y.1 ∧
    ((((x.1 : ℕ), (x.2 : ℕ)), ((y.1 : ℕ), (y.2 : ℕ))) ∈ G.edges ∨
      (((y.1 : ℕ), (y.2 : ℕ)), ((x.1 : ℕ), (x.2 : ℕ))) ∈ G.edges)))

/-- Every color class `{v : G.Vertex | v.1 = i}` is an independent set in `G.toSimpleGraph`. -/
theorem isIndepSet_colorClass (G : MulticoloredCliqueInstance) (i : Fin G.numColors) :
    G.toSimpleGraph.IsIndepSet {v : G.Vertex | v.1 = i} := by
  intro x hx y hy _ hadj
  rw [Set.mem_ofPred_eq] at hx hy
  exact hadj.1 (hx.trans hy.symm)

/-- A choice tuple `c : ∀ i, Fin G.partSizes[i]` is a multicolored `k`-clique if every pair of
strictly ordered color classes `i < j` is adjacent in `G.toSimpleGraph`. -/
@[expose]
def IsMulticoloredClique (G : MulticoloredCliqueInstance)
    (c : ∀ i : Fin G.numColors, Fin G.partSizes[i.1]) : Prop :=
  ∀ (i j : Fin G.numColors), i < j → G.toSimpleGraph.Adj ⟨i, c i⟩ ⟨j, c j⟩

/-- Existence of a multicolored `k`-clique in `G`. -/
@[expose]
def HasMulticoloredClique (G : MulticoloredCliqueInstance) : Prop :=
  ∃ c : ∀ i : Fin G.numColors, Fin G.partSizes[i.1], G.IsMulticoloredClique c

/-- Decision problem of multicolored `k`-clique instances admitting a multicolored `k`-clique. -/
@[expose]
def Language : Set MulticoloredCliqueInstance := {G | G.HasMulticoloredClique}

/-- Existence of a clique of exact cardinality `s` in `G.toSimpleGraph`. -/
@[expose]
def HasCliqueOfCard (G : MulticoloredCliqueInstance) (s : ℕ) : Prop :=
  ∃ S : Finset G.Vertex, G.toSimpleGraph.IsNClique s S

private lemma injOn_fst_of_isClique {G : MulticoloredCliqueInstance} {S : Finset G.Vertex}
    (hS : G.toSimpleGraph.IsClique (S : Set G.Vertex)) :
    Set.InjOn Sigma.fst (S : Set G.Vertex) :=
  fun x hx y hy hcol => by
    by_contra hne
    exact G.isIndepSet_colorClass x.1 rfl hcol.symm hne (hS hx hy hne)

/-- Every clique `S` in `G.toSimpleGraph` contains at most one vertex per color class, so
`S.card ≤ G.numColors`. -/
theorem card_le_numColors_of_isClique (G : MulticoloredCliqueInstance) {S : Finset G.Vertex}
    (hS : G.toSimpleGraph.IsClique (S : Set G.Vertex)) : S.card ≤ G.numColors :=
  (Finset.card_image_of_injOn (injOn_fst_of_isClique hS)).symm.le.trans
    ((Finset.card_le_univ _).trans (Fintype.card_fin G.numColors).le)

/-- The clique number of `G.toSimpleGraph` is at most `G.numColors`. -/
theorem cliqueNum_le_numColors (G : MulticoloredCliqueInstance) :
    G.toSimpleGraph.cliqueNum ≤ G.numColors := by
  rcases G.toSimpleGraph.exists_isNClique_cliqueNum with ⟨S, hS⟩
  exact hS.card_eq ▸ G.card_le_numColors_of_isClique hS.isClique

/-- Downward monotonicity of `HasCliqueOfCard`. -/
theorem hasCliqueOfCard_mono (G : MulticoloredCliqueInstance) {s₁ s₂ : ℕ}
    (h : G.HasCliqueOfCard s₂) (hs : s₁ ≤ s₂) : G.HasCliqueOfCard s₁ := by
  rcases h with ⟨S, hS⟩
  obtain ⟨T, hTS, hcard⟩ := Finset.exists_subset_card_eq (hS.card_eq ▸ hs)
  exact ⟨T, hS.isClique.subset (Finset.coe_subset.mpr hTS), hcard⟩

/-- A `k`-partite graph `G` has a multicolored `k`-clique iff `G.toSimpleGraph` has a clique of
cardinality `G.numColors`. -/
theorem hasMulticoloredClique_iff_hasCliqueOfCard (G : MulticoloredCliqueInstance) :
    G.HasMulticoloredClique ↔ G.HasCliqueOfCard G.numColors := by
  constructor
  · rintro ⟨c, hc⟩
    let emb : Fin G.numColors ↪ G.Vertex := ⟨fun i => ⟨i, c i⟩, fun _ _ h => (Sigma.mk.inj h).1⟩
    refine ⟨Finset.univ.map emb, fun x hx y hy hne => ?_, by simp⟩
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨j, -, rfl⟩
    rcases lt_or_gt_of_ne (fun h : i = j => hne (congrArg emb h)) with hij | hji
    · exact hc i j hij
    · exact (hc j i hji).symm
  · rintro ⟨S, hS⟩
    have himg : S.image Sigma.fst = Finset.univ := Finset.eq_univ_of_card _
      (by rw [Finset.card_image_of_injOn (injOn_fst_of_isClique hS.isClique),
              hS.card_eq, Fintype.card_fin])
    have hex : ∀ i : Fin G.numColors, ∃ u, (⟨i, u⟩ : G.Vertex) ∈ S := fun i => by
      rcases Finset.mem_image.mp (himg ▸ Finset.mem_univ i) with ⟨⟨j, u⟩, hmem, hjeq⟩
      dsimp only at hjeq; subst hjeq; exact ⟨u, hmem⟩
    exact ⟨fun i => (hex i).choose, fun i j hij =>
      hS.isClique (hex i).choose_spec (hex j).choose_spec fun h => hij.ne (Sigma.mk.inj h).1⟩

/-- For `1 ≤ s`, `G` has no clique of size `s` iff `G.toSimpleGraph.cliqueNum < s`. -/
theorem not_hasCliqueOfCard_iff_cliqueNum_lt (G : MulticoloredCliqueInstance) {s : ℕ}
    (hs : 1 ≤ s) : ¬ G.HasCliqueOfCard s ↔ G.toSimpleGraph.cliqueNum < s := by
  rw [Nat.lt_iff_le_pred hs]
  refine ⟨fun hno => ?_, fun hle ⟨T, hT⟩ => ?_⟩
  · rcases G.toSimpleGraph.exists_isNClique_cliqueNum with ⟨T, hT⟩
    by_contra! hgt
    exact hno (G.hasCliqueOfCard_mono ⟨T, hT⟩ (by omega))
  · have := hT.isClique.card_le_cliqueNum
    have := hT.card_eq
    omega

/-- Polynomial-time conversion from `MulticoloredCliqueInstance` to `FinTwoCSP` preserving
`numColors` identically. -/
@[expose]
def toFinTwoCSP (G : MulticoloredCliqueInstance) : FinTwoCSP :=
  let k := G.numColors
  let edgeRel (i j : ℕ) : List (ℕ × ℕ) :=
    (List.range (G.partSizes.getD i 0)).flatMap fun u =>
      ((List.range (G.partSizes.getD j 0)).filter fun v =>
        G.edges.any fun e =>
          (e.1.1 == i && e.1.2 == u && e.2.1 == j && e.2.2 == v) ||
            (e.1.1 == j && e.1.2 == v && e.2.1 == i && e.2.2 == u)).map fun v => (u, v)
  let constraints : List FinTwoCSPConstraint :=
    (List.range k).flatMap fun i =>
      ((List.range k).filter fun j => decide (i < j)).map fun j => ⟨i, j, edgeRel i j⟩
  ⟨G.partSizes, constraints⟩

theorem toFinTwoCSP_numVars (G : MulticoloredCliqueInstance) :
    G.toFinTwoCSP.numVars = G.numColors := rfl

theorem toFinTwoCSP_isSatisfiable_iff (G : MulticoloredCliqueInstance) :
    G.toFinTwoCSP.IsSatisfiable ↔ G.HasMulticoloredClique := by
  have hmem : ∀ (i j : Fin G.numColors) (u : Fin G.partSizes[i.1]) (v : Fin G.partSizes[j.1]),
      i < j →
      (((u.1, v.1) ∈ (List.range (G.partSizes.getD i.1 0)).flatMap fun u' =>
        ((List.range (G.partSizes.getD j.1 0)).filter fun v' =>
          G.edges.any fun e =>
            (e.1.1 == i.1 && e.1.2 == u' && e.2.1 == j.1 && e.2.2 == v') ||
              (e.1.1 == j.1 && e.1.2 == v' && e.2.1 == i.1 && e.2.2 == u')).map
          fun v' => (u', v'))
        ↔ G.toSimpleGraph.Adj ⟨i, u⟩ ⟨j, v⟩) := by
    intro i j u v hij
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, List.any_eq_true,
      Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq, toSimpleGraph]
    constructor
    · rintro ⟨u', -, v', ⟨-, ⟨e, he, h⟩⟩, rfl, rfl⟩
      refine ⟨hij.ne, ?_⟩
      rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · left; exact (show e = ((i.1, u.1), (j.1, v.1)) from by
          rcases e with ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp_all) ▸ he
      · right; exact (show e = ((j.1, v.1), (i.1, u.1)) from by
          rcases e with ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp_all) ▸ he
    · rintro ⟨-, h⟩
      refine ⟨u.1, by rw [List.getD_eq_getElem _ _ i.2]; exact u.2,
        v.1, ⟨by rw [List.getD_eq_getElem _ _ j.2]; exact v.2, ?_⟩, rfl, rfl⟩
      rcases h with h | h
      · exact ⟨_, h, Or.inl ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩⟩
      · exact ⟨_, h, Or.inr ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩⟩
  constructor
  · rintro ⟨σ, hσ⟩
    have hsat := FinTwoCSP.satisfies_toTwoCSP_iff.mp hσ
    refine ⟨σ, fun i j hij => ?_⟩
    have hc : ⟨i.1, j.1,
        (List.range (G.partSizes.getD i.1 0)).flatMap fun u' =>
          ((List.range (G.partSizes.getD j.1 0)).filter fun v' =>
            G.edges.any fun e =>
              (e.1.1 == i.1 && e.1.2 == u' && e.2.1 == j.1 && e.2.2 == v') ||
                (e.1.1 == j.1 && e.1.2 == v' && e.2.1 == i.1 && e.2.2 == u')).map
            fun v' => (u', v')⟩ ∈ G.toFinTwoCSP.constraints := by
      simp only [toFinTwoCSP, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq]
      exact ⟨i.1, i.2, j.1, ⟨j.2, hij⟩, rfl⟩
    exact (hmem i j (σ i) (σ j) hij).mp (hsat _ hc i.2 j.2)
  · rintro ⟨c, hc⟩
    refine ⟨c, FinTwoCSP.satisfies_toTwoCSP_iff.mpr fun con hcon h1 h2 => ?_⟩
    simp only [toFinTwoCSP, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hcon
    rcases hcon with ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩
    exact (hmem ⟨i, hi⟩ ⟨j, hj⟩ (c ⟨i, hi⟩) (c ⟨j, hj⟩) hij).mpr (hc ⟨i, hi⟩ ⟨j, hj⟩ hij)

/-- `MulticoloredCliqueInstance.toFinTwoCSP` is computable in polynomial time. -/
theorem computableInPolyTime_toFinTwoCSP :
    ComputableInPolyTime toFinTwoCSP encMulticoloredClique encFinTwoCSP := by
  unfold toFinTwoCSP numColors
  dsimp only
  fun_prop

/-- Polynomial-time conversion from `FinTwoCSP` to `MulticoloredCliqueInstance`, preserving
`numVars` identically. -/
@[expose]
def ofFinTwoCSP (I : FinTwoCSP) : MulticoloredCliqueInstance :=
  let k := I.numVars
  let selfOk (x a : ℕ) : Bool :=
    I.constraints.all fun c =>
      !(c.fst == x && c.snd == x) || c.rel.any fun p => p.1 == a && p.2 == a
  let pairOk (x a y b : ℕ) : Bool :=
    I.constraints.all fun c =>
      (!(c.fst == x && c.snd == y) || c.rel.any fun p => p.1 == a && p.2 == b) &&
        (!(c.fst == y && c.snd == x) || c.rel.any fun p => p.1 == b && p.2 == a)
  if k == 1 then
    if (List.range (I.domSizes.getD 0 0)).any (selfOk 0) then ⟨[1], []⟩ else ⟨[0], []⟩
  else
    let partSizes := (List.range k).map fun x => I.domSizes.getD x 0
    let edges := (List.range k).flatMap fun x =>
      ((List.range k).filter fun y => decide (x < y)).flatMap fun y =>
        ((List.range (I.domSizes.getD x 0)).filter fun a => selfOk x a).flatMap fun a =>
          ((List.range (I.domSizes.getD y 0)).filter fun b => selfOk y b && pairOk x a y b).map
            fun b => ((x, a), (y, b))
    ⟨partSizes, edges⟩

theorem ofFinTwoCSP_numColors (I : FinTwoCSP) : (ofFinTwoCSP I).numColors = I.numVars := by
  unfold ofFinTwoCSP numColors
  dsimp only
  split_ifs with h1 h2
  · simp [beq_iff_eq.mp h1]
  · simp [beq_iff_eq.mp h1]
  · simp

theorem ofFinTwoCSP_hasMulticoloredClique_iff (I : FinTwoCSP) :
    (ofFinTwoCSP I).HasMulticoloredClique ↔ I.IsSatisfiable := by
  by_cases hk1 : I.numVars = 1
  · unfold ofFinTwoCSP
    have hk1' : I.domSizes.length = 1 := hk1
    simp only [hk1, beq_self_eq_true, ↓reduceIte]
    have hdom0 : I.domSizes.getD 0 0 = I.domSizes[0]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have hself : ((List.range (I.domSizes.getD 0 0)).any fun a =>
        I.constraints.all fun c => !(c.fst == 0 && c.snd == 0) ||
          c.rel.any fun p => p.1 == a && p.2 == a) = true ↔ I.IsSatisfiable := by
      simp only [List.any_eq_true, List.mem_range, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_true, beq_eq_false_iff_ne,
        beq_iff_eq, hdom0]
      constructor
      · rintro ⟨a, ha, hall⟩
        refine ⟨fun x => ⟨a, by
            have hx : x = ⟨0, by omega⟩ := Fin.ext (by have := x.2; omega)
            rw [hx]; exact ha⟩,
          FinTwoCSP.satisfies_toTwoCSP_iff.mpr fun c hc h1 h2 => ?_⟩
        have h10 : c.fst = 0 := by omega
        have h20 : c.snd = 0 := by omega
        rcases hall c hc with hne | ⟨⟨p1, p2⟩, hmem, hp1, hp2⟩
        · rcases hne with hne | hne <;> [exact absurd h10 hne; exact absurd h20 hne]
        · dsimp only at hp1 hp2; subst hp1; subst hp2; exact hmem
      · rintro ⟨σ, hσ⟩
        have hsat := FinTwoCSP.satisfies_toTwoCSP_iff.mp hσ
        refine ⟨(σ ⟨0, by omega⟩).1, (σ ⟨0, by omega⟩).2, fun c hc => ?_⟩
        by_cases h1 : c.fst = 0
        · by_cases h2 : c.snd = 0
          · right
            refine ⟨((σ ⟨0, by omega⟩).1, (σ ⟨0, by omega⟩).1), ?_, rfl, rfl⟩
            have h := hsat c hc (by omega) (by omega)
            rwa [show (⟨c.fst, _⟩ : Fin I.numVars) = ⟨0, by omega⟩ from Fin.ext h1,
              show (⟨c.snd, _⟩ : Fin I.numVars) = ⟨0, by omega⟩ from Fin.ext h2] at h
          · exact Or.inl (Or.inr h2)
        · exact Or.inl (Or.inl h1)
    split_ifs with h
    · refine iff_of_true ?_ (hself.mp h)
      exact ⟨fun _ => ⟨0, by simp⟩, fun i j hij => by
        exfalso; have hi := i.2; have hj := j.2; simp [numColors] at hi hj; omega⟩
    · refine iff_of_false ?_ (mt hself.mpr h)
      rintro ⟨c, -⟩
      exact Fin.elim0 (c ⟨0, by decide⟩)
  · have hbeq : (I.numVars == 1) = false := beq_false_of_ne hk1
    have hnum : (ofFinTwoCSP I).numColors = I.numVars := ofFinTwoCSP_numColors I
    have hpart_eq : (ofFinTwoCSP I).partSizes =
        (List.range I.numVars).map fun x => I.domSizes.getD x 0 := by
      unfold ofFinTwoCSP; dsimp only; rw [hbeq]; rfl
    have hpart : ∀ x : Fin (ofFinTwoCSP I).numColors,
        (ofFinTwoCSP I).partSizes[x.1] =
          I.domSizes[x.1]'(by simpa [hnum] using x.2) := by
      intro x
      have hx : x.1 < I.numVars := by simpa [hnum] using x.2
      simp only [hpart_eq, List.getElem_map, List.getElem_range]
      exact List.getD_eq_getElem _ _ hx
    have hedge : ∀ (x y : Fin I.numVars) (a : Fin I.domSizes[x.1]) (b : Fin I.domSizes[y.1]),
        x < y →
        ((((x.1, a.1), (y.1, b.1)) ∈ (ofFinTwoCSP I).edges ∨
          ((y.1, b.1), (x.1, a.1)) ∈ (ofFinTwoCSP I).edges) ↔
        (∀ c ∈ I.constraints, c.fst = x.1 → c.snd = x.1 → (a.1, a.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = y.1 → c.snd = y.1 → (b.1, b.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = x.1 → c.snd = y.1 → (a.1, b.1) ∈ c.rel) ∧
        (∀ c ∈ I.constraints, c.fst = y.1 → c.snd = x.1 → (b.1, a.1) ∈ c.rel)) := by
      intro x y a b hxy
      have hmem_one : ∀ (u v : Fin I.numVars) (p : Fin I.domSizes[u.1]) (q : Fin I.domSizes[v.1]),
          (((u.1, p.1), (v.1, q.1)) ∈ (ofFinTwoCSP I).edges ↔
            u < v ∧
            (∀ c ∈ I.constraints, c.fst = u.1 → c.snd = u.1 → (p.1, p.1) ∈ c.rel) ∧
            (∀ c ∈ I.constraints, c.fst = v.1 → c.snd = v.1 → (q.1, q.1) ∈ c.rel) ∧
            (∀ c ∈ I.constraints, c.fst = u.1 → c.snd = v.1 → (p.1, q.1) ∈ c.rel) ∧
            (∀ c ∈ I.constraints, c.fst = v.1 → c.snd = u.1 → (q.1, p.1) ∈ c.rel)) := by
        intro u v p q
        simp only [ofFinTwoCSP, hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
          List.mem_map, List.mem_filter, List.mem_range, List.all_eq_true, List.any_eq_true,
          Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
          beq_eq_false_iff_ne, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨x', hx', y', ⟨hy', hlt⟩, a', ⟨ha', hself1⟩, b', ⟨hb', hself2, hpair⟩,
            ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
          refine ⟨hlt, fun c hc h1 h2 => ?_, fun c hc h1 h2 => ?_, fun c hc h1 h2 => ?_,
            fun c hc h1 h2 => ?_⟩
          · rcases hself1 c hc with hne | ⟨⟨p1, p2⟩, hm, hp1, hp2⟩
            · rcases hne with h | h <;> [exact absurd h1 h; exact absurd h2 h]
            · dsimp only at hp1 hp2; subst hp1; subst hp2; exact hm
          · rcases hself2 c hc with hne | ⟨⟨p1, p2⟩, hm, hp1, hp2⟩
            · rcases hne with h | h <;> [exact absurd h1 h; exact absurd h2 h]
            · dsimp only at hp1 hp2; subst hp1; subst hp2; exact hm
          · rcases (hpair c hc).1 with hne | ⟨⟨p1, p2⟩, hm, hp1, hp2⟩
            · rcases hne with h | h <;> [exact absurd h1 h; exact absurd h2 h]
            · dsimp only at hp1 hp2; subst hp1; subst hp2; exact hm
          · rcases (hpair c hc).2 with hne | ⟨⟨p1, p2⟩, hm, hp1, hp2⟩
            · rcases hne with h | h <;> [exact absurd h1 h; exact absurd h2 h]
            · dsimp only at hp1 hp2; subst hp1; subst hp2; exact hm
        · rintro ⟨hlt, hs1, hs2, hp1, hp2⟩
          refine ⟨u.1, u.2, v.1, ⟨v.2, hlt⟩,
            p.1, ⟨by rw [List.getD_eq_getElem _ _ u.2]; exact p.2, fun c hc => ?_⟩,
            q.1, ⟨by rw [List.getD_eq_getElem _ _ v.2]; exact q.2, fun c hc => ?_, fun c hc => ?_⟩,
            ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
          · by_cases h1 : c.fst = u.1
            · by_cases h2 : c.snd = u.1
              · exact Or.inr ⟨(p.1, p.1), hs1 c hc h1 h2, rfl, rfl⟩
              · exact Or.inl (Or.inr h2)
            · exact Or.inl (Or.inl h1)
          · by_cases h1 : c.fst = v.1
            · by_cases h2 : c.snd = v.1
              · exact Or.inr ⟨(q.1, q.1), hs2 c hc h1 h2, rfl, rfl⟩
              · exact Or.inl (Or.inr h2)
            · exact Or.inl (Or.inl h1)
          · refine ⟨?_, ?_⟩
            · by_cases h1 : c.fst = u.1
              · by_cases h2 : c.snd = v.1
                · exact Or.inr ⟨(p.1, q.1), hp1 c hc h1 h2, rfl, rfl⟩
                · exact Or.inl (Or.inr h2)
              · exact Or.inl (Or.inl h1)
            · by_cases h1 : c.fst = v.1
              · by_cases h2 : c.snd = u.1
                · exact Or.inr ⟨(q.1, p.1), hp2 c hc h1 h2, rfl, rfl⟩
                · exact Or.inl (Or.inr h2)
              · exact Or.inl (Or.inl h1)
      rw [hmem_one x y a b, hmem_one y x b a]
      exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd h.1 hxy.asymm),
        fun h => Or.inl ⟨hxy, h⟩⟩
    constructor
    · rintro ⟨c, hc⟩
      let σ : ∀ x : Fin I.numVars, Fin I.domSizes[x.1] := fun x =>
        let i : Fin (ofFinTwoCSP I).numColors := ⟨x.1, hnum.symm ▸ x.2⟩
        ⟨(c i).1, by rw [← hpart i]; exact (c i).2⟩
      refine ⟨σ, FinTwoCSP.satisfies_toTwoCSP_iff.mpr fun con hcon h1 h2 => ?_⟩
      by_cases h12 : con.fst = con.snd
      · have hk2 : 2 ≤ I.numVars := by omega
        have ⟨y, hy⟩ : ∃ y : Fin I.numVars, y ≠ ⟨con.fst, h1⟩ := by
          by_cases h0 : (⟨con.fst, h1⟩ : Fin I.numVars) = ⟨0, by omega⟩
          · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val (h.trans h0); simp at this⟩
          · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
        have hfst_eq : (⟨con.fst, h1⟩ : Fin I.numVars) = ⟨con.snd, h2⟩ := Fin.ext h12
        rcases lt_or_gt_of_ne hy with hlt | hgt
        · have hadj := hc ⟨y.1, hnum.symm ▸ y.2⟩ ⟨con.fst, hnum.symm ▸ h1⟩ hlt
          have h := (hedge y ⟨con.fst, h1⟩ (σ y) (σ ⟨con.fst, h1⟩) hlt).mp hadj.2
          rw [← hfst_eq]
          exact h.2.1 con hcon rfl h12.symm
        · have hadj := hc ⟨con.fst, hnum.symm ▸ h1⟩ ⟨y.1, hnum.symm ▸ y.2⟩ hgt
          have h := (hedge ⟨con.fst, h1⟩ y (σ ⟨con.fst, h1⟩) (σ y) hgt).mp hadj.2
          rw [← hfst_eq]
          exact h.1 con hcon rfl h12.symm
      · rcases lt_or_gt_of_ne h12 with hlt | hgt
        · have hlt' : (⟨con.fst, h1⟩ : Fin I.numVars) < ⟨con.snd, h2⟩ := hlt
          have hadj := hc ⟨con.fst, hnum.symm ▸ h1⟩ ⟨con.snd, hnum.symm ▸ h2⟩ hlt'
          exact ((hedge ⟨con.fst, h1⟩ ⟨con.snd, h2⟩ (σ ⟨con.fst, h1⟩) (σ ⟨con.snd, h2⟩) hlt').mp
            hadj.2).2.2.1 con hcon rfl rfl
        · have hgt' : (⟨con.snd, h2⟩ : Fin I.numVars) < ⟨con.fst, h1⟩ := hgt
          have hadj := hc ⟨con.snd, hnum.symm ▸ h2⟩ ⟨con.fst, hnum.symm ▸ h1⟩ hgt'
          exact ((hedge ⟨con.snd, h2⟩ ⟨con.fst, h1⟩ (σ ⟨con.snd, h2⟩) (σ ⟨con.fst, h1⟩) hgt').mp
            hadj.2).2.2.2 con hcon rfl rfl
    · rintro ⟨σ, hσ⟩
      have hsat := FinTwoCSP.satisfies_toTwoCSP_iff.mp hσ
      let c : ∀ i : Fin (ofFinTwoCSP I).numColors, Fin (ofFinTwoCSP I).partSizes[i.1] := fun i =>
        ⟨(σ ⟨i.1, hnum ▸ i.2⟩).1, by rw [hpart i]; exact (σ ⟨i.1, hnum ▸ i.2⟩).2⟩
      refine ⟨c, fun i j hij => ⟨hij.ne, ?_⟩⟩
      have hi : i.1 < I.numVars := hnum ▸ i.2
      have hj : j.1 < I.numVars := hnum ▸ j.2
      exact (hedge ⟨i.1, hi⟩ ⟨j.1, hj⟩ (σ ⟨i.1, hi⟩) (σ ⟨j.1, hj⟩) hij).mpr
        ⟨fun con hcon h1 h2 => by
            have h := hsat con hcon (h1.symm ▸ hi) (h2.symm ▸ hi)
            rwa [show (⟨con.fst, _⟩ : Fin I.numVars) = ⟨i.1, hi⟩ from Fin.ext h1,
              show (⟨con.snd, _⟩ : Fin I.numVars) = ⟨i.1, hi⟩ from Fin.ext h2] at h,
          fun con hcon h1 h2 => by
            have h := hsat con hcon (h1.symm ▸ hj) (h2.symm ▸ hj)
            rwa [show (⟨con.fst, _⟩ : Fin I.numVars) = ⟨j.1, hj⟩ from Fin.ext h1,
              show (⟨con.snd, _⟩ : Fin I.numVars) = ⟨j.1, hj⟩ from Fin.ext h2] at h,
          fun con hcon h1 h2 => by
            have h := hsat con hcon (h1.symm ▸ hi) (h2.symm ▸ hj)
            rwa [show (⟨con.fst, _⟩ : Fin I.numVars) = ⟨i.1, hi⟩ from Fin.ext h1,
              show (⟨con.snd, _⟩ : Fin I.numVars) = ⟨j.1, hj⟩ from Fin.ext h2] at h,
          fun con hcon h1 h2 => by
            have h := hsat con hcon (h1.symm ▸ hj) (h2.symm ▸ hi)
            rwa [show (⟨con.fst, _⟩ : Fin I.numVars) = ⟨j.1, hj⟩ from Fin.ext h1,
              show (⟨con.snd, _⟩ : Fin I.numVars) = ⟨i.1, hi⟩ from Fin.ext h2] at h⟩

/-- `MulticoloredCliqueInstance.ofFinTwoCSP` is computable in polynomial time. -/
theorem computableInPolyTime_ofFinTwoCSP :
    ComputableInPolyTime ofFinTwoCSP encFinTwoCSP encMulticoloredClique := by
  unfold ofFinTwoCSP
  dsimp only
  fun_prop

end MulticoloredCliqueInstance

/-- `MulticoloredCliqueInstance.Language` fpt-reduces to `FinTwoCSP.SatisfiableSet`. -/
theorem fptReducible_multicoloredClique_finTwoCSP :
    FPTReducible encMulticoloredClique encFinTwoCSP
      MulticoloredCliqueInstance.numColors FinTwoCSP.numVars
      MulticoloredCliqueInstance.Language FinTwoCSP.SatisfiableSet :=
  FPTReducible.of_computableInPolyTime MulticoloredCliqueInstance.computableInPolyTime_toFinTwoCSP
    (h := id) (fun _ => le_rfl) fun G =>
      (MulticoloredCliqueInstance.toFinTwoCSP_isSatisfiable_iff G).symm

/-- `FinTwoCSP.SatisfiableSet` fpt-reduces to `MulticoloredCliqueInstance.Language`. -/
theorem fptReducible_finTwoCSP_multicoloredClique :
    FPTReducible encFinTwoCSP encMulticoloredClique
      FinTwoCSP.numVars MulticoloredCliqueInstance.numColors
      FinTwoCSP.SatisfiableSet MulticoloredCliqueInstance.Language :=
  FPTReducible.of_computableInPolyTime MulticoloredCliqueInstance.computableInPolyTime_ofFinTwoCSP
    (h := id) (fun I => (MulticoloredCliqueInstance.ofFinTwoCSP_numColors I).le) fun I =>
      (MulticoloredCliqueInstance.ofFinTwoCSP_hasMulticoloredClique_iff I).symm

/-- **`MulticoloredCliqueInstance.Language` is `W[1]`-hard.** -/
theorem multicoloredClique_wHard :
    WHard 1 encMulticoloredClique MulticoloredCliqueInstance.numColors
      MulticoloredCliqueInstance.Language :=
  FinTwoCSP.finTwoCSP_wHard.trans fptReducible_finTwoCSP_multicoloredClique

/-- **`W[1] = FPT` iff `MulticoloredCliqueInstance.Language ∈ FPT`.** -/
theorem W_one_eq_FPT_iff_multicoloredClique :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 1 enc κ = FPT enc κ) ↔
      MulticoloredCliqueInstance.Language ∈
        FPT encMulticoloredClique MulticoloredCliqueInstance.numColors :=
  FinTwoCSP.W_one_eq_FPT_iff_finTwoCSP.trans
    ⟨fptReducible_multicoloredClique_finTwoCSP.mem_FPT,
      fptReducible_finTwoCSP_multicoloredClique.mem_FPT⟩

end Cslib.Complexity
