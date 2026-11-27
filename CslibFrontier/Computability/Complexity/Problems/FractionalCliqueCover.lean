/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fractional Clique Cover and NP-Hardness via 3-Coloring

Self-contained polynomial-time Karp reduction `ThreeColoring ≤ₚ FractionalCliqueCover`,
establishing NP-hardness of the fractional clique cover decision problem (equivalently,
fractional chromatic number on the complement graph).

Given a graph $G$ on $m \ge 1$ distinct vertices, the conflict-complement graph
$H = (G \mathbin{\square} K_3)^c$ on $3m$ vertices satisfies $\bar\chi_f(H) \le 3$ if and only if
$G$ is $3$-colorable.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A graph `G` admits a **Fractional Clique Cover** of total weight at most `t`: nonnegative
weights `w` on cliques of `G.induced` with `∑ w ≤ t` and `∑_{C ∋ v} w_C = 1` for every declared
vertex `v`. -/
def HasFractionalCliqueCover (G : Graph) (t : ℝ) : Prop :=
  ∃ w : Finset {v // v ∈ G.vertices} → ℝ,
    (∀ C, 0 ≤ w C) ∧
    (∀ C, w C ≠ 0 → G.induced.IsClique (C : Set {v // v ∈ G.vertices})) ∧
    (∑ C, w C ≤ t) ∧
    ∀ v : {v // v ∈ G.vertices}, (∑ C ∈ Finset.univ.filter (fun C => v ∈ C), w C) = 1

theorem hasFractionalCliqueCover_iff {G : Graph} {t : ℝ} :
    HasFractionalCliqueCover G t ↔
      ∃ w : Finset {v // v ∈ G.vertices} → ℝ,
        (∀ C, 0 ≤ w C) ∧
        (∀ C, w C ≠ 0 → G.induced.IsClique (C : Set {v // v ∈ G.vertices})) ∧
        (∑ C, w C ≤ t) ∧
        ∀ v : {v // v ∈ G.vertices}, (∑ C ∈ Finset.univ.filter (fun C => v ∈ C), w C) = 1 := by
  rfl

/-- Binary encoding of Fractional Clique Cover instances `(G, t)`. -/
abbrev encFractionalCliqueCover : Graph × ℚ ↪ List Bool :=
  encPair encGraph encRat

/-- **Fractional Clique Cover (FCC)** decision problem. -/
def FractionalCliqueCover : Set (Graph × ℚ) :=
  {x | 0 < x.2 ∧ HasFractionalCliqueCover x.1 (x.2 : ℝ)}

theorem mem_FractionalCliqueCover {x : Graph × ℚ} :
    x ∈ FractionalCliqueCover ↔ 0 < x.2 ∧ HasFractionalCliqueCover x.1 (x.2 : ℝ) := by
  rfl

/-- Conflict-complement graph $H = (G \mathbin{\square} K_3)^c$ on `3 * m` vertices (where
`m = G.distinctVertices.length`) for the Karp reduction `ThreeColoring ≤ₚ FCC`. -/
def threeColoringToFCCGraph (G : Graph) : Graph :=
  let vs := G.distinctVertices
  let m := vs.length
  if m = 0 then ⟨[0], []⟩
  else
    let verts := List.range (3 * m)
    let edges := (List.range m).flatMap fun i =>
      (List.range m).flatMap fun j =>
        if i = j then []
        else
          let u := vs.getD i 0
          let v := vs.getD j 0
          let adj := G.adjBool u v
          (List.range 3).flatMap fun c =>
            (List.range 3).flatMap fun c' =>
              if adj && decide (c = c') then []
              else [(3 * i + c, 3 * j + c')]
    ⟨verts, edges⟩

/-- Karp reduction `ThreeColoring ≤ₚ FractionalCliqueCover` mapping `G` to `(H, 3)`. -/
def threeColoringToFCC (G : Graph) : Graph × ℚ :=
  (threeColoringToFCCGraph G, 3)

@[simp]
theorem threeColoringToFCC_fst (G : Graph) :
    (threeColoringToFCC G).1 = threeColoringToFCCGraph G := by
  rfl

@[simp]
theorem threeColoringToFCC_snd (G : Graph) : (threeColoringToFCC G).2 = 3 := by
  rfl

theorem threeColoringToFCCGraph_distinctVertices_length_ge (G : Graph)
    (hm : G.distinctVertices.length ≠ 0) :
    3 ≤ (threeColoringToFCCGraph G).distinctVertices.length := by
  have hsub : (List.range (3 * G.distinctVertices.length)).toFinset ⊆
      (threeColoringToFCCGraph G).distinctVertices.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [Graph.mem_distinctVertices]
    simpa [threeColoringToFCCGraph, hm] using hx
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range,
    List.toFinset_card_of_nodup (Graph.nodup_distinctVertices _)] at h1
  have hm1 : 1 ≤ G.distinctVertices.length := Nat.pos_of_ne_zero hm
  omega

theorem computableInPolyTime_threeColoringToFCC :
    ComputableInPolyTime threeColoringToFCC encGraph encFractionalCliqueCover := by
  have h1 : ComputableInPolyTime threeColoringToFCCGraph encGraph encGraph := by
    unfold threeColoringToFCCGraph
    have hdv : ComputableInPolyTime Graph.distinctVertices encGraph (encList encNat) := by
      fun_prop
    have hlen : ComputableInPolyTime (fun G : Graph => G.distinctVertices.length)
        encGraph encUnary :=
      (ComputableInPolyTime.length_list encNat).comp hdv
    have hm0 : ComputableInPolyTime (fun G : Graph => decide (G.distinctVertices.length = 0))
        encGraph encBool := by fun_prop
    have hverts : ComputableInPolyTime (fun G : Graph => List.range (3 * G.distinctVertices.length))
        encGraph (encList encNat) := by
      have hu : ComputableInPolyTime
          (fun G : Graph => List.range (3 * G.distinctVertices.length))
          encGraph (encList encUnary) := by fun_prop
      simpa using (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hu
    have hedges : ComputableInPolyTime
        (fun G : Graph =>
          (List.range G.distinctVertices.length).flatMap fun i =>
            (List.range G.distinctVertices.length).flatMap fun j =>
              if i = j then []
              else
                let u := G.distinctVertices.getD i 0
                let v := G.distinctVertices.getD j 0
                let adj := G.adjBool u v
                (List.range 3).flatMap fun c =>
                  (List.range 3).flatMap fun c' =>
                    if adj && decide (c = c') then []
                    else [(3 * i + c, 3 * j + c')])
        encGraph (encList (encPair encNat encNat)) := by
      have hinner1 : ComputableInPolyTime
          (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) =>
            if p.1.1.1.1.adjBool (p.1.1.1.1.distinctVertices.getD p.1.1.1.2 0)
                (p.1.1.1.1.distinctVertices.getD p.1.1.2 0) && decide (p.1.2 = p.2)
            then ([] : List (ℕ × ℕ))
            else [(3 * p.1.1.1.2 + p.1.2, 3 * p.1.1.2 + p.2)])
          (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
          (encList (encPair encNat encNat)) := by
        have hget1 : ComputableInPolyTime
            (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) =>
              p.1.1.1.1.distinctVertices.getD p.1.1.1.2 0)
            (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
            encNat :=
          ComputableInPolyTime.listGetDWithInput (hdv.comp (by fun_prop)) (by fun_prop) 0
        have hget2 : ComputableInPolyTime
            (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) =>
              p.1.1.1.1.distinctVertices.getD p.1.1.2 0)
            (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
            encNat :=
          ComputableInPolyTime.listGetDWithInput (hdv.comp (by fun_prop)) (by fun_prop) 0
        have hadj : ComputableInPolyTime
            (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) =>
              p.1.1.1.1.adjBool (p.1.1.1.1.distinctVertices.getD p.1.1.1.2 0)
                (p.1.1.1.1.distinctVertices.getD p.1.1.2 0))
            (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
            encBool :=
          Graph.computableInPolyTime_adjBool_comp (by fun_prop) hget1 hget2
        have hcond : ComputableInPolyTime
            (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) =>
              p.1.1.1.1.adjBool (p.1.1.1.1.distinctVertices.getD p.1.1.1.2 0)
                (p.1.1.1.1.distinctVertices.getD p.1.1.2 0) && decide (p.1.2 = p.2))
            (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
            encBool := by fun_prop
        have hpair : ComputableInPolyTime
            (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) =>
              [(3 * p.1.1.1.2 + p.1.2, 3 * p.1.1.2 + p.2)])
            (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
            (encList (encPair encNat encNat)) := by
          have ha : ComputableInPolyTime
              (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) => 3 * p.1.1.1.2 + p.1.2)
              (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
              encNat := by
            have hu : ComputableInPolyTime
                (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) => 3 * p.1.1.1.2 + p.1.2)
                (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
                encUnary := by fun_prop
            exact ComputableInPolyTime.unary_to_binary.comp hu
          have hb : ComputableInPolyTime
              (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) => 3 * p.1.1.2 + p.2)
              (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
              encNat := by
            have hu : ComputableInPolyTime
                (fun p : ((((Graph × ℕ) × ℕ) × ℕ) × ℕ) => 3 * p.1.1.2 + p.2)
                (encPair (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encUnary)
                encUnary := by fun_prop
            exact ComputableInPolyTime.unary_to_binary.comp hu
          fun_prop
        exact ComputableInPolyTime.ite' hcond (.const []) hpair
      have hinner2 : ComputableInPolyTime
          (fun p : (((Graph × ℕ) × ℕ) × ℕ) =>
            (List.range 3).flatMap fun c' =>
              if p.1.1.1.adjBool (p.1.1.1.distinctVertices.getD p.1.1.2 0)
                  (p.1.1.1.distinctVertices.getD p.1.2 0) && decide (p.2 = c')
              then ([] : List (ℕ × ℕ))
              else [(3 * p.1.1.2 + p.2, 3 * p.1.2 + c')])
          (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary)
          (encList (encPair encNat encNat)) :=
        ComputableInPolyTime.flatMapWithInput (encA := encUnary) (.const (List.range 3)) hinner1
      have hinner3 : ComputableInPolyTime
          (fun p : ((Graph × ℕ) × ℕ) =>
            if p.1.2 = p.2 then ([] : List (ℕ × ℕ))
            else (List.range 3).flatMap fun c =>
              (List.range 3).flatMap fun c' =>
                if p.1.1.adjBool (p.1.1.distinctVertices.getD p.1.2 0)
                    (p.1.1.distinctVertices.getD p.2 0) && decide (c = c')
                then []
                else [(3 * p.1.2 + c, 3 * p.2 + c')])
          (encPair (encPair encGraph encUnary) encUnary)
          (encList (encPair encNat encNat)) := by
        have hfm := ComputableInPolyTime.flatMapWithInput (encA := encUnary)
          (f := fun (p : (Graph × ℕ) × ℕ) (c : ℕ) =>
            (List.range 3).flatMap fun c' =>
              if p.1.1.adjBool (p.1.1.distinctVertices.getD p.1.2 0)
                  (p.1.1.distinctVertices.getD p.2 0) && decide (c = c')
              then ([] : List (ℕ × ℕ))
              else [(3 * p.1.2 + c, 3 * p.2 + c')])
          (ComputableInPolyTime.const (encIn := encPair (encPair encGraph encUnary) encUnary)
            (List.range 3))
          hinner2
        have hcond : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => decide (p.1.2 = p.2))
            (encPair (encPair encGraph encUnary) encUnary) encBool := by fun_prop
        simpa using ComputableInPolyTime.ite' hcond (.const []) hfm
      have hinner4 : ComputableInPolyTime
          (fun p : Graph × ℕ =>
            (List.range p.1.distinctVertices.length).flatMap fun j =>
              if p.2 = j then ([] : List (ℕ × ℕ))
              else (List.range 3).flatMap fun c =>
                (List.range 3).flatMap fun c' =>
                  if p.1.adjBool (p.1.distinctVertices.getD p.2 0)
                      (p.1.distinctVertices.getD j 0) && decide (c = c')
                  then []
                  else [(3 * p.2 + c, 3 * j + c')])
          (encPair encGraph encUnary)
          (encList (encPair encNat encNat)) :=
        ComputableInPolyTime.flatMapWithInput (encA := encUnary) (by fun_prop) hinner3
      exact ComputableInPolyTime.flatMapWithInput (encA := encUnary) (by fun_prop) hinner4
    have hgraph : ComputableInPolyTime
        (fun G : Graph => (⟨List.range (3 * G.distinctVertices.length),
          (List.range G.distinctVertices.length).flatMap fun i =>
            (List.range G.distinctVertices.length).flatMap fun j =>
              if i = j then []
              else
                let u := G.distinctVertices.getD i 0
                let v := G.distinctVertices.getD j 0
                let adj := G.adjBool u v
                (List.range 3).flatMap fun c =>
                  (List.range 3).flatMap fun c' =>
                    if adj && decide (c = c') then []
                    else [(3 * i + c, 3 * j + c')]⟩ : Graph))
        encGraph encGraph :=
      encGraph_mk_polyTime hverts hedges
    simpa using ComputableInPolyTime.ite' hm0 (.const ⟨[0], []⟩) hgraph
  exact h1.prod (.const (3 : ℚ))

theorem threeColoringToFCC_mem_iff (G : Graph) :
    threeColoringToFCC G ∈ FractionalCliqueCover ↔ G ∈ ThreeColoring := by
  rw [mem_FractionalCliqueCover]
  simp only [threeColoringToFCC, show (0 : ℚ) < 3 by norm_num, true_and, Rat.cast_ofNat]
  unfold threeColoringToFCCGraph
  set vs := G.distinctVertices with hvs_def
  set m := vs.length with hm_def
  by_cases hm : m = 0
  · have hlen0 : vs.length = 0 := hm
    simp only [hlen0, ↓reduceIte]
    constructor
    · intro _
      rw [mem_KColoring_iff]
      refine ⟨fun _ => 0, fun v hv => ?_, fun u hu => ?_⟩
      · have hmem : v ∈ vs := (Graph.mem_distinctVertices).2 hv
        exact ((List.length_pos_of_mem hmem).ne' hm).elim
      · have hmem : u ∈ vs := (Graph.mem_distinctVertices).2 hu
        exact ((List.length_pos_of_mem hmem).ne' hm).elim
    · intro _
      let H : Graph := ⟨[0], []⟩
      let v0 : {v // v ∈ H.vertices} := ⟨0, by simp [H]⟩
      refine ⟨fun C => if C = {v0} then 1 else 0,
        fun C => by dsimp only; split_ifs <;> norm_num,
        fun C hC => by
          have : C = {v0} := by by_contra hne; simp [hne] at hC
          subst this; simp,
        by simp,
        fun v => ?_⟩
      have hv : v = v0 := Subtype.ext (by simpa [H] using v.2)
      subst hv
      rw [Finset.sum_eq_single ({v0} : Finset _)]
      · simp
      · intro C _ hC; simp [hC]
      · intro h
        exact (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩)).elim
  · have hlen0 : vs.length ≠ 0 := hm
    simp only [hlen0, ↓reduceIte]
    set H : Graph := ⟨List.range (3 * m),
      (List.range m).flatMap fun i =>
        (List.range m).flatMap fun j =>
          if i = j then []
          else
            let u := vs.getD i 0
            let v := vs.getD j 0
            let adj := G.adjBool u v
            (List.range 3).flatMap fun c =>
              (List.range 3).flatMap fun c' =>
                if adj && decide (c = c') then []
                else [(3 * i + c, 3 * j + c')]⟩
    have hH_adj : ∀ (i j : ℕ) (hi : i < m) (hj : j < m) (c c' : ℕ) (hc : c < 3) (hc' : c' < 3),
        H.toSimpleGraph.Adj (3 * i + c) (3 * j + c') ↔
          i ≠ j ∧ ¬ (G.toSimpleGraph.Adj (vs.getD i 0) (vs.getD j 0) ∧ c = c') := by
      intro i j hi hj c c' hc hc'
      rw [Graph.toSimpleGraph_adj]
      have hmem_edge : ∀ a b : ℕ, (a, b) ∈ H.edges ↔
          ∃ i₁ < m, ∃ j₁ < m, i₁ ≠ j₁ ∧ ∃ c₁ < 3, ∃ c₂ < 3,
            ¬ (G.toSimpleGraph.Adj (vs.getD i₁ 0) (vs.getD j₁ 0) ∧ c₁ = c₂) ∧
            a = 3 * i₁ + c₁ ∧ b = 3 * j₁ + c₂ := by
        intro a b
        simp only [H, List.mem_flatMap, List.mem_range]
        constructor
        · rintro ⟨i₁, hi₁, j₁, hj₁, h⟩
          by_cases hij : i₁ = j₁
          · simp [hij] at h
          · simp only [hij, ↓reduceIte, List.mem_flatMap, List.mem_range] at h
            rcases h with ⟨c₁, hc₁, c₂, hc₂, h'⟩
            by_cases hcond : (G.adjBool (vs.getD i₁ 0) (vs.getD j₁ 0) && decide (c₁ = c₂)) = true
            · rw [ite_eq_left hcond] at h'; simp at h'
            · rw [ite_eq_right hcond] at h'
              simp only [List.mem_singleton, Prod.mk.injEq] at h'
              refine ⟨i₁, hi₁, j₁, hj₁, hij, c₁, hc₁, c₂, hc₂, ?_, h'.1, h'.2⟩
              intro ⟨hadj, hceq⟩
              apply hcond
              rw [Bool.and_eq_true, Graph.adjBool_eq_true_iff, decide_eq_true_eq]
              exact ⟨hadj, hceq⟩
        · rintro ⟨i₁, hi₁, j₁, hj₁, hij, c₁, hc₁, c₂, hc₂, hnot, rfl, rfl⟩
          refine ⟨i₁, hi₁, j₁, hj₁, ?_⟩
          simp only [hij, ↓reduceIte, List.mem_flatMap, List.mem_range]
          refine ⟨c₁, hc₁, c₂, hc₂, ?_⟩
          have hcond : ¬ (G.adjBool (vs.getD i₁ 0) (vs.getD j₁ 0) && decide (c₁ = c₂)) = true := by
            intro h
            rw [Bool.and_eq_true, Graph.adjBool_eq_true_iff, decide_eq_true_eq] at h
            exact hnot h
          rw [ite_eq_right hcond]
          exact List.mem_singleton_self _
      constructor
      · rintro ⟨hne, he | he⟩
        · rw [hmem_edge] at he
          rcases he with ⟨i₁, hi₁, j₁, hj₁, hij, c₁, hc₁, c₂, hc₂, hnot, h1, h2⟩
          obtain ⟨rfl, rfl⟩ : i₁ = i ∧ c₁ = c := ⟨by omega, by omega⟩
          obtain ⟨rfl, rfl⟩ : j₁ = j ∧ c₂ = c' := ⟨by omega, by omega⟩
          exact ⟨hij, hnot⟩
        · rw [hmem_edge] at he
          rcases he with ⟨i₁, hi₁, j₁, hj₁, hij, c₁, hc₁, c₂, hc₂, hnot, h1, h2⟩
          obtain ⟨rfl, rfl⟩ : i₁ = j ∧ c₁ = c' := ⟨by omega, by omega⟩
          obtain ⟨rfl, rfl⟩ : j₁ = i ∧ c₂ = c := ⟨by omega, by omega⟩
          exact ⟨hij.symm, fun ⟨hadj, hceq⟩ => hnot ⟨hadj.symm, hceq.symm⟩⟩
      · rintro ⟨hij, hnot⟩
        refine ⟨by omega, Or.inl ?_⟩
        rw [hmem_edge]
        exact ⟨i, hi, j, hj, hij, c, hc, c', hc', hnot, rfl, rfl⟩
    constructor
    · rintro ⟨w, hw, hclique, hsum, hcov⟩
      have hcard_le : ∀ C : Finset {v // v ∈ H.vertices},
          H.induced.IsClique (C : Set {v // v ∈ H.vertices}) → C.card ≤ m := by
        intro C hC
        have hinj : Set.InjOn (fun x : {v // v ∈ H.vertices} => x.1 / 3) (C : Set _) := by
          intro x hx y hy hdiv
          by_contra hxy
          have hxlt : x.1 < 3 * m := by simpa [H] using x.2
          have hylt : y.1 < 3 * m := by simpa [H] using y.2
          have hadj : H.toSimpleGraph.Adj x.1 y.1 := hC hx hy hxy
          have h1 := (hH_adj (x.1 / 3) (y.1 / 3) (by omega) (by omega) (x.1 % 3) (y.1 % 3)
            (by omega) (by omega)).1 (by simpa [Nat.div_add_mod] using hadj)
          exact h1.1 hdiv
        calc C.card = (C.image fun x => x.1 / 3).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range m).card := by
            apply Finset.card_le_card
            intro k hk
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hk
            have hxlt : x.1 < 3 * m := by simpa [H] using x.2
            exact Finset.mem_range.2 (by omega)
          _ = m := Finset.card_range m
      have hcard_H : Fintype.card {v // v ∈ H.vertices} = 3 * m := by
        rw [Fintype.card_of_subtype (Finset.range (3 * m)) (fun x => by simp [H]),
          Finset.card_range]
      have hdouble : (3 * m : ℝ) = ∑ C, (C.card : ℝ) * w C := by
        calc (3 * m : ℝ) = ∑ _v : {v // v ∈ H.vertices}, (1 : ℝ) := by
              simp [hcard_H]
          _ = ∑ v : {v // v ∈ H.vertices},
                ∑ C ∈ Finset.univ.filter (fun C => v ∈ C), w C := by
              apply Finset.sum_congr rfl; intro v _; exact (hcov v).symm
          _ = ∑ v : {v // v ∈ H.vertices}, ∑ C, if v ∈ C then w C else 0 := by
              apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_filter]
          _ = ∑ C, ∑ v : {v // v ∈ H.vertices}, if v ∈ C then w C else 0 := Finset.sum_comm
          _ = ∑ C, (C.card : ℝ) * w C := by
              apply Finset.sum_congr rfl; intro C _
              simp [Finset.sum_ite_mem]
      have hle_m : ∑ C, (C.card : ℝ) * w C ≤ (m : ℝ) * ∑ C, w C := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro C _
        by_cases hC0 : w C = 0
        · simp [hC0]
        · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hcard_le C (hclique C hC0))) (hw C)
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
      have hsum_eq : ∑ C, w C = 3 := by nlinarith
      have hexists : ∃ C, 0 < w C := by
        by_contra hall
        push Not at hall
        have : ∑ C, w C ≤ 0 := Finset.sum_nonpos fun C _ => hall C
        linarith
      obtain ⟨C, hCw⟩ := hexists
      have hCcard : C.card = m := by
        have h1 : (C.card : ℝ) * w C = (m : ℝ) * w C := by
          have hdiff : ∑ D, ((m : ℝ) - D.card) * w D = 0 := by
            have := Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun D : Finset {v // v ∈ H.vertices} => (m : ℝ) * w D)
              (g := fun D => (D.card : ℝ) * w D)
            simp_rw [sub_mul, this, ← Finset.mul_sum, hsum_eq, ← hdouble]
            ring
          have hnn : ∀ D : Finset {v // v ∈ H.vertices}, 0 ≤ ((m : ℝ) - D.card) * w D := by
            intro D
            by_cases hD0 : w D = 0
            · simp [hD0]
            · apply mul_nonneg _ (hw D)
              have := Nat.cast_le (α := ℝ).2 (hcard_le D (hclique D hD0))
              linarith
          have hC0 := (Finset.sum_eq_zero_iff_of_nonneg fun D _ => hnn D).1
            hdiff C (Finset.mem_univ C)
          have hsub0 : (m : ℝ) - C.card = 0 := (mul_eq_zero.1 hC0).resolve_right hCw.ne'
          linarith
        have h2 : (C.card : ℝ) = m := mul_right_cancel₀ hCw.ne' h1
        exact_mod_cast h2
      have hsurj : C.image (fun x : {v // v ∈ H.vertices} => x.1 / 3) = Finset.range m := by
        apply Finset.eq_of_subset_of_card_le
        · intro k hk
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hk
          have hxlt : x.1 < 3 * m := by simpa [H] using x.2
          exact Finset.mem_range.2 (by omega)
        · have hinj : Set.InjOn (fun x : {v // v ∈ H.vertices} => x.1 / 3) (C : Set _) := by
            intro x hx y hy hdiv
            by_contra hxy
            have hxlt : x.1 < 3 * m := by simpa [H] using x.2
            have hylt : y.1 < 3 * m := by simpa [H] using y.2
            have hadj : H.toSimpleGraph.Adj x.1 y.1 := hclique C hCw.ne' hx hy hxy
            have h1 := (hH_adj (x.1 / 3) (y.1 / 3) (by omega) (by omega) (x.1 % 3) (y.1 % 3)
              (by omega) (by omega)).1 (by simpa [Nat.div_add_mod] using hadj)
            exact h1.1 hdiv
          rw [Finset.card_image_of_injOn hinj, hCcard, Finset.card_range]
      rw [mem_KColoring_iff]
      have hpick : ∀ (i : ℕ) (_ : i < m), ∃ (c : ℕ) (_ : c < 3),
          (⟨3 * i + c, by simp [H]; omega⟩ : {v // v ∈ H.vertices}) ∈ C := by
        intro i hi
        have hmem : i ∈ C.image (fun x : {v // v ∈ H.vertices} => x.1 / 3) := by
          rw [hsurj]; exact Finset.mem_range.2 hi
        obtain ⟨x, hxC, hxi⟩ := Finset.mem_image.1 hmem
        refine ⟨x.1 % 3, by omega, ?_⟩
        convert hxC using 1
        ext; dsimp only; omega
      let col (u : ℕ) : ℕ :=
        let i := vs.idxOf u
        if h : i < m then (hpick i h).choose % 3 else 0
      refine ⟨col, fun u hu => ?_, fun u hu v hv huv => ?_⟩
      · have hmem : u ∈ vs := (Graph.mem_distinctVertices).2 hu
        have hi : vs.idxOf u < m := List.idxOf_lt_length_iff.2 hmem
        simp only [col, hi, ↓reduceDIte]
        exact Nat.mod_lt _ (by norm_num)
      · have hu' : u ∈ vs := (Graph.mem_distinctVertices).2 hu
        have hv' : v ∈ vs := (Graph.mem_distinctVertices).2 hv
        have hi : vs.idxOf u < m := List.idxOf_lt_length_iff.2 hu'
        have hj : vs.idxOf v < m := List.idxOf_lt_length_iff.2 hv'
        set i := vs.idxOf u
        set j := vs.idxOf v
        set ci := (hpick i hi).choose
        set cj := (hpick j hj).choose
        have hci_lt : ci < 3 := (hpick i hi).choose_spec.1
        have hcj_lt : cj < 3 := (hpick j hj).choose_spec.1
        have hci_mem := (hpick i hi).choose_spec.2
        have hcj_mem := (hpick j hj).choose_spec.2
        have hne_ij : i ≠ j := fun h => huv.ne (by
          have h' : vs.idxOf u = vs.idxOf v := h
          rw [← List.getElem_idxOf hi, ← List.getElem_idxOf hj]
          simp [h'])
        have hne_vert : (⟨3 * i + ci, by simp [H]; omega⟩ : {v // v ∈ H.vertices}) ≠
            ⟨3 * j + cj, by simp [H]; omega⟩ := by
          intro h; apply hne_ij
          have hv_eq := congrArg Subtype.val h; dsimp only at hv_eq; omega
        have hadjH : H.toSimpleGraph.Adj (3 * i + ci) (3 * j + cj) :=
          hclique C hCw.ne' hci_mem hcj_mem hne_vert
        have hnot := ((hH_adj i j hi hj ci cj hci_lt hcj_lt).1 hadjH).2
        have hgu : vs.getD i 0 = u := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_idxOf hi
        have hgv : vs.getD j 0 = v := by
          rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_idxOf hj
        rw [hgu, hgv] at hnot
        intro heq
        have hcol_u : col u = ci := by
          dsimp only [col]
          rw [dite_eq_left hi]
          exact Nat.mod_eq_of_lt hci_lt
        have hcol_v : col v = cj := by
          dsimp only [col]
          rw [dite_eq_left hj]
          exact Nat.mod_eq_of_lt hcj_lt
        rw [hcol_u, hcol_v] at heq
        exact hnot ⟨huv, heq⟩
    · intro hcol
      rw [mem_KColoring_iff] at hcol
      rcases hcol with ⟨col, hcol_lt, hcol_adj⟩
      let shiftClique (r : Fin 3) : Finset {v // v ∈ H.vertices} :=
        Finset.univ.filter fun x => x.1 % 3 = (col (vs.getD (x.1 / 3) 0) + r.1) % 3
      have hshift_clique : ∀ r : Fin 3,
          H.induced.IsClique (shiftClique r : Set {v // v ∈ H.vertices}) := by
        intro r x hx y hy hxy
        have hx' : x.1 % 3 = (col (vs.getD (x.1 / 3) 0) + r.1) % 3 := (Finset.mem_filter.1 hx).2
        have hy' : y.1 % 3 = (col (vs.getD (y.1 / 3) 0) + r.1) % 3 := (Finset.mem_filter.1 hy).2
        have hxlt : x.1 < 3 * m := by simpa [H] using x.2
        have hylt : y.1 < 3 * m := by simpa [H] using y.2
        have hdiv_ne : x.1 / 3 ≠ y.1 / 3 := by
          intro hdiv
          apply hxy
          ext; rw [← Nat.div_add_mod x.1 3, ← Nat.div_add_mod y.1 3, hx', hy', hdiv]
        have hnot : ¬ (G.toSimpleGraph.Adj (vs.getD (x.1 / 3) 0) (vs.getD (y.1 / 3) 0) ∧
            x.1 % 3 = y.1 % 3) := by
          rintro ⟨hadj, hmod⟩
          have hu_mem : vs.getD (x.1 / 3) 0 ∈ G.vertices := by
            rw [List.getD_eq_getElem _ _ (by omega : x.1 / 3 < m)]
            exact (Graph.mem_distinctVertices).1 (List.getElem_mem _)
          have hv_mem : vs.getD (y.1 / 3) 0 ∈ G.vertices := by
            rw [List.getD_eq_getElem _ _ (by omega : y.1 / 3 < m)]
            exact (Graph.mem_distinctVertices).1 (List.getElem_mem _)
          have hcu := hcol_lt _ hu_mem
          have hcv := hcol_lt _ hv_mem
          have hne := hcol_adj _ hu_mem _ hv_mem hadj
          rw [hx', hy'] at hmod
          omega
        have hadj := (hH_adj (x.1 / 3) (y.1 / 3) (by omega) (by omega) (x.1 % 3) (y.1 % 3)
          (by omega) (by omega)).2 ⟨hdiv_ne, hnot⟩
        simpa [Nat.div_add_mod] using hadj
      let w : Finset {v // v ∈ H.vertices} → ℝ := fun C =>
        ∑ r : Fin 3, if C = shiftClique r then (1 : ℝ) else 0
      refine ⟨w, fun C => Finset.sum_nonneg fun r _ => by split_ifs <;> norm_num, ?_, ?_, ?_⟩
      · intro C hC
        have hex : ∃ r : Fin 3, C = shiftClique r := by
          by_contra hnone
          push Not at hnone
          exact hC (Finset.sum_eq_zero fun r _ => by simp [hnone r])
        obtain ⟨r, rfl⟩ := hex
        exact hshift_clique r
      · calc ∑ C, w C = ∑ r : Fin 3, ∑ C, if C = shiftClique r then (1 : ℝ) else 0 :=
              Finset.sum_comm
          _ = ∑ _r : Fin 3, (1 : ℝ) := by apply Finset.sum_congr rfl; intro r _; simp
          _ = 3 := by norm_num
          _ ≤ 3 := le_rfl
      · intro x
        have hxlt : x.1 < 3 * m := by simpa [H] using x.2
        have hu_mem : vs.getD (x.1 / 3) 0 ∈ G.vertices := by
          rw [List.getD_eq_getElem _ _ (by omega : x.1 / 3 < m)]
          exact (Graph.mem_distinctVertices).1 (List.getElem_mem _)
        have hcu : col (vs.getD (x.1 / 3) 0) < 3 := hcol_lt _ hu_mem
        let r0 : Fin 3 := ⟨(x.1 % 3 + 3 - col (vs.getD (x.1 / 3) 0)) % 3,
          Nat.mod_lt _ (by norm_num)⟩
        have hxr0 : x ∈ shiftClique r0 := by
          simp only [shiftClique, Finset.mem_filter, Finset.mem_univ, true_and, r0]
          omega
        have huniq : ∀ r : Fin 3, x ∈ shiftClique r ↔ r = r0 := by
          intro r
          constructor
          · intro hr
            have h1 := (Finset.mem_filter.1 hr).2
            ext; dsimp [r0]; omega
          · rintro rfl; exact hxr0
        rw [Finset.sum_filter]
        calc (∑ C, if x ∈ C then w C else 0)
            = ∑ r : Fin 3, ∑ C,
                if x ∈ C then (if C = shiftClique r then (1 : ℝ) else 0) else 0 := by
              have hsplit : ∀ C : Finset {v // v ∈ H.vertices},
                  (if x ∈ C then w C else 0) =
                    ∑ r : Fin 3,
                      if x ∈ C then (if C = shiftClique r then (1 : ℝ) else 0) else 0 := by
                intro C
                by_cases hx : x ∈ C <;> simp [w, hx]
              simp_rw [hsplit]
              exact Finset.sum_comm
          _ = ∑ r : Fin 3, if x ∈ shiftClique r then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl; intro r _
              rw [Finset.sum_eq_single (shiftClique r)]
              · simp
              · intro C _ hC; split_ifs <;> simp
              · intro h; exact (h (Finset.mem_univ _)).elim
          _ = 1 := by
              rw [Finset.sum_eq_single r0]
              · simp [hxr0]
              · intro r _ hr; simp [(huniq r).not.2 hr]
              · intro h; exact (h (Finset.mem_univ _)).elim

/-- **Fractional Clique Cover is NP-hard** (zero megatheorems, Karp reduction from
`ThreeColoring`). -/
theorem FractionalCliqueCover_npHard :
    NPHard encFractionalCliqueCover FractionalCliqueCover :=
  ThreeColoring_npHard.trans
    ⟨threeColoringToFCC, computableInPolyTime_threeColoringToFCC,
      fun G => (threeColoringToFCC_mem_iff G).symm⟩

end Cslib.Complexity
