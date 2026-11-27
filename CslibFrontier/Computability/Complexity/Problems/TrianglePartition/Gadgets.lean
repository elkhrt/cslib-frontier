/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Finite Gadgets and CNF Normalization for `K4FreeTrianglePartition`

Core definitions of `IsTriangleEdgePartition` and `K4FreeTrianglePartition`, together with the
finite $\mathrm{Torus}(12, 4)$ variable gadget, $K_{3,3,3}$ clause gadget, and width-3 CNF
normalization `normCNF` used in the Karp reduction `ThreeSATThree ≤ₚ K4FreeTrianglePartition`.

## Main definitions
- `IsTriangleEdgePartition`, `K4FreeTrianglePartition`: triangle edge-partition on $K_4$-free
  graphs.
- `torusAdj`, `torusEdges`, `torusUpTri`, `torusDownTri`, `torusPortAll`: $\mathrm{Torus}(12, 4)$
  variable gadget.
- `k333Adj`, `k333ClauseAdj`, `k333Edges`, `k333PortVert`, `k333PartTris`: $K_{3,3,3}$ clause
  gadget.
- `normCNF`: tautology-free, per-clause deduplicated width-3 CNF normalization.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Core Problem Definitions -/

/-- A graph `G` admits a triangle edge-partition if its edge set can be partitioned into
edge-disjoint triangles ($3$-cliques in `G.induced`). -/
def IsTriangleEdgePartition (G : Graph) : Prop :=
  ∃ 𝒯 : Finset (Finset {v // v ∈ G.vertices}),
    (∀ T ∈ 𝒯, G.induced.IsNClique 3 T) ∧
    ∀ u v : {v // v ∈ G.vertices}, G.induced.Adj u v →
      ∃! T ∈ 𝒯, u ∈ T ∧ v ∈ T

/-- Semantic API lemma for `IsTriangleEdgePartition`. -/
theorem isTriangleEdgePartition_iff (G : Graph) :
    IsTriangleEdgePartition G ↔
      ∃ 𝒯 : Finset (Finset {v // v ∈ G.vertices}),
        (∀ T ∈ 𝒯, G.induced.IsNClique 3 T) ∧
        ∀ u v : {v // v ∈ G.vertices}, G.induced.Adj u v →
          ∃! T ∈ 𝒯, u ∈ T ∧ v ∈ T :=
  Iff.rfl

/-- The decision problem of determining whether a $K_4$-free graph admits a triangle
edge-partition. -/
def K4FreeTrianglePartition : Set Graph :=
  {G | G.induced.CliqueFree 4 ∧ IsTriangleEdgePartition G}

/-- Membership characterization for `K4FreeTrianglePartition`. -/
theorem mem_K4FreeTrianglePartition {G : Graph} :
    G ∈ K4FreeTrianglePartition ↔ G.induced.CliqueFree 4 ∧ IsTriangleEdgePartition G :=
  Iff.rfl

/-! ### Trivial Base Graphs -/

/-- Fixed $K_4$-free non-partitionable graph ($K_2$). -/
@[expose] def noTriGraph : Graph := ⟨[0, 1], [(0, 1)]⟩

/-- Fixed empty $K_4$-free partitionable graph. -/
@[expose] def emptyTriGraph : Graph := ⟨[], []⟩

theorem noTriGraph_k4Free : noTriGraph.induced.CliqueFree 4 := by
  intro S hS
  have hle : S.card ≤ Fintype.card {v // v ∈ noTriGraph.vertices} := Finset.card_le_univ S
  have hcard : Fintype.card {v // v ∈ noTriGraph.vertices} ≤ 2 := by
    have hsub : ((Finset.univ : Finset {v // v ∈ noTriGraph.vertices}).image Subtype.val) ⊆
        ({0, 1} : Finset ℕ) := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨v, _, rfl⟩
      have hv := v.2
      simpa [noTriGraph] using hv
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h1
    simpa using h1
  have := hS.2
  omega

theorem noTriGraph_not_triPart : ¬ IsTriangleEdgePartition noTriGraph := by
  rintro ⟨𝒯, hcl, hcov⟩
  have h0 : (0 : ℕ) ∈ noTriGraph.vertices := by simp [noTriGraph]
  have h1 : (1 : ℕ) ∈ noTriGraph.vertices := by simp [noTriGraph]
  have hadj : noTriGraph.induced.Adj ⟨0, h0⟩ ⟨1, h1⟩ := by
    rw [Graph.induced_adj, Graph.toSimpleGraph_adj]
    exact ⟨fun h => by norm_num at h, Or.inl (by simp [noTriGraph])⟩
  obtain ⟨T, ⟨hT, _, _⟩, _⟩ := hcov ⟨0, h0⟩ ⟨1, h1⟩ hadj
  have hcard : Fintype.card {v // v ∈ noTriGraph.vertices} ≤ 2 := by
    have hsub : ((Finset.univ : Finset {v // v ∈ noTriGraph.vertices}).image Subtype.val) ⊆
        ({0, 1} : Finset ℕ) := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨v, _, rfl⟩
      have hv := v.2
      simpa [noTriGraph] using hv
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h1'
    simpa using h1'
  have := Finset.card_le_univ T
  have := (hcl T hT).2
  omega

theorem emptyTriGraph_mem : emptyTriGraph ∈ K4FreeTrianglePartition := by
  refine ⟨?_, ?_⟩
  · intro S hS
    have : S.card = 0 := by
      rw [Finset.card_eq_zero]
      ext v
      exact (List.not_mem_nil v.2).elim
    have := hS.2
    omega
  · exact ⟨∅, by simp, fun u _ _ => (List.not_mem_nil u.2).elim⟩

/-! ### Finite Gadget 1: `Torus(12, 4)` -/

/-- Adjacency predicate of the $48$-vertex triangulated torus $\mathrm{Torus}(12, 4)$. -/
@[expose] def torusAdj (p q : ℕ) : Bool :=
  if p < 48 ∧ q < 48 then
    let xp := p / 4; let yp := p % 4
    let xq := q / 4; let yq := q % 4
    decide ((xq = (xp + 1) % 12 ∧ yq = yp) ∨
      (xp = (xq + 1) % 12 ∧ yq = yp) ∨
      (xq = xp ∧ yq = (yp + 1) % 4) ∨
      (xq = xp ∧ yp = (yq + 1) % 4) ∨
      (xq = (xp + 1) % 12 ∧ yp = (yq + 1) % 4) ∨
      (xp = (xq + 1) % 12 ∧ yq = (yp + 1) % 4))
  else false

/-- The 6 neighbors of `p` on $\mathrm{Torus}(12, 4)$. -/
@[expose] def torusNbrs (p : ℕ) : List ℕ :=
  let x := p / 4; let y := p % 4
  [4 * ((x + 1) % 12) + y, 4 * ((x + 11) % 12) + y,
   4 * x + (y + 1) % 4, 4 * x + (y + 3) % 4,
   4 * ((x + 1) % 12) + (y + 3) % 4, 4 * ((x + 11) % 12) + (y + 1) % 4]

/-- The 144 edges of $\mathrm{Torus}(12, 4)$. -/
@[expose] def torusEdges : List (ℕ × ℕ) :=
  (List.range 48).flatMap fun p =>
    (List.range 48).flatMap fun q =>
      if p < q && torusAdj p q then [(p, q)] else []

/-- UP triangle `(x, y)` on $\mathrm{Torus}(12, 4)$. -/
@[expose] def torusUpTri (x y : ℕ) : List ℕ :=
  [4 * (x % 12) + y % 4, 4 * ((x + 1) % 12) + y % 4, 4 * (x % 12) + (y + 1) % 4]

/-- DOWN triangle `(x, y)` on $\mathrm{Torus}(12, 4)$. -/
@[expose] def torusDownTri (x y : ℕ) : List ℕ :=
  [4 * (x % 12) + y % 4, 4 * ((x + 1) % 12) + y % 4, 4 * ((x + 1) % 12) + (y + 3) % 4]

/-- Set-equality test for two triples of natural numbers. -/
@[expose] def isSameTri (a b c p q r : ℕ) : Bool :=
  decide (a ∈ [p, q, r] ∧ b ∈ [p, q, r] ∧ c ∈ [p, q, r] ∧
    p ∈ [a, b, c] ∧ q ∈ [a, b, c] ∧ r ∈ [a, b, c])

/-- The 4 vertices of port `occ ∈ {0, 1, 2}` (union of UP-port and DOWN-port). -/
@[expose] def torusPortAll (occ : ℕ) : List ℕ :=
  [4 * (4 * occ), 4 * (4 * occ + 1), 4 * (4 * occ) + 1, 4 * (4 * occ + 1) + 3]

/-- Check whether `{p, q, r}` is one of the 6 UP/DOWN triangles incident to `p`. -/
@[expose] def torusTriClass (p q r : ℕ) : Bool :=
  let x := p / 4; let y := p % 4
  let u1 := torusUpTri x y
  let u2 := torusUpTri ((x + 11) % 12) y
  let u3 := torusUpTri x ((y + 3) % 4)
  let d1 := torusDownTri x y
  let d2 := torusDownTri ((x + 11) % 12) y
  let d3 := torusDownTri ((x + 11) % 12) ((y + 1) % 4)
  let eq3 (l : List ℕ) := isSameTri p q r (l.getD 0 0) (l.getD 1 0) (l.getD 2 0)
  eq3 u1 || eq3 u2 || eq3 u3 || eq3 d1 || eq3 d2 || eq3 d3

theorem torusAdj_symm (p q : ℕ) : torusAdj p q = torusAdj q p := by
  by_cases hp : p < 48 <;> by_cases hq : q < 48
  · revert p q
    have : ∀ p q : Fin 48, torusAdj p.1 q.1 = torusAdj q.1 p.1 := by decide
    intro p q hp hq; exact this ⟨p, hp⟩ ⟨q, hq⟩
  · simp [torusAdj, hp, hq]
  · simp [torusAdj, hp, hq]
  · simp [torusAdj, hp, hq]

theorem torusAdj_irrefl (p : ℕ) : torusAdj p p = false := by
  by_cases hp : p < 48
  · revert p
    have : ∀ p : Fin 48, torusAdj p.1 p.1 = false := by decide
    intro p hp; exact this ⟨p, hp⟩
  · simp [torusAdj, hp]

theorem torusAdj_bounds {p q : ℕ} (h : torusAdj p q = true) : p < 48 ∧ q < 48 := by
  unfold torusAdj at h
  split_ifs at h with hb
  exact hb

theorem mem_torusEdges_iff (p q : ℕ) :
    ((p, q) ∈ torusEdges ∨ (q, p) ∈ torusEdges) ↔ torusAdj p q = true := by
  simp only [torusEdges, List.mem_flatMap, List.mem_range]
  constructor
  · rintro (⟨a, _, b, _, h⟩ | ⟨a, _, b, _, h⟩)
    · split_ifs at h with hc
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [Bool.and_eq_true] at hc; exact hc.2
      · simp at h
    · split_ifs at h with hc
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [torusAdj_symm]
        simp only [Bool.and_eq_true] at hc; exact hc.2
      · simp at h
  · intro h
    obtain ⟨hp, hq⟩ := torusAdj_bounds h
    have hne : p ≠ q := fun heq => by subst heq; rw [torusAdj_irrefl] at h; simp at h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left; refine ⟨p, hp, q, hq, ?_⟩; simp [hlt, h]
    · right; refine ⟨q, hq, p, hp, ?_⟩; rw [torusAdj_symm] at h; simp [hgt, h]

theorem mem_torusNbrs_iff (p : Fin 48) (q : ℕ) :
    q ∈ torusNbrs p.1 ↔ torusAdj p.1 q = true := by
  by_cases hq : q < 48
  · have : ∀ (a b : Fin 48), (b.1 ∈ torusNbrs a.1) = (torusAdj a.1 b.1 == true) := by decide
    simpa using this p ⟨q, hq⟩
  · constructor
    · intro hmem
      have hlt : ∀ a : Fin 48, ∀ x ∈ torusNbrs a.1, x < 48 := by decide
      exact (hq (hlt p q hmem)).elim
    · intro h; exact (hq (torusAdj_bounds h).2).elim

private theorem torus_k4Free_aux :
    ∀ p : Fin 48, ∀ q ∈ torusNbrs p.1, ∀ r ∈ torusNbrs p.1,
      torusAdj q r = true → ∀ s ∈ torusNbrs p.1, !(torusAdj q s && torusAdj r s) = true := by
  decide

theorem torus_k4Free {p q r s : ℕ}
    (hpq : torusAdj p q = true) (hpr : torusAdj p r = true) (hps : torusAdj p s = true)
    (hqr : torusAdj q r = true) (hqs : torusAdj q s = true) (hrs : torusAdj r s = true) :
    False := by
  have hp := (torusAdj_bounds hpq).1
  have hq := (mem_torusNbrs_iff ⟨p, hp⟩ q).2 hpq
  have hr := (mem_torusNbrs_iff ⟨p, hp⟩ r).2 hpr
  have hs := (mem_torusNbrs_iff ⟨p, hp⟩ s).2 hps
  have h := torus_k4Free_aux ⟨p, hp⟩ q hq r hr hqr s hs
  simp [hqs, hrs] at h

private theorem torus_port_dist_aux :
    ∀ o1 : Fin 3, ∀ o2 : Fin 3, o1 ≠ o2 →
      ∀ p ∈ torusPortAll o1.1, ∀ q ∈ torusPortAll o2.1,
        p ≠ q ∧ torusAdj p q = false ∧ (torusNbrs p).all (fun w => !torusAdj w q) = true := by
  decide

theorem torus_port_not_adj {o1 o2 p q : ℕ} (ho1 : o1 < 3) (ho2 : o2 < 3)
    (hne : o1 ≠ o2) (hp : p ∈ torusPortAll o1) (hq : q ∈ torusPortAll o2) :
    p ≠ q ∧ torusAdj p q = false := by
  have h := torus_port_dist_aux ⟨o1, ho1⟩ ⟨o2, ho2⟩
    (fun heq => hne (congrArg Fin.val heq)) p hp q hq
  exact ⟨h.1, h.2.1⟩

theorem torus_tri_class_aux :
    ∀ p : Fin 48, ∀ q ∈ torusNbrs p.1, ∀ r ∈ torusNbrs p.1,
      torusAdj q r = true → torusTriClass p.1 q r = true := by
  decide

theorem torus_up_adj (x : Fin 12) (y : Fin 4) :
    let t := torusUpTri x.1 y.1
    let a := t.getD 0 0; let b := t.getD 1 0; let c := t.getD 2 0
    a < 48 ∧ b < 48 ∧ c < 48 ∧
    torusAdj a b = true ∧ torusAdj a c = true ∧ torusAdj b c = true := by
  revert x y; decide

theorem torus_down_adj (x : Fin 12) (y : Fin 4) :
    let t := torusDownTri x.1 y.1
    let a := t.getD 0 0; let b := t.getD 1 0; let c := t.getD 2 0
    a < 48 ∧ b < 48 ∧ c < 48 ∧
    torusAdj a b = true ∧ torusAdj a c = true ∧ torusAdj b c = true := by
  revert x y; decide

theorem torus_edge_unique_up (p q : Fin 48) (h : torusAdj p.1 q.1 = true) :
    ∃! xy : Fin 12 × Fin 4,
      p.1 ∈ torusUpTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusUpTri xy.1.1 xy.2.1 := by
  revert p q h
  have hdec : ∀ p q : Fin 48, torusAdj p.1 q.1 = true →
      ((Finset.univ.filter fun xy : Fin 12 × Fin 4 =>
        p.1 ∈ torusUpTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusUpTri xy.1.1 xy.2.1).card = 1) := by
    decide
  intro p q h
  obtain ⟨xy, hxy⟩ := Finset.card_eq_one.1 (hdec p q h)
  refine ⟨xy, ?_, ?_⟩
  · have hmem : xy ∈ Finset.univ.filter (fun xy : Fin 12 × Fin 4 =>
        p.1 ∈ torusUpTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusUpTri xy.1.1 xy.2.1) := by
      rw [hxy]; exact Finset.mem_singleton_self xy
    exact (Finset.mem_filter.1 hmem).2
  · intro xy' hxy'
    have hmem : xy' ∈ Finset.univ.filter (fun xy : Fin 12 × Fin 4 =>
        p.1 ∈ torusUpTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusUpTri xy.1.1 xy.2.1) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy'⟩
    rw [hxy] at hmem
    exact Finset.mem_singleton.1 hmem

theorem torus_edge_unique_down (p q : Fin 48) (h : torusAdj p.1 q.1 = true) :
    ∃! xy : Fin 12 × Fin 4,
      p.1 ∈ torusDownTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusDownTri xy.1.1 xy.2.1 := by
  revert p q h
  have hdec : ∀ p q : Fin 48, torusAdj p.1 q.1 = true →
      ((Finset.univ.filter fun xy : Fin 12 × Fin 4 =>
        p.1 ∈ torusDownTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusDownTri xy.1.1 xy.2.1).card = 1) := by
    decide
  intro p q h
  obtain ⟨xy, hxy⟩ := Finset.card_eq_one.1 (hdec p q h)
  refine ⟨xy, ?_, ?_⟩
  · have hmem : xy ∈ Finset.univ.filter (fun xy : Fin 12 × Fin 4 =>
        p.1 ∈ torusDownTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusDownTri xy.1.1 xy.2.1) := by
      rw [hxy]; exact Finset.mem_singleton_self xy
    exact (Finset.mem_filter.1 hmem).2
  · intro xy' hxy'
    have hmem : xy' ∈ Finset.univ.filter (fun xy : Fin 12 × Fin 4 =>
        p.1 ∈ torusDownTri xy.1.1 xy.2.1 ∧ q.1 ∈ torusDownTri xy.1.1 xy.2.1) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy'⟩
    rw [hxy] at hmem
    exact Finset.mem_singleton.1 hmem

theorem torus_up_ne_down (x1 x2 : Fin 12) (y1 y2 : Fin 4) :
    (torusUpTri x1.1 y1.1).toFinset ≠ (torusDownTri x2.1 y2.1).toFinset := by
  revert x1 x2 y1 y2; decide

theorem torus_nonport_forcing (isU isD : Fin 12 × Fin 4 → Prop)
    (hhoriz : ∀ x : Fin 12, ∀ y : Fin 4,
      ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      (isU (x, y) ↔ ¬ isD (x, y)))
    (hvert : ∀ x : Fin 12, ∀ y : Fin 4,
      ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      ¬ ((y + 1).1 = 0 ∧ ((x - 1).1 = 0 ∨ (x - 1).1 = 4 ∨ (x - 1).1 = 8)) →
      (isU (x, y) ↔ ¬ isD (x - 1, y + 1)))
    (hdiag : ∀ x : Fin 12, ∀ y : Fin 4,
      ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      ¬ ((y + 1).1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      (isU (x, y) ↔ ¬ isD (x, y + 1))) :
    ∀ x : Fin 12, ∀ y : Fin 4, ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      (isU (x, y) ↔ isU (0, 1)) ∧ (isD (x, y) ↔ ¬ isU (0, 1)) := by
  have hstep_x : ∀ x : Fin 12, isU (x, 1) ↔ isU (x - 1, 1) := by
    intro x
    have h1 : isU (x, 1) ↔ ¬ isD (x - 1, 2) :=
      hvert x 1 (fun h => by simp at h) (fun h => by simp at h)
    have h2 : isU (x - 1, 2) ↔ ¬ isD (x - 1, 2) := hhoriz (x - 1) 2 (fun h => by simp at h)
    have h3 : isU (x - 1, 1) ↔ ¬ isD (x - 1, 2) :=
      hdiag (x - 1) 1 (fun h => by simp at h) (fun h => by simp at h)
    tauto
  have hall_x1 : ∀ x : Fin 12, isU (x, 1) ↔ isU (0, 1) := by
    have hloop : ∀ k : ℕ, (hk : k < 12) → (isU (⟨k, hk⟩, 1) ↔ isU (0, 1)) := by
      intro k hk
      induction k with
      | zero => exact Iff.rfl
      | succ k ih =>
        have hstep := hstep_x ⟨k + 1, hk⟩
        have hsub : (⟨k + 1, hk⟩ : Fin 12) - 1 = ⟨k, by omega⟩ := by
          ext; simp [Fin.sub_def]; omega
        rw [hsub] at hstep
        exact hstep.trans (ih (by omega))
    intro x; exact hloop x.1 x.2
  have hall_x2 : ∀ x : Fin 12, isU (x, 2) ↔ isU (0, 1) := by
    intro x
    have h1 : isU (x, 1) ↔ ¬ isD (x, 2) :=
      hdiag x 1 (fun h => by simp at h) (fun h => by simp at h)
    have h2 : isU (x, 2) ↔ ¬ isD (x, 2) := hhoriz x 2 (fun h => by simp at h)
    have h3 := hall_x1 x
    tauto
  have hall_x3 : ∀ x : Fin 12, isU (x, 3) ↔ isU (0, 1) := by
    intro x
    have h1 : isU (x, 2) ↔ ¬ isD (x, 3) :=
      hdiag x 2 (fun h => by simp at h) (fun h => by simp at h)
    have h2 : isU (x, 3) ↔ ¬ isD (x, 3) := hhoriz x 3 (fun h => by simp at h)
    have h3 := hall_x2 x
    tauto
  have hall_D123 : ∀ x : Fin 12, ∀ y : Fin 4, y.1 ≠ 0 →
      (isU (x, y) ↔ isU (0, 1)) ∧ (isD (x, y) ↔ ¬ isU (0, 1)) := by
    intro x y hy
    have hU : isU (x, y) ↔ isU (0, 1) := by
      fin_cases y
      · exact (hy rfl).elim
      · exact hall_x1 x
      · exact hall_x2 x
      · exact hall_x3 x
    have hH := hhoriz x y (fun h => hy h.1)
    exact ⟨hU, by tauto⟩
  intro x y hnp
  by_cases hy : y.1 = 0
  · have hy0 : y = 0 := Fin.ext hy
    subst hy0
    have hU : isU (x, 0) ↔ isU (0, 1) := by
      have h1 : isU (x, 0) ↔ ¬ isD (x - 1, 1) :=
        hvert x 0 hnp (fun h => by simp at h)
      have h2 := (hall_D123 (x - 1) 1 (by decide)).2
      tauto
    have hH := hhoriz x 0 hnp
    exact ⟨hU, by tauto⟩
  · exact hall_D123 x y hy

/-! ### Finite Gadget 2: `K_{3,3,3}` Clause Gadget -/

/-- Adjacency predicate of the tripartite graph $K_{3,3,3}$ on `Fin 9`. -/
@[expose] def k333Adj (u v : ℕ) : Bool :=
  decide (u < 9 ∧ v < 9 ∧ u / 3 ≠ v / 3)

/-- Vertex `pos ∈ {0, 1, 2}` of port triangle `T_r` in $K_{3,3,3}$:
$T_0 = (0, 3, 6)$, $T_1 = (1, 4, 6)$, $T_2 = (7, 2, 5)$. -/
@[expose] def k333PortVert (r pos : ℕ) : ℕ :=
  if r = 0 then (if pos = 0 then 0 else if pos = 1 then 3 else 6)
  else if r = 1 then (if pos = 0 then 1 else if pos = 1 then 4 else 6)
  else (if pos = 0 then 7 else if pos = 1 then 2 else 5)

/-- Test whether `{u, v}` is an edge of the triangle `(a, b, c)`. -/
@[expose] def isInTri (a b c u v : ℕ) : Bool :=
  decide ((u = a ∨ u = b ∨ u = c) ∧ (v = a ∨ v = b ∨ v = c) ∧ u ≠ v)

/-- Clause-gadget adjacency for a clause of width `len ∈ {1, 2, 3}`. -/
@[expose] def k333ClauseAdj (len u v : ℕ) : Bool :=
  k333Adj u v &&
    (if len ≤ 2 then !isInTri 7 2 5 u v else true) &&
    (if len ≤ 1 then !isInTri 1 4 6 u v else true)

/-- The 27 edges of $K_{3,3,3}$. -/
@[expose] def k333Edges : List (ℕ × ℕ) :=
  (List.range 9).flatMap fun u =>
    (List.range 9).flatMap fun v =>
      if u < v && k333Adj u v then [(u, v)] else []

/-- Explicit 7-triangle edge-partition of $K_{3,3,3}$ keeping port `rstar` and removing the
other two port triangles. -/
@[expose] def k333PartTris (rstar : ℕ) : List (ℕ × ℕ × ℕ) :=
  if rstar = 0 then
    [(0, 5, 6), (2, 3, 6), (1, 3, 7), (0, 4, 7), (1, 5, 8), (0, 3, 8), (2, 4, 8)]
  else if rstar = 1 then
    [(1, 5, 6), (2, 4, 6), (0, 4, 7), (1, 3, 7), (0, 5, 8), (1, 4, 8), (2, 3, 8)]
  else
    [(2, 5, 6), (0, 4, 7), (0, 5, 8), (1, 5, 7), (1, 3, 8), (2, 3, 7), (2, 4, 8)]

theorem k333Adj_symm (u v : ℕ) : k333Adj u v = k333Adj v u := by
  simp only [k333Adj]
  by_cases h1 : u < 9 <;> by_cases h2 : v < 9 <;> by_cases h3 : u / 3 = v / 3 <;>
    simp [h1, h2, h3, Ne.symm]

theorem k333ClauseAdj_symm (len u v : ℕ) :
    k333ClauseAdj len u v = k333ClauseAdj len v u := by
  unfold k333ClauseAdj
  rw [k333Adj_symm u v]
  have h1 : isInTri 7 2 5 u v = isInTri 7 2 5 v u := by
    simp only [isInTri, decide_eq_decide]; tauto
  have h2 : isInTri 1 4 6 u v = isInTri 1 4 6 v u := by
    simp only [isInTri, decide_eq_decide]; tauto
  rw [h1, h2]

theorem k333_k4Free {u v w z : ℕ}
    (huv : k333Adj u v = true) (huw : k333Adj u w = true) (huz : k333Adj u z = true)
    (hvw : k333Adj v w = true) (hvz : k333Adj v z = true) (hwz : k333Adj w z = true) :
    False := by
  simp only [k333Adj, decide_eq_true_eq] at huv huw huz hvw hvz hwz
  omega

theorem k333_part_valid :
    ∀ rstar : Fin 3, ∀ t ∈ k333PartTris rstar.1,
      k333Adj t.1 t.2.1 = true ∧ k333Adj t.1 t.2.2 = true ∧ k333Adj t.2.1 t.2.2 = true := by
  decide

theorem k333_part_exact :
    ∀ rstar : Fin 3, ∀ u v : Fin 9,
      (k333Adj u.1 v.1 = true ∧
        (rstar.1 ≠ 0 → isInTri 0 3 6 u.1 v.1 = false) ∧
        (rstar.1 ≠ 1 → isInTri 1 4 6 u.1 v.1 = false) ∧
        (rstar.1 ≠ 2 → isInTri 7 2 5 u.1 v.1 = false)) ↔
      ((k333PartTris rstar.1).filter fun t =>
        isInTri t.1 t.2.1 t.2.2 u.1 v.1).length = 1 := by
  decide

theorem k333_part_disjoint_removed :
    ∀ rstar : Fin 3, ∀ t ∈ k333PartTris rstar.1, ∀ u v : Fin 9,
      isInTri t.1 t.2.1 t.2.2 u.1 v.1 = true →
        (rstar.1 ≠ 0 → isInTri 0 3 6 u.1 v.1 = false) ∧
        (rstar.1 ≠ 1 → isInTri 1 4 6 u.1 v.1 = false) ∧
        (rstar.1 ≠ 2 → isInTri 7 2 5 u.1 v.1 = false) := by
  decide

theorem k333_edge26_blocked (len : ℕ) (hlen : 1 ≤ len) (w : ℕ)
    (h2w : k333ClauseAdj len 2 w = true) (h6w : k333ClauseAdj len 6 w = true) :
    (w = 3 ∧ isInTri 0 3 6 3 6 = true) ∨
    (w = 4 ∧ 2 ≤ len ∧ isInTri 1 4 6 4 6 = true) ∨
    (w = 5 ∧ 3 ≤ len ∧ isInTri 7 2 5 2 5 = true) := by
  have h2w' : k333Adj 2 w = true := by
    simp only [k333ClauseAdj, Bool.and_eq_true] at h2w; exact h2w.1.1
  have h6w' : k333Adj 6 w = true := by
    simp only [k333ClauseAdj, Bool.and_eq_true] at h6w; exact h6w.1.1
  have hw_cases : w = 3 ∨ w = 4 ∨ w = 5 := by
    simp only [k333Adj, decide_eq_true_eq] at h2w' h6w'
    omega
  rcases hw_cases with rfl | rfl | rfl
  · left; exact ⟨rfl, by decide⟩
  · right; left
    refine ⟨rfl, ?_, by decide⟩
    by_contra hlt
    have hle1 : len ≤ 1 := by omega
    simp [k333ClauseAdj, hle1, isInTri] at h6w
  · right; right
    refine ⟨rfl, ?_, by decide⟩
    by_contra hlt
    have hle2 : len ≤ 2 := by omega
    simp [k333ClauseAdj, hle2, isInTri] at h2w

theorem mem_torusPortAll_iff (occ p : ℕ) :
    p ∈ torusPortAll occ ↔
      p = 4 * (4 * occ) ∨ p = 4 * (4 * occ + 1) ∨
      p = 4 * (4 * occ) + 1 ∨ p = 4 * (4 * occ + 1) + 3 := by
  simp [torusPortAll]

theorem mem_torusUpTri_iff (x y z : ℕ) :
    z ∈ torusUpTri x y ↔
      z = (torusUpTri x y).getD 0 0 ∨ z = (torusUpTri x y).getD 1 0 ∨
      z = (torusUpTri x y).getD 2 0 := by
  simp [torusUpTri]

theorem mem_torusDownTri_iff (x y z : ℕ) :
    z ∈ torusDownTri x y ↔
      z = (torusDownTri x y).getD 0 0 ∨ z = (torusDownTri x y).getD 1 0 ∨
      z = (torusDownTri x y).getD 2 0 := by
  simp [torusDownTri]

theorem isInTri_eq_true_iff (a b c u v : ℕ) :
    isInTri a b c u v = true ↔ (u = a ∨ u = b ∨ u = c) ∧ (v = a ∨ v = b ∨ v = c) ∧ u ≠ v := by
  simp [isInTri]

theorem isSameTri_eq_true_iff (a b c p q r : ℕ) :
    isSameTri a b c p q r = true ↔
      (a = p ∨ a = q ∨ a = r) ∧ (b = p ∨ b = q ∨ b = r) ∧ (c = p ∨ c = q ∨ c = r) ∧
      (p = a ∨ p = b ∨ p = c) ∧ (q = a ∨ q = b ∨ q = c) ∧ (r = a ∨ r = b ∨ r = c) := by
  simp [isSameTri]

theorem torusTriClass_eq_true_iff (p q r : ℕ) :
    torusTriClass p q r = true ↔
      let x := p / 4; let y := p % 4
      let eq3 (l : List ℕ) := isSameTri p q r (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) = true
      eq3 (torusUpTri x y) ∨ eq3 (torusUpTri ((x + 11) % 12) y) ∨
      eq3 (torusUpTri x ((y + 3) % 4)) ∨ eq3 (torusDownTri x y) ∨
      eq3 (torusDownTri ((x + 11) % 12) y) ∨ eq3 (torusDownTri ((x + 11) % 12) ((y + 1) % 4)) := by
  simp only [torusTriClass, Bool.or_eq_true, or_assoc]

theorem k333Adj_bounds {u v : ℕ} (h : k333Adj u v = true) : u < 9 ∧ v < 9 ∧ u ≠ v := by
  simp only [k333Adj, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, fun heq => h.2.2 (by rw [heq])⟩

theorem k333ClauseAdj_to_k333Adj {len u v : ℕ} (h : k333ClauseAdj len u v = true) :
    k333Adj u v = true := by
  simp only [k333ClauseAdj, Bool.and_eq_true] at h
  exact h.1.1

theorem k333ClauseAdj_bounds {len u v : ℕ} (h : k333ClauseAdj len u v = true) :
    u < 9 ∧ v < 9 ∧ u ≠ v :=
  k333Adj_bounds (k333ClauseAdj_to_k333Adj h)

theorem k333ClauseAdj_eq_true_iff (len u v : ℕ) :
    k333ClauseAdj len u v = true ↔
      k333Adj u v = true ∧ (len ≤ 2 → isInTri 7 2 5 u v = false) ∧
      (len ≤ 1 → isInTri 1 4 6 u v = false) := by
  unfold k333ClauseAdj
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨ha, h2⟩, h1⟩
    refine ⟨ha, fun hle2 => ?_, fun hle1 => ?_⟩
    · simp only [hle2, ↓reduceIte, Bool.not_eq_true'] at h2; exact h2
    · simp only [hle1, ↓reduceIte, Bool.not_eq_true'] at h1; exact h1
  · rintro ⟨ha, h2, h1⟩
    refine ⟨⟨ha, ?_⟩, ?_⟩
    · split_ifs with hle2
      · rw [h2 hle2]; rfl
      · rfl
    · split_ifs with hle1
      · rw [h1 hle1]; rfl
      · rfl

theorem k333ClauseAdj_eq_bool (len u v : ℕ) :
    k333ClauseAdj len u v =
      ((k333Adj u v && (if decide (len ≤ 2) then !isInTri 7 2 5 u v else true)) &&
        (if decide (len ≤ 1) then !isInTri 1 4 6 u v else true)) := by
  unfold k333ClauseAdj; simp only [decide_eq_true_eq]

theorem k333ClauseAdj_two_six (len : ℕ) : k333ClauseAdj len 2 6 = true := by
  simp [k333ClauseAdj, k333Adj, isInTri]

theorem mem_k333Edges_of_lt {u v : ℕ} (h : u < v) (ha : k333Adj u v = true) :
    (u, v) ∈ k333Edges := by
  obtain ⟨hu, hv, _⟩ := k333Adj_bounds ha
  simp only [k333Edges, List.mem_flatMap, List.mem_range]
  exact ⟨u, hu, v, hv, by simp [h, ha]⟩

theorem k333PortVert_lt_nine (r pos : ℕ) : k333PortVert r pos < 9 := by
  unfold k333PortVert; split_ifs <;> omega

theorem k333PortVert_inj {r pos1 pos2 : ℕ} (h1 : pos1 < 3) (h2 : pos2 < 3)
    (h : k333PortVert r pos1 = k333PortVert r pos2) : pos1 = pos2 := by
  unfold k333PortVert at h; split_ifs at h <;> omega

theorem k333PortVert_ne_two_six (r pos1 pos2 : ℕ) :
    ¬ (k333PortVert r pos1 = 2 ∧ k333PortVert r pos2 = 6) := by
  unfold k333PortVert; rintro ⟨h1, h2⟩; split_ifs at h1 h2 <;> omega

theorem k333PortVert_disjoint_other {r a b : ℕ} (hr : r < 3)
    (ha : a = k333PortVert r 0 ∨ a = k333PortVert r 1 ∨ a = k333PortVert r 2)
    (hb : b = k333PortVert r 0 ∨ b = k333PortVert r 1 ∨ b = k333PortVert r 2) (hne : a ≠ b) :
    (r ≠ 0 → isInTri 0 3 6 a b = false) ∧ (r ≠ 1 → isInTri 1 4 6 a b = false) ∧
    (r ≠ 2 → isInTri 7 2 5 a b = false) := by
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr_cases with rfl | rfl | rfl
  · refine ⟨fun h => (h rfl).elim, fun _ => ?_, fun _ => ?_⟩ <;>
      (rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        simp [k333PortVert, isInTri] at hne ⊢)
  · refine ⟨fun _ => ?_, fun h => (h rfl).elim, fun _ => ?_⟩ <;>
      (rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        simp [k333PortVert, isInTri] at hne ⊢)
  · refine ⟨fun _ => ?_, fun _ => ?_, fun h => (h rfl).elim⟩ <;>
      (rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        simp [k333PortVert, isInTri] at hne ⊢)

theorem computableInPolyTime_k333PortVert :
    ComputableInPolyTime (fun p : ℕ × ℕ => k333PortVert p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold k333PortVert
  have k0 : ComputableInPolyTime (fun _ : ℕ × ℕ => (0 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 0
  have k1 : ComputableInPolyTime (fun _ : ℕ × ℕ => (1 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 1
  have k2 : ComputableInPolyTime (fun _ : ℕ × ℕ => (2 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 2
  have k3 : ComputableInPolyTime (fun _ : ℕ × ℕ => (3 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 3
  have k4 : ComputableInPolyTime (fun _ : ℕ × ℕ => (4 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 4
  have k5 : ComputableInPolyTime (fun _ : ℕ × ℕ => (5 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 5
  have k6 : ComputableInPolyTime (fun _ : ℕ × ℕ => (6 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 6
  have k7 : ComputableInPolyTime (fun _ : ℕ × ℕ => (7 : ℕ))
      (encPair encUnary encUnary) encUnary := .const 7
  have h0 := ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.2 = 0)) _ encBool) k0
    (ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.2 = 1)) _ encBool) k3 k6)
  have h1 := ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.2 = 0)) _ encBool) k1
    (ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.2 = 1)) _ encBool) k4 k6)
  have h2 := ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.2 = 0)) _ encBool) k7
    (ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.2 = 1)) _ encBool) k2 k5)
  have hr1 := ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.1 = 1)) _ encBool) h1 h2
  exact (ComputableInPolyTime.ite' (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ => decide (p.1 = 0)) _ encBool) h0 hr1).of_enc_eq fun p =>
    congrArg _ (by simp only [decide_eq_true_eq])

/-! ### CNF Normalization -/

/-- Literal equality test. -/
@[expose] def litEq (a b : Literal ℕ) : Bool :=
  decide (a.1 = b.1) && (a.2 == b.2)

/-- Test whether a clause contains complementary literals `(v, true)` and `(v, false)`. -/
@[expose] def clauseHasCompl (c : Clause ℕ) : Bool :=
  c.any fun l => c.any fun l' => decide (l.1 = l'.1) && !(l.2 == l'.2)

/-- Deduplicate a clause of length at most 3. -/
@[expose] def dedupClause3 (c : Clause ℕ) : Clause ℕ :=
  let l0 := c.getD 0 (0, false)
  let l1 := c.getD 1 (0, false)
  let l2 := c.getD 2 (0, false)
  if c.length = 0 then []
  else if c.length = 1 then [l0]
  else if c.length = 2 then
    if litEq l0 l1 then [l0] else [l0, l1]
  else
    let ab := if litEq l0 l1 then [l0] else [l0, l1]
    if litEq l0 l2 || litEq l1 l2 then ab else ab ++ [l2]

/-- Normalize a width-3 CNF by dropping tautological clauses and deduplicating each clause. -/
@[expose] def normCNF (φ : CNF ℕ) : CNF ℕ :=
  (φ.filter fun c => !clauseHasCompl c).map dedupClause3

private theorem clauseHasCompl_true_eval {c : Clause ℕ} (h : clauseHasCompl c = true)
    (σ : ℕ → Bool) : c.eval σ = true := by
  simp only [clauseHasCompl, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, beq_eq_false_iff_ne] at h
  rcases h with ⟨l, hl, l', hl', hv, hb⟩
  rw [Clause.eval_eq_true_iff]
  by_cases hs : σ l.1 = l.2
  · exact ⟨l, hl, hs⟩
  · refine ⟨l', hl', ?_⟩
    rw [← hv]
    cases h1 : σ l.1 <;> cases h2 : l.2 <;> cases h3 : l'.2 <;> simp_all

private theorem dedupClause3_eval {c : Clause ℕ} (hc : c.length ≤ 3) (σ : ℕ → Bool) :
    (dedupClause3 c).eval σ = c.eval σ := by
  match c, hc with
  | [], _ => rfl
  | [a], _ => simp [dedupClause3]
  | [a, b], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    by_cases h : litEq a b = true
    · have hab : a = b := by
        simp only [litEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        exact Prod.ext h.1 h.2
      subst hab; simp [h]
    · simp [h]
  | [a, b, d], _ =>
    have hlit : ∀ x y : Literal ℕ, litEq x y = true → x = y := fun x y h => by
      simp only [litEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact Prod.ext h.1 h.2
    simp only [dedupClause3, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ, show ¬ (3 : ℕ) = 0 by decide, show ¬ (3 : ℕ) = 1 by decide,
      show ¬ (3 : ℕ) = 2 by decide, ↓reduceIte]
    cases h1 : litEq a b
    · cases h2 : litEq a d
      · cases h3 : litEq b d
        · simp [Clause.eval_cons]
        · have := hlit b d h3; subst this
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_true, Clause.eval_cons,
            Clause.eval_nil]
          cases Literal.eval σ a <;> cases Literal.eval σ b <;> decide
      · have := hlit a d h2; subst this
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_or, Clause.eval_cons, Clause.eval_nil]
        cases Literal.eval σ a <;> cases Literal.eval σ b <;> decide
    · have := hlit a b h1; subst this
      cases h2 : litEq a d
      · simp [Clause.eval_cons]
      · have := hlit a d h2; subst this; simp [Clause.eval_cons]

theorem normCNF_eval {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) (σ : ℕ → Bool) :
    (normCNF φ).eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  constructor
  · intro h c hc
    by_cases hcomp : clauseHasCompl c = true
    · exact clauseHasCompl_true_eval hcomp σ
    · have hmem : dedupClause3 c ∈ normCNF φ :=
        List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hcomp]⟩, rfl⟩
      have hev := h _ hmem
      rwa [dedupClause3_eval (hφ c hc)] at hev
  · intro h c hc
    rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
    have hc0' := (List.mem_filter.1 hc0).1
    rw [dedupClause3_eval (hφ c0 hc0')]
    exact h c0 hc0'

private theorem dedupClause3_len_le {c : Clause ℕ} (hc : c.length ≤ 3) :
    (dedupClause3 c).length ≤ 3 := by
  match c, hc with
  | [], _ => simp [dedupClause3]
  | [a], _ => simp [dedupClause3]
  | [a, b], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil]
    split_ifs <;> simp
  | [a, b, d], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil]
    split_ifs <;> simp

private theorem dedupClause3_sublist {c : Clause ℕ} (hc : c.length ≤ 3) :
    (dedupClause3 c).Sublist c := by
  match c, hc with
  | [], _ => simp [dedupClause3]
  | [a], _ => simp [dedupClause3]
  | [a, b], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ, show ¬ (2 : ℕ) = 0 by decide, show ¬ (2 : ℕ) = 1 by decide, ↓reduceIte]
    split_ifs <;> simp
  | [a, b, d], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ, show ¬ (3 : ℕ) = 0 by decide, show ¬ (3 : ℕ) = 1 by decide,
      show ¬ (3 : ℕ) = 2 by decide, ↓reduceIte]
    split_ifs <;> simp

private theorem dedupClause3_nodup_vars {c : Clause ℕ} (hc : c.length ≤ 3)
    (hnc : clauseHasCompl c = false) : ((dedupClause3 c).map Prod.fst).Nodup := by
  have hsame : ∀ a ∈ c, ∀ b ∈ c, a.1 = b.1 → a.2 = b.2 := by
    intro a ha b hb hv
    by_contra hne
    have : clauseHasCompl c = true := by
      simp only [clauseHasCompl, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq, beq_eq_false_iff_ne]
      exact ⟨a, ha, b, hb, hv, hne⟩
    simp [this] at hnc
  match c, hc with
  | [], _ => simp [dedupClause3]
  | [a], _ => simp [dedupClause3]
  | [a, b], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ, show ¬ (2 : ℕ) = 0 by decide, show ¬ (2 : ℕ) = 1 by decide, ↓reduceIte]
    split_ifs with h
    · simp
    · rw [List.map_cons, List.map_singleton, List.nodup_cons]
      refine ⟨fun hm => h ?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton] at hm
      simp only [litEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨hm, hsame a (by simp) b (by simp) hm⟩
  | [a, b, d], _ =>
    simp only [dedupClause3, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ, show ¬ (3 : ℕ) = 0 by decide, show ¬ (3 : ℕ) = 1 by decide,
      show ¬ (3 : ℕ) = 2 by decide, ↓reduceIte]
    have hneq_lit : ∀ x ∈ ([a, b, d] : Clause ℕ), ∀ y ∈ ([a, b, d] : Clause ℕ),
        litEq x y = false → x.1 ≠ y.1 := by
      intro x hx y hy hne heq
      have ht : litEq x y = true := by
        simp only [litEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨heq, hsame x hx y hy heq⟩
      rw [hne] at ht; simp at ht
    cases h1 : litEq a b <;> cases h2 : litEq a d <;> cases h3 : litEq b d
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, not_false_eq_true, and_true, not_or]
      exact ⟨⟨hneq_lit a (by simp) b (by simp) h1, hneq_lit a (by simp) d (by simp) h2⟩,
        hneq_lit b (by simp) d (by simp) h3⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_true, List.map_cons, List.map_nil,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      exact hneq_lit a (by simp) b (by simp) h1
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_or, List.map_cons, List.map_nil,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      exact hneq_lit a (by simp) b (by simp) h1
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_or, List.map_cons, List.map_nil,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      exact hneq_lit a (by simp) b (by simp) h1
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.or_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, not_false_eq_true, and_true]
      exact hneq_lit a (by simp) d (by simp) h2
    · simp
    · simp
    · simp

theorem normCNF_count_le {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) (v : ℕ) :
    (normCNF φ).vars.count v ≤ φ.vars.count v := by
  have hsub : (normCNF φ).vars.Sublist φ.vars := by
    unfold normCNF CNF.vars
    have hfl : ((φ.filter fun c => !clauseHasCompl c).map dedupClause3).flatten.Sublist
        φ.flatten := by
      have h1 : ∀ l : CNF ℕ, (∀ c ∈ l, c.length ≤ 3) →
          (l.map dedupClause3).flatten.Sublist l.flatten := by
        intro l hl
        induction l with
        | nil => simp
        | cons c l ih =>
          simp only [List.map_cons, List.flatten_cons]
          exact List.Sublist.append (dedupClause3_sublist (hl c List.mem_cons_self))
            (ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
      have h2 := h1 (φ.filter fun c => !clauseHasCompl c)
        (fun c hc => hφ c (List.mem_filter.1 hc).1)
      have h3 : (φ.filter fun c => !clauseHasCompl c).flatten.Sublist φ.flatten := by
        have hfl_sub : ∀ (l₁ l₂ : CNF ℕ), l₁.Sublist l₂ → l₁.flatten.Sublist l₂.flatten := by
          intro l₁ l₂ hs
          induction hs with
          | slnil => exact List.Sublist.slnil
          | cons _ _ ih => exact ih.trans (List.sublist_append_right _ _)
          | cons_cons _ _ ih => exact List.Sublist.append (List.Sublist.refl _) ih
        exact hfl_sub _ _ (List.filter_sublist)
      exact h2.trans h3
    exact hfl.map Prod.fst
  exact hsub.count_le v

/-- Normalized-CNF invariants produced by `normCNF`. -/
structure NormProps (ψ : CNF ℕ) : Prop where
  clause_len_pos : ∀ c ∈ ψ, 1 ≤ c.length
  clause_len_le : ∀ c ∈ ψ, c.length ≤ 3
  clause_nodup : ∀ c ∈ ψ, (c.map Prod.fst).Nodup
  var_count_le : ∀ v : ℕ, ψ.vars.count v ≤ 3

theorem normCNF_props {φ : CNF ℕ}
    (hsyn : (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v, φ.vars.count v ≤ 3))
    (hne : (normCNF φ).any List.isEmpty = false) :
    NormProps (normCNF φ) where
  clause_len_pos := by
    intro c hc
    by_contra h0
    have he : c.isEmpty = true := List.isEmpty_iff_length_eq_zero.2 (by omega)
    have : (normCNF φ).any List.isEmpty = true := List.any_eq_true.2 ⟨c, hc, he⟩
    simp [this] at hne
  clause_len_le := by
    intro c hc
    rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
    exact dedupClause3_len_le (hsyn.1 c0 (List.mem_filter.1 hc0).1)
  clause_nodup := by
    intro c hc
    rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
    have hf := List.mem_filter.1 hc0
    exact dedupClause3_nodup_vars (hsyn.1 c0 hf.1) (by simpa using hf.2)
  var_count_le := fun v => (normCNF_count_le hsyn.1 v).trans (hsyn.2 v)

private theorem computableInPolyTime_clauseHasCompl :
    ComputableInPolyTime clauseHasCompl (encClause encNat) encBool := by
  have hinner : ComputableInPolyTime
      (fun p : (Clause ℕ × Literal ℕ) × Literal ℕ =>
        decide (p.1.2.1 = p.2.1) && !(p.1.2.2 == p.2.2))
      (encPair (encPair (encClause encNat) (encPair encNat encBool)) (encPair encNat encBool))
      encBool := by fun_prop
  have hany1 : ComputableInPolyTime
      (fun p : Clause ℕ × Literal ℕ =>
        p.1.any fun l' => decide (p.2.1 = l'.1) && !(p.2.2 == l'.2))
      (encPair (encClause encNat) (encPair encNat encBool)) encBool :=
    ComputableInPolyTime.anyWithInput (by fun_prop) hinner
  exact ComputableInPolyTime.anyWithInput (by fun_prop) hany1

private theorem computableInPolyTime_litEq :
    ComputableInPolyTime (fun p : Literal ℕ × Literal ℕ => litEq p.1 p.2)
      (encPair (encPair encNat encBool) (encPair encNat encBool)) encBool := by
  unfold litEq; fun_prop

private def dedupPair (p : Literal ℕ × Literal ℕ) : Clause ℕ :=
  if litEq p.1 p.2 then [p.1] else [p.1, p.2]

private def dedupTriple (p : (Literal ℕ × Literal ℕ) × Literal ℕ) : Clause ℕ :=
  if litEq p.1.1 p.2 || litEq p.1.2 p.2 then dedupPair p.1 else dedupPair p.1 ++ [p.2]

private theorem computableInPolyTime_dedupPair :
    ComputableInPolyTime dedupPair
      (encPair (encPair encNat encBool) (encPair encNat encBool))
      (encList (encPair encNat encBool)) := by
  have hf : ComputableInPolyTime (fun p : Literal ℕ × Literal ℕ => p.1)
      (encPair (encPair encNat encBool) (encPair encNat encBool)) (encPair encNat encBool) :=
    ComputableInPolyTime.fst _ _
  have hs : ComputableInPolyTime (fun p : Literal ℕ × Literal ℕ => p.2)
      (encPair (encPair encNat encBool) (encPair encNat encBool)) (encPair encNat encBool) :=
    ComputableInPolyTime.snd _ _
  have hnil : ComputableInPolyTime (fun _ : Literal ℕ × Literal ℕ => ([] : List (Literal ℕ)))
      (encPair (encPair encNat encBool) (encPair encNat encBool))
      (encList (encPair encNat encBool)) := .const []
  have h1 := ComputableInPolyTime.cons' hf hnil
  have h2 := ComputableInPolyTime.cons' hf (ComputableInPolyTime.cons' hs hnil)
  exact (ComputableInPolyTime.ite' computableInPolyTime_litEq h1 h2).of_enc_eq fun p =>
    congrArg _ (by rfl)

private theorem computableInPolyTime_dedupTriple :
    ComputableInPolyTime dedupTriple
      (encPair (encPair (encPair encNat encBool) (encPair encNat encBool))
        (encPair encNat encBool))
      (encList (encPair encNat encBool)) := by
  have hfst : ComputableInPolyTime
      (fun p : (Literal ℕ × Literal ℕ) × Literal ℕ => p.1)
      (encPair (encPair (encPair encNat encBool) (encPair encNat encBool))
        (encPair encNat encBool))
      (encPair (encPair encNat encBool) (encPair encNat encBool)) :=
    ComputableInPolyTime.fst _ _
  have hsnd : ComputableInPolyTime
      (fun p : (Literal ℕ × Literal ℕ) × Literal ℕ => p.2)
      (encPair (encPair (encPair encNat encBool) (encPair encNat encBool))
        (encPair encNat encBool))
      (encPair encNat encBool) :=
    ComputableInPolyTime.snd _ _
  have hab := computableInPolyTime_dedupPair.comp hfst
  have hnil : ComputableInPolyTime
      (fun _ : (Literal ℕ × Literal ℕ) × Literal ℕ => ([] : List (Literal ℕ)))
      (encPair (encPair (encPair encNat encBool) (encPair encNat encBool))
        (encPair encNat encBool))
      (encList (encPair encNat encBool)) := .const []
  have hsing2 := ComputableInPolyTime.cons' hsnd hnil
  have hab2 := (ComputableInPolyTime.listAppend (encPair encNat encBool)).comp (hab.prod hsing2)
  have h02 := computableInPolyTime_litEq.comp
    (((ComputableInPolyTime.fst _ _).comp hfst).prod hsnd)
  have h12 := computableInPolyTime_litEq.comp
    (((ComputableInPolyTime.snd _ _).comp hfst).prod hsnd)
  have hor : ComputableInPolyTime
      (fun p : (Literal ℕ × Literal ℕ) × Literal ℕ => litEq p.1.1 p.2 || litEq p.1.2 p.2)
      (encPair (encPair (encPair encNat encBool) (encPair encNat encBool))
        (encPair encNat encBool)) encBool :=
    (ComputableInPolyTime.ite' h02 (.const true) h12).of_enc_eq fun p => congrArg _ (by
      dsimp only [Function.comp_apply]; by_cases h : litEq p.1.1 p.2 = true <;> simp [h])
  exact (ComputableInPolyTime.ite' hor hab hab2).of_enc_eq fun p => congrArg _ (by rfl)

private theorem computableInPolyTime_dedupClause3 :
    ComputableInPolyTime dedupClause3 (encClause encNat) (encClause encNat) := by
  have hl0 : ComputableInPolyTime (fun c : Clause ℕ => c.getD 0 (0, false))
      (encList (encPair encNat encBool)) (encPair encNat encBool) :=
    ComputableInPolyTime.listGetDWithInput .id' (.const 0) (0, false)
  have hl1 : ComputableInPolyTime (fun c : Clause ℕ => c.getD 1 (0, false))
      (encList (encPair encNat encBool)) (encPair encNat encBool) :=
    ComputableInPolyTime.listGetDWithInput .id' (.const 1) (0, false)
  have hl2 : ComputableInPolyTime (fun c : Clause ℕ => c.getD 2 (0, false))
      (encList (encPair encNat encBool)) (encPair encNat encBool) :=
    ComputableInPolyTime.listGetDWithInput .id' (.const 2) (0, false)
  have hlen : ComputableInPolyTime (fun c : Clause ℕ => c.length)
      (encList (encPair encNat encBool)) encUnary :=
    ComputableInPolyTime.length_list (encPair encNat encBool)
  have hnil : ComputableInPolyTime (fun _ : Clause ℕ => ([] : List (Literal ℕ)))
      (encList (encPair encNat encBool)) (encList (encPair encNat encBool)) := .const []
  have hsing0 := ComputableInPolyTime.cons' hl0 hnil
  have hc2_branch := computableInPolyTime_dedupPair.comp (hl0.prod hl1)
  have hc3_branch := computableInPolyTime_dedupTriple.comp ((hl0.prod hl1).prod hl2)
  have hlen2 : ComputableInPolyTime (fun c : Clause ℕ => decide (c.length = 2))
      (encList (encPair encNat encBool)) encBool := by fun_prop
  have hlen1 : ComputableInPolyTime (fun c : Clause ℕ => decide (c.length = 1))
      (encList (encPair encNat encBool)) encBool := by fun_prop
  have hlen0 : ComputableInPolyTime (fun c : Clause ℕ => decide (c.length = 0))
      (encList (encPair encNat encBool)) encBool := by fun_prop
  have hc2 := ComputableInPolyTime.ite' hlen2 hc2_branch hc3_branch
  have hc1 := ComputableInPolyTime.ite' hlen1 hsing0 hc2
  have hc0 := ComputableInPolyTime.ite' hlen0 hnil hc1
  exact hc0.of_enc_eq fun c => congrArg _ (by
    dsimp only [dedupClause3, dedupTriple, dedupPair, Function.comp_apply]
    simp only [decide_eq_true_eq])

theorem computableInPolyTime_normCNF :
    ComputableInPolyTime normCNF encCNF encCNF := by
  unfold normCNF
  have hfilt : ComputableInPolyTime (fun φ : CNF ℕ => φ.filter fun c => !clauseHasCompl c)
      encCNF encCNF := by
    have := computableInPolyTime_clauseHasCompl
    exact ComputableInPolyTime.filter (by fun_prop)
  have hmap : ComputableInPolyTime (List.map dedupClause3) encCNF encCNF :=
    ComputableInPolyTime.map computableInPolyTime_dedupClause3
  exact hmap.comp hfilt

end Cslib.Complexity
