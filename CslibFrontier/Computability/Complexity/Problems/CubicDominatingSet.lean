module

public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Problems.CubicCapGadget

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# NP-Completeness of Connected Cubic Dominating Set

Formalizes the `NP`-completeness of `CslibFrontier.Complexity.CubicDominatingSet` — the dominating
set decision problem restricted to connected $3$-regular (cubic) finite simple graphs — via a
polynomial-time many-one reduction from `Cslib.Complexity.ThreeSAT` using the $7$-vertex $1$-port
cubic degree-cap gadget $W_7$ from `CslibFrontier.Computability.Complexity.Problems.CubicCapGadget`.

## Main definitions

- `CslibFrontier.Complexity.k4Graph`: connected cubic graph $K_4$ for trivial `ThreeSAT` instances.
- `CslibFrontier.Complexity.cubicVarV`, `CslibFrontier.Complexity.cubicClauseV`: vertex identifiers
  for the $C_{3m}$ variable rings and clause vertices.
- `CslibFrontier.Complexity.toCubicDominatingSet`: polynomial-time reduction from `ThreeSAT` to
  `CubicDominatingSet`.

## Main results

- `CslibFrontier.Complexity.toCubicDominatingSet_mem_iff`: correctness of the reduction.
- `CslibFrontier.Complexity.computableInPolyTime_toCubicDominatingSet`: polynomial-time
  computability.
- `CslibFrontier.Complexity.polyTimeReducible_ThreeSAT_CubicDominatingSet`:
  `PolyTimeReducible encCNF encDominatingSet ThreeSAT CubicDominatingSet`.
- `CslibFrontier.Complexity.CubicDominatingSet_npHard`,
  `CslibFrontier.Complexity.CubicDominatingSet_npComplete`: `CubicDominatingSet` is `NP`-complete.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Trivial Instance Graph $K_4$ and Vertex Encodings -/

/-- Connected cubic graph $K_4$ used for trivial `ThreeSAT` instances. -/
@[expose]
def k4Graph : Graph :=
  ⟨[0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩

private lemma k4Graph_connected : k4Graph.induced.Connected := by
  refine k4Graph.induced.connected_iff_exists_forall_reachable.mpr ⟨⟨0, by decide⟩, fun ⟨v,
    hv⟩ ↦ ?_⟩
  rcases (by simpa [k4Graph] using hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) with rfl | rfl | rfl | rfl
  · exact _root_.SimpleGraph.Reachable.refl _
  all_goals
    exact _root_.SimpleGraph.Adj.reachable
      (by simp [k4Graph, Graph.induced_adj, Graph.toSimpleGraph_adj])

private lemma list_getD_eq {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by simp [List.getD_eq_getElem?_getD, hi]

private lemma k4Graph_cubic (v : {w // w ∈ k4Graph.vertices}) :
    k4Graph.induced.degree v = 3 := by
  rw [← cubicGraphDegBool_eq_degree]; rcases v with ⟨v, hv⟩
  rcases (by simpa [k4Graph] using hv : v = 0 ∨ v = 1 ∨ v = 2 ∨
    v = 3) with rfl | rfl | rfl | rfl <;>
    (dsimp only; clear hv; decide)

/-- `(k4Graph, 1)` is a yes-instance of `CubicDominatingSet`. -/
theorem k4Graph_mem_one : (⟨k4Graph, 1⟩ : DominatingSetInstance) ∈ CubicDominatingSet := by
  rw [mem_CubicDominatingSet_iff]
  refine ⟨k4Graph_connected, k4Graph_cubic, mem_DominatingSet_iff.mpr
    ⟨{0}, fun v hv ↦ by simp [k4Graph, Finset.mem_singleton.mp hv], fun v hv ↦ ?_, by simp⟩⟩
  rcases (by simpa [k4Graph] using hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) with rfl | rfl | rfl | rfl
  · left; simp
  all_goals right; exact ⟨0, by simp, by simp [k4Graph, Graph.toSimpleGraph_adj]⟩

private lemma k4Graph_not_mem_zero :
    (⟨k4Graph, 0⟩ : DominatingSetInstance) ∉ CubicDominatingSet := by
  intro h; rw [mem_CubicDominatingSet_iff] at h
  rcases mem_DominatingSet_iff.mp h.2.2 with ⟨S, _, hS, hcard⟩
  have hS0 : S = ∅ := Finset.card_eq_zero.mp hcard; subst hS0
  have := hS 0 (by simp [k4Graph]); simp at this

/-- Vertex identifier for variable ring `i`, clause copy `j`, role `r ∈ {0,1,2}` (`t, f, g`). -/
@[expose]
def cubicVarV (m i j r : ℕ) : ℕ := 4 * (3 * (i * m + j) + r)

/-- Vertex identifier for clause `j`. -/
@[expose]
def cubicClauseV (j : ℕ) : ℕ := 4 * j + 1

private lemma cubicVarV_injective {m i₁ j₁ r₁ i₂ j₂ r₂ : ℕ}
    (hj₁ : j₁ < m) (hj₂ : j₂ < m) (hr₁ : r₁ < 3) (hr₂ : r₂ < 3)
    (h : cubicVarV m i₁ j₁ r₁ = cubicVarV m i₂ j₂ r₂) :
    i₁ = i₂ ∧ j₁ = j₂ ∧ r₁ = r₂ := by
  unfold cubicVarV at h
  have h1 : 3 * (i₁ * m + j₁) + r₁ = 3 * (i₂ * m + j₂) + r₂ := by omega
  have hr : r₁ = r₂ := by omega
  have h2 : i₁ * m + j₁ = i₂ * m + j₂ := by omega
  have hi : i₁ = i₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (i₁ + 1) * m ≤ i₂ * m := Nat.mul_le_mul_right m hlt
      rw [Nat.succ_mul] at this; omega
    · have : (i₂ + 1) * m ≤ i₁ * m := Nat.mul_le_mul_right m hgt
      rw [Nat.succ_mul] at this; omega
  subst hi
  exact ⟨rfl, by omega, hr⟩

/-! ### 2. Base Graph Construction and Reduction -/

/-- Normalized clause list of a valid nonempty `ThreeSAT` formula: original clauses deduplicated,
followed by `n` tautological connectivity clauses `(v_i ∨ ¬v_i ∨ v_{(i+1)%n})`. -/
private def normClauses (φ : CNF ℕ) : CNF ℕ :=
  let vars := dedupList φ.vars
  let n := vars.length
  φ.map dedupList ++
    (polyRange n).map fun i ↦
      dedupList [(vars.getD i 0, true), (vars.getD i 0, false),
        (vars.getD (if i + 1 < n then i + 1 else 0) 0, true)]

/-- Base (uncapped, max-degree-3) graph constructed from `vars` and `clauses`, using a $C_{3m}$
cycle `(0, 1, 2)` for each variable ring. -/
private def baseGraphOf (vars : List ℕ) (clauses : CNF ℕ) : Graph :=
  let n := vars.length
  let m := clauses.length
  let varVerts := (polyRange n).flatMap fun i ↦
    (polyRange m).flatMap fun j ↦
      [cubicVarV m i j 0, cubicVarV m i j 1, cubicVarV m i j 2]
  let clVerts := (polyRange m).map cubicClauseV
  let ringEdges := (polyRange n).flatMap fun i ↦
    (polyRange m).flatMap fun j ↦
      let jnext := if j + 1 < m then j + 1 else 0
      [(cubicVarV m i j 0, cubicVarV m i j 1),
       (cubicVarV m i j 1, cubicVarV m i j 2),
       (cubicVarV m i j 2, cubicVarV m i jnext 0)]
  let clEdges := (polyRange n).flatMap fun i ↦
    (polyRange m).flatMap fun j ↦
      let v := vars.getD i 0
      let c := clauses.getD j []
      (if c.any fun l ↦ decide (l = (v, true)) then
        [(cubicClauseV j, cubicVarV m i j 0)] else []) ++
      (if c.any fun l ↦ decide (l = (v, false)) then
        [(cubicClauseV j, cubicVarV m i j 1)] else [])
  ⟨varVerts ++ clVerts, ringEdges ++ clEdges⟩

/-- Validity check for a nonempty 3-CNF without empty clauses. -/
private def isNontrivialThreeCNF (φ : CNF ℕ) : Bool :=
  decide (0 < φ.length) && φ.all fun c ↦ decide (0 < c.length) && decide (c.length ≤ 3)

/-- The polynomial-time reduction from `ThreeSAT` to `CubicDominatingSet`. -/
def toCubicDominatingSet (φ : CNF ℕ) : DominatingSetInstance :=
  if φ.isEmpty then
    ⟨k4Graph, 1⟩
  else if !isNontrivialThreeCNF φ then
    ⟨k4Graph, 0⟩
  else
    let vars := dedupList φ.vars
    let clauses := normClauses φ
    let B := baseGraphOf vars clauses
    let T := (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum
    ⟨cappedGraphOf B, vars.length * clauses.length + 2 * T⟩

/-! ### 3. Base Graph Structure, Degree Bounds, and Connectedness -/

private lemma baseGraphOf_vertices_nodup (vars : List ℕ) (clauses : CNF ℕ) :
    (baseGraphOf vars clauses).vertices.Nodup := by
  unfold baseGraphOf
  simp only [polyRange_eq_range]
  set n := vars.length; set m := clauses.length
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun i _ ↦ ?_, ?_⟩
    · refine List.nodup_flatMap.mpr ⟨fun j hj ↦ ?_, ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          not_false_eq_true, List.nodup_nil, and_true]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro h; have := (cubicVarV_injective (List.mem_range.mp hj) (List.mem_range.mp hj)
            (by omega) (by omega) h).2.2; omega
        · intro h; have := (cubicVarV_injective (List.mem_range.mp hj) (List.mem_range.mp hj)
            (by omega) (by omega) h).2.2; omega
        · intro h; have := (cubicVarV_injective (List.mem_range.mp hj) (List.mem_range.mp hj)
            (by omega) (by omega) h).2.2; omega
      · refine List.pairwise_iff_getElem.mpr fun j₁ j₂ hj₁ hj₂ hlt x hx₁ hx₂ ↦ ?_
        simp only [List.getElem_range, List.mem_cons, List.not_mem_nil, or_false] at hx₁ hx₂
        have hj1 : j₁ < m := by rwa [List.length_range] at hj₁
        have hj2 : j₂ < m := by rwa [List.length_range] at hj₂
        rcases hx₁ with rfl | rfl | rfl <;> rcases hx₂ with h | h | h <;>
          have := (cubicVarV_injective hj1 hj2 (by omega) (by omega) h).2.1 <;> omega
    · refine List.pairwise_iff_getElem.mpr fun i₁ i₂ hi₁ hi₂ hlt x hx₁ hx₂ ↦ ?_
      simp only [List.getElem_range, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hx₁ hx₂
      rcases hx₁ with ⟨j₁, hj₁, rfl | rfl | rfl⟩ <;>
        rcases hx₂ with ⟨j₂, hj₂, h | h | h⟩ <;>
        have := (cubicVarV_injective hj₁ hj₂ (by omega) (by omega) h).1 <;> omega
  · exact (List.nodup_range (n := m)).map fun j₁ j₂ h ↦ by unfold cubicClauseV at h; omega
  · intro x hx₁ y hy₂ heq
    subst heq
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx₁
    simp only [List.mem_map, List.mem_range] at hy₂
    rcases hy₂ with ⟨j, _, rfl⟩
    rcases hx₁ with ⟨i, _, k, _, h | h | h⟩ <;> dsimp only [cubicVarV, cubicClauseV] at h <;> omega

private lemma mem_baseGraphOf_vertices {vars : List ℕ} {clauses : CNF ℕ} {w : ℕ} :
    w ∈ (baseGraphOf vars clauses).vertices ↔
      (∃ i < vars.length, ∃ j < clauses.length, ∃ r < 3, w = cubicVarV clauses.length i j r) ∨
      (∃ j < clauses.length, w = cubicClauseV j) := by
  unfold baseGraphOf
  simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro (⟨i, hi, j, hj, rfl | rfl | rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, j, hj, 0, by omega, rfl⟩
    · exact Or.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩
    · exact Or.inl ⟨i, hi, j, hj, 2, by omega, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (⟨i, hi, j, hj, r, hr, rfl⟩ | ⟨j, hj, rfl⟩)
    · left; refine ⟨i, hi, j, hj, ?_⟩; interval_cases r <;> simp
    · right; exact ⟨j, hj, rfl⟩

private lemma baseGraphOf_adj_iff {vars : List ℕ} {clauses : CNF ℕ}
    (_hm : 2 ≤ clauses.length) {u v : ℕ} :
    (baseGraphOf vars clauses).toSimpleGraph.Adj u v ↔
      (∃ i < vars.length, ∃ j < clauses.length,
        (u = cubicVarV clauses.length i j 0 ∧ v = cubicVarV clauses.length i j 1) ∨
        (u = cubicVarV clauses.length i j 1 ∧ v = cubicVarV clauses.length i j 0) ∨
        (u = cubicVarV clauses.length i j 1 ∧ v = cubicVarV clauses.length i j 2) ∨
        (u = cubicVarV clauses.length i j 2 ∧ v = cubicVarV clauses.length i j 1) ∨
        (u = cubicVarV clauses.length i j 2 ∧
          v = cubicVarV clauses.length i (if j + 1 < clauses.length then j + 1 else 0) 0) ∨
        (u = cubicVarV clauses.length i (if j + 1 < clauses.length then j + 1 else 0) 0 ∧
          v = cubicVarV clauses.length i j 2)) ∨
      (∃ i < vars.length, ∃ j < clauses.length,
        ((vars.getD i 0, true) ∈ clauses.getD j [] ∧
          ((u = cubicClauseV j ∧ v = cubicVarV clauses.length i j 0) ∨
           (u = cubicVarV clauses.length i j 0 ∧ v = cubicClauseV j))) ∨
        ((vars.getD i 0, false) ∈ clauses.getD j [] ∧
          ((u = cubicClauseV j ∧ v = cubicVarV clauses.length i j 1) ∨
           (u = cubicVarV clauses.length i j 1 ∧ v = cubicClauseV j)))) := by
  have hmem_e : ∀ a b : ℕ, (a, b) ∈ (baseGraphOf vars clauses).edges ↔
      (∃ i < vars.length, ∃ j < clauses.length,
        (a = cubicVarV clauses.length i j 0 ∧ b = cubicVarV clauses.length i j 1) ∨
        (a = cubicVarV clauses.length i j 1 ∧ b = cubicVarV clauses.length i j 2) ∨
        (a = cubicVarV clauses.length i j 2 ∧
          b = cubicVarV clauses.length i (if j + 1 < clauses.length then j + 1 else 0) 0)) ∨
      (∃ i < vars.length, ∃ j < clauses.length,
        ((vars.getD i 0, true) ∈ clauses.getD j [] ∧
          a = cubicClauseV j ∧ b = cubicVarV clauses.length i j 0) ∨
        ((vars.getD i 0, false) ∈ clauses.getD j [] ∧
          a = cubicClauseV j ∧ b = cubicVarV clauses.length i j 1)) := by
    intro a b; unfold baseGraphOf
    simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    constructor
    · rintro (⟨i, hi, j, hj, h | h | h⟩ | ⟨i, hi, j, hj, h⟩)
      · exact Or.inl ⟨i, hi, j, hj, Or.inl h⟩
      · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl h)⟩
      · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr h)⟩
      · rcases h with h1 | h2
        · split_ifs at h1 with hlt
          · simp only [List.mem_singleton, Prod.mk.injEq] at h1
            obtain ⟨l, hl, hEq⟩ := List.any_eq_true.mp hlt
            rw [decide_eq_true_eq] at hEq; subst hEq
            exact Or.inr ⟨i, hi, j, hj, Or.inl ⟨hl, h1⟩⟩
          · simp at h1
        · split_ifs at h2 with hlt
          · simp only [List.mem_singleton, Prod.mk.injEq] at h2
            obtain ⟨l, hl, hEq⟩ := List.any_eq_true.mp hlt
            rw [decide_eq_true_eq] at hEq; subst hEq
            exact Or.inr ⟨i, hi, j, hj, Or.inr ⟨hl, h2⟩⟩
          · simp at h2
    · rintro (⟨i, hi, j, hj, h | h | h⟩ | ⟨i, hi, j, hj, ⟨hl, ha, hb⟩ | ⟨hl, ha, hb⟩⟩)
      · exact Or.inl ⟨i, hi, j, hj, Or.inl h⟩
      · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl h)⟩
      · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr h)⟩
      · right; refine ⟨i, hi, j, hj, Or.inl ?_⟩
        have hlt : (clauses.getD j []).any (fun l ↦ decide (l = (vars.getD i 0, true))) = true :=
          List.any_eq_true.mpr ⟨_, hl, by simp⟩
        simp only [hlt, ↓reduceIte, List.mem_singleton, ha, hb]
      · right; refine ⟨i, hi, j, hj, Or.inr ?_⟩
        have hlt : (clauses.getD j []).any (fun l ↦ decide (l = (vars.getD i 0, false))) = true :=
          List.any_eq_true.mpr ⟨_, hl, by simp⟩
        simp only [hlt, ↓reduceIte, List.mem_singleton, ha, hb]
  rw [Graph.toSimpleGraph_adj, hmem_e u v, hmem_e v u]
  constructor
  · rintro ⟨_, h⟩
    rcases h with (⟨i, hi, j, hj, h | h | h⟩ | ⟨i, hi, j, hj, h | h⟩) |
        (⟨i, hi, j, hj, h | h | h⟩ | ⟨i, hi, j, hj, h | h⟩)
    · exact Or.inl ⟨i, hi, j, hj, Or.inl h⟩
    · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact Or.inr ⟨i, hi, j, hj, Or.inl ⟨h.1, Or.inl h.2⟩⟩
    · exact Or.inr ⟨i, hi, j, hj, Or.inr ⟨h.1, Or.inl h.2⟩⟩
    · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
    · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))⟩
    · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))))⟩
    · exact Or.inr ⟨i, hi, j, hj, Or.inl ⟨h.1, Or.inr ⟨h.2.2, h.2.1⟩⟩⟩
    · exact Or.inr ⟨i, hi, j, hj, Or.inr ⟨h.1, Or.inr ⟨h.2.2, h.2.1⟩⟩⟩
  · intro h
    have hne : u ≠ v := by
      rcases h with ⟨i, _, j, hj, h | h | h | h | h | h⟩ |
          ⟨i, _, j, _, ⟨_, h | h⟩ | ⟨_, h | h⟩⟩
      all_goals
        rcases h with ⟨rfl, rfl⟩
        dsimp only [cubicVarV, cubicClauseV]
        omega
    refine ⟨hne, ?_⟩
    rcases h with ⟨i, hi, j, hj, h | h | h | h | h | h⟩ |
        ⟨i, hi, j, hj, ⟨hl, h | h⟩ | ⟨hl, h | h⟩⟩
    · exact Or.inl (Or.inl ⟨i, hi, j, hj, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨i, hi, j, hj, Or.inl ⟨h.2, h.1⟩⟩)
    · exact Or.inl (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl h)⟩)
    · exact Or.inr (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl ⟨h.2, h.1⟩)⟩)
    · exact Or.inl (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr h)⟩)
    · exact Or.inr (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr ⟨h.2, h.1⟩)⟩)
    · exact Or.inl (Or.inr ⟨i, hi, j, hj, Or.inl ⟨hl, h⟩⟩)
    · exact Or.inr (Or.inr ⟨i, hi, j, hj, Or.inl ⟨hl, h.2, h.1⟩⟩)
    · exact Or.inl (Or.inr ⟨i, hi, j, hj, Or.inr ⟨hl, h⟩⟩)
    · exact Or.inr (Or.inr ⟨i, hi, j, hj, Or.inr ⟨hl, h.2, h.1⟩⟩)

private lemma baseGraphOf_degree_bounds {vars : List ℕ} {clauses : CNF ℕ}
    (hnd : vars.Nodup) (hm : 2 ≤ clauses.length)
    (hcl_pos : ∀ c ∈ clauses, 0 < c.length)
    (hcl_le : ∀ c ∈ clauses, c.length ≤ 3)
    (hcl_nd : ∀ c ∈ clauses, c.Nodup)
    (hcl_vars : ∀ c ∈ clauses, ∀ l ∈ c, l.1 ∈ vars)
    {u : ℕ} (hu : u ∈ (baseGraphOf vars clauses).vertices) :
    1 ≤ cubicGraphDegBool (baseGraphOf vars clauses) u ∧
      cubicGraphDegBool (baseGraphOf vars clauses) u ≤ 3 := by
  classical
  let B := baseGraphOf vars clauses
  have hdeg_card : cubicGraphDegBool B u =
      (B.vertices.toFinset.filter fun w ↦ B.toSimpleGraph.Adj u w).card := by
    rw [cubicGraphDegBool_eq_degree B ⟨u, hu⟩, ← _root_.SimpleGraph.card_neighborFinset_eq_degree,
      _root_.SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun x _ ↦ x.1) (fun x hx ↦ ?_)
      (fun _ _ _ _ h ↦ Subtype.ext h) (fun w hw ↦ ?_)
    · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr x.2, (Finset.mem_filter.mp hx).2⟩
    · rcases Finset.mem_filter.mp hw with ⟨hwV, hadj⟩
      exact ⟨⟨w, List.mem_toFinset.mp hwV⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
  rw [hdeg_card]
  rcases mem_baseGraphOf_vertices.mp hu with ⟨i, hi, j, hj, r, hr, rfl⟩ | ⟨j, hj, rfl⟩
  · set m := clauses.length
    have hnb_sub : ∀ (A : Finset ℕ),
        (∀ w, B.toSimpleGraph.Adj (cubicVarV m i j r) w ↔ w ∈ A) →
        (∀ w ∈ A, w ∈ B.vertices) →
        (B.vertices.toFinset.filter fun w ↦ B.toSimpleGraph.Adj (cubicVarV m i j r) w) = A := by
      intro A hA hAV; ext w; simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun ⟨_, h⟩ ↦ (hA w).mp h, fun hw ↦ ⟨hAV w hw, (hA w).mpr hw⟩⟩
    interval_cases r
    · let jprev := if j = 0 then m - 1 else j - 1
      have hjprev : jprev < m := by dsimp only [jprev]; split_ifs <;> omega
      have hnext_prev : (if jprev + 1 < m then jprev + 1 else 0) = j := by
        dsimp only [jprev]; split_ifs <;> omega
      have hne_12 : cubicVarV m i j 1 ≠ cubicVarV m i jprev 2 := by
        intro h; have := (cubicVarV_injective hj hjprev (by omega) (by omega) h).2.2; omega
      have hne_1c : cubicVarV m i j 1 ≠ cubicClauseV j := by unfold cubicVarV cubicClauseV; omega
      have hne_2c : cubicVarV m i jprev 2 ≠ cubicClauseV j := by
        unfold cubicVarV cubicClauseV; omega
      let baseN : Finset ℕ := {cubicVarV m i j 1, cubicVarV m i jprev 2}
      let fullN : Finset ℕ :=
        if (vars.getD i 0, true) ∈ clauses.getD j [] then insert (cubicClauseV j) baseN else baseN
      have heq : (B.vertices.toFinset.filter fun w ↦
          B.toSimpleGraph.Adj (cubicVarV m i j 0) w) = fullN := by
        refine hnb_sub fullN (fun w ↦ ?_) (fun w hw ↦ ?_)
        · rw [baseGraphOf_adj_iff hm]
          constructor
          · rintro (⟨i', hi', j', hj', h | h | h | h | h | h⟩ |
                ⟨i', hi', j', hj', ⟨hl, h | h⟩ | ⟨hl, h | h⟩⟩)
            all_goals
              try (have h1 := cubicVarV_injective hj hj' (by omega) (by omega) h.1; omega)
              try (have h1 :=
                cubicVarV_injective hj (by split_ifs <;> omega) (by omega) (by omega) h.1; omega)
              try (dsimp only [cubicVarV, cubicClauseV] at h; omega)
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              rw [h.2]; dsimp only [fullN, baseN, m]; split_ifs <;> simp
            · rcases cubicVarV_injective hj (by split_ifs <;> omega) (by omega) (by omega) h.1 with
                ⟨rfl, hj_eq, _⟩
              have hj'_eq : j' = jprev := by dsimp only [jprev]; split_ifs at hj_eq ⊢ <;> omega
              subst hj'_eq
              rw [h.2]; dsimp only [fullN, baseN, m]; split_ifs <;> simp
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              rw [h.2]; dsimp only [fullN]; simp only [hl, ↓reduceIte, Finset.mem_insert, true_or]
          · intro hw; dsimp only [fullN, baseN] at hw
            by_cases hmem : (vars.getD i 0, true) ∈ clauses.getD j []
            · simp only [hmem, ite_true, Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              · exact Or.inr ⟨i, hi, j, hj, Or.inl ⟨hmem, Or.inr ⟨rfl, rfl⟩⟩⟩
              · exact Or.inl ⟨i, hi, j, hj, Or.inl ⟨rfl, rfl⟩⟩
              · exact Or.inl ⟨i, hi, jprev, hjprev,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hnext_prev], rfl⟩))))⟩
            · simp only [hmem, ite_false, Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Or.inl ⟨i, hi, j, hj, Or.inl ⟨rfl, rfl⟩⟩
              · exact Or.inl ⟨i, hi, jprev, hjprev,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hnext_prev], rfl⟩))))⟩
        · dsimp only [fullN, baseN] at hw
          split_ifs at hw <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          · rcases hw with rfl | rfl | rfl
            · exact mem_baseGraphOf_vertices.mpr (.inr ⟨j, hj, rfl⟩)
            · exact mem_baseGraphOf_vertices.mpr (.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩)
            · exact mem_baseGraphOf_vertices.mpr (.inl ⟨i, hi, jprev, hjprev, 2, by omega, rfl⟩)
          · rcases hw with rfl | rfl
            · exact mem_baseGraphOf_vertices.mpr (.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩)
            · exact mem_baseGraphOf_vertices.mpr (.inl ⟨i, hi, jprev, hjprev, 2, by omega, rfl⟩)
      rw [heq]; dsimp only [fullN, baseN]
      split_ifs
      · rw [Finset.card_insert_of_notMem (by simp [hne_1c.symm, hne_2c.symm]),
          Finset.card_pair hne_12]; omega
      · rw [Finset.card_pair hne_12]; omega
    · have hne_02 : cubicVarV m i j 0 ≠ cubicVarV m i j 2 := by
        intro h; have := (cubicVarV_injective hj hj (by omega) (by omega) h).2.2; omega
      have hne_0c : cubicVarV m i j 0 ≠ cubicClauseV j := by unfold cubicVarV cubicClauseV; omega
      have hne_2c : cubicVarV m i j 2 ≠ cubicClauseV j := by unfold cubicVarV cubicClauseV; omega
      let baseN : Finset ℕ := {cubicVarV m i j 0, cubicVarV m i j 2}
      let fullN : Finset ℕ :=
        if (vars.getD i 0, false) ∈ clauses.getD j [] then insert (cubicClauseV j) baseN else baseN
      have heq : (B.vertices.toFinset.filter fun w ↦
          B.toSimpleGraph.Adj (cubicVarV m i j 1) w) = fullN := by
        refine hnb_sub fullN (fun w ↦ ?_) (fun w hw ↦ ?_)
        · rw [baseGraphOf_adj_iff hm]
          constructor
          · rintro (⟨i', hi', j', hj', h | h | h | h | h | h⟩ |
                ⟨i', hi', j', hj', ⟨hl, h | h⟩ | ⟨hl, h | h⟩⟩)
            all_goals
              try (have h1 := cubicVarV_injective hj hj' (by omega) (by omega) h.1; omega)
              try (have h1 :=
                cubicVarV_injective hj (by split_ifs <;> omega) (by omega) (by omega) h.1; omega)
              try (dsimp only [cubicVarV, cubicClauseV] at h; omega)
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              rw [h.2]; dsimp only [fullN, baseN, m]; split_ifs <;> simp
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              rw [h.2]; dsimp only [fullN, baseN, m]; split_ifs <;> simp
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              rw [h.2]; dsimp only [fullN]; simp only [hl, ↓reduceIte, Finset.mem_insert, true_or]
          · intro hw; dsimp only [fullN, baseN] at hw
            by_cases hmem : (vars.getD i 0, false) ∈ clauses.getD j []
            · simp only [hmem, ite_true, Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              · exact Or.inr ⟨i, hi, j, hj, Or.inr ⟨hmem, Or.inr ⟨rfl, rfl⟩⟩⟩
              · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
              · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
            · simp only [hmem, ite_false, Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl
              · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
              · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
        · dsimp only [fullN, baseN] at hw
          split_ifs at hw <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          · rcases hw with rfl | rfl | rfl
            · exact mem_baseGraphOf_vertices.mpr (Or.inr ⟨j, hj, rfl⟩)
            · exact mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 0, by omega, rfl⟩)
            · exact mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 2, by omega, rfl⟩)
          · rcases hw with rfl | rfl
            · exact mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 0, by omega, rfl⟩)
            · exact mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 2, by omega, rfl⟩)
      rw [heq]; dsimp only [fullN, baseN]
      split_ifs
      · rw [Finset.card_insert_of_notMem (by simp [hne_0c.symm, hne_2c.symm]),
          Finset.card_pair hne_02]; omega
      · rw [Finset.card_pair hne_02]; omega
    · let jnext := if j + 1 < m then j + 1 else 0
      have hjnext : jnext < m := by dsimp only [jnext]; split_ifs <;> omega
      have hne_10 : cubicVarV m i j 1 ≠ cubicVarV m i jnext 0 := by
        intro h; have := (cubicVarV_injective hj hjnext (by omega) (by omega) h).2.2; omega
      have heq : (B.vertices.toFinset.filter fun w ↦
          B.toSimpleGraph.Adj (cubicVarV m i j 2) w) =
          ({cubicVarV m i j 1, cubicVarV m i jnext 0} : Finset ℕ) := by
        refine hnb_sub _ (fun w ↦ ?_) (fun w hw ↦ ?_)
        · rw [baseGraphOf_adj_iff hm]
          constructor
          · rintro (⟨i', hi', j', hj', h | h | h | h | h | h⟩ |
                ⟨i', hi', j', hj', ⟨_, h | h⟩ | ⟨_, h | h⟩⟩)
            all_goals
              try (have h1 := cubicVarV_injective hj hj' (by omega) (by omega) h.1; omega)
              try (have h1 :=
                cubicVarV_injective hj (by split_ifs <;> omega) (by omega) (by omega) h.1; omega)
              try (dsimp only [cubicVarV, cubicClauseV] at h; omega)
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              simp [h.2, m]
            · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
              simp [h.2, jnext, m]
          · intro hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
            · exact Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩)
          · exact mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, jnext, hjnext, 0, by omega, rfl⟩)
      rw [heq, Finset.card_pair hne_10]; omega
  · set m := clauses.length
    have hcj_mem : clauses.getD j [] ∈ clauses := by
      rw [list_getD_eq _ _ hj]; exact List.getElem_mem hj
    let imgLit : ℕ × Bool → ℕ := fun l ↦ cubicVarV m (vars.idxOf l.1) j (if l.2 then 0 else 1)
    have hmap_eq : (B.vertices.toFinset.filter fun w ↦ B.toSimpleGraph.Adj (cubicClauseV j) w) =
        (clauses.getD j []).toFinset.image imgLit := by
      ext w; simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨_, hadj⟩
        rw [baseGraphOf_adj_iff hm] at hadj
        rcases hadj with ⟨i, _, j', _, h | h | h | h | h | h⟩ |
            ⟨i, hi, j', hj', ⟨hl, h | h⟩ | ⟨hl, h | h⟩⟩
        all_goals try (dsimp only [cubicVarV, cubicClauseV] at h; omega)
        · have hj_eq : j' = j := by unfold cubicClauseV at h; omega
          subst hj_eq
          refine ⟨(vars.getD i 0, true), hl, ?_⟩
          have hidx : vars.idxOf (vars.getD i 0) = i := by
            rw [list_getD_eq _ _ hi]; exact List.Nodup.idxOf_getElem hnd i hi
          dsimp only [imgLit, m]; rw [hidx, h.2]; rfl
        · have hj_eq : j' = j := by unfold cubicClauseV at h; omega
          subst hj_eq
          refine ⟨(vars.getD i 0, false), hl, ?_⟩
          have hidx : vars.idxOf (vars.getD i 0) = i := by
            rw [list_getD_eq _ _ hi]; exact List.Nodup.idxOf_getElem hnd i hi
          dsimp only [imgLit, m]; rw [hidx, h.2]; rfl
      · rintro ⟨⟨v, b⟩, hl, rfl⟩
        have hv : v ∈ vars := hcl_vars _ hcj_mem _ hl
        have hi : vars.idxOf v < vars.length := List.idxOf_lt_length_iff.mpr hv
        have hget : vars.getD (vars.idxOf v) 0 = v := by
          rw [list_getD_eq _ _ hi, List.getElem_idxOf]
        refine ⟨mem_baseGraphOf_vertices.mpr
            (Or.inl ⟨vars.idxOf v, hi, j, hj, if b then 0 else 1, by split_ifs <;> omega, rfl⟩),
            ?_⟩
        rw [baseGraphOf_adj_iff hm]
        cases b
        · exact Or.inr ⟨vars.idxOf v, hi, j, hj,
            Or.inr ⟨by rw [hget]; exact hl, Or.inl ⟨rfl, rfl⟩⟩⟩
        · exact Or.inr ⟨vars.idxOf v, hi, j, hj,
            Or.inl ⟨by rw [hget]; exact hl, Or.inl ⟨rfl, rfl⟩⟩⟩
    rw [hmap_eq]
    have hinj : Set.InjOn imgLit ((clauses.getD j []).toFinset : Set (ℕ × Bool)) := by
      intro l₁ hl₁ l₂ hl₂ heq
      have hi1 := List.idxOf_lt_length_iff.mpr (hcl_vars _ hcj_mem _ (List.mem_toFinset.mp hl₁))
      have hi2 := List.idxOf_lt_length_iff.mpr (hcl_vars _ hcj_mem _ (List.mem_toFinset.mp hl₂))
      have hres := cubicVarV_injective hj hj (by split_ifs <;> omega) (by split_ifs <;> omega) heq
      have hv_eq : l₁.1 = l₂.1 := by
        have := congrArg (fun k ↦ vars.getD k 0) hres.1
        rwa [list_getD_eq _ _ hi1, list_getD_eq _ _ hi2,
          List.getElem_idxOf, List.getElem_idxOf] at this
      have hb_eq : l₁.2 = l₂.2 := by
        have := hres.2.2; cases h₁ : l₁.2 <;> cases h₂ : l₂.2 <;> simp_all
      exact Prod.ext hv_eq hb_eq
    rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup (hcl_nd _ hcj_mem)]
    exact ⟨hcl_pos _ hcj_mem, hcl_le _ hcj_mem⟩

private lemma normClauses_mem_vars {φ : CNF ℕ} {j : ℕ} {v : ℕ} {b : Bool}
    (hj : j < (normClauses φ).length) (hl : (v, b) ∈ (normClauses φ).getD j []) :
    v ∈ dedupList φ.vars := by
  let vars := dedupList φ.vars
  rw [list_getD_eq _ _ hj] at hl
  simp only [normClauses] at hl
  by_cases hjφ : j < φ.length
  · rw [List.getElem_append_left (by simp [hjφ]), List.getElem_map] at hl
    exact mem_dedupList.mpr
      (CNF.mem_vars.mpr ⟨φ[j], List.getElem_mem hjφ, b, mem_dedupList.mp hl⟩)
  · rw [List.getElem_append_right (by simp; omega), List.getElem_map] at hl
    simp only [polyRange_eq_range, List.getElem_range] at hl
    have hi : j - φ.length < vars.length := by
      have : (normClauses φ).length = φ.length + vars.length := by
        simp [normClauses, polyRange_eq_range, vars]
      omega
    have hi2 : (if j - φ.length + 1 < vars.length then j - φ.length + 1 else 0) < vars.length := by
      split_ifs <;> omega
    have hl' := mem_dedupList.mp hl
    simp only [List.length_map, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hl' ⊢
    rcases hl' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rw [list_getD_eq _ _ hi]; exact List.getElem_mem hi
    · rw [list_getD_eq _ _ hi]; exact List.getElem_mem hi
    · rw [list_getD_eq _ _ hi2]; exact List.getElem_mem hi2

private lemma nontrivial_vars_clauses {φ : CNF ℕ} (hvalid : isNontrivialThreeCNF φ = true) :
    0 < (dedupList φ.vars).length ∧ 2 ≤ (normClauses φ).length := by
  simp only [isNontrivialThreeCNF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hvalid
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil φ (List.ne_nil_of_length_pos hvalid.1)
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil c (List.ne_nil_of_length_pos (hvalid.2 c hc).1)
  have h1 : 0 < (dedupList φ.vars).length :=
    List.length_pos_of_mem (mem_dedupList.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩))
  have h2 : (normClauses φ).length = φ.length + (dedupList φ.vars).length := by
    simp [normClauses, polyRange_eq_range]
  exact ⟨h1, by omega⟩

private lemma baseGraphOf_dom_iff {φ : CNF ℕ}
    (hvalid : isNontrivialThreeCNF φ = true) :
    let vars := dedupList φ.vars
    let clauses := normClauses φ
    let B := baseGraphOf vars clauses
    (∃ D : Finset ℕ, (∀ v ∈ D, v ∈ B.vertices) ∧
      (∀ v ∈ B.vertices, v ∈ D ∨ ∃ w ∈ D, B.toSimpleGraph.Adj v w) ∧
      D.card ≤ vars.length * clauses.length) ↔ φ.Satisfiable := by
  classical
  intro vars clauses B
  have hnd : vars.Nodup := nodup_dedupList φ.vars
  obtain ⟨hvars_pos, hm⟩ := nontrivial_vars_clauses hvalid
  set n := vars.length; set m := clauses.length
  constructor
  · rintro ⟨D, hDB, hDdom, hDcard⟩
    let bSet (i j : ℕ) : Finset ℕ :=
      {cubicVarV m i j 1, cubicVarV m i j 2,
        cubicVarV m i (if j + 1 < m then j + 1 else 0) 0}
    let idxSet : Finset (ℕ × ℕ) := (List.range n).toFinset ×ˢ (List.range m).toFinset
    have hb_nonempty : ∀ p ∈ idxSet, (D ∩ bSet p.1 p.2).Nonempty := by
      rintro ⟨i, j⟩ hp
      simp only [idxSet, Finset.mem_product, List.mem_toFinset, List.mem_range] at hp
      rcases hp with ⟨hi, hj⟩
      have h2V : cubicVarV m i j 2 ∈ B.vertices :=
        mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 2, by omega, rfl⟩)
      rcases hDdom _ h2V with hmem | ⟨w, hwD, hadj⟩
      · exact ⟨_, Finset.mem_inter.mpr ⟨hmem, by simp [bSet]⟩⟩
      · rw [baseGraphOf_adj_iff hm] at hadj
        rcases hadj with ⟨i', hi', j', hj', h | h | h | h | h | h⟩ |
            ⟨i', _, j', _, ⟨_, h | h⟩ | ⟨_, h | h⟩⟩
        all_goals
          try (have h1 := cubicVarV_injective hj hj' (by omega) (by omega) h.1; omega)
          try (have h1 :=
            cubicVarV_injective hj (by split_ifs <;> omega) (by omega) (by omega) h.1; omega)
          try (dsimp only [cubicVarV, cubicClauseV] at h; omega)
        · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
          exact ⟨w, Finset.mem_inter.mpr ⟨hwD, by simp [bSet, h.2, m]⟩⟩
        · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
          exact ⟨w, Finset.mem_inter.mpr ⟨hwD, by simp [bSet, h.2, m]⟩⟩
    have hb_pw : (idxSet : Set (ℕ × ℕ)).PairwiseDisjoint fun p ↦ D ∩ bSet p.1 p.2 := by
      intro ⟨i₁, j₁⟩ hp₁ ⟨i₂, j₂⟩ hp₂ hne
      simp only [Finset.mem_coe, idxSet, Finset.mem_product, List.mem_toFinset,
        List.mem_range] at hp₁ hp₂
      refine Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_
      have h1 := (Finset.mem_inter.mp hw₁).2; have h2 := (Finset.mem_inter.mp hw₂).2
      simp only [bSet, Finset.mem_insert, Finset.mem_singleton] at h1 h2
      have hne_ab : ∀ {a b r₁ r₂}, a < m → b < m → r₁ < 3 → r₂ < 3 → r₁ ≠ r₂ →
          cubicVarV m i₁ a r₁ ≠ cubicVarV m i₂ b r₂ := fun ha hb hr₁ hr₂ hne_r h ↦
        hne_r (cubicVarV_injective ha hb hr₁ hr₂ h).2.2
      have hj1' : (if j₁ + 1 < m then j₁ + 1 else 0) < m := by split_ifs <;> omega
      have hj2' : (if j₂ + 1 < m then j₂ + 1 else 0) < m := by split_ifs <;> omega
      have h12 : cubicVarV m i₁ j₁ 1 ≠ cubicVarV m i₂ j₂ 2 :=
        hne_ab hp₁.2 hp₂.2 (by omega) (by omega) (by omega)
      have h21 : cubicVarV m i₁ j₁ 2 ≠ cubicVarV m i₂ j₂ 1 :=
        hne_ab hp₁.2 hp₂.2 (by omega) (by omega) (by omega)
      have h10 : cubicVarV m i₁ j₁ 1 ≠ cubicVarV m i₂ (if j₂ + 1 < m then j₂ + 1 else 0) 0 :=
        hne_ab hp₁.2 hj2' (by omega) (by omega) (by omega)
      have h20 : cubicVarV m i₁ j₁ 2 ≠ cubicVarV m i₂ (if j₂ + 1 < m then j₂ + 1 else 0) 0 :=
        hne_ab hp₁.2 hj2' (by omega) (by omega) (by omega)
      have h01 : cubicVarV m i₁ (if j₁ + 1 < m then j₁ + 1 else 0) 0 ≠ cubicVarV m i₂ j₂ 1 :=
        hne_ab hj1' hp₂.2 (by omega) (by omega) (by omega)
      have h02 : cubicVarV m i₁ (if j₁ + 1 < m then j₁ + 1 else 0) 0 ≠ cubicVarV m i₂ j₂ 2 :=
        hne_ab hj1' hp₂.2 (by omega) (by omega) (by omega)
      have h11 : cubicVarV m i₁ j₁ 1 = cubicVarV m i₂ j₂ 1 → False := fun h ↦ by
        have hr := cubicVarV_injective hp₁.2 hp₂.2 (by omega) (by omega) h
        exact hne (Prod.ext hr.1 hr.2.1)
      have h22 : cubicVarV m i₁ j₁ 2 = cubicVarV m i₂ j₂ 2 → False := fun h ↦ by
        have hr := cubicVarV_injective hp₁.2 hp₂.2 (by omega) (by omega) h
        exact hne (Prod.ext hr.1 hr.2.1)
      have h00 : cubicVarV m i₁ (if j₁ + 1 < m then j₁ + 1 else 0) 0 =
          cubicVarV m i₂ (if j₂ + 1 < m then j₂ + 1 else 0) 0 → False := fun h ↦ by
        have hr := cubicVarV_injective hj1' hj2' (by omega) (by omega) h
        have hj_eq : j₁ = j₂ := by have h' := hr.2.1; split_ifs at h' <;> omega
        exact hne (Prod.ext hr.1 hj_eq)
      rcases h1 with rfl | rfl | rfl <;> rcases h2 with h | h | h
      · exact h11 h
      · exact h12 h
      · exact h10 h
      · exact h21 h
      · exact h22 h
      · exact h20 h
      · exact h01 h
      · exact h02 h
      · exact h00 h
    let unionB : Finset ℕ := idxSet.biUnion fun p ↦ D ∩ bSet p.1 p.2
    have hunionB_sub : unionB ⊆ D := Finset.biUnion_subset.mpr fun _ _ ↦ Finset.inter_subset_left
    have hidx_card : idxSet.card = n * m := by
      simp [idxSet, Finset.card_product, List.toFinset_card_of_nodup List.nodup_range]
    have hcard_ge : n * m ≤ unionB.card := by
      rw [Finset.card_biUnion hb_pw]
      calc n * m = ∑ _ ∈ idxSet, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hidx_card]
        _ ≤ ∑ p ∈ idxSet, (D ∩ bSet p.1 p.2).card :=
            Finset.sum_le_sum fun p hp ↦ Finset.card_pos.mpr (hb_nonempty p hp)
    have hD_eq : unionB = D := Finset.eq_of_subset_of_card_le hunionB_sub (hDcard.trans hcard_ge)
    have hcard_each : ∀ p ∈ idxSet, (D ∩ bSet p.1 p.2).card = 1 := by
      have hsum : ∑ p ∈ idxSet, (D ∩ bSet p.1 p.2).card = n * m := by
        have h1 : unionB.card = n * m := by have := Finset.card_le_card hunionB_sub; omega
        rwa [Finset.card_biUnion hb_pw] at h1
      intro p hp
      by_contra hne1
      have hge2 : 2 ≤ (D ∩ bSet p.1 p.2).card := by
        have := Finset.card_pos.mpr (hb_nonempty p hp); omega
      have hsum_gt : n * m < ∑ q ∈ idxSet, (D ∩ bSet q.1 q.2).card := by
        rw [← Finset.add_sum_erase _ _ hp]
        have hrest : idxSet.card - 1 ≤ ∑ q ∈ idxSet.erase p, (D ∩ bSet q.1 q.2).card := by
          calc idxSet.card - 1 = ∑ _ ∈ idxSet.erase p, 1 := by
                rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hp]
            _ ≤ _ := Finset.sum_le_sum fun q hq ↦
                Finset.card_pos.mpr (hb_nonempty q (Finset.mem_of_mem_erase hq))
        rw [hidx_card] at hrest; omega
      omega
    have hno_clause : ∀ j < m, cubicClauseV j ∉ D := by
      intro j _ hmem; rw [← hD_eq] at hmem
      obtain ⟨⟨i, j'⟩, _, hw⟩ := Finset.mem_biUnion.mp hmem
      have hg := (Finset.mem_inter.mp hw).2
      simp only [bSet, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with h | h | h <;> unfold cubicClauseV cubicVarV at h <;> omega
    have hback_step : ∀ i < n, ∀ j < m,
        cubicVarV m i (if j + 1 < m then j + 1 else 0) 0 ∈ D →
        cubicVarV m i j 0 ∈ D := by
      intro i hi j hj hnextD
      have h1 := hcard_each (i, j) (by simp [idxSet, hi, hj])
      have hnot1 : cubicVarV m i j 1 ∉ D := by
        intro h1D
        have hne : cubicVarV m i j 1 ≠ cubicVarV m i (if j + 1 < m then j + 1 else 0) 0 := by
          intro h; have := (cubicVarV_injective hj (by split_ifs <;> omega)
            (by omega) (by omega) h).2.2; omega
        have hsub : ({cubicVarV m i j 1,
            cubicVarV m i (if j + 1 < m then j + 1 else 0) 0} : Finset ℕ) ⊆ D ∩ bSet i j := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨h1D, by simp [bSet]⟩
          · exact Finset.mem_inter.mpr ⟨hnextD, by simp [bSet]⟩
        have := Finset.card_le_card hsub; rw [Finset.card_pair hne] at this; dsimp only at h1; omega
      have hnot2 : cubicVarV m i j 2 ∉ D := by
        intro h2D
        have hne : cubicVarV m i j 2 ≠ cubicVarV m i (if j + 1 < m then j + 1 else 0) 0 := by
          intro h; have := (cubicVarV_injective hj (by split_ifs <;> omega)
            (by omega) (by omega) h).2.2; omega
        have hsub : ({cubicVarV m i j 2,
            cubicVarV m i (if j + 1 < m then j + 1 else 0) 0} : Finset ℕ) ⊆ D ∩ bSet i j := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨h2D, by simp [bSet]⟩
          · exact Finset.mem_inter.mpr ⟨hnextD, by simp [bSet]⟩
        have := Finset.card_le_card hsub; rw [Finset.card_pair hne] at this; dsimp only at h1; omega
      have h1V : cubicVarV m i j 1 ∈ B.vertices :=
        mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩)
      rcases hDdom _ h1V with hmem | ⟨w, hwD, hadj⟩
      · exact (hnot1 hmem).elim
      · rw [baseGraphOf_adj_iff hm] at hadj
        rcases hadj with ⟨i', hi', j', hj', h | h | h | h | h | h⟩ |
            ⟨i', _, j', hj', ⟨_, h | h⟩ | ⟨_, h | h⟩⟩
        all_goals
          try (have h1 := cubicVarV_injective hj hj' (by omega) (by omega) h.1; omega)
          try (have h1 :=
            cubicVarV_injective hj (by split_ifs <;> omega) (by omega) (by omega) h.1; omega)
          try (dsimp only [cubicVarV, cubicClauseV] at h; omega)
        · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
          exact h.2 ▸ hwD
        · rcases cubicVarV_injective hj hj' (by omega) (by omega) h.1 with ⟨rfl, rfl, _⟩
          exact (hnot2 (h.2 ▸ hwD)).elim
        · exact (hno_clause j' hj' (h.2 ▸ hwD)).elim
    have hall_zero : ∀ i < n, ∀ j < m, cubicVarV m i j 0 ∈ D →
        ∀ k < m, cubicVarV m i k 0 ∈ D := by
      intro i hi j hj hjD
      have hstep : ∀ d a, a < m → cubicVarV m i a 0 ∈ D →
          cubicVarV m i ((a + m - d % m) % m) 0 ∈ D := by
        intro d; induction d with
        | zero =>
          intro a ha haD
          have : (a + m - 0 % m) % m = a := by
            simp only [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right]; exact Nat.mod_eq_of_lt ha
          rwa [this]
        | succ d' ih =>
          intro a ha haD
          have hcur := ih a ha haD
          set cur := (a + m - d' % m) % m
          have hcur_lt : cur < m := Nat.mod_lt _ (by omega)
          let prev := if cur = 0 then m - 1 else cur - 1
          have hprev_lt : prev < m := by dsimp only [prev]; split_ifs <;> omega
          have hprev_next : (if prev + 1 < m then prev + 1 else 0) = cur := by
            dsimp only [prev]; split_ifs <;> omega
          have hprevD := hback_step i hi prev hprev_lt (hprev_next ▸ hcur)
          have hprev_eq : (a + m - (d' + 1) % m) % m = prev := by
            have hstep2 : ((a + m - (d' + 1) % m) % m + 1) % m = cur := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              by_cases hd : d' % m + 1 < m
              · have h1 : (d' + 1) % m = d' % m + 1 := by
                  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt hd]
                rw [h1, show a + m - (d' % m + 1) + 1 = a + m - d' % m by omega]
              · have hlt2 : d' % m < m := Nat.mod_lt _ (by omega)
                have h1 : (d' + 1) % m = 0 := by
                  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m),
                    show d' % m + 1 = m by omega, Nat.mod_self]
                rw [h1, Nat.sub_zero, show a + m + 1 = a + 1 + m by omega, Nat.add_mod_right]
                dsimp only [cur]; rw [show a + m - d' % m = a + 1 by omega]
            have hx_lt : (a + m - (d' + 1) % m) % m < m := Nat.mod_lt _ (by omega)
            dsimp only [prev]
            split_ifs with hc0
            · by_contra hne
              have hlt' : (a + m - (d' + 1) % m) % m + 1 < m := by omega
              rw [Nat.mod_eq_of_lt hlt'] at hstep2; omega
            · by_cases hx : (a + m - (d' + 1) % m) % m + 1 < m
              · rw [Nat.mod_eq_of_lt hx] at hstep2; omega
              · have hx1 : (a + m - (d' + 1) % m) % m + 1 = m := by omega
                rw [hx1, Nat.mod_self] at hstep2; exact (hc0 hstep2.symm).elim
          rwa [hprev_eq]
      intro k hk
      have hd := hstep ((j + m - k) % m) j hj hjD
      have hcalc : (j + m - (j + m - k) % m % m) % m = k := by
        rw [Nat.mod_mod]
        by_cases hjk : k ≤ j
        · have : (j + m - k) % m = j - k := by
            rw [show j + m - k = (j - k) + m by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          rw [this, show j + m - (j - k) = k + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
        · have : (j + m - k) % m = j + m - k := Nat.mod_eq_of_lt (by omega)
          rw [this, show j + m - (j + m - k) = k by omega, Nat.mod_eq_of_lt hk]
      rwa [hcalc] at hd
    have hnot_both : ∀ i < n, ∀ j₁ < m, ∀ j₂ < m,
        cubicVarV m i j₁ 0 ∈ D → cubicVarV m i j₂ 1 ∉ D := by
      intro i hi j₁ hj₁ j₂ hj₂ ht hf
      have hnextD := hall_zero i hi j₁ hj₁ ht (if j₂ + 1 < m then j₂ + 1 else 0)
        (by split_ifs <;> omega)
      have h1 := hcard_each (i, j₂) (by simp [idxSet, hi, hj₂])
      have hne : cubicVarV m i j₂ 1 ≠ cubicVarV m i (if j₂ + 1 < m then j₂ + 1 else 0) 0 := by
        intro h; have := (cubicVarV_injective hj₂ (by split_ifs <;> omega)
          (by omega) (by omega) h).2.2; omega
      have hsub : ({cubicVarV m i j₂ 1,
          cubicVarV m i (if j₂ + 1 < m then j₂ + 1 else 0) 0} : Finset ℕ) ⊆ D ∩ bSet i j₂ := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hf, by simp [bSet]⟩
        · exact Finset.mem_inter.mpr ⟨hnextD, by simp [bSet]⟩
      have := Finset.card_le_card hsub; rw [Finset.card_pair hne] at this; dsimp only at h1; omega
    let σ : ℕ → Bool := fun v ↦ decide (cubicVarV m (vars.idxOf v) 0 0 ∈ D)
    refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc ↦ ?_⟩
    obtain ⟨j, hj_φ, hc_eq⟩ := List.mem_iff_getElem.mp hc
    have hj_m : j < m := by
      have : clauses.length = φ.length + n := by
        simp [clauses, normClauses, polyRange_eq_range, n, vars]
      omega
    have hcl_j : clauses.getD j [] = dedupList c := by
      rw [list_getD_eq _ _ hj_m]
      simp only [clauses, normClauses]
      rw [List.getElem_append_left (by simp [hj_φ]), List.getElem_map, hc_eq]
    have hcV : cubicClauseV j ∈ B.vertices := mem_baseGraphOf_vertices.mpr (Or.inr ⟨j, hj_m, rfl⟩)
    rcases hDdom _ hcV with hmem | ⟨w, hwD, hadj⟩
    · exact (hno_clause j hj_m hmem).elim
    · rw [baseGraphOf_adj_iff hm] at hadj
      rcases hadj with ⟨i, _, j', _, h | h | h | h | h | h⟩ |
          ⟨i, hi, j', hj', ⟨hl, h | h⟩ | ⟨hl, h | h⟩⟩
      all_goals try (unfold cubicVarV cubicClauseV at h; omega)
      · have hj_eq : j' = j := by unfold cubicClauseV at h; omega
        rw [hj_eq] at hl h
        have hlit : (vars.getD i 0, true) ∈ c := mem_dedupList.mp (hcl_j ▸ hl)
        have hidx : vars.idxOf (vars.getD i 0) = i := by
          rw [list_getD_eq _ _ hi]; exact List.Nodup.idxOf_getElem hnd i hi
        have h0D := hall_zero i hi j hj_m (h.2 ▸ hwD) 0 (by omega)
        exact (Clause.eval_eq_true_iff σ c).mpr ⟨(vars.getD i 0, true), hlit, by
          dsimp only [σ]; rw [hidx]; exact decide_eq_true h0D⟩
      · have hj_eq : j' = j := by unfold cubicClauseV at h; omega
        rw [hj_eq] at hl h
        have hlit : (vars.getD i 0, false) ∈ c := mem_dedupList.mp (hcl_j ▸ hl)
        have hidx : vars.idxOf (vars.getD i 0) = i := by
          rw [list_getD_eq _ _ hi]; exact List.Nodup.idxOf_getElem hnd i hi
        have h0not : cubicVarV m i 0 0 ∉ D := fun h0D ↦
          hnot_both i hi 0 (by omega) j hj_m h0D (h.2 ▸ hwD)
        exact (Clause.eval_eq_true_iff σ c).mpr ⟨(vars.getD i 0, false), hlit, by
          dsimp only [σ]; rw [hidx]; exact decide_eq_false h0not⟩
  · rintro ⟨σ, hσ⟩
    let D : Finset ℕ :=
      ((List.range n).toFinset ×ˢ (List.range m).toFinset).image fun p ↦
        cubicVarV m p.1 p.2 (if σ (vars.getD p.1 0) then 0 else 1)
    have hD_sub : ∀ v ∈ D, v ∈ B.vertices := fun v hv ↦ by
      obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.mp hv
      simp only [Finset.mem_product, List.mem_toFinset, List.mem_range] at hp
      exact mem_baseGraphOf_vertices.mpr
        (Or.inl ⟨i, hp.1, j, hp.2, if σ (vars.getD i 0) then 0 else 1, by split_ifs <;> omega, rfl⟩)
    have hD_card : D.card ≤ n * m :=
      Finset.card_image_le.trans (by
        simp [Finset.card_product, List.toFinset_card_of_nodup List.nodup_range])
    have hD_dom : ∀ v ∈ B.vertices, v ∈ D ∨ ∃ w ∈ D, B.toSimpleGraph.Adj v w := by
      intro v hv
      rcases mem_baseGraphOf_vertices.mp hv with ⟨i, hi, j, hj, r, hr, rfl⟩ | ⟨j, hj, rfl⟩
      · have hpick : cubicVarV m i j (if σ (vars.getD i 0) then 0 else 1) ∈ D :=
          Finset.mem_image.mpr ⟨(i, j), by simp [hi, hj, n, m], rfl⟩
        interval_cases r
        · cases hσi : σ (vars.getD i 0)
          · exact Or.inr ⟨_, by rw [hσi] at hpick; exact hpick, (baseGraphOf_adj_iff hm).mpr
              (Or.inl ⟨i, hi, j, hj, Or.inl ⟨rfl, rfl⟩⟩)⟩
          · exact Or.inl (by rw [hσi] at hpick; exact hpick)
        · cases hσi : σ (vars.getD i 0)
          · exact Or.inl (by rw [hσi] at hpick; exact hpick)
          · exact Or.inr ⟨_, by rw [hσi] at hpick; exact hpick, (baseGraphOf_adj_iff hm).mpr
              (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)⟩
        · cases hσi : σ (vars.getD i 0)
          · exact Or.inr ⟨_, by rw [hσi] at hpick; exact hpick, (baseGraphOf_adj_iff hm).mpr
              (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)⟩
          · let jnext := if j + 1 < m then j + 1 else 0
            have hjnext : jnext < m := by dsimp only [jnext]; split_ifs <;> omega
            have hpick' : cubicVarV m i jnext 0 ∈ D :=
              Finset.mem_image.mpr ⟨(i, jnext),
                Finset.mem_product.mpr ⟨List.mem_toFinset.mpr (List.mem_range.mpr hi),
                  List.mem_toFinset.mpr (List.mem_range.mpr hjnext)⟩, by dsimp only; rw [hσi]; rfl⟩
            exact Or.inr ⟨_, hpick', (baseGraphOf_adj_iff hm).mpr
              (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)⟩
      · have hsat_j : (clauses.getD j []).eval σ = true := by
          rw [list_getD_eq _ _ hj]
          simp only [clauses, normClauses]
          by_cases hjφ : j < φ.length
          · rw [List.getElem_append_left (by simp [hjφ]), List.getElem_map]
            have hcj := (CNF.eval_eq_true_iff σ φ).mp hσ _ (List.getElem_mem hjφ)
            obtain ⟨l, hl, hlv⟩ := (Clause.eval_eq_true_iff σ _).mp hcj
            exact (Clause.eval_eq_true_iff σ _).mpr ⟨l, mem_dedupList.mpr hl, hlv⟩
          · rw [List.getElem_append_right (by simp; omega), List.getElem_map]
            simp only [polyRange_eq_range, List.getElem_range]
            refine (Clause.eval_eq_true_iff σ _).mpr ?_
            cases hσi : σ (vars.getD (j - φ.length) 0)
            · exact ⟨(vars.getD (j - φ.length) 0, false),
                mem_dedupList.mpr (by change _ ∈ [_, _, _]; simp [vars]), hσi⟩
            · exact ⟨(vars.getD (j - φ.length) 0, true),
                mem_dedupList.mpr (by change _ ∈ [_, _, _]; simp [vars]), hσi⟩
        obtain ⟨⟨v, b⟩, hl, hvb⟩ := (Clause.eval_eq_true_iff σ _).mp hsat_j
        have hv_mem : v ∈ vars := normClauses_mem_vars hj hl
        have hi : vars.idxOf v < n := List.idxOf_lt_length_iff.mpr hv_mem
        have hget : vars.getD (vars.idxOf v) 0 = v := by
          rw [list_getD_eq _ _ hi, List.getElem_idxOf]
        have hpick : cubicVarV m (vars.idxOf v) j (if b then 0 else 1) ∈ D :=
          Finset.mem_image.mpr ⟨(vars.idxOf v, j),
            Finset.mem_product.mpr ⟨List.mem_toFinset.mpr (List.mem_range.mpr hi),
              List.mem_toFinset.mpr (List.mem_range.mpr hj)⟩,
            by dsimp only; rw [hget, hvb]⟩
        right
        refine ⟨_, hpick, (baseGraphOf_adj_iff hm).mpr (Or.inr ⟨vars.idxOf v, hi, j, hj, ?_⟩)⟩
        cases b
        · exact Or.inr ⟨by rw [hget]; exact hl, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨by rw [hget]; exact hl, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨D, hD_sub, hD_dom, hD_card⟩

private lemma baseGraphOf_connected {φ : CNF ℕ} (hvalid : isNontrivialThreeCNF φ = true) :
    (baseGraphOf (dedupList φ.vars) (normClauses φ)).induced.Connected := by
  let vars := dedupList φ.vars
  let clauses := normClauses φ
  let B := baseGraphOf vars clauses
  obtain ⟨hvars_pos, hm⟩ := nontrivial_vars_clauses hvalid
  simp only [isNontrivialThreeCNF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hvalid
  obtain ⟨_, hφ_cl⟩ := hvalid
  set n := vars.length; set m := clauses.length
  let mkV (i j r : ℕ) (hi : i < n) (hj : j < m) (hr : r < 3) : {w // w ∈ B.vertices} :=
    ⟨cubicVarV m i j r, mem_baseGraphOf_vertices.mpr (Or.inl ⟨i, hi, j, hj, r, hr, rfl⟩)⟩
  let mkC (j : ℕ) (hj : j < m) : {w // w ∈ B.vertices} :=
    ⟨cubicClauseV j, mem_baseGraphOf_vertices.mpr (Or.inr ⟨j, hj, rfl⟩)⟩
  refine B.induced.connected_iff_exists_forall_reachable.mpr ⟨mkV 0 0 0 hvars_pos (by omega)
      (by omega), fun u ↦ ?_⟩
  have hring_reach : ∀ i (hi : i < n) j (hj : j < m) r (hr : r < 3),
      B.induced.Reachable (mkV i 0 0 hi (by omega) (by omega)) (mkV i j r hi hj hr) := by
    intro i hi j
    have hstep0 : ∀ j (hj : j < m),
        B.induced.Reachable (mkV i 0 0 hi (by omega) (by omega)) (mkV i j 0 hi hj (by omega)) := by
      intro j; induction j with
      | zero => intro _; exact .refl _
      | succ j' ih =>
        intro hj'
        have hj0 : j' < m := by omega
        have ha01 : B.induced.Adj (mkV i j' 0 hi hj0 (by omega)) (mkV i j' 1 hi hj0 (by omega)) :=
          (baseGraphOf_adj_iff hm).mpr (Or.inl ⟨i, hi, j', hj0, Or.inl ⟨rfl, rfl⟩⟩)
        have ha12 : B.induced.Adj (mkV i j' 1 hi hj0 (by omega)) (mkV i j' 2 hi hj0 (by omega)) :=
          (baseGraphOf_adj_iff hm).mpr (Or.inl ⟨i, hi, j', hj0, Or.inr (Or.inr (Or.inl ⟨rfl,
            rfl⟩))⟩)
        have ha20 : B.induced.Adj (mkV i j' 2 hi hj0 (by omega))
            (mkV i (j' + 1) 0 hi hj' (by omega)) := by
          have hj'm : j' + 1 < clauses.length := hj'
          exact (baseGraphOf_adj_iff hm).mpr (Or.inl ⟨i, hi, j', hj0,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by
              change cubicVarV m i (j' + 1) 0 =
                cubicVarV m i (if j' + 1 < clauses.length then j' + 1 else 0) 0
              simp only [hj'm, ↓reduceIte]⟩))))⟩)
        exact ((ih hj0).trans ha01.reachable).trans (ha12.reachable.trans ha20.reachable)
    intro hj r hr
    interval_cases r
    · exact hstep0 j hj
    · exact (hstep0 j hj).trans (_root_.SimpleGraph.Adj.reachable
        ((baseGraphOf_adj_iff hm).mpr (Or.inl ⟨i, hi, j, hj, Or.inl ⟨rfl, rfl⟩⟩)))
    · have ha01 : B.induced.Adj (mkV i j 0 hi hj (by omega)) (mkV i j 1 hi hj (by omega)) :=
        (baseGraphOf_adj_iff hm).mpr (Or.inl ⟨i, hi, j, hj, Or.inl ⟨rfl, rfl⟩⟩)
      have ha12 : B.induced.Adj (mkV i j 1 hi hj (by omega)) (mkV i j 2 hi hj (by omega)) :=
        (baseGraphOf_adj_iff hm).mpr (Or.inl ⟨i, hi, j, hj, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
      exact ((hstep0 j hj).trans ha01.reachable).trans ha12.reachable
  have hvar_reach : ∀ i (hi : i < n),
      B.induced.Reachable (mkV 0 0 0 hvars_pos (by omega) (by omega))
        (mkV i 0 0 hi (by omega) (by omega)) := by
    intro i; induction i with
    | zero => intro _; exact .refl _
    | succ i' ih =>
      intro hi'
      have hi0 : i' < n := by omega
      let j := φ.length + i'
      have hj : j < m := by
        have : clauses.length = φ.length + n := by
          simp [clauses, normClauses, polyRange_eq_range, n, vars]
        omega
      have hcl_j : (vars.getD i' 0, true) ∈ clauses.getD j [] ∧
          (vars.getD (i' + 1) 0, true) ∈ clauses.getD j [] := by
        rw [list_getD_eq _ _ hj]; simp only [clauses, normClauses]
        rw [List.getElem_append_right (by simp; omega), List.getElem_map]
        simp only [List.length_map, polyRange_eq_range, List.getElem_range, j,
          Nat.add_sub_cancel_left]
        have hi : i' + 1 < (dedupList φ.vars).length := hi'
        exact ⟨mem_dedupList.mpr (by simp [vars]), mem_dedupList.mpr (by simp [vars, hi])⟩
      have ha1 : B.induced.Adj (mkV i' j 0 hi0 hj (by omega)) (mkC j hj) :=
        (baseGraphOf_adj_iff hm).mpr (Or.inr ⟨i', hi0, j, hj, Or.inl ⟨hcl_j.1, Or.inr ⟨rfl, rfl⟩⟩⟩)
      have ha2 : B.induced.Adj (mkC j hj) (mkV (i' + 1) j 0 hi' hj (by omega)) :=
        (baseGraphOf_adj_iff hm).mpr (Or.inr ⟨i' +
          1, hi', j, hj, Or.inl ⟨hcl_j.2, Or.inl ⟨rfl, rfl⟩⟩⟩)
      exact (((ih hi0).trans (hring_reach i' hi0 j hj 0 (by omega))).trans
        (ha1.reachable.trans ha2.reachable)).trans
        (hring_reach (i' + 1) hi' j hj 0 (by omega)).symm
  rcases mem_baseGraphOf_vertices.mp u.2 with ⟨i, hi, j, hj, r, hr, hu⟩ | ⟨j, hj, hu⟩
  · rw [show u = mkV i j r hi hj hr from Subtype.ext hu]
    exact (hvar_reach i hi).trans (hring_reach i hi j hj r hr)
  · rw [show u = mkC j hj from Subtype.ext hu]
    have hcj_pos : 0 < (clauses.getD j []).length := by
      rw [list_getD_eq _ _ hj]
      simp only [clauses, normClauses]
      by_cases hjφ : j < φ.length
      · rw [List.getElem_append_left (by simp [hjφ]), List.getElem_map]
        obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil φ[j]
          (List.ne_nil_of_length_pos (hφ_cl _ (List.getElem_mem hjφ)).1)
        exact List.length_pos_of_mem (mem_dedupList.mpr hl)
      · rw [List.getElem_append_right (by simp; omega), List.getElem_map]
        simp only [List.length_map, polyRange_eq_range, List.getElem_range]
        exact List.length_pos_of_mem (a := ((dedupList φ.vars).getD (j - φ.length) 0, true))
          (mem_dedupList.mpr (by simp))
    obtain ⟨⟨v, b⟩, hl⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hcj_pos)
    have hv_mem : v ∈ vars := normClauses_mem_vars hj hl
    have hi : vars.idxOf v < n := List.idxOf_lt_length_iff.mpr hv_mem
    have hget : vars.getD (vars.idxOf v) 0 = v := by
      rw [list_getD_eq _ _ hi, List.getElem_idxOf]
    have hadj : B.induced.Adj
        ⟨cubicVarV m (vars.idxOf v) j (if b then 0 else 1),
          mem_baseGraphOf_vertices.mpr (Or.inl ⟨vars.idxOf v, hi, j, hj, if b then 0 else 1,
            by split_ifs <;> omega, rfl⟩)⟩
        ⟨cubicClauseV j, mem_baseGraphOf_vertices.mpr (Or.inr ⟨j, hj, rfl⟩)⟩ := by
      rw [Graph.induced_adj, baseGraphOf_adj_iff hm]
      cases b
      · exact Or.inr ⟨vars.idxOf v, hi, j, hj,
          Or.inr ⟨by rw [hget]; exact hl, Or.inr ⟨rfl, rfl⟩⟩⟩
      · exact Or.inr ⟨vars.idxOf v, hi, j, hj,
          Or.inl ⟨by rw [hget]; exact hl, Or.inr ⟨rfl, rfl⟩⟩⟩
    exact ((hvar_reach (vars.idxOf v) hi).trans
      (hring_reach (vars.idxOf v) hi j hj _ (by split_ifs <;> omega))).trans hadj.reachable

/-! ### 4. Reduction Correctness and Polynomial-Time Computability -/

/-- **Reduction correctness**: `toCubicDominatingSet φ ∈ CubicDominatingSet ↔ φ ∈ ThreeSAT`. -/
theorem toCubicDominatingSet_mem_iff (φ : CNF ℕ) :
    toCubicDominatingSet φ ∈ CubicDominatingSet ↔ φ ∈ ThreeSAT := by
  unfold toCubicDominatingSet
  by_cases hemp : φ.isEmpty = true
  · have hnil : φ = [] := List.isEmpty_iff.mp hemp
    subst hnil
    simp only [hemp, ↓reduceIte]
    exact ⟨fun _ ↦ ⟨fun _ h ↦ by simp at h, ⟨fun _ ↦ false, by simp⟩⟩, fun _ ↦ k4Graph_mem_one⟩
  · simp only [hemp]
    by_cases hvalid : isNontrivialThreeCNF φ = true
    · simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hvalid' := hvalid
      simp only [isNontrivialThreeCNF, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hvalid'
      let vars := dedupList φ.vars
      let clauses := normClauses φ
      let B := baseGraphOf vars clauses
      let T := (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum
      have hndB : B.vertices.Nodup := baseGraphOf_vertices_nodup vars clauses
      have hmodB : ∀ u ∈ B.vertices, u % 4 ≠ 3 := fun u hu ↦ by
        rcases mem_baseGraphOf_vertices.mp hu with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
          dsimp only [cubicVarV, cubicClauseV] <;> omega
      obtain ⟨hvars_pos, hm⟩ := nontrivial_vars_clauses hvalid
      have hEB : ∀ e ∈ B.edges, e.1 ∈ B.vertices ∧ e.2 ∈ B.vertices := by
        intro ⟨a, b⟩ hab
        unfold B baseGraphOf at hab
        simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
          List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
        have hV := @mem_baseGraphOf_vertices vars clauses
        rcases hab with ⟨i, hi, j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, hi, j, hj, h⟩
        · exact ⟨hV.mpr (.inl ⟨i, hi, j, hj, 0, by omega, rfl⟩),
            hV.mpr (.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩)⟩
        · exact ⟨hV.mpr (.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩),
            hV.mpr (.inl ⟨i, hi, j, hj, 2, by omega, rfl⟩)⟩
        · exact ⟨hV.mpr (.inl ⟨i, hi, j, hj, 2, by omega, rfl⟩),
            hV.mpr (.inl ⟨i, hi, _, by split_ifs <;> omega, 0, by omega, rfl⟩)⟩
        · rcases h with h1 | h2
          · split_ifs at h1 <;> simp only [List.mem_singleton, Prod.mk.injEq,
              List.not_mem_nil] at h1
            rcases h1 with ⟨rfl, rfl⟩
            exact ⟨hV.mpr (.inr ⟨j, hj, rfl⟩), hV.mpr (.inl ⟨i, hi, j, hj, 0, by omega, rfl⟩)⟩
          · split_ifs at h2 <;> simp only [List.mem_singleton, Prod.mk.injEq,
              List.not_mem_nil] at h2
            rcases h2 with ⟨rfl, rfl⟩
            exact ⟨hV.mpr (.inr ⟨j, hj, rfl⟩), hV.mpr (.inl ⟨i, hi, j, hj, 1, by omega, rfl⟩)⟩
      have hdegB : ∀ u ∈ B.vertices, 1 ≤ cubicGraphDegBool B u ∧ cubicGraphDegBool B u ≤ 3 := by
        intro u hu
        refine baseGraphOf_degree_bounds (nodup_dedupList φ.vars) hm ?_ ?_ ?_ ?_ hu
        · intro c hc
          simp only [normClauses, List.mem_append, List.mem_map, polyRange_eq_range,
            List.mem_range] at hc
          rcases hc with ⟨d, hd, rfl⟩ | ⟨i, _, rfl⟩
          · obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil d
              (List.ne_nil_of_length_pos (hvalid'.2 d hd).1)
            exact List.length_pos_of_mem (mem_dedupList.mpr hl)
          · exact List.length_pos_of_mem (a := (vars.getD i 0, true))
              (mem_dedupList.mpr (by dsimp only [vars]; simp))
        · intro c hc
          simp only [normClauses, List.mem_append, List.mem_map, polyRange_eq_range,
            List.mem_range] at hc
          rcases hc with ⟨d, hd, rfl⟩ | ⟨i, _, rfl⟩
          · exact (length_dedupList_le d).trans (hvalid'.2 d hd).2
          · exact (length_dedupList_le _).trans (by simp)
        · intro c hc
          simp only [normClauses, List.mem_append, List.mem_map] at hc
          rcases hc with ⟨d, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact nodup_dedupList _
        · intro c hc l hl
          simp only [normClauses, List.mem_append, List.mem_map, polyRange_eq_range,
            List.mem_range] at hc
          rcases hc with ⟨d, hd, rfl⟩ | ⟨i, hi, rfl⟩
          · exact mem_dedupList.mpr (CNF.mem_vars.mpr ⟨d, hd, l.2, mem_dedupList.mp hl⟩)
          · have hl' := mem_dedupList.mp hl
            have hi2 : (if i + 1 < vars.length then i + 1 else 0) < vars.length := by
              split_ifs <;> omega
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
            rcases hl' with rfl | rfl | rfl
            · rw [list_getD_eq _ _ hi]; exact List.getElem_mem hi
            · rw [list_getD_eq _ _ hi]; exact List.getElem_mem hi
            · rw [list_getD_eq _ _ hi2]; exact List.getElem_mem hi2
      have hconnG : (cappedGraphOf B).induced.Connected :=
        cappedGraphOf_connected hmodB (baseGraphOf_connected hvalid)
      have hcubG : ∀ v : {w // w ∈ (cappedGraphOf B).vertices},
          (cappedGraphOf B).induced.degree v = 3 :=
        cappedGraphOf_cubic hndB hmodB hEB hdegB
      have hbound_le : vars.length * clauses.length + 2 * T ≤
          (cappedGraphOf B).vertices.toFinset.card := by
        rw [List.toFinset_card_of_nodup (cappedGraphOf_vertices_nodup hndB hmodB),
          cappedGraphOf_vertices_length]
        have hBlen : vars.length * clauses.length ≤ B.vertices.length := by
          unfold B baseGraphOf
          simp only [polyRange_eq_range, List.length_append, List.length_flatMap]
          have h3 : ∀ k : ℕ, ((List.range k).map fun _ ↦ 3).sum = 3 * k := fun k ↦ by
            induction k with
            | zero => simp
            | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; ring
          have h1 : ∀ n : ℕ, ((List.range n).map fun _ ↦
              ((List.range clauses.length).map fun _ ↦ 3).sum).sum = n * (3 * clauses.length) := by
            intro n; induction n with
            | zero => simp
            | succ n ih =>
              rw [List.range_succ, List.map_append, List.sum_append, ih, h3]; simp; ring
          have hvar : ((List.range vars.length).map fun i ↦
              ((List.range clauses.length).map fun j ↦
                [cubicVarV clauses.length i j 0, cubicVarV clauses.length i j 1,
                  cubicVarV clauses.length i j 2].length).sum).sum =
              vars.length * (3 * clauses.length) := by
            simpa using h1 vars.length
          rw [hvar]
          have : vars.length * (3 * clauses.length) = 3 * (vars.length * clauses.length) := by ring
          omega
        change vars.length * clauses.length + 2 * T ≤ B.vertices.length + 7 * T
        omega
      rw [mem_CubicDominatingSet_iff, mem_DominatingSet_iff_exists_card_le]
      constructor
      · rintro ⟨_, _, _, hdom⟩
        exact ⟨fun c hc ↦ (hvalid'.2 c hc).2,
          (baseGraphOf_dom_iff hvalid).mp ((cappedGraphOf_dom_iff hndB hmodB hEB _).mp hdom)⟩
      · rintro ⟨_, hsat⟩
        refine ⟨hconnG, hcubG, hbound_le,
          (cappedGraphOf_dom_iff hndB hmodB hEB _).mpr ((baseGraphOf_dom_iff hvalid).mpr hsat)⟩
    · simp only [hvalid, Bool.not_false]
      refine ⟨fun h ↦ (k4Graph_not_mem_zero h).elim, fun h ↦ ?_⟩
      exfalso; apply hvalid
      simp only [isNontrivialThreeCNF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp (by simpa using hemp)),
        fun c hc ↦ ⟨?_, h.1 c hc⟩⟩
      rcases h.2 with ⟨σ, hσ⟩
      obtain ⟨l, hl, _⟩ := (Clause.eval_eq_true_iff σ c).mp ((CNF.eval_eq_true_iff σ φ).mp hσ c hc)
      exact List.length_pos_of_mem hl

private lemma computableInPolyTime_cubicVarV :
    ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ ↦ cubicVarV q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encNat :=
  ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.const 4) (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 3)
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_mul' (by fun_prop) (by fun_prop)) (by fun_prop)))
      (by fun_prop)))

private lemma cpt_congr {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f g : α → β} (hf : ComputableInPolyTime f encA encB) (h : ∀ x, f x = g x) :
    ComputableInPolyTime g encA encB := by
  have heq : f = g := funext h
  exact heq ▸ hf

private lemma computableInPolyTime_clauseLitCond (b : Bool) :
    ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ p.1.any fun l ↦ decide (l = (p.2, b)))
      (encPair (encList (encPair encNat encBool)) encNat) encBool :=
  anyWithInput (test := fun p l ↦ decide (l = (p.2, b)))
    (fst (encList (encPair encNat encBool)) encNat)
    (ComputableInPolyTime.decide_eq'
      (snd (encPair (encList (encPair encNat encBool)) encNat) (encPair encNat encBool))
      (((snd (encList (encPair encNat encBool)) encNat).comp
        (fst (encPair (encList (encPair encNat encBool)) encNat) (encPair encNat encBool))).prod
        (ComputableInPolyTime.const b)))

private lemma computableInPolyTime_optEdge :
    ComputableInPolyTime (fun p : Bool × (ℕ × ℕ) ↦ if p.1 then [p.2] else [])
      (encPair encBool (encPair encNat encNat)) (encList (encPair encNat encNat)) :=
  ComputableInPolyTime.ite (fst encBool (encPair encNat encNat))
    (ComputableInPolyTime.cons' (snd encBool (encPair encNat encNat))
      (ComputableInPolyTime.const []))
    (ComputableInPolyTime.const [])

private lemma computableInPolyTime_cnfGetD :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ p.1.getD p.2 [])
      (encPair encCNF encUnary) (encList (encPair encNat encBool)) := by
  unfold encCNF
  exact listGetD []

private lemma computableInPolyTime_cnfLen :
    ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
  length_list (encList (encPair encNat encBool))

private lemma computableInPolyTime_clauseEdgeBranch (b : Bool) (r : ℕ) :
    ComputableInPolyTime
      (fun q : ((List ℕ × CNF ℕ) × ℕ) × ℕ ↦
        if (q.1.1.2.getD q.2 []).any (fun l ↦ decide (l = (q.1.1.1.getD q.1.2 0, b))) then
          [(cubicClauseV q.2, cubicVarV q.1.1.2.length q.1.2 q.2 r)] else [])
      (encPair (encPair (encPair (encList encNat) encCNF) encUnary) encUnary)
      (encList (encPair encNat encNat)) := by
  let encP := encPair (encList encNat) encCNF
  let encP1 := encPair encP encUnary
  let encQ := encPair encP1 encUnary
  have hq11 := (fst encP encUnary).comp (fst encP1 encUnary)
  have hq111 := (fst (encList encNat) encCNF).comp hq11
  have hq112 := (snd (encList encNat) encCNF).comp hq11
  have hq12 := (snd encP encUnary).comp (fst encP1 encUnary)
  have hq2 := snd encP1 encUnary
  have hv := listGetDWithInput hq111 hq12 0
  have hc := computableInPolyTime_cnfGetD.comp (hq112.prod hq2)
  have hqm := computableInPolyTime_cnfLen.comp hq112
  have hcl := (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4) ComputableInPolyTime.id')
      (ComputableInPolyTime.const 1))).comp hq2
  have hvr := computableInPolyTime_cubicVarV.comp
      (((hqm.prod hq12).prod hq2).prod (ComputableInPolyTime.const r))
  exact cpt_congr (computableInPolyTime_optEdge.comp
    (((computableInPolyTime_clauseLitCond b).comp (hc.prod hv)).prod (hcl.prod hvr)))
    fun q ↦ by simp only [Function.comp_apply, cubicClauseV]

private lemma computableInPolyTime_baseGraphOf_clauseEdges :
    ComputableInPolyTime
      (fun p : List ℕ × CNF ℕ ↦
        (polyRange p.1.length).flatMap fun i ↦
          (polyRange p.2.length).flatMap fun j ↦
            let v := p.1.getD i 0
            let c := p.2.getD j []
            (if c.any fun l ↦ decide (l = (v, true)) then
              [(cubicClauseV j, cubicVarV p.2.length i j 0)] else []) ++
            (if c.any fun l ↦ decide (l = (v, false)) then
              [(cubicClauseV j, cubicVarV p.2.length i j 1)] else []))
      (encPair (encList encNat) encCNF) (encList (encPair encNat encNat)) := by
  let encP := encPair (encList encNat) encCNF
  let encP1 := encPair encP encUnary
  have hstep := (ComputableInPolyTime.listAppend (encPair encNat encNat)).comp
    ((computableInPolyTime_clauseEdgeBranch true 0).prod
      (computableInPolyTime_clauseEdgeBranch false 1))
  have hn : ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦ p.1.length) encP encUnary :=
    (length_list encNat).comp (fst (encList encNat) encCNF)
  have hqm' : ComputableInPolyTime (fun p : (List ℕ × CNF ℕ) × ℕ ↦ p.1.2.length) encP1 encUnary :=
    ((length_list (encList (encPair encNat encBool))).comp (snd (encList encNat) encCNF)).comp
      (fst encP encUnary)
  exact flatMapWith (flatMapWith hstep ComputableInPolyTime.id'
    (computableInPolyTime_polyRange.comp hqm'))
    ComputableInPolyTime.id' (computableInPolyTime_polyRange.comp hn)

private lemma computableInPolyTime_baseGraphOf :
    ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦ baseGraphOf p.1 p.2)
      (encPair (encList encNat) encCNF) encGraph := by
  unfold baseGraphOf
  have hn : ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦ p.1.length)
      (encPair (encList encNat) encCNF) encUnary := (length_list encNat).comp (by fun_prop)
  have hm : ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦ p.2.length)
      (encPair (encList encNat) encCNF) encUnary :=
    (length_list (encList (encPair encNat encBool))).comp (by fun_prop)
  have hclV : ComputableInPolyTime cubicClauseV encUnary encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4) ComputableInPolyTime.id')
      (ComputableInPolyTime.const 1))
  have hfstU : ComputableInPolyTime (fun q : ℕ × ℕ ↦ q.1) (encPair encUnary encUnary) encUnary := by
    fun_prop
  let encT := encPair (encPair encUnary encUnary) encUnary
  have h0 := computableInPolyTime_cubicVarV.comp
    (ComputableInPolyTime.id'.pair (ComputableInPolyTime.const (encIn := encT) (encOut :=
      encUnary) 0))
  have h1 := computableInPolyTime_cubicVarV.comp
    (ComputableInPolyTime.id'.pair (ComputableInPolyTime.const (encIn := encT) (encOut :=
      encUnary) 1))
  have h2 := computableInPolyTime_cubicVarV.comp
    (ComputableInPolyTime.id'.pair (ComputableInPolyTime.const (encIn := encT) (encOut :=
      encUnary) 2))
  have hvv : ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦
      (polyRange p.1.length).flatMap fun i ↦ (polyRange p.2.length).flatMap fun j ↦
        [cubicVarV p.2.length i j 0, cubicVarV p.2.length i j 1, cubicVarV p.2.length i j 2])
      (encPair (encList encNat) encCNF) (encList encNat) :=
    flatMapWith (flatMapWith (ComputableInPolyTime.cons' h0 (ComputableInPolyTime.cons' h1
      (ComputableInPolyTime.cons' h2 (ComputableInPolyTime.const (encIn := encT)
        (encOut := encList encNat) []))))
      ComputableInPolyTime.id' (computableInPolyTime_polyRange.comp hfstU))
      hm (computableInPolyTime_polyRange.comp hn)
  have hcv : ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦ (polyRange p.2.length).map cubicClauseV)
      (encPair (encList encNat) encCNF) (encList encNat) :=
    mapWith (hclV.comp (by fun_prop : ComputableInPolyTime (fun q : Bool × ℕ ↦ q.2)
      (encPair encBool encUnary) encUnary))
      (ComputableInPolyTime.const (encOut :=
        encBool) false) (computableInPolyTime_polyRange.comp hm)
  have hre : ComputableInPolyTime (fun p : List ℕ × CNF ℕ ↦
      (polyRange p.1.length).flatMap fun i ↦ (polyRange p.2.length).flatMap fun j ↦
        let jnext := if j + 1 < p.2.length then j + 1 else 0
        [(cubicVarV p.2.length i j 0, cubicVarV p.2.length i j 1),
         (cubicVarV p.2.length i j 1, cubicVarV p.2.length i j 2),
         (cubicVarV p.2.length i j 2, cubicVarV p.2.length i jnext 0)])
      (encPair (encList encNat) encCNF) (encList (encPair encNat encNat)) := by
    have hq2 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ q.2) encT encUnary := by fun_prop
    have hq11 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ q.1.1) encT encUnary := by fun_prop
    have hq1 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ q.1)
        encT (encPair encUnary encUnary) := by fun_prop
    have hq2p1 := ComputableInPolyTime.unary_add' hq2 (ComputableInPolyTime.const 1)
    have hjn : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × ℕ ↦ if q.2 + 1 < q.1.1 then q.2 + 1 else 0) encT encUnary :=
      cpt_congr (ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hq2p1 hq11)
        hq2p1 (ComputableInPolyTime.const 0)) fun _ ↦ by simp
    have h0n := computableInPolyTime_cubicVarV.comp
      ((hq1.prod hjn).prod (ComputableInPolyTime.const (encIn := encT) (encOut := encUnary) 0))
    have htrip := ComputableInPolyTime.cons' (h0.pair h1) (ComputableInPolyTime.cons' (h1.pair h2)
      (ComputableInPolyTime.cons' (h2.pair h0n)
        (ComputableInPolyTime.const (encIn := encT) (encOut :=
          encList (encPair encNat encNat)) [])))
    exact flatMapWith (flatMapWith htrip ComputableInPolyTime.id'
      (computableInPolyTime_polyRange.comp hfstU)) hm (computableInPolyTime_polyRange.comp hn)
  exact encGraph_mk_polyTime
    ((ComputableInPolyTime.listAppend encNat).comp (hvv.pair hcv))
    ((ComputableInPolyTime.listAppend (encPair encNat encNat)).comp
      (hre.pair computableInPolyTime_baseGraphOf_clauseEdges))

private lemma computableInPolyTime_normClauses :
    ComputableInPolyTime normClauses encCNF encCNF := by
  unfold normClauses
  have hvars : ComputableInPolyTime (fun φ : CNF ℕ ↦ dedupList φ.vars) encCNF (encList encNat) :=
    computableInPolyTime_dedupList_nat.comp (CNF.computableInPolyTime_vars encNat)
  have h1 : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.map dedupList) encCNF encCNF :=
    mapWith (computableInPolyTime_dedupList_lit.comp (snd encBool _))
      (ComputableInPolyTime.const (encOut := encBool) false) ComputableInPolyTime.id'
  have hrng : ComputableInPolyTime (fun φ : CNF ℕ ↦ polyRange (dedupList φ.vars).length)
      encCNF (encList encUnary) :=
    computableInPolyTime_polyRange.comp ((length_list encNat).comp hvars)
  have hmkCl : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦
      let vs := dedupList p.1.vars; let n := vs.length
      dedupList [(vs.getD p.2 0, true), (vs.getD p.2 0, false),
        (vs.getD (if p.2 + 1 < n then p.2 + 1 else 0) 0, true)])
      (encPair encCNF encUnary) (encList (encPair encNat encBool)) := by
    have hvs := hvars.comp (fst encCNF encUnary)
    have hn := (length_list encNat).comp hvs
    have hv1 := listGetDWithInput hvs (snd encCNF encUnary) 0
    have hadd1 := ComputableInPolyTime.unary_add' (snd encCNF encUnary)
      (ComputableInPolyTime.const (encIn := encPair encCNF encUnary) 1)
    have hnext : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ if p.2 + 1 < (dedupList p.1.vars).length then p.2 + 1 else 0)
        (encPair encCNF encUnary) encUnary :=
      cpt_congr (ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hadd1 hn)
        hadd1 (ComputableInPolyTime.const (encIn := encPair encCNF encUnary) 0))
        fun _ ↦ by simp
    have hv2 := listGetDWithInput hvs hnext 0
    have hl1 := hv1.prod (ComputableInPolyTime.const (encIn := encPair encCNF encUnary)
      (encOut := encBool) true)
    have hl2 := hv1.prod (ComputableInPolyTime.const (encIn := encPair encCNF encUnary)
      (encOut := encBool) false)
    have hl3 := hv2.prod (ComputableInPolyTime.const (encIn := encPair encCNF encUnary)
      (encOut := encBool) true)
    exact computableInPolyTime_dedupList_lit.comp (ComputableInPolyTime.cons' hl1
      (ComputableInPolyTime.cons' hl2 (ComputableInPolyTime.cons' hl3
        (ComputableInPolyTime.const (encIn := encPair encCNF encUnary)
          (encOut := encList (encPair encNat encBool)) []))))
  have h2 := mapWith hmkCl ComputableInPolyTime.id' hrng
  have h1' : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.map dedupList)
      encCNF (encList (encList (encPair encNat encBool))) := h1
  exact (ComputableInPolyTime.listAppend (encList (encPair encNat encBool))).comp (h1'.prod h2)

private lemma computableInPolyTime_dsBranch :
    ComputableInPolyTime
      (fun p : (Bool × Bool) × DominatingSetInstance ↦
        if p.1.1 then ⟨k4Graph, 1⟩ else if !p.1.2 then ⟨k4Graph, 0⟩ else p.2)
      (encPair (encPair encBool encBool) encDominatingSet) encDominatingSet :=
  ComputableInPolyTime.ite
    ((fst encBool encBool).comp (fst (encPair encBool encBool) encDominatingSet))
    (ComputableInPolyTime.const (⟨k4Graph, 1⟩ : DominatingSetInstance))
    (ComputableInPolyTime.ite
      (ComputableInPolyTime.bool_not.comp
        ((snd encBool encBool).comp (fst (encPair encBool encBool) encDominatingSet)))
      (ComputableInPolyTime.const (⟨k4Graph, 0⟩ : DominatingSetInstance))
      (snd (encPair encBool encBool) encDominatingSet))

private lemma computableInPolyTime_isNontrivialThreeCNF :
    ComputableInPolyTime isNontrivialThreeCNF encCNF encBool := by
  unfold isNontrivialThreeCNF
  have h1 := ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const 0)
    computableInPolyTime_cnfLen
  have hclen := (length_list (encPair encNat encBool)).comp
    (snd encCNF (encList (encPair encNat encBool)))
  have h2 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.all fun c ↦ decide (0 < c.length) && decide (c.length ≤ 3))
      encCNF encBool :=
    allWithInput (test := fun _ (c : Clause ℕ) ↦ decide (0 < c.length) && decide (c.length ≤ 3))
      ComputableInPolyTime.id' (bool_and'
        (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const 0) hclen)
        (ComputableInPolyTime.unary_le' hclen (ComputableInPolyTime.const 3)))
  exact bool_and' h1 h2

private lemma computableInPolyTime_cubicSumU :
    ComputableInPolyTime (fun l : List ℕ ↦ l.sum) (encList encUnary) encUnary := by
  have heq : (fun l : List ℕ ↦ (l.flatMap fun n ↦ List.replicate n false).length) =
      (fun l : List ℕ ↦ l.sum) := by
    funext l; induction l with | nil => simp | cons a as ih => simp [ih]
  exact heq ▸ (length_list encBool).comp (flatMapWith
    (ComputableInPolyTime.replicate (snd encBool encUnary) (ComputableInPolyTime.const false))
    (ComputableInPolyTime.const (encOut := encBool) false) ComputableInPolyTime.id')

private lemma computableInPolyTime_deficitSum :
    ComputableInPolyTime
      (fun B : Graph ↦ (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum)
      encGraph encUnary :=
  computableInPolyTime_cubicSumU.comp
    (mapWith (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.const 3)
        computableInPolyTime_cubicGraphDegBool)
      ComputableInPolyTime.id' (by fun_prop))

private lemma computableInPolyTime_baseOf :
    ComputableInPolyTime (fun φ : CNF ℕ ↦ baseGraphOf (dedupList φ.vars) (normClauses φ))
      encCNF encGraph :=
  cpt_congr (computableInPolyTime_baseGraphOf.comp
    ((computableInPolyTime_dedupList_nat.comp (CNF.computableInPolyTime_vars encNat)).prod
      computableInPolyTime_normClauses)) fun _ ↦ by simp only [Function.comp_apply]

private lemma computableInPolyTime_cubicBudget :
    ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (dedupList φ.vars).length * (normClauses φ).length +
        2 * ((baseGraphOf (dedupList φ.vars) (normClauses φ)).vertices.map
          fun u ↦ 3 - cubicGraphDegBool (baseGraphOf (dedupList φ.vars) (normClauses φ)) u).sum)
      encCNF encNat :=
  cpt_congr (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul'
      ((length_list encNat).comp
        (computableInPolyTime_dedupList_nat.comp (CNF.computableInPolyTime_vars encNat)))
      (computableInPolyTime_cnfLen.comp computableInPolyTime_normClauses))
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
      (computableInPolyTime_deficitSum.comp computableInPolyTime_baseOf))))
    fun _ ↦ by simp only [Function.comp_apply]

private lemma computableInPolyTime_mainCubic :
    ComputableInPolyTime (fun φ : CNF ℕ ↦
      let vars := dedupList φ.vars; let clauses := normClauses φ
      let B := baseGraphOf vars clauses
      (⟨cappedGraphOf B, vars.length * clauses.length +
        2 * (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum⟩ : DominatingSetInstance))
      encCNF encDominatingSet :=
  cpt_congr (encDominatingSet_mk_polyTime
    (cpt_congr (computableInPolyTime_cappedGraphOf.comp computableInPolyTime_baseOf)
      fun _ ↦ by simp only [Function.comp_apply]) computableInPolyTime_cubicBudget) fun _ ↦ rfl

/-- `toCubicDominatingSet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toCubicDominatingSet :
    ComputableInPolyTime toCubicDominatingSet encCNF encDominatingSet :=
  cpt_congr (computableInPolyTime_dsBranch.comp
    (((cpt_congr (g := List.isEmpty) (ComputableInPolyTime.unary_le' computableInPolyTime_cnfLen
      (ComputableInPolyTime.const 0)) fun φ ↦ by cases φ <;> simp).prod
        computableInPolyTime_isNontrivialThreeCNF).prod computableInPolyTime_mainCubic))
    fun φ ↦ by simp only [Function.comp_apply, toCubicDominatingSet]

/-- Polynomial-time many-one reduction from `ThreeSAT` to `CubicDominatingSet`. -/
theorem polyTimeReducible_ThreeSAT_CubicDominatingSet :
    PolyTimeReducible encCNF encDominatingSet ThreeSAT CubicDominatingSet :=
  ⟨toCubicDominatingSet, computableInPolyTime_toCubicDominatingSet,
    fun φ ↦ (toCubicDominatingSet_mem_iff φ).symm⟩

/-- `CubicDominatingSet` is `NP`-hard. -/
theorem CubicDominatingSet_npHard : NPHard encDominatingSet CubicDominatingSet :=
  fun _ enc C hC ↦ (ThreeSAT_npHard enc C hC).trans polyTimeReducible_ThreeSAT_CubicDominatingSet

/-- **NP-completeness of Connected Cubic Dominating Set**: `CubicDominatingSet` is `NP`-complete
under polynomial-time many-one reductions. -/
theorem CubicDominatingSet_npComplete : NPComplete encDominatingSet CubicDominatingSet :=
  ⟨CubicDominatingSet.mem_NP, CubicDominatingSet_npHard⟩

end CslibFrontier.Complexity
