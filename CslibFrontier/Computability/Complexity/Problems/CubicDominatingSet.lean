module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.ExactThreeSAT

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# NP-Completeness of Dominating Set on Cubic Graphs

This module proves that the **Dominating Set** decision problem restricted to cubic (`3`-regular)
graphs (`CubicDominatingSet`) is `NP`-complete on multi-tape Turing machines under standard Lean
axioms:

* `CubicDominatingSet`, `isCubicBool`, and `CubicDominatingSet_mem_NP`: **Dominating Set**
  restricted to cubic (`3`-regular) graphs and its membership in `NP`.
* `toCubicDominatingSet`, `computableInPolyTime_toCubicDominatingSet`, and
  `toCubicDominatingSet_mem_iff`: polynomial-time Karp reduction from `ExactThreeSAT` via a
  `13`-vertex cubic variable-occurrence gadget (`3` ports of internal degree `2` and `10` internal
  degree-`3` vertices, minimum internal dominating number `4`).
* `CubicDominatingSet_npHard` and `CubicDominatingSet_npComplete`: `NP`-hardness and
  `NP`-completeness of `CubicDominatingSet`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- **Dominating Set on cubic (`3`-regular) graphs**. -/
@[expose] def CubicDominatingSet : Set DominatingSetInstance :=
  {x | x.graph.induced.IsRegularOfDegree 3 ∧ x ∈ DominatingSet}

/-- Membership characterization of `CubicDominatingSet`. -/
theorem mem_CubicDominatingSet_iff (x : DominatingSetInstance) :
    x ∈ CubicDominatingSet ↔ x.graph.induced.IsRegularOfDegree 3 ∧ x ∈ DominatingSet := Iff.rfl

/-- Executable `3`-regularity test on `G.induced`. -/
def isCubicBool (G : Graph) : Bool :=
  G.distinctVertices.all fun u ↦
    decide ((G.distinctVertices.filter fun v ↦ G.adjBool u v).length = 3)

@[fun_prop] theorem computableInPolyTime_isCubicBool :
    ComputableInPolyTime isCubicBool encGraph encBool := by
  unfold isCubicBool; fun_prop

theorem isCubicBool_eq_true_iff (G : Graph) :
    isCubicBool G = true ↔ G.induced.IsRegularOfDegree 3 := by
  classical
  simp only [isCubicBool, List.all_eq_true, Graph.mem_distinctVertices, decide_eq_true_eq,
    _root_.SimpleGraph.IsRegularOfDegree]
  have hdeg : ∀ (u : ℕ) (hu : u ∈ G.vertices),
      (G.distinctVertices.filter fun v ↦ G.adjBool u v).length = G.induced.degree ⟨u, hu⟩ := by
    intro u hu
    rw [← List.toFinset_card_of_nodup (G.nodup_distinctVertices.filter _),
      ← G.induced.card_neighborFinset_eq_degree]
    have heq : (G.distinctVertices.filter fun v ↦ G.adjBool u v).toFinset =
        (G.induced.neighborFinset ⟨u, hu⟩).map (Function.Embedding.subtype _) := by
      ext v
      simp only [List.mem_toFinset, List.mem_filter, Graph.mem_distinctVertices,
        Graph.adjBool_eq_true_iff, Finset.mem_map, Function.Embedding.coe_subtype,
        _root_.SimpleGraph.mem_neighborFinset, Graph.induced_adj, Subtype.exists]
      exact ⟨fun ⟨hv, ha⟩ ↦ ⟨v, hv, ha, rfl⟩, by rintro ⟨w, hw, ha, rfl⟩; exact ⟨hw, ha⟩⟩
    rw [heq, Finset.card_map]
  exact ⟨fun h ⟨u, hu⟩ ↦ (hdeg u hu).symm.trans (h u hu),
    fun h u hu ↦ (hdeg u hu).trans (h ⟨u, hu⟩)⟩

/-- `CubicDominatingSet` belongs to `NP`. -/
theorem CubicDominatingSet_mem_NP : CubicDominatingSet ∈ NP encDominatingSet := by
  have hset : (CubicDominatingSet : Set DominatingSetInstance) =
      {x : DominatingSetInstance | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
        (isCubicBool x.graph = true ∧ S.card = x.bound ∧
          (∀ v ∈ x.graph.vertices, v ∈ S ∨ ∃ s ∈ S, x.graph.toSimpleGraph.Adj v s))} := by
    ext ⟨G, k⟩
    simp only [CubicDominatingSet, Set.mem_ofPred_eq, isCubicBool_eq_true_iff,
      mem_DominatingSet_iff]
    exact ⟨fun ⟨hcub, S, hSV, hdom, hcard⟩ ↦ ⟨S, hSV, hcub, hcard, hdom⟩,
      fun ⟨S, hSV, hcub, hcard, hdom⟩ ↦ ⟨hcub, S, hSV, hdom, hcard⟩⟩
  change (CubicDominatingSet : Set DominatingSetInstance) ∈ NP encDominatingSet
  rw [hset]
  refine mem_NP_of_subsetWitness (encγ := encNat)
    (vs := fun (x : DominatingSetInstance) ↦ x.graph.vertices)
    (check := fun (y : DominatingSetInstance × List ℕ) ↦
      isCubicBool y.1.graph && decide (y.2.length = y.1.bound) &&
      DominatingSet.isDominating y.1.graph y.2) (by fun_prop) (by fun_prop) fun x l hl _ ↦ ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, DominatingSet.isDominating_eq_true_iff,
    List.mem_toFinset, List.toFinset_card_of_nodup hl, and_assoc]

/-! ### The `13`-vertex cubic variable-occurrence gadget `H₁₃` -/

private def h13Edges : List (ℕ × ℕ) :=
  [(0, 4), (0, 5), (1, 2), (1, 10), (2, 9), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11),
   (5, 7), (5, 9), (6, 8), (6, 11), (6, 12), (7, 8), (8, 9), (10, 12)]

private def h13Adj (u v : Fin 13) : Bool :=
  h13Edges.any fun e ↦ decide ((e.1 = u.1 ∧ e.2 = v.1) ∨ (e.1 = v.1 ∧ e.2 = u.1))

private def h13Closed (u v : Fin 13) : Bool :=
  decide (u = v) || h13Adj u v

private def h13DomInternal (S : Finset (Fin 13)) : Prop :=
  ∀ u : Fin 13, 3 ≤ u.1 → ∃ w ∈ S, h13Closed u w = true

private def h13N10 : Fin 4 → Fin 13 := ![1, 4, 10, 12]
private def h13N9 : Fin 4 → Fin 13 := ![2, 5, 8, 9]
private def h13N3 : Fin 4 → Fin 13 := ![3, 7, 11, 12]

private lemma h13_no_three_dom (a b : Fin 4) (z : Fin 13) :
    ∃ u : Fin 13, 3 ≤ u.1 ∧
      h13Closed u (h13N10 a) = false ∧
      h13Closed u (h13N9 b) = false ∧
      h13Closed u z = false := by
  fin_cases a <;> fin_cases b <;> revert z <;> decide

private lemma h13_no_zero_two_four (a : Fin 4) (z : Fin 13) :
    ∃ u : Fin 13, 3 ≤ u.1 ∧
      h13Closed u 0 = false ∧ h13Closed u 2 = false ∧
      h13Closed u (h13N10 a) = false ∧ h13Closed u z = false := by
  fin_cases a <;> revert z <;> decide

private lemma h13_no_one_two_four (a : Fin 4) (z : Fin 13) :
    ∃ u : Fin 13, 3 ≤ u.1 ∧
      h13Closed u 1 = false ∧ h13Closed u 2 = false ∧
      h13Closed u (h13N3 a) = false ∧ h13Closed u z = false := by
  fin_cases a <;> revert z <;> decide

private lemma h13_closed_ten (w : Fin 13) (h : h13Closed 10 w = true) :
    ∃ a : Fin 4, w = h13N10 a := by
  revert w; decide

private lemma h13_closed_nine (w : Fin 13) (h : h13Closed 9 w = true) :
    ∃ b : Fin 4, w = h13N9 b := by
  revert w; decide

private lemma h13_closed_three (w : Fin 13) (h : h13Closed 3 w = true) :
    ∃ a : Fin 4, w = h13N3 a := by
  revert w; decide

private lemma h13N10_ne_h13N9 (a b : Fin 4) : h13N10 a ≠ h13N9 b := by
  revert a b; decide

private lemma h13N10_ne_zero_two (a : Fin 4) : h13N10 a ≠ 0 ∧ h13N10 a ≠ 2 := by
  revert a; decide

private lemma h13N3_ne_one_two (a : Fin 4) : h13N3 a ≠ 1 ∧ h13N3 a ≠ 2 := by
  revert a; decide

private lemma h13_exists_singleton {R : Finset (Fin 13)} (hR : R.card ≤ 1) :
    ∃ z : Fin 13, ∀ w ∈ R, w = z := by
  rcases Nat.eq_zero_or_pos R.card with h0 | _
  · exact ⟨0, fun w hw ↦ (Finset.notMem_empty w (Finset.card_eq_zero.mp h0 ▸ hw)).elim⟩
  · obtain ⟨z, hzR⟩ := Finset.card_eq_one.mp (by omega : R.card = 1)
    exact ⟨z, fun w hw ↦ Finset.mem_singleton.mp (hzR ▸ hw)⟩

private lemma h13_four_le_card_of_domInternal {S : Finset (Fin 13)} (hS : h13DomInternal S) :
    4 ≤ S.card := by
  by_contra hlt
  obtain ⟨w₁, hw₁S, hw₁⟩ := hS 10 (by decide)
  obtain ⟨a, rfl⟩ := h13_closed_ten w₁ hw₁
  obtain ⟨w₂, hw₂S, hw₂⟩ := hS 9 (by decide)
  obtain ⟨b, rfl⟩ := h13_closed_nine w₂ hw₂
  have hne : h13N10 a ≠ h13N9 b := h13N10_ne_h13N9 a b
  let R := (S.erase (h13N10 a)).erase (h13N9 b)
  have c1 := Finset.card_erase_add_one hw₁S
  have c2 : R.card + 1 = (S.erase (h13N10 a)).card :=
    Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne.symm, hw₂S⟩)
  obtain ⟨z, hz⟩ := h13_exists_singleton (R := R) (by omega)
  obtain ⟨u, hu3, hn1, hn2, hn3⟩ := h13_no_three_dom a b z
  obtain ⟨w, hwS, hwu⟩ := hS u hu3
  by_cases hw1 : w = h13N10 a
  · subst hw1; exact Bool.false_ne_true (hn1.symm.trans hwu)
  · by_cases hw2 : w = h13N9 b
    · subst hw2; exact Bool.false_ne_true (hn2.symm.trans hwu)
    · have hwz : w = z := hz w (Finset.mem_erase.mpr ⟨hw2, Finset.mem_erase.mpr ⟨hw1, hwS⟩⟩)
      subst hwz; exact Bool.false_ne_true (hn3.symm.trans hwu)

private lemma h13_port_exclusion {S : Finset (Fin 13)} (hS : h13DomInternal S)
    (hcard : S.card ≤ 4) (h01 : (0 : Fin 13) ∈ S ∨ (1 : Fin 13) ∈ S) (h2 : (2 : Fin 13) ∈ S) :
    False := by
  rcases h01 with h0 | h1
  · obtain ⟨w, hwS, hw⟩ := hS 10 (by decide)
    obtain ⟨a, rfl⟩ := h13_closed_ten w hw
    obtain ⟨hne0, hne2⟩ := h13N10_ne_zero_two a
    let R := ((S.erase 0).erase 2).erase (h13N10 a)
    have c1 := Finset.card_erase_add_one h0
    have c2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨(by decide : (2 : Fin 13) ≠ 0), h2⟩)
    have c3 : R.card + 1 = ((S.erase 0).erase 2).card :=
      Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne0, hwS⟩⟩)
    obtain ⟨z, hz⟩ := h13_exists_singleton (R := R) (by omega)
    obtain ⟨u, hu3, fn0, fn2, fna, fnz⟩ := h13_no_zero_two_four a z
    obtain ⟨x, hxS, hxu⟩ := hS u hu3
    by_cases hx0 : x = 0
    · subst hx0; exact Bool.false_ne_true (fn0.symm.trans hxu)
    · by_cases hx2 : x = 2
      · subst hx2; exact Bool.false_ne_true (fn2.symm.trans hxu)
      · by_cases hxa : x = h13N10 a
        · subst hxa; exact Bool.false_ne_true (fna.symm.trans hxu)
        · have hxz := hz x (Finset.mem_erase.mpr
            ⟨hxa, Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr ⟨hx0, hxS⟩⟩⟩)
          subst hxz; exact Bool.false_ne_true (fnz.symm.trans hxu)
  · obtain ⟨w, hwS, hw⟩ := hS 3 (by decide)
    obtain ⟨a, rfl⟩ := h13_closed_three w hw
    obtain ⟨hne1, hne2⟩ := h13N3_ne_one_two a
    let R := ((S.erase 1).erase 2).erase (h13N3 a)
    have c1 := Finset.card_erase_add_one h1
    have c2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨(by decide : (2 : Fin 13) ≠ 1), h2⟩)
    have c3 : R.card + 1 = ((S.erase 1).erase 2).card :=
      Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hwS⟩⟩)
    obtain ⟨z, hz⟩ := h13_exists_singleton (R := R) (by omega)
    obtain ⟨u, hu3, fn1, fn2, fna, fnz⟩ := h13_no_one_two_four a z
    obtain ⟨x, hxS, hxu⟩ := hS u hu3
    by_cases hx1 : x = 1
    · subst hx1; exact Bool.false_ne_true (fn1.symm.trans hxu)
    · by_cases hx2 : x = 2
      · subst hx2; exact Bool.false_ne_true (fn2.symm.trans hxu)
      · by_cases hxa : x = h13N3 a
        · subst hxa; exact Bool.false_ne_true (fna.symm.trans hxu)
        · have hxz := hz x (Finset.mem_erase.mpr
            ⟨hxa, Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr ⟨hx1, hxS⟩⟩⟩)
          subst hxz; exact Bool.false_ne_true (fnz.symm.trans hxu)

private def h13SHi : List ℕ := [0, 1, 3, 8]
private def h13SLo : List ℕ := [2, 4, 6, 7]

private lemma h13SHi_dom_all :
    ∀ u : Fin 13, ∃ w ∈ h13SHi, ∃ hw : w < 13, h13Closed u ⟨w, hw⟩ = true := by
  decide

private lemma h13SLo_dom_all :
    ∀ u : Fin 13, ∃ w ∈ h13SLo, ∃ hw : w < 13, h13Closed u ⟨w, hw⟩ = true := by
  decide

private lemma h13_internal_deg :
    ∀ u : Fin 13, ((List.finRange 13).filter fun v ↦ h13Adj u v).length =
      if u.1 < 3 then 2 else 3 := by
  decide

/-! ### Reduction from `ExactThreeSAT` to `CubicDominatingSet` -/

/-- The `4`-vertex complete graph `K₄`, used as base cubic gadget. -/
def k4Graph : Graph :=
  ⟨[0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩

theorem k4Graph_isCubic : k4Graph.induced.IsRegularOfDegree 3 :=
  (isCubicBool_eq_true_iff k4Graph).mp (by decide)

theorem k4Graph_one_mem_CubicDominatingSet :
    (⟨k4Graph, 1⟩ : DominatingSetInstance) ∈ CubicDominatingSet := by
  refine ⟨k4Graph_isCubic, mem_DominatingSet_iff.mpr ⟨{0}, fun v hv ↦ ?_, fun v hv ↦ ?_, by simp⟩⟩
  · simp only [Finset.mem_singleton] at hv; subst hv; decide
  · by_cases hv0 : v = 0
    · exact Or.inl (Finset.mem_singleton.mpr hv0)
    · refine Or.inr ⟨0, Finset.mem_singleton_self 0, Graph.toSimpleGraph_adj.mpr ⟨hv0, Or.inr ?_⟩⟩
      simp only [k4Graph, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
      rcases hv with rfl | rfl | rfl | rfl
      exacts [(hv0 rfl).elim, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))]

theorem k4Graph_zero_notMem_CubicDominatingSet :
    (⟨k4Graph, 0⟩ : DominatingSetInstance) ∉ CubicDominatingSet := by
  rintro ⟨_, hdom⟩
  obtain ⟨S, _, hS, hcard⟩ := mem_DominatingSet_iff.mp hdom
  rw [Finset.card_eq_zero.mp hcard] at hS
  simpa using hS 0 (by decide)

private def gadVert (s u : ℕ) : ℕ := 4 * (16 * s + u)
private def ternVert (i : ℕ) : ℕ := 4 * i + 1
private def binVert (s : ℕ) : ℕ := 4 * s + 2

private def occSlots (L : List (ℕ × Bool)) (v : ℕ) : List ℕ :=
  (List.range L.length).filter fun t ↦ decide ((L.getD t (0, false)).1 = v)

private def nextSlot (L : List (ℕ × Bool)) (s : ℕ) : ℕ :=
  let occ := occSlots L (L.getD s (0, false)).1
  let idx := occ.idxOf s
  if idx + 1 < occ.length then occ.getD (idx + 1) 0 else occ.getD 0 0

private def negPort (L : List (ℕ × Bool)) (s : ℕ) : ℕ :=
  if (L.getD s (0, false)).2 then 2 else 1

private def posBinPort (L : List (ℕ × Bool)) (s : ℕ) : ℕ :=
  if (L.getD s (0, false)).2 then 1 else 2

private def isNonemptyExact3 (φ : CNF ℕ) : Bool :=
  !φ.isEmpty && φ.all fun c ↦ decide (c.length = 3)

private def cubicSATGraph (φ : CNF ℕ) : Graph :=
  let ψ := φ ++ φ
  let M := ψ.length
  let L := ψ.flatten
  let vGad := (List.range (3 * M)).flatMap fun s ↦ (List.range 13).map fun u ↦ gadVert s u
  let vTern := (List.range M).map ternVert
  let vBin := (List.range (3 * M)).map binVert
  let eGad := (List.range (3 * M)).flatMap fun s ↦
    h13Edges.map fun e ↦ (gadVert s e.1, gadVert s e.2)
  let eTern := (List.range M).flatMap fun i ↦
    [0, 1, 2].map fun p ↦ (ternVert i, gadVert (3 * i + p) 0)
  let eBin := (List.range (3 * M)).flatMap fun s ↦
    [(binVert s, gadVert s (negPort L s)),
     (binVert s, gadVert (nextSlot L s) (posBinPort L (nextSlot L s)))]
  let ePair := (List.range (3 * φ.length)).map fun t ↦ (binVert (2 * t), binVert (2 * t + 1))
  ⟨(vGad ++ vTern) ++ vBin, ((eGad ++ eTern) ++ eBin) ++ ePair⟩

/-- Polynomial-time reduction from `ExactThreeSAT` to `CubicDominatingSet`. -/
def toCubicDominatingSet (φ : CNF ℕ) : DominatingSetInstance :=
  if φ.isEmpty then ⟨k4Graph, 1⟩
  else if isNonemptyExact3 φ then ⟨cubicSATGraph φ, 24 * φ.length⟩
  else ⟨k4Graph, 0⟩

section CubicPolyTime

private abbrev encLit : (ℕ × Bool) ↪ List Bool := encPair encNat encBool
private abbrev encLitList : List (ℕ × Bool) ↪ List Bool := encList encLit

@[local fun_prop]
private theorem computableInPolyTime_occSlots :
    ComputableInPolyTime (fun p : List (ℕ × Bool) × ℕ ↦ occSlots p.1 p.2)
      (encPair encLitList encNat) (encList encUnary) := by
  unfold occSlots
  refine filterWithInput (range.comp ((length_list encLit).comp (fst _ _))) ?_
  have hget : ComputableInPolyTime
      (fun q : (List (ℕ × Bool) × ℕ) × ℕ ↦ q.1.1.getD q.2 (0, false))
      (encPair (encPair encLitList encNat) encUnary) encLit :=
    listGetDWithInput ((fst _ _).comp (fst _ _)) (snd _ _) (0, false)
  exact ((fst encNat encBool).comp hget).decide_eq' ((snd _ _).comp (fst _ _))

@[local fun_prop]
private theorem computableInPolyTime_nextSlot :
    ComputableInPolyTime (fun p : List (ℕ × Bool) × ℕ ↦ nextSlot p.1 p.2)
      (encPair encLitList encUnary) encUnary := by
  have hlit : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ p.1.getD p.2 (0, false))
      (encPair encLitList encUnary) encLit :=
    listGetDWithInput (fst _ _) (snd _ _) (0, false)
  have hocc : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ occSlots p.1 (p.1.getD p.2 (0, false)).1)
      (encPair encLitList encUnary) (encList encUnary) :=
    computableInPolyTime_occSlots.comp ((fst _ _).prod ((fst encNat encBool).comp hlit))
  have hidx : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ (occSlots p.1 (p.1.getD p.2 (0, false)).1).idxOf p.2)
      (encPair encLitList encUnary) encUnary :=
    idxOfWithInput hocc (snd _ _)
  have hlen : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ (occSlots p.1 (p.1.getD p.2 (0, false)).1).length)
      (encPair encLitList encUnary) encUnary :=
    (length_list encUnary).comp hocc
  have hcond : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦
        decide ((occSlots p.1 (p.1.getD p.2 (0, false)).1).idxOf p.2 + 1 <
          (occSlots p.1 (p.1.getD p.2 (0, false)).1).length))
      (encPair encLitList encUnary) encBool := by
    have hadd : ComputableInPolyTime
        (fun p : List (ℕ × Bool) × ℕ ↦
          (occSlots p.1 (p.1.getD p.2 (0, false)).1).idxOf p.2 + 1)
        (encPair encLitList encUnary) encUnary :=
      unary_add.comp (hidx.prod (const 1))
    exact unary_lt.comp (hadd.prod hlen)
  have hthen : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦
        (occSlots p.1 (p.1.getD p.2 (0, false)).1).getD
          ((occSlots p.1 (p.1.getD p.2 (0, false)).1).idxOf p.2 + 1) 0)
      (encPair encLitList encUnary) encUnary :=
    listGetDWithInput hocc (unary_add.comp (hidx.prod (const 1))) 0
  have helse : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦
        (occSlots p.1 (p.1.getD p.2 (0, false)).1).getD 0 0)
      (encPair encLitList encUnary) encUnary :=
    listGetDWithInput hocc (const 0) 0
  have heq : (fun p : List (ℕ × Bool) × ℕ ↦ nextSlot p.1 p.2) =
      fun p ↦ if decide ((occSlots p.1 (p.1.getD p.2 (0, false)).1).idxOf p.2 + 1 <
        (occSlots p.1 (p.1.getD p.2 (0, false)).1).length)
      then (occSlots p.1 (p.1.getD p.2 (0, false)).1).getD
        ((occSlots p.1 (p.1.getD p.2 (0, false)).1).idxOf p.2 + 1) 0
      else (occSlots p.1 (p.1.getD p.2 (0, false)).1).getD 0 0 := by
    funext p; simp [nextSlot]
  rw [heq]
  exact ite hcond hthen helse

@[local fun_prop]
private theorem computableInPolyTime_negPort :
    ComputableInPolyTime (fun p : List (ℕ × Bool) × ℕ ↦ negPort p.1 p.2)
      (encPair encLitList encUnary) encUnary := by
  unfold negPort
  have hlit : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ p.1.getD p.2 (0, false))
      (encPair encLitList encUnary) encLit :=
    listGetDWithInput (fst _ _) (snd _ _) (0, false)
  exact ite ((snd encNat encBool).comp hlit) (const 2) (const 1)

@[local fun_prop]
private theorem computableInPolyTime_posBinPort :
    ComputableInPolyTime (fun p : List (ℕ × Bool) × ℕ ↦ posBinPort p.1 p.2)
      (encPair encLitList encUnary) encUnary := by
  unfold posBinPort
  have hlit : ComputableInPolyTime
      (fun p : List (ℕ × Bool) × ℕ ↦ p.1.getD p.2 (0, false))
      (encPair encLitList encUnary) encLit :=
    listGetDWithInput (fst _ _) (snd _ _) (0, false)
  exact ite ((snd encNat encBool).comp hlit) (const 1) (const 2)

@[local fun_prop]
private theorem computableInPolyTime_gadVert_unary :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ gadVert p.1 p.2)
      (encPair encUnary encUnary) encNat := by
  unfold gadVert
  exact unary_to_binary.comp (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_ternVert_unary :
    ComputableInPolyTime ternVert encUnary encNat := by
  unfold ternVert
  exact unary_to_binary.comp (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_binVert_unary :
    ComputableInPolyTime binVert encUnary encNat := by
  unfold binVert
  exact unary_to_binary.comp (by fun_prop)

attribute [local irreducible] occSlots nextSlot negPort posBinPort gadVert ternVert binVert

private def cubicSATEBin (φ : CNF ℕ) : List (ℕ × ℕ) :=
  let ψ := φ ++ φ
  let L := ψ.flatten
  (List.range (3 * ψ.length)).flatMap fun s ↦
    [(binVert s, gadVert s (negPort L s)),
     (binVert s, gadVert (nextSlot L s) (posBinPort L (nextSlot L s)))]

private theorem computableInPolyTime_cubicSATEBin :
    ComputableInPolyTime cubicSATEBin encCNF (encList (encPair encNat encNat)) := by
  unfold cubicSATEBin
  set E := encPair encCNF encUnary
  set P := encPair encNat encNat
  have hψ : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ ++ φ) encCNF encCNF :=
    listAppend' id' id'
  have hM : ComputableInPolyTime (fun φ : CNF ℕ ↦ (φ ++ φ).length) encCNF encUnary :=
    (length_list (encList encLit)).comp hψ
  have h3mul : ComputableInPolyTime (fun n : ℕ ↦ 3 * n) encUnary encUnary := by fun_prop
  have h3M : ComputableInPolyTime (fun φ : CNF ℕ ↦ 3 * (φ ++ φ).length) encCNF encUnary :=
    h3mul.comp hM
  have hL : ComputableInPolyTime (fun φ : CNF ℕ ↦ (φ ++ φ).flatten) encCNF encLitList :=
    (flatten encLit).comp hψ
  have hLq : ComputableInPolyTime (fun q : CNF ℕ × ℕ ↦ (q.1 ++ q.1).flatten) E encLitList :=
    hL.comp (fst encCNF encUnary)
  have hsq : ComputableInPolyTime (fun q : CNF ℕ × ℕ ↦ q.2) E encUnary :=
    snd encCNF encUnary
  have hnxt : ComputableInPolyTime
      (fun q : CNF ℕ × ℕ ↦ nextSlot (q.1 ++ q.1).flatten q.2) E encUnary :=
    computableInPolyTime_nextSlot.comp (hLq.prod hsq)
  have hneg : ComputableInPolyTime
      (fun q : CNF ℕ × ℕ ↦ negPort (q.1 ++ q.1).flatten q.2) E encUnary :=
    computableInPolyTime_negPort.comp (hLq.prod hsq)
  have hpos : ComputableInPolyTime
      (fun q : CNF ℕ × ℕ ↦ posBinPort (q.1 ++ q.1).flatten (nextSlot (q.1 ++ q.1).flatten q.2))
      E encUnary :=
    computableInPolyTime_posBinPort.comp (hLq.prod hnxt)
  have hbin : ComputableInPolyTime (fun q : CNF ℕ × ℕ ↦ binVert q.2) E encNat :=
    computableInPolyTime_binVert_unary.comp hsq
  have hp1 : ComputableInPolyTime
      (fun q : CNF ℕ × ℕ ↦ (binVert q.2, gadVert q.2 (negPort (q.1 ++ q.1).flatten q.2))) E P :=
    hbin.prod (computableInPolyTime_gadVert_unary.comp (hsq.prod hneg))
  have hp2 : ComputableInPolyTime
      (fun q : CNF ℕ × ℕ ↦ (binVert q.2,
        gadVert (nextSlot (q.1 ++ q.1).flatten q.2)
          (posBinPort (q.1 ++ q.1).flatten (nextSlot (q.1 ++ q.1).flatten q.2)))) E P :=
    hbin.prod (computableInPolyTime_gadVert_unary.comp (hnxt.prod hpos))
  have hnil : ComputableInPolyTime (fun _ : CNF ℕ × ℕ ↦ ([] : List (ℕ × ℕ))) E (encList P) :=
    const []
  exact flatMapWithInput (range.comp h3M) (hp1.cons' (hp2.cons' hnil))

private theorem computableInPolyTime_cubicSATGraph :
    ComputableInPolyTime cubicSATGraph encCNF encGraph := by
  have hψ : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ ++ φ) encCNF encCNF :=
    listAppend' id' id'
  have hM : ComputableInPolyTime (fun φ : CNF ℕ ↦ (φ ++ φ).length) encCNF encUnary :=
    (length_list (encList encLit)).comp hψ
  have h3mul : ComputableInPolyTime (fun n : ℕ ↦ 3 * n) encUnary encUnary := by fun_prop
  have h3M : ComputableInPolyTime (fun φ : CNF ℕ ↦ 3 * (φ ++ φ).length) encCNF encUnary :=
    h3mul.comp hM
  have hvGad : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (3 * (φ ++ φ).length)).flatMap fun s ↦
        (List.range 13).map fun u ↦ gadVert s u)
      encCNF (encList encNat) := by
    refine flatMapWithInput (range.comp h3M) ?_
    exact mapConst (List.range 13) fun u _ ↦
      computableInPolyTime_gadVert_unary.comp ((snd encCNF encUnary).prod (const u))
  have hvTern : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (φ ++ φ).length).map ternVert)
      encCNF (encList encNat) :=
    mapWithInput (range.comp hM) (computableInPolyTime_ternVert_unary.comp (snd encCNF encUnary))
  have hvBin : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (3 * (φ ++ φ).length)).map binVert)
      encCNF (encList encNat) :=
    mapWithInput (range.comp h3M) (computableInPolyTime_binVert_unary.comp (snd encCNF encUnary))
  have heGad : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (3 * (φ ++ φ).length)).flatMap fun s ↦
        h13Edges.map fun e ↦ (gadVert s e.1, gadVert s e.2))
      encCNF (encList (encPair encNat encNat)) := by
    refine flatMapWithInput (range.comp h3M) ?_
    exact mapConst h13Edges fun e _ ↦
      (computableInPolyTime_gadVert_unary.comp ((snd encCNF encUnary).prod (const e.1))).prod
        (computableInPolyTime_gadVert_unary.comp ((snd encCNF encUnary).prod (const e.2)))
  have heTern : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (φ ++ φ).length).flatMap fun i ↦
        [0, 1, 2].map fun p ↦ (ternVert i, gadVert (3 * i + p) 0))
      encCNF (encList (encPair encNat encNat)) := by
    refine flatMapWithInput (range.comp hM) ?_
    refine mapConst [0, 1, 2] fun p _ ↦ ?_
    have hp_step : ComputableInPolyTime (fun n : ℕ ↦ 3 * n + p) encUnary encUnary := by fun_prop
    have hidx : ComputableInPolyTime (fun q : CNF ℕ × ℕ ↦ 3 * q.2 + p)
        (encPair encCNF encUnary) encUnary := hp_step.comp (snd encCNF encUnary)
    exact (computableInPolyTime_ternVert_unary.comp (snd encCNF encUnary)).prod
      (computableInPolyTime_gadVert_unary.comp (hidx.prod (const 0)))
  have hePair : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (3 * φ.length)).map fun t ↦
        (binVert (2 * t), binVert (2 * t + 1)))
      encCNF (encList (encPair encNat encNat)) := by
    have h3len : ComputableInPolyTime (fun φ : CNF ℕ ↦ 3 * φ.length) encCNF encUnary :=
      h3mul.comp (length_list (encList encLit))
    refine mapWithInput (range.comp h3len) ?_
    have hm2 : ComputableInPolyTime (fun n : ℕ ↦ 2 * n) encUnary encUnary := by fun_prop
    have hm21 : ComputableInPolyTime (fun n : ℕ ↦ 2 * n + 1) encUnary encUnary := by fun_prop
    exact (computableInPolyTime_binVert_unary.comp (hm2.comp (snd encCNF encUnary))).prod
      (computableInPolyTime_binVert_unary.comp (hm21.comp (snd encCNF encUnary)))
  exact (encGraph_mk_polyTime
    (listAppend' (listAppend' hvGad hvTern) hvBin)
    (listAppend' (listAppend' (listAppend' heGad heTern) computableInPolyTime_cubicSATEBin)
      hePair)).of_enc_eq fun _ ↦ rfl

@[fun_prop]
theorem computableInPolyTime_toCubicDominatingSet :
    ComputableInPolyTime toCubicDominatingSet encCNF encDominatingSet := by
  have hemp : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.isEmpty) encCNF encBool :=
    listIsEmpty' (encList encLit)
  have hex3 : ComputableInPolyTime isNonemptyExact3 encCNF encBool := by
    unfold isNonemptyExact3
    refine bool_and' (bool_not.comp hemp) ?_
    refine allWithInput id' ?_
    have hclen : ComputableInPolyTime
        (fun p : CNF ℕ × Clause ℕ ↦ p.2.length)
        (encPair encCNF (encList encLit)) encUnary :=
      (length_list encLit).comp (snd _ _)
    exact hclen.decide_eq' (const 3)
  have hmid : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (⟨cubicSATGraph φ, 24 * φ.length⟩ : DominatingSetInstance))
      encCNF encDominatingSet := by
    have hm24 : ComputableInPolyTime (fun n : ℕ ↦ 24 * n) encUnary encUnary := by fun_prop
    have h24 : ComputableInPolyTime (fun φ : CNF ℕ ↦ 24 * φ.length) encCNF encNat :=
      unary_to_binary.comp (hm24.comp (length_list (encList encLit)))
    exact encDominatingSet_mk_polyTime computableInPolyTime_cubicSATGraph h24
  unfold toCubicDominatingSet
  exact ite hemp (const (⟨k4Graph, 1⟩ : DominatingSetInstance))
    (ite hex3 hmid (const (⟨k4Graph, 0⟩ : DominatingSetInstance)))

end CubicPolyTime

section CubicCorrectness

private lemma length_flatten_of_all_three {ψ : CNF ℕ} (h3 : ∀ c ∈ ψ, c.length = 3) :
    ψ.flatten.length = 3 * ψ.length := by
  induction ψ with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      h3 c List.mem_cons_self, ih fun d hd ↦ h3 d (List.mem_cons_of_mem c hd)]
    omega

private lemma flatten_getElem_three {ψ : CNF ℕ} (h3 : ∀ c ∈ ψ, c.length = 3)
    {i p : ℕ} (hi : i < ψ.length) (hp : p < 3) :
    have hlt : 3 * i + p < ψ.flatten.length := by
      rw [length_flatten_of_all_three h3]; omega
    have hcl : p < ψ[i].length := by rw [h3 ψ[i] (List.getElem_mem hi)]; exact hp
    ψ.flatten[3 * i + p] = ψ[i][p] := by
  induction ψ generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    have hc3 : c.length = 3 := h3 c List.mem_cons_self
    have hcs3 : ∀ d ∈ cs, d.length = 3 := fun d hd ↦ h3 d (List.mem_cons_of_mem c hd)
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
      exact List.getElem_append_left (by omega)
    | succ i' =>
      have hi' : i' < cs.length := by simp only [List.length_cons] at hi; omega
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [List.getElem_append_right (by omega)]
      have hidx : 3 * (i' + 1) + p - c.length = 3 * i' + p := by omega
      simpa only [hidx] using ih hcs3 hi'

private lemma occSlots_nodup (L : List (ℕ × Bool)) (v : ℕ) : (occSlots L v).Nodup :=
  List.nodup_range.filter _

private lemma mem_occSlots_iff {L : List (ℕ × Bool)} {v t : ℕ} :
    t ∈ occSlots L v ↔ t < L.length ∧ (L.getD t (0, false)).1 = v := by
  simp [occSlots]

private lemma length_occSlots_two_le {φ : CNF ℕ} {v s : ℕ}
    (hs : s ∈ occSlots (φ ++ φ).flatten v) :
    2 ≤ (occSlots (φ ++ φ).flatten v).length := by
  have hflat : (φ ++ φ).flatten = φ.flatten ++ φ.flatten := List.flatten_append
  set A := φ.flatten
  obtain ⟨hs_lt, hs_var⟩ := mem_occSlots_iff.mp hs
  rw [hflat] at hs_var
  rw [hflat, List.length_append] at hs_lt
  by_cases hleft : s < A.length
  · have ht_mem : s + A.length ∈ occSlots (φ ++ φ).flatten v := by
      rw [mem_occSlots_iff, hflat]
      have h1 : (A ++ A).getD s (0, false) = A[s] := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getElem_append_left hleft]
      have h2 : (A ++ A).getD (s + A.length) (0, false) = A[s] := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getElem_append_right (by omega)]
        simp
      rw [h2, ← h1]
      exact ⟨by rw [List.length_append]; omega, hs_var⟩
    have hne : s ≠ s + A.length := by omega
    have hsub : ({s, s + A.length} : Finset ℕ) ⊆ (occSlots (φ ++ φ).flatten v).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr ‹_›
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hne, List.toFinset_card_of_nodup (occSlots_nodup _ _)] at hcard
    exact hcard
  · let t := s - A.length
    have ht_lt : t < A.length := by omega
    have ht_mem : t ∈ occSlots (φ ++ φ).flatten v := by
      rw [mem_occSlots_iff, hflat]
      have h1 : (A ++ A).getD t (0, false) = A[t] := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getElem_append_left ht_lt]
      have h2 : (A ++ A).getD s (0, false) = A[t] := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getElem_append_right (by omega)]
      rw [h1, ← h2]
      exact ⟨by rw [List.length_append]; omega, hs_var⟩
    have hne : t ≠ s := by omega
    have hsub : ({t, s} : Finset ℕ) ⊆ (occSlots (φ ++ φ).flatten v).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr ‹_›
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hne, List.toFinset_card_of_nodup (occSlots_nodup _ _)] at hcard
    exact hcard

private lemma nextSlot_props {φ : CNF ℕ} {s : ℕ} (hs : s < (φ ++ φ).flatten.length) :
    let L := (φ ++ φ).flatten
    nextSlot L s < L.length ∧
      (L.getD (nextSlot L s) (0, false)).1 = (L.getD s (0, false)).1 ∧
      nextSlot L s ≠ s := by
  intro L
  set v := (L.getD s (0, false)).1
  set occ := occSlots L v
  have hs_occ : s ∈ occ := mem_occSlots_iff.mpr ⟨hs, rfl⟩
  have hlen2 : 2 ≤ occ.length := length_occSlots_two_le hs_occ
  have hnd : occ.Nodup := occSlots_nodup L v
  have hidx_lt : occ.idxOf s < occ.length := List.idxOf_lt_length_iff.mpr hs_occ
  have hget_idx : occ[occ.idxOf s] = s := List.getElem_idxOf hidx_lt
  have hnxt_eq : nextSlot L s =
      if occ.idxOf s + 1 < occ.length then occ.getD (occ.idxOf s + 1) 0 else occ.getD 0 0 := rfl
  have hnxt_mem : nextSlot L s ∈ occ := by
    rw [hnxt_eq]
    split_ifs with hlt
    · rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    · rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega)
  obtain ⟨hnxt_lt, hnxt_var⟩ := mem_occSlots_iff.mp hnxt_mem
  refine ⟨hnxt_lt, hnxt_var, ?_⟩
  rw [hnxt_eq]
  split_ifs with hlt
  · rw [List.getD_eq_getElem _ _ hlt]
    intro heq
    have := (List.Nodup.getElem_inj_iff hnd).mp (heq.trans hget_idx.symm)
    omega
  · rw [List.getD_eq_getElem _ _ (by omega)]
    intro heq
    have := (List.Nodup.getElem_inj_iff hnd).mp (heq.trans hget_idx.symm)
    omega

private lemma nextSlot_exists_unique_preimage {φ : CNF ℕ} {s' : ℕ}
    (hs' : s' < (φ ++ φ).flatten.length) :
    ∃! s, s < (φ ++ φ).flatten.length ∧ nextSlot (φ ++ φ).flatten s = s' := by
  set L := (φ ++ φ).flatten
  set v := (L.getD s' (0, false)).1
  set occ := occSlots L v
  have hs'_occ : s' ∈ occ := mem_occSlots_iff.mpr ⟨hs', rfl⟩
  have hlen2 : 2 ≤ occ.length := length_occSlots_two_le hs'_occ
  have hnd : occ.Nodup := occSlots_nodup L v
  set k := occ.idxOf s'
  have hk_lt : k < occ.length := List.idxOf_lt_length_iff.mpr hs'_occ
  have hk_eq : occ[k] = s' := List.getElem_idxOf hk_lt
  let i : ℕ := if k = 0 then occ.length - 1 else k - 1
  have hi_lt : i < occ.length := by dsimp [i]; split_ifs <;> omega
  let s₀ := occ[i]
  obtain ⟨hs₀_lt, hs₀_var⟩ := mem_occSlots_iff.mp (List.getElem_mem hi_lt)
  have hs₀_nxt : nextSlot L s₀ = s' := by
    dsimp only [nextSlot]
    rw [hs₀_var]
    change (if occ.idxOf s₀ + 1 < occ.length then occ.getD (occ.idxOf s₀ + 1) 0
      else occ.getD 0 0) = s'
    have hidx_eq : occ.idxOf s₀ = i := hnd.idxOf_getElem i hi_lt
    rw [hidx_eq]
    dsimp only [i]
    split_ifs with hk0 hlt hlt
    · omega
    · rw [List.getD_eq_getElem _ _ (by omega)]
      simpa [hk0] using hk_eq
    · rw [List.getD_eq_getElem _ _ hlt]
      have hik : k - 1 + 1 = k := by omega
      simpa [hik] using hk_eq
    · omega
  refine ⟨s₀, ⟨hs₀_lt, hs₀_nxt⟩, fun s ⟨hs_lt, hs_nxt⟩ ↦ ?_⟩
  have hprops := nextSlot_props hs_lt
  have hs_var : (L.getD s (0, false)).1 = v := by
    dsimp [v]
    rw [← hs_nxt]
    exact hprops.2.1.symm
  have hs_occ : s ∈ occ := mem_occSlots_iff.mpr ⟨hs_lt, hs_var⟩
  set j := occ.idxOf s
  have hj_lt : j < occ.length := List.idxOf_lt_length_iff.mpr hs_occ
  have hj_eq : occ[j] = s := List.getElem_idxOf hj_lt
  dsimp only [nextSlot] at hs_nxt
  rw [hs_var] at hs_nxt
  change (if j + 1 < occ.length then occ.getD (j + 1) 0 else occ.getD 0 0) = s' at hs_nxt
  rw [← hk_eq] at hs_nxt
  have hji : j = i := by
    split_ifs at hs_nxt with hlt
    · rw [List.getD_eq_getElem _ _ hlt] at hs_nxt
      have hjk := (List.Nodup.getElem_inj_iff hnd).mp hs_nxt
      dsimp [i]
      split_ifs with hk0 <;> omega
    · rw [List.getD_eq_getElem _ _ (by omega)] at hs_nxt
      have hjk := (List.Nodup.getElem_inj_iff hnd).mp hs_nxt
      dsimp [i]
      split_ifs with hk0 <;> omega
  exact hj_eq.symm.trans (by simp only [hji]; rfl)

private lemma nextSlot_cycle_const {φ : CNF ℕ} {v : ℕ} {P : ℕ → Prop}
    (hstep : ∀ s ∈ occSlots (φ ++ φ).flatten v, P s → P (nextSlot (φ ++ φ).flatten s))
    {s₀ : ℕ} (hs₀ : s₀ ∈ occSlots (φ ++ φ).flatten v) (hP₀ : P s₀) :
    ∀ s ∈ occSlots (φ ++ φ).flatten v, P s := by
  set L := (φ ++ φ).flatten
  set occ := occSlots L v
  have hlen2 : 2 ≤ occ.length := length_occSlots_two_le hs₀
  have hnd : occ.Nodup := occSlots_nodup L v
  have hnext_at : ∀ j (hj : j < occ.length),
      nextSlot L occ[j] = if j + 1 < occ.length then occ.getD (j + 1) 0 else occ.getD 0 0 := by
    intro j hj
    obtain ⟨_, hvar⟩ := mem_occSlots_iff.mp (List.getElem_mem hj)
    dsimp only [nextSlot]
    rw [hvar]
    change (if occ.idxOf occ[j] + 1 < occ.length then
      occ.getD (occ.idxOf occ[j] + 1) 0 else occ.getD 0 0) = _
    rw [hnd.idxOf_getElem j hj]
  have hfwd : ∀ a b (hb : b < occ.length) (hab : a ≤ b),
      P (occ[a]'(Nat.lt_of_le_of_lt hab hb)) → P occ[b] := by
    intro a b hb hab hPa
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => simpa using hPa
    | succ d ih =>
      have hd_lt : a + d < occ.length := by omega
      have hPd : P occ[a + d] := ih hd_lt (by omega) hPa
      have h1 := hstep occ[a + d] (List.getElem_mem hd_lt) hPd
      rw [hnext_at (a + d) hd_lt] at h1
      split_ifs at h1 with hlt
      · rw [List.getD_eq_getElem _ _ hlt] at h1
        have hidx : a + d + 1 = a + (d + 1) := by omega
        simpa only [hidx] using h1
      · omega
  set i₀ := occ.idxOf s₀
  have hi₀_lt : i₀ < occ.length := List.idxOf_lt_length_iff.mpr hs₀
  have hi₀_eq : occ[i₀] = s₀ := List.getElem_idxOf hi₀_lt
  have hlast : P (occ[occ.length - 1]'(by omega)) :=
    hfwd i₀ (occ.length - 1) (by omega) (by omega) (hi₀_eq.symm ▸ hP₀)
  have h0 : P (occ[0]'(by omega)) := by
    have h1 := hstep (occ[occ.length - 1]'(by omega)) (List.getElem_mem (by omega)) hlast
    rw [hnext_at (occ.length - 1) (by omega)] at h1
    split_ifs at h1 with hlt
    · omega
    · rw [List.getD_eq_getElem _ _ (by omega)] at h1
      exact h1
  intro s hs
  set j := occ.idxOf s
  have hj_lt : j < occ.length := List.idxOf_lt_length_iff.mpr hs
  have hj_eq : occ[j] = s := List.getElem_idxOf hj_lt
  rw [← hj_eq]
  exact hfwd 0 j hj_lt (Nat.zero_le j) h0

private lemma mem_cubicSATGraph_vertices {φ : CNF ℕ} {w : ℕ} :
    w ∈ (cubicSATGraph φ).vertices ↔
      (∃ s < 3 * (φ ++ φ).length, ∃ u < 13, w = gadVert s u) ∨
      (∃ i < (φ ++ φ).length, w = ternVert i) ∨
      (∃ s < 3 * (φ ++ φ).length, w = binVert s) := by
  simp only [cubicSATGraph, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    or_assoc]
  exact ⟨by rintro (⟨s, hs, u, hu, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨s, hs, rfl⟩);
            exacts [Or.inl ⟨s, hs, u, hu, rfl⟩, Or.inr (Or.inl ⟨i, hi, rfl⟩),
              Or.inr (Or.inr ⟨s, hs, rfl⟩)],
         by rintro (⟨s, hs, u, hu, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨s, hs, rfl⟩);
            exacts [Or.inl ⟨s, hs, u, hu, rfl⟩, Or.inr (Or.inl ⟨i, hi, rfl⟩),
              Or.inr (Or.inr ⟨s, hs, rfl⟩)]⟩

private lemma mem_cubicSATGraph_edges {φ : CNF ℕ} {x y : ℕ} :
    (x, y) ∈ (cubicSATGraph φ).edges ↔
      (∃ s < 3 * (φ ++ φ).length, ∃ e ∈ h13Edges, x = gadVert s e.1 ∧ y = gadVert s e.2) ∨
      (∃ i < (φ ++ φ).length, ∃ p ∈ ([0, 1, 2] : List ℕ),
        x = ternVert i ∧ y = gadVert (3 * i + p) 0) ∨
      (∃ s < 3 * (φ ++ φ).length,
        (x = binVert s ∧ y = gadVert s (negPort (φ ++ φ).flatten s)) ∨
        (x = binVert s ∧
          y = gadVert (nextSlot (φ ++ φ).flatten s)
            (posBinPort (φ ++ φ).flatten (nextSlot (φ ++ φ).flatten s)))) ∨
      (∃ t < 3 * φ.length, x = binVert (2 * t) ∧ y = binVert (2 * t + 1)) := by
  simp only [cubicSATGraph, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, or_assoc]
  exact ⟨by rintro (⟨s, hs, e, he, rfl, rfl⟩ | ⟨i, hi, p, hp, rfl, rfl⟩ |
              ⟨s, hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨t, ht, rfl, rfl⟩)
            · exact Or.inl ⟨s, hs, e, he, rfl, rfl⟩
            · exact Or.inr (Or.inl ⟨i, hi, p, hp, rfl, rfl⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨s, hs, Or.inl ⟨rfl, rfl⟩⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨s, hs, Or.inr ⟨rfl, rfl⟩⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨t, ht, rfl, rfl⟩)),
         by rintro (⟨s, hs, e, he, rfl, rfl⟩ | ⟨i, hi, p, hp, rfl, rfl⟩ |
              ⟨s, hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨t, ht, rfl, rfl⟩)
            · exact Or.inl ⟨s, hs, e, he, rfl, rfl⟩
            · exact Or.inr (Or.inl ⟨i, hi, p, hp, rfl, rfl⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨s, hs, Or.inl ⟨rfl, rfl⟩⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨s, hs, Or.inr ⟨rfl, rfl⟩⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨t, ht, rfl, rfl⟩))⟩

private lemma h13Edges_bounds {e : ℕ × ℕ} (he : e ∈ h13Edges) :
    e.1 < 13 ∧ e.2 < 13 ∧ e.1 ≠ e.2 := by
  simp only [h13Edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma gadVert_inj {s₁ u₁ s₂ u₂ : ℕ} (hu₁ : u₁ < 16) (hu₂ : u₂ < 16)
    (h : gadVert s₁ u₁ = gadVert s₂ u₂) : s₁ = s₂ ∧ u₁ = u₂ := by
  dsimp [gadVert] at h; omega

private lemma negPort_lt (L : List (ℕ × Bool)) (s : ℕ) : negPort L s < 16 := by
  unfold negPort; split_ifs <;> omega

private lemma posBinPort_lt (L : List (ℕ × Bool)) (s : ℕ) : posBinPort L s < 16 := by
  unfold posBinPort; split_ifs <;> omega

private lemma negPort_one_two (L : List (ℕ × Bool)) (s : ℕ) :
    negPort L s = 1 ∨ negPort L s = 2 := by
  unfold negPort; split_ifs <;> omega

private lemma posBinPort_one_two (L : List (ℕ × Bool)) (s : ℕ) :
    posBinPort L s = 1 ∨ posBinPort L s = 2 := by
  unfold posBinPort; split_ifs <;> omega

/-- Complete characterization of neighbors of a gadget vertex `gadVert s u` (`u < 13`). -/
private lemma cubicSATGraph_adj_gad_iff {φ : CNF ℕ} {s u z : ℕ}
    (hs : s < 3 * (φ ++ φ).length) (hu : u < 13) :
    (cubicSATGraph φ).toSimpleGraph.Adj (gadVert s u) z ↔
      (∃ v, ∃ hv : v < 13, h13Adj ⟨u, hu⟩ ⟨v, hv⟩ = true ∧ z = gadVert s v) ∨
      (u = 0 ∧ z = ternVert (s / 3)) ∨
      (u = negPort (φ ++ φ).flatten s ∧ z = binVert s) ∨
      (∃ sp < 3 * (φ ++ φ).length,
        nextSlot (φ ++ φ).flatten sp = s ∧
          u = posBinPort (φ ++ φ).flatten s ∧ z = binVert sp) := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, h | h⟩ <;> rw [mem_cubicSATGraph_edges] at h
    · rcases h with ⟨s', _, e, he, hx, hy⟩ | ⟨_, _, _, _, hx, _⟩ |
        ⟨_, _, ⟨hx, _⟩ | ⟨hx, _⟩⟩ | ⟨_, _, hx, _⟩
      · obtain ⟨he1, he2, _⟩ := h13Edges_bounds he
        obtain ⟨rfl, rfl⟩ := gadVert_inj (by omega) (by omega) hx
        refine Or.inl ⟨e.2, he2, ?_, hy⟩
        simp only [h13Adj, List.any_eq_true, decide_eq_true_eq]
        exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
      · dsimp [gadVert, ternVert] at hx; omega
      · dsimp [gadVert, binVert] at hx; omega
      · dsimp [gadVert, binVert] at hx; omega
      · dsimp [gadVert, binVert] at hx; omega
    · rcases h with ⟨s', _, e, he, hy, hx⟩ | ⟨i, _, p, hp, hy, hx⟩ |
        ⟨sp, hsp, ⟨hy, hx⟩ | ⟨hy, hx⟩⟩ | ⟨_, _, _, hx⟩
      · obtain ⟨he1, he2, _⟩ := h13Edges_bounds he
        obtain ⟨rfl, rfl⟩ := gadVert_inj (by omega) (by omega) hx
        refine Or.inl ⟨e.1, he1, ?_, hy⟩
        simp only [h13Adj, List.any_eq_true, decide_eq_true_eq]
        exact ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        obtain ⟨hs_eq, hu_eq⟩ := gadVert_inj (by omega) (by omega) hx
        have hi_eq : i = s / 3 := by omega
        exact Or.inr (Or.inl ⟨hu_eq, hy.trans (congrArg ternVert hi_eq)⟩)
      · obtain ⟨rfl, hu_eq⟩ := gadVert_inj (by omega) (negPort_lt _ _) hx
        exact Or.inr (Or.inr (Or.inl ⟨hu_eq, hy⟩))
      · obtain ⟨hnxt, hu_eq⟩ := gadVert_inj (by omega) (posBinPort_lt _ _) hx
        exact Or.inr (Or.inr (Or.inr ⟨sp, hsp, hnxt.symm, hnxt ▸ hu_eq, hy⟩))
      · dsimp [gadVert, binVert] at hx; omega
  · rintro (⟨v, hv, hadj, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨sp, hsp, hnxt, rfl, rfl⟩)
    · simp only [h13Adj, List.any_eq_true, decide_eq_true_eq] at hadj
      obtain ⟨e, he, ⟨he1, he2⟩ | ⟨he1, he2⟩⟩ := hadj
      · obtain ⟨_, _, hne⟩ := h13Edges_bounds he
        exact ⟨by dsimp [gadVert]; omega,
          Or.inl (mem_cubicSATGraph_edges.mpr (Or.inl ⟨s, hs, e, he, by simp [he1],
            by simp [he2]⟩))⟩
      · obtain ⟨_, _, hne⟩ := h13Edges_bounds he
        exact ⟨by dsimp [gadVert]; omega,
          Or.inr (mem_cubicSATGraph_edges.mpr (Or.inl ⟨s, hs, e, he, by simp [he1],
            by simp [he2]⟩))⟩
    · have hi : s / 3 < (φ ++ φ).length := by omega
      have hp : s % 3 ∈ ([0, 1, 2] : List ℕ) := by simp; omega
      exact ⟨by dsimp [gadVert, ternVert]; omega,
        Or.inr (mem_cubicSATGraph_edges.mpr (Or.inr (Or.inl ⟨s / 3, hi, s % 3, hp, rfl,
          by congr 1; omega⟩)))⟩
    · exact ⟨by dsimp [gadVert, binVert]; omega,
        Or.inr (mem_cubicSATGraph_edges.mpr (Or.inr (Or.inr (Or.inl ⟨s, hs,
          Or.inl ⟨rfl, rfl⟩⟩))))⟩
    · exact ⟨by dsimp [gadVert, binVert]; omega,
        Or.inr (mem_cubicSATGraph_edges.mpr (Or.inr (Or.inr (Or.inl ⟨sp, hsp,
          Or.inr ⟨rfl, by rw [hnxt]⟩⟩))))⟩

private lemma cubicSATGraph_adj_gad_gad {φ : CNF ℕ} {s₁ u₁ s₂ u₂ : ℕ}
    (hu₁ : u₁ < 13) (hu₂ : u₂ < 13) (hs₁ : s₁ < 3 * (φ ++ φ).length) :
    (cubicSATGraph φ).toSimpleGraph.Adj (gadVert s₁ u₁) (gadVert s₂ u₂) ↔
      s₁ = s₂ ∧ h13Adj ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ = true := by
  rw [cubicSATGraph_adj_gad_iff hs₁ hu₁]
  constructor
  · rintro (⟨v, hv, hadj, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, _, _, _, heq⟩)
    · obtain ⟨rfl, rfl⟩ := gadVert_inj (by omega) (by omega) heq
      exact ⟨rfl, hadj⟩
    · dsimp [gadVert, ternVert] at heq; omega
    · dsimp [gadVert, binVert] at heq; omega
    · dsimp [gadVert, binVert] at heq; omega
  · rintro ⟨rfl, hadj⟩
    exact Or.inl ⟨u₂, hu₂, hadj, rfl⟩

private lemma cubicSATGraph_adj_tern_iff {φ : CNF ℕ} {i z : ℕ} (hi : i < (φ ++ φ).length) :
    (cubicSATGraph φ).toSimpleGraph.Adj (ternVert i) z ↔
      ∃ p < 3, z = gadVert (3 * i + p) 0 := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, h | h⟩ <;> rw [mem_cubicSATGraph_edges] at h
    · rcases h with ⟨_, _, _, _, hx, _⟩ | ⟨i', _, p, hp, hx, hy⟩ |
        ⟨_, _, ⟨hx, _⟩ | ⟨hx, _⟩⟩ | ⟨_, _, hx, _⟩
      · dsimp [ternVert, gadVert] at hx; omega
      · have hi_eq : i' = i := by dsimp [ternVert] at hx; omega
        subst i'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        exact ⟨p, by rcases hp with rfl | rfl | rfl <;> omega, hy⟩
      · dsimp [ternVert, binVert] at hx; omega
      · dsimp [ternVert, binVert] at hx; omega
      · dsimp [ternVert, binVert] at hx; omega
    · rcases h with ⟨_, _, _, _, _, hx⟩ | ⟨_, _, _, _, _, hx⟩ |
        ⟨_, _, ⟨_, hx⟩ | ⟨_, hx⟩⟩ | ⟨_, _, _, hx⟩ <;>
        dsimp [ternVert, gadVert, binVert] at hx <;> omega
  · rintro ⟨p, hp, rfl⟩
    have hp_mem : p ∈ ([0, 1, 2] : List ℕ) := by simp; omega
    exact ⟨by dsimp [ternVert, gadVert]; omega,
      Or.inl (mem_cubicSATGraph_edges.mpr (Or.inr (Or.inl ⟨i, hi, p, hp_mem, rfl, rfl⟩)))⟩

private lemma cubicSATGraph_adj_bin_iff {φ : CNF ℕ} {s z : ℕ} (hs : s < 3 * (φ ++ φ).length) :
    (cubicSATGraph φ).toSimpleGraph.Adj (binVert s) z ↔
      z = gadVert s (negPort (φ ++ φ).flatten s) ∨
      z = gadVert (nextSlot (φ ++ φ).flatten s)
        (posBinPort (φ ++ φ).flatten (nextSlot (φ ++ φ).flatten s)) ∨
      z = binVert (if s % 2 = 0 then s + 1 else s - 1) := by
  have hlen : (φ ++ φ).length = 2 * φ.length := by rw [List.length_append]; omega
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, h | h⟩ <;> rw [mem_cubicSATGraph_edges] at h
    · rcases h with ⟨_, _, _, _, hx, _⟩ | ⟨_, _, _, _, hx, _⟩ |
        ⟨s', _, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩ | ⟨t, _, hx, hy⟩
      · dsimp [binVert, gadVert] at hx; omega
      · dsimp [binVert, ternVert] at hx; omega
      · have hs_eq : s' = s := by dsimp [binVert] at hx; omega
        subst s'; exact Or.inl hy
      · have hs_eq : s' = s := by dsimp [binVert] at hx; omega
        subst s'; exact Or.inr (Or.inl hy)
      · have hs_eq : s = 2 * t := by dsimp [binVert] at hx; omega
        exact Or.inr (Or.inr (by simp [hs_eq, hy]))
    · rcases h with ⟨_, _, _, _, _, hx⟩ | ⟨_, _, _, _, _, hx⟩ |
        ⟨_, _, ⟨_, hx⟩ | ⟨_, hx⟩⟩ | ⟨t, _, hy, hx⟩
      · dsimp [binVert, gadVert] at hx; omega
      · dsimp [binVert, gadVert] at hx; omega
      · dsimp [binVert, gadVert] at hx; omega
      · dsimp [binVert, gadVert] at hx; omega
      · have hs_eq : s = 2 * t + 1 := by dsimp [binVert] at hx; omega
        exact Or.inr (Or.inr (by simp [hs_eq, hy]))
  · rintro (rfl | rfl | rfl)
    · exact ⟨by dsimp [binVert, gadVert]; omega,
        Or.inl (mem_cubicSATGraph_edges.mpr (Or.inr (Or.inr (Or.inl ⟨s, hs,
          Or.inl ⟨rfl, rfl⟩⟩))))⟩
    · exact ⟨by dsimp [binVert, gadVert]; omega,
        Or.inl (mem_cubicSATGraph_edges.mpr (Or.inr (Or.inr (Or.inl ⟨s, hs,
          Or.inr ⟨rfl, rfl⟩⟩))))⟩
    · let t := s / 2
      have ht : t < 3 * φ.length := by omega
      by_cases hev : s % 2 = 0
      · have hs2 : s = 2 * t := by omega
        exact ⟨by dsimp [binVert]; simp [hev],
          Or.inl (mem_cubicSATGraph_edges.mpr
            (Or.inr (Or.inr (Or.inr ⟨t, ht, by simp [hs2], by simp [hs2]⟩))))⟩
      · have hs2 : s = 2 * t + 1 := by omega
        exact ⟨by dsimp [binVert]; simp [hev]; omega,
          Or.inr (mem_cubicSATGraph_edges.mpr
            (Or.inr (Or.inr (Or.inr ⟨t, ht, by simp [hs2], by simp [hs2]⟩))))⟩

private lemma cubicSATGraph_isCubic {φ : CNF ℕ} (_hne : φ ≠ []) (h3 : ∀ c ∈ φ, c.length = 3) :
    (cubicSATGraph φ).induced.IsRegularOfDegree 3 := by
  classical
  have hψ3 : ∀ c ∈ φ ++ φ, c.length = 3 := fun c hc ↦ by
    rcases List.mem_append.mp hc with h | h <;> exact h3 c h
  have hL_len : (φ ++ φ).flatten.length = 3 * (φ ++ φ).length := length_flatten_of_all_three hψ3
  have hlen2 : (φ ++ φ).length = 2 * φ.length := by rw [List.length_append]; omega
  rintro ⟨w, hw⟩
  rw [← (cubicSATGraph φ).induced.card_neighborFinset_eq_degree,
    ← Finset.card_map (Function.Embedding.subtype _)]
  have hN_eq (S : Finset ℕ)
      (hS : ∀ z, z ∈ S ↔
        z ∈ (cubicSATGraph φ).vertices ∧ (cubicSATGraph φ).toSimpleGraph.Adj w z) :
      ((cubicSATGraph φ).induced.neighborFinset ⟨w, hw⟩).map (Function.Embedding.subtype _) =
        S := by
    ext z
    simp only [Finset.mem_map, Function.Embedding.coe_subtype,
      _root_.SimpleGraph.mem_neighborFinset, Graph.induced_adj, Subtype.exists, hS]
    exact ⟨by rintro ⟨z', hz', hadj, rfl⟩; exact ⟨hz', hadj⟩,
      fun ⟨hz, hadj⟩ ↦ ⟨z, hz, hadj, rfl⟩⟩
  rcases mem_cubicSATGraph_vertices.mp hw with ⟨s, hs, u, hu, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨s, hs, rfl⟩
  · -- Gadget vertex `gadVert s u`
    let intN : Finset ℕ := ((List.finRange 13).filter fun v ↦ h13Adj ⟨u, hu⟩ v).toFinset.image
      fun v ↦ gadVert s v.1
    have hint_card : intN.card = if u < 3 then 2 else 3 := by
      rw [Finset.card_image_of_injective _ fun a b h ↦ Fin.ext
        (gadVert_inj (by omega) (by omega) h).2,
        List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter _)]
      exact h13_internal_deg ⟨u, hu⟩
    by_cases hu3 : u < 3
    · have hu_cases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hu_cases with rfl | hu12
      · -- Port `0`
        have hi₀ : s / 3 < (φ ++ φ).length := by omega
        have hext_notMem : ternVert (s / 3) ∉ intN := by
          simp only [intN, Finset.mem_image]
          rintro ⟨v, _, heq⟩; dsimp [gadVert, ternVert] at heq; omega
        rw [hN_eq (insert (ternVert (s / 3)) intN),
          Finset.card_insert_of_notMem hext_notMem, hint_card]
        · simp
        · intro z
          rw [cubicSATGraph_adj_gad_iff hs hu]
          simp only [Finset.mem_insert, intN, Finset.mem_image, List.mem_toFinset, List.mem_filter,
            List.mem_finRange, true_and]
          constructor
          · rintro (rfl | ⟨v, hv, rfl⟩)
            · exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inr (Or.inl ⟨s / 3, hi₀, rfl⟩)),
                Or.inr (Or.inl rfl)⟩
            · exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inl ⟨s, hs, v.1, v.2, rfl⟩),
                Or.inl ⟨v.1, v.2, hv, rfl⟩⟩
          · rintro ⟨_, (⟨v, hv, hadj, rfl⟩ | rfl | ⟨hneg, _⟩ | ⟨_, _, _, hpos, _⟩)⟩
            · exact Or.inr ⟨⟨v, hv⟩, hadj, rfl⟩
            · exact Or.inl rfl
            · rcases negPort_one_two (φ ++ φ).flatten s with h | h <;> omega
            · rcases posBinPort_one_two (φ ++ φ).flatten s with h | h <;> omega
      · -- Port `u ∈ {1, 2}`: unified handling of both binary-clause ports!
        obtain ⟨sp, ⟨hsp_lt, hsp_nxt⟩, hsp_uniq⟩ :=
          nextSlot_exists_unique_preimage (hL_len ▸ hs)
        have hsp3 : sp < 3 * (φ ++ φ).length := hL_len ▸ hsp_lt
        let useNeg : Bool := decide (u = negPort (φ ++ φ).flatten s)
        have hport_dich : u = negPort (φ ++ φ).flatten s ↔ u ≠ posBinPort (φ ++ φ).flatten s := by
          unfold negPort posBinPort
          rcases hu12 with rfl | rfl <;> split_ifs <;> omega
        let extB := if useNeg then binVert s else binVert sp
        have hext_notMem : extB ∉ intN := by
          simp only [intN, Finset.mem_image]
          rintro ⟨v, _, heq⟩; dsimp [extB, gadVert, binVert] at heq; split_ifs at heq <;> omega
        rw [hN_eq (insert extB intN), Finset.card_insert_of_notMem hext_notMem, hint_card]
        · simp [hu3]
        · intro z
          rw [cubicSATGraph_adj_gad_iff hs hu]
          simp only [Finset.mem_insert, intN, Finset.mem_image, List.mem_toFinset, List.mem_filter,
            List.mem_finRange, true_and]
          constructor
          · rintro (rfl | ⟨v, hv, rfl⟩)
            · by_cases hneg_u : u = negPort (φ ++ φ).flatten s
              · have hext_eq : extB = binVert s := by
                  have huse : useNeg = true := decide_eq_true hneg_u
                  simp [extB, huse]
                rw [hext_eq]
                exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩)),
                  Or.inr (Or.inr (Or.inl ⟨hneg_u, rfl⟩))⟩
              · have hpos_u : u = posBinPort (φ ++ φ).flatten s :=
                  Classical.not_not.mp (hport_dich.not.mp hneg_u)
                have hext_eq : extB = binVert sp := by
                  have huse : useNeg = false := decide_eq_false hneg_u
                  simp [extB, huse]
                rw [hext_eq]
                exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inr (Or.inr ⟨sp, hsp3, rfl⟩)),
                  Or.inr (Or.inr (Or.inr ⟨sp, hsp3, hsp_nxt, hpos_u, rfl⟩))⟩
            · exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inl ⟨s, hs, v.1, v.2, rfl⟩),
                Or.inl ⟨v.1, v.2, hv, rfl⟩⟩
          · rintro ⟨_, (⟨v, hv, hadj, rfl⟩ | ⟨h0, _⟩ | ⟨hneg_u, rfl⟩ | ⟨sp', hsp', hnxt', hpos_u,
            rfl⟩)⟩
            · exact Or.inr ⟨⟨v, hv⟩, hadj, rfl⟩
            · rcases hu12 with rfl | rfl <;> omega
            · have huse : useNeg = true := decide_eq_true hneg_u
              exact Or.inl (by simp [extB, huse])
            · have hnot_neg : u ≠ negPort (φ ++ φ).flatten s :=
                fun h ↦ (hport_dich.mp h) hpos_u
              have huse : useNeg = false := decide_eq_false hnot_neg
              have hsp_eq : sp' = sp := hsp_uniq sp' ⟨hL_len.symm ▸ hsp', hnxt'⟩
              exact Or.inl (by simp [extB, huse, hsp_eq])
    · -- Internal vertex `3 ≤ u < 13`
      rw [hN_eq intN, hint_card]
      · simp [hu3]
      · intro z
        rw [cubicSATGraph_adj_gad_iff hs hu]
        simp only [intN, Finset.mem_image, List.mem_toFinset, List.mem_filter,
          List.mem_finRange, true_and]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inl ⟨s, hs, v.1, v.2, rfl⟩),
            Or.inl ⟨v.1, v.2, hv, rfl⟩⟩
        · rintro ⟨_, (⟨v, hv, hadj, rfl⟩ | ⟨h0, _⟩ | ⟨hneg, _⟩ | ⟨_, _, _, hpos, _⟩)⟩
          · exact ⟨⟨v, hv⟩, hadj, rfl⟩
          · omega
          · rcases negPort_one_two (φ ++ φ).flatten s with h | h <;> omega
          · rcases posBinPort_one_two (φ ++ φ).flatten s with h | h <;> omega
  · -- Ternary clause vertex `ternVert i`
    let S : Finset ℕ := {gadVert (3 * i) 0, gadVert (3 * i + 1) 0, gadVert (3 * i + 2) 0}
    rw [hN_eq S]
    · have h01 : gadVert (3 * i) 0 ≠ gadVert (3 * i + 1) 0 := by dsimp [gadVert]; omega
      have h02 : gadVert (3 * i) 0 ≠ gadVert (3 * i + 2) 0 := by dsimp [gadVert]; omega
      have h12 : gadVert (3 * i + 1) 0 ≠ gadVert (3 * i + 2) 0 := by dsimp [gadVert]; omega
      simp [S, h01, h02, h12]
    · intro z
      rw [cubicSATGraph_adj_tern_iff hi]
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inl ⟨3 * i, by omega, 0, by omega, rfl⟩),
            0, by omega, by simp⟩
        · exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inl ⟨3 * i + 1, by omega, 0, by omega, rfl⟩),
            1, by omega, rfl⟩
        · exact ⟨mem_cubicSATGraph_vertices.mpr (Or.inl ⟨3 * i + 2, by omega, 0, by omega, rfl⟩),
            2, by omega, rfl⟩
      · rintro ⟨_, p, hp, rfl⟩
        have hp_cases : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases hp_cases with rfl | rfl | rfl <;> simp
  · -- Binary clause vertex `binVert s`
    have hprops := nextSlot_props (hL_len ▸ hs)
    let g₁ := gadVert s (negPort (φ ++ φ).flatten s)
    let g₂ := gadVert (nextSlot (φ ++ φ).flatten s)
      (posBinPort (φ ++ φ).flatten (nextSlot (φ ++ φ).flatten s))
    let b₂ := binVert (if s % 2 = 0 then s + 1 else s - 1)
    rw [hN_eq {g₁, g₂, b₂}]
    · have h12 : g₁ ≠ g₂ := fun h ↦
        hprops.2.2 (gadVert_inj (negPort_lt _ _) (posBinPort_lt _ _) h).1.symm
      have h13 : g₁ ≠ b₂ := by dsimp [g₁, b₂, gadVert, binVert]; omega
      have h23 : g₂ ≠ b₂ := by dsimp [g₂, b₂, gadVert, binVert]; omega
      simp [h12, h13, h23]
    · intro z
      rw [cubicSATGraph_adj_bin_iff hs]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨mem_cubicSATGraph_vertices.mpr
            (Or.inl ⟨s, hs, negPort (φ ++ φ).flatten s,
              by rcases negPort_one_two (φ ++ φ).flatten s with h | h <;> omega, rfl⟩),
            Or.inl rfl⟩
        · exact ⟨mem_cubicSATGraph_vertices.mpr
            (Or.inl ⟨nextSlot (φ ++ φ).flatten s, hL_len ▸ hprops.1,
              posBinPort (φ ++ φ).flatten (nextSlot (φ ++ φ).flatten s),
              by rcases posBinPort_one_two (φ ++ φ).flatten (nextSlot (φ ++ φ).flatten s) with
                h | h <;> omega, rfl⟩),
            Or.inr (Or.inl rfl)⟩
        · refine ⟨mem_cubicSATGraph_vertices.mpr (Or.inr (Or.inr ⟨
            if s % 2 = 0 then s + 1 else s - 1, ?_, rfl⟩)), Or.inr (Or.inr rfl)⟩
          split_ifs <;> omega
      · rintro ⟨_, h⟩
        exact h

private lemma cubicSATGraph_iff_satisfiable {φ : CNF ℕ} (_hne : φ ≠ [])
    (h3 : ∀ c ∈ φ, c.length = 3) :
    (⟨cubicSATGraph φ, 24 * φ.length⟩ : DominatingSetInstance) ∈ DominatingSet ↔
      φ.Satisfiable := by
  classical
  have hψ3 : ∀ c ∈ φ ++ φ, c.length = 3 := fun c hc ↦ by
    rcases List.mem_append.mp hc with h | h <;> exact h3 c h
  set ψ := φ ++ φ
  set M := ψ.length
  set L := ψ.flatten
  have hM_eq : M = 2 * φ.length := by dsimp [M, ψ]; rw [List.length_append]; omega
  have hL_len : L.length = 3 * M := length_flatten_of_all_three hψ3
  have h24 : 24 * φ.length = 12 * M := by omega
  rw [h24, mem_DominatingSet_iff]
  constructor
  · rintro ⟨D, _hDV, hDdom, hDcard⟩
    let Dgad (s : ℕ) : Finset (Fin 13) :=
      Finset.univ.filter fun u ↦ gadVert s u.1 ∈ D
    have hDgad_dom (s : ℕ) (hs : s < 3 * M) : h13DomInternal (Dgad s) := by
      intro u hu3
      have hvV : gadVert s u.1 ∈ (cubicSATGraph φ).vertices :=
        mem_cubicSATGraph_vertices.mpr (Or.inl ⟨s, hs, u.1, u.2, rfl⟩)
      rcases hDdom _ hvV with hin | ⟨z, hzD, hadj⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hin⟩, by simp [h13Closed]⟩
      · rcases (cubicSATGraph_adj_gad_iff hs u.2).mp hadj with
          ⟨v, hv, hadj', rfl⟩ | ⟨h0, _⟩ | ⟨hneg, _⟩ | ⟨_, _, _, hpos, _⟩
        · exact ⟨⟨v, hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzD⟩,
            by simp [h13Closed, hadj']⟩
        · omega
        · rcases negPort_one_two (φ ++ φ).flatten s with h | h <;> omega
        · rcases posBinPort_one_two (φ ++ φ).flatten s with h | h <;> omega
    have hDgad_ge (s : ℕ) (hs : s < 3 * M) : 4 ≤ (Dgad s).card :=
      h13_four_le_card_of_domInternal (hDgad_dom s hs)
    let allGad : Finset ℕ := (Finset.range (3 * M)).biUnion fun s ↦
      (Dgad s).image fun u ↦ gadVert s u.1
    have hallGad_sub : allGad ⊆ D := by
      intro z hz
      simp only [allGad, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hz
      obtain ⟨s, _, u, hu, rfl⟩ := hz
      exact (Finset.mem_filter.mp hu).2
    have hallGad_card : allGad.card = ∑ s ∈ Finset.range (3 * M), (Dgad s).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun s _ ↦ Finset.card_image_of_injective _ fun a b h ↦
          Fin.ext (gadVert_inj (by omega) (by omega) h).2
      · intro s₁ _ s₂ _ hne
        refine Finset.disjoint_left.mpr fun z hz₁ hz₂ ↦ hne ?_
        simp only [Finset.mem_image] at hz₁ hz₂
        obtain ⟨u₁, _, rfl⟩ := hz₁
        obtain ⟨u₂, _, heq⟩ := hz₂
        exact (gadVert_inj (by omega) (by omega) heq.symm).1
    have hsum_ge : 12 * M ≤ ∑ s ∈ Finset.range (3 * M), (Dgad s).card := by
      calc 12 * M = ∑ _s ∈ Finset.range (3 * M), 4 := by simp; omega
        _ ≤ ∑ s ∈ Finset.range (3 * M), (Dgad s).card :=
            Finset.sum_le_sum fun s hs ↦ hDgad_ge s (Finset.mem_range.mp hs)
    have hallGad_eq : allGad = D :=
      Finset.eq_of_subset_of_card_le hallGad_sub (by omega)
    have hDgad_eq4 (s : ℕ) (hs : s < 3 * M) : (Dgad s).card = 4 := by
      by_contra hne4
      have hgt : 4 < (Dgad s).card := lt_of_le_of_ne (hDgad_ge s hs) (Ne.symm hne4)
      have hsum_gt : ∑ _t ∈ Finset.range (3 * M), 4 <
          ∑ t ∈ Finset.range (3 * M), (Dgad t).card :=
        Finset.sum_lt_sum (fun t ht ↦ hDgad_ge t (Finset.mem_range.mp ht))
          ⟨s, Finset.mem_range.mpr hs, hgt⟩
      have : allGad.card = 12 * M := by rw [hallGad_eq, hDcard]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum_gt
      omega
    have hnot_clause_in_D (z : ℕ) (hz : z ∈ D) : ∃ s < 3 * M, ∃ u < 13, z = gadVert s u := by
      rw [← hallGad_eq] at hz
      simp only [allGad, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hz
      obtain ⟨s, hs, u, _, rfl⟩ := hz
      exact ⟨s, hs, u.1, u.2, rfl⟩
    let posSide (s : ℕ) : Prop :=
      if (L.getD s (0, false)).2 then (0 : Fin 13) ∈ Dgad s ∨ (1 : Fin 13) ∈ Dgad s
      else (2 : Fin 13) ∈ Dgad s
    let negSide (s : ℕ) : Prop :=
      if (L.getD s (0, false)).2 then (2 : Fin 13) ∈ Dgad s
      else (0 : Fin 13) ∈ Dgad s ∨ (1 : Fin 13) ∈ Dgad s
    have hnot_both (s : ℕ) (hs : s < 3 * M) : ¬ (posSide s ∧ negSide s) := by
      rintro ⟨hp, hn⟩
      dsimp only [posSide, negSide] at hp hn
      split_ifs at hp hn
      · exact h13_port_exclusion (hDgad_dom s hs) (hDgad_eq4 s hs).le hp hn
      · exact h13_port_exclusion (hDgad_dom s hs) (hDgad_eq4 s hs).le hn hp
    have hstep_pos (s : ℕ) (hs : s < 3 * M) (hp : posSide s) : posSide (nextSlot L s) := by
      have hbV : binVert s ∈ (cubicSATGraph φ).vertices :=
        mem_cubicSATGraph_vertices.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩))
      rcases hDdom _ hbV with hbD | ⟨z, hzD, hadj⟩
      · obtain ⟨_, _, _, _, hbad⟩ := hnot_clause_in_D _ hbD
        dsimp [binVert, gadVert] at hbad; omega
      · rcases (cubicSATGraph_adj_bin_iff hs).mp hadj with rfl | rfl | rfl
        · have hneg_s : negSide s := by
            dsimp only [negSide, Dgad]
            unfold negPort at hzD
            change gadVert s (if (L.getD s (0, false)).2 then 2 else 1) ∈ D at hzD
            split_ifs at hzD ⊢
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ (2 : Fin 13), hzD⟩
            · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ (1 : Fin 13), hzD⟩)
          exact (hnot_both s hs ⟨hp, hneg_s⟩).elim
        · set s' := nextSlot L s
          dsimp only [posSide, Dgad]
          unfold posBinPort at hzD
          change gadVert s' (if (L.getD s' (0, false)).2 then 1 else 2) ∈ D at hzD
          split_ifs at hzD ⊢
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ (1 : Fin 13), hzD⟩)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ (2 : Fin 13), hzD⟩
        · obtain ⟨_, _, _, _, hbad⟩ := hnot_clause_in_D _ hzD
          dsimp [binVert, gadVert] at hbad; omega
    let σ : ℕ → Bool := fun v ↦ decide (∃ s ∈ occSlots L v, posSide s)
    refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc ↦ ?_⟩
    obtain ⟨i, hi_φ, rfl⟩ := List.getElem_of_mem hc
    have hi_M : i < M := by omega
    have hψ_i : ψ[i] = φ[i] := List.getElem_append_left hi_φ
    have htV : ternVert i ∈ (cubicSATGraph φ).vertices :=
      mem_cubicSATGraph_vertices.mpr (Or.inr (Or.inl ⟨i, hi_M, rfl⟩))
    rcases hDdom _ htV with htD | ⟨z, hzD, hadj⟩
    · obtain ⟨_, _, _, _, hbad⟩ := hnot_clause_in_D _ htD
      dsimp [ternVert, gadVert] at hbad; omega
    · obtain ⟨p, hp_lt, rfl⟩ := (cubicSATGraph_adj_tern_iff hi_M).mp hadj
      set s := 3 * i + p
      have hs_M : s < 3 * M := by dsimp [s]; omega
      have hs_L : s < L.length := by rw [hL_len]; exact hs_M
      have h0D : (0 : Fin 13) ∈ Dgad s :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ (0 : Fin 13), hzD⟩
      have hlit_eq : L.getD s (0, false) =
          φ[i][p]'(by rw [h3 φ[i] (List.getElem_mem hi_φ)]; exact hp_lt) := by
        rw [List.getD_eq_getElem _ _ hs_L]
        have hf := flatten_getElem_three hψ3 hi_M hp_lt
        simpa [L, hψ_i] using hf
      set lit := φ[i][p]'(by rw [h3 φ[i] (List.getElem_mem hi_φ)]; exact hp_lt)
      have hs_occ : s ∈ occSlots L lit.1 := mem_occSlots_iff.mpr ⟨hs_L, by rw [hlit_eq]⟩
      rw [Clause.eval_eq_true_iff]
      refine ⟨lit, List.getElem_mem _, ?_⟩
      cases hpol : lit.2
      · have hneg_s : negSide s := by
          dsimp only [negSide]
          rw [hlit_eq, hpol]
          exact Or.inl h0D
        simp only [σ, decide_eq_false_iff_not, not_exists, not_and]
        intro s₀ hs₀ hp₀
        have hall := nextSlot_cycle_const
          (fun t ht hpt ↦ hstep_pos t (hL_len ▸ (mem_occSlots_iff.mp ht).1) hpt)
          hs₀ hp₀ s hs_occ
        exact hnot_both s hs_M ⟨hall, hneg_s⟩
      · have hpos_s : posSide s := by
          dsimp only [posSide]
          rw [hlit_eq, hpol]
          exact Or.inl h0D
        simp only [σ, decide_eq_true_eq]
        exact ⟨s, hs_occ, hpos_s⟩
  · rintro ⟨σ, hσ⟩
    have hψ_eval : ∀ i (hi : i < M), ψ[i].eval σ = true := by
      intro i hi
      have hall := (CNF.eval_eq_true_iff σ φ).mp hσ
      rcases List.mem_append.mp (List.getElem_mem hi) with h | h <;> exact hall _ h
    let pickList (s : ℕ) : List ℕ :=
      let lit := L.getD s (0, false)
      if σ lit.1 == lit.2 then h13SHi else h13SLo
    let D : Finset ℕ := (Finset.range (3 * M)).biUnion fun s ↦
      (pickList s).toFinset.image fun u ↦ gadVert s u
    have hpick_sub (s : ℕ) : ∀ u ∈ pickList s, u < 13 := by
      intro u hu
      dsimp only [pickList] at hu
      split_ifs at hu
      · simp only [h13SHi, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> omega
      · simp only [h13SLo, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> omega
    have hpick_card (s : ℕ) : (pickList s).toFinset.card = 4 := by
      dsimp only [pickList]
      split_ifs <;> decide
    refine ⟨D, ?_, ?_, ?_⟩
    · intro z hz
      simp only [D, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
        List.mem_toFinset] at hz
      obtain ⟨s, hs, u, hu, rfl⟩ := hz
      exact mem_cubicSATGraph_vertices.mpr (Or.inl ⟨s, hs, u, hpick_sub s u hu, rfl⟩)
    · intro w hw
      rcases mem_cubicSATGraph_vertices.mp hw with ⟨s, hs, u, hu, rfl⟩ | ⟨i, hi, rfl⟩ |
        ⟨s, hs, rfl⟩
      · have hex : ∃ v ∈ pickList s, ∃ hv : v < 13, h13Closed ⟨u, hu⟩ ⟨v, hv⟩ = true := by
          dsimp only [pickList]
          split_ifs
          · exact h13SHi_dom_all ⟨u, hu⟩
          · exact h13SLo_dom_all ⟨u, hu⟩
        obtain ⟨v, hv_mem, hv_lt, hcl⟩ := hex
        have hvD : gadVert s v ∈ D := by
          simp only [D, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.mem_toFinset]
          exact ⟨s, hs, v, hv_mem, rfl⟩
        simp only [h13Closed, Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff] at hcl
        rcases hcl with rfl | hadj
        · exact Or.inl hvD
        · exact Or.inr ⟨gadVert s v, hvD, (cubicSATGraph_adj_gad_gad hu hv_lt hs).mpr ⟨rfl, hadj⟩⟩
      · obtain ⟨lit, hlit_mem, hlit_true⟩ := (Clause.eval_eq_true_iff σ ψ[i]).mp (hψ_eval i hi)
        obtain ⟨p, hp_lt_cl, rfl⟩ := List.getElem_of_mem hlit_mem
        have hp_lt : p < 3 := by rw [hψ3 ψ[i] (List.getElem_mem hi)] at hp_lt_cl; exact hp_lt_cl
        set s := 3 * i + p
        have hs : s < 3 * M := by dsimp [s, M, ψ] at hi ⊢; omega
        have hs_L : s < L.length := by rw [hL_len]; exact hs
        have hget : L.getD s (0, false) = ψ[i][p] := by
          rw [List.getD_eq_getElem _ _ hs_L]
          exact flatten_getElem_three hψ3 hi hp_lt
        have h0_mem : 0 ∈ pickList s := by
          simp only [pickList, hget, hlit_true, beq_self_eq_true, ↓reduceIte, h13SHi,
            List.mem_cons, true_or]
        have h0D : gadVert s 0 ∈ D := by
          simp only [D, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.mem_toFinset]
          exact ⟨s, hs, 0, h0_mem, rfl⟩
        exact Or.inr ⟨gadVert s 0, h0D, (cubicSATGraph_adj_tern_iff hi).mpr ⟨p, hp_lt, rfl⟩⟩
      · have hs_L : s < L.length := hL_len ▸ hs
        have hprops := nextSlot_props hs_L
        set v := (L.getD s (0, false)).1
        cases hσv : σ v
        · have hmem : negPort L s ∈ pickList s := by
            dsimp only [pickList, negPort]
            change _ ∈ (if (σ v == (L.getD s (0, false)).2) then h13SHi else h13SLo)
            rw [hσv]
            cases (L.getD s (0, false)).2 <;> simp [h13SHi, h13SLo]
          have hD_in : gadVert s (negPort L s) ∈ D := by
            simp only [D, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.mem_toFinset]
            exact ⟨s, hs, negPort L s, hmem, rfl⟩
          exact Or.inr ⟨gadVert s (negPort L s), hD_in,
            (cubicSATGraph_adj_bin_iff hs).mpr (Or.inl rfl)⟩
        · set s' := nextSlot L s
          have hs'_M : s' < 3 * M := hL_len ▸ hprops.1
          have hmem : posBinPort L s' ∈ pickList s' := by
            dsimp only [pickList, posBinPort]
            rw [hprops.2.1, hσv]
            cases (L.getD s' (0, false)).2 <;> simp [h13SHi, h13SLo]
          have hD_in : gadVert s' (posBinPort L s') ∈ D := by
            simp only [D, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.mem_toFinset]
            exact ⟨s', hs'_M, posBinPort L s', hmem, rfl⟩
          exact Or.inr ⟨gadVert s' (posBinPort L s'), hD_in,
            (cubicSATGraph_adj_bin_iff hs).mpr (Or.inr (Or.inl rfl))⟩
    · rw [Finset.card_biUnion]
      · calc ∑ s ∈ Finset.range (3 * M), ((pickList s).toFinset.image fun u ↦ gadVert s u).card
            = ∑ s ∈ Finset.range (3 * M), (pickList s).toFinset.card :=
              Finset.sum_congr rfl fun s _ ↦ Finset.card_image_of_injOn fun a ha b hb h ↦ by
                have ha' := hpick_sub s a (List.mem_toFinset.mp ha)
                have hb' := hpick_sub s b (List.mem_toFinset.mp hb)
                exact (gadVert_inj (by omega) (by omega) h).2
          _ = ∑ _s ∈ Finset.range (3 * M), 4 :=
              Finset.sum_congr rfl fun s _ ↦ hpick_card s
          _ = 12 * M := by simp; omega
      · intro s₁ _ s₂ _ hne
        refine Finset.disjoint_left.mpr fun z hz₁ hz₂ ↦ hne ?_
        simp only [Finset.mem_image, List.mem_toFinset] at hz₁ hz₂
        obtain ⟨u₁, hu₁, rfl⟩ := hz₁
        obtain ⟨u₂, hu₂, heq⟩ := hz₂
        have b₁ := hpick_sub s₁ u₁ hu₁
        have b₂ := hpick_sub s₂ u₂ hu₂
        exact (gadVert_inj (by omega) (by omega) heq.symm).1

theorem toCubicDominatingSet_mem_iff (φ : CNF ℕ) :
    toCubicDominatingSet φ ∈ CubicDominatingSet ↔ φ ∈ ExactThreeSAT := by
  unfold toCubicDominatingSet
  by_cases hemp : φ.isEmpty = true
  · simp only [hemp, ↓reduceIte]
    have hnil : φ = [] := List.isEmpty_iff.mp hemp
    subst hnil
    refine iff_of_true k4Graph_one_mem_CubicDominatingSet ⟨by simp, fun _ ↦ false, rfl⟩
  · have hempF : φ.isEmpty = false := Bool.eq_false_iff.mpr hemp
    simp only [hempF, Bool.false_eq_true, ↓reduceIte]
    by_cases hex3 : isNonemptyExact3 φ = true
    · simp only [hex3, ↓reduceIte]
      have hne : φ ≠ [] := fun h ↦ hemp (List.isEmpty_iff.mpr h)
      have h3 : ∀ c ∈ φ, c.length = 3 := by
        simp only [isNonemptyExact3, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq] at hex3
        exact hex3.2
      simp only [CubicDominatingSet, Set.mem_ofPred_eq, ExactThreeSAT,
        cubicSATGraph_isCubic hne h3, true_and, cubicSATGraph_iff_satisfiable hne h3]
      exact ⟨fun h ↦ ⟨h3, h⟩, fun h ↦ h.2⟩
    · have hex3F : isNonemptyExact3 φ = false := Bool.eq_false_iff.mpr hex3
      simp only [hex3F, Bool.false_eq_true, ↓reduceIte]
      refine iff_of_false k4Graph_zero_notMem_CubicDominatingSet fun ⟨h3, _⟩ ↦ hex3 ?_
      simp only [isNonemptyExact3, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        decide_eq_true_eq]
      exact ⟨hempF, h3⟩

end CubicCorrectness

/-- `ExactThreeSAT` reduces in polynomial time to `CubicDominatingSet`. -/
theorem polyTimeReducible_ExactThreeSAT_CubicDominatingSet :
    PolyTimeReducible encCNF encDominatingSet ExactThreeSAT CubicDominatingSet :=
  ⟨toCubicDominatingSet, computableInPolyTime_toCubicDominatingSet,
    fun φ ↦ (toCubicDominatingSet_mem_iff φ).symm⟩

/-- `CubicDominatingSet` is `NP`-hard. -/
theorem CubicDominatingSet_npHard : NPHard encDominatingSet CubicDominatingSet :=
  ExactThreeSAT_npHard.trans polyTimeReducible_ExactThreeSAT_CubicDominatingSet

/-- **Dominating Set** is `NP`-complete even when restricted to cubic (`3`-regular) graphs. -/
theorem CubicDominatingSet_npComplete : NPComplete encDominatingSet CubicDominatingSet :=
  ⟨CubicDominatingSet_mem_NP, CubicDominatingSet_npHard⟩

end CslibFrontier.Complexity
