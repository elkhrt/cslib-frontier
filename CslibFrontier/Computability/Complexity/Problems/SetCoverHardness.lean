module

public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# $\mathrm{NP}$-Completeness of Set Cover and Family-Covered Set Cover

Establishes Karp's unconditional $\mathrm{NP}$-completeness of `Cslib.Complexity.SetCover` and of
its family-covered restriction `CoveredSetCover` (where the full candidate family covers the ground
universe), under standard Lean axioms, via a polynomial-time many-one reduction from
`Cslib.Complexity.VertexCover`.

## Main definitions

- `Cslib.Complexity.CoveredSetCover`: family-covered Set Cover decision problem
  requiring `S.Coverable` alongside `(S, k) ∈ Cslib.Complexity.SetCover`.
- `Cslib.Complexity.vertexCoverToSetCover`: polynomial-time many-one reduction
  from `Cslib.Complexity.VertexCover` to `Cslib.Complexity.SetCover` whose output set system is
  always coverable.

## Main results

- `Cslib.Complexity.coveredSetCover_mem_NP`: `CoveredSetCover ∈ NP encSetCover`.
- `Cslib.Complexity.vertexCoverToSetCover_coverable`: every output of
  `vertexCoverToSetCover` satisfies `SetSystem.Coverable`.
- `Cslib.Complexity.vertexCoverToSetCover_mem_iff`:
  `vertexCoverToSetCover x ∈ SetCover ↔ x ∈ VertexCover`.
- `Cslib.Complexity.computableInPolyTime_vertexCoverToSetCover`: polynomial-time
  computability of the reduction.
- `Cslib.Complexity.polyTimeReducible_VertexCover_SetCover`,
  `Cslib.Complexity.polyTimeReducible_VertexCover_CoveredSetCover`: Karp
  reductions from `VertexCover` to `SetCover` and `CoveredSetCover`.
- `Cslib.Complexity.setCover_npHard`,
  `Cslib.Complexity.setCover_npComplete`,
  `Cslib.Complexity.coveredSetCover_npHard`,
  `Cslib.Complexity.coveredSetCover_npComplete`: unconditional
  $\mathrm{NP}$-hardness and $\mathrm{NP}$-completeness.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Family-covered Set Cover: instances `(S, k)` where the full family `S.sets` covers `S.ground`
and at most `k` sets from `S.sets` suffice to cover `S.ground`. -/
@[expose]
def CoveredSetCover : Set (SetSystem × ℕ) :=
  {p | p.1.Coverable ∧ p ∈ SetCover}

/-- Membership characterization for `CoveredSetCover`. -/
theorem mem_coveredSetCover_iff {S : SetSystem} {k : ℕ} :
    (S, k) ∈ CoveredSetCover ↔ S.Coverable ∧ (S, k) ∈ SetCover :=
  Iff.rfl

/-- `CoveredSetCover` coincides with `SetCover` because every yes-instance of `SetCover` is
automatically coverable. -/
theorem coveredSetCover_eq_setCover : CoveredSetCover = SetCover := by
  ext ⟨S, k⟩
  exact ⟨fun h ↦ h.2, fun h ↦
    let ⟨C, hC, _⟩ := mem_SetCover_iff.1 h
    ⟨⟨C, hC⟩, h⟩⟩

/-- `CoveredSetCover` belongs to `NP encSetCover`. -/
theorem coveredSetCover_mem_NP : CoveredSetCover ∈ NP encSetCover := by
  rw [coveredSetCover_eq_setCover]
  exact SetCover_mem_NP

/-- Non-loop declared edges of a graph `G`: declared edges `(u, v)` with `u ≠ v`. -/
@[expose]
def nonLoopDeclaredEdges (G : Graph) : List (ℕ × ℕ) :=
  (VertexCover.declaredEdges G).filter fun e ↦ decide (e.1 ≠ e.2)

private theorem mem_nonLoopDeclaredEdges {G : Graph} {e : ℕ × ℕ} :
    e ∈ nonLoopDeclaredEdges G ↔ e ∈ G.edges ∧ e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices ∧ e.1 ≠ e.2 := by
  simp only [nonLoopDeclaredEdges, List.mem_filter, VertexCover.mem_declaredEdges,
    decide_eq_true_eq, and_assoc]

/-- Karp's polynomial-time reduction from `VertexCover` to `SetCover`:
- when `x.k ≤ x.graph.distinctVertices.length`, creates one ground element per non-loop declared
  edge index `j < (nonLoopDeclaredEdges x.graph).length` and one candidate set per distinct
  declared vertex `v`, containing all incident edge indices;
- when `x.k > x.graph.distinctVertices.length`, emits the fixed coverable no-instance
  `({ ground := [0], sets := [[0]] }, 0)`. -/
@[expose]
def vertexCoverToSetCover (x : VertexCoverInstance) : SetSystem × ℕ :=
  let V := x.graph.distinctVertices
  let E := nonLoopDeclaredEdges x.graph
  if x.k ≤ V.length then
    let ground := (List.range E.length).map id
    let sets := V.map fun v ↦
      ((List.range E.length).filter fun j ↦
        let e := E.getD j (0, 0)
        decide (e.1 = v) || decide (e.2 = v)).map id
    (⟨ground, sets⟩, x.k)
  else
    (⟨[0], [[0]]⟩, 0)

/-- Every image of `vertexCoverToSetCover` is coverable. -/
@[simp]
theorem vertexCoverToSetCover_coverable (x : VertexCoverInstance) :
    (vertexCoverToSetCover x).1.Coverable := by
  dsimp only [vertexCoverToSetCover]
  split_ifs with hk
  · refine ⟨Finset.univ, fun u hu ↦ ?_⟩
    simp only [List.map_id, List.mem_range] at hu
    let E := nonLoopDeclaredEdges x.graph
    let V := x.graph.distinctVertices
    have he_mem : E[u]'hu ∈ E := List.getElem_mem hu
    have hu1 : (E[u]'hu).1 ∈ V :=
      Graph.mem_distinctVertices.2 (mem_nonLoopDeclaredEdges.1 he_mem).2.1
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 hu1
    refine ⟨⟨i, by simpa [V] using hi⟩, Finset.mem_univ _, ?_⟩
    simp only [List.map_id, Fin.getElem_fin, List.getElem_map, List.mem_filter, List.mem_range,
      Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨hu, Or.inl ?_⟩
    dsimp only [E] at hiv ⊢
    rw [List.getD_eq_getElem _ _ hu]
    exact hiv.symm
  · refine ⟨Finset.univ, fun u hu ↦ ?_⟩
    simp only [List.mem_singleton] at hu
    subst hu
    exact ⟨⟨0, by decide⟩, Finset.mem_univ _, by simp⟩

/-- Exact membership equivalence for `vertexCoverToSetCover`. -/
@[simp]
theorem vertexCoverToSetCover_mem_iff (x : VertexCoverInstance) :
    vertexCoverToSetCover x ∈ SetCover ↔ x ∈ VertexCover := by
  dsimp only [vertexCoverToSetCover]
  split_ifs with hk
  · rw [mem_SetCover_iff, mem_VertexCover_iff_exists_card_le]
    let V := x.graph.distinctVertices
    let E := nonLoopDeclaredEdges x.graph
    constructor
    · rintro ⟨C, hC, hcard⟩
      refine ⟨by simpa [V, Graph.length_distinctVertices] using hk, ?_⟩
      let S : Finset ℕ := C.image fun i ↦ V[i.1]'(by simpa [V] using i.2)
      have hS_sub : ∀ v ∈ S, v ∈ x.graph.vertices := by
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
        exact Graph.mem_distinctVertices.1 (List.getElem_mem (by simpa [V] using i.2))
      have hS_card : S.card ≤ x.k := Finset.card_image_le.trans hcard
      refine ⟨S, hS_sub, fun u hu v hv hadj ↦ ?_, hS_card⟩
      obtain ⟨hne, hedges⟩ := Graph.toSimpleGraph_adj.1 hadj
      have hmemE : (u, v) ∈ E ∨ (v, u) ∈ E := hedges.imp
        (fun h ↦ mem_nonLoopDeclaredEdges.2 ⟨h, hu, hv, hne⟩)
        (fun h ↦ mem_nonLoopDeclaredEdges.2 ⟨h, hv, hu, hne.symm⟩)
      rcases hmemE with h | h <;>
        obtain ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.1 h <;>
        obtain ⟨i, hiC, hji⟩ := hC j (by simpa [E] using hj) <;>
        simp only [List.map_id, Fin.getElem_fin, List.getElem_map, List.mem_filter, List.mem_range,
          Bool.or_eq_true, decide_eq_true_eq] at hji <;>
        dsimp only [E] at hj hj_eq <;>
        rw [List.getD_eq_getElem _ _ hj, hj_eq] at hji <;>
        rcases hji.2 with h1 | h2
      · exact Or.inl (Finset.mem_image.2 ⟨i, hiC, h1.symm⟩)
      · exact Or.inr (Finset.mem_image.2 ⟨i, hiC, h2.symm⟩)
      · exact Or.inr (Finset.mem_image.2 ⟨i, hiC, h1.symm⟩)
      · exact Or.inl (Finset.mem_image.2 ⟨i, hiC, h2.symm⟩)
    · rintro ⟨_, S, hS_sub, hS_cov, hS_card⟩
      let C : Finset (Fin (V.map fun v ↦ ((List.range E.length).filter fun j ↦
          let e := E.getD j (0, 0); decide (e.1 = v) || decide (e.2 = v)).map id).length) :=
        Finset.univ.filter fun i ↦ V[i.1]'(by simpa [V] using i.2) ∈ S
      have hC_card : C.card ≤ x.k := by
        have hinj : Set.InjOn (fun i : Fin (V.map fun v ↦
            ((List.range E.length).filter fun j ↦
              let e := E.getD j (0, 0); decide (e.1 = v) || decide (e.2 = v)).map id).length =>
            V[i.1]'(by simpa [V] using i.2)) (C : Set _) := fun i _ j _ heq ↦
          Fin.ext ((List.Nodup.getElem_inj_iff (Graph.nodup_distinctVertices x.graph)).1 heq)
        have hle : C.card ≤ S.card :=
          Finset.card_le_card_of_injOn _
            (fun i hi ↦ (Finset.mem_filter.1 hi).2) hinj
        exact hle.trans hS_card
      refine ⟨C, fun u hu ↦ ?_, hC_card⟩
      simp only [List.map_id, List.mem_range] at hu
      have he_mem : E[u]'hu ∈ E := List.getElem_mem hu
      obtain ⟨hedge, h1, h2, hne⟩ := mem_nonLoopDeclaredEdges.1 he_mem
      have hadj : x.graph.toSimpleGraph.Adj (E[u]'hu).1 (E[u]'hu).2 :=
        Graph.toSimpleGraph_adj.2 ⟨hne, Or.inl hedge⟩
      rcases hS_cov _ h1 _ h2 hadj with h1S | h2S
      · obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 (Graph.mem_distinctVertices.2 h1)
        refine ⟨⟨i, by simpa [V] using hi⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [V, hiv] using h1S⟩, ?_⟩
        simp only [List.map_id, Fin.getElem_fin, List.getElem_map, List.mem_filter, List.mem_range,
          Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨hu, Or.inl (by
          dsimp only [E] at hiv ⊢; rw [List.getD_eq_getElem _ _ hu]; exact hiv.symm)⟩
      · obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 (Graph.mem_distinctVertices.2 h2)
        refine ⟨⟨i, by simpa [V] using hi⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa [V, hiv] using h2S⟩, ?_⟩
        simp only [List.map_id, Fin.getElem_fin, List.getElem_map, List.mem_filter, List.mem_range,
          Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨hu, Or.inr (by
          dsimp only [E] at hiv ⊢; rw [List.getD_eq_getElem _ _ hu]; exact hiv.symm)⟩
  · constructor
    · intro h
      obtain ⟨C, hC, hcard⟩ := mem_SetCover_iff.1 h
      have hC0 : C = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_le_zero hcard)
      obtain ⟨i, hi, _⟩ := hC 0 (by simp)
      simp [hC0] at hi
    · intro h
      have hle := (mem_VertexCover_iff_exists_card_le.1 h).1
      rw [← Graph.length_distinctVertices] at hle
      exact absurd hle hk

/-- `vertexCoverToSetCover` is computable in polynomial time. -/
theorem computableInPolyTime_vertexCoverToSetCover :
    ComputableInPolyTime vertexCoverToSetCover encVertexCoverInstance encSetCover := by
  have hE : ComputableInPolyTime (fun x : VertexCoverInstance ↦ nonLoopDeclaredEdges x.graph)
      encVertexCoverInstance (encList (encPair encNat encNat)) := by
    unfold nonLoopDeclaredEdges
    refine filterWithInput
      (VertexCover.computableInPolyTime_declaredEdges.comp (by fun_prop)) ?_
    have h1 : ComputableInPolyTime (fun q : VertexCoverInstance × (ℕ × ℕ) ↦ q.2.1)
        (encPair encVertexCoverInstance (encPair encNat encNat)) encNat := by fun_prop
    have h2 : ComputableInPolyTime (fun q : VertexCoverInstance × (ℕ × ℕ) ↦ q.2.2)
        (encPair encVertexCoverInstance (encPair encNat encNat)) encNat := by fun_prop
    exact decide_ne h1 h2
  have hElen : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ (nonLoopDeclaredEdges x.graph).length)
      encVertexCoverInstance encUnary :=
    (length_list (encPair encNat encNat)).comp hE
  have hV : ComputableInPolyTime (fun x : VertexCoverInstance ↦ x.graph.distinctVertices)
      encVertexCoverInstance (encList encNat) := by fun_prop
  have hVlen : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ x.graph.distinctVertices.length)
      encVertexCoverInstance encNat :=
    unary_to_binary.comp ((length_list encNat).comp hV)
  have hcond : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ decide (x.k ≤ x.graph.distinctVertices.length))
      encVertexCoverInstance encBool :=
    binary_le' (by fun_prop) hVlen
  have hground : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ (List.range (nonLoopDeclaredEdges x.graph).length).map id)
      encVertexCoverInstance (encList encNat) :=
    mapWithInput (range.comp hElen) (unary_to_binary.comp (snd _ _))
  have hsets : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ x.graph.distinctVertices.map fun v ↦
        ((List.range (nonLoopDeclaredEdges x.graph).length).filter fun j ↦
          let e := (nonLoopDeclaredEdges x.graph).getD j (0, 0)
          decide (e.1 = v) || decide (e.2 = v)).map id)
      encVertexCoverInstance encNatSetList := by
    have hget : ComputableInPolyTime
        (fun q : (VertexCoverInstance × ℕ) × ℕ ↦
          (nonLoopDeclaredEdges q.1.1.graph).getD q.2 (0, 0))
        (encPair (encPair encVertexCoverInstance encNat) encUnary) (encPair encNat encNat) := by
      have h1 : ComputableInPolyTime
          (fun q : (VertexCoverInstance × ℕ) × ℕ ↦ nonLoopDeclaredEdges q.1.1.graph)
          (encPair (encPair encVertexCoverInstance encNat) encUnary)
          (encList (encPair encNat encNat)) :=
        hE.comp ((fst encVertexCoverInstance encNat).comp (fst _ _))
      exact listGetDWithInput h1 (snd _ _) (0, 0)
    have hpred : ComputableInPolyTime
        (fun q : (VertexCoverInstance × ℕ) × ℕ ↦
          let e := (nonLoopDeclaredEdges q.1.1.graph).getD q.2 (0, 0)
          decide (e.1 = q.1.2) || decide (e.2 = q.1.2))
        (encPair (encPair encVertexCoverInstance encNat) encUnary) encBool := by
      have hv : ComputableInPolyTime (fun q : (VertexCoverInstance × ℕ) × ℕ ↦ q.1.2)
          (encPair (encPair encVertexCoverInstance encNat) encUnary) encNat := by fun_prop
      exact decide_or (decide_eq' ((fst encNat encNat).comp hget) hv)
        (decide_eq' ((snd encNat encNat).comp hget) hv)
    have hfilt : ComputableInPolyTime
        (fun p : VertexCoverInstance × ℕ ↦
          (List.range (nonLoopDeclaredEdges p.1.graph).length).filter fun j ↦
            let e := (nonLoopDeclaredEdges p.1.graph).getD j (0, 0)
            decide (e.1 = p.2) || decide (e.2 = p.2))
        (encPair encVertexCoverInstance encNat) (encList encUnary) :=
      filterWithInput (range.comp (hElen.comp (fst _ _))) hpred
    have hrow : ComputableInPolyTime
        (fun p : VertexCoverInstance × ℕ ↦
          ((List.range (nonLoopDeclaredEdges p.1.graph).length).filter fun j ↦
            let e := (nonLoopDeclaredEdges p.1.graph).getD j (0, 0)
            decide (e.1 = p.2) || decide (e.2 = p.2)).map id)
        (encPair encVertexCoverInstance encNat) (encList encNat) :=
      mapWithInput hfilt (unary_to_binary.comp (snd _ _))
    exact mapWithInput hV hrow
  have hthen : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦
        (SetSystem.mk
          ((List.range (nonLoopDeclaredEdges x.graph).length).map id)
          (x.graph.distinctVertices.map fun v ↦
            ((List.range (nonLoopDeclaredEdges x.graph).length).filter fun j ↦
              let e := (nonLoopDeclaredEdges x.graph).getD j (0, 0)
              decide (e.1 = v) || decide (e.2 = v)).map id),
         x.k))
      encVertexCoverInstance encSetCover :=
    (computableInPolyTime_setSystemMk hground hsets).prod (by fun_prop)
  have helse : ComputableInPolyTime
      (fun _ : VertexCoverInstance ↦ ((⟨[0], [[0]]⟩, 0) : SetSystem × ℕ))
      encVertexCoverInstance encSetCover :=
    const ((⟨[0], [[0]]⟩, 0) : SetSystem × ℕ)
  exact (ite' hcond hthen helse).of_enc_eq fun x ↦ congrArg encSetCover <| by
    by_cases h : x.k ≤ x.graph.distinctVertices.length <;> simp [vertexCoverToSetCover, h]

/-- Polynomial-time many-one reduction from `VertexCover` to `SetCover`. -/
theorem polyTimeReducible_VertexCover_SetCover :
    PolyTimeReducible encVertexCoverInstance encSetCover VertexCover SetCover :=
  ⟨vertexCoverToSetCover, computableInPolyTime_vertexCoverToSetCover,
    fun x ↦ (vertexCoverToSetCover_mem_iff x).symm⟩

/-- Polynomial-time many-one reduction from `VertexCover` to `CoveredSetCover`. -/
theorem polyTimeReducible_VertexCover_CoveredSetCover :
    PolyTimeReducible encVertexCoverInstance encSetCover VertexCover CoveredSetCover := by
  rw [coveredSetCover_eq_setCover]
  exact polyTimeReducible_VertexCover_SetCover

/-- `SetCover` is unconditionally $\mathrm{NP}$-hard. -/
theorem setCover_npHard : NPHard encSetCover SetCover :=
  VertexCover_npHard.trans polyTimeReducible_VertexCover_SetCover

/-- **Karp's Theorem**: `SetCover` is unconditionally $\mathrm{NP}$-complete. -/
theorem setCover_npComplete : NPComplete encSetCover SetCover :=
  ⟨SetCover_mem_NP, setCover_npHard⟩

/-- `CoveredSetCover` is unconditionally $\mathrm{NP}$-hard. -/
theorem coveredSetCover_npHard : NPHard encSetCover CoveredSetCover :=
  VertexCover_npHard.trans polyTimeReducible_VertexCover_CoveredSetCover

/-- `CoveredSetCover` is unconditionally $\mathrm{NP}$-complete. -/
theorem coveredSetCover_npComplete : NPComplete encSetCover CoveredSetCover :=
  ⟨coveredSetCover_mem_NP, coveredSetCover_npHard⟩

private example : (⟨[0, 1, 2], [[0, 1], [1, 2], [0]]⟩, 2) ∈ SetCover := by
  let C : Finset (Fin 3) := {⟨0, by decide⟩, ⟨1, by decide⟩}
  refine mem_SetCover_iff.2 ⟨C, fun u hu ↦ ?_, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, by decide, by decide⟩
  · exact ⟨⟨0, by decide⟩, by decide, by decide⟩
  · exact ⟨⟨1, by decide⟩, by decide, by decide⟩

private example : (⟨[0, 1, 2], [[0], [1], [2]]⟩, 2) ∉ SetCover := by
  intro h
  obtain ⟨C, hC, hcard⟩ := mem_SetCover_iff.1 h
  have huniv : C = Finset.univ := by
    refine Finset.eq_univ_iff_forall.2 fun e ↦ ?_
    obtain ⟨i, hiC, hui⟩ := hC e.1 (by fin_cases e <;> decide)
    have hie : i = e := by fin_cases e <;> fin_cases i <;> simp_all
    rwa [← hie]
  rw [huniv] at hcard
  exact absurd hcard (by decide)

end Cslib.Complexity
