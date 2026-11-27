/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Uniform Graph Coloring, Budgeted Maximum Coverage, and `NP`-Hardness Collapse

General computational-complexity results on deterministic and nondeterministic multi-tape Turing
machines complementing `CslibFrontier.Computability.Complexity.Reduction`,
`CslibFrontier.Computability.Complexity.Problems.Coloring`, and
`CslibFrontier.Computability.Complexity.Problems.VertexCover`:

* `CslibFrontier.Computability.Complexity.p_eq_np_of_npHard_mem_P`: solving any `NPHard` problem
  (not necessarily in `NP`) in polynomial time collapses `P = NP` across every instance encoding.
* `CslibFrontier.Computability.Complexity.GraphColoring`: uniform `(G, k)` graph coloring with `k`
  encoded in binary (`encNat`), proved `NPComplete` (`graphColoring_npComplete`) by combining
  polynomial-time acceptance when `|V| ≤ k` with unary palette certificates when `k < |V|`.
* `CslibFrontier.Computability.Complexity.MaxCoverage`: budgeted maximum coverage `(U, sets, k, r)`,
  proved `NPComplete` (`maxCoverage_npComplete`) via polynomial-time reduction from `VertexCover`.
-/

public section

namespace CslibFrontier.Computability.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity

private theorem equiv_toEmbedding_trans_polyTime {α β γ : Type} {enc : γ ↪ List Bool}
    {encB : β ↪ List Bool} (e : α ≃ β) {f : γ → α}
    (hf : ComputableInPolyTime f enc (e.toEmbedding.trans encB)) :
    ComputableInPolyTime (fun x => e (f x)) enc encB :=
  hf.of_enc_eq fun _ => rfl

private theorem equiv_symm_polyTime {α β γ : Type} {enc : γ ↪ List Bool}
    {encB : β ↪ List Bool} (e : α ≃ β) {g : γ → β}
    (hg : ComputableInPolyTime g enc encB) :
    ComputableInPolyTime (fun x => e.symm (g x)) enc (e.toEmbedding.trans encB) :=
  hg.of_enc_eq fun x => by simp

/-- Solving any `NPHard` language in polynomial time implies `P = NP` on every encoding. -/
public theorem p_eq_np_of_npHard_mem_P {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hHard : NPHard encB B) (hP : B ∈ P encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_subset_NP.antisymm fun _ hA => (hHard enc _ hA).mem_P hP

/-! ### Uniform `(G, k)` Graph Coloring -/

/-- Instance `(graph, k)` of uniform **Graph Coloring**, with `k` encoded in binary. -/
@[ext]
public structure GraphColoringInstance where
  /-- Input undirected graph. -/
  graph : Graph
  /-- Number of available colors `k`. -/
  k : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Tuple equivalence for `GraphColoringInstance`. -/
@[expose]
public def graphColoringEquiv : GraphColoringInstance ≃ Graph × ℕ where
  toFun x := (x.graph, x.k)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- Framed `encGraph` paired with binary `encNat`. -/
@[expose]
public def encGraphColoring : GraphColoringInstance ↪ List Bool :=
  graphColoringEquiv.toEmbedding.trans (encPair encGraph encNat)

/-- Uniform **Graph Coloring**: pairs `(G, k)` where `G ∈ KColoring k`. -/
@[expose]
public def GraphColoring : Set GraphColoringInstance :=
  {x | x.graph ∈ KColoring x.k}

/-- Every graph with at most `k` distinct declared vertices is properly `k`-colorable. -/
public theorem mem_KColoring_of_distinctVertices_le {G : Graph} {k : ℕ}
    (hk : G.distinctVertices.length ≤ k) :
    G ∈ KColoring k := by
  rw [mem_KColoring_iff]
  refine ⟨fun v => G.distinctVertices.idxOf v, fun v hv => ?_, fun u hu v hv huv hEq => ?_⟩
  · exact (List.idxOf_lt_length_iff.mpr (G.mem_distinctVertices.mpr hv)).trans_le hk
  · have huLt := List.idxOf_lt_length_iff.mpr (G.mem_distinctVertices.mpr hu)
    have hvLt := List.idxOf_lt_length_iff.mpr (G.mem_distinctVertices.mpr hv)
    have huvEq : u = v := by
      rw [← List.getElem_idxOf huLt, ← List.getElem_idxOf hvLt]
      simp [hEq]
    exact huv.ne huvEq

private def graphColoringCheck (p : GraphColoringInstance × List ℕ) : Bool :=
  let x := p.1
  let cols := p.2
  decide (x.graph.distinctVertices.length ≤ x.k) ||
    (x.graph.vertices.all (fun u =>
        decide (cols.getD (x.graph.vertices.idxOf u) 0 < x.k)) &&
      x.graph.vertices.all (fun u =>
        x.graph.vertices.all (fun v =>
          !(x.graph.adjBool u v &&
            decide (cols.getD (x.graph.vertices.idxOf u) 0 =
              cols.getD (x.graph.vertices.idxOf v) 0)))))

private theorem length_encList_encUnary_le {cols : List ℕ} {B : ℕ} (hB : ∀ c ∈ cols, c ≤ B) :
    (encList encUnary cols).length ≤ cols.length * (2 * B + 1) := by
  induction cols with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≤ B := hB c List.mem_cons_self
    have hcs := ih fun x hx => hB x (List.mem_cons_of_mem c hx)
    simp only [encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate, List.length_cons]
    have hMul : (cs.length + 1) * (2 * B + 1) = cs.length * (2 * B + 1) + (2 * B + 1) := by ring
    rw [hMul]
    omega

/-- Uniform `(G, k)` `GraphColoring` belongs to `NP` with binary `k`. -/
public theorem graphColoring_mem_NP : GraphColoring ∈ NP encGraphColoring := by
  let encW : List ℕ ↪ List Bool := encList encUnary
  have hGraph : ComputableInPolyTime (fun p : GraphColoringInstance × List ℕ => p.1.graph)
      (encPair encGraphColoring encW) encGraph :=
    fst' (equiv_toEmbedding_trans_polyTime graphColoringEquiv (fst encGraphColoring encW))
  have hK : ComputableInPolyTime (fun p : GraphColoringInstance × List ℕ => p.1.k)
      (encPair encGraphColoring encW) encNat :=
    snd' (equiv_toEmbedding_trans_polyTime graphColoringEquiv (fst encGraphColoring encW))
  have hVerts : ComputableInPolyTime (fun p : GraphColoringInstance × List ℕ => p.1.graph.vertices)
      (encPair encGraphColoring encW) (encList encNat) := by fun_prop
  have hDistLen : ComputableInPolyTime
      (fun p : GraphColoringInstance × List ℕ => p.1.graph.distinctVertices.length)
      (encPair encGraphColoring encW) encNat :=
    unary_to_binary.comp ((length_list encNat).comp
      (Graph.computableInPolyTime_distinctVertices.comp hGraph))
  have hBranch1 := binary_le' hDistLen hK
  have hColAt : ComputableInPolyTime
      (fun q : (GraphColoringInstance × List ℕ) × ℕ =>
        q.1.2.getD (q.1.1.graph.vertices.idxOf q.2) 0)
      (encPair (encPair encGraphColoring encW) encNat) encUnary :=
    listGetDWithInput ((snd encGraphColoring encW).comp (fst _ encNat))
      (idxOfWithInput (hVerts.comp (fst _ encNat)) (snd _ encNat)) 0
  have hAllBounds : ComputableInPolyTime
      (fun p : GraphColoringInstance × List ℕ => p.1.graph.vertices.all fun u =>
        decide (p.2.getD (p.1.graph.vertices.idxOf u) 0 < p.1.k))
      (encPair encGraphColoring encW) encBool :=
    allWithInput hVerts (binary_lt' (unary_to_binary.comp hColAt) (hK.comp (fst _ encNat)))
  have hAllEdges : ComputableInPolyTime
      (fun p : GraphColoringInstance × List ℕ => p.1.graph.vertices.all fun u =>
        p.1.graph.vertices.all fun v =>
          !(p.1.graph.adjBool u v &&
            decide (p.2.getD (p.1.graph.vertices.idxOf u) 0 =
              p.2.getD (p.1.graph.vertices.idxOf v) 0)))
      (encPair encGraphColoring encW) encBool := by
    apply allWithInput hVerts
    apply allWithInput (hVerts.comp (fst _ encNat))
    have hAdj := Graph.computableInPolyTime_adjBool_comp
      (hGraph.comp ((fst _ encNat).comp (fst _ encNat)))
      ((snd _ encNat).comp (fst _ encNat)) (snd _ encNat)
    have hColU := hColAt.comp (fst _ encNat)
    have hColV := hColAt.comp ((((fst _ encNat).comp (fst _ encNat))).prod (snd _ encNat))
    exact bool_not.comp (bool_and' hAdj (unary_beq hColU hColV))
  have hCheck : ComputableInPolyTime graphColoringCheck
      (encPair encGraphColoring encW) encBool :=
    bool_or.comp (hBranch1.prod (bool_and' hAllBounds hAllEdges))
  refine mem_NP_of_check (p := Polynomial.C 3 * Polynomial.X ^ 2 + 1)
    (Decoder.list Decoder.unary) hCheck (fun x cols hAcc => ?_) (fun x hx => ?_)
  · simp only [graphColoringCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      Graph.adjBool_eq_false_iff, decide_eq_false_iff_not] at hAcc
    rcases hAcc with hle | ⟨hBnd, hProper⟩
    · exact mem_KColoring_of_distinctVertices_le hle
    · rw [GraphColoring, Set.mem_ofPred_eq, mem_KColoring_iff]
      exact ⟨fun u => cols.getD (x.graph.vertices.idxOf u) 0, hBnd,
        fun u hu v hv huv => (hProper u hu v hv).resolve_left (by simp [huv])⟩
  · by_cases hle : x.graph.distinctVertices.length ≤ x.k
    · exact ⟨[], by simp [graphColoringCheck, hle], by simp⟩
    · have hkLt : x.k < x.graph.distinctVertices.length := Nat.lt_of_not_ge hle
      obtain ⟨c, hcBnd, hcAdj⟩ := mem_KColoring_iff.mp hx
      let cols := x.graph.vertices.map fun u => if u ∈ x.graph.vertices then c u else 0
      have hLookup : ∀ u ∈ x.graph.vertices,
          cols.getD (x.graph.vertices.idxOf u) 0 = c u := by
        intro u hu
        have hIdxLt := List.idxOf_lt_length_iff.mpr hu
        have hColsLt : x.graph.vertices.idxOf u < cols.length := by simpa [cols] using hIdxLt
        rw [List.getD_eq_getElem _ _ hColsLt]
        simp [cols, List.getElem_idxOf hIdxLt, hu]
      refine ⟨cols, ?_, ?_⟩
      · simp only [graphColoringCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
          Graph.adjBool_eq_false_iff, decide_eq_false_iff_not]
        refine Or.inr ⟨fun u hu => hLookup u hu ▸ hcBnd u hu, fun u hu v hv => ?_⟩
        rw [hLookup u hu, hLookup v hv]
        by_cases huv : x.graph.toSimpleGraph.Adj u v
        · exact Or.inr (hcAdj u hu v hv huv)
        · exact Or.inl huv
      · have hVertsLeEnc : x.graph.vertices.length ≤ (encGraphColoring x).length := by
          have h1 := x.graph.length_vertices_le_encGraph
          have hEq : encGraphColoring x = encPair encGraph encNat (x.graph, x.k) := rfl
          have h2 : (encGraph x.graph).length ≤ (encGraphColoring x).length := by
            rw [hEq]; simp only [length_encPair]; omega
          exact h1.trans h2
        have hDistLeVerts : x.graph.distinctVertices.length ≤ x.graph.vertices.length := by
          rw [Graph.length_distinctVertices]
          exact List.toFinset_card_le x.graph.vertices
        have hkLeEnc : x.k ≤ (encGraphColoring x).length :=
          hkLt.le.trans (hDistLeVerts.trans hVertsLeEnc)
        have hColsBnd : ∀ m ∈ cols, m ≤ x.k := by
          intro m hm
          dsimp only [cols] at hm
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
          simp only [hu, ↓reduceIte]
          exact (hcBnd u hu).le
        have hColsLen : (encW cols).length ≤ x.graph.vertices.length * (2 * x.k + 1) := by
          simpa [cols, encW] using length_encList_encUnary_le (B := x.k) hColsBnd
        have hProd : x.graph.vertices.length * (2 * x.k + 1) ≤
            3 * (encGraphColoring x).length ^ 2 + 1 := by
          set L := (encGraphColoring x).length
          rcases eq_or_ne L 0 with hL0 | hLPos
          · have hv0 : x.graph.vertices.length = 0 := Nat.eq_zero_of_le_zero (hL0 ▸ hVertsLeEnc)
            simp [hv0]
          · calc x.graph.vertices.length * (2 * x.k + 1)
                ≤ L * (3 * L) := Nat.mul_le_mul hVertsLeEnc (by omega)
              _ ≤ 3 * L ^ 2 + 1 := by ring_nf; omega
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        exact hColsLen.trans hProd

/-- **Uniform `(G, k)` `GraphColoring` is `NP`-complete**. -/
public theorem graphColoring_npComplete : NPComplete encGraphColoring GraphColoring :=
  ⟨graphColoring_mem_NP,
    ThreeColoring_npHard.trans
      ⟨fun G => ⟨G, 3⟩, equiv_symm_polyTime graphColoringEquiv (id'.prod (const 3)),
        fun _ => Iff.rfl⟩⟩

/-! ### Budgeted Maximum Coverage (`MaxCoverage`) -/

/-- Instance `(candidates, demands, budget, target)` of **Budgeted Maximum Coverage**: candidate
elements `candidates`, demand subsets `demands` (each covered when it intersects the chosen subset
of `candidates`), cardinality budget `budget`, and coverage target `target`. -/
@[ext]
public structure MaxCoverageInstance where
  /-- Candidate elements from which at most `budget` may be chosen. -/
  candidates : List ℕ
  /-- Demand lists to cover by intersecting the chosen subset. -/
  demands : List (List ℕ)
  /-- Maximum allowed size of the chosen subset. -/
  budget : ℕ
  /-- Minimum required number of covered demand lists. -/
  target : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Tuple equivalence for `MaxCoverageInstance`. -/
@[expose]
public def maxCoverageEquiv :
    MaxCoverageInstance ≃ ((List ℕ × List (List ℕ)) × ℕ) × ℕ where
  toFun x := (((x.candidates, x.demands), x.budget), x.target)
  invFun t := ⟨t.1.1.1, t.1.1.2, t.1.2, t.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl

/-- Binary encoding of `MaxCoverageInstance`. -/
@[expose]
public def encMaxCoverage : MaxCoverageInstance ↪ List Bool :=
  maxCoverageEquiv.toEmbedding.trans
    (encPair (encPair (encPair (encList encNat) (encList (encList encNat))) encNat) encNat)

/-- Number of demand lists in `x.demands` intersecting `S ∩ x.candidates`. -/
@[expose]
public def coveredDemandCount (x : MaxCoverageInstance) (S : List ℕ) : ℕ :=
  x.demands.countP fun D => D.any fun t => decide (t ∈ x.candidates) && decide (t ∈ S)

/-- **Budgeted Maximum Coverage**: instances admitting a subset `S ⊆ candidates` of size at most
`budget` covering at least `target` demand lists. -/
@[expose]
public def MaxCoverage : Set MaxCoverageInstance :=
  {x | ∃ S : Finset ℕ, (∀ t ∈ S, t ∈ x.candidates) ∧
    S.card ≤ x.budget ∧ x.target ≤ coveredDemandCount x S.toList}

/-- `MaxCoverage` belongs to `NP`. -/
public theorem maxCoverage_mem_NP : MaxCoverage ∈ NP encMaxCoverage := by
  have hTup := equiv_toEmbedding_trans_polyTime maxCoverageEquiv (id' (encIn := encMaxCoverage))
  have hCand : ComputableInPolyTime MaxCoverageInstance.candidates
      encMaxCoverage (encList encNat) := fst' (fst' (fst' hTup))
  have hDem : ComputableInPolyTime MaxCoverageInstance.demands
      encMaxCoverage (encList (encList encNat)) := snd' (fst' (fst' hTup))
  have hBud : ComputableInPolyTime MaxCoverageInstance.budget encMaxCoverage encNat :=
    snd' (fst' hTup)
  have hTgt : ComputableInPolyTime MaxCoverageInstance.target encMaxCoverage encNat :=
    snd' hTup
  let check : MaxCoverageInstance × List ℕ → Bool := fun p =>
    decide (p.2.length ≤ p.1.budget) && decide (p.1.target ≤ coveredDemandCount p.1 p.2)
  have hCov : ComputableInPolyTime
      (fun p : MaxCoverageInstance × List ℕ => coveredDemandCount p.1 p.2)
      (encWithEntries encMaxCoverage encNat) encNat := by
    refine unary_to_binary.comp ?_
    refine countPWithInput (hDem.comp (fst encMaxCoverage (encList encNat))) ?_
    refine anyWithInput (snd (encWithEntries encMaxCoverage encNat) (encList encNat)) ?_
    let encIn := encPair (encWithEntries encMaxCoverage encNat) (encList encNat)
    have hQ1 := fst encIn encNat
    have hC := hCand.comp (fst' (fst' hQ1))
    have hSel := snd' (fst' hQ1)
    have hElem := snd (encPair encIn encNat) encNat
    have hTSub := snd' (fst (encPair encIn encNat) encNat)
    have hInC : ComputableInPolyTime
        (fun q : ((MaxCoverageInstance × List ℕ) × List ℕ) × ℕ =>
          decide (q.2 ∈ q.1.1.1.candidates))
        (encPair encIn encNat) encBool := by
      have hAny := anyWithInput
        (test := fun (q : ((MaxCoverageInstance × List ℕ) × List ℕ) × ℕ) u => decide (u = q.2))
        hC (decide_eq' hElem hTSub)
      exact hAny.of_enc_eq fun _ =>
        congrArg encBool (by rw [Bool.eq_iff_iff, List.any_eq_true]; simp [eq_comm])
    have hInSel : ComputableInPolyTime
        (fun q : ((MaxCoverageInstance × List ℕ) × List ℕ) × ℕ => decide (q.2 ∈ q.1.1.2))
        (encPair encIn encNat) encBool := by
      have hAny := anyWithInput
        (test := fun (q : ((MaxCoverageInstance × List ℕ) × List ℕ) × ℕ) u => decide (u = q.2))
        hSel (decide_eq' hElem hTSub)
      exact hAny.of_enc_eq fun _ =>
        congrArg encBool (by rw [Bool.eq_iff_iff, List.any_eq_true]; simp [eq_comm])
    exact bool_and' hInC hInSel
  have hCheck : ComputableInPolyTime check (encWithEntries encMaxCoverage encNat) encBool :=
    bool_and'
      (binary_le'
        (unary_to_binary.comp ((length_list encNat).comp (snd encMaxCoverage (encList encNat))))
        (hBud.comp (fst encMaxCoverage (encList encNat))))
      (binary_le' (hTgt.comp (fst encMaxCoverage (encList encNat))) hCov)
  refine mem_NP_of_subsetWitness hCand hCheck fun x l hl _ => ?_
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.toFinset_card_of_nodup hl]
  have hEq : coveredDemandCount x l = coveredDemandCount x l.toFinset.toList := by
    unfold coveredDemandCount
    congr 1; funext D; congr 1; funext t; simp
  rw [hEq]

/-- Polynomial-time reduction from `VertexCover` to `MaxCoverage`. -/
public def vertexCoverToMaxCoverage (x : VertexCoverInstance) : MaxCoverageInstance :=
  if decide (x.graph.distinctVertices.length < x.k) then
    ⟨[], [], 0, 1⟩
  else
    let E := (VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2)
    ⟨x.graph.vertices, E.map (fun e => [e.1, e.2]), x.k, E.length⟩

/-- Correctness of `vertexCoverToMaxCoverage`. -/
public theorem vertexCoverToMaxCoverage_mem_iff (x : VertexCoverInstance) :
    vertexCoverToMaxCoverage x ∈ MaxCoverage ↔ x ∈ VertexCover := by
  unfold vertexCoverToMaxCoverage
  rw [mem_VertexCover_iff_exists_card_le, ← Graph.length_distinctVertices]
  by_cases hGt : x.graph.distinctVertices.length < x.k
  · simp only [hGt, decide_true, ↓reduceIte, MaxCoverage, Set.mem_ofPred_eq]
    refine ⟨fun ⟨S, _, _, hAtt⟩ => ?_, fun ⟨hle, _⟩ => by omega⟩
    simp [coveredDemandCount] at hAtt
  · have hLe : x.k ≤ x.graph.distinctVertices.length := Nat.le_of_not_lt hGt
    simp only [hGt, decide_false, Bool.false_eq_true, ↓reduceIte, MaxCoverage,
      Set.mem_ofPred_eq, hLe, true_and]
    set E := (VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2)
    let inst : MaxCoverageInstance :=
      ⟨x.graph.vertices, E.map (fun e => [e.1, e.2]), x.k, E.length⟩
    have hAllCoverIff : ∀ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) →
        (E.length ≤ coveredDemandCount inst S.toList ↔
          ∀ u ∈ x.graph.vertices, ∀ v ∈ x.graph.vertices,
            x.graph.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) := by
      intro S _
      have hUpper := List.countP_le_length (l := inst.demands)
        (p := fun D => D.any fun t => decide (t ∈ inst.candidates) && decide (t ∈ S.toList))
      have hLen : inst.demands.length = E.length := by simp [inst]
      rw [hLen] at hUpper
      have hIff : E.length ≤ coveredDemandCount inst S.toList ↔
          coveredDemandCount inst S.toList = inst.demands.length := by
        rw [hLen, coveredDemandCount]; omega
      rw [hIff, coveredDemandCount, List.countP_eq_length]
      dsimp only [inst]
      constructor
      · intro hAll u hu v hv hAdj
        rw [Graph.toSimpleGraph_adj] at hAdj
        rcases hAdj with ⟨huv, hEdge | hEdge⟩
        · have heMem : (u, v) ∈ E := List.mem_filter.mpr
            ⟨VertexCover.mem_declaredEdges.mpr ⟨hEdge, hu, hv⟩, decide_eq_true huv⟩
          have hAny := hAll [u, v] (List.mem_map_of_mem heMem)
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
            Bool.and_eq_true, decide_eq_true_eq, Finset.mem_toList] at hAny
          exact hAny.imp And.right And.right
        · have heMem : (v, u) ∈ E := List.mem_filter.mpr
            ⟨VertexCover.mem_declaredEdges.mpr ⟨hEdge, hv, hu⟩, decide_eq_true huv.symm⟩
          have hAny := hAll [v, u] (List.mem_map_of_mem heMem)
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
            Bool.and_eq_true, decide_eq_true_eq, Finset.mem_toList] at hAny
          exact (hAny.imp And.right And.right).symm
      · intro hCov Si hSi
        obtain ⟨⟨u, v⟩, heMem, rfl⟩ := List.mem_map.mp hSi
        obtain ⟨hDecl, huvDec⟩ := List.mem_filter.mp heMem
        obtain ⟨hEdge, hu, hv⟩ := VertexCover.mem_declaredEdges.mp hDecl
        have huv : u ≠ v := of_decide_eq_true huvDec
        have hOr := hCov u hu v hv (Graph.toSimpleGraph_adj.mpr ⟨huv, Or.inl hEdge⟩)
        simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, Finset.mem_toList]
        exact hOr.imp (fun h => ⟨hu, h⟩) (fun h => ⟨hv, h⟩)
    refine exists_congr fun S => and_congr_right fun hSV =>
      and_comm.trans (and_congr_left fun _ => hAllCoverIff S hSV)

/-- `vertexCoverToMaxCoverage` is computable in polynomial time. -/
@[fun_prop]
public theorem computableInPolyTime_vertexCoverToMaxCoverage :
    ComputableInPolyTime vertexCoverToMaxCoverage encVertexCoverInstance encMaxCoverage := by
  unfold vertexCoverToMaxCoverage
  have hGraph : ComputableInPolyTime VertexCoverInstance.graph encVertexCoverInstance encGraph :=
    by fun_prop
  have hVerts : ComputableInPolyTime (fun x : VertexCoverInstance => x.graph.vertices)
      encVertexCoverInstance (encList encNat) := by fun_prop
  have hK : ComputableInPolyTime VertexCoverInstance.k encVertexCoverInstance encNat :=
    by fun_prop
  have hDistLen := unary_to_binary.comp ((length_list encNat).comp
    (Graph.computableInPolyTime_distinctVertices.comp hGraph))
  have hE : ComputableInPolyTime
      (fun x : VertexCoverInstance =>
        (VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2))
      encVertexCoverInstance (encList (encPair encNat encNat)) := by
    refine filterWithInput (VertexCover.computableInPolyTime_declaredEdges.comp hGraph) ?_
    have hPair := snd encVertexCoverInstance (encPair encNat encNat)
    exact (bool_not.comp (decide_eq' (fst' hPair) (snd' hPair))).of_enc_eq fun _ =>
      congrArg encBool (by simp)
  have hDem : ComputableInPolyTime
      (fun x : VertexCoverInstance =>
        ((VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2)).map
          fun e => [e.1, e.2])
      encVertexCoverInstance (encList (encList encNat)) := by
    refine mapWithInput hE ?_
    have hPair := snd encVertexCoverInstance (encPair encNat encNat)
    exact cons' (fst' hPair) (cons' (snd' hPair) (const []))
  have hELen := unary_to_binary.comp ((length_list (encPair encNat encNat)).comp hE)
  have hElse : ComputableInPolyTime _ encVertexCoverInstance encMaxCoverage :=
    equiv_symm_polyTime maxCoverageEquiv (((hVerts.prod hDem).prod hK).prod hELen)
  exact (ite (binary_lt' hDistLen hK)
    (const (⟨[], [], 0, 1⟩ : MaxCoverageInstance)) hElse).of_enc_eq fun _ => rfl

/-- **`MaxCoverage` is `NP`-complete**. -/
public theorem maxCoverage_npComplete : NPComplete encMaxCoverage MaxCoverage :=
  ⟨maxCoverage_mem_NP,
    VertexCover_npHard.trans
      ⟨vertexCoverToMaxCoverage, computableInPolyTime_vertexCoverToMaxCoverage,
        fun x => (vertexCoverToMaxCoverage_mem_iff x).symm⟩⟩

end CslibFrontier.Computability.Complexity
