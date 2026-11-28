module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# W[1]-Hardness of Unary Multidimensional Relaxed Subset Sum

This module defines the parameterized decision problem **Multidimensional Relaxed Subset Sum**
with unary-encoded inputs (`UnaryMRSS`), parameterized by ambient dimension plus subset budget
`k + m`, and proves its `W[1]`-hardness on multi-tape Turing machines under standard Lean axioms:

* `MRSSInstance`, `encUnaryMRSS`, `unaryMRSSParam`, and `UnaryMRSS`: problem definition, unary
  encoding, and combined parameter `k + m`.
* `cliqueToUnaryMRSS`, `computableInPolyTime_cliqueToUnaryMRSS`, `cliqueToUnaryMRSS_mem_iff`,
  `fptReducible_Clique_UnaryMRSS`, and `UnaryMRSS_wHard`: polynomial-time FPT reduction from
  `Cslib.Complexity.Clique` establishing `WHard 1 encUnaryMRSS unaryMRSSParam UnaryMRSS`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### Definition and unary encoding of `UnaryMRSS` -/

/-- An instance `(dim, budget, vectors, target)` of **Multidimensional Relaxed Subset Sum**
(`MRSS`). -/
@[ext]
structure MRSSInstance where
  /-- Ambient dimension `k`. -/
  dim : ℕ
  /-- Subset cardinality budget `m`. -/
  budget : ℕ
  /-- Input collection `S = [s₁, ..., sₙ]` of vectors in `ℕ^k` (entries read via `getD · 0`). -/
  vectors : List (List ℕ)
  /-- Target vector `t ∈ ℕ^k` (entries read via `getD · 0`). -/
  target : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Unary encoding of a list of unary-encoded vectors. -/
abbrev encUnaryVecList : List (List ℕ) ↪ List Bool :=
  encList (encList encUnary)

/-- Unary encoding of `MRSSInstance`. -/
enc_structure encUnaryMRSS : MRSSInstance where
  dim : encUnary,
  budget : encUnary,
  vectors : encUnaryVecList,
  target : (encList encUnary)

attribute [local fun_prop] encUnaryMRSS_dim_polyTime encUnaryMRSS_budget_polyTime
  encUnaryMRSS_vectors_polyTime encUnaryMRSS_target_polyTime encUnaryMRSS_mk_polyTime

/-- Combined parameter `k + m` of `MRSSInstance`. -/
@[expose]
def unaryMRSSParam (I : MRSSInstance) : ℕ :=
  I.dim + I.budget

/-- Equation for `unaryMRSSParam`. -/
theorem unaryMRSSParam_eq (I : MRSSInstance) :
    unaryMRSSParam I = I.dim + I.budget := rfl

/-- **Multidimensional Relaxed Subset Sum** (`UnaryMRSS`): instances
`I = (k, m, S, t)` for which there exists an index subset `J ⊆ Fin |S|` of cardinality at most `m`
whose coordinatewise sum dominates `t` on all `j < k`. -/
@[expose]
def UnaryMRSS : Set MRSSInstance :=
  {I | ∃ J : Finset (Fin I.vectors.length),
    J.card ≤ I.budget ∧
      ∀ j < I.dim, I.target.getD j 0 ≤ ∑ i ∈ J, (I.vectors[i.1]).getD j 0}

/-! ### W[1]-hardness of `UnaryMRSS` from `Clique_wHard` -/

section CliqueToMRSS

private def cliquePairs (q : ℕ) : List (ℕ × ℕ) :=
  (List.range q).flatMap fun a ↦
    ((List.range q).filter fun b ↦ decide (a < b)).map fun b ↦ (a, b)

private def mrssVertVec (q N a u : ℕ) : List ℕ :=
  let pairs := cliquePairs q
  let indV := (List.range q).map fun a' ↦ if a' = a then 1 else 0
  let indE := (List.range pairs.length).map fun _ ↦ 0
  let matchCoords := pairs.flatMap fun pr ↦
    if a = pr.1 then [u, N - u, 0, 0]
    else if a = pr.2 then [0, 0, u, N - u]
    else [0, 0, 0, 0]
  (indV ++ indE) ++ matchCoords

private def mrssEdgeVec (q N p u w : ℕ) : List ℕ :=
  let pairs := cliquePairs q
  let indV := (List.range q).map fun _ ↦ 0
  let indE := (List.range pairs.length).map fun p' ↦ if p' = p then 1 else 0
  let matchCoords := (List.range pairs.length).flatMap fun p' ↦
    if p' = p then [N - u, u, N - w, w] else [0, 0, 0, 0]
  (indV ++ indE) ++ matchCoords

private def mrssTargetVec (q N : ℕ) : List ℕ :=
  let P := (cliquePairs q).length
  (List.replicate (q + P) 1) ++ (List.replicate (4 * P) N)

private def cliqueCap (x : CliqueInstance) : ℕ :=
  min x.graph.distinctVertices.length x.m

private def yesMRSS : MRSSInstance := ⟨0, 0, [], []⟩
private def noMRSS : MRSSInstance := ⟨1, 0, [], [1]⟩

private lemma yesMRSS_mem : yesMRSS ∈ UnaryMRSS :=
  ⟨∅, by decide, fun _ hj ↦ by simp [yesMRSS] at hj⟩

private lemma noMRSS_notMem : noMRSS ∉ UnaryMRSS := by
  rintro ⟨J, hJ, hdom⟩
  have hemp : J = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hJ)
  subst hemp
  have h0 := hdom 0 (by decide)
  exact absurd h0 (by decide)

private def buildCliqueMRSS (G : Graph) (q : ℕ) : MRSSInstance :=
  let V := G.distinctVertices
  let N := V.length
  let pairs := cliquePairs q
  let P := pairs.length
  let vVecs := (List.range q).flatMap fun a ↦
    (List.range N).map fun u ↦ mrssVertVec q N a u
  let adjPairs := (List.range N).flatMap fun u ↦
    ((List.range N).filter fun w ↦ G.adjBool (V.getD u 0) (V.getD w 0)).map fun w ↦ (u, w)
  let eVecs := (List.range P).flatMap fun p ↦
    adjPairs.map fun uw ↦ mrssEdgeVec q N p uw.1 uw.2
  ⟨q + 5 * P, q + P, vVecs ++ eVecs, mrssTargetVec q N⟩

/-- Polynomial-time FPT reduction from `Clique` to `UnaryMRSS`. -/
def cliqueToUnaryMRSS (x : CliqueInstance) : MRSSInstance :=
  let q := cliqueCap x
  if !decide (q = x.m) then noMRSS
  else if decide (q = 0) then yesMRSS
  else if decide (q = 1) then
    if x.graph.distinctVertices.isEmpty then noMRSS else yesMRSS
  else buildCliqueMRSS x.graph q

@[local fun_prop]
private theorem computableInPolyTime_cliqueCap :
    ComputableInPolyTime cliqueCap encCliqueInstance encUnary := by
  unfold cliqueCap
  exact binary_min_unary' (by fun_prop) (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_cliquePairs :
    ComputableInPolyTime cliquePairs encUnary (encList (encPair encUnary encUnary)) := by
  unfold cliquePairs
  refine flatMapWithInput range ?_
  refine mapWithInput (filterWithInput (range.comp (fst _ _)) ?_) ?_
  · exact unary_lt.comp (((snd _ _).comp (fst _ _)).prod (snd _ _))
  · exact ((snd _ _).comp (fst _ _)).prod (snd _ _)

@[local fun_prop]
private theorem computableInPolyTime_mrssVertVec :
    ComputableInPolyTime
      (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ mrssVertVec t.1.1.1 t.1.1.2 t.1.2 t.2)
      (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary)
      (encList encUnary) := by
  set E := encPair (encPair (encPair encUnary encUnary) encUnary) encUnary
  have hq : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ t.1.1.1) E encUnary := by fun_prop
  have hN : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ t.1.1.2) E encUnary := by fun_prop
  have ha : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ t.1.2) E encUnary := by fun_prop
  have hu : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ t.2) E encUnary := by fun_prop
  have hpairs : ComputableInPolyTime
      (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ cliquePairs t.1.1.1)
      E (encList (encPair encUnary encUnary)) :=
    computableInPolyTime_cliquePairs.comp hq
  have hindV : ComputableInPolyTime
      (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ (List.range t.1.1.1).map fun a' ↦
        if decide (a' = t.1.2) then 1 else 0)
      E (encList encUnary) := by
    refine mapWithInput (range.comp hq) ?_
    exact ite ((snd _ _).decide_eq' (ha.comp (fst _ _))) (const 1) (const 0)
  have hindE : ComputableInPolyTime
      (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ (List.range (cliquePairs t.1.1.1).length).map fun _ ↦ 0)
      E (encList encUnary) := by
    refine mapWithInput (range.comp ((length_list (encPair encUnary encUnary)).comp hpairs)) ?_
    exact const 0
  have hmatch : ComputableInPolyTime
      (fun t : ((ℕ × ℕ) × ℕ) × ℕ ↦ (cliquePairs t.1.1.1).flatMap fun pr ↦
        if decide (t.1.2 = pr.1) then [t.2, t.1.1.2 - t.2, 0, 0]
        else if decide (t.1.2 = pr.2) then [0, 0, t.2, t.1.1.2 - t.2]
        else [0, 0, 0, 0])
      E (encList encUnary) := by
    refine flatMapWithInput hpairs ?_
    set F := encPair E (encPair encUnary encUnary)
    have hu' : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.2) F encUnary := hu.comp (fst _ _)
    have hsub' : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.1.1.2 - s.1.2) F encUnary :=
      unary_sub.comp ((hN.comp (fst _ _)).prod hu')
    have hnil : ComputableInPolyTime
        (fun _ : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ ([] : List ℕ)) F (encList encUnary) := const []
    have hl1 : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ [s.1.2, s.1.1.1.2 - s.1.2, 0, 0])
        F (encList encUnary) :=
      hu'.cons' (hsub'.cons' ((const 0).cons' ((const 0).cons' hnil)))
    have hl2 : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ [0, 0, s.1.2, s.1.1.1.2 - s.1.2])
        F (encList encUnary) :=
      (const 0).cons' ((const 0).cons' (hu'.cons' (hsub'.cons' hnil)))
    have hc1 : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ decide (s.1.1.2 = s.2.1)) F encBool :=
      (ha.comp (fst _ _)).decide_eq' ((fst _ _).comp (snd _ _))
    have hc2 : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) ↦ decide (s.1.1.2 = s.2.2)) F encBool :=
      (ha.comp (fst _ _)).decide_eq' ((snd _ _).comp (snd _ _))
    exact ite hc1 hl1 (ite hc2 hl2 (const ([0, 0, 0, 0] : List ℕ)))
  exact (listAppend' (listAppend' hindV hindE) hmatch).of_enc_eq fun t ↦
    congrArg (encList encUnary) (by simp [mrssVertVec])

@[local fun_prop]
private theorem computableInPolyTime_mrssEdgeVec :
    ComputableInPolyTime
      (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ mrssEdgeVec t.1.1.1.1 t.1.1.1.2 t.1.1.2 t.1.2 t.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary)
      (encList encUnary) := by
  set E := encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encUnary
  have hq : ComputableInPolyTime (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ t.1.1.1.1) E encUnary := by
    fun_prop
  have hN : ComputableInPolyTime (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ t.1.1.1.2) E encUnary := by
    fun_prop
  have hp : ComputableInPolyTime (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ t.1.1.2) E encUnary := by
    fun_prop
  have hu : ComputableInPolyTime (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ t.1.2) E encUnary := by
    fun_prop
  have hw : ComputableInPolyTime (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ t.2) E encUnary := by
    fun_prop
  have hP : ComputableInPolyTime
      (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ (cliquePairs t.1.1.1.1).length) E encUnary :=
    (length_list (encPair encUnary encUnary)).comp (computableInPolyTime_cliquePairs.comp hq)
  have hindV : ComputableInPolyTime
      (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦ (List.range t.1.1.1.1).map fun _ ↦ 0)
      E (encList encUnary) :=
    mapWithInput (range.comp hq) (const 0)
  have hindE : ComputableInPolyTime
      (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦
        (List.range (cliquePairs t.1.1.1.1).length).map fun p' ↦
          if decide (p' = t.1.1.2) then 1 else 0)
      E (encList encUnary) := by
    refine mapWithInput (range.comp hP) ?_
    exact ite ((snd _ _).decide_eq' (hp.comp (fst _ _))) (const 1) (const 0)
  have hmatch : ComputableInPolyTime
      (fun t : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ ↦
        (List.range (cliquePairs t.1.1.1.1).length).flatMap fun p' ↦
          if decide (p' = t.1.1.2) then [t.1.1.1.2 - t.1.2, t.1.2, t.1.1.1.2 - t.2, t.2]
          else [0, 0, 0, 0])
      E (encList encUnary) := by
    refine flatMapWithInput (range.comp hP) ?_
    set F := encPair E encUnary
    have hu' := hu.comp (fst E encUnary)
    have hw' := hw.comp (fst E encUnary)
    have hNu := unary_sub.comp ((hN.comp (fst E encUnary)).prod hu')
    have hNw := unary_sub.comp ((hN.comp (fst E encUnary)).prod hw')
    have hnil : ComputableInPolyTime
        (fun _ : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ ↦ ([] : List ℕ)) F (encList encUnary) := const []
    have hl : ComputableInPolyTime _ F (encList encUnary) :=
      hNu.cons' (hu'.cons' (hNw.cons' (hw'.cons' hnil)))
    exact ite ((snd E encUnary).decide_eq' (hp.comp (fst E encUnary))) hl
      (const ([0, 0, 0, 0] : List ℕ))
  exact (listAppend' (listAppend' hindV hindE) hmatch).of_enc_eq fun t ↦
    congrArg (encList encUnary) (by simp [mrssEdgeVec])

private theorem computableInPolyTime_buildCliqueMRSS :
    ComputableInPolyTime (fun p : Graph × ℕ ↦ buildCliqueMRSS p.1 p.2)
      (encPair encGraph encUnary) encUnaryMRSS := by
  set E := encPair encGraph encUnary
  have hG : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1) E encGraph := fst _ _
  have hq : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2) E encUnary := snd _ _
  have hV : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1.distinctVertices)
      E (encList encNat) := Graph.computableInPolyTime_distinctVertices.comp hG
  have hN : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1.distinctVertices.length)
      E encUnary := (length_list encNat).comp hV
  have hP : ComputableInPolyTime (fun p : Graph × ℕ ↦ (cliquePairs p.2).length) E encUnary :=
    (length_list (encPair encUnary encUnary)).comp (computableInPolyTime_cliquePairs.comp hq)
  have hm5 : ComputableInPolyTime (fun n : ℕ ↦ 5 * n) encUnary encUnary := by fun_prop
  have hm4 : ComputableInPolyTime (fun n : ℕ ↦ 4 * n) encUnary encUnary := by fun_prop
  have hdim : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ p.2 + 5 * (cliquePairs p.2).length) E encUnary :=
    unary_add.comp (hq.prod (hm5.comp hP))
  have hbud : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ p.2 + (cliquePairs p.2).length) E encUnary :=
    unary_add.comp (hq.prod hP)
  have hvVecs : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ (List.range p.2).flatMap fun a ↦
        (List.range p.1.distinctVertices.length).map fun u ↦
          mrssVertVec p.2 p.1.distinctVertices.length a u)
      E encUnaryVecList := by
    refine flatMapWithInput (range.comp hq) ?_
    refine mapWithInput (range.comp (hN.comp (fst _ _))) ?_
    exact computableInPolyTime_mrssVertVec.comp
      ((((hq.comp ((fst _ _).comp (fst _ _))).prod
        (hN.comp ((fst _ _).comp (fst _ _)))).prod
        ((snd _ _).comp (fst _ _))).prod (snd _ _))
  have hadjPairs : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ (List.range p.1.distinctVertices.length).flatMap fun u ↦
        ((List.range p.1.distinctVertices.length).filter fun w ↦
          p.1.adjBool (p.1.distinctVertices.getD u 0) (p.1.distinctVertices.getD w 0)).map
          fun w ↦ (u, w))
      E (encList (encPair encUnary encUnary)) := by
    refine flatMapWithInput (range.comp hN) ?_
    have hflt : ComputableInPolyTime
        (fun s : (Graph × ℕ) × ℕ ↦ (List.range s.1.1.distinctVertices.length).filter fun w ↦
          s.1.1.adjBool (s.1.1.distinctVertices.getD s.2 0) (s.1.1.distinctVertices.getD w 0))
        (encPair E encUnary) (encList encUnary) := by
      set F1 := encPair E encUnary
      refine filterWithInput (range.comp (hN.comp (fst E encUnary))) ?_
      have hvu := listGetDWithInput (hV.comp ((fst E encUnary).comp (fst F1 encUnary)))
        ((snd E encUnary).comp (fst F1 encUnary)) 0
      have hvw := listGetDWithInput (hV.comp ((fst E encUnary).comp (fst F1 encUnary)))
        (snd F1 encUnary) 0
      exact Graph.computableInPolyTime_adjBool_comp
        (hG.comp ((fst E encUnary).comp (fst F1 encUnary))) hvu hvw
    refine mapWithInput hflt ?_
    exact ((snd _ _).comp (fst _ _)).prod (snd _ _)
  have heVecs : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ (List.range (cliquePairs p.2).length).flatMap fun idx ↦
        ((List.range p.1.distinctVertices.length).flatMap fun u ↦
          ((List.range p.1.distinctVertices.length).filter fun w ↦
            p.1.adjBool (p.1.distinctVertices.getD u 0) (p.1.distinctVertices.getD w 0)).map
            fun w ↦ (u, w)).map fun uw ↦
          mrssEdgeVec p.2 p.1.distinctVertices.length idx uw.1 uw.2)
      E encUnaryVecList := by
    refine flatMapWithInput (range.comp hP) ?_
    refine mapWithInput (hadjPairs.comp (fst _ _)) ?_
    exact computableInPolyTime_mrssEdgeVec.comp
      (((((hq.comp ((fst _ _).comp (fst _ _))).prod
        (hN.comp ((fst _ _).comp (fst _ _)))).prod
        ((snd _ _).comp (fst _ _))).prod
        ((fst _ _).comp (snd _ _))).prod ((snd _ _).comp (snd _ _)))
  have htgt : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ mrssTargetVec p.2 p.1.distinctVertices.length)
      E (encList encUnary) :=
    listAppend' (replicate hbud (const 1)) (replicate (hm4.comp hP) hN)
  exact (encUnaryMRSS_mk_polyTime hdim hbud (listAppend' hvVecs heVecs) htgt).of_enc_eq
    fun _ ↦ rfl

section CliqueToMRSSPolyTime

attribute [local irreducible] cliqueCap yesMRSS noMRSS buildCliqueMRSS

@[fun_prop]
theorem computableInPolyTime_cliqueToUnaryMRSS :
    ComputableInPolyTime cliqueToUnaryMRSS encCliqueInstance encUnaryMRSS := by
  have hG : ComputableInPolyTime CliqueInstance.graph encCliqueInstance encGraph := by fun_prop
  have hm : ComputableInPolyTime CliqueInstance.m encCliqueInstance encNat := by fun_prop
  have hcap := computableInPolyTime_cliqueCap
  have hqm : ComputableInPolyTime (fun x : CliqueInstance ↦ !decide (cliqueCap x = x.m))
      encCliqueInstance encBool :=
    bool_not.comp ((unary_to_binary.comp hcap).decide_eq' hm)
  have hq0 : ComputableInPolyTime (fun x : CliqueInstance ↦ decide (cliqueCap x = 0))
      encCliqueInstance encBool := hcap.decide_eq' (const 0)
  have hq1 : ComputableInPolyTime (fun x : CliqueInstance ↦ decide (cliqueCap x = 1))
      encCliqueInstance encBool := hcap.decide_eq' (const 1)
  have hemp : ComputableInPolyTime
      (fun x : CliqueInstance ↦ x.graph.distinctVertices.isEmpty)
      encCliqueInstance encBool :=
    (listIsEmpty' encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hG)
  have hbuild : ComputableInPolyTime
      (fun x : CliqueInstance ↦ buildCliqueMRSS x.graph (cliqueCap x))
      encCliqueInstance encUnaryMRSS :=
    computableInPolyTime_buildCliqueMRSS.comp (hG.prod hcap)
  unfold cliqueToUnaryMRSS
  exact ite hqm (const noMRSS)
    (ite hq0 (const yesMRSS)
      (ite hq1 (ite hemp (const noMRSS) (const yesMRSS)) hbuild))

end CliqueToMRSSPolyTime

private lemma length_cliquePairs_le (q : ℕ) : (cliquePairs q).length ≤ q * q := by
  unfold cliquePairs
  rw [List.length_flatMap]
  calc ((List.range q).map fun a ↦
        (((List.range q).filter fun b ↦ decide (a < b)).map fun b ↦ (a, b)).length).sum
      ≤ ((List.range q).map fun a ↦
          (((List.range q).filter fun b ↦ decide (a < b)).map fun b ↦ (a, b)).length).length • q :=
          List.sum_le_length_nsmul _ q fun x hx ↦ by
            obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
            rw [List.length_map]
            exact (List.length_filter_le _ _).trans (by simp)
    _ = q * q := by simp [smul_eq_mul]

private lemma mem_cliquePairs_iff {q a b : ℕ} :
    (a, b) ∈ cliquePairs q ↔ a < b ∧ b < q := by
  simp only [cliquePairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Prod.mk.injEq]
  exact ⟨by rintro ⟨a', ha', b', ⟨hb', hab⟩, rfl, rfl⟩; exact ⟨hab, hb'⟩,
    fun ⟨hab, hb⟩ ↦ ⟨a, Nat.lt_trans hab hb, b, ⟨hb, hab⟩, rfl, rfl⟩⟩

private lemma getD_append_left' {α : Type*} {l₁ l₂ : List α} {j : ℕ}
    (hj : j < l₁.length) (d : α) :
    (l₁ ++ l₂).getD j d = l₁.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

private lemma getD_append_right' {α : Type*} {l₁ l₂ : List α} {j : ℕ}
    (hj : l₁.length ≤ j) (d : α) :
    (l₁ ++ l₂).getD j d = l₂.getD (j - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hj]

private lemma flatMap_four_getD {α : Type*} (l : List α) (f : α → List ℕ)
    (hf : ∀ x ∈ l, (f x).length = 4) {p r : ℕ} (hp : p < l.length) (hr : r < 4) :
    (l.flatMap f).getD (4 * p + r) 0 = (f l[p]).getD r 0 := by
  induction l generalizing p with
  | nil => simp at hp
  | cons x xs ih =>
    have hx4 : (f x).length = 4 := hf x List.mem_cons_self
    have hxs4 : ∀ y ∈ xs, (f y).length = 4 := fun y hy ↦ hf y (List.mem_cons_of_mem x hy)
    cases p with
    | zero =>
      rw [List.flatMap_cons, getD_append_left' (by omega), Nat.mul_zero, Nat.zero_add]
      rfl
    | succ p' =>
      have hp' : p' < xs.length := by simp only [List.length_cons] at hp; omega
      rw [List.flatMap_cons, getD_append_right' (by omega),
        show 4 * (p' + 1) + r - (f x).length = 4 * p' + r by omega, List.getElem_cons_succ]
      exact ih hxs4 hp'

private lemma mrssVertVec_indV (q N a u j : ℕ) (hj : j < q) :
    (mrssVertVec q N a u).getD j 0 = if j = a then 1 else 0 := by
  unfold mrssVertVec
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp [hj]),
    List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]

private lemma mrssVertVec_indE (q N a u p : ℕ) (hp : p < (cliquePairs q).length) :
    (mrssVertVec q N a u).getD (q + p) 0 = 0 := by
  unfold mrssVertVec
  rw [getD_append_left' (by simp; omega), getD_append_right' (by simp),
    List.length_map, List.length_range, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simp [hp]), List.getElem_map]

private lemma mrssVertVec_match (q N a u p r : ℕ) (hp : p < (cliquePairs q).length) (hr : r < 4) :
    (mrssVertVec q N a u).getD (q + (cliquePairs q).length + (4 * p + r)) 0 =
      if a = (cliquePairs q)[p].1 then ([u, N - u, 0, 0] : List ℕ).getD r 0
      else if a = (cliquePairs q)[p].2 then ([0, 0, u, N - u] : List ℕ).getD r 0
      else 0 := by
  unfold mrssVertVec
  have hlen12 : (((List.range q).map fun a' ↦ if a' = a then 1 else 0) ++
      (List.range (cliquePairs q).length).map fun _ ↦ 0).length = q + (cliquePairs q).length := by
    simp
  rw [getD_append_right' (by rw [hlen12]; omega), hlen12, Nat.add_sub_cancel_left,
    flatMap_four_getD (cliquePairs q) _ (fun pr _ ↦ by split_ifs <;> simp) hp hr]
  split_ifs
  · rfl
  · rfl
  · have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr_cases with rfl | rfl | rfl | rfl <;> rfl

private lemma mrssEdgeVec_indV (q N p u w j : ℕ) (hj : j < q) :
    (mrssEdgeVec q N p u w).getD j 0 = 0 := by
  unfold mrssEdgeVec
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp [hj]),
    List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map]

private lemma mrssEdgeVec_indE (q N p u w p' : ℕ) (hp' : p' < (cliquePairs q).length) :
    (mrssEdgeVec q N p u w).getD (q + p') 0 = if p' = p then 1 else 0 := by
  unfold mrssEdgeVec
  rw [getD_append_left' (by simp; omega), getD_append_right' (by simp),
    List.length_map, List.length_range, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simp [hp']), List.getElem_map, List.getElem_range]

private lemma mrssEdgeVec_match (q N p u w p' r : ℕ)
    (hp' : p' < (cliquePairs q).length) (hr : r < 4) :
    (mrssEdgeVec q N p u w).getD (q + (cliquePairs q).length + (4 * p' + r)) 0 =
      if p' = p then ([N - u, u, N - w, w] : List ℕ).getD r 0 else 0 := by
  unfold mrssEdgeVec
  have hlen12 : (((List.range q).map fun _ ↦ 0) ++
      (List.range (cliquePairs q).length).map fun idx ↦ if idx = p then 1 else 0).length =
      q + (cliquePairs q).length := by simp
  have hrl : p' < (List.range (cliquePairs q).length).length := by simp [hp']
  rw [getD_append_right' (by rw [hlen12]; omega), hlen12, Nat.add_sub_cancel_left,
    flatMap_four_getD (List.range (cliquePairs q).length) _
      (fun _ _ ↦ by split_ifs <;> simp) hrl hr, List.getElem_range]
  split_ifs
  · rfl
  · have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr_cases with rfl | rfl | rfl | rfl <;> rfl

private lemma mrssTargetVec_ind (q N j : ℕ) (hj : j < q + (cliquePairs q).length) :
    (mrssTargetVec q N).getD j 0 = 1 := by
  unfold mrssTargetVec
  rw [getD_append_left' (by simp [hj]), List.getD_eq_getElem _ _ (by simp [hj]),
    List.getElem_replicate]

private lemma mrssTargetVec_match (q N k : ℕ) (hk : k < 4 * (cliquePairs q).length) :
    (mrssTargetVec q N).getD (q + (cliquePairs q).length + k) 0 = N := by
  unfold mrssTargetVec
  rw [getD_append_right' (by simp), List.length_replicate, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

private lemma buildCliqueMRSS_mem_iff (G : Graph) {q : ℕ} (_hq2 : 2 ≤ q)
    (_hqN : q ≤ G.distinctVertices.length) :
    (⟨G, q⟩ : CliqueInstance) ∈ Clique ↔ buildCliqueMRSS G q ∈ UnaryMRSS := by
  classical
  set V := G.distinctVertices
  set N := V.length
  set pairs := cliquePairs q
  set P := pairs.length
  set I := buildCliqueMRSS G q
  have hItgt : I.target = mrssTargetVec q N := rfl
  have hnodupV : V.Nodup := G.nodup_distinctVertices
  have hgetV_mem (u : ℕ) (hu : u < N) : V.getD u 0 ∈ G.vertices := by
    rw [List.getD_eq_getElem _ _ hu, ← Graph.mem_distinctVertices]
    exact List.getElem_mem hu
  have hvec_cases (v : List ℕ) (hv : v ∈ I.vectors) :
      (∃ a < q, ∃ u < N, v = mrssVertVec q N a u) ∨
      (∃ p < P, ∃ u < N, ∃ w < N,
        G.toSimpleGraph.Adj (V.getD u 0) (V.getD w 0) ∧ v = mrssEdgeVec q N p u w) := by
    simp only [I, buildCliqueMRSS, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_filter, List.mem_range, Graph.adjBool_eq_true_iff] at hv
    rcases hv with ⟨a, ha, u, hu, rfl⟩ | ⟨p, hp, uw, ⟨u, hu, w, ⟨hw, hadj⟩, huw⟩, rfl⟩
    · exact Or.inl ⟨a, ha, u, hu, rfl⟩
    · subst huw
      exact Or.inr ⟨p, hp, u, hu, w, hw, hadj, rfl⟩
  constructor
  · -- `[⇒]` From a `q`-clique `S` in `G` to a subset `J` of `q + P` vectors
    rw [mem_Clique_iff]
    rintro ⟨S, hSV, hScl, hScard⟩
    dsimp only at hSV hScl hScard
    -- Map `S` into indices `< N` via `IS = (Finset.range N).filter (V.getD · 0 ∈ S)`
    let IS : Finset ℕ := (Finset.range N).filter fun u ↦ V.getD u 0 ∈ S
    have hIS_card : IS.card = q := by
      rw [← hScard, ← Fintype.card_coe, ← Fintype.card_coe]
      let emb : IS → S := fun ⟨u, hu⟩ ↦ ⟨V.getD u 0, (Finset.mem_filter.mp hu).2⟩
      exact Fintype.card_of_bijective (f := emb) ⟨fun x y hxy ↦ by
        have hv_eq : V.getD x.1 0 = V.getD y.1 0 := congrArg Subtype.val hxy
        have hx_lt : x.1 < N := Finset.mem_range.mp (Finset.mem_filter.mp x.2).1
        have hy_lt : y.1 < N := Finset.mem_range.mp (Finset.mem_filter.mp y.2).1
        rw [List.getD_eq_getElem _ _ hx_lt, List.getD_eq_getElem _ _ hy_lt] at hv_eq
        exact Subtype.ext ((List.Nodup.getElem_inj_iff hnodupV).mp hv_eq),
        fun ⟨w, hwS⟩ ↦ by
          obtain ⟨u, hu_lt, rfl⟩ :=
            List.getElem_of_mem (Graph.mem_distinctVertices.mpr (hSV w hwS))
          have hget_u : V.getD u 0 = V[u] := List.getD_eq_getElem _ _ hu_lt
          exact ⟨⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu_lt, hget_u ▸ hwS⟩⟩,
            Subtype.ext hget_u⟩⟩
    let L_IS := IS.toList
    have hL_len : L_IS.length = q := by rw [Finset.length_toList, hIS_card]
    have hL_nodup : L_IS.Nodup := Finset.nodup_toList IS
    let uOf (a : ℕ) : ℕ := L_IS.getD a 0
    have hu_mem_IS (a : ℕ) (ha : a < q) : uOf a ∈ IS := by
      dsimp [uOf]
      rw [List.getD_eq_getElem _ _ (hL_len ▸ ha), ← Finset.mem_toList]
      exact List.getElem_mem (hL_len ▸ ha)
    have hu_lt (a : ℕ) (ha : a < q) : uOf a < N :=
      Finset.mem_range.mp (Finset.mem_filter.mp (hu_mem_IS a ha)).1
    have hu_adj {a b : ℕ} (ha : a < q) (hb : b < q) (hne : a ≠ b) :
        G.toSimpleGraph.Adj (V.getD (uOf a) 0) (V.getD (uOf b) 0) := by
      have haS := (Finset.mem_filter.mp (hu_mem_IS a ha)).2
      have hbS := (Finset.mem_filter.mp (hu_mem_IS b hb)).2
      have hu_ne : uOf a ≠ uOf b := by
        dsimp [uOf]
        rw [List.getD_eq_getElem _ _ (hL_len ▸ ha), List.getD_eq_getElem _ _ (hL_len ▸ hb)]
        exact fun h ↦ hne ((List.Nodup.getElem_inj_iff hL_nodup).mp h)
      have hv_ne : V.getD (uOf a) 0 ≠ V.getD (uOf b) 0 := by
        rw [List.getD_eq_getElem _ _ (hu_lt a ha), List.getD_eq_getElem _ _ (hu_lt b hb)]
        exact fun h ↦ hu_ne ((List.Nodup.getElem_inj_iff hnodupV).mp h)
      exact hScl haS hbS hv_ne
    -- Pick one index in `Fin I.vectors.length` for each `a < q` and each `p < P`
    have hv_in (a : ℕ) (ha : a < q) : mrssVertVec q N a (uOf a) ∈ I.vectors := by
      simp only [I, buildCliqueMRSS, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range]
      exact Or.inl ⟨a, ha, uOf a, hu_lt a ha, rfl⟩
    have he_in (p : ℕ) (hp : p < P) :
        mrssEdgeVec q N p (uOf pairs[p].1) (uOf pairs[p].2) ∈ I.vectors := by
      obtain ⟨hab, hb⟩ := mem_cliquePairs_iff.mp (List.getElem_mem hp)
      have ha : pairs[p].1 < q := Nat.lt_trans hab hb
      simp only [I, buildCliqueMRSS, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_filter, List.mem_range, Graph.adjBool_eq_true_iff]
      exact Or.inr ⟨p, hp, (uOf pairs[p].1, uOf pairs[p].2),
        ⟨uOf pairs[p].1, hu_lt _ ha, uOf pairs[p].2, ⟨hu_lt _ hb,
          hu_adj ha hb (Nat.ne_of_lt hab)⟩, rfl⟩, rfl⟩
    let idxV (a : Fin q) : Fin I.vectors.length :=
      ⟨I.vectors.idxOf (mrssVertVec q N a.1 (uOf a.1)),
        List.idxOf_lt_length_iff.mpr (hv_in a.1 a.2)⟩
    let idxE (p : Fin P) : Fin I.vectors.length :=
      ⟨I.vectors.idxOf (mrssEdgeVec q N p.1 (uOf pairs[p.1].1) (uOf pairs[p.1].2)),
        List.idxOf_lt_length_iff.mpr (he_in p.1 p.2)⟩
    have hidxV_vec (a : Fin q) : I.vectors[(idxV a).1] = mrssVertVec q N a.1 (uOf a.1) :=
      List.getElem_idxOf _
    have hidxE_vec (p : Fin P) :
        I.vectors[(idxE p).1] = mrssEdgeVec q N p.1 (uOf pairs[p.1].1) (uOf pairs[p.1].2) :=
      List.getElem_idxOf _
    have hinjV : Function.Injective idxV := fun a₁ a₂ h ↦ by
      have hv := (hidxV_vec a₁).symm.trans ((congrArg (I.vectors[·.1]) h).trans (hidxV_vec a₂))
      have hc := congrArg (fun v ↦ v.getD a₁.1 0) hv
      rw [mrssVertVec_indV q N a₁.1 _ a₁.1 a₁.2, mrssVertVec_indV q N a₂.1 _ a₁.1 a₁.2] at hc
      by_contra hne
      have hne' : a₁.1 ≠ a₂.1 := Fin.val_ne_of_ne hne
      simp [hne'] at hc
    have hinjE : Function.Injective idxE := fun p₁ p₂ h ↦ by
      have hv := (hidxE_vec p₁).symm.trans ((congrArg (I.vectors[·.1]) h).trans (hidxE_vec p₂))
      have hc := congrArg (fun v ↦ v.getD (q + p₁.1) 0) hv
      rw [mrssEdgeVec_indE q N p₁.1 _ _ p₁.1 p₁.2,
        mrssEdgeVec_indE q N p₂.1 _ _ p₁.1 p₁.2] at hc
      by_contra hne
      have hne' : p₁.1 ≠ p₂.1 := Fin.val_ne_of_ne hne
      simp [hne'] at hc
    let JV : Finset (Fin I.vectors.length) := Finset.univ.image idxV
    let JE : Finset (Fin I.vectors.length) := Finset.univ.image idxE
    have hdisj : Disjoint JV JE := by
      refine Finset.disjoint_left.mpr fun idx h₁ h₂ ↦ ?_
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨p, _, heq⟩ := Finset.mem_image.mp h₂
      have hv := (hidxE_vec p).symm.trans ((congrArg (I.vectors[·.1]) heq).trans (hidxV_vec a))
      have hc := congrArg (fun v ↦ v.getD a.1 0) hv
      rw [mrssEdgeVec_indV q N _ _ _ a.1 a.2, mrssVertVec_indV q N a.1 _ a.1 a.2] at hc
      simp at hc
    refine ⟨JV ∪ JE, ?_, fun j hj ↦ ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjV,
        Finset.card_image_of_injective _ hinjE, Finset.card_fin, Finset.card_fin]
      exact le_rfl
    · rw [Finset.sum_union hdisj, Finset.sum_image fun x _ y _ h ↦ hinjV h,
        Finset.sum_image fun x _ y _ h ↦ hinjE h]
      have hj_dim : j < q + 5 * P := hj
      rw [hItgt]
      by_cases hj1 : j < q
      · rw [mrssTargetVec_ind q N j (by omega)]
        have hVsum : (∑ a : Fin q, (I.vectors[(idxV a).1]).getD j 0) = 1 := by
          simp_rw [hidxV_vec, mrssVertVec_indV q N _ _ j hj1]
          have : (∑ a : Fin q, if j = a.1 then 1 else 0) =
              ∑ a : Fin q, if a = ⟨j, hj1⟩ then 1 else 0 :=
            Finset.sum_congr rfl fun a _ ↦ by simp [Fin.ext_iff, eq_comm]
          rw [this]
          simp
        omega
      · by_cases hj2 : j < q + P
        · rw [mrssTargetVec_ind q N j hj2]
          let p₀ := j - q
          have hp₀ : p₀ < P := by omega
          have hj_eq : j = q + p₀ := by omega
          rw [hj_eq]
          have hEsum : (∑ p : Fin P, (I.vectors[(idxE p).1]).getD (q + p₀) 0) = 1 := by
            simp_rw [hidxE_vec, mrssEdgeVec_indE q N _ _ _ p₀ hp₀]
            have : (∑ p : Fin P, if p₀ = p.1 then 1 else 0) =
                ∑ p : Fin P, if p = ⟨p₀, hp₀⟩ then 1 else 0 :=
              Finset.sum_congr rfl fun p _ ↦ by simp [Fin.ext_iff, eq_comm]
            rw [this]
            simp
          omega
        · let k := j - (q + P)
          have hk : k < 4 * P := by omega
          have hj_eq : j = q + (cliquePairs q).length + k := by change j = q + P + k; omega
          have hk' : k < 4 * (cliquePairs q).length := hk
          rw [hj_eq, mrssTargetVec_match q N k hk']
          let p₀ := k / 4
          let r₀ := k % 4
          have hp₀ : p₀ < P := by omega
          have hp₀' : p₀ < (cliquePairs q).length := hp₀
          have hr₀ : r₀ < 4 := by omega
          have hk_eq : k = 4 * p₀ + r₀ := by omega
          rw [hk_eq]
          obtain ⟨hab, hb⟩ := mem_cliquePairs_iff.mp (List.getElem_mem hp₀')
          have ha : (cliquePairs q)[p₀].1 < q := Nat.lt_trans hab hb
          let aF : Fin q := ⟨(cliquePairs q)[p₀].1, ha⟩
          let bF : Fin q := ⟨(cliquePairs q)[p₀].2, hb⟩
          have hab_ne : aF ≠ bF := fun h ↦ (Nat.ne_of_lt hab) (congrArg Fin.val h)
          have hVsum : (∑ a : Fin q,
              (I.vectors[(idxV a).1]).getD (q + (cliquePairs q).length + (4 * p₀ + r₀)) 0) =
              ([uOf aF.1, N - uOf aF.1, 0, 0] : List ℕ).getD r₀ 0 +
                ([0, 0, uOf bF.1, N - uOf bF.1] : List ℕ).getD r₀ 0 := by
            simp_rw [hidxV_vec, mrssVertVec_match q N _ _ p₀ r₀ hp₀' hr₀]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ aF),
              ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab_ne.symm, Finset.mem_univ bF⟩)]
            have hrest : ∑ a ∈ (Finset.univ.erase aF).erase bF,
                (if a.1 = (cliquePairs q)[p₀].1 then
                  ([uOf a.1, N - uOf a.1, 0, 0] : List ℕ).getD r₀ 0
                 else if a.1 = (cliquePairs q)[p₀].2 then
                  ([0, 0, uOf a.1, N - uOf a.1] : List ℕ).getD r₀ 0
                 else 0) = 0 := by
              refine Finset.sum_eq_zero fun a ha_mem ↦ ?_
              have hne_b : a ≠ bF := (Finset.mem_erase.mp ha_mem).1
              have hne_a : a ≠ aF := (Finset.mem_erase.mp (Finset.mem_erase.mp ha_mem).2).1
              have h1 : a.1 ≠ (cliquePairs q)[p₀].1 := fun h ↦ hne_a (Fin.ext h)
              have h2 : a.1 ≠ (cliquePairs q)[p₀].2 := fun h ↦ hne_b (Fin.ext h)
              simp [h1, h2]
            rw [hrest, add_zero]
            have h1 : bF.1 ≠ (cliquePairs q)[p₀].1 := Nat.ne_of_gt hab
            simp [aF, bF, h1]
          have hEsum : (∑ p : Fin P,
              (I.vectors[(idxE p).1]).getD (q + (cliquePairs q).length + (4 * p₀ + r₀)) 0) =
              ([N - uOf aF.1, uOf aF.1, N - uOf bF.1, uOf bF.1] : List ℕ).getD r₀ 0 := by
            simp_rw [hidxE_vec, mrssEdgeVec_match q N _ _ _ p₀ r₀ hp₀' hr₀]
            have : (∑ p : Fin P,
                if p₀ = p.1 then
                  ([N - uOf pairs[p.1].1, uOf pairs[p.1].1,
                    N - uOf pairs[p.1].2, uOf pairs[p.1].2] : List ℕ).getD r₀ 0
                else 0) =
                ∑ p : Fin P,
                  if p = ⟨p₀, hp₀⟩ then
                    ([N - uOf aF.1, uOf aF.1, N - uOf bF.1, uOf bF.1] : List ℕ).getD r₀ 0
                  else 0 := by
              refine Finset.sum_congr rfl fun p _ ↦ ?_
              by_cases hp_eq : p = ⟨p₀, hp₀⟩
              · subst hp_eq; simp [aF, bF, pairs]
              · have hne : p₀ ≠ p.1 := fun h ↦ hp_eq (Fin.ext h.symm)
                simp [hp_eq, hne]
            rw [this]
            simp
          rw [hVsum, hEsum]
          have hua : uOf aF.1 < N := hu_lt aF.1 ha
          have hub : uOf bF.1 < N := hu_lt bF.1 hb
          have hr_cases : r₀ = 0 ∨ r₀ = 1 ∨ r₀ = 2 ∨ r₀ = 3 := by omega
          rcases hr_cases with hr0 | hr0 | hr0 | hr0 <;> (rw [hr0]; simp; omega)
  · -- `[⇐]` From a subset `J` of `≤ q + P` vectors to a `q`-clique in `G`
    rintro ⟨J, hJcard, hJdom⟩
    have hbud : I.budget = q + P := rfl
    rw [hbud] at hJcard
    -- Each vector in `I.vectors` has a unique nonzero indicator coordinate in `0 .. q + P - 1`
    have hvec_unique_ind (i : Fin I.vectors.length) :
        ∃! r, r < q + P ∧ 0 < (I.vectors[i.1]).getD r 0 := by
      rcases hvec_cases I.vectors[i.1] (List.getElem_mem i.2) with ⟨a, ha, u, _, hv⟩ |
          ⟨p, hp, u, _, w, _, _, hv⟩
      · refine ⟨a, ⟨by omega, by rw [hv, mrssVertVec_indV q N a u a ha]; simp⟩,
          fun r ⟨hr, hpos⟩ ↦ ?_⟩
        rw [hv] at hpos
        by_cases hrq : r < q
        · rw [mrssVertVec_indV q N a u r hrq] at hpos
          by_contra hne; simp [hne] at hpos
        · have hrp : r - q < P := by omega
          have hreq : r = q + (r - q) := by omega
          rw [hreq, mrssVertVec_indE q N a u (r - q) hrp] at hpos
          omega
      · refine ⟨q + p, ⟨by omega, by rw [hv, mrssEdgeVec_indE q N p u w p hp]; simp⟩,
          fun r ⟨hr, hpos⟩ ↦ ?_⟩
        rw [hv] at hpos
        by_cases hrq : r < q
        · rw [mrssEdgeVec_indV q N p u w r hrq] at hpos; omega
        · have hrp : r - q < P := by omega
          have hreq : r = q + (r - q) := by omega
          rw [hreq, mrssEdgeVec_indE q N p u w (r - q) hrp] at hpos
          by_contra hne
          have hne' : r - q ≠ p := by omega
          simp [hne'] at hpos
    let Jg (r : ℕ) : Finset (Fin I.vectors.length) :=
      J.filter fun i ↦ 0 < (I.vectors[i.1]).getD r 0
    have hJg_pos (r : ℕ) (hr : r < q + P) : 1 ≤ (Jg r).card := by
      have hdom_r := hJdom r (show r < q + 5 * P by omega)
      rw [hItgt, mrssTargetVec_ind q N r hr] at hdom_r
      by_contra h0
      have hemp : Jg r = ∅ := Finset.card_eq_zero.mp (by omega)
      have hsum0 : ∑ i ∈ J, (I.vectors[i.1]).getD r 0 = 0 := by
        refine Finset.sum_eq_zero fun i hiJ ↦ ?_
        by_contra hnz
        have hmem : i ∈ Jg r := Finset.mem_filter.mpr ⟨hiJ, Nat.pos_of_ne_zero hnz⟩
        rw [hemp] at hmem; exact Finset.notMem_empty i hmem
      omega
    have hJg_disj : ∀ r₁ ∈ Finset.range (q + P), ∀ r₂ ∈ Finset.range (q + P),
        r₁ ≠ r₂ → Disjoint (Jg r₁) (Jg r₂) := by
      intro r₁ hr₁ r₂ hr₂ hne
      refine Finset.disjoint_left.mpr fun i hi₁ hi₂ ↦ hne ?_
      obtain ⟨_, _, huniq⟩ := hvec_unique_ind i
      have e₁ := huniq r₁ ⟨Finset.mem_range.mp hr₁, (Finset.mem_filter.mp hi₁).2⟩
      have e₂ := huniq r₂ ⟨Finset.mem_range.mp hr₂, (Finset.mem_filter.mp hi₂).2⟩
      exact e₁.trans e₂.symm
    let UJ := (Finset.range (q + P)).biUnion Jg
    have hUJ_sub : UJ ⊆ J := by
      intro i hi
      obtain ⟨r, _, hir⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_filter.mp hir).1
    have hUJ_card : UJ.card = ∑ r ∈ Finset.range (q + P), (Jg r).card :=
      Finset.card_biUnion hJg_disj
    have hsum_ge : q + P ≤ ∑ r ∈ Finset.range (q + P), (Jg r).card := by
      calc q + P = ∑ _r ∈ Finset.range (q + P), 1 := by simp
        _ ≤ ∑ r ∈ Finset.range (q + P), (Jg r).card :=
            Finset.sum_le_sum fun r hr ↦ hJg_pos r (Finset.mem_range.mp hr)
    have hUJ_eq : UJ = J := Finset.eq_of_subset_of_card_le hUJ_sub (by omega)
    have hJg_eq1 (r : ℕ) (hr : r < q + P) : (Jg r).card = 1 := by
      by_contra hne1
      have hgt : 1 < (Jg r).card := lt_of_le_of_ne (hJg_pos r hr) (Ne.symm hne1)
      have hlt : ∑ _t ∈ Finset.range (q + P), 1 <
          ∑ t ∈ Finset.range (q + P), (Jg t).card :=
        Finset.sum_lt_sum (fun t ht ↦ hJg_pos t (Finset.mem_range.mp ht))
          ⟨r, Finset.mem_range.mpr hr, hgt⟩
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hlt
      have : UJ.card ≤ q + P := (Finset.card_le_card hUJ_sub).trans hJcard
      omega
    -- Extract the unique index `ia a ∈ J` for `a < q` and `ip p ∈ J` for `p < P`
    have hexV (a : ℕ) (ha : a < q) :
        ∃ i ∈ J, Jg a = {i} ∧ ∃ u < N, I.vectors[i.1] = mrssVertVec q N a u := by
      obtain ⟨i, hi_eq⟩ := Finset.card_eq_one.mp (hJg_eq1 a (by omega))
      have hi_mem : i ∈ Jg a := hi_eq ▸ Finset.mem_singleton_self i
      obtain ⟨hiJ, hpos⟩ := Finset.mem_filter.mp hi_mem
      rcases hvec_cases I.vectors[i.1] (List.getElem_mem i.2) with ⟨a', ha', u, hu, hv⟩ |
          ⟨p', hp', u, _, w, _, _, hv⟩
      · rw [hv, mrssVertVec_indV q N a' u a ha] at hpos
        have ha_eq : a = a' := by by_contra hne; simp [hne] at hpos
        subst ha_eq
        exact ⟨i, hiJ, hi_eq, u, hu, hv⟩
      · rw [hv, mrssEdgeVec_indV q N p' u w a ha] at hpos; omega
    have hexE (p : ℕ) (hp : p < P) :
        ∃ i ∈ J, Jg (q + p) = {i} ∧ ∃ u < N, ∃ w < N,
          G.toSimpleGraph.Adj (V.getD u 0) (V.getD w 0) ∧
            I.vectors[i.1] = mrssEdgeVec q N p u w := by
      obtain ⟨i, hi_eq⟩ := Finset.card_eq_one.mp (hJg_eq1 (q + p) (by omega))
      have hi_mem : i ∈ Jg (q + p) := hi_eq ▸ Finset.mem_singleton_self i
      obtain ⟨hiJ, hpos⟩ := Finset.mem_filter.mp hi_mem
      rcases hvec_cases I.vectors[i.1] (List.getElem_mem i.2) with ⟨a', _, u, _, hv⟩ |
          ⟨p', _, u, hu, w, hw, hadj, hv⟩
      · rw [hv, mrssVertVec_indE q N a' u p hp] at hpos; omega
      · rw [hv, mrssEdgeVec_indE q N p' u w p hp] at hpos
        have hp_eq : p = p' := by by_contra hne; simp [hne] at hpos
        subst hp_eq
        exact ⟨i, hiJ, hi_eq, u, hu, w, hw, hadj, hv⟩
    choose ia hia_J hia_Jg uSel huSel_lt hia_vec using hexV
    choose ip hip_J hip_Jg euSel heu_lt ewSel hew_lt he_adj hip_vec using hexE
    have hadj_sel {a b : ℕ} (hab : a < b) (hb : b < q) :
        G.toSimpleGraph.Adj (V.getD (uSel a (Nat.lt_trans hab hb)) 0)
          (V.getD (uSel b hb) 0) := by
      have ha : a < q := Nat.lt_trans hab hb
      have hmem_pair : (a, b) ∈ cliquePairs q := mem_cliquePairs_iff.mpr ⟨hab, hb⟩
      obtain ⟨p, hp_lt, hp_eq⟩ := List.getElem_of_mem hmem_pair
      have hpr1 : (cliquePairs q)[p].1 = a := congrArg Prod.fst hp_eq
      have hpr2 : (cliquePairs q)[p].2 = b := congrArg Prod.snd hp_eq
      have hP_eq : P = (cliquePairs q).length := rfl
      have hp_ltP : p < P := hP_eq.symm ▸ hp_lt
      -- Evaluate the 4 matching coordinates `r = 0, 1, 2, 3` for pair `p`
      have hmatch_coord (r : ℕ) (hr : r < 4) :
          N ≤ ([uSel a ha, N - uSel a ha, 0, 0] : List ℕ).getD r 0 +
            ([0, 0, uSel b hb, N - uSel b hb] : List ℕ).getD r 0 +
            ([N - euSel p hp_ltP, euSel p hp_ltP,
              N - ewSel p hp_ltP, ewSel p hp_ltP] : List ℕ).getD r 0 := by
        have hdom := hJdom (q + (cliquePairs q).length + (4 * p + r))
          (show q + (cliquePairs q).length + (4 * p + r) < q + 5 * (cliquePairs q).length by omega)
        rw [hItgt, mrssTargetVec_match q N (4 * p + r) (by omega)] at hdom
        rw [← hUJ_eq, Finset.sum_biUnion hJg_disj, Finset.sum_range_add,
          ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hdom
        have hsumV : (∑ a' : Fin q, ∑ i ∈ Jg a'.1,
            (I.vectors[i.1]).getD (q + (cliquePairs q).length + (4 * p + r)) 0) =
            ([uSel a ha, N - uSel a ha, 0, 0] : List ℕ).getD r 0 +
              ([0, 0, uSel b hb, N - uSel b hb] : List ℕ).getD r 0 := by
          have h1 : ∀ a' : Fin q, ∑ i ∈ Jg a'.1,
              (I.vectors[i.1]).getD (q + (cliquePairs q).length + (4 * p + r)) 0 =
              (if a'.1 = a then ([uSel a'.1 a'.2, N - uSel a'.1 a'.2, 0, 0] : List ℕ).getD r 0
               else if a'.1 = b then ([0, 0, uSel a'.1 a'.2, N - uSel a'.1 a'.2] : List ℕ).getD r 0
               else 0) := by
            intro a'
            rw [hia_Jg a'.1 a'.2, Finset.sum_singleton, hia_vec a'.1 a'.2,
              mrssVertVec_match q N a'.1 (uSel a'.1 a'.2) p r hp_lt hr, hpr1, hpr2]
          simp_rw [h1]
          let aF : Fin q := ⟨a, ha⟩
          let bF : Fin q := ⟨b, hb⟩
          have habF : aF ≠ bF := fun h ↦ (Nat.ne_of_lt hab) (congrArg Fin.val h)
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ aF),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨habF.symm, Finset.mem_univ bF⟩)]
          have hrest : ∑ a' ∈ (Finset.univ.erase aF).erase bF,
              (if a'.1 = a then ([uSel a'.1 a'.2, N - uSel a'.1 a'.2, 0, 0] : List ℕ).getD r 0
               else if a'.1 = b then ([0, 0, uSel a'.1 a'.2, N - uSel a'.1 a'.2] : List ℕ).getD r 0
               else 0) = 0 := by
            refine Finset.sum_eq_zero fun a' ha'_mem ↦ ?_
            have hneb : a' ≠ bF := (Finset.mem_erase.mp ha'_mem).1
            have hnea : a' ≠ aF := (Finset.mem_erase.mp (Finset.mem_erase.mp ha'_mem).2).1
            have h1' : a'.1 ≠ a := fun h ↦ hnea (Fin.ext h)
            have h2' : a'.1 ≠ b := fun h ↦ hneb (Fin.ext h)
            simp [h1', h2']
          rw [hrest, add_zero]
          have hba : b ≠ a := Nat.ne_of_gt hab
          simp [aF, bF, hba]
        have hsumE : (∑ p' : Fin P, ∑ i ∈ Jg (q + p'.1),
            (I.vectors[i.1]).getD (q + (cliquePairs q).length + (4 * p + r)) 0) =
            ([N - euSel p hp_ltP, euSel p hp_ltP,
              N - ewSel p hp_ltP, ewSel p hp_ltP] : List ℕ).getD r 0 := by
          have h1 : ∀ p' : Fin P, ∑ i ∈ Jg (q + p'.1),
              (I.vectors[i.1]).getD (q + (cliquePairs q).length + (4 * p + r)) 0 =
              if p = p'.1 then
                ([N - euSel p'.1 p'.2, euSel p'.1 p'.2,
                  N - ewSel p'.1 p'.2, ewSel p'.1 p'.2] : List ℕ).getD r 0
              else 0 := by
            intro p'
            rw [hip_Jg p'.1 p'.2, Finset.sum_singleton, hip_vec p'.1 p'.2,
              mrssEdgeVec_match q N p'.1 _ _ p r hp_lt hr]
          simp_rw [h1]
          have : (∑ p' : Fin P,
              if p = p'.1 then
                ([N - euSel p'.1 p'.2, euSel p'.1 p'.2,
                  N - ewSel p'.1 p'.2, ewSel p'.1 p'.2] : List ℕ).getD r 0
              else 0) =
              ∑ p' : Fin P,
                if p' = ⟨p, hp_ltP⟩ then
                  ([N - euSel p hp_ltP, euSel p hp_ltP,
                    N - ewSel p hp_ltP, ewSel p hp_ltP] : List ℕ).getD r 0
                else 0 := by
            refine Finset.sum_congr rfl fun p' _ ↦ ?_
            by_cases hpe : p' = ⟨p, hp_ltP⟩
            · subst hpe; simp
            · have hne : p ≠ p'.1 := fun h ↦ hpe (Fin.ext h.symm)
              simp [hpe, hne]
          rw [this]
          simp
        rw [hsumV, hsumE] at hdom
        omega
      have hc0 := hmatch_coord 0 (by omega)
      have hc1 := hmatch_coord 1 (by omega)
      have hc2 := hmatch_coord 2 (by omega)
      have hc3 := hmatch_coord 3 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1 hc2 hc3
      have hua_lt := huSel_lt a ha
      have hub_lt := huSel_lt b hb
      have heu := heu_lt p hp_ltP
      have hew := hew_lt p hp_ltP
      have hua_eq : uSel a ha = euSel p hp_ltP := by omega
      have hub_eq : uSel b hb = ewSel p hp_ltP := by omega
      rw [hua_eq, hub_eq]
      exact he_adj p hp_ltP
    -- Build the `q`-clique `S = Finset.univ.image (fun a : Fin q ↦ V.getD (uSel a.1 a.2) 0)`
    let vFn (a : Fin q) : ℕ := V.getD (uSel a.1 a.2) 0
    have hvFn_adj {a b : Fin q} (hne : a ≠ b) : G.toSimpleGraph.Adj (vFn a) (vFn b) := by
      rcases lt_trichotomy a.1 b.1 with hab | heq | hba
      · exact hadj_sel hab b.2
      · exact (hne (Fin.ext heq)).elim
      · exact (hadj_sel hba a.2).symm
    have hvFn_inj : Function.Injective vFn := fun a b h ↦ by
      by_contra hne
      exact (hvFn_adj hne).ne h
    rw [mem_Clique_iff]
    refine ⟨Finset.univ.image vFn, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
      exact hgetV_mem (uSel a.1 a.2) (huSel_lt a.1 a.2)
    · intro w₁ hw₁ w₂ hw₂ hne
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw₁
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw₂
      exact hvFn_adj fun h ↦ hne (congrArg vFn h)
    · rw [Finset.card_image_of_injective _ hvFn_inj, Finset.card_fin]

theorem unaryMRSSParam_cliqueToUnaryMRSS_le (x : CliqueInstance) :
    unaryMRSSParam (cliqueToUnaryMRSS x) ≤ 2 * x.m + 6 * (x.m * x.m) + 1 := by
  dsimp only [cliqueToUnaryMRSS]
  have hcap_le : cliqueCap x ≤ x.m := Nat.min_le_right _ _
  have hP_le : (cliquePairs (cliqueCap x)).length ≤ x.m * x.m :=
    (length_cliquePairs_le (cliqueCap x)).trans (Nat.mul_le_mul hcap_le hcap_le)
  have hmul : 6 * (cliquePairs (cliqueCap x)).length ≤ 6 * (x.m * x.m) :=
    Nat.mul_le_mul_left 6 hP_le
  cases (!decide (cliqueCap x = x.m)) <;>
    cases (decide (cliqueCap x = 0)) <;>
    cases (decide (cliqueCap x = 1)) <;>
    cases x.graph.distinctVertices.isEmpty <;>
    simp only [Bool.false_eq_true, ↓reduceIte, unaryMRSSParam, noMRSS, yesMRSS, buildCliqueMRSS] <;>
    omega

theorem cliqueToUnaryMRSS_mem_iff (x : CliqueInstance) :
    x ∈ Clique ↔ cliqueToUnaryMRSS x ∈ UnaryMRSS := by
  rcases x with ⟨G, m⟩
  unfold cliqueToUnaryMRSS
  set q := cliqueCap ⟨G, m⟩
  have hq_eq : q = min G.distinctVertices.length m := rfl
  by_cases hqm : (!decide (q = m)) = true
  · simp only [hqm, ↓reduceIte]
    have hne : q ≠ m := by simpa using hqm
    have hgt : G.distinctVertices.length < m := by omega
    refine iff_of_false ?_ noMRSS_notMem
    rw [mem_Clique_iff]
    rintro ⟨S, hSV, _, rfl⟩
    have hle : S.card ≤ G.distinctVertices.length := by
      rw [Graph.length_distinctVertices]
      exact Finset.card_le_card fun v hv ↦ List.mem_toFinset.mpr (hSV v hv)
    omega
  · have hqm_eq : q = m := by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at hqm
      exact hqm
    have hqmF : (!decide (q = m)) = false := Bool.eq_false_iff.mpr hqm
    simp only [hqmF, Bool.false_eq_true, ↓reduceIte]
    by_cases hq0 : decide (q = 0) = true
    · simp only [hq0, ↓reduceIte]
      have hm0 : m = 0 := hqm_eq.symm.trans (of_decide_eq_true hq0)
      subst hm0
      refine iff_of_true ?_ yesMRSS_mem
      rw [mem_Clique_iff]
      exact ⟨∅, by simp, by simp⟩
    · have hq0F : decide (q = 0) = false := Bool.eq_false_iff.mpr hq0
      have hq_ne0 : q ≠ 0 := of_decide_eq_false hq0F
      simp only [hq0F, Bool.false_eq_true, ↓reduceIte]
      by_cases hq1 : decide (q = 1) = true
      · simp only [hq1, ↓reduceIte]
        have hm1 : m = 1 := hqm_eq.symm.trans (of_decide_eq_true hq1)
        subst hm1
        by_cases hemp : G.distinctVertices.isEmpty = true
        · simp only [hemp, ↓reduceIte]
          have hnil : G.distinctVertices = [] := List.isEmpty_iff.mp hemp
          refine iff_of_false ?_ noMRSS_notMem
          rw [mem_Clique_iff]
          rintro ⟨S, hSV, _, hcard⟩
          dsimp only at hcard
          obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
          have hvD : v ∈ G.distinctVertices := Graph.mem_distinctVertices.mpr (hSV v hv)
          simp [hnil] at hvD
        · have hempF : G.distinctVertices.isEmpty = false := Bool.eq_false_iff.mpr hemp
          simp only [hempF, Bool.false_eq_true, ↓reduceIte]
          cases hG : G.distinctVertices with
          | nil => simp [hG] at hempF
          | cons v vs =>
            have hv : v ∈ G.distinctVertices := hG ▸ List.mem_cons_self
            refine iff_of_true ?_ yesMRSS_mem
            rw [mem_Clique_iff]
            exact ⟨{v}, fun w hw ↦ by
              rw [Finset.mem_singleton] at hw
              subst hw
              exact Graph.mem_distinctVertices.mp hv, by simp⟩
      · have hq1F : decide (q = 1) = false := Bool.eq_false_iff.mpr hq1
        have hq_ne1 : q ≠ 1 := of_decide_eq_false hq1F
        simp only [hq1F, Bool.false_eq_true, ↓reduceIte]
        have hq2 : 2 ≤ q := by omega
        have hqN : q ≤ G.distinctVertices.length := Nat.min_le_left _ _
        simpa only [hqm_eq] using buildCliqueMRSS_mem_iff G hq2 hqN

/-- `Clique` FPT-reduces to `UnaryMRSS`. -/
theorem fptReducible_Clique_UnaryMRSS :
    FPTReducible encCliqueInstance encUnaryMRSS (·.m) unaryMRSSParam Clique UnaryMRSS :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToUnaryMRSS
    (h := fun k ↦ 2 * k + 6 * (k * k) + 1) unaryMRSSParam_cliqueToUnaryMRSS_le
    cliqueToUnaryMRSS_mem_iff

/-- **Multidimensional Relaxed Subset Sum** with unary-encoded inputs is `W[1]`-hard
parameterized by
`k + m`. -/
theorem UnaryMRSS_wHard : WHard 1 encUnaryMRSS unaryMRSSParam UnaryMRSS :=
  Clique_wHard.trans fptReducible_Clique_UnaryMRSS

end CliqueToMRSS

end CslibFrontier.Complexity
