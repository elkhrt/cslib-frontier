/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TrianglePartition.Gadgets
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Syntax
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# Glued Graph Construction, Polynomial-Time Computability, and $K_4$-Freeness

Constructs `buildGluedGraph` and `threeSATThreeToTriGraph` by gluing $\mathrm{Torus}(12, 4)$
variable gadgets to $K_{3,3,3}$ clause gadgets along port triangles, proves polynomial-time
computability (`computableInPolyTime_threeSATThreeToTriGraph`), characterizes adjacency and
induced subgraphs, proves every triangle lies inside a single gadget (`glued_triangle_in_gadget`),
and establishes $K_4$-freeness (`threeSATThreeToTriGraph_k4Free`).

## Main definitions
- `clauseLitPos`, `torusPortPos`, `torusVertexId`, `buildGluedGraph`, `threeSATThreeToTriGraph`.

## Main results
- `computableInPolyTime_threeSATThreeToTriGraph`: polynomial-time computability.
- `glued_adj_iff`, `glued_clause_induced`, `glued_torus_induced`, `glued_triangle_in_gadget`.
- `buildGluedGraph_k4Free`, `threeSATThreeToTriGraph_k4Free`: $K_4$-freeness.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Glued Graph Construction -/

/-- Position `0, 1, 2` of variable `v` in clause `c`, or `3` if absent. -/
@[expose] def clauseLitPos (c : Clause ℕ) (v : ℕ) : ℕ :=
  if 0 < c.length && decide ((c.getD 0 (0, false)).1 = v) then 0
  else if 1 < c.length && decide ((c.getD 1 (0, false)).1 = v) then 1
  else if 2 < c.length && decide ((c.getD 2 (0, false)).1 = v) then 2
  else 3

/-- Position `0, 1, 2` of vertex `p` in port `(occ, b)`, or `3` if absent. -/
@[expose] def torusPortPos (occ : ℕ) (b : Bool) (p : ℕ) : ℕ :=
  let a0 := 4 * (4 * occ)
  let a1 := 4 * (4 * occ + 1)
  let a2 := if b then 4 * (4 * occ) + 1 else 4 * (4 * occ + 1) + 3
  if p = a0 then 0 else if p = a1 then 1 else if p = a2 then 2 else 3

/-- Test whether torus vertex `p` of variable `v` is glued to clause `j`. -/
@[expose] def matchClause (ψ : CNF ℕ) (v p j : ℕ) : Bool :=
  let c := ψ.getD j []
  let r := clauseLitPos c v
  if r < 3 then
    let b := (c.getD r (0, false)).2
    let occ := (CNF.vars (ψ.take j)).count v
    decide (torusPortPos occ b p < 3)
  else false

/-- Final vertex ID of vertex `p` on variable torus `vi` after gluing. -/
@[expose] def torusVertexId (ψ : CNF ℕ) (vars : List ℕ) (vi p : ℕ) : ℕ :=
  let v := vars.getD vi 0
  let m := ψ.length
  let j := ((List.range m).filter (matchClause ψ v p)).headD m
  if j < m then
    let c := ψ.getD j []
    let r := clauseLitPos c v
    let b := (c.getD r (0, false)).2
    let occ := (CNF.vars (ψ.take j)).count v
    let pos := torusPortPos occ b p
    9 * j + k333PortVert r pos
  else
    9 * m + 48 * vi + p

/-- Clause edges of the glued graph. -/
@[expose] def gluedClauseEdges (ψ : CNF ℕ) : List (ℕ × ℕ) :=
  (List.range ψ.length).flatMap fun j =>
    let len := (ψ.getD j []).length
    k333Edges.flatMap fun e =>
      if k333ClauseAdj len e.1 e.2 then [(9 * j + e.1, 9 * j + e.2)] else []

/-- Torus edges of the glued graph. -/
@[expose] def gluedTorusEdges (ψ : CNF ℕ) (vars : List ℕ) : List (ℕ × ℕ) :=
  (List.range vars.length).flatMap fun vi =>
    torusEdges.map fun e => (torusVertexId ψ vars vi e.1, torusVertexId ψ vars vi e.2)

/-- Glued graph for a normalized width-3, occurrence-3 CNF `ψ`. -/
@[expose] def buildGluedGraph (ψ : CNF ℕ) : Graph :=
  let vars := ψ.distinctVars
  ⟨List.range (9 * ψ.length + 48 * vars.length),
   gluedClauseEdges ψ ++ gluedTorusEdges ψ vars⟩

/-- Polynomial-time Karp reduction from `ThreeSATThree` to `K4FreeTrianglePartition`. -/
def threeSATThreeToTriGraph (φ : CNF ℕ) : Graph :=
  if ThreeSATThree.syntaxCheck φ then
    let ψ := normCNF φ
    if ψ.any List.isEmpty then noTriGraph
    else if ψ.length = 0 then emptyTriGraph
    else buildGluedGraph ψ
  else noTriGraph

theorem threeSATThreeToTriGraph_eq (φ : CNF ℕ) :
    threeSATThreeToTriGraph φ =
      if ThreeSATThree.syntaxCheck φ then
        let ψ := normCNF φ
        if ψ.any List.isEmpty then noTriGraph
        else if ψ.length = 0 then emptyTriGraph
        else buildGluedGraph ψ
      else noTriGraph := by
  rfl

/-! ### Polynomial-Time Computability -/

private theorem computableInPolyTime_clauseLitPos :
    ComputableInPolyTime (fun p : Clause ℕ × ℕ => clauseLitPos p.1 p.2)
      (encPair (encClause encNat) encNat) encUnary := by
  unfold clauseLitPos
  have hlen : ComputableInPolyTime (fun p : Clause ℕ × ℕ => p.1.length)
      (encPair (encClause encNat) encNat) encUnary :=
    Clause.computableInPolyTime_length (by fun_prop)
  have hl0 : ComputableInPolyTime (fun p : Clause ℕ × ℕ => p.1.getD 0 (0, false))
      (encPair (encClause encNat) encNat) (encPair encNat encBool) :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) (.const 0) (0, false)
  have hl1 : ComputableInPolyTime (fun p : Clause ℕ × ℕ => p.1.getD 1 (0, false))
      (encPair (encClause encNat) encNat) (encPair encNat encBool) :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) (.const 1) (0, false)
  have hl2 : ComputableInPolyTime (fun p : Clause ℕ × ℕ => p.1.getD 2 (0, false))
      (encPair (encClause encNat) encNat) (encPair encNat encBool) :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) (.const 2) (0, false)
  have hb0 : ComputableInPolyTime
      (fun p : Clause ℕ × ℕ => decide (0 < p.1.length) && decide ((p.1.getD 0 (0, false)).1 = p.2))
      (encPair (encClause encNat) encNat) encBool := by fun_prop
  have hb1 : ComputableInPolyTime
      (fun p : Clause ℕ × ℕ => decide (1 < p.1.length) && decide ((p.1.getD 1 (0, false)).1 = p.2))
      (encPair (encClause encNat) encNat) encBool := by fun_prop
  have hb2 : ComputableInPolyTime
      (fun p : Clause ℕ × ℕ => decide (2 < p.1.length) && decide ((p.1.getD 2 (0, false)).1 = p.2))
      (encPair (encClause encNat) encNat) encBool := by fun_prop
  have hc3 : ComputableInPolyTime (fun _ : Clause ℕ × ℕ => (3 : ℕ))
      (encPair (encClause encNat) encNat) encUnary := .const 3
  have hc2 : ComputableInPolyTime (fun _ : Clause ℕ × ℕ => (2 : ℕ))
      (encPair (encClause encNat) encNat) encUnary := .const 2
  have hc1 : ComputableInPolyTime (fun _ : Clause ℕ × ℕ => (1 : ℕ))
      (encPair (encClause encNat) encNat) encUnary := .const 1
  have hc0 : ComputableInPolyTime (fun _ : Clause ℕ × ℕ => (0 : ℕ))
      (encPair (encClause encNat) encNat) encUnary := .const 0
  have h2 := ComputableInPolyTime.ite' hb2 hc2 hc3
  have h1 := ComputableInPolyTime.ite' hb1 hc1 h2
  simpa using ComputableInPolyTime.ite' hb0 hc0 h1

private theorem computableInPolyTime_torusPortPos :
    ComputableInPolyTime (fun p : (ℕ × Bool) × ℕ => torusPortPos p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBool) encUnary) encUnary := by
  unfold torusPortPos
  have ha0 : ComputableInPolyTime (fun p : (ℕ × Bool) × ℕ => 4 * (4 * p.1.1))
      (encPair (encPair encUnary encBool) encUnary) encUnary := by fun_prop
  have ha1 : ComputableInPolyTime (fun p : (ℕ × Bool) × ℕ => 4 * (4 * p.1.1 + 1))
      (encPair (encPair encUnary encBool) encUnary) encUnary := by fun_prop
  have ha2 : ComputableInPolyTime
      (fun p : (ℕ × Bool) × ℕ => if p.1.2 then 4 * (4 * p.1.1) + 1 else 4 * (4 * p.1.1 + 1) + 3)
      (encPair (encPair encUnary encBool) encUnary) encUnary :=
    ComputableInPolyTime.ite' (by fun_prop) (by fun_prop) (by fun_prop)
  have hc0 : ComputableInPolyTime (fun p : (ℕ × Bool) × ℕ => decide (p.2 = 4 * (4 * p.1.1)))
      (encPair (encPair encUnary encBool) encUnary) encBool := by fun_prop
  have hc1 : ComputableInPolyTime (fun p : (ℕ × Bool) × ℕ => decide (p.2 = 4 * (4 * p.1.1 + 1)))
      (encPair (encPair encUnary encBool) encUnary) encBool := by fun_prop
  have hc2 : ComputableInPolyTime
      (fun p : (ℕ × Bool) × ℕ =>
        decide (p.2 = if p.1.2 then 4 * (4 * p.1.1) + 1 else 4 * (4 * p.1.1 + 1) + 3))
      (encPair (encPair encUnary encBool) encUnary) encBool := by fun_prop
  have k3 : ComputableInPolyTime (fun _ : (ℕ × Bool) × ℕ => (3 : ℕ))
      (encPair (encPair encUnary encBool) encUnary) encUnary := .const 3
  have k2 : ComputableInPolyTime (fun _ : (ℕ × Bool) × ℕ => (2 : ℕ))
      (encPair (encPair encUnary encBool) encUnary) encUnary := .const 2
  have k1 : ComputableInPolyTime (fun _ : (ℕ × Bool) × ℕ => (1 : ℕ))
      (encPair (encPair encUnary encBool) encUnary) encUnary := .const 1
  have k0 : ComputableInPolyTime (fun _ : (ℕ × Bool) × ℕ => (0 : ℕ))
      (encPair (encPair encUnary encBool) encUnary) encUnary := .const 0
  have h2 := ComputableInPolyTime.ite' hc2 k2 k3
  have h1 := ComputableInPolyTime.ite' hc1 k1 h2
  simpa using ComputableInPolyTime.ite' hc0 k0 h1

private theorem computableInPolyTime_matchClause :
    ComputableInPolyTime (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => matchClause p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encBool := by
  unfold matchClause
  have hc : ComputableInPolyTime (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => p.1.1.1.getD p.2 [])
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) (encClause encNat) :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) []
  have hr : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary :=
    computableInPolyTime_clauseLitPos.comp (hc.prod (by fun_prop))
  have hb : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ =>
        ((p.1.1.1.getD p.2 []).getD (clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2) (0, false)).2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encBool :=
    (by fun_prop : ComputableInPolyTime Prod.snd (encPair encNat encBool) encBool).comp
      (ComputableInPolyTime.listGetDWithInput hc hr (0, false))
  have htake : ComputableInPolyTime (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => p.1.1.1.take p.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encCNF :=
    ComputableInPolyTime.listTakeWithInput (by fun_prop) (by fun_prop)
  have hvars : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => CNF.vars (p.1.1.1.take p.2))
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) (encList encNat) :=
    (CNF.computableInPolyTime_vars encNat).comp htake
  have hocc : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => (CNF.vars (p.1.1.1.take p.2)).count p.1.1.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary :=
    ComputableInPolyTime.countWithInput hvars (by fun_prop)
  have hpos : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ =>
        torusPortPos ((CNF.vars (p.1.1.1.take p.2)).count p.1.1.2)
          ((p.1.1.1.getD p.2 []).getD (clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2) (0, false)).2
          p.1.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary :=
    computableInPolyTime_torusPortPos.comp ((hocc.prod hb).prod (by fun_prop))
  have hcond : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ =>
        decide (clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2 < 3))
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encBool := by fun_prop
  have hres : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ =>
        decide (torusPortPos ((CNF.vars (p.1.1.1.take p.2)).count p.1.1.2)
          ((p.1.1.1.getD p.2 []).getD (clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2) (0, false)).2
          p.1.2 < 3))
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encBool := by fun_prop
  simpa using ComputableInPolyTime.ite' hcond hres (.const false)

private def torusMatchClauseIdx (ψ : CNF ℕ) (v p : ℕ) : ℕ :=
  ((List.range ψ.length).filter (matchClause ψ v p)).headD ψ.length

private def torusGluedPortVert (ψ : CNF ℕ) (v p j : ℕ) : ℕ :=
  let c := ψ.getD j []
  let r := clauseLitPos c v
  let b := (c.getD r (0, false)).2
  let occ := (CNF.vars (ψ.take j)).count v
  let pos := torusPortPos occ b p
  9 * j + k333PortVert r pos

private theorem computableInPolyTime_torusMatchClauseIdx :
    ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => torusMatchClauseIdx p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encNat) encUnary) encUnary := by
  unfold torusMatchClauseIdx
  have hm : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1.length)
      (encPair (encPair encCNF encNat) encUnary) encUnary :=
    CNF.computableInPolyTime_length (by fun_prop)
  have hrange : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => List.range p.1.1.length)
      (encPair (encPair encCNF encNat) encUnary) (encList encUnary) := by fun_prop
  have hfilt : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ => (List.range p.1.1.length).filter (matchClause p.1.1 p.1.2 p.2))
      (encPair (encPair encCNF encNat) encUnary) (encList encUnary) :=
    ComputableInPolyTime.filterWithInput hrange computableInPolyTime_matchClause
  exact ComputableInPolyTime.listHeadDWithInput hfilt hm

private theorem computableInPolyTime_torusGluedPortVert :
    ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => torusGluedPortVert p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary := by
  unfold torusGluedPortVert
  have hc : ComputableInPolyTime (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => p.1.1.1.getD p.2 [])
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) (encClause encNat) :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) []
  have hr : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary :=
    computableInPolyTime_clauseLitPos.comp (hc.prod (by fun_prop))
  have hb : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ =>
        ((p.1.1.1.getD p.2 []).getD (clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2) (0, false)).2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encBool :=
    (ComputableInPolyTime.snd encNat encBool).comp
      (ComputableInPolyTime.listGetDWithInput hc hr (0, false))
  have htake : ComputableInPolyTime (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => p.1.1.1.take p.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encCNF :=
    ComputableInPolyTime.listTakeWithInput (by fun_prop) (by fun_prop)
  have hocc : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => (CNF.vars (p.1.1.1.take p.2)).count p.1.1.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary :=
    ComputableInPolyTime.countWithInput ((CNF.computableInPolyTime_vars encNat).comp htake)
      (by fun_prop)
  have hpos : ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ =>
        torusPortPos ((CNF.vars (p.1.1.1.take p.2)).count p.1.1.2)
          ((p.1.1.1.getD p.2 []).getD (clauseLitPos (p.1.1.1.getD p.2 []) p.1.1.2) (0, false)).2
          p.1.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary :=
    computableInPolyTime_torusPortPos.comp ((hocc.prod hb).prod (by fun_prop))
  have hkv := computableInPolyTime_k333PortVert.comp (hr.prod hpos)
  have h9 : ComputableInPolyTime (fun p : ((CNF ℕ × ℕ) × ℕ) × ℕ => 9 * p.2)
      (encPair (encPair (encPair encCNF encNat) encUnary) encUnary) encUnary := by fun_prop
  have hadd : ComputableInPolyTime (fun q : ℕ × ℕ => q.1 + q.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  exact (hadd.comp (h9.prod hkv)).of_enc_eq fun p => congrArg _ rfl

private theorem computableInPolyTime_torusVertexId :
    ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ => torusVertexId p.1.1 p.1.1.distinctVars p.1.2 p.2)
      (encPair (encPair encCNF encUnary) encUnary) encNat := by
  have hdv : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1.distinctVars)
      (encPair (encPair encCNF encUnary) encUnary) (encList encNat) :=
    SAT.computableInPolyTime_distinctVars.comp (by fun_prop)
  have hv : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1.distinctVars.getD p.1.2 0)
      (encPair (encPair encCNF encUnary) encUnary) encNat :=
    ComputableInPolyTime.listGetDWithInput hdv (by fun_prop) 0
  have hm : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1.length)
      (encPair (encPair encCNF encUnary) encUnary) encUnary :=
    CNF.computableInPolyTime_length (by fun_prop)
  have harg : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ => ((p.1.1, p.1.1.distinctVars.getD p.1.2 0), p.2))
      (encPair (encPair encCNF encUnary) encUnary)
      (encPair (encPair encCNF encNat) encUnary) :=
    ((by fun_prop : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1) _ encCNF).prod hv).prod
      (by fun_prop)
  have hj := computableInPolyTime_torusMatchClauseIdx.comp harg
  have hbranch1 : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ =>
        torusGluedPortVert p.1.1 (p.1.1.distinctVars.getD p.1.2 0) p.2
          (torusMatchClauseIdx p.1.1 (p.1.1.distinctVars.getD p.1.2 0) p.2))
      (encPair (encPair encCNF encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (computableInPolyTime_torusGluedPortVert.comp (harg.prod hj))
  have hbranch2 : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ => 9 * p.1.1.length + 48 * p.1.2 + p.2)
      (encPair (encPair encCNF encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hlt : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ =>
        decide (torusMatchClauseIdx p.1.1 (p.1.1.distinctVars.getD p.1.2 0) p.2 < p.1.1.length))
      (encPair (encPair encCNF encUnary) encUnary) encBool := by fun_prop
  exact (ComputableInPolyTime.ite' hlt hbranch1 hbranch2).of_enc_eq fun p => congrArg _ (by
    simp only [decide_eq_true_eq]
    dsimp only [torusVertexId, torusMatchClauseIdx, torusGluedPortVert, Function.comp_apply]
    rfl)

private theorem computableInPolyTime_gluedClauseEdges :
    ComputableInPolyTime gluedClauseEdges encCNF (encList (encPair encNat encNat)) := by
  unfold gluedClauseEdges
  have hinner : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ =>
        k333Edges.flatMap fun e =>
          if k333ClauseAdj (p.1.getD p.2 []).length e.1 e.2
          then [(9 * p.2 + e.1, 9 * p.2 + e.2)] else [])
      (encPair encCNF encUnary) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.flatMapConst k333Edges fun e _ => ?_
    have hlen_c : ComputableInPolyTime (fun p : CNF ℕ × ℕ => (p.1.getD p.2 []).length)
        (encPair encCNF encUnary) encUnary :=
      Clause.computableInPolyTime_length
        (ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) [])
    have hcond : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ => k333ClauseAdj (p.1.getD p.2 []).length e.1 e.2)
        (encPair encCNF encUnary) encBool := by
      have hle2 : ComputableInPolyTime
          (fun p : CNF ℕ × ℕ => decide ((p.1.getD p.2 []).length ≤ 2))
          (encPair encCNF encUnary) encBool := by fun_prop
      have hle1 : ComputableInPolyTime
          (fun p : CNF ℕ × ℕ => decide ((p.1.getD p.2 []).length ≤ 1))
          (encPair encCNF encUnary) encBool := by fun_prop
      have hb0 : ComputableInPolyTime (fun _ : CNF ℕ × ℕ => k333Adj e.1 e.2)
          (encPair encCNF encUnary) encBool := .const (k333Adj e.1 e.2)
      have hb1 : ComputableInPolyTime
          (fun p : CNF ℕ × ℕ =>
            if decide ((p.1.getD p.2 []).length ≤ 2) then !isInTri 7 2 5 e.1 e.2 else true)
          (encPair encCNF encUnary) encBool :=
        ComputableInPolyTime.ite' hle2 (.const (!isInTri 7 2 5 e.1 e.2)) (.const true)
      have hb2 : ComputableInPolyTime
          (fun p : CNF ℕ × ℕ =>
            if decide ((p.1.getD p.2 []).length ≤ 1) then !isInTri 1 4 6 e.1 e.2 else true)
          (encPair encCNF encUnary) encBool :=
        ComputableInPolyTime.ite' hle1 (.const (!isInTri 1 4 6 e.1 e.2)) (.const true)
      have hall : ComputableInPolyTime
          (fun p : CNF ℕ × ℕ =>
            (k333Adj e.1 e.2 &&
              (if decide ((p.1.getD p.2 []).length ≤ 2) then !isInTri 7 2 5 e.1 e.2 else true)) &&
              (if decide ((p.1.getD p.2 []).length ≤ 1) then !isInTri 1 4 6 e.1 e.2 else true))
          (encPair encCNF encUnary) encBool := by fun_prop
      exact hall.of_enc_eq fun p => congrArg _ (k333ClauseAdj_eq_bool _ _ _)
    have ha : ComputableInPolyTime (fun p : CNF ℕ × ℕ => 9 * p.2 + e.1)
        (encPair encCNF encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    have hb : ComputableInPolyTime (fun p : CNF ℕ × ℕ => 9 * p.2 + e.2)
        (encPair encCNF encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    have hnil : ComputableInPolyTime (fun _ : CNF ℕ × ℕ => ([] : List (ℕ × ℕ)))
        (encPair encCNF encUnary) (encList (encPair encNat encNat)) := .const []
    have hpair := ComputableInPolyTime.cons' (ha.prod hb) hnil
    exact ComputableInPolyTime.ite' hcond hpair hnil
  have hm : ComputableInPolyTime (fun ψ : CNF ℕ => ψ.length) encCNF encUnary :=
    CNF.computableInPolyTime_length (by fun_prop)
  exact ComputableInPolyTime.flatMapWithInput (by fun_prop) hinner

private theorem computableInPolyTime_gluedTorusEdges :
    ComputableInPolyTime (fun ψ : CNF ℕ => gluedTorusEdges ψ ψ.distinctVars)
      encCNF (encList (encPair encNat encNat)) := by
  unfold gluedTorusEdges
  have hdv : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars
  have hk : ComputableInPolyTime (fun ψ : CNF ℕ => ψ.distinctVars.length) encCNF encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hdv
  have hinner : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ =>
        torusEdges.map fun e =>
          (torusVertexId p.1 p.1.distinctVars p.2 e.1,
           torusVertexId p.1 p.1.distinctVars p.2 e.2))
      (encPair encCNF encUnary) (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.mapConst torusEdges fun e _ => ?_
    have hid : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p)
        (encPair encCNF encUnary) (encPair encCNF encUnary) := .id'
    have h1 := computableInPolyTime_torusVertexId.comp (hid.prod (.const e.1))
    have h2 := computableInPolyTime_torusVertexId.comp (hid.prod (.const e.2))
    exact h1.prod h2
  exact ComputableInPolyTime.flatMapWithInput (by fun_prop) hinner

/-- Polynomial-time computability of `threeSATThreeToTriGraph`. -/
theorem computableInPolyTime_threeSATThreeToTriGraph :
    ComputableInPolyTime threeSATThreeToTriGraph encCNF encGraph := by
  have hbuild : ComputableInPolyTime buildGluedGraph encCNF encGraph := by
    unfold buildGluedGraph
    have hdv : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
      SAT.computableInPolyTime_distinctVars
    have hk : ComputableInPolyTime (fun ψ : CNF ℕ => ψ.distinctVars.length) encCNF encUnary :=
      (ComputableInPolyTime.length_list encNat).comp hdv
    have hm : ComputableInPolyTime (fun ψ : CNF ℕ => ψ.length) encCNF encUnary :=
      CNF.computableInPolyTime_length (by fun_prop)
    have hverts : ComputableInPolyTime
        (fun ψ : CNF ℕ => List.range (9 * ψ.length + 48 * ψ.distinctVars.length))
        encCNF (encList encNat) := by
      have hr : ComputableInPolyTime
          (fun ψ : CNF ℕ => List.range (9 * ψ.length + 48 * ψ.distinctVars.length))
          encCNF (encList encUnary) := by fun_prop
      exact ((ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hr).of_enc_eq
        fun ψ => congrArg _ (by simp)
    have hedges : ComputableInPolyTime
        (fun ψ : CNF ℕ => gluedClauseEdges ψ ++ gluedTorusEdges ψ ψ.distinctVars)
        encCNF (encList (encPair encNat encNat)) :=
      (ComputableInPolyTime.listAppend (encPair encNat encNat)).comp
        (computableInPolyTime_gluedClauseEdges.prod computableInPolyTime_gluedTorusEdges)
    exact encGraph_mk_polyTime hverts hedges
  unfold threeSATThreeToTriGraph
  have hnorm := computableInPolyTime_normCNF
  have hany : ComputableInPolyTime (fun φ : CNF ℕ => (normCNF φ).any List.isEmpty)
      encCNF encBool :=
    ComputableInPolyTime.anyWithInput hnorm
      ((ComputableInPolyTime.listIsEmpty' (encPair encNat encBool)).comp (by fun_prop))
  have hlen0 : ComputableInPolyTime (fun φ : CNF ℕ => decide ((normCNF φ).length = 0))
      encCNF encBool := by
    have := CNF.computableInPolyTime_length hnorm; fun_prop
  have hb2 := ComputableInPolyTime.ite' hlen0 (.const emptyTriGraph) (hbuild.comp hnorm)
  have hb1 := ComputableInPolyTime.ite' hany (.const noTriGraph) hb2
  exact (ComputableInPolyTime.ite' ThreeSATThree.computableInPolyTime_syntaxCheck hb1
    (.const noTriGraph)).of_enc_eq fun φ => congrArg _ (by
    dsimp only [Function.comp_apply]; simp only [decide_eq_true_eq])

/-! ### Structural Lemmas on Glued Graph -/

theorem clauseLitPos_spec {ψ : CNF ℕ} (hψ : NormProps ψ) {j : ℕ} (hj : j < ψ.length) {v : ℕ} :
    (clauseLitPos (ψ.getD j []) v < 3 →
      clauseLitPos (ψ.getD j []) v < (ψ.getD j []).length ∧
      ((ψ.getD j []).getD (clauseLitPos (ψ.getD j []) v) (0, false)).1 = v) ∧
    (clauseLitPos (ψ.getD j []) v = 3 →
      ∀ r' < (ψ.getD j []).length, ((ψ.getD j []).getD r' (0, false)).1 ≠ v) ∧
    clauseLitPos (ψ.getD j []) v ≤ 3 := by
  set c := ψ.getD j []
  have hcmem : c ∈ ψ := by
    rw [show c = ψ[j] from List.getD_eq_getElem ψ [] hj]; exact List.getElem_mem hj
  have hclen : c.length ≤ 3 := hψ.clause_len_le c hcmem
  unfold clauseLitPos
  split_ifs with h0 h1 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
    exact ⟨fun _ => h0, fun h => absurd h (by decide), by omega⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨fun _ => h1, fun h => absurd h (by decide), by omega⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact ⟨fun _ => h2, fun h => absurd h (by decide), by omega⟩
  · refine ⟨fun h => by omega, fun _ r' hr' => ?_, le_rfl⟩
    intro heq
    have : r' = 0 ∨ r' = 1 ∨ r' = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h0; exact h0 ⟨hr', heq⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1; exact h1 ⟨hr', heq⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2; exact h2 ⟨hr', heq⟩

theorem clauseLitPos_unique {ψ : CNF ℕ} (hψ : NormProps ψ) {j : ℕ} (hj : j < ψ.length)
    {r : ℕ} (hr : r < (ψ.getD j []).length) :
    clauseLitPos (ψ.getD j []) ((ψ.getD j []).getD r (0, false)).1 = r := by
  have hcmem : ψ.getD j [] ∈ ψ := by
    rw [List.getD_eq_getElem ψ [] hj]; exact List.getElem_mem hj
  have hnd := hψ.clause_nodup (ψ.getD j []) hcmem
  have hspec := clauseLitPos_spec hψ hj (v := ((ψ.getD j []).getD r (0, false)).1)
  have hlt3 : clauseLitPos (ψ.getD j []) ((ψ.getD j []).getD r (0, false)).1 < 3 := by
    by_contra hge
    have heq3 : clauseLitPos (ψ.getD j []) ((ψ.getD j []).getD r (0, false)).1 = 3 := by
      have := hspec.2.2; omega
    exact hspec.2.1 heq3 r hr rfl
  obtain ⟨hr1, hv1⟩ := hspec.1 hlt3
  have heq : ((ψ.getD j []).map Prod.fst)[clauseLitPos (ψ.getD j [])
      ((ψ.getD j []).getD r (0, false)).1]'(by rw [List.length_map]; exact hr1) =
      ((ψ.getD j []).map Prod.fst)[r]'(by rw [List.length_map]; exact hr) := by
    simp only [List.getElem_map]
    rw [← List.getD_eq_getElem (ψ.getD j []) (0, false) hr1,
      ← List.getD_eq_getElem (ψ.getD j []) (0, false) hr]
    exact hv1
  exact (List.Nodup.getElem_inj_iff hnd).1 heq

theorem occ_lt_three {ψ : CNF ℕ} (hψ : NormProps ψ) {j : ℕ} (hj : j < ψ.length)
    {r : ℕ} (hr : r < (ψ.getD j []).length) :
    (CNF.vars (ψ.take j)).count ((ψ.getD j []).getD r (0, false)).1 < 3 := by
  set c := ψ.getD j []
  set v := (c.getD r (0, false)).1
  have hsplit : ψ = ψ.take j ++ ψ.drop j := (List.take_append_drop j ψ).symm
  have hv_drop : v ∈ CNF.vars (ψ.drop j) := by
    rw [CNF.mem_vars]
    have hcmem : c ∈ ψ.drop j := by
      rw [show c = ψ[j] from List.getD_eq_getElem ψ [] hj]
      have h0 : 0 < (ψ.drop j).length := by rw [List.length_drop]; omega
      have hmem := List.getElem_mem h0
      simpa [List.getElem_drop] using hmem
    have hlmem : c.getD r (0, false) ∈ c := by
      rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
    exact ⟨c, hcmem, (c.getD r (0, false)).2, hlmem⟩
  have hcnt_pos : 1 ≤ (CNF.vars (ψ.drop j)).count v := List.count_pos_iff.2 hv_drop
  have hsum : ψ.vars.count v = (CNF.vars (ψ.take j)).count v + (CNF.vars (ψ.drop j)).count v := by
    have hfl : ψ.flatten = (ψ.take j).flatten ++ (ψ.drop j).flatten := by
      conv_lhs => rw [hsplit]; rw [List.flatten_append]
    simp only [CNF.vars, hfl, List.map_append, List.count_append]
  have hle := hψ.var_count_le v
  omega

theorem occ_strict_mono {ψ : CNF ℕ} {j1 j2 : ℕ} (hj1 : j1 < j2) (hj2 : j2 < ψ.length)
    {r1 : ℕ} (hr1 : r1 < (ψ.getD j1 []).length) :
    (CNF.vars (ψ.take j1)).count ((ψ.getD j1 []).getD r1 (0, false)).1 <
      (CNF.vars (ψ.take j2)).count ((ψ.getD j1 []).getD r1 (0, false)).1 := by
  set c1 := ψ.getD j1 []
  set v := (c1.getD r1 (0, false)).1
  have hsplit : ψ.take j2 = ψ.take j1 ++ (ψ.take j2).drop j1 := by
    have := (List.take_append_drop j1 (ψ.take j2)).symm
    rwa [List.take_take, Nat.min_eq_left hj1.le] at this
  have hv_in : v ∈ CNF.vars ((ψ.take j2).drop j1) := by
    rw [CNF.mem_vars]
    have hlen : j1 < (ψ.take j2).length := by rw [List.length_take]; omega
    have hcmem : c1 ∈ (ψ.take j2).drop j1 := by
      rw [show c1 = ψ[j1] from List.getD_eq_getElem ψ [] (lt_trans hj1 hj2)]
      have h0 : 0 < ((ψ.take j2).drop j1).length := by rw [List.length_drop]; omega
      have hmem := List.getElem_mem h0
      simpa [List.getElem_drop, List.getElem_take] using hmem
    have hlmem : c1.getD r1 (0, false) ∈ c1 := by
      rw [List.getD_eq_getElem _ _ hr1]; exact List.getElem_mem hr1
    exact ⟨c1, hcmem, (c1.getD r1 (0, false)).2, hlmem⟩
  have hcnt_pos : 1 ≤ (CNF.vars ((ψ.take j2).drop j1)).count v := List.count_pos_iff.2 hv_in
  have hsum : (CNF.vars (ψ.take j2)).count v =
      (CNF.vars (ψ.take j1)).count v + (CNF.vars ((ψ.take j2).drop j1)).count v := by
    have hfl : (ψ.take j2).flatten = (ψ.take j1).flatten ++ ((ψ.take j2).drop j1).flatten := by
      conv_lhs => rw [hsplit]; rw [List.flatten_append]
    simp only [CNF.vars, hfl, List.map_append, List.count_append]
  omega

private theorem nine_mul_add_k333PortVert_lt {j m r pos : ℕ} (hj : j < m) :
    9 * j + k333PortVert r pos < 9 * m := by
  have := k333PortVert_lt_nine r pos; omega

private theorem k333PortVert_eq_six_of_ne {r1 r2 pos1 pos2 : ℕ}
    (hr1 : r1 < 3) (hr2 : r2 < 3) (hp1 : pos1 < 3) (hp2 : pos2 < 3) (hne : r1 ≠ r2)
    (heq : k333PortVert r1 pos1 = k333PortVert r2 pos2) : k333PortVert r1 pos1 = 6 := by
  have hdec : ∀ a b c d : Fin 3, a.1 ≠ b.1 →
      k333PortVert a.1 c.1 = k333PortVert b.1 d.1 → k333PortVert a.1 c.1 = 6 := by decide
  exact hdec ⟨r1, hr1⟩ ⟨r2, hr2⟩ ⟨pos1, hp1⟩ ⟨pos2, hp2⟩ hne heq

private theorem torusVertexId_eq_own_of_ge {ψ : CNF ℕ} {vi p : ℕ}
    (h : ¬ torusVertexId ψ ψ.distinctVars vi p < 9 * ψ.length) :
    torusVertexId ψ ψ.distinctVars vi p = 9 * ψ.length + 48 * vi + p := by
  dsimp only [torusVertexId] at h ⊢
  split_ifs at h ⊢ with hj
  · exact absurd (nine_mul_add_k333PortVert_lt hj) h
  · rfl

theorem mem_buildGluedGraph_vertices_iff (ψ : CNF ℕ) (x : ℕ) :
    x ∈ (buildGluedGraph ψ).vertices ↔ x < 9 * ψ.length + 48 * ψ.distinctVars.length := by
  simp [buildGluedGraph, List.mem_range]

theorem torusPortPos_eq_self (occ : ℕ) (b : Bool) (pos : ℕ) (hpos : pos < 3) :
    torusPortPos occ b
      (if pos = 0 then 4 * (4 * occ)
       else if pos = 1 then 4 * (4 * occ + 1)
       else if b then 4 * (4 * occ) + 1 else 4 * (4 * occ + 1) + 3) = pos := by
  dsimp only [torusPortPos]; cases b <;> split_ifs <;> omega

theorem torusPortPos_lt_three_mem {occ : ℕ} {b : Bool} {p : ℕ}
    (h : torusPortPos occ b p < 3) : p ∈ torusPortAll occ := by
  dsimp only [torusPortPos] at h
  rw [mem_torusPortAll_iff]
  cases b <;> split_ifs at h <;> simp_all

theorem matchClause_unique {ψ : CNF ℕ} (hψ : NormProps ψ) {v p j1 j2 : ℕ}
    (hj1 : j1 < ψ.length) (hj2 : j2 < ψ.length)
    (hm1 : matchClause ψ v p j1 = true) (hm2 : matchClause ψ v p j2 = true) : j1 = j2 := by
  by_contra hne
  wlog hlt : j1 < j2 generalizing j1 j2
  · exact this hj2 hj1 hm2 hm1 (Ne.symm hne) (by omega)
  dsimp only [matchClause] at hm1 hm2
  split_ifs at hm1 with hr1
  split_ifs at hm2 with hr2
  simp only [decide_eq_true_eq] at hm1 hm2
  obtain ⟨hl1, hv1⟩ := (clauseLitPos_spec hψ hj1).1 hr1
  obtain ⟨hl2, hv2⟩ := (clauseLitPos_spec hψ hj2).1 hr2
  have hocc1 : (CNF.vars (ψ.take j1)).count v < 3 := by
    rw [← hv1]; exact occ_lt_three hψ hj1 hl1
  have hocc2 : (CNF.vars (ψ.take j2)).count v < 3 := by
    rw [← hv2]; exact occ_lt_three hψ hj2 hl2
  have hmono : (CNF.vars (ψ.take j1)).count v < (CNF.vars (ψ.take j2)).count v := by
    rw [← hv1]; exact occ_strict_mono hlt hj2 hl1
  exact (torus_port_not_adj hocc1 hocc2 (by omega)
    (torusPortPos_lt_three_mem hm1) (torusPortPos_lt_three_mem hm2)).1 rfl

theorem torusVertexId_lt_bound {ψ : CNF ℕ} (_hψ : NormProps ψ) {vi p : ℕ}
    (hvi : vi < ψ.distinctVars.length) (hp : p < 48) :
    torusVertexId ψ ψ.distinctVars vi p < 9 * ψ.length + 48 * ψ.distinctVars.length := by
  dsimp only [torusVertexId]
  split_ifs with hj
  · exact lt_of_lt_of_le (nine_mul_add_k333PortVert_lt hj) (Nat.le_add_right _ _)
  · omega

theorem torusVertexId_eq_clause_iff {ψ : CNF ℕ} (hψ : NormProps ψ) {vi p j u : ℕ}
    (_hvi : vi < ψ.distinctVars.length) (_hp : p < 48) (hj : j < ψ.length) (hu : u < 9) :
    torusVertexId ψ ψ.distinctVars vi p = 9 * j + u ↔
      clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0) < 3 ∧
      torusPortPos ((CNF.vars (ψ.take j)).count (ψ.distinctVars.getD vi 0))
        (((ψ.getD j []).getD (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0)) (0, false)).2)
        p < 3 ∧
      u = k333PortVert (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0))
        (torusPortPos ((CNF.vars (ψ.take j)).count (ψ.distinctVars.getD vi 0))
          (((ψ.getD j []).getD (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0))
            (0, false)).2) p) := by
  set vars := ψ.distinctVars
  set v := vars.getD vi 0
  set m := ψ.length
  set L := (List.range m).filter (matchClause ψ v p)
  set j0 := L.headD m
  have hj0_spec : (j0 < m → j0 ∈ L) ∧ (¬ j0 < m → L = []) := by
    cases hL : L with
    | nil =>
      refine ⟨fun h => by simp [j0, hL] at h, fun _ => rfl⟩
    | cons a as =>
      have ha : a ∈ L := by rw [hL]; exact List.mem_cons_self
      have ham : a < m := List.mem_range.1 (List.mem_filter.1 ha).1
      refine ⟨fun _ => by simp [j0, hL], fun h => by simp [j0, hL, ham] at h⟩
  constructor
  · intro heq
    dsimp only [torusVertexId] at heq
    change (if j0 < m then 9 * j0 + k333PortVert (clauseLitPos (ψ.getD j0 []) v)
      (torusPortPos ((CNF.vars (ψ.take j0)).count v)
        (((ψ.getD j0 []).getD (clauseLitPos (ψ.getD j0 []) v) (0, false)).2) p)
      else 9 * m + 48 * vi + p) = 9 * j + u at heq
    split_ifs at heq with hj0
    · have hj0_mem := List.mem_filter.1 (hj0_spec.1 hj0)
      have hj0m : matchClause ψ v p j0 = true := hj0_mem.2
      have hpcv0 := k333PortVert_lt_nine (clauseLitPos (ψ.getD j0 []) v)
        (torusPortPos ((CNF.vars (ψ.take j0)).count v)
          (((ψ.getD j0 []).getD (clauseLitPos (ψ.getD j0 []) v) (0, false)).2) p)
      have hjj : j0 = j := by omega
      have hu_eq : k333PortVert (clauseLitPos (ψ.getD j0 []) v)
          (torusPortPos ((CNF.vars (ψ.take j0)).count v)
            (((ψ.getD j0 []).getD (clauseLitPos (ψ.getD j0 []) v) (0, false)).2) p) = u := by
        omega
      dsimp only [matchClause] at hj0m
      split_ifs at hj0m with hr
      rw [hjj] at hr hj0m hu_eq
      exact ⟨hr, of_decide_eq_true hj0m, hu_eq.symm⟩
    · omega
  · rintro ⟨hr, hpos, hu_eq⟩
    have hmj : matchClause ψ v p j = true := by
      dsimp only [matchClause]; simp only [hr, ↓reduceIte, decide_eq_true_eq]; exact hpos
    have hj_in : j ∈ L := List.mem_filter.2 ⟨List.mem_range.2 hj, hmj⟩
    have hj0_lt : j0 < m := by
      by_contra hge
      have := hj0_spec.2 hge; simp [this] at hj_in
    have hj0_mem := List.mem_filter.1 (hj0_spec.1 hj0_lt)
    have hjj : j0 = j := matchClause_unique hψ hj0_lt hj hj0_mem.2 hmj
    dsimp only [torusVertexId]
    change (if j0 < m then 9 * j0 + k333PortVert (clauseLitPos (ψ.getD j0 []) v)
      (torusPortPos ((CNF.vars (ψ.take j0)).count v)
        (((ψ.getD j0 []).getD (clauseLitPos (ψ.getD j0 []) v) (0, false)).2) p)
      else 9 * m + 48 * vi + p) = 9 * j + u
    rw [ite_eq_left hj0_lt, hjj, hu_eq]

theorem torusVertexId_eq_own_iff {ψ : CNF ℕ} (_hψ : NormProps ψ)
    {vi1 vi2 p1 p2 : ℕ} (_hvi1 : vi1 < ψ.distinctVars.length) (_hvi2 : vi2 < ψ.distinctVars.length)
    (hp1 : p1 < 48) (hp2 : p2 < 48) :
    torusVertexId ψ ψ.distinctVars vi1 p1 = 9 * ψ.length + 48 * vi2 + p2 →
      vi1 = vi2 ∧ p1 = p2 := by
  intro heq
  dsimp only [torusVertexId] at heq
  split_ifs at heq with hj
  · exfalso
    have hlt : 9 * ψ.length + 48 * vi2 + p2 < 9 * ψ.length :=
      heq ▸ nine_mul_add_k333PortVert_lt hj
    omega
  · omega

theorem torusVertexId_inj {ψ : CNF ℕ} (hψ : NormProps ψ) {vi p1 p2 : ℕ}
    (hvi : vi < ψ.distinctVars.length) (hp1 : p1 < 48) (hp2 : p2 < 48)
    (heq : torusVertexId ψ ψ.distinctVars vi p1 = torusVertexId ψ ψ.distinctVars vi p2) :
    p1 = p2 := by
  by_cases hlt : torusVertexId ψ ψ.distinctVars vi p1 < 9 * ψ.length
  · set j := torusVertexId ψ ψ.distinctVars vi p1 / 9
    set u := torusVertexId ψ ψ.distinctVars vi p1 % 9
    have hj : j < ψ.length := by omega
    have hu : u < 9 := by omega
    have h1 : torusVertexId ψ ψ.distinctVars vi p1 = 9 * j + u := by omega
    have h2 : torusVertexId ψ ψ.distinctVars vi p2 = 9 * j + u := heq.symm.trans h1
    obtain ⟨hr, hpos1, hu1⟩ := (torusVertexId_eq_clause_iff hψ hvi hp1 hj hu).1 h1
    obtain ⟨_, hpos2, hu2⟩ := (torusVertexId_eq_clause_iff hψ hvi hp2 hj hu).1 h2
    have hpeq : torusPortPos ((CNF.vars (ψ.take j)).count (ψ.distinctVars.getD vi 0))
        (((ψ.getD j []).getD (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0)) (0, false)).2)
        p1 =
      torusPortPos ((CNF.vars (ψ.take j)).count (ψ.distinctVars.getD vi 0))
        (((ψ.getD j []).getD (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0)) (0, false)).2)
        p2 := by
      have hu12 : k333PortVert (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0)) _ =
          k333PortVert (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0)) _ :=
        hu1.symm.trans hu2
      exact k333PortVert_inj hpos1 hpos2 hu12
    dsimp only [torusPortPos] at hpos1 hpos2 hpeq
    split_ifs at hpos1 hpos2 hpeq <;> omega
  · exact (torusVertexId_eq_own_iff hψ hvi hvi hp2 hp1
      (heq.symm.trans (torusVertexId_eq_own_of_ge hlt))).2.symm

theorem torus_inter_no_adj {ψ : CNF ℕ} (hψ : NormProps ψ) {vi1 vi2 p1 p2 q1 q2 : ℕ}
    (hvi1 : vi1 < ψ.distinctVars.length) (hvi2 : vi2 < ψ.distinctVars.length) (hne : vi1 ≠ vi2)
    (hp1 : p1 < 48) (hp2 : p2 < 48) (hq1 : q1 < 48) (hq2 : q2 < 48)
    (heq_p : torusVertexId ψ ψ.distinctVars vi1 p1 = torusVertexId ψ ψ.distinctVars vi2 p2)
    (heq_q : torusVertexId ψ ψ.distinctVars vi1 q1 = torusVertexId ψ ψ.distinctVars vi2 q2)
    (hadj : torusAdj p1 q1 = true) : False := by
  have hp_lt : torusVertexId ψ ψ.distinctVars vi1 p1 < 9 * ψ.length := by
    by_contra hge
    exact hne (torusVertexId_eq_own_iff hψ hvi2 hvi1 hp2 hp1
      (heq_p.symm.trans (torusVertexId_eq_own_of_ge hge))).1.symm
  have hq_lt : torusVertexId ψ ψ.distinctVars vi1 q1 < 9 * ψ.length := by
    by_contra hge
    exact hne (torusVertexId_eq_own_iff hψ hvi2 hvi1 hq2 hq1
      (heq_q.symm.trans (torusVertexId_eq_own_of_ge hge))).1.symm
  set jp := torusVertexId ψ ψ.distinctVars vi1 p1 / 9
  set up := torusVertexId ψ ψ.distinctVars vi1 p1 % 9
  set jq := torusVertexId ψ ψ.distinctVars vi1 q1 / 9
  set uq := torusVertexId ψ ψ.distinctVars vi1 q1 % 9
  have hjp : jp < ψ.length := by omega
  have hup : up < 9 := by omega
  have hjq : jq < ψ.length := by omega
  have huq : uq < 9 := by omega
  have hp1_eq : torusVertexId ψ ψ.distinctVars vi1 p1 = 9 * jp + up := by omega
  have hp2_eq : torusVertexId ψ ψ.distinctVars vi2 p2 = 9 * jp + up := heq_p.symm.trans hp1_eq
  have hq1_eq : torusVertexId ψ ψ.distinctVars vi1 q1 = 9 * jq + uq := by omega
  have hq2_eq : torusVertexId ψ ψ.distinctVars vi2 q2 = 9 * jq + uq := heq_q.symm.trans hq1_eq
  obtain ⟨hrp1, hposp1, hup1⟩ := (torusVertexId_eq_clause_iff hψ hvi1 hp1 hjp hup).1 hp1_eq
  obtain ⟨hrp2, hposp2, hup2⟩ := (torusVertexId_eq_clause_iff hψ hvi2 hp2 hjp hup).1 hp2_eq
  obtain ⟨hrq1, hposq1, huq1⟩ := (torusVertexId_eq_clause_iff hψ hvi1 hq1 hjq huq).1 hq1_eq
  obtain ⟨hrq2, hposq2, huq2⟩ := (torusVertexId_eq_clause_iff hψ hvi2 hq2 hjq huq).1 hq2_eq
  have hjp_ne_jq : jp ≠ jq := by
    intro hjeq
    rw [← hjeq] at hrq1 hrq2 hposq1 hposq2 huq1 huq2
    have hneq : p1 ≠ q1 := fun heq => by subst heq; rw [torusAdj_irrefl] at hadj; simp at hadj
    have hv_ne : ψ.distinctVars.getD vi1 0 ≠ ψ.distinctVars.getD vi2 0 := by
      intro hv
      rw [List.getD_eq_getElem _ _ hvi1, List.getD_eq_getElem _ _ hvi2] at hv
      exact hne ((List.Nodup.getElem_inj_iff (CNF.nodup_distinctVars ψ)).1 hv)
    have hrp_ne : clauseLitPos (ψ.getD jp []) (ψ.distinctVars.getD vi1 0) ≠
        clauseLitPos (ψ.getD jp []) (ψ.distinctVars.getD vi2 0) := by
      intro hr
      have h1 := ((clauseLitPos_spec hψ hjp).1 hrp1).2
      have h2 := ((clauseLitPos_spec hψ hjp).1 hrp2).2
      rw [hr] at h1; exact hv_ne (h1.symm.trans h2)
    have hup_eq6 : up = 6 :=
      hup1.trans (k333PortVert_eq_six_of_ne hrp1 hrp2 hposp1 hposp2 hrp_ne (hup1.symm.trans hup2))
    have huq_eq6 : uq = 6 :=
      huq1.trans (k333PortVert_eq_six_of_ne hrq1 hrq2 hposq1 hposq2 hrp_ne (huq1.symm.trans huq2))
    exact hneq (torusVertexId_inj hψ hvi1 hp1 hq1 (by omega))
  have hv1_l1 := (clauseLitPos_spec hψ hjp).1 hrp1
  have hv1_l2 := (clauseLitPos_spec hψ hjq).1 hrq1
  have hocc1 : (CNF.vars (ψ.take jp)).count (ψ.distinctVars.getD vi1 0) < 3 := by
    rw [← hv1_l1.2]; exact occ_lt_three hψ hjp hv1_l1.1
  have hocc2 : (CNF.vars (ψ.take jq)).count (ψ.distinctVars.getD vi1 0) < 3 := by
    rw [← hv1_l2.2]; exact occ_lt_three hψ hjq hv1_l2.1
  have hocc_ne : (CNF.vars (ψ.take jp)).count (ψ.distinctVars.getD vi1 0) ≠
      (CNF.vars (ψ.take jq)).count (ψ.distinctVars.getD vi1 0) := by
    rcases lt_or_gt_of_ne hjp_ne_jq with hlt | hgt
    · exact ne_of_lt (by rw [← hv1_l1.2]; exact occ_strict_mono hlt hjq hv1_l1.1)
    · exact ne_of_gt (by rw [← hv1_l2.2]; exact occ_strict_mono hgt hjp hv1_l2.1)
  have hbad := (torus_port_not_adj hocc1 hocc2 hocc_ne
    (torusPortPos_lt_three_mem hposp1) (torusPortPos_lt_three_mem hposq1)).2
  rw [hadj] at hbad; simp at hbad

theorem glued_adj_iff {ψ : CNF ℕ} (hψ : NormProps ψ) {u v : ℕ} :
    (buildGluedGraph ψ).toSimpleGraph.Adj u v ↔
      (∃ j < ψ.length, ∃ a b : ℕ,
        k333ClauseAdj (ψ.getD j []).length a b = true ∧
        u = 9 * j + a ∧ v = 9 * j + b) ∨
      (∃ vi < ψ.distinctVars.length, ∃ p q : ℕ,
        torusAdj p q = true ∧
        u = torusVertexId ψ ψ.distinctVars vi p ∧
        v = torusVertexId ψ ψ.distinctVars vi q) := by
  rw [Graph.toSimpleGraph_adj]
  simp only [buildGluedGraph, List.mem_append, gluedClauseEdges, gluedTorusEdges,
    List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨_, (⟨j, hj, e, _, hmem⟩ | ⟨vi, hvi, e, he, hpair⟩) |
        (⟨j, hj, e, _, hmem⟩ | ⟨vi, hvi, e, he, hpair⟩)⟩
    · split_ifs at hmem with hadj
      · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        exact Or.inl ⟨j, hj, e.1, e.2, hadj, hmem.1, hmem.2⟩
      · simp at hmem
    · simp only [Prod.mk.injEq] at hpair
      exact Or.inr ⟨vi, hvi, e.1, e.2, (mem_torusEdges_iff e.1 e.2).1 (Or.inl he),
        hpair.1.symm, hpair.2.symm⟩
    · split_ifs at hmem with hadj
      · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        rw [k333ClauseAdj_symm] at hadj
        exact Or.inl ⟨j, hj, e.2, e.1, hadj, hmem.2, hmem.1⟩
      · simp at hmem
    · simp only [Prod.mk.injEq] at hpair
      have hadj := (mem_torusEdges_iff e.1 e.2).1 (Or.inl he)
      rw [torusAdj_symm] at hadj
      exact Or.inr ⟨vi, hvi, e.2, e.1, hadj, hpair.2.symm, hpair.1.symm⟩
  · rintro (⟨j, hj, a, b, hadj, rfl, rfl⟩ | ⟨vi, hvi, p, q, hadj, rfl, rfl⟩)
    · obtain ⟨ha9, hb9, hab⟩ := k333ClauseAdj_bounds hadj
      refine ⟨by omega, ?_⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · left; left; refine ⟨j, hj, (a, b), mem_k333Edges_of_lt hlt (k333ClauseAdj_to_k333Adj hadj),
          by simp only [hadj, ↓reduceIte, List.mem_singleton]⟩
      · right; left
        have hadj' : k333ClauseAdj (ψ.getD j []).length b a = true := by
          rwa [k333ClauseAdj_symm]
        refine ⟨j, hj, (b, a), mem_k333Edges_of_lt hgt (k333ClauseAdj_to_k333Adj hadj'),
          by simp only [hadj', ↓reduceIte, List.mem_singleton]⟩
    · obtain ⟨hp, hq⟩ := torusAdj_bounds hadj
      have hpq : p ≠ q := fun h => by subst h; rw [torusAdj_irrefl] at hadj; simp at hadj
      refine ⟨fun h => hpq (torusVertexId_inj hψ hvi hp hq h), ?_⟩
      rcases (mem_torusEdges_iff p q).2 hadj with h | h
      · left; right; exact ⟨vi, hvi, (p, q), h, rfl⟩
      · right; right; exact ⟨vi, hvi, (q, p), h, rfl⟩

theorem glued_clause_induced {ψ : CNF ℕ} (hψ : NormProps ψ) {j a b : ℕ}
    (hj : j < ψ.length) (ha : a < 9) (hb : b < 9)
    (hadj : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j + a) (9 * j + b)) :
    k333ClauseAdj (ψ.getD j []).length a b = true := by
  rcases (glued_adj_iff hψ).1 hadj with ⟨j', _, a', b', hc, h1, h2⟩ | ⟨vi, hvi, p, q, ht, h1, h2⟩
  · obtain ⟨ha', hb', _⟩ := k333ClauseAdj_bounds hc
    have : j' = j ∧ a' = a ∧ b' = b := by omega
    rcases this with ⟨rfl, rfl, rfl⟩; exact hc
  · obtain ⟨hp, hq⟩ := torusAdj_bounds ht
    obtain ⟨hr1, hpos1, hu1⟩ := (torusVertexId_eq_clause_iff hψ hvi hp hj ha).1 h1.symm
    obtain ⟨_, hpos2, hu2⟩ := (torusVertexId_eq_clause_iff hψ hvi hq hj hb).1 h2.symm
    have hne : a ≠ b := by
      intro heq; subst heq
      have := torusVertexId_inj hψ hvi hp hq (h1.symm.trans h2)
      subst this; rw [torusAdj_irrefl] at ht; simp at ht
    set r := clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0)
    have hr_lt : r < (ψ.getD j []).length := ((clauseLitPos_spec hψ hj).1 hr1).1
    have hlen_le : (ψ.getD j []).length ≤ 3 := by
      have hcmem : ψ.getD j [] ∈ ψ := by
        rw [List.getD_eq_getElem ψ [] hj]; exact List.getElem_mem hj
      exact hψ.clause_len_le _ hcmem
    rw [hu1, hu2] at hne ⊢
    set pos1 := torusPortPos _ _ p
    set pos2 := torusPortPos _ _ q
    have hpos_ne : pos1 ≠ pos2 := fun h => hne (by rw [h])
    have hdec : ∀ len : Fin 4, ∀ r pos1 pos2 : Fin 3,
        r.1 < len.1 → pos1.1 ≠ pos2.1 →
        k333ClauseAdj len.1 (k333PortVert r.1 pos1.1) (k333PortVert r.1 pos2.1) = true := by
      decide
    exact hdec ⟨(ψ.getD j []).length, by omega⟩ ⟨r, hr1⟩ ⟨pos1, hpos1⟩ ⟨pos2, hpos2⟩ hr_lt hpos_ne

theorem glued_torus_induced {ψ : CNF ℕ} (hψ : NormProps ψ) {vi p q : ℕ}
    (hvi : vi < ψ.distinctVars.length) (hp : p < 48) (hq : q < 48)
    (hadj : (buildGluedGraph ψ).toSimpleGraph.Adj
      (torusVertexId ψ ψ.distinctVars vi p) (torusVertexId ψ ψ.distinctVars vi q)) :
    torusAdj p q = true := by
  rcases (glued_adj_iff hψ).1 hadj with ⟨j, hj, a, b, hc, h1, h2⟩ | ⟨vi', hvi', p', q', ht, h1, h2⟩
  · obtain ⟨ha, hb, hab⟩ := k333ClauseAdj_bounds hc
    obtain ⟨hr, hpos1, _⟩ := (torusVertexId_eq_clause_iff hψ hvi hp hj ha).1 h1
    obtain ⟨_, hpos2, _⟩ := (torusVertexId_eq_clause_iff hψ hvi hq hj hb).1 h2
    set occ := (CNF.vars (ψ.take j)).count (ψ.distinctVars.getD vi 0)
    set pol := ((ψ.getD j []).getD (clauseLitPos (ψ.getD j []) (ψ.distinctVars.getD vi 0))
      (0, false)).2
    have hocc_lt : occ < 3 := by
      have hspec := (clauseLitPos_spec hψ hj).1 hr
      dsimp only [occ]; rw [← hspec.2]; exact occ_lt_three hψ hj hspec.1
    have hne : p ≠ q := by
      intro heq; subst heq; rw [h1] at h2
      exact hab (by omega)
    have hdec : ∀ o : Fin 3, ∀ pol : Bool, ∀ p q : Fin 48,
        p.1 ≠ q.1 → torusPortPos o.1 pol p.1 < 3 → torusPortPos o.1 pol q.1 < 3 →
        torusAdj p.1 q.1 = true := by decide
    exact hdec ⟨occ, hocc_lt⟩ pol ⟨p, hp⟩ ⟨q, hq⟩ hne hpos1 hpos2
  · by_cases heq : vi = vi'
    · subst heq
      obtain ⟨hp', hq'⟩ := torusAdj_bounds ht
      rw [torusVertexId_inj hψ hvi hp hp' h1, torusVertexId_inj hψ hvi hq hq' h2]
      exact ht
    · obtain ⟨hp', hq'⟩ := torusAdj_bounds ht
      exact (torus_inter_no_adj hψ hvi' hvi (Ne.symm heq) hp' hp hq' hq h1.symm h2.symm ht).elim

/-- Every triangle in `buildGluedGraph ψ` lies completely inside a single clause gadget or a
single torus gadget. -/
theorem glued_triangle_in_gadget {ψ : CNF ℕ} (hψ : NormProps ψ) {u v w : ℕ}
    (huv : (buildGluedGraph ψ).toSimpleGraph.Adj u v)
    (hvw : (buildGluedGraph ψ).toSimpleGraph.Adj v w)
    (huw : (buildGluedGraph ψ).toSimpleGraph.Adj u w) :
    (∃ j < ψ.length, ∃ a b c : ℕ, a < 9 ∧ b < 9 ∧ c < 9 ∧
      u = 9 * j + a ∧ v = 9 * j + b ∧ w = 9 * j + c) ∨
    (∃ vi < ψ.distinctVars.length, ∃ p q r : ℕ, p < 48 ∧ q < 48 ∧ r < 48 ∧
      u = torusVertexId ψ ψ.distinctVars vi p ∧
      v = torusVertexId ψ ψ.distinctVars vi q ∧
      w = torusVertexId ψ ψ.distinctVars vi r) := by
  have hbound_c : ∀ {len a b : ℕ}, k333ClauseAdj len a b = true → a < 9 ∧ b < 9 := fun h =>
    let hb := k333ClauseAdj_bounds h; ⟨hb.1, hb.2.1⟩
  rcases (glued_adj_iff hψ).1 huv with ⟨j1, hj1, a1, b1, hc1, hu1, hv1⟩ |
      ⟨vi1, hvi1, p1, q1, ht1, hu1, hv1⟩
  · obtain ⟨ha1, hb1⟩ := hbound_c hc1
    rcases (glued_adj_iff hψ).1 hvw with ⟨j2, hj2, a2, b2, hc2, hv2, hw2⟩ |
        ⟨vi2, hvi2, p2, q2, ht2, hv2, hw2⟩
    · obtain ⟨_, hb2⟩ := hbound_c hc2
      have : j1 = j2 := by omega
      subst this; exact Or.inl ⟨j1, hj1, a1, b1, b2, ha1, hb1, hb2, hu1, hv1, hw2⟩
    · rcases (glued_adj_iff hψ).1 huw with ⟨j3, hj3, a3, b3, hc3, hu3, hw3⟩ |
          ⟨vi3, hvi3, p3, q3, ht3, hu3, hw3⟩
      · obtain ⟨_, hb3⟩ := hbound_c hc3
        have : j1 = j3 := by omega
        subst this; exact Or.inl ⟨j1, hj1, a1, b1, b3, ha1, hb1, hb3, hu1, hv1, hw3⟩
      · obtain ⟨hp2, hq2⟩ := torusAdj_bounds ht2
        obtain ⟨hp3, hq3⟩ := torusAdj_bounds ht3
        by_cases hvi_eq : vi2 = vi3
        · subst hvi_eq
          exact Or.inr ⟨vi2, hvi2, p3, p2, q2, hp3, hp2, hq2, hu3, hv2, hw2⟩
        · have hw_lt : w < 9 * ψ.length := by
            by_contra hge
            exact hvi_eq (torusVertexId_eq_own_iff hψ hvi3 hvi2 hq3 hq2
              (hw3.symm.trans (hw2.trans (torusVertexId_eq_own_of_ge (hw2 ▸ hge))))).1.symm
          set jw := w / 9; set uw := w % 9
          have hjw : jw < ψ.length := by omega
          have huw' : uw < 9 := by omega
          have hw_eq : w = 9 * jw + uw := by omega
          by_cases hjw1 : jw = j1
          · subst hjw1; exact Or.inl ⟨jw, hjw, a1, b1, uw, ha1, hb1, huw', hu1, hv1, hw_eq⟩
          · obtain ⟨hrv, hposv, _⟩ :=
              (torusVertexId_eq_clause_iff hψ hvi2 hp2 hj1 hb1).1 (hv2.symm.trans hv1)
            obtain ⟨hrw, hposw, _⟩ :=
              (torusVertexId_eq_clause_iff hψ hvi2 hq2 hjw huw').1 (hw2.symm.trans hw_eq)
            have hv_l := (clauseLitPos_spec hψ hj1).1 hrv
            have hw_l := (clauseLitPos_spec hψ hjw).1 hrw
            have hocc1 : (CNF.vars (ψ.take j1)).count (ψ.distinctVars.getD vi2 0) < 3 := by
              rw [← hv_l.2]; exact occ_lt_three hψ hj1 hv_l.1
            have hocc2 : (CNF.vars (ψ.take jw)).count (ψ.distinctVars.getD vi2 0) < 3 := by
              rw [← hw_l.2]; exact occ_lt_three hψ hjw hw_l.1
            have hocc_ne : (CNF.vars (ψ.take j1)).count (ψ.distinctVars.getD vi2 0) ≠
                (CNF.vars (ψ.take jw)).count (ψ.distinctVars.getD vi2 0) := by
              rcases lt_or_gt_of_ne hjw1 with hlt' | hgt'
              · exact ne_of_gt (by rw [← hw_l.2]; exact occ_strict_mono hlt' hj1 hw_l.1)
              · exact ne_of_lt (by rw [← hv_l.2]; exact occ_strict_mono hgt' hjw hv_l.1)
            have hbad := (torus_port_not_adj hocc1 hocc2 hocc_ne
              (torusPortPos_lt_three_mem hposv) (torusPortPos_lt_three_mem hposw)).2
            rw [ht2] at hbad; simp at hbad
  · obtain ⟨hp1, hq1⟩ := torusAdj_bounds ht1
    rcases (glued_adj_iff hψ).1 hvw with ⟨j2, hj2, a2, b2, hc2, hv2, hw2⟩ |
        ⟨vi2, hvi2, p2, q2, ht2, hv2, hw2⟩
    · obtain ⟨ha2, hb2⟩ := hbound_c hc2
      rcases (glued_adj_iff hψ).1 huw with ⟨j3, hj3, a3, b3, hc3, hu3, hw3⟩ |
          ⟨vi3, hvi3, p3, q3, ht3, hu3, hw3⟩
      · obtain ⟨ha3, _⟩ := hbound_c hc3
        have : j2 = j3 := by omega
        subst this; exact Or.inl ⟨j2, hj2, a3, a2, b2, ha3, ha2, hb2, hu3, hv2, hw2⟩
      · obtain ⟨hp3, hq3⟩ := torusAdj_bounds ht3
        by_cases hvi_eq : vi1 = vi3
        · subst hvi_eq; exact Or.inr ⟨vi1, hvi1, p1, q1, q3, hp1, hq1, hq3, hu1, hv1, hw3⟩
        · have hu_lt : u < 9 * ψ.length := by
            by_contra hge
            exact hvi_eq (torusVertexId_eq_own_iff hψ hvi3 hvi1 hp3 hp1
              (hu3.symm.trans (hu1.trans (torusVertexId_eq_own_of_ge (hu1 ▸ hge))))).1.symm
          set ju := u / 9; set uu := u % 9
          have hju : ju < ψ.length := by omega
          have huu : uu < 9 := by omega
          have hu_eq : u = 9 * ju + uu := by omega
          by_cases hju2 : ju = j2
          · subst hju2; exact Or.inl ⟨ju, hju, uu, a2, b2, huu, ha2, hb2, hu_eq, hv2, hw2⟩
          · obtain ⟨hru, hposu, _⟩ :=
              (torusVertexId_eq_clause_iff hψ hvi1 hp1 hju huu).1 (hu1.symm.trans hu_eq)
            obtain ⟨hrv, hposv, _⟩ :=
              (torusVertexId_eq_clause_iff hψ hvi1 hq1 hj2 ha2).1 (hv1.symm.trans hv2)
            have hu_l := (clauseLitPos_spec hψ hju).1 hru
            have hv_l := (clauseLitPos_spec hψ hj2).1 hrv
            have hocc1 : (CNF.vars (ψ.take ju)).count (ψ.distinctVars.getD vi1 0) < 3 := by
              rw [← hu_l.2]; exact occ_lt_three hψ hju hu_l.1
            have hocc2 : (CNF.vars (ψ.take j2)).count (ψ.distinctVars.getD vi1 0) < 3 := by
              rw [← hv_l.2]; exact occ_lt_three hψ hj2 hv_l.1
            have hocc_ne : (CNF.vars (ψ.take ju)).count (ψ.distinctVars.getD vi1 0) ≠
                (CNF.vars (ψ.take j2)).count (ψ.distinctVars.getD vi1 0) := by
              rcases lt_or_gt_of_ne hju2 with hlt' | hgt'
              · exact ne_of_lt (by rw [← hu_l.2]; exact occ_strict_mono hlt' hj2 hu_l.1)
              · exact ne_of_gt (by rw [← hv_l.2]; exact occ_strict_mono hgt' hju hv_l.1)
            have hbad := (torus_port_not_adj hocc1 hocc2 hocc_ne
              (torusPortPos_lt_three_mem hposu) (torusPortPos_lt_three_mem hposv)).2
            rw [ht1] at hbad; simp at hbad
    · obtain ⟨hp2, hq2⟩ := torusAdj_bounds ht2
      by_cases hvi12 : vi1 = vi2
      · subst hvi12; exact Or.inr ⟨vi1, hvi1, p1, q1, q2, hp1, hq1, hq2, hu1, hv1, hw2⟩
      · rcases (glued_adj_iff hψ).1 huw with ⟨j3, hj3, a3, b3, hc3, hu3, hw3⟩ |
            ⟨vi3, hvi3, p3, q3, ht3, hu3, hw3⟩
        · obtain ⟨ha3, hb3⟩ := hbound_c hc3
          have hv_lt : v < 9 * ψ.length := by
            by_contra hge
            exact hvi12 (torusVertexId_eq_own_iff hψ hvi2 hvi1 hp2 hq1
              (hv2.symm.trans (hv1.trans (torusVertexId_eq_own_of_ge (hv1 ▸ hge))))).1.symm
          set jv := v / 9; set uv := v % 9
          have hjv : jv < ψ.length := by omega
          have huv' : uv < 9 := by omega
          have hv_eq : v = 9 * jv + uv := by omega
          by_cases hjv3 : jv = j3
          · subst hjv3; exact Or.inl ⟨jv, hjv, a3, uv, b3, ha3, huv', hb3, hu3, hv_eq, hw3⟩
          · obtain ⟨hru, hposu, _⟩ :=
              (torusVertexId_eq_clause_iff hψ hvi1 hp1 hj3 ha3).1 (hu1.symm.trans hu3)
            obtain ⟨hrv, hposv, _⟩ :=
              (torusVertexId_eq_clause_iff hψ hvi1 hq1 hjv huv').1 (hv1.symm.trans hv_eq)
            have hu_l := (clauseLitPos_spec hψ hj3).1 hru
            have hv_l := (clauseLitPos_spec hψ hjv).1 hrv
            have hocc1 : (CNF.vars (ψ.take j3)).count (ψ.distinctVars.getD vi1 0) < 3 := by
              rw [← hu_l.2]; exact occ_lt_three hψ hj3 hu_l.1
            have hocc2 : (CNF.vars (ψ.take jv)).count (ψ.distinctVars.getD vi1 0) < 3 := by
              rw [← hv_l.2]; exact occ_lt_three hψ hjv hv_l.1
            have hocc_ne : (CNF.vars (ψ.take j3)).count (ψ.distinctVars.getD vi1 0) ≠
                (CNF.vars (ψ.take jv)).count (ψ.distinctVars.getD vi1 0) := by
              rcases lt_or_gt_of_ne hjv3 with hlt' | hgt'
              · exact ne_of_gt (by rw [← hv_l.2]; exact occ_strict_mono hlt' hj3 hv_l.1)
              · exact ne_of_lt (by rw [← hu_l.2]; exact occ_strict_mono hgt' hjv hu_l.1)
            have hbad := (torus_port_not_adj hocc1 hocc2 hocc_ne
              (torusPortPos_lt_three_mem hposu) (torusPortPos_lt_three_mem hposv)).2
            rw [ht1] at hbad; simp at hbad
        · obtain ⟨hp3, hq3⟩ := torusAdj_bounds ht3
          by_cases hvi13 : vi1 = vi3
          · subst hvi13; exact Or.inr ⟨vi1, hvi1, p1, q1, q3, hp1, hq1, hq3, hu1, hv1, hw3⟩
          · by_cases hvi23 : vi2 = vi3
            · subst hvi23; exact Or.inr ⟨vi2, hvi2, p3, p2, q2, hp3, hp2, hq2, hu3, hv2, hw2⟩
            · have hv_lt : v < 9 * ψ.length := by
                by_contra hge
                exact hvi12 (torusVertexId_eq_own_iff hψ hvi2 hvi1 hp2 hq1
                  (hv2.symm.trans (hv1.trans (torusVertexId_eq_own_of_ge (hv1 ▸ hge))))).1.symm
              have hu_lt : u < 9 * ψ.length := by
                by_contra hge
                exact hvi13 (torusVertexId_eq_own_iff hψ hvi3 hvi1 hp3 hp1
                  (hu3.symm.trans (hu1.trans (torusVertexId_eq_own_of_ge (hu1 ▸ hge))))).1.symm
              set ju := u / 9; set uu := u % 9
              set jv := v / 9; set uv := v % 9
              have hju : ju < ψ.length := by omega
              have huu : uu < 9 := by omega
              have hjv : jv < ψ.length := by omega
              have huv' : uv < 9 := by omega
              have hu_eq : u = 9 * ju + uu := by omega
              have hv_eq : v = 9 * jv + uv := by omega
              obtain ⟨hru, hposu, hu1'⟩ :=
                (torusVertexId_eq_clause_iff hψ hvi1 hp1 hju huu).1 (hu1.symm.trans hu_eq)
              obtain ⟨hrv, hposv, hv1'⟩ :=
                (torusVertexId_eq_clause_iff hψ hvi1 hq1 hjv huv').1 (hv1.symm.trans hv_eq)
              by_cases hjuv : ju = jv
              · rw [← hjuv] at hrv hposv hv1' hv_eq
                obtain ⟨hru3, hposu3, hu3'⟩ :=
                  (torusVertexId_eq_clause_iff hψ hvi3 hp3 hju huu).1 (hu3.symm.trans hu_eq)
                obtain ⟨hrv2, hposv2, hv2'⟩ :=
                  (torusVertexId_eq_clause_iff hψ hvi2 hp2 hju huv').1 (hv2.symm.trans hv_eq)
                have hneq_u : u ≠ v := huv.ne
                have hu6 : uu = 6 := by
                  have h1 : ψ.distinctVars.getD vi1 0 ≠ ψ.distinctVars.getD vi3 0 := by
                    intro h
                    rw [List.getD_eq_getElem _ _ hvi1, List.getD_eq_getElem _ _ hvi3] at h
                    exact hvi13 ((List.Nodup.getElem_inj_iff (CNF.nodup_distinctVars ψ)).1 h)
                  have hrne : clauseLitPos (ψ.getD ju []) (ψ.distinctVars.getD vi1 0) ≠
                      clauseLitPos (ψ.getD ju []) (ψ.distinctVars.getD vi3 0) := by
                    intro hr
                    have ha := ((clauseLitPos_spec hψ hju).1 hru).2
                    have hb := ((clauseLitPos_spec hψ hju).1 hru3).2
                    rw [hr] at ha; exact h1 (ha.symm.trans hb)
                  exact hu1'.trans (k333PortVert_eq_six_of_ne hru hru3 hposu hposu3 hrne
                    (hu1'.symm.trans hu3'))
                have hv6 : uv = 6 := by
                  have h1 : ψ.distinctVars.getD vi1 0 ≠ ψ.distinctVars.getD vi2 0 := by
                    intro h
                    rw [List.getD_eq_getElem _ _ hvi1, List.getD_eq_getElem _ _ hvi2] at h
                    exact hvi12 ((List.Nodup.getElem_inj_iff (CNF.nodup_distinctVars ψ)).1 h)
                  have hrne : clauseLitPos (ψ.getD ju []) (ψ.distinctVars.getD vi1 0) ≠
                      clauseLitPos (ψ.getD ju []) (ψ.distinctVars.getD vi2 0) := by
                    intro hr
                    have ha := ((clauseLitPos_spec hψ hju).1 hrv).2
                    have hb := ((clauseLitPos_spec hψ hju).1 hrv2).2
                    rw [hr] at ha; exact h1 (ha.symm.trans hb)
                  exact hv1'.trans (k333PortVert_eq_six_of_ne hrv hrv2 hposv hposv2 hrne
                    (hv1'.symm.trans hv2'))
                exact (hneq_u (by omega)).elim
              · have hu_l := (clauseLitPos_spec hψ hju).1 hru
                have hv_l := (clauseLitPos_spec hψ hjv).1 hrv
                have hocc1 : (CNF.vars (ψ.take ju)).count (ψ.distinctVars.getD vi1 0) < 3 := by
                  rw [← hu_l.2]; exact occ_lt_three hψ hju hu_l.1
                have hocc2 : (CNF.vars (ψ.take jv)).count (ψ.distinctVars.getD vi1 0) < 3 := by
                  rw [← hv_l.2]; exact occ_lt_three hψ hjv hv_l.1
                have hocc_ne : (CNF.vars (ψ.take ju)).count (ψ.distinctVars.getD vi1 0) ≠
                    (CNF.vars (ψ.take jv)).count (ψ.distinctVars.getD vi1 0) := by
                  rcases lt_or_gt_of_ne hjuv with hlt' | hgt'
                  · exact ne_of_lt (by rw [← hu_l.2]; exact occ_strict_mono hlt' hjv hu_l.1)
                  · exact ne_of_gt (by rw [← hv_l.2]; exact occ_strict_mono hgt' hju hv_l.1)
                have hbad := (torus_port_not_adj hocc1 hocc2 hocc_ne
                  (torusPortPos_lt_three_mem hposu) (torusPortPos_lt_three_mem hposv)).2
                rw [ht1] at hbad; simp at hbad

/-- Every output of `buildGluedGraph` (for normalized `ψ`) is $K_4$-free. -/
theorem buildGluedGraph_k4Free {ψ : CNF ℕ} (hψ : NormProps ψ) :
    (buildGluedGraph ψ).induced.CliqueFree 4 := by
  intro S hS
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz⟩ :
      ∃ u v w z : {v // v ∈ (buildGluedGraph ψ).vertices},
        (buildGluedGraph ψ).induced.Adj u v ∧ (buildGluedGraph ψ).induced.Adj u w ∧
        (buildGluedGraph ψ).induced.Adj u z ∧ (buildGluedGraph ψ).induced.Adj v w ∧
        (buildGluedGraph ψ).induced.Adj v z ∧ (buildGluedGraph ψ).induced.Adj w z := by
    obtain ⟨u, S1, hS1u, hS1eq, hS1c⟩ :=
      Finset.card_eq_succ.1 (by have := hS.2; omega : S.card = 3 + 1)
    obtain ⟨v, S2, hS2v, hS2eq, hS2c⟩ := Finset.card_eq_succ.1 (by omega : S1.card = 2 + 1)
    obtain ⟨w, S3, hS3w, hS3eq, hS3c⟩ := Finset.card_eq_succ.1 (by omega : S2.card = 1 + 1)
    obtain ⟨z, hS3eq'⟩ := Finset.card_eq_one.1 hS3c
    have hSeq : S = insert u (insert v (insert w {z})) := by
      rw [← hS1eq, ← hS2eq, ← hS3eq, hS3eq']
    have hcl := hS.1
    have hu' : u ∈ S := by rw [hSeq]; simp
    have hv' : v ∈ S := by rw [hSeq]; simp
    have hw' : w ∈ S := by rw [hSeq]; simp
    have hz' : z ∈ S := by rw [hSeq]; simp
    have hv_in1 : v ∈ S1 := by rw [← hS2eq]; simp
    have hw_in1 : w ∈ S1 := by rw [← hS2eq, ← hS3eq]; simp
    have hz_in1 : z ∈ S1 := by rw [← hS2eq, ← hS3eq, hS3eq']; simp
    have hw_in2 : w ∈ S2 := by rw [← hS3eq]; simp
    have hz_in2 : z ∈ S2 := by rw [← hS3eq, hS3eq']; simp
    have hz_in3 : z ∈ S3 := by rw [hS3eq']; simp
    exact ⟨u, v, w, z,
      hcl hu' hv' (fun h => hS1u (h ▸ hv_in1)),
      hcl hu' hw' (fun h => hS1u (h ▸ hw_in1)),
      hcl hu' hz' (fun h => hS1u (h ▸ hz_in1)),
      hcl hv' hw' (fun h => hS2v (h ▸ hw_in2)),
      hcl hv' hz' (fun h => hS2v (h ▸ hz_in2)),
      hcl hw' hz' (fun h => hS3w (h ▸ hz_in3))⟩
  rw [Graph.induced_adj] at huv huw huz hvw hvz hwz
  have h1 := glued_triangle_in_gadget hψ huv hvw huw
  have h2 := glued_triangle_in_gadget hψ huv hvz huz
  have h3 := glued_triangle_in_gadget hψ huw hwz huz
  have hcl_4 : ∀ j < ψ.length, ∀ a b c d : ℕ, a < 9 → b < 9 → c < 9 → d < 9 →
      u.1 = 9 * j + a → v.1 = 9 * j + b → w.1 = 9 * j + c → z.1 = 9 * j + d → False := by
    intro j hj a b c d ha hb hc hd hu hv hw hz
    have e1 := glued_clause_induced hψ hj ha hb (hu ▸ hv ▸ huv)
    have e2 := glued_clause_induced hψ hj ha hc (hu ▸ hw ▸ huw)
    have e3 := glued_clause_induced hψ hj ha hd (hu ▸ hz ▸ huz)
    have e4 := glued_clause_induced hψ hj hb hc (hv ▸ hw ▸ hvw)
    have e5 := glued_clause_induced hψ hj hb hd (hv ▸ hz ▸ hvz)
    have e6 := glued_clause_induced hψ hj hc hd (hw ▸ hz ▸ hwz)
    exact k333_k4Free (k333ClauseAdj_to_k333Adj e1) (k333ClauseAdj_to_k333Adj e2)
      (k333ClauseAdj_to_k333Adj e3) (k333ClauseAdj_to_k333Adj e4)
      (k333ClauseAdj_to_k333Adj e5) (k333ClauseAdj_to_k333Adj e6)
  have htor_4 : ∀ vi < ψ.distinctVars.length, ∀ p q r s : ℕ,
      p < 48 → q < 48 → r < 48 → s < 48 →
      u.1 = torusVertexId ψ ψ.distinctVars vi p →
      v.1 = torusVertexId ψ ψ.distinctVars vi q →
      w.1 = torusVertexId ψ ψ.distinctVars vi r →
      z.1 = torusVertexId ψ ψ.distinctVars vi s → False := by
    intro vi hvi p q r s hp hq hr hs hu hv hw hz
    exact torus_k4Free
      (glued_torus_induced hψ hvi hp hq (hu ▸ hv ▸ huv))
      (glued_torus_induced hψ hvi hp hr (hu ▸ hw ▸ huw))
      (glued_torus_induced hψ hvi hp hs (hu ▸ hz ▸ huz))
      (glued_torus_induced hψ hvi hq hr (hv ▸ hw ▸ hvw))
      (glued_torus_induced hψ hvi hq hs (hv ▸ hz ▸ hvz))
      (glued_torus_induced hψ hvi hr hs (hw ▸ hz ▸ hwz))
  rcases h1 with ⟨j1, hj1, a1, b1, c1, ha1, hb1, hc1, hu1, hv1, hw1⟩ |
      ⟨vi1, hvi1, p1, q1, r1, hp1, hq1, hr1, hu1, hv1, hw1⟩
  · rcases h2 with ⟨j2, _, _, _, d2, _, _, hd2, _, _, hz2⟩ |
        ⟨vi2, hvi2, p2, q2, s2, hp2, hq2, hs2, hu2, hv2, hz2⟩
    · have : j1 = j2 := by omega
      subst this; exact hcl_4 j1 hj1 a1 b1 c1 d2 ha1 hb1 hc1 hd2 hu1 hv1 hw1 hz2
    · rcases h3 with ⟨j3, _, _, _, d3, _, _, hd3, _, _, hz3⟩ |
          ⟨vi3, hvi3, p3, r3, s3, hp3, hr3, hs3, hu3, hw3, hz3⟩
      · have : j1 = j3 := by omega
        subst this; exact hcl_4 j1 hj1 a1 b1 c1 d3 ha1 hb1 hc1 hd3 hu1 hv1 hw1 hz3
      · by_cases hvi : vi2 = vi3
        · subst hvi; exact htor_4 vi2 hvi2 p2 q2 r3 s2 hp2 hq2 hr3 hs2 hu2 hv2 hw3 hz2
        · exact torus_inter_no_adj hψ hvi2 hvi3 hvi hp2 hp3 hs2 hs3
            (hu2.symm.trans hu3) (hz2.symm.trans hz3)
            (glued_torus_induced hψ hvi2 hp2 hs2 (hu2 ▸ hz2 ▸ huz))
  · rcases h2 with ⟨j2, hj2, a2, b2, d2, ha2, hb2, hd2, hu2, hv2, hz2⟩ |
        ⟨vi2, hvi2, p2, q2, s2, hp2, hq2, hs2, hu2, hv2, hz2⟩
    · rcases h3 with ⟨j3, _, _, c3, _, _, hc3, _, _, hw3, _⟩ |
          ⟨vi3, hvi3, p3, r3, s3, hp3, hr3, hs3, hu3, hw3, hz3⟩
      · have : j2 = j3 := by omega
        subst this; exact hcl_4 j2 hj2 a2 b2 c3 d2 ha2 hb2 hc3 hd2 hu2 hv2 hw3 hz2
      · by_cases hvi : vi1 = vi3
        · subst hvi; exact htor_4 vi1 hvi1 p1 q1 r1 s3 hp1 hq1 hr1 hs3 hu1 hv1 hw1 hz3
        · exact torus_inter_no_adj hψ hvi1 hvi3 hvi hp1 hp3 hr1 hr3
            (hu1.symm.trans hu3) (hw1.symm.trans hw3)
            (glued_torus_induced hψ hvi1 hp1 hr1 (hu1 ▸ hw1 ▸ huw))
    · by_cases hvi : vi1 = vi2
      · subst hvi; exact htor_4 vi1 hvi1 p1 q1 r1 s2 hp1 hq1 hr1 hs2 hu1 hv1 hw1 hz2
      · exact torus_inter_no_adj hψ hvi1 hvi2 hvi hp1 hp2 hq1 hq2
          (hu1.symm.trans hu2) (hv1.symm.trans hv2)
          (glued_torus_induced hψ hvi1 hp1 hq1 (hu1 ▸ hv1 ▸ huv))

/-- Every output of `threeSATThreeToTriGraph` is $K_4$-free. -/
theorem threeSATThreeToTriGraph_k4Free (φ : CNF ℕ) :
    (threeSATThreeToTriGraph φ).induced.CliqueFree 4 := by
  unfold threeSATThreeToTriGraph
  dsimp only
  by_cases hsyn : ThreeSATThree.syntaxCheck φ = true
  · rw [ite_eq_left hsyn]
    by_cases hany : (normCNF φ).any List.isEmpty = true
    · rw [ite_eq_left hany]; exact noTriGraph_k4Free
    · rw [ite_eq_right hany]
      by_cases hlen : (normCNF φ).length = 0
      · rw [ite_eq_left hlen]; exact (mem_K4FreeTrianglePartition.1 emptyTriGraph_mem).1
      · rw [ite_eq_right hlen]
        exact buildGluedGraph_k4Free (normCNF_props ((ThreeSATThree.syntaxCheck_iff φ).1 hsyn)
          (Bool.eq_false_iff.2 hany))
  · rw [ite_eq_right hsyn]; exact noTriGraph_k4Free

end Cslib.Complexity
