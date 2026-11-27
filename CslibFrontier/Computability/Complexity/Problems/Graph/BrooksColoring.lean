/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Constructive Polynomial-Time Brooks Coloring (Algorithm, Poly-Time, and Core Specs)

This module defines the executable polynomial-time Brooks coloring algorithm on
`Cslib.Complexity.Graph` together with graph complementation, BFS ordering, greedy coloring,
`K_{k+1}`-component detection, and their polynomial-time computability and core specifications.
The Lovász cherry existence proof and full Brooks correctness theorem are proved in
`BrooksColoringProof.lean`.
-/

public section

namespace Cslib.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Graph Complement and Core Executable Primitives -/

/-- Complement of a `Cslib.Complexity.Graph` on its deduplicated vertex list. -/
@[expose]
def complGraph (G : Graph) : Graph :=
  let V := G.distinctVertices
  { vertices := V
    edges := V.flatMap fun u ↦ (V.filter fun v ↦ decide (u < v) && !G.adjBool u v).map fun v ↦
      (u, v) }

/-- Degree of `v` inside vertex subset `S` in graph `H`. -/
@[expose]
def subsetDegBool (H : Graph) (S : List ℕ) (v : ℕ) : ℕ :=
  (S.filter fun w ↦ H.adjBool v w).length

/-- One BFS layer-extension step in `H` restricted to `S`. -/
@[expose]
def bfsStep (H : Graph) (S : List ℕ) (acc : List ℕ) : List ℕ :=
  acc ++ S.filter fun w ↦ !acc.contains w && acc.any fun u ↦ H.adjBool u w

/-- BFS reachability order from root `r` in `H` restricted to `S` (run for `S.length` steps). -/
@[expose]
def bfsOrder (H : Graph) (S : List ℕ) (r : ℕ) : List ℕ :=
  (List.replicate S.length true).foldl (fun acc _ ↦ bfsStep H S acc) [r]

/-- Smallest color in `{0, ..., k - 1}` not used by any `H`-neighbor of `v` in `cols`. -/
@[expose]
def firstFreeColor (H : Graph) (k : ℕ) (cols : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  ((List.range k).filter fun c ↦
    !(cols.any fun p ↦ H.adjBool v p.1 && decide (p.2 = c))).headD 0

/-- One greedy coloring step along `v`. -/
@[expose]
def greedyColorStep (H : Graph) (k : ℕ) (cols : List (ℕ × ℕ)) (v : ℕ) : List (ℕ × ℕ) :=
  if cols.any fun p ↦ decide (p.1 = v) then cols
  else (v, firstFreeColor H k cols v) :: cols

/-- Greedy `< k`-coloring of `order` extending pre-colored pairs `initCol`. -/
@[expose]
def greedyColor (H : Graph) (k : ℕ) (order : List ℕ) (initCol : List (ℕ × ℕ)) :
    List (ℕ × ℕ) :=
  order.foldl (greedyColorStep H k) initCol

/-- Color assigned to `v` in association list `cols` (default `0`). -/
@[expose]
def lookupColor (cols : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  ((cols.filter fun p ↦ decide (p.1 = v)).headD (0, 0)).2

/-- Swap colors `c₁` and `c₂`, leaving all other colors unchanged. -/
@[expose]
def swapColor (c₁ c₂ c : ℕ) : ℕ :=
  if c = c₁ then c₂ else if c = c₂ then c₁ else c

/-- Whether `H` has a `K_{k+1}` connected component (every vertex in the component has `H`-degree
`k` and the component has `k + 1` vertices). -/
@[expose]
def hasCompleteCompBool (H : Graph) (k : ℕ) : Bool :=
  let V := H.distinctVertices
  V.any fun u ↦
    let C := bfsOrder H V u
    decide (C.length = k + 1) && C.all fun x ↦ decide (subsetDegBool H V x = k)

/-- Test whether `(x, y, z)` is a Lovász cherry in component `C` of `H`. -/
@[expose]
def isLovaszCherry (H : Graph) (C : List ℕ) (t : (ℕ × ℕ) × ℕ) : Bool :=
  let x := t.1.1
  let y := t.1.2
  let z := t.2
  H.adjBool x y && H.adjBool x z && !H.adjBool y z && decide (y ≠ z) &&
    let rem := C.filter fun w ↦ decide (w ≠ y) && decide (w ≠ z)
    decide ((bfsOrder H rem x).length = rem.length)

/-- Constructive `k`-coloring of a single connected component `C` of `H`:
1. If some `r ∈ C` has degree `< k`, reverse-BFS greedy from `r`.
2. Else if some `x ∈ C` is a cut-vertex of `C`, split `C \ {x}` into `S₁` and `S₂`, reverse-BFS
   greedy both `x :: S₁` and `x :: S₂` from `x`, and align the color of `x`.
3. Else find a Lovász cherry `(x, y, z)` in `C`, pre-color `y, z ↦ 0`, and reverse-BFS greedy
   `C \ {y, z}` from `x`. -/
@[expose]
def colorComponent (H : Graph) (k : ℕ) (C : List ℕ) : List (ℕ × ℕ) :=
  let lowDeg := C.filter fun v ↦ decide (subsetDegBool H C v < k)
  if !lowDeg.isEmpty then
    greedyColor H k (bfsOrder H C (lowDeg.headD 0)).reverse []
  else
    let cutVerts := C.filter fun v ↦
      let Cv := C.filter fun w ↦ decide (w ≠ v)
      decide ((bfsOrder H Cv (Cv.headD 0)).length < Cv.length)
    if !cutVerts.isEmpty then
      let x := cutVerts.headD 0
      let Cx := C.filter fun w ↦ decide (w ≠ x)
      let S1 := bfsOrder H Cx (Cx.headD 0)
      let S2 := Cx.filter fun w ↦ !S1.contains w
      let col1 := greedyColor H k (bfsOrder H (x :: S1) x).reverse []
      let col2 := greedyColor H k (bfsOrder H (x :: S2) x).reverse []
      let c1 := lookupColor col1 x
      let c2 := lookupColor col2 x
      col1 ++ (col2.filter fun p ↦ decide (p.1 ≠ x)).map fun p ↦ (p.1, swapColor c1 c2 p.2)
    else
      let cherries := (C.flatMap fun x ↦ C.flatMap fun y ↦ C.map fun z ↦ ((x, y), z)).filter
        (isLovaszCherry H C)
      if !cherries.isEmpty then
        let t := cherries.headD ((0, 0), 0)
        let x := t.1.1
        let y := t.1.2
        let z := t.2
        let rem := C.filter fun w ↦ decide (w ≠ y) && decide (w ≠ z)
        greedyColor H k (bfsOrder H rem x).reverse [(y, 0), (z, 0)]
      else
        greedyColor H (k + 1) C []

/-- Canonical connected components of `H` (each component emitted once at its minimum vertex). -/
@[expose]
def canonicalComponents (H : Graph) : List (List ℕ) :=
  let V := H.distinctVertices
  V.flatMap fun u ↦
    let C := bfsOrder H V u
    if C.all fun x ↦ decide (u ≤ x) then [C] else []

/-- Convert an association list of `(vertex, color)` pairs into nonempty color classes in
`0 .. numColors - 1`. -/
@[expose]
def colorClasses (numColors : ℕ) (cols : List (ℕ × ℕ)) : List (List ℕ) :=
  ((List.range numColors).map fun c ↦
    (cols.filter fun p ↦ decide (p.2 = c)).map Prod.fst).filter fun part ↦ !part.isEmpty

/-- Constructive polynomial-time Brooks `k`-coloring of `H` (returning `≤ k` independent sets). -/
@[expose]
def brooksColoring (H : Graph) (k : ℕ) : List (List ℕ) :=
  colorClasses k ((canonicalComponents H).flatMap (colorComponent H k))

/-- Constructive polynomial-time greedy `(k + 1)`-coloring of `H` (returning `≤ k + 1` independent
sets). -/
@[expose]
def greedyColoring (H : Graph) (k : ℕ) : List (List ℕ) :=
  colorClasses (k + 1) (greedyColor H (k + 1) H.distinctVertices [])

/-! ### 2. Polynomial-Time Computability Certificates -/

section BrooksPolyTime

attribute [local irreducible] encGraph encNat encUnary

theorem computableInPolyTime_complGraph :
    ComputableInPolyTime complGraph encGraph encGraph := by
  have hV : ComputableInPolyTime Graph.distinctVertices encGraph (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices
  have hedges : ComputableInPolyTime
      (fun G : Graph ↦ G.distinctVertices.flatMap fun u ↦
        (G.distinctVertices.filter fun v ↦ decide (u < v) && !G.adjBool u v).map fun v ↦ (u, v))
      encGraph (encList (encPair encNat encNat)) := by
    refine flatMapWithInput hV ?_
    let encP := encPair encGraph encNat
    have hG : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1) encP encGraph := fst _ _
    have hu : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2) encP encNat := snd _ _
    have hVp : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1.distinctVertices) encP
        (encList encNat) := hV.comp hG
    have hfilt : ComputableInPolyTime
        (fun p : Graph × ℕ ↦ p.1.distinctVertices.filter fun v ↦
          decide (p.2 < v) && !p.1.adjBool p.2 v) encP (encList encNat) := by
      refine filterWithInput hVp ?_
      let encQ := encPair encP encNat
      have hGq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.1.1) encQ encGraph :=
        hG.comp (fst _ _)
      have huq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.1.2) encQ encNat :=
        hu.comp (fst _ _)
      have hvq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.2) encQ encNat := snd _ _
      exact bool_and' (binary_lt' huq hvq)
        (bool_not.comp (Graph.computableInPolyTime_adjBool_comp hGq huq hvq))
    exact mapWithInput hfilt ((hu.comp (fst _ _)).prod (snd _ _))
  unfold complGraph
  exact (encGraph_mk_polyTime hV hedges).of_enc_eq fun _ ↦ rfl

private theorem computableInPolyTime_subsetDegBool :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ ↦ subsetDegBool p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) encNat) encUnary := by
  unfold subsetDegBool
  refine (length_list encNat).comp (filterWithInput ((snd _ _).comp (fst _ _)) ?_)
  let encQ := encPair (encPair (encPair encGraph (encList encNat)) encNat) encNat
  have hG : ComputableInPolyTime (fun q : ((Graph × List ℕ) × ℕ) × ℕ ↦ q.1.1.1) encQ encGraph :=
    (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hv : ComputableInPolyTime (fun q : ((Graph × List ℕ) × ℕ) × ℕ ↦ q.1.2) encQ encNat :=
    (snd _ _).comp (fst _ _)
  have hw : ComputableInPolyTime (fun q : ((Graph × List ℕ) × ℕ) × ℕ ↦ q.2) encQ encNat :=
    snd _ _
  exact Graph.computableInPolyTime_adjBool_comp hG hv hw

private theorem computableInPolyTime_bfsStep :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × List ℕ ↦ bfsStep p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) (encList encNat)) (encList encNat) := by
  unfold bfsStep
  let encP := encPair (encPair encGraph (encList encNat)) (encList encNat)
  have hG : ComputableInPolyTime (fun p : (Graph × List ℕ) × List ℕ ↦ p.1.1) encP encGraph :=
    (fst _ _).comp (fst _ _)
  have hS : ComputableInPolyTime (fun p : (Graph × List ℕ) × List ℕ ↦ p.1.2) encP
      (encList encNat) := (snd _ _).comp (fst _ _)
  have hacc : ComputableInPolyTime (fun p : (Graph × List ℕ) × List ℕ ↦ p.2) encP
      (encList encNat) := snd _ _
  have hnew : ComputableInPolyTime
      (fun p : (Graph × List ℕ) × List ℕ ↦
        p.1.2.filter fun w ↦ !p.2.contains w && p.2.any fun u ↦ p.1.1.adjBool u w)
      encP (encList encNat) := by
    refine filterWithInput hS ?_
    let encQ := encPair encP encNat
    have hGq : ComputableInPolyTime (fun q : ((Graph × List ℕ) × List ℕ) × ℕ ↦ q.1.1.1) encQ
        encGraph := hG.comp (fst _ _)
    have haq : ComputableInPolyTime (fun q : ((Graph × List ℕ) × List ℕ) × ℕ ↦ q.1.2) encQ
        (encList encNat) := hacc.comp (fst _ _)
    have hwq : ComputableInPolyTime (fun q : ((Graph × List ℕ) × List ℕ) × ℕ ↦ q.2) encQ
        encNat := snd _ _
    have hany : ComputableInPolyTime
        (fun q : ((Graph × List ℕ) × List ℕ) × ℕ ↦ q.1.2.any fun u ↦ q.1.1.1.adjBool u q.2)
        encQ encBool := by
      refine anyWithInput haq ?_
      let encR := encPair encQ encNat
      exact Graph.computableInPolyTime_adjBool_comp (hGq.comp (fst _ _)) (snd _ _)
        (hwq.comp (fst _ _))
    exact bool_and' (bool_not.comp (contains haq hwq)) hany
  exact (listAppend encNat).comp (hacc.prod hnew)

theorem computableInPolyTime_bfsOrder :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ ↦ bfsOrder p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) encNat) (encList encNat) := by
  unfold bfsOrder
  let encP := encPair (encPair encGraph (encList encNat)) encNat
  have hpar : ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ ↦ p.1) encP
      (encPair encGraph (encList encNat)) := fst _ _
  have hlist : ComputableInPolyTime
      (fun p : (Graph × List ℕ) × ℕ ↦ List.replicate p.1.2.length true) encP encBits :=
    (bitsReplicate true).comp ((length_list encNat).comp ((snd _ _).comp hpar))
  have hinit : ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ ↦ [p.2]) encP
      (encList encNat) := (ComputableInPolyTime.cons encNat).comp ((snd _ _).prod (const []))
  have hstep : ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × List ℕ) × Bool ↦
        (fun (par : Graph × List ℕ) (acc : List ℕ) (_ : Bool) ↦ bfsStep par.1 par.2 acc)
          q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encGraph (encList encNat)) (encList encNat)) encBool)
      (encList encNat) := computableInPolyTime_bfsStep.comp (fst _ _)
  have hgrowth_poly : PolyBounded (fun p : (Graph × List ℕ) × ℕ ↦ (encP p).length)
      (fun p ↦ (encList encNat p.1.2).length) := by
    refine PolyBounded.of_forall_le 1 1 fun p ↦ ?_
    have hS : (encList encNat p.1.2).length ≤ (encP p).length := by dsimp only [encP]; enc_len
    simp only [pow_one, one_mul]; omega
  refine foldlWith_of_bounded_growth (encA := encBool) (encL := encBits)
    (step := fun (par : Graph × List ℕ) (acc : List ℕ) (_ : Bool) ↦ bfsStep par.1 par.2 acc)
    hpar hlist hinit hstep hgrowth_poly ?_
  intro p acc _ _
  unfold bfsStep
  simp only [encList_append, List.length_append]
  have hle : ∀ (f : ℕ → Bool) (l : List ℕ),
      (encList encNat (l.filter f)).length ≤ (encList encNat l).length := by
    intro f l
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.filter_cons]
      split_ifs <;> simp only [encList_cons, List.length_append] <;> omega
  have := hle (fun w ↦ !acc.contains w && acc.any fun u ↦ p.1.1.adjBool u w) p.1.2
  omega

attribute [local irreducible] bfsOrder subsetDegBool

private theorem computableInPolyTime_firstFreeColor :
    ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ firstFreeColor p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encGraph encUnary) (encList (encPair encNat encNat))) encNat)
      encNat := by
  unfold firstFreeColor
  let encP := encPair (encPair (encPair encGraph encUnary) (encList (encPair encNat encNat)))
    encNat
  have hG : ComputableInPolyTime (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ p.1.1.1) encP
      encGraph := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hk : ComputableInPolyTime (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ p.1.1.2) encP
      encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hcols : ComputableInPolyTime (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ p.1.2) encP
      (encList (encPair encNat encNat)) := (snd _ _).comp (fst _ _)
  have hv : ComputableInPolyTime (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ p.2) encP encNat :=
    snd _ _
  have hrange : ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ List.range p.1.1.2) encP (encList encNat) := by
    have hr : ComputableInPolyTime
        (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ List.range p.1.1.2) encP
        (encList encUnary) := ComputableInPolyTime.range.comp hk
    have hc : ComputableInPolyTime (fun l : List ℕ ↦ l.map fun i ↦ i)
        (encList encUnary) (encList encNat) := map unary_to_binary
    simpa only [Function.comp_def, List.map_id'] using hc.comp hr
  have hfilt : ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦
        (List.range p.1.1.2).filter fun c ↦
          !(p.1.2.any fun q ↦ p.1.1.1.adjBool p.2 q.1 && decide (q.2 = c)))
      encP (encList encNat) := by
    refine filterWithInput hrange ?_
    let encQ := encPair encP encNat
    have hany : ComputableInPolyTime
        (fun r : (((Graph × ℕ) × List (ℕ × ℕ)) × ℕ) × ℕ ↦
          r.1.1.2.any fun q ↦ r.1.1.1.1.adjBool r.1.2 q.1 && decide (q.2 = r.2))
        encQ encBool := by
      refine anyWithInput (hcols.comp (fst _ _)) ?_
      let encR := encPair encQ (encPair encNat encNat)
      have hGr : ComputableInPolyTime
          (fun s : ((((Graph × ℕ) × List (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.1.1.1.1) encR
          encGraph := (hG.comp (fst _ _)).comp (fst _ _)
      have hvr : ComputableInPolyTime
          (fun s : ((((Graph × ℕ) × List (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.1.2) encR encNat :=
        (hv.comp (fst _ _)).comp (fst _ _)
      have hcr : ComputableInPolyTime
          (fun s : ((((Graph × ℕ) × List (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.2) encR encNat :=
        (snd _ _).comp (fst _ _)
      have hq1 : ComputableInPolyTime
          (fun s : ((((Graph × ℕ) × List (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.2.1) encR encNat :=
        (fst _ _).comp (snd _ _)
      have hq2 : ComputableInPolyTime
          (fun s : ((((Graph × ℕ) × List (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.2.2) encR encNat :=
        (snd _ _).comp (snd _ _)
      exact bool_and' (Graph.computableInPolyTime_adjBool_comp hGr hvr hq1) (hq2.decide_eq' hcr)
    exact bool_not.comp hany
  exact listHeadDWithInput hfilt (const 0)

theorem computableInPolyTime_greedyColor :
    ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List ℕ) × List (ℕ × ℕ) ↦ greedyColor p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encGraph encUnary) (encList encNat))
        (encList (encPair encNat encNat)))
      (encList (encPair encNat encNat)) := by
  unfold greedyColor
  let encPar := encPair encGraph encUnary
  let encP := encPair (encPair encPar (encList encNat)) (encList (encPair encNat encNat))
  have hpar : ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List ℕ) × List (ℕ × ℕ) ↦ p.1.1) encP encPar :=
    (fst _ _).comp (fst _ _)
  have hlist : ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List ℕ) × List (ℕ × ℕ) ↦ p.1.2) encP (encList encNat) :=
    (snd _ _).comp (fst _ _)
  have hinit : ComputableInPolyTime
      (fun p : ((Graph × ℕ) × List ℕ) × List (ℕ × ℕ) ↦ p.2) encP
      (encList (encPair encNat encNat)) := snd _ _
  have hstep : ComputableInPolyTime
      (fun q : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦
        greedyColorStep q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair encPar (encList (encPair encNat encNat))) encNat)
      (encList (encPair encNat encNat)) := by
    unfold greedyColorStep
    let encQ := encPair (encPair encPar (encList (encPair encNat encNat))) encNat
    have hcols : ComputableInPolyTime
        (fun q : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ q.1.2) encQ
        (encList (encPair encNat encNat)) := (snd _ _).comp (fst _ _)
    have hv : ComputableInPolyTime
        (fun q : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ q.2) encQ encNat := snd _ _
    have hseen : ComputableInPolyTime
        (fun q : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦ q.1.2.any fun p ↦ decide (p.1 = q.2))
        encQ encBool := by
      refine anyWithInput hcols ?_
      exact ((fst _ _).comp (snd _ _)).decide_eq' (hv.comp (fst _ _))
    have hcons : ComputableInPolyTime
        (fun q : ((Graph × ℕ) × List (ℕ × ℕ)) × ℕ ↦
          (q.2, firstFreeColor q.1.1.1 q.1.1.2 q.1.2 q.2) :: q.1.2)
        encQ (encList (encPair encNat encNat)) :=
      (ComputableInPolyTime.cons (encPair encNat encNat)).comp
        ((hv.prod computableInPolyTime_firstFreeColor).prod hcols)
    exact hseen.ite hcols hcons
  have hgrowth_poly : PolyBounded (fun p : ((Graph × ℕ) × List ℕ) × List (ℕ × ℕ) ↦ (encP p).length)
      (fun p ↦ 4 * (encList encNat p.1.2).length + 2 * p.1.1.2 + 8) := by
    refine PolyBounded.of_forall_le 16 1 fun p ↦ ?_
    have h1 : (encList encNat p.1.2).length ≤ (encP p).length := by dsimp only [encP]; enc_len
    have h2 : p.1.1.2 ≤ (encP p).length := by
      have : p.1.1.2 = (encUnary p.1.1.2).length := by simp [encUnary_apply]
      rw [this]; dsimp only [encP, encPar]; enc_len
    simp only [pow_one]; omega
  refine foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (step := fun (par : Graph × ℕ) (acc : List (ℕ × ℕ)) (v : ℕ) ↦
      greedyColorStep par.1 par.2 acc v)
    hpar hlist hinit hstep hgrowth_poly ?_
  intro p acc v hv
  unfold greedyColorStep
  split_ifs
  · exact Nat.le_add_right _ _
  · simp only [encList_cons, List.length_append, length_frame, length_encPair]
    have hv_le : (encNat v).length ≤ (encList encNat p.1.2).length :=
      SizedListEncoding.length_elem_le p.1.2 v hv
    have hc_le : (encNat (firstFreeColor p.1.1.1 p.1.1.2 acc v)).length ≤ p.1.1.2 + 1 := by
      unfold firstFreeColor
      set cands := (List.range p.1.1.2).filter fun c ↦
        !(acc.any fun q ↦ p.1.1.1.adjBool v q.1 && decide (q.2 = c))
      cases hc : cands with
      | nil => simp [encNat_apply, Nat.zero_bits]
      | cons c cs =>
        have hcm : c ∈ List.range p.1.1.2 := (List.mem_filter.mp (hc ▸ List.mem_cons_self)).1
        have hlt : c < p.1.1.2 := List.mem_range.mp hcm
        have hsz : c.size ≤ p.1.1.2 := (Nat.size_le_self c).trans (by omega)
        have hbits := Nat.size_eq_bits_len c
        simp only [List.headD_cons, encNat_apply]; omega
    omega

attribute [local irreducible] greedyColor

private theorem computableInPolyTime_lookupColor :
    ComputableInPolyTime (fun p : List (ℕ × ℕ) × ℕ ↦ lookupColor p.1 p.2)
      (encPair (encList (encPair encNat encNat)) encNat) encNat := by
  unfold lookupColor
  have hfilt : ComputableInPolyTime
      (fun p : List (ℕ × ℕ) × ℕ ↦ p.1.filter fun q ↦ decide (q.1 = p.2))
      (encPair (encList (encPair encNat encNat)) encNat) (encList (encPair encNat encNat)) := by
    refine filterWithInput (fst _ _) ?_
    exact ((fst _ _).comp (snd _ _)).decide_eq' ((snd _ _).comp (fst _ _))
  exact (snd encNat encNat).comp (listHeadDWithInput hfilt (const (0, 0)))

private theorem computableInPolyTime_swapColor :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ swapColor p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encNat) encNat := by
  unfold swapColor
  let encP := encPair (encPair encNat encNat) encNat
  have hc1 : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ p.1.1) encP encNat :=
    (fst _ _).comp (fst _ _)
  have hc2 : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ p.1.2) encP encNat :=
    (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ p.2) encP encNat := snd _ _
  exact ((hc.decide_eq' hc1).ite hc2 ((hc.decide_eq' hc2).ite hc1 hc)).of_enc_eq fun _ ↦ by
    simp only [decide_eq_true_eq]

theorem computableInPolyTime_hasCompleteCompBool :
    ComputableInPolyTime (fun p : Graph × ℕ ↦ hasCompleteCompBool p.1 p.2)
      (encPair encGraph encUnary) encBool := by
  unfold hasCompleteCompBool
  let encP := encPair encGraph encUnary
  have hG : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1) encP encGraph := fst _ _
  have hk : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2) encP encUnary := snd _ _
  have hV : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1.distinctVertices) encP
      (encList encNat) := Graph.computableInPolyTime_distinctVertices.comp hG
  refine anyWithInput hV ?_
  let encQ := encPair encP encNat
  have hGq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.1.1) encQ encGraph :=
    hG.comp (fst _ _)
  have hkq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.1.2) encQ encUnary :=
    hk.comp (fst _ _)
  have hVq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.1.1.distinctVertices) encQ
      (encList encNat) := hV.comp (fst _ _)
  have huq : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ ↦ q.2) encQ encNat := snd _ _
  have hC : ComputableInPolyTime
      (fun q : (Graph × ℕ) × ℕ ↦ bfsOrder q.1.1 q.1.1.distinctVertices q.2) encQ
      (encList encNat) := computableInPolyTime_bfsOrder.comp ((hGq.prod hVq).prod huq)
  have hlen : ComputableInPolyTime
      (fun q : (Graph × ℕ) × ℕ ↦ decide ((bfsOrder q.1.1 q.1.1.distinctVertices q.2).length =
        q.1.2 + 1)) encQ encBool :=
    ((length_list encNat).comp hC).decide_eq' (unary_add' hkq (const 1))
  have hall : ComputableInPolyTime
      (fun q : (Graph × ℕ) × ℕ ↦
        (bfsOrder q.1.1 q.1.1.distinctVertices q.2).all fun x ↦
          decide (subsetDegBool q.1.1 q.1.1.distinctVertices x = q.1.2)) encQ encBool := by
    refine allWithInput hC ?_
    let encR := encPair encQ encNat
    exact (computableInPolyTime_subsetDegBool.comp
      (((hGq.comp (fst _ _)).prod (hVq.comp (fst _ _))).prod (snd _ _))).decide_eq'
        (hkq.comp (fst _ _))
  exact bool_and' hlen hall

private theorem computableInPolyTime_isLovaszCherry :
    ComputableInPolyTime
      (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦ isLovaszCherry q.1.1 q.1.2 q.2)
      (encPair (encPair encGraph (encList encNat)) (encPair (encPair encNat encNat) encNat))
      encBool := by
  unfold isLovaszCherry
  let encQ := encPair (encPair encGraph (encList encNat)) (encPair (encPair encNat encNat) encNat)
  have hG : ComputableInPolyTime (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦ q.1.1) encQ
      encGraph := (fst _ _).comp (fst _ _)
  have hC : ComputableInPolyTime (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦ q.1.2) encQ
      (encList encNat) := (snd _ _).comp (fst _ _)
  have hx : ComputableInPolyTime (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦ q.2.1.1) encQ
      encNat := (fst _ _).comp ((fst _ _).comp (snd _ _))
  have hy : ComputableInPolyTime (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦ q.2.1.2) encQ
      encNat := (snd _ _).comp ((fst _ _).comp (snd _ _))
  have hz : ComputableInPolyTime (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦ q.2.2) encQ
      encNat := (snd _ _).comp (snd _ _)
  have hrem : ComputableInPolyTime
      (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦
        q.1.2.filter fun w ↦ decide (w ≠ q.2.1.2) && decide (w ≠ q.2.2)) encQ (encList encNat) := by
    refine filterWithInput hC ?_
    let encR := encPair encQ encNat
    have hw : ComputableInPolyTime (fun r : ((Graph × List ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ ↦ r.2) encR
        encNat := snd _ _
    exact bool_and' (bool_not.comp (hw.decide_eq' (hy.comp (fst _ _))))
      (bool_not.comp (hw.decide_eq' (hz.comp (fst _ _))))
  have hbfs : ComputableInPolyTime
      (fun q : (Graph × List ℕ) × ((ℕ × ℕ) × ℕ) ↦
        decide ((bfsOrder q.1.1
          (q.1.2.filter fun w ↦ decide (w ≠ q.2.1.2) && decide (w ≠ q.2.2)) q.2.1.1).length =
          (q.1.2.filter fun w ↦ decide (w ≠ q.2.1.2) && decide (w ≠ q.2.2)).length))
      encQ encBool :=
    ((length_list encNat).comp (computableInPolyTime_bfsOrder.comp ((hG.prod hrem).prod hx)))
      |>.decide_eq' ((length_list encNat).comp hrem)
  exact bool_and'
    (bool_and'
      (bool_and'
        (bool_and' (Graph.computableInPolyTime_adjBool_comp hG hx hy)
          (Graph.computableInPolyTime_adjBool_comp hG hx hz))
        (bool_not.comp (Graph.computableInPolyTime_adjBool_comp hG hy hz)))
      (bool_not.comp (hy.decide_eq' hz)))
    hbfs

attribute [local irreducible] isLovaszCherry lookupColor swapColor

private theorem computableInPolyTime_colorComponent :
    ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦ colorComponent p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph encUnary) (encList encNat))
      (encList (encPair encNat encNat)) := by
  let encP := encPair (encPair encGraph encUnary) (encList encNat)
  have hG : ComputableInPolyTime (fun p : (Graph × ℕ) × List ℕ ↦ p.1.1) encP encGraph :=
    (fst _ _).comp (fst _ _)
  have hk : ComputableInPolyTime (fun p : (Graph × ℕ) × List ℕ ↦ p.1.2) encP encUnary :=
    (snd _ _).comp (fst _ _)
  have hC : ComputableInPolyTime (fun p : (Graph × ℕ) × List ℕ ↦ p.2) encP (encList encNat) :=
    snd _ _
  have hpar : ComputableInPolyTime (fun p : (Graph × ℕ) × List ℕ ↦ p.1) encP
      (encPair encGraph encUnary) := fst _ _
  -- Case 1: low-degree vertices:
  have hlowDeg : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦ p.2.filter fun v ↦ decide (subsetDegBool p.1.1 p.2 v < p.1.2))
      encP (encList encNat) := by
    refine filterWithInput hC ?_
    exact unary_lt' (computableInPolyTime_subsetDegBool.comp
      (((hG.comp (fst _ _)).prod (hC.comp (fst _ _))).prod (snd _ _))) (hk.comp (fst _ _))
  have hcase1 : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦
        greedyColor p.1.1 p.1.2
          (bfsOrder p.1.1 p.2
            ((p.2.filter fun v ↦ decide (subsetDegBool p.1.1 p.2 v < p.1.2)).headD 0)).reverse [])
      encP (encList (encPair encNat encNat)) := by
    have hr := listHeadDWithInput hlowDeg (const 0)
    have hord := (listReverse encNat).comp
      (computableInPolyTime_bfsOrder.comp ((hG.prod hC).prod hr))
    exact computableInPolyTime_greedyColor.comp ((hpar.prod hord).prod (const []))
  -- Case 2: cut-vertices:
  have hcutVerts : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦ p.2.filter fun v ↦
        let Cv := p.2.filter fun w ↦ decide (w ≠ v)
        decide ((bfsOrder p.1.1 Cv (Cv.headD 0)).length < Cv.length))
      encP (encList encNat) := by
    refine filterWithInput hC ?_
    let encQ := encPair encP encNat
    have hGq : ComputableInPolyTime (fun q : ((Graph × ℕ) × List ℕ) × ℕ ↦ q.1.1.1) encQ
        encGraph := hG.comp (fst _ _)
    have hCv : ComputableInPolyTime
        (fun q : ((Graph × ℕ) × List ℕ) × ℕ ↦ q.1.2.filter fun w ↦ decide (w ≠ q.2))
        encQ (encList encNat) := by
      refine filterWithInput (hC.comp (fst _ _)) ?_
      exact bool_not.comp ((snd _ _).decide_eq' ((snd _ _).comp (fst _ _)))
    exact unary_lt'
      ((length_list encNat).comp (computableInPolyTime_bfsOrder.comp
        ((hGq.prod hCv).prod (listHeadDWithInput hCv (const 0)))))
      ((length_list encNat).comp hCv)
  have hcase2 : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦
        let cutVerts := p.2.filter fun v ↦
          let Cv := p.2.filter fun w ↦ decide (w ≠ v)
          decide ((bfsOrder p.1.1 Cv (Cv.headD 0)).length < Cv.length)
        let x := cutVerts.headD 0
        let Cx := p.2.filter fun w ↦ decide (w ≠ x)
        let S1 := bfsOrder p.1.1 Cx (Cx.headD 0)
        let S2 := Cx.filter fun w ↦ !S1.contains w
        let col1 := greedyColor p.1.1 p.1.2 (bfsOrder p.1.1 (x :: S1) x).reverse []
        let col2 := greedyColor p.1.1 p.1.2 (bfsOrder p.1.1 (x :: S2) x).reverse []
        let c1 := lookupColor col1 x
        let c2 := lookupColor col2 x
        col1 ++ (col2.filter fun q ↦ decide (q.1 ≠ x)).map fun q ↦ (q.1, swapColor c1 c2 q.2))
      encP (encList (encPair encNat encNat)) := by
    have hx := listHeadDWithInput hcutVerts (const 0)
    have hCx : ComputableInPolyTime
        (fun p : (Graph × ℕ) × List ℕ ↦ p.2.filter fun w ↦ decide (w ≠ (
          (p.2.filter fun v ↦ let Cv := p.2.filter fun w ↦ decide (w ≠ v)
            decide ((bfsOrder p.1.1 Cv (Cv.headD 0)).length < Cv.length)).headD 0)))
        encP (encList encNat) := by
      refine filterWithInput hC ?_
      exact bool_not.comp ((snd _ _).decide_eq' (hx.comp (fst _ _)))
    have hS1 := computableInPolyTime_bfsOrder.comp
      ((hG.prod hCx).prod (listHeadDWithInput hCx (const 0)))
    have hS2 : ComputableInPolyTime
        (fun p : (Graph × ℕ) × List ℕ ↦
          let x := ((p.2.filter fun v ↦
            let Cv := p.2.filter fun w ↦ decide (w ≠ v)
            decide ((bfsOrder p.1.1 Cv (Cv.headD 0)).length < Cv.length)).headD 0)
          let Cx := p.2.filter fun w ↦ decide (w ≠ x)
          Cx.filter fun w ↦ !(bfsOrder p.1.1 Cx (Cx.headD 0)).contains w)
        encP (encList encNat) := by
      refine filterWithInput hCx ?_
      exact bool_not.comp (contains (hS1.comp (fst _ _)) (snd _ _))
    have hcol1 := computableInPolyTime_greedyColor.comp
      ((hpar.prod ((listReverse encNat).comp (computableInPolyTime_bfsOrder.comp
        ((hG.prod ((ComputableInPolyTime.cons encNat).comp (hx.prod hS1))).prod hx)))).prod
        (const []))
    have hcol2 := computableInPolyTime_greedyColor.comp
      ((hpar.prod ((listReverse encNat).comp (computableInPolyTime_bfsOrder.comp
        ((hG.prod ((ComputableInPolyTime.cons encNat).comp (hx.prod hS2))).prod hx)))).prod
        (const []))
    have hc1 := computableInPolyTime_lookupColor.comp (hcol1.prod hx)
    have hc2 := computableInPolyTime_lookupColor.comp (hcol2.prod hx)
    have hpred : ComputableInPolyTime
        (fun p : ((Graph × ℕ) × List ℕ) × (ℕ × ℕ) ↦
          !decide (p.2.1 = ((p.1.2.filter fun v ↦
            let Cv := p.1.2.filter fun w ↦ decide (w ≠ v)
            decide ((bfsOrder p.1.1.1 Cv (Cv.headD 0)).length < Cv.length)).headD 0)))
        (encPair encP (encPair encNat encNat)) encBool :=
      bool_not.comp (((fst encNat encNat).comp (snd encP (encPair encNat encNat))).decide_eq'
        (hx.comp (fst encP (encPair encNat encNat))))
    have hcol2_f := filterWithInput
      (test := fun a q ↦ !decide (q.1 = ((a.2.filter fun v ↦
        let Cv := a.2.filter fun w ↦ decide (w ≠ v)
        decide ((bfsOrder a.1.1 Cv (Cv.headD 0)).length < Cv.length)).headD 0)))
      hcol2 hpred
    have hcol2_m := mapWith
      (((fst encNat encNat).comp (snd encP (encPair encNat encNat))).prod
        (computableInPolyTime_swapColor.comp
          (((hc1.comp (fst encP (encPair encNat encNat))).prod
            (hc2.comp (fst encP (encPair encNat encNat)))).prod
            ((snd encNat encNat).comp (snd encP (encPair encNat encNat))))))
      id' hcol2_f
    exact (listAppend (encPair encNat encNat)).comp (hcol1.prod hcol2_m)
  -- Case 3: Lovász cherries:
  have hcherries : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦
        (p.2.flatMap fun x ↦ p.2.flatMap fun y ↦ p.2.map fun z ↦ ((x, y), z)).filter
          (isLovaszCherry p.1.1 p.2))
      encP (encList (encPair (encPair encNat encNat) encNat)) := by
    have htriples : ComputableInPolyTime
        (fun p : (Graph × ℕ) × List ℕ ↦
          p.2.flatMap fun x ↦ p.2.flatMap fun y ↦ p.2.map fun z ↦ ((x, y), z))
        encP (encList (encPair (encPair encNat encNat) encNat)) := by
      refine flatMapWithInput hC ?_
      refine flatMapWithInput (hC.comp (fst _ _)) ?_
      refine mapWithInput (hC.comp ((fst _ _).comp (fst _ _))) ?_
      exact (((snd _ _).comp ((fst _ _).comp (fst _ _))).prod ((snd _ _).comp (fst _ _))).prod
        (snd _ _)
    refine filterWithInput htriples ?_
    exact computableInPolyTime_isLovaszCherry.comp
      (((hG.prod hC).comp (fst _ _)).prod (snd _ _))
  have hcase3 : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦
        let cherries := (p.2.flatMap fun x ↦ p.2.flatMap fun y ↦ p.2.map fun z ↦ ((x, y), z)).filter
          (isLovaszCherry p.1.1 p.2)
        let t := cherries.headD ((0, 0), 0)
        let rem := p.2.filter fun w ↦ decide (w ≠ t.1.2) && decide (w ≠ t.2)
        greedyColor p.1.1 p.1.2 (bfsOrder p.1.1 rem t.1.1).reverse [(t.1.2, 0), (t.2, 0)])
      encP (encList (encPair encNat encNat)) := by
    have ht := listHeadDWithInput hcherries (const ((0, 0), 0))
    have hx := (fst _ _).comp ((fst _ _).comp ht)
    have hy := (snd _ _).comp ((fst _ _).comp ht)
    have hz := (snd _ _).comp ht
    have hrem := filterWithInput
      (test := fun (p : (Graph × ℕ) × List ℕ) (w : ℕ) ↦
        let t := ((p.2.flatMap fun x ↦ p.2.flatMap fun y ↦ p.2.map fun z ↦ ((x, y), z)).filter
          (isLovaszCherry p.1.1 p.2)).headD ((0, 0), 0)
        !decide (w = t.1.2) && !decide (w = t.2))
      hC (bool_and' (bool_not.comp ((snd _ _).decide_eq' (hy.comp (fst _ _))))
        (bool_not.comp ((snd _ _).decide_eq' (hz.comp (fst _ _)))))
    have hord := (listReverse encNat).comp
      (computableInPolyTime_bfsOrder.comp ((hG.prod hrem).prod hx))
    have hinit := (ComputableInPolyTime.cons (encPair encNat encNat)).comp
      ((hy.prod (const 0)).prod ((ComputableInPolyTime.cons (encPair encNat encNat)).comp
        ((hz.prod (const 0)).prod (const []))))
    exact computableInPolyTime_greedyColor.comp ((hpar.prod hord).prod hinit)
  have hcase4 : ComputableInPolyTime
      (fun p : (Graph × ℕ) × List ℕ ↦ greedyColor p.1.1 (p.1.2 + 1) p.2 [])
      encP (encList (encPair encNat encNat)) :=
    computableInPolyTime_greedyColor.comp
      (((hG.prod (unary_add' hk (const 1))).prod hC).prod (const []))
  have h1 := (bool_not.comp ((listIsEmpty' encNat).comp hlowDeg)).ite hcase1
    ((bool_not.comp ((listIsEmpty' encNat).comp hcutVerts)).ite hcase2
      ((bool_not.comp ((listIsEmpty' _).comp hcherries)).ite hcase3 hcase4))
  exact h1.of_enc_eq fun p ↦ congrArg (encList (encPair encNat encNat)) (by
    unfold colorComponent; rfl)

private theorem computableInPolyTime_canonicalComponents :
    ComputableInPolyTime canonicalComponents encGraph (encList (encList encNat)) := by
  unfold canonicalComponents
  have hV := Graph.computableInPolyTime_distinctVertices
  refine flatMapWithInput hV ?_
  let encP := encPair encGraph encNat
  have hG : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1) encP encGraph := fst _ _
  have hu : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2) encP encNat := snd _ _
  have hVp : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1.distinctVertices) encP
      (encList encNat) := hV.comp hG
  have hC := computableInPolyTime_bfsOrder.comp ((hG.prod hVp).prod hu)
  have hall : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ (bfsOrder p.1 p.1.distinctVertices p.2).all fun x ↦ decide (p.2 ≤ x))
      encP encBool := by
    refine allWithInput hC ?_
    exact binary_le' (hu.comp (fst _ _)) (snd _ _)
  have hwrap : ComputableInPolyTime
      (fun p : Graph × ℕ ↦ [bfsOrder p.1 p.1.distinctVertices p.2]) encP
      (encList (encList encNat)) :=
    (ComputableInPolyTime.cons (encList encNat)).comp (hC.prod (const []))
  exact hall.ite hwrap (const [])

private theorem computableInPolyTime_colorClasses :
    ComputableInPolyTime (fun p : ℕ × List (ℕ × ℕ) ↦ colorClasses p.1 p.2)
      (encPair encUnary (encList (encPair encNat encNat))) (encList (encList encNat)) := by
  unfold colorClasses
  let encP := encPair encUnary (encList (encPair encNat encNat))
  have hrange : ComputableInPolyTime (fun p : ℕ × List (ℕ × ℕ) ↦ List.range p.1) encP
      (encList encNat) := by
    have hr : ComputableInPolyTime (fun p : ℕ × List (ℕ × ℕ) ↦ List.range p.1) encP
        (encList encUnary) := ComputableInPolyTime.range.comp (fst _ _)
    have hc : ComputableInPolyTime (fun l : List ℕ ↦ l.map fun i ↦ i)
        (encList encUnary) (encList encNat) := map unary_to_binary
    simpa only [Function.comp_def, List.map_id'] using hc.comp hr
  have hmap : ComputableInPolyTime
      (fun p : ℕ × List (ℕ × ℕ) ↦ (List.range p.1).map fun c ↦
        (p.2.filter fun q ↦ decide (q.2 = c)).map Prod.fst)
      encP (encList (encList encNat)) := by
    refine mapWithInput hrange ?_
    have hfilt : ComputableInPolyTime
        (fun r : (ℕ × List (ℕ × ℕ)) × ℕ ↦ r.1.2.filter fun q ↦ decide (q.2 = r.2))
        (encPair encP encNat) (encList (encPair encNat encNat)) := by
      refine filterWithInput ((snd _ _).comp (fst _ _)) ?_
      exact ((snd _ _).comp (snd _ _)).decide_eq' ((snd _ _).comp (fst _ _))
    exact (map (fst encNat encNat)).comp hfilt
  exact (ComputableInPolyTime.filter (bool_not.comp (listIsEmpty' encNat))).comp hmap

attribute [local irreducible] colorComponent canonicalComponents colorClasses

theorem computableInPolyTime_brooksColoring :
    ComputableInPolyTime (fun p : Graph × ℕ ↦ brooksColoring p.1 p.2)
      (encPair encGraph encUnary) (encList (encList encNat)) := by
  unfold brooksColoring
  let encP := encPair encGraph encUnary
  have hcomps := computableInPolyTime_canonicalComponents.comp (fst encGraph encUnary)
  have hcols := flatMapWithInput (f := fun (par : Graph × ℕ) C ↦ colorComponent par.1 par.2 C)
    hcomps computableInPolyTime_colorComponent
  exact computableInPolyTime_colorClasses.comp ((snd encGraph encUnary).prod hcols)

theorem computableInPolyTime_greedyColoring :
    ComputableInPolyTime (fun p : Graph × ℕ ↦ greedyColoring p.1 p.2)
      (encPair encGraph encUnary) (encList (encList encNat)) := by
  unfold greedyColoring
  let encP := encPair encGraph encUnary
  have hk1 : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2 + 1) encP encUnary :=
    unary_add' (snd _ _) (const 1)
  have hV : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1.distinctVertices) encP
      (encList encNat) := Graph.computableInPolyTime_distinctVertices.comp (fst _ _)
  have hcols := computableInPolyTime_greedyColor.comp
    ((((fst encGraph encUnary).prod hk1).prod hV).prod (const []))
  exact computableInPolyTime_colorClasses.comp (hk1.prod hcols)

end BrooksPolyTime

/-! ### 3. Core Specifications of `complGraph`, `bfsOrder`, `greedyColor`, and
`hasCompleteCompBool` -/

theorem complGraph_vertices (G : Graph) : (complGraph G).vertices = G.distinctVertices := rfl

theorem mem_complGraph_vertices_iff (G : Graph) (v : ℕ) :
    v ∈ (complGraph G).vertices ↔ v ∈ G.vertices := by
  simpa [complGraph] using G.mem_distinctVertices

theorem complGraph_adjBool_eq (G : Graph) {u v : ℕ} (hu : u ∈ G.vertices) (hv : v ∈ G.vertices) :
    (complGraph G).adjBool u v = (decide (u ≠ v) && !G.adjBool u v) := by
  rw [Bool.eq_iff_iff, Graph.adjBool_eq_true_iff, Graph.toSimpleGraph_adj, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  simp only [complGraph, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', Prod.mk.injEq]
  constructor
  · rintro ⟨hne, ⟨a, _, b, ⟨_, hab, hna⟩, rfl, rfl⟩ | ⟨a, _, b, ⟨_, hab, hna⟩, rfl, rfl⟩⟩
    · exact ⟨hne, hna⟩
    · refine ⟨hne, Bool.eq_false_iff.mpr fun h ↦ ?_⟩
      have h' := (G.adjBool_eq_true_iff a b).mpr ((G.adjBool_eq_true_iff b a).mp h).symm
      rw [hna] at h'; cases h'
  · rintro ⟨hne, hna⟩
    refine ⟨hne, ?_⟩
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · left
      exact ⟨u, G.mem_distinctVertices.mpr hu, v, ⟨G.mem_distinctVertices.mpr hv, hlt, hna⟩,
        rfl, rfl⟩
    · right
      refine ⟨v, G.mem_distinctVertices.mpr hv, u, ⟨G.mem_distinctVertices.mpr hu, hgt, ?_⟩, rfl,
        rfl⟩
      refine Bool.eq_false_iff.mpr fun h ↦ ?_
      have h' := (G.adjBool_eq_true_iff u v).mpr ((G.adjBool_eq_true_iff v u).mp h).symm
      rw [hna] at h'; cases h'

theorem subsetDegBool_eq_degree (H : Graph) (v : {w // w ∈ H.vertices}) :
    subsetDegBool H H.distinctVertices v.1 = H.induced.degree v := by
  classical
  unfold subsetDegBool
  rw [← List.toFinset_card_of_nodup (H.nodup_distinctVertices.filter _),
    ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w hw ↦ ⟨w, H.mem_distinctVertices.mp
      (List.mem_filter.mp (List.mem_toFinset.mp hw)).1⟩) ?_ ?_ ?_
  · intro w hw
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr
      ((H.adjBool_eq_true_iff v.1 w).mp (List.mem_filter.mp (List.mem_toFinset.mp hw)).2)
  · intro _ _ _ _ h; exact congrArg Subtype.val h
  · intro w hw
    exact ⟨w.1, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨H.mem_distinctVertices.mpr w.2,
      (H.adjBool_eq_true_iff v.1 w.1).mpr
        ((SimpleGraph.mem_neighborFinset H.induced v w).mp hw)⟩), rfl⟩

/-- `bfsOrder H S r` invariant after `t` iterations. -/
private theorem bfsOrder_iter_inv (H : Graph) (S : List ℕ) (hnd : S.Nodup)
    {r : ℕ} (hr : r ∈ S) (t : ℕ) :
    let acc := (bfsStep H S)^[t] [r]
    acc.Nodup ∧ (∀ x ∈ acc, x ∈ S) ∧ r ∈ acc ∧
    (∀ x ∈ acc, x ≠ r → ∃ u ∈ acc, acc.idxOf u < acc.idxOf x ∧ H.adjBool u x = true) ∧
    (∀ (hS : ∀ y ∈ S, y ∈ H.vertices) (x : ℕ) (hx : x ∈ S), x ∈ acc →
      (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ S}).Reachable
        ⟨⟨r, hS r hr⟩, hr⟩ ⟨⟨x, hS x hx⟩, hx⟩) ∧
    (acc.length < t + 1 → ∀ u ∈ acc, ∀ w ∈ S, H.adjBool u w = true → w ∈ acc) := by
  induction t with
  | zero =>
    refine ⟨List.nodup_singleton r, fun x hx ↦ (List.mem_singleton.mp hx) ▸ hr,
      List.mem_singleton_self r, fun x hx hne ↦ (hne (List.mem_singleton.mp hx)).elim,
      fun hS x _ hx ↦ by
        obtain rfl := List.mem_singleton.mp hx
        exact SimpleGraph.Reachable.refl _,
      fun h ↦ by simp at h⟩
  | succ t ih =>
    obtain ⟨hnd_a, hsub_a, hr_a, hpar_a, hreach_a, hstall_a⟩ := ih
    set acc := (bfsStep H S)^[t] [r]
    dsimp only
    rw [Function.iterate_succ_apply']
    set new := S.filter fun w ↦ !acc.contains w && acc.any fun u ↦ H.adjBool u w
    have hstep_eq : bfsStep H S acc = acc ++ new := rfl
    rw [hstep_eq]
    have hdisj : ∀ x ∈ acc, x ∉ new := fun x hx hxn ↦ by
      have := ((Bool.and_eq_true _ _).mp (List.mem_filter.mp hxn).2).1
      simp [hx] at this
    have hnd_next : (acc ++ new).Nodup :=
      List.nodup_append.mpr ⟨hnd_a, hnd.filter _, fun x hx y hy hEq ↦ hdisj x hx (hEq ▸ hy)⟩
    have hsub_next : ∀ x ∈ acc ++ new, x ∈ S := fun x hx ↦
      (List.mem_append.mp hx).elim (hsub_a x) (fun h ↦ (List.mem_filter.mp h).1)
    have hidx_left : ∀ x ∈ acc, (acc ++ new).idxOf x = acc.idxOf x := fun x hx ↦
      List.idxOf_append_of_mem hx
    have hidx_right : ∀ x ∈ new, acc.length ≤ (acc ++ new).idxOf x := fun x hx ↦ by
      rw [List.idxOf_append_of_notMem (fun h ↦ hdisj x h hx)]; omega
    refine ⟨hnd_next, hsub_next, List.mem_append_left new hr_a, ?_, ?_, ?_⟩
    · intro x hx hxr
      rcases List.mem_append.mp hx with hxa | hxn
      · obtain ⟨u, hu, hlt, hadj⟩ := hpar_a x hxa hxr
        exact ⟨u, List.mem_append_left new hu, by rw [hidx_left u hu, hidx_left x hxa]; exact hlt,
          hadj⟩
      · have hf := ((Bool.and_eq_true _ _).mp (List.mem_filter.mp hxn).2).2
        obtain ⟨u, hu, hadj⟩ := List.any_eq_true.mp hf
        refine ⟨u, List.mem_append_left new hu, ?_, hadj⟩
        have hlt_u : acc.idxOf u < acc.length := List.idxOf_lt_length_iff.mpr hu
        have hge_x := hidx_right x hxn
        rw [hidx_left u hu]; omega
    · intro hS x hx hxm
      rcases List.mem_append.mp hxm with hxa | hxn
      · exact hreach_a hS x hx hxa
      · have hf := ((Bool.and_eq_true _ _).mp (List.mem_filter.mp hxn).2).2
        obtain ⟨u, hu, hadj⟩ := List.any_eq_true.mp hf
        have hru := hreach_a hS u (hsub_a u hu) hu
        have huv : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ S}).Adj
            ⟨⟨u, hS u (hsub_a u hu)⟩, hsub_a u hu⟩
            ⟨⟨x, hS x hx⟩, hx⟩ :=
          (H.adjBool_eq_true_iff u x).mp hadj
        exact hru.trans (SimpleGraph.Adj.reachable huv)
    · intro hlen u hu w hw hadj
      by_cases hnew : new = []
      · rw [hnew, List.append_nil] at hu ⊢
        by_contra hwn
        have hmem : w ∈ new := List.mem_filter.mpr ⟨hw, (Bool.and_eq_true _ _).mpr
          ⟨by simp [hwn], List.any_eq_true.mpr ⟨u, hu, hadj⟩⟩⟩
        rw [hnew] at hmem; cases hmem
      · have hpos : 0 < new.length := List.length_pos_of_ne_nil hnew
        have hlt : acc.length < t + 1 := by rw [List.length_append] at hlen; omega
        have hwn : w ∈ acc := by
          rcases List.mem_append.mp hu with hua | hun
          · exact hstall_a hlt u hua w hw hadj
          · exfalso
            have hf := ((Bool.and_eq_true _ _).mp (List.mem_filter.mp hun).2).2
            obtain ⟨u₀, hu₀, hadj₀⟩ := List.any_eq_true.mp hf
            have := hstall_a hlt u₀ hu₀ u (List.mem_filter.mp hun).1 hadj₀
            exact hdisj u this hun
        exact List.mem_append_left new hwn

private theorem bfsOrder_eq_iter (H : Graph) (S : List ℕ) (r : ℕ) :
    bfsOrder H S r = (bfsStep H S)^[S.length] [r] := by
  unfold bfsOrder
  rw [List.foldl_const, List.length_replicate]

/-- Full specification of `bfsOrder H S r` for a duplicate-free subset `S` of `H.vertices`
containing `r`. -/
theorem bfsOrder_spec (H : Graph) (S : List ℕ) (hnd : S.Nodup)
    (hS : ∀ y ∈ S, y ∈ H.vertices) {r : ℕ} (hr : r ∈ S) :
    let B := bfsOrder H S r
    B.Nodup ∧ (∀ x ∈ B, x ∈ S) ∧ r ∈ B ∧
    (∀ x ∈ B, x ≠ r → ∃ u ∈ B, B.idxOf u < B.idxOf x ∧ H.adjBool u x = true) ∧
    (∀ u ∈ B, ∀ w ∈ S, H.adjBool u w = true → w ∈ B) ∧
    (∀ x (hx : x ∈ S), x ∈ B ↔
      (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ S}).Reachable
        ⟨⟨r, hS r hr⟩, hr⟩ ⟨⟨x, hS x hx⟩, hx⟩) := by
  have h := bfsOrder_iter_inv H S hnd hr S.length
  dsimp only at h
  rw [← bfsOrder_eq_iter] at h
  obtain ⟨hnd_B, hsub_B, hr_B, hpar_B, hreach_B, hstall_B⟩ := h
  have hlen_le : (bfsOrder H S r).length ≤ S.length := by
    rw [← List.toFinset_card_of_nodup hnd_B, ← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun x hx ↦
      List.mem_toFinset.mpr (hsub_B x (List.mem_toFinset.mp hx))
  have hclosed := hstall_B (by omega)
  refine ⟨hnd_B, hsub_B, hr_B, hpar_B, hclosed, fun x hx ↦ ⟨fun hxB ↦ hreach_B hS x hx hxB, ?_⟩⟩
  rintro ⟨p⟩
  have hwalk : ∀ {a b : {v : {w // w ∈ H.vertices} | v.1 ∈ S}}
      (q : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ S}).Walk a b),
      a.1.1 ∈ bfsOrder H S r → b.1.1 ∈ bfsOrder H S r := by
    intro a b q
    induction q with
    | nil => exact id
    | @cons a₁ b₁ c₁ hadj q' ih =>
      intro ha
      exact ih (hclosed a₁.1.1 ha b₁.1.1 b₁.2 ((H.adjBool_eq_true_iff a₁.1.1 b₁.1.1).mpr hadj))
  exact hwalk p hr_B

/-- General specification of `greedyColor`: if `initCol` is a proper `< k`-coloring and every
vertex `v ∈ order` has strictly fewer than `k` distinct colors among its already-colored neighbors
at the moment `v` is processed, then `greedyColor H k order initCol` is a proper `< k`-coloring
covering `initCol.map Prod.fst ∪ order`. -/
theorem greedyColor_spec (H : Graph) (k : ℕ) (_hk : 0 < k) (order : List ℕ)
    (initCol : List (ℕ × ℕ))
    (hinit_nd : (initCol.map Prod.fst).Nodup)
    (hinit_lt : ∀ p ∈ initCol, p.2 < k)
    (hinit_prop : ∀ p ∈ initCol, ∀ q ∈ initCol, H.adjBool p.1 q.1 = true → p.2 ≠ q.2)
    (hstep_free : ∀ i (hi : i < order.length),
      let pre := (order.take i).foldl (greedyColorStep H k) initCol
      let v := order[i]'hi
      ¬ pre.any (fun p ↦ decide (p.1 = v)) = true →
      ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset.card < k) :
    let cols := greedyColor H k order initCol
    (cols.map Prod.fst).Nodup ∧
    (∀ p ∈ cols, p.2 < k) ∧
    (∀ p ∈ cols, ∀ q ∈ cols, H.adjBool p.1 q.1 = true → p.2 ≠ q.2) ∧
    (∀ v, v ∈ cols.map Prod.fst ↔ v ∈ initCol.map Prod.fst ∨ v ∈ order) := by
  suffices ∀ n (hn : n ≤ order.length),
      let cols := (order.take n).foldl (greedyColorStep H k) initCol
      (cols.map Prod.fst).Nodup ∧
      (∀ p ∈ cols, p.2 < k) ∧
      (∀ p ∈ cols, ∀ q ∈ cols, H.adjBool p.1 q.1 = true → p.2 ≠ q.2) ∧
      (∀ v, v ∈ cols.map Prod.fst ↔ v ∈ initCol.map Prod.fst ∨ v ∈ order.take n) by
    simpa only [greedyColor, List.take_length] using this order.length le_rfl
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨hinit_nd, hinit_lt, hinit_prop, fun v ↦ by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨hnd_m, hlt_m, hprop_m, hcov_m⟩ := ih (by omega)
    set pre := (order.take m).foldl (greedyColorStep H k) initCol
    have htake : order.take (m + 1) = order.take m ++ [order[m]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    dsimp only
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set v := order[m]'(by omega)
    have hstep_eq : greedyColorStep H k pre v =
        if pre.any (fun p ↦ decide (p.1 = v)) then pre
        else (v, firstFreeColor H k pre v) :: pre := rfl
    rw [hstep_eq]
    by_cases hseen : pre.any (fun p ↦ decide (p.1 = v)) = true
    · rw [hseen]; simp only [↓reduceIte]
      refine ⟨hnd_m, hlt_m, hprop_m, fun u ↦ ?_⟩
      rw [hcov_m u, List.mem_append, List.mem_singleton]
      constructor
      · exact fun h ↦ h.elim Or.inl (fun h' ↦ Or.inr (Or.inl h'))
      · rintro (h | h | rfl)
        · exact Or.inl h
        · exact Or.inr h
        · obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hseen
          exact (hcov_m v).mp (List.mem_map.mpr ⟨p, hp, decide_eq_true_eq.mp hpe⟩)
    · have hseen_f : pre.any (fun p ↦ decide (p.1 = v)) = false := Bool.eq_false_iff.mpr hseen
      rw [hseen_f]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfree := hstep_free m (by omega) hseen
      set used : Finset ℕ := ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset
      have hex_c : ∃ c ∈ List.range k,
          !(pre.any fun p ↦ H.adjBool v p.1 && decide (p.2 = c)) = true := by
        by_contra hnone
        push Not at hnone
        have hsub : Finset.range k ⊆ used := fun c hc ↦ by
          have hc' : pre.any (fun p ↦ H.adjBool v p.1 && decide (p.2 = c)) = true := by
            have := hnone c (List.mem_range.mpr (Finset.mem_range.mp hc))
            simpa using this
          obtain ⟨p, hp, hp'⟩ := List.any_eq_true.mp hc'
          have hpa := (Bool.and_eq_true _ _).mp hp'
          exact List.mem_toFinset.mpr (List.mem_map.mpr
            ⟨p, List.mem_filter.mpr ⟨hp, hpa.1⟩, decide_eq_true_eq.mp hpa.2⟩)
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this; omega
      set cands := (List.range k).filter fun c ↦
        !(pre.any fun p ↦ H.adjBool v p.1 && decide (p.2 = c))
      have hcands_ne : cands ≠ [] := by
        obtain ⟨c, hc1, hc2⟩ := hex_c
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hc1, hc2⟩)
      have hc_mem : firstFreeColor H k pre v ∈ cands := by
        unfold firstFreeColor
        cases hc : cands with
        | nil => exact (hcands_ne hc).elim
        | cons a as => simp [cands, hc]
      have hc_lt : firstFreeColor H k pre v < k :=
        List.mem_range.mp (List.mem_filter.mp hc_mem).1
      have hc_unused : ∀ q ∈ pre, H.adjBool v q.1 = true →
          q.2 ≠ firstFreeColor H k pre v := by
        intro q hq hadj hEq
        have hnot := (List.mem_filter.mp hc_mem).2
        have hany : pre.any (fun p ↦ H.adjBool v p.1 && decide (p.2 = firstFreeColor H k pre v)) =
            true :=
          List.any_eq_true.mpr ⟨q, hq, (Bool.and_eq_true _ _).mpr ⟨hadj, decide_eq_true_eq.mpr hEq⟩⟩
        simp [hany] at hnot
      have hv_not : v ∉ pre.map Prod.fst := by
        intro hm
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
        exact hseen (List.any_eq_true.mpr ⟨p, hp, decide_eq_true_eq.mpr hpe⟩)
      refine ⟨List.nodup_cons.mpr ⟨hv_not, hnd_m⟩, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hc_lt
        · exact hlt_m p hp'
      · intro p hp q hq hadj
        rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
        · exfalso
          exact H.toSimpleGraph.ne_of_adj ((H.adjBool_eq_true_iff v v).mp hadj) rfl
        · exact (hc_unused q hq' hadj).symm
        · exact hc_unused p hp' (by
            rw [H.adjBool_eq_true_iff] at hadj ⊢; exact hadj.symm)
        · exact hprop_m p hp' q hq' hadj
      · intro u
        rw [List.map_cons, List.mem_cons, hcov_m u, List.mem_append, List.mem_singleton]
        tauto

/-- Specification of `greedyColoring`: when `Δ(H) ≤ k`, `greedyColoring H k` is a valid partition
of `H` into at most `k + 1` nonempty independent sets of `H`. -/
theorem greedyColoring_spec (H : Graph) (k : ℕ)
    (hΔ : ∀ v : {w // w ∈ H.vertices}, H.induced.degree v ≤ k) :
    let parts := greedyColoring H k
    (∀ part ∈ parts, part ≠ [] ∧ part.Nodup ∧ (∀ v ∈ part, v ∈ H.vertices) ∧
      ∀ u ∈ part, ∀ v ∈ part, H.adjBool u v = false) ∧
    parts.Pairwise (fun a b ↦ ∀ v ∈ a, v ∉ b) ∧
    (∀ v ∈ H.vertices, ∃ part ∈ parts, v ∈ part) ∧
    parts.length ≤ k + 1 := by
  classical
  have hstep : ∀ i (hi : i < H.distinctVertices.length),
      let pre := (H.distinctVertices.take i).foldl (greedyColorStep H (k + 1)) []
      let v := H.distinctVertices[i]'hi
      ¬ pre.any (fun p ↦ decide (p.1 = v)) = true →
      ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset.card < k + 1 := by
    intro i hi
    dsimp only
    intro _
    set pre := (H.distinctVertices.take i).foldl (greedyColorStep H (k + 1)) []
    set v := H.distinctVertices[i]'hi
    have hvG : v ∈ H.vertices := H.mem_distinctVertices.mp (List.getElem_mem hi)
    have hpre_nd : (pre.map Prod.fst).Nodup := by
      have : ∀ m, ((H.distinctVertices.take m).foldl (greedyColorStep H (k + 1)) [] |>.map
          Prod.fst).Nodup := fun m ↦ by
        induction m with
        | zero => simp
        | succ m ih =>
          by_cases hm : m < H.distinctVertices.length
          · rw [List.take_succ_eq_append_getElem hm, List.foldl_append, List.foldl_cons,
              List.foldl_nil]
            unfold greedyColorStep
            split_ifs with hs
            · exact ih
            · refine List.nodup_cons.mpr ⟨fun hm' ↦ ?_, ih⟩
              obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm'
              exact hs (List.any_eq_true.mpr ⟨p, hp, decide_eq_true_eq.mpr hpe⟩)
          · rw [List.take_of_length_le (by omega)] at ih
            rw [List.take_of_length_le (by omega)]
            exact ih
      exact this i
    have hpre_sub : ∀ p ∈ pre, p.1 ∈ H.vertices := by
      have : ∀ m, ∀ p ∈ (H.distinctVertices.take m).foldl (greedyColorStep H (k + 1)) [],
          p.1 ∈ H.vertices := fun m ↦ by
        induction m with
        | zero => simp
        | succ m ih =>
          by_cases hm : m < H.distinctVertices.length
          · rw [List.take_succ_eq_append_getElem hm, List.foldl_append, List.foldl_cons,
              List.foldl_nil]
            unfold greedyColorStep
            split_ifs
            · exact ih
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact H.mem_distinctVertices.mp (List.getElem_mem hm)
              · exact ih p hp'
          · rw [List.take_of_length_le (by omega)] at ih
            rw [List.take_of_length_le (by omega)]
            exact ih
      exact this i
    calc ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset.card
        ≤ (pre.filter fun p ↦ H.adjBool v p.1).length := by
          calc _ ≤ ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).length :=
                List.toFinset_card_le _
            _ = _ := List.length_map _
      _ ≤ H.induced.degree ⟨v, hvG⟩ := by
          rw [← List.toFinset_card_of_nodup ((hpre_nd.of_map _).filter _),
            ← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_le_card_of_injOn
            (fun p : ℕ × ℕ ↦ if hp : p.1 ∈ H.vertices then (⟨p.1, hp⟩ : {w // w ∈ H.vertices})
              else ⟨v, hvG⟩) ?_ ?_
          · intro p hp
            have hf := List.mem_filter.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hp))
            have hpG : p.1 ∈ H.vertices := hpre_sub p hf.1
            simp only [hpG, ↓reduceDIte]
            exact Finset.mem_coe.mpr ((SimpleGraph.mem_neighborFinset _ _ _).mpr
              ((H.adjBool_eq_true_iff v p.1).mp hf.2))
          · intro p hp q hq hEq
            have hp' := List.mem_toFinset.mp (Finset.mem_coe.mp hp)
            have hq' := List.mem_toFinset.mp (Finset.mem_coe.mp hq)
            have hpG : p.1 ∈ H.vertices := hpre_sub p (List.mem_filter.mp hp').1
            have hqG : q.1 ∈ H.vertices := hpre_sub q (List.mem_filter.mp hq').1
            simp only [hpG, hqG, ↓reduceDIte] at hEq
            have h1 : p.1 = q.1 := congrArg Subtype.val hEq
            have hmem : ∀ a b : ℕ × ℕ, a ∈ pre → b ∈ pre → a.1 = b.1 → a = b := by
              intro a b ha hb hab
              have hidx := (List.nodup_iff_injective_getElem.mp hpre_nd)
              obtain ⟨ia, hia, hae⟩ := List.getElem_of_mem ha
              obtain ⟨ib, hib, hbe⟩ := List.getElem_of_mem hb
              have hia' : ia < (pre.map Prod.fst).length := by simpa using hia
              have hib' : ib < (pre.map Prod.fst).length := by simpa using hib
              have heq_idx : ia = ib := (List.Nodup.getElem_inj_iff hpre_nd (i := ia) (j := ib)
                (hi := hia') (hj := hib')).mp (by
                simp only [List.getElem_map, hae, hbe, hab])
              subst heq_idx; rw [← hae, ← hbe]
            exact hmem p q (List.mem_filter.mp hp').1 (List.mem_filter.mp hq').1 h1
      _ < k + 1 := Nat.lt_succ_of_le (hΔ ⟨v, hvG⟩)
  obtain ⟨hnd, hlt, hprop, hcov⟩ := greedyColor_spec H (k + 1) (Nat.succ_pos k)
    H.distinctVertices [] (by simp) (by simp) (by simp) hstep
  set cols := greedyColor H (k + 1) H.distinctVertices []
  have hcov' : ∀ v, v ∈ cols.map Prod.fst ↔ v ∈ H.vertices := fun v ↦ by
    rw [hcov v]; simp [H.mem_distinctVertices]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro part hp
    simp only [greedyColoring, colorClasses, List.mem_filter, List.mem_map, List.mem_range] at hp
    obtain ⟨⟨c, hc, rfl⟩, hne⟩ := hp
    refine ⟨List.isEmpty_eq_false_iff.mp (by simpa using hne), ?_, ?_, ?_⟩
    · refine hnd.sublist ?_
      exact (List.filter_sublist (l := cols)).map Prod.fst
    · intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact (hcov' p.1).mp (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)
    · intro u hu v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      have hpf := List.mem_filter.mp hp; have hqf := List.mem_filter.mp hq
      exact Bool.eq_false_iff.mpr fun hadj ↦
        hprop p hpf.1 q hqf.1 hadj
          ((decide_eq_true_eq.mp hpf.2).trans (decide_eq_true_eq.mp hqf.2).symm)
  · simp only [greedyColoring, colorClasses]
    refine List.Pairwise.filter _ ?_
    refine (List.nodup_range.pairwise_of_forall_ne fun c₁ _ c₂ _ hne ↦ hne).map _ ?_
    intro c₁ c₂ hne v hv₁ hv₂
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv₁
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hv₂
    have hpf := List.mem_filter.mp hp; have hqf := List.mem_filter.mp hq
    have hpq : p = q := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpf.1
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hqf.1
      have hij : i = j := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
        (hi := by simpa using hi) (hj := by simpa using hj)).mp (by
        simp only [List.getElem_map]; exact hqp.symm)
      subst hij; rfl
    subst hpq
    exact hne ((decide_eq_true_eq.mp hpf.2).symm.trans (decide_eq_true_eq.mp hqf.2))
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((hcov' v).mpr hv)
    refine ⟨(cols.filter fun q ↦ decide (q.2 = p.2)).map Prod.fst, ?_,
      List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr rfl⟩, rfl⟩⟩
    simp only [greedyColoring, colorClasses, List.mem_filter, List.mem_map, List.mem_range]
    refine ⟨⟨p.2, hlt p hp, rfl⟩, ?_⟩
    have hne : ((cols.filter fun q ↦ decide (q.2 = p.2)).map Prod.fst) ≠ [] :=
      List.ne_nil_of_mem (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr rfl⟩,
        rfl⟩)
    simp [List.isEmpty_eq_false_iff.mpr hne]
  · calc (greedyColoring H k).length
        ≤ ((List.range (k + 1)).map fun c ↦
            (cols.filter fun p ↦ decide (p.2 = c)).map Prod.fst).length :=
          List.length_filter_le _ _
      _ = k + 1 := by simp

/-- Exact characterization of `hasCompleteCompBool H k`: it holds iff `H` has a connected component
of size `k + 1` in which every vertex has `H`-degree `k`. -/
theorem hasCompleteCompBool_eq_true_iff (H : Graph) (k : ℕ) :
    hasCompleteCompBool H k = true ↔
      ∃ u : {w // w ∈ H.vertices},
        let C := bfsOrder H H.distinctVertices u.1
        C.length = k + 1 ∧ ∀ x ∈ C, subsetDegBool H H.distinctVertices x = k := by
  simp only [hasCompleteCompBool, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro ⟨u, hu, h1, h2⟩
    exact ⟨⟨u, H.mem_distinctVertices.mp hu⟩, h1, h2⟩
  · rintro ⟨⟨u, hu⟩, h1, h2⟩
    exact ⟨u, H.mem_distinctVertices.mpr hu, h1, h2⟩

end Cslib.Complexity
