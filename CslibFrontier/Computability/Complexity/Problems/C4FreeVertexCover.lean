/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.EUThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# `NP`-Completeness of `C₄`-Free Vertex Cover

A finite graph `G : Cslib.Complexity.Graph` is *`C₄`-free* on its declared vertices
(`Cslib.Complexity.IsC4FreeGraph`) when any two distinct declared vertices share at most one
common declared neighbor — equivalently, when the induced simple graph `G.induced` contains no
simple cycle of length `4` (`isC4FreeGraph_iff_forall_isCycle_length_ne_four`).

We prove that the restricted decision problem `Cslib.Complexity.C4FreeVertexCover` is
`NP`-complete under standard Lean axioms (`c4FreeVertexCover_npComplete`). Applying Garey and
Johnson's classical variable-edge and clause-triangle construction directly to
`Cslib.Complexity.EUThreeSAT` (where every clause contains three literals on three pairwise distinct
variables) produces exclusively `C₄`-free graphs: every vertex is adjacent to at most one literal
vertex, no pair of distinct vertices from the same clause shares a literal neighbor (by variable
distinctness), and two clause triangles share no edges.

## Main definitions

* `Cslib.Complexity.IsC4FreeGraph`, `Cslib.Complexity.isC4FreeGraphBool`: `C₄`-freeness
  on declared vertices of `Cslib.Complexity.Graph` and its polynomial-time Boolean test.
* `Cslib.Complexity.C4FreeVertexCover`: the `VertexCover` decision problem restricted to
  `C₄`-free graphs on `encVertexCoverInstance`.
* `Cslib.Complexity.euThreeSATToC4FreeVertexCover`: polynomial-time many-one reduction from
  `EUThreeSAT` to `C4FreeVertexCover`.

## Main results

* `Cslib.Complexity.isC4FreeGraph_iff_forall_isCycle_length_ne_four`: `IsC4FreeGraph G` holds
  if and only if `G.induced` has no simple cycle of length `4`.
* `Cslib.Complexity.c4FreeVertexCover_mem_NP`:
  `C4FreeVertexCover ∈ NP encVertexCoverInstance`.
* `Cslib.Complexity.polyTimeReducible_euThreeSAT_c4FreeVertexCover`,
  `Cslib.Complexity.c4FreeVertexCover_npHard`,
  `Cslib.Complexity.c4FreeVertexCover_npComplete`: `NP`-completeness of `C4FreeVertexCover`.

## Tags

computational complexity, NP-completeness, vertex cover, C4-free graph, 3-SAT reduction
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- A graph `G : Cslib.Complexity.Graph` is *`C₄`-free* on its declared vertices when any two
distinct declared vertices share at most one common declared neighbor. -/
@[expose] def IsC4FreeGraph (G : Graph) : Prop :=
  ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, u ≠ v →
    ∀ w₁ ∈ G.vertices, ∀ w₂ ∈ G.vertices,
      G.toSimpleGraph.Adj u w₁ → G.toSimpleGraph.Adj v w₁ →
      G.toSimpleGraph.Adj u w₂ → G.toSimpleGraph.Adj v w₂ → w₁ = w₂

/-- `IsC4FreeGraph G` holds if and only if `G.induced` contains no simple cycle of length `4`. -/
theorem isC4FreeGraph_iff_forall_isCycle_length_ne_four (G : Graph) :
    IsC4FreeGraph G ↔
      ∀ (a : {v // v ∈ G.vertices}) (c : G.induced.Walk a a), c.IsCycle → c.length ≠ 4 := by
  constructor
  · intro hG a c hc hlen
    match c, hlen with
    | @SimpleGraph.Walk.cons _ _ _ b _ hab
        (@SimpleGraph.Walk.cons _ _ _ d _ hbd
          (@SimpleGraph.Walk.cons _ _ _ e _ hde
            (@SimpleGraph.Walk.cons _ _ _ _ _ hea .nil))), _ =>
      have hnd := hc.support_nodup
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨hb_not, hd_not, _⟩ := hnd
      have had : a.1 ≠ d.1 := fun h ↦ hd_not (Or.inr (Subtype.ext h.symm))
      have hbe : b.1 ≠ e.1 := fun h ↦ hb_not (Or.inr (Or.inl (Subtype.ext h)))
      exact hbe (hG a.1 a.2 d.1 d.2 had b.1 b.2 e.1 e.2 hab hbd.symm hea.symm hde)
  · intro hno u hu v hv huv w₁ hw₁ w₂ hw₂ hu1 hv1 hu2 hv2
    by_contra hw12
    let a : {x // x ∈ G.vertices} := ⟨u, hu⟩
    let b : {x // x ∈ G.vertices} := ⟨w₁, hw₁⟩
    let d : {x // x ∈ G.vertices} := ⟨v, hv⟩
    let e : {x // x ∈ G.vertices} := ⟨w₂, hw₂⟩
    have hab : G.induced.Adj a b := hu1
    have hbd : G.induced.Adj b d := hv1.symm
    have hde : G.induced.Adj d e := hv2
    have hea : G.induced.Adj e a := hu2.symm
    let c : G.induced.Walk a a := .cons hab (.cons hbd (.cons hde (.cons hea .nil)))
    have hne_ab : a ≠ b := hab.ne
    have hne_bd : b ≠ d := hbd.ne
    have hne_de : d ≠ e := hde.ne
    have hne_ea : e ≠ a := hea.ne
    have hne_ad : a ≠ d := fun h ↦ huv (congrArg Subtype.val h)
    have hne_be : b ≠ e := fun h ↦ hw12 (congrArg Subtype.val h)
    have hsupp : c.support.tail.Nodup := by
      simp only [c, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      refine ⟨?_, ?_, hne_ea, not_false⟩
      · rintro (h | h | h)
        exacts [hne_bd h, hne_be h, hne_ab h.symm]
      · rintro (h | h)
        exacts [hne_de h, hne_ad h.symm]
    have hedges : c.edges.Nodup := by
      have neE : ∀ {x y z w : {t // t ∈ G.vertices}},
          ¬((x = z ∧ y = w) ∨ (x = w ∧ y = z)) → s(x, y) ≠ s(z, w) :=
        fun h heq ↦ h (Sym2.eq_iff.mp heq)
      simp only [c, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
      refine ⟨⟨neE ?_, neE ?_, neE ?_⟩, ⟨neE ?_, neE ?_⟩, neE ?_, not_false⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩); exacts [hne_ab h, hne_ad h]
      · rintro (⟨h, _⟩ | ⟨_, h⟩); exacts [hne_ad h, hne_bd h]
      · rintro (⟨_, h⟩ | ⟨_, h⟩); exacts [hne_ab h.symm, hne_be h]
      · rintro (⟨h, _⟩ | ⟨h, _⟩); exacts [hne_bd h, hne_be h]
      · rintro (⟨h, _⟩ | ⟨h, _⟩); exacts [hne_be h, hne_ab h.symm]
      · rintro (⟨h, _⟩ | ⟨h, _⟩); exacts [hne_de h, hne_ad h.symm]
    exact hno a c { edges_nodup := hedges, ne_nil := by simp [c], support_nodup := hsupp } rfl

/-- Executable Boolean test deciding `IsC4FreeGraph G`. -/
def isC4FreeGraphBool (G : Graph) : Bool :=
  G.vertices.all fun u ↦ G.vertices.all fun v ↦
    decide (u = v) ||
      G.vertices.all fun w₁ ↦ G.vertices.all fun w₂ ↦
        !(G.adjBool u w₁ && G.adjBool v w₁ && G.adjBool u w₂ && G.adjBool v w₂) ||
          decide (w₁ = w₂)

/-- `isC4FreeGraphBool G = true` iff `IsC4FreeGraph G`. -/
theorem isC4FreeGraphBool_eq_true_iff (G : Graph) :
    isC4FreeGraphBool G = true ↔ IsC4FreeGraph G := by
  simp only [isC4FreeGraphBool, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_true_eq, IsC4FreeGraph]
  constructor
  · intro h u hu v hv huv w₁ hw₁ w₂ hw₂ hu1 hv1 hu2 hv2
    rcases (h u hu v hv).resolve_left huv w₁ hw₁ w₂ hw₂ with
      (((h' | h') | h') | h') | heq
    · exact absurd ((G.adjBool_eq_true_iff u w₁).mpr hu1) (by rw [h']; decide)
    · exact absurd ((G.adjBool_eq_true_iff v w₁).mpr hv1) (by rw [h']; decide)
    · exact absurd ((G.adjBool_eq_true_iff u w₂).mpr hu2) (by rw [h']; decide)
    · exact absurd ((G.adjBool_eq_true_iff v w₂).mpr hv2) (by rw [h']; decide)
    · exact heq
  · intro h u hu v hv
    by_cases huv : u = v
    · exact Or.inl huv
    · refine Or.inr fun w₁ hw₁ w₂ hw₂ ↦ ?_
      by_cases hall : G.adjBool u w₁ = true ∧ G.adjBool v w₁ = true ∧
          G.adjBool u w₂ = true ∧ G.adjBool v w₂ = true
      · exact Or.inr (h u hu v hv huv w₁ hw₁ w₂ hw₂
          ((G.adjBool_eq_true_iff u w₁).mp hall.1)
          ((G.adjBool_eq_true_iff v w₁).mp hall.2.1)
          ((G.adjBool_eq_true_iff u w₂).mp hall.2.2.1)
          ((G.adjBool_eq_true_iff v w₂).mp hall.2.2.2))
      · left
        cases h1 : G.adjBool u w₁ <;> cases h2 : G.adjBool v w₁ <;>
          cases h3 : G.adjBool u w₂ <;> cases h4 : G.adjBool v w₂ <;>
          simp_all

/-- Testing `isC4FreeGraphBool` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_isC4FreeGraphBool :
    ComputableInPolyTime isC4FreeGraphBool encGraph encBool := by
  unfold isC4FreeGraphBool
  fun_prop

/-- **`C₄`-Free Vertex Cover**: pairs `(G, k)` where `G` is `C₄`-free on its declared vertices and
admits a vertex cover of cardinality at most `k`. -/
@[expose] def C4FreeVertexCover : Set VertexCoverInstance :=
  {x | IsC4FreeGraph x.graph ∧ x ∈ VertexCover}

/-- `C4FreeVertexCover` belongs to `NP`. -/
theorem c4FreeVertexCover_mem_NP : C4FreeVertexCover ∈ NP encVertexCoverInstance := by
  have heq : C4FreeVertexCover =
      {x : VertexCoverInstance | isC4FreeGraphBool x.graph = true ∧ x ∈ VertexCover} := by
    ext x
    simp [C4FreeVertexCover, isC4FreeGraphBool_eq_true_iff]
  rw [heq]
  exact ⟨Polynomial.X, fun q ↦ isC4FreeGraphBool q.1.graph && VertexCover.verifier q,
    by fun_prop, VertexCover.isVerifier.guard⟩

/-! ### Garey–Johnson reduction from `EUThreeSAT` to `C4FreeVertexCover` -/

private def gjVars (φ : CNF ℕ) : List ℕ :=
  selectDistinct φ.vars (List.replicate φ.vars.length true)

private theorem mem_gjVars {φ : CNF ℕ} {v : ℕ} : v ∈ gjVars φ ↔ v ∈ φ.vars :=
  mem_selectDistinct_replicate

private theorem nodup_gjVars (φ : CNF ℕ) : (gjVars φ).Nodup :=
  nodup_selectDistinct _ _

@[local fun_prop]
private theorem computableInPolyTime_gjVars :
    ComputableInPolyTime gjVars encCNF (encList encNat) := by
  have hraw : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.vars) encCNF (encList encNat) := by
    unfold CNF.vars encCNF
    fun_prop
  have hrep : ComputableInPolyTime (fun φ : CNF ℕ ↦ List.replicate φ.vars.length true)
      encCNF encBits :=
    (bitsReplicate true).comp ((length_list encNat).comp hraw)
  exact (computableInPolyTime_selectDistinct encNat).comp (hraw.prod hrep)

private def gjLitVert (i : ℕ) (b : Bool) : ℕ :=
  2 * i + if b then 1 else 0

private def gjClauseVert (n j t : ℕ) : ℕ :=
  2 * n + (3 * j + t)

/-- The `t`-th literal of the `j`-th clause of `φ` (totalized via `getD`). -/
private def gjLit (φ : CNF ℕ) (j t : ℕ) : Literal ℕ :=
  (φ.getD j []).getD t (0, false)

private theorem gjLit_eq_getElem {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) (j : Fin φ.length)
    (t : Fin 3) :
    ∃ ht : t.1 < φ[j.1].length, gjLit φ j.1 t.1 = φ[j.1][t.1]'ht := by
  have hc3 : φ[j.1].length = 3 := (hφ φ[j.1] (List.getElem_mem j.2)).1
  have ht : t.1 < φ[j.1].length := by omega
  refine ⟨ht, ?_⟩
  unfold gjLit
  rw [List.getD_eq_getElem φ [] j.2, List.getD_eq_getElem φ[j.1] (0, false) ht]

private theorem gjLit_mem_clause {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) (j : Fin φ.length)
    (t : Fin 3) : gjLit φ j.1 t.1 ∈ φ[j.1] := by
  obtain ⟨ht, heq⟩ := gjLit_eq_getElem hφ j t
  rw [heq]
  exact List.getElem_mem ht

private theorem gjLit_idxOf_spec {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) (j : Fin φ.length)
    (t : Fin 3) :
    ∃ hlt : (gjVars φ).idxOf (gjLit φ j.1 t.1).1 < (gjVars φ).length,
      (gjVars φ)[(gjVars φ).idxOf (gjLit φ j.1 t.1).1]'hlt = (gjLit φ j.1 t.1).1 ∧
      gjLitVert ((gjVars φ).idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2 <
        2 * (gjVars φ).length := by
  have hmem : (gjLit φ j.1 t.1).1 ∈ gjVars φ :=
    mem_gjVars.mpr <| List.mem_map_of_mem <|
      List.mem_flatten.mpr ⟨φ[j.1], List.getElem_mem j.2, gjLit_mem_clause hφ j t⟩
  have hlt : (gjVars φ).idxOf (gjLit φ j.1 t.1).1 < (gjVars φ).length :=
    List.idxOf_lt_length_iff.mpr hmem
  refine ⟨hlt, List.getElem_idxOf hlt, ?_⟩
  cases (gjLit φ j.1 t.1).2 <;> simp [gjLitVert] <;> omega

private theorem gjLit_idxOf_ne {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) (j : Fin φ.length)
    {t₁ t₂ : Fin 3} (hne : t₁ ≠ t₂) :
    (gjVars φ).idxOf (gjLit φ j.1 t₁.1).1 ≠ (gjVars φ).idxOf (gjLit φ j.1 t₂.1).1 := by
  intro heq
  obtain ⟨h1, hv1, _⟩ := gjLit_idxOf_spec hφ j t₁
  obtain ⟨h2, hv2, _⟩ := gjLit_idxOf_spec hφ j t₂
  obtain ⟨ht1, hl1⟩ := gjLit_eq_getElem hφ j t₁
  obtain ⟨ht2, hl2⟩ := gjLit_eq_getElem hφ j t₂
  have hvar : (φ[j.1][t₁.1]'ht1).1 = (φ[j.1][t₂.1]'ht2).1 := by
    rw [← hl1, ← hl2, ← hv1, ← hv2]
    exact congrArg (fun k : Fin (gjVars φ).length ↦ (gjVars φ)[k.1])
      (Fin.ext heq : (⟨_, h1⟩ : Fin (gjVars φ).length) = ⟨_, h2⟩)
  have hnd := (hφ φ[j.1] (List.getElem_mem j.2)).2
  have hmap : (φ[j.1].map Prod.fst)[t₁.1]'(by simpa using ht1) =
      (φ[j.1].map Prod.fst)[t₂.1]'(by simpa using ht2) := by
    simpa using hvar
  exact hne (Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp hmap))

private def gjClauseEdges (vars : List ℕ) (c : Clause ℕ) (j : ℕ) : List (ℕ × ℕ) :=
  let n := vars.length
  let v0 := gjClauseVert n j 0
  let v1 := gjClauseVert n j 1
  let v2 := gjClauseVert n j 2
  let l0 := c.getD 0 (0, false)
  let l1 := c.getD 1 (0, false)
  let l2 := c.getD 2 (0, false)
  [(v0, v1), (v1, v2), (v0, v2),
   (v0, gjLitVert (vars.idxOf l0.1) l0.2),
   (v1, gjLitVert (vars.idxOf l1.1) l1.2),
   (v2, gjLitVert (vars.idxOf l2.1) l2.2)]

private def gjGraph (φ : CNF ℕ) : Graph :=
  let vars := gjVars φ
  let n := vars.length
  let m := φ.length
  let varEdges := (List.range n).map fun i ↦ (gjLitVert i false, gjLitVert i true)
  let clEdges := φ.zipIdx.flatMap fun p ↦ gjClauseEdges vars p.1 p.2
  Graph.mk (List.range (2 * n + 3 * m)) (varEdges ++ clEdges)

/-- Polynomial-time many-one reduction from `EUThreeSAT` to `C4FreeVertexCover`. -/
def euThreeSATToC4FreeVertexCover (φ : CNF ℕ) : VertexCoverInstance :=
  if EUThreeSAT.syntaxCheck φ then
    VertexCoverInstance.mk (gjGraph φ) ((gjVars φ).length + 2 * φ.length)
  else
    VertexCoverInstance.mk (Graph.mk [0, 1] [(0, 1)]) 0

private theorem computableInPolyTime_two_mul :
    ComputableInPolyTime (fun x : ℕ ↦ 2 * x) encNat encNat := by
  have h := binary_add' (id' (encIn := encNat)) (id' (encIn := encNat))
  have heq : (fun x : ℕ ↦ x + x) = fun x : ℕ ↦ 2 * x := funext fun _ ↦ by omega
  rwa [heq] at h

private theorem computableInPolyTime_three_mul :
    ComputableInPolyTime (fun x : ℕ ↦ 3 * x) encNat encNat := by
  have h := binary_add' computableInPolyTime_two_mul (id' (encIn := encNat))
  have heq : (fun x : ℕ ↦ 2 * x + x) = fun x : ℕ ↦ 3 * x := funext fun _ ↦ by omega
  rwa [heq] at h

private theorem computableInPolyTime_gjClauseEdges :
    ComputableInPolyTime
      (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦ gjClauseEdges (gjVars q.1) q.2.1 q.2.2)
      (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary))
      (encList (encPair encNat encNat)) := by
  let encCl := encList (encPair encNat encBool)
  let encQ := encPair encCNF (encPair encCl encUnary)
  have hlit : ∀ t : ℕ, ComputableInPolyTime
      (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦ q.2.1.getD t (0, false))
      encQ (encPair encNat encBool) := fun t ↦
    listGetDWithInput ((fst _ _).comp (snd _ _)) (const t) (0, false)
  have hvarsQ : ComputableInPolyTime (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦ gjVars q.1)
      encQ (encList encNat) :=
    computableInPolyTime_gjVars.comp (fst _ _)
  have hlvert : ∀ t : ℕ, ComputableInPolyTime
      (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦
        gjLitVert ((gjVars q.1).idxOf (q.2.1.getD t (0, false)).1) (q.2.1.getD t (0, false)).2)
      encQ encNat := fun t ↦
    binary_add'
      (computableInPolyTime_two_mul.comp (unary_to_binary.comp
        ((idxOf encNat).comp (hvarsQ.prod ((fst _ _).comp (hlit t))))))
      (ComputableInPolyTime.ite ((snd _ _).comp (hlit t)) (const 1) (const 0))
  have h2nQ : ComputableInPolyTime (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦ 2 * (gjVars q.1).length)
      encQ encNat :=
    computableInPolyTime_two_mul.comp (unary_to_binary.comp ((length_list encNat).comp hvarsQ))
  have h3jQ : ComputableInPolyTime (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦ 3 * q.2.2) encQ encNat :=
    computableInPolyTime_three_mul.comp (unary_to_binary.comp ((snd _ _).comp (snd _ _)))
  have hcvert : ∀ t : ℕ, ComputableInPolyTime
      (fun q : CNF ℕ × (Clause ℕ × ℕ) ↦ gjClauseVert (gjVars q.1).length q.2.2 t)
      encQ encNat := fun t ↦
    binary_add' h2nQ (binary_add' h3jQ (const t))
  exact cons' ((hcvert 0).prod (hcvert 1)) <|
    cons' ((hcvert 1).prod (hcvert 2)) <|
      cons' ((hcvert 0).prod (hcvert 2)) <|
        cons' ((hcvert 0).prod (hlvert 0)) <|
          cons' ((hcvert 1).prod (hlvert 1)) <|
            cons' ((hcvert 2).prod (hlvert 2)) (const [])

private theorem computableInPolyTime_gjGraph :
    ComputableInPolyTime gjGraph encCNF encGraph := by
  let encCl := encList (encPair encNat encBool)
  have hn_u : ComputableInPolyTime (fun φ : CNF ℕ ↦ (gjVars φ).length) encCNF encUnary :=
    (length_list encNat).comp computableInPolyTime_gjVars
  have hm_u : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
    length_list encCl
  have htot_u : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ 2 * (gjVars φ).length + 3 * φ.length) encCNF encUnary :=
    unary_add.comp ((unary_mul.comp ((const 2).prod hn_u)).prod
      (unary_mul.comp ((const 3).prod hm_u)))
  have hverts : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ List.range (2 * (gjVars φ).length + 3 * φ.length))
      encCNF (encList encNat) := by
    have h := (map unary_to_binary).comp (range.comp htot_u)
    simpa only [Function.comp_def, List.map_id'] using h
  have hpairVar : ComputableInPolyTime
      (fun i : ℕ ↦ (gjLitVert i false, gjLitVert i true))
      encUnary (encPair encNat encNat) :=
    (binary_add' (computableInPolyTime_two_mul.comp unary_to_binary) (const 0)).prod
      (binary_add' (computableInPolyTime_two_mul.comp unary_to_binary) (const 1))
  have hve : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (gjVars φ).length).map
        fun i ↦ (gjLitVert i false, gjLitVert i true))
      encCNF (encList (encPair encNat encNat)) :=
    (map hpairVar).comp (range.comp hn_u)
  have hcle : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.zipIdx.flatMap fun p ↦ gjClauseEdges (gjVars φ) p.1 p.2)
      encCNF (encList (encPair encNat encNat)) :=
    flatMapWithInput (zipIdx encCl) computableInPolyTime_gjClauseEdges
  exact encGraph_mk_polyTime hverts (listAppend' hve hcle)

/-- `euThreeSATToC4FreeVertexCover` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_euThreeSATToC4FreeVertexCover :
    ComputableInPolyTime euThreeSATToC4FreeVertexCover encCNF encVertexCoverInstance := by
  let encCl := encList (encPair encNat encBool)
  have hn : ComputableInPolyTime (fun φ : CNF ℕ ↦ (gjVars φ).length) encCNF encNat :=
    unary_to_binary.comp ((length_list encNat).comp computableInPolyTime_gjVars)
  have hm : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encNat :=
    unary_to_binary.comp (length_list encCl)
  have h2m : ComputableInPolyTime (fun φ : CNF ℕ ↦ 2 * φ.length) encCNF encNat := by
    have h := binary_add' hm hm
    have heq : (fun φ : CNF ℕ ↦ φ.length + φ.length) = fun φ : CNF ℕ ↦ 2 * φ.length :=
      funext fun _ ↦ by omega
    rwa [heq] at h
  exact ComputableInPolyTime.ite (by fun_prop)
    (encVertexCoverInstance_mk_polyTime computableInPolyTime_gjGraph (binary_add' hn h2m))
    (const (VertexCoverInstance.mk (Graph.mk [0, 1] [(0, 1)]) 0))

private theorem gjGraph_adj_cases {φ : CNF ℕ} {u v : ℕ}
    (hadj : (gjGraph φ).toSimpleGraph.Adj u v) :
    let n := (gjVars φ).length
    (∃ i < n, (u = gjLitVert i false ∧ v = gjLitVert i true) ∨
      (u = gjLitVert i true ∧ v = gjLitVert i false)) ∨
    (∃ (j : Fin φ.length) (t₁ t₂ : Fin 3), t₁ ≠ t₂ ∧
      u = gjClauseVert n j.1 t₁.1 ∧ v = gjClauseVert n j.1 t₂.1) ∨
    (∃ (j : Fin φ.length) (t : Fin 3),
      let lv := gjLitVert ((gjVars φ).idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2
      (u = gjClauseVert n j.1 t.1 ∧ v = lv) ∨ (v = gjClauseVert n j.1 t.1 ∧ u = lv)) := by
  set vars := gjVars φ
  set n := vars.length
  have dir : ∀ {a b : ℕ}, (a, b) ∈ (gjGraph φ).edges →
      (∃ i < n, a = gjLitVert i false ∧ b = gjLitVert i true) ∨
      (∃ (j : Fin φ.length) (t₁ t₂ : Fin 3), t₁ ≠ t₂ ∧
        a = gjClauseVert n j.1 t₁.1 ∧ b = gjClauseVert n j.1 t₂.1) ∨
      (∃ (j : Fin φ.length) (t : Fin 3),
        a = gjClauseVert n j.1 t.1 ∧
        b = gjLitVert (vars.idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2) := by
    intro a b hmem
    simp only [gjGraph, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at hmem
    rcases hmem with ⟨i, hi, heq⟩ | ⟨⟨c, j⟩, hzip, hce⟩
    · exact Or.inl ⟨i, hi, (Prod.mk.inj heq).1.symm, (Prod.mk.inj heq).2.symm⟩
    · obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hzip)
      have hj' : j < φ.length := by simpa using hj
      have hc_eq : c = φ.getD j [] := by
        rw [List.getD_eq_getElem φ [] hj']
        exact hcj.symm
      subst hc_eq
      simp only [gjClauseEdges, List.mem_cons, List.not_mem_nil, or_false] at hce
      rcases hce with h | h | h | h | h | h
      · exact Or.inr (Or.inl ⟨⟨j, hj'⟩, 0, 1, by decide, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
      · exact Or.inr (Or.inl ⟨⟨j, hj'⟩, 1, 2, by decide, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
      · exact Or.inr (Or.inl ⟨⟨j, hj'⟩, 0, 2, by decide, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
      · exact Or.inr (Or.inr ⟨⟨j, hj'⟩, 0, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
      · exact Or.inr (Or.inr ⟨⟨j, hj'⟩, 1, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
      · exact Or.inr (Or.inr ⟨⟨j, hj'⟩, 2, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
  rcases (Graph.toSimpleGraph_adj.mp hadj).2 with h | h
  · rcases dir h with ⟨i, hi, h1, h2⟩ | ⟨j, t₁, t₂, hne, h1, h2⟩ | ⟨j, t, h1, h2⟩
    · exact Or.inl ⟨i, hi, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr (Or.inl ⟨j, t₁, t₂, hne, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨j, t, Or.inl ⟨h1, h2⟩⟩)
  · rcases dir h with ⟨i, hi, h1, h2⟩ | ⟨j, t₁, t₂, hne, h1, h2⟩ | ⟨j, t, h1, h2⟩
    · exact Or.inl ⟨i, hi, Or.inr ⟨h2, h1⟩⟩
    · exact Or.inr (Or.inl ⟨j, t₂, t₁, hne.symm, h2, h1⟩)
    · exact Or.inr (Or.inr ⟨j, t, Or.inr ⟨h1, h2⟩⟩)

private theorem gjClauseVert_ge (n j t : ℕ) : 2 * n ≤ gjClauseVert n j t := by
  simp [gjClauseVert]

private theorem gjClauseVert_inj {n : ℕ} {j₁ j₂ : ℕ} {t₁ t₂ : Fin 3}
    (h : gjClauseVert n j₁ t₁.1 = gjClauseVert n j₂ t₂.1) : j₁ = j₂ ∧ t₁ = t₂ := by
  have := t₁.2; have := t₂.2
  simp only [gjClauseVert] at h
  exact ⟨by omega, Fin.ext (by omega)⟩

private theorem gjLitVert_div_two (i : ℕ) (b : Bool) : gjLitVert i b / 2 = i := by
  cases b <;> simp [gjLitVert]; omega

private theorem gjLitVert_lt {i n : ℕ} (hi : i < n) (b : Bool) : gjLitVert i b < 2 * n := by
  cases b <;> simp [gjLitVert] <;> omega

/-- For every exact-3-distinct CNF `φ`, the Garey–Johnson graph `gjGraph φ` is `C₄`-free. -/
private theorem gjGraph_isC4FreeGraph {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) :
    IsC4FreeGraph (gjGraph φ) := by
  set vars := gjVars φ
  set n := vars.length
  let lvOf (j : Fin φ.length) (t : Fin 3) : ℕ :=
    gjLitVert (vars.idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2
  have lvOf_lt : ∀ (j : Fin φ.length) (t : Fin 3), lvOf j t < 2 * n := fun j t ↦
    (gjLit_idxOf_spec hφ j t).2.2
  have lvOf_div_ne : ∀ (j : Fin φ.length) {t₁ t₂ : Fin 3}, t₁ ≠ t₂ →
      lvOf j t₁ / 2 ≠ lvOf j t₂ / 2 := by
    intro j t₁ t₂ hne
    simpa only [lvOf, gjLitVert_div_two] using gjLit_idxOf_ne hφ j hne
  -- A clause vertex `(j, t)` has exact unique literal neighbor `lvOf j t`.
  have cl_lit_nbr : ∀ (j : Fin φ.length) (t : Fin 3) {y : ℕ}, y < 2 * n →
      (gjGraph φ).toSimpleGraph.Adj (gjClauseVert n j.1 t.1) y → y = lvOf j t := by
    intro j t y hy ha
    rcases gjGraph_adj_cases ha with ⟨i, hi, ⟨hx, _⟩ | ⟨hx, _⟩⟩ |
        ⟨_, _, _, _, _, hy'⟩ | ⟨j', t', ⟨hx, hy'⟩ | ⟨hy', _⟩⟩
    · exact absurd (hx ▸ gjClauseVert_ge n j.1 t.1) (not_le_of_gt (gjLitVert_lt hi false))
    · exact absurd (hx ▸ gjClauseVert_ge n j.1 t.1) (not_le_of_gt (gjLitVert_lt hi true))
    · exact absurd (hy' ▸ gjClauseVert_ge n _ _) (not_le_of_gt hy)
    · obtain ⟨hj, ht⟩ := gjClauseVert_inj hx
      cases Fin.ext hj.symm; cases ht.symm
      exact hy'
    · exact absurd (hy' ▸ gjClauseVert_ge n _ _) (not_le_of_gt hy)
  -- Two adjacent literal vertices share the same variable (`x / 2 = y / 2`) and are unique.
  have lit_lit_nbr : ∀ {x y : ℕ}, x < 2 * n → y < 2 * n →
      (gjGraph φ).toSimpleGraph.Adj x y →
      y = (if x % 2 = 0 then x + 1 else x - 1) ∧ x / 2 = y / 2 := by
    intro x y hx hy ha
    rcases gjGraph_adj_cases ha with ⟨i, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨_, _, _, _, hx', _⟩ | ⟨_, _, ⟨hx', _⟩ | ⟨hy', _⟩⟩
    · simp [gjLitVert]; omega
    · simp [gjLitVert]; omega
    · exact absurd (hx' ▸ gjClauseVert_ge n _ _) (not_le_of_gt hx)
    · exact absurd (hx' ▸ gjClauseVert_ge n _ _) (not_le_of_gt hx)
    · exact absurd (hy' ▸ gjClauseVert_ge n _ _) (not_le_of_gt hy)
  -- Neighbors of a clause vertex `(j, t)`: either `(j, t')` (`t' ≠ t`) or `lvOf j t`.
  have cl_nbr : ∀ (j : Fin φ.length) (t : Fin 3) {x : ℕ},
      (gjGraph φ).toSimpleGraph.Adj x (gjClauseVert n j.1 t.1) →
      (∃ t' : Fin 3, t' ≠ t ∧ x = gjClauseVert n j.1 t'.1) ∨ x = lvOf j t := by
    intro j t x ha
    rcases gjGraph_adj_cases ha with ⟨i, hi, ⟨_, hw⟩ | ⟨_, hw⟩⟩ |
        ⟨j', t₁, t₂, hne, hx, hw⟩ | ⟨j', t', ⟨_, hw⟩ | ⟨hw, hx⟩⟩
    · exact absurd (hw ▸ gjClauseVert_ge n j.1 t.1) (not_le_of_gt (gjLitVert_lt hi true))
    · exact absurd (hw ▸ gjClauseVert_ge n j.1 t.1) (not_le_of_gt (gjLitVert_lt hi false))
    · obtain ⟨hj, ht⟩ := gjClauseVert_inj hw
      cases Fin.ext hj; cases ht
      exact Or.inl ⟨t₁, hne, hx⟩
    · have hlt : lvOf j' t' < 2 * n := lvOf_lt j' t'
      dsimp only [lvOf] at hlt
      rw [← hw] at hlt
      exact absurd (gjClauseVert_ge n j.1 t.1) (not_le_of_gt hlt)
    · obtain ⟨hj, ht⟩ := gjClauseVert_inj hw
      cases Fin.ext hj; cases ht
      exact Or.inr hx
  -- No mixed pair `(w_lit < 2 * n, gjClauseVert n j t)` can share two distinct neighbors `u ≠ v`.
  have no_mixed : ∀ {u v w : ℕ} (j : Fin φ.length) (t : Fin 3), u ≠ v → w < 2 * n →
      (gjGraph φ).toSimpleGraph.Adj u w → (gjGraph φ).toSimpleGraph.Adj v w →
      (gjGraph φ).toSimpleGraph.Adj u (gjClauseVert n j.1 t.1) →
      (gjGraph φ).toSimpleGraph.Adj v (gjClauseVert n j.1 t.1) → False := by
    intro u v w j t huv hw huw hvw huc hvc
    rcases cl_nbr j t huc with ⟨tu, htu, rfl⟩ | rfl <;>
      rcases cl_nbr j t hvc with ⟨tv, htv, rfl⟩ | rfl
    · have hne_t : tu ≠ tv := fun h ↦ huv (by rw [h])
      have heq := (cl_lit_nbr j tu hw huw).symm.trans (cl_lit_nbr j tv hw hvw)
      exact lvOf_div_ne j hne_t (congrArg (· / 2) heq)
    · have hw_u := cl_lit_nbr j tu hw huw
      have hdiv := (lit_lit_nbr (lvOf_lt j t) hw hvw).2
      rw [hw_u] at hdiv
      exact lvOf_div_ne j htu hdiv.symm
    · have hw_v := cl_lit_nbr j tv hw hvw
      have hdiv := (lit_lit_nbr (lvOf_lt j t) hw huw).2
      rw [hw_v] at hdiv
      exact lvOf_div_ne j htv hdiv.symm
    · exact huv rfl
  have decode_cl : ∀ {w : ℕ}, w ∈ (gjGraph φ).vertices → 2 * n ≤ w →
      ∃ (j : Fin φ.length) (t : Fin 3), w = gjClauseVert n j.1 t.1 := by
    intro w hw hge
    have hlt : w < 2 * n + 3 * φ.length := List.mem_range.mp hw
    exact ⟨⟨(w - 2 * n) / 3, by omega⟩, ⟨(w - 2 * n) % 3, by omega⟩,
      by simp [gjClauseVert]; omega⟩
  intro u hu v _ huv w₁ hw₁ w₂ hw₂ hu1 hv1 hu2 hv2
  by_cases h1 : w₁ < 2 * n <;> by_cases h2 : w₂ < 2 * n
  · by_cases hu_lt : u < 2 * n
    · exact (lit_lit_nbr hu_lt h1 hu1).1.trans (lit_lit_nbr hu_lt h2 hu2).1.symm
    · obtain ⟨j, t, rfl⟩ := decode_cl hu (Nat.not_lt.mp hu_lt)
      exact (cl_lit_nbr j t h1 hu1).trans (cl_lit_nbr j t h2 hu2).symm
  · obtain ⟨j, t, rfl⟩ := decode_cl hw₂ (Nat.not_lt.mp h2)
    exact False.elim (no_mixed j t huv h1 hu1 hv1 hu2 hv2)
  · obtain ⟨j, t, rfl⟩ := decode_cl hw₁ (Nat.not_lt.mp h1)
    exact False.elim (no_mixed j t huv h2 hu2 hv2 hu1 hv1)
  · obtain ⟨j₁, t₁, rfl⟩ := decode_cl hw₁ (Nat.not_lt.mp h1)
    obtain ⟨j₂, t₂, rfl⟩ := decode_cl hw₂ (Nat.not_lt.mp h2)
    rcases cl_nbr j₁ t₁ hu1 with ⟨tu₁, htu₁, hu_eq⟩ | hu_lit <;>
      rcases cl_nbr j₂ t₂ hu2 with ⟨tu₂, htu₂, hu_eq'⟩ | hu_lit'
    · obtain ⟨hj, htu⟩ := gjClauseVert_inj (hu_eq.symm.trans hu_eq')
      cases Fin.ext hj; cases htu
      by_contra hne_w
      have ht12 : t₁ ≠ t₂ := fun h ↦ hne_w (by rw [h])
      rcases cl_nbr j₁ t₁ hv1 with ⟨tv₁, htv₁, hv_eq⟩ | hv_lit <;>
        rcases cl_nbr j₁ t₂ hv2 with ⟨tv₂, htv₂, hv_eq'⟩ | hv_lit'
      · obtain ⟨_, htv⟩ := gjClauseVert_inj (hv_eq.symm.trans hv_eq')
        cases htv
        have : tu₁.1 ≠ tv₁.1 := fun h ↦ huv (by rw [hu_eq, hv_eq, h])
        have : tu₁.1 ≠ t₁.1 := fun h ↦ htu₁ (Fin.ext h)
        have : tu₁.1 ≠ t₂.1 := fun h ↦ htu₂ (Fin.ext h)
        have : tv₁.1 ≠ t₁.1 := fun h ↦ htv₁ (Fin.ext h)
        have : tv₁.1 ≠ t₂.1 := fun h ↦ htv₂ (Fin.ext h)
        have : t₁.1 ≠ t₂.1 := fun h ↦ ht12 (Fin.ext h)
        have := tu₁.2; have := tv₁.2; have := t₁.2; have := t₂.2
        omega
      · have hlt := lvOf_lt j₁ t₂; rw [← hv_lit', hv_eq] at hlt
        exact absurd (gjClauseVert_ge n _ _) (not_le_of_gt hlt)
      · have hlt := lvOf_lt j₁ t₁; rw [← hv_lit, hv_eq'] at hlt
        exact absurd (gjClauseVert_ge n _ _) (not_le_of_gt hlt)
      · exact lvOf_div_ne j₁ ht12 (congrArg (· / 2) (hv_lit.symm.trans hv_lit'))
    · have hlt := lvOf_lt j₂ t₂; rw [← hu_lit', hu_eq] at hlt
      exact absurd (gjClauseVert_ge n _ _) (not_le_of_gt hlt)
    · have hlt := lvOf_lt j₁ t₁; rw [← hu_lit, hu_eq'] at hlt
      exact absurd (gjClauseVert_ge n _ _) (not_le_of_gt hlt)
    · rcases cl_nbr j₁ t₁ hv1 with ⟨tv₁, _, hv_eq⟩ | hv_lit <;>
        rcases cl_nbr j₂ t₂ hv2 with ⟨tv₂, _, hv_eq'⟩ | hv_lit'
      · obtain ⟨hj, _⟩ := gjClauseVert_inj (hv_eq.symm.trans hv_eq')
        cases Fin.ext hj
        by_contra hne_w
        have ht12 : t₁ ≠ t₂ := fun h ↦ hne_w (by rw [h])
        exact lvOf_div_ne j₁ ht12 (congrArg (· / 2) (hu_lit.symm.trans hu_lit'))
      · have hlt := lvOf_lt j₂ t₂; rw [← hv_lit', hv_eq] at hlt
        exact absurd (gjClauseVert_ge n _ _) (not_le_of_gt hlt)
      · have hlt := lvOf_lt j₁ t₁; rw [← hv_lit, hv_eq'] at hlt
        exact absurd (gjClauseVert_ge n _ _) (not_le_of_gt hlt)
      · exact absurd (hu_lit.trans hv_lit.symm) huv

/-- Correctness of `euThreeSATToC4FreeVertexCover`: maps `φ` into `C4FreeVertexCover` iff
`φ ∈ EUThreeSAT`. -/
theorem euThreeSATToC4FreeVertexCover_mem_iff (φ : CNF ℕ) :
    euThreeSATToC4FreeVertexCover φ ∈ C4FreeVertexCover ↔ φ ∈ EUThreeSAT := by
  classical
  unfold euThreeSATToC4FreeVertexCover
  split_ifs with hsyn
  · have hφ : φ.IsExactThreeDistinct := (EUThreeSAT.syntaxCheck_iff φ).mp hsyn
    simp only [C4FreeVertexCover, EUThreeSAT, Set.mem_ofPred_eq, gjGraph_isC4FreeGraph hφ, hφ,
      true_and, mem_VertexCover_iff_mk]
    set vars := gjVars φ
    set n := vars.length
    set m := φ.length
    set G := gjGraph φ
    have hV : ∀ x, x ∈ G.vertices ↔ x < 2 * n + 3 * m := fun _ ↦ List.mem_range
    constructor
    · rintro ⟨S, _, hcov, hcard⟩
      let varBlock (i : Fin n) : Finset ℕ := {gjLitVert i.1 false, gjLitVert i.1 true}
      let clBlock (j : Fin m) : Finset ℕ :=
        {gjClauseVert n j.1 0, gjClauseVert n j.1 1, gjClauseVert n j.1 2}
      have hvar_adj : ∀ i : Fin n, G.toSimpleGraph.Adj (gjLitVert i.1 false) (gjLitVert i.1 true) :=
        fun i ↦ Graph.toSimpleGraph_adj.mpr ⟨by simp [gjLitVert], Or.inl <|
          List.mem_append_left _ (List.mem_map.mpr ⟨i.1, List.mem_range.mpr i.2, rfl⟩)⟩
      have hcl_adj : ∀ (j : Fin m) (a b : ℕ),
          (a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 2 ∨ a = 0 ∧ b = 2) →
          G.toSimpleGraph.Adj (gjClauseVert n j.1 a) (gjClauseVert n j.1 b) := by
        rintro j a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          exact Graph.toSimpleGraph_adj.mpr ⟨by simp [gjClauseVert], Or.inl <|
            List.mem_append_right _ <| List.mem_flatMap.mpr
              ⟨(φ[j.1], j.1), List.mem_zipIdx_iff_getElem?.mpr (by simp),
                by simp [gjClauseEdges, n, vars]⟩⟩
      have hcl_lit_adj : ∀ (j : Fin m) (t : Fin 3),
          G.toSimpleGraph.Adj (gjClauseVert n j.1 t.1)
            (gjLitVert (vars.idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2) := by
        intro j t
        have hlt := (gjLit_idxOf_spec hφ j t).2.2
        have hne : gjClauseVert n j.1 t.1 ≠
            gjLitVert (vars.idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2 :=
          ne_of_gt (lt_of_lt_of_le hlt (gjClauseVert_ge n j.1 t.1))
        refine Graph.toSimpleGraph_adj.mpr ⟨hne, Or.inl <|
          List.mem_append_right _ <| List.mem_flatMap.mpr
            ⟨(φ[j.1], j.1), List.mem_zipIdx_iff_getElem?.mpr (by simp), ?_⟩⟩
        have hgd : φ.getD j.1 [] = φ[j.1] := List.getD_eq_getElem φ [] j.2
        rcases t with ⟨_ | _ | _ | _, ht3⟩
        · dsimp only [gjLit, gjClauseEdges]; rw [hgd]; simp [n, vars]
        · dsimp only [gjLit, gjClauseEdges]; rw [hgd]; simp [n, vars]
        · dsimp only [gjLit, gjClauseEdges]; rw [hgd]; simp [n, vars]
        · omega
      have hvar_lb : ∀ i : Fin n, 1 ≤ (S ∩ varBlock i).card := fun i ↦ Finset.card_pos.mpr <| by
        have h0 := (hV _).mpr ((gjLitVert_lt i.2 false).trans_le (Nat.le_add_right _ _))
        have h1 := (hV _).mpr ((gjLitVert_lt i.2 true).trans_le (Nat.le_add_right _ _))
        rcases hcov _ h0 _ h1 (hvar_adj i) with h | h
        · exact ⟨_, Finset.mem_inter.mpr ⟨h, by simp [varBlock]⟩⟩
        · exact ⟨_, Finset.mem_inter.mpr ⟨h, by simp [varBlock]⟩⟩
      have hcl_memV : ∀ (j : Fin m) (a : ℕ), a < 3 → gjClauseVert n j.1 a ∈ G.vertices :=
        fun j a ha ↦ (hV _).mpr (by have := j.2; simp [gjClauseVert]; omega)
      have hcl_lb : ∀ j : Fin m, 2 ≤ (S ∩ clBlock j).card := fun j ↦ by
        have h01 := hcov _ (hcl_memV j 0 (by decide)) _ (hcl_memV j 1 (by decide))
          (hcl_adj j 0 1 (Or.inl ⟨rfl, rfl⟩))
        have h12 := hcov _ (hcl_memV j 1 (by decide)) _ (hcl_memV j 2 (by decide))
          (hcl_adj j 1 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        have h02 := hcov _ (hcl_memV j 0 (by decide)) _ (hcl_memV j 2 (by decide))
          (hcl_adj j 0 2 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        have pair2 : ∀ {a b : ℕ}, a ≠ b → a ∈ S ∩ clBlock j → b ∈ S ∩ clBlock j →
            2 ≤ (S ∩ clBlock j).card := fun {a b} hne ha hb ↦ by
          have hsub : ({a, b} : Finset ℕ) ⊆ S ∩ clBlock j := fun x hx ↦ by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact ha
            · rw [Finset.mem_singleton.mp hx']; exact hb
          have hc := Finset.card_le_card hsub
          rwa [Finset.card_pair hne] at hc
        rcases h01 with h0 | h1
        · rcases h12 with h1 | h2
          · exact pair2 (by simp [gjClauseVert])
              (Finset.mem_inter.mpr ⟨h0, by simp [clBlock]⟩)
              (Finset.mem_inter.mpr ⟨h1, by simp [clBlock]⟩)
          · exact pair2 (by simp [gjClauseVert])
              (Finset.mem_inter.mpr ⟨h0, by simp [clBlock]⟩)
              (Finset.mem_inter.mpr ⟨h2, by simp [clBlock]⟩)
        · rcases h02 with h0 | h2
          · exact pair2 (by simp [gjClauseVert])
              (Finset.mem_inter.mpr ⟨h0, by simp [clBlock]⟩)
              (Finset.mem_inter.mpr ⟨h1, by simp [clBlock]⟩)
          · exact pair2 (by simp [gjClauseVert])
              (Finset.mem_inter.mpr ⟨h1, by simp [clBlock]⟩)
              (Finset.mem_inter.mpr ⟨h2, by simp [clBlock]⟩)
      let allVar := (Finset.univ : Finset (Fin n)).biUnion fun i ↦ S ∩ varBlock i
      let allCl := (Finset.univ : Finset (Fin m)).biUnion fun j ↦ S ∩ clBlock j
      have hd_var : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ i' ∈ (Finset.univ : Finset (Fin n)),
          i ≠ i' → Disjoint (S ∩ varBlock i) (S ∩ varBlock i') :=
        fun i _ i' _ hne ↦ Finset.disjoint_left.mpr fun x h1 h2 ↦ hne <| Fin.ext <| by
          have d1 : x / 2 = i.1 := by
            rcases Finset.mem_insert.mp (Finset.mem_inter.mp h1).2 with rfl | h
            · exact gjLitVert_div_two i.1 false
            · rw [Finset.mem_singleton.mp h]; exact gjLitVert_div_two i.1 true
          have d2 : x / 2 = i'.1 := by
            rcases Finset.mem_insert.mp (Finset.mem_inter.mp h2).2 with rfl | h
            · exact gjLitVert_div_two i'.1 false
            · rw [Finset.mem_singleton.mp h]; exact gjLitVert_div_two i'.1 true
          exact d1.symm.trans d2
      have hd_cl : ∀ j ∈ (Finset.univ : Finset (Fin m)), ∀ j' ∈ (Finset.univ : Finset (Fin m)),
          j ≠ j' → Disjoint (S ∩ clBlock j) (S ∩ clBlock j') :=
        fun j _ j' _ hne ↦ Finset.disjoint_left.mpr fun x h1 h2 ↦ hne <| Fin.ext <| by
          have m1 := (Finset.mem_inter.mp h1).2
          have m2 := (Finset.mem_inter.mp h2).2
          simp only [clBlock, gjClauseVert, Finset.mem_insert, Finset.mem_singleton] at m1 m2
          omega
      have hd_vc : Disjoint allVar allCl := Finset.disjoint_left.mpr fun x h1 h2 ↦ by
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h1
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp h2
        have hlt : x < 2 * n := by
          rcases Finset.mem_insert.mp (Finset.mem_inter.mp hi).2 with rfl | h
          · exact gjLitVert_lt i.2 false
          · rw [Finset.mem_singleton.mp h]; exact gjLitVert_lt i.2 true
        have hge : 2 * n ≤ x := by
          have m2 := (Finset.mem_inter.mp hj).2
          simp only [clBlock, gjClauseVert, Finset.mem_insert, Finset.mem_singleton] at m2
          omega
        omega
      have hcard_var : allVar.card = ∑ i : Fin n, (S ∩ varBlock i).card :=
        Finset.card_biUnion hd_var
      have hcard_cl : allCl.card = ∑ j : Fin m, (S ∩ clBlock j).card :=
        Finset.card_biUnion hd_cl
      have hsum_le : allVar.card + allCl.card ≤ n + 2 * m := by
        rw [← Finset.card_union_of_disjoint hd_vc, ← hcard]
        refine Finset.card_le_card fun x hx ↦ ?_
        rcases Finset.mem_union.mp hx with h | h <;>
        · obtain ⟨_, _, hm⟩ := Finset.mem_biUnion.mp h
          exact (Finset.mem_inter.mp hm).1
      have hlb_var : n ≤ ∑ i : Fin n, (S ∩ varBlock i).card := by
        simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hvar_lb i
      have hlb_cl : 2 * m ≤ ∑ j : Fin m, (S ∩ clBlock j).card := by
        have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hcl_lb j
        simpa [Nat.mul_comm] using h
      have hvar_eq1 : ∀ i : Fin n, (S ∩ varBlock i).card = 1 := fun i ↦ by
        by_contra hne1
        have hstrict := Finset.sum_lt_sum (fun i' (_ : i' ∈ Finset.univ) ↦ hvar_lb i')
          ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hvar_lb i) (Ne.symm hne1)⟩
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_one] at hstrict
        omega
      have hcl_eq2 : ∀ j : Fin m, (S ∩ clBlock j).card = 2 := fun j ↦ by
        by_contra hne2
        have hstrict := Finset.sum_lt_sum (fun j' (_ : j' ∈ Finset.univ) ↦ hcl_lb j')
          ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hcl_lb j) (Ne.symm hne2)⟩
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hstrict
        omega
      let σ : ℕ → Bool := fun v ↦ decide (gjLitVert (vars.idxOf v) true ∈ S)
      have hlit_in_S : ∀ (i : Fin n) (b : Bool),
          gjLitVert i.1 b ∈ S → σ vars[i.1] = b := by
        intro i b hbS
        have hidx : vars.idxOf vars[i.1] = i.1 := List.Nodup.idxOf_getElem (nodup_gjVars φ) i.1 i.2
        simp only [σ, hidx]
        cases b with
        | true => exact decide_eq_true hbS
        | false =>
          refine decide_eq_false fun htS ↦ ?_
          have hsub : varBlock i ⊆ S ∩ varBlock i := fun x hx ↦ by
            refine Finset.mem_inter.mpr ⟨?_, hx⟩
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hbS
            · rw [Finset.mem_singleton.mp hx']; exact htS
          have h2 := Finset.card_le_card hsub
          rw [Finset.card_pair (by simp [gjLitVert]), hvar_eq1 i] at h2
          exact absurd h2 (by decide)
      refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc ↦ ?_⟩
      obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hc
      let j : Fin m := ⟨j₀, hj₀⟩
      have hnot_all : ¬clBlock j ⊆ S := fun hsub ↦ by
        have heq : S ∩ clBlock j = clBlock j := Finset.inter_eq_right.mpr hsub
        have hc3 : (clBlock j).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [gjClauseVert]),
            Finset.card_insert_of_notMem (by simp [gjClauseVert]), Finset.card_singleton]
        exact absurd ((hcl_eq2 j).symm.trans (congrArg Finset.card heq |>.trans hc3)) (by decide)
      obtain ⟨w, hwC, hwS⟩ := Finset.not_subset.mp hnot_all
      have hex_t : ∃ t : Fin 3, w = gjClauseVert n j.1 t.1 := by
        simp only [clBlock, Finset.mem_insert, Finset.mem_singleton] at hwC
        rcases hwC with rfl | rfl | rfl
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
      obtain ⟨t, rfl⟩ := hex_t
      obtain ⟨hlt_l, hvar_l, hlv_lt⟩ := gjLit_idxOf_spec hφ j t
      have hlitS : gjLitVert (vars.idxOf (gjLit φ j.1 t.1).1) (gjLit φ j.1 t.1).2 ∈ S :=
        (hcov _ (hcl_memV j t.1 t.2) _ ((hV _).mpr (hlv_lt.trans_le (Nat.le_add_right _ _)))
          (hcl_lit_adj j t)).resolve_left hwS
      have hσ := hlit_in_S ⟨vars.idxOf (gjLit φ j.1 t.1).1, hlt_l⟩ (gjLit φ j.1 t.1).2 hlitS
      rw [hvar_l] at hσ
      exact (Clause.eval_eq_true_iff σ φ[j.1]).mpr ⟨gjLit φ j.1 t.1, gjLit_mem_clause hφ j t, hσ⟩
    · rintro ⟨σ, hσ⟩
      have hchoose : ∀ j : Fin m, ∃ t : Fin 3, σ (gjLit φ j.1 t.1).1 = (gjLit φ j.1 t.1).2 :=
        fun j ↦ by
          obtain ⟨l, hl, hsat⟩ := (Clause.eval_eq_true_iff σ φ[j.1]).mp
            ((CNF.eval_eq_true_iff σ φ).mp hσ φ[j.1] (List.getElem_mem j.2))
          obtain ⟨t₀, ht₀, rfl⟩ := List.getElem_of_mem hl
          have hc3 : φ[j.1].length = 3 := (hφ φ[j.1] (List.getElem_mem j.2)).1
          let t : Fin 3 := ⟨t₀, by omega⟩
          obtain ⟨_, heq⟩ := gjLit_eq_getElem hφ j t
          exact ⟨t, by rwa [heq]⟩
      choose tSat htSat using hchoose
      let Svar : Finset ℕ := (Finset.univ : Finset (Fin n)).image fun i ↦
        gjLitVert i.1 (σ vars[i.1])
      let Scl : Finset ℕ := (Finset.univ : Finset (Fin m)).biUnion fun j ↦
        ((Finset.univ : Finset (Fin 3)).erase (tSat j)).image fun t ↦ gjClauseVert n j.1 t.1
      have hSvar_card : Svar.card = n := by
        rw [Finset.card_image_of_injective _ (fun i₁ i₂ h ↦ Fin.ext <| by
          have := congrArg (· / 2) h
          simpa only [gjLitVert_div_two] using this), Finset.card_univ, Fintype.card_fin]
      have hScl_card : Scl.card = 2 * m := by
        rw [Finset.card_biUnion]
        · have h2 : ∀ j : Fin m, (((Finset.univ : Finset (Fin 3)).erase (tSat j)).image
              fun t ↦ gjClauseVert n j.1 t.1).card = 2 := fun j ↦ by
            rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (gjClauseVert_inj h).2)]
            simp
          simp [h2, Nat.mul_comm]
        · intro j₁ _ j₂ _ hne
          refine Finset.disjoint_left.mpr fun x h1 h2 ↦ hne ?_
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨b, _, heq⟩ := Finset.mem_image.mp h2
          exact Fin.ext (gjClauseVert_inj heq.symm).1
      have hdisj : Disjoint Svar Scl := Finset.disjoint_left.mpr fun x h1 h2 ↦ by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨j, _, hx2⟩ := Finset.mem_biUnion.mp h2
        obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hx2
        exact not_le_of_gt (gjLitVert_lt i.2 (σ vars[i.1])) (heq ▸ gjClauseVert_ge n j.1 t.1)
      refine ⟨Svar ∪ Scl, fun x hx ↦ (hV x).mpr ?_, fun u _ v _ hadj ↦ ?_,
        by rw [Finset.card_union_of_disjoint hdisj, hSvar_card, hScl_card]⟩
      · rcases Finset.mem_union.mp hx with h1 | h2
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
          exact (gjLitVert_lt i.2 _).trans_le (Nat.le_add_right _ _)
        · obtain ⟨j, _, hx2⟩ := Finset.mem_biUnion.mp h2
          obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx2
          have := j.2; have := t.2
          simp [gjClauseVert]; omega
      · have memVar : ∀ (i : Fin n), gjLitVert i.1 (σ vars[i.1]) ∈ Svar ∪ Scl := fun i ↦
          Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        have memCl : ∀ (j : Fin m) (t : Fin 3), t ≠ tSat j →
            gjClauseVert n j.1 t.1 ∈ Svar ∪ Scl := fun j t ht ↦
          Finset.mem_union_right _ <| Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_univ j, Finset.mem_image_of_mem _
              (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)⟩
        rcases gjGraph_adj_cases hadj with ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
            ⟨j, t₁, t₂, hne, rfl, rfl⟩ | ⟨j, t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · have hm := memVar ⟨i, hi⟩
          cases h : σ vars[i] <;> rw [h] at hm
          exacts [Or.inl hm, Or.inr hm]
        · have hm := memVar ⟨i, hi⟩
          cases h : σ vars[i] <;> rw [h] at hm
          exacts [Or.inr hm, Or.inl hm]
        · by_cases h1 : t₁ = tSat j
          · exact Or.inr (memCl j t₂ fun h2 ↦ hne (h1.trans h2.symm))
          · exact Or.inl (memCl j t₁ h1)
        · by_cases ht : t = tSat j
          · subst ht
            obtain ⟨hlt_l, hvar_l, _⟩ := gjLit_idxOf_spec hφ j (tSat j)
            have hm := memVar ⟨vars.idxOf (gjLit φ j.1 (tSat j).1).1, hlt_l⟩
            rw [hvar_l, htSat j] at hm
            exact Or.inr hm
          · exact Or.inl (memCl j t ht)
        · by_cases ht : t = tSat j
          · subst ht
            obtain ⟨hlt_l, hvar_l, _⟩ := gjLit_idxOf_spec hφ j (tSat j)
            have hm := memVar ⟨vars.idxOf (gjLit φ j.1 (tSat j).1).1, hlt_l⟩
            rw [hvar_l, htSat j] at hm
            exact Or.inl hm
          · exact Or.inr (memCl j t ht)
  · have hnsyn : ¬φ.IsExactThreeDistinct := mt (EUThreeSAT.syntaxCheck_iff φ).mpr hsyn
    simp only [C4FreeVertexCover, EUThreeSAT, Set.mem_ofPred_eq, mem_VertexCover_iff_mk]
    refine ⟨fun ⟨_, S, _, hcov, hcard⟩ ↦ ?_, fun ⟨hw, _⟩ ↦ False.elim (hnsyn hw)⟩
    have hS0 : S = ∅ := Finset.card_eq_zero.mp hcard
    have h01 := hcov 0 (by decide) 1 (by decide) (by rw [Graph.toSimpleGraph_adj]; decide)
    simp [hS0] at h01

/-- `EUThreeSAT` reduces in polynomial time to `C4FreeVertexCover`. -/
theorem polyTimeReducible_euThreeSAT_c4FreeVertexCover :
    PolyTimeReducible encCNF encVertexCoverInstance EUThreeSAT C4FreeVertexCover :=
  ⟨euThreeSATToC4FreeVertexCover, computableInPolyTime_euThreeSATToC4FreeVertexCover,
    fun φ ↦ (euThreeSATToC4FreeVertexCover_mem_iff φ).symm⟩

/-- `C4FreeVertexCover` is `NP`-hard. -/
theorem c4FreeVertexCover_npHard : NPHard encVertexCoverInstance C4FreeVertexCover :=
  EUThreeSAT_npHard.trans polyTimeReducible_euThreeSAT_c4FreeVertexCover

/-- **`C₄`-Free Vertex Cover is `NP`-complete**. -/
theorem c4FreeVertexCover_npComplete : NPComplete encVertexCoverInstance C4FreeVertexCover :=
  ⟨c4FreeVertexCover_mem_NP, c4FreeVertexCover_npHard⟩

-- Non-vacuity check: `K_3` with budget `2` belongs to `C4FreeVertexCover` (and is not covered by
-- `1` vertex), while the `4`-cycle `C_4` fails `IsC4FreeGraph`.
example : (∃ x : VertexCoverInstance, x ∈ C4FreeVertexCover ∧ 3 ≤ x.graph.vertices.toFinset.card) ∧
    (∃ G : Graph, ¬IsC4FreeGraph G) := by
  refine ⟨⟨VertexCoverInstance.mk (Graph.mk [0, 1, 2] [(0, 1), (1, 2), (0, 2)]) 2, ⟨?_, ?_⟩,
      by decide⟩,
    ⟨Graph.mk [0, 1, 2, 3] [(0, 1), (1, 2), (2, 3), (3, 0)], ?_⟩⟩
  · rw [← isC4FreeGraphBool_eq_true_iff]; decide
  · rw [mem_VertexCover_iff_mk]
    refine ⟨{0, 1}, by decide, ?_, by decide⟩
    intro u hu v hv hadj
    have hne := hadj.ne
    have hedge := (Graph.toSimpleGraph_adj.mp hadj).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv hedge
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> simp at hne hedge ⊢
  · rw [← isC4FreeGraphBool_eq_true_iff]; decide

end Cslib.Complexity
end
