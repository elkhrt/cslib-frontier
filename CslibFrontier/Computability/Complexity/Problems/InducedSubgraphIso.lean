module

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.GraphIsomorphism
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Induced Subgraph Isomorphism and Unconditional $\mathrm{NP}$-Completeness

Formalizes the canonical Induced Subgraph Isomorphism decision problem
 on `Cslib.Complexity.Graph` pairs (`InducedSubgraphIsoInstance`, `InducedSubgraphIso`,
encoded by `encInducedSubgraphIso`), proves membership in `NP` via polynomial-time ordering
verification (`Graph.verifyOrdering`), constructs a polynomial-time many-one reduction from
`Cslib.Complexity.IndependentSet` mapping `(G, m)` to the edgeless `m`-vertex graph and `G`, and
establishes unconditional $\mathrm{NP}$-completeness under standard Lean axioms.

## Main definitions

- `Cslib.Complexity.InducedSubgraphIsoInstance`: pair `(pattern, host)` of
  finite graphs.
- `Cslib.Complexity.encInducedSubgraphIso`: framed binary encoding of
  `InducedSubgraphIsoInstance`.
- `Cslib.Complexity.InducedSubgraphIso`: decision language of pairs `(H, G)`
  admitting an induced subgraph embedding `H.induced ↪g G.induced`.
- `Cslib.Complexity.inducedSubgraphIsoVerifier`: polynomial-time verifier.
- `Cslib.Complexity.independentSetToInducedSubgraphIso`: Karp reduction from
  `Cslib.Complexity.IndependentSet`.

## Main results

- `Cslib.Complexity.mem_inducedSubgraphIso_iff`: position-based vertex
  embedding characterization.
- `Cslib.Complexity.inducedSubgraphIso_mem_NP`:
  `InducedSubgraphIso ∈ NP encInducedSubgraphIso`.
- `Cslib.Complexity.independentSetToInducedSubgraphIso_mem_iff`:
  `independentSetToInducedSubgraphIso x ∈ InducedSubgraphIso ↔ x ∈ IndependentSet`.
- `Cslib.Complexity.polyTimeReducible_IndependentSet_InducedSubgraphIso`:
  polynomial-time many-one reduction from `IndependentSet` to `InducedSubgraphIso`.
- `Cslib.Complexity.inducedSubgraphIso_npHard`,
  `Cslib.Complexity.inducedSubgraphIso_npComplete`: unconditional
  $\mathrm{NP}$-hardness and $\mathrm{NP}$-completeness.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- An instance `(pattern, host)` of the **Induced Subgraph Isomorphism** problem. -/
@[ext]
structure InducedSubgraphIsoInstance where
  /-- The pattern graph to embed as an induced subgraph. -/
  pattern : Graph
  /-- The host graph into which `pattern` is embedded. -/
  host : Graph
  deriving DecidableEq, Repr, Inhabited

/-- Framed encoding of `InducedSubgraphIsoInstance` as a pair `(pattern, host)`. -/
enc_structure encInducedSubgraphIso : InducedSubgraphIsoInstance where
  pattern : encGraph,
  host : encGraph

attribute [fun_prop] encInducedSubgraphIso_pattern_polyTime
  encInducedSubgraphIso_host_polyTime encInducedSubgraphIso_mk_polyTime

/-- The pairs `(H, G)` such that `H.induced` embeds into `G.induced` as an induced subgraph, i.e.,
admits a Mathlib `SimpleGraph.Embedding` (`↪g`). -/
@[expose]
def InducedSubgraphIso : Set InducedSubgraphIsoInstance :=
  {x | Nonempty (x.pattern.induced ↪g x.host.induced)}

/-- Position-based characterization of `InducedSubgraphIso`: `(H, G)` is a yes-instance iff there
exists an injective map `f` from positions in `H.distinctVertices` to positions in
`G.distinctVertices` preserving and reflecting `Graph.adjIndex`. -/
theorem mem_inducedSubgraphIso_iff {x : InducedSubgraphIsoInstance} :
    x ∈ InducedSubgraphIso ↔
      ∃ f : Fin x.pattern.distinctVertices.length → Fin x.host.distinctVertices.length,
        Function.Injective f ∧
          ∀ i j, x.host.adjIndex (f i) (f j) = x.pattern.adjIndex i j := by
  constructor
  · rintro ⟨φ⟩
    let f := fun i ↦ x.host.vertexEquiv.symm (φ (x.pattern.vertexEquiv i))
    refine ⟨f,
      x.host.vertexEquiv.symm.injective.comp (φ.injective.comp x.pattern.vertexEquiv.injective),
      fun i j ↦ ?_⟩
    rw [Bool.eq_iff_iff, ← Graph.induced_adj_vertexEquiv, ← Graph.induced_adj_vertexEquiv]
    simp only [f, Equiv.apply_symm_apply]
    exact φ.map_adj_iff
  · rintro ⟨f, hinj, hadj⟩
    let emb : {v // v ∈ x.pattern.vertices} ↪ {v // v ∈ x.host.vertices} :=
      ⟨fun u ↦ x.host.vertexEquiv (f (x.pattern.vertexEquiv.symm u)),
        x.host.vertexEquiv.injective.comp (hinj.comp x.pattern.vertexEquiv.symm.injective)⟩
    refine ⟨⟨emb, fun {u v} ↦ ?_⟩⟩
    obtain ⟨i, rfl⟩ := x.pattern.vertexEquiv.surjective u
    obtain ⟨j, rfl⟩ := x.pattern.vertexEquiv.surjective v
    simp only [emb, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]
    rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj_vertexEquiv, hadj]

/-- Every yes-instance `(H, G)` satisfies `|V(H)| ≤ |V(G)|`. -/
theorem pattern_le_host_of_mem_inducedSubgraphIso {x : InducedSubgraphIsoInstance}
    (hx : x ∈ InducedSubgraphIso) :
    x.pattern.distinctVertices.length ≤ x.host.distinctVertices.length := by
  obtain ⟨f, hinj, -⟩ := mem_inducedSubgraphIso_iff.1 hx
  simpa using Fintype.card_le_of_injective f hinj

/-- Polynomial-time verifier for `InducedSubgraphIso`: decodes an enumeration `p` of all declared
vertices of `x.host`, checks `x.pattern.distinctVertices.length ≤ p.length`, and checks that the
first `x.pattern.distinctVertices.length` entries preserve and reflect adjacency. -/
@[expose]
def inducedSubgraphIsoVerifier : InducedSubgraphIsoInstance × List Bool → Bool :=
  Graph.verifyOrdering (fun x ↦ x.host.vertices) fun x p ↦
    decide (x.pattern.distinctVertices.length ≤ p.length) &&
      (List.range x.pattern.distinctVertices.length).all fun i ↦
        (List.range x.pattern.distinctVertices.length).all fun j ↦
          x.host.adjBool (p.getD i 0) (p.getD j 0) == x.pattern.adjIndex i j

/-- `inducedSubgraphIsoVerifier` is computable in polynomial time. -/
theorem computableInPolyTime_inducedSubgraphIsoVerifier :
    ComputableInPolyTime inducedSubgraphIsoVerifier
      (encPair encInducedSubgraphIso encBits) encBool := by
  have hlen : ComputableInPolyTime
      (fun x : InducedSubgraphIsoInstance × List ℕ ↦ x.1.pattern.distinctVertices.length)
      (encPair encInducedSubgraphIso (encList encNat)) encUnary :=
    (length_list encNat).comp (by fun_prop)
  refine Graph.computableInPolyTime_verifyOrdering (by fun_prop) ?_
  have hle : ComputableInPolyTime
      (fun x : InducedSubgraphIsoInstance × List ℕ ↦
        decide (x.1.pattern.distinctVertices.length ≤ x.2.length))
      (encPair encInducedSubgraphIso (encList encNat)) encBool := by fun_prop
  have hall : ComputableInPolyTime
      (fun x : InducedSubgraphIsoInstance × List ℕ ↦
        (List.range x.1.pattern.distinctVertices.length).all fun i ↦
          (List.range x.1.pattern.distinctVertices.length).all fun j ↦
            x.1.host.adjBool (x.2.getD i 0) (x.2.getD j 0) == x.1.pattern.adjIndex i j)
      (encPair encInducedSubgraphIso (encList encNat)) encBool := by
    refine allWithInput (range.comp hlen)
      (allWithInput (range.comp (hlen.comp (fst _ _))) ?_)
    exact beq
      (Graph.computableInPolyTime_adjBool_comp (by fun_prop) (by fun_prop) (by fun_prop))
      (Graph.computableInPolyTime_adjIndex (by fun_prop) (by fun_prop) (by fun_prop))
  exact bool_and.comp (hle.prod hall)

/-- `inducedSubgraphIsoVerifier` is a valid `NP` verifier for `InducedSubgraphIso` with
quadratic certificate length. -/
theorem isVerifier_inducedSubgraphIso :
    IsVerifier encInducedSubgraphIso (Polynomial.X ^ 2)
      inducedSubgraphIsoVerifier InducedSubgraphIso := by
  have hset : InducedSubgraphIso =
      {x : InducedSubgraphIsoInstance |
        ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ x.host.vertices) ∧
          x.pattern.distinctVertices.length ≤ p.length ∧
          ∀ i < x.pattern.distinctVertices.length, ∀ j < x.pattern.distinctVertices.length,
            x.host.adjBool (p.getD i 0) (p.getD j 0) = x.pattern.adjIndex i j} := by
    ext ⟨H, G⟩
    rw [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨φ⟩
      let m := H.distinctVertices.length
      let f : Fin m → ℕ := fun i ↦ (φ (H.vertexEquiv i)).1
      have hf : Function.Injective f :=
        Subtype.val_injective.comp (φ.injective.comp H.vertexEquiv.injective)
      let pref : List ℕ := List.ofFn f
      let rest : List ℕ := G.distinctVertices.filter fun v ↦ decide (v ∉ pref)
      let p : List ℕ := pref ++ rest
      have hnd_pref : pref.Nodup := List.nodup_ofFn.2 hf
      have hnd_rest : rest.Nodup := (Graph.nodup_distinctVertices G).filter _
      have hdisj : List.Disjoint pref rest := fun v hvp hvr ↦ by
        simp only [rest, List.mem_filter, decide_eq_true_eq] at hvr
        exact hvr.2 hvp
      have hnd : p.Nodup :=
        List.nodup_append.2 ⟨hnd_pref, hnd_rest, fun a ha b hb heq ↦ hdisj ha (heq ▸ hb)⟩
      have hcov : ∀ v, v ∈ p ↔ v ∈ G.vertices := fun v ↦ by
        simp only [p, List.mem_append, rest, List.mem_filter, decide_eq_true_eq,
          Graph.mem_distinctVertices]
        constructor
        · rintro (hvp | ⟨hvG, _⟩)
          · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hvp
            exact (φ (H.vertexEquiv i)).2
          · exact hvG
        · intro hvG
          by_cases hvp : v ∈ pref
          · exact Or.inl hvp
          · exact Or.inr ⟨hvG, hvp⟩
      refine ⟨p, hnd, hcov, by simp [p, pref, m], fun i hi j hj ↦ ?_⟩
      have hip : i < pref.length := by simpa [pref] using hi
      have hjp : j < pref.length := by simpa [pref] using hj
      have hpi : p.getD i 0 = f ⟨i, hi⟩ := by
        rw [List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le hip (by simp [p])),
          List.getElem_append_left hip]
        exact List.getElem_ofFn _
      have hpj : p.getD j 0 = f ⟨j, hj⟩ := by
        rw [List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le hjp (by simp [p])),
          List.getElem_append_left hjp]
        exact List.getElem_ofFn _
      rw [hpi, hpj, Bool.eq_iff_iff, G.adjBool_eq_true_iff,
        ← Graph.induced_adj_vertexEquiv H ⟨i, hi⟩ ⟨j, hj⟩]
      exact φ.map_adj_iff
    · rintro ⟨p, hnd, hcov, hlen, hadj⟩
      let f : Fin H.distinctVertices.length → {v // v ∈ G.vertices} :=
        fun i ↦ ⟨p[i.1]'(Nat.lt_of_lt_of_le i.2 hlen), (hcov _).1 (List.getElem_mem _)⟩
      have hf : Function.Injective f := fun i j heq ↦
        Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 (congrArg Subtype.val heq))
      refine ⟨⟨⟨fun u ↦ f (H.vertexEquiv.symm u), hf.comp H.vertexEquiv.symm.injective⟩,
        fun {u v} ↦ ?_⟩⟩
      obtain ⟨i, rfl⟩ := H.vertexEquiv.surjective u
      obtain ⟨j, rfl⟩ := H.vertexEquiv.surjective v
      simp only [Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]
      rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj, ← G.adjBool_eq_true_iff,
        ← hadj i.1 i.2 j.1 j.2,
        List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le i.2 hlen),
        List.getD_eq_getElem _ _ (Nat.lt_of_lt_of_le j.2 hlen)]
  rw [hset]
  refine Graph.isVerifier_verifyOrdering (fun x ↦ x.host.length_vertices_le_encGraph.trans
      (by simp only [encInducedSubgraphIso_apply, length_encPair]; omega))
    fun x p ↦ ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]

/-- `InducedSubgraphIso` belongs to `NP encInducedSubgraphIso`. -/
theorem inducedSubgraphIso_mem_NP : InducedSubgraphIso ∈ NP encInducedSubgraphIso :=
  ⟨Polynomial.X ^ 2, inducedSubgraphIsoVerifier,
    computableInPolyTime_inducedSubgraphIsoVerifier, isVerifier_inducedSubgraphIso⟩

/-- Polynomial-time Karp reduction from `IndependentSet` to `InducedSubgraphIso`:
maps `(G, m)` to the edgeless `m`-vertex pattern `⟨List.range m, []⟩` and host `G` when
`m ≤ G.distinctVertices.length`, and to the fixed negative instance
`(⟨[0, 1], [(0, 1)]⟩, ⟨[0, 1], []⟩)` (`K₂` into `E₂`) otherwise. -/
@[expose]
def independentSetToInducedSubgraphIso (x : IndependentSetInstance) :
    InducedSubgraphIsoInstance :=
  if x.m ≤ x.graph.distinctVertices.length then
    ⟨⟨(List.range x.m).map id, []⟩, x.graph⟩
  else
    ⟨⟨[0, 1], [(0, 1)]⟩, ⟨[0, 1], []⟩⟩

private theorem noGadget_not_mem_inducedSubgraphIso :
    (⟨⟨[0, 1], [(0, 1)]⟩, ⟨[0, 1], []⟩⟩ : InducedSubgraphIsoInstance) ∉ InducedSubgraphIso := by
  rintro ⟨φ⟩
  have h01 : (⟨[0, 1], [(0, 1)]⟩ : Graph).induced.Adj
      ⟨0, by simp⟩ ⟨1, by simp⟩ :=
    Graph.toSimpleGraph_adj.2 ⟨by decide, Or.inl (by simp)⟩
  have h := φ.map_adj_iff.2 h01
  have hfalse := (Graph.toSimpleGraph_adj.1 h).2
  simp at hfalse

/-- Exact membership equivalence for `independentSetToInducedSubgraphIso`. -/
theorem independentSetToInducedSubgraphIso_mem_iff (x : IndependentSetInstance) :
    independentSetToInducedSubgraphIso x ∈ InducedSubgraphIso ↔ x ∈ IndependentSet := by
  dsimp only [independentSetToInducedSubgraphIso]
  split_ifs with hm
  · rw [mem_IndependentSet_iff]
    constructor
    · rintro ⟨φ⟩
      let S : Finset ℕ := Finset.univ.image fun u : {v // v ∈ (⟨(List.range x.m).map id, []⟩ :
          Graph).vertices} ↦ (φ u).1
      have hS_sub : ∀ v ∈ S, v ∈ x.graph.vertices := fun v hv ↦ by
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hv
        exact (φ u).2
      have hS_indep : x.graph.toSimpleGraph.IsIndepSet (S : Set ℕ) := by
        intro a ha b hb _ hadj
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
        have huv : (⟨(List.range x.m).map id, []⟩ : Graph).induced.Adj u v :=
          φ.map_adj_iff.1 hadj
        have hnil := (Graph.toSimpleGraph_adj.1 huv).2
        simp at hnil
      have hS_card : S.card = x.m := by
        rw [Finset.card_image_of_injective _ (fun _ _ h ↦ φ.injective (Subtype.ext h)),
          Finset.card_univ, Graph.card_vertexSubtype]
        simp [List.toFinset_range]
      exact ⟨S, hS_sub, hS_indep, hS_card⟩
    · rintro ⟨S, hS_sub, hS_indep, hS_card⟩
      let H : Graph := ⟨(List.range x.m).map id, []⟩
      have hcardH : Fintype.card {v // v ∈ H.vertices} = x.m := by
        rw [Graph.card_vertexSubtype]
        simp [H, List.toFinset_range]
      have hcardS : Fintype.card S = x.m := by
        simpa [Fintype.card_coe] using hS_card
      let e : {v // v ∈ H.vertices} ≃ S :=
        (Fintype.equivFinOfCardEq hcardH).trans (Fintype.equivFinOfCardEq hcardS).symm
      let emb : {v // v ∈ H.vertices} ↪ {v // v ∈ x.graph.vertices} :=
        ⟨fun u ↦ ⟨(e u).1, hS_sub _ (e u).2⟩, fun u v heq ↦
          e.injective (Subtype.ext (Subtype.mk.inj heq))⟩
      refine ⟨⟨emb, fun {u v} ↦ ?_⟩⟩
      have hH_false : ¬ H.induced.Adj u v := fun h ↦ by
        have := (Graph.toSimpleGraph_adj.1 h).2; simp [H] at this
      have hG_false : ¬ x.graph.induced.Adj (emb u) (emb v) := fun h ↦ by
        have hne : (e u).1 ≠ (e v).1 := x.graph.toSimpleGraph.ne_of_adj h
        exact hS_indep (e u).2 (e v).2 hne h
      exact iff_of_false hG_false hH_false
  · constructor
    · intro h; exact (noGadget_not_mem_inducedSubgraphIso h).elim
    · intro h
      have hle := Graph.le_card_of_mem_IndependentSet h
      rw [← Graph.length_distinctVertices] at hle
      exact absurd hle hm

/-- `independentSetToInducedSubgraphIso` is computable in polynomial time. -/
theorem computableInPolyTime_independentSetToInducedSubgraphIso :
    ComputableInPolyTime independentSetToInducedSubgraphIso
      encIndependentSetInstance encInducedSubgraphIso := by
  have hG : ComputableInPolyTime (fun x : IndependentSetInstance ↦ x.graph)
      encIndependentSetInstance encGraph := by fun_prop
  have hm : ComputableInPolyTime (fun x : IndependentSetInstance ↦ x.m)
      encIndependentSetInstance encNat := by fun_prop
  have hVlen_u : ComputableInPolyTime
      (fun x : IndependentSetInstance ↦ x.graph.distinctVertices.length)
      encIndependentSetInstance encUnary :=
    (length_list encNat).comp (by fun_prop)
  have hVlen : ComputableInPolyTime
      (fun x : IndependentSetInstance ↦ x.graph.distinctVertices.length)
      encIndependentSetInstance encNat :=
    unary_to_binary.comp hVlen_u
  have hcond : ComputableInPolyTime
      (fun x : IndependentSetInstance ↦ decide (x.m ≤ x.graph.distinctVertices.length))
      encIndependentSetInstance encBool :=
    binary_le' hm hVlen
  have hmin_u : ComputableInPolyTime
      (fun x : IndependentSetInstance ↦ min x.graph.distinctVertices.length x.m)
      encIndependentSetInstance encUnary :=
    binary_min_unary' hVlen_u hm
  have hverts : ComputableInPolyTime
      (fun x : IndependentSetInstance ↦
        (List.range (min x.graph.distinctVertices.length x.m)).map id)
      encIndependentSetInstance (encList encNat) :=
    mapWithInput (range.comp hmin_u) (unary_to_binary.comp (snd _ _))
  have hthen_aux : ComputableInPolyTime
      (fun x : IndependentSetInstance ↦
        (⟨⟨(List.range (min x.graph.distinctVertices.length x.m)).map id, []⟩, x.graph⟩ :
          InducedSubgraphIsoInstance))
      encIndependentSetInstance encInducedSubgraphIso := by
    have hpat : ComputableInPolyTime
        (fun x : IndependentSetInstance ↦
          (⟨(List.range (min x.graph.distinctVertices.length x.m)).map id, []⟩ : Graph))
        encIndependentSetInstance encGraph :=
      encGraph_mk_polyTime hverts (const [])
    exact encInducedSubgraphIso_mk_polyTime hpat hG
  have helse : ComputableInPolyTime
      (fun _ : IndependentSetInstance ↦
        (⟨⟨[0, 1], [(0, 1)]⟩, ⟨[0, 1], []⟩⟩ : InducedSubgraphIsoInstance))
      encIndependentSetInstance encInducedSubgraphIso :=
    const _
  exact (ite' hcond hthen_aux helse).of_enc_eq fun x ↦ congrArg encInducedSubgraphIso <| by
    by_cases h : x.m ≤ x.graph.distinctVertices.length <;>
      simp [independentSetToInducedSubgraphIso, h]

/-- Polynomial-time many-one reduction from `IndependentSet` to `InducedSubgraphIso`. -/
theorem polyTimeReducible_IndependentSet_InducedSubgraphIso :
    PolyTimeReducible encIndependentSetInstance encInducedSubgraphIso
      IndependentSet InducedSubgraphIso :=
  ⟨independentSetToInducedSubgraphIso, computableInPolyTime_independentSetToInducedSubgraphIso,
    fun x ↦ (independentSetToInducedSubgraphIso_mem_iff x).symm⟩

/-- `InducedSubgraphIso` is unconditionally $\mathrm{NP}$-hard. -/
theorem inducedSubgraphIso_npHard : NPHard encInducedSubgraphIso InducedSubgraphIso :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_InducedSubgraphIso

/-- **Garey–Johnson / Sysło**: `InducedSubgraphIso` is unconditionally
$\mathrm{NP}$-complete.
-/
theorem inducedSubgraphIso_npComplete : NPComplete encInducedSubgraphIso InducedSubgraphIso :=
  ⟨inducedSubgraphIso_mem_NP, inducedSubgraphIso_npHard⟩

private example : (⟨⟨[0, 1], [(0, 1)]⟩, ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩⟩ :
    InducedSubgraphIsoInstance) ∈ InducedSubgraphIso := by
  refine mem_inducedSubgraphIso_iff.2 ⟨fun i ↦ ⟨i.1, by
    have hi := i.2
    simp only [Graph.length_distinctVertices] at hi ⊢
    have h1 : ([0, 1] : List ℕ).toFinset.card = 2 := by decide
    have h2 : ([0, 1, 2] : List ℕ).toFinset.card = 3 := by decide
    omega⟩, fun i j heq ↦ Fin.ext (Fin.mk.inj heq), fun i j ↦ ?_⟩
  have h1 : (⟨[0, 1], [(0, 1)]⟩ : Graph).distinctVertices = [0, 1] := by decide
  have h2 : (⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩ : Graph).distinctVertices = [0, 1, 2] := by
    decide
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  have hi2 : i < 2 := by simpa [h1] using hi
  have hj2 : j < 2 := by simpa [h1] using hj
  interval_cases i <;> interval_cases j <;> simp [Graph.adjIndex, Graph.adjBool, h1, h2]

private example : (⟨⟨[0, 1, 2], []⟩, ⟨[0, 1], []⟩⟩ : InducedSubgraphIsoInstance) ∉
    InducedSubgraphIso := by
  intro h
  have hle := pattern_le_host_of_mem_inducedSubgraphIso h
  have h1 : (⟨[0, 1, 2], []⟩ : Graph).distinctVertices.length = 3 := by decide
  have h2 : (⟨[0, 1], []⟩ : Graph).distinctVertices.length = 2 := by decide
  dsimp only at hle; rw [h1, h2] at hle; omega

end Cslib.Complexity
