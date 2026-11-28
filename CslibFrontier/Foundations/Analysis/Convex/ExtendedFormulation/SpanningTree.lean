module

public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Matrix.ColumnRowPartitioned

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spanning Tree Polytope and Edmonds' Characterization

Formalizes Edmonds' spanning tree polytope theorem for finite connected simple graphs along with
forest component-edge and rooted-tree slack identities:

- `card_edgeFinset_add_card_connectedComponent_eq_card`: `|E(H)| + c(H) = |V|` for any finite
  acyclic simple graph `H`.
- `spanningTree_slack_eq_components_sub_one` & `card_leaving_parentEdges_eq_slack`: the subtour
  elimination slack `(|U| - 1) - |E[U] ∩ E(T)|` equals `c(T[U]) - 1` and equals the number of
  rooted-tree parent edges leaving `U`.
- `spanningTreePolytope_eq_hPolytope`: Edmonds' spanning tree polytope theorem, proved via
  Kruskal's greedy algorithm, Abel summation, and geometric Hahn–Banach separation.
- `spanningTreePolytope_eq_setOf_mulVec_le`: matrix H-description `{x | A *ᵥ x ≤ b}` split into
  non-negativity rows and non-trivial subtour-elimination / total-size rows.
-/

public section

namespace CslibFrontier.ExtendedFormulation

open Matrix SimpleGraph

/-! ### Forest component-edge formula and rooted-tree orientation -/

section ForestFormula

variable {V : Type*}

/-- For any finite acyclic simple graph `H`, the number of edges plus the number of connected
components equals the number of vertices: `|E(H)| + c(H) = |V|`. -/
theorem card_edgeFinset_add_card_connectedComponent_eq_card [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : H.IsAcyclic) :
    H.edgeFinset.card + Fintype.card H.ConnectedComponent = Fintype.card V := by
  classical
  have hcomp : ∀ c : H.ConnectedComponent,
      c.toSimpleGraph.edgeFinset.card + 1 = Fintype.card c.supp := fun c =>
    (hH.isTree_connectedComponent c).card_edgeFinset
  have hsum : ∑ c : H.ConnectedComponent, (c.toSimpleGraph.edgeFinset.card + 1) =
      ∑ c : H.ConnectedComponent, Fintype.card c.supp :=
    Finset.sum_congr rfl fun c _ => hcomp c
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hverts : ∑ c : H.ConnectedComponent, Fintype.card c.supp = Fintype.card V := by
    let e : (c : H.ConnectedComponent) × c.supp ≃ V :=
      { toFun := fun p => p.2.1
        invFun := fun v => ⟨H.connectedComponentMk v, v, rfl⟩
        left_inv := fun ⟨c, ⟨v, hv⟩⟩ => by
          subst hv
          rfl
        right_inv := fun _ => rfl }
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr e
  have hedges : ∑ c : H.ConnectedComponent, c.toSimpleGraph.edgeFinset.card =
      H.edgeFinset.card := by
    let e : (c : H.ConnectedComponent) × c.toSimpleGraph.edgeFinset ≃ H.edgeFinset :=
      { toFun := fun ⟨c, ⟨f, hf⟩⟩ => ⟨Sym2.map Subtype.val f, by
          have hmem : f ∈ c.toSimpleGraph.edgeSet := (SimpleGraph.mem_edgeFinset).1 hf
          rw [SimpleGraph.mem_edgeFinset]
          rcases f with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
          exact hmem⟩
        invFun := fun f =>
          let u := f.1.out.1
          let v := f.1.out.2
          have hf : s(u, v) = f.1 := Quot.out_eq f.1
          have hadj : H.Adj u v := by
            have hmem : f.1 ∈ H.edgeSet := (SimpleGraph.mem_edgeFinset).1 f.2
            rwa [← hf] at hmem
          let c := H.connectedComponentMk u
          have hu : u ∈ c.supp := rfl
          have hv : v ∈ c.supp := (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm
          ⟨c, ⟨s(⟨u, hu⟩, ⟨v, hv⟩), by
            rw [SimpleGraph.mem_edgeFinset]
            exact hadj⟩⟩
        left_inv := fun ⟨c, ⟨f, hf⟩⟩ => by
          rcases f with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
          have hpair : (s(u, v).out.1 = u ∧ s(u, v).out.2 = v) ∨
              (s(u, v).out.1 = v ∧ s(u, v).out.2 = u) :=
            Sym2.eq_iff.1 (Quot.out_eq s(u, v))
          have hc : H.connectedComponentMk s(u, v).out.1 = c := by
            rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩
            · rw [h1]; exact hu
            · rw [h1]; exact hv
          cases hc
          refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
          apply Sym2.map.injective Subtype.val_injective
          exact Quot.out_eq s(u, v)
        right_inv := fun ⟨f, hf⟩ => by
          apply Subtype.ext
          exact Quot.out_eq f }
    have hcard := Fintype.card_congr e
    rw [Fintype.card_sigma] at hcard
    simp only [Fintype.card_coe] at hcard
    convert hcard
  rw [hedges, hverts] at hsum
  exact hsum

/-- Given a tree `T` and a root `r : V`, the parent of any vertex `v ≠ r` is the second vertex on
the unique path from `v` to `r` (and `r` maps to itself). -/
noncomputable def treeParent (T : SimpleGraph V) (hT : T.IsTree) (r : V) (v : V) : V := by
  classical
  exact if h : v = r then r
  else ((hT.existsUnique_path v r).choose.firstDart (SimpleGraph.Walk.not_nil_of_ne h)).snd

theorem treeParent_adj {T : SimpleGraph V} (hT : T.IsTree) (r v : V) (hv : v ≠ r) :
    T.Adj v (treeParent T hT r v) := by
  classical
  simp only [treeParent, hv, ↓reduceDIte]
  exact ((hT.existsUnique_path v r).choose.firstDart (SimpleGraph.Walk.not_nil_of_ne hv)).adj

/-- The parent-edge map `v ↦ s(v, treeParent T hT r v)` is a bijection from `{v : V // v ≠ r}` to
`T.edgeFinset` (from Mathlib's proof of `IsTree.card_edgeFinset`). -/
theorem treeParent_edge_bijective [Fintype V]
    {T : SimpleGraph V} [DecidableRel T.Adj] (hT : T.IsTree) (r : V) :
    Function.Bijective (fun v : {v : V // v ≠ r} =>
      (⟨s(v.1, treeParent T hT r v.1),
        SimpleGraph.mem_edgeFinset.2 (treeParent_adj hT r v.1 v.2)⟩ : T.edgeFinset)) := by
  classical
  have hcard : Fintype.card {v : V // v ≠ r} = Fintype.card T.edgeFinset := by
    have h1 : Fintype.card {v : V // v ≠ r} + 1 = Fintype.card V := by
      have hc : Fintype.card {v : V // v ≠ r} = Fintype.card V - Fintype.card {v : V // v = r} :=
        Fintype.card_subtype_compl (fun v => v = r)
      have huniq : Fintype.card {v : V // v = r} = 1 := Fintype.card_unique
      rw [hc, huniq]
      exact Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨r⟩)
    have h2 : Fintype.card T.edgeFinset + 1 = Fintype.card V := by
      rw [Fintype.card_coe]
      convert hT.card_edgeFinset
    omega
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  have hedge : s(a, treeParent T hT r a) = s(b, treeParent T hT r b) := congrArg Subtype.val h
  apply Subtype.ext
  let f : ∀ w : V, T.Walk w r := fun w => (hT.existsUnique_path w r).choose
  have hf : ∀ w, (f w).IsPath := fun w => (hT.existsUnique_path w r).choose_spec.1
  have hf' : ∀ w (p : T.Walk w r), p.IsPath → p = f w :=
    fun w p hp => (hT.existsUnique_path w r).choose_spec.2 p hp
  have hpar : ∀ (w : V) (hw : w ≠ r), treeParent T hT r w = (f w).snd := by
    intro w hw
    simp [treeParent, hw, f]
  have haux : ∀ (x y : V) (hx : x ≠ r) (hy : y ≠ r),
      s(x, (f x).snd) = s(y, (f y).snd) → (f x).length ≤ (f y).length → x = y := by
    intro x y hx hy heq hlen
    rcases Sym2.eq_iff.1 heq with ⟨rfl, _⟩ | ⟨_, hyx⟩
    · rfl
    · have htail : (f x).tail.IsPath := (hf x).tail
      have hcopy : ((f x).tail.copy hyx rfl).IsPath := by simpa using htail
      have heq_path := hf' y ((f x).tail.copy hyx rfl) hcopy
      have hlen_eq := congrArg SimpleGraph.Walk.length heq_path
      rw [SimpleGraph.Walk.length_copy] at hlen_eq
      have h1 := (f x).length_tail_add_one (SimpleGraph.Walk.not_nil_of_ne hx)
      omega
  rw [hpar a ha, hpar b hb] at hedge
  rcases le_total (f a).length (f b).length with hlen | hlen
  · exact haux a b ha hb hedge hlen
  · exact (haux b a hb ha hedge.symm hlen).symm

end ForestFormula

/-! ### Spanning tree polytope definitions and slack identities -/

section SpanningTreeDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced edge set `E[U]` of a vertex subset `U ⊆ V` inside `G.edgeFinset`. -/
@[expose] def inducedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    Finset G.edgeFinset :=
  Finset.univ.filter fun e => ∀ v ∈ e.1, v ∈ U

/-- Membership characterization for `inducedEdges G U`. -/
theorem mem_inducedEdges_iff (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (e : G.edgeFinset) :
    e ∈ inducedEdges G U ↔ ∀ v ∈ e.1, v ∈ U := by
  simp [inducedEdges]

/-- The incidence vector `χ^{E(T)} ∈ ℝ^{E(G)}` of a subgraph `T` of `G`. -/
@[expose] noncomputable def spanningTreeVec (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) : G.edgeFinset → ℝ := by
  classical
  exact fun e => if e.1 ∈ T.edgeSet then 1 else 0

omit [DecidableEq V] in
/-- Entries of `spanningTreeVec G T` are nonnegative. -/
theorem spanningTreeVec_nonneg (G T : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeFinset) :
    0 ≤ spanningTreeVec G T e := by
  classical
  simp only [spanningTreeVec]
  split_ifs <;> norm_num

omit [DecidableEq V] in
/-- Sum of `spanningTreeVec G T` over a finset `s` equals the number of edges of `T` in `s`. -/
theorem sum_spanningTreeVec_eq_card_filter (G T : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset G.edgeFinset) [DecidablePred fun e : G.edgeFinset => e.1 ∈ T.edgeSet] :
    ∑ e ∈ s, spanningTreeVec G T e = ((s.filter fun e => e.1 ∈ T.edgeSet).card : ℝ) := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [spanningTreeVec, Nat.cast_one]
  split_ifs <;> rfl

/-- The spanning tree polytope `SPAN(G)`: the convex hull of the incidence vectors of all
spanning trees of `G`. -/
@[expose] noncomputable def spanningTreePolytope (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set (G.edgeFinset → ℝ) :=
  convexHull ℝ (Set.range fun T : {T : SimpleGraph V // T ≤ G ∧ T.IsTree} =>
    spanningTreeVec G T.1)

/-- Edmonds' linear inequality description of the spanning tree polytope:
`x(E[U]) ≤ |U| - 1` for nonempty `U ⊆ V`, `x(E) = |V| - 1`, and
`x_e ≥ 0` for `e ∈ E`. -/
@[expose] def spanningTreeHPolytope (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set (G.edgeFinset → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
    (∑ e : G.edgeFinset, x e = (Fintype.card V : ℝ) - 1) ∧
    (∀ U : Finset V, U.Nonempty → ∑ e ∈ inducedEdges G U, x e ≤ (U.card : ℝ) - 1)}

/-- For a spanning tree `T ≤ G` and any subset `U`, the sum of `χ^{E(T)}` over `E[U]` equals the
number of edges of the induced subgraph `T[U]`. -/
theorem sum_inducedEdges_spanningTreeVec {G T : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel T.Adj] (hTG : T ≤ G) (U : Finset V) :
    ∑ e ∈ inducedEdges G U, spanningTreeVec G T e =
      ((T.induce (U : Set V)).edgeFinset.card : ℝ) := by
  classical
  rw [show (∑ e ∈ inducedEdges G U, spanningTreeVec G T e) =
      (((inducedEdges G U).filter fun e => e.1 ∈ T.edgeSet).card : ℝ) by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [spanningTreeVec, Nat.cast_one]
    split_ifs <;> rfl]
  norm_cast
  symm
  refine Finset.card_bij
    (fun e he => (⟨Sym2.map Subtype.val e, by
      have hmem := SimpleGraph.mem_edgeFinset.1 he
      rcases e with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
      exact SimpleGraph.mem_edgeFinset.2 (hTG hmem)⟩ : G.edgeFinset))
    (fun e he => ?_) (fun e₁ _ e₂ _ h => ?_) (fun f hf => ?_)
  · have hmem := SimpleGraph.mem_edgeFinset.1 he
    rcases e with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hmem⟩
    intro w hw
    change w ∈ s(u, v) at hw
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption
  · exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h)
  · simp only [Finset.mem_filter, inducedEdges, Finset.mem_univ, true_and] at hf
    rcases f with ⟨f, hfG⟩
    rcases f with ⟨u, v⟩
    have hu : u ∈ U := hf.1 u (Sym2.mem_mk_left u v)
    have hv : v ∈ U := hf.1 v (Sym2.mem_mk_right u v)
    refine ⟨s(⟨u, hu⟩, ⟨v, hv⟩), SimpleGraph.mem_edgeFinset.2 hf.2, ?_⟩
    apply Subtype.ext
    rfl

/-- Subtour-elimination slack identity: for any spanning tree `T ≤ G` and subset `U ⊆ V`,
the slack `(|U| - 1) - x(E[U])` equals the number of connected
components of `T[U]` minus one. -/
theorem spanningTree_slack_eq_components_sub_one {G T : SimpleGraph V} [DecidableRel G.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) (U : Finset V) :
    ((U.card : ℝ) - 1) - ∑ e ∈ inducedEdges G U, spanningTreeVec G T e =
      (Fintype.card (T.induce (U : Set V)).ConnectedComponent : ℝ) - 1 := by
  classical
  rw [sum_inducedEdges_spanningTreeVec hTG U]
  have hfor := card_edgeFinset_add_card_connectedComponent_eq_card (T.induce (U : Set V))
    (hT.isAcyclic.induce (U : Set V))
  have hcardU : Fintype.card (U : Set V) = U.card := Fintype.card_coe U
  rw [hcardU] at hfor
  have hR : ((T.induce (U : Set V)).edgeFinset.card : ℝ) +
      (Fintype.card (T.induce (U : Set V)).ConnectedComponent : ℝ) = (U.card : ℝ) := by
    exact_mod_cast hfor
  linarith

/-- Rooted-tree leaving-edge count: for any spanning tree
`T ≤ G`, nonempty `U ⊆ V`, and root `u ∈ U`, the number of vertices `v ∈ U \ {u}` whose parent
edge `(v, parent(v))` leaves `U` equals the subtour-elimination slack `(|U| - 1) - x(E[U])`. -/
theorem card_leaving_parentEdges_eq_slack {G T : SimpleGraph V} [DecidableRel G.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) (U : Finset V) {u : V} (hu : u ∈ U) :
    (((Finset.univ.filter fun v : {v : V // v ≠ u} =>
        v.1 ∈ U ∧ treeParent T hT u v.1 ∉ U).card : ℝ)) =
      ((U.card : ℝ) - 1) - ∑ e ∈ inducedEdges G U, spanningTreeVec G T e := by
  classical
  let ebij := Equiv.ofBijective _ (treeParent_edge_bijective hT u)
  let inU : Finset {v : V // v ≠ u} := Finset.univ.filter fun v => v.1 ∈ U
  let stay : Finset {v : V // v ≠ u} := inU.filter fun v => treeParent T hT u v.1 ∈ U
  let leave : Finset {v : V // v ≠ u} := inU.filter fun v => treeParent T hT u v.1 ∉ U
  have hleave_eq : (Finset.univ.filter fun v : {v : V // v ≠ u} =>
      v.1 ∈ U ∧ treeParent T hT u v.1 ∉ U) = leave := by
    ext v; simp [leave, inU]
  have hpart : stay.card + leave.card = inU.card := by
    simpa [stay, leave] using Finset.card_filter_add_card_filter_not
      (s := inU) (p := fun v : {v : V // v ≠ u} => treeParent T hT u v.1 ∈ U)
  have hinU_card : inU.card = U.card - 1 := by
    have hbij : inU.card = (U.erase u).card := by
      refine Finset.card_bij (fun v _ => v.1) (fun v hv => ?_)
        (fun a _ b _ h => Subtype.ext h) (fun w hw => ?_)
      · rw [Finset.mem_erase]
        exact ⟨v.2, (Finset.mem_filter.1 hv).2⟩
      · rw [Finset.mem_erase] at hw
        exact ⟨⟨w, hw.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hw.2⟩, rfl⟩
    rw [hbij, Finset.card_erase_of_mem hu]
  have hstay_card : stay.card = (T.induce (U : Set V)).edgeFinset.card := by
    have hsum_edges : (T.induce (U : Set V)).edgeFinset.card =
        (Finset.univ.filter fun e : T.edgeFinset => ∀ w ∈ e.1, w ∈ U).card := by
      refine Finset.card_bij
        (fun e he => (⟨Sym2.map Subtype.val e, by
          have hmem := SimpleGraph.mem_edgeFinset.1 he
          rcases e with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
          exact SimpleGraph.mem_edgeFinset.2 hmem⟩ : T.edgeFinset))
        (fun e he => ?_) (fun a _ b _ h => Sym2.map.injective Subtype.val_injective
          (congrArg Subtype.val h)) (fun f hf => ?_)
      · rcases e with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun w hw => ?_⟩
        change w ∈ s(a, b) at hw
        rw [Sym2.mem_iff] at hw
        rcases hw with rfl | rfl <;> assumption
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rcases f with ⟨f, hfT⟩
        rcases f with ⟨a, b⟩
        have ha : a ∈ U := hf a (Sym2.mem_mk_left a b)
        have hb : b ∈ U := hf b (Sym2.mem_mk_right a b)
        have hadj : T.Adj a b := SimpleGraph.mem_edgeFinset.1 hfT
        exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), SimpleGraph.mem_edgeFinset.2 hadj, Subtype.ext rfl⟩
    rw [hsum_edges]
    refine Finset.card_bij (fun v _ => ebij v) (fun v hv => ?_)
      (fun a _ b _ h => ebij.injective h) (fun f hf => ?_)
    · simp only [stay, inU, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun w hw => ?_⟩
      simp only [ebij, Equiv.ofBijective_apply, Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact hv.1
      · exact hv.2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨ebij.symm f, ?_, ebij.apply_symm_apply f⟩
      have heq := ebij.apply_symm_apply f
      have hsub : (ebij (ebij.symm f)).1 = f.1 := congrArg Subtype.val heq
      simp only [stay, inU, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hf _ (hsub ▸ Sym2.mem_mk_left _ _), hf _ (hsub ▸ Sym2.mem_mk_right _ _)⟩
  rw [hleave_eq, sum_inducedEdges_spanningTreeVec hTG U, ← hstay_card]
  have hUpos : 1 ≤ U.card := Finset.card_pos.2 ⟨u, hu⟩
  have h1 : (stay.card : ℝ) + (leave.card : ℝ) = (U.card : ℝ) - 1 := by
    have hnat : stay.card + leave.card = U.card - 1 := hpart.trans hinU_card
    have hR : (stay.card : ℝ) + (leave.card : ℝ) = ((U.card - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [hR, Nat.cast_sub hUpos, Nat.cast_one]
  linarith

end SpanningTreeDefs

/-! ### Edmonds' Spanning Tree Polytope Theorem -/

section EdmondsSpanningTree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Abel summation inequality for nonnegative antitone weights. -/
private theorem sum_mul_le_sum_mul_of_antitone_nonneg :
    ∀ {n : ℕ} (w a b : Fin n → ℝ),
      Antitone w → (∀ i, 0 ≤ w i) →
      (∀ k : ℕ, k ≤ n → (∑ i : Fin n with i.1 < k, a i) ≤ ∑ i : Fin n with i.1 < k, b i) →
      ∑ i : Fin n, w i * a i ≤ ∑ i : Fin n, w i * b i
  | 0, _, _, _, _, _, _ => by simp
  | n + 1, w, a, b, hanti, hw0, hpref => by
    let wLast := w (Fin.last n)
    let w' : Fin n → ℝ := fun i => w i.castSucc - wLast
    have hw'anti : Antitone w' := fun i j hij =>
      sub_le_sub_right (hanti (Fin.castSucc_le_castSucc_iff.2 hij)) wLast
    have hw'0 : ∀ i : Fin n, 0 ≤ w' i := fun i =>
      sub_nonneg.2 (hanti (Fin.le_last i.castSucc))
    have hpref' : ∀ k : ℕ, k ≤ n →
        (∑ i : Fin n with i.1 < k, a i.castSucc) ≤ ∑ i : Fin n with i.1 < k, b i.castSucc := by
      intro k hk
      have h := hpref k (by omega)
      have hnot : ¬ n < k := by omega
      have ha : (∑ i : Fin (n + 1), if i.1 < k then a i else 0) =
          ∑ i : Fin n, if i.1 < k then a i.castSucc else 0 := by
        rw [Fin.sum_univ_castSucc]
        simp [hnot]
      have hb : (∑ i : Fin (n + 1), if i.1 < k then b i else 0) =
          ∑ i : Fin n, if i.1 < k then b i.castSucc else 0 := by
        rw [Fin.sum_univ_castSucc]
        simp [hnot]
      rw [Finset.sum_filter, Finset.sum_filter] at h ⊢
      linarith
    have ih := sum_mul_le_sum_mul_of_antitone_nonneg w' (fun i => a i.castSucc)
      (fun i => b i.castSucc) hw'anti hw'0 hpref'
    have htot : ∑ i : Fin (n + 1), a i ≤ ∑ i : Fin (n + 1), b i := by
      have h1 := hpref (n + 1) le_rfl
      have hfilt : (Finset.univ.filter fun i : Fin (n + 1) => i.1 < n + 1) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => i.2
      rwa [hfilt] at h1
    have hdecomp : ∀ f : Fin (n + 1) → ℝ,
        ∑ i : Fin (n + 1), w i * f i =
          wLast * (∑ i : Fin (n + 1), f i) + ∑ i : Fin n, w' i * f i.castSucc := by
      intro f
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
      have hsum : ∑ i : Fin n, w i.castSucc * f i.castSucc =
          (∑ i : Fin n, wLast * f i.castSucc) + ∑ i : Fin n, w' i * f i.castSucc := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [w']
        ring
      linarith
    rw [hdecomp a, hdecomp b]
    exact add_le_add (mul_le_mul_of_nonneg_left htot (hw0 (Fin.last n))) ih

/-- Abel summation inequality for arbitrary (possibly negative) antitone weights when total sums
are equal. -/
private theorem sum_mul_le_sum_mul_of_antitone_eq {n : ℕ} (w a b : Fin n → ℝ)
    (hanti : Antitone w)
    (hpref : ∀ k : ℕ, k ≤ n → (∑ i : Fin n with i.1 < k, a i) ≤ ∑ i : Fin n with i.1 < k, b i)
    (htot : ∑ i : Fin n, a i = ∑ i : Fin n, b i) :
    ∑ i : Fin n, w i * a i ≤ ∑ i : Fin n, w i * b i := by
  cases n with
  | zero => simp
  | succ m =>
    let c := w (Fin.last m)
    let w' : Fin (m + 1) → ℝ := fun i => w i - c
    have hw'anti : Antitone w' := fun i j hij => sub_le_sub_right (hanti hij) c
    have hw'0 : ∀ i : Fin (m + 1), 0 ≤ w' i := fun i => sub_nonneg.2 (hanti (Fin.le_last i))
    have h := sum_mul_le_sum_mul_of_antitone_nonneg w' a b hw'anti hw'0 hpref
    have hshift : ∀ f : Fin (m + 1) → ℝ,
        ∑ i : Fin (m + 1), w' i * f i = (∑ i, w i * f i) - c * ∑ i, f i := by
      intro f
      simp only [w', sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hshift a, hshift b, htot] at h
    linarith

section KruskalHelpers

/-- Kruskal greedy forest construction on an edge list `L`, taking prefix length `k`. -/
private noncomputable def kruskalPrefix (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List G.edgeFinset) : ℕ → SimpleGraph V
  | 0 => ⊥
  | k + 1 => by
    classical
    let prev := kruskalPrefix G L k
    exact if h : k < L.length then
      let e := L[k]
      if ¬ prev.Reachable e.1.out.1 e.1.out.2 then
        prev ⊔ SimpleGraph.edge e.1.out.1 e.1.out.2
      else prev
    else prev

/-- The full graph formed by the first `k` edges of `L`. -/
private def edgePrefixGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List G.edgeFinset) (k : ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Subtype.val '' {e : G.edgeFinset | e ∈ L.take k})

omit [DecidableEq V] in
private theorem kruskalPrefix_invariants (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List G.edgeFinset) :
    ∀ k, k ≤ L.length →
      kruskalPrefix G L k ≤ edgePrefixGraph G L k ∧
      (kruskalPrefix G L k).IsAcyclic ∧
      (∀ u v, (kruskalPrefix G L k).Reachable u v ↔ (edgePrefixGraph G L k).Reachable u v) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨bot_le, SimpleGraph.isAcyclic_bot, fun u v => ?_⟩
    have hempty : edgePrefixGraph G L 0 = ⊥ := by
      ext a b; simp [edgePrefixGraph]
    rw [hempty]
    rfl
  | succ k ih =>
    intro hk
    obtain ⟨hle, hacyc, hreach⟩ := ih (by omega)
    have hkl : k < L.length := by omega
    set e := L[k]
    set u := e.1.out.1
    set v := e.1.out.2
    have huv_eq : s(u, v) = e.1 := Quot.out_eq e.1
    have huv_ne : u ≠ v := by
      have heG : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.1 e.2
      rw [← huv_eq] at heG
      exact G.ne_of_adj heG
    have htake : edgePrefixGraph G L (k + 1) = edgePrefixGraph G L k ⊔ SimpleGraph.edge u v := by
      ext a b
      simp only [edgePrefixGraph, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj,
        SimpleGraph.edge_adj, Set.mem_image, Set.mem_ofPred_eq,
        List.take_succ_eq_append_getElem hkl, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨⟨f, hf | rfl, hfab⟩, hab⟩
        · exact Or.inl ⟨⟨f, hf, hfab⟩, hab⟩
        · right
          rw [← huv_eq] at hfab
          exact ⟨Sym2.eq_iff.1 hfab.symm, hab⟩
      · rintro (⟨⟨f, hf, hfab⟩, hab⟩ | ⟨hpair, hab⟩)
        · exact ⟨⟨f, Or.inl hf, hfab⟩, hab⟩
        · refine ⟨⟨e, Or.inr rfl, ?_⟩, hab⟩
          rw [← huv_eq]; exact (Sym2.eq_iff.2 hpair).symm
    simp only [kruskalPrefix, hkl, ↓reduceDIte]
    split_ifs with hr
    · refine ⟨hle.trans (htake ▸ le_sup_left), hacyc, fun a b => ?_⟩
      rw [htake]
      constructor
      · exact fun h => ((hreach a b).1 h).mono le_sup_left
      · intro ⟨p⟩
        induction p with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons x y z hxy _ ihp =>
          refine SimpleGraph.Reachable.trans ?_ ihp
          rcases hxy with hxy1 | hxy2
          · exact (hreach x y).2 hxy1.reachable
          · rcases Sym2.eq_iff.1 hxy2.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hr
            · exact hr.symm
    · refine ⟨?_, hacyc.sup_edge_of_not_reachable hr, fun a b => ?_⟩
      · rw [htake]
        exact sup_le_sup_right hle _
      · rw [htake]
        constructor
        · exact SimpleGraph.Reachable.mono (sup_le_sup_right hle _)
        · intro ⟨p⟩
          induction p with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x y z hxy _ ihp =>
            refine SimpleGraph.Reachable.trans ?_ ihp
            rcases hxy with hxy1 | hxy2
            · exact ((hreach x y).2 hxy1.reachable).mono le_sup_left
            · exact (SimpleGraph.Adj.reachable (Or.inr hxy2))

omit [DecidableEq V] in
private theorem kruskalPrefix_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List G.edgeFinset) {j k : ℕ} (hjk : j ≤ k) :
    kruskalPrefix G L j ≤ kruskalPrefix G L k := by
  classical
  induction hjk with
  | refl => exact le_rfl
  | @step m _ ih =>
    refine ih.trans ?_
    simp only [kruskalPrefix]
    split_ifs
    · exact le_rfl
    · exact le_sup_left
    · exact le_rfl

omit [DecidableEq V] in
private theorem kruskalPrefix_mem_edgeSet_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : List G.edgeFinset) (hL : L.Nodup) {k : ℕ} (hk : k ≤ L.length) (i : Fin L.length) :
    L[i.1].1 ∈ (kruskalPrefix G L k).edgeSet ↔
      i.1 < k ∧ L[i.1].1 ∈ (kruskalPrefix G L L.length).edgeSet := by
  classical
  have hsub : ∀ m ≤ L.length, (kruskalPrefix G L m).edgeSet ⊆
      Subtype.val '' {e : G.edgeFinset | e ∈ L.take m} := fun m hm => by
    have hle := (kruskalPrefix_invariants G L m hm).1
    intro e he
    have he' : e ∈ (edgePrefixGraph G L m).edgeSet := SimpleGraph.edgeSet_mono hle he
    rcases e with ⟨a, b⟩
    rw [SimpleGraph.mem_edgeSet, edgePrefixGraph, SimpleGraph.fromEdgeSet_adj] at he'
    exact he'.1
  constructor
  · intro hi
    refine ⟨?_, SimpleGraph.edgeSet_mono (kruskalPrefix_mono G L hk) hi⟩
    have hmem := hsub k hk hi
    rcases hmem with ⟨f, hf, hfeq⟩
    have hfe : f = L[i.1] := Subtype.ext hfeq
    subst hfe
    change L[i.1] ∈ L.take k at hf
    rw [List.mem_iff_getElem] at hf
    obtain ⟨j, hj, hjeq⟩ := hf
    have hjlt : j < k := by
      rw [List.length_take] at hj
      omega
    have hjL : j < L.length := by omega
    rw [List.getElem_take] at hjeq
    have hij : j = i.1 := (List.Nodup.getElem_inj_iff hL).1 hjeq
    omega
  · rintro ⟨hik, hi⟩
    have hnot_added : ∀ m, k ≤ m → m ≤ L.length →
        L[i.1].1 ∈ (kruskalPrefix G L m).edgeSet → L[i.1].1 ∈ (kruskalPrefix G L k).edgeSet := by
      intro m hkm hmL
      induction m, hkm using Nat.le_induction with
      | base => exact id
      | succ m hkm' ihm =>
        intro hin
        apply ihm (by omega)
        have hml : m < L.length := by omega
        simp only [kruskalPrefix, hml, ↓reduceDIte] at hin
        split_ifs at hin with hnr
        · exact hin
        · rw [SimpleGraph.edgeSet_sup, Set.mem_union] at hin
          rcases hin with h1 | h2
          · exact h1
          · have hpair : L[i.1].1 = s(L[m].1.out.1, L[m].1.out.2) := by
              rw [SimpleGraph.edgeSet_edge] at h2
              exact Set.mem_singleton_iff.1 h2.1
            rw [show s(L[m].1.out.1, L[m].1.out.2) = L[m].1 from Quot.out_eq L[m].1] at hpair
            have hEq : L[i.1] = L[m] := Subtype.ext hpair
            have him : i.1 = m := (List.Nodup.getElem_inj_iff hL).1 hEq
            omega
    exact hnot_added L.length hk le_rfl hi

end KruskalHelpers

/-- **Edmonds' Spanning Tree Polytope Theorem**: for every finite connected simple graph `G`,
`SPAN(G)` equals the
non-negativity, total-size, and subtour-elimination inequalities. -/
theorem spanningTreePolytope_eq_hPolytope [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    spanningTreePolytope G = spanningTreeHPolytope G := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · -- `SPAN(G) ⊆ H-polytope`
    refine convexHull_min ?_ ?_
    · rintro _ ⟨⟨T, hTG, hT⟩, rfl⟩
      refine ⟨fun e => by simp only [spanningTreeVec]; split_ifs <;> norm_num, ?_, fun U hU => ?_⟩
      · have hcard : ∑ e : G.edgeFinset, spanningTreeVec G T e = (T.edgeFinset.card : ℝ) := by
          simp only [spanningTreeVec, Finset.sum_boole]
          norm_cast
          refine Finset.card_bij (fun e _ => e.1)
            (fun e he => SimpleGraph.mem_edgeFinset.2 (Finset.mem_filter.1 he).2)
            (fun a _ b _ h => Subtype.ext h)
            (fun f hf => ⟨⟨f, SimpleGraph.mem_edgeFinset.2
              (SimpleGraph.edgeSet_mono hTG (SimpleGraph.mem_edgeFinset.1 hf))⟩,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.mem_edgeFinset.1 hf⟩, rfl⟩)
        rw [hcard]
        have ht : (T.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
          exact_mod_cast hT.card_edgeFinset
        linarith
      · have hslack := spanningTree_slack_eq_components_sub_one hTG hT U
        have hpos : 1 ≤ Fintype.card (T.induce (U : Set V)).ConnectedComponent := by
          obtain ⟨u, hu⟩ := hU
          exact Fintype.card_pos_iff.2 ⟨(T.induce (U : Set V)).connectedComponentMk ⟨u, hu⟩⟩
        have hposR : (1 : ℝ) ≤ Fintype.card (T.induce (U : Set V)).ConnectedComponent := by
          exact_mod_cast hpos
        linarith
    · intro x hx y hy a b ha hb hab
      refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_,
        fun U hU => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hx.2.1, hy.2.1]
        nlinarith
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        have hxU := hx.2.2 U hU
        have hyU := hy.2.2 U hU
        nlinarith
  · -- `H-polytope ⊆ SPAN(G)` via Hahn–Banach + Kruskal + Abel summation
    intro x hx
    by_contra hxS
    have hcomp : IsCompact (spanningTreePolytope G) :=
      (Set.finite_range _).isCompact_convexHull ℝ
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hcomp.isClosed hxS
    let w : G.edgeFinset → ℝ := fun e => f (Pi.single e (1 : ℝ))
    have hf_eq : ∀ y : G.edgeFinset → ℝ, f y = ∑ e : G.edgeFinset, w e * y e := fun y => by
      have hy : y = ∑ e : G.edgeFinset, y e • Pi.single e (1 : ℝ) := by
        ext e; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hy]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    -- Sort `G.edgeFinset` in decreasing order of `w`.
    let L : List G.edgeFinset :=
      (Finset.univ : Finset G.edgeFinset).toList.mergeSort (fun a b => decide (w b ≤ w a))
    have hperm : L.Perm (Finset.univ : Finset G.edgeFinset).toList := List.mergeSort_perm _ _
    have hLnodup : L.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
    have hLmem : ∀ e : G.edgeFinset, e ∈ L := fun e =>
      hperm.mem_iff.2 (Finset.mem_toList.2 (Finset.mem_univ e))
    have hLpair : L.Pairwise (fun a b => w b ≤ w a) := by
      have hp := List.pairwise_mergeSort (l := (Finset.univ : Finset G.edgeFinset).toList)
        (le := fun a b => decide (w b ≤ w a))
        (by intro a b c hab hbc; simp only [decide_eq_true_eq] at hab hbc ⊢; exact hbc.trans hab)
        (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total (w b) (w a))
      exact hp.imp fun h => of_decide_eq_true h
    let T := kruskalPrefix G L L.length
    obtain ⟨hTle_full, hTacyc, hTreach⟩ := kruskalPrefix_invariants G L L.length le_rfl
    have hfull_eq : edgePrefixGraph G L L.length = G := by
      ext a b
      simp only [edgePrefixGraph, List.take_length, SimpleGraph.fromEdgeSet_adj, Set.mem_image,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨e, -, he⟩, -⟩
        have hmem := SimpleGraph.mem_edgeFinset.1 e.2
        rwa [he] at hmem
      · intro hab
        exact ⟨⟨⟨s(a, b), SimpleGraph.mem_edgeFinset.2 hab⟩, hLmem _, rfl⟩, G.ne_of_adj hab⟩
    have hTG : T ≤ G := hfull_eq ▸ hTle_full
    have hTconn : T.Connected := by
      refine SimpleGraph.Connected.mk fun a b => ?_
      rw [hTreach a b, hfull_eq]
      exact hG a b
    have hTtree : T.IsTree := ⟨hTconn, hTacyc⟩
    -- Bijection `Fin L.length ≃ G.edgeFinset`.
    let idxEquiv : Fin L.length ≃ G.edgeFinset :=
      Equiv.ofBijective (fun i => L[i.1]) <| by
        refine ⟨fun i j hij => Fin.ext ((List.Nodup.getElem_inj_iff hLnodup).1 hij), fun e => ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (hLmem e)
        exact ⟨⟨i, hi⟩, rfl⟩
    let w' : Fin L.length → ℝ := fun i => w (idxEquiv i)
    let a' : Fin L.length → ℝ := fun i => x (idxEquiv i)
    let b' : Fin L.length → ℝ := fun i => spanningTreeVec G T (idxEquiv i)
    have hanti : Antitone w' := fun i j hij => by
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact le_rfl
      · exact List.pairwise_iff_getElem.1 hLpair i.1 j.1 i.2 j.2 hlt
    have hpref : ∀ k : ℕ, k ≤ L.length →
        (∑ i : Fin L.length with i.1 < k, a' i) ≤ ∑ i : Fin L.length with i.1 < k, b' i := by
      intro k hk
      obtain ⟨_, hKacyc, hKreach⟩ := kruskalPrefix_invariants G L k hk
      set Hk := edgePrefixGraph G L k
      set Tk := kruskalPrefix G L k
      have hTcard : (∑ i : Fin L.length with i.1 < k, b' i) = (Tk.edgeFinset.card : ℝ) := by
        simp only [b', idxEquiv, spanningTreeVec, Finset.sum_boole]
        norm_cast
        refine Finset.card_bij (fun i _ => L[i.1].1) (fun i hi => ?_)
          (fun i _ j _ h => Fin.ext ((List.Nodup.getElem_inj_iff hLnodup).1 (Subtype.ext h)))
          (fun e he => ?_)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact SimpleGraph.mem_edgeFinset.2
            ((kruskalPrefix_mem_edgeSet_iff G L hLnodup hk i).2 hi)
        · have heG : e ∈ G.edgeSet :=
            SimpleGraph.edgeSet_mono ((kruskalPrefix_mono G L hk).trans hTG)
              (SimpleGraph.mem_edgeFinset.1 he)
          let ef : G.edgeFinset := ⟨e, SimpleGraph.mem_edgeFinset.2 heG⟩
          obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.1 (hLmem ef)
          have hmem_k : L[j].1 ∈ Tk.edgeSet := by
            rw [hjeq]; exact SimpleGraph.mem_edgeFinset.1 he
          have hpair := (kruskalPrefix_mem_edgeSet_iff G L hLnodup hk ⟨j, hj⟩).1 hmem_k
          exact ⟨⟨j, hj⟩, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hpair.1⟩,
            hpair.2⟩, by rw [hjeq]⟩
      rw [hTcard]
      -- Each component `c` of `Hk` gives `x(E[c]) ≤ |c| - 1`, summing to `|V| - c(Hk) = |E(Tk)|`.
      let compFin (c : Hk.ConnectedComponent) : Finset V :=
        Finset.univ.filter fun v => Hk.connectedComponentMk v = c
      have hcomp_ne : ∀ c : Hk.ConnectedComponent, (compFin c).Nonempty := fun c => by
        obtain ⟨v, rfl⟩ := c.exists_rep
        exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, rfl⟩⟩
      have hcomp_card : ∑ c : Hk.ConnectedComponent, ((compFin c).card : ℝ) = Fintype.card V := by
        have hnat : ∑ c : Hk.ConnectedComponent, (compFin c).card = Fintype.card V := by
          simpa [compFin] using (Finset.card_eq_sum_card_fiberwise
            (f := Hk.connectedComponentMk) (s := Finset.univ) (t := Finset.univ)
            fun _ _ => Finset.mem_univ _).symm
        exact_mod_cast hnat
      have hcomp_eq : Fintype.card Tk.ConnectedComponent = Fintype.card Hk.ConnectedComponent := by
        refine Fintype.card_congr
          { toFun := Quot.lift (fun v => Hk.connectedComponentMk v)
              (fun a b hab => SimpleGraph.ConnectedComponent.sound ((hKreach a b).1 hab))
            invFun := Quot.lift (fun v => Tk.connectedComponentMk v)
              (fun a b hab => SimpleGraph.ConnectedComponent.sound ((hKreach a b).2 hab))
            left_inv := fun c => by obtain ⟨v, rfl⟩ := c.exists_rep; rfl
            right_inv := fun c => by obtain ⟨v, rfl⟩ := c.exists_rep; rfl }
      have hfor := card_edgeFinset_add_card_connectedComponent_eq_card Tk hKacyc
      rw [hcomp_eq] at hfor
      have hTk_eq : (Tk.edgeFinset.card : ℝ) =
          ∑ c : Hk.ConnectedComponent, (((compFin c).card : ℝ) - 1) := by
        rw [Finset.sum_sub_distrib, hcomp_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one]
        have hR : (Tk.edgeFinset.card : ℝ) + (Fintype.card Hk.ConnectedComponent : ℝ) =
            (Fintype.card V : ℝ) := by exact_mod_cast hfor
        linarith
      rw [hTk_eq]
      -- Every edge `L[i]` with `i < k` belongs to `inducedEdges G (compFin c)` for a unique `c`.
      let S : Finset G.edgeFinset :=
        (Finset.univ.filter fun i : Fin L.length => i.1 < k).image idxEquiv
      have hsum_a : (∑ i : Fin L.length with i.1 < k, a' i) = ∑ e ∈ S, x e := by
        symm
        exact Finset.sum_image fun _ _ _ _ h => idxEquiv.injective h
      rw [hsum_a]
      have hdisj : ((Finset.univ : Finset Hk.ConnectedComponent) :
          Set Hk.ConnectedComponent).PairwiseDisjoint
          (fun c => inducedEdges G (compFin c)) := by
        intro c₁ _ c₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e he₁ he₂
        have hu₁ := (Finset.mem_filter.1 he₁).2 e.1.out.1 (Sym2.out_fst_mem e.1)
        have hu₂ := (Finset.mem_filter.1 he₂).2 e.1.out.1 (Sym2.out_fst_mem e.1)
        have h1 : Hk.connectedComponentMk e.1.out.1 = c₁ := (Finset.mem_filter.1 hu₁).2
        have h2 : Hk.connectedComponentMk e.1.out.1 = c₂ := (Finset.mem_filter.1 hu₂).2
        exact hne (h1.symm.trans h2)
      have hS_sub : S ⊆ Finset.univ.biUnion fun c : Hk.ConnectedComponent =>
          inducedEdges G (compFin c) := by
        intro e he
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
        have hik : i.1 < k := (Finset.mem_filter.1 hi).2
        set u₀ := (idxEquiv i).1.out.1
        set v₀ := (idxEquiv i).1.out.2
        have hpair : s(u₀, v₀) = (idxEquiv i).1 := Quot.out_eq _
        have hne : u₀ ≠ v₀ := by
          have heG := SimpleGraph.mem_edgeFinset.1 (idxEquiv i).2
          rw [← hpair] at heG
          exact G.ne_of_adj heG
        have hadj : Hk.Adj u₀ v₀ := by
          rw [show Hk = edgePrefixGraph G L k from rfl, edgePrefixGraph,
            SimpleGraph.fromEdgeSet_adj]
          refine ⟨⟨idxEquiv i, ?_, hpair.symm⟩, hne⟩
          change idxEquiv i ∈ L.take k
          rw [List.mem_iff_getElem]
          refine ⟨i.1, ?_, by rw [List.getElem_take]; rfl⟩
          rw [List.length_take]; omega
        refine Finset.mem_biUnion.2 ⟨Hk.connectedComponentMk u₀, Finset.mem_univ _,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, fun w hw => ?_⟩⟩
        rw [← hpair, Sym2.mem_iff] at hw
        refine Finset.mem_filter.2 ⟨Finset.mem_univ w, ?_⟩
        rcases hw with rfl | rfl
        · rfl
        · exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm
      calc ∑ e ∈ S, x e
          ≤ ∑ e ∈ Finset.univ.biUnion (fun c : Hk.ConnectedComponent => inducedEdges G (compFin c)),
              x e := Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun e _ _ => hx.1 e
        _ = ∑ c : Hk.ConnectedComponent, ∑ e ∈ inducedEdges G (compFin c), x e :=
            Finset.sum_biUnion fun c₁ hc₁ c₂ hc₂ hne => hdisj hc₁ hc₂ hne
        _ ≤ ∑ c : Hk.ConnectedComponent, (((compFin c).card : ℝ) - 1) :=
            Finset.sum_le_sum fun c _ => hx.2.2 (compFin c) (hcomp_ne c)
    have htot : ∑ i : Fin L.length, a' i = ∑ i : Fin L.length, b' i := by
      have ha : ∑ i : Fin L.length, a' i = ∑ e : G.edgeFinset, x e :=
        Equiv.sum_comp idxEquiv x
      have hb : ∑ i : Fin L.length, b' i = ∑ e : G.edgeFinset, spanningTreeVec G T e :=
        Equiv.sum_comp idxEquiv (spanningTreeVec G T)
      have hTtot : ∑ e : G.edgeFinset, spanningTreeVec G T e = (Fintype.card V : ℝ) - 1 := by
        have hcard : ∑ e : G.edgeFinset, spanningTreeVec G T e = (T.edgeFinset.card : ℝ) := by
          simp only [spanningTreeVec, Finset.sum_boole]
          norm_cast
          refine Finset.card_bij (fun e _ => e.1)
            (fun e he => SimpleGraph.mem_edgeFinset.2 (Finset.mem_filter.1 he).2)
            (fun a _ b _ h => Subtype.ext h)
            (fun f hf => ⟨⟨f, SimpleGraph.mem_edgeFinset.2
              (SimpleGraph.edgeSet_mono hTG (SimpleGraph.mem_edgeFinset.1 hf))⟩,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.mem_edgeFinset.1 hf⟩, rfl⟩)
        rw [hcard]
        have ht : (T.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
          exact_mod_cast hTtree.card_edgeFinset
        linarith
      rw [ha, hb, hx.2.1, hTtot]
    have habel := sum_mul_le_sum_mul_of_antitone_eq w' a' b' hanti hpref htot
    have hfx : f x = ∑ i : Fin L.length, w' i * a' i := by
      rw [hf_eq x]
      exact (Equiv.sum_comp idxEquiv fun e => w e * x e).symm
    have hfT : f (spanningTreeVec G T) = ∑ i : Fin L.length, w' i * b' i := by
      rw [hf_eq (spanningTreeVec G T)]
      exact (Equiv.sum_comp idxEquiv fun e => w e * spanningTreeVec G T e).symm
    have hTmem : spanningTreeVec G T ∈ spanningTreePolytope G :=
      subset_convexHull ℝ _ ⟨⟨T, hTG, hTtree⟩, rfl⟩
    have hlt := hfu _ hTmem
    linarith

/-! ### Matrix form of Edmonds' H-description for `SPAN(G)` -/

/-- Non-trivial row indices for `SPAN(G)`: all nonempty vertex subsets `U ⊆ V` (subtour
elimination `x(E[U]) ≤ |U| - 1`) plus one reversed total-edge inequality
`-x(E) ≤ -(|V| - 1)`. -/
abbrev SpanningTreeNontrivRow (V : Type*) := {U : Finset V // U.Nonempty} ⊕ Unit

/-- Non-trivial constraint matrix `A'` for `SPAN(G)`. -/
@[expose] def spanningTreeNontrivMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix (SpanningTreeNontrivRow V) G.edgeFinset ℝ :=
  Matrix.of fun row e =>
    match row with
    | Sum.inl U => if e ∈ inducedEdges G U.1 then 1 else 0
    | Sum.inr () => -1

/-- Non-trivial right-hand side `b'` for `SPAN(G)`. -/
@[expose] def spanningTreeNontrivRHS : SpanningTreeNontrivRow V → ℝ :=
  fun row =>
    match row with
    | Sum.inl U => (U.1.card : ℝ) - 1
    | Sum.inr () => -((Fintype.card V : ℝ) - 1)

/-- Full H-description matrix `A` for `SPAN(G)` split into non-negativity rows `G.edgeFinset` and
non-trivial rows `SpanningTreeNontrivRow V`. -/
@[expose] def spanningTreeFullMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix (G.edgeFinset ⊕ SpanningTreeNontrivRow V) G.edgeFinset ℝ :=
  Matrix.fromRows (-1 : Matrix G.edgeFinset G.edgeFinset ℝ) (spanningTreeNontrivMatrix G)

/-- Full right-hand side `b` for `SPAN(G)`. -/
@[expose] def spanningTreeFullRHS (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset ⊕ SpanningTreeNontrivRow V → ℝ :=
  Sum.elim 0 (spanningTreeNontrivRHS (V := V))

/-- Non-negativity row entry of `spanningTreeFullMatrix G`. -/
theorem spanningTreeFullMatrix_apply_inl (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : G.edgeFinset) :
    spanningTreeFullMatrix G (Sum.inl e) f = -(if e = f then (1 : ℝ) else 0) := by
  simp [spanningTreeFullMatrix, Matrix.one_apply]

/-- Subtour-elimination row entry of `spanningTreeFullMatrix G`. -/
theorem spanningTreeFullMatrix_apply_inr_inl (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : {U : Finset V // U.Nonempty}) (e : G.edgeFinset) :
    spanningTreeFullMatrix G (Sum.inr (Sum.inl U)) e = if e ∈ inducedEdges G U.1 then 1 else 0 :=
  rfl

/-- Total-edge-count row entry of `spanningTreeFullMatrix G`. -/
theorem spanningTreeFullMatrix_apply_inr_inr (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeFinset) :
    spanningTreeFullMatrix G (Sum.inr (Sum.inr ())) e = -1 := rfl

omit [DecidableEq V] in
/-- Non-negativity row right-hand side of `spanningTreeFullRHS G`. -/
theorem spanningTreeFullRHS_apply_inl (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeFinset) :
    spanningTreeFullRHS G (Sum.inl e) = 0 := rfl

omit [DecidableEq V] in
/-- Subtour-elimination row right-hand side of `spanningTreeFullRHS G`. -/
theorem spanningTreeFullRHS_apply_inr_inl (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : {U : Finset V // U.Nonempty}) :
    spanningTreeFullRHS G (Sum.inr (Sum.inl U)) = (U.1.card : ℝ) - 1 := rfl

omit [DecidableEq V] in
/-- Total-edge-count row right-hand side of `spanningTreeFullRHS G`. -/
theorem spanningTreeFullRHS_apply_inr_inr (G : SimpleGraph V) [DecidableRel G.Adj] :
    spanningTreeFullRHS G (Sum.inr (Sum.inr ())) = -((Fintype.card V : ℝ) - 1) := rfl

/-- Matrix form of Edmonds' Spanning Tree Polytope Theorem: for any finite connected simple graph
`G`, `SPAN(G) = {x | spanningTreeFullMatrix G *ᵥ x ≤ spanningTreeFullRHS G}`. -/
theorem spanningTreePolytope_eq_setOf_mulVec_le [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) :
    spanningTreePolytope G = {x | spanningTreeFullMatrix G *ᵥ x ≤ spanningTreeFullRHS G} := by
  rw [spanningTreePolytope_eq_hPolytope G hG]
  ext x
  simp only [spanningTreeHPolytope, Set.mem_ofPred_eq, Pi.le_def, spanningTreeFullMatrix,
    spanningTreeFullRHS, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨h0, heq, hU⟩ (e | (U | u))
    · simp [h0 e]
    · simp only [Sum.elim_inr, Matrix.mulVec, dotProduct, spanningTreeNontrivMatrix,
        spanningTreeNontrivRHS, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem,
        Finset.univ_inter]
      exact hU U.1 U.2
    · simp only [Sum.elim_inr, Matrix.mulVec, dotProduct, spanningTreeNontrivMatrix,
        spanningTreeNontrivRHS, Matrix.of_apply, neg_mul, one_mul, Finset.sum_neg_distrib,
        neg_le_neg_iff]
      exact heq.ge
  · intro h
    refine ⟨fun e => ?_, ?_, fun U hU => ?_⟩
    · have he := h (Sum.inl e)
      simpa using he
    · have hle : ∑ e : G.edgeFinset, x e ≤ (Fintype.card V : ℝ) - 1 := by
        have h1 := h (Sum.inr (Sum.inl ⟨Finset.univ, Finset.univ_nonempty⟩))
        have hind : inducedEdges G Finset.univ = Finset.univ := by
          ext e; simp [inducedEdges]
        simpa [Matrix.mulVec, dotProduct, spanningTreeNontrivMatrix, spanningTreeNontrivRHS,
          hind] using h1
      have hge : (Fintype.card V : ℝ) - 1 ≤ ∑ e : G.edgeFinset, x e := by
        have h2 := h (Sum.inr (Sum.inr ()))
        simp only [Sum.elim_inr, Matrix.mulVec, dotProduct, spanningTreeNontrivMatrix,
          spanningTreeNontrivRHS, Matrix.of_apply, neg_mul, one_mul, Finset.sum_neg_distrib,
          neg_le_neg_iff] at h2
        exact h2
      exact le_antisymm hle hge
    · have h1 := h (Sum.inr (Sum.inl ⟨U, hU⟩))
      simp only [Sum.elim_inr, Matrix.mulVec, dotProduct, spanningTreeNontrivMatrix,
        spanningTreeNontrivRHS, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem,
        Finset.univ_inter] at h1
      exact h1

end EdmondsSpanningTree

end CslibFrontier.ExtendedFormulation
