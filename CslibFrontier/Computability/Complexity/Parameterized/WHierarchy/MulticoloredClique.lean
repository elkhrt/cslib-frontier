/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
public import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Multicolored Clique: `W[1]`-Completeness and `NP`-Completeness

Under standard Lean axioms, this module formalizes the parameterized **Multicolored Clique**
(`k`-Colored Clique) problem and proves its equivalence with `Cslib.Complexity.Clique` under both
polynomial-time
many-one reductions and parameter-preserving FPT reductions:

1. **Multicolored Clique (`MulticoloredCliqueInstance`, `MulticoloredClique`)**: given an undirected
   graph `G`, a vertex coloring list `colors`, and an integer `k`, decide whether `G` contains `k`
   pairwise adjacent declared vertices `v_0, …, v_{k-1}` with `colorOf G colors v_i = i`.
2. **Reduction from `Clique` (`cliqueToMulticoloredClique`)**: duplicating `V(G)` into `k` color
   classes (when `k ≤ |V(G)|`, and outputting an empty graph otherwise) runs in polynomial time,
   preserves `k`, and proves `MulticoloredClique` is `W[1]`-hard and `NP`-hard.
3. **Reduction to `Clique` (`multicoloredCliqueToClique`)**: retaining only properly colored edges
   between color classes `< k` runs in polynomial time, preserves `k`, and proves
   `MulticoloredClique ∈ W[1]` and `MulticoloredClique ∈ NP`.

## Main definitions

* `Cslib.Complexity.MulticoloredCliqueInstance`,
  `Cslib.Complexity.encMulticoloredClique`: instances `(graph, colors, k)` and their
  framed binary encoding.
* `Cslib.Complexity.MulticoloredClique`: the Multicolored Clique decision problem.
* `Cslib.Complexity.cliqueToMulticoloredClique`,
  `Cslib.Complexity.multicoloredCliqueToClique`: parameter-preserving
  polynomial-time reductions between `Clique` and `MulticoloredClique`.

## Main results

* `Cslib.Complexity.mem_multicoloredClique_iff_finset`: characterization as a
  `k`-clique whose image under `colorOf` equals `Finset.range k`.
* `Cslib.Complexity.cliqueToMulticoloredClique_mem_iff`,
  `Cslib.Complexity.multicoloredCliqueToClique_mem_iff`: correctness of both
  reductions.
* `Cslib.Complexity.multicoloredClique_wHard`,
  `Cslib.Complexity.multicoloredClique_mem_W`: `W[1]`-completeness.
* `Cslib.Complexity.multicoloredClique_npComplete`: `NP`-completeness.

## Tags

multicolored clique, parameterized complexity, W[1]-completeness, FPT reduction
-/

public section

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

namespace Cslib.Complexity

/-! ### 1. Problem Definition and Equivalences -/

/-- An instance `(graph, colors, k)` of **Multicolored Clique**. -/
@[ext]
structure MulticoloredCliqueInstance where
  /-- Underlying undirected graph. -/
  graph : Graph
  /-- Vertex colors listed parallel to `graph.vertices` (read via `Cslib.Complexity.colorOf`). -/
  colors : List ℕ
  /-- Number of color classes / target clique size. -/
  k : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed binary encoding of `MulticoloredCliqueInstance`. -/
enc_structure encMulticoloredClique : MulticoloredCliqueInstance where
  graph : encGraph,
  colors : (encList encNat),
  k : encNat

/-- **Multicolored Clique**: instances admitting `k` pairwise adjacent declared vertices
`f 0, …, f (k - 1)` with `colorOf x.graph x.colors (f i) = i`. -/
def MulticoloredClique : Set MulticoloredCliqueInstance :=
  {x | ∃ f : Fin x.k → ℕ,
    (∀ i : Fin x.k, f i ∈ x.graph.vertices ∧ colorOf x.graph x.colors (f i) = i.1) ∧
    ∀ i j : Fin x.k, i ≠ j → x.graph.toSimpleGraph.Adj (f i) (f j)}

/-- Unfolding characterization of `MulticoloredClique`. -/
theorem mem_multicoloredClique_iff {x : MulticoloredCliqueInstance} :
    x ∈ MulticoloredClique ↔
      ∃ f : Fin x.k → ℕ,
        (∀ i : Fin x.k, f i ∈ x.graph.vertices ∧ colorOf x.graph x.colors (f i) = i.1) ∧
        ∀ i j : Fin x.k, i ≠ j → x.graph.toSimpleGraph.Adj (f i) (f j) := by
  unfold MulticoloredClique; rfl

/-- Finset characterization of `MulticoloredClique`: a `k`-clique of declared vertices whose colors
span `Finset.range x.k`. -/
theorem mem_multicoloredClique_iff_finset {x : MulticoloredCliqueInstance} :
    x ∈ MulticoloredClique ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
        x.graph.toSimpleGraph.IsNClique x.k S ∧
        S.image (colorOf x.graph x.colors) = Finset.range x.k := by
  classical
  constructor
  · rintro ⟨f, hfV, hadj⟩
    have hinj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      rw [← (hfV i).2, ← (hfV j).2, hij]
    refine ⟨Finset.univ.image f, ?_, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
      exact (hfV i).1
    · intro u hu v hv huv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hv
      exact hadj i j fun h => huv (h ▸ rfl)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · ext c
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [(hfV i).2]
        exact i.isLt
      · intro hc
        exact ⟨f ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, (hfV ⟨c, hc⟩).2⟩
  · rintro ⟨S, hSV, ⟨hclq, hcard⟩, himg⟩
    have hex : ∀ i : Fin x.k, ∃ v ∈ S, colorOf x.graph x.colors v = i.1 := by
      intro i
      have hi : i.1 ∈ S.image (colorOf x.graph x.colors) := himg ▸ Finset.mem_range.2 i.isLt
      exact Finset.mem_image.1 hi
    choose f hfS hfc using hex
    refine ⟨f, fun i => ⟨hSV (f i) (hfS i), hfc i⟩, fun i j hij => ?_⟩
    have hne : f i ≠ f j := by
      intro heq
      apply hij
      apply Fin.ext
      rw [← hfc i, ← hfc j, heq]
    exact hclq (hfS i) (hfS j) hne

/-! ### 2. Reduction from `Clique` to `MulticoloredClique` (`W[1]`-Hardness) -/

private def mcEntries (G : Graph) (k : ℕ) : List (ℕ × ℕ) :=
  if decide (k ≤ G.vertices.length) then
    (List.range (G.vertices.take k).length).flatMap fun i => G.vertices.map (i, ·)
  else []

private def mcAdj (G : Graph) (p q : ℕ × ℕ) : Bool :=
  decide (p.1 ≠ q.1) && G.adjBool p.2 q.2

/-- Polynomial-time, parameter-preserving reduction from `Clique` to `MulticoloredClique`. -/
def cliqueToMulticoloredClique (x : CliqueInstance) : MulticoloredCliqueInstance :=
  let vs := mcEntries x.graph x.m
  ⟨Graph.ofAdj vs (mcAdj x.graph), vs.map Prod.fst, x.m⟩

private lemma colorOf_ofAdj_fst {V : Type} (vs : List V) (adj : V → V → Bool) (f : V → ℕ)
    {idx : ℕ} (hidx : idx < vs.length) :
    colorOf (Graph.ofAdj vs adj) (vs.map f) idx = f vs[idx] := by
  have hlt_i := List.idxOf_lt_length_of_mem (List.mem_range.2 hidx)
  have hidxOf : (List.range vs.length).idxOf idx = idx := by
    have h1 := List.getElem_idxOf hlt_i
    rwa [List.getElem_range] at h1
  simp [colorOf, Graph.ofAdj, hidxOf, List.getD_eq_getElem?_getD, hidx]

/-- Correctness of `cliqueToMulticoloredClique`. -/
theorem cliqueToMulticoloredClique_mem_iff (x : CliqueInstance) :
    cliqueToMulticoloredClique x ∈ MulticoloredClique ↔ x ∈ Clique := by
  classical
  obtain ⟨G, k⟩ := x
  unfold cliqueToMulticoloredClique
  dsimp only
  by_cases hk : k ≤ G.vertices.length
  · have htake : (G.vertices.take k).length = k := List.length_take_of_le hk
    have hvs : mcEntries G k = (List.range k).flatMap fun i => G.vertices.map (i, ·) := by
      simp [mcEntries, hk, htake]
    constructor
    · rintro ⟨f, hfV, hadj⟩
      have hlt (i : Fin k) : f i < (mcEntries G k).length := by
        have hv := (hfV i).1
        simpa [Graph.ofAdj] using hv
      let g (i : Fin k) : ℕ := ((mcEntries G k)[f i]'(hlt i)).2
      have hg_col (i : Fin k) : ((mcEntries G k)[f i]'(hlt i)).1 = i.1 := by
        have hc := (hfV i).2
        rwa [colorOf_ofAdj_fst _ _ Prod.fst (hlt i)] at hc
      have hg_mem (i : Fin k) : g i ∈ G.vertices := by
        have hmem : (mcEntries G k)[f i]'(hlt i) ∈
            (List.range k).flatMap (fun j => G.vertices.map (j, ·)) :=
          hvs ▸ List.getElem_mem _
        rw [List.mem_flatMap] at hmem
        obtain ⟨_, _, hm⟩ := hmem
        obtain ⟨v, hv, heq⟩ := List.mem_map.1 hm
        simpa [g, ← heq] using hv
      have hg_adj : ∀ i j : Fin k, i ≠ j → G.toSimpleGraph.Adj (g i) (g j) := by
        intro i j hij
        have ha := hadj i j hij
        obtain ⟨_, hi', hj', hor⟩ := Graph.ofAdj_adj.1 ha
        simp only [mcAdj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Graph.adjBool_eq_true_iff] at hor
        rcases hor with ⟨_, h⟩ | ⟨_, h⟩
        · exact h
        · exact h.symm
      have hg_inj : Function.Injective g := by
        intro i j hij
        by_contra hne
        exact (hg_adj i j hne).ne hij
      rw [mem_Clique_iff]
      refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
      · intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
        exact hg_mem i
      · intro u hu v hv huv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hv
        exact hg_adj i j fun h => huv (h ▸ rfl)
      · rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin]
    · rw [mem_Clique_iff]
      rintro ⟨S, hSV, hclq, hcard⟩
      let e := S.equivFinOfCardEq hcard
      let w (i : Fin k) : ℕ := (e.symm i).1
      have hwS (i : Fin k) : w i ∈ S := (e.symm i).2
      have hwV (i : Fin k) : w i ∈ G.vertices := hSV (w i) (hwS i)
      have hpair_mem (i : Fin k) : (i.1, w i) ∈ mcEntries G k := by
        rw [hvs, List.mem_flatMap]
        exact ⟨i.1, List.mem_range.2 i.isLt, List.mem_map.2 ⟨w i, hwV i, rfl⟩⟩
      let idx (i : Fin k) : ℕ := (mcEntries G k).idxOf (i.1, w i)
      have hidx_lt (i : Fin k) : idx i < (mcEntries G k).length :=
        List.idxOf_lt_length_of_mem (hpair_mem i)
      have hidx_get (i : Fin k) : (mcEntries G k)[idx i]'(hidx_lt i) = (i.1, w i) :=
        List.getElem_idxOf (hidx_lt i)
      refine ⟨idx, fun i => ⟨by simpa [Graph.ofAdj] using hidx_lt i, ?_⟩, fun i j hij => ?_⟩
      · rw [colorOf_ofAdj_fst _ _ Prod.fst (hidx_lt i), hidx_get i]
      · have hne_w : w i ≠ w j := by
          intro heq
          apply hij
          exact e.symm.injective (Subtype.ext heq)
        have hne_idx : idx i ≠ idx j := by
          intro heq
          have h1 := hidx_get i
          have h2 := hidx_get j
          have hpair : (i.1, w i) = (j.1, w j) := by
            rw [← h1, ← h2]
            exact congrArg (fun t : Fin (mcEntries G k).length => (mcEntries G k)[t])
              (Fin.ext heq : (⟨idx i, hidx_lt i⟩ : Fin (mcEntries G k).length) =
                ⟨idx j, hidx_lt j⟩)
          exact hij (Fin.ext (Prod.mk.inj hpair).1)
        refine Graph.ofAdj_adj.2 ⟨hne_idx, hidx_lt i, hidx_lt j, Bool.or_eq_true_iff.2 (Or.inl ?_)⟩
        rw [hidx_get i, hidx_get j]
        simp only [mcAdj, Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff]
        exact ⟨fun h => hij (Fin.ext h), hclq (hwS i) (hwS j) hne_w⟩
  · have hvs : mcEntries G k = [] := by simp [mcEntries, hk]
    have hk_pos : 0 < k := by omega
    constructor
    · rintro ⟨f, hfV, _⟩
      have h0 := (hfV ⟨0, hk_pos⟩).1
      simp [hvs, Graph.ofAdj] at h0
    · rw [mem_Clique_iff]
      rintro ⟨S, hSV, _, hcard⟩
      dsimp only at hcard
      have hle : S.card ≤ G.vertices.length :=
        (Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv)).trans
          G.vertices.toFinset_card_le
      omega

/-- Polynomial-time certificate for `cliqueToMulticoloredClique`. -/
@[fun_prop]
theorem computableInPolyTime_cliqueToMulticoloredClique :
    ComputableInPolyTime cliqueToMulticoloredClique encCliqueInstance encMulticoloredClique := by
  have hcond : ComputableInPolyTime
      (fun x : CliqueInstance => decide (x.m ≤ x.graph.vertices.length))
      encCliqueInstance encBool :=
    binary_le' (by fun_prop) (unary_to_binary.comp (by fun_prop))
  have htakeLen : ComputableInPolyTime
      (fun x : CliqueInstance => (x.graph.vertices.take x.m).length)
      encCliqueInstance encUnary := by
    have hmin : ComputableInPolyTime
        (fun x : CliqueInstance => min x.graph.vertices.length x.m)
        encCliqueInstance encUnary :=
      binary_min_unary' (by fun_prop) (by fun_prop)
    simpa only [List.length_take, Nat.min_comm] using hmin
  have hrange : ComputableInPolyTime
      (fun x : CliqueInstance => List.range (x.graph.vertices.take x.m).length)
      encCliqueInstance (encList encNat) := by
    have hr : ComputableInPolyTime
        (fun x : CliqueInstance => List.range (x.graph.vertices.take x.m).length)
        encCliqueInstance (encList encUnary) := range.comp htakeLen
    have hc : ComputableInPolyTime (List.map (fun n : ℕ => n))
        (encList encUnary) (encList encNat) := map unary_to_binary
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using hc.comp hr
  have hvs : ComputableInPolyTime
      (fun x : CliqueInstance => mcEntries x.graph x.m)
      encCliqueInstance (encList (encPair encNat encNat)) := by
    unfold mcEntries
    refine hcond.ite ?_ (const [])
    refine flatMapWithInput hrange ?_
    exact mapWithInput (by fun_prop) (by fun_prop)
  have hadj : ComputableInPolyTime
      (fun p : CliqueInstance × ((ℕ × ℕ) × (ℕ × ℕ)) => mcAdj p.1.graph p.2.1 p.2.2)
      (encPair encCliqueInstance (encPair (encPair encNat encNat) (encPair encNat encNat)))
      encBool := by
    unfold mcAdj
    fun_prop
  have hG := Graph.computableInPolyTime_ofAdj (adj := fun x p q => mcAdj x.graph p q) hvs hadj
  unfold cliqueToMulticoloredClique
  exact encMulticoloredClique_mk_polyTime hG (by fun_prop) (by fun_prop)

/-- `Clique` reduces to `MulticoloredClique` in polynomial time. -/
theorem polyTimeReducible_clique_multicoloredClique :
    PolyTimeReducible encCliqueInstance encMulticoloredClique Clique MulticoloredClique :=
  ⟨cliqueToMulticoloredClique, computableInPolyTime_cliqueToMulticoloredClique,
    fun x => (cliqueToMulticoloredClique_mem_iff x).symm⟩

/-- `Clique` FPT-reduces to `MulticoloredClique` preserving the parameter `k`. -/
theorem fptReducible_clique_multicoloredClique :
    FPTReducible encCliqueInstance encMulticoloredClique (·.m) (·.k) Clique MulticoloredClique :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToMulticoloredClique
    (h := id) (fun _ => by simp [cliqueToMulticoloredClique])
    fun x => (cliqueToMulticoloredClique_mem_iff x).symm

/-- **Multicolored Clique is `W[1]`-hard**. -/
theorem multicoloredClique_wHard : WHard 1 encMulticoloredClique (·.k) MulticoloredClique :=
  Clique_wHard.trans fptReducible_clique_multicoloredClique

/-- **Multicolored Clique is `NP`-hard**. -/
theorem multicoloredClique_npHard : NPHard encMulticoloredClique MulticoloredClique :=
  Clique_npHard.trans polyTimeReducible_clique_multicoloredClique

/-! ### 3. Reduction from `MulticoloredClique` to `Clique` (`∈ W[1]` and `∈ NP`) -/

/-- Filter vertices of `x.graph` to colors `< x.k` and retain only edges between distinct color
classes. -/
@[expose] def multicoloredCliqueToClique (x : MulticoloredCliqueInstance) : CliqueInstance :=
  ⟨⟨x.graph.vertices.filter fun v => decide (colorOf x.graph x.colors v < x.k),
    x.graph.edges.filter fun e =>
      decide (colorOf x.graph x.colors e.1 ≠ colorOf x.graph x.colors e.2)⟩,
    x.k⟩

/-- Correctness of `multicoloredCliqueToClique`. -/
theorem multicoloredCliqueToClique_mem_iff (x : MulticoloredCliqueInstance) :
    multicoloredCliqueToClique x ∈ Clique ↔ x ∈ MulticoloredClique := by
  classical
  rw [mem_multicoloredClique_iff_finset, multicoloredCliqueToClique, mem_Clique_iff]
  dsimp only
  set G' : Graph :=
    ⟨x.graph.vertices.filter fun v => decide (colorOf x.graph x.colors v < x.k),
      x.graph.edges.filter fun e =>
        decide (colorOf x.graph x.colors e.1 ≠ colorOf x.graph x.colors e.2)⟩
  have hadj_iff {u v : ℕ} :
      G'.toSimpleGraph.Adj u v ↔
        x.graph.toSimpleGraph.Adj u v ∧
          colorOf x.graph x.colors u ≠ colorOf x.graph x.colors v := by
    simp only [Graph.toSimpleGraph_adj, G', List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨hne, ⟨he, hcne⟩ | ⟨he, hcne⟩⟩
      · exact ⟨⟨hne, Or.inl he⟩, hcne⟩
      · exact ⟨⟨hne, Or.inr he⟩, hcne.symm⟩
    · rintro ⟨⟨hne, he | he⟩, hcne⟩
      · exact ⟨hne, Or.inl ⟨he, hcne⟩⟩
      · exact ⟨hne, Or.inr ⟨he, hcne.symm⟩⟩
  constructor
  · rintro ⟨S, hSV', hclq, hcard⟩
    have hSV : ∀ v ∈ S, v ∈ x.graph.vertices := fun v hv =>
      (List.mem_filter.1 (hSV' v hv)).1
    have hScol : ∀ v ∈ S, colorOf x.graph x.colors v < x.k := fun v hv =>
      decide_eq_true_iff.1 (List.mem_filter.1 (hSV' v hv)).2
    have hinj : Set.InjOn (colorOf x.graph x.colors) ↑S := by
      intro u hu v hv hce
      by_contra hne
      exact (hadj_iff.1 (hclq hu hv hne)).2 hce
    refine ⟨S, hSV, ⟨fun u hu v hv huv => (hadj_iff.1 (hclq hu hv huv)).1, hcard⟩, ?_⟩
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro c hc
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hc
      exact Finset.mem_range.2 (hScol v hv)
    · rw [Finset.card_image_of_injOn hinj, hcard, Finset.card_range]
  · rintro ⟨S, hSV, ⟨hclq, hcard⟩, himg⟩
    have hScol : ∀ v ∈ S, colorOf x.graph x.colors v < x.k := by
      intro v hv
      have hc : colorOf x.graph x.colors v ∈ Finset.range x.k :=
        himg ▸ Finset.mem_image_of_mem _ hv
      exact Finset.mem_range.1 hc
    have hSV' : ∀ v ∈ S, v ∈ G'.vertices := fun v hv =>
      List.mem_filter.2 ⟨hSV v hv, decide_eq_true (hScol v hv)⟩
    have hinj : Set.InjOn (colorOf x.graph x.colors) ↑S := by
      have hcard_img : (S.image (colorOf x.graph x.colors)).card = S.card := by
        rw [himg, Finset.card_range, hcard]
      exact Finset.injOn_of_card_image_eq hcard_img
    refine ⟨S, hSV', ?_, hcard⟩
    intro u hu v hv huv
    exact hadj_iff.2 ⟨hclq hu hv huv, fun hce => huv (hinj hu hv hce)⟩

/-- Polynomial-time certificate for `multicoloredCliqueToClique`. -/
@[fun_prop]
theorem computableInPolyTime_multicoloredCliqueToClique :
    ComputableInPolyTime multicoloredCliqueToClique encMulticoloredClique encCliqueInstance := by
  have hv : ComputableInPolyTime
      (fun x : MulticoloredCliqueInstance =>
        x.graph.vertices.filter fun v => decide (colorOf x.graph x.colors v < x.k))
      encMulticoloredClique (encList encNat) := by
    refine filterWithInput (by fun_prop) ?_
    let E1 := encPair encMulticoloredClique encNat
    have hx1 : ComputableInPolyTime (fun p : MulticoloredCliqueInstance × ℕ => p.1)
        E1 encMulticoloredClique := fst _ _
    have hc := computableInPolyTime_colorOf_comp (enc := E1)
      (G := fun p : MulticoloredCliqueInstance × ℕ => p.1.graph)
      (cs := fun p : MulticoloredCliqueInstance × ℕ => p.1.colors)
      (v := fun p : MulticoloredCliqueInstance × ℕ => p.2)
      (encMulticoloredClique_graph_polyTime hx1)
      (encMulticoloredClique_colors_polyTime hx1) (snd _ _)
    exact binary_lt' hc (encMulticoloredClique_k_polyTime hx1)
  have he : ComputableInPolyTime
      (fun x : MulticoloredCliqueInstance =>
        x.graph.edges.filter fun e =>
          decide (colorOf x.graph x.colors e.1 ≠ colorOf x.graph x.colors e.2))
      encMulticoloredClique (encList (encPair encNat encNat)) := by
    refine filterWithInput (by fun_prop) ?_
    let E2 := encPair encMulticoloredClique (encPair encNat encNat)
    have hx2 : ComputableInPolyTime (fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.1)
        E2 encMulticoloredClique := fst _ _
    have hc1 := computableInPolyTime_colorOf_comp (enc := E2)
      (G := fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.1.graph)
      (cs := fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.1.colors)
      (v := fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.2.1)
      (encMulticoloredClique_graph_polyTime hx2)
      (encMulticoloredClique_colors_polyTime hx2) ((fst _ _).comp (snd _ _))
    have hc2 := computableInPolyTime_colorOf_comp (enc := E2)
      (G := fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.1.graph)
      (cs := fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.1.colors)
      (v := fun p : MulticoloredCliqueInstance × (ℕ × ℕ) => p.2.2)
      (encMulticoloredClique_graph_polyTime hx2)
      (encMulticoloredClique_colors_polyTime hx2) ((snd _ _).comp (snd _ _))
    exact decide_ne hc1 hc2
  unfold multicoloredCliqueToClique
  exact encCliqueInstance_mk_polyTime (encGraph_mk_polyTime hv he) (by fun_prop)

/-- `MulticoloredClique` reduces to `Clique` in polynomial time. -/
theorem polyTimeReducible_multicoloredClique_clique :
    PolyTimeReducible encMulticoloredClique encCliqueInstance MulticoloredClique Clique :=
  ⟨multicoloredCliqueToClique, computableInPolyTime_multicoloredCliqueToClique,
    fun x => (multicoloredCliqueToClique_mem_iff x).symm⟩

/-- `MulticoloredClique` FPT-reduces to `Clique` preserving the parameter `k`. -/
theorem fptReducible_multicoloredClique_clique :
    FPTReducible encMulticoloredClique encCliqueInstance (·.k) (·.m) MulticoloredClique Clique :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_multicoloredCliqueToClique
    (h := id) (fun _ => by simp [multicoloredCliqueToClique])
    fun x => (multicoloredCliqueToClique_mem_iff x).symm

/-- **Multicolored Clique belongs to `W[1]`**. -/
theorem multicoloredClique_mem_W : MulticoloredClique ∈ W 1 encMulticoloredClique (·.k) :=
  fptReducible_multicoloredClique_clique.mem_W Clique_mem_W

/-- **Multicolored Clique belongs to `NP`**. -/
theorem multicoloredClique_mem_NP : MulticoloredClique ∈ NP encMulticoloredClique :=
  polyTimeReducible_multicoloredClique_clique.mem_NP Clique.mem_NP

/-- **Multicolored Clique is `NP`-complete**. -/
theorem multicoloredClique_npComplete : NPComplete encMulticoloredClique MulticoloredClique :=
  ⟨multicoloredClique_mem_NP, multicoloredClique_npHard⟩

end Cslib.Complexity
