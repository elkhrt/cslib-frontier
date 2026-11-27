/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Evaluation
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.SetCover

import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Membership of Set Cover and Dominating Set in `W[2]`

Unweighted Set Cover (`Cslib.Complexity.SetCover`) and Dominating Set
(`Cslib.Complexity.DominatingSet`), each parameterized by target solution cardinality `k`, belong
to the second level `W[2]` of the Downey–Fellows `W`-hierarchy.

For a set system `S = (U, 𝒮)` with `m = |𝒮|`, `setCoverToWCS` constructs in polynomial time an
`m`-input Boolean circuit of weft at most `2` and depth at most `2` consisting of one disjunction
gate over `{i < m : u ∈ 𝒮ᵢ}` for each `u ∈ U` fed into a single output conjunction gate, paired
with clamped Hamming weight `min k m`. Since supersets of a cover remain covers, `S` admits a
cover of cardinality at most `k` if and only if the circuit has a satisfying assignment of exact
weight `min k m`, yielding `SetCover ∈ W 2 encSetCover Prod.snd`. Reducing a graph `(G, k)` to the
closed-neighborhood set system `(V, {N[v] : v ∈ V})` (for `k ≤ |V|`) then yields
`DominatingSet ∈ W 2 encDominatingSet DominatingSetInstance.bound`.

## Main definitions

* `Cslib.Complexity.setCoverToWCS`: polynomial-time fpt-reduction from `SetCover` to `WCS 2 2`.

## Main results

* `Cslib.Complexity.setCoverToWCS_mem_iff`: exact decision preservation of `setCoverToWCS`.
* `Cslib.Complexity.computableInPolyTime_setCoverToWCS`: polynomial-time computability of
  `setCoverToWCS`.
* `Cslib.Complexity.SetCover_mem_W`: `SetCover ∈ W 2 encSetCover Prod.snd`.
* `Cslib.Complexity.DominatingSet_mem_W`:
  `DominatingSet ∈ W 2 encDominatingSet DominatingSetInstance.bound`.
-/

public section

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private def coveringIndices (S : SetSystem) (u : ℕ) : List ℕ :=
  (List.range S.sets.length).filter fun i => decide (u ∈ S.sets.getD i [])

private def setCoverGates (S : SetSystem) : List (Unbounded.Op × List ℕ) :=
  let m := S.sets.length
  S.ground.map (fun u =>
    let cov := coveringIndices S u
    (Unbounded.Op.or cov.length, cov)) ++
  [(Unbounded.Op.and S.ground.length, (List.range S.ground.length).map (m + ·))]

private def setCoverCircuitCode (S : SetSystem) : List (Unbounded.Op × List ℕ) × List ℕ :=
  (setCoverGates S, [S.sets.length + S.ground.length])

private theorem lt_of_mem_coveringIndices {S : SetSystem} {u i : ℕ}
    (hi : i ∈ coveringIndices S u) : i < S.sets.length :=
  List.mem_range.mp (List.mem_filter.mp hi).1

private theorem isSome_ofCode_setCoverCircuitCode (S : SetSystem) :
    (Circuit.ofCode S.sets.length 1 (setCoverCircuitCode S) :
      Option (Circuit Unbounded.signature S.sets.length 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨?_, rfl, ?_⟩
  · rw [setCoverCircuitCode, setCoverGates, Program.isCodeFrom_append]
    refine ⟨Program.isCodeFrom_of_forall (List.forall_mem_map.mpr fun _ _ =>
        ⟨rfl, fun _ hi => lt_of_mem_coveringIndices hi⟩),
      Program.isCodeFrom_of_forall (List.forall_mem_singleton.mpr ⟨by simp,
        List.forall_mem_map.mpr fun j hj => ?_⟩)⟩
    simp only [List.mem_range, List.length_map] at hj ⊢
    omega
  · simp [setCoverCircuitCode, setCoverGates]

private def setCoverCircuit (S : SetSystem) : Circuit Unbounded.signature S.sets.length 1 :=
  (Circuit.ofCode S.sets.length 1 (setCoverCircuitCode S)).get
    (isSome_ofCode_setCoverCircuitCode S)

private theorem code_setCoverCircuit (S : SetSystem) :
    (setCoverCircuit S).code = setCoverCircuitCode S :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

private theorem eval_setCoverCircuit (S : SetSystem) (x : BitString S.sets.length) :
    (setCoverCircuit S).eval Unbounded.interpretation x 0 = true ↔
      S.IsCover (Finset.univ.filter fun i : Fin S.sets.length => x i = true) := by
  have hout : ((setCoverCircuit S).outputs 0).toNat = S.sets.length + S.ground.length :=
    congrArg (fun c => c.2.headD 0) (code_setCoverCircuit S)
  rw [Circuit.eval_eq_getD _ _ false, hout, code_setCoverCircuit]
  dsimp only [setCoverCircuitCode, setCoverGates]
  rw [evalCode_append]
  set lx := List.ofFn x
  have hlx : lx.length = S.sets.length := List.length_ofFn
  have hlayer1 : evalCode Unbounded.interpretation false lx
      (S.ground.map fun u => (Unbounded.Op.or (coveringIndices S u).length, coveringIndices S u)) =
      lx ++ S.ground.map fun u => (coveringIndices S u).any fun i => lx.getD i false := by
    rw [evalCode_layer]
    · congr 1
      rw [List.map_map]
      refine List.map_congr_left fun u _ => ?_
      dsimp only [Function.comp_apply]
      rw [Unbounded.interpretation_or, Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true,
        Fin.exists_iff]
      refine ⟨fun ⟨j, hj, htrue⟩ => ?_, fun ⟨i, hi, htrue⟩ => ?_⟩
      · rw [List.getElem?_eq_getElem hj, Option.elim_some] at htrue
        exact ⟨(coveringIndices S u)[j]'hj, List.getElem_mem hj, htrue⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hi
        exact ⟨j, hj, by rw [List.getElem?_eq_getElem hj, Option.elim_some]; exact htrue⟩
    · exact List.forall_mem_map.mpr fun _ _ _ hi => hlx ▸ lt_of_mem_coveringIndices hi
  rw [hlayer1, evalCode_layer]
  · have hlen1 : (lx ++ S.ground.map fun u =>
        (coveringIndices S u).any fun i => lx.getD i false).length =
        S.sets.length + S.ground.length := by simp [hlx]
    rw [← hlen1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [List.map_singleton, List.getD_cons_zero, Unbounded.interpretation_and,
      decide_eq_true_eq]
    rw [SetSystem.IsCover, List.forall_mem_iff_getElem, Fin.forall_iff]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    have hj' : j < S.ground.length := by simpa using hj
    have hget_rhs : (lx ++ S.ground.map fun u =>
        (coveringIndices S u).any fun i => lx.getD i false).getD (S.sets.length + j) false =
        (coveringIndices S S.ground[j]).any fun i => lx.getD i false := by
      rw [← hlx, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp [hj']), Option.getD_some, List.getElem_map]
    rw [List.getElem?_eq_getElem (by simp [hj']), Option.elim_some, List.getElem_map,
      List.getElem_range, hget_rhs]
    simp only [List.any_eq_true, coveringIndices, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, ⟨hilt, hmem⟩, hxi⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some] at hmem
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlx ▸ hilt),
        Option.getD_some, List.getElem_ofFn] at hxi
      exact ⟨⟨i, hilt⟩, hxi, hmem⟩
    · rintro ⟨i, hxi, hmem⟩
      have hilt' : i.1 < lx.length := hlx.symm ▸ i.isLt
      refine ⟨i.1, ⟨i.isLt, by
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]⟩, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt',
        Option.getD_some, List.getElem_ofFn]
      exact hxi
  · refine List.forall_mem_singleton.mpr (List.forall_mem_map.mpr fun j hj => ?_)
    simp only [List.mem_range, List.length_append, hlx, List.length_map] at hj ⊢
    omega

private theorem weft_setCoverCircuit_le (S : SetSystem) : (setCoverCircuit S).weft ≤ 2 := by
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  rw [code_setCoverCircuit] at hv
  dsimp only [setCoverCircuitCode, setCoverGates] at hv
  rw [evalCode_append] at hv
  exact le_of_mem_evalCode_depth_layer _ _ _
    (List.forall_mem_singleton.mpr (List.forall_mem_map.mpr fun j hj => by
      simp only [List.mem_range, length_evalCode, List.length_replicate, List.length_map] at hj ⊢
      omega))
    (le_of_mem_evalCode_depth_layer _ _ _
      (List.forall_mem_map.mpr fun _ _ _ hi => by simpa using lt_of_mem_coveringIndices hi)
      (fun _ h => (List.eq_of_mem_replicate h).le)
      (List.forall_mem_map.mpr fun _ _ => largeGateCost_le_one _))
    (List.forall_mem_singleton.mpr (largeGateCost_le_one _)) v hv

private theorem depth_setCoverCircuit_le (S : SetSystem) : (setCoverCircuit S).depth ≤ 2 := by
  rw [← Circuit.depthWith_one]
  refine Circuit.depthWith_le_of_evalCode (fun _ => 1) _ fun v hv => ?_
  rw [code_setCoverCircuit] at hv
  dsimp only [setCoverCircuitCode, setCoverGates] at hv
  rw [evalCode_append] at hv
  exact le_of_mem_evalCode_depth_layer (σ := Unbounded.signature) (fun _ => 1) _ _
    (List.forall_mem_singleton.mpr (List.forall_mem_map.mpr fun j hj => by
      simp only [List.mem_range, length_evalCode, List.length_replicate, List.length_map] at hj ⊢
      omega))
    (le_of_mem_evalCode_depth_layer (σ := Unbounded.signature) (fun _ => 1) _ _
      (List.forall_mem_map.mpr fun _ _ _ hi => by simpa using lt_of_mem_coveringIndices hi)
      (fun _ h => (List.eq_of_mem_replicate h).le)
      (List.forall_mem_map.mpr fun _ _ => le_rfl))
    (List.forall_mem_singleton.mpr le_rfl) v hv

/-- Polynomial-time fpt-reduction from `SetCover` to weft-`2`, depth-`2` Weighted Circuit
Satisfiability (`WCS 2 2`). -/
def setCoverToWCS (p : SetSystem × ℕ) : WCSInstance 2 2 :=
  ⟨⟨⟨p.1.sets.length, setCoverCircuit p.1⟩,
    weft_setCoverCircuit_le p.1, depth_setCoverCircuit_le p.1⟩,
    min p.2 p.1.sets.length⟩

/-- `setCoverToWCS p ∈ WCS 2 2` if and only if `p ∈ SetCover`. -/
theorem setCoverToWCS_mem_iff (p : SetSystem × ℕ) :
    setCoverToWCS p ∈ WCS 2 2 ↔ p ∈ SetCover := by
  rcases p with ⟨S, k⟩
  simp only [setCoverToWCS, mem_WCS, Circuit.SatisfiableWithWeight, eval_setCoverCircuit,
    mem_SetCover_iff]
  constructor
  · rintro ⟨x, hwt, hcov⟩
    exact ⟨Finset.univ.filter fun i => x i = true, hcov, hwt.trans_le (Nat.min_le_left _ _)⟩
  · rintro ⟨C, hcov, hcard⟩
    have hle : C.card ≤ min k S.sets.length :=
      le_min hcard ((Finset.card_le_univ C).trans_eq (Fintype.card_fin _))
    have hmin_le : min k S.sets.length ≤ (Finset.univ : Finset (Fin S.sets.length)).card := by
      simp
    obtain ⟨T, hCT, -, hTcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ C) hle hmin_le
    let x : BitString S.sets.length := fun i => decide (i ∈ T)
    have hfilt : (Finset.univ.filter fun i : Fin S.sets.length => x i = true) = T := by
      ext i; simp [x]
    refine ⟨x, ?_, fun u hu => let ⟨i, hi, hui⟩ := hcov u hu; ⟨i, hfilt ▸ hCT hi, hui⟩⟩
    change (Finset.univ.filter fun i : Fin S.sets.length => x i = true).card = _
    rw [hfilt, hTcard]

private theorem computableInPolyTime_setCoverCircuitCode :
    ComputableInPolyTime setCoverCircuitCode encSetSystem (Circuit.encCode Unbounded.encOp) := by
  have hb := ComputableInPolyTime.unary_to_binary
  have hcov : ComputableInPolyTime (fun q : SetSystem × ℕ => coveringIndices q.1 q.2)
      (encPair encSetSystem encNat) (encList encUnary) := by
    unfold coveringIndices; fun_prop
  have hcov_bin : ComputableInPolyTime (fun q : SetSystem × ℕ => coveringIndices q.1 q.2)
      (encPair encSetSystem encNat) (encList encNat) := by
    simpa only [Function.comp_def, List.map_id'] using (ComputableInPolyTime.map hb).comp hcov
  have hor : ComputableInPolyTime
      (fun S : SetSystem => S.ground.map fun u =>
        ((Unbounded.Op.or (coveringIndices S u).length, coveringIndices S u) :
          Unbounded.Op × List ℕ))
      encSetSystem (encList (Circuit.encGate Unbounded.encOp)) :=
    mapWithInput computableInPolyTime_setSystemGround
      ((Unbounded.computableInPolyTime_or.comp ((length_list encUnary).comp hcov)).prod hcov_bin)
  have hglen : ComputableInPolyTime (fun S : SetSystem => S.ground.length) encSetSystem encUnary :=
    by fun_prop
  have hand : ComputableInPolyTime
      (fun S : SetSystem => [((Unbounded.Op.and S.ground.length,
        (List.range S.ground.length).map (S.sets.length + ·)) : Unbounded.Op × List ℕ)])
      encSetSystem (encList (Circuit.encGate Unbounded.encOp)) :=
    .cons' ((Unbounded.computableInPolyTime_and.comp hglen).prod
      ((ComputableInPolyTime.range.comp hglen).mapWithInput (hb.comp (by fun_prop)))) (.const [])
  unfold setCoverCircuitCode setCoverGates
  exact (hor.listAppend' hand).prod (.cons' (hb.comp (by fun_prop)) (.const []))

/-- `setCoverToWCS` is computable in polynomial time. -/
theorem computableInPolyTime_setCoverToWCS :
    ComputableInPolyTime setCoverToWCS encSetCover (encWCS 2 2) := by
  have hc := computableInPolyTime_setCoverCircuitCode
  have hm_bin : ComputableInPolyTime (fun p : SetSystem × ℕ => p.1.sets.length)
      encSetCover encNat :=
    unary_to_binary.comp (by fun_prop)
  have hmin : ComputableInPolyTime (fun p : SetSystem × ℕ => min p.2 p.1.sets.length)
      encSetCover encNat :=
    (ite' (binary_le' (snd encSetSystem encNat) hm_bin) (snd encSetSystem encNat) hm_bin).of_enc_eq
      fun p => congrArg encNat <| by
        by_cases h : p.2 ≤ p.1.sets.length
        · simp [h]
        · simp [h, le_of_not_ge h]
  refine (by fun_prop : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        ((p.1.sets.length, setCoverCircuitCode p.1), min p.2 p.1.sets.length))
      encSetCover
      (encPair (encPair encUnary (Circuit.encCode Unbounded.encOp)) encNat)).of_enc_eq
    fun p => by
      simp only [setCoverToWCS, encWCS_apply, encPair_apply, encWeftCircuit_apply,
        Circuit.encCircuit_apply, code_setCoverCircuit]

/-- Unweighted Set Cover parameterized by solution cardinality belongs to `W[2]`. -/
theorem SetCover_mem_W : SetCover ∈ W 2 encSetCover Prod.snd :=
  ⟨2, FPTReducible.of_computableInPolyTime computableInPolyTime_setCoverToWCS (h := id)
    (fun p => Nat.min_le_left p.2 _) fun p => (setCoverToWCS_mem_iff p).symm⟩

private def domSetToSetSystem (G : Graph) : SetSystem :=
  ⟨G.distinctVertices,
    G.distinctVertices.map fun v => v :: G.distinctVertices.filter (G.adjBool v)⟩

/-- Dominating Set parameterized by solution cardinality belongs to `W[2]`. -/
theorem DominatingSet_mem_W :
    DominatingSet ∈ W 2 encDominatingSet DominatingSetInstance.bound := by
  let red (x : DominatingSetInstance) : SetSystem × ℕ :=
    if decide (x.bound ≤ x.graph.distinctVertices.length) then
      (domSetToSetSystem x.graph, x.bound)
    else
      (⟨[0], []⟩, 0)
  have hV := Graph.computableInPolyTime_distinctVertices
  have hsys : ComputableInPolyTime domSetToSetSystem encGraph encSetSystem := by
    unfold domSetToSetSystem; fun_prop
  have hlen : ComputableInPolyTime
      (fun x : DominatingSetInstance => x.graph.distinctVertices.length)
      encDominatingSet encNat := unary_to_binary.comp (by fun_prop)
  have hred : ComputableInPolyTime red encDominatingSet encSetCover :=
    ite' (binary_le' (by fun_prop) hlen)
      ((hsys.comp (by fun_prop)).prod (by fun_prop))
      (const ((⟨[0], []⟩, 0) : SetSystem × ℕ))
  refine (FPTReducible.of_computableInPolyTime hred (h := id)
    (fun x => by dsimp only [red]; split_ifs <;> simp) fun ⟨G, k⟩ => ?_).mem_W SetCover_mem_W
  rw [mem_DominatingSet_iff_exists_card_le]
  have hcard_dv : G.distinctVertices.length = G.vertices.toFinset.card := by
    rw [← List.toFinset_card_of_nodup G.nodup_distinctVertices]
    congr 1; ext v; simp [Graph.mem_distinctVertices]
  dsimp only [red]
  by_cases hk : k ≤ G.distinctVertices.length
  · simp only [decide_eq_true hk, ↓reduceIte, hcard_dv ▸ hk, true_and, mem_SetCover_iff]
    constructor
    · rintro ⟨S, hSV, hdom, hScard⟩
      let C : Finset (Fin (domSetToSetSystem G).sets.length) :=
        Finset.univ.filter fun i =>
          (G.distinctVertices[i.1]'(by simpa [domSetToSetSystem] using i.isLt)) ∈ S
      have hCcard : C.card ≤ S.card :=
        Finset.card_le_card_of_injOn
          (fun i => G.distinctVertices[i.1]'(by simpa [domSetToSetSystem] using i.isLt))
          (fun _ hi => (Finset.mem_filter.mp hi).2)
          fun _ _ _ _ hij => Fin.ext (G.nodup_distinctVertices.getElem_inj_iff.mp hij)
      refine ⟨C, fun u hu => ?_, hCcard.trans hScard⟩
      change u ∈ G.distinctVertices at hu
      rcases hdom u (Graph.mem_distinctVertices.mp hu) with huS | ⟨s, hsS, hadj⟩
      · obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hu
        exact ⟨⟨idx, by simp [domSetToSetSystem, hidx]⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hget] using huS⟩,
          by simp [domSetToSetSystem, hget]⟩
      · obtain ⟨idx, hidx, hget⟩ :=
          List.mem_iff_getElem.mp (Graph.mem_distinctVertices.mpr (hSV s hsS))
        exact ⟨⟨idx, by simp [domSetToSetSystem, hidx]⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hget] using hsS⟩,
          by simp [domSetToSetSystem, hget, hu, hadj.symm]⟩
    · rintro ⟨C, hcov, hCcard⟩
      let S : Finset ℕ := C.image fun i =>
        G.distinctVertices[i.1]'(by simpa [domSetToSetSystem] using i.isLt)
      refine ⟨S, fun v hv => ?_, fun v hv => ?_, Finset.card_image_le.trans hCcard⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
        exact Graph.mem_distinctVertices.mp (List.getElem_mem _)
      · obtain ⟨i, hiC, hmem⟩ := hcov v (Graph.mem_distinctVertices.mpr hv)
        have hi' : i.1 < G.distinctVertices.length := by simpa [domSetToSetSystem] using i.isLt
        let s := G.distinctVertices[i.1]'hi'
        have hsS : s ∈ S := Finset.mem_image_of_mem _ hiC
        change v ∈ (G.distinctVertices.map fun w =>
          w :: G.distinctVertices.filter (G.adjBool w))[i.1] at hmem
        simp only [List.getElem_map, List.mem_cons, List.mem_filter,
          Graph.adjBool_eq_true_iff] at hmem
        exact hmem.elim (fun e => Or.inl (e ▸ hsS)) fun ⟨_, ha⟩ => Or.inr ⟨s, hsS, ha.symm⟩
  · simp only [decide_eq_false hk, Bool.false_eq_true, ↓reduceIte, hcard_dv ▸ hk, false_and,
      mem_SetCover_iff, false_iff, not_exists, not_and]
    intro C hcov
    obtain ⟨i, -, -⟩ := hcov 0 List.mem_cons_self
    exact Fin.elim0 i

end Cslib.Complexity
