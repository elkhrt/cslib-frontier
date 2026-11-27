module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.EUThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.CircleOneTwoDomination.Proofs

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# NP-Completeness of `[1, 2]`-Domination on Circle Graphs

Formalizes the `[1, 2]`-domination decision problem on circle graphs (`CircleOneTwoDomination`)
under the binary graph encoding `encDominatingSet`, proves membership in `NP` via canonical
`[0, 2|V|)` chord placements, and proves NP-completeness via a native multi-tape Turing-machine
polynomial-time reduction from `EUThreeSAT`.

## Main definitions

* `Cslib.Complexity.CircleOneTwoDomination`: the decision problem of circle graphs admitting a
  `[1, 2]`-dominating set of cardinality at most `k`.
* `Cslib.Complexity.toCircleOneTwoDomination`: the guarded polynomial-time reduction from
  `EUThreeSAT`.

## Main results

* `Cslib.Complexity.CircleOneTwoDomination.mem_NP`: `CircleOneTwoDomination ∈ NP encDominatingSet`.
* `Cslib.Complexity.computableInPolyTime_toCircleOneTwoDomination`: native multi-tape TM
  polynomial-time computability of the reduction.
* `Cslib.Complexity.CircleOneTwoDomination_npComplete`:
  `NPComplete encDominatingSet CircleOneTwoDomination`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Complexity.CircleOneTwoDomination Turing.MultiTapeTM
  ComputableInPolyTime

/-! ### 1. Decision Problem & NP Membership -/

/-- The `[1, 2]`-domination decision problem on circle graphs: instances `(G, k)` where
`G.induced` is a circle graph admitting a `[1, 2]`-dominating set of at most `k` declared
vertices. -/
def CircleOneTwoDomination : Set DominatingSetInstance :=
  {x | IsCircleChordGraph x.graph.induced ∧
    ∃ D : Finset ℕ, (∀ v ∈ D, v ∈ x.graph.vertices) ∧
      (∀ v ∈ x.graph.vertices, v ∉ D →
        1 ≤ (D.filter fun u ↦ x.graph.adjBool v u = true).card ∧
        (D.filter fun u ↦ x.graph.adjBool v u = true).card ≤ 2) ∧
      D.card ≤ x.bound}

namespace CircleOneTwoDomination

/-- Executable check verifying a witness `(D, chords)` for `CircleOneTwoDomination`:
`D` is a duplicate-free list of at most `x.bound` declared vertices `[1, 2]`-dominating `x.graph`,
and `chords` assigns each distinct vertex `v_i` in `x.graph.distinctVertices` a chord `(l_i, r_i)`
with `l_i < r_i < 2 * n`, pairwise distinct endpoints, and alternating chords iff adjacent. -/
def verify (y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) : Bool :=
  let G := y.1.graph
  let V := G.distinctVertices
  let D := y.2.1
  let chords := y.2.2
  let P := V.zip chords
  D.all (fun v ↦ decide (v ∈ V)) &&
  D.all (fun v ↦ decide (D.count v = 1)) &&
  decide (D.length ≤ y.1.bound) &&
  V.all (fun v ↦ decide (v ∈ D) ||
    (let c := D.countP (fun u ↦ G.adjBool v u)
     decide (1 ≤ c) && decide (c ≤ 2))) &&
  decide (chords.length = V.length) &&
  chords.all (fun c ↦ decide (c.1 < c.2) && decide (c.2 < 2 * V.length)) &&
  P.all (fun p ↦ P.all (fun q ↦
    decide (p.1 = q.1) ||
    (decide (p.2.1 ≠ q.2.1) && decide (p.2.1 ≠ q.2.2) &&
     decide (p.2.2 ≠ q.2.1) && decide (p.2.2 ≠ q.2.2) &&
     decide (G.adjBool p.1 q.1 =
       chordsAlternateBool p.2.1 p.2.2 q.2.1 q.2.2))))

private theorem computableInPolyTime_chordsAlternateBool :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ chordsAlternateBool p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encNat encNat) (encPair encNat encNat)) encBool := by
  simp_rw [chordsAlternateBool_eq]
  fun_prop

/-- The verifier `CircleOneTwoDomination.verify` runs in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_verify :
    ComputableInPolyTime verify
      (encPair encDominatingSet (encPair (encList encNat) (encList (encPair encNat encNat))))
      encBool := by
  let encW := encPair (encList encNat) (encList (encPair encNat encNat))
  let encY := encPair encDominatingSet encW
  let encP := encPair encNat (encPair encNat encNat)
  have hG : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.1.graph) encY encGraph := by fun_prop
  have hV : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.1.graph.distinctVertices) encY (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp hG
  have hD : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.2.1) encY (encList encNat) := by fun_prop
  have hC : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.2.2) encY (encList (encPair encNat encNat)) := by fun_prop
  have hP : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.1.graph.distinctVertices.zip y.2.2) encY (encList encP) :=
    (ComputableInPolyTime.zip encNat (encPair encNat encNat)).comp (hV.prod hC)
  have h1 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.2.1.all (fun v ↦ decide (v ∈ y.1.graph.distinctVertices))) encY encBool :=
    allWithInput hD (by fun_prop)
  have h2 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.2.1.all (fun v ↦ decide (y.2.1.count v = 1))) encY encBool :=
    allWithInput hD (by fun_prop)
  have h3 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      decide (y.2.1.length ≤ y.1.bound)) encY encBool := by fun_prop
  have h4 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.1.graph.distinctVertices.all (fun v ↦ decide (v ∈ y.2.1) ||
        (let c := y.2.1.countP (fun u ↦ y.1.graph.adjBool v u)
         decide (1 ≤ c) && decide (c ≤ 2)))) encY encBool := by
    refine allWithInput hV ?_
    have hmem : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × ℕ ↦
          decide (p.2 ∈ p.1.2.1)) (encPair encY encNat) encBool := by fun_prop
    have hcnt : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × ℕ ↦
          p.1.2.1.countP (fun u ↦ p.1.1.graph.adjBool p.2 u))
        (encPair encY encNat) encUnary :=
      countPWithInput (hD.comp (fst encY encNat)) (by fun_prop)
    have h1le : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × ℕ ↦
          decide (1 ≤ p.1.2.1.countP (fun u ↦ p.1.1.graph.adjBool p.2 u)))
        (encPair encY encNat) encBool :=
      unary_le' (const 1) hcnt
    have hle2 : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × ℕ ↦
          decide (p.1.2.1.countP (fun u ↦ p.1.1.graph.adjBool p.2 u) ≤ 2))
        (encPair encY encNat) encBool :=
      unary_le' hcnt (const 2)
    exact bool_or' hmem (bool_and' h1le hle2)
  have h5 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      decide (y.2.2.length = y.1.graph.distinctVertices.length)) encY encBool := by fun_prop
  have h6 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      y.2.2.all (fun c ↦ decide (c.1 < c.2) &&
        decide (c.2 < 2 * y.1.graph.distinctVertices.length))) encY encBool := by
    refine allWithInput hC ?_
    have hlt1 : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × (ℕ × ℕ) ↦
          decide (p.2.1 < p.2.2)) (encPair encY (encPair encNat encNat)) encBool := by fun_prop
    have hlen2 : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × (ℕ × ℕ) ↦
          2 * p.1.1.graph.distinctVertices.length)
        (encPair encY (encPair encNat encNat)) encNat :=
      unary_to_binary.comp (unary_mul' (const 2) (by fun_prop))
    have hlt2 : ComputableInPolyTime
        (fun p : (DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) × (ℕ × ℕ) ↦
          decide (p.2.2 < 2 * p.1.1.graph.distinctVertices.length))
        (encPair encY (encPair encNat encNat)) encBool :=
      binary_lt' (by fun_prop) hlen2
    exact bool_and' hlt1 hlt2
  have h7 : ComputableInPolyTime (fun y : DominatingSetInstance × (List ℕ × List (ℕ × ℕ)) ↦
      (y.1.graph.distinctVertices.zip y.2.2).all fun p ↦
        (y.1.graph.distinctVertices.zip y.2.2).all fun q ↦
          decide (p.1 = q.1) ||
          (decide (p.2.1 ≠ q.2.1) && decide (p.2.1 ≠ q.2.2) &&
           decide (p.2.2 ≠ q.2.1) && decide (p.2.2 ≠ q.2.2) &&
           decide (y.1.graph.adjBool p.1 q.1 =
             chordsAlternateBool p.2.1 p.2.2 q.2.1 q.2.2))) encY encBool := by
    refine allWithInput hP (allWithInput (hP.comp (fst encY encP)) ?_)
    have halt : ComputableInPolyTime
        (fun r : ((DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) ×
            (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ)) ↦
          chordsAlternateBool r.1.2.2.1 r.1.2.2.2 r.2.2.1 r.2.2.2)
        (encPair (encPair encY encP) encP) encBool :=
      computableInPolyTime_chordsAlternateBool.comp
        (show ComputableInPolyTime
          (fun r : ((DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) ×
              (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ)) ↦
            ((r.1.2.2.1, r.1.2.2.2), (r.2.2.1, r.2.2.2)))
          (encPair (encPair encY encP) encP)
          (encPair (encPair encNat encNat) (encPair encNat encNat)) by fun_prop)
    have hadj : ComputableInPolyTime
        (fun r : ((DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) ×
            (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ)) ↦
          r.1.1.1.graph.adjBool r.1.2.1 r.2.1)
        (encPair (encPair encY encP) encP) encBool := by fun_prop
    have heq_adj : ComputableInPolyTime
        (fun r : ((DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) ×
            (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ)) ↦
          decide (r.1.1.1.graph.adjBool r.1.2.1 r.2.1 =
            chordsAlternateBool r.1.2.2.1 r.1.2.2.2 r.2.2.1 r.2.2.2))
        (encPair (encPair encY encP) encP) encBool :=
      decide_eq' hadj halt
    have hne : ComputableInPolyTime
        (fun r : ((DominatingSetInstance × (List ℕ × List (ℕ × ℕ))) ×
            (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ)) ↦
          decide (r.1.2.2.1 ≠ r.2.2.1) && decide (r.1.2.2.1 ≠ r.2.2.2) &&
          decide (r.1.2.2.2 ≠ r.2.2.1) && decide (r.1.2.2.2 ≠ r.2.2.2))
        (encPair (encPair encY encP) encP) encBool := by fun_prop
    exact bool_or' (by fun_prop) (bool_and' hne heq_adj)
  unfold verify
  exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (bool_and' h1 h2) h3) h4) h5) h6) h7

private lemma nodup_of_forall_count_eq_one {l : List ℕ} (h : ∀ x ∈ l, l.count x = 1) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    have ha : a ∉ t := by
      intro hat
      have hc := h a List.mem_cons_self
      rw [List.count_cons_self] at hc
      have hpos : 0 < t.count a := List.count_pos_iff.mpr hat
      omega
    refine List.nodup_cons.mpr ⟨ha, ih fun x hx ↦ ?_⟩
    have hc := h x (List.mem_cons_of_mem _ hx)
    rw [List.count_cons_of_ne (by rintro rfl; exact ha hx)] at hc
    exact hc

private lemma countP_eq_card_filter_toFinset {D : List ℕ} (hnd : D.Nodup) (p : ℕ → Bool) :
    D.countP p = (D.toFinset.filter (fun u ↦ p u = true)).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter p)]
  congr 1; ext x; simp

private lemma length_encList_filter_le {l : List ℕ} (p : ℕ → Bool) :
    (encList encNat (l.filter p)).length ≤ (encList encNat l).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, encList_cons, List.length_append]
    split_ifs
    · simp only [encList_cons, List.length_append]; omega
    · omega

private lemma length_encList_selectDistinct_le {l : List ℕ} (m : List Bool) :
    (encList encNat (selectDistinct l m)).length ≤ (encList encNat l).length := by
  have hsublist : ∀ {s t : List ℕ}, s.Sublist t →
    (encList encNat s).length ≤ (encList encNat t).length := by
    intro s t hst
    induction hst with
    | slnil => exact le_rfl
    | cons a _ ih => simp only [encList_cons, List.length_append]; omega
    | cons_cons a _ ih => simp only [encList_cons, List.length_append]; omega
  refine hsublist ?_
  unfold selectDistinct
  have hfl : ((l.zipIdx.filter fun e ↦
      m.getD e.2 false && decide (l.idxOf e.1 = e.2)).map Prod.fst).Sublist
      (l.zipIdx.map Prod.fst) := (List.filter_sublist).map Prod.fst
  have hfst : ∀ (s : List ℕ) (k : ℕ), (s.zipIdx k).map Prod.fst = s := by
    intro s; induction s with
    | nil => intro _; rfl
    | cons a t ih => intro k; simp [List.zipIdx_cons, ih]
  rw [hfst] at hfl
  exact hfl

/-- `CircleOneTwoDomination` belongs to `NP` under `encDominatingSet`. -/
theorem mem_NP : CircleOneTwoDomination ∈ NP encDominatingSet := by
  classical
  let encW := encPair (encList encNat) (encList (encPair encNat encNat))
  let decW : Decoder encW :=
    Decoder.pair (Decoder.list Decoder.nat) (Decoder.list (Decoder.pair Decoder.nat Decoder.nat))
  let p : Polynomial ℕ :=
    Polynomial.C 12 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 1
  refine mem_NP_of_check (p := p) decW computableInPolyTime_verify ?_ ?_
  · -- Soundness
    rintro x ⟨D, chords⟩ hv
    simp only [verify, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨⟨⟨hDsub, hDcnt⟩, hDlen⟩, hDdom⟩, hclen⟩, hcbounds⟩, hcpairs⟩ := hv
    have hDnd : D.Nodup := nodup_of_forall_count_eq_one hDcnt
    let V := x.graph.distinctVertices
    have hcircle : IsCircleChordGraph x.graph.induced := by
      let lF : {v // v ∈ x.graph.vertices} → ℕ := fun v ↦
        (chords.getD (x.graph.vertexEquiv.symm v).1 (0, 0)).1
      let rF : {v // v ∈ x.graph.vertices} → ℕ := fun v ↦
        (chords.getD (x.graph.vertexEquiv.symm v).1 (0, 0)).2
      refine ⟨2 * V.length, lF, rF, ?_, ?_, ?_⟩
      · intro v
        have hi : (x.graph.vertexEquiv.symm v).1 < chords.length := by
          rw [hclen]; exact (x.graph.vertexEquiv.symm v).2
        have hmem : chords[(x.graph.vertexEquiv.symm v).1]'hi ∈ chords := List.getElem_mem hi
        have hget : chords.getD (x.graph.vertexEquiv.symm v).1 (0, 0) =
          chords[(x.graph.vertexEquiv.symm v).1]'hi :=
          List.getD_eq_getElem _ _ hi
        have hb := hcbounds _ hmem
        dsimp [lF, rF]; rw [hget]; exact hb
      · intro u v huv
        have hne_val : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
        have hiu : (x.graph.vertexEquiv.symm u).1 < V.length := (x.graph.vertexEquiv.symm u).2
        have hiv : (x.graph.vertexEquiv.symm v).1 < V.length := (x.graph.vertexEquiv.symm v).2
        have hpu_mem : (u.1, (lF u, rF u)) ∈ V.zip chords := by
          have hmem := List.getElem_mem (l := V.zip chords) (n := (x.graph.vertexEquiv.symm u).1)
            (by rw [List.length_zip, hclen, min_self]; exact hiu)
          have heq1 : V[(x.graph.vertexEquiv.symm u).1]'hiu = u.1 := by
            have := x.graph.vertexEquiv_apply (x.graph.vertexEquiv.symm u)
            simp only [Equiv.apply_symm_apply] at this
            dsimp only [V] at hiu ⊢; rw [List.getD_eq_getElem _ _ hiu] at this
            exact this.symm
          have heq2 : chords[(x.graph.vertexEquiv.symm u).1]'(hclen.symm ▸ hiu) = (lF u, rF u) := by
            dsimp [lF, rF]
            rw [List.getD_eq_getElem _ _ (hclen.symm ▸ hiu)]
          simpa [List.getElem_zip, heq1, heq2] using hmem
        have hpv_mem : (v.1, (lF v, rF v)) ∈ V.zip chords := by
          have hmem := List.getElem_mem (l := V.zip chords) (n := (x.graph.vertexEquiv.symm v).1)
            (by rw [List.length_zip, hclen, min_self]; exact hiv)
          have heq1 : V[(x.graph.vertexEquiv.symm v).1]'hiv = v.1 := by
            have := x.graph.vertexEquiv_apply (x.graph.vertexEquiv.symm v)
            simp only [Equiv.apply_symm_apply] at this
            dsimp only [V] at hiv ⊢; rw [List.getD_eq_getElem _ _ hiv] at this
            exact this.symm
          have heq2 : chords[(x.graph.vertexEquiv.symm v).1]'(hclen.symm ▸ hiv) = (lF v, rF v) := by
            dsimp [lF, rF]
            rw [List.getD_eq_getElem _ _ (hclen.symm ▸ hiv)]
          simpa [List.getElem_zip, heq1, heq2] using hmem
        rcases hcpairs _ hpu_mem _ hpv_mem with heq | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩
        · exact absurd heq hne_val
        · exact ⟨h1, h2, h3, h4⟩
      · intro u v huv
        have hne_val : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
        have hiu : (x.graph.vertexEquiv.symm u).1 < V.length := (x.graph.vertexEquiv.symm u).2
        have hiv : (x.graph.vertexEquiv.symm v).1 < V.length := (x.graph.vertexEquiv.symm v).2
        have hpu_mem : (u.1, (lF u, rF u)) ∈ V.zip chords := by
          have hmem := List.getElem_mem (l := V.zip chords) (n := (x.graph.vertexEquiv.symm u).1)
            (by rw [List.length_zip, hclen, min_self]; exact hiu)
          have heq1 : V[(x.graph.vertexEquiv.symm u).1]'hiu = u.1 := by
            have := x.graph.vertexEquiv_apply (x.graph.vertexEquiv.symm u)
            simp only [Equiv.apply_symm_apply] at this
            dsimp only [V] at hiu ⊢; rw [List.getD_eq_getElem _ _ hiu] at this
            exact this.symm
          have heq2 : chords[(x.graph.vertexEquiv.symm u).1]'(hclen.symm ▸ hiu) = (lF u, rF u) := by
            dsimp [lF, rF]; rw [List.getD_eq_getElem _ _ (hclen.symm ▸ hiu)]
          simpa [List.getElem_zip, heq1, heq2] using hmem
        have hpv_mem : (v.1, (lF v, rF v)) ∈ V.zip chords := by
          have hmem := List.getElem_mem (l := V.zip chords) (n := (x.graph.vertexEquiv.symm v).1)
            (by rw [List.length_zip, hclen, min_self]; exact hiv)
          have heq1 : V[(x.graph.vertexEquiv.symm v).1]'hiv = v.1 := by
            have := x.graph.vertexEquiv_apply (x.graph.vertexEquiv.symm v)
            simp only [Equiv.apply_symm_apply] at this
            dsimp only [V] at hiv ⊢; rw [List.getD_eq_getElem _ _ hiv] at this
            exact this.symm
          have heq2 : chords[(x.graph.vertexEquiv.symm v).1]'(hclen.symm ▸ hiv) = (lF v, rF v) := by
            dsimp [lF, rF]; rw [List.getD_eq_getElem _ _ (hclen.symm ▸ hiv)]
          simpa [List.getElem_zip, heq1, heq2] using hmem
        rcases hcpairs _ hpu_mem _ hpv_mem with heq | ⟨_, hadj_eq⟩
        · exact absurd heq hne_val
        · rw [Graph.induced_adj, ← Graph.adjBool_eq_true_iff, hadj_eq,
            chordsAlternateBool_eq_true_iff]
    refine ⟨hcircle, D.toFinset, fun v hv ↦
        Graph.mem_distinctVertices.mp (hDsub v (List.mem_toFinset.mp hv)), fun v hv hvD ↦ ?_, ?_⟩
    · rcases hDdom v (Graph.mem_distinctVertices.mpr hv) with hmem | hbounds
      · exact absurd (List.mem_toFinset.mpr hmem) hvD
      · have hcnt_eq : D.countP (fun u ↦ x.graph.adjBool v u) =
            (D.toFinset.filter fun u ↦ x.graph.adjBool v u = true).card := by
          rw [countP_eq_card_filter_toFinset hDnd]
        rw [← hcnt_eq]; exact hbounds
    · rw [List.toFinset_card_of_nodup hDnd]; exact hDlen
  · -- Completeness with quadratic length bound
    rintro x ⟨hcircle, Dset, hDsub, hDdom, hDcard⟩
    let V := x.graph.distinctVertices
    let D := V.filter (fun v ↦ decide (v ∈ Dset))
    obtain ⟨lF, rF, hlr, hdisj, hadj⟩ := exists_canonical_circleChordPlacement hcircle
    let chords : List (ℕ × ℕ) :=
      (List.finRange V.length).map fun i ↦ (lF (x.graph.vertexEquiv i), rF (x.graph.vertexEquiv i))
    refine ⟨(D, chords), ?_, ?_⟩
    · have hD_toFinset : D.toFinset = Dset := by
        ext v; simp only [D, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        exact ⟨fun h ↦ h.2, fun hv ↦ ⟨Graph.mem_distinctVertices.mpr (hDsub v hv), hv⟩⟩
      have hDnd : D.Nodup := x.graph.nodup_distinctVertices.filter _
      have hclen : chords.length = V.length := by simp [chords]
      have hcard_eq : Fintype.card {v // v ∈ x.graph.vertices} = V.length := by
        rw [Graph.card_vertexSubtype, Graph.length_distinctVertices]
      simp only [verify, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hclen⟩, ?_⟩, ?_⟩
      · intro v hv; exact (List.mem_filter.mp hv).1
      · intro v hv; exact (List.Nodup.count hDnd).trans (by simp [hv])
      · rw [← List.toFinset_card_of_nodup hDnd, hD_toFinset]; exact hDcard
      · intro v hv
        by_cases hvD : v ∈ Dset
        · exact Or.inl (List.mem_filter.mpr ⟨hv, decide_eq_true hvD⟩)
        · right
          have hcnt_eq : D.countP (fun u ↦ x.graph.adjBool v u) =
              (Dset.filter fun u ↦ x.graph.adjBool v u = true).card := by
            rw [countP_eq_card_filter_toFinset hDnd, hD_toFinset]
          rw [hcnt_eq]; exact hDdom v (Graph.mem_distinctVertices.mp hv) hvD
      · intro c hc
        simp only [chords, List.mem_map, List.mem_finRange, true_and] at hc
        obtain ⟨i, rfl⟩ := hc
        have hb := hlr (x.graph.vertexEquiv i)
        rw [hcard_eq] at hb; exact hb
      · intro p hp q hq
        rw [List.mem_iff_getElem] at hp hq
        obtain ⟨ip, hip, rfl⟩ := hp
        obtain ⟨iq, hiq, rfl⟩ := hq
        simp only [List.length_zip, hclen, V, min_self] at hip hiq
        have hip' : ip < V.length := hip
        have hiq' : iq < V.length := hiq
        simp only [List.getElem_zip]
        have hVp : V[ip]'hip' = (x.graph.vertexEquiv ⟨ip, hip'⟩).1 := by
          have := x.graph.vertexEquiv_apply ⟨ip, hip'⟩
          rw [List.getD_eq_getElem _ _ hip'] at this; exact this.symm
        have hVq : V[iq]'hiq' = (x.graph.vertexEquiv ⟨iq, hiq'⟩).1 := by
          have := x.graph.vertexEquiv_apply ⟨iq, hiq'⟩
          rw [List.getD_eq_getElem _ _ hiq'] at this; exact this.symm
        have hcp : chords[ip]'(hclen.symm ▸ hip') =
            (lF (x.graph.vertexEquiv ⟨ip, hip'⟩), rF (x.graph.vertexEquiv ⟨ip, hip'⟩)) := by
          simp [chords]
        have hcq : chords[iq]'(hclen.symm ▸ hiq') =
            (lF (x.graph.vertexEquiv ⟨iq, hiq'⟩), rF (x.graph.vertexEquiv ⟨iq, hiq'⟩)) := by
          simp [chords]
        rw [hVp, hVq, hcp, hcq]
        by_cases heq : ip = iq
        · left; subst heq; rfl
        · right
          have hne_sub : x.graph.vertexEquiv ⟨ip, hip'⟩ ≠ x.graph.vertexEquiv ⟨iq, hiq'⟩ :=
            fun h ↦ heq (congrArg Fin.val (x.graph.vertexEquiv.injective h))
          have hd := hdisj _ _ hne_sub
          have ha := hadj _ _ hne_sub
          refine ⟨⟨⟨⟨hd.1, hd.2.1⟩, hd.2.2.1⟩, hd.2.2.2⟩, ?_⟩
          rw [Bool.eq_iff_iff, Graph.adjBool_eq_true_iff, chordsAlternateBool_eq_true_iff]
          exact ha
    · -- Polynomial length bound `(encW (D, chords)).length ≤ p.eval (encDominatingSet x).length`
      set L := (encDominatingSet x).length
      have hG_le : (encGraph x.graph).length ≤ L := by
        dsimp [L]; enc_len [encDominatingSet_apply]
      have hV_le : V.length ≤ L :=
        x.graph.length_distinctVertices_le.trans hG_le
      have hD_enc : (encList encNat D).length ≤ L := by
        calc (encList encNat D).length
            ≤ (encList encNat V).length := length_encList_filter_le _
          _ ≤ (encList encNat x.graph.vertices).length := length_encList_selectDistinct_le _
          _ ≤ (encGraph x.graph).length := by enc_len [encGraph_apply]
          _ ≤ L := hG_le
      have hchords_enc : (encList (encPair encNat encNat) chords).length ≤
          L * (12 * L + 3) := by
        rw [length_encList]
        have hmem_le : ∀ c ∈ chords,
            2 * (encPair encNat encNat c).length + 1 ≤ 12 * L + 3 := by
          intro c hc
          simp only [chords, List.mem_map, List.mem_finRange, true_and] at hc
          obtain ⟨i, rfl⟩ := hc
          have hcard_eq : Fintype.card {v // v ∈ x.graph.vertices} = V.length := by
            rw [Graph.card_vertexSubtype, Graph.length_distinctVertices]
          have hb := hlr (x.graph.vertexEquiv i)
          rw [hcard_eq] at hb
          have hl_len : (encNat (lF (x.graph.vertexEquiv i))).length ≤ 2 * L := by
            rw [encNat_apply, Nat.size_eq_bits_len]
            exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
          have hr_len : (encNat (rF (x.graph.vertexEquiv i))).length ≤ 2 * L := by
            rw [encNat_apply, Nat.size_eq_bits_len]
            exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
          rw [length_encPair]
          dsimp only
          omega
        have hsum := List.sum_le_length_nsmul
          (chords.map fun a ↦ 2 * (encPair encNat encNat a).length + 1) (12 * L + 3)
          (fun m hm ↦ by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
            exact hmem_le c hc)
        simp only [List.length_map, smul_eq_mul] at hsum
        have hcl : chords.length ≤ L := by simpa [chords] using hV_le
        exact hsum.trans (Nat.mul_le_mul_right _ hcl)
      have hpair_len : (encW (D, chords)).length =
          2 * (encList encNat D).length + 1 +
          (encList (encPair encNat encNat) chords).length := length_encPair (D, chords)
      rw [hpair_len]
      simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      nlinarith

end CircleOneTwoDomination

/-! ### 2. Polynomial-Time Reduction from `EUThreeSAT` -/

/-- Guarded reduction from `EUThreeSAT` to `CircleOneTwoDomination`: well-formed formulas map to
`⟨reductionGraph φ, reductionBound φ⟩`, and ill-formed formulas map to the 1-vertex circle graph
with target bound `0` (unsatisfiable). -/
def toCircleOneTwoDomination (φ : CNF ℕ) : DominatingSetInstance :=
  if EUThreeSAT.syntaxCheck φ then ⟨reductionGraph φ, reductionBound φ⟩
  else ⟨⟨[0], []⟩, 0⟩

/-- Total correctness of `toCircleOneTwoDomination`. -/
theorem toCircleOneTwoDomination_mem_iff (φ : CNF ℕ) :
    toCircleOneTwoDomination φ ∈ CircleOneTwoDomination ↔ φ ∈ EUThreeSAT := by
  unfold toCircleOneTwoDomination
  split_ifs with hsyn
  · have hφ : φ.IsExactThreeDistinct := (EUThreeSAT.syntaxCheck_iff φ).mp hsyn
    constructor
    · rintro ⟨_, D, hDsub, hDdom, hDcard⟩
      exact ⟨hφ, dom_imp_sat hφ hDsub hDdom hDcard⟩
    · rintro ⟨_, hsat⟩
      obtain ⟨D, hDsub, hDdom, hDcard⟩ := sat_imp_dom hφ hsat
      exact ⟨reductionGraph_isCircleChordGraph hφ, D, hDsub, hDdom, le_of_eq hDcard⟩
  · refine iff_of_false ?_ (fun h ↦ hsyn ((EUThreeSAT.syntaxCheck_iff φ).mpr h.1))
    rintro ⟨_, D, _, hDdom, hDcard⟩
    have hD0 : D = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hDcard)
    subst hD0
    have h0 := hDdom 0 List.mem_cons_self (by simp)
    simp at h0

/-! #### Polynomial-Time Certificates for the Reduction Components -/

private lemma baseL_eq_listGetD (k : ℕ) :
    baseL ⟨k % 34, Nat.mod_lt _ (by decide)⟩ =
      ([0, 11, 12, 13, 14, 15, 30, 41, 42, 43, 44, 45, 60, 71, 72, 73, 74, 75,
        90, 91, 92, 93, 97, 99, 100, 103, 105, 106, 110, 113, 119, 121, 122, 123] : List ℕ).getD
        (k % 34) 123 := by
  have h : ∀ r : Fin 34, baseL r =
      ([0, 11, 12, 13, 14, 15, 30, 41, 42, 43, 44, 45, 60, 71, 72, 73, 74, 75,
        90, 91, 92, 93, 97, 99, 100, 103, 105, 106, 110, 113, 119, 121, 122, 123] : List ℕ).getD
        r.1 123 := by decide
  exact h ⟨k % 34, Nat.mod_lt _ (by decide)⟩

private lemma baseR_eq_listGetD (k : ℕ) :
    baseR ⟨k % 34, Nat.mod_lt _ (by decide)⟩ =
      ([16, 102, 101, 18, 17, 29, 46, 109, 108, 48, 47, 59, 76, 116, 115, 78, 77, 89,
        96, 95, 94, 98, 104, 107, 114, 117, 111, 112, 118, 120, 124, 127, 126, 125] : List ℕ).getD
        (k % 34) 125 := by
  have h : ∀ r : Fin 34, baseR r =
      ([16, 102, 101, 18, 17, 29, 46, 109, 108, 48, 47, 59, 76, 116, 115, 78, 77, 89,
        96, 95, 94, 98, 104, 107, 114, 117, 111, 112, 118, 120, 124, 127, 126, 125] : List ℕ).getD
        r.1 125 := by decide
  exact h ⟨k % 34, Nat.mod_lt _ (by decide)⟩

private theorem computableInPolyTime_baseL_mod :
    ComputableInPolyTime (fun k : ℕ ↦ baseL ⟨k % 34, Nat.mod_lt _ (by decide)⟩) encNat encNat := by
  simp_rw [baseL_eq_listGetD]
  exact listGetD_binary (encL := encList encNat) 123 (const _)
    (binary_mod.comp (id'.prod (const 34)))

private theorem computableInPolyTime_baseR_mod :
    ComputableInPolyTime (fun k : ℕ ↦ baseR ⟨k % 34, Nat.mod_lt _ (by decide)⟩) encNat encNat := by
  simp_rw [baseR_eq_listGetD]
  exact listGetD_binary (encL := encList encNat) 125 (const _)
    (binary_mod.comp (id'.prod (const 34)))

private theorem computableInPolyTime_slotBase :
    ComputableInPolyTime (fun p : ℕ × Bool ↦ slotBase p.1 p.2)
      (encPair encNat encBool) encNat := by
  simp_rw [slotBase_eq]
  exact binary_add' (binary_mul' (const 30) (fst encNat encBool))
    (ite' (snd encNat encBool) (const 1) (const 19))

private theorem computableInPolyTime_literalAt :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ literalAt p.1 p.2)
      (encPair encCNF encNat) (encPair encNat encBool) := by
  simp_rw [literalAt_eq_getD]
  unfold encCNF
  have hcl : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ p.1.getD (p.2 / 3) [])
      (encPair (encList (encList (encPair encNat encBool))) encNat)
      (encList (encPair encNat encBool)) :=
    listGetD_binary (encA := encList (encPair encNat encBool)) []
      (fst _ encNat) (binary_div.comp ((snd _ encNat).prod (const 3)))
  exact listGetD_binary (0, false) hcl
    (binary_mod.comp ((snd _ encNat).prod (const 3)))

private theorem computableInPolyTime_nextOcc :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ nextOcc p.1 p.2)
      (encPair encCNF encNat) (encOption encNat) := by
  have hrange : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ List.range (3 * p.1.length))
      (encPair encCNF encNat) (encList encUnary) := by
    have hlen : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ 3 * p.1.length)
        (encPair encCNF encNat) encUnary :=
      unary_mul' (const 3)
        ((length_list (encList (encPair encNat encBool))).comp (fst encCNF encNat))
    exact range.comp hlen
  have hfind : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ nextOcc p.1 p.2)
      (encPair encCNF encNat) (encOption encUnary) := by
    simp_rw [nextOcc_eq_find?]
    refine findWithInput hrange ?_
    have hlt : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ decide (q.1.2 < q.2))
        (encPair (encPair encCNF encNat) encUnary) encBool :=
      binary_lt' (by fun_prop) (unary_to_binary.comp (snd _ _))
    have hvar1 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ (literalAt q.1.1 q.2).1)
        (encPair (encPair encCNF encNat) encUnary) encNat :=
      (computableInPolyTime_literalAt.comp
        (((fst encCNF encNat).comp (fst _ _)).prod (unary_to_binary.comp (snd _ _)))).fst'
    have hvar2 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ (literalAt q.1.1 q.1.2).1)
        (encPair (encPair encCNF encNat) encUnary) encNat :=
      (computableInPolyTime_literalAt.comp (fst _ _)).fst'
    exact bool_and' hlt (decide_eq' hvar1 hvar2)
  have hmap := optionMapWithInput (f := fun (_ : CNF ℕ × ℕ) (n : ℕ) ↦ n) hfind
    (unary_to_binary.comp (snd _ _))
  simpa only [Option.map_id'] using hmap

private theorem computableInPolyTime_repetitionCount :
    ComputableInPolyTime repetitionCount encCNF encUnary := by
  rw [show repetitionCount = _ from funext repetitionCount_eq_countP]
  have hrange : ComputableInPolyTime (fun φ : CNF ℕ ↦ List.range (3 * φ.length))
      encCNF (encList encUnary) :=
    range.comp (unary_mul' (const 3) (length_list (encList (encPair encNat encBool))))
  refine countPWithInput hrange ?_
  have hopt : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ nextOcc p.1 p.2)
      (encPair encCNF encUnary) (encOption encNat) :=
    computableInPolyTime_nextOcc.comp ((fst encCNF encUnary).prod (unary_to_binary.comp (snd _ _)))
  exact optionIsSome hopt

private theorem computableInPolyTime_reductionBound :
    ComputableInPolyTime reductionBound encCNF encNat := by
  rw [show reductionBound = _ from funext reductionBound_eq]
  have h1 : ComputableInPolyTime (fun φ : CNF ℕ ↦ 7 * φ.length) encCNF encUnary :=
    unary_mul' (const 7) (length_list (encList (encPair encNat encBool)))
  have h2 : ComputableInPolyTime (fun φ : CNF ℕ ↦ 2 * repetitionCount φ) encCNF encUnary :=
    unary_mul' (const 2) computableInPolyTime_repetitionCount
  exact unary_to_binary.comp (unary_add' h1 h2)

private theorem computableInPolyTime_redVertices :
    ComputableInPolyTime redVertices encCNF (encList encNat) := by
  have hlen : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
    length_list (encList (encPair encNat encBool))
  have h1 : ComputableInPolyTime (fun φ : CNF ℕ ↦ List.range (34 * φ.length))
      encCNF (encList encNat) := by
    have hr := range.comp (unary_mul' (const 34) hlen)
    have hmap := mapWithInput (f := fun (_ : CNF ℕ) (n : ℕ) ↦ n) hr
      (unary_to_binary.comp (snd _ _))
    simpa only [List.map_id', Function.comp_apply] using hmap
  have hfilt : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (3 * φ.length)).filter fun idx ↦ (nextOcc φ idx).isSome)
      encCNF (encList encUnary) := by
    refine filterWithInput (range.comp (unary_mul' (const 3) hlen)) ?_
    exact optionIsSome (computableInPolyTime_nextOcc.comp
      ((fst encCNF encUnary).prod (unary_to_binary.comp (snd _ _))))
  have h2 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ ((List.range (3 * φ.length)).filter fun idx ↦ (nextOcc φ idx).isSome).flatMap
        fun idx ↦ [0, 1].flatMap fun b ↦
          (List.range 5).map fun q ↦ 34 * φ.length + 5 * (2 * idx + b) + q)
      encCNF (encList encNat) := by
    refine flatMapWithInput hfilt ?_
    refine flatMapConst [0, 1] fun b _ ↦ ?_
    refine mapConst (List.range 5) fun q _ ↦ ?_
    have hm : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ 34 * p.1.length)
        (encPair encCNF encUnary) encUnary :=
      unary_mul' (const 34) (hlen.comp (fst encCNF encUnary))
    have hs : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ 5 * (2 * p.2 + b))
        (encPair encCNF encUnary) encUnary :=
      unary_mul' (const 5) (unary_add' (unary_mul' (const 2) (snd encCNF encUnary)) (const b))
    exact unary_to_binary.comp (unary_add' (unary_add' hm hs) (const q))
  rw [show redVertices = _ from funext redVertices_eq_append]
  exact listAppend' h1 h2

private theorem computableInPolyTime_chordL :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ chordL p.1 p.2)
      (encPair encCNF encNat) encNat := by
  have hm : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ 34 * p.1.length)
      (encPair encCNF encNat) encNat :=
    unary_to_binary.comp (unary_mul' (const 34)
      ((length_list (encList (encPair encNat encBool))).comp (fst encCNF encNat)))
  have hcond : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ decide (p.2 < 34 * p.1.length))
      (encPair encCNF encNat) encBool := binary_lt' (snd encCNF encNat) hm
  have hthen : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ 128 * (p.2 / 34) + baseL ⟨p.2 % 34, Nat.mod_lt _ (by decide)⟩)
      (encPair encCNF encNat) encNat :=
    binary_add'
      (binary_mul' (const 128) (binary_div.comp ((snd encCNF encNat).prod (const 34))))
      (computableInPolyTime_baseL_mod.comp (snd encCNF encNat))
  have hsb : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦
        let off := p.2 - 34 * p.1.length
        let s := off / 5
        128 * (s / 2 / 3) + slotBase (s / 2 % 3) (decide (s % 2 = 0)))
      (encPair encCNF encNat) encNat := by
    have hoff : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ p.2 - 34 * p.1.length)
        (encPair encCNF encNat) encNat := binary_sub' (snd encCNF encNat) hm
    have hs : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (p.2 - 34 * p.1.length) / 5)
        (encPair encCNF encNat) encNat := binary_div.comp (hoff.prod (const 5))
    have hidx : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (p.2 - 34 * p.1.length) / 5 / 2)
        (encPair encCNF encNat) encNat := binary_div.comp (hs.prod (const 2))
    have hisTrue : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ decide ((p.2 - 34 * p.1.length) / 5 % 2 = 0))
        (encPair encCNF encNat) encBool :=
      decide_eq' (binary_mod.comp (hs.prod (const 2))) (const 0)
    exact binary_add'
      (binary_mul' (const 128) (binary_div.comp (hidx.prod (const 3))))
      (computableInPolyTime_slotBase.comp ((binary_mod.comp (hidx.prod (const 3))).prod hisTrue))
  have hq : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (p.2 - 34 * p.1.length) % 5)
      (encPair encCNF encNat) encNat :=
    binary_mod.comp ((binary_sub' (snd encCNF encNat) hm).prod (const 5))
  have helse : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦
        let off := p.2 - 34 * p.1.length
        let s := off / 5
        let q := off % 5
        let sb := 128 * (s / 2 / 3) + slotBase (s / 2 % 3) (decide (s % 2 = 0))
        match q with | 0 => sb + 8 | 1 => sb + 4 | 2 => sb + 1 | 3 => sb + 2 | _ => sb + 3)
      (encPair encCNF encNat) encNat := by
    have hbody := ite' (decide_eq' hq (const 0)) (binary_add' hsb (const 8))
      (ite' (decide_eq' hq (const 1)) (binary_add' hsb (const 4))
        (ite' (decide_eq' hq (const 2)) (binary_add' hsb (const 1))
          (ite' (decide_eq' hq (const 3)) (binary_add' hsb (const 2))
            (binary_add' hsb (const 3)))))
    convert hbody using 1
    funext p
    rcases hqp : (p.2 - 34 * p.1.length) % 5 with _ | _ | _ | _ | _ <;> simp [hqp]
  have hcomb := ite' hcond hthen helse
  convert hcomb using 1
  funext p; rw [chordL_eq_ite]; dsimp only
  by_cases hlt : p.2 < 34 * p.1.length
  · simp [hlt]
  · simp only [hlt, ↓reduceIte, decide_false, Bool.false_eq_true]
    rcases (p.2 - 34 * p.1.length) % 5 with _ | _ | _ | _ | _ <;> rfl

private theorem computableInPolyTime_chordR :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ chordR p.1 p.2)
      (encPair encCNF encNat) encNat := by
  have hm : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ 34 * p.1.length)
      (encPair encCNF encNat) encNat :=
    unary_to_binary.comp (unary_mul' (const 34)
      ((length_list (encList (encPair encNat encBool))).comp (fst encCNF encNat)))
  have hcond : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ decide (p.2 < 34 * p.1.length))
      (encPair encCNF encNat) encBool := binary_lt' (snd encCNF encNat) hm
  have hthen : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ 128 * (p.2 / 34) + baseR ⟨p.2 % 34, Nat.mod_lt _ (by decide)⟩)
      (encPair encCNF encNat) encNat :=
    binary_add'
      (binary_mul' (const 128) (binary_div.comp ((snd encCNF encNat).prod (const 34))))
      (computableInPolyTime_baseR_mod.comp (snd encCNF encNat))
  have hoff : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ p.2 - 34 * p.1.length)
      (encPair encCNF encNat) encNat := binary_sub' (snd encCNF encNat) hm
  have hs : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (p.2 - 34 * p.1.length) / 5)
      (encPair encCNF encNat) encNat := binary_div.comp (hoff.prod (const 5))
  have hidx : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (p.2 - 34 * p.1.length) / 5 / 2)
      (encPair encCNF encNat) encNat := binary_div.comp (hs.prod (const 2))
  have hisTrue : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ decide ((p.2 - 34 * p.1.length) / 5 % 2 = 0))
      (encPair encCNF encNat) encBool :=
    decide_eq' (binary_mod.comp (hs.prod (const 2))) (const 0)
  have hsb : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦
        let off := p.2 - 34 * p.1.length
        let s := off / 5
        128 * (s / 2 / 3) + slotBase (s / 2 % 3) (decide (s % 2 = 0)))
      (encPair encCNF encNat) encNat :=
    binary_add'
      (binary_mul' (const 128) (binary_div.comp (hidx.prod (const 3))))
      (computableInPolyTime_slotBase.comp ((binary_mod.comp (hidx.prod (const 3))).prod hisTrue))
  have hq : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (p.2 - 34 * p.1.length) % 5)
      (encPair encCNF encNat) encNat := binary_mod.comp (hoff.prod (const 5))
  have hnext : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ nextOcc p.1 ((p.2 - 34 * p.1.length) / 5 / 2))
      (encPair encCNF encNat) (encOption encNat) :=
    computableInPolyTime_nextOcc.comp ((fst encCNF encNat).prod hidx)
  have hq0 : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦
        let off := p.2 - 34 * p.1.length
        let s := off / 5
        let idx := s / 2
        let isTrue := decide (s % 2 = 0)
        let sb := 128 * (idx / 3) + slotBase (idx % 3) isTrue
        match nextOcc p.1 idx with
        | some idx' =>
          let samePol := decide ((literalAt p.1 idx).2 = (literalAt p.1 idx').2)
          let isTrue' := if samePol then !isTrue else isTrue
          128 * (idx' / 3) + slotBase (idx' % 3) isTrue'
        | none => sb + 9)
      (encPair encCNF encNat) encNat := by
    have helim := optionElimWithInput hnext (binary_add' hsb (const 9))
      (body := fun (p : CNF ℕ × ℕ) (idx' : ℕ) ↦
        let off := p.2 - 34 * p.1.length
        let s := off / 5
        let idx := s / 2
        let isTrue := decide (s % 2 = 0)
        let samePol := decide ((literalAt p.1 idx).2 = (literalAt p.1 idx').2)
        let isTrue' := if samePol then !isTrue else isTrue
        128 * (idx' / 3) + slotBase (idx' % 3) isTrue')
      (by
        have hpol1 : ComputableInPolyTime
            (fun r : (CNF ℕ × ℕ) × ℕ ↦ (literalAt r.1.1 ((r.1.2 - 34 * r.1.1.length) / 5 / 2)).2)
            (encPair (encPair encCNF encNat) encNat) encBool :=
          (computableInPolyTime_literalAt.comp
            (((fst encCNF encNat).comp (fst _ _)).prod (hidx.comp (fst _ _)))).snd'
        have hpol2 : ComputableInPolyTime
            (fun r : (CNF ℕ × ℕ) × ℕ ↦ (literalAt r.1.1 r.2).2)
            (encPair (encPair encCNF encNat) encNat) encBool :=
          (computableInPolyTime_literalAt.comp
            (((fst encCNF encNat).comp (fst _ _)).prod (snd _ _))).snd'
        have hisT : ComputableInPolyTime
            (fun r : (CNF ℕ × ℕ) × ℕ ↦ decide ((r.1.2 - 34 * r.1.1.length) / 5 % 2 = 0))
            (encPair (encPair encCNF encNat) encNat) encBool :=
          hisTrue.comp (fst _ _)
        have hisT' : ComputableInPolyTime
            (fun r : (CNF ℕ × ℕ) × ℕ ↦
              if decide ((literalAt r.1.1 ((r.1.2 - 34 * r.1.1.length) / 5 / 2)).2 =
                  (literalAt r.1.1 r.2).2)
              then !decide ((r.1.2 - 34 * r.1.1.length) / 5 % 2 = 0)
              else decide ((r.1.2 - 34 * r.1.1.length) / 5 % 2 = 0))
            (encPair (encPair encCNF encNat) encNat) encBool :=
          ite' (decide_eq' hpol1 hpol2) (bool_not.comp hisT) hisT
        exact binary_add'
          (binary_mul' (const 128) (binary_div.comp ((snd _ _).prod (const 3))))
          (computableInPolyTime_slotBase.comp
            ((binary_mod.comp ((snd _ _).prod (const 3))).prod hisT')))
    convert helim using 1
    funext p; dsimp only; cases nextOcc p.1 ((p.2 - 34 * p.1.length) / 5 / 2) <;> rfl
  have helse : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦
        let off := p.2 - 34 * p.1.length
        let s := off / 5
        let q := off % 5
        let idx := s / 2
        let isTrue := decide (s % 2 = 0)
        let sb := 128 * (idx / 3) + slotBase (idx % 3) isTrue
        match q with
        | 0 => match nextOcc p.1 idx with
          | some idx' =>
            let samePol := decide ((literalAt p.1 idx).2 = (literalAt p.1 idx').2)
            let isTrue' := if samePol then !isTrue else isTrue
            128 * (idx' / 3) + slotBase (idx' % 3) isTrue'
          | none => sb + 9
        | 1 => sb + 9 | 2 => sb + 7 | 3 => sb + 6 | _ => sb + 5)
      (encPair encCNF encNat) encNat := by
    have hbody := ite' (decide_eq' hq (const 0)) hq0
      (ite' (decide_eq' hq (const 1)) (binary_add' hsb (const 9))
        (ite' (decide_eq' hq (const 2)) (binary_add' hsb (const 7))
          (ite' (decide_eq' hq (const 3)) (binary_add' hsb (const 6))
            (binary_add' hsb (const 5)))))
    convert hbody using 1
    funext p
    rcases hqp : (p.2 - 34 * p.1.length) % 5 with _ | _ | _ | _ | _ <;> simp [hqp]
  have hcomb := ite' hcond hthen helse
  convert hcomb using 1
  funext p; rw [chordR_eq_ite]; dsimp only
  by_cases hlt : p.2 < 34 * p.1.length
  · simp [hlt]
  · simp only [hlt, ↓reduceIte, decide_false, Bool.false_eq_true]
    rcases (p.2 - 34 * p.1.length) % 5 with _ | _ | _ | _ | _ <;> rfl

private theorem computableInPolyTime_redEdges :
    ComputableInPolyTime redEdges encCNF (encList (encPair encNat encNat)) := by
  rw [show redEdges = _ from funext redEdges_eq_flatMap]
  refine flatMapWithInput computableInPolyTime_redVertices ?_
  have hfilt : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ (redVertices p.1).filter fun v ↦
        decide (p.2 < v) &&
        chordsAlternateBool (chordL p.1 p.2) (chordR p.1 p.2) (chordL p.1 v) (chordR p.1 v))
      (encPair encCNF encNat) (encList encNat) := by
    refine filterWithInput (computableInPolyTime_redVertices.comp (fst encCNF encNat)) ?_
    have hlt : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ decide (q.1.2 < q.2))
        (encPair (encPair encCNF encNat) encNat) encBool := by fun_prop
    have hLu : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ chordL q.1.1 q.1.2)
        (encPair (encPair encCNF encNat) encNat) encNat :=
      computableInPolyTime_chordL.comp (fst _ _)
    have hRu : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ chordR q.1.1 q.1.2)
        (encPair (encPair encCNF encNat) encNat) encNat :=
      computableInPolyTime_chordR.comp (fst _ _)
    have hLv : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ chordL q.1.1 q.2)
        (encPair (encPair encCNF encNat) encNat) encNat :=
      computableInPolyTime_chordL.comp (((fst encCNF encNat).comp (fst _ _)).prod (snd _ _))
    have hRv : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ chordR q.1.1 q.2)
        (encPair (encPair encCNF encNat) encNat) encNat :=
      computableInPolyTime_chordR.comp (((fst encCNF encNat).comp (fst _ _)).prod (snd _ _))
    have halt := CircleOneTwoDomination.computableInPolyTime_chordsAlternateBool.comp
      ((hLu.prod hRu).prod (hLv.prod hRv))
    exact bool_and' hlt halt
  exact mapWithInput hfilt (by fun_prop)

private theorem computableInPolyTime_reductionGraph :
    ComputableInPolyTime reductionGraph encCNF encGraph :=
  encGraph_mk_polyTime computableInPolyTime_redVertices computableInPolyTime_redEdges

/-- The reduction `toCircleOneTwoDomination` runs in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toCircleOneTwoDomination :
    ComputableInPolyTime toCircleOneTwoDomination encCNF encDominatingSet := by
  unfold toCircleOneTwoDomination
  exact ite' EUThreeSAT.computableInPolyTime_syntaxCheck
    (encDominatingSet_mk_polyTime computableInPolyTime_reductionGraph
      computableInPolyTime_reductionBound)
    (const (⟨⟨[0], []⟩, 0⟩ : DominatingSetInstance))

/-! ### 3. NP-Completeness & Non-Vacuity Witness -/

/-- `EUThreeSAT` reduces in polynomial time to `CircleOneTwoDomination`. -/
theorem polyTimeReducible_EUThreeSAT_CircleOneTwoDomination :
    PolyTimeReducible encCNF encDominatingSet EUThreeSAT CircleOneTwoDomination :=
  ⟨toCircleOneTwoDomination, computableInPolyTime_toCircleOneTwoDomination,
    fun φ ↦ (toCircleOneTwoDomination_mem_iff φ).symm⟩

/-- `CircleOneTwoDomination` is NP-hard under `encDominatingSet`. -/
theorem CircleOneTwoDomination_npHard :
    NPHard encDominatingSet CircleOneTwoDomination :=
  EUThreeSAT_npHard.trans polyTimeReducible_EUThreeSAT_CircleOneTwoDomination

/-- `[1, 2]`-domination on circle graphs is NP-complete under the binary graph encoding
`encDominatingSet`. -/
theorem CircleOneTwoDomination_npComplete : NPComplete encDominatingSet CircleOneTwoDomination :=
  ⟨CircleOneTwoDomination.mem_NP, CircleOneTwoDomination_npHard⟩

/-- Non-degenerate joint non-vacuity witness for `CircleOneTwoDomination` and the reduction:
the 1-clause `EUThreeSAT` formula `[(0, true), (1, true), (2, true)]` maps to a 34-vertex circle
graph in `CircleOneTwoDomination` (with a `[1, 2]`-dominating set of size `7`), while the
single-vertex circle graph with bound `0` is outside `CircleOneTwoDomination`. -/
theorem circleOneTwoDomination_nonvacuous :
    let φ : CNF ℕ := [[(0, true), (1, true), (2, true)]]
    φ ∈ EUThreeSAT ∧
    toCircleOneTwoDomination φ ∈ CircleOneTwoDomination ∧
    (⟨⟨[0], []⟩, 0⟩ : DominatingSetInstance) ∉ CircleOneTwoDomination := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, fun _ ↦ true, by decide⟩
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, by decide⟩
  · rw [toCircleOneTwoDomination_mem_iff]
    refine ⟨?_, fun _ ↦ true, by decide⟩
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, by decide⟩
  · rintro ⟨_, D, _, hDdom, hDcard⟩
    have hD0 : D = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hDcard)
    subst hD0
    have h0 := hDdom 0 List.mem_cons_self (by simp)
    simp at h0

end Cslib.Complexity
