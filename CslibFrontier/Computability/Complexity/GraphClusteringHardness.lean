/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.MaxCut.Simple
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Reduction.Guard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Graph-Clustering Primitives and NP-Completeness of Bisection and Dense Subgraphs

This module establishes polynomial-time primitives for rational list summation and induced-subgraph
connectivity on multi-tape Turing machines, together with full NP-completeness proofs (under
standard Lean axioms) for two graph-clustering decision problems:

1. **Polynomial-time rational list summation and induced-subgraph connectivity**
   (`computableInPolyTime_rat_listSum`, `graphConnectedBool`, `graphConnectedBool_eq_true_iff`):
   summing framed lists of binary rationals via common-denominator clearing, and deciding
   connectedness of induced subgraphs of `Cslib.Complexity.Graph` in polynomial time via fixed-width
   iterative reachability relaxation.
2. **Minimum Bisection (`MinimumBisection`)**: deciding whether an even-order undirected graph
   admits an equitable two-way vertex partition cutting at most `B` edges is NP-complete, proved
   via the padding-and-complementation reduction `H = (G ⊔ K̄_n)ᶜ` from
   `Cslib.Complexity.SimpleMaxCut`.
3. **Fixed-Density Connected Subgraph (`FixedDensityConnectedSubgraph`)**: deciding whether a graph
   contains a connected `s`-vertex induced subgraph with at least `τ` edges is NP-complete, proved
   via reduction from `Cslib.Complexity.Clique`.

## Main definitions

- `CslibFrontier.Computability.Complexity.distinctNatList`: duplicate-free first-occurrence list.
- `CslibFrontier.Computability.Complexity.graphConnectedBool`: polynomial-time connectedness test
  for induced subgraphs of `Cslib.Complexity.Graph`.
- `CslibFrontier.Computability.Complexity.MinimumBisectionInstance`,
  `CslibFrontier.Computability.Complexity.MinimumBisection`: minimum graph bisection problem.
- `CslibFrontier.Computability.Complexity.FDCSInstance`,
  `CslibFrontier.Computability.Complexity.FixedDensityConnectedSubgraph`: fixed-density connected
  subgraph decision problem.

## Main results

- `CslibFrontier.Computability.Complexity.computableInPolyTime_rat_listSum`,
  `CslibFrontier.Computability.Complexity.graphConnectedBool_eq_true_iff`,
  `CslibFrontier.Computability.Complexity.computableInPolyTime_graphConnectedBool`.
- `CslibFrontier.Computability.Complexity.MinimumBisection_npHard`,
  `CslibFrontier.Computability.Complexity.MinimumBisection_npComplete`.
- `CslibFrontier.Computability.Complexity.FixedDensityConnectedSubgraph_npHard`,
  `CslibFrontier.Computability.Complexity.FixedDensityConnectedSubgraph_npComplete`.

## Tags

computational complexity, NP-completeness, minimum bisection, dense connected subgraph, graph
connectivity
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Polynomial-Time Rational List Summation and Induced-Subgraph Connectivity -/

private def listDenomProd (l : List ℚ) : ℕ :=
  (l.map Rat.den).prod

private lemma listDenomProd_pos (l : List ℚ) : 0 < listDenomProd l :=
  List.prod_pos fun _ hd ↦ by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    exact q.pos

private lemma dvd_listDenomProd {l : List ℚ} {q : ℚ} (hq : q ∈ l) :
    q.den ∣ listDenomProd l :=
  List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)

private def listScaledNumSum (l : List ℚ) : ℤ :=
  (l.map fun q ↦ q.num * ((listDenomProd l / q.den : ℕ) : ℤ)).sum

private lemma cast_sum_clearDenom (D : ℕ) :
    ∀ (s : List ℚ), (∀ q ∈ s, q.den ∣ D) →
      (((s.map fun q ↦ q.num * ((D / q.den : ℕ) : ℤ)).sum : ℤ) : ℚ) = (D : ℚ) * s.sum
  | [], _ => by simp
  | q :: s, h => by
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    rw [← Rat.clearDenom_entry (h q List.mem_cons_self),
      cast_sum_clearDenom D s fun r hr ↦ h r (List.mem_cons_of_mem q hr)]

private lemma divInt_listScaledNumSum (l : List ℚ) :
    Rat.divInt (listScaledNumSum l) (listDenomProd l : ℤ) = l.sum := by
  have hD : (listDenomProd l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (listDenomProd_pos l).ne'
  rw [Rat.divInt_eq_div, Int.cast_natCast, listScaledNumSum,
    cast_sum_clearDenom (listDenomProd l) l fun _ hq ↦ dvd_listDenomProd hq,
    mul_div_cancel_left₀ _ hD]

@[fun_prop]
private theorem computableInPolyTime_listDenomProd :
    ComputableInPolyTime listDenomProd (encList encRat) encNat := by
  unfold listDenomProd
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_listScaledNumSum :
    ComputableInPolyTime listScaledNumSum (encList encRat) encIntBin := by
  unfold listScaledNumSum
  exact intBin_sum.comp (mapWithInput id' (by fun_prop))

/-- Summing a framed list of binary rationals (`encList encRat`) is computable in polynomial time.
-/
@[fun_prop]
theorem computableInPolyTime_rat_listSum :
    ComputableInPolyTime (List.sum : List ℚ → ℚ) (encList encRat) encRat :=
  (show ComputableInPolyTime
      (fun l : List ℚ ↦ Rat.divInt (listScaledNumSum l) ((listDenomProd l : ℕ) : ℤ))
      (encList encRat) encRat by fun_prop).of_enc_eq fun l ↦
    congrArg encRat (divInt_listScaledNumSum l).symm

/-- Compositional polynomial-time rule for summing a computed list of rationals. -/
@[fun_prop]
theorem computableInPolyTime_rat_listSum' {α : Type} {enc : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f enc (encList encRat)) :
    ComputableInPolyTime (fun a ↦ (f a).sum) enc encRat :=
  computableInPolyTime_rat_listSum.comp hf

/-- Deduplication of a natural-number list preserving first occurrences. -/
def distinctNatList (S : List ℕ) : List ℕ :=
  selectDistinct S (List.replicate S.length true)

theorem mem_distinctNatList {S : List ℕ} {v : ℕ} : v ∈ distinctNatList S ↔ v ∈ S :=
  mem_selectDistinct_replicate

theorem nodup_distinctNatList (S : List ℕ) : (distinctNatList S).Nodup :=
  nodup_selectDistinct _ _

@[fun_prop]
theorem computableInPolyTime_distinctNatList :
    ComputableInPolyTime distinctNatList (encList encNat) (encList encNat) := by
  unfold distinctNatList
  fun_prop

private def relaxStepFn (G : Graph) (S' : List ℕ) (vis : List Bool) : List Bool :=
  (List.range S'.length).map fun i ↦
    vis.getD i false ||
      (List.range S'.length).any fun j ↦
        vis.getD j false && G.adjBool (S'.getD j 0) (S'.getD i 0)

/-- Polynomial-time test deciding whether the subgraph of `G.toSimpleGraph` induced on `{v | v ∈ S}`
is connected (nonempty and all pairs joined by a walk inside `S`). -/
def graphConnectedBool (G : Graph) (S : List ℕ) : Bool :=
  let S' := distinctNatList S
  if S'.isEmpty then false
  else
    let vis₀ := (List.range S'.length).map fun i ↦ decide (i = 0)
    ((List.range S'.length).foldl (fun vis _ ↦ relaxStepFn G S' vis) vis₀).all (· == true)

private lemma relaxStepFn_getD (G : Graph) (S' : List ℕ) (vis : List Bool) {i : ℕ}
    (hi : i < S'.length) :
    (relaxStepFn G S' vis).getD i false =
      (vis.getD i false ||
        (List.range S'.length).any fun j ↦
          vis.getD j false && G.adjBool (S'.getD j 0) (S'.getD i 0)) := by
  unfold relaxStepFn
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private lemma foldl_relaxStepFn_eq_iterate (G : Graph) (S' : List ℕ) :
    ∀ (rs : List ℕ) (vis : List Bool),
      rs.foldl (fun v _ ↦ relaxStepFn G S' v) vis = (relaxStepFn G S')^[rs.length] vis
  | [], _ => rfl
  | _ :: rs, vis => by
    simp only [List.foldl_cons, List.length_cons, Function.iterate_succ_apply]
    exact foldl_relaxStepFn_eq_iterate G S' rs (relaxStepFn G S' vis)

private lemma length_iterate_relaxStepFn (G : Graph) (S' : List ℕ) :
    ∀ (k : ℕ) {vis : List Bool}, vis.length = S'.length →
      ((relaxStepFn G S')^[k] vis).length = S'.length
  | 0, _, h => h
  | k + 1, _, h => by
    rw [Function.iterate_succ_apply']
    unfold relaxStepFn
    rw [List.length_map, List.length_range]

private lemma relaxStepFn_mono (G : Graph) (S' : List ℕ) {vis : List Bool} {i : ℕ}
    (hi : i < S'.length) (h : vis.getD i false = true) :
    (relaxStepFn G S' vis).getD i false = true := by
  rw [relaxStepFn_getD G S' vis hi, h, Bool.true_or]

private lemma iterate_relaxStepFn_mono (G : Graph) (S' : List ℕ) {vis : List Bool} {i : ℕ}
    (hi : i < S'.length) :
    ∀ {a b : ℕ}, a ≤ b → ((relaxStepFn G S')^[a] vis).getD i false = true →
      ((relaxStepFn G S')^[b] vis).getD i false = true := by
  intro a b hab h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simpa using h
  | succ d ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact relaxStepFn_mono G S' hi (ih (Nat.le_add_right a d))

/-- Exact correctness of `graphConnectedBool`: it returns `true` if and only if the induced
subgraph `G.toSimpleGraph.induce {v | v ∈ S}` is connected. -/
theorem graphConnectedBool_eq_true_iff (G : Graph) (S : List ℕ) :
    graphConnectedBool G S = true ↔ (G.toSimpleGraph.induce {v | v ∈ S}).Connected := by
  unfold graphConnectedBool
  set S' := distinctNatList S
  set H := G.toSimpleGraph.induce {v | v ∈ S}
  by_cases hemp : S'.isEmpty = true
  · simp only [hemp, ↓reduceIte, Bool.false_eq_true, false_iff]
    intro hconn
    obtain ⟨⟨v, hvS⟩⟩ := hconn.nonempty
    have hv' : v ∈ S' := mem_distinctNatList.mpr hvS
    rw [List.isEmpty_iff] at hemp
    simp [hemp] at hv'
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    have hne : S' ≠ [] := fun h ↦ hemp (List.isEmpty_iff.mpr h)
    have hm : 0 < S'.length := List.length_pos_of_ne_nil hne
    set m := S'.length
    let e : Fin m ≃ {v // v ∈ S} :=
      ((nodup_distinctNatList S).getEquiv _).trans
        (Equiv.subtypeEquivRight fun _ ↦ mem_distinctNatList)
    have he_val (i : Fin m) : (e i : ℕ) = S'.getD i.1 0 := by
      change S'[i.1] = S'.getD i.1 0
      exact (List.getD_eq_getElem S' 0 i.2).symm
    let v₀ : {v // v ∈ S} := e ⟨0, hm⟩
    let vis₀ : List Bool := (List.range m).map fun i ↦ decide (i = 0)
    rw [foldl_relaxStepFn_eq_iterate, List.length_range]
    have hlen_m : ((relaxStepFn G S')^[m] vis₀).length = m :=
      length_iterate_relaxStepFn G S' m (by simp [vis₀, m])
    have hsound : ∀ (k : ℕ), ∀ i : Fin m,
        ((relaxStepFn G S')^[k] vis₀).getD i.1 false = true → H.Reachable v₀ (e i) := by
      intro k
      induction k with
      | zero =>
        intro i hi
        have hi0 : i.1 = 0 := by
          simpa [vis₀, List.getD_eq_getElem?_getD, i.2] using hi
        have hieq : i = ⟨0, hm⟩ := Fin.ext hi0
        subst hieq
        exact SimpleGraph.Reachable.refl v₀
      | succ k ih =>
        intro i hi
        rw [Function.iterate_succ_apply', relaxStepFn_getD G S' _ i.2,
          Bool.or_eq_true, List.any_eq_true] at hi
        rcases hi with hprev | ⟨j, hj_mem, hand⟩
        · exact ih i hprev
        · rw [List.mem_range] at hj_mem
          rw [Bool.and_eq_true, Graph.adjBool_eq_true_iff] at hand
          have hreachj := ih ⟨j, hj_mem⟩ hand.1
          have hadjH : H.Adj (e ⟨j, hj_mem⟩) (e i) := by
            change G.toSimpleGraph.Adj (e ⟨j, hj_mem⟩).1 (e i).1
            rw [he_val ⟨j, hj_mem⟩, he_val i]
            exact hand.2
          exact hreachj.trans hadjH.reachable
    have hwalk : ∀ (u z : {v // v ∈ S}) (p : H.Walk u z), z = v₀ →
        ((relaxStepFn G S')^[p.length] vis₀).getD (e.symm u).1 false = true := by
      intro u z p
      induction p with
      | nil =>
        rintro rfl
        have h0 : (e.symm v₀).1 = 0 := by simp [v₀]
        simp [h0, vis₀, List.getD_eq_getElem?_getD, hm]
      | @cons u w z hadj q ih =>
        rintro rfl
        rw [SimpleGraph.Walk.length_cons, Function.iterate_succ_apply',
          relaxStepFn_getD G S' _ (e.symm u).2, Bool.or_eq_true, List.any_eq_true]
        right
        refine ⟨(e.symm w).1, List.mem_range.mpr (e.symm w).2, ?_⟩
        rw [Bool.and_eq_true, Graph.adjBool_eq_true_iff]
        refine ⟨ih rfl, ?_⟩
        rw [← he_val (e.symm w), ← he_val (e.symm u), e.apply_symm_apply, e.apply_symm_apply]
        exact hadj.symm
    constructor
    · intro hall
      have hall_idx : ∀ i : Fin m, ((relaxStepFn G S')^[m] vis₀).getD i.1 false = true := by
        intro i
        rw [List.all_eq_true] at hall
        have hi_lt : i.1 < ((relaxStepFn G S')^[m] vis₀).length := by
          rw [hlen_m]; exact i.2
        have hmem := List.getElem_mem hi_lt
        rw [List.getD_eq_getElem _ false hi_lt]
        exact beq_iff_eq.mp (hall _ hmem)
      rw [SimpleGraph.connected_iff]
      refine ⟨fun u w ↦ ?_, ⟨v₀⟩⟩
      have hu := hsound m (e.symm u) (hall_idx (e.symm u))
      have hw := hsound m (e.symm w) (hall_idx (e.symm w))
      rw [e.apply_symm_apply] at hu hw
      exact hu.symm.trans hw
    · intro hconn
      rw [List.all_eq_true]
      intro b hb
      obtain ⟨i_nat, hi_lt, rfl⟩ := List.getElem_of_mem hb
      have hi_m : i_nat < m := by
        have hlen_eq : ((relaxStepFn G S')^[m]
            ((List.range m).map fun i ↦ decide (i = 0))).length = m := hlen_m
        omega
      let i : Fin m := ⟨i_nat, hi_m⟩
      obtain ⟨p, hp⟩ := (hconn.preconnected (e i) v₀).exists_isPath
      have hplen : p.length ≤ m := by
        have hnd : (p.support.map e.symm).Nodup := hp.support_nodup.map e.symm.injective
        have hle : (p.support.map e.symm).toFinset.card ≤ (univ : Finset (Fin m)).card :=
          card_le_univ _
        rw [List.toFinset_card_of_nodup hnd, List.length_map,
          SimpleGraph.Walk.length_support, card_univ, Fintype.card_fin] at hle
        omega
      have hget := iterate_relaxStepFn_mono G S' hi_m hplen
        (by simpa [i] using hwalk (e i) v₀ p rfl)
      rw [List.getD_eq_getElem _ false hi_lt] at hget
      exact beq_iff_eq.mpr hget

private theorem computableInPolyTime_relaxStepFn :
    ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × List Bool) × ℕ ↦
        relaxStepFn q.1.1.1 q.1.1.2 q.1.2)
      (encPair (encPair (encPair encGraph (encList encNat)) (encList encBool)) encUnary)
      (encList encBool) := by
  let E₀ := encPair (encPair (encPair encGraph (encList encNat)) (encList encBool)) encUnary
  let E₁ := encPair E₀ encUnary
  let E₂ := encPair E₁ encUnary
  have hS_len : ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × List Bool) × ℕ ↦ q.1.1.2.length) E₀ encUnary :=
    (length_list encNat).comp ((snd encGraph (encList encNat)).comp
      ((fst _ (encList encBool)).comp (fst _ encUnary)))
  have hS_len1 : ComputableInPolyTime
      (fun p : (((Graph × List ℕ) × List Bool) × ℕ) × ℕ ↦ p.1.1.1.2.length) E₁ encUnary :=
    hS_len.comp (fst E₀ encUnary)
  have hvis_i : ComputableInPolyTime
      (fun p : (((Graph × List ℕ) × List Bool) × ℕ) × ℕ ↦ p.1.1.2.getD p.2 false) E₁ encBool :=
    listGetDWithInput
      ((snd _ (encList encBool)).comp ((fst _ encUnary).comp (fst E₀ encUnary)))
      (snd E₀ encUnary) false
  have hvis_j : ComputableInPolyTime
      (fun r : ((((Graph × List ℕ) × List Bool) × ℕ) × ℕ) × ℕ ↦ r.1.1.1.2.getD r.2 false)
      E₂ encBool :=
    listGetDWithInput
      ((snd _ (encList encBool)).comp
        ((fst _ encUnary).comp ((fst E₀ encUnary).comp (fst E₁ encUnary))))
      (snd E₁ encUnary) false
  have hS2 : ComputableInPolyTime
      (fun r : ((((Graph × List ℕ) × List Bool) × ℕ) × ℕ) × ℕ ↦ r.1.1.1.1.2)
      E₂ (encList encNat) :=
    (snd encGraph (encList encNat)).comp
      ((fst _ (encList encBool)).comp
        ((fst _ encUnary).comp ((fst E₀ encUnary).comp (fst E₁ encUnary))))
  have hG2 : ComputableInPolyTime
      (fun r : ((((Graph × List ℕ) × List Bool) × ℕ) × ℕ) × ℕ ↦ r.1.1.1.1.1)
      E₂ encGraph :=
    (fst encGraph (encList encNat)).comp
      ((fst _ (encList encBool)).comp
        ((fst _ encUnary).comp ((fst E₀ encUnary).comp (fst E₁ encUnary))))
  have hadj : ComputableInPolyTime
      (fun r : ((((Graph × List ℕ) × List Bool) × ℕ) × ℕ) × ℕ ↦
        r.1.1.1.1.1.adjBool (r.1.1.1.1.2.getD r.2 0) (r.1.1.1.1.2.getD r.1.2 0))
      E₂ encBool :=
    Graph.computableInPolyTime_adjBool_comp hG2
      (listGetDWithInput hS2 (snd E₁ encUnary) 0)
      (listGetDWithInput hS2 ((snd E₀ encUnary).comp (fst E₁ encUnary)) 0)
  unfold relaxStepFn
  exact mapWithInput (ComputableInPolyTime.range.comp hS_len)
    (bool_or' hvis_i
      (anyWithInput (ComputableInPolyTime.range.comp hS_len1) (bool_and' hvis_j hadj)))

/-- `graphConnectedBool` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_graphConnectedBool :
    ComputableInPolyTime (fun p : Graph × List ℕ ↦ graphConnectedBool p.1 p.2)
      (encPair encGraph (encList encNat)) encBool := by
  have hS' : ComputableInPolyTime (fun p : Graph × List ℕ ↦ distinctNatList p.2)
      (encPair encGraph (encList encNat)) (encList encNat) :=
    computableInPolyTime_distinctNatList.comp (snd encGraph (encList encNat))
  have hlenS' : ComputableInPolyTime (fun p : Graph × List ℕ ↦ (distinctNatList p.2).length)
      (encPair encGraph (encList encNat)) encUnary :=
    (length_list encNat).comp hS'
  have hfold : ComputableInPolyTime
      (fun p : Graph × List ℕ ↦
        (List.range (distinctNatList p.2).length).foldl
          (fun vis _ ↦ relaxStepFn p.1 (distinctNatList p.2) vis)
          ((List.range (distinctNatList p.2).length).map fun i ↦ decide (i = 0)))
      (encPair encGraph (encList encNat)) (encList encBool) := by
    refine foldlWith
      (encIn := encPair encGraph (encList encNat))
      (encA := encUnary) (encL := encList encUnary)
      (encB := encList encBool) (encP := encPair encGraph (encList encNat))
      (par := fun p ↦ (p.1, distinctNatList p.2))
      (list := fun p ↦ List.range (distinctNatList p.2).length)
      (init := fun p ↦ (List.range (distinctNatList p.2).length).map fun i ↦ decide (i = 0))
      (step := fun gs vis _ ↦ relaxStepFn gs.1 gs.2 vis)
      ((fst encGraph (encList encNat)).prod hS')
      (ComputableInPolyTime.range.comp hlenS')
      (mapWithInput (ComputableInPolyTime.range.comp hlenS')
        (decide_eq' (snd (encPair encGraph (encList encNat)) encUnary) (const 0)))
      computableInPolyTime_relaxStepFn
      (B := fun p ↦ (distinctNatList p.2).length * 3)
      (by
        obtain ⟨c, d, hcd⟩ := hlenS'.polyBounded.exists_le
        exact PolyBounded.of_forall_le (3 * c) d fun p ↦ by
          have := hcd p
          nlinarith)
      (fun p k _ ↦ by
        set S' := distinctNatList p.2
        rw [foldl_relaxStepFn_eq_iterate, List.length_take]
        have hlen_vis : ((relaxStepFn p.1 S')^[min k (List.range S'.length).length]
            ((List.range S'.length).map fun i ↦ decide (i = 0))).length = S'.length :=
          length_iterate_relaxStepFn p.1 S' _ (by simp)
        calc
          (encList encBool _).length ≤
              ((relaxStepFn p.1 S')^[min k (List.range S'.length).length]
                ((List.range S'.length).map fun i ↦ decide (i = 0))).length * (2 * 1 + 1) :=
            length_encList_le encBool _ (b := 1) fun b _ ↦ by cases b <;> decide
          _ = S'.length * 3 := by rw [hlen_vis])
  have heq : (fun p : Graph × List ℕ ↦ graphConnectedBool p.1 p.2) =
      fun p : Graph × List ℕ ↦
        if (distinctNatList p.2).isEmpty then false
        else ((List.range (distinctNatList p.2).length).foldl
          (fun vis _ ↦ relaxStepFn p.1 (distinctNatList p.2) vis)
          ((List.range (distinctNatList p.2).length).map fun i ↦ decide (i = 0))).all
            (fun b ↦ decide (b = true)) := rfl
  rw [heq]
  exact ite' ((listIsEmpty' encNat).comp hS') (const false)
    (allWithInput hfold
      (decide_eq' (snd (encPair encGraph (encList encNat)) encBool) (const true)))

/-! ### 2. Minimum Bisection (`MinimumBisection`) -/

/-- An instance `(graph, bound)` of **Minimum Bisection**. -/
@[ext]
structure MinimumBisectionInstance where
  /-- Undirected graph on its declared vertices. -/
  graph : Graph
  /-- Upper bound on the number of edges crossing the bisection. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `MinimumBisectionInstance`. -/
enc_structure encMinimumBisection : MinimumBisectionInstance where
  graph : encGraph,
  bound : encNat

attribute [fun_prop] encMinimumBisection_graph_polyTime encMinimumBisection_bound_polyTime
  encMinimumBisection_mk_polyTime

/-- **Minimum Bisection**: even-order graphs admitting an equitable vertex subset `S`
(`2 * |S| = |V|`) with at most `bound` crossing edges `(G.induced.interedges S Sᶜ).card ≤ bound`.
-/
@[expose]
def MinimumBisection : Set MinimumBisectionInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices},
    2 * S.card = Fintype.card {v // v ∈ x.graph.vertices} ∧
    (x.graph.induced.interedges S Sᶜ).card ≤ x.bound}

namespace MinimumBisection

private def cutCountBool (G : Graph) (S : List ℕ) : ℕ :=
  ((G.distinctVertices.flatMap fun u ↦ G.distinctVertices.map fun v ↦ (u, v)).filter
    fun p ↦ G.adjBool p.1 p.2 && (decide (p.1 ∈ S) && !decide (p.2 ∈ S))).length

@[fun_prop]
private theorem computableInPolyTime_cutCountBool :
    ComputableInPolyTime (fun p : Graph × List ℕ ↦ cutCountBool p.1 p.2)
      (encPair encGraph (encList encNat)) encUnary := by
  unfold cutCountBool
  refine (length_list (encPair encNat encNat)).comp (filterWithInput ?_ ?_)
  · exact flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))
  · fun_prop

private lemma cutCountBool_eq_card_interedges (G : Graph) (S : Finset ℕ) {l : List ℕ}
    (_hl : l.Nodup) (hSl : l.toFinset = S) :
    cutCountBool G l =
      (G.induced.interedges (S.subtype (· ∈ G.vertices))
        (S.subtype (· ∈ G.vertices))ᶜ).card := by
  unfold cutCountBool
  have hnodup_pairs :
      (G.distinctVertices.flatMap fun u ↦ G.distinctVertices.map fun v ↦ (u, v)).Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun u _ ↦ G.nodup_distinctVertices.map fun a b h ↦
      (Prod.mk.inj h).2, ?_⟩
    refine G.nodup_distinctVertices.pairwise_of_forall_ne fun u _ v _ huv p hp1 hp2 ↦ ?_
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp1
    obtain ⟨b, _, hEq⟩ := List.mem_map.mp hp2
    exact huv (Prod.mk.inj hEq).1.symm
  symm
  refine SimpleMaxCut.card_interedges_eq_length G S (hnodup_pairs.filter _) fun p ↦ ?_
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, Graph.mem_distinctVertices,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    Graph.adjBool_eq_true_iff]
  have hmemS : ∀ v, v ∈ l ↔ v ∈ S := fun v ↦ by rw [← hSl, List.mem_toFinset]
  constructor
  · rintro ⟨⟨u, hu, v, hv, rfl⟩, hadj, huS, hvS⟩
    exact ⟨hu, hv, hadj, (hmemS u).mp huS, fun h ↦ hvS ((hmemS v).mpr h)⟩
  · rintro ⟨hp1, hp2, hadj, hp1S, hp2S⟩
    exact ⟨⟨p.1, hp1, p.2, hp2, rfl⟩, hadj, (hmemS p.1).mpr hp1S, fun h ↦ hp2S ((hmemS p.2).mp h)⟩

theorem mem_iff_finset {x : MinimumBisectionInstance} :
    x ∈ MinimumBisection ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
        (2 * S.card = x.graph.distinctVertices.length ∧
          (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
            (S.subtype (· ∈ x.graph.vertices))ᶜ).card ≤ x.bound) := by
  rw [MinimumBisection, Set.mem_ofPred_eq, Graph.card_vertexSubtype,
    ← Graph.length_distinctVertices]
  constructor
  · rintro ⟨T, hcard, hcut⟩
    refine ⟨T.map (Function.Embedding.subtype _), fun v hv ↦ ?_, ?_, ?_⟩
    · obtain ⟨u, _, rfl⟩ := mem_map.mp hv; exact u.2
    · rwa [card_map]
    · have hT : (T.map (Function.Embedding.subtype _)).subtype (· ∈ x.graph.vertices) = T := by
        ext u; simp [u.2]
      rwa [hT]
  · rintro ⟨S, hSV, hcard, hcut⟩
    refine ⟨S.subtype (· ∈ x.graph.vertices), ?_, hcut⟩
    have hcard_sub : (S.subtype (· ∈ x.graph.vertices)).card = S.card := by
      rw [← card_map (Function.Embedding.subtype _), subtype_map, filter_eq_self.mpr hSV]
    rwa [hcard_sub]

/-- `MinimumBisection` belongs to `NP`. -/
theorem mem_NP : MinimumBisection ∈ NP encMinimumBisection := by
  have hset : MinimumBisection = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      (2 * S.card = x.graph.distinctVertices.length ∧
        (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
          (S.subtype (· ∈ x.graph.vertices))ᶜ).card ≤ x.bound)} :=
    Set.ext fun _ ↦ mem_iff_finset
  rw [hset]
  let EW := encWithEntries encMinimumBisection encNat
  have hG : ComputableInPolyTime (fun y : MinimumBisectionInstance × List ℕ ↦ y.1.graph)
      EW encGraph := encMinimumBisection_graph_polyTime (fst _ _)
  have hB : ComputableInPolyTime (fun y : MinimumBisectionInstance × List ℕ ↦ y.1.bound)
      EW encNat := encMinimumBisection_bound_polyTime (fst _ _)
  have hL : ComputableInPolyTime (fun y : MinimumBisectionInstance × List ℕ ↦ y.2)
      EW (encList encNat) := snd _ _
  refine mem_NP_of_subsetWitness (encγ := encNat)
    (vs := fun x : MinimumBisectionInstance ↦ x.graph.vertices)
    (check := fun y ↦
      decide (2 * y.2.length = y.1.graph.distinctVertices.length) &&
      decide (cutCountBool y.1.graph y.2 ≤ y.1.bound))
    (by fun_prop)
    (bool_and'
      (decide_eq'
        (binary_mul' (const 2) (unary_to_binary.comp ((length_list encNat).comp hL)))
        (unary_to_binary.comp
          ((length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hG))))
      (binary_le'
        (unary_to_binary.comp (computableInPolyTime_cutCountBool.comp (hG.prod hL)))
        hB))
    fun x l hl _ ↦ ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.toFinset_card_of_nodup hl,
    cutCountBool_eq_card_interedges x.graph l.toFinset hl rfl]

/-- Fixed accepted `MinimumBisection` instance (`2` isolated vertices, `bound = 0`). -/
def yesInstance : MinimumBisectionInstance :=
  ⟨⟨[0, 1], []⟩, 0⟩

private theorem yesInstance_mem : yesInstance ∈ MinimumBisection := by
  rw [mem_iff_finset]
  refine ⟨{0}, ?_, ?_, ?_⟩
  · simp [yesInstance]
  · decide
  · change (yesInstance.graph.induced.interedges
        (({0} : Finset ℕ).subtype (· ∈ yesInstance.graph.vertices))
        (({0} : Finset ℕ).subtype (· ∈ yesInstance.graph.vertices))ᶜ).card ≤ 0
    rw [Nat.le_zero, card_eq_zero, eq_empty_iff_forall_notMem]
    rintro ⟨u, v⟩ h
    rw [SimpleGraph.mem_interedges_iff] at h
    have hadj : yesInstance.graph.toSimpleGraph.Adj u.1 v.1 := h.2.2
    rw [Graph.toSimpleGraph_adj] at hadj
    rcases hadj.2 with h1 | h2
    · exact List.not_mem_nil h1
    · exact List.not_mem_nil h2

/-- Fixed rejected `MinimumBisection` instance (`1` vertex, odd order). -/
def noInstance : MinimumBisectionInstance :=
  ⟨⟨[0], []⟩, 0⟩

private theorem noInstance_notMem : noInstance ∉ MinimumBisection := by
  rw [mem_iff_finset]
  rintro ⟨S, _, hcard, _⟩
  have hlen : noInstance.graph.distinctVertices.length = 1 := by decide
  omega

/-- Padded graph `G ⊔ K̄_n`: copies `2 * v` of declared vertices `v` of `G` with their edges,
together with `n = |V(G)|` isolated vertices `2 * i + 1` (`i < n`). -/
def paddedGraph (G : Graph) : Graph :=
  let vs := G.distinctVertices
  ⟨vs.map (2 * ·) ++ (List.range vs.length).map (fun i ↦ 2 * i + 1),
    (G.edges.filter fun e ↦ decide (e.1 ∈ vs ∧ e.2 ∈ vs ∧ e.1 ≠ e.2)).map
      fun e ↦ (2 * e.1, 2 * e.2)⟩

@[fun_prop]
private theorem computableInPolyTime_paddedGraph :
    ComputableInPolyTime paddedGraph encGraph encGraph := by
  have hvs : ComputableInPolyTime Graph.distinctVertices encGraph (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices
  have hV1 : ComputableInPolyTime (fun G : Graph ↦ G.distinctVertices.map (2 * ·))
      encGraph (encList encNat) :=
    mapWithInput hvs (binary_mul' (const 2) (snd _ _))
  have hV2 : ComputableInPolyTime
      (fun G : Graph ↦ (List.range G.distinctVertices.length).map fun i ↦ 2 * i + 1)
      encGraph (encList encNat) :=
    mapWithInput (ComputableInPolyTime.range.comp ((length_list encNat).comp hvs))
      (binary_add' (binary_mul' (const 2) (unary_to_binary.comp (snd _ _))) (const 1))
  have hE : ComputableInPolyTime
      (fun G : Graph ↦
        (G.edges.filter fun e ↦
          decide (e.1 ∈ G.distinctVertices ∧ e.2 ∈ G.distinctVertices ∧ e.1 ≠ e.2)).map
            fun e ↦ (2 * e.1, 2 * e.2))
      encGraph (encList (encPair encNat encNat)) := by
    refine mapWithInput (filterWithInput (encGraph_edges_polyTime id') ?_) ?_
    · fun_prop
    · exact ((binary_mul' (const 2) ((fst encNat encNat).comp (snd _ _))).prod
        (binary_mul' (const 2) ((snd encNat encNat).comp (snd _ _))))
  unfold paddedGraph
  dsimp only
  exact encGraph_mk_polyTime (listAppend' hV1 hV2) hE

/-- Polynomial-time reduction from `SimpleMaxCut` to `MinimumBisection`. -/
def fromSimpleMaxCut (x : SimpleMaxCutInstance) : MinimumBisectionInstance :=
  let n := x.graph.distinctVertices.length
  if decide (n = 0) then
    if decide (x.bound = 0) then yesInstance else noInstance
  else if decide (x.bound ≤ n * n) then
    ⟨(paddedGraph x.graph).compl, n * n - x.bound⟩
  else noInstance

@[fun_prop]
private theorem computableInPolyTime_fromSimpleMaxCut :
    ComputableInPolyTime fromSimpleMaxCut encSimpleMaxCut encMinimumBisection := by
  have hG : ComputableInPolyTime SimpleMaxCutInstance.graph encSimpleMaxCut encGraph :=
    encSimpleMaxCut_graph_polyTime id'
  have hB : ComputableInPolyTime SimpleMaxCutInstance.bound encSimpleMaxCut encNat :=
    encSimpleMaxCut_bound_polyTime id'
  have hn_un : ComputableInPolyTime
      (fun x : SimpleMaxCutInstance ↦ x.graph.distinctVertices.length)
      encSimpleMaxCut encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hG)
  have hn_bin : ComputableInPolyTime
      (fun x : SimpleMaxCutInstance ↦ x.graph.distinctVertices.length)
      encSimpleMaxCut encNat := unary_to_binary.comp hn_un
  have hnn : ComputableInPolyTime
      (fun x : SimpleMaxCutInstance ↦
        x.graph.distinctVertices.length * x.graph.distinctVertices.length)
      encSimpleMaxCut encNat := binary_mul' hn_bin hn_bin
  unfold fromSimpleMaxCut
  dsimp only
  exact ite' (decide_eq' hn_un (const 0))
    (ite' (decide_eq' hB (const 0))
      (const yesInstance) (const noInstance))
    (ite' (binary_le' hB hnn)
      (encMinimumBisection_mk_polyTime
        (Graph.computableInPolyTime_compl.comp (computableInPolyTime_paddedGraph.comp hG))
        (binary_sub' hnn hB))
      (const noInstance))

private lemma paddedGraph_vertices_nodup (G : Graph) : (paddedGraph G).vertices.Nodup := by
  unfold paddedGraph
  dsimp only
  refine List.nodup_append.mpr ⟨G.nodup_distinctVertices.map fun a b h ↦ by omega,
    List.nodup_range.map fun a b h ↦ by omega, ?_⟩
  intro u hu v hv hEq
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
  omega

private lemma mem_paddedGraph_vertices {G : Graph} {w : ℕ} :
    w ∈ (paddedGraph G).vertices ↔
      (∃ v ∈ G.vertices, 2 * v = w) ∨ (∃ i < G.distinctVertices.length, 2 * i + 1 = w) := by
  unfold paddedGraph
  simp [Graph.mem_distinctVertices]

private lemma paddedGraph_adj_iff {G : Graph} {a b : ℕ} :
    (paddedGraph G).toSimpleGraph.Adj a b ↔
      ∃ u ∈ G.vertices, ∃ v ∈ G.vertices, a = 2 * u ∧ b = 2 * v ∧ G.toSimpleGraph.Adj u v := by
  rw [Graph.toSimpleGraph_adj]
  unfold paddedGraph
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Graph.mem_distinctVertices,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hne, (⟨e, ⟨he, he1, he2, _⟩, rfl, rfl⟩ | ⟨e, ⟨he, he1, he2, _⟩, rfl, rfl⟩)⟩
    · exact ⟨e.1, he1, e.2, he2, rfl, rfl, Graph.toSimpleGraph_adj.mpr ⟨by omega, Or.inl he⟩⟩
    · exact ⟨e.2, he2, e.1, he1, rfl, rfl, Graph.toSimpleGraph_adj.mpr ⟨by omega, Or.inr he⟩⟩
  · rintro ⟨u, hu, v, hv, rfl, rfl, hadj⟩
    obtain ⟨huv, he | he⟩ := Graph.toSimpleGraph_adj.mp hadj
    · exact ⟨by omega, Or.inl ⟨(u, v), ⟨he, hu, hv, huv⟩, rfl, rfl⟩⟩
    · exact ⟨by omega, Or.inr ⟨(v, u), ⟨he, hv, hu, huv.symm⟩, rfl, rfl⟩⟩

private lemma interedges_compl_add {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    (Hᶜ.interedges S Sᶜ).card + (H.interedges S Sᶜ).card = S.card * (Sᶜ : Finset V).card := by
  rw [← card_product]
  have hdisj : Disjoint (Hᶜ.interedges S Sᶜ) (H.interedges S Sᶜ) := by
    refine Finset.disjoint_left.mpr fun p hp1 hp2 ↦ ?_
    rw [SimpleGraph.mem_interedges_iff] at hp1 hp2
    exact hp1.2.2.2 hp2.2.2
  have hunion : Hᶜ.interedges S Sᶜ ∪ H.interedges S Sᶜ = S ×ˢ Sᶜ := by
    ext ⟨u, v⟩
    simp only [mem_union, SimpleGraph.mem_interedges_iff, mem_product, mem_compl,
      SimpleGraph.compl_adj]
    constructor
    · rintro (⟨hu, hv, _⟩ | ⟨hu, hv, _⟩) <;> exact ⟨hu, hv⟩
    · rintro ⟨hu, hv⟩
      have hne : u ≠ v := fun h ↦ hv (h ▸ hu)
      by_cases hadj : H.Adj u v
      · exact Or.inr ⟨hu, hv, hadj⟩
      · exact Or.inl ⟨hu, hv, hne, hadj⟩
  rw [← card_union_of_disjoint hdisj, hunion]

private lemma card_interedges_graph_compl (H : Graph) (S : Finset {w // w ∈ H.vertices}) :
    (@SimpleGraph.interedges {w // w ∈ H.vertices} H.compl.induced
        (Graph.instDecidableRelInducedAdj H.compl) S Sᶜ).card +
        (H.induced.interedges S Sᶜ).card =
      S.card * (Sᶜ : Finset {w // w ∈ H.vertices}).card := by
  have heq : @SimpleGraph.interedges {w // w ∈ H.vertices} H.compl.induced
        (Graph.instDecidableRelInducedAdj H.compl) S Sᶜ =
      H.inducedᶜ.interedges S Sᶜ := by
    apply Finset.ext
    rintro ⟨u, v⟩
    refine (@SimpleGraph.mem_interedges_iff {w // w ∈ H.vertices} H.compl.induced
      (Graph.instDecidableRelInducedAdj H.compl) S Sᶜ (u, v)).trans ?_
    refine (and_congr_right fun _ ↦ and_congr_right fun _ ↦
      (Graph.compl_adj_iff u.2 v.2).trans
        ((and_congr_left' Subtype.ext_iff.not.symm).trans
          (H.induced.compl_adj u v).symm)).trans
      (SimpleGraph.mem_interedges_iff H.inducedᶜ).symm
  rw [heq]
  exact interedges_compl_add H.induced S

theorem fromSimpleMaxCut_mem_iff (x : SimpleMaxCutInstance) :
    fromSimpleMaxCut x ∈ MinimumBisection ↔ x ∈ SimpleMaxCut := by
  unfold fromSimpleMaxCut
  set G := x.graph
  set n := G.distinctVertices.length
  by_cases hn0 : n = 0
  · simp only [decide_eq_true hn0, ↓reduceIte]
    have hV_empty : IsEmpty {v // v ∈ G.vertices} := by
      rw [← Fintype.card_eq_zero_iff, Graph.card_vertexSubtype, ← Graph.length_distinctVertices]
      exact hn0
    by_cases hb0 : x.bound = 0
    · simp only [decide_eq_true hb0, ↓reduceIte]
      exact ⟨fun _ ↦ ⟨∅, by simp [hb0]⟩, fun _ ↦ yesInstance_mem⟩
    · simp only [decide_eq_false hb0, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun h ↦ (noInstance_notMem h).elim, fun ⟨S, hS⟩ ↦ ?_⟩
      change x.bound ≤ (G.induced.interedges S Sᶜ).card at hS
      have h0 : (G.induced.interedges S Sᶜ).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        rintro ⟨u, _⟩ _
        exact hV_empty.false u
      omega
  · simp only [decide_eq_false hn0, Bool.false_eq_true, ↓reduceIte]
    by_cases hble : x.bound ≤ n * n
    · simp only [decide_eq_true hble, ↓reduceIte]
      let H₀ := paddedGraph G
      change (∃ Ŝ : Finset {w // w ∈ H₀.vertices},
          2 * Ŝ.card = Fintype.card {w // w ∈ H₀.vertices} ∧
          (@SimpleGraph.interedges {w // w ∈ H₀.vertices} H₀.compl.induced
            (Graph.instDecidableRelInducedAdj H₀.compl) Ŝ Ŝᶜ).card ≤
            n * n - x.bound) ↔
        ∃ S : Finset {v // v ∈ G.vertices}, x.bound ≤ (G.induced.interedges S Sᶜ).card
      have hH₀_card : Fintype.card {w // w ∈ H₀.vertices} = 2 * n := by
        rw [Graph.card_vertexSubtype, List.toFinset_card_of_nodup (paddedGraph_vertices_nodup G)]
        dsimp [H₀, paddedGraph]
        simp [n]
        omega
      let embEven : {v // v ∈ G.vertices} ↪ {w // w ∈ H₀.vertices} :=
        ⟨fun v ↦ ⟨2 * v.1, mem_paddedGraph_vertices.mpr (Or.inl ⟨v.1, v.2, rfl⟩)⟩,
          fun u v h ↦ Subtype.ext (by have := congrArg Subtype.val h; dsimp at this; omega)⟩
      have hcut_eq : ∀ (Ŝ : Finset {w // w ∈ H₀.vertices}),
          (H₀.induced.interedges Ŝ Ŝᶜ).card =
            (G.induced.interedges (Ŝ.preimage embEven embEven.injective.injOn)
              (Ŝ.preimage embEven embEven.injective.injOn)ᶜ).card := by
        intro Ŝ
        let S := Ŝ.preimage embEven embEven.injective.injOn
        let f : {v // v ∈ G.vertices} × {v // v ∈ G.vertices} ↪
            {w // w ∈ H₀.vertices} × {w // w ∈ H₀.vertices} :=
          embEven.prodMap embEven
        rw [← card_map f]
        congr 1
        ext ⟨a, b⟩
        simp only [SimpleGraph.mem_interedges_iff, mem_compl, Graph.induced_adj, mem_map,
          Prod.exists]
        constructor
        · rintro ⟨haŜ, hbŜ, hadj⟩
          obtain ⟨u, hu, v, hv, hau, hbv, huv⟩ := paddedGraph_adj_iff.mp hadj
          have ha_eq : embEven ⟨u, hu⟩ = a := Subtype.ext hau.symm
          have hb_eq : embEven ⟨v, hv⟩ = b := Subtype.ext hbv.symm
          refine ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨?_, ?_, huv⟩, Prod.ext ha_eq hb_eq⟩
          · rw [mem_preimage, ha_eq]; exact haŜ
          · rw [mem_preimage, hb_eq]; exact hbŜ
        · rintro ⟨u, v, ⟨huS, hvS, huv⟩, hEq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          refine ⟨by simpa [S] using huS, by simpa [S] using hvS, ?_⟩
          exact paddedGraph_adj_iff.mpr ⟨u.1, u.2, v.1, v.2, rfl, rfl, huv⟩
      constructor
      · rintro ⟨Ŝ, hŜ_bisect, hŜ_cut⟩
        rw [hH₀_card] at hŜ_bisect
        have hŜ_card : Ŝ.card = n := by omega
        have hŜc_card : (Ŝᶜ : Finset {w // w ∈ H₀.vertices}).card = n := by
          have := card_compl Ŝ
          rw [hH₀_card, hŜ_card] at this
          omega
        have hcomp := card_interedges_graph_compl H₀ Ŝ
        rw [hŜ_card, hŜc_card, hcut_eq Ŝ] at hcomp
        exact ⟨Ŝ.preimage embEven embEven.injective.injOn, by omega⟩
      · rintro ⟨S, hScut⟩
        have hS_le : S.card ≤ n := by
          calc
            S.card ≤ Fintype.card {v // v ∈ G.vertices} := card_le_univ S
            _ = n := by rw [Graph.card_vertexSubtype, ← Graph.length_distinctVertices]
        let embOdd : Fin n ↪ {w // w ∈ H₀.vertices} :=
          ⟨fun i ↦ ⟨2 * i.1 + 1, mem_paddedGraph_vertices.mpr (Or.inr ⟨i.1, i.2, rfl⟩)⟩,
            fun i j h ↦ Fin.ext (by have := congrArg Subtype.val h; dsimp at this; omega)⟩
        let oddPad : Finset {w // w ∈ H₀.vertices} :=
          (Finset.range (n - S.card)).attach.image fun i ↦
            embOdd ⟨i.1, (Finset.mem_range.mp i.2).trans_le (Nat.sub_le n S.card)⟩
        have hodd_card : oddPad.card = n - S.card := by
          dsimp [oddPad]
          rw [card_image_of_injective _ fun i j h ↦ Subtype.ext (by
            have := congrArg Fin.val (embOdd.injective h); simpa using this)]
          rw [card_attach, card_range]
        have hdisj_eo : Disjoint (S.map embEven) oddPad := by
          refine Finset.disjoint_left.mpr fun w hw1 hw2 ↦ ?_
          obtain ⟨u, _, rfl⟩ := mem_map.mp hw1
          obtain ⟨i, _, hEq⟩ := mem_image.mp hw2
          have hval : 2 * i.1 + 1 = 2 * u.1 := congrArg Subtype.val hEq
          omega
        let Ŝ : Finset {w // w ∈ H₀.vertices} := S.map embEven ∪ oddPad
        have hŜ_card : Ŝ.card = n := by
          dsimp [Ŝ]
          rw [card_union_of_disjoint hdisj_eo, card_map, hodd_card]
          omega
        have hpre : Ŝ.preimage embEven embEven.injective.injOn = S := by
          ext u
          simp only [mem_preimage, Ŝ, mem_union, mem_map]
          constructor
          · rintro (⟨v, hv, hEq⟩ | hodd)
            · exact embEven.injective hEq ▸ hv
            · obtain ⟨i, _, hEq⟩ := mem_image.mp hodd
              have hval : 2 * i.1 + 1 = 2 * u.1 := congrArg Subtype.val hEq
              omega
          · intro hu
            exact Or.inl ⟨u, hu, rfl⟩
        refine ⟨Ŝ, by rw [hH₀_card, hŜ_card], ?_⟩
        have hŜc_card : (Ŝᶜ : Finset {w // w ∈ H₀.vertices}).card = n := by
          have := card_compl Ŝ
          rw [hH₀_card, hŜ_card] at this
          omega
        have hcomp := card_interedges_graph_compl H₀ Ŝ
        rw [hŜ_card, hŜc_card, hcut_eq Ŝ, hpre] at hcomp
        omega
    · simp only [decide_eq_false hble, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun h ↦ (noInstance_notMem h).elim, fun ⟨S, hScut⟩ ↦ ?_⟩
      change x.bound ≤ (G.induced.interedges S Sᶜ).card at hScut
      have hcardV : Fintype.card {v // v ∈ G.vertices} = n := by
        rw [Graph.card_vertexSubtype, ← Graph.length_distinctVertices]
      have hmax : (G.induced.interedges S Sᶜ).card ≤ n * n := by
        calc
          (G.induced.interedges S Sᶜ).card ≤ (S ×ˢ Sᶜ).card :=
            card_le_card fun ⟨u, v⟩ hp ↦ by
              rw [SimpleGraph.mem_interedges_iff] at hp
              exact mem_product.mpr ⟨hp.1, hp.2.1⟩
          _ = S.card * (Sᶜ : Finset _).card := card_product S Sᶜ
          _ ≤ n * n := Nat.mul_le_mul ((card_le_univ S).trans_eq hcardV)
            ((card_le_univ Sᶜ).trans_eq hcardV)
      omega

end MinimumBisection

/-- `SimpleMaxCut` reduces in polynomial time to `MinimumBisection`. -/
theorem polyTimeReducible_SimpleMaxCut_MinimumBisection :
    PolyTimeReducible encSimpleMaxCut encMinimumBisection SimpleMaxCut MinimumBisection :=
  ⟨MinimumBisection.fromSimpleMaxCut, MinimumBisection.computableInPolyTime_fromSimpleMaxCut,
    fun x ↦ (MinimumBisection.fromSimpleMaxCut_mem_iff x).symm⟩

/-- `MinimumBisection` is `NP`-hard. -/
theorem MinimumBisection_npHard : NPHard encMinimumBisection MinimumBisection :=
  SimpleMaxCut_npHard.trans polyTimeReducible_SimpleMaxCut_MinimumBisection

/-- **Minimum Bisection is `NP`-complete.** -/
theorem MinimumBisection_npComplete : NPComplete encMinimumBisection MinimumBisection :=
  ⟨MinimumBisection.mem_NP, MinimumBisection_npHard⟩

/-! ### 3. Fixed-Density Connected Subgraph (`FixedDensityConnectedSubgraph`) -/

/-- An instance `(graph, size, minEdges)` of **Fixed-Density Connected Subgraph (FDCS)**. -/
@[ext]
structure FDCSInstance where
  /-- Host undirected graph. -/
  graph : Graph
  /-- Target vertex count `s`. -/
  size : ℕ
  /-- Minimum required induced edge count `τ`. -/
  minEdges : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `FDCSInstance`. -/
enc_structure encFDCS : FDCSInstance where
  graph : encGraph,
  size : encNat,
  minEdges : encNat

attribute [fun_prop] encFDCS_graph_polyTime encFDCS_size_polyTime
  encFDCS_minEdges_polyTime encFDCS_mk_polyTime

/-- Number of undirected edges of `G` with both endpoints in `S`. -/
@[expose]
def inducedEdgesCount {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S.powersetCard 2).filter fun e ↦ ∃ u ∈ e, ∃ v ∈ e, G.Adj u v).card

/-- **Fixed-Density Connected Subgraph (FDCS)**: graphs containing a connected `s`-vertex induced
subgraph with at least `τ` induced edges. -/
@[expose]
def FixedDensityConnectedSubgraph : Set FDCSInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices},
    S.card = x.size ∧
    (x.graph.induced.induce (S : Set {v // v ∈ x.graph.vertices})).Connected ∧
    x.minEdges ≤ inducedEdgesCount x.graph.induced S}

namespace FixedDensityConnectedSubgraph

private def orderedAdjPairsCount (G : Graph) (l : List ℕ) : ℕ :=
  ((l.flatMap fun u ↦ l.map fun v ↦ (u, v)).filter fun p ↦ G.adjBool p.1 p.2).length

@[fun_prop]
private theorem computableInPolyTime_orderedAdjPairsCount :
    ComputableInPolyTime (fun p : Graph × List ℕ ↦ orderedAdjPairsCount p.1 p.2)
      (encPair encGraph (encList encNat)) encUnary := by
  unfold orderedAdjPairsCount
  refine (length_list (encPair encNat encNat)).comp (filterWithInput ?_ ?_)
  · exact flatMapWithInput (snd _ _) (mapWithInput ((snd _ _).comp (fst _ _))
      (((snd _ _).comp (fst _ _)).prod (snd _ _)))
  · exact Graph.computableInPolyTime_adjBool_comp ((fst _ _).comp (fst _ _))
      ((fst _ _).comp (snd _ _)) ((snd _ _).comp (snd _ _))

private lemma orderedAdjPairsCount_eq_two_mul_inducedEdges (G : Graph) {l : List ℕ}
    (hl : l.Nodup) (hV : ∀ v ∈ l, v ∈ G.vertices) :
    orderedAdjPairsCount G l =
      2 * inducedEdgesCount G.induced (l.toFinset.subtype (· ∈ G.vertices)) := by
  unfold orderedAdjPairsCount inducedEdgesCount
  set S : Finset {v // v ∈ G.vertices} := l.toFinset.subtype (· ∈ G.vertices)
  have hnodup : (l.flatMap fun u ↦ l.map fun v ↦ (u, v)).Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun u _ ↦ hl.map fun a b h ↦ (Prod.mk.inj h).2, ?_⟩
    refine hl.pairwise_of_forall_ne fun u _ v _ huv p hp1 hp2 ↦ ?_
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp1
    obtain ⟨b, _, hEq⟩ := List.mem_map.mp hp2
    exact huv (Prod.mk.inj hEq).1.symm
  rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
  let E2 := (S.powersetCard 2).filter fun e ↦ ∃ u ∈ e, ∃ v ∈ e, G.induced.Adj u v
  let ordPairs : Finset (ℕ × ℕ) :=
    E2.biUnion fun e ↦ ((e ×ˢ e).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ (p.1.1, p.2.1)
  have heq_set :
      ((l.flatMap fun u ↦ l.map fun v ↦ (u, v)).filter fun p ↦ G.adjBool p.1 p.2).toFinset =
      ordPairs := by
    ext ⟨a, b⟩
    simp only [List.mem_toFinset, List.mem_filter, List.mem_flatMap, List.mem_map,
      Graph.adjBool_eq_true_iff, ordPairs, mem_biUnion, mem_image, mem_filter, mem_product,
      Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨u, hu, v, hv, rfl, rfl⟩, hadj⟩
      let ua : {x // x ∈ G.vertices} := ⟨u, hV u hu⟩
      let vb : {x // x ∈ G.vertices} := ⟨v, hV v hv⟩
      have huaS : ua ∈ S := by simp [S, ua, hu]
      have hvbS : vb ∈ S := by simp [S, vb, hv]
      have huv_ne : ua ≠ vb := fun h ↦ hadj.ne (congrArg Subtype.val h)
      refine ⟨{ua, vb}, ?_, ua, vb,
        ⟨⟨mem_insert_self _ _, mem_insert_of_mem (mem_singleton_self _)⟩, huv_ne⟩, rfl, rfl⟩
      simp only [E2, mem_filter, mem_powersetCard]
      exact ⟨⟨insert_subset_iff.mpr ⟨huaS, singleton_subset_iff.mpr hvbS⟩, card_pair huv_ne⟩,
        ua, mem_insert_self _ _, vb, mem_insert_of_mem (mem_singleton_self _), hadj⟩
    · rintro ⟨e, he, ua, vb, ⟨⟨huae, hvbe⟩, hne⟩, rfl, rfl⟩
      simp only [E2, mem_filter, mem_powersetCard] at he
      rcases he with ⟨⟨heS, hcard2⟩, u', hu'e, v', hv'e, hadj'⟩
      have hua_mem : ua.1 ∈ l := by have := heS huae; simpa [S] using this
      have hvb_mem : vb.1 ∈ l := by have := heS hvbe; simpa [S] using this
      refine ⟨⟨ua.1, hua_mem, vb.1, hvb_mem, rfl, rfl⟩, ?_⟩
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard2
      have hpair : ({ua, vb} : Finset _) = {x, y} :=
        eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨huae, singleton_subset_iff.mpr hvbe⟩)
          (by rw [card_pair hxy, card_pair hne])
      have hpair' : ({u', v'} : Finset _) = {x, y} :=
        eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hu'e, singleton_subset_iff.mpr hv'e⟩)
          (by rw [card_pair hxy, card_pair hadj'.ne])
      have hEq := hpair.trans hpair'.symm
      have hua_in : ua ∈ ({u', v'} : Finset _) := hEq ▸ mem_insert_self ua {vb}
      have hvb_in : vb ∈ ({u', v'} : Finset _) :=
        hEq ▸ mem_insert_of_mem (mem_singleton_self vb)
      simp only [mem_insert, mem_singleton] at hua_in hvb_in
      rcases hua_in with rfl | rfl <;> rcases hvb_in with rfl | rfl
      · exact (hne rfl).elim
      · exact hadj'
      · exact hadj'.symm
      · exact (hne rfl).elim
  rw [heq_set]
  have hpw : (E2 : Set (Finset {v // v ∈ G.vertices})).PairwiseDisjoint
      (fun e ↦ ((e ×ˢ e).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ (p.1.1, p.2.1)) := by
    intro e₁ he₁ e₂ he₂ hne
    refine Finset.disjoint_left.mpr fun q hq1 hq2 ↦ hne ?_
    obtain ⟨⟨u₁, v₁⟩, hp1, hEq1⟩ := mem_image.mp hq1
    obtain ⟨⟨u₂, v₂⟩, hp2, hEq2⟩ := mem_image.mp hq2
    have hu_eq : u₁ = u₂ := Subtype.ext (Prod.mk.inj (hEq1.trans hEq2.symm)).1
    have hv_eq : v₁ = v₂ := Subtype.ext (Prod.mk.inj (hEq1.trans hEq2.symm)).2
    subst hu_eq hv_eq
    simp only [mem_filter, mem_product] at hp1 hp2
    have he₁' : e₁ ∈ E2 := he₁
    have he₂' : e₂ ∈ E2 := he₂
    simp only [E2, mem_filter, mem_powersetCard] at he₁' he₂'
    have h1 : ({u₁, v₁} : Finset _) = e₁ :=
      eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hp1.1.1, singleton_subset_iff.mpr hp1.1.2⟩)
        (by rw [he₁'.1.2, card_pair hp1.2])
    have h2 : ({u₁, v₁} : Finset _) = e₂ :=
      eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hp2.1.1, singleton_subset_iff.mpr hp2.1.2⟩)
        (by rw [he₂'.1.2, card_pair hp2.2])
    exact h1.symm.trans h2
  dsimp [ordPairs]
  rw [card_biUnion hpw]
  have h2 : ∀ e ∈ E2,
      (((e ×ˢ e).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ (p.1.1, p.2.1)).card = 2 := by
    intro e he
    simp only [E2, mem_filter, mem_powersetCard] at he
    obtain ⟨⟨_, hcard2⟩, _⟩ := he
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard2
    rw [card_image_of_injOn (fun p₁ _ p₂ _ h ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).1)
      (Subtype.ext (Prod.mk.inj h).2))]
    have hfilt :
        ((({x, y} : Finset _) ×ˢ ({x, y} : Finset _)).filter fun p ↦ p.1 ≠ p.2) =
          {(x, y), (y, x)} := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl | rfl, rfl | rfl⟩, hne⟩
        · exact (hne rfl).elim
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact (hne rfl).elim
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨Or.inl rfl, Or.inr rfl⟩, hxy⟩
        · exact ⟨⟨Or.inr rfl, Or.inl rfl⟩, hxy.symm⟩
    rw [hfilt, card_pair (fun h ↦ hxy (Prod.mk.inj h).1)]
  rw [sum_congr rfl h2, sum_const, smul_eq_mul, Nat.mul_comm]

private lemma induce_subtype_connected_iff (G : Graph) {S : Finset ℕ}
    (hSV : ∀ v ∈ S, v ∈ G.vertices) :
    (G.induced.induce ((S.subtype (· ∈ G.vertices)) : Set {v // v ∈ G.vertices})).Connected ↔
      (G.toSimpleGraph.induce {v | v ∈ S}).Connected := by
  let iso : G.induced.induce ((S.subtype (· ∈ G.vertices)) : Set {v // v ∈ G.vertices}) ≃g
      G.toSimpleGraph.induce {v | v ∈ S} :=
    { toFun := fun x ↦ ⟨x.1.1, Finset.mem_subtype.mp x.2⟩
      invFun := fun y ↦ ⟨⟨y.1, hSV y.1 y.2⟩, Finset.mem_coe.mpr (Finset.mem_subtype.mpr y.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }
  exact iso.connected_iff

/-- `FixedDensityConnectedSubgraph` belongs to `NP`. -/
theorem mem_NP : FixedDensityConnectedSubgraph ∈ NP encFDCS := by
  have hset : FixedDensityConnectedSubgraph =
      {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
        (S.card = x.size ∧
          (x.graph.induced.induce ((S.subtype (· ∈ x.graph.vertices)) : Set _)).Connected ∧
          x.minEdges ≤ inducedEdgesCount x.graph.induced (S.subtype (· ∈ x.graph.vertices)))} := by
    ext x
    simp only [FixedDensityConnectedSubgraph, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨T, hcard, hconn, hedg⟩
      let S := T.map (Function.Embedding.subtype _)
      have hSV : ∀ v ∈ S, v ∈ x.graph.vertices := fun v hv ↦ by
        obtain ⟨u, _, rfl⟩ := mem_map.mp hv; exact u.2
      have hST : S.subtype (· ∈ x.graph.vertices) = T := by ext u; simp [S, u.2]
      exact ⟨S, hSV, (card_map _).trans hcard, hST ▸ hconn, hST ▸ hedg⟩
    · rintro ⟨S, hSV, hcard, hconn, hedg⟩
      refine ⟨S.subtype (· ∈ x.graph.vertices), ?_, hconn, hedg⟩
      rw [← card_map (Function.Embedding.subtype _), subtype_map, filter_eq_self.mpr hSV]
      exact hcard
  rw [hset]
  let EW := encWithEntries encFDCS encNat
  have hG : ComputableInPolyTime (fun y : FDCSInstance × List ℕ ↦ y.1.graph) EW encGraph :=
    encFDCS_graph_polyTime (fst _ _)
  have hs : ComputableInPolyTime (fun y : FDCSInstance × List ℕ ↦ y.1.size) EW encNat :=
    encFDCS_size_polyTime (fst _ _)
  have hminE : ComputableInPolyTime (fun y : FDCSInstance × List ℕ ↦ y.1.minEdges) EW encNat :=
    encFDCS_minEdges_polyTime (fst _ _)
  have hL : ComputableInPolyTime (fun y : FDCSInstance × List ℕ ↦ y.2) EW (encList encNat) :=
    snd _ _
  refine mem_NP_of_subsetWitness (encγ := encNat)
    (vs := fun x : FDCSInstance ↦ x.graph.vertices)
    (check := fun y ↦
      decide (y.2.length = y.1.size) &&
      graphConnectedBool y.1.graph y.2 &&
      decide (2 * y.1.minEdges ≤ orderedAdjPairsCount y.1.graph y.2))
    (by fun_prop)
    (bool_and'
      (bool_and'
        (decide_eq' (unary_to_binary.comp ((length_list encNat).comp hL)) hs)
        (computableInPolyTime_graphConnectedBool.comp (hG.prod hL)))
      (binary_le'
        (binary_mul' (const 2) hminE)
        (unary_to_binary.comp (computableInPolyTime_orderedAdjPairsCount.comp (hG.prod hL)))))
    fun x l hl hsub ↦ ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.toFinset_card_of_nodup hl,
    graphConnectedBool_eq_true_iff, orderedAdjPairsCount_eq_two_mul_inducedEdges x.graph hl hsub,
    induce_subtype_connected_iff x.graph (fun v hv ↦ hsub v (List.mem_toFinset.mp hv)),
    and_assoc]
  have hmem_iff : {v | v ∈ l} = {v | v ∈ l.toFinset} := by ext v; simp
  rw [hmem_iff]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun h ↦ by omega, fun h ↦ by omega⟩

/-- Fixed accepted `FDCS` instance (`1` vertex, `s = 1`, `τ = 0`). -/
def yesInstance : FDCSInstance :=
  ⟨⟨[0], []⟩, 1, 0⟩

private theorem yesInstance_mem : yesInstance ∈ FixedDensityConnectedSubgraph := by
  refine ⟨univ, by decide, ?_, Nat.zero_le _⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v ↦ ?_, ⟨⟨⟨0, by simp [yesInstance]⟩, mem_univ _⟩⟩⟩
  have : u = v := Subtype.ext (Subtype.ext (by
    have hu := u.1.2
    have hv := v.1.2
    simp [yesInstance] at hu hv
    omega))
  subst this
  exact SimpleGraph.Reachable.refl u

/-- Fixed rejected `FDCS` instance (`empty` graph, `s = 1`, `τ = 0`). -/
def noInstance : FDCSInstance :=
  ⟨⟨[], []⟩, 1, 0⟩

private theorem noInstance_notMem : noInstance ∉ FixedDensityConnectedSubgraph := by
  rintro ⟨S, hcard, _, _⟩
  dsimp [noInstance] at S hcard
  obtain ⟨⟨v, hv⟩, _⟩ := card_pos.mp (by rw [hcard]; decide : 0 < S.card)
  exact List.not_mem_nil hv

/-- Polynomial-time reduction from `Clique` to `FixedDensityConnectedSubgraph`. -/
def fromClique (x : CliqueInstance) : FDCSInstance :=
  if decide (x.m = 0) then yesInstance
  else if decide (x.m = 1) then
    if x.graph.distinctVertices.isEmpty then noInstance else yesInstance
  else
    ⟨x.graph, x.m, x.m * (x.m - 1) / 2⟩

@[fun_prop]
private theorem computableInPolyTime_fromClique :
    ComputableInPolyTime fromClique encCliqueInstance encFDCS := by
  have hG : ComputableInPolyTime CliqueInstance.graph encCliqueInstance encGraph :=
    encCliqueInstance_graph_polyTime id'
  have hm : ComputableInPolyTime CliqueInstance.m encCliqueInstance encNat :=
    encCliqueInstance_m_polyTime id'
  unfold fromClique
  exact ite' (decide_eq' hm (const 0)) (const yesInstance)
    (ite' (decide_eq' hm (const 1))
      (ite' ((listIsEmpty' encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hG))
        (const noInstance) (const yesInstance))
      (encFDCS_mk_polyTime hG hm
        (binary_div' (binary_mul' hm (binary_sub' hm (const 1))) (const 2))))

theorem fromClique_mem_iff (x : CliqueInstance) :
    fromClique x ∈ FixedDensityConnectedSubgraph ↔ x ∈ Clique := by
  unfold fromClique
  by_cases hm0 : x.m = 0
  · simp only [decide_eq_true hm0, ↓reduceIte]
    exact ⟨fun _ ↦ ⟨∅, by simp [hm0, SimpleGraph.isNClique_iff]⟩, fun _ ↦ yesInstance_mem⟩
  · simp only [decide_eq_false hm0, Bool.false_eq_true, ↓reduceIte]
    by_cases hm1 : x.m = 1
    · simp only [decide_eq_true hm1, ↓reduceIte]
      by_cases hemp : x.graph.distinctVertices.isEmpty = true
      · simp only [hemp, ↓reduceIte]
        refine ⟨fun h ↦ (noInstance_notMem h).elim, fun ⟨S, hcl⟩ ↦ ?_⟩
        obtain ⟨v, _⟩ := card_pos.mp (by rw [hcl.card_eq, hm1]; decide)
        have hv' : v.1 ∈ x.graph.distinctVertices := Graph.mem_distinctVertices.mpr v.2
        rw [List.isEmpty_iff] at hemp
        simp [hemp] at hv'
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        have hne : x.graph.distinctVertices ≠ [] := fun h ↦ hemp (List.isEmpty_iff.mpr h)
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
        have hvV : v ∈ x.graph.vertices := Graph.mem_distinctVertices.mp hv
        exact ⟨fun _ ↦ ⟨{⟨v, hvV⟩}, by simp [hm1, SimpleGraph.isNClique_iff]⟩,
          fun _ ↦ yesInstance_mem⟩
    · simp only [decide_eq_false hm1, Bool.false_eq_true, ↓reduceIte]
      have hm_ge2 : 2 ≤ x.m := by omega
      constructor
      · rintro ⟨S, hScard, _, hedg⟩
        dsimp at S hScard hedg
        unfold inducedEdgesCount at hedg
        have hpow_card : (S.powersetCard 2).card = x.m * (x.m - 1) / 2 := by
          rw [card_powersetCard, hScard, Nat.choose_two_right]
        have hfilt_eq :=
          eq_of_subset_of_card_le (filter_subset _ _) (by rw [hpow_card]; exact hedg)
        refine ⟨S, ?_⟩
        rw [SimpleGraph.isNClique_iff]
        refine ⟨?_, hScard⟩
        intro u hu v hv huv
        have he_mem : ({u, v} : Finset _) ∈ S.powersetCard 2 :=
          mem_powersetCard.mpr
            ⟨insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩, card_pair huv⟩
        rw [← hfilt_eq, mem_filter] at he_mem
        rcases he_mem with ⟨_, a, ha, b, hb, hadj⟩
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (hadj.ne rfl).elim
        · exact hadj
        · exact hadj.symm
        · exact (hadj.ne rfl).elim
      · rintro ⟨S, hcl⟩
        rw [SimpleGraph.isNClique_iff] at hcl
        rcases hcl with ⟨hclique, hScard⟩
        obtain ⟨v₀, hv₀⟩ := card_pos.mp (by omega : 0 < S.card)
        refine ⟨S, hScard, ?_, ?_⟩
        · rw [SimpleGraph.connected_iff]
          refine ⟨fun u w ↦ ?_, ⟨⟨v₀, hv₀⟩⟩⟩
          by_cases huw : u = w
          · subst huw; exact SimpleGraph.Reachable.refl u
          · have hadj : (x.graph.induced.induce (S : Set _)).Adj u w :=
              hclique u.2 w.2 (Subtype.coe_ne_coe.mpr huw)
            exact hadj.reachable
        · change x.m * (x.m - 1) / 2 ≤ inducedEdgesCount x.graph.induced S
          unfold inducedEdgesCount
          rw [filter_true_of_mem, card_powersetCard, hScard, Nat.choose_two_right]
          intro e he
          obtain ⟨heS, hcard2⟩ := mem_powersetCard.mp he
          obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hcard2
          exact ⟨u, mem_insert_self _ _, v, mem_insert_of_mem (mem_singleton_self _),
            hclique (heS (mem_insert_self _ _))
              (heS (mem_insert_of_mem (mem_singleton_self _))) huv⟩

end FixedDensityConnectedSubgraph

/-- `Clique` reduces in polynomial time to `FixedDensityConnectedSubgraph`. -/
theorem polyTimeReducible_Clique_FixedDensityConnectedSubgraph :
    PolyTimeReducible encCliqueInstance encFDCS Clique FixedDensityConnectedSubgraph :=
  ⟨FixedDensityConnectedSubgraph.fromClique,
    FixedDensityConnectedSubgraph.computableInPolyTime_fromClique,
    fun x ↦ (FixedDensityConnectedSubgraph.fromClique_mem_iff x).symm⟩

/-- `FixedDensityConnectedSubgraph` is `NP`-hard. -/
theorem FixedDensityConnectedSubgraph_npHard : NPHard encFDCS FixedDensityConnectedSubgraph :=
  Clique_npHard.trans polyTimeReducible_Clique_FixedDensityConnectedSubgraph

/-- **Fixed-Density Connected Subgraph (FDCS) is `NP`-complete.** -/
theorem FixedDensityConnectedSubgraph_npComplete :
    NPComplete encFDCS FixedDensityConnectedSubgraph :=
  ⟨FixedDensityConnectedSubgraph.mem_NP, FixedDensityConnectedSubgraph_npHard⟩

end CslibFrontier.Computability.Complexity
