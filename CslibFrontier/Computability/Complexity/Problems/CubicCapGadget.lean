module

public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Tactic.FinCases

/-!
# Cubic Dominating Set and the One-Port Cubic Degree-Cap Gadget $W_7$

Defines `CslibFrontier.Complexity.CubicDominatingSet` (connected $3$-regular dominating set), proves
its membership in `NP`, and constructs the $7$-vertex $1$-port cubic degree-cap gadget $W_7$
($K_{3,3}$ with one edge subdivided by port `0`) together with its polynomial-time capping operator
`CslibFrontier.Complexity.cappedGraphOf` preserving connectedness, enforcing exact degree $3$, and
shifting the minimum dominating set cardinality by $+2$ per attached cap.

## Main definitions

- `CslibFrontier.Complexity.CubicDominatingSet`: connected $3$-regular instances of `DominatingSet`.
- `CslibFrontier.Complexity.w7Edges`, `CslibFrontier.Complexity.cubicCapV`,
  `CslibFrontier.Complexity.cappedGraphOf`: the $7$-vertex cubic cap gadget and capping operator.
- `CslibFrontier.Complexity.polyRange`, `CslibFrontier.Complexity.dedupList`: polynomial-time list
  helpers.

## Main results

- `CslibFrontier.Complexity.CubicDominatingSet.mem_NP`: `CubicDominatingSet ∈ NP encDominatingSet`.
- `CslibFrontier.Complexity.cappedGraphOf_cubic`,
  `CslibFrontier.Complexity.cappedGraphOf_connected`,
  `CslibFrontier.Complexity.cappedGraphOf_dom_iff`: exact degree-$3$ regularity, connectedness, and
  $+2$-per-cap domination shift of `cappedGraphOf`.
- `CslibFrontier.Complexity.computableInPolyTime_cappedGraphOf`: polynomial-time computability of
  `cappedGraphOf`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- **Connected Cubic Dominating Set**: instances `(G, k)` of `DominatingSet` whose induced finite
simple graph `G.induced` is connected and $3$-regular (`∀ v, G.induced.degree v = 3`). -/
def CubicDominatingSet : Set DominatingSetInstance :=
  {x | x.graph.induced.Connected ∧
    (∀ v : {w // w ∈ x.graph.vertices}, x.graph.induced.degree v = 3) ∧
    x ∈ DominatingSet}

/-- Membership characterization of `CubicDominatingSet`. -/
theorem mem_CubicDominatingSet_iff {x : DominatingSetInstance} :
    x ∈ CubicDominatingSet ↔
      x.graph.induced.Connected ∧
        (∀ v : {w // w ∈ x.graph.vertices}, x.graph.induced.degree v = 3) ∧
        x ∈ DominatingSet := Iff.rfl

/-! ### 1. Polynomial-Time Graph Helpers and `NP` Membership -/

/-- Executable degree of vertex `v` in `G.induced`. -/
@[expose]
def cubicGraphDegBool (G : Graph) (v : ℕ) : ℕ :=
  (G.distinctVertices.filter fun w ↦ G.adjBool v w).length

/-- `cubicGraphDegBool` equals `G.induced.degree` on declared vertices. -/
theorem cubicGraphDegBool_eq_degree (G : Graph) (v : {u // u ∈ G.vertices}) :
    cubicGraphDegBool G v.1 = G.induced.degree v := by
  classical
  rw [cubicGraphDegBool, ← _root_.SimpleGraph.card_neighborFinset_eq_degree,
    _root_.SimpleGraph.neighborFinset_eq_filter]
  rw [← List.toFinset_card_of_nodup (G.nodup_distinctVertices.filter _)]
  refine Finset.card_bij (fun w hw ↦ ⟨w, Graph.mem_distinctVertices.mp
      (List.mem_filter.mp (List.mem_toFinset.mp hw)).1⟩)
    (fun w hw ↦ ?_) (fun _ _ _ _ h ↦ congrArg Subtype.val h) (fun u hu ↦ ?_)
  · have hm := List.mem_filter.mp (List.mem_toFinset.mp hw)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Graph.adjBool_eq_true_iff G v.1 w).mp hm.2⟩
  · have hadj : G.toSimpleGraph.Adj v.1 u.1 := (Finset.mem_filter.mp hu).2
    exact ⟨u.1, List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨Graph.mem_distinctVertices.mpr u.2, (Graph.adjBool_eq_true_iff G v.1 u.1).mpr hadj⟩), rfl⟩

/-- `cubicGraphDegBool` is computable in polynomial time (into unary). -/
@[fun_prop]
theorem computableInPolyTime_cubicGraphDegBool :
    ComputableInPolyTime (fun p : Graph × ℕ ↦ cubicGraphDegBool p.1 p.2)
      (encPair encGraph encNat) encUnary :=
  (length_list encNat).comp (filterWithInput (by fun_prop) (by fun_prop))

private lemma length_encList_filter_le_cap {α : Type} (enc : α ↪ List Bool) (l : List α)
    (p : α → Bool) :
    (encList enc (l.filter p)).length ≤ (encList enc l).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter_cons]
    split_ifs <;> simp only [length_encList, List.map_cons, List.sum_cons] at ih ⊢ <;> omega

private def bfsStepCap (G : Graph) (vis : List ℕ) : List ℕ :=
  G.distinctVertices.filter fun u ↦
    vis.any (fun w ↦ decide (w = u)) || vis.any (fun w ↦ G.adjBool w u)

private def isConnBoolCap (G : Graph) : Bool :=
  match G.distinctVertices with
  | [] => false
  | v₀ :: _ =>
    let reached := (bfsStepCap G)^[G.distinctVertices.length] [v₀]
    G.distinctVertices.all fun u ↦ reached.any fun w ↦ decide (w = u)

private lemma isConnBoolCap_eq_true_iff (G : Graph) :
    isConnBoolCap G = true ↔ G.induced.Connected := by
  classical
  cases hdv : G.distinctVertices with
  | nil =>
    have hempty : G.vertices = [] := by
      by_contra hne
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil G.vertices hne
      have : v ∈ G.distinctVertices := Graph.mem_distinctVertices.mpr hv
      rw [hdv] at this; simp at this
    rw [isConnBoolCap, hdv]
    simp only [Bool.false_eq_true, false_iff]
    intro hconn; obtain ⟨⟨v, hv⟩⟩ := hconn.nonempty; simp [hempty] at hv
  | cons v₀ vs =>
    rw [isConnBoolCap, hdv]
    simp only [List.length_cons]
    have hv₀ : v₀ ∈ G.vertices := Graph.mem_distinctVertices.mp (by simp [hdv])
    have hiter : ∀ (t : ℕ) (u : {v // v ∈ G.vertices}),
        (∃ p : G.induced.Walk ⟨v₀, hv₀⟩ u, p.length ≤ t) ↔
          u.1 ∈ (bfsStepCap G)^[t] [v₀] := by
      intro t; induction t with
      | zero =>
        intro u
        simp only [Function.iterate_zero, id_eq, List.mem_singleton, Nat.le_zero]
        exact ⟨fun ⟨p, hp⟩ ↦
            (congrArg Subtype.val (_root_.SimpleGraph.Walk.eq_of_length_eq_zero hp)).symm,
          fun hu ↦ by
            have heq : (⟨v₀, hv₀⟩ : {v // v ∈ G.vertices}) = u := Subtype.ext hu.symm
            exact ⟨heq ▸ .nil, by subst heq; rfl⟩⟩
      | succ t ih =>
        intro u
        rw [Function.iterate_succ_apply']
        simp only [bfsStepCap, List.mem_filter, Graph.mem_distinctVertices, u.2, true_and,
          Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff]
        constructor
        · rintro ⟨p, hp⟩
          cases hrev : p.reverse with
          | nil => left; exact ⟨v₀, (ih ⟨v₀, hv₀⟩).mp ⟨.nil, Nat.zero_le t⟩, rfl⟩
          | @cons _ w' _ hadj' q' =>
            right
            have hlen_q : q'.reverse.length ≤ t := by
              have h2 : q'.length + 1 = p.reverse.length := by simp [hrev]
              rw [_root_.SimpleGraph.Walk.length_reverse] at h2 ⊢; omega
            exact ⟨w'.1, (ih w').mp ⟨q'.reverse, hlen_q⟩, hadj'.symm⟩
        · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, hadj⟩)
          · obtain ⟨p, hp⟩ := (ih u).mpr hw
            exact ⟨p, hp.trans (Nat.le_succ t)⟩
          · have hw_mem : w ∈ G.vertices := by
              cases t with
              | zero =>
                simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hw
                exact hw ▸ hv₀
              | succ t' =>
                rw [Function.iterate_succ_apply'] at hw
                exact Graph.mem_distinctVertices.mp (List.mem_filter.mp hw).1
            obtain ⟨p, hp⟩ := (ih ⟨w, hw_mem⟩).mpr hw
            refine ⟨p.append (.cons (show G.induced.Adj ⟨w, hw_mem⟩ u from hadj) .nil), ?_⟩
            rw [_root_.SimpleGraph.Walk.length_append, _root_.SimpleGraph.Walk.length_cons,
              _root_.SimpleGraph.Walk.length_nil]
            omega
    simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
    constructor
    · intro hall
      refine G.induced.connected_iff_exists_forall_reachable.mpr ⟨⟨v₀, hv₀⟩, fun u ↦ ?_⟩
      obtain ⟨w, hw, hwu⟩ := hall u.1 (hdv ▸ Graph.mem_distinctVertices.mpr u.2)
      subst hwu
      exact ((hiter (vs.length + 1) u).mpr hw).choose.reachable
    · intro hconn u hu
      have hu' : u ∈ G.vertices := Graph.mem_distinctVertices.mp (hdv ▸ hu)
      obtain ⟨p, hp⟩ := (hconn ⟨v₀, hv₀⟩ ⟨u, hu'⟩).exists_isPath
      have hlen : p.length ≤ vs.length + 1 := by
        have hlt := hp.length_lt
        rw [Graph.card_vertexSubtype, ← Graph.length_distinctVertices, hdv] at hlt
        simp only [List.length_cons] at hlt; omega
      exact ⟨u, (hiter (vs.length + 1) ⟨u, hu'⟩).mp ⟨p, hlen⟩, rfl⟩

private lemma computableInPolyTime_isConnBoolCap :
    ComputableInPolyTime isConnBoolCap encGraph encBool := by
  have hstep : ComputableInPolyTime (fun p : Graph × List ℕ ↦ bfsStepCap p.1 p.2)
      (encPair encGraph (encList encNat)) (encList encNat) :=
    filterWithInput (by fun_prop)
      (bool_or' (anyWithInput (by fun_prop) (by fun_prop))
        (anyWithInput (by fun_prop) (by fun_prop)))
  have hinit : ComputableInPolyTime (fun G : Graph ↦ [G.distinctVertices.getD 0 0])
      encGraph (encList encNat) :=
    ComputableInPolyTime.cons'
      (listGetDWithInput Graph.computableInPolyTime_distinctVertices
        (ComputableInPolyTime.const (encOut := encUnary) 0) 0)
      (ComputableInPolyTime.const ([] : List ℕ))
  have hcnt : ComputableInPolyTime (fun G : Graph ↦ G.distinctVertices.length)
      encGraph encUnary := (length_list encNat).comp Graph.computableInPolyTime_distinctVertices
  have hbound : PolyBounded (fun G : Graph ↦ (encGraph G).length)
      (fun G : Graph ↦ (encList encNat G.distinctVertices).length +
        (encList encNat [G.distinctVertices.getD 0 0]).length) :=
    (ComputableInPolyTime.unary_add.comp
      (((ComputableInPolyTime.encoding_length (encList encNat)).comp
          Graph.computableInPolyTime_distinctVertices).pair
        ((ComputableInPolyTime.encoding_length (encList encNat)).comp hinit))).polyBounded
  have hiter : ComputableInPolyTime
      (fun G : Graph ↦ (bfsStepCap G)^[G.distinctVertices.length] [G.distinctVertices.getD 0 0])
      encGraph (encList encNat) :=
    ComputableInPolyTime.iterateWith ComputableInPolyTime.id' hcnt hinit hstep hbound
      (fun G i _ ↦ by
        cases i with
        | zero => simp
        | succ j =>
          rw [Function.iterate_succ_apply']
          exact (length_encList_filter_le_cap encNat _ _).trans (Nat.le_add_right _ _))
  have hne : ComputableInPolyTime (fun G : Graph ↦ decide (0 < G.distinctVertices.length))
      encGraph encBool :=
    ComputableInPolyTime.unary_lt.comp
      ((ComputableInPolyTime.const (encOut := encUnary) 0).pair hcnt)
  have hall : ComputableInPolyTime
      (fun G : Graph ↦
        G.distinctVertices.all fun u ↦
          ((bfsStepCap G)^[G.distinctVertices.length] [G.distinctVertices.getD 0 0]).any
            fun w ↦ decide (w = u))
      encGraph encBool :=
    allWithInput (by fun_prop) (anyWithInput (hiter.comp (by fun_prop)) (by fun_prop))
  have heq : (fun G : Graph ↦ decide (0 < G.distinctVertices.length) &&
      G.distinctVertices.all fun u ↦
        ((bfsStepCap G)^[G.distinctVertices.length] [G.distinctVertices.getD 0 0]).any
          fun w ↦ decide (w = u)) = isConnBoolCap := by
    funext G; cases hdv : G.distinctVertices <;> simp [isConnBoolCap, hdv]
  exact heq ▸ bool_and' hne hall

/-- `CubicDominatingSet` belongs to `NP encDominatingSet`. -/
theorem CubicDominatingSet.mem_NP : CubicDominatingSet ∈ NP encDominatingSet := by
  rcases DominatingSet.mem_NP with ⟨p, V, hV, hVer⟩
  let c : DominatingSetInstance → Bool := fun x ↦
    isConnBoolCap x.graph &&
      x.graph.distinctVertices.all fun v ↦
        decide (cubicGraphDegBool x.graph v ≤ 3) && decide (3 ≤ cubicGraphDegBool x.graph v)
  have hc : ComputableInPolyTime c encDominatingSet encBool := by
    have h1 : ComputableInPolyTime (fun x : DominatingSetInstance ↦ isConnBoolCap x.graph)
        encDominatingSet encBool := computableInPolyTime_isConnBoolCap.comp (by fun_prop)
    have hp : ComputableInPolyTime (fun q : DominatingSetInstance × ℕ ↦ (q.1.graph, q.2))
        (encPair encDominatingSet encNat) (encPair encGraph encNat) := by fun_prop
    have hd := computableInPolyTime_cubicGraphDegBool.comp hp
    have h2 : ComputableInPolyTime
        (fun x : DominatingSetInstance ↦
          x.graph.distinctVertices.all fun v ↦
            decide (cubicGraphDegBool x.graph v ≤ 3) && decide (3 ≤ cubicGraphDegBool x.graph v))
        encDominatingSet encBool :=
      allWithInput (by fun_prop)
        (bool_and'
          (ComputableInPolyTime.unary_le.comp
            (hd.pair (ComputableInPolyTime.const (encOut := encUnary) 3)))
          (ComputableInPolyTime.unary_le.comp
            ((ComputableInPolyTime.const (encOut := encUnary) 3).pair hd)))
    exact bool_and' h1 h2
  refine ⟨p, fun y ↦ c y.1 && V y, bool_and' (hc.comp (by fun_prop)) hV, ?_⟩
  have hguard := hVer.guard (c := c)
  convert hguard using 1
  ext x
  simp only [Set.mem_ofPred_eq, mem_CubicDominatingSet_iff, c, Bool.and_eq_true,
    isConnBoolCap_eq_true_iff, List.all_eq_true, decide_eq_true_eq, and_assoc]
  refine and_congr_right fun _ ↦ and_congr_left fun _ ↦ ?_
  constructor
  · intro h v hv
    have hv' : v ∈ x.graph.vertices := Graph.mem_distinctVertices.mp hv
    rw [cubicGraphDegBool_eq_degree x.graph ⟨v, hv'⟩, h ⟨v, hv'⟩]
    exact ⟨le_rfl, le_rfl⟩
  · intro h v
    have := h v.1 (Graph.mem_distinctVertices.mpr v.2)
    rw [cubicGraphDegBool_eq_degree] at this; omega

/-! ### 2. Polynomial-Time `polyRange` and `dedupList` Helpers -/

/-- Executable `List.range n` built from `replicate` and `zipIdx` for polynomial-time proofs. -/
def polyRange (n : ℕ) : List ℕ :=
  ((List.replicate n false).zipIdx).map Prod.snd

theorem polyRange_eq_range (n : ℕ) : polyRange n = List.range n := by
  unfold polyRange
  refine List.ext_getElem (by simp) fun i hi _ ↦ ?_
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range]
  omega

theorem computableInPolyTime_polyRange :
    ComputableInPolyTime polyRange encUnary (encList encUnary) := by
  unfold polyRange
  have hrep : ComputableInPolyTime (fun n : ℕ ↦ List.replicate n false)
      encUnary (encList encBool) :=
    ComputableInPolyTime.replicate ComputableInPolyTime.id' (ComputableInPolyTime.const false)
  have hzip : ComputableInPolyTime (fun n : ℕ ↦ (List.replicate n false).zipIdx)
      encUnary (encList (encPair encBool encUnary)) :=
    (ComputableInPolyTime.zipIdx encBool).comp hrep
  have hsnd : ComputableInPolyTime (fun p : Bool × (Bool × ℕ) ↦ p.2.2)
      (encPair encBool (encPair encBool encUnary)) encUnary := by fun_prop
  exact mapWith hsnd (ComputableInPolyTime.const (encOut := encBool) false) hzip

/-- Polynomial-time deduplication keeping first occurrences. -/
def dedupList {α : Type} [DecidableEq α] (l : List α) : List α :=
  (l.zipIdx.filter fun p ↦ !(l.take p.2).any fun x ↦ decide (x = p.1)).map Prod.fst

theorem mem_dedupList {α : Type} [DecidableEq α] {l : List α} {a : α} :
    a ∈ dedupList l ↔ a ∈ l := by
  simp only [dedupList, List.mem_map, List.mem_filter, Bool.not_eq_true', List.any_eq_false,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x, i⟩, ⟨hmem, _⟩, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hkl : k < l.length := by simpa using hk
    have hx : x = l[k] := by
      have := congrArg Prod.fst hget
      simpa using this.symm
    exact hx ▸ List.getElem_mem hkl
  · intro ha
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp ha
    have hex : ∃ m, ∃ _ : m < l.length, l[m] = a := ⟨k, hk, hget⟩
    let m := Nat.find hex
    have hm_spec : ∃ hm : m < l.length, l[m] = a := Nat.find_spec hex
    obtain ⟨hm_lt, hm_eq⟩ := hm_spec
    have hm_min : ∀ (j : ℕ), j < m → ∀ (hj : j < l.length), l[j]'hj ≠ a := fun j hjm _ heq ↦
      Nat.find_min hex hjm ⟨by omega, heq⟩
    refine ⟨(a, m), ⟨?_, ?_⟩, rfl⟩
    · rw [List.mem_iff_getElem]
      refine ⟨m, by simpa using hm_lt, ?_⟩
      simp [hm_eq]
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
      have hjm : j < m := by
        rw [List.length_take] at hj; omega
      have hjl : j < l.length := by omega
      simpa [List.getElem_take] using hm_min j hjm hjl

theorem nodup_dedupList {α : Type} [DecidableEq α] (l : List α) : (dedupList l).Nodup := by
  rw [dedupList]
  have hnd_zip : l.zipIdx.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    have hi' : i < l.length := by simpa using hi
    have hj' : j < l.length := by simpa using hj
    have h2 := congrArg Prod.snd heq
    simp only [List.getElem_zipIdx, Nat.zero_add] at h2
    exact Fin.ext h2
  have hsub : ∀ {m : List (α × ℕ)},
      (∀ p ∈ m, ∀ q ∈ m, p.1 = q.1 → p.2 = q.2) → m.Nodup → (m.map Prod.fst).Nodup := by
    intro m hm hnd
    induction m with
    | nil => simp
    | cons p ps ih =>
      rw [List.map_cons, List.nodup_cons]
      rw [List.nodup_cons] at hnd
      refine ⟨?_, ih (fun a ha b hb ↦ hm a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)) hnd.2⟩
      intro hmem
      obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hmem
      exact hnd.1 (Prod.ext hqp (hm q (List.mem_cons_of_mem _ hq) p List.mem_cons_self hqp) ▸ hq)
  refine hsub ?_ (hnd_zip.filter _)
  intro p hp q hq hpq
  have hp' := List.mem_filter.mp hp
  have hq' := List.mem_filter.mp hq
  obtain ⟨ip, hip, hgp⟩ := List.mem_iff_getElem.mp hp'.1
  obtain ⟨iq, hiq, hgq⟩ := List.mem_iff_getElem.mp hq'.1
  have hip' : ip < l.length := by simpa using hip
  have hiq' : iq < l.length := by simpa using hiq
  have hp2 : p.2 = ip := by have := congrArg Prod.snd hgp; simpa using this.symm
  have hq2 : q.2 = iq := by have := congrArg Prod.snd hgq; simpa using this.symm
  have hp1 : p.1 = l[ip] := by have := congrArg Prod.fst hgp; simpa using this.symm
  have hq1 : q.1 = l[iq] := by have := congrArg Prod.fst hgq; simpa using this.symm
  have hp_not : ∀ x ∈ l.take p.2, x ≠ p.1 := by simpa using hp'.2
  have hq_not : ∀ x ∈ l.take q.2, x ≠ q.1 := by simpa using hq'.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : l[ip] ∈ l.take q.2 := by
      rw [List.mem_iff_getElem]
      exact ⟨ip, by rw [List.length_take]; omega, by simp⟩
    exact hq_not _ hmem (by rw [← hp1, hpq])
  · have hmem : l[iq] ∈ l.take p.2 := by
      rw [List.mem_iff_getElem]
      exact ⟨iq, by rw [List.length_take]; omega, by simp⟩
    exact hp_not _ hmem (by rw [← hq1, ← hpq])

theorem length_dedupList_le {α : Type} [DecidableEq α] (l : List α) :
    (dedupList l).length ≤ l.length := by
  unfold dedupList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- `dedupList` on `List ℕ` is computable in polynomial time. -/
theorem computableInPolyTime_dedupList_nat :
    ComputableInPolyTime (dedupList (α := ℕ)) (encList encNat) (encList encNat) := by
  unfold dedupList
  have hflt : ComputableInPolyTime
      (fun l : List ℕ ↦ l.zipIdx.filter fun p ↦ !(l.take p.2).any fun x ↦ decide (x = p.1))
      (encList encNat) (encList (encPair encNat encUnary)) :=
    filterWithInput ((ComputableInPolyTime.zipIdx encNat).comp ComputableInPolyTime.id')
      (ComputableInPolyTime.bool_not.comp
        (anyWithInput (listTakeWithInput (by fun_prop) (by fun_prop)) (by fun_prop)))
  have hfst : ComputableInPolyTime (fun p : Bool × (ℕ × ℕ) ↦ p.2.1)
      (encPair encBool (encPair encNat encUnary)) encNat := by fun_prop
  exact mapWith hfst (ComputableInPolyTime.const (encOut := encBool) false) hflt

/-- `dedupList` on `List (ℕ × Bool)` is computable in polynomial time. -/
theorem computableInPolyTime_dedupList_lit :
    ComputableInPolyTime (dedupList (α := ℕ × Bool))
      (encList (encPair encNat encBool)) (encList (encPair encNat encBool)) := by
  unfold dedupList
  have hflt : ComputableInPolyTime
      (fun l : List (ℕ × Bool) ↦
        l.zipIdx.filter fun p ↦ !(l.take p.2).any fun x ↦ decide (x = p.1))
      (encList (encPair encNat encBool))
      (encList (encPair (encPair encNat encBool) encUnary)) :=
    filterWithInput
      ((ComputableInPolyTime.zipIdx (encPair encNat encBool)).comp ComputableInPolyTime.id')
      (ComputableInPolyTime.bool_not.comp
        (anyWithInput (listTakeWithInput (by fun_prop) (by fun_prop)) (by fun_prop)))
  have hfst : ComputableInPolyTime (fun p : Bool × ((ℕ × Bool) × ℕ) ↦ p.2.1)
      (encPair encBool (encPair (encPair encNat encBool) encUnary)) (encPair encNat encBool) := by
    fun_prop
  exact mapWith hfst (ComputableInPolyTime.const (encOut := encBool) false) hflt

/-! ### 3. The $7$-Vertex $1$-Port Cubic Degree-Cap Gadget $W_7$ -/

/-- Internal undirected edge list of the $7$-vertex $1$-port cubic degree-cap gadget $W_7$
($K_{3,3}$ with one edge subdivided by port `0`). -/
@[expose]
def w7Edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 5), (4, 6)]

/-- Executable adjacency on `Fin 7` for `w7Edges`. -/
@[expose]
def w7Adj (a b : Fin 7) : Bool :=
  w7Edges.any fun e ↦ decide (e = (a.1, b.1)) || decide (e = (b.1, a.1))

private lemma w7Edges_lt {e : ℕ × ℕ} (he : e ∈ w7Edges) : e.1 < 7 ∧ e.2 < 7 := by
  have hall : w7Edges.all (fun p ↦ decide (p.1 < 7) && decide (p.2 < 7)) = true := by decide
  simpa using List.all_eq_true.mp hall e he

private lemma w7Adj_symm (a b : Fin 7) : w7Adj a b = w7Adj b a := by
  revert a b; decide

private lemma w7_dom_pair (x : Fin 7) :
    x = 1 ∨ x = 2 ∨ w7Adj 1 x = true ∨ w7Adj 2 x = true := by
  fin_cases x <;> decide

private lemma w7_no_single_dom_inner (u : Fin 7) :
    ∃ x : Fin 7, x ≠ 0 ∧ x ≠ u ∧ w7Adj u x = false := by
  fin_cases u <;> decide

private lemma w7_no_single_dom_c4 (u : Fin 7) :
    ∃ x : Fin 7, (x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6) ∧ x ≠ u ∧ w7Adj u x = false := by
  fin_cases u <;> decide

private lemma w7_deg_val (x : Fin 7) :
    ((List.finRange 7).filter fun y ↦ w7Adj x y).length = if x = 0 then 2 else 3 := by
  fin_cases x <;> decide

/-- Vertex identifier for vertex `q < 7` of the `s`-th $W_7$ cap (`s < 3`) attached to base vertex
`u`. -/
@[expose]
def cubicCapV (u s q : ℕ) : ℕ := 4 * (7 * (3 * u + s) + q) + 3

theorem cubicCapV_injective {u₁ s₁ q₁ u₂ s₂ q₂ : ℕ}
    (hs₁ : s₁ < 3) (hs₂ : s₂ < 3) (hq₁ : q₁ < 7) (hq₂ : q₂ < 7)
    (h : cubicCapV u₁ s₁ q₁ = cubicCapV u₂ s₂ q₂) :
    u₁ = u₂ ∧ s₁ = s₂ ∧ q₁ = q₂ := by
  unfold cubicCapV at h
  omega

/-- Capped cubic graph obtained by attaching `3 - deg_B(u)` copies of $W_7$ to every base vertex
`u ∈ B.vertices`. -/
def cappedGraphOf (B : Graph) : Graph :=
  let capVerts := B.vertices.flatMap fun u ↦
    (polyRange (3 - cubicGraphDegBool B u)).flatMap fun s ↦
      [0, 1, 2, 3, 4, 5, 6].map fun q ↦ cubicCapV u s q
  let capEdges := B.vertices.flatMap fun u ↦
    (polyRange (3 - cubicGraphDegBool B u)).flatMap fun s ↦
      (u, cubicCapV u s 0) :: w7Edges.map fun e ↦ (cubicCapV u s e.1, cubicCapV u s e.2)
  ⟨B.vertices ++ capVerts, B.edges ++ capEdges⟩

theorem cappedGraphOf_vertices_nodup {B : Graph} (hnd : B.vertices.Nodup)
    (hmod : ∀ u ∈ B.vertices, u % 4 ≠ 3) :
    (cappedGraphOf B).vertices.Nodup := by
  unfold cappedGraphOf
  simp only [polyRange_eq_range]
  refine List.nodup_append.mpr ⟨hnd, ?_, ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun u _ ↦ ?_, ?_⟩
    · refine List.nodup_flatMap.mpr ⟨fun s hs ↦ ?_, ?_⟩
      · have hs3 : s < 3 := by have := List.mem_range.mp hs; omega
        have hnd7 : ([0, 1, 2, 3, 4, 5, 6] : List ℕ).Nodup := by decide
        refine hnd7.map_on fun q₁ hq₁ q₂ hq₂ h ↦ ?_
        exact (cubicCapV_injective hs3 hs3 (by simp at hq₁; omega) (by simp at hq₂; omega) h).2.2
      · refine List.pairwise_iff_getElem.mpr fun i j hi hj hij x hx₁ hx₂ ↦ ?_
        simp only [List.getElem_range, List.mem_map] at hx₁ hx₂
        obtain ⟨q₁, hq₁, rfl⟩ := hx₁; obtain ⟨q₂, hq₂, h⟩ := hx₂
        have h1 : i < 3 := by rw [List.length_range] at hi; omega
        have h2 : j < 3 := by rw [List.length_range] at hj; omega
        have heq := (cubicCapV_injective h1 h2 (by simp at hq₁; omega) (by simp at hq₂; omega)
          h.symm).2.1
        omega
    · refine List.pairwise_iff_getElem.mpr fun i j hi hj hij x hx₁ hx₂ ↦ ?_
      simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hx₁ hx₂
      obtain ⟨s₁, hs₁, q₁, hq₁, rfl⟩ := hx₁; obtain ⟨s₂, hs₂, q₂, hq₂, h⟩ := hx₂
      have hu := (cubicCapV_injective (by omega) (by omega)
        (by simp at hq₁; omega) (by simp at hq₂; omega) h.symm).1
      have hne : B.vertices[i] ≠ B.vertices[j] :=
        (List.nodup_iff_injective_getElem.mp hnd).ne
          (show (⟨i, hi⟩ : Fin B.vertices.length) ≠ ⟨j, hj⟩ from Fin.ne_of_lt hij)
      exact hne hu
  · intro x hx₁ y hy₂ heq
    subst heq
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hy₂
    obtain ⟨u, _, s, _, q, _, rfl⟩ := hy₂
    exact hmod _ hx₁ (by unfold cubicCapV; omega)

private lemma mem_cappedGraphOf_cap {B : Graph} {b s q : ℕ}
    (hb : b ∈ B.vertices) (hs : s < 3 - cubicGraphDegBool B b) (hq : q < 7) :
    cubicCapV b s q ∈ (cappedGraphOf B).vertices := by
  unfold cappedGraphOf
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb,
    List.mem_flatMap.mpr ⟨s, by rw [polyRange_eq_range]; exact List.mem_range.mpr hs,
      List.mem_map.mpr ⟨q, by interval_cases q <;> simp, rfl⟩⟩⟩)

theorem cappedGraphOf_adj_iff {B : Graph}
    (hmod : ∀ u ∈ B.vertices, u % 4 ≠ 3)
    (u v : ℕ) :
    (cappedGraphOf B).toSimpleGraph.Adj u v ↔
      B.toSimpleGraph.Adj u v ∨
      (∃ b ∈ B.vertices, ∃ s < 3 - cubicGraphDegBool B b,
        (u = b ∧ v = cubicCapV b s 0) ∨ (u = cubicCapV b s 0 ∧ v = b) ∨
        ∃ q₁ : Fin 7, ∃ q₂ : Fin 7, w7Adj q₁ q₂ = true ∧
          u = cubicCapV b s q₁.1 ∧ v = cubicCapV b s q₂.1) := by
  have hmem_e : ∀ a c : ℕ, (a, c) ∈ (cappedGraphOf B).edges ↔
      (a, c) ∈ B.edges ∨
      ∃ x ∈ B.vertices, ∃ s < 3 - cubicGraphDegBool B x,
        (a = x ∧ c = cubicCapV x s 0) ∨
        ∃ e ∈ w7Edges, a = cubicCapV x s e.1 ∧ c = cubicCapV x s e.2 := by
    intro a c; unfold cappedGraphOf
    simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
      List.mem_cons, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨x, hx, s, hs, h | ⟨e, he, ha, hc⟩⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, s, hs, Or.inl h⟩
      · exact Or.inr ⟨x, hx, s, hs, Or.inr ⟨e, he, ha.symm, hc.symm⟩⟩
    · rintro (h | ⟨x, hx, s, hs, h | ⟨e, he, ha, hc⟩⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, s, hs, Or.inl h⟩
      · exact Or.inr ⟨x, hx, s, hs, Or.inr ⟨e, he, ha.symm, hc.symm⟩⟩
  rw [Graph.toSimpleGraph_adj, hmem_e u v, hmem_e v u]
  constructor
  · rintro ⟨hne, (h | ⟨x, hx, s, hs, ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩⟩) |
        (h | ⟨x, hx, s, hs, ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩⟩)⟩
    · exact Or.inl ((Graph.toSimpleGraph_adj).mpr ⟨hne, Or.inl h⟩)
    · exact Or.inr ⟨u, hx, s, hs, Or.inl ⟨rfl, rfl⟩⟩
    · have ⟨h1, h2⟩ := w7Edges_lt he
      exact Or.inr ⟨x, hx, s, hs, Or.inr (Or.inr ⟨⟨e.1, h1⟩, ⟨e.2, h2⟩,
        List.any_eq_true.mpr ⟨e, he, by simp⟩, rfl, rfl⟩)⟩
    · exact Or.inl ((Graph.toSimpleGraph_adj).mpr ⟨hne, Or.inr h⟩)
    · exact Or.inr ⟨v, hx, s, hs, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · have ⟨h1, h2⟩ := w7Edges_lt he
      exact Or.inr ⟨x, hx, s, hs, Or.inr (Or.inr ⟨⟨e.2, h2⟩, ⟨e.1, h1⟩,
        List.any_eq_true.mpr ⟨e, he, by simp⟩, rfl, rfl⟩)⟩
  · rintro (hadj | ⟨x, hx, s, hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨q₁, q₂, hq, rfl, rfl⟩⟩)
    · rcases (Graph.toSimpleGraph_adj).mp hadj with ⟨hne, h | h⟩
      · exact ⟨hne, Or.inl (Or.inl h)⟩
      · exact ⟨hne, Or.inr (Or.inl h)⟩
    · exact ⟨fun h ↦ hmod _ hx (by unfold cubicCapV at h; omega),
        Or.inl (Or.inr ⟨u, hx, s, hs, Or.inl ⟨rfl, rfl⟩⟩)⟩
    · exact ⟨fun h ↦ hmod _ hx (by unfold cubicCapV at h; omega),
        Or.inr (Or.inr ⟨v, hx, s, hs, Or.inl ⟨rfl, rfl⟩⟩)⟩
    · have hqne : q₁ ≠ q₂ := by
        intro heq; subst heq; exact absurd hq (by revert q₁; decide)
      have hne : cubicCapV x s q₁.1 ≠ cubicCapV x s q₂.1 := fun h ↦
        hqne (Fin.ext (cubicCapV_injective (by omega) (by omega) q₁.2 q₂.2 h).2.2)
      simp only [w7Adj, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hq
      obtain ⟨e, he, h1 | h2⟩ := hq
      · exact ⟨hne, Or.inl (Or.inr ⟨x, hx, s, hs, Or.inr ⟨e, he, by simp [h1], by simp [h1]⟩⟩)⟩
      · exact ⟨hne, Or.inr (Or.inr ⟨x, hx, s, hs, Or.inr ⟨e, he, by simp [h2], by simp [h2]⟩⟩)⟩

/-- Exact vertex count of `cappedGraphOf B`. -/
theorem cappedGraphOf_vertices_length (B : Graph) :
    (cappedGraphOf B).vertices.length =
      B.vertices.length + 7 * (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum := by
  unfold cappedGraphOf
  rw [List.length_append]
  congr 1
  simp only [List.length_flatMap, polyRange_eq_range]
  have hinner : ∀ n : ℕ, ((List.range n).map fun _ ↦
      ([0, 1, 2, 3, 4, 5, 6].map fun q ↦ q).length).sum = 7 * n := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; ring
  have hstep : ∀ l : List ℕ, (l.map fun u ↦
      ((List.range (3 - cubicGraphDegBool B u)).map fun s ↦
        ([0, 1, 2, 3, 4, 5, 6].map fun q ↦ cubicCapV u s q).length).sum).sum =
      7 * (l.map fun u ↦ 3 - cubicGraphDegBool B u).sum := by
    intro l; induction l with
    | nil => simp
    | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
      have h7 : ((List.range (3 - cubicGraphDegBool B a)).map fun s ↦
          ([0, 1, 2, 3, 4, 5, 6].map fun q ↦ cubicCapV a s q).length).sum =
          7 * (3 - cubicGraphDegBool B a) := by
        simpa [List.length_map] using hinner (3 - cubicGraphDegBool B a)
      rw [h7]; ring
  exact hstep B.vertices

/-- Every vertex of `cappedGraphOf B` has exact degree `3`. -/
theorem cappedGraphOf_cubic {B : Graph}
    (hnd : B.vertices.Nodup)
    (hmod : ∀ u ∈ B.vertices, u % 4 ≠ 3)
    (hE : ∀ e ∈ B.edges, e.1 ∈ B.vertices ∧ e.2 ∈ B.vertices)
    (hdeg : ∀ u ∈ B.vertices, 1 ≤ cubicGraphDegBool B u ∧ cubicGraphDegBool B u ≤ 3)
    (v : {w // w ∈ (cappedGraphOf B).vertices}) :
    (cappedGraphOf B).induced.degree v = 3 := by
  classical
  let G := cappedGraphOf B
  have hndG := cappedGraphOf_vertices_nodup hnd hmod
  rw [← cubicGraphDegBool_eq_degree G v]
  have hdeg_card : cubicGraphDegBool G v.1 =
      (G.vertices.toFinset.filter fun w ↦ G.toSimpleGraph.Adj v.1 w).card := by
    rw [cubicGraphDegBool, ← List.toFinset_card_of_nodup (G.nodup_distinctVertices.filter _)]
    congr 1; ext w
    simp [Graph.mem_distinctVertices, Graph.adjBool_eq_true_iff]
  rw [hdeg_card]
  have hv_mem : v.1 ∈ G.vertices := v.2
  dsimp only [G, cappedGraphOf] at hv_mem
  simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_map] at hv_mem
  rcases hv_mem with hvB | ⟨b, hb, s, hs, q, hq, hv_eq⟩
  · let N_B := B.vertices.toFinset.filter fun w ↦ B.toSimpleGraph.Adj v.1 w
    let N_cap := ((List.range (3 - cubicGraphDegBool B v.1)).map fun s ↦ cubicCapV v.1 s 0).toFinset
    have hdisj : Disjoint N_B N_cap := Finset.disjoint_left.mpr fun w hwB hwC ↦ by
      have hwV := List.mem_toFinset.mp (Finset.mem_filter.mp hwB).1
      simp only [N_cap, List.mem_toFinset, List.mem_map, List.mem_range] at hwC
      obtain ⟨s, _, rfl⟩ := hwC; exact hmod _ hwV (by unfold cubicCapV; omega)
    have heq_set : (G.vertices.toFinset.filter fun w ↦ G.toSimpleGraph.Adj v.1 w) =
      N_B ∪ N_cap := by
      ext w; simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_union, N_B, N_cap,
        List.mem_map, List.mem_range]
      constructor
      · rintro ⟨_, hadj⟩
        rw [cappedGraphOf_adj_iff hmod v.1 w] at hadj
        rcases hadj with hB | ⟨b, hb, s, hs, ⟨hv_eq_b, rfl⟩ | ⟨h0, _⟩ | ⟨_, _, _, h0, _⟩⟩
        · left
          rcases (Graph.toSimpleGraph_adj).mp hB with ⟨_, h | h⟩
          · exact ⟨(hE _ h).2, hB⟩
          · exact ⟨(hE _ h).1, hB⟩
        · right; exact ⟨s, hv_eq_b ▸ hs, hv_eq_b ▸ rfl⟩
        · exact (hmod _ hvB (by rw [h0]; unfold cubicCapV; omega)).elim
        · exact (hmod _ hvB (by rw [h0]; unfold cubicCapV; omega)).elim
      · rintro (⟨hwB, hadj⟩ | ⟨s, hs, rfl⟩)
        · exact ⟨List.mem_append_left _ hwB, (cappedGraphOf_adj_iff hmod v.1 w).mpr (Or.inl hadj)⟩
        · exact ⟨mem_cappedGraphOf_cap hvB hs (by omega),
            (cappedGraphOf_adj_iff hmod _ _).mpr (Or.inr ⟨v.1, hvB, s, hs, Or.inl ⟨rfl, rfl⟩⟩)⟩
    rw [heq_set, Finset.card_union_of_disjoint hdisj]
    have hNB_card : N_B.card = cubicGraphDegBool B v.1 := by
      rw [cubicGraphDegBool, ← List.toFinset_card_of_nodup (B.nodup_distinctVertices.filter _)]
      congr 1; ext w; simp [N_B, Graph.mem_distinctVertices, Graph.adjBool_eq_true_iff]
    have hNcap_card : N_cap.card = 3 - cubicGraphDegBool B v.1 := by
      have hnd_cap : ((List.range (3 - cubicGraphDegBool B v.1)).map
          fun s ↦ cubicCapV v.1 s 0).Nodup :=
        (List.nodup_range).map fun s₁ s₂ h ↦ by unfold cubicCapV at h; omega
      rw [List.toFinset_card_of_nodup hnd_cap, List.length_map, List.length_range]
    rw [hNB_card, hNcap_card]; have := hdeg v.1 hvB; omega
  · have hq7 : q < 7 := by simp at hq; omega
    let qF : Fin 7 := ⟨q, hq7⟩
    let N_in := ((List.finRange 7).filter fun y ↦ w7Adj qF y).map (fun y ↦ cubicCapV b s y.1)
    let N_all := if q = 0 then b :: N_in else N_in
    have hnd_in : N_in.Nodup :=
      ((List.nodup_finRange 7).filter _).map fun y₁ y₂ h ↦
        Fin.ext (cubicCapV_injective (by omega) (by omega) y₁.2 y₂.2 h).2.2
    have hnd_all : N_all.Nodup := by
      dsimp only [N_all]; split_ifs
      · refine List.nodup_cons.mpr ⟨?_, hnd_in⟩
        intro hmem; simp only [N_in, List.mem_map] at hmem
        obtain ⟨y, _, hy⟩ := hmem
        exact hmod _ hb (by rw [← hy]; unfold cubicCapV; omega)
      · exact hnd_in
    have heq_set : (G.vertices.toFinset.filter fun w ↦ G.toSimpleGraph.Adj v.1 w) =
      N_all.toFinset := by
      ext w; simp only [Finset.mem_filter, List.mem_toFinset]
      constructor
      · rintro ⟨_, hadj⟩
        rw [cappedGraphOf_adj_iff hmod v.1 w] at hadj
        rcases hadj with hB | ⟨b', hb', s', hs', ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨q₁, q₂, hqa, h1, h2⟩⟩
        · rcases (Graph.toSimpleGraph_adj).mp hB with ⟨_, h | h⟩
          · exact (hmod _ (hE _ h).1 (by rw [← hv_eq]; unfold cubicCapV; omega)).elim
          · exact (hmod _ (hE _ h).2 (by rw [← hv_eq]; unfold cubicCapV; omega)).elim
        · exact (hmod _ hb' (by rw [← h1, ← hv_eq]; unfold cubicCapV; omega)).elim
        · rcases cubicCapV_injective (by omega) (by omega) hq7 (by omega) (hv_eq.trans h1) with
            ⟨rfl, rfl, hq0⟩
          simp [N_all, hq0, h2]
        · rcases cubicCapV_injective (by omega) (by omega) hq7 q₁.2 (hv_eq.trans h1) with
            ⟨rfl, rfl, hq1⟩
          have hqF : q₁ = qF := Fin.ext hq1.symm; subst hqF
          have hw_in : w ∈ N_in := List.mem_map.mpr
            ⟨q₂, List.mem_filter.mpr ⟨List.mem_finRange q₂, hqa⟩, h2.symm⟩
          dsimp only [N_all]; split_ifs <;> simp [hw_in]
      · intro hw
        have hw_cases : (q = 0 ∧ w = b) ∨ ∃ y : Fin 7, w7Adj qF y = true ∧
          w = cubicCapV b s y.1 := by
          dsimp only [N_all] at hw; split_ifs at hw with hq0
          · rcases List.mem_cons.mp hw with rfl | hmem
            · exact Or.inl ⟨hq0, rfl⟩
            · simp only [N_in, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hmem
              obtain ⟨y, hy, rfl⟩ := hmem; exact Or.inr ⟨y, hy, rfl⟩
          · simp only [N_in, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
            obtain ⟨y, hy, rfl⟩ := hw; exact Or.inr ⟨y, hy, rfl⟩
        rcases hw_cases with ⟨hq0, hwb⟩ | ⟨y, hy, rfl⟩
        · subst hwb
          exact ⟨List.mem_append_left _ hb, (cappedGraphOf_adj_iff hmod _ _).mpr
            (Or.inr ⟨w, hb, s, hs, Or.inr (Or.inl ⟨hv_eq.symm.trans (by rw [hq0]), rfl⟩)⟩)⟩
        · exact ⟨mem_cappedGraphOf_cap hb hs y.2, (cappedGraphOf_adj_iff hmod _ _).mpr
            (Or.inr ⟨b, hb, s, hs, Or.inr (Or.inr ⟨qF, y, hy, hv_eq.symm, rfl⟩)⟩)⟩
    rw [heq_set, List.toFinset_card_of_nodup hnd_all]
    have hlen_in : N_in.length = if qF = 0 then 2 else 3 := by rw [List.length_map, w7_deg_val]
    dsimp only [N_all]; split_ifs with hq0
    · have hqF0 : qF = 0 := Fin.ext hq0; simp [hlen_in, hqF0]
    · have hqF0 : qF ≠ 0 := fun h ↦ hq0 (congrArg Fin.val h); simp [hlen_in, hqF0]

/-- `cappedGraphOf B` is connected whenever `B` is connected. -/
theorem cappedGraphOf_connected {B : Graph}
    (hmod : ∀ u ∈ B.vertices, u % 4 ≠ 3)
    (hB : B.induced.Connected) :
    (cappedGraphOf B).induced.Connected := by
  let G := cappedGraphOf B
  obtain ⟨⟨v₀, hv₀⟩⟩ := hB.nonempty
  have hv₀G : v₀ ∈ G.vertices := List.mem_append_left _ hv₀
  refine G.induced.connected_iff_exists_forall_reachable.mpr ⟨⟨v₀, hv₀G⟩, fun u ↦ ?_⟩
  have hreach_base : ∀ w (hw : w ∈ B.vertices),
      G.induced.Reachable ⟨v₀, hv₀G⟩ ⟨w, List.mem_append_left _ hw⟩ := by
    intro w hw
    obtain ⟨p⟩ := hB ⟨v₀, hv₀⟩ ⟨w, hw⟩
    let hom : B.induced →g G.induced :=
      ⟨fun x ↦ ⟨x.1, List.mem_append_left _ x.2⟩,
       fun hadj ↦ (cappedGraphOf_adj_iff hmod _ _).mpr (Or.inl hadj)⟩
    exact (p.map hom).reachable
  have hu_mem := u.2
  dsimp only [G, cappedGraphOf] at hu_mem
  simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_map] at hu_mem
  rcases hu_mem with huB | ⟨b, hb, s, hs, q, hq, hu_eq⟩
  · exact hreach_base u.1 huB
  · have hq7 : q < 7 := by simp at hq; omega
    have h0G : cubicCapV b s 0 ∈ G.vertices := mem_cappedGraphOf_cap hb hs (by omega)
    have h0_reach : G.induced.Reachable ⟨b, List.mem_append_left _ hb⟩ ⟨cubicCapV b s 0, h0G⟩ :=
      _root_.SimpleGraph.Adj.reachable
        ((cappedGraphOf_adj_iff hmod _ _).mpr (Or.inr ⟨b, hb, s, hs, Or.inl ⟨rfl, rfl⟩⟩))
    have hadj_w7 : ∀ a c : Fin 7, w7Adj a c = true →
        G.induced.Reachable ⟨cubicCapV b s a.1, mem_cappedGraphOf_cap hb hs a.2⟩
          ⟨cubicCapV b s c.1, mem_cappedGraphOf_cap hb hs c.2⟩ := fun a c h ↦
      _root_.SimpleGraph.Adj.reachable ((cappedGraphOf_adj_iff hmod _ _).mpr
        (Or.inr ⟨b, hb, s, hs, Or.inr (Or.inr ⟨a, c, h, rfl, rfl⟩)⟩))
    have htarget : u = ⟨cubicCapV b s q, mem_cappedGraphOf_cap hb hs hq7⟩ :=
      Subtype.ext hu_eq.symm
    have hq_reach : G.induced.Reachable ⟨cubicCapV b s 0, h0G⟩ u := by
      rw [htarget]
      interval_cases q
      · exact .refl _
      · exact hadj_w7 0 1 (by decide)
      · exact hadj_w7 0 2 (by decide)
      · exact (hadj_w7 0 1 (by decide)).trans (hadj_w7 1 3 (by decide))
      · exact (hadj_w7 0 1 (by decide)).trans (hadj_w7 1 4 (by decide))
      · exact (hadj_w7 0 2 (by decide)).trans (hadj_w7 2 5 (by decide))
      · exact (hadj_w7 0 2 (by decide)).trans (hadj_w7 2 6 (by decide))
    exact ((hreach_base b hb).trans h0_reach).trans hq_reach

/-- **Cap-stripping theorem**: `cappedGraphOf B` has a dominating set of size `≤ k + 2 * T` if and
only if `B` has a dominating set of size `≤ k`, where `T = ∑ u ∈ B, (3 - deg_B(u))`. -/
theorem cappedGraphOf_dom_iff {B : Graph}
    (hnd : B.vertices.Nodup)
    (hmod : ∀ u ∈ B.vertices, u % 4 ≠ 3)
    (hE : ∀ e ∈ B.edges, e.1 ∈ B.vertices ∧ e.2 ∈ B.vertices)
    (k : ℕ) :
    (∃ S : Finset ℕ, (∀ v ∈ S, v ∈ (cappedGraphOf B).vertices) ∧
      (∀ v ∈ (cappedGraphOf B).vertices, v ∈ S ∨ ∃ w ∈ S, (cappedGraphOf B).toSimpleGraph.Adj v w) ∧
      S.card ≤ k + 2 * (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum) ↔
    (∃ D : Finset ℕ, (∀ v ∈ D, v ∈ B.vertices) ∧
      (∀ v ∈ B.vertices, v ∈ D ∨ ∃ w ∈ D, B.toSimpleGraph.Adj v w) ∧
      D.card ≤ k) := by
  classical
  let G := cappedGraphOf B
  let T := (B.vertices.map fun u ↦ 3 - cubicGraphDegBool B u).sum
  let slots : Finset (ℕ × ℕ) :=
    B.vertices.toFinset.biUnion fun b ↦
      (List.range (3 - cubicGraphDegBool B b)).toFinset.image fun s ↦ (b, s)
  have hslots_card : slots.card = T := by
    have hdisj : (B.vertices.toFinset : Set ℕ).PairwiseDisjoint
        (fun b ↦ (List.range (3 - cubicGraphDegBool B b)).toFinset.image fun s ↦ (b, s)) := by
      intro b₁ _ b₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ ↦ ?_
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp₁
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp hp₂
      exact hne (congrArg Prod.fst h.symm)
    rw [Finset.card_biUnion hdisj]
    have hsum_eq : ∑ b ∈ B.vertices.toFinset,
        ((List.range (3 - cubicGraphDegBool B b)).toFinset.image fun s ↦ (b, s)).card =
        ∑ b ∈ B.vertices.toFinset, (3 - cubicGraphDegBool B b) := by
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Finset.card_image_of_injective _ fun s₁ s₂ h ↦ congrArg Prod.snd h,
        List.toFinset_card_of_nodup List.nodup_range, List.length_range]
    rw [hsum_eq]; dsimp only [T]
    rw [← List.sum_toFinset _ hnd]
  constructor
  · rintro ⟨S, hSG, hSdom, hScard⟩
    let capSet (b s : ℕ) : Finset ℕ := (List.finRange 7).toFinset.image fun q ↦ cubicCapV b s q.1
    let forced : Finset ℕ := B.vertices.toFinset.filter fun b ↦
      ∃ s < 3 - cubicGraphDegBool B b, cubicCapV b s 0 ∈ S
    let D : Finset ℕ := (S ∩ B.vertices.toFinset) ∪ forced
    have hD_sub : ∀ v ∈ D, v ∈ B.vertices := fun v hv ↦ by
      rcases Finset.mem_union.mp hv with h1 | h2
      · exact List.mem_toFinset.mp (Finset.mem_inter.mp h1).2
      · exact List.mem_toFinset.mp (Finset.mem_filter.mp h2).1
    have hD_dom : ∀ v ∈ B.vertices, v ∈ D ∨ ∃ w ∈ D, B.toSimpleGraph.Adj v w := by
      intro v hv
      rcases hSdom v (List.mem_append_left _ hv) with hvS | ⟨w, hwS, hadj⟩
      · exact Or.inl (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvS, List.mem_toFinset.mpr hv⟩))
      · rw [cappedGraphOf_adj_iff hmod v w] at hadj
        rcases hadj with hB | ⟨b, _, s, hs, ⟨rfl, rfl⟩ | ⟨h0, _⟩ | ⟨_, _, _, h0, _⟩⟩
        · have hwB : w ∈ B.vertices := by
            rcases (Graph.toSimpleGraph_adj).mp hB with ⟨_, h | h⟩
            · exact (hE _ h).2
            · exact (hE _ h).1
          exact Or.inr ⟨w, Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hwS, List.mem_toFinset.mpr hwB⟩), hB⟩
        · exact Or.inl (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, s, hs, hwS⟩))
        · exact (hmod _ hv (by rw [h0]; unfold cubicCapV; omega)).elim
        · exact (hmod _ hv (by rw [h0]; unfold cubicCapV; omega)).elim
    have hdom_cap : ∀ b ∈ B.vertices, ∀ s < 3 - cubicGraphDegBool B b, ∀ q : Fin 7, q ≠ 0 →
        cubicCapV b s q.1 ∈ S ∨ ∃ y : Fin 7, cubicCapV b s y.1 ∈ S ∧ w7Adj q y = true := by
      intro b hb s hs q hq0
      rcases hSdom _ (mem_cappedGraphOf_cap hb hs q.2) with hmem | ⟨w, hwS, hadj⟩
      · exact Or.inl hmem
      · rw [cappedGraphOf_adj_iff hmod _ _] at hadj
        rcases hadj with hB | ⟨b', hb', s', hs', ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨q₁, q₂, hqa, h1, h2⟩⟩
        · rcases (Graph.toSimpleGraph_adj).mp hB with ⟨_, h | h⟩
          · exact (hmod _ (hE _ h).1 (by unfold cubicCapV; omega)).elim
          · exact (hmod _ (hE _ h).2 (by unfold cubicCapV; omega)).elim
        · exact (hmod _ hb' (by rw [← h1]; unfold cubicCapV; omega)).elim
        · exfalso
          exact hq0 (Fin.ext (cubicCapV_injective (by omega) (by omega) q.2 (by omega) h1).2.2)
        · rcases cubicCapV_injective (by omega) (by omega) q.2 q₁.2 h1 with ⟨rfl, rfl, hq1⟩
          have : q₁ = q := Fin.ext hq1.symm; subst this
          exact Or.inr ⟨q₂, h2 ▸ hwS, hqa⟩
    have hcap_ge2 : ∀ b ∈ B.vertices, ∀ s < 3 - cubicGraphDegBool B b,
        2 ≤ (S ∩ capSet b s).card := by
      intro b hb s hs
      have hcard_lt : ¬ (S ∩ capSet b s).card ≤ 1 := by
        intro hle1
        rcases Finset.card_le_one_iff_subset_singleton.mp hle1 with ⟨u₀, hu₀⟩
        by_cases hu_cap : ∃ q₀ : Fin 7, u₀ = cubicCapV b s q₀.1
        · obtain ⟨q₀, rfl⟩ := hu_cap
          obtain ⟨x, hx0, hxq, hno⟩ := w7_no_single_dom_inner q₀
          rcases hdom_cap b hb s hs x hx0 with hmem | ⟨y, hyS, hya⟩
          · have heq := Finset.mem_singleton.mp (hu₀ (Finset.mem_inter.mpr
              ⟨hmem, Finset.mem_image.mpr ⟨x, by simp, rfl⟩⟩))
            exact hxq (Fin.ext (cubicCapV_injective (by omega) (by omega) x.2 q₀.2 heq).2.2)
          · have heq := Finset.mem_singleton.mp (hu₀ (Finset.mem_inter.mpr
              ⟨hyS, Finset.mem_image.mpr ⟨y, by simp, rfl⟩⟩))
            have hyq : y = q₀ :=
              Fin.ext (cubicCapV_injective (by omega) (by omega) y.2 q₀.2 heq).2.2
            subst hyq
            rw [w7Adj_symm y x] at hno
            simp [hno] at hya
        · obtain ⟨x, hx0, _, _⟩ := w7_no_single_dom_inner 0
          rcases hdom_cap b hb s hs x hx0 with hmem | ⟨y, hyS, _⟩
          · exact hu_cap ⟨x, (Finset.mem_singleton.mp (hu₀ (Finset.mem_inter.mpr
              ⟨hmem, Finset.mem_image.mpr ⟨x, by simp, rfl⟩⟩))).symm⟩
          · exact hu_cap ⟨y, (Finset.mem_singleton.mp (hu₀ (Finset.mem_inter.mpr
              ⟨hyS, Finset.mem_image.mpr ⟨y, by simp, rfl⟩⟩))).symm⟩
      omega
    have hcap_ge3 : ∀ b ∈ B.vertices, ∀ s < 3 - cubicGraphDegBool B b,
        cubicCapV b s 0 ∈ S → 3 ≤ (S ∩ capSet b s).card := by
      intro b hb s hs h0S
      have h0mem : cubicCapV b s 0 ∈ S ∩ capSet b s :=
        Finset.mem_inter.mpr ⟨h0S, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
      have hcard_lt : ¬ ((S ∩ capSet b s).erase (cubicCapV b s 0)).card ≤ 1 := by
        intro hle1
        rcases Finset.card_le_one_iff_subset_singleton.mp hle1 with ⟨u₀, hu₀⟩
        have hcheck : ∀ q₀ : Fin 7,
            (∀ z ∈ (S ∩ capSet b s).erase (cubicCapV b s 0), z = cubicCapV b s q₀.1) → False := by
          intro q₀ hsub
          obtain ⟨x, hxc4, hxq, hno⟩ := w7_no_single_dom_c4 q₀
          have hx0 : x ≠ 0 := by rcases hxc4 with rfl | rfl | rfl | rfl <;> decide
          have hno0 : w7Adj x 0 = false := by rcases hxc4 with rfl | rfl | rfl | rfl <;> decide
          rcases hdom_cap b hb s hs x hx0 with hmem | ⟨y, hyS, hya⟩
          · have hne0 : cubicCapV b s x.1 ≠ cubicCapV b s 0 := fun h ↦
              hx0 (Fin.ext (cubicCapV_injective (by omega) (by omega) x.2 (by omega) h).2.2)
            have heq := hsub _ (Finset.mem_erase.mpr
              ⟨hne0, Finset.mem_inter.mpr ⟨hmem, Finset.mem_image.mpr ⟨x, by simp, rfl⟩⟩⟩)
            exact hxq (Fin.ext (cubicCapV_injective (by omega) (by omega) x.2 q₀.2 heq).2.2)
          · have hy0 : y ≠ 0 := by intro hy0; subst hy0; simp [hno0] at hya
            have hne0 : cubicCapV b s y.1 ≠ cubicCapV b s 0 := fun h ↦
              hy0 (Fin.ext (cubicCapV_injective (by omega) (by omega) y.2 (by omega) h).2.2)
            have heq := hsub _ (Finset.mem_erase.mpr
              ⟨hne0, Finset.mem_inter.mpr ⟨hyS, Finset.mem_image.mpr ⟨y, by simp, rfl⟩⟩⟩)
            have hyq : y = q₀ :=
              Fin.ext (cubicCapV_injective (by omega) (by omega) y.2 q₀.2 heq).2.2
            subst hyq
            rw [w7Adj_symm y x] at hno
            simp [hno] at hya
        by_cases hu_cap : ∃ q₀ : Fin 7, u₀ = cubicCapV b s q₀.1
        · obtain ⟨q₀, rfl⟩ := hu_cap
          exact hcheck q₀ fun z hz ↦ Finset.mem_singleton.mp (hu₀ hz)
        · exact hcheck 0 fun z hz ↦ by
            have := Finset.mem_singleton.mp (hu₀ hz)
            obtain ⟨q, _, rfl⟩ :=
              Finset.mem_image.mp (Finset.mem_inter.mp (Finset.mem_erase.mp hz).2).2
            exact (hu_cap ⟨q, this.symm⟩).elim
      have := Finset.card_erase_add_one h0mem; omega
    let allCap : Finset ℕ := slots.biUnion fun p ↦ S ∩ capSet p.1 p.2
    have hallCap_sub : allCap ⊆ S := Finset.biUnion_subset.mpr fun _ _ ↦ Finset.inter_subset_left
    have hallCap_disj : Disjoint (S ∩ B.vertices.toFinset) allCap := by
      refine Finset.disjoint_left.mpr fun w hwB hwC ↦ ?_
      have hwV := List.mem_toFinset.mp (Finset.mem_inter.mp hwB).2
      obtain ⟨⟨b, s⟩, _, hwCap⟩ := Finset.mem_biUnion.mp hwC
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hwCap).2
      exact hmod _ hwV (by unfold cubicCapV; omega)
    have hallCap_pw : (slots : Set (ℕ × ℕ)).PairwiseDisjoint fun p ↦ S ∩ capSet p.1 p.2 := by
      intro ⟨b₁, s₁⟩ hp₁ ⟨b₂, s₂⟩ hp₂ hne
      simp only [Finset.mem_coe, slots, Finset.mem_biUnion, Finset.mem_image,
        List.mem_toFinset, List.mem_range, Prod.mk.injEq] at hp₁ hp₂
      obtain ⟨_, _, _, hs₁, rfl, rfl⟩ := hp₁
      obtain ⟨_, _, _, hs₂, rfl, rfl⟩ := hp₂
      refine Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_
      obtain ⟨q₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hw₁).2
      obtain ⟨q₂, _, h⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hw₂).2
      have := cubicCapV_injective (by omega) (by omega) q₁.2 q₂.2 h.symm
      exact hne (Prod.ext this.1 this.2.1)
    have hforced_le : forced.card + 2 * T ≤ allCap.card := by
      let wit : ℕ → ℕ × ℕ := fun b ↦
        if h : ∃ s < 3 - cubicGraphDegBool B b, cubicCapV b s 0 ∈ S then (b, h.choose) else (b, 0)
      have hwit_mem : ∀ b ∈ forced, wit b ∈ slots := fun b hb ↦ by
        have hex : ∃ s < 3 - cubicGraphDegBool B b, cubicCapV b s 0 ∈ S :=
          (Finset.mem_filter.mp hb).2
        simp only [wit, hex, ↓reduceDIte, slots, Finset.mem_biUnion, Finset.mem_image,
          List.mem_toFinset, List.mem_range]
        exact ⟨b, List.mem_toFinset.mp (Finset.mem_filter.mp hb).1,
          hex.choose, hex.choose_spec.1, rfl⟩
      have hwit_inj : Set.InjOn wit (forced : Set ℕ) := fun b₁ hb₁ b₂ hb₂ h ↦ by
        have h1 : ∃ s < 3 - cubicGraphDegBool B b₁, cubicCapV b₁ s 0 ∈ S :=
          (Finset.mem_filter.mp hb₁).2
        have h2 : ∃ s < 3 - cubicGraphDegBool B b₂, cubicCapV b₂ s 0 ∈ S :=
          (Finset.mem_filter.mp hb₂).2
        simp only [wit, h1, h2, ↓reduceDIte, Prod.mk.injEq] at h; exact h.1
      have hge : ∑ p ∈ slots, (S ∩ capSet p.1 p.2).card ≥
          ∑ p ∈ slots, (2 + if p ∈ forced.image wit then 1 else 0) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        simp only [slots, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset,
          List.mem_range] at hp
        obtain ⟨b, hb, s, hs, rfl⟩ := hp
        split_ifs with hmem
        · obtain ⟨b', hb', hwb⟩ := Finset.mem_image.mp hmem
          have h' : ∃ s' < 3 - cubicGraphDegBool B b', cubicCapV b' s' 0 ∈ S :=
            (Finset.mem_filter.mp hb').2
          simp only [wit, h', ↓reduceDIte, Prod.mk.injEq] at hwb
          rcases hwb with ⟨rfl, rfl⟩
          exact hcap_ge3 b' hb h'.choose hs h'.choose_spec.2
        · exact hcap_ge2 b hb s hs
      rw [Finset.card_biUnion hallCap_pw]
      have hsum_split : ∑ p ∈ slots, (2 + if p ∈ forced.image wit then 1 else 0) =
          2 * slots.card + (forced.image wit).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
          Finset.sum_boole, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (Finset.image_subset_iff.mpr hwit_mem), Nat.cast_id]
      rw [hsum_split, hslots_card, Finset.card_image_of_injOn hwit_inj] at hge; omega
    have hD_card : D.card ≤ k := by
      have h1 : D.card ≤ (S ∩ B.vertices.toFinset).card + forced.card := Finset.card_union_le _ _
      have h2 : (S ∩ B.vertices.toFinset).card + allCap.card ≤ S.card := by
        rw [← Finset.card_union_of_disjoint hallCap_disj]
        exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left hallCap_sub)
      omega
    exact ⟨D, hD_sub, hD_dom, hD_card⟩
  · rintro ⟨D, hDB, hDdom, hDcard⟩
    let capPairs : Finset ℕ := slots.biUnion fun p ↦ {cubicCapV p.1 p.2 1, cubicCapV p.1 p.2 2}
    let S : Finset ℕ := D ∪ capPairs
    have hS_sub : ∀ v ∈ S, v ∈ G.vertices := fun v hv ↦ by
      rcases Finset.mem_union.mp hv with hD | hC
      · exact List.mem_append_left _ (hDB v hD)
      · simp only [capPairs, slots, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset,
          List.mem_range, Finset.mem_insert, Finset.mem_singleton] at hC
        obtain ⟨⟨b, s⟩, ⟨b', hb, s', hs', hpair⟩, hv_eq⟩ := hC
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        rcases hv_eq with rfl | rfl
        · exact mem_cappedGraphOf_cap hb hs' (by omega)
        · exact mem_cappedGraphOf_cap hb hs' (by omega)
    have hS_dom : ∀ v ∈ G.vertices, v ∈ S ∨ ∃ w ∈ S, G.toSimpleGraph.Adj v w := by
      intro v hv
      unfold G cappedGraphOf at hv
      simp only [polyRange_eq_range, List.mem_append, List.mem_flatMap, List.mem_range,
        List.mem_map] at hv
      rcases hv with hvB | ⟨b, hb, s, hs, q, hq, rfl⟩
      · rcases hDdom v hvB with hD | ⟨w, hwD, hadj⟩
        · exact Or.inl (Finset.mem_union_left _ hD)
        · exact Or.inr ⟨w, Finset.mem_union_left _ hwD,
            (cappedGraphOf_adj_iff hmod v w).mpr (Or.inl hadj)⟩
      · have hq7 : q < 7 := by simp at hq; omega
        have hmem_pair : ∀ r, r = 1 ∨ r = 2 → cubicCapV b s r ∈ S := fun r hr ↦
          Finset.mem_union_right _ (by
            simp only [capPairs, slots, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset,
              List.mem_range, Finset.mem_insert, Finset.mem_singleton]
            exact ⟨(b, s), ⟨b, hb, s, hs, rfl⟩, by rcases hr with rfl | rfl <;> simp⟩)
        rcases w7_dom_pair ⟨q, hq7⟩ with h1 | h2 | ha1 | ha2
        · have hq1 : q = 1 := congrArg Fin.val h1; subst hq1
          exact Or.inl (hmem_pair 1 (Or.inl rfl))
        · have hq2 : q = 2 := congrArg Fin.val h2; subst hq2
          exact Or.inl (hmem_pair 2 (Or.inr rfl))
        · refine Or.inr ⟨cubicCapV b s 1, hmem_pair 1 (Or.inl rfl),
            (cappedGraphOf_adj_iff hmod _ _).mpr (Or.inr ⟨b, hb, s, hs, Or.inr (Or.inr
              ⟨⟨q, hq7⟩, 1, by rw [w7Adj_symm]; exact ha1, rfl, rfl⟩)⟩)⟩
        · refine Or.inr ⟨cubicCapV b s 2, hmem_pair 2 (Or.inr rfl),
            (cappedGraphOf_adj_iff hmod _ _).mpr (Or.inr ⟨b, hb, s, hs, Or.inr (Or.inr
              ⟨⟨q, hq7⟩, 2, by rw [w7Adj_symm]; exact ha2, rfl, rfl⟩)⟩)⟩
    have hS_card : S.card ≤ k + 2 * T := by
      have hcap_le : capPairs.card ≤ 2 * T :=
        calc capPairs.card ≤
              ∑ p ∈ slots, ({cubicCapV p.1 p.2 1, cubicCapV p.1 p.2 2} : Finset ℕ).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _ ∈ slots, 2 := Finset.sum_le_sum fun _ _ ↦ Finset.card_le_two
          _ = 2 * T := by rw [Finset.sum_const, smul_eq_mul, mul_comm, hslots_card]
      exact (Finset.card_union_le _ _).trans (by omega)
    exact ⟨S, hS_sub, hS_dom, hS_card⟩

/-- `cubicCapV` is computable in polynomial time. -/
theorem computableInPolyTime_cubicCapV :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ cubicCapV q.1.1 q.1.2 q.2)
      (encPair (encPair encNat encUnary) encUnary) encNat := by
  unfold cubicCapV
  have h3u : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ 3 * q.1.1)
      (encPair (encPair encNat encUnary) encUnary) encNat :=
    binary_mul.comp ((ComputableInPolyTime.const (encOut := encNat) 3).pair (by fun_prop))
  have h3us : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ 3 * q.1.1 + q.1.2)
      (encPair (encPair encNat encUnary) encUnary) encNat :=
    binary_add' h3u (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have h7 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ 7 * (3 * q.1.1 + q.1.2))
      (encPair (encPair encNat encUnary) encUnary) encNat :=
    binary_mul.comp ((ComputableInPolyTime.const (encOut := encNat) 7).pair h3us)
  have h7q : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ 7 * (3 * q.1.1 + q.1.2) + q.2)
      (encPair (encPair encNat encUnary) encUnary) encNat :=
    binary_add' h7 (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have h4 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ ↦ 4 * (7 * (3 * q.1.1 + q.1.2) + q.2))
      (encPair (encPair encNat encUnary) encUnary) encNat :=
    binary_mul.comp ((ComputableInPolyTime.const (encOut := encNat) 4).pair h7q)
  exact binary_add' h4 (ComputableInPolyTime.const 3)

/-- `cappedGraphOf` is computable in polynomial time. -/
theorem computableInPolyTime_cappedGraphOf :
    ComputableInPolyTime cappedGraphOf encGraph encGraph := by
  unfold cappedGraphOf
  have hdeg3 : ComputableInPolyTime (fun p : Graph × ℕ ↦ 3 - cubicGraphDegBool p.1 p.2)
      (encPair encGraph encNat) encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.const 3)
      computableInPolyTime_cubicGraphDegBool
  have hGverts : ComputableInPolyTime Graph.vertices encGraph (encList encNat) := by fun_prop
  have hGsnd : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2) (encPair encGraph encNat) encNat := by
    fun_prop
  have hcv : ComputableInPolyTime
      (fun B : Graph ↦ B.vertices.flatMap fun u ↦
        (polyRange (3 - cubicGraphDegBool B u)).flatMap fun s ↦
          [0, 1, 2, 3, 4, 5, 6].map fun q ↦ cubicCapV u s q)
      encGraph (encList encNat) := by
    have hq7 : ComputableInPolyTime
        (fun q : ℕ × ℕ ↦ [0, 1, 2, 3, 4, 5, 6].map fun r ↦ cubicCapV q.1 q.2 r)
        (encPair encNat encUnary) (encList encNat) :=
      mapWith computableInPolyTime_cubicCapV ComputableInPolyTime.id'
        (ComputableInPolyTime.const (encOut := encList encUnary) [0, 1, 2, 3, 4, 5, 6])
    have hinner : ComputableInPolyTime
        (fun p : Graph × ℕ ↦
          (polyRange (3 - cubicGraphDegBool p.1 p.2)).flatMap fun s ↦
            [0, 1, 2, 3, 4, 5, 6].map fun q ↦ cubicCapV p.2 s q)
        (encPair encGraph encNat) (encList encNat) :=
      flatMapWith hq7 hGsnd (computableInPolyTime_polyRange.comp hdeg3)
    exact flatMapWithInput hGverts hinner
  have hce : ComputableInPolyTime
      (fun B : Graph ↦ B.vertices.flatMap fun u ↦
        (polyRange (3 - cubicGraphDegBool B u)).flatMap fun s ↦
          (u, cubicCapV u s 0) :: w7Edges.map fun e ↦ (cubicCapV u s e.1, cubicCapV u s e.2))
      encGraph (encList (encPair encNat encNat)) := by
    have hhd : ComputableInPolyTime (fun q : ℕ × ℕ ↦ (q.1, cubicCapV q.1 q.2 0))
        (encPair encNat encUnary) (encPair encNat encNat) :=
      (by fun_prop : ComputableInPolyTime (fun q : ℕ × ℕ ↦ q.1) _ encNat).pair
        (computableInPolyTime_cubicCapV.comp
          (ComputableInPolyTime.id'.pair (ComputableInPolyTime.const (encOut := encUnary) 0)))
    have hpairE : ComputableInPolyTime
        (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ (cubicCapV p.1.1 p.1.2 p.2.1, cubicCapV p.1.1 p.1.2 p.2.2))
        (encPair (encPair encNat encUnary) (encPair encUnary encUnary)) (encPair encNat encNat) :=
      (computableInPolyTime_cubicCapV.comp
        ((by fun_prop : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.1) _ _).pair
          (by fun_prop : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2.1) _
            encUnary))).pair
      (computableInPolyTime_cubicCapV.comp
        ((by fun_prop : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.1) _ _).pair
          (by fun_prop : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2.2) _
            encUnary)))
    have htl : ComputableInPolyTime
        (fun q : ℕ × ℕ ↦ w7Edges.map fun e ↦ (cubicCapV q.1 q.2 e.1, cubicCapV q.1 q.2 e.2))
        (encPair encNat encUnary) (encList (encPair encNat encNat)) :=
      mapWith hpairE ComputableInPolyTime.id'
        (ComputableInPolyTime.const (encOut := encList (encPair encUnary encUnary)) w7Edges)
    have hstep := ComputableInPolyTime.cons' hhd htl
    have hinner : ComputableInPolyTime
        (fun p : Graph × ℕ ↦
          (polyRange (3 - cubicGraphDegBool p.1 p.2)).flatMap fun s ↦
            (p.2, cubicCapV p.2 s 0) ::
              w7Edges.map fun e ↦ (cubicCapV p.2 s e.1, cubicCapV p.2 s e.2))
        (encPair encGraph encNat) (encList (encPair encNat encNat)) :=
      flatMapWith hstep hGsnd (computableInPolyTime_polyRange.comp hdeg3)
    exact flatMapWithInput hGverts hinner
  have hverts := (ComputableInPolyTime.listAppend encNat).comp (hGverts.pair hcv)
  have hedges := (ComputableInPolyTime.listAppend (encPair encNat encNat)).comp
    ((by fun_prop : ComputableInPolyTime Graph.edges encGraph _).pair hce)
  exact encGraph_mk_polyTime hverts hedges

end CslibFrontier.Complexity
