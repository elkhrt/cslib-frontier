/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT.PolyTime
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Logics.Polymorphism.Graph

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Mathlib.Data.List.GetD

/-!
# Finite-Domain CSP Instances, $H$-Coloring, `NP` Membership, and Bipartite Tractability

This module introduces finite-domain single-relation constraint satisfaction problems `CSP(R)` and
graph homomorphism problems `$H$-Coloring` on canonical `CslibFrontier` multi-tape Turing-machine
encodings, together with:

1. `NP` membership for every finite-domain `CSP(R)` and `$H$-Coloring`.
2. Polynomial-time equivalence between `CSP(E_H)` and `$H$-Coloring` (for nonempty target vertex
   sets).
3. Polynomial-time decidability of `$H$-Coloring` for every bipartite simple graph $H$ (via 2-SAT).
4. `NP`-completeness of `$K_V$-Coloring` for every finite vertex set $V$ with $|V| \ge 3$.
5. Impossibility of `NP`-completeness for trivial `CSP(R)`.

## Main definitions

* `Cslib.Complexity.CSPInstance`, `Cslib.Complexity.encTuple`,
  `Cslib.Complexity.encCSPInstance`: finite-domain single-relation CSP instances and their
  binary framed-list encoding.
* `Cslib.Complexity.CSPRel`: the decision problem `CSP(R)`.
* `Cslib.Complexity.HColoring`: the graph homomorphism problem `$H$-Coloring` on
  `Cslib.Complexity.Graph`.

## Main results

* `Cslib.Complexity.CSPRel.mem_NP`, `Cslib.Complexity.HColoring.mem_NP`: `NP` membership.
* `Cslib.Complexity.HColoring.mem_P_of_isBipartite`: bipartite `$H$-Coloring` is in `P`.
* `Cslib.Complexity.HColoring.npComplete_top`: $K_V$-Coloring ($|V| \ge 3$) is `NP`-complete.
* `Cslib.Complexity.CSPRel.polyTimeReducible_edgeRel_hColoring`,
  `Cslib.Complexity.HColoring.polyTimeReducible_cspRel_edgeRel`: polynomial-time equivalence
  between `CSP(E_H)` and `$H$-Coloring`.
* `Cslib.Complexity.CSPRel.not_npComplete_of_trivial`: trivial `CSP(R)` is never `NP`-complete.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic Cslib.Logic.SimpleGraph Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Finite-domain single-relation CSP instances and encodings -/

/-- An instance of `CSP(R)` for an `n`-ary relation `R` is a finite list of `n`-tuples of
variables in `ℕ`. Every syntactic instance is well-formed. -/
abbrev CSPInstance (n : ℕ) : Type := List (Fin n → ℕ)

/-- Binary framed-list encoding of a fixed-arity variable tuple `Fin n → ℕ`. -/
@[expose] def encTuple (n : ℕ) : (Fin n → ℕ) ↪ List Bool where
  toFun t := encList encNat (List.ofFn t)
  inj' _ _ h := List.ofFn_injective ((encList encNat).injective h)

/-- Binary encoding of a `CSPInstance n` as a framed list of encoded tuples. -/
def encCSPInstance (n : ℕ) : CSPInstance n ↪ List Bool :=
  encList (encTuple n)

/-- Raw list representation of a `CSPInstance n`. -/
@[expose] def CSPInstance.toRaw {n : ℕ} (I : CSPInstance n) : List (List ℕ) :=
  I.map List.ofFn

/-- Reconstruct a `CSPInstance n` from raw lists of variables (padding/truncating via `getD`). -/
@[expose] def CSPInstance.ofRaw (n : ℕ) (L : List (List ℕ)) : CSPInstance n :=
  L.map fun l i => l.getD i.val 0

/-- Encoding `I : CSPInstance n` agrees bit-for-bit with encoding `I.toRaw` as `List (List ℕ)`. -/
theorem encCSPInstance_eq_encList_toRaw {n : ℕ} (I : CSPInstance n) :
    encCSPInstance n I = encList (encList encNat) I.toRaw := by
  induction I with
  | nil => rfl
  | cons t ts ih =>
    simp only [encCSPInstance, CSPInstance.toRaw, List.map_cons, encList_cons] at ih ⊢
    rw [ih]
    rfl

/-- `CSPInstance.toRaw` is polynomial-time computable. -/
theorem computableInPolyTime_toRaw (n : ℕ) :
    ComputableInPolyTime (CSPInstance.toRaw (n := n))
      (encCSPInstance n) (encList (encList encNat)) :=
  ComputableInPolyTime.id'.of_enc_eq fun I => (encCSPInstance_eq_encList_toRaw I).symm

/-- Converting a polynomial-time list-of-lists constructor whose outputs all have length `n` into a
polynomial-time `CSPInstance n` constructor. -/
theorem computableInPolyTime_ofRaw_comp {α : Type} {encA : α ↪ List Bool} (n : ℕ)
    {g : α → List (List ℕ)}
    (hg : ComputableInPolyTime g encA (encList (encList encNat)))
    (hlen : ∀ a, ∀ l ∈ g a, l.length = n) :
    ComputableInPolyTime (fun a => CSPInstance.ofRaw n (g a)) encA (encCSPInstance n) := by
  refine hg.of_enc_eq fun a => ?_
  rw [encCSPInstance_eq_encList_toRaw]
  congr 1
  simp only [CSPInstance.toRaw, CSPInstance.ofRaw, List.map_map]
  symm
  have hmap_eq : ∀ (L : List (List ℕ)), (∀ l ∈ L, l.length = n) →
      L.map (List.ofFn ∘ fun l (i : Fin n) => l.getD i.val 0) = L := by
    intro L hL
    induction L with
    | nil => rfl
    | cons l ls ih =>
      simp only [List.map_cons, ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
      congr 1
      have hln : l.length = n := hL l List.mem_cons_self
      refine List.ext_getElem (by simp [hln]) fun i hi _ => ?_
      simp only [Function.comp_apply, List.getElem_ofFn]
      rw [List.getD_eq_getElem _ _ (by omega)]
  exact (hmap_eq (g a) (hlen a)).symm

/-- All variable occurrences of a CSP instance, in order. -/
@[expose] def CSPInstance.vars {n : ℕ} (I : CSPInstance n) : List ℕ :=
  I.flatMap List.ofFn

/-- Number of distinct variables occurring in a CSP instance. -/
@[expose] def CSPInstance.numVars {n : ℕ} (I : CSPInstance n) : ℕ :=
  I.vars.toFinset.card

/-- Distinct variables of a CSP instance in order of first occurrence. -/
@[expose] def CSPInstance.distinctVars {n : ℕ} (I : CSPInstance n) : List ℕ :=
  Cslib.Complexity.selectDistinct I.vars (List.replicate I.vars.length true)

/-- The decision problem `CSP(R)` for a relation `R : Set (Fin n → D)`. -/
@[expose] def CSPRel {D : Type*} {n : ℕ} (R : Set (Fin n → D)) : Set (CSPInstance n) :=
  {I | ∃ σ : ℕ → D, ∀ t ∈ I, (σ ∘ t) ∈ R}

/-- The graph homomorphism problem `$H$-Coloring` on `Cslib.Complexity.Graph`. -/
@[expose] def HColoring {V : Type*} (H : _root_.SimpleGraph V) : Set Cslib.Complexity.Graph :=
  {G | Nonempty (G.induced →g H)}

/-- Membership in `HColoring H` written as a map `ℕ → V` when `V` is nonempty. -/
theorem mem_HColoring_iff_of_nonempty {V : Type*} [Nonempty V] {H : _root_.SimpleGraph V}
    {G : Cslib.Complexity.Graph} :
    G ∈ HColoring H ↔
      ∃ f : ℕ → V, ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v →
        H.Adj (f u) (f v) := by
  classical
  constructor
  · rintro ⟨φ⟩
    obtain ⟨v0⟩ := ‹Nonempty V›
    refine ⟨fun u => if hu : u ∈ G.vertices then φ ⟨u, hu⟩ else v0, fun u hu v hv huv => ?_⟩
    have hadj_ind : G.induced.Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
    simpa only [hu, hv, dite_true] using φ.map_rel hadj_ind
  · rintro ⟨f, hf⟩
    exact ⟨⟨fun u => f u.1, fun {u v} huv => hf u.1 u.2 v.1 v.2 huv⟩⟩

/-- `HColoring` of the complete graph on `Fin k` is identically `KColoring k`. -/
theorem hColoring_top_eq_kColoring (k : ℕ) :
    HColoring (⊤ : _root_.SimpleGraph (Fin k)) = KColoring k := by
  ext G
  rfl

/-- Trivial `CSP(R)` (every instance satisfiable) is never `NP`-complete, even if `P = NP`. -/
theorem CSPRel.not_npComplete_of_trivial {D : Type*} {n : ℕ} {R : Set (Fin n → D)}
    (htriv : CSPRel R = Set.univ) : ¬ NPComplete (encCSPInstance n) (CSPRel R) := by
  intro hnpc
  have hEmpty_P : (∅ : Set Bool) ∈ P encBool :=
    ⟨fun _ => false, ComputableInPolyTime.const false, fun b => by simp⟩
  have hEmpty_NP : (∅ : Set Bool) ∈ NP encBool := P_subset_NP hEmpty_P
  obtain ⟨f, _, hred⟩ := hnpc.2 encBool (∅ : Set Bool) hEmpty_NP
  have := (hred true).mpr (by rw [htriv]; trivial)
  exact this

/-! ### `NP` membership for `CSPRel` and `HColoring` -/

/-- Every finite-domain `CSP(R)` belongs to `NP`. -/
theorem CSPRel.mem_NP {D : Type*} [Finite D] {n : ℕ} (R : Set (Fin n → D)) :
    CSPRel R ∈ NP (encCSPInstance n) := by
  have : Fintype D := Fintype.ofFinite D
  classical
  let k : ℕ := Fintype.card D
  by_cases hk : k = 0
  · have hEmpty : IsEmpty D := Fintype.card_eq_zero_iff.mp hk
    have hCSPEmpty : CSPRel R = ∅ := by
      ext I
      simp only [CSPRel, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro σ _
      exact isEmptyElim (σ 0)
    rw [hCSPEmpty]
    exact P_subset_NP ⟨fun _ => false, ComputableInPolyTime.const false, fun _ => by simp⟩
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let e : D ≃ Fin k := Fintype.equivFinOfCardEq rfl
    let R_nat : List (List ℕ) :=
      ((Set.toFinite R).toFinset.toList).map fun t => List.ofFn fun i => (e (t i)).val
    have hR_nat_mem : ∀ (c : ℕ → ℕ) (t : Fin n → ℕ) (hc : ∀ i, c (t i) < k),
        List.ofFn (fun i => c (t i)) ∈ R_nat ↔
          (fun i => e.symm ⟨c (t i), hc i⟩) ∈ R := by
      intro c t hc
      simp only [R_nat, List.mem_map, Set.Finite.mem_toFinset, Finset.mem_toList]
      constructor
      · rintro ⟨a, ha, hEq⟩
        have hfun : (fun i => e.symm ⟨c (t i), hc i⟩) = a := by
          funext i
          have hi := congrArg (fun l => l.getD i.val 0) hEq
          have hlen1 : i.val < (List.ofFn fun i : Fin n => (e (a i)).val).length := by simp
          have hlen2 : i.val < (List.ofFn fun i : Fin n => c (t i)).length := by simp
          rw [List.getD_eq_getElem _ _ hlen1, List.getD_eq_getElem _ _ hlen2,
            List.getElem_ofFn, List.getElem_ofFn] at hi
          apply e.injective
          apply Fin.ext
          simpa using hi.symm
        rwa [hfun]
      · intro hmem
        refine ⟨fun i => e.symm ⟨c (t i), hc i⟩, hmem, ?_⟩
        refine List.ext_getElem (by simp) fun i hi _ => ?_
        simp
    let verifier : CSPInstance n × List Bool → Bool := fun x =>
      let raw := x.1.toRaw
      let V := raw.flatten
      let c := KColoring.colorOf k V x.2
      V.all (fun v => decide (c v < k)) &&
        raw.all (fun l => R_nat.any (fun r => decide (l.map c = r)))
    have hV_len : ∀ I : CSPInstance n, I.toRaw.flatten.length ≤ (encCSPInstance n I).length := by
      intro I
      rw [encCSPInstance_eq_encList_toRaw]
      induction I.toRaw with
      | nil => simp
      | cons l ls ih =>
        have h1 : l.length ≤ (encList encNat l).length := length_le_length_encList encNat l
        simp only [encList_cons, List.length_append, List.flatten_cons, List.length_flatten] at *
        have := length_frame (encList encNat l)
        omega
    have hVer : IsVerifier (encCSPInstance n) (Polynomial.C k * Polynomial.X) verifier
        (CSPRel R) := by
      intro I
      simp only [CSPRel, Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, verifier, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro ⟨σ, hσ⟩
        let V := I.toRaw.flatten
        let c : ℕ → ℕ := fun v => (e (σ v)).val
        let w := unaryBlocks k (k * (encCSPInstance n I).length) (fun i => c (V.getD i 0))
        have hcol : ∀ v ∈ V, KColoring.colorOf k V w v = c v := by
          intro v hv
          have hlt : V.idxOf v < V.length := List.idxOf_lt_length_iff.2 hv
          have hget : V.getD (V.idxOf v) 0 = v := by
            rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
          have hlen : V.length ≤ (encCSPInstance n I).length := hV_len I
          have hidx_le : V.idxOf v + 1 ≤ (encCSPInstance n I).length :=
            Nat.lt_of_lt_of_le hlt hlen
          rw [KColoring.colorOf, countP_unaryBlocks (by rw [hget]; exact (e (σ v)).isLt.le)
            (Nat.mul_le_mul_left k hidx_le), hget]
        refine ⟨w, length_unaryBlocks .., ?_, ?_⟩
        · intro v hv
          rw [hcol v hv]
          exact (e (σ v)).isLt
        · intro l hl
          simp only [CSPInstance.toRaw, List.mem_map] at hl
          rcases hl with ⟨t, ht, rfl⟩
          have hmap : (List.ofFn t).map (KColoring.colorOf k V w) =
              List.ofFn (fun i => c (t i)) := by
            rw [List.map_ofFn]
            refine congrArg List.ofFn (funext fun i => hcol (t i) ?_)
            exact List.mem_flatten.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
              List.mem_ofFn.mpr ⟨i, rfl⟩⟩
          rw [hmap]
          have hmem := (hR_nat_mem c t (fun i => (e (σ (t i))).isLt)).mpr
          have hEq : (fun i => e.symm ⟨c (t i), (e (σ (t i))).isLt⟩) = σ ∘ t := by
            funext i
            simp [c]
          rw [hEq] at hmem
          exact ⟨_, hmem (hσ t ht), rfl⟩
      · rintro ⟨w, -, hlt, hsat⟩
        let V := I.toRaw.flatten
        let c := KColoring.colorOf k V w
        let d0 : D := e.symm ⟨0, hkpos⟩
        let σ : ℕ → D := fun v => if hv : c v < k then e.symm ⟨c v, hv⟩ else d0
        refine ⟨σ, fun t ht => ?_⟩
        have ht_mem : ∀ i : Fin n, t i ∈ V := fun i =>
          List.mem_flatten.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
            List.mem_ofFn.mpr ⟨i, rfl⟩⟩
        have htc : ∀ i : Fin n, c (t i) < k := fun i => hlt (t i) (ht_mem i)
        obtain ⟨r, hr, hreq⟩ := hsat (List.ofFn t) (List.mem_map.mpr ⟨t, ht, rfl⟩)
        rw [List.map_ofFn] at hreq
        have hmem := (hR_nat_mem c t htc).mp (hreq.symm ▸ hr)
        have hEq : σ ∘ t = fun i => e.symm ⟨c (t i), htc i⟩ := by
          funext i
          simp [σ, htc i]
        rw [hEq]
        exact hmem
    have hpoly : ComputableInPolyTime verifier
        (encPair (encCSPInstance n) encBits) encBool := by
      have hraw : ComputableInPolyTime (fun x : CSPInstance n × List Bool => x.1.toRaw)
          (encPair (encCSPInstance n) encBits) (encList (encList encNat)) :=
        (computableInPolyTime_toRaw n).comp (fst _ _)
      have hV : ComputableInPolyTime (fun x : CSPInstance n × List Bool => x.1.toRaw.flatten)
          (encPair (encCSPInstance n) encBits) (encList encNat) :=
        (flatten (enc := encNat)).comp hraw
      have hcol : ComputableInPolyTime
          (fun p : (CSPInstance n × List Bool) × ℕ =>
            KColoring.colorOf k p.1.1.toRaw.flatten p.1.2 p.2)
          (encPair (encPair (encCSPInstance n) encBits) encNat) encUnary :=
        (KColoring.computableInPolyTime_colorOf k).comp
          (((hV.comp (fst _ _)).prod ((snd _ _).comp (fst _ _))).prod (snd _ _))
      have hpart1 : ComputableInPolyTime
          (fun x : CSPInstance n × List Bool =>
            x.1.toRaw.flatten.all fun v =>
              decide (KColoring.colorOf k x.1.toRaw.flatten x.2 v < k))
          (encPair (encCSPInstance n) encBits) encBool :=
        allWithInput hV (unary_lt' hcol (const k))
      have hmap : ComputableInPolyTime
          (fun p : (CSPInstance n × List Bool) × List ℕ =>
            p.2.map (KColoring.colorOf k p.1.1.toRaw.flatten p.1.2))
          (encPair (encPair (encCSPInstance n) encBits) (encList encNat)) (encList encUnary) :=
        mapWithInput (snd _ _) (hcol.comp (((fst _ _).comp (fst _ _)).prod (snd _ _)))
      have hRcheck : ComputableInPolyTime
          (fun p : (CSPInstance n × List Bool) × List ℕ =>
            R_nat.any fun r =>
              decide (p.2.map (KColoring.colorOf k p.1.1.toRaw.flatten p.1.2) = r))
          (encPair (encPair (encCSPInstance n) encBits) (encList encNat)) encBool :=
        anyConst R_nat fun r _ =>
          decide_eq' hmap (const (encOut := encList encUnary) r)
      have hpart2 : ComputableInPolyTime
          (fun x : CSPInstance n × List Bool =>
            x.1.toRaw.all fun l => R_nat.any fun r =>
              decide (l.map (KColoring.colorOf k x.1.toRaw.flatten x.2) = r))
          (encPair (encCSPInstance n) encBits) encBool :=
        allWithInput hraw hRcheck
      exact bool_and' hpart1 hpart2
    exact ⟨_, verifier, hpoly, hVer⟩

/-- Every finite graph homomorphism problem `HColoring H` belongs to `NP`. -/
theorem HColoring.mem_NP {V : Type*} [Finite V] (H : _root_.SimpleGraph V) :
    HColoring H ∈ NP encGraph := by
  have : Fintype V := Fintype.ofFinite V
  classical
  let k : ℕ := Fintype.card V
  by_cases hk : k = 0
  · have hEmpty : IsEmpty V := Fintype.card_eq_zero_iff.mp hk
    have hP : HColoring H ∈ P encGraph := by
      refine ⟨fun G => G.vertices.all (fun _ => false),
        allWithInput (by fun_prop) (const false), fun G => ?_⟩
      simp only [HColoring, Set.mem_ofPred_eq, List.all_eq_true, Bool.false_eq_true]
      constructor
      · rintro ⟨φ⟩ u hu
        exact isEmptyElim (φ ⟨u, hu⟩)
      · intro hno
        exact ⟨⟨fun u => False.elim (hno u.1 u.2), fun {u} => False.elim (hno u.1 u.2)⟩⟩
    exact P_subset_NP hP
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have : Nonempty V := Fintype.card_pos_iff.mp hkpos
    let e : V ≃ Fin k := Fintype.equivFinOfCardEq rfl
    let adjList : List (ℕ × ℕ) :=
      ((Finset.univ : Finset (V × V)).filter fun p => H.Adj p.1 p.2).toList.map
        fun p => ((e p.1).val, (e p.2).val)
    have hadj_mem : ∀ (c : ℕ → ℕ) (u v : ℕ) (hu : c u < k) (hv : c v < k),
        (c u, c v) ∈ adjList ↔ H.Adj (e.symm ⟨c u, hu⟩) (e.symm ⟨c v, hv⟩) := by
      intro c u v hu hv
      simp only [adjList, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨a, b⟩, hab, h1, h2⟩
        have ha : e.symm ⟨c u, hu⟩ = a := e.injective (by apply Fin.ext; simpa using h1.symm)
        have hb : e.symm ⟨c v, hv⟩ = b := e.injective (by apply Fin.ext; simpa using h2.symm)
        rwa [ha, hb]
      · intro h
        exact ⟨(e.symm ⟨c u, hu⟩, e.symm ⟨c v, hv⟩), h, by simp, by simp⟩
    let verifier : Cslib.Complexity.Graph × List Bool → Bool := fun x =>
      let c := KColoring.colorOf k x.1.vertices x.2
      x.1.vertices.all fun u => decide (c u < k) &&
        x.1.vertices.all fun v =>
          !(x.1.adjBool u v && !adjList.any (fun p => decide ((c u, c v) = p)))
    have hVer : IsVerifier encGraph (Polynomial.C k * Polynomial.X) verifier (HColoring H) := by
      intro G
      simp only [mem_HColoring_iff_of_nonempty, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, verifier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.not_eq_true', Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff, Bool.not_eq_false',
        List.any_eq_true]
      constructor
      · rintro ⟨f, hf⟩
        let c : ℕ → ℕ := fun v => (e (f v)).val
        let w := unaryBlocks k (k * (encGraph G).length) (fun i => c (G.vertices.getD i 0))
        have hcol : ∀ v ∈ G.vertices, KColoring.colorOf k G.vertices w v = c v := by
          intro v hv
          have hlt : G.vertices.idxOf v < G.vertices.length := List.idxOf_lt_length_iff.2 hv
          have hget : G.vertices.getD (G.vertices.idxOf v) 0 = v := by
            rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
          have hlen := G.length_vertices_le_encGraph
          rw [KColoring.colorOf, countP_unaryBlocks (by rw [hget]; exact (e (f v)).isLt.le)
            (Nat.mul_le_mul_left k (by omega)), hget]
        refine ⟨w, length_unaryBlocks .., fun u hu => ⟨by rw [hcol u hu]; exact (e (f u)).isLt,
          fun v hv => ?_⟩⟩
        rw [hcol u hu, hcol v hv]
        by_cases huv : G.toSimpleGraph.Adj u v
        · right
          have hmem := (hadj_mem c u v (e (f u)).isLt (e (f v)).isLt).mpr
          have hfu : e.symm ⟨c u, (e (f u)).isLt⟩ = f u := by simp [c]
          have hfv : e.symm ⟨c v, (e (f v)).isLt⟩ = f v := by simp [c]
          rw [hfu, hfv] at hmem
          exact ⟨(c u, c v), hmem (hf u hu v hv huv), rfl⟩
        · exact Or.inl huv
      · rintro ⟨w, -, hw⟩
        let c := KColoring.colorOf k G.vertices w
        let v0 : V := e.symm ⟨0, hkpos⟩
        refine ⟨fun u => if hu : c u < k then e.symm ⟨c u, hu⟩ else v0,
          fun u hu v hv huv => ?_⟩
        have hcu : c u < k := (hw u hu).1
        have hcv : c v < k := (hw v hv).1
        rcases (hw u hu).2 v hv with hno | ⟨p, hp, hpeq⟩
        · exact (hno huv).elim
        · simp only [hcu, hcv, dite_true]
          exact (hadj_mem c u v hcu hcv).mp (hpeq.symm ▸ hp)
    have hpoly : ComputableInPolyTime verifier (encPair encGraph encBits) encBool := by
      have hV : ComputableInPolyTime (fun x : Cslib.Complexity.Graph × List Bool => x.1.vertices)
          (encPair encGraph encBits) (encList encNat) := by fun_prop
      have hcol : ComputableInPolyTime
          (fun p : (Cslib.Complexity.Graph × List Bool) × ℕ =>
            KColoring.colorOf k p.1.1.vertices p.1.2 p.2)
          (encPair (encPair encGraph encBits) encNat) encUnary :=
        (KColoring.computableInPolyTime_colorOf k).comp
          (g := fun p : (Cslib.Complexity.Graph × List Bool) × ℕ =>
            ((p.1.1.vertices, p.1.2), p.2)) (by fun_prop)
      have hproj : ComputableInPolyTime
          (fun p : ((Cslib.Complexity.Graph × List Bool) × ℕ) × ℕ => ((p.1.1.1, p.1.2), p.2))
          (encPair (encPair (encPair encGraph encBits) encNat) encNat)
          (encPair (encPair encGraph encNat) encNat) := by fun_prop
      have hproj' : ComputableInPolyTime
          (fun p : ((Cslib.Complexity.Graph × List Bool) × ℕ) × ℕ => (p.1.1, p.2))
          (encPair (encPair (encPair encGraph encBits) encNat) encNat)
          (encPair (encPair encGraph encBits) encNat) := by fun_prop
      have hpair : ComputableInPolyTime
          (fun p : ((Cslib.Complexity.Graph × List Bool) × ℕ) × ℕ =>
            (KColoring.colorOf k p.1.1.1.vertices p.1.1.2 p.1.2,
             KColoring.colorOf k p.1.1.1.vertices p.1.1.2 p.2))
          (encPair (encPair (encPair encGraph encBits) encNat) encNat)
          (encPair encUnary encUnary) :=
        (hcol.comp (fst _ _)).prod (hcol.comp hproj')
      have hcheckAdj : ComputableInPolyTime
          (fun p : ((Cslib.Complexity.Graph × List Bool) × ℕ) × ℕ =>
            adjList.any fun q =>
              decide ((KColoring.colorOf k p.1.1.1.vertices p.1.1.2 p.1.2,
                       KColoring.colorOf k p.1.1.1.vertices p.1.1.2 p.2) = q))
          (encPair (encPair (encPair encGraph encBits) encNat) encNat) encBool :=
        anyConst adjList fun q _ => decide_eq' hpair (const (encOut := encPair encUnary encUnary) q)
      exact allWithInput hV (bool_and' (unary_lt' hcol (const k))
        (allWithInput (hV.comp (fst _ _)) (bool_not.comp
          (bool_and' (Graph.computableInPolyTime_adjBool.comp hproj)
            (bool_not.comp hcheckAdj)))))
    exact ⟨_, verifier, hpoly, hVer⟩

/-! ### Bipartite tractability (`HColoring H ∈ P`) and clique `NP`-completeness -/

/-- For every bipartite simple graph `H`, `$H$-Coloring` is decidable in polynomial time
(reducing to `TwoSAT ∈ P` when `H` has an edge, and checking edgelessness / empty vertex list
otherwise). -/
theorem HColoring.mem_P_of_isBipartite {V : Type*} {H : _root_.SimpleGraph V}
    (hH : H.IsBipartite) : HColoring H ∈ P encGraph := by
  classical
  by_cases hEmpty : IsEmpty V
  · refine ⟨fun G => G.vertices.all (fun _ => false),
      allWithInput (by fun_prop) (const false), fun G => ?_⟩
    simp only [HColoring, Set.mem_ofPred_eq, List.all_eq_true, Bool.false_eq_true]
    constructor
    · rintro ⟨φ⟩ u hu
      exact isEmptyElim (φ ⟨u, hu⟩)
    · intro hno
      exact ⟨⟨fun u => False.elim (hno u.1 u.2), fun {u} => False.elim (hno u.1 u.2)⟩⟩
  · have : Nonempty V := not_isEmpty_iff.mp hEmpty
    by_cases hedge : ∃ u v : V, H.Adj u v
    · -- `H` is bipartite with an edge: `HColoring H = KColoring 2`,
      -- reduced in poly-time to `TwoSAT`.
      rcases hedge with ⟨u0, v0, huv0⟩
      rcases hH with ⟨col⟩
      have hEq : HColoring H = KColoring 2 := by
        ext G
        rw [← hColoring_top_eq_kColoring 2]
        constructor
        · rintro ⟨φ⟩; exact ⟨col.comp φ⟩
        · rintro ⟨ψ⟩
          let emb : (⊤ : _root_.SimpleGraph (Fin 2)) →g H :=
            { toFun := ![u0, v0]
              map_rel' := fun {a b} hab => by
                fin_cases a <;> fin_cases b
                · exact (hab rfl).elim
                · exact huv0
                · exact huv0.symm
                · exact (hab rfl).elim }
          exact ⟨emb.comp ψ⟩
      rw [hEq]
      let to2SAT : Cslib.Complexity.Graph → CNF ℕ := fun G =>
        (G.edges.filter fun e =>
          decide (e.1 ≠ e.2) && decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices)).flatMap
          fun e => [[(e.1, true), (e.2, true)], [(e.1, false), (e.2, false)]]
      have hpoly : ComputableInPolyTime to2SAT encGraph encCNF := by
        unfold to2SAT encCNF
        fun_prop
      have hred : PolyTimeReducible encGraph encCNF (KColoring 2) TwoSAT := by
        refine ⟨to2SAT, hpoly, fun G => ?_⟩
        rw [mem_KColoring_iff, mem_TwoSAT]
        constructor
        · rintro ⟨c, hlt, hc⟩
          refine ⟨fun cl hcl => ?_, ?_⟩
          · simp only [to2SAT, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hcl
            rcases hcl with ⟨e, _, rfl | rfl⟩ <;> simp
          · refine ⟨fun v => decide (c v = 0), (CNF.eval_eq_true_iff _ _).mpr fun cl hcl => ?_⟩
            simp only [to2SAT, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
              decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hcl
            rcases hcl with ⟨e, ⟨he, ⟨hne, hu⟩, hv⟩, rfl | rfl⟩
            · have hdiff := hc e.1 hu e.2 hv (Graph.toSimpleGraph_adj.mpr ⟨hne, Or.inl he⟩)
              have h1 := hlt e.1 hu; have h2 := hlt e.2 hv
              rw [Clause.eval_eq_true_iff]
              by_cases h0 : c e.1 = 0
              · exact ⟨(e.1, true), by simp, by simp [h0]⟩
              · have : c e.2 = 0 := by omega
                exact ⟨(e.2, true), by simp, by simp [this]⟩
            · have hdiff := hc e.1 hu e.2 hv (Graph.toSimpleGraph_adj.mpr ⟨hne, Or.inl he⟩)
              have h1 := hlt e.1 hu; have h2 := hlt e.2 hv
              rw [Clause.eval_eq_true_iff]
              by_cases h0 : c e.1 = 0
              · have : c e.2 ≠ 0 := by omega
                exact ⟨(e.2, false), by simp, by simp [this]⟩
              · exact ⟨(e.1, false), by simp, by simp [h0]⟩
        · rintro ⟨_, τ, hτ⟩
          have hall := (CNF.eval_eq_true_iff _ _).mp hτ
          refine ⟨fun v => if τ v then 0 else 1, fun v _ => by cases h : τ v <;> simp [h],
            fun u hu v hv huv => ?_⟩
          rw [Graph.toSimpleGraph_adj] at huv
          rcases huv with ⟨hne, he | he⟩
          · have hmem : (u, v) ∈ G.edges.filter (fun e =>
                decide (e.1 ≠ e.2) && decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices)) :=
              List.mem_filter.mpr ⟨he, by simp [hne, hu, hv]⟩
            have hc1 := hall [(u, true), (v, true)]
              (List.mem_flatMap.mpr ⟨(u, v), hmem, by simp⟩)
            have hc2 := hall [(u, false), (v, false)]
              (List.mem_flatMap.mpr ⟨(u, v), hmem, by simp⟩)
            simp only [Clause.eval_eq_true_iff, List.mem_cons, List.not_mem_nil,
              or_false] at hc1 hc2
            cases htu : τ u <;> cases htv : τ v <;> simp [htu, htv] at hc1 hc2 ⊢
          · have hmem : (v, u) ∈ G.edges.filter (fun e =>
                decide (e.1 ≠ e.2) && decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices)) :=
              List.mem_filter.mpr ⟨he, by simp [hne.symm, hu, hv]⟩
            have hc1 := hall [(v, true), (u, true)]
              (List.mem_flatMap.mpr ⟨(v, u), hmem, by simp⟩)
            have hc2 := hall [(v, false), (u, false)]
              (List.mem_flatMap.mpr ⟨(v, u), hmem, by simp⟩)
            simp only [Clause.eval_eq_true_iff, List.mem_cons, List.not_mem_nil,
              or_false] at hc1 hc2
            cases htu : τ u <;> cases htv : τ v <;> simp [htu, htv] at hc1 hc2 ⊢
      exact hred.mem_P TwoSAT.mem_P
    · -- `H` has no edges on a nonempty vertex set: `G ∈ HColoring H` iff `G.induced` has no edges.
      push Not at hedge
      let check : Cslib.Complexity.Graph → Bool := fun G =>
        G.vertices.all fun u => G.vertices.all fun v => !G.adjBool u v
      have hpoly : ComputableInPolyTime check encGraph encBool := by
        have hV : ComputableInPolyTime (fun G : Cslib.Complexity.Graph => G.vertices)
            encGraph (encList encNat) := by fun_prop
        have hproj : ComputableInPolyTime
            (fun p : (Cslib.Complexity.Graph × ℕ) × ℕ => ((p.1.1, p.1.2), p.2))
            (encPair (encPair encGraph encNat) encNat)
            (encPair (encPair encGraph encNat) encNat) := by fun_prop
        exact allWithInput hV (allWithInput (hV.comp (fst _ _))
          (bool_not.comp (Graph.computableInPolyTime_adjBool.comp hproj)))
      refine ⟨check, hpoly, fun G => ?_⟩
      rw [mem_HColoring_iff_of_nonempty]
      simp only [check, List.all_eq_true, Bool.not_eq_true', Graph.adjBool_eq_false_iff]
      constructor
      · rintro ⟨f, hf⟩ u hu v hv huv
        exact hedge (f u) (f v) (hf u hu v hv huv)
      · intro hno
        obtain ⟨v0⟩ := ‹Nonempty V›
        exact ⟨fun _ => v0, fun u hu v hv huv => (hno u hu v hv huv).elim⟩

/-- For every finite vertex set `V` with `|V| ≥ 3`, `$K_V$-Coloring` is `NP`-complete. -/
theorem HColoring.npComplete_top {V : Type*} [Fintype V] (hcard : 3 ≤ Fintype.card V) :
    NPComplete encGraph (HColoring (⊤ : _root_.SimpleGraph V)) := by
  have hEq : HColoring (⊤ : _root_.SimpleGraph V) = KColoring (Fintype.card V) := by
    ext G
    rw [← hColoring_top_eq_kColoring]
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    constructor
    · rintro ⟨φ⟩
      exact ⟨⟨fun u => e (φ u), fun {u v} huv => e.injective.ne (φ.map_rel huv)⟩⟩
    · rintro ⟨φ⟩
      exact ⟨⟨fun u => e.symm (φ u), fun {u v} huv => e.symm.injective.ne (φ.map_rel huv)⟩⟩
  rw [hEq]
  exact KColoring_npComplete hcard

/-! ### Polynomial-time equivalence between `CSP(E_H)` and `$H$-Coloring` -/

/-- A fixed complete graph on `m` vertices (`0, ..., m - 1`). -/
private def completeGraphList (m : ℕ) : Cslib.Complexity.Graph :=
  let V := List.range m
  ⟨V, V.flatMap fun u => (V.filter fun v => decide (u ≠ v)).map fun v => (u, v)⟩

/-- `completeGraphList (Fintype.card V + 1)` is never `H`-colorable for any finite simple graph `H`.
-/
private theorem completeGraphList_not_mem_HColoring {V : Type*} [Fintype V]
    (H : _root_.SimpleGraph V) : completeGraphList (Fintype.card V + 1) ∉ HColoring H := by
  rintro ⟨φ⟩
  have hinj : Function.Injective (fun i : Fin (Fintype.card V + 1) =>
      φ ⟨i.val, by simp [completeGraphList, i.isLt]⟩) := by
    intro i j hij
    by_contra hne
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hadj : (completeGraphList (Fintype.card V + 1)).induced.Adj
        ⟨i.val, by simp [completeGraphList, i.isLt]⟩
        ⟨j.val, by simp [completeGraphList, j.isLt]⟩ := by
      simp only [Graph.induced_adj, Graph.toSimpleGraph_adj]
      refine ⟨hval, Or.inl ?_⟩
      simp only [completeGraphList, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
      exact ⟨i.val, i.isLt, j.val, ⟨j.isLt, hval⟩, rfl, rfl⟩
    have hEq : φ ⟨i.val, by simp [completeGraphList, i.isLt]⟩ =
        φ ⟨j.val, by simp [completeGraphList, j.isLt]⟩ := hij
    have hadj' := φ.map_rel hadj
    rw [hEq] at hadj'
    exact H.loopless.irrefl _ hadj'
  have hle := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hle
  omega

/-- Polynomial-time reduction from `CSP(E_H)` to `$H$-Coloring` (for nonempty `V`). -/
theorem CSPRel.polyTimeReducible_edgeRel_hColoring {V : Type*} [Finite V] [Nonempty V]
    (H : _root_.SimpleGraph V) :
    PolyTimeReducible (encCSPInstance 2) encGraph (CSPRel (edgeRel H)) (HColoring H) := by
  have : Fintype V := Fintype.ofFinite V
  classical
  let rejectG := completeGraphList (Fintype.card V + 1)
  let f : CSPInstance 2 → Cslib.Complexity.Graph := fun I =>
    let raw := I.toRaw
    if raw.any (fun l => decide (l.getD 0 0 = l.getD 1 0)) then rejectG
    else ⟨raw.flatten, raw.map fun l => (l.getD 0 0, l.getD 1 0)⟩
  have hf_poly : ComputableInPolyTime f (encCSPInstance 2) encGraph := by
    have hraw := computableInPolyTime_toRaw 2
    have hloop : ComputableInPolyTime
        (fun I : CSPInstance 2 => I.toRaw.any fun l => decide (l.getD 0 0 = l.getD 1 0))
        (encCSPInstance 2) encBool :=
      anyWithInput hraw (by fun_prop)
    have hok : ComputableInPolyTime
        (fun I : CSPInstance 2 =>
          (⟨I.toRaw.flatten, I.toRaw.map fun l => (l.getD 0 0, l.getD 1 0)⟩ :
            Cslib.Complexity.Graph))
        (encCSPInstance 2) encGraph := by
      have h1 : ComputableInPolyTime (fun I : CSPInstance 2 => I.toRaw.flatten)
          (encCSPInstance 2) (encList encNat) := (flatten (enc := encNat)).comp hraw
      have h2 : ComputableInPolyTime
          (fun I : CSPInstance 2 => I.toRaw.map fun l => (l.getD 0 0, l.getD 1 0))
          (encCSPInstance 2) (encList (encPair encNat encNat)) :=
        mapWithInput hraw (by fun_prop)
      exact encGraph_mk_polyTime h1 h2
    exact hloop.ite (const rejectG) hok
  refine ⟨f, hf_poly, fun I => ?_⟩
  have hloop_iff : (I.toRaw.any fun l => decide (l.getD 0 0 = l.getD 1 0)) = true ↔
      ∃ t ∈ I, t 0 = t 1 := by
    simp only [CSPInstance.toRaw, List.any_eq_true, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨l, ⟨t, ht, rfl⟩, hEq⟩
      exact ⟨t, ht, by simpa using hEq⟩
    · rintro ⟨t, ht, hEq⟩
      exact ⟨List.ofFn t, ⟨t, ht, rfl⟩, by simpa using hEq⟩
  dsimp only [f]
  split_ifs with hloop
  · have ⟨t, ht, htEq⟩ := hloop_iff.mp hloop
    refine ⟨fun ⟨σ, hσ⟩ => ?_, fun h => (completeGraphList_not_mem_HColoring H h).elim⟩
    have hadj : H.Adj (σ (t 0)) (σ (t 1)) := hσ t ht
    rw [htEq] at hadj
    exact (H.loopless.irrefl _ hadj).elim
  · have hno : ∀ t ∈ I, t 0 ≠ t 1 := fun t ht heq => hloop (hloop_iff.mpr ⟨t, ht, heq⟩)
    rw [mem_HColoring_iff_of_nonempty]
    constructor
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, fun u _ v _ huv => ?_⟩
      rw [Graph.toSimpleGraph_adj] at huv
      rcases huv with ⟨hne, h1 | h2⟩
      · rcases List.mem_map.mp h1 with ⟨l, hl, hEq⟩
        rcases List.mem_map.mp hl with ⟨t, ht, rfl⟩
        have h0 : t 0 = u := by simpa using congrArg Prod.fst hEq
        have h1' : t 1 = v := by simpa using congrArg Prod.snd hEq
        rw [← h0, ← h1']
        exact hσ t ht
      · rcases List.mem_map.mp h2 with ⟨l, hl, hEq⟩
        rcases List.mem_map.mp hl with ⟨t, ht, rfl⟩
        have h0 : t 0 = v := by simpa using congrArg Prod.fst hEq
        have h1' : t 1 = u := by simpa using congrArg Prod.snd hEq
        rw [← h0, ← h1']
        exact (hσ t ht).symm
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, fun t ht => ?_⟩
      have hm0 : t 0 ∈ I.toRaw.flatten :=
        List.mem_flatten.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
          List.mem_ofFn.mpr ⟨0, rfl⟩⟩
      have hm1 : t 1 ∈ I.toRaw.flatten :=
        List.mem_flatten.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
          List.mem_ofFn.mpr ⟨1, rfl⟩⟩
      have hedge : (t 0, t 1) ∈ I.toRaw.map (fun l => (l.getD 0 0, l.getD 1 0)) :=
        List.mem_map.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩, by simp⟩
      exact hσ (t 0) hm0 (t 1) hm1 (Graph.toSimpleGraph_adj.mpr ⟨hno t ht, Or.inl hedge⟩)

/-- Polynomial-time reduction from `$H$-Coloring` to `CSP(E_H)` (for nonempty `V`). -/
theorem HColoring.polyTimeReducible_cspRel_edgeRel {V : Type*} [Nonempty V]
    (H : _root_.SimpleGraph V) :
    PolyTimeReducible encGraph (encCSPInstance 2) (HColoring H) (CSPRel (edgeRel H)) := by
  classical
  let gRaw : Cslib.Complexity.Graph → List (List ℕ) := fun G =>
    (G.edges.filter fun e =>
      decide (e.1 ≠ e.2) && decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices)).map
      fun e => [e.1, e.2]
  have hgRaw_poly : ComputableInPolyTime gRaw encGraph (encList (encList encNat)) := by
    unfold gRaw
    fun_prop
  have hgRaw_len : ∀ G, ∀ l ∈ gRaw G, l.length = 2 := by
    intro G l hl
    simp only [gRaw, List.mem_map] at hl
    rcases hl with ⟨e, _, rfl⟩
    rfl
  refine ⟨fun G => CSPInstance.ofRaw 2 (gRaw G),
    computableInPolyTime_ofRaw_comp 2 hgRaw_poly hgRaw_len, fun G => ?_⟩
  rw [mem_HColoring_iff_of_nonempty]
  simp only [CSPRel, Set.mem_ofPred_eq, CSPInstance.ofRaw, gRaw, List.map_map, List.mem_map,
    List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, mem_edgeRel_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    rintro t ⟨e, ⟨he, ⟨hne, hu⟩, hv⟩, rfl⟩
    exact hσ e.1 hu e.2 hv (Graph.toSimpleGraph_adj.mpr ⟨hne, Or.inl he⟩)
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, fun u hu v hv huv => ?_⟩
    rw [Graph.toSimpleGraph_adj] at huv
    rcases huv with ⟨hne, h1 | h2⟩
    · exact hσ _ ⟨(u, v), ⟨h1, ⟨hne, hu⟩, hv⟩, rfl⟩
    · exact (hσ _ ⟨(v, u), ⟨h2, ⟨hne.symm, hv⟩, hu⟩, rfl⟩).symm

end Cslib.Complexity
