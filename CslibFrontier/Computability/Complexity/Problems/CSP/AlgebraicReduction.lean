/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Problems.CSP.FiniteDomain

import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.FineGrained.ExhaustiveSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Algebraic CSP Reductions and Fine-Grained Complexity Transfer

This module builds on `CslibFrontier.Computability.Complexity.Problems.CSP.FiniteDomain` to
establish the algebraic complexity reductions for finite-domain single-relation constraint
satisfaction problems `CSP(R)`:

1. **Jeavons' polynomial-time reduction theorem**: pp-definability (or $\mathrm{Pol}(R)
   \subseteq \mathrm{Pol}(R')$ under the sharp nonemptiness / constant-tuple-free guard) yields a
   polynomial-time many-one reduction from `CSP(R')` to `CSP(R)`.
2. **Exhaustive-search exponential-time upper bound**: every finite-domain `CSP(R)` is decidable in
   exponential time `O*(2^(|D| * numVars))` via a polynomial-time reduction to `SAT`.
3. **Jonsson–Lagerkvist–Nordh–Zanuttini fine-grained transfer theorem**: qfpp-definability
   (or $\mathrm{pPol}(R) \subseteq \mathrm{pPol}(R')$ unconditionally for all $R, R'$) yields
   variable-non-increasing polynomial-time reductions and hence ${\sf T}(R') \le {\sf T}(R)$.

## Main definitions

* `Cslib.Complexity.cspRateExponent`, `Cslib.Complexity.cspTimeBase`: the fine-grained
  exponential rate exponent and base ${\sf T}(R)$ of `CSP(R)`.

## Main results

* `Cslib.Complexity.CSPRel.polyTimeReducible_of_isPPDefinable`,
  `Cslib.Complexity.CSPRel.polyTimeReducible_of_polSubset`: Jeavons' reduction theorem.
* `Cslib.Complexity.CSPRel.exists_varNonincreasing_reduction_of_isQFPPDefinable`,
  `Cslib.Complexity.CSPRel.decidableInExpTime_of_isQFPPDefinable`,
  `Cslib.Complexity.CSPRel.decidableInExpTime_of_fintype`: variable-non-increasing qfpp
  reductions and exhaustive-search exponential upper bounds.
* `Cslib.Complexity.CSPRel.cspRateExponent_le_of_ppolSubset`,
  `Cslib.Complexity.CSPRel.cspTimeBase_le_of_ppolSubset`: Jonsson et al.'s fine-grained
  complexity transfer theorem.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic Cslib.Logic.SimpleGraph Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Polynomial-time equality-constraint elimination (shared engine) -/

section EqCollapse

/-- Undirected adjacency test for a list of equality pairs. -/
private def eqAdj (E : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  E.any fun e => (decide (e.1 = u) && decide (e.2 = v)) || (decide (e.1 = v) && decide (e.2 = u))

/-- One breadth-first step over `V` along undirected equality edges `E`. -/
private def eqStepReach (V : List ℕ) (E : List (ℕ × ℕ)) (s : List ℕ) : List ℕ :=
  V.filter fun v => s.contains v || s.any fun u => eqAdj E u v

/-- `n` iterations of `eqStepReach` starting from `V.filter (· == v₀)`. -/
private def eqReachFrom (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) (n : ℕ) : List ℕ :=
  (eqStepReach V E)^[n] (V.filter fun u => decide (u = v₀))

/-- Fixed-point connected component of `v₀` in `(V, E)`. -/
private def eqReach (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) : List ℕ :=
  eqReachFrom V E v₀ (V.length + 1)

/-- Canonical representative of `v₀` in its equality component (first element of `eqReach`,
falling back to `v₀`). -/
private def eqRep (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) : ℕ :=
  (eqReach V E v₀).headD v₀

/-- Undirected one-step equality relation restricted to `V`. -/
private def EqEdge (V : List ℕ) (E : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  u ∈ V ∧ v ∈ V ∧ ((u, v) ∈ E ∨ (v, u) ∈ E)

private theorem eqAdj_eq_true_iff (E : List (ℕ × ℕ)) (u v : ℕ) :
    eqAdj E u v = true ↔ (u, v) ∈ E ∨ (v, u) ∈ E := by
  simp only [eqAdj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b⟩, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl hab
    · exact Or.inr hab
  · rintro (h | h)
    · exact ⟨(u, v), h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(v, u), h, Or.inr ⟨rfl, rfl⟩⟩

private theorem mem_eqStepReach (V : List ℕ) (E : List (ℕ × ℕ)) (s : List ℕ) (v : ℕ) :
    v ∈ eqStepReach V E s ↔ v ∈ V ∧ (v ∈ s ∨ ∃ u ∈ s, (u, v) ∈ E ∨ (v, u) ∈ E) := by
  simp only [eqStepReach, List.mem_filter, Bool.or_eq_true, List.contains_iff_mem,
    List.any_eq_true, eqAdj_eq_true_iff]

private theorem eqReachFrom_sublist (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) (n : ℕ) :
    List.Sublist (eqReachFrom V E v₀ n) V := by
  cases n <;> simp only [eqReachFrom, Function.iterate_zero_apply, Function.iterate_succ_apply'] <;>
    exact List.filter_sublist

private theorem eqReachFrom_subset_succ (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) (n : ℕ) :
    eqReachFrom V E v₀ n ⊆ eqReachFrom V E v₀ (n + 1) := by
  intro m hm
  rw [eqReachFrom, Function.iterate_succ_apply']
  exact (mem_eqStepReach V E _ m).mpr ⟨(eqReachFrom_sublist V E v₀ n).subset hm, Or.inl hm⟩

private theorem eqStepReach_congr (V : List ℕ) (E : List (ℕ × ℕ)) {s t : List ℕ}
    (h : ∀ m, m ∈ s ↔ m ∈ t) : eqStepReach V E s = eqStepReach V E t := by
  simp only [eqStepReach]
  refine List.filter_congr fun _ _ => Bool.eq_iff_iff.mpr ?_
  simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, h]

private theorem eqReachFrom_fixed (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) :
    eqStepReach V E (eqReach V E v₀) = eqReach V E v₀ := by
  let s (n : ℕ) := (eqReachFrom V E v₀ n).toFinset
  have hincl (n : ℕ) : s n ⊆ s (n + 1) := fun m hm =>
    List.mem_toFinset.mpr (eqReachFrom_subset_succ V E v₀ n (List.mem_toFinset.mp hm))
  have hmono : Monotone fun n => (s n).card :=
    monotone_nat_of_le_succ fun n => Finset.card_le_card (hincl n)
  have hbound (n : ℕ) : (s n).card ≤ V.length := by
    have hsub : s n ⊆ V.toFinset := fun m hm =>
      List.mem_toFinset.mpr ((eqReachFrom_sublist V E v₀ n).subset (List.mem_toFinset.mp hm))
    exact (Finset.card_le_card hsub).trans (List.toFinset_card_le V)
  have heq (n : ℕ) (h : (s n).card = (s (n + 1)).card) : s n = s (n + 1) :=
    Finset.eq_of_subset_of_card_le (hincl n) h.ge
  have hnext (n : ℕ) (h : (s n).card = (s (n + 1)).card) :
      eqReachFrom V E v₀ (n + 1) = eqReachFrom V E v₀ (n + 2) := by
    have hm (m : ℕ) : m ∈ eqReachFrom V E v₀ n ↔ m ∈ eqReachFrom V E v₀ (n + 1) := by
      simpa only [s, List.mem_toFinset] using Finset.ext_iff.mp (heq n h) m
    simpa only [eqReachFrom, Function.iterate_succ_apply'] using eqStepReach_congr V E hm
  have hstab (n : ℕ) (h : (s n).card = (s (n + 1)).card) :
      (s (n + 1)).card = (s (n + 2)).card := by
    simp only [s, hnext n h]
  have hc := Nat.stabilises_of_monotone hmono hbound hstab (n := V.length + 1) (by omega)
  simpa only [eqReach, eqReachFrom, Function.iterate_succ_apply'] using
    (hnext V.length hc.symm).symm

private theorem eqReachFrom_sound (V : List ℕ) (E : List (ℕ × ℕ)) (v₀ : ℕ) :
    ∀ (n : ℕ) {m : ℕ}, m ∈ eqReachFrom V E v₀ n →
      m ∈ V ∧ Relation.ReflTransGen (EqEdge V E) v₀ m
  | 0, m, hm => by
    simp only [eqReachFrom, Function.iterate_zero_apply, List.mem_filter, decide_eq_true_eq] at hm
    rcases hm with ⟨hmV, rfl⟩
    exact ⟨hmV, .refl⟩
  | n + 1, m, hm => by
    rw [eqReachFrom, Function.iterate_succ_apply'] at hm
    obtain ⟨hmV, hm | ⟨u, hu, huv⟩⟩ := (mem_eqStepReach V E _ m).mp hm
    · exact eqReachFrom_sound V E v₀ n hm
    · have hrec := eqReachFrom_sound V E v₀ n hu
      exact ⟨hmV, hrec.2.tail ⟨hrec.1, hmV, huv⟩⟩

private theorem mem_eqReach_iff {V : List ℕ} {E : List (ℕ × ℕ)} {v₀ : ℕ} (hv₀ : v₀ ∈ V) (m : ℕ) :
    m ∈ eqReach V E v₀ ↔ Relation.ReflTransGen (EqEdge V E) v₀ m := by
  refine ⟨fun hm => (eqReachFrom_sound V E v₀ _ hm).2, fun h => ?_⟩
  induction h with
  | refl =>
    rw [eqReach]
    induction V.length + 1 with
    | zero => simp [eqReachFrom, hv₀]
    | succ k ih => exact eqReachFrom_subset_succ V E v₀ k ih
  | tail _ hbc ih =>
    have hstep : _ ∈ eqStepReach V E (eqReach V E v₀) :=
      (mem_eqStepReach V E _ _).mpr ⟨hbc.2.1, Or.inr ⟨_, ih, hbc.2.2⟩⟩
    rwa [eqReachFrom_fixed] at hstep

private theorem eqEdge_symm {V : List ℕ} {E : List (ℕ × ℕ)} {u v : ℕ} (h : EqEdge V E u v) :
    EqEdge V E v u :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

private theorem eqReach_eq_of_mem_edges {V : List ℕ} {E : List (ℕ × ℕ)} {u v : ℕ}
    (hu : u ∈ V) (hv : v ∈ V) (huv : (u, v) ∈ E) : eqReach V E u = eqReach V E v := by
  have he : EqEdge V E u v := ⟨hu, hv, Or.inl huv⟩
  have hmem : ∀ w, w ∈ eqReach V E u ↔ w ∈ eqReach V E v := by
    intro w
    rw [mem_eqReach_iff hu, mem_eqReach_iff hv]
    exact ⟨fun h => (Relation.ReflTransGen.single (eqEdge_symm he)).trans h,
      fun h => (Relation.ReflTransGen.single he).trans h⟩
  rw [← eqReachFrom_fixed V E u, ← eqReachFrom_fixed V E v]
  exact eqStepReach_congr V E hmem

private theorem eqRep_eq_of_mem_edges {V : List ℕ} {E : List (ℕ × ℕ)} {u v : ℕ}
    (hu : u ∈ V) (hv : v ∈ V) (huv : (u, v) ∈ E) : eqRep V E u = eqRep V E v := by
  have hEq := eqReach_eq_of_mem_edges hu hv huv
  have hne : eqReach V E u ≠ [] := by
    intro hnil
    have hm : u ∈ eqReach V E u := (mem_eqReach_iff hu u).mpr .refl
    simp [hnil] at hm
  cases hL : eqReach V E u with
  | nil => exact (hne hL).elim
  | cons a as =>
    dsimp [eqRep]
    rw [← hEq, hL]
    rfl

private theorem eqRep_mem_and_reach {V : List ℕ} {E : List (ℕ × ℕ)} {v : ℕ} (hv : v ∈ V) :
    eqRep V E v ∈ V ∧ Relation.ReflTransGen (EqEdge V E) v (eqRep V E v) := by
  have hmem : eqRep V E v ∈ eqReach V E v := by
    have hv_in : v ∈ eqReach V E v := (mem_eqReach_iff hv v).mpr .refl
    cases hL : eqReach V E v with
    | nil => simp [hL] at hv_in
    | cons a as => simp [eqRep, hL]
  exact ⟨(eqReachFrom_sublist V E v _).subset hmem, (mem_eqReach_iff hv _).mp hmem⟩

private theorem eq_of_eqReach_of_assign {D : Type*} {V : List ℕ} {E : List (ℕ × ℕ)} {σ : ℕ → D}
    (hσ : ∀ e ∈ E, e.1 ∈ V → e.2 ∈ V → σ e.1 = σ e.2) {u v : ℕ}
    (h : Relation.ReflTransGen (EqEdge V E) u v) : σ u = σ v := by
  induction h with
  | refl => rfl
  | tail _ hab ih =>
    rcases hab with ⟨ha, hb, h1 | h2⟩
    · exact ih.trans (hσ _ h1 ha hb)
    · exact ih.trans (hσ _ h2 hb ha).symm

@[fun_prop]
private theorem computableInPolyTime_eqAdj {α : Type} {encIn : α ↪ List Bool}
    {E : α → List (ℕ × ℕ)} {u v : α → ℕ}
    (hE : ComputableInPolyTime E encIn (encList (encPair encNat encNat)))
    (hu : ComputableInPolyTime u encIn encNat)
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun a => eqAdj (E a) (u a) (v a)) encIn encBool := by
  have h1 : ComputableInPolyTime (fun p : (List (ℕ × ℕ) × ℕ) × ℕ => eqAdj p.1.1 p.1.2 p.2)
      (encPair (encPair (encList (encPair encNat encNat)) encNat) encNat) encBool := by
    unfold eqAdj
    fun_prop
  exact h1.comp ((hE.prod hu).prod hv)

private def eqStepReachPair (ve : List ℕ × List (ℕ × ℕ)) (s : List ℕ) : List ℕ :=
  eqStepReach ve.1 ve.2 s

@[fun_prop]
private theorem computableInPolyTime_eqStepReach :
    ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × List ℕ => eqStepReachPair p.1 p.2)
      (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) (encList encNat))
      (encList encNat) := by
  simp only [eqStepReachPair, eqStepReach, List.contains_eq_mem]
  fun_prop

private theorem computableInPolyTime_eqReach :
    ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × ℕ => eqReach p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat)
      (encList encNat) := by
  have hcount : ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × ℕ => p.1.1.length + 1)
      (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat) encUnary := by
    fun_prop
  have hinit : ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × ℕ => p.1.1.filter fun u => decide (u = p.2))
      (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat)
      (encList encNat) := by
    fun_prop
  have hV : ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × ℕ => p.1.1)
      (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat)
      (encList encNat) := by fun_prop
  have hiter := ComputableInPolyTime.iterateWith
    (step := eqStepReachPair)
    (.fst (encPair (encList encNat) (encList (encPair encNat encNat))) encNat)
    hcount hinit computableInPolyTime_eqStepReach hV.polyBounded_length
    (fun p i _ => length_encList_sublist encNat (eqReachFrom_sublist p.1.1 p.1.2 p.2 i))
  exact hiter

private theorem computableInPolyTime_eqRep :
    ComputableInPolyTime
      (fun p : (List ℕ × List (ℕ × ℕ)) × ℕ => eqRep p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat) encNat := by
  unfold eqRep
  exact listHeadDWithInput computableInPolyTime_eqReach (snd _ _)

end EqCollapse

/-! ### Jeavons and Jonsson et al. -/

/-- **Jeavons' Polynomial-Time Reduction Theorem**: if `R'` is pp-definable from `R`, then
`CSP(R')` reduces in polynomial time to `CSP(R)`.
-/
theorem CSPRel.polyTimeReducible_of_isPPDefinable {D : Type*} {n n' : ℕ}
    {R : Set (Fin n → D)} {R' : Set (Fin n' → D)} (hdef : IsPPDefinable R R') :
    PolyTimeReducible (encCSPInstance n') (encCSPInstance n) (CSPRel R') (CSPRel R) := by
  classical
  rcases hdef with ⟨q, atoms, eqs, hspec⟩
  let q' : ℕ := max q 1
  have hq'_pos : 0 < q' := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right q 1)
  let encPort (idx : ℕ) (scope : List ℕ) (u : Fin (n' + q)) : ℕ :=
    if h : u.val < n' then 2 * scope.getD u.val 0
    else 2 * (q' * idx + (u.val - n')) + 1
  let extVars (raw : List (List ℕ)) : List ℕ :=
    raw.flatten.map (fun v => 2 * v) ++
      (List.range raw.length).flatMap fun idx =>
        (List.range q).map fun j => 2 * (q' * idx + j) + 1
  let extEqs (raw : List (List ℕ)) : List (ℕ × ℕ) :=
    raw.zipIdx.flatMap fun p =>
      eqs.map fun eqp => (encPort p.2 p.1 eqp.1, encPort p.2 p.1 eqp.2)
  let extAtoms (raw : List (List ℕ)) : List (List ℕ) :=
    raw.zipIdx.flatMap fun p =>
      atoms.map fun α => List.ofFn fun i : Fin n => encPort p.2 p.1 (α i)
  let gRaw (I : CSPInstance n') : List (List ℕ) :=
    let raw := I.toRaw
    let V := extVars raw
    let E := extEqs raw
    (extAtoms raw).map fun l => l.map (eqRep V E)
  have hlen : ∀ I : CSPInstance n', ∀ l ∈ gRaw I, l.length = n := by
    intro I l hl
    simp only [gRaw, extAtoms, List.mem_map, List.mem_flatMap] at hl
    rcases hl with ⟨l0, ⟨_, _, ⟨α, _, rfl⟩⟩, rfl⟩
    simp
  have hpoly_gRaw : ComputableInPolyTime gRaw (encCSPInstance n') (encList (encList encNat)) := by
    have hraw := computableInPolyTime_toRaw n'
    have hencPort : ∀ u : Fin (n' + q),
        ComputableInPolyTime
          (fun p : List ℕ × ℕ => encPort p.2 p.1 u)
          (encPair (encList encNat) encUnary) encNat := by
      intro u
      dsimp only [encPort]
      split_ifs with hu
      · have hget : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.getD u.val 0)
            (encPair (encList encNat) encUnary) encNat := by
          have : ComputableInPolyTime (fun _ : List ℕ × ℕ => u.val)
              (encPair (encList encNat) encUnary) encUnary := const u.val
          fun_prop
        exact binary_mul' (const 2) hget
      · have hidx : ComputableInPolyTime (fun p : List ℕ × ℕ => q' * p.2 + (u.val - n'))
            (encPair (encList encNat) encUnary) encUnary := by fun_prop
        have hbin : ComputableInPolyTime
            (fun p : List ℕ × ℕ => 2 * (q' * p.2 + (u.val - n')) + 1)
            (encPair (encList encNat) encUnary) encUnary := by fun_prop
        exact unary_to_binary.comp hbin
    have hV : ComputableInPolyTime (fun I : CSPInstance n' => extVars I.toRaw)
        (encCSPInstance n') (encList encNat) := by
      have h1 : ComputableInPolyTime
          (fun I : CSPInstance n' => I.toRaw.flatten.map (fun v => 2 * v))
          (encCSPInstance n') (encList encNat) := by
        have hfl : ComputableInPolyTime (fun I : CSPInstance n' => I.toRaw.flatten)
            (encCSPInstance n') (encList encNat) := (flatten (enc := encNat)).comp hraw
        have hmul2 : ComputableInPolyTime (fun v : ℕ => 2 * v) encNat encNat :=
          binary_mul' (const 2) id'
        exact mapWithInput hfl (hmul2.comp (snd _ _))
      have h2 : ComputableInPolyTime
          (fun I : CSPInstance n' =>
            (List.range I.toRaw.length).flatMap fun idx =>
              (List.range q).map fun j => 2 * (q' * idx + j) + 1)
          (encCSPInstance n') (encList encNat) := by
        have hrange : ComputableInPolyTime (fun I : CSPInstance n' => List.range I.toRaw.length)
            (encCSPInstance n') (encList encUnary) := by
          have hlen_r : ComputableInPolyTime (fun I : CSPInstance n' => I.toRaw.length)
              (encCSPInstance n') encUnary := (length_list (encList encNat)).comp hraw
          exact range.comp hlen_r
        have hinner : ComputableInPolyTime
            (fun p : CSPInstance n' × ℕ =>
              (List.range q).map fun j => 2 * (q' * p.2 + j) + 1)
            (encPair (encCSPInstance n') encUnary) (encList encNat) := by
          refine mapConst (List.range q) fun j _ => ?_
          exact unary_to_binary.comp (by fun_prop)
        exact flatMapWithInput hrange hinner
      exact listAppend' h1 h2
    have hE : ComputableInPolyTime (fun I : CSPInstance n' => extEqs I.toRaw)
        (encCSPInstance n') (encList (encPair encNat encNat)) := by
      have hzip : ComputableInPolyTime (fun I : CSPInstance n' => I.toRaw.zipIdx)
          (encCSPInstance n') (encList (encPair (encList encNat) encUnary)) :=
        (ComputableInPolyTime.zipIdx _).comp hraw
      refine flatMapWithInput hzip ?_
      refine mapConst eqs fun eqp _ => ?_
      exact ((hencPort eqp.1).comp (snd _ _)).prod ((hencPort eqp.2).comp (snd _ _))
    have hA : ComputableInPolyTime (fun I : CSPInstance n' => extAtoms I.toRaw)
        (encCSPInstance n') (encList (encList encNat)) := by
      have hzip : ComputableInPolyTime (fun I : CSPInstance n' => I.toRaw.zipIdx)
          (encCSPInstance n') (encList (encPair (encList encNat) encUnary)) :=
        (ComputableInPolyTime.zipIdx _).comp hraw
      refine flatMapWithInput hzip ?_
      refine mapConst atoms fun α _ => ?_
      -- `List.ofFn (fun i : Fin n => encPort p.2 p.1 (α i))` equals mapping over `List.finRange n`!
      have hEqFn : (fun p : CSPInstance n' × (List ℕ × ℕ) =>
          List.ofFn fun i : Fin n => encPort p.2.2 p.2.1 (α i)) =
          (fun p : CSPInstance n' × (List ℕ × ℕ) =>
            (List.finRange n).map fun i => encPort p.2.2 p.2.1 (α i)) := by
        funext p
        exact List.ofFn_eq_map
      rw [hEqFn]
      exact mapConst (List.finRange n) fun i _ => (hencPort (α i)).comp (snd _ _)
    have hrep_comp : ComputableInPolyTime
        (fun q : (CSPInstance n' × List ℕ) × ℕ =>
          eqRep (extVars q.1.1.toRaw) (extEqs q.1.1.toRaw) q.2)
        (encPair (encPair (encCSPInstance n') (encList encNat)) encNat) encNat :=
      computableInPolyTime_eqRep.comp
        (g := fun q : (CSPInstance n' × List ℕ) × ℕ =>
          ((extVars q.1.1.toRaw, extEqs q.1.1.toRaw), q.2))
        (((hV.comp (fst _ _)).prod (hE.comp (fst _ _))).comp (fst _ _) |>.prod (snd _ _))
    exact mapWithInput hA (mapWithInput (snd _ _) hrep_comp)
  refine ⟨fun I => CSPInstance.ofRaw n (gRaw I),
    computableInPolyTime_ofRaw_comp n hpoly_gRaw hlen, fun I => ?_⟩
  -- Correctness: `I ∈ CSPRel R' ↔ CSPInstance.ofRaw n (gRaw I) ∈ CSPRel R`.
  have hmem_extVars : ∀ (i : ℕ) (hi : i < I.length) (u : Fin (n' + q)),
      encPort i (List.ofFn I[i]) u ∈ extVars I.toRaw := by
    intro i hi u
    simp only [extVars, CSPInstance.toRaw, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_range, List.length_map]
    by_cases hu : u.val < n'
    · left
      refine ⟨I[i] ⟨u.val, hu⟩, ?_, ?_⟩
      · exact List.mem_flatten.mpr ⟨List.ofFn I[i],
          List.mem_map.mpr ⟨I[i], List.getElem_mem hi, rfl⟩,
          List.mem_ofFn.mpr ⟨⟨u.val, hu⟩, rfl⟩⟩
      · simp [encPort, hu]
    · right
      refine ⟨i, hi, u.val - n', by omega, ?_⟩
      simp [encPort, hu]
  have hmem_extEqs : ∀ (i : ℕ) (hi : i < I.length) (eqp : Fin (n' + q) × Fin (n' + q)),
      eqp ∈ eqs →
      (encPort i (List.ofFn I[i]) eqp.1, encPort i (List.ofFn I[i]) eqp.2) ∈ extEqs I.toRaw := by
    intro i hi eqp heqp
    simp only [extEqs, CSPInstance.toRaw, List.mem_flatMap, List.mem_map]
    refine ⟨(List.ofFn I[i], i), ?_, ⟨eqp, heqp, rfl⟩⟩
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hi])
  have hport_free : ∀ (i : ℕ) (hi : i < I.length) (j : Fin n'),
      encPort i (List.ofFn I[i]) (Fin.castAdd q j) = 2 * I[i] j := by
    intro i _ j
    simp [encPort, j.isLt]
  have hport_aux : ∀ (i : ℕ) (hi : i < I.length) (j : Fin q),
      encPort i (List.ofFn I[i]) (Fin.natAdd n' j) = 2 * (q' * i + j.val) + 1 := by
    intro i _ j
    have hnot : ¬ (n' + j.val < n') := by omega
    simp [encPort, hnot]
  constructor
  · rintro ⟨σ, hσ⟩
    have hex : ∀ (i : ℕ) (hi : i < I.length), ∃ e : Fin q → D,
        (∀ α ∈ atoms, Fin.append (σ ∘ I[i]) e ∘ α ∈ R) ∧
        (∀ p ∈ eqs, Fin.append (σ ∘ I[i]) e p.1 = Fin.append (σ ∘ I[i]) e p.2) :=
      fun i hi => (hspec (σ ∘ I[i])).mp (hσ I[i] (List.getElem_mem hi))
    choose e he using hex
    let d0 : D := σ 0
    let τ : ℕ → D := fun v =>
      if v % 2 = 0 then σ (v / 2)
      else
        let idx := (v / 2) / q'
        let j := (v / 2) % q'
        if hi : idx < I.length then
          if hj : j < q then e idx hi ⟨j, hj⟩ else d0
        else d0
    have hτ_port : ∀ (i : ℕ) (hi : i < I.length) (u : Fin (n' + q)),
        τ (encPort i (List.ofFn I[i]) u) = Fin.append (σ ∘ I[i]) (e i hi) u := by
      intro i hi u
      refine Fin.addCases (fun j => ?_) (fun j => ?_) u
      · rw [hport_free i hi j, Fin.append_left]
        simp [τ]
      · rw [hport_aux i hi j, Fin.append_right]
        have hjq' : j.val < q' := lt_of_lt_of_le j.isLt (le_max_left q 1)
        have hhalf : (2 * (q' * i + j.val) + 1) / 2 = q' * i + j.val := by omega
        have hdiv : (q' * i + j.val) / q' = i := by
          rw [Nat.mul_add_div hq'_pos, Nat.div_eq_of_lt hjq', Nat.add_zero]
        have hmod : (q' * i + j.val) % q' = j.val := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hjq']
        simp only [τ, ite_eq_right (by omega : (2 * (q' * i + j.val) + 1) % 2 ≠ 0),
          hhalf, hdiv, hmod, hi, j.isLt, dite_true]
    have hτ_eqs : ∀ p ∈ extEqs I.toRaw, p.1 ∈ extVars I.toRaw → p.2 ∈ extVars I.toRaw →
        τ p.1 = τ p.2 := by
      intro p hp _ _
      simp only [extEqs, CSPInstance.toRaw, List.mem_flatMap, List.mem_map] at hp
      rcases hp with ⟨⟨l, idx⟩, hzip, ⟨eqp, heqp, rfl⟩⟩
      obtain ⟨hidx, hl⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hzip)
      simp only [List.length_map, List.getElem_map] at hidx hl
      rw [← hl, hτ_port idx hidx eqp.1, hτ_port idx hidx eqp.2]
      exact (he idx hidx).2 eqp heqp
    refine ⟨τ, fun t ht => ?_⟩
    rcases List.mem_map.mp ht with ⟨l0, hl0, rfl⟩
    rcases List.mem_map.mp hl0 with ⟨l1, hl1, rfl⟩
    simp only [extAtoms, List.mem_flatMap, List.mem_map] at hl1
    rcases hl1 with ⟨⟨l, idx⟩, hzip, ⟨α, hα, rfl⟩⟩
    obtain ⟨hidx, hl⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hzip)
    simp only [CSPInstance.toRaw, List.length_map, List.getElem_map] at hidx hl
    have hEq : (τ ∘ fun i : Fin n =>
        ((List.ofFn fun k : Fin n => encPort idx l (α k)).map
          (eqRep (extVars I.toRaw) (extEqs I.toRaw))).getD i.val 0) =
        Fin.append (σ ∘ I[idx]) (e idx hidx) ∘ α := by
      funext k
      simp only [Function.comp_apply, List.map_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, ← hl]
      simp only [Function.comp_apply]
      have hreach := (eqRep_mem_and_reach (E := extEqs I.toRaw) (hmem_extVars idx hidx (α k))).2
      rw [← eq_of_eqReach_of_assign hτ_eqs hreach, hτ_port idx hidx (α k)]
    rw [hEq]
    exact (he idx hidx).1 α hα
  · rintro ⟨τ, hτ⟩
    let V := extVars I.toRaw
    let E := extEqs I.toRaw
    refine ⟨fun v => τ (eqRep V E (2 * v)), ?_⟩
    rw [List.forall_mem_iff_getElem]
    intro idx hidx
    rw [hspec]
    refine ⟨fun j => τ (eqRep V E (2 * (q' * idx + j.val) + 1)), ?_, ?_⟩
    · intro α hα
      have hmem_t : (fun k : Fin n =>
          ((List.ofFn fun i : Fin n => encPort idx (List.ofFn I[idx]) (α i)).map
            (eqRep V E)).getD k.val 0) ∈ CSPInstance.ofRaw n (gRaw I) := by
        refine List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
          ⟨(List.ofFn I[idx], idx),
            List.mem_zipIdx_iff_getElem?.mpr (by simp [CSPInstance.toRaw, hidx]),
            List.mem_map.mpr ⟨α, hα, rfl⟩⟩, rfl⟩, rfl⟩
      have hEq : Fin.append ((fun v => τ (eqRep V E (2 * v))) ∘ I[idx])
          (fun j => τ (eqRep V E (2 * (q' * idx + j.val) + 1))) ∘ α =
          τ ∘ (fun k : Fin n =>
            ((List.ofFn fun i : Fin n => encPort idx (List.ofFn I[idx]) (α i)).map
              (eqRep V E)).getD k.val 0) := by
        funext k
        simp only [Function.comp_apply, List.map_ofFn]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        simp only [Function.comp_apply]
        refine Fin.addCases (fun j => ?_) (fun j => ?_) (α k)
        · rw [Fin.append_left, hport_free idx hidx j]; rfl
        · rw [Fin.append_right, hport_aux idx hidx j]
      rw [hEq]
      exact hτ _ hmem_t
    · intro eqp heqp
      have h1 := hmem_extVars idx hidx eqp.1
      have h2 := hmem_extVars idx hidx eqp.2
      have hrep := eqRep_eq_of_mem_edges h1 h2 (hmem_extEqs idx hidx eqp heqp)
      have hval : ∀ u : Fin (n' + q),
          Fin.append ((fun v => τ (eqRep V E (2 * v))) ∘ I[idx])
            (fun j => τ (eqRep V E (2 * (q' * idx + j.val) + 1))) u =
            τ (eqRep V E (encPort idx (List.ofFn I[idx]) u)) := by
        intro u
        refine Fin.addCases (fun j => ?_) (fun j => ?_) u
        · rw [Fin.append_left, hport_free idx hidx j]; rfl
        · rw [Fin.append_right, hport_aux idx hidx j]
      rw [hval, hval, hrep]

/-- **Jeavons via Pöschel's Galois connection**: if `Pol(R) ⊆ Pol(R')` on a finite domain `D`
and either `R'` is nonempty or `R` contains no constant tuple, then `CSP(R')` reduces in
polynomial time to `CSP(R)`.
-/
theorem CSPRel.polyTimeReducible_of_polSubset {D : Type*} [Finite D]
    {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)}
    (hguard : R'.Nonempty ∨ ∀ a : D, (fun _ => a) ∉ R) (hpol : PolSubset R R') :
    PolyTimeReducible (encCSPInstance n') (encCSPInstance n) (CSPRel R') (CSPRel R) :=
  polyTimeReducible_of_isPPDefinable ((poschel_galois_pp hguard).mp hpol)

/-! ### Fine-grained rate exponent, exhaustive search, and Jonsson et al. -/

/-- The fine-grained exponential rate exponent of `CSP(R)`: infimum of `δ ≥ 0` such that `CSP(R)`
is decidable in time `O(2^(δ * numVars) * poly(L))`. -/
@[expose] noncomputable def cspRateExponent {D : Type*} {n : ℕ} (R : Set (Fin n → D)) : ℝ :=
  Cslib.rateExponent (DecidableInExpTime (CSPRel R) (encCSPInstance n) CSPInstance.numVars)

/-- The fine-grained exponential time base $\mathsf{T}(R) = 2^{\mathrm{cspRateExponent}(R)}$ of
`CSP(R)` (matching $\inf \{ c \ge 1 \mid \mathrm{CSP}(R) \text{ solvable in } O^*(c^n) \}$). -/
@[expose] noncomputable def cspTimeBase {D : Type*} {n : ℕ} (R : Set (Fin n → D)) : ℝ :=
  (2 : ℝ) ^ cspRateExponent R

/-- `1 ≤ cspTimeBase R` unconditionally. -/
theorem one_le_cspTimeBase {D : Type*} {n : ℕ} (R : Set (Fin n → D)) :
    1 ≤ cspTimeBase R :=
  Real.one_le_rpow (by norm_num) (Cslib.rateExponent_nonneg _)

/-- **Variable-non-increasing reduction from qfpp-definability**: if `R'` is qfpp-definable from
`R`, then there is a polynomial-time reduction `f` from `CSP(R')` to `CSP(R)` satisfying
`(f I).numVars ≤ I.numVars` for every instance `I`. -/
theorem CSPRel.exists_varNonincreasing_reduction_of_isQFPPDefinable {D : Type*} {n n' : ℕ}
    {R : Set (Fin n → D)} {R' : Set (Fin n' → D)} (hdef : IsQFPPDefinable R R') :
    ∃ f : CSPInstance n' → CSPInstance n,
      ComputableInPolyTime f (encCSPInstance n') (encCSPInstance n) ∧
      (∀ I, I ∈ CSPRel R' ↔ f I ∈ CSPRel R) ∧
      (∀ I, (f I).numVars ≤ I.numVars) := by
  classical
  rcases hdef with ⟨atoms, eqs, hspec⟩
  let qfEqs (raw : List (List ℕ)) : List (ℕ × ℕ) :=
    raw.flatMap fun l => eqs.map fun p => (l.getD p.1.val 0, l.getD p.2.val 0)
  let qfAtoms (raw : List (List ℕ)) : List (List ℕ) :=
    raw.flatMap fun l => atoms.map fun α => List.ofFn fun i : Fin n => l.getD (α i).val 0
  let gRaw (I : CSPInstance n') : List (List ℕ) :=
    let raw := I.toRaw
    let V := raw.flatten
    let E := qfEqs raw
    (qfAtoms raw).map fun l => l.map (eqRep V E)
  have hlen : ∀ I : CSPInstance n', ∀ l ∈ gRaw I, l.length = n := by
    intro I l hl
    simp only [gRaw, qfAtoms, List.mem_map, List.mem_flatMap] at hl
    rcases hl with ⟨l0, ⟨_, _, ⟨α, _, rfl⟩⟩, rfl⟩
    simp
  have hpoly_gRaw : ComputableInPolyTime gRaw (encCSPInstance n') (encList (encList encNat)) := by
    have hraw := computableInPolyTime_toRaw n'
    have hV : ComputableInPolyTime (fun I : CSPInstance n' => I.toRaw.flatten)
        (encCSPInstance n') (encList encNat) := (flatten (enc := encNat)).comp hraw
    have hE : ComputableInPolyTime (fun I : CSPInstance n' => qfEqs I.toRaw)
        (encCSPInstance n') (encList (encPair encNat encNat)) := by
      refine flatMapWithInput hraw ?_
      refine mapConst eqs fun eqp _ => ?_
      have h1 : ComputableInPolyTime (fun p : CSPInstance n' × List ℕ => p.2.getD eqp.1.val 0)
          (encPair (encCSPInstance n') (encList encNat)) encNat := by
        have : ComputableInPolyTime (fun _ : CSPInstance n' × List ℕ => eqp.1.val)
            (encPair (encCSPInstance n') (encList encNat)) encUnary := const eqp.1.val
        fun_prop
      have h2 : ComputableInPolyTime (fun p : CSPInstance n' × List ℕ => p.2.getD eqp.2.val 0)
          (encPair (encCSPInstance n') (encList encNat)) encNat := by
        have : ComputableInPolyTime (fun _ : CSPInstance n' × List ℕ => eqp.2.val)
            (encPair (encCSPInstance n') (encList encNat)) encUnary := const eqp.2.val
        fun_prop
      exact h1.prod h2
    have hA : ComputableInPolyTime (fun I : CSPInstance n' => qfAtoms I.toRaw)
        (encCSPInstance n') (encList (encList encNat)) := by
      refine flatMapWithInput hraw ?_
      refine mapConst atoms fun α _ => ?_
      have hEqFn : (fun p : CSPInstance n' × List ℕ =>
          List.ofFn fun i : Fin n => p.2.getD (α i).val 0) =
          (fun p : CSPInstance n' × List ℕ =>
            (List.finRange n).map fun i => p.2.getD (α i).val 0) := by
        funext p; exact List.ofFn_eq_map
      rw [hEqFn]
      refine mapConst (List.finRange n) fun i _ => ?_
      have : ComputableInPolyTime (fun _ : CSPInstance n' × List ℕ => (α i).val)
          (encPair (encCSPInstance n') (encList encNat)) encUnary := const (α i).val
      fun_prop
    have hrep_comp : ComputableInPolyTime
        (fun q : (CSPInstance n' × List ℕ) × ℕ =>
          eqRep q.1.1.toRaw.flatten (qfEqs q.1.1.toRaw) q.2)
        (encPair (encPair (encCSPInstance n') (encList encNat)) encNat) encNat :=
      computableInPolyTime_eqRep.comp
        (g := fun q : (CSPInstance n' × List ℕ) × ℕ =>
          ((q.1.1.toRaw.flatten, qfEqs q.1.1.toRaw), q.2))
        (((hV.comp (fst _ _)).prod (hE.comp (fst _ _))).comp (fst _ _) |>.prod (snd _ _))
    exact mapWithInput hA (mapWithInput (snd _ _) hrep_comp)
  refine ⟨fun I => CSPInstance.ofRaw n (gRaw I),
    computableInPolyTime_ofRaw_comp n hpoly_gRaw hlen, fun I => ?_, fun I => ?_⟩
  · -- Correctness of the variable-non-increasing qfpp reduction.
    have hV_eq : I.toRaw.flatten = I.vars := by
      rw [CSPInstance.toRaw, CSPInstance.vars, List.flatMap_def]
    let V := I.toRaw.flatten
    let E := qfEqs I.toRaw
    have hmemV : ∀ t ∈ I, ∀ i : Fin n', t i ∈ V := fun t ht i =>
      List.mem_flatten.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
        List.mem_ofFn.mpr ⟨i, rfl⟩⟩
    have hmemE : ∀ t ∈ I, ∀ p ∈ eqs, (t p.1, t p.2) ∈ E := by
      intro t ht p hp
      simp only [E, qfEqs, CSPInstance.toRaw, List.mem_flatMap, List.mem_map]
      exact ⟨List.ofFn t, ⟨t, ht, rfl⟩, ⟨p, hp, by simp⟩⟩
    constructor
    · rintro ⟨σ, hσ⟩
      have hσ_eqs : ∀ p ∈ E, p.1 ∈ V → p.2 ∈ V → σ p.1 = σ p.2 := by
        intro p hp _ _
        simp only [E, qfEqs, CSPInstance.toRaw, List.mem_flatMap, List.mem_map] at hp
        rcases hp with ⟨l, ⟨t, ht, rfl⟩, ⟨eqp, heqp, rfl⟩⟩
        have h1 : (List.ofFn t).getD eqp.1.val 0 = t eqp.1 := by simp
        have h2 : (List.ofFn t).getD eqp.2.val 0 = t eqp.2 := by simp
        rw [h1, h2]
        exact ((hspec (σ ∘ t)).mp (hσ t ht)).2 eqp heqp
      refine ⟨σ, fun u hu => ?_⟩
      rcases List.mem_map.mp hu with ⟨l0, hl0, rfl⟩
      rcases List.mem_map.mp hl0 with ⟨l1, hl1, rfl⟩
      simp only [qfAtoms, CSPInstance.toRaw, List.mem_flatMap, List.mem_map] at hl1
      rcases hl1 with ⟨l, ⟨t, ht, rfl⟩, ⟨α, hα, rfl⟩⟩
      have hEq : (σ ∘ fun i : Fin n =>
          ((List.ofFn fun k : Fin n => (List.ofFn t).getD (α k).val 0).map
            (eqRep V E)).getD i.val 0) = σ ∘ t ∘ α := by
        funext k
        simp only [Function.comp_apply, List.map_ofFn]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        simp only [Function.comp_apply]
        have hg : (List.ofFn t).getD (α k).val 0 = t (α k) := by simp
        rw [hg]
        exact (eq_of_eqReach_of_assign hσ_eqs (eqRep_mem_and_reach (hmemV t ht (α k))).2).symm
      rw [hEq]
      exact ((hspec (σ ∘ t)).mp (hσ t ht)).1 α hα
    · rintro ⟨τ, hτ⟩
      refine ⟨fun v => τ (eqRep V E v), fun t ht => ?_⟩
      rw [hspec]
      constructor
      · intro α hα
        have hmem_u : (fun k : Fin n =>
            ((List.ofFn fun i : Fin n => (List.ofFn t).getD (α i).val 0).map
              (eqRep V E)).getD k.val 0) ∈ CSPInstance.ofRaw n (gRaw I) :=
          List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
            ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
              List.mem_map.mpr ⟨α, hα, rfl⟩⟩, rfl⟩, rfl⟩
        have hEq : ((fun v => τ (eqRep V E v)) ∘ t) ∘ α =
            τ ∘ (fun k : Fin n =>
              ((List.ofFn fun i : Fin n => (List.ofFn t).getD (α i).val 0).map
                (eqRep V E)).getD k.val 0) := by
          funext k
          simp only [Function.comp_apply, List.map_ofFn]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          simp
        rw [hEq]
        exact hτ _ hmem_u
      · intro p hp
        exact congrArg τ (eqRep_eq_of_mem_edges (hmemV t ht p.1) (hmemV t ht p.2) (hmemE t ht p hp))
  · -- Variable count bound: `(f I).numVars ≤ I.numVars`.
    simp only [CSPInstance.numVars]
    refine Finset.card_le_card fun v hv => ?_
    rw [List.mem_toFinset] at hv ⊢
    rcases List.mem_flatMap.mp hv with ⟨u, hu, hvu⟩
    rcases List.mem_map.mp hu with ⟨l0, hl0, rfl⟩
    rcases List.mem_map.mp hl0 with ⟨l1, hl1, rfl⟩
    simp only [qfAtoms, CSPInstance.toRaw, List.mem_flatMap, List.mem_map] at hl1
    rcases hl1 with ⟨l, ⟨t, ht, rfl⟩, ⟨α, _, rfl⟩⟩
    rcases List.mem_ofFn.mp hvu with ⟨k, rfl⟩
    simp only [List.map_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp only [Function.comp_apply]
    have hg : (List.ofFn t).getD (α k).val 0 = t (α k) := by simp
    rw [hg]
    have hmemV : t (α k) ∈ I.toRaw.flatten :=
      List.mem_flatten.mpr ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
        List.mem_ofFn.mpr ⟨α k, rfl⟩⟩
    have hrep := (eqRep_mem_and_reach (E := qfEqs I.toRaw) hmemV).1
    simp only [CSPInstance.toRaw, List.mem_flatten, List.mem_map] at hrep
    rcases hrep with ⟨l', ⟨t', ht', rfl⟩, hmem_l'⟩
    exact List.mem_flatMap.mpr ⟨t', ht', hmem_l'⟩

/-- **Transfer of exponential time bounds under qfpp-definability**: if `R'` is qfpp-definable
from `R`, every exponential time bound `δ ≥ 0` for `CSP(R)` transfers unchanged to `CSP(R')`. -/
theorem CSPRel.decidableInExpTime_of_isQFPPDefinable {D : Type*} {n n' : ℕ}
    {R : Set (Fin n → D)} {R' : Set (Fin n' → D)} (hdef : IsQFPPDefinable R R')
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hR : DecidableInExpTime (CSPRel R) (encCSPInstance n) CSPInstance.numVars δ) :
    DecidableInExpTime (CSPRel R') (encCSPInstance n') CSPInstance.numVars δ := by
  obtain ⟨f, hf, hred, hvars⟩ := exists_varNonincreasing_reduction_of_isQFPPDefinable hdef
  have h1 :=
    hR.of_reduction hf hred (c := 1) (fun I => by simpa using Nat.le_succ_of_le (hvars I)) hδ
  simpa using h1

/-- Exhaustive-search exponential-time decidability of finite-domain `CSP(R)` via `SAT`
(showing `{δ ≥ 0 | DecidableInExpTime (CSPRel R) ... δ}` is always nonempty). -/
theorem CSPRel.decidableInExpTime_of_fintype {D : Type*} [Fintype D] {n : ℕ}
    (R : Set (Fin n → D)) :
    DecidableInExpTime (CSPRel R) (encCSPInstance n) CSPInstance.numVars (Fintype.card D) := by
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
    have h0 : DecidableInExpTime (∅ : Set (CSPInstance n)) (encCSPInstance n)
        CSPInstance.numVars 0 :=
      .of_computableInPolyTime (const false) (fun _ => by simp)
    simpa [k, hk] using h0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let e : D ≃ Fin k := Fintype.equivFinOfCardEq rfl
    -- Reduce `I : CSPInstance n` to a CNF formula on `k * I.numVars` variables!
    let forb : List (List ℕ) :=
      ((Finset.univ : Finset (Fin n → Fin k)).filter fun a =>
        (fun i => e.symm (a i)) ∉ R).toList.map fun a => List.ofFn fun i => (a i).val
    let varIdx (dv : List ℕ) (v : ℕ) (c : ℕ) : ℕ := k * dv.idxOf v + c
    let toSATRaw (raw : List (List ℕ)) : CNF ℕ :=
      let V := raw.flatten
      let dv := selectDistinct V (List.replicate V.length true)
      let atLeast := dv.map fun v => (List.range k).map fun c => (varIdx dv v c, true)
      let atMost := dv.flatMap fun v =>
        (List.range k).flatMap fun c1 =>
          (List.range k).flatMap fun c2 =>
            if c1 < c2 then [[(varIdx dv v c1, false), (varIdx dv v c2, false)]] else []
      let forbid := raw.flatMap fun l =>
        forb.map fun a =>
          (List.finRange n).map fun i => (varIdx dv (l.getD i.val 0) (a.getD i.val 0), false)
      atLeast ++ atMost ++ forbid
    let toSAT (I : CSPInstance n) : CNF ℕ := toSATRaw I.toRaw
    have hpoly : ComputableInPolyTime toSAT (encCSPInstance n) encCNF := by
      have hraw := computableInPolyTime_toRaw n
      have hV : ComputableInPolyTime (fun I : CSPInstance n => I.toRaw.flatten)
          (encCSPInstance n) (encList encNat) := (flatten (enc := encNat)).comp hraw
      have hdv : ComputableInPolyTime
          (fun I : CSPInstance n =>
            selectDistinct I.toRaw.flatten (List.replicate I.toRaw.flatten.length true))
          (encCSPInstance n) (encList encNat) := by
        have hrep : ComputableInPolyTime
            (fun I : CSPInstance n => List.replicate I.toRaw.flatten.length true)
            (encCSPInstance n) encBits := by
          have := bitsReplicate true
          fun_prop
        fun_prop
      have hidx_enc : ComputableInPolyTime
          (fun p : (CSPInstance n × ℕ) × ℕ =>
            varIdx (selectDistinct p.1.1.toRaw.flatten
              (List.replicate p.1.1.toRaw.flatten.length true)) p.1.2 p.2)
          (encPair (encPair (encCSPInstance n) encNat) encUnary) encNat := by
        have h1 : ComputableInPolyTime
            (fun p : (CSPInstance n × ℕ) × ℕ =>
              (selectDistinct p.1.1.toRaw.flatten
                (List.replicate p.1.1.toRaw.flatten.length true)).idxOf p.1.2)
            (encPair (encPair (encCSPInstance n) encNat) encUnary) encUnary :=
          idxOfWithInput (hdv.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _))
        have h2 : ComputableInPolyTime
            (fun p : (CSPInstance n × ℕ) × ℕ =>
              k * (selectDistinct p.1.1.toRaw.flatten
                (List.replicate p.1.1.toRaw.flatten.length true)).idxOf p.1.2 + p.2)
            (encPair (encPair (encCSPInstance n) encNat) encUnary) encUnary := by fun_prop
        exact unary_to_binary.comp h2
      have hAtLeast : ComputableInPolyTime
          (fun I : CSPInstance n =>
            (selectDistinct I.toRaw.flatten (List.replicate I.toRaw.flatten.length true)).map
              fun v => (List.range k).map fun c =>
                let vars := selectDistinct I.toRaw.flatten
                  (List.replicate I.toRaw.flatten.length true)
                (varIdx vars v c, true))
          (encCSPInstance n) encCNF := by
        unfold encCNF
        refine mapWithInput hdv ?_
        refine mapConst (List.range k) fun c _ => ?_
        exact (hidx_enc.comp (id'.prod (const c))).prod (const true)
      have hAtMost : ComputableInPolyTime
          (fun I : CSPInstance n =>
            (selectDistinct I.toRaw.flatten (List.replicate I.toRaw.flatten.length true)).flatMap
              fun v => (List.range k).flatMap fun c1 => (List.range k).flatMap fun c2 =>
                if c1 < c2 then
                  [[(varIdx (selectDistinct I.toRaw.flatten
                      (List.replicate I.toRaw.flatten.length true)) v c1, false),
                    (varIdx (selectDistinct I.toRaw.flatten
                      (List.replicate I.toRaw.flatten.length true)) v c2, false)]]
                else [])
          (encCSPInstance n) encCNF := by
        unfold encCNF
        refine flatMapWithInput hdv ?_
        refine flatMapConst (List.range k) fun c1 _ => ?_
        refine flatMapConst (List.range k) fun c2 _ => ?_
        split_ifs
        · have hl1 := (hidx_enc.comp (id'.prod (const c1))).prod (const (encOut := encBool) false)
          have hl2 := (hidx_enc.comp (id'.prod (const c2))).prod (const (encOut := encBool) false)
          exact cons' (cons' hl1 (cons' hl2 (const []))) (const [])
        · exact const []
      have hForbid : ComputableInPolyTime
          (fun I : CSPInstance n =>
            I.toRaw.flatMap fun l => forb.map fun a => (List.finRange n).map fun i =>
              (varIdx (selectDistinct I.toRaw.flatten (List.replicate I.toRaw.flatten.length true))
                (l.getD i.val 0) (a.getD i.val 0), false))
          (encCSPInstance n) encCNF := by
        unfold encCNF
        refine flatMapWithInput hraw ?_
        refine mapConst forb fun a _ => ?_
        refine mapConst (List.finRange n) fun i _ => ?_
        have hget : ComputableInPolyTime
            (fun p : CSPInstance n × List ℕ => p.2.getD i.val 0)
            (encPair (encCSPInstance n) (encList encNat)) encNat := by
          have : ComputableInPolyTime (fun _ : CSPInstance n × List ℕ => i.val)
              (encPair (encCSPInstance n) (encList encNat)) encUnary := const i.val
          fun_prop
        exact (hidx_enc.comp (((fst _ _).prod hget).prod (const (a.getD i.val 0)))).prod
          (const false)
      unfold toSAT toSATRaw encCNF
      exact listAppend' (listAppend' hAtLeast hAtMost) hForbid
    have hred : ∀ I : CSPInstance n, I ∈ CSPRel R ↔ toSAT I ∈ SAT := by
      intro I
      have hV_eq : I.toRaw.flatten = I.vars := by
        rw [CSPInstance.toRaw, CSPInstance.vars, List.flatMap_def]
      let dv := selectDistinct I.toRaw.flatten (List.replicate I.toRaw.flatten.length true)
      have hdv_mem : ∀ v, v ∈ dv ↔ v ∈ I.vars := fun v => by
        rw [← hV_eq]; exact mem_selectDistinct_replicate
      have hdv_nodup : dv.Nodup := nodup_selectDistinct _ _
      have hvar_inj : ∀ {v₁ v₂ c₁ c₂}, v₁ ∈ dv → v₂ ∈ dv → c₁ < k → c₂ < k →
          varIdx dv v₁ c₁ = varIdx dv v₂ c₂ → v₁ = v₂ ∧ c₁ = c₂ := by
        intro v₁ v₂ c₁ c₂ hv₁ hv₂ hc₁ hc₂ hEq
        have h1 : dv.idxOf v₁ = dv.idxOf v₂ := by
          have hd1 := congrArg (· / k) hEq
          simp only [varIdx, Nat.mul_add_div hkpos, Nat.div_eq_of_lt hc₁, Nat.div_eq_of_lt hc₂,
            Nat.add_zero] at hd1
          exact hd1
        have h2 : c₁ = c₂ := by
          have hm1 := congrArg (· % k) hEq
          simp only [varIdx, Nat.mul_add_mod, Nat.mod_eq_of_lt hc₁, Nat.mod_eq_of_lt hc₂] at hm1
          exact hm1
        exact ⟨(List.idxOf_inj hv₁).mp h1, h2⟩
      rw [mem_SAT]
      constructor
      · rintro ⟨σ, hσ⟩
        let τ : ℕ → Bool := fun x =>
          let i := x / k
          let c := x % k
          if hi : i < dv.length then decide ((e (σ dv[i])).val = c) else false
        have hτ : ∀ v ∈ dv, ∀ c < k, τ (varIdx dv v c) = decide ((e (σ v)).val = c) := by
          intro v hv c hc
          have hlt : dv.idxOf v < dv.length := List.idxOf_lt_length_iff.mpr hv
          have hdiv : (k * dv.idxOf v + c) / k = dv.idxOf v := by
            rw [Nat.mul_add_div hkpos, Nat.div_eq_of_lt hc, Nat.add_zero]
          have hmod : (k * dv.idxOf v + c) % k = c := by
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
          simp only [τ, varIdx, hdiv, hmod, hlt, dite_true, List.getElem_idxOf]
        refine ⟨τ, (CNF.eval_eq_true_iff _ _).mpr fun cl hcl => ?_⟩
        simp only [toSAT, toSATRaw, List.mem_append, List.mem_map, List.mem_flatMap,
          List.mem_range] at hcl
        rcases hcl with (⟨v, hv, rfl⟩ | ⟨v, hv, c1, hc1, c2, hc2, hcl⟩) | ⟨l, hl, a, ha, rfl⟩
        · rw [Clause.eval_eq_true_iff]
          refine ⟨(varIdx dv v (e (σ v)).val, true),
            List.mem_map.mpr ⟨(e (σ v)).val, List.mem_range.mpr (e (σ v)).isLt, rfl⟩, ?_⟩
          simp only [hτ v hv _ (e (σ v)).isLt, decide_true]
        · split_ifs at hcl with hlt
          · simp only [List.mem_singleton] at hcl
            subst hcl
            rw [Clause.eval_eq_true_iff]
            by_cases hc : (e (σ v)).val = c1
            · refine ⟨(varIdx dv v c2, false), List.mem_cons_of_mem _ (List.mem_singleton_self _),
                ?_⟩
              simp only [hτ v hv c2 hc2, hc, Nat.ne_of_lt hlt, decide_false]
            · refine ⟨(varIdx dv v c1, false), List.mem_cons_self, ?_⟩
              simp only [hτ v hv c1 hc1, hc, decide_false]
          · simp at hcl
        · simp only [CSPInstance.toRaw, List.mem_map] at hl
          rcases hl with ⟨t, ht, rfl⟩
          simp only [forb, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
            true_and] at ha
          rcases ha with ⟨af, haf, rfl⟩
          rw [Clause.eval_eq_true_iff]
          have hne_a : ∃ i : Fin n, e (σ (t i)) ≠ af i := by
            by_contra hall
            push Not at hall
            apply haf
            have hEq : (fun i => e.symm (af i)) = σ ∘ t := by
              funext i; simp [← hall i]
            rw [hEq]
            exact hσ t ht
          obtain ⟨i, hi⟩ := hne_a
          refine ⟨(varIdx dv (t i) (af i).val, false),
            List.mem_map.mpr ⟨i, List.mem_finRange i, by
              rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
                List.getElem_ofFn, List.getElem_ofFn]⟩, ?_⟩
          have hmem_ti : t i ∈ dv := (hdv_mem (t i)).mpr
            (List.mem_flatMap.mpr ⟨t, ht, List.mem_ofFn.mpr ⟨i, rfl⟩⟩)
          have hne_val : (e (σ (t i))).val ≠ (af i).val := fun h => hi (Fin.ext h)
          simp only [hτ (t i) hmem_ti (af i).val (af i).isLt, hne_val, decide_false]
      · rintro ⟨τ, hτ⟩
        have hall := (CNF.eval_eq_true_iff _ _).mp hτ
        have hex_c : ∀ v ∈ dv, ∃ c : Fin k, τ (varIdx dv v c.val) = true := by
          intro v hv
          have hc := hall _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.mpr ⟨v, hv, rfl⟩)))
          rw [Clause.eval_eq_true_iff] at hc
          rcases hc with ⟨lit, hlit, hev⟩
          simp only [List.mem_map, List.mem_range] at hlit
          rcases hlit with ⟨c, hc_lt, rfl⟩
          exact ⟨⟨c, hc_lt⟩, by simpa only [beq_true] using hev⟩
        have huniq_c : ∀ v ∈ dv, ∀ c1 c2 : Fin k,
            τ (varIdx dv v c1.val) = true → τ (varIdx dv v c2.val) = true → c1 = c2 := by
          intro v hv c1 c2 h1 h2
          by_contra hne
          have hne' : c1.val ≠ c2.val := fun h => hne (Fin.ext h)
          rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
          · have hcl := hall [(varIdx dv v c1.val, false), (varIdx dv v c2.val, false)]
              (List.mem_append_left _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨v, hv, List.mem_flatMap.mpr ⟨c1.val,
                  List.mem_range.mpr c1.isLt, List.mem_flatMap.mpr ⟨c2.val,
                    List.mem_range.mpr c2.isLt,
                    by rw [ite_eq_left hlt]; exact List.mem_singleton_self _⟩⟩⟩)))
            rw [Clause.eval_eq_true_iff] at hcl
            simp [h1, h2] at hcl
          · have hcl := hall [(varIdx dv v c2.val, false), (varIdx dv v c1.val, false)]
              (List.mem_append_left _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨v, hv, List.mem_flatMap.mpr ⟨c2.val,
                  List.mem_range.mpr c2.isLt, List.mem_flatMap.mpr ⟨c1.val,
                    List.mem_range.mpr c1.isLt,
                    by rw [ite_eq_left hlt]; exact List.mem_singleton_self _⟩⟩⟩)))
            rw [Clause.eval_eq_true_iff] at hcl
            simp [h1, h2] at hcl
        let d0 : D := e.symm ⟨0, hkpos⟩
        let σ : ℕ → D := fun v => if hv : v ∈ dv then e.symm (hex_c v hv).choose else d0
        refine ⟨σ, fun t ht => ?_⟩
        by_contra hnotR
        let af : Fin n → Fin k := fun i => e (σ (t i))
        have hmem_ti : ∀ i : Fin n, t i ∈ dv := fun i =>
          (hdv_mem (t i)).mpr (List.mem_flatMap.mpr ⟨t, ht, List.mem_ofFn.mpr ⟨i, rfl⟩⟩)
        have hforb : List.ofFn (fun i => (af i).val) ∈ forb := by
          simp only [forb, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
            true_and]
          refine ⟨af, ?_, rfl⟩
          have hEq : (fun i => e.symm (af i)) = σ ∘ t := by funext i; simp [af]
          rw [hEq]
          exact hnotR
        have hcl := hall _ (List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨List.ofFn t, List.mem_map.mpr ⟨t, ht, rfl⟩,
            List.mem_map.mpr ⟨List.ofFn (fun i => (af i).val), hforb, rfl⟩⟩))
        rw [Clause.eval_eq_true_iff] at hcl
        rcases hcl with ⟨lit, hlit, hev⟩
        simp only [List.mem_map, List.mem_finRange, true_and] at hlit
        rcases hlit with ⟨i, rfl⟩
        have hget_t : (List.ofFn t).getD i.val 0 = t i := by simp
        have hget_a : (List.ofFn fun j => (af j).val).getD i.val 0 = (af i).val := by simp
        rw [hget_t, hget_a] at hev
        have haf_eq : af i = (hex_c (t i) (hmem_ti i)).choose := by
          simp [af, σ, hmem_ti i]
        have htrue : τ (varIdx dv (t i) (af i).val) = true := by
          rw [haf_eq]
          exact (hex_c (t i) (hmem_ti i)).choose_spec
        exact Bool.false_ne_true (hev.symm.trans htrue)
    have hvars : ∀ I : CSPInstance n, (toSAT I).numVars ≤ k * I.numVars := by
      intro I
      have hV_eq : I.toRaw.flatten = I.vars := by
        rw [CSPInstance.toRaw, CSPInstance.vars, List.flatMap_def]
      let dv := selectDistinct I.toRaw.flatten (List.replicate I.toRaw.flatten.length true)
      have hdv_len : dv.length = I.numVars := by
        rw [CSPInstance.numVars, ← hV_eq]
        exact length_selectDistinct_replicate _
      have hdv_mem : ∀ v, v ∈ dv ↔ v ∈ I.vars := fun v => by
        rw [← hV_eq]; exact mem_selectDistinct_replicate
      have hsub : (toSAT I).vars.toFinset ⊆ Finset.range (k * I.numVars) := by
        intro x hx
        rw [List.mem_toFinset, CNF.mem_vars] at hx
        rcases hx with ⟨cl, hcl, b, hlit⟩
        rw [Finset.mem_range, ← hdv_len]
        have hbound_idx : ∀ v ∈ dv, ∀ c < k, varIdx dv v c < k * dv.length := by
          intro v hv c hc
          have hlt : dv.idxOf v < dv.length := List.idxOf_lt_length_iff.mpr hv
          dsimp [varIdx]
          nlinarith
        simp only [toSAT, toSATRaw, List.mem_append, List.mem_map, List.mem_flatMap,
          List.mem_range] at hcl
        rcases hcl with (⟨v, hv, rfl⟩ | ⟨v, hv, c1, hc1, c2, hc2, hcl⟩) | ⟨l, hl, a, ha, rfl⟩
        · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hlit
          rcases hlit with ⟨c, hc, rfl, _⟩
          exact hbound_idx v hv c hc
        · split_ifs at hcl with hlt
          · simp only [List.mem_singleton] at hcl
            subst hcl
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlit
            rcases hlit with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact hbound_idx v hv c1 hc1
            · exact hbound_idx v hv c2 hc2
          · simp at hcl
        · simp only [List.mem_map, List.mem_finRange, true_and, Prod.mk.injEq] at hlit
          rcases hlit with ⟨i, rfl, _⟩
          simp only [CSPInstance.toRaw, List.mem_map] at hl
          rcases hl with ⟨t, ht, rfl⟩
          simp only [forb, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
            true_and] at ha
          rcases ha with ⟨af, _, rfl⟩
          have hget_t : (List.ofFn t).getD i.val 0 = t i := by simp
          have hget_a : (List.ofFn fun j => (af j).val).getD i.val 0 = (af i).val := by simp
          rw [hget_t, hget_a]
          have hmem_ti : t i ∈ dv := (hdv_mem (t i)).mpr
            (List.mem_flatMap.mpr ⟨t, ht, List.mem_ofFn.mpr ⟨i, rfl⟩⟩)
          exact hbound_idx (t i) hmem_ti (af i).val (af i).isLt
      calc (toSAT I).numVars = (toSAT I).vars.toFinset.card := rfl
        _ ≤ (Finset.range (k * I.numVars)).card := Finset.card_le_card hsub
        _ = k * I.numVars := Finset.card_range _
    have hres := SAT_decidableInExpTime_one.of_reduction hpoly hred (c := k)
      (fun I => (hvars I).trans (Nat.le_add_right _ _)) zero_le_one
    simpa [k] using hres

/-- **Jonsson–Lagerkvist–Nordh–Zanuttini** (rate-exponent form): if `pPol(R) ⊆ pPol(R')` on
a finite domain `D`, then `cspRateExponent R' ≤ cspRateExponent R` unconditionally (for all `R, R'`,
including `R' = ∅`).
-/
theorem CSPRel.cspRateExponent_le_of_ppolSubset {D : Type*} [Finite D]
    {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)} (hppol : PPolSubset R R') :
    cspRateExponent R' ≤ cspRateExponent R := by
  have : Fintype D := Fintype.ofFinite D
  classical
  by_cases hne : R'.Nonempty
  · have hdef : IsQFPPDefinable R R' := (poschel_galois_qfpp (Or.inl hne)).mp hppol
    have hnonempty : (Fintype.card D : ℝ) ∈
        {δ | 0 ≤ δ ∧ DecidableInExpTime (CSPRel R) (encCSPInstance n) CSPInstance.numVars δ} :=
      ⟨Nat.cast_nonneg _, decidableInExpTime_of_fintype R⟩
    change cspRateExponent R' ≤ Cslib.rateExponent _
    rw [Cslib.rateExponent_def]
    exact le_csInf ⟨_, hnonempty⟩ fun δ hδ =>
      Cslib.rateExponent_le hδ.1 (decidableInExpTime_of_isQFPPDefinable hdef hδ.1 hδ.2)
  · -- When `R' = ∅`, `CSPRel R' = {[]}` (or `∅` if `D` is empty), both in `P`, so rate is `0`!
    have hEmpty : R' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hEmpty
    have hP : CSPRel (∅ : Set (Fin n' → D)) ∈ P (encCSPInstance n') := by
      by_cases hD : IsEmpty D
      · refine ⟨fun _ => false, const false, fun I => ?_⟩
        simp only [CSPRel, Set.mem_ofPred_eq, Bool.false_eq_true, iff_false, not_exists]
        intro σ _; exact isEmptyElim (σ 0)
      · have : Nonempty D := not_isEmpty_iff.mp hD
        refine ⟨fun I => I.toRaw.isEmpty,
          (listIsEmpty' (encList encNat)).comp (computableInPolyTime_toRaw n'), fun I => ?_⟩
        cases I with
        | nil =>
          simp only [CSPRel, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
            imp_true_iff, CSPInstance.toRaw, List.map_nil, List.isEmpty_nil, iff_true]
          exact ⟨fun _ => Classical.arbitrary D, trivial⟩
        | cons t ts =>
          simp only [CSPRel, Set.mem_ofPred_eq, List.mem_cons, Set.mem_empty_iff_false,
            CSPInstance.toRaw, List.map_cons, List.isEmpty_cons, Bool.false_eq_true, iff_false,
            not_exists]
          intro σ hσ
          exact hσ t (Or.inl rfl)
    have h0 : DecidableInExpTime (CSPRel (∅ : Set (Fin n' → D)))
        (encCSPInstance n') CSPInstance.numVars 0 := by
      obtain ⟨g, hg, hred⟩ := hP
      exact .of_computableInPolyTime hg hred
    have hle0 : cspRateExponent (∅ : Set (Fin n' → D)) ≤ 0 :=
      Cslib.rateExponent_le le_rfl h0
    exact hle0.trans (Cslib.rateExponent_nonneg _)

/-- **Jonsson–Lagerkvist–Nordh–Zanuttini** (base-`T` form): `pPol(R) ⊆ pPol(R')` implies
${\sf T}(R') \le {\sf T}(R)$ unconditionally on any finite domain.
-/
theorem CSPRel.cspTimeBase_le_of_ppolSubset {D : Type*} [Finite D]
    {n n' : ℕ} {R : Set (Fin n → D)} {R' : Set (Fin n' → D)} (hppol : PPolSubset R R') :
    cspTimeBase R' ≤ cspTimeBase R :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (cspRateExponent_le_of_ppolSubset hppol)

end Cslib.Complexity
