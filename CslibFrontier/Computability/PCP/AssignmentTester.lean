/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Basic

import Mathlib.Data.Fintype.Card
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alphabet-Polymorphic Assignment Testers and Constraint-Graph Composition

Defines assignment testers over arbitrary (finite or infinite) input and output alphabets, together
with Dinur-style edge-by-edge composition with any finite-edge `Cslib.PCP.ConstraintGraph` and a
subset-decoding invariant that preserves restricted unsatisfiability values over any non-empty
target sub-alphabet.

## Main definitions

* `CslibFrontier.PCP.AssignmentTester`: an `ℓ`-query assignment tester reducing binary constraints
  over input alphabet `A` to `ℓ`-ary constraints in `D` over output alphabet `Γ`, with error
  threshold `ζ > 0` and relative Hamming distance `δ > 0`.
* `CslibFrontier.PCP.composeGraph`: composed constraint graph over tuple alphabet `Fin ℓ → Γ` with
  `(ℓ + 1) · R · |E|` edges.
* `CslibFrontier.PCP.unsatValRestricted`: minimum unsatisfied edge fraction over assignments taking
  values in a restricted subset `S ⊆ α`.
* `CslibFrontier.PCP.AssignmentTester.SubsetDecoding`: unique `< δ / 2`-ball decoding preserves
  membership in a sub-alphabet `S ⊆ A` from `W ⊆ Γ`.

## Main results

* `CslibFrontier.PCP.composeGraph_unsatVal_eq_zero`: completeness of assignment-tester composition.
* `CslibFrontier.PCP.le_unsatVal_composeGraph`: soundness bound
  `(ζ / (ℓ + 1)) · UNSAT(G) ≤ UNSAT(composeGraph G cEdge T)`.
* `CslibFrontier.PCP.le_unsatValRestricted_composeGraph`: restricted-alphabet soundness bound under
  `AssignmentTester.SubsetDecoding`.
-/

public section

namespace CslibFrontier.PCP

open Cslib.PCP
open scoped BigOperators

/-- Relative Hamming difference count `#{i : Fin k | u i ≠ v i}` over an arbitrary alphabet. -/
noncomputable def tupleDiffCount {Γ : Type*} {k : ℕ} (u v : Fin k → Γ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin k ↦ u i ≠ v i).card

theorem tupleDiffCount_triangle {Γ : Type*} {k : ℕ} (u v w : Fin k → Γ) :
    tupleDiffCount u w ≤ tupleDiffCount u v + tupleDiffCount v w := by
  classical
  dsimp only [tupleDiffCount]
  refine (Finset.card_le_card (t :=
      (Finset.univ.filter fun i ↦ u i ≠ v i) ∪
        (Finset.univ.filter fun i ↦ v i ≠ w i)) fun i hi ↦ ?_).trans
    (Finset.card_union_le _ _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h; push Not at h; exact hi (h.1.trans h.2)

/-- Concatenation `(u, v, aux)` of two `k`-tuples and an `m`-tuple into `Fin (2 * k + m) → Γ`. -/
@[expose]
def concatThree {Γ : Type*} {k m : ℕ} (u v : Fin k → Γ) (aux : Fin m → Γ)
    (idx : Fin (2 * k + m)) : Γ :=
  if h1 : idx.1 < k then u ⟨idx.1, h1⟩
  else if h2 : idx.1 < 2 * k then v ⟨idx.1 - k, by omega⟩
  else aux ⟨idx.1 - 2 * k, by omega⟩

/-- Number of indices `r : Fin R` satisfying `P r`. -/
noncomputable def countPassing {R : ℕ} (P : Fin R → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

/-- An `ℓ`-query assignment tester over arbitrary input alphabet `A` and output alphabet `Γ` for an
indexed family of binary relations `evalC : CIdx → A → A → Prop`, outputting local `ℓ`-ary
constraints in `D`. -/
structure AssignmentTester (A Γ CIdx : Type*) {ℓ : ℕ} (evalC : CIdx → A → A → Prop)
    (D : Set ((Fin ℓ → Γ) → Prop)) where
  /-- Codeword length `k ≥ 1`. -/
  k : ℕ
  /-- Positivity of codeword length. -/
  hk : 1 ≤ k
  /-- Auxiliary block length per tested constraint. -/
  m : ℕ
  /-- Number of local checks (verifier coin outcomes) per tested constraint. -/
  R : ℕ
  /-- Positivity of local check count. -/
  hR : 1 ≤ R
  /-- Positivity of query arity. -/
  hℓ : 1 ≤ ℓ
  /-- Soundness rejection threshold `ζ > 0`. -/
  ζ : ℝ
  /-- Positivity of `ζ`. -/
  hζ : 0 < ζ
  /-- Relative minimum Hamming distance `δ > 0` of `encode`. -/
  δ : ℝ
  /-- Positivity of `δ`. -/
  hδ : 0 < δ
  /-- Error-correcting encoding `A → (Fin k → Γ)`. -/
  encode : A → (Fin k → Γ)
  /-- Minimum distance lower bound on distinct inputs. -/
  dist_encode : ∀ x y : A, x ≠ y → δ * (k : ℝ) ≤ (tupleDiffCount (encode x) (encode y) : ℝ)
  /-- Non-adaptive query map into the concatenated `(u, v, aux)` view. -/
  query : CIdx → Fin R → Fin ℓ → Fin (2 * k + m)
  /-- Local `ℓ`-ary accepting set for constraint index `c` and coin `r`. -/
  testSet : CIdx → Fin R → Set (Fin ℓ → Γ)
  /-- Every local check belongs to `D`. -/
  testSet_mem : ∀ (c : CIdx) (r : Fin R), (fun v ↦ v ∈ testSet c r) ∈ D
  /-- Perfect completeness: valid pairs `(x, y)` extend to an auxiliary tuple passing all checks. -/
  complete : ∀ (c : CIdx) (x y : A), evalC c x y →
    ∃ aux : Fin m → Γ, ∀ r : Fin R,
      (fun j ↦ concatThree (encode x) (encode y) aux (query c r j)) ∈ testSet c r
  /-- Soundness: passing at least `(1 - ζ) R` checks implies `< δ / 2`-closeness to an encoded
  satisfying pair `(x, y)`. -/
  sound : ∀ (c : CIdx) (α β : Fin k → Γ) (γ : Fin m → Γ),
    (1 - ζ) * (R : ℝ) ≤
      (countPassing (fun r : Fin R ↦
        (fun j ↦ concatThree α β γ (query c r j)) ∈ testSet c r) : ℝ) →
    ∃ x y : A, evalC c x y ∧
      (tupleDiffCount α (encode x) : ℝ) < (δ / 2) * (k : ℝ) ∧
      (tupleDiffCount β (encode y) : ℝ) < (δ / 2) * (k : ℝ)

/-- Subset-decoding property: any codeword strictly within relative distance `δ / 2` of a
`W`-valued string comes from an element of `S`. -/
@[expose]
def AssignmentTester.SubsetDecoding {A Γ CIdx : Type*} {ℓ : ℕ} {evalC : CIdx → A → A → Prop}
    {D : Set ((Fin ℓ → Γ) → Prop)} (T : AssignmentTester A Γ CIdx evalC D)
    (S : Set A) (W : Set Γ) : Prop :=
  ∀ (b : Fin T.k → Γ) (x : A), (∀ i : Fin T.k, b i ∈ W) →
    (tupleDiffCount b (T.encode x) : ℝ) < (T.δ / 2) * (T.k : ℝ) → x ∈ S

/-- Uniqueness of `< δ / 2`-decoding for any `AssignmentTester`. -/
theorem AssignmentTester.decode_unique {A Γ CIdx : Type*} {ℓ : ℕ} {evalC : CIdx → A → A → Prop}
    {D : Set ((Fin ℓ → Γ) → Prop)} (T : AssignmentTester A Γ CIdx evalC D)
    {b : Fin T.k → Γ} {x y : A}
    (hx : (tupleDiffCount b (T.encode x) : ℝ) < (T.δ / 2) * (T.k : ℝ))
    (hy : (tupleDiffCount b (T.encode y) : ℝ) < (T.δ / 2) * (T.k : ℝ)) :
    x = y := by
  by_contra hne
  have hdist := T.dist_encode x y hne
  have hsym : tupleDiffCount (T.encode x) b = tupleDiffCount b (T.encode x) := by
    classical
    dsimp only [tupleDiffCount]; simp only [ne_comm]
  have htri : (tupleDiffCount (T.encode x) (T.encode y) : ℝ) ≤
      (tupleDiffCount b (T.encode x) : ℝ) + (tupleDiffCount b (T.encode y) : ℝ) := by
    rw [← hsym]; exact_mod_cast tupleDiffCount_triangle (T.encode x) b (T.encode y)
  linarith

/-- Vertex type of the composed constraint graph: codeword symbols `V × Fin k`, per-edge auxiliary
symbols `E × Fin m`, and per-check local views `E × Fin R`. -/
abbrev ComposedVertex (V E : Type*) (k m R : ℕ) : Type _ :=
  (V × Fin k) ⊕ (E × Fin m) ⊕ (E × Fin R)

/-- Edge type of the composed constraint graph: for each `(e, r)`, one self-loop `none` enforcing
the local test and `ℓ` consistency edges `some j`. -/
abbrev ComposedEdge (E : Type*) (R ℓ : ℕ) : Type _ :=
  E × Fin R × Option (Fin ℓ)

/-- Target vertex in `ComposedVertex V E k m R` corresponding to window index `idx`. -/
@[expose]
def composedTarget {V E : Type*} {k m R : ℕ} (u v : V) (e : E)
    (idx : Fin (2 * k + m)) : ComposedVertex V E k m R :=
  if h1 : idx.1 < k then .inl (u, ⟨idx.1, h1⟩)
  else if h2 : idx.1 < 2 * k then .inl (v, ⟨idx.1 - k, by omega⟩)
  else .inr (.inl (e, ⟨idx.1 - 2 * k, by omega⟩))

/-- Composed constraint graph over tuple alphabet `Fin ℓ → Γ`. -/
@[expose]
def composeGraph {V E A Γ CIdx : Type*} {ℓ : ℕ} {evalC : CIdx → A → A → Prop}
    {D : Set ((Fin ℓ → Γ) → Prop)}
    (G : ConstraintGraph V E A) (cEdge : E → CIdx) (T : AssignmentTester A Γ CIdx evalC D) :
    ConstraintGraph (ComposedVertex V E T.k T.m T.R) (ComposedEdge E T.R ℓ) (Fin ℓ → Γ) where
  src er := .inr (.inr (er.1, er.2.1))
  dst er := match er.2.2 with
    | none => .inr (.inr (er.1, er.2.1))
    | some j => composedTarget (G.src er.1) (G.dst er.1) er.1 (T.query (cEdge er.1) er.2.1 j)
  rel er x y := match er.2.2 with
    | none => x ∈ T.testSet (cEdge er.1) er.2.1
    | some j => x j = y ⟨0, T.hℓ⟩

theorem card_composedEdge (E : Type*) [Fintype E] (R ℓ : ℕ) :
    Fintype.card (ComposedEdge E R ℓ) = (ℓ + 1) * R * Fintype.card E := by
  simp only [ComposedEdge, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]; ring

/-- Minimum unsatisfied fraction of `G` over assignments restricted to a subset `S ⊆ α`. -/
noncomputable def unsatValRestricted {V E α : Type*} [Fintype E]
    (G : ConstraintGraph V E α) (S : Set α) : ℝ :=
  sInf {G.unsatFrac σ | (σ : V → α) (_ : ∀ v : V, σ v ∈ S)}

theorem exists_unsatFrac_eq_unsatValRestricted {V E α : Type*} [Fintype E]
    (G : ConstraintGraph V E α) {S : Set α} (hS : S.Nonempty) :
    ∃ σ : V → α, (∀ v : V, σ v ∈ S) ∧ G.unsatFrac σ = unsatValRestricted G S := by
  obtain ⟨s₀, hs₀⟩ := hS
  have hne : {G.unsatFrac σ | (σ : V → α) (_ : ∀ v, σ v ∈ S)}.Nonempty :=
    ⟨G.unsatFrac (fun _ ↦ s₀), fun _ ↦ s₀, fun _ ↦ hs₀, rfl⟩
  have hfin : {G.unsatFrac σ | (σ : V → α) (_ : ∀ v, σ v ∈ S)}.Finite :=
    G.finite_range_unsatFrac.subset (by rintro _ ⟨σ, -, rfl⟩; exact ⟨σ, rfl⟩)
  obtain ⟨σ, hσ, heq⟩ := hne.csInf_mem hfin
  exact ⟨σ, hσ, heq⟩

theorem unsatValRestricted_le {V E α : Type*} [Fintype E]
    (G : ConstraintGraph V E α) {S : Set α} {σ : V → α} (hσ : ∀ v : V, σ v ∈ S) :
    unsatValRestricted G S ≤ G.unsatFrac σ := by
  refine csInf_le ⟨0, ?_⟩ ⟨σ, hσ, rfl⟩
  rintro _ ⟨τ, -, rfl⟩; exact G.unsatFrac_nonneg τ

/-- Subset-decoding soundness of assignment-tester composition: if `T` is subset-decoding on
`(S, W)`, then `(ζ / (ℓ + 1)) · UNSAT_S(G) ≤ UNSAT_{W^ℓ}(composeGraph G cEdge T)`. -/
theorem le_unsatValRestricted_composeGraph {V E A Γ CIdx : Type*} [Fintype E] {ℓ : ℕ}
    {evalC : CIdx → A → A → Prop} {D : Set ((Fin ℓ → Γ) → Prop)}
    (G : ConstraintGraph V E A) (cEdge : E → CIdx)
    (hc : ∀ (e : E) (x y : A), G.rel e x y ↔ evalC (cEdge e) x y)
    (T : AssignmentTester A Γ CIdx evalC D) {S : Set A} {W : Set Γ}
    (hS : S.Nonempty) (hW : W.Nonempty) (hdec : T.SubsetDecoding S W) :
    (T.ζ / ((ℓ : ℝ) + 1)) * unsatValRestricted G S ≤
      unsatValRestricted (composeGraph G cEdge T) {v : Fin ℓ → Γ | ∀ j, v j ∈ W} := by
  classical
  let h0 : Fin ℓ := ⟨0, T.hℓ⟩
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨w₀, hw₀⟩ := hW
  let G' := composeGraph G cEdge T
  obtain ⟨B, hBW, hBmin⟩ := exists_unsatFrac_eq_unsatValRestricted G'
    (S := {v : Fin ℓ → Γ | ∀ j, v j ∈ W}) ⟨fun _ ↦ w₀, fun _ ↦ hw₀⟩
  rw [← hBmin]
  by_cases hE0 : Fintype.card E = 0
  · have : IsEmpty E := Fintype.card_eq_zero_iff.mp hE0
    have hG0 : unsatValRestricted G S ≤ 0 := by
      simpa [ConstraintGraph.unsatFrac] using
        unsatValRestricted_le G (σ := fun _ ↦ s₀) (fun _ ↦ hs₀)
    have hpos : 0 ≤ T.ζ / ((ℓ : ℝ) + 1) := by have := T.hζ; positivity
    exact (mul_nonpos_of_nonneg_of_nonpos hpos hG0).trans (G'.unsatFrac_nonneg B)
  · let word (u : V) (i : Fin T.k) : Γ := B (.inl (u, i)) h0
    let aux (e : E) (j : Fin T.m) : Γ := B (.inr (.inl (e, j))) h0
    have hwordW (u : V) (i : Fin T.k) : word u i ∈ W := hBW (.inl (u, i)) h0
    let close (u : V) : Prop := ∃ x : A, (tupleDiffCount (word u) (T.encode x) : ℝ) <
      (T.δ / 2) * (T.k : ℝ)
    let σ (u : V) : A := if h : close u then h.choose else s₀
    have hσS (u : V) : σ u ∈ S := by
      dsimp only [σ]
      by_cases h : close u
      · rw [dite_eq_left h]; exact hdec (word u) h.choose (hwordW u) h.choose_spec
      · rw [dite_eq_right h]; exact hs₀
    have hedge (e : E) (hunsat : e ∈ G.unsatEdges σ) :
        T.ζ * (T.R : ℝ) ≤
          ((Finset.univ.filter fun ro : Fin T.R × Option (Fin ℓ) ↦
            (e, ro.1, ro.2) ∈ G'.unsatEdges B).card : ℝ) := by
      by_contra hlt; push Not at hlt
      let good (r : Fin T.R) : Prop := ∀ o : Option (Fin ℓ), (e, r, o) ∉ G'.unsatEdges B
      have hbad_le : (Finset.univ.filter fun r : Fin T.R ↦ ¬ good r).card ≤
          (Finset.univ.filter fun ro : Fin T.R × Option (Fin ℓ) ↦
            (e, ro.1, ro.2) ∈ G'.unsatEdges B).card := by
        have hpick : ∀ r ∈ Finset.univ.filter (fun r : Fin T.R ↦ ¬ good r),
            ∃ o : Option (Fin ℓ), (e, r, o) ∈ G'.unsatEdges B := fun r hr ↦ by
          have := (Finset.mem_filter.mp hr).2; dsimp [good] at this; push Not at this; exact this
        refine Finset.card_le_card_of_injOn
          (fun r ↦ if hr : r ∈ Finset.univ.filter (fun r ↦ ¬ good r)
            then (r, (hpick r hr).choose) else (r, none))
          (fun r hr ↦ by
            have hr' : r ∈ Finset.univ.filter fun r ↦ ¬ good r := hr
            dsimp only; rw [Finset.mem_coe, dite_eq_left hr']
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpick r hr').choose_spec⟩)
          (fun r₁ h₁ r₂ h₂ heq ↦ by
            have h₁' : r₁ ∈ Finset.univ.filter fun r ↦ ¬ good r := h₁
            have h₂' : r₂ ∈ Finset.univ.filter fun r ↦ ¬ good r := h₂
            dsimp only at heq; rw [dite_eq_left h₁', dite_eq_left h₂'] at heq
            exact (Prod.mk.inj heq).1)
      have hgood_part := Finset.card_filter_add_card_filter_not good (s := Finset.univ)
      rw [Finset.card_univ, Fintype.card_fin] at hgood_part
      have hpass_ge : (1 - T.ζ) * (T.R : ℝ) ≤
          (countPassing (fun r : Fin T.R ↦
            (fun j ↦ concatThree (word (G.src e)) (word (G.dst e)) (aux e)
              (T.query (cEdge e) r j)) ∈ T.testSet (cEdge e) r) : ℝ) := by
        have hsub : (Finset.univ.filter good).card ≤
            countPassing (fun r : Fin T.R ↦
              (fun j ↦ concatThree (word (G.src e)) (word (G.dst e)) (aux e)
                (T.query (cEdge e) r j)) ∈ T.testSet (cEdge e) r) :=
          Finset.card_le_card fun r hr ↦ by
            have hg := (Finset.mem_filter.mp hr).2
            have hnone : G'.Satisfies B (e, r, none) :=
              not_not.mp ((ConstraintGraph.mem_unsatEdges (G := G')).not.mp (hg none))
            have hsome (j : Fin ℓ) : B (.inr (.inr (e, r))) j =
                concatThree (word (G.src e)) (word (G.dst e)) (aux e)
                  (T.query (cEdge e) r j) := by
              have hj : G'.Satisfies B (e, r, some j) :=
                not_not.mp ((ConstraintGraph.mem_unsatEdges (G := G')).not.mp (hg (some j)))
              change B (.inr (.inr (e, r))) j =
                B (composedTarget (G.src e) (G.dst e) e (T.query (cEdge e) r j)) h0 at hj
              rw [hj]; unfold composedTarget concatThree; split_ifs <;> rfl
            change B (.inr (.inr (e, r))) ∈ T.testSet (cEdge e) r at hnone
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← funext hsome] using hnone
        have hbad_r : ((Finset.univ.filter fun r : Fin T.R ↦ ¬ good r).card : ℝ) <
            T.ζ * (T.R : ℝ) := lt_of_le_of_lt (by exact_mod_cast hbad_le) hlt
        have hp_r : ((Finset.univ.filter good).card : ℝ) +
            ((Finset.univ.filter fun r : Fin T.R ↦ ¬ good r).card : ℝ) = (T.R : ℝ) := by
          exact_mod_cast hgood_part
        have hsub_r := (Nat.cast_le (α := ℝ)).mpr hsub
        linarith
      obtain ⟨x, y, hxy, hx, hy⟩ := T.sound (cEdge e) (word (G.src e)) (word (G.dst e)) (aux e)
        hpass_ge
      have hcs : close (G.src e) := ⟨x, hx⟩
      have hcd : close (G.dst e) := ⟨y, hy⟩
      have hsx : σ (G.src e) = x := by
        dsimp only [σ]; rw [dite_eq_left hcs]; exact T.decode_unique hcs.choose_spec hx
      have hdy : σ (G.dst e) = y := by
        dsimp only [σ]; rw [dite_eq_left hcd]; exact T.decode_unique hcd.choose_spec hy
      exact (ConstraintGraph.mem_unsatEdges.mp hunsat)
        ((hc e _ _).mpr (hsx ▸ hdy ▸ hxy))
    have hsum : T.ζ * (T.R : ℝ) * ((G.unsatEdges σ).card : ℝ) ≤ ((G'.unsatEdges B).card : ℝ) := by
      have h1 : ∑ _e ∈ G.unsatEdges σ, T.ζ * (T.R : ℝ) ≤
          ∑ e : E, ((Finset.univ.filter fun ro : Fin T.R × Option (Fin ℓ) ↦
            (e, ro.1, ro.2) ∈ G'.unsatEdges B).card : ℝ) :=
        (Finset.sum_le_sum fun e he ↦ hedge e he).trans
          (Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.cast_nonneg _)
      have h2 : (∑ e : E, (Finset.univ.filter fun ro : Fin T.R × Option (Fin ℓ) ↦
          (e, ro.1, ro.2) ∈ G'.unsatEdges B).card) = (G'.unsatEdges B).card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun p _ ↦ (p.1, p.2.1, p.2.2))
          (fun p hp ↦ (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2)
          (fun p₁ _ p₂ _ h ↦ by
            rcases p₁ with ⟨e₁, r₁, o₁⟩; rcases p₂ with ⟨e₂, r₂, o₂⟩
            simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl, rfl⟩; rfl)
          (fun er her ↦ ⟨⟨er.1, (er.2.1, er.2.2)⟩,
            Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, her⟩⟩, rfl⟩)
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at h1
      exact h1.trans_eq (by exact_mod_cast h2)
    have hE_pos : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hE0)
    have hR_pos : (0 : ℝ) < T.R := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one T.hR)
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    refine (mul_le_mul_of_nonneg_left (unsatValRestricted_le G hσS)
      (by have := T.hζ; positivity)).trans ?_
    rw [ConstraintGraph.unsatFrac, ConstraintGraph.unsatFrac, card_composedEdge]
    push_cast
    rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hℓ_pos hE_pos)
      (mul_pos (mul_pos hℓ_pos hR_pos) hE_pos)]
    have := mul_le_mul_of_nonneg_right hsum (mul_pos hℓ_pos hE_pos).le
    linarith

/-- Unconditional soundness of assignment-tester composition over any non-empty alphabet:
`(ζ / (ℓ + 1)) · UNSAT(G) ≤ UNSAT(composeGraph G cEdge T)`. -/
theorem le_unsatVal_composeGraph {V E A Γ CIdx : Type*} [Fintype E] [Nonempty A] [Nonempty Γ]
    {ℓ : ℕ} {evalC : CIdx → A → A → Prop} {D : Set ((Fin ℓ → Γ) → Prop)}
    (G : ConstraintGraph V E A) (cEdge : E → CIdx)
    (hc : ∀ (e : E) (x y : A), G.rel e x y ↔ evalC (cEdge e) x y)
    (T : AssignmentTester A Γ CIdx evalC D) :
    (T.ζ / ((ℓ : ℝ) + 1)) * G.unsatVal ≤ (composeGraph G cEdge T).unsatVal := by
  have h1 : unsatValRestricted G Set.univ = G.unsatVal := by
    unfold unsatValRestricted ConstraintGraph.unsatVal; congr 1; ext r; simp [Set.mem_range]
  have h2 : unsatValRestricted (composeGraph G cEdge T) Set.univ =
      (composeGraph G cEdge T).unsatVal := by
    unfold unsatValRestricted ConstraintGraph.unsatVal; congr 1; ext r; simp [Set.mem_range]
  have hset : {v : Fin ℓ → Γ | ∀ j, v j ∈ (Set.univ : Set Γ)} = Set.univ := by ext; simp
  have hle := le_unsatValRestricted_composeGraph G cEdge hc T Set.univ_nonempty Set.univ_nonempty
    fun _ _ _ _ ↦ Set.mem_univ _
  rwa [hset, h1, h2] at hle

/-- Completeness of assignment-tester composition: if `UNSAT(G) = 0`, then
`UNSAT(composeGraph G cEdge T) = 0`. -/
theorem composeGraph_unsatVal_eq_zero {V E A Γ CIdx : Type*} [Fintype E] [Nonempty A] [Nonempty Γ]
    {ℓ : ℕ} {evalC : CIdx → A → A → Prop} {D : Set ((Fin ℓ → Γ) → Prop)}
    (G : ConstraintGraph V E A) (cEdge : E → CIdx)
    (hc : ∀ (e : E) (x y : A), G.rel e x y ↔ evalC (cEdge e) x y)
    (T : AssignmentTester A Γ CIdx evalC D) (h0 : G.unsatVal = 0) :
    (composeGraph G cEdge T).unsatVal = 0 := by
  have : Nonempty (Fin ℓ → Γ) := ⟨fun _ ↦ Classical.arbitrary Γ⟩
  obtain ⟨σ, hσ⟩ := (ConstraintGraph.unsatVal_eq_zero_iff G).mp h0
  have haux : ∀ e : E, ∃ aux : Fin T.m → Γ, ∀ r : Fin T.R,
      (fun j ↦ concatThree (T.encode (σ (G.src e))) (T.encode (σ (G.dst e))) aux
        (T.query (cEdge e) r j)) ∈ T.testSet (cEdge e) r :=
    fun e ↦ T.complete (cEdge e) _ _ ((hc e _ _).mp (hσ e))
  choose auxFn hauxFn using haux
  refine (ConstraintGraph.unsatVal_eq_zero_iff _).mpr ⟨fun w ↦ match w with
    | .inl (u, i) => fun _ ↦ T.encode (σ u) i
    | .inr (.inl (e, a)) => fun _ ↦ auxFn e a
    | .inr (.inr (e, r)) => fun j ↦ concatThree (T.encode (σ (G.src e)))
        (T.encode (σ (G.dst e))) (auxFn e) (T.query (cEdge e) r j), ?_⟩
  rintro ⟨e, r, none | j⟩
  · exact hauxFn e r
  · dsimp only [ConstraintGraph.Satisfies, composeGraph, composedTarget, concatThree]
    split_ifs <;> rfl

end CslibFrontier.PCP
