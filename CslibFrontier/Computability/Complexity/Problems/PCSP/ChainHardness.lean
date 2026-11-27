/-
Copyright (c) 2026 PanMath Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PCP.Approximation.LabelCover.SmallSoundness
public import CslibFrontier.Computability.Complexity.Problems.PCSP.MinorCondition

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.PCP.Encoded.Size
import CslibFrontier.Tactic.EncLen
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Chain-Minor Hardness Criterion for Promise CSPs

This module formalizes the chain-of-minors NP-hardness criterion of Brandts, Wrochna, and Živný
 for `PMC_M(m)` and `PCSP(A, B)`, proved under standard Lean axioms directly
from the parallel-repeated Label Cover hardness theorem
`Cslib.Complexity.exists_GapLabelCover_npHard`.

## Main definitions

* `Cslib.Complexity.PCSP.MinorChain`: a chain of minors `f_0 → f_1 →... → f_ℓ` of arities `≤ m`.
* `Cslib.Complexity.PCSP.MinorChain.composeMap`: composed minor map `π_{i, j}` along a `MinorChain`.

## Main results

* `Cslib.Complexity.PCSP.MinorChain.minor_composeMap`:
  `M.minor (C.composeMap i j hij) (C.elem i) = C.elem j`.
* `Cslib.Complexity.PCSP.npHard_pmc_of_chain_selector`: chain-of-minors NP-hardness for `PMC_M(m)`
.
* `Cslib.Complexity.PCSP.npHard_pcsp_of_chain_selector`: chain-of-minors NP-hardness for
  `PCSP(A, B)`.
-/

public section

namespace Cslib.Complexity.PCSP

open Cslib.Complexity
open Cslib.PCP
open Cslib.PCP.Encoded
open Turing.MultiTapeTM

universe u v

/-! ### Chain-of-minors hardness criterion -/

/-- A chain of minors of length `ℓ` with all arities bounded by `m`. -/
structure MinorChain (M : Minion.{u}) (ℓ m : ℕ) where
  /-- Arity of the `i`-th element (`0 ≤ i ≤ ℓ`). -/
  arity : Fin (ℓ + 1) → ℕ
  /-- Every arity is at most `m`. -/
  arity_le : ∀ i, arity i ≤ m
  /-- The elements `f_0, f_1, ..., f_ℓ` of the chain. -/
  elem : ∀ i : Fin (ℓ + 1), M.carrier (arity i)
  /-- The step maps `π_{i, i+1} : Fin (arity i) → Fin (arity (i+1))`. -/
  stepMap : ∀ i : Fin ℓ, Fin (arity i.castSucc) → Fin (arity i.succ)
  /-- Each step satisfies `M.minor (stepMap i) (elem i) = elem (i + 1)`. -/
  step_minor : ∀ i : Fin ℓ, M.minor (stepMap i) (elem i.castSucc) = elem i.succ

namespace MinorChain

/-- Composed minor map `π_{i, j} : Fin (arity i) → Fin (arity j)` along a `MinorChain` for
`i ≤ j`. -/
def composeMap {M : Minion.{u}} {ℓ m : ℕ} (C : MinorChain M ℓ m) :
    ∀ (i j : Fin (ℓ + 1)), i ≤ j → Fin (C.arity i) → Fin (C.arity j)
  | i, ⟨j, hj⟩, hij =>
    if hlt : i.1 < j then
      have hj' : j - 1 < ℓ := by omega
      have hij' : i ≤ ⟨j - 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
      have heq : (⟨j - 1, hj'⟩ : Fin ℓ).succ = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
      heq ▸ (C.stepMap ⟨j - 1, hj'⟩ ∘ C.composeMap i ⟨j - 1, by omega⟩ hij')
    else
      have heq : i = ⟨j, hj⟩ := Fin.ext (le_antisymm (Fin.mk_le_mk.mp hij) (Nat.le_of_not_lt hlt))
      heq ▸ id

/-- `composeMap` sends `C.elem i` to `C.elem j` under `M.minor`. -/
theorem minor_composeMap {M : Minion.{u}} {ℓ m : ℕ} (C : MinorChain M ℓ m)
    (i j : Fin (ℓ + 1)) (hij : i ≤ j) :
    M.minor (C.composeMap i j hij) (C.elem i) = C.elem j := by
  rcases j with ⟨j, hj⟩
  induction j with
  | zero =>
    have hi0 : i = ⟨0, hj⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Fin.mk_le_mk.mp hij))
    subst hi0
    rw [composeMap]
    simp only [lt_self_iff_false, ↓reduceDIte]
    exact M.minor_id _
  | succ j ih =>
    by_cases hlt : i.1 < j + 1
    · have hj' : j < ℓ := by omega
      have hij' : i ≤ ⟨j, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
      rw [composeMap]
      simp only [hlt, ↓reduceDIte]
      change M.minor (C.stepMap ⟨j, hj'⟩ ∘ C.composeMap i ⟨j, by omega⟩ hij') (C.elem i) =
        C.elem ⟨j + 1, hj⟩
      rw [M.minor_comp, ih (by omega) hij']
      exact C.step_minor ⟨j, hj'⟩
    · have hi_eq : i = ⟨j + 1, hj⟩ :=
        Fin.ext (le_antisymm (Fin.mk_le_mk.mp hij) (Nat.le_of_not_lt hlt))
      subst hi_eq
      rw [composeMap]
      simp only [lt_self_iff_false, ↓reduceDIte]
      exact M.minor_id _

end MinorChain

/-! #### Layered Label Cover construction for `npHard_pmc_of_chain_selector` -/

/-- Layer alphabet `Σ_i = (Fin i → γ) × (Fin (ℓ - i) → β)` of layer `i` (`0 ≤ i ≤ ℓ`). -/
private abbrev LayerSigma (ℓ : ℕ) (β γ : Type) (i : ℕ) : Type :=
  (Fin i → γ) × (Fin (ℓ - i) → β)

/-- Cardinality of `LayerSigma ℓ β γ i`. -/
private def cardLayerSigma (ℓ : ℕ) (β γ : Type) [Fintype β] [Fintype γ] (i : ℕ) : ℕ :=
  Fintype.card γ ^ i * Fintype.card β ^ (ℓ - i)

private theorem card_layerSigma_eq (ℓ : ℕ) (β γ : Type) [Fintype β] [Fintype γ] (i : ℕ) :
    Fintype.card (LayerSigma ℓ β γ i) = cardLayerSigma ℓ β γ i := by
  simp [LayerSigma, cardLayerSigma, Fintype.card_prod]

/-- Step projection from layer `i` to layer `i + 1` along a projection `π : β → γ`. -/
private def layerStepProj (ℓ : ℕ) {β γ : Type} (i : Fin ℓ) (π : β → γ)
    (x : LayerSigma ℓ β γ i.1) : LayerSigma ℓ β γ (i.1 + 1) :=
  (fun t => if ht : t.1 < i.1 then x.1 ⟨t.1, ht⟩ else π (x.2 ⟨0, by omega⟩),
   fun t => x.2 ⟨t.1 + 1, by omega⟩)

/-- Composed layer projection from layer `i` to layer `j` (`i ≤ j ≤ ℓ`) along a chain of
projections `πs : Fin ℓ → β → γ`. -/
private def layerCompProj (ℓ : ℕ) {β γ : Type} (πs : Fin ℓ → β → γ)
    (i j : Fin (ℓ + 1)) (hij : i ≤ j) (x : LayerSigma ℓ β γ i.1) : LayerSigma ℓ β γ j.1 :=
  (fun t =>
    if ht : t.1 < i.1 then x.1 ⟨t.1, ht⟩
    else πs ⟨t.1, by omega⟩ (x.2 ⟨t.1 - i.1, by omega⟩),
   fun t => x.2 ⟨t.1 + (j.1 - i.1), by omega⟩)

private theorem layerCompProj_step (ℓ : ℕ) {β γ : Type} (πs : Fin ℓ → β → γ)
    (i : Fin (ℓ + 1)) (j : Fin ℓ) (hij : i ≤ j.castSucc) (x : LayerSigma ℓ β γ i.1) :
    layerStepProj ℓ j (πs j) (layerCompProj ℓ πs i j.castSucc hij x) =
      layerCompProj ℓ πs i j.succ (hij.trans (Fin.le_of_lt j.castSucc_lt_succ)) x := by
  apply Prod.ext
  · funext t
    dsimp only [layerStepProj, layerCompProj]
    by_cases ht1 : t.1 < j.1
    · simp only [ht1, ↓reduceDIte]
    · simp only [ht1, ↓reduceDIte]
      have htj : t.1 = j.1 := by have := t.2; omega
      have hnoti : ¬ (t.1 < i.1) := by have := Fin.mk_le_mk.mp hij; omega
      simp only [hnoti, ↓reduceDIte]
      simp only [htj]
      exact congrArg (πs j) (congrArg x.2 (Fin.ext (by dsimp; omega)))
  · funext t
    dsimp only [layerStepProj, layerCompProj]
    exact congrArg x.2 (Fin.ext (by
      have := Fin.mk_le_mk.mp hij; simp only [Fin.val_castSucc, Fin.val_succ]; omega))

/-- Base-`B` encoding of an `ℓ`-tuple of natural numbers below `B`. -/
private def tupleToNat (B : ℕ) : ∀ k : ℕ, (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, v => v 0 + B * tupleToNat B k (Fin.tail v)

/-- Base-`B` decoding of a natural number into an `ℓ`-tuple. -/
private def natToTuple (B : ℕ) : ∀ k : ℕ, ℕ → (Fin k → ℕ)
  | 0, _ => Fin.elim0
  | k + 1, n => Fin.cons (n % B) (natToTuple B k (n / B))

private theorem tupleToNat_lt {B : ℕ} :
    ∀ (k : ℕ) (v : Fin k → ℕ), (∀ t, v t < B) → tupleToNat B k v < B ^ k
  | 0, _, _ => by simp [tupleToNat]
  | k + 1, v, hv => by
    have htail := tupleToNat_lt k (Fin.tail v) (fun t => hv t.succ)
    have h0 := hv 0
    have hB : 0 < B := Nat.zero_lt_of_lt h0
    dsimp only [tupleToNat]
    have h1 : v 0 + B * tupleToNat B k (Fin.tail v) < B * (tupleToNat B k (Fin.tail v) + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have h2 : B * (tupleToNat B k (Fin.tail v) + 1) ≤ B * B ^ k :=
      Nat.mul_le_mul_left B htail
    rw [pow_succ']
    exact lt_of_lt_of_le h1 h2

private theorem natToTuple_tupleToNat {B : ℕ} :
    ∀ (k : ℕ) (v : Fin k → ℕ), (∀ t, v t < B) → natToTuple B k (tupleToNat B k v) = v
  | 0, v, _ => funext fun t => Fin.elim0 t
  | k + 1, v, hv => by
    have h0 : v 0 < B := hv 0
    have hB : 0 < B := Nat.zero_lt_of_lt h0
    dsimp only [tupleToNat, natToTuple]
    have hmod : (v 0 + B * tupleToNat B k (Fin.tail v)) % B = v 0 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    have hdiv : (v 0 + B * tupleToNat B k (Fin.tail v)) / B = tupleToNat B k (Fin.tail v) := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h0, Nat.zero_add]
    rw [hmod, hdiv, natToTuple_tupleToNat k (Fin.tail v) (fun t => hv t.succ)]
    exact Fin.cons_self_tail v

/-- Maximum endpoint appearing in an edge list, plus `1`, bounded below by `g.vertices`. -/
private def graphVertexBound {C : Type} (g : Graph C) : ℕ :=
  max (max g.vertices 1)
    (g.edges.foldl (fun acc e => max acc (max e.src e.dst + 1)) 0)

private theorem src_dst_lt_graphVertexBound {C : Type} (g : Graph C) {e : Edge C}
    (he : e ∈ g.edges) : e.src < graphVertexBound g ∧ e.dst < graphVertexBound g := by
  have haux : ∀ (l : List (Edge C)) (acc : ℕ),
      (∀ d ∈ l, max d.src d.dst + 1 ≤
        l.foldl (fun a x => max a (max x.src x.dst + 1)) acc) := by
    intro l
    induction l with
    | nil => exact fun _ _ h => nomatch h
    | cons x xs ih =>
      intro acc d hd
      dsimp only [List.foldl_cons]
      have hacc : ∀ (l' : List (Edge C)) (a : ℕ),
          a ≤ l'.foldl (fun b y => max b (max y.src y.dst + 1)) a := by
        intro l'
        induction l' with
        | nil => exact fun _ => le_rfl
        | cons y ys ihy =>
          intro a; dsimp only [List.foldl_cons]
          exact (le_max_left a _).trans (ihy _)
      rcases List.mem_cons.mp hd with rfl | hd
      · exact (le_max_right acc _).trans (hacc xs _)
      · exact ih _ d hd
  have hle : max e.src e.dst + 1 ≤ graphVertexBound g :=
    (haux g.edges 0 e he).trans (le_max_right _ _)
  dsimp only [graphVertexBound] at hle ⊢
  omega

/-- All `k`-tuples of edges from a list `es`. -/
private def edgePowList {C : Type} : ∀ k : ℕ, List (Edge C) → List (Fin k → Edge C)
  | 0, _ => [Fin.elim0]
  | k + 1, es => es.flatMap fun e => (edgePowList k es).map fun rest => Fin.cons e rest

private theorem mem_edgePowList_iff {C : Type} {es : List (Edge C)} :
    ∀ {k : ℕ} {d : Fin k → Edge C}, d ∈ edgePowList k es ↔ ∀ t, d t ∈ es
  | 0, d => by
    simp only [edgePowList, List.mem_singleton]
    exact ⟨fun h t => Fin.elim0 t, fun _ => funext fun t => Fin.elim0 t⟩
  | k + 1, d => by
    simp only [edgePowList, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨e, he, rest, hrest, rfl⟩ t
      refine Fin.cases he (fun s => (mem_edgePowList_iff.mp hrest) s) t
    · intro hd
      refine ⟨d 0, hd 0, Fin.tail d, mem_edgePowList_iff.mpr fun s => hd s.succ,
        Fin.cons_self_tail d⟩

/-- The layer-`i` vertex tuple `(d_0.dst, ..., d_{i-1}.dst, d_i.src, ..., d_{ℓ-1}.src)` of a
chain of edges `d`. -/
private def chainVertex {C : Type} (ℓ : ℕ) (i : ℕ) (d : Fin ℓ → Edge C) : Fin ℓ → ℕ :=
  fun t => if t.1 < i then (d t).dst else (d t).src

/-- Build the `ℓ`-layered bipartite minor condition from a Label Cover instance `g`. -/
private noncomputable def lcToMinorCond (ℓ m : ℕ) {β γ : Type} [Fintype β] [Fintype γ]
    (g : Graph (β → γ)) : MinorCondition m :=
  let B := graphVertexBound g
  let layerSize := B ^ ℓ
  let eSig : ∀ i : ℕ, LayerSigma ℓ β γ i ≃ Fin (cardLayerSigma ℓ β γ i) :=
    fun i => Fintype.equivFinOfCardEq (card_layerSigma_eq ℓ β γ i)
  let arities : List ℕ :=
    (List.range (ℓ + 1)).flatMap fun i => List.replicate layerSize (cardLayerSigma ℓ β γ i)
  let idConstraints : List MinorConstraint :=
    (List.range (ℓ + 1)).flatMap fun i =>
      (List.range layerSize).map fun v =>
        { leftIdx := i * layerSize + v
          rightIdx := i * layerSize + v
          map := List.range (cardLayerSigma ℓ β γ i) }
  let chainConstraints : List MinorConstraint :=
    (edgePowList ℓ g.edges).flatMap fun d =>
      (List.ofFn fun i : Fin ℓ => i).map fun i =>
        let vi := tupleToNat B ℓ (chainVertex ℓ i.1 d)
        let vj := tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) d)
        { leftIdx := i.1 * layerSize + vi
          rightIdx := (i.1 + 1) * layerSize + vj
          map := List.ofFn fun x : Fin (cardLayerSigma ℓ β γ i.1) =>
            (eSig (i.1 + 1) (layerStepProj ℓ i (d i).constraint ((eSig i.1).symm x))).1 }
  { leftArities := arities
    rightArities := arities
    constraints := idConstraints ++ chainConstraints }

private theorem computableInPolyTime_graphVertexBound {C : Type} (encC : C ↪ List Bool) :
    ComputableInPolyTime (graphVertexBound (C := C)) (Graph.encoding encC) encUnary := by
  have hstep : ComputableInPolyTime
      (fun p : ℕ × Edge C => max p.1 (max p.2.src p.2.dst + 1))
      (encPair encUnary (Edge.encoding encC)) encUnary := by fun_prop
  have hfold : ComputableInPolyTime
      (fun g : Graph C => g.edges.foldl (fun acc e => max acc (max e.src e.dst + 1)) 0)
      (Graph.encoding encC) encUnary := by
    refine ComputableInPolyTime.foldl'
      (encA := Edge.encoding encC) (encB := encUnary) (encL := encList (Edge.encoding encC))
      (list := Graph.edges) (init := fun _ => 0)
      (step := fun acc e => max acc (max e.src e.dst + 1))
      (by fun_prop) (.const 0) hstep
      (B := fun g => (Graph.encoding encC g).length + 1)
      (PolyBounded.self.add (.const 1)) ?_
    intro g i _
    simp only [encUnary_apply, List.length_replicate]
    have haux : ∀ (l : List (Edge C)) (acc : ℕ), acc ≤ (Graph.encoding encC g).length + 1 →
        (∀ e ∈ l, max e.src e.dst + 1 ≤ (Graph.encoding encC g).length + 1) →
        l.foldl (fun a e => max a (max e.src e.dst + 1)) acc ≤
          (Graph.encoding encC g).length + 1 := by
      intro l
      induction l with
      | nil => exact fun _ h _ => h
      | cons x xs ih =>
        intro acc hacc hl
        dsimp only [List.foldl_cons]
        exact ih _ (max_le hacc (hl x List.mem_cons_self))
          (fun e he => hl e (List.mem_cons_of_mem _ he))
    refine haux _ 0 (by omega) fun e he => ?_
    have hmem : e ∈ g.edges := List.mem_of_mem_take he
    have he1 := SizedListEncoding.length_elem_le (encA := Edge.encoding encC)
      (encL := encList (Edge.encoding encC)) g.edges e hmem
    have he2 : (encList (Edge.encoding encC) g.edges).length ≤ (Graph.encoding encC g).length := by
      change (encList (Edge.encoding encC) g.edges).length ≤
        (encPair encUnary (encList (Edge.encoding encC)) (g.vertices, g.edges)).length
      enc_len
    have hlen_e := Edge.length_encoding (enc := encC) e
    omega
  unfold graphVertexBound
  exact ComputableInPolyTime.unary_max.comp
    ((ComputableInPolyTime.unary_max.comp ((Graph.isPolyTime_vertices .id').prod (.const 1))).prod
      hfold)

private theorem computableInPolyTime_tupleToNat (k : ℕ) :
    ComputableInPolyTime (fun p : ℕ × (Fin k → ℕ) => tupleToNat p.1 k p.2)
      (encPair encUnary (encFinFn k encUnary)) encUnary := by
  induction k with
  | zero => exact .const 0
  | succ k ih =>
    dsimp only [tupleToNat]
    have h0 : ComputableInPolyTime (fun p : ℕ × (Fin (k + 1) → ℕ) => p.2 0)
        (encPair encUnary (encFinFn (k + 1) encUnary)) encUnary :=
      (ComputableInPolyTime.finFn_apply encUnary 0).comp (ComputableInPolyTime.snd _ _)
    have htail : ComputableInPolyTime (fun p : ℕ × (Fin (k + 1) → ℕ) => Fin.tail p.2)
        (encPair encUnary (encFinFn (k + 1) encUnary)) (encFinFn k encUnary) := by
      refine ComputableInPolyTime.finFn fun i => ?_
      exact (ComputableInPolyTime.finFn_apply encUnary i.succ).comp (ComputableInPolyTime.snd _ _)
    exact ComputableInPolyTime.unary_add.comp
      (h0.prod (ComputableInPolyTime.unary_mul.comp
        ((ComputableInPolyTime.fst _ _).prod
          (ih.comp ((ComputableInPolyTime.fst _ _).prod htail)))))

private theorem computableInPolyTime_edgePowList {C : Type} (encC : C ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime (edgePowList (C := C) k)
      (encList (Edge.encoding encC)) (encList (encFinFn k (Edge.encoding encC))) := by
  induction k with
  | zero => exact .const [Fin.elim0]
  | succ k ih =>
    dsimp only [edgePowList]
    refine ComputableInPolyTime.flatMapWithInput .id' ?_
    refine ComputableInPolyTime.mapWithInput (ih.comp (ComputableInPolyTime.fst _ _)) ?_
    refine ComputableInPolyTime.finFn fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
    · exact (ComputableInPolyTime.finFn_apply (Edge.encoding encC) j).comp
        (ComputableInPolyTime.snd _ _)

private theorem computableInPolyTime_lcToMinorCond (ℓ m : ℕ) {β γ : Type} [Fintype β] [Fintype γ]
    (encG : γ ↪ List Bool) :
    ComputableInPolyTime (lcToMinorCond ℓ m (β := β) (γ := γ))
      (Graph.encoding (encPi encG)) (encMinorCondition m) := by
  let eSig : ∀ i : ℕ, LayerSigma ℓ β γ i ≃ Fin (cardLayerSigma ℓ β γ i) :=
    fun i => Fintype.equivFinOfCardEq (card_layerSigma_eq ℓ β γ i)
  have hB : ComputableInPolyTime (graphVertexBound (C := β → γ))
      (Graph.encoding (encPi encG)) encUnary :=
    computableInPolyTime_graphVertexBound (encPi encG)
  have hLS : ComputableInPolyTime (fun g : Graph (β → γ) => graphVertexBound g ^ ℓ)
      (Graph.encoding (encPi encG)) encUnary :=
    (ComputableInPolyTime.unary_pow ℓ).comp hB
  have harities : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (List.range (ℓ + 1)).flatMap fun i =>
          List.replicate (graphVertexBound g ^ ℓ) (cardLayerSigma ℓ β γ i))
      (Graph.encoding (encPi encG)) (encList encUnary) := by
    refine ComputableInPolyTime.flatMapConst (List.range (ℓ + 1)) fun i _ => ?_
    exact ComputableInPolyTime.replicate hLS (.const _)
  have hid : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (List.range (ℓ + 1)).flatMap fun i =>
          (List.range (graphVertexBound g ^ ℓ)).map fun v =>
            MinorConstraint.mk (i * graphVertexBound g ^ ℓ + v) (i * graphVertexBound g ^ ℓ + v)
              (List.range (cardLayerSigma ℓ β γ i)))
      (Graph.encoding (encPi encG)) (encList encMinorConstraint) := by
    refine ComputableInPolyTime.flatMapConst (List.range (ℓ + 1)) fun i _ => ?_
    refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
    have hLS' := hLS.comp (ComputableInPolyTime.fst (Graph.encoding (encPi encG)) encUnary)
    have hv : ComputableInPolyTime (fun p : Graph (β → γ) × ℕ => p.2)
        (encPair (Graph.encoding (encPi encG)) encUnary) encUnary := by fun_prop
    have hidx : ComputableInPolyTime
        (fun p : Graph (β → γ) × ℕ => i * graphVertexBound p.1 ^ ℓ + p.2)
        (encPair (Graph.encoding (encPi encG)) encUnary) encUnary := by fun_prop
    exact encMinorConstraint_mk_polyTime hidx hidx (.const _)
  have hchain : ComputableInPolyTime
      (fun g : Graph (β → γ) =>
        (edgePowList ℓ g.edges).flatMap fun d =>
          (List.ofFn fun i : Fin ℓ => i).map fun i =>
            MinorConstraint.mk
              (i.1 * graphVertexBound g ^ ℓ +
                tupleToNat (graphVertexBound g) ℓ (chainVertex ℓ i.1 d))
              ((i.1 + 1) * graphVertexBound g ^ ℓ +
                tupleToNat (graphVertexBound g) ℓ (chainVertex ℓ (i.1 + 1) d))
              (List.ofFn fun x : Fin (cardLayerSigma ℓ β γ i.1) =>
                (eSig (i.1 + 1)
                  (layerStepProj ℓ i (d i).constraint ((eSig i.1).symm x))).1))
      (Graph.encoding (encPi encG)) (encList encMinorConstraint) := by
    refine ComputableInPolyTime.flatMapWithInput
      ((computableInPolyTime_edgePowList (encPi encG) ℓ).comp (Graph.isPolyTime_edges .id')) ?_
    refine ComputableInPolyTime.mapConst (List.ofFn fun i : Fin ℓ => i) fun i _ => ?_
    have hB' := hB.comp (ComputableInPolyTime.fst (Graph.encoding (encPi (Index := β) encG))
      (encFinFn ℓ (Edge.encoding (encPi (Index := β) encG))))
    have hLS' := hLS.comp (ComputableInPolyTime.fst (Graph.encoding (encPi (Index := β) encG))
      (encFinFn ℓ (Edge.encoding (encPi (Index := β) encG))))
    have hcv (j : ℕ) : ComputableInPolyTime
        (fun p : Graph (β → γ) × (Fin ℓ → Edge (β → γ)) => chainVertex ℓ j p.2)
        (encPair (Graph.encoding (encPi encG)) (encFinFn ℓ (Edge.encoding (encPi encG))))
        (encFinFn ℓ encUnary) := by
      refine ComputableInPolyTime.finFn fun t => ?_
      dsimp only [chainVertex]
      split_ifs
      · exact (Edge.isPolyTime_dst
          ((ComputableInPolyTime.finFn_apply (Edge.encoding (encPi encG)) t).comp
            (ComputableInPolyTime.snd _ _)))
      · exact (Edge.isPolyTime_src
          ((ComputableInPolyTime.finFn_apply (Edge.encoding (encPi encG)) t).comp
            (ComputableInPolyTime.snd _ _)))
    have hvi : ComputableInPolyTime
        (fun p : Graph (β → γ) × (Fin ℓ → Edge (β → γ)) =>
          i.1 * graphVertexBound p.1 ^ ℓ +
            tupleToNat (graphVertexBound p.1) ℓ (chainVertex ℓ i.1 p.2))
        (encPair (Graph.encoding (encPi encG)) (encFinFn ℓ (Edge.encoding (encPi encG))))
        encUnary :=
      ComputableInPolyTime.unary_add.comp
        ((ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const i.1).prod hLS')).prod
          ((computableInPolyTime_tupleToNat ℓ).comp (hB'.prod (hcv i.1))))
    have hvj : ComputableInPolyTime
        (fun p : Graph (β → γ) × (Fin ℓ → Edge (β → γ)) =>
          (i.1 + 1) * graphVertexBound p.1 ^ ℓ +
            tupleToNat (graphVertexBound p.1) ℓ (chainVertex ℓ (i.1 + 1) p.2))
        (encPair (Graph.encoding (encPi encG)) (encFinFn ℓ (Edge.encoding (encPi encG))))
        encUnary :=
      ComputableInPolyTime.unary_add.comp
        ((ComputableInPolyTime.unary_mul.comp
            ((ComputableInPolyTime.const (i.1 + 1)).prod hLS')).prod
          ((computableInPolyTime_tupleToNat ℓ).comp (hB'.prod (hcv (i.1 + 1)))))
    have hmp : ComputableInPolyTime
        (fun p : Graph (β → γ) × (Fin ℓ → Edge (β → γ)) =>
          List.ofFn fun x : Fin (cardLayerSigma ℓ β γ i.1) =>
            (eSig (i.1 + 1) (layerStepProj ℓ i (p.2 i).constraint ((eSig i.1).symm x))).1)
        (encPair (Graph.encoding (encPi encG)) (encFinFn ℓ (Edge.encoding (encPi encG))))
        (encList encUnary) := by
      have hcon : ComputableInPolyTime
          (fun p : Graph (β → γ) × (Fin ℓ → Edge (β → γ)) => (p.2 i).constraint)
          (encPair (Graph.encoding (encPi encG)) (encFinFn ℓ (Edge.encoding (encPi encG))))
          (encPi encG) :=
        Edge.isPolyTime_constraint
          ((ComputableInPolyTime.finFn_apply (Edge.encoding (encPi encG)) i).comp
            (ComputableInPolyTime.snd _ _))
      have hfin : ComputableInPolyTime
          (fun π : β → γ =>
            List.ofFn fun x : Fin (cardLayerSigma ℓ β γ i.1) =>
              (eSig (i.1 + 1) (layerStepProj ℓ i π ((eSig i.1).symm x))).1)
          (encPi encG) (encList encUnary) := .of_finite _
      exact hfin.comp hcon
    exact encMinorConstraint_mk_polyTime hvi hvj hmp
  exact encMinorCondition_mk_polyTime harities harities
    ((ComputableInPolyTime.listAppend encMinorConstraint).comp (hid.prod hchain))

private theorem length_flatMap_range_replicate {α : Type*} (f : ℕ → α) (m n : ℕ) :
    ((List.range n).flatMap fun k => List.replicate m (f k)).length = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      List.length_replicate, Nat.succ_mul]

private theorem getElem?_flatMap_range_replicate {α : Type*} (f : ℕ → α) {m n i v : ℕ}
    (hi : i < n) (hv : v < m) :
    ((List.range n).flatMap fun k => List.replicate m (f k))[i * m + v]? = some (f i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen_l := length_flatMap_range_replicate f m n
    by_cases hin : i < n
    · have hlt' : i * m + v < n * m := by
        have h1 : i * m + v < (i + 1) * m := by rw [Nat.add_mul, Nat.one_mul]; omega
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right m hin)
      rw [List.getElem?_append_left (hlen_l ▸ hlt')]
      exact ih hin
    · have hieq : i = n := by omega
      subst hieq
      rw [List.getElem?_append_right (by omega), hlen_l]
      have hsub : i * m + v - i * m = v := by omega
      rw [hsub, List.getElem?_replicate]
      simp [hv]

private theorem lcToMinorCond_wellFormed (ℓ m : ℕ) {β γ : Type} [Fintype β] [Fintype γ]
    (hm : ∀ i ≤ ℓ, cardLayerSigma ℓ β γ i ≤ m) (g : Graph (β → γ)) :
    (lcToMinorCond ℓ m g).WellFormed := by
  let B := graphVertexBound g
  let layerSize := B ^ ℓ
  have hB_pos : 0 < B :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hLS_pos : 0 < layerSize := Nat.pow_pos hB_pos
  have harity_len : (lcToMinorCond ℓ m g).leftArities.length = (ℓ + 1) * layerSize :=
    length_flatMap_range_replicate (cardLayerSigma ℓ β γ) layerSize (ℓ + 1)
  have harity_getD : ∀ i v, i < ℓ + 1 → v < layerSize →
      (lcToMinorCond ℓ m g).leftArities.getD (i * layerSize + v) 0 = cardLayerSigma ℓ β γ i := by
    intro i v hi hv
    dsimp only [lcToMinorCond]
    rw [List.getD_eq_getElem?_getD,
      getElem?_flatMap_range_replicate (cardLayerSigma ℓ β γ) hi hv]
    rfl
  have hmem_arity : ∀ p ∈ (lcToMinorCond ℓ m g).leftArities, p ≤ m := by
    intro p hp
    dsimp only [lcToMinorCond] at hp
    rw [List.mem_flatMap] at hp
    obtain ⟨i, hi, hrep⟩ := hp
    rw [List.mem_replicate] at hrep
    exact hrep.2 ▸ hm i (by have := List.mem_range.mp hi; omega)
  have hlr : (lcToMinorCond ℓ m g).rightArities = (lcToMinorCond ℓ m g).leftArities := rfl
  refine ⟨hmem_arity, hmem_arity, fun c hc => ?_⟩
  dsimp only [lcToMinorCond] at hc
  rcases List.mem_append.mp hc with hid | hch
  · rw [List.mem_flatMap] at hid
    obtain ⟨i, hi, hmap⟩ := hid
    rw [List.mem_map] at hmap
    obtain ⟨v, hv, rfl⟩ := hmap
    have hi' : i < ℓ + 1 := List.mem_range.mp hi
    have hv' : v < layerSize := List.mem_range.mp hv
    have hlt : i * layerSize + v < (ℓ + 1) * layerSize := by
      have h1 : i * layerSize + v < (i + 1) * layerSize := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize hi')
    have hget : (lcToMinorCond ℓ m g).leftArities.getD (i * layerSize + v) 0 =
        cardLayerSigma ℓ β γ i := harity_getD i v hi' hv'
    refine ⟨harity_len.symm ▸ hlt, hlr ▸ harity_len.symm ▸ hlt, ?_, ?_⟩
    · dsimp only; rw [hget, List.length_range]
    · intro k hk
      dsimp only at hk ⊢
      rw [hlr, hget, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_range]
      simpa using hk
  · rw [List.mem_flatMap] at hch
    obtain ⟨d, hd, hmap⟩ := hch
    rw [List.mem_map] at hmap
    obtain ⟨i, _, rfl⟩ := hmap
    have hd_mem := mem_edgePowList_iff.mp hd
    have hvi : tupleToNat B ℓ (chainVertex ℓ i.1 d) < layerSize := by
      refine tupleToNat_lt ℓ _ fun t => ?_
      have hsd := src_dst_lt_graphVertexBound g (hd_mem t)
      dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]
    have hvj : tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) d) < layerSize := by
      refine tupleToNat_lt ℓ _ fun t => ?_
      have hsd := src_dst_lt_graphVertexBound g (hd_mem t)
      dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]
    have hlti : i.1 * layerSize + tupleToNat B ℓ (chainVertex ℓ i.1 d) < (ℓ + 1) * layerSize := by
      have h1 : i.1 * layerSize + tupleToNat B ℓ (chainVertex ℓ i.1 d) < (i.1 + 1) * layerSize := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize (by omega))
    have hltj : (i.1 + 1) * layerSize + tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) d) <
        (ℓ + 1) * layerSize := by
      have h1 : (i.1 + 1) * layerSize + tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) d) <
          (i.1 + 2) * layerSize := by
        have h2 : (i.1 + 2) * layerSize = (i.1 + 1) * layerSize + layerSize := by ring
        omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize (by omega))
    have hgeti := harity_getD i.1 _ (by omega) hvi
    have hgetj := harity_getD (i.1 + 1) _ (by omega) hvj
    refine ⟨harity_len.symm ▸ hlti, hlr ▸ harity_len.symm ▸ hltj, ?_, ?_⟩
    · dsimp only
      change (List.ofFn _).length = (lcToMinorCond ℓ m g).leftArities.getD
        (i.1 * layerSize + tupleToNat B ℓ (chainVertex ℓ i.1 d)) 0
      rw [hgeti, List.length_ofFn]
    · intro k hk
      dsimp only at hk ⊢
      simp only [List.length_ofFn] at hk
      change (List.ofFn _).getD k 0 < (lcToMinorCond ℓ m g).leftArities.getD
        ((i.1 + 1) * layerSize + tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) d)) 0
      rw [hgetj, List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
      exact Fin.is_lt _

private theorem chain_delta_bound (ℓ k p : ℕ) (hp : p ≤ (ℓ + 1) ^ 2) :
    (p : ℝ) * ((k : ℝ) ^ 2 *
      (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1)))) < 1 := by
  have hp' : (p : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hp
  have hk_le : (k : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    nlinarith
  have hnum_le : (p : ℝ) * (k : ℝ) ^ 2 ≤
      ((ℓ + 1 : ℕ) : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 :=
    mul_le_mul hp' hk_le (by positivity) (by positivity)
  have hden_pos : 0 < 2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1) := by positivity
  calc (p : ℝ) * ((k : ℝ) ^ 2 *
        (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1))))
      = ((p : ℝ) * (k : ℝ) ^ 2) /
          (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1)) := by ring
    _ ≤ (((ℓ + 1 : ℕ) : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2) /
          (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1)) :=
        div_le_div_of_nonneg_right hnum_le hden_pos.le
    _ < 1 := by
        rw [div_lt_one hden_pos]
        nlinarith

private theorem lcToMinorCond_completeness (ℓ m : ℕ) {β γ : Type} [Fintype β] [Fintype γ]
    [DecidableEq γ] (hm_bound : ∀ i ≤ ℓ, cardLayerSigma ℓ β γ i ≤ m)
    (M : Minion.{u}) (hM : Nonempty (M.carrier 1))
    (g : Graph (β → γ)) (hsat_lc : (g.toGraph projectionEval).Satisfiable) :
    lcToMinorCond ℓ m g ∈ (pmc (m := m) M hM).yes := by
  obtain ⟨labL, labR, hlab⟩ := (satisfiable_toGraph_projectionEval_iff g).mp hsat_lc
  let B := graphVertexBound g
  let layerSize := B ^ ℓ
  let eSig : ∀ i : ℕ, LayerSigma ℓ β γ i ≃ Fin (cardLayerSigma ℓ β γ i) :=
    fun i => Fintype.equivFinOfCardEq (card_layerSigma_eq ℓ β γ i)
  let asgn (idx : ℕ) : ℕ :=
    let i := idx / layerSize
    let v := natToTuple B ℓ (idx % layerSize)
    if hi : i < ℓ + 1 then
      (eSig i (fun t : Fin i => labR (v ⟨t.1, by omega⟩),
               fun t : Fin (ℓ - i) => labL (v ⟨i + t.1, by omega⟩))).1
    else 0
  have hWF := lcToMinorCond_wellFormed ℓ m hm_bound g
  have hB_pos : 0 < B :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hLS_pos : 0 < layerSize := Nat.pow_pos hB_pos
  have hlen : (lcToMinorCond ℓ m g).leftArities.length = (ℓ + 1) * layerSize :=
    length_flatMap_range_replicate (cardLayerSigma ℓ β γ) layerSize (ℓ + 1)
  have hgetD_arity : ∀ i v, i < ℓ + 1 → v < layerSize →
      (lcToMinorCond ℓ m g).leftArities.getD (i * layerSize + v) 0 = cardLayerSigma ℓ β γ i := by
    intro i v hi hv
    dsimp only [lcToMinorCond]
    rw [List.getD_eq_getElem?_getD,
      getElem?_flatMap_range_replicate (cardLayerSigma ℓ β γ) hi hv]
    rfl
  have hasgn_lt : ∀ idx < (lcToMinorCond ℓ m g).leftArities.length,
      asgn idx < (lcToMinorCond ℓ m g).leftArities.getD idx 0 := by
    intro idx hidx
    rw [hlen] at hidx
    have hi : idx / layerSize < ℓ + 1 := (Nat.div_lt_iff_lt_mul hLS_pos).mpr hidx
    have hv : idx % layerSize < layerSize := Nat.mod_lt idx hLS_pos
    have hdecomp : idx / layerSize * layerSize + idx % layerSize = idx := by
      rw [Nat.mul_comm, Nat.div_add_mod]
    conv_rhs => rw [← hdecomp, hgetD_arity (idx / layerSize) (idx % layerSize) hi hv]
    dsimp only [asgn]
    simp only [hi, ↓reduceDIte]
    exact Fin.is_lt _
  rw [mem_yes_pmc]
  refine ⟨hWF, asgn, asgn, hasgn_lt, hasgn_lt, fun c hc => ?_⟩
  dsimp only [lcToMinorCond] at hc
  rcases List.mem_append.mp hc with hid | hch
  · rw [List.mem_flatMap] at hid
    obtain ⟨i, hi, hmap⟩ := hid
    rw [List.mem_map] at hmap
    obtain ⟨v, hv, rfl⟩ := hmap
    have hi' : i < ℓ + 1 := List.mem_range.mp hi
    have hv' : v < layerSize := List.mem_range.mp hv
    have hlt : asgn (i * layerSize + v) < cardLayerSigma ℓ β γ i := by
      have h1 := hasgn_lt (i * layerSize + v) (by
        rw [hlen]
        have h2 : i * layerSize + v < (i + 1) * layerSize := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        exact lt_of_lt_of_le h2 (Nat.mul_le_mul_right layerSize hi'))
      rwa [hgetD_arity i v hi' hv'] at h1
    dsimp only
    rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hlt), List.getElem_range]
  · rw [List.mem_flatMap] at hch
    obtain ⟨d, hd, hmap⟩ := hch
    rw [List.mem_map] at hmap
    obtain ⟨i, _, rfl⟩ := hmap
    have hd_mem := mem_edgePowList_iff.mp hd
    have hvi_lt : ∀ t, chainVertex ℓ i.1 d t < B := fun t => by
      have hsd := src_dst_lt_graphVertexBound g (hd_mem t)
      dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]
    have hvj_lt : ∀ t, chainVertex ℓ (i.1 + 1) d t < B := fun t => by
      have hsd := src_dst_lt_graphVertexBound g (hd_mem t)
      dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]
    have hasgn_at : ∀ (k : ℕ) (hk : k < ℓ + 1) (w : Fin ℓ → ℕ) (hw : ∀ t, w t < B),
        asgn (k * layerSize + tupleToNat B ℓ w) =
          (eSig k (fun t : Fin k => labR (w ⟨t.1, by omega⟩),
                   fun t : Fin (ℓ - k) => labL (w ⟨k + t.1, by omega⟩))).1 := by
      intro k hk w hw
      have hlt_w : tupleToNat B ℓ w < layerSize := tupleToNat_lt ℓ w hw
      have hdiv : (k * layerSize + tupleToNat B ℓ w) / layerSize = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hLS_pos, Nat.div_eq_of_lt hlt_w, Nat.zero_add]
      have hmod : (k * layerSize + tupleToNat B ℓ w) % layerSize = tupleToNat B ℓ w := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt_w]
      have h1 : (k * layerSize + tupleToNat B ℓ w) / layerSize < ℓ + 1 := by omega
      dsimp only [asgn]
      rw [hmod, natToTuple_tupleToNat ℓ w hw]
      simp only [h1, ↓reduceDIte]
      have hfun : ∀ (a b : ℕ) (ha : a < ℓ + 1) (hb : b < ℓ + 1), a = b →
          (eSig a (fun t : Fin a => labR (w ⟨t.1, by omega⟩),
                   fun t : Fin (ℓ - a) => labL (w ⟨a + t.1, by omega⟩))).1 =
          (eSig b (fun t : Fin b => labR (w ⟨t.1, by omega⟩),
                   fun t : Fin (ℓ - b) => labL (w ⟨b + t.1, by omega⟩))).1 := by
        rintro a _ _ _ rfl; rfl
      exact hfun _ k h1 hk hdiv
    change (List.ofFn _).getD (asgn (i.1 * layerSize + tupleToNat B ℓ (chainVertex ℓ i.1 d))) 0 =
      asgn ((i.1 + 1) * layerSize + tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) d))
    rw [hasgn_at i.1 (by omega) _ hvi_lt, hasgn_at (i.1 + 1) (by omega) _ hvj_lt]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact Fin.is_lt _), List.getElem_ofFn]
    dsimp only [eSig]
    simp only [Fin.eta, Equiv.symm_apply_apply]
    congr 1; congr 1
    apply Prod.ext
    · funext t
      dsimp only [layerStepProj, chainVertex]
      have h1 : t.1 < i.1 + 1 := t.2
      by_cases ht : t.1 < i.1
      · simp only [ht, h1, ↓reduceDIte, ↓reduceIte]
      · have hteq : t.1 = i.1 := by omega
        have h2 : ¬ (i.1 + 0 < i.1) := by omega
        simp only [ht, h1, h2, ↓reduceDIte, ↓reduceIte]
        have hfin : (⟨i.1 + 0, by omega⟩ : Fin ℓ) = i := Fin.ext (Nat.add_zero _)
        have hfin' : (⟨t.1, by omega⟩ : Fin ℓ) = i := Fin.ext hteq
        rw [hfin, hfin']
        exact hlab (d i) (hd_mem i)
    · funext t
      dsimp only [layerStepProj, chainVertex]
      have h1 : ¬ (i.1 + (t.1 + 1) < i.1) := by omega
      have h2 : ¬ (i.1 + 1 + t.1 < i.1 + 1) := by omega
      simp only [h1, h2, ↓reduceIte]
      exact congrArg (fun k => labL (d k).src) (Fin.ext (by dsimp; omega))

private noncomputable def lcGoodSet (ℓ : ℕ) {β γ : Type} (g : Graph (β → γ))
    (S : ∀ i : Fin (ℓ + 1), Fin ((graphVertexBound g) ^ ℓ) → Finset (LayerSigma ℓ β γ i.1))
    (i j : Fin (ℓ + 1)) (hij : i < j) : Finset (Fin ℓ → Fin g.edges.length) :=
  @Finset.filter _ (fun d =>
    let de : Fin ℓ → Edge (β → γ) := fun t => g.edges[d t]
    let vi : Fin ((graphVertexBound g) ^ ℓ) :=
      ⟨tupleToNat (graphVertexBound g) ℓ (chainVertex ℓ i.1 de), tupleToNat_lt ℓ _ fun t => by
        have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
        dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
    let vj : Fin ((graphVertexBound g) ^ ℓ) :=
      ⟨tupleToNat (graphVertexBound g) ℓ (chainVertex ℓ j.1 de), tupleToNat_lt ℓ _ fun t => by
        have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
        dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
    ∃ a ∈ S i vi, layerCompProj ℓ (fun t => (de t).constraint) i j (le_of_lt hij) a ∈ S j vj)
    (Classical.decPred _) Finset.univ

private theorem mem_lcGoodSet_iff (ℓ : ℕ) {β γ : Type} (g : Graph (β → γ))
    (S : ∀ i : Fin (ℓ + 1), Fin ((graphVertexBound g) ^ ℓ) → Finset (LayerSigma ℓ β γ i.1))
    (i j : Fin (ℓ + 1)) (hij : i < j) (d : Fin ℓ → Fin g.edges.length) :
    d ∈ lcGoodSet ℓ g S i j hij ↔
      let de : Fin ℓ → Edge (β → γ) := fun t => g.edges[d t]
      let vi : Fin ((graphVertexBound g) ^ ℓ) :=
        ⟨tupleToNat (graphVertexBound g) ℓ (chainVertex ℓ i.1 de), tupleToNat_lt ℓ _ fun t => by
          have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
          dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
      let vj : Fin ((graphVertexBound g) ^ ℓ) :=
        ⟨tupleToNat (graphVertexBound g) ℓ (chainVertex ℓ j.1 de), tupleToNat_lt ℓ _ fun t => by
          have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
          dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
      ∃ a ∈ S i vi,
        layerCompProj ℓ (fun t => (de t).constraint) i j (le_of_lt hij) a ∈ S j vj := by
  classical
  simp [lcGoodSet]

private theorem lcToMinorCond_good_bound (ℓ k : ℕ) {β γ : Type}
    [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (g : Graph (β → γ)) (δ : ℝ)
    (hval_le : 1 - (g.toGraph projectionEval).unsatVal ≤ δ)
    (S : ∀ i : Fin (ℓ + 1), Fin ((graphVertexBound g) ^ ℓ) → Finset (LayerSigma ℓ β γ i.1))
    (hS_card : ∀ i v, (S i v).card ≤ k)
    (i j : Fin (ℓ + 1)) (hij : i < j) :
    ((lcGoodSet ℓ g S i j hij).card : ℝ) ≤ (k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ := by
  classical
  let B := graphVertexBound g
  let layerSize := B ^ ℓ
  let E := Fin g.edges.length
  let Good := lcGoodSet ℓ g S i j hij
  change (Good.card : ℝ) ≤ (k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ
  have hB_pos : 0 < B :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hLS_pos : 0 < layerSize := Nat.pow_pos hB_pos
  let i0 : Fin ℓ := ⟨i.1, by omega⟩
  -- Decompose `Fin ℓ → E` into `(other coords) × (coord i0)`.
  let eSplit : (Fin ℓ → E) ≃ ({t : Fin ℓ // t ≠ i0} → E) × E :=
    { toFun := fun d => (fun t => d t.1, d i0)
      invFun := fun p t => if h : t = i0 then p.2 else p.1 ⟨t, h⟩
      left_inv := fun d => funext fun t => by
        dsimp only; split_ifs with h <;> [exact h ▸ rfl; rfl]
      right_inv := fun p => Prod.ext (funext fun t => by simp [t.2]) (by simp) }
  -- For each fixed `d_{-i0}`, bound good `e : E` by `k^2 * δ * |E|`.
  have hslice : ∀ rest : {t : Fin ℓ // t ≠ i0} → E,
      ((Finset.univ.filter fun e : E => eSplit.symm (rest, e) ∈ Good).card : ℝ) ≤
        (k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) := by
    intro rest
    have hcover_opt : ∀ {α : Type} (T : Finset α), T.card ≤ k →
        ∃ pick : Fin k → Option α, ∀ a ∈ T, ∃ p : Fin k, pick p = some a := by
      intro α T hT
      let eT := T.equivFin
      refine ⟨fun p => if hp : p.1 < T.card then some (eT.symm ⟨p.1, hp⟩).1 else none, ?_⟩
      intro a ha
      refine ⟨⟨(eT ⟨a, ha⟩).1, lt_of_lt_of_le (eT ⟨a, ha⟩).2 hT⟩, ?_⟩
      simp [(eT ⟨a, ha⟩).2]
    let vLeft (u : ℕ) : Fin layerSize :=
      if hu : u < B then
        ⟨tupleToNat B ℓ fun t =>
          if h : t = i0 then u
          else if t.1 < i.1 then (g.edges[rest ⟨t, h⟩]).dst
          else (g.edges[rest ⟨t, h⟩]).src,
         tupleToNat_lt ℓ _ fun t => by
           split_ifs with h1 h2
           · exact hu
           · exact (src_dst_lt_graphVertexBound g (List.getElem_mem (rest ⟨t, h1⟩).2)).2
           · exact (src_dst_lt_graphVertexBound g (List.getElem_mem (rest ⟨t, h1⟩).2)).1⟩
      else ⟨0, hLS_pos⟩
    let vRight (w : ℕ) : Fin layerSize :=
      if hw : w < B then
        ⟨tupleToNat B ℓ fun t =>
          if h : t = i0 then w
          else if t.1 < j.1 then (g.edges[rest ⟨t, h⟩]).dst
          else (g.edges[rest ⟨t, h⟩]).src,
         tupleToNat_lt ℓ _ fun t => by
           split_ifs with h1 h2
           · exact hw
           · exact (src_dst_lt_graphVertexBound g (List.getElem_mem (rest ⟨t, h1⟩).2)).2
           · exact (src_dst_lt_graphVertexBound g (List.getElem_mem (rest ⟨t, h1⟩).2)).1⟩
      else ⟨0, hLS_pos⟩
    have hpickL : ∀ u : ℕ, ∃ pick : Fin k → Option (LayerSigma ℓ β γ i.1),
        ∀ a ∈ S i (vLeft u), ∃ p, pick p = some a := fun u => hcover_opt _ (hS_card i (vLeft u))
    have hpickR : ∀ w : ℕ, ∃ pick : Fin k → Option (LayerSigma ℓ β γ j.1),
        ∀ b ∈ S j (vRight w), ∃ q, pick q = some b :=
          fun w => hcover_opt _ (hS_card j (vRight w))
    choose pickL hL_cov using hpickL
    choose pickR hR_cov using hpickR
    let b₀ : β := Classical.arbitrary β
    let c₀ : γ := Classical.arbitrary γ
    let satFor (p q : Fin k) : Finset E :=
      Finset.univ.filter fun e =>
        (g.toGraph projectionEval).Satisfies
          (fun u =>
            (match pickL u p with | some a => a.2 ⟨0, by omega⟩ | none => b₀,
             match pickR u q with | some b => b.1 ⟨i.1, hij⟩ | none => c₀)) e
    have hsub : (Finset.univ.filter fun e : E => eSplit.symm (rest, e) ∈ Good) ⊆
        (Finset.univ : Finset (Fin k × Fin k)).biUnion fun pq => satFor pq.1 pq.2 := by
      intro e he
      have hgood_e := (mem_lcGoodSet_iff ℓ g S i j hij _).mp (Finset.mem_filter.mp he).2
      obtain ⟨a, ha, hb⟩ := hgood_e
      have he_sd := src_dst_lt_graphVertexBound g (List.getElem_mem e.2)
      have hsrc : (g.edges[e.1]).src < B := he_sd.1
      have hdst : (g.edges[e.1]).dst < B := he_sd.2
      have heSplit_self : ∀ h : i.1 < ℓ, eSplit.symm (rest, e) ⟨i.1, h⟩ = e := fun h => by
        have hEq : (⟨i.1, h⟩ : Fin ℓ) = i0 := rfl
        rw [hEq]; simp [eSplit]
      have heSplit_other : ∀ {t : Fin ℓ} (h : t ≠ i0),
          eSplit.symm (rest, e) t = rest ⟨t, h⟩ := fun h => by simp [eSplit, h]
      have hvi_eq : (⟨tupleToNat B ℓ (chainVertex ℓ i.1 (fun t => g.edges[eSplit.symm (rest,
        e) t])),
          tupleToNat_lt ℓ _ fun t => by
            have hsd := src_dst_lt_graphVertexBound g
              (List.getElem_mem (eSplit.symm (rest, e) t).2)
            dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩ :
          Fin layerSize) = vLeft (g.edges[e.1]).src := by
        apply Fin.ext
        dsimp only [vLeft]
        simp only [hsrc, ↓reduceDIte]
        congr 1; funext t
        dsimp only [chainVertex]
        by_cases hti : t = i0
        · subst hti
          simp only [↓reduceDIte, i0, lt_irrefl, ↓reduceIte, heSplit_self]
          rfl
        · simp only [hti, ↓reduceDIte, heSplit_other hti]
      have hvj_eq : (⟨tupleToNat B ℓ (chainVertex ℓ j.1 (fun t => g.edges[eSplit.symm (rest,
        e) t])),
          tupleToNat_lt ℓ _ fun t => by
            have hsd := src_dst_lt_graphVertexBound g
              (List.getElem_mem (eSplit.symm (rest, e) t).2)
            dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩ :
          Fin layerSize) = vRight (g.edges[e.1]).dst := by
        apply Fin.ext
        dsimp only [vRight]
        simp only [hdst, ↓reduceDIte]
        congr 1; funext t
        dsimp only [chainVertex]
        by_cases hti : t = i0
        · subst hti
          have hlt_ij : i.1 < j.1 := hij
          simp only [↓reduceDIte, i0, hlt_ij, ↓reduceIte, heSplit_self]
          rfl
        · simp only [hti, ↓reduceDIte, heSplit_other hti]
      rw [hvi_eq] at ha
      rw [hvj_eq] at hb
      obtain ⟨p, hp⟩ := hL_cov (g.edges[e.1]).src a ha
      obtain ⟨q, hq⟩ := hR_cov (g.edges[e.1]).dst _ hb
      refine Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [satisfies_toGraph_projectionEval_iff]
      dsimp only [List.get_eq_getElem]
      rw [hp, hq]
      dsimp only [layerCompProj]
      have hnot_lt : ¬ (i.1 < i.1) := lt_irrefl _
      have hsub0 : i.1 - i.1 = 0 := Nat.sub_self _
      simp only [hnot_lt, ↓reduceDIte, hsub0, heSplit_self]
      rfl
    have hsat_le : ∀ p q : Fin k, ((satFor p q).card : ℝ) ≤ δ * (g.edges.length : ℝ) := by
      intro p q
      let σ : ℕ → β × γ := fun u =>
        (match pickL u p with | some a => a.2 ⟨0, by omega⟩ | none => b₀,
         match pickR u q with | some b => b.1 ⟨i.1, hij⟩ | none => c₀)
      have hunsat : (g.toGraph projectionEval).unsatVal ≤
          (g.toGraph projectionEval).unsatFrac σ :=
        (g.toGraph projectionEval).unsatVal_le σ
      have hfrac_ge : 1 - δ ≤ (g.toGraph projectionEval).unsatFrac σ := by linarith
      have hcard_unsat : (1 - δ) * (g.edges.length : ℝ) ≤
          (((g.toGraph projectionEval).unsatEdges σ).card : ℝ) := by
        have hmul := (g.toGraph projectionEval).card_mul_unsatFrac σ
        simp only [Fintype.card_fin] at hmul
        rw [← hmul]
        have hE_nn : (0 : ℝ) ≤ (g.edges.length : ℝ) := Nat.cast_nonneg _
        nlinarith
      have hdisj : Disjoint (satFor p q) ((g.toGraph projectionEval).unsatEdges σ) := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact ((ConstraintGraph.mem_unsatEdges).mp he2) (Finset.mem_filter.mp he1).2
      have hcard_add : (satFor p q).card + ((g.toGraph projectionEval).unsatEdges σ).card ≤
          g.edges.length := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact (Finset.card_le_univ _).trans (by simp [E])
      have hcard_add' : ((satFor p q).card : ℝ) +
          (((g.toGraph projectionEval).unsatEdges σ).card : ℝ) ≤ (g.edges.length : ℝ) := by
        exact_mod_cast hcard_add
      linarith
    calc ((Finset.univ.filter fun e : E => eSplit.symm (rest, e) ∈ Good).card : ℝ)
        ≤ (((Finset.univ : Finset (Fin k × Fin k)).biUnion fun pq =>
            satFor pq.1 pq.2).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ pq : Fin k × Fin k, ((satFor pq.1 pq.2).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _pq : Fin k × Fin k, (δ * (g.edges.length : ℝ)) :=
          Finset.sum_le_sum fun pq _ => hsat_le pq.1 pq.2
      _ = (k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) := by
          simp [Finset.sum_const, Fintype.card_prod, Fintype.card_fin]
          ring
  -- Sum `hslice` over all `rest : {t : Fin ℓ // t ≠ i0} → E`.
  have hcard_good : Good.card =
      ∑ rest : {t : Fin ℓ // t ≠ i0} → E,
        (Finset.univ.filter fun e : E => eSplit.symm (rest, e) ∈ Good).card := by
    have hbij : Good.card =
        (Finset.univ.filter fun p : ({t : Fin ℓ // t ≠ i0} → E) × E =>
          eSplit.symm p ∈ Good).card := by
      refine Finset.card_bij (fun d _ => eSplit d) ?_ ?_ ?_
      · intro d hd; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hd⟩
      · intro _ _ _ _ h; exact eSplit.injective h
      · intro p hp
        exact ⟨eSplit.symm p, (Finset.mem_filter.mp hp).2, eSplit.apply_symm_apply p⟩
    rw [hbij, ← Finset.card_sigma]
    · refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩⟩
      · intro p₁ _ p₂ _ h
        rcases p₁ with ⟨x₁, y₁⟩; rcases p₂ with ⟨x₂, y₂⟩; cases h; rfl
      · intro s hs
        refine ⟨(s.1, s.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hs).2).2⟩, rfl⟩
  have hcard_rest : Fintype.card ({t : Fin ℓ // t ≠ i0} → E) * g.edges.length =
      g.edges.length ^ ℓ := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, Fintype.card_fin]
    have hℓ_pos : 1 ≤ ℓ := by omega
    rw [← pow_succ, Nat.sub_add_cancel hℓ_pos]
  calc (Good.card : ℝ)
      = ∑ rest : {t : Fin ℓ // t ≠ i0} → E,
          ((Finset.univ.filter fun e : E => eSplit.symm (rest, e) ∈ Good).card : ℝ) := by
        rw [hcard_good]; push_cast; rfl
    _ ≤ ∑ _rest : {t : Fin ℓ // t ≠ i0} → E,
          ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ)) :=
        Finset.sum_le_sum fun rest _ => hslice rest
    _ = (Fintype.card ({t : Fin ℓ // t ≠ i0} → E) : ℝ) *
          ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ)) := by
        simp [Finset.sum_const]
    _ = (k : ℝ) ^ 2 * δ * ((Fintype.card ({t : Fin ℓ // t ≠ i0} → E) *
          g.edges.length : ℕ) : ℝ) := by push_cast; ring
    _ = (k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ := by rw [hcard_rest]; push_cast; ring

/-- **Chain-of-minors hardness criterion for `PMC_M(m)`**
: for every `ℓ, k : ℕ`, there exists `m = m(ℓ, k) > 0` such that if a minion `M`
with a unary element admits a `k`-bounded selector `sel` intersecting every `MinorChain M ℓ m`,
then `PMC_M(m)` is NP-hard.
-/
theorem npHard_pmc_of_chain_selector (ℓ k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ (M : Minion.{u}) (hM : Nonempty (M.carrier 1))
      (sel : ∀ {n : ℕ}, n ≤ m → M.carrier n → Finset (Fin n)),
      (∀ {n : ℕ} (hn : n ≤ m) (f : M.carrier n), (sel hn f).card ≤ k) →
      (∀ C : MinorChain M ℓ m,
        ∃ (i j : Fin (ℓ + 1)) (hij : i < j),
          ∃ x ∈ sel (C.arity_le i) (C.elem i),
            C.composeMap i j (le_of_lt hij) x ∈ sel (C.arity_le j) (C.elem j)) →
      PromiseProblem.NPHard (encMinorCondition m) (pmc (m := m) M hM) := by
  let δ : ℝ := 1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1))
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < 1 := by
    dsimp only [δ]
    rw [div_lt_one (by positivity)]
    have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith
    have h2 : (2 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) ^ 2 + 1 := by
      have : (1 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos ℓ
      nlinarith
    nlinarith
  obtain ⟨kRep, hkRep, hLC⟩ := exists_GapLabelCover_npHard hδ_pos hδ_lt
  let β := Fin kRep → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool))
  let γ := Fin kRep → Bool × (Fin 6 → Bool)
  let m := Fintype.card β ^ ℓ
  have hcard_le : Fintype.card γ ≤ Fintype.card β := by
    simp only [β, γ, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    exact Nat.pow_le_pow_left (by norm_num) kRep
  have hβ_pos : 0 < Fintype.card β := Fintype.card_pos
  have hγ_pos : 0 < Fintype.card γ := Fintype.card_pos
  have hm_pos : 0 < m := Nat.pow_pos hβ_pos
  have hm_bound : ∀ i ≤ ℓ, cardLayerSigma ℓ β γ i ≤ m := by
    intro i hi
    dsimp only [cardLayerSigma, m]
    calc Fintype.card γ ^ i * Fintype.card β ^ (ℓ - i)
        ≤ Fintype.card β ^ i * Fintype.card β ^ (ℓ - i) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard_le i)
      _ = Fintype.card β ^ (i + (ℓ - i)) := (pow_add _ _ _).symm
      _ = Fintype.card β ^ ℓ := by rw [Nat.add_sub_of_le hi]
  refine ⟨m, hm_pos, fun M hM sel hsel_card hsel_chain => ?_⟩
  let encG : (Fin kRep → Bool × (Fin 6 → Bool)) ↪ List Bool :=
    encPi (encPair encBool (encPi encBool))
  refine hLC.trans ⟨lcToMinorCond ℓ m, computableInPolyTime_lcToMinorCond ℓ m encG, ?_, ?_⟩
  · -- Completeness: satisfiable Label Cover gives `TriviallySat (lcToMinorCond ℓ m g)`.
    intro g hg
    have hsat_lc : (g.toGraph projectionEval).Satisfiable := by
      rw [← ConstraintGraph.unsatVal_eq_zero_iff]
      rw [GapLabelCover, PromiseProblem.mem_yes_gapMax] at hg
      have hnn := (g.toGraph projectionEval).unsatVal_nonneg
      linarith
    exact lcToMinorCond_completeness ℓ m hm_bound M hM g hsat_lc
  · -- Soundness (contrapositive): `SatIn M (lcToMinorCond ℓ m g)` contradicts `g ∈ no`.
    intro g hno
    rw [mem_no_pmc]
    refine ⟨lcToMinorCond_wellFormed ℓ m hm_bound g, fun hsat => ?_⟩
    classical
    have hval_le : 1 - (g.toGraph projectionEval).unsatVal ≤ δ := by
      rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hno
      exact hno.1
    have hE_pos : 0 < g.edges.length := by
      by_contra h0
      have hemp : g.edges = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hzero : (g.toGraph projectionEval).unsatVal = 0 := by
        have : IsEmpty (Fin g.edges.length) := by rw [hemp, List.length_nil]; exact Fin.isEmpty
        exact ConstraintGraph.unsatVal_of_isEmpty _
      linarith
    obtain ⟨hWF, fL, gR, hsat_c⟩ := hsat
    let B := graphVertexBound g
    let layerSize := B ^ ℓ
    let eSig : ∀ i : ℕ, LayerSigma ℓ β γ i ≃ Fin (cardLayerSigma ℓ β γ i) :=
      fun i => Fintype.equivFinOfCardEq (card_layerSigma_eq ℓ β γ i)
    have hB_pos : 0 < B :=
      lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) (le_max_left _ _))
    have hLS_pos : 0 < layerSize := Nat.pow_pos hB_pos
    have harity_len : (lcToMinorCond ℓ m g).leftArities.length = (ℓ + 1) * layerSize :=
      length_flatMap_range_replicate (cardLayerSigma ℓ β γ) layerSize (ℓ + 1)
    have harity_eq : ∀ (i : Fin (ℓ + 1)) (v : Fin layerSize),
        (lcToMinorCond ℓ m g).leftArities[i.1 * layerSize + v.1]'(by
          rw [harity_len]
          have h1 : i.1 * layerSize + v.1 < (i.1 + 1) * layerSize := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize i.2)) =
        cardLayerSigma ℓ β γ i.1 := by
      intro i v
      have hlt : i.1 * layerSize + v.1 < (lcToMinorCond ℓ m g).leftArities.length := by
        rw [harity_len]
        have h1 : i.1 * layerSize + v.1 < (i.1 + 1) * layerSize := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize i.2)
      have hget := getElem?_flatMap_range_replicate (cardLayerSigma ℓ β γ) i.2 v.2
      dsimp only [lcToMinorCond] at hlt ⊢
      rw [List.getElem?_eq_getElem hlt] at hget
      exact Option.some.inj hget
    -- Extract the casted assignment `F (i, v) : M.carrier (cardLayerSigma ℓ β γ i.1)` with `F = G`.
    let F : ∀ (i : Fin (ℓ + 1)), Fin layerSize → M.carrier (cardLayerSigma ℓ β γ i.1) :=
      fun i v =>
        have hlt : i.1 * layerSize + v.1 < (lcToMinorCond ℓ m g).leftArities.length := by
          rw [harity_len]
          have h1 : i.1 * layerSize + v.1 < (i.1 + 1) * layerSize := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize i.2)
        (harity_eq i v) ▸ fL ⟨i.1 * layerSize + v.1, hlt⟩
    let G_ass : ∀ (i : Fin (ℓ + 1)), Fin layerSize → M.carrier (cardLayerSigma ℓ β γ i.1) :=
      fun i v =>
        have hlt : i.1 * layerSize + v.1 < (lcToMinorCond ℓ m g).rightArities.length := by
          change i.1 * layerSize + v.1 < (lcToMinorCond ℓ m g).leftArities.length
          rw [harity_len]
          have h1 : i.1 * layerSize + v.1 < (i.1 + 1) * layerSize := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize i.2)
        (harity_eq i v) ▸ gR ⟨i.1 * layerSize + v.1, hlt⟩
    have hFG : ∀ i v, F i v = G_ass i v := by
      intro i v
      have hlt : i.1 * layerSize + v.1 < (lcToMinorCond ℓ m g).leftArities.length := by
        rw [harity_len]
        have h1 : i.1 * layerSize + v.1 < (i.1 + 1) * layerSize := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize i.2)
      have hcmem : MinorConstraint.mk (i.1 * layerSize + v.1) (i.1 * layerSize + v.1)
          (List.range (cardLayerSigma ℓ β γ i.1)) ∈ (lcToMinorCond ℓ m g).constraints := by
        refine List.mem_append_left _ ?_
        rw [List.mem_flatMap]
        refine ⟨i.1, List.mem_range.mpr i.2, ?_⟩
        rw [List.mem_map]
        exact ⟨v.1, List.mem_range.mpr v.2, rfl⟩
      have hminor := hsat_c _ hcmem hlt hlt (fun x => by
        have hx : x.1 < cardLayerSigma ℓ β γ i.1 := by rw [← harity_eq i v]; exact x.2
        change (List.range _).getD x.1 0 < (lcToMinorCond ℓ m g).leftArities[i.1 * layerSize + v.1]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hx), List.getElem_range]
        exact lt_of_lt_of_eq hx (harity_eq i v).symm)
      dsimp only [F, G_ass]
      generalize_proofs hp1 hp2
      have hcast : ∀ {a b : ℕ} (h : a = b) (x : M.carrier a) (y : M.carrier a),
          M.minor (fun t : Fin a => ⟨(List.range b).getD t.1 0, by
            have ht : t.1 < b := h ▸ t.2; simp [ht, h]⟩) x = y →
          (h ▸ x) = (h ▸ y) := by
        rintro a _ rfl x y hxy
        have hid : (fun t : Fin a => (⟨(List.range a).getD t.1 0, by
            simp [t.2]⟩ : Fin a)) = id := by
          funext t; apply Fin.ext; simp [t.2]
        rw [hid, M.minor_id] at hxy
        exact hxy
      exact hcast (harity_eq i v) _ _ hminor
    -- Helper: step minor equation for any edge chain `d : Fin ℓ → Fin g.edges.length`.
    let E := Fin g.edges.length
    have hstep_chain : ∀ (d : Fin ℓ → E) (i : Fin ℓ),
        let de : Fin ℓ → Edge (β → γ) := fun t => g.edges[d t]
        let vi : Fin layerSize :=
          ⟨tupleToNat B ℓ (chainVertex ℓ i.1 de), tupleToNat_lt ℓ _ fun t => by
          have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
          dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
        let vj : Fin layerSize :=
          ⟨tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) de), tupleToNat_lt ℓ _ fun t => by
          have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
          dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
        M.minor (fun x => eSig (i.1 + 1) (layerStepProj ℓ i (de i).constraint ((eSig i.1).symm x)))
          (F i.castSucc vi) = F i.succ vj := by
      intro d i
      dsimp only
      set de : Fin ℓ → Edge (β → γ) := fun t => g.edges[d t]
      set vi : Fin layerSize :=
        ⟨tupleToNat B ℓ (chainVertex ℓ i.1 de), tupleToNat_lt ℓ _ fun t => by
        have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
        dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
      set vj : Fin layerSize :=
        ⟨tupleToNat B ℓ (chainVertex ℓ (i.1 + 1) de), tupleToNat_lt ℓ _ fun t => by
        have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
        dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
      have hlti : i.1 * layerSize + vi.1 < (lcToMinorCond ℓ m g).leftArities.length := by
        rw [harity_len]
        have h1 : i.1 * layerSize + vi.1 < (i.1 + 1) * layerSize := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize (by omega))
      have hltj : (i.1 + 1) * layerSize + vj.1 < (lcToMinorCond ℓ m g).rightArities.length := by
        change (i.1 + 1) * layerSize + vj.1 < (lcToMinorCond ℓ m g).leftArities.length
        rw [harity_len]
        have h1 : (i.1 + 1) * layerSize + vj.1 < (i.1 + 2) * layerSize := by
          have := vj.2
          have h2 : (i.1 + 2) * layerSize = (i.1 + 1) * layerSize + layerSize := by ring
          omega
        have := i.2
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right layerSize (by omega))
      have hcmem : MinorConstraint.mk (i.1 * layerSize + vi.1) ((i.1 + 1) * layerSize + vj.1)
          (List.ofFn fun x : Fin (cardLayerSigma ℓ β γ i.1) =>
            (eSig (i.1 + 1) (layerStepProj ℓ i (de i).constraint ((eSig i.1).symm x))).1) ∈
          (lcToMinorCond ℓ m g).constraints := by
        refine List.mem_append_right _ ?_
        rw [List.mem_flatMap]
        refine ⟨de, mem_edgePowList_iff.mpr fun t => List.getElem_mem (d t).2, ?_⟩
        rw [List.mem_map]
        exact ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
      rw [hFG i.succ vj]
      have hminor := hsat_c _ hcmem hlti hltj (fun x => by
        have hx : x.1 < cardLayerSigma ℓ β γ i.1 :=
          lt_of_lt_of_eq x.2 (harity_eq i.castSucc vi)
        change (List.ofFn _).getD x.1 0 <
          (lcToMinorCond ℓ m g).leftArities[i.succ.1 * layerSize + vj.1]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hx), List.getElem_ofFn]
        exact lt_of_lt_of_eq (Fin.is_lt _) (harity_eq i.succ vj).symm)
      dsimp only [F, G_ass]
      generalize_proofs hp1 hp2
      have hcast : ∀ {a₁ b₁ a₂ b₂ : ℕ} (h₁ : a₁ = b₁) (h₂ : a₂ = b₂)
          (x : M.carrier a₁) (y : M.carrier a₂)
          (π : Fin b₁ → Fin b₂),
          M.minor (fun t : Fin a₁ => h₂.symm ▸ π (h₁ ▸ t)) x = y →
          M.minor π (h₁ ▸ x) = (h₂ ▸ y) := by
        rintro a₁ _ a₂ _ rfl rfl x y π hxy
        exact hxy
      refine hcast (harity_eq i.castSucc vi) (harity_eq i.succ vj) _ _ _ ?_
      refine Eq.trans ?_ hminor
      congr 1
      funext t
      have ht : t.1 < cardLayerSigma ℓ β γ i.1 := lt_of_lt_of_eq t.2 (harity_eq i.castSucc vi)
      apply Fin.ext
      dsimp only
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact ht), List.getElem_ofFn]
      have hcast_fin : ∀ {a b : ℕ} (h : a = b) (z : Fin a), (h ▸ z).1 = z.1 := by
        rintro a _ rfl z; rfl
      rw [hcast_fin (harity_eq i.succ vj).symm]
      exact congrArg
        (fun z => (eSig (i.1 + 1) (layerStepProj ℓ i (de i).constraint ((eSig i.1).symm z))).1)
        (Fin.ext (hcast_fin (harity_eq i.castSucc vi) t))
    -- Define the selector sets `S i v : Finset (LayerSigma ℓ β γ i.1)` of size `≤ k`.
    let S (i : Fin (ℓ + 1)) (v : Fin layerSize) : Finset (LayerSigma ℓ β γ i.1) :=
      (sel (hm_bound i.1 (by omega)) (F i v)).image (eSig i.1).symm
    have hS_card : ∀ i v, (S i v).card ≤ k := fun i v =>
      (Finset.card_image_le).trans (hsel_card (hm_bound i.1 (by omega)) (F i v))
    -- For every chain `d : Fin ℓ → E`, build `MinorChain M ℓ m` and extract a good pair `i < j`.
    have hchain_good : ∀ d : Fin ℓ → E,
        ∃ (i j : Fin (ℓ + 1)) (hij : i < j),
          let de : Fin ℓ → Edge (β → γ) := fun t => g.edges[d t]
          let vi : Fin layerSize :=
            ⟨tupleToNat B ℓ (chainVertex ℓ i.1 de), tupleToNat_lt ℓ _ fun t => by
            have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
            dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
          let vj : Fin layerSize :=
            ⟨tupleToNat B ℓ (chainVertex ℓ j.1 de), tupleToNat_lt ℓ _ fun t => by
            have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
            dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
          ∃ a ∈ S i vi,
            layerCompProj ℓ (fun t => (de t).constraint) i j (le_of_lt hij) a ∈ S j vj := by
      intro d
      let de : Fin ℓ → Edge (β → γ) := fun t => g.edges[d t]
      let vOf (i : Fin (ℓ + 1)) : Fin layerSize :=
        ⟨tupleToNat B ℓ (chainVertex ℓ i.1 de), tupleToNat_lt ℓ _ fun t => by
          have hsd := src_dst_lt_graphVertexBound g (List.getElem_mem (d t).2)
          dsimp only [chainVertex]; split_ifs <;> [exact hsd.2; exact hsd.1]⟩
      let C : MinorChain M ℓ m :=
        { arity := fun i => cardLayerSigma ℓ β γ i.1
          arity_le := fun i => hm_bound i.1 (by omega)
          elem := fun i => F i (vOf i)
          stepMap := fun i x =>
            eSig (i.1 + 1) (layerStepProj ℓ i (de i).constraint ((eSig i.1).symm x))
          step_minor := fun i => hstep_chain d i }
      have hcomp_eq : ∀ (i j : Fin (ℓ + 1)) (hij : i ≤ j) (x : Fin (C.arity i)),
          C.composeMap i j hij x =
            eSig j.1 (layerCompProj ℓ (fun t => (de t).constraint) i j hij ((eSig i.1).symm x))
              := by
        intro i j hij x
        rcases j with ⟨j, hj⟩
        induction j with
        | zero =>
          have hi0 : i = ⟨0, hj⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Fin.mk_le_mk.mp hij))
          subst hi0
          rw [MinorChain.composeMap]
          simp only [Nat.not_lt_zero, ↓reduceDIte, id_eq]
          conv_lhs => rw [← Equiv.apply_symm_apply (eSig 0) x]
          congr 1
          apply Prod.ext <;> funext t
          · exact Fin.elim0 t
          · dsimp only [layerCompProj]; exact congrArg _ (Fin.ext (by simp))
        | succ j ih =>
          by_cases hlt : i.1 < j + 1
          · have hj' : j < ℓ := by omega
            have hij' : i ≤ ⟨j, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
            rw [MinorChain.composeMap]
            simp only [hlt, ↓reduceDIte]
            change C.stepMap ⟨j, hj'⟩ (C.composeMap i ⟨j, by omega⟩ hij' x) = _
            rw [ih (by omega) hij']
            dsimp only [C]
            rw [Equiv.symm_apply_apply]
            exact congrArg (eSig (j + 1)) (layerCompProj_step ℓ _ i ⟨j, hj'⟩ hij' _)
          · have hi_eq : i = ⟨j + 1, hj⟩ :=
              Fin.ext (le_antisymm (Fin.mk_le_mk.mp hij) (Nat.le_of_not_lt hlt))
            subst hi_eq
            rw [MinorChain.composeMap]
            simp only [lt_self_iff_false, ↓reduceDIte, id_eq]
            conv_lhs => rw [← Equiv.apply_symm_apply (eSig (j + 1)) x]
            congr 1
            apply Prod.ext <;> funext t
            · dsimp only [layerCompProj]; simp only [t.2, ↓reduceDIte]
            · dsimp only [layerCompProj]; exact congrArg _ (Fin.ext (by simp))
      obtain ⟨i, j, hij, x, hx, hy⟩ := hsel_chain C
      refine ⟨i, j, hij, (eSig i.1).symm x, Finset.mem_image_of_mem _ hx, ?_⟩
      have h1 : (eSig j.1).symm (C.composeMap i j (le_of_lt hij) x) =
          layerCompProj ℓ (fun t => (de t).constraint) i j (le_of_lt hij) ((eSig i.1).symm x) := by
        rw [hcomp_eq i j (le_of_lt hij) x, Equiv.symm_apply_apply]
      rw [← h1]
      exact Finset.mem_image_of_mem _ hy
    -- Count good chains for each fixed pair `i < j`.
    let Good (i j : Fin (ℓ + 1)) (hij : i < j) : Finset (Fin ℓ → E) :=
      lcGoodSet ℓ g S i j hij
    have hgood_bound : ∀ (i j : Fin (ℓ + 1)) (hij : i < j),
        ((Good i j hij).card : ℝ) ≤ (k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ :=
      fun i j hij => lcToMinorCond_good_bound ℓ k g δ hval_le S hS_card i j hij
    -- Sum `hgood_bound` over all pairs `i < j` to derive a contradiction.
    let pairs := (Finset.univ : Finset (Fin (ℓ + 1) × Fin (ℓ + 1))).filter fun p => p.1 < p.2
    have hcover_all : (Finset.univ : Finset (Fin ℓ → E)) ⊆
        pairs.biUnion fun p => if h : p.1 < p.2 then Good p.1 p.2 h else ∅ := by
      intro d _
      obtain ⟨i, j, hij, a, ha, hb⟩ := hchain_good d
      refine Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, ?_⟩
      simp only [hij, ↓reduceDIte]
      exact (mem_lcGoodSet_iff ℓ g S i j hij d).mpr ⟨a, ha, hb⟩
    have htot_le : ((g.edges.length : ℝ) ^ ℓ) ≤
        ((pairs.card : ℝ) * ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ)) := by
      have h1 : (g.edges.length : ℕ) ^ ℓ = (Finset.univ : Finset (Fin ℓ → E)).card := by
        simp [E, Fintype.card_fin]
      calc ((g.edges.length : ℝ) ^ ℓ)
          = ((Finset.univ : Finset (Fin ℓ → E)).card : ℝ) := by exact_mod_cast h1
        _ ≤ ((pairs.biUnion fun p => if h : p.1 < p.2 then Good p.1 p.2 h else ∅).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hcover_all
        _ ≤ ∑ p ∈ pairs,
              (((if h : p.1 < p.2 then Good p.1 p.2 h else ∅).card : ℝ)) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ pairs, ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
            simp only [hlt, ↓reduceDIte]
            exact hgood_bound p.1 p.2 hlt
        _ = (pairs.card : ℝ) * ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ) := by
            simp [Finset.sum_const]
    have hpairs_le : pairs.card ≤ (ℓ + 1) ^ 2 := by
      calc pairs.card ≤ (Finset.univ : Finset (Fin (ℓ + 1) × Fin (ℓ + 1))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = (ℓ + 1) ^ 2 := by simp [Fintype.card_prod, Fintype.card_fin, sq]
    have hcoeff_lt : (pairs.card : ℝ) * ((k : ℝ) ^ 2 * δ) < 1 :=
      chain_delta_bound ℓ k pairs.card hpairs_le
    have hpow_pos : (0 : ℝ) < (g.edges.length : ℝ) ^ ℓ := by positivity
    have hstrict : (pairs.card : ℝ) * ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ) <
        (g.edges.length : ℝ) ^ ℓ := by
      calc (pairs.card : ℝ) * ((k : ℝ) ^ 2 * δ * (g.edges.length : ℝ) ^ ℓ)
          = ((pairs.card : ℝ) * ((k : ℝ) ^ 2 * δ)) * (g.edges.length : ℝ) ^ ℓ := by ring
        _ < 1 * (g.edges.length : ℝ) ^ ℓ := mul_lt_mul_of_pos_right hcoeff_lt hpow_pos
        _ = (g.edges.length : ℝ) ^ ℓ := one_mul _
    linarith

/-- **Chain-of-minors hardness criterion for `PCSP(A, B)`**
: for every `ℓ, k : ℕ`, there exists `m = m(ℓ, k) > 0` such that if `Pol(A, B)`
admits a `k`-bounded selector intersecting every `MinorChain (polMinion A B) ℓ m`, then
`PCSP(A, B)` is NP-hard.
-/
theorem npHard_pcsp_of_chain_selector (ℓ k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ {r : ℕ} {A : Template.{u} r} {B : Template.{v} r}
      [Finite A.Domain] [Nonempty A.Domain] (hAB : A.HasHom B)
      (sel : ∀ {n : ℕ}, n ≤ m → (polMinion A B).carrier n → Finset (Fin n)),
      (∀ {n : ℕ} (hn : n ≤ m) (f : (polMinion A B).carrier n), (sel hn f).card ≤ k) →
      (∀ C : MinorChain (polMinion A B) ℓ m,
        ∃ (i j : Fin (ℓ + 1)) (hij : i < j),
          ∃ x ∈ sel (C.arity_le i) (C.elem i),
            C.composeMap i j (le_of_lt hij) x ∈ sel (C.arity_le j) (C.elem j)) →
      PromiseProblem.NPHard (encFinStructure r) (pcsp A B hAB) := by
  obtain ⟨m, hm_pos, hpmc⟩ := npHard_pmc_of_chain_selector.{max u v} ℓ k
  refine ⟨m, hm_pos, fun {r A B} _ _ hAB sel hcard hchain => ?_⟩
  exact (hpmc (polMinion A B) ⟨hAB.some.projPoly (p := 1) 0⟩ sel hcard hchain).trans
    (polyTimeReducible_pmc_pcsp m hAB)

end Cslib.Complexity.PCSP
