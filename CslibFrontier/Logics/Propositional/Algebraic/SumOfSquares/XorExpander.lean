module
/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.ProofSystem
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.Parity
import CslibFrontier.Foundations.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grigoriev's Sum-of-Squares Degree Lower Bound for Expanding XOR-CSPs

This module proves Grigoriev's linear Sum-of-Squares degree lower bound for Boolean XOR
constraint satisfaction problems over left-regular bipartite vertex expanders, under standard
Lean constraints, connecting bipartite unique-neighbor expansion to Schoenebeck's parity
pseudo-expectation (`Cslib.Logic.PL.ParitySystem.not_sos_refutableInDegree_toPolys`).

For a bipartite incidence relation `adj : U → V → Prop` where every left vertex `u ∈ U` has
degree `k` and every subset `W ⊆ U` with `W.card ≤ r` satisfies
`((1 / 2 + δ) * k) * W.card ≤ (neighborSet adj W).card` (`0 < δ`), double counting yields at
least `2 * δ * k * W.card` unique neighbors of `W`, and hence odd-neighbor boundary size at
least `2 * δ * k * W.card`. A Ben-Sasson–Wigderson induction on bounded-width parity derivations
rules out deriving `0 = 1` in width strictly less than `δ * k * r`. Pulling back along the
degree-`1` affine change of variables `X_v ↦ 1 - 2 x_v` transfers the resulting Sum-of-Squares
degree lower bound to both the multiplicative `{0, 1}` encoding
`∏_{v ∈ N(u)} (1 - 2 x_v) = 1 - 2 b_u` (with twin Boolean and complementation constraints) and the
multilinear Boolean XOR polynomial encoding `xorBoolPoly (N(u)) = b_u`, as well as any subset
of constraints `U' ⊆ U`.

We also establish sharpness of the threshold `c > k / 2`: for every `m ≥ 1`, taking `m` disjoint
copies of `K_{2, 4}` yields a `(2 * m, 4, 2)`-expander on `4 * m` right vertices whose XOR-CSP
admits a constant-degree (`d = 4`) Sum-of-Squares refutation.

## Main definitions

* `CslibFrontier.ProofComplexity.bipartiteNeighbors`,
  `CslibFrontier.ProofComplexity.bipartiteNeighborSet`:
  right neighborhood of a left vertex and of a finite set of left vertices.
* `CslibFrontier.ProofComplexity.IsBipartiteExpander`: left-`k`-regular `(r, k, c)`-vertex expander.
* `CslibFrontier.ProofComplexity.oddNeighborSet`: right vertices adjacent to an odd number of
  vertices
  in `W ⊆ U`.
* `CslibFrontier.ProofComplexity.xorConstraintPoly`, `CslibFrontier.ProofComplexity.xorCspPolys`:
  twin-literal Boolean `{0, 1}` polynomial encoding of an XOR-CSP over a bipartite graph.
* `CslibFrontier.ProofComplexity.xorBoolPoly`, `CslibFrontier.ProofComplexity.xorMultilinPolys`:
  multilinear `{0, 1}`-valued XOR polynomial `(1 - ∏_{v ∈ S} (1 - 2 X_v)) / 2` and the resulting
  Boolean polynomial system.

## Main results

* `CslibFrontier.ProofComplexity.two_mul_sub_le_card_oddNeighborSet`: unique-neighbor lower bound
  `2 * |N(W)| - k * |W| ≤ |oddNeighborSet W|` for left-`k`-regular bipartite graphs.
* `CslibFrontier.ProofComplexity.not_derives_empty_true_of_isBipartiteExpander`: no parity
  derivation
  of `0 = 1` in width strictly less than `δ * k * r` on an `(r, k, (1 / 2 + δ) * k)`-expander.
* `CslibFrontier.ProofComplexity.grigoriev_xor_sos_degree`: Grigoriev's SoS degree lower bound
  `δ * k * r ≤ d` for the twin-literal `{0, 1}` XOR-CSP on an `(r, k, (1 / 2 + δ) * k)`-expander.
* `CslibFrontier.ProofComplexity.grigoriev_xor_multilin_sos_degree`: corresponding SoS degree lower
  bound for any constraint subsystem of the multilinear `{0, 1}` XOR encoding.
* `CslibFrontier.ProofComplexity.grigoriev_three_xor_sos_degree`: specialization to `(r, 3, 2)`
  expanders yielding degree at least `r / 2`.
* `CslibFrontier.ProofComplexity.exists_two_expander_sosRefutableInDegree_four`: for every `m ≥ 1`,
  there exists a `(2 * m, 4, 2)`-expander with `4 * m` right vertices whose XOR-CSP is refutable
  in Sum-of-Squares degree `4`.
-/

public section

namespace CslibFrontier.ProofComplexity

open MvPolynomial Finset
open Cslib.Logic.PL
open scoped symmDiff

/-! ### Bipartite Vertex Expansion and Odd-Neighbor Boundary -/

section Expansion

variable {U V : Type*} [Fintype V]

/-- Right neighbors of a left vertex `u : U` under a bipartite adjacency relation `adj`. -/
noncomputable def bipartiteNeighbors (adj : U → V → Prop) (u : U) : Finset V := by
  classical
  exact Finset.univ.filter (adj u)

@[simp]
theorem mem_bipartiteNeighbors {adj : U → V → Prop} {u : U} {v : V} :
    v ∈ bipartiteNeighbors adj u ↔ adj u v := by
  classical
  simp [bipartiteNeighbors]

/-- Right neighborhood `N(W) = ⋃ u ∈ W, N(u)` of a finite set of left vertices `W ⊆ U`. -/
noncomputable def bipartiteNeighborSet (adj : U → V → Prop) (W : Finset U) : Finset V := by
  classical
  exact W.biUnion (bipartiteNeighbors adj)

@[simp]
theorem mem_bipartiteNeighborSet {adj : U → V → Prop} {W : Finset U} {v : V} :
    v ∈ bipartiteNeighborSet adj W ↔ ∃ u ∈ W, adj u v := by
  classical
  simp [bipartiteNeighborSet]

/-- A bipartite relation `adj : U → V → Prop` is an `(r, k, c)`-expander if every `u : U` has
left degree `k` and every subset `W ⊆ U` of size at most `r` has `|N(W)| ≥ c * |W|`. -/
@[expose] def IsBipartiteExpander (adj : U → V → Prop) (r k : ℕ) (c : ℝ) : Prop :=
  (∀ u : U, (bipartiteNeighbors adj u).card = k) ∧
  (∀ W : Finset U, W.card ≤ r → c * (W.card : ℝ) ≤ ((bipartiteNeighborSet adj W).card : ℝ))

/-- Set of right vertices in `V` adjacent to an odd number of vertices in `W : Finset U`
(equivalently the iterated symmetric difference `∆_{u ∈ W} N(u)`). -/
noncomputable def oddNeighborSet (adj : U → V → Prop) (W : Finset U) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ Odd (W.filter fun u ↦ adj u v).card

@[simp]
theorem oddNeighborSet_empty (adj : U → V → Prop) :
    oddNeighborSet adj (∅ : Finset U) = ∅ := by
  classical
  ext v
  simp [oddNeighborSet]

@[simp]
theorem oddNeighborSet_singleton (adj : U → V → Prop) (u : U) :
    oddNeighborSet adj {u} = bipartiteNeighbors adj u := by
  classical
  ext v
  simp only [oddNeighborSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_bipartiteNeighbors]
  by_cases h : adj u v
  · rw [Finset.filter_true_of_mem (by simpa using h)]; simp [h]
  · rw [Finset.filter_false_of_mem (by simpa using h)]; simp [h]

/-- Symmetric difference law:
`oddNeighborSet adj (W₁ ∆ W₂) = oddNeighborSet adj W₁ ∆ oddNeighborSet adj W₂`. -/
theorem oddNeighborSet_symmDiff [DecidableEq U] [DecidableEq V] (adj : U → V → Prop)
    (W₁ W₂ : Finset U) :
    oddNeighborSet adj (W₁ ∆ W₂) = oddNeighborSet adj W₁ ∆ oddNeighborSet adj W₂ := by
  classical
  ext v
  simp only [oddNeighborSet, Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and]
  let P : U → Prop := fun u ↦ adj u v
  let A₁ := W₁.filter P
  let A₂ := W₂.filter P
  have hsd : (W₁ ∆ W₂).filter P = A₁ ∆ A₂ := by
    ext u
    simp only [A₁, A₂, Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  rw [hsd]
  have hadd : (A₁ ∆ A₂).card + 2 * (A₁ ∩ A₂).card = A₁.card + A₂.card := by
    have h1 := Finset.card_sdiff_add_card_inter A₁ A₂
    have h2 := Finset.card_sdiff_add_card_inter A₂ A₁
    rw [Finset.inter_comm A₂ A₁] at h2
    have h3 : (A₁ ∆ A₂).card = (A₁ \ A₂).card + (A₂ \ A₁).card := by
      rw [symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    omega
  have hiff : Odd (A₁ ∆ A₂).card ↔ ¬ (Odd A₁.card ↔ Odd A₂.card) := by
    simp only [Nat.odd_iff]; omega
  rw [hiff]
  tauto

/-- **Unique-neighbor double-counting bound**: if every `u ∈ W` has at most `k` right neighbors,
then `2 * |N(W)| ≤ k * |W| + |oddNeighborSet adj W|`. -/
theorem two_mul_card_neighborSet_le (adj : U → V → Prop) {W : Finset U} {k : ℕ}
    (hdeg : ∀ u ∈ W, (bipartiteNeighbors adj u).card ≤ k) :
    2 * (bipartiteNeighborSet adj W).card ≤ k * W.card + (oddNeighborSet adj W).card := by
  classical
  let N1 : Finset V := (bipartiteNeighborSet adj W).filter
    fun v ↦ (W.filter fun u ↦ adj u v).card = 1
  let N2 : Finset V := (bipartiteNeighborSet adj W).filter
    fun v ↦ (W.filter fun u ↦ adj u v).card ≠ 1
  have hpart : N1.card + N2.card = (bipartiteNeighborSet adj W).card :=
    Finset.card_filter_add_card_filter_not _
  have hN1_sub : N1 ⊆ oddNeighborSet adj W := by
    intro v hv
    have hc : (W.filter fun u ↦ adj u v).card = 1 := (Finset.mem_filter.mp hv).2
    simp [oddNeighborSet, hc]
  have hN2_ge : ∀ v ∈ N2, 2 ≤ (W.filter fun u ↦ adj u v).card := by
    intro v hv
    obtain ⟨hvN, hne1⟩ := Finset.mem_filter.mp hv
    obtain ⟨u, huW, huv⟩ := mem_bipartiteNeighborSet.mp hvN
    have hpos : 0 < (W.filter fun u ↦ adj u v).card :=
      Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨huW, huv⟩⟩
    omega
  have hedges : ∑ v ∈ bipartiteNeighborSet adj W, (W.filter fun u ↦ adj u v).card =
      ∑ u ∈ W, (bipartiteNeighbors adj u).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [← Finset.card_filter, bipartiteNeighbors]
    congr 1; ext v
    simp only [Finset.mem_filter, mem_bipartiteNeighborSet, Finset.mem_univ, true_and,
      and_iff_right_iff_imp]
    exact fun h ↦ ⟨u, hu, h⟩
  have hup : ∑ u ∈ W, (bipartiteNeighbors adj u).card ≤ k * W.card := by
    calc
      ∑ u ∈ W, (bipartiteNeighbors adj u).card ≤ ∑ _u ∈ W, k := Finset.sum_le_sum hdeg
      _ = k * W.card := by simp [Nat.mul_comm]
  have hlow : N1.card + 2 * N2.card ≤
      ∑ v ∈ bipartiteNeighborSet adj W, (W.filter fun u ↦ adj u v).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (bipartiteNeighborSet adj W)
      (fun v ↦ (W.filter fun u ↦ adj u v).card = 1)]
    refine Nat.add_le_add ?_ ?_
    · rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun v hv ↦ (Finset.mem_filter.mp hv).2.ge
    · calc
        2 * N2.card = ∑ _v ∈ N2, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ N2, (W.filter fun u ↦ adj u v).card := Finset.sum_le_sum hN2_ge
  have hN1_le : N1.card ≤ (oddNeighborSet adj W).card := Finset.card_le_card hN1_sub
  omega

/-- On an `(r, k, (1 / 2 + δ) * k)`-expander, every `W ⊆ U` with `|W| ≤ r` satisfies
`2 * δ * k * |W| ≤ |oddNeighborSet adj W|`. -/
theorem two_mul_delta_le_card_oddNeighborSet {adj : U → V → Prop} {r k : ℕ} {δ : ℝ}
    (hexp : IsBipartiteExpander adj r k ((1 / 2 + δ) * k))
    {W : Finset U} (hW : W.card ≤ r) :
    2 * δ * (k : ℝ) * (W.card : ℝ) ≤ ((oddNeighborSet adj W).card : ℝ) := by
  have h1 : ((2 * (bipartiteNeighborSet adj W).card : ℕ) : ℝ) ≤
      ((k * W.card + (oddNeighborSet adj W).card : ℕ) : ℝ) :=
    Nat.cast_le.mpr (two_mul_card_neighborSet_le adj fun u _ ↦ (hexp.1 u).le)
  push_cast at h1
  have h2 := hexp.2 W hW
  linarith

/-- Parity system over `V` associated to a bipartite relation `adj : U → V → Prop`, a list `us`
of active constraints in `U`, and right-hand side `b : U → Bool`. -/
noncomputable def bipartiteParitySystem (adj : U → V → Prop) (us : List U) (b : U → Bool) :
    ParitySystem V :=
  us.map fun u ↦ ⟨bipartiteNeighbors adj u, b u⟩

/-- **Ben-Sasson–Wigderson width lower bound for expanding parity systems**: if `adj` is an
`(r, k, (1 / 2 + δ) * k)`-expander with `0 < δ`, then for any list `us : List U` of constraints,
any right-hand side `b : U → Bool`, and any width `w` with `(w : ℝ) < δ * k * r`, the parity
system `bipartiteParitySystem adj us b` cannot derive `0 = 1` in width `w`. -/
theorem not_derives_empty_true_of_isBipartiteExpander [DecidableEq V]
    {adj : U → V → Prop} {r k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hexp : IsBipartiteExpander adj r k ((1 / 2 + δ) * k))
    (us : List U) (b : U → Bool) {w : ℕ} (hw : (w : ℝ) < δ * (k : ℝ) * (r : ℝ)) :
    ¬ (bipartiteParitySystem adj us b).Derives w ∅ true := by
  classical
  have hk_pos : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp at hw
    linarith [Nat.cast_nonneg (α := ℝ) w]
  have hr_pos : 1 ≤ r := by
    by_contra hr0
    have : r = 0 := by omega
    subst this
    simp at hw
    linarith [Nat.cast_nonneg (α := ℝ) w]
  rcases eq_or_lt_of_le hr_pos with hr1 | hr2
  · -- Case `r = 1`: we have `δ ≤ 1 / 2` if any `u ∈ us`, so `w < δ * k ≤ k`, no constraint fits!
    rw [eq_comm] at hr1
    subst hr1
    have hinv : ∀ {T : Finset V} {c : Bool},
        (bipartiteParitySystem adj us b).Derives w T c → T = ∅ ∧ c = false := by
      intro T c hd
      induction hd with
      | empty => exact ⟨rfl, rfl⟩
      | mem he hS =>
        obtain ⟨u, _, heq⟩ := List.mem_map.mp he
        obtain ⟨rfl, rfl⟩ := ParityEquation.mk.inj heq
        have hex1 := two_mul_delta_le_card_oddNeighborSet hexp (W := {u}) (by simp)
        rw [oddNeighborSet_singleton, hexp.1 u, Finset.card_singleton] at hex1
        have hSc : ((bipartiteNeighbors adj u).card : ℝ) ≤ (w : ℝ) := Nat.cast_le.mpr hS
        rw [hexp.1 u] at hSc
        simp only [Nat.cast_one, mul_one] at hex1 hw
        linarith
      | symmDiff _ _ _ ih1 ih2 =>
        rw [ih1.1, ih1.2, ih2.1, ih2.2]; simp
    intro hd
    exact Bool.false_ne_true (hinv hd).2.symm
  · -- Case `2 ≤ r`: every derived equation comes from `W ⊆ U` with `2 * |W| ≤ r`.
    have hinv : ∀ {T : Finset V} {c : Bool},
        (bipartiteParitySystem adj us b).Derives w T c →
        ∃ W : Finset U, oddNeighborSet adj W = T ∧ Cslib.parityOn W b = c ∧
          2 * (W.card : ℝ) ≤ (r : ℝ) := by
      intro T c hd
      induction hd with
      | empty =>
        exact ⟨∅, oddNeighborSet_empty adj, Cslib.parityOn_empty b, by simp⟩
      | mem he _ =>
        obtain ⟨u, _, heq⟩ := List.mem_map.mp he
        obtain ⟨rfl, rfl⟩ := ParityEquation.mk.inj heq
        have hr2' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
        exact ⟨{u}, oddNeighborSet_singleton adj u, Cslib.parityOn_singleton u b,
          by simp; linarith⟩
      | symmDiff _ _ hST ih1 ih2 =>
        obtain ⟨W₁, rfl, rfl, h1⟩ := ih1
        obtain ⟨W₂, rfl, rfl, h2⟩ := ih2
        refine ⟨W₁ ∆ W₂, oddNeighborSet_symmDiff adj W₁ W₂, Cslib.parityOn_symmDiff W₁ W₂ b, ?_⟩
        have hW_le : (W₁ ∆ W₂).card ≤ r := by
          have hc : (((W₁ ∆ W₂).card : ℕ) : ℝ) ≤ ((W₁.card + W₂.card : ℕ) : ℝ) :=
            Nat.cast_le.mpr (card_symmDiff_le W₁ W₂)
          push_cast at hc
          have hcr : (((W₁ ∆ W₂).card : ℕ) : ℝ) ≤ (r : ℝ) := by linarith
          exact_mod_cast hcr
        have hex := two_mul_delta_le_card_oddNeighborSet hexp hW_le
        rw [oddNeighborSet_symmDiff] at hex
        have hST' : (((oddNeighborSet adj W₁ ∆ oddNeighborSet adj W₂).card : ℕ) : ℝ) ≤ (w : ℝ) :=
          Nat.cast_le.mpr hST
        have hdk : 0 < δ * (k : ℝ) := mul_pos hδ (Nat.cast_pos.mpr hk_pos)
        nlinarith
    intro hd
    obtain ⟨W, hW_odd, hW_par, hW_card⟩ := hinv hd
    have hWr : W.card ≤ r := by
      have : (W.card : ℝ) ≤ (r : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) W.card]
      exact_mod_cast this
    have hex := two_mul_delta_le_card_oddNeighborSet hexp hWr
    rw [hW_odd, Finset.card_empty, Nat.cast_zero] at hex
    have hdk : 0 < 2 * δ * (k : ℝ) := by positivity
    have hW0 : (W.card : ℝ) ≤ 0 := nonpos_of_mul_nonpos_right hex hdk
    have hWempty : W = ∅ :=
      Finset.card_eq_zero.mp (by exact_mod_cast le_antisymm hW0 (Nat.cast_nonneg _))
    rw [hWempty, Cslib.parityOn_empty] at hW_par
    exact Bool.false_ne_true hW_par

end Expansion

/-! ### Boolean `{0, 1}` XOR-CSP Encodings and Grigoriev's Theorem -/

section XorBoolPoly

open Cslib

variable {V : Type*}

private theorem vars_one_sub_two_X_subset (w : V) :
    (1 - 2 * (X w : MvPolynomial V ℝ)).vars ⊆ {w} := by
  classical
  refine (vars_sub_le _ _).trans (Finset.union_subset (by simp) ?_)
  have h2 : (2 : MvPolynomial V ℝ) = C 2 := map_ofNat C 2
  rw [h2]
  exact (vars_mul _ _).trans (Finset.union_subset (by simp [vars_C]) (vars_X_subset_singleton w))

/-- Multiplicative `{0, 1}` XOR constraint polynomial
`∏ v ∈ S, (1 - 2 * X (Lit.pos v)) - C (1 - 2 * b)` over twin variables `Lit V`. -/
noncomputable def xorConstraintPoly (S : Finset V) (b : Bool) : MvPolynomial (Lit V) ℝ :=
  (∏ v ∈ S, (1 - 2 * X (Lit.pos v))) - C (if b then -1 else 1)

/-- Unique multilinear `{0, 1}`-valued polynomial `(1 - ∏ v ∈ S, (1 - 2 * X v)) / 2` over plain
variables `V` evaluating to `(parityOn S a)` on every `a : V → Bool`. -/
noncomputable def xorBoolPoly (S : Finset V) : MvPolynomial V ℝ :=
  C (1 / 2 : ℝ) * (1 - ∏ v ∈ S, (1 - 2 * X v))

/-- Evaluation of `xorBoolPoly S` on a `{0, 1}` point equals the parity of `a` on `S`. -/
theorem eval_boolPoint_xorBoolPoly (S : Finset V) (a : V → Bool) :
    eval (boolPoint ℝ a) (xorBoolPoly S) = if parityOn S a then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [xorBoolPoly]
  | insert v S hv ih =>
    have h1 : eval (boolPoint ℝ a) (xorBoolPoly S) = if parityOn S a then 1 else 0 := ih
    simp only [xorBoolPoly, map_mul, map_sub, map_one, eval_C] at h1
    have hprod : eval (boolPoint ℝ a) (∏ u ∈ S, (1 - 2 * X u)) =
        if parityOn S a then -1 else 1 := by
      cases hp : parityOn S a <;> rw [hp] at h1 <;> norm_num at h1 ⊢ <;> linarith
    simp only [xorBoolPoly, Finset.prod_insert hv, map_mul, map_sub, map_one, map_ofNat,
      eval_C, eval_X, parityOn_insert hv, hprod]
    cases hv' : a v <;> cases parityOn S a <;> simp [hv'] <;> norm_num

/-- Every variable has degree at most `1` in `xorBoolPoly S` (it is multilinear). -/
theorem degreeOf_xorBoolPoly_le_one (S : Finset V) (v : V) :
    (xorBoolPoly S).degreeOf v ≤ 1 := by
  classical
  have hdeg0 : ∀ {q : MvPolynomial V ℝ} {u : V}, u ∉ q.vars → q.degreeOf u = 0 := by
    intro q u hnot
    rw [degreeOf_eq_sup]
    exact Nat.eq_zero_of_le_zero <| Finset.sup_le fun m hm ↦
      (Nat.eq_zero_of_not_pos fun hpos ↦
        hnot (mem_vars_of_mem_support hm (Finsupp.mem_support_iff.mpr hpos.ne'))).le
  simp only [xorBoolPoly]
  refine (degreeOf_mul_le v _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_sub_le v _ _).trans (max_le (by simp) ?_)
  induction S using Finset.induction_on with
  | empty => simp
  | insert u S hu ih =>
    rw [Finset.prod_insert hu]
    refine (degreeOf_mul_le v _ _).trans ?_
    by_cases huv : u = v
    · subst huv
      have hnot : (∏ w ∈ S, (1 - 2 * (X w : MvPolynomial V ℝ))).degreeOf u = 0 :=
        hdeg0 fun hmem ↦ by
          obtain ⟨w, hw, hwu⟩ := Finset.mem_biUnion.mp (vars_prod_le S _ hmem)
          exact hu (Finset.mem_singleton.mp (vars_one_sub_two_X_subset w hwu) ▸ hw)
      have hfac : (1 - 2 * (X u : MvPolynomial V ℝ)).degreeOf u ≤ 1 :=
        (degreeOf_le_totalDegree _ u).trans ((totalDegree_sub _ _).trans (max_le (by simp) (by
          rw [show (2 : MvPolynomial V ℝ) = C 2 from map_ofNat C 2]
          exact (totalDegree_mul _ _).trans
            (by rw [totalDegree_C, zero_add]; exact totalDegree_var_le u))))
      omega
    · have hfac : (1 - 2 * (X u : MvPolynomial V ℝ)).degreeOf v = 0 :=
        hdeg0 fun hmem ↦ huv (Finset.mem_singleton.mp (vars_one_sub_two_X_subset u hmem)).symm
      rw [hfac, zero_add]
      exact ih

/-- `xorBoolPoly S` uses only variables from `S`. -/
theorem vars_xorBoolPoly_subset (S : Finset V) :
    (xorBoolPoly S).vars ⊆ S := by
  classical
  simp only [xorBoolPoly]
  refine (vars_mul _ _).trans (Finset.union_subset (by simp [vars_C]) ?_)
  refine (vars_sub_le _ _).trans (Finset.union_subset (by simp) ?_)
  refine (vars_prod_le S _).trans (Finset.biUnion_subset.mpr fun u hu ↦ ?_)
  exact (vars_one_sub_two_X_subset u).trans (Finset.singleton_subset_iff.mpr hu)

/-- Total degree of `xorBoolPoly S` is at most `S.card`. -/
theorem totalDegree_xorBoolPoly_le (S : Finset V) :
    (xorBoolPoly S).totalDegree ≤ S.card := by
  simp only [xorBoolPoly]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
  rw [show (2 : MvPolynomial V ℝ) = C 2 from map_ofNat C 2]
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact totalDegree_var_le u)

end XorBoolPoly

section XorEncodings

variable {U V : Type*} [Fintype V]

/-- Full twin-literal `{0, 1}` polynomial encoding `Φ(G, b)` of an XOR-CSP on a finite bipartite
graph `(U, V, adj)`: constraint polynomials for every `u ∈ U`, plus all twin Boolean and
complementation constraints on `V`. -/
noncomputable def xorCspPolys [Fintype U] (adj : U → V → Prop) (b : U → Bool) :
    List (MvPolynomial (Lit V) ℝ) :=
  (Finset.univ.toList.map fun u ↦ xorConstraintPoly (bipartiteNeighbors adj u) (b u)) ++
    twinBoolAxioms V

/-- Multilinear `{0, 1}` XOR-CSP polynomial system over plain variables `V` for a constraint list
`us : List U`: `{xorBoolPoly (N(u)) - b_u | u ∈ us} ∪ {y_v ^ 2 - y_v | v ∈ V}`. -/
@[expose]
noncomputable def xorMultilinPolys (adj : U → V → Prop) (us : List U) (b : U → Bool) :
    List (MvPolynomial V ℝ) :=
  (us.map fun u ↦ xorBoolPoly (bipartiteNeighbors adj u) - C (if b u then 1 else 0)) ++
    (Finset.univ.toList.map (boolAxiom ℝ))

/-- Transfer from twin-literal `{0, 1}` XOR-CSP refutation in degree `d` to `±1`
`ParitySystem.toPolys ℝ` refutation in degree `d` via `x_v ↦ (1 - X_v) / 2`,
`x̄_v ↦ (1 + X_v) / 2`. -/
private theorem refutableInDegree_paritySystem_of_xorCsp (adj : U → V → Prop)
    (us : List U) (b : U → Bool) {d : ℕ}
    (href : SosRefutableInDegree
      ((us.map fun u ↦ xorConstraintPoly (bipartiteNeighbors adj u) (b u)) ++
        twinBoolAxioms V) d) :
    SOS.RefutableInDegree ((bipartiteParitySystem adj us b).toPolys ℝ) d := by
  let φ : Lit V → MvPolynomial V ℝ
    | (v, false) => C (1 / 2 : ℝ) * (1 - X v)
    | (v, true) => C (1 / 2 : ℝ) * (1 + X v)
  have hφ_deg : ∀ l : Lit V, (φ l).totalDegree ≤ 1 := by
    rintro ⟨v, _ | _⟩
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_var_le v))
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_add _ _).trans (max_le (by simp) (totalDegree_var_le v))
  have hhalf : C (1 / 2 : ℝ) * (2 : MvPolynomial V ℝ) = 1 := by
    rw [show (2 : MvPolynomial V ℝ) = C 2 from map_ofNat C 2, ← map_mul]; norm_num
  have hquarter : (C (1 / 2 : ℝ) : MvPolynomial V ℝ) ^ 2 = C (1 / 4 : ℝ) := by
    rw [← map_pow]; norm_num
  have hch : (C (1 / 2 : ℝ) : MvPolynomial V ℝ) = C (1 / 4 : ℝ) * 2 := by
    rw [show (2 : MvPolynomial V ℝ) = C 2 from map_ofNat C 2, ← map_mul]; norm_num
  have hφ_xor : ∀ (S : Finset V) (c : Bool),
      aeval φ (xorConstraintPoly S c) = ParitySystem.parityPoly ℝ S c := by
    intro S c
    simp only [xorConstraintPoly, ParitySystem.parityPoly, map_sub, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun v _ ↦ ?_
      simp only [map_one, map_mul, map_ofNat, aeval_X, φ]
      calc
        1 - 2 * (C (1 / 2 : ℝ) * (1 - X v))
            = 1 - (C (1 / 2 : ℝ) * 2) * (1 - X v) := by ring
        _ = X v := by rw [hhalf]; ring
    · cases c <;> simp
  have hφ_bool : ∀ l : Lit V,
      aeval φ (boolAxiom ℝ l) = C (1 / 4 : ℝ) * (X l.1 ^ 2 - 1) := by
    rintro ⟨v, _ | _⟩
    · simp only [aeval_boolAxiom, φ]
      calc
        (C (1 / 2 : ℝ) * (1 - X v)) ^ 2 - C (1 / 2 : ℝ) * (1 - X v)
            = C (1 / 4 : ℝ) * (1 - X v) ^ 2 - C (1 / 4 : ℝ) * 2 * (1 - X v) := by
              rw [mul_pow, hquarter, hch]
        _ = C (1 / 4 : ℝ) * (X v ^ 2 - 1) := by ring
    · simp only [aeval_boolAxiom, φ]
      calc
        (C (1 / 2 : ℝ) * (1 + X v)) ^ 2 - C (1 / 2 : ℝ) * (1 + X v)
            = C (1 / 4 : ℝ) * (1 + X v) ^ 2 - C (1 / 4 : ℝ) * 2 * (1 + X v) := by
              rw [mul_pow, hquarter, hch]
        _ = C (1 / 4 : ℝ) * (X v ^ 2 - 1) := by ring
  have hφ_compl : ∀ v : V,
      aeval φ (1 - X (Lit.pos v) - X (Lit.neg v) : MvPolynomial (Lit V) ℝ) = 0 := by
    intro v
    simp only [map_sub, map_one, aeval_X, φ]
    calc
      1 - C (1 / 2 : ℝ) * (1 - X v) - C (1 / 2 : ℝ) * (1 + X v)
          = 1 - C (1 / 2 : ℝ) * 2 := by ring
      _ = 0 := by rw [hhalf, sub_self]
  obtain ⟨π, hπ⟩ := href
  obtain ⟨hmul, hsq⟩ := SosProof.degree_le_iff.mp hπ
  let F := (us.map fun u ↦ xorConstraintPoly (bipartiteNeighbors adj u) (b u)) ++ twinBoolAxioms V
  let pairOf (i : Fin F.length) : Option (MvPolynomial V ℝ × MvPolynomial V ℝ) := by
    classical
    exact
      if h : ∃ u ∈ us, F.get i = xorConstraintPoly (bipartiteNeighbors adj u) (b u) then
        some (aeval φ (π.mult i), aeval φ (F.get i))
      else if hb : ∃ l : Lit V, F.get i = boolAxiom ℝ l then
        let l := Classical.choose hb
        some (C (1 / 4 : ℝ) * aeval φ (π.mult i), X l.1 ^ 2 - 1)
      else
        none
  let L := (List.finRange F.length).filterMap pairOf
  refine SOS.RefutableInDegree.of_list L ?_ (π.squares.map fun s ↦ (1, aeval φ s))
    (by simp) ?_ ?_
  · intro p hp
    obtain ⟨i, _, hpi⟩ := List.mem_filterMap.mp hp
    dsimp only [pairOf] at hpi
    split_ifs at hpi with h hb
    · obtain ⟨rfl⟩ := Option.some.inj hpi
      obtain ⟨u, hu, hfi⟩ := h
      refine ⟨?_, ?_⟩
      · rw [hfi, hφ_xor]
        exact ParitySystem.parityPoly_mem_toPolys (List.mem_map_of_mem hu)
      · rw [← map_mul]
        exact (totalDegree_aeval_le_mul hφ_deg _).trans (by simpa using hmul i)
    · obtain ⟨rfl⟩ := Option.some.inj hpi
      let l₀ : Lit V := Classical.choose hb
      have hl : F.get i = boolAxiom ℝ l₀ := Classical.choose_spec hb
      refine ⟨ParitySystem.X_sq_sub_one_mem_toPolys _ _, ?_⟩
      have heq : C (1 / 4 : ℝ) * aeval φ (π.mult i) * (X l₀.1 ^ 2 - 1) =
          aeval φ (π.mult i * F.get i) := by
        rw [map_mul, hl, hφ_bool]; ring
      rw [heq]
      exact (totalDegree_aeval_le_mul hφ_deg _).trans (by simpa using hmul i)
  · intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
    exact (Nat.mul_le_mul_left 2 (by simpa using totalDegree_aeval_le_mul hφ_deg s)).trans
      (hsq s hs)
  · have heq := congrArg (aeval φ) π.eq
    simp only [map_add, map_sum, map_mul, map_list_sum, List.map_map, map_neg, map_one] at heq
    rw [← heq]
    congr 1
    · have hterm : ∀ i : Fin F.length,
          (match pairOf i with | some p => p.1 * p.2 | none => 0) =
          aeval φ (π.mult i) * aeval φ (F.get i) := by
        intro i
        dsimp only [pairOf]
        split_ifs with h hb
        · rfl
        · let l₀ : Lit V := Classical.choose hb
          have hl : F.get i = boolAxiom ℝ l₀ := Classical.choose_spec hb
          change C (1 / 4 : ℝ) * aeval φ (π.mult i) * (X l₀.1 ^ 2 - 1) = _
          rw [hl, hφ_bool]; ring
        · have hmem : F.get i ∈ F := List.get_mem F i
          rcases List.mem_append.mp hmem with h1 | h2
          · obtain ⟨u, hu, he⟩ := List.mem_map.mp h1
            exact absurd ⟨u, hu, he.symm⟩ h
          · obtain ⟨v, _, hm⟩ := List.mem_flatMap.mp h2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with hm | hm | hm
            · exact absurd ⟨Lit.pos v, hm⟩ hb
            · exact absurd ⟨Lit.neg v, hm⟩ hb
            · dsimp only; rw [hm, hφ_compl, mul_zero]
      have hfm : ∀ l : List (Fin F.length),
          ((l.filterMap pairOf).map fun p ↦ p.1 * p.2).sum =
          (l.map fun i ↦ aeval φ (π.mult i) * aeval φ (F.get i)).sum := by
        intro l
        induction l with
        | nil => simp
        | cons i is ih =>
          simp only [List.filterMap_cons, List.map_cons, List.sum_cons, ← hterm i]
          cases pairOf i <;> simp [ih]
      rw [hfm, Fin.sum_univ_def]
    · simp [List.map_map, Function.comp_def, map_pow]

/-- **Grigoriev's Sum-of-Squares degree lower bound for expanding XOR-CSPs**: if `(U, V, adj)`
is an `(r, k, (1 / 2 + δ) * k)`-expander with `0 < δ`, then for every right-hand side
`b : U → Bool` and every degree-`d` SoS refutation of `xorCspPolys adj b`, `δ * k * r ≤ d`. -/
theorem grigoriev_xor_sos_degree [Fintype U] {adj : U → V → Prop} {r k : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hexp : IsBipartiteExpander adj r k ((1 / 2 + δ) * k))
    (b : U → Bool) {d : ℕ} (href : SosRefutableInDegree (xorCspPolys adj b) d) :
    δ * (k : ℝ) * (r : ℝ) ≤ (d : ℝ) := by
  classical
  by_contra hlt
  push Not at hlt
  exact ParitySystem.not_sos_refutableInDegree_toPolys
    (not_derives_empty_true_of_isBipartiteExpander hδ hexp Finset.univ.toList b hlt)
    (refutableInDegree_paritySystem_of_xorCsp adj Finset.univ.toList b href)

/-- **Grigoriev's Sum-of-Squares degree lower bound for multilinear `{0, 1}` XOR subsystems**:
for any `(r, k, (1 / 2 + δ) * k)`-expander (`0 < δ`), any subset of constraints `us : List U`,
and any `b : U → Bool`, every degree-`d` SoS refutation of `xorMultilinPolys adj us b` satisfies
`δ * k * r ≤ d`. -/
theorem grigoriev_xor_multilin_sos_degree {adj : U → V → Prop} {r k : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hexp : IsBipartiteExpander adj r k ((1 / 2 + δ) * k))
    (us : List U) (b : U → Bool) {d : ℕ}
    (href : SosRefutableInDegree (xorMultilinPolys adj us b) d) :
    δ * (k : ℝ) * (r : ℝ) ≤ (d : ℝ) := by
  classical
  -- Embed plain variables `v ↦ X (Lit.pos v)` into twin-literal `xorConstraintPoly`.
  let ι : V → MvPolynomial (Lit V) ℝ := fun v ↦ X (Lit.pos v)
  have hι_deg : ∀ v : V, (ι v).totalDegree ≤ 1 := fun v ↦ totalDegree_var_le _
  have hι_eq : ∀ (S : Finset V) (c : Bool),
      aeval ι (xorBoolPoly S - C (if c then 1 else 0)) =
      C (-1 / 2 : ℝ) * xorConstraintPoly S c := by
    intro S c
    simp only [map_sub, map_mul, map_one, map_prod, map_ofNat, aeval_C, aeval_X,
      algebraMap_eq, xorBoolPoly, xorConstraintPoly, ι]
    have hcn : (C (-1 / 2 : ℝ) : MvPolynomial (Lit V) ℝ) = -C (1 / 2 : ℝ) := by
      rw [← map_neg]; norm_num
    have hch : C (1 / 2 : ℝ) * (2 : MvPolynomial (Lit V) ℝ) = 1 := by
      rw [show (2 : MvPolynomial (Lit V) ℝ) = C 2 from map_ofNat C 2, ← map_mul]; norm_num
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, map_zero, sub_zero, map_one, hcn]; ring
    · simp only [↓reduceIte, map_one, map_neg, hcn]
      set P : MvPolynomial (Lit V) ℝ := ∏ x ∈ S, (1 - 2 * X (Lit.pos x))
      calc
        C (1 / 2 : ℝ) * (1 - P) - 1
            = C (1 / 2 : ℝ) * (1 - P) - C (1 / 2 : ℝ) * 2 := by rw [hch]
        _ = -C (1 / 2 : ℝ) * (P - -1) := by ring
  obtain ⟨π, hπ⟩ := href
  obtain ⟨hmul, hsq⟩ := SosProof.degree_le_iff.mp hπ
  let F := xorMultilinPolys adj us b
  let G := (us.map fun u ↦ xorConstraintPoly (bipartiteNeighbors adj u) (b u)) ++ twinBoolAxioms V
  let pairOf (i : Fin F.length) : MvPolynomial (Lit V) ℝ × MvPolynomial (Lit V) ℝ :=
    if h : ∃ u ∈ us, F.get i = xorBoolPoly (bipartiteNeighbors adj u) - C (if b u then 1 else 0)
    then
      let u := Classical.choose h
      (C (-1 / 2 : ℝ) * aeval ι (π.mult i), xorConstraintPoly (bipartiteNeighbors adj u) (b u))
    else
      (aeval ι (π.mult i), aeval ι (F.get i))
  have hrefG : SosRefutableInDegree G d := by
    refine SosRefutableInDegree.of_list ((List.finRange F.length).map pairOf) ?_
      (π.squares.map (aeval ι)) ?_ ?_
    · intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      dsimp only [pairOf]
      split_ifs with h
      · let u₀ : U := Classical.choose h
        obtain ⟨hu, hfi⟩ : u₀ ∈ us ∧
            F.get i = xorBoolPoly (bipartiteNeighbors adj u₀) - C (if b u₀ then 1 else 0) :=
          Classical.choose_spec h
        refine ⟨List.mem_append_left _ (List.mem_map_of_mem hu), ?_⟩
        have heq : C (-1 / 2 : ℝ) * aeval ι (π.mult i) *
            xorConstraintPoly (bipartiteNeighbors adj u₀) (b u₀) =
            aeval ι (π.mult i * F.get i) := by
          rw [map_mul, hfi, hι_eq]; ring
        rw [heq]
        exact (totalDegree_aeval_le_mul hι_deg _).trans (by simpa using hmul i)
      · rcases List.mem_append.mp (List.get_mem F i) with h1 | h2
        · obtain ⟨u, hu, he⟩ := List.mem_map.mp h1
          exact absurd ⟨u, hu, he.symm⟩ h
        · obtain ⟨v, _, he⟩ := List.mem_map.mp h2
          refine ⟨?_, ?_⟩
          · rw [← he]
            have : aeval ι (boolAxiom ℝ v) = boolAxiom ℝ (Lit.pos v) := by
              rw [aeval_boolAxiom, boolAxiom_eq_sub]
            rw [this]
            exact List.mem_append_right _ (boolAxiom_mem_twinBoolAxioms (Lit.pos v))
          · rw [← map_mul]
            exact (totalDegree_aeval_le_mul hι_deg _).trans (by simpa using hmul i)
    · intro s hs
      obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
      exact (Nat.mul_le_mul_left 2 (by simpa using totalDegree_aeval_le_mul hι_deg s₀)).trans
        (hsq s₀ hs₀)
    · have heq := congrArg (aeval ι) π.eq
      simp only [map_add, map_sum, map_mul, map_list_sum, List.map_map, map_neg, map_one] at heq
      rw [← heq]
      congr 1
      · rw [List.map_map, Fin.sum_univ_def]
        congr 2; funext i
        dsimp only [Function.comp_apply, pairOf]
        split_ifs with h
        · let u₀ : U := Classical.choose h
          obtain ⟨_, hfi⟩ : u₀ ∈ us ∧
              F.get i = xorBoolPoly (bipartiteNeighbors adj u₀) - C (if b u₀ then 1 else 0) :=
            Classical.choose_spec h
          change C (-1 / 2 : ℝ) * aeval ι (π.mult i) *
            xorConstraintPoly (bipartiteNeighbors adj u₀) (b u₀) = _
          rw [hfi, hι_eq]; ring
        · rfl
      · simp [List.map_map, Function.comp_def, map_pow]
  by_contra hlt
  push Not at hlt
  exact ParitySystem.not_sos_refutableInDegree_toPolys
    (not_derives_empty_true_of_isBipartiteExpander hδ hexp us b hlt)
    (refutableInDegree_paritySystem_of_xorCsp adj us b hrefG)

/-- Specialization to `(r, 3, 2)`-expanders (`3`-XOR): since `2 = (1 / 2 + 1 / 6) * 3`, every SoS
refutation of `xorCspPolys adj b` has degree at least `r / 2`. -/
theorem grigoriev_three_xor_sos_degree [Fintype U] {adj : U → V → Prop} {r : ℕ}
    (hexp : IsBipartiteExpander adj r 3 2) (b : U → Bool) {d : ℕ}
    (href : SosRefutableInDegree (xorCspPolys adj b) d) :
    (r : ℝ) / 2 ≤ (d : ℝ) := by
  have hexp' : IsBipartiteExpander adj r 3 ((1 / 2 + 1 / 6) * (3 : ℕ)) := by
    convert hexp using 1; norm_num
  have h := grigoriev_xor_sos_degree (by norm_num : (0 : ℝ) < 1 / 6) hexp' b href
  push_cast at h
  linarith

/-- **Sharpness counterexample for expansion `c = 2` at arity `k = 4`**: for every `m ≥ 1`, the
disjoint union of `m` copies of `K_{2, 4}` is a `(2 * m, 4, 2)`-expander on `2 * m` left vertices
and `4 * m` right vertices, yet admits a right-hand side `b` whose twin-literal XOR-CSP
`xorCspPolys` has a Sum-of-Squares refutation of constant degree `4`. -/
theorem exists_two_expander_sosRefutableInDegree_four (m : ℕ) (hm : 1 ≤ m) :
    let adj : Fin m × Fin 2 → Fin m × Fin 4 → Prop := fun u v ↦ u.1 = v.1
    IsBipartiteExpander adj (2 * m) 4 2 ∧
    Fintype.card (Fin m × Fin 4) = 4 * m ∧
    ∃ b : Fin m × Fin 2 → Bool, SosRefutableInDegree (xorCspPolys adj b) 4 := by
  intro adj
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨i, a⟩
    have hset : bipartiteNeighbors adj (i, (0 : Fin 2)) =
        (Finset.univ : Finset (Fin 4)).map
          ⟨fun c ↦ (i, c), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
      ext ⟨j, c⟩
      simp only [mem_bipartiteNeighbors, adj, Finset.mem_map, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ ⟨c, Prod.ext h rfl⟩, fun ⟨_, h⟩ ↦ (Prod.mk.inj h).1⟩
    have heq : bipartiteNeighbors adj (i, a) = bipartiteNeighbors adj (i, 0) := by
      ext ⟨j, c⟩; simp [adj]
    rw [heq, hset, Finset.card_map, Finset.card_fin]
  · intro W _
    let I : Finset (Fin m) := W.image Prod.fst
    have hW_le : W.card ≤ 2 * I.card := by
      have hsub : W ⊆ I ×ˢ (Finset.univ : Finset (Fin 2)) := fun ⟨i, a⟩ h ↦
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst h, Finset.mem_univ a⟩
      calc
        W.card ≤ (I ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_le_card hsub
        _ = 2 * I.card := by rw [Finset.card_product, Finset.card_fin, Nat.mul_comm]
    have hN_eq : (bipartiteNeighborSet adj W).card = 4 * I.card := by
      have hset : bipartiteNeighborSet adj W = I ×ˢ (Finset.univ : Finset (Fin 4)) := by
        ext ⟨j, c⟩
        simp [mem_bipartiteNeighborSet, adj, I]
      rw [hset, Finset.card_product, Finset.card_fin, Nat.mul_comm]
    have hnat : 2 * W.card ≤ (bipartiteNeighborSet adj W).card := by omega
    exact_mod_cast hnat
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]
  · let i₀ : Fin m := ⟨0, hm⟩
    let u₀ : Fin m × Fin 2 := (i₀, 0)
    let u₁ : Fin m × Fin 2 := (i₀, 1)
    let b : Fin m × Fin 2 → Bool := fun u ↦ decide (u = u₁)
    have hN : bipartiteNeighbors adj u₁ = bipartiteNeighbors adj u₀ := by
      ext ⟨j, c⟩; simp [adj, u₀, u₁]
    have hb1 : b u₁ = true := by simp [b]
    have hb0 : b u₀ = false := by
      simp only [b, u₀, u₁, decide_eq_false_iff_not, Prod.mk.injEq, true_and]
      decide
    let p₀ := xorConstraintPoly (bipartiteNeighbors adj u₀) (b u₀)
    let p₁ := xorConstraintPoly (bipartiteNeighbors adj u₁) (b u₁)
    have hcard0 : (bipartiteNeighbors adj u₀).card = 4 := by
      have hset : bipartiteNeighbors adj u₀ =
          (Finset.univ : Finset (Fin 4)).map
            ⟨fun c ↦ (i₀, c), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
        ext ⟨j, c⟩
        simp only [mem_bipartiteNeighbors, adj, u₀, Finset.mem_map, Finset.mem_univ, true_and]
        exact ⟨fun h ↦ ⟨c, Prod.ext h rfl⟩, fun ⟨_, h⟩ ↦ (Prod.mk.inj h).1⟩
      rw [hset, Finset.card_map, Finset.card_fin]
    have hdeg_xor : ∀ (S : Finset (Fin m × Fin 4)) (c : Bool),
        S.card = 4 → (xorConstraintPoly S c).totalDegree ≤ 4 := by
      intro S c hSc
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      refine (totalDegree_finsetProd _ _).trans ?_
      calc
        ∑ v ∈ S, (1 - 2 * (X (Lit.pos v) : MvPolynomial _ ℝ)).totalDegree
            ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum fun v _ ↦
              (totalDegree_sub _ _).trans (max_le (by simp) (by
                rw [show (2 : MvPolynomial (Lit (Fin m × Fin 4)) ℝ) = C 2 from map_ofNat C 2]
                exact (totalDegree_mul _ _).trans
                  (by rw [totalDegree_C, zero_add]; exact totalDegree_var_le _)))
        _ = 4 := by simp [hSc]
    refine ⟨b, SosRefutableInDegree.of_list [(C (1 / 2 : ℝ), p₀), (C (-1 / 2 : ℝ), p₁)]
      ?_ [] (by simp) ?_⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · refine ⟨List.mem_append_left _ (List.mem_map_of_mem (Finset.mem_toList.mpr
            (Finset.mem_univ u₀))),
          (totalDegree_mul _ _).trans (by simpa using hdeg_xor _ _ hcard0)⟩
      · refine ⟨List.mem_append_left _ (List.mem_map_of_mem (Finset.mem_toList.mpr
            (Finset.mem_univ u₁))),
          (totalDegree_mul _ _).trans (by simpa [p₁, hN] using hdeg_xor _ _ hcard0)⟩
    · have hcn : (C (-1 / 2 : ℝ) : MvPolynomial (Lit (Fin m × Fin 4)) ℝ) = -C (1 / 2 : ℝ) := by
        rw [← map_neg]; norm_num
      have hch : (C (1 / 2 : ℝ) : MvPolynomial (Lit (Fin m × Fin 4)) ℝ) * C 2 = 1 := by
        rw [← map_mul]; norm_num
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, p₀, p₁,
        xorConstraintPoly, hN, hb0, hb1, Bool.false_eq_true, ↓reduceIte, map_one, map_neg, hcn]
      rw [show (C (1 / 2 : ℝ) * (∏ v ∈ bipartiteNeighbors adj u₀, (1 - 2 * X (Lit.pos v)) - 1) +
            -C (1 / 2 : ℝ) * (∏ v ∈ bipartiteNeighbors adj u₀, (1 - 2 * X (Lit.pos v)) - -1)) =
          -(C (1 / 2 : ℝ) * 2) by ring,
        show (2 : MvPolynomial (Lit (Fin m × Fin 4)) ℝ) = C 2 from map_ofNat C 2, hch]

end XorEncodings

end CslibFrontier.ProofComplexity
