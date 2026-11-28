/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ROABP
public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closure Properties and Whitebox Identity Testing for Ordered ROABPs

This module develops structural closure operations and whitebox polynomial identity testing for
fixed-order read-once oblivious algebraic branching programs (`IsOrderedROABP`).

Given a permutation `σ : Equiv.Perm (Fin n)` specifying the variable order, a multivariate
polynomial `f ∈ MvPolynomial (Fin n) F` satisfies `IsOrderedROABP σ w δ f` if `f` is computed as an
`(s, t)`-entry of `roabpProd M (List.ofFn σ)` where every univariate layer entry `M i a b` has
degree at most `δ`.

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP`: fixed-order width-`w`, layer-degree-`≤ δ`
  read-once oblivious algebraic branching program predicate.
* `CslibFrontier.Circuits.Arithmetic.roabpSuffixSubspace`: recursive `≤ w`-dimensional `F`-subspace
  spanned by suffix monomial coefficient vectors of an ROABP.

## Main results

* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.isROABP`: every ordered ROABP is an `IsROABP`.
* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.mono_width` and
  `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.mono_deg`: monotonicity in width and layer
  degree.
* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.add`: addition in a shared variable order adds
  widths (`w₁ + w₂`).
* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.mul`: multiplication in a shared variable order
  multiplies widths (`w₁ * w₂`) via Kronecker products of layer matrices.
* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.homogeneousComponent`: extracting the
  degree-`k` homogeneous component (`k ≤ d`) blows up width by at most `d + 1`.
* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.iterate_pderiv`: iterated partial
  differentiation preserves width and variable order.
* `CslibFrontier.Circuits.Arithmetic.IsOrderedROABP.sum_univariate_pow`: the `k`-th power of a sum
  of univariate polynomials of degree at most `δ` is computed in width `k + 1` in *every* variable
  order via upper-triangular Pascal transfer matrices.
* `CslibFrontier.Circuits.Arithmetic.roabpProd_eq_zero_iff_roabpSuffixSubspace`: whitebox
  characterization of `roabpProd M l s t = 0` via `roabpSuffixSubspace` of dimension at most `w`.
-/

public section

open scoped Polynomial

namespace CslibFrontier.Circuits.Arithmetic

open MvPolynomial Cslib.Circuits.Arithmetic

/-- `f` is computed by a read-once oblivious algebraic branching program of width `w` and layer
degree at most `δ` reading the variables in the order `List.ofFn σ`. -/
@[expose] def IsOrderedROABP {F : Type*} [Field F] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (w δ : ℕ) (f : MvPolynomial (Fin n) F) : Prop :=
  ∃ (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (s t : Fin w),
    (∀ i a b, (M i a b).natDegree ≤ δ) ∧ f = roabpProd M (List.ofFn σ) s t

/-- Every fixed-order ROABP is an `IsROABP`. -/
theorem IsOrderedROABP.isROABP {F : Type*} [Field F] {n w δ : ℕ}
    {σ : Equiv.Perm (Fin n)} {f : MvPolynomial (Fin n) F} (hf : IsOrderedROABP σ w δ f) :
    IsROABP w δ f := by
  rcases hf with ⟨M, s, t, hdeg, rfl⟩
  exact ⟨List.ofFn σ, M, s, t, List.nodup_ofFn.mpr σ.injective, hdeg, rfl⟩

/-- Layer-degree monotonicity for `IsOrderedROABP`. -/
theorem IsOrderedROABP.mono_deg {F : Type*} [Field F] {n w δ₁ δ₂ : ℕ}
    {σ : Equiv.Perm (Fin n)} {f : MvPolynomial (Fin n) F}
    (hδ : δ₁ ≤ δ₂) (hf : IsOrderedROABP σ w δ₁ f) :
    IsOrderedROABP σ w δ₂ f := by
  rcases hf with ⟨M, s, t, hM, rfl⟩
  exact ⟨M, s, t, fun i a b ↦ (hM i a b).trans hδ, rfl⟩

private theorem roabpProd_nil {F : Type*} [Field F] {n w : ℕ}
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) :
    roabpProd M [] = 1 := rfl

private theorem roabpProd_cons {F : Type*} [Field F] {n w : ℕ}
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (i : Fin n) (rest : List (Fin n)) :
    roabpProd M (i :: rest) =
      (M i).map (Polynomial.aeval (X i)) * roabpProd M rest := by
  simp [roabpProd]

private theorem roabpProd_append {F : Type*} [Field F] {n w : ℕ}
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (l₁ l₂ : List (Fin n)) :
    roabpProd M (l₁ ++ l₂) = roabpProd M l₁ * roabpProd M l₂ := by
  simp [roabpProd]

private noncomputable def gRoabpProd {F : Type*} [Field F] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Fin n → Matrix ι ι F[X]) (l : List (Fin n)) :
    Matrix ι ι (MvPolynomial (Fin n) F) :=
  (l.map fun i ↦ (M i).map (Polynomial.aeval (X i : MvPolynomial (Fin n) F))).prod

private theorem gRoabpProd_nil {F : Type*} [Field F] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Fin n → Matrix ι ι F[X]) :
    gRoabpProd M [] = 1 := rfl

private theorem gRoabpProd_cons {F : Type*} [Field F] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Fin n → Matrix ι ι F[X]) (i : Fin n) (rest : List (Fin n)) :
    gRoabpProd M (i :: rest) =
      (M i).map (Polynomial.aeval (X i)) * gRoabpProd M rest := by
  simp [gRoabpProd]

private theorem gRoabpProd_append {F : Type*} [Field F] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Fin n → Matrix ι ι F[X]) (l₁ l₂ : List (Fin n)) :
    gRoabpProd M (l₁ ++ l₂) = gRoabpProd M l₁ * gRoabpProd M l₂ := by
  simp [gRoabpProd]

private theorem gRoabpProd_reindex {F : Type*} [Field F] {n w : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin w) (M : Fin n → Matrix ι ι F[X]) :
    ∀ (l : List (Fin n)) (s t : ι),
      roabpProd (fun i ↦ Matrix.reindex e e (M i)) l (e s) (e t) = gRoabpProd M l s t
  | [], s, t => by
    simp [roabpProd_nil, gRoabpProd_nil, Matrix.one_apply, e.injective.eq_iff]
  | i :: rest, s, t => by
    rw [roabpProd_cons, gRoabpProd_cons, Matrix.mul_apply, Matrix.mul_apply, ← e.sum_comp]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [gRoabpProd_reindex e M rest u t]
    simp [Matrix.reindex_apply]

/-- Width monotonicity for `IsOrderedROABP`. -/
theorem IsOrderedROABP.mono_width {F : Type*} [Field F] {n w₁ w₂ δ : ℕ}
    {σ : Equiv.Perm (Fin n)} {f : MvPolynomial (Fin n) F}
    (hw : w₁ ≤ w₂) (hf : IsOrderedROABP σ w₁ δ f) :
    IsOrderedROABP σ w₂ δ f := by
  rcases hf with ⟨M, s, t, hM, rfl⟩
  let pad : Fin n → Matrix (Fin w₂) (Fin w₂) F[X] := fun i a b ↦
    if ha : a.1 < w₁ then
      if hb : b.1 < w₁ then M i ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0
    else 0
  have hpad_deg : ∀ i a b, (pad i a b).natDegree ≤ δ := by
    intro i a b; dsimp [pad]; split_ifs with ha hb
    · exact hM i ⟨a.1, ha⟩ ⟨b.1, hb⟩
    · simp
    · simp
  have hpad_prod :
      ∀ (l : List (Fin n)) (u v : Fin w₁),
        roabpProd pad l (Fin.castLE hw u) (Fin.castLE hw v) = roabpProd M l u v := by
    intro l
    induction l with
    | nil => intro u v; simp [roabpProd_nil, Matrix.one_apply, Fin.ext_iff]
    | cons i rest ih =>
      intro u v
      rw [roabpProd_cons, roabpProd_cons, Matrix.mul_apply, Matrix.mul_apply]
      have hsplit :
          (∑ k : Fin w₂,
              (pad i).map (Polynomial.aeval (X i)) (Fin.castLE hw u) k *
                roabpProd pad rest k (Fin.castLE hw v)) =
            ∑ k ∈ Finset.univ.filter (fun k : Fin w₂ ↦ k.1 < w₁),
              (pad i).map (Polynomial.aeval (X i)) (Fin.castLE hw u) k *
                roabpProd pad rest k (Fin.castLE hw v) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk ↦ ?_
        rw [Finset.mem_filter] at hk
        have hnot : ¬ k.1 < w₁ := fun hlt ↦ hk ⟨Finset.mem_univ k, hlt⟩
        have h0 : pad i (Fin.castLE hw u) k = 0 := by
          dsimp only [pad]
          split <;> rfl
        rw [Matrix.map_apply, h0, map_zero, zero_mul]
      rw [hsplit]
      refine Finset.sum_bij
        (fun (k : Fin w₂) (hk : k ∈ Finset.univ.filter (fun k : Fin w₂ ↦ k.1 < w₁)) ↦
          (⟨k.1, (Finset.mem_filter.mp hk).2⟩ : Fin w₁))
        (fun _ _ ↦ Finset.mem_univ _)
        (fun (k₁ : Fin w₂) _ (k₂ : Fin w₂) _ heq ↦
          Fin.ext (congrArg (Fin.val : Fin w₁ → ℕ) heq))
        (fun r _ ↦ ⟨Fin.castLE hw r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.isLt⟩, rfl⟩)
        fun k hk ↦ ?_
      have hk_lt : k.1 < w₁ := (Finset.mem_filter.mp hk).2
      have hcast : Fin.castLE hw ⟨k.1, hk_lt⟩ = k := Fin.ext rfl
      have hpad_eq : pad i (Fin.castLE hw u) k = M i u ⟨k.1, hk_lt⟩ := by
        dsimp only [pad]
        split
        · rfl
        · next hu_out => exact False.elim (hu_out u.isLt)
      rw [← ih ⟨k.1, hk_lt⟩ v, hcast, Matrix.map_apply, Matrix.map_apply, hpad_eq]
  exact ⟨pad, Fin.castLE hw s, Fin.castLE hw t, hpad_deg, (hpad_prod (List.ofFn σ) s t).symm⟩

private theorem exists_snoc_of_ne_nil {α : Type*} :
    ∀ l : List α, l ≠ [] → ∃ (mid : List α) (last : α), l = mid ++ [last]
  | [], h => False.elim (h rfl)
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: zs, _ => by
    rcases exists_snoc_of_ne_nil (y :: zs) (List.cons_ne_nil y zs) with ⟨mid, last, h⟩
    exact ⟨x :: mid, last, by simp [h]⟩

/-- Addition closure for `IsOrderedROABP`: for `1 ≤ n`, adding ordered ROABPs of widths `w₁` and
`w₂` in the same variable order `σ` yields an ordered ROABP of width `w₁ + w₂`. -/
theorem IsOrderedROABP.add {F : Type*} [Field F] {n w₁ w₂ δ : ℕ} (hn : 1 ≤ n)
    {σ : Equiv.Perm (Fin n)} {f g : MvPolynomial (Fin n) F}
    (hf : IsOrderedROABP σ w₁ δ f) (hg : IsOrderedROABP σ w₂ δ g) :
    IsOrderedROABP σ (w₁ + w₂) δ (f + g) := by
  classical
  rcases hf with ⟨M₁, s₁, t₁, hM₁, hf_prod⟩
  rcases hg with ⟨M₂, s₂, t₂, hM₂, hg_prod⟩
  have hlen : (List.ofFn σ).length = n := List.length_ofFn
  have hnodup : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  rcases eq_or_lt_of_le hn with rfl | hn2
  · cases hl : List.ofFn σ with
    | nil => rw [hl] at hlen; simp at hlen
    | cons i₀ rest =>
      have hrest_nil : rest = [] :=
        List.eq_nil_of_length_eq_zero (by rw [hl, List.length_cons] at hlen; omega)
      subst hrest_nil
      let B : Fin 1 → Matrix (Fin w₁ ⊕ Fin w₂) (Fin w₁ ⊕ Fin w₂) F[X] := fun i a b ↦
        if a = Sum.inl s₁ ∧ b = Sum.inl t₁ then M₁ i s₁ t₁ + M₂ i s₂ t₂ else 0
      have hB_deg : ∀ i a b, (B i a b).natDegree ≤ δ := by
        intro i a b; dsimp [B]; split_ifs
        · exact (Polynomial.natDegree_add_le _ _).trans (max_le (hM₁ i s₁ t₁) (hM₂ i s₂ t₂))
        · simp
      have heq : f + g = gRoabpProd B (List.ofFn σ) (Sum.inl s₁) (Sum.inl t₁) := by
        rw [hf_prod, hg_prod, hl, roabpProd_cons, roabpProd_nil, mul_one,
          roabpProd_cons, roabpProd_nil, mul_one, gRoabpProd_cons, gRoabpProd_nil, mul_one,
          Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
        dsimp only [B]
        rw [ite_eq_left ⟨rfl, rfl⟩, map_add]
      refine ⟨fun i ↦ Matrix.reindex finSumFinEquiv finSumFinEquiv (B i),
        finSumFinEquiv (Sum.inl s₁), finSumFinEquiv (Sum.inl t₁), fun i a b ↦ ?_, ?_⟩
      · simpa [Matrix.reindex_apply] using hB_deg i _ _
      · exact heq.trans (gRoabpProd_reindex finSumFinEquiv B (List.ofFn σ) _ _).symm
  · cases hl : List.ofFn σ with
    | nil => rw [hl] at hlen; simp at hlen; omega
    | cons i₀ rest =>
      have hrest_ne : rest ≠ [] := fun hnil ↦ by rw [hl, hnil] at hlen; simp at hlen; omega
      rcases exists_snoc_of_ne_nil rest hrest_ne with ⟨mid, i_last, hrest_eq⟩
      rw [hl, hrest_eq] at hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hi₀_not, hmid_nodup⟩
      rw [List.mem_append, List.mem_singleton, not_or] at hi₀_not
      rcases hi₀_not with ⟨hi₀_mid, hi₀_last⟩
      have hlast_mid : i_last ∉ mid := by
        rw [List.nodup_append] at hmid_nodup
        exact fun hm ↦ hmid_nodup.2.2 i_last hm i_last (List.mem_singleton_self _) rfl
      let B : Fin n → Matrix (Fin w₁ ⊕ Fin w₂) (Fin w₁ ⊕ Fin w₂) F[X] := fun i ↦
        if i = i₀ then
          Matrix.fromBlocks (M₁ i) (Matrix.of fun a b ↦ if a = s₁ then M₂ i s₂ b else 0) 0 0
        else if i = i_last then
          Matrix.fromBlocks (M₁ i) 0 (Matrix.of fun a b ↦ if b = t₁ then M₂ i a t₂ else 0) 0
        else
          Matrix.fromBlocks (M₁ i) 0 0 (M₂ i)
      have hB_deg : ∀ i a b, (B i a b).natDegree ≤ δ := by
        intro i a b; dsimp [B]
        split_ifs with h1 h2
        · cases a <;> cases b <;> simp only [Matrix.fromBlocks_apply₁₁,
            Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Matrix.of_apply, Matrix.zero_apply]
          · exact hM₁ i _ _
          · split_ifs <;> [exact hM₂ i _ _; simp]
          · simp
          · simp
        · cases a <;> cases b <;> simp only [Matrix.fromBlocks_apply₁₁,
            Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Matrix.of_apply, Matrix.zero_apply]
          · exact hM₁ i _ _
          · simp
          · split_ifs <;> [exact hM₂ i _ _; simp]
          · simp
        · cases a <;> cases b <;> simp only [Matrix.fromBlocks_apply₁₁,
            Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Matrix.zero_apply]
          · exact hM₁ i _ _
          · simp
          · simp
          · exact hM₂ i _ _
      let mapX (i : Fin n) {ι₁ ι₂ : Type} (A : Matrix ι₁ ι₂ F[X]) :
          Matrix ι₁ ι₂ (MvPolynomial (Fin n) F) :=
        A.map (Polynomial.aeval (X i : MvPolynomial (Fin n) F))
      have hmap_blocks : ∀ (i : Fin n) (A₁₁ : Matrix (Fin w₁) (Fin w₁) F[X])
          (A₁₂ : Matrix (Fin w₁) (Fin w₂) F[X]) (A₂₁ : Matrix (Fin w₂) (Fin w₁) F[X])
          (A₂₂ : Matrix (Fin w₂) (Fin w₂) F[X]),
          mapX i (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) =
            Matrix.fromBlocks (mapX i A₁₁) (mapX i A₁₂) (mapX i A₂₁) (mapX i A₂₂) := by
        intro i A₁₁ A₁₂ A₂₁ A₂₂; ext (a | a) (b | b) <;> rfl
      have hmap_zero : ∀ {ι₁ ι₂ : Type} (i : Fin n), mapX i (0 : Matrix ι₁ ι₂ F[X]) = 0 := by
        intro ι₁ ι₂ i; ext a b; simp [mapX]
      have hmid_prod :
          ∀ l : List (Fin n), (∀ j ∈ l, j ≠ i₀ ∧ j ≠ i_last) →
            gRoabpProd B l = Matrix.fromBlocks (roabpProd M₁ l) 0 0 (roabpProd M₂ l) := by
        intro l
        induction l with
        | nil =>
          intro _; ext (a | a) (b | b) <;> simp [gRoabpProd_nil, roabpProd_nil, Matrix.one_apply]
        | cons j js ih =>
          intro hj
          rcases hj j List.mem_cons_self with ⟨hj0, hjlast⟩
          have hBj : mapX j (B j) = Matrix.fromBlocks (mapX j (M₁ j)) 0 0 (mapX j (M₂ j)) := by
            dsimp [B]
            rw [ite_eq_right hj0, ite_eq_right hjlast, hmap_blocks, hmap_zero, hmap_zero]
          rw [gRoabpProd_cons, ih (fun k hk ↦ hj k (List.mem_cons_of_mem _ hk)),
            show (B j).map (Polynomial.aeval (X j)) = mapX j (B j) from rfl, hBj,
            Matrix.fromBlocks_multiply]
          simp [roabpProd_cons, mapX]
      have hmid_avoid : ∀ j ∈ mid, j ≠ i₀ ∧ j ≠ i_last :=
        fun j hj ↦ ⟨fun h ↦ hi₀_mid (h ▸ hj), fun h ↦ hlast_mid (h ▸ hj)⟩
      have hBi₀ :
          mapX i₀ (B i₀) =
            Matrix.fromBlocks (mapX i₀ (M₁ i₀))
              (mapX i₀ (Matrix.of fun a b ↦ if a = s₁ then M₂ i₀ s₂ b else 0)) 0 0 := by
        dsimp [B]; rw [ite_eq_left rfl, hmap_blocks, hmap_zero, hmap_zero]
      have hBlast :
          mapX i_last (B i_last) =
            Matrix.fromBlocks (mapX i_last (M₁ i_last)) 0
              (mapX i_last (Matrix.of fun a b ↦ if b = t₁ then M₂ i_last a t₂ else 0)) 0 := by
        dsimp [B]
        rw [ite_eq_right (Ne.symm hi₀_last), ite_eq_left rfl, hmap_blocks, hmap_zero, hmap_zero]
      have heq : f + g = gRoabpProd B (List.ofFn σ) (Sum.inl s₁) (Sum.inl t₁) := by
        rw [hl, hrest_eq, gRoabpProd_cons, gRoabpProd_append, gRoabpProd_cons, gRoabpProd_nil,
          mul_one, hmid_prod mid hmid_avoid,
          show (B i₀).map (Polynomial.aeval (X i₀)) = mapX i₀ (B i₀) from rfl,
          show (B i_last).map (Polynomial.aeval (X i_last)) = mapX i_last (B i_last) from rfl,
          hBi₀, hBlast, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.mul_zero, Matrix.zero_mul, add_zero,
          zero_add, Matrix.add_apply]
        congr 1
        · rw [hf_prod, hl, hrest_eq, roabpProd_cons, roabpProd_append, roabpProd_cons,
            roabpProd_nil, mul_one]
        · rw [hg_prod, hl, hrest_eq, roabpProd_cons, roabpProd_append, roabpProd_cons,
            roabpProd_nil, mul_one]
          change ((mapX i₀ (M₂ i₀) * (roabpProd M₂ mid * mapX i_last (M₂ i_last))) s₂ t₂) = _
          simp only [Matrix.mul_apply, mapX, Matrix.map_apply, Matrix.of_apply, ite_true]
      refine ⟨fun i ↦ Matrix.reindex finSumFinEquiv finSumFinEquiv (B i),
        finSumFinEquiv (Sum.inl s₁), finSumFinEquiv (Sum.inl t₁), fun i a b ↦ ?_, ?_⟩
      · simpa [Matrix.reindex_apply] using hB_deg i _ _
      · exact heq.trans (gRoabpProd_reindex finSumFinEquiv B (List.ofFn σ) _ _).symm

/-- Multiplication closure for `IsOrderedROABP`: multiplying ordered ROABPs of widths `w₁, w₂` and
layer degrees `δ₁, δ₂` in the same variable order `σ` yields an ordered ROABP of width `w₁ * w₂` and
layer degree `δ₁ + δ₂`. -/
theorem IsOrderedROABP.mul {F : Type*} [Field F] {n w₁ w₂ δ₁ δ₂ : ℕ}
    {σ : Equiv.Perm (Fin n)} {f g : MvPolynomial (Fin n) F}
    (hf : IsOrderedROABP σ w₁ δ₁ f) (hg : IsOrderedROABP σ w₂ δ₂ g) :
    IsOrderedROABP σ (w₁ * w₂) (δ₁ + δ₂) (f * g) := by
  rcases hf with ⟨M₁, s₁, t₁, hM₁, hf_prod⟩
  rcases hg with ⟨M₂, s₂, t₂, hM₂, hg_prod⟩
  let B : Fin n → Matrix (Fin w₁ × Fin w₂) (Fin w₁ × Fin w₂) F[X] :=
    fun i p q ↦ M₁ i p.1 q.1 * M₂ i p.2 q.2
  have hkron :
      ∀ (l : List (Fin n)) (u₁ v₁ : Fin w₁) (u₂ v₂ : Fin w₂),
        gRoabpProd B l (u₁, u₂) (v₁, v₂) = roabpProd M₁ l u₁ v₁ * roabpProd M₂ l u₂ v₂ := by
    intro l
    induction l with
    | nil =>
      intro u₁ v₁ u₂ v₂
      simp only [gRoabpProd_nil, roabpProd_nil, Matrix.one_apply, Prod.mk.injEq]
      by_cases h1 : u₁ = v₁ <;> by_cases h2 : u₂ = v₂ <;> simp [h1, h2]
    | cons i rest ih =>
      intro u₁ v₁ u₂ v₂
      rw [gRoabpProd_cons, roabpProd_cons, roabpProd_cons,
        Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
        Fintype.sum_prod_type, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k₁ _ ↦ Finset.sum_congr rfl fun k₂ _ ↦ ?_
      rw [ih k₁ v₁ k₂ v₂, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      dsimp only [B]
      rw [map_mul]
      ring
  refine ⟨fun i ↦ Matrix.reindex finProdFinEquiv finProdFinEquiv (B i),
    finProdFinEquiv (s₁, s₂), finProdFinEquiv (t₁, t₂), fun i a b ↦ ?_, ?_⟩
  · dsimp [B, Matrix.reindex_apply]
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hM₁ i _ _) (hM₂ i _ _))
  · rw [hf_prod, hg_prod, ← hkron, gRoabpProd_reindex]

/-- Homogeneous component closure for `IsOrderedROABP`: for `k ≤ d`, the degree-`k` homogeneous
component of `f` has an ordered ROABP of width `(d + 1) * w` and layer degree at most `d`. -/
theorem IsOrderedROABP.homogeneousComponent {F : Type*} [Field F] {n w δ d k : ℕ} (hk : k ≤ d)
    {σ : Equiv.Perm (Fin n)} {f : MvPolynomial (Fin n) F}
    (hf : IsOrderedROABP σ w δ f) :
    IsOrderedROABP σ ((d + 1) * w) d (MvPolynomial.homogeneousComponent k f) := by
  classical
  rcases hf with ⟨M, s₀, t₀, _, hf_prod⟩
  let B : Fin n → Matrix (Fin (d + 1) × Fin w) (Fin (d + 1) × Fin w) F[X] :=
    fun i p q ↦
      if p.1.val ≤ q.1.val then
        Polynomial.monomial (q.1.val - p.1.val) ((M i p.2 q.2).coeff (q.1.val - p.1.val))
      else
        0
  let eqv : Fin (d + 1) × Fin w ≃ Fin ((d + 1) * w) := finProdFinEquiv
  let B' : Fin n → Matrix (Fin ((d + 1) * w)) (Fin ((d + 1) * w)) F[X] :=
    fun i ↦ Matrix.reindex eqv eqv (B i)
  have hB'_deg : ∀ i a b, (B' i a b).natDegree ≤ d := by
    intro i a b
    dsimp only [B']
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    dsimp [B]
    split_ifs with hle
    · refine (Polynomial.natDegree_monomial_le _).trans ?_
      have hlt := (eqv.symm b).1.isLt
      omega
    · simp
  let homStep (i : Fin n) (e : ℕ) :
      Matrix (Fin (d + 1) × Fin w) (Fin (d + 1) × Fin w) F :=
    fun p q ↦ if p.1.val + e = q.1.val then (M i p.2 q.2).coeff e else 0
  have hB_coeff : ∀ (i : Fin n) (e : ℕ) (p q : Fin (d + 1) × Fin w),
      (B i p q).coeff e = homStep i e p q := by
    intro i e p q
    dsimp [B, homStep]
    by_cases hle : p.1.val ≤ q.1.val
    · rw [ite_eq_left hle]
      by_cases hsub : q.1.val - p.1.val = e
      · have hadd : p.1.val + e = q.1.val := by omega
        rw [hsub, Polynomial.coeff_monomial_same, ite_eq_left hadd]
      · have hadd : ¬ p.1.val + e = q.1.val := by omega
        rw [Polynomial.coeff_monomial, Finsupp.single_eq_of_ne (Ne.symm hsub), ite_eq_right hadd]
    · have hadd : ¬ p.1.val + e = q.1.val := by omega
      rw [ite_eq_right hle, Polynomial.coeff_zero, ite_eq_right hadd]
  have hstep_prod :
      ∀ (l : List (Fin n)) (m : Fin n →₀ ℕ) (a b : Fin (d + 1)) (u v : Fin w),
        ((l.map fun i ↦ homStep i (m i)).prod) (a, u) (b, v) =
          if a.val + (l.map (fun i ↦ m i)).sum = b.val then
            ((l.map fun i ↦ layerCoeff M i (m i)).prod) u v
          else
            0 := by
    intro l
    induction l with
    | nil =>
      intro m a b u v
      simp only [List.map_nil, List.prod_nil, List.sum_nil, add_zero, Matrix.one_apply,
        Prod.mk.injEq, Fin.ext_iff]
      by_cases hab : a.val = b.val <;> by_cases huv : u = v <;> simp [hab, huv]
    | cons i rest ih =>
      intro m a b u v
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_prod_type]
      simp_rw [ih m _ b _ v]
      rw [List.map_cons, List.sum_cons]
      by_cases htot : a.val + (m i + (rest.map (fun j ↦ m j)).sum) = b.val
      · rw [ite_eq_left htot]
        have hlt_d1 : a.val + m i < d + 1 := by have hb_lt := b.isLt; omega
        let c₀ : Fin (d + 1) := ⟨a.val + m i, hlt_d1⟩
        rw [Finset.sum_eq_single c₀]
        · have hc₀ : c₀.val + (rest.map (fun j ↦ m j)).sum = b.val := by dsimp [c₀]; omega
          rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          simp [homStep, layerCoeff, c₀, hc₀]
        · intro c _ hc_ne
          refine Finset.sum_eq_zero fun r _ ↦ ?_
          have hnot_eq : ¬ a.val + m i = c.val := fun heq ↦ hc_ne (Fin.ext heq.symm)
          simp [homStep, hnot_eq]
        · intro hnot; exact False.elim (hnot (Finset.mem_univ c₀))
      · rw [ite_eq_right htot]
        refine Finset.sum_eq_zero fun c _ ↦ Finset.sum_eq_zero fun r _ ↦ ?_
        by_cases hac : a.val + m i = c.val
        · have hnot_rest : ¬ c.val + (rest.map (fun j ↦ m j)).sum = b.val := by omega
          simp [homStep, hac, hnot_rest]
        · simp [homStep, hac]
  refine ⟨B', eqv (⟨0, Nat.zero_lt_succ d⟩, s₀), eqv (⟨k, Nat.lt_succ_of_le hk⟩, t₀),
    hB'_deg, ?_⟩
  have hnodup : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hmem_all : ∀ i : Fin n, i ∈ List.ofFn σ :=
    fun i ↦ List.mem_ofFn.mpr ⟨σ.symm i, σ.apply_symm_apply i⟩
  ext m
  have hm0 : ∀ i ∉ List.ofFn σ, m i = 0 := fun i hi ↦ False.elim (hi (hmem_all i))
  rw [coeff_roabpProd B' hnodup m hm0]
  have hreindex_prod :
      ∀ (l : List (Fin n)) (p q : Fin (d + 1) × Fin w),
        ((l.map fun i ↦ layerCoeff B' i (m i)).prod) (eqv p) (eqv q) =
          ((l.map fun i ↦ homStep i (m i)).prod) p q := by
    intro l
    induction l with
    | nil => intro p q; simp [Matrix.one_apply, eqv.injective.eq_iff]
    | cons i rest ih =>
      intro p q
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        Matrix.mul_apply, Matrix.mul_apply, ← eqv.sum_comp]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [ih r q]
      simp [layerCoeff, B', hB_coeff]
  rw [hreindex_prod, hstep_prod]
  have hsum_deg : ((List.ofFn σ).map (fun i ↦ m i)).sum = m.degree := by
    rw [List.map_ofFn, List.sum_ofFn]
    dsimp only [Function.comp_def]
    rw [Equiv.sum_comp σ, Finsupp.degree_apply]
    symm
    exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦
      Finsupp.notMem_support_iff.mp hi
  rw [zero_add, hsum_deg, ← coeff_roabpProd M hnodup m hm0 s₀ t₀, ← hf_prod,
    coeff_homogeneousComponent]

private theorem list_prod_smul_unique {F : Type*} [Field F] {n w : ℕ} (z : Fin n) (c : F)
    (A B : Fin n → Matrix (Fin w) (Fin w) F)
    (hBz : B z = c • A z) (hBne : ∀ i, i ≠ z → B i = A i) :
    ∀ {l : List (Fin n)}, l.Nodup → z ∈ l → (l.map B).prod = c • (l.map A).prod
  | [], _, hz => False.elim (List.not_mem_nil hz)
  | i :: rest, hl, hz => by
    rcases List.nodup_cons.mp hl with ⟨hi_not_rest, hrest_nodup⟩
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hz with rfl | hz_rest
    · have hrest_eq : rest.map B = rest.map A :=
        List.map_congr_left fun j hj ↦ hBne j (fun h ↦ hi_not_rest (h ▸ hj))
      rw [hBz, hrest_eq, Matrix.smul_mul]
    · have hij : i ≠ z := fun h ↦ hi_not_rest (h ▸ hz_rest)
      rw [hBne i hij, list_prod_smul_unique z c A B hBz hBne hrest_nodup hz_rest, Matrix.mul_smul]

/-- Iterated partial derivative closure for `IsOrderedROABP`: differentiating layer `z` `e` times
computes `(pderiv z)^[e] f` in the same variable order `σ` and width `w` with layer degree `≤ δ`. -/
theorem IsOrderedROABP.iterate_pderiv {F : Type*} [Field F] {n w δ : ℕ}
    {σ : Equiv.Perm (Fin n)} (z : Fin n) (e : ℕ)
    {f : MvPolynomial (Fin n) F} (hf : IsOrderedROABP σ w δ f) :
    IsOrderedROABP σ w δ ((pderiv z)^[e] f) := by
  classical
  rcases hf with ⟨M, s₀, t₀, hM, hf_prod⟩
  have hpderiv_one : ∀ N : Fin n → Matrix (Fin w) (Fin w) F[X],
      pderiv z (roabpProd N (List.ofFn σ) s₀ t₀) =
        roabpProd (Function.update N z ((N z).map Polynomial.derivative)) (List.ofFn σ) s₀ t₀ := by
    intro N
    set N' := Function.update N z ((N z).map Polynomial.derivative)
    have hnodup : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
    have hmem_all : ∀ i : Fin n, i ∈ List.ofFn σ :=
      fun i ↦ List.mem_ofFn.mpr ⟨σ.symm i, σ.apply_symm_apply i⟩
    ext m
    have hm0 : ∀ i ∉ List.ofFn σ, m i = 0 := fun i hi ↦ False.elim (hi (hmem_all i))
    have hm1 : ∀ i ∉ List.ofFn σ, (m + Finsupp.single z (1 : ℕ)) i = 0 :=
      fun i hi ↦ False.elim (hi (hmem_all i))
    rw [coeff_pderiv, coeff_roabpProd N hnodup (m + Finsupp.single z (1 : ℕ)) hm1 s₀ t₀,
      coeff_roabpProd N' hnodup m hm0 s₀ t₀]
    let A : Fin n → Matrix (Fin w) (Fin w) F :=
      fun i ↦ layerCoeff N i ((m + Finsupp.single z (1 : ℕ)) i)
    let B : Fin n → Matrix (Fin w) (Fin w) F := fun i ↦ layerCoeff N' i (m i)
    have hBz : B z = ((m z : F) + 1) • A z := by
      ext u v
      change (Function.update N z ((N z).map Polynomial.derivative) z u v).coeff (m z) =
        ((m z : F) + 1) * (N z u v).coeff ((m + Finsupp.single z (1 : ℕ)) z)
      rw [Function.update_self, Matrix.map_apply, Finsupp.add_apply, Finsupp.single_apply,
        ite_eq_left rfl, Polynomial.coeff_derivative]; ring
    have hBne : ∀ i, i ≠ z → B i = A i := by
      intro i hiz; ext u v
      change (Function.update N z ((N z).map Polynomial.derivative) i u v).coeff (m i) =
        (N i u v).coeff ((m + Finsupp.single z (1 : ℕ)) i)
      rw [Function.update_of_ne hiz, Finsupp.add_apply, Finsupp.single_apply,
        ite_eq_right (Ne.symm hiz), add_zero]
    have hprod_smul := list_prod_smul_unique z ((m z : F) + 1) A B hBz hBne hnodup (hmem_all z)
    have hentry : (List.map B (List.ofFn σ)).prod s₀ t₀ =
        ((m z : F) + 1) * (List.map A (List.ofFn σ)).prod s₀ t₀ := by
      rw [hprod_smul, Matrix.smul_apply, smul_eq_mul]
    rw [hentry, mul_comm]
  have hpderiv_iter :
      ∀ k : ℕ,
        (pderiv z)^[k] (roabpProd M (List.ofFn σ) s₀ t₀) =
          roabpProd (Function.update M z ((M z).map (Polynomial.derivative^[k])))
            (List.ofFn σ) s₀ t₀ ∧
        ∀ i a b, (Function.update M z ((M z).map (Polynomial.derivative^[k])) i a b).natDegree ≤
          δ := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hM⟩
    | succ k ih =>
      refine ⟨?_, fun i a b ↦ ?_⟩
      · rw [Function.iterate_succ_apply', ih.1, hpderiv_one]
        congr 1; ext i u v
        by_cases hiz : i = z
        · subst hiz
          simp only [Function.update_self, Matrix.map_apply]
          rw [← Function.iterate_succ_apply' Polynomial.derivative k]
        · simp [hiz]
      · by_cases hiz : i = z
        · subst hiz
          have hprev := ih.2 i a b
          simp only [Function.update_self, Matrix.map_apply] at hprev ⊢
          rw [Function.iterate_succ_apply']
          have hderiv_le : ∀ P : F[X], (Polynomial.derivative P).natDegree ≤ P.natDegree :=
            fun P ↦ Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ by
              rw [Polynomial.coeff_derivative,
                Polynomial.coeff_eq_zero_of_natDegree_lt (hm.trans (Nat.lt_succ_self m)), zero_mul]
          exact (hderiv_le _).trans hprev
        · simpa [hiz] using hM i a b
  exact ⟨Function.update M z ((M z).map (Polynomial.derivative^[e])), s₀, t₀,
    (hpderiv_iter e).2, hf_prod ▸ (hpderiv_iter e).1⟩

private def pascalMatrix {R : Type*} [CommSemiring R] (k : ℕ) (x : R) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  fun a b ↦ if a.val ≤ b.val then (b.val.choose a.val : R) * x ^ (b.val - a.val) else 0

private theorem pascalMatrix_zero {R : Type*} [CommSemiring R] (k : ℕ) :
    pascalMatrix k (0 : R) = 1 := by
  ext a b; dsimp [pascalMatrix]
  by_cases hab : a.val ≤ b.val
  · rw [ite_eq_left hab]
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hab_fin : a = b := Fin.ext heq
      subst hab_fin; simp
    · have hne : a ≠ b := fun h ↦ by subst h; omega
      rw [Matrix.one_apply, ite_eq_right hne, zero_pow (by omega), mul_zero]
  · have hne : a ≠ b := fun h ↦ hab (by subst h; exact le_rfl)
    rw [ite_eq_right hab, Matrix.one_apply, ite_eq_right hne]

private theorem pascalMatrix_mul {R : Type*} [CommSemiring R] (k : ℕ) (x y : R) :
    pascalMatrix k x * pascalMatrix k y = pascalMatrix k (x + y) := by
  classical
  ext a c; rw [Matrix.mul_apply]; dsimp [pascalMatrix]
  by_cases hac : a.val ≤ c.val
  · rw [ite_eq_left hac]
    have hfilter :
        (∑ b : Fin (k + 1),
            (if a.val ≤ b.val then (b.val.choose a.val : R) * x ^ (b.val - a.val) else 0) *
              (if b.val ≤ c.val then (c.val.choose b.val : R) * y ^ (c.val - b.val) else 0)) =
          ∑ j ∈ Finset.range (c.val - a.val + 1),
            ((a.val + j).choose a.val : R) * x ^ j *
              ((c.val.choose (a.val + j) : R) * y ^ (c.val - a.val - j)) := by
      have hsub :
          (∑ b : Fin (k + 1),
              (if a.val ≤ b.val then (b.val.choose a.val : R) * x ^ (b.val - a.val) else 0) *
                (if b.val ≤ c.val then (c.val.choose b.val : R) * y ^ (c.val - b.val) else 0)) =
            ∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) ↦ a.val ≤ b.val ∧ b.val ≤ c.val),
              (b.val.choose a.val : R) * x ^ (b.val - a.val) *
                ((c.val.choose b.val : R) * y ^ (c.val - b.val)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        by_cases h1 : a.val ≤ b.val <;> by_cases h2 : b.val ≤ c.val <;> simp [h1, h2]
      rw [hsub]
      refine Finset.sum_bij (fun b _ ↦ b.val - a.val) ?_ ?_ ?_ ?_
      · intro b hb; rcases (Finset.mem_filter.mp hb).2 with ⟨h1, h2⟩
        exact Finset.mem_range.mpr (by omega)
      · intro b₁ hb₁ b₂ hb₂ heq
        rcases (Finset.mem_filter.mp hb₁).2 with ⟨h1₁, _⟩
        rcases (Finset.mem_filter.mp hb₂).2 with ⟨h1₂, _⟩
        exact Fin.ext (by omega)
      · intro j hj
        have hj_le : j ≤ c.val - a.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hlt_k1 : a.val + j < k + 1 := by have hc_lt := c.isLt; omega
        refine ⟨⟨a.val + j, hlt_k1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩, ?_⟩
        dsimp; omega
      · intro b hb; rcases (Finset.mem_filter.mp hb).2 with ⟨h1, h2⟩
        rw [show a.val + (b.val - a.val) = b.val by omega,
          show c.val - a.val - (b.val - a.val) = c.val - b.val by omega]
    rw [hfilter, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hchoose_nat :
        c.val.choose (a.val + j) * (a.val + j).choose a.val =
          c.val.choose a.val * (c.val - a.val).choose j := by
      have h := Nat.choose_mul (n := c.val) (k := a.val + j) (s := a.val) (Nat.le_add_right _ _)
      rwa [show a.val + j - a.val = j by omega] at h
    have hchoose_R := congrArg (Nat.cast (R := R)) hchoose_nat
    push_cast at hchoose_R
    calc
      ((a.val + j).choose a.val : R) * x ^ j *
          ((c.val.choose (a.val + j) : R) * y ^ (c.val - a.val - j))
        = ((c.val.choose (a.val + j) : R) * ((a.val + j).choose a.val : R)) *
            (x ^ j * y ^ (c.val - a.val - j)) := by ring
      _ = (c.val.choose a.val : R) *
            (x ^ j * y ^ (c.val - a.val - j) * ((c.val - a.val).choose j : R)) := by
          rw [hchoose_R]; ring
  · rw [ite_eq_right hac]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    by_cases hab : a.val ≤ b.val
    · simp [hab, show ¬ b.val ≤ c.val by omega]
    · simp [hab]

private theorem list_prod_pascalMatrix {R : Type*} [CommSemiring R] (k : ℕ) {ι : Type*}
    (x : ι → R) :
    ∀ l : List ι, (l.map fun i ↦ pascalMatrix k (x i)).prod = pascalMatrix k ((l.map x).sum)
  | [] => by simp [pascalMatrix_zero]
  | i :: rest => by
    rw [List.map_cons, List.prod_cons, list_prod_pascalMatrix k x rest, pascalMatrix_mul,
      List.map_cons, List.sum_cons]

/-- For `1 ≤ n`, any variable order `σ`, constant `a₀ : F`, univariate polynomials
`q : Fin n → F[X]` of degree at most `δ`, and exponent `k : ℕ`,
`(C a₀ + ∑ i, aeval (X i) (q i)) ^ k` has an ordered ROABP of width `k + 1` and layer degree at
most `k * δ`. -/
theorem IsOrderedROABP.sum_univariate_pow {F : Type*} [Field F] {n : ℕ} (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n)) (a₀ : F) (q : Fin n → F[X]) (δ k : ℕ)
    (hq : ∀ i, (q i).natDegree ≤ δ) :
    IsOrderedROABP σ (k + 1) (k * δ)
      ((C a₀ + ∑ i : Fin n, Polynomial.aeval (X i) (q i)) ^ k) := by
  classical
  let i₀ := σ ⟨0, hn⟩
  let q' : Fin n → F[X] := Function.update q i₀ (Polynomial.C a₀ + q i₀)
  have hq'_deg : ∀ i : Fin n, (q' i).natDegree ≤ δ := by
    intro i; dsimp [q']
    by_cases hi : i = i₀
    · subst hi; rw [Function.update_self]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (hq _))
    · rw [Function.update_of_ne hi]; exact hq i
  have hsum_eq :
      (∑ i : Fin n, Polynomial.aeval (X i : MvPolynomial (Fin n) F) (q' i)) =
        C a₀ + ∑ i : Fin n, Polynomial.aeval (X i) (q i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have hi₀ : q' i₀ = Polynomial.C a₀ + q i₀ := Function.update_self i₀ _ q
    have hrest :
        ∑ x ∈ Finset.univ.erase i₀, Polynomial.aeval (X x : MvPolynomial (Fin n) F) (q' x) =
          ∑ x ∈ Finset.univ.erase i₀, Polynomial.aeval (X x) (q x) :=
      Finset.sum_congr rfl fun x hx ↦ by
        dsimp only [q']; rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [hi₀, map_add, Polynomial.aeval_C, algebraMap_eq, hrest, add_assoc]
  let M : Fin n → Matrix (Fin (k + 1)) (Fin (k + 1)) F[X] := fun i ↦ pascalMatrix k (q' i)
  have hM_deg : ∀ i a b, (M i a b).natDegree ≤ k * δ := by
    intro i a b; dsimp [M, pascalMatrix]; split_ifs with hab
    · refine Polynomial.natDegree_mul_le.trans ?_
      have h1 : (Polynomial.C (b.val.choose a.val : F)).natDegree = 0 := by simp
      have h2 : ((q' i) ^ (b.val - a.val)).natDegree ≤ (b.val - a.val) * δ :=
        (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hq'_deg i))
      have hb_le : b.val - a.val ≤ k := by have := b.isLt; omega
      have h3 : (b.val - a.val) * δ ≤ k * δ := Nat.mul_le_mul_right δ hb_le
      change ((b.val.choose a.val : F[X])).natDegree + _ ≤ _
      rw [← Polynomial.C_eq_natCast, h1, zero_add]
      exact h2.trans h3
    · simp
  have hmap_pascal : ∀ i : Fin n,
      (M i).map (Polynomial.aeval (X i : MvPolynomial (Fin n) F)) =
        pascalMatrix k (Polynomial.aeval (X i : MvPolynomial (Fin n) F) (q' i)) := by
    intro i; ext a b; dsimp [M, pascalMatrix]; split_ifs <;> simp
  refine ⟨M, ⟨0, Nat.zero_lt_succ k⟩, ⟨k, Nat.lt_succ_self k⟩, hM_deg, ?_⟩
  have hprod :
      roabpProd M (List.ofFn σ) =
        pascalMatrix k
          (((List.ofFn σ).map fun i ↦
            Polynomial.aeval (X i : MvPolynomial (Fin n) F) (q' i)).sum) := by
    rw [roabpProd]
    have hlist_eq :
        ((List.ofFn σ).map fun i ↦
            (M i).map (Polynomial.aeval (X i : MvPolynomial (Fin n) F))) =
          (List.ofFn σ).map fun i ↦
            pascalMatrix k (Polynomial.aeval (X i : MvPolynomial (Fin n) F) (q' i)) :=
      List.map_congr_left fun i _ ↦ hmap_pascal i
    rw [hlist_eq, list_prod_pascalMatrix]
  have hsum_fn :
      (((List.ofFn σ).map fun i ↦
          Polynomial.aeval (X i : MvPolynomial (Fin n) F) (q' i)).sum) =
        C a₀ + ∑ i : Fin n, Polynomial.aeval (X i) (q i) := by
    rw [List.map_ofFn, List.sum_ofFn]
    dsimp only [Function.comp_def]
    rw [Equiv.sum_comp σ
      (fun i : Fin n ↦ Polynomial.aeval (X i : MvPolynomial (Fin n) F) (q' i)), hsum_eq]
  rw [hprod, hsum_fn]
  simp [pascalMatrix]

/-- Recursive suffix subspace of `Fin w → F` spanned by all monomial coefficient column vectors of
`roabpProd M l · t` when all layers have degree at most `d`. -/
noncomputable def roabpSuffixSubspace {F : Type*} [Field F] {n w : ℕ}
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (d : ℕ) (t : Fin w) :
    List (Fin n) → Submodule F (Fin w → F)
  | [] => Submodule.span F {fun a ↦ if a = t then 1 else 0}
  | i :: rest =>
    ⨆ e ∈ Finset.range (d + 1),
      (roabpSuffixSubspace M d t rest).map (Matrix.mulVecLin (layerCoeff M i e))

/-- At every variable list `l`, `roabpSuffixSubspace M d t l` has `F`-dimension at most `w`. -/
theorem finrank_roabpSuffixSubspace_le {F : Type*} [Field F] {n w : ℕ}
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (d : ℕ) (t : Fin w) (l : List (Fin n)) :
    Module.finrank F (roabpSuffixSubspace M d t l) ≤ w :=
  (Submodule.finrank_le _).trans_eq (by simp)

private theorem roabpSuffixSubspace_eq_span {F : Type*} [Field F] {n w d : ℕ}
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (hM : ∀ i a b, (M i a b).natDegree ≤ d)
    (t : Fin w) :
    ∀ {l : List (Fin n)}, l.Nodup →
      roabpSuffixSubspace M d t l =
        Submodule.span F
          (Set.range fun m : Fin n →₀ ℕ ↦ fun a : Fin w ↦ (roabpProd M l a t).coeff m)
  | [], _ => by
    apply le_antisymm
    · rw [roabpSuffixSubspace, Submodule.span_le]
      rintro v hv
      rw [Set.mem_singleton_iff.mp hv]
      refine Submodule.subset_span ⟨0, ?_⟩
      ext a; by_cases hat : a = t <;> simp [roabpProd_nil, hat]
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      dsimp only
      by_cases hm0 : m = 0
      · subst hm0; rw [roabpSuffixSubspace]
        refine Submodule.subset_span ?_
        rw [Set.mem_singleton_iff]
        ext a; by_cases hat : a = t <;> simp [roabpProd_nil, hat]
      · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
        have hzero : (fun a : Fin w ↦ (roabpProd M [] a t).coeff m) = 0 := by
          ext a
          exact coeff_roabpProd_eq_zero M [] List.not_mem_nil (Finsupp.mem_support_iff.mp hi) a t
        rw [hzero]
        exact (roabpSuffixSubspace M d t []).zero_mem
  | i :: rest, hl => by
    classical
    rcases List.nodup_cons.mp hl with ⟨hi_not_rest, hrest_nodup⟩
    rw [roabpSuffixSubspace, roabpSuffixSubspace_eq_span M hM t hrest_nodup]
    apply le_antisymm
    · refine iSup₂_le fun e _ ↦ Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr ?_)
      rintro _ ⟨m₀, rfl⟩
      refine Submodule.mem_comap.mpr ?_
      dsimp only
      by_cases hm₀i : m₀ i = 0
      · let m₁ : Fin n →₀ ℕ := m₀ + Finsupp.single i e
        have hm₁_i : m₁ i = e := by simp [m₁, hm₀i]
        have hm₁_erase : m₁.erase i = m₀ := by
          ext j
          by_cases hji : j = i
          · subst hji; simp [hm₀i]
          · dsimp [m₁]
            rw [Finsupp.erase_ne hji, Finsupp.add_apply, Finsupp.single_apply,
              ite_eq_right (Ne.symm hji), add_zero]
        refine Submodule.subset_span ⟨m₁, ?_⟩
        ext a; dsimp only
        rw [roabpProd_cons, Matrix.mul_apply, coeff_sum, Matrix.mulVecLin_apply, Matrix.mulVec,
          dotProduct]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Matrix.map_apply,
          coeff_aeval_X_mul_of_mem_supported (S := {j | j ∈ rest}) hi_not_rest (M i a k)
            (roabpProd_mem_supported M rest (fun _ h ↦ h) k t) m₁,
          hm₁_i, hm₁_erase]
        rfl
      · have hv0 : (fun a : Fin w ↦ (roabpProd M rest a t).coeff m₀) = 0 := by
          ext a; exact coeff_roabpProd_eq_zero M rest hi_not_rest hm₀i a t
        rw [hv0, map_zero]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      dsimp only
      have hu_eq :
          (fun a : Fin w ↦ (roabpProd M (i :: rest) a t).coeff m) =
            Matrix.mulVecLin (layerCoeff M i (m i))
              (fun k : Fin w ↦ (roabpProd M rest k t).coeff (m.erase i)) := by
        ext a
        rw [roabpProd_cons, Matrix.mul_apply, coeff_sum, Matrix.mulVecLin_apply, Matrix.mulVec,
          dotProduct]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Matrix.map_apply,
          coeff_aeval_X_mul_of_mem_supported (S := {j | j ∈ rest}) hi_not_rest (M i a k)
            (roabpProd_mem_supported M rest (fun _ h ↦ h) k t) m]
        rfl
      rw [hu_eq]
      by_cases hmi_le : m i ≤ d
      · have hmem_range : m i ∈ Finset.range (d + 1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le hmi_le)
        refine (le_iSup₂ (f := fun e (_ : e ∈ Finset.range (d + 1)) ↦
          (Submodule.span F
            (Set.range fun m' : Fin n →₀ ℕ ↦ fun a ↦ (roabpProd M rest a t).coeff m')).map
            (Matrix.mulVecLin (layerCoeff M i e))) (m i) hmem_range) ?_
        exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨m.erase i, rfl⟩)
      · have hlayer0 : layerCoeff M i (m i) = 0 := by
          ext a k
          exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hM i a k).trans_lt (lt_of_not_ge hmi_le))
        rw [hlayer0, Matrix.mulVecLin_zero, LinearMap.zero_apply]
        exact Submodule.zero_mem _

/-- Whitebox ROABP identity testing: for any duplicate-free variable list `l` and layer-degree-`≤ d`
branching program `M`, `roabpProd M l s t = 0` holds if and only if the `s`-th coordinate vanishes
on every vector in the `≤ w`-dimensional suffix subspace `roabpSuffixSubspace M d t l`. -/
theorem roabpProd_eq_zero_iff_roabpSuffixSubspace {F : Type*} [Field F] {n w d : ℕ}
    {l : List (Fin n)} (hl : l.Nodup) (M : Fin n → Matrix (Fin w) (Fin w) F[X])
    (hM : ∀ i a b, (M i a b).natDegree ≤ d) (s t : Fin w) :
    roabpProd M l s t = 0 ↔ ∀ v ∈ roabpSuffixSubspace M d t l, v s = 0 := by
  rw [roabpSuffixSubspace_eq_span M hM t hl]
  constructor
  · intro h0
    have hsub :
        Submodule.span F
            (Set.range fun m : Fin n →₀ ℕ ↦ fun a : Fin w ↦ (roabpProd M l a t).coeff m) ≤
          LinearMap.ker (LinearMap.proj s) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      change (roabpProd M l s t).coeff m = 0
      rw [h0]; simp
    exact fun v hv ↦ hsub hv
  · intro hall
    ext m
    change (roabpProd M l s t).coeff m = 0
    exact hall (fun a ↦ (roabpProd M l a t).coeff m) (Submodule.subset_span ⟨m, rfl⟩)

end CslibFrontier.Circuits.Arithmetic
