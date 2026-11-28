/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.AlgebraicBranchingProgram
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebraic Branching Program Substitution and Composition Operations

This module establishes closure of edge-labeled algebraic branching programs (ABPs) under general
and single-variable affine substitutions and under constant-arity composition over `ZMod p`.

## Main definitions

* `CslibFrontier.Computability.Circuit.ABP.affineSubst`: substitutes affine linear forms in `m`
  variables into an `n`-variable ABP with size `≤ (3 * m + 2) * P.size`.
* `CslibFrontier.Computability.Circuit.ABP.singleVarAffineSubst`: substitutes single-variable affine
  forms `a i * X (idx i) + c i` with size `≤ 5 * P.size`.
* `CslibFrontier.Computability.Circuit.ABP.composeZMod`: substitutes `d` ABPs into an arbitrary
  `d`-ary function `(Fin d → ZMod p) → ZMod p` via Lagrange interpolation over `ZMod p`.

## Main results

* `CslibFrontier.Computability.Circuit.ABP.poly_affineSubst`,
  `CslibFrontier.Computability.Circuit.ABP.size_affineSubst_le`.
* `CslibFrontier.Computability.Circuit.ABP.poly_singleVarAffineSubst`,
  `CslibFrontier.Computability.Circuit.ABP.size_singleVarAffineSubst_le`.
* `CslibFrontier.Computability.Circuit.ABP.eval_composeZMod`,
  `CslibFrontier.Computability.Circuit.ABP.size_composeZMod_le`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open MvPolynomial
open Cslib.Circuits.Arithmetic

universe u v

namespace ABP

variable {K : Type u} {σ : Type v}

private theorem list_sum_flatMap {α β γ : Type*} [AddCommMonoid γ] (l : List α)
    (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-! ### Affine substitution -/

/-- General affine substitution into an ABP: replaces each variable `X i` by
`C (c i) + ∑ j : Fin m, C (a i j) * X j` using `m` midpoint vertices per edge, achieving
size `≤ (3 * m + 2) * P.size`. -/
public noncomputable def affineSubst {n m : ℕ} (P : ABP K (Fin n))
    (c : Fin n → K) (a : Fin n → Fin m → K) : ABP K (Fin m) :=
  let k := P.innerVerts
  let eLen := P.edges.length
  let dstOf (r : Fin eLen) : Fin (k + 2) := (P.edges.get r).dst
  let eqv := subEquiv (w := m) dstOf
  let newEdges : List (ABPEdge K (Fin m) (k + m * eLen)) :=
    (List.finRange eLen).flatMap fun r =>
      let e := P.edges.get r
      match e.label with
      | .inr d =>
        [⟨eqv (.inl e.src), eqv (.inl e.dst), by
          change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
          rw [subEquiv_inl_val, subEquiv_inl_val]
          exact subPosVal_strictMono dstOf m e.lt, .inr d⟩]
      | .inl i =>
        ⟨eqv (.inl e.src), eqv (.inl e.dst), by
          change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
          rw [subEquiv_inl_val, subEquiv_inl_val]
          exact subPosVal_strictMono dstOf m e.lt, .inr (c i)⟩ ::
        (List.finRange m).flatMap fun j =>
          [⟨eqv (.inl e.src), eqv (.inr (r, j)), by
            change (eqv (.inl e.src)).1 < (eqv (.inr (r, j))).1
            rw [subEquiv_inl_val, subEquiv_inr_val]
            exact subPosVal_lt_subMidVal e.lt j, .inr (a i j)⟩,
           ⟨eqv (.inr (r, j)), eqv (.inl e.dst), by
            change (eqv (.inr (r, j))).1 < (eqv (.inl e.dst)).1
            rw [subEquiv_inr_val, subEquiv_inl_val]
            exact subMidVal_lt_subPosVal dstOf r j, .inl j⟩]
  ⟨k + m * eLen, newEdges⟩

public theorem size_affineSubst_le {n m : ℕ} (P : ABP K (Fin n))
    (c : Fin n → K) (a : Fin n → Fin m → K) :
    (P.affineSubst c a).size ≤ (3 * m + 2) * P.size := by
  have hlen : (P.affineSubst c a).edges.length ≤ (2 * m + 1) * P.edges.length := by
    simp only [affineSubst, List.length_flatMap]
    calc (List.map (fun r : Fin P.edges.length => _) (List.finRange P.edges.length)).sum
        ≤ (List.map (fun _ : Fin P.edges.length => 2 * m + 1)
            (List.finRange P.edges.length)).sum := by
          refine List.sum_le_sum fun r _ => ?_
          cases (P.edges.get r).label with
          | inr d => simp
          | inl i =>
            simp only [List.length_cons, List.length_flatMap, List.length_nil, zero_add]
            have hfm : (List.map (fun _ : Fin m => 2) (List.finRange m)).sum = 2 * m := by
              simp [List.sum_replicate, mul_comm]
            rw [hfm]
      _ = (2 * m + 1) * P.edges.length := by
          simp [List.sum_replicate, mul_comm]
  simp only [size_eq_innerVerts_add_two_add_length, affineSubst] at hlen ⊢
  nlinarith

public theorem poly_affineSubst [CommSemiring K] {n m : ℕ} (P : ABP K (Fin n))
    (c : Fin n → K) (a : Fin n → Fin m → K) :
    (P.affineSubst c a).poly =
      MvPolynomial.aeval (fun i => MvPolynomial.C (c i) + ∑ j : Fin m, MvPolynomial.C (a i j) * X j)
        P.poly := by
  let k := P.innerVerts
  let eLen := P.edges.length
  let dstOf (r : Fin eLen) : Fin (k + 2) := (P.edges.get r).dst
  let eqv := subEquiv (w := m) dstOf
  let Φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin m) K :=
    MvPolynomial.aeval fun i => MvPolynomial.C (c i) + ∑ j : Fin m, MvPolynomial.C (a i j) * X j
  have hdst0 : ∀ r : Fin eLen, 0 < dstOf r := fun r =>
    lt_of_le_of_lt (Fin.zero_le _) (P.edges.get r).lt
  have h0 : eqv (.inl 0) = 0 := by
    apply Fin.ext; rw [subEquiv_inl_val, subPosVal_zero hdst0]; rfl
  let edgeBlock (r : Fin eLen) : List (ABPEdge K (Fin m) (k + m * eLen)) :=
    let e := P.edges.get r
    match e.label with
    | .inr d =>
      [⟨eqv (.inl e.src), eqv (.inl e.dst), by
        change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
        rw [subEquiv_inl_val, subEquiv_inl_val]
        exact subPosVal_strictMono dstOf m e.lt, .inr d⟩]
    | .inl i =>
      ⟨eqv (.inl e.src), eqv (.inl e.dst), by
        change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
        rw [subEquiv_inl_val, subEquiv_inl_val]
        exact subPosVal_strictMono dstOf m e.lt, .inr (c i)⟩ ::
      (List.finRange m).flatMap fun j =>
        [⟨eqv (.inl e.src), eqv (.inr (r, j)), by
          change (eqv (.inl e.src)).1 < (eqv (.inr (r, j))).1
          rw [subEquiv_inl_val, subEquiv_inr_val]
          exact subPosVal_lt_subMidVal e.lt j, .inr (a i j)⟩,
         ⟨eqv (.inr (r, j)), eqv (.inl e.dst), by
          change (eqv (.inr (r, j))).1 < (eqv (.inl e.dst)).1
          rw [subEquiv_inr_val, subEquiv_inl_val]
          exact subMidVal_lt_subPosVal dstOf r j, .inl j⟩]
  have hedges_aff : (P.affineSubst c a).edges = (List.finRange eLen).flatMap edgeBlock := rfl
  -- Compute nodePoly at midpoints first, then at original vertices by strong induction.
  have hmid_val : ∀ (r : Fin eLen) (j : Fin m) (i : Fin n),
      (P.edges.get r).label = .inl i →
      (P.affineSubst c a).nodePoly (eqv (.inr (r, j))) =
        (P.affineSubst c a).nodePoly (eqv (.inl (P.edges.get r).src)) * MvPolynomial.C (a i j) := by
    intro r j i hlab
    have hne0 : (eqv (.inr (r, j)) : Fin ((P.affineSubst c a).innerVerts + 2)) ≠ 0 := by
      rw [← h0]; exact fun h => nomatch eqv.injective h
    rw [nodePoly_of_ne_zero (P.affineSubst c a) hne0]
    change ((P.affineSubst c a).edges.map _).sum = _
    rw [hedges_aff]
    change (((List.finRange eLen).flatMap edgeBlock).map fun e : ABPEdge K (Fin m) (k + m * eLen) =>
      if e.dst = eqv (.inr (r, j)) then
        (P.affineSubst c a).nodePoly e.src * abpLabelPoly e.label else 0).sum = _
    rw [list_sum_flatMap]
    have hsum_r : ∀ r' : Fin eLen, r' ≠ r →
        ((edgeBlock r').map fun e => if e.dst = eqv (.inr (r, j)) then
          (P.affineSubst c a).nodePoly e.src * abpLabelPoly e.label else 0).sum = 0 := by
      intro r' hr'
      dsimp only [edgeBlock]
      cases (P.edges.get r').label with
      | inr d => simp
      | inl i' =>
        have hne1 : eqv (.inl (P.edges.get r').dst) ≠ eqv (.inr (r, j)) :=
          fun h => nomatch eqv.injective h
        simp only [List.map_cons, List.sum_cons, hne1, ↓reduceIte, zero_add,
          list_sum_flatMap]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨j', -, rfl⟩ := List.mem_map.mp hx
        have hne2 : eqv (.inr (r', j')) ≠ eqv (.inr (r, j)) := fun h =>
          hr' (congrArg Prod.fst (Sum.inr.inj (eqv.injective h)))
        simp [hne2]
    have hsum_single : ∀ (f : Fin eLen → MvPolynomial (Fin m) K) (r₀ : Fin eLen),
        (∀ r' ≠ r₀, f r' = 0) → ((List.finRange eLen).map f).sum = f r₀ := by
      intro f r₀ hf
      have h1 : ((List.finRange eLen).map f).sum = ∑ r' : Fin eLen, f r' := by
        rw [← List.sum_ofFn (f := f)]; congr 1
        apply List.ext_getElem (by simp)
        intro idx h1 h2; simp
      rw [h1, Finset.sum_eq_single r₀ (fun b _ hb => hf b hb)
        (fun h => absurd (Finset.mem_univ _) h)]
    rw [hsum_single _ r hsum_r]
    have hne_dst : eqv (.inl (P.edges.get r).dst) ≠ eqv (.inr (r, j)) :=
      fun h => nomatch eqv.injective h
    dsimp only [edgeBlock]
    simp only [hlab, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hne_dst,
      ↓reduceIte, zero_add, add_zero, list_sum_flatMap]
    have hsum_j : ∀ j' : Fin m, j' ≠ j →
        (if eqv (.inr (r, j')) = eqv (.inr (r, j)) then
          (P.affineSubst c a).nodePoly (eqv (.inl (P.edges.get r).src)) *
            abpLabelPoly (.inr (a i j'))
        else 0) = 0 := by
      intro j' hj'
      have hne1 : eqv (.inr (r, j')) ≠ eqv (.inr (r, j)) := fun h =>
        hj' (congrArg Prod.snd (Sum.inr.inj (eqv.injective h)))
      simp [hne1]
    have hsum_single_m : ∀ (f : Fin m → MvPolynomial (Fin m) K) (j₀ : Fin m),
        (∀ j' ≠ j₀, f j' = 0) → ((List.finRange m).map f).sum = f j₀ := by
      intro f j₀ hf
      have h1 : ((List.finRange m).map f).sum = ∑ j' : Fin m, f j' := by
        rw [← List.sum_ofFn (f := f)]; congr 1
        apply List.ext_getElem (by simp)
        intro idx h1 h2; simp
      rw [h1, Finset.sum_eq_single j₀ (fun b _ hb => hf b hb)
        (fun h => absurd (Finset.mem_univ _) h)]
    rw [hsum_single_m _ j hsum_j]
    simp
  have hmain : ∀ v : Fin (k + 2),
      (P.affineSubst c a).nodePoly (eqv (.inl v)) = Φ (P.nodePoly v) := by
    suffices h : ∀ (t : ℕ) (v : Fin (k + 2)), v.1 = t →
        (P.affineSubst c a).nodePoly (eqv (.inl v)) = Φ (P.nodePoly v) from
      fun v => h v.1 v rfl
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro v hvt
      by_cases hv0 : v = 0
      · subst hv0
        have h0' : eqv (.inl 0) = (0 : Fin ((P.affineSubst c a).innerVerts + 2)) := h0
        rw [h0', (P.affineSubst c a).nodePoly_zero, P.nodePoly_zero, map_one]
      · have hne0 : (eqv (.inl v) : Fin ((P.affineSubst c a).innerVerts + 2)) ≠ 0 := by
          rw [← h0]; exact fun h => hv0 (Sum.inl.inj (eqv.injective h))
        rw [nodePoly_of_ne_zero (P.affineSubst c a) hne0, nodePoly_of_ne_zero P hv0,
          map_list_sum, List.map_map]
        change ((P.affineSubst c a).edges.map _).sum = _
        rw [hedges_aff]
        change (((List.finRange eLen).flatMap edgeBlock).map
          fun e : ABPEdge K (Fin m) (k + m * eLen) =>
            if e.dst = eqv (.inl v) then
              (P.affineSubst c a).nodePoly e.src * abpLabelPoly e.label else 0).sum = _
        rw [list_sum_flatMap]
        have hlist_eq :
            ((List.finRange eLen).map fun r =>
              ((edgeBlock r).map fun e => if e.dst = eqv (.inl v) then
                (P.affineSubst c a).nodePoly e.src * abpLabelPoly e.label else 0).sum) =
            (List.finRange eLen).map fun r =>
              Φ (if (P.edges.get r).dst = v then
                P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label else 0) := by
          refine List.map_congr_left fun r _ => ?_
          dsimp only [edgeBlock]
          cases hlab : (P.edges.get r).label with
          | inr d =>
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
              eqv.apply_eq_iff_eq, Sum.inl.injEq]
            split_ifs with hd
            · rw [ih _ (hvt ▸ (hd ▸ (P.edges.get r).lt)) _ rfl]; simp [Φ, map_mul]
            · simp
          | inl i =>
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
              list_sum_flatMap, eqv.apply_eq_iff_eq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte,
              zero_add]
            have hfin_m :
                ((List.finRange m).map fun j =>
                  if (P.edges.get r).dst = v then
                    (P.affineSubst c a).nodePoly (eqv (.inr (r, j))) * abpLabelPoly (.inl j)
                  else 0).sum =
                if (P.edges.get r).dst = v then
                  ∑ j : Fin m,
                    (P.affineSubst c a).nodePoly (eqv (.inl (P.edges.get r).src)) *
                      MvPolynomial.C (a i j) * MvPolynomial.X j
                else 0 := by
              have h1 : ∀ j : Fin m,
                  (if (P.edges.get r).dst = v then
                    (P.affineSubst c a).nodePoly (eqv (.inr (r, j))) * abpLabelPoly (.inl j)
                  else 0) =
                  if (P.edges.get r).dst = v then
                    (P.affineSubst c a).nodePoly (eqv (.inl (P.edges.get r).src)) *
                      MvPolynomial.C (a i j) * MvPolynomial.X j
                  else 0 := by
                intro j
                split_ifs with hd
                · rw [hmid_val r j i hlab]; rfl
                · rfl
              simp only [h1]
              split_ifs
              · rw [← List.sum_ofFn]; congr 1
                apply List.ext_getElem (by simp); intro idx _ _; simp
              · simp
            rw [hfin_m]
            split_ifs with hd
            · rw [ih _ (hvt ▸ (hd ▸ (P.edges.get r).lt)) _ rfl]
              simp only [abpLabelPoly_inr, abpLabelPoly_inl, map_mul, Φ, aeval_X]
              rw [mul_add, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl fun j _ => by ring
            · simp
        rw [hlist_eq]
        have hmap_fin :
            ((List.finRange eLen).map fun r =>
              Φ (if (P.edges.get r).dst = v then
                P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label else 0)) =
            P.edges.map (Φ ∘ fun e =>
              if e.dst = v then P.nodePoly e.src * abpLabelPoly e.label else 0) := by
          apply List.ext_getElem (by simp [eLen])
          intro idx h1 h2; simp
        rw [hmap_fin]
  have hlast : eqv (.inl (Fin.last (k + 1))) = Fin.last ((P.affineSubst c a).innerVerts + 1) := by
    apply Fin.ext; rw [subEquiv_inl_val, subPosVal_last]; rfl
  rw [poly_eq_nodePoly_last, poly_eq_nodePoly_last, ← hlast]
  exact hmain (Fin.last (k + 1))

/-- Single-variable affine substitution into an ABP: replaces each `X i` by
`C (c i) + C (a i) * X (idx i)` in size `≤ 4 * P.size`. -/
public noncomputable def singleVarAffineSubst {n m : ℕ} (P : ABP K (Fin n))
    (c : Fin n → K) (a : Fin n → K) (idx : Fin n → Fin m) : ABP K (Fin m) :=
  let k := P.innerVerts
  let eLen := P.edges.length
  let dstOf (r : Fin eLen) : Fin (k + 2) := (P.edges.get r).dst
  let eqv := subEquiv (w := 1) dstOf
  let newEdges : List (ABPEdge K (Fin m) (k + 1 * eLen)) :=
    (List.finRange eLen).flatMap fun r =>
      let e := P.edges.get r
      match e.label with
      | .inr d =>
        [⟨eqv (.inl e.src), eqv (.inl e.dst), by
          change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
          rw [subEquiv_inl_val, subEquiv_inl_val]
          exact subPosVal_strictMono dstOf 1 e.lt, .inr d⟩]
      | .inl i =>
        [⟨eqv (.inl e.src), eqv (.inl e.dst), by
          change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
          rw [subEquiv_inl_val, subEquiv_inl_val]
          exact subPosVal_strictMono dstOf 1 e.lt, .inr (c i)⟩,
         ⟨eqv (.inl e.src), eqv (.inr (r, 0)), by
          change (eqv (.inl e.src)).1 < (eqv (.inr (r, 0))).1
          rw [subEquiv_inl_val, subEquiv_inr_val]
          exact subPosVal_lt_subMidVal e.lt 0, .inr (a i)⟩,
         ⟨eqv (.inr (r, 0)), eqv (.inl e.dst), by
          change (eqv (.inr (r, 0))).1 < (eqv (.inl e.dst)).1
          rw [subEquiv_inr_val, subEquiv_inl_val]
          exact subMidVal_lt_subPosVal dstOf r 0, .inl (idx i)⟩]
  ⟨k + 1 * eLen, newEdges⟩

public theorem size_singleVarAffineSubst_le {n m : ℕ} (P : ABP K (Fin n))
    (c : Fin n → K) (a : Fin n → K) (idx : Fin n → Fin m) :
    (P.singleVarAffineSubst c a idx).size ≤ 4 * P.size := by
  have hlen : (P.singleVarAffineSubst c a idx).edges.length ≤ 3 * P.edges.length := by
    simp only [singleVarAffineSubst, List.length_flatMap]
    calc (List.map (fun r : Fin P.edges.length => _) (List.finRange P.edges.length)).sum
        ≤ (List.map (fun _ : Fin P.edges.length => 3) (List.finRange P.edges.length)).sum := by
          refine List.sum_le_sum fun r _ => ?_
          cases (P.edges.get r).label <;> simp
      _ = 3 * P.edges.length := by simp [List.sum_replicate, mul_comm]
  simp only [size_eq_innerVerts_add_two_add_length, singleVarAffineSubst] at hlen ⊢
  omega

public theorem poly_singleVarAffineSubst [CommSemiring K] {n m : ℕ} (P : ABP K (Fin n))
    (c : Fin n → K) (a : Fin n → K) (idx : Fin n → Fin m) :
    (P.singleVarAffineSubst c a idx).poly =
      MvPolynomial.aeval (fun i => MvPolynomial.C (c i) + MvPolynomial.C (a i) * X (idx i))
        P.poly := by
  let k := P.innerVerts
  let eLen := P.edges.length
  let dstOf (r : Fin eLen) : Fin (k + 2) := (P.edges.get r).dst
  let eqv := subEquiv (w := 1) dstOf
  let Φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin m) K :=
    MvPolynomial.aeval fun i => MvPolynomial.C (c i) + MvPolynomial.C (a i) * X (idx i)
  have hdst0 : ∀ r : Fin eLen, 0 < dstOf r := fun r =>
    lt_of_le_of_lt (Fin.zero_le _) (P.edges.get r).lt
  have h0 : eqv (.inl 0) = 0 := by
    apply Fin.ext; rw [subEquiv_inl_val, subPosVal_zero hdst0]; rfl
  have hsum_single : ∀ (f : Fin eLen → MvPolynomial (Fin m) K) (r₀ : Fin eLen),
      (∀ r' ≠ r₀, f r' = 0) → ((List.finRange eLen).map f).sum = f r₀ := by
    intro f r₀ hf
    have h1 : ((List.finRange eLen).map f).sum = ∑ r' : Fin eLen, f r' := by
      rw [← List.sum_ofFn (f := f)]; congr 1
      apply List.ext_getElem (by simp); intro i _ _; simp
    rw [h1, Finset.sum_eq_single r₀ (fun b _ hb => hf b hb) (fun h => absurd (Finset.mem_univ _) h)]
  let edgeBlockSv (r : Fin eLen) : List (ABPEdge K (Fin m) (k + 1 * eLen)) :=
    let e := P.edges.get r
    match e.label with
    | .inr d =>
      [⟨eqv (.inl e.src), eqv (.inl e.dst), by
        change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
        rw [subEquiv_inl_val, subEquiv_inl_val]
        exact subPosVal_strictMono dstOf 1 e.lt, .inr d⟩]
    | .inl i =>
      [⟨eqv (.inl e.src), eqv (.inl e.dst), by
        change (eqv (.inl e.src)).1 < (eqv (.inl e.dst)).1
        rw [subEquiv_inl_val, subEquiv_inl_val]
        exact subPosVal_strictMono dstOf 1 e.lt, .inr (c i)⟩,
       ⟨eqv (.inl e.src), eqv (.inr (r, 0)), by
        change (eqv (.inl e.src)).1 < (eqv (.inr (r, 0))).1
        rw [subEquiv_inl_val, subEquiv_inr_val]
        exact subPosVal_lt_subMidVal e.lt 0, .inr (a i)⟩,
       ⟨eqv (.inr (r, 0)), eqv (.inl e.dst), by
        change (eqv (.inr (r, 0))).1 < (eqv (.inl e.dst)).1
        rw [subEquiv_inr_val, subEquiv_inl_val]
        exact subMidVal_lt_subPosVal dstOf r 0, .inl (idx i)⟩]
  have hedges_sv : (P.singleVarAffineSubst c a idx).edges =
      (List.finRange eLen).flatMap edgeBlockSv := rfl
  have hmid_val : ∀ (r : Fin eLen) (i : Fin n),
      (P.edges.get r).label = .inl i →
      (P.singleVarAffineSubst c a idx).nodePoly (eqv (.inr (r, 0))) =
        (P.singleVarAffineSubst c a idx).nodePoly (eqv (.inl (P.edges.get r).src)) *
          MvPolynomial.C (a i) := by
    intro r i hlab
    have hne0 :
        (eqv (.inr (r, 0)) : Fin ((P.singleVarAffineSubst c a idx).innerVerts + 2)) ≠ 0 := by
      rw [← h0]; exact fun h => nomatch eqv.injective h
    rw [nodePoly_of_ne_zero (P.singleVarAffineSubst c a idx) hne0]
    change ((P.singleVarAffineSubst c a idx).edges.map _).sum = _
    rw [hedges_sv]
    change (((List.finRange eLen).flatMap edgeBlockSv).map
      fun e : ABPEdge K (Fin m) (k + 1 * eLen) =>
        if e.dst = eqv (.inr (r, 0)) then
          (P.singleVarAffineSubst c a idx).nodePoly e.src * abpLabelPoly e.label else 0).sum = _
    rw [list_sum_flatMap]
    have hsum_r : ∀ r' : Fin eLen, r' ≠ r →
        ((edgeBlockSv r').map fun e => if e.dst = eqv (.inr (r, 0)) then
          (P.singleVarAffineSubst c a idx).nodePoly e.src *
            abpLabelPoly e.label else 0).sum = 0 := by
      intro r' hr'
      dsimp only [edgeBlockSv]
      cases (P.edges.get r').label with
      | inr d => simp
      | inl i' =>
        have hne2 : eqv (.inr (r', 0)) ≠ eqv (.inr (r, 0)) := fun h =>
          hr' (congrArg Prod.fst (Sum.inr.inj (eqv.injective h)))
        simp [hne2]
    rw [hsum_single _ r hsum_r]
    dsimp only [edgeBlockSv]
    rw [hlab]
    simp
  have hmain : ∀ v : Fin (k + 2),
      (P.singleVarAffineSubst c a idx).nodePoly (eqv (.inl v)) = Φ (P.nodePoly v) := by
    suffices h : ∀ (t : ℕ) (v : Fin (k + 2)), v.1 = t →
        (P.singleVarAffineSubst c a idx).nodePoly (eqv (.inl v)) = Φ (P.nodePoly v) from
      fun v => h v.1 v rfl
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro v hvt
      by_cases hv0 : v = 0
      · subst hv0
        have h0' : eqv (.inl 0) = (0 : Fin ((P.singleVarAffineSubst c a idx).innerVerts + 2)) := h0
        rw [h0', (P.singleVarAffineSubst c a idx).nodePoly_zero, P.nodePoly_zero, map_one]
      · have hne0 :
            (eqv (.inl v) : Fin ((P.singleVarAffineSubst c a idx).innerVerts + 2)) ≠ 0 := by
          rw [← h0]; exact fun h => hv0 (Sum.inl.inj (eqv.injective h))
        rw [nodePoly_of_ne_zero (P.singleVarAffineSubst c a idx) hne0, nodePoly_of_ne_zero P hv0,
          map_list_sum, List.map_map]
        change ((P.singleVarAffineSubst c a idx).edges.map _).sum = _
        rw [hedges_sv]
        change (((List.finRange eLen).flatMap edgeBlockSv).map
          fun e : ABPEdge K (Fin m) (k + 1 * eLen) =>
            if e.dst = eqv (.inl v) then
              (P.singleVarAffineSubst c a idx).nodePoly e.src *
                abpLabelPoly e.label else 0).sum = _
        rw [list_sum_flatMap]
        have hlist_eq :
            ((List.finRange eLen).map fun r =>
              ((edgeBlockSv r).map fun e => if e.dst = eqv (.inl v) then
                (P.singleVarAffineSubst c a idx).nodePoly e.src *
                  abpLabelPoly e.label else 0).sum) =
            (List.finRange eLen).map fun r =>
              Φ (if (P.edges.get r).dst = v then
                P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label else 0) := by
          refine List.map_congr_left fun r _ => ?_
          dsimp only [edgeBlockSv]
          cases hlab : (P.edges.get r).label with
          | inr d =>
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
              eqv.apply_eq_iff_eq, Sum.inl.injEq]
            split_ifs with hd
            · rw [ih _ (hvt ▸ (hd ▸ (P.edges.get r).lt)) _ rfl]; simp [Φ, map_mul]
            · simp
          | inl i =>
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
              eqv.apply_eq_iff_eq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte, zero_add]
            split_ifs with hd
            · rw [hmid_val r i hlab, ih _ (hvt ▸ (hd ▸ (P.edges.get r).lt)) _ rfl]
              simp only [abpLabelPoly_inr, abpLabelPoly_inl, map_mul, Φ, aeval_X]
              ring
            · simp
        rw [hlist_eq]
        have hmap_fin :
            ((List.finRange eLen).map fun r =>
              Φ (if (P.edges.get r).dst = v then
                P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label else 0)) =
            P.edges.map (Φ ∘ fun e =>
              if e.dst = v then P.nodePoly e.src * abpLabelPoly e.label else 0) := by
          apply List.ext_getElem (by simp [eLen])
          intro idx' h1 h2; simp
        rw [hmap_fin]
  have hlast : eqv (.inl (Fin.last (k + 1))) =
      Fin.last ((P.singleVarAffineSubst c a idx).innerVerts + 1) := by
    apply Fin.ext; rw [subEquiv_inl_val, subPosVal_last]; rfl
  rw [poly_eq_nodePoly_last, poly_eq_nodePoly_last, ← hlast]
  exact hmain (Fin.last (k + 1))

/-! ### Constant-arity composition over `ZMod p` -/

/-- Lagrange indicator ABP for a single point `a : Fin d → ZMod p`: evaluates to `1` at `a`
and `0` elsewhere on `ZMod p` (with `[Fact p.Prime]`). -/
public noncomputable def lagrangeIndicatorZMod {p d : ℕ} [Fact p.Prime]
    (a : Fin d → ZMod p) : ABP (ZMod p) (Fin d) :=
  prodList <| (List.finRange d).map fun i =>
    prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
      fun b : Fin p =>
        (var i).add (const (-(b : ZMod p))) |>.mul (const ((a i - (b : ZMod p))⁻¹))

public theorem eval_lagrangeIndicatorZMod {p d : ℕ} [Fact p.Prime]
    (a x : Fin d → ZMod p) :
    (lagrangeIndicatorZMod a).eval x = if x = a then 1 else 0 := by
  simp only [eval, lagrangeIndicatorZMod, poly_prodList, List.map_map, map_list_prod,
    Function.comp_def]
  have hcoord : ∀ i : Fin d,
      ((((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map fun b : Fin p =>
        MvPolynomial.aeval x
          (((var i).add (const (-(b : ZMod p)))).mul (const (a i - (b : ZMod p))⁻¹)).poly)).prod =
        if x i = a i then 1 else 0 := by
    intro i
    by_cases hxi : x i = a i
    · simp only [hxi, ↓reduceIte]
      refine List.prod_eq_one fun y hy => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      have hne : (b : ZMod p) ≠ a i := by simpa using (List.mem_filter.mp hb).2
      simp only [poly_mul, poly_add, poly_var, poly_const, map_mul, map_add, aeval_X, aeval_C, hxi,
        Algebra.algebraMap_self, RingHom.id_apply]
      have hsub : a i - (b : ZMod p) ≠ 0 := sub_ne_zero.mpr hne.symm
      rw [← sub_eq_add_neg]
      exact mul_inv_cancel₀ hsub
    · simp only [hxi, ↓reduceIte]
      have hmem : (⟨(x i).val, (x i).val_lt⟩ : Fin p) ∈
          (List.finRange p).filter (fun b : Fin p => (b : ZMod p) ≠ a i) := by
        rw [List.mem_filter]
        exact ⟨List.mem_finRange _, by simpa using hxi⟩
      refine List.prod_eq_zero (List.mem_map.mpr ⟨(⟨(x i).val, (x i).val_lt⟩ : Fin p), hmem, ?_⟩)
      simp only [poly_mul, poly_add, poly_var, poly_const, map_mul, map_add, aeval_X, aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply]
      have hcast : ((⟨(x i).val, (x i).val_lt⟩ : Fin p) : ZMod p) = x i := by simp
      rw [hcast, add_neg_cancel, zero_mul]
  have h1 : ((List.finRange d).map fun i : Fin d =>
      if x i = a i then (1 : ZMod p) else 0).prod =
      ∏ i : Fin d, (if x i = a i then (1 : ZMod p) else 0) := by
    rw [← List.prod_ofFn]; congr 1
    apply List.ext_getElem (by simp)
    intro idx _ _; simp
  simp_rw [hcoord]
  rw [h1]
  by_cases hxa : x = a
  · subst hxa; simp
  · simp only [hxa, ↓reduceIte]
    have hex : ∃ i, x i ≠ a i := Function.ne_iff.mp hxa
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Any function `f : (Fin d → ZMod p) → ZMod p` on fixed arity `d` over a prime field `ZMod p`
is computed by an ABP whose size depends only on `(d, p)`. -/
public noncomputable def ofEvalFinZMod {p d : ℕ} [Fact p.Prime]
    (f : (Fin d → ZMod p) → ZMod p) : ABP (ZMod p) (Fin d) :=
  sumList <| (Finset.univ : Finset (Fin d → ZMod p)).toList.map fun a =>
    (const (f a)).mul (lagrangeIndicatorZMod a)

public theorem eval_ofEvalFinZMod {p d : ℕ} [Fact p.Prime]
    (f : (Fin d → ZMod p) → ZMod p) (x : Fin d → ZMod p) :
    (ofEvalFinZMod f).eval x = f x := by
  have htoList : ∀ (l : List (Fin d → ZMod p)) (g : (Fin d → ZMod p) → ZMod p),
      l.Nodup → (l.map g).sum = ∑ a ∈ l.toFinset, g a := fun l g hnd => by
    induction l with
    | nil => simp
    | cons a tl ih =>
      rw [List.nodup_cons] at hnd
      simp [List.toFinset_cons, Finset.sum_insert (List.mem_toFinset.not.mpr hnd.1), ih hnd.2]
  simp only [eval, ofEvalFinZMod, poly_sumList, List.map_map, map_list_sum, Function.comp_def]
  have hsum :
      (((Finset.univ : Finset (Fin d → ZMod p)).toList).map fun a =>
        MvPolynomial.aeval x (((const (f a)).mul (lagrangeIndicatorZMod a)).poly)).sum =
      ∑ a : Fin d → ZMod p, f a * (if x = a then 1 else 0) := by
    rw [htoList _ _ (Finset.nodup_toList _)]
    have htf : (Finset.univ : Finset (Fin d → ZMod p)).toList.toFinset = Finset.univ := by
      ext a; simp
    rw [htf]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [poly_mul, poly_const, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    exact congrArg (f a * ·) (eval_lagrangeIndicatorZMod a x)
  rw [hsum]
  simp

/-- Substituting ABPs `Q_1, ..., Q_d` into a `d`-ary function `f : (Fin d → ZMod p) → ZMod p`
produces an ABP computing `x ↦ f (fun i => (Q i).eval x)` of size bounded linearly in
`∑ i, (Q i).size` (with constant depending only on `(d, p)`). -/
public noncomputable def composeZMod {p d n : ℕ} [Fact p.Prime]
    (f : (Fin d → ZMod p) → ZMod p) (Q : Fin d → ABP (ZMod p) (Fin n)) :
    ABP (ZMod p) (Fin n) :=
  sumList <| (Finset.univ : Finset (Fin d → ZMod p)).toList.map fun a =>
    (const (f a)).mul <| prodList <| (List.finRange d).map fun i =>
      prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
        fun b : Fin p =>
          ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹))

public theorem eval_composeZMod {p d n : ℕ} [Fact p.Prime]
    (f : (Fin d → ZMod p) → ZMod p) (Q : Fin d → ABP (ZMod p) (Fin n)) (x : Fin n → ZMod p) :
    (composeZMod f Q).eval x = f (fun i => (Q i).eval x) := by
  have htoList : ∀ (l : List (Fin d → ZMod p)) (g : (Fin d → ZMod p) → ZMod p),
      l.Nodup → (l.map g).sum = ∑ a ∈ l.toFinset, g a := fun l g hnd => by
    induction l with
    | nil => simp
    | cons a tl ih =>
      rw [List.nodup_cons] at hnd
      simp [List.toFinset_cons, Finset.sum_insert (List.mem_toFinset.not.mpr hnd.1), ih hnd.2]
  simp only [eval, composeZMod, poly_sumList, List.map_map, map_list_sum, Function.comp_def]
  have hsum :
      (((Finset.univ : Finset (Fin d → ZMod p)).toList).map fun a =>
        MvPolynomial.aeval x (((const (f a)).mul <| prodList <| (List.finRange d).map fun i =>
          prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
            fun b : Fin p =>
              ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹))).poly)).sum =
      ∑ a : Fin d → ZMod p, f a * (if (fun i => (Q i).eval x) = a then 1 else 0) := by
    rw [htoList _ _ (Finset.nodup_toList _)]
    have htf : (Finset.univ : Finset (Fin d → ZMod p)).toList.toFinset = Finset.univ := by
      ext a; simp
    rw [htf]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [poly_mul, poly_const, map_mul, aeval_C]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    congr 1
    simp only [poly_prodList, List.map_map, map_list_prod, Function.comp_def]
    have hcoord : ∀ i : Fin d,
        ((((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map fun b : Fin p =>
          MvPolynomial.aeval x (((Q i).add (const (-(b : ZMod p)))).mul
            (const (a i - (b : ZMod p))⁻¹)).poly)).prod =
          if (Q i).eval x = a i then 1 else 0 := by
      intro i
      by_cases hxi : (Q i).eval x = a i
      · simp only [hxi, ↓reduceIte]
        refine List.prod_eq_one fun y hy => ?_
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        have hne : (b : ZMod p) ≠ a i := by simpa using (List.mem_filter.mp hb).2
        simp only [poly_mul, poly_add, poly_const, map_mul, map_add, aeval_C, eval,
          Algebra.algebraMap_self, RingHom.id_apply] at hxi ⊢
        rw [hxi, ← sub_eq_add_neg]
        exact mul_inv_cancel₀ (sub_ne_zero.mpr hne.symm)
      · simp only [hxi, ↓reduceIte]
        have hmem : (⟨((Q i).eval x).val, ((Q i).eval x).val_lt⟩ : Fin p) ∈
            (List.finRange p).filter (fun b : Fin p => (b : ZMod p) ≠ a i) := by
          rw [List.mem_filter]
          exact ⟨List.mem_finRange _, by simpa using hxi⟩
        refine List.prod_eq_zero (List.mem_map.mpr ⟨(⟨((Q i).eval x).val, _⟩ : Fin p), hmem, ?_⟩)
        simp only [poly_mul, poly_add, poly_const, map_mul, map_add, aeval_C, eval,
          Algebra.algebraMap_self, RingHom.id_apply, ZMod.natCast_zmod_val,
          add_neg_cancel, zero_mul]
    have h1 : ((List.finRange d).map fun i : Fin d =>
        if (Q i).eval x = a i then (1 : ZMod p) else 0).prod =
        ∏ i : Fin d, (if (Q i).eval x = a i then (1 : ZMod p) else 0) := by
      rw [← List.prod_ofFn]; congr 1
      apply List.ext_getElem (by simp)
      intro idx _ _; simp
    simp_rw [hcoord]
    rw [h1]
    by_cases hxa : (fun i => (Q i).eval x) = a
    · simp only [hxa, ↓reduceIte]
      rw [← hxa]; simp
    · simp only [hxa, ↓reduceIte]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hxa
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [hsum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  rfl

public theorem size_composeZMod_le {p d n : ℕ} [Fact p.Prime]
    (f : (Fin d → ZMod p) → ZMod p) (Q : Fin d → ABP (ZMod p) (Fin n)) (L : ℕ)
    (hQ : ∀ i, (Q i).size ≤ L) :
    (composeZMod f Q).size ≤ p ^ d * (d * p * (L + 10) + 10) + 2 := by
  have h1 := size_sumList_le ((Finset.univ : Finset (Fin d → ZMod p)).toList.map fun a =>
    (const (f a)).mul <| prodList <| (List.finRange d).map fun i =>
      prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
        fun b : Fin p =>
          ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹)))
  have hcard : (Finset.univ : Finset (Fin d → ZMod p)).toList.length = p ^ d := by
    simp [Finset.length_toList, ZMod.card]
  have hterm : ∀ a : Fin d → ZMod p,
      ((const (f a)).mul <| prodList <| (List.finRange d).map fun i =>
        prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
          fun b : Fin p =>
            ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹))).size ≤
      d * p * (L + 10) + 10 := by
    intro a
    have hmul := size_mul_le (const (f a)) (prodList <| (List.finRange d).map fun i =>
      prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
        fun b : Fin p =>
          ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹)))
    have hprod1 := size_prodList_le ((List.finRange d).map fun i =>
      prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
        fun b : Fin p =>
          ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹)))
    have hsum1 : (((List.finRange d).map fun i =>
        (prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
          fun b : Fin p =>
            ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹))).size)).sum ≤
        d * (p * (L + 6) + 3) := by
      calc _ ≤ ((List.finRange d).map fun _ => p * (L + 6) + 3).sum := by
            refine List.sum_le_sum fun i _ => ?_
            have hp2 := size_prodList_le (((List.finRange p).filter fun b : Fin p =>
              (b : ZMod p) ≠ a i).map fun b : Fin p =>
                ((Q i).add (const (-(b : ZMod p)))).mul (const ((a i - (b : ZMod p))⁻¹)))
            have hle_filter :
                ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).length ≤ p :=
              (List.length_filter_le _ _).trans (by simp)
            have hsum2 : ((((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
                fun b : Fin p => (((Q i).add (const (-(b : ZMod p)))).mul
                  (const ((a i - (b : ZMod p))⁻¹))).size)).sum ≤ p * (L + 6) := by
              calc _ ≤ ((((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
                    fun _ : Fin p => L + 6)).sum := by
                    refine List.sum_le_sum fun b _ => ?_
                    have hm1 := size_mul_le ((Q i).add (const (-(b : ZMod p))))
                      (const ((a i - (b : ZMod p))⁻¹))
                    have ha1 := size_add_le (Q i) (const (-(b : ZMod p)))
                    have hqi := hQ i
                    simp only [size_const] at hm1 ha1
                    omega
                _ = ((List.finRange p).filter
                      fun b : Fin p => (b : ZMod p) ≠ a i).length * (L + 6) := by
                    simp [List.sum_replicate]
                _ ≤ p * (L + 6) := Nat.mul_le_mul_right _ hle_filter
            simp only [List.map_map, Function.comp_def] at hp2
            omega
        _ = d * (p * (L + 6) + 3) := by simp [List.sum_replicate]
    simp only [size_const, List.map_map, Function.comp_def] at hmul hprod1
    have hp_pos : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    nlinarith
  have hsum_all :
      ((((Finset.univ : Finset (Fin d → ZMod p)).toList.map fun a =>
        ((const (f a)).mul <| prodList <| (List.finRange d).map fun i =>
          prodList <| ((List.finRange p).filter fun b : Fin p => (b : ZMod p) ≠ a i).map
            fun b : Fin p =>
              ((Q i).add (const (-(b : ZMod p)))).mul
                (const ((a i - (b : ZMod p))⁻¹))).size)).sum) ≤
      p ^ d * (d * p * (L + 10) + 10) := by
    calc _ ≤ (((Finset.univ : Finset (Fin d → ZMod p)).toList.map
          fun _ => d * p * (L + 10) + 10)).sum :=
            List.sum_le_sum fun a _ => hterm a
      _ = (Finset.univ : Finset (Fin d → ZMod p)).toList.length *
            (d * p * (L + 10) + 10) := by
            simp [List.sum_replicate]
      _ = p ^ d * (d * p * (L + 10) + 10) := by rw [hcard]
  simp only [composeZMod, List.map_map, Function.comp_def] at h1 ⊢
  omega

end ABP

/-- Minimum ABP size computing a polynomial `f` (in `ℕ∞`). -/
public noncomputable def abpComplexity {K : Type u} [CommRing K] {σ : Type v}
    (f : MvPolynomial σ K) : ℕ∞ :=
  ⨅ (P : ABP K σ) (_ : P.poly = f), (P.size : ℕ∞)

/-- Minimum dimension `m` of a specialization matrix (projection of `(genericMatrix K m).det`)
computing a polynomial `f` (in `ℕ∞`). -/
public noncomputable def projDetComplexity {K : Type u} [CommRing K] {σ : Type v}
    (f : MvPolynomial σ K) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : IsProjection f (genericMatrix K m).det), (m : ℕ∞)

public theorem abpComplexity_le {K : Type u} [CommRing K] {σ : Type v}
    {P : ABP K σ} {f : MvPolynomial σ K} (h : P.poly = f) :
    abpComplexity f ≤ P.size :=
  iInf₂_le P h

public theorem projDetComplexity_le {K : Type u} [CommRing K] {σ : Type v}
    {f : MvPolynomial σ K} {m : ℕ}
    (h : IsProjection f (genericMatrix K m).det) :
    projDetComplexity f ≤ m :=
  iInf₂_le m h

@[simp]
public theorem abpComplexity_zero {K : Type u} [CommRing K] {σ : Type v} :
    abpComplexity (0 : MvPolynomial σ K) = 2 := by
  refine le_antisymm
    (by simpa [ABP.size_zero] using abpComplexity_le (P := ABP.zero) ABP.poly_zero)
    (le_iInf₂ fun P _ => ?_)
  exact Nat.cast_le.mpr P.two_le_size

/-- Projection determinantal complexity is bounded above by ABP complexity. -/
public theorem projDetComplexity_le_abpComplexity {K : Type u} [CommRing K] {σ : Type v}
    (f : MvPolynomial σ K) :
    projDetComplexity f ≤ abpComplexity f :=
  le_iInf₂ fun P hP => projDetComplexity_le (hP ▸ P.isProjection_det)

end CslibFrontier.Computability.Circuit
