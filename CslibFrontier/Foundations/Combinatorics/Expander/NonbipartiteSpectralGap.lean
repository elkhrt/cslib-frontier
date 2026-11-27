/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Cheeger
public import CslibFrontier.Foundations.Combinatorics.Expander.SimpleGraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spectral Gap of Connected Non-Bipartite Regular Multigraphs

This module proves the Alon–Sudakov / Reingold spectral-gap lower bound for connected
non-bipartite regular multigraphs represented by rotation maps (`Cslib.RotationMap`), under
standard Lean axioms:

For every finite `D`-regular connected non-bipartite multigraph `G` on `V` (with self-loops and
parallel edges permitted), the two-sided spectral expansion `G.spectralExpansion` satisfies
`G.spectralExpansion ≤ 1 - 1 / (|D| * |V| ^ 2)`, equivalently
`1 / (|D| * |V| ^ 2) ≤ 1 - G.spectralExpansion`.

## Main definitions

* `CslibFrontier.RotationMap.IsBipartite`: bipartiteness of a rotation-map multigraph via a `Bool`
  2-coloring flipping across every dart (so any multigraph with a self-loop or odd cycle is
  non-bipartite).

## Main results

* `CslibFrontier.RotationMap.isBipartite_iff`: characterization of `IsBipartite`.
* `CslibFrontier.RotationMap.not_isBipartite_of_loop`: any rotation map with a self-loop is
  non-bipartite.
* `CslibFrontier.RotationMap.secondEigenvalue_le_one_sub_of_preconnected`: every connected
  `D`-regular multigraph on `|V| ≥ 2` vertices with `|D| ≥ 1` satisfies
  `G.secondEigenvalue ≤ 1 - 1 / (|D| * |V| ^ 2)`.
* `CslibFrontier.RotationMap.spectralExpansion_le_one_sub_of_not_isBipartite`: **Alon–Sudakov
  Non-Bipartite Spectral Gap Theorem**,
  `G.spectralExpansion ≤ 1 - 1 / (|D| * |V| ^ 2)` for every connected non-bipartite `D`-regular
  multigraph `G`.
* `CslibFrontier.RotationMap.le_one_sub_spectralExpansion_of_not_isBipartite`: equivalent
  spectral-gap form `1 / (|D| * |V| ^ 2) ≤ 1 - G.spectralExpansion`.
-/

public section

namespace CslibFrontier.RotationMap

open Finset
open scoped BigOperators

/-! ### 1. Bipartiteness of Rotation-Map Multigraphs -/

/-- A rotation-map multigraph `G` is **bipartite** if its vertices have a 2-coloring `V → Bool`
that changes color across every dart `(v, i)` (including self-loops, so any multigraph with a
self-loop is non-bipartite). -/
def IsBipartite {V D : Type*} (G : Cslib.RotationMap V D) : Prop :=
  ∃ c : V → Bool, ∀ v i, c (G.neighbor v i) ≠ c v

/-- Characterization of `IsBipartite` without `@[simp]`. -/
theorem isBipartite_iff {V D : Type*} (G : Cslib.RotationMap V D) :
    IsBipartite G ↔ ∃ c : V → Bool, ∀ v i, c (G.neighbor v i) ≠ c v :=
  Iff.rfl

/-- A rotation map containing a self-loop at any vertex is non-bipartite. -/
theorem not_isBipartite_of_loop {V D : Type*} (G : Cslib.RotationMap V D) {v : V} {i : D}
    (hloop : G.neighbor v i = v) : ¬ IsBipartite G := by
  rintro ⟨c, hc⟩
  exact hc v i (congrArg c hloop)

/-- A non-bipartite rotation map has a nonempty vertex type. -/
theorem nonempty_vertices_of_not_isBipartite {V D : Type*} {G : Cslib.RotationMap V D}
    (h : ¬ IsBipartite G) : Nonempty V := by
  by_contra hV
  rw [not_nonempty_iff] at hV
  exact h ⟨fun v ↦ hV.elim v, fun v ↦ hV.elim v⟩

/-- A non-bipartite rotation map has a nonempty edge-label type. -/
theorem nonempty_labels_of_not_isBipartite {V D : Type*} {G : Cslib.RotationMap V D}
    (h : ¬ IsBipartite G) : Nonempty D := by
  by_contra hD
  rw [not_nonempty_iff] at hD
  exact h ⟨fun _ ↦ false, fun _ i ↦ hD.elim i⟩

/-- For a loopless rotation map, `IsBipartite G` agrees with `G.toSimpleGraph.IsBipartite`. -/
theorem isBipartite_iff_toSimpleGraph {V D : Type*} (G : Cslib.RotationMap V D)
    (hloopless : ∀ v i, G.neighbor v i ≠ v) :
    IsBipartite G ↔ G.toSimpleGraph.IsBipartite := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun v ↦ if c v then (1 : Fin 2) else 0, fun {u w} hadj ↦ ?_⟩
    obtain ⟨_, i, rfl⟩ := G.toSimpleGraph_adj.mp hadj
    have hci := hc u i
    cases hcu : c u <;> cases hcn : c (G.neighbor u i) <;> simp_all
  · rintro ⟨col, hcol⟩
    refine ⟨fun v ↦ decide (col v = 1), fun v i ↦ ?_⟩
    have hadj : G.toSimpleGraph.Adj v (G.neighbor v i) :=
      G.toSimpleGraph_adj.mpr ⟨(hloopless v i).symm, i, rfl⟩
    have hne := hcol hadj
    rcases h1 : col v with ⟨_ | _ | _, hv'⟩ <;>
      rcases h2 : col (G.neighbor v i) with ⟨_ | _ | _, hw'⟩ <;>
      simp_all <;> omega

/-! ### 2. Dart Walks and Telescoping Estimates -/

section DartWalks

variable {V D : Type*}

/-- A sequence of darts `L : List (V × D)` forming a directed walk from `u` to `w` in `G`. -/
private inductive DartWalk (G : Cslib.RotationMap V D) : V → V → List (V × D) → Prop
  | nil (u : V) : DartWalk G u u []
  | cons {u w : V} (i : D) {L : List (V × D)} :
      DartWalk G (G.neighbor u i) w L → DartWalk G u w ((u, i) :: L)

private theorem DartWalk.nil_iff {G : Cslib.RotationMap V D} {u w : V} :
    DartWalk G u w [] ↔ u = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ .nil u⟩
  generalize hL : ([] : List (V × D)) = L at h
  cases h with
  | nil _ => rfl
  | cons _ _ => cases hL

private theorem DartWalk.cons_iff {G : Cslib.RotationMap V D} {u w : V} {p : V × D}
    {L : List (V × D)} :
    DartWalk G u w (p :: L) ↔ p.1 = u ∧ DartWalk G (G.neighbor p.1 p.2) w L := by
  constructor
  · intro h
    generalize hL : p :: L = L' at h
    cases h with
    | nil _ => cases hL
    | cons i hrest =>
      injection hL with hp htl
      subst htl
      subst hp
      exact ⟨rfl, hrest⟩
  · rintro ⟨rfl, hrest⟩
    rcases p with ⟨pv, pi⟩
    exact .cons pi hrest

private theorem DartWalk.append {G : Cslib.RotationMap V D} {u v w : V} {L₁ L₂ : List (V × D)}
    (h₁ : DartWalk G u v L₁) (h₂ : DartWalk G v w L₂) : DartWalk G u w (L₁ ++ L₂) := by
  induction h₁ with
  | nil _ => exact h₂
  | cons i _ ih => exact .cons i (ih h₂)

private theorem DartWalk.rev {G : Cslib.RotationMap V D} {u w : V} {L : List (V × D)}
    (h : DartWalk G u w L) : DartWalk G w u (L.reverse.map G.rot) := by
  induction h with
  | nil _ => exact .nil _
  | @cons u w i L' _ ih =>
    simp only [List.reverse_cons, List.map_append, List.map_singleton]
    refine ih.append ?_
    have h1 : DartWalk G (G.neighbor u i) u [(G.rot (u, i))] := by
      have hrot : G.rot (u, i) = (G.neighbor u i, (G.rot (u, i)).2) := Prod.ext rfl rfl
      rw [hrot]
      refine .cons (G.rot (u, i)).2 ?_
      rw [G.neighbor_neighbor_rot]
      exact .nil u
    exact h1

private theorem exists_dartWalk_of_simpleWalk {G : Cslib.RotationMap V D} {u w : V}
    (P : G.toSimpleGraph.Walk u w) :
    ∃ L : List (V × D), DartWalk G u w L ∧ L.map Prod.fst = P.support.dropLast := by
  induction P with
  | nil => exact ⟨[], .nil _, rfl⟩
  | @cons u v w hadj P' ih =>
    obtain ⟨_, i, rfl⟩ := G.toSimpleGraph_adj.mp hadj
    obtain ⟨L', hL', hfst⟩ := ih
    refine ⟨(u, i) :: L', .cons i hL', ?_⟩
    rw [SimpleGraph.Walk.support_cons]
    have hne : P'.support ≠ [] := SimpleGraph.Walk.support_ne_nil P'
    rw [List.dropLast_cons_of_ne_nil hne, List.map_cons, hfst]

private theorem DartWalk.abs_sub_le {G : Cslib.RotationMap V D} {u w : V} {L : List (V × D)}
    (h : DartWalk G u w L) (f : V → ℝ) :
    |f u - f w| ≤ (L.map fun p ↦ |f p.1 - f (G.neighbor p.1 p.2)|).sum := by
  induction h with
  | nil _ => simp
  | @cons u w i L' _ ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [_root_.abs_sub_le (f u) (f (G.neighbor u i)) (f w), ih]

private theorem DartWalk.abs_alt_le {G : Cslib.RotationMap V D} {u w : V} {L : List (V × D)}
    (h : DartWalk G u w L) (f : V → ℝ) :
    |f u - (-1 : ℝ) ^ L.length * f w| ≤
      (L.map fun p ↦ |f p.1 + f (G.neighbor p.1 p.2)|).sum := by
  induction h with
  | nil _ => simp
  | @cons u w i L' _ ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ]
    have hid :
        f u - (-1 : ℝ) ^ L'.length * -1 * f w =
          (f u + f (G.neighbor u i)) - (f (G.neighbor u i) - (-1 : ℝ) ^ L'.length * f w) := by
      ring
    rw [hid]
    linarith [abs_sub (f u + f (G.neighbor u i))
      (f (G.neighbor u i) - (-1 : ℝ) ^ L'.length * f w), ih]

private theorem DartWalk.split_at {G : Cslib.RotationMap V D} {u w : V} {L₁ L₂ : List (V × D)}
    (h : DartWalk G u w (L₁ ++ L₂)) :
    ∃ v : V, DartWalk G u v L₁ ∧ DartWalk G v w L₂ ∧
      ∀ q, L₂.head? = some q → q.1 = v := by
  induction L₁ generalizing u with
  | nil =>
    refine ⟨u, .nil u, h, ?_⟩
    intro q hq
    cases h with
    | nil _ => simp at hq
    | cons i _ => simp at hq; exact congrArg Prod.fst hq.symm
  | cons p L₁' ih =>
    cases h with
    | cons i h' =>
      obtain ⟨v, h₁, h₂, hhead⟩ := ih h'
      exact ⟨v, .cons i h₁, h₂, hhead⟩

private theorem DartWalk.mem_Endpoints_closed {G : Cslib.RotationMap V D} {u : V}
    {L : List (V × D)} (h : DartWalk G u u L) (hl : L ≠ []) :
    ∀ p ∈ L, p.1 ∈ L.map Prod.fst ∧ G.neighbor p.1 p.2 ∈ L.map Prod.fst := by
  have hmem_start : u ∈ L.map Prod.fst := by
    cases h with
    | nil _ => exact absurd rfl hl
    | cons i _ => simp
  intro p hp
  refine ⟨List.mem_map_of_mem hp, ?_⟩
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hp
  obtain ⟨v, _, h₂, _⟩ := h.split_at (L₁ := L₁) (L₂ := p :: L₂)
  cases h₂ with
  | cons i hrest =>
    cases L₂ with
    | nil =>
      cases hrest with
      | nil _ => simpa using hmem_start
    | cons q L₂' =>
      cases hrest with
      | cons j _ =>
        simp

end DartWalks

/-! ### 3. Upper Bound on the Second Eigenvalue for Connected Multigraphs -/

section ConnectedUpperBound

private theorem sq_sum_le_card_mul_sum_sq_real {α : Type*} (s : Finset α) (g : α → ℝ) :
    (∑ x ∈ s, g x) ^ 2 ≤ (#s : ℝ) * ∑ x ∈ s, g x ^ 2 := by
  have h0 : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (g x - g y) ^ 2 :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  have hid :
      ∑ x ∈ s, ∑ y ∈ s, (g x - g y) ^ 2 =
        2 * (#s : ℝ) * (∑ x ∈ s, g x ^ 2) - 2 * (∑ x ∈ s, g x) ^ 2 := by
    have hpt (x : α) :
        ∑ y ∈ s, (g x - g y) ^ 2 =
          (#s : ℝ) * g x ^ 2 - 2 * g x * (∑ y ∈ s, g y) + ∑ y ∈ s, g y ^ 2 := by
      have h1 (y : α) : (g x - g y) ^ 2 = g x ^ 2 - 2 * (g x * g y) + g y ^ 2 := by ring
      simp only [h1, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      ring
    simp only [hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, sum_const,
      nsmul_eq_mul]
    ring
  linarith

variable {V D : Type*} [Fintype V] [Fintype D]

private theorem sum_dart_sub_sq_eq (G : Cslib.RotationMap V D) (f : V → ℝ) :
    ∑ p : V × D, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 =
      2 * (Fintype.card D : ℝ) * (Fintype.card V : ℝ) *
        (𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  have hexp :
      𝔼 p : V × D, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 =
        2 * (𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v) := by
    rw [Fintype.expect_prod_type]
    have hpt (v : V) (i : D) :
        (f v - f (G.neighbor v i)) ^ 2 =
          f v ^ 2 - 2 * (f v * f (G.neighbor v i)) + f (G.neighbor v i) ^ 2 := by ring
    simp only [hpt, expect_add_distrib, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
    rw [G.expect_expect_neighbor fun w ↦ f w ^ 2]
    have hw : 𝔼 v, f v * 𝔼 i, f (G.neighbor v i) = 𝔼 v, f v * G.walk f v :=
      expect_congr rfl fun v _ ↦ by rw [Cslib.RotationMap.walk_apply]
    rw [hw]
    ring
  have hcard := Fintype.card_mul_expect (fun p : V × D ↦ (f p.1 - f (G.neighbor p.1 p.2)) ^ 2)
  rw [Fintype.card_prod, Nat.cast_mul] at hcard
  rw [← hcard, hexp]
  ring

private theorem sum_dart_add_sq_eq (G : Cslib.RotationMap V D) (f : V → ℝ) :
    ∑ p : V × D, (f p.1 + f (G.neighbor p.1 p.2)) ^ 2 =
      2 * (Fintype.card D : ℝ) * (Fintype.card V : ℝ) *
        (𝔼 v, f v ^ 2 + 𝔼 v, f v * G.walk f v) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  have hexp :
      𝔼 p : V × D, (f p.1 + f (G.neighbor p.1 p.2)) ^ 2 =
        2 * (𝔼 v, f v ^ 2 + 𝔼 v, f v * G.walk f v) := by
    rw [Fintype.expect_prod_type]
    have hpt (v : V) (i : D) :
        (f v + f (G.neighbor v i)) ^ 2 =
          f v ^ 2 + 2 * (f v * f (G.neighbor v i)) + f (G.neighbor v i) ^ 2 := by ring
    simp only [hpt, expect_add_distrib, ← mul_expect, Fintype.expect_const]
    rw [G.expect_expect_neighbor fun w ↦ f w ^ 2]
    have hw : 𝔼 v, f v * 𝔼 i, f (G.neighbor v i) = 𝔼 v, f v * G.walk f v :=
      expect_congr rfl fun v _ ↦ by rw [Cslib.RotationMap.walk_apply]
    rw [hw]
    ring
  have hcard := Fintype.card_mul_expect (fun p : V × D ↦ (f p.1 + f (G.neighbor p.1 p.2)) ^ 2)
  rw [Fintype.card_prod, Nat.cast_mul] at hcard
  rw [← hcard, hexp]
  ring

private theorem expect_mul_walk_le_of_preconnected [Nonempty D] (G : Cslib.RotationMap V D)
    (hconn : G.toSimpleGraph.Preconnected) {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    𝔼 v, f v * G.walk f v ≤
      (1 - 1 / ((Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2)) * 𝔼 v, f v ^ 2 := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hf0 : ∀ v, f v = 0 := fun v ↦ by
      have : 𝔼 w, f w = f v := by
        calc 𝔼 w, f w = 𝔼 _w : V, f v :=
              expect_congr rfl fun w _ ↦ congrArg f (Subsingleton.elim w v)
          _ = f v := Fintype.expect_const (f v)
      linarith
    simp [hf0]
  have hN2 : 2 ≤ Fintype.card V := Fintype.one_lt_card
  have hN2_real : (2 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.ofNat_le_cast.mpr hN2
  have hD1 : 1 ≤ Fintype.card D := Fintype.card_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set d : ℝ := (Fintype.card D : ℝ)
  have hN_pos : 0 < N := by linarith
  have hd_pos : 0 < d := by positivity
  set E := ∑ p : V × D, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2
  have hE_eq : E = 2 * d * N * (𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v) :=
    sum_dart_sub_sq_eq G f
  have hE_nn : 0 ≤ E := sum_nonneg fun _ _ ↦ sq_nonneg _
  -- Pairwise difference bound `(f u - f w)^2 ≤ (N - 1) * E` for every `(u, w)`.
  have hpair (u w : V) : (f u - f w) ^ 2 ≤ (N - 1) * E := by
    by_cases huw : u = w
    · subst huw
      rw [sub_self, zero_pow two_ne_zero]
      exact mul_nonneg (by linarith) hE_nn
    obtain ⟨q⟩ := hconn u w
    let P := q.bypass
    have hP_path : P.IsPath := q.bypass_isPath
    have hP_len : P.length ≤ Fintype.card V - 1 := Nat.le_sub_one_of_lt hP_path.length_lt
    obtain ⟨L, hL, hfst⟩ := exists_dartWalk_of_simpleWalk P
    have hL_nodup : L.Nodup := by
      refine List.Nodup.of_map Prod.fst ?_
      rw [hfst]
      exact hP_path.support_nodup.sublist (List.dropLast_sublist _)
    have hL_len : L.length = P.length := by
      have := congrArg List.length hfst
      rw [List.length_map, List.length_dropLast, SimpleGraph.Walk.length_support] at this
      omega
    have habs := hL.abs_sub_le f
    have hsum_finset :
        (L.map fun p ↦ |f p.1 - f (G.neighbor p.1 p.2)|).sum =
          ∑ p ∈ L.toFinset, |f p.1 - f (G.neighbor p.1 p.2)| :=
      (List.sum_toFinset _ hL_nodup).symm
    rw [hsum_finset] at habs
    have hsq1 : (f u - f w) ^ 2 ≤
        (∑ p ∈ L.toFinset, |f p.1 - f (G.neighbor p.1 p.2)|) ^ 2 := by
      rw [← sq_abs (f u - f w)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hcs :
        (∑ p ∈ L.toFinset, |f p.1 - f (G.neighbor p.1 p.2)|) ^ 2 ≤
          (#L.toFinset : ℝ) * ∑ p ∈ L.toFinset, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 := by
      simpa only [sq_abs] using
        sq_sum_le_card_mul_sum_sq_real L.toFinset (fun p ↦ |f p.1 - f (G.neighbor p.1 p.2)|)
    have hsub_E : ∑ p ∈ L.toFinset, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 ≤ E :=
      sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    have hcard_le : (#L.toFinset : ℝ) ≤ N - 1 := by
      rw [List.card_toFinset, hL_nodup.dedup, hL_len]
      have : (P.length : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
        rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
        exact_mod_cast hP_len
      exact this
    calc (f u - f w) ^ 2 ≤ (#L.toFinset : ℝ) *
          ∑ p ∈ L.toFinset, (f p.1 - f (G.neighbor p.1 p.2)) ^ 2 := hsq1.trans hcs
      _ ≤ (N - 1) * E := mul_le_mul hcard_le hsub_E (sum_nonneg fun _ _ ↦ sq_nonneg _)
          (by linarith)
  -- Sum over off-diagonal pairs `(u, w)` (`u ≠ w`).
  let offDiag : Finset (V × V) := univ.filter fun p : V × V ↦ p.1 ≠ p.2
  have hsum_var : ∑ p ∈ offDiag, (f p.1 - f p.2) ^ 2 = 2 * N ^ 2 * 𝔼 v, f v ^ 2 := by
    have hall : ∑ p ∈ offDiag, (f p.1 - f p.2) ^ 2 = ∑ p : V × V, (f p.1 - f p.2) ^ 2 := by
      refine sum_subset (subset_univ _) fun p _ hp ↦ ?_
      simp only [offDiag, mem_filter, mem_univ, true_and, not_not] at hp
      simp [hp]
    rw [hall, Fintype.sum_prod_type]
    have hsum_f : ∑ v : V, f v = 0 := by
      have := Fintype.card_mul_expect f
      rw [hf, mul_zero] at this
      exact this.symm
    have hsum_sq : ∑ v : V, f v ^ 2 = N * 𝔼 v, f v ^ 2 :=
      (Fintype.card_mul_expect fun v ↦ f v ^ 2).symm
    have hpt (u : V) :
        ∑ w : V, (f u - f w) ^ 2 = N * f u ^ 2 - 2 * f u * (∑ w : V, f w) + ∑ w : V, f w ^ 2 := by
      have h1 (w : V) : (f u - f w) ^ 2 = f u ^ 2 - 2 * f u * f w + f w ^ 2 := by ring
      simp only [h1, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        ← mul_sum]
      rfl
    simp only [hpt, hsum_f, mul_zero, sub_zero, sum_add_distrib, ← mul_sum, sum_const, card_univ,
      nsmul_eq_mul, hsum_sq]
    ring
  have hcard_off : (#offDiag : ℝ) ≤ N * N := by
    have h1 : (#offDiag : ℝ) ≤ (Fintype.card (V × V) : ℝ) :=
      Nat.cast_le.mpr (card_filter_le _ _)
    rw [Fintype.card_prod, Nat.cast_mul] at h1
    exact h1
  have hbound : 2 * N ^ 2 * 𝔼 v, f v ^ 2 ≤ N * N * ((N - 1) * E) := by
    rw [← hsum_var]
    calc ∑ p ∈ offDiag, (f p.1 - f p.2) ^ 2
        ≤ ∑ _p ∈ offDiag, (N - 1) * E := sum_le_sum fun p _ ↦ hpair p.1 p.2
      _ = (#offDiag : ℝ) * ((N - 1) * E) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N * N * ((N - 1) * E) :=
          mul_le_mul_of_nonneg_right hcard_off (mul_nonneg (by linarith) hE_nn)
  have hN1_E : (N - 1) * E ≤ N * E :=
    mul_le_mul_of_nonneg_right (by linarith) hE_nn
  have h1 : 2 * N ^ 2 * 𝔼 v, f v ^ 2 ≤ N * N * (N * E) :=
    hbound.trans (mul_le_mul_of_nonneg_left hN1_E (by positivity))
  rw [hE_eq] at h1
  have h2 : 𝔼 v, f v ^ 2 ≤ d * N ^ 2 * (𝔼 v, f v ^ 2 - 𝔼 v, f v * G.walk f v) := by
    nlinarith [sq_pos_of_pos hN_pos]
  rw [sub_mul, div_mul_eq_mul_div, le_sub_iff_add_le, ← le_sub_iff_add_le',
    div_le_iff₀ (by positivity : 0 < d * N ^ 2)]
  linarith

/-- Every connected `D`-regular multigraph on at least two vertices with `|D| ≥ 1` has signed
second eigenvalue `G.secondEigenvalue ≤ 1 - 1 / (|D| * |V| ^ 2)`. -/
theorem secondEigenvalue_le_one_sub_of_preconnected [Nontrivial V] [Nonempty D]
    (G : Cslib.RotationMap V D) (hconn : G.toSimpleGraph.Preconnected) :
    G.secondEigenvalue ≤ 1 - 1 / ((Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2) :=
  G.secondEigenvalue_le_iff.mpr fun _ hf ↦ expect_mul_walk_le_of_preconnected G hconn hf

end ConnectedUpperBound

/-! ### 4. Lower Bound on the Smallest Eigenvalue for Non-Bipartite Multigraphs -/

section NonbipartiteLowerBound

private theorem exists_odd_closed_dartWalk {V D : Type*} {G : Cslib.RotationMap V D}
    (hconn : G.toSimpleGraph.Preconnected) (hnb : ¬ IsBipartite G) :
    ∃ (u₀ : V) (L : List (V × D)), DartWalk G u₀ u₀ L ∧ Odd L.length := by
  classical
  have : Nonempty V := nonempty_vertices_of_not_isBipartite hnb
  obtain ⟨x₀⟩ := ‹Nonempty V›
  by_contra hno
  push Not at hno
  let OddReach (v : V) : Prop := ∃ L : List (V × D), DartWalk G x₀ v L ∧ Odd L.length
  have hexists_walk (u w : V) : ∃ L : List (V × D), DartWalk G u w L := by
    obtain ⟨P⟩ := hconn u w
    obtain ⟨L, hL, _⟩ := exists_dartWalk_of_simpleWalk P
    exact ⟨L, hL⟩
  have hnot_both (v : V) :
      ¬ ((∃ L₁, DartWalk G x₀ v L₁ ∧ Odd L₁.length) ∧
          (∃ L₂, DartWalk G x₀ v L₂ ∧ Even L₂.length)) := by
    rintro ⟨⟨L₁, hL₁, hodd⟩, ⟨L₂, hL₂, heven⟩⟩
    have hclosed : DartWalk G x₀ x₀ (L₁ ++ L₂.reverse.map G.rot) := hL₁.append hL₂.rev
    have hlen : Odd (L₁ ++ L₂.reverse.map G.rot).length := by
      rw [List.length_append, List.length_map, List.length_reverse]
      exact hodd.add_even heven
    exact (Nat.not_even_iff_odd.mpr hlen) (hno x₀ _ hclosed)
  have heither (v : V) :
      (∃ L₁, DartWalk G x₀ v L₁ ∧ Odd L₁.length) ∨
        (∃ L₂, DartWalk G x₀ v L₂ ∧ Even L₂.length) := by
    obtain ⟨L, hL⟩ := hexists_walk x₀ v
    rcases Nat.even_or_odd L.length with hev | hod
    · exact .inr ⟨L, hL, hev⟩
    · exact .inl ⟨L, hL, hod⟩
  refine hnb ⟨fun v ↦ decide (OddReach v), fun v i ↦ ?_⟩
  rcases heither v with ⟨L, hL, hodd⟩ | ⟨L, hL, heven⟩
  · have hv : decide (OddReach v) = true := decide_eq_true ⟨L, hL, hodd⟩
    have hnext_even : ∃ L₂, DartWalk G x₀ (G.neighbor v i) L₂ ∧ Even L₂.length := by
      refine ⟨L ++ [(v, i)], hL.append (.cons i (.nil _)), ?_⟩
      rw [List.length_append, List.length_singleton]
      exact hodd.add_odd odd_one
    have hnext_not_odd : ¬ OddReach (G.neighbor v i) := fun hod ↦
      hnot_both (G.neighbor v i) ⟨hod, hnext_even⟩
    simp [hv, decide_eq_false hnext_not_odd]
  · have hv_not : ¬ OddReach v := fun hod ↦ hnot_both v ⟨hod, ⟨L, hL, heven⟩⟩
    have hv : decide (OddReach v) = false := decide_eq_false hv_not
    have hnext_odd : OddReach (G.neighbor v i) := by
      refine ⟨L ++ [(v, i)], hL.append (.cons i (.nil _)), ?_⟩
      rw [List.length_append, List.length_singleton]
      exact heven.add_odd odd_one
    simp [hv, decide_eq_true hnext_odd]

private theorem exists_nodup_odd_closed_dartWalk {V D : Type*} {G : Cslib.RotationMap V D}
    (hconn : G.toSimpleGraph.Preconnected) (hnb : ¬ IsBipartite G) :
    ∃ (u₀ : V) (L₀ : List (V × D)),
      DartWalk G u₀ u₀ L₀ ∧ Odd L₀.length ∧ (L₀.map Prod.fst).Nodup := by
  classical
  have hex : ∃ n : ℕ, ∃ (u₀ : V) (L : List (V × D)),
      DartWalk G u₀ u₀ L ∧ Odd L.length ∧ L.length = n := by
    obtain ⟨u₀, L, hL, hodd⟩ := exists_odd_closed_dartWalk hconn hnb
    exact ⟨L.length, u₀, L, hL, hodd, rfl⟩
  let n₀ := Nat.find hex
  obtain ⟨u₀, L₀, hL₀, hodd₀, hlen₀⟩ := Nat.find_spec hex
  refine ⟨u₀, L₀, hL₀, hodd₀, ?_⟩
  by_contra hnot_nd
  -- If `L₀.map Prod.fst` has a duplicate, split `L₀ = A ++ (p :: B) ++ (q :: C)` with `p.1 = q.1`.
  rw [List.nodup_iff_injective_getElem, Function.Injective] at hnot_nd
  push Not at hnot_nd
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij_eq, hij_ne⟩ := hnot_nd
  have hij_val : i ≠ j := fun h ↦ hij_ne (Fin.ext h)
  have hshort : ∀ (a b : ℕ) (hab : a < b) (hb : b < (L₀.map Prod.fst).length),
      (L₀.map Prod.fst)[a]'(hab.trans hb) = (L₀.map Prod.fst)[b]'hb → False := by
    intro a b hab hb heq
    have hb' : b < L₀.length := by simpa only [List.length_map] using hb
    have ha' : a < L₀.length := hab.trans hb'
    let A := L₀.take a
    let B := (L₀.drop a).take (b - a)
    let C := L₀.drop b
    have hsplit : L₀ = A ++ B ++ C := by
      have hdrop_eq : L₀.drop b = (L₀.drop a).drop (b - a) := by
        rw [List.drop_drop, Nat.add_sub_of_le hab.le]
      dsimp only [A, B, C]
      rw [List.append_assoc, hdrop_eq, List.take_append_drop, List.take_append_drop]
    have hB_len : B.length = b - a := by
      dsimp only [B]; rw [List.length_take, List.length_drop]; omega
    have hA_len : A.length = a := by dsimp only [A]; rw [List.length_take]; omega
    have hC_len : C.length = L₀.length - b := by dsimp only [C]; rw [List.length_drop]
    have hB_pos : 0 < B.length := by omega
    have hB_lt : B.length < n₀ := by dsimp only [n₀]; omega
    have hAC_lt : (A ++ C).length < n₀ := by
      dsimp only [n₀]; rw [List.length_append, hA_len, hC_len]; omega
    have hL_split : DartWalk G u₀ u₀ (A ++ (B ++ C)) := by
      rwa [← List.append_assoc, ← hsplit]
    obtain ⟨v₁, hA_walk, hBC_walk, hhead₁⟩ := hL_split.split_at (L₁ := A) (L₂ := B ++ C)
    obtain ⟨v₂, hB_walk, hC_walk, hhead₂⟩ := hBC_walk.split_at (L₁ := B) (L₂ := C)
    have hv₁_eq : v₁ = (L₀[a]'ha').1 := by
      have hneB : B ≠ [] := List.ne_nil_of_length_pos hB_pos
      have hBC_head : (B ++ C).head? = B.head? := List.head?_append_of_ne_nil B hneB
      have hB_head : B.head? = some (L₀[a]'ha') := by
        dsimp only [B]
        have hba : b - a = (b - a - 1) + 1 := by omega
        rw [List.drop_eq_getElem_cons ha', hba]
        rfl
      exact (hhead₁ (L₀[a]'ha') (hBC_head.trans hB_head)).symm
    have hv₂_eq : v₂ = (L₀[b]'hb').1 := by
      have hC_head : C.head? = some (L₀[b]'hb') := by
        dsimp only [C]
        rw [List.head?_drop, List.getElem?_eq_getElem hb']
      exact (hhead₂ (L₀[b]'hb') hC_head).symm
    have hv₁₂ : v₁ = v₂ := by
      rw [hv₁_eq, hv₂_eq]
      simpa [List.getElem_map] using heq
    subst hv₁₂
    have hAC_walk : DartWalk G u₀ u₀ (A ++ C) := hA_walk.append hC_walk
    have hlen_sum : L₀.length = B.length + (A ++ C).length := by
      rw [List.length_append, hA_len, hB_len, hC_len]; omega
    rcases Nat.even_or_odd B.length with hB_ev | hB_od
    · have hAC_od : Odd (A ++ C).length := by
        rcases Nat.even_or_odd (A ++ C).length with hAC_ev | hAC_od
        · exfalso
          have : Even L₀.length := by rw [hlen_sum]; exact hB_ev.add hAC_ev
          exact (Nat.not_even_iff_odd.mpr hodd₀) this
        · exact hAC_od
      exact Nat.find_min hex hAC_lt ⟨u₀, A ++ C, hAC_walk, hAC_od, rfl⟩
    · exact Nat.find_min hex hB_lt ⟨v₁, B, hB_walk, hB_od, rfl⟩
  rcases lt_or_gt_of_ne hij_val with hlt | hgt
  · exact hshort i j hlt hj hij_eq
  · exact hshort j i hgt hi hij_eq.symm

variable {V D : Type*} [Fintype V] [Fintype D]

private theorem neg_expect_mul_walk_le_of_not_isBipartite (G : Cslib.RotationMap V D)
    (hconn : G.toSimpleGraph.Preconnected) (hnb : ¬ IsBipartite G) (f : V → ℝ) :
    -(1 - 1 / ((Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2)) * 𝔼 v, f v ^ 2 ≤
      𝔼 v, f v * G.walk f v := by
  classical
  have : Nonempty V := nonempty_vertices_of_not_isBipartite hnb
  have : Nonempty D := nonempty_labels_of_not_isBipartite hnb
  obtain ⟨u₀, L₀, hL₀, hodd₀, hnd₀⟩ := exists_nodup_odd_closed_dartWalk hconn hnb
  have hL₀_pos : 0 < L₀.length := by
    rcases hodd₀ with ⟨k, hk⟩; omega
  have hL₀_ne : L₀ ≠ [] := List.ne_nil_of_length_pos hL₀_pos
  have hL₀_dart_nd : L₀.Nodup := List.Nodup.of_map Prod.fst hnd₀
  let C_list := L₀.map Prod.fst
  let C : Finset V := C_list.toFinset
  have hC_card : #C = L₀.length := by
    dsimp only [C, C_list]
    rw [List.card_toFinset, hnd₀.dedup, List.length_map]
  have hu₀_mem : u₀ ∈ C := by
    dsimp only [C, C_list]
    rw [List.mem_toFinset]
    exact (hL₀.mem_Endpoints_closed hL₀_ne _ (List.head_mem hL₀_ne)).1 |> fun _ ↦ by
      cases hL₀ with
      | nil _ => exact absurd rfl hL₀_ne
      | cons _ _ => simp
  -- Every `z ∈ C` satisfies `2 * |f z| ≤ ∑ p ∈ L₀.toFinset, |f p.1 + f (G.neighbor p.1 p.2)|`.
  have hcycle_bound (z : V) (hz : z ∈ C) :
      2 * |f z| ≤ ∑ p ∈ L₀.toFinset, |f p.1 + f (G.neighbor p.1 p.2)| := by
    have hz_list : z ∈ L₀.map Prod.fst := List.mem_toFinset.mp hz
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hz_list
    obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hp₀
    have hwalk_split : DartWalk G u₀ u₀ (L₁ ++ (p₀ :: L₂)) := hsplit ▸ hL₀
    obtain ⟨v, h₁, h₂, hhead⟩ := hwalk_split.split_at (L₁ := L₁) (L₂ := p₀ :: L₂)
    have hv : p₀.1 = v := hhead p₀ rfl
    subst hv
    let Lrot := (p₀ :: L₂) ++ L₁
    have hrot_walk : DartWalk G p₀.1 p₀.1 Lrot := h₂.append h₁
    have hrot_len : Lrot.length = L₀.length := by
      dsimp only [Lrot]
      rw [hsplit, List.length_append, List.length_append, add_comm]
    have hrot_odd : Odd Lrot.length := hrot_len ▸ hodd₀
    have habs := hrot_walk.abs_alt_le f
    rw [hrot_odd.neg_one_pow] at habs
    have h2 : |2 * f p₀.1| = 2 * |f p₀.1| := by rw [abs_mul, abs_of_pos (by norm_num)]
    have h1 : f p₀.1 - (-1 : ℝ) * f p₀.1 = 2 * f p₀.1 := by ring
    rw [h1, h2] at habs
    have hrot_perm : Lrot.Perm L₀ := by
      dsimp only [Lrot]
      rw [hsplit]
      exact List.perm_append_comm
    have hrot_nd : Lrot.Nodup := hrot_perm.nodup_iff.mpr hL₀_dart_nd
    have hfin_eq : Lrot.toFinset = L₀.toFinset := by
      ext x; simp [hrot_perm.mem_iff]
    rw [← List.sum_toFinset _ hrot_nd, hfin_eq] at habs
    exact habs
  -- For any `u : V`, pick a minimum-length dart walk `R` from `u` to `C`, giving `S_u` with
  -- `#S_u ≤ 2 * N - 1` and `4 * f u ^ 2 ≤ (2 * N - 1) * ∑_{V × D} (f + f ∘ neighbor)^2`.
  have hN1 : 1 ≤ Fintype.card V := Fintype.card_pos
  have hN1_real : (1 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.one_le_cast.mpr hN1
  have hD1 : 1 ≤ Fintype.card D := Fintype.card_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set d : ℝ := (Fintype.card D : ℝ)
  set Eplus := ∑ p : V × D, (f p.1 + f (G.neighbor p.1 p.2)) ^ 2
  have hEp_eq : Eplus = 2 * d * N * (𝔼 v, f v ^ 2 + 𝔼 v, f v * G.walk f v) :=
    sum_dart_add_sq_eq G f
  have hEp_nn : 0 ≤ Eplus := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hvertex_bound (u : V) : 4 * f u ^ 2 ≤ (2 * N - 1) * Eplus := by
    have hex_R : ∃ m : ℕ, ∃ (z : V) (R : List (V × D)),
        z ∈ C ∧ DartWalk G u z R ∧ R.length = m := by
      obtain ⟨P⟩ := hconn u u₀
      obtain ⟨R, hR, _⟩ := exists_dartWalk_of_simpleWalk P
      exact ⟨R.length, u₀, R, hu₀_mem, hR, rfl⟩
    let m₀ := Nat.find hex_R
    obtain ⟨z, R, hzC, hR, hR_len⟩ := Nat.find_spec hex_R
    -- Every `p ∈ R` has `p.1 ∉ C`.
    have hR_not_C : ∀ p ∈ R, p.1 ∉ C := by
      intro p hp hpC
      obtain ⟨R₁, R₂, hR_eq⟩ := List.append_of_mem hp
      have hwalk_sp : DartWalk G u z (R₁ ++ (p :: R₂)) := hR_eq ▸ hR
      obtain ⟨v, h₁, _, hhead⟩ := hwalk_sp.split_at (L₁ := R₁) (L₂ := p :: R₂)
      have hv : p.1 = v := hhead p rfl
      subst hv
      have hlt : R₁.length < m₀ := by
        dsimp only [m₀]; rw [← hR_len, hR_eq, List.length_append, List.length_cons]; omega
      exact Nat.find_min hex_R hlt ⟨p.1, R₁, hpC, h₁, rfl⟩
    -- `R.map Prod.fst` is `Nodup`.
    have hR_fst_nd : (R.map Prod.fst).Nodup := by
      by_contra hnot
      rw [List.nodup_iff_injective_getElem, Function.Injective] at hnot
      push Not at hnot
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij_eq, hij_ne⟩ := hnot
      have hij_val : i ≠ j := fun h ↦ hij_ne (Fin.ext h)
      have hshort : ∀ (a b : ℕ) (hab : a < b) (hb : b < (R.map Prod.fst).length),
          (R.map Prod.fst)[a]'(hab.trans hb) = (R.map Prod.fst)[b]'hb → False := by
        intro a b hab hb heq
        have hb' : b < R.length := by simpa only [List.length_map] using hb
        have ha' : a < R.length := hab.trans hb'
        let A := R.take a
        let B := (R.drop a).take (b - a)
        let Cr := R.drop b
        have hsp : R = A ++ B ++ Cr := by
          have hdrop_eq : R.drop b = (R.drop a).drop (b - a) := by
            rw [List.drop_drop, Nat.add_sub_of_le hab.le]
          dsimp only [A, B, Cr]
          rw [List.append_assoc, hdrop_eq, List.take_append_drop, List.take_append_drop]
        have hA_l : A.length = a := by dsimp only [A]; rw [List.length_take]; omega
        have hCr_l : Cr.length = R.length - b := by dsimp only [Cr]; rw [List.length_drop]
        have hB_pos : 0 < B.length := by
          dsimp only [B]; rw [List.length_take, List.length_drop]; omega
        have hsp_w : DartWalk G u z (A ++ (B ++ Cr)) := by rwa [← List.append_assoc, ← hsp]
        obtain ⟨v₁, hA_w, hBCr_w, hh₁⟩ := hsp_w.split_at (L₁ := A) (L₂ := B ++ Cr)
        obtain ⟨v₂, _, hCr_w, hh₂⟩ := hBCr_w.split_at (L₁ := B) (L₂ := Cr)
        have hv₁ : v₁ = (R[a]'ha').1 := by
          have hneB : B ≠ [] := List.ne_nil_of_length_pos hB_pos
          have h1 : (B ++ Cr).head? = B.head? := List.head?_append_of_ne_nil B hneB
          have h2 : B.head? = some (R[a]'ha') := by
            dsimp only [B]
            have hba : b - a = (b - a - 1) + 1 := by omega
            rw [List.drop_eq_getElem_cons ha', hba]
            rfl
          exact (hh₁ _ (h1.trans h2)).symm
        have hv₂ : v₂ = (R[b]'hb').1 := by
          have h2 : Cr.head? = some (R[b]'hb') := by
            dsimp only [Cr]; rw [List.head?_drop, List.getElem?_eq_getElem hb']
          exact (hh₂ _ h2).symm
        have hv12 : v₁ = v₂ := by
          rw [hv₁, hv₂]; simpa [List.getElem_map] using heq
        subst hv12
        have hACr_lt : (A ++ Cr).length < m₀ := by
          dsimp only [m₀]; rw [List.length_append, hA_l, hCr_l]; omega
        exact Nat.find_min hex_R hACr_lt ⟨z, A ++ Cr, hzC, hA_w.append hCr_w, rfl⟩
      rcases lt_or_gt_of_ne hij_val with hlt | hgt
      · exact hshort i j hlt hj hij_eq
      · exact hshort j i hgt hi hij_eq.symm
    have hR_nd : R.Nodup := List.Nodup.of_map Prod.fst hR_fst_nd
    have hRrot_nd : (R.map G.rot).Nodup := hR_nd.map G.rot_involutive.injective
    -- Disjointness of `R.toFinset`, `(R.map G.rot).toFinset`, and `L₀.toFinset`.
    have hdisj_RL₀ : Disjoint R.toFinset L₀.toFinset := by
      rw [Finset.disjoint_left]
      intro p hpR hpL₀
      have hp_not := hR_not_C p (List.mem_toFinset.mp hpR)
      have hp_in : p.1 ∈ C := by
        dsimp only [C, C_list]
        rw [List.mem_toFinset]
        exact (hL₀.mem_Endpoints_closed hL₀_ne p (List.mem_toFinset.mp hpL₀)).1
      exact hp_not hp_in
    have hdisj_RrotL₀ : Disjoint (R.map G.rot).toFinset L₀.toFinset := by
      rw [Finset.disjoint_left]
      intro p hpRrot hpL₀
      obtain ⟨q, hqR, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hpRrot)
      have hq_not := hR_not_C q hqR
      have hneigh_in : G.neighbor (G.rot q).1 (G.rot q).2 ∈ C := by
        dsimp only [C, C_list]
        rw [List.mem_toFinset]
        exact (hL₀.mem_Endpoints_closed hL₀_ne (G.rot q) (List.mem_toFinset.mp hpL₀)).2
      have hneigh_eq : G.neighbor (G.rot q).1 (G.rot q).2 = q.1 := by
        rcases q with ⟨qv, qi⟩
        exact G.neighbor_neighbor_rot qv qi
      rw [hneigh_eq] at hneigh_in
      exact hq_not hneigh_in
    have hdisj_RRrot : Disjoint R.toFinset (R.map G.rot).toFinset := by
      rw [Finset.disjoint_left]
      intro p hpR hpRrot
      have hpR' := List.mem_toFinset.mp hpR
      obtain ⟨q, hqR, hrot_eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hpRrot)
      -- `p.1 = G.neighbor q.1 q.2` and `G.neighbor p.1 p.2 = q.1`.
      have hq_neigh : G.neighbor q.1 q.2 = p.1 := by
        rw [Cslib.RotationMap.neighbor_def, show (q.1, q.2) = q from Prod.mk.eta, hrot_eq]
      have hp_neigh : G.neighbor p.1 p.2 = q.1 := by
        have := congrArg G.rot hrot_eq
        rw [G.rot_rot] at this
        rw [Cslib.RotationMap.neighbor_def, show (p.1, p.2) = p from Prod.mk.eta, ← this]
      -- Find indices `a` of `p` and `b` of `q` in `R`.
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hpR'
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hqR
      have hstep_walk : ∀ (k : ℕ) (hk : k < R.length),
          if hk1 : k + 1 < R.length then G.neighbor (R[k]).1 (R[k]).2 = (R[k + 1]).1
          else G.neighbor (R[k]).1 (R[k]).2 = z := by
        intro k hk
        have hsp_w : DartWalk G u z (R.take k ++ (R[k] :: R.drop (k + 1))) := by
          rwa [← List.drop_eq_getElem_cons hk, List.take_append_drop]
        obtain ⟨vk, _, h2, _⟩ := hsp_w.split_at (L₁ := R.take k) (L₂ := R[k] :: R.drop (k + 1))
        obtain ⟨_, hrest⟩ := DartWalk.cons_iff.mp h2
        split_ifs with hk1
        · rw [List.drop_eq_getElem_cons hk1] at hrest
          exact (DartWalk.cons_iff.mp hrest).1.symm
        · rw [List.drop_eq_nil_of_le (by omega)] at hrest
          exact DartWalk.nil_iff.mp hrest
      have hnext_b := hstep_walk b hb
      let hinj := List.nodup_iff_injective_getElem.mp hR_fst_nd
      split_ifs at hnext_b with hb1
      · have hab1 : a = b + 1 := by
          have heq_fst : (R.map Prod.fst)[a]'(by simp [ha]) =
              (R.map Prod.fst)[b + 1]'(by simp [hb1]) := by
            simp only [List.getElem_map]
            exact hq_neigh.symm.trans hnext_b
          exact Fin.val_eq_of_eq (@hinj ⟨a, by simp [ha]⟩ ⟨b + 1, by simp [hb1]⟩ heq_fst)
        have hnext_a := hstep_walk a ha
        split_ifs at hnext_a with ha1
        · have hba1 : b = a + 1 := by
            have heq_fst : (R.map Prod.fst)[b]'(by simp [hb]) =
                (R.map Prod.fst)[a + 1]'(by simp [ha1]) := by
              simp only [List.getElem_map]
              exact hp_neigh.symm.trans hnext_a
            exact Fin.val_eq_of_eq (@hinj ⟨b, by simp [hb]⟩ ⟨a + 1, by simp [ha1]⟩ heq_fst)
          omega
        · have hzb : (R[b]).1 = z := hp_neigh.symm.trans hnext_a
          exact hR_not_C (R[b]) (List.getElem_mem hb) (hzb ▸ hzC)
      · have hza : (R[a]).1 = z := hq_neigh.symm.trans hnext_b
        exact hR_not_C (R[a]) (List.getElem_mem ha) (hza ▸ hzC)
    -- Cardinality bound `#S_u ≤ 2 * N - 1`.
    let S_u : Finset (V × D) := R.toFinset ∪ (R.map G.rot).toFinset ∪ L₀.toFinset
    have hRC_card : R.length + L₀.length ≤ Fintype.card V := by
      let Rfst : Finset V := (R.map Prod.fst).toFinset
      have hRfst_card : #Rfst = R.length := by
        dsimp only [Rfst]
        rw [List.card_toFinset, hR_fst_nd.dedup, List.length_map]
      have hdisj_V : Disjoint Rfst C := by
        rw [Finset.disjoint_left]
        intro v hvR hvC
        obtain ⟨p, hpR, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hvR)
        exact hR_not_C p hpR hvC
      have hunion_le : #(Rfst ∪ C) ≤ Fintype.card V := card_le_univ _
      rw [card_union_of_disjoint hdisj_V, hRfst_card, hC_card] at hunion_le
      exact hunion_le
    have hSu_card : (#S_u : ℝ) ≤ 2 * N - 1 := by
      have h1 : #S_u ≤ #R.toFinset + #(R.map G.rot).toFinset + #L₀.toFinset :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      have h2 : #R.toFinset = R.length := by rw [List.card_toFinset, hR_nd.dedup]
      have h3 : #(R.map G.rot).toFinset = R.length := by
        rw [List.card_toFinset, hRrot_nd.dedup, List.length_map]
      have h4 : #L₀.toFinset = L₀.length := by rw [List.card_toFinset, hL₀_dart_nd.dedup]
      have hnat : #S_u ≤ 2 * Fintype.card V - 1 := by omega
      have hcast : (#S_u : ℝ) ≤ (2 * Fintype.card V - 1 : ℕ) := by exact_mod_cast hnat
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * Fintype.card V), Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one] at hcast
      exact hcast
    -- Triangle inequality `2 * |f u| ≤ ∑ p ∈ S_u, |f p.1 + f (G.neighbor p.1 p.2)|`.
    let g : V × D → ℝ := fun p ↦ |f p.1 + f (G.neighbor p.1 p.2)|
    have hg_rot (q : V × D) : g (G.rot q) = g q := by
      rcases q with ⟨qv, qi⟩
      dsimp only [g]
      have h2 : G.neighbor (G.rot (qv, qi)).1 (G.rot (qv, qi)).2 = qv :=
        G.neighbor_neighbor_rot qv qi
      rw [h2, show (G.rot (qv, qi)).1 = G.neighbor qv qi from rfl, add_comm]
    have hR_sum : (R.map g).sum = ∑ p ∈ R.toFinset, g p := (List.sum_toFinset g hR_nd).symm
    have hRrot_sum : (R.map g).sum = ∑ p ∈ (R.map G.rot).toFinset, g p := by
      rw [List.sum_toFinset g hRrot_nd, List.map_map]
      congr 1
      exact List.map_congr_left fun q _ ↦ (hg_rot q).symm
    have h2fu : 2 * |f u| ≤ ∑ p ∈ S_u, g p := by
      have htri : |f u| ≤ |f u - (-1 : ℝ) ^ R.length * f z| + |(-1 : ℝ) ^ R.length * f z| := by
        simpa using abs_add_le (f u - (-1 : ℝ) ^ R.length * f z) ((-1 : ℝ) ^ R.length * f z)
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at htri
      have hR_alt := hR.abs_alt_le f
      have hz_alt := hcycle_bound z hzC
      have hunion_sum :
          ∑ p ∈ S_u, g p =
            ∑ p ∈ R.toFinset, g p + ∑ p ∈ (R.map G.rot).toFinset, g p + ∑ p ∈ L₀.toFinset, g p := by
        dsimp only [S_u]
        rw [sum_union (Finset.disjoint_union_left.mpr ⟨hdisj_RL₀, hdisj_RrotL₀⟩),
          sum_union hdisj_RRrot]
      rw [hunion_sum, ← hR_sum, ← hRrot_sum]
      linarith
    have hsq1 : 4 * f u ^ 2 ≤ (∑ p ∈ S_u, g p) ^ 2 := by
      have : 4 * f u ^ 2 = (2 * |f u|) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
      rw [this]
      exact pow_le_pow_left₀ (by positivity) h2fu 2
    have hcs : (∑ p ∈ S_u, g p) ^ 2 ≤
      (#S_u : ℝ) * ∑ p ∈ S_u, (f p.1 + f (G.neighbor p.1 p.2)) ^ 2 := by
      simpa only [g, sq_abs] using sq_sum_le_card_mul_sum_sq_real S_u g
    have hsub : ∑ p ∈ S_u, (f p.1 + f (G.neighbor p.1 p.2)) ^ 2 ≤ Eplus :=
      sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    calc 4 * f u ^ 2 ≤ (#S_u : ℝ) * ∑ p ∈ S_u, (f p.1 + f (G.neighbor p.1 p.2)) ^ 2 :=
          hsq1.trans hcs
      _ ≤ (2 * N - 1) * Eplus :=
          mul_le_mul hSu_card hsub (sum_nonneg fun _ _ ↦ sq_nonneg _) (by linarith)
  -- Average over `u : V`.
  have havg : 4 * 𝔼 u, f u ^ 2 ≤ (2 * N - 1) * Eplus := by
    have : 4 * 𝔼 u, f u ^ 2 = 𝔼 u, (4 * f u ^ 2) := mul_expect univ (fun u ↦ f u ^ 2) 4
    rw [this]
    exact (expect_le_expect fun u _ ↦ hvertex_bound u).trans_eq (Fintype.expect_const _)
  have h2N : (2 * N - 1) * Eplus ≤ 2 * N * Eplus :=
    mul_le_mul_of_nonneg_right (by linarith) hEp_nn
  have hstep : 4 * 𝔼 u, f u ^ 2 ≤ 2 * N * (2 * d * N * (𝔼 v, f v ^ 2 + 𝔼 v, f v * G.walk f v)) := by
    rw [← hEp_eq]; exact havg.trans h2N
  have hpos : 0 < d * N ^ 2 := by positivity
  have hdiv : (1 / (d * N ^ 2)) * 𝔼 v, f v ^ 2 ≤ 𝔼 v, f v ^ 2 + 𝔼 v, f v * G.walk f v := by
    rw [one_div_mul_eq_div, div_le_iff₀ hpos]
    nlinarith
  linarith

/-- **Alon–Sudakov Non-Bipartite Spectral Gap Theorem**: for every finite connected non-bipartite
`D`-regular multigraph `G` on `V`,
`G.spectralExpansion ≤ 1 - 1 / (|D| * |V| ^ 2)`. -/
theorem spectralExpansion_le_one_sub_of_not_isBipartite (G : Cslib.RotationMap V D)
    (hconn : G.toSimpleGraph.Preconnected) (hnb : ¬ IsBipartite G) :
    G.spectralExpansion ≤ 1 - 1 / ((Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2) := by
  have : Nonempty V := nonempty_vertices_of_not_isBipartite hnb
  have : Nonempty D := nonempty_labels_of_not_isBipartite hnb
  have hc : 0 ≤ 1 - 1 / ((Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) ≤ (Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr Fintype.card_pos)
        (one_le_pow₀ (Nat.one_le_cast.mpr Fintype.card_pos))
    rw [sub_nonneg, div_le_one (by positivity)]
    exact h1
  refine G.spectralExpansion_le_of_abs_expect_mul_walk_le hc fun f hf ↦ ?_
  rw [abs_le]
  exact ⟨by linarith [neg_expect_mul_walk_le_of_not_isBipartite G hconn hnb f],
    expect_mul_walk_le_of_preconnected G hconn hf⟩

/-- Equivalent spectral-gap form of the Alon–Sudakov theorem:
`1 / (|D| * |V| ^ 2) ≤ 1 - G.spectralExpansion`. -/
theorem le_one_sub_spectralExpansion_of_not_isBipartite (G : Cslib.RotationMap V D)
    (hconn : G.toSimpleGraph.Preconnected) (hnb : ¬ IsBipartite G) :
    1 / ((Fintype.card D : ℝ) * (Fintype.card V : ℝ) ^ 2) ≤ 1 - G.spectralExpansion := by
  linarith [spectralExpansion_le_one_sub_of_not_isBipartite G hconn hnb]

end NonbipartiteLowerBound

/-! ### 5. Non-Degenerate Sanity and Sharpness Examples -/

/-- Bipartite `K_2` shows that `¬ IsBipartite G` cannot be omitted (`spectralExpansion = 1`). -/
private example :
    let K2 : Cslib.RotationMap (Fin 2) Unit :=
      Cslib.RotationMap.ofInvolutive (fun x : Fin 2 ↦ x + 1) (fun x ↦ by fin_cases x <;> decide)
    IsBipartite K2 ∧ K2.toSimpleGraph.Preconnected := by
  refine ⟨⟨fun x ↦ x == 1, fun v u ↦ by fin_cases v <;> cases u <;> decide⟩, ?_⟩
  intro u v
  fin_cases u <;> fin_cases v
  · exact .refl _
  · exact SimpleGraph.Adj.reachable (Cslib.RotationMap.toSimpleGraph_adj _ |>.mpr ⟨by decide, (),
    rfl⟩)
  · exact SimpleGraph.Adj.reachable (Cslib.RotationMap.toSimpleGraph_adj _ |>.mpr ⟨by decide, (),
    rfl⟩)
  · exact .refl _

end CslibFrontier.RotationMap
