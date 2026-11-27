/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.Kernelization
public import CslibFrontier.Computability.Complexity.Classes.Inclusions
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.EncLen

/-!
# Kernel-to-`FPT` Transfer for `NP` / `EXP` Problems and Polynomial-Time Induced Graph Reachability

This module provides two general parameterized/computational complexity building blocks on top of
`CslibFrontier`:

1. **`EXP` and `NP` Kernel-to-`FPT` Transfer**
: `Cslib.Complexity.IsKernelization.mem_FPT` and
   `Cslib.Complexity.HasKernel.mem_FPT` require a concrete `DTIME enc t` witness `t`. Combining
   `Cslib.Complexity.mem_EXP_iff` and `Cslib.Complexity.NP_subset_EXP` discharges this decidability
   premise automatically for every problem in `EXP enc` or `NP enc`, giving direct transfer theorems
   `isKernelization_mem_FPT_of_mem_EXP`, `isKernelization_mem_FPT_of_mem_NP`,
   `hasKernel_mem_FPT_of_mem_NP`, `hasPolyKernel_mem_FPT_of_mem_NP`, and the characterizations
   `mem_FPT_iff_hasKernel_of_mem_EXP` and `mem_FPT_iff_hasKernel_of_mem_NP`.
2. **Polynomial-Time Induced Graph Reachability on `Cslib.Complexity.Graph`**: `reachIn G S u`
   computes in multi-tape Turing-machine polynomial time (`computableInPolyTime_reachIn`) the exact
   sublist of vertices in `S : List ℕ` reachable from `u : ℕ` inside the induced subgraph
   `G.toSimpleGraph.induce {w : ℕ | w ∈ S}` (`mem_reachIn_iff`).

## Main definitions

* `CslibFrontier.Complexity.encReachInInput`: canonical pair encoding for `(G, S, u)`.
* `CslibFrontier.Complexity.reachIn`: vertices of `S` reachable from `u` in `G[S]`.

## Main results

* `CslibFrontier.Complexity.isKernelization_mem_FPT_of_mem_EXP`,
  `CslibFrontier.Complexity.isKernelization_mem_FPT_of_mem_NP`,
  `CslibFrontier.Complexity.hasKernel_mem_FPT_of_mem_NP`,
  `CslibFrontier.Complexity.hasPolyKernel_mem_FPT_of_mem_NP`.
* `CslibFrontier.Complexity.mem_FPT_iff_hasKernel_of_mem_EXP`,
  `CslibFrontier.Complexity.mem_FPT_iff_hasKernel_of_mem_NP`.
* `CslibFrontier.Complexity.computableInPolyTime_reachIn`,
  `CslibFrontier.Complexity.mem_reachIn_iff`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity SimpleGraph Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-! ### 1. Kernel-to-`FPT` Transfer for `EXP` and `NP` Languages -/

section KernelTransfer

variable {α : Type} {enc : α ↪ List Bool} {κ : α → ℕ} {A : Set α}

/-- Every problem in `EXP enc` admitting a kernelization is fixed-parameter tractable. -/
theorem isKernelization_mem_FPT_of_mem_EXP {K : α → α} {g : ℕ → ℕ}
    (hK : IsKernelization enc κ A K g) (hA : A ∈ EXP enc) : A ∈ FPT enc κ := by
  obtain ⟨k, hdt⟩ := mem_EXP_iff.mp hA
  exact hK.mem_FPT hdt

/-- Every problem in `EXP enc` that has a kernel is fixed-parameter tractable. -/
theorem hasKernel_mem_FPT_of_mem_EXP (h : HasKernel enc κ A) (hA : A ∈ EXP enc) :
    A ∈ FPT enc κ := by
  obtain ⟨K, g, hK⟩ := h
  exact isKernelization_mem_FPT_of_mem_EXP hK hA

/-- Every problem in `NP enc` admitting a kernelization is fixed-parameter tractable
.
-/
theorem isKernelization_mem_FPT_of_mem_NP {K : α → α} {g : ℕ → ℕ}
    (hK : IsKernelization enc κ A K g) (hA : A ∈ NP enc) : A ∈ FPT enc κ :=
  isKernelization_mem_FPT_of_mem_EXP hK (NP_subset_EXP hA)

/-- Every problem in `NP enc` that has a kernel is fixed-parameter tractable. -/
theorem hasKernel_mem_FPT_of_mem_NP (h : HasKernel enc κ A) (hA : A ∈ NP enc) :
    A ∈ FPT enc κ :=
  hasKernel_mem_FPT_of_mem_EXP h (NP_subset_EXP hA)

/-- Every problem in `NP enc` with a polynomial kernel is fixed-parameter tractable. -/
theorem hasPolyKernel_mem_FPT_of_mem_NP (h : HasPolyKernel enc κ A) (hA : A ∈ NP enc) :
    A ∈ FPT enc κ :=
  hasKernel_mem_FPT_of_mem_NP h.hasKernel hA

/-- Over a nonempty instance type, a problem in `EXP enc` belongs to `FPT enc κ` if and only if it
has a kernel. -/
theorem mem_FPT_iff_hasKernel_of_mem_EXP [Nonempty α] (hA : A ∈ EXP enc) :
    A ∈ FPT enc κ ↔ HasKernel enc κ A :=
  ⟨hasKernel_of_mem_FPT, fun h ↦ hasKernel_mem_FPT_of_mem_EXP h hA⟩

/-- Over a nonempty instance type, a problem in `NP enc` belongs to `FPT enc κ` if and only if it
has a kernel.
-/
theorem mem_FPT_iff_hasKernel_of_mem_NP [Nonempty α] (hA : A ∈ NP enc) :
    A ∈ FPT enc κ ↔ HasKernel enc κ A :=
  mem_FPT_iff_hasKernel_of_mem_EXP (NP_subset_EXP hA)

end KernelTransfer

/-! ### 2. Polynomial-Time Induced Graph Reachability on `Cslib.Complexity.Graph` -/

section InducedReachability

/-- Pair encoding `((G, S), u)` for induced graph reachability queries on `Cslib.Complexity.Graph`
with vertex subset `S : List ℕ` (binary-encoded naturals) and source vertex `u : ℕ` (binary). -/
abbrev encReachInInput : ((Graph × List ℕ) × ℕ) ↪ List Bool :=
  encPair (encPair encGraph (encList encNat)) encNat

private def memNatBool (l : List ℕ) (x : ℕ) : Bool :=
  l.any fun y ↦ decide (y = x)

@[fun_prop]
private theorem computableInPolyTime_memNatBool {γ : Type} {enc : γ ↪ List Bool}
    {l : γ → List ℕ} {x : γ → ℕ}
    (hl : ComputableInPolyTime l enc (encList encNat))
    (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun c ↦ memNatBool (l c) (x c)) enc encBool := by
  have h0 : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ memNatBool p.1 p.2)
      (encPair (encList encNat) encNat) encBool := by
    unfold memNatBool; fun_prop
  exact h0.comp (hl.prod hx)

private theorem memNatBool_eq_true_iff {l : List ℕ} {x : ℕ} :
    memNatBool l x = true ↔ x ∈ l := by
  simp only [memNatBool, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨y, hy, heq⟩ ↦ heq ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩

private theorem sublist_length_encList_le {α : Type} (enc : α ↪ List Bool) {l₁ l₂ : List α}
    (h : l₁.Sublist l₂) : (encList enc l₁).length ≤ (encList enc l₂).length := by
  induction h with
  | slnil => exact le_rfl
  | cons _ _ ih =>
    simp only [encList_cons, List.length_append]; omega
  | cons_cons _ _ ih =>
    simp only [encList_cons, List.length_append]; omega

/-- Single breadth-first relaxation step inside `S : List ℕ` on `G : Cslib.Complexity.Graph`. -/
def reachStep (G : Graph) (S vis : List ℕ) : List ℕ :=
  S.filter fun v ↦ memNatBool vis v || vis.any (G.adjBool · v)

/-- Sublist of `S : List ℕ` consisting of all vertices reachable from `u : ℕ` inside the induced
subgraph `G.toSimpleGraph.induce {w : ℕ | w ∈ S}` (empty when `u ∉ S`). -/
def reachIn (G : Graph) (S : List ℕ) (u : ℕ) : List ℕ :=
  (reachStep G S)^[S.length] (S.filter fun v ↦ decide (v = u))

/-- `reachIn G S u` is always a sublist of `S`. -/
theorem reachIn_sublist (G : Graph) (S : List ℕ) (u : ℕ) :
    (reachIn G S u).Sublist S := by
  unfold reachIn
  generalize S.length = m
  cases m with
  | zero => exact List.filter_sublist
  | succ m =>
    rw [Function.iterate_succ_apply']
    exact List.filter_sublist

/-- Multi-tape Turing-machine polynomial-time computability of `reachIn`. -/
@[fun_prop]
theorem computableInPolyTime_reachIn :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ ↦ reachIn p.1.1 p.1.2 p.2)
      encReachInInput (encList encNat) := by
  have hsub_iter : ∀ (G : Graph) (S : List ℕ) (u i : ℕ),
      ((reachStep G S)^[i] (S.filter fun v ↦ decide (v = u))).Sublist S := by
    intro G S u i; cases i with
    | zero => exact List.filter_sublist
    | succ i => rw [Function.iterate_succ_apply']; exact List.filter_sublist
  exact iterateWith
    (encPar := encPair encGraph (encList encNat))
    (par := fun p : (Graph × List ℕ) × ℕ ↦ p.1)
    (count := fun p ↦ p.1.2.length)
    (init := fun p ↦ p.1.2.filter fun v ↦ decide (v = p.2))
    (step := fun q vis ↦ reachStep q.1 q.2 vis)
    (by dsimp only [encReachInInput]; fun_prop)
    (by dsimp only [encReachInInput]; fun_prop)
    (by dsimp only [encReachInInput]; fun_prop)
    (by unfold reachStep; fun_prop)
    (bound := fun p ↦ (encReachInInput p).length)
    PolyBounded.self
    (fun p i _ ↦ (sublist_length_encList_le encNat (hsub_iter p.1.1 p.1.2 p.2 i)).trans
      (by dsimp only [encReachInInput]; enc_len))

/-- Soundness and completeness of `reachIn`: when `u ∈ S`, `v ∈ reachIn G S u` holds if and only if
`v ∈ S` and `v` is reachable from `u` in `G.toSimpleGraph.induce {w : ℕ | w ∈ S}`. -/
theorem mem_reachIn_iff {G : Graph} {S : List ℕ} {u v : ℕ} (hu : u ∈ S) :
    v ∈ reachIn G S u ↔
      ∃ hv : v ∈ S,
        (G.toSimpleGraph.induce {w : ℕ | w ∈ S}).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  let GS := G.toSimpleGraph.induce {w : ℕ | w ∈ S}
  let initL := S.filter fun w ↦ decide (w = u)
  have hmono_step : ∀ vis : List ℕ, (∀ x ∈ vis, x ∈ S) →
      ∀ x ∈ vis, x ∈ reachStep G S vis := fun vis hsub x hx ↦
    List.mem_filter.mpr ⟨hsub x hx, by simp [memNatBool_eq_true_iff.mpr hx]⟩
  have hsub_iter : ∀ i : ℕ, ∀ x ∈ (reachStep G S)^[i] initL, x ∈ S := by
    intro i; cases i with
    | zero => intro x hx; exact (List.mem_filter.mp hx).1
    | succ i =>
      rw [Function.iterate_succ_apply']
      intro x hx; exact (List.mem_filter.mp hx).1
  have hmono_le : ∀ {i j : ℕ}, i ≤ j →
      ∀ x ∈ (reachStep G S)^[i] initL, x ∈ (reachStep G S)^[j] initL := by
    intro i j hij
    induction hij with
    | refl => intro x hx; exact hx
    | @step m _ ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hmono_step _ (hsub_iter m) x (ih x hx)
  have hsound : ∀ i : ℕ, ∀ x ∈ (reachStep G S)^[i] initL,
      ∃ hx : x ∈ S, GS.Reachable ⟨u, hu⟩ ⟨x, hx⟩ := by
    intro i; induction i with
    | zero =>
      intro x hx
      obtain ⟨hxS, hxu⟩ := List.mem_filter.mp hx
      have hxu' : x = u := of_decide_eq_true hxu
      subst hxu'; exact ⟨hu, .rfl⟩
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      obtain ⟨hxS, hcond⟩ := List.mem_filter.mp hx
      simp only [Bool.or_eq_true, memNatBool_eq_true_iff, List.any_eq_true,
        Graph.adjBool_eq_true_iff] at hcond
      rcases hcond with hmem | ⟨y, hy, hadj⟩
      · exact ih x hmem
      · obtain ⟨hyS, hruy⟩ := ih y hy
        exact ⟨hxS, hruy.trans (Adj.reachable (show GS.Adj ⟨y, hyS⟩ ⟨x, hxS⟩ from hadj))⟩
  refine ⟨hsound S.length v, fun ⟨hv, hr⟩ ↦ ?_⟩
  obtain ⟨w₀⟩ := hr
  let p := w₀.toPath.val
  have hp_path : p.IsPath := w₀.toPath.property
  have hlen_le : p.length ≤ S.length := by
    have hnd_val : (p.support.map Subtype.val).Nodup :=
      hp_path.support_nodup.map Subtype.val_injective
    have hsub_S : ∀ z ∈ p.support.map Subtype.val, z ∈ S := by
      intro z hz; obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz; exact z'.2
    have hcard := List.Nodup.length_le_of_subset hnd_val hsub_S
    rw [List.length_map, Walk.length_support] at hcard
    omega
  have hwalk_in : ∀ j ≤ p.length, (p.getVert j).1 ∈ (reachStep G S)^[j] initL := by
    intro j; induction j with
    | zero =>
      intro _; simp only [Walk.getVert_zero, Function.iterate_zero, id_eq]
      exact List.mem_filter.mpr ⟨hu, decide_eq_true rfl⟩
    | succ j ih =>
      intro hj
      have hj_prev := ih (Nat.le_of_succ_le hj)
      have hadj : GS.Adj (p.getVert j) (p.getVert (j + 1)) := p.adj_getVert_succ (by omega)
      rw [Function.iterate_succ_apply']
      refine List.mem_filter.mpr ⟨(p.getVert (j + 1)).2, ?_⟩
      simp only [Bool.or_eq_true, memNatBool_eq_true_iff, List.any_eq_true,
        Graph.adjBool_eq_true_iff]
      exact .inr ⟨(p.getVert j).1, hj_prev, hadj⟩
  have hend : (p.getVert p.length).1 = v := congrArg Subtype.val p.getVert_length
  have h0 := hwalk_in p.length le_rfl
  rw [hend] at h0
  exact hmono_le hlen_le v h0

end InducedReachability

end CslibFrontier.Complexity
