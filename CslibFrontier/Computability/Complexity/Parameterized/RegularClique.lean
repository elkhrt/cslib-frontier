/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.Clique.OfAdj
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `RegularClique` is `NP`-Hard and `W[1]`-Hard

Formalizes the polynomial-time and `FPT` degree-regularization reduction from
`Cslib.Complexity.Clique` to `Cslib.Complexity.RegularClique` (`Clique` restricted to regular
induced graphs).

Given `x : CliqueInstance` with `n = x.graph.distinctVertices.length` and capped unary parameter
`m' = min (n + 1) x.m`, we first join the induced graph on `Fin n` with $K_3$ (`joinK3Graph`,
raising the clique target to `x.m + 3 ≥ 3` so triangles cannot use bipartite deficiency gadgets)
and then embed two disjoint copies of the $K_3$-joined graph into a $D$-regular graph `regGraph`
of degree `D = max (n + 3) (m' + 4)` using $K_{D, D} - M_v$ gadgets.

## Main definitions

* `Cslib.Complexity.RegularClique`: `Clique` restricted to regular induced graphs.
* `Cslib.Complexity.cliqueToRegularClique`: polynomial-time and `FPT` reduction on
  `CliqueInstance`.

## Main results

* `Cslib.Complexity.cliqueToRegularClique_isRegular`: output graphs are regular.
* `Cslib.Complexity.cliqueToRegularClique_mem_iff`: exact clique membership equivalence.
* `Cslib.Complexity.computableInPolyTime_cliqueToRegularClique`: the reduction is polynomial-time.
* `Cslib.Complexity.polyTimeReducible_Clique_RegularClique`,
  `Cslib.Complexity.fptReducible_Clique_RegularClique`: polynomial-time and `FPT` reductions.
* `Cslib.Complexity.RegularClique_npHard`: `NPHard encCliqueInstance RegularClique`.
* `Cslib.Complexity.RegularClique_wHard`: `WHard 1 encCliqueInstance (·.m) RegularClique`.
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

/-! ### `RegularClique` and `Fin`-indexed graph pullback -/

/-- **Regular Clique**: instances `x : CliqueInstance` that belong to `Clique` and whose induced
graph `x.graph.induced` is `d`-regular for some degree `d`. -/
def RegularClique : Set CliqueInstance :=
  {x | x ∈ Clique ∧ ∃ d : ℕ, x.graph.induced.IsRegularOfDegree d}

private def graphFin (G : Graph) : SimpleGraph (Fin G.distinctVertices.length) :=
  G.induced.comap G.vertexEquiv.toEmbedding

private def graphFinIso (G : Graph) : graphFin G ≃g G.induced where
  toEquiv := G.vertexEquiv
  map_rel_iff' := Iff.rfl

private theorem graphFin_adj_iff_adjBool (G : Graph) (i j : Fin G.distinctVertices.length) :
    (graphFin G).Adj i j ↔
      G.adjBool (G.distinctVertices.getD i.1 0) (G.distinctVertices.getD j.1 0) = true := by
  rw [graphFin, SimpleGraph.comap_adj, Equiv.coe_toEmbedding, Graph.induced_adj,
    ← Graph.adjBool_eq_true_iff, G.vertexEquiv_apply, G.vertexEquiv_apply]

private theorem exists_isNClique_graphFin_iff (x : CliqueInstance) :
    (∃ s : Finset (Fin x.graph.distinctVertices.length), (graphFin x.graph).IsNClique x.m s) ↔
      x ∈ Clique := by
  let iso := graphFinIso x.graph
  simp only [Clique, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s.map iso.toEquiv.toEmbedding, ?_, by rw [Finset.card_map, hcard]⟩
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    exact iso.map_rel_iff.mpr (hs hi hj fun h ↦ hab (congrArg iso.toEquiv h))
  · rintro ⟨S, hS, hcard⟩
    refine ⟨S.map iso.symm.toEquiv.toEmbedding, ?_, by rw [Finset.card_map, hcard]⟩
    intro i hi j hj hij
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hj
    exact iso.symm.map_rel_iff.mpr (hS ha hb fun h ↦ hij (congrArg iso.symm.toEquiv h))

/-! ### `K₃`-join and `K_{D, D} - M_v` degree regularization on `Fin` -/

section Regularization

private def joinK3Adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin (n + 3)) : Prop :=
  u ≠ v ∧ (n ≤ u.1 ∨ n ≤ v.1 ∨ ∃ (hu : u.1 < n) (hv : v.1 < n), G.Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩)

private def joinK3Graph (n : ℕ) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 3)) where
  Adj := joinK3Adj G
  symm := ⟨fun _ _ ⟨hne, h⟩ ↦ ⟨hne.symm, by
    rcases h with h1 | h2 | ⟨hu, hv, hadj⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2
    · exact Or.inr (Or.inr ⟨hv, hu, hadj.symm⟩)⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ ↦ hne rfl⟩

private theorem joinK3Graph_mem_iff (n l : ℕ) (G : SimpleGraph (Fin n)) :
    (∃ s : Finset (Fin n), G.IsNClique l s) ↔
      ∃ t : Finset (Fin (n + 3)), (joinK3Graph n G).IsNClique (l + 3) t := by
  classical
  let emb : Fin n ↪ Fin (n + 3) := ⟨fun v ↦ ⟨v.1, by omega⟩, fun a b h ↦ Fin.ext (Fin.mk.inj h)⟩
  let tri : Finset (Fin (n + 3)) := {⟨n, by omega⟩, ⟨n + 1, by omega⟩, ⟨n + 2, by omega⟩}
  have htri_card : tri.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]
  constructor
  · rintro ⟨s, hsc, hscard⟩
    have hdisj : Disjoint (s.map emb) tri := Finset.disjoint_left.mpr fun x hx hxt ↦ by
      rcases Finset.mem_map.mp hx with ⟨v, _, rfl⟩
      simp only [tri, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hxt
      change v.1 = n ∨ v.1 = n + 1 ∨ v.1 = n + 2 at hxt
      have hv := v.2; omega
    refine ⟨s.map emb ∪ tri, ?_, ?_⟩
    · intro x hx y hy hne
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
        exact ⟨hne, Or.inr (Or.inr ⟨a.2, b.2, hsc ha hb fun h ↦ hne (congrArg emb h)⟩)⟩
      · simp only [tri, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hy
        exact ⟨hne, Or.inr (Or.inl (by omega))⟩
      · simp only [tri, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx
        exact ⟨hne, Or.inl (by omega)⟩
      · simp only [tri, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx
        exact ⟨hne, Or.inl (by omega)⟩
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, hscard, htri_card]
  · rintro ⟨t, htc, htcard⟩
    let t0 : Finset (Fin (n + 3)) := t.filter fun x ↦ x.1 < n
    let t1 : Finset (Fin (n + 3)) := t.filter fun x ↦ n ≤ x.1
    have ht1_sub : t1 ⊆ tri := fun x hx ↦ by
      have hx' := (Finset.mem_filter.mp hx).2; have hlt := x.2
      simp only [tri, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega
    have ht1_card : t1.card ≤ 3 := (Finset.card_le_card ht1_sub).trans htri_card.le
    have ht_split : t0.card + t1.card = t.card := by
      simpa [t0, t1, not_lt] using
        Finset.card_filter_add_card_filter_not (s := t) (p := fun x : Fin (n + 3) ↦ x.1 < n)
    obtain ⟨s', hs'sub, hs'card⟩ := Finset.exists_subset_card_eq (show l ≤ t0.card by omega)
    let s : Finset (Fin n) := Finset.univ.filter fun v ↦ emb v ∈ s'
    have himg : s.map emb = s' := by
      ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, s]
      exact ⟨fun ⟨_, hv, heq⟩ ↦ heq ▸ hv, fun hx ↦
        ⟨⟨x.1, (Finset.mem_filter.mp (hs'sub hx)).2⟩, hx, Fin.ext rfl⟩⟩
    refine ⟨s, ?_, by rw [← Finset.card_map emb, himg, hs'card]⟩
    intro a ha b hb hab
    have ha' := hs'sub (by simpa [s] using ha)
    have hb' := hs'sub (by simpa [s] using hb)
    rcases (htc (Finset.mem_filter.mp ha').1 (Finset.mem_filter.mp hb').1
      (emb.injective.ne hab)).2 with h1 | h2 | ⟨_, _, hadjG⟩
    · have := a.2; change n ≤ a.1 at h1; omega
    · have := b.2; change n ≤ b.1 at h2; omega
    · exact hadjG

private noncomputable def regDeficiency (n₁ D : ℕ) (G₁ : SimpleGraph (Fin n₁)) (v : Fin n₁) : ℕ :=
  let _ := Classical.decRel G₁.Adj
  D - G₁.degree v

private theorem regDeficiency_pos {n₁ D : ℕ} (hD : n₁ ≤ D) (G₁ : SimpleGraph (Fin n₁))
    (v : Fin n₁) : 1 ≤ regDeficiency n₁ D G₁ v ∧ regDeficiency n₁ D G₁ v ≤ D := by
  classical
  have hdeg : G₁.degree v < n₁ := G₁.degree_lt_card_verts v |>.trans_eq (Fintype.card_fin n₁)
  simp only [regDeficiency]; omega

private def regAdj (n₁ D : ℕ) (G₁ : SimpleGraph (Fin n₁))
    (u v : Fin (2 * n₁ + 2 * n₁ * D)) : Prop :=
  let _ := Classical.decRel G₁.Adj
  u ≠ v ∧
  ( (∃ (hu : u.1 < n₁) (hv : v.1 < n₁), G₁.Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩) ∨
    (∃ (hu1 : n₁ ≤ u.1) (hu2 : u.1 < 2 * n₁) (hv1 : n₁ ≤ v.1) (hv2 : v.1 < 2 * n₁),
      G₁.Adj ⟨u.1 - n₁, by omega⟩ ⟨v.1 - n₁, by omega⟩) ∨
    (2 * n₁ ≤ u.1 ∧ 2 * n₁ ≤ v.1 ∧
      let bu := (u.1 - 2 * n₁) / D
      let bv := (v.1 - 2 * n₁) / D
      let ju := (u.1 - 2 * n₁) % D
      let jv := (v.1 - 2 * n₁) % D
      bu / 2 = bv / 2 ∧ bu % 2 ≠ bv % 2 ∧
      ¬ (ju = jv ∧ ∃ (hbu : bu / 2 < n₁), ju < regDeficiency n₁ D G₁ ⟨bu / 2, hbu⟩)) ∨
    (∃ (hu : u.1 < n₁), 2 * n₁ ≤ v.1 ∧
      (v.1 - 2 * n₁) / D = 2 * u.1 ∧ (v.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨u.1, hu⟩) ∨
    (2 * n₁ ≤ u.1 ∧ ∃ (hv : v.1 < n₁),
      (u.1 - 2 * n₁) / D = 2 * v.1 ∧ (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨v.1, hv⟩) ∨
    (∃ (hu1 : n₁ ≤ u.1) (hu2 : u.1 < 2 * n₁), 2 * n₁ ≤ v.1 ∧
      (v.1 - 2 * n₁) / D = 2 * (u.1 - n₁) + 1 ∧
      (v.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨u.1 - n₁, by omega⟩) ∨
    (2 * n₁ ≤ u.1 ∧ ∃ (hv1 : n₁ ≤ v.1) (hv2 : v.1 < 2 * n₁),
      (u.1 - 2 * n₁) / D = 2 * (v.1 - n₁) + 1 ∧
      (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨v.1 - n₁, by omega⟩) )

private theorem regAdj_symm (n₁ D : ℕ) (G₁ : SimpleGraph (Fin n₁)) :
    Std.Symm (regAdj n₁ D G₁) := by
  refine ⟨fun u v ⟨hne, h⟩ ↦ ⟨hne.symm, ?_⟩⟩
  rcases h with ⟨hu, hv, h1⟩ | ⟨hu1, hu2, hv1, hv2, h2⟩ | h3 |
      ⟨hu, hv, hbv, hlt⟩ | ⟨hu, hv, hbu, hlt⟩ | ⟨hu1, hu2, hv, hbv, hlt⟩ |
      ⟨hu, hv1, hv2, hbu, hlt⟩
  · exact Or.inl ⟨hv, hu, h1.symm⟩
  · exact Or.inr (Or.inl ⟨hv1, hv2, hu1, hu2, h2.symm⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨h3.2.1, h3.1, h3.2.2.1.symm, h3.2.2.2.1.symm, ?_⟩))
    intro ⟨hj, hbv, hlt⟩
    apply h3.2.2.2.2
    have hbu : (u.1 - 2 * n₁) / D / 2 < n₁ := h3.2.2.1 ▸ hbv
    refine ⟨hj.symm, hbu, ?_⟩
    have heq : (⟨(u.1 - 2 * n₁) / D / 2, hbu⟩ : Fin n₁) = ⟨(v.1 - 2 * n₁) / D / 2, hbv⟩ :=
      Fin.ext h3.2.2.1
    change (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨(u.1 - 2 * n₁) / D / 2, hbu⟩
    rw [heq]; convert hlt using 1; exact hj.symm
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu, hbv, hlt⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu, hbu, hlt⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, hu1, hu2, hbv, hlt⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv1, hv2, hu, hbu, hlt⟩)))))

private def regGraph (n₁ D : ℕ) (G₁ : SimpleGraph (Fin n₁)) :
    SimpleGraph (Fin (2 * n₁ + 2 * n₁ * D)) where
  Adj := regAdj n₁ D G₁
  symm := regAdj_symm n₁ D G₁
  loopless := ⟨fun _ ⟨hne, _⟩ ↦ hne rfl⟩

private theorem regGraph_degree_eq (n₁ D : ℕ) (hD : n₁ ≤ D) (hDpos : 0 < D)
    (G₁ : SimpleGraph (Fin n₁)) :
    let _ := Classical.decRel (regGraph n₁ D G₁).Adj
    (regGraph n₁ D G₁).IsRegularOfDegree D := by
  classical
  have hdef := regDeficiency_pos hD G₁
  intro instDec u
  have hdeg_eq : (let _ := instDec; (regGraph n₁ D G₁).degree u) =
      (Finset.univ.filter (fun w ↦ regAdj n₁ D G₁ u w)).card := by
    let _ := instDec
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]; rfl
  change (let _ := instDec; (regGraph n₁ D G₁).degree u) = D
  rw [hdeg_eq]
  set ns := Finset.univ.filter (fun w ↦ regAdj n₁ D G₁ u w)
  have hmem_ns : ∀ w, w ∈ ns ↔ regAdj n₁ D G₁ u w := fun w ↦ by simp [ns]
  by_cases hu0 : u.1 < n₁
  · let u' : Fin n₁ := ⟨u.1, hu0⟩
    let f1 : Fin n₁ → Fin (2 * n₁ + 2 * n₁ * D) := fun w ↦ ⟨w.1, by omega⟩
    have hf1 : Function.Injective f1 := fun a b h ↦ Fin.ext (by
      have hv := congrArg Fin.val h; change a.1 = b.1 at hv; exact hv)
    let f2 : {j : ℕ // j ∈ Finset.range (regDeficiency n₁ D G₁ u')} →
        Fin (2 * n₁ + 2 * n₁ * D) := fun j ↦
      ⟨2 * n₁ + 2 * u.1 * D + j.1, by
        have hj := (hdef u').2; have hj' := Finset.mem_range.mp j.2
        have : (2 * u.1 + 1) * D ≤ 2 * n₁ * D := Nat.mul_le_mul_right D (by omega)
        linarith⟩
    have hf2 : Function.Injective f2 := fun a b h ↦ Subtype.ext (by
      have hv := congrArg Fin.val h
      change 2 * n₁ + 2 * u.1 * D + a.1 = 2 * n₁ + 2 * u.1 * D + b.1 at hv; omega)
    let S₁ := (G₁.neighborFinset u').map ⟨f1, hf1⟩
    let S₂ := (Finset.range (regDeficiency n₁ D G₁ u')).attach.map ⟨f2, hf2⟩
    have hdisj : Disjoint S₁ S₂ := Finset.disjoint_left.mpr fun w hw1 hw2 ↦ by
      rcases Finset.mem_map.mp hw1 with ⟨x, _, rfl⟩
      rcases Finset.mem_map.mp hw2 with ⟨j, _, hw⟩
      have hv := congrArg Fin.val hw
      change 2 * n₁ + 2 * u.1 * D + j.1 = x.1 at hv; omega
    have hns : ns = S₁ ∪ S₂ := by
      ext w; rw [hmem_ns, Finset.mem_union]
      simp only [S₁, S₂, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        Finset.mem_range]
      constructor
      · intro ⟨_, h⟩
        rcases h with ⟨_, hv, h1⟩ | ⟨hu1, _⟩ | ⟨hu2n, _⟩ | ⟨_, _, hbv, hjv⟩ |
            ⟨hu2n, _⟩ | ⟨hu1, _⟩ | ⟨hu2n, _⟩
        · left; exact ⟨⟨w.1, hv⟩, (G₁.mem_neighborFinset u' ⟨w.1, hv⟩).mpr h1, Fin.ext rfl⟩
        · omega
        · omega
        · right
          have hdm := Nat.div_add_mod (w.1 - 2 * n₁) D
          rw [hbv, Nat.mul_comm D (2 * u.1)] at hdm
          exact ⟨(w.1 - 2 * n₁) % D, hjv,
            Fin.ext (by change 2 * n₁ + 2 * u.1 * D + (w.1 - 2 * n₁) % D = w.1; omega)⟩
        · omega
        · omega
        · omega
      · rintro (⟨x, hx, hw_eq⟩ | ⟨j, hj, hw_eq⟩)
        · subst hw_eq
          have hx' := (G₁.mem_neighborFinset u' x).mp hx
          refine ⟨Fin.ne_of_val_ne (by
              change u.1 ≠ x.1; intro h
              exact G₁.ne_of_adj hx' (Fin.ext h)), Or.inl ⟨hu0, x.2, hx'⟩⟩
        · subst hw_eq
          have hjD : j < D := hj.trans_le (hdef u').2
          refine ⟨Fin.ne_of_val_ne (by change u.1 ≠ 2 * n₁ + 2 * u.1 * D + j; omega),
            Or.inr (Or.inr (Or.inr (Or.inl ⟨hu0,
              by change 2 * n₁ ≤ 2 * n₁ + 2 * u.1 * D + j; omega, ?_⟩)))⟩
          change (2 * n₁ + 2 * u.1 * D + j - 2 * n₁) / D = 2 * u.1 ∧
            (2 * n₁ + 2 * u.1 * D + j - 2 * n₁) % D < regDeficiency n₁ D G₁ u'
          have hsub : 2 * n₁ + 2 * u.1 * D + j - 2 * n₁ = D * (2 * u.1) + j := by ring_nf; omega
          rw [hsub, Nat.mul_add_div hDpos, Nat.div_eq_of_lt hjD, add_zero,
            mul_comm D (2 * u.1), Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hjD]
          exact ⟨rfl, hj⟩
    rw [hns, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
      Finset.card_attach, Finset.card_range, SimpleGraph.card_neighborFinset_eq_degree]
    have hdeg_lt : G₁.degree u' ≤ D := (G₁.degree_lt_card_verts u').le.trans (by simpa using hD)
    simp only [regDeficiency]; omega
  · by_cases hu1 : u.1 < 2 * n₁
    · let u' : Fin n₁ := ⟨u.1 - n₁, by omega⟩
      let f1 : Fin n₁ → Fin (2 * n₁ + 2 * n₁ * D) := fun w ↦ ⟨n₁ + w.1, by omega⟩
      have hf1 : Function.Injective f1 := fun a b h ↦ Fin.ext (by
        have hv := congrArg Fin.val h; change n₁ + a.1 = n₁ + b.1 at hv; omega)
      let f2 : {j : ℕ // j ∈ Finset.range (regDeficiency n₁ D G₁ u')} →
          Fin (2 * n₁ + 2 * n₁ * D) := fun j ↦
        ⟨2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j.1, by
          have hj := (hdef u').2; have hj' := Finset.mem_range.mp j.2
          have : (2 * (u.1 - n₁) + 2) * D ≤ 2 * n₁ * D := Nat.mul_le_mul_right D (by omega)
          linarith⟩
      have hf2 : Function.Injective f2 := fun a b h ↦ Subtype.ext (by
        have hv := congrArg Fin.val h
        change 2 * n₁ + (2 * (u.1 - n₁) + 1) * D + a.1 =
          2 * n₁ + (2 * (u.1 - n₁) + 1) * D + b.1 at hv; omega)
      let S₁ := (G₁.neighborFinset u').map ⟨f1, hf1⟩
      let S₂ := (Finset.range (regDeficiency n₁ D G₁ u')).attach.map ⟨f2, hf2⟩
      have hdisj : Disjoint S₁ S₂ := Finset.disjoint_left.mpr fun w hw1 hw2 ↦ by
        rcases Finset.mem_map.mp hw1 with ⟨x, _, rfl⟩
        rcases Finset.mem_map.mp hw2 with ⟨j, _, hw⟩
        have hv := congrArg Fin.val hw
        change 2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j.1 = n₁ + x.1 at hv; omega
      have hns : ns = S₁ ∪ S₂ := by
        ext w; rw [hmem_ns, Finset.mem_union]
        simp only [S₁, S₂, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
          Finset.mem_range]
        constructor
        · intro ⟨_, h⟩
          rcases h with ⟨hu0', _⟩ | ⟨_, _, hv1, hv2, h2⟩ | ⟨hu2n, _⟩ | ⟨hu0', _⟩ |
              ⟨hu2n, _⟩ | ⟨_, _, _, hbv, hjv⟩ | ⟨hu2n, _⟩
          · omega
          · left; exact ⟨⟨w.1 - n₁, by omega⟩, (G₁.mem_neighborFinset u' _).mpr h2,
              Fin.ext (by change n₁ + (w.1 - n₁) = w.1; omega)⟩
          · omega
          · omega
          · omega
          · right
            have hdm := Nat.div_add_mod (w.1 - 2 * n₁) D
            rw [hbv, Nat.mul_comm D (2 * (u.1 - n₁) + 1)] at hdm
            exact ⟨(w.1 - 2 * n₁) % D, hjv, Fin.ext (by
              change 2 * n₁ + (2 * (u.1 - n₁) + 1) * D + (w.1 - 2 * n₁) % D = w.1; omega)⟩
          · omega
        · rintro (⟨x, hx, hw_eq⟩ | ⟨j, hj, hw_eq⟩)
          · subst hw_eq
            have hx' := (G₁.mem_neighborFinset u' x).mp hx
            refine ⟨Fin.ne_of_val_ne (by
                change u.1 ≠ n₁ + x.1; intro h
                exact G₁.ne_of_adj hx' (Fin.ext (by dsimp [u']; omega))),
              Or.inr (Or.inl ⟨by omega, hu1, by change n₁ ≤ n₁ + x.1; omega,
                by change n₁ + x.1 < 2 * n₁; omega, ?_⟩)⟩
            have hx_eq : (⟨(f1 x).1 - n₁, by change n₁ + x.1 - n₁ < n₁; omega⟩ : Fin n₁) = x :=
              Fin.ext (by change n₁ + x.1 - n₁ = x.1; omega)
            change G₁.Adj u' ⟨(f1 x).1 - n₁, _⟩; rw [hx_eq]; exact hx'
          · subst hw_eq
            have hjD : j < D := hj.trans_le (hdef u').2
            refine ⟨Fin.ne_of_val_ne (by
                change u.1 ≠ 2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j; omega),
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hu1,
                by change 2 * n₁ ≤ 2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j; omega, ?_⟩)))))⟩
            change (2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j - 2 * n₁) / D = 2 * (u.1 - n₁) + 1 ∧
              (2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j - 2 * n₁) % D < regDeficiency n₁ D G₁ u'
            have hsub : 2 * n₁ + (2 * (u.1 - n₁) + 1) * D + j - 2 * n₁ =
                D * (2 * (u.1 - n₁) + 1) + j := by ring_nf; omega
            rw [hsub, Nat.mul_add_div hDpos, Nat.div_eq_of_lt hjD, add_zero,
              mul_comm D (2 * (u.1 - n₁) + 1), Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hjD]
            exact ⟨rfl, hj⟩
      rw [hns, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
        Finset.card_attach, Finset.card_range, SimpleGraph.card_neighborFinset_eq_degree]
      have hdeg_lt : G₁.degree u' ≤ D := (G₁.degree_lt_card_verts u').le.trans (by simpa using hD)
      simp only [regDeficiency]; omega
    · have hu2n : 2 * n₁ ≤ u.1 := by omega
      set bu := (u.1 - 2 * n₁) / D
      set ju := (u.1 - 2 * n₁) % D
      have hbu_lt : bu < 2 * n₁ := by
        dsimp only [bu]; rw [Nat.div_lt_iff_lt_mul hDpos]; have := u.2; omega
      have hbu2_lt : bu / 2 < n₁ := by omega
      have hju_lt : ju < D := Nat.mod_lt _ hDpos
      let v0 : Fin n₁ := ⟨bu / 2, hbu2_lt⟩
      let opp : ℕ := if bu % 2 = 0 then bu + 1 else bu - 1
      have hopp_lem : ∀ (b m : ℕ), b < 2 * m →
          (if b % 2 = 0 then b + 1 else b - 1) < 2 * m ∧
          (if b % 2 = 0 then b + 1 else b - 1) / 2 = b / 2 ∧
          (if b % 2 = 0 then b + 1 else b - 1) % 2 ≠ b % 2 := fun b m _ ↦ by
        split_ifs <;> omega
      have hopp_props : opp < 2 * n₁ ∧ opp / 2 = bu / 2 ∧ opp % 2 ≠ bu % 2 :=
        hopp_lem bu n₁ hbu_lt
      let fS₁ : {x : ℕ // x ∈ (Finset.range D).filter
          (fun j ↦ ¬ (ju = j ∧ ju < regDeficiency n₁ D G₁ v0))} → Fin (2 * n₁ + 2 * n₁ * D) :=
        fun j ↦ ⟨2 * n₁ + opp * D + j.1, by
          have hj := Finset.mem_range.mp (Finset.mem_filter.mp j.2).1
          have : (opp + 1) * D ≤ 2 * n₁ * D := Nat.mul_le_mul_right D hopp_props.1
          linarith⟩
      have hfS₁_inj : Function.Injective fS₁ := fun a b h ↦ Subtype.ext (by
        have hv := congrArg Fin.val h
        change 2 * n₁ + opp * D + a.1 = 2 * n₁ + opp * D + b.1 at hv; omega)
      let S₁ : Finset (Fin (2 * n₁ + 2 * n₁ * D)) :=
        ((Finset.range D).filter (fun j ↦ ¬ (ju = j ∧ ju < regDeficiency n₁ D G₁ v0))).attach.map
          ⟨fS₁, hfS₁_inj⟩
      let wBase : Fin (2 * n₁ + 2 * n₁ * D) :=
        ⟨if bu % 2 = 0 then bu / 2 else n₁ + bu / 2, by split_ifs <;> omega⟩
      let S₂ : Finset (Fin (2 * n₁ + 2 * n₁ * D)) :=
        if ju < regDeficiency n₁ D G₁ v0 then {wBase} else ∅
      have hdisj : Disjoint S₁ S₂ := Finset.disjoint_left.mpr fun w hw1 hw2 ↦ by
        rcases Finset.mem_map.mp hw1 with ⟨j, _, rfl⟩
        dsimp only [S₂] at hw2
        by_cases hju : ju < regDeficiency n₁ D G₁ v0
        · rw [ite_eq_left hju, Finset.mem_singleton] at hw2
          have hv := congrArg Fin.val hw2
          change 2 * n₁ + opp * D + j.1 = (if bu % 2 = 0 then bu / 2 else n₁ + bu / 2) at hv
          split_ifs at hv <;> omega
        · rw [ite_eq_right hju] at hw2; exact Finset.notMem_empty _ hw2
      have hns : ns = S₁ ∪ S₂ := by
        ext w; rw [hmem_ns, Finset.mem_union]
        constructor
        · intro ⟨_, h⟩
          rcases h with ⟨hu0', _⟩ | ⟨_, hu1', _⟩ | h3 | ⟨hu0', _⟩ |
              ⟨_, hw, hbu_eq, hju_def⟩ | ⟨_, hu1', _⟩ | ⟨_, hw1, hw2, hbu_eq, hju_def⟩
          · omega
          · omega
          · left
            have hbv : (w.1 - 2 * n₁) / D = opp := by
              have h1 := h3.2.2.1; have h2 := h3.2.2.2.1
              dsimp only [opp, bu] at *; split_ifs <;> omega
            have hjv_lt : (w.1 - 2 * n₁) % D < D := Nat.mod_lt _ hDpos
            have hnot : ¬ (ju = (w.1 - 2 * n₁) % D ∧ ju < regDeficiency n₁ D G₁ v0) :=
              fun ⟨hj, hlt⟩ ↦ h3.2.2.2.2 ⟨hj, hbu2_lt, hlt⟩
            simp only [S₁, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
              Finset.mem_filter, Finset.mem_range]
            refine ⟨(w.1 - 2 * n₁) % D, ⟨hjv_lt, hnot⟩, Fin.ext ?_⟩
            have hdm := Nat.div_add_mod (w.1 - 2 * n₁) D
            rw [hbv, Nat.mul_comm D opp] at hdm
            change 2 * n₁ + opp * D + (w.1 - 2 * n₁) % D = w.1
            have hw2n := h3.2.1; omega
          · omega
          · right
            have hbu_eq' : bu = 2 * w.1 := hbu_eq
            have hbeven : bu % 2 = 0 := by omega
            have hv0_eq : v0 = ⟨w.1, hw⟩ := Fin.ext (by dsimp only [v0]; omega)
            have hju_v0 : ju < regDeficiency n₁ D G₁ v0 := hv0_eq ▸ hju_def
            dsimp only [S₂]; rw [ite_eq_left hju_v0, Finset.mem_singleton]
            exact Fin.ext (by dsimp only [wBase]; rw [ite_eq_left hbeven]; omega)
          · omega
          · right
            have hbu_eq' : bu = 2 * (w.1 - n₁) + 1 := hbu_eq
            have hbodd : ¬ bu % 2 = 0 := by omega
            have hv0_eq : v0 = ⟨w.1 - n₁, by omega⟩ := Fin.ext (by dsimp only [v0]; omega)
            have hju_v0 : ju < regDeficiency n₁ D G₁ v0 := hv0_eq ▸ hju_def
            dsimp only [S₂]; rw [ite_eq_left hju_v0, Finset.mem_singleton]
            exact Fin.ext (by dsimp only [wBase]; rw [ite_eq_right hbodd]; omega)
        · intro hw
          rcases hw with hw1 | hw2
          · simp only [S₁, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
              Finset.mem_filter, Finset.mem_range] at hw1
            rcases hw1 with ⟨j, ⟨hjD, hnot⟩, hw_eq⟩
            have hw_val : w.1 = 2 * n₁ + opp * D + j := (congrArg Fin.val hw_eq).symm
            have hsub : w.1 - 2 * n₁ = D * opp + j := by ring_nf at hw_val ⊢; omega
            have hdiv : (w.1 - 2 * n₁) / D = opp := by
              rw [hsub, Nat.mul_add_div hDpos, Nat.div_eq_of_lt hjD, add_zero]
            have hmod : (w.1 - 2 * n₁) % D = j := by
              rw [hsub, mul_comm D opp, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hjD]
            have hne : u ≠ w := fun heq ↦ by
              have hdiv_eq := congrArg (fun z : Fin _ ↦ (z.1 - 2 * n₁) / D) heq
              rw [hdiv] at hdiv_eq; change bu = opp at hdiv_eq
              exact hopp_props.2.2 (by rw [hdiv_eq])
            refine ⟨hne, Or.inr (Or.inr (Or.inl ⟨hu2n, by omega, ?_⟩))⟩
            change (u.1 - 2 * n₁) / D / 2 = (w.1 - 2 * n₁) / D / 2 ∧
              (u.1 - 2 * n₁) / D % 2 ≠ (w.1 - 2 * n₁) / D % 2 ∧
              ¬ ((u.1 - 2 * n₁) % D = (w.1 - 2 * n₁) % D ∧ ∃ (hbu : (u.1 - 2 * n₁) / D / 2 < n₁),
                (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨(u.1 - 2 * n₁) / D / 2, hbu⟩)
            rw [hdiv, hmod]
            exact ⟨hopp_props.2.1.symm, hopp_props.2.2.symm, fun ⟨hj, _, hlt⟩ ↦ hnot ⟨hj, hlt⟩⟩
          · dsimp only [S₂] at hw2
            by_cases hju : ju < regDeficiency n₁ D G₁ v0
            · rw [ite_eq_left hju, Finset.mem_singleton] at hw2; subst hw2
              by_cases hbeven : bu % 2 = 0
              · have hw_val : wBase.1 = bu / 2 := by dsimp only [wBase]; rw [ite_eq_left hbeven]
                refine ⟨Fin.ne_of_val_ne (by rw [hw_val]; omega),
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu2n, by rw [hw_val]; omega, ?_⟩))))⟩
                have hfin : (⟨wBase.1, by rw [hw_val]; omega⟩ : Fin n₁) = v0 :=
                  Fin.ext (by dsimp only [v0]; exact hw_val)
                change bu = 2 * wBase.1 ∧ ju < regDeficiency n₁ D G₁ ⟨wBase.1, _⟩
                rw [hfin, hw_val]; exact ⟨by omega, hju⟩
              · have hw_val : wBase.1 = n₁ + bu / 2 := by
                  dsimp only [wBase]; rw [ite_eq_right hbeven]
                refine ⟨Fin.ne_of_val_ne (by rw [hw_val]; omega),
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hu2n, by rw [hw_val]; omega,
                    by rw [hw_val]; omega, ?_⟩)))))⟩
                have hsub : wBase.1 - n₁ = bu / 2 := by rw [hw_val]; omega
                have hfin : (⟨wBase.1 - n₁, by rw [hw_val]; omega⟩ : Fin n₁) = v0 :=
                  Fin.ext (by dsimp only [v0]; exact hsub)
                change bu = 2 * (wBase.1 - n₁) + 1 ∧ ju < regDeficiency n₁ D G₁ ⟨wBase.1 - n₁, _⟩
                rw [hfin, hsub]; exact ⟨by omega, hju⟩
            · rw [ite_eq_right hju] at hw2; exact (Finset.notMem_empty _ hw2).elim
      rw [hns, Finset.card_union_of_disjoint hdisj]
      simp only [S₁, S₂, Finset.card_map, Finset.card_attach]
      by_cases hju : ju < regDeficiency n₁ D G₁ v0
      · have hfilt : (Finset.range D).filter (fun j ↦ ¬ (ju = j ∧ ju < regDeficiency n₁ D G₁ v0)) =
            (Finset.range D).erase ju := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, not_and]
          exact ⟨fun ⟨hj, h⟩ ↦ ⟨fun heq ↦ h heq.symm hju, hj⟩,
            fun ⟨hne, hj⟩ ↦ ⟨hj, fun heq _ ↦ hne heq.symm⟩⟩
        rw [hfilt, Finset.card_erase_of_mem (Finset.mem_range.mpr hju_lt), Finset.card_range,
          ite_eq_left hju, Finset.card_singleton]
        omega
      · have hfilt : (Finset.range D).filter (fun j ↦ ¬ (ju = j ∧ ju < regDeficiency n₁ D G₁ v0)) =
            Finset.range D := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range, not_and, and_iff_left_iff_imp]
          intro _ _ hlt; exact hju hlt
        rw [hfilt, Finset.card_range, ite_eq_right hju, Finset.card_empty, add_zero]

private theorem regGraph_gadget_indep_neighbors (n₁ D : ℕ)
    (G₁ : SimpleGraph (Fin n₁)) {u v w : Fin (2 * n₁ + 2 * n₁ * D)}
    (hu : 2 * n₁ ≤ u.1) (huv : (regGraph n₁ D G₁).Adj u v)
    (huw : (regGraph n₁ D G₁).Adj u w) : ¬ (regGraph n₁ D G₁).Adj v w := by
  have hparity : ∀ {x y : Fin (2 * n₁ + 2 * n₁ * D)}, 2 * n₁ ≤ x.1 →
      (regGraph n₁ D G₁).Adj x y →
      (2 * n₁ ≤ y.1 ∧ (x.1 - 2 * n₁) / D % 2 ≠ (y.1 - 2 * n₁) / D % 2) ∨
      (y.1 < n₁ ∧ (x.1 - 2 * n₁) / D = 2 * y.1) ∨
      (n₁ ≤ y.1 ∧ y.1 < 2 * n₁ ∧ (x.1 - 2 * n₁) / D = 2 * (y.1 - n₁) + 1) := by
    intro x y hx hxy
    rcases hxy.2 with ⟨hx0, _⟩ | ⟨_, hx1, _⟩ | h3 | ⟨hx0, _⟩ | ⟨_, hy, hbx, _⟩ |
        ⟨_, hx1, _⟩ | ⟨_, hy1, hy2, hbx, _⟩
    · omega
    · omega
    · exact Or.inl ⟨h3.2.1, h3.2.2.2.1⟩
    · omega
    · exact Or.inr (Or.inl ⟨hy, hbx⟩)
    · omega
    · exact Or.inr (Or.inr ⟨hy1, hy2, hbx⟩)
  intro hvw
  rcases hparity hu huv with ⟨hv2n, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩
  · rcases hparity hu huw with ⟨hw2n, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩
    · rcases hparity hv2n hvw with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega
    · rcases hparity hv2n hvw with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega
    · rcases hparity hv2n hvw with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega
  · rcases hparity hu huw with ⟨hw2n, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩
    · rcases hparity hw2n hvw.symm with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega
    · exact hvw.1 (Fin.ext (by omega))
    · omega
  · rcases hparity hu huw with ⟨hw2n, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩
    · rcases hparity hw2n hvw.symm with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega
    · omega
    · exact hvw.1 (Fin.ext (by omega))

private theorem regGraph_clique_iff (n₁ D l₁ : ℕ) (hl₁ : 3 ≤ l₁) (G₁ : SimpleGraph (Fin n₁)) :
    (∃ t : Finset (Fin (2 * n₁ + 2 * n₁ * D)), (regGraph n₁ D G₁).IsNClique l₁ t) ↔
      ∃ s : Finset (Fin n₁), G₁.IsNClique l₁ s := by
  classical
  let emb : Fin n₁ ↪ Fin (2 * n₁ + 2 * n₁ * D) :=
    ⟨fun v ↦ ⟨v.1, by omega⟩, fun a b h ↦ Fin.ext (by
      have hv := congrArg Fin.val h; dsimp only at hv; exact hv)⟩
  constructor
  · rintro ⟨t, htc, htcard⟩
    have hno_gad : ∀ u ∈ t, u.1 < 2 * n₁ := by
      intro u hu; by_contra hu_ge
      obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp
        (show 1 < (t.erase u).card by rw [Finset.card_erase_of_mem hu, htcard]; omega)
      exact regGraph_gadget_indep_neighbors n₁ D G₁ (by omega)
        (htc hu (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1.symm)
        (htc hu (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm)
        (htc (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hw).2 hvw)
    obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp (by rw [htcard]; omega : 0 < t.card)
    have hu₀_lt := hno_gad u₀ hu₀
    by_cases hcopy : u₀.1 < n₁
    · have hall0 : ∀ v ∈ t, v.1 < n₁ := fun v hv ↦ by
        by_cases heq : v = u₀
        · exact heq ▸ hcopy
        · have hv2n := hno_gad v hv
          rcases (htc hu₀ hv (Ne.symm heq)).2 with ⟨_, hv', _⟩ | ⟨hu1, _⟩ | ⟨hu2n, _⟩ |
              ⟨_, hv2n', _⟩ | ⟨hu2n, _⟩ | ⟨hu1, _⟩ | ⟨hu2n, _⟩ <;> omega
      let s : Finset (Fin n₁) := Finset.univ.filter fun v ↦ emb v ∈ t
      have himg : s.map emb = t := by
        ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, s]
        exact ⟨fun ⟨_, hv, heq⟩ ↦ heq ▸ hv, fun hx ↦ ⟨⟨x.1, hall0 x hx⟩, hx, Fin.ext rfl⟩⟩
      refine ⟨s, ?_, by rw [← Finset.card_map emb, himg, htcard]⟩
      intro a ha b hb hab
      have hadj := htc (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
        (emb.injective.ne hab)
      rcases hadj.2 with ⟨_, _, h1⟩ | ⟨ha1, _⟩ | ⟨ha2n, _⟩ | ⟨_, hb2n, _⟩ |
          ⟨ha2n, _⟩ | ⟨ha1, _⟩ | ⟨ha2n, _⟩
      · exact h1
      all_goals
        exfalso
        have ha_lt : (emb a).1 < n₁ := a.2
        have hb_lt : (emb b).1 < n₁ := b.2
        omega
    · have hall1 : ∀ v ∈ t, n₁ ≤ v.1 ∧ v.1 < 2 * n₁ := fun v hv ↦ by
        by_cases heq : v = u₀
        · exact heq ▸ ⟨by omega, hu₀_lt⟩
        · have hv2n := hno_gad v hv
          rcases (htc hu₀ hv (Ne.symm heq)).2 with ⟨hu0', _⟩ | ⟨_, _, hv1, hv2, _⟩ | ⟨hu2n, _⟩ |
              ⟨hu0', _⟩ | ⟨hu2n, _⟩ | ⟨_, _, hv2n', _⟩ | ⟨hu2n, _⟩
          · omega
          · exact ⟨hv1, hv2⟩
          all_goals omega
      let emb1 : Fin n₁ ↪ Fin (2 * n₁ + 2 * n₁ * D) :=
        ⟨fun v ↦ ⟨n₁ + v.1, by omega⟩, fun a b h ↦ Fin.ext (by
          have := congrArg Fin.val h; dsimp only at this; omega)⟩
      let s : Finset (Fin n₁) := Finset.univ.filter fun v ↦ emb1 v ∈ t
      have himg : s.map emb1 = t := by
        ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, s]
        refine ⟨fun ⟨_, hv, heq⟩ ↦ heq ▸ hv, fun hx ↦ ?_⟩
        have hx' := hall1 x hx
        have heq : emb1 ⟨x.1 - n₁, by omega⟩ = x :=
          Fin.ext (by change n₁ + (x.1 - n₁) = x.1; omega)
        exact ⟨⟨x.1 - n₁, by omega⟩, heq ▸ hx, heq⟩
      refine ⟨s, ?_, by rw [← Finset.card_map emb1, himg, htcard]⟩
      intro a ha b hb hab
      have ha_eq : (emb1 a).1 = n₁ + a.1 := rfl
      have hb_eq : (emb1 b).1 = n₁ + b.1 := rfl
      have hadj := htc (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
        (emb1.injective.ne hab)
      rcases hadj.2 with ⟨ha0, _⟩ | ⟨_, _, _, _, h2⟩ | ⟨ha2n, _⟩ | ⟨ha0, _⟩ |
          ⟨ha2n, _⟩ | ⟨_, _, hb2n, _⟩ | ⟨ha2n, _⟩
      · exfalso; omega
      · have h1 : (⟨(emb1 a).1 - n₁, by omega⟩ : Fin n₁) = a := Fin.ext (by dsimp only; omega)
        have h3 : (⟨(emb1 b).1 - n₁, by omega⟩ : Fin n₁) = b := Fin.ext (by dsimp only; omega)
        rwa [h1, h3] at h2
      all_goals
        exfalso
        have := a.2; have := b.2; omega
  · rintro ⟨s, hsc, hscard⟩
    refine ⟨s.map emb, ?_, by rw [Finset.card_map, hscard]⟩
    intro x hx y hy hne
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨b, hb, rfl⟩
    exact ⟨hne, Or.inl ⟨a.2, b.2, hsc ha hb fun h ↦ hne (congrArg emb h)⟩⟩

end Regularization

/-! ### Polynomial-time and `FPT` reduction on `CliqueInstance` -/

/-- Regularity degree parameter `D(x) = max (n + 3) (min (n + 1) x.m + 4)`. -/
def regCliqueDeg (x : CliqueInstance) : ℕ :=
  let n := x.graph.distinctVertices.length
  max (n + 3) (min (n + 1) x.m + 4)

/-- Total vertex count `N(x) = 2 * (n + 3) + 2 * (n + 3) * regCliqueDeg x`. -/
def regCliqueNumVerts (x : CliqueInstance) : ℕ :=
  let n₁ := x.graph.distinctVertices.length + 3
  2 * n₁ + 2 * n₁ * regCliqueDeg x

private def regCliqueFinGraph (x : CliqueInstance) : SimpleGraph (Fin (regCliqueNumVerts x)) :=
  regGraph (x.graph.distinctVertices.length + 3) (regCliqueDeg x)
    (joinK3Graph x.graph.distinctVertices.length (graphFin x.graph))

private theorem regCliqueFinGraph_isRegular (x : CliqueInstance) :
    let _ := Classical.decRel (regCliqueFinGraph x).Adj
    (regCliqueFinGraph x).IsRegularOfDegree (regCliqueDeg x) := by
  unfold regCliqueFinGraph regCliqueNumVerts; dsimp only
  exact regGraph_degree_eq _ (regCliqueDeg x) (le_max_left _ _)
    (by unfold regCliqueDeg; dsimp only; omega) _

private theorem regCliqueFinGraph_clique_iff (x : CliqueInstance) :
    (∃ t : Finset (Fin (regCliqueNumVerts x)), (regCliqueFinGraph x).IsNClique (x.m + 3) t) ↔
      x ∈ Clique := by
  unfold regCliqueFinGraph regCliqueNumVerts; dsimp only
  rw [regGraph_clique_iff _ _ (x.m + 3) (by omega), ← joinK3Graph_mem_iff,
    exists_isNClique_graphFin_iff]

private def udiv (a b : ℕ) : ℕ :=
  if decide (b ≤ 0) then 0 else (List.range a).countP fun q ↦ decide ((q + 1) * b ≤ a)

private theorem udiv_eq_div (a b : ℕ) : udiv a b = a / b := by
  unfold udiv
  by_cases hb : b ≤ 0
  · obtain rfl : b = 0 := by omega
    simp
  · rw [ite_eq_right (mt of_decide_eq_true hb)]
    have hb_pos : 0 < b := by omega
    have hq_le : a / b ≤ a := Nat.div_le_self a b
    have hiff : ∀ q : ℕ, (q + 1) * b ≤ a ↔ q < a / b := fun q ↦
      (Nat.le_div_iff_mul_le hb_pos).symm
    have hcnt : ∀ m : ℕ, (List.range m).countP (fun q ↦ decide ((q + 1) * b ≤ a)) =
        min m (a / b) := fun m ↦ by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.countP_append, ih, List.countP_singleton]
        by_cases hm : (m + 1) * b ≤ a
        · have hm' : m < a / b := (hiff m).mp hm
          simp only [hm, decide_true, ↓reduceIte]
          omega
        · have hm' : ¬ m < a / b := fun h ↦ hm ((hiff m).mpr h)
          simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
          omega
    rw [hcnt a, Nat.min_eq_right hq_le]

private def umod (a b : ℕ) : ℕ := a - b * udiv a b

private theorem umod_eq_mod (a b : ℕ) : umod a b = a % b := by
  unfold umod; rw [udiv_eq_div]
  have h := Nat.div_add_mod a b; omega

private def joinK3Bool (x : CliqueInstance) (a b : ℕ) : Bool :=
  let dvs := x.graph.distinctVertices
  let n := dvs.length
  !decide (a = b) &&
    (decide (n ≤ a) || decide (n ≤ b) ||
      (decide (a < n) && decide (b < n) && x.graph.adjBool (dvs.getD a 0) (dvs.getD b 0)))

private theorem joinK3Bool_eq_decide (x : CliqueInstance)
    (a b : Fin (x.graph.distinctVertices.length + 3)) :
    joinK3Bool x a.1 b.1 =
      let _ := Classical.decRel (joinK3Graph x.graph.distinctVertices.length (graphFin x.graph)).Adj
      decide ((joinK3Graph x.graph.distinctVertices.length (graphFin x.graph)).Adj a b) := by
  classical
  dsimp only
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [joinK3Bool, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, joinK3Graph, joinK3Adj, or_assoc]
  rw [← Fin.ext_iff]
  refine and_congr_right fun _ ↦ or_congr_right (or_congr_right ?_)
  constructor
  · rintro ⟨⟨ha, hb⟩, hbit⟩
    exact ⟨ha, hb, (graphFin_adj_iff_adjBool x.graph ⟨a.1, ha⟩ ⟨b.1, hb⟩).mpr hbit⟩
  · rintro ⟨ha, hb, hadj⟩
    exact ⟨⟨ha, hb⟩, (graphFin_adj_iff_adjBool x.graph ⟨a.1, ha⟩ ⟨b.1, hb⟩).mp hadj⟩

private def joinK3DegBool (x : CliqueInstance) (u : ℕ) : ℕ :=
  let n₁ := x.graph.distinctVertices.length + 3
  if decide (u < n₁) then (List.range n₁).countP (fun w ↦ joinK3Bool x u w) else 0

private theorem joinK3DegBool_eq_degree (x : CliqueInstance)
    (u : Fin (x.graph.distinctVertices.length + 3)) :
    joinK3DegBool x u.1 =
      let _ := Classical.decRel (joinK3Graph x.graph.distinctVertices.length (graphFin x.graph)).Adj
      (joinK3Graph x.graph.distinctVertices.length (graphFin x.graph)).degree u := by
  classical
  let n₁ := x.graph.distinctVertices.length + 3
  let G₁ := joinK3Graph x.graph.distinctVertices.length (graphFin x.graph)
  unfold joinK3DegBool
  dsimp only
  rw [ite_eq_left (decide_eq_true u.2), SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  have hr : List.range n₁ = (List.finRange n₁).map Fin.val :=
    (List.ext_getElem (by simp) fun i _ _ ↦ by simp).symm
  rw [hr, List.countP_map, Function.comp_def]
  have hcongr : List.countP (fun w : Fin n₁ ↦ joinK3Bool x u.1 w.1) (List.finRange n₁) =
      ((List.finRange n₁).filter fun w : Fin n₁ ↦ decide (G₁.Adj u w)).length := by
    rw [List.countP_eq_length_filter]
    congr 1; refine List.filter_congr fun w _ ↦ ?_
    exact joinK3Bool_eq_decide x u w
  rw [hcongr]
  have hnd : ((List.finRange n₁).filter fun w : Fin n₁ ↦ decide (G₁.Adj u w)).Nodup :=
    (List.nodup_finRange n₁).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1; ext w; simp [G₁]

private def regAdjBool (x : CliqueInstance) (u v : ℕ) : Bool :=
  let n₁ := x.graph.distinctVertices.length + 3
  let D := regCliqueDeg x
  let defOf (z : ℕ) : ℕ := D - joinK3DegBool x z
  let bu := udiv (u - 2 * n₁) D
  let bv := udiv (v - 2 * n₁) D
  let ju := umod (u - 2 * n₁) D
  let jv := umod (v - 2 * n₁) D
  !decide (u = v) &&
    ((decide (u < n₁) && decide (v < n₁) && joinK3Bool x u v) ||
     (decide (n₁ ≤ u) && decide (u < 2 * n₁) && decide (n₁ ≤ v) && decide (v < 2 * n₁) &&
       joinK3Bool x (u - n₁) (v - n₁)) ||
     (decide (2 * n₁ ≤ u) && decide (2 * n₁ ≤ v) &&
       decide (udiv bu 2 = udiv bv 2) && !decide (umod bu 2 = umod bv 2) &&
       !(decide (ju = jv) && decide (ju < defOf (udiv bu 2)))) ||
     (decide (u < n₁) && decide (2 * n₁ ≤ v) && decide (bv = 2 * u) && decide (jv < defOf u)) ||
     (decide (2 * n₁ ≤ u) && decide (v < n₁) && decide (bu = 2 * v) && decide (ju < defOf v)) ||
     (decide (n₁ ≤ u) && decide (u < 2 * n₁) && decide (2 * n₁ ≤ v) &&
       decide (bv = 2 * (u - n₁) + 1) && decide (jv < defOf (u - n₁))) ||
     (decide (2 * n₁ ≤ u) && decide (n₁ ≤ v) && decide (v < 2 * n₁) &&
       decide (bu = 2 * (v - n₁) + 1) && decide (ju < defOf (v - n₁))))

private theorem regAdjBool_eq_true_iff (x : CliqueInstance) (u v : Fin (regCliqueNumVerts x)) :
    regAdjBool x u.1 v.1 = true ↔ (regCliqueFinGraph x).Adj u v := by
  classical
  set n₁ := x.graph.distinctVertices.length + 3
  set D := regCliqueDeg x
  set G₁ := joinK3Graph x.graph.distinctVertices.length (graphFin x.graph)
  have hDpos : 0 < D := by dsimp only [D, regCliqueDeg]; omega
  have hdef_eq : ∀ z : Fin n₁, D - joinK3DegBool x z.1 = regDeficiency n₁ D G₁ z := fun z ↦ by
    rw [joinK3DegBool_eq_degree x z]; rfl
  simp only [regAdjBool, udiv_eq_div, umod_eq_mod, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
    regCliqueFinGraph, regGraph, regAdj]
  rw [← Fin.ext_iff]
  refine and_congr_right fun _ ↦ ?_
  have c1 : (((u.1 < n₁ ∧ v.1 < n₁) ∧ joinK3Bool x u.1 v.1 = true) ↔
      ∃ (hu : u.1 < n₁) (hv : v.1 < n₁), G₁.Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩) := by
    refine ⟨fun ⟨⟨hu, hv⟩, hb⟩ ↦ ⟨hu, hv, ?_⟩, fun ⟨hu, hv, hadj⟩ ↦ ⟨⟨hu, hv⟩, ?_⟩⟩
    · rw [joinK3Bool_eq_decide x ⟨u.1, hu⟩ ⟨v.1, hv⟩, decide_eq_true_eq] at hb; exact hb
    · rw [joinK3Bool_eq_decide x ⟨u.1, hu⟩ ⟨v.1, hv⟩, decide_eq_true_eq]; exact hadj
  have c2 : (((((n₁ ≤ u.1 ∧ u.1 < 2 * n₁) ∧ n₁ ≤ v.1) ∧ v.1 < 2 * n₁) ∧
      joinK3Bool x (u.1 - n₁) (v.1 - n₁) = true) ↔
      ∃ (hu1 : n₁ ≤ u.1) (hu2 : u.1 < 2 * n₁) (hv1 : n₁ ≤ v.1) (hv2 : v.1 < 2 * n₁),
        G₁.Adj ⟨u.1 - n₁, by omega⟩ ⟨v.1 - n₁, by omega⟩) := by
    refine ⟨fun ⟨⟨⟨⟨hu1, hu2⟩, hv1⟩, hv2⟩, hb⟩ ↦ ⟨hu1, hu2, hv1, hv2, ?_⟩,
      fun ⟨hu1, hu2, hv1, hv2, hadj⟩ ↦ ⟨⟨⟨⟨hu1, hu2⟩, hv1⟩, hv2⟩, ?_⟩⟩
    · rw [joinK3Bool_eq_decide x ⟨u.1 - n₁, by omega⟩ ⟨v.1 - n₁, by omega⟩,
        decide_eq_true_eq] at hb
      exact hb
    · rw [joinK3Bool_eq_decide x ⟨u.1 - n₁, by omega⟩ ⟨v.1 - n₁, by omega⟩, decide_eq_true_eq]
      exact hadj
  have c3 : (((((2 * n₁ ≤ u.1 ∧ 2 * n₁ ≤ v.1) ∧
        (u.1 - 2 * n₁) / D / 2 = (v.1 - 2 * n₁) / D / 2) ∧
        ¬(u.1 - 2 * n₁) / D % 2 = (v.1 - 2 * n₁) / D % 2) ∧
        (¬(u.1 - 2 * n₁) % D = (v.1 - 2 * n₁) % D ∨
          ¬(u.1 - 2 * n₁) % D < D - joinK3DegBool x ((u.1 - 2 * n₁) / D / 2))) ↔
      (2 * n₁ ≤ u.1 ∧ 2 * n₁ ≤ v.1 ∧
        (u.1 - 2 * n₁) / D / 2 = (v.1 - 2 * n₁) / D / 2 ∧
        (u.1 - 2 * n₁) / D % 2 ≠ (v.1 - 2 * n₁) / D % 2 ∧
        ¬((u.1 - 2 * n₁) % D = (v.1 - 2 * n₁) % D ∧
          ∃ hbu : (u.1 - 2 * n₁) / D / 2 < n₁,
            (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨(u.1 - 2 * n₁) / D / 2, hbu⟩))) := by
    constructor
    · rintro ⟨⟨⟨⟨hu2, hv2⟩, hdiv⟩, hmod⟩, hor⟩
      refine ⟨hu2, hv2, hdiv, hmod, fun ⟨hj, hbu, hlt⟩ ↦ ?_⟩
      rcases hor with hne | hnlt
      · exact hne hj
      · exact hnlt (by rwa [hdef_eq ⟨(u.1 - 2 * n₁) / D / 2, hbu⟩])
    · rintro ⟨hu2, hv2, hdiv, hmod, hnot⟩
      refine ⟨⟨⟨⟨hu2, hv2⟩, hdiv⟩, hmod⟩, ?_⟩
      by_cases hj : (u.1 - 2 * n₁) % D = (v.1 - 2 * n₁) % D
      · right; intro hlt
        have hu_lt : u.1 < 2 * n₁ + 2 * n₁ * D := by
          simpa only [regCliqueNumVerts, n₁, D] using u.2
        have hbu_lt : (u.1 - 2 * n₁) / D < 2 * n₁ := (Nat.div_lt_iff_lt_mul hDpos).mpr (by omega)
        have hbu : (u.1 - 2 * n₁) / D / 2 < n₁ := by omega
        exact hnot ⟨hj, hbu, by rwa [← hdef_eq ⟨(u.1 - 2 * n₁) / D / 2, hbu⟩]⟩
      · exact Or.inl hj
  have c4 : ((((u.1 < n₁ ∧ 2 * n₁ ≤ v.1) ∧ (v.1 - 2 * n₁) / D = 2 * u.1) ∧
      (v.1 - 2 * n₁) % D < D - joinK3DegBool x u.1) ↔
      ∃ hu : u.1 < n₁, 2 * n₁ ≤ v.1 ∧ (v.1 - 2 * n₁) / D = 2 * u.1 ∧
        (v.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨u.1, hu⟩) :=
    ⟨fun ⟨⟨⟨hu, hv2⟩, hbv⟩, hlt⟩ ↦ ⟨hu, hv2, hbv, by rwa [← hdef_eq ⟨u.1, hu⟩]⟩,
     fun ⟨hu, hv2, hbv, hlt⟩ ↦ ⟨⟨⟨hu, hv2⟩, hbv⟩, by rwa [hdef_eq ⟨u.1, hu⟩]⟩⟩
  have c5 : ((((2 * n₁ ≤ u.1 ∧ v.1 < n₁) ∧ (u.1 - 2 * n₁) / D = 2 * v.1) ∧
      (u.1 - 2 * n₁) % D < D - joinK3DegBool x v.1) ↔
      2 * n₁ ≤ u.1 ∧ ∃ hv : v.1 < n₁, (u.1 - 2 * n₁) / D = 2 * v.1 ∧
        (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨v.1, hv⟩) :=
    ⟨fun ⟨⟨⟨hu2, hv⟩, hbu⟩, hlt⟩ ↦ ⟨hu2, hv, hbu, by rwa [← hdef_eq ⟨v.1, hv⟩]⟩,
     fun ⟨hu2, hv, hbu, hlt⟩ ↦ ⟨⟨⟨hu2, hv⟩, hbu⟩, by rwa [hdef_eq ⟨v.1, hv⟩]⟩⟩
  have c6 : (((((n₁ ≤ u.1 ∧ u.1 < 2 * n₁) ∧ 2 * n₁ ≤ v.1) ∧
      (v.1 - 2 * n₁) / D = 2 * (u.1 - n₁) + 1) ∧
      (v.1 - 2 * n₁) % D < D - joinK3DegBool x (u.1 - n₁)) ↔
      ∃ (hu1 : n₁ ≤ u.1) (hu2 : u.1 < 2 * n₁), 2 * n₁ ≤ v.1 ∧
        (v.1 - 2 * n₁) / D = 2 * (u.1 - n₁) + 1 ∧
        (v.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨u.1 - n₁, by omega⟩) :=
    ⟨fun ⟨⟨⟨⟨hu1, hu2⟩, hv2⟩, hbv⟩, hlt⟩ ↦
       ⟨hu1, hu2, hv2, hbv, by rwa [← hdef_eq ⟨u.1 - n₁, by omega⟩]⟩,
     fun ⟨hu1, hu2, hv2, hbv, hlt⟩ ↦
       ⟨⟨⟨⟨hu1, hu2⟩, hv2⟩, hbv⟩, by rwa [hdef_eq ⟨u.1 - n₁, by omega⟩]⟩⟩
  have c7 : (((((2 * n₁ ≤ u.1 ∧ n₁ ≤ v.1) ∧ v.1 < 2 * n₁) ∧
      (u.1 - 2 * n₁) / D = 2 * (v.1 - n₁) + 1) ∧
      (u.1 - 2 * n₁) % D < D - joinK3DegBool x (v.1 - n₁)) ↔
      2 * n₁ ≤ u.1 ∧ ∃ (hv1 : n₁ ≤ v.1) (hv2 : v.1 < 2 * n₁),
        (u.1 - 2 * n₁) / D = 2 * (v.1 - n₁) + 1 ∧
        (u.1 - 2 * n₁) % D < regDeficiency n₁ D G₁ ⟨v.1 - n₁, by omega⟩) :=
    ⟨fun ⟨⟨⟨⟨hu2, hv1⟩, hv2⟩, hbu⟩, hlt⟩ ↦
       ⟨hu2, hv1, hv2, hbu, by rwa [← hdef_eq ⟨v.1 - n₁, by omega⟩]⟩,
     fun ⟨hu2, hv1, hv2, hbu, hlt⟩ ↦
       ⟨⟨⟨⟨hu2, hv1⟩, hv2⟩, hbu⟩, by rwa [hdef_eq ⟨v.1 - n₁, by omega⟩]⟩⟩
  rw [c1, c2, c3, c4, c5, c6, c7]
  simp only [or_assoc]
  exact Iff.rfl

private lemma poly_and {α : Type} {enc : α ↪ List Bool} {a b : α → Bool}
    (ha : ComputableInPolyTime a enc encBool) (hb : ComputableInPolyTime b enc encBool) :
    ComputableInPolyTime (fun x ↦ a x && b x) enc encBool :=
  (ha.ite hb (.const false)).of_enc_eq fun x ↦ by cases a x <;> rfl

private lemma poly_or {α : Type} {enc : α ↪ List Bool} {a b : α → Bool}
    (ha : ComputableInPolyTime a enc encBool) (hb : ComputableInPolyTime b enc encBool) :
    ComputableInPolyTime (fun x ↦ a x || b x) enc encBool :=
  (ha.ite (.const true) hb).of_enc_eq fun x ↦ by cases a x <;> rfl

private lemma poly_not {α : Type} {enc : α ↪ List Bool} {a : α → Bool}
    (ha : ComputableInPolyTime a enc encBool) :
    ComputableInPolyTime (fun x ↦ !a x) enc encBool :=
  (ha.ite (.const false) (.const true)).of_enc_eq fun x ↦ by cases a x <;> rfl

@[local fun_prop]
private theorem computableInPolyTime_udiv {γ : Type} {enc : γ ↪ List Bool} {f g : γ → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun a ↦ udiv (f a) (g a)) enc encUnary := by
  unfold udiv; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_umod {γ : Type} {enc : γ ↪ List Bool} {f g : γ → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun a ↦ umod (f a) (g a)) enc encUnary := by
  unfold umod; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_regCliqueDeg :
    ComputableInPolyTime regCliqueDeg encCliqueInstance encUnary := by
  change ComputableInPolyTime
    (fun x : CliqueInstance ↦
      max (x.graph.distinctVertices.length + 3)
        (min (x.graph.distinctVertices.length + 1) x.m + 4))
    encCliqueInstance encUnary
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_regCliqueNumVerts :
    ComputableInPolyTime regCliqueNumVerts encCliqueInstance encUnary := by
  have hn₁ : ComputableInPolyTime (fun x : CliqueInstance ↦ x.graph.distinctVertices.length + 3)
      encCliqueInstance encUnary := by fun_prop
  have hD := computableInPolyTime_regCliqueDeg
  exact ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (.const 2) hn₁)
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul' (.const 2) hn₁) hD)

private lemma computableInPolyTime_joinK3Bool {γ : Type} {enc : γ ↪ List Bool}
    {fx : γ → CliqueInstance} {fa fb : γ → ℕ}
    (hx : ComputableInPolyTime fx enc encCliqueInstance)
    (ha : ComputableInPolyTime fa enc encUnary)
    (hb : ComputableInPolyTime fb enc encUnary) :
    ComputableInPolyTime (fun z ↦ joinK3Bool (fx z) (fa z) (fb z)) enc encBool := by
  have hg := encCliqueInstance_graph_polyTime hx
  have hdvs : ComputableInPolyTime (fun z ↦ (fx z).graph.distinctVertices) enc (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp hg
  have hn : ComputableInPolyTime (fun z ↦ (fx z).graph.distinctVertices.length) enc encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hdvs
  have hgetA := ComputableInPolyTime.listGetDWithInput hdvs ha 0
  have hgetB := ComputableInPolyTime.listGetDWithInput hdvs hb 0
  have hadj := Graph.computableInPolyTime_adjBool.comp ((hg.prod hgetA).prod hgetB)
  exact (poly_and (poly_not (ComputableInPolyTime.decide_eq' ha hb))
    (poly_or (poly_or (ComputableInPolyTime.unary_le' hn ha)
        (ComputableInPolyTime.unary_le' hn hb))
      (poly_and (poly_and (ComputableInPolyTime.unary_lt' ha hn)
        (ComputableInPolyTime.unary_lt' hb hn)) hadj))).of_enc_eq fun _ ↦
    congrArg encBool
      (by dsimp only [joinK3Bool]; simp only [Bool.or_assoc, Bool.and_assoc, Function.comp_apply])

private lemma computableInPolyTime_joinK3DegBool {γ : Type} {enc : γ ↪ List Bool}
    {fx : γ → CliqueInstance} {fu : γ → ℕ}
    (hx : ComputableInPolyTime fx enc encCliqueInstance)
    (hu : ComputableInPolyTime fu enc encUnary) :
    ComputableInPolyTime (fun z ↦ joinK3DegBool (fx z) (fu z)) enc encUnary := by
  have hn₁ : ComputableInPolyTime (fun z ↦ (fx z).graph.distinctVertices.length + 3)
      enc encUnary :=
    ComputableInPolyTime.unary_add'
      ((ComputableInPolyTime.length_list encNat).comp
        (Graph.computableInPolyTime_distinctVertices.comp
          (encCliqueInstance_graph_polyTime hx)))
      (.const 3)
  have hcnt : ComputableInPolyTime
      (fun z ↦ (List.range ((fx z).graph.distinctVertices.length + 3)).countP
        (fun w ↦ joinK3Bool (fx z) (fu z) w)) enc encUnary :=
    ComputableInPolyTime.countPWithInput (ComputableInPolyTime.range.comp hn₁)
      (computableInPolyTime_joinK3Bool (hx.comp (.fst _ _)) (hu.comp (.fst _ _)) (.snd _ _))
  exact ((ComputableInPolyTime.unary_lt' hu hn₁).ite hcnt (.const 0)).of_enc_eq fun _ ↦ rfl

private theorem computableInPolyTime_regAdjBool :
    ComputableInPolyTime (fun p : CliqueInstance × (ℕ × ℕ) ↦ regAdjBool p.1 p.2.1 p.2.2)
      (encPair encCliqueInstance (encPair encUnary encUnary)) encBool := by
  have hx : ComputableInPolyTime (fun p : CliqueInstance × (ℕ × ℕ) ↦ p.1)
      (encPair encCliqueInstance (encPair encUnary encUnary)) encCliqueInstance := .fst _ _
  have hu : ComputableInPolyTime (fun p : CliqueInstance × (ℕ × ℕ) ↦ p.2.1)
      (encPair encCliqueInstance (encPair encUnary encUnary)) encUnary :=
    (ComputableInPolyTime.snd _ _).fst'
  have hv : ComputableInPolyTime (fun p : CliqueInstance × (ℕ × ℕ) ↦ p.2.2)
      (encPair encCliqueInstance (encPair encUnary encUnary)) encUnary :=
    (ComputableInPolyTime.snd _ _).snd'
  have hn₁ := ComputableInPolyTime.unary_add'
    ((ComputableInPolyTime.length_list encNat).comp
      (Graph.computableInPolyTime_distinctVertices.comp
        (encCliqueInstance_graph_polyTime hx))) (.const 3)
  have h2n₁ := ComputableInPolyTime.unary_mul' (.const 2) hn₁
  have hD := computableInPolyTime_regCliqueDeg.comp hx
  have hu_sub := ComputableInPolyTime.unary_sub' hu h2n₁
  have hv_sub := ComputableInPolyTime.unary_sub' hv h2n₁
  have hbu := computableInPolyTime_udiv hu_sub hD
  have hbv := computableInPolyTime_udiv hv_sub hD
  have hju := computableInPolyTime_umod hu_sub hD
  have hjv := computableInPolyTime_umod hv_sub hD
  have hbu2 := computableInPolyTime_udiv hbu (.const 2)
  have hbv2 := computableInPolyTime_udiv hbv (.const 2)
  have hbum2 := computableInPolyTime_umod hbu (.const 2)
  have hbvm2 := computableInPolyTime_umod hbv (.const 2)
  have hun := ComputableInPolyTime.unary_sub' hu hn₁
  have hvn := ComputableInPolyTime.unary_sub' hv hn₁
  have hdef_bu2 := ComputableInPolyTime.unary_sub' hD (computableInPolyTime_joinK3DegBool hx hbu2)
  have hdef_u := ComputableInPolyTime.unary_sub' hD (computableInPolyTime_joinK3DegBool hx hu)
  have hdef_v := ComputableInPolyTime.unary_sub' hD (computableInPolyTime_joinK3DegBool hx hv)
  have hdef_un := ComputableInPolyTime.unary_sub' hD (computableInPolyTime_joinK3DegBool hx hun)
  have hdef_vn := ComputableInPolyTime.unary_sub' hD (computableInPolyTime_joinK3DegBool hx hvn)
  have hb1 := poly_and (poly_and (ComputableInPolyTime.unary_lt' hu hn₁)
      (ComputableInPolyTime.unary_lt' hv hn₁))
    (computableInPolyTime_joinK3Bool hx hu hv)
  have hb2 := poly_and (poly_and (poly_and (poly_and
      (ComputableInPolyTime.unary_le' hn₁ hu) (ComputableInPolyTime.unary_lt' hu h2n₁))
      (ComputableInPolyTime.unary_le' hn₁ hv)) (ComputableInPolyTime.unary_lt' hv h2n₁))
    (computableInPolyTime_joinK3Bool hx hun hvn)
  have hb3 := poly_and (poly_and (poly_and (poly_and
      (ComputableInPolyTime.unary_le' h2n₁ hu) (ComputableInPolyTime.unary_le' h2n₁ hv))
      (ComputableInPolyTime.decide_eq' hbu2 hbv2))
      (poly_not (ComputableInPolyTime.decide_eq' hbum2 hbvm2)))
    (poly_not (poly_and (ComputableInPolyTime.decide_eq' hju hjv)
      (ComputableInPolyTime.unary_lt' hju hdef_bu2)))
  have hb4 := poly_and (poly_and (poly_and
      (ComputableInPolyTime.unary_lt' hu hn₁) (ComputableInPolyTime.unary_le' h2n₁ hv))
      (ComputableInPolyTime.decide_eq' hbv (ComputableInPolyTime.unary_mul' (.const 2) hu)))
    (ComputableInPolyTime.unary_lt' hjv hdef_u)
  have hb5 := poly_and (poly_and (poly_and
      (ComputableInPolyTime.unary_le' h2n₁ hu) (ComputableInPolyTime.unary_lt' hv hn₁))
      (ComputableInPolyTime.decide_eq' hbu (ComputableInPolyTime.unary_mul' (.const 2) hv)))
    (ComputableInPolyTime.unary_lt' hju hdef_v)
  have hb6 := poly_and (poly_and (poly_and (poly_and
      (ComputableInPolyTime.unary_le' hn₁ hu) (ComputableInPolyTime.unary_lt' hu h2n₁))
      (ComputableInPolyTime.unary_le' h2n₁ hv))
      (ComputableInPolyTime.decide_eq' hbv
        (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hun)
          (.const 1))))
    (ComputableInPolyTime.unary_lt' hjv hdef_un)
  have hb7 := poly_and (poly_and (poly_and (poly_and
      (ComputableInPolyTime.unary_le' h2n₁ hu) (ComputableInPolyTime.unary_le' hn₁ hv))
      (ComputableInPolyTime.unary_lt' hv h2n₁))
      (ComputableInPolyTime.decide_eq' hbu
        (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hvn)
          (.const 1))))
    (ComputableInPolyTime.unary_lt' hju hdef_vn)
  exact (poly_and (poly_not (ComputableInPolyTime.decide_eq' hu hv))
    (poly_or (poly_or (poly_or (poly_or (poly_or (poly_or hb1 hb2) hb3) hb4) hb5) hb6)
      hb7)).of_enc_eq fun _ ↦
    congrArg encBool
      (by dsimp only [regAdjBool]; simp only [Bool.or_assoc, Bool.and_assoc, Function.comp_apply])

/-- **Polynomial-time and `FPT` degree-regularization reduction** from `Clique` to `RegularClique`
on `CliqueInstance`, increasing the target clique size from `x.m` to `x.m + 3`. -/
def cliqueToRegularClique (x : CliqueInstance) : CliqueInstance :=
  ⟨Graph.ofAdj (List.range (regCliqueNumVerts x)) (regAdjBool x), x.m + 3⟩

private def ofAdjRangeIso (x : CliqueInstance) :
    regCliqueFinGraph x ≃g (cliqueToRegularClique x).graph.induced where
  toEquiv :=
    { toFun := fun i ↦ ⟨i.1, by simp [cliqueToRegularClique, Graph.ofAdj, i.2]⟩
      invFun := fun v ↦ ⟨v.1, by simpa [cliqueToRegularClique, Graph.ofAdj] using v.2⟩
      left_inv := fun i ↦ Fin.ext rfl
      right_inv := fun v ↦ Subtype.ext rfl }
  map_rel_iff' := by
    intro i j
    simp only [Graph.induced_adj, cliqueToRegularClique, Graph.ofAdj_adj,
      List.length_range, List.getElem_range]
    constructor
    · intro ⟨hne, _, _, hor⟩
      rcases Bool.or_eq_true_iff.mp hor with h1 | h2
      · exact (regAdjBool_eq_true_iff x i j).mp h1
      · exact ((regAdjBool_eq_true_iff x j i).mp h2).symm
    · intro hadj
      exact ⟨Fin.val_ne_of_ne ((regCliqueFinGraph x).ne_of_adj hadj), i.2, j.2,
        Bool.or_eq_true_iff.mpr (Or.inl ((regAdjBool_eq_true_iff x i j).mpr hadj))⟩

/-- Every graph constructed by `cliqueToRegularClique x` is `regCliqueDeg x`-regular. -/
theorem cliqueToRegularClique_isRegular (x : CliqueInstance) :
    (cliqueToRegularClique x).graph.induced.IsRegularOfDegree (regCliqueDeg x) := by
  intro v
  let iso := ofAdjRangeIso x
  let _ := Classical.decRel (regCliqueFinGraph x).Adj
  have hdeg : (cliqueToRegularClique x).graph.induced.degree v =
      (regCliqueFinGraph x).degree (iso.symm v) := by
    rw [SimpleGraph.degree, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun w _ ↦ iso.symm w)
      (fun w hw ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        iso.symm.map_rel_iff.mpr (Finset.mem_filter.mp hw).2⟩)
      (fun _ _ _ _ h ↦ iso.symm.injective h)
      (fun u hu ↦ ⟨iso u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have hadj := iso.map_rel_iff.mpr (Finset.mem_filter.mp hu).2
        rwa [iso.apply_symm_apply] at hadj⟩, iso.symm_apply_apply u⟩)
  exact hdeg.trans (regCliqueFinGraph_isRegular x (iso.symm v))

/-- **Exact clique equivalence**: `x ∈ Clique` iff `cliqueToRegularClique x ∈ RegularClique`. -/
theorem cliqueToRegularClique_mem_iff (x : CliqueInstance) :
    x ∈ Clique ↔ cliqueToRegularClique x ∈ RegularClique := by
  let iso := ofAdjRangeIso x
  have hcl : (cliqueToRegularClique x) ∈ Clique ↔
      ∃ t : Finset (Fin (regCliqueNumVerts x)),
        (regCliqueFinGraph x).IsNClique (x.m + 3) t := by
    rw [Clique, Set.mem_ofPred_eq]
    have hm : (cliqueToRegularClique x).m = x.m + 3 := by unfold cliqueToRegularClique; rfl
    rw [hm]
    constructor
    · rintro ⟨S, hS, hcard⟩
      refine ⟨S.map iso.symm.toEquiv.toEmbedding, ?_, by rw [Finset.card_map, hcard]⟩
      intro a ha b hb hab
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
      exact iso.symm.map_rel_iff.mpr (hS hu hv fun h ↦ hab (congrArg iso.symm.toEquiv h))
    · rintro ⟨t, ht, hcard⟩
      refine ⟨t.map iso.toEquiv.toEmbedding, ?_, by rw [Finset.card_map, hcard]⟩
      intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      exact iso.map_rel_iff.mpr (ht ha hb fun h ↦ huv (congrArg iso.toEquiv h))
  change x ∈ Clique ↔
    (cliqueToRegularClique x ∈ Clique ∧
      ∃ d, (cliqueToRegularClique x).graph.induced.IsRegularOfDegree d)
  rw [hcl, regCliqueFinGraph_clique_iff]
  exact ⟨fun h ↦ ⟨h, regCliqueDeg x, cliqueToRegularClique_isRegular x⟩, fun h ↦ h.1⟩

/-- **`cliqueToRegularClique` is computable in polynomial time.** -/
@[fun_prop]
theorem computableInPolyTime_cliqueToRegularClique :
    ComputableInPolyTime cliqueToRegularClique encCliqueInstance encCliqueInstance := by
  unfold cliqueToRegularClique
  exact encCliqueInstance_mk_polyTime
    (Graph.computableInPolyTime_ofAdj (by fun_prop) computableInPolyTime_regAdjBool)
    (by fun_prop)

/-- **`Clique` reduces in polynomial time to `RegularClique`.** -/
theorem polyTimeReducible_Clique_RegularClique :
    PolyTimeReducible encCliqueInstance encCliqueInstance Clique RegularClique :=
  ⟨cliqueToRegularClique, computableInPolyTime_cliqueToRegularClique, cliqueToRegularClique_mem_iff⟩

/-- **`Clique` fpt-reduces to `RegularClique`** with parameter bound `m ↦ m + 3`. -/
theorem fptReducible_Clique_RegularClique :
    FPTReducible encCliqueInstance encCliqueInstance (·.m) (·.m) Clique RegularClique :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToRegularClique
    (h := fun k ↦ k + 3) (fun _ ↦ le_rfl) cliqueToRegularClique_mem_iff

/-- **`RegularClique` is `NP`-hard**. -/
theorem RegularClique_npHard : NPHard encCliqueInstance RegularClique :=
  Clique_npHard.trans polyTimeReducible_Clique_RegularClique

/-- **`RegularClique` is `W[1]`-hard** with respect to the clique size parameter `m`
.
-/
theorem RegularClique_wHard : WHard 1 encCliqueInstance (·.m) RegularClique :=
  Clique_wHard.trans fptReducible_Clique_RegularClique

end Cslib.Complexity
