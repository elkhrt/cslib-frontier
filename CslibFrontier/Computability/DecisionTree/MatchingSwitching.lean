module

public import CslibFrontier.Computability.DecisionTree.PartialMatching
public import Mathlib.Data.Finset.Sort

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Finite Matching Switching Lemma and Canonical Matching Decision Trees

This module formalizes canonical matching decision trees `canonTree`, the Beame--Impagliazzo--
Krajíček--Pitassi--Pudlák--Woods / Krajíček finite Matching Switching Lemma
(`card_matching_switching_le`), and simultaneous family switching
(`exists_extension_switching_family`) on top of
`CslibFrontier.Computability.DecisionTree.PartialMatching`.

## Main definitions

- `CslibFrontier.Computability.DecisionTree.edgeKey`,
  `CslibFrontier.Computability.DecisionTree.sortEdges`: canonical total ordering on
  `Sym2 U` for a linearly ordered vertex type `U`.
- `CslibFrontier.Computability.DecisionTree.queryVerts`,
  `CslibFrontier.Computability.DecisionTree.canonTreeAux`,
  `CslibFrontier.Computability.DecisionTree.canonTree`: the canonical matching decision tree of a
  matching DNF under a partial matching `ρ`.

## Main results

- `CslibFrontier.Computability.DecisionTree.canonTree_eval`: soundness of `canonTree F ρ` on every
  perfect matching extending `ρ`.
- `CslibFrontier.Computability.DecisionTree.card_matching_switching_le`: the finite Matching
  Switching Lemma bounding bad extensions `ρ ∈ ρ₀.extensions r'` of width-`k` matching DNFs.
- `CslibFrontier.Computability.DecisionTree.exists_extension_switching_family`: union-bound
  existence of a partial matching switching a finite family of width-`k` matching DNFs
  simultaneously.
-/

public section

namespace CslibFrontier.Computability.DecisionTree

open scoped BigOperators

universe u

/-! ### 4. Canonical Matching Decision Trees -/

section EdgeOrdering

variable {U : Type u} [LinearOrder U]

/-- Linear key `(min a b, max a b)` giving a canonical total ordering of edges in `Sym2 U`. -/
@[expose] def edgeKey (e : Sym2 U) : U × U :=
  Quot.lift (fun p : U × U ↦ (min p.1 p.2, max p.1 p.2))
    (fun _ _ h ↦ by
      cases h with
      | refl => rfl
      | swap => simp [min_comm, max_comm]) e

lemma edgeKey_injective : Function.Injective (edgeKey (U := U)) := by
  intro e₁ e₂ h
  induction e₁ using Sym2.ind with
  | _ a b =>
    induction e₂ using Sym2.ind with
    | _ c d =>
      simp only [edgeKey, Prod.mk.injEq] at h
      rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
      · rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at h
        rw [h.1, h.2]
      · rw [min_eq_left hab, max_eq_right hab, min_eq_right hcd, max_eq_left hcd] at h
        rw [h.1, h.2, Sym2.eq_swap]
      · rw [min_eq_right hab, max_eq_left hab, min_eq_left hcd, max_eq_right hcd] at h
        rw [h.1, h.2, Sym2.eq_swap]
      · rw [min_eq_right hab, max_eq_left hab, min_eq_right hcd, max_eq_left hcd] at h
        rw [h.1, h.2]

private lemma s_edgeKey (e : Sym2 U) : s((edgeKey e).1, (edgeKey e).2) = e := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases le_total a b with h | h
    · simp [edgeKey, min_eq_left h, max_eq_right h]
    · simp [edgeKey, min_eq_right h, max_eq_left h, Sym2.eq_swap]

private lemma mem_edgeKey_left (e : Sym2 U) : (edgeKey e).1 ∈ e := by
  have h : (edgeKey e).1 ∈ s((edgeKey e).1, (edgeKey e).2) := Sym2.mem_mk_left _ _
  rwa [s_edgeKey] at h

private lemma mem_edgeKey_right (e : Sym2 U) : (edgeKey e).2 ∈ e := by
  have h : (edgeKey e).2 ∈ s((edgeKey e).1, (edgeKey e).2) := Sym2.mem_mk_right _ _
  rwa [s_edgeKey] at h

/-- Lexicographic total order on `Sym2 U` induced by `edgeKey`. -/
private def edgeLe (e₁ e₂ : Sym2 U) : Prop :=
  (edgeKey e₁).1 < (edgeKey e₂).1 ∨
    ((edgeKey e₁).1 = (edgeKey e₂).1 ∧ (edgeKey e₁).2 ≤ (edgeKey e₂).2)

private local instance instDecidableRelEdgeLe : DecidableRel (edgeLe (U := U)) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

private local instance instIsTransEdgeLe : IsTrans (Sym2 U) edgeLe where
  trans a b c h₁ h₂ := by
    rcases h₁ with h₁ | ⟨h₁a, h₁b⟩ <;> rcases h₂ with h₂ | ⟨h₂a, h₂b⟩
    · exact Or.inl (lt_trans h₁ h₂)
    · exact Or.inl (h₂a ▸ h₁)
    · exact Or.inl (h₁a.symm ▸ h₂)
    · exact Or.inr ⟨h₁a.trans h₂a, le_trans h₁b h₂b⟩

private local instance instAntisymmEdgeLe : Std.Antisymm (edgeLe (U := U)) where
  antisymm a b h₁ h₂ := by
    apply edgeKey_injective
    apply Prod.ext
    · rcases h₁ with h₁ | ⟨h₁a, _⟩
      · rcases h₂ with h₂ | ⟨h₂a, _⟩
        · exact absurd h₁ (not_lt_of_gt h₂)
        · exact absurd h₁ (h₂a ▸ lt_irrefl _)
      · exact h₁a
    · rcases h₁ with h₁ | ⟨h₁a, h₁b⟩
      · rcases h₂ with h₂ | ⟨h₂a, _⟩
        · exact absurd h₁ (not_lt_of_gt h₂)
        · exact absurd h₁ (h₂a ▸ lt_irrefl _)
      · rcases h₂ with h₂ | ⟨_, h₂b⟩
        · exact absurd h₂ (h₁a ▸ lt_irrefl _)
        · exact le_antisymm h₁b h₂b

private local instance instTotalEdgeLe : Std.Total (edgeLe (U := U)) where
  total a b := by
    rcases lt_trichotomy (edgeKey a).1 (edgeKey b).1 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total (edgeKey a).2 (edgeKey b).2 with h2 | h2
      · exact Or.inl (Or.inr ⟨h, h2⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
    · exact Or.inr (Or.inl h)

/-- Canonical sorting of a finset of edges using `edgeKey`. -/
def sortEdges (E : Finset (Sym2 U)) : List (Sym2 U) :=
  E.sort edgeLe

@[simp] lemma mem_sortEdges {E : Finset (Sym2 U)} {e : Sym2 U} :
    e ∈ sortEdges E ↔ e ∈ E := by
  exact Finset.mem_sort _

@[simp] lemma length_sortEdges (E : Finset (Sym2 U)) :
    (sortEdges E).length = E.card := by
  exact Finset.length_sort _

@[simp] lemma sortEdges_nodup (E : Finset (Sym2 U)) : (sortEdges E).Nodup := by
  exact Finset.sort_nodup _ _

end EdgeOrdering

section CanonicalTree

private lemma exists_mem_sym2 {U : Type u} (e : Sym2 U) : ∃ x : U, x ∈ e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

variable {U : Type u} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- Queries a list of vertices `vs` against `ρ ∪ π`, extending `π` along every valid branch. -/
@[expose] def queryVerts (ρ : PMatching U) : List U → (π : PMatching U) →
    Disjoint ρ.support π.support →
    ((π' : PMatching U) → Disjoint ρ.support π'.support → MTree U) → MTree U
  | [], π, hπ, cont => cont π hπ
  | x :: xs, π, hπ, cont =>
      if hx : x ∈ (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).support then
        queryVerts ρ xs π hπ cont
      else
        .query x fun v ↦
          if hv : v ≠ x ∧ v ∉ ρ.support ∧ v ∉ π.support then
            have hxρ : x ∉ ρ.support := fun h ↦
              hx (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h)
            have hxπ : x ∉ π.support := fun h ↦
              hx (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h)
            let π' := π.addEdge x v hv.1.symm hxπ hv.2.2
            have hπ' : Disjoint ρ.support π'.support := by
              rw [PMatching.addEdge_support]
              exact Finset.disjoint_insert_right.mpr
                ⟨hxρ, Finset.disjoint_insert_right.mpr ⟨hv.2.1, hπ⟩⟩
            queryVerts ρ xs π' hπ' cont
          else
            .leaf false

/-- Fuel-indexed canonical matching decision tree recursion. -/
@[expose] def canonTreeAux : ℕ → MDNF U → (ρ π : PMatching U) →
    Disjoint ρ.support π.support → MTree U
  | fuel, F, ρ, π, hπ =>
      let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
      match F.find? (fun C ↦ decide (C.Compatible ρπ)) with
      | none => .leaf false
      | some C =>
          let D := C.sdiff ρπ
          if D.edges = ∅ then
            .leaf true
          else
            match fuel with
            | 0 => .leaf false
            | fuel' + 1 =>
                queryVerts ρ (D.support.sort (· ≤ ·)) π hπ
                  (fun π' hπ' ↦ canonTreeAux fuel' F ρ π' hπ')

/-- The canonical matching decision tree for matching DNF `F` under partial matching `ρ`. -/
@[expose] def canonTree (F : MDNF U) (ρ : PMatching U) : MTree U :=
  canonTreeAux (Fintype.card U) F ρ ⊥ (by simp)

omit [Fintype U] [LinearOrder U] in
@[simp] lemma queryVerts_nil (ρ π : PMatching U) (hπ : Disjoint ρ.support π.support)
    (cont : (π' : PMatching U) → Disjoint ρ.support π'.support → MTree U) :
    queryVerts ρ [] π hπ cont = cont π hπ := rfl

omit [Fintype U] [LinearOrder U] in
lemma queryVerts_cons (ρ : PMatching U) (x : U) (xs : List U) (π : PMatching U)
    (hπ : Disjoint ρ.support π.support)
    (cont : (π' : PMatching U) → Disjoint ρ.support π'.support → MTree U) :
    queryVerts ρ (x :: xs) π hπ cont =
      if hx : x ∈ (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).support then
        queryVerts ρ xs π hπ cont
      else
        .query x fun v ↦
          if hv : v ≠ x ∧ v ∉ ρ.support ∧ v ∉ π.support then
            have hxρ : x ∉ ρ.support := fun h ↦
              hx (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h)
            have hxπ : x ∉ π.support := fun h ↦
              hx (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h)
            let π' := π.addEdge x v hv.1.symm hxπ hv.2.2
            have hπ' : Disjoint ρ.support π'.support := by
              rw [PMatching.addEdge_support]
              exact Finset.disjoint_insert_right.mpr
                ⟨hxρ, Finset.disjoint_insert_right.mpr ⟨hv.2.1, hπ⟩⟩
            queryVerts ρ xs π' hπ' cont
          else
            .leaf false := rfl

omit [Fintype U] in
lemma canonTreeAux_zero (F : MDNF U) (ρ π : PMatching U) (hπ : Disjoint ρ.support π.support) :
    canonTreeAux 0 F ρ π hπ =
      let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
      match F.find? (fun C ↦ decide (C.Compatible ρπ)) with
      | none => .leaf false
      | some C => if (C.sdiff ρπ).edges = ∅ then .leaf true else .leaf false := by
  unfold canonTreeAux; rfl

omit [Fintype U] in
lemma canonTreeAux_succ (fuel' : ℕ) (F : MDNF U) (ρ π : PMatching U)
    (hπ : Disjoint ρ.support π.support) :
    canonTreeAux (fuel' + 1) F ρ π hπ =
      let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
      match F.find? (fun C ↦ decide (C.Compatible ρπ)) with
      | none => .leaf false
      | some C =>
          let D := C.sdiff ρπ
          if D.edges = ∅ then .leaf true
          else queryVerts ρ (D.support.sort (· ≤ ·)) π hπ
            (fun π' hπ' ↦ canonTreeAux fuel' F ρ π' hπ') := by
  conv_lhs => unfold canonTreeAux

omit [Fintype U] [LinearOrder U] in
private lemma compatible_of_find?_eq_some {F : MDNF U} {σ C : PMatching U}
    (h : F.find? (fun (C' : PMatching U) ↦ decide (C'.Compatible σ)) = some C) : C.Compatible σ :=
  of_decide_eq_true (List.find?_some (p := fun (C' : PMatching U) ↦ decide (C'.Compatible σ)) h)

omit [LinearOrder U] in
private lemma queryVerts_eval (ρ : PMatching U) (vs : List U) (π : PMatching U)
    (hπ : Disjoint ρ.support π.support)
    (cont : (π' : PMatching U) → Disjoint ρ.support π'.support → MTree U)
    {σ : PMatching U} (hρ : ρ ≤ σ) (hπσ : π ≤ σ) (hσ : σ.IsPerfect) :
    ∃ (π' : PMatching U) (hπ' : Disjoint ρ.support π'.support),
      π ≤ π' ∧ π' ≤ σ ∧ (∀ x ∈ vs, x ∈ (ρ.union π'
        (PMatching.compatible_of_disjoint_support hπ')).support) ∧
      (queryVerts ρ vs π hπ cont).eval σ = (cont π' hπ').eval σ := by
  induction vs generalizing π with
  | nil =>
    exact ⟨π, hπ, le_rfl, hπσ, (fun _ h ↦ nomatch h), rfl⟩
  | cons x xs ih =>
    simp only [queryVerts]
    split_ifs with hx
    · rcases ih π hπ hπσ with ⟨π', hπ', hle, hleσ, hall, hev⟩
      refine ⟨π', hπ', hle, hleσ, fun y hy ↦ ?_, hev⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · rw [PMatching.union_support] at hx ⊢
        rcases Finset.mem_union.mp hx with h1 | h2
        · exact Finset.mem_union_left _ h1
        · exact Finset.mem_union_right _ (PMatching.support_mono hle h2)
      · exact hall y hy'
    · obtain ⟨v, hv⟩ := PMatching.exists_partner_of_isPerfect hσ x
      have hsv : s(x, v) ∈ σ.edges := PMatching.partner_eq_some_iff.mp hv
      have hvx : v ≠ x := PMatching.partner_ne_self hv
      have hxρ : x ∉ ρ.support := fun h ↦
        hx (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h)
      have hxπ : x ∉ π.support := fun h ↦
        hx (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h)
      have hvρ : v ∉ ρ.support := by
        intro hsup
        rcases PMatching.mem_support_iff.mp hsup with ⟨e, he, hve⟩
        have hne : e ≠ s(x, v) := fun heq ↦
          hxρ (PMatching.mem_support_iff.mpr ⟨e, he, heq ▸ Sym2.mem_mk_left x v⟩)
        exact σ.disjoint e (hρ he) s(x, v) hsv hne v hve (Sym2.mem_mk_right x v)
      have hvπ : v ∉ π.support := by
        intro hsup
        rcases PMatching.mem_support_iff.mp hsup with ⟨e, he, hve⟩
        have hne : e ≠ s(x, v) := fun heq ↦
          hxπ (PMatching.mem_support_iff.mpr ⟨e, he, heq ▸ Sym2.mem_mk_left x v⟩)
        exact σ.disjoint e (hπσ he) s(x, v) hsv hne v hve (Sym2.mem_mk_right x v)
      have hcond : v ≠ x ∧ v ∉ ρ.support ∧ v ∉ π.support := ⟨hvx, hvρ, hvπ⟩
      let π₁ := π.addEdge x v hvx.symm hxπ hvπ
      have hπ₁ : Disjoint ρ.support π₁.support := by
        rw [PMatching.addEdge_support]
        exact Finset.disjoint_insert_right.mpr
          ⟨hxρ, Finset.disjoint_insert_right.mpr ⟨hvρ, hπ⟩⟩
      have hπ₁σ : π₁ ≤ σ := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact hsv
        · exact hπσ he'
      rcases ih π₁ hπ₁ hπ₁σ with ⟨π', hπ', hle₁, hleσ, hall, hev⟩
      refine ⟨π', hπ', le_trans (PMatching.le_addEdge _ _ _ _ _ _) hle₁, hleσ, fun y hy ↦ ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rw [PMatching.union_support]
          refine Finset.mem_union_right _ (PMatching.support_mono hle₁ ?_)
          rw [PMatching.addEdge_support]
          exact Finset.mem_insert_self _ _
        · exact hall y hy'
      · simp only [MTree.eval_query, hv]
        split_ifs
        exact hev

private lemma canonTreeAux_eval (fuel : ℕ) (F : MDNF U) (ρ π : PMatching U)
    (hπ : Disjoint ρ.support π.support) {σ : PMatching U}
    (hρ : ρ ≤ σ) (hπσ : π ≤ σ) (hσ : σ.IsPerfect)
    (hfuel : (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).free.card ≤ fuel) :
    (canonTreeAux fuel F ρ π hπ).eval σ = F.eval σ := by
  induction fuel generalizing π with
  | zero =>
    unfold canonTreeAux
    dsimp only
    let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
    have hρπ_le : ρπ ≤ σ := fun e he ↦ (Finset.mem_union.mp he).elim (fun h ↦ hρ h) (fun h ↦ hπσ h)
    have hfree0 : ρπ.free = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
    have hρπ_eq : ρπ = σ := by
      ext e
      refine ⟨fun h ↦ hρπ_le h, fun he ↦ ?_⟩
      induction e using Sym2.ind with
      | _ x y =>
        have hx : x ∈ ρπ.support := by
          have := PMatching.mem_free_iff (ρ := ρπ) (x := x)
          rw [hfree0] at this; exact Classical.not_not.mp (by simpa using this)
        rcases PMatching.mem_support_iff.mp hx with ⟨e', he', hxe'⟩
        by_contra hne
        have hne' : e' ≠ s(x, y) := fun heq ↦ hne (heq ▸ he')
        exact σ.disjoint e' (hρπ_le he') s(x, y) he hne' x hxe' (Sym2.mem_mk_left x y)
    cases hfind : F.find? (fun C ↦ decide (C.Compatible ρπ)) with
    | none =>
      symm
      rw [MTree.eval_leaf, Bool.eq_false_iff, ne_eq, MDNF.eval_eq_true_iff]
      rintro ⟨C, hC, hCσ⟩
      have hcomp : C.Compatible ρπ := hρπ_eq ▸ PMatching.compatible_of_le hCσ
      have hnot := List.find?_eq_none.mp hfind C hC
      simp [hcomp] at hnot
    | some C =>
      have hmem : C ∈ F := List.mem_of_find?_eq_some hfind
      have hcomp : C.Compatible ρπ := compatible_of_find?_eq_some hfind
      have hD0 : (C.sdiff ρπ).edges = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        have he' := Finset.mem_sdiff.mp he
        obtain ⟨x, hx⟩ := exists_mem_sym2 e
        have hxsup : x ∈ ρπ.support := by
          have := PMatching.mem_free_iff (ρ := ρπ) (x := x)
          rw [hfree0] at this; exact Classical.not_not.mp (by simpa using this)
        rcases PMatching.mem_support_iff.mp hxsup with ⟨e', he'', hxe'⟩
        have hne : e ≠ e' := fun heq ↦ he'.2 (heq ▸ he'')
        exact hcomp e he'.1 e' he'' hne x hx hxe'
      dsimp only
      split_ifs with hD0'
      · symm
        rw [MTree.eval_leaf, MDNF.eval_eq_true_iff]
        refine ⟨C, hmem, fun e he ↦ hρπ_le ?_⟩
        by_contra hnot
        have : e ∈ (C.sdiff ρπ).edges := Finset.mem_sdiff.mpr ⟨he, hnot⟩
        rw [hD0] at this
        exact Finset.notMem_empty _ this
      · exact absurd hD0 hD0'
  | succ fuel' ih =>
    unfold canonTreeAux
    dsimp only
    let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
    have hρπ_le : ρπ ≤ σ := fun e he ↦ (Finset.mem_union.mp he).elim (fun h ↦ hρ h) (fun h ↦ hπσ h)
    cases hfind : F.find? (fun C ↦ decide (C.Compatible ρπ)) with
    | none =>
      symm
      rw [MTree.eval_leaf, Bool.eq_false_iff, ne_eq, MDNF.eval_eq_true_iff]
      rintro ⟨C, hC, hCσ⟩
      have hcomp : C.Compatible ρπ :=
        PMatching.compatible_mono_right (PMatching.compatible_of_le hCσ) hρπ_le
      have hnot := List.find?_eq_none.mp hfind C hC
      simp [hcomp] at hnot
    | some C =>
      have hmem : C ∈ F := List.mem_of_find?_eq_some hfind
      have hcomp : C.Compatible ρπ := compatible_of_find?_eq_some hfind
      dsimp only
      split_ifs with hD0
      · symm
        rw [MTree.eval_leaf, MDNF.eval_eq_true_iff]
        refine ⟨C, hmem, fun e he ↦ hρπ_le ?_⟩
        by_contra hnot
        have : e ∈ (C.sdiff ρπ).edges := Finset.mem_sdiff.mpr ⟨he, hnot⟩
        rw [hD0] at this
        exact Finset.notMem_empty _ this
      · rcases queryVerts_eval ρ ((C.sdiff ρπ).support.sort (· ≤ ·)) π hπ
            (fun π' hπ' ↦ canonTreeAux fuel' F ρ π' hπ') hρ hπσ hσ
          with ⟨π', hπ', hle, hleσ, hall, hev⟩
        rw [hev]
        refine ih π' hπ' hleσ ?_
        -- `π'` matches at least one vertex of `D.support`, which was free in `ρπ`!
        obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hD0
        obtain ⟨x, hx⟩ := exists_mem_sym2 e
        have hxD : x ∈ (C.sdiff ρπ).support := PMatching.mem_support_iff.mpr ⟨e, he, hx⟩
        have hx_nρπ : x ∉ ρπ.support := by
          intro hsup
          rcases PMatching.mem_support_iff.mp hsup with ⟨e', he', hxe'⟩
          have he_s := Finset.mem_sdiff.mp he
          have hne : e ≠ e' := fun heq ↦ he_s.2 (heq ▸ he')
          exact hcomp e he_s.1 e' he' hne x hx hxe'
        have hx_in : x ∈ (ρ.union π' (PMatching.compatible_of_disjoint_support hπ')).support :=
          hall x ((Finset.mem_sort _).mpr hxD)
        have hsub : ρπ.support ⊂
            (ρ.union π' (PMatching.compatible_of_disjoint_support hπ')).support := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun heq ↦ hx_nρπ (heq ▸ hx_in)⟩
          rw [PMatching.union_support, PMatching.union_support]
          exact Finset.union_subset_union_right (PMatching.support_mono hle)
        have hfree_lt :
            (ρ.union π' (PMatching.compatible_of_disjoint_support hπ')).free.card <
              ρπ.free.card := by
          have h1 := ρπ.card_free_add
          have h2 := (ρ.union π' (PMatching.compatible_of_disjoint_support hπ')).card_free_add
          have h3 := ρπ.card_support
          have h4 := (ρ.union π' (PMatching.compatible_of_disjoint_support hπ')).card_support
          have hlt := Finset.card_lt_card hsub
          omega
        change ρπ.free.card ≤ fuel' + 1 at hfuel
        omega

/-- Soundness of `canonTree F ρ` on every perfect matching extending `ρ`. -/
theorem canonTree_eval (F : MDNF U) (ρ σ : PMatching U) (hρ : ρ ≤ σ) (hσ : σ.IsPerfect) :
    (canonTree F ρ).eval σ = F.eval σ := by
  refine canonTreeAux_eval (Fintype.card U) F ρ ⊥ (by simp) hρ (Finset.empty_subset _) hσ ?_
  have := (ρ.union ⊥ (PMatching.compatible_of_disjoint_support (by simp))).card_free_add
  omega

/-! ### 5. Stage-Trace Extraction and Encoder/Decoder Proof of the Switching Lemma -/

omit [Fintype U] [LinearOrder U] in
private lemma disjoint_support_sdiff_of_compatible {ρ σ : PMatching U} (h : ρ.Compatible σ) :
    Disjoint σ.support (ρ.sdiff σ).support := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rcases PMatching.mem_support_iff.mp hx₁ with ⟨e₁, he₁, hxe₁⟩
  rcases PMatching.mem_support_iff.mp hx₂ with ⟨e₂, he₂, hxe₂⟩
  have he₂' := Finset.mem_sdiff.mp he₂
  have hne : e₂ ≠ e₁ := fun heq ↦ he₂'.2 (heq ▸ he₁)
  exact h e₂ he₂'.1 e₁ he₁ hne x hxe₂ hxe₁

omit [Fintype U] [LinearOrder U] in
private lemma find?_compatible_of_le {F : MDNF U} {σ₁ σ₂ C : PMatching U}
    (hfind : F.find? (fun C' ↦ decide (C'.Compatible σ₁)) = some C)
    (hle : σ₁ ≤ σ₂) (hcomp : C.Compatible σ₂) :
    F.find? (fun C' ↦ decide (C'.Compatible σ₂)) = some C := by
  induction F with
  | nil => simp at hfind
  | cons C₀ Fs ih =>
    simp only [List.find?_cons] at hfind ⊢
    cases h0 : decide (C₀.Compatible σ₁)
    · rw [h0] at hfind
      have hnot : decide (C₀.Compatible σ₂) = false := by
        rw [decide_eq_false_iff_not]
        intro hc2
        have hc1 := PMatching.compatible_mono_right hc2 hle
        simp [hc1] at h0
      rw [hnot]
      exact ih hfind
    · rw [h0] at hfind
      have hEq : C₀ = C := Option.some.inj hfind
      subst hEq
      simp [hcomp]

/-- A forward stage trace extracted from a deep branch of `canonTreeAux`. -/
private inductive DeepTrace (F : MDNF U) (ρ : PMatching U) :
    (π : PMatching U) → Disjoint ρ.support π.support → Type u
  | last (π : PMatching U) (hπ : Disjoint ρ.support π.support) (C D_part : PMatching U)
      (hfind : F.find? (fun C' ↦ decide (C'.Compatible
        (ρ.union π (PMatching.compatible_of_disjoint_support hπ)))) = some C)
      (hDle : D_part ≤ C.sdiff (ρ.union π (PMatching.compatible_of_disjoint_support hπ)))
      (hDne : D_part.edges.Nonempty) :
      DeepTrace F ρ π hπ
  | step (π : PMatching U) (hπ : Disjoint ρ.support π.support) (C D B : PMatching U)
      (hfind : F.find? (fun C' ↦ decide (C'.Compatible
        (ρ.union π (PMatching.compatible_of_disjoint_support hπ)))) = some C)
      (hDeq : D = C.sdiff (ρ.union π (PMatching.compatible_of_disjoint_support hπ)))
      (hDne : D.edges.Nonempty)
      (hBdisj : Disjoint (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).support
        B.support)
      (hBhit : ∀ e ∈ B.edges, ∃ x ∈ D.support, x ∈ e)
      (hDsubB : D.support ⊆ B.support)
      (hπB : Disjoint ρ.support (π.union B (PMatching.compatible_of_disjoint_support
        (Finset.disjoint_of_subset_left
          (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj))).support)
      (rest : DeepTrace F ρ
        (π.union B (PMatching.compatible_of_disjoint_support
          (Finset.disjoint_of_subset_left
            (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj))) hπB) :
      DeepTrace F ρ π hπ

private def DeepTrace.totalEdges {F : MDNF U} {ρ π : PMatching U}
    {hπ : Disjoint ρ.support π.support} : DeepTrace F ρ π hπ → ℕ
  | .last _ _ _ D_part _ _ _ => D_part.edges.card
  | .step _ _ _ D _ _ _ _ _ _ _ _ rest => D.edges.card + rest.totalEdges

private def DeepTrace.futureData {F : MDNF U} {ρ π : PMatching U}
    {hπ : Disjoint ρ.support π.support} :
    (tr : DeepTrace F ρ π hπ) →
    { Dtot : PMatching U //
        Disjoint (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).support Dtot.support ∧
        Dtot.edges.card = tr.totalEdges }
  | .last π hπ C D_part hfind hDle _ =>
      let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
      have hcomp : C.Compatible ρπ := compatible_of_find?_eq_some hfind
      have hdisj : Disjoint ρπ.support D_part.support :=
        Finset.disjoint_of_subset_right (PMatching.support_mono hDle)
          (disjoint_support_sdiff_of_compatible hcomp)
      ⟨D_part, hdisj, rfl⟩
  | .step π hπ C D B hfind hDeq _ hBdisj _ hDsubB hπB rest =>
      let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
      let πB := π.union B (PMatching.compatible_of_disjoint_support
        (Finset.disjoint_of_subset_left
          (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj))
      let ρπB := ρ.union πB (PMatching.compatible_of_disjoint_support hπB)
      have hcomp : C.Compatible ρπ := compatible_of_find?_eq_some hfind
      have hDdisj : Disjoint ρπ.support D.support := by
        rw [hDeq]; exact disjoint_support_sdiff_of_compatible hcomp
      let ⟨Drest, hRestDisj, hRestCard⟩ := rest.futureData
      have hρπB_sup : ρπB.support = ρπ.support ∪ B.support := by
        simp only [ρπB, ρπ, πB, PMatching.union_support, Finset.union_assoc]
      have hDRestDisj : Disjoint D.support Drest.support :=
        Finset.disjoint_of_subset_left
          (hDsubB.trans (by rw [hρπB_sup]; exact Finset.subset_union_right)) hRestDisj
      have hρπRestDisj : Disjoint ρπ.support Drest.support :=
        Finset.disjoint_of_subset_left
          (by rw [hρπB_sup]; exact Finset.subset_union_left) hRestDisj
      let Dtot := D.union Drest (PMatching.compatible_of_disjoint_support hDRestDisj)
      have htotDisj : Disjoint ρπ.support Dtot.support := by
        have hDsup : Dtot.support = D.support ∪ Drest.support := PMatching.union_support _ _ _
        rw [hDsup]
        exact Finset.disjoint_union_right.mpr ⟨hDdisj, hρπRestDisj⟩
      have htotCard : Dtot.edges.card = D.edges.card + rest.totalEdges := by
        rw [PMatching.union_edges, Finset.card_union_of_disjoint, hRestCard]
        rw [Finset.disjoint_left]
        intro e he₁ he₂
        obtain ⟨x, hx⟩ := exists_mem_sym2 e
        exact Finset.disjoint_left.mp hDRestDisj
          (PMatching.mem_support_iff.mpr ⟨e, he₁, hx⟩)
          (PMatching.mem_support_iff.mpr ⟨e, he₂, hx⟩)
      ⟨Dtot, htotDisj, htotCard⟩

omit [LinearOrder U] in
private lemma queryVerts_depth_ge (ρ : PMatching U) (vs : List U) (π : PMatching U)
    (hπ : Disjoint ρ.support π.support)
    (cont : (π' : PMatching U) → Disjoint ρ.support π'.support → MTree U)
    {d : ℕ} (hvd : vs.length < d) (hd : d ≤ (queryVerts ρ vs π hπ cont).depth) :
    ∃ (B : PMatching U)
      (hBdisj : Disjoint (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).support
        B.support)
      (hπB : Disjoint ρ.support (π.union B (PMatching.compatible_of_disjoint_support
        (Finset.disjoint_of_subset_left
          (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj))).support),
      (∀ e ∈ B.edges, ∃ x ∈ vs, x ∈ e) ∧
      (∀ x ∈ vs, x ∈ (ρ.union (π.union B (PMatching.compatible_of_disjoint_support
        (Finset.disjoint_of_subset_left
          (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj)))
        (PMatching.compatible_of_disjoint_support hπB)).support) ∧
      d ≤ vs.length + (cont _ hπB).depth := by
  induction vs generalizing π d with
  | nil =>
    have hEq : π.union ⊥ (PMatching.compatible_of_disjoint_support (by simp)) = π := by
      ext e; simp [PMatching.union_edges]
    refine ⟨⊥, by simp, by rw [hEq]; exact hπ, (fun _ h ↦ (Finset.notMem_empty _ h).elim),
      (fun _ h ↦ nomatch h), ?_⟩
    simpa [queryVerts, hEq] using hd
  | cons x xs ih =>
    simp only [queryVerts] at hd
    split_ifs at hd with hx
    · rcases ih π hπ (by simp only [List.length_cons] at hvd; omega) hd
        with ⟨B, hBdisj, hπB, hBhit, hxs, hdep⟩
      refine ⟨B, hBdisj, hπB, fun e he ↦ ?_, fun y hy ↦ ?_, by simp only [List.length_cons]; omega⟩
      · rcases hBhit e he with ⟨y, hy, hye⟩
        exact ⟨y, List.mem_cons_of_mem x hy, hye⟩
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rw [PMatching.union_support] at hx ⊢
          rcases Finset.mem_union.mp hx with h1 | h2
          · exact Finset.mem_union_left _ h1
          · exact Finset.mem_union_right _
              (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h2)
        · exact hxs y hy'
    · rw [MTree.depth_query] at hd
      have hsup_pos : ∃ v : U, d ≤ 1 + (if hv : v ≠ x ∧ v ∉ ρ.support ∧ v ∉ π.support then
          (queryVerts ρ xs
            (π.addEdge x v hv.1.symm
              (fun h ↦ hx (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h))
              hv.2.2)
            (by
              rw [PMatching.addEdge_support]
              exact Finset.disjoint_insert_right.mpr
                ⟨fun h ↦ hx (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h),
                  Finset.disjoint_insert_right.mpr ⟨hv.2.1, hπ⟩⟩)
            cont).depth else 0) := by
        obtain ⟨v, _, hvmax⟩ := Finset.exists_mem_eq_sup Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨x⟩)
          (fun v : U ↦
            (if hv : v ≠ x ∧ v ∉ ρ.support ∧ v ∉ π.support then
              queryVerts ρ xs (π.addEdge x v hv.1.symm
                (fun h ↦ hx (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h))
                hv.2.2)
                (by
                  rw [PMatching.addEdge_support]
                  exact Finset.disjoint_insert_right.mpr
                    ⟨fun h ↦ hx (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h),
                      Finset.disjoint_insert_right.mpr ⟨hv.2.1, hπ⟩⟩) cont
            else .leaf false).depth)
        refine ⟨v, ?_⟩
        rw [hvmax] at hd
        split_ifs at hd ⊢
        · exact hd
        · simp only [MTree.depth_leaf] at hd; exact hd
      rcases hsup_pos with ⟨v, hv_d⟩
      by_cases hv : v ≠ x ∧ v ∉ ρ.support ∧ v ∉ π.support
      · split_ifs at hv_d
        have hxρ : x ∉ ρ.support := fun h ↦
          hx (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h)
        have hxπ : x ∉ π.support := fun h ↦
          hx (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h)
        let π₁ := π.addEdge x v hv.1.symm hxπ hv.2.2
        have hπ₁ : Disjoint ρ.support π₁.support := by
          rw [PMatching.addEdge_support]
          exact Finset.disjoint_insert_right.mpr
            ⟨hxρ, Finset.disjoint_insert_right.mpr ⟨hv.2.1, hπ⟩⟩
        have hvd' : xs.length < d - 1 := by simp only [List.length_cons] at hvd; omega
        rcases ih π₁ hπ₁ hvd' (by change d ≤ 1 + (queryVerts ρ xs π₁ hπ₁ cont).depth at hv_d; omega)
          with ⟨B₁, hB₁disj, hπ₁B₁, hB₁hit, hxs, hdep⟩
        have hB₁_disj_xv : x ∉ B₁.support ∧ v ∉ B₁.support := by
          have h1 : x ∈ (ρ.union π₁ (PMatching.compatible_of_disjoint_support hπ₁)).support := by
            rw [PMatching.union_support, PMatching.addEdge_support]
            exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          have h2 : v ∈ (ρ.union π₁ (PMatching.compatible_of_disjoint_support hπ₁)).support := by
            rw [PMatching.union_support, PMatching.addEdge_support]
            exact Finset.mem_union_right _
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          exact ⟨Finset.disjoint_left.mp hB₁disj h1, Finset.disjoint_left.mp hB₁disj h2⟩
        let B := B₁.addEdge x v hv.1.symm hB₁_disj_xv.1 hB₁_disj_xv.2
        have hBdisj : Disjoint (ρ.union π (PMatching.compatible_of_disjoint_support hπ)).support
            B.support := by
          rw [PMatching.addEdge_support]
          refine Finset.disjoint_insert_right.mpr ⟨hx, Finset.disjoint_insert_right.mpr ⟨?_, ?_⟩⟩
          · rw [PMatching.union_support]
            exact fun hm ↦ (Finset.mem_union.mp hm).elim hv.2.1 hv.2.2
          · refine Finset.disjoint_of_subset_left ?_ hB₁disj
            rw [PMatching.union_support, PMatching.union_support]
            exact Finset.union_subset_union_right
              (PMatching.support_mono (PMatching.le_addEdge _ _ _ _ _ _))
        have hπB_eq : π.union B (PMatching.compatible_of_disjoint_support
            (Finset.disjoint_of_subset_left
              (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj)) =
            π₁.union B₁ (PMatching.compatible_of_disjoint_support
              (Finset.disjoint_of_subset_left
                (by rw [PMatching.union_support]; exact Finset.subset_union_right) hB₁disj)) := by
          ext e
          simp only [B, π₁, PMatching.union_edges, PMatching.addEdge_edges, Finset.mem_union,
            Finset.mem_insert]
          tauto
        have hπB : Disjoint ρ.support (π.union B (PMatching.compatible_of_disjoint_support
            (Finset.disjoint_of_subset_left
              (by rw [PMatching.union_support]; exact Finset.subset_union_right)
              hBdisj))).support := by
          rw [hπB_eq]; exact hπ₁B₁
        refine ⟨B, hBdisj, hπB, fun e he ↦ ?_, fun y hy ↦ ?_, ?_⟩
        · rcases Finset.mem_insert.mp he with rfl | he'
          · exact ⟨x, List.mem_cons_self, Sym2.mem_mk_left x v⟩
          · rcases hB₁hit e he' with ⟨y, hy, hye⟩
            exact ⟨y, List.mem_cons_of_mem x hy, hye⟩
        · rcases List.mem_cons.mp hy with rfl | hy'
          · rw [PMatching.union_support, PMatching.union_support, PMatching.addEdge_support]
            exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
          · simpa only [hπB_eq] using hxs y hy'
        · have hcont_eq : (cont _ hπB).depth = (cont _ hπ₁B₁).depth := by
            congr 1
            have hsub : (⟨_, hπB⟩ : { q : PMatching U // Disjoint ρ.support q.support }) =
                ⟨_, hπ₁B₁⟩ := Subtype.ext hπB_eq
            exact congrArg (fun p : { q : PMatching U // Disjoint ρ.support q.support } ↦
              cont p.1 p.2) hsub
          rw [hcont_eq, List.length_cons]
          omega
      · simp only [hv, ↓reduceDIte] at hv_d
        simp only [List.length_cons] at hvd
        omega

private lemma exists_deepTrace_of_depth (fuel : ℕ) (F : MDNF U) (ρ π : PMatching U)
    (hπ : Disjoint ρ.support π.support) {s : ℕ} (hs : 1 ≤ s)
    (hdepth : 2 * s ≤ (canonTreeAux fuel F ρ π hπ).depth) :
    ∃ tr : DeepTrace F ρ π hπ, tr.totalEdges = s := by
  induction fuel generalizing π s with
  | zero =>
    unfold canonTreeAux at hdepth
    dsimp only at hdepth
    cases hfind : F.find? (fun C ↦ decide (C.Compatible
        (ρ.union π (PMatching.compatible_of_disjoint_support hπ)))) with
    | none => rw [hfind] at hdepth; simp [MTree.depth_leaf] at hdepth; omega
    | some C =>
      rw [hfind] at hdepth
      dsimp only at hdepth
      split_ifs at hdepth <;> simp [MTree.depth_leaf] at hdepth <;> omega
  | succ fuel' ih =>
    unfold canonTreeAux at hdepth
    dsimp only at hdepth
    let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
    cases hfind : F.find? (fun C ↦ decide (C.Compatible ρπ)) with
    | none => rw [hfind] at hdepth; simp [MTree.depth_leaf] at hdepth; omega
    | some C =>
      rw [hfind] at hdepth
      dsimp only at hdepth
      split_ifs at hdepth with hD0
      · simp [MTree.depth_leaf] at hdepth; omega
      · let D := C.sdiff ρπ
        have hDne : D.edges.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD0
        by_cases hDs : s ≤ D.edges.card
        · let D_part : PMatching U :=
            ⟨((sortEdges D.edges).take s).toFinset,
              fun e he ↦ D.nonDiag e
                (mem_sortEdges.mp (List.mem_of_mem_take (List.mem_toFinset.mp he))),
              fun e₁ he₁ e₂ he₂ ↦
                D.disjoint e₁
                  (mem_sortEdges.mp (List.mem_of_mem_take (List.mem_toFinset.mp he₁)))
                  e₂ (mem_sortEdges.mp (List.mem_of_mem_take (List.mem_toFinset.mp he₂)))⟩
          have hDle : D_part ≤ D := fun e he ↦
            mem_sortEdges.mp (List.mem_of_mem_take (List.mem_toFinset.mp he))
          have hDcard : D_part.edges.card = s := by
            have hnodup : ((sortEdges D.edges).take s).Nodup :=
              (sortEdges_nodup D.edges).sublist (List.take_sublist s _)
            rw [List.toFinset_card_of_nodup hnodup, List.length_take, length_sortEdges,
              Nat.min_eq_left hDs]
          have hDpart_ne : D_part.edges.Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨.last π hπ C D_part hfind hDle hDpart_ne, hDcard⟩
        · push Not at hDs
          have hlen : (D.support.sort (· ≤ ·)).length = 2 * D.edges.card := by
            rw [Finset.length_sort, D.card_support]
          have hvd : (D.support.sort (· ≤ ·)).length < 2 * s := by omega
          rcases queryVerts_depth_ge ρ (D.support.sort (· ≤ ·)) π hπ
              (fun π' hπ' ↦ canonTreeAux fuel' F ρ π' hπ') hvd hdepth
            with ⟨B, hBdisj, hπB, hBhit, hDcov, hdep⟩
          rw [hlen] at hdep
          have hs' : 1 ≤ s - D.edges.card := by omega
          have hdep' : 2 * (s - D.edges.card) ≤ (canonTreeAux fuel' F ρ _ hπB).depth := by omega
          rcases ih _ hπB hs' hdep' with ⟨rest, hrest⟩
          have hBhit' : ∀ e ∈ B.edges, ∃ x ∈ D.support, x ∈ e := fun e he ↦ by
            rcases hBhit e he with ⟨x, hx, hxe⟩
            exact ⟨x, (Finset.mem_sort _).mp hx, hxe⟩
          have hDsubB : D.support ⊆ B.support := by
            intro x hx
            have hcomp : C.Compatible ρπ := compatible_of_find?_eq_some hfind
            have hx_nρπ : x ∉ ρπ.support :=
              Finset.disjoint_right.mp (disjoint_support_sdiff_of_compatible hcomp) hx
            have hxin := hDcov x ((Finset.mem_sort _).mpr hx)
            rw [PMatching.union_support, PMatching.union_support] at hxin
            rcases Finset.mem_union.mp hxin with h1 | h2
            · exact absurd (by rw [PMatching.union_support]; exact Finset.mem_union_left _ h1)
                hx_nρπ
            · rcases Finset.mem_union.mp h2 with h2a | h2b
              · exact absurd (by rw [PMatching.union_support]; exact Finset.mem_union_right _ h2a)
                  hx_nρπ
              · exact h2b
          refine ⟨.step π hπ C D B hfind rfl hDne hBdisj hBhit' hDsubB hπB rest, ?_⟩
          simp only [DeepTrace.totalEdges, hrest]
          omega

/-- Hint entry type for one edge of a stage in the Switching Lemma encoding. -/
private abbrev HintEntry (k r' : ℕ) := Fin k × Bool × Fin r' × Fin r'

/-- Splits a hint list at the first entry with `isLast = true` (inclusive). -/
private def splitChunk {k r' : ℕ} :
    List (HintEntry k r') → List (HintEntry k r') × List (HintEntry k r')
  | [] => ([], [])
  | h :: hs =>
      if h.2.1 then ([h], hs)
      else
        let p := splitChunk hs
        (h :: p.1, p.2)

private lemma splitChunk_append {k r' : ℕ} (chunk rest : List (HintEntry k r'))
    (hne : chunk ≠ [])
    (hlast : ∀ i (hi : i < chunk.length), (chunk[i]'hi).2.1 = decide (i + 1 = chunk.length)) :
    splitChunk (chunk ++ rest) = (chunk, rest) := by
  induction chunk with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
    cases as with
    | nil =>
      have ha : a.2.1 = true := by simpa using hlast 0 (by simp)
      simp [splitChunk, ha]
    | cons b bs =>
      have ha : a.2.1 = false := by
        have h0 := hlast 0 (by simp)
        simpa using h0
      have hlast' : ∀ i (hi : i < (b :: bs).length),
          ((b :: bs)[i]'hi).2.1 = decide (i + 1 = (b :: bs).length) := by
        intro i hi
        have := hlast (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa using this
      have hih := ih (by simp) hlast'
      dsimp only [List.cons_append]
      unfold splitChunk
      simp only [ha, Bool.false_eq_true, ↓reduceIte]
      rw [← List.cons_append, hih]

/-- Builds a `PMatching U` from a finset of edges if it is valid (non-diagonal & disjoint). -/
private def mkPMatching? (E : Finset (Sym2 U)) : Option (PMatching U) :=
  if h : (∀ e ∈ E, ¬ e.IsDiag) ∧
      (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) then
    some ⟨E, h.1, h.2⟩
  else
    none

/-- Reconstructs `ρ` from `(τ, π, hint)` in the Matching Switching Lemma proof. -/
private def decodeAux (F : MDNF U) (k r' : ℕ) :
    ℕ → PMatching U → PMatching U → List (HintEntry k r') → Option (PMatching U)
  | 0, _, _, _ => none
  | fuel + 1, τ, π, hint =>
      match hint with
      | [] => none
      | _ :: _ =>
        match F.find? (fun C ↦ decide (C.Compatible τ)) with
        | none => none
        | some C =>
          let (chunk, rest) := splitChunk hint
          let cList := sortEdges C.edges
          let dEdges : Finset (Sym2 U) :=
            (chunk.filterMap fun h ↦ cList[h.1.val]?).toFinset
          match mkPMatching? dEdges with
          | none => none
          | some D_part =>
            let τ_mid := τ.sdiff D_part
            match rest with
            | [] => some (τ_mid.sdiff π)
            | _ :: _ =>
              let freeList := τ_mid.free.sort (· ≤ ·)
              let bEdges : Finset (Sym2 U) :=
                (chunk.flatMap fun h ↦
                  match cList[h.1.val]?, freeList[h.2.2.1.val]?, freeList[h.2.2.2.val]? with
                  | some e, some u, some v =>
                      let p := edgeKey e
                      [s(p.1, u), s(p.2, v)]
                  | _, _, _ => []).toFinset
              match mkPMatching? bEdges with
              | none => none
              | some B =>
                if hdisj : Disjoint τ_mid.support B.support then
                  if hcompπ : π.Compatible B then
                    decodeAux F k r' fuel
                      (τ_mid.union B (PMatching.compatible_of_disjoint_support hdisj))
                      (π.union B hcompπ) rest
                  else none
                else none

omit [LinearOrder U] in
private lemma mkPMatching?_eq_some (M : PMatching U) : mkPMatching? M.edges = some M := by
  unfold mkPMatching?
  have h : (∀ e ∈ M.edges, ¬ e.IsDiag) ∧
      (∀ e₁ ∈ M.edges, ∀ e₂ ∈ M.edges, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) :=
    ⟨M.nonDiag, M.disjoint⟩
  split_ifs
  rfl

private lemma idxOf_lt_of_mem_le {α : Type*} [DecidableEq α] {l : List α} {a : α} {n : ℕ}
    (ha : a ∈ l) (hl : l.length ≤ n) : l.idxOf a < n :=
  Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem ha) hl

private lemma getElem?_idxOf_eq_some {α : Type*} [DecidableEq α] {l : List α} {a : α}
    (ha : a ∈ l) : l[l.idxOf a]? = some a := by
  have hlt : l.idxOf a < l.length := List.idxOf_lt_length_of_mem ha
  rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]

/-- Encodes a `DeepTrace` into a hint list of length `tr.totalEdges`. -/
private noncomputable def encodeTrace {F : MDNF U} {ρ : PMatching U} {k r' : ℕ}
    (hF : ∀ C ∈ F, C.edges.card ≤ k) (hr' : 1 ≤ r') (hρ : ρ.free.card = r') :
    ∀ {π : PMatching U} {hπ : Disjoint ρ.support π.support},
      DeepTrace F ρ π hπ → List (HintEntry k r')
  | π, hπ, .last _ _ C D_part hfind hDle _ =>
      let cList := sortEdges C.edges
      let dList := sortEdges D_part.edges
      List.ofFn fun i : Fin dList.length ↦
        let e := dList[i]
        have heC : e ∈ cList :=
          mem_sortEdges.mpr
            (Finset.mem_sdiff.mp (hDle (mem_sortEdges.mp (List.getElem_mem i.isLt)))).1
        have hclen : cList.length ≤ k := by
          rw [length_sortEdges]; exact hF C (List.mem_of_find?_eq_some hfind)
        let idx : Fin k := ⟨cList.idxOf e, idxOf_lt_of_mem_le heC hclen⟩
        (idx, decide (i.val + 1 = dList.length), ⟨0, hr'⟩, ⟨0, hr'⟩)
  | π, hπ, .step _ _ C D B hfind hDeq _ hBdisj _ hDsubB hπB rest =>
      let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
      let Drest := rest.futureData.1
      have hRestDisj := rest.futureData.2.1
      have hρπ_sub : ρπ.support ⊆ (ρ.union (π.union B (PMatching.compatible_of_disjoint_support
          (Finset.disjoint_of_subset_left
            (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj)))
          (PMatching.compatible_of_disjoint_support hπB)).support := by
        simp only [ρπ, PMatching.union_support]
        exact Finset.union_subset_union_right Finset.subset_union_left
      let hρπRest : Disjoint ρπ.support Drest.support :=
        Finset.disjoint_of_subset_left hρπ_sub hRestDisj
      let τ_mid := ρπ.union Drest (PMatching.compatible_of_disjoint_support hρπRest)
      have hB_free : B.support ⊆ τ_mid.free := by
        intro x hx
        rw [PMatching.mem_free_iff, PMatching.union_support]
        intro hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact Finset.disjoint_left.mp hBdisj h1 hx
        · have hx' : x ∈ (ρ.union (π.union B (PMatching.compatible_of_disjoint_support
              (Finset.disjoint_of_subset_left
                (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj)))
              (PMatching.compatible_of_disjoint_support hπB)).support := by
            simp only [PMatching.union_support]
            exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
          exact Finset.disjoint_left.mp hRestDisj hx' h2
      have hfree_le : (τ_mid.free.sort (· ≤ ·)).length ≤ r' := by
        rw [Finset.length_sort, ← hρ]
        refine PMatching.card_free_le (le_trans (PMatching.le_union_left _ _ _)
          (PMatching.le_union_left _ _ _))
      let cList := sortEdges C.edges
      let dList := sortEdges D.edges
      let freeList := τ_mid.free.sort (· ≤ ·)
      let chunk : List (HintEntry k r') :=
        List.ofFn fun i : Fin dList.length ↦
          let e := dList[i]
          have heD : e ∈ D.edges := mem_sortEdges.mp (List.getElem_mem i.isLt)
          have heC : e ∈ cList :=
            mem_sortEdges.mpr (Finset.mem_sdiff.mp (hDeq ▸ heD)).1
          have hclen : cList.length ≤ k := by
            rw [length_sortEdges]; exact hF C (List.mem_of_find?_eq_some hfind)
          let p := edgeKey e
          have hp1D : p.1 ∈ D.support := PMatching.mem_support_iff.mpr ⟨e, heD, mem_edgeKey_left e⟩
          have hp2D : p.2 ∈ D.support :=
            PMatching.mem_support_iff.mpr ⟨e, heD, mem_edgeKey_right e⟩
          have hp1B : p.1 ∈ B.support := hDsubB hp1D
          have hp2B : p.2 ∈ B.support := hDsubB hp2D
          let u : U := match B.partner p.1 with | some w => w | none => p.1
          let v : U := match B.partner p.2 with | some w => w | none => p.2
          have hu_mem : u ∈ freeList := by
            refine (Finset.mem_sort _).mpr (hB_free ?_)
            cases hpu : B.partner p.1 with
            | none => exact absurd hp1B (PMatching.partner_eq_none_iff.mp hpu)
            | some w =>
              simp only [u, hpu]
              exact PMatching.mem_support_iff.mpr
                ⟨s(p.1, w), PMatching.partner_eq_some_iff.mp hpu, Sym2.mem_mk_right _ _⟩
          have hv_mem : v ∈ freeList := by
            refine (Finset.mem_sort _).mpr (hB_free ?_)
            cases hpv : B.partner p.2 with
            | none => exact absurd hp2B (PMatching.partner_eq_none_iff.mp hpv)
            | some w =>
              simp only [v, hpv]
              exact PMatching.mem_support_iff.mpr
                ⟨s(p.2, w), PMatching.partner_eq_some_iff.mp hpv, Sym2.mem_mk_right _ _⟩
          let idx : Fin k := ⟨cList.idxOf e, idxOf_lt_of_mem_le heC hclen⟩
          let px : Fin r' := ⟨freeList.idxOf u, idxOf_lt_of_mem_le hu_mem hfree_le⟩
          let py : Fin r' := ⟨freeList.idxOf v, idxOf_lt_of_mem_le hv_mem hfree_le⟩
          (idx, decide (i.val + 1 = dList.length), px, py)
      chunk ++ encodeTrace hF hr' hρ rest

private lemma length_encodeTrace {F : MDNF U} {ρ : PMatching U} {k r' : ℕ}
    (hF : ∀ C ∈ F, C.edges.card ≤ k) (hr' : 1 ≤ r') (hρ : ρ.free.card = r') :
    ∀ {π : PMatching U} {hπ : Disjoint ρ.support π.support} (tr : DeepTrace F ρ π hπ),
      (encodeTrace hF hr' hρ tr).length = tr.totalEdges
  | _, _, .last _ _ _ D_part _ _ _ => by
    simp [encodeTrace, DeepTrace.totalEdges, length_sortEdges]
  | _, _, .step _ _ _ D _ _ _ _ _ _ _ _ rest => by
    simp [encodeTrace, DeepTrace.totalEdges, length_sortEdges, length_encodeTrace hF hr' hρ rest]

private lemma encodeTrace_ne_nil {F : MDNF U} {ρ : PMatching U} {k r' : ℕ}
    (hF : ∀ C ∈ F, C.edges.card ≤ k) (hr' : 1 ≤ r') (hρ : ρ.free.card = r') :
    ∀ {π : PMatching U} {hπ : Disjoint ρ.support π.support} (tr : DeepTrace F ρ π hπ),
      encodeTrace hF hr' hρ tr ≠ [] := by
  intro π hπ tr
  have hlen := length_encodeTrace hF hr' hρ tr
  have hpos : 0 < tr.totalEdges := by
    cases tr with
    | last _ _ _ D_part _ _ hDne => exact Finset.card_pos.mpr hDne
    | step _ _ _ D _ _ _ hDne _ _ _ _ _ =>
      simp only [DeepTrace.totalEdges]
      have := Finset.card_pos.mpr hDne; omega
  intro hnil
  rw [hnil] at hlen
  simp at hlen
  omega

omit [Fintype U] [LinearOrder U] in
private lemma exists_partner_of_mem_support {M : PMatching U} {x : U} (hx : x ∈ M.support) :
    ∃ u, M.partner x = some u := by
  cases hp : M.partner x with
  | none => exact absurd hx (PMatching.partner_eq_none_iff.mp hp)
  | some w => exact ⟨w, rfl⟩

private lemma decodeAux_encodeTrace {F : MDNF U} {ρ : PMatching U} {k r' : ℕ}
    (hF : ∀ C ∈ F, C.edges.card ≤ k) (hr' : 1 ≤ r') (hρ : ρ.free.card = r') :
    ∀ {π : PMatching U} {hπ : Disjoint ρ.support π.support} (tr : DeepTrace F ρ π hπ)
      {fuel : ℕ}, tr.totalEdges ≤ fuel →
      decodeAux F k r' fuel
        ((ρ.union π (PMatching.compatible_of_disjoint_support hπ)).union tr.futureData.1
          (PMatching.compatible_of_disjoint_support tr.futureData.2.1))
        π (encodeTrace hF hr' hρ tr) = some ρ
  | π, hπ, .last _ _ C D_part hfind hDle hDne, fuel, hfuel => by
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := fuel) (by
      have hpos : 0 < D_part.edges.card := Finset.card_pos.mpr hDne
      have hle : D_part.edges.card ≤ fuel := hfuel
      omega)
    let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
    have hcompC₀ : C.Compatible ρπ := compatible_of_find?_eq_some hfind
    let τ := ρπ.union D_part (PMatching.compatible_of_disjoint_support
      (Finset.disjoint_of_subset_right (PMatching.support_mono hDle)
        (disjoint_support_sdiff_of_compatible hcompC₀)))
    have hcompC : C.Compatible τ := by
      intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
      rcases Finset.mem_union.mp he₂ with h2a | h2b
      · exact hcompC₀ e₁ he₁ e₂ h2a hne x hx₁ hx₂
      · exact C.disjoint e₁ he₁ e₂ (Finset.mem_sdiff.mp (hDle h2b)).1 hne x hx₁ hx₂
    have hfind' : F.find? (fun C' ↦ decide (C'.Compatible τ)) = some C :=
      find?_compatible_of_le hfind (PMatching.le_union_left _ _ _) hcompC
    have hne_chunk : encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne) ≠ [] :=
      encodeTrace_ne_nil hF hr' hρ _
    have hsplit : splitChunk (encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne)) =
        (encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne), []) := by
      have := splitChunk_append (encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne)) []
        hne_chunk (by
          intro i hi
          simp only [encodeTrace, List.getElem_ofFn, List.length_ofFn] at hi ⊢)
      simpa using this
    have hdEdges : ((encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne)).filterMap
        fun h ↦ (sortEdges C.edges)[h.1.val]?).toFinset = D_part.edges := by
      ext e
      simp only [List.mem_toFinset, List.mem_filterMap, encodeTrace, List.mem_ofFn]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, heq⟩
        have heC : (sortEdges D_part.edges)[i] ∈ sortEdges C.edges :=
          mem_sortEdges.mpr
            (Finset.mem_sdiff.mp (hDle (mem_sortEdges.mp (List.getElem_mem i.isLt)))).1
        rw [getElem?_idxOf_eq_some heC] at heq
        have := Option.some.inj heq
        subst this
        exact mem_sortEdges.mp (List.getElem_mem i.isLt)
      · intro he
        have he_d : e ∈ sortEdges D_part.edges := mem_sortEdges.mpr he
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he_d
        refine ⟨_, ⟨⟨i, hi⟩, rfl⟩, ?_⟩
        have heC : (sortEdges D_part.edges)[i] ∈ sortEdges C.edges :=
          mem_sortEdges.mpr (Finset.mem_sdiff.mp (hDle he)).1
        exact getElem?_idxOf_eq_some heC
    change decodeAux F k r' (fuel' + 1) τ π
      (encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne)) = some ρ
    cases hlist : encodeTrace hF hr' hρ (.last π hπ C D_part hfind hDle hDne) with
    | nil => exact (hne_chunk hlist).elim
    | cons a as =>
      rw [← hlist]
      unfold decodeAux
      rw [hlist]
      dsimp only
      rw [← hlist, hfind', hsplit]
      dsimp only
      rw [hdEdges, mkPMatching?_eq_some]
      dsimp only
      congr 1
      ext e
      simp only [τ, ρπ, PMatching.sdiff_edges, PMatching.union_edges, Finset.mem_sdiff,
        Finset.mem_union]
      constructor
      · rintro ⟨⟨(h1 | h2) | h3, hnotD⟩, hnotπ⟩
        · exact h1
        · exact absurd h2 hnotπ
        · exact absurd h3 hnotD
      · intro he
        have hnotD : e ∉ D_part.edges := fun hD ↦ by
          obtain ⟨x, hx⟩ := exists_mem_sym2 e
          have hdisj := (DeepTrace.last π hπ C D_part hfind hDle hDne).futureData.2.1
          exact Finset.disjoint_left.mp hdisj
            (by
              rw [PMatching.union_support]
              exact Finset.mem_union_left _ (PMatching.mem_support_iff.mpr ⟨e, he, hx⟩))
            (PMatching.mem_support_iff.mpr ⟨e, hD, hx⟩)
        have hnotπ : e ∉ π.edges := fun hπe ↦ by
          obtain ⟨x, hx⟩ := exists_mem_sym2 e
          exact Finset.disjoint_left.mp hπ
            (PMatching.mem_support_iff.mpr ⟨e, he, hx⟩)
            (PMatching.mem_support_iff.mpr ⟨e, hπe, hx⟩)
        exact ⟨⟨Or.inl (Or.inl he), hnotD⟩, hnotπ⟩
  | π, hπ, .step _ _ C D B hfind hDeq hDne hBdisj hBhit hDsubB hπB rest, fuel, hfuel => by
    let ρπ := ρ.union π (PMatching.compatible_of_disjoint_support hπ)
    let πB := π.union B (PMatching.compatible_of_disjoint_support
      (Finset.disjoint_of_subset_left
        (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj))
    let ρπB := ρ.union πB (PMatching.compatible_of_disjoint_support hπB)
    let Drest := rest.futureData.1
    have hRestDisj := rest.futureData.2.1
    have hρπB_sup : ρπB.support = ρπ.support ∪ B.support := by
      simp only [ρπB, ρπ, πB, PMatching.union_support, Finset.union_assoc]
    have hDRestDisj : Disjoint D.support Drest.support :=
      Finset.disjoint_of_subset_left
        (hDsubB.trans (by rw [hρπB_sup]; exact Finset.subset_union_right)) hRestDisj
    have hρπRest : Disjoint ρπ.support Drest.support :=
      Finset.disjoint_of_subset_left
        (by rw [hρπB_sup]; exact Finset.subset_union_left) hRestDisj
    have hBRest : Disjoint B.support Drest.support :=
      Finset.disjoint_of_subset_left
        (by rw [hρπB_sup]; exact Finset.subset_union_right) hRestDisj
    let τ_mid := ρπ.union Drest (PMatching.compatible_of_disjoint_support hρπRest)
    let Dtot := D.union Drest (PMatching.compatible_of_disjoint_support hDRestDisj)
    have hcompC₀ : C.Compatible ρπ := compatible_of_find?_eq_some hfind
    let τ := ρπ.union Dtot (PMatching.compatible_of_disjoint_support
      (by
        have hDsup : Dtot.support = D.support ∪ Drest.support := PMatching.union_support _ _ _
        rw [hDsup]
        exact Finset.disjoint_union_right.mpr
          ⟨hDeq ▸ disjoint_support_sdiff_of_compatible hcompC₀, hρπRest⟩))
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := fuel) (by
      have hpos : 0 < D.edges.card := Finset.card_pos.mpr hDne
      have hle : D.edges.card + rest.totalEdges ≤ fuel := hfuel
      omega)
    have hcompC : C.Compatible τ := by
      intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
      rcases Finset.mem_union.mp he₂ with h2a | h2b
      · exact hcompC₀ e₁ he₁ e₂ h2a hne x hx₁ hx₂
      · rcases Finset.mem_union.mp h2b with h2D | h2R
        · exact C.disjoint e₁ he₁ e₂ (Finset.mem_sdiff.mp (hDeq ▸ h2D)).1 hne x hx₁ hx₂
        · by_cases he₁ρπ : e₁ ∈ ρπ.edges
          · exact Finset.disjoint_left.mp hρπRest
              (PMatching.mem_support_iff.mpr ⟨e₁, he₁ρπ, hx₁⟩)
              (PMatching.mem_support_iff.mpr ⟨e₂, h2R, hx₂⟩)
          · have he₁D : e₁ ∈ D.edges := by rw [hDeq]; exact Finset.mem_sdiff.mpr ⟨he₁, he₁ρπ⟩
            exact Finset.disjoint_left.mp hDRestDisj
              (PMatching.mem_support_iff.mpr ⟨e₁, he₁D, hx₁⟩)
              (PMatching.mem_support_iff.mpr ⟨e₂, h2R, hx₂⟩)
    have hfind' : F.find? (fun C' ↦ decide (C'.Compatible τ)) = some C :=
      find?_compatible_of_le hfind (PMatching.le_union_left _ _ _) hcompC
    -- Split `encodeTrace` into `(chunk, restHint)`
    set restHint := encodeTrace hF hr' hρ rest
    have hrest_ne : restHint ≠ [] := encodeTrace_ne_nil hF hr' hρ rest
    -- Extract the chunk from `encodeTrace`
    change decodeAux F k r' (fuel' + 1) τ π (encodeTrace hF hr' hρ
      (.step π hπ C D B hfind hDeq hDne hBdisj hBhit hDsubB hπB rest)) = some ρ
    set fullHint := encodeTrace hF hr' hρ
      (.step π hπ C D B hfind hDeq hDne hBdisj hBhit hDsubB hπB rest)
    have hfull_eq : ∃ chunk : List (HintEntry k r'),
        fullHint = chunk ++ restHint ∧
        chunk ≠ [] ∧
        splitChunk fullHint = (chunk, restHint) ∧
        (chunk.filterMap fun h ↦ (sortEdges C.edges)[h.1.val]?).toFinset = D.edges ∧
        (chunk.flatMap fun h ↦
          match (sortEdges C.edges)[h.1.val]?, (τ_mid.free.sort (· ≤ ·))[h.2.2.1.val]?,
              (τ_mid.free.sort (· ≤ ·))[h.2.2.2.val]? with
          | some e, some u, some v => [s((edgeKey e).1, u), s((edgeKey e).2, v)]
          | _, _, _ => []).toFinset = B.edges := by
      have hDC : D.edges ⊆ C.edges := fun e he ↦ by
        rw [hDeq] at he; exact (Finset.mem_sdiff.mp he).1
      -- Directly read off from the `step` branch of `encodeTrace`
      refine ⟨fullHint.take D.edges.card, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [fullHint, encodeTrace]
        rw [List.take_left' (by simp [length_sortEdges])]
      · intro hnil
        have hlen : (fullHint.take D.edges.card).length = D.edges.card := by
          simp only [fullHint, encodeTrace]
          rw [List.take_left' (by simp [length_sortEdges]), List.length_ofFn, length_sortEdges]
        rw [hnil, List.length_nil] at hlen
        exact (Finset.card_pos.mpr hDne).ne hlen
      · simp only [fullHint, encodeTrace]
        rw [List.take_left' (by simp [length_sortEdges])]
        refine splitChunk_append _ _ ?_ ?_
        · intro hnil
          have := congrArg List.length hnil
          simp only [List.length_ofFn, length_sortEdges, List.length_nil] at this
          exact (Finset.card_pos.mpr hDne).ne' this
        · intro i hi
          simp only [List.getElem_ofFn, List.length_ofFn] at hi ⊢
      · simp only [fullHint, encodeTrace]
        rw [List.take_left' (by simp [length_sortEdges])]
        ext e
        simp only [List.mem_toFinset, List.mem_filterMap, List.mem_ofFn]
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, heq⟩
          have heD : (sortEdges D.edges)[i] ∈ D.edges := mem_sortEdges.mp (List.getElem_mem i.isLt)
          have heC : (sortEdges D.edges)[i] ∈ sortEdges C.edges := mem_sortEdges.mpr (hDC heD)
          rw [getElem?_idxOf_eq_some heC] at heq
          exact (Option.some.inj heq) ▸ heD
        · intro heD
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_sortEdges.mpr heD)
          refine ⟨_, ⟨⟨i, hi⟩, rfl⟩, getElem?_idxOf_eq_some (mem_sortEdges.mpr (hDC heD))⟩
      · simp only [fullHint, encodeTrace]
        rw [List.take_left' (by simp [length_sortEdges])]
        ext e'
        simp only [List.mem_toFinset, List.mem_flatMap, List.mem_ofFn]
        have hB_free : B.support ⊆ τ_mid.free := fun x hx ↦ by
          rw [PMatching.mem_free_iff, PMatching.union_support]
          intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h2
          · exact Finset.disjoint_left.mp hBdisj h1 hx
          · exact Finset.disjoint_left.mp hBRest hx h2
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, he'⟩
          have heD : (sortEdges D.edges)[i] ∈ D.edges := mem_sortEdges.mp (List.getElem_mem i.isLt)
          have heC : (sortEdges D.edges)[i] ∈ sortEdges C.edges := mem_sortEdges.mpr (hDC heD)
          set e := (sortEdges D.edges)[i]
          set p := edgeKey e
          obtain ⟨u, hu⟩ := exists_partner_of_mem_support
            (hDsubB (PMatching.mem_support_iff.mpr ⟨e, heD, mem_edgeKey_left e⟩))
          obtain ⟨v, hv⟩ := exists_partner_of_mem_support
            (hDsubB (PMatching.mem_support_iff.mpr ⟨e, heD, mem_edgeKey_right e⟩))
          have hu_mem : u ∈ τ_mid.free.sort (· ≤ ·) :=
            (Finset.mem_sort _).mpr (hB_free (PMatching.mem_support_iff.mpr
              ⟨s(p.1, u), PMatching.partner_eq_some_iff.mp hu, Sym2.mem_mk_right _ _⟩))
          have hv_mem : v ∈ τ_mid.free.sort (· ≤ ·) :=
            (Finset.mem_sort _).mpr (hB_free (PMatching.mem_support_iff.mpr
              ⟨s(p.2, v), PMatching.partner_eq_some_iff.mp hv, Sym2.mem_mk_right _ _⟩))
          have hfl : ((ρ.union π (PMatching.compatible_of_disjoint_support hπ)).union
              rest.futureData.1 (PMatching.compatible_of_disjoint_support
                (Finset.disjoint_of_subset_left
                  (by simp only [PMatching.union_support]
                      exact Finset.union_subset_union_right Finset.subset_union_left)
                  hRestDisj))).free.sort (· ≤ ·) = τ_mid.free.sort (· ≤ ·) := rfl
          dsimp only at he'
          rw [hfl, getElem?_idxOf_eq_some heC, hu, hv, getElem?_idxOf_eq_some hu_mem,
            getElem?_idxOf_eq_some hv_mem] at he'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl
          · exact PMatching.partner_eq_some_iff.mp hu
          · exact PMatching.partner_eq_some_iff.mp hv
        · intro he'
          rcases hBhit e' he' with ⟨x, hxD, hxe'⟩
          rcases PMatching.mem_support_iff.mp hxD with ⟨e, heD, hxe⟩
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_sortEdges.mpr heD)
          have heC : (sortEdges D.edges)[i] ∈ sortEdges C.edges := mem_sortEdges.mpr (hDC heD)
          set p := edgeKey (sortEdges D.edges)[i]
          obtain ⟨u, hu⟩ := exists_partner_of_mem_support
            (hDsubB (PMatching.mem_support_iff.mpr ⟨_, heD, mem_edgeKey_left _⟩))
          obtain ⟨v, hv⟩ := exists_partner_of_mem_support
            (hDsubB (PMatching.mem_support_iff.mpr ⟨_, heD, mem_edgeKey_right _⟩))
          have hu_mem : u ∈ τ_mid.free.sort (· ≤ ·) :=
            (Finset.mem_sort _).mpr (hB_free (PMatching.mem_support_iff.mpr
              ⟨s(p.1, u), PMatching.partner_eq_some_iff.mp hu, Sym2.mem_mk_right _ _⟩))
          have hv_mem : v ∈ τ_mid.free.sort (· ≤ ·) :=
            (Finset.mem_sort _).mpr (hB_free (PMatching.mem_support_iff.mpr
              ⟨s(p.2, v), PMatching.partner_eq_some_iff.mp hv, Sym2.mem_mk_right _ _⟩))
          refine ⟨_, ⟨⟨i, hi⟩, rfl⟩, ?_⟩
          dsimp only
          change e' ∈ match (sortEdges C.edges)[(sortEdges C.edges).idxOf
              (sortEdges D.edges)[i]]?,
            (τ_mid.free.sort (· ≤ ·))[(τ_mid.free.sort (· ≤ ·)).idxOf
              (match B.partner p.1 with | some w => w | none => p.1)]?,
            (τ_mid.free.sort (· ≤ ·))[(τ_mid.free.sort (· ≤ ·)).idxOf
              (match B.partner p.2 with | some w => w | none => p.2)]? with
            | some e, some u, some v => [s((edgeKey e).1, u), s((edgeKey e).2, v)]
            | _, _, _ => []
          rw [getElem?_idxOf_eq_some heC, hu, hv, getElem?_idxOf_eq_some hu_mem,
            getElem?_idxOf_eq_some hv_mem]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          have hxp : x = p.1 ∨ x = p.2 := by
            rw [← s_edgeKey (sortEdges D.edges)[i]] at hxe
            exact Sym2.mem_iff.mp hxe
          obtain ⟨w, hwe'⟩ := Sym2.mem_iff_exists.mp hxe'
          subst hwe'
          rcases hxp with rfl | rfl
          · left
            have hw := PMatching.partner_eq_some_iff.mpr he'
            rw [hu] at hw
            rw [Option.some.inj hw]
          · right
            have hw := PMatching.partner_eq_some_iff.mpr he'
            rw [hv] at hw
            rw [Option.some.inj hw]
    rcases hfull_eq with ⟨chunk, hfeq, hchunk_ne, hsplit, hdE, hbE⟩
    have hτ_sdiff : τ.sdiff D = τ_mid := by
      ext e
      simp only [τ, τ_mid, Dtot, PMatching.sdiff_edges, PMatching.union_edges,
        Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | (h2 | h3), hnotD⟩
        · exact Or.inl h1
        · exact absurd h2 hnotD
        · exact Or.inr h3
      · rintro (h1 | h3)
        · refine ⟨Or.inl h1, fun hD ↦ ?_⟩
          obtain ⟨x, hx⟩ := exists_mem_sym2 e
          have hDd := hDeq ▸ disjoint_support_sdiff_of_compatible hcompC₀
          exact Finset.disjoint_left.mp hDd
            (PMatching.mem_support_iff.mpr ⟨e, h1, hx⟩)
            (PMatching.mem_support_iff.mpr ⟨e, hD, hx⟩)
        · refine ⟨Or.inr (Or.inr h3), fun hD ↦ ?_⟩
          obtain ⟨x, hx⟩ := exists_mem_sym2 e
          exact Finset.disjoint_left.mp hDRestDisj
            (PMatching.mem_support_iff.mpr ⟨e, hD, hx⟩)
            (PMatching.mem_support_iff.mpr ⟨e, h3, hx⟩)
    have hdisj_mid_B : Disjoint τ_mid.support B.support := by
      rw [PMatching.union_support]
      exact Finset.disjoint_union_left.mpr ⟨hBdisj, hBRest.symm⟩
    have hcompπB : π.Compatible B :=
      PMatching.compatible_of_disjoint_support
        (Finset.disjoint_of_subset_left
          (by rw [PMatching.union_support]; exact Finset.subset_union_right) hBdisj)
    have hτ_next : τ_mid.union B (PMatching.compatible_of_disjoint_support hdisj_mid_B) =
        ρπB.union Drest (PMatching.compatible_of_disjoint_support hRestDisj) := by
      ext e
      simp only [τ_mid, ρπB, ρπ, πB, PMatching.union_edges, Finset.mem_union]
      tauto
    have hfull_ne : fullHint ≠ [] := by
      rw [hfeq]; intro h; exact hchunk_ne (List.append_eq_nil_iff.mp h).1
    cases hfh : fullHint with
    | nil => exact (hfull_ne hfh).elim
    | cons a as =>
      cases hrh : restHint with
      | nil => exact (hrest_ne hrh).elim
      | cons b bs =>
        rw [← hfh]
        unfold decodeAux
        rw [hfh]
        dsimp only
        rw [← hfh, hfind', hsplit]
        dsimp only
        rw [hdE, mkPMatching?_eq_some]
        dsimp only
        rw [hτ_sdiff, hrh]
        dsimp only
        rw [← hrh, hbE, mkPMatching?_eq_some]
        dsimp only
        simp only [hdisj_mid_B, hcompπB, ↓reduceDIte, hτ_next]
        refine decodeAux_encodeTrace hF hr' hρ rest ?_
        have := Finset.card_pos.mpr hDne
        simp only [DeepTrace.totalEdges] at hfuel
        omega

/-- **Finite Matching Switching Lemma**: for any width-`k` matching DNF `F` (`1 ≤ k`) and
parameters `2 * s ≤ r' ≤ ρ₀.free.card` with `Even (ρ₀.free.card - r')`, the number of extensions
`ρ ∈ ρ₀.extensions r'` whose canonical decision tree has depth `≥ 2 * s` satisfies
`#{bad ρ} * (ρ₀.free.card - r') ^ s ≤ #(ρ₀.extensions r') * (2 * k * r' ^ 4) ^ s`. -/
theorem card_matching_switching_le (ρ₀ : PMatching U) (F : MDNF U) {r' k s : ℕ}
    (hF : ∀ C ∈ F, C.edges.card ≤ k) (hk : 1 ≤ k) (hr' : 2 * s ≤ r')
    (hr'le : r' ≤ ρ₀.free.card) (heven : Even (ρ₀.free.card - r')) :
    ((ρ₀.extensions r').filter (fun ρ ↦ 2 * s ≤ (canonTree F ρ).depth)).card *
        (ρ₀.free.card - r') ^ s ≤
      (ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s := by
  by_cases hs0 : s = 0
  · subst hs0
    simp only [pow_zero, mul_one]
    exact Finset.card_filter_le _ _
  have hs : 1 ≤ s := Nat.pos_of_ne_zero hs0
  have hr'1 : 1 ≤ r' := by omega
  let bad := (ρ₀.extensions r').filter (fun ρ ↦ 2 * s ≤ (canonTree F ρ).depth)
  let target := (ρ₀.extensions (r' - 2 * s)) ×ˢ
    (Finset.univ : Finset (Fin s → HintEntry k r'))
  have hbad_le : bad.card ≤ target.card := by
    -- Inject `bad` into `target` via `(τ, hint)` from `exists_deepTrace_of_depth` + `encodeTrace`.
    classical
    have hex : ∀ ρ ∈ bad, ∃ p ∈ target,
        decodeAux F k r' (s + 1) p.1 ⊥ (List.ofFn p.2) = some ρ := by
      intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hρext, hdep⟩
      rcases PMatching.mem_extensions_iff.mp hρext with ⟨hρ₀, hρfree⟩
      obtain ⟨tr, htr⟩ := exists_deepTrace_of_depth (Fintype.card U) F ρ ⊥ (by simp) hs hdep
      let Dtot := tr.futureData.1
      have hDdisj := tr.futureData.2.1
      have hDcard : Dtot.edges.card = s := tr.futureData.2.2.trans htr
      have hρD_disj : Disjoint ρ.support Dtot.support := by
        simpa [PMatching.union_support] using hDdisj
      let τ := (ρ.union ⊥ (PMatching.compatible_of_disjoint_support (by simp))).union Dtot
        (PMatching.compatible_of_disjoint_support hDdisj)
      let hintList := encodeTrace hF hr'1 hρfree tr
      have hlen : hintList.length = s := (length_encodeTrace hF hr'1 hρfree tr).trans htr
      let hintFn : Fin s → HintEntry k r' := fun i ↦ hintList[i.val]'(by omega)
      have hofFn : List.ofFn hintFn = hintList := by
        refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ ↦ ?_
        simp [hintFn]
      have hτ_mem : τ ∈ ρ₀.extensions (r' - 2 * s) := by
        rw [PMatching.mem_extensions_iff]
        refine ⟨le_trans hρ₀ (le_trans (PMatching.le_union_left _ _ _)
          (PMatching.le_union_left _ _ _)), ?_⟩
        have h1 := τ.card_free_add
        have h2 := ρ.card_free_add
        have hτ_eq : τ.edges = ρ.edges ∪ Dtot.edges := by
          simp [τ, PMatching.union_edges]
        have hτ_card : τ.edges.card = ρ.edges.card + s := by
          rw [hτ_eq, Finset.card_union_of_disjoint, hDcard]
          rw [Finset.disjoint_left]
          intro e he₁ he₂
          obtain ⟨x, hx⟩ := exists_mem_sym2 e
          exact Finset.disjoint_left.mp hρD_disj
            (PMatching.mem_support_iff.mpr ⟨e, he₁, hx⟩)
            (PMatching.mem_support_iff.mpr ⟨e, he₂, hx⟩)
        omega
      refine ⟨(τ, hintFn), Finset.mem_product.mpr ⟨hτ_mem, Finset.mem_univ _⟩, ?_⟩
      rw [hofFn]
      exact decodeAux_encodeTrace hF hr'1 hρfree tr (by omega)
    let enc : PMatching U → PMatching U × (Fin s → HintEntry k r') := fun ρ ↦
      if h : ρ ∈ bad then Classical.choose (hex ρ h)
      else (⊥, fun _ ↦ (⟨0, hk⟩, false, ⟨0, hr'1⟩, ⟨0, hr'1⟩))
    refine Finset.card_le_card_of_injOn enc ?_ ?_
    · intro ρ hρ
      have hρm : ρ ∈ bad := hρ
      simp only [enc, hρm, ↓reduceDIte]
      exact (Classical.choose_spec (hex ρ hρm)).1
    · intro ρ₁ hρ₁ ρ₂ hρ₂ heq
      have h1m : ρ₁ ∈ bad := hρ₁
      have h2m : ρ₂ ∈ bad := hρ₂
      simp only [enc, h1m, h2m, ↓reduceDIte] at heq
      have h1 := (Classical.choose_spec (hex ρ₁ h1m)).2
      have h2 := (Classical.choose_spec (hex ρ₂ h2m)).2
      rw [heq] at h1
      exact Option.some.inj (h1.symm.trans h2)
  have htarget_card : target.card =
      (ρ₀.extensions (r' - 2 * s)).card * (2 * k * r' ^ 2) ^ s := by
    simp only [target, Finset.card_product, Finset.card_univ, Fintype.card_fun,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    congr 1
    ring
  have hratio := PMatching.card_extensions_ratio ρ₀ hr' hr'le heven
  calc bad.card * (ρ₀.free.card - r') ^ s
      ≤ target.card * (ρ₀.free.card - r') ^ s := Nat.mul_le_mul_right _ hbad_le
    _ = (ρ₀.extensions (r' - 2 * s)).card * (ρ₀.free.card - r') ^ s * (2 * k * r' ^ 2) ^ s := by
        rw [htarget_card]; ring
    _ ≤ (ρ₀.extensions r').card * r' ^ (2 * s) * (2 * k * r' ^ 2) ^ s :=
        Nat.mul_le_mul_right _ hratio
    _ = (ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s := by
        rw [mul_assoc, pow_mul, ← mul_pow]; ring

/-- Simultaneous switching of a finite family of `M` width-`k` matching DNFs under a single
extension `ρ ∈ ρ₀.extensions r'`. -/
theorem exists_extension_switching_family (ρ₀ : PMatching U) {M : ℕ} (Fs : Fin M → MDNF U)
    {r' k s : ℕ} (hF : ∀ i C, C ∈ Fs i → C.edges.card ≤ k) (hk : 1 ≤ k)
    (hr' : 2 * s ≤ r') (hr'le : r' ≤ ρ₀.free.card) (heven : Even (ρ₀.free.card - r'))
    (hbound : M * (2 * k * r' ^ 4) ^ s < (ρ₀.free.card - r') ^ s) :
    ∃ ρ ∈ ρ₀.extensions r', ∀ i : Fin M, (canonTree (Fs i) ρ).depth < 2 * s := by
  by_contra hall
  push Not at hall
  have hsub : ρ₀.extensions r' ⊆ Finset.univ.biUnion
      (fun i : Fin M ↦ (ρ₀.extensions r').filter fun ρ ↦ 2 * s ≤ (canonTree (Fs i) ρ).depth) := by
    intro ρ hρ
    rcases hall ρ hρ with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hρ, hi⟩⟩
  have hcard_le : (ρ₀.extensions r').card ≤
      ∑ i : Fin M, ((ρ₀.extensions r').filter fun ρ ↦ 2 * s ≤ (canonTree (Fs i) ρ).depth).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hmul_le : (ρ₀.extensions r').card * (ρ₀.free.card - r') ^ s ≤
      M * ((ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s) := by
    calc (ρ₀.extensions r').card * (ρ₀.free.card - r') ^ s
        ≤ (∑ i : Fin M, ((ρ₀.extensions r').filter
            fun ρ ↦ 2 * s ≤ (canonTree (Fs i) ρ).depth).card) * (ρ₀.free.card - r') ^ s :=
          Nat.mul_le_mul_right _ hcard_le
      _ = ∑ i : Fin M, ((ρ₀.extensions r').filter
            fun ρ ↦ 2 * s ≤ (canonTree (Fs i) ρ).depth).card * (ρ₀.free.card - r') ^ s := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _i : Fin M, (ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s :=
          Finset.sum_le_sum fun i _ ↦
            card_matching_switching_le ρ₀ (Fs i) (hF i) hk hr' hr'le heven
      _ = M * ((ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s) := by
          simp [Finset.sum_const, smul_eq_mul]
  have hpos : 0 < (ρ₀.extensions r').card :=
    Finset.card_pos.mpr (PMatching.extensions_nonempty ρ₀ hr'le heven)
  have hstrict : M * ((ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s) <
      (ρ₀.extensions r').card * (ρ₀.free.card - r') ^ s := by
    calc M * ((ρ₀.extensions r').card * (2 * k * r' ^ 4) ^ s)
        = (ρ₀.extensions r').card * (M * (2 * k * r' ^ 4) ^ s) := by ring
      _ < (ρ₀.extensions r').card * (ρ₀.free.card - r') ^ s :=
          Nat.mul_lt_mul_of_pos_left hbound hpos
  omega

end CanonicalTree

end CslibFrontier.Computability.DecisionTree
