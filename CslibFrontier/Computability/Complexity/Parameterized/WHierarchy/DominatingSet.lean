/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
public import CslibFrontier.Computability.Complexity.Problems.Clique.OfAdj
public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.SetCover

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-!
# W[1]-Hardness of Dominating Set, Ladder-Free Dominating Set, and Set Cover

Explicit polynomial-time parameterized reductions establishing `W[1]`-hardness of
`Cslib.Complexity.DominatingSet` (including on the ladder-free class forbidding semi-induced
ladders of order `46`) and `Cslib.Complexity.SetCover`, starting from
`Cslib.Complexity.Clique_wHard`.

## Main definitions

* `CslibFrontier.Complexity.HasSemiInducedLadder`: existence of a semi-induced ladder of order `n`
  in a simple graph.
* `CslibFrontier.Complexity.GadgetVert`, `CslibFrontier.Complexity.encGadgetVert`: structured
  gadget vertex type and polynomial-time framed encoding.
* `CslibFrontier.Complexity.cliqueToLadDomSet`: polynomial-time parameterized reduction from
  `Clique` to `DominatingSet` producing graphs with no semi-induced ladder of order `46`.
* `CslibFrontier.Complexity.domSetToSetCover`: closed-neighborhood polynomial-time parameterized
  reduction from `DominatingSet` to `SetCover`.

## Main results

* `CslibFrontier.Complexity.fptReducible_Clique_DominatingSet_ladderFree`: FPT reduction from
  `Clique` to ladder-free `DominatingSet`.
* `CslibFrontier.Complexity.DominatingSet_ladderFree_wHard`: `W[1]`-hardness of `DominatingSet`
  restricted to graphs excluding semi-induced ladders of order `46`.
* `CslibFrontier.Complexity.DominatingSet_wHard`: `W[1]`-hardness of `DominatingSet`.
* `CslibFrontier.Complexity.fptReducible_DominatingSet_SetCover`: FPT reduction from
  `DominatingSet` to `SetCover`.
* `CslibFrontier.Complexity.SetCover_wHard`: `W[1]`-hardness of `SetCover`.
-/

public section

namespace CslibFrontier.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open _root_.SimpleGraph

/-- A simple graph `G` contains a **semi-induced ladder** of order `n` if there exist sequences
`a, b : Fin n → V` with disjoint ranges such that `G.Adj (a i) (b j) ↔ j < i` for all `i, j`. -/
@[expose]
def HasSemiInducedLadder {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (a b : Fin n → V), Disjoint (Set.range a) (Set.range b) ∧
    ∀ i j : Fin n, G.Adj (a i) (b j) ↔ j < i

section Helpers

private theorem nodup_append_of_disjoint {α : Type*} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hd : ∀ x, x ∈ l₁ → x ∈ l₂ → False) :
    (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h₁, h₂, fun x hx₁ _ hx₂ heq ↦ hd x hx₁ (heq ▸ hx₂)⟩

private theorem nodup_flatMap_disjoint {α β : Type*} {l : List α} (hl : l.Nodup) (f : α → List β)
    (hfn : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a₁ a₂, a₁ ≠ a₂ → ∀ x, x ∈ f a₁ → x ∉ f a₂) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    obtain ⟨hatl, htl⟩ := List.nodup_cons.mp hl
    rw [List.flatMap_cons]
    refine nodup_append_of_disjoint (hfn a (List.mem_cons_self ..))
      (ih htl (fun x hx ↦ hfn x (List.mem_cons_of_mem _ hx))) fun x hxa hxtl ↦ ?_
    obtain ⟨a₂, ha₂, hxa₂⟩ := List.mem_flatMap.mp hxtl
    exact hdisj a a₂ (fun heq ↦ hatl (heq ▸ ha₂)) x hxa hxa₂

private theorem mem_ite_singleton {α : Type*} {c : Bool} {x v : α}
    (h : x ∈ (if c then [v] else [])) : c = true ∧ x = v := by
  cases c
  · simp at h
  · simp only [↓reduceIte, List.mem_singleton] at h
    exact ⟨rfl, h⟩

private theorem exists_fiber_card_ge {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (m : ℕ) (h : Fintype.card β * m < Fintype.card α) :
    ∃ b : β, m + 1 ≤ #(univ.filter fun a : α ↦ f a = b) := by
  classical
  by_contra hno
  push Not at hno
  have hsum : ∑ b : β, #(univ.filter fun a : α ↦ f a = b) ≤ Fintype.card β * m := by
    simpa using sum_le_card_nsmul (univ : Finset β) _ m fun b _ ↦ Nat.lt_succ_iff.mp (hno b)
  have hcov : (univ : Finset α) ⊆ (univ : Finset β).biUnion
      fun b ↦ univ.filter fun a : α ↦ f a = b :=
    fun a _ ↦ mem_biUnion.mpr ⟨f a, mem_univ _, mem_filter.mpr ⟨mem_univ a, rfl⟩⟩
  have hle : Fintype.card α ≤ ∑ b : β, #(univ.filter fun a : α ↦ f a = b) := by
    rw [← card_univ]
    exact (card_le_card hcov).trans card_biUnion_le
  omega

private theorem ofAdj_induced_embedding {V : Type} {vs : List V} {adj : V → V → Bool}
    (hnd : vs.Nodup) (hsym : ∀ x y, adj x y = adj y x) (hirr : ∀ x, adj x x = false) :
    Nonempty ((Graph.ofAdj vs adj).induced ↪g
      SimpleGraph.fromRel (fun x y : V ↦ adj x y = true)) := by
  have hlt : ∀ p : {v // v ∈ (Graph.ofAdj vs adj).vertices}, p.1 < vs.length :=
    fun p ↦ List.mem_range.mp p.2
  refine ⟨{
    toFun := fun p ↦ vs[p.1]'(hlt p)
    inj' := fun p q hpq ↦ Subtype.ext ((hnd.getElem_inj_iff (hi := hlt p) (hj := hlt q)).mp hpq)
    map_rel_iff' := fun {p q} ↦ ?_ }⟩
  change (SimpleGraph.fromRel fun x y : V ↦ adj x y = true).Adj (vs[p.1]'(hlt p))
    (vs[q.1]'(hlt q)) ↔ (Graph.ofAdj vs adj).induced.Adj p q
  simp only [SimpleGraph.fromRel_adj, Graph.induced_adj, Graph.ofAdj_adj]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨fun hpq ↦ hne (by simp only [hpq]), hlt p, hlt q, ?_⟩
    rcases h with h1 | h2
    · simp [h1]
    · rw [hsym] at h2; simp [h2]
  · rintro ⟨_, _, _, hor⟩
    have h1 : adj vs[p.1] vs[q.1] = true := by
      rw [hsym vs[q.1] vs[p.1], Bool.or_self] at hor
      exact hor
    refine ⟨fun heq ↦ ?_, Or.inl h1⟩
    rw [heq, hirr] at h1
    cases h1

private theorem hasSemiInducedLadder_of_embedding {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ↪g H) {n : ℕ} (h : HasSemiInducedLadder G n) :
    HasSemiInducedLadder H n := by
  obtain ⟨a, b, hdisj, hadj⟩ := h
  refine ⟨e ∘ a, e ∘ b, ?_, fun i j ↦ e.map_rel_iff.trans (hadj i j)⟩
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hij⟩
  have hij' : e (b j) = e (a i) := hij
  exact Set.disjoint_left.mp hdisj ⟨i, rfl⟩ ⟨j, e.injective hij'⟩

private theorem not_hasSemiInducedLadder_of_subsingleton {V : Type*} [Subsingleton V]
    (G : SimpleGraph V) {n : ℕ} (hn : 1 ≤ n) : ¬ HasSemiInducedLadder G n := by
  rintro ⟨a, b, hdisj, -⟩
  let i₀ : Fin n := ⟨0, hn⟩
  exact Set.disjoint_left.mp hdisj ⟨i₀, rfl⟩ ⟨i₀, Subsingleton.elim (b i₀) (a i₀)⟩

end Helpers

/-! ### 2. Shared Vertex Encoding for Gadget Constructions -/

/-- Tagged gadget vertex used in the `Clique → DominatingSet` reductions. -/
@[ext]
structure GadgetVert where
  /-- Vertex role tag (`0` = selection clique vertex, `≥ 1` = guard/equality/non-edge witness). -/
  tag : ℕ
  /-- Primary part index (`< k`), encoded in unary. -/
  i : ℕ
  /-- Secondary part or side index, encoded in unary. -/
  j : ℕ
  /-- Primary vertex label in `G`, encoded in binary. -/
  u : ℕ
  /-- Secondary vertex label in `G`, encoded in binary. -/
  w : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed encoding of `GadgetVert` with unary indices `(tag, i, j)` and binary vertex labels
`(u, w)`. -/
enc_structure encGadgetVert : GadgetVert where
  tag : encUnary,
  i : encUnary,
  j : encUnary,
  u : encNat,
  w : encNat

attribute [local fun_prop] encGadgetVert_tag_polyTime encGadgetVert_i_polyTime
  encGadgetVert_j_polyTime encGadgetVert_u_polyTime encGadgetVert_w_polyTime
  encGadgetVert_mk_polyTime

/-! ### 3. Ladder-Free Reduction -/

section LadderFreeReduction

/-- Selection vertices (`tag = 0`) of the ladder-free reduction. -/
@[expose]
def ladSelVerts (G : Graph) (k : ℕ) : List GadgetVert :=
  (List.range k).flatMap fun i ↦ G.distinctVertices.map fun u ↦ ⟨0, i, 0, u, 0⟩

/-- Twin guard vertices (`tag = 1`) forcing one vertex per selection clique. -/
@[expose]
def ladGuardVerts (k : ℕ) : List GadgetVert :=
  (List.range k).flatMap fun i ↦ [⟨1, i, 0, 0, 0⟩, ⟨1, i, 1, 0, 0⟩]

/-- Non-edge witness vertices (`tag = 2`) for pairs `i < j < k` and non-adjacent `u, w` in `G`. -/
@[expose]
def ladNonedgeVerts (G : Graph) (k : ℕ) : List GadgetVert :=
  (List.range k).flatMap fun i ↦
    (List.range k).flatMap fun j ↦
      G.distinctVertices.flatMap fun u ↦
        G.distinctVertices.flatMap fun w ↦
          if decide (i < j) && !G.adjBool u w then [⟨2, i, j, u, w⟩] else []

/-- Full vertex list of the ladder-free `Clique → DominatingSet` gadget. -/
@[expose]
def ladVerts (G : Graph) (k : ℕ) : List GadgetVert :=
  ladSelVerts G k ++ ladGuardVerts k ++ ladNonedgeVerts G k

/-- Directed half of adjacency from a valid selection vertex (`tag = 0, j = 0, w = 0`) in the
ladder-free reduction. -/
@[expose]
def ladHalf (a b : GadgetVert) : Bool :=
  decide (a.tag = 0) && decide (a.j = 0) && decide (a.w = 0) &&
    ((decide (b.tag = 0) && decide (b.j = 0) && decide (b.w = 0) &&
        decide (a.i = b.i) && decide (a.u ≠ b.u)) ||
     (decide (b.tag = 1) && decide (a.i = b.i)) ||
     (decide (b.tag = 2) &&
       ((decide (a.i = b.i) && decide (a.u ≠ b.u)) ||
        (decide (a.i = b.j) && decide (a.u ≠ b.w)))))

private lemma ladHalf_eq_true_iff (a b : GadgetVert) :
    ladHalf a b = true ↔
      a.tag = 0 ∧ a.j = 0 ∧ a.w = 0 ∧
        ((b.tag = 0 ∧ b.j = 0 ∧ b.w = 0 ∧ a.i = b.i ∧ a.u ≠ b.u) ∨
         (b.tag = 1 ∧ a.i = b.i) ∨
         (b.tag = 2 ∧ ((a.i = b.i ∧ a.u ≠ b.u) ∨ (a.i = b.j ∧ a.u ≠ b.w)))) := by
  simp only [ladHalf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  tauto

/-- Symmetric irreflexive Boolean adjacency test on `GadgetVert` for the ladder-free reduction. -/
@[expose]
def ladAdj (a b : GadgetVert) : Bool :=
  ladHalf a b || ladHalf b a

private lemma ladAdj_symm (a b : GadgetVert) : ladAdj a b = ladAdj b a :=
  Bool.or_comm _ _

private lemma ladAdj_irrefl (a : GadgetVert) : ladAdj a a = false := by
  simp [ladAdj, ladHalf]
  omega

private lemma ladVerts_nodup (G : Graph) (k : ℕ) : (ladVerts G k).Nodup := by
  have hsel : (ladSelVerts G k).Nodup := by
    refine nodup_flatMap_disjoint List.nodup_range _
      (fun i _ ↦ G.nodup_distinctVertices.map fun u₁ u₂ h ↦ by injection h) ?_
    intro i₁ i₂ hne x hx₁ hx₂
    obtain ⟨u₁, -, rfl⟩ := List.mem_map.mp hx₁
    obtain ⟨u₂, -, h⟩ := List.mem_map.mp hx₂
    injection h; omega
  have hguard : (ladGuardVerts k).Nodup := by
    refine nodup_flatMap_disjoint List.nodup_range _ (fun _ _ ↦ by simp) ?_
    intro i₁ i₂ hne x hx₁ hx₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₁ hx₂
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h <;> (injection h; omega)
  have hnon : (ladNonedgeVerts G k).Nodup := by
    refine nodup_flatMap_disjoint List.nodup_range _ (fun i _ ↦ ?_) ?_
    · refine nodup_flatMap_disjoint List.nodup_range _ (fun j _ ↦ ?_) ?_
      · refine nodup_flatMap_disjoint G.nodup_distinctVertices _ (fun u _ ↦ ?_) ?_
        · refine nodup_flatMap_disjoint G.nodup_distinctVertices _ (fun w _ ↦ ?_) ?_
          · by_cases hc : (decide (i < j) && !G.adjBool u w) = true <;> simp [hc]
          · intro w₁ w₂ hne x hx₁ hx₂
            obtain ⟨_, rfl⟩ := mem_ite_singleton hx₁
            obtain ⟨_, h⟩ := mem_ite_singleton hx₂
            injection h; omega
        · intro u₁ u₂ hne x hx₁ hx₂
          obtain ⟨w₁, -, hx₁⟩ := List.mem_flatMap.mp hx₁
          obtain ⟨w₂, -, hx₂⟩ := List.mem_flatMap.mp hx₂
          obtain ⟨_, rfl⟩ := mem_ite_singleton hx₁
          obtain ⟨_, h⟩ := mem_ite_singleton hx₂
          injection h; omega
      · intro j₁ j₂ hne x hx₁ hx₂
        obtain ⟨u₁, -, hx₁⟩ := List.mem_flatMap.mp hx₁
        obtain ⟨w₁, -, hx₁⟩ := List.mem_flatMap.mp hx₁
        obtain ⟨u₂, -, hx₂⟩ := List.mem_flatMap.mp hx₂
        obtain ⟨w₂, -, hx₂⟩ := List.mem_flatMap.mp hx₂
        obtain ⟨_, rfl⟩ := mem_ite_singleton hx₁
        obtain ⟨_, h⟩ := mem_ite_singleton hx₂
        injection h; omega
    · intro i₁ i₂ hne x hx₁ hx₂
      obtain ⟨j₁, -, hx₁⟩ := List.mem_flatMap.mp hx₁
      obtain ⟨u₁, -, hx₁⟩ := List.mem_flatMap.mp hx₁
      obtain ⟨w₁, -, hx₁⟩ := List.mem_flatMap.mp hx₁
      obtain ⟨j₂, -, hx₂⟩ := List.mem_flatMap.mp hx₂
      obtain ⟨u₂, -, hx₂⟩ := List.mem_flatMap.mp hx₂
      obtain ⟨w₂, -, hx₂⟩ := List.mem_flatMap.mp hx₂
      obtain ⟨_, rfl⟩ := mem_ite_singleton hx₁
      obtain ⟨_, h⟩ := mem_ite_singleton hx₂
      injection h; omega
  have htag_sel : ∀ v ∈ ladSelVerts G k, v.tag = 0 := by
    intro v hv
    obtain ⟨_, -, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hv
    rfl
  have htag_guard : ∀ v ∈ ladGuardVerts k, v.tag = 1 := by
    intro v hv
    obtain ⟨_, -, hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rfl
    · simp only [List.mem_singleton] at hv; subst hv; rfl
  have htag_non : ∀ v ∈ ladNonedgeVerts G k, v.tag = 2 := by
    intro v hv
    obtain ⟨_, -, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨_, -, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨_, -, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨_, -, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨_, rfl⟩ := mem_ite_singleton hv
    rfl
  unfold ladVerts
  refine nodup_append_of_disjoint (nodup_append_of_disjoint hsel hguard fun x h1 h2 ↦ ?_) hnon
    fun x h12 h3 ↦ ?_
  · have := (htag_sel x h1).symm.trans (htag_guard x h2); omega
  · rcases List.mem_append.mp h12 with h1 | h2
    · have := (htag_sel x h1).symm.trans (htag_non x h3); omega
    · have := (htag_guard x h2).symm.trans (htag_non x h3); omega

/-- Universal simple graph on `GadgetVert` induced by `ladAdj`. -/
private def ladUnivGraph : SimpleGraph GadgetVert :=
  SimpleGraph.fromRel fun a b ↦ ladAdj a b = true

private lemma ladUnivGraph_adj_iff (a b : GadgetVert) :
    ladUnivGraph.Adj a b ↔ ladAdj a b = true := by
  simp only [ladUnivGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun ⟨_, h⟩ ↦ h.elim id (fun hba ↦ ladAdj_symm a b ▸ hba), fun hab ↦ ⟨?_, Or.inl hab⟩⟩
  intro rfl
  rw [ladAdj_irrefl] at hab
  cases hab

private lemma not_lad_sel_vs_nonedge (a b : Fin 6 → GadgetVert)
    (ha_tag : ∀ t, (a t).tag = 0) (hb_tag : ∀ t, (b t).tag ≠ 0 ∧ (b t).tag ≠ 1)
    (hlad : ∀ r s : Fin 6, ladUnivGraph.Adj (a r) (b s) ↔ s < r) : False := by
  have ha_inj : Function.Injective a := by
    intro r₁ r₂ heq
    rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
    · have h1 : ladUnivGraph.Adj (a r₂) (b r₁) := (hlad r₂ r₁).mpr hlt
      rw [← heq] at h1
      exact False.elim (lt_irrefl r₁ ((hlad r₁ r₁).mp h1))
    · rfl
    · have h1 : ladUnivGraph.Adj (a r₁) (b r₂) := (hlad r₁ r₂).mpr hgt
      rw [heq] at h1
      exact False.elim (lt_irrefl r₂ ((hlad r₂ r₂).mp h1))
  have hadj0 : ∀ r : Fin 5, ladHalf (a r.succ) (b 0) = true := by
    intro r
    have h := (ladUnivGraph_adj_iff _ _).mp ((hlad r.succ 0).mpr (Fin.succ_pos r))
    rw [ladAdj, Bool.or_eq_true] at h
    exact h.resolve_right (by have hb0 := (hb_tag 0).1; simp [ladHalf, hb0])
  have hside_or : ∀ r : Fin 5, (a r.succ).i = (b 0).i ∨ (a r.succ).i = (b 0).j := by
    intro r
    obtain ⟨_, _, _, hc⟩ := (ladHalf_eq_true_iff _ _).mp (hadj0 r)
    rcases hc with ⟨hb0, _⟩ | ⟨hb1, _⟩ | ⟨_, h2⟩
    · exact False.elim ((hb_tag 0).1 hb0)
    · exact False.elim ((hb_tag 0).2 hb1)
    · exact h2.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left)
  let side : Fin 5 → Bool := fun r ↦ decide ((a r.succ).i = (b 0).i)
  obtain ⟨flag, hflag_card⟩ := exists_fiber_card_ge side 2 (by decide)
  obtain ⟨S₃, hS₃_sub, hS₃_card⟩ := exists_subset_card_eq hflag_card
  let emb : Fin 3 ↪o Fin 5 := S₃.orderEmbOfFin hS₃_card
  let t₀ : Fin 6 := (emb 0).succ
  let t₁ : Fin 6 := (emb 1).succ
  let t₂ : Fin 6 := (emb 2).succ
  have ht₀₁ : t₀ < t₁ := Fin.succ_lt_succ_iff.mpr (emb.strictMono (by decide))
  have ht₁₂ : t₁ < t₂ := Fin.succ_lt_succ_iff.mpr (emb.strictMono (by decide))
  have hsame_part : ∀ x : Fin 3,
      (a (emb x).succ).i = if flag then (b 0).i else (b 0).j := by
    intro x
    have hx : side (emb x) = flag := (mem_filter.mp (hS₃_sub (S₃.orderEmbOfFin_mem hS₃_card x))).2
    cases flag
    · exact (hside_or (emb x)).resolve_left (of_decide_eq_false hx)
    · exact of_decide_eq_true hx
  set p := if flag then (b 0).i else (b 0).j
  have hp₀ : (a t₀).i = p := hsame_part 0
  have hp₁ : (a t₁).i = p := hsame_part 1
  have hp₂ : (a t₂).i = p := hsame_part 2
  have hvalid₀ : (a t₀).j = 0 ∧ (a t₀).w = 0 := by
    obtain ⟨_, hj, hw, _⟩ := (ladHalf_eq_true_iff _ _).mp (hadj0 (emb 0))
    exact ⟨hj, hw⟩
  have hvalid₁ : (a t₁).j = 0 ∧ (a t₁).w = 0 := by
    obtain ⟨_, hj, hw, _⟩ := (ladHalf_eq_true_iff _ _).mp (hadj0 (emb 1))
    exact ⟨hj, hw⟩
  have hu_ne : (a t₀).u ≠ (a t₁).u := by
    intro heq
    apply ht₀₁.ne
    apply ha_inj
    ext
    · exact (ha_tag t₀).trans (ha_tag t₁).symm
    · exact hp₀.trans hp₁.symm
    · exact hvalid₀.1.trans hvalid₁.1.symm
    · exact heq
    · exact hvalid₀.2.trans hvalid₁.2.symm
  have hadj_21 : ladHalf (a t₂) (b t₁) = true := by
    have h := (ladUnivGraph_adj_iff _ _).mp ((hlad t₂ t₁).mpr ht₁₂)
    rw [ladAdj, Bool.or_eq_true] at h
    exact h.resolve_right (by have hb1 := (hb_tag t₁).1; simp [ladHalf, hb1])
  have hb1_info : (b t₁).tag = 2 ∧ (p = (b t₁).i ∨ p = (b t₁).j) := by
    obtain ⟨_, _, _, hc⟩ := (ladHalf_eq_true_iff _ _).mp hadj_21
    rcases hc with ⟨hb0, _⟩ | ⟨hb1, _⟩ | ⟨hb2, h2⟩
    · exact False.elim ((hb_tag t₁).1 hb0)
    · exact False.elim ((hb_tag t₁).2 hb1)
    · refine ⟨hb2, ?_⟩
      rcases h2 with ⟨hi, _⟩ | ⟨hj, _⟩
      · exact Or.inl (hp₂.symm.trans hi)
      · exact Or.inr (hp₂.symm.trans hj)
  have hnot_01 : ladHalf (a t₀) (b t₁) = false := by
    have h := (ladUnivGraph_adj_iff _ _).not.mp ((hlad t₀ t₁).not.mpr (not_lt.mpr ht₀₁.le))
    rw [Bool.not_eq_true, ladAdj, Bool.or_eq_false_iff] at h
    exact h.1
  have hnot_11 : ladHalf (a t₁) (b t₁) = false := by
    have h := (ladUnivGraph_adj_iff _ _).not.mp ((hlad t₁ t₁).not.mpr (lt_irrefl t₁))
    rw [Bool.not_eq_true, ladAdj, Bool.or_eq_false_iff] at h
    exact h.1
  rcases hb1_info.2 with hpi | hpj
  · have hu₀ : (a t₀).u = (b t₁).u := by
      by_contra hne_u
      have htrue : ladHalf (a t₀) (b t₁) = true :=
        (ladHalf_eq_true_iff _ _).mpr ⟨ha_tag t₀, hvalid₀.1, hvalid₀.2,
          Or.inr (Or.inr ⟨hb1_info.1, Or.inl ⟨hp₀.trans hpi, hne_u⟩⟩)⟩
      rw [htrue] at hnot_01; cases hnot_01
    have hu₁ : (a t₁).u = (b t₁).u := by
      by_contra hne_u
      have htrue : ladHalf (a t₁) (b t₁) = true :=
        (ladHalf_eq_true_iff _ _).mpr ⟨ha_tag t₁, hvalid₁.1, hvalid₁.2,
          Or.inr (Or.inr ⟨hb1_info.1, Or.inl ⟨hp₁.trans hpi, hne_u⟩⟩)⟩
      rw [htrue] at hnot_11; cases hnot_11
    exact hu_ne (hu₀.trans hu₁.symm)
  · have hu₀ : (a t₀).u = (b t₁).w := by
      by_contra hne_w
      have htrue : ladHalf (a t₀) (b t₁) = true :=
        (ladHalf_eq_true_iff _ _).mpr ⟨ha_tag t₀, hvalid₀.1, hvalid₀.2,
          Or.inr (Or.inr ⟨hb1_info.1, Or.inr ⟨hp₀.trans hpj, hne_w⟩⟩)⟩
      rw [htrue] at hnot_01; cases hnot_01
    have hu₁ : (a t₁).u = (b t₁).w := by
      by_contra hne_w
      have htrue : ladHalf (a t₁) (b t₁) = true :=
        (ladHalf_eq_true_iff _ _).mpr ⟨ha_tag t₁, hvalid₁.1, hvalid₁.2,
          Or.inr (Or.inr ⟨hb1_info.1, Or.inr ⟨hp₁.trans hpj, hne_w⟩⟩)⟩
      rw [htrue] at hnot_11; cases hnot_11
    exact hu_ne (hu₀.trans hu₁.symm)

private theorem not_hasSemiInducedLadder_ladUnivGraph : ¬ HasSemiInducedLadder ladUnivGraph 46 := by
  intro h46
  obtain ⟨a₀, b₀, hdisj, hlad₀⟩ := h46
  let classify : GadgetVert → Fin 3 := fun v ↦
    if v.tag = 0 then 0 else if v.tag = 1 then 1 else 2
  let color : Fin 46 → Fin 3 × Fin 3 := fun t ↦ (classify (a₀ t), classify (b₀ t))
  obtain ⟨⟨ca, cb⟩, hcard⟩ := exists_fiber_card_ge color 5 (by decide)
  obtain ⟨S₆, hS₆_sub, hS₆_card⟩ := exists_subset_card_eq hcard
  let emb : Fin 6 ↪o Fin 46 := S₆.orderEmbOfFin hS₆_card
  let a : Fin 6 → GadgetVert := a₀ ∘ emb
  let b : Fin 6 → GadgetVert := b₀ ∘ emb
  have hne_ab : ∀ r s : Fin 6, a r ≠ b s :=
    fun r s heq ↦ Set.disjoint_left.mp hdisj ⟨emb r, rfl⟩ ⟨emb s, heq.symm⟩
  have hlad : ∀ r s : Fin 6, ladUnivGraph.Adj (a r) (b s) ↔ s < r :=
    fun r s ↦ (hlad₀ (emb r) (emb s)).trans emb.strictMono.lt_iff_lt
  have hcol : ∀ t : Fin 6, classify (a t) = ca ∧ classify (b t) = cb := by
    intro t
    exact Prod.mk.inj (mem_filter.mp (hS₆_sub (S₆.orderEmbOfFin_mem hS₆_card t))).2
  have hc0 : ∀ {v : GadgetVert} {hlt : 0 < 3}, classify v = ⟨0, hlt⟩ → v.tag = 0 := by
    intro v _ hv; dsimp [classify] at hv; split_ifs at hv <;> first | assumption | nomatch hv
  have hc1 : ∀ {v : GadgetVert} {hlt : 1 < 3}, classify v = ⟨1, hlt⟩ → v.tag = 1 := by
    intro v _ hv; dsimp [classify] at hv; split_ifs at hv <;> first | assumption | nomatch hv
  have hc2 : ∀ {v : GadgetVert} {hlt : 2 < 3}, classify v = ⟨2, hlt⟩ → v.tag ≠ 0 ∧ v.tag ≠ 1 := by
    intro v _ hv; dsimp [classify] at hv
    split_ifs at hv with h0 h1
    · nomatch hv
    · nomatch hv
    · exact ⟨h0, h1⟩
  rcases ca with ⟨_ | _ | _ | _, hca⟩ <;> rcases cb with ⟨_ | _ | _ | _, hcb⟩
  · -- (0, 0): selection vs selection
    have ha_t : ∀ t, (a t).tag = 0 := fun t ↦ hc0 (hcol t).1
    have hb_t : ∀ t, (b t).tag = 0 := fun t ↦ hc0 (hcol t).2
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    have h20 := (ladUnivGraph_adj_iff _ _).mp ((hlad 2 0).mpr (by decide))
    have h21 := (ladUnivGraph_adj_iff _ _).mp ((hlad 2 1).mpr (by decide))
    have h11 := (ladUnivGraph_adj_iff _ _).not.mp ((hlad 1 1).not.mpr (by decide))
    rw [ladAdj, Bool.or_eq_true, ladHalf_eq_true_iff, ladHalf_eq_true_iff] at h10 h20 h21
    have hp10 : (a 1).j = 0 ∧ (a 1).w = 0 ∧ (a 1).i = (b 0).i := by
      have ha1 := ha_t 1; have hb0 := hb_t 0
      rcases h10 with ⟨_, hj, hw, ⟨_, _, _, hi, _⟩ | ⟨hb1, _⟩ | ⟨hb2, _⟩⟩ |
          ⟨_, _, _, ⟨_, hj, hw, hi, _⟩ | ⟨hb1, _⟩ | ⟨hb2, _⟩⟩
      · exact ⟨hj, hw, hi⟩
      · omega
      · omega
      · exact ⟨hj, hw, hi.symm⟩
      · omega
      · omega
    have hp20 : (a 2).i = (b 0).i := by
      have ha2 := ha_t 2; have hb0 := hb_t 0
      rcases h20 with ⟨_, _, _, ⟨_, _, _, hi, _⟩ | ⟨hb1, _⟩ | ⟨hb2, _⟩⟩ |
          ⟨_, _, _, ⟨_, _, _, hi, _⟩ | ⟨hb1, _⟩ | ⟨hb2, _⟩⟩ <;> omega
    have hp21 : (b 1).j = 0 ∧ (b 1).w = 0 ∧ (a 2).i = (b 1).i := by
      have ha2 := ha_t 2; have hb1 := hb_t 1
      rcases h21 with ⟨_, _, _, ⟨_, hj, hw, hi, _⟩ | ⟨hbad, _⟩ | ⟨hbad, _⟩⟩ |
          ⟨_, hj, hw, ⟨_, _, _, hi, _⟩ | ⟨hbad, _⟩ | ⟨hbad, _⟩⟩
      · exact ⟨hj, hw, hi⟩
      · omega
      · omega
      · exact ⟨hj, hw, hi.symm⟩
      · omega
      · omega
    have hi_eq : (a 1).i = (b 1).i := hp10.2.2.trans (hp20.symm.trans hp21.2.2)
    have hu_ne : (a 1).u ≠ (b 1).u := by
      intro hu
      apply hne_ab 1 1
      ext
      · exact (ha_t 1).trans (hb_t 1).symm
      · exact hi_eq
      · exact hp10.1.trans hp21.1.symm
      · exact hu
      · exact hp10.2.1.trans hp21.2.1.symm
    refine h11 ?_
    rw [ladAdj, Bool.or_eq_true]
    exact Or.inl ((ladHalf_eq_true_iff _ _).mpr ⟨ha_t 1, hp10.1, hp10.2.1,
      Or.inl ⟨hb_t 1, hp21.1, hp21.2.1, hi_eq, hu_ne⟩⟩)
  · -- (0, 1): selection vs guard
    have ha1 := hc0 (hcol 1).1; have ha2 := hc0 (hcol 2).1
    have hb0 := hc1 (hcol 0).2; have hb1 := hc1 (hcol 1).2
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    have h20 := (ladUnivGraph_adj_iff _ _).mp ((hlad 2 0).mpr (by decide))
    have h21 := (ladUnivGraph_adj_iff _ _).mp ((hlad 2 1).mpr (by decide))
    have h11 := (ladUnivGraph_adj_iff _ _).not.mp ((hlad 1 1).not.mpr (by decide))
    simp [ladAdj, ladHalf, ha1, ha2, hb0, hb1] at h10 h20 h21 h11
    omega
  · -- (0, 2): selection vs non-edge
    exact not_lad_sel_vs_nonedge a b (fun t ↦ hc0 (hcol t).1) (fun t ↦ hc2 (hcol t).2) hlad
  · omega
  · -- (1, 0): guard vs selection
    have ha1 := hc1 (hcol 1).1; have ha2 := hc1 (hcol 2).1
    have hb0 := hc0 (hcol 0).2; have hb1 := hc0 (hcol 1).2
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    have h20 := (ladUnivGraph_adj_iff _ _).mp ((hlad 2 0).mpr (by decide))
    have h21 := (ladUnivGraph_adj_iff _ _).mp ((hlad 2 1).mpr (by decide))
    have h11 := (ladUnivGraph_adj_iff _ _).not.mp ((hlad 1 1).not.mpr (by decide))
    simp [ladAdj, ladHalf, ha1, ha2, hb0, hb1] at h10 h20 h21 h11
    omega
  · -- (1, 1)
    have ha1 : (a 1).tag ≠ 0 := by have := hc1 (hcol 1).1; omega
    have hb0 : (b 0).tag ≠ 0 := by have := hc1 (hcol 0).2; omega
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    simp [ladAdj, ladHalf, ha1, hb0] at h10
  · -- (1, 2)
    have ha1 : (a 1).tag ≠ 0 := by have := hc1 (hcol 1).1; omega
    have hb0 : (b 0).tag ≠ 0 := (hc2 (hcol 0).2).1
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    simp [ladAdj, ladHalf, ha1, hb0] at h10
  · omega
  · -- (2, 0): non-edge vs selection (dual via Fin.rev)
    refine not_lad_sel_vs_nonedge (fun t ↦ b t.rev) (fun t ↦ a t.rev)
      (fun t ↦ hc0 (hcol t.rev).2) (fun t ↦ hc2 (hcol t.rev).1) fun r s ↦ ?_
    rw [adj_comm, hlad s.rev r.rev, Fin.rev_lt_rev]
  · -- (2, 1)
    have ha1 : (a 1).tag ≠ 0 := (hc2 (hcol 1).1).1
    have hb0 : (b 0).tag ≠ 0 := by have := hc1 (hcol 0).2; omega
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    simp [ladAdj, ladHalf, ha1, hb0] at h10
  · -- (2, 2)
    have ha1 : (a 1).tag ≠ 0 := (hc2 (hcol 1).1).1
    have hb0 : (b 0).tag ≠ 0 := (hc2 (hcol 0).2).1
    have h10 := (ladUnivGraph_adj_iff _ _).mp ((hlad 1 0).mpr (by decide))
    simp [ladAdj, ladHalf, ha1, hb0] at h10
  · omega
  · omega
  · omega
  · omega
  · omega

/-- Every graph `Graph.ofAdj (ladVerts G k) ladAdj` forbids semi-induced ladders of order `46`. -/
theorem not_hasSemiInducedLadder_ladOfAdj (G : Graph) (k : ℕ) :
    ¬ HasSemiInducedLadder (Graph.ofAdj (ladVerts G k) ladAdj).induced 46 := by
  obtain ⟨emb⟩ := ofAdj_induced_embedding (ladVerts_nodup G k) ladAdj_symm ladAdj_irrefl
  exact fun h ↦ not_hasSemiInducedLadder_ladUnivGraph (hasSemiInducedLadder_of_embedding emb h)

/-- Polynomial-time parameterized reduction from `Clique` to `DominatingSet` producing graphs with
no semi-induced ladder of order `46`. -/
@[expose]
def cliqueToLadDomSet (x : CliqueInstance) : DominatingSetInstance :=
  let kk := min x.graph.distinctVertices.length x.m
  if decide (x.m = 0) then ⟨⟨[], []⟩, 0⟩
  else if decide (x.m ≤ x.graph.distinctVertices.length) then
    ⟨Graph.ofAdj (ladVerts x.graph kk) ladAdj, x.m⟩
  else ⟨⟨[0], []⟩, 0⟩

/-- Parameter bound of `cliqueToLadDomSet`: `(cliqueToLadDomSet x).bound ≤ x.m`. -/
theorem cliqueToLadDomSet_bound_le (x : CliqueInstance) :
    (cliqueToLadDomSet x).bound ≤ x.m := by
  by_cases h0 : x.m = 0
  · simp [cliqueToLadDomSet, h0]
  · by_cases hle : x.m ≤ x.graph.distinctVertices.length <;> simp [cliqueToLadDomSet, h0, hle]

/-- Every output of `cliqueToLadDomSet` forbids semi-induced ladders of order `46`. -/
theorem not_hasSemiInducedLadder_cliqueToLadDomSet (x : CliqueInstance) :
    ¬ HasSemiInducedLadder (cliqueToLadDomSet x).graph.induced 46 := by
  by_cases h0 : x.m = 0
  · have hd : cliqueToLadDomSet x = ⟨⟨[], []⟩, 0⟩ := by simp [cliqueToLadDomSet, h0]
    rw [hd]
    have : Subsingleton {v // v ∈ ([] : List ℕ)} := ⟨fun a ↦ nomatch a.2⟩
    exact not_hasSemiInducedLadder_of_subsingleton _ (by omega)
  · by_cases hle : x.m ≤ x.graph.distinctVertices.length
    · have hd : cliqueToLadDomSet x =
          ⟨Graph.ofAdj (ladVerts x.graph (min x.graph.distinctVertices.length x.m)) ladAdj,
            x.m⟩ := by simp [cliqueToLadDomSet, h0, hle]
      rw [hd]
      exact not_hasSemiInducedLadder_ladOfAdj _ _
    · have hd : cliqueToLadDomSet x = ⟨⟨[0], []⟩, 0⟩ := by simp [cliqueToLadDomSet, h0, hle]
      rw [hd]
      have : Subsingleton {v // v ∈ ([0] : List ℕ)} :=
        ⟨fun ⟨_, ha⟩ ⟨_, hb⟩ ↦
          Subtype.ext ((List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm)⟩
      exact not_hasSemiInducedLadder_of_subsingleton _ (by omega)

/-- Correctness of `cliqueToLadDomSet`: `x ∈ Clique ↔ cliqueToLadDomSet x ∈ DominatingSet`. -/
theorem cliqueToLadDomSet_mem_iff (x : CliqueInstance) :
    x ∈ Clique ↔ cliqueToLadDomSet x ∈ DominatingSet := by
  classical
  obtain ⟨G, k⟩ := x
  simp only [cliqueToLadDomSet]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [decide_true, ↓reduceIte, mem_Clique_iff_mk, mem_DominatingSet_iff]
    exact ⟨fun _ ↦ ⟨∅, by simp, by simp, rfl⟩,
      fun _ ↦ ⟨∅, by simp, ⟨by simp, rfl⟩⟩⟩
  · simp only [hk0, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hkn : k ≤ G.distinctVertices.length
    · simp only [hkn, decide_true, ↓reduceIte, Nat.min_eq_right hkn]
      set vs := ladVerts G k
      have hnd : vs.Nodup := ladVerts_nodup G k
      have hmem_sel : ∀ {i u : ℕ}, i < k → u ∈ G.distinctVertices →
          (⟨0, i, 0, u, 0⟩ : GadgetVert) ∈ vs := by
        intro i u hi hu
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨u, hu, rfl⟩⟩))
      have hmem_guard : ∀ {i b : ℕ}, i < k → (b = 0 ∨ b = 1) →
          (⟨1, i, b, 0, 0⟩ : GadgetVert) ∈ vs := by
        intro i b hi hb
        refine List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩))
        rcases hb with rfl | rfl <;> simp
      have hmem_non : ∀ {i j u w : ℕ}, i < j → j < k →
          u ∈ G.distinctVertices → w ∈ G.distinctVertices → G.adjBool u w = false →
          (⟨2, i, j, u, w⟩ : GadgetVert) ∈ vs := by
        intro i j u w hij hjk hu hw hnadj
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (hij.trans hjk),
          List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hjk,
            List.mem_flatMap.mpr ⟨u, hu, List.mem_flatMap.mpr ⟨w, hw, ?_⟩⟩⟩⟩)
        simp [hij, hnadj]
      rw [mem_Clique_iff_mk, mem_DominatingSet_iff]
      constructor
      · rintro ⟨S, hSV, hScl, hScard⟩
        let emb : Fin k ↪o ℕ := S.orderEmbOfFin hScard
        have hemb_mem : ∀ r : Fin k, emb r ∈ G.distinctVertices :=
          fun r ↦ G.mem_distinctVertices.mpr (hSV _ (S.orderEmbOfFin_mem hScard r))
        let pos : Fin k → ℕ := fun r ↦ vs.idxOf ⟨0, r.1, 0, emb r, 0⟩
        have hpos_lt : ∀ r : Fin k, pos r < vs.length :=
          fun r ↦ List.idxOf_lt_length_of_mem (hmem_sel r.isLt (hemb_mem r))
        have hpos_get : ∀ r : Fin k, vs[pos r]'(hpos_lt r) = ⟨0, r.1, 0, emb r, 0⟩ :=
          fun r ↦ List.getElem_idxOf (hpos_lt r)
        have hpos_inj : Function.Injective pos := by
          intro r₁ r₂ heq
          have hg : vs[pos r₁]'(hpos_lt r₁) = vs[pos r₂]'(hpos_lt r₂) := by simp only [heq]
          have hh := (hpos_get r₁).symm.trans (hg.trans (hpos_get r₂))
          exact Fin.ext (by injection hh)
        let D : Finset ℕ := univ.image pos
        refine ⟨D, fun p hp ↦ ?_, fun q hq ↦ ?_, by rw [card_image_of_injective _ hpos_inj,
          card_fin]⟩
        · obtain ⟨r, -, rfl⟩ := mem_image.mp hp
          exact List.mem_range.mpr (hpos_lt r)
        · have hq_lt : q < vs.length := List.mem_range.mp hq
          have hvq : vs[q] ∈ vs := List.getElem_mem hq_lt
          rcases List.mem_append.mp hvq with hv12 | hv3
          · rcases List.mem_append.mp hv12 with hv1 | hv2
            · obtain ⟨i, hi_r, hv1⟩ := List.mem_flatMap.mp hv1
              obtain ⟨u, _, hveq⟩ := List.mem_map.mp hv1
              let r : Fin k := ⟨i, List.mem_range.mp hi_r⟩
              by_cases hur : u = emb r
              · refine Or.inl (mem_image.mpr ⟨r, mem_univ r, ?_⟩)
                apply (hnd.getElem_inj_iff (hi := hpos_lt r) (hj := hq_lt)).mp
                rw [hpos_get r, ← hveq, hur]
              · refine Or.inr ⟨pos r, mem_image_of_mem pos (mem_univ r), ?_⟩
                rw [Graph.ofAdj_adj]
                refine ⟨fun heq ↦ hur ?_, hq_lt, hpos_lt r, ?_⟩
                · subst heq
                  have := (hpos_get r).symm.trans hveq.symm
                  injection this; omega
                · simp [← hveq, hpos_get r, ladAdj, ladHalf, r, hur]
            · obtain ⟨i, hi_r, hv2⟩ := List.mem_flatMap.mp hv2
              let r : Fin k := ⟨i, List.mem_range.mp hi_r⟩
              refine Or.inr ⟨pos r, mem_image_of_mem pos (mem_univ r), ?_⟩
              rw [Graph.ofAdj_adj]
              rcases List.mem_cons.mp hv2 with hveq | hv2'
              · refine ⟨fun heq ↦ ?_, hq_lt, hpos_lt r, ?_⟩
                · subst heq; have := (hpos_get r).symm.trans hveq; injection this; omega
                · simp [hveq, hpos_get r, ladAdj, ladHalf, r]
              · simp only [List.mem_singleton] at hv2'
                refine ⟨fun heq ↦ ?_, hq_lt, hpos_lt r, ?_⟩
                · subst heq; have := (hpos_get r).symm.trans hv2'; injection this; omega
                · simp [hv2', hpos_get r, ladAdj, ladHalf, r]
          · obtain ⟨i, hi_r, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨j, hj_r, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨u, _, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨w, _, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨hcond, hv3⟩ := mem_ite_singleton hv3
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcond
            let ri : Fin k := ⟨i, List.mem_range.mp hi_r⟩
            let rj : Fin k := ⟨j, List.mem_range.mp hj_r⟩
            have hnot_both : ¬ (emb ri = u ∧ emb rj = w) := by
              rintro ⟨hu_eq, hw_eq⟩
              have hadj_uw : G.toSimpleGraph.Adj u w := by
                rw [← hu_eq, ← hw_eq]
                exact hScl (S.orderEmbOfFin_mem hScard ri) (S.orderEmbOfFin_mem hScard rj)
                  (emb.injective.ne (Fin.ne_of_lt hcond.1))
              have htrue := (G.adjBool_eq_true_iff u w).mpr hadj_uw
              rw [hcond.2] at htrue; cases htrue
            by_cases hui : emb ri ≠ u
            · refine Or.inr ⟨pos ri, mem_image_of_mem pos (mem_univ ri), ?_⟩
              rw [Graph.ofAdj_adj]
              refine ⟨fun heq ↦ ?_, hq_lt, hpos_lt ri, ?_⟩
              · subst heq; have := (hpos_get ri).symm.trans hv3; injection this; omega
              · simp [hv3, hpos_get ri, ladAdj, ladHalf, ri, hui]
            · push Not at hui
              have hwj : emb rj ≠ w := fun hw ↦ hnot_both ⟨hui, hw⟩
              refine Or.inr ⟨pos rj, mem_image_of_mem pos (mem_univ rj), ?_⟩
              rw [Graph.ofAdj_adj]
              refine ⟨fun heq ↦ ?_, hq_lt, hpos_lt rj, ?_⟩
              · subst heq; have := (hpos_get rj).symm.trans hv3; injection this; omega
              · simp [hv3, hpos_get rj, ladAdj, ladHalf, rj, hwj]
      · rintro ⟨D, hDV, hDdom, hDcard⟩
        have hD_lt : ∀ p ∈ D, p < vs.length := fun p hp ↦ List.mem_range.mp (hDV p hp)
        let partOf : ℕ → ℕ := fun p ↦
          if hp : p < vs.length then
            if vs[p].tag ≤ 1 then vs[p].i else k
          else k
        let slice : Fin k → Finset ℕ := fun r ↦ D.filter fun p ↦ partOf p = r.1
        have hguard_dom : ∀ (r : Fin k) (b : ℕ), (b = 0 ∨ b = 1) →
            ∃ p, ∃ hp : p ∈ slice r, vs[p]'(hD_lt p (mem_filter.mp hp).1) = ⟨1, r.1, b, 0, 0⟩ ∨
              (vs[p]'(hD_lt p (mem_filter.mp hp).1)).tag = 0 := by
          intro r b hb
          let q := vs.idxOf ⟨1, r.1, b, 0, 0⟩
          have hq_lt : q < vs.length := List.idxOf_lt_length_of_mem (hmem_guard r.isLt hb)
          have hq_get : vs[q] = ⟨1, r.1, b, 0, 0⟩ := List.getElem_idxOf hq_lt
          rcases hDdom q (List.mem_range.mpr hq_lt) with hqD | ⟨p, hpD, hadj⟩
          · refine ⟨q, mem_filter.mpr ⟨hqD, ?_⟩, Or.inl hq_get⟩
            simp [partOf, hq_lt, hq_get]
          · rw [Graph.ofAdj_adj] at hadj
            obtain ⟨_, _, hp_lt, hor⟩ := hadj
            rw [hq_get, ladAdj_symm _ vs[p], Bool.or_self, ladAdj, Bool.or_eq_true] at hor
            have hp_info : vs[p].tag = 0 ∧ vs[p].i = r.1 := by
              rcases hor with h1 | h2
              · obtain ⟨ht0, _, _, hc⟩ := (ladHalf_eq_true_iff _ _).mp h1
                rcases hc with ⟨hb0, _⟩ | ⟨_, hpi⟩ | ⟨hb2, _⟩
                · simp at hb0
                · exact ⟨ht0, hpi⟩
                · simp at hb2
              · simp [ladHalf] at h2
            refine ⟨p, mem_filter.mpr ⟨hpD, ?_⟩, Or.inr hp_info.1⟩
            simp [partOf, hp_lt, hp_info.1, hp_info.2]
        have hslice_pos : ∀ r : Fin k, 1 ≤ #(slice r) := by
          intro r
          obtain ⟨p, hp, _⟩ := hguard_dom r 0 (Or.inl rfl)
          exact card_pos.mpr ⟨p, hp⟩
        have hdisj_slice : ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint slice :=
          fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun _ hp₁ hp₂ ↦
            hne (Fin.ext ((mem_filter.mp hp₁).2.symm.trans (mem_filter.mp hp₂).2))
        let U := (univ : Finset (Fin k)).biUnion slice
        have hU_sub : U ⊆ D := biUnion_subset.mpr fun _ _ ↦ filter_subset _ _
        have hsum_le : ∑ r : Fin k, #(slice r) ≤ k :=
          (card_biUnion hdisj_slice).symm.trans_le ((card_le_card hU_sub).trans_eq hDcard)
        have hslice_eq_one : ∀ r : Fin k, #(slice r) = 1 := by
          intro r
          by_contra hne1
          have hge2 : 2 ≤ #(slice r) := by have := hslice_pos r; omega
          have hgt : k < ∑ r' : Fin k, #(slice r') := by
            calc k = ∑ _ : Fin k, 1 := by simp
              _ < ∑ r' : Fin k, #(slice r') :=
                  sum_lt_sum (fun r' _ ↦ hslice_pos r') ⟨r, mem_univ r, hge2⟩
          omega
        have hU_eq_D : U = D := by
          apply eq_of_subset_of_card_le hU_sub
          rw [card_biUnion hdisj_slice, hDcard]
          simp [hslice_eq_one]
        have hex_sel : ∀ r : Fin k, ∃ p, ∃ hp : p ∈ slice r,
            ∃ u ∈ G.distinctVertices, vs[p]'(hD_lt p (mem_filter.mp hp).1) =
              ⟨0, r.1, 0, u, 0⟩ := by
          intro r
          obtain ⟨p₀, hp₀, hc₀⟩ := hguard_dom r 0 (Or.inl rfl)
          obtain ⟨p₁, hp₁, hc₁⟩ := hguard_dom r 1 (Or.inr rfl)
          have hp_eq : p₀ = p₁ := card_le_one.mp (hslice_eq_one r).le p₀ hp₀ p₁ hp₁
          subst hp_eq
          have htag0 : (vs[p₀]'(hD_lt p₀ (mem_filter.mp hp₀).1)).tag = 0 := by
            rcases hc₀ with h0 | h0
            · rcases hc₁ with h1 | h1
              · have := h0.symm.trans h1; injection this with _ _ hb; omega
              · exact h1
            · exact h0
          have hvp : vs[p₀]'(hD_lt p₀ (mem_filter.mp hp₀).1) ∈ vs := List.getElem_mem _
          rcases List.mem_append.mp hvp with hv12 | hv3
          · rcases List.mem_append.mp hv12 with hv1 | hv2
            · obtain ⟨_, -, hv1⟩ := List.mem_flatMap.mp hv1
              obtain ⟨u, hu, hveq⟩ := List.mem_map.mp hv1
              have hp0_lt := hD_lt p₀ (mem_filter.mp hp₀).1
              have hpart : partOf p₀ = r.1 := (mem_filter.mp hp₀).2
              simp only [partOf, hp0_lt, ↓reduceDIte, ← hveq] at hpart
              simp only [Nat.zero_le, ↓reduceIte] at hpart
              exact ⟨p₀, hp₀, u, hu, by rw [← hveq, hpart]⟩
            · obtain ⟨_, -, hv2⟩ := List.mem_flatMap.mp hv2
              rcases List.mem_cons.mp hv2 with h | h <;> simp_all
          · obtain ⟨_, -, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨_, -, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨_, -, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨_, -, hv3⟩ := List.mem_flatMap.mp hv3
            obtain ⟨_, hv3⟩ := mem_ite_singleton hv3
            rw [hv3] at htag0; cases htag0
        choose pSel hpSel uSel huSel hvSel using hex_sel
        have hD_is_pSel : ∀ p ∈ D, ∃ r : Fin k, p = pSel r := by
          intro p hpD
          rw [← hU_eq_D, mem_biUnion] at hpD
          obtain ⟨r, -, hpr⟩ := hpD
          exact ⟨r, card_le_one.mp (hslice_eq_one r).le p hpr (pSel r) (hpSel r)⟩
        have hadj_pair : ∀ r₁ r₂ : Fin k, r₁ < r₂ → G.toSimpleGraph.Adj (uSel r₁) (uSel r₂) := by
          intro r₁ r₂ hlt
          by_contra hnadj
          have hb_false : G.adjBool (uSel r₁) (uSel r₂) = false :=
            (G.adjBool_eq_false_iff _ _).mpr hnadj
          let q := vs.idxOf ⟨2, r₁.1, r₂.1, uSel r₁, uSel r₂⟩
          have hq_lt : q < vs.length :=
            List.idxOf_lt_length_of_mem (hmem_non hlt r₂.isLt (huSel r₁) (huSel r₂) hb_false)
          have hq_get : vs[q] = ⟨2, r₁.1, r₂.1, uSel r₁, uSel r₂⟩ := List.getElem_idxOf hq_lt
          rcases hDdom q (List.mem_range.mpr hq_lt) with hqD | ⟨p, hpD, hadj⟩
          · obtain ⟨r, hqr⟩ := hD_is_pSel q hqD
            have hq_sel : vs[q] = vs[pSel r]'(hD_lt _ (mem_filter.mp (hpSel r)).1) := by
              simp only [hqr]
            have := hq_get.symm.trans (hq_sel.trans (hvSel r))
            injection this; omega
          · obtain ⟨r, rfl⟩ := hD_is_pSel p hpD
            rw [Graph.ofAdj_adj] at hadj
            obtain ⟨_, _, _, hor⟩ := hadj
            rw [hq_get, hvSel r, ladAdj_symm, Bool.or_self, ladAdj, Bool.or_eq_true] at hor
            rcases hor with h1 | h2
            · obtain ⟨_, _, _, hc⟩ := (ladHalf_eq_true_iff _ _).mp h1
              rcases hc with ⟨hb0, _⟩ | ⟨hb1, _⟩ | ⟨_, (⟨hri, hne1⟩ | ⟨hrj, hne2⟩)⟩
              · simp at hb0
              · simp at hb1
              · have hr : r = r₁ := Fin.ext hri; exact hne1 (hr ▸ rfl)
              · have hr : r = r₂ := Fin.ext hrj; exact hne2 (hr ▸ rfl)
            · simp [ladHalf] at h2
        have hu_inj : Function.Injective uSel := by
          intro r₁ r₂ heq
          rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
          · exact False.elim ((hadj_pair r₁ r₂ hlt).ne heq)
          · rfl
          · exact False.elim ((hadj_pair r₂ r₁ hgt).ne heq.symm)
        refine ⟨univ.image uSel, fun v hv ↦ ?_, ⟨?_, ?_⟩⟩
        · obtain ⟨r, -, rfl⟩ := mem_image.mp hv
          exact G.mem_distinctVertices.mp (huSel r)
        · intro x hx y hy hxy
          rw [mem_coe, mem_image] at hx hy
          obtain ⟨r₁, -, rfl⟩ := hx
          obtain ⟨r₂, -, rfl⟩ := hy
          rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
          · exact hadj_pair r₁ r₂ hlt
          · exact False.elim (hxy rfl)
          · exact (hadj_pair r₂ r₁ hgt).symm
        · rw [card_image_of_injective _ hu_inj, card_fin]
    · simp only [hkn, decide_false, Bool.false_eq_true, ↓reduceIte, mem_DominatingSet_iff]
      refine ⟨fun hcl ↦ ?_, fun ⟨D, _, hD, hcard⟩ ↦ ?_⟩
      · have hle := Graph.le_card_of_mem_Clique hcl
        rw [← G.length_distinctVertices] at hle
        exact absurd hle hkn
      · obtain rfl := card_eq_zero.mp hcard
        have := hD 0 (by simp)
        simp at this

private theorem computableInPolyTime_ladHalf :
    ComputableInPolyTime (fun p : GadgetVert × GadgetVert ↦ ladHalf p.1 p.2)
      (encPair encGadgetVert encGadgetVert) encBool := by
  unfold ladHalf
  fun_prop

private theorem computableInPolyTime_ladAdj :
    ComputableInPolyTime (fun p : CliqueInstance × (GadgetVert × GadgetVert) ↦ ladAdj p.2.1 p.2.2)
      (encPair encCliqueInstance (encPair encGadgetVert encGadgetVert)) encBool := by
  have h1 : ComputableInPolyTime
      (fun p : CliqueInstance × (GadgetVert × GadgetVert) ↦ ladHalf p.2.1 p.2.2)
      (encPair encCliqueInstance (encPair encGadgetVert encGadgetVert)) encBool :=
    computableInPolyTime_ladHalf.comp (snd _ _)
  have h2 : ComputableInPolyTime
      (fun p : CliqueInstance × (GadgetVert × GadgetVert) ↦ ladHalf p.2.2 p.2.1)
      (encPair encCliqueInstance (encPair encGadgetVert encGadgetVert)) encBool :=
    computableInPolyTime_ladHalf.comp (((snd _ _).comp (snd _ _)).prod ((fst _ _).comp (snd _ _)))
  exact bool_or' h1 h2

private theorem computableInPolyTime_ladVerts :
    ComputableInPolyTime
      (fun x : CliqueInstance ↦ ladVerts x.graph (min x.graph.distinctVertices.length x.m))
      encCliqueInstance (encList encGadgetVert) := by
  let kk : CliqueInstance → ℕ := fun x ↦ min x.graph.distinctVertices.length x.m
  have hdv : ComputableInPolyTime (fun x : CliqueInstance ↦ x.graph.distinctVertices)
      encCliqueInstance (encList encNat) := by fun_prop
  have hkk : ComputableInPolyTime kk encCliqueInstance encUnary :=
    binary_min_unary' ((length_list encNat).comp hdv) (by fun_prop)
  have hrange : ComputableInPolyTime (fun x : CliqueInstance ↦ List.range (kk x))
      encCliqueInstance (encList encUnary) := by fun_prop
  have hsel : ComputableInPolyTime (fun x : CliqueInstance ↦ ladSelVerts x.graph (kk x))
      encCliqueInstance (encList encGadgetVert) := by
    unfold ladSelVerts
    exact flatMapWithInput hrange (by fun_prop)
  have hguard : ComputableInPolyTime (fun x : CliqueInstance ↦ ladGuardVerts (kk x))
      encCliqueInstance (encList encGadgetVert) := by
    unfold ladGuardVerts
    exact flatMapWithInput hrange (by fun_prop)
  have hnon : ComputableInPolyTime (fun x : CliqueInstance ↦ ladNonedgeVerts x.graph (kk x))
      encCliqueInstance (encList encGadgetVert) := by
    unfold ladNonedgeVerts
    refine flatMapWithInput hrange ?_
    refine flatMapWithInput (hrange.comp (fst _ _)) ?_
    refine flatMapWithInput (hdv.comp ((fst _ _).comp (fst _ _))) ?_
    refine flatMapWithInput (hdv.comp (((fst _ _).comp (fst _ _)).comp (fst _ _))) ?_
    exact ite' (by fun_prop) (by fun_prop) (const [])
  unfold ladVerts
  exact listAppend' (listAppend' hsel hguard) hnon

/-- `cliqueToLadDomSet` is computable in polynomial time. -/
theorem computableInPolyTime_cliqueToLadDomSet :
    ComputableInPolyTime cliqueToLadDomSet encCliqueInstance encDominatingSet := by
  have hofAdj : ComputableInPolyTime
      (fun x : CliqueInstance ↦
        Graph.ofAdj (ladVerts x.graph (min x.graph.distinctVertices.length x.m)) ladAdj)
      encCliqueInstance encGraph :=
    Graph.computableInPolyTime_ofAdj computableInPolyTime_ladVerts computableInPolyTime_ladAdj
  have hle : ComputableInPolyTime
      (fun x : CliqueInstance ↦ decide (x.m ≤ x.graph.distinctVertices.length))
      encCliqueInstance encBool :=
    binary_le' (by fun_prop) (unary_to_binary.comp (by fun_prop))
  unfold cliqueToLadDomSet
  exact ite' (by fun_prop) (const (⟨⟨[], []⟩, 0⟩ : DominatingSetInstance))
    (ite' hle (encDominatingSet_mk_polyTime hofAdj (by fun_prop))
      (const (⟨⟨[0], []⟩, 0⟩ : DominatingSetInstance)))

end LadderFreeReduction

section WHardness

/-- `Clique` FPT-reduces to `DominatingSet` restricted to graphs with no semi-induced ladder of
order `46`. -/
theorem fptReducible_Clique_DominatingSet_ladderFree :
    FPTReducible encCliqueInstance encDominatingSet (·.m) (·.bound)
      Clique {x : DominatingSetInstance |
        x ∈ DominatingSet ∧ ¬ HasSemiInducedLadder x.graph.induced 46} := by
  refine FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToLadDomSet
    (h := fun k ↦ k) cliqueToLadDomSet_bound_le fun x ↦ ?_
  exact ⟨fun hx ↦ ⟨(cliqueToLadDomSet_mem_iff x).mp hx,
        not_hasSemiInducedLadder_cliqueToLadDomSet x⟩,
      fun hx ↦ (cliqueToLadDomSet_mem_iff x).mpr hx.1⟩

/-- `DominatingSet` restricted to graphs forbidding semi-induced ladders of order `46` is
`W[1]`-hard. -/
theorem DominatingSet_ladderFree_wHard :
    WHard 1 encDominatingSet (·.bound)
      {x : DominatingSetInstance |
        x ∈ DominatingSet ∧ ¬ HasSemiInducedLadder x.graph.induced 46} :=
  Clique_wHard.trans fptReducible_Clique_DominatingSet_ladderFree

/-- `Clique` FPT-reduces to `DominatingSet`. -/
theorem fptReducible_Clique_DominatingSet :
    FPTReducible encCliqueInstance encDominatingSet (·.m) (·.bound) Clique DominatingSet :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToLadDomSet
    (h := fun k ↦ k) cliqueToLadDomSet_bound_le cliqueToLadDomSet_mem_iff

/-- `DominatingSet` is `W[1]`-hard. -/
theorem DominatingSet_wHard :
    WHard 1 encDominatingSet (·.bound) DominatingSet :=
  Clique_wHard.trans fptReducible_Clique_DominatingSet

/-- Closed-neighborhood `DominatingSet → SetCover` reduction. -/
@[expose]
def domSetToSetCover (x : DominatingSetInstance) : SetSystem × ℕ :=
  let V := x.graph.distinctVertices
  if decide (x.bound ≤ V.length) then
    (⟨V, V.map fun v ↦ v :: V.filter (x.graph.adjBool v)⟩, x.bound)
  else
    (⟨[0], []⟩, 0)

/-- `domSetToSetCover` is computable in polynomial time. -/
theorem computableInPolyTime_domSetToSetCover :
    ComputableInPolyTime domSetToSetCover encDominatingSet encSetCover := by
  have hdv : ComputableInPolyTime (fun x : DominatingSetInstance ↦ x.graph.distinctVertices)
      encDominatingSet (encList encNat) := by fun_prop
  have hle : ComputableInPolyTime
      (fun x : DominatingSetInstance ↦ decide (x.bound ≤ x.graph.distinctVertices.length))
      encDominatingSet encBool :=
    binary_le' (by fun_prop) (unary_to_binary.comp (by fun_prop))
  have hsets : ComputableInPolyTime
      (fun x : DominatingSetInstance ↦
        x.graph.distinctVertices.map fun v ↦
          v :: x.graph.distinctVertices.filter (x.graph.adjBool v))
      encDominatingSet encNatSetList := by
    refine mapWithInput hdv ?_
    exact cons' (snd _ _) (filterWithInput (hdv.comp (fst _ _)) (by fun_prop))
  unfold domSetToSetCover
  exact ite' hle
    (ComputableInPolyTime.prod (computableInPolyTime_setSystemMk hdv hsets) (by fun_prop))
    (const ((⟨[0], []⟩, 0) : SetSystem × ℕ))

/-- Membership equivalence for `domSetToSetCover`. -/
theorem domSetToSetCover_mem_iff (x : DominatingSetInstance) :
    x ∈ DominatingSet ↔ domSetToSetCover x ∈ SetCover := by
  classical
  obtain ⟨G, k⟩ := x
  rw [mem_DominatingSet_iff_exists_card_le]
  simp only [domSetToSetCover, ← G.length_distinctVertices]
  set V := G.distinctVertices
  by_cases hkn : k ≤ V.length
  · simp only [hkn, decide_true, ↓reduceIte, true_and, mem_SetCover_iff]
    let sys : SetSystem := ⟨V, V.map fun v ↦ v :: V.filter (G.adjBool v)⟩
    have hlen : sys.sets.length = V.length := List.length_map _
    constructor
    · rintro ⟨S, hSV, hSdom, hScard⟩
      let C : Finset (Fin sys.sets.length) :=
        (S.image V.idxOf).subtype (· < sys.sets.length) |>.map
          ⟨fun p ↦ ⟨p.1, p.2⟩, fun _ _ h ↦ Subtype.ext (Fin.mk.inj h)⟩
      have hCcard : #C ≤ k := by
        dsimp only [C]
        calc #C = #((S.image V.idxOf).subtype (· < sys.sets.length)) := card_map _
          _ ≤ #(S.image V.idxOf) := by
              rw [card_subtype]; exact card_filter_le _ _
          _ ≤ #S := card_image_le
          _ ≤ k := hScard
      refine ⟨C, fun u huV ↦ ?_, hCcard⟩
      rcases hSdom u (G.mem_distinctVertices.mp huV) with huS | ⟨s, hsS, hadj⟩
      · have hi_lt : V.idxOf u < sys.sets.length :=
          hlen ▸ List.idxOf_lt_length_of_mem huV
        let idx : Fin sys.sets.length := ⟨V.idxOf u, hi_lt⟩
        have hmemC : idx ∈ C := by
          dsimp only [C]
          refine mem_map.mpr ⟨⟨V.idxOf u, hi_lt⟩, mem_subtype.mpr (mem_image_of_mem _ huS), rfl⟩
        refine ⟨idx, hmemC, ?_⟩
        have hget : sys.sets[idx.1] = V[V.idxOf u] :: V.filter (G.adjBool V[V.idxOf u]) := by
          simp [sys, idx]
        rw [Fin.getElem_fin, hget, List.getElem_idxOf (List.idxOf_lt_length_of_mem huV)]
        exact List.mem_cons_self ..
      · have hsv : s ∈ V := G.mem_distinctVertices.mpr (hSV s hsS)
        have hi_lt : V.idxOf s < sys.sets.length :=
          hlen ▸ List.idxOf_lt_length_of_mem hsv
        let idx : Fin sys.sets.length := ⟨V.idxOf s, hi_lt⟩
        have hmemC : idx ∈ C := by
          dsimp only [C]
          refine mem_map.mpr ⟨⟨V.idxOf s, hi_lt⟩, mem_subtype.mpr (mem_image_of_mem _ hsS), rfl⟩
        refine ⟨idx, hmemC, ?_⟩
        have hget : sys.sets[idx.1] = V[V.idxOf s] :: V.filter (G.adjBool V[V.idxOf s]) := by
          simp [sys, idx]
        rw [Fin.getElem_fin, hget, List.getElem_idxOf (List.idxOf_lt_length_of_mem hsv)]
        exact List.mem_cons_of_mem _ (List.mem_filter.mpr
          ⟨huV, (G.adjBool_eq_true_iff s u).mpr hadj.symm⟩)
    · rintro ⟨C, hcov, hCcard⟩
      let f : Fin sys.sets.length → ℕ := fun i ↦ V[i.1]'(hlen ▸ i.isLt)
      let S : Finset ℕ := C.image f
      refine ⟨S, fun v hv ↦ ?_, fun u huG ↦ ?_, card_image_le.trans hCcard⟩
      · obtain ⟨i, -, rfl⟩ := mem_image.mp hv
        exact G.mem_distinctVertices.mp (List.getElem_mem _)
      · have huV : u ∈ V := G.mem_distinctVertices.mpr huG
        obtain ⟨i, hiC, hui⟩ := hcov u huV
        have hget : sys.sets[i.1] = f i :: V.filter (G.adjBool (f i)) := by simp [sys, f]
        rw [Fin.getElem_fin, hget] at hui
        rcases List.mem_cons.mp hui with rfl | hfil
        · exact Or.inl (mem_image_of_mem f hiC)
        · have hadj : G.toSimpleGraph.Adj (f i) u :=
            (G.adjBool_eq_true_iff _ _).mp (List.mem_filter.mp hfil).2
          exact Or.inr ⟨f i, mem_image_of_mem f hiC, hadj.symm⟩
  · simp only [hkn, decide_false, Bool.false_eq_true, ↓reduceIte, false_and, false_iff,
      mem_SetCover_iff, not_exists, not_and]
    intro C hcov _
    obtain ⟨i, _, _⟩ := hcov 0 (by simp)
    exact Fin.elim0 i

/-- `DominatingSet` FPT-reduces to `SetCover` via closed neighborhoods. -/
theorem fptReducible_DominatingSet_SetCover :
    FPTReducible encDominatingSet encSetCover (·.bound) Prod.snd DominatingSet SetCover := by
  refine FPTReducible.of_computableInPolyTime computableInPolyTime_domSetToSetCover
    (h := fun k ↦ k) (fun x ↦ ?_) domSetToSetCover_mem_iff
  by_cases hkn : x.bound ≤ x.graph.distinctVertices.length
  · simp [domSetToSetCover, hkn]
  · simp [domSetToSetCover, hkn]

/-- `SetCover` is `W[1]`-hard. -/
theorem SetCover_wHard :
    WHard 1 encSetCover Prod.snd SetCover :=
  DominatingSet_wHard.trans fptReducible_DominatingSet_SetCover

end WHardness

end CslibFrontier.Complexity
