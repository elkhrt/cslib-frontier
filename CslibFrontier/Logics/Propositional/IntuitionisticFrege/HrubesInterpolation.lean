/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import CslibFrontier.Computability.Circuit.Clique
public import CslibFrontier.Computability.Circuit.Monotone.Basic
public import CslibFrontier.Computability.Circuit.Monotone.Clique.Asymptotic
public import CslibFrontier.Computability.Circuit.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hrubeš's Monotone Feasible Interpolation and Exponential Intuitionistic Frege Lower Bound

This module formalizes **Hrubeš's monotone feasible interpolation theorem** for
intuitionistic propositional Frege systems (`hrubes_monotone_circuit_of_pool`) and combines it
with the Razborov–Alon–Boppana monotone circuit lower bound
(`Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_size_of_separates`) to obtain an unconditional
`2 ^ (2 ⌊√k⌋)` size lower bound (`two_pow_two_mul_sqrt_lt_ifregePool_of_hrubesTau`) on
subformula-closed intuitionistic Frege proof pools for Hrubeš's Clique–Coloring tautologies
`hrubesTau n k`.

## Main definitions

* `CslibFrontier.Logics.Propositional.IntuitionisticFrege.IFregeSchema`: Hilbert-style
  schemas for intuitionistic propositional logic over `Cslib.Logic.PL.Proposition`.
* `CslibFrontier.Logics.Propositional.IntuitionisticFrege.IFregeProof`: intuitionistic Frege
  line proofs.
* `CslibFrontier.Logics.Propositional.IntuitionisticFrege.IFregePool`: intuitionistic Frege
  derivability restricted to an ambient subformula pool `F`.
* `CslibFrontier.Logics.Propositional.IntuitionisticFrege.HrubesAtom`, `hrubesTau`: Hrubeš's
  intuitionistic Clique–Coloring tautology
  `DISJ(p, r) → ((Clique(p, q) → ⊥) ∨ (Color(r, z) → ⊥))`.

## Main results

* `CslibFrontier.Logics.Propositional.IntuitionisticFrege.hrubes_monotone_circuit_of_pool`:
  any subformula-closed intuitionistic Frege pool `F₀` proving `hrubesTau n k` yields a monotone
  circuit `C : Circuit Monotone.signature (edgeCount n) 1` of size `≤ 12 * (F₀.length + 1) ^ 3`
  separating `k`-cliques from `(k - 1)`-colorable graphs on `n` vertices.
* `two_pow_two_mul_sqrt_lt_ifregePool_of_hrubesTau`:
  for `2 ≤ k` and `k ^ 4 ≤ n`, every subformula-closed intuitionistic Frege pool `F₀` proving
  `hrubesTau n k` satisfies `2 ^ (2 * Nat.sqrt k) < 12 * (F₀.length + 1) ^ 3`.
-/

public section

namespace CslibFrontier.Logics.Propositional.IntuitionisticFrege

open Cslib.Logic.PL Cslib.BitString.Graph Cslib.Circuits

/-! ### 1. Classical Semantics, Subformulas, and Balanced Connectives -/

/-- Classical Boolean evaluation of a `Cslib.Logic.PL.Proposition`. -/
@[expose] def propEval {α : Type*} (σ : α → Bool) : Proposition α → Bool
  | .atom a => σ a
  | .falsum => false
  | .and A B => propEval σ A && propEval σ B
  | .or A B => propEval σ A || propEval σ B
  | .imp A B => !propEval σ A || propEval σ B

@[simp] theorem propEval_atom {α : Type*} (σ : α → Bool) (a : α) :
    propEval σ (.atom a) = σ a := rfl
@[simp] theorem propEval_falsum {α : Type*} (σ : α → Bool) :
    propEval σ .falsum = false := rfl
@[simp] theorem propEval_bot {α : Type*} (σ : α → Bool) :
    propEval σ (⊥ : Proposition α) = false := rfl
@[simp] theorem propEval_top {α : Type*} (σ : α → Bool) :
    propEval σ (⊤ : Proposition α) = true := rfl
@[simp] theorem propEval_and {α : Type*} (σ : α → Bool) (A B : Proposition α) :
    propEval σ (.and A B) = (propEval σ A && propEval σ B) := rfl
@[simp] theorem propEval_or {α : Type*} (σ : α → Bool) (A B : Proposition α) :
    propEval σ (.or A B) = (propEval σ A || propEval σ B) := rfl
@[simp] theorem propEval_imp {α : Type*} (σ : α → Bool) (A B : Proposition α) :
    propEval σ (.imp A B) = (!propEval σ A || propEval σ B) := rfl

/-- All subformulas of a `Cslib.Logic.PL.Proposition`. -/
@[expose] def propSubformulas {α : Type*} : Proposition α → List (Proposition α)
  | .atom a => [.atom a]
  | .falsum => [.falsum]
  | .and A B => .and A B :: (propSubformulas A ++ propSubformulas B)
  | .or A B => .or A B :: (propSubformulas A ++ propSubformulas B)
  | .imp A B => .imp A B :: (propSubformulas A ++ propSubformulas B)

theorem self_mem_propSubformulas {α : Type*} (A : Proposition α) : A ∈ propSubformulas A := by
  cases A <;> simp [propSubformulas]

theorem propSubformulas_trans {α : Type*} {A B C : Proposition α}
    (h1 : A ∈ propSubformulas B) (h2 : B ∈ propSubformulas C) : A ∈ propSubformulas C := by
  induction C with
  | atom _ =>
    simp only [propSubformulas, List.mem_singleton] at h2; subst h2; exact h1
  | falsum =>
    simp only [propSubformulas, List.mem_singleton] at h2; subst h2; exact h1
  | and D E ihD ihE =>
    simp only [propSubformulas, List.mem_cons, List.mem_append] at h2 ⊢
    rcases h2 with rfl | hD | hE
    · simp only [propSubformulas, List.mem_cons, List.mem_append] at h1; exact h1
    · exact Or.inr (Or.inl (ihD hD))
    · exact Or.inr (Or.inr (ihE hE))
  | or D E ihD ihE =>
    simp only [propSubformulas, List.mem_cons, List.mem_append] at h2 ⊢
    rcases h2 with rfl | hD | hE
    · simp only [propSubformulas, List.mem_cons, List.mem_append] at h1; exact h1
    · exact Or.inr (Or.inl (ihD hD))
    · exact Or.inr (Or.inr (ihE hE))
  | imp D E ihD ihE =>
    simp only [propSubformulas, List.mem_cons, List.mem_append] at h2 ⊢
    rcases h2 with rfl | hD | hE
    · simp only [propSubformulas, List.mem_cons, List.mem_append] at h1; exact h1
    · exact Or.inr (Or.inl (ihD hD))
    · exact Or.inr (Or.inr (ihE hE))

/-- Balanced binary conjunction over a list of propositions (returns `⊤` on `[]`). -/
@[expose] def balAnd {Atom : Type*} : List (Proposition Atom) → Proposition Atom
  | [] => ⊤
  | [A] => A
  | A :: B :: rest =>
    let half := (A :: B :: rest).length / 2
    .and (balAnd ((A :: B :: rest).take half)) (balAnd ((A :: B :: rest).drop half))
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- Balanced binary disjunction over a list of propositions (returns `⊥` on `[]`). -/
@[expose] def balOr {Atom : Type*} : List (Proposition Atom) → Proposition Atom
  | [] => ⊥
  | [A] => A
  | A :: B :: rest =>
    let half := (A :: B :: rest).length / 2
    .or (balOr ((A :: B :: rest).take half)) (balOr ((A :: B :: rest).drop half))
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

theorem propEval_balAnd {Atom : Type*} (σ : Atom → Bool) (l : List (Proposition Atom)) :
    propEval σ (balAnd l) = true ↔ ∀ A ∈ l, propEval σ A = true := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | ind k ih =>
    match l with
    | [] => simp [balAnd]
    | [A] => simp [balAnd]
    | A :: B :: rest =>
      let half := (A :: B :: rest).length / 2
      have h1 : ((A :: B :: rest).take half).length < k := by
        simp only [half, List.length_take, List.length_cons] at *; omega
      have h2 : ((A :: B :: rest).drop half).length < k := by
        simp only [half, List.length_drop, List.length_cons] at *; omega
      rw [balAnd.eq_3]
      simp only [propEval_and, Bool.and_eq_true]
      rw [ih _ h1 _ rfl, ih _ h2 _ rfl]
      constructor
      · rintro ⟨ht, hd⟩ C hC
        have hsplit := List.take_append_drop half (A :: B :: rest)
        rw [← hsplit, List.mem_append] at hC
        rcases hC with hC | hC
        · exact ht C hC
        · exact hd C hC
      · intro hall
        exact ⟨fun C hC => hall C (List.mem_of_mem_take hC),
          fun C hC => hall C (List.mem_of_mem_drop hC)⟩

theorem propEval_balOr {Atom : Type*} (σ : Atom → Bool) (l : List (Proposition Atom)) :
    propEval σ (balOr l) = true ↔ ∃ A ∈ l, propEval σ A = true := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | ind k ih =>
    match l with
    | [] => simp [balOr]
    | [A] => simp [balOr]
    | A :: B :: rest =>
      let half := (A :: B :: rest).length / 2
      have h1 : ((A :: B :: rest).take half).length < k := by
        simp only [half, List.length_take, List.length_cons] at *; omega
      have h2 : ((A :: B :: rest).drop half).length < k := by
        simp only [half, List.length_drop, List.length_cons] at *; omega
      rw [balOr.eq_3]
      simp only [propEval_or, Bool.or_eq_true]
      rw [ih _ h1 _ rfl, ih _ h2 _ rfl]
      constructor
      · rintro (⟨C, hC, hv⟩ | ⟨C, hC, hv⟩)
        · exact ⟨C, List.mem_of_mem_take hC, hv⟩
        · exact ⟨C, List.mem_of_mem_drop hC, hv⟩
      · rintro ⟨C, hC, hv⟩
        have hsplit := List.take_append_drop half (A :: B :: rest)
        rw [← hsplit, List.mem_append] at hC
        rcases hC with hC | hC
        · exact Or.inl ⟨C, hC, hv⟩
        · exact Or.inr ⟨C, hC, hv⟩

private theorem mem_propSubformulas_balAnd {Atom : Type*}
    {l : List (Proposition Atom)} {A : Proposition Atom} (hA : A ∈ l) :
    A ∈ propSubformulas (balAnd l) := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | ind k ih =>
    match l with
    | [] => cases hA
    | [B] =>
      rcases List.mem_singleton.mp hA with rfl
      simpa only [balAnd] using self_mem_propSubformulas A
    | B :: C :: rest =>
      let half := (B :: C :: rest).length / 2
      have h1 : ((B :: C :: rest).take half).length < k := by
        simp only [half, List.length_take, List.length_cons] at *; omega
      have h2 : ((B :: C :: rest).drop half).length < k := by
        simp only [half, List.length_drop, List.length_cons] at *; omega
      rw [balAnd.eq_3]
      have hsplit := List.take_append_drop half (B :: C :: rest)
      rw [← hsplit, List.mem_append] at hA
      simp only [propSubformulas, List.mem_cons, List.mem_append]
      rcases hA with hL | hR
      · exact Or.inr (Or.inl (ih _ h1 hL rfl))
      · exact Or.inr (Or.inr (ih _ h2 hR rfl))

/-! ### 2. Intuitionistic Frege Schemas, Line Proofs, and Formula Pools -/

/-- Standard intuitionistic Frege (Hilbert-style) schemas over `Proposition Atom`. -/
inductive IFregeSchema {Atom : Type*} : Proposition Atom → Prop where
  | axK (A B : Proposition Atom) : IFregeSchema (.imp A (.imp B A))
  | axS (A B C : Proposition Atom) :
      IFregeSchema (.imp (.imp A (.imp B C)) (.imp (.imp A B) (.imp A C)))
  | andE₁ (A B : Proposition Atom) : IFregeSchema (.imp (.and A B) A)
  | andE₂ (A B : Proposition Atom) : IFregeSchema (.imp (.and A B) B)
  | andI (A B : Proposition Atom) : IFregeSchema (.imp A (.imp B (.and A B)))
  | orI₁ (A B : Proposition Atom) : IFregeSchema (.imp A (.or A B))
  | orI₂ (A B : Proposition Atom) : IFregeSchema (.imp B (.or A B))
  | orE (A B C : Proposition Atom) :
      IFregeSchema (.imp (.imp A C) (.imp (.imp B C) (.imp (.or A B) C)))
  | efq (A : Proposition Atom) : IFregeSchema (.imp .falsum A)

theorem IFregeSchema.eval_true {Atom : Type*} (σ : Atom → Bool)
    {φ : Proposition Atom} (h : IFregeSchema φ) : propEval σ φ = true := by
  cases h with
  | axK A B => simp only [propEval]; cases propEval σ A <;> cases propEval σ B <;> rfl
  | axS A B C =>
    simp only [propEval]
    cases propEval σ A <;> cases propEval σ B <;> cases propEval σ C <;> rfl
  | andE₁ A B => simp only [propEval]; cases propEval σ A <;> cases propEval σ B <;> rfl
  | andE₂ A B => simp only [propEval]; cases propEval σ A <;> cases propEval σ B <;> rfl
  | andI A B => simp only [propEval]; cases propEval σ A <;> cases propEval σ B <;> rfl
  | orI₁ A B => simp only [propEval]; cases propEval σ A <;> cases propEval σ B <;> rfl
  | orI₂ A B => simp only [propEval]; cases propEval σ A <;> cases propEval σ B <;> rfl
  | orE A B C =>
    simp only [propEval]
    cases propEval σ A <;> cases propEval σ B <;> cases propEval σ C <;> rfl
  | efq _ => rfl

/-- A valid intuitionistic Frege proof sequence (newest derived line at the head of the list). -/
inductive IFregeProof {Atom : Type*} : List (Proposition Atom) → Prop where
  | nil : IFregeProof []
  | ax {L : List (Proposition Atom)} (φ : Proposition Atom)
      (hL : IFregeProof L) (hax : IFregeSchema φ) : IFregeProof (φ :: L)
  | mp {L : List (Proposition Atom)} {α β : Proposition Atom}
      (hL : IFregeProof L) (himp : Proposition.imp α β ∈ L) (harg : α ∈ L) :
      IFregeProof (β :: L)

/-- Provability within a fixed ambient formula pool `F : List (Proposition Atom)` using only
schema instances in `F` and modus ponens steps inside `F`. -/
inductive IFregePool {Atom : Type*} (F : List (Proposition Atom)) :
    Proposition Atom → Prop where
  | ax {φ : Proposition Atom} (hmem : φ ∈ F) (hax : IFregeSchema φ) : IFregePool F φ
  | mp {α β : Proposition Atom} (hmem : β ∈ F)
      (himp : IFregePool F (.imp α β)) (harg : IFregePool F α) : IFregePool F β

theorem IFregePool.mem {Atom : Type*} {F : List (Proposition Atom)} {φ : Proposition Atom}
    (h : IFregePool F φ) : φ ∈ F := by
  cases h with
  | ax hmem _ => exact hmem
  | mp hmem _ _ => exact hmem

theorem IFregePool.mono {Atom : Type*} {F₁ F₂ : List (Proposition Atom)}
    (hsub : ∀ ψ ∈ F₁, ψ ∈ F₂) {φ : Proposition Atom} (h : IFregePool F₁ φ) :
    IFregePool F₂ φ := by
  induction h with
  | ax hmem hax => exact .ax (hsub _ hmem) hax
  | mp hmem _ _ ih₁ ih₂ => exact .mp (hsub _ hmem) ih₁ ih₂

/-! ### 3. Hrubeš's Clique–Coloring Formula `hrubesTau n k` -/

/-- Propositional atoms of Hrubeš's Clique–Coloring tautology on `n` vertices with clique
size `k` and `k - 1` colors. -/
inductive HrubesAtom (n k : ℕ) : Type where
  /-- Edge-presence indicator `p_e` for undirected edge `e : Fin (edgeCount n)`. -/
  | pEdge (e : Fin (edgeCount n)) : HrubesAtom n k
  /-- Edge-absence indicator `r_e` for undirected edge `e : Fin (edgeCount n)`. -/
  | rEdge (e : Fin (edgeCount n)) : HrubesAtom n k
  /-- Clique-map atom `q_{u, v}` (`u < k`, `v < n`). -/
  | qClique (u : Fin k) (v : Fin n) : HrubesAtom n k
  /-- Coloring atom `z_{v, c}` (`v < n`, `c < k - 1`). -/
  | zColor (v : Fin n) (c : Fin (k - 1)) : HrubesAtom n k
deriving DecidableEq, Repr

/-- `DISJ(p, r) = ⋀_e ((p_e → ⊥) ∨ (r_e → ⊥))`: no edge `e` has both `p_e` and `r_e`. -/
@[expose] def hrubesDisj (n k : ℕ) : Proposition (HrubesAtom n k) :=
  balAnd ((List.finRange (edgeCount n)).map fun e =>
    .or (.imp (.atom (.pEdge e)) ⊥) (.imp (.atom (.rEdge e)) ⊥))

/-- `k`-clique totality: each clique slot `u < k` chooses at least one vertex `v < n`. -/
@[expose] def hrubesCliqueTot (n k : ℕ) : Proposition (HrubesAtom n k) :=
  balAnd ((List.finRange k).map fun u =>
    balOr ((List.finRange n).map fun v => .atom (.qClique u v)))

/-- `k`-clique injectivity: distinct clique slots `u < u'` cannot pick the same vertex `v`. -/
@[expose] def hrubesCliqueInj (n k : ℕ) : Proposition (HrubesAtom n k) :=
  balAnd ((List.finRange k).flatMap fun u =>
    (((List.finRange k).filter (fun u' => u < u')).flatMap fun u' =>
      (List.finRange n).map fun v =>
        .imp (.atom (.qClique u v)) (.imp (.atom (.qClique u' v)) ⊥)))

/-- `k`-clique adjacency: distinct vertices picked by `u < u'` must have `p_{v, w}` true. -/
@[expose] noncomputable def hrubesCliqueAdj (n k : ℕ) : Proposition (HrubesAtom n k) :=
  balAnd ((List.finRange k).flatMap fun u =>
    (((List.finRange k).filter (fun u' => u < u')).flatMap fun u' =>
      (List.finRange n).flatMap fun v =>
        (((List.finRange n).filter (fun w => w ≠ v)).map fun w =>
          if h : v ≠ w then
            .imp (.atom (.qClique u v))
              (.imp (.atom (.qClique u' w)) (.atom (.pEdge (edgeEquiv n (edge h)))))
          else ⊤)))

/-- Full `k`-clique formula `Clique(p, q)`. -/
@[expose] noncomputable def hrubesClique (n k : ℕ) : Proposition (HrubesAtom n k) :=
  .and (.and (hrubesCliqueTot n k) (hrubesCliqueInj n k)) (hrubesCliqueAdj n k)

/-- `(k - 1)`-coloring totality: each vertex `v < n` receives at least one color `c < k - 1`. -/
@[expose] def hrubesColorTot (n k : ℕ) : Proposition (HrubesAtom n k) :=
  balAnd ((List.finRange n).map fun v =>
    balOr ((List.finRange (k - 1)).map fun c => .atom (.zColor v c)))

/-- `(k - 1)`-coloring properness: monochromatic pairs `v < w` require non-edge indicator
`r_{v, w}`. -/
@[expose] noncomputable def hrubesColorProper (n k : ℕ) : Proposition (HrubesAtom n k) :=
  balAnd ((List.finRange (k - 1)).flatMap fun c =>
    (List.finRange n).flatMap fun v =>
      (((List.finRange n).filter (fun w => v < w)).map fun w =>
        if h : v ≠ w then
          .imp (.atom (.zColor v c))
            (.imp (.atom (.zColor w c)) (.atom (.rEdge (edgeEquiv n (edge h)))))
        else ⊤))

/-- Full `(k - 1)`-coloring formula `Color(r, z)`. -/
@[expose] noncomputable def hrubesColor (n k : ℕ) : Proposition (HrubesAtom n k) :=
  .and (hrubesColorTot n k) (hrubesColorProper n k)

/-- Hrubeš's intuitionistic Clique–Coloring tautology:
`DISJ(p, r) → ((Clique(p, q) → ⊥) ∨ (Color(r, z) → ⊥))`. -/
@[expose] noncomputable def hrubesTau (n k : ℕ) : Proposition (HrubesAtom n k) :=
  .imp (hrubesDisj n k) (.or (.imp (hrubesClique n k) ⊥) (.imp (hrubesColor n k) ⊥))

/-! ### 4. Semantic Evaluation and Monotone Circuit Construction -/

/-- Classical soundness predicate `a(φ, x)` on graph edge-vector `x`: `φ` evaluates to `true`
under every Boolean valuation setting `p_e = false` on non-edges of `x` and `r_e = false`
everywhere. -/
def hrubesAPred {n k : ℕ} (x : Fin (edgeCount n) → Bool)
    (φ : Proposition (HrubesAtom n k)) : Prop :=
  ∀ σ : HrubesAtom n k → Bool,
    (∀ e : Fin (edgeCount n), x e = false → σ (.pEdge e) = false) →
    (∀ e : Fin (edgeCount n), σ (.rEdge e) = false) →
    propEval σ φ = true

theorem not_hrubesAPred_neg_clique_of_clique {n k : ℕ}
    {x : Fin (edgeCount n) → Bool} (hx : clique n k x = true) :
    ¬ hrubesAPred (k := k) x (.imp (hrubesClique n k) ⊥) := by
  obtain ⟨s, hs, hxs⟩ := of_decide_eq_true hx
  have hcard : Fintype.card (Fin k) = Fintype.card s := by
    rw [Fintype.card_fin, Fintype.card_coe, hs]
  let emb : Fin k ≃ s := Fintype.equivOfCardEq hcard
  let f : Fin k → Fin n := fun u => (emb u).1
  have hfinj : Function.Injective f := fun u₁ u₂ h =>
    emb.injective (Subtype.ext h)
  let σ : HrubesAtom n k → Bool := fun
    | .pEdge e => x e
    | .rEdge _ => false
    | .qClique u v => decide (f u = v)
    | .zColor _ _ => false
  intro ha
  have hval := ha σ (fun e he => he) (fun _ => rfl)
  have hcl : propEval σ (hrubesClique n k) = true := by
    simp only [hrubesClique, propEval_and, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hrubesCliqueTot, propEval_balAnd]
      intro φ hφ
      rcases List.mem_map.mp hφ with ⟨u, _, rfl⟩
      rw [propEval_balOr]
      refine ⟨.atom (.qClique u (f u)),
        List.mem_map.mpr ⟨f u, List.mem_finRange _, rfl⟩, ?_⟩
      simp [σ]
    · rw [hrubesCliqueInj, propEval_balAnd]
      intro φ hφ
      rcases List.mem_flatMap.mp hφ with ⟨u, _, h1⟩
      rcases List.mem_flatMap.mp h1 with ⟨u', hu', h2⟩
      rcases List.mem_map.mp h2 with ⟨v, _, rfl⟩
      have hlt : u < u' := of_decide_eq_true (List.mem_filter.mp hu').2
      have hne : u ≠ u' := ne_of_lt hlt
      simp only [propEval_imp, propEval_atom, propEval_bot, Bool.or_false, Bool.or_eq_true,
        Bool.not_eq_true', σ, decide_eq_false_iff_not]
      by_cases hfu : f u = v
      · right; intro hfu'; exact hne (hfinj (hfu.trans hfu'.symm))
      · left; exact hfu
    · rw [hrubesCliqueAdj, propEval_balAnd]
      intro φ hφ
      rcases List.mem_flatMap.mp hφ with ⟨u, _, h1⟩
      rcases List.mem_flatMap.mp h1 with ⟨u', _, h2⟩
      rcases List.mem_flatMap.mp h2 with ⟨v, _, h3⟩
      rcases List.mem_map.mp h3 with ⟨w, hw, rfl⟩
      have hvw_ne : w ≠ v := of_decide_eq_true (List.mem_filter.mp hw).2
      have hne : v ≠ w := hvw_ne.symm
      split_ifs
      simp only [propEval_imp, propEval_atom, Bool.or_eq_true, Bool.not_eq_true',
        σ, decide_eq_false_iff_not]
      by_cases hfu : f u = v
      · by_cases hfu' : f u' = w
        · right; right
          refine hxs (edge hne) ?_
          rw [toFinset_edge, Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨hfu ▸ (emb u).2, hfu' ▸ (emb u').2⟩
        · right; left; exact hfu'
      · left; exact hfu
  simp [hcl] at hval

private def monoConst (n_in : ℕ) (b : Bool) : Circuit Monotone.signature n_in 1 :=
  Circuit.oneGate (.const b) Fin.elim0

@[simp] private theorem eval_monoConst {n_in : ℕ} (b : Bool) (x : Fin n_in → Bool) (j : Fin 1) :
    (monoConst n_in b).eval Monotone.interpretation x j = b := rfl

@[simp] private theorem size_monoConst (n_in : ℕ) (b : Bool) :
    (monoConst n_in b).size = 1 := rfl

private def monoInput (n_in : ℕ) (i : Fin n_in) : Circuit Monotone.signature n_in 1 :=
  Circuit.wiring Monotone.signature (fun _ => i)

@[simp] private theorem eval_monoInput {n_in : ℕ} (i : Fin n_in) (x : Fin n_in → Bool)
    (j : Fin 1) : (monoInput n_in i).eval Monotone.interpretation x j = x i := rfl

@[simp] private theorem size_monoInput (n_in : ℕ) (i : Fin n_in) :
    (monoInput n_in i).size = 0 := rfl

private def monoAnd {n_in : ℕ} (c₁ c₂ : Circuit Monotone.signature n_in 1) :
    Circuit Monotone.signature n_in 1 :=
  (Circuit.oneGate (σ := Monotone.signature) .and id).comp
    (Circuit.pi (fun i : Fin 2 => if i.val = 0 then c₁ else c₂))

@[simp] private theorem eval_monoAnd {n_in : ℕ} (c₁ c₂ : Circuit Monotone.signature n_in 1)
    (x : Fin n_in → Bool) (j : Fin 1) :
    (monoAnd c₁ c₂).eval Monotone.interpretation x j =
      (c₁.eval Monotone.interpretation x 0 && c₂.eval Monotone.interpretation x 0) := by
  simp [monoAnd]

private theorem size_monoAnd {n_in : ℕ} (c₁ c₂ : Circuit Monotone.signature n_in 1) :
    (monoAnd c₁ c₂).size = c₁.size + c₂.size + 1 := by
  simp only [monoAnd, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, Fin.sum_univ_two]
  rfl

private def monoOr {n_in : ℕ} (c₁ c₂ : Circuit Monotone.signature n_in 1) :
    Circuit Monotone.signature n_in 1 :=
  (Circuit.oneGate (σ := Monotone.signature) .or id).comp
    (Circuit.pi (fun i : Fin 2 => if i.val = 0 then c₁ else c₂))

@[simp] private theorem eval_monoOr {n_in : ℕ} (c₁ c₂ : Circuit Monotone.signature n_in 1)
    (x : Fin n_in → Bool) (j : Fin 1) :
    (monoOr c₁ c₂).eval Monotone.interpretation x j =
      (c₁.eval Monotone.interpretation x 0 || c₂.eval Monotone.interpretation x 0) := by
  simp [monoOr]

private theorem size_monoOr {n_in : ℕ} (c₁ c₂ : Circuit Monotone.signature n_in 1) :
    (monoOr c₁ c₂).size = c₁.size + c₂.size + 1 := by
  simp only [monoOr, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate, Fin.sum_univ_two]
  rfl

private def monoOrList {n_in : ℕ} :
    List (Circuit Monotone.signature n_in 1) → Circuit Monotone.signature n_in 1
  | [] => monoConst n_in false
  | c :: cs => monoOr c (monoOrList cs)

private theorem eval_monoOrList {n_in : ℕ} (cs : List (Circuit Monotone.signature n_in 1))
    (x : Fin n_in → Bool) :
    (monoOrList cs).eval Monotone.interpretation x 0 = true ↔
      ∃ c ∈ cs, c.eval Monotone.interpretation x 0 = true := by
  induction cs with
  | nil => simp [monoOrList]
  | cons c cs ih =>
    simp only [monoOrList, eval_monoOr, Bool.or_eq_true, ih, List.mem_cons]
    exact ⟨fun h => h.elim (fun hc => ⟨c, Or.inl rfl, hc⟩)
      (fun ⟨c', hc', hv⟩ => ⟨c', Or.inr hc', hv⟩),
      fun ⟨c', hc', hv⟩ => hc'.elim (fun hEq => Or.inl (hEq ▸ hv))
        (fun hmem => Or.inr ⟨c', hmem, hv⟩)⟩

private theorem size_monoOrList_le {n_in : ℕ} (cs : List (Circuit Monotone.signature n_in 1))
    {B : ℕ} (hB : ∀ c ∈ cs, c.size ≤ B) :
    (monoOrList cs).size ≤ cs.length * (B + 1) + 1 := by
  induction cs with
  | nil => simp [monoOrList]
  | cons c cs ih =>
    have hc := hB c List.mem_cons_self
    have hrec := ih (fun c' hc' => hB c' (List.mem_cons_of_mem _ hc'))
    rw [monoOrList, size_monoOr, List.length_cons]
    nlinarith

private noncomputable def poolBaseGate {n k : ℕ} (φ : Proposition (HrubesAtom n k)) :
    Circuit Monotone.signature (edgeCount n) 1 :=
  if @decide (IFregeSchema φ) (Classical.propDecidable _) then
    monoConst (edgeCount n) true
  else
    match φ with
    | .imp (.atom (.pEdge _)) .falsum => monoConst (edgeCount n) true
    | .imp (.atom (.rEdge e)) .falsum => monoInput (edgeCount n) e
    | _ => monoConst (edgeCount n) false

private theorem size_poolBaseGate_le {n k : ℕ} (φ : Proposition (HrubesAtom n k)) :
    (poolBaseGate φ).size ≤ 1 := by
  unfold poolBaseGate
  split_ifs
  · exact le_rfl
  · cases φ with
    | imp A B =>
      cases A with
      | atom a =>
        cases B with
        | falsum => cases a <;> simp
        | _ => simp
      | _ => simp
    | _ => simp

private noncomputable def poolBaseLayer {n k : ℕ}
    (F : List (Proposition (HrubesAtom n k))) :
    Circuit Monotone.signature (edgeCount n) F.length :=
  Circuit.pi (fun j : Fin F.length => poolBaseGate (F.get j))

private theorem size_poolBaseLayer_le {n k : ℕ}
    (F : List (Proposition (HrubesAtom n k))) :
    (poolBaseLayer F).size ≤ F.length := by
  rw [poolBaseLayer, Circuit.size_pi]
  calc
    ∑ j : Fin F.length, (poolBaseGate (F.get j)).size
      ≤ ∑ _j : Fin F.length, 1 :=
        Finset.sum_le_sum fun j _ => size_poolBaseGate_le (F.get j)
    _ = F.length := by simp

private def poolFindIdx {Atom : Type*} [DecidableEq Atom]
    (F : List (Proposition Atom)) (ψ : Proposition Atom) : Option (Fin F.length) :=
  (List.finRange F.length).find? (fun i => F.get i == ψ)

private theorem poolFindIdx_eq {Atom : Type*} [DecidableEq Atom]
    {F : List (Proposition Atom)} {ψ : Proposition Atom} {i : Fin F.length}
    (h : poolFindIdx F ψ = some i) : F.get i = ψ := by
  have h' : (List.finRange F.length).find? (fun k : Fin F.length => F.get k == ψ) = some i := h
  exact eq_of_beq (@List.find?_some _ (fun k : Fin F.length => F.get k == ψ) _ _ h')

private theorem poolFindIdx_some_iff {Atom : Type*} [DecidableEq Atom]
    (F : List (Proposition Atom)) (ψ : Proposition Atom) :
    (∃ i : Fin F.length, poolFindIdx F ψ = some i ∧ F.get i = ψ) ↔ ψ ∈ F := by
  constructor
  · rintro ⟨i, _, rfl⟩
    exact F.get_mem i
  · intro hmem
    cases hfind : poolFindIdx F ψ with
    | some i =>
      exact ⟨i, rfl, poolFindIdx_eq hfind⟩
    | none =>
      have hfind' : (List.finRange F.length).find? (fun k => F.get k == ψ) = none := hfind
      rcases List.mem_iff_get.mp hmem with ⟨j, rfl⟩
      have hnone := List.find?_eq_none.mp hfind' j (List.mem_finRange j)
      simp at hnone

private def poolStepTerms {Atom : Type*} [DecidableEq Atom]
    (F : List (Proposition Atom)) (j : Fin F.length) :
    List (Circuit Monotone.signature F.length 1) :=
  let φ := F.get j
  let mpTerms : List (Circuit Monotone.signature F.length 1) :=
    (List.finRange F.length).filterMap fun i =>
      match F.get i with
      | .imp α β =>
        if β == φ then
          match poolFindIdx F α with
          | some iα => some (monoAnd (monoInput F.length i) (monoInput F.length iα))
          | none => none
        else none
      | _ => none
  let introTerms : List (Circuit Monotone.signature F.length 1) :=
    match φ with
    | .and α β =>
      match poolFindIdx F α, poolFindIdx F β with
      | some iα, some iβ => [monoAnd (monoInput F.length iα) (monoInput F.length iβ)]
      | _, _ => []
    | .or α β =>
      (match poolFindIdx F α with | some iα => [monoInput F.length iα] | none => []) ++
      (match poolFindIdx F β with | some iβ => [monoInput F.length iβ] | none => [])
    | _ => []
  monoInput F.length j :: (mpTerms ++ introTerms)

private def poolStepLayer {Atom : Type*} [DecidableEq Atom]
    (F : List (Proposition Atom)) :
    Circuit Monotone.signature F.length F.length :=
  Circuit.pi (fun j : Fin F.length => monoOrList (poolStepTerms F j))

private theorem size_poolStepLayer_le {Atom : Type*} [DecidableEq Atom]
    (F : List (Proposition Atom)) :
    (poolStepLayer F).size ≤ F.length * (2 * F.length + 9) := by
  rw [poolStepLayer, Circuit.size_pi]
  have hgate : ∀ j : Fin F.length,
      (monoOrList (poolStepTerms F j)).size ≤ 2 * F.length + 9 := by
    intro j
    have hterms_size : ∀ c ∈ poolStepTerms F j, c.size ≤ 1 := by
      intro c hc
      simp only [poolStepTerms, List.mem_cons, List.mem_append] at hc
      rcases hc with rfl | hmp | hintro
      · simp
      · rcases List.mem_filterMap.mp hmp with ⟨i, _, hi⟩
        revert hi
        cases F.get i with
        | imp α β =>
          dsimp only []
          split_ifs
          · cases poolFindIdx F α with
            | none => intro h; cases h
            | some iα =>
              intro h; injection h with hEq; subst hEq
              rw [size_monoAnd]; simp
          · intro h; cases h
        | _ => intro h; cases h
      · revert hintro
        cases F.get j with
        | and α β =>
          dsimp only []
          cases poolFindIdx F α with
          | none => simp
          | some iα =>
            cases poolFindIdx F β with
            | none => simp
            | some iβ =>
              simp only [List.mem_singleton]
              rintro rfl
              rw [size_monoAnd]; simp
        | or α β =>
          dsimp only []
          intro hintro
          simp only [List.mem_append] at hintro
          rcases hintro with hL | hR
          · revert hL
            cases poolFindIdx F α with
            | none => simp
            | some iα => simp only [List.mem_singleton]; rintro rfl; simp
          · revert hR
            cases poolFindIdx F β with
            | none => simp
            | some iβ => simp only [List.mem_singleton]; rintro rfl; simp
        | _ => intro h; cases h
    have hterms_len : (poolStepTerms F j).length ≤ F.length + 4 := by
      simp only [poolStepTerms, List.length_cons, List.length_append]
      have hintro_len : (match F.get j with
          | .and α β =>
            match poolFindIdx F α, poolFindIdx F β with
            | some iα, some iβ => [monoAnd (monoInput F.length iα) (monoInput F.length iβ)]
            | _, _ => []
          | .or α β =>
            (match poolFindIdx F α with | some iα => [monoInput F.length iα] | none => []) ++
            (match poolFindIdx F β with | some iβ => [monoInput F.length iβ] | none => [])
          | _ => ([] : List (Circuit Monotone.signature F.length 1))).length ≤ 2 := by
        cases F.get j with
        | and α β => dsimp only []; cases poolFindIdx F α <;> cases poolFindIdx F β <;> simp
        | or α β => dsimp only []; cases poolFindIdx F α <;> cases poolFindIdx F β <;> simp
        | _ => simp
      calc
        _ ≤ (List.finRange F.length).length + 2 + 1 :=
          Nat.add_le_add (Nat.add_le_add (List.length_filterMap_le _ _) hintro_len) le_rfl
        _ ≤ F.length + 4 := by simp
    have hsz := size_monoOrList_le (poolStepTerms F j) hterms_size
    nlinarith
  calc
    ∑ j : Fin F.length, (monoOrList (poolStepTerms F j)).size
      ≤ ∑ _j : Fin F.length, (2 * F.length + 9) :=
        Finset.sum_le_sum fun j _ => hgate j
    _ = F.length * (2 * F.length + 9) := by simp

private noncomputable def poolIterLayer {n k : ℕ}
    (F : List (Proposition (HrubesAtom n k))) :
    ℕ → Circuit Monotone.signature (edgeCount n) F.length
  | 0 => poolBaseLayer F
  | t + 1 => (poolStepLayer F).comp (poolIterLayer F t)

private theorem size_poolIterLayer_le {n k : ℕ}
    (F : List (Proposition (HrubesAtom n k))) (t : ℕ) :
    (poolIterLayer F t).size ≤ F.length + t * (F.length * (2 * F.length + 9)) := by
  induction t with
  | zero =>
    simp only [poolIterLayer, zero_mul, add_zero]
    exact size_poolBaseLayer_le F
  | succ t ih =>
    rw [poolIterLayer, Circuit.size_comp]
    have hs := size_poolStepLayer_le F
    nlinarith

private theorem stepLayer_increasing {Atom : Type*} [DecidableEq Atom]
    (F : List (Proposition Atom)) (y : Fin F.length → Bool) (j : Fin F.length) :
    y j = true → (poolStepLayer F).eval Monotone.interpretation y j = true := by
  intro hy
  simp only [poolStepLayer, Circuit.eval_pi]
  rw [eval_monoOrList]
  exact ⟨monoInput F.length j, List.mem_cons_self, hy⟩

private theorem iterLayer_fixed_point {n k : ℕ}
    (F : List (Proposition (HrubesAtom n k))) (x : Fin (edgeCount n) → Bool) :
    let y := (poolIterLayer F (F.length + 1)).eval Monotone.interpretation x
    (poolStepLayer F).eval Monotone.interpretation y = y := by
  set m := F.length
  let yAt : ℕ → (Fin m → Bool) := fun t => (poolIterLayer F t).eval Monotone.interpretation x
  have hstep : ∀ t : ℕ, yAt (t + 1) = (poolStepLayer F).eval Monotone.interpretation (yAt t) := by
    intro t; simp only [yAt, poolIterLayer, Circuit.eval_comp]
  let cardTrue : (Fin m → Bool) → ℕ :=
    fun y => (Finset.univ.filter (fun j : Fin m => y j = true)).card
  have hcard_le : ∀ y : Fin m → Bool, cardTrue y ≤ m := by
    intro y
    calc
      cardTrue y ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := Fintype.card_fin m
  have hstrict : ∀ t : ℕ, yAt (t + 1) ≠ yAt t → cardTrue (yAt t) + 1 ≤ cardTrue (yAt (t + 1)) := by
    intro t hne
    have hsub : Finset.univ.filter (fun j => yAt t j = true) ⊂
        Finset.univ.filter (fun j => yAt (t + 1) j = true) := by
      rw [Finset.ssubset_iff_of_subset (fun j hj => by
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_univ j, hstep t ▸ stepLayer_increasing F (yAt t) j hj.2⟩)]
      by_contra hnot
      push Not at hnot
      apply hne
      funext j
      cases h1 : yAt t j with
      | true => exact hstep t ▸ stepLayer_increasing F (yAt t) j h1
      | false =>
        cases h2 : yAt (t + 1) j with
        | false => rfl
        | true =>
          have hjmem : j ∈ Finset.univ.filter (fun k : Fin m => yAt (t + 1) k = true) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, h2⟩
          have hj := hnot j hjmem
          rw [Finset.mem_filter, h1] at hj
          cases hj.2
    exact Finset.card_lt_card hsub
  have hex_eq : ∃ t ≤ m, yAt (t + 1) = yAt t := by
    by_contra hall
    push Not at hall
    have hgrow : ∀ t ≤ m + 1, t ≤ cardTrue (yAt t) := by
      intro t
      induction t with
      | zero => intro _; exact Nat.zero_le _
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have h2 := hstrict t (hall t (by omega))
        omega
    have h1 := hgrow (m + 1) le_rfl
    have h2 := hcard_le (yAt (m + 1))
    omega
  rcases hex_eq with ⟨t₀, ht₀, heq₀⟩
  have hconst : ∀ d : ℕ, yAt (t₀ + d) = yAt t₀ := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [← Nat.add_assoc, hstep (t₀ + d), ih, ← hstep t₀, heq₀]
  have hm1 : yAt (m + 1) = yAt t₀ := by
    have : m + 1 = t₀ + (m + 1 - t₀) := by omega
    rw [this]; exact hconst (m + 1 - t₀)
  change (poolStepLayer F).eval Monotone.interpretation (yAt (m + 1)) = yAt (m + 1)
  rw [hm1, ← hstep t₀, heq₀]

private theorem iterLayer_sound_coloring {n k : ℕ}
    (F : List (Proposition (HrubesAtom n k)))
    (x : Fin (edgeCount n) → Bool) (σ : HrubesAtom n k → Bool)
    (hp : ∀ e, σ (.pEdge e) = false)
    (hr : ∀ e, x e = true → σ (.rEdge e) = false) :
    ∀ (t : ℕ) (j : Fin F.length),
      (poolIterLayer F t).eval Monotone.interpretation x j = true →
        propEval σ (F.get j) = true := by
  intro t
  induction t with
  | zero =>
    intro j hj
    simp only [poolIterLayer, poolBaseLayer, Circuit.eval_pi, poolBaseGate] at hj
    by_cases hax : @decide (IFregeSchema (F.get j)) (Classical.propDecidable _) = true
    · exact (@of_decide_eq_true _ (Classical.propDecidable _) hax).eval_true σ
    · simp only [hax, Bool.false_eq_true, ↓reduceIte] at hj
      revert hj
      cases hφ : F.get j with
      | imp A B =>
        cases A with
        | atom a =>
          cases B with
          | falsum =>
            cases a with
            | pEdge e => intro _; simp [hp e]
            | rEdge e =>
              simp only [eval_monoInput]
              intro hx
              simp [hr e hx]
            | qClique _ _ => simp
            | zColor _ _ => simp
          | _ => simp
        | _ => simp
      | _ => simp
  | succ t ih =>
    intro j hj
    simp only [poolIterLayer, Circuit.eval_comp, poolStepLayer, Circuit.eval_pi] at hj
    rw [eval_monoOrList] at hj
    rcases hj with ⟨c, hc, hval⟩
    simp only [poolStepTerms, List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hmp | hintro
    · exact ih j hval
    · rcases List.mem_filterMap.mp hmp with ⟨i, _, hi⟩
      have hc_eq : ∃ α β iα, F.get i = .imp α β ∧ (β == F.get j) = true ∧
          poolFindIdx F α = some iα ∧
          c = monoAnd (monoInput F.length i) (monoInput F.length iα) := by
        revert hi
        cases hFi : F.get i with
        | imp α β =>
          dsimp only []
          by_cases hβ : (β == F.get j) = true
          · simp only [hβ, ↓reduceIte]
            cases hfind : poolFindIdx F α with
            | none => intro h; cases h
            | some iα =>
              intro h
              injection h with hEq
              exact ⟨α, β, iα, rfl, hβ, hfind, hEq.symm⟩
          · simp only [hβ, Bool.false_eq_true, ↓reduceIte]; intro h; cases h
        | _ => intro h; cases h
      rcases hc_eq with ⟨α, β, iα, hFi, hβ, hfind, rfl⟩
      simp only [eval_monoAnd, eval_monoInput, Bool.and_eq_true] at hval
      rcases hval with ⟨hi_t, hiα_t⟩
      have h1 := ih i hi_t
      rw [hFi, propEval_imp, Bool.or_eq_true, Bool.not_eq_true'] at h1
      have h2 := ih iα hiα_t
      rw [poolFindIdx_eq hfind] at h2
      rw [← eq_of_beq hβ]
      exact h1.resolve_left (by simp [h2])
    · have hc_intro :
        (∃ α β iα iβ, F.get j = .and α β ∧ poolFindIdx F α = some iα ∧
          poolFindIdx F β = some iβ ∧
          c = monoAnd (monoInput F.length iα) (monoInput F.length iβ)) ∨
        (∃ α β iα, F.get j = .or α β ∧ poolFindIdx F α = some iα ∧
          c = monoInput F.length iα) ∨
        (∃ α β iβ, F.get j = .or α β ∧ poolFindIdx F β = some iβ ∧
          c = monoInput F.length iβ) := by
        revert hintro
        cases hFj : F.get j with
        | and α β =>
          dsimp only []
          cases hfα : poolFindIdx F α with
          | none => intro h; cases h
          | some iα =>
            cases hfβ : poolFindIdx F β with
            | none => intro h; cases h
            | some iβ =>
              simp only [List.mem_singleton]
              intro hc_eq
              exact Or.inl ⟨α, β, iα, iβ, rfl, hfα, hfβ, hc_eq⟩
        | or α β =>
          dsimp only []
          intro hintro
          rcases List.mem_append.mp hintro with hL | hR
          · revert hL
            cases hfα : poolFindIdx F α with
            | none => intro h; cases h
            | some iα =>
              simp only [List.mem_singleton]
              intro hc_eq
              exact Or.inr (Or.inl ⟨α, β, iα, rfl, hfα, hc_eq⟩)
          · revert hR
            cases hfβ : poolFindIdx F β with
            | none => intro h; cases h
            | some iβ =>
              simp only [List.mem_singleton]
              intro hc_eq
              exact Or.inr (Or.inr ⟨α, β, iβ, rfl, hfβ, hc_eq⟩)
        | _ => intro h; cases h
      rcases hc_intro with
        ⟨α, β, iα, iβ, hFj, hfα, hfβ, rfl⟩ |
        ⟨α, β, iα, hFj, hfα, rfl⟩ |
        ⟨α, β, iβ, hFj, hfβ, rfl⟩
      · simp only [eval_monoAnd, eval_monoInput, Bool.and_eq_true] at hval
        rcases hval with ⟨h1, h2⟩
        have e1 := poolFindIdx_eq hfα
        have e2 := poolFindIdx_eq hfβ
        rw [hFj]
        simp [propEval_and, e1 ▸ ih iα h1, e2 ▸ ih iβ h2]
      · simp only [eval_monoInput] at hval
        have e1 := poolFindIdx_eq hfα
        rw [hFj]
        simp [propEval_or, e1 ▸ ih iα hval]
      · simp only [eval_monoInput] at hval
        have e2 := poolFindIdx_eq hfβ
        rw [hFj]
        simp [propEval_or, e2 ▸ ih iβ hval]

private def hrubesSlash {Atom : Type*} (sPred : Proposition Atom → Prop) :
    Proposition Atom → Prop
  | .atom a => sPred (.atom a)
  | .falsum => False
  | .and α β => hrubesSlash sPred α ∧ hrubesSlash sPred β
  | .or α β => hrubesSlash sPred α ∨ hrubesSlash sPred β
  | .imp α β => (hrubesSlash sPred α → hrubesSlash sPred β) ∧ sPred (.imp α β)

/-- **Hrubeš Monotone Feasible Interpolation**: From any subformula-closed formula pool
`F₀` proving `hrubesTau n k` in intuitionistic Frege (`IFregePool F₀ (hrubesTau n k)`), we can
construct a monotone Boolean circuit `C` of size `≤ 12 * (F₀.length + 1) ^ 3` separating
`k`-cliques from `(k - 1)`-colorable graphs on `n` vertices.
-/
theorem hrubes_monotone_circuit_of_pool {n k : ℕ}
    (F₀ : List (Proposition (HrubesAtom n k)))
    (hsub₀ : ∀ ψ ∈ F₀, ∀ δ ∈ propSubformulas ψ, δ ∈ F₀)
    (hpool₀ : IFregePool F₀ (hrubesTau n k)) :
    ∃ C : Circuit Monotone.signature (edgeCount n) 1,
      C.size ≤ 12 * (F₀.length + 1) ^ 3 ∧
      Clique.Separates k (k - 1) (fun x => C.eval Monotone.interpretation x 0) := by
  let F := F₀.dedup
  have hF_len : F.length ≤ F₀.length := (List.dedup_sublist F₀).length_le
  have hsub : ∀ ψ ∈ F, ∀ δ ∈ propSubformulas ψ, δ ∈ F := by
    intro ψ hψ δ hδ
    exact List.mem_dedup.mpr (hsub₀ ψ (List.mem_dedup.mp hψ) δ hδ)
  have hpool : IFregePool F (hrubesTau n k) :=
    hpool₀.mono (fun ψ hψ => List.mem_dedup.mpr hψ)
  have htau_mem : hrubesTau n k ∈ F := hpool.mem
  have hcol_neg_mem : Proposition.imp (hrubesColor n k) ⊥ ∈ F :=
    hsub (hrubesTau n k) htau_mem _ (by simp [hrubesTau, propSubformulas])
  rcases List.mem_iff_get.mp hcol_neg_mem with ⟨outIdx, houtIdx⟩
  let iterC := poolIterLayer F (F.length + 1)
  let C : Circuit Monotone.signature (edgeCount n) 1 :=
    iterC.comapOutputs (fun _ => outIdx)
  refine ⟨C, ?_, ?_⟩
  · change iterC.size ≤ _
    have hsz := size_poolIterLayer_le F (F.length + 1)
    let M := F₀.length + 1
    have hFM : F.length ≤ M := by dsimp only [M]; omega
    have hFM1 : F.length + 1 ≤ M := by dsimp only [M]; omega
    have hM1 : 1 ≤ M := by dsimp only [M]; omega
    have h2F9 : 2 * F.length + 9 ≤ 11 * M := by dsimp only [M]; omega
    have hprod1 : F.length * (2 * F.length + 9) ≤ 11 * (M * M) := by
      calc
        F.length * (2 * F.length + 9) ≤ M * (11 * M) := Nat.mul_le_mul hFM h2F9
        _ = 11 * (M * M) := by ring
    have hprod2 : (F.length + 1) * (F.length * (2 * F.length + 9)) ≤ 11 * M ^ 3 := by
      calc
        (F.length + 1) * (F.length * (2 * F.length + 9))
          ≤ M * (11 * (M * M)) := Nat.mul_le_mul hFM1 hprod1
        _ = 11 * M ^ 3 := by ring
    have hM_le_cu : M ≤ M ^ 3 := Nat.le_self_pow (by omega) M
    calc
      iterC.size ≤ F.length + (F.length + 1) * (F.length * (2 * F.length + 9)) := hsz
      _ ≤ M + 11 * M ^ 3 := Nat.add_le_add hFM hprod2
      _ ≤ M ^ 3 + 11 * M ^ 3 := Nat.add_le_add_right hM_le_cu _
      _ = 12 * M ^ 3 := by ring
  · refine ⟨?_, ?_⟩
    · intro x hx
      let y : Fin F.length → Bool := iterC.eval Monotone.interpretation x
      have hfp : (poolStepLayer F).eval Monotone.interpretation y = y :=
        iterLayer_fixed_point F x
      have hy_ge_base : ∀ j : Fin F.length,
          (poolBaseLayer F).eval Monotone.interpretation x j = true → y j = true := by
        intro j hbase
        have hmono : ∀ t : ℕ,
            (poolIterLayer F t).eval Monotone.interpretation x j = true := by
          intro t
          induction t with
          | zero => exact hbase
          | succ t ih =>
            simp only [poolIterLayer, Circuit.eval_comp]
            exact stepLayer_increasing F _ j ih
        exact hmono (F.length + 1)
      let inClos : Proposition (HrubesAtom n k) → Prop :=
        fun φ => ∃ j : Fin F.length, F.get j = φ ∧ y j = true
      let sPred : Proposition (HrubesAtom n k) → Prop :=
        fun φ => hrubesAPred x φ ∧ inClos φ
      have hinClos_ax : ∀ {φ}, φ ∈ F → IFregeSchema φ → inClos φ := by
        intro φ hφ hax
        rcases List.mem_iff_get.mp hφ with ⟨j, rfl⟩
        refine ⟨j, rfl, hy_ge_base j ?_⟩
        simp only [poolBaseLayer, Circuit.eval_pi, poolBaseGate]
        have hdec : @decide (IFregeSchema (F.get j)) (Classical.propDecidable _) = true :=
          @decide_eq_true _ (Classical.propDecidable _) hax
        simp only [hdec, ↓reduceIte, eval_monoConst]
      have hinClos_mp : ∀ {α β}, β ∈ F → inClos (.imp α β) → inClos α → inClos β := by
        intro α β hβ ⟨i, hi, hyi⟩ ⟨iα, hiα, hyiα⟩
        rcases List.mem_iff_get.mp hβ with ⟨j, rfl⟩
        refine ⟨j, rfl, ?_⟩
        rw [← hfp]
        simp only [poolStepLayer, Circuit.eval_pi]
        rw [eval_monoOrList]
        rcases (poolFindIdx_some_iff F α).mpr (hiα ▸ F.get_mem iα) with ⟨kα, hkα, hkα_eq⟩
        have hykα : y kα = true := by
          have hnodup : F.Nodup := List.nodup_dedup F₀
          have heqIdx : kα = iα := hnodup.get_inj_iff.mp (hkα_eq.trans hiα.symm)
          exact heqIdx ▸ hyiα
        refine ⟨monoAnd (monoInput F.length i) (monoInput F.length kα), ?_, ?_⟩
        · simp only [poolStepTerms, List.mem_cons, List.mem_append]
          right; left
          refine List.mem_filterMap.mpr ⟨i, List.mem_finRange i, ?_⟩
          rw [hi]
          dsimp only []
          simp only [beq_self_eq_true, ↓reduceIte, hkα]
        · simp [hyi, hykα]
      have hinClos_andI : ∀ {α β}, Proposition.and α β ∈ F →
          inClos α → inClos β → inClos (.and α β) := by
        intro α β hmem ⟨iα, hiα, hyiα⟩ ⟨iβ, hiβ, hyiβ⟩
        rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
        refine ⟨j, hj, ?_⟩
        rw [← hfp]
        simp only [poolStepLayer, Circuit.eval_pi]
        rw [eval_monoOrList]
        have hnodup : F.Nodup := List.nodup_dedup F₀
        rcases (poolFindIdx_some_iff F α).mpr (hiα ▸ F.get_mem iα) with ⟨kα, hkα, hkα_eq⟩
        rcases (poolFindIdx_some_iff F β).mpr (hiβ ▸ F.get_mem iβ) with ⟨kβ, hkβ, hkβ_eq⟩
        have hykα : y kα = true := (hnodup.get_inj_iff.mp (hkα_eq.trans hiα.symm)) ▸ hyiα
        have hykβ : y kβ = true := (hnodup.get_inj_iff.mp (hkβ_eq.trans hiβ.symm)) ▸ hyiβ
        refine ⟨monoAnd (monoInput F.length kα) (monoInput F.length kβ), ?_, ?_⟩
        · simp only [poolStepTerms, List.mem_cons, List.mem_append, hj, hkα, hkβ]
          exact Or.inr (Or.inr (Or.inl trivial))
        · simp [hykα, hykβ]
      have hinClos_orI₁ : ∀ {α β}, Proposition.or α β ∈ F → inClos α → inClos (.or α β) := by
        intro α β hmem ⟨iα, hiα, hyiα⟩
        rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
        refine ⟨j, hj, ?_⟩
        rw [← hfp]
        simp only [poolStepLayer, Circuit.eval_pi]
        rw [eval_monoOrList]
        have hnodup : F.Nodup := List.nodup_dedup F₀
        rcases (poolFindIdx_some_iff F α).mpr (hiα ▸ F.get_mem iα) with ⟨kα, hkα, hkα_eq⟩
        have hykα : y kα = true := (hnodup.get_inj_iff.mp (hkα_eq.trans hiα.symm)) ▸ hyiα
        refine ⟨monoInput F.length kα, ?_, hykα⟩
        simp only [poolStepTerms, List.mem_cons, List.mem_append, hj, hkα]
        exact Or.inr (Or.inr (Or.inl (Or.inl trivial)))
      have hinClos_orI₂ : ∀ {α β}, Proposition.or α β ∈ F → inClos β → inClos (.or α β) := by
        intro α β hmem ⟨iβ, hiβ, hyiβ⟩
        rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
        refine ⟨j, hj, ?_⟩
        rw [← hfp]
        simp only [poolStepLayer, Circuit.eval_pi]
        rw [eval_monoOrList]
        have hnodup : F.Nodup := List.nodup_dedup F₀
        rcases (poolFindIdx_some_iff F β).mpr (hiβ ▸ F.get_mem iβ) with ⟨kβ, hkβ, hkβ_eq⟩
        have hykβ : y kβ = true := (hnodup.get_inj_iff.mp (hkβ_eq.trans hiβ.symm)) ▸ hyiβ
        refine ⟨monoInput F.length kβ, ?_, hykβ⟩
        simp only [poolStepTerms, List.mem_cons, List.mem_append, hj, hkβ]
        exact Or.inr (Or.inr (Or.inr (Or.inl trivial)))
      have hsPred_mp : ∀ {α β}, β ∈ F → sPred (.imp α β) → sPred α → sPred β := by
        intro α β hβ ⟨ha1, hc1⟩ ⟨ha2, hc2⟩
        refine ⟨fun σ hp hr => ?_, hinClos_mp hβ hc1 hc2⟩
        have h1 := ha1 σ hp hr
        have h2 := ha2 σ hp hr
        simp only [propEval_imp, Bool.or_eq_true, Bool.not_eq_true'] at h1
        exact h1.resolve_left (by simp [h2])
      have hslash_to_sPred : ∀ φ ∈ F, hrubesSlash sPred φ → sPred φ := by
        intro φ
        induction φ with
        | atom _ => intro _ h; exact h
        | falsum => intro _ h; exact False.elim h
        | and α β ihα ihβ =>
          intro hmem ⟨h1, h2⟩
          have hαF : α ∈ F := hsub _ hmem α (by simp [propSubformulas, self_mem_propSubformulas])
          have hβF : β ∈ F := hsub _ hmem β (by simp [propSubformulas, self_mem_propSubformulas])
          have sα := ihα hαF h1
          have sβ := ihβ hβF h2
          exact ⟨fun σ hp hr => by simp [propEval_and, sα.1 σ hp hr, sβ.1 σ hp hr],
            hinClos_andI hmem sα.2 sβ.2⟩
        | or α β ihα ihβ =>
          intro hmem h
          have hαF : α ∈ F := hsub _ hmem α (by simp [propSubformulas, self_mem_propSubformulas])
          have hβF : β ∈ F := hsub _ hmem β (by simp [propSubformulas, self_mem_propSubformulas])
          rcases h with h1 | h2
          · have sα := ihα hαF h1
            exact ⟨fun σ hp hr => by simp [propEval_or, sα.1 σ hp hr],
              hinClos_orI₁ hmem sα.2⟩
          · have sβ := ihβ hβF h2
            exact ⟨fun σ hp hr => by simp [propEval_or, sβ.1 σ hp hr],
              hinClos_orI₂ hmem sβ.2⟩
        | imp _ _ _ _ => intro _ h; exact h.2
      have hslash_pool : ∀ {φ}, IFregePool F φ → hrubesSlash sPred φ := by
        intro φ hP
        induction hP with
        | @mp α β _ _ _ ih₁ ih₂ => exact ih₁.1 ih₂
        | @ax φ hmem hax =>
          have hs0 : sPred φ := ⟨fun σ _ _ => hax.eval_true σ, hinClos_ax hmem hax⟩
          cases hax with
          | axK A B =>
            have hAF : A ∈ F := hsub _ hmem A (by simp [propSubformulas, self_mem_propSubformulas])
            have hBAF : Proposition.imp B A ∈ F :=
              hsub _ hmem _ (by simp [propSubformulas])
            refine ⟨fun hA => ⟨fun _ => hA, hsPred_mp hBAF hs0 (hslash_to_sPred A hAF hA)⟩, hs0⟩
          | axS A B C =>
            have h1F : Proposition.imp (.imp A B) (.imp A C) ∈ F :=
              hsub _ hmem _ (by simp [propSubformulas])
            have h2F : Proposition.imp A C ∈ F :=
              hsub _ hmem _ (by simp [propSubformulas])
            refine ⟨fun hABC => ?_, hs0⟩
            have hs1 := hsPred_mp h1F hs0 hABC.2
            refine ⟨fun hAB => ?_, hs1⟩
            have hs2 := hsPred_mp h2F hs1 hAB.2
            exact ⟨fun hA => (hABC.1 hA).1 (hAB.1 hA), hs2⟩
          | andE₁ A B => exact ⟨fun h => h.1, hs0⟩
          | andE₂ A B => exact ⟨fun h => h.2, hs0⟩
          | andI A B =>
            have hAF : A ∈ F := hsub _ hmem A (by simp [propSubformulas, self_mem_propSubformulas])
            have h1F : Proposition.imp B (.and A B) ∈ F :=
              hsub _ hmem _ (by simp [propSubformulas])
            refine ⟨fun hA => ?_, hs0⟩
            exact ⟨fun hB => ⟨hA, hB⟩, hsPred_mp h1F hs0 (hslash_to_sPred A hAF hA)⟩
          | orI₁ A B => exact ⟨fun hA => Or.inl hA, hs0⟩
          | orI₂ A B => exact ⟨fun hB => Or.inr hB, hs0⟩
          | orE A B C =>
            have h1F : Proposition.imp (.imp B C) (.imp (.or A B) C) ∈ F :=
              hsub _ hmem _ (by simp [propSubformulas])
            have h2F : Proposition.imp (.or A B) C ∈ F :=
              hsub _ hmem _ (by simp [propSubformulas])
            refine ⟨fun hAC => ?_, hs0⟩
            have hs1 := hsPred_mp h1F hs0 hAC.2
            refine ⟨fun hBC => ?_, hs1⟩
            have hs2 := hsPred_mp h2F hs1 hBC.2
            refine ⟨fun hAB => ?_, hs2⟩
            rcases hAB with hA | hB
            · exact hAC.1 hA
            · exact hBC.1 hB
          | efq A => exact ⟨fun h => False.elim h, hs0⟩
      have hslash_balAnd : ∀ (l : List (Proposition (HrubesAtom n k))),
          l ≠ [] → (∀ A ∈ l, hrubesSlash sPred A) → hrubesSlash sPred (balAnd l) := by
        intro l
        induction hk : l.length using Nat.strong_induction_on generalizing l with
        | ind m ih =>
          match l with
          | [] => intro hne; exact absurd rfl hne
          | [A] => intro _ hall; simpa only [balAnd] using hall A List.mem_cons_self
          | A :: B :: rest =>
            subst hk
            intro _ hall
            rw [balAnd.eq_3]
            have h1 : ((A :: B :: rest).take ((A :: B :: rest).length / 2)).length <
                (A :: B :: rest).length := by
              simp only [List.length_take, List.length_cons]; omega
            have h2 : ((A :: B :: rest).drop ((A :: B :: rest).length / 2)).length <
                (A :: B :: rest).length := by
              simp only [List.length_drop, List.length_cons]; omega
            have hne1 : (A :: B :: rest).take ((A :: B :: rest).length / 2) ≠ [] := by
              intro h; have := congrArg List.length h
              simp only [List.length_take, List.length_cons, List.length_nil] at this; omega
            have hne2 : (A :: B :: rest).drop ((A :: B :: rest).length / 2) ≠ [] := by
              intro h; have := congrArg List.length h
              simp only [List.length_drop, List.length_cons, List.length_nil] at this; omega
            exact ⟨ih _ h1 _ rfl hne1 (fun X hX => hall X (List.mem_of_mem_take hX)),
                   ih _ h2 _ rfl hne2 (fun X hX => hall X (List.mem_of_mem_drop hX))⟩
      have hdisj_F : hrubesDisj n k ∈ F :=
        hsub _ htau_mem _ (by simp [hrubesTau, propSubformulas, self_mem_propSubformulas])
      have hslash_disj : hrubesSlash sPred (hrubesDisj n k) := by
        by_cases hE0 : edgeCount n = 0
        · have hnil : (List.finRange (edgeCount n)).map
              (fun e : Fin (edgeCount n) =>
                Proposition.or (.imp (.atom (HrubesAtom.pEdge (k := k) e)) ⊥)
                  (.imp (.atom (HrubesAtom.rEdge (k := k) e)) ⊥)) = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp [hE0]
          have htop : hrubesDisj n k = .imp .falsum .falsum := by
            simp only [hrubesDisj, hnil, balAnd]; rfl
          rw [htop] at hdisj_F ⊢
          exact hslash_pool (.ax hdisj_F (.efq .falsum))
        · refine hslash_balAnd _ (fun h => hE0 (by
            have := congrArg List.length h
            simpa using this)) ?_
          intro D hD
          have hDF : D ∈ F :=
            hsub _ hdisj_F D (mem_propSubformulas_balAnd hD)
          rcases List.mem_map.mp hD with ⟨e, _, rfl⟩
          cases hxe : x e with
          | false =>
            left
            have hpF : Proposition.imp (.atom (HrubesAtom.pEdge (k := k) e)) ⊥ ∈ F :=
              hsub _ hDF _ (by simp [propSubformulas])
            have ha_p : hrubesAPred (k := k) x
                (.imp (.atom (HrubesAtom.pEdge (k := k) e)) ⊥) := by
              intro σ hp _
              simp [hp e hxe]
            have hc_p : inClos (.imp (.atom (HrubesAtom.pEdge (k := k) e)) ⊥) := by
              rcases List.mem_iff_get.mp hpF with ⟨j, hj⟩
              refine ⟨j, hj, hy_ge_base j ?_⟩
              simp only [poolBaseLayer, Circuit.eval_pi, poolBaseGate, hj]
              split_ifs <;> rfl
            refine ⟨fun hpe => ?_, ⟨ha_p, hc_p⟩⟩
            have h0 := hpe.1 (fun _ => false) (fun _ _ => rfl) (fun _ => rfl)
            simp at h0
          | true =>
            right
            have hrF : Proposition.imp (.atom (HrubesAtom.rEdge (k := k) e)) ⊥ ∈ F :=
              hsub _ hDF _ (by simp [propSubformulas])
            have ha_r : hrubesAPred (k := k) x
                (.imp (.atom (HrubesAtom.rEdge (k := k) e)) ⊥) := by
              intro σ _ hr
              simp [hr e]
            have hc_r : inClos (.imp (.atom (HrubesAtom.rEdge (k := k) e)) ⊥) := by
              rcases List.mem_iff_get.mp hrF with ⟨j, hj⟩
              refine ⟨j, hj, hy_ge_base j ?_⟩
              simp only [poolBaseLayer, Circuit.eval_pi, poolBaseGate, hj]
              split_ifs
              · rfl
              · exact hxe
            refine ⟨fun hre => ?_, ⟨ha_r, hc_r⟩⟩
            have h0 := hre.1 (fun _ => false) (fun _ _ => rfl) (fun _ => rfl)
            simp at h0
      have hslash_tau := hslash_pool hpool
      have hslash_or := hslash_tau.1 hslash_disj
      rcases hslash_or with hcl_false | hcol_true
      · exact False.elim (not_hrubesAPred_neg_clique_of_clique hx hcl_false.2.1)
      · rcases hcol_true.2.2 with ⟨j, hj, hyj⟩
        have hnodup : F.Nodup := List.nodup_dedup F₀
        have heqIdx : outIdx = j := hnodup.get_inj_iff.mp (houtIdx.trans hj.symm)
        change y outIdx = true
        exact heqIdx ▸ hyj
    · intro x hcol
      rcases hcol with ⟨col⟩
      let σ : HrubesAtom n k → Bool := fun
        | .pEdge _ => false
        | .rEdge e => !x e
        | .qClique _ _ => false
        | .zColor v c => decide (col v = c)
      have hcol_eval : propEval σ (hrubesColor n k) = true := by
        simp only [hrubesColor, propEval_and, Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [hrubesColorTot, propEval_balAnd]
          intro φ hφ
          rcases List.mem_map.mp hφ with ⟨v, _, rfl⟩
          rw [propEval_balOr]
          refine ⟨.atom (.zColor v (col v)),
            List.mem_map.mpr ⟨col v, List.mem_finRange _, rfl⟩, ?_⟩
          simp [σ]
        · rw [hrubesColorProper, propEval_balAnd]
          intro φ hφ
          rcases List.mem_flatMap.mp hφ with ⟨c, _, h1⟩
          rcases List.mem_flatMap.mp h1 with ⟨v, _, h2⟩
          rcases List.mem_map.mp h2 with ⟨w, hw, rfl⟩
          have hlt : v < w := of_decide_eq_true (List.mem_filter.mp hw).2
          have hne : v ≠ w := ne_of_lt hlt
          split_ifs
          simp only [propEval_imp, propEval_atom, Bool.or_eq_true, Bool.not_eq_true',
            σ, decide_eq_false_iff_not]
          by_cases hcv : col v = c
          · by_cases hcw : col w = c
            · right; right
              have hnotadj : ¬ (graph x).Adj v w := fun hadj =>
                col.valid hadj (hcv.trans hcw.symm)
              rw [graph_adj hne] at hnotadj
              simpa using hnotadj
            · right; left; exact hcw
          · left; exact hcv
      by_cases hC : C.eval Monotone.interpretation x 0 = true
      · have hsnd := iterLayer_sound_coloring F x σ
          (fun _ => rfl) (fun e he => by simp [σ, he]) (F.length + 1) outIdx hC
        rw [houtIdx] at hsnd
        simp [hcol_eval] at hsnd
      · exact Bool.eq_false_iff.mpr hC

/-- **Exponential Intuitionistic Frege Lower Bound for Hrubeš's Clique–Coloring Tautologies**:
For `2 ≤ k` and `k ^ 4 ≤ n`, any subformula-closed formula pool `F₀` proving `hrubesTau n k`
in intuitionistic Frege satisfies `2 ^ (2 * Nat.sqrt k) < 12 * (F₀.length + 1) ^ 3`. -/
theorem two_pow_two_mul_sqrt_lt_ifregePool_of_hrubesTau {n k : ℕ}
    (hk : 2 ≤ k) (hn : k ^ 4 ≤ n)
    (F₀ : List (Proposition (HrubesAtom n k)))
    (hsub₀ : ∀ ψ ∈ F₀, ∀ δ ∈ propSubformulas ψ, δ ∈ F₀)
    (hpool₀ : IFregePool F₀ (hrubesTau n k)) :
    2 ^ (2 * Nat.sqrt k) < 12 * (F₀.length + 1) ^ 3 := by
  rcases hrubes_monotone_circuit_of_pool F₀ hsub₀ hpool₀ with ⟨C, hsz, hsep⟩
  exact lt_of_lt_of_le
    (Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_size_of_separates hk hn hsep) hsz

end CslibFrontier.Logics.Propositional.IntuitionisticFrege
