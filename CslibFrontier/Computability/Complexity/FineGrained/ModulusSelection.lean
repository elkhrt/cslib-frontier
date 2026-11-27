/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.ResidueCollisions
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Tactic.Linarith

/-!
# Deterministic Two-Prime Modulus Selection on Multi-Tape Turing Machines

This module implements deterministic multi-tape Turing machine algorithms with explicit
`ComputableInO` bounds for the two-prime modulus search of Chan and He's 3SUM-to-Convolution-3SUM
reduction:

1. Generic candidate-prime threshold scan `searchPrimeList` over a strictly increasing list `Q`;
2. First-prime search `firstPList` matching `ChanHe.firstP`;
3. Second-prime search `secondPList` matching `ChanHe.secondP`;
4. Two-prime product `modulusList` matching `ChanHe.modulus` in time
   `O((|Q| + 1) * (|Q| + |L₁| + |L₂| + |L₃| + 1) * modScale x ^ d)`.

## Main definitions

* `CslibFrontier.Complexity.searchPrimePred`, `CslibFrontier.Complexity.searchPrimeList`: generic
  candidate-prime scan.
* `CslibFrontier.Complexity.firstPList`, `CslibFrontier.Complexity.secondPList`,
  `CslibFrontier.Complexity.modulusList`: deterministic minimum-prime searches matching `ChanHe`.
* `CslibFrontier.Complexity.modLen`,
  `CslibFrontier.Complexity.modScale`: element-count and bit-scale
  complexity parameters.

## Main results

* `CslibFrontier.Complexity.firstPList_eq_firstP`,
  `CslibFrontier.Complexity.secondPList_eq_secondP`,
  `CslibFrontier.Complexity.modulusList_eq_modulus`: exact agreement with `ChanHe.modulus`.
* `CslibFrontier.Complexity.modulusList_pos`,
  `CslibFrontier.Complexity.modulusList_size_le`: positivity and
  bit-size bounds.
* `CslibFrontier.Complexity.computableInO_searchPrimeList`,
  `CslibFrontier.Complexity.computableInO_modulusList`: Turing machine time and space bounds.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.ThreeSum.ChanHe

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

attribute [local irreducible] encNat encIntBin encUnary

/-- Three-set collision threshold check `cᵢ * qLen ≤ Bᵢ` for `i = 1, 2, 3`. -/
def searchPrimePred (qLen B₁ B₂ B₃ c₁ c₂ c₃ : ℕ) : Bool :=
  decide (c₁ * qLen ≤ B₁) && (decide (c₂ * qLen ≤ B₂) && decide (c₃ * qLen ≤ B₃))

/-- Scalar parameters `((qLen, mul₀), ((B₁, B₂), B₃))` for candidate-prime scanning. -/
private abbrev SearchParams := (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)

/-- Triple of integer lists `(L₁, (L₂, L₃))`. -/
abbrev IntTriple := List ℤ × (List ℤ × List ℤ)

/-- Context tuple `(params, triple)` for candidate-prime scanning. -/
private abbrev SearchCtx := SearchParams × IntTriple

/-- Encoding of `SearchParams`. -/
private def encSearchParams : SearchParams ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair (encPair encNat encNat) encNat)

/-- Encoding of `IntTriple`. -/
@[expose] def encIntTriple : IntTriple ↪ List Bool :=
  encPair (encList encIntBin) (encPair (encList encIntBin) (encList encIntBin))

/-- Encoding of `SearchCtx`. -/
private def encSearchCtx : SearchCtx ↪ List Bool :=
  encPair encSearchParams encIntTriple

/-- One candidate-prime scan transition on `(acc, qs, ctx)`. -/
private def searchPrimeStep (st : Option ℕ × (List ℕ × SearchCtx)) :
    Option ℕ × (List ℕ × SearchCtx) :=
  let acc := st.1
  let qs := st.2.1
  let ctx := st.2.2
  if acc.isSome || qs.isEmpty then
    (acc, (qs.drop 1, ctx))
  else
    let q := qs.headD 0
    let M := ctx.1.1.2 * q
    let ok := searchPrimePred ctx.1.1.1 ctx.1.2.1.1 ctx.1.2.1.2 ctx.1.2.2
      (collList M ctx.2.1) (collList M ctx.2.2.1) (collList M ctx.2.2.2)
    (if ok then some q else none, (qs.drop 1, ctx))

/-- Deterministic scan over `Q` returning the first `q ∈ Q` meeting `searchPrimePred`, or `1`. -/
def searchPrimeList (Q : List ℕ) (mul₀ B₁ B₂ B₃ : ℕ) (L₁ L₂ L₃ : List ℤ) : ℕ :=
  ((searchPrimeStep^[Q.length]
    (none, (Q, (((Q.length, mul₀), ((B₁, B₂), B₃)), (L₁, (L₂, L₃)))))).1).getD 1

private def ctxPred (ctx : SearchCtx) (q : ℕ) : Bool :=
  let M := ctx.1.1.2 * q
  searchPrimePred ctx.1.1.1 ctx.1.2.1.1 ctx.1.2.1.2 ctx.1.2.2
    (collList M ctx.2.1) (collList M ctx.2.2.1) (collList M ctx.2.2.2)

private theorem iterate_searchPrimeStep (Q : List ℕ) (ctx : SearchCtx) (k : ℕ)
    (hk : k ≤ Q.length) :
    searchPrimeStep^[k] (none, (Q, ctx)) =
      ((Q.take k).foldl
        (fun acc q => if acc.isSome then acc else if ctxPred ctx q then some q else none) none,
        (Q.drop k, ctx)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (Nat.le_of_succ_le hk)]
    have hk_lt : k < Q.length := hk
    obtain ⟨q, qs, hdrop⟩ : ∃ q qs, Q.drop k = q :: qs := by
      cases hd : Q.drop k with
      | nil =>
        have := congrArg List.length hd
        simp [List.length_drop] at this
        omega
      | cons q qs => exact ⟨q, qs, rfl⟩
    have hq_eq : Q[k] = q := by
      have := List.drop_eq_getElem_cons hk_lt
      rw [hdrop] at this
      exact (List.cons.inj this).1.symm
    have hdrop_succ : Q.drop (k + 1) = qs := by
      rw [← List.drop_drop, hdrop]
      rfl
    have htake_succ : Q.take (k + 1) = Q.take k ++ [q] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt, Option.toList_some, hq_eq]
    rw [htake_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hdrop_succ]
    unfold searchPrimeStep
    dsimp only
    rw [hdrop]
    cases ((Q.take k).foldl
      (fun acc x => if acc.isSome then acc else if ctxPred ctx x then some x else none) none) <;>
      rfl

private theorem foldl_findFirst_some (P : ℕ → Bool) (qs : List ℕ) (r : ℕ) :
    qs.foldl (fun acc q => if acc.isSome then acc else if P q then some q else none) (some r) =
      some r := by
  induction qs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem foldl_findFirst_eq_minOrOne {Q : List ℕ} (hQ : List.Pairwise (· < ·) Q)
    (P : ℕ → Bool) :
    (Q.foldl (fun acc q => if acc.isSome then acc else if P q then some q else none) none).getD 1 =
      minOrOne {q ∈ Q.toFinset | P q = true} := by
  induction Q with
  | nil => simp [minOrOne]
  | cons q qs ih =>
    obtain ⟨hq_lt, hqs⟩ := List.pairwise_cons.mp hQ
    rw [List.foldl_cons]
    cases hp : P q
    · change (qs.foldl _ none).getD 1 = _
      rw [ih hqs]
      congr 1
      ext x
      simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hpx⟩
        exact ⟨Or.inr hx, hpx⟩
      · rintro ⟨rfl | hx, hpx⟩
        · rw [hp] at hpx; cases hpx
        · exact ⟨hx, hpx⟩
    · change (qs.foldl _ (some q)).getD 1 = _
      rw [foldl_findFirst_some, Option.getD_some]
      set T : Finset ℕ := {x ∈ (q :: qs).toFinset | P x = true}
      have hqT : q ∈ T := Finset.mem_filter.mpr ⟨by simp, hp⟩
      have hne : T.Nonempty := ⟨q, hqT⟩
      unfold minOrOne
      split_ifs
      refine le_antisymm ?_ (Finset.min'_le T q hqT)
      rw [Finset.le_min'_iff]
      intro x hx
      rcases List.mem_cons.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hx).1) with rfl | hxs'
      · exact le_rfl
      · exact (hq_lt x hxs').le

/-- First-prime list search matching `ChanHe.firstP`. -/
def firstPList (Q : List ℕ) (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) : ℕ :=
  searchPrimeList Q 1 (3 * Λ * L₁.length ^ 2) (3 * Λ * L₂.length ^ 2) (3 * Λ * L₃.length ^ 2)
    L₁ L₂ L₃

/-- Second-prime list search matching `ChanHe.secondP`. -/
def secondPList (Q : List ℕ) (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) (p : ℕ) : ℕ :=
  searchPrimeList Q p (3 * Λ * collList p L₁) (3 * Λ * collList p L₂) (3 * Λ * collList p L₃)
    L₁ L₂ L₃

/-- Deterministic two-prime modulus selection matching `ChanHe.modulus`. -/
def modulusList (Q : List ℕ) (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) : ℕ :=
  let p := firstPList Q Λ L₁ L₂ L₃
  p * secondPList Q Λ L₁ L₂ L₃ p

@[simp] theorem searchPrimeList_nil (mul₀ B₁ B₂ B₃ : ℕ) (L₁ L₂ L₃ : List ℤ) :
    searchPrimeList [] mul₀ B₁ B₂ B₃ L₁ L₂ L₃ = 1 := by unfold searchPrimeList; rfl

@[simp] theorem firstPList_nil (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) :
    firstPList [] Λ L₁ L₂ L₃ = 1 := by unfold firstPList searchPrimeList; rfl

@[simp] theorem secondPList_nil (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) (p : ℕ) :
    secondPList [] Λ L₁ L₂ L₃ p = 1 := by unfold secondPList searchPrimeList; rfl

@[simp] theorem modulusList_nil (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) :
    modulusList [] Λ L₁ L₂ L₃ = 1 := by simp [modulusList]

theorem searchPrimeList_mem_or_one (Q : List ℕ) (mul₀ B₁ B₂ B₃ : ℕ) (L₁ L₂ L₃ : List ℤ) :
    searchPrimeList Q mul₀ B₁ B₂ B₃ L₁ L₂ L₃ = 1 ∨
      searchPrimeList Q mul₀ B₁ B₂ B₃ L₁ L₂ L₃ ∈ Q := by
  let ctx : SearchCtx := (((Q.length, mul₀), ((B₁, B₂), B₃)), (L₁, (L₂, L₃)))
  unfold searchPrimeList
  rw [iterate_searchPrimeStep Q ctx Q.length le_rfl, List.take_length]
  dsimp only
  suffices ∀ (t : List ℕ) (acc : Option ℕ),
      (acc = none ∨ ∃ q ∈ Q, acc = some q) → (∀ z ∈ t, z ∈ Q) →
      let r := t.foldl
        (fun a q => if a.isSome then a else if ctxPred ctx q then some q else none) acc
      r.getD 1 = 1 ∨ r.getD 1 ∈ Q from
    this Q none (Or.inl rfl) fun _ h => h
  intro t
  induction t with
  | nil =>
    intro acc hacc _
    rcases hacc with rfl | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr hq
  | cons x xs ih =>
    intro acc hacc htQ
    dsimp only
    rw [List.foldl_cons]
    have hxQ : x ∈ Q := htQ x (List.mem_cons_self ..)
    have hxsQ : ∀ z ∈ xs, z ∈ Q := fun z hz => htQ z (List.mem_cons_of_mem _ hz)
    rcases acc with _ | r
    · cases ctxPred ctx x
      · exact ih none (Or.inl rfl) hxsQ
      · exact ih (some x) (Or.inr ⟨x, hxQ, rfl⟩) hxsQ
    · exact ih (some r) hacc hxsQ

theorem modulusList_pos {Q : List ℕ} (hQ : ∀ q ∈ Q, 0 < q) (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) :
    0 < modulusList Q Λ L₁ L₂ L₃ := by
  unfold modulusList firstPList secondPList
  dsimp only
  have hpos : ∀ mul₀ B₁ B₂ B₃, 0 < searchPrimeList Q mul₀ B₁ B₂ B₃ L₁ L₂ L₃ := by
    intro mul₀ B₁ B₂ B₃
    rcases searchPrimeList_mem_or_one Q mul₀ B₁ B₂ B₃ L₁ L₂ L₃ with h1 | hmem
    · rw [h1]; decide
    · exact hQ _ hmem
  exact Nat.mul_pos (hpos ..) (hpos ..)

theorem modulusList_size_le (Q : List ℕ) (Λ : ℕ) (L₁ L₂ L₃ : List ℤ) :
    (modulusList Q Λ L₁ L₂ L₃).size ≤ 2 * listMax Nat.size Q + 3 := by
  have h1sz : (1 : ℕ).size = 1 := by decide
  have hbound : ∀ mul₀ B₁ B₂ B₃,
      (searchPrimeList Q mul₀ B₁ B₂ B₃ L₁ L₂ L₃).size ≤ listMax Nat.size Q + 1 := by
    intro mul₀ B₁ B₂ B₃
    rcases searchPrimeList_mem_or_one Q mul₀ B₁ B₂ B₃ L₁ L₂ L₃ with h1 | hmem
    · rw [h1, h1sz]; omega
    · exact (le_listMax (f := Nat.size) hmem).trans (Nat.le_succ _)
  unfold modulusList
  dsimp only
  set p := firstPList Q Λ L₁ L₂ L₃
  set q := secondPList Q Λ L₁ L₂ L₃ p
  have hp : p.size ≤ listMax Nat.size Q + 1 := hbound ..
  have hq : q.size ≤ listMax Nat.size Q + 1 := hbound ..
  have hmul := Nat.size_mul_le p q
  omega

theorem firstPList_eq_firstP {Q : List ℕ} (hQ : List.Pairwise (· < ·) Q) (Λ : ℕ)
    {L₁ L₂ L₃ : List ℤ} (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup) :
    firstPList Q Λ L₁ L₂ L₃ = firstP Q.toFinset Λ L₁.toFinset L₂.toFinset L₃.toFinset := by
  let ctx : SearchCtx :=
    (((Q.length, 1), ((3 * Λ * L₁.length ^ 2, 3 * Λ * L₂.length ^ 2), 3 * Λ * L₃.length ^ 2)),
      (L₁, (L₂, L₃)))
  unfold firstPList searchPrimeList
  rw [iterate_searchPrimeStep Q ctx Q.length le_rfl, List.take_length]
  dsimp only
  rw [foldl_findFirst_eq_minOrOne hQ, firstP]
  congr 1
  ext p
  simp only [ctxPred, ctx, one_mul, searchPrimePred, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_filter,
    collList_eq_coll p h₁, collList_eq_coll p h₂, collList_eq_coll p h₃,
    List.toFinset_card_of_nodup (hQ.imp ne_of_lt),
    List.toFinset_card_of_nodup h₁, List.toFinset_card_of_nodup h₂,
    List.toFinset_card_of_nodup h₃]

theorem secondPList_eq_secondP {Q : List ℕ} (hQ : List.Pairwise (· < ·) Q) (Λ : ℕ)
    {L₁ L₂ L₃ : List ℤ} (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup) (p : ℕ) :
    secondPList Q Λ L₁ L₂ L₃ p =
      secondP Q.toFinset Λ L₁.toFinset L₂.toFinset L₃.toFinset p := by
  let ctx : SearchCtx :=
    (((Q.length, p), ((3 * Λ * collList p L₁, 3 * Λ * collList p L₂), 3 * Λ * collList p L₃)),
      (L₁, (L₂, L₃)))
  unfold secondPList searchPrimeList
  rw [iterate_searchPrimeStep Q ctx Q.length le_rfl, List.take_length]
  dsimp only
  rw [foldl_findFirst_eq_minOrOne hQ, secondP]
  congr 1
  ext q
  simp only [ctxPred, ctx, searchPrimePred, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter,
    collList_eq_coll (p * q) h₁, collList_eq_coll (p * q) h₂, collList_eq_coll (p * q) h₃,
    collList_eq_coll p h₁, collList_eq_coll p h₂, collList_eq_coll p h₃,
    List.toFinset_card_of_nodup (hQ.imp ne_of_lt)]

/-- For strictly increasing `Q` and duplicate-free `L₁, L₂, L₃`, `modulusList` equals
`ChanHe.modulus`. -/
theorem modulusList_eq_modulus {Q : List ℕ} (hQ : List.Pairwise (· < ·) Q) (Λ : ℕ)
    {L₁ L₂ L₃ : List ℤ} (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) (h₃ : L₃.Nodup) :
    modulusList Q Λ L₁ L₂ L₃ = modulus Q.toFinset Λ L₁.toFinset L₂.toFinset L₃.toFinset := by
  unfold modulusList modulus
  dsimp only
  rw [firstPList_eq_firstP hQ Λ h₁ h₂ h₃, secondPList_eq_secondP hQ Λ h₁ h₂ h₃]

/-- Input tuple `(Q, (Λ, (L₁, (L₂, L₃))))` for `modulusList`. -/
abbrev ModInput := List ℕ × (ℕ × IntTriple)

/-- Encoding of `ModInput`. -/
@[expose] def encModInput : ModInput ↪ List Bool :=
  encPair (encList encNat) (encPair encNat encIntTriple)

/-- Total element count `|Q| + |L₁| + |L₂| + |L₃| + 1` of `x : ModInput`. -/
def modLen (x : ModInput) : ℕ :=
  x.1.length + x.2.2.1.length + x.2.2.2.1.length + x.2.2.2.2.length + 1

/-- Bit-scale parameter for `modulusList` on `x : ModInput`. -/
def modScale (x : ModInput) : ℕ :=
  listMax Nat.size x.1 + x.1.length.size + x.2.1.size +
    listMax (fun z => (encIntBin z).length) x.2.2.1 +
    listMax (fun z => (encIntBin z).length) x.2.2.2.1 +
    listMax (fun z => (encIntBin z).length) x.2.2.2.2 + (modLen x).size + 8

theorem modLen_le {x : ModInput} {b : ℕ}
    (h : x.1.length + x.2.2.1.length + x.2.2.2.1.length + x.2.2.2.2.length + 1 ≤ b) :
    modLen x ≤ b := h

theorem modScale_le {x : ModInput} {bQ bQl bLam b1 b2 b3 bM : ℕ}
    (hQ : listMax Nat.size x.1 ≤ bQ) (hQl : x.1.length.size ≤ bQl) (hLam : x.2.1.size ≤ bLam)
    (h1 : listMax (fun z => (encIntBin z).length) x.2.2.1 ≤ b1)
    (h2 : listMax (fun z => (encIntBin z).length) x.2.2.2.1 ≤ b2)
    (h3 : listMax (fun z => (encIntBin z).length) x.2.2.2.2 ≤ b3)
    (hM : (modLen x).size ≤ bM) :
    modScale x ≤ bQ + bQl + bLam + b1 + b2 + b3 + bM + 8 := by
  dsimp only [modScale]; omega

private abbrev SearchState := Option ℕ × (List ℕ × SearchCtx)

private def encSearchState : SearchState ↪ List Bool :=
  encPair (encOption encNat) (encPair (encList encNat) encSearchCtx)

private def stLen (st : SearchState) : ℕ :=
  st.2.1.length + st.2.2.2.1.length + st.2.2.2.2.1.length + st.2.2.2.2.2.length + 1

private def stScale (st : SearchState) : ℕ :=
  (encOption encNat st.1).length + listMax Nat.size st.2.1 +
    (encSearchParams st.2.2.1).length +
    listMax (fun z => (encIntBin z).length) st.2.2.2.1 +
    listMax (fun z => (encIntBin z).length) st.2.2.2.2.1 +
    listMax (fun z => (encIntBin z).length) st.2.2.2.2.2 + (stLen st).size + 8

private theorem length_encSearchState_le (st : SearchState) :
    (encSearchState st).length ≤ 16 * (stLen st * stScale st) := by
  simp only [encSearchState, encSearchCtx, encIntTriple, length_encPair]
  have hQ := length_encList_le_mul encNat st.2.1 (b := listMax Nat.size st.2.1)
    fun r hr => by rw [length_encNat]; exact le_listMax hr
  have h1 := length_encList_le_mul encIntBin st.2.2.2.1
    (b := listMax (fun z => (encIntBin z).length) st.2.2.2.1)
    fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
  have h2 := length_encList_le_mul encIntBin st.2.2.2.2.1
    (b := listMax (fun z => (encIntBin z).length) st.2.2.2.2.1)
    fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
  have h3 := length_encList_le_mul encIntBin st.2.2.2.2.2
    (b := listMax (fun z => (encIntBin z).length) st.2.2.2.2.2)
    fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
  set L := stLen st
  set S := stScale st
  have hbQ : 2 * listMax Nat.size st.2.1 + 1 ≤ 2 * S := by dsimp only [S, stScale]; omega
  have hb1 : 2 * listMax (fun z => (encIntBin z).length) st.2.2.2.1 + 1 ≤ 2 * S := by
    dsimp only [S, stScale]; omega
  have hb2 : 2 * listMax (fun z => (encIntBin z).length) st.2.2.2.2.1 + 1 ≤ 2 * S := by
    dsimp only [S, stScale]; omega
  have hb3 : 2 * listMax (fun z => (encIntBin z).length) st.2.2.2.2.2 + 1 ≤ 2 * S := by
    dsimp only [S, stScale]; omega
  have hQ' := hQ.trans (Nat.mul_le_mul_left _ hbQ)
  have h1' := h1.trans (Nat.mul_le_mul_left _ hb1)
  have h2' := h2.trans (Nat.mul_le_mul_left _ hb2)
  have h3' := h3.trans (Nat.mul_le_mul_left _ hb3)
  have hL : st.2.1.length + st.2.2.2.1.length + st.2.2.2.2.1.length +
      st.2.2.2.2.2.length + 1 = L := rfl
  have hSp : (encOption encNat st.1).length + (encSearchParams st.2.2.1).length + 4 ≤ S := by
    dsimp only [S, stScale]; omega
  nlinarith

private theorem computableInPolyTime_mulNat :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat := by fun_prop

private theorem computableInPolyTime_leProd :
    ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => decide (p.1 * p.2.1 ≤ p.2.2))
      (encPair encNat (encPair encNat encNat)) encBool := by fun_prop

private theorem computableInPolyTime_someIf :
    ComputableInPolyTime (fun p : Bool × ℕ => if p.1 then some p.2 else none)
      (encPair encBool encNat) (encOption encNat) := by fun_prop

private theorem computableInO_searchPrimeStep :
    ∃ d, ComputableInO searchPrimeStep encSearchState encSearchState
      (fun st => stLen st * stScale st ^ d)
      (fun st => stLen st * stScale st ^ d) := by
  obtain ⟨dc, hcoll⟩ := computableInO_collList
  have hAcc := ComputableInO.fst (encOption encNat) (encPair (encList encNat) encSearchCtx)
  have hRest := ComputableInO.snd (encOption encNat) (encPair (encList encNat) encSearchCtx)
  have hQs : ComputableInO (fun st : SearchState => st.2.1) encSearchState (encList encNat)
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.fst (encList encNat) encSearchCtx).comp_linear hRest).mono_le
      (fun st => by simp only [encSearchState, length_encPair]; omega)
      (fun st => by simp only [encSearchState, length_encPair]; omega)
  have hCtx : ComputableInO (fun st : SearchState => st.2.2) encSearchState encSearchCtx
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.snd (encList encNat) encSearchCtx).comp_linear hRest).mono_le
      (fun st => by simp only [encSearchState, length_encPair]; omega)
      (fun st => by simp only [encSearchState, length_encPair]; omega)
  have hParams : ComputableInO (fun st : SearchState => st.2.2.1) encSearchState encSearchParams
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.fst encSearchParams encIntTriple).comp_linear hCtx).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hTriple : ComputableInO (fun st : SearchState => st.2.2.2) encSearchState encIntTriple
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.snd encSearchParams encIntTriple).comp_linear hCtx).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL1 : ComputableInO (fun st : SearchState => st.2.2.2.1) encSearchState (encList encIntBin)
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.fst (encList encIntBin)
      (encPair (encList encIntBin) (encList encIntBin))).comp_linear hTriple).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL23 : ComputableInO (fun st : SearchState => st.2.2.2.2) encSearchState
      (encPair (encList encIntBin) (encList encIntBin))
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.snd (encList encIntBin)
      (encPair (encList encIntBin) (encList encIntBin))).comp_linear hTriple).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL2 : ComputableInO (fun st : SearchState => st.2.2.2.2.1) encSearchState (encList encIntBin)
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.fst (encList encIntBin) (encList encIntBin)).comp_linear hL23).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL3 : ComputableInO (fun st : SearchState => st.2.2.2.2.2) encSearchState (encList encIntBin)
      (fun st => (encSearchState st).length) (fun st => (encSearchState st).length) :=
    ((ComputableInO.snd (encList encIntBin) (encList encIntBin)).comp_linear hL23).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hOne : ComputableInO (fun _ : SearchState => (1 : ℕ)) encSearchState encUnary
      (fun st => (encSearchState st).length) (fun _ => 0) := ComputableInO.constZero 1
  have hTail : ComputableInO (fun st : SearchState => (st.2.1.drop 1, st.2.2)) encSearchState
      (encPair (encList encNat) encSearchCtx)
      (fun st => stLen st * stScale st) (fun st => stLen st * stScale st) := by
    refine ((hQs.drop' hOne).prod hCtx).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 128 0 fun st => ?_
      have hst := length_encSearchState_le st
      have hq_le : (encList encNat st.2.1).length ≤ (encSearchState st).length := by
        simp only [encSearchState, length_encPair]; omega
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      have hpos : 1 ≤ stLen st * stScale st :=
        Nat.mul_pos (by dsimp only [stLen]; omega) (by dsimp only [stScale]; omega)
      omega
  have hSkip : ComputableInO (fun st : SearchState => (st.1, (st.2.1.drop 1, st.2.2)))
      encSearchState encSearchState
      (fun st => stLen st * stScale st) (fun st => stLen st * stScale st) := by
    refine (hAcc.prod hTail).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 32 0 fun st => ?_
      have hst := length_encSearchState_le st
      dsimp only [encSearchState] at hst
      omega
  have hCond : ComputableInO
      (fun st : SearchState => decide ((st.1.isSome || st.2.1.isEmpty) = true))
      encSearchState encBool
      (fun st => stLen st * stScale st) (fun st => stLen st * stScale st) := by
    refine (((hAcc.optionIsNone.not').or' hQs.isEmpty').of_enc_eq
      (g := fun st : SearchState => decide ((st.1.isSome || st.2.1.isEmpty) = true))
      fun st => by rcases st with ⟨_ | _, _ | _, _⟩ <;> rfl).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 64 0 fun st => ?_
      have hst := length_encSearchState_le st
      have hq_le : (encList encNat st.2.1).length ≤ (encSearchState st).length := by
        simp only [encSearchState, length_encPair]; omega
      dsimp only [encSearchState] at hst hq_le ⊢
      omega
  have hHead := (ComputableInO.headD' (enc := encNat) 0).comp_linear hQs
  have hPar1 := (ComputableInO.fst (encPair encNat encNat)
    (encPair (encPair encNat encNat) encNat)).comp_linear hParams
  have hPar2 := (ComputableInO.snd (encPair encNat encNat)
    (encPair (encPair encNat encNat) encNat)).comp_linear hParams
  have hQLen := (ComputableInO.fst encNat encNat).comp_linear hPar1
  have hMul0 := (ComputableInO.snd encNat encNat).comp_linear hPar1
  have hB12 := (ComputableInO.fst (encPair encNat encNat) encNat).comp_linear hPar2
  have hB1 := (ComputableInO.fst encNat encNat).comp_linear hB12
  have hB2 := (ComputableInO.snd encNat encNat).comp_linear hB12
  have hB3 := (ComputableInO.snd (encPair encNat encNat) encNat).comp_linear hPar2
  obtain ⟨dm, _, hMulDeg⟩ := computableInPolyTime_mulNat.exists_degree
  have hM : ComputableInO (fun st : SearchState => st.2.2.1.1.2 * st.2.1.headD 0)
      encSearchState encNat
      (fun st => stLen st * stScale st ^ (dm + 1))
      (fun st => stLen st * stScale st ^ (dm + 1)) := by
    refine (hMulDeg.inO.comp (hMul0.prod hHead)).weaken ?_ ?_
    all_goals
      refine BigOLe.add ?_ ?_
      · refine BigOLe.of_le_linear 32 0 fun st => ?_
        have hS : stScale st ≤ stScale st ^ (dm + 1) := Nat.le_self_pow (by omega) _
        have hst := length_encSearchState_le st
        nlinarith [Nat.mul_le_mul_left (stLen st) hS]
      · refine BigOLe.of_le_linear (4 ^ dm) 0 fun st => ?_
        have hhd : (st.2.1.headD 0).size ≤ listMax Nat.size st.2.1 := by
          cases st.2.1 with
          | nil => simp
          | cons q qs => simp [le_listMax (List.mem_cons_self ..)]
        have hm0 : st.2.2.1.1.2.size ≤ (encSearchParams st.2.2.1).length := by
          simp only [encSearchParams, length_encPair, length_encNat]; omega
        have hlenP : 2 * st.2.2.1.1.2.size + 1 + (st.2.1.headD 0).size + 1 ≤
            4 * stScale st := by dsimp only [stScale]; omega
        have hpow : (2 * st.2.2.1.1.2.size + 1 + (st.2.1.headD 0).size + 1) ^ dm ≤
            4 ^ dm * (stLen st * stScale st ^ (dm + 1)) :=
          calc _ ≤ (4 * stScale st) ^ dm := Nat.pow_le_pow_left hlenP dm
            _ = 4 ^ dm * stScale st ^ dm := Nat.mul_pow 4 _ dm
            _ ≤ 4 ^ dm * stScale st ^ (dm + 1) := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right (by dsimp only [stScale]; omega) (Nat.le_succ dm))
            _ ≤ 4 ^ dm * (stLen st * stScale st ^ (dm + 1)) := Nat.mul_le_mul_left _
                (Nat.le_mul_of_pos_left _ (by dsimp only [stLen]; omega))
        change ((encPair encNat encNat (st.2.2.1.1.2, st.2.1.headD 0)).length + 1) ^ dm ≤ _
        rw [length_encPair, length_encNat, length_encNat]
        exact hpow.trans_eq (add_zero _).symm
  let D₁ := dm + dc + 2
  have hM_sz (st : SearchState) :
      (st.2.2.1.1.2 * st.2.1.headD 0).size ≤ 2 * stScale st := by
    have hmul_sz := Nat.size_mul_le st.2.2.1.1.2 (st.2.1.headD 0)
    have h1 : st.2.2.1.1.2.size ≤ (encSearchParams st.2.2.1).length := by
      simp only [encSearchParams, length_encPair, length_encNat]; omega
    have h2 : (st.2.1.headD 0).size ≤ listMax Nat.size st.2.1 := by
      cases st.2.1 with
      | nil => simp
      | cons q qs => simp [le_listMax (List.mem_cons_self ..)]
    dsimp only [stScale]; omega
  have mkColl : ∀ (fL : SearchState → List ℤ)
      (hfL : ComputableInO fL encSearchState (encList encIntBin)
        (fun st => (encSearchState st).length) (fun st => (encSearchState st).length))
      (hlenL : ∀ st, (fL st).length + 1 ≤ stLen st)
      (hmaxL : ∀ st, listMax (fun z => (encIntBin z).length) (fL st) ≤ stScale st),
      ComputableInO (fun st : SearchState => collList (st.2.2.1.1.2 * st.2.1.headD 0) (fL st))
        encSearchState encNat
        (fun st => stLen st * stScale st ^ D₁)
        (fun st => stLen st * stScale st ^ D₁) := by
    intro fL hfL hlenL hmaxL
    refine (hcoll.comp (hM.prod hfL)).weaken ?_ ?_
    all_goals
      refine BigOLe.add (BigOLe.add ?_ ?_) ?_
      · exact BigOLe.of_le fun st => Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by dsimp only [stScale]; omega) (by dsimp only [D₁]; omega))
      · refine BigOLe.of_le_linear 16 0 fun st => ?_
        have hS : stScale st ≤ stScale st ^ D₁ :=
          Nat.le_self_pow (by dsimp only [D₁]; omega) _
        have := length_encSearchState_le st
        nlinarith [Nat.mul_le_mul_left (stLen st) hS]
      · refine BigOLe.of_le_linear (4 ^ dc) 0 fun st => ?_
        have hcs : collScale (st.2.2.1.1.2 * st.2.1.headD 0, fL st) ≤ 4 * stScale st := by
          have hlsz : (fL st).length.size ≤ (stLen st).size :=
            Nat.size_le_size ((Nat.le_succ _).trans (hlenL st))
          have hc0 := collScale_le (p := (st.2.2.1.1.2 * st.2.1.headD 0, fL st))
            (hM_sz st) (hmaxL st) hlsz
          have hst_ge : (stLen st).size + 1 ≤ stScale st := by dsimp only [stScale]; omega
          omega
        have hpow : collScale (st.2.2.1.1.2 * st.2.1.headD 0, fL st) ^ dc ≤
            4 ^ dc * stScale st ^ D₁ :=
          calc _ ≤ (4 * stScale st) ^ dc := Nat.pow_le_pow_left hcs dc
            _ = 4 ^ dc * stScale st ^ dc := Nat.mul_pow 4 _ dc
            _ ≤ 4 ^ dc * stScale st ^ D₁ := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right (by dsimp only [stScale]; omega) (by dsimp only [D₁]; omega))
        have hmul : ((fL st).length + 1) *
            collScale (st.2.2.1.1.2 * st.2.1.headD 0, fL st) ^ dc ≤
            4 ^ dc * (stLen st * stScale st ^ D₁) :=
          (Nat.mul_le_mul (hlenL st) hpow).trans_eq (Nat.mul_left_comm _ _ _)
        exact hmul.trans_eq (add_zero _).symm
  have hc1 := mkColl _ hL1 (fun st => by dsimp only [stLen]; omega)
    (fun st => by dsimp only [stScale]; omega)
  have hc2 := mkColl _ hL2 (fun st => by dsimp only [stLen]; omega)
    (fun st => by dsimp only [stScale]; omega)
  have hc3 := mkColl _ hL3 (fun st => by dsimp only [stLen]; omega)
    (fun st => by dsimp only [stScale]; omega)
  obtain ⟨dle, _, hLeDeg⟩ := computableInPolyTime_leProd.exists_degree
  obtain ⟨dsm, _, hSomeDeg⟩ := computableInPolyTime_someIf.exists_degree
  let D₂ := D₁ + dle + 2
  have mkOk : ∀ (fc fB : SearchState → ℕ)
      (hfc : ComputableInO fc encSearchState encNat
        (fun st => stLen st * stScale st ^ D₁) (fun st => stLen st * stScale st ^ D₁))
      (hfB : ComputableInO fB encSearchState encNat
        (fun st => (encSearchState st).length) (fun st => (encSearchState st).length))
      (hcsz : ∀ st, (fc st).size ≤ 2 * (stLen st).size + 1)
      (hBsz : ∀ st, (fB st).size ≤ (encSearchParams st.2.2.1).length),
      ComputableInO (fun st : SearchState => decide (fc st * st.2.2.1.1.1 ≤ fB st))
        encSearchState encBool
        (fun st => stLen st * stScale st ^ D₂)
        (fun st => stLen st * stScale st ^ D₂) := by
    intro fc fB hfc hfB hcsz hBsz
    refine (hLeDeg.inO.comp (hfc.prod (hQLen.prod hfB))).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (36 + 16 ^ dle) 0 fun st => ?_
      have hS1 : 1 ≤ stScale st := by dsimp only [stScale]; omega
      have hSD : stScale st ≤ stScale st ^ D₂ := Nat.le_self_pow (by dsimp only [D₂]; omega) _
      have hst : (encSearchState st).length ≤ 16 * (stLen st * stScale st ^ D₂) :=
        (length_encSearchState_le st).trans (by nlinarith [Nat.mul_le_mul_left (stLen st) hSD])
      have hsub := Nat.mul_le_mul_left (stLen st)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D₂]; omega : D₁ ≤ D₂))
      have hqs : st.2.2.1.1.1.size ≤ (encSearchParams st.2.2.1).length := by
        simp only [encSearchParams, length_encPair, length_encNat]; omega
      have hbase : (encPair encNat (encPair encNat encNat)
          (fc st, (st.2.2.1.1.1, fB st))).length + 1 ≤ 16 * stScale st := by
        simp only [length_encPair, length_encNat]
        have := hcsz st
        have := hBsz st
        dsimp only [stScale]; omega
      have hpow : ((encPair encNat (encPair encNat encNat)
          (fc st, (st.2.2.1.1.1, fB st))).length + 1) ^ dle ≤
          16 ^ dle * (stLen st * stScale st ^ D₂) :=
        calc _ ≤ (16 * stScale st) ^ dle := Nat.pow_le_pow_left hbase dle
          _ = 16 ^ dle * stScale st ^ dle := Nat.mul_pow 16 _ dle
          _ ≤ 16 ^ dle * stScale st ^ D₂ := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D₂]; omega))
          _ ≤ 16 ^ dle * (stLen st * stScale st ^ D₂) := Nat.mul_le_mul_left _
              (Nat.le_mul_of_pos_left _ (by dsimp only [stLen]; omega))
      change stLen st * stScale st ^ D₁ +
          ((encSearchState st).length + (encSearchState st).length) +
          ((encPair encNat (encPair encNat encNat) (fc st, (st.2.2.1.1.1, fB st))).length +
            1) ^ dle ≤
        (36 + 16 ^ dle) * (stLen st * stScale st ^ D₂) + 0
      rw [Nat.add_mul 36 (16 ^ dle)]
      omega
  have hc_sz : ∀ (st : SearchState) (L : List ℤ), L.length ≤ stLen st →
      (collList (st.2.2.1.1.2 * st.2.1.headD 0) L).size ≤ 2 * (stLen st).size + 1 :=
    fun st L hL => (Nat.size_le_size ((collList_le_sq _ L).trans
      (Nat.pow_le_pow_left hL 2))).trans (Nat.size_pow_le _ 2)
  have hok1 := mkOk _ _ hc1 hB1 (fun st => hc_sz st _ (by dsimp only [stLen]; omega))
    (fun st => by
      dsimp only [Function.comp_apply]
      simp only [encSearchParams, length_encPair, length_encNat]; omega)
  have hok2 := mkOk _ _ hc2 hB2 (fun st => hc_sz st _ (by dsimp only [stLen]; omega))
    (fun st => by
      dsimp only [Function.comp_apply]
      simp only [encSearchParams, length_encPair, length_encNat]; omega)
  have hok3 := mkOk _ _ hc3 hB3 (fun st => hc_sz st _ (by dsimp only [stLen]; omega))
    (fun st => by
      dsimp only [Function.comp_apply]
      simp only [encSearchParams, length_encPair, length_encNat]; omega)
  let okFn (st : SearchState) : Bool :=
    searchPrimePred st.2.2.1.1.1 st.2.2.1.2.1.1 st.2.2.1.2.1.2 st.2.2.1.2.2
      (collList (st.2.2.1.1.2 * st.2.1.headD 0) st.2.2.2.1)
      (collList (st.2.2.1.1.2 * st.2.1.headD 0) st.2.2.2.2.1)
      (collList (st.2.2.1.1.2 * st.2.1.headD 0) st.2.2.2.2.2)
  have hOk : ComputableInO okFn encSearchState encBool
      (fun st => stLen st * stScale st ^ D₂) (fun st => stLen st * stScale st ^ D₂) :=
    ((hok1.and' (hok2.and' hok3)).of_enc_eq (g := okFn) fun _ => rfl).mono 4
      (fun _ => by omega) (fun _ => by omega)
  let D := D₂ + dsm + 2
  have hNewAcc : ComputableInO
      (fun st : SearchState => if okFn st then some (st.2.1.headD 0) else none)
      encSearchState (encOption encNat)
      (fun st => stLen st * stScale st ^ D) (fun st => stLen st * stScale st ^ D) := by
    refine (hSomeDeg.inO.comp (hOk.prod hHead)).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (20 + 8 ^ dsm) 0 fun st => ?_
      have hS1 : 1 ≤ stScale st := by dsimp only [stScale]; omega
      have hSD : stScale st ≤ stScale st ^ D := Nat.le_self_pow (by dsimp only [D]; omega) _
      have hst : (encSearchState st).length ≤ 16 * (stLen st * stScale st ^ D) :=
        (length_encSearchState_le st).trans (by nlinarith [Nat.mul_le_mul_left (stLen st) hSD])
      have hsub := Nat.mul_le_mul_left (stLen st)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : D₂ ≤ D))
      have hhd : (st.2.1.headD 0).size ≤ listMax Nat.size st.2.1 := by
        cases st.2.1 with
        | nil => simp
        | cons q qs => simp [le_listMax (List.mem_cons_self ..)]
      have hblen : ∀ b : Bool, (encBool b).length = 1 := by rintro (_ | _) <;> rfl
      have hbase : (encPair encBool encNat (okFn st, st.2.1.headD 0)).length + 1 ≤
          8 * stScale st := by
        rw [length_encPair, hblen, length_encNat]; dsimp only [stScale]; omega
      have hpow : ((encPair encBool encNat (okFn st, st.2.1.headD 0)).length + 1) ^ dsm ≤
          8 ^ dsm * (stLen st * stScale st ^ D) :=
        calc _ ≤ (8 * stScale st) ^ dsm := Nat.pow_le_pow_left hbase dsm
          _ = 8 ^ dsm * stScale st ^ dsm := Nat.mul_pow 8 _ dsm
          _ ≤ 8 ^ dsm * stScale st ^ D := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega))
          _ ≤ 8 ^ dsm * (stLen st * stScale st ^ D) := Nat.mul_le_mul_left _
              (Nat.le_mul_of_pos_left _ (by dsimp only [stLen]; omega))
      dsimp only [Function.comp_apply]
      rw [Nat.add_mul 20 (8 ^ dsm)]
      omega
  have hFull := (hCond.iteDecide hSkip (hNewAcc.prod hTail)).of_enc_eq (g := searchPrimeStep)
    fun st => congrArg encSearchState (by
      unfold searchPrimeStep
      rcases st with ⟨_ | r, _ | ⟨q, qs⟩, ctx⟩ <;> rfl)
  refine ⟨D, hFull.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear 8 0 fun st => ?_
    have hS : stScale st ≤ stScale st ^ D := Nat.le_self_pow (by dsimp only [D]; omega) _
    have hsub := Nat.mul_le_mul_left (stLen st) hS
    split_ifs <;> omega

/-- Generic `ComputableInO` bound for `searchPrimeList` parameterized by scalar inputs. -/
theorem computableInO_searchPrimeList :
    ∃ d, ComputableInO
      (fun p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple) =>
        searchPrimeList p.1 p.2.1.1 p.2.1.2.1.1 p.2.1.2.1.2 p.2.1.2.2
          p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair (encList encNat)
        (encPair (encPair encNat (encPair (encPair encNat encNat) encNat)) encIntTriple))
      encNat
      (fun p => (p.1.length + 1) *
        (p.1.length + p.2.2.1.length + p.2.2.2.1.length + p.2.2.2.2.length + 1) *
        (listMax Nat.size p.1 + p.1.length.size +
          (encPair encNat (encPair (encPair encNat encNat) encNat) p.2.1).length +
          listMax (fun z => (encIntBin z).length) p.2.2.1 +
          listMax (fun z => (encIntBin z).length) p.2.2.2.1 +
          listMax (fun z => (encIntBin z).length) p.2.2.2.2 +
          (p.1.length + p.2.2.1.length + p.2.2.2.1.length + p.2.2.2.2.length + 1).size + 16) ^ d)
      (fun p =>
        (p.1.length + p.2.2.1.length + p.2.2.2.1.length + p.2.2.2.2.length + 1) *
        (listMax Nat.size p.1 + p.1.length.size +
          (encPair encNat (encPair (encPair encNat encNat) encNat) p.2.1).length +
          listMax (fun z => (encIntBin z).length) p.2.2.1 +
          listMax (fun z => (encIntBin z).length) p.2.2.2.1 +
          listMax (fun z => (encIntBin z).length) p.2.2.2.2 +
          (p.1.length + p.2.2.1.length + p.2.2.2.1.length + p.2.2.2.2.length + 1).size +
            16) ^ d) := by
  let encScal := encPair encNat (encPair (encPair encNat encNat) encNat)
  let encIn := encPair (encList encNat) (encPair encScal encIntTriple)
  let pLen (p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple)) : ℕ :=
    p.1.length + p.2.2.1.length + p.2.2.2.1.length + p.2.2.2.2.length + 1
  let pScale (p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple)) : ℕ :=
    listMax Nat.size p.1 + p.1.length.size + (encScal p.2.1).length +
      listMax (fun z => (encIntBin z).length) p.2.2.1 +
      listMax (fun z => (encIntBin z).length) p.2.2.2.1 +
      listMax (fun z => (encIntBin z).length) p.2.2.2.2 + (pLen p).size + 16
  obtain ⟨dl, hlenQ⟩ := computableInO_listLengthNat encNat
  obtain ⟨ds, hstep⟩ := computableInO_searchPrimeStep
  have hlenIn_le (p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple)) :
      (encIn p).length ≤ 16 * (pLen p * pScale p) := by
    simp only [encIn, encIntTriple, length_encPair]
    have hQ_l := length_encList_le_mul encNat p.1 (b := listMax Nat.size p.1)
      fun r hr => by rw [length_encNat]; exact le_listMax hr
    have h1 := length_encList_le_mul encIntBin p.2.2.1
      (b := listMax (fun z => (encIntBin z).length) p.2.2.1)
      fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
    have h2 := length_encList_le_mul encIntBin p.2.2.2.1
      (b := listMax (fun z => (encIntBin z).length) p.2.2.2.1)
      fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
    have h3 := length_encList_le_mul encIntBin p.2.2.2.2
      (b := listMax (fun z => (encIntBin z).length) p.2.2.2.2)
      fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
    have hbQ : 2 * listMax Nat.size p.1 + 1 ≤ 2 * pScale p := by dsimp only [pScale]; omega
    have hb1 : 2 * listMax (fun z => (encIntBin z).length) p.2.2.1 + 1 ≤ 2 * pScale p := by
      dsimp only [pScale]; omega
    have hb2 : 2 * listMax (fun z => (encIntBin z).length) p.2.2.2.1 + 1 ≤ 2 * pScale p := by
      dsimp only [pScale]; omega
    have hb3 : 2 * listMax (fun z => (encIntBin z).length) p.2.2.2.2 + 1 ≤ 2 * pScale p := by
      dsimp only [pScale]; omega
    have hQ' := hQ_l.trans (Nat.mul_le_mul_left _ hbQ)
    have h1' := h1.trans (Nat.mul_le_mul_left _ hb1)
    have h2' := h2.trans (Nat.mul_le_mul_left _ hb2)
    have h3' := h3.trans (Nat.mul_le_mul_left _ hb3)
    have hSc : (encScal p.2.1).length + 4 ≤ pScale p := by dsimp only [pScale]; omega
    have hPl : p.1.length + p.2.2.1.length + p.2.2.2.1.length + p.2.2.2.2.length + 1 =
        pLen p := rfl
    nlinarith
  have hQ := ComputableInO.fst (encList encNat) (encPair encScal encIntTriple)
  have hR := ComputableInO.snd (encList encNat) (encPair encScal encIntTriple)
  have hScal : ComputableInO (fun p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple) => p.2.1)
      encIn encScal (fun p => (encIn p).length) (fun p => (encIn p).length) :=
    ((ComputableInO.fst encScal encIntTriple).comp_linear hR).mono_le
      (fun p => by simp only [encIn, length_encPair]; omega)
      (fun p => by simp only [encIn, length_encPair]; omega)
  have hTri : ComputableInO (fun p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple) => p.2.2)
      encIn encIntTriple (fun p => (encIn p).length) (fun p => (encIn p).length) :=
    ((ComputableInO.snd encScal encIntTriple).comp_linear hR).mono_le
      (fun p => by simp only [encIn, length_encPair]; omega)
      (fun p => by simp only [encIn, length_encPair]; omega)
  have hn : ComputableInO (fun p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple) => p.1.length)
      encIn encNat
      (fun p => pLen p * pScale p ^ (dl + 1))
      (fun p => pLen p * pScale p ^ (dl + 1)) := by
    refine (hlenQ.comp hQ).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (32 + 4 ^ dl) 0 fun p => ?_
      have hin := hlenIn_le p
      have hS1 : pScale p ≤ pScale p ^ (dl + 1) := Nat.le_self_pow (by omega) _
      have hin' : (encIn p).length ≤ 16 * (pLen p * pScale p ^ (dl + 1)) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (pLen p) hS1])
      have hp1 : (encList encNat p.1).length ≤ (encIn p).length := by
        simp only [encIn, length_encPair]; omega
      have hlm : listMax (fun a => (encNat a).length) p.1 ≤ listMax Nat.size p.1 :=
        listMax_le fun r hr => by rw [length_encNat]; exact le_listMax hr
      have hb : listMax (fun a => (encNat a).length) p.1 + p.1.length.size + 4 ≤ 4 * pScale p := by
        dsimp only [pScale]; omega
      have hpow : (listMax (fun a => (encNat a).length) p.1 + p.1.length.size + 4) ^ dl ≤
          4 ^ dl * pScale p ^ (dl + 1) :=
        calc _ ≤ (4 * pScale p) ^ dl := Nat.pow_le_pow_left hb dl
          _ = 4 ^ dl * pScale p ^ dl := Nat.mul_pow 4 _ dl
          _ ≤ 4 ^ dl * pScale p ^ (dl + 1) := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right (by dsimp only [pScale]; omega) (Nat.le_succ dl))
      have hmul : (p.1.length + 1) *
          (listMax (fun a => (encNat a).length) p.1 + p.1.length.size + 4) ^ dl ≤
          4 ^ dl * (pLen p * pScale p ^ (dl + 1)) :=
        (Nat.mul_le_mul (show p.1.length + 1 ≤ pLen p by dsimp only [pLen]; omega) hpow).trans_eq
          (Nat.mul_left_comm _ _ _)
      have hsp := hpow.trans (Nat.mul_le_mul_left _
        (Nat.le_mul_of_pos_left _ (show 0 < pLen p by dsimp only [pLen]; omega)))
      dsimp only [Function.comp_apply, encIn] at hp1 hin' ⊢
      rw [Nat.add_mul 32 (4 ^ dl)]
      omega
  have hReassocPt : ComputableInPolyTime
      (fun q : ℕ × (ℕ × ((ℕ × ℕ) × ℕ)) => ((q.1, q.2.1), q.2.2))
      (encPair encNat encScal) encSearchParams := by fun_prop
  obtain ⟨dr, _, hReassocDeg⟩ := hReassocPt.exists_degree
  let D₀ := dl + dr + 2
  have hParams : ComputableInO
      (fun p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple) =>
        ((p.1.length, p.2.1.1), p.2.1.2))
      encIn encSearchParams
      (fun p => pLen p * pScale p ^ D₀)
      (fun p => pLen p * pScale p ^ D₀) := by
    refine (hReassocDeg.inO.comp (hn.prod hScal)).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (32 + 4 ^ dr) 0 fun p => ?_
      have hin := hlenIn_le p
      have hS1 : pScale p ≤ pScale p ^ D₀ := Nat.le_self_pow (by dsimp only [D₀]; omega) _
      have hin' : (encIn p).length ≤ 16 * (pLen p * pScale p ^ D₀) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (pLen p) hS1])
      have hsub : pLen p * pScale p ^ (dl + 1) ≤ pLen p * pScale p ^ D₀ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by dsimp only [pScale]; omega)
          (by dsimp only [D₀]; omega))
      have hb : (encPair encNat encScal (p.1.length, p.2.1)).length + 1 ≤ 4 * pScale p := by
        rw [length_encPair, length_encNat]
        dsimp only [pScale]; omega
      have hpow : ((encPair encNat encScal (p.1.length, p.2.1)).length + 1) ^ dr ≤
          4 ^ dr * (pLen p * pScale p ^ D₀) :=
        calc _ ≤ (4 * pScale p) ^ dr := Nat.pow_le_pow_left hb dr
          _ = 4 ^ dr * pScale p ^ dr := Nat.mul_pow 4 _ dr
          _ ≤ 4 ^ dr * pScale p ^ D₀ := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right (by dsimp only [pScale]; omega) (by dsimp only [D₀]; omega))
          _ ≤ 4 ^ dr * (pLen p * pScale p ^ D₀) := Nat.mul_le_mul_left _
              (Nat.le_mul_of_pos_left _ (by dsimp only [pLen]; omega))
      rw [Nat.add_mul 32 (4 ^ dr)]
      omega
  have hInit : ComputableInO
      (fun p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple) =>
        ((none : Option ℕ), (p.1, (((p.1.length, p.2.1.1), p.2.1.2), p.2.2))))
      encIn encSearchState
      (fun p => pLen p * pScale p ^ D₀)
      (fun p => pLen p * pScale p ^ D₀) := by
    have hNone : ComputableInO (fun _ => (none : Option ℕ)) encIn (encOption encNat)
        (fun p => (encIn p).length) (fun _ => 0) := ComputableInO.constZero none
    refine (hNone.prod (hQ.prod (hParams.prod hTri))).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 64 0 fun p => ?_
      have hin := hlenIn_le p
      have hS1 : pScale p ≤ pScale p ^ D₀ := Nat.le_self_pow (by dsimp only [D₀]; omega) _
      have hin' : (encIn p).length ≤ 16 * (pLen p * pScale p ^ D₀) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (pLen p) hS1])
      have hpQ : (encList encNat p.1).length ≤ (encIn p).length := by
        simp only [encIn, length_encPair]; omega
      dsimp only [encIn] at hpQ hin' ⊢
      omega
  let R (p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple)) : ℕ :=
    pLen p * (6 * pScale p) ^ ds
  let B (p : List ℕ × ((ℕ × ((ℕ × ℕ) × ℕ)) × IntTriple)) : ℕ :=
    96 * (pLen p * pScale p)
  have hst_bounds : ∀ p k, k ≤ p.1.length →
      stLen (searchPrimeStep^[k] (none, (p.1, (((p.1.length, p.2.1.1), p.2.1.2), p.2.2)))) ≤
        pLen p ∧
      stScale (searchPrimeStep^[k] (none, (p.1, (((p.1.length, p.2.1.1), p.2.1.2), p.2.2)))) ≤
        6 * pScale p := by
    intro p k hk
    let ctx : SearchCtx := (((p.1.length, p.2.1.1), p.2.1.2), p.2.2)
    rw [iterate_searchPrimeStep p.1 ctx k hk]
    have hdlen : (p.1.drop k).length ≤ p.1.length := by simp [List.length_drop]
    have hstL : stLen ((p.1.take k).foldl
        (fun acc q => if acc.isSome then acc else if ctxPred ctx q then some q else none) none,
        (p.1.drop k, ctx)) ≤ pLen p := by
      dsimp only [stLen, pLen, ctx]; omega
    refine ⟨hstL, ?_⟩
    have hacc_mem : ∀ (t : List ℕ) (acc : Option ℕ),
        (acc = none ∨ ∃ q ∈ p.1, acc = some q) → (∀ z ∈ t, z ∈ p.1) →
        let r := t.foldl
          (fun a q => if a.isSome then a else if ctxPred ctx q then some q else none) acc
        r = none ∨ ∃ q ∈ p.1, r = some q := by
      intro t
      induction t with
      | nil => intro acc h _; exact h
      | cons z zs ih =>
        intro acc h hz
        dsimp only
        rw [List.foldl_cons]
        have hz1 : z ∈ p.1 := hz z (List.mem_cons_self ..)
        have hzs : ∀ w ∈ zs, w ∈ p.1 := fun w hw => hz w (List.mem_cons_of_mem _ hw)
        rcases acc with _ | r
        · cases ctxPred ctx z
          · exact ih none (Or.inl rfl) hzs
          · exact ih (some z) (Or.inr ⟨z, hz1, rfl⟩) hzs
        · exact ih (some r) h hzs
    have hacc_len : (encOption encNat ((p.1.take k).foldl
        (fun acc q => if acc.isSome then acc else if ctxPred ctx q then some q else none)
          none)).length ≤ listMax Nat.size p.1 + 1 := by
      rcases hacc_mem (p.1.take k) none (Or.inl rfl) (fun _ h => List.mem_of_mem_take h) with
        h0 | ⟨q, hq, hsome⟩
      · rw [h0]; simp
      · rw [hsome, encOption_some, List.length_cons, length_encNat]
        exact Nat.succ_le_succ (le_listMax hq)
    have hdrop_max : listMax Nat.size (p.1.drop k) ≤ listMax Nat.size p.1 :=
      listMax_le fun r hr => le_listMax (List.mem_of_mem_drop hr)
    have hpar_len : (encSearchParams ctx.1).length ≤
        4 * p.1.length.size + 4 * (encScal p.2.1).length + 8 := by
      simp only [ctx, encSearchParams, encScal, length_encPair, length_encNat]
      omega
    have hszL : (stLen ((p.1.take k).foldl
        (fun acc q => if acc.isSome then acc else if ctxPred ctx q then some q else none) none,
        (p.1.drop k, ctx))).size ≤ (pLen p).size := Nat.size_le_size hstL
    have hc2 : ctx.2 = p.2.2 := rfl
    dsimp only [stScale, pScale] at hpar_len hszL ⊢
    rw [hc2]
    omega
  have hround : ∀ p k, k ≤ p.1.length →
      stLen (searchPrimeStep^[k] (none, (p.1, (((p.1.length, p.2.1.1), p.2.1.2), p.2.2)))) *
        stScale (searchPrimeStep^[k] (none, (p.1, (((p.1.length, p.2.1.1), p.2.1.2), p.2.2)))) ^
          ds ≤ R p := fun p k hk => by
    obtain ⟨h1, h2⟩ := hst_bounds p k hk
    exact Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 ds)
  have hstate : ∀ p k, k ≤ p.1.length →
      (encSearchState (searchPrimeStep^[k]
        (none, (p.1, (((p.1.length, p.2.1.1), p.2.1.2), p.2.2))))).length ≤ B p :=
    fun p k hk => by
      obtain ⟨h1, h2⟩ := hst_bounds p k hk
      exact (length_encSearchState_le _).trans (by dsimp only [B]; nlinarith)
  have hiter := ComputableInO.optionGetD 1
    ((ComputableInO.fst (encOption encNat) (encPair (encList encNat) encSearchCtx)).comp_linear
      (ComputableInO.iterate hn hInit hstep hround hround hstate))
  let D := D₀ + ds + 2
  refine ⟨D, (hiter.of_enc_eq (g := fun p =>
      searchPrimeList p.1 p.2.1.1 p.2.1.2.1.1 p.2.1.2.1.2 p.2.1.2.2
        p.2.2.1 p.2.2.2.1 p.2.2.2.2) fun _ => rfl).weaken ?_ ?_⟩
  · refine BigOLe.of_le_linear (128 + 6 ^ ds) 0 fun p => ?_
    have hS1 : 1 ≤ pScale p := by dsimp only [pScale]; omega
    have hpow0 : pScale p ^ D₀ ≤ pScale p ^ D :=
      Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega)
    have hpow_dl : pScale p ^ (dl + 1) ≤ pScale p ^ D :=
      Nat.pow_le_pow_right hS1 (by dsimp only [D, D₀]; omega)
    have hpow_ds : (6 * pScale p) ^ ds ≤ 6 ^ ds * pScale p ^ D :=
      calc (6 * pScale p) ^ ds = 6 ^ ds * pScale p ^ ds := Nat.mul_pow 6 _ ds
        _ ≤ 6 ^ ds * pScale p ^ D := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega))
    have hR : R p ≤ 6 ^ ds * (pLen p * pScale p ^ D) :=
      (Nat.mul_le_mul_left (pLen p) hpow_ds).trans_eq (Nat.mul_left_comm _ _ _)
    have hB : B p ≤ 96 * (pLen p * pScale p ^ D) := by
      have hSD : pScale p ≤ pScale p ^ D := Nat.le_self_pow (by dsimp only [D]; omega) _
      dsimp only [B]; nlinarith [Nat.mul_le_mul_left (pLen p) hSD]
    have hnsz : ((encNat p.1.length).length + 1) ^ 2 ≤ 4 * (pLen p * pScale p ^ D) := by
      rw [length_encNat]
      have hb : p.1.length.size + 1 ≤ 2 * pScale p := by dsimp only [pScale]; omega
      have hsq : (p.1.length.size + 1) ^ 2 ≤ 4 * pScale p ^ D :=
        calc (p.1.length.size + 1) ^ 2 ≤ (2 * pScale p) ^ 2 := Nat.pow_le_pow_left hb 2
          _ = 4 * pScale p ^ 2 := Nat.mul_pow 2 (pScale p) 2
          _ ≤ 4 * pScale p ^ D := Nat.mul_le_mul_left 4
              (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega))
      exact hsq.trans (by
        have hp1 : 1 ≤ pLen p := by dsimp only [pLen]; omega
        nlinarith [Nat.one_le_pow D (pScale p) hS1])
    have hsub0 := Nat.mul_le_mul_left (pLen p) hpow0
    have hsub_dl := Nat.mul_le_mul_left (pLen p) hpow_dl
    have hsum : R p + B p + ((encNat p.1.length).length + 1) ^ 2 ≤
        (100 + 6 ^ ds) * (pLen p * pScale p ^ D) := by
      rw [Nat.add_mul 100 (6 ^ ds)]
      omega
    have hmul : (p.1.length + 1) * (R p + B p + ((encNat p.1.length).length + 1) ^ 2) ≤
        (100 + 6 ^ ds) * ((p.1.length + 1) * pLen p * pScale p ^ D) :=
      ((Nat.mul_le_mul_left (p.1.length + 1) hsum).trans_eq (Nat.mul_left_comm _ _ _)).trans_eq
        (congrArg ((100 + 6 ^ ds) * ·) (Nat.mul_assoc _ _ _).symm)
    have hsub' : pLen p * pScale p ^ D ≤ (p.1.length + 1) * pLen p * pScale p ^ D := by
      have : pLen p ≤ (p.1.length + 1) * pLen p := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      exact Nat.mul_le_mul_right _ this
    change _ ≤ (128 + 6 ^ ds) * ((p.1.length + 1) * pLen p * pScale p ^ D) + 0
    rw [Nat.add_mul 100 (6 ^ ds)] at hmul
    rw [Nat.add_mul 128 (6 ^ ds)]
    omega
  · refine BigOLe.of_le_linear (128 + 6 ^ ds) 0 fun p => ?_
    have hS1 : 1 ≤ pScale p := by dsimp only [pScale]; omega
    have hpow0 := Nat.mul_le_mul_left (pLen p)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : D₀ ≤ D))
    have hpow_dl := Nat.mul_le_mul_left (pLen p)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D, D₀]; omega : dl + 1 ≤ D))
    have hpow_ds : (6 * pScale p) ^ ds ≤ 6 ^ ds * pScale p ^ D :=
      calc (6 * pScale p) ^ ds = 6 ^ ds * pScale p ^ ds := Nat.mul_pow 6 _ ds
        _ ≤ 6 ^ ds * pScale p ^ D := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega))
    have hR : R p ≤ 6 ^ ds * (pLen p * pScale p ^ D) :=
      (Nat.mul_le_mul_left (pLen p) hpow_ds).trans_eq (Nat.mul_left_comm _ _ _)
    have hB : B p ≤ 96 * (pLen p * pScale p ^ D) := by
      have hSD : pScale p ≤ pScale p ^ D := Nat.le_self_pow (by dsimp only [D]; omega) _
      dsimp only [B]; nlinarith [Nat.mul_le_mul_left (pLen p) hSD]
    have hnsz : (encNat p.1.length).length ≤ pLen p * pScale p ^ D := by
      rw [length_encNat]
      have h1 : p.1.length.size ≤ pScale p := by dsimp only [pScale]; omega
      have h2 : pScale p ≤ pScale p ^ D := Nat.le_self_pow (by dsimp only [D]; omega) _
      exact (h1.trans h2).trans (Nat.le_mul_of_pos_left _ (by dsimp only [pLen]; omega))
    change _ ≤ (128 + 6 ^ ds) * (pLen p * pScale p ^ D) + 0
    rw [Nat.add_mul 128 (6 ^ ds)]
    omega

private theorem computableInPolyTime_scal1 :
    ComputableInPolyTime
      (fun q : ℕ × (ℕ × (ℕ × ℕ)) =>
        ((1 : ℕ), ((3 * q.1 * q.2.1 ^ 2, 3 * q.1 * q.2.2.1 ^ 2), 3 * q.1 * q.2.2.2 ^ 2)))
      (encPair encNat (encPair encNat (encPair encNat encNat)))
      (encPair encNat (encPair (encPair encNat encNat) encNat)) := by fun_prop

private theorem computableInPolyTime_scal2 :
    ComputableInPolyTime
      (fun q : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) =>
        (q.2.1, ((3 * q.1 * q.2.2.1, 3 * q.1 * q.2.2.2.1), 3 * q.1 * q.2.2.2.2)))
      (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
      (encPair encNat (encPair (encPair encNat encNat) encNat)) := by fun_prop

/-- `modulusList` runs in `O((|Q| + 1) * modLen x * modScale x ^ d)` time and
`O(modLen x * modScale x ^ d)` space. -/
theorem computableInO_modulusList :
    ∃ d, ComputableInO (fun x : ModInput => modulusList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      encModInput encNat
      (fun x => (x.1.length + 1) * modLen x * modScale x ^ d)
      (fun x => modLen x * modScale x ^ d) := by
  obtain ⟨dl, hlenL⟩ := computableInO_listLengthNat encIntBin
  obtain ⟨dc, hcoll⟩ := computableInO_collList
  obtain ⟨ds, hsp⟩ := computableInO_searchPrimeList
  obtain ⟨ds1, _, hScal1Deg⟩ := computableInPolyTime_scal1.exists_degree
  obtain ⟨ds2, _, hScal2Deg⟩ := computableInPolyTime_scal2.exists_degree
  obtain ⟨dmul, _, hMulOutDeg⟩ := computableInPolyTime_mulNat.exists_degree
  have hQ := ComputableInO.fst (encList encNat) (encPair encNat encIntTriple)
  have hR := ComputableInO.snd (encList encNat) (encPair encNat encIntTriple)
  have hLam : ComputableInO (fun x : ModInput => x.2.1) encModInput encNat
      (fun x => (encModInput x).length) (fun x => (encModInput x).length) :=
    ((ComputableInO.fst encNat encIntTriple).comp_linear hR).mono_le
      (fun x => by simp only [encModInput, length_encPair]; omega)
      (fun x => by simp only [encModInput, length_encPair]; omega)
  have hTri : ComputableInO (fun x : ModInput => x.2.2) encModInput encIntTriple
      (fun x => (encModInput x).length) (fun x => (encModInput x).length) :=
    ((ComputableInO.snd encNat encIntTriple).comp_linear hR).mono_le
      (fun x => by simp only [encModInput, length_encPair]; omega)
      (fun x => by simp only [encModInput, length_encPair]; omega)
  have hL1 : ComputableInO (fun x : ModInput => x.2.2.1) encModInput (encList encIntBin)
      (fun x => (encModInput x).length) (fun x => (encModInput x).length) :=
    ((ComputableInO.fst (encList encIntBin)
      (encPair (encList encIntBin) (encList encIntBin))).comp_linear hTri).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL23 : ComputableInO (fun x : ModInput => x.2.2.2) encModInput
      (encPair (encList encIntBin) (encList encIntBin))
      (fun x => (encModInput x).length) (fun x => (encModInput x).length) :=
    ((ComputableInO.snd (encList encIntBin)
      (encPair (encList encIntBin) (encList encIntBin))).comp_linear hTri).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL2 : ComputableInO (fun x : ModInput => x.2.2.2.1) encModInput (encList encIntBin)
      (fun x => (encModInput x).length) (fun x => (encModInput x).length) :=
    ((ComputableInO.fst (encList encIntBin) (encList encIntBin)).comp_linear hL23).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hL3 : ComputableInO (fun x : ModInput => x.2.2.2.2) encModInput (encList encIntBin)
      (fun x => (encModInput x).length) (fun x => (encModInput x).length) :=
    ((ComputableInO.snd (encList encIntBin) (encList encIntBin)).comp_linear hL23).mono_le
      (fun _ => le_rfl) (fun _ => le_rfl)
  have hlenIn_le (x : ModInput) : (encModInput x).length ≤ 16 * (modLen x * modScale x) := by
    simp only [encModInput, encIntTriple, length_encPair, length_encNat]
    have hQ_l := length_encList_le_mul encNat x.1 (b := listMax Nat.size x.1)
      fun r hr => by rw [length_encNat]; exact le_listMax hr
    have h1 := length_encList_le_mul encIntBin x.2.2.1
      (b := listMax (fun z => (encIntBin z).length) x.2.2.1)
      fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
    have h2 := length_encList_le_mul encIntBin x.2.2.2.1
      (b := listMax (fun z => (encIntBin z).length) x.2.2.2.1)
      fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
    have h3 := length_encList_le_mul encIntBin x.2.2.2.2
      (b := listMax (fun z => (encIntBin z).length) x.2.2.2.2)
      fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
    have hbQ : 2 * listMax Nat.size x.1 + 1 ≤ 2 * modScale x := by dsimp only [modScale]; omega
    have hb1 : 2 * listMax (fun z => (encIntBin z).length) x.2.2.1 + 1 ≤ 2 * modScale x := by
      dsimp only [modScale]; omega
    have hb2 : 2 * listMax (fun z => (encIntBin z).length) x.2.2.2.1 + 1 ≤ 2 * modScale x := by
      dsimp only [modScale]; omega
    have hb3 : 2 * listMax (fun z => (encIntBin z).length) x.2.2.2.2 + 1 ≤ 2 * modScale x := by
      dsimp only [modScale]; omega
    have hQ' := hQ_l.trans (Nat.mul_le_mul_left _ hbQ)
    have h1' := h1.trans (Nat.mul_le_mul_left _ hb1)
    have h2' := h2.trans (Nat.mul_le_mul_left _ hb2)
    have h3' := h3.trans (Nat.mul_le_mul_left _ hb3)
    have hL : x.1.length + x.2.2.1.length + x.2.2.2.1.length + x.2.2.2.2.length + 1 =
        modLen x := rfl
    have hLm : x.2.1.size + 4 ≤ modScale x := by dsimp only [modScale]; omega
    nlinarith
  have mkLen : ∀ (fL : ModInput → List ℤ)
      (hfL : ComputableInO fL encModInput (encList encIntBin)
        (fun x => (encModInput x).length) (fun x => (encModInput x).length))
      (hl : ∀ x, (fL x).length + 1 ≤ modLen x)
      (hm : ∀ x, listMax (fun z => (encIntBin z).length) (fL x) ≤ modScale x),
      ComputableInO (fun x => (fL x).length) encModInput encNat
        (fun x => modLen x * modScale x ^ (dl + 1))
        (fun x => modLen x * modScale x ^ (dl + 1)) := by
    intro fL hfL hl hm
    refine (hlenL.comp hfL).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (32 + 2 ^ dl) 0 fun x => ?_
      have hin := hlenIn_le x
      have hS0 : 1 ≤ modScale x := by dsimp only [modScale]; omega
      have hS1 : modScale x ≤ modScale x ^ (dl + 1) := Nat.le_self_pow (by omega) _
      have hin' : (encModInput x).length ≤ 16 * (modLen x * modScale x ^ (dl + 1)) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (modLen x) hS1])
      have hfl_enc : (encList encIntBin (fL x)).length ≤
          3 * (modLen x * modScale x ^ (dl + 1)) := by
        have h1 := length_encList_le_mul encIntBin (fL x)
          (b := listMax (fun z => (encIntBin z).length) (fL x))
          fun z hz => le_listMax (f := fun z => (encIntBin z).length) hz
        have h2 : 2 * listMax (fun z => (encIntBin z).length) (fL x) + 1 ≤ 3 * modScale x := by
          have := hm x; omega
        calc _ ≤ (fL x).length * (3 * modScale x) := h1.trans (Nat.mul_le_mul_left _ h2)
          _ ≤ 3 * (modLen x * modScale x ^ (dl + 1)) := by
            have := hl x
            nlinarith [Nat.mul_le_mul_left (modLen x) hS1]
      have hpow : (listMax (fun z => (encIntBin z).length) (fL x) + (fL x).length.size + 4) ^ dl ≤
          2 ^ dl * modScale x ^ (dl + 1) := by
        have hb : listMax (fun z => (encIntBin z).length) (fL x) + (fL x).length.size + 4 ≤
            2 * modScale x := by
          have hmx := hm x
          have hls : (fL x).length.size + 4 ≤ modScale x := by
            have := Nat.size_le_size ((Nat.le_succ _).trans (hl x))
            dsimp only [modScale]; omega
          omega
        calc _ ≤ (2 * modScale x) ^ dl := Nat.pow_le_pow_left hb dl
          _ = 2 ^ dl * modScale x ^ dl := Nat.mul_pow 2 _ dl
          _ ≤ 2 ^ dl * modScale x ^ (dl + 1) := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS0 (Nat.le_succ dl))
      have hmul : ((fL x).length + 1) *
          (listMax (fun z => (encIntBin z).length) (fL x) + (fL x).length.size + 4) ^ dl ≤
          2 ^ dl * (modLen x * modScale x ^ (dl + 1)) :=
        (Nat.mul_le_mul (hl x) hpow).trans_eq (Nat.mul_left_comm _ _ _)
      have hsp := hpow.trans (Nat.mul_le_mul_left _
        (Nat.le_mul_of_pos_left _ (show 0 < modLen x by dsimp only [modLen]; omega)))
      rw [Nat.add_mul 32 (2 ^ dl)]
      omega
  have hn1 := mkLen _ hL1 (fun x => by dsimp only [modLen]; omega)
    (fun x => by dsimp only [modScale]; omega)
  have hn2 := mkLen _ hL2 (fun x => by dsimp only [modLen]; omega)
    (fun x => by dsimp only [modScale]; omega)
  have hn3 := mkLen _ hL3 (fun x => by dsimp only [modLen]; omega)
    (fun x => by dsimp only [modScale]; omega)
  let D_s1 := dl + ds1 + 2
  have hScal1 : ComputableInO
      (fun x : ModInput => ((1 : ℕ), ((3 * x.2.1 * x.2.2.1.length ^ 2,
        3 * x.2.1 * x.2.2.2.1.length ^ 2), 3 * x.2.1 * x.2.2.2.2.length ^ 2)))
      encModInput (encPair encNat (encPair (encPair encNat encNat) encNat))
      (fun x => modLen x * modScale x ^ D_s1) (fun x => modLen x * modScale x ^ D_s1) := by
    refine (hScal1Deg.inO.comp (hLam.prod (hn1.prod (hn2.prod hn3)))).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (32 + 16 ^ ds1) 0 fun x => ?_
      have hin := hlenIn_le x
      have hS1 : 1 ≤ modScale x := by dsimp only [modScale]; omega
      have hSD : modScale x ≤ modScale x ^ D_s1 := Nat.le_self_pow (by dsimp only [D_s1]; omega) _
      have hsub := Nat.mul_le_mul_left (modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D_s1]; omega : dl + 1 ≤ D_s1))
      have hsc_in : (encPair encNat (encPair encNat (encPair encNat encNat))
          (x.2.1, (x.2.2.1.length, (x.2.2.2.1.length, x.2.2.2.2.length)))).length + 1 ≤
          16 * modScale x := by
        simp only [length_encPair, length_encNat]
        have s1 := Nat.size_le_size (by dsimp only [modLen]; omega : x.2.2.1.length ≤ modLen x)
        have s2 := Nat.size_le_size (by dsimp only [modLen]; omega : x.2.2.2.1.length ≤ modLen x)
        have s3 := Nat.size_le_size (by dsimp only [modLen]; omega : x.2.2.2.2.length ≤ modLen x)
        dsimp only [modScale]; omega
      have hpow : ((encPair encNat (encPair encNat (encPair encNat encNat))
          (x.2.1, (x.2.2.1.length, (x.2.2.2.1.length, x.2.2.2.2.length)))).length + 1) ^ ds1 ≤
          16 ^ ds1 * (modLen x * modScale x ^ D_s1) :=
        calc _ ≤ (16 * modScale x) ^ ds1 := Nat.pow_le_pow_left hsc_in ds1
          _ = 16 ^ ds1 * modScale x ^ ds1 := Nat.mul_pow 16 _ ds1
          _ ≤ 16 ^ ds1 * modScale x ^ D_s1 := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D_s1]; omega))
          _ ≤ 16 ^ ds1 * (modLen x * modScale x ^ D_s1) := Nat.mul_le_mul_left _
              (Nat.le_mul_of_pos_left _ (by dsimp only [modLen]; omega))
      have hin' : (encModInput x).length ≤ 16 * (modLen x * modScale x ^ D_s1) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (modLen x) hSD])
      rw [Nat.add_mul 32 (16 ^ ds1)]
      omega
  let D₁ := D_s1 + ds + 2
  have hp1 : ComputableInO (fun x : ModInput => firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      encModInput encNat
      (fun x => (x.1.length + 1) * modLen x * modScale x ^ D₁)
      (fun x => modLen x * modScale x ^ D₁) := by
    refine ((hsp.comp (hQ.prod (hScal1.prod hTri))).of_enc_eq
      (g := fun x => firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) fun _ => rfl).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (64 + 48 ^ ds) 0 fun x => ?_
      have hin := hlenIn_le x
      have hS1 : 1 ≤ modScale x := by dsimp only [modScale]; omega
      have hSD : modScale x ≤ modScale x ^ D₁ := Nat.le_self_pow (by dsimp only [D₁]; omega) _
      have hin' : (encModInput x).length ≤ 16 * (modLen x * modScale x ^ D₁) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (modLen x) hSD])
      have hsub := Nat.mul_le_mul_left (modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega : D_s1 ≤ D₁))
      have hsc1_out : (encPair encNat (encPair (encPair encNat encNat) encNat)
          (1, ((3 * x.2.1 * x.2.2.1.length ^ 2, 3 * x.2.1 * x.2.2.2.1.length ^ 2),
            3 * x.2.1 * x.2.2.2.2.length ^ 2))).length ≤ 28 * modScale x := by
        simp only [length_encPair, length_encNat]
        have h1sz : (1 : ℕ).size = 1 := by decide
        have h3sz : (3 : ℕ).size = 2 := by decide
        have bnd : ∀ k : ℕ, k ≤ modLen x →
            (3 * x.2.1 * k ^ 2).size ≤ x.2.1.size + 2 * (modLen x).size + 5 := by
          intro k hk
          have a1 := Nat.size_mul_le (3 * x.2.1) (k ^ 2)
          have a2 := Nat.size_mul_le 3 x.2.1
          have a3 := Nat.size_pow_le k 2
          have a4 := Nat.size_le_size hk
          omega
        have b1 := bnd x.2.2.1.length (by dsimp only [modLen]; omega)
        have b2 := bnd x.2.2.2.1.length (by dsimp only [modLen]; omega)
        have b3 := bnd x.2.2.2.2.length (by dsimp only [modLen]; omega)
        dsimp only [modScale]; omega
      let ps1 := listMax Nat.size x.1 + x.1.length.size +
        (encPair encNat (encPair (encPair encNat encNat) encNat)
          (1, ((3 * x.2.1 * x.2.2.1.length ^ 2, 3 * x.2.1 * x.2.2.2.1.length ^ 2),
            3 * x.2.1 * x.2.2.2.2.length ^ 2))).length +
        listMax (fun z => (encIntBin z).length) x.2.2.1 +
        listMax (fun z => (encIntBin z).length) x.2.2.2.1 +
        listMax (fun z => (encIntBin z).length) x.2.2.2.2 + (modLen x).size + 16
      have hps_le : ps1 ≤ 48 * modScale x := by
        dsimp only [ps1, modScale] at hsc1_out ⊢; omega
      have hpow_ds : ps1 ^ ds ≤ 48 ^ ds * modScale x ^ D₁ :=
        calc _ ≤ (48 * modScale x) ^ ds := Nat.pow_le_pow_left hps_le ds
          _ = 48 ^ ds * modScale x ^ ds := Nat.mul_pow 48 _ ds
          _ ≤ 48 ^ ds * modScale x ^ D₁ := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D₁]; omega))
      have hmul_sp : modLen x * _ ≤ 48 ^ ds * (modLen x * modScale x ^ D₁) :=
        (Nat.mul_le_mul_left (modLen x) hpow_ds).trans_eq (Nat.mul_left_comm _ _ _)
      have hmul_tm : (x.1.length + 1) * modLen x * _ ≤
          48 ^ ds * ((x.1.length + 1) * modLen x * modScale x ^ D₁) :=
        (Nat.mul_le_mul_left ((x.1.length + 1) * modLen x) hpow_ds).trans_eq
          (Nat.mul_left_comm _ _ _)
      have hpQ : (encList encNat x.1).length ≤ (encModInput x).length := by
        simp only [encModInput, length_encPair]; omega
      have hZ_tm : modLen x * modScale x ^ D₁ ≤ (x.1.length + 1) * modLen x * modScale x ^ D₁ :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have hml_eq : x.1.length + x.2.2.1.length + x.2.2.2.1.length + x.2.2.2.2.length + 1 =
          modLen x := rfl
      dsimp only [encModInput, ps1] at hpQ hin' hmul_sp hmul_tm ⊢
      rw [hml_eq] at *
      rw [Nat.add_mul 64 (48 ^ ds)]
      omega
  have hp1_sz (x : ModInput) :
      (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).size ≤ listMax Nat.size x.1 + 1 := by
    have h1sz : (1 : ℕ).size = 1 := by decide
    rcases searchPrimeList_mem_or_one x.1 1 _ _ _ x.2.2.1 x.2.2.2.1 x.2.2.2.2 with h1 | hmem
    · unfold firstPList; rw [h1, h1sz]; omega
    · exact (le_listMax (f := Nat.size) hmem).trans (Nat.le_succ _)
  let D₂ := D₁ + dc + 2
  have mkCollP : ∀ (fL : ModInput → List ℤ)
      (hfL : ComputableInO fL encModInput (encList encIntBin)
        (fun x => (encModInput x).length) (fun x => (encModInput x).length))
      (hl : ∀ x, (fL x).length + 1 ≤ modLen x)
      (hm : ∀ x, listMax (fun z => (encIntBin z).length) (fL x) ≤ modScale x),
      ComputableInO
        (fun x : ModInput => collList (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) (fL x))
        encModInput encNat
        (fun x => (x.1.length + 1) * modLen x * modScale x ^ D₂)
        (fun x => modLen x * modScale x ^ D₂) := by
    intro fL hfL hl hm
    refine (hcoll.comp (hp1.prod hfL)).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (32 + 4 ^ dc) 0 fun x => ?_
      have hin := hlenIn_le x
      have hS1 : 1 ≤ modScale x := by dsimp only [modScale]; omega
      have hSD : modScale x ≤ modScale x ^ D₂ := Nat.le_self_pow (by dsimp only [D₂]; omega) _
      have hin' : (encModInput x).length ≤ 16 * (modLen x * modScale x ^ D₂) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (modLen x) hSD])
      have hsub1 : modLen x * modScale x ^ D₁ ≤ modLen x * modScale x ^ D₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp only [D₂]; omega))
      have hsub1_tm : (x.1.length + 1) * modLen x * modScale x ^ D₁ ≤
          (x.1.length + 1) * modLen x * modScale x ^ D₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hS1 (by dsimp only [D₂]; omega))
      have hcs : collScale (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, fL x) ≤
          4 * modScale x := by
        have hp1' : (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).size ≤ modScale x := by
          have := hp1_sz x; dsimp only [modScale]; omega
        have hlsz : (fL x).length.size ≤ (modLen x).size :=
          Nat.size_le_size ((Nat.le_succ _).trans (hl x))
        have hc0 := collScale_le
          (p := (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, fL x)) hp1' (hm x) hlsz
        have hms_ge : (modLen x).size + 1 ≤ modScale x := by dsimp only [modScale]; omega
        omega
      have hpow : collScale (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, fL x) ^ dc ≤
          4 ^ dc * modScale x ^ D₂ :=
        calc _ ≤ (4 * modScale x) ^ dc := Nat.pow_le_pow_left hcs dc
          _ = 4 ^ dc * modScale x ^ dc := Nat.mul_pow 4 _ dc
          _ ≤ 4 ^ dc * modScale x ^ D₂ := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D₂]; omega))
      have hmul_sp : ((fL x).length + 1) *
          collScale (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, fL x) ^ dc ≤
          4 ^ dc * (modLen x * modScale x ^ D₂) :=
        (Nat.mul_le_mul (hl x) hpow).trans_eq (Nat.mul_left_comm _ _ _)
      have hZ_tm : modLen x * modScale x ^ D₂ ≤ (x.1.length + 1) * modLen x * modScale x ^ D₂ :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have hmul_tm := hmul_sp.trans (Nat.mul_le_mul_left (4 ^ dc) hZ_tm)
      dsimp only at *
      rw [Nat.add_mul 32 (4 ^ dc)]
      omega
  have hcp1 := mkCollP _ hL1 (fun x => by dsimp only [modLen]; omega)
    (fun x => by dsimp only [modScale]; omega)
  have hcp2 := mkCollP _ hL2 (fun x => by dsimp only [modLen]; omega)
    (fun x => by dsimp only [modScale]; omega)
  have hcp3 := mkCollP _ hL3 (fun x => by dsimp only [modLen]; omega)
    (fun x => by dsimp only [modScale]; omega)
  let D_s2 := D₂ + ds2 + 2
  have hScal2 : ComputableInO
      (fun x : ModInput =>
        let pVal := firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
        (pVal, ((3 * x.2.1 * collList pVal x.2.2.1, 3 * x.2.1 * collList pVal x.2.2.2.1),
          3 * x.2.1 * collList pVal x.2.2.2.2)))
      encModInput (encPair encNat (encPair (encPair encNat encNat) encNat))
      (fun x => (x.1.length + 1) * modLen x * modScale x ^ D_s2)
      (fun x => modLen x * modScale x ^ D_s2) := by
    refine (hScal2Deg.inO.comp (hLam.prod (hp1.prod (hcp1.prod (hcp2.prod hcp3))))).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (64 + 32 ^ ds2) 0 fun x => ?_
      have hin := hlenIn_le x
      have hS1 : 1 ≤ modScale x := by dsimp only [modScale]; omega
      have hSD : modScale x ≤ modScale x ^ D_s2 := Nat.le_self_pow (by dsimp only [D_s2]; omega) _
      have hin' : (encModInput x).length ≤ 16 * (modLen x * modScale x ^ D_s2) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (modLen x) hSD])
      have hsub1_sp := Nat.mul_le_mul_left (modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D_s2, D₂]; omega : D₁ ≤ D_s2))
      have hsub1_tm := Nat.mul_le_mul_left ((x.1.length + 1) * modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D_s2, D₂]; omega : D₁ ≤ D_s2))
      have hsub2_sp := Nat.mul_le_mul_left (modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D_s2]; omega : D₂ ≤ D_s2))
      have hsub2_tm := Nat.mul_le_mul_left ((x.1.length + 1) * modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D_s2]; omega : D₂ ≤ D_s2))
      set pVal := firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
      have hc_sz : ∀ L : List ℤ, L.length ≤ modLen x →
          (collList pVal L).size ≤ 2 * (modLen x).size + 1 := fun L hL =>
        (Nat.size_le_size ((collList_le_sq pVal L).trans (Nat.pow_le_pow_left hL 2))).trans
          (Nat.size_pow_le _ 2)
      have hc1s := hc_sz x.2.2.1 (by dsimp only [modLen]; omega)
      have hc2s := hc_sz x.2.2.2.1 (by dsimp only [modLen]; omega)
      have hc3s := hc_sz x.2.2.2.2 (by dsimp only [modLen]; omega)
      have hp1s := hp1_sz x
      have hsc2_in : (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))
          (x.2.1, (pVal, (collList pVal x.2.2.1,
            (collList pVal x.2.2.2.1, collList pVal x.2.2.2.2))))).length + 1 ≤
          32 * modScale x := by
        simp only [length_encPair, length_encNat]
        dsimp only [modScale, pVal] at *; omega
      have hpow : ((encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))
          (x.2.1, (pVal, (collList pVal x.2.2.1,
            (collList pVal x.2.2.2.1, collList pVal x.2.2.2.2))))).length + 1) ^ ds2 ≤
          32 ^ ds2 * (modLen x * modScale x ^ D_s2) :=
        calc _ ≤ (32 * modScale x) ^ ds2 := Nat.pow_le_pow_left hsc2_in ds2
          _ = 32 ^ ds2 * modScale x ^ ds2 := Nat.mul_pow 32 _ ds2
          _ ≤ 32 ^ ds2 * modScale x ^ D_s2 := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D_s2]; omega))
          _ ≤ 32 ^ ds2 * (modLen x * modScale x ^ D_s2) := Nat.mul_le_mul_left _
              (Nat.le_mul_of_pos_left _ (by dsimp only [modLen]; omega))
      have hZ_tm : modLen x * modScale x ^ D_s2 ≤
          (x.1.length + 1) * modLen x * modScale x ^ D_s2 :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have hpow_tm := hpow.trans (Nat.mul_le_mul_left (32 ^ ds2) hZ_tm)
      dsimp only [pVal] at hpow hpow_tm ⊢
      rw [Nat.add_mul 64 (32 ^ ds2)]
      omega
  let D₃ := D_s2 + ds + 2
  have hp2 : ComputableInO
      (fun x : ModInput => secondPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
        (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
      encModInput encNat
      (fun x => (x.1.length + 1) * modLen x * modScale x ^ D₃)
      (fun x => modLen x * modScale x ^ D₃) := by
    refine ((hsp.comp (hQ.prod (hScal2.prod hTri))).of_enc_eq
      (g := fun x => secondPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
        (firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)) fun _ => rfl).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (64 + 48 ^ ds) 0 fun x => ?_
      have hin := hlenIn_le x
      have hS1 : 1 ≤ modScale x := by dsimp only [modScale]; omega
      have hSD : modScale x ≤ modScale x ^ D₃ := Nat.le_self_pow (by dsimp only [D₃]; omega) _
      have hin' : (encModInput x).length ≤ 16 * (modLen x * modScale x ^ D₃) :=
        hin.trans (by nlinarith [Nat.mul_le_mul_left (modLen x) hSD])
      have hsub_sp := Nat.mul_le_mul_left (modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D₃]; omega : D_s2 ≤ D₃))
      have hsub_tm := Nat.mul_le_mul_left ((x.1.length + 1) * modLen x)
        (Nat.pow_le_pow_right hS1 (by dsimp only [D₃]; omega : D_s2 ≤ D₃))
      set pVal := firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
      have hc_sz : ∀ L : List ℤ, L.length ≤ modLen x →
          (collList pVal L).size ≤ 2 * (modLen x).size + 1 := fun L hL =>
        (Nat.size_le_size ((collList_le_sq pVal L).trans (Nat.pow_le_pow_left hL 2))).trans
          (Nat.size_pow_le _ 2)
      have hc1s := hc_sz x.2.2.1 (by dsimp only [modLen]; omega)
      have hc2s := hc_sz x.2.2.2.1 (by dsimp only [modLen]; omega)
      have hc3s := hc_sz x.2.2.2.2 (by dsimp only [modLen]; omega)
      have hp1s := hp1_sz x
      have hsc2_out : (encPair encNat (encPair (encPair encNat encNat) encNat)
          (pVal, ((3 * x.2.1 * collList pVal x.2.2.1, 3 * x.2.1 * collList pVal x.2.2.2.1),
            3 * x.2.1 * collList pVal x.2.2.2.2))).length ≤ 28 * modScale x := by
        simp only [length_encPair, length_encNat]
        have h3sz : (3 : ℕ).size = 2 := by decide
        have bnd : ∀ c : ℕ, c.size ≤ 2 * (modLen x).size + 1 →
            (3 * x.2.1 * c).size ≤ x.2.1.size + 2 * (modLen x).size + 5 := by
          intro c hc
          have a1 := Nat.size_mul_le (3 * x.2.1) c
          have a2 := Nat.size_mul_le 3 x.2.1
          omega
        have b1 := bnd _ hc1s
        have b2 := bnd _ hc2s
        have b3 := bnd _ hc3s
        dsimp only [modScale, pVal] at *; omega
      let ps2 := listMax Nat.size x.1 + x.1.length.size +
        (encPair encNat (encPair (encPair encNat encNat) encNat)
          (pVal, ((3 * x.2.1 * collList pVal x.2.2.1, 3 * x.2.1 * collList pVal x.2.2.2.1),
            3 * x.2.1 * collList pVal x.2.2.2.2))).length +
        listMax (fun z => (encIntBin z).length) x.2.2.1 +
        listMax (fun z => (encIntBin z).length) x.2.2.2.1 +
        listMax (fun z => (encIntBin z).length) x.2.2.2.2 + (modLen x).size + 16
      have hps2_le : ps2 ≤ 48 * modScale x := by
        dsimp only [ps2, modScale] at hsc2_out ⊢; omega
      have hpow_ds : ps2 ^ ds ≤ 48 ^ ds * modScale x ^ D₃ :=
        calc _ ≤ (48 * modScale x) ^ ds := Nat.pow_le_pow_left hps2_le ds
          _ = 48 ^ ds * modScale x ^ ds := Nat.mul_pow 48 _ ds
          _ ≤ 48 ^ ds * modScale x ^ D₃ := Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hS1 (by dsimp only [D₃]; omega))
      have hmul_sp : modLen x * _ ≤ 48 ^ ds * (modLen x * modScale x ^ D₃) :=
        (Nat.mul_le_mul_left (modLen x) hpow_ds).trans_eq (Nat.mul_left_comm _ _ _)
      have hmul_tm : (x.1.length + 1) * modLen x * _ ≤
          48 ^ ds * ((x.1.length + 1) * modLen x * modScale x ^ D₃) :=
        (Nat.mul_le_mul_left ((x.1.length + 1) * modLen x) hpow_ds).trans_eq
          (Nat.mul_left_comm _ _ _)
      have hpQ : (encList encNat x.1).length ≤ (encModInput x).length := by
        simp only [encModInput, length_encPair]; omega
      have hZ_tm : modLen x * modScale x ^ D₃ ≤ (x.1.length + 1) * modLen x * modScale x ^ D₃ :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have hml_eq : x.1.length + x.2.2.1.length + x.2.2.2.1.length + x.2.2.2.2.length + 1 =
          modLen x := rfl
      dsimp only [encModInput, pVal, ps2] at hpQ hin' hmul_sp hmul_tm ⊢
      rw [hml_eq] at *
      rw [Nat.add_mul 64 (48 ^ ds)]
      omega
  let D := D₃ + dmul + 2
  have hMod := (hMulOutDeg.inO.comp (hp1.prod hp2)).of_enc_eq
    (g := fun x : ModInput => modulusList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) fun _ => rfl
  refine ⟨D, hMod.weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear (8 + 16 ^ dmul) 0 fun x => ?_
    have hS1 : 1 ≤ modScale x := by dsimp only [modScale]; omega
    have hsub1_sp := Nat.mul_le_mul_left (modLen x)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D, D₃, D_s2, D₂]; omega : D₁ ≤ D))
    have hsub1_tm := Nat.mul_le_mul_left ((x.1.length + 1) * modLen x)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D, D₃, D_s2, D₂]; omega : D₁ ≤ D))
    have hsub3_sp := Nat.mul_le_mul_left (modLen x)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : D₃ ≤ D))
    have hsub3_tm := Nat.mul_le_mul_left ((x.1.length + 1) * modLen x)
      (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega : D₃ ≤ D))
    set pVal := firstPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
    set qVal := secondPList x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 pVal
    have hp1s := hp1_sz x
    have hq_sz : qVal.size ≤ listMax Nat.size x.1 + 1 := by
      have h1sz : (1 : ℕ).size = 1 := by decide
      rcases searchPrimeList_mem_or_one x.1 pVal _ _ _ x.2.2.1 x.2.2.2.1 x.2.2.2.2 with h1 | hmem
      · unfold qVal secondPList; rw [h1, h1sz]; omega
      · exact (le_listMax (f := Nat.size) hmem).trans (Nat.le_succ _)
    have hmul_in : (encPair encNat encNat (pVal, qVal)).length + 1 ≤ 16 * modScale x := by
      rw [length_encPair, length_encNat, length_encNat]
      dsimp only [modScale, pVal] at *; omega
    have hpow_dmul : ((encPair encNat encNat (pVal, qVal)).length + 1) ^ dmul ≤
        16 ^ dmul * (modLen x * modScale x ^ D) :=
      calc _ ≤ (16 * modScale x) ^ dmul := Nat.pow_le_pow_left hmul_in dmul
        _ = 16 ^ dmul * modScale x ^ dmul := Nat.mul_pow 16 _ dmul
        _ ≤ 16 ^ dmul * modScale x ^ D := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right hS1 (by dsimp only [D]; omega))
        _ ≤ 16 ^ dmul * (modLen x * modScale x ^ D) := Nat.mul_le_mul_left _
            (Nat.le_mul_of_pos_left _ (by dsimp only [modLen]; omega))
    have hZ_tm : modLen x * modScale x ^ D ≤ (x.1.length + 1) * modLen x * modScale x ^ D :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hpow_tm := hpow_dmul.trans (Nat.mul_le_mul_left (16 ^ dmul) hZ_tm)
    dsimp only [pVal, qVal] at hpow_dmul hpow_tm ⊢
    rw [Nat.add_mul 8 (16 ^ dmul)]
    omega

end CslibFrontier.Complexity
