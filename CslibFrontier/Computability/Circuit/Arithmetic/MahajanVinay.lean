/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.AlgebraicBranchingProgram
public import CslibFrontier.Computability.Circuit.Arithmetic.ABPOperations
public import CslibFrontier.Computability.Circuit.Arithmetic.ClowSequence
public import CslibFrontier.Computability.Circuit.Arithmetic.ClowInvolution
public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Projection
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mahajan–Vinay Layered ABP for the Determinant

This module constructs the Mahajan–Vinay layered algebraic branching program (ABP) of size
`O(m ^ 4)` computing `M.det` for any `m × m` specialization matrix `M` over an arbitrary
commutative ring `K`. Combined with `ABP.isProjection_det`, this establishes the polynomial
equivalence between ABP size and projection determinantal complexity.

## Main results

* `CslibFrontier.Computability.Circuit.exists_abp_det_of_isSubstMatrix`: every `m × m`
  specialization matrix `M` (`IsSubstMatrix M`) has an ABP computing `M.det` of size
  `≤ 6 * m ^ 4 + 10`.
* `CslibFrontier.Computability.Circuit.exists_abp_det_genericMatrix`: `(genericMatrix K m).det`
  has an ABP of size `≤ 6 * m ^ 4 + 10`.
* `CslibFrontier.Computability.Circuit.abpComplexity_poly_equiv_projDetComplexity`: polynomial
  equivalence between `abpComplexity` and `projDetComplexity`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open MvPolynomial
open Cslib.Circuits.Arithmetic
open scoped Matrix

universe u v

section Clows

/-! ### Layered DAG ABP for `M.det` -/

/-- Vertices of the Mahajan–Vinay layered DAG for an `m × m` matrix (`m ≥ 1`):
source, `m` layers of states `(ℓ, h, u, p)`, two pre-sink parity vertices, and sink. -/
private inductive MVVert (m : ℕ)
  | source
  | state (ℓ h u : Fin m) (p : Bool)
  | presink (p : Bool)
  | sink
deriving DecidableEq

private def MVVert.toNat {m : ℕ} : MVVert m → ℕ
  | .source => 0
  | .state ℓ h u p => 1 + (((ℓ.1 * m + h.1) * m + u.1) * 2 + (if p then 1 else 0))
  | .presink p => 1 + 2 * m ^ 3 + (if p then 1 else 0)
  | .sink => 3 + 2 * m ^ 3

private theorem MVVert.toNat_lt {m : ℕ} (v : MVVert m) : v.toNat < 2 * m ^ 3 + 4 := by
  cases v with
  | source => simp [toNat]
  | state ℓ h u p =>
    simp only [toNat]
    have hℓ := ℓ.2; have hh := h.2; have hu := u.2
    have h1 : ℓ.1 * m + h.1 < m * m := by nlinarith
    have h2 : (ℓ.1 * m + h.1) * m + u.1 < m ^ 3 := by nlinarith [pow_succ m 2, sq m]
    cases p <;> simp <;> omega
  | presink p => cases p <;> simp [toNat] <;> omega
  | sink => simp [toNat]; omega

private theorem MVVert.toNat_injective {m : ℕ} : Function.Injective (MVVert.toNat (m := m)) := by
  intro v₁ v₂ h
  cases v₁ <;> cases v₂ <;> simp only [toNat] at h
  · rfl
  · omega
  · omega
  · omega
  · omega
  · rename_i ℓ₁ h₁ u₁ p₁ ℓ₂ h₂ u₂ p₂
    have hℓ₁ := ℓ₁.2; have hh₁ := h₁.2; have hu₁ := u₁.2
    have hℓ₂ := ℓ₂.2; have hh₂ := h₂.2; have hu₂ := u₂.2
    have hp : p₁ = p₂ := by cases p₁ <;> cases p₂ <;> simp at h ⊢ <;> omega
    subst hp
    have hmul_eq : (ℓ₁.1 * m + h₁.1) * m + u₁.1 = (ℓ₂.1 * m + h₂.1) * m + u₂.1 := by
      cases p₁ <;> simp at h <;> omega
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hℓ₁
    have hu : u₁ = u₂ := Fin.ext (by
      have hmod := congrArg (· % m) hmul_eq
      rw [mul_comm _ m, Nat.mul_add_mod, mul_comm _ m, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hu₁, Nat.mod_eq_of_lt hu₂] at hmod
      exact hmod)
    subst hu
    have hdiv : ℓ₁.1 * m + h₁.1 = ℓ₂.1 * m + h₂.1 :=
      Nat.eq_of_mul_eq_mul_right hm (by omega)
    have hh : h₁ = h₂ := Fin.ext (by
      have hmod := congrArg (· % m) hdiv
      rw [mul_comm ℓ₁.1 m, Nat.mul_add_mod, mul_comm ℓ₂.1 m, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hh₁, Nat.mod_eq_of_lt hh₂] at hmod
      exact hmod)
    subst hh
    have hℓ : ℓ₁ = ℓ₂ := Fin.ext (Nat.eq_of_mul_eq_mul_right hm (by omega))
    subst hℓ; rfl
  · rename_i ℓ₁ h₁ u₁ p₁ p₂
    have hℓ₁ := ℓ₁.2; have hh₁ := h₁.2; have hu₁ := u₁.2
    have h2 : (ℓ₁.1 * m + h₁.1) * m + u₁.1 < m ^ 3 := by nlinarith [pow_succ m 2, sq m]
    cases p₁ <;> cases p₂ <;> simp at h <;> omega
  · rename_i ℓ₁ h₁ u₁ p₁
    have hℓ₁ := ℓ₁.2; have hh₁ := h₁.2; have hu₁ := u₁.2
    have h2 : (ℓ₁.1 * m + h₁.1) * m + u₁.1 < m ^ 3 := by nlinarith [pow_succ m 2, sq m]
    cases p₁ <;> simp at h <;> omega
  · omega
  · rename_i p₁ ℓ₂ h₂ u₂ p₂
    have hℓ₂ := ℓ₂.2; have hh₂ := h₂.2; have hu₂ := u₂.2
    have h2 : (ℓ₂.1 * m + h₂.1) * m + u₂.1 < m ^ 3 := by nlinarith [pow_succ m 2, sq m]
    cases p₁ <;> cases p₂ <;> simp at h <;> omega
  · rename_i p₁ p₂; cases p₁ <;> cases p₂ <;> simp at h ⊢
  · rename_i p₁; cases p₁
    · simp at h
    · simp at h; omega
  · omega
  · rename_i ℓ₂ h₂ u₂ p₂
    have hℓ₂ := ℓ₂.2; have hh₂ := h₂.2; have hu₂ := u₂.2
    have h2 : (ℓ₂.1 * m + h₂.1) * m + u₂.1 < m ^ 3 := by nlinarith [pow_succ m 2, sq m]
    cases p₂ <;> simp at h <;> omega
  · rename_i p₂; cases p₂
    · simp at h
    · simp at h; omega
  · rfl

private def MVVert.toFin {m : ℕ} (v : MVVert m) : Fin ((2 * m ^ 3 + 2) + 2) :=
  ⟨v.toNat, v.toNat_lt⟩

private theorem MVVert.toFin_injective {m : ℕ} : Function.Injective (MVVert.toFin (m := m)) :=
  fun _ _ h => MVVert.toNat_injective (by simpa [MVVert.toFin] using congrArg Fin.val h)

/-- Partial clow sequences of length `ℓ.1 + 1` ending at `(h, u)` with clow-count parity `p`. -/
private structure PartialClowSeq (m : ℕ) (ℓ h u : Fin m) (p : Bool) where
  done : List (Clow m)
  done_pw : done.Pairwise (fun c₁ c₂ => c₁.head < c₂.head)
  done_lt : ∀ c ∈ done, c.head < h
  curTail : List (Fin m)
  cur_lt : ∀ v ∈ curTail, h < v
  cur_last : (h :: curTail).getLast (List.cons_ne_nil _ _) = u
  len_eq : (done.map Clow.len).sum + (curTail.length + 1) = ℓ.1 + 1
  par_eq : ((done.length + 1) % 2 == 1) = p
deriving DecidableEq

private noncomputable def PartialClowSeq.weight {m : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin m) (Fin m) R) {ℓ h u : Fin m} {p : Bool}
    (w : PartialClowSeq m ℓ h u p) : R :=
  (w.done.map (Clow.weight M)).prod * ((pairChain h w.curTail).map fun q => M q.1 q.2).prod

private instance instFinitePartialClowSeq {m : ℕ} (ℓ h u : Fin m) (p : Bool) :
    Finite (PartialClowSeq m ℓ h u p) := by
  have hinj : Function.Injective (fun w : PartialClowSeq m ℓ h u p =>
      (w.done.flatMap fun c => c.verts.map fun v => (c.head, v)) ++
        w.curTail.map fun v => (h, v)) := by
    intro w₁ w₂ heq
    -- Same argument as `clowSeq_finite`: the `(h, v)` suffix is separated from earlier `< h` heads!
    have hsplit : ∀ (P : Fin m × Fin m → Prop) (a₁ b₁ a₂ b₂ : List (Fin m × Fin m)),
        (∀ x ∈ a₁, P x) → (∀ x ∈ a₂, P x) →
        (∀ x ∈ b₁, ¬ P x) → (∀ x ∈ b₂, ¬ P x) →
        a₁ ++ b₁ = a₂ ++ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
      intro P a₁ b₁ a₂ b₂ ha₁ ha₂ hb₁ hb₂ h'
      induction a₁ generalizing a₂ with
      | nil =>
        cases a₂ with
        | nil => exact ⟨rfl, h'⟩
        | cons x xs =>
          have hmem : x ∈ b₁ := by
            rw [List.nil_append, List.cons_append] at h'
            rw [h']; exact List.mem_cons_self
          exact absurd (ha₂ x List.mem_cons_self) (hb₁ x hmem)
      | cons x xs ih =>
        cases a₂ with
        | nil =>
          have hmem : x ∈ b₂ := by
            rw [List.nil_append, List.cons_append] at h'
            rw [← h']; exact List.mem_cons_self
          exact absurd (ha₁ x List.mem_cons_self) (hb₂ x hmem)
        | cons y ys =>
          obtain ⟨rfl, h''⟩ := List.cons.inj h'
          obtain ⟨hxs, hbs⟩ := ih ys (fun z hz => ha₁ z (List.mem_cons_of_mem _ hz))
            (fun z hz => ha₂ z (List.mem_cons_of_mem _ hz)) h''
          exact ⟨congrArg _ hxs, hbs⟩
    have ⟨hd, ht⟩ := hsplit (fun q : Fin m × Fin m => q.1 < h)
      _ _ _ _
      (fun q hq => by
        obtain ⟨c, hc, hq'⟩ := List.mem_flatMap.mp hq
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq'
        exact w₁.done_lt c hc)
      (fun q hq => by
        obtain ⟨c, hc, hq'⟩ := List.mem_flatMap.mp hq
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq'
        exact w₂.done_lt c hc)
      (fun q hq => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq; exact lt_irrefl _)
      (fun q hq => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq; exact lt_irrefl _)
      heq
    have htail : w₁.curTail = w₂.curTail := by
      have := congrArg (List.map Prod.snd) ht; simpa [List.map_map] using this
    have hdone : w₁.done = w₂.done := by
      -- Same reconstruction as in `clowSeq_finite`:
      have hrec : ∀ (l₁ l₂ : List (Clow m)),
          l₁.Pairwise (fun c₁ c₂ => c₁.head < c₂.head) →
          l₂.Pairwise (fun c₁ c₂ => c₁.head < c₂.head) →
          (l₁.flatMap fun c => c.verts.map fun v => (c.head, v)) =
          (l₂.flatMap fun c => c.verts.map fun v => (c.head, v)) →
          l₁ = l₂ := by
        intro l₁ l₂ hp₁ hp₂ h'
        induction l₁ generalizing l₂ with
        | nil => cases l₂ with | nil => rfl | cons c₂ cs₂ => simp [Clow.verts_eq_cons] at h'
        | cons c₁ cs₁ ih =>
          cases l₂ with
          | nil => simp [Clow.verts_eq_cons] at h'
          | cons c₂ cs₂ =>
            simp only [List.flatMap_cons, Clow.verts_eq_cons, List.map_cons, List.cons_append] at h'
            have hh : c₁.head = c₂.head := congrArg Prod.fst (List.cons.inj h').1
            have ⟨hm, hr⟩ := hsplit (fun q : Fin m × Fin m => q.1 = c₁.head)
              (c₁.tail.map fun v => (c₁.head, v))
              (cs₁.flatMap fun c => (c.head, c.head) :: c.tail.map fun v => (c.head, v))
              (c₂.tail.map fun v => (c₂.head, v))
              (cs₂.flatMap fun c => (c.head, c.head) :: c.tail.map fun v => (c.head, v))
              (fun q hq => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq; rfl)
              (fun q hq => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq; exact hh.symm)
              (fun q hq => by
                obtain ⟨c, hc, hq'⟩ := List.mem_flatMap.mp hq
                rcases List.mem_cons.mp hq' with rfl | hq''
                · exact ne_of_gt ((List.pairwise_cons.mp hp₁).1 c hc)
                · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq''
                  exact ne_of_gt ((List.pairwise_cons.mp hp₁).1 c hc))
              (fun q hq => by
                obtain ⟨c, hc, hq'⟩ := List.mem_flatMap.mp hq
                rcases List.mem_cons.mp hq' with rfl | hq''
                · exact ne_of_gt (hh ▸ (List.pairwise_cons.mp hp₂).1 c hc)
                · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq''
                  exact ne_of_gt (hh ▸ (List.pairwise_cons.mp hp₂).1 c hc))
              (List.cons.inj h').2
            have ht' : c₁.tail = c₂.tail := by
              have := congrArg (List.map Prod.snd) hm; simpa [List.map_map] using this
            have hc' : c₁ = c₂ := by
              cases c₁; cases c₂; dsimp only at hh ht'; subst hh; subst ht'; rfl
            have hr' : (cs₁.flatMap fun c => c.verts.map fun v => (c.head, v)) =
                (cs₂.flatMap fun c => c.verts.map fun v => (c.head, v)) := by
              simpa only [Clow.verts_eq_cons, List.map_cons] using hr
            rw [hc', ih cs₂ (List.pairwise_cons.mp hp₁).2 (List.pairwise_cons.mp hp₂).2 hr']
      exact hrec w₁.done w₂.done w₁.done_pw w₂.done_pw hd
    cases w₁; cases w₂; dsimp only at hdone htail; subst hdone; subst htail; rfl
  have hlen : ∀ w : PartialClowSeq m ℓ h u p,
      ((w.done.flatMap fun c => c.verts.map fun v => (c.head, v)) ++
        w.curTail.map fun v => (h, v)).length = ℓ.1 := by
    intro w
    simp only [List.length_append, List.length_flatMap, List.length_map, Clow.verts_eq_cons,
      List.length_cons]
    have hlen_w := w.len_eq
    rw [show (w.done.map fun c => c.tail.length + 1) = w.done.map Clow.len from rfl]
    omega
  let emb : PartialClowSeq m ℓ h u p → (Fin ℓ.1 → Fin m × Fin m) := fun w i =>
    ((w.done.flatMap fun c => c.verts.map fun v => (c.head, v)) ++
      w.curTail.map fun v => (h, v)).get (i.cast (hlen w).symm)
  refine Finite.of_injective emb fun w₁ w₂ h' => hinj <|
    List.ext_getElem ((hlen w₁).trans (hlen w₂).symm) fun i hi _ => by
      simpa [emb] using congrFun h' ⟨i, (hlen w₁) ▸ hi⟩

private noncomputable instance instFintypePartialClowSeq {m : ℕ} (ℓ h u : Fin m) (p : Bool) :
    Fintype (PartialClowSeq m ℓ h u p) :=
  Fintype.ofFinite _

private theorem PartialClowSeq.heq_mk {m : ℕ} {ℓ h₁ h₂ u₁ u₂ : Fin m} {p : Bool}
    (w₁ : PartialClowSeq m ℓ h₁ u₁ p) (w₂ : PartialClowSeq m ℓ h₂ u₂ p)
    (hd : w₁.done = w₂.done) (ht : w₁.curTail = w₂.curTail) (hh : h₁ = h₂) (hu : u₁ = u₂) :
    HEq w₁ w₂ := by
  subst hh; subst hu; cases w₁; cases w₂; dsimp only at hd ht; subst hd; subst ht; rfl

private theorem sigma_sub_partialClowSeq_eq {m : ℕ} {ℓ : Fin m} {p : Bool} {P : Fin m → Prop}
    (a₁ a₂ : Subtype P) (u₁ u₂ : Fin m)
    (w₁ : PartialClowSeq m ℓ a₁.1 u₁ p) (w₂ : PartialClowSeq m ℓ a₂.1 u₂ p)
    (ha : a₁.1 = a₂.1) (hu : u₁ = u₂) (hd : w₁.done = w₂.done) (ht : w₁.curTail = w₂.curTail) :
    (⟨a₁, ⟨u₁, w₁⟩⟩ : Σ (a : Subtype P) (u : Fin m), PartialClowSeq m ℓ a.1 u p) =
      ⟨a₂, ⟨u₂, w₂⟩⟩ := by
  have ha' : a₁ = a₂ := Subtype.ext ha
  subst ha'; subst hu; cases w₁; cases w₂; dsimp only at hd ht; subst hd; subst ht; rfl

private theorem sigma_fin_partialClowSeq_eq {m : ℕ} {ℓ : Fin m} {p : Bool}
    (h₁ h₂ u₁ u₂ : Fin m)
    (w₁ : PartialClowSeq m ℓ h₁ u₁ p) (w₂ : PartialClowSeq m ℓ h₂ u₂ p)
    (hh : h₁ = h₂) (hu : u₁ = u₂) (hd : w₁.done = w₂.done) (ht : w₁.curTail = w₂.curTail) :
    (⟨h₁, ⟨u₁, w₁⟩⟩ : Σ (h : Fin m) (u : Fin m), PartialClowSeq m ℓ h u p) =
      ⟨h₂, ⟨u₂, w₂⟩⟩ := by
  subst hh; subst hu; cases w₁; cases w₂; dsimp only at hd ht; subst hd; subst ht; rfl

private theorem sum_map_flatMap {α β γ : Type*} [AddCommMonoid γ] (l : List α)
    (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem sum_map_nodup {α γ : Type*} [DecidableEq α] [AddCommMonoid γ] (l : List α)
    (hnd : l.Nodup) (g : α → γ) :
    (l.map g).sum = ∑ x ∈ l.toFinset, g x := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    simp [List.toFinset_cons, Finset.sum_insert (List.mem_toFinset.not.mpr hnd.1), ih hnd.2]

private theorem flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (hk : ∀ x ∈ l, (f x).length ≤ k) :
    (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := hk a List.mem_cons_self
    have h2 := ih (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    omega

private abbrev mvEdgesInit {K : Type u} [CommRing K] {σ : Type v} {m : ℕ} (hm : 0 < m) :
    List (ABPEdge K σ (2 * m ^ 3 + 2)) :=
  (List.finRange m).map fun h =>
    ⟨MVVert.source.toFin, (MVVert.state ⟨0, hm⟩ h h true).toFin,
      by simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def]; omega, .inr 1⟩

private abbrev mvExtEdge {K : Type u} [CommRing K] {σ : Type v} {m : ℕ}
    (lab : Fin m → Fin m → σ ⊕ K) (ℓ h u : Fin m) (p : Bool) (v : Fin m) :
    ABPEdge K σ (2 * m ^ 3 + 2) :=
  if hℓ : ℓ.1 + 1 < m then
    ⟨(MVVert.state ℓ h u p).toFin, (MVVert.state ⟨ℓ.1 + 1, hℓ⟩ h v p).toFin, by
      simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def]
      have h1 : ℓ.1 * m + h.1 < (ℓ.1 + 1) * m + h.1 := by nlinarith
      have hh := h.2; have hu := u.2; have hv := v.2
      have h2 : (ℓ.1 * m + h.1) * m + u.1 < ((ℓ.1 + 1) * m + h.1) * m + v.1 := by
        nlinarith
      cases p <;> simp <;> omega, lab u v⟩
  else
    ⟨MVVert.source.toFin, MVVert.sink.toFin,
      by simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def]; omega, .inr 0⟩

private abbrev mvEdgesExt {K : Type u} [CommRing K] {σ : Type v} {m : ℕ}
    (lab : Fin m → Fin m → σ ⊕ K) : List (ABPEdge K σ (2 * m ^ 3 + 2)) :=
  ((List.finRange m).filter (fun ℓ : Fin m => decide (ℓ.1 + 1 < m))).flatMap fun ℓ =>
    (List.finRange m).flatMap fun h =>
      (List.finRange m).flatMap fun u =>
        ([false, true]).flatMap fun p =>
          ((List.finRange m).filter (fun v : Fin m => decide (h < v))).map fun v =>
            mvExtEdge lab ℓ h u p v

private abbrev mvEdgesClose {K : Type u} [CommRing K] {σ : Type v} {m : ℕ}
    (lab : Fin m → Fin m → σ ⊕ K) : List (ABPEdge K σ (2 * m ^ 3 + 2)) :=
  ((List.finRange m).filter (fun ℓ : Fin m => decide (ℓ.1 + 1 < m))).flatMap fun ℓ =>
    (List.finRange m).flatMap fun h =>
      (List.finRange m).flatMap fun u =>
        ([false, true]).flatMap fun p =>
          ((List.finRange m).filter (fun h' : Fin m => decide (h < h'))).map fun h' =>
            if hℓ : ℓ.1 + 1 < m then
              ⟨(MVVert.state ℓ h u p).toFin, (MVVert.state ⟨ℓ.1 + 1, hℓ⟩ h' h' (!p)).toFin, by
                simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def]
                have h1 : ℓ.1 * m + h.1 < (ℓ.1 + 1) * m + h'.1 := by
                  have : h.1 < m := h.2; nlinarith
                have hu := u.2; have hh' := h'.2
                have h2 : (ℓ.1 * m + h.1) * m + u.1 < ((ℓ.1 + 1) * m + h'.1) * m + h'.1 := by
                  nlinarith
                cases p <;> simp <;> omega, lab u h⟩
            else
              ⟨MVVert.source.toFin, MVVert.sink.toFin,
                by simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def]; omega, .inr 0⟩

private abbrev mvEdgesFin {K : Type u} {σ : Type v} {m : ℕ} (hm : 0 < m)
    (lab : Fin m → Fin m → σ ⊕ K) : List (ABPEdge K σ (2 * m ^ 3 + 2)) :=
  (List.finRange m).flatMap fun h =>
    (List.finRange m).flatMap fun u =>
      ([false, true]).map fun p =>
        ⟨(MVVert.state ⟨m - 1, by omega⟩ h u p).toFin, (MVVert.presink p).toFin, by
          simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def]
          have hh := h.2; have hu := u.2
          have h1 : ((m - 1) * m + h.1) * m + u.1 < m ^ 3 := by
            have hsub : (m - 1) * m + h.1 < m * m := by
              rcases m with _ | m'
              · omega
              · simp only [Nat.add_sub_cancel]; nlinarith
            nlinarith [pow_succ m 2, sq m]
          cases p <;> simp <;> omega, lab u h⟩

private abbrev mvEdgesSink {K : Type u} [CommRing K] {σ : Type v} (m : ℕ) :
    List (ABPEdge K σ (2 * m ^ 3 + 2)) :=
  [⟨(MVVert.presink false).toFin, MVVert.sink.toFin,
      by simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def, Bool.false_eq_true, ↓reduceIte]
         omega, .inr ((-1 : K) ^ m)⟩,
   ⟨(MVVert.presink true).toFin, MVVert.sink.toFin,
      by simp only [MVVert.toFin, MVVert.toNat, Fin.lt_def, ↓reduceIte]; omega,
      .inr ((-1 : K) ^ (m + 1))⟩]

private abbrev mvABP {K : Type u} [CommRing K] {σ : Type v} {m : ℕ} (hm : 0 < m)
    (lab : Fin m → Fin m → σ ⊕ K) : ABP K σ :=
  ⟨2 * m ^ 3 + 2,
    mvEdgesInit hm ++ mvEdgesExt lab ++ mvEdgesClose lab ++ mvEdgesFin hm lab ++ mvEdgesSink m⟩

private theorem mvABP_state {K : Type u} [CommRing K] {σ : Type v} {m : ℕ} (hm : 0 < m)
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ K)) (lab : Fin m → Fin m → σ ⊕ K)
    (hlab : ∀ i j, abpLabelPoly (lab i j) = M i j) :
    ∀ (ℓ : Fin m) (h u : Fin m) (p : Bool),
      (mvABP hm lab).nodePoly (MVVert.state ℓ h u p).toFin =
        ∑ w : PartialClowSeq m ℓ h u p, w.weight M := by
    let P := mvABP hm lab
    let e_init := mvEdgesInit (K := K) (σ := σ) hm
    let e_ext := mvEdgesExt lab
    let e_close := mvEdgesClose lab
    let e_fin := mvEdgesFin hm lab
    let e_sink := mvEdgesSink (K := K) (σ := σ) m
    change ∀ (ℓ : Fin m) (h u : Fin m) (p : Bool),
      P.nodePoly (MVVert.state ℓ h u p).toFin = ∑ w : PartialClowSeq m ℓ h u p, w.weight M
    intro ⟨ℓ, hℓ⟩
    induction ℓ with
    | zero =>
      intro h u p
      have hne0 : (MVVert.state ⟨0, hℓ⟩ h u p).toFin ≠ 0 := by
        intro h0; exact absurd (congrArg Fin.val h0) (by simp [MVVert.toFin, MVVert.toNat])
      rw [P.nodePoly_of_ne_zero hne0]
      -- Only `e_init` can target layer `0`!
      have hother_zero :
          (((e_ext ++ e_close ++ e_fin ++ e_sink).map fun e =>
            if e.dst = (MVVert.state ⟨0, hℓ⟩ h u p).toFin then
              P.nodePoly e.src * abpLabelPoly e.label else 0)).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        split_ifs with hdst
        · exfalso
          simp only [List.mem_append] at he
          rcases he with ((he | he) | he) | he
          · simp only [e_ext, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
              true_and, decide_eq_true_eq] at he
            obtain ⟨ℓ', hℓ', _, _, _, _, _, _, rfl⟩ := he
            simp only [mvExtEdge, hℓ', ↓reduceDIte] at hdst
            cases MVVert.toFin_injective hdst
          · simp only [e_close, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
              true_and, decide_eq_true_eq] at he
            obtain ⟨ℓ', hℓ', _, _, _, _, _, _, rfl⟩ := he
            simp only [hℓ', ↓reduceDIte] at hdst
            cases MVVert.toFin_injective hdst
          · simp only [e_fin, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at he
            obtain ⟨_, _, _, _, rfl⟩ := he
            dsimp only at hdst
            cases MVVert.toFin_injective hdst
          · simp only [e_sink, List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl <;> (dsimp only at hdst; cases MVVert.toFin_injective hdst)
        · rfl
      have happ : P.edges = e_init ++ (e_ext ++ e_close ++ e_fin ++ e_sink) := by
        simp only [P, mvABP, e_init, e_ext, e_close, e_fin, e_sink, List.append_assoc]
      rw [happ, List.map_append, List.sum_append, hother_zero, add_zero]
      -- Compute `e_init` contribution: `1` if `h = u ∧ p = true`, else `0`!
      have hinit_val :
          ((e_init.map fun e => if e.dst = (MVVert.state ⟨0, hℓ⟩ h u p).toFin then
            P.nodePoly e.src * abpLabelPoly e.label else 0)).sum =
          if h = u ∧ p = true then 1 else 0 := by
        have hsrc0 : (MVVert.source (m := m)).toFin = 0 := Fin.ext rfl
        simp only [e_init, List.map_map, Function.comp_def, hsrc0, P.nodePoly_zero,
          abpLabelPoly_inr, one_mul, map_one]
        have hsum_f : ∀ (g : Fin m → MvPolynomial σ K),
            ((List.finRange m).map g).sum = ∑ i : Fin m, g i := by
          intro g; rw [← List.sum_ofFn]; congr 1
          apply List.ext_getElem (by simp); intro i _ _; simp
        rw [hsum_f]
        have hcond : ∀ h' : Fin m,
            ((MVVert.state ⟨0, hℓ⟩ h' h' true).toFin = (MVVert.state ⟨0, hℓ⟩ h u p).toFin) ↔
            (h' = h ∧ h = u ∧ p = true) := fun h' => by
          constructor
          · intro heq
            cases MVVert.toFin_injective heq; exact ⟨rfl, rfl, rfl⟩
          · rintro ⟨rfl, rfl, rfl⟩; rfl
        by_cases hup : h = u ∧ p = true
        · rcases hup with ⟨rfl, rfl⟩
          simp only [and_self, ↓reduceIte]
          rw [Finset.sum_eq_single h]
          · simp
          · intro h' _ hne'
            simp only [ite_eq_right_iff]
            intro heq
            exact absurd (MVVert.state.inj (MVVert.toFin_injective heq)).2.1 hne'
          · intro hc; exact absurd (Finset.mem_univ h) hc
        · simp only [hup, ↓reduceIte]
          refine Finset.sum_eq_zero fun h' _ => ?_
          simp [hcond, hup]
      rw [hinit_val]
      -- Match against `∑ w : PartialClowSeq m ⟨0, hℓ⟩ h u p, w.weight M`:
      by_cases hup : h = u ∧ p = true
      · rcases hup with ⟨rfl, rfl⟩
        simp only [and_self, ↓reduceIte]
        let w₀ : PartialClowSeq m ⟨0, hℓ⟩ h h true :=
          ⟨[], .nil, fun _ hc => by simp at hc, [], fun _ hc => by simp at hc, rfl, rfl, rfl⟩
        rw [Finset.sum_eq_single w₀]
        · simp [w₀, PartialClowSeq.weight]
        · intro w _ hne; exfalso; apply hne
          have hlen_w := w.len_eq
          have htl : w.curTail = [] := by
            cases ht : w.curTail with
            | nil => rfl
            | cons _ _ => simp [ht] at hlen_w; omega
          have hdn : w.done = [] := by
            cases hd : w.done with
            | nil => rfl
            | cons c cs => simp [hd, Clow.len_eq_length_tail_add_one] at hlen_w; omega
          cases w; simp_all [w₀]
        · intro hc; exact absurd (Finset.mem_univ w₀) hc
      · simp only [hup, ↓reduceIte]
        symm; refine Finset.sum_eq_zero fun w _ => ?_
        exfalso; apply hup
        have hlen_w := w.len_eq
        have htl : w.curTail = [] := by
          cases ht : w.curTail with
          | nil => rfl
          | cons _ _ => simp [ht] at hlen_w; omega
        have hdn : w.done = [] := by
          cases hd : w.done with
          | nil => rfl
          | cons c cs => simp [hd, Clow.len_eq_length_tail_add_one] at hlen_w; omega
        have hhu : h = u := by simpa [htl] using w.cur_last
        have hp : p = true := by simpa [hdn] using w.par_eq
        exact ⟨hhu, hp⟩
    | succ ℓ ih =>
      intro h u p
      have hne0 : (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin ≠ 0 := by
        intro h0; exact absurd (congrArg Fin.val h0) (by simp [MVVert.toFin, MVVert.toNat])
      rw [P.nodePoly_of_ne_zero hne0]
      -- Split incoming edges into `e_ext` (when `h < u`) and `e_close` (when `h = u`)!
      -- Both give clean bijections with `PartialClowSeq m ⟨ℓ + 1, hℓ⟩ h u p`!
      -- Let's evaluate the sum over `P.edges` and match with `PartialClowSeq` in one step.
      have hℓ_lt : ℓ < m := by omega
      have hℓ1_lt : ℓ + 1 < m := hℓ
      have hpairChain_snoc : ∀ (x : Fin m) (l : List (Fin m)) (y : Fin m),
          pairChain x (l ++ [y]) =
            pairChain x l ++ [((x :: l).getLast (List.cons_ne_nil _ _), y)] := by
        intro x l y
        induction l generalizing x with
        | nil => simp
        | cons z zs ih' =>
          simp only [List.cons_append, pairChain_cons, List.getLast_cons (List.cons_ne_nil z zs)]
          rw [ih' z]
      have hfinRange_toFinset : (List.finRange m).toFinset = Finset.univ := by
        ext x; simp
      have hfilter_toFinset : ∀ (q : Fin m → Bool),
          ((List.finRange m).filter q).toFinset = Finset.univ.filter (fun x => q x = true) := by
        intro q; ext x; simp
      have hbool_toFinset : ([false, true] : List Bool).toFinset = Finset.univ := by
        ext b; cases b <;> simp
      have hbool_nodup : ([false, true] : List Bool).Nodup := by decide
      have hsum_P :
          (P.edges.map fun e => if e.dst = (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin then
            P.nodePoly e.src * abpLabelPoly e.label else 0).sum =
          (if h < u then
            ∑ u' : Fin m, P.nodePoly (MVVert.state ⟨ℓ, hℓ_lt⟩ h u' p).toFin * M u' u
          else 0) +
          (if h = u then
            ∑ h' ∈ Finset.univ.filter (fun h' : Fin m => h' < h),
              ∑ u' : Fin m, P.nodePoly (MVVert.state ⟨ℓ, hℓ_lt⟩ h' u' (!p)).toFin * M u' h'
          else 0) := by
        -- Only `e_ext` and `e_close` at layer `ℓ` can hit `(ℓ + 1, h, u, p)`:
        have hzero_other : ∀ (l : List (ABPEdge K σ (2 * m ^ 3 + 2))),
            (∀ e ∈ l, e.dst ≠ (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin) →
            (l.map fun e => if e.dst = (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin then
              P.nodePoly e.src * abpLabelPoly e.label else 0).sum = 0 := by
          intro l hl
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
          simp [hl e he]
        have hz_init : ∀ e ∈ e_init, e.dst ≠ (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := by
          intro e he hdst
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
          dsimp only at hdst
          cases MVVert.toFin_injective hdst
        have hz_fin : ∀ e ∈ e_fin, e.dst ≠ (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := by
          intro e he hdst
          simp only [e_fin, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at he
          obtain ⟨_, _, _, _, rfl⟩ := he
          dsimp only at hdst
          cases MVVert.toFin_injective hdst
        have hz_sink : ∀ e ∈ e_sink, e.dst ≠ (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := by
          intro e he hdst
          simp only [e_sink, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl <;> (dsimp only at hdst; cases MVVert.toFin_injective hdst)
        change ((e_init ++ e_ext ++ e_close ++ e_fin ++ e_sink).map
          fun e : ABPEdge K σ (2 * m ^ 3 + 2) =>
            if e.dst = (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin then
              P.nodePoly e.src * abpLabelPoly e.label else 0).sum = _
        simp only [List.map_append, List.sum_append, hzero_other e_init hz_init,
          hzero_other e_fin hz_fin, hzero_other e_sink hz_sink, zero_add, add_zero]
        congr 1
        · -- `e_ext` term:
          simp only [e_ext, sum_map_flatMap, List.map_map, Function.comp_def]
          rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
          rw [Finset.sum_eq_single ⟨ℓ, hℓ_lt⟩]
          · rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
            rw [Finset.sum_eq_single h]
            · rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
              have hinner : ∀ u' : Fin m,
                  ((([false, true] : List Bool).map fun p' =>
                    ((((List.finRange m).filter fun v' => decide (h < v')).map fun v' =>
                      if (mvExtEdge lab ⟨ℓ, hℓ_lt⟩ h u' p' v').dst =
                          (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin
                      then P.nodePoly (mvExtEdge lab ⟨ℓ, hℓ_lt⟩ h u' p' v').src *
                          abpLabelPoly (mvExtEdge lab ⟨ℓ, hℓ_lt⟩ h u' p' v').label
                      else 0).sum)).sum) =
                  if h < u then P.nodePoly (MVVert.state ⟨ℓ, hℓ_lt⟩ h u' p).toFin * M u' u
                  else 0 := fun u' => by
                rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
                rw [Finset.sum_eq_single p]
                · rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
                  by_cases hhu : h < u
                  · simp only [hhu, ↓reduceIte]
                    rw [Finset.sum_eq_single u]
                    · simp only [mvExtEdge, hℓ1_lt, ↓reduceDIte, ↓reduceIte, hlab]
                    · intro v' _ hv'
                      simp only [mvExtEdge, hℓ1_lt, ↓reduceDIte]
                      have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h v' p).toFin ≠
                          (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst =>
                        hv' (by cases MVVert.toFin_injective hdst; rfl)
                      simp [hne]
                    · intro hc
                      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ u,
                        decide_eq_true hhu⟩) hc
                  · simp only [hhu, ↓reduceIte]
                    refine Finset.sum_eq_zero fun v' hv' => ?_
                    have hhv' : h < v' := of_decide_eq_true (Finset.mem_filter.mp hv').2
                    simp only [mvExtEdge, hℓ1_lt, ↓reduceDIte]
                    have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h v' p).toFin ≠
                        (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst => by
                      cases MVVert.toFin_injective hdst; exact hhu hhv'
                    simp [hne]
                · intro p' _ hp'
                  rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
                  refine Finset.sum_eq_zero fun v' _ => ?_
                  simp only [mvExtEdge, hℓ1_lt, ↓reduceDIte]
                  have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h v' p').toFin ≠
                      (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst =>
                    hp' (by cases MVVert.toFin_injective hdst; rfl)
                  simp [hne]
                · intro hc; exact absurd (Finset.mem_univ p) hc
              simp_rw [hinner]
              split_ifs <;> simp
            · intro h' _ hh'
              rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
              refine Finset.sum_eq_zero fun u' _ => ?_
              rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
              refine Finset.sum_eq_zero fun p' _ => ?_
              rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
              refine Finset.sum_eq_zero fun v' _ => ?_
              simp only [mvExtEdge, hℓ1_lt, ↓reduceDIte]
              have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h' v' p').toFin ≠
                  (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst =>
                hh' (by cases MVVert.toFin_injective hdst; rfl)
              simp [hne]
            · intro hc; exact absurd (Finset.mem_univ h) hc
          · intro ℓ' hℓ'_mem hℓ'_ne
            have hℓ'_lt : ℓ'.1 + 1 < m := of_decide_eq_true (Finset.mem_filter.mp hℓ'_mem).2
            rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
            refine Finset.sum_eq_zero fun h' _ => ?_
            rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
            refine Finset.sum_eq_zero fun u' _ => ?_
            rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
            refine Finset.sum_eq_zero fun p' _ => ?_
            rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
            refine Finset.sum_eq_zero fun v' _ => ?_
            simp only [mvExtEdge, hℓ'_lt, ↓reduceDIte]
            have hne : (MVVert.state ⟨ℓ'.1 + 1, hℓ'_lt⟩ h' v' p').toFin ≠
                (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst => by
              have hst := MVVert.toFin_injective hdst
              have h1 : ℓ'.1 + 1 = ℓ + 1 := congrArg Fin.val (MVVert.state.inj hst).1
              exact hℓ'_ne (Fin.ext (by dsimp only; omega))
            simp [hne]
          · intro hc
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (⟨ℓ, hℓ_lt⟩ : Fin m),
              decide_eq_true hℓ1_lt⟩) hc
        · -- `e_close` term:
          simp only [e_close, sum_map_flatMap, List.map_map, Function.comp_def]
          rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
          rw [Finset.sum_eq_single ⟨ℓ, hℓ_lt⟩]
          · rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
            by_cases hhu : h = u
            · subst hhu
              simp only [↓reduceIte]
              rw [← Finset.sum_subset (Finset.filter_subset (fun h' : Fin m => h' < h) Finset.univ)]
              · refine Finset.sum_congr rfl fun h' hh' => ?_
                have hh'lt : h' < h := (Finset.mem_filter.mp hh').2
                rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
                refine Finset.sum_congr rfl fun u' _ => ?_
                rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
                rw [Finset.sum_eq_single (!p)]
                · rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
                  rw [Finset.sum_eq_single h]
                  · simp only [hℓ1_lt, ↓reduceDIte, ↓reduceIte, Bool.not_not, hlab]
                  · intro h'' _ hh''
                    simp only [hℓ1_lt, ↓reduceDIte, Bool.not_not, ite_eq_right_iff]
                    intro hdst
                    exact absurd (MVVert.state.inj (MVVert.toFin_injective hdst)).2.1 hh''
                  · intro hc
                    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ h,
                      decide_eq_true hh'lt⟩) hc
                · intro p' _ hp'
                  rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
                  refine Finset.sum_eq_zero fun h'' _ => ?_
                  simp only [hℓ1_lt, ↓reduceDIte]
                  have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h'' h'' (!p')).toFin ≠
                      (MVVert.state ⟨ℓ + 1, hℓ⟩ h h p).toFin := fun hdst => by
                    cases MVVert.toFin_injective hdst
                    exact hp' (by simp)
                  simp [hne]
                · intro hc; exact absurd (Finset.mem_univ (!p)) hc
              · intro h' _ hh'_not
                have hh'_nlt : ¬ (h' < h) := fun hh'lt =>
                  hh'_not (Finset.mem_filter.mpr ⟨Finset.mem_univ h', hh'lt⟩)
                rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
                refine Finset.sum_eq_zero fun u' _ => ?_
                rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
                refine Finset.sum_eq_zero fun p' _ => ?_
                rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
                refine Finset.sum_eq_zero fun h'' hh'' => ?_
                have hh'lt'' : h' < h'' := of_decide_eq_true (Finset.mem_filter.mp hh'').2
                simp only [hℓ1_lt, ↓reduceDIte]
                have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h'' h'' (!p')).toFin ≠
                    (MVVert.state ⟨ℓ + 1, hℓ⟩ h h p).toFin := fun hdst => by
                  cases MVVert.toFin_injective hdst
                  exact hh'_nlt hh'lt''
                simp [hne]
            · simp only [hhu, ↓reduceIte]
              refine Finset.sum_eq_zero fun h' _ => ?_
              rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
              refine Finset.sum_eq_zero fun u' _ => ?_
              rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
              refine Finset.sum_eq_zero fun p' _ => ?_
              rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
              refine Finset.sum_eq_zero fun h'' _ => ?_
              simp only [hℓ1_lt, ↓reduceDIte]
              have hne : (MVVert.state ⟨ℓ + 1, hℓ1_lt⟩ h'' h'' (!p')).toFin ≠
                  (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst => by
                cases MVVert.toFin_injective hdst
                exact hhu rfl
              simp [hne]
          · intro ℓ' hℓ'_mem hℓ'_ne
            have hℓ'_lt : ℓ'.1 + 1 < m := of_decide_eq_true (Finset.mem_filter.mp hℓ'_mem).2
            rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
            refine Finset.sum_eq_zero fun h' _ => ?_
            rw [sum_map_nodup _ (List.nodup_finRange m), hfinRange_toFinset]
            refine Finset.sum_eq_zero fun u' _ => ?_
            rw [sum_map_nodup _ hbool_nodup, hbool_toFinset]
            refine Finset.sum_eq_zero fun p' _ => ?_
            rw [sum_map_nodup _ ((List.nodup_finRange m).filter _), hfilter_toFinset]
            refine Finset.sum_eq_zero fun h'' _ => ?_
            simp only [hℓ'_lt, ↓reduceDIte]
            have hne : (MVVert.state ⟨ℓ'.1 + 1, hℓ'_lt⟩ h'' h'' (!p')).toFin ≠
                (MVVert.state ⟨ℓ + 1, hℓ⟩ h u p).toFin := fun hdst => by
              have hst := MVVert.toFin_injective hdst
              have h1 : ℓ'.1 + 1 = ℓ + 1 := congrArg Fin.val (MVVert.state.inj hst).1
              exact hℓ'_ne (Fin.ext (by dsimp only; omega))
            simp [hne]
          · intro hc
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (⟨ℓ, hℓ_lt⟩ : Fin m),
              decide_eq_true hℓ1_lt⟩) hc
      rw [hsum_P]
      -- Match against `∑ w : PartialClowSeq, w.weight M` via `lt_trichotomy h u`:
      rcases lt_trichotomy h u with hhu | rfl | huh
      · -- Case `h < u`: `e_ext` bijects with `PartialClowSeq` (every `w` has `w.curTail ≠ []`).
        simp only [hhu, ne_of_lt hhu, ↓reduceIte, add_zero]
        simp_rw [ih hℓ_lt, Finset.sum_mul]
        rw [← Fintype.sum_sigma (f := fun q : Σ u' : Fin m, PartialClowSeq m ⟨ℓ, hℓ_lt⟩ h u' p =>
          q.2.weight M * M q.1 u)]
        let e : (Σ u' : Fin m, PartialClowSeq m ⟨ℓ, hℓ_lt⟩ h u' p) ≃
            PartialClowSeq m ⟨ℓ + 1, hℓ⟩ h u p :=
          { toFun := fun ⟨u', w⟩ =>
              ⟨w.done, w.done_pw, w.done_lt, w.curTail ++ [u],
                fun v hv => by
                  rcases List.mem_append.mp hv with hv | hv
                  · exact w.cur_lt v hv
                  · rw [List.mem_singleton.mp hv]; exact hhu,
                by simp, by have hlen := w.len_eq; simp at hlen ⊢; omega, w.par_eq⟩
            invFun := fun w =>
              have hne : w.curTail ≠ [] := by
                intro hnil
                exact ne_of_lt hhu (by simpa [hnil] using w.cur_last)
              have hlast : w.curTail.getLast hne = u := by
                have := w.cur_last
                rwa [List.getLast_cons hne] at this
              let pref := w.curTail.dropLast
              let u' := (h :: pref).getLast (List.cons_ne_nil _ _)
              ⟨u', ⟨w.done, w.done_pw, w.done_lt, pref,
                fun v hv => w.cur_lt v (List.dropLast_subset _ hv),
                rfl,
                by
                  have hlen := w.len_eq; dsimp only at hlen ⊢
                  have hdl : pref.length + 1 = w.curTail.length := by
                    have htmp := congrArg List.length (List.dropLast_append_getLast hne)
                    simp only [List.length_append, List.length_singleton] at htmp
                    exact htmp
                  omega,
                w.par_eq⟩⟩
            left_inv := fun ⟨u', w⟩ => by
              have hdl : (w.curTail ++ [u]).dropLast = w.curTail := List.dropLast_concat
              have hu' : (h :: w.curTail).getLast (List.cons_ne_nil _ _) = u' := w.cur_last
              have hidx : (h :: (w.curTail ++ [u]).dropLast).getLast (List.cons_ne_nil _ _) =
                  u' := by rw [hdl]; exact hu'
              refine Sigma.ext hidx ?_
              exact PartialClowSeq.heq_mk _ w rfl hdl rfl hidx
            right_inv := fun w => by
              have hne : w.curTail ≠ [] := by
                intro hnil; exact ne_of_lt hhu (by simpa [hnil] using w.cur_last)
              have hlast : w.curTail.getLast hne = u := by
                have := w.cur_last; rwa [List.getLast_cons hne] at this
              have hrec : w.curTail.dropLast ++ [u] = w.curTail := by
                have htmp := List.dropLast_append_getLast hne
                rwa [hlast] at htmp
              cases w; simp [hrec] }
        refine (Fintype.sum_equiv e _ _ fun ⟨u', w⟩ => ?_)
        simp only [e, Equiv.coe_fn_mk, PartialClowSeq.weight, hpairChain_snoc, List.map_append,
          List.prod_append, List.map_singleton, List.prod_singleton, w.cur_last]
        ring
      · -- Case `h = u`: `e_close` bijects with `PartialClowSeq` (every `w` has `w.curTail = []`).
        simp only [lt_irrefl, ↓reduceIte, zero_add]
        simp_rw [ih hℓ_lt, Finset.sum_mul]
        have hsub :
            (∑ h' ∈ Finset.univ.filter (fun h' : Fin m => h' < h),
              ∑ u' : Fin m, ∑ w : PartialClowSeq m ⟨ℓ, hℓ_lt⟩ h' u' (!p), w.weight M * M u' h') =
            ∑ a : {x : Fin m // x < h},
              ∑ u' : Fin m, ∑ w : PartialClowSeq m ⟨ℓ, hℓ_lt⟩ a.1 u' (!p),
                w.weight M * M u' a.1 :=
          Finset.sum_subtype _ (fun _ => by simp) _
        rw [hsub]
        have hsig1 : ∀ a : {x : Fin m // x < h},
            (∑ u' : Fin m, ∑ w : PartialClowSeq m ⟨ℓ, hℓ_lt⟩ a.1 u' (!p),
              w.weight M * M u' a.1) =
            ∑ q : Σ u' : Fin m, PartialClowSeq m ⟨ℓ, hℓ_lt⟩ a.1 u' (!p),
              q.2.weight M * M q.1 a.1 :=
          fun a => (Fintype.sum_sigma fun q : Σ u' : Fin m,
            PartialClowSeq m ⟨ℓ, hℓ_lt⟩ a.1 u' (!p) => q.2.weight M * M q.1 a.1).symm
        simp_rw [hsig1]
        rw [← Fintype.sum_sigma (f := fun r : (Σ (a : {x : Fin m // x < h}) (u' : Fin m),
            PartialClowSeq m ⟨ℓ, hℓ_lt⟩ a.1 u' (!p)) => r.2.2.weight M * M r.2.1 r.1.1)]
        let e : (Σ (h' : {x : Fin m // x < h}) (u' : Fin m),
              PartialClowSeq m ⟨ℓ, hℓ_lt⟩ h'.1 u' (!p)) ≃
            PartialClowSeq m ⟨ℓ + 1, hℓ⟩ h h p :=
          { toFun := fun ⟨⟨h', hh'⟩, u', w⟩ =>
              let cLast : Clow m := ⟨h', w.curTail, w.cur_lt⟩
              ⟨w.done ++ [cLast],
                List.pairwise_append.mpr ⟨w.done_pw, List.pairwise_singleton _ _,
                  fun c hc c' hc' => by
                    rw [List.mem_singleton.mp hc']; exact w.done_lt c hc⟩,
                fun c hc => by
                  rcases List.mem_append.mp hc with hc | hc
                  · exact lt_trans (w.done_lt c hc) hh'
                  · rw [List.mem_singleton.mp hc]; exact hh',
                [], fun _ hv => by simp at hv, rfl,
                by
                  have hlen := w.len_eq; dsimp only at hlen ⊢
                  simp only [List.map_append, List.sum_append, List.map_singleton,
                    List.sum_singleton, List.length_nil, cLast, Clow.len_mk]
                  omega,
                by
                  have := w.par_eq
                  simp only [List.length_append, List.length_singleton]
                  have hmod : (w.done.length + 1 + 1) % 2 = 1 - (w.done.length + 1) % 2 := by omega
                  cases hp : ((w.done.length + 1) % 2 == 1) <;> simp_all⟩
            invFun := fun w =>
              have htail : w.curTail = [] := by
                cases ht : w.curTail with
                | nil => rfl
                | cons z zs =>
                  exfalso
                  have hlast := w.cur_last
                  have hmem : h ∈ w.curTail := by
                    rw [ht] at hlast ⊢
                    rw [List.getLast_cons (List.cons_ne_nil z zs)] at hlast
                    exact hlast ▸ List.getLast_mem (List.cons_ne_nil z zs)
                  exact lt_irrefl h (w.cur_lt h hmem)
              have hne : w.done ≠ [] := by
                intro hnil
                have := w.len_eq; simp [hnil, htail] at this
              let cLast := w.done.getLast hne
              let init := w.done.dropLast
              let u' := (cLast.head :: cLast.tail).getLast (List.cons_ne_nil _ _)
              have hinit_app : init ++ [cLast] = w.done := List.dropLast_append_getLast hne
              have hcLast_mem : cLast ∈ w.done := List.getLast_mem hne
              have hpw_app : (init ++ [cLast]).Pairwise (fun c₁ c₂ => c₁.head < c₂.head) := by
                rw [hinit_app]; exact w.done_pw
              ⟨⟨cLast.head, w.done_lt cLast hcLast_mem⟩, u',
                ⟨init, (List.pairwise_append.mp hpw_app).1,
                  fun c hc => (List.pairwise_append.mp hpw_app).2.2 c hc cLast List.mem_cons_self,
                  cLast.tail, cLast.lt_tail, rfl,
                  by
                    have hlen := w.len_eq; dsimp only at hlen ⊢
                    rw [← hinit_app] at hlen
                    simp only [List.map_append, List.sum_append, List.map_singleton,
                      List.sum_singleton, htail, List.length_nil,
                      Clow.len_eq_length_tail_add_one] at hlen
                    omega,
                  by
                    have hpar := w.par_eq
                    have hdl : w.done.length = init.length + 1 := by
                      have := congrArg List.length hinit_app; simp at this; exact this.symm
                    rw [hdl] at hpar
                    cases hp : p <;> simp_all <;> omega⟩⟩
            left_inv := fun ⟨⟨h', hh'⟩, u', w⟩ => by
              let cLast : Clow m := ⟨h', w.curTail, w.cur_lt⟩
              have hne : w.done ++ [cLast] ≠ [] :=
                List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
              have hlast : (w.done ++ [cLast]).getLast hne = cLast := List.getLast_concat
              have hdl : (w.done ++ [cLast]).dropLast = w.done := List.dropLast_concat
              have hu' : (cLast.head :: cLast.tail).getLast (List.cons_ne_nil _ _) = u' :=
                w.cur_last
              have hhead : ((w.done ++ [cLast]).getLast hne).head = h' := by rw [hlast]
              have htail_eq : ((w.done ++ [cLast]).getLast hne).tail = w.curTail := by rw [hlast]
              have hu_eq : (((w.done ++ [cLast]).getLast hne).head ::
                  ((w.done ++ [cLast]).getLast hne).tail).getLast (List.cons_ne_nil _ _) = u' := by
                rw [hlast]; exact hu'
              exact sigma_sub_partialClowSeq_eq _ _ _ _ _ w hhead hu_eq hdl htail_eq
            right_inv := fun w => by
              have htail : w.curTail = [] := by
                cases ht : w.curTail with
                | nil => rfl
                | cons z zs =>
                  exfalso
                  have hlast := w.cur_last
                  have hmem : h ∈ w.curTail := by
                    rw [ht] at hlast ⊢
                    rw [List.getLast_cons (List.cons_ne_nil z zs)] at hlast
                    exact hlast ▸ List.getLast_mem (List.cons_ne_nil z zs)
                  exact lt_irrefl h (w.cur_lt h hmem)
              have hne : w.done ≠ [] := by
                intro hnil; have := w.len_eq; simp [hnil, htail] at this
              have hrec : w.done.dropLast ++ [w.done.getLast hne] = w.done :=
                List.dropLast_append_getLast hne
              cases w; simp_all }
        refine (Fintype.sum_equiv e _ _ fun ⟨⟨h', hh'⟩, u', w⟩ => ?_)
        simp only [e, Equiv.coe_fn_mk, PartialClowSeq.weight, List.map_append, List.prod_append,
          List.map_singleton, List.prod_singleton, pairChain_nil, List.map_nil, List.prod_nil,
          mul_one, Clow.weight_eq_prod_edges, Clow.edges_eq_cycleEdges_verts, Clow.verts_mk,
          cycleEdges_cons_eq_pairChain, hpairChain_snoc, w.cur_last]
        ring
      · -- Case `u < h`: both `if`s are false (`0`), and `PartialClowSeq` is empty.
        simp only [not_lt_of_gt huh, ne_of_gt huh, ↓reduceIte, add_zero]
        symm
        refine Finset.sum_eq_zero fun w _ => ?_
        exfalso
        have hlast := w.cur_last
        cases ht : w.curTail with
        | nil => exact ne_of_gt huh (by simpa [ht] using hlast)
        | cons z zs =>
          have hmem : u ∈ w.curTail := by
            rw [ht] at hlast ⊢
            rw [List.getLast_cons (List.cons_ne_nil z zs)] at hlast
            exact hlast ▸ List.getLast_mem (List.cons_ne_nil z zs)
          exact lt_asymm huh (w.cur_lt u hmem)

private theorem mvABP_presink {K : Type u} [CommRing K] {σ : Type v} {m : ℕ} (hm : 0 < m)
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ K)) (lab : Fin m → Fin m → σ ⊕ K)
    (hlab : ∀ i j, abpLabelPoly (lab i j) = M i j) (p : Bool) :
    let _ : Fintype (ClowSeq m) := @Fintype.ofFinite _ (clowSeq_finite m)
    (mvABP hm lab).nodePoly (MVVert.presink p).toFin =
      ∑ w ∈ Finset.univ.filter (fun w : ClowSeq m => (w.clows.length % 2 == 1) = p),
        (w.clows.map (Clow.weight M)).prod := by
    let _ : Fintype (ClowSeq m) := @Fintype.ofFinite _ (clowSeq_finite m)
    let P := mvABP hm lab
    change P.nodePoly (MVVert.presink p).toFin = _
    have hstate : ∀ (ℓ : Fin m) (h u : Fin m) (p : Bool),
        P.nodePoly (MVVert.state ℓ h u p).toFin = ∑ w : PartialClowSeq m ℓ h u p, w.weight M :=
      mvABP_state hm M lab hlab
    have hpairChain_snoc2 : ∀ (x : Fin m) (l : List (Fin m)) (y : Fin m),
        pairChain x (l ++ [y]) =
          pairChain x l ++ [((x :: l).getLast (List.cons_ne_nil _ _), y)] := by
      intro x l y
      induction l generalizing x with
      | nil => simp
      | cons z zs ih' =>
        simp only [List.cons_append, pairChain_cons, List.getLast_cons (List.cons_ne_nil z zs)]
        rw [ih' z]
    have hne0 : (MVVert.presink (m := m) p).toFin ≠ 0 := by
      intro h0; exact absurd (congrArg Fin.val h0) (by simp [MVVert.toFin, MVVert.toNat])
    rw [P.nodePoly_of_ne_zero hne0]
    have hzero_other : ∀ (l : List (ABPEdge K σ (2 * m ^ 3 + 2))),
        (∀ e ∈ l, e.dst ≠ (MVVert.presink p).toFin) →
        (l.map fun e => if e.dst = (MVVert.presink p).toFin then
          P.nodePoly e.src * abpLabelPoly e.label else 0).sum = 0 := by
      intro l hl
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      simp [hl e he]
    let e_init := mvEdgesInit (K := K) (σ := σ) hm
    let e_ext := mvEdgesExt lab
    let e_close := mvEdgesClose lab
    let e_fin := mvEdgesFin hm lab
    have hz_init : ∀ e ∈ e_init, e.dst ≠ (MVVert.presink p).toFin := by
      intro e he hdst; obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
      dsimp only at hdst; cases MVVert.toFin_injective hdst
    have hz_ext : ∀ e ∈ e_ext, e.dst ≠ (MVVert.presink p).toFin := by
      intro e he hdst
      simp only [e_ext, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and, decide_eq_true_eq] at he
      obtain ⟨ℓ', hℓ', _, _, _, _, _, _, rfl⟩ := he
      simp only [mvExtEdge, hℓ', ↓reduceDIte] at hdst
      cases MVVert.toFin_injective hdst
    have hz_close : ∀ e ∈ e_close, e.dst ≠ (MVVert.presink p).toFin := by
      intro e he hdst
      simp only [e_close, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and, decide_eq_true_eq] at he
      obtain ⟨ℓ', hℓ', _, _, _, _, _, _, rfl⟩ := he
      simp only [hℓ', ↓reduceDIte] at hdst
      cases MVVert.toFin_injective hdst
    have hz_sink : ∀ e ∈ mvEdgesSink (K := K) (σ := σ) m, e.dst ≠ (MVVert.presink p).toFin := by
      intro e he hdst
      simp only [mvEdgesSink, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> (dsimp only at hdst; cases MVVert.toFin_injective hdst)
    change ((e_init ++ e_ext ++ e_close ++ e_fin ++ mvEdgesSink m).map
      fun e : ABPEdge K σ (2 * m ^ 3 + 2) =>
        if e.dst = (MVVert.presink p).toFin then
          P.nodePoly e.src * abpLabelPoly e.label else 0).sum = _
    simp only [List.map_append, List.sum_append, hzero_other e_init hz_init,
      hzero_other e_ext hz_ext, hzero_other e_close hz_close, hzero_other _ hz_sink,
      zero_add, add_zero]
    have hm1 : m - 1 < m := by omega
    simp only [e_fin, sum_map_flatMap, List.map_map, Function.comp_def]
    rw [sum_map_nodup _ (List.nodup_finRange m)]
    have hfr : (List.finRange m).toFinset = Finset.univ := by ext x; simp
    have hbn : ([false, true] : List Bool).Nodup := by decide
    have hbf : ([false, true] : List Bool).toFinset = Finset.univ := by ext b; cases b <;> simp
    rw [hfr]
    have hstep : ∀ h : Fin m,
        (((List.finRange m).map fun u =>
          (([false, true] : List Bool).map fun p' =>
            if (MVVert.presink (m := m) p').toFin = (MVVert.presink (m := m) p).toFin then
              P.nodePoly (MVVert.state ⟨m - 1, hm1⟩ h u p').toFin * abpLabelPoly (lab u h)
            else 0).sum).sum) =
        ∑ u : Fin m, P.nodePoly (MVVert.state ⟨m - 1, hm1⟩ h u p).toFin * M u h := fun h => by
      rw [sum_map_nodup _ (List.nodup_finRange m), hfr]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [sum_map_nodup _ hbn, hbf, Finset.sum_eq_single p]
      · simp [hlab]
      · intro p' _ hp'
        have hne : (MVVert.presink (m := m) p').toFin ≠ (MVVert.presink (m := m) p).toFin :=
          fun hdst => hp' (by cases MVVert.toFin_injective hdst; rfl)
        simp [hne]
      · intro hc; exact absurd (Finset.mem_univ p) hc
    simp_rw [hstep, hstate ⟨m - 1, hm1⟩, Finset.sum_mul]
    have hsig1 : ∀ h : Fin m,
        (∑ u : Fin m, ∑ w : PartialClowSeq m ⟨m - 1, hm1⟩ h u p, w.weight M * M u h) =
        ∑ q : Σ u : Fin m, PartialClowSeq m ⟨m - 1, hm1⟩ h u p, q.2.weight M * M q.1 h :=
      fun h => (Fintype.sum_sigma fun q : Σ u : Fin m,
        PartialClowSeq m ⟨m - 1, hm1⟩ h u p => q.2.weight M * M q.1 h).symm
    simp_rw [hsig1]
    rw [← Fintype.sum_sigma (f := fun r : (Σ (h : Fin m) (u : Fin m),
        PartialClowSeq m ⟨m - 1, hm1⟩ h u p) => r.2.2.weight M * M r.2.1 r.1)]
    have hsub :
        (∑ w ∈ Finset.univ.filter (fun w : ClowSeq m => (w.clows.length % 2 == 1) = p),
          (w.clows.map (Clow.weight M)).prod) =
        ∑ w : {w : ClowSeq m // (w.clows.length % 2 == 1) = p},
          (w.1.clows.map (Clow.weight M)).prod :=
      Finset.sum_subtype _ (fun _ => by simp) _
    rw [hsub]
    let e : (Σ (h : Fin m) (u : Fin m), PartialClowSeq m ⟨m - 1, hm1⟩ h u p) ≃
        {w : ClowSeq m // (w.clows.length % 2 == 1) = p} :=
      { toFun := fun ⟨h, u, w⟩ =>
          let cLast : Clow m := ⟨h, w.curTail, w.cur_lt⟩
          ⟨⟨w.done ++ [cLast],
            List.pairwise_append.mpr ⟨w.done_pw, List.pairwise_singleton _ _, fun c hc c' hc' => by
              rw [List.mem_singleton.mp hc']; exact w.done_lt c hc⟩,
            by
              have hlen := w.len_eq; dsimp only at hlen ⊢
              simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
                cLast, Clow.len_mk]
              omega⟩,
            by simpa using w.par_eq⟩
        invFun := fun ⟨w, hw⟩ =>
          have hne : w.clows ≠ [] := by
            intro hnil; have := w.len_sum; simp [hnil] at this; omega
          let cLast := w.clows.getLast hne
          let init := w.clows.dropLast
          let u := (cLast.head :: cLast.tail).getLast (List.cons_ne_nil _ _)
          have hinit_app : init ++ [cLast] = w.clows := List.dropLast_append_getLast hne
          have hpw_app : (init ++ [cLast]).Pairwise (fun c₁ c₂ => c₁.head < c₂.head) := by
            rw [hinit_app]; exact w.heads_strict
          ⟨cLast.head, u,
            ⟨init, (List.pairwise_append.mp hpw_app).1,
              fun c hc => (List.pairwise_append.mp hpw_app).2.2 c hc cLast List.mem_cons_self,
              cLast.tail, cLast.lt_tail, rfl,
              by
                have hlen := w.len_sum; dsimp only at hlen ⊢
                rw [← hinit_app] at hlen
                simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
                  Clow.len_eq_length_tail_add_one] at hlen
                omega,
              by
                have hdl : w.clows.length = init.length + 1 := by
                  have := congrArg List.length hinit_app; simp at this; exact this.symm
                simpa [hdl] using hw⟩⟩
        left_inv := fun ⟨h, u, w⟩ => by
          let cLast : Clow m := ⟨h, w.curTail, w.cur_lt⟩
          have hne : w.done ++ [cLast] ≠ [] :=
            List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
          have hlast : (w.done ++ [cLast]).getLast hne = cLast := List.getLast_concat
          have hdl : (w.done ++ [cLast]).dropLast = w.done := List.dropLast_concat
          have hu : (cLast.head :: cLast.tail).getLast (List.cons_ne_nil _ _) = u := w.cur_last
          have hhead : ((w.done ++ [cLast]).getLast hne).head = h := by rw [hlast]
          have htail_eq : ((w.done ++ [cLast]).getLast hne).tail = w.curTail := by rw [hlast]
          have hu_eq : (((w.done ++ [cLast]).getLast hne).head ::
              ((w.done ++ [cLast]).getLast hne).tail).getLast (List.cons_ne_nil _ _) = u := by
            rw [hlast]; exact hu
          exact sigma_fin_partialClowSeq_eq _ _ _ _ _ w hhead hu_eq hdl htail_eq
        right_inv := fun ⟨w, hw⟩ => by
          have hne : w.clows ≠ [] := by
            intro hnil; have := w.len_sum; simp [hnil] at this; omega
          have hrec : w.clows.dropLast ++ [w.clows.getLast hne] = w.clows :=
            List.dropLast_append_getLast hne
          apply Subtype.ext
          cases w; simp [hrec] }
    refine Fintype.sum_equiv e _ _ fun ⟨h, u, w⟩ => ?_
    simp only [e, Equiv.coe_fn_mk, PartialClowSeq.weight, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, Clow.weight_eq_prod_edges,
      Clow.edges_eq_cycleEdges_verts, Clow.verts_mk, cycleEdges_cons_eq_pairChain,
      hpairChain_snoc2, w.cur_last]
    ring
private theorem mvABP_poly {K : Type u} [CommRing K] {σ : Type v} {m : ℕ} (hm : 0 < m)
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ K)) (lab : Fin m → Fin m → σ ⊕ K)
    (hlab : ∀ i j, abpLabelPoly (lab i j) = M i j) :
    (mvABP hm lab).poly = M.det := by
    let _ : Fintype (ClowSeq m) := @Fintype.ofFinite _ (clowSeq_finite m)
    let P := mvABP hm lab
    change P.poly = M.det
    have hpresink : ∀ p : Bool,
        P.nodePoly (MVVert.presink p).toFin =
          ∑ w ∈ Finset.univ.filter (fun w : ClowSeq m => (w.clows.length % 2 == 1) = p),
            (w.clows.map (Clow.weight M)).prod :=
      mvABP_presink hm M lab hlab
    have hsink_eq : Fin.last (P.innerVerts + 1) = MVVert.sink.toFin :=
      Fin.ext (by simp [P, MVVert.toFin, MVVert.toNat]; omega)
    have hsink_ne0 : (MVVert.sink (m := m)).toFin ≠ 0 := by
      intro h0; exact absurd (congrArg Fin.val h0) (by simp [MVVert.toFin, MVVert.toNat])
    rw [ABP.poly_eq_nodePoly_last, hsink_eq, P.nodePoly_of_ne_zero hsink_ne0]
    have hzero_other : ∀ (l : List (ABPEdge K σ (2 * m ^ 3 + 2))),
        (∀ e ∈ l, e.dst ≠ MVVert.sink.toFin) →
        (l.map fun e => if e.dst = MVVert.sink.toFin then
          P.nodePoly e.src * abpLabelPoly e.label else 0).sum = 0 := by
      intro l hl
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      simp [hl e he]
    have hz_init : ∀ e ∈ mvEdgesInit (K := K) (σ := σ) hm, e.dst ≠ MVVert.sink.toFin := by
      intro e he hdst; obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
      dsimp only at hdst; cases MVVert.toFin_injective hdst
    have hz_ext : ∀ e ∈ mvEdgesExt lab, e.dst ≠ MVVert.sink.toFin := by
      intro e he hdst
      simp only [mvEdgesExt, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and, decide_eq_true_eq] at he
      obtain ⟨ℓ', hℓ', _, _, _, _, _, _, rfl⟩ := he
      simp only [mvExtEdge, hℓ', ↓reduceDIte] at hdst
      cases MVVert.toFin_injective hdst
    have hz_close : ∀ e ∈ mvEdgesClose lab, e.dst ≠ MVVert.sink.toFin := by
      intro e he hdst
      simp only [mvEdgesClose, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and, decide_eq_true_eq] at he
      obtain ⟨ℓ', hℓ', _, _, _, _, _, _, rfl⟩ := he
      simp only [hℓ', ↓reduceDIte] at hdst
      cases MVVert.toFin_injective hdst
    have hz_fin : ∀ e ∈ mvEdgesFin hm lab, e.dst ≠ MVVert.sink.toFin := by
      intro e he hdst
      simp only [mvEdgesFin, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at he
      obtain ⟨_, _, _, _, rfl⟩ := he
      dsimp only at hdst; cases MVVert.toFin_injective hdst
    change ((mvEdgesInit hm ++ mvEdgesExt lab ++ mvEdgesClose lab ++ mvEdgesFin hm lab ++
        mvEdgesSink m).map
      fun e : ABPEdge K σ (2 * m ^ 3 + 2) =>
        if e.dst = MVVert.sink.toFin then
          P.nodePoly e.src * abpLabelPoly e.label else 0).sum = _
    simp only [List.map_append, List.sum_append, hzero_other _ hz_init,
      hzero_other _ hz_ext, hzero_other _ hz_close, hzero_other _ hz_fin,
      zero_add, add_zero]
    simp only [mvEdgesSink, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
      abpLabelPoly_inr, add_zero, hpresink false, hpresink true, Finset.sum_mul]
    rw [← sum_clowSeq_eq_det M,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun w : ClowSeq m => (w.clows.length % 2 == 1) = true)]
    have hflt_eq :
        Finset.univ.filter (fun w : ClowSeq m => ¬ ((w.clows.length % 2 == 1) = true)) =
        Finset.univ.filter (fun w : ClowSeq m => (w.clows.length % 2 == 1) = false) := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases (w.clows.length % 2 == 1) <;> simp
    rw [hflt_eq, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun w hw => ?_
      have hpar : w.clows.length % 2 = 1 := by
        have h2 := (Finset.mem_filter.mp hw).2
        rcases Nat.mod_two_eq_zero_or_one w.clows.length with h0 | h1
        · simp [h0] at h2
        · exact h1
      simp only [ClowSeq.signedWeight_eq, map_pow, map_neg, map_one]
      rw [pow_add (-1) m w.clows.length, Odd.neg_one_pow (Nat.odd_iff.mpr hpar),
        pow_succ, mul_comm]
    · refine Finset.sum_congr rfl fun w hw => ?_
      have hpar : w.clows.length % 2 = 0 := by
        have h2 := (Finset.mem_filter.mp hw).2
        rcases Nat.mod_two_eq_zero_or_one w.clows.length with h0 | h1
        · exact h0
        · simp [h1] at h2
      simp only [ClowSeq.signedWeight_eq, map_pow, map_neg, map_one]
      rw [pow_add, Even.neg_one_pow (Nat.even_iff.mpr hpar), mul_one, mul_comm]

private theorem mvABP_size {K : Type u} [CommRing K] {σ : Type v} {m : ℕ} (hm : 0 < m)
    (lab : Fin m → Fin m → σ ⊕ K) :
    (mvABP hm lab).size ≤ 6 * m ^ 4 + 10 := by
    have he_init : (mvEdgesInit (K := K) (σ := σ) hm).length = m := by simp [mvEdgesInit]
    let e_ext := mvEdgesExt lab
    let e_close := mvEdgesClose lab
    let e_fin := mvEdgesFin hm lab
    let e_sink := mvEdgesSink (K := K) (σ := σ) m
    let P := mvABP hm lab
    change P.size ≤ 6 * m ^ 4 + 10
    have he_ext : e_ext.length ≤ 2 * m ^ 4 := by
      have h1 : e_ext.length ≤
          ((List.finRange m).filter
            (fun ℓ : Fin m => decide (ℓ.1 + 1 < m))).length * (2 * m ^ 3) := by
        refine flatMap_length_le _ _ (2 * m ^ 3) fun ℓ _ => ?_
        refine (flatMap_length_le _ _ (2 * m ^ 2) fun h _ => ?_).trans
          (by simp [pow_succ]; ring_nf; exact le_rfl)
        refine (flatMap_length_le _ _ (2 * m) fun u _ => ?_).trans
          (by simp [pow_two]; ring_nf; exact le_rfl)
        refine (flatMap_length_le _ _ m fun p _ => ?_).trans (by simp)
        rw [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
      have hflt : ((List.finRange m).filter
          (fun ℓ : Fin m => decide (ℓ.1 + 1 < m))).length ≤ m :=
        (List.length_filter_le _ _).trans (by simp)
      calc e_ext.length ≤ _ := h1
        _ ≤ m * (2 * m ^ 3) := Nat.mul_le_mul_right _ hflt
        _ = 2 * m ^ 4 := by ring
    have he_close : e_close.length ≤ 2 * m ^ 4 := by
      have h1 : e_close.length ≤
          ((List.finRange m).filter
            (fun ℓ : Fin m => decide (ℓ.1 + 1 < m))).length * (2 * m ^ 3) := by
        refine flatMap_length_le _ _ (2 * m ^ 3) fun ℓ _ => ?_
        refine (flatMap_length_le _ _ (2 * m ^ 2) fun h _ => ?_).trans
          (by simp [pow_succ]; ring_nf; exact le_rfl)
        refine (flatMap_length_le _ _ (2 * m) fun u _ => ?_).trans
          (by simp [pow_two]; ring_nf; exact le_rfl)
        refine (flatMap_length_le _ _ m fun p _ => ?_).trans (by simp)
        rw [List.length_map]; exact (List.length_filter_le _ _).trans (by simp)
      have hflt : ((List.finRange m).filter
          (fun ℓ : Fin m => decide (ℓ.1 + 1 < m))).length ≤ m :=
        (List.length_filter_le _ _).trans (by simp)
      calc e_close.length ≤ _ := h1
        _ ≤ m * (2 * m ^ 3) := Nat.mul_le_mul_right _ hflt
        _ = 2 * m ^ 4 := by ring
    have he_fin : e_fin.length ≤ 2 * m ^ 2 := by
      have h1 : e_fin.length ≤ (List.finRange m).length * (2 * m) := by
        refine flatMap_length_le _ _ (2 * m) fun h _ => ?_
        refine (flatMap_length_le _ _ 2 fun u _ => by simp).trans (by simp; ring_nf; exact le_rfl)
      calc e_fin.length ≤ (List.finRange m).length * (2 * m) := h1
        _ = 2 * m ^ 2 := by simp [pow_two]; ring
    have he_sink : e_sink.length = 2 := rfl
    have hsz_eq : P.size = (2 * m ^ 3 + 4) +
        ((mvEdgesInit (K := K) (σ := σ) hm).length + e_ext.length + e_close.length +
          e_fin.length + e_sink.length) := by
      simp only [P, mvABP, e_ext, e_close, e_fin, e_sink, ABP.size_mk, List.length_append]
    rw [hsz_eq, he_init, he_sink]
    by_cases hm1 : m = 1
    · subst hm1; simp only [one_pow, mul_one] at *; omega
    · have hm2 : 2 ≤ m := by omega
      have hpow3 : m ^ 3 ≤ m ^ 4 := by
        rw [show m ^ 4 = m ^ 3 * m by ring]; exact Nat.le_mul_of_pos_right _ hm
      have hpow2 : m ^ 2 ≤ m ^ 3 := by
        rw [show m ^ 3 = m ^ 2 * m by ring]; exact Nat.le_mul_of_pos_right _ hm
      have hpow1 : m ≤ m ^ 2 := by
        rw [show m ^ 2 = m * m by ring]; exact Nat.le_mul_of_pos_right _ hm
      have h2m3 : 2 * m ^ 3 + 2 * m ^ 2 + m ≤ 2 * m ^ 4 := by
        have hstep1 : m ^ 2 * 2 ≤ m ^ 3 := by
          rw [show m ^ 3 = m ^ 2 * m by ring]; exact Nat.mul_le_mul_left _ hm2
        have hstep2 : m * 2 ≤ m ^ 2 := by
          rw [show m ^ 2 = m * m by ring]; exact Nat.mul_le_mul_left _ hm2
        have hstep3 : m ^ 3 * 2 ≤ m ^ 4 := by
          rw [show m ^ 4 = m ^ 3 * m by ring]; exact Nat.mul_le_mul_left _ hm2
        nlinarith
      omega

/-- **Mahajan–Vinay theorem**: the determinant of any `m × m` specialization matrix
(`IsSubstMatrix M`) is computed by an ABP of size `≤ 6 * m ^ 4 + 10`.
-/
public theorem exists_abp_det_of_isSubstMatrix {K : Type u} [CommRing K] {σ : Type v} {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ K)) (hM : IsSubstMatrix M) :
    ∃ P : ABP K σ, P.poly = M.det ∧ P.size ≤ 6 * m ^ 4 + 10 := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨ABP.const 1, ?_, by simp⟩
    simp [Matrix.det_fin_zero]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  let lab (i j : Fin m) : σ ⊕ K := (hM i j).choose
  have hlab : ∀ i j, abpLabelPoly (lab i j) = M i j := fun i j => (hM i j).choose_spec
  exact ⟨mvABP hm lab, mvABP_poly hm M lab hlab, mvABP_size hm lab⟩

/-- **Mahajan–Vinay** specialized to `(genericMatrix K m).det`. -/
public theorem exists_abp_det_genericMatrix {K : Type u} [CommRing K] (m : ℕ) :
    ∃ P : ABP K (Fin (m * m)), P.poly = (genericMatrix K m).det ∧ P.size ≤ 6 * m ^ 4 + 10 :=
  exists_abp_det_of_isSubstMatrix (genericMatrix K m) (fun _ _ => .X _)

/-- **Theorem `abp-to-det`**: ABP size and projection
determinantal complexity are polynomially related over every commutative ring `K`.
-/
public theorem abpComplexity_poly_equiv_projDetComplexity {K : Type u} [CommRing K] {σ : Type v}
    (f : MvPolynomial σ K) :
    projDetComplexity f ≤ abpComplexity f ∧
    ∀ m : ℕ, IsProjection f (genericMatrix K m).det →
      abpComplexity f ≤ (6 * m ^ 4 + 10 : ℕ) := by
  refine ⟨projDetComplexity_le_abpComplexity f, fun m hm => ?_⟩
  obtain ⟨M, hM, rfl⟩ := isProjection_det_iff_exists_isSubstMatrix.mp hm
  obtain ⟨P, hP, hsz⟩ := exists_abp_det_of_isSubstMatrix M hM
  exact (abpComplexity_le hP).trans (Nat.cast_le.mpr hsz)

end Clows

end CslibFrontier.Computability.Circuit
