/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Foundations.Relation.Termination
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.CompleteLattice.Finset

/-!
# Derivation Height and Worst-Case Complexity of Reduction Relations

This module extends `Cslib.Foundations.Relation.RelatesInSteps` and
`Cslib.Foundations.Relation.Termination` with `ℕ∞`-valued derivation height and size-indexed
worst-case complexity functions for abstract binary reduction relations `r : α → α → Prop`,
including the dynamic-programming Bellman equation, König's lemma for finitely branching
strongly normalizing relations, and quantitative upper bounds from `ℕ`-valued step measures.

## Main definitions

* `CslibFrontier.Relation.derivationHeight`: supremum in `ℕ∞` of `n : ℕ` such that
  `∃ b, Relation.RelatesInSteps r a b n`.
* `CslibFrontier.Relation.complexity`: supremum in `ℕ∞` of `derivationHeight r s` over
  `s ∈ T` with `size s ≤ n`.

## Main results

* `CslibFrontier.Relation.exists_relatesInSteps_of_derivationHeight_eq_coe`: every finite
  derivation height `(m : ℕ∞)` is attained by an explicit `m`-step walk.
* `CslibFrontier.Relation.derivationHeight_eq_zero_iff`: `derivationHeight r a = 0 ↔
  Relation.Normal r a`.
* `CslibFrontier.Relation.derivationHeight_eq_iSup_succ`: Bellman equation
  `derivationHeight r a = ⨆ b ∈ Relation.successors r a, (derivationHeight r b + 1)`.
* `CslibFrontier.Relation.derivationHeight_lt_top_iff_sn`: König's lemma for finitely
  branching reduction relations (`derivationHeight r a < ⊤ ↔ Relation.SN r a`).
* `CslibFrontier.Relation.derivationHeight_le_of_step_measure` and
  `CslibFrontier.Relation.complexity_le_of_step_measure`: quantitative step-measure bounds.
-/

public section

namespace CslibFrontier.Relation

universe u v

variable {α : Type u}

/-- The derivation height of `a : α` with respect to a reduction relation `r : α → α → Prop`,
valued in `ℕ∞`: the supremum of all step counts `n : ℕ` for which there exists `b : α` with
`_root_.Relation.RelatesInSteps r a b n`. -/
noncomputable def derivationHeight (r : α → α → Prop) (a : α) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ b, _root_.Relation.RelatesInSteps r a b n), (n : ℕ∞)

/-- Any `n`-step walk from `a` to `b` witnesses `(n : ℕ∞) ≤ derivationHeight r a`. -/
theorem le_derivationHeight_of_relatesInSteps {r : α → α → Prop} {a b : α} {n : ℕ}
    (h : _root_.Relation.RelatesInSteps r a b n) :
    (n : ℕ∞) ≤ derivationHeight r a :=
  le_iSup₂_of_le n ⟨b, h⟩ le_rfl

/-- Upper-bound characterization of `derivationHeight`. -/
theorem derivationHeight_le_iff {r : α → α → Prop} {a : α} {k : ℕ∞} :
    derivationHeight r a ≤ k ↔
      ∀ (n : ℕ) (b : α), _root_.Relation.RelatesInSteps r a b n → (n : ℕ∞) ≤ k := by
  simp only [derivationHeight, iSup_le_iff, forall_exists_index]

/-- Every finite value `(m : ℕ∞)` of `derivationHeight r a` is attained by an explicit `m`-step
reduction sequence starting at `a`. -/
theorem exists_relatesInSteps_of_derivationHeight_eq_coe {r : α → α → Prop} {a : α} {m : ℕ}
    (h : derivationHeight r a = (m : ℕ∞)) :
    ∃ b, _root_.Relation.RelatesInSteps r a b m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact ⟨a, .refl a⟩
  · by_contra hnot
    have hle : derivationHeight r a ≤ ((m - 1 : ℕ) : ℕ∞) := by
      rw [derivationHeight_le_iff]
      intro n b hnb
      have hnm : n ≤ m := Nat.cast_le.mp (h ▸ le_derivationHeight_of_relatesInSteps hnb)
      have hne : n ≠ m := fun hEq ↦ hnot ⟨b, hEq ▸ hnb⟩
      exact Nat.cast_le.mpr (Nat.le_sub_one_of_lt (lt_of_le_of_ne hnm hne))
    rw [h] at hle
    have hlt : m - 1 < m := Nat.sub_lt (Nat.pos_of_ne_zero hm) Nat.one_pos
    exact (not_lt_of_ge (Nat.cast_le.mp hle)) hlt

/-- If `a` is a normal form of `r`, then `derivationHeight r a = 0`. -/
theorem derivationHeight_eq_zero_of_normal {r : α → α → Prop} {a : α}
    (hn : _root_.Relation.Normal r a) :
    derivationHeight r a = 0 := by
  apply le_antisymm _ bot_le
  rw [derivationHeight_le_iff]
  intro n b hnb
  cases n with
  | zero => simp
  | succ _ =>
    obtain ⟨c, hac, _⟩ := hnb.succ'
    exact False.elim (hn ⟨c, hac⟩)

/-- `derivationHeight r a = 0` if and only if `a` is a normal form of `r`. -/
theorem derivationHeight_eq_zero_iff {r : α → α → Prop} {a : α} :
    derivationHeight r a = 0 ↔ _root_.Relation.Normal r a := by
  refine ⟨fun h ⟨b, hab⟩ ↦ ?_, derivationHeight_eq_zero_of_normal⟩
  have h1 : (1 : ℕ∞) ≤ derivationHeight r a :=
    le_derivationHeight_of_relatesInSteps (.single hab)
  rw [h] at h1
  exact absurd h1 (by decide)

/-- A single reduction step `r a b` satisfies `derivationHeight r b + 1 ≤ derivationHeight r a`. -/
theorem add_one_le_derivationHeight_of_rel {r : α → α → Prop} {a b : α} (hab : r a b) :
    derivationHeight r b + 1 ≤ derivationHeight r a := by
  cases hdh : derivationHeight r b with
  | top =>
    rw [top_add, top_le_iff]
    cases ha : derivationHeight r a with
    | top => rfl
    | coe m =>
      have hle : derivationHeight r b ≤ (m : ℕ∞) := by
        rw [derivationHeight_le_iff]
        intro n c hbc
        have hstep : _root_.Relation.RelatesInSteps r a c (n + 1) := .head a b c n hab hbc
        have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) :=
          ha ▸ le_derivationHeight_of_relatesInSteps hstep
        exact Nat.cast_le.mpr (Nat.le_of_succ_le (Nat.cast_le.mp h1))
      rw [hdh] at hle
      exact absurd hle (by simp)
  | coe m =>
    obtain ⟨c, hbc⟩ := exists_relatesInSteps_of_derivationHeight_eq_coe hdh
    exact le_derivationHeight_of_relatesInSteps (.head a b c m hab hbc)

/-- Dynamic-programming recurrence for `derivationHeight`. -/
theorem derivationHeight_eq_iSup_succ (r : α → α → Prop) (a : α) :
    derivationHeight r a =
      ⨆ (b : α) (_ : b ∈ _root_.Relation.successors r a), (derivationHeight r b + 1) := by
  apply le_antisymm
  · rw [derivationHeight_le_iff]
    intro n c hac
    cases n with
    | zero => exact bot_le
    | succ m =>
      obtain ⟨b, hab, hbc⟩ := hac.succ'
      refine le_iSup₂_of_le b hab ?_
      have hm : (m : ℕ∞) ≤ derivationHeight r b := le_derivationHeight_of_relatesInSteps hbc
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add_left hm 1
  · exact iSup₂_le fun b hab ↦ add_one_le_derivationHeight_of_rel hab

/-- König's lemma (forward direction) for finitely branching relations. -/
theorem derivationHeight_lt_top_of_sn {r : α → α → Prop}
    (hfb : ∀ x, (_root_.Relation.successors r x).Finite)
    {a : α} (hsn : _root_.Relation.SN r a) :
    derivationHeight r a < ⊤ := by
  classical
  induction hsn with
  | intro x _ ih =>
    rw [derivationHeight_eq_iSup_succ]
    have hfin := hfb x
    let S : Finset α := hfin.toFinset
    have hle :
        (⨆ (b : α) (_ : b ∈ _root_.Relation.successors r x), (derivationHeight r b + 1)) ≤
          S.sup (fun b ↦ if r x b then derivationHeight r b + 1 else 0) := by
      refine iSup₂_le fun b hxb ↦ ?_
      have hbS : b ∈ S := hfin.mem_toFinset.mpr hxb
      have hr : r x b := hxb
      refine le_trans ?_ (Finset.le_sup (f := fun b ↦
        if r x b then derivationHeight r b + 1 else 0) hbS)
      simp only [hr, ↓reduceIte]
      exact le_rfl
    refine lt_of_le_of_lt hle ?_
    rw [Finset.sup_lt_iff (ENat.natCast_lt_top 0)]
    intro b _
    split_ifs with hxb
    · have hlt : derivationHeight r b < ⊤ := ih b hxb
      cases hdh : derivationHeight r b with
      | top =>
        rw [hdh] at hlt
        exact absurd hlt (lt_irrefl ⊤)
      | coe m =>
        exact ENat.natCast_lt_top (m + 1)
    · exact ENat.natCast_lt_top 0

/-- Finite derivation height implies strong normalization. -/
theorem sn_of_derivationHeight_lt_top {r : α → α → Prop} {a : α}
    (h : derivationHeight r a < ⊤) :
    _root_.Relation.SN r a := by
  cases hm : derivationHeight r a with
  | top =>
    rw [hm] at h
    exact absurd h (lt_irrefl ⊤)
  | coe m =>
    have hle : derivationHeight r a ≤ (m : ℕ∞) := hm.le
    clear hm h
    induction m generalizing a with
    | zero =>
      have h0 : derivationHeight r a = 0 := le_antisymm hle bot_le
      exact _root_.Relation.SN.of_normal (derivationHeight_eq_zero_iff.mp h0)
    | succ k ih =>
      refine _root_.Relation.SN.intro fun b hab ↦ ?_
      have hstep := (add_one_le_derivationHeight_of_rel hab).trans hle
      cases hdh : derivationHeight r b with
      | top =>
        rw [hdh, top_add] at hstep
        exact absurd hstep (by simp)
      | coe n =>
        rw [hdh, ← Nat.cast_one, ← Nat.cast_add] at hstep
        have hnk : n ≤ k := Nat.le_of_succ_le_succ (Nat.cast_le.mp hstep)
        refine ih ?_
        rw [hdh]
        exact Nat.cast_le.mpr hnk

/-- König's lemma for finitely branching reduction relations:
`derivationHeight r a < ⊤ ↔ Relation.SN r a`. -/
theorem derivationHeight_lt_top_iff_sn {r : α → α → Prop}
    (hfb : ∀ x, (_root_.Relation.successors r x).Finite) {a : α} :
    derivationHeight r a < ⊤ ↔ _root_.Relation.SN r a :=
  ⟨sn_of_derivationHeight_lt_top, derivationHeight_lt_top_of_sn hfb⟩

/-- Quantitative step-measure bound on `derivationHeight`. -/
theorem derivationHeight_le_of_step_measure {r : α → α → Prop} (Φ : α → ℕ) {a : α}
    (hstep : ∀ x y, _root_.Relation.ReflTransGen r a x → r x y → Φ y < Φ x) :
    derivationHeight r a ≤ (Φ a : ℕ∞) := by
  rw [derivationHeight_le_iff]
  intro n b hnb
  suffices hsum : Φ b + n ≤ Φ a by
    exact Nat.cast_le.mpr (Nat.le_of_add_left_le hsum)
  induction hnb with
  | refl => simp
  | tail t' t'' _ h₁ h₂ ih =>
    have hlt : Φ t'' < Φ t' := hstep t' t'' h₁.reflTransGen h₂
    omega

/-- Worst-case derivation complexity `comp(n, r, T)` over initial states `s ∈ T` of size
`size s ≤ n`. -/
noncomputable def complexity (size : α → ℕ) (r : α → α → Prop) (T : Set α) (n : ℕ) : ℕ∞ :=
  ⨆ (s : α) (_ : s ∈ T ∧ size s ≤ n), derivationHeight r s

/-- Upper-bound characterization of `complexity`. -/
theorem complexity_le_iff {size : α → ℕ} {r : α → α → Prop} {T : Set α} {n : ℕ} {k : ℕ∞} :
    complexity size r T n ≤ k ↔ ∀ s ∈ T, size s ≤ n → derivationHeight r s ≤ k := by
  simp only [complexity, iSup_le_iff, and_imp]

/-- Quantitative `ℕ` upper bound on `complexity` from a strictly decreasing reachable step
measure `Φ : α → ℕ`. -/
theorem complexity_le_of_step_measure {size : α → ℕ} {r : α → α → Prop} {T : Set α}
    (Φ : α → ℕ)
    (hstep : ∀ s ∈ T, ∀ x y, _root_.Relation.ReflTransGen r s x → r x y → Φ y < Φ x)
    {n B : ℕ} (hbound : ∀ s ∈ T, size s ≤ n → Φ s ≤ B) :
    complexity size r T n ≤ (B : ℕ∞) := by
  rw [complexity_le_iff]
  intro s hs hsz
  exact (derivationHeight_le_of_step_measure Φ (hstep s hs)).trans
    (Nat.cast_le.mpr (hbound s hs hsz))

end CslibFrontier.Relation
