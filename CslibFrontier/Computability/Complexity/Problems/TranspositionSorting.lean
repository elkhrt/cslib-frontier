/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sigma
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sigma
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Find

/-!
# Sorting Permutations by Block Transpositions (`SB3T` and `SBT`)

Formalizes block transpositions, transposition sorting distance, framed transposition breakpoints,
the Bafna--Pevzner lower bound $b_\tau(\pi) \le 3 \, d_\tau(\pi)$, canonical multi-tape
Turing-machine encodings for variable-size finite permutations, the polynomial-time Karp reduction
$\mathrm{SB3T} \le_m^p \mathrm{SBT}$, and polynomial-time decidability of the unit-distance regime
$d_\tau(\pi) \le 1$.

## Main definitions

* `CslibFrontier.Complexity.blockTransp`, `CslibFrontier.Complexity.transpDist`,
  `CslibFrontier.Complexity.transpBreakpoints`: block transpositions, minimum sorting distance, and
  transposition breakpoint count on `Equiv.Perm (Fin n)`.
* `CslibFrontier.Complexity.FinPerm`, `CslibFrontier.Complexity.encFinPerm`,
  `CslibFrontier.Complexity.SBTInstance`, `CslibFrontier.Complexity.encSBTInstance`: finite
  permutation and budgeted instance carriers with injective multi-tape encodings.
* `CslibFrontier.Complexity.SB3T`, `CslibFrontier.Complexity.SBT`,
  `CslibFrontier.Complexity.TranspDistLeOne`: decision languages.

## Main results

* `CslibFrontier.Complexity.transpBreakpoints_le_three_mul_transpDist`: Bafna--Pevzner lower bound.
* `CslibFrontier.Complexity.polyTimeReducible_SB3T_SBT`: $\mathrm{SB3T} \le_m^p \mathrm{SBT}$.
* `CslibFrontier.Complexity.TranspDistLeOne_mem_P`: $\{P \mid d_\tau(P) \le 1\} \in \mathrm{P}$.
-/

public section

namespace CslibFrontier.Complexity

open Turing.MultiTapeTM

/-- Interval reversal on `Fin n`: reverses `[a, b]` when `a ≤ b`, fixing outside `[a, b]`. -/
def revRangePerm {n : ℕ} (a b : Fin n) : Equiv.Perm (Fin n) where
  toFun r :=
    if h : a.val ≤ r.val ∧ r.val ≤ b.val then
      ⟨a.val + b.val - r.val, by have := b.isLt; omega⟩
    else r
  invFun r :=
    if h : a.val ≤ r.val ∧ r.val ≤ b.val then
      ⟨a.val + b.val - r.val, by have := b.isLt; omega⟩
    else r
  left_inv r := by dsimp only; split_ifs <;> apply Fin.ext <;> dsimp only at * <;> omega
  right_inv r := by dsimp only; split_ifs <;> apply Fin.ext <;> dsimp only at * <;> omega

@[simp] theorem val_revRangePerm {n : ℕ} (a b r : Fin n) :
    (revRangePerm a b r).val =
      if a ≤ r ∧ r ≤ b then a.val + b.val - r.val else r.val := by
  simp only [revRangePerm, Fin.le_def, Equiv.coe_fn_mk]; split_ifs <;> rfl

/-- Block transposition $\tau_{i, j, k}$ on `Fin n` (`0 ≤ i < j < k ≤ n`). -/
def blockTransp {n : ℕ} (i j k : ℕ) : Equiv.Perm (Fin n) :=
  if h : i < j ∧ j < k ∧ k ≤ n then
    revRangePerm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ *
      revRangePerm ⟨j, by omega⟩ ⟨k - 1, by omega⟩ *
      revRangePerm ⟨i, by omega⟩ ⟨k - 1, by omega⟩
  else 1

theorem val_blockTransp {n : ℕ} (i j k : ℕ) (r : Fin n) :
    (blockTransp (n := n) i j k r).val =
      if i < j ∧ j < k ∧ k ≤ n then
        if r.val < i then r.val else if r.val < i + (k - j) then j + (r.val - i)
        else if r.val < k then i + (r.val - (i + (k - j))) else r.val
      else r.val := by
  have hr := r.isLt
  simp only [blockTransp]
  split_ifs with h
  · simp only [Equiv.Perm.mul_apply, val_revRangePerm, Fin.le_def]; split_ifs <;> omega
  · simp only [Equiv.Perm.mul_apply, val_revRangePerm, Fin.le_def]; split_ifs <;> omega
  · simp only [Equiv.Perm.mul_apply, val_revRangePerm, Fin.le_def]; split_ifs <;> omega
  · simp only [Equiv.Perm.mul_apply, val_revRangePerm, Fin.le_def]; split_ifs <;> omega
  · rfl

@[simp] theorem blockTransp_mul_cancel {n : ℕ} (i j k : ℕ) :
    blockTransp (n := n) i j k * blockTransp i (i + (k - j)) k = 1 := by
  ext r; simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    val_blockTransp]; split_ifs <;> omega

/-- Single-step block transposition relation on `Equiv.Perm (Fin n)`. -/
def IsTranspStep {n : ℕ} (π σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ k ≤ n ∧ σ = π * blockTransp i j k

/-- `m`-step block-transposition reachability on `Equiv.Perm (Fin n)`. -/
def TranspReachableInSteps {n : ℕ} : ℕ → Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop
  | 0, π, σ => π = σ
  | m + 1, π, σ => ∃ τ : Equiv.Perm (Fin n), IsTranspStep π τ ∧ TranspReachableInSteps m τ σ

theorem TranspReachableInSteps.trans {n m₁ m₂ : ℕ} {π τ σ : Equiv.Perm (Fin n)}
    (h₁ : TranspReachableInSteps m₁ π τ) (h₂ : TranspReachableInSteps m₂ τ σ) :
    TranspReachableInSteps (m₁ + m₂) π σ := by
  induction m₁ generalizing π with
  | zero => subst h₁; simpa using h₂
  | succ m₁ ih => obtain ⟨ξ, hπξ, hξτ⟩ := h₁; rw [Nat.succ_add]; exact ⟨ξ, hπξ, ih hξτ⟩

private theorem exists_transpReachableInSteps_one_aux {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ m ≤ n, TranspReachableInSteps m π 1 := by
  have hpref : ∀ p ≤ n, ∃ m ≤ p, ∃ σ : Equiv.Perm (Fin n),
      TranspReachableInSteps m π σ ∧ ∀ r : Fin n, r.val < p → σ r = r := by
    intro p hp; induction p with
    | zero => exact ⟨0, le_rfl, π, rfl, fun _ hr ↦ absurd hr (Nat.not_lt_zero _)⟩
    | succ p ih =>
      obtain ⟨m, hm, σ₀, hr₀, hp₀⟩ := ih (Nat.le_of_succ_le hp)
      let pFin : Fin n := ⟨p, hp⟩
      let qFin : Fin n := σ₀.symm pFin
      have hle : p ≤ qFin.val := by
        by_contra hlt
        have hfix := (hp₀ qFin (Nat.lt_of_not_ge hlt)).symm.trans (σ₀.apply_symm_apply pFin)
        have : qFin.val = p := congrArg Fin.val hfix; omega
      by_cases hpeq : p = qFin.val
      · refine ⟨m, by omega, σ₀, hr₀, fun r hr ↦ ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
        · exact hp₀ r hlt
        · rw [(Fin.ext (heq.trans hpeq) : r = qFin)]
          exact (σ₀.apply_symm_apply pFin).trans (Fin.ext hpeq)
      · have hpq : p < qFin.val := Nat.lt_of_le_of_ne hle hpeq
        let σ₁ := σ₀ * blockTransp p qFin.val (qFin.val + 1)
        have hstep : TranspReachableInSteps 1 σ₀ σ₁ :=
          ⟨σ₁, ⟨p, qFin.val, qFin.val + 1, hpq, Nat.lt_succ_self _, qFin.isLt, rfl⟩, rfl⟩
        refine ⟨m + 1, by omega, σ₁, hr₀.trans hstep, fun r hr ↦ ?_⟩
        change σ₀ (blockTransp p qFin.val (qFin.val + 1) r) = r
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
        · have hv : (blockTransp (n := n) p qFin.val (qFin.val + 1) r).val = r.val := by
            rw [val_blockTransp, ite_eq_left ⟨hpq, Nat.lt_succ_self _, qFin.isLt⟩, ite_eq_left hlt]
          rw [Fin.ext hv]; exact hp₀ r hlt
        · have hv : (blockTransp (n := n) p qFin.val (qFin.val + 1) r).val = qFin.val := by
            rw [val_blockTransp, ite_eq_left ⟨hpq, Nat.lt_succ_self _, qFin.isLt⟩,
              ite_eq_right (by omega), ite_eq_left (by omega)]; omega
          rw [Fin.ext hv, ← (Fin.ext heq.symm : pFin = r)]; exact σ₀.apply_symm_apply pFin
  obtain ⟨m, hm, σ, hr, hσ⟩ := hpref n le_rfl
  obtain rfl : σ = 1 := Equiv.Perm.ext fun r ↦ hσ r r.isLt
  exact ⟨m, hm, hr⟩

/-- Minimum block-transposition sorting distance $d_\tau(\pi)$ on `Equiv.Perm (Fin n)`. -/
noncomputable def transpDist {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  letI := Classical.decPred fun m ↦ TranspReachableInSteps m π 1
  Nat.find (let ⟨m, _, hm⟩ := exists_transpReachableInSteps_one_aux π; ⟨m, hm⟩)

/-- Framed extension $\widehat{\pi} : \mathrm{Fin}\,(n + 2) \to \mathbb{N}$ of `π`. -/
def extendUnsigned {n : ℕ} (π : Equiv.Perm (Fin n)) (r : Fin (n + 2)) : ℕ :=
  if h0 : r.val = 0 then 0 else if h : r.val ≤ n then (π ⟨r.val - 1, by omega⟩).val + 1 else n + 1

/-- Transposition breakpoint predicate at cut `r : Fin (n + 1)`. -/
def IsTranspBreakpoint {n : ℕ} (π : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : Prop :=
  extendUnsigned π ⟨r.val + 1, by omega⟩ ≠ extendUnsigned π ⟨r.val, by omega⟩ + 1

instance instDecidablePredIsTranspBreakpoint {n : ℕ} (π : Equiv.Perm (Fin n)) :
    DecidablePred (IsTranspBreakpoint π) :=
  fun r ↦ inferInstanceAs
    (Decidable (extendUnsigned π ⟨r.val + 1, by omega⟩ ≠ extendUnsigned π ⟨r.val, by omega⟩ + 1))

/-- Transposition breakpoint count $b_\tau(\pi)$. -/
def transpBreakpoints {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1))).filter (IsTranspBreakpoint π)).card

@[simp] theorem transpBreakpoints_one (n : ℕ) :
    transpBreakpoints (1 : Equiv.Perm (Fin n)) = 0 := by
  rw [transpBreakpoints, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r _
  simp only [IsTranspBreakpoint, extendUnsigned, Equiv.Perm.one_apply, not_ne_iff]
  have := r.isLt; split_ifs <;> omega

theorem transpBreakpoints_le_add_three_blockTransp {n : ℕ} (π : Equiv.Perm (Fin n)) (i j k : ℕ) :
    transpBreakpoints π ≤ transpBreakpoints (π * blockTransp i j k) + 3 := by
  by_cases h : i < j ∧ j < k ∧ k ≤ n
  · obtain ⟨hi, hj, hk⟩ := h
    set π' : Equiv.Perm (Fin n) := π * blockTransp i j k
    let adjSet (σ : Equiv.Perm (Fin n)) : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun r ↦ ¬ IsTranspBreakpoint σ r
    have hcomp : ∀ σ : Equiv.Perm (Fin n), transpBreakpoints σ + (adjSet σ).card = n + 1 :=
      fun σ ↦ by
        simpa only [transpBreakpoints, adjSet, Finset.card_univ, Fintype.card_fin] using
          (Finset.univ : Finset (Fin (n + 1))).card_filter_add_card_filter_not
            (IsTranspBreakpoint σ)
    let shift (r : Fin (n + 1)) : Fin (n + 1) :=
      if h1 : r.val < i then r else if h2 : r.val < i + (k - j) then ⟨j + (r.val - i), by omega⟩
      else if h3 : r.val < k then ⟨i + (r.val - (i + (k - j))), by omega⟩ else r
    let cuts : Finset (Fin (n + 1)) := {⟨i, by omega⟩, ⟨i + (k - j), by omega⟩, ⟨k, by omega⟩}
    have hcuts_card : cuts.card ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ (by simp))))
    have hext : ∀ m : ℕ, (hm : m ≤ n + 1) →
        extendUnsigned π' ⟨m, by omega⟩ =
          extendUnsigned π ⟨if m ≤ i then m else if m ≤ i + (k - j) then j + (m - i)
            else if m ≤ k then i + (m - (i + (k - j))) else m, by split_ifs <;> omega⟩ := by
      intro m hm
      by_cases hm0 : m = 0
      · subst hm0; simp [extendUnsigned]
      · by_cases hmn : m ≤ n
        · simp only [extendUnsigned, hm0, ↓reduceDIte, hmn, π', Equiv.Perm.mul_apply]
          have hbt := val_blockTransp (n := n) i j k ⟨m - 1, by omega⟩
          rw [ite_eq_left ⟨hi, hj, hk⟩] at hbt
          dsimp only at hbt
          have hcond : ¬ (if m ≤ i then m else if m ≤ i + (k - j) then j + (m - i)
              else if m ≤ k then i + (m - (i + (k - j))) else m) = 0 ∧
              (if m ≤ i then m else if m ≤ i + (k - j) then j + (m - i)
              else if m ≤ k then i + (m - (i + (k - j))) else m) ≤ n := by split_ifs <;> omega
          simp only [hcond.1, hcond.2, ↓reduceDIte]
          congr 3; apply Fin.ext; rw [hbt]; dsimp only; split_ifs <;> omega
        · obtain rfl : m = n + 1 := by omega
          simp only [extendUnsigned]; split_ifs <;> omega
    have hsdiff : (adjSet π' \ cuts).card ≤ (adjSet π).card := by
      refine Finset.card_le_card_of_injOn shift (fun r hr ↦ ?_) (fun r₁ hr₁ r₂ hr₂ heq ↦ ?_)
      · rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter] at hr
        obtain ⟨⟨_, hadj⟩, hrc⟩ := hr
        have hne : r.val ≠ i ∧ r.val ≠ i + (k - j) ∧ r.val ≠ k :=
          ⟨fun he ↦ hrc (by have : r = ⟨i, by omega⟩ := Fin.ext he; simp [cuts, this]),
           fun he ↦ hrc (by have : r = ⟨i + (k - j), by omega⟩ := Fin.ext he; simp [cuts, this]),
           fun he ↦ hrc (by have : r = ⟨k, by omega⟩ := Fin.ext he; simp [cuts, this])⟩
        simp only [adjSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          IsTranspBreakpoint, not_ne_iff] at hadj ⊢
        have hrlt := r.isLt
        have h0 := hext r.val (by omega)
        have h1 := hext (r.val + 1) (by omega)
        rw [h0, h1] at hadj
        have eq0 : (⟨(shift r).val, by omega⟩ : Fin (n + 2)) =
            ⟨if r.val ≤ i then r.val else if r.val ≤ i + (k - j) then j + (r.val - i)
             else if r.val ≤ k then i + (r.val - (i + (k - j))) else r.val,
               by split_ifs <;> omega⟩ := by
          apply Fin.ext; simp only [shift, apply_dite Fin.val]; split_ifs <;> omega
        have eq1 : (⟨(shift r).val + 1, by omega⟩ : Fin (n + 2)) =
            ⟨if r.val + 1 ≤ i then r.val + 1 else if r.val + 1 ≤
              i + (k - j) then j + (r.val + 1 - i)
             else if r.val + 1 ≤ k then i + (r.val + 1 - (i + (k - j))) else r.val + 1,
               by split_ifs <;> omega⟩ := by
          apply Fin.ext; simp only [shift, apply_dite Fin.val]; split_ifs <;> omega
        rwa [eq0, eq1]
      · rw [Finset.mem_coe, Finset.mem_sdiff] at hr₁ hr₂
        have h₁ : r₁.val ≠ i ∧ r₁.val ≠ i + (k - j) ∧ r₁.val ≠ k :=
          ⟨fun he ↦ hr₁.2 (by have : r₁ = ⟨i, by omega⟩ := Fin.ext he; simp [cuts, this]),
           fun he ↦ hr₁.2 (by have : r₁ = ⟨i + (k - j), by omega⟩ := Fin.ext he; simp [cuts, this]),
           fun he ↦ hr₁.2 (by have : r₁ = ⟨k, by omega⟩ := Fin.ext he; simp [cuts, this])⟩
        have h₂ : r₂.val ≠ i ∧ r₂.val ≠ i + (k - j) ∧ r₂.val ≠ k :=
          ⟨fun he ↦ hr₂.2 (by have : r₂ = ⟨i, by omega⟩ := Fin.ext he; simp [cuts, this]),
           fun he ↦ hr₂.2 (by have : r₂ = ⟨i + (k - j), by omega⟩ := Fin.ext he; simp [cuts, this]),
           fun he ↦ hr₂.2 (by have : r₂ = ⟨k, by omega⟩ := Fin.ext he; simp [cuts, this])⟩
        have hv := congrArg Fin.val heq
        simp only [shift, apply_dite Fin.val] at hv; split_ifs at hv <;> apply Fin.ext <;> omega
    have hunion : adjSet π' ⊆ (adjSet π' \ cuts) ∪ cuts := fun r hr ↦
      if hrc : r ∈ cuts then Finset.mem_union_right _ hrc
      else Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hr, hrc⟩)
    have hadj_le : (adjSet π').card ≤ (adjSet π).card + 3 :=
      (Finset.card_le_card hunion).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add hsdiff hcuts_card))
    have hc1 := hcomp π; have hc2 := hcomp π'; omega
  · simp [blockTransp, h]

/-- **Bafna--Pevzner lower bound**: `transpBreakpoints π ≤ 3 * transpDist π`. -/
theorem transpBreakpoints_le_three_mul_transpDist {n : ℕ} (π : Equiv.Perm (Fin n)) :
    transpBreakpoints π ≤ 3 * transpDist π := by
  classical
  have hchain : ∀ m (σ : Equiv.Perm (Fin n)), TranspReachableInSteps m σ 1 →
      transpBreakpoints σ ≤ 3 * m := by
    intro m
    induction m with
    | zero => intro σ h; subst h; simp
    | succ m ih =>
      intro σ h
      obtain ⟨τ, ⟨i, j, k, _, _, _, rfl⟩, hr⟩ := h
      have h1 := transpBreakpoints_le_add_three_blockTransp σ i j k
      have h2 := ih (σ * blockTransp i j k) hr
      omega
  exact hchain (transpDist π) π
    (Nat.find_spec (let ⟨m, _, hm⟩ := exists_transpReachableInSteps_one_aux π; ⟨m, hm⟩))

/-- Variable-size finite unsigned permutation carrier. -/
abbrev FinPerm : Type := Σ n : ℕ, Equiv.Perm (Fin n)

/-- Zero-based one-line list of `π : Equiv.Perm (Fin n)`. -/
def permOneLine {n : ℕ} (π : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map fun i ↦ (π i).val

@[simp] theorem length_permOneLine {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (permOneLine π).length = n := by simp [permOneLine]

@[simp] theorem getElem_permOneLine {n : ℕ} (π : Equiv.Perm (Fin n)) (r : ℕ)
    (hr : r < (permOneLine π).length) :
    (permOneLine π)[r] = (π ⟨r, by simpa using hr⟩).val := by simp [permOneLine]

theorem permOneLine_injective (n : ℕ) : Function.Injective (permOneLine (n := n)) := by
  intro π₁ π₂ h
  ext i
  have hi₁ : i.val < (permOneLine π₁).length := by simp [permOneLine, i.isLt]
  have hi₂ : i.val < (permOneLine π₂).length := by simp [permOneLine, i.isLt]
  have hget := congrArg (fun L : List ℕ ↦ L.getD i.val 0) h
  simpa [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂, permOneLine] using hget

/-- Encoding of `Equiv.Perm (Fin n)` via `permOneLine`. -/
@[expose] def encPermFin (n : ℕ) : Equiv.Perm (Fin n) ↪ List Bool where
  toFun π := encList encUnary (permOneLine π)
  inj' _ _ h := permOneLine_injective n ((encList encUnary).injective h)

/-- Canonical encoding of `FinPerm` into `List Bool`. -/
@[expose] def encFinPerm : FinPerm ↪ List Bool :=
  encSigma encUnary encPermFin

@[fun_prop] theorem computableInPolyTime_finPerm_view :
    ComputableInPolyTime (fun P : FinPerm ↦ (P.1, permOneLine P.2))
      encFinPerm (encPair encUnary (encList encUnary)) :=
  ComputableInPolyTime.of_eq fun _ ↦ rfl

@[fun_prop] theorem computableInPolyTime_finPerm_size :
    ComputableInPolyTime (fun P : FinPerm ↦ P.1) encFinPerm encUnary :=
  computableInPolyTime_finPerm_view.fst'

@[fun_prop] theorem computableInPolyTime_finPerm_oneLine :
    ComputableInPolyTime (fun P : FinPerm ↦ permOneLine P.2) encFinPerm (encList encUnary) :=
  computableInPolyTime_finPerm_view.snd'

/-- Framed one-line list matching `extendUnsigned π`. -/
def framedOneLine {n : ℕ} (π : Equiv.Perm (Fin n)) : List ℕ :=
  0 :: ((permOneLine π).map fun v ↦ v + 1) ++ [n + 1]

theorem framedOneLine_eq_ofFn {n : ℕ} (π : Equiv.Perm (Fin n)) :
    framedOneLine π = List.ofFn (extendUnsigned π) := by
  apply List.ext_getElem
  · simp [framedOneLine]
  · intro r hr₁ hr₂
    simp only [List.length_ofFn] at hr₂
    simp only [List.getElem_ofFn, extendUnsigned]
    by_cases hr0 : r = 0
    · subst hr0; simp [framedOneLine]
    · by_cases hrn : r ≤ n
      · simp only [hr0, hrn, ↓reduceDIte]
        have hlen1 : r < (0 :: List.map (fun v ↦ v + 1) (permOneLine π)).length := by
          simp [hrn]
        dsimp only [framedOneLine] at hr₁ ⊢
        rw [List.getElem_append_left hlen1]
        cases r with
        | zero => contradiction
        | succ m =>
          simp
      · obtain rfl : r = n + 1 := by omega
        simp [framedOneLine]

@[fun_prop] theorem computableInPolyTime_framedOneLine :
    ComputableInPolyTime (fun P : FinPerm ↦ framedOneLine P.2) encFinPerm (encList encUnary) := by
  have hinc : ComputableInPolyTime
      (fun P : FinPerm ↦ (permOneLine P.2).map fun v ↦ v + 1)
      encFinPerm (encList encUnary) :=
    ComputableInPolyTime.mapWith (encP := encBool) (encA := encUnary) (encB := encUnary)
      (f := fun q : Bool × ℕ ↦ q.2 + 1)
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.snd encBool encUnary)
        (ComputableInPolyTime.const 1))
      (.const true) computableInPolyTime_finPerm_oneLine
  have hcons : ComputableInPolyTime
      (fun P : FinPerm ↦ 0 :: (permOneLine P.2).map fun v ↦ v + 1)
      encFinPerm (encList encUnary) :=
    (ComputableInPolyTime.cons encUnary).comp ((ComputableInPolyTime.const 0).prod hinc)
  have hlast : ComputableInPolyTime (fun P : FinPerm ↦ [P.1 + 1]) encFinPerm (encList encUnary) :=
    (ComputableInPolyTime.cons encUnary).comp
      ((by fun_prop : ComputableInPolyTime (fun P : FinPerm ↦ P.1 + 1) encFinPerm encUnary).prod
        (ComputableInPolyTime.const []))
  exact (ComputableInPolyTime.listAppend encUnary).comp (hcons.prod hlast)

private lemma countP_ofFn_eq_card_filter {m : ℕ} {α : Type*} (f : Fin m → α) (p : α → Bool) :
    (List.ofFn f).countP p =
      ((Finset.univ : Finset (Fin m)).filter fun i ↦ p (f i) = true).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.countP_cons, ih, Fin.univ_succ, Finset.filter_cons]
    split_ifs with h
    · rw [Finset.card_cons (by simp), Finset.filter_map, Function.Embedding.coeFn_mk]
      simp [Finset.card_map]
    · rw [Finset.filter_map, Function.Embedding.coeFn_mk]
      simp [Finset.card_map]

private lemma zip_ofFn_succ_tail {m : ℕ} {α : Type*} (f : Fin (m + 1) → α) :
    (List.ofFn f).zip (List.ofFn f).tail =
      List.ofFn fun r : Fin m ↦ (f ⟨r.val, by omega⟩, f ⟨r.val + 1, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_zip, List.length_tail, List.length_ofFn]; omega
  · intro r _ _
    simp only [List.getElem_zip, List.getElem_tail, List.getElem_ofFn]

@[fun_prop] theorem computableInPolyTime_transpBreakpoints :
    ComputableInPolyTime (fun P : FinPerm ↦ transpBreakpoints P.2) encFinPerm encUnary := by
  have hF := computableInPolyTime_framedOneLine
  have hTail : ComputableInPolyTime (fun P : FinPerm ↦ (framedOneLine P.2).tail)
      encFinPerm (encList encUnary) :=
    (ComputableInPolyTime.listTail encUnary).comp hF
  have hZip : ComputableInPolyTime
      (fun P : FinPerm ↦ (framedOneLine P.2).zip (framedOneLine P.2).tail)
      encFinPerm (encList (encPair encUnary encUnary)) :=
    (ComputableInPolyTime.zip encUnary encUnary).comp (hF.prod hTail)
  have hCnt : ComputableInPolyTime
      (fun P : FinPerm ↦
        ((framedOneLine P.2).zip (framedOneLine P.2).tail).countP fun q ↦ !(q.1 + 1 == q.2))
      encFinPerm encUnary :=
    ComputableInPolyTime.countPWithInput hZip (by fun_prop)
  refine hCnt.of_enc_eq fun ⟨n, π⟩ ↦ congrArg encUnary ?_
  dsimp only
  rw [framedOneLine_eq_ofFn, zip_ofFn_succ_tail, countP_ofFn_eq_card_filter, transpBreakpoints]
  congr 1; ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, IsTranspBreakpoint]
  omega

private lemma countP_range_div_three (b : ℕ) :
    ((List.range b).countP fun q ↦ decide (3 * (q + 1) ≤ b)) = b / 3 := by
  rw [List.countP_eq_length_filter]
  have hsplit : List.range b =
      List.range (b / 3) ++ (List.range (b - b / 3)).map (b / 3 + ·) := by
    conv_lhs => rw [← Nat.add_sub_of_le (Nat.div_le_self b 3)]
    exact List.range_add
  rw [hsplit, List.filter_append]
  have hleft : (List.range (b / 3)).filter (fun q ↦ decide (3 * (q + 1) ≤ b)) =
      List.range (b / 3) := by
    rw [List.filter_eq_self]
    intro q hq; rw [List.mem_range] at hq; simp only [decide_eq_true_eq]; omega
  have hright : ((List.range (b - b / 3)).map (b / 3 + ·)).filter
      (fun q ↦ decide (3 * (q + 1) ≤ b)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq; rw [List.mem_map] at hq; obtain ⟨d, _, rfl⟩ := hq
    simp only [decide_eq_true_eq]; omega
  rw [hleft, hright, List.append_nil, List.length_range]

@[fun_prop] theorem computableInPolyTime_unary_div_three :
    ComputableInPolyTime (fun b : ℕ ↦ b / 3) encUnary encUnary := by
  have h : ComputableInPolyTime
      (fun b : ℕ ↦ (List.range b).countP fun q ↦ decide (3 * (q + 1) ≤ b))
      encUnary encUnary :=
    ComputableInPolyTime.countPWithInput
      (ComputableInPolyTime.range.comp ComputableInPolyTime.id') (by fun_prop)
  exact h.of_enc_eq fun b ↦ congrArg encUnary (countP_range_div_three b).symm

/-- Sorting by $3$-Transpositions (`SB3T`). -/
def SB3T : Set FinPerm :=
  {P | ∃ m : ℕ, TranspReachableInSteps m P.2 1 ∧ 3 * m = transpBreakpoints P.2}

/-- Budgeted instance of Sorting by Transpositions (`SBT`). -/
@[ext]
structure SBTInstance where
  /-- Input finite unsigned permutation. -/
  perm : FinPerm
  /-- Upper bound on block transpositions. -/
  budget : ℕ

/-- Encoding of `SBTInstance`. -/
enc_structure encSBTInstance : SBTInstance where
  perm : encFinPerm,
  budget : encUnary

attribute [fun_prop] encSBTInstance_perm_polyTime
  encSBTInstance_budget_polyTime encSBTInstance_mk_polyTime

/-- Sorting by Transpositions (`SBT`). -/
def SBT : Set SBTInstance :=
  {I | transpDist I.perm.2 ≤ I.budget}

/-- Polynomial-time Karp reduction $\mathrm{SB3T} \le_m^p \mathrm{SBT}$. -/
theorem polyTimeReducible_SB3T_SBT :
    Cslib.Complexity.PolyTimeReducible encFinPerm encSBTInstance SB3T SBT := by
  classical
  let f : FinPerm → SBTInstance := fun P ↦ ⟨P, transpBreakpoints P.2 / 3⟩
  have hf : ComputableInPolyTime f encFinPerm encSBTInstance := by
    unfold f
    exact encSBTInstance_mk_polyTime ComputableInPolyTime.id'
      (computableInPolyTime_unary_div_three.comp computableInPolyTime_transpBreakpoints)
  refine ⟨f, hf, fun P ↦ ?_⟩
  simp only [SB3T, SBT, Set.mem_ofPred, f]
  have hbp := transpBreakpoints_le_three_mul_transpDist P.2
  have hspec : TranspReachableInSteps (transpDist P.2) P.2 1 :=
    Nat.find_spec (let ⟨m, _, hm⟩ := exists_transpReachableInSteps_one_aux P.2; ⟨m, hm⟩)
  constructor
  · rintro ⟨m, hreach, hm⟩
    have hle : transpDist P.2 ≤ m :=
      Nat.find_min' (let ⟨m₀, _, hm₀⟩ := exists_transpReachableInSteps_one_aux P.2; ⟨m₀, hm₀⟩)
        hreach
    omega
  · intro hle
    exact ⟨transpDist P.2, hspec, by omega⟩

/-- Unit-distance block transposition language `{P | transpDist P.2 ≤ 1}`. -/
def TranspDistLeOne : Set FinPerm :=
  {P | transpDist P.2 ≤ 1}

private def listEqNat (L₁ L₂ : List ℕ) : Bool :=
  (L₁.length == L₂.length) && (L₁.zip L₂).all fun p ↦ p.1 == p.2

private lemma listEqNat_eq_true_iff (L₁ L₂ : List ℕ) :
    listEqNat L₁ L₂ = true ↔ L₁ = L₂ := by
  simp only [listEqNat, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨fun ⟨hlen, hall⟩ ↦ List.ext_getElem hlen fun r hr₁ hr₂ ↦ ?_, fun h ↦ ?_⟩
  · have hmem : (L₁[r], L₂[r]) ∈ L₁.zip L₂ := by
      rw [List.mem_iff_getElem]; exact ⟨r, by simp [hr₁, hr₂], by simp⟩
    exact hall _ hmem
  · subst h
    refine ⟨rfl, fun p hp ↦ ?_⟩
    obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hp
    simp only [List.getElem_zip] at hget
    rw [← hget]

private def applyTranspList (L : List ℕ) (i j k : ℕ) : List ℕ :=
  L.take i ++ (L.drop j).take (k - j) ++ (L.drop i).take (j - i) ++ L.drop k

private lemma applyTranspList_permOneLine {n : ℕ} (π : Equiv.Perm (Fin n)) {i j k : ℕ}
    (hi : i < j) (hj : j < k) (hk : k ≤ n) :
    applyTranspList (permOneLine π) i j k = permOneLine (π * blockTransp i j k) := by
  apply List.ext_getElem
  · simp only [applyTranspList, List.length_append, List.length_take, List.length_drop,
      length_permOneLine]; omega
  · intro r _ hr₂
    have hrn : r < n := by simpa only [length_permOneLine] using hr₂
    rw [getElem_permOneLine]
    simp only [Equiv.Perm.mul_apply, applyTranspList]
    by_cases h1 : r < i
    · have hlen1 : r < ((permOneLine π).take i).length := by simp; omega
      have hlen2 : r < ((permOneLine π).take i ++ ((permOneLine π).drop j).take (k - j)).length :=
        by simp; omega
      have hlen3 : r < ((permOneLine π).take i ++ ((permOneLine π).drop j).take (k - j) ++
          ((permOneLine π).drop i).take (j - i)).length := by simp; omega
      rw [List.getElem_append_left hlen3, List.getElem_append_left hlen2,
        List.getElem_append_left hlen1, List.getElem_take, getElem_permOneLine]
      refine congrArg (fun x : Fin n ↦ (π x).val) (Fin.ext ?_)
      rw [val_blockTransp, ite_eq_left ⟨hi, hj, hk⟩]; dsimp only; split_ifs; omega
    · by_cases h2 : r < i + (k - j)
      · have hlen1 : ((permOneLine π).take i).length ≤ r := by simp; omega
        have hlen2 : r < ((permOneLine π).take i ++ ((permOneLine π).drop j).take (k - j)).length :=
          by simp; omega
        have hlen3 : r < ((permOneLine π).take i ++ ((permOneLine π).drop j).take (k - j) ++
            ((permOneLine π).drop i).take (j - i)).length := by simp; omega
        rw [List.getElem_append_left hlen3, List.getElem_append_left hlen2,
          List.getElem_append_right hlen1]
        simp only [List.length_take, length_permOneLine, Nat.min_eq_left (by omega : i ≤ n),
          List.getElem_take, List.getElem_drop, getElem_permOneLine]
        refine congrArg (fun x : Fin n ↦ (π x).val) (Fin.ext ?_)
        rw [val_blockTransp, ite_eq_left ⟨hi, hj, hk⟩]; dsimp only; split_ifs; omega
      · by_cases h3 : r < k
        · have hlen2 : ((permOneLine π).take i ++
              ((permOneLine π).drop j).take (k - j)).length ≤ r := by simp; omega
          have hlen3 : r < ((permOneLine π).take i ++ ((permOneLine π).drop j).take (k - j) ++
              ((permOneLine π).drop i).take (j - i)).length := by simp; omega
          rw [List.getElem_append_left hlen3, List.getElem_append_right hlen2]
          simp only [List.length_append, List.length_take, List.length_drop, length_permOneLine,
            Nat.min_eq_left (by omega : i ≤ n), Nat.min_eq_left (by omega : k - j ≤ n - j),
            List.getElem_take, List.getElem_drop, getElem_permOneLine]
          refine congrArg (fun x : Fin n ↦ (π x).val) (Fin.ext ?_)
          rw [val_blockTransp, ite_eq_left ⟨hi, hj, hk⟩]; dsimp only; split_ifs; omega
        · have hlen3 : ((permOneLine π).take i ++ ((permOneLine π).drop j).take (k - j) ++
              ((permOneLine π).drop i).take (j - i)).length ≤ r := by simp; omega
          rw [List.getElem_append_right hlen3]
          simp only [List.length_append, List.length_take, List.length_drop, length_permOneLine,
            Nat.min_eq_left (by omega : i ≤ n), Nat.min_eq_left (by omega : k - j ≤ n - j),
            Nat.min_eq_left (by omega : j - i ≤ n - i), List.getElem_drop, getElem_permOneLine]
          refine congrArg (fun x : Fin n ↦ (π x).val) (Fin.ext ?_)
          rw [val_blockTransp, ite_eq_left ⟨hi, hj, hk⟩]; dsimp only; split_ifs; omega

/-- Deciding whether `transpDist P.2 ≤ 1` belongs to `Cslib.Complexity.P encFinPerm`. -/
theorem TranspDistLeOne_mem_P :
    TranspDistLeOne ∈ Cslib.Complexity.P encFinPerm := by
  classical
  let decider : FinPerm → Bool := fun P ↦
    listEqNat (permOneLine P.2) (List.range P.1) ||
      (List.range (P.1 + 1)).any fun i ↦
        (List.range (P.1 + 1)).any fun j ↦
          (List.range (P.1 + 1)).any fun k ↦
            decide (i < j) && decide (j < k) &&
              listEqNat (applyTranspList (permOneLine P.2) i j k) (List.range P.1)
  have hListEq : ∀ {γ : Type} {encIn : γ ↪ List Bool} {f g : γ → List ℕ},
      ComputableInPolyTime f encIn (encList encUnary) →
      ComputableInPolyTime g encIn (encList encUnary) →
      ComputableInPolyTime (fun x ↦ listEqNat (f x) (g x)) encIn encBool := by
    intro γ encIn f g hf hg
    unfold listEqNat
    have hlen : ComputableInPolyTime (fun x ↦ (f x).length == (g x).length) encIn encBool := by
      fun_prop
    have hzip : ComputableInPolyTime (fun x ↦ (f x).zip (g x))
        encIn (encList (encPair encUnary encUnary)) :=
      (ComputableInPolyTime.zip encUnary encUnary).comp (hf.prod hg)
    have hpairSnd := ComputableInPolyTime.snd encBool (encPair encUnary encUnary)
    have hall : ComputableInPolyTime (fun x ↦ ((f x).zip (g x)).all fun p ↦ p.1 == p.2)
        encIn encBool :=
      ComputableInPolyTime.allWith (encP := encBool) (encA := encPair encUnary encUnary)
        (test := fun q : Bool × (ℕ × ℕ) ↦ q.2.1 == q.2.2)
        (ComputableInPolyTime.unary_beq hpairSnd.fst' hpairSnd.snd') (.const true) hzip
    exact ComputableInPolyTime.bool_and.comp (hlen.prod hall)
  have hdec : ComputableInPolyTime decider encFinPerm encBool := by
    unfold decider
    have hidCheck : ComputableInPolyTime
        (fun P : FinPerm ↦ listEqNat (permOneLine P.2) (List.range P.1)) encFinPerm encBool :=
      hListEq computableInPolyTime_finPerm_oneLine
        (ComputableInPolyTime.range.comp computableInPolyTime_finPerm_size)
    have hP3 : ComputableInPolyTime (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦ u.1.1.1)
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary) encFinPerm := by
      fun_prop
    have hi3 : ComputableInPolyTime (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦ u.1.1.2)
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary) encUnary := by
      fun_prop
    have hj3 : ComputableInPolyTime (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦ u.1.2)
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary) encUnary := by
      fun_prop
    have hk3 : ComputableInPolyTime (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦ u.2)
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary) encUnary := by
      fun_prop
    have hL3 : ComputableInPolyTime (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦ permOneLine u.1.1.1.2)
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary)
        (encList encUnary) :=
      computableInPolyTime_finPerm_oneLine.comp hP3
    have happ3 : ComputableInPolyTime
        (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦
          applyTranspList (permOneLine u.1.1.1.2) u.1.1.2 u.1.2 u.2)
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary)
        (encList encUnary) := by
      unfold applyTranspList
      have s1 := ComputableInPolyTime.listTakeWithInput hL3 hi3
      have s2 := ComputableInPolyTime.listTakeWithInput
        (ComputableInPolyTime.listDropWithInput hL3 hj3)
        (ComputableInPolyTime.unary_sub' hk3 hj3)
      have s3 := ComputableInPolyTime.listTakeWithInput
        (ComputableInPolyTime.listDropWithInput hL3 hi3)
        (ComputableInPolyTime.unary_sub' hj3 hi3)
      have s4 := ComputableInPolyTime.listDropWithInput hL3 hk3
      have a1 := (ComputableInPolyTime.listAppend encUnary).comp (s1.prod s2)
      have a2 := (ComputableInPolyTime.listAppend encUnary).comp (a1.prod s3)
      exact (ComputableInPolyTime.listAppend encUnary).comp (a2.prod s4)
    have hinner3 : ComputableInPolyTime
        (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦
          decide (u.1.1.2 < u.1.2) && decide (u.1.2 < u.2) &&
            listEqNat (applyTranspList (permOneLine u.1.1.1.2) u.1.1.2 u.1.2 u.2)
              (List.range u.1.1.1.1))
        (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary) encBool := by
      have hc1 : ComputableInPolyTime
          (fun u : ((FinPerm × ℕ) × ℕ) × ℕ ↦ decide (u.1.1.2 < u.1.2) && decide (u.1.2 < u.2))
          (encPair (encPair (encPair encFinPerm encUnary) encUnary) encUnary) encBool := by
        fun_prop
      have hc2 := hListEq happ3
        (ComputableInPolyTime.range.comp (computableInPolyTime_finPerm_size.comp hP3))
      exact ComputableInPolyTime.bool_and.comp (hc1.prod hc2)
    have hrng1 : ComputableInPolyTime (fun P : FinPerm ↦ List.range (P.1 + 1))
        encFinPerm (encList encUnary) :=
      ComputableInPolyTime.range.comp (by fun_prop)
    have hP2 : ComputableInPolyTime (fun q : (FinPerm × ℕ) × ℕ ↦ q.1.1)
        (encPair (encPair encFinPerm encUnary) encUnary) encFinPerm := by fun_prop
    have hP1 : ComputableInPolyTime (fun q : FinPerm × ℕ ↦ q.1)
        (encPair encFinPerm encUnary) encFinPerm := by fun_prop
    have hanyK := ComputableInPolyTime.anyWith hinner3 ComputableInPolyTime.id' (hrng1.comp hP2)
    have hanyJ := ComputableInPolyTime.anyWith hanyK ComputableInPolyTime.id' (hrng1.comp hP1)
    have hanyI := ComputableInPolyTime.anyWith hanyJ ComputableInPolyTime.id' hrng1
    exact ComputableInPolyTime.bool_or.comp (hidCheck.prod hanyI)
  refine ⟨decider, hdec, fun ⟨n, π⟩ ↦ ?_⟩
  have hone : permOneLine (1 : Equiv.Perm (Fin n)) = List.range n := by
    apply List.ext_getElem <;> simp
  simp only [TranspDistLeOne, Set.mem_ofPred, decider, Bool.or_eq_true,
    List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, listEqNat_eq_true_iff,
    ← hone]
  classical
  have hex : ∀ σ : Equiv.Perm (Fin n), ∃ m, TranspReachableInSteps m σ 1 := fun σ ↦ by
    obtain ⟨m₀, _, hm₀⟩ := exists_transpReachableInSteps_one_aux σ
    exact ⟨m₀, hm₀⟩
  have hspec : TranspReachableInSteps (transpDist π) π 1 := Nat.find_spec (hex π)
  constructor
  · intro hle
    rcases (by omega : transpDist π = 0 ∨ transpDist π = 1) with h0 | h1
    · left
      have hr0 : TranspReachableInSteps 0 π 1 := h0 ▸ hspec
      rw [show π = 1 from hr0]
    · right
      obtain ⟨σ, ⟨i, j, k, hi, hj, hk, hσ⟩, hσ1⟩ : TranspReachableInSteps 1 π 1 := h1 ▸ hspec
      obtain rfl : σ = 1 := hσ1
      refine ⟨i, by omega, j, by omega, k, by omega, ⟨hi, hj⟩, ?_⟩
      rw [applyTranspList_permOneLine π hi hj hk, ← hσ]
  · rintro (h0 | ⟨i, _, j, _, k, hklt, ⟨hi, hj⟩, heq⟩)
    · rw [permOneLine_injective n h0]
      exact (Nat.find_min' (hex 1) (m := 0) rfl).trans (by omega)
    · have hk : k ≤ n := by omega
      rw [applyTranspList_permOneLine π hi hj hk] at heq
      have hmul : π * blockTransp i j k = 1 := permOneLine_injective n heq
      have hr1 : TranspReachableInSteps 1 π 1 := ⟨1, ⟨i, j, k, hi, hj, hk, hmul.symm⟩, rfl⟩
      exact Nat.find_min' (hex π) hr1

end CslibFrontier.Complexity
