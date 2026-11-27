/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.Hardness
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter-Bounded Disjunctive FPT-Reductions and Sublogarithmic Exponent Collapse

This module develops parameter-bounded disjunctive fixed-parameter tractable reductions
(`CslibFrontier.ParameterizedComplexity.FPTDisjReducible`), hardness under disjunctive
FPT-reductions
(`CslibFrontier.ParameterizedComplexity.FPTDisjHard`), the Cai–Juedes sublogarithmic-exponent
fixed-parameter tractability collapse, and subexponential $o(k / \log_2 k)$ exponent transfers
across linear-parameter disjunctive FPT-reductions.

## Main definitions

* `CslibFrontier.ParameterizedComplexity.FPTDisjReducible`: parameter-bounded disjunctive
  FPT-reductions emitting at most $\mu(k)$ reduced instances of bounded parameter in FPT time.
* `CslibFrontier.ParameterizedComplexity.FPTDisjHard`: hardness of a parameterized problem for a
  parameterized complexity class under disjunctive FPT-reductions.
* `CslibFrontier.ParameterizedComplexity.IsSublogBaseTwo`: functions $s : \mathbb{N} \to \mathbb{R}$
  satisfying $s(n) = o(\log_2 n)$.
* `CslibFrontier.ParameterizedComplexity.IsLittleOKDivLog`: functions $s : \mathbb{N} \to
  \mathbb{R}$
  satisfying $s(k) = o(k / \log_2 k)$.

## Main results

* `CslibFrontier.ParameterizedComplexity.fptDisjReducible_of_fptReducible`: every many-one
  FPT-reduction is a disjunctive FPT-reduction with branch bound $1$.
* `CslibFrontier.ParameterizedComplexity.FPTDisjReducible.refl`,
  `CslibFrontier.ParameterizedComplexity.FPTDisjReducible.trans`: disjunctive FPT-reducibility is a
  preorder.
* `CslibFrontier.ParameterizedComplexity.FPTDisjReducible.mem_FPT`,
  `CslibFrontier.ParameterizedComplexity.FPTDisjReducible.mem_XP`: both `FPT` and `XP` are closed
  downward under disjunctive FPT-reductions.
* `CslibFrontier.ParameterizedComplexity.FPTDisjHard.of_fptHard`,
  `CslibFrontier.ParameterizedComplexity.FPTDisjHard.trans`,
  `CslibFrontier.ParameterizedComplexity.FPTDisjHard.subset_FPT`: transfer and `FPT`-collapse rules
  for
  disjunctive FPT-hardness.
* `CslibFrontier.ParameterizedComplexity.two_rpow_le_fpt_of_isSublogBaseTwo`,
  `CslibFrontier.ParameterizedComplexity.mem_FPT_of_decidableInExpTime_sublog`,
  `CslibFrontier.ParameterizedComplexity.exists_fpt_decider_of_decidableInExpTime_sublog`: the
  Cai–Juedes sublogarithmic exponent collapse
  $2^{\delta \cdot f(k) \cdot o(\log_2 n)} \le F(k) \cdot (L + 1)$.
* `CslibFrontier.ParameterizedComplexity.isLittleOKDivLog_sup_linear`,
  `CslibFrontier.ParameterizedComplexity.decidableInTimeO_of_fptDisj_subexp`: transfer of
  $f(r) \cdot (M + 1)^{o(r / \log_2 r)} \cdot (|y| + 1)^e$ algorithms across linear-parameter
  disjunctive FPT-reductions.
-/

public section

namespace CslibFrontier.ParameterizedComplexity

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Disjunctive FPT-Reductions and Closure of `FPT` / `XP` -/

/-- **Parameter-bounded disjunctive FPT-reducibility**: `A` disjunctively FPT-reduces to `B` when
an FPT-time transducer `f : α → List β` produces at most `μ (κA a)` instances of `B`, each of
parameter at most `h (κA a)`, such that `a ∈ A` if and only if at least one `b ∈ f a` belongs to
`B`. -/
@[expose]
def FPTDisjReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → List β, ComputableInFPTTime f encA (encList encB) κA ∧
    (∃ μ h : ℕ → ℕ, (∀ a, (f a).length ≤ μ (κA a)) ∧
      ∀ a, ∀ b ∈ f a, κB b ≤ h (κA a)) ∧
    ∀ a, a ∈ A ↔ ∃ b ∈ f a, b ∈ B

/-- **Hardness under disjunctive FPT-reductions** for a parameterized complexity class `𝒞`. -/
@[expose]
def FPTDisjHard (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)) {β : Type}
    (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α), A ∈ 𝒞 encA κA →
    FPTDisjReducible encA enc κA κ A B

private theorem le_sum_range_succ {f : ℕ → ℕ} {i k : ℕ} (h : i ≤ k) :
    f i ≤ ∑ j ∈ Finset.range (k + 1), f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

private def FPTBounded {α : Type} (encA : α ↪ List Bool) (κ : α → ℕ) (g : α → ℕ) : Prop :=
  ∃ (F : ℕ → ℕ) (c : ℕ), ∀ a, g a ≤ F (κ a) * ((encA a).length + 1) ^ c

private theorem FPTBounded.const {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ} (K : ℕ) :
    FPTBounded encA κ (fun _ => K) :=
  ⟨fun _ => K, 0, fun _ => by simp⟩

private theorem FPTBounded.param {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ} (h : ℕ → ℕ) :
    FPTBounded encA κ (fun a => h (κ a)) :=
  ⟨h, 0, fun _ => by simp⟩

private theorem FPTBounded.len {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ} :
    FPTBounded encA κ (fun a => (encA a).length) :=
  ⟨fun _ => 1, 1, fun _ => by simp⟩

private theorem FPTBounded.mono {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ}
    {g₁ g₂ : α → ℕ} (hle : ∀ a, g₁ a ≤ g₂ a) (h₂ : FPTBounded encA κ g₂) :
    FPTBounded encA κ g₁ := by
  obtain ⟨F, c, hc⟩ := h₂
  exact ⟨F, c, fun a => (hle a).trans (hc a)⟩

private theorem FPTBounded.add {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ}
    {g₁ g₂ : α → ℕ} (h₁ : FPTBounded encA κ g₁) (h₂ : FPTBounded encA κ g₂) :
    FPTBounded encA κ (fun a => g₁ a + g₂ a) := by
  obtain ⟨F₁, c₁, hc₁⟩ := h₁
  obtain ⟨F₂, c₂, hc₂⟩ := h₂
  refine ⟨fun k => F₁ k + F₂ k, c₁ + c₂, fun a => ?_⟩
  have hp₁ : ((encA a).length + 1) ^ c₁ ≤ ((encA a).length + 1) ^ (c₁ + c₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
  have hp₂ : ((encA a).length + 1) ^ c₂ ≤ ((encA a).length + 1) ^ (c₁ + c₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hc₁ a).trans (Nat.mul_le_mul_left _ hp₁))
    ((hc₂ a).trans (Nat.mul_le_mul_left _ hp₂))

private theorem FPTBounded.mul {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ}
    {g₁ g₂ : α → ℕ} (h₁ : FPTBounded encA κ g₁) (h₂ : FPTBounded encA κ g₂) :
    FPTBounded encA κ (fun a => g₁ a * g₂ a) := by
  obtain ⟨F₁, c₁, hc₁⟩ := h₁
  obtain ⟨F₂, c₂, hc₂⟩ := h₂
  refine ⟨fun k => F₁ k * F₂ k, c₁ + c₂, fun a => ?_⟩
  calc g₁ a * g₂ a
      ≤ (F₁ (κ a) * ((encA a).length + 1) ^ c₁) *
          (F₂ (κ a) * ((encA a).length + 1) ^ c₂) := Nat.mul_le_mul (hc₁ a) (hc₂ a)
    _ = F₁ (κ a) * F₂ (κ a) * ((encA a).length + 1) ^ (c₁ + c₂) := by
        rw [Nat.pow_add]; ring

private theorem FPTBounded.pow_const {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ}
    {g : α → ℕ} (hg : FPTBounded encA κ g) (d : ℕ) :
    FPTBounded encA κ (fun a => (g a) ^ d) := by
  obtain ⟨F, c, hc⟩ := hg
  refine ⟨fun k => (F k) ^ d, c * d, fun a => ?_⟩
  calc (g a) ^ d
      ≤ (F (κ a) * ((encA a).length + 1) ^ c) ^ d := Nat.pow_le_pow_left (hc a) d
    _ = (F (κ a)) ^ d * ((encA a).length + 1) ^ (c * d) := by
        rw [Nat.mul_pow, ← Nat.pow_mul]

private theorem exists_computableInO_of_fptTime {α β : Type} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ}
    (h : ComputableInFPTTime f encA encB κ) :
    ∃ (F : ℕ → ℕ) (c : ℕ), ComputableInO f encA encB
      (fun a => F (κ a) * ((encA a).length + 1) ^ c)
      (fun a => F (κ a) * ((encA a).length + 1) ^ c) := by
  obtain ⟨F, c, hc⟩ := h
  exact ⟨F, c, .of_bounds hc 1 (fun _ => by omega) (fun _ => by omega)
    fun a => (hc.length_le a).trans (by omega)⟩

private theorem length_encList_drop_le {β : Type} (encB : β ↪ List Bool) :
    ∀ (L : List β) (j : ℕ), (encList encB (L.drop j)).length ≤ (encList encB L).length
  | [], _ => by simp
  | _ :: _, 0 => le_rfl
  | _ :: bs, j + 1 =>
    (length_encList_drop_le encB bs j).trans (by simp [encList_cons])

private theorem length_enc_mem_le_encList {β : Type} (encB : β ↪ List Bool) :
    ∀ {L : List β} {b : β}, b ∈ L → (encB b).length ≤ (encList encB L).length
  | _ :: bs, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hmem
    · simp only [encList_cons, List.length_append, length_frame]
      omega
    · exact (length_enc_mem_le_encList encB hmem).trans (by simp [encList_cons])

/-- Every many-one FPT-reduction is a disjunctive FPT-reduction emitting a singleton list. -/
theorem fptDisjReducible_of_fptReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ} {A : Set α} {B : Set β}
    (h : FPTReducible encA encB κA κB A B) :
    FPTDisjReducible encA encB κA κB A B := by
  obtain ⟨f, ⟨hf, hκ, hhκ⟩, hfA⟩ := h
  have hsingle : ComputableInPolyTime (fun b : β => [b]) encB (encList encB) :=
    (ComputableInPolyTime.cons encB).comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const []))
  refine ⟨fun a => [f a], (hsingle.computableInFPTTime κB).comp hf hhκ,
    ⟨fun _ => 1, hκ, fun _ => le_rfl, fun a b hb => by
      obtain rfl := List.mem_singleton.mp hb
      exact hhκ a⟩,
    fun a => by simp [hfA a]⟩

/-- Disjunctive FPT-reducibility is reflexive. -/
@[refl]
theorem FPTDisjReducible.refl {α : Type} (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α) :
    FPTDisjReducible encA encA κA κA A A :=
  fptDisjReducible_of_fptReducible (FPTReducible.refl encA κA A)

section ListMachines

private abbrev AnyState (β : Type) : Type := List β × Bool

private def encAnyState {β : Type} (encB : β ↪ List Bool) : AnyState β ↪ List Bool :=
  encPair (encList encB) encBool

private def anyStep {β : Type} (b₀ : β) (g : β → Bool) (s : AnyState β) : AnyState β :=
  if s.1.isEmpty then s else (s.1.tail, s.2 || g (s.1.headD b₀))

private theorem iterate_anyStep {β : Type} (b₀ : β) (g : β → Bool) :
    ∀ (L : List β) (acc : Bool) (j : ℕ),
      (anyStep b₀ g)^[j] (L, acc) = (L.drop j, acc || (L.take j).any g)
  | L, acc, 0 => by simp
  | [], acc, j + 1 => by
    rw [Function.iterate_succ_apply, anyStep]
    simp [iterate_anyStep b₀ g [] acc j]
  | b :: bs, acc, j + 1 => by
    rw [Function.iterate_succ_apply, anyStep]
    simpa [Bool.or_assoc] using iterate_anyStep b₀ g bs (acc || g b) j

open ComputableInPolyTime in
/-- Evaluating `L.any g` on a framed list `L : List β` using a machine `g : β → Bool` with clock
`t` runs in `O((L.length + 1) * ((|encList L| + 1) ^ D + leafBound L))` steps. -/
private theorem exists_computableInO_listAny {β : Type} {encB : β ↪ List Bool}
    {g : β → Bool} {t : β → ℕ} (hg : ComputableInO g encB encBool t t) :
    ∃ D : ℕ, ∀ (leafBound : List β → ℕ),
      (∀ L, ∀ b ∈ L, t b ≤ leafBound L) →
      ComputableInO (fun L : List β => L.any g) (encList encB) encBool
        (fun L => (L.length + 1) * (((encList encB L).length + 1) ^ D + leafBound L))
        (fun L => (L.length + 1) * (((encList encB L).length + 1) ^ D + leafBound L)) := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
  · refine ⟨1, fun leafBound _ => ?_⟩
    have heq : (fun L : List β => L.any g) = fun _ => false := by
      funext L
      cases L with
      | nil => rfl
      | cons b _ => exact isEmptyElim b
    rw [heq]
    refine (ComputableInO.const false).mono 1 (fun L => ?_) (fun L => ?_)
    all_goals
      calc (encList encB L).length
          ≤ ((encList encB L).length + 1) ^ 1 + leafBound L := by simp; omega
        _ ≤ (L.length + 1) * (((encList encB L).length + 1) ^ 1 + leafBound L) :=
            Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        _ ≤ 1 * ((L.length + 1) * (((encList encB L).length + 1) ^ 1 + leafBound L) + 1) := by
            omega
  · obtain ⟨dE, _, hEmpty⟩ := (show ComputableInPolyTime (fun s : AnyState β => s.1.isEmpty)
      (encAnyState encB) encBool by unfold encAnyState; fun_prop).exists_degree
    obtain ⟨dT, _, hTail⟩ := (show ComputableInPolyTime (fun s : AnyState β => s.1.tail)
      (encAnyState encB) (encList encB) by unfold encAnyState; fun_prop).exists_degree
    obtain ⟨dH, _, hHead⟩ := (show ComputableInPolyTime (fun s : AnyState β => s.1.headD b₀)
      (encAnyState encB) encB by unfold encAnyState; fun_prop).exists_degree
    obtain ⟨dB, _, hAcc⟩ := (show ComputableInPolyTime (fun s : AnyState β => s.2)
      (encAnyState encB) encBool by unfold encAnyState; fun_prop).exists_degree
    obtain ⟨dO, _, hOr⟩ := bool_or.exists_degree
    obtain ⟨dN, _, hRounds⟩ := (unary_to_binary.comp (length_list encB)).exists_degree
    obtain ⟨dI, _, hInit⟩ :=
      (show ComputableInPolyTime (fun L : List β => ((L, false) : AnyState β))
      (encList encB) (encAnyState encB) by unfold encAnyState; fun_prop).exists_degree
    set dStep := dE + dT + dH + dB + 2
    have hBr : ComputableInO (fun s : AnyState β => (s.1.tail, s.2 || g (s.1.headD b₀)))
        (encAnyState encB) (encAnyState encB)
        (fun s => ((encAnyState encB s).length + 1) ^ dStep + t (s.1.headD b₀))
        (fun s => ((encAnyState encB s).length + 1) ^ dStep + t (s.1.headD b₀)) := by
      have raw := (hTail.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO.prod
        (hOr.inO.comp ((hAcc.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO.prod
          (hg.comp (hHead.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO)))
      refine (raw.mono (5 ^ dO + 4) (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl
      all_goals
        simp only [Function.comp_apply,
          show ∀ p : Bool × Bool, (encPair encBool encBool p).length = 4 from fun _ => by simp]
        have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
        generalize ((encAnyState encB s).length + 1) ^ dStep = P,
          t (s.1.headD b₀) = T, (4 + 1) ^ dO = F at hF ⊢
        nlinarith
    have hStep : ComputableInO (anyStep b₀ g) (encAnyState encB) (encAnyState encB)
        (fun s => ((encAnyState encB s).length + 1) ^ dStep +
          if s.1.isEmpty then 0 else t (s.1.headD b₀))
        (fun s => ((encAnyState encB s).length + 1) ^ dStep +
          if s.1.isEmpty then 0 else t (s.1.headD b₀)) := by
      have raw := (hEmpty.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO.ite
        (ComputableInO.id' (encMid := encAnyState encB)) hBr
      refine (raw.mono 4 (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl
      all_goals
        have hL1 : (encAnyState encB s).length ≤ ((encAnyState encB s).length + 1) ^ dStep :=
          (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
        split_ifs <;> omega
    set D := dStep + dN + dI + dB + 4
    refine ⟨D, fun leafBound hleaf => ?_⟩
    have hst_len (L : List β) (k : ℕ) :
        (encAnyState encB ((anyStep b₀ g)^[k] (L, false))).length ≤
          2 * (encList encB L).length + 4 := by
      rw [iterate_anyStep, encAnyState, length_encPair]
      have hd := length_encList_drop_le encB L k
      simp only [encBool_apply, List.length_singleton]
      omega
    have hround (L : List β) (k : ℕ) (_ : k ≤ L.length) :
        ((encAnyState encB ((anyStep b₀ g)^[k] (L, false))).length + 1) ^ dStep +
          (if ((anyStep b₀ g)^[k] (L, false)).1.isEmpty then 0
           else t (((anyStep b₀ g)^[k] (L, false)).1.headD b₀)) ≤
          (2 * (encList encB L).length + 5) ^ dStep + leafBound L := by
      refine Nat.add_le_add (Nat.pow_le_pow_left (Nat.add_le_add_right (hst_len L k) 1) _) ?_
      rw [iterate_anyStep]
      dsimp only
      cases hdrop : L.drop k with
      | nil => simp
      | cons b bs =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons]
        exact hleaf L b ((List.drop_subset k L) (by simp [hdrop]))
    have hit := hAcc.inO.comp (ComputableInO.iterate hRounds.inO hInit.inO hStep
      hround hround (fun L k _ => hst_len L k))
    have heq : ((fun s : AnyState β => s.2) ∘
        fun x : List β => (anyStep b₀ g)^[x.length] (x, false)) =
        fun L : List β => L.any g := by
      funext L
      dsimp only [Function.comp_apply]
      rw [iterate_anyStep, List.take_length, Bool.false_or]
    have hcnt_len (L : List β) : (encNat L.length).length ≤ (encList encB L).length + 1 := by
      have h1 : L.length ≤ (encList encB L).length := length_le_length_encList encB L
      have h2 : (encNat L.length).length ≤ L.length + 1 := by
        rcases L.length with _ | m
        · simp
        · exact (length_encNat_mono (Nat.lt_two_pow_self (n := m + 1)).le).trans_eq
            (length_encNat_two_pow (m + 1))
      omega
    refine heq ▸ hit.mono (6 ^ D) (fun L => ?_) (fun L => ?_)
    all_goals
      dsimp only [Function.comp_apply]
      set M := (encList encB L).length
      have h5 : (2 * M + 5) ≤ 5 * (M + 1) := by omega
      have hpow_step : (2 * M + 5) ^ dStep ≤ 5 ^ D * (M + 1) ^ D := by
        calc (2 * M + 5) ^ dStep ≤ (5 * (M + 1)) ^ dStep := Nat.pow_le_pow_left h5 _
          _ = 5 ^ dStep * (M + 1) ^ dStep := Nat.mul_pow _ _ _
          _ ≤ 5 ^ D * (M + 1) ^ D := Nat.mul_le_mul
              (Nat.pow_le_pow_right (by norm_num) (by omega))
              (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have hpow_B : (2 * M + 5) ^ dB ≤ 5 ^ D * (M + 1) ^ D := by
        calc (2 * M + 5) ^ dB ≤ (5 * (M + 1)) ^ dB := Nat.pow_le_pow_left h5 _
          _ = 5 ^ dB * (M + 1) ^ dB := Nat.mul_pow _ _ _
          _ ≤ 5 ^ D * (M + 1) ^ D := Nat.mul_le_mul
              (Nat.pow_le_pow_right (by norm_num) (by omega))
              (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have hfin_B :
          ((encAnyState encB ((anyStep b₀ g)^[L.length] (L, false))).length + 1) ^ dB ≤
            5 ^ D * (M + 1) ^ D :=
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hst_len L L.length) 1) dB).trans hpow_B
      have hpow_N : (M + 1) ^ dN ≤ (M + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hpow_I : (M + 1) ^ dI ≤ (M + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hpow_2 : ((encNat L.length).length + 1) ^ 2 ≤ 4 * (M + 1) ^ D := by
        have hc := hcnt_len L
        calc ((encNat L.length).length + 1) ^ 2 ≤ (2 * (M + 1)) ^ 2 :=
              Nat.pow_le_pow_left (by omega) 2
          _ = 4 * (M + 1) ^ 2 := by ring
          _ ≤ 4 * (M + 1) ^ D := Nat.mul_le_mul_left 4
              (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have hM_le : 2 * M + 4 ≤ 4 * (M + 1) ^ D := by
        calc 2 * M + 4 ≤ 4 * (M + 1) ^ 1 := by rw [pow_one]; omega
          _ ≤ 4 * (M + 1) ^ D := Nat.mul_le_mul_left 4
              (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have hcnt1 : (encNat L.length).length ≤ 2 * (M + 1) ^ D := by
        have hc := hcnt_len L
        calc (encNat L.length).length ≤ 2 * (M + 1) ^ 1 := by rw [pow_one]; omega
          _ ≤ 2 * (M + 1) ^ D := Nat.mul_le_mul_left 2
              (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have h6 : 2 * 5 ^ D + 12 ≤ 6 ^ D := by
        have : 2 * 5 ^ 4 + 12 ≤ 6 ^ 4 := by decide
        have hmul : 6 ^ (D - 4) * 6 ^ 4 = 6 ^ D := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        have h5mul : 5 ^ D = 5 ^ (D - 4) * 5 ^ 4 := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        have hle56 : 5 ^ (D - 4) ≤ 6 ^ (D - 4) := Nat.pow_le_pow_left (by omega) _
        have hpos6 : 1 ≤ 6 ^ (D - 4) := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have hKpos : 0 < L.length + 1 := Nat.succ_pos L.length
      generalize (M + 1) ^ D = P, L.length + 1 = K, leafBound L = T at *
      have hPK : P ≤ K * P := Nat.le_mul_of_pos_left P hKpos
      have hTK : T ≤ K * T := Nat.le_mul_of_pos_left T hKpos
      have hStep_KP : (2 * M + 5) ^ dStep ≤ 5 ^ D * (K * P) := by
        calc (2 * M + 5) ^ dStep ≤ 5 ^ D * P := hpow_step
          _ ≤ K * (5 ^ D * P) := Nat.le_mul_of_pos_left _ hKpos
          _ = 5 ^ D * (K * P) := by ring
      have hfin_KP : ((encAnyState encB ((anyStep b₀ g)^[L.length] (L, false))).length + 1) ^ dB ≤
          5 ^ D * (K * P) := by
        calc _ ≤ 5 ^ D * P := hfin_B
          _ ≤ K * (5 ^ D * P) := Nat.le_mul_of_pos_left _ hKpos
          _ = 5 ^ D * (K * P) := by ring
      have hKsum : K * ((2 * M + 5) ^ dStep + T + (2 * M + 4) +
            ((encNat L.length).length + 1) ^ 2) ≤
          5 ^ D * (K * P) + 8 * (K * P) + K * T := by
        calc K * ((2 * M + 5) ^ dStep + T + (2 * M + 4) + ((encNat L.length).length + 1) ^ 2)
            ≤ K * (5 ^ D * P + 8 * P + T) := Nat.mul_le_mul_left K (by omega)
          _ = 5 ^ D * (K * P) + 8 * (K * P) + K * T := by ring
      have hK6 : 2 * (5 ^ D * (K * P)) + 12 * (K * P) ≤ 6 ^ D * (K * P) := by
        calc 2 * (5 ^ D * (K * P)) + 12 * (K * P)
            = (2 * 5 ^ D + 12) * (K * P) := by ring
          _ ≤ 6 ^ D * (K * P) := Nat.mul_le_mul_right _ h6
      have hKT6 : K * T ≤ 6 ^ D * (K * T) :=
        Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by omega))
      have hExpand : 6 ^ D * (K * (P + T) + 1) = 6 ^ D * (K * P) + 6 ^ D * (K * T) + 6 ^ D := by
        ring
      rw [hExpand]
      omega

private abbrev FlatState (β γ : Type) : Type := List β × List γ

private def encFlatState {β γ : Type} (encB : β ↪ List Bool) (encC : γ ↪ List Bool) :
    FlatState β γ ↪ List Bool :=
  encPair (encList encB) (encList encC)

private def flatStep {β γ : Type} (b₀ : β) (g : β → List γ) (s : FlatState β γ) :
    FlatState β γ :=
  if s.1.isEmpty then s else (s.1.tail, s.2 ++ g (s.1.headD b₀))

private theorem iterate_flatStep {β γ : Type} (b₀ : β) (g : β → List γ) :
    ∀ (L : List β) (acc : List γ) (j : ℕ),
      (flatStep b₀ g)^[j] (L, acc) = (L.drop j, acc ++ (L.take j).flatMap g)
  | L, acc, 0 => by simp
  | [], acc, j + 1 => by
    rw [Function.iterate_succ_apply, flatStep]
    simp [iterate_flatStep b₀ g [] acc j]
  | b :: bs, acc, j + 1 => by
    rw [Function.iterate_succ_apply, flatStep]
    simpa [List.append_assoc] using iterate_flatStep b₀ g bs (acc ++ g b) j

private theorem length_encList_flatMap_le {β γ : Type} (encC : γ ↪ List Bool) (g : β → List γ) :
    ∀ (xs : List β) (m : ℕ), (∀ b ∈ xs, (encList encC (g b)).length ≤ m) →
      (encList encC (xs.flatMap g)).length ≤ xs.length * m
  | [], _, _ => by simp
  | b :: bs, m, hm => by
    simp only [List.flatMap_cons, encList_append, List.length_append, List.length_cons]
    have hb := hm b List.mem_cons_self
    have hbs := length_encList_flatMap_le encC g bs m fun x hx => hm x (List.mem_cons_of_mem _ hx)
    nlinarith

open ComputableInPolyTime in
/-- Disjunctive FPT-reductions compose via `List.flatMap`. -/
@[trans]
theorem FPTDisjReducible.trans {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ} {κC : γ → ℕ}
    {A : Set α} {B : Set β} {C : Set γ}
    (hAB : FPTDisjReducible encA encB κA κB A B)
    (hBC : FPTDisjReducible encB encC κB κC B C) :
    FPTDisjReducible encA encC κA κC A C := by
  obtain ⟨f₁, hf₁, ⟨μ₁, h₁, hμ₁, hh₁⟩, hf₁A⟩ := hAB
  obtain ⟨f₂, hf₂, ⟨μ₂, h₂, hμ₂, hh₂⟩, hf₂B⟩ := hBC
  set μ₂' : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (h₁ k + 1), μ₂ j
  set h₂' : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (h₁ k + 1), h₂ j
  refine ⟨fun a => (f₁ a).flatMap f₂, ?_,
    ⟨fun k => μ₁ k * μ₂' k, h₂', fun a => ?_, fun a c hc => ?_⟩,
    fun a => ?_⟩
  · rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
    · have heq : (fun a : α => (f₁ a).flatMap f₂) = fun _ => [] := by
        funext a
        cases f₁ a with
        | nil => rfl
        | cons b _ => exact isEmptyElim b
      rw [heq]
      exact (const []).computableInFPTTime κA
    · obtain ⟨F₁, c₁, hf₁O⟩ := exists_computableInO_of_fptTime hf₁
      have ⟨l₁, _, hl₁⟩ := hf₁O
      obtain ⟨F₂, c₂, hf₂O⟩ := exists_computableInO_of_fptTime hf₂
      have ⟨l₂, _, hl₂⟩ := hf₂O
      set F₂' : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (h₁ k + 1), F₂ j
      obtain ⟨dE, _, hEmpty⟩ := (show ComputableInPolyTime (fun s : FlatState β γ => s.1.isEmpty)
        (encFlatState encB encC) encBool by unfold encFlatState; fun_prop).exists_degree
      obtain ⟨dT, _, hTail⟩ := (show ComputableInPolyTime (fun s : FlatState β γ => s.1.tail)
        (encFlatState encB encC) (encList encB) by unfold encFlatState; fun_prop).exists_degree
      obtain ⟨dH, _, hHead⟩ := (show ComputableInPolyTime (fun s : FlatState β γ => s.1.headD b₀)
        (encFlatState encB encC) encB by unfold encFlatState; fun_prop).exists_degree
      obtain ⟨dA, _, hAcc⟩ := (show ComputableInPolyTime (fun s : FlatState β γ => s.2)
        (encFlatState encB encC) (encList encC) by unfold encFlatState; fun_prop).exists_degree
      obtain ⟨dApp, _, hApp⟩ := (listAppend encC).exists_degree
      obtain ⟨dN, _, hRounds⟩ := (unary_to_binary.comp (length_list encB)).exists_degree
      obtain ⟨dI, _, hInit⟩ := (show ComputableInPolyTime
        (fun L : List β => ((L, []) : FlatState β γ))
        (encList encB) (encFlatState encB encC) by unfold encFlatState; fun_prop).exists_degree
      set dStep := dE + dT + dH + dA + 2
      have hAppStep : ComputableInO
          (fun s : FlatState β γ => (s.1.tail, s.2 ++ f₂ (s.1.headD b₀)))
          (encFlatState encB encC) (encFlatState encB encC)
          (fun s => (((encFlatState encB encC s).length + 1) ^ dStep +
            F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂ +
            (encList encC (f₂ (s.1.headD b₀))).length + 1) ^ (dApp + 1))
          (fun s => (((encFlatState encB encC s).length + 1) ^ dStep +
            F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂ +
            (encList encC (f₂ (s.1.headD b₀))).length + 1) ^ (dApp + 1)) := by
        have hgHead := hf₂O.comp (hHead.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO
        have hPair := (hAcc.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO.prod hgHead
        have hRhs := hApp.inO.comp hPair
        have hAll := (hTail.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO.prod hRhs
        refine (hAll.mono (4 ^ (dApp + 2)) (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl
        all_goals
          simp only [Function.comp_apply, length_encPair]
          have hacc_le : (encList encC s.2).length ≤ (encFlatState encB encC s).length := by
            simp [encFlatState]
          set X := ((encFlatState encB encC s).length + 1) ^ dStep +
            F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂ +
            (encList encC (f₂ (s.1.headD b₀))).length + 1
          have hX1 : (encList encC s.2).length ≤ X :=
            hacc_le.trans ((show _ ≤ (encFlatState encB encC s).length + 1 by omega).trans
              ((Nat.le_self_pow (n := dStep) (by omega) _).trans (by omega)))
          have hpair_le : 2 * (encList encC s.2).length + 1 +
              (encList encC (f₂ (s.1.headD b₀))).length + 1 ≤ 4 * X := by omega
          have hpowZ : (2 * (encList encC s.2).length + 1 +
              (encList encC (f₂ (s.1.headD b₀))).length + 1) ^ dApp ≤
              4 ^ dApp * X ^ (dApp + 1) :=
            ((Nat.pow_le_pow_left hpair_le _).trans_eq (Nat.mul_pow _ _ _)).trans
              (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)))
          have hXd : X ≤ X ^ (dApp + 1) := Nat.le_self_pow (n := dApp + 1) (by omega) _
          have h3X : ((encFlatState encB encC s).length + 1) ^ dStep +
              (((encFlatState encB encC s).length + 1) ^ dStep +
                (((encFlatState encB encC s).length + 1) ^ dStep +
                  F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂)) ≤
              3 * X ^ (dApp + 1) := by
            calc _ ≤ 3 * X := by omega
              _ ≤ 3 * X ^ (dApp + 1) := Nat.mul_le_mul_left 3 hXd
          have h4 : 4 ^ dApp + 4 ≤ 4 ^ (dApp + 2) := by
            have hmul4 : 4 ^ dApp * 16 = 4 ^ (dApp + 2) := by rw [Nat.pow_add]
            have hpos4 : 1 ≤ 4 ^ dApp := Nat.one_le_pow _ _ (by omega)
            omega
          generalize X ^ (dApp + 1) = Z at hpowZ h3X ⊢
          have hZsum : 4 ^ dApp * Z + 4 * Z ≤ 4 ^ (dApp + 2) * Z := by
            simpa [Nat.add_mul] using Nat.mul_le_mul_right Z h4
          rw [Nat.mul_add]
          omega
      have hStep : ComputableInO (flatStep b₀ f₂) (encFlatState encB encC) (encFlatState encB encC)
          (fun s => if s.1.isEmpty then ((encFlatState encB encC s).length + 1) ^ dStep
            else (((encFlatState encB encC s).length + 1) ^ dStep +
              F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂ +
              (encList encC (f₂ (s.1.headD b₀))).length + 1) ^ (dApp + 1))
          (fun s => if s.1.isEmpty then ((encFlatState encB encC s).length + 1) ^ dStep
            else (((encFlatState encB encC s).length + 1) ^ dStep +
              F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂ +
              (encList encC (f₂ (s.1.headD b₀))).length + 1) ^ (dApp + 1)) := by
        have raw := (hEmpty.mono (d' := dStep) (e' := _) (by omega) le_rfl).inO.ite
          (ComputableInO.id' (encMid := encFlatState encB encC)) hAppStep
        refine (raw.mono 3 (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl
        all_goals
          have hL1 : (encFlatState encB encC s).length ≤
              ((encFlatState encB encC s).length + 1) ^ dStep :=
            (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
          have hP1 : ((encFlatState encB encC s).length + 1) ^ dStep ≤
              (((encFlatState encB encC s).length + 1) ^ dStep +
                F₂ (κB (s.1.headD b₀)) * ((encB (s.1.headD b₀)).length + 1) ^ c₂ +
                (encList encC (f₂ (s.1.headD b₀))).length + 1) ^ (dApp + 1) :=
            (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
              ((Nat.le_add_right _ _).trans (Nat.le_self_pow (by omega) _)))
          split_ifs <;> omega
      set L₁ : α → ℕ := fun a => l₁ * (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + 1)
      set m₂ : α → ℕ := fun a => l₂ * (F₂' (κA a) * (L₁ a + 1) ^ c₂ + 1)
      set stBound : α → ℕ := fun a => 2 * L₁ a + μ₁ (κA a) * m₂ a + 4
      set rdBound : α → ℕ := fun a =>
        ((stBound a + 1) ^ dStep + F₂' (κA a) * (L₁ a + 1) ^ c₂ + m₂ a + 1) ^ (dApp + 1)
      have hL₁ (a : α) : (encList encB (f₁ a)).length ≤ L₁ a := hl₁ a
      have hm₂ (a : α) (b : β) (hb : b ∈ f₁ a) : (encList encC (f₂ b)).length ≤ m₂ a := by
        have hb_len : (encB b).length ≤ L₁ a :=
          (length_enc_mem_le_encList encB hb).trans (hL₁ a)
        have hF₂ : F₂ (κB b) ≤ F₂' (κA a) := le_sum_range_succ (hh₁ a b hb)
        exact (hl₂ b).trans (Nat.mul_le_mul_left l₂ (Nat.add_le_add_right
          (Nat.mul_le_mul hF₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hb_len 1) _)) 1))
      have hst_a (a : α) (k : ℕ) (_ : k ≤ (f₁ a).length) :
          (encFlatState encB encC ((flatStep b₀ f₂)^[k] (f₁ a, []))).length ≤ stBound a := by
        rw [iterate_flatStep, List.nil_append, encFlatState, length_encPair]
        dsimp only [stBound]
        have hd := (length_encList_drop_le encB (f₁ a) k).trans (hL₁ a)
        have hfl := length_encList_flatMap_le encC f₂ ((f₁ a).take k) (m₂ a)
          fun b hb => hm₂ a b (List.take_subset k (f₁ a) hb)
        have htk : ((f₁ a).take k).length ≤ μ₁ (κA a) :=
          (List.length_take_le' k (f₁ a)).trans (hμ₁ a)
        have hmul := Nat.mul_le_mul_right (m₂ a) htk
        omega
      have hrd_a (a : α) (k : ℕ) (hk : k ≤ (f₁ a).length) :
          (if ((flatStep b₀ f₂)^[k] (f₁ a, [])).1.isEmpty then
             ((encFlatState encB encC ((flatStep b₀ f₂)^[k] (f₁ a, []))).length + 1) ^ dStep
           else
             (((encFlatState encB encC ((flatStep b₀ f₂)^[k] (f₁ a, []))).length + 1) ^ dStep +
               F₂ (κB (((flatStep b₀ f₂)^[k] (f₁ a, [])).1.headD b₀)) *
                 ((encB (((flatStep b₀ f₂)^[k] (f₁ a, [])).1.headD b₀)).length + 1) ^ c₂ +
               (encList encC (f₂ (((flatStep b₀ f₂)^[k] (f₁ a, [])).1.headD b₀))).length + 1) ^
                 (dApp + 1)) ≤ rdBound a := by
        have hst := hst_a a k hk
        rw [iterate_flatStep] at hst ⊢
        dsimp only
        cases hdrop : (f₁ a).drop k with
        | nil =>
          rw [hdrop] at hst
          simp only [List.isEmpty_nil, ↓reduceIte]
          exact (Nat.pow_le_pow_left (Nat.add_le_add_right hst 1) _).trans
            ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
              ((Nat.le_add_right _ _).trans (Nat.le_self_pow (by omega) _))))
        | cons b bs =>
          rw [hdrop] at hst
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.headD_cons]
          have hb : b ∈ f₁ a := (List.drop_subset k (f₁ a)) (by simp [hdrop])
          have hb_len : (encB b).length ≤ L₁ a :=
            (length_enc_mem_le_encList encB hb).trans (hL₁ a)
          have hF₂ : F₂ (κB b) ≤ F₂' (κA a) := le_sum_range_succ (hh₁ a b hb)
          have hm := hm₂ a b hb
          refine Nat.pow_le_pow_left ?_ _
          have h1 := Nat.pow_le_pow_left (Nat.add_le_add_right hst 1) dStep
          have h2 := Nat.mul_le_mul hF₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hb_len 1) c₂)
          omega
      have hit := hAcc.inO.comp (ComputableInO.iterate
        (hRounds.inO.comp hf₁O) (hInit.inO.comp hf₁O) hStep hrd_a hrd_a hst_a)
      have heq : ((fun s : FlatState β γ => s.2) ∘
          fun a : α => (flatStep b₀ f₂)^[(f₁ a).length] (f₁ a, [])) =
          fun a => (f₁ a).flatMap f₂ := by
        funext a
        dsimp only [Function.comp_apply]
        rw [iterate_flatStep, List.take_length, List.nil_append]
      have hcnt (a : α) : (encNat (f₁ a).length).length ≤ μ₁ (κA a) + 1 := by
        have hlen := hμ₁ a
        rcases heq_l : (f₁ a).length with _ | m
        · simp
        · exact ((length_encNat_mono (Nat.lt_two_pow_self (n := m + 1)).le).trans_eq
            (length_encNat_two_pow (m + 1))).trans (by omega)
      have hb_f₁ : FPTBounded encA κA (fun a => F₁ (κA a) * ((encA a).length + 1) ^ c₁) :=
        ⟨F₁, c₁, fun _ => le_rfl⟩
      have hb_L₁ : FPTBounded encA κA L₁ :=
        .mul (.const l₁) (.add hb_f₁ (.const 1))
      have hb_m₂ : FPTBounded encA κA m₂ :=
        .mul (.const l₂) (.add (.mul (.param F₂') (.pow_const (.add hb_L₁ (.const 1)) c₂))
          (.const 1))
      have hb_st : FPTBounded encA κA stBound :=
        .add (.add (.mul (.const 2) hb_L₁) (.mul (.param μ₁) hb_m₂)) (.const 4)
      have hb_rd : FPTBounded encA κA rdBound :=
        .pow_const (.add (.add (.add (.pow_const (.add hb_st (.const 1)) dStep)
          (.mul (.param F₂') (.pow_const (.add hb_L₁ (.const 1)) c₂))) hb_m₂) (.const 1)) (dApp + 1)
      have hb_enc₁ : FPTBounded encA κA (fun a => (encList encB (f₁ a)).length + 1) :=
        .mono (fun a => Nat.add_le_add_right (hL₁ a) 1) (.add hb_L₁ (.const 1))
      have hb_tot : FPTBounded encA κA (fun a =>
          (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + ((encList encB (f₁ a)).length + 1) ^ dN) +
          (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + ((encList encB (f₁ a)).length + 1) ^ dI) +
          (μ₁ (κA a) + 1) * (rdBound a + stBound a + (μ₁ (κA a) + 2) ^ 2) +
          (stBound a + 1) ^ dA) :=
        .add (.add (.add (.add hb_f₁ (.pow_const hb_enc₁ dN))
          (.add hb_f₁ (.pow_const hb_enc₁ dI)))
          (.mul (.param fun k => μ₁ k + 1)
            (.add (.add hb_rd hb_st) (.param fun k => (μ₁ k + 2) ^ 2))))
          (.pow_const (.add hb_st (.const 1)) dA)
      obtain ⟨F_tot, c_tot, hF_tot⟩ := hb_tot
      refine ComputableInO.computableInFPTTime (F := F_tot) (c := c_tot)
        (heq ▸ hit.mono_le (fun a => ?_) (fun a => ?_))
      · dsimp only [Function.comp_apply]
        have hlen := hμ₁ a
        have hc := hcnt a
        have hst_end : ((encFlatState encB encC
            ((flatStep b₀ f₂)^[(f₁ a).length] (f₁ a, []))).length + 1) ^ dA ≤
            (stBound a + 1) ^ dA :=
          Nat.pow_le_pow_left (Nat.add_le_add_right (hst_a a _ le_rfl) 1) dA
        have hmid : ((f₁ a).length + 1) *
            (rdBound a + stBound a + ((encNat (f₁ a).length).length + 1) ^ 2) ≤
            (μ₁ (κA a) + 1) * (rdBound a + stBound a + (μ₁ (κA a) + 2) ^ 2) :=
          Nat.mul_le_mul (Nat.add_le_add_right hlen 1)
            (Nat.add_le_add_left (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2) _)
        exact (by omega : _ ≤
          (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + ((encList encB (f₁ a)).length + 1) ^ dN) +
          (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + ((encList encB (f₁ a)).length + 1) ^ dI) +
          (μ₁ (κA a) + 1) * (rdBound a + stBound a + (μ₁ (κA a) + 2) ^ 2) +
          (stBound a + 1) ^ dA).trans (hF_tot a)
      · dsimp only [Function.comp_apply]
        have hc := hcnt a
        have hst_end : ((encFlatState encB encC
            ((flatStep b₀ f₂)^[(f₁ a).length] (f₁ a, []))).length + 1) ^ dA ≤
            (stBound a + 1) ^ dA :=
          Nat.pow_le_pow_left (Nat.add_le_add_right (hst_a a _ le_rfl) 1) dA
        have h1 : rdBound a + stBound a + (encNat (f₁ a).length).length ≤
            (μ₁ (κA a) + 1) * (rdBound a + stBound a + (μ₁ (κA a) + 2) ^ 2) := by
          have hle1 : (encNat (f₁ a).length).length ≤ (μ₁ (κA a) + 2) ^ 2 := by nlinarith
          exact (Nat.add_le_add_left hle1 _).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
        exact (by omega : _ ≤
          (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + ((encList encB (f₁ a)).length + 1) ^ dN) +
          (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + ((encList encB (f₁ a)).length + 1) ^ dI) +
          (μ₁ (κA a) + 1) * (rdBound a + stBound a + (μ₁ (κA a) + 2) ^ 2) +
          (stBound a + 1) ^ dA).trans (hF_tot a)
  · rw [List.length_flatMap]
    calc ((f₁ a).map fun b => (f₂ b).length).sum
        ≤ ((f₁ a).map fun b => (f₂ b).length).length • μ₂' (κA a) :=
          List.sum_le_length_nsmul _ _ fun x hx => by
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
            exact (hμ₂ b).trans (le_sum_range_succ (hh₁ a b hb))
      _ = (f₁ a).length * μ₂' (κA a) := by simp
      _ ≤ μ₁ (κA a) * μ₂' (κA a) := Nat.mul_le_mul_right _ (hμ₁ a)
  · obtain ⟨b, hb, hc'⟩ := List.mem_flatMap.mp hc
    exact (hh₂ b c hc').trans (le_sum_range_succ (hh₁ a b hb))
  · simp only [hf₁A a, List.mem_flatMap]
    exact ⟨fun ⟨b, hb, hbB⟩ => let ⟨c, hc, hcC⟩ := (hf₂B b).mp hbB; ⟨c, ⟨b, hb, hc⟩, hcC⟩,
      fun ⟨c, ⟨b, hb, hc⟩, hcC⟩ => ⟨b, hb, (hf₂B b).mpr ⟨c, hc, hcC⟩⟩⟩

/-- **`FPT` is closed downward under disjunctive FPT-reductions.** -/
theorem FPTDisjReducible.mem_FPT {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κA : α → ℕ} {κB : β → ℕ} {A : Set α} {B : Set β}
    (hAB : FPTDisjReducible encA encB κA κB A B) (hB : B ∈ FPT encB κB) :
    A ∈ FPT encA κA := by
  obtain ⟨f, hf, ⟨μ, h, hμ, hh⟩, hfA⟩ := hAB
  obtain ⟨g, hg, hgB⟩ := mem_FPT_iff_computableInFPTTime.mp hB
  obtain ⟨F₁, c₁, hfO⟩ := exists_computableInO_of_fptTime hf
  have ⟨l₁, _, hl₁⟩ := hfO
  obtain ⟨F₂, c₂, hgO⟩ := exists_computableInO_of_fptTime hg
  obtain ⟨D, hAny⟩ := exists_computableInO_listAny hgO
  set F₂' : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (h k + 1), F₂ j
  set L₁ : α → ℕ := fun a => l₁ * (F₁ (κA a) * ((encA a).length + 1) ^ c₁ + 1)
  let leafBound : List β → ℕ := fun L =>
    (L.map fun b => F₂ (κB b)).sum * ((encList encB L).length + 1) ^ c₂
  have hleaf (L : List β) (b : β) (hb : b ∈ L) :
      F₂ (κB b) * ((encB b).length + 1) ^ c₂ ≤ leafBound L := by
    refine Nat.mul_le_mul
      (List.le_sum_of_mem (List.mem_map_of_mem hb))
      (Nat.pow_le_pow_left (Nat.add_le_add_right (length_enc_mem_le_encList encB hb) 1) c₂)
  have hcomp := (hAny leafBound hleaf).comp hfO
  have hb_f₁ : FPTBounded encA κA (fun a => F₁ (κA a) * ((encA a).length + 1) ^ c₁) :=
    ⟨F₁, c₁, fun _ => le_rfl⟩
  have hb_L₁ : FPTBounded encA κA L₁ := .mul (.const l₁) (.add hb_f₁ (.const 1))
  have hb_leaf : FPTBounded encA κA (fun a => leafBound (f a)) := by
    refine .mono (fun a => ?_)
      (.mul (.mul (.param μ) (.param F₂')) (.pow_const (.add hb_L₁ (.const 1)) c₂))
    have hsum : ((f a).map fun b => F₂ (κB b)).sum ≤ μ (κA a) * F₂' (κA a) := by
      calc ((f a).map fun b => F₂ (κB b)).sum
          ≤ ((f a).map fun b => F₂ (κB b)).length • F₂' (κA a) :=
            List.sum_le_length_nsmul _ _ fun x hx => by
              obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
              exact le_sum_range_succ (hh a b hb)
        _ = (f a).length * F₂' (κA a) := by simp
        _ ≤ μ (κA a) * F₂' (κA a) := Nat.mul_le_mul_right _ (hμ a)
    exact Nat.mul_le_mul hsum (Nat.pow_le_pow_left (Nat.add_le_add_right (hl₁ a) 1) c₂)
  have hb_tot : FPTBounded encA κA (fun a =>
      F₁ (κA a) * ((encA a).length + 1) ^ c₁ +
        (μ (κA a) + 1) * ((L₁ a + 1) ^ D + leafBound (f a))) :=
    .add hb_f₁ (.mul (.param fun k => μ k + 1)
      (.add (.pow_const (.add hb_L₁ (.const 1)) D) hb_leaf))
  obtain ⟨F_tot, c_tot, hF_tot⟩ := hb_tot
  refine mem_FPT_iff_computableInFPTTime.mpr ⟨fun a => (f a).any g,
    ComputableInO.computableInFPTTime (F := F_tot) (c := c_tot)
      (hcomp.mono_le (fun a => ?_) (fun a => ?_)),
    fun a => by simp [hfA a, List.any_eq_true, ← hgB]⟩
  all_goals
    exact (Nat.add_le_add_left (Nat.mul_le_mul (Nat.add_le_add_right (hμ a) 1)
      (Nat.add_le_add_right (Nat.pow_le_pow_left (Nat.add_le_add_right (hl₁ a) 1) D) _)) _).trans
      (hF_tot a)

/-- **`XP` is closed downward under disjunctive FPT-reductions.** -/
theorem FPTDisjReducible.mem_XP {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κA : α → ℕ} {κB : β → ℕ} {A : Set α} {B : Set β}
    (hAB : FPTDisjReducible encA encB κA κB A B) (hB : B ∈ XP encB κB) :
    A ∈ XP encA κA := by
  obtain ⟨f, hf, ⟨μ, h, hμ, hh⟩, hfA⟩ := hAB
  obtain ⟨g, F₂, e₂, hgO, hgB⟩ := mem_XP_iff_exists_computableInO.mp hB
  obtain ⟨F₁, c₁, hfO⟩ := exists_computableInO_of_fptTime hf
  have ⟨l₁, _, hl₁⟩ := hfO
  obtain ⟨D, hAny⟩ := exists_computableInO_listAny hgO
  set F₂' : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (h k + 1), F₂ j
  set E₂' : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (h k + 1), e₂ j
  let leafBound : List β → ℕ := fun L =>
    (L.map fun b => F₂ (κB b)).sum *
      ((encList encB L).length + 1) ^ (L.map fun b => e₂ (κB b)).sum
  have hleaf (L : List β) (b : β) (hb : b ∈ L) :
      F₂ (κB b) * ((encB b).length + 1) ^ e₂ (κB b) ≤ leafBound L := by
    refine Nat.mul_le_mul
      (List.le_sum_of_mem (List.mem_map_of_mem hb))
      ((Nat.pow_le_pow_left (Nat.add_le_add_right (length_enc_mem_le_encList encB hb) 1) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _)
          (List.le_sum_of_mem (List.mem_map_of_mem hb))))
  have hcomp := (hAny leafBound hleaf).comp hfO
  set K₁ : ℕ → ℕ := fun k => (l₁ + 1) * (F₁ k + 1)
  set E_xp : ℕ → ℕ := fun k => c₁ + c₁ * (D + μ k * E₂' k)
  set F_xp : ℕ → ℕ := fun k =>
    F₁ k + (μ k + 1) * (K₁ k ^ D + μ k * F₂' k * K₁ k ^ (μ k * E₂' k))
  refine mem_XP_iff_exists_computableInO.mpr ⟨fun a => (f a).any g, F_xp, E_xp,
    hcomp.mono_le (fun a => ?_) (fun a => ?_),
    fun a => by simp [hfA a, List.any_eq_true, ← hgB]⟩
  all_goals
    set k := κA a
    set P₁ := ((encA a).length + 1) ^ c₁
    have hP₁ : 1 ≤ P₁ := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hL₁_le : (encList encB (f a)).length + 1 ≤ K₁ k * P₁ := by
      have : (encList encB (f a)).length ≤ l₁ * (F₁ k * P₁ + 1) := hl₁ a
      dsimp only [K₁]
      nlinarith [Nat.mul_le_mul_left l₁ hP₁, Nat.mul_le_mul_left (F₁ k) hP₁]
    have hsum_F : ((f a).map fun b => F₂ (κB b)).sum ≤ μ k * F₂' k := by
      calc ((f a).map fun b => F₂ (κB b)).sum
          ≤ ((f a).map fun b => F₂ (κB b)).length • F₂' k :=
            List.sum_le_length_nsmul _ _ fun x hx => by
              obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
              exact le_sum_range_succ (hh a b hb)
        _ = (f a).length * F₂' k := by simp
        _ ≤ μ k * F₂' k := Nat.mul_le_mul_right _ (hμ a)
    have hsum_e : ((f a).map fun b => e₂ (κB b)).sum ≤ μ k * E₂' k := by
      calc ((f a).map fun b => e₂ (κB b)).sum
          ≤ ((f a).map fun b => e₂ (κB b)).length • E₂' k :=
            List.sum_le_length_nsmul _ _ fun x hx => by
              obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
              exact le_sum_range_succ (hh a b hb)
        _ = (f a).length * E₂' k := by simp
        _ ≤ μ k * E₂' k := Nat.mul_le_mul_right _ (hμ a)
    have hD_pow : ((encList encB (f a)).length + 1) ^ D ≤
        K₁ k ^ D * ((encA a).length + 1) ^ E_xp k := by
      calc ((encList encB (f a)).length + 1) ^ D
          ≤ (K₁ k * P₁) ^ D := Nat.pow_le_pow_left hL₁_le D
        _ = K₁ k ^ D * ((encA a).length + 1) ^ (c₁ * D) := by rw [Nat.mul_pow, ← Nat.pow_mul]
        _ ≤ K₁ k ^ D * ((encA a).length + 1) ^ E_xp k := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [E_xp]; rw [Nat.mul_add]; omega))
    have hlf_pow : leafBound (f a) ≤
        μ k * F₂' k * K₁ k ^ (μ k * E₂' k) * ((encA a).length + 1) ^ E_xp k := by
      dsimp only [leafBound]
      calc ((f a).map fun b => F₂ (κB b)).sum *
            ((encList encB (f a)).length + 1) ^ ((f a).map fun b => e₂ (κB b)).sum
          ≤ (μ k * F₂' k) * (K₁ k * P₁) ^ (μ k * E₂' k) :=
            Nat.mul_le_mul hsum_F ((Nat.pow_le_pow_left hL₁_le _).trans
              (Nat.pow_le_pow_right (Nat.mul_pos (by dsimp [K₁]; positivity) hP₁) hsum_e))
        _ = μ k * F₂' k * K₁ k ^ (μ k * E₂' k) *
              ((encA a).length + 1) ^ (c₁ * (μ k * E₂' k)) := by
            rw [Nat.mul_pow, ← Nat.pow_mul]; ring
        _ ≤ μ k * F₂' k * K₁ k ^ (μ k * E₂' k) * ((encA a).length + 1) ^ E_xp k :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
              (by dsimp only [E_xp]; rw [Nat.mul_add]; omega))
    have h1_pow : F₁ k * P₁ ≤ F₁ k * ((encA a).length + 1) ^ E_xp k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp [E_xp]; omega))
    have hlen_mu := Nat.add_le_add_right (hμ a) 1
    have hinner := Nat.mul_le_mul hlen_mu (Nat.add_le_add hD_pow hlf_pow)
    dsimp only [F_xp]
    nlinarith

end ListMachines

/-! ### 2. Disjunctive FPT-Hardness -/

/-- Every problem hard for `𝒞` under many-one FPT-reductions is hard for `𝒞` under disjunctive
FPT-reductions. -/
theorem FPTDisjHard.of_fptHard
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)} {β : Type}
    {enc : β ↪ List Bool} {κ : β → ℕ} {B : Set β}
    (h : FPTHard 𝒞 enc κ B) : FPTDisjHard 𝒞 enc κ B :=
  fun _ encA κA A hA => fptDisjReducible_of_fptReducible (h encA κA A hA)

/-- Disjunctive FPT-hardness transfers along disjunctive FPT-reductions. -/
theorem FPTDisjHard.trans
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)} {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
    {A : Set α} {B : Set β}
    (hB : FPTDisjHard 𝒞 encB κB B) (hred : FPTDisjReducible encB encA κB κA B A) :
    FPTDisjHard 𝒞 encA κA A :=
  fun _ encX κX X hX => (hB encX κX X hX).trans hred

/-- If a disjunctively `𝒞`-hard problem lies in `FPT`, then the entire class `𝒞` lies in `FPT`. -/
theorem FPTDisjHard.subset_FPT
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)} {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ} {B : Set β}
    (hB : FPTDisjHard 𝒞 encB κB B) (hFPT : B ∈ FPT encB κB) :
    𝒞 encA κA ⊆ FPT encA κA :=
  fun _ hX => (hB encA κA _ hX).mem_FPT hFPT

/-! ### 3. Cai–Juedes Sublogarithmic Exponent Collapse -/

/-- A real function $s : \mathbb{N} \to \mathbb{R}$ is sublogarithmic in base $2$, written
$s(n) = o(\log_2 n)$, if for every $\varepsilon > 0$ we eventually have
$s(n) \le \varepsilon \log_2 n$. -/
@[expose]
def IsSublogBaseTwo (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n ≥ N₀, s n ≤ ε * Real.logb 2 n

/-- The identically zero function is sublogarithmic in base $2$. -/
@[simp]
theorem isSublogBaseTwo_zero : IsSublogBaseTwo (fun _ => 0) :=
  fun ε hε => ⟨2, fun n hn => mul_nonneg hε.le
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ n)))⟩

/-- **Cai–Juedes sublogarithmic exponent bound**: if $s(n) = o(\log_2 n)$
and $f : \mathbb{N} \to \mathbb{R}$ is nonnegative, then for any $\delta \ge 0$ there exists
$F : \mathbb{N} \to \mathbb{N}$ such that whenever $n \le L + 1$ and $\mu \le f(k) \cdot s(n)$,
one has $2^{\delta \mu} \le F(k) \cdot (L + 1)$.
-/
theorem two_rpow_le_fpt_of_isSublogBaseTwo {δ : ℝ} (hδ : 0 ≤ δ) {f s : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : IsSublogBaseTwo s) :
    ∃ F : ℕ → ℕ, ∀ (k μ n L : ℕ), n ≤ L + 1 → (μ : ℝ) ≤ f k * s n →
      (2 : ℝ) ^ (δ * μ) ≤ (F k : ℝ) * (L + 1) := by
  classical
  have hchoice : ∀ k : ℕ, ∃ N : ℕ, 2 ≤ N ∧
      ∀ n ≥ N, s n ≤ (1 / max 1 (δ * f k)) * Real.logb 2 n := by
    intro k
    obtain ⟨N₀, hN₀⟩ := hs (1 / max 1 (δ * f k)) (by positivity)
    exact ⟨max N₀ 2, le_max_right _ _, fun n hn => hN₀ n ((le_max_left _ _).trans hn)⟩
  choose N hN2 hNbound using hchoice
  let M : ℕ → ℕ := fun k => ∑ m ∈ Finset.range (N k), ⌈max (s m) 0⌉₊
  let F : ℕ → ℕ := fun k => ⌈(2 : ℝ) ^ (δ * f k * M k)⌉₊ + 1
  refine ⟨F, fun k μ n L hnL hμ => ?_⟩
  have hF1 : (1 : ℝ) ≤ F k := by exact_mod_cast Nat.succ_pos _
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  by_cases hn : N k ≤ n
  · have hn2 : 2 ≤ n := (hN2 k).trans hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn2
    have hlog_nonneg : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_of_lt hn2)
    have hsn := hNbound k n hn
    have hexp : δ * (μ : ℝ) ≤ Real.logb 2 n := by
      have h1 : δ * (μ : ℝ) ≤ (δ * f k) * s n := by
        nlinarith [mul_le_mul_of_nonneg_left hμ hδ]
      have h2 : (δ * f k) * s n ≤
          (δ * f k) * ((1 / max 1 (δ * f k)) * Real.logb 2 n) :=
        mul_le_mul_of_nonneg_left hsn (mul_nonneg hδ (hf k))
      have hmax_pos : 0 < max 1 (δ * f k) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have h3 : (δ * f k) * (1 / max 1 (δ * f k)) ≤ 1 := by
        rw [mul_one_div, div_le_one hmax_pos]
        exact le_max_right _ _
      have h4 := mul_le_mul_of_nonneg_right h3 hlog_nonneg
      linarith
    calc (2 : ℝ) ^ (δ * μ)
        ≤ (2 : ℝ) ^ (Real.logb 2 n) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (n : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hn_pos
      _ ≤ (L : ℝ) + 1 := by exact_mod_cast hnL
      _ ≤ (F k : ℝ) * ((L : ℝ) + 1) := le_mul_of_one_le_left (by positivity) hF1
  · have hn_lt : n < N k := not_le.mp hn
    have hsm : s n ≤ M k := by
      have hle : ⌈max (s n) 0⌉₊ ≤ M k :=
        Finset.single_le_sum (f := fun m => ⌈max (s m) 0⌉₊)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn_lt)
      exact (le_max_left (s n) 0).trans ((Nat.le_ceil _).trans (by exact_mod_cast hle))
    have hexp : δ * (μ : ℝ) ≤ δ * f k * M k := by
      have hfk := mul_le_mul_of_nonneg_left hsm (hf k)
      have := mul_le_mul_of_nonneg_left (hμ.trans hfk) hδ
      linarith
    have hF_ge : (2 : ℝ) ^ (δ * f k * M k) ≤ F k :=
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
    calc (2 : ℝ) ^ (δ * μ)
        ≤ (2 : ℝ) ^ (δ * f k * M k) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ ≤ (F k : ℝ) := hF_ge
      _ ≤ (F k : ℝ) * ((L : ℝ) + 1) := le_mul_of_one_le_right (Nat.cast_nonneg _) hL1

/-- **Cai–Juedes FPT collapse under a polynomial-time guard**: if `A` is decidable in time
$2^{\delta \mu(a)} \cdot \mathrm{poly}(|a|)$ ($\delta \ge 0$) and a polynomial-time guard `p`
selects instances with $\mu(a) \le f(\kappa(a)) \cdot s(\mathrm{size}(a))$ where
$s(n) = o(\log_2 n)$ and $\mathrm{size}(a) \le |a| + 1$, then `{a | p a = true} ∩ A` lies in
`FPT`. -/
theorem mem_FPT_of_decidableInExpTime_sublog {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {μ size κ : α → ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hExp : DecidableInExpTime A enc μ δ)
    (hsize : ∀ a, size a ≤ (enc a).length + 1)
    {f s : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (hs : IsSublogBaseTwo s)
    {p : α → Bool} (hp : ComputableInPolyTime p enc encBool)
    (hbound : ∀ a, p a = true → (μ a : ℝ) ≤ f (κ a) * s (size a)) :
    {a | p a = true} ∩ A ∈ FPT enc κ := by
  obtain ⟨e, hdec⟩ := hExp
  obtain ⟨e', hInt⟩ := hdec.inter hp (fun _ => by positivity)
  obtain ⟨F, hF⟩ := two_rpow_le_fpt_of_isSublogBaseTwo hδ hf hs
  refine ⟨fun k => F k + 1, e + e' + 1, hInt.mono 1 (fun a => ?_) (fun _ => by positivity)⟩
  set L := ((enc a).length : ℝ)
  have hL1 : 1 ≤ L + 1 := by
    dsimp [L]; linarith [show (0 : ℝ) ≤ (enc a).length from Nat.cast_nonneg _]
  have hpe' : (L + 1) ^ e' ≤ (L + 1) ^ (e + e' + 1) :=
    pow_le_pow_right₀ hL1 (by omega)
  split_ifs with hpa
  · have h2pow := hF (κ a) (μ a) (size a) (enc a).length (hsize a) (hbound a hpa)
    have hmul : (2 : ℝ) ^ (δ * μ a) * (L + 1) ^ e ≤
        (F (κ a) : ℝ) * (L + 1) ^ (e + e' + 1) := by
      calc (2 : ℝ) ^ (δ * μ a) * (L + 1) ^ e
          ≤ ((F (κ a) : ℝ) * (L + 1)) * (L + 1) ^ e :=
            mul_le_mul_of_nonneg_right h2pow (by positivity)
        _ = (F (κ a) : ℝ) * (L + 1) ^ (e + 1) := by rw [pow_succ]; ring
        _ ≤ (F (κ a) : ℝ) * (L + 1) ^ (e + e' + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) (Nat.cast_nonneg _)
    push_cast
    linarith
  · push_cast
    linarith [mul_nonneg (Nat.cast_nonneg (F (κ a)))
      (pow_nonneg (by linarith : (0 : ℝ) ≤ L + 1) (e + e' + 1))]

/-- **Uniform promise FPT decider**: if `A` is decidable in time
$2^{\delta \mu(a)} \cdot \mathrm{poly}(|a|)$ ($\delta \ge 0$), then a single machine decides `A`
on **all** instances while halting within FPT time $F(\kappa(a)) \cdot (|a| + 1)^c$ on every
instance satisfying $\mu(a) \le f(\kappa(a)) \cdot s(\mathrm{size}(a))$, for arbitrary
(not necessarily computable) $f, s : \mathbb{N} \to \mathbb{R}$ with $f \ge 0$ and
$s(n) = o(\log_2 n)$.
-/
theorem exists_fpt_decider_of_decidableInExpTime_sublog {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {μ size κ : α → ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hExp : DecidableInExpTime A enc μ δ)
    (hsize : ∀ a, size a ≤ (enc a).length + 1)
    {f s : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (hs : IsSublogBaseTwo s) :
    ∃ (dec : α → Bool) (t w : α → ℕ) (F : ℕ → ℕ) (c : ℕ),
      ComputableInTimeAndSpace dec enc encBool t w ∧
      (∀ a, a ∈ A ↔ dec a = true) ∧
      ∀ a, (μ a : ℝ) ≤ f (κ a) * s (size a) → t a ≤ F (κ a) * ((enc a).length + 1) ^ c := by
  obtain ⟨e, c₀, t, w, ht, hdec⟩ := hExp
  obtain ⟨dec, htm, hmem⟩ := decidableInTimeAndSpace_iff.mp hdec
  obtain ⟨F, hF⟩ := two_rpow_le_fpt_of_isSublogBaseTwo hδ hf hs
  refine ⟨dec, t, w, fun k => c₀ * F k + c₀, e + 1, htm, hmem, fun a hbound => ?_⟩
  have h2pow := hF (κ a) (μ a) (size a) (enc a).length (hsize a) hbound
  set L := ((enc a).length : ℝ)
  have hL1 : 1 ≤ (L + 1) ^ (e + 1) :=
    one_le_pow₀ (by dsimp [L]; linarith [show (0 : ℝ) ≤ (enc a).length from Nat.cast_nonneg _])
  have hmain : (t a : ℝ) ≤ ((c₀ * F (κ a) + c₀ : ℕ) : ℝ) * (L + 1) ^ (e + 1) := by
    have hmul : (2 : ℝ) ^ (δ * μ a) * (L + 1) ^ e ≤ (F (κ a) : ℝ) * (L + 1) ^ (e + 1) := by
      calc (2 : ℝ) ^ (δ * μ a) * (L + 1) ^ e
          ≤ ((F (κ a) : ℝ) * (L + 1)) * (L + 1) ^ e :=
            mul_le_mul_of_nonneg_right h2pow (by positivity)
        _ = (F (κ a) : ℝ) * (L + 1) ^ (e + 1) := by rw [pow_succ]; ring
    have hc_mul := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg c₀)
    have hc_one := mul_le_mul_of_nonneg_left hL1 (Nat.cast_nonneg c₀)
    push_cast
    linarith [ht a]
  dsimp only [L] at hmain ⊢
  exact_mod_cast hmain

/-! ### 4. Fine-Grained $o(k / \log_2 k)$ Transfers Across Disjunctive FPT-Reductions -/

/-- A function $s : \mathbb{N} \to \mathbb{R}$ satisfies $s(k) = o(k / \log_2 k)$ if for every
$\varepsilon > 0$ we eventually have $s(k) \le \varepsilon \cdot (k / \log_2 k)$. -/
@[expose]
def IsLittleOKDivLog (s : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, s k ≤ ε * ((k : ℝ) / Real.logb 2 k)

/-- The identically zero function satisfies $o(k / \log_2 k)$. -/
@[simp]
theorem isLittleOKDivLog_zero : IsLittleOKDivLog (fun _ => 0) :=
  fun ε hε => ⟨2, fun k hk => mul_nonneg hε.le (div_nonneg (Nat.cast_nonneg k)
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k))))⟩

private theorem add_three_le_four_mul_two_pow : ∀ m : ℕ, m + 3 ≤ 4 * 2 ^ m
  | 0 => by decide
  | m + 1 => by
    have ih := add_three_le_four_mul_two_pow m
    rw [Nat.pow_succ]
    omega

private theorem sq_le_two_pow_of_four_le : ∀ t : ℕ, 4 ≤ t → t ^ 2 ≤ 2 ^ t
  | 0, h | 1, h | 2, h | 3, h => by omega
  | 4, _ => by decide
  | t + 5, _ => by
    have ih := sq_le_two_pow_of_four_le (t + 4) (by omega)
    have h2t : 16 ≤ 2 ^ (t + 4) := by
      calc 16 = 2 ^ 4 := by decide
        _ ≤ 2 ^ (t + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hlin : 2 * (t + 4) + 1 ≤ (t + 4) ^ 2 := by nlinarith
    calc (t + 5) ^ 2 = (t + 4) ^ 2 + (2 * (t + 4) + 1) := by ring
      _ ≤ 2 ^ (t + 4) + 2 ^ (t + 4) := Nat.add_le_add ih (hlin.trans ih)
      _ = 2 ^ (t + 5) := by rw [Nat.pow_succ]; ring

private theorem div_logb_le_two_mul_div_logb {r : ℕ} {B : ℝ} (hr4 : 4 ≤ r) (hrB : (r : ℝ) ≤ B) :
    (r : ℝ) / Real.logb 2 r ≤ 2 * (B / Real.logb 2 B) := by
  have hr_pos : (0 : ℝ) < r := by positivity
  have hB_pos : 0 < B := hr_pos.trans_le hrB
  have hlog_r_ge2 : 2 ≤ Real.logb 2 r := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hr_pos]
    norm_num
    exact_mod_cast hr4
  have hlog_B_ge : Real.logb 2 r ≤ Real.logb 2 B :=
    Real.logb_le_logb_of_le (by norm_num) hr_pos hrB
  have hlog_r_pos : 0 < Real.logb 2 r := by linarith
  have hlog_B_pos : 0 < Real.logb 2 B := by linarith
  set d := Real.logb 2 B - Real.logb 2 r
  have hd_nonneg : 0 ≤ d := sub_nonneg.mpr hlog_B_ge
  set m : ℕ := ⌊d⌋₊
  have hm_le : (m : ℝ) ≤ Real.logb 2 (B / r) := by
    rw [Real.logb_div hB_pos.ne' hr_pos.ne']
    exact Nat.floor_le hd_nonneg
  have hr_pow_B : (r : ℝ) * (2 : ℝ) ^ m ≤ B := by
    have h1 : (2 : ℝ) ^ (m : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (B / r)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hm_le
    rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) (div_pos hB_pos hr_pos),
      le_div_iff₀ hr_pos] at h1
    linarith
  have hm_lt : d < (m : ℝ) + 1 := Nat.lt_floor_add_one d
  have hlog_B_le : Real.logb 2 B ≤ (2 : ℝ) ^ (m + 1) * Real.logb 2 r := by
    have h1 : Real.logb 2 B < Real.logb 2 r + ((m : ℝ) + 1) := by dsimp [d] at hm_lt; linarith
    have h2 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) / 2 * Real.logb 2 r := by nlinarith
    have h3 : ((m : ℝ) + 3) / 2 ≤ (2 : ℝ) ^ (m + 1) := by
      have hnat : (m : ℝ) + 3 ≤ 4 * (2 : ℝ) ^ m := by
        exact_mod_cast add_three_le_four_mul_two_pow m
      rw [pow_succ]
      linarith
    nlinarith
  rw [ ← mul_div_assoc, div_le_div_iff₀ hlog_r_pos hlog_B_pos]
  have hmul := mul_le_mul hr_pow_B hlog_B_le hlog_B_pos.le hB_pos.le
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hsimp : B * ((2 : ℝ) ^ (m + 1) * Real.logb 2 r) =
      (2 : ℝ) ^ m * (2 * B * Real.logb 2 r) := by rw [pow_succ]; ring
  rw [hsimp] at hmul
  nlinarith

private theorem tendsto_k_div_logb (M : ℝ) :
    ∃ K₀ : ℕ, ∀ k ≥ K₀, M ≤ (k : ℝ) / Real.logb 2 k := by
  let T : ℕ := max (2 * ⌈max M 0⌉₊ + 2) 4
  refine ⟨2 ^ T, fun k hk => ?_⟩
  have ht_ge : T ≤ Nat.log 2 k := Nat.le_log_of_pow_le Nat.one_lt_two hk
  set t := Nat.log 2 k
  have ht4 : 4 ≤ t := (le_max_right _ _).trans ht_ge
  have hk_ne : k ≠ 0 := by
    have : 0 < 2 ^ T := by positivity
    omega
  have hk_ge_sq : (t : ℝ) ^ 2 ≤ k := by
    have hnat : t ^ 2 ≤ k :=
      (sq_le_two_pow_of_four_le t ht4).trans (Nat.pow_log_le_self 2 hk_ne)
    exact_mod_cast hnat
  have hk_lt : (k : ℝ) ≤ (2 : ℝ) ^ (t + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two k).le
  have hk_pos : (0 : ℝ) < k := by
    have : 0 < 2 ^ T := by positivity
    exact_mod_cast this.trans_le hk
  have hlog_le : Real.logb 2 k ≤ 2 * (t : ℝ) := by
    have h1 : Real.logb 2 k ≤ (t : ℝ) + 1 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) hk_pos,
        show (2 : ℝ) ^ ((t : ℝ) + 1) = (2 : ℝ) ^ (t + 1 : ℕ) by
          rw [← Real.rpow_natCast]; push_cast; rfl]
      exact hk_lt
    have ht4' : (4 : ℝ) ≤ t := by exact_mod_cast ht4
    linarith
  have hlog_pos : 0 < Real.logb 2 k := by
    apply Real.logb_pos (by norm_num)
    have : 2 ≤ 2 ^ T := by
      calc 2 = 2 ^ 1 := by ring
        _ ≤ 2 ^ T := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (this.trans hk))
  have ht_div : (t : ℝ) / 2 ≤ (k : ℝ) / Real.logb 2 k := by
    rw [div_le_div_iff₀ (by norm_num) hlog_pos]
    nlinarith
  have hM_le_T : M ≤ (t : ℝ) / 2 := by
    have hT1 : 2 * ⌈max M 0⌉₊ + 2 ≤ t := (le_max_left _ _).trans ht_ge
    have hT2 : 2 * max M 0 ≤ (t : ℝ) := by
      have : (2 * ⌈max M 0⌉₊ : ℝ) ≤ t := by exact_mod_cast (by omega : 2 * ⌈max M 0⌉₊ ≤ t)
      linarith [Nat.le_ceil (max M 0)]
    linarith [le_max_left M 0]
  exact hM_le_T.trans ht_div

/-- If $s(r) = o(r / \log_2 r)$, then for any constants $C \ge 1$, $c_1 \ge 1$, and additive
offset $d : \mathbb{R}$, the envelope
$k \mapsto c_1 \cdot \max_{r \le C k} \max(s(r), 0) + d$ also satisfies $o(k / \log_2 k)$. -/
theorem isLittleOKDivLog_sup_linear {s : ℕ → ℝ} (hs : IsLittleOKDivLog s)
    (C c₁ : ℕ) (hC : 1 ≤ C) (d : ℝ) :
    IsLittleOKDivLog (fun k =>
      (c₁ : ℝ) * ((Finset.range (C * k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
        fun r => max (s r) 0) + d) := by
  intro ε hε
  set c₁' : ℝ := max (c₁ : ℝ) 1
  have hc₁_pos : 0 < c₁' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC_pos : (0 : ℝ) < C := by exact_mod_cast hC
  set ε' : ℝ := ε / (4 * c₁' * C)
  have hε' : 0 < ε' := by positivity
  obtain ⟨r₀, hr₀⟩ := hs ε' hε'
  set R : ℕ := max r₀ 4
  let M_low : ℝ := ∑ r ∈ Finset.range R, max (s r) 0
  obtain ⟨K₁, hK₁⟩ := tendsto_k_div_logb ((c₁' * M_low + max d 0 + 1) / (ε / 2))
  refine ⟨max K₁ 4, fun k hk => ?_⟩
  have hk4 : 4 ≤ k := (le_max_right _ _).trans hk
  have hk_div_ge : (c₁' * M_low + max d 0 + 1) / (ε / 2) ≤ (k : ℝ) / Real.logb 2 k :=
    hK₁ k ((le_max_left _ _).trans hk)
  have hlow_term : c₁' * M_low + d ≤ (ε / 2) * ((k : ℝ) / Real.logb 2 k) := by
    rw [div_le_iff₀ (half_pos hε)] at hk_div_ge
    linarith [le_max_left d 0]
  have hsup_le : (Finset.range (C * k +
    1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
      (fun r => max (s r) 0) ≤ M_low + (ε / (2 * c₁')) * ((k : ℝ) / Real.logb 2 k) := by
    refine Finset.sup'_le _ _ fun r hr_mem => ?_
    have hr_le : r ≤ C * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr_mem)
    have hM_nonneg : 0 ≤ M_low := Finset.sum_nonneg fun _ _ => le_max_right _ _
    have hk_pos : 0 ≤ (ε / (2 * c₁')) * ((k : ℝ) / Real.logb 2 k) := by
      have hlog_pos : 0 ≤ Real.logb 2 k :=
        Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k))
      exact mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg k) hlog_pos)
    by_cases hrR : R ≤ r
    · have hr4 : 4 ≤ r := (le_max_right _ _).trans hrR
      have hsr : s r ≤ ε' * ((r : ℝ) / Real.logb 2 r) := hr₀ r ((le_max_left _ _).trans hrR)
      have hrB : (r : ℝ) ≤ (C : ℝ) * k := by exact_mod_cast hr_le
      have hdiv1 := div_logb_le_two_mul_div_logb hr4 hrB
      have hlog_Ck : Real.logb 2 k ≤ Real.logb 2 ((C : ℝ) * k) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity)
          (le_mul_of_one_le_left (Nat.cast_nonneg k) (by exact_mod_cast hC))
      have hlog_k_pos : 0 < Real.logb 2 k :=
        Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < k))
      have hdiv2 : ((C : ℝ) * k) / Real.logb 2 ((C : ℝ) * k) ≤
          (C : ℝ) * ((k : ℝ) / Real.logb 2 k) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_left (by positivity) hlog_k_pos hlog_Ck
      have hsr' : max (s r) 0 ≤ (ε / (2 * c₁')) * ((k : ℝ) / Real.logb 2 k) := by
        refine max_le ?_ hk_pos
        calc s r ≤ ε' * ((r : ℝ) / Real.logb 2 r) := hsr
          _ ≤ ε' * (2 * (((C : ℝ) * k) / Real.logb 2 ((C : ℝ) * k))) :=
              mul_le_mul_of_nonneg_left hdiv1 hε'.le
          _ ≤ ε' * (2 * ((C : ℝ) * ((k : ℝ) / Real.logb 2 k))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hdiv2 zero_le_two) hε'.le
          _ = (ε / (2 * c₁')) * ((k : ℝ) / Real.logb 2 k) := by
              dsimp [ε']
              field_simp
              ring
      linarith
    · have hr_lt : r < R := not_le.mp hrR
      have hle_sum : max (s r) 0 ≤ M_low :=
        Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_range.mpr hr_lt)
      linarith
  set S_sup := (Finset.range (C * k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun r => max (s r) 0)
  have hS_nonneg : 0 ≤ S_sup :=
    (le_max_right (s 0) 0).trans
      (Finset.le_sup' (fun r => max (s r) 0) (Finset.mem_range.mpr (Nat.succ_pos _)))
  have hc1_le : (c₁ : ℝ) * S_sup ≤ c₁' * S_sup :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hS_nonneg
  have hmul_sup := mul_le_mul_of_nonneg_left hsup_le hc₁_pos.le
  have hcancel : c₁' * (ε / (2 * c₁')) = ε / 2 := by field_simp
  calc (c₁ : ℝ) * S_sup + d
      ≤ c₁' * (M_low + (ε / (2 * c₁')) * ((k : ℝ) / Real.logb 2 k)) + d := by linarith
    _ = (c₁' * M_low + d) + (c₁' * (ε / (2 * c₁'))) * ((k : ℝ) / Real.logb 2 k) := by ring
    _ = (c₁' * M_low + d) + (ε / 2) * ((k : ℝ) / Real.logb 2 k) := by rw [hcancel]
    _ ≤ ε * ((k : ℝ) / Real.logb 2 k) := by linarith

/-- **Subexponential $o(k / \log_2 k)$ runtime transfer across linear-parameter disjunctive
FPT-reductions**: suppose `f : α → List β` runs in FPT time wrt `κA`, emits at most `μ (κA a)`
instances each of parameter `κB b ≤ C * κA a` (`C ≥ 1`), and `a ∈ A ↔ ∃ b ∈ f a, b ∈ B`. If `dec`
is a machine running in time $f_B(\kappa_B(b)) \cdot (\mathrm{size}_B(b) + 1)^{s(\kappa_B(b))}
\cdot (|b| + 1)^e$ with $\mathrm{size}_B(b) \le |b|$ and $s(r) = o(r / \log_2 r)$ that correctly
decides `B` on every emitted query $b \in f(a)$, then `A` is decidable in time
$f_A(\kappa_A(a)) \cdot (|a| + 1)^{s_A(\kappa_A(a))}$ for some $f_A, s_A$ with
$s_A(k) = o(k / \log_2 k)$. -/
theorem decidableInTimeO_of_fptDisj_subexp {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κA : α → ℕ} {κB sizeB : β → ℕ} {A : Set α} {B : Set β}
    {f : α → List β} (hf : ComputableInFPTTime f encA (encList encB) κA)
    {μ : ℕ → ℕ} {C : ℕ} (hC : 1 ≤ C)
    (hμ : ∀ a, (f a).length ≤ μ (κA a))
    (hκ : ∀ a, ∀ b ∈ f a, κB b ≤ C * κA a)
    (hfA : ∀ a, a ∈ A ↔ ∃ b ∈ f a, b ∈ B)
    (hsizeB : ∀ b, sizeB b ≤ (encB b).length)
    {fB s : ℕ → ℝ} {e : ℕ} (hs : IsLittleOKDivLog s)
    {dec : β → Bool} {tB : β → ℕ} {cB : ℕ}
    (hdecO : ComputableInO dec encB encBool tB tB)
    (hdec_corr : ∀ a, ∀ b ∈ f a, b ∈ B ↔ dec b = true)
    (htB : ∀ b, (tB b : ℝ) ≤ cB * (fB (κB b) * ((sizeB b : ℝ) + 1) ^ s (κB b) *
      (((encB b).length : ℝ) + 1) ^ e) + cB) :
    ∃ fA sA : ℕ → ℝ, IsLittleOKDivLog sA ∧
      DecidableInTimeO A encA
        (fun a => fA (κA a) * (((encA a).length : ℝ) + 1) ^ sA (κA a)) := by
  obtain ⟨F₁, c₁, hfO⟩ := exists_computableInO_of_fptTime hf
  have ⟨l₁, _, hl₁⟩ := hfO
  obtain ⟨D, hAny⟩ := exists_computableInO_listAny hdecO
  let leafBound : List β → ℕ := fun L => (L.map tB).sum
  have hleaf (L : List β) (b : β) (hb : b ∈ L) : tB b ≤ leafBound L :=
    List.le_sum_of_mem (List.mem_map_of_mem hb)
  have hcomp := (hAny leafBound hleaf).comp hfO
  let S_sup : ℕ → ℝ := fun k =>
    (Finset.range (C * k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      fun r => max (s r) 0
  let F_sup : ℕ → ℝ := fun k => ∑ r ∈ Finset.range (C * k + 1), |fB r|
  let K₁ : ℕ → ℕ := fun k => (l₁ + 1) * (F₁ k + 1) + 1
  set c₁' : ℕ := max c₁ 1
  let sA : ℕ → ℝ := fun k => (c₁' : ℝ) * S_sup k + (c₁' * (D + e + 1) : ℕ)
  let fA : ℕ → ℝ := fun k =>
    (F₁ k : ℝ) + (μ k + 1 : ℝ) *
      ((K₁ k : ℝ) ^ D + (μ k + 1 : ℝ) * (2 * cB + 1 : ℝ) * (F_sup k + 1) *
        (K₁ k : ℝ) ^ (S_sup k + e))
  have hsA : IsLittleOKDivLog sA :=
    isLittleOKDivLog_sup_linear hs C c₁' hC _
  refine ⟨fA, sA, hsA, DecidableInTimeO.of_computableInO hcomp
    (fun a => (hfA a).trans ⟨fun ⟨b, hb, hbB⟩ => List.any_eq_true.mpr ⟨b, hb,
      (hdec_corr a b hb).mp hbB⟩,
      fun hany => let ⟨b, hb, hdb⟩ :=
        List.any_eq_true.mp hany; ⟨b, hb, (hdec_corr a b hb).mpr hdb⟩⟩)
    fun a => ?_⟩
  set k := κA a
  set LA := (encA a).length
  have hLA1 : (1 : ℝ) ≤ (LA : ℝ) + 1 := by
    linarith [show (0 : ℝ) ≤ LA from Nat.cast_nonneg _]
  have hP₁ : 1 ≤ (LA + 1) ^ c₁' := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hc₁_le : (LA + 1) ^ c₁ ≤ (LA + 1) ^ c₁' :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
  have hL_out_nat : (encList encB (f a)).length + 1 ≤ K₁ k * (LA + 1) ^ c₁' := by
    have h1 : (encList encB (f a)).length ≤ l₁ * (F₁ k * (LA + 1) ^ c₁ + 1) := hl₁ a
    have h2 := Nat.mul_le_mul_left (F₁ k) hc₁_le
    dsimp only [K₁]
    nlinarith [Nat.mul_le_mul_left l₁ hP₁, Nat.mul_le_mul_left l₁ h2]
  have hL_out : ((encList encB (f a)).length : ℝ) + 1 ≤ (K₁ k : ℝ) * ((LA : ℝ) + 1) ^ c₁' := by
    exact_mod_cast hL_out_nat
  have hS_nonneg : 0 ≤ S_sup k :=
    (le_max_right (s 0) 0).trans
      (Finset.le_sup' (fun r => max (s r) 0) (Finset.mem_range.mpr (Nat.succ_pos _)))
  have hsA_ge (m : ℕ) (hm : m ≤ c₁' * (D + e + 1)) :
      ((LA : ℝ) + 1) ^ m ≤ ((LA : ℝ) + 1) ^ sA k := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hLA1 ?_
    have hm' : (m : ℝ) ≤ (c₁' * (D + e + 1) : ℕ) := by exact_mod_cast hm
    dsimp only [sA]
    have : 0 ≤ (c₁' : ℝ) * S_sup k := mul_nonneg (Nat.cast_nonneg _) hS_nonneg
    linarith
  -- Bound each `tB b` for `b ∈ f a`.
  have htB_bound : ∀ b ∈ f a, (tB b : ℝ) ≤
      (2 * cB + 1 : ℝ) * (F_sup k + 1) * (K₁ k : ℝ) ^ (S_sup k + e) *
        ((LA : ℝ) + 1) ^ sA k := by
    intro b hb
    have hkb : κB b ≤ C * k := hκ a b hb
    have hkb_mem : κB b ∈ Finset.range (C * k + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hkb)
    have hLb : ((encB b).length : ℝ) + 1 ≤ (K₁ k : ℝ) * ((LA : ℝ) + 1) ^ c₁' := by
      have hb_nat : (encB b).length ≤ (encList encB (f a)).length :=
        length_enc_mem_le_encList encB hb
      exact (by exact_mod_cast Nat.add_le_add_right hb_nat 1 :
        ((encB b).length : ℝ) + 1 ≤ ((encList encB (f a)).length : ℝ) + 1).trans hL_out
    have hsize_le : (sizeB b : ℝ) + 1 ≤ ((encB b).length : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (hsizeB b) 1
    have hs_le : s (κB b) ≤ S_sup k :=
      (le_max_left _ _).trans (Finset.le_sup' (fun r => max (s r) 0) hkb_mem)
    have hrpow_size : ((sizeB b : ℝ) + 1) ^ s (κB b) ≤
        (((encB b).length : ℝ) + 1) ^ S_sup k :=
      (Real.rpow_le_rpow_of_exponent_le
        (by linarith [show (0 : ℝ) ≤ sizeB b from Nat.cast_nonneg _]) hs_le).trans
        (Real.rpow_le_rpow (by positivity) hsize_le hS_nonneg)
    have hfB_le : |fB (κB b)| ≤ F_sup k :=
      Finset.single_le_sum (f := fun r => |fB r|) (fun _ _ => abs_nonneg _) hkb_mem
    have hF_nonneg : 0 ≤ F_sup k := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hLb_pow : (((encB b).length : ℝ) + 1) ^ S_sup k *
        (((encB b).length : ℝ) + 1) ^ e ≤
        (K₁ k : ℝ) ^ (S_sup k + e) * ((LA : ℝ) + 1) ^ sA k := by
      rw [← Real.rpow_natCast (((encB b).length : ℝ) + 1) e,
        ← Real.rpow_add (by positivity)]
      have h1 : (((encB b).length : ℝ) + 1) ^ (S_sup k + e) ≤
          ((K₁ k : ℝ) * ((LA : ℝ) + 1) ^ c₁') ^ (S_sup k + e) :=
        Real.rpow_le_rpow (by positivity) hLb (by positivity)
      rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity),
        ← Real.rpow_natCast ((LA : ℝ) + 1) c₁',
        ← Real.rpow_mul (by positivity)] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hLA1 ?_) (by positivity))
      dsimp only [sA]
      push_cast
      nlinarith
    have ht1 := htB b
    set W : ℝ := (F_sup k + 1) * (K₁ k : ℝ) ^ (S_sup k + e) * ((LA : ℝ) + 1) ^ sA k
    have hprod : fB (κB b) * ((sizeB b : ℝ) + 1) ^ s (κB b) *
        (((encB b).length : ℝ) + 1) ^ e ≤ W := by
      calc fB (κB b) * ((sizeB b : ℝ) + 1) ^ s (κB b) * (((encB b).length : ℝ) + 1) ^ e
          ≤ |fB (κB b)| * ((((encB b).length : ℝ) + 1) ^ S_sup k *
              (((encB b).length : ℝ) + 1) ^ e) := by
            rw [mul_assoc]
            exact mul_le_mul (le_abs_self _)
              (mul_le_mul_of_nonneg_right hrpow_size (by positivity))
              (by positivity) (abs_nonneg _)
        _ ≤ (F_sup k + 1) * ((K₁ k : ℝ) ^ (S_sup k + e) * ((LA : ℝ) + 1) ^ sA k) :=
            mul_le_mul (by linarith) hLb_pow (by positivity) (by positivity)
        _ = W := by dsimp [W]; ring
    have hone_le : 1 ≤ W := by
      have hk1 : (1 : ℝ) ≤ K₁ k := by exact_mod_cast (by dsimp [K₁]; omega : 1 ≤ K₁ k)
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith)
          (Real.one_le_rpow hk1 (by positivity)))
        (hsA_ge 0 (Nat.zero_le _) |> (by simpa using ·))
    have hcB_mul := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg cB)
    have hcB_one := mul_le_mul_of_nonneg_left hone_le (Nat.cast_nonneg cB)
    calc (tB b : ℝ) ≤ (cB : ℝ) * W + (cB : ℝ) * 1 := by linarith
      _ ≤ (cB : ℝ) * W + (cB : ℝ) * W + W := by linarith
      _ = (2 * cB + 1 : ℝ) * (F_sup k + 1) * (K₁ k : ℝ) ^ (S_sup k + e) *
            ((LA : ℝ) + 1) ^ sA k := by dsimp [W]; ring
  have hleaf_real : (leafBound (f a) : ℝ) ≤
      (μ k + 1 : ℝ) * (2 * cB + 1 : ℝ) * (F_sup k + 1) * (K₁ k : ℝ) ^ (S_sup k + e) *
        ((LA : ℝ) + 1) ^ sA k := by
    let B_bound : ℝ :=
      (2 * cB + 1 : ℝ) * (F_sup k + 1) * (K₁ k : ℝ) ^ (S_sup k + e) * ((LA : ℝ) + 1) ^ sA k
    have hsum_r : ∀ xs : List β, (∀ b ∈ xs, b ∈ f a) →
        (((xs.map tB).sum : ℕ) : ℝ) ≤ (xs.length : ℝ) * B_bound := by
      intro xs hxs
      induction xs with
      | nil => simp
      | cons b bs ih =>
        have hb := htB_bound b (hxs b List.mem_cons_self)
        have hbs := ih fun x hx => hxs x (List.mem_cons_of_mem _ hx)
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
    have hlen_le : ((f a).length : ℝ) ≤ (μ k + 1 : ℝ) := by
      exact_mod_cast (hμ a).trans (Nat.le_succ _)
    calc (leafBound (f a) : ℝ)
        ≤ ((f a).length : ℝ) * B_bound := hsum_r (f a) fun _ h => h
      _ ≤ (μ k + 1 : ℝ) * B_bound :=
          mul_le_mul_of_nonneg_right hlen_le (by dsimp [B_bound]; positivity)
      _ = _ := by dsimp [B_bound]; ring
  have hD_real : (((encList encB (f a)).length : ℝ) + 1) ^ D ≤
      (K₁ k : ℝ) ^ D * ((LA : ℝ) + 1) ^ sA k := by
    calc (((encList encB (f a)).length : ℝ) + 1) ^ D
        ≤ ((K₁ k : ℝ) * ((LA : ℝ) + 1) ^ c₁') ^ D :=
          pow_le_pow_left₀ (by positivity) hL_out D
      _ = (K₁ k : ℝ) ^ D * ((LA : ℝ) + 1) ^ (c₁' * D) := by rw [mul_pow, ← pow_mul]
      _ ≤ (K₁ k : ℝ) ^ D * ((LA : ℝ) + 1) ^ sA k :=
          mul_le_mul_of_nonneg_left (hsA_ge (c₁' * D) (by nlinarith)) (by positivity)
  have hf1_real : (F₁ k : ℝ) * ((LA : ℝ) + 1) ^ c₁ ≤
      (F₁ k : ℝ) * ((LA : ℝ) + 1) ^ sA k :=
    mul_le_mul_of_nonneg_left
      (hsA_ge c₁ ((le_max_left c₁ 1).trans (Nat.le_mul_of_pos_right c₁' (by omega))))
      (Nat.cast_nonneg _)
  have hlen_real : ((f a).length : ℝ) + 1 ≤ (μ k + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (hμ a) 1
  push_cast
  have hsum_in := add_le_add hD_real hleaf_real
  have hmul_in := mul_le_mul hlen_real hsum_in (by positivity) (by positivity)
  dsimp only [fA]
  linarith

end CslibFrontier.ParameterizedComplexity

