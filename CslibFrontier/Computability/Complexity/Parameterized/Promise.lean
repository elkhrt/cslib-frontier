/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Parameterized.Hardness
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
public import CslibFrontier.Computability.Complexity.Problems.Clique

import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Parameterized Promise Problems and FPT-Promise Reductions

This module lifts the fixed-parameter tractability classes and reductions of
`CslibFrontier.Computability.Complexity.Parameterized` to promise problems via
`Cslib.Complexity.promiseClass`.

## Main definitions

* `Cslib.Complexity.PromiseFPT`: the lift `promiseClass (FPT enc κ)` of `FPT` to promise problems.
* `Cslib.Complexity.FPTPromiseReducible`: parameterized fpt-time reductions between promise
  problems mapping yes-instances to yes-instances and no-instances to no-instances while bounding
  the output parameter by a function of the input parameter.
* `Cslib.Complexity.FPTPromiseHard`: hardness of a parameterized promise problem for a
  parameterized decision class under `FPTPromiseReducible`.
* `Cslib.Complexity.W1PromiseHard`: `W[1]`-hardness of a parameterized promise problem.

## Main results

* `Cslib.Complexity.computableInFPTTime_of_computableInPolyTime_pad`: any polynomial-time
  function on padded pairs `(a, 2 ^ ν a)` with `ν a ≤ h (κ a)` is computable in fpt time.
* `Cslib.Complexity.mem_promiseFPT_iff`: Goldreich-style characterization of `PromiseFPT` by
  fpt-time functions solving the promise problem.
* `Cslib.Complexity.FPTPromiseReducible.refl`, `.trans`, `.of_subset`, `.of_computableInPolyTime`,
  `.of_computableInPolyTime_pad`, `.mem_promiseFPT`: closure and composition properties of
  fpt-promise reductions.
* `Cslib.Complexity.FPTPromiseHard.subset_FPT`, `.not_mem_promiseFPT`: hardness transfer and
  separation consequences.
* `Cslib.Complexity.w1PromiseHard_of_fptPromiseReducible_clique`,
  `Cslib.Complexity.W1PromiseHard.not_mem_promiseFPT_of_W_one_ne_FPT`: `W[1]`-hardness via
  `Clique` and separation under `W[1] ≠ FPT`.
-/

public section

namespace Cslib.Complexity

open PromiseProblem
open Turing.MultiTapeTM

/-! ### FPT-Time Computability via Unary Padding -/

private lemma le_sum_range_succ_aux (f : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    f a ≤ ∑ j ∈ Finset.range (b + 1), f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- **FPT time by unary padding.** If `f` is polynomial-time on pairs `(a, N)` with `N` in unary,
and `ν` is computable in unary in polynomial time with `ν a ≤ h (κ a)` for some function
`h : ℕ → ℕ`, then `a ↦ f (a, 2 ^ ν a)` is computable in fpt time with respect to `κ`. -/
theorem computableInFPTTime_of_computableInPolyTime_pad {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ}
    {f : α × ℕ → β} {ν : α → ℕ} {h : ℕ → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encUnary) encB)
    (hν : ComputableInPolyTime ν encA encUnary) (hνκ : ∀ a, ν a ≤ h (κ a)) :
    ComputableInFPTTime (fun a => f (a, 2 ^ ν a)) encA encB κ := by
  obtain ⟨C, D, hO⟩ := hf.exists_computableInO_pad hν
  refine (hO.mono_le (fun a => ?_) (fun a => ?_)).computableInFPTTime
    (F := fun k => C * 2 ^ (D * h k)) (c := D)
  all_goals
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left D (hνκ a))))

/-! ### The Class `PromiseFPT` -/

section PromiseFPT

variable {α : Type} {enc : α ↪ List Bool} {κ κ' : α → ℕ} {Q : PromiseProblem α}

/-- The parameterized promise problems solvable in fixed-parameter tractable time with respect to
encoding `enc` and parameter `κ`: the lift `promiseClass (FPT enc κ)` of `FPT`. -/
def PromiseFPT (enc : α ↪ List Bool) (κ : α → ℕ) : Set (PromiseProblem α) :=
  promiseClass (FPT enc κ)

/-- **Goldreich-style characterization of `PromiseFPT`**: a promise problem belongs to
`PromiseFPT enc κ` iff some function computable in fpt time solves it. -/
theorem mem_promiseFPT_iff :
    Q ∈ PromiseFPT enc κ ↔
      ∃ g : α → Bool, ComputableInFPTTime g enc encBool κ ∧ Q.SolvedBy g :=
  mem_promiseClass_iff_solvedBy fun _ => mem_FPT_iff_computableInFPTTime

/-- A parameterized decision problem belongs to `PromiseFPT` iff it belongs to `FPT`. -/
@[simp]
theorem ofSet_mem_promiseFPT {A : Set α} :
    ofSet A ∈ PromiseFPT enc κ ↔ A ∈ FPT enc κ :=
  ofSet_mem_promiseClass

/-- Enlarging the parameter via a bounding function preserves membership in `PromiseFPT`. -/
theorem PromiseFPT.mono {h : ℕ → ℕ} (hκ : ∀ a, κ a ≤ h (κ' a)) :
    PromiseFPT enc κ ⊆ PromiseFPT enc κ' :=
  promiseClass_mono (FPT_subset_FPT_of_le_comp hκ)

/-- Every problem in `PromiseP` belongs to `PromiseFPT` for every parameter. -/
theorem PromiseP_subset_promiseFPT : PromiseP enc ⊆ PromiseFPT enc κ :=
  promiseClass_mono P_subset_FPT

/-- For a uniformly bounded parameter, `PromiseFPT` coincides with `PromiseP`. -/
theorem promiseFPT_eq_promiseP_of_le {K : ℕ} (hκ : ∀ a, κ a ≤ K) :
    PromiseFPT enc κ = PromiseP enc := by
  rw [PromiseFPT, FPT_eq_P_of_le hκ, PromiseP]

/-- `PromiseFPT` is closed under complementation of promise problems. -/
theorem compl_mem_promiseFPT (hQ : Q ∈ PromiseFPT enc κ) : Qᶜ ∈ PromiseFPT enc κ :=
  compl_mem_promiseClass (fun _ => compl_mem_FPT) hQ

end PromiseFPT

/-! ### FPT-Promise Reductions -/

section Reduction

/-- **Parameterized fpt-time reduction between promise problems**: `X` fpt-reduces to `Y` if some
function `f` computable in fpt time with respect to `κA` bounds `κB (f a)` by a function of `κA a`
and maps `X.yes` into `Y.yes` and `X.no` into `Y.no`. -/
def FPTPromiseReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (κA : α → ℕ) (κB : β → ℕ) (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  ∃ f : α → β, ComputableInFPTWithParam encA encB κA κB f ∧
    Set.MapsTo f X.yes Y.yes ∧ Set.MapsTo f X.no Y.no

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {κA : α → ℕ} {κB : β → ℕ} {κC : γ → ℕ}
  {X : PromiseProblem α} {Y Y' : PromiseProblem β} {Z : PromiseProblem γ}

/-- On decision problems, fpt-promise reductions coincide with `FPTReducible`. -/
theorem fptPromiseReducible_ofSet_iff {A : Set α} {B : Set β} :
    FPTPromiseReducible encA encB κA κB (ofSet A) (ofSet B) ↔
      FPTReducible encA encB κA κB A B :=
  exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun ⟨hyes, hno⟩ _ => ⟨fun ha => hyes ha, fun hfa => by_contra fun ha => hno ha hfa⟩,
      fun h => ⟨fun a ha => (h a).1 ha, fun a ha hfa => ha ((h a).2 hfa)⟩⟩

/-- Every parameterized promise problem fpt-reduces to itself. -/
@[refl]
theorem FPTPromiseReducible.refl (encA : α ↪ List Bool) (κA : α → ℕ) (X : PromiseProblem α) :
    FPTPromiseReducible encA encA κA κA X X :=
  ⟨id, ⟨ComputableInPolyTime.id'.computableInFPTTime κA, id, fun _ => le_rfl⟩,
    Set.mapsTo_id _, Set.mapsTo_id _⟩

/-- Parameterized fpt-promise reductions compose. -/
@[trans]
theorem FPTPromiseReducible.trans
    (hXY : FPTPromiseReducible encA encB κA κB X Y)
    (hYZ : FPTPromiseReducible encB encC κB κC Y Z) :
    FPTPromiseReducible encA encC κA κC X Z := by
  rcases hXY with ⟨f, ⟨hf, h₁, hκ₁⟩, hfyes, hfno⟩
  rcases hYZ with ⟨g, ⟨hg, h₂, hκ₂⟩, hgyes, hgno⟩
  exact ⟨g ∘ f, ⟨hg.comp hf hκ₁, fun k => ∑ j ∈ Finset.range (h₁ k + 1), h₂ j,
    fun a => (hκ₂ (f a)).trans (le_sum_range_succ_aux h₂ (hκ₁ a))⟩,
    hgyes.comp hfyes, hgno.comp hfno⟩

/-- Enlarging the target promise yields an fpt-promise reduction via the identity. -/
theorem FPTPromiseReducible.of_subset (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    FPTPromiseReducible encB encB κB κB Y Y' :=
  ⟨id, ⟨ComputableInPolyTime.id'.computableInFPTTime κB, id, fun _ => le_rfl⟩,
    fun _ h => hyes h, fun _ h => hno h⟩

/-- A polynomial-time map bounding the parameter and preserving yes/no instances is an
fpt-promise reduction. -/
theorem FPTPromiseReducible.of_computableInPolyTime {f : α → β}
    (hf : ComputableInPolyTime f encA encB) {h : ℕ → ℕ} (hκ : ∀ a, κB (f a) ≤ h (κA a))
    (hyes : Set.MapsTo f X.yes Y.yes) (hno : Set.MapsTo f X.no Y.no) :
    FPTPromiseReducible encA encB κA κB X Y :=
  ⟨f, ⟨hf.computableInFPTTime κA, h, hκ⟩, hyes, hno⟩

/-- A polynomial-time map on padded inputs `(a, 2 ^ ν a)` with `ν a ≤ hν (κA a)` bounding the
target parameter and preserving yes/no instances is an fpt-promise reduction. -/
theorem FPTPromiseReducible.of_computableInPolyTime_pad {f : α × ℕ → β} {ν : α → ℕ}
    {hν hκ : ℕ → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encUnary) encB)
    (hν_poly : ComputableInPolyTime ν encA encUnary) (hν_le : ∀ a, ν a ≤ hν (κA a))
    (hκ_le : ∀ a, κB (f (a, 2 ^ ν a)) ≤ hκ (κA a))
    (hyes : Set.MapsTo (fun a => f (a, 2 ^ ν a)) X.yes Y.yes)
    (hno : Set.MapsTo (fun a => f (a, 2 ^ ν a)) X.no Y.no) :
    FPTPromiseReducible encA encB κA κB X Y :=
  ⟨fun a => f (a, 2 ^ ν a),
    ⟨computableInFPTTime_of_computableInPolyTime_pad hf hν_poly hν_le, hκ, hκ_le⟩,
    hyes, hno⟩

/-- **`PromiseFPT` is closed under fpt-promise reductions.** -/
theorem FPTPromiseReducible.mem_promiseFPT
    (hXY : FPTPromiseReducible encA encB κA κB X Y) (hY : Y ∈ PromiseFPT encB κB) :
    X ∈ PromiseFPT encA κA := by
  rcases hXY with ⟨f, ⟨hf, _, hκ⟩, hfyes, hfno⟩
  rcases mem_promiseFPT_iff.mp hY with ⟨g, hg, hgyes, hgno⟩
  exact mem_promiseFPT_iff.mpr ⟨g ∘ f, hg.comp hf hκ,
    fun a ha => hgyes _ (hfyes ha), fun a ha => hgno _ (hfno ha)⟩

/-- Contrapositive of `FPTPromiseReducible.mem_promiseFPT`. -/
theorem FPTPromiseReducible.not_mem_promiseFPT
    (hXY : FPTPromiseReducible encA encB κA κB X Y) (hX : X ∉ PromiseFPT encA κA) :
    Y ∉ PromiseFPT encB κB :=
  fun hY => hX (hXY.mem_promiseFPT hY)

end Reduction

/-! ### Parameterized Hardness of Promise Problems -/

section Hardness

/-- A parameterized promise problem `Y` is **hard for the parameterized class `𝒞`** under
fpt-promise reductions when every problem `A ∈ 𝒞` fpt-reduces (via `ofSet A`) to `Y`. -/
def FPTPromiseHard (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)) {β : Type}
    (enc : β ↪ List Bool) (κ : β → ℕ) (Y : PromiseProblem β) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α), A ∈ 𝒞 encA κA →
    FPTPromiseReducible encA enc κA κ (ofSet A) Y

/-- `W[1]`-hardness of a parameterized promise problem. -/
abbrev W1PromiseHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (Y : PromiseProblem β) : Prop :=
  FPTPromiseHard (@W 1) enc κ Y

variable {𝒞 𝒟 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)} {α β : Type}
  {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {X : PromiseProblem α} {Y Y' : PromiseProblem β}

/-- On decision problems, `FPTPromiseHard` coincides with `FPTHard`. -/
theorem fptPromiseHard_ofSet_iff {B : Set β} :
    FPTPromiseHard 𝒞 encB κB (ofSet B) ↔ FPTHard 𝒞 encB κB B :=
  ⟨fun h _ encA κA A hA => fptPromiseReducible_ofSet_iff.mp (h encA κA A hA),
    fun h _ encA κA A hA => fptPromiseReducible_ofSet_iff.mpr (h encA κA A hA)⟩

/-- Hardness of promise problems transfers along fpt-promise reductions. -/
theorem FPTPromiseHard.trans (hX : FPTPromiseHard 𝒞 encA κA X)
    (hXY : FPTPromiseReducible encA encB κA κB X Y) :
    FPTPromiseHard 𝒞 encB κB Y :=
  fun _ encC κC A hA => (hX encC κC A hA).trans hXY

/-- Enlarging the promise preserves hardness. -/
theorem FPTPromiseHard.mono (hY : FPTPromiseHard 𝒞 encB κB Y)
    (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    FPTPromiseHard 𝒞 encB κB Y' :=
  hY.trans (.of_subset hyes hno)

/-- Hardness for a larger class implies hardness for every subclass. -/
theorem FPTPromiseHard.mono_class
    (h𝒟𝒞 : ∀ {γ : Type} (enc : γ ↪ List Bool) (κ : γ → ℕ), 𝒟 enc κ ⊆ 𝒞 enc κ)
    (hY : FPTPromiseHard 𝒞 encB κB Y) : FPTPromiseHard 𝒟 encB κB Y :=
  fun _ encC κC A hA => hY encC κC A (h𝒟𝒞 encC κC hA)

/-- If a `𝒞`-hard promise problem lies in `PromiseFPT`, then `𝒞 ⊆ FPT` for every encoding and
parameter. -/
theorem FPTPromiseHard.subset_FPT (hY : FPTPromiseHard 𝒞 encB κB Y)
    (hFPT : Y ∈ PromiseFPT encB κB) : 𝒞 encA κA ⊆ FPT encA κA :=
  fun _ hA => ofSet_mem_promiseFPT.mp ((hY encA κA _ hA).mem_promiseFPT hFPT)

/-- If `𝒞 ≠ FPT` for some encoding and parameter while `FPT ⊆ 𝒞`, then no `𝒞`-hard promise
problem lies in `PromiseFPT`. -/
theorem FPTPromiseHard.not_mem_promiseFPT (hY : FPTPromiseHard 𝒞 encB κB Y)
    (hsub : FPT encA κA ⊆ 𝒞 encA κA) (hne : 𝒞 encA κA ≠ FPT encA κA) :
    Y ∉ PromiseFPT encB κB :=
  fun hFPT => hne (Set.Subset.antisymm (hY.subset_FPT hFPT) hsub)

/-- An fpt-promise reduction from `Clique` proves `W[1]`-hardness. -/
theorem w1PromiseHard_of_fptPromiseReducible_clique
    (h : FPTPromiseReducible encCliqueInstance encB (·.m) κB (ofSet Clique) Y) :
    W1PromiseHard encB κB Y :=
  (fptPromiseHard_ofSet_iff.mpr Clique_wHard).trans h

/-- Under `W[1] ≠ FPT`, no `W[1]`-hard promise problem lies in `PromiseFPT`. -/
theorem W1PromiseHard.not_mem_promiseFPT_of_W_one_ne_FPT (hY : W1PromiseHard encB κB Y)
    (hW : ¬ ∀ ⦃γ : Type⦄ (enc : γ ↪ List Bool) (κ : γ → ℕ), W 1 enc κ = FPT enc κ) :
    Y ∉ PromiseFPT encB κB := by
  intro hFPT
  apply hW
  intro γ enc κ
  exact Set.Subset.antisymm (hY.subset_FPT hFPT) (FPT_subset_W 1)

end Hardness

end Cslib.Complexity
