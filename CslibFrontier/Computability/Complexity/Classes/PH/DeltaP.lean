/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module

public import CslibFrontier.Computability.Complexity.Classes.BooleanHierarchy
public import CslibFrontier.Computability.Complexity.Classes.DP
public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Foundations.Order.BooleanSubalgebra

import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.Classes.P.Closure
import CslibFrontier.Computability.Complexity.Classes.PH.Oracle
import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Oracle

/-!
# Deterministic Oracle Levels `Δₖᴾ` of the Polynomial Hierarchy

This module defines and develops the deterministic oracle levels `Δₖᴾ`
(`CslibFrontier.Complexity.DeltaP`) of Stockmeyer's polynomial-time hierarchy, where
`Δ₀ᴾ = Δ₁ᴾ = P` and `Δₖ₊₁ᴾ = P^{Σₖᴾ} = ⋃_{O ∈ Σₖᴾ} P^O`.

## Main definitions

* `CslibFrontier.Complexity.DeltaP`: the `k`-th deterministic oracle level `Δₖᴾ` of the polynomial
  hierarchy for an injective bitstring encoding `enc : α ↪ List Bool`.
* `CslibFrontier.Complexity.DeltaP.booleanSubalgebra`: `DeltaP k enc` bundled as a Boolean
  subalgebra of `Set α`.
* `CslibFrontier.Complexity.DeltaPHard`, `CslibFrontier.Complexity.DeltaPComplete`: polynomial-time
  many-one hardness and completeness for `DeltaP k`.

## Main results

* `CslibFrontier.Complexity.DeltaP_zero`, `CslibFrontier.Complexity.DeltaP_one`,
  `CslibFrontier.Complexity.DeltaP_two`: `Δ₀ᴾ = P`, `Δ₁ᴾ = P`, and `Δ₂ᴾ = P^{NP}`.
* `CslibFrontier.Complexity.DeltaP_succ_eq_PWithOracle`: for any raw-word `Σₖᴾ`-complete language
  `A`, `Δₖ₊₁ᴾ = P^A`.
* `CslibFrontier.Complexity.SigmaP_subset_DeltaP_succ`,
  `CslibFrontier.Complexity.PiP_subset_DeltaP_succ`,
  `CslibFrontier.Complexity.DeltaP_succ_subset_SigmaP_succ_inter_PiP_succ`,
  `CslibFrontier.Complexity.DeltaP_mono`, `CslibFrontier.Complexity.DeltaP_subset_PH`:
  `Σₖᴾ ∪ Πₖᴾ ⊆ Δₖ₊₁ᴾ ⊆ Σₖ₊₁ᴾ ∩ Πₖ₊₁ᴾ ⊆ PH` and monotonicity of `k ↦ Δₖᴾ`.
* `CslibFrontier.Complexity.compl_mem_DeltaP`, `CslibFrontier.Complexity.inter_mem_DeltaP`,
  `CslibFrontier.Complexity.union_mem_DeltaP`, `CslibFrontier.Complexity.diff_mem_DeltaP`,
  `CslibFrontier.Complexity.symmDiff_mem_DeltaP`: Boolean closure of `Δₖᴾ`.
* `CslibFrontier.Complexity.BooleanHierarchy_subset_DeltaP_two`,
  `CslibFrontier.Complexity.DP_subset_DeltaP_two`,
  `CslibFrontier.Complexity.coDP_subset_DeltaP_two`: `BH ⊆ Δ₂ᴾ` and `DP, coDP ⊆ Δ₂ᴾ`.
* `CslibFrontier.Complexity.mem_DeltaP_of_polyTimeReducible`: downward closure under
  polynomial-time many-one reductions.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM

section Hierarchy

variable {α β : Type}

/-- The `k`-th deterministic oracle level `Δₖᴾ` of the polynomial-time hierarchy for an injective
encoding `enc : α ↪ List Bool`: `Δ₀ᴾ = P` and `Δₖ₊₁ᴾ = P^{Σₖᴾ} = ⋃_{O ∈ Σₖᴾ} P^O`. -/
def DeltaP : ℕ → (α ↪ List Bool) → Set (Set α)
  | 0, enc => P enc
  | k + 1, enc => ⋃ O ∈ SigmaP k encBits, PWithOracle O enc

/-- At level `0`, `Δ₀ᴾ` coincides with deterministic polynomial time `P`. -/
@[simp]
theorem DeltaP_zero (enc : α ↪ List Bool) : DeltaP 0 enc = P enc := by
  simp [DeltaP]

/-- Membership in `Δₖ₊₁ᴾ` holds iff the language is decidable in deterministic polynomial time with
some raw-word `Σₖᴾ` oracle. -/
theorem mem_DeltaP_succ {k : ℕ} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ DeltaP (k + 1) enc ↔ ∃ O ∈ SigmaP k encBits, L ∈ PWithOracle O enc := by
  simp [DeltaP]

/-- Dual oracle characterization `Δₖ₊₁ᴾ = ⋃_{O ∈ Πₖᴾ} P^O`. -/
theorem DeltaP_succ_eq_iUnion_PiP (k : ℕ) (enc : α ↪ List Bool) :
    DeltaP (k + 1) enc = ⋃ O ∈ PiP k encBits, PWithOracle O enc :=
  (iUnion_PWithOracle_PiP_eq k enc).symm

/-- Complete-oracle characterization of `Δₖ₊₁ᴾ`: for any raw-word `Σₖᴾ`-complete language `A`,
`Δₖ₊₁ᴾ = P^A`. -/
theorem DeltaP_succ_eq_PWithOracle {k : ℕ} {A : Set (List Bool)}
    (hA : SigmaPComplete k encBits A) (enc : α ↪ List Bool) :
    DeltaP (k + 1) enc = PWithOracle A enc :=
  hA.iUnion_PWithOracle_eq enc

private theorem deltaP_succ_eq_PWithOracle_image_SigmaSAT {k : ℕ} (hk : 1 ≤ k)
    (enc : α ↪ List Bool) :
    DeltaP (k + 1) enc = PWithOracle (encQBF '' SigmaSAT k) enc :=
  DeltaP_succ_eq_PWithOracle (image_SigmaSAT_sigmaPComplete hk) enc

/-- At level `1`, `Δ₁ᴾ = P^P = P`. -/
@[simp]
theorem DeltaP_one (enc : α ↪ List Bool) : DeltaP 1 enc = P enc := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun O hO => ?_
    rw [SigmaP_zero] at hO
    rw [PWithOracle_eq_P hO enc]
  · intro L hL
    exact mem_DeltaP_succ.mpr
      ⟨∅, by rw [SigmaP_zero]; exact (P.booleanSubalgebra encBits).bot_mem,
        P_subset_PWithOracle ∅ enc hL⟩

/-- At level `2`, `Δ₂ᴾ = P^{NP} = ⋃_{O ∈ NP} P^O`. -/
theorem DeltaP_two (enc : α ↪ List Bool) :
    DeltaP 2 enc = ⋃ O ∈ NP encBits, PWithOracle O enc := by
  simp only [DeltaP, SigmaP_one]

/-- Membership in `Δ₂ᴾ` holds iff the language lies in `P^O` for some `NP` oracle `O`. -/
theorem mem_DeltaP_two {enc : α ↪ List Bool} {L : Set α} :
    L ∈ DeltaP 2 enc ↔ ∃ O ∈ NP encBits, L ∈ PWithOracle O enc := by
  rw [DeltaP_two]
  simp

/-- Every `Σₖᴾ` language belongs to `Δₖ₊₁ᴾ`. -/
theorem SigmaP_subset_DeltaP_succ (k : ℕ) (enc : α ↪ List Bool) :
    SigmaP k enc ⊆ DeltaP (k + 1) enc :=
  Set.subset_union_left.trans (SigmaP_union_PiP_subset_iUnion_PWithOracle k enc)

/-- Every `Πₖᴾ` language belongs to `Δₖ₊₁ᴾ`. -/
theorem PiP_subset_DeltaP_succ (k : ℕ) (enc : α ↪ List Bool) :
    PiP k enc ⊆ DeltaP (k + 1) enc :=
  Set.subset_union_right.trans (SigmaP_union_PiP_subset_iUnion_PWithOracle k enc)

/-- Both `Σₖᴾ` and `Πₖᴾ` are contained in `Δₖ₊₁ᴾ`. -/
theorem SigmaP_union_PiP_subset_DeltaP_succ (k : ℕ) (enc : α ↪ List Bool) :
    SigmaP k enc ∪ PiP k enc ⊆ DeltaP (k + 1) enc :=
  SigmaP_union_PiP_subset_iUnion_PWithOracle k enc

/-- `NP` is contained in `Δ₂ᴾ = P^{NP}`. -/
theorem NP_subset_DeltaP_two (enc : α ↪ List Bool) : NP enc ⊆ DeltaP 2 enc := by
  rw [← SigmaP_one]
  exact SigmaP_subset_DeltaP_succ 1 enc

/-- `coNP` is contained in `Δ₂ᴾ = P^{NP}`. -/
theorem coNP_subset_DeltaP_two (enc : α ↪ List Bool) : coNP enc ⊆ DeltaP 2 enc := by
  rw [← PiP_one_eq_coNP]
  exact PiP_subset_DeltaP_succ 1 enc

/-- Deterministic polynomial time `P` is contained in `Δₖᴾ` for every `k : ℕ`. -/
theorem P_subset_DeltaP (k : ℕ) (enc : α ↪ List Bool) : P enc ⊆ DeltaP k enc := by
  cases k with
  | zero => exact (DeltaP_zero enc).symm.subset
  | succ k =>
    exact (SigmaP_zero.symm.subset.trans (SigmaP_mono (Nat.zero_le k))).trans
      (SigmaP_subset_DeltaP_succ k enc)

/-- `Δₖ₊₁ᴾ` is contained in the intersection `Σₖ₊₁ᴾ ∩ Πₖ₊₁ᴾ`. -/
theorem DeltaP_succ_subset_SigmaP_succ_inter_PiP_succ (k : ℕ) (enc : α ↪ List Bool) :
    DeltaP (k + 1) enc ⊆ SigmaP (k + 1) enc ∩ PiP (k + 1) enc :=
  iUnion_PWithOracle_subset_SigmaP_succ_inter_PiP_succ k enc

/-- `Δₖᴾ` is contained in `Σₖᴾ` for every `k : ℕ`. -/
theorem DeltaP_subset_SigmaP (k : ℕ) (enc : α ↪ List Bool) :
    DeltaP k enc ⊆ SigmaP k enc := by
  cases k with
  | zero => simp [SigmaP_zero]
  | succ k =>
    exact (DeltaP_succ_subset_SigmaP_succ_inter_PiP_succ k enc).trans Set.inter_subset_left

/-- `Δₖᴾ` is contained in `Πₖᴾ` for every `k : ℕ`. -/
theorem DeltaP_subset_PiP (k : ℕ) (enc : α ↪ List Bool) :
    DeltaP k enc ⊆ PiP k enc := by
  cases k with
  | zero => simp [PiP_zero]
  | succ k =>
    exact (DeltaP_succ_subset_SigmaP_succ_inter_PiP_succ k enc).trans Set.inter_subset_right

/-- Every level `Δₖᴾ` is contained in `Δₖ₊₁ᴾ`. -/
theorem DeltaP_subset_DeltaP_succ (k : ℕ) (enc : α ↪ List Bool) :
    DeltaP k enc ⊆ DeltaP (k + 1) enc :=
  (DeltaP_subset_SigmaP k enc).trans (SigmaP_subset_DeltaP_succ k enc)

/-- The hierarchy `k ↦ Δₖᴾ` is monotone. -/
theorem DeltaP_mono (enc : α ↪ List Bool) : Monotone fun k => DeltaP k enc :=
  monotone_nat_of_le_succ fun k => DeltaP_subset_DeltaP_succ k enc

/-- Every level `Δₖᴾ` lies in the polynomial-time hierarchy `PH`. -/
theorem DeltaP_subset_PH (k : ℕ) (enc : α ↪ List Bool) : DeltaP k enc ⊆ PH enc :=
  (DeltaP_subset_SigmaP k enc).trans (SigmaP_subset_PH k)

end Hierarchy

section Closure

variable {α β : Type} {k : ℕ} {enc : α ↪ List Bool} {A B : Set α}

/-- The empty language belongs to `Δₖᴾ`. -/
theorem empty_mem_DeltaP (k : ℕ) (enc : α ↪ List Bool) : ∅ ∈ DeltaP k enc :=
  P_subset_DeltaP k enc (P.booleanSubalgebra enc).bot_mem

/-- `Δₖᴾ` is closed under complementation. -/
theorem compl_mem_DeltaP (hA : A ∈ DeltaP k enc) : Aᶜ ∈ DeltaP k enc := by
  cases k with
  | zero =>
    rw [DeltaP_zero] at hA ⊢
    exact (P.booleanSubalgebra enc).compl_mem hA
  | succ k =>
    obtain ⟨O, hO, hAO⟩ := mem_DeltaP_succ.mp hA
    exact mem_DeltaP_succ.mpr ⟨O, hO, compl_mem_PWithOracle hAO⟩

/-- `Δₖᴾ` is closed under binary intersection. -/
theorem inter_mem_DeltaP (hA : A ∈ DeltaP k enc) (hB : B ∈ DeltaP k enc) :
    A ∩ B ∈ DeltaP k enc := by
  rcases k with _ | _ | k
  · rw [DeltaP_zero] at hA hB ⊢
    exact inter_mem_P hA hB
  · rw [DeltaP_one] at hA hB ⊢
    exact inter_mem_P hA hB
  · rw [deltaP_succ_eq_PWithOracle_image_SigmaSAT (Nat.succ_pos k) enc] at hA hB ⊢
    exact inter_mem_PWithOracle hA hB

/-- `Δₖᴾ` bundled as a Boolean subalgebra of `Set α`. -/
def DeltaP.booleanSubalgebra (k : ℕ) (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  BooleanSubalgebra.ofComplInf (DeltaP k enc) (empty_mem_DeltaP k enc)
    (fun _ => compl_mem_DeltaP) (fun _ _ => inter_mem_DeltaP)

/-- Coercion of `DeltaP.booleanSubalgebra` recovers `DeltaP k enc`. -/
@[simp]
theorem DeltaP.coe_booleanSubalgebra (k : ℕ) (enc : α ↪ List Bool) :
    (DeltaP.booleanSubalgebra k enc : Set (Set α)) = DeltaP k enc :=
  BooleanSubalgebra.coe_ofComplInf _ _ _ _

/-- Membership in `DeltaP.booleanSubalgebra` is membership in `DeltaP`. -/
theorem DeltaP.mem_booleanSubalgebra :
    A ∈ DeltaP.booleanSubalgebra k enc ↔ A ∈ DeltaP k enc :=
  BooleanSubalgebra.mem_ofComplInf

/-- `Δₖᴾ` is closed under binary union. -/
theorem union_mem_DeltaP (hA : A ∈ DeltaP k enc) (hB : B ∈ DeltaP k enc) :
    A ∪ B ∈ DeltaP k enc :=
  (DeltaP.booleanSubalgebra k enc).sup_mem hA hB

/-- `Δₖᴾ` is closed under set difference. -/
theorem diff_mem_DeltaP (hA : A ∈ DeltaP k enc) (hB : B ∈ DeltaP k enc) :
    A \ B ∈ DeltaP k enc :=
  (DeltaP.booleanSubalgebra k enc).sdiff_mem hA hB

/-- `Δₖᴾ` is closed under symmetric difference. -/
theorem symmDiff_mem_DeltaP (hA : A ∈ DeltaP k enc) (hB : B ∈ DeltaP k enc) :
    symmDiff A B ∈ DeltaP k enc :=
  (DeltaP.booleanSubalgebra k enc).symmDiff_mem hA hB

/-- The entire Boolean hierarchy over `NP` is contained in `Δ₂ᴾ = P^{NP}`. -/
theorem BooleanHierarchy_subset_DeltaP_two (enc : α ↪ List Bool) :
    BooleanHierarchy enc ⊆ DeltaP 2 enc :=
  BooleanHierarchy_subset (NP_subset_DeltaP_two enc) fun _ h₁ _ h₂ => diff_mem_DeltaP h₁ h₂

/-- Papadimitriou–Yannakakis's difference class `DP` is contained in `Δ₂ᴾ = P^{NP}`. -/
theorem DP_subset_DeltaP_two (enc : α ↪ List Bool) : DP enc ⊆ DeltaP 2 enc := by
  rw [← BH_two]
  exact (BH_subset_BooleanHierarchy 2).trans (BooleanHierarchy_subset_DeltaP_two enc)

/-- The dual difference class `coDP` is contained in `Δ₂ᴾ = P^{NP}`. -/
theorem coDP_subset_DeltaP_two (enc : α ↪ List Bool) : coDP enc ⊆ DeltaP 2 enc := by
  intro L hL
  simpa only [compl_compl] using compl_mem_DeltaP (DP_subset_DeltaP_two enc (mem_coDP.mp hL))

/-- `Δₖᴾ` is closed downward under polynomial-time many-one reductions. -/
theorem mem_DeltaP_of_polyTimeReducible {encB : β ↪ List Bool} {C : Set β}
    (h : PolyTimeReducible enc encB A C) (hC : C ∈ DeltaP k encB) :
    A ∈ DeltaP k enc := by
  cases k with
  | zero =>
    rw [DeltaP_zero] at hC ⊢
    exact h.mem_P hC
  | succ k =>
    obtain ⟨O, hO, hCO⟩ := mem_DeltaP_succ.mp hC
    exact mem_DeltaP_succ.mpr ⟨O, hO, h.mem_PWithOracle hCO⟩

/-- Polynomial-time many-one hardness for `Δₖᴾ`. -/
abbrev DeltaPHard (k : ℕ) (encB : β ↪ List Bool) (C : Set β) : Prop :=
  PolyTimeHard (@fun α e => DeltaP (α := α) k e) encB C

/-- Polynomial-time many-one completeness for `Δₖᴾ`. -/
abbrev DeltaPComplete (k : ℕ) (encB : β ↪ List Bool) (C : Set β) : Prop :=
  PolyTimeComplete (@fun α e => DeltaP (α := α) k e) encB C

end Closure

end CslibFrontier.Complexity
