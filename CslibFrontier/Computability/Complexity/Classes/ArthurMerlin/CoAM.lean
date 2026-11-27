/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Collapse

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification

/-!
# The Complement Class `coAM`, `AM ∩ coAM`, and `NP ⊆ coAM` Collapse

This module defines the complement Arthur–Merlin class `coAM` and the intersection class
`AMInterCoAM` ($\mathrm{AM} \cap \mathrm{coAM}$) on top of `Cslib.Complexity.AM`, establishes their
complement dualities, fundamental inclusions from `P`, `NP`, `coNP`, and `BPP`, closure under
polynomial-time many-one reductions, placement inside the second level of the polynomial hierarchy
($\mathrm{coAM} \subseteq \Sigma_2^{\mathrm{P}}$, $\mathrm{AM} \cap \mathrm{coAM} \subseteq
\Sigma_2^{\mathrm{P}} \cap \Pi_2^{\mathrm{P}}$), and the Boppana–Håstad–Zachos collapse
consequence of $\mathrm{NP} \subseteq \mathrm{coAM}$.

## Main definitions

* `Cslib.Complexity.coAM`: the complement class `{A | Aᶜ ∈ AM enc}`.
* `Cslib.Complexity.AMInterCoAM`: the intersection class `AM enc ∩ coAM enc`.

## Main results

* `Cslib.Complexity.coNP_subset_coAM`, `Cslib.Complexity.BPP_subset_coAM`,
  `Cslib.Complexity.P_subset_AM`, `Cslib.Complexity.P_subset_coAM`,
  `Cslib.Complexity.P_subset_AMInterCoAM`, `Cslib.Complexity.BPP_subset_AMInterCoAM`.
* `Cslib.Complexity.PolyTimeReducible.mem_coAM`,
  `Cslib.Complexity.PolyTimeReducible.mem_AMInterCoAM`.
* `Cslib.Complexity.coAM_subset_SigmaP_two`,
  `Cslib.Complexity.AMInterCoAM_subset_SigmaP_two_inter_PiP_two`,
  `Cslib.Complexity.coAM_subset_PH`.
* `Cslib.Complexity.coNP_subset_AM_iff_NP_subset_coAM`,
  `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_coAM`,
  `Cslib.Complexity.SigmaP_two_eq_PiP_two_of_NP_subset_coAM`,
  `Cslib.Complexity.PH_eq_SigmaP_two_of_NPComplete_mem_coAM`.
-/

public section

namespace Cslib.Complexity

variable {α β : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The complement Arthur–Merlin class `coAM`: a decision problem `A` lies in `coAM enc` if and
only if its complement `Aᶜ` lies in `Cslib.Complexity.AM enc`. -/
@[expose] def coAM (enc : α ↪ List Bool) : Set (Set α) :=
  {A | Aᶜ ∈ AM enc}

/-- Membership in `coAM` is membership of the complement in `AM`. -/
theorem mem_coAM_iff : A ∈ coAM enc ↔ Aᶜ ∈ AM enc :=
  Iff.rfl

/-- `coAM` is the preimage of `AM` under set complementation. -/
theorem coAM_eq_preimage_compl_AM (enc : α ↪ List Bool) :
    coAM enc = compl ⁻¹' AM enc :=
  rfl

/-- Complement duality: `Aᶜ ∈ coAM enc ↔ A ∈ AM enc`. -/
theorem compl_mem_coAM_iff : Aᶜ ∈ coAM enc ↔ A ∈ AM enc := by
  rw [mem_coAM_iff, compl_compl]

/-- Complement duality: `Aᶜ ∈ AM enc ↔ A ∈ coAM enc`. -/
theorem compl_mem_AM_iff : Aᶜ ∈ AM enc ↔ A ∈ coAM enc :=
  Iff.rfl

/-- The intersection class `AM ∩ coAM` with respect to an encoding `enc`. -/
@[expose] def AMInterCoAM (enc : α ↪ List Bool) : Set (Set α) :=
  AM enc ∩ coAM enc

/-- Membership in `AMInterCoAM` unfolds to simultaneous membership in `AM` and `coAM`. -/
theorem mem_AMInterCoAM_iff : A ∈ AMInterCoAM enc ↔ A ∈ AM enc ∧ A ∈ coAM enc :=
  Iff.rfl

/-- `AM ∩ coAM` is closed under set complementation. -/
theorem compl_mem_AMInterCoAM_iff : Aᶜ ∈ AMInterCoAM enc ↔ A ∈ AMInterCoAM enc := by
  rw [mem_AMInterCoAM_iff, mem_AMInterCoAM_iff, compl_mem_AM_iff, compl_mem_coAM_iff, and_comm]

/-- **`coNP ⊆ coAM`**: complements of `NP` problems lie in `coAM`. -/
theorem coNP_subset_coAM : coNP enc ⊆ coAM enc := fun _ hA ↦
  NP_subset_AM (mem_coNP.mp hA)

/-- **`P ⊆ AM`**: every polynomial-time decidable problem lies in `AM`. -/
theorem P_subset_AM : P enc ⊆ AM enc :=
  P_subset_NP.trans NP_subset_AM

/-- **`P ⊆ coAM`**: every polynomial-time decidable problem lies in `coAM`. -/
theorem P_subset_coAM : P enc ⊆ coAM enc :=
  P_subset_coNP.trans coNP_subset_coAM

/-- **`BPP ⊆ coAM`**: since `BPP` is closed under complements and `BPP ⊆ AM`, `BPP ⊆ coAM`. -/
theorem BPP_subset_coAM : BPP enc ⊆ coAM enc := fun A hA ↦ by
  rw [mem_coAM_iff]
  have hcompl : Aᶜ ∈ BPP enc := by
    change A ∈ compl ⁻¹' BPP enc
    rwa [← BPP_eq_preimage_compl_BPP enc]
  exact BPP_subset_AM hcompl

/-- **`P ⊆ AM ∩ coAM`**. -/
theorem P_subset_AMInterCoAM : P enc ⊆ AMInterCoAM enc := fun _ hA ↦
  ⟨P_subset_AM hA, P_subset_coAM hA⟩

/-- **`BPP ⊆ AM ∩ coAM`**. -/
theorem BPP_subset_AMInterCoAM : BPP enc ⊆ AMInterCoAM enc := fun _ hA ↦
  ⟨BPP_subset_AM hA, BPP_subset_coAM hA⟩

/-- The empty language belongs to `AM ∩ coAM`. -/
theorem empty_mem_AMInterCoAM : (∅ : Set α) ∈ AMInterCoAM enc :=
  P_subset_AMInterCoAM empty_mem_P

/-- The universal language belongs to `AM ∩ coAM`. -/
theorem univ_mem_AMInterCoAM : (Set.univ : Set α) ∈ AMInterCoAM enc :=
  P_subset_AMInterCoAM univ_mem_P

/-- **`coAM` is closed under polynomial-time many-one reductions**. -/
theorem PolyTimeReducible.mem_coAM {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ coAM encB) : A ∈ coAM enc :=
  h.compl.mem_AM hB

/-- **`AM ∩ coAM` is closed under polynomial-time many-one reductions**. -/
theorem PolyTimeReducible.mem_AMInterCoAM {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ AMInterCoAM encB) :
    A ∈ AMInterCoAM enc :=
  ⟨h.mem_AM hB.1, h.mem_coAM hB.2⟩

/-- **`coAM ⊆ Σ₂`**: complements of `AM ⊆ Π₂` problems lie in `Σ₂`. -/
theorem coAM_subset_SigmaP_two : coAM enc ⊆ SigmaP 2 enc := fun _ hA ↦
  compl_mem_PiP_iff.mp (AM_subset_PiP_two hA)

/-- **`AM ∩ coAM ⊆ Σ₂ ∩ Π₂`**. -/
theorem AMInterCoAM_subset_SigmaP_two_inter_PiP_two :
    AMInterCoAM enc ⊆ SigmaP 2 enc ∩ PiP 2 enc := fun _ hA ↦
  ⟨coAM_subset_SigmaP_two hA.2, AM_subset_PiP_two hA.1⟩

/-- **`coAM ⊆ PH`**. -/
theorem coAM_subset_PH : coAM enc ⊆ PH enc := fun _ hA ↦
  Set.mem_iUnion.mpr ⟨2, coAM_subset_SigmaP_two hA⟩

/-- Global equivalence between `coNP ⊆ AM` and `NP ⊆ coAM` across all encodings. -/
theorem coNP_subset_AM_iff_NP_subset_coAM :
    (∀ {γ : Type} (encC : γ ↪ List Bool), coNP encC ⊆ AM encC) ↔
      (∀ {γ : Type} (encC : γ ↪ List Bool), NP encC ⊆ coAM encC) := by
  constructor
  · intro h γ encC A hA
    rw [mem_coAM_iff]
    exact h encC (mem_coNP.mpr (by rwa [compl_compl]))
  · intro h γ encC A hA
    have h' : Aᶜ ∈ coAM encC := h encC (mem_coNP.mp hA)
    rwa [compl_mem_coAM_iff] at h'

/-- **Boppana–Håstad–Zachos collapse (`NP ⊆ coAM` form)**: if `NP ⊆ coAM` for all encodings,
then `PH = Σ₂`. -/
theorem PH_eq_SigmaP_two_of_NP_subset_coAM
    (h : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC ⊆ coAM encC) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_coNP_subset_AM (coNP_subset_AM_iff_NP_subset_coAM.mpr h)

/-- If `NP ⊆ coAM` for all encodings, then `Σ₂ = Π₂`. -/
theorem SigmaP_two_eq_PiP_two_of_NP_subset_coAM
    (h : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC ⊆ coAM encC) :
    SigmaP 2 enc = PiP 2 enc :=
  (PiP_two_eq_SigmaP_two_of_coNP_subset_AM (coNP_subset_AM_iff_NP_subset_coAM.mpr h)).symm

/-- If an `NP`-hard problem `B` belongs to `coAM`, then `NP ⊆ coAM` for every encoding. -/
theorem NP_subset_coAM_of_NPHard_mem_coAM {encB : β ↪ List Bool} {B : Set β}
    (hHard : NPHard encB B) (hB : B ∈ coAM encB) {γ : Type} (encC : γ ↪ List Bool) :
    NP encC ⊆ coAM encC := fun A hA ↦
  (hHard encC A hA).mem_coAM hB

/-- **Collapse from an `NP`-complete problem in `coAM` (or `AM ∩ coAM`)**: if an `NP`-complete
problem lies in `coAM`, then `PH = Σ₂`. -/
theorem PH_eq_SigmaP_two_of_NPComplete_mem_coAM {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) (hCoAM : B ∈ coAM encB) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_NP_subset_coAM (NP_subset_coAM_of_NPHard_mem_coAM hB.2 hCoAM)

end Cslib.Complexity
