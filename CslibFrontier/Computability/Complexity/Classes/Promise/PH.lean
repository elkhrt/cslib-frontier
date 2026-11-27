/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction

import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
import CslibFrontier.Computability.Complexity.Classes.PH.Projection

/-!
# Promise Polynomial-Time Hierarchy and Collapse Criteria

This module lifts the levels `SigmaP k` and `PiP k` of the polynomial-time hierarchy and `coNP` to
promise problems via `Cslib.Complexity.promiseClass`, defines Karp-reduction hardness and
completeness (`PromiseSigmaPHard`, `PromisePiPHard`, `PromiseSigmaPComplete`,
`PromisePiPComplete`), and proves that if a `Π₂ᵖ`-hard promise problem belongs to `PromiseNP` or
`PromiseCoNP`, then `PH = NP` at every encoding.

## Main definitions

* `CslibFrontier.Complexity.PromiseSigmaP`, `CslibFrontier.Complexity.PromisePiP`,
  `CslibFrontier.Complexity.PromiseCoNP`: promise lifts of `Σₖᵖ`, `Πₖᵖ`, and `coNP`.
* `CslibFrontier.Complexity.PromiseSigmaPHard`, `CslibFrontier.Complexity.PromisePiPHard`,
  `CslibFrontier.Complexity.PromiseSigmaPComplete`,
  `CslibFrontier.Complexity.PromisePiPComplete`: hardness and completeness of promise problems for
  levels of the polynomial-time hierarchy.

## Main results

* `CslibFrontier.Complexity.PromisePiPHard.PH_eq_NP_of_mem_PromiseNP`: if a `Π₂ᵖ`-hard promise
  problem lies in `PromiseNP`, then `PH = NP`.
* `CslibFrontier.Complexity.PromisePiPHard.PH_eq_NP_of_mem_PromiseCoNP`: if a `Π₂ᵖ`-hard promise
  problem lies in `PromiseCoNP`, then `PH = NP`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- The promise lift of `Σₖᵖ`: promise problems separated by a language in `SigmaP k enc`. -/
def PromiseSigmaP (k : ℕ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  promiseClass (SigmaP k enc)

/-- The promise lift of `Πₖᵖ`: promise problems separated by a language in `PiP k enc`. -/
def PromisePiP (k : ℕ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  promiseClass (PiP k enc)

/-- The promise lift of `coNP`: promise problems separated by a language in `coNP enc`. -/
def PromiseCoNP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  promiseClass (coNP enc)

/-- A promise problem belongs to `PromiseCoNP` iff its complement belongs to `PromiseNP`. -/
theorem mem_PromiseCoNP_iff_compl {Q : PromiseProblem α} :
    Q ∈ PromiseCoNP encA ↔ Qᶜ ∈ PromiseNP encA := by
  constructor
  · rintro ⟨A, hA, hyes, hno⟩
    exact ⟨Aᶜ, hA, Set.subset_compl_iff_disjoint_left.mpr hno,
      Set.disjoint_compl_left_iff_subset.mpr hyes⟩
  · rintro ⟨A, hA, hyes, hno⟩
    refine ⟨Aᶜ, ?_, Set.subset_compl_iff_disjoint_left.mpr hno,
      Set.disjoint_compl_left_iff_subset.mpr hyes⟩
    simpa only [coNP, Set.mem_ofPred_eq, compl_compl] using hA

/-- A promise problem is `Σₖᵖ`-hard when every language in `Σₖᵖ` reduces to it in polynomial
time. -/
def PromiseSigmaPHard (k : ℕ) (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Q => PromiseProblem.PolyTimeReducible enc encB (PromiseProblem.ofSet A) Q)
    (fun {α} => SigmaP (α := α) k) Y

/-- A promise problem is `Πₖᵖ`-hard when every language in `Πₖᵖ` reduces to it in polynomial
time. -/
def PromisePiPHard (k : ℕ) (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Q => PromiseProblem.PolyTimeReducible enc encB (PromiseProblem.ofSet A) Q)
    (fun {α} => PiP (α := α) k) Y

/-- A promise problem is `Σₖᵖ`-complete when it belongs to `PromiseSigmaP k` and is `Σₖᵖ`-hard. -/
def PromiseSigmaPComplete (k : ℕ) (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  Y ∈ PromiseSigmaP k encB ∧ PromiseSigmaPHard k encB Y

/-- A promise problem is `Πₖᵖ`-complete when it belongs to `PromisePiP k` and is `Πₖᵖ`-hard. -/
def PromisePiPComplete (k : ℕ) (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  Y ∈ PromisePiP k encB ∧ PromisePiPHard k encB Y

/-- `Σₖᵖ`-hardness transfers along polynomial-time promise reductions. -/
theorem PromiseSigmaPHard.trans {k : ℕ} {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : PromiseSigmaPHard k encA X)
    (h : PromiseProblem.PolyTimeReducible encA encB X Y) :
    PromiseSigmaPHard k encB Y :=
  HardUnder.trans (fun _ _ h₁ h₂ => h₁.trans h₂) hX h

/-- `Πₖᵖ`-hardness transfers along polynomial-time promise reductions. -/
theorem PromisePiPHard.trans {k : ℕ} {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : PromisePiPHard k encA X)
    (h : PromiseProblem.PolyTimeReducible encA encB X Y) :
    PromisePiPHard k encB Y :=
  HardUnder.trans (fun _ _ h₁ h₂ => h₁.trans h₂) hX h

/-- `PromiseSigmaP k` is closed downward under polynomial-time promise reductions. -/
theorem mem_PromiseSigmaP_of_polyTimeReducible {k : ℕ} {X : PromiseProblem α}
    {Y : PromiseProblem β} (h : PromiseProblem.PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseSigmaP k encB) : X ∈ PromiseSigmaP k encA := by
  obtain ⟨B, hB, hyes, hno⟩ := hY
  obtain ⟨A, hAyes, hAno, hAB⟩ := h.exists_polyTimeReducible hyes hno
  exact ⟨A, hAB.mem_SigmaP hB, hAyes, hAno⟩

/-- `PromisePiP k` is closed downward under polynomial-time promise reductions. -/
theorem mem_PromisePiP_of_polyTimeReducible {k : ℕ} {X : PromiseProblem α}
    {Y : PromiseProblem β} (h : PromiseProblem.PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromisePiP k encB) : X ∈ PromisePiP k encA := by
  obtain ⟨B, hB, hyes, hno⟩ := hY
  obtain ⟨A, hAyes, hAno, hAB⟩ := h.exists_polyTimeReducible hyes hno
  exact ⟨A, hAB.mem_PiP hB, hAyes, hAno⟩

/-- If a `Π₂ᵖ`-hard promise problem belongs to `PromiseNP`, then `PH = NP` at every encoding. -/
theorem PromisePiPHard.PH_eq_NP_of_mem_PromiseNP {Y : PromiseProblem β}
    (hHard : PromisePiPHard 2 encB Y) (hNP : Y ∈ PromiseNP encB) :
    PH encA = NP encA := by
  refine PH_eq_NP_of_coNP_subset_NP fun {δ} encD L hL => ?_
  have hPi1 : L ∈ PiP 1 encD := by rwa [PiP_one_eq_coNP]
  have hPi2 : L ∈ PiP 2 encD := PiP_mono (by omega : 1 ≤ 2) hPi1
  exact ofSet_mem_PromiseNP.mp ((hHard encD L hPi2).mem_PromiseNP hNP)

/-- If a `Π₂ᵖ`-hard promise problem belongs to `PromiseCoNP`, then `PH = NP` at every encoding. -/
theorem PromisePiPHard.PH_eq_NP_of_mem_PromiseCoNP {Y : PromiseProblem β}
    (hHard : PromisePiPHard 2 encB Y) (hCoNP : Y ∈ PromiseCoNP encB) :
    PH encA = NP encA := by
  have hNP : Yᶜ ∈ PromiseNP encB := mem_PromiseCoNP_iff_compl.mp hCoNP
  refine PH_eq_NP_of_coNP_subset_NP fun {δ} encD L hL => ?_
  have hPi1 : L ∈ PiP 1 encD := by rwa [PiP_one_eq_coNP]
  have hSig2 : L ∈ SigmaP 2 encD := PiP_subset_SigmaP_succ 1 hPi1
  have hPi2 : Lᶜ ∈ PiP 2 encD := compl_mem_PiP_of_mem_SigmaP hSig2
  obtain ⟨f, hf, hyes, hno⟩ := hHard encD Lᶜ hPi2
  have hred : PromiseProblem.PolyTimeReducible encD encB (PromiseProblem.ofSet L) Yᶜ := by
    refine ⟨f, hf, ?_, ?_⟩
    · intro x hx
      exact hno (by simpa [PromiseProblem.ofSet] using hx)
    · intro x hx
      exact hyes (by simpa [PromiseProblem.ofSet] using hx)
  exact ofSet_mem_PromiseNP.mp (hred.mem_PromiseNP hNP)

end CslibFrontier.Complexity
