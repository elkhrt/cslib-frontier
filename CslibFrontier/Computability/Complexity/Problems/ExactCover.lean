/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Parameterized.Promise
public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith

/-!
# Exact Set Cover and Parameterized Gap Set Cover Promise Problems

Exact partition covering predicates (`SetSystem.IsExactCover`, `SetSystem.HasExactCover`) and
parameterized `r`-gap promise problems (`GapSetCoverParam`, `GapExactCover`) built directly on
`Cslib.Complexity.SetSystem`.

## Main definitions

* `Cslib.Complexity.SetSystem.IsExactCover`, `Cslib.Complexity.SetSystem.HasExactCover`.
* `Cslib.Complexity.GapSetCoverParam`, `Cslib.Complexity.GapExactCover`.

## Main results

* `Cslib.Complexity.SetSystem.IsExactCover.isCover`.
* `Cslib.Complexity.fptPromiseReducible_gapExactCover_mono`,
  `Cslib.Complexity.fptPromiseReducible_gapExactCover_gapSetCover`.
-/

public section

namespace Cslib.Complexity

namespace SetSystem

/-- A selection of indices `C` is an **exact cover** of `S` when `C` covers `S.ground` and distinct
selected sets in `C` are pairwise disjoint. -/
@[expose]
def IsExactCover (S : SetSystem) (C : Finset (Fin S.sets.length)) : Prop :=
  S.IsCover C ∧ ∀ i ∈ C, ∀ j ∈ C, i ≠ j → ∀ u, u ∈ S.sets[i] → u ∉ S.sets[j]

/-- Every exact cover is a set cover. -/
theorem IsExactCover.isCover {S : SetSystem} {C : Finset (Fin S.sets.length)}
    (h : SetSystem.IsExactCover S C) : S.IsCover C := h.1

/-- `S` admits an exact cover of exact cardinality `k`. -/
@[expose]
def HasExactCover (S : SetSystem) (k : ℕ) : Prop :=
  ∃ C : Finset (Fin S.sets.length), SetSystem.IsExactCover S C ∧ C.card = k

end SetSystem

/-- **Parameterized `r`-gap `k`-SetCover** (`r ≥ 1`):
- Yes: `S` admits a set cover of size at most `k`;
- No: every set cover of `S` has size strictly greater than `r * k`. -/
@[expose]
def GapSetCoverParam (r : ℝ) (hr : 1 ≤ r) : PromiseProblem (SetSystem × ℕ) where
  yes := {p | ∃ C : Finset (Fin p.1.sets.length), p.1.IsCover C ∧ C.card ≤ p.2}
  no := {p | ∀ C : Finset (Fin p.1.sets.length), p.1.IsCover C → r * (p.2 : ℝ) < (C.card : ℝ)}
  disjoint := Set.disjoint_left.mpr fun p ⟨C, hC, hle⟩ hno => by
    have h1 : (C.card : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hle
    have h2 : (p.2 : ℝ) ≤ r * (p.2 : ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hr
    linarith [hno C hC]

/-- **Parameterized `r`-gap `k`-ExactCover** (`r ≥ 1`):
- Yes: `S` admits an exact cover (partition) of `S.ground` consisting of `k` sets;
- No: every set cover of `S` has size strictly greater than `r * k`. -/
@[expose]
def GapExactCover (r : ℝ) (hr : 1 ≤ r) : PromiseProblem (SetSystem × ℕ) where
  yes := {p | SetSystem.HasExactCover p.1 p.2}
  no := {p | ∀ C : Finset (Fin p.1.sets.length), p.1.IsCover C → r * (p.2 : ℝ) < (C.card : ℝ)}
  disjoint := Set.disjoint_left.mpr fun p ⟨C, hC, hcard⟩ hno => by
    have h1 : (C.card : ℝ) = (p.2 : ℝ) := by exact_mod_cast hcard
    have h2 : (p.2 : ℝ) ≤ r * (p.2 : ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hr
    linarith [hno C hC.isCover]

/-- Monotonicity of `GapExactCover` in the gap factor: larger `r` makes the problem easier, so
`GapExactCover r₂` fpt-promise reduces to `GapExactCover r₁` when `1 ≤ r₁ ≤ r₂`. -/
theorem fptPromiseReducible_gapExactCover_mono {r₁ r₂ : ℝ} (hr₁ : 1 ≤ r₁) (h : r₁ ≤ r₂) :
    FPTPromiseReducible encSetCover encSetCover Prod.snd Prod.snd
      (GapExactCover r₂ (hr₁.trans h)) (GapExactCover r₁ hr₁) :=
  FPTPromiseReducible.of_subset subset_rfl fun p hno C hC =>
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg p.2)).trans_lt (hno C hC)

/-- `GapExactCover r` fpt-promise reduces to `GapSetCoverParam r`. -/
theorem fptPromiseReducible_gapExactCover_gapSetCover {r : ℝ} (hr : 1 ≤ r) :
    FPTPromiseReducible encSetCover encSetCover Prod.snd Prod.snd
      (GapExactCover r hr) (GapSetCoverParam r hr) :=
  FPTPromiseReducible.of_subset (fun _ ⟨C, hC, hcard⟩ => ⟨C, hC.isCover, hcard.le⟩) subset_rfl

end Cslib.Complexity
