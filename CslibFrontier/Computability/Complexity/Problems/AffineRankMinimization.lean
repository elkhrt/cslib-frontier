/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.RankPrimitives
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.CircuitCompilation
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Membership
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.HardnessGates
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Hardness
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.CircuitPolyTime
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.HardnessPolyTime

/-!
# Affine Rank Minimization (`ARM(k)`) and `∃ℝ`-Completeness of `ARM(3)`

Formalization of the Affine Rank Minimization decision problem `ARM(k)` over `ℝ`:

* `Cslib.Complexity.arm_mem_existsReal`: `ARM(k) ∈ ∃ℝ` for every fixed rank bound `k : ℕ`.
* `Cslib.Complexity.arm3_mem_existsReal_det`: independent determinantal proof of `ARM(3) ∈ ∃ℝ`.
* `Cslib.Complexity.polyTimeReducible_ETR_ARM3`: polynomial-time many-one reduction `ETR ≤ₚ ARM(3)`.
* `Cslib.Complexity.arm3_existsRealHard`: `ARM(3)` is `∃ℝ`-hard.
* `Cslib.Complexity.arm3_existsRealComplete`: `ARM(3)` is `∃ℝ`-complete.
-/
