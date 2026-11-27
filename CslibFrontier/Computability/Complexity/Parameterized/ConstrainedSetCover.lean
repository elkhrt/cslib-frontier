/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset

import CslibFrontier.Computability.Complexity.FineGrained.Padding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Constrained Set Cover and Fixed-Parameter Tractability

This module formalizes the **Constrained Set Cover (CSC)** problem (selecting one candidate from
each of `m` candidate groups to cover a finite requirement set `R`) and proves that it is
fixed-parameter tractable in the number of requirements `|R|`.

## Main definitions

* `CslibFrontier.Complexity.AbstractCSC`: polymorphic abstract CSC instance over finite sets.
* `CslibFrontier.Complexity.AbstractCSC.IsDPTable`, `AbstractCSC.algTable`: dynamic-programming
  table specification and subset-DP construction.
* `CslibFrontier.Complexity.CSCInstance`, `encCSCInstance`, `ConstrainedSetCover`: machine-encodable
  CSC instance, binary encoding, and decision problem.
* `CslibFrontier.Complexity.cscBoolOfPad`: polynomial-time padded bitmask DP evaluator.

## Main results

* `CslibFrontier.Complexity.AbstractCSC.canCoverPrefix_succ_iff`: recursive prefix-covering
  characterization.
* `CslibFrontier.Complexity.AbstractCSC.algTable_isDPTable`,
  `AbstractCSC.extract_solution_of_isDPTable`: DP table soundness/completeness and backwards
  solution extraction.
* `CslibFrontier.Complexity.AbstractCSC.alg_loop_count_le`: `2 ^ (2 * |R|) * |C|` inner-loop bound.
* `CslibFrontier.Complexity.ConstrainedSetCover_decidableInExpTime`,
  `ConstrainedSetCover_mem_FPT`: multi-tape Turing-machine single-exponential time bound and
  membership in `Cslib.Complexity.FPT` parameterized by `CSCInstance.numReqs`.
-/

public section

namespace CslibFrontier.Complexity

/-! ### 1. Abstract Constrained Set Cover, DP Specification, Recursion, and Extraction -/

section AbstractCSC

variable {α β : Type*}

/-- An abstract instance of **Constrained Set Cover**: a finite set of requirements `reqs`, `m`
candidate sets `cands 0, ..., cands (m - 1)`, and a map `satisfies` assigning each candidate its
satisfied requirements. -/
structure AbstractCSC (α β : Type*) (m : ℕ) where
  /-- Universe of requirements `R`. -/
  reqs : Finset β
  /-- Candidate sets `C₁, ..., C_m`. -/
  cands : Fin m → Finset α
  /-- Requirements satisfied by each candidate. -/
  satisfies : α → Finset β

/-- A choice `s : Fin m → α` is a *constrained set cover* if `s i ∈ C_i` for all `i` and the
union of `satisfies (s i)` covers all of `reqs`. -/
def AbstractCSC.IsSolution {m : ℕ} (inst : AbstractCSC α β m) (s : Fin m → α) : Prop :=
  (∀ i : Fin m, s i ∈ inst.cands i) ∧
    ∀ r ∈ inst.reqs, ∃ i : Fin m, r ∈ inst.satisfies (s i)

/-- Prefix solvability: there exist `s_0 ∈ C_0, ..., s_{i-1} ∈ C_{i-1}` covering `R`. -/
def AbstractCSC.CanCoverPrefix {m : ℕ} (inst : AbstractCSC α β m) (i : ℕ) (R : Finset β) : Prop :=
  ∃ s : (j : Fin m) → j.1 < i → α,
    (∀ j (hj : j.1 < i), s j hj ∈ inst.cands j) ∧
      ∀ r ∈ R, ∃ j, ∃ (hj : j.1 < i), r ∈ inst.satisfies (s j hj)

/-- Prefix solvability at `i = 0` holds iff `R = ∅`. -/
theorem AbstractCSC.canCoverPrefix_zero_iff {m : ℕ} (inst : AbstractCSC α β m) (R : Finset β) :
    inst.CanCoverPrefix 0 R ↔ R = ∅ := by
  constructor
  · rintro ⟨_, _, hcov⟩
    ext r
    simp only [Finset.notMem_empty, iff_false]
    intro hr
    obtain ⟨j, hj, _⟩ := hcov r hr
    omega
  · rintro rfl
    exact ⟨fun j hj => (Nat.not_lt_zero j.1 hj).elim, fun j hj => (Nat.not_lt_zero j.1 hj).elim,
      fun r hr => (Finset.notMem_empty r hr).elim⟩

/-- Prefix solvability is downward-closed in `R`. -/
theorem AbstractCSC.CanCoverPrefix.mono_reqs {m : ℕ} {inst : AbstractCSC α β m} {i : ℕ}
    {R₁ R₂ : Finset β} (h : inst.CanCoverPrefix i R₂) (hsub : R₁ ⊆ R₂) :
    inst.CanCoverPrefix i R₁ := by
  obtain ⟨s, hs, hcov⟩ := h
  exact ⟨s, hs, fun r hr => hcov r (hsub hr)⟩

/-- At `i = m`, `CanCoverPrefix m inst.reqs` is equivalent to the existence of a solution. -/
theorem AbstractCSC.canCoverPrefix_full_iff {m : ℕ} (inst : AbstractCSC α β m) :
    inst.CanCoverPrefix m inst.reqs ↔ ∃ s, inst.IsSolution s := by
  constructor
  · rintro ⟨s, hs, hcov⟩
    refine ⟨fun j => s j j.isLt, fun j => hs j j.isLt, fun r hr => ?_⟩
    obtain ⟨j, _, hjr⟩ := hcov r hr
    exact ⟨j, hjr⟩
  · rintro ⟨s, hs, hcov⟩
    exact ⟨fun j _ => s j, fun j _ => hs j, fun r hr =>
      let ⟨j, hj⟩ := hcov r hr; ⟨j, j.isLt, hj⟩⟩

/-- Dynamic-programming table specification for Constrained Set Cover: a family of tables `D`
returning `Option α` satisfies `IsDPTable` when for every `i < m` and `R ⊆ inst.reqs`:
- `D (i + 1) R = some c` implies `c ∈ C_i` and `CanCoverPrefix i (R \ Ψ(c))`;
- `D (i + 1) R = none` iff `¬ CanCoverPrefix (i + 1) R`. -/
structure AbstractCSC.IsDPTable [DecidableEq β] {m : ℕ} (inst : AbstractCSC α β m)
    (D : ℕ → Finset β → Option α) : Prop where
  /-- For `i < m`, any non-`⊥` value `some c` is in `C_i` and extends a prefix covering
  `R \ Ψ(c)`. -/
  some_spec : ∀ (i : Fin m) (R : Finset β) (c : α), D (i.1 + 1) R = some c →
    c ∈ inst.cands i ∧ inst.CanCoverPrefix i.1 (R \ inst.satisfies c)
  /-- `D (i + 1) R` is non-`⊥` iff `R` is coverable by the first `i + 1` candidate sets. -/
  isSome_iff : ∀ (i : Fin m) (R : Finset β), (D (i.1 + 1) R).isSome ↔
    inst.CanCoverPrefix (i.1 + 1) R

/-- Recursive characterization of prefix solvability `CanCoverPrefix (i + 1) R`. -/
theorem AbstractCSC.canCoverPrefix_succ_iff [DecidableEq β] {m : ℕ} (inst : AbstractCSC α β m)
    (i : Fin m) (R : Finset β) :
    inst.CanCoverPrefix (i.1 + 1) R ↔
      ∃ K ⊆ R, ∃ c ∈ inst.cands i, R ⊆ K ∪ inst.satisfies c ∧ inst.CanCoverPrefix i.1 K := by
  constructor
  · rintro ⟨s, hs, hcov⟩
    let c := s i (Nat.lt_succ_self i.1)
    have hc : c ∈ inst.cands i := hs i (Nat.lt_succ_self i.1)
    let K : Finset β := R \ inst.satisfies c
    refine ⟨K, Finset.sdiff_subset, c, hc, ?_, ?_⟩
    · intro r hr
      by_cases hrc : r ∈ inst.satisfies c
      · exact Finset.mem_union_right _ hrc
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hr, hrc⟩)
    · refine ⟨fun j hj => s j (Nat.lt_trans hj (Nat.lt_succ_self i.1)),
        fun j hj => hs j (Nat.lt_trans hj (Nat.lt_succ_self i.1)), fun r hr => ?_⟩
      obtain ⟨hrR, hrc⟩ := Finset.mem_sdiff.mp hr
      obtain ⟨j, hj, hjr⟩ := hcov r hrR
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact ⟨j, hlt, hjr⟩
      · have hji : j = i := Fin.ext heq
        subst hji
        exact (hrc hjr).elim
  · rintro ⟨K, _, c, hc, hRsub, ⟨s, hs, hcov⟩⟩
    refine ⟨fun j hj => if h : j.1 < i.1 then s j h else c, fun j hj => ?_, fun r hr => ?_⟩
    · dsimp only
      split_ifs with h
      · exact hs j h
      · have hji : j = i := Fin.ext (by omega)
        exact hji ▸ hc
    · rcases Finset.mem_union.mp (hRsub hr) with hrK | hrc
      · obtain ⟨j, hj, hjr⟩ := hcov r hrK
        refine ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i.1), ?_⟩
        simpa [hj] using hjr
      · refine ⟨i, Nat.lt_succ_self i.1, ?_⟩
        have hnot : ¬i.1 < i.1 := Nat.lt_irrefl i.1
        simpa [hnot] using hrc

/-- Bottom-up dynamic programming table `D_i(S)` over subsets `S ⊆ R`. -/
noncomputable def AbstractCSC.algTable [DecidableEq β] {m : ℕ} (inst : AbstractCSC α β m) :
    ℕ → Finset β → Option α
  | 0, _ => none
  | i + 1, R =>
    if hi : i < m then
      let prev := inst.algTable i
      let ok (c : α) : Prop :=
        ∃ K ∈ R.powerset, R ⊆ K ∪ inst.satisfies c ∧ (i = 0 ∧ K = ∅ ∨ 0 < i ∧ (prev K).isSome)
      if h : ∃ c ∈ inst.cands ⟨i, hi⟩, ok c then some h.choose else none
    else none

/-- Correctness of the bottom-up DP table: `algTable` satisfies `IsDPTable`. -/
theorem AbstractCSC.algTable_isDPTable [DecidableEq β] {m : ℕ} (inst : AbstractCSC α β m) :
    inst.IsDPTable inst.algTable := by
  have hmain : ∀ (k : ℕ) (hk : k ≤ m) (R : Finset β),
      (k = 0 → True) ∧
      ∀ (i : Fin m), i.1 + 1 = k →
        (∀ c, inst.algTable (i.1 + 1) R = some c →
          c ∈ inst.cands i ∧ inst.CanCoverPrefix i.1 (R \ inst.satisfies c)) ∧
        ((inst.algTable (i.1 + 1) R).isSome ↔ inst.CanCoverPrefix (i.1 + 1) R) := by
    intro k
    induction k with
    | zero => intro _ _ ; exact ⟨fun _ => trivial, fun i hi => by omega⟩
    | succ k ih =>
      intro hk R
      refine ⟨fun h => by omega, fun i hi => ?_⟩
      have hik : i.1 = k := by omega
      have hi_lt : i.1 < m := i.isLt
      have hprev_iff : ∀ K : Finset β,
          (i.1 = 0 ∧ K = ∅ ∨ 0 < i.1 ∧ (inst.algTable i.1 K).isSome) ↔
            inst.CanCoverPrefix i.1 K := by
        intro K
        rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
        · rw [h0, inst.canCoverPrefix_zero_iff]
          simp
        · simp only [Nat.ne_of_gt hpos, false_and, false_or, hpos, true_and]
          let j : Fin m := ⟨i.1 - 1, by omega⟩
          have hj : j.1 + 1 = k := by simp [j]; omega
          have hsub : i.1 = j.1 + 1 := by simp [j]; omega
          rw [hsub]
          exact ((ih (by omega) K).2 j hj).2
      have hstep_iff : ∀ (c : α),
          (∃ K ∈ R.powerset, R ⊆ K ∪ inst.satisfies c ∧
            (i.1 = 0 ∧ K = ∅ ∨ 0 < i.1 ∧ (inst.algTable i.1 K).isSome)) ↔
            inst.CanCoverPrefix i.1 (R \ inst.satisfies c) := by
        intro c
        constructor
        · rintro ⟨K, _, hRsub, hK⟩
          have hcovK : inst.CanCoverPrefix i.1 K := (hprev_iff K).mp hK
          refine hcovK.mono_reqs fun r hr => ?_
          obtain ⟨hrR, hrc⟩ := Finset.mem_sdiff.mp hr
          exact (Finset.mem_union.mp (hRsub hrR)).resolve_right hrc
        · intro hcov
          refine ⟨R \ inst.satisfies c, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_,
            (hprev_iff _).mpr hcov⟩
          intro r hr
          by_cases hrc : r ∈ inst.satisfies c
          · exact Finset.mem_union_right _ hrc
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hr, hrc⟩)
      constructor
      · intro c hc
        simp only [algTable, hi_lt, ↓reduceDIte] at hc
        split_ifs at hc with hex
        · obtain rfl := Option.some.inj hc
          exact ⟨hex.choose_spec.1, (hstep_iff _).mp hex.choose_spec.2⟩
      · rw [inst.canCoverPrefix_succ_iff i R]
        simp only [algTable, hi_lt, ↓reduceDIte]
        constructor
        · intro hsome
          split_ifs at hsome with hex
          · obtain ⟨c, hc, hok⟩ := hex
            obtain ⟨K, hKmem, hRsub, hK⟩ := hok
            exact ⟨K, Finset.mem_powerset.mp hKmem, c, hc, hRsub, (hprev_iff K).mp hK⟩
          · simp at hsome
        · rintro ⟨K, hKR, c, hc, hRsub, hcovK⟩
          have hex : ∃ c ∈ inst.cands i,
              ∃ K ∈ R.powerset, R ⊆ K ∪ inst.satisfies c ∧
                (i.1 = 0 ∧ K = ∅ ∨ 0 < i.1 ∧ (inst.algTable i.1 K).isSome) :=
            ⟨c, hc, K, Finset.mem_powerset.mpr hKR, hRsub, (hprev_iff K).mpr hcovK⟩
          rw [dite_eq_left hex]
          rfl
  exact ⟨fun i R c hc => ((hmain (i.1 + 1) i.isLt R).2 i rfl).1 c hc,
    fun i R => ((hmain (i.1 + 1) i.isLt R).2 i rfl).2⟩

/-- Backwards solution extraction from a DP table: given any valid DP table `D`, extracting
`s_m = D_m(R)`, `s_{i-1} = D_{i-1}(R \ ⋃_{j≥i} Ψ(s_j))` produces a valid constrained set cover
whenever `D_m(R) ≠ ⊥`. -/
theorem AbstractCSC.extract_solution_of_isDPTable [DecidableEq β] {m : ℕ}
    (inst : AbstractCSC α β m) {D : ℕ → Finset β → Option α} (hD : inst.IsDPTable D) :
    (∀ R : Finset β, inst.CanCoverPrefix m R ↔ (m = 0 ∧ R = ∅ ∨ 0 < m ∧ (D m R).isSome)) ∧
    (inst.CanCoverPrefix m inst.reqs → ∃ s : Fin m → α, inst.IsSolution s) := by
  constructor
  · intro R
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [inst.canCoverPrefix_zero_iff]; simp
    · simp only [Nat.ne_of_gt hm, false_and, false_or, hm, true_and]
      let last : Fin m := ⟨m - 1, by omega⟩
      have hlast : last.1 + 1 = m := by simp [last]; omega
      simpa [hlast] using (hD.isSome_iff last R).symm
  · intro h
    -- Construct backwards by strong/ordinary induction on `k ≤ m`!
    suffices ∀ (k : ℕ) (hk : k ≤ m) (R : Finset β), inst.CanCoverPrefix k R →
        ∃ s : (j : Fin m) → j.1 < k → α,
          (∀ j (hj : j.1 < k), s j hj ∈ inst.cands j) ∧
          ∀ r ∈ R, ∃ j, ∃ (hj : j.1 < k), r ∈ inst.satisfies (s j hj) by
      obtain ⟨s, hs, hcov⟩ := this m le_rfl inst.reqs h
      exact ⟨fun j => s j j.isLt, fun j => hs j j.isLt, fun r hr =>
        let ⟨j, _, hjr⟩ := hcov r hr; ⟨j, hjr⟩⟩
    intro k
    induction k with
    | zero =>
      intro _ R hR
      rw [inst.canCoverPrefix_zero_iff] at hR
      subst hR
      exact ⟨fun j hj => (Nat.not_lt_zero j.1 hj).elim, fun j hj => (Nat.not_lt_zero j.1 hj).elim,
        fun r hr => (Finset.notMem_empty r hr).elim⟩
    | succ k ih =>
      intro hk R hR
      let idx : Fin m := ⟨k, hk⟩
      have hsome : (D (idx.1 + 1) R).isSome := (hD.isSome_iff idx R).mpr hR
      obtain ⟨c, hcD⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hc_mem, hpref⟩ := hD.some_spec idx R c hcD
      obtain ⟨s, hs, hcov⟩ := ih (Nat.le_of_succ_le hk) (R \ inst.satisfies c) hpref
      refine ⟨fun j hj => if h : j.1 < k then s j h else c, fun j hj => ?_, fun r hr => ?_⟩
      · dsimp only
        split_ifs with h
        · exact hs j h
        · have hji : j = idx := Fin.ext (show j.1 = k by omega)
          exact hji ▸ hc_mem
      · by_cases hrc : r ∈ inst.satisfies c
        · refine ⟨idx, Nat.lt_succ_self k, ?_⟩
          have hnot : ¬idx.1 < k := Nat.lt_irrefl k
          simpa [hnot] using hrc
        · obtain ⟨j, hj, hjr⟩ := hcov r (Finset.mem_sdiff.mpr ⟨hr, hrc⟩)
          refine ⟨j, Nat.lt_trans hj (Nat.lt_succ_self k), ?_⟩
          simpa [hj] using hjr

/-- Exact inner-loop operation count of the subset-DP algorithm: for any CSC instance with `|R|`
requirements and `|C| = ∑_i |C_i|` total candidates, the number of inner-loop pairs
`(c ∈ C_i, K ⊆ R, F ⊆ Ψ(c))` is at most `2 ^ (2 * |R|) * |C|`. -/
theorem AbstractCSC.alg_loop_count_le {m : ℕ} (inst : AbstractCSC α β m)
    (hsub : ∀ i : Fin m, ∀ c ∈ inst.cands i, inst.satisfies c ⊆ inst.reqs) :
    (∑ i : Fin m, ∑ c ∈ inst.cands i,
      inst.reqs.powerset.card * (inst.satisfies c).powerset.card) ≤
      2 ^ (2 * inst.reqs.card) * (∑ i : Fin m, (inst.cands i).card) := by
  have hterm : ∀ i : Fin m, ∀ c ∈ inst.cands i,
      inst.reqs.powerset.card * (inst.satisfies c).powerset.card ≤ 2 ^ (2 * inst.reqs.card) := by
    intro i c hc
    rw [Finset.card_powerset, Finset.card_powerset, two_mul, pow_add]
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (Finset.card_le_card (hsub i c hc)))
  calc (∑ i : Fin m, ∑ c ∈ inst.cands i,
          inst.reqs.powerset.card * (inst.satisfies c).powerset.card)
      ≤ ∑ i : Fin m, ∑ _c ∈ inst.cands i, 2 ^ (2 * inst.reqs.card) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c hc => hterm i c hc
    _ = ∑ i : Fin m, (inst.cands i).card * 2 ^ (2 * inst.reqs.card) := by
        simp [Finset.sum_const, smul_eq_mul]
    _ = 2 ^ (2 * inst.reqs.card) * ∑ i : Fin m, (inst.cands i).card := by
        rw [← Finset.sum_mul, mul_comm]

end AbstractCSC

/-! ### 2. Concrete Multi-Tape Turing-Machine FPT Complexity (`Cslib.Complexity.FPT`) -/

section ConcreteCSC

open Cslib.Complexity Turing.MultiTapeTM

/-- Concrete machine-encodable instance of **Constrained Set Cover**: a list of requirement
identifiers `reqs` and candidate groups `groups`, where each group `C_i` is a list of candidates
and each candidate is given by the list of requirements it satisfies. -/
@[ext]
structure CSCInstance where
  /-- Requirement universe `R`. -/
  reqs : List ℕ
  /-- Candidate sets `C_1, ..., C_m`, each candidate given by its list of satisfied requirements. -/
  groups : List (List (List ℕ))
  deriving DecidableEq, Repr, Inhabited

/-- Binary encoding of `CSCInstance`. -/
enc_structure encCSCInstance : CSCInstance where
  reqs : (encList encNat),
  groups : (encList (encList (encList encNat)))

attribute [fun_prop] encCSCInstance_reqs_polyTime encCSCInstance_groups_polyTime
  encCSCInstance_mk_polyTime

/-- The **Constrained Set Cover** decision problem: there exists a choice of one candidate
`s_i ∈ C_i` from each group whose union covers every requirement in `x.reqs`. -/
def ConstrainedSetCover : Set CSCInstance :=
  {x | ∃ chosen : List (List ℕ),
    List.Forall₂ (· ∈ ·) chosen x.groups ∧ ∀ r ∈ x.reqs, ∃ s ∈ chosen, r ∈ s}

/-- Characterization of `ConstrainedSetCover` membership. -/
theorem mem_ConstrainedSetCover_iff {x : CSCInstance} :
    x ∈ ConstrainedSetCover ↔
      ∃ chosen : List (List ℕ),
        List.Forall₂ (· ∈ ·) chosen x.groups ∧ ∀ r ∈ x.reqs, ∃ s ∈ chosen, r ∈ s := by
  rfl

/-- Distinct requirements of `x`, computed in polynomial time via `selectDistinct`. -/
def CSCInstance.distinctReqs (x : CSCInstance) : List ℕ :=
  selectDistinct x.reqs (List.replicate x.reqs.length true)

/-- Membership in `distinctReqs` coincides with membership in `reqs`. -/
theorem CSCInstance.mem_distinctReqs {x : CSCInstance} {r : ℕ} :
    r ∈ x.distinctReqs ↔ r ∈ x.reqs :=
  mem_selectDistinct_replicate

/-- `distinctReqs` has no duplicates. -/
theorem CSCInstance.nodup_distinctReqs (x : CSCInstance) : x.distinctReqs.Nodup :=
  nodup_selectDistinct _ _

/-- Parameter of a `CSCInstance`: the number of distinct requirements `|R|`. -/
def CSCInstance.numReqs (x : CSCInstance) : ℕ :=
  x.distinctReqs.length

/-- Length characterization of `CSCInstance.numReqs`. -/
theorem CSCInstance.numReqs_eq_length (x : CSCInstance) :
    x.numReqs = x.distinctReqs.length := by rfl

/-- The distinct requirement count equals `x.reqs.toFinset.card`. -/
theorem CSCInstance.numReqs_eq_card (x : CSCInstance) :
    x.numReqs = x.reqs.toFinset.card :=
  length_selectDistinct_replicate x.reqs

/-- Bitmask of a candidate `c : List ℕ` relative to a requirement list `rs : List ℕ`: bit `j` is
set iff `rs[j] ∈ c`. -/
def cscCandMask (rs c : List ℕ) : ℕ :=
  (List.range rs.length).foldl
    (fun acc j => if rs.getD j 0 ∈ c then acc + 2 ^ j else acc) 0

private lemma foldl_mask_lt (rs c : List ℕ) (m : ℕ) :
    (List.range m).foldl
      (fun acc i => if rs.getD i 0 ∈ c then acc + 2 ^ i else acc) 0 < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ihm =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs
    · have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ, mul_two]
      omega
    · exact ihm.trans (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m))

private lemma nat_add_eq_or_of_and_eq_zero (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  induction a using Nat.strong_induction_on generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp
    · have h0 : ¬(a % 2 = 1 ∧ b % 2 = 1) := by
        rintro ⟨ha1, hb1⟩
        have ht := congrArg (fun n => n.testBit 0) h
        simp [Nat.testBit_zero, ha1, hb1] at ht
      have hdiv : (a / 2) &&& (b / 2) = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        have ht := congrArg (fun n => n.testBit (i + 1)) h
        rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.zero_testBit] at ht
        rw [Nat.testBit_and, Nat.zero_testBit]
        exact ht
      have hrec := ih (a / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by decide)) (b / 2) hdiv
      have hsum : a + b = 2 * (a / 2 + b / 2) + (a % 2 + b % 2) := by omega
      have hor : a ||| b = 2 * (a / 2 ||| b / 2) + (a % 2 + b % 2) := by
        have hmod : (a ||| b) % 2 = a % 2 + b % 2 := by
          have ht := Nat.testBit_or a b 0
          simp only [Nat.testBit_zero] at ht
          rcases Nat.mod_two_eq_zero_or_one a with ha' | ha' <;>
            rcases Nat.mod_two_eq_zero_or_one b with hb' | hb' <;>
            rcases Nat.mod_two_eq_zero_or_one (a ||| b) with hab | hab <;>
            first | omega | simp [ha', hb', hab] at ht
        have hdv : (a ||| b) / 2 = a / 2 ||| b / 2 := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [← Nat.testBit_succ, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ,
            Nat.testBit_or]
        rw [← Nat.div_add_mod (a ||| b) 2, hdv, hmod]
      rw [hsum, hor, hrec]

private lemma foldl_mask_testBit (rs c : List ℕ) :
    ∀ (k : ℕ) (_hk : k ≤ rs.length) (j : ℕ),
      ((List.range k).foldl
        (fun acc i => if rs.getD i 0 ∈ c then acc + 2 ^ i else acc) 0).testBit j =
      (decide (j < k) && decide (rs.getD j 0 ∈ c)) := by
  intro k
  induction k with
  | zero => intro _ j; simp
  | succ k ih =>
    intro hk j
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := (List.range k).foldl
      (fun acc i => if rs.getD i 0 ∈ c then acc + 2 ^ i else acc) 0
    have hprev_lt : prev < 2 ^ k := foldl_mask_lt rs c k
    have hadd_bit : ∀ x < 2 ^ k, (x + 2 ^ k).testBit j = (x.testBit j || decide (j = k)) := by
      intro x hx
      have hdisj : x &&& 2 ^ k = 0 := by
        apply Nat.eq_of_testBit_eq; intro t
        rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
        by_cases htk : t = k
        · subst htk; simp [Nat.testBit_lt_two_pow hx]
        · simp [Ne.symm htk]
      rw [nat_add_eq_or_of_and_eq_zero _ _ hdisj, Nat.testBit_or, Nat.testBit_two_pow]
      simp [eq_comm]
    split_ifs with hmem
    · rw [hadd_bit prev hprev_lt, ih (Nat.le_of_succ_le hk) j]
      by_cases hjk : j = k
      · subst hjk; simp only [Nat.lt_succ_self, decide_true, Bool.or_true, Bool.true_and]
        exact (decide_eq_true hmem).symm
      · have : (j < k + 1) ↔ (j < k) := by omega
        simp [hjk, this]
    · rw [ih (Nat.le_of_succ_le hk) j]
      by_cases hjk : j = k
      · subst hjk; simp only [Nat.lt_succ_self, decide_true, Bool.true_and, Nat.lt_irrefl,
          decide_false, Bool.false_and]
        exact (decide_eq_false hmem).symm
      · have : (j < k + 1) ↔ (j < k) := by omega
        simp [this]

private lemma cscCandMask_testBit (rs c : List ℕ) (j : ℕ) :
    (cscCandMask rs c).testBit j = (decide (j < rs.length) && decide (rs.getD j 0 ∈ c)) :=
  foldl_mask_testBit rs c rs.length le_rfl j

private lemma cscCandMask_lt (rs c : List ℕ) : cscCandMask rs c < 2 ^ rs.length :=
  foldl_mask_lt rs c rs.length

private lemma testBit_sub_and (m cm j : ℕ) :
    (m - (m &&& cm)).testBit j = (m.testBit j && !cm.testBit j) := by
  have hle : m &&& cm ≤ m := Nat.and_le_left
  have hxor : m - (m &&& cm) = m ^^^ (m &&& cm) := by
    have h1 : (m ^^^ (m &&& cm)) + (m &&& cm) = m := by
      have hd : (m ^^^ (m &&& cm)) &&& (m &&& cm) = 0 := by
        apply Nat.eq_of_testBit_eq; intro t
        simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
        cases m.testBit t <;> cases cm.testBit t <;> rfl
      rw [nat_add_eq_or_of_and_eq_zero _ _ hd]
      apply Nat.eq_of_testBit_eq; intro t
      simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and]
      cases m.testBit t <;> cases cm.testBit t <;> rfl
    omega
  rw [hxor, Nat.testBit_xor, Nat.testBit_and]
  cases m.testBit j <;> cases cm.testBit j <;> rfl

/-- One DP row update for `CSC`: given the previous row `row : List Bool` of length `N` and
candidate group `C_i` (with requirement list `rs`), compute the new row of length `N`. -/
def cscStepRow (rs : List ℕ) (N : ℕ) (row : List Bool) (grp : List (List ℕ)) : List Bool :=
  (List.range N).map fun m =>
    grp.any fun c => row.getD (m - (m &&& cscCandMask rs c)) false

/-- Full DP over `groups`, returning the final Boolean row of length `N`. -/
def cscDPRow (rs : List ℕ) (N : ℕ) (groups : List (List (List ℕ))) : List Bool :=
  groups.foldl (cscStepRow rs N) ((List.range N).map fun m => m == 0)

/-- The padded CSC decider: given `(x, N)` with `N = 2 ^ |distinctReqs|`, run the DP and test
entry `N - 1`. -/
def cscPadBool (x : CSCInstance) (N : ℕ) : Bool :=
  (cscDPRow x.distinctReqs N x.groups).getD (N - 1) false

/-- Padded CSC decider accepting any unary table size `N ≥ 2 ^ x.numReqs`. -/
def cscBoolOfPad (x : CSCInstance) (N : ℕ) : Bool :=
  (cscDPRow x.distinctReqs N x.groups).getD (2 ^ x.numReqs - 1) false

/-- Executable CSC decision procedure. -/
def cscBool (x : CSCInstance) : Bool :=
  cscPadBool x (2 ^ x.numReqs)

private lemma length_cscDPRow (rs : List ℕ) (N : ℕ) (groups : List (List (List ℕ))) :
    (cscDPRow rs N groups).length = N := by
  unfold cscDPRow
  suffices ∀ (gs : List (List (List ℕ))) (init : List Bool),
      init.length = N → (gs.foldl (cscStepRow rs N) init).length = N from
    this groups _ (by simp)
  intro gs
  induction gs with
  | nil => intro init h; exact h
  | cons g gs ih => intro init _; exact ih _ (by simp [cscStepRow])

private lemma cscDPRow_getD_iff_of_le (rs : List ℕ) (groups : List (List (List ℕ))) (N m : ℕ)
    (hN : 2 ^ rs.length ≤ N) (hm : m < 2 ^ rs.length) :
    (cscDPRow rs N groups).getD m false = true ↔
      ∃ chosen : List (List ℕ), List.Forall₂ (· ∈ ·) chosen groups ∧
        ∀ j < rs.length, m.testBit j = true → ∃ s ∈ chosen, rs.getD j 0 ∈ s := by
  unfold cscDPRow
  induction groups using List.reverseRecOn generalizing m with
  | nil =>
    have hmN : m < N := lt_of_lt_of_le hm hN
    simp only [List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hmN, Option.map_some, Option.getD_some, beq_iff_eq,
      List.forall₂_nil_right_iff]
    constructor
    · rintro rfl
      refine ⟨[], rfl, fun j _ hbit => ?_⟩
      simp at hbit
    · rintro ⟨_, rfl, hcov⟩
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.zero_testBit]
      by_cases hbit : m.testBit j = true
      · have hj : j < rs.length := by
          by_contra hge
          have hltj : m < 2 ^ j :=
            hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
          exact absurd hbit (by simp [Nat.testBit_lt_two_pow hltj])
        obtain ⟨_, hs, _⟩ := hcov j hj hbit
        simp at hs
      · simpa using hbit
  | append_singleton gs g ih =>
    have hmN : m < N := lt_of_lt_of_le hm hN
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := gs.foldl (cscStepRow rs N) ((List.range N).map fun m => m == 0)
    simp only [cscStepRow, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hmN, Option.map_some, Option.getD_some, List.any_eq_true]
    constructor
    · rintro ⟨c, hc, hprev⟩
      have hsub_lt : m - (m &&& cscCandMask rs c) < 2 ^ rs.length :=
        lt_of_le_of_lt (Nat.sub_le m _) hm
      rw [← List.getD_eq_getElem?_getD] at hprev
      obtain ⟨chosen, hfor, hcov⟩ := (ih _ hsub_lt).mp hprev
      have hfor_app : List.Forall₂ (· ∈ ·) (chosen ++ [c]) (gs ++ [g]) := by
        clear hcov ih hprev
        induction hfor with
        | nil => exact .cons hc .nil
        | cons ha _ ih' => exact .cons ha ih'
      refine ⟨chosen ++ [c], hfor_app, fun j hj hbit => ?_⟩
      by_cases hmem : rs.getD j 0 ∈ c
      · exact ⟨c, by simp, hmem⟩
      · have hbit' : (m - (m &&& cscCandMask rs c)).testBit j = true := by
          rw [testBit_sub_and, cscCandMask_testBit, hbit, decide_eq_true hj,
            decide_eq_false hmem]
          rfl
        obtain ⟨s, hs, hjs⟩ := hcov j hj hbit'
        exact ⟨s, List.mem_append_left _ hs, hjs⟩
    · rintro ⟨chosen, hfor, hcov⟩
      have hfor' : List.Forall₂ (· ∈ ·) (chosen.take gs.length) gs :=
        List.forall₂_take_append chosen gs [g] hfor
      have htail : List.Forall₂ (· ∈ ·) (chosen.drop gs.length) [g] :=
        List.forall₂_drop_append chosen gs [g] hfor
      have hch_eq : chosen = chosen.take gs.length ++ chosen.drop gs.length :=
        (List.take_append_drop gs.length chosen).symm
      generalize hdrop_eq : chosen.drop gs.length = tail at htail hch_eq
      cases htail with
      | cons hc hnil =>
        cases hnil
        rename_i c
        refine ⟨c, hc, ?_⟩
        have hsub_lt : m - (m &&& cscCandMask rs c) < 2 ^ rs.length :=
          lt_of_le_of_lt (Nat.sub_le m _) hm
        rw [← List.getD_eq_getElem?_getD]
        refine (ih _ hsub_lt).mpr ⟨chosen.take gs.length, hfor', fun j hj hbit' => ?_⟩
        rw [testBit_sub_and, cscCandMask_testBit] at hbit'
        have hbit : m.testBit j = true := by
          simpa using (Bool.and_eq_true _ _).mp hbit' |>.1
        have hnotmem : rs.getD j 0 ∉ c := by
          have h2 := (Bool.and_eq_true _ _).mp hbit' |>.2
          simp [hj] at h2
          rwa [List.getD_eq_getElem _ _ hj]
        obtain ⟨s, hs, hjs⟩ := hcov j hj hbit
        rw [hch_eq, List.mem_append] at hs
        rcases hs with hs' | hsc
        · exact ⟨s, hs', hjs⟩
        · simp only [List.mem_singleton] at hsc
          exact absurd (hsc ▸ hjs) hnotmem

/-- Correctness of `cscBoolOfPad` whenever `2 ^ x.numReqs ≤ N`. -/
theorem cscBoolOfPad_eq_true_iff (x : CSCInstance) {N : ℕ} (hN : 2 ^ x.numReqs ≤ N) :
    cscBoolOfPad x N = true ↔ x ∈ ConstrainedSetCover := by
  unfold cscBoolOfPad
  have hlt : 2 ^ x.numReqs - 1 < 2 ^ x.numReqs := Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
  have hlen : x.distinctReqs.length = x.numReqs := rfl
  rw [← hlen] at hN hlt ⊢
  rw [cscDPRow_getD_iff_of_le x.distinctReqs x.groups N _ hN hlt]
  refine exists_congr fun chosen => and_congr_right fun _ => ?_
  constructor
  · intro h r hr
    have hr' : r ∈ x.distinctReqs := x.mem_distinctReqs.mpr hr
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hr'
    have hbit : (2 ^ x.distinctReqs.length - 1).testBit j = true := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj
    have hgetD : x.distinctReqs.getD j 0 = r := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hget]
    have h' := h j hj hbit
    rwa [hgetD] at h'
  · intro h j hj _
    have hmem : x.distinctReqs.getD j 0 ∈ x.reqs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact x.mem_distinctReqs.mp (List.getElem_mem hj)
    exact h _ hmem

/-- Correctness of `cscBool`: `cscBool x = true ↔ x ∈ ConstrainedSetCover`. -/
theorem cscBool_eq_true_iff (x : CSCInstance) :
    cscBool x = true ↔ x ∈ ConstrainedSetCover := by
  simpa [cscBool, cscPadBool, cscBoolOfPad] using cscBoolOfPad_eq_true_iff x le_rfl

private lemma computableInPolyTime_distinctReqs :
    ComputableInPolyTime CSCInstance.distinctReqs encCSCInstance (encList encNat) := by
  unfold CSCInstance.distinctReqs
  fun_prop

private lemma computableInPolyTime_numReqs :
    ComputableInPolyTime CSCInstance.numReqs encCSCInstance encUnary := by
  unfold CSCInstance.numReqs
  have h := computableInPolyTime_distinctReqs
  fun_prop

private lemma computableInPolyTime_cscCandMask :
    ComputableInPolyTime (fun p : List ℕ × List ℕ => cscCandMask p.1 p.2)
      (encPair (encList encNat) (encList encNat)) encNat := by
  unfold cscCandMask
  have hstep : ComputableInPolyTime
      (fun q : ((List ℕ × List ℕ) × ℕ) × ℕ =>
        if q.1.1.1.getD q.2 0 ∈ q.1.1.2 then q.1.2 + 2 ^ q.2 else q.1.2)
      (encPair (encPair (encPair (encList encNat) (encList encNat)) encNat) encUnary) encNat := by
    have hmem : ComputableInPolyTime
        (fun q : ((List ℕ × List ℕ) × ℕ) × ℕ => decide (q.1.1.1.getD q.2 0 ∈ q.1.1.2))
        (encPair (encPair (encPair (encList encNat) (encList encNat)) encNat) encUnary)
        encBool := by
      refine ComputableInPolyTime.decide_mem (by fun_prop) ?_
      exact ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) 0
    have hadd : ComputableInPolyTime
        (fun q : ((List ℕ × List ℕ) × ℕ) × ℕ => q.1.2 + 2 ^ q.2)
        (encPair (encPair (encPair (encList encNat) (encList encNat)) encNat) encUnary) encNat :=
      ComputableInPolyTime.binary_add' (by fun_prop)
        (ComputableInPolyTime.binary_two_pow.comp (by fun_prop))
    simpa only [decide_eq_true_eq] using hmem.ite' hadd (by fun_prop)
  refine ComputableInPolyTime.foldlWith (encA := encUnary) (encL := encList encUnary)
    (encB := encNat) (encP := encPair (encList encNat) (encList encNat))
    (par := id) (list := fun p => List.range p.1.length) (init := fun _ => 0)
    (step := fun p acc j => if p.1.getD j 0 ∈ p.2 then acc + 2 ^ j else acc)
    ComputableInPolyTime.id' (by fun_prop) (ComputableInPolyTime.const 0) hstep
    (B := fun p => (encPair (encList encNat) (encList encNat) p).length)
    PolyBounded.self ?_
  intro p i hi
  simp only [List.length_range] at hi
  rw [List.take_range]
  have hlt : ((List.range (min i p.1.length)).foldl
      (fun acc j => if p.1.getD j 0 ∈ p.2 then acc + 2 ^ j else acc) 0) < 2 ^ p.1.length := by
    exact (foldl_mask_lt p.1 p.2 (min i p.1.length)).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))
  simp only [encNat_apply, id_eq]
  rw [Nat.size_eq_bits_len]
  have hsize : (((List.range (min i p.1.length)).foldl
      (fun acc j => if p.1.getD j 0 ∈ p.2 then acc + 2 ^ j else acc) 0)).size ≤ p.1.length :=
    Nat.size_le.mpr hlt
  have hlen1 : p.1.length ≤ (encList encNat p.1).length := length_le_length_encList encNat p.1
  have hlen2 : (encList encNat p.1).length ≤
      (encPair (encList encNat) (encList encNat) p).length := by
    rw [length_encPair]; omega
  omega

private lemma computableInPolyTime_cscStepRow :
    ComputableInPolyTime
      (fun q : ((List ℕ × ℕ) × List Bool) × List (List ℕ) =>
        cscStepRow q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair (encList encNat) encUnary) (encList encBool))
        (encList (encList encNat)))
      (encList encBool) := by
  unfold cscStepRow
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  refine ComputableInPolyTime.anyWithInput (by fun_prop) ?_
  refine ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encList encBool) false
    (by fun_prop) ?_
  have hm_bin : ComputableInPolyTime
      (fun r : ((((List ℕ × ℕ) × List Bool) × List (List ℕ)) × ℕ) × List ℕ => r.1.2)
      (encPair (encPair (encPair (encPair (encPair (encList encNat) encUnary) (encList encBool))
        (encList (encList encNat))) encUnary) (encList encNat)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hmask : ComputableInPolyTime
      (fun r : ((((List ℕ × ℕ) × List Bool) × List (List ℕ)) × ℕ) × List ℕ =>
        cscCandMask r.1.1.1.1.1 r.2)
      (encPair (encPair (encPair (encPair (encPair (encList encNat) encUnary) (encList encBool))
        (encList (encList encNat))) encUnary) (encList encNat)) encNat :=
    computableInPolyTime_cscCandMask.comp
      (((((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).comp
        (ComputableInPolyTime.fst _ _)).comp (ComputableInPolyTime.fst _ _)).comp
        (ComputableInPolyTime.fst _ _) |>.prod (ComputableInPolyTime.snd _ _))
  exact ComputableInPolyTime.binary_sub' hm_bin
    (ComputableInPolyTime.binary_and' hm_bin hmask)

private lemma computableInPolyTime_cscInitRow :
    ComputableInPolyTime
      (fun p : CSCInstance × ℕ => (List.range p.2).map fun m => m == 0)
      (encPair encCSCInstance encUnary) (encList encBool) := by
  refine ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.snd _ _)) ?_
  exact ComputableInPolyTime.unary_beq (ComputableInPolyTime.snd _ _)
    (ComputableInPolyTime.const 0)

private lemma cscDPRow_prefix_bound (p : CSCInstance × ℕ) (i : ℕ) (_hi : i ≤ p.1.groups.length) :
    (encList encBool
      (((p.1.groups.take i).foldl (cscStepRow p.1.distinctReqs p.2)
        ((List.range p.2).map fun m => m == 0)))).length ≤
      (encPair encCSCInstance encUnary p).length * 3 := by
  have hrow_len : (((p.1.groups.take i).foldl (cscStepRow p.1.distinctReqs p.2)
      ((List.range p.2).map fun m => m == 0))).length = p.2 := by
    have : ∀ (gs : List (List (List ℕ))) (init : List Bool),
        init.length = p.2 → (gs.foldl (cscStepRow p.1.distinctReqs p.2) init).length = p.2 := by
      intro gs
      induction gs with
      | nil => intro init h; exact h
      | cons g gs ih => intro init _; exact ih _ (by simp [cscStepRow])
    exact this _ _ (by simp)
  have henc_le := length_encList_le encBool
    (((p.1.groups.take i).foldl (cscStepRow p.1.distinctReqs p.2)
      ((List.range p.2).map fun m => m == 0))) (b := 1) (fun b _ => by simp [encBool_apply])
  have hp2_le : p.2 ≤ (encPair encCSCInstance encUnary p).length := by
    rw [length_encPair, encUnary_apply, List.length_replicate]; omega
  rw [hrow_len] at henc_le
  exact henc_le.trans (Nat.mul_le_mul_right 3 hp2_le)

private lemma computableInPolyTime_cscDPRow :
    ComputableInPolyTime (fun p : CSCInstance × ℕ => cscDPRow p.1.distinctReqs p.2 p.1.groups)
      (encPair encCSCInstance encUnary) (encList encBool) := by
  unfold cscDPRow
  have hpar : ComputableInPolyTime (fun p : CSCInstance × ℕ => (p.1.distinctReqs, p.2))
      (encPair encCSCInstance encUnary) (encPair (encList encNat) encUnary) :=
    (computableInPolyTime_distinctReqs.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _)
  have hgroups : ComputableInPolyTime (fun p : CSCInstance × ℕ => p.1.groups)
      (encPair encCSCInstance encUnary) (encList (encList (encList encNat))) :=
    encCSCInstance_groups_polyTime (ComputableInPolyTime.fst _ _)
  have hB : PolyBounded (fun p : CSCInstance × ℕ => (encPair encCSCInstance encUnary p).length)
      (fun p => (encPair encCSCInstance encUnary p).length * 3) :=
    PolyBounded.self.mul (.const 3)
  exact @ComputableInPolyTime.foldlWith (CSCInstance × ℕ) (List (List ℕ)) (List Bool) (List ℕ × ℕ)
    (encPair encCSCInstance encUnary) (encList (encList encNat)) (encList encBool)
    (encList (encList (encList encNat))) (encPair (encList encNat) encUnary)
    inferInstance inferInstance
    (fun p => (p.1.distinctReqs, p.2)) (fun p => p.1.groups)
    (fun p => (List.range p.2).map fun m => m == 0)
    (fun par => cscStepRow par.1 par.2)
    hpar hgroups computableInPolyTime_cscInitRow computableInPolyTime_cscStepRow
    (fun p => (encPair encCSCInstance encUnary p).length * 3)
    hB cscDPRow_prefix_bound

private lemma computableInPolyTime_cscPadBool :
    ComputableInPolyTime (fun p : CSCInstance × ℕ => cscPadBool p.1 p.2)
      (encPair encCSCInstance encUnary) encBool := by
  unfold cscPadBool
  exact ComputableInPolyTime.listGetDWithInput computableInPolyTime_cscDPRow
    (ComputableInPolyTime.unary_sub.comp
      ((ComputableInPolyTime.snd _ _).prod (ComputableInPolyTime.const 1)))
    false

/-- `cscBoolOfPad` is computable in polynomial time (in the instance and unary table size `N`). -/
@[fun_prop]
theorem computableInPolyTime_cscBoolOfPad :
    ComputableInPolyTime (fun p : CSCInstance × ℕ => cscBoolOfPad p.1 p.2)
      (encPair encCSCInstance encUnary) encBool := by
  unfold cscBoolOfPad
  have hidx : ComputableInPolyTime (fun p : CSCInstance × ℕ => 2 ^ p.1.numReqs - 1)
      (encPair encCSCInstance encUnary) encNat :=
    ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_two_pow.comp (computableInPolyTime_numReqs.comp (by fun_prop)))
      (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.listGetD_binary false computableInPolyTime_cscDPRow hidx

/-- **Constrained Set Cover is decidable in time `2 ^ (O(|R|)) * poly(|x|)`** on multi-tape Turing
machines. -/
theorem ConstrainedSetCover_decidableInExpTime :
    ∃ δ : ℝ, DecidableInExpTime ConstrainedSetCover encCSCInstance CSCInstance.numReqs δ :=
  DecidableInExpTime.of_computableInPolyTime_pad computableInPolyTime_cscPadBool
    computableInPolyTime_numReqs (fun _ => le_rfl) (fun x => (cscBool_eq_true_iff x).symm)

/-- **Constrained Set Cover is fixed-parameter tractable** in the number of distinct requirements
`|R|` (`Cslib.Complexity.FPT`). -/
theorem ConstrainedSetCover_mem_FPT :
    ConstrainedSetCover ∈ FPT encCSCInstance CSCInstance.numReqs :=
  ConstrainedSetCover_decidableInExpTime.elim fun _ => DecidableInExpTime.mem_FPT

end ConcreteCSC

end CslibFrontier.Complexity
