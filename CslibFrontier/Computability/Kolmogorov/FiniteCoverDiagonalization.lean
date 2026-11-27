/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Image

/-!
# Impossibility of Uniform Finite Clocked Program Covers by Diagonalization

Given any deterministic clocked program evaluator `evalStep : ℕ → ℕ → ℕ → Option ℕ` (where
`evalStep p n t` returns `some k` if program `p` on input `n` produces output `k` within `t` steps,
monotonically in `t`) and a step budget `T : ℕ → ℕ`, fewer than `n + 1` distinct outputs can be
produced on input `n` within `T n` steps by programs of index strictly below `Nat.log 2 (n + 1)`.
Selecting the least omitted output in `{0, …, n}` defines a function `finiteCoverDiag evalStep T`
bounded pointwise by `n` (and primitive recursive whenever `evalStep` and `T` are primitive
recursive) that cannot be covered across all inputs `n` by any finite family `{0, …, Z - 1}` of
programs each obeying a uniform per-program additive linear-logarithmic time bound
`Nat.clog 2 ((n + 1) * (k + 1)) + c`.

## Main definitions

* `CslibFrontier.Computability.Kolmogorov.finiteCoverOutputs`: finite set of outputs produced on
  input `n` within `T n` steps by programs `p < Nat.log 2 (n + 1)`.
* `CslibFrontier.Computability.Kolmogorov.finiteCoverDiag`: least `k ≤ n` avoided by
  `finiteCoverOutputs`.
* `CslibFrontier.Computability.Kolmogorov.HasFiniteLinearLogCover`: existence of a finite bound `Z`
  covering a target function `f : ℕ → ℕ` with per-program constant additive overhead above
  `Nat.clog 2 ((n + 1) * (k + 1))`.

## Main results

* `CslibFrontier.Computability.Kolmogorov.finiteCoverDiag_le`: `finiteCoverDiag evalStep T n ≤ n`.
* `CslibFrontier.Computability.Kolmogorov.finiteCoverDiag_notMem`: no program `p < Nat.log 2 (n+1)`
  outputs `finiteCoverDiag evalStep T n` within `T n` steps on input `n`.
* `CslibFrontier.Computability.Kolmogorov.not_hasFiniteLinearLogCover_diag`: no monotone clocked
  evaluator admits a finite linear-logarithmic cover for its own `3 · Nat.clog 2 (n + 1)` diagonal
  function.
* `CslibFrontier.Computability.Kolmogorov.not_hasFiniteLinearLogCover_partrecCode`: specialization
  to `Nat.Partrec.Code.evaln`.
-/

public section

namespace CslibFrontier.Computability.Kolmogorov

/-- Finite set of outputs produced on input `n` within `T n` steps by programs of index strictly
below `Nat.log 2 (n + 1)`. -/
def finiteCoverOutputs (evalStep : ℕ → ℕ → ℕ → Option ℕ) (T : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (n + 1))).biUnion fun p ↦
    match evalStep p n (T n) with
    | some k => {k}
    | none => ∅

/-- Membership characterization for `finiteCoverOutputs`. -/
@[simp]
theorem mem_finiteCoverOutputs_iff {evalStep : ℕ → ℕ → ℕ → Option ℕ} {T : ℕ → ℕ} {n k : ℕ} :
    k ∈ finiteCoverOutputs evalStep T n ↔
      ∃ p < Nat.log 2 (n + 1), evalStep p n (T n) = some k := by
  simp only [finiteCoverOutputs, Finset.mem_biUnion, Finset.mem_range]
  refine ⟨fun ⟨p, hp, hk⟩ ↦ ⟨p, hp, ?_⟩, fun ⟨p, hp, hk⟩ ↦ ⟨p, hp, ?_⟩⟩
  · cases h : evalStep p n (T n) with
    | none => simp [h] at hk
    | some v =>
        simp only [h, Finset.mem_singleton] at hk
        rw [hk]
  · simp [hk]

/-- The cardinality of `finiteCoverOutputs evalStep T n` is at most `Nat.log 2 (n + 1)`. -/
theorem card_finiteCoverOutputs_le (evalStep : ℕ → ℕ → ℕ → Option ℕ) (T : ℕ → ℕ) (n : ℕ) :
    (finiteCoverOutputs evalStep T n).card ≤ Nat.log 2 (n + 1) := by
  classical
  let f : ℕ → Finset ℕ := fun p ↦
    match evalStep p n (T n) with
    | some k => {k}
    | none => ∅
  calc
    (finiteCoverOutputs evalStep T n).card
        ≤ ∑ p ∈ Finset.range (Nat.log 2 (n + 1)), (f p).card := Finset.card_biUnion_le
    _ ≤ (Finset.range (Nat.log 2 (n + 1))).card • 1 :=
        Finset.sum_le_card_nsmul _ _ 1 fun p _ ↦ by
          dsimp only [f]
          cases evalStep p n (T n) <;> simp
    _ = Nat.log 2 (n + 1) := by simp

/-- For every `n : ℕ`, `Nat.log 2 (n + 1) < n + 1`. -/
theorem log2_succ_lt_succ (n : ℕ) : Nat.log 2 (n + 1) < n + 1 := by
  have hpow : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  exact (Nat.lt_pow_self (by decide : 1 < 2)).trans_le hpow

/-- For every `n : ℕ`, there exists `k ≤ n` not belonging to `finiteCoverOutputs evalStep T n`. -/
theorem exists_le_notMem_finiteCoverOutputs (evalStep : ℕ → ℕ → ℕ → Option ℕ) (T : ℕ → ℕ)
    (n : ℕ) : ∃ k ≤ n, k ∉ finiteCoverOutputs evalStep T n := by
  by_contra! hall
  have hsub : Finset.range (n + 1) ⊆ finiteCoverOutputs evalStep T n := by
    intro k hk
    exact hall k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hcard : n + 1 ≤ (finiteCoverOutputs evalStep T n).card := by
    simpa using Finset.card_le_card hsub
  exact absurd (hcard.trans (card_finiteCoverOutputs_le evalStep T n))
    (not_le.mpr (log2_succ_lt_succ n))

/-- The **finite-cover diagonal function**: the least `k ≤ n` not produced on input `n` within
`T n` steps by any program `p < Nat.log 2 (n + 1)`. -/
def finiteCoverDiag (evalStep : ℕ → ℕ → ℕ → Option ℕ) (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.find (exists_le_notMem_finiteCoverOutputs evalStep T n)

/-- Pointwise bound `finiteCoverDiag evalStep T n ≤ n`. -/
theorem finiteCoverDiag_le (evalStep : ℕ → ℕ → ℕ → Option ℕ) (T : ℕ → ℕ) (n : ℕ) :
    finiteCoverDiag evalStep T n ≤ n :=
  (Nat.find_spec (exists_le_notMem_finiteCoverOutputs evalStep T n)).1

/-- Diagonal avoidance: `finiteCoverDiag evalStep T n` is not in `finiteCoverOutputs`. -/
theorem finiteCoverDiag_notMem (evalStep : ℕ → ℕ → ℕ → Option ℕ) (T : ℕ → ℕ) (n : ℕ) :
    finiteCoverDiag evalStep T n ∉ finiteCoverOutputs evalStep T n :=
  (Nat.find_spec (exists_le_notMem_finiteCoverOutputs evalStep T n)).2

/-- Minimality of `finiteCoverDiag`: every `j < finiteCoverDiag evalStep T n` belongs to
`finiteCoverOutputs evalStep T n`. -/
theorem mem_finiteCoverOutputs_of_lt_diag {evalStep : ℕ → ℕ → ℕ → Option ℕ} {T : ℕ → ℕ}
    {n j : ℕ} (hj : j < finiteCoverDiag evalStep T n) :
    j ∈ finiteCoverOutputs evalStep T n := by
  have hle : j ≤ n := hj.le.trans (finiteCoverDiag_le evalStep T n)
  by_contra hnot
  exact Nat.find_min (exists_le_notMem_finiteCoverOutputs evalStep T n) hj ⟨hle, hnot⟩

/-- A function `f : ℕ → ℕ` admits a **finite linear-logarithmic program cover** under `evalStep`
if there is a bound `Z : ℕ` such that for every input `n : ℕ`, some program `p < Z` with uniform
constant `c : ℕ` computes `f n` and halts at step `Nat.clog 2 ((n + 1) * (f n' + 1)) + c` whenever
it outputs `f n'`. -/
def HasFiniteLinearLogCover (evalStep : ℕ → ℕ → ℕ → Option ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ Z : ℕ, ∀ n : ℕ, ∃ p < Z, ∃ c : ℕ,
    (∃ t : ℕ, evalStep p n t = some (f n)) ∧
      ∀ n' : ℕ, (∃ t : ℕ, evalStep p n' t = some (f n')) →
        evalStep p n' (Nat.clog 2 ((n' + 1) * (f n' + 1)) + c) = some (f n') ∧
          ∀ t < Nat.clog 2 ((n' + 1) * (f n' + 1)) + c, evalStep p n' t = none

/-- **Uniform Finite-Cover Diagonalization Theorem**: for any time-monotone evaluator `evalStep`,
the diagonal function at budget `T n = 3 * Nat.clog 2 (n + 1)` admits no finite linear-logarithmic
program cover. -/
theorem not_hasFiniteLinearLogCover_diag (evalStep : ℕ → ℕ → ℕ → Option ℕ)
    (hmono : ∀ {p n t₁ t₂ k}, t₁ ≤ t₂ → evalStep p n t₁ = some k → evalStep p n t₂ = some k) :
    ¬HasFiniteLinearLogCover evalStep (finiteCoverDiag evalStep fun n ↦ 3 * Nat.clog 2 (n +
      1)) := by
  set T : ℕ → ℕ := fun n ↦ 3 * Nat.clog 2 (n + 1)
  set f : ℕ → ℕ := finiteCoverDiag evalStep T
  rintro ⟨Z, hcover⟩
  -- For each program `p < Z`, extract a uniform constant `cFun p` independent of `n`.
  let ValidConst (p c : ℕ) : Prop :=
    ∃ n₀ : ℕ, (∃ t : ℕ, evalStep p n₀ t = some (f n₀)) ∧
      ∀ n' : ℕ, (∃ t : ℕ, evalStep p n' t = some (f n')) →
        evalStep p n' (Nat.clog 2 ((n' + 1) * (f n' + 1)) + c) = some (f n') ∧
          ∀ t < Nat.clog 2 ((n' + 1) * (f n' + 1)) + c, evalStep p n' t = none
  have huniq : ∀ p c₁ c₂ : ℕ, ValidConst p c₁ → ValidConst p c₂ → c₁ = c₂ := by
    rintro p c₁ c₂ ⟨n₀, hrun₀, hall₁⟩ ⟨_, _, hall₂⟩
    rcases hall₁ n₀ hrun₀ with ⟨hs₁, hlt₁⟩
    rcases hall₂ n₀ hrun₀ with ⟨hs₂, hlt₂⟩
    rcases lt_trichotomy c₁ c₂ with hlt | rfl | hgt
    · have hnone := hlt₂ _ (Nat.add_lt_add_left hlt _)
      rw [hs₁] at hnone
      cases hnone
    · rfl
    · have hnone := hlt₁ _ (Nat.add_lt_add_left hgt _)
      rw [hs₂] at hnone
      cases hnone
  let cFun (p : ℕ) : ℕ :=
    @dite ℕ (∃ c : ℕ, ValidConst p c) (Classical.propDecidable _)
      (fun h ↦ Classical.choose h) (fun _ ↦ 0)
  let Cmax : ℕ := (Finset.range Z).sup cFun
  set m : ℕ := max Z Cmax + 1
  set n : ℕ := 2 ^ m - 1
  have hpow_pos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hn_succ : n + 1 = 2 ^ m := Nat.sub_add_cancel hpow_pos
  have hlog : Nat.log 2 (n + 1) = m := by
    rw [hn_succ, Nat.log_pow (by decide : 1 < 2)]
  have hclog_n : Nat.clog 2 (n + 1) = m := by
    rw [hn_succ, Nat.clog_pow _ _ (by decide : 1 < 2)]
  rcases hcover n with ⟨p, hpZ, c, hrun_n, hall_p⟩
  have hvc : ValidConst p c := ⟨n, hrun_n, hall_p⟩
  have hc_eq : c = cFun p := by
    have hex : ∃ c' : ℕ, ValidConst p c' := ⟨c, hvc⟩
    have hspec : ValidConst p (cFun p) := by
      dsimp only [cFun]
      simp only [hex, ↓reduceDIte]
      exact Classical.choose_spec hex
    exact huniq p c (cFun p) hvc hspec
  have hc_le : c ≤ Cmax := by
    rw [hc_eq]
    exact Finset.le_sup (f := cFun) (Finset.mem_range.mpr hpZ)
  have hfn_le : f n + 1 ≤ 2 ^ m := by
    have hle : f n ≤ n := finiteCoverDiag_le evalStep T n
    omega
  have hprod_le : (n + 1) * (f n + 1) ≤ 2 ^ (2 * m) := by
    have hm_two : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← Nat.pow_add, two_mul]
    rw [hn_succ, ← hm_two]
    exact Nat.mul_le_mul_left (2 ^ m) hfn_le
  have hclog_prod : Nat.clog 2 ((n + 1) * (f n + 1)) ≤ 2 * m := by
    rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
    exact hprod_le
  have htime_le : Nat.clog 2 ((n + 1) * (f n + 1)) + c ≤ T n := by
    dsimp only [T]
    rw [hclog_n]
    have hcm : c ≤ m := hc_le.trans ((le_max_right Z Cmax).trans (Nat.le_succ _))
    omega
  have heval_c : evalStep p n (Nat.clog 2 ((n + 1) * (f n + 1)) + c) = some (f n) :=
    (hall_p n hrun_n).1
  have heval_T : evalStep p n (T n) = some (f n) := hmono htime_le heval_c
  have hp_lt_log : p < Nat.log 2 (n + 1) := by
    rw [hlog]
    exact hpZ.trans_le ((le_max_left Z Cmax).trans (Nat.le_succ _))
  have hmem : f n ∈ finiteCoverOutputs evalStep T n :=
    mem_finiteCoverOutputs_iff.mpr ⟨p, hp_lt_log, heval_T⟩
  exact finiteCoverDiag_notMem evalStep T n hmem

/-- Clocked evaluator associated to `Nat.Partrec.Code.evaln` via `Denumerable.ofNat`. -/
def partrecCodeEvalStep (p n t : ℕ) : Option ℕ :=
  Nat.Partrec.Code.evaln t (Denumerable.ofNat Nat.Partrec.Code p) n

/-- Specialization of `not_hasFiniteLinearLogCover_diag` to `Nat.Partrec.Code.evaln`. -/
theorem not_hasFiniteLinearLogCover_partrecCode :
    ¬HasFiniteLinearLogCover partrecCodeEvalStep
      (finiteCoverDiag partrecCodeEvalStep fun n ↦ 3 * Nat.clog 2 (n + 1)) := by
  refine not_hasFiniteLinearLogCover_diag partrecCodeEvalStep fun {p n t₁ t₂ k} hle hk ↦ ?_
  exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hle (Option.mem_def.mpr hk))

end CslibFrontier.Computability.Kolmogorov
