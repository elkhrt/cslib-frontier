/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.EUThreeSAT
public import CslibFrontier.Logics.Propositional.CNF.ExactDistinct
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Exact $k$-SAT with Distinct Clause Variables

This module formalizes the exact $k$-satisfiability problem `ExactKSAT k` over binary-encoded CNF
formulas (`Cslib.Complexity.encCNF`), in which every clause consists of exactly `k` literals on
pairwise distinct variables (`Cslib.Logic.PL.CNF.IsExactDistinct k`), and proves its
`NP`-membership for all `k : ℕ` and its `NP`-completeness for all `k ≥ 3` under standard Lean
axioms.

For `k = 3`, `ExactKSAT 3` coincides with `Cslib.Complexity.EUThreeSAT`. For `k = 3 + d`, the
reduction `toExactKSAT k` shifts all input variable indices upward by `d` and expands every
3-literal clause `c` into the `2 ^ d` clauses `c' ∨ (ℓ₀ ∨ ⋯ ∨ ℓ_{d-1})` ranging over all sign
combinations on the `d` fresh padding variables `0, …, d - 1`, preserving exact distinctness and
satisfiability in polynomial time.

## Main definitions

- `CslibFrontier.Complexity.ExactKSAT`: satisfiable CNF formulas in which every clause has `k`
  literals on pairwise distinct variables.
- `CslibFrontier.Complexity.exactKSATSyntaxCheck`: polynomial-time Boolean syntax test for
  `CNF.IsExactDistinct k`.
- `CslibFrontier.Complexity.padSignCombos`: all `2 ^ d` literal lists on variables `0, …, d - 1`.
- `CslibFrontier.Complexity.toExactKSAT`: polynomial-time many-one reduction from `EUThreeSAT` to
  `ExactKSAT k` for `k ≥ 3`.

## Main results

- `CslibFrontier.Complexity.exactKSAT_three_eq`: `ExactKSAT 3 = EUThreeSAT`.
- `CslibFrontier.Complexity.exactKSAT_mem_NP`: `ExactKSAT k ∈ NP encCNF` for every `k : ℕ`.
- `CslibFrontier.Complexity.mem_exactKSAT_toExactKSAT_iff`: total soundness and completeness of
  `toExactKSAT k` for `k ≥ 3`.
- `CslibFrontier.Complexity.computableInPolyTime_toExactKSAT`: `toExactKSAT k` runs in polynomial
  time under `encCNF`.
- `CslibFrontier.Complexity.polyTimeReducible_EUThreeSAT_exactKSAT`,
  `CslibFrontier.Complexity.exactKSAT_npHard`,
  `CslibFrontier.Complexity.exactKSAT_npComplete`: `ExactKSAT k` is `NP`-complete for all `k ≥ 3`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Exact $k$-SAT language and `NP`-membership -/

/-- The exact `k`-satisfiability language: satisfiable CNF formulas over `ℕ` in which every clause
has length `k` and pairwise distinct variable indices. -/
@[expose] def ExactKSAT (k : ℕ) : Set (CNF ℕ) :=
  {φ | φ.IsExactDistinct k ∧ φ.Satisfiable}

/-- Membership characterization for `ExactKSAT k`. -/
theorem mem_exactKSAT_iff {k : ℕ} {φ : CNF ℕ} :
    φ ∈ ExactKSAT k ↔ φ.IsExactDistinct k ∧ φ.Satisfiable :=
  Iff.rfl

/-- At `k = 3`, `ExactKSAT 3` coincides with `Cslib.Complexity.EUThreeSAT`. -/
theorem exactKSAT_three_eq : ExactKSAT 3 = EUThreeSAT := by
  rfl

private def clauseExactDistinctCheck (k : ℕ) (c : Clause ℕ) : Bool :=
  let vs := c.map Prod.fst
  decide (c.length = k) && vs.zipIdx.all fun e ↦ decide (vs.idxOf e.1 = e.2)

private theorem nodup_iff_zipIdx_idxOf {α : Type*} [DecidableEq α] (l : List α) :
    (l.zipIdx.all fun e ↦ decide (l.idxOf e.1 = e.2)) = true ↔ l.Nodup := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun h ↦ List.nodup_iff_injective_get.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ ?_,
    fun hnd e he ↦ ?_⟩
  · simp only [List.get_eq_getElem] at hij
    have hi' : l.idxOf l[i] = i := h (l[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
    have hj' : l.idxOf l[j] = j := h (l[j], j) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
    exact Fin.ext ((hij ▸ hi').symm.trans hj')
  · obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
    rw [← heq]
    exact hnd.idxOf_getElem e.2 hlt

private theorem clauseExactDistinctCheck_iff (k : ℕ) (c : Clause ℕ) :
    clauseExactDistinctCheck k c = true ↔ c.IsExactDistinct k := by
  simp only [clauseExactDistinctCheck, Bool.and_eq_true, decide_eq_true_eq,
    nodup_iff_zipIdx_idxOf, Clause.IsExactDistinct]

/-- Executable Boolean test deciding whether `φ : CNF ℕ` satisfies `CNF.IsExactDistinct k`. -/
def exactKSATSyntaxCheck (k : ℕ) (φ : CNF ℕ) : Bool :=
  φ.all (clauseExactDistinctCheck k)

/-- `exactKSATSyntaxCheck k φ` returns `true` if and only if `φ.IsExactDistinct k`. -/
theorem exactKSATSyntaxCheck_iff (k : ℕ) (φ : CNF ℕ) :
    exactKSATSyntaxCheck k φ = true ↔ φ.IsExactDistinct k := by
  simp only [exactKSATSyntaxCheck, List.all_eq_true, clauseExactDistinctCheck_iff,
    CNF.IsExactDistinct]

/-- `exactKSATSyntaxCheck k` is computable in polynomial time under `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_exactKSATSyntaxCheck (k : ℕ) :
    ComputableInPolyTime (exactKSATSyntaxCheck k) encCNF encBool := by
  have hc : ComputableInPolyTime (clauseExactDistinctCheck k)
      (encList (encPair encNat encBool)) encBool := by
    unfold clauseExactDistinctCheck
    fun_prop
  unfold exactKSATSyntaxCheck encCNF
  fun_prop

/-- `ExactKSAT k` belongs to `NP encCNF` for every `k : ℕ`. -/
theorem exactKSAT_mem_NP (k : ℕ) : ExactKSAT k ∈ NP encCNF := by
  have hset : ExactKSAT k = {φ | exactKSATSyntaxCheck k φ = true ∧ φ ∈ SAT} :=
    Set.ext fun φ ↦ by simp only [ExactKSAT, Set.mem_ofPred_eq, exactKSATSyntaxCheck_iff, mem_SAT]
  have hpoly : ComputableInPolyTime (fun x : CNF ℕ × List Bool ↦
      exactKSATSyntaxCheck k x.1 && SAT.verifier x) (encPair encCNF encBits) encBool :=
    ComputableInPolyTime.bool_and'
      ((computableInPolyTime_exactKSATSyntaxCheck k).comp (ComputableInPolyTime.fst _ _))
      SAT.computableInPolyTime_verifier
  exact ⟨Polynomial.X, _, hpoly, hset ▸ SAT.isVerifier.guard⟩

/-! ### Padding reduction from `EUThreeSAT` to `ExactKSAT k` (`k ≥ 3`) -/

/-- All `2 ^ d` sign combinations on the `d` fresh padding variables `0, …, d - 1`: each clause in
`padSignCombos d` has length `d` and variables `[0, …, d - 1]`. -/
def padSignCombos : ℕ → List (Clause ℕ)
  | 0 => [[]]
  | d + 1 => (padSignCombos d).flatMap fun p ↦ [p ++ [(d, false)], p ++ [(d, true)]]

private theorem map_fst_of_mem_padSignCombos :
    ∀ {d : ℕ} {p : Clause ℕ}, p ∈ padSignCombos d → p.map Prod.fst = List.range d
  | 0, _, hp => by
    obtain rfl := List.mem_singleton.mp hp
    rfl
  | d + 1, _, hp => by
    obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;>
      simp [List.map_append, map_fst_of_mem_padSignCombos hq, List.range_succ]

private theorem exists_falsified_padSignCombos (σ : ℕ → Bool) :
    ∀ d : ℕ, ∃ p ∈ padSignCombos d, p.eval σ = false
  | 0 => ⟨[], List.mem_singleton.mpr rfl, rfl⟩
  | d + 1 => by
    obtain ⟨q, hq, hqev⟩ := exists_falsified_padSignCombos σ d
    refine ⟨q ++ [(d, !(σ d))], List.mem_flatMap.mpr ⟨q, hq, by cases σ d <;> simp⟩, ?_⟩
    rw [Bool.eq_false_iff]
    intro hev
    obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ _).mp hev
    rcases List.mem_append.mp hl with hlq | hld
    · have htrue : q.eval σ = true := (Clause.eval_eq_true_iff σ q).mpr ⟨l, hlq, hlσ⟩
      exact Bool.false_ne_true (hqev.symm.trans htrue)
    · obtain rfl := List.mem_singleton.mp hld
      cases hsd : σ d <;> simp [hsd] at hlσ

private def expandClauseToK (d : ℕ) (c : Clause ℕ) : CNF ℕ :=
  let shifted := c.map fun l ↦ (l.1 + d, l.2)
  (padSignCombos d).map fun p ↦ shifted ++ p

private theorem isExactDistinct_expandClauseToK (d : ℕ) {c : Clause ℕ}
    (hc : c.IsExactThreeDistinct) : (expandClauseToK d c).IsExactDistinct (3 + d) := by
  intro c' hc'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
  have hpv := map_fst_of_mem_padSignCombos hp
  have hplen : p.length = d := by simpa using congrArg List.length hpv
  refine ⟨by simp [hc.1, hplen], ?_⟩
  rw [List.map_append, hpv, List.map_map]
  have hsh : (Prod.fst ∘ fun l : Literal ℕ ↦ (l.1 + d, l.2)) = (· + d) ∘ Prod.fst := rfl
  rw [hsh, ← List.map_map]
  refine List.nodup_append.mpr ⟨hc.2.map (add_left_injective d), List.nodup_range, ?_⟩
  intro x hx y hy hxy
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  have hylt : y < d := List.mem_range.mp hy
  omega

private theorem eval_expandClauseToK_iff (d : ℕ) (σ : ℕ → Bool) (c : Clause ℕ) :
    (expandClauseToK d c).eval σ = true ↔ c.eval (fun v ↦ σ (v + d)) = true := by
  rw [CNF.eval, List.all_eq_true]
  constructor
  · intro hall
    obtain ⟨p, hp, hpf⟩ := exists_falsified_padSignCombos σ d
    have hsat := hall _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ _).mp hsat
    rcases List.mem_append.mp hl with hls | hlp
    · obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hls
      exact (Clause.eval_eq_true_iff _ c).mpr ⟨l₀, hl₀, hlσ⟩
    · have hpt : p.eval σ = true := (Clause.eval_eq_true_iff σ p).mpr ⟨l, hlp, hlσ⟩
      exact absurd (hpf.symm.trans hpt) Bool.false_ne_true
  · intro hc c' hc'
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨l₀, hl₀, hl₀σ⟩ := (Clause.eval_eq_true_iff _ c).mp hc
    exact (Clause.eval_eq_true_iff σ _).mpr
      ⟨(l₀.1 + d, l₀.2), List.mem_append_left _ (List.mem_map_of_mem hl₀), hl₀σ⟩

/-- Total polynomial-time reduction from `EUThreeSAT` to `ExactKSAT k` (for `k ≥ 3`): checks
`EUThreeSAT.syntaxCheck`, shifts variables by `k - 3`, and expands every 3-literal clause by all
`2 ^ (k - 3)` sign combinations on `{0, …, k - 4}`; rejects malformed inputs with `[[]]`. -/
def toExactKSAT (k : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  if EUThreeSAT.syntaxCheck φ then φ.flatMap (expandClauseToK (k - 3)) else [[]]

/-- Total correctness of `toExactKSAT k` for every `k ≥ 3`. -/
theorem mem_exactKSAT_toExactKSAT_iff {k : ℕ} (hk : 3 ≤ k) (φ : CNF ℕ) :
    toExactKSAT k φ ∈ ExactKSAT k ↔ φ ∈ EUThreeSAT := by
  set d := k - 3
  have hkd : 3 + d = k := by omega
  unfold toExactKSAT
  split_ifs with hs
  · have hφ : φ.IsExactThreeDistinct := (EUThreeSAT.syntaxCheck_iff φ).mp hs
    have hex : CNF.IsExactDistinct k (φ.flatMap (expandClauseToK d)) := by
      rw [← hkd]
      intro c' hc'
      obtain ⟨c, hc, hc'⟩ := List.mem_flatMap.mp hc'
      exact isExactDistinct_expandClauseToK d (hφ c hc) c' hc'
    refine ⟨fun ⟨_, σ, hσ⟩ ↦ ⟨hφ, fun v ↦ σ (v + d), ?_⟩, fun ⟨_, σ, hσ⟩ ↦ ⟨hex, ?_⟩⟩
    · rw [CNF.eval_eq_true_iff]
      intro c hc
      exact (eval_expandClauseToK_iff d σ c).mp ((CNF.eval_flatMap_eq_true_iff σ _ _).mp hσ c hc)
    · refine ⟨fun u ↦ if d ≤ u then σ (u - d) else false, ?_⟩
      rw [CNF.eval_flatMap_eq_true_iff]
      intro c hc
      rw [eval_expandClauseToK_iff]
      have hshift : (fun v ↦ if d ≤ v + d then σ (v + d - d) else false) = σ :=
        funext fun v ↦ by simp
      rw [hshift]
      exact (CNF.eval_eq_true_iff σ φ).mp hσ c hc
  · have hns : ¬ φ.IsExactThreeDistinct := fun h ↦ hs ((EUThreeSAT.syntaxCheck_iff φ).mpr h)
    refine iff_of_false (fun ⟨hex, _⟩ ↦ ?_) fun ⟨h, _⟩ ↦ hns h
    have h0 := (hex [] (List.mem_singleton.mpr rfl)).1
    simp only [List.length_nil] at h0
    omega

/-- `toExactKSAT k` is computable in polynomial time under `encCNF` for every fixed `k : ℕ`. -/
@[fun_prop]
theorem computableInPolyTime_toExactKSAT (k : ℕ) :
    ComputableInPolyTime (toExactKSAT k) encCNF encCNF := by
  have hexp : ∀ p : Clause ℕ,
      ComputableInPolyTime (fun c : Clause ℕ ↦ (c.map fun l ↦ (l.1 + (k - 3), l.2)) ++ p)
        (encList (encPair encNat encBool)) (encList (encPair encNat encBool)) :=
    fun _ ↦ by fun_prop
  have hlist : ∀ ps : List (Clause ℕ),
      ComputableInPolyTime
        (fun c : Clause ℕ ↦ ps.map fun p ↦ (c.map fun l ↦ (l.1 + (k - 3), l.2)) ++ p)
        (encList (encPair encNat encBool)) encCNF := by
    intro ps
    induction ps with
    | nil => exact ComputableInPolyTime.const []
    | cons p ps ih =>
      unfold encCNF at ih ⊢
      simpa only [List.map_cons] using ComputableInPolyTime.cons' (hexp p) ih
  have hcl : ComputableInPolyTime (expandClauseToK (k - 3))
      (encList (encPair encNat encBool)) encCNF := hlist (padSignCombos (k - 3))
  unfold toExactKSAT encCNF
  unfold encCNF at hcl
  fun_prop

/-- `EUThreeSAT` polynomial-time many-one reduces to `ExactKSAT k` for all `k ≥ 3`. -/
theorem polyTimeReducible_EUThreeSAT_exactKSAT {k : ℕ} (hk : 3 ≤ k) :
    PolyTimeReducible encCNF encCNF EUThreeSAT (ExactKSAT k) :=
  ⟨toExactKSAT k, computableInPolyTime_toExactKSAT k,
    fun φ ↦ (mem_exactKSAT_toExactKSAT_iff hk φ).symm⟩

/-- `ExactKSAT k` is unconditionally `NP`-hard for all `k ≥ 3`. -/
theorem exactKSAT_npHard {k : ℕ} (hk : 3 ≤ k) : NPHard encCNF (ExactKSAT k) :=
  EUThreeSAT_npHard.trans (polyTimeReducible_EUThreeSAT_exactKSAT hk)

/-- **Exact $k$-SAT is `NP`-complete** for every fixed `k ≥ 3`. -/
theorem exactKSAT_npComplete {k : ℕ} (hk : 3 ≤ k) : NPComplete encCNF (ExactKSAT k) :=
  ⟨exactKSAT_mem_NP k, exactKSAT_npHard hk⟩

/-! ### Internal non-vacuity check -/

/-- For every `k ≥ 1`, `ExactKSAT k` contains both a satisfiable formula and excludes an
unsatisfiable `IsExactDistinct k` formula. -/
private theorem exactKSAT_nonempty_and_nontrivial {k : ℕ} (hk : 1 ≤ k) :
    ([(List.range k).map fun i ↦ (i, true)] ∈ ExactKSAT k) ∧
      CNF.IsExactDistinct k (padSignCombos k) ∧ padSignCombos k ∉ ExactKSAT k := by
  refine ⟨⟨fun c hc ↦ ?_, fun _ ↦ true, ?_⟩, fun c hc ↦ ?_, fun ⟨_, σ, hσ⟩ ↦ ?_⟩
  · obtain rfl := List.mem_singleton.mp hc
    refine ⟨by simp, ?_⟩
    simpa [List.map_map, Function.comp_def] using List.nodup_range
  · rw [CNF.eval_eq_true_iff]
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact (Clause.eval_eq_true_iff _ _).mpr
      ⟨(0, true), List.mem_map.mpr ⟨0, List.mem_range.mpr hk, rfl⟩, rfl⟩
  · have hv := map_fst_of_mem_padSignCombos hc
    exact ⟨by simpa using congrArg List.length hv, hv ▸ List.nodup_range⟩
  · obtain ⟨p, hp, hpf⟩ := exists_falsified_padSignCombos σ k
    have hpt := (CNF.eval_eq_true_iff σ _).mp hσ p hp
    exact Bool.false_ne_true (hpf.symm.trans hpt)

end CslibFrontier.Complexity
