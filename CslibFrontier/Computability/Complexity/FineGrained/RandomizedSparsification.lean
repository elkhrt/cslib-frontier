/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Randomized
public import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
public import CslibFrontier.Computability.Complexity.Problems.Coloring
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.FineGrained.GraphProblems
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Foundations.Data.List.Fold
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification
import CslibFrontier.Tactic.EncLen

/-!
# One-sided randomized (`RP`) sparsification and `rETH` clause/graph lower bounds

This module extends algorithmic sparsification (`Cslib.Complexity.Sparsify`) to one-sided-error
randomized (`ErrorModel.oneSidedRP`) solvers:

* Running `Sparsify.search` with a single random seed `w` of length `L_max(φ)` (sliced via
  `padTake ℓ (ψ, w)` at each sparse leaf `ψ`) preserves zero false positives (`noErr = 0`) and
  preserves the false-negative bound `yesErr` on any satisfiable leaf `ψ*` without any union bound
  over leaves.
* Converting any binary-time-computable `L_max : CNF ℕ → ℕ` to unary via `ComputableInO.iterate`
  keeps the overall runtime within `2 ^ ((ε + c * δ) * n) · poly(|φ|)`.

## Main results

* `Cslib.Complexity.exists_solvesWithErrorInExpTime_oneSidedRP_numVars_of_length`:
  one-sided `RP` sparsification from clauses (`List.length`) to variables (`CNF.numVars`).
* `Cslib.Complexity.SolvesWithErrorInSubexpTime.oneSidedRP_numVars_of_length`:
  subexponential one-sided `RP` time in clauses implies subexponential one-sided `RP` time in
  variables.
* `Cslib.Complexity.rETH.not_solvesWithErrorInSubexpTime_oneSidedRP_length`:
  under `rETH`, `ThreeSAT` has no one-sided `RP` subexponential solver in the number of clauses.
* `Cslib.Complexity.rETH.not_solvesWithErrorInSubexpTime_oneSidedRP_ThreeColoring`:
  under `rETH`, `ThreeColoring` has no one-sided `RP` subexponential solver in `|V| + |E|`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM PromiseProblem
open ClauseSet.Sparsification (base one_le_threshold BranchingRule)
open scoped List

private abbrev spThreshold := ClauseSet.Sparsification.threshold

/-! ### Seed padding and binary-to-unary conversion -/

/-- Pad or truncate a seed `w` to exact length `ℓ a` using `true` bits. -/
private def rpPadTake {α : Type} (ℓ : α → ℕ) (p : α × List Bool) : List Bool :=
  (p.2 ++ List.replicate (ℓ p.1) true).take (ℓ p.1)

private theorem length_rpPadTake {α : Type} (ℓ : α → ℕ) (p : α × List Bool) :
    (rpPadTake ℓ p).length = ℓ p.1 := by
  simp [rpPadTake]

private theorem rpPadTake_of_le {α : Type} (ℓ : α → ℕ) (a : α) {w : List Bool}
    (hw : ℓ a ≤ w.length) : rpPadTake ℓ (a, w) = w.take (ℓ a) := by
  simp [rpPadTake, List.take_append_of_le_length hw]

private theorem computableInO_rpPadTake {α : Type} {enc : α ↪ List Bool} {ℓ : α → ℕ}
    {Tℓ Sℓ : α → ℕ} (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ) :
    ∃ Tpad Spad : α × List Bool → ℕ,
      ComputableInO (rpPadTake ℓ) (encPair enc encBits) encBits Tpad Spad ∧
      ∀ p, Tpad p ≤ 4 * (encPair enc encBits p).length + 2 * Tℓ p.1 := by
  have hℓ_fst := hℓ.comp (ComputableInO.fst enc encBits)
  have happ : ComputableInO (fun p : α × List Bool => p.2 ++ List.replicate (ℓ p.1) true)
      (encPair enc encBits) encBits _ _ :=
    (ComputableInO.snd enc encBits).append hℓ_fst fun _ => rfl
  have htake := (ComputableInO.of_linear ComputableInDegree.bitsTake).comp_linear
    (happ.prod hℓ_fst)
  refine ⟨_, _, htake, fun p => ?_⟩
  omega

/-- Convert any binary-encoded natural function `n : α → ℕ` to unary in time polynomial in
`n a` plus the binary computation time `Tn a`, using a given degree bound `d` for `m ↦ m + 1`. -/
theorem computableInO_binary_to_unary_of_deg {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    {Tn Sn : α → ℕ} {d e : ℕ}
    (hsucc : ComputableInDegree (fun m : ℕ => m + 1) encUnary encUnary d e)
    (hn : ComputableInO n enc encNat Tn Sn) :
    ∃ Tu Su : α → ℕ,
      ComputableInO n enc encUnary Tu Su ∧
      ∀ a, Tu a ≤ Tn a + (enc a).length +
        (n a + 1) * ((n a + 1) ^ d + n a + ((encNat (n a)).length + 1) ^ 2) + 1 := by
  have hinit : ComputableInO (fun _ : α => (0 : ℕ)) enc encUnary
      (fun a => (enc a).length) (fun _ => 0) :=
    ComputableInO.constZero 0
  have hiter_id : ∀ m : ℕ, (· + 1)^[m] 0 = m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih]
  have hround : ∀ a, ∀ k ≤ n a, ((encUnary ((· + 1)^[k] 0)).length + 1) ^ d ≤ (n a + 1) ^ d := by
    intro a k hk
    rw [hiter_id k, encUnary_apply, List.length_replicate]
    exact Nat.pow_le_pow_left (by omega) d
  have hstate : ∀ a, ∀ k ≤ n a, (encUnary ((· + 1)^[k] 0)).length ≤ n a := by
    intro a k hk
    rw [hiter_id k, encUnary_apply, List.length_replicate]
    exact hk
  have hit := ComputableInO.iterate hn hinit hsucc.inO hround hround hstate
  have heq : (fun a : α => (· + 1)^[n a] 0) = n := by
    funext a
    induction n a with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]
  rw [heq] at hit
  exact ⟨_, _, hit, fun a => by omega⟩

/-- Convert any binary-encoded natural function `n : α → ℕ` to unary in time polynomial in
`n a` plus the binary computation time `Tn a`. -/
theorem computableInO_binary_to_unary {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    {Tn Sn : α → ℕ} (hn : ComputableInO n enc encNat Tn Sn) :
    ∃ d : ℕ, ∃ Tu Su : α → ℕ,
      ComputableInO n enc encUnary Tu Su ∧
      ∀ a, Tu a ≤ Tn a + (enc a).length +
        (n a + 1) * ((n a + 1) ^ d + n a + ((encNat (n a)).length + 1) ^ 2) + 1 := by
  obtain ⟨d, e, hsucc⟩ := (show ComputableInPolyTime (fun m : ℕ => m + 1) encUnary encUnary by
    fun_prop).exists_degree
  obtain ⟨Tu, Su, h1, h2⟩ := computableInO_binary_to_unary_of_deg hsucc hn
  exact ⟨d, Tu, Su, h1, h2⟩

/-! ### Seeded sparsification search -/

namespace RandomizedSparsify

/-- Seeded search state: stack of formulas, Boolean accumulator, and shared random seed. -/
abbrev SeededState : Type := Sparsify.State × List Bool

private abbrev encSeededState : SeededState ↪ List Bool :=
  encPair (encPair (encList encCNF) encBool) encBits

/-- One step of the seeded depth-first sparsification search, preserving the random seed `w`. -/
def seededStep (K α : ℕ) (V : CNF ℕ × List Bool → Bool) (s : SeededState) : SeededState :=
  (Sparsify.step K α (fun ψ => V (ψ, s.2)) s.1, s.2)

private theorem iterate_seededStep (K α : ℕ) (V : CNF ℕ × List Bool → Bool) (i : ℕ)
    (s : Sparsify.State) (w : List Bool) :
    (seededStep K α V)^[i] (s, w) = ((Sparsify.step K α (fun ψ => V (ψ, w)))^[i] s, w) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, seededStep, ih]

/-- Seeded sparsification search: runs `Sparsify.search` using the fixed seed `w` at every leaf. -/
def seededSearch (K α k M : ℕ) (V : CNF ℕ × List Bool → Bool) (p : CNF ℕ × List Bool) : Bool :=
  (((seededStep K α V)^[Sparsify.rounds M p.1] (([Sparsify.root k p.1], false), p.2)).1).2

private theorem seededSearch_eq (K α k M : ℕ) (V : CNF ℕ × List Bool → Bool)
    (p : CNF ℕ × List Bool) :
    seededSearch K α k M V p = Sparsify.search K α k M (fun ψ => V (ψ, p.2)) p.1 := by
  simp only [seededSearch, Sparsify.search, iterate_seededStep]

private theorem exists_step_degree (K α : ℕ) :
    ∃ d : ℕ, ∀ {V : CNF ℕ × List Bool → Bool} {Tv Sv : CNF ℕ × List Bool → ℕ},
      ComputableInO V (encPair encCNF encBits) encBool Tv Sv →
      ∃ C : ℕ, ComputableInO (seededStep K α V) encSeededState encSeededState
        (fun s => C * (((encSeededState s).length + 1) ^ d +
          if s.1.1.isEmpty = false ∧
              isSparse (ClauseSet.Sparsification.threshold K α) K (s.1.1.headD []) = true then
            Tv (s.1.1.headD [], s.2) else 0) + C)
        (fun s => C * (((encSeededState s).length + 1) ^ d +
          if s.1.1.isEmpty = false ∧
              isSparse (ClauseSet.Sparsification.threshold K α) K (s.1.1.headD []) = true then
            Sv (s.1.1.headD [], s.2) else 0) + C) := by
  -- Fixed polynomial-time subcomponents independent of `V`:
  obtain ⟨dE, _, hE⟩ := (show ComputableInPolyTime (fun s : SeededState => s.1.1.isEmpty)
    encSeededState encBool by unfold encSeededState; fun_prop).exists_degree
  obtain ⟨dI, _, hI⟩ := (ComputableInPolyTime.id' (encIn := encSeededState)).exists_degree
  obtain ⟨dS, _, hS⟩ := (show ComputableInPolyTime
    (fun s : SeededState =>
      isSparse (ClauseSet.Sparsification.threshold K α) K (s.1.1.headD []))
    encSeededState encBool by
      have h := computableInPolyTime_isSparse encNat
        (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
      have hH : ComputableInPolyTime (fun s : SeededState => s.1.1.headD [])
          encSeededState encCNF := by unfold encSeededState; fun_prop
      exact h.comp hH).exists_degree
  obtain ⟨dH, _, hH⟩ := (show ComputableInPolyTime (fun s : SeededState => (s.1.1.headD [], s.2))
    encSeededState (encPair encCNF encBits) by unfold encSeededState; fun_prop).exists_degree
  obtain ⟨dB, _, hB⟩ := (show ComputableInPolyTime (fun s : SeededState => s.1.2)
    encSeededState encBool by unfold encSeededState; fun_prop).exists_degree
  obtain ⟨dT, _, hT⟩ := (show ComputableInPolyTime (fun s : SeededState => s.1.1.tail)
    encSeededState (encList encCNF) by unfold encSeededState; fun_prop).exists_degree
  obtain ⟨dW, _, hW⟩ := (show ComputableInPolyTime (fun s : SeededState => s.2)
    encSeededState encBits by unfold encSeededState; fun_prop).exists_degree
  obtain ⟨dN, _, hN⟩ := (show ComputableInPolyTime
    (fun s : SeededState =>
      ((next (spThreshold K α) K (s.1.1.headD []) false ::
        next (spThreshold K α) K (s.1.1.headD []) true :: s.1.1.tail, s.1.2), s.2))
    encSeededState encSeededState by
      have h := computableInPolyTime_next encNat
        (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
      unfold encSeededState encCNF; fun_prop).exists_degree
  obtain ⟨dO, _, hO⟩ := ComputableInPolyTime.bool_or.exists_degree
  set D := dE + dI + dS + dH + dB + dT + dW + dN
  refine ⟨D, fun {V Tv Sv} hV => ?_⟩
  have hE' := (hE.mono (d' := D) (by omega) le_rfl).inO
  have hI' := (hI.mono (d' := D) (by omega) le_rfl).inO
  have hS' := (hS.mono (d' := D) (by omega) le_rfl).inO
  have hH' := (hH.mono (d' := D) (by omega) le_rfl).inO
  have hB' := (hB.mono (d' := D) (by omega) le_rfl).inO
  have hT' := (hT.mono (d' := D) (by omega) le_rfl).inO
  have hW' := (hW.mono (d' := D) (by omega) le_rfl).inO
  have hN' := (hN.mono (d' := D) (by omega) le_rfl).inO
  have hleaf := (hT'.prod (hO.inO.comp (hB'.prod (hV.comp hH')))).prod hW'
  have h := hE'.ite hI' (hS'.ite hleaf hN')
  have h4 (p : Bool × Bool) : (encPair encBool encBool p).length = 4 := by simp
  have hstep_eq : (fun s : SeededState =>
      if s.1.1.isEmpty then s
      else if isSparse (spThreshold K α) K (s.1.1.headD []) then
        ((s.1.1.tail, s.1.2 || V (s.1.1.headD [], s.2)), s.2)
      else ((next (spThreshold K α) K (s.1.1.headD []) false ::
        next (spThreshold K α) K (s.1.1.headD []) true :: s.1.1.tail, s.1.2), s.2)) =
      seededStep K α V := by
    funext s; unfold seededStep Sparsify.step; split_ifs <;> rfl
  dsimp only [Function.comp_apply] at h
  change ComputableInO
    (fun s : SeededState =>
      if s.1.1.isEmpty then s
      else if isSparse (spThreshold K α) K (s.1.1.headD []) then
        ((s.1.1.tail, s.1.2 || V (s.1.1.headD [], s.2)), s.2)
      else ((next (spThreshold K α) K (s.1.1.headD []) false ::
        next (spThreshold K α) K (s.1.1.headD []) true :: s.1.1.tail, s.1.2), s.2))
    encSeededState encSeededState _ _ at h
  rw [hstep_eq] at h
  refine ⟨5 ^ dO + 9, h.mono 1 (fun s => ?_) (fun s => ?_)⟩
  all_goals
    simp only [h4, one_mul]
    generalize ((encSeededState s).length + 1) ^ D = P
    have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
    generalize (4 + 1) ^ dO = F at hF ⊢
    cases s.1.1.isEmpty <;> cases isSparse (spThreshold K α) K (s.1.1.headD []) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, and_true, and_false,
        Bool.true_eq_false] <;> nlinarith

end RandomizedSparsify

/-! ### Main one-sided `RP` sparsification theorem -/

private theorem acceptCount_scale {α : Type} (W₀ W₁ : α × List Bool → Bool) (a : α)
    {m n : ℕ} (hmn : m ≤ n)
    (hprefix : ∀ u : List Bool, u.length = m → ∀ rest : List Bool,
      W₁ (a, u ++ rest) = W₀ (a, u)) {B : ℝ}
    (hB : (acceptCount W₀ a m : ℝ) ≤ B * 2 ^ m) :
    (acceptCount W₁ a n : ℝ) ≤ B * 2 ^ n := by
  have hcount : acceptCount W₁ a n = acceptCount W₀ a m * 2 ^ (n - m) := by
    have hsplit : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
    conv_lhs => rw [hsplit, acceptCount_add]
    calc ∑ u : Fin m → Bool, acceptCount (fun x => W₁ (x.1, List.ofFn u ++ x.2)) a (n - m)
        = ∑ u : Fin m → Bool, if W₀ (a, List.ofFn u) = true then 2 ^ (n - m) else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [acceptCount_congr (W := fun _ => W₀ (a, List.ofFn u))
            (fun rest => hprefix _ List.length_ofFn rest) _]
          cases W₀ (a, List.ofFn u) <;> simp
      _ = acceptCount W₀ a m * 2 ^ (n - m) := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]; rfl
  have hpow_eq : (2 : ℝ) ^ n = (2 : ℝ) ^ m * (2 : ℝ) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  rw [hcount, hpow_eq]
  push_cast
  exact (mul_le_mul_of_nonneg_right hB (by positivity)).trans_eq (mul_assoc ..)

private theorem rp_step_iterate_map {K α : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α) (g : CNF ℕ → Bool) :
    ∀ (n : ℕ) (stk : List {ψ : CNF ℕ // Normalized K ψ}) (acc : Bool),
      (Sparsify.step K α g)^[n] (stk.map Subtype.val, acc) =
        Prod.map (List.map Subtype.val) id
          (((CNF.Sparsification.rule (V := ℕ) (one_le_threshold hK hα) K).tree.searchStep
            (fun acc t => acc || g t.1))^[n] (stk, acc)) := by
  classical
  let R : BranchingRule (spThreshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
    CNF.Sparsification.rule (one_le_threshold hK hα) K
  intro n; induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro stk acc
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have h1 : Sparsify.step K α g (stk.map Subtype.val, acc) =
        Prod.map (List.map Subtype.val) id
          (R.tree.searchStep (fun acc t => acc || g t.1) (stk, acc)) := by
      cases stk with
      | nil => rfl
      | cons s rest =>
        have hiff := isSparse_eq_true_iff (one_le_threshold hK hα) s.2
        by_cases hs : ClauseSet.Sparsification.Sparse (spThreshold K α) s.1.toClauseSet
        · have hs' : isSparse (spThreshold K α) K s.1 = true := hiff.mpr hs
          simp [Sparsify.step, BinaryBranching.searchStep, hs, hs', CNF.Sparsification.rule, R]
        · have hs' : isSparse (spThreshold K α) K s.1 = false := by
            simpa using fun h => hs (hiff.mp h)
          simp [Sparsify.step, BinaryBranching.searchStep, hs, hs', CNF.Sparsification.rule, R]
    rw [h1]
    obtain ⟨stk', acc'⟩ := R.tree.searchStep (fun acc t => acc || g t.1) (stk, acc)
    exact ih stk' acc'

private theorem rp_root_normalized {K k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) :
    Normalized K (Sparsify.root k φ) := by
  unfold Sparsify.root
  split_ifs with h
  · simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact normalized_normalize fun C hC => (h C hC).trans hkK
  · exact ⟨by simp, by simp, by simp,
      by simp [CNF.toClauseSet, ClauseSet.Sparsification.Reduced]⟩

private theorem rp_root_vars_mem {k : ℕ} (φ : CNF ℕ)
    (hroot : Sparsify.root k φ = normalize φ) :
    ∀ C ∈ (Sparsify.root k φ).toClauseSet, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
  intro C hC l hl
  obtain ⟨C', hC', rfl⟩ := mem_toClauseSet.mp hC
  rw [hroot] at hC'
  have hsub : normalize φ <+ φ.map dedup :=
    (reduce_sublist _).trans (dedupClauses_sublist _)
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC')
  rw [toFinset_dedup, List.mem_toFinset] at hl
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl⟩, rfl⟩)

private theorem rp_search_eq_true_iff {K α k M : ℕ} (hK : 1 ≤ K) (hkK : k ≤ K) (hα : 1 ≤ α)
    (hLB : Sparsify.LeafBound K α M) (g : CNF ℕ → Bool) (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ k) :
    Sparsify.search K α k M g φ = true ↔
      ∃ u, (CNF.Sparsification.rule (V := ℕ) (one_le_threshold hK hα) K).tree.IsLeafWord
        ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩ u ∧
        g ((CNF.Sparsification.rule (V := ℕ) (one_le_threshold hK hα) K).tree.walk
          ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩ u).1 = true := by
  classical
  let R : BranchingRule (spThreshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
    CNF.Sparsification.rule (one_le_threshold hK hα) K
  let s₀ : {ψ : CNF ℕ // Normalized K ψ} := ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩
  have hroot : Sparsify.root k φ = normalize φ :=
    ite_eq_left (List.all_eq_true.mpr fun cl hcl => decide_eq_true (hw cl hcl))
  have hroot_mem := rp_root_vars_mem φ hroot
  have hlen_w : ∀ u, R.tree.IsLeafWord s₀ u → u.length ≤ φ.numVars * (K * base K α ^ (2 * K)) :=
    fun u hu => BranchingRule.length_le_of_isLeafWord hK hα s₀.2.reduced s₀.2.card_le
      φ.vars.toFinset hroot_mem hu
  obtain ⟨L, hnd, hL, N, hN, hrun⟩ := R.tree.exists_iterate_searchStep
    (BranchingRule.tree_terminating (one_le_threshold hK hα)) (fun acc t => acc || g t.1) s₀
    hlen_w
  have hLcard : L.length ≤ 2 ^ (φ.numVars / M + 1) := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact (BranchingRule.card_le_of_isLeafWord hK hα s₀.2.reduced s₀.2.card_le
      φ.vars.toFinset hroot_mem L.toFinset
      fun u hu => (hL u).mp (List.mem_toFinset.mp hu)).trans (hLB φ.numVars)
  have hNr : N ≤ Sparsify.rounds M φ := by
    grind [Sparsify.rounds, CNF.length_distinctVars, pow_succ]
  have hacc : (L.map (R.tree.walk s₀)).foldl (fun acc t => acc || g t.1) false =
      decide (∃ u, R.tree.IsLeafWord s₀ u ∧ g (R.tree.walk s₀ u).1 = true) := by
    rw [List.foldl_or_eq, Bool.false_or, List.any_map, Bool.eq_iff_iff, List.any_eq_true,
      decide_eq_true_iff]
    simp only [hL, Function.comp_apply]
  have hfin := (hrun [] false).1
  have hN_eq : (Sparsify.step K α g)^[N] ([Sparsify.root k φ], false) =
      ([], decide (∃ u, R.tree.IsLeafWord s₀ u ∧ g (R.tree.walk s₀ u).1 = true)) := by
    change (Sparsify.step K α g)^[N] (([s₀]).map Subtype.val, false) = _
    rw [rp_step_iterate_map hK hα, hfin, hacc]; simp
  have hnil_fix : ∀ m, (Sparsify.step K α g)^[m] ([], decide (∃ u, R.tree.IsLeafWord s₀ u ∧
      g (R.tree.walk s₀ u).1 = true)) = ([], decide (∃ u, R.tree.IsLeafWord s₀ u ∧
      g (R.tree.walk s₀ u).1 = true)) := fun m => Function.iterate_fixed rfl m
  rw [Sparsify.search, show Sparsify.rounds M φ = (Sparsify.rounds M φ - N) + N by omega,
    Function.iterate_add_apply, hN_eq, hnil_fix, decide_eq_true_iff]

private theorem rp_seeded_traj {K α k : ℕ} (hK : 1 ≤ K) (hkK : k ≤ K) (hα : 1 ≤ α)
    (V_leaf : CNF ℕ × List Bool → Bool) (φ : CNF ℕ) (w : List Bool) (i : ℕ) :
    ∃ (stk : List {ψ : CNF ℕ // Normalized K ψ}) (acc : Bool),
      (RandomizedSparsify.seededStep K α V_leaf)^[i] (([Sparsify.root k φ], false), w) =
        ((stk.map Subtype.val, acc), w) ∧
      stk.length ≤ φ.numVars * (K * base K α ^ (2 * K)) + 1 ∧
      ∀ t ∈ stk, ∃ u,
        (CNF.Sparsification.rule (V := ℕ) (one_le_threshold hK hα) K).tree.IsNodeWord
          ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩ u ∧
        (CNF.Sparsification.rule (V := ℕ) (one_le_threshold hK hα) K).tree.walk
          ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩ u = t := by
  classical
  rw [RandomizedSparsify.iterate_seededStep]
  set g := fun ψ => V_leaf (ψ, w)
  let R : BranchingRule (spThreshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
    CNF.Sparsification.rule (one_le_threshold hK hα) K
  let s₀ : {ψ : CNF ℕ // Normalized K ψ} := ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩
  have hroot_mem : ∀ C ∈ (Sparsify.root k φ).toClauseSet, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
    unfold Sparsify.root
    split_ifs with h
    · have h1 := rp_root_vars_mem (k := k) φ (ite_eq_left h)
      simpa [Sparsify.root, h] using h1
    · intro C hC; simp [CNF.toClauseSet] at hC
  have hlen_u : ∀ u, R.tree.IsLeafWord s₀ u → u.length ≤ φ.numVars * (K * base K α ^ (2 * K)) :=
    fun u hu => BranchingRule.length_le_of_isLeafWord hK hα s₀.2.reduced s₀.2.card_le
      φ.vars.toFinset hroot_mem hu
  obtain ⟨L, hnd, hL, N, hN, hrun⟩ := R.tree.exists_iterate_searchStep
    (BranchingRule.tree_terminating (one_le_threshold hK hα)) (fun acc t => acc || g t.1) s₀
    hlen_u
  obtain ⟨hfin, hmid⟩ := hrun [] false
  have hN_eq : (Sparsify.step K α g)^[N] ([Sparsify.root k φ], false) =
      ([], (L.map (R.tree.walk s₀)).foldl (fun acc t => acc || g t.1) false) := by
    change (Sparsify.step K α g)^[N] (([s₀]).map Subtype.val, false) = _
    rw [rp_step_iterate_map hK hα, hfin]; simp
  by_cases hi : i ≤ N
  · obtain ⟨stk, L', -, heq, hstk, hmem⟩ := hmid i hi
    refine ⟨stk, (L'.map (R.tree.walk s₀)).foldl (fun acc t => acc || g t.1) false, ?_, hstk,
      fun t ht => ?_⟩
    · change (Sparsify.step K α g)^[i] (([s₀]).map Subtype.val, false) |> fun x => (x, w) = _
      rw [rp_step_iterate_map hK hα, heq]; simp
    · obtain ⟨u, hu, -, rfl⟩ := hmem t ht; exact ⟨u, hu, rfl⟩
  · refine ⟨[], (L.map (R.tree.walk s₀)).foldl (fun acc t => acc || g t.1) false, ?_,
      by simp, by simp⟩
    rw [show i = (i - N) + N by omega, Function.iterate_add_apply, hN_eq,
      Function.iterate_fixed rfl]
    rfl

private theorem rp_sparsify_round_bound
    {M Ms dS e c₀ c₁ c₂ B_c cStep Kx occ L N nodeB ℓ_val : ℕ} {φ : CNF ℕ}
    {δ : ℝ} (hMs_lo : δ * (occ : ℝ) ≤ 1 / (Ms : ℝ))
    (hc₂ : c₂ = 4 * (Kx + 1) * (2 * c₁ + 1) + 2)
    (hNL : N ≤ L) (hnb : nodeB ≤ c₁ * (L + 1) ^ 2)
    (hℓ_R : (ℓ_val : ℝ) ≤ (2 * B_c : ℝ) * (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) *
      ((L : ℝ) + 1) ^ (2 * e))
    (hcnt_R : (((encNat (Sparsify.rounds M φ)).length : ℝ) + 1) ^ 2 ≤ 16 * ((L : ℝ) + 1) ^ 2) :
    let sb := 2 * (2 * ((N * Kx + 1) * (2 * nodeB + 1)) + 2) + 2 * ℓ_val + 4
    let lt := 5 * (2 * nodeB + 2 * ℓ_val + 4) +
      3 * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * ⌈(2 : ℝ) ^ (δ * (occ * N : ℝ))⌉₊ * (nodeB + 1) ^ e + c₀ + 2)
    let r_rnd := cStep * ((sb + 1) ^ dS + lt) + cStep
    let C_sb := c₂ + 4 * B_c + 8
    let C_lt := 10 * (c₁ + 1) + 20 * B_c + 30 +
      6 * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2)
    let C_rnd := cStep * (C_sb ^ dS + C_lt) + cStep + C_sb + 25
    (r_rnd : ℝ) + (sb : ℝ) + (((encNat (Sparsify.rounds M φ)).length : ℝ) + 1) ^ 2 ≤
      (C_rnd : ℝ) * ((2 : ℝ) ^ ((((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
        ((L : ℝ) + 1) ^ (max 3 (2 * e) * max dS 1 + 2)) := by
  intro sb lt r_rnd C_sb C_lt C_rnd
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hsb_nat : sb + 1 ≤ c₂ * (L + 1) ^ 3 + 2 * ℓ_val + 7 := by
    have hnb1 : 2 * nodeB + 1 ≤ (2 * c₁ + 1) * (L + 1) ^ 2 := by
      have hsq : 1 ≤ (L + 1) ^ 2 := one_le_pow₀ (Nat.succ_pos L)
      nlinarith
    have h1' : (N * Kx + 1) * (2 * nodeB + 1) ≤ (Kx + 1) * (2 * c₁ + 1) * (L + 1) ^ 3 := by
      have hnk : N * Kx + 1 ≤ (Kx + 1) * (L + 1) := by nlinarith [hNL]
      calc (N * Kx + 1) * (2 * nodeB + 1)
          ≤ ((Kx + 1) * (L + 1)) * ((2 * c₁ + 1) * (L + 1) ^ 2) := Nat.mul_le_mul hnk hnb1
        _ = (Kx + 1) * (2 * c₁ + 1) * (L + 1) ^ 3 := by ring
    have hsq3 : 1 ≤ (L + 1) ^ 3 := one_le_pow₀ (Nat.succ_pos L)
    dsimp only [sb]; rw [hc₂]; nlinarith only [h1', hsq3]
  have hsb_R : ((sb : ℝ) + 1) ≤
      (C_sb : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e))) := by
    have hcast : ((sb : ℝ) + 1) ≤
        (c₂ : ℝ) * ((L : ℝ) + 1) ^ 3 + 2 * (ℓ_val : ℝ) + 7 := by exact_mod_cast hsb_nat
    have h2_ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hL3 : ((L : ℝ) + 1) ^ 3 ≤ ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      pow_le_pow_right₀ hL1 (le_max_left 3 (2 * e))
    have hLe : ((L : ℝ) + 1) ^ (2 * e) ≤ ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      pow_le_pow_right₀ hL1 (le_max_right 3 (2 * e))
    have h1m : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      one_le_mul_of_one_le_of_one_le h2_ge (one_le_pow₀ hL1)
    have hL3m : ((L : ℝ) + 1) ^ 3 ≤
        (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      hL3.trans (le_mul_of_one_le_left (by positivity) h2_ge)
    have hℓm : (ℓ_val : ℝ) ≤
        (2 * B_c : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) +
          1) ^ (max 3 (2 * e))) :=
      hℓ_R.trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hLe (by positivity)) (by positivity))
    dsimp only [C_sb]; push_cast
    nlinarith only [hcast, h1m, hL3m, hℓm]
  have hlt_R : (lt : ℝ) ≤
      (C_lt : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e))) := by
    have hnb_R : (nodeB : ℝ) + 1 ≤ ((c₁ + 1 : ℕ) : ℝ) * ((L : ℝ) + 1) ^ 2 := by
      have hsq : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ 2 := one_le_pow₀ hL1
      have hnb' : (nodeB : ℝ) ≤ (c₁ : ℝ) * ((L : ℝ) + 1) ^ 2 := by exact_mod_cast hnb
      push_cast; nlinarith only [hnb', hsq]
    have hnb_e : ((nodeB : ℝ) + 1) ^ e ≤
      ((c₁ + 1 : ℕ) : ℝ) ^ e * ((L : ℝ) + 1) ^ (2 * e) := by
      calc ((nodeB : ℝ) + 1) ^ e
          ≤ (((c₁ + 1 : ℕ) : ℝ) * ((L : ℝ) + 1) ^ 2) ^ e :=
            pow_le_pow_left₀ (by positivity) hnb_R e
        _ = ((c₁ + 1 : ℕ) : ℝ) ^ e * ((L : ℝ) + 1) ^ (2 * e) := by rw [mul_pow, ← pow_mul]
    have hceil_le : (⌈(2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ))⌉₊ : ℝ) ≤
        2 * (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) := by
      have h1' : (⌈(2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ))⌉₊ : ℝ) <
          (2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2' : (2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ)) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        push_cast
        have := mul_le_mul_of_nonneg_right hMs_lo (Nat.cast_nonneg N)
        nlinarith only [this]
      have h3' : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      linarith only [h1', h2', h3']
    have hlt_cast : (lt : ℝ) =
        5 * (2 * (nodeB : ℝ) + 2 * (ℓ_val : ℝ) + 4) +
          3 * ((c₀ : ℝ) * (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) *
            (⌈(2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ))⌉₊ : ℝ) *
            ((nodeB : ℝ) + 1) ^ e + (c₀ : ℝ) + 2) := by
      dsimp only [lt]; push_cast; rfl
    have h2_ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hL2 : ((L : ℝ) + 1) ^ 2 ≤ ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      pow_le_pow_right₀ hL1 (by omega)
    have hLe : ((L : ℝ) + 1) ^ (2 * e) ≤ ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      pow_le_pow_right₀ hL1 (le_max_right 3 (2 * e))
    have h1m : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      one_le_mul_of_one_le_of_one_le h2_ge (one_le_pow₀ hL1)
    have hL2m : ((L : ℝ) + 1) ^ 2 ≤
        (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e)) :=
      hL2.trans (le_mul_of_one_le_left (by positivity) h2_ge)
    have hℓm : (ℓ_val : ℝ) ≤
        (2 * B_c : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) +
          1) ^ (max 3 (2 * e))) :=
      hℓ_R.trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hLe (by positivity)) (by positivity))
    have hbig_prod : (⌈(2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ))⌉₊ : ℝ) * ((nodeB : ℝ) + 1) ^ e ≤
        2 * ((c₁ + 1 : ℕ) : ℝ) ^ e *
          ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e))) := by
      calc (⌈(2 : ℝ) ^ (δ * ((occ * N : ℕ) : ℝ))⌉₊ : ℝ) * ((nodeB : ℝ) + 1) ^ e
          ≤ (2 * (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ))) *
              (((c₁ + 1 : ℕ) : ℝ) ^ e * ((L : ℝ) + 1) ^ (2 * e)) :=
            mul_le_mul hceil_le hnb_e (by positivity) (by positivity)
        _ = 2 * ((c₁ + 1 : ℕ) : ℝ) ^ e *
              ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (2 * e)) := by ring
        _ ≤ 2 * ((c₁ + 1 : ℕ) : ℝ) ^ e *
              ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLe (by positivity))
              (by positivity)
    rw [hlt_cast]
    have hcoef_prod := mul_le_mul_of_nonneg_left hbig_prod
      (by positivity : (0 : ℝ) ≤ (c₀ : ℝ) * (⌈(2 : ℝ) ^ δ⌉₊ : ℝ))
    dsimp only [C_lt]; push_cast at hnb_R hcoef_prod ⊢
    nlinarith only [hnb_R, hL2m, hℓm, h1m, hcoef_prod]
  set B_base : ℝ := (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 3 (2 * e))
  set M_rhs : ℝ := (2 : ℝ) ^ ((((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
      ((L : ℝ) + 1) ^ (max 3 (2 * e) * max dS 1 + 2)
  have hB1 : (1 : ℝ) ≤ B_base :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
      (one_le_pow₀ hL1)
  have hM_ge : (1 : ℝ) ≤ M_rhs :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
      (one_le_pow₀ hL1)
  have hB_pow_le : B_base ^ dS ≤ M_rhs := by
    dsimp only [B_base, M_rhs]
    rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
      mul_comm ((1 / (Ms : ℝ)) * (N : ℝ)), ← mul_assoc (dS : ℝ), ← pow_mul]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hd_le : (dS : ℝ) ≤ ((max dS 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left dS 1
      nlinarith only [hd_le, show (0 : ℝ) ≤ (1 / (Ms : ℝ)) * (N : ℝ) by positivity]
    · refine pow_le_pow_right₀ hL1 ?_
      exact (Nat.mul_le_mul_left _ (le_max_left dS 1)).trans (Nat.le_add_right _ 2)
  have hB_le : B_base ≤ M_rhs := by
    have h1' : B_base = B_base ^ 1 := (pow_one B_base).symm
    have h2' : B_base ^ 1 ≤ B_base ^ (max dS 1) := pow_le_pow_right₀ hB1 (le_max_right dS 1)
    have h3' : B_base ^ (max dS 1) ≤ M_rhs := by
      dsimp only [B_base, M_rhs]
      rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
        mul_comm ((1 / (Ms : ℝ)) * (N : ℝ)), ← mul_assoc ((max dS 1 : ℕ) : ℝ), ← pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) (by positivity)
    exact (h1'.trans_le h2').trans h3'
  have hL2_le : ((L : ℝ) + 1) ^ 2 ≤ M_rhs := by
    dsimp only [M_rhs]
    exact (pow_le_pow_right₀ hL1 (by omega)).trans
      (le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) (by positivity)))
  have hsb_pow : ((sb : ℝ) + 1) ^ dS ≤ (C_sb : ℝ) ^ dS * M_rhs := by
    calc ((sb : ℝ) + 1) ^ dS
        ≤ ((C_sb : ℝ) * B_base) ^ dS := pow_le_pow_left₀ (by positivity) hsb_R dS
      _ = (C_sb : ℝ) ^ dS * B_base ^ dS := mul_pow _ _ _
      _ ≤ (C_sb : ℝ) ^ dS * M_rhs := mul_le_mul_of_nonneg_left hB_pow_le (by positivity)
  have hR_cast : (r_rnd : ℝ) =
      (cStep : ℝ) * (((sb : ℝ) + 1) ^ dS + (lt : ℝ)) + (cStep : ℝ) := by
    dsimp only [r_rnd]; push_cast; rfl
  rw [hR_cast]
  have hlt_M : (lt : ℝ) ≤ (C_lt : ℝ) * M_rhs :=
    hlt_R.trans (mul_le_mul_of_nonneg_left hB_le (by positivity))
  have hsb_M : (sb : ℝ) ≤ (C_sb : ℝ) * M_rhs := by
    have h1' := hsb_R.trans (mul_le_mul_of_nonneg_left hB_le (by positivity))
    linarith only [h1']
  have hcStep_M : (cStep : ℝ) * (((sb : ℝ) + 1) ^ dS + (lt : ℝ)) ≤
      (cStep : ℝ) * ((C_sb : ℝ) ^ dS * M_rhs + (C_lt : ℝ) * M_rhs) :=
    mul_le_mul_of_nonneg_left (add_le_add hsb_pow hlt_M) (Nat.cast_nonneg _)
  have hcStep1 : (cStep : ℝ) ≤ (cStep : ℝ) * M_rhs :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hM_ge
  dsimp only [C_rnd]; push_cast
  linarith only [hcStep_M, hcStep1, hsb_M, hcnt_R, hL2_le, hM_ge]

private theorem rp_sparsify_time_bound
    {M Ms dS dU di dBin dn dW e c₀ c₁ c₂ B_c cStep Kx occ : ℕ}
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hMε : 1 / (M : ℝ) < ε / 4)
    (hMs_lo : δ * (occ : ℝ) ≤ 1 / (Ms : ℝ))
    (hMs_hi : ((max dS (max (dU + 3) di) + 2 : ℕ) : ℝ) * (1 / (Ms : ℝ)) ≤
      ε / 2 + 2 * ((max dS (max (dU + 3) di) + 2 : ℕ) : ℝ) * (occ : ℝ) * δ)
    (hc₂ : c₂ = 4 * (Kx + 1) * (2 * c₁ + 1) + 2)
    (φ : CNF ℕ) (w : List Bool)
    (Tℓ_val : ℕ)
    (nodeB : ℕ) (hnb : nodeB ≤ c₁ * ((encCNF φ).length + 1) ^ 2)
    (hTℓ_new : Tℓ_val ≤ ((encCNF φ).length + 1) ^ dBin + (encCNF φ).length +
      (B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e) + 1) *
        ((B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e) + 1) ^ dU +
          B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e) +
          ((encNat (B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e))).length +
            1) ^ 2) + 1)
    (hw : w.length = B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e)) :
    let dMax := max dS (max (dU + 3) di)
    let c := (2 * (dMax + 2) + 4) * occ + 2
    let E_deg := max (dBin + (2 * e + 1) * (dU + 3) + 6)
      (dn + dW + (max 3 (2 * e) + 1) * (max dS di + 2) + 12)
    let ℓ_val := B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e)
    let sb := 2 * (2 * ((φ.numVars * Kx + 1) * (2 * nodeB + 1)) + 2) + 2 * ℓ_val + 4
    let lt := 5 * (2 * nodeB + 2 * ℓ_val + 4) +
      3 * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * ⌈(2 : ℝ) ^ (δ * (occ * φ.numVars : ℝ))⌉₊ *
        (nodeB + 1) ^ e + c₀ + 2)
    let r_rnd := cStep * ((sb + 1) ^ dS + lt) + cStep
    let C_sb := c₂ + 4 * B_c + 8
    let C_lt := 10 * (c₁ + 1) + 20 * B_c + 30 +
      6 * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2)
    let C_rnd := cStep * (C_sb ^ dS + C_lt) + cStep + C_sb + 25
    let C_ℓ := 6 * (2 * B_c + 1) ^ (dU + 3) + 3
    let C_all := C_ℓ + 5 * C_rnd + 4 * B_c + (2 * B_c + 3) ^ di + 12
    ((encCNF φ).length : ℝ) + (Tℓ_val : ℝ) +
      (((((encPair encCNF encBits (φ, w)).length + ((encCNF φ).length + 1) ^ dW) +
        ((((encPair encCNF encBits (φ, w)).length + ((encCNF φ).length + 1) ^ dn) +
          ((encPair encCNF encBits (φ, w)).length + 1) ^ di) +
            (Sparsify.rounds M φ + 1) *
              (r_rnd + sb + ((encNat (Sparsify.rounds M φ)).length + 1) ^ 2))) : ℕ) : ℝ) ≤
      (C_all : ℝ) * ((2 : ℝ) ^ ((ε + (c : ℝ) * δ) * (φ.numVars : ℝ)) *
        (((encCNF φ).length : ℝ) + 1) ^ E_deg) + (C_all : ℝ) := by
  intro dMax c E_deg ℓ_val sb lt r_rnd C_sb C_lt C_rnd C_ℓ C_all
  set L := (encCNF φ).length
  set N := φ.numVars
  set P : ℝ := ((L : ℝ) + 1) ^ E_deg
  set Z : ℝ := (2 : ℝ) ^ ((ε + (c : ℝ) * δ) * (N : ℝ))
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hP1 : (1 : ℝ) ≤ P := one_le_pow₀ hL1
  have hZ1 : (1 : ℝ) ≤ Z := Real.one_le_rpow (by norm_num) (by positivity)
  have hZP1 : (1 : ℝ) ≤ Z * P := one_le_mul_of_one_le_of_one_le hZ1 hP1
  have hNL : N ≤ L := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  have hP_mono : ∀ a ≤ E_deg, ((L : ℝ) + 1) ^ a ≤ P := fun a ha => pow_le_pow_right₀ hL1 ha
  have h2_ms : (2 : ℝ) ^ ((N / Ms : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]; exact Nat.cast_div_le
  have h2_m : (2 : ℝ) ^ ((N / M : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 / (M : ℝ)) * (N : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]; exact Nat.cast_div_le
  have hexp_all : (1 / (M : ℝ)) + ((dMax + 2 : ℕ) : ℝ) * (1 / (Ms : ℝ)) ≤ ε + (c : ℝ) * δ := by
    have hMs_hi' : ((dMax + 2 : ℕ) : ℝ) * (1 / (Ms : ℝ)) ≤
        ε / 2 + 2 * ((dMax + 2 : ℕ) : ℝ) * (occ : ℝ) * δ := hMs_hi
    have h1_c : 2 * ((dMax + 2 : ℕ) : ℝ) * (occ : ℝ) ≤ (c : ℝ) := by
      have : 2 * (dMax + 2) * occ ≤ c :=
        (Nat.mul_le_mul_right occ (by omega : 2 * (dMax + 2) ≤ 2 * (dMax + 2) + 4)).trans
          (Nat.le_add_right _ 2)
      exact_mod_cast this
    nlinarith only [hMε, hMs_hi', h1_c, hδ, hε]
  have h2_exp : ∀ (a b : ℕ), a ≤ 1 → b ≤ dMax + 2 →
      (2 : ℝ) ^ (((a : ℝ) * (1 / (M : ℝ)) + (b : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) ≤ Z := by
    intro a b ha hb
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have ha' : (a : ℝ) ≤ 1 := by exact_mod_cast ha
    have hb' : (b : ℝ) ≤ ((dMax + 2 : ℕ) : ℝ) := by exact_mod_cast hb
    have h1' : (a : ℝ) * (1 / (M : ℝ)) ≤ 1 / (M : ℝ) := by
      nlinarith only [ha', show (0 : ℝ) ≤ 1 / (M : ℝ) by positivity]
    have h2' : (b : ℝ) * (1 / (Ms : ℝ)) ≤ ((dMax + 2 : ℕ) : ℝ) * (1 / (Ms : ℝ)) := by
      nlinarith only [hb', show (0 : ℝ) ≤ 1 / (Ms : ℝ) by positivity]
    nlinarith only [h1', h2', show (0 : ℝ) ≤ (N : ℝ) by exact Nat.cast_nonneg N, hexp_all]
  have hℓ_nat : ℓ_val ≤ (2 * B_c) * 2 ^ (N / Ms) * (L + 1) ^ (2 * e) := by
    dsimp only [ℓ_val]
    rw [pow_succ, show B_c * (2 ^ (N / Ms) * 2) * (L + 1) ^ (2 * e) =
      2 * B_c * 2 ^ (N / Ms) * (L + 1) ^ (2 * e) by ring]
  have hℓ_R : (ℓ_val : ℝ) ≤ (2 * B_c : ℝ) * (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) *
      ((L : ℝ) + 1) ^ (2 * e) := by
    have h1' : (ℓ_val : ℝ) ≤ ((2 * B_c : ℕ) : ℝ) * ((2 ^ (N / Ms) : ℕ) : ℝ) *
        (((L + 1 : ℕ) : ℝ) ^ (2 * e)) := by exact_mod_cast hℓ_nat
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast 2] at h1'
    have h2' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2_ms (by positivity : (0 : ℝ) ≤ (2 * B_c : ℕ)))
      (by positivity : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ (2 * e))
    push_cast at h1' h2' ⊢
    exact h1'.trans h2'
  have hstep_ell : ((ℓ_val : ℝ) + 1) ≤
      ((2 * B_c + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) +
        1) ^ (2 * e)) := by
    have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (2 * e) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
        (one_le_pow₀ hL1)
    push_cast; nlinarith only [hℓ_R, hge1]
  have hpow_ell : ∀ m, m ≤ dMax + 2 → 2 * e * m ≤ E_deg →
      ((ℓ_val : ℝ) + 1) ^ m ≤ ((2 * B_c + 1 : ℕ) : ℝ) ^ m * (Z * P) := by
    intro m hm hEm
    calc ((ℓ_val : ℝ) + 1) ^ m
        ≤ (((2 * B_c + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) *
            ((L : ℝ) + 1) ^ (2 * e))) ^ m :=
          pow_le_pow_left₀ (by positivity) hstep_ell m
      _ = ((2 * B_c + 1 : ℕ) : ℝ) ^ m *
            ((2 : ℝ) ^ (((0 : ℕ) : ℝ) * (1 / (M : ℝ)) +
              (m : ℝ) * (1 / (Ms : ℝ)) |> fun x => x * (N : ℝ)) *
              ((L : ℝ) + 1) ^ (2 * e * m)) := by
          simp only [Nat.cast_zero, zero_mul, zero_add]
          rw [mul_pow, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _),
            ← Real.rpow_mul (by norm_num), mul_comm ((1 / (Ms : ℝ)) * (N : ℝ)), ← pow_mul,
            mul_assoc (m : ℝ)]
      _ ≤ ((2 * B_c + 1 : ℕ) : ℝ) ^ m * (Z * P) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (h2_exp 0 m (by omega) hm) (hP_mono _ hEm) (by positivity)
              (by positivity))
            (by positivity)
  have hTℓ_R : (Tℓ_val : ℝ) ≤ (C_ℓ : ℝ) * (Z * P) := by
    have hlen_le : (encNat ℓ_val).length + 1 ≤ 2 * (ℓ_val + 1) := by
      have := length_encNat_le_of_le_two_pow (Nat.lt_two_pow_self (n := ℓ_val)).le; omega
    have hsq_le : ((encNat ℓ_val).length + 1) ^ 2 ≤ 4 * (ℓ_val + 1) ^ 2 := by
      calc ((encNat ℓ_val).length + 1) ^ 2 ≤ (2 * (ℓ_val + 1)) ^ 2 :=
            Nat.pow_le_pow_left hlen_le 2
        _ = 4 * (ℓ_val + 1) ^ 2 := by ring
    have hp1 : (ℓ_val + 1) * (ℓ_val + 1) ^ dU ≤ (ℓ_val + 1) ^ (dU + 3) := by
      rw [mul_comm, ← pow_succ]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hp2 : (ℓ_val + 1) * ℓ_val ≤ (ℓ_val + 1) ^ (dU + 3) :=
      (show (ℓ_val + 1) * ℓ_val ≤ (ℓ_val + 1) ^ 2 by nlinarith).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hp3 : (ℓ_val + 1) * (4 * (ℓ_val + 1) ^ 2) ≤ 4 * (ℓ_val + 1) ^ (dU + 3) := by
      rw [show (ℓ_val + 1) * (4 * (ℓ_val + 1) ^ 2) = 4 * (ℓ_val + 1) ^ 3 by ring]
      exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) (by omega))
    have hnat_Tℓ : Tℓ_val ≤ (L + 1) ^ dBin + (L + 1) + 6 * (ℓ_val + 1) ^ (dU + 3) := by
      have hTℓ_new' : Tℓ_val ≤ (L + 1) ^ dBin + L +
          (ℓ_val + 1) * ((ℓ_val + 1) ^ dU + ℓ_val + ((encNat ℓ_val).length + 1) ^ 2) + 1 :=
        hTℓ_new
      have hmul_le : (ℓ_val + 1) * ((ℓ_val + 1) ^ dU + ℓ_val +
          ((encNat ℓ_val).length + 1) ^ 2) ≤ 6 * (ℓ_val + 1) ^ (dU + 3) := by
        calc (ℓ_val + 1) * ((ℓ_val + 1) ^ dU + ℓ_val + ((encNat ℓ_val).length + 1) ^ 2)
            ≤ (ℓ_val + 1) * ((ℓ_val + 1) ^ dU + ℓ_val + 4 * (ℓ_val + 1) ^ 2) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = (ℓ_val + 1) * (ℓ_val + 1) ^ dU + (ℓ_val + 1) * ℓ_val +
              (ℓ_val + 1) * (4 * (ℓ_val + 1) ^ 2) := by ring
          _ ≤ 6 * (ℓ_val + 1) ^ (dU + 3) := by omega
      omega
    have hTℓ_cast : (Tℓ_val : ℝ) ≤
      ((L : ℝ) + 1) ^ dBin + ((L : ℝ) + 1) + 6 * ((ℓ_val : ℝ) + 1) ^ (dU + 3) := by
      exact_mod_cast hnat_Tℓ
    have hterm1 : ((L : ℝ) + 1) ^ dBin ≤ Z * P :=
      (hP_mono dBin (by dsimp only [E_deg]; omega)).trans
        (le_mul_of_one_le_left (by positivity) hZ1)
    have hterm1b : ((L : ℝ) + 1) ≤ Z * P := by
      have h1 : ((L : ℝ) + 1) ^ 1 ≤ P := hP_mono 1 (by dsimp only [E_deg]; omega)
      rw [pow_one] at h1
      exact h1.trans (le_mul_of_one_le_left (by positivity) hZ1)
    have hterm2 := hpow_ell (dU + 3) (by dsimp only [dMax]; omega) (by
      have : 2 * e * (dU + 3) ≤ (2 * e + 1) * (dU + 3) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
      dsimp only [E_deg]; omega)
    dsimp only [C_ℓ]; push_cast at hterm2 ⊢
    nlinarith only [hTℓ_cast, hterm1, hterm1b, hterm2, hZP1]
  have hpair_R : ((encPair encCNF encBits (φ, w)).length : ℝ) + 1 ≤
      ((2 * B_c + 3 : ℕ) : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) *
        ((L : ℝ) + 1) ^ (max 1 (2 * e))) := by
    have hpair_nat : (encPair encCNF encBits (φ, w)).length + 1 ≤ 2 * (L + 1) + ℓ_val + 1 := by
      have hw' : w.length = ℓ_val := hw
      simp only [length_encPair, encBits, Function.Embedding.refl_apply, hw']
      change 2 * L + 1 + ℓ_val + 1 ≤ 2 * (L + 1) + ℓ_val + 1
      omega
    have hpair_cast : ((encPair encCNF encBits (φ, w)).length : ℝ) + 1 ≤
        2 * ((L : ℝ) + 1) + (ℓ_val : ℝ) + 1 := by exact_mod_cast hpair_nat
    have h2_ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hL_max1 : ((L : ℝ) + 1) ≤ ((L : ℝ) + 1) ^ (max 1 (2 * e)) := by
      simpa using pow_le_pow_right₀ hL1 (le_max_left 1 (2 * e))
    have hL_max2 : ((L : ℝ) + 1) ^ (2 * e) ≤ ((L : ℝ) + 1) ^ (max 1 (2 * e)) :=
      pow_le_pow_right₀ hL1 (le_max_right 1 (2 * e))
    have h1_max : (1 : ℝ) ≤
      (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 1 (2 * e)) :=
      one_le_mul_of_one_le_of_one_le h2_ge (one_le_pow₀ hL1)
    have hL_prod : ((L : ℝ) + 1) ≤
        (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) + 1) ^ (max 1 (2 * e)) :=
      hL_max1.trans (le_mul_of_one_le_left (by positivity) h2_ge)
    have hℓ_prod : (ℓ_val : ℝ) ≤
        (2 * B_c : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) * ((L : ℝ) +
          1) ^ (max 1 (2 * e))) :=
      hℓ_R.trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hL_max2 (by positivity)) (by positivity))
    push_cast; nlinarith only [hpair_cast, h1_max, hL_prod, hℓ_prod]
  have hrounds_R : ((Sparsify.rounds M φ : ℝ) + 1) ≤ 5 * (2 : ℝ) ^ ((1 / (M : ℝ)) * (N : ℝ)) := by
    have hr : (Sparsify.rounds M φ : ℝ) + 1 ≤ 5 * ((2 ^ (N / M) : ℕ) : ℝ) := by
      exact_mod_cast Sparsify.rounds_add_one_le M φ
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast 2] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left h2_m (by norm_num))
  have hcnt_R : (((encNat (Sparsify.rounds M φ)).length : ℝ) + 1) ^ 2 ≤
    16 * ((L : ℝ) + 1) ^ 2 := by
    have hlen_r : (encNat (Sparsify.rounds M φ)).length + 1 ≤ 4 * (L + 1) := by
      rw [Sparsify.length_encNat_rounds M φ]
      have hdiv_le : φ.numVars / M ≤ L := (Nat.div_le_self φ.numVars M).trans hNL
      omega
    have hsq : ((encNat (Sparsify.rounds M φ)).length + 1) ^ 2 ≤ 16 * (L + 1) ^ 2 := by
      calc ((encNat (Sparsify.rounds M φ)).length + 1) ^ 2 ≤ (4 * (L + 1)) ^ 2 :=
            Nat.pow_le_pow_left hlen_r 2
        _ = 16 * (L + 1) ^ 2 := by ring
    exact_mod_cast hsq
  have hR_round : (r_rnd : ℝ) + (sb : ℝ) +
      (((encNat (Sparsify.rounds M φ)).length : ℝ) + 1) ^ 2 ≤
      (C_rnd : ℝ) * ((2 : ℝ) ^ ((((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
        ((L : ℝ) + 1) ^ (max 3 (2 * e) * max dS 1 + 2)) :=
    rp_sparsify_round_bound hMs_lo hc₂ hNL hnb hℓ_R hcnt_R
  have hiter_R : ((Sparsify.rounds M φ : ℝ) + 1) *
      ((r_rnd : ℝ) + (sb : ℝ) + (((encNat (Sparsify.rounds M φ)).length : ℝ) + 1) ^ 2) ≤
      5 * (C_rnd : ℝ) * (Z * P) := by
    have hmul := mul_le_mul hrounds_R hR_round (by positivity) (by positivity)
    have hprod_le : (2 : ℝ) ^ ((1 / (M : ℝ)) * (N : ℝ)) *
        ((2 : ℝ) ^ ((((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
          ((L : ℝ) + 1) ^ (max 3 (2 * e) * max dS 1 + 2)) ≤ Z * P := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
      have hexp_eq : (1 / (M : ℝ)) * (N : ℝ) + ((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ)) * (N : ℝ) =
          (((1 : ℕ) : ℝ) * (1 / (M : ℝ)) + ((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ) := by
        simp; ring
      rw [hexp_eq]
      refine mul_le_mul (h2_exp 1 (max dS 1) le_rfl (by dsimp only [dMax]; omega))
        (hP_mono _ ?_) (by positivity) (by positivity)
      have h1' : max 3 (2 * e) * max dS 1 ≤ (max 3 (2 * e) + 1) * (max dS di + 2) := by
        have : max dS 1 ≤ max dS di + 2 := by omega
        exact Nat.mul_le_mul (Nat.le_succ _) this
      dsimp only [E_deg]; omega
    calc ((Sparsify.rounds M φ : ℝ) + 1) *
            ((r_rnd : ℝ) + (sb : ℝ) + (((encNat (Sparsify.rounds M φ)).length : ℝ) + 1) ^ 2)
        ≤ (5 * (2 : ℝ) ^ ((1 / (M : ℝ)) * (N : ℝ))) *
            ((C_rnd : ℝ) * ((2 : ℝ) ^ ((((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
              ((L : ℝ) + 1) ^ (max 3 (2 * e) * max dS 1 + 2))) := hmul
      _ = 5 * (C_rnd : ℝ) * ((2 : ℝ) ^ ((1 / (M : ℝ)) * (N : ℝ)) *
            ((2 : ℝ) ^ ((((max dS 1 : ℕ) : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
              ((L : ℝ) + 1) ^ (max 3 (2 * e) * max dS 1 + 2))) := by ring
      _ ≤ 5 * (C_rnd : ℝ) * (Z * P) := mul_le_mul_of_nonneg_left hprod_le (by positivity)
  have hpair_ZP : ((encPair encCNF encBits (φ, w)).length : ℝ) + 1 ≤
      ((2 * B_c + 3 : ℕ) : ℝ) * (Z * P) := by
    refine hpair_R.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h2_le : (2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) ≤ Z := by
      simpa using h2_exp 0 1 (by omega) (by omega)
    have hm1 : max 1 (2 * e) ≤ E_deg := by
      have h1' : max 1 (2 * e) ≤ (max 3 (2 * e) + 1) * (max dS di + 2) :=
        (show max 1 (2 * e) ≤ max 3 (2 * e) + 1 by omega).trans
          (Nat.le_mul_of_pos_right _ (by omega))
      dsimp only [E_deg]; omega
    exact mul_le_mul h2_le (hP_mono _ hm1) (by positivity) (by positivity)
  have hinit_ZP : (((encPair encCNF encBits (φ, w)).length : ℝ) + 1) ^ di ≤
      ((2 * B_c + 3 : ℕ) : ℝ) ^ di * (Z * P) := by
    calc (((encPair encCNF encBits (φ, w)).length : ℝ) + 1) ^ di
        ≤ (((2 * B_c + 3 : ℕ) : ℝ) * ((2 : ℝ) ^ ((1 / (Ms : ℝ)) * (N : ℝ)) *
            ((L : ℝ) + 1) ^ (max 1 (2 * e)))) ^ di :=
          pow_le_pow_left₀ (by positivity) hpair_R di
      _ = ((2 * B_c + 3 : ℕ) : ℝ) ^ di *
            ((2 : ℝ) ^ ((((0 : ℕ) : ℝ) * (1 / (M : ℝ)) + (di : ℝ) * (1 / (Ms : ℝ))) * (N : ℝ)) *
              ((L : ℝ) + 1) ^ (max 1 (2 * e) * di)) := by
          simp only [Nat.cast_zero, zero_mul, zero_add]
          rw [mul_pow, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _),
            ← Real.rpow_mul (by norm_num), mul_comm ((1 / (Ms : ℝ)) * (N : ℝ)),
            ← mul_assoc (di : ℝ), ← pow_mul]
      _ ≤ ((2 * B_c + 3 : ℕ) : ℝ) ^ di * (Z * P) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul (h2_exp 0 di (by omega) (by dsimp only [dMax]; omega))
              (hP_mono _ ?_) (by positivity) (by positivity)) (by positivity)
          have h1' : max 1 (2 * e) * di ≤ (max 3 (2 * e) + 1) * (max dS di + 2) :=
            Nat.mul_le_mul (by omega) (by omega)
          dsimp only [E_deg]; omega
  have hL_ZP : (L : ℝ) ≤ Z * P := by
    have h1 := hP_mono 1 (by dsimp only [E_deg]; omega)
    rw [pow_one] at h1
    have h2 : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
    exact h2.trans (h1.trans (le_mul_of_one_le_left (by positivity) hZ1))
  have hW_ZP : ((L : ℝ) + 1) ^ dW ≤ Z * P := by
    have h1 : dW ≤ E_deg := by dsimp only [E_deg]; omega
    exact (hP_mono dW h1).trans (le_mul_of_one_le_left (by positivity) hZ1)
  have hN_ZP : ((L : ℝ) + 1) ^ dn ≤ Z * P := by
    have h1 : dn ≤ E_deg := by dsimp only [E_deg]; omega
    exact (hP_mono dn h1).trans (le_mul_of_one_le_left (by positivity) hZ1)
  have hC_nn : (0 : ℝ) ≤
      (C_ℓ : ℝ) + 5 * (C_rnd : ℝ) + 4 * (B_c : ℝ) + (2 * (B_c : ℝ) + 3) ^ di + 12 := by positivity
  dsimp only [C_all]
  push_cast at hpair_ZP hinit_ZP ⊢
  linarith only [hL_ZP, hTℓ_R, hpair_ZP, hW_ZP, hN_ZP, hinit_ZP, hiter_R, hZP1, hC_nn]

/-- **One-sided `RP` sparsification** [ImpagliazzoPaturiZane2001]: for every width `k`, every
`ε > 0`, and every one-sided `RP` error bound `err ∈ [0, 1)`, there exists a constant `c` such
that for every `δ ≥ 0`, a one-sided `RP` solver for `KSAT k` running in `2 ^ (δ * m) · poly(L)`
time on formulas with `m` clauses yields a one-sided `RP` solver for `KSAT k` running in
`2 ^ ((ε + c * δ) * n) · poly(L)` time on formulas with `n` variables. -/
theorem exists_solvesWithErrorInExpTime_oneSidedRP_numVars_of_length (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) {err : ℝ} (h0 : 0 ≤ err) (h1 : err < 1) :
    ∃ c : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF
        (ErrorModel.oneSidedRP err h0 h1) List.length δ →
      SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF
        (ErrorModel.oneSidedRP err h0 h1) CNF.numVars (ε + c * δ) := by
  set K := max k 1
  have hK : 1 ≤ K := le_max_right _ _
  have hkK : k ≤ K := le_max_left _ _
  obtain ⟨M, hM⟩ := exists_nat_gt (4 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hMε : 1 / (M : ℝ) < ε / 4 := by
    rw [div_lt_iff₀ hMpos]
    have := (div_lt_iff₀ hε).mp hM
    linarith
  obtain ⟨α, hα, hcount⟩ :=
    ClauseSet.Sparsification.exists_sum_choose_le hK (ε := 1 / M) (by positivity)
  have hLB : Sparsify.LeafBound K α M := fun N => by
    have hlt : N < M * (N / M + 1) := by
      have := Nat.mod_lt N (Nat.cast_pos.mp hMpos)
      have := Nat.div_add_mod N M
      nlinarith
    have hltR : (N : ℝ) < M * ((N / M + 1 : ℕ) : ℝ) := by exact_mod_cast hlt
    have h₂ : (1 / M : ℝ) * N ≤ ((N / M + 1 : ℕ) : ℝ) := by
      rw [one_div_mul_eq_div, div_le_iff₀ hMpos]
      linarith
    exact_mod_cast (hcount N).trans
      (Real.rpow_natCast 2 _ ▸ Real.rpow_le_rpow_of_exponent_le (by norm_num) h₂)
  obtain ⟨dS, hstep_deg⟩ := RandomizedSparsify.exists_step_degree K α
  obtain ⟨dU, _, hsucc_deg⟩ := (show ComputableInPolyTime (fun m : ℕ => m + 1) encUnary encUnary by
    fun_prop).exists_degree
  obtain ⟨di, _, hi_deg⟩ := (show ComputableInPolyTime
      (fun p : CNF ℕ × List Bool => (([Sparsify.root k p.1], false), p.2))
      (encPair encCNF encBits) RandomizedSparsify.encSeededState by
    have hroot : ComputableInPolyTime (fun φ : CNF ℕ => ([Sparsify.root k φ], false))
        encCNF (encPair (encList encCNF) encBool) := by
      have hn := computableInPolyTime_normalize encNat
      unfold Sparsify.root encCNF; fun_prop
    exact (hroot.comp (ComputableInPolyTime.fst encCNF encBits)).prod
      (ComputableInPolyTime.snd encCNF encBits)).exists_degree
  set dMax : ℕ := max dS (max (dU + 3) di)
  set occ := Sparsify.occBound K α
  -- Choose `c` large enough for both the `δ * occ ≥ 1 / 2` trivial branch and the sparsified
  -- branch.
  set c : ℕ := (2 * (dMax + 2) + 4) * occ + 2
  refine ⟨c, fun δ hδ hsolver => ?_⟩
  by_cases hbig : 1 ≤ ε + (c : ℝ) * δ
  · exact (KSAT_solvesWithErrorInExpTime_one k _).mono hbig
  · -- Small-`δ` regime: `δ * occ < 1 / 2`!
    have hδ_occ_lt : δ * (occ : ℝ) < 1 / 2 := by
      have h1_c : 2 * (occ : ℝ) ≤ (c : ℝ) := by
        have : 2 * occ ≤ c := by dsimp only [c]; nlinarith
        exact_mod_cast this
      nlinarith
    -- Pick `M_s ≥ 1` with `δ * occ ≤ 1 / M_s` and `(dMax + 2) * (1 / M_s) ≤ ε / 2 + ...`!
    set γ : ℝ := max (δ * (occ : ℝ)) (ε / (8 * ((dMax + 2 : ℕ) : ℝ)))
    have hγ_pos : 0 < γ := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    obtain ⟨Ms, hMs_pos_nat, hMs_lo, hMs_hi⟩ : ∃ Ms : ℕ, 1 ≤ Ms ∧
        δ * (occ : ℝ) ≤ 1 / (Ms : ℝ) ∧
        ((dMax + 2 : ℕ) : ℝ) * (1 / (Ms : ℝ)) ≤
          ε / 2 + 2 * ((dMax + 2 : ℕ) : ℝ) * (occ : ℝ) * δ := by
      by_cases hγ_half : γ < 1 / 2
      · set Ms := ⌊1 / γ⌋₊
        have h2le : (2 : ℝ) ≤ 1 / γ := by
          rw [le_div_iff₀ hγ_pos]; linarith
        have hMs_ge2 : 2 ≤ Ms := Nat.le_floor h2le
        have hMs_le : (Ms : ℝ) ≤ 1 / γ := Nat.floor_le (by positivity)
        have hMs_gt : 1 / γ < (Ms : ℝ) + 1 := Nat.lt_floor_add_one (1 / γ)
        have hMs_pos : (0 : ℝ) < Ms := by exact_mod_cast (by omega : 0 < Ms)
        refine ⟨Ms, by omega, ?_, ?_⟩
        · have hγ_le : γ ≤ 1 / (Ms : ℝ) := by
            rw [le_div_iff₀ hMs_pos]
            have := (le_div_iff₀ hγ_pos).mp hMs_le
            linarith
          exact (le_max_left _ _).trans hγ_le
        · have hinv_le : 1 / (Ms : ℝ) ≤ 2 * γ := by
            rw [div_le_iff₀ hMs_pos]
            have h2Ms : (Ms : ℝ) + 1 ≤ 2 * (Ms : ℝ) := by
              have : (1 : ℝ) ≤ (Ms : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ms)
              linarith
            have h1 := (div_lt_iff₀ hγ_pos).mp (lt_of_lt_of_le hMs_gt h2Ms)
            linarith
          have hγ_le_sum : γ ≤ δ * (occ : ℝ) + ε / (8 * ((dMax + 2 : ℕ) : ℝ)) := by
            unfold γ; apply max_le <;> linarith [show 0 ≤ δ * (occ : ℝ) by positivity,
              show 0 ≤ ε / (8 * ((dMax + 2 : ℕ) : ℝ)) by positivity]
          have hinv2 : 1 / (Ms : ℝ) ≤ 2 * (δ * (occ : ℝ) + ε / (8 * ((dMax + 2 : ℕ) : ℝ))) :=
            hinv_le.trans (by linarith)
          have hmul := mul_le_mul_of_nonneg_left hinv2
            (by positivity : (0 : ℝ) ≤ ((dMax + 2 : ℕ) : ℝ))
          have hcancel : ((dMax + 2 : ℕ) : ℝ) * (2 * (ε / (8 * ((dMax + 2 : ℕ) : ℝ)))) = ε / 4 := by
            have hne : ((dMax + 2 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp [hne]; ring
          nlinarith [hcancel]
      · have hε_big : (4 : ℝ) * ((dMax + 2 : ℕ) : ℝ) ≤ ε := by
          have : 1 / 2 ≤ ε / (8 * ((dMax + 2 : ℕ) : ℝ)) := by
            have := not_lt.mp hγ_half
            unfold γ at this
            rcases le_max_iff.mp this with h | h
            · linarith
            · exact h
          rw [le_div_iff₀ (by positivity)] at this
          linarith
        refine ⟨1, le_rfl, by simp; linarith, ?_⟩
        simp only [Nat.cast_one, div_one, mul_one]
        have hnonneg : (0 : ℝ) ≤ 2 * ((dMax + 2 : ℕ) : ℝ) * (occ : ℝ) * δ := by positivity
        linarith
    -- Extract the underlying `(ℓ, V)` solver at rate `δ`:
    obtain ⟨e, ℓ, V, Tℓ, Sℓ, Tv, Sv, c₀, hℓ, hV, ht, hyes, hno⟩ := hsolver
    obtain ⟨cℓ, hlen_ℓ⟩ := hℓ.length_le_time
    -- Compute the leaf size bound and seed length `ℓ_new φ` in binary, then convert to unary!
    set Kx := K * base K α ^ (2 * K)
    set c₁ := (1 + Kx) * (6 * K + 1)
    set c₂ := 4 * (Kx + 1) * (2 * c₁ + 1) + 2
    set B_c : ℕ := cℓ * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2) + 1
    let ℓ_new (φ : CNF ℕ) : ℕ := B_c * 2 ^ (φ.numVars / Ms + 1) * ((encCNF φ).length + 1) ^ (2 * e)
    -- `ℓ_new` is polytime in binary (`encCNF → encNat`):
    have hℓ_new_bin : ComputableInPolyTime ℓ_new encCNF encNat := by
      have hnv : ComputableInPolyTime CNF.numVars encCNF encUnary := by
        have h := (ComputableInPolyTime.length_list encNat).comp
          SAT.computableInPolyTime_distinctVars
        have hEq : (fun φ : CNF ℕ => φ.distinctVars.length) = CNF.numVars :=
          funext fun φ => CNF.length_distinctVars φ
        change ComputableInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length) encCNF encUnary at h
        rwa [hEq] at h
      have hdiv : ComputableInPolyTime (fun φ : CNF ℕ => φ.numVars / Ms + 1) encCNF encUnary := by
        have h1 := (ComputableInPolyTime.unary_div_const Ms).comp hnv
        exact ComputableInPolyTime.unary_add.comp (h1.prod (ComputableInPolyTime.const 1))
      have hpow : ComputableInPolyTime (fun φ : CNF ℕ => 2 ^ (φ.numVars / Ms + 1)) encCNF encNat :=
        ComputableInPolyTime.binary_two_pow.comp hdiv
      have hpowL : ComputableInPolyTime (fun φ : CNF ℕ => ((encCNF φ).length + 1) ^ (2 * e))
          encCNF encNat := by
        have h1 : ComputableInPolyTime (fun φ : CNF ℕ => (encCNF φ).length) encCNF encUnary :=
          ComputableInPolyTime.encoding_length encCNF
        have h2 := ComputableInPolyTime.unary_add.comp (h1.prod (ComputableInPolyTime.const 1))
        have h3 := (ComputableInPolyTime.unary_pow (2 * e)).comp h2
        exact ComputableInPolyTime.unary_to_binary.comp h3
      exact ComputableInPolyTime.binary_mul.comp
        ((ComputableInPolyTime.binary_mul.comp
          ((ComputableInPolyTime.const B_c).prod hpow)).prod hpowL)
    -- Convert `ℓ_new` to unary via `computableInO_binary_to_unary_of_deg`:
    obtain ⟨dBin, _, hℓ_bin_deg⟩ := hℓ_new_bin.exists_degree
    obtain ⟨Tℓ_new, Sℓ_new, hℓ_new_unary, hTℓ_new⟩ :=
      computableInO_binary_to_unary_of_deg hsucc_deg hℓ_bin_deg.inO
    -- Build the padded leaf verifier `V_leaf (ψ, w) := V (ψ, rpPadTake ℓ (ψ, w))`:
    obtain ⟨Tpad, Spad, hpad, hTpad⟩ := computableInO_rpPadTake hℓ
    let V_leaf (p : CNF ℕ × List Bool) : Bool := V (p.1, rpPadTake ℓ p)
    have hV_leaf_inO := hV.comp ((ComputableInO.fst encCNF encBits).prod hpad)
    obtain ⟨cStep, hstep_inO⟩ := hstep_deg hV_leaf_inO
    -- Root + rounds:
    obtain ⟨dn, _, hn_deg⟩ := (Sparsify.computableInPolyTime_rounds M).exists_degree
    -- Bound `nodeBound` and `ℓ ψ ≤ ℓ_new φ` on all nodes of the sparsification tree of `φ`:
    let nodeBound (φ : CNF ℕ) : ℕ :=
      (φ.length + φ.numVars * Kx) * (2 * (K * (2 * (encCNF φ).length + 1)) + 1)
    let stateBound (φ : CNF ℕ) (wlen : ℕ) : ℕ :=
      2 * (2 * ((φ.numVars * Kx + 1) * (2 * nodeBound φ + 1)) + 2) + 2 * wlen + 4
    have hnb_le (φ : CNF ℕ) : nodeBound φ ≤ c₁ * ((encCNF φ).length + 1) ^ 2 := by
      have hNL : φ.numVars ≤ (encCNF φ).length :=
        φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
      have hmL : φ.length ≤ (encCNF φ).length := length_le_length_encList _ φ
      have h₁ : φ.length + φ.numVars * Kx ≤ (1 + Kx) * ((encCNF φ).length + 1) := by nlinarith
      have h₂ : 2 * (K * (2 * (encCNF φ).length + 1)) + 1 ≤
          (6 * K + 1) * ((encCNF φ).length + 1) := by nlinarith
      calc nodeBound φ ≤ ((1 + Kx) * ((encCNF φ).length + 1)) *
              ((6 * K + 1) * ((encCNF φ).length + 1)) := Nat.mul_le_mul h₁ h₂
        _ = c₁ * ((encCNF φ).length + 1) ^ 2 := by ring
    have hℓ_le_new (φ ψ : CNF ℕ) (hψ_len : ψ.length ≤ occ * φ.numVars + 1)
        (hψ_enc : (encCNF ψ).length ≤ nodeBound φ) : ℓ ψ ≤ ℓ_new φ := by
      have h1 := hlen_ℓ ψ
      rw [encUnary_apply, List.length_replicate] at h1
      have hT := ht ψ (List.replicate (ℓ ψ) false) (List.length_replicate ..)
      have hTψ : (Tℓ ψ : ℝ) + 1 ≤ (c₀ : ℝ) * (2 ^ (δ * (ψ.length : ℝ)) *
          (((encCNF ψ).length : ℝ) + 1) ^ e) + c₀ + 1 := by
        linarith [(Nat.cast_nonneg (encCNF ψ).length : (0 : ℝ) ≤ _),
          (Nat.cast_nonneg (Tv (ψ, List.replicate (ℓ ψ) false)) : (0 : ℝ) ≤ _)]
      have hpow1 : (2 : ℝ) ^ (δ * (ψ.length : ℝ)) ≤
          (2 : ℝ) ^ δ * (2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) := by
        rw [← Real.rpow_add (by norm_num)]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hle_m : (ψ.length : ℝ) ≤ (occ : ℝ) * φ.numVars + 1 := by exact_mod_cast hψ_len
        have hMs_pos : (0 : ℝ) < Ms := by exact_mod_cast (by omega : 0 < Ms)
        have hdiv_ge : (φ.numVars : ℝ) / Ms ≤ ((φ.numVars / Ms + 1 : ℕ) : ℝ) := by
          have hlt : φ.numVars < Ms * (φ.numVars / Ms + 1) := by
            have := Nat.mod_lt φ.numVars (by omega : 0 < Ms)
            have := Nat.div_add_mod φ.numVars Ms
            nlinarith
          rw [div_le_iff₀ hMs_pos]
          have : (φ.numVars : ℝ) ≤ (Ms : ℝ) * ((φ.numVars / Ms + 1 : ℕ) : ℝ) := by
            exact_mod_cast le_of_lt hlt
          linarith
        have hstep1 : δ * ((occ : ℝ) * φ.numVars) ≤ (φ.numVars : ℝ) / Ms := by
          have := mul_le_mul_of_nonneg_right hMs_lo (Nat.cast_nonneg φ.numVars)
          rw [one_div_mul_eq_div] at this
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hle_m hδ]
      have hpow2 : (((encCNF ψ).length : ℝ) + 1) ^ e ≤
          ((c₁ : ℝ) + 1) ^ e * (((encCNF φ).length : ℝ) + 1) ^ (2 * e) := by
        have hnb1 : ((encCNF ψ).length : ℝ) + 1 ≤
          ((c₁ : ℝ) + 1) * (((encCNF φ).length : ℝ) + 1) ^ 2 := by
          have h1' : (nodeBound φ : ℝ) ≤ c₁ * (((encCNF φ).length : ℝ) + 1) ^ 2 := by
            exact_mod_cast hnb_le φ
          have h2' : (1 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ 2 :=
            one_le_pow₀ (by linarith [(Nat.cast_nonneg (encCNF φ).length : (0 : ℝ) ≤ _)])
          have h3' : ((encCNF ψ).length : ℝ) ≤ (nodeBound φ : ℝ) := by exact_mod_cast hψ_enc
          linarith
        calc (((encCNF ψ).length : ℝ) + 1) ^ e
            ≤ (((c₁ : ℝ) + 1) * (((encCNF φ).length : ℝ) + 1) ^ 2) ^ e :=
              pow_le_pow_left₀ (by positivity) hnb1 e
          _ = ((c₁ : ℝ) + 1) ^ e * (((encCNF φ).length : ℝ) + 1) ^ (2 * e) := by
              rw [mul_pow, ← pow_mul]
      have hT_bound : (Tℓ ψ : ℝ) + 1 ≤
          ((c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2 : ℕ) : ℝ) *
            ((2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) *
              (((encCNF φ).length : ℝ) + 1) ^ (2 * e)) := by
        have h1' : (2 : ℝ) ^ δ ≤ (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) := Nat.le_ceil _
        have h2pow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        have hL_ge : (1 : ℝ) ≤ (((encCNF φ).length : ℝ) + 1) ^ (2 * e) :=
          one_le_pow₀ (by linarith [(Nat.cast_nonneg (encCNF φ).length : (0 : ℝ) ≤ _)])
        have hprod_ge : (1 : ℝ) ≤ (2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) *
            (((encCNF φ).length : ℝ) + 1) ^ (2 * e) :=
          one_le_mul_of_one_le_of_one_le h2pow_ge hL_ge
        have hmul1 : (c₀ : ℝ) * ((2 : ℝ) ^ (δ * (ψ.length : ℝ)) *
            (((encCNF ψ).length : ℝ) + 1) ^ e) ≤
            (c₀ : ℝ) * (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) * ((c₁ : ℝ) + 1) ^ e *
              ((2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) *
                (((encCNF φ).length : ℝ) + 1) ^ (2 * e)) := by
          have hm1 := mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
          have hm2 := mul_le_mul_of_nonneg_left hm1 (Nat.cast_nonneg c₀)
          have hm3 := mul_le_mul_of_nonneg_right h1'
            (show (0 : ℝ) ≤ (c₀ : ℝ) * ((2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) *
              (((c₁ : ℝ) + 1) ^ e * (((encCNF φ).length : ℝ) + 1) ^ (2 * e))) by positivity)
          linarith
        push_cast at hmul1 hprod_ge ⊢
        nlinarith only [hTψ, hmul1, hprod_ge]
      have hℓ_real : (ℓ ψ : ℝ) ≤ (ℓ_new φ : ℝ) := by
        have h1R : (ℓ ψ : ℝ) ≤ (cℓ : ℝ) * ((Tℓ ψ : ℝ) + 1) := by exact_mod_cast h1
        have hm := mul_le_mul_of_nonneg_left hT_bound (Nat.cast_nonneg cℓ)
        have hgoal : (cℓ : ℝ) * (((c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2 : ℕ) : ℝ) *
            ((2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) *
              (((encCNF φ).length : ℝ) + 1) ^ (2 * e))) ≤ (ℓ_new φ : ℝ) := by
          dsimp only [ℓ_new, B_c]
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
            ← Real.rpow_natCast 2]
          have hA : (cℓ : ℝ) * ((c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2 : ℕ) : ℝ) ≤
              ((cℓ * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2) + 1 : ℕ) : ℝ) := by
            push_cast; linarith
          have hR : (0 : ℝ) ≤ (2 : ℝ) ^ ((φ.numVars / Ms + 1 : ℕ) : ℝ) *
              (((encCNF φ).length : ℝ) + 1) ^ (2 * e) := by positivity
          have h1' := mul_le_mul_of_nonneg_right hA hR
          push_cast at h1' ⊢
          linarith only [h1']
        exact (h1R.trans hm).trans hgoal
      exact_mod_cast hℓ_real
    -- Now prove the `ComputableInO` bound for `V_search (φ, w) := (φ.all (·.length ≤ k)) &&
    -- seededSearch ...`:
    -- Use `hstep_inO` + `ComputableInO.iterate`, then combine with `hℓ_new_unary`!
    let V_search (p : CNF ℕ × List Bool) : Bool :=
      (p.1.all fun c => decide (c.length ≤ k)) &&
        RandomizedSparsify.seededSearch K α k M V_leaf p
    -- Error correctness on `KSAT k`:
    have hV_yes : ∀ φ ∈ KSAT k,
        (acceptCount (fun p => !V_search p) φ (ℓ_new φ) : ℝ) ≤ err * (2 : ℝ) ^ (ℓ_new φ) := by
      intro φ hφ
      obtain ⟨hw, hsat⟩ := hφ
      have hroot : Sparsify.root k φ = normalize φ :=
        ite_eq_left (List.all_eq_true.mpr fun cl hcl => decide_eq_true (hw cl hcl))
      -- Find a satisfiable leaf `ψ*` of the sparsification tree of `φ`:
      classical
      let R : BranchingRule (spThreshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
        CNF.Sparsification.rule (one_le_threshold hK hα) K
      have hnorm : Normalized K (Sparsify.root k φ) := rp_root_normalized hkK φ
      let s₀ : {ψ : CNF ℕ // Normalized K ψ} := ⟨Sparsify.root k φ, hnorm⟩
      obtain ⟨σ, hσ⟩ := hsat
      have hsat₀ : (R.toClauseSet s₀).Sat σ := by
        change (Sparsify.root k φ).toClauseSet.Sat σ
        rw [hroot, sat_toClauseSet_normalize_iff]; exact hσ
      obtain ⟨wLeaf, hwLeaf, hleaf_sat⟩ :=
        (BranchingRule.exists_isLeafWord_sat_iff (one_le_threshold hK hα) s₀ σ).mpr hsat₀
      set ψStar := (R.tree.walk s₀ wLeaf).1
      -- `ψStar` has width `≤ k`, is satisfiable, and satisfies the sparse clause and encoding
      -- bounds!
      have hψStar_sat : ψStar.Satisfiable :=
        ⟨σ, (CNF.sat_toClauseSet_iff ψStar σ).mp hleaf_sat⟩
      have hψStar_mem_root : ∀ C ∈ (Sparsify.root k φ).toClauseSet,
          ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
        intro C hC l hl
        obtain ⟨C', hC', rfl⟩ := mem_toClauseSet.mp hC
        rw [hroot] at hC'
        have hsub : normalize φ <+ φ.map dedup :=
          (reduce_sublist _).trans (dedupClauses_sublist _)
        obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC')
        rw [toFinset_dedup, List.mem_toFinset] at hl
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl⟩, rfl⟩)
      have hψStar_refine : ∀ C ∈ ψStar, ∃ D ∈ φ, C.toFinset ⊆ D.toFinset := by
        intro C hC
        obtain ⟨D', hD', hCD'⟩ := BranchingRule.refines_walk (one_le_threshold hK hα)
          hwLeaf.isNodeWord C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
        obtain ⟨D'', hD'', rfl⟩ := mem_toClauseSet.mp hD'
        change D'' ∈ Sparsify.root k φ at hD''
        rw [hroot] at hD''
        have hsub : normalize φ <+ φ.map dedup :=
          (reduce_sublist _).trans (dedupClauses_sublist _)
        obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hD'')
        exact ⟨D, hD, (toFinset_dedup D) ▸ hCD'⟩
      have hψStar_width : ∀ C ∈ ψStar, C.length ≤ k := by
        intro C hC
        obtain ⟨D, hD, hCD⟩ := hψStar_refine C hC
        rw [← List.toFinset_card_of_nodup ((R.tree.walk s₀ wLeaf).2.nodup C hC)]
        exact (Finset.card_le_card hCD).trans ((List.toFinset_card_le D).trans (hw D hD))
      have hψStar_in : ψStar ∈ KSAT k := ⟨hψStar_width, hψStar_sat⟩
      have hψStar_len : ψStar.length ≤ occ * φ.numVars + 1 := by
        rw [← Normalized.card_toClauseSet (R.tree.walk s₀ wLeaf).2]
        refine ClauseSet.Sparsification.card_le_of_sparse (one_le_threshold hK hα)
          hwLeaf.isLeaf_walk (R.tree.walk s₀ wLeaf).2.card_le φ.vars.toFinset fun C' hC' l hl => ?_
        obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
        obtain ⟨D, hD, hCD⟩ := hψStar_refine C hC
        exact List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, List.mem_toFinset.mp (hCD hl)⟩, rfl⟩)
      have hψStar_enc : (encCNF ψStar).length ≤ nodeBound φ := by
        have hcard : ψStar.length ≤ φ.length + φ.numVars * Kx := by
          have h := BranchingRule.card_walk_le hK hα s₀.2.reduced s₀.2.card_le
            φ.vars.toFinset hψStar_mem_root hwLeaf.isNodeWord
          change Finset.card (R.tree.walk s₀ wLeaf).1.toClauseSet ≤
            Finset.card s₀.1.toClauseSet + φ.vars.toFinset.card * Kx at h
          rw [Normalized.card_toClauseSet (R.tree.walk s₀ wLeaf).2,
            Normalized.card_toClauseSet s₀.2] at h
          refine h.trans (Nat.add_le_add_right ?_ _)
          change (Sparsify.root k φ).length ≤ φ.length
          rw [hroot]
          exact ((reduce_sublist _).trans (dedupClauses_sublist _)).length_le.trans
            (List.length_map _).le
        refine (length_encList_le _ ψStar (b :=
          K * (2 * (encCNF φ).length + 1)) fun C hC => ?_).trans
          (Nat.mul_le_mul_right _ hcard)
        refine (length_encList_le _ C (b := (encCNF φ).length) fun l hl => ?_).trans
          (Nat.mul_le_mul_right _ ((R.tree.walk s₀ wLeaf).2.length_le C hC))
        obtain ⟨D, hD, hCD⟩ := hψStar_refine C hC
        exact (length_le_encList_of_mem _
          (List.mem_toFinset.mp (hCD (List.mem_toFinset.mpr hl)))).trans
          (length_le_encList_of_mem _ hD)
      have hℓ_star_le : ℓ ψStar ≤ ℓ_new φ := hℓ_le_new φ ψStar hψStar_len hψStar_enc
      -- Whenever `V_leaf (ψStar, w) = true`, `V_search (φ, w) = true`!
      have himp : ∀ w : List Bool, V_leaf (ψStar, w) = true → V_search (φ, w) = true := by
        intro w hvw
        have hall : (φ.all fun c => decide (c.length ≤ k)) = true :=
          List.all_eq_true.mpr fun cl hcl => decide_eq_true (hw cl hcl)
        simp only [V_search, hall, Bool.true_and, RandomizedSparsify.seededSearch_eq]
        exact (rp_search_eq_true_iff hK hkK hα hLB (fun ψ => V_leaf (ψ, w)) φ hw).mpr
          ⟨wLeaf, hwLeaf, hvw⟩
      -- Contrapositive + `acceptCount_scale`:
      have hcnt_le : acceptCount (fun p => !V_search p) φ (ℓ_new φ) ≤
          acceptCount (fun p => !V_leaf p) ψStar (ℓ_new φ) := by
        unfold acceptCount
        refine Finset.card_le_card fun w hw_m => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true'] at hw_m ⊢
        cases hvs : V_leaf (ψStar, List.ofFn w)
        · rfl
        · exfalso; exact absurd (himp _ hvs) (by simp [hw_m])
      refine (Nat.cast_le.mpr hcnt_le).trans ?_
      refine acceptCount_scale (fun p => !V p) (fun p => !V_leaf p) ψStar hℓ_star_le ?_
        (hyes ψStar hψStar_in)
      intro u hu rest
      dsimp only [V_leaf]
      rw [rpPadTake_of_le ℓ ψStar (by simp [hu]), List.take_left' hu]
    have hV_no : ∀ φ ∈ (ofSet (KSAT k)).no,
        (acceptCount V_search φ (ℓ_new φ) : ℝ) ≤ 0 * (2 : ℝ) ^ (ℓ_new φ) := by
      intro φ hφ
      rw [zero_mul]
      have hzero : acceptCount V_search φ (ℓ_new φ) = 0 := by
        by_contra hne
        have hpos : 0 < acceptCount V_search φ (ℓ_new φ) := Nat.pos_of_ne_zero hne
        obtain ⟨w, hw_len, hw_acc⟩ := acceptCount_pos_iff.mp hpos
        simp only [V_search, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
          RandomizedSparsify.seededSearch_eq] at hw_acc
        obtain ⟨hwidth, hsrch⟩ := hw_acc
        -- Every leaf `ψ` of `φ` is unsatisfiable, hence `V_leaf (ψ, w) = false`!
        have hfalse : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) → ¬ψ.Satisfiable →
          V_leaf (ψ, w) = false := by
          intro ψ hψw hψu
          have hnoψ := hno ψ (by intro hm; exact hψu hm.2)
          simp only [ErrorModel.oneSidedRP, zero_mul] at hnoψ
          have hz : acceptCount V ψ (ℓ ψ) = 0 := Nat.eq_zero_of_le_zero (by exact_mod_cast hnoψ)
          by_contra hne
          have hpos' : 0 < acceptCount V ψ (ℓ ψ) :=
            acceptCount_pos_iff.mpr ⟨rpPadTake ℓ (ψ, w), length_rpPadTake ℓ (ψ, w),
              Bool.eq_true_of_not_eq_false hne⟩
          omega
        classical
        let R : BranchingRule (spThreshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
          CNF.Sparsification.rule (one_le_threshold hK hα) K
        have hroot : Sparsify.root k φ = normalize φ :=
          ite_eq_left (List.all_eq_true.mpr fun cl hcl => decide_eq_true (hwidth cl hcl))
        let s₀ : {ψ : CNF ℕ // Normalized K ψ} := ⟨Sparsify.root k φ, rp_root_normalized hkK φ⟩
        have hunsat : ¬ φ.Satisfiable := fun hs => hφ ⟨hwidth, hs⟩
        obtain ⟨u, hu, hgu⟩ :=
          (rp_search_eq_true_iff hK hkK hα hLB (fun ψ => V_leaf (ψ, w)) φ hwidth).mp hsrch
        have hψ_unsat : ¬ (R.tree.walk s₀ u).1.Satisfiable := by
          rintro ⟨σ, hσ⟩
          have hsat_u : (R.toClauseSet (R.tree.walk s₀ u)).Sat σ :=
            (CNF.sat_toClauseSet_iff _ σ).mpr hσ
          have hsat₀ := (BranchingRule.exists_isLeafWord_sat_iff (one_le_threshold hK hα) s₀ σ).mp
            ⟨u, hu, hsat_u⟩
          have hsat_φ : φ.eval σ = true := by
            change (Sparsify.root k φ).toClauseSet.Sat σ at hsat₀
            rwa [hroot, sat_toClauseSet_normalize_iff] at hsat₀
          exact hunsat ⟨σ, hsat_φ⟩
        have hψ_width : ∀ C ∈ (R.tree.walk s₀ u).1, C.length ≤ k := by
          intro C hC
          obtain ⟨D', hD', hCD'⟩ := BranchingRule.refines_walk (one_le_threshold hK hα)
            hu.isNodeWord C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
          obtain ⟨D'', hD'', rfl⟩ := mem_toClauseSet.mp hD'
          change D'' ∈ Sparsify.root k φ at hD''
          rw [hroot] at hD''
          have hsub : normalize φ <+ φ.map dedup :=
            (reduce_sublist _).trans (dedupClauses_sublist _)
          obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hD'')
          rw [← List.toFinset_card_of_nodup ((R.tree.walk s₀ u).2.nodup C hC)]
          exact (Finset.card_le_card ((toFinset_dedup D) ▸ hCD')).trans
            ((List.toFinset_card_le D).trans (hwidth D hD))
        have hfl := hfalse _ hψ_width hψ_unsat
        rw [hgu] at hfl
        exact Bool.noConfusion hfl
      simp [hzero]
    -- Finally, assemble the `ComputableInO` runtime bound for `V_search` and package
    -- `SolvesWithErrorInExpTime`!
    classical
    let R_rule : BranchingRule (spThreshold K α) ℕ {ψ : CNF ℕ // Normalized K ψ} :=
      CNF.Sparsification.rule (one_le_threshold hK hα) K
    have hnorm_root : ∀ φ : CNF ℕ, Normalized K (Sparsify.root k φ) := rp_root_normalized hkK
    have htraj := rp_seeded_traj hK hkK hα V_leaf
    -- Bound leaf time on `p = (φ, w)` for `w.length = ℓ_new φ`:
    let leafTime (p : CNF ℕ × List Bool) : ℕ :=
      5 * (2 * nodeBound p.1 + 2 * p.2.length + 4) +
        3 * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * ⌈(2 : ℝ) ^ (δ * (occ * p.1.numVars : ℝ))⌉₊ *
          (nodeBound p.1 + 1) ^ e + c₀ + 2)
    have hV_leaf_time : ∀ (φ ψ : CNF ℕ) (w : List Bool),
        ψ.length ≤ occ * φ.numVars + 1 → (encCNF ψ).length ≤ nodeBound φ →
        (encPair encCNF encBits (ψ, w)).length + Tpad (ψ, w) +
          Tv (ψ, rpPadTake ℓ (ψ, w)) ≤ leafTime (φ, w) := by
      intro φ ψ w hlen henc
      have htp := hTpad (ψ, w)
      have hpair : (encPair encCNF encBits (ψ, w)).length ≤ 2 * nodeBound φ + 2 * w.length + 4 := by
        simp only [length_encPair, encBits, Function.Embedding.refl_apply]; omega
      have htv := ht ψ (rpPadTake ℓ (ψ, w)) (length_rpPadTake ℓ (ψ, w))
      have htv_nat : Tℓ ψ + Tv (ψ, rpPadTake ℓ (ψ, w)) ≤
          c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * ⌈(2 : ℝ) ^ (δ * (occ * φ.numVars : ℝ))⌉₊ *
            (nodeBound φ + 1) ^ e + c₀ + 1 := by
        have hpow : (2 : ℝ) ^ (δ * (ψ.length : ℝ)) ≤
            (⌈(2 : ℝ) ^ δ⌉₊ : ℝ) * (⌈(2 : ℝ) ^ (δ * (occ * φ.numVars : ℝ))⌉₊ : ℝ) := by
          have h1' : (2 : ℝ) ^ (δ * (ψ.length : ℝ)) ≤
              (2 : ℝ) ^ δ * (2 : ℝ) ^ (δ * (occ * φ.numVars : ℝ)) := by
            rw [← Real.rpow_add (by norm_num)]
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            have : (ψ.length : ℝ) ≤ (occ : ℝ) * φ.numVars + 1 := by exact_mod_cast hlen
            nlinarith only [this, hδ]
          exact h1'.trans
            (mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity))
        have hnb_p : (((encCNF ψ).length : ℝ) + 1) ^ e ≤ ((nodeBound φ : ℝ) + 1) ^ e :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right henc 1) e
        have hR : ((Tℓ ψ + Tv (ψ, rpPadTake ℓ (ψ, w)) : ℕ) : ℝ) ≤
            ((c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * ⌈(2 : ℝ) ^ (δ * (occ * φ.numVars : ℝ))⌉₊ *
              (nodeBound φ + 1) ^ e + c₀ + 1 : ℕ) : ℝ) := by
          have hm1 := mul_le_mul hpow hnb_p (by positivity) (by positivity)
          have hm2 := mul_le_mul_of_nonneg_left hm1 (Nat.cast_nonneg c₀)
          have hlen_nn : (0 : ℝ) ≤ (encCNF ψ).length := Nat.cast_nonneg _
          push_cast at hm2 ⊢
          linarith only [htv, hm2, hlen_nn]
        exact_mod_cast hR
      dsimp only [leafTime] at htp ⊢
      omega
    -- Apply `ComputableInO.iterate` to `seededStep`:
    let R_round (p : CNF ℕ × List Bool) : ℕ :=
      cStep * ((stateBound p.1 p.2.length + 1) ^ dS + leafTime p) + cStep
    have henc_walk : ∀ (φ : CNF ℕ) (t : {ψ : CNF ℕ // Normalized K ψ}) (u : List Bool),
        R_rule.tree.IsNodeWord ⟨Sparsify.root k φ, hnorm_root φ⟩ u →
        R_rule.tree.walk ⟨Sparsify.root k φ, hnorm_root φ⟩ u = t →
        (encCNF t.1).length ≤ nodeBound φ := by
      intro φ t u hu hwalk
      set s_t := R_rule.tree.walk ⟨Sparsify.root k φ, hnorm_root φ⟩ u
      have hst : t = s_t := hwalk.symm
      subst hst
      have hnorm_r : Normalized K (Sparsify.root k φ) := hnorm_root φ
      have hcard : s_t.1.length ≤ φ.length + φ.numVars * Kx := by
        have h1 := BranchingRule.card_walk_le hK hα hnorm_r.reduced hnorm_r.card_le
          φ.vars.toFinset (by
            intro C hC l hl
            obtain ⟨C', hC', rfl⟩ := mem_toClauseSet.mp hC
            unfold Sparsify.root at hC'; split_ifs at hC'
            · have hsub : normalize φ <+ φ.map dedup :=
                (reduce_sublist _).trans (dedupClauses_sublist _)
              obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC')
              rw [toFinset_dedup, List.mem_toFinset] at hl
              exact List.mem_toFinset.mpr
                (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl⟩, rfl⟩)
            · simp at hC') hu
        change Finset.card s_t.1.toClauseSet ≤
          Finset.card (Sparsify.root k φ).toClauseSet + φ.vars.toFinset.card * Kx at h1
        rw [Normalized.card_toClauseSet s_t.2] at h1
        refine h1.trans (Nat.add_le_add_right ?_ _)
        rw [Normalized.card_toClauseSet hnorm_r]
        unfold Sparsify.root; split_ifs
        · exact ((reduce_sublist _).trans (dedupClauses_sublist _)).length_le.trans
            (List.length_map _).le
        · exact Nat.zero_le _
      refine (length_encList_le _ s_t.1 (b := K * (2 * (encCNF φ).length + 1)) fun C hC => ?_).trans
        (Nat.mul_le_mul_right _ hcard)
      refine (length_encList_le _ C (b := (encCNF φ).length) fun l hl => ?_).trans
        (Nat.mul_le_mul_right _ (s_t.2.length_le C hC))
      obtain ⟨D', hD', hCD'⟩ := BranchingRule.refines_walk (one_le_threshold hK hα) hu
        C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
      obtain ⟨D'', hD'', rfl⟩ := mem_toClauseSet.mp hD'
      unfold Sparsify.root at hD''; split_ifs at hD''
      · have hsub : normalize φ <+ φ.map dedup :=
          (reduce_sublist _).trans (dedupClauses_sublist _)
        obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hD'')
        exact (length_le_encList_of_mem _
          (List.mem_toFinset.mp (((toFinset_dedup D) ▸ hCD') (List.mem_toFinset.mpr hl)))).trans
          (length_le_encList_of_mem _ hD)
      · simp at hD''
    have hstate_le : ∀ p : CNF ℕ × List Bool, ∀ i ≤ Sparsify.rounds M p.1,
        (RandomizedSparsify.encSeededState
          ((RandomizedSparsify.seededStep K α V_leaf)^[i]
            (([Sparsify.root k p.1], false), p.2))).length ≤ stateBound p.1 p.2.length := by
      intro p i _
      obtain ⟨stk, acc, heq, hstk, hmem⟩ := htraj p.1 p.2 i
      rw [heq]
      have hlen_stk : (encList encCNF (stk.map Subtype.val)).length ≤
          (p.1.numVars * Kx + 1) * (2 * nodeBound p.1 + 1) := by
        have h := length_encList_le encCNF (stk.map Subtype.val) (b := nodeBound p.1) fun ψ hψ => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hψ
          obtain ⟨u, hu, hwalk⟩ := hmem t ht
          exact henc_walk p.1 t u hu hwalk
        rw [List.length_map] at h
        exact h.trans (Nat.mul_le_mul_right _ hstk)
      simp only [RandomizedSparsify.encSeededState, length_encPair, encBool_apply,
        List.length_singleton, encBits, Function.Embedding.refl_apply, stateBound]
      omega
    have hround_le : ∀ p : CNF ℕ × List Bool, ∀ i ≤ Sparsify.rounds M p.1,
        (let s := (RandomizedSparsify.seededStep K α V_leaf)^[i] (([Sparsify.root k p.1], false),
          p.2)
         cStep * (((RandomizedSparsify.encSeededState s).length + 1) ^ dS +
          if s.1.1.isEmpty = false ∧ isSparse (spThreshold K α) K (s.1.1.headD []) = true then
            ((encPair encCNF encBits (s.1.1.headD [], s.2)).length +
              Tpad (s.1.1.headD [], s.2)) +
              Tv (s.1.1.headD [], rpPadTake ℓ (s.1.1.headD [], s.2))
          else 0) + cStep) ≤ R_round p := by
      intro p i hi
      have hS := hstate_le p i hi
      dsimp only [R_round]
      refine Nat.add_le_add_right (Nat.mul_le_mul_left cStep (Nat.add_le_add
        (Nat.pow_le_pow_left (by omega) dS) ?_)) cStep
      split_ifs with hc
      · obtain ⟨stk, acc, heq, hstk, hmem⟩ := htraj p.1 p.2 i
        rw [heq] at hc ⊢
        cases stk with
        | nil => simp at hc
        | cons s rest =>
          obtain ⟨u, hu, hwalk⟩ := hmem s List.mem_cons_self
          simp only [List.map_cons, List.headD_cons] at hc ⊢
          have hsp := (isSparse_eq_true_iff (one_le_threshold hK hα) s.2).mp hc.2
          have hlen_s : s.1.length ≤ occ * p.1.numVars + 1 := by
            rw [← Normalized.card_toClauseSet s.2]
            refine ClauseSet.Sparsification.card_le_of_sparse (one_le_threshold hK hα) hsp
              s.2.card_le p.1.vars.toFinset fun C' hC' l hl => ?_
            obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
            rw [← hwalk] at hC
            obtain ⟨D', hD', hCD'⟩ := BranchingRule.refines_walk (one_le_threshold hK hα) hu
              C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
            obtain ⟨D'', hD'', rfl⟩ := mem_toClauseSet.mp hD'
            unfold Sparsify.root at hD''; split_ifs at hD''
            · have hsub : normalize p.1 <+ p.1.map dedup :=
                (reduce_sublist _).trans (dedupClauses_sublist _)
              obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hD'')
              exact List.mem_toFinset.mpr (List.mem_map.mpr
                ⟨l, List.mem_flatten.mpr ⟨D, hD,
                  List.mem_toFinset.mp (((toFinset_dedup D) ▸ hCD') hl)⟩, rfl⟩)
            · simp at hD''
          exact hV_leaf_time p.1 s.1 p.2 hlen_s (henc_walk p.1 s u hu hwalk)
      · exact Nat.zero_le _
    have hsearch_inO :=
      ((ComputableInO.iterate (hn_deg.inO.comp (ComputableInO.fst encCNF encBits))
        hi_deg.inO hstep_inO hround_le
        (fun p i hi => Finset.le_sup (f := fun i =>
          let hstep_s := (RandomizedSparsify.seededStep K α V_leaf)^[i]
            (([Sparsify.root k p.1], false), p.2)
          cStep * (((RandomizedSparsify.encSeededState hstep_s).length + 1) ^ dS +
            if (hstep_s.1.1.isEmpty = false) ∧
              isSparse (spThreshold K α) K (hstep_s.1.1.headD []) = true then
              ((encPair encCNF encBits (hstep_s.1.1.headD [], hstep_s.2)).length +
                Spad (hstep_s.1.1.headD [], hstep_s.2)) +
                Sv (hstep_s.1.1.headD [], rpPadTake ℓ (hstep_s.1.1.headD [], hstep_s.2))
            else 0) + cStep) (Finset.mem_Iic.mpr hi)) hstate_le).fst').snd'
    -- Combine with `φ.all (·.length ≤ k)` using a linear finite Boolean conjunction:
    obtain ⟨dW, _, hW_deg⟩ := (computableInPolyTime_all_length_le k).exists_degree
    have hV_search_inO :=
      (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
        fun q : Bool × Bool => q.1 && q.2).inO_one.comp_linear
      ((hW_deg.inO.comp (ComputableInO.fst encCNF encBits)).prod hsearch_inO)
    -- Bound total time `(encCNF φ).length + Tℓ_new φ + Tv_search (φ, w)` by `C * 2^((ε + c*δ)*n) *
    -- (L+1)^E`!
    set E_deg : ℕ :=
      max (dBin + (2 * e + 1) * (dU + 3) + 6)
        (dn + dW + (max 3 (2 * e) + 1) * (max dS di + 2) + 12)
    set C_sb : ℕ := c₂ + 4 * B_c + 8
    set C_lt : ℕ :=
      10 * (c₁ + 1) + 20 * B_c + 30 + 6 * (c₀ * ⌈(2 : ℝ) ^ δ⌉₊ * (c₁ + 1) ^ e + c₀ + 2)
    set C_rnd : ℕ := cStep * (C_sb ^ dS + C_lt) + cStep + C_sb + 25
    set C_ℓ : ℕ := 6 * (2 * B_c + 1) ^ (dU + 3) + 3
    set C_all : ℕ := C_ℓ + 5 * C_rnd + 4 * B_c + (2 * B_c + 3) ^ di + 12
    refine ⟨E_deg, ℓ_new, V_search, Tℓ_new, Sℓ_new, _, _, C_all, hℓ_new_unary, hV_search_inO,
      fun φ w hw => ?_, hV_yes, hV_no⟩
    have hres := rp_sparsify_time_bound (dS := dS) (dU := dU) (di := di) (dBin := dBin)
      (dn := dn) (dW := dW) (e := e) (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (B_c := B_c)
      (cStep := cStep) (Kx := Kx) (occ := occ) hε hδ hMε hMs_lo hMs_hi rfl φ w (Tℓ_new φ)
      (nodeBound φ) (hnb_le φ) (hTℓ_new φ) hw
    dsimp only at hres
    convert hres using 1
    simp only [R_round, stateBound, leafTime, Function.comp_apply, hw, ℓ_new]

/-- Subexponential one-sided `RP` time in clauses gives subexponential one-sided `RP` time in
variables. -/
theorem SolvesWithErrorInSubexpTime.oneSidedRP_numVars_of_length {k : ℕ} {err : ℝ}
    (h0 : 0 ≤ err) (h1 : err < 1)
    (h : SolvesWithErrorInSubexpTime (ofSet (KSAT k)) encCNF
      (ErrorModel.oneSidedRP err h0 h1) List.length) :
    SolvesWithErrorInSubexpTime (ofSet (KSAT k)) encCNF
      (ErrorModel.oneSidedRP err h0 h1) CNF.numVars := by
  intro δ hδ
  obtain ⟨c, hc⟩ :=
    exists_solvesWithErrorInExpTime_oneSidedRP_numVars_of_length k (half_pos hδ) h0 h1
  have hδ' : 0 < δ / 2 / (c + 1) := by positivity
  refine (hc _ hδ'.le (h _ hδ')).mono ?_
  have hle := natCast_mul_div_add_one_le (half_pos hδ).le c
  linarith

/-- Under `rETH`, `ThreeSAT` admits no subexponential one-sided `RP` solver in the number of
clauses. -/
theorem rETH.not_solvesWithErrorInSubexpTime_oneSidedRP_length (hrETH : rETH) {err : ℝ}
    (h0 : 0 < err) (h1 : err < 1) :
    ¬SolvesWithErrorInSubexpTime (ofSet ThreeSAT) encCNF
      (ErrorModel.oneSidedRP err h0.le h1) List.length := by
  intro hsub
  have hvars : SolvesWithErrorInSubexpTime (ofSet (KSAT 3)) encCNF
      (ErrorModel.oneSidedRP err h0.le h1) CNF.numVars := by
    rw [KSAT_three]
    exact hsub.oneSidedRP_numVars_of_length h0.le h1
  have hrp0 : rpSatExponent 3 = 0 := by
    apply le_antisymm _ (rpSatExponent_nonneg 3)
    apply le_of_forall_pos_le_add
    intro δ hδ
    rw [zero_add]
    have hδ' : SolvesWithErrorInExpTime (ofSet (KSAT 3)) encCNF ErrorModel.rp CNF.numVars δ := by
      have := (solvesWithErrorInExpTime_oneSidedRP_iff h0 h1
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mp (hvars δ hδ)
      exact this
    exact rpSatExponent_le hδ.le hδ'
  have hr0 : rSatExponent 3 ≤ 0 := hrp0 ▸ rSatExponent_le_rpSatExponent 3
  have hpos : 0 < rSatExponent 3 := rETH_iff_rSatExponent_pos.mp hrETH
  linarith

/-- Under `rETH`, `ThreeColoring` admits no subexponential one-sided `RP` solver in `|V| + |E|`. -/
theorem rETH.not_solvesWithErrorInSubexpTime_oneSidedRP_ThreeColoring (hrETH : rETH) {err : ℝ}
    (h0 : 0 < err) (h1 : err < 1) :
    ¬SolvesWithErrorInSubexpTime (ofSet ThreeColoring) encGraph
      (ErrorModel.oneSidedRP err h0.le h1) (fun G => G.vertices.length + G.edges.length) := by
  intro hcol
  apply hrETH.not_solvesWithErrorInSubexpTime_oneSidedRP_length h0 h1
  -- Compose `SAT.toThreeColoring` (width-3 clauses only; handle non-width-3 via `KSAT_of_le`-style
  -- filter):
  let red (φ : CNF ℕ) : Graph :=
    if φ.all (fun c => decide (c.length ≤ 3)) then SAT.toThreeColoring φ
    else ⟨[0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩
  have hred_poly : ComputableInPolyTime red encCNF encGraph :=
    (computableInPolyTime_all_length_le 3).ite SAT.computableInPolyTime_toThreeColoring
      (ComputableInPolyTime.const _)
  have hred_mem : ∀ φ, φ ∈ ThreeSAT ↔ red φ ∈ ThreeColoring := by
    intro φ
    dsimp only [red]
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      have h3 : φ ∈ ThreeSAT ↔ φ ∈ SAT := by
        change (φ ∈ KSAT 3) ↔ φ ∈ SAT
        exact ⟨And.right, And.intro hw⟩
      rw [h3, ← SAT.toThreeColoring_mem_iff φ]
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      constructor
      · intro h; exact absurd h.1 hw
      · intro hK4
        -- `K4` is not 3-colorable!
        exfalso
        rw [mem_KColoring_iff] at hK4
        obtain ⟨f, hlt, hf⟩ := hK4
        have h0lt : f 0 < 3 := hlt 0 (by simp)
        have h1lt : f 1 < 3 := hlt 1 (by simp)
        have h2lt : f 2 < 3 := hlt 2 (by simp)
        have h3lt : f 3 < 3 := hlt 3 (by simp)
        have h01 : f 0 ≠ f 1 :=
          hf 0 (by simp) 1 (by simp) (Graph.toSimpleGraph_adj.mpr ⟨by omega, by simp⟩)
        have h02 : f 0 ≠ f 2 :=
          hf 0 (by simp) 2 (by simp) (Graph.toSimpleGraph_adj.mpr ⟨by omega, by simp⟩)
        have h03 : f 0 ≠ f 3 :=
          hf 0 (by simp) 3 (by simp) (Graph.toSimpleGraph_adj.mpr ⟨by omega, by simp⟩)
        have h12 : f 1 ≠ f 2 :=
          hf 1 (by simp) 2 (by simp) (Graph.toSimpleGraph_adj.mpr ⟨by omega, by simp⟩)
        have h13 : f 1 ≠ f 3 :=
          hf 1 (by simp) 3 (by simp) (Graph.toSimpleGraph_adj.mpr ⟨by omega, by simp⟩)
        have h23 : f 2 ≠ f 3 :=
          hf 2 (by simp) 3 (by simp) (Graph.toSimpleGraph_adj.mpr ⟨by omega, by simp⟩)
        omega
  have hred_size : ∀ φ, (red φ).vertices.length + (red φ).edges.length ≤ 93 * φ.length + 93 := by
    intro φ; dsimp only [red]
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      have := SAT.length_toThreeColoring_le hw
      nlinarith
    · simp
  exact hcol.of_promiseReduction hred_poly
    (fun φ hφ => (hred_mem φ).mp hφ)
    (fun φ hφ hm => hφ ((hred_mem φ).mpr hm)) hred_size

end Cslib.Complexity
