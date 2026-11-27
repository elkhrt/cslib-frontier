/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ApproximationSchemes
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Probabilistic.Sampling
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Parameterized Approximation Schemes and Marx's Bounded-Optimum Reduction

This module develops deterministic and randomized fixed-parameter tractable approximation schemes
(`FPT-AS`) for `Cslib.Complexity.NPOptimizationProblem` instances under standard Lean axioms,
:

1. **Exact FPT optimization and deterministic `FPT-AS` (`ParamAS`)**:
   - `Cslib.Complexity.ExactFPT`: existence of an FPT-time solver returning an optimal
     feasible solution on every instance.
   - `Cslib.Complexity.ParamAS`: existence of an FPT-time solver `solve (k, a)` (with respect
     to `Nat.pair k (κ a)`) achieving `1 / k` multiplicative accuracy `P.IsApproximate k a`.
   - `Cslib.Complexity.ExactFPT.toParamAS`, `Cslib.Complexity.ParamAS.of_fptas`, and
     `Cslib.Complexity.ParamAS.exists_fpt_solver`.
2. **Randomized `FPT-AS` in expectation (`RandParamAS`)**:
   - `Cslib.Complexity.ComputableInRandFPTTime`: fair-coin randomized algorithms running in
     FPT time via an FPT-computable unary coin budget and deterministic FPT evaluator.
   - `Cslib.Complexity.IsApproximateInExpectation` and
     `Cslib.Complexity.RandParamAS`, together with
     `Cslib.Complexity.ParamAS.toRandParamAS` and real-`ε` `(1 - ε)`-approximation
     `Cslib.Complexity.RandParamAS.exists_fpt_eps_approx`.
3. **Marx's bounded-optimum decision reduction (`ParamAS.boundedOpt_mem_fpt`)**:
   - `Cslib.Complexity.computableInFPTTime_binaryToUnary`: converting a binary natural `t` to
     unary `encUnary` is computable in FPT time parameterized by `t`.
   - `Cslib.Complexity.ParamAS.boundedOpt_mem_fpt`: if a maximization NP optimization problem
     admits a deterministic `ParamAS` for parameter `κ`, then deciding whether the optimum is at
     least `t` lies in `FPT` parameterized by `Nat.pair (κ a) t`.

## Main definitions

* `Cslib.Complexity.ExactFPT`: exact optimization in FPT time.
* `Cslib.Complexity.ParamAS`: deterministic parameterized approximation scheme (`FPT-AS`).
* `Cslib.Complexity.ComputableInRandFPTTime`: fair-coin randomized FPT-time computability.
* `Cslib.Complexity.IsApproximateInExpectation`: multiplicative `1 / k` approximation in
  expectation over a discrete distribution `PMF β`.
* `Cslib.Complexity.RandParamAS`: randomized parameterized approximation scheme.

## Main results

* `Cslib.Complexity.computableInFPTTime_binaryToUnary`
* `Cslib.Complexity.tsum_eval_map_sampleList`
* `Cslib.Complexity.ExactFPT.toParamAS`, `Cslib.Complexity.ParamAS.of_fptas`,
  `Cslib.Complexity.ParamAS.exists_fpt_solver`, `Cslib.Complexity.ParamAS.toRandParamAS`
* `Cslib.Complexity.RandParamAS.exists_fpt_eps_approx`
* `Cslib.Complexity.ParamAS.boundedOpt_mem_fpt`
-/

public section

open Cslib Cslib.Complexity Turing.MultiTapeTM

namespace Cslib.Complexity

/-! ### 1. Binary-to-Unary Conversion in Parameterized Time -/

/-- Converting a binary-encoded natural number `t` (`encNat`) to unary (`encUnary`) is computable
in FPT time parameterized by `t` itself (`κ = id`). -/
theorem computableInFPTTime_binaryToUnary :
    ComputableInFPTTime (id : ℕ → ℕ) encNat encUnary id := by
  obtain ⟨dn, _, hn⟩ := (ComputableInPolyTime.id' (encIn := encNat)).exists_degree
  obtain ⟨di, _, hi⟩ := (ComputableInPolyTime.const (encIn := encNat)
    (encOut := encUnary) 0).exists_degree
  obtain ⟨ds, _, hs⟩ := ComputableInDegree.unary_succ.computableInPolyTime.exists_degree
  have hiter_eq (k : ℕ) : (fun m : ℕ ↦ m + 1)^[k] 0 = k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]
  have hround (x k : ℕ) (hk : k ≤ x) :
      ((encUnary ((fun m : ℕ ↦ m + 1)^[k] 0)).length + 1) ^ ds ≤ (x + 1) ^ ds := by
    rw [hiter_eq, encUnary_apply, List.length_replicate]
    exact Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) ds
  have hstate (x k : ℕ) (hk : k ≤ x) :
      (encUnary ((fun m : ℕ ↦ m + 1)^[k] 0)).length ≤ x := by
    rw [hiter_eq, encUnary_apply, List.length_replicate]
    exact hk
  have hO := ComputableInO.iterate hn.inO hi.inO hs.inO hround hround hstate
  have hO' : ComputableInO (id : ℕ → ℕ) encNat encUnary
      (fun x ↦ (3 + (x + 1) * ((x + 1) ^ ds + x + 1)) *
        ((encNat x).length + 1) ^ (dn + di + 2))
      (fun x ↦ (3 + (x + 1) * ((x + 1) ^ ds + x + 1)) *
        ((encNat x).length + 1) ^ (dn + di + 2)) := by
    refine (hO.of_enc_eq fun x ↦ by rw [hiter_eq]; rfl).mono_le (fun x ↦ ?_) (fun x ↦ ?_)
    · set L := (encNat x).length + 1
      have hLdn : L ^ dn ≤ L ^ (dn + di + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hLdi : L ^ di ≤ L ^ (dn + di + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hL2 : L ^ 2 ≤ L ^ (dn + di + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hL1 : 1 ≤ L ^ (dn + di + 2) :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hm1 := Nat.mul_le_mul_left ((x + 1) * ((x + 1) ^ ds + x)) hL1
      have hm2 := Nat.mul_le_mul_left (x + 1) hL2
      nlinarith
    · set L := (encNat x).length + 1
      have hLdn : L ^ dn ≤ L ^ (dn + di + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hLdi : L ^ di ≤ L ^ (dn + di + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hL1 : (encNat x).length ≤ L ^ (dn + di + 2) :=
        (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
      have h1 : 1 ≤ L ^ (dn + di + 2) := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hm1 := Nat.mul_le_mul_left ((x + 1) ^ ds + x + x) h1
      rw [Nat.mul_one] at hm1
      have hx_le : (x + 1) ^ ds + x + x ≤ (x + 1) * ((x + 1) ^ ds + x + 1) := by
        have := Nat.zero_le (x * (x + 1) ^ ds)
        nlinarith
      have hm2 := Nat.mul_le_mul_right (L ^ (dn + di + 2)) hx_le
      rw [Nat.add_mul]
      omega
  exact hO'.computableInFPTTime (F := fun k ↦ 3 + (k + 1) * ((k + 1) ^ ds + k + 1))
    (c := dn + di + 2)

/-! ### 2. Exact FPT Solvers and Deterministic Parameterized Approximation Schemes -/

/-- An NP optimization problem `P` is solvable **exactly in FPT time** (`ExactFPT P κ`) with
respect to parameter `κ` if some FPT-time function outputs an optimal feasible solution for every
instance. -/
@[expose]
def ExactFPT {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (P : NPOptimizationProblem encI encS) (κ : α → ℕ) : Prop :=
  ∃ solve : α → β,
    ComputableInFPTTime solve encI encS κ ∧
    ∀ a : α, P.Feasible a (solve a) ∧
      ∀ other : β, P.Feasible a other →
        match P.goal with
        | .minimize => P.value (a, solve a) ≤ P.value (a, other)
        | .maximize => P.value (a, other) ≤ P.value (a, solve a)

/-- A deterministic **parameterized approximation scheme** (`FPT-AS`, `ParamAS P κ`) for an NP
optimization problem `P` and parameter `κ : α → ℕ` computes a `1 / k`-approximate feasible solution
on `(k, a)` in FPT time parameterized by `Nat.pair k (κ a)`. -/
@[expose]
def ParamAS {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (P : NPOptimizationProblem encI encS) (κ : α → ℕ) : Prop :=
  ∃ solve : ℕ × α → β,
    ComputableInFPTTime solve (encPair encUnary encI) encS (fun p ↦ Nat.pair p.1 (κ p.2)) ∧
    ∀ k : ℕ, 0 < k → ∀ a : α, P.IsApproximate k a (solve (k, a))

/-- Every exact FPT optimization algorithm yields a deterministic `FPT-AS` (`ParamAS`). -/
theorem ExactFPT.toParamAS {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {P : NPOptimizationProblem encI encS} {κ : α → ℕ} (h : ExactFPT P κ) :
    ParamAS P κ := by
  obtain ⟨solve, hsolve, hopt⟩ := h
  refine ⟨fun p ↦ solve p.2, ?_, fun k _ a ↦ ?_⟩
  · exact hsolve.comp ((ComputableInPolyTime.snd encUnary encI).computableInFPTTime _)
      (h := fun z ↦ (Nat.unpair z).2) (by
        intro p
        simp [Nat.unpair_pair])
  · obtain ⟨hfeas, hbest⟩ := hopt a
    refine ⟨hfeas, fun other hother ↦ ?_⟩
    have hb := hbest other hother
    cases hgoal : P.goal <;> rw [hgoal] at hb
    · calc
        k * P.value (a, solve a) ≤ k * P.value (a, other) := Nat.mul_le_mul_left k hb
        _ ≤ (k + 1) * P.value (a, other) := Nat.mul_le_mul_right _ (Nat.le_succ k)
    · calc
        (k - 1) * P.value (a, other) ≤ k * P.value (a, other) :=
          Nat.mul_le_mul_right _ (Nat.sub_le k 1)
        _ ≤ k * P.value (a, solve a) := Nat.mul_le_mul_left k hb

/-- Every classical `FPTAS` is a `ParamAS` for every parameter `κ`. -/
theorem ParamAS.of_fptas {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {P : NPOptimizationProblem encI encS} (h : P.FPTAS) (κ : α → ℕ) :
    ParamAS P κ := by
  obtain ⟨solve, hsolve, happrox⟩ := h
  exact ⟨solve, hsolve.computableInFPTTime _, happrox⟩

/-- Fixing any positive accuracy parameter `k > 0` in a `ParamAS` produces an FPT-time
`1 / k`-approximation algorithm parameterized solely by `κ`. -/
theorem ParamAS.exists_fpt_solver {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {P : NPOptimizationProblem encI encS} {κ : α → ℕ} (h : ParamAS P κ)
    {k : ℕ} (hk : 0 < k) :
    ∃ solve : α → β,
      ComputableInFPTTime solve encI encS κ ∧
      ∀ a : α, P.IsApproximate k a (solve a) := by
  obtain ⟨solve, hsolve, happrox⟩ := h
  have hpair : ComputableInPolyTime (fun a : α ↦ (k, a)) encI (encPair encUnary encI) :=
    (ComputableInPolyTime.const k).prod ComputableInPolyTime.id'
  refine ⟨fun a ↦ solve (k, a),
    hsolve.comp (hpair.computableInFPTTime κ) (h := Nat.pair k) (fun _ ↦ le_rfl),
    happrox k hk⟩

/-! ### 3. Randomized FPT Computability and Expectation Approximation Schemes -/

/-- A randomized program `alg : α → ProbComp β` is **computable in randomized FPT time**
(`ComputableInRandFPTTime`) with respect to parameter `κ` if it samples an FPT-computable unary
number of fair coin bits and applies an FPT-time deterministic evaluator to the input and sampled
bits. -/
@[expose]
def ComputableInRandFPTTime {α β : Type} (alg : α → ProbComp β)
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) (κ : α → ℕ) : Prop :=
  ∃ (coins : α → ℕ) (run : α × List Bool → β),
    ComputableInFPTTime coins encA encUnary κ ∧
    ComputableInFPTTime run (encPair encA encBits) encB (fun p ↦ κ p.1) ∧
    ∀ a : α, alg a = (fun w ↦ run (a, w)) <$> BitString.sampleList (coins a)

/-- Deterministic FPT-time functions lift to `ComputableInRandFPTTime` using zero random bits. -/
theorem ComputableInRandFPTTime.of_computableInFPTTime {α β : Type} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ}
    (hf : ComputableInFPTTime f encA encB κ) :
    ComputableInRandFPTTime (fun a ↦ pure (f a)) encA encB κ := by
  refine ⟨fun _ ↦ 0, fun p ↦ f p.1,
    (ComputableInPolyTime.const 0).computableInFPTTime κ,
    hf.comp ((ComputableInPolyTime.fst encA encBits).computableInFPTTime _)
      (h := id) (fun _ ↦ le_rfl),
    fun a ↦ ?_⟩
  simp [BitString.sampleList]

/-- Returning the input deterministically (`pure`) runs in randomized FPT time for any encoding and
parameter. -/
@[simp]
theorem computableInRandFPTTime_pure {α : Type} (encA : α ↪ List Bool) (κ : α → ℕ) :
    ComputableInRandFPTTime (pure : α → ProbComp α) encA encA κ :=
  .of_computableInFPTTime (ComputableInPolyTime.id'.computableInFPTTime κ)

/-- Exact finite-sum expectation formula for a function `g : β → ℝ` under a mapped `n`-bit fair
coin sample `(fun w ↦ f w) <$> BitString.sampleList n`. -/
theorem tsum_eval_map_sampleList {β : Type} (f : List Bool → β) (g : β → ℝ) (n : ℕ) :
    (∑' b : β, ((ProbComp.eval (f <$> BitString.sampleList n)) b).toReal * g b) =
      (∑ r : Fin n → Bool, g (f (List.ofFn r))) / (2 : ℝ) ^ n := by
  classical
  rw [ProbComp.eval_map, BitString.eval_sampleList]
  let S : Finset β := Finset.univ.image (fun r : Fin n → Bool ↦ f (List.ofFn r))
  have hvanish : ∀ b ∉ S, (((BitString.uniformList n).map f) b).toReal * g b = 0 := by
    intro b hb
    rw [BitString.uniformList_map_apply]
    have hempty : (Finset.univ.filter fun r : Fin n → Bool ↦ f (List.ofFn r) = b) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hfr
      exact hb (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hfr⟩)
    simp [hempty]
  rw [tsum_eq_sum hvanish]
  have hterm : ∀ b ∈ S,
      (((BitString.uniformList n).map f) b).toReal * g b =
        (∑ r ∈ Finset.univ.filter (fun r : Fin n → Bool ↦ f (List.ofFn r) = b),
          g (f (List.ofFn r))) / (2 : ℝ) ^ n := by
    intro b _
    rw [BitString.uniformList_map_apply]
    have : ((2 : ENNReal) ^ n) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    have : ((2 : ENNReal) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    have hsum_const :
        (∑ r ∈ Finset.univ.filter (fun r : Fin n → Bool ↦ f (List.ofFn r) = b),
          g (f (List.ofFn r))) =
          ((Finset.univ.filter fun r : Fin n → Bool ↦ f (List.ofFn r) = b).card : ℝ) * g b := by
      calc
        (∑ r ∈ Finset.univ.filter (fun r : Fin n → Bool ↦ f (List.ofFn r) = b),
            g (f (List.ofFn r)))
            = ∑ _r ∈ Finset.univ.filter (fun r : Fin n → Bool ↦ f (List.ofFn r) = b), g b := by
              refine Finset.sum_congr rfl fun r hr ↦ ?_
              rw [(Finset.mem_filter.mp hr).2]
        _ = ((Finset.univ.filter fun r : Fin n → Bool ↦ f (List.ofFn r) = b).card : ℝ) * g b := by
              simp [nsmul_eq_mul]
    rw [hsum_const, div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to
    (fun r _ ↦ Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩) _

/-- For `n = 0` coin flips, `BitString.sampleList 0` evaluates deterministically at `[]`. -/
theorem tsum_eval_map_sampleList_zero {β : Type} (f : List Bool → β) (g : β → ℝ) :
    (∑' b : β, ((ProbComp.eval (f <$> BitString.sampleList 0)) b).toReal * g b) = g (f []) := by
  rw [tsum_eval_map_sampleList]
  simp [List.ofFn_zero]

/-- Distributional `1 / k` multiplicative approximation in expectation over `d : PMF β`: every
element in the support of `d` is feasible, and the expected objective value achieves at least
`(1 - 1 / k)` of every feasible value for maximization (or at most `(1 + 1 / k)` for
minimization). -/
@[expose]
def IsApproximateInExpectation {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (P : NPOptimizationProblem encI encS) (k : ℕ) (a : α) (d : PMF β) : Prop :=
  (∀ b ∈ d.support, P.Feasible a b) ∧
  ∀ other : β, P.Feasible a other →
    match P.goal with
    | .minimize =>
        (k : ℝ) * (∑' b : β, (d b).toReal * (P.value (a, b) : ℝ)) ≤
          ((k : ℝ) + 1) * (P.value (a, other) : ℝ)
    | .maximize =>
        ((k : ℝ) - 1) * (P.value (a, other) : ℝ) ≤
          (k : ℝ) * (∑' b : β, (d b).toReal * (P.value (a, b) : ℝ))

/-- A **randomized parameterized approximation scheme** (`RandParamAS P κ`) computes a feasible
solution distribution achieving `IsApproximateInExpectation P k a` in randomized FPT time
parameterized by `Nat.pair k (κ a)`. -/
@[expose]
def RandParamAS {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (P : NPOptimizationProblem encI encS) (κ : α → ℕ) : Prop :=
  ∃ alg : ℕ × α → ProbComp β,
    ComputableInRandFPTTime alg (encPair encUnary encI) encS (fun p ↦ Nat.pair p.1 (κ p.2)) ∧
    ∀ k : ℕ, 0 < k → ∀ a : α, IsApproximateInExpectation P k a (ProbComp.eval (alg (k, a)))

/-- Every deterministic `ParamAS` induces a `RandParamAS`. -/
theorem ParamAS.toRandParamAS {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {P : NPOptimizationProblem encI encS} {κ : α → ℕ} (h : ParamAS P κ) :
    RandParamAS P κ := by
  obtain ⟨solve, hsolve, happrox⟩ := h
  refine ⟨fun p ↦ pure (solve p), .of_computableInFPTTime hsolve, fun k hk a ↦ ?_⟩
  obtain ⟨hfeas, hval⟩ := happrox k hk a
  rw [ProbComp.eval_pure]
  refine ⟨fun b hb ↦ by rwa [(PMF.mem_support_pure_iff _ _).mp hb], fun other hother ↦ ?_⟩
  have htsum : (∑' b : β, (PMF.pure (solve (k, a)) b).toReal * (P.value (a, b) : ℝ)) =
      (P.value (a, solve (k, a)) : ℝ) := by
    classical
    rw [tsum_eq_single (solve (k, a))]
    · simp
    · intro b hb
      simp [PMF.pure_apply, hb]
  have hv := hval other hother
  cases hgoal : P.goal
  · rw [hgoal] at hv
    rw [htsum]
    exact_mod_cast hv
  · rw [hgoal] at hv
    rw [htsum]
    have hk1 : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk]
      simp
    rw [hk1]
    exact_mod_cast hv

/-- For a maximization problem (`P.goal = .maximize`), `RandParamAS P κ` yields for every real
`ε > 0` a randomized FPT algorithm parameterized by `κ` whose output is always feasible and achieves
at least `(1 - ε) * OPT` in expectation. -/
theorem RandParamAS.exists_fpt_eps_approx {α β : Type} {encI : α ↪ List Bool}
    {encS : β ↪ List Bool} {P : NPOptimizationProblem encI encS} {κ : α → ℕ}
    (h : RandParamAS P κ) (hmax : P.goal = .maximize) {ε : ℝ} (hε : 0 < ε) :
    ∃ alg : α → ProbComp β,
      ComputableInRandFPTTime alg encI encS κ ∧
      ∀ a : α, (∀ b ∈ (ProbComp.eval (alg a)).support, P.Feasible a b) ∧
        ∀ other : β, P.Feasible a other →
          (1 - ε) * (P.value (a, other) : ℝ) ≤
            ∑' b : β, ((ProbComp.eval (alg a)) b).toReal * (P.value (a, b) : ℝ) := by
  obtain ⟨alg, ⟨coins, run, hcoins, hrun, halg⟩, happrox⟩ := h
  let k : ℕ := max 1 ⌈1 / ε⌉₊
  have hk : 0 < k := by positivity
  have hpair : ComputableInPolyTime (fun a : α ↦ (k, a)) encI (encPair encUnary encI) :=
    (ComputableInPolyTime.const k).prod ComputableInPolyTime.id'
  have hpair2 : ComputableInPolyTime (fun p : α × List Bool ↦ ((k, p.1), p.2))
      (encPair encI encBits) (encPair (encPair encUnary encI) encBits) :=
    (hpair.comp (ComputableInPolyTime.fst encI encBits)).prod
      (ComputableInPolyTime.snd encI encBits)
  refine ⟨fun a ↦ alg (k, a),
    ⟨fun a ↦ coins (k, a), fun p ↦ run ((k, p.1), p.2),
      hcoins.comp (hpair.computableInFPTTime κ) (h := Nat.pair k) (fun _ ↦ le_rfl),
      hrun.comp (hpair2.computableInFPTTime (fun p ↦ κ p.1))
        (h := Nat.pair k) (fun _ ↦ le_rfl),
      fun a ↦ halg (k, a)⟩,
    fun a ↦ ?_⟩
  obtain ⟨hfeas, hexp⟩ := happrox k hk a
  refine ⟨hfeas, fun other hother ↦ ?_⟩
  have h1 := hexp other hother
  rw [hmax] at h1
  dsimp only at h1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk_inv : 1 / (k : ℝ) ≤ ε := by
    have hceil : 1 / ε ≤ (k : ℝ) :=
      (Nat.le_ceil (1 / ε)).trans (Nat.cast_le.mpr (le_max_right 1 ⌈1 / ε⌉₊))
    rw [div_le_iff₀ hk_pos]
    have hmul := mul_le_mul_of_nonneg_left hceil hε.le
    rwa [mul_one_div_cancel hε.ne'] at hmul
  have hdiv : ((k : ℝ) - 1) / (k : ℝ) * (P.value (a, other) : ℝ) ≤
      ∑' b : β, ((ProbComp.eval (alg (k, a))) b).toReal * (P.value (a, b) : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk_pos]
    linarith
  have hsub : 1 - ε ≤ ((k : ℝ) - 1) / (k : ℝ) := by
    rw [sub_div, div_self hk_pos.ne']
    linarith
  exact (mul_le_mul_of_nonneg_right hsub (Nat.cast_nonneg _)).trans hdiv

/-! ### 4. Marx's Bounded-Optimum Decision Reduction -/

/-- **Marx's Bounded-Optimum Decision Theorem**: if a
maximization NP optimization problem `P` admits a deterministic `ParamAS` with respect to parameter
`κ`, then deciding whether `P` has a feasible solution of objective value at least `t` lies in
`FPT` parameterized by `Nat.pair (κ a) t`.
-/
theorem ParamAS.boundedOpt_mem_fpt {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {P : NPOptimizationProblem encI encS} {κ : α → ℕ}
    (h : ParamAS P κ) (hmax : P.goal = .maximize) :
    {p : α × ℕ | ∃ b : β, P.Feasible p.1 b ∧ p.2 ≤ P.value (p.1, b)} ∈
      FPT (encPair encI encNat) (fun p ↦ Nat.pair (κ p.1) p.2) := by
  obtain ⟨solve, hsolve, happrox⟩ := h
  let μ : α × ℕ → ℕ := fun p ↦ Nat.pair (κ p.1) p.2
  have ht_bin : ComputableInPolyTime (fun p : α × ℕ ↦ p.2 + 1) (encPair encI encNat) encNat := by
    fun_prop
  have ht_unary : ComputableInFPTTime (fun p : α × ℕ ↦ p.2 + 1)
      (encPair encI encNat) encUnary μ :=
    computableInFPTTime_binaryToUnary.comp (ht_bin.computableInFPTTime μ)
      (h := fun z ↦ z + 1) (fun p ↦ Nat.add_le_add_right (Nat.right_le_pair (κ p.1) p.2) 1)
  -- Pair `(p.2 + 1, p.1)` in `encPair encUnary encI` via FPT-time composition.
  have hprep : ComputableInFPTTime (fun p : α × ℕ ↦ (p.2 + 1, p.1))
      (encPair encI encNat) (encPair encUnary encI) μ := by
    have hstep1 : ComputableInFPTTime (fun p : α × ℕ ↦ p.2 + 1) (encPair encI encNat) encUnary μ :=
      ht_unary
    obtain ⟨F₁, c₁, h1⟩ := hstep1
    obtain ⟨d₂, _, h2⟩ := (ComputableInPolyTime.fst encI encNat).exists_degree
    have h1_O : ComputableInO (fun p : α × ℕ ↦ p.2 + 1) (encPair encI encNat) encUnary
        (fun p ↦ F₁ (μ p) * ((encPair encI encNat p).length + 1) ^ c₁)
        (fun p ↦ F₁ (μ p) * ((encPair encI encNat p).length + 1) ^ c₁) :=
      ComputableInO.of_bounds h1 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
        (fun a ↦ (h1.length_le a).trans (by omega))
    have hprod := h1_O.prod h2.inO
    refine (hprod.mono_le (fun p ↦ ?_) (fun p ↦ ?_)).computableInFPTTime
      (F := fun z ↦ F₁ z + 1) (c := c₁ + d₂)
    all_goals
      set L := ((encPair encI encNat p).length + 1)
      have hc1 : L ^ c₁ ≤ L ^ (c₁ + d₂) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hd2 : L ^ d₂ ≤ L ^ (c₁ + d₂) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hm := Nat.mul_le_mul_left (F₁ (μ p)) hc1
      rw [Nat.add_mul, Nat.one_mul]
      omega
  have hcand : ComputableInFPTTime (fun p : α × ℕ ↦ solve (p.2 + 1, p.1))
      (encPair encI encNat) encS μ :=
    hsolve.comp hprep
      (h := fun z ↦ Nat.pair ((Nat.unpair z).2 + 1) (Nat.unpair z).1)
      (fun p ↦ by simp [μ])
  -- Compute `(p.2, P.value (p.1, solve (p.2 + 1, p.1)))` and compare in FPT time.
  have hdec : ComputableInFPTTime
      (fun p : α × ℕ ↦ decide (p.2 ≤ P.value (p.1, solve (p.2 + 1, p.1))))
      (encPair encI encNat) encBool μ := by
    obtain ⟨Fs, cs, hs⟩ := hcand
    obtain ⟨da, _, ha⟩ := (ComputableInPolyTime.fst encI encNat).exists_degree
    have hs_O : ComputableInO (fun p : α × ℕ ↦ solve (p.2 + 1, p.1))
        (encPair encI encNat) encS
        (fun p ↦ Fs (μ p) * ((encPair encI encNat p).length + 1) ^ cs)
        (fun p ↦ Fs (μ p) * ((encPair encI encNat p).length + 1) ^ cs) :=
      ComputableInO.of_bounds hs 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
        (fun p ↦ (hs.length_le p).trans (by omega))
    have hpair_as := (ha.inO.prod hs_O).mono_le
      (fun p ↦ by
        set L := (encPair encI encNat p).length + 1
        have h1 : L ^ da ≤ L ^ (da + cs) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have h2 : L ^ cs ≤ L ^ (da + cs) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have hm := Nat.mul_le_mul_left (Fs (μ p)) h2
        change L ^ da + Fs (μ p) * L ^ cs ≤ (Fs (μ p) + 1) * L ^ (da + cs)
        rw [Nat.add_mul, Nat.one_mul]; omega)
      (fun p ↦ by
        set L := (encPair encI encNat p).length + 1
        have h1 : L ^ da ≤ L ^ (da + cs) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have h2 : L ^ cs ≤ L ^ (da + cs) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have hm := Nat.mul_le_mul_left (Fs (μ p)) h2
        change L ^ da + Fs (μ p) * L ^ cs ≤ (Fs (μ p) + 1) * L ^ (da + cs)
        rw [Nat.add_mul, Nat.one_mul]; omega)
    have hval_fpt : ComputableInFPTTime
        (fun p : α × ℕ ↦ P.value (p.1, solve (p.2 + 1, p.1)))
        (encPair encI encNat) encNat μ :=
      (P.computableInPolyTime_value.computableInFPTTime (fun _ ↦ 0)).comp
        (hpair_as.computableInFPTTime (F := fun z ↦ Fs z + 1) (c := da + cs))
        (h := fun _ ↦ 0) (fun _ ↦ le_rfl)
    obtain ⟨Fv, cv, hv⟩ := hval_fpt
    obtain ⟨dt, _, ht⟩ := (ComputableInPolyTime.snd encI encNat).exists_degree
    have hv_O : ComputableInO (fun p : α × ℕ ↦ P.value (p.1, solve (p.2 + 1, p.1)))
        (encPair encI encNat) encNat
        (fun p ↦ Fv (μ p) * ((encPair encI encNat p).length + 1) ^ cv)
        (fun p ↦ Fv (μ p) * ((encPair encI encNat p).length + 1) ^ cv) :=
      ComputableInO.of_bounds hv 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
        (fun p ↦ (hv.length_le p).trans (by omega))
    have hpair_tv := (ht.inO.prod hv_O).mono_le
      (fun p ↦ by
        set L := (encPair encI encNat p).length + 1
        have h1 : L ^ dt ≤ L ^ (dt + cv) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have h2 : L ^ cv ≤ L ^ (dt + cv) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have hm := Nat.mul_le_mul_left (Fv (μ p)) h2
        change L ^ dt + Fv (μ p) * L ^ cv ≤ (Fv (μ p) + 1) * L ^ (dt + cv)
        rw [Nat.add_mul, Nat.one_mul]; omega)
      (fun p ↦ by
        set L := (encPair encI encNat p).length + 1
        have h1 : L ^ dt ≤ L ^ (dt + cv) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have h2 : L ^ cv ≤ L ^ (dt + cv) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        have hm := Nat.mul_le_mul_left (Fv (μ p)) h2
        change L ^ dt + Fv (μ p) * L ^ cv ≤ (Fv (μ p) + 1) * L ^ (dt + cv)
        rw [Nat.add_mul, Nat.one_mul]; omega)
    exact ((ComputableInPolyTime.binary_le.computableInFPTTime (fun _ ↦ 0)).comp
      (hpair_tv.computableInFPTTime (F := fun z ↦ Fv z + 1) (c := dt + cv))
      (h := fun _ ↦ 0) (fun _ ↦ le_rfl))
  refine mem_FPT_iff_computableInFPTTime.mpr ⟨_, hdec, fun ⟨a, t⟩ ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq]
  obtain ⟨hfeas_cand, hval_cand⟩ := happrox (t + 1) (Nat.succ_pos t) a
  refine ⟨?_, fun hle ↦ ⟨solve (t + 1, a), hfeas_cand, hle⟩⟩
  rintro ⟨b, hfb, htb⟩
  rcases eq_or_ne t 0 with rfl | _
  · exact Nat.zero_le _
  · have hineq := hval_cand b hfb
    rw [hmax, Nat.add_sub_cancel] at hineq
    by_contra hlt
    push Not at hlt
    have : P.value (a, solve (t + 1, a)) + 1 ≤ t := hlt
    have hmul1 : t * t ≤ t * P.value (a, b) := Nat.mul_le_mul_left t htb
    have hmul2 : (t + 1) * P.value (a, solve (t + 1, a)) < t * t := by nlinarith
    omega

end Cslib.Complexity
