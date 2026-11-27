/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.TotalComputability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Parameterized Counting Problems, Strongly Uniform FPT, and Parsimonious Reductions

This module formalizes the core deterministic foundations of parameterized counting complexity
 :

1. **Total computability closure and Blum step-count bounds**: binary-to-unary conversion,
   arithmetic and range-tabulation closure of `IsComputable`, Blum's computable step-count lemma
   (`IsComputable.exists_computable_time`), and polynomial-time word extensions.
2. **`ParameterizedCountingProblem α` and `ParameterizedCountingProblem.InFPT`**: bundles an
   injective binary instance encoding `enc : α ↪ List Bool`, an exact counting target
   `count : α → ℕ`, and a polynomial-time parameterization `param : α → ℕ`, together with
   strongly uniform fixed-parameter tractability (`InFPT`) and unary-padded word simulation.
3. **`FPTParsimoniousReducible`**: FPT parsimonious reductions with reflexivity, transitivity,
   polynomial-time lifting, and downward closure of `InFPT`.

## Main definitions

* `CslibFrontier.Computability.cumulSum`,
  `CslibFrontier.Computability.ComputableInStronglyUniformFPTTime`,
  `CslibFrontier.Computability.ParameterizedCountingProblem`,
  `CslibFrontier.Computability.ParameterizedCountingProblem.InFPT`,
  `CslibFrontier.Computability.FPTParsimoniousReducible`.

## Main results

* `CslibFrontier.Computability.isComputable_nat_to_unary`,
  `CslibFrontier.Computability.IsComputable.two_pow_nat`,
  `CslibFrontier.Computability.IsComputable.cumulSum`,
  `CslibFrontier.Computability.IsComputable.range_map_unary`,
  `CslibFrontier.Computability.IsComputable.exists_computable_time`,
  `CslibFrontier.Computability.ComputableInPolyTime.exists_word_extension`.
* `CslibFrontier.Computability.ParameterizedCountingProblem.InFPT.of_computableInPolyTime`,
  `CslibFrontier.Computability.ParameterizedCountingProblem.InFPT.of_paddedPolyTime`,
  `CslibFrontier.Computability.ParameterizedCountingProblem.InFPT.computableInFPTTime`,
  `CslibFrontier.Computability.ParameterizedCountingProblem.InFPT.exists_paddedWordSimulator`.
* `CslibFrontier.Computability.FPTParsimoniousReducible.refl`,
  `CslibFrontier.Computability.FPTParsimoniousReducible.trans`,
  `CslibFrontier.Computability.FPTParsimoniousReducible.of_computableInPolyTime`,
  `CslibFrontier.Computability.FPTParsimoniousReducible.inFPT`.
-/

public section

open Cslib Cslib.Complexity Cslib.Probability
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapePTM

namespace CslibFrontier

namespace Computability

/-! ### 1. Total Computability Closure and Blum Step-Count Majorants -/

section ComputableHelpers

/-- Binary-to-unary conversion `id : ℕ → ℕ` is total computable (`IsComputable id encNat encUnary`).
-/
theorem isComputable_nat_to_unary : IsComputable (id : ℕ → ℕ) encNat encUnary := by
  have hn := (ComputableInDegree.of_eq (encIn := encNat) (encMid := encNat) fun _ ↦ rfl).inO_one
  have hinit := (ComputableInDegree.const (encIn := encNat) (encMid := encUnary) 0).inO_one
  obtain ⟨ds, _, hs_deg⟩ := ((ComputableInPolyTime.unary_add.comp
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1))).of_enc_eq
    (g := fun u : ℕ ↦ u + 1) (encD := encUnary) fun _ ↦ rfl).exists_degree
  have hstep : ComputableInO (fun u : ℕ ↦ u + 1) encUnary encUnary
      (fun u ↦ (u + 1) ^ ds) (fun u ↦ (u + 1) ^ ds) := by
    simpa [encUnary_apply] using hs_deg.inO
  have hiter_eq (k : ℕ) : ((fun u : ℕ ↦ u + 1)^[k] 0) = k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]
  have hit := ComputableInO.iterate hn hinit hstep
    (R := fun n ↦ (n + 1) ^ ds) (Q := fun n ↦ (n + 1) ^ ds) (B := fun n ↦ n)
    (fun n k hk ↦ by rw [hiter_eq]; exact Nat.pow_le_pow_left (by omega) ds)
    (fun n k hk ↦ by rw [hiter_eq]; exact Nat.pow_le_pow_left (by omega) ds)
    (fun n k hk ↦ by simpa [hiter_eq] using hk)
  obtain ⟨_, hts, -⟩ := hit.of_enc_eq (g := (id : ℕ → ℕ)) (encC := encUnary)
    fun n ↦ by simp [hiter_eq]
  exact hts.isComputable

/-- Addition of two `IsComputable` natural-valued functions is `IsComputable`. -/
theorem IsComputable.add_nat {α : Type} {encA : α ↪ List Bool} {f g : α → ℕ}
    (hf : IsComputable f encA encNat) (hg : IsComputable g encA encNat) :
    IsComputable (fun a ↦ f a + g a) encA encNat :=
  ComputableInPolyTime.binary_add.isComputable.comp (hf.prod (enc := encPair encNat encNat) hg)

/-- Multiplication of two `IsComputable` natural-valued functions is `IsComputable`. -/
theorem IsComputable.mul_nat {α : Type} {encA : α ↪ List Bool} {f g : α → ℕ}
    (hf : IsComputable f encA encNat) (hg : IsComputable g encA encNat) :
    IsComputable (fun a ↦ f a * g a) encA encNat :=
  ComputableInPolyTime.binary_mul.isComputable.comp (hf.prod (enc := encPair encNat encNat) hg)

/-- Pairing two `IsComputable` functions into `encPair` is `IsComputable`. -/
theorem IsComputable.pair_enc {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g : α → γ}
    (hf : IsComputable f encA encB) (hg : IsComputable g encA encC) :
    IsComputable (fun a ↦ (f a, g a)) encA (encPair encB encC) :=
  hf.prod (enc := encPair encB encC) hg

/-- Fixed natural power of an `IsComputable` function is `IsComputable`. -/
theorem IsComputable.pow_const_nat {α : Type} {encA : α ↪ List Bool} {f : α → ℕ}
    (hf : IsComputable f encA encNat) (d : ℕ) :
    IsComputable (fun a ↦ f a ^ d) encA encNat := by
  induction d with
  | zero => exact (ComputableInPolyTime.const 1).isComputable
  | succ d ih => simpa only [pow_succ] using IsComputable.mul_nat ih hf

/-- Exponential `2 ^ f a` of an `IsComputable` natural-valued function is `IsComputable`. -/
theorem IsComputable.two_pow_nat {α : Type} {encA : α ↪ List Bool} {f : α → ℕ}
    (hf : IsComputable f encA encNat) :
    IsComputable (fun a ↦ 2 ^ f a) encA encNat :=
  ComputableInPolyTime.binary_two_pow.isComputable.comp (isComputable_nat_to_unary.comp hf)

/-- Cumulative partial-sum majorant `∑ j ∈ Finset.range (k + 1), f j` of `f : ℕ → ℕ`. -/
def cumulSum (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), f j

/-- Base evaluation `cumulSum f 0 = f 0`. -/
@[simp]
theorem cumulSum_zero (f : ℕ → ℕ) : cumulSum f 0 = f 0 := by
  simp [cumulSum]

/-- Step recurrence `cumulSum f (k + 1) = cumulSum f k + f (k + 1)`. -/
@[simp]
theorem cumulSum_succ (f : ℕ → ℕ) (k : ℕ) :
    cumulSum f (k + 1) = cumulSum f k + f (k + 1) := by
  simp [cumulSum, Finset.sum_range_succ]

/-- `cumulSum f` dominates `f` on `[0, k]`. -/
theorem le_cumulSum {f : ℕ → ℕ} {i k : ℕ} (hik : i ≤ k) : f i ≤ cumulSum f k :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))

/-- `cumulSum f` is monotone. -/
theorem monotone_cumulSum (f : ℕ → ℕ) : Monotone (cumulSum f) :=
  fun _ _ h ↦ Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

/-- If `f : ℕ → ℕ` is `IsComputable`, then its monotone majorant `cumulSum f` is `IsComputable`. -/
theorem IsComputable.cumulSum {f : ℕ → ℕ} (hf : IsComputable f encNat encNat) :
    IsComputable (Computability.cumulSum f) encNat encNat := by
  obtain ⟨tf, sf, htf⟩ := hf
  have hf_inO : ComputableInO f encNat encNat
      (fun n ↦ tf n + (encNat (f n)).length) (fun n ↦ sf n + (encNat (f n)).length) :=
    ComputableInO.of_bounds htf 1 (fun _ ↦ by omega) (fun _ ↦ by omega) (fun _ ↦ by omega)
  have hn := (ComputableInDegree.of_eq (encIn := encNat) (encMid := encNat) fun _ ↦ rfl).inO_one
  obtain ⟨_, _, hi_deg⟩ :=
    (ComputableInPolyTime.const (encIn := encNat) (encOut := encPair encNat encNat)
      (0, f 0)).exists_degree
  obtain ⟨_, _, ha_deg⟩ := ComputableInPolyTime.binary_add.exists_degree
  obtain ⟨_, _, hp1_deg⟩ := (ComputableInPolyTime.binary_add.comp
    ((ComputableInPolyTime.fst encNat encNat).prod (ComputableInPolyTime.const 1))).exists_degree
  obtain ⟨_, _, hsnd_deg⟩ := (ComputableInPolyTime.snd encNat encNat).exists_degree
  let step : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.1 + 1, p.2 + f (p.1 + 1))
  have hstep_inO : ∃ Ts Ss, ComputableInO step (encPair encNat encNat) (encPair encNat encNat)
      Ts Ss :=
    ⟨_, _, hp1_deg.inO.prod (ha_deg.inO.comp (hsnd_deg.inO.prod (hf_inO.comp hp1_deg.inO)))⟩
  obtain ⟨Ts, Ss, hstep⟩ := hstep_inO
  have hiter_eq (r : ℕ) : step^[r] (0, f 0) = (r, Computability.cumulSum f r) := by
    induction r with
    | zero => simp [Computability.cumulSum]
    | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [step, Computability.cumulSum, Finset.sum_range_succ]
  have hit := ComputableInO.iterate hn hi_deg.inO hstep
    (R := fun k ↦ (Finset.Iic k).sup fun r ↦ Ts (step^[r] (0, f 0)))
    (Q := fun k ↦ (Finset.Iic k).sup fun r ↦ Ss (step^[r] (0, f 0)))
    (B := fun k ↦ (Finset.Iic k).sup fun r ↦ (encPair encNat encNat (step^[r] (0, f 0))).length)
    (fun k r hr ↦ Finset.le_sup (f := fun r ↦ Ts (step^[r] (0, f 0))) (Finset.mem_Iic.mpr hr))
    (fun k r hr ↦ Finset.le_sup (f := fun r ↦ Ss (step^[r] (0, f 0))) (Finset.mem_Iic.mpr hr))
    (fun k r hr ↦ Finset.le_sup
      (f := fun r ↦ (encPair encNat encNat (step^[r] (0, f 0))).length) (Finset.mem_Iic.mpr hr))
  obtain ⟨_, hts, -⟩ := (hsnd_deg.inO.comp hit).of_enc_eq
    (g := Computability.cumulSum f) (encC := encNat) fun k ↦ by simp [hiter_eq]
  exact hts.isComputable

/-- Mapping `(List.range (k + 1)).map f` into `encList encUnary` is `IsComputable` whenever `f` is
`IsComputable f encNat encNat`. -/
theorem IsComputable.range_map_unary {f : ℕ → ℕ} (hf : IsComputable f encNat encNat) :
    IsComputable (fun k ↦ (List.range (k + 1)).map f) encNat (encList encUnary) := by
  have hf_un : IsComputable f encNat encUnary := isComputable_nat_to_unary.comp hf
  obtain ⟨tf, sf, htf⟩ := hf_un
  have hf_inO : ComputableInO f encNat encUnary
      (fun n ↦ tf n + (encUnary (f n)).length) (fun n ↦ sf n + (encUnary (f n)).length) :=
    ComputableInO.of_bounds htf 1 (fun _ ↦ by omega) (fun _ ↦ by omega) (fun _ ↦ by omega)
  have hn := (ComputableInDegree.of_eq (encIn := encNat) (encMid := encNat) fun _ ↦ rfl).inO_one
  let E := encPair encNat (encList encUnary)
  obtain ⟨_, _, hi_deg⟩ :=
    (ComputableInPolyTime.const (encIn := encNat) (encOut := E) (0, [f 0])).exists_degree
  obtain ⟨_, _, hp1_deg⟩ := (ComputableInPolyTime.binary_add.comp
    ((ComputableInPolyTime.fst encNat (encList encUnary)).prod
      (ComputableInPolyTime.const 1))).exists_degree
  obtain ⟨_, _, hsnd_deg⟩ := (ComputableInPolyTime.snd encNat (encList encUnary)).exists_degree
  obtain ⟨_, _, hsing_deg⟩ := ((ComputableInPolyTime.cons encUnary).comp
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const []))).exists_degree
  obtain ⟨_, _, happ_deg⟩ := (ComputableInPolyTime.listAppend encUnary).exists_degree
  let step : ℕ × List ℕ → ℕ × List ℕ := fun p ↦ (p.1 + 1, p.2 ++ [f (p.1 + 1)])
  have hstep_inO : ∃ Ts Ss, ComputableInO step E E Ts Ss :=
    ⟨_, _, hp1_deg.inO.prod
      (happ_deg.inO.comp (hsnd_deg.inO.prod (hsing_deg.inO.comp (hf_inO.comp hp1_deg.inO))))⟩
  obtain ⟨Ts, Ss, hstep⟩ := hstep_inO
  have hiter_eq (r : ℕ) : step^[r] (0, [f 0]) = (r, (List.range (r + 1)).map f) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [step, List.range_succ]
  have hit := ComputableInO.iterate hn hi_deg.inO hstep
    (R := fun k ↦ (Finset.Iic k).sup fun r ↦ Ts (step^[r] (0, [f 0])))
    (Q := fun k ↦ (Finset.Iic k).sup fun r ↦ Ss (step^[r] (0, [f 0])))
    (B := fun k ↦ (Finset.Iic k).sup fun r ↦ (E (step^[r] (0, [f 0]))).length)
    (fun k r hr ↦ Finset.le_sup (f := fun r ↦ Ts (step^[r] (0, [f 0]))) (Finset.mem_Iic.mpr hr))
    (fun k r hr ↦ Finset.le_sup (f := fun r ↦ Ss (step^[r] (0, [f 0]))) (Finset.mem_Iic.mpr hr))
    (fun k r hr ↦ Finset.le_sup (f := fun r ↦ (E (step^[r] (0, [f 0]))).length)
      (Finset.mem_Iic.mpr hr))
  obtain ⟨_, hts, -⟩ := (hsnd_deg.inO.comp hit).of_enc_eq
    (g := fun k ↦ (List.range (k + 1)).map f) (encC := encList encUnary)
    fun k ↦ by simp [hiter_eq]
  exact hts.isComputable

private lemma ofDeterministic_interpret_run_eq {k : ℕ} {State : Type}
    (tm : MultiTapeTM k Bool State) (ans : Unit × List Bool → List Bool)
    (fuel : ℕ) (w : List Bool) :
    OracleComp.interpret (m := Id) ans
      ((MultiTapePTM.ofDeterministic (Oracle := Unit) tm).run (pure false)
        (fun op word ↦ OracleComp.query (op, word)) fuel w) =
    (tm.runFrom (tm.initCfg w) fuel).output := by
  let M₀ := MultiTapePTM.ofDeterministic (Oracle := Unit) tm
  have hmem := M₀.mem_support_runConfigFrom_pure false ans () fuel (M₀.initialConfig w)
  have hmap : (OracleComp.interpret (m := Id) ans
      (M₀.run (pure false) (fun op word ↦ OracleComp.query (op, word)) fuel w), ()) ∈
    (ProbOracleComp.runWith (fun q s ↦ PMF.pure (ans q, s))
      (M₀.runOracle fuel w) ()).support := by
    simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
      ProbOracleComp.runWith_map, PMF.mem_support_map_iff, OracleComp.interpret_map]
    exact ⟨_, hmem, rfl⟩
  rw [MultiTapePTM.run_interpret_runOracle_ofDeterministic, PMF.mem_support_pure_iff] at hmap
  exact (Prod.mk.inj hmap).1

private lemma ofDeterministic_localStep_state {k : ℕ} {State : Type}
    (tm : MultiTapeTM k Bool State) :
    ∀ (i : ℕ) (cfg : FiniteConfig k Bool State Unit) (c : Cfg k Bool State cfg.tapes.input),
      cfg.tapes.Represents c →
      (((MultiTapePTM.ofDeterministic (Oracle := Unit) tm).localStep)^[i] cfg).tapes.state =
        (tm.runFrom c i).state := by
  intro i
  induction i with
  | zero =>
    intro cfg c hrep
    exact hrep.state
  | succ i ih =>
    intro cfg c hrep
    rw [Function.iterate_succ_apply, MultiTapeTM.runFrom, Function.iterate_succ_apply]
    let M₀ := MultiTapePTM.ofDeterministic (Oracle := Unit) tm
    change (M₀.localStep^[i] (M₀.localStep cfg)).tapes.state = (tm.runFrom (tm.step c) i).state
    unfold MultiTapePTM.localStep
    cases hs : c.state with
    | none =>
      have hcs : cfg.tapes.state = none := hrep.state.trans hs
      simp only [hcs, Option.map_none]
      rw [MultiTapeTM.step_of_halt hs]
      exact ih cfg c hrep
    | some q =>
      have hcs : cfg.tapes.state = some q := hrep.state.trans hs
      simp only [hcs, Option.map_some]
      rw [MultiTapeTM.step_of_state hs, ← hrep.inputSymbol, ← hrep.workTapeSymbols]
      exact ih _ _ (hrep.step _)

/-- **Blum Step-Count Lemma**: every total computable function `f : ℕ → β` (`IsComputable f encNat
encB`) admits computable time and space bounds `t, s : ℕ → ℕ` (`IsComputable t encNat encNat`,
`IsComputable s encNat encNat`). -/
theorem IsComputable.exists_computable_time {β : Type} {encB : β ↪ List Bool} {f : ℕ → β}
    (hf : IsComputable f encNat encB) :
    ∃ t s : ℕ → ℕ, IsComputable t encNat encNat ∧ IsComputable s encNat encNat ∧
      ComputableInTimeAndSpace f encNat encB t s := by
  classical
  obtain ⟨t₀, _, k, State, hfin, tm, htm⟩ := hf
  let _ : Finite State := hfin
  let M₀ := MultiTapePTM.ofDeterministic (Oracle := Unit) tm
  let initC (n : ℕ) : FiniteConfig k Bool State Unit := FiniteConfig.init tm.q₀ (encNat n)
  have hstate_eq (n m : ℕ) :
      (M₀.localStep^[m] (initC n)).tapes.state = (tm.runFrom (tm.initCfg (encNat n)) m).state :=
    ofDeterministic_localStep_state tm m (initC n) (tm.initCfg (encNat n))
      (FiniteCfg.represents_init tm.q₀ (encNat n))
  have hhalts (n : ℕ) : ∃ m, (M₀.localStep^[m] (initC n)).tapes.state = none :=
    ⟨t₀ n, (hstate_eq n (t₀ n)).trans (runsInTime_iff_halted.mp (htm n).2.1)⟩
  let r (n : ℕ) : ℕ := Nat.find (hhalts n)
  have hr_spec (n : ℕ) : (M₀.localStep^[r n] (initC n)).tapes.state = none :=
    Nat.find_spec (hhalts n)
  have hr_min (n m : ℕ) (hm : m < r n) : (M₀.localStep^[m] (initC n)).tapes.state ≠ none :=
    Nat.find_min (hhalts n) hm
  let round (o : Option (ℕ × FiniteConfig k Bool State Unit)) :
      Option (ℕ × FiniteConfig k Bool State Unit) :=
    match o with
    | none => none
    | some p => if p.2.tapes.state.isSome then some (p.1 + 1, M₀.localStep p.2) else none
  let encP := encPair encNat (encFiniteConfig (k := k) (State := State) (Oracle := Unit))
  let encC := encOption encP
  have hround_pt : ComputableInPolyTime round encC encC := by
    have hget : ComputableInPolyTime
        (fun o : Option (ℕ × FiniteConfig k Bool State Unit) ↦
          o.getD (0, FiniteConfig.init tm.q₀ [])) encC encP :=
      (ComputableInDegree.getD (enc₁ := encP) (enc := encC) _).computableInPolyTime
    have hcond : ComputableInPolyTime
        (fun o : Option (ℕ × FiniteConfig k Bool State Unit) ↦
          o.isSome && (o.getD (0, FiniteConfig.init tm.q₀ [])).2.tapes.state.isSome)
        encC encBool :=
      ComputableInPolyTime.bool_and'
        (ComputableInDegree.isSome encP).computableInPolyTime
        ((ComputableInPolyTime.of_finite Option.isSome).comp
          (ComputableInPolyTime.finiteCfg_state.comp
            (ComputableInPolyTime.finiteConfig_tapes.comp hget.snd')))
    have hsome : ComputableInPolyTime
        (fun o : Option (ℕ × FiniteConfig k Bool State Unit) ↦
          let p := o.getD (0, FiniteConfig.init tm.q₀ [])
          (some (p.1 + 1, M₀.localStep p.2) :
            Option (ℕ × FiniteConfig k Bool State Unit))) encC encC :=
      (ComputableInDegree.optionSome (enc₁ := encP) (enc := encC)).computableInPolyTime.comp
        ((ComputableInPolyTime.binary_add' hget.fst' (ComputableInPolyTime.const 1)).prod
          (M₀.localStep_pt.comp hget.snd'))
    refine (hcond.ite' hsome (ComputableInPolyTime.const none)).of_enc_eq fun o ↦ ?_
    rcases o with _ | ⟨_, cfg⟩
    · rfl
    · cases cfg.tapes.state <;> rfl
  obtain ⟨dr, _, hround_deg⟩ := hround_pt.exists_degree
  obtain ⟨c, ⟨_, _, _, tmf, hf_round⟩, -⟩ := Internal.NormalForm.inO hround_deg.inO
  let o₀ (n : ℕ) : Option (ℕ × FiniteConfig k Bool State Unit) := some (1, initC n)
  have hround_iter (n j : ℕ) (hj : j ≤ r n) :
      round^[j] (o₀ n) = some (j + 1, M₀.localStep^[j] (initC n)) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hne := hr_min n j (by omega)
      cases hs : (M₀.localStep^[j] (initC n)).tapes.state with
      | none => exact absurd hs hne
      | some q => simp [round, hs, Function.iterate_succ_apply']
  have hleast (n : ℕ) : IsLeast {m | encC (round^[m + 1] (o₀ n)) = []} (r n) := by
    refine ⟨?_, fun m hm ↦ ?_⟩
    · change encC (round^[r n + 1] (o₀ n)) = []
      rw [Function.iterate_succ_apply', hround_iter n (r n) le_rfl]
      simp [round, hr_spec n, encC, encOption_none]
    · by_contra hlt
      rw [not_le] at hlt
      change encC (round^[m + 1] (o₀ n)) = [] at hm
      rw [hround_iter n (m + 1) (by omega)] at hm
      simp [encC, encOption_some] at hm
  obtain ⟨_, _, hstart_deg⟩ :=
    ((ComputableInDegree.optionSome (enc₁ := encP) (enc := encC)).computableInPolyTime.comp
      ((ComputableInPolyTime.const 1).prod
        (ComputableInPolyTime.finiteConfig_init ComputableInPolyTime.natBits tm.q₀))).exists_degree
  obtain ⟨_, ⟨_, _, _, tm₀, h₀⟩, -⟩ := Internal.NormalForm.inO hstart_deg.inO
  have hloop_comp : IsComputable (fun n ↦ round^[r n] (o₀ n)) encNat encC := by
    have hts_n (n : ℕ) :=
      ((h₀ n).comp
        (computesTidily_iterateWhile
          (w := fun j ↦ encC (round^[j] (o₀ n))) (r := r n)
          (fun j hj ↦ by
            simpa only [Function.iterate_succ_apply'] using (hf_round (round^[j] (o₀ n))).mono
              (Finset.le_sup
                (f := fun j ↦ c * (((encC (round^[j] (o₀ n))).length + 1) ^ dr + 1))
                (Finset.mem_Iic.mpr hj))
              (Finset.le_sup
                (f := fun j ↦ c * (((encC (round^[j] (o₀ n))).length + 1) ^ dr + 1))
                (Finset.mem_Iic.mpr hj)))
          (fun j hj ↦ Finset.le_sup (f := fun j ↦ (encC (round^[j] (o₀ n))).length)
            (Finset.mem_Iic.mpr hj))
          (fun j hj he ↦ absurd ((hleast n).2 he) (by omega))
          (hleast n).1 true)
        true).computesInTimeAndSpace
    exact ⟨_, _, _, _, inferInstance, (tmf.iterateWhile true).comp tm₀ true, hts_n⟩
  have hextract_pt : ComputableInPolyTime
      (fun o : Option (ℕ × FiniteConfig k Bool State Unit) ↦
        (o.getD (0, FiniteConfig.init tm.q₀ [])).1) encC encNat :=
    ((ComputableInDegree.getD (enc₁ := encP) (enc := encC) _).computableInPolyTime).fst'
  have ht_comp : IsComputable (fun n ↦ r n + 1) encNat encNat := by
    convert hextract_pt.isComputable.comp hloop_comp using 1
    funext n
    simp [hround_iter n (r n) le_rfl]
  have hraw : ComputableInTimeAndSpace f encNat encB (fun n ↦ r n + 1)
      (fun n ↦ (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg (encNat n))
        (r n + 1)).space) := by
    refine ⟨k, State, hfin, tm, fun n ↦ ?_⟩
    have hhalt_r : (tm.runFrom (tm.initCfg (encNat n)) (r n)).state = none :=
      (hstate_eq n (r n)).symm.trans (hr_spec n)
    have hhalt : (tm.runFrom (tm.initCfg (encNat n)) (r n + 1)).state = none := by
      rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
        MultiTapeTM.step_of_halt hhalt_r, hhalt_r]
    exact ⟨(htm n).1, runsInTime_of_halted hhalt, runsInSpace_of_halted hhalt le_rfl⟩
  obtain ⟨ksp, hlin⟩ := hraw.exists_space_linear
  have hs_comp : IsComputable (fun n ↦ ksp * (r n + 1) + ksp) encNat encNat :=
    IsComputable.add_nat
      (IsComputable.mul_nat (ComputableInPolyTime.const ksp).isComputable ht_comp)
      (ComputableInPolyTime.const ksp).isComputable
  exact ⟨fun n ↦ r n + 1, fun n ↦ ksp * (r n + 1) + ksp, ht_comp, hs_comp, hlin⟩

/-- Any polynomial-time function `f : α → ℕ` extends to a polynomial-time function
`f_ext : List Bool → ℕ` on all bit strings agreeing with `f` on `encA a`. -/
theorem ComputableInPolyTime.exists_word_extension {α : Type} {encA : α ↪ List Bool}
    {f : α → ℕ} (hf : ComputableInPolyTime f encA encNat) :
    ∃ f_ext : List Bool → ℕ,
      ComputableInPolyTime f_ext encBits encNat ∧ ∀ a : α, f_ext (encA a) = f a := by
  classical
  obtain ⟨t, _, ht, _, k, State, hfin, tm, htm⟩ := hf
  let _ : Finite State := hfin
  obtain ⟨c, d, hcd⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  let M₀ := MultiTapePTM.ofDeterministic (Oracle := Unit) tm
  have hrun_pt := M₀.computableInPolyTime_run (input := encBits)
    (ComputableInPolyTime.const false) c d
  let f_ext (w : List Bool) : ℕ :=
    ofBits (OracleComp.interpret (m := Id) (fun _ ↦ [false])
      (M₀.run (pure false) (fun op word ↦ OracleComp.query (op, word))
        (c * (w.length + 1) ^ d) w))
  refine ⟨f_ext, ComputableInPolyTime.bitsToNat.comp hrun_pt, fun a ↦ ?_⟩
  dsimp only [f_ext]
  rw [ofDeterministic_interpret_run_eq tm _ _ _, ((htm a).runFrom_of_le (hcd (encA a).length)).2]
  exact Nat.foldr_bit_bits (f a)

end ComputableHelpers

/-! ### 2. Strongly Uniform FPT Computability and `ParameterizedCountingProblem` -/

section ProblemsAndFPT

/-- Strongly uniform FPT-time computability: `f` is
computable in time and space `F (κ a) * ((encA a).length + 1) ^ c` for a **computable** function
`F : ℕ → ℕ` and an exponent `c > 0`.
-/
@[expose] def ComputableInStronglyUniformFPTTime {α β : Type*} (f : α → β) (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (κ : α → ℕ) : Prop :=
  ∃ (F : ℕ → ℕ) (c : ℕ),
    IsComputable F encNat encNat ∧
    0 < c ∧
    ComputableInTimeAndSpace f encA encB
      (fun a ↦ F (κ a) * ((encA a).length + 1) ^ c)
      (fun a ↦ F (κ a) * ((encA a).length + 1) ^ c)

/-- Strongly uniform FPT-time computability implies `Cslib.Complexity.ComputableInFPTTime`. -/
theorem ComputableInStronglyUniformFPTTime.computableInFPTTime {α β : Type*} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ}
    (h : ComputableInStronglyUniformFPTTime f encA encB κ) :
    ComputableInFPTTime f encA encB κ := by
  obtain ⟨F, c, _, _, hts⟩ := h
  exact ⟨F, c, hts⟩

/-- A time bound `F (κ a) * ((encA a).length + 1) ^ c` with `IsComputable F` and `c > 0` suffices
for `ComputableInStronglyUniformFPTTime`. -/
theorem ComputableInStronglyUniformFPTTime.of_time {α β : Type*} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ} {F : ℕ → ℕ} {c : ℕ} {s : α → ℕ}
    (hF : IsComputable F encNat encNat) (hc : 0 < c)
    (h : ComputableInTimeAndSpace f encA encB (fun a ↦ F (κ a) * ((encA a).length + 1) ^ c) s) :
    ComputableInStronglyUniformFPTTime f encA encB κ := by
  obtain ⟨k, hlin⟩ := h.exists_space_linear
  have hle (a : α) (m : ℕ) (hm : m ≤ k + 1) :
      m * (F (κ a) * ((encA a).length + 1) ^ c) + m ≤
        (k + 1) * (F (κ a) + 1) * ((encA a).length + 1) ^ c := by
    have hP := Nat.one_le_pow c _ (Nat.succ_pos (encA a).length)
    have := Nat.mul_le_mul_right (F (κ a) * ((encA a).length + 1) ^ c) hm
    nlinarith
  have hF' : IsComputable (fun n ↦ (k + 1) * (F n + 1)) encNat encNat :=
    IsComputable.mul_nat (ComputableInPolyTime.const (k + 1)).isComputable
      (IsComputable.add_nat hF (ComputableInPolyTime.const 1).isComputable)
  exact ⟨fun n ↦ (k + 1) * (F n + 1), c, hF', hc,
    hlin.mono (fun a ↦ by dsimp only; have := hle a 1 (by omega); omega)
      (fun a ↦ by dsimp only; exact hle a k (by omega))⟩

/-- Every polynomial-time function is computable in strongly uniform FPT time for any parameter. -/
theorem ComputableInStronglyUniformFPTTime.of_computableInPolyTime {α β : Type} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (hf : ComputableInPolyTime f encA encB) (κ : α → ℕ) :
    ComputableInStronglyUniformFPTTime f encA encB κ := by
  obtain ⟨d, _, hdeg⟩ := hf.exists_degree
  obtain ⟨k, hts, -⟩ := hdeg.inO
  have hle (a : α) : k * (((encA a).length + 1) ^ d + 1) ≤
      (2 * k + 1) * ((encA a).length + 1) ^ (d + 1) := by
    have h1 : 1 ≤ ((encA a).length + 1) ^ (d + 1) :=
      Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h2 : ((encA a).length + 1) ^ d ≤ ((encA a).length + 1) ^ (d + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ d)
    nlinarith
  exact ⟨fun _ ↦ 2 * k + 1, d + 1, (ComputableInPolyTime.const _).isComputable,
    Nat.succ_pos d, hts.mono hle hle⟩

private lemma fpt_comp_arith {L F₁ c₁ l n F₂' e : ℕ}
    (hn : n ≤ l * (F₁ * (L + 1) ^ c₁ + 1)) (hF : 0 ≤ F₂') :
    F₁ * (L + 1) ^ c₁ + F₂' * (n + 1) ^ e ≤
      (F₁ + F₂' * ((l + 1) * (F₁ + 1)) ^ e) * (L + 1) ^ (c₁ + c₁ * e) := by
  have _ := hF
  have hP : 1 ≤ (L + 1) ^ c₁ := Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hQ : 1 ≤ ((L + 1) ^ c₁) ^ e := Nat.one_le_pow _ _ hP
  have hn' : n + 1 ≤ (l + 1) * (F₁ + 1) * (L + 1) ^ c₁ := by nlinarith [Nat.mul_le_mul_left l hP]
  have h₁ : (n + 1) ^ e ≤ ((l + 1) * (F₁ + 1)) ^ e * ((L + 1) ^ c₁) ^ e := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left hn' e
  have h₂ := Nat.mul_le_mul_left F₂' h₁
  have h₃ := Nat.mul_le_mul_left (F₂' * ((l + 1) * (F₁ + 1)) ^ e * ((L + 1) ^ c₁) ^ e) hP
  have h₄ := Nat.mul_le_mul_left (F₁ * (L + 1) ^ c₁) hQ
  rw [Nat.pow_add, Nat.pow_mul]
  calc F₁ * (L + 1) ^ c₁ + F₂' * (n + 1) ^ e
      ≤ F₁ * (L + 1) ^ c₁ * ((L + 1) ^ c₁) ^ e +
        F₂' * ((l + 1) * (F₁ + 1)) ^ e * ((L + 1) ^ c₁) ^ e * (L + 1) ^ c₁ := by
        rw [Nat.mul_one] at h₃ h₄
        rw [← Nat.mul_assoc] at h₂
        omega
    _ = _ := by ring

/-- Strongly uniform FPT-time computability is closed under composition along a computable
parameter bound. -/
theorem ComputableInStronglyUniformFPTTime.comp {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {κA : α → ℕ} {κB : β → ℕ} {f : α → β} {g : β → γ} {h : ℕ → ℕ}
    (hg : ComputableInStronglyUniformFPTTime g encB encC κB)
    (hf : ComputableInStronglyUniformFPTTime f encA encB κA)
    (hh : IsComputable h encNat encNat)
    (hκ : ∀ a, κB (f a) ≤ h (κA a)) :
    ComputableInStronglyUniformFPTTime (g ∘ f) encA encC κA := by
  obtain ⟨F₂, c₂, hF₂, _, hts₂⟩ := hg
  obtain ⟨F₁, c₁, hF₁, hc₁, hts₁⟩ := hf
  have hg_inO : ComputableInO g encB encC
      (fun b ↦ F₂ (κB b) * ((encB b).length + 1) ^ c₂)
      (fun b ↦ F₂ (κB b) * ((encB b).length + 1) ^ c₂) :=
    ComputableInO.of_bounds hts₂ 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
      (fun b ↦ (hts₂.length_le b).trans (by omega))
  have hf_inO : ComputableInO f encA encB
      (fun a ↦ F₁ (κA a) * ((encA a).length + 1) ^ c₁)
      (fun a ↦ F₁ (κA a) * ((encA a).length + 1) ^ c₁) :=
    ComputableInO.of_bounds hts₁ 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
      (fun a ↦ (hts₁.length_le a).trans (by omega))
  obtain ⟨l, _, hl⟩ := id hf_inO
  let F₂' (k : ℕ) : ℕ := cumulSum F₂ (h k)
  have hF₂'_comp : IsComputable F₂' encNat encNat := (IsComputable.cumulSum hF₂).comp hh
  have key (a : α) :
      F₁ (κA a) * ((encA a).length + 1) ^ c₁ +
        F₂ (κB (f a)) * ((encB (f a)).length + 1) ^ c₂ ≤
      (F₁ (κA a) + F₂' (κA a) * ((l + 1) * (F₁ (κA a) + 1)) ^ c₂) *
        ((encA a).length + 1) ^ (c₁ + c₁ * c₂) := by
    have hsub : F₂ (κB (f a)) ≤ F₂' (κA a) := le_cumulSum (hκ a)
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hsub) _).trans
      (fpt_comp_arith (hl a) (Nat.zero_le _))
  obtain ⟨d, hd, -⟩ := (hg_inO.comp hf_inO).mono_le key key
  let F_comp (k : ℕ) : ℕ :=
    d * ((F₁ k + F₂' k * ((l + 1) * (F₁ k + 1)) ^ c₂) + 1)
  have hF_comp : IsComputable F_comp encNat encNat := by
    have hbase := IsComputable.add_nat hF₁
      (IsComputable.mul_nat hF₂'_comp
        (IsComputable.pow_const_nat
          (IsComputable.mul_nat (ComputableInPolyTime.const (l + 1)).isComputable
            (IsComputable.add_nat hF₁ (ComputableInPolyTime.const 1).isComputable))
          c₂))
    exact IsComputable.mul_nat (ComputableInPolyTime.const d).isComputable
      (IsComputable.add_nat hbase (ComputableInPolyTime.const 1).isComputable)
  have hmono (a : α) :
      d * ((F₁ (κA a) + F₂' (κA a) * ((l + 1) * (F₁ (κA a) + 1)) ^ c₂) *
        ((encA a).length + 1) ^ (c₁ + c₁ * c₂) + 1) ≤
      F_comp (κA a) * ((encA a).length + 1) ^ (c₁ + c₁ * c₂) := by
    have hP := Nat.one_le_pow (c₁ + c₁ * c₂) _ (Nat.succ_pos (encA a).length)
    have := Nat.mul_le_mul_left d hP
    dsimp [F_comp]
    nlinarith
  exact ⟨F_comp, c₁ + c₁ * c₂, hF_comp, by omega, hd.mono hmono hmono⟩

/-- Preparing `(a, aux (κ a))` from `a` is computable in strongly uniform FPT time whenever `κ` is
polynomial-time and `aux` is `IsComputable`. -/
theorem ComputableInStronglyUniformFPTTime.pair_aux {α Aux : Type}
    {encA : α ↪ List Bool} {encAux : Aux ↪ List Bool} {κ : α → ℕ} {aux : ℕ → Aux}
    (hκ : ComputableInPolyTime κ encA encNat) (haux : IsComputable aux encNat encAux) :
    ComputableInStronglyUniformFPTTime (fun a ↦ (a, aux (κ a))) encA (encPair encA encAux) κ := by
  obtain ⟨t_a, s_a, ht_a, hs_a, hts_a⟩ := IsComputable.exists_computable_time haux
  let B_a (k : ℕ) : ℕ := t_a k + s_a k + 1
  have hB_comp : IsComputable B_a encNat encNat :=
    IsComputable.add_nat (IsComputable.add_nat ht_a hs_a)
      (ComputableInPolyTime.const 1).isComputable
  have haux_fpt : ComputableInStronglyUniformFPTTime aux encNat encAux id := by
    refine ⟨B_a, 1, hB_comp, Nat.one_pos, hts_a.mono (fun k ↦ ?_) (fun k ↦ ?_)⟩
    · calc t_a k ≤ B_a k * 1 := by dsimp [B_a]; omega
        _ ≤ B_a k * ((encNat k).length + 1) ^ 1 :=
          Nat.mul_le_mul_left _ (by simp)
    · calc s_a k ≤ B_a k * 1 := by dsimp [B_a]; omega
        _ ≤ B_a k * ((encNat k).length + 1) ^ 1 :=
          Nat.mul_le_mul_left _ (by simp)
  have hcomp : ComputableInStronglyUniformFPTTime (fun a ↦ aux (κ a)) encA encAux κ :=
    haux_fpt.comp (ComputableInStronglyUniformFPTTime.of_computableInPolyTime hκ κ)
      (ComputableInPolyTime.id').isComputable (fun _ ↦ le_rfl)
  obtain ⟨F₁, c₁, hF₁, hc₁, hts₁⟩ := hcomp
  obtain ⟨hid_deg, _, hid_c⟩ := (ComputableInPolyTime.id' (encIn := encA)).exists_degree
  obtain ⟨kid, hts_id, -⟩ := hid_c.inO
  obtain ⟨kp, hp⟩ := PairEncoding.pair_mono (enc := encPair encA encAux) hts_id hts₁
  let F₂ (k : ℕ) : ℕ := kp * (kid * 2 + F₁ k + 1)
  have hF₂ : IsComputable F₂ encNat encNat :=
    IsComputable.mul_nat (ComputableInPolyTime.const kp).isComputable
      (IsComputable.add_nat
        (IsComputable.add_nat (ComputableInPolyTime.const (kid * 2)).isComputable hF₁)
        (ComputableInPolyTime.const 1).isComputable)
  have hle (a : α) :
      kp * (kid * (((encA a).length + 1) ^ hid_deg + 1) +
        F₁ (κ a) * ((encA a).length + 1) ^ c₁ + 1) ≤
      F₂ (κ a) * ((encA a).length + 1) ^ (hid_deg + c₁) := by
    let P := ((encA a).length + 1) ^ (hid_deg + c₁)
    have hP₁ : ((encA a).length + 1) ^ hid_deg ≤ P :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hP₂ : ((encA a).length + 1) ^ c₁ ≤ P :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hP₀ : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hinner :
        kid * (((encA a).length + 1) ^ hid_deg + 1) +
          F₁ (κ a) * ((encA a).length + 1) ^ c₁ + 1 ≤
        (kid * 2 + F₁ (κ a) + 1) * P := by
      calc kid * (((encA a).length + 1) ^ hid_deg + 1) +
              F₁ (κ a) * ((encA a).length + 1) ^ c₁ + 1
          ≤ kid * (P + P) + F₁ (κ a) * P + P := by
            have := Nat.mul_le_mul_left kid (Nat.add_le_add hP₁ hP₀)
            have := Nat.mul_le_mul_left (F₁ (κ a)) hP₂
            omega
        _ = (kid * 2 + F₁ (κ a) + 1) * P := by ring
    calc kp * (kid * (((encA a).length + 1) ^ hid_deg + 1) +
            F₁ (κ a) * ((encA a).length + 1) ^ c₁ + 1)
        ≤ kp * ((kid * 2 + F₁ (κ a) + 1) * P) := Nat.mul_le_mul_left kp hinner
      _ = F₂ (κ a) * P := by dsimp [F₂]; ring
  exact ComputableInStronglyUniformFPTTime.of_time hF₂ (by omega)
    (hp.mono hle (fun _ ↦ le_rfl))

/-- Any polynomial-time algorithm taking `(a, pad (κ a))` (with `pad` in unary and `IsComputable`)
runs in strongly uniform FPT time on `a`. -/
theorem ComputableInStronglyUniformFPTTime.of_paddedPolyTime {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κ : α → ℕ} {pad : ℕ → ℕ} {g : α × ℕ → β}
    (hκ : ComputableInPolyTime κ encA encNat)
    (hpad : IsComputable pad encNat encNat)
    (hg : ComputableInPolyTime g (encPair encA encUnary) encB) :
    ComputableInStronglyUniformFPTTime (fun a ↦ g (a, pad (κ a))) encA encB κ :=
  (ComputableInStronglyUniformFPTTime.of_computableInPolyTime hg (fun p ↦ p.2)).comp
    (ComputableInStronglyUniformFPTTime.pair_aux hκ (isComputable_nat_to_unary.comp hpad))
    hpad (fun _ ↦ le_rfl)

/-- Canonical carrier for a **parameterized counting problem** `(F, k)`
: an injective binary instance encoding `enc : α ↪ List Bool`, an
exact count `count : α → ℕ`, and a polynomial-time computable parameterization `param : α → ℕ`.
-/
structure ParameterizedCountingProblem (α : Type*) where
  /-- Injective binary instance encoding. -/
  enc : α ↪ List Bool
  /-- Exact solution count `F(x) : ℕ`. -/
  count : α → ℕ
  /-- Parameterization `k(x) : ℕ`. -/
  param : α → ℕ
  /-- Polynomial-time computability of the parameterization `k`. -/
  param_polyTime : ComputableInPolyTime param enc encNat

/-- Fixed-parameter tractability (`InFPT`) of a `ParameterizedCountingProblem`: `P.count` is
computable in deterministic time `f (P.param x) * ((P.enc x).length + 1) ^ c` for some computable
function `f : ℕ → ℕ` and constant `c > 0`. -/
@[expose] def ParameterizedCountingProblem.InFPT {α : Type*}
    (P : ParameterizedCountingProblem α) : Prop :=
  ∃ (f : ℕ → ℕ) (c : ℕ) (s : α → ℕ),
    IsComputable f encNat encNat ∧
    0 < c ∧
    ComputableInTimeAndSpace P.count P.enc encNat
      (fun x ↦ f (P.param x) * ((P.enc x).length + 1) ^ c) s

/-- Equivalence between `P.InFPT` and `ComputableInStronglyUniformFPTTime P.count P.enc encNat
P.param`. -/
theorem ParameterizedCountingProblem.inFPT_iff_stronglyUniform {α : Type*}
    (P : ParameterizedCountingProblem α) :
    P.InFPT ↔ ComputableInStronglyUniformFPTTime P.count P.enc encNat P.param :=
  ⟨fun ⟨_f, _c, _, hf, hc, hts⟩ ↦ ComputableInStronglyUniformFPTTime.of_time hf hc hts,
    fun ⟨f, c, hf, hc, hts⟩ ↦ ⟨f, c, _, hf, hc, hts⟩⟩

/-- Every `InFPT` parameterized counting problem is computable in
`Cslib.Complexity.ComputableInFPTTime`. -/
theorem ParameterizedCountingProblem.InFPT.computableInFPTTime {α : Type*}
    {P : ParameterizedCountingProblem α} (h : P.InFPT) :
    ComputableInFPTTime P.count P.enc encNat P.param :=
  ((P.inFPT_iff_stronglyUniform).mp h).computableInFPTTime

/-- Any polynomial-time computable counting problem is `InFPT`. -/
theorem ParameterizedCountingProblem.InFPT.of_computableInPolyTime {α : Type}
    {P : ParameterizedCountingProblem α} (h : ComputableInPolyTime P.count P.enc encNat) :
    P.InFPT :=
  (P.inFPT_iff_stronglyUniform).mpr
    (ComputableInStronglyUniformFPTTime.of_computableInPolyTime h P.param)

/-- Constructor for `P.InFPT` from a polynomial-time algorithm taking `(x, pad (P.param x))` with
`pad : ℕ → ℕ` computable and unary-encoded. -/
theorem ParameterizedCountingProblem.InFPT.of_paddedPolyTime {α : Type}
    {P : ParameterizedCountingProblem α} {pad : ℕ → ℕ} {alg : α × ℕ → ℕ}
    (hpad : IsComputable pad encNat encNat)
    (halg : ComputableInPolyTime alg (encPair P.enc encUnary) encNat)
    (hval : ∀ x, alg (x, pad (P.param x)) = P.count x) :
    P.InFPT := by
  rw [P.inFPT_iff_stronglyUniform]
  obtain ⟨F, c, hF, hc, k, State, hfin, tm, htm⟩ :=
    ComputableInStronglyUniformFPTTime.of_paddedPolyTime P.param_polyTime hpad halg
  exact ⟨F, c, hF, hc, k, State, hfin, tm, fun x ↦ hval x ▸ htm x⟩

/-- Every `InFPT` problem admits a polynomial-time word simulator `sim : List Bool × ℕ → ℕ` on
`encPair encBits encUnary` and a computable monotone budget `pad : ℕ → ℕ` such that
`sim (P.enc x, B) = P.count x` for all `B ≥ pad (P.param x)`. -/
theorem ParameterizedCountingProblem.InFPT.exists_paddedWordSimulator {α : Type}
    {P : ParameterizedCountingProblem α} (h : P.InFPT) :
    ∃ (pad : ℕ → ℕ) (sim : List Bool × ℕ → ℕ),
      IsComputable pad encNat encNat ∧
      Monotone pad ∧
      ComputableInPolyTime sim (encPair encBits encUnary) encNat ∧
      ∀ (x : α) {B : ℕ}, pad (P.param x) ≤ B → sim (P.enc x, B) = P.count x := by
  classical
  obtain ⟨f, c, _, hf, _, k, State, hfin, tm, htm⟩ := h
  let _ : Finite State := hfin
  let M₀ := MultiTapePTM.ofDeterministic (Oracle := Unit) tm
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := State) (Oracle := Unit)
  let budget (p : List Bool × ℕ) : ℕ := p.2 * (p.1.length + 1) ^ c
  have hbudget : ComputableInPolyTime budget (encPair encBits encUnary) encUnary := by
    have hpoly : ComputableInPolyTime (fun p : List Bool × ℕ ↦ (p.1.length + 1) ^ c)
        (encPair encBits encUnary) encUnary :=
      ((ComputableInPolyTime.unary_eval ((Polynomial.X + 1) ^ c)).comp
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.fst encBits encUnary))).of_enc_eq fun p ↦ by simp
    exact ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.snd encBits encUnary).prod hpoly)
  have hbudget_pb : PolyBounded (fun p : List Bool × ℕ ↦ (encPair encBits encUnary p).length)
      budget := by
    simpa only [encUnary_apply, List.length_replicate] using hbudget.polyBounded_length
  have hinit : ComputableInPolyTime
      (fun p : List Bool × ℕ ↦ FiniteConfig.init (k := k) (Oracle := Unit) tm.q₀ p.1)
      (encPair encBits encUnary) encFiniteConfig :=
    ComputableInPolyTime.finiteConfig_init (ComputableInPolyTime.fst encBits encUnary) tm.q₀
  let stepF := M₀.answerStep (fun _ ↦ [false])
  have hstepF_pt : ComputableInPolyTime stepF encFiniteConfig encFiniteConfig :=
    M₀.computableInPolyTime_answerStep (ComputableInPolyTime.const false)
  have hspace (w : List Bool) (i : ℕ) :
      FiniteConfig.SpaceBound w.length i 1 (stepF^[i] (FiniteConfig.init M₀.initial w)) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact M₀.spaceBound_answerStep (fun _ ↦ false) ih
  have hit := ComputableInPolyTime.iterate hbudget hinit hstepF_pt
    ((PolyBounded.const cf).mul
      ((((PolyBounded.of_forall_le 1 1 fun p ↦
        (length_le_encPair_left encBits encUnary p).trans (by simp)).add hbudget_pb).add
        (.const 1)).add (.const 1)))
    fun p i hi ↦ (hcf _ _ _ _ (hspace p.1 i)).trans
      (Nat.mul_le_mul_left cf (by simp only [encBits_apply] at *; omega))
  let sim (p : List Bool × ℕ) : ℕ :=
    ofBits (stepF^[budget p] (FiniteConfig.init tm.q₀ p.1)).tapes.output
  have hout_pt : ComputableInPolyTime
      (fun cfg : FiniteConfig k Bool State Unit ↦ cfg.tapes.output)
      encFiniteConfig encBits := by fun_prop
  refine ⟨cumulSum f, sim, IsComputable.cumulSum hf, monotone_cumulSum f,
    ComputableInPolyTime.bitsToNat.comp (hout_pt.comp hit),
    fun x {B} hB ↦ ?_⟩
  have hfB : f (P.param x) ≤ B := (le_cumulSum le_rfl).trans hB
  have hle : f (P.param x) * ((P.enc x).length + 1) ^ c ≤ budget (P.enc x, B) :=
    Nat.mul_le_mul_right _ hfB
  have hinterp := M₀.interpret_run_pure_false (fun _ ↦ [false]) (budget (P.enc x, B)) (P.enc x)
  have hdet := ofDeterministic_interpret_run_eq tm (fun _ ↦ [false]) (budget (P.enc x, B))
    (P.enc x)
  have hrun := ((htm x).runFrom_of_le hle).2
  dsimp only [sim, stepF]
  change ofBits ((M₀.answerStep (fun _ ↦ [false]))^[budget (P.enc x, B)]
    (FiniteConfig.init M₀.initial (P.enc x))).tapes.output = P.count x
  rw [← hinterp, hdet, hrun]
  exact Nat.foldr_bit_bits (P.count x)

end ProblemsAndFPT

/-! ### 3. FPT Parsimonious Reductions -/

section Parsimonious

/-- **FPT Parsimonious Reduction**: a map
`R : α → β` preserving counts (`P.count x = Q.count (R x)`), computable in strongly uniform FPT
time, with `Q.param (R x) ≤ g (P.param x)` for a computable function `g : ℕ → ℕ`.
-/
@[expose] def FPTParsimoniousReducible {α β : Type*} (P : ParameterizedCountingProblem α)
    (Q : ParameterizedCountingProblem β) : Prop :=
  ∃ R : α → β,
    (∀ x, P.count x = Q.count (R x)) ∧
    ComputableInStronglyUniformFPTTime R P.enc Q.enc P.param ∧
    ∃ g : ℕ → ℕ, IsComputable g encNat encNat ∧ ∀ x, Q.param (R x) ≤ g (P.param x)

/-- Reflexivity of `FPTParsimoniousReducible`. -/
@[refl]
theorem FPTParsimoniousReducible.refl {α : Type} (P : ParameterizedCountingProblem α) :
    FPTParsimoniousReducible P P :=
  ⟨id, fun _ ↦ rfl,
    ComputableInStronglyUniformFPTTime.of_computableInPolyTime ComputableInPolyTime.id' P.param,
    id, ComputableInPolyTime.id'.isComputable, fun _ ↦ le_rfl⟩

/-- Transitivity of `FPTParsimoniousReducible`. -/
@[trans]
theorem FPTParsimoniousReducible.trans {α β γ : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {S : ParameterizedCountingProblem γ}
    (hPQ : FPTParsimoniousReducible P Q) (hQS : FPTParsimoniousReducible Q S) :
    FPTParsimoniousReducible P S := by
  obtain ⟨R₁, hcnt₁, hfpt₁, g₁, hg₁, hparam₁⟩ := hPQ
  obtain ⟨R₂, hcnt₂, hfpt₂, g₂, hg₂, hparam₂⟩ := hQS
  refine ⟨R₂ ∘ R₁, fun x ↦ (hcnt₁ x).trans (hcnt₂ (R₁ x)),
    hfpt₂.comp hfpt₁ hg₁ hparam₁,
    fun k ↦ cumulSum g₂ (g₁ k), (IsComputable.cumulSum hg₂).comp hg₁,
    fun x ↦ (hparam₂ (R₁ x)).trans (le_cumulSum (hparam₁ x))⟩

/-- Polynomial-time count-preserving maps with computable parameter bounds are FPT parsimonious
reductions. -/
theorem FPTParsimoniousReducible.of_computableInPolyTime {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {R : α → β} (hcnt : ∀ x, P.count x = Q.count (R x))
    (hR : ComputableInPolyTime R P.enc Q.enc)
    {g : ℕ → ℕ} (hg : IsComputable g encNat encNat)
    (hparam : ∀ x, Q.param (R x) ≤ g (P.param x)) :
    FPTParsimoniousReducible P Q :=
  ⟨R, hcnt, ComputableInStronglyUniformFPTTime.of_computableInPolyTime hR P.param, g, hg, hparam⟩

/-- `InFPT` is closed downwards under `FPTParsimoniousReducible`. -/
theorem FPTParsimoniousReducible.inFPT {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    (hPQ : FPTParsimoniousReducible P Q) (hQ : Q.InFPT) : P.InFPT := by
  obtain ⟨R, hcnt, hfptR, g, hg, hparam⟩ := hPQ
  rw [P.inFPT_iff_stronglyUniform]
  have hQ' := (Q.inFPT_iff_stronglyUniform).mp hQ
  obtain ⟨F, c, hF, hc, k, State, hfin, tm, htm⟩ := hQ'.comp hfptR hg hparam
  exact ⟨F, c, hF, hc, k, State, hfin, tm, fun x ↦ (hcnt x).symm ▸ htm x⟩

end Parsimonious

end Computability

end CslibFrontier
