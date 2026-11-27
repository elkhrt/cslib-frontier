/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import CslibFrontier.Computability.Complexity.Parameterized.Counting

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Adaptive FPT Turing Reductions, `#W[1]`, and Canonical `#k-Clique` / `#k-Matching` Carriers

This module develops adaptive multi-tape FPT Turing reductions, `#W[1]` and `#W[1]`-hardness, and
the canonical `#k-Clique` and `#k-Matching` parameterized counting problems under standard Lean
axioms :

1. **`IsCountingOracleFor` and `FPTTuringReducible`**: choice-free relational oracle specification
   and adaptive multi-tape FPT Turing reductions, with auxiliary-input, unary-padded,
   polynomial-time, and batch query constructors, parsimonious-to-Turing lifting, transitivity
   (`FPTTuringReducible.trans`), and downward closure of `InFPT` (`FPTTuringReducible.inFPT`).
2. **`sharpKCliqueProblem`, `SharpWOne`, and `SharpWOneHard`**: `#W[1]`-completeness of
   `#k-Clique` and hardness/intractability transfer across `FPTTuringReducible`.
3. **`matchingCount` and `sharpKMatchingProblem`**: exact $k$-matching count on `SimpleGraph`,
   bijection with $k$-subsets of pairwise vertex-disjoint edges, boundary evaluations, and the
   canonical `#k-Matching` problem carrier.

## Main definitions

* `CslibFrontier.Computability.IsCountingOracleFor`,
  `CslibFrontier.Computability.FPTTuringReducible`,
  `CslibFrontier.Computability.queryCount`,
  `CslibFrontier.Computability.queryCountList`.
* `CslibFrontier.Computability.sharpKCliqueCount`,
  `CslibFrontier.Computability.sharpKCliqueProblem`,
  `CslibFrontier.Computability.SharpWOne`,
  `CslibFrontier.Computability.SharpWOneHard`.
* `CslibFrontier.SimpleGraph.matchingCount`,
  `CslibFrontier.Computability.sharpKMatchingProblem`.

## Main results

* `CslibFrontier.Computability.IsCountingOracleFor.unique`,
  `CslibFrontier.Computability.existsUnique_isCountingOracleFor`.
* `CslibFrontier.Computability.FPTTuringReducible.of_auxOraclePPT`,
  `CslibFrontier.Computability.FPTTuringReducible.of_paddedOraclePPT`,
  `CslibFrontier.Computability.FPTTuringReducible.of_oraclePPT`,
  `CslibFrontier.Computability.FPTTuringReducible.of_paddedBatchQueries`,
  `CslibFrontier.Computability.FPTTuringReducible.of_batchQueries`,
  `CslibFrontier.Computability.FPTParsimoniousReducible.fptTuringReducible_of_polyBounded`,
  `CslibFrontier.Computability.FPTTuringReducible.refl_of_polyBounded`,
  `CslibFrontier.Computability.FPTTuringReducible.trans`,
  `CslibFrontier.Computability.FPTTuringReducible.inFPT`.
* `CslibFrontier.Computability.sharpWOne_sharpKCliqueProblem`,
  `CslibFrontier.Computability.sharpWOneHard_sharpKCliqueProblem`,
  `CslibFrontier.Computability.SharpWOne.fptTuringReducible_sharpKClique`,
  `CslibFrontier.Computability.SharpWOneHard.trans`,
  `CslibFrontier.Computability.SharpWOneHard.not_inFPT_of_not_inFPT_sharpKClique`.
* `CslibFrontier.SimpleGraph.matchingCount_eq_card_disjoint_edgeFinset`,
  `CslibFrontier.SimpleGraph.matchingCount_zero`,
  `CslibFrontier.SimpleGraph.matchingCount_bot_succ`,
  `CslibFrontier.SimpleGraph.matchingCount_eq_zero_of_card_lt_two_mul`,
  `CslibFrontier.SimpleGraph.matchingCount_top_two_one`.
-/

public section

open Cslib Cslib.Complexity Cslib.Probability
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapePTM

namespace CslibFrontier

namespace Computability

/-! ### 1. Adaptive FPT Turing Reductions and Program Constructors -/

section TuringReductions

/-- Choice-free relational specification of the deterministic word-query counting oracle for a
parameterized counting problem `Q`: every encoded instance `Q.enc y` receives
`encNat (Q.count y)` and every non-instance word receives `[]`. -/
def IsCountingOracleFor {β : Type*} (Q : ParameterizedCountingProblem β)
    (ans : Unit × List Bool → List Bool) : Prop :=
  (∀ (u : Unit) (y : β), ans (u, Q.enc y) = encNat (Q.count y)) ∧
    (∀ (u : Unit) (w : List Bool), (∀ y : β, Q.enc y ≠ w) → ans (u, w) = [])

/-- Injectivity of `Q.enc` forces uniqueness of any oracle satisfying `IsCountingOracleFor Q`. -/
theorem IsCountingOracleFor.unique {β : Type*} {Q : ParameterizedCountingProblem β}
    {ans₁ ans₂ : Unit × List Bool → List Bool}
    (h₁ : IsCountingOracleFor Q ans₁) (h₂ : IsCountingOracleFor Q ans₂) :
    ans₁ = ans₂ := by
  funext ⟨u, w⟩
  by_cases hex : ∃ y : β, Q.enc y = w
  · obtain ⟨y, rfl⟩ := hex
    rw [h₁.1 u y, h₂.1 u y]
  · push Not at hex
    rw [h₁.2 u w hex, h₂.2 u w hex]

private noncomputable def canonicalCountingOracle {β : Type*}
    (Q : ParameterizedCountingProblem β) : Unit × List Bool → List Bool := fun q ↦
  let _ := Classical.propDecidable
  if h : ∃ y : β, Q.enc y = q.2 then encNat (Q.count h.choose) else []

private lemma isCountingOracleFor_canonical {β : Type*} (Q : ParameterizedCountingProblem β) :
    IsCountingOracleFor Q (canonicalCountingOracle Q) := by
  classical
  refine ⟨fun u y ↦ ?_, fun u w hno ↦ ?_⟩
  · unfold canonicalCountingOracle
    split_ifs with hex
    · rw [Q.enc.injective hex.choose_spec]
    · exact absurd ⟨y, rfl⟩ hex
  · unfold canonicalCountingOracle
    split_ifs with hex
    · obtain ⟨y, hy⟩ := hex
      exact absurd hy (hno y)
    · rfl

/-- Every parameterized counting problem `Q` admits a unique deterministic word-query oracle
satisfying `IsCountingOracleFor Q`. -/
theorem existsUnique_isCountingOracleFor {β : Type*} (Q : ParameterizedCountingProblem β) :
    ∃! ans : Unit × List Bool → List Bool, IsCountingOracleFor Q ans :=
  ⟨canonicalCountingOracle Q, isCountingOracleFor_canonical Q,
    fun _ hans ↦ hans.unique (isCountingOracleFor_canonical Q)⟩

/-- **Adaptive FPT Turing Reduction**:
a deterministic multi-tape oracle Turing machine `M` (`MultiTapePTM` with coins fixed to `false`)
that, against the unique counting oracle for `Q`, computes `encNat (P.count x)` within
`f (P.param x) * ((P.enc x).length + 1) ^ c` steps (`f` computable, `c > 0`) such that every
queried word is an encoded instance `Q.enc y` satisfying `Q.param y ≤ g (P.param x)` (`g`
computable).
-/
def FPTTuringReducible {α β : Type} (P : ParameterizedCountingProblem α)
    (Q : ParameterizedCountingProblem β) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (M : MultiTapePTM k Bool Control Unit) (f g : ℕ → ℕ) (c : ℕ),
    IsComputable f encNat encNat ∧
    IsComputable g encNat encNat ∧
    0 < c ∧
    ∀ (ans : Unit × List Bool → List Bool), IsCountingOracleFor Q ans →
      ∀ x : α,
        let fuel := f (P.param x) * ((P.enc x).length + 1) ^ c
        let run := M.run (pure false) (fun op word ↦ OracleComp.query (op, word)) fuel (P.enc x)
        OracleComp.interpret (m := Id) ans run = encNat (P.count x) ∧
        ∀ q ∈ OracleComp.queriesWith ans run,
          ∃ y : β, Q.enc y = q.2 ∧ Q.param y ≤ g (P.param x)

private def logStep {ι : Type} (answer : ι → List Bool) (q : ι) (s : List ι) :
    List Bool × List ι :=
  (answer q, s ++ [q])

private lemma run_interpret_logStep {ι γ : Type} (answer : ι → List Bool)
    (prog : OracleComp (fun _ : ι ↦ List Bool) γ) (s : List ι) :
    (OracleComp.interpret (m := StateM (List ι)) (fun q ↦ (logStep answer q : StateM _ _))
      prog).run s =
    (OracleComp.interpret (m := Id) answer prog, s ++ OracleComp.queriesWith answer prog) := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure b =>
    change (b, s) = (b, s ++ [])
    rw [List.append_nil]
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      OracleComp.interpret_id_query_bind, OracleComp.queriesWith_query_bind]
    change (OracleComp.interpret (m := StateM (List ι)) _ (cont (answer q))).run (s ++ [q]) = _
    rw [ih (answer q) (s ++ [q]), List.append_assoc, List.singleton_append]

private lemma runWith_logStep_interpret_query {γ : Type}
    (answer : Unit × List Bool → List Bool) (prog : WordQueryComp Unit γ)
    (s : List (Unit × List Bool)) :
    ProbOracleComp.runWith (fun q st ↦ PMF.pure (logStep answer q st))
      (OracleComp.interpret ProbOracleComp.query prog) s =
    PMF.pure (OracleComp.interpret (m := Id) answer prog,
      s ++ OracleComp.queriesWith answer prog) := by
  rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  suffices ∀ (p : WordQueryComp Unit γ) (st : List (Unit × List Bool)),
      (OracleComp.interpret
        (fun i ↦ OracleComp.sumHandler (fun n ↦ StateT.lift (ProbComp.unifOracle n))
          (fun q st' ↦ PMF.pure (logStep answer q st')) (Sum.inr i)) p).run st =
      PMF.pure ((OracleComp.interpret (m := StateM _) (fun q ↦ (logStep answer q : StateM _ _))
        p).run st) by
    rw [this prog s, run_interpret_logStep]
  intro p st
  induction p using PFunctor.FreeM.induction generalizing st with
  | pure b => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, OracleComp.interpret_bind, OracleComp.interpret_query,
      StateT.run_bind]
    exact (PMF.pure_bind _ _).trans (ih _ _)

private lemma computesTidily_run_pure_false {k : ℕ} {Control : Type}
    (M : MultiTapePTM k Bool Control Unit) (w : List Bool) (T : ℕ)
    (prog : WordQueryComp Unit (List Bool))
    (hM : M.ComputesTidily w T (OracleComp.interpret ProbOracleComp.query prog))
    (answer : Unit × List Bool → List Bool) :
    let run := M.run (pure false) (fun op word ↦ OracleComp.query (op, word)) T w
    OracleComp.interpret (m := Id) answer run = OracleComp.interpret (m := Id) answer prog ∧
      OracleComp.queriesWith answer run = OracleComp.queriesWith answer prog := by
  have hlaw := hM.runOracle (fun q st ↦ PMF.pure (logStep answer q st))
    ([] : List (Unit × List Bool))
  rw [runWith_logStep_interpret_query, List.nil_append] at hlaw
  have hmem := M.mem_support_runConfigFrom_pure_stateM false (logStep answer)
    ([] : List (Unit × List Bool)) T (M.initialConfig w)
  have hmap : Prod.map (fun cfg : Config k Bool Control Unit w ↦ cfg.tapes.output) id
      ((OracleComp.interpret (m := StateM _) (fun q ↦ (logStep answer q : StateM _ _))
        (M.runConfigFrom (pure false) (fun op word ↦ OracleComp.query (op, word)) T
          (M.initialConfig w))).run []) ∈
      (ProbOracleComp.runWith (fun q st ↦ PMF.pure (logStep answer q st))
        (M.runOracle T w) []).support := by
    simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
      ProbOracleComp.runWith_map, PMF.mem_support_map_iff]
    exact ⟨_, hmem, rfl⟩
  rw [hlaw, PMF.mem_support_pure_iff] at hmap
  have hrun_eq :
      Prod.map (fun cfg : Config k Bool Control Unit w ↦ cfg.tapes.output) id
        ((OracleComp.interpret (m := StateM _) (fun q ↦ (logStep answer q : StateM _ _))
          (M.runConfigFrom (pure false) (fun op word ↦ OracleComp.query (op, word)) T
            (M.initialConfig w))).run []) =
      (OracleComp.interpret (m := Id) answer
        (M.run (pure false) (fun op word ↦ OracleComp.query (op, word)) T w),
        OracleComp.queriesWith answer
          (M.run (pure false) (fun op word ↦ OracleComp.query (op, word)) T w)) := by
    rw [run_interpret_logStep, List.nil_append, MultiTapePTM.run, MultiTapePTM.runFrom,
      OracleComp.interpret_map, OracleComp.queriesWith_map]
    rfl
  rw [hrun_eq] at hmap
  exact Prod.mk.inj hmap

private lemma tidy_comp_time_bound (T₀ L c₀ c₁ d₁ : ℕ) :
    5 * (T₀ * (L + 1) ^ c₀) + c₁ * (T₀ * (L + 1) ^ c₀ + 1) ^ d₁ + 9 ≤
      (5 * T₀ + c₁ * (T₀ + 1) ^ d₁ + 10) * (L + 1) ^ (c₀ + c₀ * d₁) := by
  let t₀ := T₀ * (L + 1) ^ c₀
  let c := c₀ + c₀ * d₁
  have hP₀ : 1 ≤ (L + 1) ^ c₀ := Nat.one_le_pow _ _ (Nat.succ_pos L)
  have ht₀_add : t₀ + 1 ≤ (T₀ + 1) * (L + 1) ^ c₀ := by dsimp [t₀]; nlinarith
  have hpow : (t₀ + 1) ^ d₁ ≤ (T₀ + 1) ^ d₁ * ((L + 1) ^ c₀) ^ d₁ := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left ht₀_add d₁
  have hL₁ : (L + 1) ^ c₀ ≤ (L + 1) ^ c :=
    Nat.pow_le_pow_right (Nat.succ_pos L) (by dsimp [c]; omega)
  have hL₂ : ((L + 1) ^ c₀) ^ d₁ ≤ (L + 1) ^ c := by
    rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (Nat.succ_pos L) (by dsimp [c]; omega)
  have hL₃ : 1 ≤ (L + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos L)
  have h1 : 5 * t₀ ≤ 5 * T₀ * (L + 1) ^ c := by
    dsimp [t₀]; rw [← mul_assoc]; exact Nat.mul_le_mul_left (5 * T₀) hL₁
  have h2 : c₁ * (t₀ + 1) ^ d₁ ≤ c₁ * (T₀ + 1) ^ d₁ * (L + 1) ^ c :=
    calc c₁ * (t₀ + 1) ^ d₁
        ≤ c₁ * ((T₀ + 1) ^ d₁ * ((L + 1) ^ c₀) ^ d₁) := Nat.mul_le_mul_left c₁ hpow
      _ = c₁ * (T₀ + 1) ^ d₁ * ((L + 1) ^ c₀) ^ d₁ := (mul_assoc _ _ _).symm
      _ ≤ c₁ * (T₀ + 1) ^ d₁ * (L + 1) ^ c := Nat.mul_le_mul_left _ hL₂
  have h3 : 9 ≤ 10 * (L + 1) ^ c := by omega
  calc 5 * t₀ + c₁ * (t₀ + 1) ^ d₁ + 9
      ≤ 5 * T₀ * (L + 1) ^ c + c₁ * (T₀ + 1) ^ d₁ * (L + 1) ^ c + 10 * (L + 1) ^ c :=
        Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ = (5 * T₀ + c₁ * (T₀ + 1) ^ d₁ + 10) * (L + 1) ^ c := by ring

/-- **General Auxiliary-Input Program Constructor for `FPTTuringReducible`**. -/
theorem FPTTuringReducible.of_auxOraclePPT {α β Aux : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {encAux : Aux ↪ List Bool} {aux : ℕ → Aux} {g : ℕ → ℕ}
    (haux : IsComputable aux encNat encAux)
    (hg : IsComputable g encNat encNat)
    (prog : α × Aux → WordQueryComp Unit ℕ)
    (hprog : IsOraclePPTOn (encPair P.enc encAux) encNat
      (fun p ↦ OracleComp.interpret ProbOracleComp.query (prog p)))
    (hval : ∀ ans, IsCountingOracleFor Q ans → ∀ x : α,
      OracleComp.interpret (m := Id) ans (prog (x, aux (P.param x))) = P.count x)
    (hq : ∀ ans, IsCountingOracleFor Q ans → ∀ x : α,
      ∀ q ∈ OracleComp.queriesWith ans (prog (x, aux (P.param x))),
        ∃ y : β, Q.enc y = q.2 ∧ Q.param y ≤ g (P.param x)) :
    FPTTuringReducible P Q := by
  let encMid := encPair P.enc encAux
  obtain ⟨F₀, c₀, hF₀, hc₀, k₀, State₀, hfin₀, tm₀, htm₀⟩ :=
    ComputableInStronglyUniformFPTTime.pair_aux P.param_polyTime haux
  let _ : Finite State₀ := hfin₀
  let M₀ : MultiTapePTM (k₀ + k₀) Bool _ Unit :=
    MultiTapePTM.ofDeterministic (tidy false true tm₀)
  obtain ⟨_, k₁, Control₁, hfin₁, M₁, c₁, d₁, hM₁⟩ := hprog.oraclePhase
  let _ : Finite Control₁ := hfin₁
  let M := M₁.tidyComp M₀ true
  let T₀_fn (k : ℕ) : ℕ := 5 * F₀ k + 8 * k₀ + 5
  have hT₀_comp : IsComputable T₀_fn encNat encNat :=
    IsComputable.add_nat
      (IsComputable.add_nat
        (IsComputable.mul_nat (ComputableInPolyTime.const 5).isComputable hF₀)
        (ComputableInPolyTime.const (8 * k₀)).isComputable)
      (ComputableInPolyTime.const 5).isComputable
  let f (k : ℕ) : ℕ := 5 * T₀_fn k + c₁ * (T₀_fn k + 1) ^ d₁ + 10
  have hf_comp : IsComputable f encNat encNat :=
    IsComputable.add_nat
      (IsComputable.add_nat
        (IsComputable.mul_nat (ComputableInPolyTime.const 5).isComputable hT₀_comp)
        (IsComputable.mul_nat (ComputableInPolyTime.const c₁).isComputable
          (IsComputable.pow_const_nat
            (IsComputable.add_nat hT₀_comp (ComputableInPolyTime.const 1).isComputable) d₁)))
      (ComputableInPolyTime.const 10).isComputable
  let c : ℕ := c₀ + c₀ * d₁
  refine ⟨_, _, inferInstance, M, f, g, c, hf_comp, hg, by omega, fun ans hans x ↦ ?_⟩
  let p : α × Aux := (x, aux (P.param x))
  let L := (P.enc x).length
  let t₀ := T₀_fn (P.param x) * (L + 1) ^ c₀
  have htidy₀ : M₀.ComputesTidily (P.enc x) t₀ (pure (encMid p)) := by
    have hraw := ComputesTidily.of_deterministic (Operation := Unit)
      ((htm₀ x).computesTidily_tidy Bool.false_ne_true)
    refine hraw.mono ?_
    have hP : 1 ≤ (L + 1) ^ c₀ := Nat.one_le_pow _ _ (Nat.succ_pos L)
    dsimp [t₀, T₀_fn, L]
    nlinarith
  have hcomp_tidy : M.ComputesTidily (P.enc x) (5 * t₀ + c₁ * (t₀ + 1) ^ d₁ + 9)
      ((pure p : WordOracleComp Unit (α × Aux)) >>=
        fun p' ↦ encNat <$> OracleComp.interpret ProbOracleComp.query (prog p')) := by
    refine ComputesTidily.comp_encoded encMid true
      (by simpa only [map_pure] using htidy₀)
      (fun p' _ oracle s s' hp' ↦ ?_)
    rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hp'
    obtain ⟨rfl, _⟩ := Prod.mk.inj hp'
    have hlen : (encPair P.enc encAux p).length ≤ t₀ :=
      htidy₀.length_output_le (s' := s') oracle s'
        (by rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff])
    exact (hM₁ p).mono (Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (by omega) d₁))
  have htime_le : 5 * t₀ + c₁ * (t₀ + 1) ^ d₁ + 9 ≤ f (P.param x) * (L + 1) ^ c :=
    tidy_comp_time_bound (T₀_fn (P.param x)) L c₀ c₁ d₁
  have hprog_eq :
      ((pure p : WordOracleComp Unit (α × Aux)) >>=
        fun p' ↦ encNat <$> OracleComp.interpret ProbOracleComp.query (prog p')) =
      OracleComp.interpret ProbOracleComp.query (encNat <$> prog p) := by
    simp [OracleComp.interpret_map]
  have htidy_full := (hprog_eq ▸ hcomp_tidy).mono htime_le
  obtain ⟨hout, hqs⟩ := computesTidily_run_pure_false M (P.enc x) (f (P.param x) * (L + 1) ^ c)
    (encNat <$> prog p) htidy_full ans
  rw [OracleComp.interpret_map, hval ans hans x] at hout
  rw [OracleComp.queriesWith_map] at hqs
  exact ⟨hout, fun q hq_mem ↦ hq ans hans x q (hqs ▸ hq_mem)⟩

/-- **Unary-Padded Program Constructor for `FPTTuringReducible`**. -/
theorem FPTTuringReducible.of_paddedOraclePPT {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {pad g : ℕ → ℕ}
    (hpad : IsComputable pad encNat encNat)
    (hg : IsComputable g encNat encNat)
    (prog : α × ℕ → WordQueryComp Unit ℕ)
    (hprog : IsOraclePPTOn (encPair P.enc encUnary) encNat
      (fun p ↦ OracleComp.interpret ProbOracleComp.query (prog p)))
    (hval : ∀ ans, IsCountingOracleFor Q ans → ∀ x : α,
      OracleComp.interpret (m := Id) ans (prog (x, pad (P.param x))) = P.count x)
    (hq : ∀ ans, IsCountingOracleFor Q ans → ∀ x : α,
      ∀ q ∈ OracleComp.queriesWith ans (prog (x, pad (P.param x))),
        ∃ y : β, Q.enc y = q.2 ∧ Q.param y ≤ g (P.param x)) :
    FPTTuringReducible P Q :=
  FPTTuringReducible.of_auxOraclePPT (isComputable_nat_to_unary.comp hpad) hg prog hprog hval hq

/-- **Polynomial-Time Oracle Program Constructor for `FPTTuringReducible`**. -/
theorem FPTTuringReducible.of_oraclePPT {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {g : ℕ → ℕ}
    (hg : IsComputable g encNat encNat)
    (prog : α → WordQueryComp Unit ℕ)
    (hprog : IsOraclePPTOn P.enc encNat
      (fun x ↦ OracleComp.interpret ProbOracleComp.query (prog x)))
    (hval : ∀ ans, IsCountingOracleFor Q ans → ∀ x : α,
      OracleComp.interpret (m := Id) ans (prog x) = P.count x)
    (hq : ∀ ans, IsCountingOracleFor Q ans → ∀ x : α,
      ∀ q ∈ OracleComp.queriesWith ans (prog x),
        ∃ y : β, Q.enc y = q.2 ∧ Q.param y ≤ g (P.param x)) :
    FPTTuringReducible P Q :=
  FPTTuringReducible.of_paddedOraclePPT
    (ComputableInPolyTime.const 0).isComputable hg (fun p ↦ prog p.1)
    (hprog.preprocess (ComputableInPolyTime.fst P.enc encUnary))
    (fun ans hans x ↦ hval ans hans x) (fun ans hans x ↦ hq ans hans x)

/-- Single-query word-oracle program reading at most `bitBound` bits of the counting oracle on `y`
and decoding the little-endian binary natural via `ofBits`. -/
def queryCount {β : Type} (encB : β ↪ List Bool) (y : β) (bitBound : ℕ) :
    WordQueryComp Unit ℕ :=
  ofBits <$> (List.take bitBound <$> OracleComp.query ((), encB y))

/-- `queryCount` is strict oracle PPT in `(y, bitBound)` (`bitBound` in unary). -/
theorem isOraclePPTOn_queryCount {β : Type} (encB : β ↪ List Bool) :
    IsOraclePPTOn (encPair encB encUnary) encNat
      (fun p ↦ OracleComp.interpret ProbOracleComp.query (queryCount encB p.1 p.2)) := by
  simp only [queryCount, Functor.map_map, OracleComp.interpret_map, OracleComp.interpret_query]
  exact (IsOraclePPTOn.query_take ()
    (ComputableInPolyTime.encoding_comp (ComputableInPolyTime.fst encB encUnary))
    (ComputableInPolyTime.snd encB encUnary)).map ComputableInPolyTime.bitsToNat

/-- Evaluating `queryCount Q.enc y B` against any counting oracle `ans` for `Q` returns `Q.count y`
whenever `(encNat (Q.count y)).length ≤ B` (in particular whenever `Q.count y < 2 ^ B`). -/
theorem interpret_queryCount {β : Type} (Q : ParameterizedCountingProblem β)
    {ans : Unit × List Bool → List Bool} (hans : IsCountingOracleFor Q ans) (y : β) {B : ℕ}
    (hB : (encNat (Q.count y)).length ≤ B) :
    OracleComp.interpret (m := Id) ans (queryCount Q.enc y B) = Q.count y := by
  dsimp only [queryCount]
  rw [OracleComp.interpret_map, OracleComp.interpret_map, OracleComp.interpret_query, hans.1 () y]
  change ofBits (List.take B (encNat (Q.count y))) = Q.count y
  rw [List.take_of_length_le hB, encNat_apply]
  exact Nat.foldr_bit_bits (Q.count y)

/-- Queries emitted by `queryCount Q.enc y B`. -/
@[simp]
theorem queriesWith_queryCount {β : Type} (encB : β ↪ List Bool)
    (ans : Unit × List Bool → List Bool) (y : β) (B : ℕ) :
    OracleComp.queriesWith ans (queryCount encB y B) = [((), encB y)] := by
  simp [queryCount]

/-- Sequential batch-query program querying `queryCount encB y bitBound` for every `y ∈ ys`. -/
def queryCountList {β : Type} (encB : β ↪ List Bool) (ys : List β) (bitBound : ℕ) :
    WordQueryComp Unit (List ℕ) :=
  Prod.snd <$> OracleComp.iterate ys.length
    (fun st : List β × List ℕ ↦ match st.1 with
      | [] => pure ([], st.2)
      | y :: rest => (fun v ↦ (rest, st.2 ++ [v])) <$> queryCount encB y bitBound)
    (ys, [])

private lemma queryCountList_iter_eq {β : Type} (encB : β ↪ List Bool)
    (ans : Unit × List Bool → List Bool) (B : ℕ) :
    ∀ (ys : List β) (acc : List ℕ),
      OracleComp.interpret (m := Id) ans
        (OracleComp.iterate ys.length
          (fun st : List β × List ℕ ↦ match st.1 with
            | [] => pure ([], st.2)
            | y :: rest => (fun v ↦ (rest, st.2 ++ [v])) <$> queryCount encB y B)
          (ys, acc)) =
      ([], acc ++ ys.map fun y ↦ Id.run (OracleComp.interpret (m :=
        Id) ans (queryCount encB y B))) ∧
      OracleComp.queriesWith ans
        (OracleComp.iterate ys.length
          (fun st : List β × List ℕ ↦ match st.1 with
            | [] => pure ([], st.2)
            | y :: rest => (fun v ↦ (rest, st.2 ++ [v])) <$> queryCount encB y B)
          (ys, acc)) =
      ys.flatMap fun y ↦ OracleComp.queriesWith ans (queryCount encB y B) := by
  intro ys
  induction ys with
  | nil =>
    intro acc
    rw [List.length_nil, List.map_nil, List.append_nil, List.flatMap_nil]
    exact ⟨rfl, rfl⟩
  | cons y rest ih =>
    intro acc
    rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.interpret_bind,
      OracleComp.interpret_map, OracleComp.queriesWith_bind, OracleComp.queriesWith_map]
    let v : ℕ := Id.run (OracleComp.interpret (m := Id) ans (queryCount encB y B))
    obtain ⟨hval, hq⟩ := ih (acc ++ [v])
    refine ⟨?_, ?_⟩
    · change OracleComp.interpret (m := Id) ans
        (OracleComp.iterate rest.length _ (rest, acc ++ [v])) = ([], acc ++ (v :: rest.map _))
      rw [hval, List.append_assoc, List.singleton_append]
    · change OracleComp.queriesWith ans (queryCount encB y B) ++
        OracleComp.queriesWith ans (OracleComp.iterate rest.length _ (rest, acc ++ [v])) = _
      rw [hq, List.flatMap_cons]

/-- `queryCountList encB` is strict oracle PPT on `encPair (encList encB) encUnary`. -/
theorem isOraclePPTOn_queryCountList {β : Type} (encB : β ↪ List Bool) :
    IsOraclePPTOn (encPair (encList encB) encUnary) (encList encNat)
      (fun p ↦ OracleComp.interpret ProbOracleComp.query (queryCountList encB p.1 p.2)) := by
  let encIn := encPair (encList encB) encUnary
  let encSt := encPair (encList encB) (encList encNat)
  have hcount : ComputableInPolyTime (fun p : List β × ℕ ↦ p.1.length) encIn encUnary :=
    (ComputableInPolyTime.length encB).comp (ComputableInPolyTime.fst (encList encB) encUnary)
  have hinit : ComputableInPolyTime (fun p : List β × ℕ ↦ (p.1, ([] : List ℕ))) encIn encSt :=
    (ComputableInPolyTime.fst (encList encB) encUnary).prod (ComputableInPolyTime.const [])
  have hhead_enc : ComputableInPolyTime
      (fun q : (List β × ℕ) × (List β × List ℕ) ↦
        match q.2.1 with | [] => ([] : List Bool) | hd :: _ => encB hd)
      (encPair encIn encSt) encBits := by
    have hlist : ComputableInPolyTime
        (fun q : (List β × ℕ) × (List β × List ℕ) ↦ q.2.1.map fun b ↦ encB b)
        (encPair encIn encSt) (encList encBits) :=
      (ComputableInPolyTime.map (ComputableInPolyTime.encoding_comp ComputableInPolyTime.id')).comp
        ((ComputableInPolyTime.fst (encList encB) (encList encNat)).comp
          (ComputableInPolyTime.snd encIn encSt))
    refine ((ComputableInPolyTime.listGetD (encA := encBits) ([] : List Bool)).comp
      (hlist.prod (ComputableInPolyTime.const 0))).of_enc_eq fun q ↦ ?_
    rcases q with ⟨_, _ | ⟨_, _⟩, _⟩ <;> rfl
  have hcond : ComputableInPolyTime
      (fun q : (List β × ℕ) × (List β × List ℕ) ↦ q.2.1.isEmpty)
      (encPair encIn encSt) encBool := by
    have hlen := (ComputableInPolyTime.length encB).comp
      ((ComputableInPolyTime.fst (encList encB) (encList encNat)).comp
        (ComputableInPolyTime.snd encIn encSt))
    refine (ComputableInPolyTime.unary_beq hlen
      (ComputableInPolyTime.const 0)).of_enc_eq fun q ↦ ?_
    rcases q with ⟨_, _ | ⟨_, _⟩, _⟩ <;> rfl
  have hyes : IsOraclePPTOn (Operation := Unit) (encPair encIn encSt) encSt
      (fun q : (List β × ℕ) × (List β × List ℕ) ↦ pure (([], q.2.2) : List β × List ℕ)) :=
    ((ComputableInPolyTime.const ([] : List β)).prod
      ((ComputableInPolyTime.snd (encList encB) (encList encNat)).comp
        (ComputableInPolyTime.snd encIn encSt))).isOraclePPTOn
  have hno : IsOraclePPTOn (encPair encIn encSt) encSt
      (fun q : (List β × ℕ) × (List β × List ℕ) ↦ do
        let raw ← List.take q.1.2 <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
            ((), match q.2.1 with | [] => [] | hd :: _ => encB hd)
        pure (q.2.1.tail, q.2.2 ++ [ofBits raw])) := by
    have hq_take := IsOraclePPTOn.query_take () hhead_enc
      ((ComputableInPolyTime.snd (encList encB) encUnary).comp
        (ComputableInPolyTime.fst encIn encSt))
    have htail : ComputableInPolyTime
        (fun qr : ((List β × ℕ) × (List β × List ℕ)) × List Bool ↦ qr.1.2.1.tail)
        (encPair (encPair encIn encSt) encBits) (encList encB) := by
      simpa [List.drop_one] using ComputableInPolyTime.listDropWithInput
        (((ComputableInPolyTime.fst (encList encB) (encList encNat)).comp
          (ComputableInPolyTime.snd encIn encSt)).comp
          (ComputableInPolyTime.fst (encPair encIn encSt) encBits))
        (ComputableInPolyTime.const 1)
    have happ : ComputableInPolyTime
        (fun qr : ((List β × ℕ) × (List β × List ℕ)) × List Bool ↦
          qr.1.2.2 ++ [ofBits qr.2])
        (encPair (encPair encIn encSt) encBits) (encList encNat) :=
      (ComputableInPolyTime.listAppend encNat).comp
        ((((ComputableInPolyTime.snd (encList encB) (encList encNat)).comp
          (ComputableInPolyTime.snd encIn encSt)).comp
          (ComputableInPolyTime.fst (encPair encIn encSt) encBits)).prod
          ((ComputableInPolyTime.cons encNat).comp
            ((ComputableInPolyTime.bitsToNat.comp
              (ComputableInPolyTime.snd (encPair encIn encSt) encBits)).prod
              (ComputableInPolyTime.const ([] : List ℕ)))))
    exact (hq_take.map_with
      (f := fun (q : (List β × ℕ) × (List β × List ℕ)) (raw : List Bool) ↦
        (q.2.1.tail, q.2.2 ++ [ofBits raw]))
      (htail.prod happ)).congr fun q _ _ _ ↦ by simp [bind_pure_comp]
  let stepClean (p : List β × ℕ) (st : List β × List ℕ) : WordOracleComp Unit (List β × List ℕ) :=
    if st.1.isEmpty then pure ([], st.2)
    else do
      let raw ← List.take p.2 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
          ((), match st.1 with | [] => [] | hd :: _ => encB hd)
      pure (st.1.tail, st.2 ++ [ofBits raw])
  have hstep_ppt : IsOraclePPTOn (encPair encIn encSt) encSt
      (fun q ↦ stepClean q.1 q.2) :=
    IsOraclePPTOn.cond hcond hyes hno
  have hgrowth_pb : PolyBounded (fun p : List β × ℕ ↦ (encIn p).length)
      (fun p ↦ 2 * p.2 + 4) := by
    have hb : PolyBounded (fun p : List β × ℕ ↦ (encIn p).length) Prod.snd := by
      simpa only [encUnary_apply, List.length_replicate] using
        (ComputableInPolyTime.snd (encList encB) encUnary).polyBounded_length
    exact ((PolyBounded.const 2).mul hb).add (.const 4)
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth hcount hinit hstep_ppt hgrowth_pb
    (fun p st next hnext ↦ by
      dsimp only [stepClean] at hnext
      rcases hst : st.1 with _ | ⟨hd, tl⟩
      · simp only [hst, List.isEmpty_nil, ↓reduceIte] at hnext
        rw [OracleComp.eq_of_mem_supportWith_pure hnext]
        simp [encSt]
        omega
      · simp only [hst, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hnext
        obtain ⟨raw, hraw, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
        obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hraw
        rw [OracleComp.eq_of_mem_supportWith_pure hnext]
        have h1 : (encList encB tl).length ≤ (encList encB (hd :: tl)).length := by
          simp [encList_cons]
        have hbits : (encNat (ofBits (List.take p.2 reply))).length ≤ p.2 := by
          rw [encNat_apply, Nat.size_eq_bits_len]
          exact Nat.size_le.mpr ((Nat.foldr_bit_lt _).trans_le
            (Nat.pow_le_pow_right (by omega) (List.length_take_le _ _)))
        have h2 : (encList encNat (st.2 ++ [ofBits (List.take p.2 reply)])).length ≤
            (encList encNat st.2).length + 2 * p.2 + 2 := by
          rw [encList_append, List.length_append]
          simp only [encList_cons, encList_nil, length_frame, List.length_append, List.length_nil]
          omega
        dsimp only [encSt]
        simp only [length_encPair, hst, List.tail_cons]
        have hfr : (frame (encList encB tl)).length ≤ (frame (encList encB (hd :: tl))).length := by
          simp only [length_frame]; omega
        omega)
  refine (hloop.map (ComputableInPolyTime.snd (encList encB) (encList encNat))).congr
    fun p State oracle s ↦ ?_
  have hstep_eq (st : List β × List ℕ) :
      stepClean p st =
        OracleComp.interpret ProbOracleComp.query
          (match st.1 with
            | [] => pure ([], st.2)
            | y :: rest => (fun v ↦ (rest, st.2 ++ [v])) <$> queryCount encB y p.2) := by
    rcases hst1 : st.1 with _ | ⟨y, rest⟩
    · simp [stepClean, hst1]
    · simp [stepClean, hst1, queryCount, OracleComp.interpret_map, OracleComp.interpret_query,
        Functor.map_map]
  simp only [queryCountList, OracleComp.interpret_map, OracleComp.interpret_iterate]
  congr 3
  funext st
  exact hstep_eq st

/-- **Unary-Padded Batch Query Constructor for `FPTTuringReducible`**. -/
theorem FPTTuringReducible.of_paddedBatchQueries {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {pad g : ℕ → ℕ}
    (hpad : IsComputable pad encNat encNat)
    (hg : IsComputable g encNat encNat)
    (queries : α × ℕ → List β)
    (bitBound : α × ℕ → ℕ)
    (combine : (α × ℕ) × List ℕ → ℕ)
    (hqueries : ComputableInPolyTime queries (encPair P.enc encUnary) (encList Q.enc))
    (hbitBound : ComputableInPolyTime bitBound (encPair P.enc encUnary) encUnary)
    (hcombine : ComputableInPolyTime combine
      (encPair (encPair P.enc encUnary) (encList encNat)) encNat)
    (hlen : ∀ x, ∀ y ∈ queries (x, pad (P.param x)),
      (encNat (Q.count y)).length ≤ bitBound (x, pad (P.param x)))
    (hparam : ∀ x, ∀ y ∈ queries (x, pad (P.param x)), Q.param y ≤ g (P.param x))
    (hspec : ∀ x,
      combine ((x, pad (P.param x)), (queries (x, pad (P.param x))).map Q.count) = P.count x) :
    FPTTuringReducible P Q := by
  let prog (p : α × ℕ) : WordQueryComp Unit ℕ :=
    (fun vals ↦ combine (p, vals)) <$> queryCountList Q.enc (queries p) (bitBound p)
  have hprog_ppt : IsOraclePPTOn (encPair P.enc encUnary) encNat
      (fun p ↦ OracleComp.interpret ProbOracleComp.query (prog p)) := by
    simp only [prog, OracleComp.interpret_map]
    exact ((isOraclePPTOn_queryCountList Q.enc).preprocess
      (hqueries.prod hbitBound)).map_with hcombine
  refine FPTTuringReducible.of_paddedOraclePPT hpad hg prog hprog_ppt
    (fun ans hans x ↦ ?_) (fun ans _ x q hq ↦ ?_)
  · let p := (x, pad (P.param x))
    obtain ⟨hval_it, -⟩ := queryCountList_iter_eq Q.enc ans (bitBound p) (queries p) []
    dsimp only [prog, queryCountList]
    rw [OracleComp.interpret_map, OracleComp.interpret_map]
    change combine (p, ((OracleComp.interpret (m := Id) ans
      (OracleComp.iterate (queries p).length _ (queries p, [])) : List β × List ℕ)).2) = P.count x
    rw [hval_it, List.nil_append]
    have hmap : (queries p).map
        (fun y ↦ Id.run (OracleComp.interpret (m := Id) ans
          (queryCount Q.enc y (bitBound p)))) = (queries p).map Q.count :=
      List.map_congr_left fun y hy ↦ interpret_queryCount Q hans y (hlen x y hy)
    dsimp only
    rw [hmap, hspec x]
  · obtain ⟨-, hq_it⟩ := queryCountList_iter_eq Q.enc ans
      (bitBound (x, pad (P.param x))) (queries (x, pad (P.param x))) []
    dsimp only [prog, queryCountList] at hq
    rw [OracleComp.queriesWith_map, OracleComp.queriesWith_map, hq_it, List.mem_flatMap] at hq
    obtain ⟨y, hy, hqy⟩ := hq
    rw [queriesWith_queryCount, List.mem_singleton] at hqy
    exact ⟨y, by subst hqy; rfl, hparam x y hy⟩

/-- **Polynomial-Time Batch Query Constructor for `FPTTuringReducible`**. -/
theorem FPTTuringReducible.of_batchQueries {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {g : ℕ → ℕ}
    (hg : IsComputable g encNat encNat)
    (queries : α → List β)
    (bitBound : α → ℕ)
    (combine : α × List ℕ → ℕ)
    (hqueries : ComputableInPolyTime queries P.enc (encList Q.enc))
    (hbitBound : ComputableInPolyTime bitBound P.enc encUnary)
    (hcombine : ComputableInPolyTime combine (encPair P.enc (encList encNat)) encNat)
    (hlen : ∀ x, ∀ y ∈ queries x, (encNat (Q.count y)).length ≤ bitBound x)
    (hparam : ∀ x, ∀ y ∈ queries x, Q.param y ≤ g (P.param x))
    (hspec : ∀ x, combine (x, (queries x).map Q.count) = P.count x) :
    FPTTuringReducible P Q :=
  FPTTuringReducible.of_paddedBatchQueries
    (ComputableInPolyTime.const 0).isComputable hg
    (fun p ↦ queries p.1) (fun p ↦ bitBound p.1) (fun pv ↦ combine (pv.1.1, pv.2))
    (hqueries.comp (ComputableInPolyTime.fst P.enc encUnary))
    (hbitBound.comp (ComputableInPolyTime.fst P.enc encUnary))
    (hcombine.comp (((ComputableInPolyTime.fst P.enc encUnary).comp
      (ComputableInPolyTime.fst (encPair P.enc encUnary) (encList encNat))).prod
      (ComputableInPolyTime.snd (encPair P.enc encUnary) (encList encNat))))
    (fun x y hy ↦ hlen x y hy)
    (fun x y hy ↦ hparam x y hy)
    (fun x ↦ hspec x)

/-- Any FPT parsimonious reduction to a problem `Q` whose encoded output length is polynomially
bounded lifts to an FPT Turing reduction. -/
theorem FPTParsimoniousReducible.fptTuringReducible_of_polyBounded {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    (hPQ : FPTParsimoniousReducible P Q)
    (hpoly : PolyBounded (fun y ↦ (Q.enc y).length) (fun y ↦ (encNat (Q.count y)).length)) :
    FPTTuringReducible P Q := by
  obtain ⟨R, hcnt, hfptR, g, hg, hparam⟩ := hPQ
  obtain ⟨cb, db, hbd⟩ := hpoly.exists_le
  obtain ⟨F_R, c_R, hF_R, hc_R, hts_R⟩ := hfptR
  let boundQ (y : β) : ℕ := cb * ((Q.enc y).length + 1) ^ db
  have hboundQ_pt : ComputableInPolyTime boundQ Q.enc encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C cb * (Polynomial.X + 1) ^ db)).comp
      (ComputableInPolyTime.encoding_length Q.enc)).of_enc_eq fun _ ↦ by simp [boundQ]
  let qprog (y : β) : WordQueryComp Unit ℕ := queryCount Q.enc y (boundQ y)
  have hqprog_ppt : IsOraclePPTOn Q.enc encNat
      (fun y ↦ OracleComp.interpret ProbOracleComp.query (qprog y)) :=
    (isOraclePPTOn_queryCount Q.enc).preprocess (ComputableInPolyTime.id'.prod hboundQ_pt)
  obtain ⟨k_R, State_R, hfin_R, tm_R, htm_R⟩ := hts_R
  let _ : Finite State_R := hfin_R
  let M₀ : MultiTapePTM (k_R + k_R) Bool _ Unit :=
    MultiTapePTM.ofDeterministic (tidy false true tm_R)
  obtain ⟨_, k₁, Control₁, hfin₁, M₁, c₁, d₁, hM₁⟩ := hqprog_ppt.oraclePhase
  let _ : Finite Control₁ := hfin₁
  let M := M₁.tidyComp M₀ true
  let T₀_fn (k : ℕ) : ℕ := 5 * F_R k + 8 * k_R + 5
  have hT₀_comp : IsComputable T₀_fn encNat encNat :=
    IsComputable.add_nat
      (IsComputable.add_nat
        (IsComputable.mul_nat (ComputableInPolyTime.const 5).isComputable hF_R)
        (ComputableInPolyTime.const (8 * k_R)).isComputable)
      (ComputableInPolyTime.const 5).isComputable
  let f (k : ℕ) : ℕ := 5 * T₀_fn k + c₁ * (T₀_fn k + 1) ^ d₁ + 10
  have hf_comp : IsComputable f encNat encNat :=
    IsComputable.add_nat
      (IsComputable.add_nat
        (IsComputable.mul_nat (ComputableInPolyTime.const 5).isComputable hT₀_comp)
        (IsComputable.mul_nat (ComputableInPolyTime.const c₁).isComputable
          (IsComputable.pow_const_nat
            (IsComputable.add_nat hT₀_comp (ComputableInPolyTime.const 1).isComputable) d₁)))
      (ComputableInPolyTime.const 10).isComputable
  let c : ℕ := c_R + c_R * d₁
  refine ⟨_, _, inferInstance, M, f, g, c, hf_comp, hg, by omega, fun ans hans x ↦ ?_⟩
  let L := (P.enc x).length
  let t₀ := T₀_fn (P.param x) * (L + 1) ^ c_R
  have htidy₀ : M₀.ComputesTidily (P.enc x) t₀ (pure (Q.enc (R x))) := by
    refine (ComputesTidily.of_deterministic (Operation := Unit)
      ((htm_R x).computesTidily_tidy Bool.false_ne_true)).mono ?_
    have hP : 1 ≤ (L + 1) ^ c_R := Nat.one_le_pow _ _ (Nat.succ_pos L)
    dsimp [t₀, T₀_fn, L]
    nlinarith
  have hcomp_tidy : M.ComputesTidily (P.enc x) (5 * t₀ + c₁ * (t₀ + 1) ^ d₁ + 9)
      ((pure (R x) : WordOracleComp Unit β) >>=
        fun y ↦ encNat <$> OracleComp.interpret ProbOracleComp.query (qprog y)) := by
    refine ComputesTidily.comp_encoded Q.enc true
      (by simpa only [map_pure] using htidy₀)
      (fun y _ oracle s s' hy ↦ ?_)
    rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hy
    obtain ⟨rfl, _⟩ := Prod.mk.inj hy
    have hlen : (Q.enc (R x)).length ≤ t₀ :=
      htidy₀.length_output_le (s' := s') oracle s'
        (by rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff])
    exact (hM₁ (R x)).mono (Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (by omega) d₁))
  have htime_le : 5 * t₀ + c₁ * (t₀ + 1) ^ d₁ + 9 ≤ f (P.param x) * (L + 1) ^ c :=
    tidy_comp_time_bound (T₀_fn (P.param x)) L c_R c₁ d₁
  have hprog_eq :
      ((pure (R x) : WordOracleComp Unit β) >>=
        fun y ↦ encNat <$> OracleComp.interpret ProbOracleComp.query (qprog y)) =
      OracleComp.interpret ProbOracleComp.query (encNat <$> qprog (R x)) := by
    simp [OracleComp.interpret_map]
  obtain ⟨hout, hqs⟩ := computesTidily_run_pure_false M (P.enc x) (f (P.param x) * (L + 1) ^ c)
    (encNat <$> qprog (R x)) ((hprog_eq ▸ hcomp_tidy).mono htime_le) ans
  rw [OracleComp.interpret_map, interpret_queryCount Q hans (R x) (hbd (R x)), ← hcnt x] at hout
  rw [OracleComp.queriesWith_map, queriesWith_queryCount] at hqs
  refine ⟨hout, fun q hq_mem ↦ ?_⟩
  rw [hqs, List.mem_singleton] at hq_mem
  subst hq_mem
  exact ⟨R x, rfl, hparam x⟩

/-- Reflexivity of `FPTTuringReducible` on any problem with polynomially bounded output bit-length.
-/
theorem FPTTuringReducible.refl_of_polyBounded {α : Type} {P : ParameterizedCountingProblem α}
    (hpoly : PolyBounded (fun x ↦ (P.enc x).length) (fun x ↦ (encNat (P.count x)).length)) :
    FPTTuringReducible P P :=
  (FPTParsimoniousReducible.refl P).fptTuringReducible_of_polyBounded hpoly

private lemma queriesWith_interpret {ι κ γ : Type} {spec₁ : OracleSpec.{0, 0} ι}
    {spec₂ : OracleSpec.{0, 0} κ} (ans : (q : κ) → spec₂ q)
    (handler : (q : ι) → OracleComp spec₂ (spec₁ q)) (prog : OracleComp spec₁ γ) :
    OracleComp.queriesWith ans (OracleComp.interpret handler prog) =
      (OracleComp.queriesWith (fun q ↦ OracleComp.interpret (m := Id) ans (handler q))
        prog).flatMap fun q ↦ OracleComp.queriesWith ans (handler q) := by
  induction prog using PFunctor.FreeM.induction with
  | pure _ => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.queriesWith_bind,
      OracleComp.queriesWith_query_bind, List.flatMap_cons, ih]

private lemma isOraclePPTOn_finiteStep_pure_false {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Unit) :
    IsOraclePPTOn (encPair encUnary encFiniteConfig) encFiniteConfig
      (fun pair : ℕ × FiniteConfig k Bool Control Unit ↦
        OracleComp.interpret ProbOracleComp.query
          (machine.finiteStep (fun choices ↦ choices <$> pure false)
            (fun op word ↦ List.take pair.1 <$>
              OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, word))
            pair.2)) := by
  let branch (ctrl : Option Control) (pair : ℕ × FiniteConfig k Bool Control Unit) :
      WordOracleComp Unit (FiniteConfig k Bool Control Unit) :=
    match ctrl with
    | none => pure pair.2
    | some q =>
      match machine.tr q pair.2.tapes.inputSymbol pair.2.tapes.workTapeSymbols
          pair.2.answerSymbols false with
      | .step action symbol move => pure (pair.2.step action symbol move)
      | .query ch next => do
        let answer ← List.take pair.1 <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
            (ch, (pair.2.channels ch).1)
        pure (pair.2.receive ch next answer)
  have hprog (pair : ℕ × FiniteConfig k Bool Control Unit) :
      branch pair.2.tapes.state pair =
        OracleComp.interpret ProbOracleComp.query
          (machine.finiteStep (fun choices ↦ choices <$> pure false)
            (fun op word ↦ List.take pair.1 <$>
              OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, word))
            pair.2) := by
    rcases pair with ⟨limit, cfg⟩
    cases hst : cfg.tapes.state with
    | none => simp [branch, MultiTapeMachine.finiteStep, hst]
    | some q =>
      simp only [branch, MultiTapeMachine.finiteStep, hst, map_pure, pure_bind]
      cases machine.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
          false with
      | step _ _ _ => simp
      | query ch next => simp [OracleComp.interpret_map, OracleComp.interpret_query]
  refine (IsOraclePPTOn.finite_cases (tagEncoding := encFinite (Option Control))
    (tag := fun pair : ℕ × FiniteConfig k Bool Control Unit ↦ pair.2.tapes.state)
    (branch := branch) (by fun_prop) fun ctrl ↦ ?_).congr
    fun pair State oracle s ↦ by rw [hprog]
  cases ctrl with
  | none => exact (by fun_prop : ComputableInPolyTime Prod.snd _ _).isPPTOn.isOraclePPTOn
  | some q =>
    refine IsOraclePPTOn.finite_cases
      (tag := fun pair : ℕ × FiniteConfig k Bool Control Unit ↦
        (pair.2.tapes.inputSymbol, pair.2.tapes.workTapeSymbols, pair.2.answerSymbols))
      (tagEncoding := encPair (encFinEnum (Option Bool))
        (encPair (encFinEnum (Fin k → Option Bool)) (encFinite (Unit → Option Bool))))
      (branch := fun obs (pair : ℕ × FiniteConfig k Bool Control Unit) ↦
        match machine.tr q obs.1 obs.2.1 obs.2.2 false with
        | .step action symbol move => pure (pair.2.step action symbol move)
        | .query ch next => do
          let answer ← List.take pair.1 <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool)
              (ch, (pair.2.channels ch).1)
          pure (pair.2.receive ch next answer))
      (by fun_prop) ?_
    rintro ⟨inp, work, ans⟩
    cases machine.tr q inp work ans false with
    | step action symbol move =>
      exact (by fun_prop : ComputableInPolyTime _ _ encFiniteConfig).isPPTOn.isOraclePPTOn
    | query ch next =>
      have hreq : ComputableInPolyTime
          (fun pair : ℕ × FiniteConfig k Bool Control Unit ↦ (pair.2.channels ch).1)
          (encPair encUnary encFiniteConfig) encBits :=
        (((ComputableInPolyTime.pi_apply (encPair encBits (encBiTape encBool)) ch).comp
          ComputableInPolyTime.finiteConfig_channels).comp
          (ComputableInPolyTime.snd encUnary encFiniteConfig)).fst'
      have hq := (IsOraclePPTOn.query_take ch
        (request := fun pair : ℕ × FiniteConfig k Bool Control Unit ↦ (pair.2.channels ch).1)
        (limit := Prod.fst) hreq (by fun_prop)).map_with
        (f := fun pair answer ↦ pair.2.receive ch next answer) (by fun_prop)
      simpa only [bind_pure_comp] using hq

private lemma isOraclePPTOn_run_pure_false_of_clock {k : ℕ} {Control α : Type} [Finite Control]
    {encIn : α ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    {word : α → List Bool} {clock : α → ℕ}
    (hword : ComputableInPolyTime word encIn encBits)
    (hclock : ComputableInPolyTime clock encIn encUnary) :
    IsOraclePPTOn encIn encBits
      (fun a ↦ OracleComp.interpret ProbOracleComp.query
        (machine.run (pure false)
          (fun op w ↦ OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, w))
          (clock a) (word a))) ∧
    ∀ a, ∀ out ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query
        (machine.run (pure false)
          (fun op w ↦ OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, w))
          (clock a) (word a))),
      out.length ≤ clock a := by
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  have hclock_pb : PolyBounded (fun a ↦ (encIn a).length) clock := by
    simpa only [encUnary_apply, List.length_replicate] using hclock.polyBounded_length
  have hword_pb : PolyBounded (fun a ↦ (encIn a).length) (fun a ↦ (word a).length) := by
    simpa only [encBits_apply] using hword.polyBounded_length
  have hstart : ComputableInPolyTime
      (fun a ↦ FiniteConfig.init (k := k) (Oracle := Unit) machine.initial (word a))
      encIn encFiniteConfig :=
    ComputableInPolyTime.finiteConfig_init hword machine.initial
  let step (a : α) (cfg : FiniteConfig k Bool Control Unit) :
      WordOracleComp Unit (FiniteConfig k Bool Control Unit) :=
    OracleComp.interpret ProbOracleComp.query
      (machine.finiteStep (fun choices ↦ choices <$> pure false)
        (fun op q ↦ List.take (clock a) <$>
          OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, q)) cfg)
  have hstep : IsOraclePPTOn (encPair encIn encFiniteConfig) encFiniteConfig
      (fun pair ↦ step pair.1 pair.2) :=
    (isOraclePPTOn_finiteStep_pure_false machine).preprocess
      (prepare := fun pair : α × FiniteConfig k Bool Control Unit ↦ (clock pair.1, pair.2))
      ((hclock.comp (ComputableInPolyTime.fst encIn encFiniteConfig)).prod
        (ComputableInPolyTime.snd encIn encFiniteConfig))
  obtain ⟨hloop_ppt, hloop_inv⟩ := IsOraclePPTOn.iterateWith_spec hclock hstart hstep
    (fun a i cfg ↦ FiniteConfig.SpaceBound (word a).length i (clock a) cfg)
    (fun a ↦ FiniteConfig.spaceBound_init _ _ _)
    (fun a i cfg _ hcfg next hnext ↦ by
      dsimp only [step] at hnext
      cases hst : cfg.tapes.state with
      | none =>
        simp only [MultiTapeMachine.finiteStep, hst] at hnext
        exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
          hcfg.mono le_rfl (Nat.le_succ i) le_rfl
      | some q =>
        simp only [MultiTapeMachine.finiteStep, hst, map_pure, pure_bind] at hnext
        cases htr : machine.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
            false with
        | step action symbol move =>
          rw [htr] at hnext
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸ hcfg.step action symbol move
        | query ch ctrl =>
          rw [htr] at hnext
          simp only [bind_map_left, OracleComp.interpret_bind, OracleComp.interpret_query,
            OracleComp.interpret_pure] at hnext
          obtain ⟨reply, -, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
            hcfg.receive ch ctrl _ (List.length_take_le _ _))
    (size := fun a ↦ cf * ((word a).length + clock a + clock a + 1))
    ((PolyBounded.const cf).mul (((hword_pb.add hclock_pb).add hclock_pb).add (.const 1)))
    (fun a _ cfg _ hcfg ↦ (hcf _ _ _ cfg hcfg).trans (Nat.mul_le_mul_left cf (by omega)))
  have hprog_eq (a : α) :
      ((fun cfg : FiniteConfig k Bool Control Unit ↦ cfg.tapes.output) <$>
        OracleComp.iterate (clock a) (step a) (FiniteConfig.init machine.initial (word a))) =
      OracleComp.interpret ProbOracleComp.query
        (machine.run (pure false)
          (fun op w ↦ OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, w))
          (clock a) (word a)) := by
    rw [← finiteRunFrom_take_init, MultiTapeMachine.finiteRunFrom, OracleComp.interpret_map,
      OracleComp.interpret_iterate]
  refine ⟨(hloop_ppt.map (by fun_prop : ComputableInPolyTime
      (fun cfg : FiniteConfig k Bool Control Unit ↦ cfg.tapes.output)
      encFiniteConfig encBits)).congr fun a State oracle s ↦ by rw [hprog_eq a],
    fun a out hout ↦ ?_⟩
  rw [← hprog_eq a] at hout
  obtain ⟨cfg, hcfg, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hout
  exact (hloop_inv a cfg hcfg).output

/-- **Transitivity of Adaptive FPT Turing Reductions** (`FPTTuringReducible.trans`). -/
@[trans]
theorem FPTTuringReducible.trans {α β γ : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    {R : ParameterizedCountingProblem γ}
    (hPQ : FPTTuringReducible P Q) (hQR : FPTTuringReducible Q R) :
    FPTTuringReducible P R := by
  obtain ⟨k₁, Control₁, hfin₁, M₁, f₁, g₁, c₁, hf₁, hg₁, _, hM₁⟩ := hPQ
  obtain ⟨k₂, Control₂, hfin₂, M₂, f₂, g₂, c₂, hf₂, hg₂, _, hM₂⟩ := hQR
  let _ : Finite Control₁ := hfin₁
  let _ : Finite Control₂ := hfin₂
  obtain ⟨paramQ_ext, hparamQ_pt, hparamQ_eq⟩ :=
    ComputableInPolyTime.exists_word_extension Q.param_polyTime
  let Aux := ℕ × List ℕ
  let encAux : Aux ↪ List Bool := encPair encUnary (encList encUnary)
  let aux (k : ℕ) : Aux := (f₁ k, (List.range (g₁ k + 1)).map f₂)
  have haux_comp : IsComputable aux encNat encAux :=
    IsComputable.pair_enc (isComputable_nat_to_unary.comp hf₁)
      ((IsComputable.range_map_unary hf₂).comp hg₁)
  let Caller := α × Aux
  let encCaller : Caller ↪ List Bool := encPair P.enc encAux
  let clock₁ (p : List Bool × ℕ) : ℕ := p.2 * (p.1.length + 1) ^ c₁
  have hclock₁_pt : ComputableInPolyTime clock₁ (encPair encBits encUnary) encUnary := by
    have hpoly : ComputableInPolyTime (fun p : List Bool × ℕ ↦ (p.1.length + 1) ^ c₁)
        (encPair encBits encUnary) encUnary :=
      ((ComputableInPolyTime.unary_eval ((Polynomial.X + 1) ^ c₁)).comp
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.fst encBits encUnary))).of_enc_eq fun p ↦ by simp
    exact ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.snd encBits encUnary).prod hpoly)
  obtain ⟨hM₁_ppt, -⟩ := isOraclePPTOn_run_pure_false_of_clock M₁
    (ComputableInPolyTime.fst encBits encUnary) hclock₁_pt
  let lookupF₂ (caller : Caller) (w : List Bool) : ℕ :=
    caller.2.2.getD (paramQ_ext w) 0
  have hlookup_pt : ComputableInPolyTime (fun cw : Caller × List Bool ↦ lookupF₂ cw.1 cw.2)
      (encPair encCaller encBits) encUnary :=
    ComputableInPolyTime.listGetD_binary 0
      (((ComputableInPolyTime.snd encUnary (encList encUnary)).comp
        (ComputableInPolyTime.snd P.enc encAux)).comp
        (ComputableInPolyTime.fst encCaller encBits))
      (hparamQ_pt.comp (ComputableInPolyTime.snd encCaller encBits))
  let clock₂ (caller : Caller) (w : List Bool) : ℕ :=
    lookupF₂ caller w * (w.length + 1) ^ c₂
  have hclock₂_pt : ComputableInPolyTime (fun cw : Caller × List Bool ↦ clock₂ cw.1 cw.2)
      (encPair encCaller encBits) encUnary := by
    have hpoly : ComputableInPolyTime (fun cw : Caller × List Bool ↦ (cw.2.length + 1) ^ c₂)
        (encPair encCaller encBits) encUnary :=
      ((ComputableInPolyTime.unary_eval ((Polynomial.X + 1) ^ c₂)).comp
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.snd encCaller encBits))).of_enc_eq fun _ ↦ by simp
    exact ComputableInPolyTime.unary_mul.comp (hlookup_pt.prod hpoly)
  let hreq_enc := encPair encCaller (encPair (encFinEnum Unit) encBits)
  have hw_proj : ComputableInPolyTime (fun cr : Caller × (Unit × List Bool) ↦ cr.2.2)
      hreq_enc encBits :=
    (ComputableInPolyTime.snd (encFinEnum Unit) encBits).comp
      (ComputableInPolyTime.snd encCaller _)
  have hclock₂_req : ComputableInPolyTime
      (fun cr : Caller × (Unit × List Bool) ↦ clock₂ cr.1 cr.2.2) hreq_enc encUnary :=
    hclock₂_pt.comp ((ComputableInPolyTime.fst encCaller _).prod hw_proj)
  obtain ⟨hM₂_ppt, hM₂_len⟩ := isOraclePPTOn_run_pure_false_of_clock M₂ hw_proj hclock₂_req
  let handlerQ (caller : Caller) (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
    M₂.run (pure false)
      (fun op w ↦ OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, w))
      (clock₂ caller q.2) q.2
  let prog (caller : Caller) : WordQueryComp Unit ℕ :=
    ofBits <$> OracleComp.interpret (handlerQ caller)
      (M₁.run (pure false)
        (fun op w ↦ OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, w))
        (clock₁ (P.enc caller.1, caller.2.1)) (P.enc caller.1))
  have hprepare : ComputableInPolyTime (fun caller : Caller ↦ (P.enc caller.1, caller.2.1))
      encCaller (encPair encBits encUnary) :=
    (ComputableInPolyTime.encoding_comp (ComputableInPolyTime.fst P.enc encAux)).prod
      ((ComputableInPolyTime.fst encUnary (encList encUnary)).comp
        (ComputableInPolyTime.snd P.enc encAux))
  have hsubst_ppt : IsOraclePPTOn encCaller encNat
      (fun caller ↦ OracleComp.interpret ProbOracleComp.query (prog caller)) := by
    have hsub := hM₁_ppt.interpret_preprocess_open'
      (operationEncoding := encFinEnum Unit)
      (handler := fun caller q ↦ OracleComp.interpret ProbOracleComp.query (handlerQ caller q))
      (prepare := fun caller : Caller ↦ (P.enc caller.1, caller.2.1))
      (resources := clock₂)
      hprepare hM₂_ppt hclock₂_pt
      (fun caller q reply hreply ↦ hM₂_len (caller, q) reply hreply)
    refine (hsub.map ComputableInPolyTime.bitsToNat).congr fun caller State oracle s ↦ ?_
    simp only [prog, OracleComp.interpret_map, OracleComp.interpret_interpret]
    congr 3
    funext q
    simp [ProbOracleComp.interpret_query]
  let g_comp (k : ℕ) : ℕ := cumulSum g₂ (g₁ k)
  have hg_comp : IsComputable g_comp encNat encNat := (IsComputable.cumulSum hg₂).comp hg₁
  have hansQ := isCountingOracleFor_canonical Q
  have hboth (ansR : Unit × List Bool → List Bool) (hansR : IsCountingOracleFor R ansR) (x : α) :
      OracleComp.interpret (m := Id) ansR (prog (x, aux (P.param x))) = P.count x ∧
      ∀ q ∈ OracleComp.queriesWith ansR (prog (x, aux (P.param x))),
        ∃ z : γ, R.enc z = q.2 ∧ R.param z ≤ g_comp (P.param x) := by
    let caller : Caller := (x, aux (P.param x))
    let run₁ : WordQueryComp Unit (List Bool) :=
      M₁.run (pure false)
        (fun op w ↦ OracleComp.query (spec := fun _ : Unit × List Bool ↦ List Bool) (op, w))
        (f₁ (P.param x) * ((P.enc x).length + 1) ^ c₁) (P.enc x)
    obtain ⟨hout₁, hqs₁⟩ := hM₁ (canonicalCountingOracle Q) hansQ x
    let h_det (q' : Unit × List Bool) : List Bool :=
      OracleComp.interpret (m := Id) ansR (handlerQ caller q')
    have hclk_eq (y : β) (hy : Q.param y ≤ g₁ (P.param x)) :
        clock₂ caller (Q.enc y) = f₂ (Q.param y) * ((Q.enc y).length + 1) ^ c₂ := by
      have htab : lookupF₂ caller (Q.enc y) = f₂ (Q.param y) := by
        dsimp [lookupF₂, caller, aux]
        rw [hparamQ_eq y, List.getD_eq_getElem _ _ (by simp; omega)]
        simp
      simp [clock₂, htab]
    have hagrees : ∀ q' ∈ OracleComp.queriesWith (canonicalCountingOracle Q) run₁,
        h_det q' = canonicalCountingOracle Q q' := by
      intro q' hq'
      obtain ⟨y, hy_enc, hy_param⟩ := hqs₁ q' hq'
      rcases q' with ⟨⟨⟩, w⟩
      subst hy_enc
      dsimp [h_det, handlerQ]
      rw [hclk_eq y hy_param, (hM₂ ansR hansR y).1, hansQ.1 () y]
    obtain ⟨heval, hqlist⟩ := OracleComp.interpret_id_congr (canonicalCountingOracle Q) h_det run₁
      (fun q' hq' ↦ hagrees q' hq')
    refine ⟨?_, fun q hq ↦ ?_⟩
    · dsimp only [prog]
      rw [OracleComp.interpret_map, OracleComp.interpret_interpret]
      change ofBits (OracleComp.interpret (m := Id) h_det run₁) = P.count x
      rw [heval, hout₁, encNat_apply]
      exact Nat.foldr_bit_bits (P.count x)
    · simp only [prog, OracleComp.queriesWith_map] at hq
      rw [queriesWith_interpret, hqlist, List.mem_flatMap] at hq
      obtain ⟨q₁, hq₁, hq₂⟩ := hq
      obtain ⟨y, hy_enc, hy_param⟩ := hqs₁ q₁ hq₁
      rcases q₁ with ⟨⟨⟩, w⟩
      subst hy_enc
      dsimp [handlerQ] at hq₂
      rw [hclk_eq y hy_param] at hq₂
      obtain ⟨z, hz_enc, hz_param⟩ := (hM₂ ansR hansR y).2 q hq₂
      exact ⟨z, hz_enc, hz_param.trans (le_cumulSum hy_param)⟩
  exact FPTTuringReducible.of_auxOraclePPT haux_comp hg_comp prog hsubst_ppt
    (fun ansR hansR x ↦ (hboth ansR hansR x).1) (fun ansR hansR x ↦ (hboth ansR hansR x).2)

private def zeroUnitProblem : ParameterizedCountingProblem Unit where
  enc := encFinEnum Unit
  count _ := 0
  param _ := 0
  param_polyTime := ComputableInPolyTime.const 0

private lemma isCountingOracleFor_zeroUnitProblem :
    IsCountingOracleFor zeroUnitProblem (fun _ ↦ ([] : List Bool)) :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

/-- **`InFPT` is closed downwards under `FPTTuringReducible`**. -/
theorem FPTTuringReducible.inFPT {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    (hPQ : FPTTuringReducible P Q) (hQ : Q.InFPT) : P.InFPT := by
  obtain ⟨padQ, simQ, hpadQ, _, hsimQ_pt, hsimQ_eq⟩ := hQ.exists_paddedWordSimulator
  have hQ0 : FPTTuringReducible Q zeroUnitProblem := by
    refine FPTTuringReducible.of_paddedOraclePPT hpadQ
      (ComputableInPolyTime.const 0).isComputable
      (fun p ↦ pure (simQ (Q.enc p.1, p.2)))
      ((hsimQ_pt.comp
        ((ComputableInPolyTime.encoding_comp (ComputableInPolyTime.fst Q.enc encUnary)).prod
          (ComputableInPolyTime.snd Q.enc encUnary))).isPPTOn.isOraclePPTOn)
      (fun _ _ y ↦ hsimQ_eq y le_rfl)
      (fun _ _ _ _ hq ↦ by simp at hq)
  obtain ⟨k, Control, hfin, M, f, _, c, hf, _, _, hM⟩ := hPQ.trans hQ0
  let _ : Finite Control := hfin
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let stepNil := M.answerStep (fun _ ↦ ([] : List Bool))
  have hstepNil_pt : ComputableInPolyTime stepNil encFiniteConfig encFiniteConfig := by
    have hcond : ComputableInPolyTime (fun cfg ↦ (M.pendingQuery cfg).isSome)
        encFiniteConfig encBool :=
      (ComputableInPolyTime.of_finite Option.isSome).comp M.pendingQuery_pt
    have hrecv : ComputableInPolyTime
        (fun cfg : FiniteConfig k Bool Control Unit ↦
          match M.pendingQuery cfg with
          | some (op, next) => cfg.receive op next []
          | none => cfg) encFiniteConfig encFiniteConfig := by
      refine ComputableInPolyTime.finite_cases (tag := M.pendingQuery)
        (branch := fun pq cfg ↦ match pq with
          | some (op, next) => cfg.receive op next []
          | none => cfg) M.pendingQuery_pt ?_
      rintro (_ | ⟨op, next⟩)
      · exact ComputableInPolyTime.id'
      · exact ComputableInPolyTime.finiteConfig_receive ComputableInPolyTime.id'
          (ComputableInPolyTime.const []) op next
    refine (ComputableInPolyTime.ite (encC := encBool) hcond hrecv M.localStep_pt).of_enc_eq
      fun cfg ↦ ?_
    unfold stepNil MultiTapePTM.answerStep MultiTapePTM.localStep MultiTapePTM.pendingQuery
    cases cfg.tapes.state with
    | none => rfl
    | some ctrl =>
      simp only [Option.map_some]
      cases M.tr ctrl cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols false <;>
        rfl
  have hsp_iter (w : List Bool) (i : ℕ) :
      FiniteConfig.SpaceBound w.length i 1 (stepNil^[i] (FiniteConfig.init M.initial w)) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      unfold stepNil MultiTapePTM.answerStep
      split
      · exact ih.mono le_rfl (Nat.le_succ i) le_rfl
      · split
        exacts [ih.step _ _ _, ih.receive _ _ _ (by simp)]
  let budget (p : α × ℕ) : ℕ := p.2 * ((P.enc p.1).length + 1) ^ c
  have hbudget_pt : ComputableInPolyTime budget (encPair P.enc encUnary) encUnary := by
    have hpoly : ComputableInPolyTime (fun p : α × ℕ ↦ ((P.enc p.1).length + 1) ^ c)
        (encPair P.enc encUnary) encUnary :=
      ((ComputableInPolyTime.unary_eval ((Polynomial.X + 1) ^ c)).comp
        ((ComputableInPolyTime.encoding_length P.enc).comp
          (ComputableInPolyTime.fst P.enc encUnary))).of_enc_eq fun _ ↦ by simp
    exact ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.snd P.enc encUnary).prod hpoly)
  have hbudget_pb : PolyBounded (fun p : α × ℕ ↦ (encPair P.enc encUnary p).length) budget := by
    simpa only [encUnary_apply, List.length_replicate] using hbudget_pt.polyBounded_length
  have hlen_pb : PolyBounded (fun p : α × ℕ ↦ (encPair P.enc encUnary p).length)
      (fun p ↦ (P.enc p.1).length) :=
    PolyBounded.of_forall_le 1 1 fun p ↦
      (length_le_encPair_left P.enc encUnary p).trans (by simp)
  have hit := ComputableInPolyTime.iterate hbudget_pt
    (ComputableInPolyTime.finiteConfig_init
      (ComputableInPolyTime.encoding_comp (ComputableInPolyTime.fst P.enc encUnary)) M.initial)
    hstepNil_pt
    ((PolyBounded.const cf).mul (((hlen_pb.add hbudget_pb).add (.const 1)).add (.const 1)))
    fun p i hi ↦ (hcf _ _ _ _ (hsp_iter (P.enc p.1) i)).trans
      (Nat.mul_le_mul_left cf (by omega))
  let alg (p : α × ℕ) : ℕ :=
    ofBits (stepNil^[budget p] (FiniteConfig.init M.initial (P.enc p.1))).tapes.output
  refine ParameterizedCountingProblem.InFPT.of_paddedPolyTime hf
    (ComputableInPolyTime.bitsToNat.comp
      ((by fun_prop : ComputableInPolyTime
        (fun cfg : FiniteConfig k Bool Control Unit ↦ cfg.tapes.output)
        encFiniteConfig encBits).comp hit))
    fun x ↦ ?_
  have hrun := M.interpret_run_pure_false (fun _ ↦ ([] : List Bool))
    (f (P.param x) * ((P.enc x).length + 1) ^ c) (P.enc x)
  have hout := (hM (fun _ ↦ ([] : List Bool)) isCountingOracleFor_zeroUnitProblem x).1
  change ofBits ((M.answerStep fun _ ↦ ([] : List Bool))^[f (P.param x) * ((P.enc x).length +
    1) ^ c]
    (FiniteConfig.init M.initial (P.enc x))).tapes.output = P.count x
  rw [← hrun, hout, encNat_apply]
  exact Nat.foldr_bit_bits (P.count x)

end TuringReductions

/-! ### 2. `#k-Clique`, `#W[1]`, and `#W[1]`-Hardness -/

section SharpWOne

/-- Exact number of $m$-cliques in `x : CliqueInstance`, matching `Cslib.Complexity.Clique`. -/
@[expose] noncomputable def sharpKCliqueCount (x : CliqueInstance) : ℕ :=
  Nat.card {S : Finset {v // v ∈ x.graph.vertices} // x.graph.induced.IsNClique x.m S}

/-- For `m = 0`, every graph has exactly `1` clique of size `0` (the empty vertex set `∅`). -/
@[simp]
theorem sharpKCliqueCount_zero (G : Graph) : sharpKCliqueCount ⟨G, 0⟩ = 1 := by
  have : Unique {S : Finset {v // v ∈ G.vertices} // G.induced.IsNClique 0 S} :=
    { default := ⟨∅, by simp⟩
      uniq := fun ⟨S, hS⟩ ↦ Subtype.ext (Finset.card_eq_zero.mp hS.2) }
  rw [sharpKCliqueCount, Nat.card_unique]

/-- Upper bound `sharpKCliqueCount x ≤ 2 ^ x.graph.vertices.length`. -/
theorem sharpKCliqueCount_le_two_pow (x : CliqueInstance) :
    sharpKCliqueCount x ≤ 2 ^ x.graph.vertices.length := by
  classical
  rw [sharpKCliqueCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter fun S : Finset {v // v ∈ x.graph.vertices} ↦
          x.graph.induced.IsNClique x.m S).card
      ≤ (Finset.univ : Finset (Finset {v // v ∈ x.graph.vertices})).card :=
        Finset.card_le_univ _
    _ = 2 ^ Fintype.card {v // v ∈ x.graph.vertices} := by simp
    _ = 2 ^ x.graph.vertices.toFinset.card := by rw [Graph.card_vertexSubtype]
    _ ≤ 2 ^ x.graph.vertices.length :=
        Nat.pow_le_pow_right (by omega) x.graph.vertices.toFinset_card_le

/-- Canonical `#k-Clique` parameterized counting problem on `CliqueInstance`. -/
@[expose] noncomputable def sharpKCliqueProblem : ParameterizedCountingProblem CliqueInstance where
  enc := encCliqueInstance
  count := sharpKCliqueCount
  param := CliqueInstance.m
  param_polyTime := by fun_prop

/-- Unfolding `sharpKCliqueProblem.count`. -/
@[simp, grind =]
theorem sharpKCliqueProblem_count (x : CliqueInstance) :
    sharpKCliqueProblem.count x = sharpKCliqueCount x := rfl

/-- Unfolding `sharpKCliqueProblem.param`. -/
@[simp, grind =]
theorem sharpKCliqueProblem_param (x : CliqueInstance) :
    sharpKCliqueProblem.param x = x.m := rfl

/-- Encoded output length of `sharpKCliqueProblem` is linearly bounded by the encoded instance
length. -/
theorem length_encNat_sharpKCliqueCount_le (x : CliqueInstance) :
    (encNat (sharpKCliqueProblem.count x)).length ≤ (encCliqueInstance x).length + 1 := by
  rw [sharpKCliqueProblem_count, encNat_apply, Nat.size_eq_bits_len]
  have hlt : sharpKCliqueCount x < 2 ^ (x.graph.vertices.length + 1) :=
    (sharpKCliqueCount_le_two_pow x).trans_lt
      (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
  have hsize : (sharpKCliqueCount x).size ≤ x.graph.vertices.length + 1 := Nat.size_le.mpr hlt
  have hv : x.graph.vertices.length ≤ (encCliqueInstance x).length :=
    x.graph.length_vertices_le_encGraph.trans
      (length_le_encPair_left encGraph encNat (x.graph, x.m))
  omega

/-- Membership in the parameterized counting class `#W[1]`
: existence of an FPT parsimonious reduction to `sharpKCliqueProblem`.
-/
def SharpWOne {α : Type*} (P : ParameterizedCountingProblem α) : Prop :=
  FPTParsimoniousReducible P sharpKCliqueProblem

/-- `#W[1]`-hardness: existence of an
FPT Turing reduction from `sharpKCliqueProblem` to `P`.
-/
def SharpWOneHard {α : Type} (P : ParameterizedCountingProblem α) : Prop :=
  FPTTuringReducible sharpKCliqueProblem P

/-- `sharpKCliqueProblem` belongs to `#W[1]`. -/
theorem sharpWOne_sharpKCliqueProblem : SharpWOne sharpKCliqueProblem :=
  FPTParsimoniousReducible.refl sharpKCliqueProblem

/-- `sharpKCliqueProblem` is `#W[1]`-hard. -/
theorem sharpWOneHard_sharpKCliqueProblem : SharpWOneHard sharpKCliqueProblem :=
  FPTTuringReducible.refl_of_polyBounded
    (PolyBounded.of_forall_le 1 1 fun x ↦ by
      change (encNat (sharpKCliqueProblem.count x)).length ≤
        1 * ((encCliqueInstance x).length + 1) ^ 1
      simpa only [one_mul, pow_one] using length_encNat_sharpKCliqueCount_le x)

/-- `#W[1]` is closed downwards under `FPTParsimoniousReducible`. -/
theorem FPTParsimoniousReducible.sharpWOne {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    (hPQ : FPTParsimoniousReducible P Q) (hQ : SharpWOne Q) : SharpWOne P :=
  hPQ.trans hQ

/-- Every problem in `#W[1]` reduces to `sharpKCliqueProblem` under FPT Turing reductions. -/
theorem SharpWOne.fptTuringReducible_sharpKClique {α : Type}
    {P : ParameterizedCountingProblem α} (hP : SharpWOne P) :
    FPTTuringReducible P sharpKCliqueProblem :=
  hP.fptTuringReducible_of_polyBounded
    (PolyBounded.of_forall_le 1 1 fun x ↦ by
      change (encNat (sharpKCliqueProblem.count x)).length ≤
        1 * ((encCliqueInstance x).length + 1) ^ 1
      simpa only [one_mul, pow_one] using length_encNat_sharpKCliqueCount_le x)

/-- **`#W[1]`-hardness transfers across `FPTTuringReducible`**. -/
theorem SharpWOneHard.trans {α β : Type}
    {P : ParameterizedCountingProblem α} {Q : ParameterizedCountingProblem β}
    (hP : SharpWOneHard P) (hPQ : FPTTuringReducible P Q) : SharpWOneHard Q :=
  FPTTuringReducible.trans hP hPQ

/-- If `P` is `#W[1]`-hard and `sharpKCliqueProblem` is not in `FPT`, then `P` is not in `FPT`. -/
theorem SharpWOneHard.not_inFPT_of_not_inFPT_sharpKClique {α : Type}
    {P : ParameterizedCountingProblem α} (hP : SharpWOneHard P)
    (hClique : ¬ sharpKCliqueProblem.InFPT) : ¬ P.InFPT :=
  fun hFPT ↦ hClique (hP.inFPT hFPT)

private theorem sharpKCliqueProblem_triangle_check :
    sharpKCliqueProblem.count ⟨⟨[0, 1, 2], [(0, 1), (1, 2), (0, 2)]⟩, 3⟩ = 1 ∧
      sharpKCliqueProblem.count ⟨⟨[0, 1, 2], [(0, 1), (1, 2)]⟩, 3⟩ = 0 := by
  have h1 : ∀ x : CliqueInstance,
      sharpKCliqueProblem.count x =
        ((Finset.univ : Finset (Finset {v // v ∈ x.graph.vertices})).filter
          fun S ↦ x.graph.induced.IsNClique x.m S).card := by
    intro x
    classical
    rw [sharpKCliqueProblem_count, sharpKCliqueCount, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [h1, h1]
  decide

end SharpWOne

end Computability

/-! ### 3. Exact $k$-Matching Counts and Canonical `#k-Matching` Carrier -/

namespace SimpleGraph

open _root_.SimpleGraph

/-- Exact number of $k$-edge matchings in a simple graph `G : SimpleGraph V`, defined as the
cardinality of `{M : G.Subgraph // M.IsMatching ∧ M.edgeSet.ncard = k}`. -/
@[expose] noncomputable def matchingCount {V : Type*} (G : _root_.SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {M : G.Subgraph // M.IsMatching ∧ M.edgeSet.ncard = k}

private def subgraphOfDisjointEdges {V : Type*} {G : _root_.SimpleGraph V} (S : Set (Sym2 V))
    (hSG : S ⊆ G.edgeSet) : G.Subgraph where
  verts := {v : V | ∃ e ∈ S, v ∈ e}
  Adj u v := s(u, v) ∈ S
  adj_sub h := G.mem_edgeSet.mp (hSG h)
  edge_vert h := ⟨s(_, _), h, Sym2.mem_mk_left _ _⟩
  symm := ⟨fun _ _ h ↦ by rwa [Sym2.eq_swap]⟩

private lemma edgeSet_subgraphOfDisjointEdges {V : Type*} {G : _root_.SimpleGraph V}
    {S : Set (Sym2 V)} (hSG : S ⊆ G.edgeSet) :
    (subgraphOfDisjointEdges S hSG).edgeSet = S := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [Subgraph.mem_edgeSet, subgraphOfDisjointEdges]

private lemma isMatching_subgraphOfDisjointEdges {V : Type*} {G : _root_.SimpleGraph V}
    {S : Set (Sym2 V)} (hSG : S ⊆ G.edgeSet)
    (hdisj : S.Pairwise fun e₁ e₂ ↦ ∀ v, v ∈ e₁ → v ∉ e₂) :
    (subgraphOfDisjointEdges S hSG).IsMatching := by
  rintro v ⟨e, heS, hve⟩
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
  have hvw : v ≠ w := (G.mem_edgeSet.mp (hSG heS)).ne
  refine ⟨w, heS, fun w' hw' ↦ ?_⟩
  have heq : s(v, w') = s(v, w) := by
    by_contra hne
    exact hdisj hw' heS hne v (Sym2.mem_mk_left v w') (Sym2.mem_mk_left v w)
  rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
  · rfl
  · exact absurd rfl hvw

private lemma eq_of_isMatching_of_edgeSet_eq {V : Type*} {G : _root_.SimpleGraph V}
    {M₁ M₂ : G.Subgraph} (h₁ : M₁.IsMatching) (h₂ : M₂.IsMatching)
    (he : M₁.edgeSet = M₂.edgeSet) : M₁ = M₂ := by
  have hadj (u v : V) : M₁.Adj u v ↔ M₂.Adj u v := by
    rw [← M₁.mem_edgeSet, he, M₂.mem_edgeSet]
  refine Subgraph.ext ?_ (funext₂ fun u v ↦ propext (hadj u v))
  ext v
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · obtain ⟨w, hw, -⟩ := h₁ hv
    exact M₂.edge_vert ((hadj v w).mp hw)
  · obtain ⟨w, hw, -⟩ := h₂ hv
    exact M₁.edge_vert ((hadj v w).mpr hw)

/-- **Matching-Edge Bijection**: on a finite simple graph `G`, `matchingCount G k` equals the
number of `k`-element subsets `S ⊆ G.edgeFinset` whose edges are pairwise vertex-disjoint. -/
theorem matchingCount_eq_card_disjoint_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    matchingCount G k =
      ((G.edgeFinset.powersetCard k).filter fun S ↦
        ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ →
          Disjoint e₁.toMultiset.toFinset e₂.toMultiset.toFinset).card := by
  classical
  let Target := {S : Finset (Sym2 V) // S ∈ (G.edgeFinset.powersetCard k).filter fun S ↦
    ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → Disjoint e₁.toMultiset.toFinset e₂.toMultiset.toFinset}
  have hdisj_iff {e₁ e₂ : Sym2 V} :
      Disjoint e₁.toMultiset.toFinset e₂.toMultiset.toFinset ↔ ∀ v, v ∈ e₁ → v ∉ e₂ := by
    simp [Finset.disjoint_left]
  have hSG_of (S : Target) : (S.1 : Set (Sym2 V)) ⊆ G.edgeSet :=
    fun _ he ↦ G.mem_edgeFinset.mp ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp S.2).1).1 he)
  have hDisj_of (S : Target) : (S.1 : Set (Sym2 V)).Pairwise fun e₁ e₂ ↦ ∀ v, v ∈ e₁ → v ∉ e₂ :=
    fun e₁ he₁ e₂ he₂ hne ↦ hdisj_iff.mp ((Finset.mem_filter.mp S.2).2 e₁ he₁ e₂ he₂ hne)
  let φ : {M : G.Subgraph // M.IsMatching ∧ M.edgeSet.ncard = k} ≃ Target :=
    { toFun := fun ⟨M, hM, hk⟩ ↦
        ⟨M.edgeSet.toFinset, by
          have hsub : M.edgeSet.toFinset ⊆ G.edgeFinset := fun e he ↦
            G.mem_edgeFinset.mpr (M.edgeSet_subset (Set.mem_toFinset.mp he))
          have hcard : M.edgeSet.toFinset.card = k := by
            rw [← Set.ncard_eq_toFinset_card']
            exact hk
          refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩
          intro e₁ he₁ e₂ he₂ hne
          rw [hdisj_iff]
          intro v hv₁ hv₂
          obtain ⟨w₁, rfl⟩ := Sym2.mem_iff_exists.mp hv₁
          obtain ⟨w₂, rfl⟩ := Sym2.mem_iff_exists.mp hv₂
          have hadj₁ : M.Adj v w₁ := M.mem_edgeSet.mp (Set.mem_toFinset.mp he₁)
          have hadj₂ : M.Adj v w₂ := M.mem_edgeSet.mp (Set.mem_toFinset.mp he₂)
          obtain ⟨w, -, huniq⟩ := hM (M.edge_vert hadj₁)
          exact hne (by rw [huniq w₁ hadj₁, huniq w₂ hadj₂])⟩
      invFun := fun S ↦
        ⟨subgraphOfDisjointEdges (S.1 : Set (Sym2 V)) (hSG_of S),
          isMatching_subgraphOfDisjointEdges (hSG_of S) (hDisj_of S),
          by rw [edgeSet_subgraphOfDisjointEdges, Set.ncard_coe_finset,
               (Finset.mem_powersetCard.mp (Finset.mem_filter.mp S.2).1).2]⟩
      left_inv := fun ⟨M, hM, hk⟩ ↦ Subtype.ext <|
        eq_of_isMatching_of_edgeSet_eq
          (isMatching_subgraphOfDisjointEdges (hSG_of _) (hDisj_of _)) hM
          (by rw [edgeSet_subgraphOfDisjointEdges, Set.coe_toFinset])
      right_inv := fun S ↦ Subtype.ext <| by
        ext e
        have hmem := Set.ext_iff.mp (edgeSet_subgraphOfDisjointEdges (hSG_of S)) e
        simpa using hmem }
  rw [matchingCount, Nat.card_congr φ, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Every finite simple graph `G` has exactly `1` matching of size `0` (the empty subgraph `⊥`). -/
@[simp]
theorem matchingCount_zero {V : Type*} [Finite V] (G : _root_.SimpleGraph V) :
    matchingCount G 0 = 1 := by
  have hbot : (⊥ : G.Subgraph).IsMatching ∧ (⊥ : G.Subgraph).edgeSet.ncard = 0 :=
    ⟨fun v hv ↦ False.elim hv, by simp⟩
  have : Unique {M : G.Subgraph // M.IsMatching ∧ M.edgeSet.ncard = 0} :=
    { default := ⟨⊥, hbot⟩
      uniq := fun ⟨M, hM, hk⟩ ↦ Subtype.ext <| by
        have hemp : M.edgeSet = ∅ := (Set.ncard_eq_zero (hs := Set.toFinite _)).mp hk
        exact eq_of_isMatching_of_edgeSet_eq hM hbot.1 (by simp [hemp]) }
  rw [matchingCount, Nat.card_unique]

/-- On an edgeless graph `⊥`, `matchingCount ⊥ (k + 1) = 0`. -/
@[simp]
theorem matchingCount_bot_succ {V : Type*} (k : ℕ) :
    matchingCount (⊥ : _root_.SimpleGraph V) (k + 1) = 0 := by
  rw [matchingCount, Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨M, _, hk⟩ ↦ ?_⟩
  have hemp : M.edgeSet = ∅ := by simpa using M.edgeSet_subset
  simp [hemp] at hk

/-- **Vertex-Count Bound**: if `Fintype.card V < 2 * k`, then `G` has zero $k$-matchings. -/
theorem matchingCount_eq_zero_of_card_lt_two_mul {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {k : ℕ} (hlt : Fintype.card V < 2 * k) :
    matchingCount G k = 0 := by
  classical
  rw [matchingCount_eq_card_disjoint_edgeFinset, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS hpair
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  let U : Finset V := S.biUnion fun e ↦ e.toMultiset.toFinset
  have hU_card : U.card = 2 * k := by
    rw [Finset.card_biUnion (fun e₁ he₁ e₂ he₂ hne ↦ hpair e₁ he₁ e₂ he₂ hne)]
    have htwo : ∀ e ∈ S, e.toMultiset.toFinset.card = 2 := by
      intro e he
      have hadj := G.mem_edgeFinset.mp (hsub he)
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := G.ne_of_adj hadj
        simp [Sym2.toMultiset, Finset.card_pair huv]
    rw [Finset.sum_congr rfl htwo, Finset.sum_const, hcard, smul_eq_mul, mul_comm]
  have hle : U.card ≤ Fintype.card V := Finset.card_le_univ U
  omega

/-- Concrete evaluation on `K_2`: the complete graph on `Fin 2` has exactly `1` matching of size
`1`. -/
theorem matchingCount_top_two_one :
    matchingCount (⊤ : _root_.SimpleGraph (Fin 2)) 1 = 1 := by
  rw [matchingCount_eq_card_disjoint_edgeFinset]
  decide

end SimpleGraph

namespace Computability

/-- Canonical `#k-Matching` parameterized counting problem on `(G, k) : Graph × ℕ`: given an
encoded graph `G` and parameter `k`, count the $k$-edge matchings in `G.induced`. -/
@[expose] noncomputable def sharpKMatchingProblem : ParameterizedCountingProblem (Graph × ℕ) where
  enc := encPair encGraph encNat
  count p := CslibFrontier.SimpleGraph.matchingCount p.1.induced p.2
  param := Prod.snd
  param_polyTime := ComputableInPolyTime.snd encGraph encNat

/-- Unfolding `sharpKMatchingProblem.count`. -/
@[simp, grind =]
theorem sharpKMatchingProblem_count (G : Graph) (k : ℕ) :
    sharpKMatchingProblem.count (G, k) = CslibFrontier.SimpleGraph.matchingCount G.induced k := rfl

/-- Unfolding `sharpKMatchingProblem.param`. -/
@[simp, grind =]
theorem sharpKMatchingProblem_param (G : Graph) (k : ℕ) :
    sharpKMatchingProblem.param (G, k) = k := rfl

end Computability

end CslibFrontier
