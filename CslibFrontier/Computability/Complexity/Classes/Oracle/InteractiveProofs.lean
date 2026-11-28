module

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.PolyRounds
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.Repetition
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PH
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.RoundCollapse
public import CslibFrontier.Computability.Complexity.Classes.IP.Games
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.Emulation
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.GoldwasserSipser
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.PolyRounds
public import CslibFrontier.Computability.Complexity.Classes.IP.Games.Repetition
public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.PH.OracleCollapse
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Combinatorics.Lautemann
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Languages.Probabilistic.Iteration
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Relativized Polynomial Hierarchy, Arthur–Merlin Games, and Interactive Proofs

This module extends the relativized polynomial hierarchy (`Cslib.Complexity.SigmaPWithOracle`,
`Cslib.Complexity.PHWithOracle`) with universal levels (`PiPWithOracle`), relativized
Arthur–Merlin games (`AMWithOracle`, `MAWithOracle`, `AMGameClassWithOracle`, `AMkWithOracle`),
and relativized private-coin interactive proof games (`IPGameClassWithOracle`, `IPkWithOracle`)
relative to a classical Boolean oracle language `O : Set (List Bool)`.

By equipping `ComputableInPolyTimeWithOracle` with bounded-loop combinators (`allWithInput`,
`anyWithInput`, `countPWithInput`), we lift the purely combinatorial game
theorems of `CslibFrontier` to any oracle `O`, establishing:
* `AM^O ⊆ Π₂^{p,O} ⊆ PH^O`;
* `AM[k]^O = AM^O` for all constant `k ≥ 2`;
* `IP[k]^O ⊆ AM[k+2]^O = AM^O ⊆ PH^O` for all constant `k`.

## Main definitions

* `CslibFrontier.Complexity.PiPWithOracle`: universal levels `Π_k^{p,O}` of the relativized
  polynomial hierarchy (complementing `Cslib.Complexity.SigmaPWithOracle` and
  `Cslib.Complexity.PHWithOracle`).
* `CslibFrontier.Complexity.AMWithOracle`, `CslibFrontier.Complexity.MAWithOracle`,
  `CslibFrontier.Complexity.AMGameClassWithOracle`, `CslibFrontier.Complexity.AMkWithOracle`:
  relativized Arthur–Merlin classes.
* `CslibFrontier.Complexity.IPGameClassWithOracle`, `CslibFrontier.Complexity.IPkWithOracle`:
  relativized interactive proof game classes.
* `CslibFrontier.Complexity.runStateful`: execution of a private-coin interactive game against an
  arbitrary stateful prover.

## Main results

* `CslibFrontier.Complexity.AMWithOracle_subset_PiPWithOracle_two`: `AM^O ⊆ Π₂^{p,O}`.
* `CslibFrontier.Complexity.AMGameClassWithOracle_subset_AMWithOracle`: `AMGame^O[π] ⊆ AM^O`.
* `CslibFrontier.Complexity.AMkWithOracle_eq_AMWithOracle`: `AM[k]^O = AM^O` for `k ≥ 2`.
* `CslibFrontier.Complexity.IPGameClassWithOracle_subset_AMGameClassWithOracle`: relativized
  Goldwasser–Sipser private-coin emulation.
* `CslibFrontier.Complexity.IPkWithOracle_subset_PHWithOracle`: every constant-message interactive
  proof system relative to `O` lies in `PH^O`.

-/

public section

namespace CslibFrontier

namespace Complexity

open Cslib Cslib.Complexity Cslib.Probability Finset Turing.MultiTapeTM

attribute [local irreducible] ComputableInPolyTime

variable {α β γ : Type}

/-! ### Oracle polynomial-time combinators -/

namespace OraclePoly

/-- Conditional selection between two oracle polynomial-time computations driven by a plain
polynomial-time Boolean condition. -/
theorem cond {O : Set (List Bool)} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c input encBool)
    (hf : ComputableInPolyTimeWithOracle O f input output)
    (hg : ComputableInPolyTimeWithOracle O g input output) :
    ComputableInPolyTimeWithOracle O (fun a => if c a then f a else g a) input output := by
  obtain ⟨pf, hpf, hfeq⟩ := hf
  obtain ⟨pg, hpg, hgeq⟩ := hg
  refine ⟨fun a => if c a then pf a else pg a, ?_, fun a => ?_⟩
  · refine (hpf.cond hc hpg).congr fun a State oracle s => ?_
    cases hca : c a <;> simp [hca]
  · dsimp only
    cases hca : c a
    · simp only [Bool.false_eq_true, ↓reduceIte, hgeq]
    · simp only [↓reduceIte, hfeq]

/-- Bounded loop over `ℕ` preserving a polynomial-time invariant on every reachable state in
`OracleComp.support`. -/
theorem iterateWith_spec {O : Set (List Bool)} {σ : Type} {input : α ↪ List Bool}
    {stateEnc : σ ↪ List Bool} {count : α → ℕ} {initial : α → σ} {step : α → σ → σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEnc)
    (_hstep : ComputableInPolyTimeWithOracle O (fun p : α × σ => step p.1 p.2)
      (encPair input stateEnc) stateEnc)
    (invariant : α → ℕ → σ → Prop)
    (hbase : ∀ a, invariant a 0 (initial a))
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state → (stateEnc state).length ≤ size a) :
    ∀ (stepProg : α × σ → WordQueryComp Unit σ),
      IsOraclePPTOn (encPair input stateEnc) stateEnc
        (fun p => OracleComp.interpret ProbOracleComp.query (stepProg p)) →
      (∀ p, OracleComp.interpret (m := Id) (languageOracle O) (stepProg p) = step p.1 p.2) →
      (∀ a i state, i < count a → invariant a i state →
        ∀ next ∈ OracleComp.support
          (OracleComp.interpret ProbOracleComp.query (stepProg (a, state))),
          invariant a (i + 1) next) →
      ComputableInPolyTimeWithOracle O (fun a => (step a)^[count a] (initial a))
        input stateEnc := by
  intro stepProg hstepPPT hstepEq hpres
  have hiter := IsOraclePPTOn.iterateWith_spec
    (step := fun a s => OracleComp.interpret ProbOracleComp.query (stepProg (a, s)))
    hcount hinitial hstepPPT invariant hbase hpres hsize hbound
  refine ⟨fun a => OracleComp.iterate (count a) (fun s => stepProg (a, s)) (initial a), ?_,
    fun a => ?_⟩
  · simpa only [OracleComp.interpret_iterate] using hiter.1
  · clear hiter hstepPPT hpres hbound hsize hbase _hstep hinitial hcount
    dsimp only
    induction count a with
    | zero => rfl
    | succ k ih =>
      rw [OracleComp.iterate_succ, OracleComp.interpret_bind, ih, Function.iterate_succ_apply']
      exact hstepEq (a, (step a)^[k] (initial a))

/-- Evaluate `(List.range (m a)).all (fun i => test (a, i))` in oracle polynomial time. -/
theorem allWithInput {O : Set (List Bool)} {input : α ↪ List Bool} {m : α → ℕ}
    {test : α × ℕ → Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (htest : ComputableInPolyTimeWithOracle O test (encPair input encUnary) encBool) :
    ComputableInPolyTimeWithOracle O (fun a => (List.range (m a)).all fun i => test (a, i))
      input encBool := by
  obtain ⟨prog, hprog, hprogeq⟩ := htest
  let stepFn (a : α) (st : ℕ × Bool) : ℕ × Bool := (st.1 + 1, st.2 && test (a, st.1))
  let stepProg (p : α × (ℕ × Bool)) : WordQueryComp Unit (ℕ × Bool) :=
    (fun b => (p.2.1 + 1, p.2.2 && b)) <$> prog (p.1, p.2.1)
  have hstepPPT : IsOraclePPTOn (encPair input (encPair encUnary encBool))
      (encPair encUnary encBool)
      (fun p => OracleComp.interpret ProbOracleComp.query (stepProg p)) := by
    have hpre : ComputableInPolyTime (fun p : α × (ℕ × Bool) => (p.1, p.2.1))
        (encPair input (encPair encUnary encBool)) (encPair input encUnary) := by fun_prop
    have h1 := hprog.preprocess hpre
    have hpost : ComputableInPolyTime
        (fun q : (α × (ℕ × Bool)) × Bool => (q.1.2.1 + 1, q.1.2.2 && q.2))
        (encPair (encPair input (encPair encUnary encBool)) encBool)
        (encPair encUnary encBool) := by fun_prop
    simpa only [stepProg, OracleComp.interpret_map] using h1.map_with hpost
  have hstepEq : ∀ p, OracleComp.interpret (m := Id) (languageOracle O) (stepProg p) =
      stepFn p.1 p.2 := fun p => by
    simp only [stepProg, stepFn, OracleComp.interpret_map, hprogeq]
    rfl
  have hstepOracle : ComputableInPolyTimeWithOracle O (fun p : α × (ℕ × Bool) => stepFn p.1 p.2)
      (encPair input (encPair encUnary encBool)) (encPair encUnary encBool) :=
    ⟨stepProg, hstepPPT, hstepEq⟩
  have hloop := iterateWith_spec hm (initial := fun _ => (0, true)) (by fun_prop) hstepOracle
    (fun _ i st => st.1 = i) (fun _ => rfl)
    (size := fun a => 2 * m a + 2) (by
      obtain ⟨c, d, hc⟩ := hm.polyBounded_length.exists_le
      refine PolyBounded.of_forall_le (2 * c + 2) d fun a => ?_
      have hma : m a ≤ c * ((input a).length + 1) ^ d := by
        simpa [encUnary_apply] using hc a
      have hpow : 1 ≤ ((input a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith)
    (fun a i st hi hinv => by
      subst hinv
      simp only [length_encPair, encUnary_apply, encBool_apply, List.length_replicate,
        List.length_singleton]
      omega)
    stepProg hstepPPT hstepEq
    (fun a i st _ hinv next hnext => by
      simp only [stepProg, OracleComp.interpret_map, OracleComp.support,
        OracleComp.mem_supportWith_map_iff] at hnext
      obtain ⟨b, _, rfl⟩ := hnext
      exact congrArg (· + 1) hinv)
  have hval : ∀ a k, ((stepFn a)^[k] (0, true)) =
      (k, (List.range k).all fun i => test (a, i)) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, List.range_succ, List.all_append]
      simp [stepFn]
  have hres := hloop.map (g := Prod.snd) (by fun_prop)
  simpa only [hval] using hres

/-- Evaluate `(List.range (m a)).any (fun i => test (a, i))` in oracle polynomial time. -/
theorem anyWithInput {O : Set (List Bool)} {input : α ↪ List Bool} {m : α → ℕ}
    {test : α × ℕ → Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (htest : ComputableInPolyTimeWithOracle O test (encPair input encUnary) encBool) :
    ComputableInPolyTimeWithOracle O (fun a => (List.range (m a)).any fun i => test (a, i))
      input encBool := by
  have hall := allWithInput hm (htest.map (g := Bool.not) (by fun_prop))
  have hnot := hall.map (g := Bool.not) (by fun_prop)
  refine ⟨hnot.choose, hnot.choose_spec.1, fun a => ?_⟩
  rw [hnot.choose_spec.2 a]
  rw [Bool.eq_iff_iff]
  simp

/-- Evaluate `(List.range (m a)).countP (fun i => test (a, i))` in oracle polynomial time. -/
theorem countPWithInput {O : Set (List Bool)} {input : α ↪ List Bool} {m : α → ℕ}
    {test : α × ℕ → Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (htest : ComputableInPolyTimeWithOracle O test (encPair input encUnary) encBool) :
    ComputableInPolyTimeWithOracle O (fun a => (List.range (m a)).countP fun i => test (a, i))
      input encUnary := by
  obtain ⟨prog, hprog, hprogeq⟩ := htest
  let stepFn (a : α) (st : ℕ × ℕ) : ℕ × ℕ :=
    (st.1 + 1, st.2 + (test (a, st.1)).toNat)
  let stepProg (p : α × (ℕ × ℕ)) : WordQueryComp Unit (ℕ × ℕ) :=
    (fun b => (p.2.1 + 1, p.2.2 + b.toNat)) <$> prog (p.1, p.2.1)
  have hstepPPT : IsOraclePPTOn (encPair input (encPair encUnary encUnary))
      (encPair encUnary encUnary)
      (fun p => OracleComp.interpret ProbOracleComp.query (stepProg p)) := by
    have hpre : ComputableInPolyTime (fun p : α × (ℕ × ℕ) => (p.1, p.2.1))
        (encPair input (encPair encUnary encUnary)) (encPair input encUnary) := by fun_prop
    have h1 := hprog.preprocess hpre
    have hpost : ComputableInPolyTime
        (fun q : (α × (ℕ × ℕ)) × Bool => (q.1.2.1 + 1, q.1.2.2 + q.2.toNat))
        (encPair (encPair input (encPair encUnary encUnary)) encBool)
        (encPair encUnary encUnary) := by fun_prop
    simpa only [stepProg, OracleComp.interpret_map] using h1.map_with hpost
  have hstepEq : ∀ p, OracleComp.interpret (m := Id) (languageOracle O) (stepProg p) =
      stepFn p.1 p.2 := fun p => by
    simp only [stepProg, stepFn, OracleComp.interpret_map, hprogeq]
    rfl
  have hstepOracle : ComputableInPolyTimeWithOracle O (fun p : α × (ℕ × ℕ) => stepFn p.1 p.2)
      (encPair input (encPair encUnary encUnary)) (encPair encUnary encUnary) :=
    ⟨stepProg, hstepPPT, hstepEq⟩
  have hloop := iterateWith_spec hm (initial := fun _ => (0, 0)) (by fun_prop) hstepOracle
    (fun _ i st => st.1 = i ∧ st.2 ≤ i) (fun _ => ⟨rfl, le_rfl⟩)
    (size := fun a => 3 * m a + 1) (by
      obtain ⟨c, d, hc⟩ := hm.polyBounded_length.exists_le
      refine PolyBounded.of_forall_le (3 * c + 1) d fun a => ?_
      have hma : m a ≤ c * ((input a).length + 1) ^ d := by
        simpa [encUnary_apply] using hc a
      have hpow : 1 ≤ ((input a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith)
    (fun a i st hi hinv => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)
    stepProg hstepPPT hstepEq
    (fun a i st _ hinv next hnext => by
      simp only [stepProg, OracleComp.interpret_map, OracleComp.support,
        OracleComp.mem_supportWith_map_iff] at hnext
      obtain ⟨b, _, rfl⟩ := hnext
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      exact ⟨congrArg (· + 1) hinv.1, by omega⟩)
  have hval : ∀ a k, ((stepFn a)^[k] (0, 0)) =
      (k, (List.range k).countP fun i => test (a, i)) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, List.range_succ, List.countP_append]
      simp only [stepFn, List.countP_cons, List.countP_nil, zero_add]
      cases test (a, k) <;> simp
  have hres := hloop.map (g := Prod.snd) (by fun_prop)
  simpa only [hval] using hres

end OraclePoly

/-! ### Relativized Polynomial Hierarchy -/

/-- **Relativized `Π_k^{p,O}`**: languages verified by `k` alternating polynomial-length quantifier
blocks starting universally, with a deterministic polynomial-time oracle verifier relative to
`O`. -/
@[expose] def PiPWithOracle (O : Set (List Bool)) (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool),
    ps.length = k ∧ ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc false ps V A}

theorem mem_PiPWithOracle {O : Set (List Bool)} {k : ℕ} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PiPWithOracle O k enc ↔
      ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool),
        ps.length = k ∧ ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool ∧
          IsAlternatingVerifier enc false ps V A := Iff.rfl

theorem SigmaPWithOracle_subset_SigmaPWithOracle_succ (O : Set (List Bool)) (k : ℕ)
    (enc : α ↪ List Bool) : SigmaPWithOracle O k enc ⊆ SigmaPWithOracle O (k + 1) enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  exact ⟨ps ++ [0], V, by simp [hlen], hV, hA.append_zero⟩

theorem PiPWithOracle_subset_SigmaPWithOracle_succ (O : Set (List Bool)) (k : ℕ)
    (enc : α ↪ List Bool) : PiPWithOracle O k enc ⊆ SigmaPWithOracle O (k + 1) enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  exact ⟨0 :: ps, V, by simp [hlen], hV, hA.zero_cons⟩

theorem PiPWithOracle_subset_PHWithOracle (O : Set (List Bool)) (k : ℕ) (enc : α ↪ List Bool) :
    PiPWithOracle O k enc ⊆ PHWithOracle O enc :=
  (PiPWithOracle_subset_SigmaPWithOracle_succ O k enc).trans
    (Set.subset_iUnion (fun i => SigmaPWithOracle O i enc) (k + 1))

theorem SigmaPWithOracle_zero (O : Set (List Bool)) (enc : α ↪ List Bool) :
    SigmaPWithOracle O 0 enc = PWithOracle O enc := by
  ext A
  constructor
  · rintro ⟨ps, V, hlen, hV, hA⟩
    obtain rfl := List.length_eq_zero_iff.mp hlen
    refine ⟨fun a => V (a, []), hV.preprocess (ComputableInPolyTime.id'.prod (.const [])),
      fun a => ?_⟩
    simpa [IsAlternatingVerifier, Alternation] using hA a
  · rintro ⟨f, hf, hA⟩
    refine ⟨[], fun x => f x.1, rfl, hf.preprocess (.fst _ _), fun a => ?_⟩
    simpa [IsAlternatingVerifier, Alternation] using hA a

theorem SigmaPWithOracle_one (O : Set (List Bool)) (enc : α ↪ List Bool) :
    SigmaPWithOracle O 1 enc = NPWithOracle O enc := by
  ext A
  constructor
  · rintro ⟨ps, V, hlen, hV, hA⟩
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨p, V, hV, isAlternatingVerifier_true_singleton.mp hA⟩
  · rintro ⟨p, V, hV, hA⟩
    exact ⟨[p], V, rfl, hV, isAlternatingVerifier_true_singleton.mpr hA⟩

/-! ### Relativized Arthur–Merlin and Interactive Proof Game Classes -/

/-- **Relativized `AM^O`**: languages with two-message public-coin Arthur–Merlin proof systems
whose verifier runs in polynomial time relative to `O`. -/
@[expose] def AMWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool ∧
      IsArthurMerlinVerifier enc p q V A}

/-- **Relativized `MA^O`**: languages with two-message Merlin–Arthur proof systems whose verifier
runs in polynomial time relative to `O`. -/
@[expose] def MAWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool ∧
      IsMerlinArthurVerifier enc q p V A}

/-- **Relativized public-coin game class `AM^O[π]`** for a fixed move pattern `π`. -/
@[expose] def AMGameClassWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool)
    (π : List AMMove) : Set (Set α) :=
  {A | ∃ (G : List (AMMove × Polynomial ℕ)) (V : α × List Bool → Bool),
    G.map Prod.fst = π ∧ ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool ∧
      IsAMGameVerifier enc G V A}

/-- **Relativized `AM[k]^O`**: public-coin games with `k` alternating moves starting with Arthur. -/
@[expose] def AMkWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  AMGameClassWithOracle O enc (alternatingMoves .arthur k)

/-- **Relativized private-coin game class `IP^O[π]`** for a fixed move pattern `π`. -/
@[expose] def IPGameClassWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool)
    (π : List IPMove) : Set (Set α) :=
  {A | ∃ (G : List (IPMove × Polynomial ℕ)) (ρ : Polynomial ℕ)
    (msg : α × List Bool × ℕ × List Bool → List Bool) (dec : α × List Bool × List Bool → Bool),
    G.map Prod.fst = π ∧
      ComputableInPolyTimeWithOracle O msg (IPGame.encMsgInput enc) encBits ∧
      ComputableInPolyTimeWithOracle O dec (IPGame.encDecInput enc) encBool ∧
      IsIPGameVerifier enc G ρ msg dec A}

/-- **Relativized `IP[k]^O`**: private-coin interactive proofs with `k` alternating moves starting
with the verifier. -/
@[expose] def IPkWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  IPGameClassWithOracle O enc ((alternatingMoves .arthur k).map AMMove.toIP)

/-- **Relativized `AM^O ⊆ Π₂^{p,O}`**. -/
theorem AMWithOracle_subset_PiPWithOracle_two (O : Set (List Bool)) (enc : α ↪ List Bool) :
    AMWithOracle O enc ⊆ PiPWithOracle O 2 enc := by
  rintro A ⟨p, q, V, hV, hAM⟩
  let e : Polynomial ℕ := 12 * p + 1
  have hrep : ComputableInPolyTimeWithOracle O
      (arthurMerlinRepeat enc (6 * e) p q V) (encPair enc encBits) encBool := by
    unfold arthurMerlinRepeat
    have hm : ComputableInPolyTime (fun x : α × List Bool => 2 * (6 * e).eval (enc x.1).length)
        (encPair enc encBits) encUnary := by fun_prop
    have htest : ComputableInPolyTimeWithOracle O
        (fun y : (α × List Bool) × ℕ =>
          V (y.1.1, BitString.listRow (p.eval (enc y.1.1).length) y.2 y.1.2 ++
            BitString.listRow (q.eval (enc y.1.1).length) y.2
              (y.1.2.drop (2 * (6 * e).eval (enc y.1.1).length * p.eval (enc y.1.1).length))))
        (encPair (encPair enc encBits) encUnary) encBool :=
      hV.preprocess (by fun_prop)
    have hcnt := OraclePoly.countPWithInput hm htest
    have hthr : ComputableInPolyTime (fun x : α × List Bool => (6 * e).eval (enc x.1).length)
        (encPair enc encBits) encUnary := by fun_prop
    exact (hcnt.map_with (g := fun x cnt => decide ((6 * e).eval (enc x.1).length < cnt))
      (by fun_prop))
  have hpi2 : ComputableInPolyTimeWithOracle O
      (ArthurMerlin.piTwoVerifier enc e (12 * e * p) (12 * e * q)
        (arthurMerlinRepeat enc (6 * e) p q V))
      (encPair enc encBits) encBool := by
    unfold ArthurMerlin.piTwoVerifier
    have hm : ComputableInPolyTime (fun x : α × List Bool => e.eval (enc x.1).length)
        (encPair enc encBits) encUnary := by fun_prop
    have htest : ComputableInPolyTimeWithOracle O
        (fun y : (α × List Bool) × ℕ =>
          arthurMerlinRepeat enc (6 * e) p q V
            (y.1.1,
              List.zipWith Bool.xor
                (BitString.listRow ((12 * e * p).eval (enc y.1.1).length) 0
                  (y.1.2.drop (e.eval (enc y.1.1).length *
                    (12 * e * p).eval (enc y.1.1).length)))
                (BitString.listRow ((12 * e * p).eval (enc y.1.1).length) y.2 y.1.2) ++
              BitString.listRow ((12 * e * q).eval (enc y.1.1).length) y.2
                (y.1.2.drop (e.eval (enc y.1.1).length *
                  (12 * e * p).eval (enc y.1.1).length +
                  (12 * e * p).eval (enc y.1.1).length))))
        (encPair (encPair enc encBits) encUnary) encBool :=
      hrep.preprocess (by fun_prop)
    exact OraclePoly.allWithInput hm htest
  refine ⟨[e * (12 * e * p), 12 * e * p + e * (12 * e * q)], _, rfl, hpi2,
    ArthurMerlin.isAlternatingVerifier_piTwoVerifier (hAM.repeatMajority e)
      (fun n => ArthurMerlin.eval_lt_mul p n) (fun n => by
        dsimp only [e]
        exact Nat.lt_two_pow_self)⟩

/-- **`AM^O ⊆ PH^O`** for every oracle `O`. -/
theorem AMWithOracle_subset_PHWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) :
    AMWithOracle O enc ⊆ PHWithOracle O enc :=
  (AMWithOracle_subset_PiPWithOracle_two O enc).trans (PiPWithOracle_subset_PHWithOracle O 2 enc)

/-- Relativized `AMGame.majority` runs in oracle polynomial time. -/
private theorem computableInPolyTimeWithOracle_majority {O : Set (List Bool)}
    {enc : α ↪ List Bool} (G : List (AMMove × Polynomial ℕ)) (k : Polynomial ℕ)
    {V : α × List Bool → Bool}
    (hV : ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool) :
    ComputableInPolyTimeWithOracle O
      (fun x : α × List Bool =>
        AMGame.majority (AMGame.evalShape G (enc x.1).length) (k.eval (enc x.1).length)
          (fun t => V (x.1, t)) x.2)
      (encPair enc encBits) encBool := by
  have hlen : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ => (enc y.1.1).length)
      (encPair (encPair enc encBits) encUnary) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp
      ((ComputableInPolyTime.fst _ _).comp (.fst _ _))
  have hcopy : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ =>
        (y.1.1, AMGame.copyTranscript (2 * k.eval (enc y.1.1).length) y.2
          (AMGame.evalShape G (enc y.1.1).length) y.1.2))
      (encPair (encPair enc encBits) encUnary) (encPair enc encBits) := by
    have h1 : ComputableInPolyTime (fun y : (α × List Bool) × ℕ => y.1.1)
        (encPair (encPair enc encBits) encUnary) enc := by fun_prop
    have h2 := AMGame.computableInPolyTime_copyTranscript G hlen
      (m := fun y => 2 * k.eval (enc y.1.1).length)
      (i := fun y => y.2) (w := fun y => y.1.2)
      (by fun_prop) (by fun_prop) (by fun_prop)
    exact h1.prod h2
  have hm : ComputableInPolyTime (fun x : α × List Bool => 2 * k.eval (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hk : ComputableInPolyTime (fun x : α × List Bool => k.eval (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hcnt := OraclePoly.countPWithInput hm (hV.preprocess hcopy)
  have hfinal := ((hk.computableInPolyTimeWithOracle O).prod hcnt).map
    (g := fun p : ℕ × ℕ => decide (p.1 < p.2)) (by fun_prop)
  refine ⟨hfinal.choose, hfinal.choose_spec.1, fun x => ?_⟩
  rw [hfinal.choose_spec.2 x]
  rfl

/-- Transparent local copy of `AMGame.swapVerifier` (opaque in `RoundCollapse.lean`). -/
private def swapVerifierLocal (L P q : ℕ) (g' : List (AMMove × ℕ)) (k : ℕ)
    (V : List Bool → Bool) (w : List Bool) : Bool :=
  AMGame.majority g' k (fun u => V (w.take L ++ ((w.drop (L + P)).take q ++ u)))
    ((w.drop L).take P ++ w.drop (L + P + q))

private theorem swapVerifierLocal_apply {L P q : ℕ} (g' : List (AMMove × ℕ)) (k : ℕ)
    (V : List Bool → Bool) {s : List Bool} (hs : s.length = L) (R : Fin P → Bool)
    (y : Fin q → Bool) (t : List Bool) :
    swapVerifierLocal L P q g' k V (s ++ (List.ofFn R ++ (List.ofFn y ++ t))) =
      AMGame.majority g' k (fun u => V (s ++ (List.ofFn y ++ u))) (List.ofFn R ++ t) := by
  have e2 : ((s ++ (List.ofFn R ++ (List.ofFn y ++ t))).drop (L + P)).take q = List.ofFn y := by
    rw [← List.append_assoc, List.drop_left' (by simp [hs]), List.take_left' List.length_ofFn]
  have e4 : (s ++ (List.ofFn R ++ (List.ofFn y ++ t))).drop (L + P + q) = t := by
    rw [← List.append_assoc, ← List.append_assoc, List.drop_left' (by simp [hs]; omega)]
  rw [swapVerifierLocal, List.take_left' hs, e2, List.drop_left' hs,
    List.take_left' List.length_ofFn, e4]

private theorem value_swap_local_le (σ τ : List (AMMove × ℕ)) (q p k : ℕ)
    (V : List Bool → Bool) :
    AMGame.value true (σ ++ (.arthur, 2 * k * p) :: (.merlin, q) :: AMGame.repeatShape (2 * k) τ)
      (fun w => ((swapVerifierLocal (AMGame.transcriptLength σ) (2 * k * p) q
        ((.arthur, p) :: τ) k V w).toNat : ℚ)) ≤
      3 * AMGame.value true (σ ++ (.merlin, q) :: (.arthur, p) :: τ) (fun w => ((V w).toNat : ℚ)) +
        2 ^ q * ((8 / 9 : ℚ) ^ k / 2) := by
  rw [AMGame.value_append, AMGame.value_append,
    ← AMGame.value_affine _ _ _ (by norm_num : (0 : ℚ) ≤ 3)]
  refine AMGame.value_mono_of_length _ _ fun s hs => ?_
  rw [AMGame.value_arthur, AMGame.value_merlin_true]
  simp only [AMGame.value_merlin_true, swapVerifierLocal_apply _ _ _ hs]
  set H : (Fin (2 * k * p) → Bool) → (Fin q → Bool) → ℚ := fun R y =>
    AMGame.value true (AMGame.repeatShape (2 * k) τ) fun t =>
      ((AMGame.majority ((.arthur, p) :: τ) k (fun u => V (s ++ (List.ofFn y ++ u)))
        (List.ofFn R ++ t)).toNat : ℚ)
  have hH0 (R y) : 0 ≤ H R y := AMGame.value_nonneg _ _ fun _ => by positivity
  have hH1 (R y) : H R y ≤ 1 := AMGame.value_le_one _ _ fun t => by
    cases AMGame.majority ((.arthur, p) :: τ) k _ (List.ofFn R ++ t) <;> norm_num
  have hP : (0 : ℚ) < 2 ^ (2 * k * p) := by positivity
  set m := univ.sup' univ_nonempty fun y : Fin q → Bool =>
    AMGame.value true ((.arthur, p) :: τ) fun u => ((V (s ++ (List.ofFn y ++ u))).toNat : ℚ)
  have hm0 : 0 ≤ m := (AMGame.value_nonneg _ _ fun _ => by positivity).trans
    (le_sup' (f := fun y : Fin q → Bool => AMGame.value true ((.arthur, p) :: τ)
      fun u => ((V (s ++ (List.ofFn y ++ u))).toNat : ℚ)) (mem_univ fun _ => false))
  have hε : (0 : ℚ) ≤ 2 ^ q * ((8 / 9 : ℚ) ^ k / 2) := by positivity
  by_cases hc : 1 ≤ 3 * m
  · have : (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p) ≤ 1 := by
      rw [div_le_one hP]
      calc _ ≤ ∑ _R : Fin (2 * k * p) → Bool, (1 : ℚ) :=
            sum_le_sum fun R _ => sup'_le _ _ fun y _ => hH1 R y
        _ = _ := by simp
    exact this.trans (by linarith)
  · push Not at hc
    have hF (y : Fin q → Bool) : (∑ R, H R y) / 2 ^ (2 * k * p) ≤ (8 / 9 : ℚ) ^ k / 2 :=
      AMGame.value_majority_le ((.arthur, p) :: τ) k _ (by
        linarith [le_sup' (f := fun y : Fin q → Bool => AMGame.value true ((.arthur, p) :: τ)
          fun u => ((V (s ++ (List.ofFn y ++ u))).toNat : ℚ)) (mem_univ y)])
    calc (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p)
        ≤ (∑ R, ∑ y, H R y) / 2 ^ (2 * k * p) := by
          gcongr with R
          exact sup'_le _ _ fun y _ => single_le_sum (fun j _ => hH0 R j) (mem_univ y)
      _ = ∑ y, (∑ R, H R y) / 2 ^ (2 * k * p) := by
          rw [sum_comm]; simp only [div_eq_mul_inv, sum_mul]
      _ ≤ ∑ _y : Fin q → Bool, (8 / 9 : ℚ) ^ k / 2 := sum_le_sum fun y _ => hF y
      _ = 2 ^ q * ((8 / 9 : ℚ) ^ k / 2) := by simp
      _ ≤ _ := by linarith

private theorem value_swap_local_ge (σ τ : List (AMMove × ℕ)) (q p k : ℕ)
    (V : List Bool → Bool) :
    3 * AMGame.value true (σ ++ (.merlin, q) :: (.arthur, p) :: τ) (fun w => ((V w).toNat : ℚ)) +
        (-2 - (8 / 9 : ℚ) ^ k) ≤
      AMGame.value true (σ ++ (.arthur, 2 * k * p) :: (.merlin, q) :: AMGame.repeatShape (2 * k) τ)
        (fun w => ((swapVerifierLocal (AMGame.transcriptLength σ) (2 * k * p) q
          ((.arthur, p) :: τ) k V w).toNat : ℚ)) := by
  rw [AMGame.value_append, AMGame.value_append,
    ← AMGame.value_affine _ _ _ (by norm_num : (0 : ℚ) ≤ 3)]
  refine AMGame.value_mono_of_length _ _ fun s hs => ?_
  rw [AMGame.value_arthur, AMGame.value_merlin_true]
  simp only [AMGame.value_merlin_true, swapVerifierLocal_apply _ _ _ hs]
  set H : (Fin (2 * k * p) → Bool) → (Fin q → Bool) → ℚ := fun R y =>
    AMGame.value true (AMGame.repeatShape (2 * k) τ) fun t =>
      ((AMGame.majority ((.arthur, p) :: τ) k (fun u => V (s ++ (List.ofFn y ++ u)))
        (List.ofFn R ++ t)).toNat : ℚ)
  have hH0 (R y) : 0 ≤ H R y := AMGame.value_nonneg _ _ fun _ => by positivity
  have hP : (0 : ℚ) < 2 ^ (2 * k * p) := by positivity
  have hrhs : 0 ≤ (∑ R, univ.sup' univ_nonempty (H R)) / 2 ^ (2 * k * p) :=
    div_nonneg (sum_nonneg fun R _ => (hH0 R fun _ => false).trans
      (le_sup' (H R) (mem_univ _))) hP.le
  obtain ⟨y₀, _, hy₀⟩ := exists_mem_eq_sup' univ_nonempty (fun y : Fin q → Bool =>
    AMGame.value true ((.arthur, p) :: τ) fun u => ((V (s ++ (List.ofFn y ++ u))).toNat : ℚ))
  rw [hy₀]
  have hv1 : AMGame.value true ((.arthur, p) :: τ)
      (fun u => ((V (s ++ (List.ofFn y₀ ++ u))).toNat : ℚ)) ≤ 1 :=
    AMGame.value_le_one _ _ fun t => by cases V (s ++ (List.ofFn y₀ ++ t)) <;> norm_num
  have hpow : (0 : ℚ) ≤ (8 / 9 : ℚ) ^ k := by positivity
  by_cases hc : 2 ≤ 3 * AMGame.value true ((.arthur, p) :: τ)
      (fun u => ((V (s ++ (List.ofFn y₀ ++ u))).toNat : ℚ))
  · have hF : _ ≤ (∑ R, H R y₀) / 2 ^ (2 * k * p) :=
      AMGame.value_majority_ge ((.arthur, p) :: τ) k _ hc
    linarith [div_le_div_of_nonneg_right
      (sum_le_sum (s := univ) fun R _ => le_sup' (s := univ) (f := H R) (mem_univ y₀)) hP.le]
  · linarith [not_le.mp hc]

/-- Relativized `swapVerifierLocal` runs in oracle polynomial time. -/
private theorem computableInPolyTimeWithOracle_swapVerifier {O : Set (List Bool)}
    {enc : α ↪ List Bool} (σ τ : List (AMMove × Polynomial ℕ)) (q p k : Polynomial ℕ)
    {V : α × List Bool → Bool}
    (hV : ComputableInPolyTimeWithOracle O V (encPair enc encBits) encBool) :
    ComputableInPolyTimeWithOracle O
      (fun x : α × List Bool =>
        swapVerifierLocal
          (AMGame.transcriptLength (AMGame.evalShape σ (enc x.1).length))
          (2 * k.eval (enc x.1).length * p.eval (enc x.1).length)
          (q.eval (enc x.1).length)
          (AMGame.evalShape ((.arthur, p) :: τ) (enc x.1).length)
          (k.eval (enc x.1).length) (fun u => V (x.1, u)) x.2)
      (encPair enc encBits) encBool := by
  have hm : ComputableInPolyTime (fun x : α × List Bool => 2 * k.eval (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hk : ComputableInPolyTime (fun x : α × List Bool => k.eval (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hlen : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ => (enc y.1.1).length)
      (encPair (encPair enc encBits) encUnary) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp
      ((ComputableInPolyTime.fst _ _).comp (.fst _ _))
  have hcopy : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ =>
        (y.1.1,
          y.1.2.take (AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length)) ++
            ((y.1.2.drop (AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length) +
              2 * k.eval (enc y.1.1).length * p.eval (enc y.1.1).length)).take
              (q.eval (enc y.1.1).length) ++
            AMGame.copyTranscript (2 * k.eval (enc y.1.1).length) y.2
              (AMGame.evalShape ((.arthur, p) :: τ) (enc y.1.1).length)
              ((y.1.2.drop (AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length))).take
                  (2 * k.eval (enc y.1.1).length * p.eval (enc y.1.1).length) ++
                y.1.2.drop (AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length) +
                  2 * k.eval (enc y.1.1).length * p.eval (enc y.1.1).length +
                  q.eval (enc y.1.1).length)))))
      (encPair (encPair enc encBits) encUnary) (encPair enc encBits) := by
    have hL : ComputableInPolyTime
        (fun y : (α × List Bool) × ℕ =>
          AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length))
        (encPair (encPair enc encBits) encUnary) encUnary := by
      simpa only [Function.comp_def, AMGame.transcriptLength_evalShape] using
        (ComputableInPolyTime.unary_eval (AMGame.transcriptLengthPoly σ)).comp hlen
    have hct := AMGame.computableInPolyTime_copyTranscript ((.arthur, p) :: τ) hlen
      (m := fun y => 2 * k.eval (enc y.1.1).length) (i := fun y => y.2)
      (w := fun y =>
        (y.1.2.drop (AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length))).take
          (2 * k.eval (enc y.1.1).length * p.eval (enc y.1.1).length) ++
        y.1.2.drop (AMGame.transcriptLength (AMGame.evalShape σ (enc y.1.1).length) +
          2 * k.eval (enc y.1.1).length * p.eval (enc y.1.1).length +
          q.eval (enc y.1.1).length))
      (by fun_prop) (by fun_prop) (by fun_prop)
    have h1 : ComputableInPolyTime (fun y : (α × List Bool) × ℕ => y.1.1)
        (encPair (encPair enc encBits) encUnary) enc := by fun_prop
    exact h1.prod (by fun_prop)
  have hcnt := OraclePoly.countPWithInput hm (hV.preprocess hcopy)
  have hfinal := ((hk.computableInPolyTimeWithOracle O).prod hcnt).map
    (g := fun p : ℕ × ℕ => decide (p.1 < p.2)) (by fun_prop)
  refine ⟨hfinal.choose, hfinal.choose_spec.1, fun x => ?_⟩
  rw [hfinal.choose_spec.2 x]
  rfl

/-- Relativized padding: inserting a zero-length move preserves `AMGameClassWithOracle`. -/
theorem AMGameClassWithOracle_insert {O : Set (List Bool)} {enc : α ↪ List Bool}
    (σ τ : List AMMove) (x : AMMove) :
    AMGameClassWithOracle O enc (σ ++ τ) ⊆ AMGameClassWithOracle O enc (σ ++ x :: τ) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  have hsplit : ∃ G₁ G₂ : List (AMMove × Polynomial ℕ),
      G = G₁ ++ G₂ ∧ G₁.map Prod.fst = σ ∧ G₂.map Prod.fst = τ := by
    refine ⟨G.take σ.length, G.drop σ.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
    · rw [List.map_take, hG, List.take_left]
    · rw [List.map_drop, hG, List.drop_left]
  obtain ⟨G₁, G₂, rfl, hG₁, hG₂⟩ := hsplit
  refine ⟨G₁ ++ (x, 0) :: G₂, fun z => V (z.1,
    z.2.take (AMGame.transcriptLength (AMGame.evalShape G₁ (enc z.1).length)) ++
      z.2.drop (AMGame.transcriptLength (AMGame.evalShape G₁ (enc z.1).length))), ?_, ?_, ?_⟩
  · simp [hG₁, hG₂]
  · refine hV.preprocess ?_
    have hL : ComputableInPolyTime
        (fun z : α × List Bool => AMGame.transcriptLength (AMGame.evalShape G₁ (enc z.1).length))
        (encPair enc encBits) encUnary := by
      simpa only [Function.comp_def, AMGame.transcriptLength_evalShape] using
        (ComputableInPolyTime.unary_eval (AMGame.transcriptLengthPoly G₁)).comp
          ((ComputableInPolyTime.encoding_length enc).comp (.fst _ _))
    fun_prop
  · rw [isAMGameVerifier_iff_value] at hA ⊢
    intro a
    simp only [AMGame.evalShape_append, AMGame.evalShape_cons, Polynomial.eval_zero]
    have hcongr : ∀ b : Bool,
        AMGame.value b
          (AMGame.evalShape G₁ (enc a).length ++ (x, 0) :: AMGame.evalShape G₂ (enc a).length)
          (fun t => ((V (a, t.take (AMGame.transcriptLength (AMGame.evalShape G₁ (enc a).length)) ++
            t.drop (AMGame.transcriptLength (AMGame.evalShape G₁ (enc a).length)))).toNat : ℚ)) =
        AMGame.value b
          (AMGame.evalShape G₁ (enc a).length ++ AMGame.evalShape G₂ (enc a).length)
          (fun t => ((V (a, t)).toNat : ℚ)) := by
      intro b
      rw [AMGame.value_insert_zero]
      exact AMGame.value_congr_of_length b _ fun t _ => by rw [List.take_append_drop]
    rw [hcongr true]
    simpa only [AMGame.evalShape_append] using hA a

/-- Relativized merging: collapsing two adjacent moves of the same player. -/
theorem AMGameClassWithOracle_merge {O : Set (List Bool)} {enc : α ↪ List Bool}
    (σ τ : List AMMove) (x : AMMove) :
    AMGameClassWithOracle O enc (σ ++ x :: x :: τ) ⊆ AMGameClassWithOracle O enc (σ ++ x :: τ) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  obtain ⟨G₁, G', rfl, hG₁, h'⟩ := List.map_eq_append_iff.1 hG
  obtain ⟨⟨x₁, p₁⟩, G'', rfl, hx₁, h''⟩ := List.map_eq_cons_iff.1 h'
  obtain ⟨⟨x₂, p₂⟩, G₂, rfl, hx₂, hG₂⟩ := List.map_eq_cons_iff.1 h''
  dsimp only at hx₁ hx₂
  subst hx₁ hx₂
  refine ⟨G₁ ++ (x₂, p₁ + p₂) :: G₂, V, by simp [hG₁, hG₂], hV, ?_⟩
  rw [isAMGameVerifier_iff_value] at hA ⊢
  intro a
  simp only [AMGame.evalShape_append, AMGame.evalShape_cons, Polynomial.eval_add]
  cases x₂
  · rw [← AMGame.value_merge_arthur]
    simpa only [AMGame.evalShape_append, AMGame.evalShape_cons] using hA a
  · rw [← AMGame.value_merge_merlin]
    simpa only [AMGame.evalShape_append, AMGame.evalShape_cons] using hA a

/-- **Relativized Babai–Moran swap**: `σ M A τ ⊆ σ A M τ` relative to any oracle `O`. -/
theorem AMGameClassWithOracle_swap {O : Set (List Bool)} {enc : α ↪ List Bool}
    (σ τ : List AMMove) :
    AMGameClassWithOracle O enc (σ ++ .merlin :: .arthur :: τ) ⊆
      AMGameClassWithOracle O enc (σ ++ .arthur :: .merlin :: τ) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  obtain ⟨G₁, G', rfl, hG₁, h'⟩ := List.map_eq_append_iff.1 hG
  obtain ⟨⟨x₁, q⟩, G'', rfl, hx₁, h''⟩ := List.map_eq_cons_iff.1 h'
  obtain ⟨⟨x₂, p⟩, G₂, rfl, hx₂, hG₂⟩ := List.map_eq_cons_iff.1 h''
  dsimp only at hx₁ hx₂
  subst hx₁ hx₂
  -- Step 1: Amplify by majority of 48 copies
  let V₁ : α × List Bool → Bool := fun x =>
    AMGame.majority (AMGame.evalShape (G₁ ++ (.merlin, q) :: (.arthur, p) :: G₂) (enc x.1).length)
      24 (fun t => V (x.1, t)) x.2
  have hV₁ : ComputableInPolyTimeWithOracle O V₁ (encPair enc encBits) encBool := by
    simpa only [V₁, Polynomial.eval_ofNat] using
      computableInPolyTimeWithOracle_majority (G₁ ++ (.merlin, q) :: (.arthur, p) :: G₂)
        (24 : Polynomial ℕ) hV
  let G₁' := G₁.map fun x => (x.1, 48 * x.2)
  let G₂' := G₂.map fun x => (x.1, 48 * x.2)
  let Q : Polynomial ℕ := 48 * q
  let P : Polynomial ℕ := 48 * p
  let k : Polynomial ℕ := 6 * (Q + 4)
  -- Step 2: Apply swapVerifier
  let V₂ : α × List Bool → Bool := fun x =>
    swapVerifierLocal
      (AMGame.transcriptLength (AMGame.evalShape G₁' (enc x.1).length))
      (2 * k.eval (enc x.1).length * P.eval (enc x.1).length)
      (Q.eval (enc x.1).length)
      (AMGame.evalShape ((.arthur, P) :: G₂') (enc x.1).length)
      (k.eval (enc x.1).length) (fun u => V₁ (x.1, u)) x.2
  have hV₂ : ComputableInPolyTimeWithOracle O V₂ (encPair enc encBits) encBool :=
    computableInPolyTimeWithOracle_swapVerifier G₁' G₂' Q P k hV₁
  refine ⟨G₁' ++ (.arthur, 2 * k * P) :: (.merlin, Q) :: (G₂'.map fun x => (x.1, 2 * k * x.2)),
    V₂, ?_, hV₂, ?_⟩
  · simp [G₁', G₂', hG₁, hG₂, List.map_map, Function.comp_def]
  · rw [isAMGameVerifier_iff_value] at hA ⊢
    intro a
    set n := (enc a).length
    have hshape : AMGame.repeatShape 48
        (AMGame.evalShape (G₁ ++ (.merlin, q) :: (.arthur, p) :: G₂) n) =
        AMGame.evalShape G₁' n ++ (.merlin, Q.eval n) :: (.arthur, P.eval n) ::
          AMGame.evalShape G₂' n := by
      simp [G₁', G₂', Q, P, AMGame.repeatShape, AMGame.evalShape, List.map_map, Function.comp_def]
    have hshape2 : AMGame.evalShape
        (G₁' ++ (.arthur, 2 * k * P) :: (.merlin, Q) :: (G₂'.map fun x => (x.1, 2 * k * x.2))) n =
        AMGame.evalShape G₁' n ++ (.arthur, 2 * k.eval n * P.eval n) :: (.merlin, Q.eval n) ::
          AMGame.repeatShape (2 * k.eval n) (AMGame.evalShape G₂' n) := by
      simp [AMGame.evalShape, AMGame.repeatShape, List.map_map, Function.comp_def, mul_assoc]
    have h89 : ((8 / 9 : ℚ) ^ 6) ≤ 1 / 2 := by norm_num
    have hkdef : k.eval n = 6 * (Q.eval n + 4) := by simp [k]
    have hk4 : 2 ^ Q.eval n * ((8 / 9 : ℚ) ^ k.eval n / 2) ≤ 1 / 32 := by
      have hpow : (8 / 9 : ℚ) ^ k.eval n ≤ (1 / 2 : ℚ) ^ (Q.eval n + 4) := by
        rw [hkdef, pow_mul]; exact pow_le_pow_left₀ (by positivity) h89 _
      calc (2 : ℚ) ^ Q.eval n * ((8 / 9 : ℚ) ^ k.eval n / 2)
          ≤ (2 : ℚ) ^ Q.eval n * ((1 / 2 : ℚ) ^ (Q.eval n + 4) / 2) := by gcongr
        _ = 1 / 32 := by
            rw [one_div_pow, pow_add]
            have hne : (2 : ℚ) ^ Q.eval n ≠ 0 := by positivity
            field_simp; norm_num
    have h89k : (8 / 9 : ℚ) ^ k.eval n ≤ 1 / 16 := by
      rw [hkdef, pow_mul]
      have hle4 : 4 ≤ Q.eval n + 4 := by omega
      exact (pow_le_pow_left₀ (by positivity) h89 _).trans
        ((pow_le_pow_of_le_one (by positivity) (by norm_num) hle4).trans (by norm_num))
    have hamp_ge (ha : a ∈ A) :
        15 / 16 ≤ AMGame.value true
          (AMGame.evalShape G₁' n ++ (.merlin, Q.eval n) :: (.arthur, P.eval n) ::
            AMGame.evalShape G₂' n) (fun t => ((V₁ (a, t)).toNat : ℚ)) := by
      rw [← hshape]
      linarith [AMGame.value_majority_ge
        (AMGame.evalShape (G₁ ++ (.merlin, q) :: (.arthur, p) :: G₂) n) 24
        (fun t => V (a, t)) ((hA a).1 ha), show (8 / 9 : ℚ) ^ 24 ≤ 1 / 16 by norm_num]
    have hamp_le (ha : a ∉ A) :
        AMGame.value true
          (AMGame.evalShape G₁' n ++ (.merlin, Q.eval n) :: (.arthur, P.eval n) ::
            AMGame.evalShape G₂' n) (fun t => ((V₁ (a, t)).toNat : ℚ)) ≤ 1 / 32 := by
      rw [← hshape]
      linarith [AMGame.value_majority_le
        (AMGame.evalShape (G₁ ++ (.merlin, q) :: (.arthur, p) :: G₂) n) 24
        (fun t => V (a, t)) ((hA a).2 ha), show (8 / 9 : ℚ) ^ 24 / 2 ≤ 1 / 32 by norm_num]
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · rw [hshape2]; simp only [V₂, AMGame.evalShape_cons]
      linarith [value_swap_local_ge (AMGame.evalShape G₁' n) (AMGame.evalShape G₂' n)
        (Q.eval n) (P.eval n) (k.eval n) (fun t => V₁ (a, t)), hamp_ge ha]
    · rw [hshape2]; simp only [V₂, AMGame.evalShape_cons]
      linarith [value_swap_local_le (AMGame.evalShape G₁' n) (AMGame.evalShape G₂' n)
        (Q.eval n) (P.eval n) (k.eval n) (fun t => V₁ (a, t)), hamp_le ha]

/-- **Every constant-round relativized public-coin game lies in `AM^O`**. -/
theorem AMGameClassWithOracle_subset_AMWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool)
    (π : List AMMove) : AMGameClassWithOracle O enc π ⊆ AMWithOracle O enc := by
  have hsub : ∀ l : List AMMove,
      AMGameClassWithOracle O enc ([.arthur, .merlin] ++ l) ⊆
        AMGameClassWithOracle O enc [.arthur, .merlin] := by
    intro l
    induction l with
    | nil => simp
    | cons m l ih =>
      cases m
      · calc AMGameClassWithOracle O enc ([.arthur, .merlin] ++ .arthur :: l)
            = AMGameClassWithOracle O enc ([.arthur] ++ .merlin :: .arthur :: l) := rfl
          _ ⊆ AMGameClassWithOracle O enc ([.arthur] ++ .arthur :: .merlin :: l) :=
              AMGameClassWithOracle_swap [.arthur] l
          _ ⊆ AMGameClassWithOracle O enc ([.arthur, .merlin] ++ l) :=
              AMGameClassWithOracle_merge [] (.merlin :: l) .arthur
          _ ⊆ AMGameClassWithOracle O enc [.arthur, .merlin] := ih
      · calc AMGameClassWithOracle O enc ([.arthur, .merlin] ++ .merlin :: l)
            = AMGameClassWithOracle O enc ([.arthur] ++ .merlin :: .merlin :: l) := rfl
          _ ⊆ AMGameClassWithOracle O enc ([.arthur] ++ .merlin :: l) :=
              AMGameClassWithOracle_merge [.arthur] l .merlin
          _ ⊆ AMGameClassWithOracle O enc [.arthur, .merlin] := ih
  have hAM : AMGameClassWithOracle O enc [.arthur, .merlin] = AMWithOracle O enc := by
    ext A
    constructor
    · rintro ⟨G, V, hG, hV, hA⟩
      match G, hG with
      | [(.arthur, p), (.merlin, q)], _ =>
        exact ⟨p, q, V, hV, (isAMGameVerifier_arthur_merlin_iff).mp hA⟩
    · rintro ⟨p, q, V, hV, hA⟩
      exact ⟨[(.arthur, p), (.merlin, q)], V, rfl, hV, (isAMGameVerifier_arthur_merlin_iff).mpr hA⟩
  rw [← hAM]
  have h1 := AMGameClassWithOracle_insert (O := O) (enc := enc) [] π .merlin
  have h2 := AMGameClassWithOracle_insert (O := O) (enc := enc) [] (.merlin :: π) .arthur
  exact h1.trans (h2.trans (hsub π))

/-- **Relativized `AM[k]^O ⊆ AM^O`** for all constant `k : ℕ`. -/
theorem AMkWithOracle_subset_AMWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) :
    AMkWithOracle O enc k ⊆ AMWithOracle O enc :=
  AMGameClassWithOracle_subset_AMWithOracle O enc _

/-- **Relativized `AM[k]^O = AM^O`** for every constant `k ≥ 2`. -/
theorem AMkWithOracle_eq_AMWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) {k : ℕ}
    (hk : 2 ≤ k) : AMkWithOracle O enc k = AMWithOracle O enc := by
  refine Set.Subset.antisymm (AMkWithOracle_subset_AMWithOracle O enc k) ?_
  have hAM : AMWithOracle O enc ⊆ AMGameClassWithOracle O enc [.arthur, .merlin] := by
    rintro A ⟨p, q, V, hV, hA⟩
    exact ⟨[(.arthur, p), (.merlin, q)], V, rfl, hV, (isAMGameVerifier_arthur_merlin_iff).mpr hA⟩
  have hpad : ∀ (m : ℕ) (x : AMMove),
      AMGameClassWithOracle O enc (alternatingMoves x m) ⊆
        AMGameClassWithOracle O enc (alternatingMoves x (m + 1)) := by
    intro m x
    have heq : alternatingMoves x (m + 1) =
        alternatingMoves x m ++ [if m % 2 = 0 then x else x.other] := by
      induction m generalizing x with
      | zero => rfl
      | succ m ih =>
        change x :: alternatingMoves x.other (m + 1) =
          x :: alternatingMoves x.other m ++ [if (m + 1) % 2 = 0 then x else x.other]
        rw [List.cons_append, ih x.other]
        congr 2
        by_cases hm : m % 2 = 0
        · have : (m + 1) % 2 = 1 := by omega
          cases x <;> simp [AMMove.other, hm, this]
        · have : (m + 1) % 2 = 0 := by omega
          cases x <;> simp [AMMove.other, hm, this]
    have h := AMGameClassWithOracle_insert (O := O) (enc := enc) (alternatingMoves x m) []
      (if m % 2 = 0 then x else x.other)
    simpa only [List.append_nil, ← heq] using h
  have hmono : ∀ m, 2 ≤ m →
      AMGameClassWithOracle O enc [.arthur, .merlin] ⊆ AMkWithOracle O enc m := by
    intro m hm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction r with
    | zero => exact Set.Subset.refl _
    | succ r ih => exact (ih (by omega)).trans (hpad (2 + r) .arthur)
  exact hAM.trans (hmono k hk)

/-- **Relativized `AM[k]^O ⊆ PH^O`** for all constant `k : ℕ`. -/
theorem AMkWithOracle_subset_PHWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) :
    AMkWithOracle O enc k ⊆ PHWithOracle O enc :=
  (AMkWithOracle_subset_AMWithOracle O enc k).trans (AMWithOracle_subset_PHWithOracle O enc)

/-- **Public coins are private coins, relativized**: `AMGame^O[π] ⊆ IPGame^O[π.map toIP]`. -/
theorem AMGameClassWithOracle_subset_IPGameClassWithOracle (O : Set (List Bool))
    (enc : α ↪ List Bool) (π : List AMMove) :
    AMGameClassWithOracle O enc π ⊆ IPGameClassWithOracle O enc (π.map AMMove.toIP) := by
  rintro A ⟨G, V, hG, hV, hA⟩
  refine ⟨G.map fun x => (x.1.toIP, x.2), AMGame.transcriptLengthPoly G,
    fun x => x.2.1.drop x.2.2.2.length, fun x => V (x.1, x.2.2), by simp [← hG], ?_, ?_,
    fun a => ?_⟩
  · exact (show ComputableInPolyTime (fun x : α × List Bool × ℕ × List Bool =>
        x.2.1.drop x.2.2.2.length) (IPGame.encMsgInput enc) encBits by fun_prop)
      |>.computableInPolyTimeWithOracle O
  · exact hV.preprocess (by fun_prop)
  · set n := (enc a).length
    have hK := (AMGame.transcriptLength_evalShape G n).symm
    rw [IPGame.countAt, IPGame.evalShape_map_toIP, IPGame.bestCount_reveal _ (fun t => V (a, t)) hK,
      hK, IPGame.transcriptLength_eq_arthurBits_add_merlinBits, pow_add]
    obtain ⟨h1, h2⟩ := hA a
    set M := 2 ^ IPGame.merlinBits (AMGame.evalShape G n)
    exact ⟨fun ha => by linarith [Nat.mul_le_mul_right M (h1 ha)],
      fun ha => by linarith [Nat.mul_le_mul_right M (h2 ha)]⟩

/-- **Relativized `AM[k]^O ⊆ IP[k]^O`**. -/
theorem AMkWithOracle_subset_IPkWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) :
    AMkWithOracle O enc k ⊆ IPkWithOracle O enc k :=
  AMGameClassWithOracle_subset_IPGameClassWithOracle O enc _

/-- Relativized `IPGame.agrees` runs in oracle polynomial time for a fixed game shape `G`. -/
private theorem computableInPolyTimeWithOracle_agrees {O : Set (List Bool)} {γ : Type}
    {encIn : γ ↪ List Bool} (G : List (IPMove × Polynomial ℕ))
    {len : γ → ℕ} {msg : γ → ℕ → List Bool → List Bool}
    (hlen : ComputableInPolyTime len encIn encUnary)
    (hmsg : ComputableInPolyTimeWithOracle O (fun y : γ × ℕ × List Bool => msg y.1 y.2.1 y.2.2)
      (encPair encIn (encPair encUnary encBits)) encBits) :
    ∀ (j : ℕ) {p t : γ → List Bool},
      ComputableInPolyTime p encIn encBits →
      ComputableInPolyTime t encIn encBits →
      ComputableInPolyTimeWithOracle O
        (fun x : γ => IPGame.agrees (msg x) (IPGame.evalShape G (len x)) j (p x) (t x))
        encIn encBool := by
  induction G with
  | nil =>
    intro j p t _ _
    exact (ComputableInPolyTime.const true).computableInPolyTimeWithOracle O
  | cons mv G' ih =>
    obtain ⟨v, q⟩ := mv
    intro j p t hp ht
    cases v
    · have hq : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary := by fun_prop
      have htake : ComputableInPolyTime (fun x => (t x).take (q.eval (len x))) encIn encBits := by
        fun_prop
      have hdrop : ComputableInPolyTime (fun x => (t x).drop (q.eval (len x))) encIn encBits := by
        fun_prop
      have hmsg_x : ComputableInPolyTimeWithOracle O
          (fun x => msg x j (p x)) encIn encBits :=
        hmsg.preprocess (ComputableInPolyTime.id'.prod
          ((ComputableInPolyTime.const j).prod hp))
      have heqBit : ComputableInPolyTimeWithOracle O
          (fun x => decide ((t x).take (q.eval (len x)) =
            List.ofFn (BitString.ofList (q.eval (len x)) (msg x j (p x)))))
          encIn encBool := by
        have h1 : ComputableInPolyTimeWithOracle O
            (fun x => (q.eval (len x), ((t x).take (q.eval (len x)), msg x j (p x)))) encIn
            (encPair encUnary (encPair encBits encBits)) :=
          ((hq.computableInPolyTimeWithOracle O).prod
            ((htake.computableInPolyTimeWithOracle O).prod hmsg_x))
        refine h1.map (g := fun z : ℕ × List Bool × List Bool =>
            decide (z.2.1 = List.ofFn (BitString.ofList z.1 z.2.2))) ?_
        have hrow : ComputableInPolyTime
            (fun z : ℕ × List Bool × List Bool => List.ofFn (BitString.ofList z.1 z.2.2))
            (encPair encUnary (encPair encBits encBits)) encBits := by
          have h := ComputableInPolyTime.bitsRowWithInput
            (input := encPair encUnary (encPair encBits encBits))
            (width := fun z => z.1) (row := fun _ => 0) (word := fun z => z.2.2)
            (by fun_prop) (by fun_prop) (by fun_prop)
          refine h.of_enc_eq fun z => congrArg encBits ?_
          simp [BitString.listRow_zero]
        exact ComputableInPolyTime.decide_eq' (by fun_prop) hrow
      have hrest := ih (j + 1) (p := fun x => p x ++ (t x).take (q.eval (len x)))
        (t := fun x => (t x).drop (q.eval (len x))) (by fun_prop) hdrop
      have hand := (heqBit.prod hrest).map (g := fun b => b.1 && b.2) (by fun_prop)
      refine ⟨hand.choose, hand.choose_spec.1, fun x => ?_⟩
      rw [hand.choose_spec.2 x]
      simp [IPGame.evalShape, IPGame.agrees]
    · have hq : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary := by fun_prop
      have hrest := ih (j + 1) (p := fun x => p x ++ (t x).take (q.eval (len x)))
        (t := fun x => (t x).drop (q.eval (len x))) (by fun_prop) (by fun_prop)
      refine ⟨hrest.choose, hrest.choose_spec.1, fun x => ?_⟩
      rw [hrest.choose_spec.2 x]
      simp [IPGame.evalShape, IPGame.agrees]

/-- Relativized `Emulation.check` runs in oracle polynomial time for a fixed game shape `G`. -/
private theorem computableInPolyTimeWithOracle_check {O : Set (List Bool)} {γ : Type}
    {encIn : γ ↪ List Bool} (G : List (IPMove × Polynomial ℕ))
    {B Z K len : γ → ℕ} {V : γ → List Bool → Bool}
    (hB : ComputableInPolyTime B encIn encUnary)
    (hZ : ComputableInPolyTime Z encIn encUnary)
    (hK : ComputableInPolyTime K encIn encUnary)
    (hlen : ComputableInPolyTime len encIn encUnary)
    (hV : ∀ {q : γ → List Bool}, ComputableInPolyTime q encIn encBits →
      ComputableInPolyTimeWithOracle O (fun x => V x (q x)) encIn encBool) :
    ∀ {κ : γ → ℕ} {p w : γ → List Bool},
      ComputableInPolyTime κ encIn encUnary →
      ComputableInPolyTime p encIn encBits →
      ComputableInPolyTime w encIn encBits →
      ComputableInPolyTimeWithOracle O
        (fun x => Emulation.check (B x) (Z x) (K x) (V x)
          (IPGame.evalShape G (len x)) (κ x) (p x) (w x))
        encIn encBool := by
  induction G with
  | nil =>
    intro κ p w hκ hp _
    have h0 : ComputableInPolyTimeWithOracle O (fun x => decide (κ x = 0)) encIn encBool :=
      (ComputableInPolyTime.decide_eq' hκ (ComputableInPolyTime.const 0))
        |>.computableInPolyTimeWithOracle O
    have hand := (h0.prod (hV hp)).map (g := fun b => b.1 && b.2) (by fun_prop)
    refine ⟨hand.choose, hand.choose_spec.1, fun x => ?_⟩
    rw [hand.choose_spec.2 x]
    simp [IPGame.evalShape, Emulation.check]
  | cons mv G' ih =>
    obtain ⟨v, q⟩ := mv
    intro κ p w hκ hp hw
    cases v
    · have hn : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary :=
        (ComputableInPolyTime.unary_eval q).comp hlen
      have hnZ := ComputableInPolyTime.unary_add' hn hZ
      have hP := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hB hnZ) hB
      have hr := ComputableInPolyTime.bitsTakeWithInput hw hP
      have hy := ComputableInPolyTime.bitsDropWithInput hw hP
      have hb := ComputableInPolyTime.bitsCountWithInput
        (ComputableInPolyTime.bitsTakeWithInput hy hB) (ComputableInPolyTime.const true)
      have hyB := ComputableInPolyTime.bitsDropWithInput hy hB
      have hx := ComputableInPolyTime.bitsTakeWithInput hyB hnZ
      have hhash := Cslib.BitString.LinearHash.computableInPolyTime_hashZero hB hnZ hr hx
      have hpad := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.bitsAnyWithInput
        (test := fun _ b => b)
        (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.bitsDropWithInput hx hn)
          (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' hZ hκ)
            (ComputableInPolyTime.unary_add' hb hK)))
        (ComputableInPolyTime.snd _ _))
      have hpre := (ComputableInPolyTime.bool_and' hhash hpad).computableInPolyTimeWithOracle O
      have hrec := ih hb
        (ComputableInPolyTime.bitsAppend hp (ComputableInPolyTime.bitsTakeWithInput hx hn))
        (ComputableInPolyTime.bitsDropWithInput hyB hnZ)
      have hand := (hpre.prod hrec).map (g := fun b => b.1 && b.2) (by fun_prop)
      refine ⟨hand.choose, hand.choose_spec.1, fun x => ?_⟩
      rw [hand.choose_spec.2 x]
      rfl
    · have hn : ComputableInPolyTime (fun x => q.eval (len x)) encIn encUnary :=
        (ComputableInPolyTime.unary_eval q).comp hlen
      have hrec := ih hκ
        (ComputableInPolyTime.bitsAppend hp (ComputableInPolyTime.bitsTakeWithInput hw hn))
        (ComputableInPolyTime.bitsDropWithInput hw hn)
      refine ⟨hrec.choose, hrec.choose_spec.1, fun x => ?_⟩
      rw [hrec.choose_spec.2 x]
      rfl

/-- Copy-by-copy coin-revealing payoff for `t` parallel repetitions, avoiding `flatMap` over
oracle-computed lists so that it runs in oracle polynomial time via `OraclePoly.allWithInput`. -/
private def repeatRevealPayoff (t : ℕ) (g : List (IPMove × ℕ)) (ρ : ℕ)
    (msg : List Bool → ℕ → List Bool → List Bool) (dec : List Bool → List Bool → Bool)
    (L : ℕ) (w : List Bool) : Bool :=
  (List.range t).all fun i =>
    let ci := BitString.listRow ρ i (w.drop L)
    let ti := AMGame.copyTranscript t i (IPGame.toAM g) (w.take L)
    IPGame.agrees (msg ci) g 0 [] ti && dec ci ti

private theorem repeatRevealPayoff_eq_revealPayoff (t : ℕ) (g : List (IPMove × ℕ)) (ρ : ℕ)
    (msg : List Bool → ℕ → List Bool → List Bool) (dec : List Bool → List Bool → Bool)
    {L : ℕ} (hL : IPGame.transcriptLength (IPGame.repeatShape t g) = L) (w : List Bool)
    (hw : w.length = L + t * ρ) :
    repeatRevealPayoff t g ρ msg dec L w =
      Emulation.revealPayoff
        (fun c => IPGame.repeatMsg t g fun i => msg (BitString.listRow ρ i c))
        (fun c => IPGame.repeatDec t g fun i => dec (BitString.listRow ρ i c))
        (IPGame.repeatShape t g) L w := by
  have hwtake : (w.take L).length = IPGame.transcriptLength (IPGame.repeatShape t g) := by
    rw [List.length_take, hL, Nat.min_eq_left (by omega)]
  rw [Bool.eq_iff_iff]
  simp only [repeatRevealPayoff, Emulation.revealPayoff, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, IPGame.repeatDec_eq_true_iff]
  have hag := IPGame.agrees_repeatMsg t
    (fun i => msg (BitString.listRow ρ i (w.drop L))) g [] [] (w.take L) rfl hwtake
  simp only [List.nil_append, List.length_nil, IPGame.toAM_nil] at hag
  rw [hag]
  constructor
  · intro h
    exact ⟨fun i => (h i i.2).1, fun i => (h i i.2).2⟩
  · rintro ⟨h1, h2⟩ i hi
    exact ⟨h1 ⟨i, hi⟩, h2 ⟨i, hi⟩⟩

private theorem countFrom_repeatRevealPayoff (t : ℕ) (g : List (IPMove × ℕ)) (ρ : ℕ)
    (msg : List Bool → ℕ → List Bool → List Bool) (dec : List Bool → List Bool → Bool)
    {L : ℕ} (hL : IPGame.transcriptLength (IPGame.repeatShape t g) = L) :
    Emulation.countFrom (IPGame.repeatShape t g ++ [(.verifier, t * ρ)])
        (repeatRevealPayoff t g ρ msg dec L) [] =
      IPGame.bestCount (ρ :=
        ρ) (fun c => msg (List.ofFn c)) (fun c => dec (List.ofFn c)) g ^ t := by
  have hcongr : Emulation.countFrom (IPGame.repeatShape t g ++ [(.verifier, t * ρ)])
        (repeatRevealPayoff t g ρ msg dec L) [] =
      Emulation.countFrom (IPGame.repeatShape t g ++ [(.verifier, t * ρ)])
        (Emulation.revealPayoff
          (fun c => IPGame.repeatMsg t g fun i => msg (BitString.listRow ρ i c))
          (fun c => IPGame.repeatDec t g fun i => dec (BitString.listRow ρ i c))
          (IPGame.repeatShape t g) L) [] := by
    simp only [Emulation.countFrom, List.nil_append]
    refine IPGame.count_congr_of_length _ fun w hw => ?_
    have hw' : w.length = L + t * ρ := by
      rw [← hL]
      simpa [IPGame.transcriptLength] using hw
    rw [repeatRevealPayoff_eq_revealPayoff t g ρ msg dec hL w hw']
  rw [hcongr, Emulation.countFrom_revealPayoff _ _ _ hL (t * ρ),
    IPGame.bestCount_repeat t ρ msg dec g]

private theorem computableInPolyTimeWithOracle_repeatRevealPayoff {O : Set (List Bool)}
    {enc : α ↪ List Bool} (G : List (IPMove × Polynomial ℕ)) (R ρ : Polynomial ℕ)
    {msg : α × List Bool × ℕ × List Bool → List Bool} {dec : α × List Bool × List Bool → Bool}
    (hmsg : ComputableInPolyTimeWithOracle O msg (IPGame.encMsgInput enc) encBits)
    (hdec : ComputableInPolyTimeWithOracle O dec (IPGame.encDecInput enc) encBool) :
    ∀ {q : α × List Bool → List Bool},
      ComputableInPolyTime q (encPair enc encBits) encBits →
      ComputableInPolyTimeWithOracle O
        (fun x : α × List Bool =>
          repeatRevealPayoff (R.eval (enc x.1).length) (IPGame.evalShape G (enc x.1).length)
            (ρ.eval (enc x.1).length)
            (fun c j p => msg (x.1, c, j, p)) (fun c t => dec (x.1, c, t))
            (IPGame.transcriptLength
              (IPGame.evalShape (IPGame.repeatShapePoly R G) (enc x.1).length))
            (q x))
        (encPair enc encBits) encBool := by
  intro q hq
  let encXY := encPair (encPair enc encBits) encUnary
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  have hR : ComputableInPolyTime (fun x : α × List Bool => R.eval (enc x.1).length)
      (encPair enc encBits) encUnary := (ComputableInPolyTime.unary_eval R).comp hn
  have hL : ComputableInPolyTime
      (fun x : α × List Bool =>
        IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G) (enc x.1).length))
      (encPair enc encBits) encUnary := by
    have hpoly := (ComputableInPolyTime.unary_eval
      (AMGame.transcriptLengthPoly ((IPGame.repeatShapePoly R G).map fun x => (x.1.toAM,
        x.2)))).comp hn
    refine hpoly.of_enc_eq fun x => congrArg encUnary ?_
    simp only [Function.comp_apply, ← AMGame.transcriptLength_evalShape,
      ← IPGame.toAM_evalShape, IPGame.transcriptLength_toAM]
  have hci : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ =>
        BitString.listRow (ρ.eval (enc y.1.1).length) y.2 ((q y.1).drop
          (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
            (enc y.1.1).length))))
      encXY encBits :=
    ComputableInPolyTime.bitsRowWithInput
      ((ComputableInPolyTime.unary_eval ρ).comp (hn.comp (.fst _ _)))
      (ComputableInPolyTime.snd _ _)
      (ComputableInPolyTime.bitsDropWithInput (hq.comp (.fst _ _)) (hL.comp (.fst _ _)))
  have hti : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ =>
        AMGame.copyTranscript (R.eval (enc y.1.1).length) y.2
          (IPGame.toAM (IPGame.evalShape G (enc y.1.1).length))
          ((q y.1).take (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
            (enc y.1.1).length))))
      encXY encBits := by
    have h := AMGame.computableInPolyTime_copyTranscript (G.map fun x => (x.1.toAM, x.2))
      (hn.comp (ComputableInPolyTime.fst (encPair enc encBits) encUnary))
      (m := fun y : (α × List Bool) × ℕ => R.eval (enc y.1.1).length)
      (i := fun y : (α × List Bool) × ℕ => y.2)
      (w := fun y : (α × List Bool) × ℕ =>
        (q y.1).take (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
          (enc y.1.1).length)))
      (hR.comp (ComputableInPolyTime.fst (encPair enc encBits) encUnary))
      (ComputableInPolyTime.snd (encPair enc encBits) encUnary)
      (ComputableInPolyTime.bitsTakeWithInput
        (hq.comp (ComputableInPolyTime.fst (encPair enc encBits) encUnary))
        (hL.comp (ComputableInPolyTime.fst (encPair enc encBits) encUnary)))
    refine h.of_enc_eq fun y => congrArg encBits ?_
    rw [IPGame.toAM_evalShape]
    rfl
  have hmsg_y : ComputableInPolyTimeWithOracle O
      (fun z : ((α × List Bool) × ℕ) × ℕ × List Bool =>
        msg (z.1.1.1, BitString.listRow (ρ.eval (enc z.1.1.1).length) z.1.2
          ((q z.1.1).drop (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
            (enc z.1.1.1).length))), z.2.1, z.2.2))
      (encPair encXY (encPair encUnary encBits)) encBits :=
    hmsg.preprocess (by
      have h1 : ComputableInPolyTime (fun z : ((α × List Bool) × ℕ) × ℕ × List Bool => z.1.1.1)
          (encPair encXY (encPair encUnary encBits)) enc := by fun_prop
      exact h1.prod ((hci.comp (ComputableInPolyTime.fst encXY (encPair encUnary encBits))).prod
        (ComputableInPolyTime.snd encXY (encPair encUnary encBits))))
  have hag := computableInPolyTimeWithOracle_agrees (encIn := encXY)
    (msg := fun y j p => msg (y.1.1, BitString.listRow (ρ.eval (enc y.1.1).length) y.2
      ((q y.1).drop (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
        (enc y.1.1).length))), j, p)) G
    (hn.comp (ComputableInPolyTime.fst (encPair enc encBits) encUnary)) hmsg_y 0
    (ComputableInPolyTime.const []) hti
  have hdec_y : ComputableInPolyTimeWithOracle O
      (fun y : (α × List Bool) × ℕ =>
        dec (y.1.1, BitString.listRow (ρ.eval (enc y.1.1).length) y.2
          ((q y.1).drop (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
            (enc y.1.1).length))),
          AMGame.copyTranscript (R.eval (enc y.1.1).length) y.2
            (IPGame.toAM (IPGame.evalShape G (enc y.1.1).length))
            ((q y.1).take (IPGame.transcriptLength (IPGame.evalShape (IPGame.repeatShapePoly R G)
              (enc y.1.1).length)))))
      encXY encBool :=
    hdec.preprocess (by
      have h1 : ComputableInPolyTime (fun y : (α × List Bool) × ℕ => y.1.1) encXY enc := by
        fun_prop
      exact h1.prod (hci.prod hti))
  have htest := (hag.prod hdec_y).map (g := fun b => b.1 && b.2) (by fun_prop)
  exact OraclePoly.allWithInput hR htest

/-- **Relativized Goldwasser–Sipser**: every fixed-pattern relativized private-coin
interactive proof game is emulated by a relativized public-coin Arthur–Merlin game with
`Emulation.pattern (π ++ [.verifier])`.
-/
theorem IPGameClassWithOracle_subset_AMGameClassWithOracle (O : Set (List Bool))
    (enc : α ↪ List Bool) (π : List IPMove) :
    IPGameClassWithOracle O enc π ⊆
      AMGameClassWithOracle O enc (Emulation.pattern (π ++ [.verifier])) := by
  rintro A ⟨G₀, ρ₀, msg₀, dec₀, hG₀, hmsg₀, hdec₀, hA⟩
  let c := (G₀.map Prod.fst).count .verifier + 1
  let W : Polynomial ℕ := AMGame.transcriptLengthPoly (G₀.map fun x => (x.1.toAM, x.2)) + ρ₀ + 1
  have hev : ∀ᶠ r : ℕ in Filter.atTop, 6 * (288 * c ^ 2) ^ c * r ^ (4 * c) * 2 ^ r ≤ 3 ^ r := by
    filter_upwards [Nat.eventually_mul_pow_le_pow_div (6 * (288 * c ^ 2) ^ c) (4 * c) 2
      one_lt_two two_pos] with r hr
    have h89 : (2 ^ (r + r / 2)) ^ 2 ≤ (3 ^ r) ^ 2 := calc
      (2 ^ (r + r / 2)) ^ 2 ≤ 2 ^ (3 * r) := by
        rw [← pow_mul]; exact Nat.pow_le_pow_right two_pos (by omega)
      _ = 8 ^ r := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ r := Nat.pow_le_pow_left (by norm_num) r
      _ = (3 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc 6 * (288 * c ^ 2) ^ c * r ^ (4 * c) * 2 ^ r ≤ 2 ^ (r / 2) * 2 ^ r :=
          Nat.mul_le_mul_right _ hr
      _ = 2 ^ (r + r / 2) := by rw [← pow_add, Nat.add_comm]
      _ ≤ 3 ^ r := (Nat.pow_le_pow_iff_left two_ne_zero).1 h89
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atTop.1 hev
  let R : Polynomial ℕ := Polynomial.C (max A₀ 1) * W
  let B : Polynomial ℕ := R * W
  let Z : Polynomial ℕ := 2 * (B + 6 * Polynomial.C c * (B + 1))
  have hGfst : (IPGame.repeatShapePoly R G₀).map Prod.fst = G₀.map Prod.fst := by
    simp [IPGame.repeatShapePoly]
  let V_am : α × List Bool → Bool := fun x =>
    Emulation.check (B.eval (enc x.1).length) (Z.eval (enc x.1).length)
      (Emulation.threshold c (B.eval (enc x.1).length))
      (repeatRevealPayoff (R.eval (enc x.1).length) (IPGame.evalShape G₀ (enc x.1).length)
        (ρ₀.eval (enc x.1).length) (fun c j p => msg₀ (x.1, c, j, p))
        (fun c t => dec₀ (x.1, c, t))
        (IPGame.transcriptLength
          (IPGame.evalShape (IPGame.repeatShapePoly R G₀) (enc x.1).length)))
      (IPGame.evalShape (IPGame.repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]) (enc x.1).length)
      ((R * ρ₀).eval (enc x.1).length - R.eval (enc x.1).length) [] x.2
  have hV_am : ComputableInPolyTimeWithOracle O V_am (encPair enc encBits) encBool := by
    have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
    have hB : ComputableInPolyTime (fun x : α × List Bool => B.eval (enc x.1).length)
        (encPair enc encBits) encUnary := (ComputableInPolyTime.unary_eval B).comp hn
    exact computableInPolyTimeWithOracle_check (IPGame.repeatShapePoly R G₀ ++ [(.verifier,
      R * ρ₀)])
      hB ((ComputableInPolyTime.unary_eval Z).comp hn)
      (Emulation.computableInPolyTime_threshold c hB) hn
      (fun hq => computableInPolyTimeWithOracle_repeatRevealPayoff G₀ R ρ₀ hmsg₀ hdec₀ hq)
      (ComputableInPolyTime.unary_sub' ((ComputableInPolyTime.unary_eval (R * ρ₀)).comp hn)
        ((ComputableInPolyTime.unary_eval R).comp hn))
      (ComputableInPolyTime.const []) (ComputableInPolyTime.snd _ _)
  refine ⟨Emulation.shapePoly B Z (IPGame.repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]),
    V_am, by rw [Emulation.map_fst_shapePoly, List.map_append, hGfst, hG₀]; rfl, hV_am, ?_⟩
  rw [isAMGameVerifier_iff_value]
  intro a
  obtain ⟨h1, h2⟩ := hA a
  simp only [V_am, Emulation.evalShape_shapePoly]
  have hL : IPGame.transcriptLength
      (IPGame.repeatShape (R.eval (enc a).length) (IPGame.evalShape G₀ (enc a).length)) =
      IPGame.transcriptLength
        (IPGame.evalShape (IPGame.repeatShapePoly R G₀) (enc a).length) := by
    rw [IPGame.evalShape_repeatShapePoly]
  have hN : Emulation.countFrom
      (IPGame.evalShape (IPGame.repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]) (enc a).length)
      (repeatRevealPayoff (R.eval (enc a).length) (IPGame.evalShape G₀ (enc a).length)
        (ρ₀.eval (enc a).length) (fun c j p => msg₀ (a, c, j, p)) (fun c t => dec₀ (a, c, t))
        (IPGame.transcriptLength
          (IPGame.evalShape (IPGame.repeatShapePoly R G₀) (enc a).length))) [] =
      IPGame.countAt enc G₀ ρ₀ msg₀ dec₀ a ^ R.eval (enc a).length := by
    simp only [IPGame.evalShape_append, IPGame.evalShape_repeatShapePoly, IPGame.evalShape_cons,
      IPGame.evalShape_nil, Polynomial.eval_mul]
    exact countFrom_repeatRevealPayoff _ _ _ _ _ rfl
  generalize IPGame.countAt enc G₀ ρ₀ msg₀ dec₀ a = N₀ at hN h1 h2
  generalize (enc a).length = n at hN h1 h2 ⊢
  have hc' : IPGame.verifierMoves
      (IPGame.evalShape (IPGame.repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]) n) = c := by
    simp [IPGame.verifierMoves_evalShape, hGfst, c]
  have hRn : R.eval n = max A₀ 1 * W.eval n := by simp [R]
  have hBn : B.eval n = R.eval n * W.eval n := by simp [B]
  have hZn : Z.eval n = 2 * (B.eval n + 6 * c * (B.eval n + 1)) := by simp [Z]
  have hWn : W.eval n = IPGame.transcriptLength (IPGame.evalShape G₀ n) + ρ₀.eval n + 1 := by
    simp only [W, Polynomial.eval_add, Polynomial.eval_one, ← AMGame.transcriptLength_evalShape,
      ← IPGame.toAM_evalShape, IPGame.transcriptLength_toAM]
  have hκ : (R * ρ₀).eval n - R.eval n ≤ B.eval n := by
    rw [Polynomial.eval_mul, hBn]
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ (by omega))
  have hg : IPGame.verifierBits
      (IPGame.evalShape (IPGame.repeatShapePoly R G₀ ++ [(.verifier, R * ρ₀)]) n) ≤ B.eval n := by
    simp only [IPGame.evalShape_append, IPGame.verifierBits_append,
      IPGame.evalShape_repeatShapePoly, IPGame.verifierBits_repeatShape, IPGame.evalShape_cons,
      IPGame.evalShape_nil, IPGame.verifierBits_verifier, show IPGame.verifierBits [] = 0 from rfl,
      Polynomial.eval_mul, hBn, Nat.add_zero, ← Nat.mul_add]
    have := IPGame.verifierBits_le_transcriptLength (IPGame.evalShape G₀ n)
    exact Nat.mul_le_mul_left _ (by omega)
  have hgap : 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * 2 ^ R.eval n ≤ 3 ^ R.eval n := by
    have hWr : W.eval n ≤ R.eval n := hRn ▸ Nat.le_mul_of_pos_left _ (by omega)
    have hAr : A₀ ≤ R.eval n :=
      hRn ▸ (le_max_left A₀ 1).trans (Nat.le_mul_of_pos_right _ (by omega))
    have hr1 : 1 ≤ R.eval n := hRn ▸ Nat.mul_pos (by omega) (by omega)
    have hb : B.eval n + 1 ≤ 2 * R.eval n ^ 2 := by
      rw [hBn]; nlinarith [Nat.mul_le_mul_left (R.eval n) hWr, Nat.mul_le_mul hr1 hr1]
    have hM : 72 * c ^ 2 * (B.eval n + 1) ^ 2 ≤ 288 * c ^ 2 * R.eval n ^ 4 := by
      nlinarith [Nat.pow_le_pow_left hb 2]
    calc 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * 2 ^ R.eval n
        ≤ 6 * (288 * c ^ 2 * R.eval n ^ 4) ^ c * 2 ^ R.eval n := by gcongr
      _ = 6 * (288 * c ^ 2) ^ c * R.eval n ^ (4 * c) * 2 ^ R.eval n := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ 3 ^ R.eval n := hA₀ _ hAr
  have hRρ : (R * ρ₀).eval n = R.eval n * ρ₀.eval n := Polynomial.eval_mul
  rw [← hc']
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine Emulation.two_le_three_mul_value _ _ _ _ (by omega) (by rw [hc', hZn]) hg _ hκ ?_
    rw [hN]
    exact two_pow_sub_le <| calc
      2 ^ R.eval n * 2 ^ (R * ρ₀).eval n = (2 * 2 ^ ρ₀.eval n) ^ R.eval n := by
        rw [hRρ, mul_pow, ← pow_mul, mul_comm (ρ₀.eval n)]
      _ ≤ (3 * N₀) ^ R.eval n := Nat.pow_le_pow_left (h1 ha) _
      _ = 3 ^ R.eval n * N₀ ^ R.eval n := mul_pow _ _ _
  · refine Emulation.three_mul_value_le_one _ _ _ _ (by omega) _ hκ ?_
    rw [hN, hc']
    exact le_two_pow_sub <| calc
      6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * N₀ ^ R.eval n * 2 ^ R.eval n
        = 6 * (72 * c ^ 2 * (B.eval n + 1) ^ 2) ^ c * 2 ^ R.eval n * N₀ ^ R.eval n := by ring
      _ ≤ 3 ^ R.eval n * N₀ ^ R.eval n := Nat.mul_le_mul_right _ hgap
      _ = (3 * N₀) ^ R.eval n := (mul_pow _ _ _).symm
      _ ≤ (2 ^ ρ₀.eval n) ^ R.eval n := Nat.pow_le_pow_left (h2 ha) _
      _ = 2 ^ (R * ρ₀).eval n := by rw [hRρ, ← pow_mul, mul_comm]

/-- **Every fixed-pattern relativized private-coin game lies in `AM^O`**. -/
theorem IPGameClassWithOracle_subset_AMWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool)
    (π : List IPMove) : IPGameClassWithOracle O enc π ⊆ AMWithOracle O enc :=
  (IPGameClassWithOracle_subset_AMGameClassWithOracle O enc π).trans
    (AMGameClassWithOracle_subset_AMWithOracle O enc _)

/-- **Relativized `IP[k]^O ⊆ AM[k+2]^O`**. -/
theorem IPkWithOracle_subset_AMkWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) :
    IPkWithOracle O enc k ⊆ AMkWithOracle O enc (k + 2) := by
  rw [AMkWithOracle_eq_AMWithOracle O enc (by omega)]
  exact IPGameClassWithOracle_subset_AMWithOracle O enc _

/-- **Relativized `IP[k]^O = AM^O`** for every constant `k ≥ 2`. -/
theorem IPkWithOracle_eq_AMWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) {k : ℕ}
    (hk : 2 ≤ k) : IPkWithOracle O enc k = AMWithOracle O enc :=
  Set.Subset.antisymm (IPGameClassWithOracle_subset_AMWithOracle O enc _)
    ((AMkWithOracle_eq_AMWithOracle O enc hk).symm.subset.trans
      (AMkWithOracle_subset_IPkWithOracle O enc k))

/-- **Relativized `IP[k]^O ⊆ PH^O`** for every constant `k : ℕ`. -/
theorem IPkWithOracle_subset_PHWithOracle (O : Set (List Bool)) (enc : α ↪ List Bool) (k : ℕ) :
    IPkWithOracle O enc k ⊆ PHWithOracle O enc :=
  (IPGameClassWithOracle_subset_AMWithOracle O enc _).trans (AMWithOracle_subset_PHWithOracle O enc)

/-- Execute a private-coin interactive game against an arbitrary stateful prover (whose internal
state `State : Type*` may be arbitrary — classical, randomized conditioned on coins, or quantum
Hilbert-space state exchanging classical messages). -/
@[expose] def runStateful {State : Type*} (msg : ℕ → List Bool → List Bool)
    (step : State → ℕ → List Bool → List Bool × State) :
    List (IPMove × ℕ) → ℕ → List Bool → State → List Bool
  | [], _, _, _ => []
  | (.verifier, n) :: g, j, p, s =>
    let m := List.ofFn (BitString.ofList n (msg j p))
    m ++ runStateful msg step g (j + 1) (p ++ m) s
  | (.prover, n) :: g, j, p, s =>
    let res := step s j p
    let m := List.ofFn (BitString.ofList n res.1)
    m ++ runStateful msg step g (j + 1) (p ++ m) res.2

@[simp] theorem runStateful_nil {State : Type*} (msg : ℕ → List Bool → List Bool)
    (step : State → ℕ → List Bool → List Bool × State) (j : ℕ) (p : List Bool) (s : State) :
    runStateful msg step [] j p s = [] := rfl

@[simp] theorem runStateful_verifier {State : Type*} (msg : ℕ → List Bool → List Bool)
    (step : State → ℕ → List Bool → List Bool × State) (n : ℕ) (g : List (IPMove × ℕ)) (j : ℕ)
    (p : List Bool) (s : State) :
    runStateful msg step ((.verifier, n) :: g) j p s =
      List.ofFn (BitString.ofList n (msg j p)) ++
        runStateful msg step g (j + 1) (p ++ List.ofFn (BitString.ofList n (msg j p))) s := rfl

@[simp] theorem runStateful_prover {State : Type*} (msg : ℕ → List Bool → List Bool)
    (step : State → ℕ → List Bool → List Bool × State) (n : ℕ) (g : List (IPMove × ℕ)) (j : ℕ)
    (p : List Bool) (s : State) :
    runStateful msg step ((.prover, n) :: g) j p s =
      List.ofFn (BitString.ofList n (step s j p).1) ++
        runStateful msg step g (j + 1)
          (p ++ List.ofFn (BitString.ofList n (step s j p).1)) (step s j p).2 := rfl

/-- Any stateful prover (arbitrary `State : Type*`) is accepted on at most `IPGame.bestCount`
coin strings. -/
theorem card_filter_runStateful_le_bestCount {ρ : ℕ} {State : Type*}
    (msg : BitString ρ → ℕ → List Bool → List Bool) (dec : BitString ρ → List Bool → Bool)
    (g : List (IPMove × ℕ)) (step : State → ℕ → List Bool → List Bool × State) (s₀ : State) :
    #(univ.filter fun c : BitString ρ =>
      dec c (runStateful (msg c) step g 0 [] s₀) = true) ≤
      IPGame.bestCount msg dec g := by
  have hgen : ∀ (g : List (IPMove × ℕ)) (j : ℕ) (p : List Bool) (s : State)
      (S : Finset (BitString ρ)),
      #(S.filter fun c => dec c (p ++ runStateful (msg c) step g j p s) = true) ≤
        IPGame.count g fun t =>
          #(S.filter fun c => IPGame.agrees (msg c) g j p t = true ∧ dec c (p ++ t) = true) := by
    intro g
    induction g with
    | nil =>
      intro j p s S
      simp [runStateful, IPGame.count, IPGame.agrees]
    | cons mv g ih =>
      obtain ⟨v, n⟩ := mv
      intro j p s S
      cases v
      · -- Verifier move: partition `S` by the verifier's message `m : Fin n → Bool`
        rw [IPGame.count_verifier]
        have hpart : #(S.filter fun c =>
              dec c (p ++ runStateful (msg c) step ((.verifier, n) :: g) j p s) = true) =
            ∑ m : Fin n → Bool,
              #((S.filter fun c => BitString.ofList n (msg c j p) = m).filter fun c =>
                dec c (p ++ List.ofFn m ++
                  runStateful (msg c) step g (j + 1) (p ++ List.ofFn m) s) = true) := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext c
            simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
            constructor
            · intro ⟨hc, hdec⟩
              refine ⟨BitString.ofList n (msg c j p), ⟨hc, rfl⟩, ?_⟩
              simpa [runStateful, List.append_assoc] using hdec
            · rintro ⟨m, ⟨hc, rfl⟩, hdec⟩
              exact ⟨hc, by simpa [runStateful, List.append_assoc] using hdec⟩
          · intro m₁ _ m₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro c h1 h2
            simp only [Finset.mem_filter] at h1 h2
            exact hne (h1.1.2.symm.trans h2.1.2)
        rw [hpart]
        refine Finset.sum_le_sum fun m _ => ?_
        have hstep := ih (j + 1) (p ++ List.ofFn m) s
          (S.filter fun c => BitString.ofList n (msg c j p) = m)
        refine hstep.trans (IPGame.count_mono_of_length g fun t _ => ?_)
        refine Finset.card_le_card fun c hc => ?_
        simp only [Finset.mem_filter] at hc ⊢
        refine ⟨hc.1.1, ?_, by simpa [List.append_assoc] using hc.2.2⟩
        simp only [IPGame.agrees, List.take_left' List.length_ofFn,
          List.drop_left' List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by rw [hc.1.2], hc.2.1⟩
      · -- Prover move: `step s j p` is independent of `c`, so bounded by `univ.sup`
        rw [IPGame.count_prover]
        let res := step s j p
        let m : Fin n → Bool := BitString.ofList n res.1
        have hrun : ∀ c, p ++ runStateful (msg c) step ((.prover, n) :: g) j p s =
            p ++ List.ofFn m ++
              runStateful (msg c) step g (j + 1) (p ++ List.ofFn m) res.2 := fun c => by
          simp [runStateful, res, m, List.append_assoc]
        simp_rw [hrun]
        refine ((ih (j + 1) (p ++ List.ofFn m) res.2 S).trans
          (IPGame.count_mono_of_length g fun t _ =>
            Finset.card_le_card fun c hc => by
              simp only [Finset.mem_filter] at hc ⊢
              refine ⟨hc.1, ?_, by simpa [List.append_assoc] using hc.2.2⟩
              simpa [IPGame.agrees, List.take_left' List.length_ofFn,
                List.drop_left' List.length_ofFn] using hc.2.1)).trans
          (Finset.le_sup (f := fun y : Fin n → Bool => IPGame.count g fun t =>
            #(S.filter fun c => IPGame.agrees (msg c) ((.prover, n) :: g) j p (List.ofFn y ++ t) =
              true ∧ dec c (p ++ (List.ofFn y ++ t)) = true)) (Finset.mem_univ m))
  have h := hgen g 0 [] s₀ Finset.univ
  rw [IPGame.bestCount]
  refine (by simpa only [List.nil_append] using h :
    #(univ.filter fun c => dec c (runStateful (msg c) step g 0 [] s₀) = true) ≤
      IPGame.count g fun t =>
        #(univ.filter fun c => IPGame.agrees (msg c) g 0 [] t = true ∧ dec c t = true)).trans_eq ?_
  refine IPGame.count_congr_of_length g fun t _ => ?_
  simp only [IPGame.acceptedCoins, Bool.and_eq_true]

end Complexity

end CslibFrontier
