/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic

/-!
# Promise Search Problems and Oracle-Relativized Search-to-Decision Reductions

This module defines promise search problems (`CslibFrontier.Complexity.PromiseSearchProblem`) and
proves a general polynomial-time Turing reduction from a decision problem to a promise search
problem whenever candidate witnesses can be verified in polynomial time (possibly relative to an
oracle).

## Main definitions

* `CslibFrontier.Complexity.PromiseSearchProblem`: a search relation `valid : α → β → Prop` together
  with its realizable promise domain `promise := {a | ∃ b, valid a b}`.
* `CslibFrontier.Complexity.PromiseSearchProblem.Solves`: a total solver `f : α → β` that returns
  a valid witness on every promised instance (while still halting on unpromised inputs).

## Main results

* `CslibFrontier.Complexity.PromiseSearchProblem.decision_in_PWithOracle_of_polyTime_solver`:
  if a promise search problem has a polynomial-time solver and its relation is verifiable in
  polynomial time relative to an oracle `O`, then the promise domain lies in `PWithOracle O`.
* `CslibFrontier.Complexity.PromiseSearchProblem.decision_in_P_of_polyTime_solver`:
  unrelativized special case placing the promise domain in `P`.
* `CslibFrontier.Complexity.PromiseSearchProblem.oracle_reduction_of_polyTime_solver`:
  instance-dependent oracle variant: given instance-specific oracles `O : α → Set (List Bool)`
  and a polynomial-time oracle verifier `prog` deciding `valid a b` against `O a`, composing with
  any polynomial-time solver `f` produces a polynomial-time oracle decider for `a ∈ promise`
  against `O a`.
-/

public section

namespace CslibFrontier

namespace Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-- A promise search problem over input type `α` and witness type `β`: given `a : α` promised to
have at least one valid witness `b : β` satisfying `valid a b`, output such a witness. -/
@[ext]
structure PromiseSearchProblem (α β : Type*) where
  /-- Search relation: `valid a b` holds when `b` is an acceptable solution for instance `a`. -/
  valid : α → β → Prop

namespace PromiseSearchProblem

variable {α β : Type*}

/-- The promise domain (decision language) of a promise search problem: inputs having a valid
solution. -/
def promise (Q : PromiseSearchProblem α β) : Set α :=
  {a | ∃ b, Q.valid a b}

theorem mem_promise_iff (Q : PromiseSearchProblem α β) {a : α} :
    a ∈ Q.promise ↔ ∃ b, Q.valid a b := by
  rfl

/-- A total function `f : α → β` solves `Q` under the promise if `Q.valid a (f a)` holds for every
instance `a ∈ Q.promise`. -/
def Solves (Q : PromiseSearchProblem α β) (f : α → β) : Prop :=
  ∀ a ∈ Q.promise, Q.valid a (f a)

/-- Decision correctness of verify-after-search: if `f` solves `Q`, then `a ∈ Q.promise` holds
if and only if `Q.valid a (f a)`. -/
theorem mem_promise_iff_valid_solver {Q : PromiseSearchProblem α β} {f : α → β}
    (hf : Q.Solves f) (a : α) :
    a ∈ Q.promise ↔ Q.valid a (f a) :=
  ⟨hf a, fun h => ⟨f a, h⟩⟩

section Complexity

variable {α β : Type}

/-- Search-to-decision reduction relative to a fixed oracle `O`: if `f` is a polynomial-time
solver for `Q` and `Q.valid` is verifiable in polynomial time with oracle `O`, then `Q.promise`
is decidable in polynomial time with oracle `O`. -/
theorem decision_in_PWithOracle_of_polyTime_solver
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {O : Set (List Bool)} {Q : PromiseSearchProblem α β}
    {f : α → β} {verify : α × β → Bool}
    (hf_poly : ComputableInPolyTime f encA encB)
    (hf_solves : Q.Solves f)
    (hv_poly : ComputableInPolyTimeWithOracle O verify (encPair encA encB) encBool)
    (hv_spec : ∀ a b, verify (a, b) = true ↔ Q.valid a b) :
    Q.promise ∈ PWithOracle O encA := by
  rw [mem_PWithOracle]
  refine ⟨fun a => verify (a, f a), ?_, fun a => ?_⟩
  · exact hv_poly.preprocess (ComputableInPolyTime.id'.prod hf_poly)
  · rw [mem_promise_iff_valid_solver hf_solves a, ← hv_spec]

/-- Unrelativized search-to-decision reduction: if `f` is a polynomial-time solver for `Q` and
`Q.valid` is verifiable in polynomial time, then `Q.promise ∈ P encA`. -/
theorem decision_in_P_of_polyTime_solver
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {Q : PromiseSearchProblem α β}
    {f : α → β} {verify : α × β → Bool}
    (hf_poly : ComputableInPolyTime f encA encB)
    (hf_solves : Q.Solves f)
    (hv_poly : ComputableInPolyTime verify (encPair encA encB) encBool)
    (hv_spec : ∀ a b, verify (a, b) = true ↔ Q.valid a b) :
    Q.promise ∈ P encA := by
  rw [mem_P]
  refine ⟨fun a => verify (a, f a), ?_, fun a => ?_⟩
  · exact hv_poly.comp (ComputableInPolyTime.id'.prod hf_poly)
  · rw [mem_promise_iff_valid_solver hf_solves a, ← hv_spec]

/-- Instance-dependent oracle search-to-decision reduction: given a polynomial-time solver `f`
for `Q` and a uniform polynomial-time oracle verifier `vprog` deciding `Q.valid a b` against
instance-specific oracle `O a`, composing `f` with `vprog` yields a uniform polynomial-time
oracle program deciding `a ∈ Q.promise` against `O a`. -/
theorem oracle_reduction_of_polyTime_solver
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {O : α → Set (List Bool)} {Q : PromiseSearchProblem α β}
    {f : α → β} (hf_poly : ComputableInPolyTime f encA encB) (hf_solves : Q.Solves f)
    {vprog : α × β → WordQueryComp Unit Bool}
    (hv_poly : IsOraclePPTOn (encPair encA encB) encBool
      (fun p => OracleComp.interpret ProbOracleComp.query (vprog p)))
    (hv_spec : ∀ a b,
      OracleComp.interpret (m := Id) (languageOracle (O a)) (vprog (a, b)) = true ↔ Q.valid a b) :
    ∃ rprog : α → WordQueryComp Unit Bool,
      IsOraclePPTOn encA encBool
        (fun a => OracleComp.interpret ProbOracleComp.query (rprog a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle (O a)) (rprog a) = true ↔
        a ∈ Q.promise := by
  refine ⟨fun a => vprog (a, f a), ?_, fun a => ?_⟩
  · exact hv_poly.preprocess (ComputableInPolyTime.id'.prod hf_poly)
  · rw [hv_spec a (f a), ← mem_promise_iff_valid_solver hf_solves a]

end Complexity

end PromiseSearchProblem

end Complexity

end CslibFrontier
