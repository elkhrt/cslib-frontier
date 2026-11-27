/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Deterministic Evaluation and Path Query Counting for Oracle Computations

Universe-polymorphic deterministic evaluation (`evalDet`) and executed path query counting
(`queryCount`) for typed oracle programs `Cslib.OracleComp spec α`, together with monadic
composition, bounded-iteration (`Cslib.OracleComp.iterate`), and path-budget
(`Cslib.OracleComp.IsCostBounded` / `Cslib.OracleComp.IsQueryBounded`) bridge lemmas.

## Main definitions

* `Cslib.OracleComp.evalDet`: deterministic output value of an `OracleComp` program against a pure
  dependent oracle `(q : ι) → spec q`.
* `Cslib.OracleComp.queryCount`: exact number of oracle queries executed along the deterministic
  path of an `OracleComp` program against `(q : ι) → spec q`.

## Main results

* `Cslib.OracleComp.evalDet_freeMBind`, `Cslib.OracleComp.evalDet_bind`,
  `Cslib.OracleComp.queryCount_freeMBind`, `Cslib.OracleComp.queryCount_bind`: composition and
  additive path-query laws under monadic sequencing.
* `Cslib.OracleComp.evalDet_eq_of_queryCount_eq_zero`: any deterministic execution issuing zero
  queries produces the same output against every oracle.
* `Cslib.OracleComp.evalDet_iterate`, `Cslib.OracleComp.queryCount_iterate_le`: deterministic
  evaluation of `Cslib.OracleComp.iterate` agrees with `Function.iterate` and scales per-step query
  bounds linearly.
* `Cslib.OracleComp.queryCount_le_of_isQueryBounded`, `Cslib.OracleComp.isCostBounded_iterate`,
  `Cslib.OracleComp.isQueryBounded_iterate`, `Cslib.OracleComp.not_isQueryBounded_query_zero`:
  soundness and sharpness bridges between `queryCount` and `IsQueryBounded`.
-/

public section

namespace Cslib.OracleComp

universe u v w w'

section EvaluationAndCount

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Evaluate an `OracleComp` program deterministically by answering each query `q : ι` with
`oracle q : spec q`. -/
def evalDet {α : Type w} (oracle : (q : ι) → spec q) (program : OracleComp spec α) : α :=
  PFunctor.FreeM.foldFreeM id (fun q cont ↦ cont (oracle q)) program

/-- Count the number of oracle queries executed along the deterministic path of `program` against
`oracle : (q : ι) → spec q`. -/
def queryCount {α : Type w} (oracle : (q : ι) → spec q) (program : OracleComp spec α) : ℕ :=
  PFunctor.FreeM.foldFreeM (fun _ ↦ 0) (fun q cont ↦ cont (oracle q) + 1) program

/-- Deterministic evaluation of a pure value returns that value. -/
@[simp]
theorem evalDet_pure {α : Type w} (oracle : (q : ι) → spec q) (a : α) :
    evalDet oracle (pure a : OracleComp spec α) = a := by
  rfl

/-- Evaluating a single oracle call `OracleComp.query q` returns `oracle q`. -/
@[simp]
theorem evalDet_query (oracle : (q : ι) → spec q) (q : ι) :
    evalDet oracle (OracleComp.query (spec := spec) q) = oracle q := by
  rfl

/-- Deterministic evaluation of heterogeneous sequencing feeds the first output into the
continuation. -/
@[simp]
theorem evalDet_freeMBind {α : Type w} {β : Type w'} (oracle : (q : ι) → spec q)
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    evalDet oracle (PFunctor.FreeM.bind program next) =
      evalDet oracle (next (evalDet oracle program)) := by
  induction program using PFunctor.FreeM.induction with
  | pure _ => rfl
  | lift_bind q _ ih => exact ih (oracle q)

/-- Deterministic evaluation of monadic `>>=` feeds the first output into the continuation. -/
@[simp]
theorem evalDet_bind {α β : Type w} (oracle : (q : ι) → spec q)
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    evalDet oracle (program >>= next) = evalDet oracle (next (evalDet oracle program)) := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using evalDet_freeMBind oracle program next

/-- Deterministic evaluation commutes with heterogeneous `PFunctor.FreeM.map`. -/
@[simp]
theorem evalDet_freeMMap {α : Type w} {β : Type w'} (oracle : (q : ι) → spec q)
    (f : α → β) (program : OracleComp spec α) :
    evalDet oracle (PFunctor.FreeM.map f program) = f (evalDet oracle program) := by
  rw [← PFunctor.FreeM.bind_pure_comp, evalDet_freeMBind, Function.comp_apply, evalDet_pure]

/-- Deterministic evaluation commutes with `<$>`. -/
@[simp]
theorem evalDet_map {α β : Type w} (oracle : (q : ι) → spec q)
    (f : α → β) (program : OracleComp spec α) :
    evalDet oracle (f <$> program) = f (evalDet oracle program) := by
  simpa only [PFunctor.FreeM.map_eq_map] using evalDet_freeMMap oracle f program

/-- Returning a pure value executes `0` oracle queries. -/
@[simp]
theorem queryCount_pure {α : Type w} (oracle : (q : ι) → spec q) (a : α) :
    queryCount oracle (pure a : OracleComp spec α) = 0 := by
  rfl

/-- A single oracle call `OracleComp.query q` executes exactly `1` query. -/
@[simp]
theorem queryCount_query (oracle : (q : ι) → spec q) (q : ι) :
    queryCount oracle (OracleComp.query (spec := spec) q) = 1 := by
  rfl

/-- Path query count adds across heterogeneous `PFunctor.FreeM.bind`. -/
@[simp]
theorem queryCount_freeMBind {α : Type w} {β : Type w'} (oracle : (q : ι) → spec q)
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    queryCount oracle (PFunctor.FreeM.bind program next) =
      queryCount oracle program + queryCount oracle (next (evalDet oracle program)) := by
  induction program using PFunctor.FreeM.induction with
  | pure _ => exact (Nat.zero_add _).symm
  | lift_bind q cont ih =>
    change queryCount oracle (PFunctor.FreeM.bind (cont (oracle q)) next) + 1 =
      (queryCount oracle (cont (oracle q)) + 1) +
        queryCount oracle (next (evalDet oracle (cont (oracle q))))
    rw [ih (oracle q)]
    omega

/-- Path query count adds across monadic `>>=`. -/
@[simp]
theorem queryCount_bind {α β : Type w} (oracle : (q : ι) → spec q)
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    queryCount oracle (program >>= next) =
      queryCount oracle program + queryCount oracle (next (evalDet oracle program)) := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using queryCount_freeMBind oracle program next

/-- Postprocessing via `PFunctor.FreeM.map` issues no additional oracle queries. -/
@[simp]
theorem queryCount_freeMMap {α : Type w} {β : Type w'} (oracle : (q : ι) → spec q)
    (f : α → β) (program : OracleComp spec α) :
    queryCount oracle (PFunctor.FreeM.map f program) = queryCount oracle program := by
  rw [← PFunctor.FreeM.bind_pure_comp, queryCount_freeMBind, Function.comp_apply,
    queryCount_pure, Nat.add_zero]

/-- Postprocessing via `<$>` issues no additional oracle queries. -/
@[simp]
theorem queryCount_map {α β : Type w} (oracle : (q : ι) → spec q)
    (f : α → β) (program : OracleComp spec α) :
    queryCount oracle (f <$> program) = queryCount oracle program := by
  simpa only [PFunctor.FreeM.map_eq_map] using queryCount_freeMMap oracle f program

/-- If `program` makes `0` queries against `oracle₁`, then its deterministic output is independent
of the oracle and agrees with its evaluation against any `oracle₂`. -/
theorem evalDet_eq_of_queryCount_eq_zero {α : Type w} {oracle₁ oracle₂ : (q : ι) → spec q}
    {program : OracleComp spec α} (h : queryCount oracle₁ program = 0) :
    evalDet oracle₁ program = evalDet oracle₂ program := by
  induction program using PFunctor.FreeM.induction with
  | pure _ => rfl
  | lift_bind q cont _ =>
    change queryCount oracle₁ (cont (oracle₁ q)) + 1 = 0 at h
    omega

end EvaluationAndCount

section IterationAndBudgets

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {State : Type v}

/-- Deterministic evaluation of `OracleComp.iterate count step initial` coincides with
`count`-fold iteration of the deterministic step map `fun s ↦ evalDet oracle (step s)`. -/
@[simp]
theorem evalDet_iterate (oracle : (q : ι) → spec q) (count : ℕ)
    (step : State → OracleComp spec State) (initial : State) :
    evalDet oracle (iterate count step initial) =
      (fun s ↦ evalDet oracle (step s))^[count] initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterate_succ, evalDet_bind, ih, Function.iterate_succ_apply']

/-- If each step `step s` issues at most `b` queries against `oracle`, then `count` adaptive
iterations via `OracleComp.iterate` issue at most `count * b` queries. -/
theorem queryCount_iterate_le (oracle : (q : ι) → spec q) (count : ℕ)
    (step : State → OracleComp spec State) (initial : State) {b : ℕ}
    (hstep : ∀ s, queryCount oracle (step s) ≤ b) :
    queryCount oracle (iterate count step initial) ≤ count * b := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [iterate_succ, queryCount_bind, Nat.succ_mul]
    exact Nat.add_le_add ih (hstep _)

/-- Every path-wide query budget `program.IsQueryBounded n` bounds the executed deterministic
query count `queryCount oracle program` against every oracle. -/
theorem queryCount_le_of_isQueryBounded {α : Type v} (oracle : (q : ι) → spec q)
    {program : OracleComp spec α} {n : ℕ} (h : program.IsQueryBounded n) :
    queryCount oracle program ≤ n := by
  induction h with
  | pure _ n => exact Nat.zero_le n
  | liftBind q _ _ _ ih =>
    rw [queryCount_bind, queryCount_query, evalDet_query]
    have hcont := ih (oracle q)
    omega

/-- Path-wide query cost budgets scale linearly across `OracleComp.iterate`. -/
theorem isCostBounded_iterate {cost : ι → ℕ} (count : ℕ)
    {step : State → OracleComp spec State} (initial : State) {b : ℕ}
    (hstep : ∀ s, IsCostBounded cost (step s) b) :
    IsCostBounded cost (iterate count step initial) (count * b) := by
  induction count with
  | zero => simpa using IsCostBounded.pure initial 0
  | succ count ih =>
    rw [iterate_succ, Nat.succ_mul]
    exact ih.bind hstep

/-- Path-wide unit query budgets `IsQueryBounded` scale linearly across `OracleComp.iterate`. -/
theorem isQueryBounded_iterate (count : ℕ)
    {step : State → OracleComp spec State} (initial : State) {b : ℕ}
    (hstep : ∀ s, (step s).IsQueryBounded b) :
    (iterate count step initial).IsQueryBounded (count * b) :=
  isCostBounded_iterate count initial hstep

/-- Sharpness of zero query budgets: a single oracle call `OracleComp.query q` never satisfies
`IsQueryBounded 0` when the oracle interface `∀ q, spec q` is inhabited. -/
theorem not_isQueryBounded_query_zero (oracle : (q : ι) → spec q) (q : ι) :
    ¬ (OracleComp.query (spec := spec) q).IsQueryBounded 0 := by
  intro h
  have hle := queryCount_le_of_isQueryBounded oracle h
  rw [queryCount_query] at hle
  exact Nat.not_succ_le_zero 0 hle

end IterationAndBudgets

end Cslib.OracleComp
