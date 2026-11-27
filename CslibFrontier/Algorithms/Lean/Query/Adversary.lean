/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.Query.FreeM

/-!
# Query transcripts, stateful adversaries, and nonadaptivity for `Cslib.FreeM`

This module extends the `Cslib.FreeM` query-complexity framework
(`Cslib.Algorithms.Lean.Query.FreeM`) with:

* **Ordered query-answer transcripts** (`Cslib.FreeM.transcript`): the exact sequence of dependent
  query-response pairs `⟨ι, op, a⟩` observed along the execution path of a query program against an
  oracle, whose length equals `FreeM.countQueries`, together with **oracle congruence**
  (`Cslib.FreeM.eval_congr_transcript`, `Cslib.FreeM.transcript_congr`,
  `Cslib.FreeM.countQueries_congr_transcript`).
* **Interactive stateful adversaries** (`Cslib.FreeM.runAdversary`): adaptive adversaries that
  maintain internal state `S` across queries and choose each answer dynamically, together with the
  **adversary consistency theorem** (`Cslib.FreeM.runAdversary_consistent`): whenever a concrete
  oracle realizes every query-answer pair recorded in the adversary transcript, running the query
  program on that oracle produces the exact same output, transcript, and query count as the
  adversary interaction.
* **Nonadaptive query programs** (`Cslib.FreeM.IsNonadaptive`, `Cslib.FreeM.queryBatch`):
  characterization of query programs whose issued query sequence is independent of the oracle, and
  a canonical batch-query constructor issuing a fixed list of homogeneous queries in parallel.

## Main definitions

* `Cslib.FreeM.QueryEntry`, `Cslib.FreeM.QueryObs`: erased queries and dependent query-answer pairs
  for a query effect `F : Type u → Type v`.
* `Cslib.FreeM.transcript`, `Cslib.FreeM.queries`: ordered query-answer and query transcripts of a
  `FreeM F α` program against an oracle.
* `Cslib.FreeM.Adversary`, `Cslib.FreeM.runAdversary`: stateful adaptive query adversaries and
  their execution semantics.
* `Cslib.FreeM.IsNonadaptive`, `Cslib.FreeM.queryBatch`: nonadaptive query programs and batch
  queries.

## Main results

* `Cslib.FreeM.length_transcript`, `Cslib.FreeM.transcript_bind`: transcript length agrees with
  `countQueries` and distributes over monadic bind.
* `Cslib.FreeM.eval_congr_transcript`, `Cslib.FreeM.countQueries_congr_transcript`: two oracles
  agreeing on all queries issued along `p.transcript oracle₁` induce identical outputs, transcripts,
  and query counts.
* `Cslib.FreeM.runAdversary_consistent`: fundamental consistency lemma for adaptive adversary lower
  bounds.
* `Cslib.FreeM.isNonadaptive_queryBatch`: batch query programs are nonadaptive with query count
  equal to batch length.
-/

public section

namespace Cslib.FreeM

universe u v w

variable {F : Type u → Type v} {α β : Type u}

/-- A single query of signature `F : Type u → Type v` packaged with its response type. -/
structure QueryEntry (F : Type u → Type v) : Type (max (u + 1) v) where
  /-- Response type of the query. -/
  Resp : Type u
  /-- The query operation itself. -/
  op : F Resp

/-- A recorded query-answer observation `(Resp, op, ans)` from executing a `FreeM F` program. -/
structure QueryObs (F : Type u → Type v) : Type (max (u + 1) v) where
  /-- Response type of the query. -/
  Resp : Type u
  /-- The issued query operation. -/
  op : F Resp
  /-- The answer returned by the oracle or adversary. -/
  ans : Resp

/-- Forget the recorded answer of a `QueryObs`, retaining only the issued query. -/
def QueryObs.entry (obs : QueryObs F) : QueryEntry F :=
  ⟨obs.Resp, obs.op⟩

/-- Predicate asserting that `oracle` agrees with a recorded observation `obs`. -/
def QueryObs.MatchesOracle (oracle : {ι : Type u} → F ι → ι) (obs : QueryObs F) : Prop :=
  oracle obs.op = obs.ans

/-- Ordered transcript of query-answer observations along the execution of `p` against `oracle`. -/
def transcript (oracle : {ι : Type u} → F ι → ι) : FreeM F α → List (QueryObs F)
  | .pure _ => []
  | .liftBind op cont => ⟨_, op, oracle op⟩ :: transcript oracle (cont (oracle op))

@[simp]
theorem transcript_pure (oracle : {ι : Type u} → F ι → ι) (a : α) :
    transcript oracle (pure a : FreeM F α) = [] := by
  rfl

@[simp]
theorem transcript_liftBind (oracle : {ι : Type u} → F ι → ι) {ι : Type u}
    (op : F ι) (cont : ι → FreeM F α) :
    transcript oracle (FreeM.lift op >>= cont) =
      ⟨ι, op, oracle op⟩ :: transcript oracle (cont (oracle op)) := by
  rfl

@[simp]
theorem transcript_lift (oracle : {ι : Type u} → F ι → ι) {ι : Type u} (op : F ι) :
    transcript oracle (FreeM.lift op) = [⟨ι, op, oracle op⟩] := by
  rfl

/-- Sequential composition concatenates query-answer transcripts. -/
@[simp]
theorem transcript_bind (oracle : {ι : Type u} → F ι → ι) (p : FreeM F α) (k : α → FreeM F β) :
    transcript oracle (p >>= k) = transcript oracle p ++ transcript oracle (k (p.eval oracle)) := by
  induction p with
  | pure _ => rfl
  | lift_bind op _ ih => exact congrArg (⟨_, op, oracle op⟩ :: ·) (ih (oracle op))

/-- Every entry in `p.transcript oracle` matches `oracle`. -/
theorem matchesOracle_of_mem_transcript (oracle : {ι : Type u} → F ι → ι) (p : FreeM F α)
    {obs : QueryObs F} (h : obs ∈ p.transcript oracle) : obs.MatchesOracle oracle := by
  induction p with
  | pure _ => cases h
  | lift_bind op _ ih =>
    rcases List.mem_cons.mp h with rfl | htail
    · rfl
    · exact ih (oracle op) htail

/-- The length of `p.transcript oracle` equals `p.countQueries oracle`. -/
@[simp]
theorem length_transcript (oracle : {ι : Type u} → F ι → ι) (p : FreeM F α) :
    (p.transcript oracle).length = p.countQueries oracle := by
  induction p with
  | pure _ => rfl
  | lift_bind op cont ih =>
    change (transcript oracle (cont (oracle op))).length + 1 =
      1 + countQueries oracle (cont (oracle op))
    rw [ih (oracle op), Nat.add_comm]

/-- Ordered list of queries (without answers) issued by `p` against `oracle`. -/
def queries (oracle : {ι : Type u} → F ι → ι) (p : FreeM F α) : List (QueryEntry F) :=
  (p.transcript oracle).map QueryObs.entry

@[simp]
theorem length_queries (oracle : {ι : Type u} → F ι → ι) (p : FreeM F α) :
    (p.queries oracle).length = p.countQueries oracle := by
  rw [queries, List.length_map, length_transcript]

private theorem congr_of_matchesOracle {oracle₁ oracle₂ : {ι : Type u} → F ι → ι}
    (p : FreeM F α) (h : ∀ obs ∈ p.transcript oracle₁, obs.MatchesOracle oracle₂) :
    p.eval oracle₁ = p.eval oracle₂ ∧ p.transcript oracle₁ = p.transcript oracle₂ := by
  induction p with
  | pure _ => exact ⟨rfl, rfl⟩
  | lift_bind op cont ih =>
    have hop : oracle₂ op = oracle₁ op := h ⟨_, op, oracle₁ op⟩ List.mem_cons_self
    obtain ⟨he, ht⟩ := ih (oracle₁ op) fun obs hobs ↦ h obs (List.mem_cons_of_mem _ hobs)
    change eval oracle₁ (cont (oracle₁ op)) = eval oracle₂ (cont (oracle₂ op)) ∧
      (⟨_, op, oracle₁ op⟩ :: transcript oracle₁ (cont (oracle₁ op))) =
      (⟨_, op, oracle₂ op⟩ :: transcript oracle₂ (cont (oracle₂ op)))
    rw [hop]
    exact ⟨he, congrArg _ ht⟩

/-- **Oracle congruence for evaluation**: if `oracle₂` agrees with `oracle₁` on every query in
`p.transcript oracle₁`, then `p.eval oracle₁ = p.eval oracle₂`. -/
theorem eval_congr_transcript {oracle₁ oracle₂ : {ι : Type u} → F ι → ι} (p : FreeM F α)
    (h : ∀ obs ∈ p.transcript oracle₁, obs.MatchesOracle oracle₂) :
    p.eval oracle₁ = p.eval oracle₂ :=
  (congr_of_matchesOracle p h).1

/-- **Oracle congruence for transcripts**: if `oracle₂` agrees with `oracle₁` on every query in
`p.transcript oracle₁`, then `p.transcript oracle₁ = p.transcript oracle₂`. -/
theorem transcript_congr {oracle₁ oracle₂ : {ι : Type u} → F ι → ι} (p : FreeM F α)
    (h : ∀ obs ∈ p.transcript oracle₁, obs.MatchesOracle oracle₂) :
    p.transcript oracle₁ = p.transcript oracle₂ :=
  (congr_of_matchesOracle p h).2

/-- **Oracle congruence for query counts**: if `oracle₂` agrees with `oracle₁` on every query in
`p.transcript oracle₁`, then `p.countQueries oracle₁ = p.countQueries oracle₂`. -/
theorem countQueries_congr_transcript {oracle₁ oracle₂ : {ι : Type u} → F ι → ι} (p : FreeM F α)
    (h : ∀ obs ∈ p.transcript oracle₁, obs.MatchesOracle oracle₂) :
    p.countQueries oracle₁ = p.countQueries oracle₂ := by
  rw [← length_transcript, ← length_transcript, transcript_congr p h]

/-- A stateful adaptive adversary with state type `S` answering queries of signature `F`. -/
abbrev Adversary (F : Type u → Type v) (S : Type w) : Type (max (u + 1) v w) :=
  S → {ι : Type u} → F ι → ι × S

/-- Run `p : FreeM F α` interactively against a stateful adversary `adv` starting in state `s`,
returning `(result, transcript, finalState)`. -/
def runAdversary {S : Type w} (adv : Adversary F S) :
    FreeM F α → S → α × List (QueryObs F) × S
  | .pure a, s => (a, [], s)
  | .liftBind op cont, s =>
    let step := adv s op
    let next := runAdversary adv (cont step.1) step.2
    (next.1, ⟨_, op, step.1⟩ :: next.2.1, next.2.2)

@[simp]
theorem runAdversary_pure {S : Type w} (adv : Adversary F S) (a : α) (s : S) :
    runAdversary adv (pure a : FreeM F α) s = (a, [], s) := by
  rfl

@[simp]
theorem runAdversary_liftBind {S : Type w} (adv : Adversary F S) {ι : Type u}
    (op : F ι) (cont : ι → FreeM F α) (s : S) :
    runAdversary adv (FreeM.lift op >>= cont) s =
      let step := adv s op
      let next := runAdversary adv (cont step.1) step.2
      (next.1, ⟨ι, op, step.1⟩ :: next.2.1, next.2.2) := by
  rfl

/-- **Adversary consistency theorem**: if a concrete `oracle` realizes every observation recorded
during `runAdversary adv p s`, then executing `p` against `oracle` yields the exact output,
transcript, and query count of the adversary run. -/
theorem runAdversary_consistent {S : Type w} (adv : Adversary F S) (p : FreeM F α) (s : S)
    (oracle : {ι : Type u} → F ι → ι)
    (hcons : ∀ obs ∈ (runAdversary adv p s).2.1, obs.MatchesOracle oracle) :
    p.eval oracle = (runAdversary adv p s).1 ∧
      p.transcript oracle = (runAdversary adv p s).2.1 ∧
      p.countQueries oracle = (runAdversary adv p s).2.1.length := by
  suffices p.eval oracle = (runAdversary adv p s).1 ∧
      p.transcript oracle = (runAdversary adv p s).2.1 from
    ⟨this.1, this.2, by rw [← length_transcript, this.2]⟩
  induction p generalizing s with
  | pure _ => exact ⟨rfl, rfl⟩
  | lift_bind op cont ih =>
    have hop : oracle op = (adv s op).1 := hcons ⟨_, op, (adv s op).1⟩ List.mem_cons_self
    obtain ⟨he, ht⟩ := ih (adv s op).1 (adv s op).2
      fun obs hobs ↦ hcons obs (List.mem_cons_of_mem _ hobs)
    change eval oracle (cont (oracle op)) = (runAdversary adv (cont (adv s op).1) (adv s op).2).1 ∧
      (⟨_, op, oracle op⟩ :: transcript oracle (cont (oracle op))) =
      (⟨_, op, (adv s op).1⟩ :: (runAdversary adv (cont (adv s op).1) (adv s op).2).2.1)
    rw [hop]
    exact ⟨he, congrArg _ ht⟩

/-- A query program `p : FreeM F α` is **nonadaptive** if the ordered list of queries it issues is
independent of the oracle. -/
def IsNonadaptive (p : FreeM F α) : Prop :=
  ∀ oracle₁ oracle₂ : {ι : Type u} → F ι → ι, p.queries oracle₁ = p.queries oracle₂

/-- Every nonadaptive query program has an oracle-independent query count. -/
theorem IsNonadaptive.countQueries_eq {p : FreeM F α} (hp : p.IsNonadaptive)
    (oracle₁ oracle₂ : {ι : Type u} → F ι → ι) :
    p.countQueries oracle₁ = p.countQueries oracle₂ := by
  rw [← length_queries, ← length_queries, hp oracle₁ oracle₂]

/-- Issue a fixed batch `qs : List (F ι)` of queries nonadaptively and apply `combine` to the list
of answers. -/
def queryBatch {ι : Type u} : List (F ι) → (List ι → α) → FreeM F α
  | [], combine => pure (combine [])
  | q :: qs, combine => FreeM.lift q >>= fun a ↦ queryBatch qs fun as ↦ combine (a :: as)

@[simp]
theorem eval_queryBatch {ι : Type u} (oracle : {κ : Type u} → F κ → κ)
    (qs : List (F ι)) (combine : List ι → α) :
    (queryBatch qs combine).eval oracle = combine (qs.map fun q ↦ oracle q) := by
  induction qs generalizing combine with
  | nil => rfl
  | cons q qs ih => exact ih fun as ↦ combine (oracle q :: as)

@[simp]
theorem queries_queryBatch {ι : Type u} (oracle : {κ : Type u} → F κ → κ)
    (qs : List (F ι)) (combine : List ι → α) :
    (queryBatch qs combine).queries oracle = qs.map fun q ↦ ⟨ι, q⟩ := by
  induction qs generalizing combine with
  | nil => rfl
  | cons q qs ih => exact congrArg (⟨ι, q⟩ :: ·) (ih _)

@[simp]
theorem countQueries_queryBatch {ι : Type u} (oracle : {κ : Type u} → F κ → κ)
    (qs : List (F ι)) (combine : List ι → α) :
    (queryBatch qs combine).countQueries oracle = qs.length := by
  rw [← length_queries, queries_queryBatch, List.length_map]

/-- Every batch query program `queryBatch qs combine` is nonadaptive. -/
theorem isNonadaptive_queryBatch {ι : Type u} (qs : List (F ι)) (combine : List ι → α) :
    (queryBatch qs combine).IsNonadaptive := fun o₁ o₂ ↦ by
  rw [queries_queryBatch, queries_queryBatch]

end Cslib.FreeM
