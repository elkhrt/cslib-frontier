/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Deterministic Exact-Value Oracle Decision Trees and Multiplicative Fiber Amplification

This module formalizes adaptive deterministic exact-value (real-answer) oracle algorithms, their
equivalence with fixed-horizon sequential query protocols, simulation and composition combinators,
worst-case deterministic exact-value query complexity, finite-net solvability for uniformly
Lipschitz families on compact pseudometric spaces, and exact `|ι| * ℓ` (in particular `2 ^ n * ℓ` on
the fractional hypercube `[0, 1]^n`) multiplicative query-complexity amplification for minimizing a
common-optimum family glued across finitely many vertex-isolated fibers.

All declarations are proved purely under standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Main definitions

* `CslibFrontier.QueryComplexity.DetValueAlg`: adaptive deterministic real-value decision tree of
  depth at most `n` querying `Q` and returning an output in `O`.
* `CslibFrontier.QueryComplexity.DetValueAlg.run`,
  `CslibFrontier.QueryComplexity.DetValueAlg.queryCount`,
  `CslibFrontier.QueryComplexity.DetValueAlg.queriedSet`,
  `CslibFrontier.QueryComplexity.DetValueAlg.transcript`: execution semantics, query count, queried
  set, and query-response transcript.
* `CslibFrontier.QueryComplexity.DetValueAlg.castLe`,
  `CslibFrontier.QueryComplexity.DetValueAlg.mapQuery`,
  `CslibFrontier.QueryComplexity.DetValueAlg.map`,
  `CslibFrontier.QueryComplexity.DetValueAlg.bind`,
  `CslibFrontier.QueryComplexity.DetValueAlg.seqList`,
  `CslibFrontier.QueryComplexity.DetValueAlg.evalMin`: budget weakening, query/response/output
  simulation, sequential composition, and finite-candidate argmin.
* `CslibFrontier.QueryComplexity.DetSeqValueAlg`: fixed-horizon sequential exact-value protocol and
  output-preserving translations to and from `DetValueAlg`.
* `CslibFrontier.QueryComplexity.IsExactValueSolvable`,
  `CslibFrontier.QueryComplexity.exactValueComplexity`: worst-case deterministic exact-value
  solvability and query complexity.
* `CslibFrontier.QueryComplexity.hypercubePenalty`,
  `CslibFrontier.QueryComplexity.hypercubeGluedObj`: vertex-isolating affine penalties on `[0, 1]^n`
  and convex-preserving fractional extension of `2 ^ n` fiber objectives.

## Main results

* `CslibFrontier.QueryComplexity.DetValueAlg.eq_on_queriedSet`: agreement of output, transcript,
  query count, and queried set on objectives coinciding on the queried set.
* `CslibFrontier.QueryComplexity.DetValueAlg.evalMin_spec`: exact argmin over `K` candidates in `K`
  evaluations.
* `CslibFrontier.QueryComplexity.DetSeqValueAlg.run_toDetValueAlg`,
  `CslibFrontier.QueryComplexity.DetValueAlg.run_toDetSeqValueAlg`: equivalence of tree and
  sequential deterministic exact-value models.
* `CslibFrontier.QueryComplexity.exists_isExactValueSolvable_of_compact_lipschitz`: finite-budget
  solvability of uniformly Lipschitz families on nonempty compact pseudometric domains.
* `CslibFrontier.QueryComplexity.two_pow_mul_le_exactValueComplexity_hypercube`: exact `2 ^ n * ℓ`
  multiplicative exact-value query-complexity amplification over `[0, 1]^n × Y` when fractional
  queries are permitted and outputs lie in `{0, 1}^n × Y`.
-/

public section

universe u v w z

namespace CslibFrontier.QueryComplexity

open Set

/-! ### Adaptive deterministic exact-value query trees -/

/-- Adaptive deterministic exact-value decision tree with query domain `Q`, output domain `O`, and
worst-case query budget `n`. -/
inductive DetValueAlg (Q : Type u) (O : Type v) : ℕ → Type (max u v)
  /-- Halt immediately and output `out : O`. -/
  | halt {n : ℕ} (out : O) : DetValueAlg Q O n
  /-- Evaluate `f pt` and branch adaptively on the exact real response. -/
  | query {n : ℕ} (pt : Q) (next : ℝ → DetValueAlg Q O n) : DetValueAlg Q O (n + 1)

section Core

variable {Q : Type u} {O : Type v}

/-- Execute `alg` against an exact value oracle `f : Q → ℝ`. -/
def DetValueAlg.run : {n : ℕ} → DetValueAlg Q O n → (Q → ℝ) → O
  | _, .halt out, _ => out
  | _, .query pt next, f => (next (f pt)).run f

@[simp]
theorem DetValueAlg.run_halt {n : ℕ} (out : O) (f : Q → ℝ) :
    (DetValueAlg.halt (Q := Q) (n := n) out).run f = out := by
  rw [DetValueAlg.run]

@[simp]
theorem DetValueAlg.run_query {n : ℕ} (pt : Q) (next : ℝ → DetValueAlg Q O n) (f : Q → ℝ) :
    (DetValueAlg.query pt next).run f = (next (f pt)).run f := by
  rw [DetValueAlg.run]

/-- Number of oracle evaluations issued when running `alg` on `f`. -/
def DetValueAlg.queryCount : {n : ℕ} → DetValueAlg Q O n → (Q → ℝ) → ℕ
  | _, .halt _, _ => 0
  | _, .query pt next, f => (next (f pt)).queryCount f + 1

@[simp]
theorem DetValueAlg.queryCount_halt {n : ℕ} (out : O) (f : Q → ℝ) :
    (DetValueAlg.halt (Q := Q) (n := n) out).queryCount f = 0 := by
  rw [DetValueAlg.queryCount]

@[simp]
theorem DetValueAlg.queryCount_query {n : ℕ} (pt : Q) (next : ℝ → DetValueAlg Q O n)
    (f : Q → ℝ) :
    (DetValueAlg.query pt next).queryCount f = (next (f pt)).queryCount f + 1 := by
  rw [DetValueAlg.queryCount]

/-- Every execution of `alg : DetValueAlg Q O n` performs at most `n` queries. -/
theorem DetValueAlg.queryCount_le :
    ∀ {n : ℕ} (alg : DetValueAlg Q O n) (f : Q → ℝ), alg.queryCount f ≤ n
  | _, .halt _, _ => by simp
  | _, .query pt next, f => by simpa using Nat.succ_le_succ ((next (f pt)).queryCount_le f)

/-- Set of points queried during the execution of `alg` on `f`. -/
def DetValueAlg.queriedSet : {n : ℕ} → DetValueAlg Q O n → (Q → ℝ) → Set Q
  | _, .halt _, _ => ∅
  | _, .query pt next, f => insert pt ((next (f pt)).queriedSet f)

@[simp]
theorem DetValueAlg.queriedSet_halt {n : ℕ} (out : O) (f : Q → ℝ) :
    (DetValueAlg.halt (Q := Q) (n := n) out).queriedSet f = ∅ := by
  rw [DetValueAlg.queriedSet]

@[simp]
theorem DetValueAlg.queriedSet_query {n : ℕ} (pt : Q) (next : ℝ → DetValueAlg Q O n)
    (f : Q → ℝ) :
    (DetValueAlg.query pt next).queriedSet f = insert pt ((next (f pt)).queriedSet f) := by
  rw [DetValueAlg.queriedSet]

/-- Ordered transcript of `(query, value)` pairs generated by `alg` on `f`. -/
def DetValueAlg.transcript : {n : ℕ} → DetValueAlg Q O n → (Q → ℝ) → List (Q × ℝ)
  | _, .halt _, _ => []
  | _, .query pt next, f => (pt, f pt) :: (next (f pt)).transcript f

@[simp]
theorem DetValueAlg.transcript_halt {n : ℕ} (out : O) (f : Q → ℝ) :
    (DetValueAlg.halt (Q := Q) (n := n) out).transcript f = [] := by
  rw [DetValueAlg.transcript]

@[simp]
theorem DetValueAlg.transcript_query {n : ℕ} (pt : Q) (next : ℝ → DetValueAlg Q O n)
    (f : Q → ℝ) :
    DetValueAlg.transcript (.query pt next) f = (pt, f pt) :: (next (f pt)).transcript f := by
  rw [DetValueAlg.transcript]

/-- Agreement invariance: two oracles agreeing on `alg.queriedSet f` induce identical output,
transcript, query count, and queried set. -/
theorem DetValueAlg.eq_on_queriedSet :
    ∀ {n : ℕ} (alg : DetValueAlg Q O n) {f g : Q → ℝ},
      (∀ q ∈ alg.queriedSet f, f q = g q) →
        alg.run f = alg.run g ∧ alg.transcript f = alg.transcript g ∧
          alg.queryCount f = alg.queryCount g ∧ alg.queriedSet f = alg.queriedSet g
  | _, .halt _, _, _, _ => by simp
  | _, .query pt next, f, g, hfg => by
    have hpt : f pt = g pt := hfg pt (mem_insert pt _)
    obtain ⟨hrun, htr, hcnt, hset⟩ :=
      (next (f pt)).eq_on_queriedSet fun q hq ↦ hfg q (mem_insert_of_mem pt hq)
    simp only [DetValueAlg.run_query, DetValueAlg.transcript_query, DetValueAlg.queryCount_query,
      DetValueAlg.queriedSet_query, ← hpt]
    exact ⟨hrun, by rw [htr], by rw [hcnt], by rw [hset]⟩

end Core

/-! ### Simulation, composition, and finite-candidate argmin combinators -/

section Combinators

variable {Q : Type u} {O : Type v}

/-- Weaken the query budget from `n` to any `m ≥ n` without altering execution. -/
def DetValueAlg.castLe : {n m : ℕ} → n ≤ m → DetValueAlg Q O n → DetValueAlg Q O m
  | _, _, _, .halt out => .halt out
  | _ + 1, 0, h, .query _ _ => False.elim (Nat.not_succ_le_zero _ h)
  | _ + 1, _ + 1, h, .query pt next =>
    .query pt fun y ↦ (next y).castLe (Nat.le_of_succ_le_succ h)

@[simp]
theorem DetValueAlg.run_castLe :
    ∀ {n m : ℕ} (h : n ≤ m) (alg : DetValueAlg Q O n) (f : Q → ℝ),
      (alg.castLe h).run f = alg.run f
  | _, _, _, .halt _, _ => by simp [DetValueAlg.castLe]
  | _ + 1, 0, h, .query _ _, _ => False.elim (Nat.not_succ_le_zero _ h)
  | _ + 1, _ + 1, h, .query pt next, f => by
    simpa [DetValueAlg.castLe] using (next (f pt)).run_castLe (Nat.le_of_succ_le_succ h) f

/-- Query-preserving simulation via query translation `toQ`, query-dependent response transformation
`postVal`, and output translation `toO`. -/
def DetValueAlg.mapQuery {Q' : Type w} {O' : Type z} (toQ : Q → Q') (postVal : Q → ℝ → ℝ)
    (toO : O → O') : {n : ℕ} → DetValueAlg Q O n → DetValueAlg Q' O' n
  | _, .halt out => .halt (toO out)
  | _, .query pt next =>
    .query (toQ pt) fun y ↦ (next (postVal pt y)).mapQuery toQ postVal toO

@[simp]
theorem DetValueAlg.run_mapQuery {Q' : Type w} {O' : Type z} (toQ : Q → Q')
    (postVal : Q → ℝ → ℝ) (toO : O → O') :
    ∀ {n : ℕ} (alg : DetValueAlg Q O n) (f : Q' → ℝ),
      (alg.mapQuery toQ postVal toO).run f = toO (alg.run fun q ↦ postVal q (f (toQ q)))
  | _, .halt _, _ => by simp [DetValueAlg.mapQuery]
  | _, .query pt next, f => by
    simpa [DetValueAlg.mapQuery] using
      (next (postVal pt (f (toQ pt)))).run_mapQuery toQ postVal toO f

/-- Uniform-postprocessing specialization of `DetValueAlg.mapQuery`. -/
def DetValueAlg.map {Q' : Type w} {O' : Type z} (toQ : Q → Q') (postVal : ℝ → ℝ)
    (toO : O → O') {n : ℕ} (alg : DetValueAlg Q O n) : DetValueAlg Q' O' n :=
  alg.mapQuery toQ (fun _ y ↦ postVal y) toO

@[simp]
theorem DetValueAlg.run_map {Q' : Type w} {O' : Type z} (toQ : Q → Q') (postVal : ℝ → ℝ)
    (toO : O → O') {n : ℕ} (alg : DetValueAlg Q O n) (f : Q' → ℝ) :
    (alg.map toQ postVal toO).run f = toO (alg.run fun q ↦ postVal (f (toQ q))) := by
  simp [DetValueAlg.map]

/-- Sequential composition of two exact-value algorithms with additive query budget `m + n`. -/
def DetValueAlg.bind {O' : Type w} :
    {n m : ℕ} → DetValueAlg Q O n → (O → DetValueAlg Q O' m) → DetValueAlg Q O' (m + n)
  | _, _, .halt out, k => (k out).castLe (Nat.le_add_right _ _)
  | _ + 1, _, .query pt next, k => .query pt fun y ↦ (next y).bind k

@[simp]
theorem DetValueAlg.run_bind {O' : Type w} :
    ∀ {n m : ℕ} (alg : DetValueAlg Q O n) (k : O → DetValueAlg Q O' m) (f : Q → ℝ),
      (alg.bind k).run f = (k (alg.run f)).run f
  | _, _, .halt _, _, _ => by simp [DetValueAlg.bind]
  | _ + 1, _, .query pt next, k, f => by
    simpa [DetValueAlg.bind] using (next (f pt)).run_bind k f

/-- Execute a finite list of `n`-query algorithms sequentially and collect their outputs. -/
def DetValueAlg.seqList :
    {n : ℕ} → (xs : List (DetValueAlg Q O n)) → DetValueAlg Q (List O) (xs.length * n)
  | _, [] => .halt []
  | _, alg :: algs =>
    (alg.bind fun a ↦ (DetValueAlg.seqList algs).map id id (a :: ·)).castLe
      (by rw [List.length_cons, Nat.add_mul, one_mul, Nat.add_comm])

@[simp]
theorem DetValueAlg.run_seqList :
    ∀ {n : ℕ} (xs : List (DetValueAlg Q O n)) (f : Q → ℝ),
      (DetValueAlg.seqList xs).run f = xs.map (·.run f)
  | _, [], _ => by simp [DetValueAlg.seqList]
  | _, alg :: algs, f => by
    simp only [DetValueAlg.seqList, DetValueAlg.run_castLe, DetValueAlg.run_bind,
      DetValueAlg.run_map, id_eq, List.map_cons]
    exact congrArg (alg.run f :: ·) (DetValueAlg.run_seqList algs f)

private noncomputable def evalMinAux (toQ : O → Q) (best : O) (val : ℝ) :
    (xs : List O) → DetValueAlg Q O xs.length
  | [] => .halt best
  | y :: ys =>
    .query (toQ y) fun vy ↦
      if vy < val then evalMinAux toQ y vy ys else evalMinAux toQ best val ys

private theorem evalMinAux_spec (toQ : O → Q) (f : Q → ℝ) :
    ∀ (xs : List O) (best : O) (val : ℝ), val = f (toQ best) →
      ((evalMinAux toQ best val xs).run f = best ∨ (evalMinAux toQ best val xs).run f ∈ xs) ∧
        f (toQ ((evalMinAux toQ best val xs).run f)) ≤ f (toQ best) ∧
        ∀ y ∈ xs, f (toQ ((evalMinAux toQ best val xs).run f)) ≤ f (toQ y)
  | [], _, _, _ => by simp [evalMinAux]
  | y :: ys, best, val, hval => by
    simp only [evalMinAux, DetValueAlg.run_query]
    split_ifs with hlt
    · have ih := evalMinAux_spec toQ f ys y (f (toQ y)) rfl
      refine ⟨?_, ih.2.1.trans (hlt.le.trans_eq hval), fun z hz ↦ ?_⟩
      · rcases ih.1 with hr | hr
        · rw [hr]; exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem y hr)
      · rcases List.mem_cons.mp hz with rfl | hm
        · exact ih.2.1
        · exact ih.2.2 z hm
    · have ih := evalMinAux_spec toQ f ys best val hval
      refine ⟨?_, ih.2.1, fun z hz ↦ ?_⟩
      · rcases ih.1 with hr | hr
        · exact Or.inl hr
        · exact Or.inr (List.mem_cons_of_mem y hr)
      · rcases List.mem_cons.mp hz with rfl | hm
        · exact ih.2.1.trans (hval.symm.trans_le (le_of_not_gt hlt))
        · exact ih.2.2 z hm

/-- Select a minimizer of `f ∘ toQ` over `x₀ :: xs` using `(x₀ :: xs).length` exact queries. -/
noncomputable def DetValueAlg.evalMin (toQ : O → Q) (x₀ : O) (xs : List O) :
    DetValueAlg Q O (x₀ :: xs).length :=
  (DetValueAlg.query (toQ x₀) fun v₀ ↦ evalMinAux toQ x₀ v₀ xs).castLe (by simp)

/-- `DetValueAlg.evalMin` outputs an element of `x₀ :: xs` minimizing `f ∘ toQ`. -/
theorem DetValueAlg.evalMin_spec (toQ : O → Q) (x₀ : O) (xs : List O) (f : Q → ℝ) :
    (DetValueAlg.evalMin toQ x₀ xs).run f ∈ x₀ :: xs ∧
      ∀ y ∈ x₀ :: xs, f (toQ ((DetValueAlg.evalMin toQ x₀ xs).run f)) ≤ f (toQ y) := by
  have h := evalMinAux_spec toQ f xs x₀ (f (toQ x₀)) rfl
  simp only [DetValueAlg.evalMin, DetValueAlg.run_castLe, DetValueAlg.run_query]
  refine ⟨List.mem_cons.mpr h.1, fun y hy ↦ ?_⟩
  rcases List.mem_cons.mp hy with rfl | hm
  · exact h.2.1
  · exact h.2.2 y hm

end Combinators

/-! ### Equivalence with fixed-horizon sequential exact-value protocols -/

/-- Fixed-horizon `T`-round deterministic adaptive exact-value protocol. -/
@[ext]
structure DetSeqValueAlg (Q : Type u) (O : Type v) (T : ℕ) : Type (max u v) where
  /-- Adaptive query rule at round `t : Fin T` given previous answers. -/
  step : (t : Fin T) → (Fin t → ℝ) → Q
  /-- Final decision rule given all `T` answers. -/
  out : (Fin T → ℝ) → O

/-- Prefix of `k ≤ T` oracle responses collected when running `alg` on `f`. -/
def DetSeqValueAlg.hist {Q : Type u} {O : Type v} {T : ℕ}
    (alg : DetSeqValueAlg Q O T) (f : Q → ℝ) : (k : ℕ) → k ≤ T → (Fin k → ℝ)
  | 0, _ => Fin.elim0
  | k + 1, hk =>
    Fin.snoc (alg.hist f k (Nat.le_of_succ_le hk))
      (f (alg.step ⟨k, hk⟩ (alg.hist f k (Nat.le_of_succ_le hk))))

/-- Output returned by sequential protocol `alg` on `f`. -/
def DetSeqValueAlg.run {Q : Type u} {O : Type v} {T : ℕ}
    (alg : DetSeqValueAlg Q O T) (f : Q → ℝ) : O :=
  alg.out (alg.hist f T le_rfl)

private def detSeqAux {Q : Type u} {O : Type v} {T : ℕ} (alg : DetSeqValueAlg Q O T) :
    (m : ℕ) → m ≤ T → (Fin m → ℝ) → DetValueAlg Q O (T - m)
  | m, _, vals =>
    if hlt : m < T then
      (DetValueAlg.query (alg.step ⟨m, hlt⟩ vals) fun y ↦
        detSeqAux alg (m + 1) hlt (Fin.snoc vals y)).castLe (by omega)
    else
      .halt (alg.out fun i ↦ vals ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩)
termination_by m => T - m

private theorem detSeqAux_run {Q : Type u} {O : Type v} {T : ℕ} (alg : DetSeqValueAlg Q O T)
    (f : Q → ℝ) (m : ℕ) (hm : m ≤ T) :
    (detSeqAux alg m hm (alg.hist f m hm)).run f = alg.run f := by
  rw [detSeqAux]
  split_ifs with hlt
  · have hnext : alg.hist f (m + 1) hlt =
        Fin.snoc (alg.hist f m hm) (f (alg.step ⟨m, hlt⟩ (alg.hist f m hm))) := by
      rw [DetSeqValueAlg.hist]
    simpa only [DetValueAlg.run_castLe, DetValueAlg.run_query, ← hnext] using
      detSeqAux_run alg f (m + 1) hlt
  · have hmT : m = T := le_antisymm hm (not_lt.mp hlt)
    subst hmT
    simp [DetSeqValueAlg.run]
termination_by T - m

/-- Convert a `T`-round sequential protocol into a depth-`T` query tree. -/
def DetSeqValueAlg.toDetValueAlg {Q : Type u} {O : Type v} {T : ℕ}
    (alg : DetSeqValueAlg Q O T) : DetValueAlg Q O T :=
  (detSeqAux alg 0 (Nat.zero_le T) Fin.elim0).castLe (Nat.sub_zero T).le

/-- `DetSeqValueAlg.toDetValueAlg` preserves execution outputs on all oracles. -/
theorem DetSeqValueAlg.run_toDetValueAlg {Q : Type u} {O : Type v} {T : ℕ}
    (alg : DetSeqValueAlg Q O T) (f : Q → ℝ) : alg.toDetValueAlg.run f = alg.run f := by
  have h0 : alg.hist f 0 (Nat.zero_le T) = Fin.elim0 := by rw [DetSeqValueAlg.hist]
  simpa only [DetSeqValueAlg.toDetValueAlg, DetValueAlg.run_castLe, ← h0] using
    detSeqAux_run alg f 0 (Nat.zero_le T)

private noncomputable def treeToSeq {Q : Type u} {O : Type v} [Nonempty Q] :
    {k : ℕ} → DetValueAlg Q O k → DetSeqValueAlg Q O k
  | _, .halt out => { step := fun _ _ ↦ Classical.arbitrary Q, out := fun _ ↦ out }
  | k + 1, .query pt next =>
    { step := fun t vals ↦
        if ht : t.val = 0 then pt
        else
          have : t.val < k + 1 := t.isLt
          (treeToSeq (next (vals ⟨0, Nat.pos_of_ne_zero ht⟩))).step ⟨t.val - 1, by omega⟩
            fun i ↦ vals ⟨i.val + 1, by have : i.val < t.val - 1 := i.isLt; omega⟩
      out := fun vals ↦
        (treeToSeq (next (vals ⟨0, Nat.succ_pos _⟩))).out
          fun i ↦ vals ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

private theorem treeToSeq_hist_zero {Q : Type u} {O : Type v} [Nonempty Q] {k : ℕ} (pt : Q)
    (next : ℝ → DetValueAlg Q O k) (f : Q → ℝ) :
    ∀ (r : ℕ) (hr : r + 1 ≤ k + 1),
      (treeToSeq (DetValueAlg.query pt next)).hist f (r + 1) hr ⟨0, Nat.succ_pos r⟩ = f pt
  | 0, hr => by
    change (treeToSeq (DetValueAlg.query pt next)).hist f 1 hr (Fin.last 0) = f pt
    rw [DetSeqValueAlg.hist, Fin.snoc_last]
    simp [treeToSeq]
  | r + 1, hr => by
    change (treeToSeq (DetValueAlg.query pt next)).hist f (r + 2) hr
      (Fin.castSucc ⟨0, Nat.succ_pos r⟩) = f pt
    rw [DetSeqValueAlg.hist, Fin.snoc_castSucc]
    exact treeToSeq_hist_zero pt next f r (Nat.le_of_succ_le hr)

private theorem treeToSeq_hist_succ {Q : Type u} {O : Type v} [Nonempty Q] {k : ℕ} (pt : Q)
    (next : ℝ → DetValueAlg Q O k) (f : Q → ℝ) :
    ∀ (m : ℕ) (hm : m ≤ k) (i : Fin m),
      (treeToSeq (DetValueAlg.query pt next)).hist f (m + 1) (Nat.succ_le_succ hm)
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
        (treeToSeq (next (f pt))).hist f m hm i
  | 0, _, i => Fin.elim0 i
  | m + 1, hm, i => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hi | hi
    · have hl : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (m + 2)) =
          Fin.castSucc ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := rfl
      have hr : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      conv_lhs => rw [hl, DetSeqValueAlg.hist, Fin.snoc_castSucc]
      conv_rhs => rw [hr, DetSeqValueAlg.hist, Fin.snoc_castSucc]
      exact treeToSeq_hist_succ pt next f m (Nat.le_of_succ_le hm) ⟨i.val, hi⟩
    · have hl : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (m + 2)) = Fin.last (m + 1) :=
        Fin.ext (congrArg (· + 1) hi)
      have hr : i = Fin.last m := Fin.ext hi
      conv_lhs => rw [hl, DetSeqValueAlg.hist, Fin.snoc_last]
      conv_rhs => rw [hr, DetSeqValueAlg.hist, Fin.snoc_last]
      have hst : (treeToSeq (DetValueAlg.query pt next)).step ⟨m + 1, Nat.succ_lt_succ hm⟩ =
          fun vals ↦ (treeToSeq (next (vals ⟨0, Nat.succ_pos m⟩))).step ⟨m, hm⟩
            fun j ↦ vals ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
        funext vals; simp [treeToSeq]
      rw [hst]
      dsimp only
      rw [treeToSeq_hist_zero pt next f m (Nat.le_of_succ_le (Nat.succ_le_succ hm))]
      congr 2
      ext j
      exact treeToSeq_hist_succ pt next f m (Nat.le_of_succ_le hm) j

/-- Convert a depth-`T` query tree (on nonempty `Q`) into a fixed-horizon `T`-round protocol. -/
noncomputable def DetValueAlg.toDetSeqValueAlg {Q : Type u} {O : Type v} [Nonempty Q] {T : ℕ}
    (alg : DetValueAlg Q O T) : DetSeqValueAlg Q O T :=
  treeToSeq alg

/-- `DetValueAlg.toDetSeqValueAlg` preserves execution outputs on all oracles. -/
theorem DetValueAlg.run_toDetSeqValueAlg {Q : Type u} {O : Type v} [Nonempty Q] :
    ∀ {T : ℕ} (alg : DetValueAlg Q O T) (f : Q → ℝ), alg.toDetSeqValueAlg.run f = alg.run f
  | _, .halt _, _ => by simp [DetValueAlg.toDetSeqValueAlg, DetSeqValueAlg.run, treeToSeq]
  | k + 1, .query pt next, f => by
    rw [DetValueAlg.toDetSeqValueAlg, DetSeqValueAlg.run]
    have h0 := treeToSeq_hist_zero pt next f k le_rfl
    have hsh : (fun i : Fin k ↦
        (treeToSeq (DetValueAlg.query pt next)).hist f (k + 1) le_rfl
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = (treeToSeq (next (f pt))).hist f k le_rfl :=
      funext (treeToSeq_hist_succ pt next f k le_rfl)
    have hout : (treeToSeq (DetValueAlg.query pt next)).out =
        fun vals ↦ (treeToSeq (next (vals ⟨0, Nat.succ_pos k⟩))).out
          fun i ↦ vals ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := rfl
    rw [hout, DetValueAlg.run_query]
    dsimp only
    rw [h0, hsh]
    exact (next (f pt)).run_toDetSeqValueAlg f

/-! ### Worst-case exact-value query complexity and compact Lipschitz solvability -/

/-- `T`-query deterministic exact-value solvability of `F : Set (Q → ℝ)` to tolerance `ε` under
error functional `err : (Q → ℝ) → O → ℝ`. -/
def IsExactValueSolvable (Q : Type u) (O : Type v) (F : Set (Q → ℝ)) (err : (Q → ℝ) → O → ℝ)
    (ε : ℝ) (T : ℕ) : Prop :=
  ∃ alg : DetValueAlg Q O T, ∀ f ∈ F, err f (alg.run f) ≤ ε

/-- Worst-case deterministic exact-value query complexity (`Nat.sInf` of solvable budgets). -/
noncomputable def exactValueComplexity (Q : Type u) (O : Type v) (F : Set (Q → ℝ))
    (err : (Q → ℝ) → O → ℝ) (ε : ℝ) : ℕ :=
  sInf {T : ℕ | IsExactValueSolvable Q O F err ε T}

theorem isExactValueSolvable_exactValueComplexity {Q : Type u} {O : Type v} {F : Set (Q → ℝ)}
    {err : (Q → ℝ) → O → ℝ} {ε : ℝ} (hne : ∃ T, IsExactValueSolvable Q O F err ε T) :
    IsExactValueSolvable Q O F err ε (exactValueComplexity Q O F err ε) :=
  Nat.sInf_mem (s := {T : ℕ | IsExactValueSolvable Q O F err ε T}) hne

theorem exactValueComplexity_le {Q : Type u} {O : Type v} {F : Set (Q → ℝ)}
    {err : (Q → ℝ) → O → ℝ} {ε : ℝ} {T : ℕ} (h : IsExactValueSolvable Q O F err ε T) :
    exactValueComplexity Q O F err ε ≤ T :=
  Nat.sInf_le (s := {T : ℕ | IsExactValueSolvable Q O F err ε T}) h

theorem le_exactValueComplexity_of_nonempty {Q : Type u} {O : Type v} {F : Set (Q → ℝ)}
    {err : (Q → ℝ) → O → ℝ} {ε : ℝ} {B : ℕ} (hne : ∃ T, IsExactValueSolvable Q O F err ε T)
    (hfail : ∀ T < B, ¬ IsExactValueSolvable Q O F err ε T) :
    B ≤ exactValueComplexity Q O F err ε :=
  le_csInf (s := {T : ℕ | IsExactValueSolvable Q O F err ε T}) hne
    fun T hT ↦ not_lt.mp fun hlt ↦ hfail T hlt hT

/-- Every uniformly `L`-Lipschitz class (`L ≥ 0`) on a nonempty compact pseudometric domain is
`ε`-solvable (`ε > 0`) in finitely many exact value queries. -/
theorem exists_isExactValueSolvable_of_compact_lipschitz {D : Type u} [PseudoMetricSpace D]
    [CompactSpace D] [Nonempty D] (F : Set (D → ℝ)) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hLip : ∀ f ∈ F, ∀ x y : D, |f x - f y| ≤ L * dist x y) :
    ∃ T : ℕ, IsExactValueSolvable D D F (fun f x ↦ f x - sInf (f '' univ)) ε T := by
  classical
  let δ : ℝ := ε / (2 * (L + 1))
  obtain ⟨t, _, ht_fin, ht_cov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_univ : IsCompact (univ : Set D)).totallyBounded δ (by positivity)
  let s : Finset D := ht_fin.toFinset
  cases hlist : s.toList with
  | nil =>
    obtain ⟨x₀⟩ := ‹Nonempty D›
    obtain ⟨y, hyt, _⟩ := mem_iUnion₂.mp (ht_cov (mem_univ x₀))
    have hyl : y ∈ s.toList := Finset.mem_toList.mpr (ht_fin.mem_toFinset.mpr hyt)
    rw [hlist] at hyl
    exact False.elim (List.not_mem_nil hyl)
  | cons x₀ xs =>
    refine ⟨(x₀ :: xs).length, DetValueAlg.evalMin id x₀ xs, fun f hf ↦ ?_⟩
    have hcont : Continuous f := Metric.continuous_iff.mpr fun x γ hγ ↦
      ⟨γ / (L + 1), by positivity, fun y hy ↦ by
        rw [Real.dist_eq]
        calc |f y - f x| ≤ L * dist y x := hLip f hf y x
          _ ≤ (L + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
          _ < (L + 1) * (γ / (L + 1)) := mul_lt_mul_of_pos_left hy (by positivity)
          _ = γ := mul_div_cancel₀ γ (by positivity)⟩
    have hcpt : IsCompact (f '' univ) := isCompact_univ.image hcont
    obtain ⟨_, ⟨xmin, _, rfl⟩, hmin⟩ := hcpt.exists_isMinOn (univ_nonempty.image f) continuousOn_id
    have hinf : sInf (f '' univ) = f xmin :=
      le_antisymm (csInf_le hcpt.bddBelow ⟨xmin, mem_univ xmin, rfl⟩)
        (le_csInf (univ_nonempty.image f) fun _ ⟨y, _, hy⟩ ↦ hy ▸ hmin ⟨y, mem_univ y, rfl⟩)
    obtain ⟨y, hyt, hyb⟩ := mem_iUnion₂.mp (ht_cov (mem_univ xmin))
    have hyl : y ∈ x₀ :: xs := by rw [← hlist, Finset.mem_toList]; exact ht_fin.mem_toFinset.mpr hyt
    have hsel := (DetValueAlg.evalMin_spec id x₀ xs f).2 y hyl
    have hdy : dist y xmin < δ := by simpa only [Metric.mem_ball, dist_comm] using hyb
    have hgap : f y - f xmin ≤ ε :=
      calc f y - f xmin ≤ |f y - f xmin| := le_abs_self _
        _ ≤ L * dist y xmin := hLip f hf y xmin
        _ ≤ (L + 1) * δ := mul_le_mul (by linarith) hdy.le dist_nonneg (by positivity)
        _ = ε / 2 := by dsimp only [δ]; field_simp [show (L + 1 : ℝ) ≠ 0 by positivity]
        _ ≤ ε := by linarith
    dsimp only [id_eq] at hsel ⊢
    rw [hinf]
    linarith

/-! ### Exact `2 ^ n * ℓ` multiplicative query-complexity amplification on `[0, 1]^n × Y` -/

/-- Fractional hypercube `[0, 1]^n` represented as a subtype of `Fin n → ℝ`. -/
@[expose]
def UnitHypercube (n : ℕ) : Type :=
  {x : Fin n → ℝ // ∀ k : Fin n, x k ∈ Icc (0 : ℝ) 1}

/-- Canonical vertex embedding `{0, 1}^n → [0, 1]^n`. -/
def boolVertex {n : ℕ} (z : Fin n → Bool) : UnitHypercube n :=
  ⟨fun k ↦ if z k then 1 else 0, fun k ↦ by cases hk : z k <;> simp [hk]⟩

/-- Vertex-isolating affine penalty `φ_z(x) := ∑_k (if z_k then 1 - x_k else x_k)` on `[0, 1]^n`. -/
def hypercubePenalty {n : ℕ} (z : Fin n → Bool) (x : UnitHypercube n) : ℝ :=
  ∑ k : Fin n, if z k then 1 - x.val k else x.val k

theorem hypercubePenalty_boolVertex {n : ℕ} (z : Fin n → Bool) :
    hypercubePenalty z (boolVertex z) = 0 :=
  Finset.sum_eq_zero fun k _ ↦ by cases hk : z k <;> simp [boolVertex, hk]

theorem one_le_hypercubePenalty_add {n : ℕ} {z₁ z₂ : Fin n → Bool} (hne : z₁ ≠ z₂)
    (x : UnitHypercube n) : 1 ≤ hypercubePenalty z₁ x + hypercubePenalty z₂ x := by
  have hex : ∃ k : Fin n, z₁ k ≠ z₂ k := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  obtain ⟨k₀, hk₀⟩ := hex
  rw [hypercubePenalty, hypercubePenalty, ← Finset.sum_add_distrib]
  have hnn : ∀ k : Fin n,
      0 ≤ (if z₁ k then 1 - x.val k else x.val k) + (if z₂ k then 1 - x.val k else x.val k) :=
    fun k ↦ by have hk := x.property k; cases z₁ k <;> cases z₂ k <;> simp <;> linarith [hk.1, hk.2]
  have hk₀_eq :
      (if z₁ k₀ then 1 - x.val k₀ else x.val k₀) + (if z₂ k₀ then 1 - x.val k₀ else x.val k₀) =
        1 := by
    cases h1 : z₁ k₀ <;> cases h2 : z₂ k₀ <;> simp_all
  exact hk₀_eq.symm.trans_le (Finset.single_le_sum (fun k _ ↦ hnn k) (Finset.mem_univ k₀))

/-- Fractional extension gluing `2 ^ n` fiber functions `h : (Fin n → Bool) → Y → ℝ` across
`[0, 1]^n × Y` via `F(x, y) = max(m*, max_z (h_z(y) - S₀ * φ_z(x)))`; preserves convexity in
`(x, y)` whenever every `h_z` is convex on a convex domain `Y`, and matches `h_z` identically on
each Boolean fiber `(boolVertex z, y)`. -/
noncomputable def hypercubeGluedObj {n : ℕ} {Y : Type u} (mStar S₀ : ℝ)
    (h : (Fin n → Bool) → Y → ℝ) (p : UnitHypercube n × Y) : ℝ :=
  max mStar <| Finset.univ.sup' Finset.univ_nonempty
    fun z : Fin n → Bool ↦ h z p.2 - S₀ * hypercubePenalty z p.1

theorem hypercubeGluedObj_boolVertex {n : ℕ} {Y : Type u} {mStar B S₀ : ℝ}
    (hS₀ : 2 * B + 2 ≤ S₀) {h : (Fin n → Bool) → Y → ℝ}
    (hlo : ∀ z y, mStar ≤ h z y) (hhi : ∀ z y, h z y ≤ mStar + B) (z : Fin n → Bool) (y : Y) :
    hypercubeGluedObj mStar S₀ h (boolVertex z, y) = h z y := by
  refine le_antisymm ?_ ?_
  · refine max_le (hlo z y) ((Finset.sup'_le_iff Finset.univ_nonempty _).mpr fun z' _ ↦ ?_)
    by_cases hzz : z' = z
    · subst hzz; simp [hypercubePenalty_boolVertex]
    · have hpen : 1 ≤ hypercubePenalty z' (boolVertex z) := by
        have h1 := one_le_hypercubePenalty_add hzz (boolVertex z)
        rwa [hypercubePenalty_boolVertex, add_zero] at h1
      have hB : 0 ≤ B := by linarith [hlo z y, hhi z y]
      have hmul : S₀ ≤ S₀ * hypercubePenalty z' (boolVertex z) :=
        le_mul_of_one_le_right (by linarith) hpen
      linarith [hhi z' y, hlo z y]
  · have hmem : h z y ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun z' : Fin n → Bool ↦ h z' y - S₀ * hypercubePenalty z' (boolVertex z)) := by
      simpa only [hypercubePenalty_boolVertex, mul_zero, sub_zero] using
        Finset.le_sup'
          (f := fun z' : Fin n → Bool ↦ h z' y - S₀ * hypercubePenalty z' (boolVertex z))
          (Finset.mem_univ z)
    exact hmem.trans (le_max_right _ _)

/-- **Exact `2 ^ n * ℓ` multiplicative query-complexity amplification over `[0, 1]^n × Y`**: let `I`
be a family of bounded functions `g : Y → ℝ` all taking values in `[m*, m* + M]` and achieving
minimum value `m*` on `Y`, such that no deterministic exact-value algorithm of budget `< ℓ` solves
`I` within additive error `ε > 0`. Let `F_glued` consist of all extensions
`hypercubeGluedObj m* S₀ h` whose Boolean fibers `h_z` are either in `I` or of the floor-raised form
`y ↦ max (m* + ε + δ) (g y)` (`g ∈ I`, `0 < δ < 1`). Then no deterministic exact-value algorithm
querying arbitrary fractional points of `[0, 1]^n × Y` with fewer than `2 ^ n * ℓ` queries solves
`F_glued` on `{0, 1}^n × Y` within additive error `ε`. -/
theorem two_pow_mul_le_exactValueComplexity_hypercube {Y : Type u} [Nonempty Y] (n : ℕ)
    {mStar M ε : ℝ} (hε : 0 < ε) (I : Set (Y → ℝ))
    (hI_range : ∀ g ∈ I, ∀ y : Y, mStar ≤ g y ∧ g y ≤ mStar + M)
    (hI_min : ∀ g ∈ I, ∃ yStar : Y, g yStar = mStar)
    {ℓ : ℕ} (hI_hard : ∀ T < ℓ, ¬ IsExactValueSolvable Y Y I (fun g y ↦ g y - mStar) ε T) :
    let B := max M (ε + 1)
    let S₀ := 2 * B + 2
    let FiberOk (hz : Y → ℝ) : Prop :=
      hz ∈ I ∨ ∃ g ∈ I, ∃ δ ∈ Ioo (0 : ℝ) 1, hz = fun y ↦ max (mStar + ε + δ) (g y)
    let Fglued : Set (UnitHypercube n × Y → ℝ) :=
      {F | ∃ h : (Fin n → Bool) → Y → ℝ, (∀ z, FiberOk (h z)) ∧ F = hypercubeGluedObj mStar S₀ h}
    let errMI (F : UnitHypercube n × Y → ℝ) (out : (Fin n → Bool) × Y) : ℝ :=
      F (boolVertex out.1, out.2) -
        sInf (range fun p : (Fin n → Bool) × Y ↦ F (boolVertex p.1, p.2))
    ∀ T < 2 ^ n * ℓ,
      ¬ IsExactValueSolvable (UnitHypercube n × Y) ((Fin n → Bool) × Y) Fglued errMI ε T := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ_pos
  · intro _ _ _ _ _ T hT; simp at hT
  have hI_ne : I.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    exact hI_hard 0 hℓ_pos ⟨.halt (Classical.arbitrary Y), by simp [hemp]⟩
  set B : ℝ := max M (ε + 1)
  have hB_pos : 0 < B := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  set S₀ : ℝ := 2 * B + 2
  have hS₀_pos : 0 < S₀ := by linarith
  let FiberOk (hz : Y → ℝ) : Prop :=
    hz ∈ I ∨ ∃ g ∈ I, ∃ δ ∈ Ioo (0 : ℝ) 1, hz = fun y ↦ max (mStar + ε + δ) (g y)
  have hfib_bdd : ∀ {hz}, FiberOk hz → ∀ y, mStar ≤ hz y ∧ hz y ≤ mStar + B := by
    rintro hz (hg | ⟨g, hg, δ, hδ, rfl⟩) y
    · exact ⟨(hI_range hz hg y).1, by linarith [(hI_range hz hg y).2, le_max_left M (ε + 1)]⟩
    · exact ⟨(hI_range g hg y).1.trans (le_max_right _ _),
        max_le (by linarith [hδ.2, le_max_right M (ε + 1)])
          (by linarith [(hI_range g hg y).2, le_max_left M (ε + 1)])⟩
  -- Adversary tracks per-fiber remaining budget `rem z : ℕ`, surviving unsolvable set `S z ⊆ I`,
  -- active query list `(y, v)` with `g y = v > m* + ε`, and inactive list `(x, y)` with `S₀ φ_z x >
  -- ε` and `g y ≤ m* + S₀ φ_z x` (plus optional frozen `(g₀, δ)` when `rem z = 0`).
  let Inv (rem : (Fin n → Bool) → ℕ) (S : (Fin n → Bool) → Set (Y → ℝ))
      (act : (Fin n → Bool) → List (Y × ℝ)) (inact : (Fin n → Bool) → List (UnitHypercube n × Y))
      (frz : (Fin n → Bool) → Option ((Y → ℝ) × ℝ)) : Prop :=
    ∀ z, match frz z with
      | some (g₀, δ) => rem z = 0 ∧ g₀ ∈ I ∧ δ ∈ Ioo (0 : ℝ) 1
      | none =>
        1 ≤ rem z ∧ S z ⊆ I ∧
        ¬ IsExactValueSolvable Y Y (S z) (fun g y ↦ g y - mStar) ε (rem z - 1) ∧
        (∀ e ∈ act z, mStar + ε < e.2 ∧ ∀ g ∈ S z, g e.1 = e.2) ∧
        (∀ p ∈ inact z, ε < S₀ * hypercubePenalty z p.1 ∧
          ∀ g ∈ S z, g p.2 ≤ mStar + S₀ * hypercubePenalty z p.1)
  let Compat (rem : (Fin n → Bool) → ℕ) (S : (Fin n → Bool) → Set (Y → ℝ))
      (act : (Fin n → Bool) → List (Y × ℝ)) (inact : (Fin n → Bool) → List (UnitHypercube n × Y))
      (frz : (Fin n → Bool) → Option ((Y → ℝ) × ℝ)) (h : (Fin n → Bool) → Y → ℝ) : Prop :=
    ∀ z, FiberOk (h z) ∧ match frz z with
      | some (g₀, δ) => h z = fun y ↦ max (mStar + ε + δ) (g₀ y)
      | none => h z ∈ S z ∨ ∃ g₀ ∈ S z, ∃ δ ∈ Ioo (0 : ℝ) 1,
          (h z = fun y ↦ max (mStar + ε + δ) (g₀ y)) ∧
          (∀ e ∈ act z, mStar + ε + δ ≤ e.2) ∧
          (∀ p ∈ inact z, mStar + ε + δ ≤ mStar + S₀ * hypercubePenalty z p.1)
  have hpick_delta : ∀ (z : Fin n → Bool) (aL : List (Y × ℝ)) (iL : List (UnitHypercube n × Y)),
      (∀ e ∈ aL, mStar + ε < e.2) → (∀ p ∈ iL, ε < S₀ * hypercubePenalty z p.1) →
      ∃ δ ∈ Ioo (0 : ℝ) 1,
        (∀ e ∈ aL, mStar + ε + δ ≤ e.2) ∧
        (∀ p ∈ iL, mStar + ε + δ ≤ mStar + S₀ * hypercubePenalty z p.1) := by
    intro z aL iL ha hi
    let fA : List (Y × ℝ) → ℝ := fun l ↦ l.foldr (fun e r ↦ min r ((e.2 - (mStar + ε)) / 2)) (1 / 2)
    let fI : List (UnitHypercube n × Y) → ℝ :=
      fun l ↦ l.foldr (fun p r ↦ min r ((S₀ * hypercubePenalty z p.1 - ε) / 2)) (1 / 2)
    have hA : ∀ l, (∀ e ∈ l, mStar + ε < e.2) →
        0 < fA l ∧ fA l ≤ 1 / 2 ∧ ∀ e ∈ l, mStar + ε + fA l ≤ e.2 := by
      intro l hl; induction l with
      | nil => exact ⟨by dsimp [fA]; norm_num, le_rfl, by simp⟩
      | cons e es ih =>
        obtain ⟨hp, hle, hall⟩ := ih fun e' h' ↦ hl e' (List.mem_cons_of_mem e h')
        have he := hl e List.mem_cons_self
        have hstep : fA (e :: es) = min (fA es) ((e.2 - (mStar + ε)) / 2) := rfl
        rw [hstep]
        refine ⟨lt_min hp (by linarith), (min_le_left _ _).trans hle, fun e' h' ↦ ?_⟩
        rcases List.mem_cons.mp h' with h_eq | hm
        · rw [h_eq]; linarith [min_le_right (fA es) ((e.2 - (mStar + ε)) / 2)]
        · linarith [min_le_left (fA es) ((e.2 - (mStar + ε)) / 2), hall e' hm]
    have hI : ∀ l, (∀ p ∈ l, ε < S₀ * hypercubePenalty z p.1) →
        0 < fI l ∧ ∀ p ∈ l, mStar + ε + fI l ≤ mStar + S₀ * hypercubePenalty z p.1 := by
      intro l hl; induction l with
      | nil => exact ⟨by dsimp [fI]; norm_num, by simp⟩
      | cons p ps ih =>
        obtain ⟨hp, hall⟩ := ih fun p' h' ↦ hl p' (List.mem_cons_of_mem p h')
        have hpe := hl p List.mem_cons_self
        have hstep : fI (p :: ps) = min (fI ps) ((S₀ * hypercubePenalty z p.1 - ε) / 2) := rfl
        rw [hstep]
        refine ⟨lt_min hp (by linarith), fun p' h' ↦ ?_⟩
        rcases List.mem_cons.mp h' with h_eq | hm
        · rw [h_eq]; linarith [min_le_right (fI ps) ((S₀ * hypercubePenalty z p.1 - ε) / 2)]
        · linarith [min_le_left (fI ps) ((S₀ * hypercubePenalty z p.1 - ε) / 2), hall p' hm]
    obtain ⟨hAp, hAh, hAle⟩ := hA aL ha
    obtain ⟨hIp, hIle⟩ := hI iL hi
    exact ⟨min (fA aL) (fI iL),
      ⟨lt_min hAp hIp, ((min_le_left _ _).trans hAh).trans_lt (by norm_num)⟩,
      fun e he ↦ by linarith [min_le_left (fA aL) (fI iL), hAle e he],
      fun p hp ↦ by linarith [min_le_right (fA aL) (fI iL), hIle p hp]⟩
  have hne_unsolv : ∀ {U : Set (Y → ℝ)} {k : ℕ},
      ¬ IsExactValueSolvable Y Y U (fun g y ↦ g y - mStar) ε k → U.Nonempty := fun hnot ↦ by
    by_contra he; rw [not_nonempty_iff_eq_empty] at he
    exact hnot ⟨.halt (Classical.arbitrary Y), by simp [he]⟩
  have hadv : ∀ {T : ℕ} (alg : DetValueAlg (UnitHypercube n × Y) ((Fin n → Bool) × Y) T)
      (rem S act inact frz), Inv rem S act inact frz → T < (∑ z, rem z) →
      ∃ h, Compat rem S act inact frz h ∧
        ε < hypercubeGluedObj mStar S₀ h
            (boolVertex (alg.run (hypercubeGluedObj mStar S₀ h)).1,
              (alg.run (hypercubeGluedObj mStar S₀ h)).2) -
          sInf (range fun p : (Fin n → Bool) × Y ↦
            hypercubeGluedObj mStar S₀ h (boolVertex p.1, p.2)) := by
    intro T alg
    induction alg with
    | halt out =>
      intro rem S act inact frz hinv hpot
      obtain ⟨zAct, _, hzAct⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt (Nat.zero_lt_of_lt hpot))
      have hunraised : ∃ zStar gStar, frz zStar = none ∧ gStar ∈ S zStar ∧ gStar ∈ I ∧
          (out.1 = zStar → mStar + ε < gStar out.2) := by
        cases hfo : frz out.1 with
        | none =>
          have hv := hinv out.1; rw [hfo] at hv
          have hex : ∃ g ∈ S out.1, mStar + ε < g out.2 := by
            by_contra hall; push Not at hall
            exact hv.2.2.1 ⟨.halt out.2, fun g hg ↦ by
              simp only [DetValueAlg.run_halt]; linarith [hall g hg]⟩
          obtain ⟨gStar, hgS, hgt⟩ := hex
          exact ⟨out.1, gStar, hfo, hgS, hv.2.1 hgS, fun _ ↦ hgt⟩
        | some gd =>
          cases hfa : frz zAct with
          | some gd' => have hv := hinv zAct; rw [hfa] at hv; exact False.elim (hzAct hv.1)
          | none =>
            have hv := hinv zAct; rw [hfa] at hv
            obtain ⟨gStar, hgS⟩ := hne_unsolv hv.2.2.1
            exact ⟨zAct, gStar, hfa, hgS, hv.2.1 hgS,
              fun he ↦ by subst he; rw [hfo] at hfa; cases hfa⟩
      obtain ⟨zStar, gStar, hfzS, hgSS, hgSI, hout_case⟩ := hunraised
      have hfrz_other : ∀ z, z ≠ zStar → ∃ g₀ ∈ I, ∃ δ ∈ Ioo (0 : ℝ) 1,
          match frz z with
            | some (g', δ') => g₀ = g' ∧ δ = δ'
            | none => g₀ ∈ S z ∧ (∀ e ∈ act z, mStar + ε + δ ≤ e.2) ∧
                ∀ p ∈ inact z, mStar + ε + δ ≤ mStar + S₀ * hypercubePenalty z p.1 := by
        intro z _
        cases hfz : frz z with
        | some gd =>
          have hv := hinv z; rw [hfz] at hv
          exact ⟨gd.1, hv.2.1, gd.2, hv.2.2, rfl, rfl⟩
        | none =>
          have hv := hinv z; rw [hfz] at hv
          obtain ⟨g₀, hg₀⟩ := hne_unsolv hv.2.2.1
          obtain ⟨δ, hδ, ha, hi⟩ := hpick_delta z (act z) (inact z)
            (fun e he ↦ (hv.2.2.2.1 e he).1) (fun p hp ↦ (hv.2.2.2.2 p hp).1)
          exact ⟨g₀, hv.2.1 hg₀, δ, hδ, hg₀, ha, hi⟩
      let mkOther (z : Fin n → Bool) (hzz : z ≠ zStar) : Y → ℝ :=
        let g₀ := (hfrz_other z hzz).choose
        let δ := (hfrz_other z hzz).choose_spec.2.choose
        fun y ↦ max (mStar + ε + δ) (g₀ y)
      let h (z : Fin n → Bool) : Y → ℝ := if hzz : z = zStar then gStar else mkOther z hzz
      have hcomp : Compat rem S act inact frz h := fun z ↦ by
        by_cases hzz : z = zStar
        · subst hzz
          simp only [h, ↓reduceDIte, hfzS]
          exact ⟨Or.inl hgSI, Or.inl hgSS⟩
        · simp only [h, hzz, ↓reduceDIte]
          set g₀ : Y → ℝ := (hfrz_other z hzz).choose
          have hg₀I : g₀ ∈ I := (hfrz_other z hzz).choose_spec.1
          set δ : ℝ := (hfrz_other z hzz).choose_spec.2.choose
          have hδ : δ ∈ Ioo (0 : ℝ) 1 := (hfrz_other z hzz).choose_spec.2.choose_spec.1
          have hm : (match frz z with
              | some (g', δ') => g₀ = g' ∧ δ = δ'
              | none => g₀ ∈ S z ∧ (∀ e ∈ act z, mStar + ε + δ ≤ e.2) ∧
                  ∀ p ∈ inact z, mStar + ε + δ ≤ mStar + S₀ * hypercubePenalty z p.1) :=
            (hfrz_other z hzz).choose_spec.2.choose_spec.2
          refine ⟨Or.inr ⟨g₀, hg₀I, δ, hδ, rfl⟩, ?_⟩
          cases hfz : frz z with
          | some gd => rw [hfz] at hm; dsimp only [mkOther]; rw [← hm.1, ← hm.2]
          | none => rw [hfz] at hm; exact Or.inr ⟨g₀, hm.1, δ, hδ, rfl, hm.2.1, hm.2.2⟩
      have hlo : ∀ z y, mStar ≤ h z y := fun z y ↦ (hfib_bdd (hcomp z).1 y).1
      have hhi : ∀ z y, h z y ≤ mStar + B := fun z y ↦ (hfib_bdd (hcomp z).1 y).2
      obtain ⟨yStar, hyStar⟩ := hI_min gStar hgSI
      have hinf : sInf (range fun p : (Fin n → Bool) × Y ↦
          hypercubeGluedObj mStar S₀ h (boolVertex p.1, p.2)) = mStar := by
        have hval : hypercubeGluedObj mStar S₀ h (boolVertex zStar, yStar) = mStar := by
          rw [hypercubeGluedObj_boolVertex le_rfl hlo hhi]; simp [h, hyStar]
        exact le_antisymm
          (csInf_le ⟨mStar, by rintro _ ⟨_, rfl⟩; exact le_max_left _ _⟩ ⟨(zStar, yStar), hval⟩)
          (le_csInf ⟨mStar, (zStar, yStar), hval⟩ fun _ ⟨_, he⟩ ↦ he ▸ le_max_left _ _)
      refine ⟨h, hcomp, ?_⟩
      rw [DetValueAlg.run_halt, hinf, hypercubeGluedObj_boolVertex le_rfl hlo hhi]
      by_cases hzz : out.1 = zStar
      · simp only [h, hzz, ↓reduceDIte]; linarith [hout_case hzz]
      · simp only [h, hzz, ↓reduceDIte, mkOther]
        have hδ := (hfrz_other out.1 hzz).choose_spec.2.choose_spec.1
        linarith [hδ.1, le_max_left (mStar + ε + (hfrz_other out.1 hzz).choose_spec.2.choose)
          ((hfrz_other out.1 hzz).choose out.2)]
    | @query T' pt next ih =>
      intro rem S act inact frz hinv hpot
      have hval_cone : ∀ {h : (Fin n → Bool) → Y → ℝ} {z₀},
          (∀ z, FiberOk (h z)) → hypercubePenalty z₀ pt.1 < 1 / 2 →
          hypercubeGluedObj mStar S₀ h pt =
            max mStar (h z₀ pt.2 - S₀ * hypercubePenalty z₀ pt.1) := by
        intro h z₀ hok hz₀
        refine le_antisymm
          (max_le (le_max_left _ _) ((Finset.sup'_le_iff Finset.univ_nonempty _).mpr fun z' _ ↦ ?_))
          (max_le (le_max_left _ _) ((Finset.le_sup'
            (fun z' : Fin n → Bool ↦ h z' pt.2 - S₀ * hypercubePenalty z' pt.1)
            (Finset.mem_univ z₀)).trans (le_max_right _ _)))
        by_cases hzz : z' = z₀
        · subst hzz; exact le_max_right _ _
        · have hp : 1 / 2 < hypercubePenalty z' pt.1 := by
            linarith [one_le_hypercubePenalty_add hzz pt.1]
          have hm : S₀ * (1 / 2) < S₀ * hypercubePenalty z' pt.1 :=
            mul_lt_mul_of_pos_left hp hS₀_pos
          exact (show h z' pt.2 - S₀ * hypercubePenalty z' pt.1 ≤ mStar by
            linarith [(hfib_bdd (hok z') pt.2).2]).trans (le_max_left _ _)
      by_cases hcone : ∃ z₀ : Fin n → Bool, hypercubePenalty z₀ pt.1 < 1 / 2
      · obtain ⟨z₀, hz₀⟩ := hcone
        cases hfz₀ : frz z₀ with
        | some gd =>
          let ans := max mStar (max (mStar + ε + gd.2) (gd.1 pt.2) - S₀ * hypercubePenalty z₀ pt.1)
          obtain ⟨h, hc, hgt⟩ := ih ans rem S act inact frz hinv
            ((Nat.lt_succ_self T').trans hpot)
          have hhz := (hc z₀).2; rw [hfz₀] at hhz
          have hfp : hypercubeGluedObj mStar S₀ h pt = ans := by
            rw [hval_cone (fun z ↦ (hc z).1) hz₀, hhz]
          exact ⟨h, hc, by simpa only [DetValueAlg.run_query, hfp] using hgt⟩
        | none =>
          have hv := hinv z₀; rw [hfz₀] at hv
          obtain ⟨hrem1, hSsub, hunsolv, haInv, hiInv⟩ := hv
          have hpot_drop : ∀ r', r' + 1 = rem z₀ →
              T' < ∑ z, Function.update rem z₀ r' z := fun r' hr' ↦ by
            have hsum : (∑ z, rem z) = (∑ z, Function.update rem z₀ r' z) + 1 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z₀),
                ← Finset.add_sum_erase _ (Function.update rem z₀ r') (Finset.mem_univ z₀)]
              simp only [Function.update_self]
              have hrest : ∑ z ∈ Finset.univ.erase z₀, rem z =
                  ∑ z ∈ Finset.univ.erase z₀, Function.update rem z₀ r' z :=
                Finset.sum_congr rfl fun z hz ↦
                  (Function.update_of_ne (Finset.ne_of_mem_erase hz) ..).symm
              omega
            omega
          by_cases hrem2 : 2 ≤ rem z₀
          · -- Query `pt.2` in the single-fiber game: some real response `v₀` stays unsolvable!
            have hex_v : ∃ v₀ : ℝ, ¬ IsExactValueSolvable Y Y {g ∈ S z₀ | g pt.2 = v₀}
                (fun g y ↦ g y - mStar) ε (rem z₀ - 2) := by
              by_contra hall; push Not at hall
              have hk : (rem z₀ - 2) + 1 = rem z₀ - 1 := by omega
              let comb : DetValueAlg Y Y ((rem z₀ - 2) + 1) :=
                .query pt.2 fun v ↦ (hall v).choose
              refine hunsolv ⟨comb.castLe hk.le, fun g hg ↦ ?_⟩
              simpa only [comb, DetValueAlg.run_castLe, DetValueAlg.run_query] using
                (hall (g pt.2)).choose_spec g ⟨hg, rfl⟩
            obtain ⟨v₀, hv₀_un⟩ := hex_v
            -- Cannot have `v₀ ≤ mStar + ε` (else halting at `pt.2` solves `{g | g pt.2 = v₀}`).
            have hv₀_gt : mStar + ε < v₀ := by
              by_contra hle; push Not at hle
              exact hv₀_un ⟨.halt pt.2, fun g hg ↦ by
                simp only [DetValueAlg.run_halt]; linarith [hg.2]⟩
            let S' := {g ∈ S z₀ | g pt.2 = v₀}
            let rem' := Function.update rem z₀ (rem z₀ - 1)
            let Smap' := Function.update S z₀ S'
            rcases le_or_gt v₀ (mStar + S₀ * hypercubePenalty z₀ pt.1) with hv_floor | hv_act
            · have hpen_gt : ε < S₀ * hypercubePenalty z₀ pt.1 := by linarith
              let inact' := Function.update inact z₀ (pt :: inact z₀)
              have hinv' : Inv rem' Smap' act inact' frz := fun z ↦ by
                by_cases hzz : z = z₀
                · subst hzz
                  simp only [hfz₀, rem', Smap', inact', Function.update_self,
                    show rem z - 1 - 1 = rem z - 2 by omega]
                  refine ⟨by omega, fun g hg ↦ hSsub hg.1, hv₀_un,
                    fun e he ↦ ⟨(haInv e he).1, fun g hg ↦ (haInv e he).2 g hg.1⟩, fun p hp ↦ ?_⟩
                  rcases List.mem_cons.mp hp with rfl | hm
                  · exact ⟨hpen_gt, fun g hg ↦ hg.2.symm ▸ hv_floor⟩
                  · exact ⟨(hiInv p hm).1, fun g hg ↦ (hiInv p hm).2 g hg.1⟩
                · simpa only [rem', Smap', inact', Function.update_of_ne hzz] using hinv z
              obtain ⟨h, hc, hgt⟩ := ih mStar rem' Smap' act inact' frz hinv'
                (hpot_drop (rem z₀ - 1) (by omega))
              have hfp : hypercubeGluedObj mStar S₀ h pt = mStar := by
                rw [hval_cone (fun z ↦ (hc z).1) hz₀, max_eq_left]
                have hc₀ := (hc z₀).2
                simp only [hfz₀, Smap', inact', Function.update_self] at hc₀
                rcases hc₀ with hg | ⟨g₀, hg₀, δ, _, hze, _, hi'⟩
                · linarith [hg.2, hv_floor]
                · rw [hze]
                  have hmax : max (mStar + ε + δ) (g₀ pt.2) ≤
                      mStar + S₀ * hypercubePenalty z₀ pt.1 :=
                    max_le (hi' pt List.mem_cons_self) (hg₀.2.symm ▸ hv_floor)
                  linarith
              have hcold : Compat rem S act inact frz h := fun z ↦ by
                by_cases hzz : z = z₀
                · subst hzz
                  have hcz := hc z
                  simp only [hfz₀, Smap', inact', Function.update_self] at hcz ⊢
                  refine ⟨hcz.1, ?_⟩
                  rcases hcz.2 with hg | ⟨g₀, hg₀, δ, hδ, hze, ha', hi'⟩
                  · exact Or.inl hg.1
                  · exact Or.inr ⟨g₀, hg₀.1, δ, hδ, hze, ha',
                      fun p hp ↦ hi' p (List.mem_cons_of_mem pt hp)⟩
                · simpa only [rem', Smap', inact', Function.update_of_ne hzz] using hc z
              exact ⟨h, hcold, by simpa only [DetValueAlg.run_query, hfp] using hgt⟩
            · let act' := Function.update act z₀ ((pt.2, v₀) :: act z₀)
              let ans := v₀ - S₀ * hypercubePenalty z₀ pt.1
              have hinv' : Inv rem' Smap' act' inact frz := fun z ↦ by
                by_cases hzz : z = z₀
                · subst hzz
                  simp only [hfz₀, rem', Smap', act', Function.update_self,
                    show rem z - 1 - 1 = rem z - 2 by omega]
                  refine ⟨by omega, fun g hg ↦ hSsub hg.1, hv₀_un, fun e he ↦ ?_,
                    fun p hp ↦ ⟨(hiInv p hp).1, fun g hg ↦ (hiInv p hp).2 g hg.1⟩⟩
                  rcases List.mem_cons.mp he with rfl | hm
                  · exact ⟨hv₀_gt, fun g hg ↦ hg.2⟩
                  · exact ⟨(haInv e hm).1, fun g hg ↦ (haInv e hm).2 g hg.1⟩
                · simpa only [rem', Smap', act', Function.update_of_ne hzz] using hinv z
              obtain ⟨h, hc, hgt⟩ := ih ans rem' Smap' act' inact frz hinv'
                (hpot_drop (rem z₀ - 1) (by omega))
              have hfp : hypercubeGluedObj mStar S₀ h pt = ans := by
                rw [hval_cone (fun z ↦ (hc z).1) hz₀]
                have hc₀ := (hc z₀).2
                simp only [hfz₀, Smap', act', Function.update_self] at hc₀
                have hhz : h z₀ pt.2 = v₀ := by
                  rcases hc₀ with hg | ⟨g₀, hg₀, δ, _, hze, ha', _⟩
                  · exact hg.2
                  · rw [hze]; dsimp only; rw [hg₀.2]
                    exact max_eq_right (ha' (pt.2, v₀) List.mem_cons_self)
                rw [hhz]; exact max_eq_right (by linarith)
              have hcold : Compat rem S act inact frz h := fun z ↦ by
                by_cases hzz : z = z₀
                · subst hzz
                  have hcz := hc z
                  simp only [hfz₀, Smap', act', Function.update_self] at hcz ⊢
                  refine ⟨hcz.1, ?_⟩
                  rcases hcz.2 with hg | ⟨g₀, hg₀, δ, hδ, hze, ha', hi'⟩
                  · exact Or.inl hg.1
                  · exact Or.inr ⟨g₀, hg₀.1, δ, hδ, hze,
                      fun e he ↦ ha' e (List.mem_cons_of_mem _ he), hi'⟩
                · simpa only [rem', Smap', act', Function.update_of_ne hzz] using hc z
              exact ⟨h, hcold, by simpa only [DetValueAlg.run_query, hfp] using hgt⟩
          · -- `rem z₀ = 1`: freeze fiber `z₀`, dropping total budget by `1`.
            have hrem_eq : rem z₀ = 1 := by omega
            obtain ⟨g₀, hg₀⟩ := hne_unsolv hunsolv
            obtain ⟨δ, hδ, ha', hi'⟩ := hpick_delta z₀ (act z₀) (inact z₀)
              (fun e he ↦ (haInv e he).1) (fun p hp ↦ (hiInv p hp).1)
            let rem' := Function.update rem z₀ 0
            let frz' := Function.update frz z₀ (some (g₀, δ))
            let ans := max mStar (max (mStar + ε + δ) (g₀ pt.2) - S₀ * hypercubePenalty z₀ pt.1)
            have hinv' : Inv rem' S act inact frz' := fun z ↦ by
              by_cases hzz : z = z₀
              · subst hzz
                simp only [rem', frz', Function.update_self]
                exact ⟨trivial, hSsub hg₀, hδ⟩
              · simpa only [rem', frz', Function.update_of_ne hzz] using hinv z
            obtain ⟨h, hc, hgt⟩ := ih ans rem' S act inact frz' hinv'
              (hpot_drop 0 (by omega))
            have hhz : h z₀ = fun y ↦ max (mStar + ε + δ) (g₀ y) := by
              have hcz := (hc z₀).2; simpa only [frz', Function.update_self] using hcz
            have hfp : hypercubeGluedObj mStar S₀ h pt = ans := by
              rw [hval_cone (fun z ↦ (hc z).1) hz₀, hhz]
            have hcold : Compat rem S act inact frz h := fun z ↦ by
              by_cases hzz : z = z₀
              · subst hzz
                simp only [hfz₀]
                exact ⟨(hc z).1, Or.inr ⟨g₀, hg₀, δ, hδ, hhz, ha', hi'⟩⟩
              · simpa only [frz', Function.update_of_ne hzz] using hc z
            exact ⟨h, hcold, by simpa only [DetValueAlg.run_query, hfp] using hgt⟩
      · push Not at hcone
        obtain ⟨h, hc, hgt⟩ := ih mStar rem S act inact frz hinv
          ((Nat.lt_succ_self T').trans hpot)
        have hfp : hypercubeGluedObj mStar S₀ h pt = mStar :=
          max_eq_left ((Finset.sup'_le_iff Finset.univ_nonempty _).mpr fun z _ ↦ by
            have hm : S₀ * (1 / 2) ≤ S₀ * hypercubePenalty z pt.1 :=
              mul_le_mul_of_nonneg_left (hcone z) hS₀_pos.le
            linarith [(hfib_bdd (hc z).1 pt.2).2])
        exact ⟨h, hc, by simpa only [DetValueAlg.run_query, hfp] using hgt⟩
  intro _ _ _ _ _ T hT ⟨alg, halg⟩
  have hinv0 : Inv (fun _ ↦ ℓ) (fun _ ↦ I) (fun _ ↦ []) (fun _ ↦ []) (fun _ ↦ none) :=
    fun _ ↦ ⟨hℓ_pos, Subset.rfl, hI_hard (ℓ - 1) (by omega), by simp, by simp⟩
  have hsum0 : (∑ _ : Fin n → Bool, ℓ) = 2 ^ n * ℓ := by
    simp
  obtain ⟨h, hc, hgt⟩ :=
    hadv alg (fun _ ↦ ℓ) (fun _ ↦ I) (fun _ ↦ []) (fun _ ↦ []) (fun _ ↦ none) hinv0 (hsum0 ▸ hT)
  exact not_le_of_gt hgt (halg (hypercubeGluedObj mStar S₀ h) ⟨h, fun z ↦ (hc z).1, rfl⟩)

end CslibFrontier.QueryComplexity
