module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Black-Box Promise-to-Total Query Compilation and Lipschitz Cube Interpolation

This module develops reusable query-complexity combinators over `Cslib.OracleComp` for converting
promise search algorithms into total search algorithms, together with Lipschitz interpolation and
damping reductions on `ℓ_∞` hypercubes under standard Lean axioms.

## Main definitions

* `CslibFrontier.Computability.QueryComplexity.EndoQueryAlg`: deterministic adaptive oracle query
  programs querying a self-map `f : α → α`.
* `CslibFrontier.Computability.QueryComplexity.TotalSearchCertificate`: certificate sum type for
  total search problems over `f : α → α`, returning either a candidate solution `x` or a pair of
  queried inputs `(q₁, q₂)` refuting a pairwise consistency relation.
* `CslibFrontier.Computability.QueryComplexity.runWithQueryLog`: query-logging instrumentation for
  `EndoQueryAlg` preserving worst-case query budgets (`IsQueryBounded`).
* `CslibFrontier.Computability.QueryComplexity.promiseToTotalQueryAlg`: generic black-box compiler
  turning an `m`-query promise algorithm into an `(m + 1)`-query total search algorithm whenever
  consistency with the promise class is characterized by a pairwise input-output relation.
* `CslibFrontier.Computability.QueryComplexity.UnitCube`,
  `CslibFrontier.Computability.QueryComplexity.mcShaneCubeExtension`,
  `CslibFrontier.Computability.QueryComplexity.dampedCubeMap`: the sup-norm hypercube `[0, 1]^k`,
  explicit coordinatewise McShane `L`-Lipschitz extension from finite query transcripts, and
  contractive damping of non-expansive cube maps.

## Main results

* `CslibFrontier.Computability.QueryComplexity.isQueryBounded_promiseToTotalQueryAlg`,
  `CslibFrontier.Computability.QueryComplexity.promiseToTotalQueryAlg_spec`: query-budget bound
  (`m + 1`) and total-search correctness of `promiseToTotalQueryAlg`.
* `CslibFrontier.Computability.QueryComplexity.exists_consistent_lipschitz_cube_iff`: a finite
  family of input-output pairs on `[0, 1]^k` extends to an `L`-Lipschitz self-map (`L ≥ 0`) if and
  only if every pair satisfies `dist (a t₁) (a t₂) ≤ L * dist (q t₁) (q t₂)`.
* `CslibFrontier.Computability.QueryComplexity.lipschitzApproxFixedPt_totalSearch_spec`: compiling
  an `m`-query `ε`-approximate fixed-point solver for `L`-Lipschitz self-maps of `[0, 1]^k` yields
  an `(m + 1)`-query total search algorithm on arbitrary self-maps of `[0, 1]^k`.
* `CslibFrontier.Computability.QueryComplexity.dampedCubeMap_lipschitz`,
  `CslibFrontier.Computability.QueryComplexity.dist_of_dampedCubeMap_approxFixedPt`: damping a
  non-expansive self-map of `[0, 1]^k` produces a `(1 - ε / 2)`-Lipschitz map whose `(ε / 2)`-fixed
  points are `ε`-fixed points of the original map.
* `CslibFrontier.Computability.QueryComplexity.dist_fixedPoint_le_of_approxFixedPt`: in any
  nonempty complete metric space, an `(ε * γ)`-approximate fixed point of a `(1 - γ)`-contraction
  lies within distance `ε` of its unique Banach fixed point.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity

/-! ### Generic Promise-to-Total Query Compiler -/

/-- Deterministic oracle query computation over evaluation queries to a self-map `α → α`. -/
public abbrev EndoQueryAlg (α β : Type) : Type :=
  Cslib.OracleComp (fun _ : α ↦ α) β

/-- Output certificate for a total search problem obtained from a pairwise-testable promise:
either a candidate solution `x`, or a pair of inputs `(q₁, q₂)` witnessing a violation of `R`. -/
public inductive TotalSearchCertificate (α : Type) : Type
  /-- Candidate solution `x` satisfying the target input-output predicate `G x (f x)`. -/
  | solution (x : α) : TotalSearchCertificate α
  /-- Witness pair `(q₁, q₂)` refuting the pairwise relation `R (q₁, f q₁) (q₂, f q₂)`. -/
  | violation (q₁ q₂ : α) : TotalSearchCertificate α

/-- Validity of a `TotalSearchCertificate α` with respect to goal `G` and pairwise relation `R` on
an arbitrary oracle `f : α → α`. -/
@[expose] public def TotalSearchCertificate.IsValid {α : Type}
    (G : α → α → Prop) (R : α × α → α × α → Prop) (f : α → α) :
    TotalSearchCertificate α → Prop
  | .solution x => G x (f x)
  | .violation q₁ q₂ => ¬R (q₁, f q₁) (q₂, f q₂)

/-- Instrument a deterministic `EndoQueryAlg α β` to record all `(query, answer)` pairs. -/
public def runWithQueryLog {α β : Type} :
    EndoQueryAlg α β → List (α × α) → EndoQueryAlg α (β × List (α × α))
  | .pure x, log => pure (x, log)
  | .liftBind q cont, log =>
      Cslib.OracleComp.query q >>= fun ans ↦ runWithQueryLog (cont ans) ((q, ans) :: log)

/-- `runWithQueryLog` preserves worst-case query budgets `IsQueryBounded`. -/
public theorem isQueryBounded_runWithQueryLog {α β : Type} {alg : EndoQueryAlg α β}
    {m : ℕ} (halg : alg.IsQueryBounded m) (log : List (α × α)) :
    (runWithQueryLog alg log).IsQueryBounded m := by
  induction halg generalizing log with
  | pure a n => exact .pure (a, log) n
  | liftBind q cont n _ ih =>
    change Cslib.OracleComp.IsCostBounded _ (Cslib.OracleComp.query q >>= fun ans ↦
      runWithQueryLog (cont ans) ((q, ans) :: log)) (n + 1)
    rw [Nat.add_comm]
    exact (Cslib.OracleComp.IsCostBounded.query q).bind fun ans ↦ ih ans ((q, ans) :: log)

private lemma evalPure_runWithQueryLog_fst {α β : Type}
    (f : α → α) (alg : EndoQueryAlg α β) (log : List (α × α)) :
    (Cslib.OracleComp.evalPure f (runWithQueryLog alg log)).1 =
      Cslib.OracleComp.evalPure f alg := by
  induction alg generalizing log with
  | pure x => rfl
  | liftBind q cont ih => exact ih (f q) ((q, f q) :: log)

private lemma evalPure_runWithQueryLog_consistent {α β : Type}
    (f : α → α) (alg : EndoQueryAlg α β) (log : List (α × α))
    (hlog : ∀ p ∈ log, f p.1 = p.2) :
    ∀ p ∈ (Cslib.OracleComp.evalPure f (runWithQueryLog alg log)).2, f p.1 = p.2 := by
  induction alg generalizing log with
  | pure x => exact hlog
  | liftBind q cont ih =>
    apply ih (f q) ((q, f q) :: log)
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · rfl
    · exact hlog p hmem

private lemma sublog_subset_evalPure_runWithQueryLog {α β : Type}
    (f : α → α) (alg : EndoQueryAlg α β) (log : List (α × α)) :
    ∀ p ∈ log, p ∈ (Cslib.OracleComp.evalPure f (runWithQueryLog alg log)).2 := by
  induction alg generalizing log with
  | pure x => exact fun _ hp ↦ hp
  | liftBind q cont ih =>
    intro p hp
    exact ih (f q) ((q, f q) :: log) p (List.mem_cons_of_mem _ hp)

private lemma evalPure_eq_of_agrees_on_queryLog {α β : Type}
    (f f' : α → α) (alg : EndoQueryAlg α β) (log : List (α × α))
    (hagree : ∀ p ∈ (Cslib.OracleComp.evalPure f (runWithQueryLog alg log)).2, f' p.1 = p.2) :
    Cslib.OracleComp.evalPure f' alg = Cslib.OracleComp.evalPure f alg := by
  induction alg generalizing log with
  | pure x => rfl
  | liftBind q cont ih =>
    have hq_mem : (q, f q) ∈
        (Cslib.OracleComp.evalPure f (runWithQueryLog (cont (f q)) ((q, f q) :: log))).2 :=
      sublog_subset_evalPure_runWithQueryLog f (cont (f q)) ((q, f q) :: log) (q, f q)
        List.mem_cons_self
    have hfq : f' q = f q := hagree (q, f q) hq_mem
    have heval_step : ∀ g : α → α,
        Cslib.OracleComp.evalPure g (.liftBind q cont) =
          Cslib.OracleComp.evalPure g (cont (g q)) := fun _ ↦ rfl
    rw [heval_step f', heval_step f, hfq]
    exact ih (f q) ((q, f q) :: log) hagree

/-- Extract a violating query pair from `fullLog` if one exists, or return `.solution fallback`. -/
public noncomputable def extractPairwiseViolation {α : Type}
    (R : α × α → α × α → Prop) (fallback : α) (fullLog : List (α × α)) :
    TotalSearchCertificate α :=
  @dite _ (∃ p₁ ∈ fullLog, ∃ p₂ ∈ fullLog, ¬R p₁ p₂) (Classical.propDecidable _)
    (fun h ↦
      let p₁ := Classical.choose h
      let hp₁ := Classical.choose_spec h
      let p₂ := Classical.choose hp₁.2
      .violation p₁.1 p₂.1)
    (fun _ ↦ .solution fallback)

/-- Generic black-box promise-to-total query compiler: runs `alg` while logging all queries,
makes one final verification query at the candidate output `x`, and returns either `.solution x`
(if `G x (f x)` holds) or a pair of logged queries violating `R`. -/
public noncomputable def promiseToTotalQueryAlg {α : Type}
    (G : α → α → Prop) (R : α × α → α × α → Prop) (alg : EndoQueryAlg α α) :
    EndoQueryAlg α (TotalSearchCertificate α) :=
  runWithQueryLog alg [] >>= fun res ↦
    Cslib.OracleComp.query res.1 >>= fun fxOut ↦
      @ite _ (G res.1 fxOut) (Classical.propDecidable _)
        (pure (.solution res.1))
        (pure (extractPairwiseViolation R res.1 ((res.1, fxOut) :: res.2)))

/-- `promiseToTotalQueryAlg` uses at most `m + 1` queries when `alg` uses at most `m` queries. -/
public theorem isQueryBounded_promiseToTotalQueryAlg {α : Type}
    (G : α → α → Prop) (R : α × α → α × α → Prop) {alg : EndoQueryAlg α α} {m : ℕ}
    (halg : alg.IsQueryBounded m) :
    (promiseToTotalQueryAlg G R alg).IsQueryBounded (m + 1) := by
  refine (isQueryBounded_runWithQueryLog halg []).bind fun res ↦ ?_
  exact (Cslib.OracleComp.IsCostBounded.query res.1).bind
    (next := fun fxOut ↦
      @ite _ (G res.1 fxOut) (Classical.propDecidable _)
        (pure (TotalSearchCertificate.solution res.1))
        (pure (extractPairwiseViolation R res.1 ((res.1, fxOut) :: res.2))))
    (m := 0) fun fxOut ↦ by
      split_ifs <;> exact .pure _ 0

/-- Soundness of `promiseToTotalQueryAlg`: if every finite query log satisfying `R` pairwise
extends to a promise-satisfying function `f' : α → α` (`P f'`), and `alg` achieves `G` on every
`f'` satisfying `P`, then `promiseToTotalQueryAlg G R alg` outputs a valid total-search
certificate on *every* function `f : α → α`. -/
public theorem promiseToTotalQueryAlg_spec {α : Type}
    {P : (α → α) → Prop} {G : α → α → Prop} {R : α × α → α × α → Prop}
    (hext : ∀ log : List (α × α),
      (∀ p₁ ∈ log, ∀ p₂ ∈ log, R p₁ p₂) → ∃ f' : α → α, P f' ∧ ∀ p ∈ log, f' p.1 = p.2)
    {alg : EndoQueryAlg α α}
    (hsol : ∀ f' : α → α, P f' →
      G (Cslib.OracleComp.evalPure f' alg) (f' (Cslib.OracleComp.evalPure f' alg)))
    (f : α → α) :
    (Cslib.OracleComp.evalPure f (promiseToTotalQueryAlg G R alg)).IsValid G R f := by
  dsimp only [promiseToTotalQueryAlg]
  rw [Cslib.OracleComp.evalPure_bind, Cslib.OracleComp.evalPure_bind,
    Cslib.OracleComp.evalPure_query]
  set res := Cslib.OracleComp.evalPure f (runWithQueryLog alg [])
  have hfst : res.1 = Cslib.OracleComp.evalPure f alg := evalPure_runWithQueryLog_fst f alg []
  have hcons_log : ∀ p ∈ res.2, f p.1 = p.2 :=
    evalPure_runWithQueryLog_consistent f alg [] (fun _ h ↦ False.elim (List.not_mem_nil h))
  split_ifs with hgoal
  · rw [Cslib.OracleComp.evalPure_pure]
    exact hgoal
  · rw [Cslib.OracleComp.evalPure_pure]
    set fullLog := (res.1, f res.1) :: res.2
    have hcons_full : ∀ p ∈ fullLog, f p.1 = p.2 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · rfl
      · exact hcons_log p hmem
    dsimp only [extractPairwiseViolation]
    split_ifs with hviol
    · let p₁ := Classical.choose hviol
      let hp₁ := Classical.choose_spec hviol
      let p₂ := Classical.choose hp₁.2
      let hp₂ := Classical.choose_spec hp₁.2
      dsimp only [TotalSearchCertificate.IsValid]
      rw [hcons_full p₁ hp₁.1, hcons_full p₂ hp₂.1]
      exact hp₂.2
    · exfalso
      have hpairwise : ∀ p₁ ∈ fullLog, ∀ p₂ ∈ fullLog, R p₁ p₂ := by
        intro p₁ hp₁ p₂ hp₂
        by_contra hnot
        exact hviol ⟨p₁, hp₁, p₂, hp₂, hnot⟩
      obtain ⟨f', hf'_P, hf'_full⟩ := hext fullLog hpairwise
      have hf'_eval : Cslib.OracleComp.evalPure f' alg = res.1 := by
        rw [hfst]
        exact evalPure_eq_of_agrees_on_queryLog f f' alg [] fun p hp ↦
          hf'_full p (List.mem_cons_of_mem _ hp)
      have hf'_out : f' res.1 = f res.1 := hf'_full (res.1, f res.1) List.mem_cons_self
      have hgood := hsol f' hf'_P
      rw [hf'_eval, hf'_out] at hgood
      exact hgoal hgood

/-! ### `ℓ_∞` McShane Lipschitz Cube Interpolation and Contraction Reductions -/

/-- The unit `k`-cube `[0, 1]^k` in `Fin k → ℝ` equipped with the sup-norm metric. -/
public abbrev UnitCube (k : ℕ) : Type :=
  ↥(Set.Icc (0 : Fin k → ℝ) 1)

private lemma coord_abs_le_norm_pi {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    |v i| ≤ ‖v‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i

private noncomputable def mcShaneBranch {m k : ℕ} (L : ℝ) (q a : Fin m → UnitCube k)
    (x : UnitCube k) (i : Fin k) : Option (Fin m) → ℝ
  | none => 1
  | some t => L * dist x (q t) + (a t : Fin k → ℝ) i

/-- Coordinatewise McShane Lipschitz extension on `UnitCube k`:
`f(x)_i = min(1, min_{t : Fin m} (L * dist x (q t) + (a t)_i))`. -/
public noncomputable def mcShaneCubeExtension {m k : ℕ} (L : ℝ) (hL : 0 ≤ L)
    (q a : Fin m → UnitCube k) (x : UnitCube k) : UnitCube k :=
  ⟨fun i ↦ Finset.univ.inf' ⟨none, Finset.mem_univ none⟩ (mcShaneBranch L q a x i),
    fun i ↦ by
      rw [Pi.zero_apply]
      refine (Finset.le_inf'_iff _ _).mpr fun o _ ↦ ?_
      cases o with
      | none => exact zero_le_one
      | some t =>
          dsimp only [mcShaneBranch]
          have ha0 : 0 ≤ (a t : Fin k → ℝ) i := by
            simpa only [Pi.zero_apply] using (a t).2.1 i
          exact add_nonneg (mul_nonneg hL dist_nonneg) ha0,
    fun i ↦ by
      rw [Pi.one_apply]
      exact Finset.inf'_le _ (Finset.mem_univ none)⟩

/-- Necessary and sufficient condition for extending finitely many input-output pairs on
`UnitCube k` to an `L`-Lipschitz self-map (`L ≥ 0`). -/
public theorem exists_consistent_lipschitz_cube_iff {m k : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (q a : Fin m → UnitCube k) :
    (∃ f : UnitCube k → UnitCube k,
        (∀ x y : UnitCube k, dist (f x) (f y) ≤ L * dist x y) ∧ ∀ t : Fin m, f (q t) = a t) ↔
      ∀ t₁ t₂ : Fin m, dist (a t₁) (a t₂) ≤ L * dist (q t₁) (q t₂) := by
  constructor
  · rintro ⟨f, hlip, hcons⟩ t₁ t₂
    simpa only [hcons t₁, hcons t₂] using hlip (q t₁) (q t₂)
  · intro hpair_all
    refine ⟨mcShaneCubeExtension L hL q a, ?_, ?_⟩
    · intro x y
      have hstep : ∀ u v : UnitCube k, ∀ i : Fin k,
          (mcShaneCubeExtension L hL q a u : Fin k → ℝ) i ≤
            (mcShaneCubeExtension L hL q a v : Fin k → ℝ) i + L * dist u v := by
        intro u v i
        have hle_each : ∀ o ∈ (Finset.univ : Finset (Option (Fin m))),
            (mcShaneCubeExtension L hL q a u : Fin k → ℝ) i - L * dist u v ≤
              mcShaneBranch L q a v i o := by
          intro o _
          cases o with
          | none =>
            have hu1 : (mcShaneCubeExtension L hL q a u : Fin k → ℝ) i ≤ 1 := by
              simpa only [Pi.one_apply] using (mcShaneCubeExtension L hL q a u).2.2 i
            have hnn : 0 ≤ L * dist u v := mul_nonneg hL dist_nonneg
            dsimp only [mcShaneBranch]
            linarith
          | some t =>
            have hu_t : (mcShaneCubeExtension L hL q a u : Fin k → ℝ) i ≤
                L * dist u (q t) + (a t : Fin k → ℝ) i :=
              Finset.inf'_le _ (Finset.mem_univ (some t))
            have htri : dist u (q t) ≤ dist u v + dist v (q t) := dist_triangle u v (q t)
            have hmul : L * dist u (q t) ≤ L * dist u v + L * dist v (q t) := by
              calc
                L * dist u (q t) ≤ L * (dist u v + dist v (q t)) :=
                  mul_le_mul_of_nonneg_left htri hL
                _ = L * dist u v + L * dist v (q t) := mul_add _ _ _
            dsimp only [mcShaneBranch]
            linarith
        have hinf : (mcShaneCubeExtension L hL q a u : Fin k → ℝ) i - L * dist u v ≤
            Finset.univ.inf' ⟨none, Finset.mem_univ none⟩ (mcShaneBranch L q a v i) :=
          (Finset.le_inf'_iff ⟨none, Finset.mem_univ none⟩ (mcShaneBranch L q a v i)).mpr hle_each
        dsimp only [mcShaneCubeExtension] at hinf ⊢
        linarith
      rw [Subtype.dist_eq, dist_eq_norm]
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg hL dist_nonneg)).mpr fun i ↦ ?_
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
      have h1 := hstep x y i
      have h2 := hstep y x i
      rw [dist_comm y x] at h2
      constructor <;> linarith
    · intro j
      apply Subtype.ext
      funext i
      dsimp only [mcShaneCubeExtension]
      refine le_antisymm ?_ ?_
      · have hle : Finset.univ.inf' ⟨none, Finset.mem_univ none⟩
            (mcShaneBranch L q a (q j) i) ≤ mcShaneBranch L q a (q j) i (some j) :=
          Finset.inf'_le (mcShaneBranch L q a (q j) i) (Finset.mem_univ (some j))
        simpa only [mcShaneBranch, dist_self, mul_zero, zero_add] using hle
      · refine (Finset.le_inf'_iff _ _).mpr fun o _ ↦ ?_
        cases o with
        | none =>
          dsimp only [mcShaneBranch]
          have ha1 : (a j : Fin k → ℝ) i ≤ 1 := by
            simpa only [Pi.one_apply] using (a j).2.2 i
          exact ha1
        | some t =>
          dsimp only [mcShaneBranch]
          have hpair : dist (a j) (a t) ≤ L * dist (q j) (q t) := hpair_all j t
          have hcoord : |(a j : Fin k → ℝ) i - (a t : Fin k → ℝ) i| ≤ dist (a j) (a t) := by
            rw [Subtype.dist_eq, dist_eq_norm]
            simpa only [Pi.sub_apply] using
              coord_abs_le_norm_pi ((a j : Fin k → ℝ) - (a t : Fin k → ℝ)) i
          linarith [(abs_le.mp (hcoord.trans hpair)).2]

/-- Instantiation of `promiseToTotalQueryAlg` for `ε`-approximate fixed-point search over
`L`-Lipschitz self-maps of `UnitCube k`: any `m`-query promise solver compiles into an
`(m + 1)`-query total search algorithm on arbitrary `f : UnitCube k → UnitCube k`. -/
public theorem lipschitzApproxFixedPt_totalSearch_spec {k m : ℕ} {ε L : ℝ} (hL : 0 ≤ L)
    {alg : EndoQueryAlg (UnitCube k) (UnitCube k)} (halg : alg.IsQueryBounded m)
    (hsol : ∀ f' : UnitCube k → UnitCube k,
      (∀ x y : UnitCube k, dist (f' x) (f' y) ≤ L * dist x y) →
        dist (f' (Cslib.OracleComp.evalPure f' alg)) (Cslib.OracleComp.evalPure f' alg) ≤ ε) :
    let G : UnitCube k → UnitCube k → Prop := fun x fx ↦ dist fx x ≤ ε
    let R : (UnitCube k × UnitCube k) → (UnitCube k × UnitCube k) → Prop :=
      fun p₁ p₂ ↦ dist p₁.2 p₂.2 ≤ L * dist p₁.1 p₂.1
    (promiseToTotalQueryAlg G R alg).IsQueryBounded (m + 1) ∧
      ∀ f : UnitCube k → UnitCube k,
        (Cslib.OracleComp.evalPure f (promiseToTotalQueryAlg G R alg)).IsValid G R f := by
  refine ⟨isQueryBounded_promiseToTotalQueryAlg _ _ halg, fun f ↦ ?_⟩
  refine promiseToTotalQueryAlg_spec (P := fun f' ↦ ∀ x y, dist (f' x) (f' y) ≤ L * dist x y)
    ?_ hsol f
  intro log hlog
  let qFn : Fin log.length → UnitCube k := fun t ↦ (log[t.val]).1
  let aFn : Fin log.length → UnitCube k := fun t ↦ (log[t.val]).2
  obtain ⟨f', hlip, hcons⟩ := (exists_consistent_lipschitz_cube_iff hL qFn aFn).mpr
    fun t₁ t₂ ↦ hlog (log[t₁.val]) (List.getElem_mem _) (log[t₂.val]) (List.getElem_mem _)
  refine ⟨f', hlip, fun p hp ↦ ?_⟩
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hp
  exact hcons ⟨idx, hidx⟩

/-- Contractive damping `g(x) = (1 - ε / 2) • f(x)` on `UnitCube k` for `0 < ε ≤ 2`. -/
public noncomputable def dampedCubeMap {k : ℕ} (ε : ℝ) (hε₀ : 0 < ε) (hε₂ : ε ≤ 2)
    (f : UnitCube k → UnitCube k) (x : UnitCube k) : UnitCube k :=
  ⟨fun i ↦ (1 - ε / 2) * (f x : Fin k → ℝ) i,
    fun i ↦ by
      rw [Pi.zero_apply]
      have hfx0 : 0 ≤ (f x : Fin k → ℝ) i := by simpa only [Pi.zero_apply] using (f x).2.1 i
      exact mul_nonneg (by linarith) hfx0,
    fun i ↦ by
      rw [Pi.one_apply]
      have hfx : (f x : Fin k → ℝ) i ≤ 1 := by simpa only [Pi.one_apply] using (f x).2.2 i
      have hfx0 : 0 ≤ (f x : Fin k → ℝ) i := by simpa only [Pi.zero_apply] using (f x).2.1 i
      nlinarith⟩

/-- If `f` is `1`-Lipschitz (non-expansive) on `UnitCube k` and `0 < ε ≤ 2`, then
`dampedCubeMap ε hε₀ hε₂ f` is `(1 - ε / 2)`-Lipschitz. -/
public theorem dampedCubeMap_lipschitz {k : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε₂ : ε ≤ 2)
    {f : UnitCube k → UnitCube k} (hf : ∀ x y : UnitCube k, dist (f x) (f y) ≤ dist x y)
    (x y : UnitCube k) :
    dist (dampedCubeMap ε hε₀ hε₂ f x) (dampedCubeMap ε hε₀ hε₂ f y) ≤
      (1 - ε / 2) * dist x y := by
  have h1_nn : 0 ≤ 1 - ε / 2 := by linarith
  have hscale : dist (dampedCubeMap ε hε₀ hε₂ f x) (dampedCubeMap ε hε₀ hε₂ f y) =
      (1 - ε / 2) * dist (f x) (f y) := by
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have heq : (dampedCubeMap ε hε₀ hε₂ f x : Fin k → ℝ) -
        (dampedCubeMap ε hε₀ hε₂ f y : Fin k → ℝ) =
        (1 - ε / 2) • ((f x : Fin k → ℝ) - (f y : Fin k → ℝ)) := by
      ext i
      simp only [dampedCubeMap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1_nn]
  rw [hscale]
  exact mul_le_mul_of_nonneg_left (hf x y) h1_nn

/-- Any `(ε / 2)`-approximate fixed point of `dampedCubeMap ε hε₀ hε₂ f` is an `ε`-approximate
fixed point of `f`. -/
public theorem dist_of_dampedCubeMap_approxFixedPt {k : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε₂ : ε ≤ 2)
    (f : UnitCube k → UnitCube k) {x : UnitCube k}
    (hx : dist (dampedCubeMap ε hε₀ hε₂ f x) x ≤ ε / 2) :
    dist (f x) x ≤ ε := by
  have hdiff : dist (f x) (dampedCubeMap ε hε₀ hε₂ f x) ≤ ε / 2 := by
    rw [Subtype.dist_eq, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
    simp only [dampedCubeMap, Pi.sub_apply, Real.norm_eq_abs]
    have heq : (f x : Fin k → ℝ) i - (1 - ε / 2) * (f x : Fin k → ℝ) i =
        (ε / 2) * (f x : Fin k → ℝ) i := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity),
      abs_of_nonneg (by simpa only [Pi.zero_apply] using (f x).2.1 i)]
    have hfx1 : (f x : Fin k → ℝ) i ≤ 1 := by simpa only [Pi.one_apply] using (f x).2.2 i
    nlinarith
  linarith [dist_triangle (f x) (dampedCubeMap ε hε₀ hε₂ f x) x]

/-- In any nonempty complete metric space, an `(ε * γ)`-approximate fixed point of a
`(1 - γ)`-contraction (`0 < γ ≤ 1`) lies within distance `ε` of its unique Banach fixed point. -/
public theorem dist_fixedPoint_le_of_approxFixedPt {M : Type*} [MetricSpace M] [Nonempty M]
    [CompleteSpace M] {ε γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) {f : M → M}
    (hf : ContractingWith (Real.toNNReal (1 - γ)) f) {x : M}
    (hx : dist (f x) x ≤ ε * γ) :
    dist x (ContractingWith.fixedPoint f hf) ≤ ε := by
  have hbound := hf.dist_fixedPoint_le x
  rw [Real.coe_toNNReal (1 - γ) (sub_nonneg.mpr hγ₁),
    show (1 : ℝ) - (1 - γ) = γ by ring, dist_comm x (f x)] at hbound
  exact hbound.trans ((div_le_iff₀ hγ₀).mpr hx)

end CslibFrontier.Computability.QueryComplexity
