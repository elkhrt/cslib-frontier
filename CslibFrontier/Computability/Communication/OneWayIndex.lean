/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module

public import CslibFrontier.Computability.Streaming.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Randomized One-Way Communication Protocols and the Boolean Index Lower Bound

This module develops deterministic and public-coin randomized one-way two-party communication
protocols, Yao's minimax averaging lemma over discrete probability mass functions (`PMF`), the
single-pass streaming-to-one-way reduction for `Cslib.Streaming.Algorithm`, and an elementary
Hamming-ball proof of the $\Omega(n)$ randomized one-way communication lower bound for the Boolean
index function $\mathrm{INDEX}_n(x, i) = x_i$.

## Main definitions

* `CslibFrontier.Communication.indexFun`: the index function `(x, i) ↦ x i` on
  `(Fin n → α) × Fin n`.
* `CslibFrontier.Communication.OneWayProtocol`,
  `CslibFrontier.Communication.RandomizedOneWayProtocol`: deterministic and public-coin randomized
  one-way communication protocols from Alice to Bob.
* `CslibFrontier.Communication.OneWayProtocol.ofStreamingAlgorithm`: deterministic one-way protocol
  induced by a single-pass `Cslib.Streaming.Algorithm` on split streams `alice x ++ bob y`.

## Main results

* `CslibFrontier.Communication.exists_mem_support_card_error_le_of_pmf_error_le`,
  `CslibFrontier.Communication.exists_card_error_le_of_pmf_error_le`: Yao's minimax averaging
  principle over a `PMF`.
* `CslibFrontier.Communication.card_hammingBall_bool_pow_five_le`: fifth-power bound `≤ 16 ^ n`
  for binary Hamming balls of radius `d` with `5 * d ≤ n`.
* `CslibFrontier.Communication.RandomizedOneWayProtocol` Boolean `INDEX` lower bounds:
  `two_pow_le_of_computesWithError_indexFun_bool`,
  `logb_card_ge_of_computesWithError_indexFun_bool`, and
  `clog_card_ge_of_computesWithError_indexFun_bool`.
* `CslibFrontier.Communication.OneWayProtocol.computes_ofStreamingAlgorithm`: correctness of the
  one-way protocol induced by a single-pass `Cslib.Streaming.Algorithm`.
-/

public section

open scoped ENNReal

namespace CslibFrontier.Communication

/-! ### Yao's Minimax Averaging Principle -/

section YaoMinimax

private lemma tsum_finset_sum_ennreal {Ω ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    (∑' ω : Ω, ∑ i ∈ s, f i ω) = ∑ i ∈ s, ∑' ω : Ω, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [tsum_add, ih]

/-- **Yao's Minimax Averaging Principle (support-refined)**: if a discrete probability distribution
`μ : PMF Ω` satisfies `μ.toOuterMeasure {ω | err ω i} ≤ ε` for every input `i` in a nonempty finite
input space `I`, then there exists an outcome `ω ∈ μ.support` whose number of erring inputs is at
most `ε * Fintype.card I`. -/
theorem exists_mem_support_card_error_le_of_pmf_error_le {Ω I : Type*} [Fintype I] [Nonempty I]
    (μ : PMF Ω) (err : Ω → I → Prop) [∀ ω, DecidablePred (err ω)] {ε : ℝ≥0∞}
    (hε : ∀ i : I, μ.toOuterMeasure {ω | err ω i} ≤ ε) :
    ∃ ω ∈ μ.support,
      ((Finset.univ.filter (err ω)).card : ℝ≥0∞) ≤ ε * (Fintype.card I : ℝ≥0∞) := by
  by_cases htop : ε = ∞
  · rcases μ.support_nonempty with ⟨ω, hω⟩
    refine ⟨ω, hω, ?_⟩
    have hcard : (Fintype.card I : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [htop, ENNReal.top_mul hcard]
  · by_contra hcontra
    push Not at hcontra
    have hsum_le :
        (∑' ω : Ω, μ ω * ((Finset.univ.filter (err ω)).card : ℝ≥0∞)) ≤
          ε * (Fintype.card I : ℝ≥0∞) := by
      have hrewrite :
          (∑' ω : Ω, μ ω * ((Finset.univ.filter (err ω)).card : ℝ≥0∞)) =
            ∑ i : I, μ.toOuterMeasure {ω | err ω i} := by
        have hpt : ∀ ω : Ω,
            μ ω * ((Finset.univ.filter (err ω)).card : ℝ≥0∞) =
              ∑ i : I, ({ω' | err ω' i} : Set Ω).indicator μ ω := by
          intro ω
          rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          by_cases hi : err ω i <;> simp [Set.indicator, hi]
        simp_rw [hpt, PMF.toOuterMeasure_apply]
        exact tsum_finset_sum_ennreal Finset.univ _
      rw [hrewrite]
      calc
        ∑ i : I, μ.toOuterMeasure {ω | err ω i} ≤ ∑ _i : I, ε :=
          Finset.sum_le_sum fun i _ ↦ hε i
        _ = ε * (Fintype.card I : ℝ≥0∞) := by simp [mul_comm]
    have hlt : ε * (Fintype.card I : ℝ≥0∞) <
        ∑' ω : Ω, μ ω * ((Finset.univ.filter (err ω)).card : ℝ≥0∞) := by
      have hlhs : ε * (Fintype.card I : ℝ≥0∞) =
          ∑' ω : Ω, μ ω * (ε * (Fintype.card I : ℝ≥0∞)) := by
        rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
      rw [hlhs]
      rcases μ.support_nonempty with ⟨ω₀, hω₀⟩
      have hμ_ne : μ ω₀ ≠ 0 := (PMF.mem_support_iff μ ω₀).mp hω₀
      have hμ_top : μ ω₀ ≠ ∞ := μ.apply_ne_top ω₀
      have hterm_lt :
          μ ω₀ * (ε * (Fintype.card I : ℝ≥0∞)) <
            μ ω₀ * ((Finset.univ.filter (err ω₀)).card : ℝ≥0∞) :=
        ENNReal.mul_lt_mul_right hμ_ne hμ_top (hcontra ω₀ hω₀)
      have hfin : (∑' ω : Ω, μ ω * (ε * (Fintype.card I : ℝ≥0∞))) ≠ ∞ := by
        rw [← hlhs]
        exact ENNReal.mul_ne_top htop (ENNReal.natCast_ne_top _)
      have hle_pt : ∀ ω : Ω,
          μ ω * (ε * (Fintype.card I : ℝ≥0∞)) ≤
            μ ω * ((Finset.univ.filter (err ω)).card : ℝ≥0∞) := fun ω ↦ by
        by_cases hω : ω ∈ μ.support
        · exact mul_le_mul_right (le_of_lt (hcontra ω hω)) (μ ω)
        · have h0 : μ ω = 0 := by simpa [PMF.mem_support_iff] using hω
          rw [h0]; simp
      exact ENNReal.tsum_lt_tsum hfin hle_pt hterm_lt
    exact (not_le_of_gt hlt) hsum_le

/-- **Yao's Minimax Averaging Principle**: if `μ : PMF Ω` achieves pointwise error probability at
most `ε` across a nonempty finite input space `I`, some seed `ω : Ω` errs on at most
`ε * Fintype.card I` inputs. -/
theorem exists_card_error_le_of_pmf_error_le {Ω I : Type*} [Fintype I] [Nonempty I]
    (μ : PMF Ω) (err : Ω → I → Prop) [∀ ω, DecidablePred (err ω)] {ε : ℝ≥0∞}
    (hε : ∀ i : I, μ.toOuterMeasure {ω | err ω i} ≤ ε) :
    ∃ ω : Ω, ((Finset.univ.filter (err ω)).card : ℝ≥0∞) ≤ ε * (Fintype.card I : ℝ≥0∞) :=
  let ⟨ω, _, hω⟩ := exists_mem_support_card_error_le_of_pmf_error_le μ err hε
  ⟨ω, hω⟩

end YaoMinimax

/-! ### One-Way Protocols and the Randomized Boolean `INDEX` Lower Bound -/

section OneWay

/-- The two-party index function `INDEX_{n, α}`: Alice holds `x : Fin n → α`, Bob holds `i : Fin n`,
and the target output is `x i`. -/
def indexFun (n : ℕ) (α : Type*) (p : (Fin n → α) × Fin n) : α :=
  p.1 p.2

/-- Evaluation of `indexFun` on a pair `(x, i)`. -/
@[simp] lemma indexFun_mk (n : ℕ) (α : Type*) (x : Fin n → α) (i : Fin n) :
    indexFun n α (x, i) = x i := by exact id rfl

/-- A deterministic one-way communication protocol from Alice (`X`) to Bob (`Y`) with message
alphabet `M` and output type `Z`. -/
@[ext] structure OneWayProtocol (X Y Z M : Type*) where
  /-- Single message sent from Alice to Bob as a function of Alice's input `x : X`. -/
  enc : X → M
  /-- Output computed by Bob from Alice's message and Bob's input `y : Y`. -/
  dec : M × Y → Z

/-- Output produced by a deterministic one-way protocol `P` on inputs `x : X` and `y : Y`. -/
def OneWayProtocol.run {X Y Z M : Type*} (P : OneWayProtocol X Y Z M) (x : X) (y : Y) : Z :=
  P.dec (P.enc x, y)

/-- Evaluating `OneWayProtocol.mk enc dec` returns `dec (enc x, y)`. -/
@[simp] lemma OneWayProtocol.run_mk {X Y Z M : Type*} (enc : X → M) (dec : M × Y → Z)
    (x : X) (y : Y) : (OneWayProtocol.mk enc dec).run x y = dec (enc x, y) := by exact id rfl

/-- A deterministic one-way protocol `P` computes `f : X × Y → Z` if `P.run x y = f (x, y)` on
every input pair `(x, y)`. -/
def OneWayProtocol.Computes {X Y Z M : Type*} (P : OneWayProtocol X Y Z M) (f : X × Y → Z) :
    Prop :=
  ∀ x y, P.run x y = f (x, y)

/-- Pointwise characterization of `OneWayProtocol.Computes`. -/
lemma OneWayProtocol.computes_iff {X Y Z M : Type*} {P : OneWayProtocol X Y Z M}
    {f : X × Y → Z} : P.Computes f ↔ ∀ x y, P.run x y = f (x, y) := Iff.rfl

/-- Canonical deterministic one-way protocol induced by a single-pass `Cslib.Streaming.Algorithm`
on two-party concatenated streams `alice x ++ bob y` with output post-processing `post`. -/
def OneWayProtocol.ofStreamingAlgorithm {S Token Z X Y W : Type*}
    (A : Cslib.Streaming.Algorithm S Token Z) (alice : X → List Token) (bob : Y → List Token)
    (post : Z → W) : OneWayProtocol X Y W S where
  enc x := A.state (alice x)
  dec q := post (A.output (A.stateFrom q.1 (bob q.2)))

/-- `OneWayProtocol.ofStreamingAlgorithm` evaluates to `post (A.run (alice x ++ bob y))`. -/
@[simp] lemma OneWayProtocol.run_ofStreamingAlgorithm {S Token Z X Y W : Type*}
    (A : Cslib.Streaming.Algorithm S Token Z) (alice : X → List Token) (bob : Y → List Token)
    (post : Z → W) (x : X) (y : Y) :
    (OneWayProtocol.ofStreamingAlgorithm A alice bob post).run x y =
      post (A.run (alice x ++ bob y)) := by
  simp [OneWayProtocol.ofStreamingAlgorithm, Cslib.Streaming.Algorithm.run,
    Cslib.Streaming.Algorithm.state, Cslib.Streaming.Algorithm.stateFrom_append]

/-- If `post (A.run (alice x ++ bob y)) = f (x, y)` for all `(x, y)`, then
`OneWayProtocol.ofStreamingAlgorithm A alice bob post` computes `f`. -/
theorem OneWayProtocol.computes_ofStreamingAlgorithm {S Token Z X Y W : Type*}
    (A : Cslib.Streaming.Algorithm S Token Z) (alice : X → List Token) (bob : Y → List Token)
    (post : Z → W) {f : X × Y → W}
    (hf : ∀ x y, post (A.run (alice x ++ bob y)) = f (x, y)) :
    (OneWayProtocol.ofStreamingAlgorithm A alice bob post).Computes f := fun x y ↦ by
  rw [run_ofStreamingAlgorithm, hf x y]

/-- A public-coin randomized one-way communication protocol from `X` to `Y` with message space `M`,
output space `Z`, and random seed distribution `dist : PMF Ω`. -/
@[ext] structure RandomizedOneWayProtocol (X Y Z M Ω : Type*) where
  /-- Deterministic one-way protocol executed for each random seed `ω : Ω`. -/
  proto : Ω → OneWayProtocol X Y Z M
  /-- Probability mass function over random seeds `Ω`. -/
  dist : PMF Ω

variable {X Y Z M Ω : Type*}

/-- Error probability of a randomized one-way protocol `P` on input `(x, y)` for target `f`. -/
noncomputable def RandomizedOneWayProtocol.errorProb
    (P : RandomizedOneWayProtocol X Y Z M Ω) (f : X × Y → Z) (x : X) (y : Y) : ℝ≥0∞ :=
  P.dist.toOuterMeasure {ω | (P.proto ω).run x y ≠ f (x, y)}

/-- Upper-bounding `RandomizedOneWayProtocol.errorProb` via an event containment. -/
lemma RandomizedOneWayProtocol.errorProb_le_of_subset
    (P : RandomizedOneWayProtocol X Y Z M Ω) (f : X × Y → Z) (x : X) (y : Y) {E : Set Ω}
    (hE : {ω | (P.proto ω).run x y ≠ f (x, y)} ⊆ E) :
    P.errorProb f x y ≤ P.dist.toOuterMeasure E :=
  P.dist.toOuterMeasure.mono hE

/-- A randomized one-way protocol `P` computes `f` with error probability at most `ε` if
`P.errorProb f x y ≤ ε` for every `(x, y) : X × Y`. -/
def RandomizedOneWayProtocol.ComputesWithError
    (P : RandomizedOneWayProtocol X Y Z M Ω) (f : X × Y → Z) (ε : ℝ≥0∞) : Prop :=
  ∀ x y, P.errorProb f x y ≤ ε

/-- Pointwise characterization of `RandomizedOneWayProtocol.ComputesWithError`. -/
lemma RandomizedOneWayProtocol.computesWithError_iff
    {P : RandomizedOneWayProtocol X Y Z M Ω} {f : X × Y → Z} {ε : ℝ≥0∞} :
    P.ComputesWithError f ε ↔ ∀ x y, P.errorProb f x y ≤ ε := Iff.rfl

/-- View a deterministic `OneWayProtocol` as a `RandomizedOneWayProtocol` over `PUnit`. -/
noncomputable def OneWayProtocol.toRandomized (P : OneWayProtocol X Y Z M) :
    RandomizedOneWayProtocol X Y Z M PUnit where
  proto _ := P
  dist := PMF.pure PUnit.unit

/-- A deterministic one-way protocol computing `f` computes `f` with error probability `0`. -/
theorem OneWayProtocol.computesWithError_zero_of_computes {P : OneWayProtocol X Y Z M}
    {f : X × Y → Z} (hP : P.Computes f) : P.toRandomized.ComputesWithError f 0 := by
  intro x y
  simp [RandomizedOneWayProtocol.errorProb, OneWayProtocol.toRandomized, hP x y]

/-- Monotonicity of `RandomizedOneWayProtocol.ComputesWithError` in the error threshold. -/
theorem RandomizedOneWayProtocol.ComputesWithError.mono {P : RandomizedOneWayProtocol X Y Z M Ω}
    {f : X × Y → Z} {ε₁ ε₂ : ℝ≥0∞} (h : P.ComputesWithError f ε₁) (hle : ε₁ ≤ ε₂) :
    P.ComputesWithError f ε₂ := fun x y ↦ (h x y).trans hle

private lemma card_hammingBall_bool_eq_sum (n d : ℕ) (center : Fin n → Bool) :
    (Finset.univ.filter fun x : Fin n → Bool ↦
      (Finset.univ.filter fun i ↦ x i ≠ center i).card ≤ d).card =
      ∑ t ∈ Finset.range (d + 1), n.choose t := by
  let φ : (Fin n → Bool) → Finset (Fin n) := fun x ↦ Finset.univ.filter fun i ↦ x i ≠ center i
  have hbij :
      Finset.card (Finset.univ.filter fun x : Fin n → Bool ↦ (φ x).card ≤ d) =
        Finset.card (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ d) := by
    refine Finset.card_bij (fun x _ ↦ φ x) (fun x hx ↦ by simpa using hx) ?_ ?_
    · intro x₁ _ x₂ _ hEq
      funext i
      have hi : (x₁ i ≠ center i) ↔ (x₂ i ≠ center i) := by
        simpa [φ] using congr_arg (i ∈ ·) hEq
      cases h1 : x₁ i <;> cases h2 : x₂ i <;> cases hc : center i <;> simp_all
    · intro S hS
      refine ⟨fun i ↦ if i ∈ S then !center i else center i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        have hφ : φ (fun i ↦ if i ∈ S then !center i else center i) = S := by
          ext i; by_cases hi : i ∈ S <;> simp [φ, hi]
        rwa [hφ]
      · ext i; by_cases hi : i ∈ S <;> simp [φ, hi]
  rw [hbij]
  have hunion :
      (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ d) =
        (Finset.range (d + 1)).biUnion
          (fun t ↦ Finset.powersetCard t (Finset.univ : Finset (Fin n))) := by
    ext S; simp
  rw [hunion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun t _ ↦ by simp [Finset.card_powersetCard]
  · intro t₁ _ t₂ _ hne
    exact Finset.disjoint_left.mpr fun S hS₁ hS₂ ↦
      hne ((Finset.mem_powersetCard.mp hS₁).2.symm.trans (Finset.mem_powersetCard.mp hS₂).2)

/-- Elementary binomial upper bound on binary Hamming balls of radius `d` with `5 * d ≤ n`:
for every center in `Fin n → Bool`, the fifth power of the Hamming-ball cardinality is at most
`16 ^ n`. -/
theorem card_hammingBall_bool_pow_five_le {n d : ℕ} (hd : 5 * d ≤ n) (center : Fin n → Bool) :
    (Finset.univ.filter fun x : Fin n → Bool ↦
      (Finset.univ.filter fun i ↦ x i ≠ center i).card ≤ d).card ^ 5 ≤ 16 ^ n := by
  rw [card_hammingBall_bool_eq_sum]
  suffices hq : ((∑ t ∈ Finset.range (d + 1), n.choose t : ℕ) : ℚ) ^ 5 ≤ (16 : ℚ) ^ n by
    exact_mod_cast hq
  have hsum_le : ((∑ t ∈ Finset.range (d + 1), n.choose t : ℕ) : ℚ) ≤
      (4 : ℚ) ^ d * (5 / 4 : ℚ) ^ n := by
    have hterm : ∀ t ∈ Finset.range (d + 1),
        (n.choose t : ℚ) ≤ (4 : ℚ) ^ d * ((n.choose t : ℚ) * (1 / 4 : ℚ) ^ t) := by
      intro t ht
      have htd : t ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      have hpow : (1 : ℚ) ≤ (4 : ℚ) ^ d * (1 / 4 : ℚ) ^ t := by
        have h4 : (4 : ℚ) ^ t ≤ (4 : ℚ) ^ d := pow_le_pow_right₀ (by norm_num) htd
        have hpos : (0 : ℚ) < (4 : ℚ) ^ t := by positivity
        rw [one_div, inv_pow, ← div_eq_mul_inv]
        exact (one_le_div hpos).mpr h4
      have hnn : (0 : ℚ) ≤ (n.choose t : ℚ) := Nat.cast_nonneg _
      nlinarith
    calc
      ((∑ t ∈ Finset.range (d + 1), n.choose t : ℕ) : ℚ)
          = ∑ t ∈ Finset.range (d + 1), (n.choose t : ℚ) := by push_cast; rfl
      _ ≤ ∑ t ∈ Finset.range (d + 1), (4 : ℚ) ^ d * ((n.choose t : ℚ) * (1 / 4 : ℚ) ^ t) :=
        Finset.sum_le_sum hterm
      _ = (4 : ℚ) ^ d * ∑ t ∈ Finset.range (d + 1), (n.choose t : ℚ) * (1 / 4 : ℚ) ^ t := by
        rw [Finset.mul_sum]
      _ ≤ (4 : ℚ) ^ d * ∑ t ∈ Finset.range (n + 1), (n.choose t : ℚ) * (1 / 4 : ℚ) ^ t := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ ↦ by positivity)
      _ = (4 : ℚ) ^ d * (5 / 4 : ℚ) ^ n := by
        congr 1
        have hbin := add_pow (1 / 4 : ℚ) (1 : ℚ) n
        rw [show (1 / 4 : ℚ) + 1 = 5 / 4 by norm_num] at hbin
        rw [hbin]
        exact Finset.sum_congr rfl fun t _ ↦ by ring
  calc
    ((∑ t ∈ Finset.range (d + 1), n.choose t : ℕ) : ℚ) ^ 5
        ≤ ((4 : ℚ) ^ d * (5 / 4 : ℚ) ^ n) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hsum_le 5
    _ = (4 : ℚ) ^ (5 * d) * ((5 / 4 : ℚ) ^ 5) ^ n := by
      rw [mul_pow, ← pow_mul, mul_comm d 5, ← pow_mul, mul_comm n 5, pow_mul (5 / 4 : ℚ) 5 n]
    _ ≤ (4 : ℚ) ^ n * ((5 / 4 : ℚ) ^ 5) ^ n :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hd) (by positivity)
    _ = (4 * (5 / 4 : ℚ) ^ 5) ^ n := by rw [← mul_pow]
    _ ≤ (16 : ℚ) ^ n := pow_le_pow_left₀ (by positivity) (by norm_num) n

/-- **Randomized One-Way Lower Bound for Boolean `INDEX`**: any randomized one-way protocol with
finite message space `M` computing `indexFun n Bool` with error probability at most `1 / 10`
satisfies `2 ^ n ≤ 32 * Fintype.card M ^ 5`. -/
theorem RandomizedOneWayProtocol.two_pow_le_of_computesWithError_indexFun_bool
    {n : ℕ} {M Ω : Type*} [Fintype M]
    {P : RandomizedOneWayProtocol (Fin n → Bool) (Fin n) Bool M Ω}
    (hP : P.ComputesWithError (indexFun n Bool) (1 / 10 : ℝ≥0∞)) :
    2 ^ n ≤ 32 * Fintype.card M ^ 5 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases P.dist.support_nonempty with ⟨ω, _⟩
    have hM : 1 ≤ Fintype.card M := Fintype.card_pos_iff.mpr ⟨(P.proto ω).enc Fin.elim0⟩
    have hM5 : 1 ≤ Fintype.card M ^ 5 := one_le_pow₀ hM
    omega
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨ω, hω⟩ := exists_card_error_le_of_pmf_error_le P.dist
      (fun ω (p : (Fin n → Bool) × Fin n) ↦ (P.proto ω).run p.1 p.2 ≠ indexFun n Bool p)
      (fun p ↦ hP p.1 p.2)
    let Q := P.proto ω
    let errCount : (Fin n → Bool) → ℕ :=
      fun x ↦ (Finset.univ.filter fun i : Fin n ↦ Q.run x i ≠ x i).card
    have htotal_eq :
        (Finset.univ.filter fun p : (Fin n → Bool) × Fin n ↦
          Q.run p.1 p.2 ≠ indexFun n Bool p).card =
          ∑ x : Fin n → Bool, errCount x := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun x _ ↦ (Finset.card_filter _ _).symm
    have htotal : 10 * ∑ x : Fin n → Bool, errCount x ≤ 2 ^ n * n := by
      rw [← htotal_eq]
      have hcardI : (Fintype.card ((Fin n → Bool) × Fin n) : ℝ≥0∞) =
          ((2 ^ n * n : ℕ) : ℝ≥0∞) := by simp [Fintype.card_prod]
      rw [hcardI] at hω
      have hmul := mul_le_mul_right hω (10 : ℝ≥0∞)
      have hcancel : (10 : ℝ≥0∞) * (1 / 10 : ℝ≥0∞) = 1 := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      rw [← mul_assoc, hcancel, one_mul] at hmul
      exact_mod_cast hmul
    let good : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦ 5 * errCount x ≤ n
    let bad : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦ n < 5 * errCount x
    have hbad_le : 2 * bad.card ≤ 2 ^ n := by
      refine Nat.le_of_mul_le_mul_right ?_ hn
      calc
        2 * bad.card * n = ∑ _x ∈ bad, 2 * n := by simp; ring
        _ ≤ ∑ x ∈ bad, 10 * errCount x :=
          Finset.sum_le_sum fun x hx ↦ by have := (Finset.mem_filter.mp hx).2; omega
        _ = 10 * ∑ x ∈ bad, errCount x := by rw [Finset.mul_sum]
        _ ≤ 10 * ∑ x : Fin n → Bool, errCount x :=
          Nat.mul_le_mul_left 10 (Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _)
        _ ≤ 2 ^ n * n := htotal
    have hpart : good.card + bad.card = 2 ^ n := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Bool))) (p := fun x ↦ 5 * errCount x ≤ n)
      rw [show (Finset.univ.filter fun x : Fin n → Bool ↦ ¬ 5 * errCount x ≤ n) = bad by
        ext x; simp [bad]] at h
      simpa [good] using h
    have hgood_ge : 2 ^ n ≤ 2 * good.card := by omega
    let d : ℕ := n / 5
    have hd : 5 * d ≤ n := Nat.mul_div_le n 5
    have hcover : good ⊆ Finset.univ.biUnion (fun m : M ↦
        Finset.univ.filter fun x : Fin n → Bool ↦
          (Finset.univ.filter fun i : Fin n ↦ x i ≠ Q.dec (m, i)).card ≤ d) := by
      intro x hx
      refine Finset.mem_biUnion.mpr ⟨Q.enc x, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hgx : 5 * errCount x ≤ n := (Finset.mem_filter.mp hx).2
      have herr_eq : (Finset.univ.filter fun i : Fin n ↦ x i ≠ Q.dec (Q.enc x, i)).card =
          errCount x := by congr 1; ext i; simp [OneWayProtocol.run, ne_comm]
      rw [herr_eq]
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).mpr (by omega)
    have hgood_pow5 : good.card ^ 5 ≤ Fintype.card M ^ 5 * 16 ^ n := by
      have hcard_le : good.card ≤ ∑ m : M, (Finset.univ.filter fun x : Fin n → Bool ↦
          (Finset.univ.filter fun i : Fin n ↦ x i ≠ Q.dec (m, i)).card ≤ d).card :=
        (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      simp_rw [fun m ↦ card_hammingBall_bool_eq_sum n d (fun i ↦ Q.dec (m, i))] at hcard_le
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcard_le
      have h5 := Nat.pow_le_pow_left hcard_le 5
      rw [mul_pow] at h5
      have hb5 : (∑ t ∈ Finset.range (d + 1), n.choose t) ^ 5 ≤ 16 ^ n := by
        rw [← card_hammingBall_bool_eq_sum n d (fun _ ↦ false)]
        exact card_hammingBall_bool_pow_five_le hd (fun _ ↦ false)
      exact h5.trans (Nat.mul_le_mul_left _ hb5)
    have hmain : (2 ^ n) ^ 5 ≤ 32 * Fintype.card M ^ 5 * 16 ^ n := calc
      (2 ^ n) ^ 5 ≤ (2 * good.card) ^ 5 := Nat.pow_le_pow_left hgood_ge 5
      _ = 32 * good.card ^ 5 := by ring
      _ ≤ 32 * (Fintype.card M ^ 5 * 16 ^ n) := Nat.mul_le_mul_left 32 hgood_pow5
      _ = 32 * Fintype.card M ^ 5 * 16 ^ n := by ring
    rw [show 16 ^ n = 2 ^ (4 * n) by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul],
      show (2 ^ n) ^ 5 = 2 ^ n * 2 ^ (4 * n) by rw [← pow_mul, ← pow_add]; congr 1; omega] at hmain
    exact Nat.le_of_mul_le_mul_right hmain (by positivity)

private lemma card_pos_of_two_pow_le {n : ℕ} {M : Type*} [Fintype M]
    (hpow : 2 ^ n ≤ 32 * Fintype.card M ^ 5) : 0 < Fintype.card M := by
  by_contra h0
  rw [show Fintype.card M = 0 by omega] at hpow
  have : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  omega

/-- **Logarithmic Randomized One-Way Lower Bound for Boolean `INDEX`**: any randomized one-way
protocol with finite message space `M` computing `indexFun n Bool` with error probability at most
`1 / 10` satisfies `(n : ℝ) / 5 - 1 ≤ Real.logb 2 (Fintype.card M)`. -/
theorem RandomizedOneWayProtocol.logb_card_ge_of_computesWithError_indexFun_bool
    {n : ℕ} {M Ω : Type*} [Fintype M]
    {P : RandomizedOneWayProtocol (Fin n → Bool) (Fin n) Bool M Ω}
    (hP : P.ComputesWithError (indexFun n Bool) (1 / 10 : ℝ≥0∞)) :
    (n : ℝ) / 5 - 1 ≤ Real.logb 2 (Fintype.card M : ℝ) := by
  have hpow := P.two_pow_le_of_computesWithError_indexFun_bool hP
  have hMpos : 0 < Fintype.card M := card_pos_of_two_pow_le hpow
  have hreal : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 5 * (Fintype.card M : ℝ) ^ 5 := by exact_mod_cast hpow
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (pow_pos (by norm_num) n) hreal
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  simp only [Nat.cast_ofNat] at hlog
  linarith

/-- Bit-length randomized one-way lower bound for Boolean `INDEX`:
`(n : ℝ) / 5 - 1 ≤ Nat.clog 2 (Fintype.card M)`. -/
theorem RandomizedOneWayProtocol.clog_card_ge_of_computesWithError_indexFun_bool
    {n : ℕ} {M Ω : Type*} [Fintype M]
    {P : RandomizedOneWayProtocol (Fin n → Bool) (Fin n) Bool M Ω}
    (hP : P.ComputesWithError (indexFun n Bool) (1 / 10 : ℝ≥0∞)) :
    (n : ℝ) / 5 - 1 ≤ (Nat.clog 2 (Fintype.card M) : ℝ) := by
  have hlog := P.logb_card_ge_of_computesWithError_indexFun_bool hP
  have hMpos := card_pos_of_two_pow_le (P.two_pow_le_of_computesWithError_indexFun_bool hP)
  have hle : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (Fintype.card M) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card M)
  have hlog_le : Real.logb 2 (Fintype.card M : ℝ) ≤ (Nat.clog 2 (Fintype.card M) : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Nat.cast_pos.mpr hMpos) hle
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
  exact hlog.trans hlog_le

end OneWay

end CslibFrontier.Communication
