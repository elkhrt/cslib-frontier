/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Basic.Real.Basic

/-!
# Layered `d`-adaptive oracle Boolean circuits, adaptive closeness, and `ε`-robustness

An oracle Boolean circuit making adaptive queries can be decomposed into `d` adaptivity levels of
oracle gates (`AdaptiveOracleCircuit`), with oracle-free De Morgan Boolean circuits `C_0, …, C_d`
computing each level's query strings from the input `x` and prior query-answer pairs, and `C_d`
computing the final output bit. Substituting a candidate query-answer sequence `Q'` in place of the
true oracle trace `trueTrace O x` defines the substituted evaluation `evalSubst`.

Because modifying an oracle answer in an earlier adaptivity level can alter which queries a circuit
legitimately asks in later levels, closeness of a candidate trace `Q'` to the true trace of an
adaptive circuit is defined iteratively (`IsAdaptiveClose`): at each level `r`, one recomputes the
intended queries `T_r^in` from `(x, Q'_1, …, Q'_{r-1})`, pairs them with true oracle answers `O`,
and counts positions where `Q'_r` differs from `T_r`. For `1`-adaptive (nonadaptive) circuits, this
coincides with ordinary Hamming distance (`isAdaptiveClose_one_iff_hammingDist_le`). An oracle
circuit is *`ε`-robust* (`IsRobust`) if substituting any `ε`-close trace preserves its output on
every input `x`.

## Main definitions

* `Cslib.Circuits.Boolean.OracleQueryAnswer`: a query bit-vector paired with a 1-bit oracle answer.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit`: level-by-level De Morgan decomposition of a
  `d`-adaptive oracle Boolean circuit.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.trueTrace`,
  `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.evalSubst`: honest oracle execution trace and
  substituted evaluation `C_{Q'}(x)`.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.recomputedStep`,
  `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.adaptiveDeviation`,
  `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.IsAdaptiveClose`: iterative `d`-adaptive deviation
  count and `ε`-closeness.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.IsRobust`: `ε`-robustness with respect to an oracle.

## Main results

* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.evalSubst_trueTrace`: `C_{Q(x)}(x) = C^O(x)`.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.isAdaptiveClose_one_iff_hammingDist_le`: for `d = 1`
  (nonadaptive circuits), `IsAdaptiveClose` equals fractional Hamming closeness.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.IsAdaptiveClose.mono`: monotonicity in `ε`.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.isRobust_of_lt_one`: vacuous robustness when
  `ε * ℓ < 1` and `0 ≤ ε`.
* `Cslib.Circuits.Boolean.AdaptiveOracleCircuit.isAdaptiveClose_of_consistentQueries`: any trace
  whose queries match the circuit's induced queries and whose answers disagree with `O` in at most
  `ε * ℓ` positions is `ε`-close to `trueTrace`.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

/-- A single query-answer pair `(query, answer)` for an oracle gate of query arity `m`. -/
@[ext]
structure OracleQueryAnswer (m : ℕ) where
  /-- The `m`-bit query string fed into the oracle gate. -/
  query : Fin m → Bool
  /-- The 1-bit answer returned for `query`. -/
  answer : Bool
  deriving DecidableEq, Fintype

namespace OracleQueryAnswer

/-- Total bit width `m + 1` of an `OracleQueryAnswer m`. -/
def toBits {m : ℕ} (qa : OracleQueryAnswer m) : Fin (m + 1) → Bool :=
  Fin.snoc qa.query qa.answer

/-- Reconstruct an `OracleQueryAnswer m` from `m + 1` bits. -/
def ofBits {m : ℕ} (v : Fin (m + 1) → Bool) : OracleQueryAnswer m :=
  ⟨Fin.init v, v (Fin.last m)⟩

@[simp]
theorem ofBits_toBits {m : ℕ} (qa : OracleQueryAnswer m) : ofBits qa.toBits = qa := by
  ext i
  · simp [ofBits, toBits]
  · simp [ofBits, toBits]

@[simp]
theorem toBits_ofBits {m : ℕ} (v : Fin (m + 1) → Bool) : (ofBits v).toBits = v := by
  simp [ofBits, toBits]

end OracleQueryAnswer

/-- Level-by-level decomposition of an `n`-input, `d`-adaptive oracle Boolean circuit with query
length `m` and `layerCount i` oracle gates at adaptivity level `i : Fin d`. Each transition map is
computed by a genuine fan-in-at-most-2 De Morgan Boolean circuit over `signature`. -/
structure AdaptiveOracleCircuit (n d m : ℕ) where
  /-- Number of oracle gates `ℓ_i` in adaptivity level `i : Fin d`. -/
  layerCount : Fin d → ℕ
  /-- De Morgan circuit computing the queries at level `i` from `x` and prior query-answer layers
  `(Q_0, …, Q_{i-1})` flattened to bits. -/
  queryCircuit : (i : Fin d) →
    Circuit signature (n + (∑ j : Fin i.val, layerCount ⟨j.val, j.isLt.trans i.isLt⟩) * (m + 1))
      (layerCount i * m)
  /-- De Morgan circuit computing the final 1-bit output from `x` and all `d` query-answer layers
  `(Q_0, …, Q_{d-1})`. -/
  outputCircuit : Circuit signature (n + (∑ i : Fin d, layerCount i) * (m + 1)) 1

namespace AdaptiveOracleCircuit

variable {n d m : ℕ} (C : AdaptiveOracleCircuit n d m)

/-- Total number of oracle gates `ℓ = ∑ i, ℓ_i` across all `d` adaptivity levels. -/
def totalGates : ℕ :=
  ∑ i : Fin d, C.layerCount i

/-- Type of a query-answer trace `Q = (Q_0, …, Q_{d-1})` across all `d` levels. -/
abbrev Trace : Type :=
  (i : Fin d) → Fin (C.layerCount i) → OracleQueryAnswer m

/-- Pack `x : Fin n → Bool` and the first `k ≤ d` layers of a trace into a flat input bit-vector
for `queryCircuit` or `outputCircuit`. -/
def packPrefix (x : Fin n → Bool) (Q : C.Trace) :
    (k : ℕ) → (hk : k ≤ d) →
      Fin (n + (∑ j : Fin k, C.layerCount ⟨j.val, j.isLt.trans_le hk⟩) * (m + 1)) → Bool
  | 0, _, idx => x (idx.cast (by simp))
  | k + 1, hk, idx =>
    have hsplit :
        n + (∑ j : Fin (k + 1), C.layerCount ⟨j.val, j.isLt.trans_le hk⟩) * (m + 1) =
          (n + (∑ j : Fin k, C.layerCount ⟨j.val,
            Nat.lt_of_lt_of_le j.isLt (Nat.le_of_succ_le hk)⟩) *
            (m + 1)) + C.layerCount ⟨k, hk⟩ * (m + 1) := by
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      ring
    Fin.addCases
      (packPrefix x Q k (Nat.le_of_succ_le hk))
      (fun rem ↦
        let p := finProdFinEquiv.symm rem
        (Q ⟨k, hk⟩ p.1).toBits p.2)
      (idx.cast hsplit)

/-- Evaluate level-`i` query circuit `C_i` on input `x` and prior trace layers of `Q`. -/
def evalQueriesAt (x : Fin n → Bool) (Q : C.Trace) (i : Fin d) :
    Fin (C.layerCount i) → (Fin m → Bool) :=
  let raw := (C.queryCircuit i).eval interpretation (C.packPrefix x Q i.val i.isLt.le)
  fun g bit ↦ raw (finProdFinEquiv (g, bit))

/-- Evaluate the substituted circuit `C_{Q'}(x)` using candidate query-answer trace `Q'`. -/
def evalSubst (x : Fin n → Bool) (Q' : C.Trace) : Bool :=
  (C.outputCircuit.eval interpretation (C.packPrefix x Q' d le_rfl)) 0

private lemma packPrefix_congr {x : Fin n → Bool} {Q₁ Q₂ : C.Trace} :
    ∀ (k : ℕ) (hk : k ≤ d),
      (∀ (j : Fin d), j.val < k → Q₁ j = Q₂ j) →
      C.packPrefix x Q₁ k hk = C.packPrefix x Q₂ k hk
  | 0, _, _ => rfl
  | k + 1, hk, hagree => by
    have h1 : C.packPrefix x Q₁ k (Nat.le_of_succ_le hk) =
        C.packPrefix x Q₂ k (Nat.le_of_succ_le hk) :=
      packPrefix_congr k (Nat.le_of_succ_le hk)
        (fun j hj ↦ hagree j (Nat.lt_succ_of_lt hj))
    have h2 : Q₁ ⟨k, hk⟩ = Q₂ ⟨k, hk⟩ := hagree ⟨k, hk⟩ (Nat.lt_succ_self k)
    simp only [packPrefix, h1, h2]

/-- `evalQueriesAt x Q i` depends only on layers `j < i` of `Q`. -/
theorem evalQueriesAt_congr {x : Fin n → Bool} {Q₁ Q₂ : C.Trace} {i : Fin d}
    (h : ∀ j : Fin d, j.val < i.val → Q₁ j = Q₂ j) :
    C.evalQueriesAt x Q₁ i = C.evalQueriesAt x Q₂ i := by
  simp only [evalQueriesAt, C.packPrefix_congr i.val i.isLt.le h]

/-- Build the honest trace up to `k` levels by iteratively querying `O : Language Bool`. -/
noncomputable def buildTrueTrace (O : Language Bool) (x : Fin n → Bool) :
    (k : ℕ) → C.Trace
  | 0 => fun _ _ ↦ ⟨fun _ ↦ false, false⟩
  | k + 1 =>
    let prev := buildTrueTrace O x k
    fun i g ↦
      if i.val = k then
        let q := C.evalQueriesAt x prev i
        ⟨q g, O.slice m (q g)⟩
      else
        prev i g

private lemma buildTrueTrace_stable (O : Language Bool) (x : Fin n → Bool) :
    ∀ {k : ℕ} {i : Fin d}, i.val < k →
      C.buildTrueTrace O x k i =
        fun g ↦
          let q := C.evalQueriesAt x (C.buildTrueTrace O x i.val) i
          ⟨q g, O.slice m (q g)⟩
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · have hne : i.val ≠ k := ne_of_lt hlt
      ext g : 1
      simp only [buildTrueTrace, hne, ↓reduceIte]
      exact congrFun (buildTrueTrace_stable O x hlt) g
    · ext g : 1
      simp [buildTrueTrace]

/-- The honest oracle query-answer trace `Q(x)` produced by `C` with access to `O` on input `x`. -/
noncomputable def trueTrace (O : Language Bool) (x : Fin n → Bool) : C.Trace :=
  C.buildTrueTrace O x d

/-- At every level `i : Fin d`, `trueTrace O x i` equals the queries induced by `trueTrace O x`
paired with their true oracle answers under `O`. -/
theorem trueTrace_eq (O : Language Bool) (x : Fin n → Bool) (i : Fin d) :
    C.trueTrace O x i =
      fun g ↦
        let q := C.evalQueriesAt x (C.trueTrace O x) i
        ⟨q g, O.slice m (q g)⟩ := by
  have h1 := C.buildTrueTrace_stable O x i.isLt
  have hcong : C.evalQueriesAt x (C.buildTrueTrace O x i.val) i =
      C.evalQueriesAt x (C.trueTrace O x) i := by
    refine C.evalQueriesAt_congr fun j hj ↦ ?_
    rw [C.buildTrueTrace_stable O x hj, trueTrace, C.buildTrueTrace_stable O x j.isLt]
  simpa [trueTrace, hcong] using h1

/-- Evaluate `C^O(x)` with true oracle access to `O`. -/
noncomputable def evalOracle (O : Language Bool) (x : Fin n → Bool) : Bool :=
  C.evalSubst x (C.trueTrace O x)

/-- Substituting the honest trace `trueTrace O x` recovers `C^O(x)` (`C_{Q(x)}(x) = C^O(x)`). -/
theorem evalSubst_trueTrace (O : Language Bool) (x : Fin n → Bool) :
    C.evalSubst x (C.trueTrace O x) = C.evalOracle O x := by
  unfold evalOracle
  rfl

/-- Recomputed reference step `T_i = (C_{i-1}(x, Q'_0, …, Q'_{i-1}), O(…))` in the `ε`-closeness
algorithm.
-/
noncomputable def recomputedStep (O : Language Bool) (x : Fin n → Bool) (Q' : C.Trace)
    (i : Fin d) : Fin (C.layerCount i) → OracleQueryAnswer m :=
  let q := C.evalQueriesAt x Q' i
  fun g ↦ ⟨q g, O.slice m (q g)⟩

/-- Total number of modified query-answer positions across all `d` levels in the iterative
closeness algorithm (`∑ i, hammingDist (Q' i) (T_i)`). -/
noncomputable def adaptiveDeviation (O : Language Bool) (x : Fin n → Bool) (Q' : C.Trace) : ℕ :=
  ∑ i : Fin d, hammingDist (Q' i) (C.recomputedStep O x Q' i)

/-- Candidate trace `Q'` is *`ε`-close* to `trueTrace O x` if its iterative
deviation count across all `d` levels is at most `ε * totalGates`.
-/
def IsAdaptiveClose (O : Language Bool) (ε : ℝ) (x : Fin n → Bool) (Q' : C.Trace) : Prop :=
  (C.adaptiveDeviation O x Q' : ℝ) ≤ ε * (C.totalGates : ℝ)

/-- Monotonicity of `IsAdaptiveClose` in `ε`. -/
theorem IsAdaptiveClose.mono {O : Language Bool} {ε₁ ε₂ : ℝ} {x : Fin n → Bool} {Q' : C.Trace}
    (h : C.IsAdaptiveClose O ε₁ x Q') (hle : ε₁ ≤ ε₂) :
    C.IsAdaptiveClose O ε₂ x Q' :=
  h.trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))

/-- For a nonadaptive (`1`-adaptive) oracle circuit, `IsAdaptiveClose` coincides with fractional
Hamming distance to `trueTrace O x`.
-/
theorem isAdaptiveClose_one_iff_hammingDist_le (C₁ : AdaptiveOracleCircuit n 1 m)
    (O : Language Bool) (ε : ℝ) (x : Fin n → Bool) (Q' : C₁.Trace) :
    C₁.IsAdaptiveClose O ε x Q' ↔
      (hammingDist (Q' 0) (C₁.trueTrace O x 0) : ℝ) ≤ ε * (C₁.layerCount 0 : ℝ) := by
  have hstep : C₁.recomputedStep O x Q' 0 = C₁.trueTrace O x 0 := by
    rw [C₁.trueTrace_eq O x 0]
    have hq : C₁.evalQueriesAt x Q' 0 = C₁.evalQueriesAt x (C₁.trueTrace O x) 0 :=
      C₁.evalQueriesAt_congr fun j hj ↦ absurd hj (Nat.not_lt_zero _)
    simp only [recomputedStep, hq]
  simp [IsAdaptiveClose, adaptiveDeviation, totalGates, hstep]

/-- An adaptive oracle circuit `C` is *`ε`-robust* with respect to `O` if for
every `x : Fin n → Bool` and every `Q'` that is `ε`-close to `trueTrace O x`,
`C.evalSubst x Q' = C.evalOracle O x`.
-/
def IsRobust (O : Language Bool) (ε : ℝ) : Prop :=
  ∀ (x : Fin n → Bool) (Q' : C.Trace),
    C.IsAdaptiveClose O ε x Q' → C.evalSubst x Q' = C.evalOracle O x

/-- If `ε * totalGates < 1`, then `adaptiveDeviation = 0`, forcing `Q' = trueTrace O x`, so every
adaptive oracle circuit is vacuously `ε`-robust. -/
theorem isRobust_of_lt_one (O : Language Bool) {ε : ℝ} (h : ε * (C.totalGates : ℝ) < 1) :
    C.IsRobust O ε := by
  intro x Q' hclose
  have hdev_lt : (C.adaptiveDeviation O x Q' : ℝ) < 1 := lt_of_le_of_lt hclose h
  have hdev_zero : C.adaptiveDeviation O x Q' = 0 := by
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hdev_lt)
  have hlayer_eq : ∀ k : ℕ, ∀ i : Fin d, i.val < k → Q' i = C.trueTrace O x i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hdist0 : hammingDist (Q' i) (C.recomputedStep O x Q' i) = 0 :=
          (Finset.sum_eq_zero_iff.mp hdev_zero) i (Finset.mem_univ i)
        have hQi : Q' i = C.recomputedStep O x Q' i := hammingDist_eq_zero.mp hdist0
        have hq : C.evalQueriesAt x Q' i = C.evalQueriesAt x (C.trueTrace O x) i :=
          C.evalQueriesAt_congr fun j hj ↦ ih j (heq ▸ hj)
        rw [hQi, C.trueTrace_eq O x i]
        simp only [recomputedStep, hq]
  have hQeq : Q' = C.trueTrace O x := funext fun i ↦ hlayer_eq d i i.isLt
  rw [hQeq, C.evalSubst_trueTrace]

/-- **Trajectory-error closeness lemma**: if `Q*` satisfies query consistency
`(Q* i g).query = C.evalQueriesAt x Q* i g` at every gate `(i, g)` and has at most `ε * totalGates`
incorrect oracle answers `(Q* i g).answer ≠ O ((Q* i g).query)`, then `Q*` is `ε`-close to
`trueTrace O x`. -/
theorem isAdaptiveClose_of_consistentQueries (O : Language Bool) {ε : ℝ} {x : Fin n → Bool}
    {Qstar : C.Trace}
    (hq : ∀ (i : Fin d) (g : Fin (C.layerCount i)),
      (Qstar i g).query = C.evalQueriesAt x Qstar i g)
    (herr : ((∑ i : Fin d,
      (Finset.univ.filter fun g : Fin (C.layerCount i) ↦
        (Qstar i g).answer ≠ O.slice m (Qstar i g).query).card : ℕ) : ℝ) ≤
      ε * (C.totalGates : ℝ)) :
    C.IsAdaptiveClose O ε x Qstar := by
  have hdev_eq : C.adaptiveDeviation O x Qstar =
      ∑ i : Fin d,
        (Finset.univ.filter fun g : Fin (C.layerCount i) ↦
          (Qstar i g).answer ≠ O.slice m (Qstar i g).query).card := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hammingDist, recomputedStep]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, OracleQueryAnswer.ext_iff,
      hq i g, true_and]
  simpa [IsAdaptiveClose, hdev_eq] using herr

end AdaptiveOracleCircuit

end Cslib.Circuits.Boolean
