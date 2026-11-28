module

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.Schedule
public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Derandomization
import Cslib.Computability.Circuit.Composition
import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Computability.Circuit.Boolean.BitBlast
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import CslibFrontier.Computability.Circuit.Boolean.Lookup
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relativized Oracle-Circuit Size, Hardness Amplification, and NW Reconstruction

This module develops relativized Boolean circuit complexity over oracle gates and proves under
standard Lean axioms both the local-list-decoding worst-case-to-average-case
hardness amplification and the Nisan–Wigderson pseudorandom generator reconstruction relative to
an arbitrary Boolean oracle language `A`.

An oracle circuit over `Cslib.Circuits.Boolean.oracleSignature` combines standard De Morgan gates
with oracle query gates of arbitrary arity `q`. Its wire-and-gate size (`oracleCircuitSize`) counts
each gate together with its incoming wires, preventing degenerate constant-gate circuits with
exponentially wide oracle queries and matching `Cslib.Circuits.Boolean.PPolyOracle` up to
polynomial factors (`mem_PPolyOracle_iff_exists_oracleCircuitSize`,
`enpHypothesis_iff_gate_and_fanIn`).

## Main definitions

* `CslibFrontier.Computability.oracleGateCost`, `CslibFrontier.Computability.oracleCircuitSize`:
  wire-and-gate cost `1 + arity` on `OracleOp` and total wire-and-gate size of an oracle circuit.
* `CslibFrontier.Computability.oracleSIZE`, `CslibFrontier.Computability.oracleSIZEInfOften`:
  relativized oracle circuit size classes `Size^A(s)` and `i.o.-Size^A(s)`.
* `CslibFrontier.Computability.ENPHypothesis`: the open complexity-theoretic conjecture `(E-NP)`
  asserting that some language in `E` lies outside `i.o.-Size^A(2^{ε n})` for every `A ∈ NP`.
* `CslibFrontier.Computability.BoundedOracleOp`,
  `CslibFrontier.Computability.boundedOracleSignature`,
  `CslibFrontier.Computability.boundedOracleInterpretation`: fan-in-capped oracle circuit basis.
* `CslibFrontier.Computability.IsOracleAverageCaseHard`: average-case hardness against
  fan-in-bounded `A`-oracle circuits.

## Main results

* `CslibFrontier.Computability.mem_PPolyOracle_iff_exists_oracleCircuitSize`: characterization of
  `P/poly^A` via polynomial wire-and-gate oracle circuit size.
* `CslibFrontier.Computability.enpHypothesis_iff_gate_and_fanIn`: equivalence of wire-and-gate
  `(E-NP)` with simultaneous exponential gate-count and fan-in lower bounds.
* `CslibFrontier.Computability.abs_card_div_sub_card_div_lt_boundedOracle`: relativized
  Nisan–Wigderson distinguishing-probability bound against fan-in-bounded `A`-oracle circuits.
* `CslibFrontier.Computability.eventually_isOracleAverageCaseHard_encodedSlice`: relativized
  Impagliazzo–Wigderson / worst-case-to-average-case hardness amplification
  for `A`-oracle circuits.


-/

public section

namespace CslibFrontier.Computability

open Filter Finset
open Cslib Cslib.Code Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Crypto Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson Cslib.HardnessEncoding
open Turing.MultiTapeTM

/-! ### Wire-and-gate size of oracle circuits and the `(E-NP)` hypothesis -/

/-- The wire-and-gate cost of an operation in `oracleSignature`: one for the gate itself plus its
fan-in (at most `3` for a standard De Morgan gate and `q + 1` for a `q`-bit oracle query). -/
def oracleGateCost (op : OracleOp) : ℕ :=
  1 + oracleSignature.Arity op

/-- A standard De Morgan operation has wire-and-gate cost at most `3`. -/
theorem oracleGateCost_base_le (op : Op) : oracleGateCost (.base op) ≤ 3 := by
  cases op <;> simp [oracleGateCost, OracleOp.arity]

/-- An arity-`q` oracle query gate has wire-and-gate cost `q + 1`. -/
@[simp]
theorem oracleGateCost_query (q : ℕ) : oracleGateCost (.query q) = q + 1 := by
  simp only [oracleGateCost, OracleOp.arity]
  exact Nat.add_comm 1 q

/-- Every operation in `oracleSignature` has positive wire-and-gate cost. -/
theorem oracleGateCost_pos (op : OracleOp) : 1 ≤ oracleGateCost op :=
  Nat.le_add_right 1 _

/-- The total wire-and-gate size of an oracle circuit: the sum of `1 + arity` over all gates in
its program. -/
def oracleCircuitSize {n m : ℕ} (C : Circuit oracleSignature n m) : ℕ :=
  C.program.cost oracleGateCost

/-- The number of gates of an oracle circuit is at most its wire-and-gate size. -/
theorem size_le_oracleCircuitSize {n m : ℕ} (C : Circuit oracleSignature n m) :
    C.size ≤ oracleCircuitSize C := by
  rw [oracleCircuitSize, Program.cost_eq_sum]
  calc C.size = ∑ _k : Fin C.size, 1 := by simp
    _ ≤ ∑ k : Fin C.size, oracleGateCost (C.program.lines k).op :=
        sum_le_sum fun _ _ => oracleGateCost_pos _

/-- Every gate in an oracle circuit has fan-in bounded by the circuit's wire-and-gate size. -/
theorem fanInAtMost_oracleCircuitSize {n m : ℕ} (C : Circuit oracleSignature n m) :
    C.FanInAtMost (oracleCircuitSize C) := by
  rw [Circuit.FanInAtMost, Program.fanInAtMost_iff]
  intro k
  rw [oracleCircuitSize, Program.cost_eq_sum]
  have hmem : oracleGateCost (C.program.lines k).op ≤
      ∑ i : Fin C.size, oracleGateCost (C.program.lines i).op :=
    single_le_sum (f := fun i : Fin C.size => oracleGateCost (C.program.lines i).op)
      (fun _ _ => Nat.zero_le _) (mem_univ k)
  exact (Nat.le_add_left _ 1).trans hmem

/-- An oracle circuit with gate fan-in at most `r` has wire-and-gate size at most
`C.size * (r + 1)`. -/
theorem oracleCircuitSize_le_mul_of_fanInAtMost {n m r : ℕ} (C : Circuit oracleSignature n m)
    (hC : C.FanInAtMost r) : oracleCircuitSize C ≤ C.size * (r + 1) := by
  rw [oracleCircuitSize, Program.cost_eq_sum]
  have hfan := Program.fanInAtMost_iff.1 hC
  calc ∑ k : Fin C.size, oracleGateCost (C.program.lines k).op
      ≤ ∑ _k : Fin C.size, (r + 1) := sum_le_sum fun k _ => by
        have hk : oracleSignature.Arity (C.program.lines k).op ≤ r := hfan k
        change 1 + oracleSignature.Arity (C.program.lines k).op ≤ r + 1
        omega
    _ = C.size * (r + 1) := by simp

/-- Embedding a De Morgan circuit into `oracleSignature` scales its size by at most `3`. -/
theorem oracleCircuitSize_mapOp_toOracle_le {n m : ℕ} (C : Circuit signature n m) :
    oracleCircuitSize (C.mapOp toOracle) ≤ 3 * C.size := by
  have h := oracleCircuitSize_le_mul_of_fanInAtMost (C.mapOp toOracle)
    (fanInAtMost_mapOp_toOracle C.program le_rfl)
  rwa [Circuit.size_mapOp, Nat.mul_comm] at h

/-- `P/poly` relative to an oracle `A` coincides with the languages decided by oracle circuit
families of polynomially bounded wire-and-gate size. -/
theorem mem_PPolyOracle_iff_exists_oracleCircuitSize {A L : Language Bool} :
    L ∈ PPolyOracle A ↔
      ∃ (C : ∀ n, Circuit oracleSignature n 1) (s : ℕ → ℕ), PolynomiallyBounded s ∧
        ∀ n, oracleCircuitSize (C n) ≤ s n ∧
          (C n).Computes (oracleInterpretation A) (single (L.slice n)) := by
  constructor
  · rintro ⟨C, s, hs, hC⟩
    refine ⟨C, fun n => s n * (s n + 1), by fun_prop, fun n =>
      ⟨(oracleCircuitSize_le_mul_of_fanInAtMost (C n) (hC n).2.1).trans
        (Nat.mul_le_mul_right _ (hC n).1), (hC n).2.2⟩⟩
  · rintro ⟨C, s, hs, hC⟩
    refine ⟨C, s, hs, fun n =>
      ⟨(size_le_oracleCircuitSize (C n)).trans (hC n).1,
        Program.fanInAtMost_iff.2 fun k =>
          (Program.fanInAtMost_iff.1 (fanInAtMost_oracleCircuitSize (C n)) k).trans (hC n).1,
        (hC n).2⟩⟩

/-- The oracle circuit size class `Size^A(s)`: the languages `L` such that for every input length
`n ≥ 1`, the `n`-bit slice `L.slice n` is computed by an `A`-oracle circuit of wire-and-gate size
at most `s n`. -/
def oracleSIZE (A : Language Bool) (s : ℕ → ℝ) : Set (Language Bool) :=
  {L | ∀ n, 1 ≤ n → ∃ C : Circuit oracleSignature n 1,
    (oracleCircuitSize C : ℝ) ≤ s n ∧
      C.Computes (oracleInterpretation A) (single (L.slice n))}

/-- The infinitely-often oracle circuit size class `i.o.-Size^A(s)`: the languages `L` such that
for infinitely many input lengths `n`, the slice `L.slice n` is computed by an `A`-oracle circuit
of wire-and-gate size at most `s n`. -/
def oracleSIZEInfOften (A : Language Bool) (s : ℕ → ℝ) : Set (Language Bool) :=
  {L | ∃ᶠ n in atTop, ∃ C : Circuit oracleSignature n 1,
    (oracleCircuitSize C : ℝ) ≤ s n ∧
      C.Computes (oracleInterpretation A) (single (L.slice n))}

/-- A language avoids `i.o.-Size^A(s)` if and only if for all sufficiently large `n`, every
`A`-oracle circuit computing `L.slice n` has wire-and-gate size strictly exceeding `s n`. -/
theorem notMem_oracleSIZEInfOften_iff {A L : Language Bool} {s : ℕ → ℝ} :
    L ∉ oracleSIZEInfOften A s ↔
      ∀ᶠ n in atTop, ∀ C : Circuit oracleSignature n 1,
        C.Computes (oracleInterpretation A) (single (L.slice n)) →
          s n < (oracleCircuitSize C : ℝ) := by
  simp only [oracleSIZEInfOften, Set.mem_ofPred_eq, not_frequently, not_exists, not_and]
  exact eventually_congr (Eventually.of_forall fun _ =>
    ⟨fun h C hC => lt_of_not_ge fun hle => h C hle hC, fun h C hle hC => (h C hC).not_ge hle⟩)

/-- Every language in `Size^A(s)` belongs to `i.o.-Size^A(s)`. -/
theorem oracleSIZE_subset_oracleSIZEInfOften (A : Language Bool) (s : ℕ → ℝ) :
    oracleSIZE A s ⊆ oracleSIZEInfOften A s := fun _ hL =>
  (eventually_ge_atTop 1 |>.mono fun n hn => hL n hn).frequently

/-- Monotonicity of `i.o.-Size^A(s)` in the size bound `s`. -/
theorem oracleSIZEInfOften_mono (A : Language Bool) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) :
    oracleSIZEInfOften A s ⊆ oracleSIZEInfOften A t := fun _ hL =>
  hL.mono fun n ⟨C, hCs, hC⟩ => ⟨C, hCs.trans (hst n), hC⟩

/-- **The `(E-NP)` circuit lower-bound hypothesis** (open complexity-theoretic conjecture): there
exists a language `L ∈ E` (deterministic time `2^{O(n)}`) such that for every language `A ∈ NP`,
there exists `ε > 0` with `L ∉ i.o.-Size^A(2^{ε n})`. -/
@[expose]
def ENPHypothesis : Prop :=
  ∃ L : Language Bool, (L : Set (List Bool)) ∈ E encBits ∧
    ∀ A : Language Bool, (A : Set (List Bool)) ∈ NP encBits →
      ∃ ε : ℝ, 0 < ε ∧ L ∉ oracleSIZEInfOften A (fun n => (2 : ℝ) ^ (ε * (n : ℝ)))

/-- Characterization of `ENPHypothesis` via simultaneous gate-count and fan-in bounds: measuring
oracle circuit size by gates plus wires yields the exact same exponential hardness hypothesis as
bounding gate count and gate fan-in separately. -/
theorem enpHypothesis_iff_gate_and_fanIn :
    ENPHypothesis ↔
      ∃ L : Language Bool, (L : Set (List Bool)) ∈ E encBits ∧
        ∀ A : Language Bool, (A : Set (List Bool)) ∈ NP encBits →
          ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ∀ (s : ℕ) (C : Circuit oracleSignature n 1),
            C.Computes (oracleInterpretation A) (single (L.slice n)) →
              C.size ≤ s → C.FanInAtMost s → (2 : ℝ) ^ (ε * (n : ℝ)) < (s : ℝ) := by
  refine exists_congr fun L => and_congr_right fun _ => forall_congr' fun A =>
    imp_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨ε, hε, hhard⟩
    refine ⟨ε / 3, by positivity, ?_⟩
    rw [notMem_oracleSIZEInfOften_iff] at hhard
    filter_upwards [hhard, eventually_ge_atTop (⌈3 / ε⌉₊ + 1)] with n hn hn1 s C hcomp hsize hfan
    by_contra hle
    push Not at hle
    have h1 : (1 : ℝ) ≤ ε / 3 * (n : ℝ) := by
      have : 3 / ε ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hn1)
      rw [div_le_iff₀ hε] at this
      linarith
    set X : ℝ := (2 : ℝ) ^ (ε / 3 * (n : ℝ))
    have h2 : (2 : ℝ) ≤ X :=
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ X := Real.rpow_le_rpow_of_exponent_le one_le_two h1
    have hcost : (oracleCircuitSize C : ℝ) ≤ (s : ℝ) * ((s : ℝ) + 1) := by
      exact_mod_cast (oracleCircuitSize_le_mul_of_fanInAtMost C hfan).trans
        (Nat.mul_le_mul_right _ hsize)
    have hleX : (s : ℝ) ≤ X := hle
    have hs1 : (s : ℝ) + 1 ≤ X * X := by
      have : X + 1 ≤ 2 * X := by linarith
      have : 2 * X ≤ X * X := mul_le_mul_of_nonneg_right h2 (by linarith)
      linarith
    have hprod : (s : ℝ) * ((s : ℝ) + 1) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) :=
      calc (s : ℝ) * ((s : ℝ) + 1) ≤ X * (X * X) :=
            mul_le_mul hleX hs1 (by positivity) (by linarith)
        _ = (2 : ℝ) ^ (ε * (n : ℝ)) := by
            simp only [X, ← Real.rpow_add two_pos]
            congr 1; ring
    exact (hn C hcomp).not_ge (hcost.trans hprod)
  · rintro ⟨ε, hε, hhard⟩
    refine ⟨ε, hε, notMem_oracleSIZEInfOften_iff.2 ?_⟩
    filter_upwards [hhard] with n hn C hcomp
    exact hn (oracleCircuitSize C) C hcomp (size_le_oracleCircuitSize C)
      (fanInAtMost_oracleCircuitSize C)

/-! ### Fan-in-capped oracle signatures and generic synthesis lifting -/

/-- Operations of the oracle basis whose query gates have arity at most `r`. -/
inductive BoundedOracleOp (r : ℕ) where
  /-- A standard De Morgan operation. -/
  | base (op : Op)
  /-- An oracle query of arity `q ≤ r`. -/
  | query (q : Fin (r + 1))

/-- Arity of a fan-in-capped oracle operation. -/
abbrev BoundedOracleOp.arity {r : ℕ} : BoundedOracleOp r → ℕ
  | .base op => signature.Arity op
  | .query q => q.val

/-- The fan-in-capped oracle signature allowing De Morgan gates and oracle queries of arity at
most `r`. -/
abbrev boundedOracleSignature (r : ℕ) : Signature :=
  ⟨BoundedOracleOp r, BoundedOracleOp.arity⟩

/-- Interpretation of `boundedOracleSignature r` against an oracle language `A`. -/
noncomputable def boundedOracleInterpretation (A : Language Bool) (r : ℕ) :
    Interpretation (boundedOracleSignature r) Bool
  | .base op, x => interpretation op x
  | .query q, x => A.slice q.val x

/-- Inclusion of the De Morgan signature into `boundedOracleSignature r`. -/
def toBoundedOracle (r : ℕ) : signature.Hom (boundedOracleSignature r) :=
  ⟨BoundedOracleOp.base, fun _ => rfl⟩

/-- Inclusion of `boundedOracleSignature r` into the full `oracleSignature`. -/
def fromBoundedOracle (r : ℕ) : (boundedOracleSignature r).Hom oracleSignature :=
  ⟨fun | .base op => .base op | .query q => .query q.val,
   fun | .base _ => rfl | .query _ => rfl⟩

/-- `toBoundedOracle r` preserves Boolean gate semantics. -/
instance instPreservesToBoundedOracle (A : Language Bool) (r : ℕ) :
    (toBoundedOracle r).Preserves interpretation (boundedOracleInterpretation A r) :=
  ⟨fun _ _ => rfl⟩

/-- `fromBoundedOracle r` preserves oracle gate semantics. -/
instance instPreservesFromBoundedOracle (A : Language Bool) (r : ℕ) :
    (fromBoundedOracle r).Preserves (boundedOracleInterpretation A r) (oracleInterpretation A) :=
  ⟨fun op _ => by cases op <;> rfl⟩

/-- Translating a synthesis bound over `inputs m` along a meaning-preserving signature morphism
and feeding the `m` inputs from functions already available in `S`. -/
private theorem synthesis_lift {σ τ : Signature} {U : Type*}
    {I : Interpretation σ U} {J : Interpretation τ U} (φ : σ.Hom τ) [φ.Preserves I J]
    {m n cost : ℕ} {T : Set ((Fin m → U) → U)} (h : Synthesis I (inputs m) T cost)
    {S : Set ((Fin n → U) → U)} (g : Fin m → (Fin n → U) → U) (hg : ∀ i, g i ∈ S) :
    Synthesis J S ((fun f x => f fun i => g i x) '' T) cost := by
  obtain ⟨k, p, hk, -, hT⟩ := h 0 .empty (inputs_subset_available .empty)
  intro g₁ p₁ hp₁
  choose wires hw using fun i => mem_available.mp (hp₁ (hg i))
  refine ⟨g₁ + k, p₁.append wires (p.mapOp φ), by omega, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, hw'⟩ := mem_available.mp hf
    exact mem_available.mpr ⟨w.castAdd k, fun x =>
      (Program.trace_append_castAdd p₁ wires J x (p.mapOp φ) w).trans (hw' x)⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨w, hwf⟩ := mem_available.mp (hT hf)
    refine mem_available.mpr ⟨Program.appendedWire wires w, fun x => ?_⟩
    rw [Program.trace_append_appendedWire]
    have hargs : (fun i => p₁.trace J x (wires i)) = fun i => g i x := funext fun i => hw i x
    rw [hargs]
    cases w with
    | input i => exact hwf fun j => g j x
    | gate j =>
      exact (congrFun (Program.eval_mapOp p (fun i => g i x)) j).trans (hwf fun i => g i x)

private theorem isComplete_of_hom {σ τ : Signature} {U : Type*}
    (I : Interpretation σ U) {J : Interpretation τ U} (φ : σ.Hom τ) [φ.Preserves I J]
    [I.IsComplete] : J.IsComplete where
  exists_computes_single f :=
    let ⟨c, hc⟩ := Interpretation.IsComplete.exists_computes_single (I := I) f
    ⟨c.mapOp φ, hc.mapOp⟩

/-- Functional completeness of `boundedOracleInterpretation A r`. -/
instance instIsCompleteBoundedOracleInterpretation (A : Language Bool) (r : ℕ) :
    (boundedOracleInterpretation A r).IsComplete :=
  isComplete_of_hom interpretation (toBoundedOracle r)

/-- Scoped functional completeness of `oracleInterpretation A`. -/
scoped instance instIsCompleteOracleInterpretation (A : Language Bool) :
    (oracleInterpretation A).IsComplete :=
  isComplete_of_hom interpretation toOracle

private theorem complexity_le_of_hom {σ τ : Signature} {U : Type*}
    {I : Interpretation σ U} {J : Interpretation τ U} (φ : σ.Hom τ) [φ.Preserves I J]
    [I.IsComplete] [J.IsComplete] {n m : ℕ} (f : (Fin n → U) → Fin m → U) :
    complexity J f ≤ complexity I f := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := I) (f := f)
  exact (complexity_le_of_computes (c.mapOp φ) hc.mapOp).trans (by rw [Circuit.size_mapOp, hsize])

private theorem fanInAtMost_fromBoundedOracle {n m r : ℕ}
    (c : Circuit (boundedOracleSignature r) n m) :
    (c.mapOp (fromBoundedOracle r)).FanInAtMost (max 2 r) := by
  rw [Circuit.fanInAtMost_mapOp, Circuit.FanInAtMost, Program.fanInAtMost_iff]
  intro k
  cases (c.program.lines k).op with
  | base op =>
    have : signature.Arity op ≤ 2 := by cases op <;> simp
    exact this.trans (le_max_left 2 r)
  | query q => exact (Nat.lt_succ_iff.1 q.isLt).trans (le_max_right 2 r)

private theorem oracleCircuitSize_fromBoundedOracle_le {n m r : ℕ}
    (c : Circuit (boundedOracleSignature r) n m) :
    oracleCircuitSize (c.mapOp (fromBoundedOracle r)) ≤ c.size * (max 2 r + 1) := by
  simpa only [Circuit.size_mapOp] using
    oracleCircuitSize_le_mul_of_fanInAtMost (c.mapOp (fromBoundedOracle r))
      (fanInAtMost_fromBoundedOracle c)

/-- The slice `A.slice r` has circuit complexity at most `1` in `boundedOracleInterpretation A r`,
computed by a single arity-`r` oracle query gate. -/
theorem complexity_boundedOracle_slice_le_one (A : Language Bool) (r : ℕ) :
    complexity (boundedOracleInterpretation A r) (single (A.slice r)) ≤ 1 := by
  let op : BoundedOracleOp r := .query ⟨r, Nat.lt_succ_self r⟩
  let c : Circuit (boundedOracleSignature r) r 1 := Circuit.oneGate op id
  have hc : c.Computes (boundedOracleInterpretation A r) (single (A.slice r)) :=
    fun _ => funext fun i => by obtain rfl : i = 0 := Subsingleton.elim i 0; rfl
  exact complexity_le_of_computes c hc

/-! ### Relativized synthesis, Sudan–Trevisan–Vadhan, and Nisan–Wigderson reconstruction -/

section RelativizedSynthesis

variable {τ : Signature} {J : Interpretation τ Bool}
variable (φ : signature.Hom τ) [hφ : φ.Preserves interpretation J]

include hφ in
private theorem synthesis_const_hom {n : ℕ} {S : Set (BooleanFunction n)} (b : Bool) :
    Synthesis J S {fun _ => b} 1 := by
  simpa using synthesis_lift φ (m := 0) (Synthesis.const (s := inputs 0) b)
    (S := S) Fin.elim0 fun i => i.elim0

include hφ in
private theorem synthesis_not_hom {n a : ℕ} {S : Set (BooleanFunction n)} {f : BooleanFunction n}
    (hf : Synthesis J S {f} a) : Synthesis J S {fun x => !f x} (a + 1) := by
  have h1 : Synthesis interpretation (inputs 1) {fun y : Fin 1 → Bool => !y 0} 1 :=
    (Synthesis.of_mem (s := inputs 1) ⟨0, rfl⟩).not
  exact hf.trans (by
    simpa using synthesis_lift φ h1 (S :=
      S ∪ {f}) (fun _ => f) (fun _ => Set.mem_union_right _ rfl))

include hφ in
private theorem synthesis_atLeast_hom {n k j : ℕ} {S : Set (BooleanFunction n)}
    (f : ℕ → BooleanFunction n) (hf : ∀ i < k, f i ∈ S) (hj : j ≤ k + 1) :
    Synthesis J S {atLeast f k j} (2 + k * (2 * (k + 2))) := by
  let proj : ℕ → BooleanFunction k := fun l y => if hl : l < k then y ⟨l, hl⟩ else false
  have hbase : Synthesis interpretation (inputs k) {atLeast proj k j} (2 + k * (2 * (k + 2))) :=
    synthesis_atLeast proj (fun l hl => ⟨⟨l, hl⟩, funext fun y => by simp [proj, hl]⟩) hj
  refine (synthesis_lift φ hbase (S := S) (fun i : Fin k => f i.val)
    (fun i => hf i.val i.isLt)).mono Set.Subset.rfl ?_ le_rfl
  rw [Set.image_singleton, Set.singleton_subset_iff, Set.mem_singleton_iff]
  funext x
  simp only [atLeast, decide_eq_decide]
  have hcard : #{l ∈ range k | proj l (fun i => f i.val x) = true} =
      #{l ∈ range k | f l x = true} :=
    congrArg card (filter_congr fun l hl => by simp [proj, mem_range.1 hl])
  rw [hcard]

include hφ in
private theorem synthesis_bitBlast_hom {F : Type*} {w N n c : ℕ} (enc : F ≃ BitString w)
    {ι : Type*} [Finite ι] (Ψ : ι → (Fin N → F) → F)
    (hΨ : Synthesis (fullInterpretation (k := 2)) (inputs N) (Set.range Ψ) c)
    {S : Set (BooleanFunction n)} (ψ : Fin N → (Fin n → Bool) → F)
    (hψ : ∀ i j, bitsOf enc (ψ i) j ∈ S) :
    Synthesis J S
      (Set.range fun ij : ι × Fin w => bitsOf enc (fun x => Ψ ij.1 fun i => ψ i x) ij.2)
      (c * bitBlastCost w) := by
  let inp : Fin N → (Fin (N * w) → Bool) → F :=
    fun i y => enc.symm fun j => y (finProdFinEquiv (i, j))
  have hinp : ∀ i j, bitsOf enc (inp i) j ∈ inputs (N * w) := fun i j =>
    ⟨finProdFinEquiv (i, j), funext fun y => by simp [bitsOf, inp]⟩
  have hbase := Synthesis.bitBlast_synthesis enc enc.symm enc.symm_apply_apply Ψ hΨ inp hinp
  let g : Fin (N * w) → BooleanFunction n :=
    fun idx => bitsOf enc (ψ (finProdFinEquiv.symm idx).1) (finProdFinEquiv.symm idx).2
  refine (synthesis_lift φ hbase (S := S) g (fun _ => hψ _ _)).mono Set.Subset.rfl ?_ le_rfl
  rintro _ ⟨ij, rfl⟩
  refine ⟨bitsOf enc (fun y => Ψ ij.1 fun i => inp i y) ij.2, ⟨ij, rfl⟩, funext fun x => ?_⟩
  simp only [bitsOf, inp, g, Equiv.symm_apply_apply]

include hφ in
private theorem complexity_not_hom_le [J.IsComplete] {n : ℕ} (f : BooleanFunction n) :
    complexity J (single fun x => !f x) ≤ complexity J (single f) + 1 := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := J) (f := single f)
  have h1 : Synthesis J (inputs n) {f} c.size :=
    (Synthesis.circuit (I := J) (s := inputs n) c (fun i x => x i) (fun i => ⟨i, rfl⟩)).mono
      Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, funext fun x => congrFun (hc x) 0⟩) le_rfl
  exact hsize ▸ (synthesis_not_hom φ h1).complexity_le

include hφ in
private theorem complexity_substitute_hom_le [J.IsComplete] {n N : ℕ}
    (ρ : Fin N → Fin n ⊕ Bool) (f : BooleanFunction N) :
    complexity J (single fun x => f (substitute ρ x)) ≤ complexity J (single f) + 2 := by
  have h := complexity_comp_le (I := J) (substitute ρ) (single f)
  rw [add_comm] at h
  exact h.trans (Nat.add_le_add_left
    ((complexity_le_of_hom φ (substitute ρ)).trans (complexity_substitute_le_two ρ)) _)

include hφ in
private theorem exists_complexity_hom_le_of_agree_prefix [J.IsComplete] {n N : ℕ} (hle : n ≤ N)
    (E : BooleanFunction n) (g : BooleanFunction N) {δ : ℝ}
    (hagree : δ * 2 ^ N < #{y | g y = E fun i => y (Fin.castLE hle i)}) :
    ∃ C : BooleanFunction n, complexity J (single C) ≤ complexity J (single g) + 2 ∧
      δ * 2 ^ n < #{x | C x = E x} := by
  classical
  set p := N - n
  have hN : n + p = N := Nat.add_sub_cancel' hle
  let ρ : BitString p → Fin N → Fin n ⊕ Bool := fun z k => appendInputs z (Fin.cast hN.symm k)
  have hρ : ∀ z x, substitute (ρ z) x = fun k => Fin.append x z (Fin.cast hN.symm k) :=
    fun z x => funext fun k => congrFun (substitute_appendInputs z x) (Fin.cast hN.symm k)
  have hleft : ∀ (x : BitString n) (z : BitString p) (i : Fin n),
      Fin.append x z (Fin.cast hN.symm (Fin.castLE hle i)) = x i := fun x z i => by
    rw [show Fin.cast hN.symm (Fin.castLE hle i) = Fin.castAdd p i from Fin.ext rfl,
      Fin.append_left]
  have hinv (y : BitString N) : (fun k => Fin.append (fun i => y (Fin.castLE hle i))
      (fun j => y (Fin.cast hN (Fin.natAdd n j))) (Fin.cast hN.symm k)) = y := by
    funext k
    obtain ⟨k', rfl⟩ : ∃ k', k = Fin.cast hN k' := ⟨Fin.cast hN.symm k, by simp⟩
    exact Fin.addCases
      (fun i => by simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]; rfl)
      (fun j => by simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]) k'
  have hsplit : #{y | g y = E fun i => y (Fin.castLE hle i)} =
      ∑ z : BitString p, #{x | g (substitute (ρ z) x) = E x} := by
    rw [← card_sigma]
    refine card_nbij'
      (fun y => ⟨fun j => y (Fin.cast hN (Fin.natAdd n j)), fun i => y (Fin.castLE hle i)⟩)
      (fun q k => Fin.append q.2 q.1 (Fin.cast hN.symm k))
      (fun y hy => ?_) (fun q hq => ?_) (fun y _ => hinv y) (fun ⟨z, x⟩ _ => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma,
        Set.mem_sigma_iff, mem_coe, hρ] at hy ⊢
      rwa [hinv]
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_sigma,
        Set.mem_sigma_iff, mem_coe, hρ] at hq ⊢
      rwa [show (fun i => Fin.append q.2 q.1 (Fin.cast hN.symm (Fin.castLE hle i))) = q.2 from
        funext (hleft q.2 q.1)]
    · exact Sigma.ext
        (funext fun j => by simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.append_right])
        (heq_of_eq (funext (hleft x z)))
  have hex : ∃ z : BitString p, δ * 2 ^ n < #{x | g (substitute (ρ z) x) = E x} := by
    by_contra hall
    push Not at hall
    have hsum : (#{y | g y = E fun i => y (Fin.castLE hle i)} : ℝ) ≤
        ∑ _z : BitString p, δ * 2 ^ n := by
      rw [hsplit, Nat.cast_sum]; exact sum_le_sum fun z _ => hall z
    rw [sum_const, card_univ, nsmul_eq_mul] at hsum
    have hcard : (Fintype.card (BitString p) : ℝ) * (δ * 2 ^ n) = δ * 2 ^ N := by
      rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat, mul_left_comm, ← pow_add, ← hN, add_comm]
    linarith
  obtain ⟨z, hz⟩ := hex
  exact ⟨fun x => g (substitute (ρ z) x), complexity_substitute_hom_le φ (ρ z) g, hz⟩

private def GenBitSynthesis {F : Type*} {w m : ℕ} (J : Interpretation τ Bool)
    (enc : F ≃ BitString w) (G : (Fin m → F) → F) (cost : ℕ) : Prop :=
  ∀ (n : ℕ) (S : Set (BooleanFunction n)) (ψ : Fin m → (Fin n → Bool) → F),
    (∀ i j, bitsOf enc (ψ i) j ∈ S) →
      Synthesis J S (Set.range fun j => bitsOf enc (fun v => G fun i => ψ i v) j) cost

private theorem strictMajorityOn_eq_atLeast' {n : ℕ} {ι : Type*} (T : Finset ι)
    (vote : ι → BooleanFunction n) (v : Fin n → Bool) :
    BitString.strictMajorityOn T (fun i => vote i v) =
      atLeast (fun l => if h : l < #T then vote (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
        #T (#T / 2 + 1) v := by
  classical
  simp only [BitString.strictMajorityOn, atLeast]
  congr 1; rw [Nat.lt_iff_add_one_le]; congr 1
  refine card_bij (fun i hi => (T.equivFin ⟨i, (mem_filter.1 hi).1⟩ : ℕ)) (fun i hi => ?_)
    (fun _ _ _ _ h => congrArg Subtype.val (T.equivFin.injective (Fin.ext h))) (fun l hl => ?_)
  · rw [mem_filter] at hi ⊢
    exact ⟨mem_range.2 (T.equivFin _).2, by rw [dite_eq_left (T.equivFin _).2]; simpa using hi.2⟩
  · rw [mem_filter, mem_range] at hl
    obtain ⟨hl, hv⟩ := hl
    rw [dite_eq_left hl] at hv
    exact ⟨T.equivFin.symm ⟨l, hl⟩, mem_filter.2 ⟨(T.equivFin.symm ⟨l, hl⟩).2, hv⟩, by simp⟩

include hφ in
private theorem bitSynthesis_glPredictor_hom [J.IsComplete] {F : Type*} {w m : ℕ}
    (enc : F ≃ BitString w) {C : BooleanFunction (m * w + w)} {sC : ℕ}
    (hC : complexity J (single C) ≤ sC) {K : ℕ} (masks : Fin K → BitString w)
    (guess : BitString K) :
    GenBitSynthesis J enc (glPredictor enc C masks guess) (glCost w K sC) := by
  classical
  intro n S ψ hψ
  obtain ⟨c, hc, hsize⟩ := complexity_le_iff.1 hC
  let xb : Fin (m * w) → BooleanFunction n := fun k v => BitString.pointBits enc (fun i => ψ i v) k
  have hxb : ∀ k, xb k ∈ S := fun k => hψ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hconst : Synthesis J S ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (synthesis_const_hom φ (S := S) true).union (synthesis_const_hom φ (S := S) false)
  set S₁ := S ∪ ({fun _ => true} ∪ {fun _ => false})
  let bitFn : Fin w → BooleanFunction n := fun j v =>
    GoldreichLevin.candidate (fun r => C (Fin.append (fun k => xb k v) r)) masks guess j
  have hbit (j : Fin w) : Synthesis J S₁ {bitFn j} (glBitCost K sC) := by
    have hvote (r : BitString w) (bit : Bool) :
        Synthesis J S₁ {fun v => C (Fin.append (fun k => xb k v) r) ^^ bit} (sC + 1) := by
      let g : Fin (m * w + w) → BooleanFunction n := Fin.append xb fun k _ => r k
      have hg : ∀ k, g k ∈ S₁ := fun k => Fin.addCases
        (fun i => by simp only [g, Fin.append_left]; exact Set.mem_union_left _ (hxb i))
        (fun i => by
          simp only [g, Fin.append_right]
          cases r i
          · exact Set.mem_union_right _ (Set.mem_union_right _ rfl)
          · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)) k
      have heval : (fun v => c.eval J (fun k => g k v) 0) =
          fun v => C (Fin.append (fun k => xb k v) r) := funext fun v => by
        rw [hc]; simp only [single_apply]; congr 1 with k
        exact Fin.addCases (fun _ => by simp [g]) (fun _ => by simp [g]) k
      have h1 : Synthesis J S₁ {fun v => C (Fin.append (fun k => xb k v) r)} sC :=
        (Synthesis.circuit (I := J) (s := S₁) c g hg).mono Set.Subset.rfl
          (Set.singleton_subset_iff.2 ⟨0, heval⟩) hsize
      cases bit
      · simpa using h1.mono Set.Subset.rfl Set.Subset.rfl (Nat.le_succ _)
      · simpa using synthesis_not_hom φ h1
    set T := GoldreichLevin.nonemptySubsets K
    let V : Finset (Fin K) → BooleanFunction n := fun t v =>
      C (Fin.append (fun k => xb k v) (Pi.single j 1 + ∑ l ∈ t, masks l)) ^^ ∑ l ∈ t, guess l
    have hvotes := Synthesis.biUnion (I := J) (s := S₁) T (fun t => {V t}) (fun _ => sC + 1)
      fun _ _ => hvote _ _
    let seq : ℕ → BooleanFunction n :=
      fun l => if h : l < #T then V (T.equivFin.symm ⟨l, h⟩) else fun _ => false
    have hmaj := synthesis_atLeast_hom (J := J) φ (S := S₁ ∪ ⋃ t ∈ T, {V t})
      (k := #T) (j := #T / 2 + 1) seq (fun l hl => by
        simp only [seq, hl, dite_true]
        exact Set.mem_union_right _ (Set.mem_biUnion (T.equivFin.symm ⟨l, hl⟩).2 rfl)) (by omega)
    refine (hvotes.trans hmaj).mono Set.Subset.rfl (Set.singleton_subset_iff.2 ?_) ?_
    · funext v; dsimp only [bitFn, seq]; exact strictMajorityOn_eq_atLeast' T V v
    · simp only [sum_const, smul_eq_mul, glBitCost, T, GoldreichLevin.card_nonemptySubsets, le_refl]
  have hall := Synthesis.iUnion (I := J) (s := S₁) (fun j => {bitFn j})
    (fun _ => glBitCost K sC) hbit
  refine (hconst.trans hall).mono Set.Subset.rfl ?_ ?_
  · rintro _ ⟨j, rfl⟩
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [Set.mem_singleton_iff]; funext v; simp [bitsOf, glPredictor, bitFn, xb]
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, glCost_eq, le_refl]

include hφ in
private theorem bitSynthesis_lineListDecode_hom {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {w m SG : ℕ} {enc : F ≃ BitString w} {G : (Fin m → F) → F}
    (hG : GenBitSynthesis J enc G SG) (d D : ℕ) (z : Fin m → F) (a : F) :
    GenBitSynthesis J enc (Code.lineListDecode G d D z a)
      (lineCost w (Fintype.card F) m #(Sudan.monomials d D) (D / d) d SG) := by
  intro n S ψ hψ
  set q := Fintype.card F
  let ΨA : Option (F × Fin m) → (Fin m → F) → F := fun o v => match o with
    | none => LinearAlgebra.firstNonzero (z - fun i => v i)
    | some (t, i) =>
      ((fun i => v i) + t • (LinearAlgebra.firstNonzero (z - fun i => v i))⁻¹ •
        (z - fun i => v i)) i
  have hA : Synthesis (fullInterpretation (k := 2)) (inputs m) (Set.range ΨA)
      ((q + 5) * m + 2) :=
    Synthesis.full_linePoints (s := inputs m) (fun i v => v i) (fun i => ⟨i, rfl⟩) z
  have hA' := synthesis_bitBlast_hom (J := J) φ enc ΨA hA ψ hψ
  set TA := Set.range fun oj : Option (F × Fin m) × Fin w =>
    bitsOf enc (fun x => ΨA oj.1 fun i => ψ i x) oj.2
  let pt : F → Fin m → (Fin n → Bool) → F := fun t i x => ΨA (some (t, i)) fun k => ψ k x
  have hB : Synthesis J (S ∪ TA)
      (⋃ t : F, Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j) (q * SG) := by
    simpa [q] using Synthesis.iUnion (I := J) (s := S ∪ TA)
      (fun t : F => Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j)
      (fun _ => SG) (fun t => hG n (S ∪ TA) (pt t) fun i j =>
        Set.mem_union_right _ ⟨(some (t, i), j), rfl⟩)
  set TB := ⋃ t : F, Set.range fun j => bitsOf enc (fun x => G fun i => pt t i x) j
  let e := Fintype.equivFin F
  let ΨC : Unit → (Fin (q + 1) → F) → F := fun _ v =>
    hintDecode id (fun t => v (Fin.castSucc (e t))) d D (v (Fin.last q)) a
  have hC : Synthesis (fullInterpretation (k := 2)) (inputs (q + 1)) (Set.range ΨC)
      (1 + hintDecodeCost q q #(Sudan.monomials d D) (D / d) d) := by
    have hconst := Synthesis.full_const (k := 2) (s := inputs (q + 1)) a
    have hdec := Synthesis.full_hintDecode (s := inputs (q + 1) ∪ {fun _ => a}) (ι := F) id
      (fun t v => v (Fin.castSucc (e t)))
      (fun t => Set.mem_union_left _ ⟨Fin.castSucc (e t), rfl⟩)
      (τ := fun v => v (Fin.last q)) (Set.mem_union_left _ ⟨Fin.last q, rfl⟩)
      (Set.mem_union_right _ rfl) d D
    exact (hconst.trans hdec).mono Set.Subset.rfl (by rintro _ ⟨_, rfl⟩; rfl) le_rfl
  let ψC : Fin (q + 1) → (Fin n → Bool) → F :=
    Fin.lastCases (fun x => ΨA none fun i => ψ i x) fun k x => G fun i => pt (e.symm k) i x
  have hψC : ∀ k j, bitsOf enc (ψC k) j ∈ (S ∪ TA) ∪ TB := fun k j =>
    Fin.lastCases
      (by simp only [ψC, Fin.lastCases_last]
          exact Set.mem_union_left _ (Set.mem_union_right _ ⟨(none, j), rfl⟩))
      (fun k => by
        simp only [ψC, Fin.lastCases_castSucc]
        exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨e.symm k, j, rfl⟩)) k
  have hC' := synthesis_bitBlast_hom (J := J) φ enc ΨC hC ψC hψC
  refine (hA'.trans (hB.comp hC')).mono Set.Subset.rfl ?_ (by unfold lineCost; nlinarith)
  rintro _ ⟨j, rfl⟩
  refine Or.inr ⟨((), j), funext fun x => ?_⟩
  simp only [bitsOf, ΨC, ψC, Fin.lastCases_last, Fin.lastCases_castSucc, Equiv.symm_apply_apply,
    Code.lineListDecode, pt, ΨA]

include hφ in
private theorem bitSynthesis_selfCorrect_hom {F : Type*} [Field F] [DecidableEq F]
    {w m S1 d L : ℕ} {enc : F ≃ BitString w} {C1 : (Fin m → F) → F}
    (hC1 : GenBitSynthesis J enc C1 S1) (ν : Fin (d + 1) ↪ F)
    (V : Fin (3 ^ L) → Fin m → F) :
    GenBitSynthesis J enc (fun x => majTree L fun τ => lagrangeDecode ν C1 x (V τ))
      (selfCorrectCost w m d L S1) := by
  intro n S ψ hψ
  let ΨA : (Fin (3 ^ L) × Fin (d + 1)) × Fin m → (Fin m → F) → F :=
    fun o v => v o.2 + ν o.1.2 * V o.1.1 o.2
  have hA : Synthesis (fullInterpretation (k := 2)) (inputs m) (Set.range ΨA)
      (m * (3 ^ L * (d + 1))) := by
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using
      Synthesis.family (I := fullInterpretation (k := 2)) (s := inputs m) ΨA (fun _ => 1)
        fun o => Synthesis.full_unary (fun a => a + ν o.1.2 * V o.1.1 o.2) ⟨o.2, rfl⟩
  have hA' := synthesis_bitBlast_hom (J := J) φ enc ΨA hA ψ hψ
  set TA := Set.range fun oj : ((Fin (3 ^ L) × Fin (d + 1)) × Fin m) × Fin w =>
    bitsOf enc (fun x => ΨA oj.1 fun i => ψ i x) oj.2
  let pt : Fin (3 ^ L) × Fin (d + 1) → Fin m → (Fin n → Bool) → F :=
    fun τi k x => ΨA (τi, k) fun i => ψ i x
  have hB : Synthesis J (S ∪ TA)
      (⋃ τi : Fin (3 ^ L) × Fin (d + 1),
        Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j)
      (3 ^ L * (d + 1) * S1) := by
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using
      Synthesis.iUnion (I := J) (s := S ∪ TA)
        (fun τi : Fin (3 ^ L) × Fin (d + 1) =>
          Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j)
        (fun _ => S1) (fun τi => hC1 n (S ∪ TA) (pt τi) fun k j =>
          Set.mem_union_right _ ⟨((τi, k), j), rfl⟩)
  set TB := ⋃ τi : Fin (3 ^ L) × Fin (d + 1),
    Set.range fun j => bitsOf enc (fun x => C1 fun k => pt τi k x) j
  let ΨC : Unit → (Fin (3 ^ L * (d + 1)) → F) → F := fun _ v =>
    majTree L fun τ => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i))
  have hC : Synthesis (fullInterpretation (k := 2)) (inputs (3 ^ L * (d + 1))) (Set.range ΨC)
      (3 ^ L * (2 * (d + 1) + 1) + (2 * 3 ^ L - 2)) := by
    have hsums := Synthesis.family (I := fullInterpretation (k := 2))
      (s := inputs (3 ^ L * (d + 1)))
      (fun τ v => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i)))
      (fun _ => 2 * (d + 1) + 1) fun τ => by
        simpa using Synthesis.full_weightedSum (s := inputs (3 ^ L * (d + 1))) (lagrangeWeight ν)
          (fun i v => v (finProdFinEquiv (τ, i))) fun _ => ⟨_, rfl⟩
    have htree := Synthesis.full_majTree (s := inputs (3 ^ L * (d + 1)) ∪
        Set.range fun τ (v : Fin (3 ^ L * (d + 1)) → F) =>
          ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i))) L
      (fun τ v => ∑ i, lagrangeWeight ν i * v (finProdFinEquiv (τ, i)))
      fun τ => Set.mem_union_right _ ⟨τ, rfl⟩
    exact (hsums.trans htree).mono Set.Subset.rfl (by rintro _ ⟨_, rfl⟩; rfl)
      (by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, le_refl])
  let ψC : Fin (3 ^ L * (d + 1)) → (Fin n → Bool) → F :=
    fun k x => C1 fun i => pt (finProdFinEquiv.symm k) i x
  have hψC : ∀ k j, bitsOf enc (ψC k) j ∈ (S ∪ TA) ∪ TB :=
    fun k j => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨finProdFinEquiv.symm k, j, rfl⟩)
  have hC' := synthesis_bitBlast_hom (J := J) φ enc ΨC hC ψC hψC
  refine (hA'.trans (hB.comp hC')).mono Set.Subset.rfl ?_ (by unfold selfCorrectCost; nlinarith)
  rintro _ ⟨j, rfl⟩
  refine Or.inr ⟨((), j), funext fun x => ?_⟩
  simp only [bitsOf, ΨC, ψC, Equiv.symm_apply_apply, lagrangeDecode, pt, ΨA]; rfl

private theorem two_mul_mul_le' {q Q a ε D : ℝ} (hq : 0 ≤ q) (hQ : 0 ≤ Q) {K : ℕ}
    (hgl : ε * Q ≤ 2 ^ (K + 2) * a) (hmargin : 2 ^ (K + 3) * D ≤ q * ε) : 2 * D * Q ≤ q * a := by
  refine le_of_mul_le_mul_left (a := (2 : ℝ) ^ (K + 2)) ?_ (by positivity)
  calc 2 ^ (K + 2) * (2 * D * Q) = 2 ^ (K + 3) * D * Q := by ring
    _ ≤ q * ε * Q := mul_le_mul_of_nonneg_right hmargin hQ
    _ = q * (ε * Q) := by ring
    _ ≤ q * (2 ^ (K + 2) * a) := mul_le_mul_of_nonneg_left hgl hq
    _ = 2 ^ (K + 2) * (q * a) := by ring

private theorem lineErrors_le' {q Q a ε D δ : ℝ} (hq : 1 < q) (hQ : 1 ≤ Q) (ha : 0 < a)
    (hε : 0 < ε) {K : ℕ} (hgl : ε * Q ≤ 2 ^ (K + 2) * a)
    (hmargin : 2 ^ (K + 3) * D ≤ q * ε) (hδ : 0 ≤ δ) (hδD : δ ≤ D) :
    1 + (q * a * (Q - 1) / (q * a / Q - D) ^ 2 + Q * (Q - 1) * δ / (q - 1)) / Q ≤
      Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) := by
  have hQpos : 0 < Q := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set μ := q * a / Q
  have hμpos : 0 < μ := by positivity
  have hμ : 2 * D ≤ μ := (le_div_iff₀ hQpos).2 (two_mul_mul_le' hq0.le hQpos.le hgl hmargin)
  have hμD : μ / 2 ≤ μ - D := by linarith only [hμ]
  have hsq : μ ^ 2 / 4 ≤ (μ - D) ^ 2 := by
    simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (by positivity) hμD 2
  have hterm1 : q * a * (Q - 1) / (μ - D) ^ 2 / Q ≤ Q * (2 ^ (K + 4) / (q * ε)) := by
    have hμD' : 0 < μ - D := by linarith only [hμpos, hμD]
    rw [div_div, div_le_iff₀ (by positivity)]
    have hμsq : μ ^ 2 * Q ^ 2 = (q * a) ^ 2 := by simp only [μ]; field_simp
    have key : q * a * (Q - 1) ≤ q * a * Q :=
      mul_le_mul_of_nonneg_left (by linarith only [hQ]) (by positivity)
    have hstep : q * a * Q * 4 ≤ Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) := by
      rw [show Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) = 2 ^ (K + 4) * (μ ^ 2 * Q ^ 2) /
        (q * ε) by field_simp, hμsq, le_div_iff₀ (by positivity)]
      calc q * a * Q * 4 * (q * ε) = 4 * q * (q * a) * (ε * Q) := by ring
        _ ≤ 4 * q * (q * a) * (2 ^ (K + 2) * a) := mul_le_mul_of_nonneg_left hgl (by positivity)
        _ = 2 ^ (K + 4) * (q * a) ^ 2 := by ring
    calc q * a * (Q - 1) ≤ q * a * Q := key
      _ = q * a * Q * 4 / 4 := by ring
      _ ≤ Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) / 4 := by gcongr
      _ = Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 / 4 * Q) := by ring
      _ ≤ Q * (2 ^ (K + 4) / (q * ε)) * ((μ - D) ^ 2 * Q) := by gcongr
  have hterm2 : Q * (Q - 1) * δ / (q - 1) / Q ≤ Q * (D / (q - 1)) := by
    rw [div_div, div_le_iff₀ (by positivity)]
    calc Q * (Q - 1) * δ ≤ Q * Q * D := by gcongr; linarith only [hQ]
      _ = Q * (D / (q - 1)) * ((q - 1) * Q) := by field_simp
  rw [add_div]
  calc 1 + (q * a * (Q - 1) / (μ - D) ^ 2 / Q + Q * (Q - 1) * δ / (q - 1) / Q)
      ≤ 1 + (Q * (2 ^ (K + 4) / (q * ε)) + Q * (D / (q - 1))) := by linarith only [hterm1, hterm2]
    _ = Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) := by field_simp; ring

private theorem reconstruction_ranges' {q d D K m : ℕ} {ε : ℝ} (hq2 : 2 ≤ q) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hn : q < #(Sudan.monomials d D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ q * ε)
    (herr : 6 * ((d : ℝ) + 1) * (1 / (q : ℝ) ^ m + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) ≤ 1) :
    1 ≤ D ∧ D < q ∧ d + 1 ≤ q - 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq2
  have hD1 : 1 ≤ D := by
    by_contra! hD0
    have : #(Sudan.monomials d D) ≤ 1 := card_le_one.2 fun x hx y hy => by
      rw [Sudan.mem_monomials] at hx hy; ext <;> omega
    omega
  have hDq : D < q := by
    have hqε : (q : ℝ) * ε ≤ q / 2 := by
      linarith only [mul_le_mul_of_nonneg_left hε1 (by linarith only [hq1] : (0 : ℝ) ≤ q)]
    have h8 : (8 : ℝ) ≤ 2 ^ (K + 3) :=
      (show (8 : ℝ) = 2 ^ 3 by norm_num) ▸ pow_le_pow_right₀ (by norm_num) (by omega)
    have h8D : 8 * (D : ℝ) ≤ q / 2 :=
      (mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg D)).trans (hmargin.trans hqε)
    exact_mod_cast (by linarith only [h8D, hq1] : (D : ℝ) < q)
  refine ⟨hD1, hDq, ?_⟩
  have hpos_sum : (0 : ℝ) ≤ 1 / (q : ℝ) ^ m + 2 ^ (K + 4) / (q * ε) := by positivity
  have h6 : 6 * ((d : ℝ) + 1) * (D / (q - 1)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith only [hpos_sum]) (by positivity)).trans herr
  have h6' : 6 * ((d : ℝ) + 1) * D ≤ q - 1 := by
    rwa [mul_div_assoc', div_le_one (by linarith only [hq1])] at h6
  have h6d : 6 * ((d : ℝ) + 1) ≤ q - 1 :=
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hD1)).trans h6'
  rw [← Nat.cast_le (α := ℝ), Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  linarith [Nat.cast_nonneg (α := ℝ) d]

include hφ in
private theorem complexity_hom_le_pow_of_agree_hardnessEncode [J.IsComplete]
    {F : Type*} [Field F] [Fintype F] {w m b s K D L : ℕ} {ε : ℝ}
    (enc : F ≃ BitString w) (h : BitString b ↪ F) (f : BooleanFunction (m * b))
    {C : BooleanFunction (m * w + w)} (hC : complexity J (single C) ≤ s) (hε : 0 < ε)
    (hagree : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ #{y | C y = hardnessEncode enc h f y})
    (hK : 0 < K) (hsize : (w : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1 : ℕ))
    (hd : 1 ≤ m * (2 ^ b - 1))
    (hn : Fintype.card F < #(Sudan.monomials (m * (2 ^ b - 1)) D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ Fintype.card F * ε)
    (herr : 6 * ((m * (2 ^ b - 1) : ℕ) + 1 : ℝ) * (1 / (Fintype.card F : ℝ) ^ m +
      2 ^ (K + 4) / (Fintype.card F * ε) + D / (Fintype.card F - 1)) ≤ 1)
    (hL : m * b ≤ 2 ^ L) :
    complexity J (single f) ≤
      2 ^ 11 * 3 ^ L * m * w ^ 2 * Fintype.card F ^ 9 * 4 ^ K * (s + 1) := by
  classical
  set d := m * (2 ^ b - 1)
  set q := Fintype.card F
  set p := truthTableExtension h f
  have hp : p ∈ reedMuller F m d := truthTableExtension_mem_reedMuller h f
  have hqw : q = 2 ^ w := (Fintype.card_congr enc).trans BitString.card
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq2
  obtain ⟨masks, guess, hgl⟩ := exists_glPredictor_agree enc h f C hε hagree hK hsize
  set G := glPredictor enc C masks guess
  have hε1 : ε ≤ 1 / 2 := by
    have hN : (#{y | C y = hardnessEncode enc h f y} : ℝ) ≤ 2 ^ (m * w + w) := by
      exact_mod_cast (card_le_univ _).trans_eq BitString.card
    linarith only [le_of_mul_le_mul_right
      (hagree.trans (by linarith only [hN]) : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ 1 * 2 ^ (m * w + w))
      (by positivity : (0 : ℝ) < 2 ^ (m * w + w))]
  obtain ⟨hD1, hDq, hdq⟩ := reconstruction_ranges' hq2 hε hε1 hn hmargin herr
  set Q : ℝ := (q : ℝ) ^ m
  have hQ : (Fintype.card (Fin m → F) : ℝ) = Q := by simp [Q, q]
  have hQ2 : (2 : ℝ) ^ (m * w) = Q := by simp [Q, hqw, ← pow_mul, mul_comm]
  have hQ1 : (1 : ℝ) ≤ Q := one_le_pow₀ hq1.le
  set a := (#{x | G x = p x} : ℕ)
  have ha : ε * Q ≤ 2 ^ (K + 2) * a := by rw [← hQ2]; exact hgl
  have hapos : (0 : ℝ) < a :=
    pos_of_mul_pos_right ((by positivity : (0 : ℝ) < ε * Q).trans_le ha) (by positivity)
  have hμ : (D : ℝ) < q * #{y | G y = p y} / q ^ m := by
    rw [lt_div_iff₀ (by positivity)]
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    linarith only [two_mul_mul_le' (Nat.cast_nonneg q) (by linarith only [hQ1]) ha hmargin,
      one_le_mul_of_one_le_of_one_le hD1' hQ1]
  obtain ⟨z, hz⟩ := exists_card_lineListDecode_ne_le hd hn hDq hp G hμ
  set C1 := Code.lineListDecode G d D z (p z)
  have herrC1 : ((d : ℝ) + 1) * #{x | C1 x ≠ p x} ≤ Q / 6 := by
    have hbound := lineErrors_le' (q := q) (Q := Q) (a := a) (ε := ε) (D := D)
      (δ := ((D - d : ℕ) : ℝ)) hq1 hQ1 hapos hε ha hmargin (by positivity)
      (by exact_mod_cast Nat.sub_le D d)
    calc ((d : ℝ) + 1) * #{x | C1 x ≠ p x}
        ≤ ((d : ℝ) + 1) * (Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1))) := by
          gcongr; exact hz.trans hbound
      _ = Q / 6 * (6 * ((d : ℝ) + 1) * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1))) := by ring
      _ ≤ Q / 6 := mul_le_of_le_one_right (by positivity) herr
  have hdq' : d + 2 ≤ Fintype.card F := by omega
  let ν : Fin (d + 1) ↪ F := nonzeroNodes hdq'
  have hν : ∀ i, ν i ≠ 0 := nonzeroNodes_ne_zero hdq'
  let grid : Finset (Fin m → F) :=
    univ.image fun x : BitString (m * b) => fun i => h (BitString.block x i)
  have hgrid : #grid ≤ 2 ^ (2 ^ L) :=
    calc #grid ≤ #(univ : Finset (BitString (m * b))) := card_image_le
      _ = 2 ^ (m * b) := by rw [card_univ, BitString.card]
      _ ≤ 2 ^ (2 ^ L) := Nat.pow_le_pow_right (by decide) hL
  obtain ⟨V, hV⟩ := exists_forall_majTree_eq (α := F) (Ω := Fin m → F) grid
    (fun x v => lagrangeDecode ν C1 x v) p (ρ := 1 / 6) (fun x _ => by
      have := card_lagrangeDecode_ne_le ν hν hp C1 x
      rw [hQ]
      calc (#{v | lagrangeDecode ν C1 x v ≠ p x} : ℝ) ≤ ((d + 1) * #{y | C1 y ≠ p y} : ℕ) := by
            exact_mod_cast this
        _ = ((d : ℝ) + 1) * #{y | C1 y ≠ p y} := by push_cast; ring
        _ ≤ Q / 6 := herrC1
        _ = 1 / 6 * Q := by ring) (by norm_num) hgrid
  have hGL := bitSynthesis_glPredictor_hom φ enc hC masks guess
  have hLL := bitSynthesis_lineListDecode_hom φ hGL d D z (p z)
  have hU := bitSynthesis_selfCorrect_hom φ hLL ν V
  let gp : Fin m → (Fin (m * b) → Bool) → F := fun i x => h (BitString.block x i)
  have hemb_dm : Synthesis interpretation (inputs (m * b))
      (Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2)
      (m * w * (2 ^ b * (2 * b + 2) + 1)) := by
    simpa only [Finset.sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
      mul_assoc] using Synthesis.family (I := interpretation) (s := inputs (m * b))
      (fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2) (fun _ => 2 ^ b * (2 * b + 2) + 1)
      fun ij => Synthesis.selected (fun l => finProdFinEquiv (ij.1, l)) fun y => enc (h y) ij.2
  have hemb : Synthesis J (inputs (m * b))
      (Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2)
      (m * w * (2 ^ b * (2 * b + 2) + 1)) :=
    (synthesis_lift φ hemb_dm (S := inputs (m * b)) (fun i x => x i) (fun i => ⟨i, rfl⟩)).mono
      Set.Subset.rfl (by rintro _ ⟨ij, rfl⟩; exact ⟨_, ⟨ij, rfl⟩, rfl⟩) le_rfl
  set T₁ := Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2
  have hUs := hU (m * b) (inputs (m * b) ∪ T₁) gp fun i j => Set.mem_union_right _ ⟨(i, j), rfl⟩
  set U : (Fin m → F) → F := fun x => majTree L fun τ => lagrangeDecode ν C1 x (V τ)
  set T₂ := Set.range fun j => bitsOf enc (fun v => U fun i => gp i v) j
  have hout : Synthesis J ((inputs (m * b) ∪ T₁) ∪ T₂) {f} (2 ^ w * (2 * w + 2) + 1) := by
    have hsel := Synthesis.selected (n := w) id (fun y => decide (enc.symm y = 1))
    refine (synthesis_lift φ hsel (S := (inputs (m * b) ∪ T₁) ∪ T₂)
      (fun j => bitsOf enc (fun v => U fun i => gp i v) j)
      (fun j => Set.mem_union_right _ ⟨j, rfl⟩)).mono Set.Subset.rfl ?_ le_rfl
    rw [Set.image_singleton, Set.singleton_subset_iff, Set.mem_singleton_iff]
    funext x
    have hUx : U (fun i => gp i x) = p (fun i => gp i x) :=
      hV _ (mem_image.2 ⟨x, mem_univ _, rfl⟩)
    simp only [Function.comp_id, bitsOf, Equiv.symm_apply_apply, hUx, p, gp,
      truthTableExtension_block]
    cases f x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, decide_false, decide_true]
  have hrec : complexity J (single f) ≤ reconstructionCost w b m D K L s q
      #(Sudan.monomials d D) :=
    (hemb.trans (hUs.trans hout)).complexity_le.trans (by
      unfold reconstructionCost glCost lineCost selfCorrectCost
      dsimp only [d, q]; omega)
  refine hrec.trans (reconstructionCost_le hqw ?_ ?_ ?_ hDq ?_ (by omega))
  · exact Nat.pos_of_ne_zero fun hw => by rw [hw, pow_zero] at hqw; omega
  · exact Nat.pos_of_ne_zero fun hm => by dsimp only [d] at hd; rw [hm, zero_mul] at hd; omega
  · exact (BitString.card (n := b)) ▸ Fintype.card_le_of_embedding h
  · calc #(Sudan.monomials d D) ≤ #(range (D + 1) ×ˢ range (D + 1)) := card_filter_le _ _
      _ = (D + 1) * (D + 1) := by rw [card_product, card_range]
      _ ≤ q * q := Nat.mul_le_mul hDq hDq
      _ = q ^ 2 := (sq _).symm

include hφ in
private theorem abs_card_div_sub_card_div_lt_hom [J.IsComplete] {ℓ n a m S s : ℕ} {ε : ℝ}
    (D : Design ℓ n a m) {f : BooleanFunction n}
    (hf : ∀ g : BooleanFunction n, complexity J (single g) ≤ s →
      (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 / 2 + 1 / (s : ℝ))
    (hs : S + 1 + m * (2 ^ a * (2 * a + 3) + 1) + 1 ≤ s) (hm : (m : ℝ) < ε * s)
    (test : BooleanFunction m) (htest : complexity J (single test) ≤ S) :
    |((#{z | test (generator D f z) = true} : ℕ) : ℝ) / 2 ^ ℓ -
      ((#{y | test y = true} : ℕ) : ℝ) / 2 ^ m| < ε := by
  have hspos : (0 : ℝ) < s := Nat.cast_pos.2
    (Nat.pos_of_ne_zero fun h => (Nat.cast_nonneg m).not_gt (hm.trans_eq (by simp [h])))
  have hε0 : 0 < ε := pos_of_mul_pos_left ((Nat.cast_nonneg m).trans_lt hm) hspos.le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hr (r : Fin 0 → Bool) : test r = test Fin.elim0 := congrArg test (Subsingleton.elim _ _)
    rcases hb : test Fin.elim0 with _ | _ <;> simp [hr, hb, hε0]
  have hεm : 1 / (s : ℝ) < ε / m := by
    rw [div_lt_div_iff₀ hspos (by exact_mod_cast hm0)]; linarith
  have hfool (t : BooleanFunction m) (ht : complexity J (single t) ≤ S + 1) :
      ((generator D f).realExperiment (fun y => PMF.pure (t y)) true).toReal -
        (Generator.idealExperiment (fun y => PMF.pure (t y)) true).toReal < ε := by
    by_contra hge
    obtain ⟨i, supp, bit, r, u, hsupp, hbit, hagree⟩ :=
      exists_dependsOn_half_add_div_le_card_nextBitGuess_eq D f t hm0 (not_lt.1 hge)
    set B := 2 ^ a * (2 * a + 3) + 1
    let q : Fin m → BooleanFunction n := fun j x =>
      if hj : (j : ℕ) < i then bit ⟨j, hj⟩ x else if j = i then r else u j
    have hq (j : Fin m) : complexity J (single (q j)) ≤ B := by
      refine (complexity_le_of_hom (I := interpretation) φ (single (q j))).trans ?_
      by_cases hj : (j : ℕ) < i
      · simp only [q, dite_eq_left hj]
        have hs_le := hsupp ⟨j, hj⟩
        exact (complexity_le_of_dependsOn (hbit ⟨j, hj⟩)).trans
          (Nat.add_le_add_right
            (Nat.mul_le_mul (Nat.pow_le_pow_right two_pos hs_le) (by omega)) 1)
      · simp only [q, dite_eq_right hj]
        exact (Synthesis.const _).complexity_le.trans (Nat.le_add_left 1 _)
    have hcomp : complexity J (single fun x => t fun j => q j x) ≤ S + 1 + m * B := by
      calc complexity J (single fun x => t fun j => q j x)
          ≤ complexity J (fun x j => q j x) + complexity J (single t) :=
            complexity_comp_le _ (single t)
        _ ≤ m * B + (S + 1) := Nat.add_le_add
            ((complexity_pi_le (I := J) q).trans ((sum_le_sum fun j _ => hq j).trans_eq (by simp)))
            ht
        _ = S + 1 + m * B := add_comm _ _
    let guess : BooleanFunction n := fun x => nextBitGuess t i r u fun j => bit j x
    have hguess : complexity J (single guess) ≤ s := by
      cases r
      · have e : guess = fun x => !t fun j => q j x := funext fun x => by
          simp only [guess, nextBitGuess, q]; cases t _ <;> rfl
        rw [e]; exact (complexity_not_hom_le φ _).trans (Nat.add_le_add_right hcomp 1 |>.trans hs)
      · have e : guess = fun x => t fun j => q j x := funext fun x => by
          simp only [guess, nextBitGuess, q]; cases t _ <;> rfl
        rw [e]; exact hcomp.trans ((Nat.le_succ _).trans hs)
    linarith [hf guess hguess, hagree, hεm]
  have hcompl {k : ℕ} (p : BitString k → Bool) :
      ((#{x | (!p x) = true} : ℕ) : ℝ) / Fintype.card (BitString k) =
        1 - ((#{x | p x = true} : ℕ) : ℝ) / Fintype.card (BitString k) := by
    have hpos : (0 : ℝ) < Fintype.card (BitString k) := mod_cast Fintype.card_pos
    have hsum : #{x | p x = true} + #{x | (!p x) = true} = Fintype.card (BitString k) := by
      simpa using card_filter_add_card_filter_not (s := univ) fun x => p x = true
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
    exact_mod_cast (add_comm _ _).trans hsum
  have h₁ := hfool test (htest.trans (Nat.le_succ S))
  have h₂ := hfool (fun y => !test y)
    ((complexity_not_hom_le φ test).trans (Nat.add_le_add_right htest 1))
  simp only [Generator.toReal_realExperiment_pure, Generator.toReal_idealExperiment_pure,
    nnratCast_dens] at h₁ h₂
  rw [hcompl (fun z => test (generator D f z)), hcompl test] at h₂
  simp only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] at h₁ h₂
  exact abs_lt.2 ⟨by linarith, h₁⟩

end RelativizedSynthesis

/-! ### Worst-case-to-average-case amplification and NW fooling for oracle circuits -/

/-- Average-case hardness against `A`-oracle circuits of gate count at most `s` and query arity at
most `r`: no such circuit agrees with `f` on more than a `1 / 2 + 1 / s` fraction of inputs. -/
def IsOracleAverageCaseHard (A : Language Bool) {n : ℕ} (f : BooleanFunction n)
    (r s : ℕ) : Prop :=
  ∀ g : BooleanFunction n, complexity (boundedOracleInterpretation A r) (single g) ≤ s →
    (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 / 2 + 1 / (s : ℝ)

/-- **Relativized Nisan–Wigderson pseudorandomness against fan-in-capped oracle circuits.** If `f`
satisfies `IsOracleAverageCaseHard A f r s`, then `generator D f` `ε`-fools every Boolean test of
complexity at most `S` over `boundedOracleInterpretation A r` whenever
`S + 1 + m * (2 ^ a * (2 * a + 3) + 1) + 1 ≤ s` and `m < ε * s`. -/
theorem abs_card_div_sub_card_div_lt_boundedOracle (A : Language Bool) {ℓ n a m r S s : ℕ} {ε : ℝ}
    (D : Design ℓ n a m) {f : BooleanFunction n}
    (hf : IsOracleAverageCaseHard A f r s)
    (hs : S + 1 + m * (2 ^ a * (2 * a + 3) + 1) + 1 ≤ s) (hm : (m : ℝ) < ε * s)
    (test : BooleanFunction m)
    (htest : complexity (boundedOracleInterpretation A r) (single test) ≤ S) :
    |((#{z | test (generator D f z) = true} : ℕ) : ℝ) / 2 ^ ℓ -
      ((#{y | test y = true} : ℕ) : ℝ) / 2 ^ m| < ε :=
  abs_card_div_sub_card_div_lt_hom (toBoundedOracle r) D hf hs hm test htest

/-- The block factor `⌈80 / ε⌉₊ + 1` for oracle-circuit hardness amplification. -/
noncomputable def oracleBlockFactor (ε : ℝ) : ℕ :=
  ⌈80 / ε⌉₊ + 1

/-- The divisor `200 * (oracleBlockFactor ε + 1)` of the oracle average-case hardness exponent. -/
noncomputable def oracleHardnessDivisor (ε : ℝ) : ℕ :=
  200 * (oracleBlockFactor ε + 1)

private theorem three_pow_log_le' {x : ℕ} (hx : 0 < x) :
    3 ^ (Nat.log 2 x + 1) ≤ 3 * x ^ 2 := by
  have h1 : 3 ^ Nat.log 2 x ≤ 4 ^ Nat.log 2 x := Nat.pow_le_pow_left (by norm_num) _
  have h2 : 4 ^ Nat.log 2 x = (2 ^ Nat.log 2 x) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h3 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx.ne'
  rw [pow_succ]
  calc 3 ^ Nat.log 2 x * 3 ≤ (2 ^ Nat.log 2 x) ^ 2 * 3 := by rw [← h2]; gcongr
    _ ≤ x ^ 2 * 3 := by gcongr
    _ = 3 * x ^ 2 := by ring

private theorem two_pow_masks_le' (σ : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) ≤ 16 * b * 4 ^ σ := by
  rw [pow_add, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  calc 4 ^ σ * 2 ^ Nat.log 2 (4 * b) * 4 ≤ 4 ^ σ * (4 * b) * 4 := by
        gcongr; exact Nat.pow_log_le_self 2 (by omega)
    _ = 16 * b * 4 ^ σ := by ring

private theorem two_pow_masks_ge' (σ b : ℕ) :
    2 * (4 * b) * 4 ^ σ + 1 ≤ 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) := by
  rw [pow_add, pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  have h : 4 * b < 2 ^ (Nat.log 2 (4 * b) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [pow_succ] at h
  have h4 : 1 ≤ 4 ^ σ := Nat.one_le_pow _ _ (by norm_num)
  have h' : 2 * (4 * b) + 2 ≤ 4 * 2 ^ Nat.log 2 (4 * b) := by omega
  calc 2 * (4 * b) * 4 ^ σ + 1 ≤ (2 * (4 * b) + 2) * 4 ^ σ := by nlinarith
    _ ≤ 4 * 2 ^ Nat.log 2 (4 * b) * 4 ^ σ := Nat.mul_le_mul_right _ h'
    _ = 4 ^ σ * 2 ^ Nat.log 2 (4 * b) * 4 := by ring

private theorem stv_error_le_one {M b σ : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b) (h3σ : 3 * σ ≤ b)
    (hD' : 4608 * M * b ≤ 2 ^ (b / 4)) (hE : 36 * M ≤ 2 ^ (b / 4)) :
    6 * (((M * (2 ^ b - 1) : ℕ) : ℝ) + 1) * (1 / ((2 ^ (4 * b) : ℕ) : ℝ) ^ M +
      2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 4) /
        (((2 ^ (4 * b) : ℕ) : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) +
      ((2 ^ (3 * b - b / 4) : ℕ) : ℝ) / (((2 ^ (4 * b) : ℕ) : ℝ) - 1)) ≤ 1 := by
  set q := 2 ^ (4 * b) with hq
  set d := M * (2 ^ b - 1)
  set Km := 2 * σ + Nat.log 2 (4 * b) + 2
  set D := 2 ^ (3 * b - b / 4)
  have hd1' : d + 1 ≤ M * 2 ^ b := by
    have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have : M ≤ M * 2 ^ b := Nat.le_mul_of_pos_right _ (by positivity)
    rw [show d = M * 2 ^ b - M from Nat.mul_sub_one M (2 ^ b)]; omega
  have hq18 : 18 * (d + 1) ≤ q :=
    calc 18 * (d + 1) ≤ 18 * M * 2 ^ b := by nlinarith
      _ ≤ 2 ^ (3 * b) * 2 ^ b := Nat.mul_le_mul_right _
          ((show 18 * M ≤ 2 ^ (b / 4) by omega).trans
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
      _ = q := by rw [hq, ← pow_add]; congr 1; ring
  have hT1 : 18 * (d + 1) ≤ q ^ M := hq18.trans (Nat.le_self_pow (by omega) q)
  have hT2 : 18 * (d + 1) * 2 ^ (Km + 4) * 2 ^ σ ≤ q :=
    calc 18 * (d + 1) * 2 ^ (Km + 4) * 2 ^ σ
        ≤ 18 * (M * 2 ^ b) * (16 * b * 4 ^ σ * 16) * 2 ^ σ := by
          rw [pow_add _ Km 4, show (2 : ℕ) ^ 4 = 16 by norm_num]
          gcongr; exact two_pow_masks_le' σ hb
      _ = 4608 * M * b * 2 ^ b * 2 ^ (3 * σ) := by
          rw [show 3 * σ = 2 * σ + σ by ring, pow_add, pow_mul,
            show (2 : ℕ) ^ 2 = 4 by norm_num]; ring
      _ ≤ 2 ^ (b / 4) * 2 ^ b * 2 ^ b := by gcongr
      _ ≤ q := by
          rw [← pow_add, ← pow_add, hq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT3 : 18 * (d + 1) * D + 1 ≤ q := by
    have h1 : 18 * (d + 1) * D ≤ 18 * M * 2 ^ (4 * b - b / 4) :=
      calc 18 * (d + 1) * D ≤ 18 * (M * 2 ^ b) * D := by gcongr
        _ = 18 * M * 2 ^ (b + (3 * b - b / 4)) := by rw [pow_add]; ring
        _ = 18 * M * 2 ^ (4 * b - b / 4) := by congr 2; omega
    have h2 : 36 * M * 2 ^ (4 * b - b / 4) ≤ q :=
      calc 36 * M * 2 ^ (4 * b - b / 4) ≤ 2 ^ (b / 4) * 2 ^ (4 * b - b / 4) := by gcongr
        _ = q := by rw [hq, ← pow_add]; congr 1; omega
    have h3 : 1 ≤ 18 * M * 2 ^ (4 * b - b / 4) := Nat.one_le_iff_ne_zero.2 (by positivity)
    linarith
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Nat.one_lt_two_pow (by omega : 4 * b ≠ 0)
  have hdpos : (0 : ℝ) < 18 * ((d : ℝ) + 1) := by positivity
  have e1 : 1 / (q : ℝ) ^ M ≤ 1 / (18 * ((d : ℝ) + 1)) :=
    one_div_le_one_div_of_le hdpos (by exact_mod_cast hT1)
  have e2 : (2 : ℝ) ^ (Km + 4) / ((q : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ))) ≤
      1 / (18 * ((d : ℝ) + 1)) := by
    rw [mul_one_div, div_div_eq_mul_div, div_le_div_iff₀ (by linarith) hdpos, one_mul]
    have : ((18 * (d + 1) * 2 ^ (Km + 4) * 2 ^ σ : ℕ) : ℝ) ≤ q := by exact_mod_cast hT2
    push_cast at this ⊢; linarith
  have e3 : (D : ℝ) / ((q : ℝ) - 1) ≤ 1 / (18 * ((d : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by linarith) hdpos, one_mul]
    have : ((18 * (d + 1) * D + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hT3
    push_cast at this; linarith
  calc _ ≤ 6 * ((d : ℝ) + 1) * (3 * (1 / (18 * ((d : ℝ) + 1)))) := by gcongr; linarith
    _ = 1 := by field_simp; ring

private theorem stv_final_cost_le {M b σ : ℕ} (hM : 1 ≤ M) (hb : 1 ≤ b) (h5σ : 5 * σ ≤ b)
    (hF : 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4)) :
    2 ^ 11 * 3 ^ (Nat.log 2 (M * b) + 1) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
      4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * (2 ^ σ + 2 + 1) ≤ 2 ^ (40 * b) := by
  have h3L := three_pow_log_le' (Nat.mul_pos hM hb)
  have h4K : 4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) ≤ 256 * b ^ 2 * 16 ^ σ := by
    rw [show 4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) =
      (2 ^ (2 * σ + Nat.log 2 (4 * b) + 2)) ^ 2 by
        rw [← pow_mul, mul_comm _ 2, pow_mul]; norm_num]
    calc (2 ^ (2 * σ + Nat.log 2 (4 * b) + 2)) ^ 2 ≤ (16 * b * 4 ^ σ) ^ 2 :=
          Nat.pow_le_pow_left (two_pow_masks_le' σ hb) 2
      _ = 256 * b ^ 2 * 16 ^ σ := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm σ 2, pow_mul]; norm_num
  have hs : 2 ^ σ + 2 + 1 ≤ 4 * 2 ^ σ := by have := @Nat.one_le_two_pow σ; omega
  calc 2 ^ 11 * 3 ^ (Nat.log 2 (M * b) + 1) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
        4 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * (2 ^ σ + 2 + 1)
      ≤ 2 ^ 11 * (3 * (M * b) ^ 2) * M * (4 * b) ^ 2 * (2 ^ (4 * b)) ^ 9 *
          (256 * b ^ 2 * 16 ^ σ) * (4 * 2 ^ σ) := by gcongr
    _ = 3 * 2 ^ 25 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ (5 * σ) := by
        rw [show 16 ^ σ = 2 ^ (4 * σ) by rw [pow_mul]; norm_num,
          show 5 * σ = 4 * σ + σ by ring, pow_add 2 (4 * σ) σ, ← pow_mul,
          show 4 * b * 9 = 36 * b by ring]; ring
    _ ≤ 2 ^ 27 * M ^ 3 * b ^ 6 * (2 ^ (36 * b) * 2 ^ b) := by
        have hpow5 : 2 ^ (5 * σ) ≤ 2 ^ b := Nat.pow_le_pow_right two_pos h5σ
        calc 3 * 2 ^ 25 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ (5 * σ)
            ≤ 2 ^ 27 * (M ^ 3 * b ^ 6) * 2 ^ (36 * b) * 2 ^ b := by
              gcongr; norm_num
          _ = 2 ^ 27 * M ^ 3 * b ^ 6 * (2 ^ (36 * b) * 2 ^ b) := by ring
    _ ≤ 2 ^ (b / 4) * 2 ^ (37 * b) := by
        rw [← pow_add, show 36 * b + b = 37 * b by ring]; exact Nat.mul_le_mul_right _ hF
    _ ≤ 2 ^ (40 * b) := by rw [← pow_add]; exact Nat.pow_le_pow_right two_pos (by omega)

/-- **Relativized Impagliazzo–Wigderson / Sudan–Trevisan–Vadhan hardness amplification.** If a
language `L` avoids `i.o.-Size^A(2^{ε n})` for some `ε > 0`, then at all sufficiently large input
lengths `K` (uniformly over all query-arity caps `r ≤ 2 ^ ⌊K / c⌋`), the encoded slice of `L` is
average-case hard against `A`-oracle circuits of gate count `2 ^ ⌊K / c⌋` and query arity `r`. -/
theorem eventually_isOracleAverageCaseHard_encodedSlice {A L : Language Bool} {ε : ℝ}
    (hε : 0 < ε) (hard : L ∉ oracleSIZEInfOften A (fun n => (2 : ℝ) ^ (ε * (n : ℝ)))) :
    ∀ᶠ K in atTop, ∀ r ≤ 2 ^ (K / oracleHardnessDivisor ε),
      IsOracleAverageCaseHard A (encodedSlice L (oracleBlockFactor ε) K) r
        (2 ^ (K / oracleHardnessDivisor ε)) := by
  set M := oracleBlockFactor ε with hM_def
  have hM : 1 ≤ M := Nat.le_add_left 1 _
  have hεM : 80 ≤ ε * M := by
    have h : 80 / ε ≤ M := by
      simpa only [hM_def, oracleBlockFactor, Nat.cast_add, Nat.cast_one] using
        (Nat.le_ceil (80 / ε)).trans (le_add_of_nonneg_right zero_le_one)
    rwa [div_le_iff₀ hε, mul_comm] at h
  have hblock : Tendsto (blockLength M) atTop atTop := Nat.tendsto_div_const_atTop (by positivity)
  have hMb : Tendsto (fun b : ℕ => M * b) atTop atTop := tendsto_id.const_mul_atTop' (by omega)
  have hhard : ∀ᶠ b : ℕ in atTop, ∀ C : Circuit oracleSignature (M * b) 1,
      C.Computes (oracleInterpretation A) (single (L.slice (M * b))) →
        2 ^ (80 * b) < oracleCircuitSize C := by
    filter_upwards [hMb.eventually (notMem_oracleSIZEInfOften_iff.1 hard)] with b hb C hC
    have h1 : ((2 ^ (80 * b) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * ((M * b : ℕ) : ℝ)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (by push_cast; nlinarith)
    exact_mod_cast h1.trans_lt (hb C hC)
  have hev := Nat.eventually_mul_pow_le_pow_div (2 ^ 27 * M ^ 3 + 4608 * M + 128) 6 4
    one_lt_two (by positivity)
  filter_upwards [hblock.eventually (hhard.and (hev.and (eventually_ge_atTop 2)))] with K hK r hr
  classical
  set b := blockLength M K
  set σ := K / oracleHardnessDivisor ε
  obtain ⟨hhardb, hevb, hb2⟩ := hK
  have hb : 1 ≤ b := by omega
  have hb0 : b ≠ 0 := by omega
  have hw0 : 4 * b ≠ 0 := by omega
  have hσ50 : 50 * σ ≤ b + 1 := by
    have h1 := Nat.div_mul_le_self K (oracleHardnessDivisor ε)
    have h2 := Nat.lt_div_mul_add (a := K) (b := 4 * (M + 1)) (by positivity)
    simp only [oracleHardnessDivisor, ← hM_def, blockLength, b, σ] at h1 h2 ⊢; nlinarith
  have h3σ : 3 * σ ≤ b := by omega
  have h5σ : 5 * σ ≤ b := by omega
  have hb6 : b ≤ b ^ 6 := Nat.le_self_pow (by norm_num) b
  have hB : 128 * b ≤ 2 ^ (b / 4) := (Nat.mul_le_mul (Nat.le_add_left _ _) hb6).trans hevb
  have hD' : 4608 * M * b ≤ 2 ^ (b / 4) := (Nat.mul_le_mul (by omega) hb6).trans hevb
  have hF : 2 ^ 27 * M ^ 3 * b ^ 6 ≤ 2 ^ (b / 4) :=
    (Nat.mul_le_mul_right _ (by omega)).trans hevb
  have hE : 36 * M ≤ 2 ^ (b / 4) := by have := Nat.mul_le_mul_left (4608 * M) hb; omega
  have hA : 2 * M ≤ 2 ^ (b / 2) :=
    (show 2 * M ≤ 2 ^ (b / 4) by omega).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2b : 2 ≤ 2 ^ b := (show 2 = 2 ^ 1 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hb
  have hd1 : 1 ≤ M * (2 ^ b - 1) := Nat.mul_pos (by omega) (by omega)
  intro g hg
  by_contra hcon
  push Not at hcon
  rw [encodedSlice, dite_eq_right hb0, lt_div_iff₀ (by positivity)] at hcon
  obtain ⟨C, hC, hCagree⟩ := exists_complexity_hom_le_of_agree_prefix
    (J := boundedOracleInterpretation A r) (toBoundedOracle r) (encodedLength_le M K) _ g hcon
  have hmasks : ((4 * b : ℕ) : ℝ) ≤ 2 * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 *
      ((2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) - 1 : ℕ) : ℝ) := by
    have hcast : (2 * (4 * b) * 4 ^ σ : ℝ) ≤
        ((2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_sub_one_of_lt (two_pow_masks_ge' σ b)
    have h4 : (2 : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ) / 2) ^ 2 * (2 * (4 * b) * 4 ^ σ) = (4 * b : ℕ) := by
      rw [show (4 : ℝ) ^ σ = (2 ^ σ) ^ 2 by rw [← pow_mul, mul_comm σ 2, pow_mul]; norm_num]
      push_cast; field_simp
    exact h4.symm.le.trans (by gcongr)
  have hmon : 2 ^ (4 * b) < #(Sudan.monomials (M * (2 ^ b - 1)) (2 ^ (3 * b - b / 4))) := by
    set d := M * (2 ^ b - 1)
    set D := 2 ^ (3 * b - b / 4)
    have hDsq : 2 ^ (6 * b - b / 2) ≤ D * D := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdlt : d < M * 2 ^ b := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have h2dq : 2 * d * 2 ^ (4 * b) < 2 ^ (6 * b - b / 2) :=
      calc 2 * d * 2 ^ (4 * b) < 2 * (M * 2 ^ b) * 2 ^ (4 * b) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = 2 * M * 2 ^ (b + 4 * b) := by rw [pow_add]; ring
        _ ≤ 2 ^ (b / 2) * 2 ^ (b + 4 * b) := Nat.mul_le_mul_right _ hA
        _ = 2 ^ (b / 2 + (b + 4 * b)) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (6 * b - b / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_mul_lt_mul_left
      ((h2dq.trans_le hDsq).trans_le ((Nat.mul_le_mul (Nat.le_succ D) (by omega)).trans
        (Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials hd1 D))) (Nat.zero_le _)
  have hmarg : (2 : ℝ) ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * ((2 ^ (3 * b - b / 4) : ℕ) : ℝ) ≤
      ((2 ^ (4 * b) : ℕ) : ℝ) * (1 / ((2 ^ σ : ℕ) : ℝ)) := by
    have hnat : 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * 2 ^ (3 * b - b / 4) * 2 ^ σ ≤
        2 ^ (4 * b) :=
      calc 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2 + 3) * 2 ^ (3 * b - b / 4) * 2 ^ σ
          = 2 ^ (2 * σ + Nat.log 2 (4 * b) + 2) * 8 * 2 ^ (3 * b - b / 4) * 2 ^ σ := by
            rw [pow_add _ _ 3]; norm_num
        _ ≤ 16 * b * 4 ^ σ * 8 * 2 ^ (3 * b - b / 4) * 2 ^ σ := by
            gcongr; exact two_pow_masks_le' σ hb
        _ = 128 * b * 2 ^ (3 * σ) * 2 ^ (3 * b - b / 4) := by
            rw [show 3 * σ = 2 * σ + σ by ring, pow_add, pow_mul,
              show (2 : ℕ) ^ 2 = 4 by norm_num]; ring
        _ ≤ 2 ^ (b / 4) * 2 ^ b * 2 ^ (3 * b - b / 4) := by gcongr
        _ = 2 ^ (4 * b) := by rw [← pow_add, ← pow_add]; congr 1; omega
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    exact_mod_cast hnat
  have herr := stv_error_le_one hM hb h3σ hD' hE
  have hrec := complexity_hom_le_pow_of_agree_hardnessEncode (toBoundedOracle r)
    (BinaryField.equivBits hw0).toEquiv (BinaryField.embed hw0 (by omega : b ≤ 4 * b))
    (L.slice (M * b)) (C := C) (s := 2 ^ σ + 2) (hC.trans (by omega))
    (ε := 1 / ((2 ^ σ : ℕ) : ℝ)) (by positivity) hCagree.le
    (K := 2 * σ + Nat.log 2 (4 * b) + 2) (D := 2 ^ (3 * b - b / 4))
    (L := Nat.log 2 (M * b) + 1) (by omega) hmasks hd1
    (by rw [BinaryField.card hw0]; exact hmon)
    (by rw [BinaryField.card hw0]; exact hmarg)
    (by rw [BinaryField.card hw0]; exact herr)
    (Nat.lt_pow_succ_log_self (by norm_num) (M * b)).le
  rw [BinaryField.card hw0] at hrec
  obtain ⟨circ, hcirc, hcirc_sz⟩ :=
    complexity_le_iff.1 (hrec.trans (stv_final_cost_le hM hb h5σ hF))
  have hrmax : max 2 r + 1 ≤ 2 ^ (2 * b) := by
    have hr2b : r ≤ 2 ^ b := hr.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : 4 ≤ 2 ^ b := (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hb2
    have hsq : 2 ^ (2 * b) = 2 ^ b * 2 ^ b := by rw [two_mul, pow_add]
    have hmax : max 2 r ≤ 2 ^ b := max_le (by omega) hr2b
    nlinarith
  have horacle : oracleCircuitSize (circ.mapOp (fromBoundedOracle r)) ≤ 2 ^ (80 * b) :=
    calc oracleCircuitSize (circ.mapOp (fromBoundedOracle r))
        ≤ circ.size * (max 2 r + 1) := oracleCircuitSize_fromBoundedOracle_le circ
      _ ≤ 2 ^ (40 * b) * 2 ^ (2 * b) := Nat.mul_le_mul hcirc_sz hrmax
      _ ≤ 2 ^ (80 * b) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (hhardb _ hcirc.mapOp).not_ge horacle

/-- Positivity of `oracleHardnessDivisor ε` for every real `ε`. -/
theorem oracleHardnessDivisor_pos (ε : ℝ) : 0 < oracleHardnessDivisor ε := by
  unfold oracleHardnessDivisor; positivity

end CslibFrontier.Computability
